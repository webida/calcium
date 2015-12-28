(function(f){if(typeof exports==="object"&&typeof module!=="undefined"){module.exports=f()}else if(typeof define==="function"&&define.amd){define([],f)}else{var g;if(typeof window!=="undefined"){g=window}else if(typeof global!=="undefined"){g=global}else if(typeof self!=="undefined"){g=self}else{g=this}g.calcium = f()}})(function(){var define,module,exports;return (function e(t,n,r){function s(o,u){if(!n[o]){if(!t[o]){var a=typeof require=="function"&&require;if(!u&&a)return a(o,!0);if(i)return i(o,!0);var f=new Error("Cannot find module '"+o+"'");throw f.code="MODULE_NOT_FOUND",f}var l=n[o]={exports:{}};t[o][0].call(l.exports,function(e){var n=t[o][1][e];return s(n?n:e)},l,l.exports,e,t,n,r)}return n[o].exports}var i=typeof require=="function"&&require;for(var o=0;o<r.length;o++)s(r[o]);return s})({1:[function(require,module,exports){
'use strict';

exports.__esModule = true;
var options = {
    acornOption: {
        ecmaVersion: 6,
        // sourceType: 'script' or 'module'
        // 'module' is used for ES6 modules and
        // 'use strict' assumed for those modules.
        // This option is also used by the analyzer.
        sourceType: 'script'
    },
    // At the start of program and each function,
    // check 'use strict'
    // maybe we do not need this option
    detectUseStrict: true,

    // context insensitive
    sensitivityParameter: {
        maxDepthK: 0,
        contextLengthOfFunc: function contextLengthOfFunc(fn) {
            return 0;
        }
    }
};
exports.options = options;

},{}],2:[function(require,module,exports){
/**
 * @file Generates constraints from ASTs
 * @author sewon326.kim@samsung.com
 */

'use strict';
exports.__esModule = true;
exports.getRestAVal = getRestAVal;
exports.addConstraints = addConstraints;

function _interopRequireWildcard(obj) { if (obj && obj.__esModule) { return obj; } else { var newObj = {}; if (obj != null) { for (var key in obj) { if (Object.prototype.hasOwnProperty.call(obj, key)) newObj[key] = obj[key]; } } newObj['default'] = obj; return newObj; } }

var _domainsTypes = require('../domains/types');

var types = _interopRequireWildcard(_domainsTypes);

var _utilMyWalker = require('../util/myWalker');

var myWalker = _interopRequireWildcard(_utilMyWalker);

var _domainsContext = require('../domains/context');

var csc = _interopRequireWildcard(_domainsContext);

var walk = require('acorn/dist/walk');
var cstr = require('./constraints');

// returns [access type, prop value]
function propAccess(node) {
    var prop = node.property;
    if (prop.type === 'Identifier' && myWalker.isDummyIdNode(node.property)) {
        return ['dummyProperty'];
    }
    if (!node.computed) {
        return ['dotAccess', prop.name];
    }
    if (prop.type === 'Literal') {
        if (typeof prop.value === 'string') return ['stringLiteral', prop.value];
        if (typeof prop.value === 'number')
            // convert number to string
            return ['numberLiteral', prop.value + ''];
    }
    return ['computed', null];
}

function unopResultType(op) {
    switch (op) {
        case '+':case '-':case '~':
            return types.PrimNumber;
        case '!':
            return types.PrimBoolean;
        case 'typeof':
            return types.PrimString;
        case 'void':case 'delete':
            return null;
    }
}

function binopIsBoolean(op) {
    switch (op) {
        case '==':case '!=':case '===':case '!==':
        case '<':case '>':case '>=':case '<=':
        case 'in':case 'instanceof':
            return true;
    }
    return false;
}

// To prevent recursion,
// we remember the status used in addConstraints
var visitedStatus = [];

var rtCX = undefined;
var connectPattern = undefined;

exports.connectPattern = connectPattern;

function getRestAVal(node, curStatus) {
    if (node.type !== "RestElement") throw new Error('Should be RestElement');
    if (!node.restArrayMap) {
        node.restArrayMap = new Map();
    }
    var restAVal = undefined;
    if (node.restArrayMap.has(curStatus.delta)) {
        restAVal = node.restArrayMap.get(curStatus.delta);
    } else {
        restAVal = new types.AVal(new types.ArrType(new types.AVal(rtCX.protos.Array)));
        node.restArrayMap.set(curStatus.delta, restAVal);
    }
    return restAVal;
}

/**
 * Generate constraints.
 * This function returns `true` when it actually added constraints.
 * @param astNode
 * @param initStatus
 * @param newRtCX
 * @return {boolean}
 */

function addConstraints(astNode, initStatus, newRtCX) {

    // set rtCX
    rtCX = newRtCX || rtCX;
    var Ĉ = rtCX.Ĉ;

    // Check whether we have processed 'initStatus' before
    for (var i = 0; i < visitedStatus.length; i++) {
        if (initStatus.equals(visitedStatus[i])) {
            // If so, do nothing
            // signifying we didn't add constraints
            return false;
        }
    }
    // If the initStatus is new, push it.
    // We do not record ast since ast node depends on the status
    visitedStatus.push(initStatus);

    function readMember(node, curStatus, c) {
        var ret = Ĉ.get(node, curStatus.delta);
        var objAVal = c(node.object, curStatus, undefined);
        if (node.property.type !== 'Identifier') {
            // return from property is ignored
            c(node.property, curStatus, undefined);
        }

        var _propAccess = propAccess(node);

        var accType = _propAccess[0];
        var propName = _propAccess[1];

        if (accType !== 'dummyProperty') {
            objAVal.propagate(new cstr.ReadProp(propName, ret));
        }

        // returns AVal for receiver and read member
        return [objAVal, ret];
    }

    var patternWalk = {
        Identifier: function Identifier(node, curStatus, source) {
            var varName = node.name;
            var lhsAVal = curStatus.sc.getAValOf(varName);
            Ĉ.set(node, curStatus.delta, lhsAVal);
            source.propagate(lhsAVal);
        },
        MemberExpression: function MemberExpression(node, curStatus, source) {
            var objAVal = stmtExprWalker(node.object, curStatus);

            var _propAccess2 = propAccess(node.left);

            var accType = _propAccess2[0];
            var propName = _propAccess2[1];

            // assignment to member
            if (accType !== 'dummyProperty') {
                objAVal.propagate(new cstr.WriteProp(propName, source));
            }
            // if property is number literal, also write to 'unknown'
            if (accType === 'numberLiteral') {
                objAVal.propagate(new cstr.WriteProp(null, source));
            }
            // node's AVal from RHS
            Ĉ.set(node, curStatus.delta, source);
        },
        ObjectPattern: function ObjectPattern(node, curStatus, source) {
            for (var i = 0; i < node.properties.length; i++) {
                var prop = node.properties[i];
                // We need an AVal for prop read.
                // Not sure attaching the AVal to prop.key node is good.
                var propAVal = Ĉ.get(prop.key, curStatus.delta);
                source.propagate(new cstr.ReadProp(prop.key.name, propAVal));
                connectPattern(prop.value, curStatus, propAVal);
            }
        },
        ArrayPattern: function ArrayPattern(node, curStatus, source) {
            for (var i = 0; i < node.elements.length; i++) {
                var elt = node.elements[i];
                var eltAVal = Ĉ.get(elt, curStatus.delta);
                if (elt.type === 'RestElement') {
                    // use only one element
                    var restAVal = getRestAVal(node, curStatus);
                    restAVal.propagate(eltAVal);

                    var tempAVal = new types.AVal();
                    source.propagate(new cstr.ReadProp(String(i), tempAVal));
                    restAVal.propagate(new cstr.WriteProp(String(0), tempAVal));
                    restAVal.propagate(new cstr.WriteProp(null, tempAVal));
                    connectPattern(elt, curStatus, restAVal);
                    break;
                }
                if (elt) {
                    // We need an AVal for index read
                    // Not sure attaching the AVal to elt node is good.
                    source.propagate(new cstr.ReadProp(String(i), eltAVal));
                    connectPattern(elt, curStatus, eltAVal);
                }
            }
        },
        AssignmentPattern: function AssignmentPattern(node, curStatus, source) {
            var mergedAVal = Ĉ.get(node, curStatus.delta);
            var rhsAVal = stmtExprWalker(node.right, curStatus);
            source.propagate(mergedAVal);
            rhsAVal.propagate(mergedAVal);
            connectPattern(node.left, curStatus, mergedAVal);
        },
        RestElement: function RestElement(node, curStatus, source) {
            connectPattern(node.argument, curStatus, source);
        }
    };

    exports.connectPattern = connectPattern = function (node, curStatus, source) {
        var connector = patternWalk[node.type];
        if (connector) connector(node, curStatus, source);
    };

    // constraint generating walker for expressions
    var stmtExprWalk = walk.make({

        Identifier: function Identifier(node, curStatus, c) {
            if (myWalker.isDummyIdNode(node)) {
                // Return AValNull for dummy identity node
                return types.AValNull;
            }
            var av = curStatus.sc.getAValOf(node.name);
            // use aval in the scope
            Ĉ.set(node, curStatus.delta, av);
            return av;
        },

        ThisExpression: function ThisExpression(node, curStatus, c) {
            var av = curStatus.self;
            // use aval for 'this'
            Ĉ.set(node, curStatus.delta, av);
            return av;
        },

        Literal: function Literal(node, curStatus, c) {
            var res = Ĉ.get(node, curStatus.delta);
            if (node.regex) {
                // not implemented yet
                // throw new Error('regex literal is not implemented yet');
                return res;
            }
            switch (typeof node.value) {
                case 'number':
                    res.addType(types.PrimNumber);
                    break;
                case 'string':
                    res.addType(types.PrimString);
                    break;
                case 'boolean':
                    res.addType(types.PrimBoolean);
                    break;
                case 'object':
                    // I guess: Literal && object ==> node.value == null
                    // null is ignored, so nothing to add
                    break;
                case 'function':
                    throw new Error('I guess function is impossible here.');
            }
            return res;
        },

        AssignmentExpression: function AssignmentExpression(node, curStatus, c) {
            var rhsAVal = c(node.right, curStatus, undefined);
            if (node.left.type === 'Identifier') {
                // LHS is a simple variable.
                var varName = node.left.name;
                var lhsAVal = curStatus.sc.getAValOf(varName);
                // lhs is not visited. Need to handle here.
                // Use aval found in the scope for lhs
                Ĉ.set(node.left, curStatus.delta, lhsAVal);

                if (node.operator === '=') {
                    // simple assignment
                    rhsAVal.propagate(lhsAVal);
                    // node's AVal from RHS
                    Ĉ.set(node, curStatus.delta, rhsAVal);
                    return rhsAVal;
                }
                // updating assignment
                var resAVal = Ĉ.get(node, curStatus.delta);
                if (node.operator === '+=') {
                    // concatenating update
                    lhsAVal.propagate(new cstr.IsAdded(rhsAVal, resAVal));
                    rhsAVal.propagate(new cstr.IsAdded(lhsAVal, resAVal));
                } else {
                    // arithmetic update
                    resAVal.addType(types.PrimNumber);
                }
                return resAVal;
            } else if (node.left.type === 'MemberExpression') {
                var objAVal = c(node.left.object, curStatus, undefined);

                var _propAccess3 = propAccess(node.left);

                var accType = _propAccess3[0];
                var propName = _propAccess3[1];

                if (node.operator === '=') {
                    // assignment to member
                    if (accType !== 'dummyProperty') {
                        objAVal.propagate(new cstr.WriteProp(propName, rhsAVal));
                    }
                    // if property is number literal, also write to 'unknown'
                    if (accType === 'numberLiteral') {
                        objAVal.propagate(new cstr.WriteProp(null, rhsAVal));
                    }
                    // node's AVal from RHS
                    Ĉ.set(node, curStatus.delta, rhsAVal);
                    return rhsAVal;
                }
                // updating assignment
                var resAVal = Ĉ.get(node, curStatus.delta);

                var _readMember = readMember(node.left, curStatus, c);

                var retAVal = _readMember[1];

                if (node.operator === '+=') {
                    // concatenating update
                    retAVal.propagate(new cstr.IsAdded(rhsAVal, resAVal));
                    rhsAVal.propagate(new cstr.IsAdded(retAVal, resAVal));
                } else {
                    // arithmetic update
                    resAVal.addType(types.PrimNumber);
                }
                return resAVal;
            } else {
                connectPattern(node.left, curStatus, rhsAVal);
            }
        },

        VariableDeclaration: function VariableDeclaration(node, curStatus, c) {
            for (var i = 0; i < node.declarations.length; i++) {
                var decl = node.declarations[i];
                // const lhsAVal = curStatus.sc.getAValOf(decl.id.name);
                // declared var node is 'id'
                // Ĉ.set(decl.id, curStatus.delta, lhsAVal);
                if (decl.init) {
                    var rhsAVal = c(decl.init, curStatus, undefined);
                    Ĉ.set(decl.init, curStatus.delta, rhsAVal);
                    //rhsAVal.propagate(lhsAVal);
                    connectPattern(decl.id, curStatus, rhsAVal);
                }
            }
        },

        LogicalExpression: function LogicalExpression(node, curStatus, c) {
            var res = Ĉ.get(node, curStatus.delta);
            var left = c(node.left, curStatus, undefined);
            var right = c(node.right, curStatus, undefined);
            left.propagate(res);
            right.propagate(res);
            return res;
        },

        ConditionalExpression: function ConditionalExpression(node, curStatus, c) {
            var res = Ĉ.get(node, curStatus.delta);
            c(node.test, curStatus, undefined);
            var cons = c(node.consequent, curStatus, undefined);
            var alt = c(node.alternate, curStatus, undefined);
            cons.propagate(res);
            alt.propagate(res);
            return res;
        },

        NewExpression: function NewExpression(node, curStatus, c) {
            var ret = Ĉ.get(node, curStatus.delta);
            var callee = c(node.callee, curStatus, undefined);
            var args = [];
            for (var i = 0; i < node.arguments.length; i++) {
                args.push(c(node.arguments[i], curStatus, undefined));
            }
            var newDelta = curStatus.delta.appendOne(node['@label']);
            callee.propagate(new cstr.IsCtor(args, ret, curStatus.exc, newDelta));
            return ret;
        },

        ArrayExpression: function ArrayExpression(node, curStatus, c) {
            var ret = Ĉ.get(node, curStatus.delta);
            // NOTE prototype object is not recorded in Ĉ
            var arrType = new types.ArrType(new types.AVal(rtCX.protos.Array));
            // add length property
            arrType.getProp('length').addType(types.PrimNumber);

            ret.addType(arrType);

            // add array elements
            for (var i = 0; i < node.elements.length; i++) {
                if (node.elements[i] == null) {
                    continue;
                }
                var eltAVal = c(node.elements[i], curStatus, undefined);

                var prop = i + '';
                ret.propagate(new cstr.WriteProp(prop, eltAVal));
                ret.propagate(new cstr.WriteProp(null, eltAVal));
            }
            return ret;
        },

        ObjectExpression: function ObjectExpression(node, curStatus, c) {
            var ret = Ĉ.get(node, curStatus.delta);
            // NOTE prototype object is not recorded in Ĉ
            var objType = new types.ObjType(new types.AVal(rtCX.protos.Object));
            ret.addType(objType);

            for (var i = 0; i < node.properties.length; i++) {
                var propPair = node.properties[i];
                var propKey = propPair.key;
                var _name = undefined;
                var propExpr = propPair.value;

                var fldAVal = c(propExpr, curStatus, undefined);

                if (propKey.type === 'Identifier') {
                    _name = propKey.name;
                } else if (typeof propKey.value === 'string') {
                    _name = propKey.value;
                } else if (typeof propKey.value === 'number') {
                    // convert number to string
                    _name = propKey.value + '';
                }
                ret.propagate(new cstr.WriteProp(_name, fldAVal));
            }
            return ret;
        },

        ArrowFunctionExpression: function ArrowFunctionExpression(node, curStatus, c) {
            if (!node.fnInstances) {
                node.fnInstances = [];
            }
            var fnInstance = null;
            node.fnInstances.forEach(function (fnType) {
                if (fnType.sc === curStatus.sc) {
                    fnInstance = fnType;
                }
            });
            if (!fnInstance) {
                fnInstance = new types.FnType(new types.AVal(rtCX.protos.Function), '[arrow function]', node.body['@block'].getParamVarNames(), curStatus.sc, node, undefined, curStatus.self // arrow function should remember AVal of outer this.
                );
                node.fnInstances.push(fnInstance);
            }
            var ret = Ĉ.get(node, curStatus.delta);
            ret.addType(fnInstance);

            ret.propagate(new cstr.IsCallee(types.AValNull, // nothing to propagate to self
            [], // no arguments
            types.AValNull, // return is ignored
            types.AValNull, // no valid caller with excAVal
            csc.CallSiteContext.nullContext // Using nullContext
            ));

            return ret;
        },

        FunctionExpression: function FunctionExpression(node, curStatus, c) {
            if (!node.fnInstances) {
                node.fnInstances = [];
            }
            var fnInstance = null;
            node.fnInstances.forEach(function (fnType) {
                if (fnType.sc === curStatus.sc) {
                    fnInstance = fnType;
                }
            });
            if (!fnInstance) {
                // NOTE prototype object is not recorded in Ĉ
                fnInstance = new types.FnType(new types.AVal(rtCX.protos.Function), '[anonymous function]', node.body['@block'].getParamVarNames(), curStatus.sc, node, rtCX.protos.Object);
                node.fnInstances.push(fnInstance);
                // NOTE prototype object is not recorded in Ĉ
                var prototypeObject = new types.ObjType(new types.AVal(rtCX.protos.Object), '.prototype');
                // For .prototype
                new types.AVal(fnInstance).propagate(new cstr.WriteProp('prototype', new types.AVal(prototypeObject)));
                // For .prototype.constructor
                var constructorProp = prototypeObject.getProp('constructor');
                constructorProp.addType(fnInstance);
            }
            var ret = Ĉ.get(node, curStatus.delta);
            ret.addType(fnInstance);

            // Call the function using nullContext

            var _fnInstance$getFunEnv = fnInstance.getFunEnv(csc.CallSiteContext.nullContext);

            var selfAVal = _fnInstance$getFunEnv[0];

            // add the function's instance
            selfAVal.addType(fnInstance.getInstance());
            ret.propagate(new cstr.IsCallee(types.AValNull, // nothing to propagate to self
            [], // no arguments
            types.AValNull, // return is ignored
            types.AValNull, // no valid caller with excAVal
            csc.CallSiteContext.nullContext // Using nullContext
            ));

            return ret;
        },

        FunctionDeclaration: function FunctionDeclaration(node, curStatus, c) {
            // Drop initial catch or normal scopes
            var sc0 = curStatus.sc.removeInitialCatchOrNormalBlocks();
            if (!node.fnInstances) {
                node.fnInstances = [];
            }
            var fnInstance = null;
            node.fnInstances.forEach(function (fnType) {
                if (fnType.sc === sc0) {
                    fnInstance = fnType;
                }
            });
            if (!fnInstance) {
                // NOTE prototype object is not recorded in Ĉ
                fnInstance = new types.FnType(new types.AVal(rtCX.protos.Function), node.id.name, node.body['@block'].getParamVarNames(), sc0, node, rtCX.protos.Object);
                node.fnInstances.push(fnInstance);
                // for each fnInstance, assign one prototype object
                // NOTE prototype object is not recorded in Ĉ
                var prototypeObject = new types.ObjType(new types.AVal(rtCX.protos.Object), node.id.name + '.prototype');
                // For .prototype
                new types.AVal(fnInstance).propagate(new cstr.WriteProp('prototype', new types.AVal(prototypeObject)));
                // For .prototype.constructor
                var constructorProp = prototypeObject.getProp('constructor');
                constructorProp.addType(fnInstance);
            }
            var lhsAVal = sc0.getAValOf(node.id.name);
            lhsAVal.addType(fnInstance);

            // Call the function using nullContext

            var _fnInstance$getFunEnv2 = fnInstance.getFunEnv(csc.CallSiteContext.nullContext);

            var selfAVal = _fnInstance$getFunEnv2[0];

            // add the function's instance
            selfAVal.addType(fnInstance.getInstance());
            lhsAVal.propagate(new cstr.IsCallee(types.AValNull, // nothing to propagate to self
            [], // no arguments
            types.AValNull, // return is ignored
            types.AValNull, // no valid caller with excAVal
            csc.CallSiteContext.nullContext // Using nullContext
            ));

            // nothing to return
            return types.AValNull;
        },

        SequenceExpression: function SequenceExpression(node, curStatus, c) {
            var lastIndex = node.expressions.length - 1;
            for (var i = 0; i < lastIndex; i++) {
                c(node.expressions[i], curStatus, undefined);
            }
            var lastAVal = c(node.expressions[lastIndex], curStatus, undefined);
            Ĉ.set(node, curStatus.delta, lastAVal);
            return lastAVal;
        },

        UnaryExpression: function UnaryExpression(node, curStatus, c) {
            c(node.argument, curStatus, undefined);
            var res = Ĉ.get(node, curStatus.delta);
            var type = unopResultType(node.operator);
            if (type) {
                res.addType(type);
            }
            return res;
        },

        UpdateExpression: function UpdateExpression(node, curStatus, c) {
            c(node.argument, curStatus, undefined);
            var res = Ĉ.get(node, curStatus.delta);
            res.addType(types.PrimNumber);
            // We ignore the effect of updating to number type
            return res;
        },

        BinaryExpression: function BinaryExpression(node, curStatus, c) {
            var lOprd = c(node.left, curStatus, undefined);
            var rOprd = c(node.right, curStatus, undefined);
            var res = Ĉ.get(node, curStatus.delta);

            if (node.operator == '+') {
                lOprd.propagate(new cstr.IsAdded(rOprd, res));
                rOprd.propagate(new cstr.IsAdded(lOprd, res));
            } else {
                if (binopIsBoolean(node.operator)) {
                    res.addType(types.PrimBoolean);
                } else {
                    res.addType(types.PrimNumber);
                }
            }
            return res;
        },

        ForStatement: function ForStatement(node, curStatus, c) {
            if (node['@block']) {
                // if it has @block property
                var forBlockSC = node['@block'].getScopeInstance(curStatus.sc, curStatus.delta);
                curStatus = curStatus.getNewStatus({ sc: forBlockSC });
            }
            walk.base.ForStatement(node, curStatus, c);
        },

        BlockStatement: function BlockStatement(node, curStatus, c) {
            if (node['@block']) {
                // if it has @block property
                var normalBlockSC = node['@block'].getScopeInstance(curStatus.sc, curStatus.delta);
                curStatus = curStatus.getNewStatus({ sc: normalBlockSC });
            }
            walk.base.BlockStatement(node, curStatus, c);
        },

        TryStatement: function TryStatement(node, curStatus, c) {
            // construct scope chain for catch block
            var catchBlockSC = node.handler.body['@block'].getScopeInstance(curStatus.sc, curStatus.delta);
            // get the AVal for exception parameter
            var excAVal = catchBlockSC.caughtAVal;

            // for try block
            var tryStatus = curStatus.getNewStatus({ exc: excAVal });
            c(node.block, tryStatus, undefined);

            // for catch block
            var catchStatus = curStatus.getNewStatus({ sc: catchBlockSC });
            connectPattern(node.handler.param, catchStatus, excAVal);
            c(node.handler.body, catchStatus, undefined);

            // for finally block
            if (node.finalizer !== null) c(node.finalizer, curStatus, undefined);
        },

        ThrowStatement: function ThrowStatement(node, curStatus, c) {
            var thr = c(node.argument, curStatus, undefined);
            thr.propagate(curStatus.exc);
        },

        CallExpression: function CallExpression(node, curStatus, c) {
            var resAVal = Ĉ.get(node, curStatus.delta);
            var argAVals = [];

            // get AVals for each arguments
            for (var i = 0; i < node.arguments.length; i++) {
                argAVals.push(c(node.arguments[i], curStatus, undefined));
            }
            // append current call site to the context
            var newDelta = curStatus.delta.appendOne(node['@label']);

            if (node.callee.type === 'MemberExpression') {
                // method call

                var _readMember2 = readMember(node.callee, curStatus, c);

                var recvAVal = _readMember2[0];
                var retAVal = _readMember2[1];

                retAVal.propagate(new cstr.IsCallee(recvAVal, argAVals, resAVal, curStatus.exc, newDelta));
            } else {
                // normal function call
                var calleeAVal = c(node.callee, curStatus, undefined);
                // callee의 return을 call expression으로
                // callee의 exception을 호출 측의 exception에 전달해야
                calleeAVal.propagate(new cstr.IsCallee(new types.AVal(rtCX.globalObject), argAVals, resAVal, curStatus.exc, newDelta));
            }
            return resAVal;
        },

        MemberExpression: function MemberExpression(node, curStatus, c) {
            var _readMember3 = readMember(node, curStatus, c);

            var retAVal = _readMember3[1];

            return retAVal;
        },

        ReturnStatement: function ReturnStatement(node, curStatus, c) {
            if (!node.argument) return;
            var ret = c(node.argument, curStatus, undefined);
            ret.propagate(curStatus.ret);
        }
    });

    var stmtExprWalker = function stmtExprWalker(node, curStatus) {
        return myWalker.recursiveWithReturn(node, curStatus, stmtExprWalk);
    };

    var outAVal = stmtExprWalker(astNode, initStatus);
    if (outAVal) {
        // must be an expression body
        outAVal.propagate(initStatus.ret);
    }
    // We actually added constraints
    return true;
}

},{"../domains/context":4,"../domains/types":6,"../util/myWalker":12,"./constraints":3,"acorn/dist/walk":17}],3:[function(require,module,exports){
/**
 * @file Defines CSTR and its subclasses.
 * @author sewon326.kim@samsung.com
 */

'use strict';
exports.__esModule = true;

function _interopRequireWildcard(obj) { if (obj && obj.__esModule) { return obj; } else { var newObj = {}; if (obj != null) { for (var key in obj) { if (Object.prototype.hasOwnProperty.call(obj, key)) newObj[key] = obj[key]; } } newObj['default'] = obj; return newObj; } }

function _inherits(subClass, superClass) { if (typeof superClass !== 'function' && superClass !== null) { throw new TypeError('Super expression must either be null or a function, not ' + typeof superClass); } subClass.prototype = Object.create(superClass && superClass.prototype, { constructor: { value: subClass, enumerable: false, writable: true, configurable: true } }); if (superClass) Object.setPrototypeOf ? Object.setPrototypeOf(subClass, superClass) : subClass.__proto__ = superClass; }

function _classCallCheck(instance, Constructor) { if (!(instance instanceof Constructor)) { throw new TypeError('Cannot call a class as a function'); } }

var _domainsTypes = require('../domains/types');

var types = _interopRequireWildcard(_domainsTypes);

var _domainsStatus = require('../domains/status');

var status = _interopRequireWildcard(_domainsStatus);

var _domainsContext = require('../domains/context');

var csc = _interopRequireWildcard(_domainsContext);

var _cGen = require('./cGen');

var cGen = _interopRequireWildcard(_cGen);

var CSTR = (function () {
    function CSTR() {
        _classCallCheck(this, CSTR);
    }

    /**
     * Checks the equality between CSTRs.
     * @param {CSTR} other
     * @return {boolean}
     */

    CSTR.prototype.equals = function equals(other) {
        return this === other;
    };

    /**
     * Adds type using the information of CSTR.
     * @abstract
     * @param {Type} type
     */

    CSTR.prototype.addType = function addType(type) {
        throw new Error("calling abstract method");
    };

    return CSTR;
})();

var ReadProp = (function (_CSTR) {
    _inherits(ReadProp, _CSTR);

    /**
     * Constructs ReadProp.
     * @param {string|null} prop
     * @param {AVal} to
     */

    function ReadProp(prop, to) {
        _classCallCheck(this, ReadProp);

        _CSTR.call(this);
        this.prop = prop;
        this.to = to;
    }

    /**
     * @override
     */

    ReadProp.prototype.addType = function addType(obj) {
        if (!(obj instanceof types.ObjType)) return;
        // when obj is ObjType,
        var ownProp = obj.getProp(this.prop, true);
        if (ownProp) {
            // when the object has the prop,
            ownProp.propagate(this.to);
        } else if (obj.getProp('__proto__', true)) {
            // Propagate from unknown prop if obj has it.
            if (obj.hasProp(null)) {
                obj.getProp(null, true).propagate(this.to);
            }
            // use prototype chain
            obj.getProp('__proto__').propagate(this);
        }
    };

    /**
     * @override
     */

    ReadProp.prototype.equals = function equals(other) {
        if (!(other instanceof ReadProp)) return false;
        return this.prop === other.prop && this.to.equals(other.to);
    };

    return ReadProp;
})(CSTR);

exports.ReadProp = ReadProp;

var WriteProp = (function (_CSTR2) {
    _inherits(WriteProp, _CSTR2);

    /**
     * Constructs WriteProp.
     * @param {string|null} prop
     * @param {AVal} from
     */

    function WriteProp(prop, from) {
        _classCallCheck(this, WriteProp);

        _CSTR2.call(this);
        this.prop = prop;
        this.from = from;
    }

    /**
     * @override
     */

    WriteProp.prototype.addType = function addType(obj) {
        if (!(obj instanceof types.ObjType)) return;
        var ownProp = obj.getProp(this.prop);
        this.from.propagate(ownProp);
        // Handle 'prototypeOf' when writing to 'prototype'
        if (this.prop === 'prototype') {
            this.from.getTypes().forEach(function (tp) {
                tp.prototypeOf.addType(obj);
            });
        }
        // When assigning FnType to a prop,
        this.from.getTypes().forEach(function (fn) {
            if (!(fn instanceof types.FnType)) return;
            // obj's prototypeOf => selfAVal of null context

            var _fn$getFunEnv = fn.getFunEnv(csc.CallSiteContext.nullContext);

            var selfAVal = _fn$getFunEnv[0];

            obj.prototypeOf.getTypes().forEach(function (ctor) {
                if (ctor instanceof types.FnType) selfAVal.addType(ctor.getInstance());
            });
        });
    };

    return WriteProp;
})(CSTR);

exports.WriteProp = WriteProp;

var IsAdded = (function (_CSTR3) {
    _inherits(IsAdded, _CSTR3);

    /**
     * Constructs IsAdded.
     * @param {AVal} other
     * @param {AVal} target
     */

    function IsAdded(other, target) {
        _classCallCheck(this, IsAdded);

        _CSTR3.call(this);
        this.other = other;
        this.target = target;
    }

    /**
     * @override
     */

    IsAdded.prototype.addType = function addType(type) {
        if ((type === types.PrimNumber || type === types.PrimBoolean) && (this.other.hasType(types.PrimNumber) || this.other.hasType(types.PrimBoolean))) {
            this.target.addType(types.PrimNumber);
        }
        if (type === types.PrimString && !this.other.isEmpty()) {
            this.target.addType(types.PrimString);
        }
    };

    return IsAdded;
})(CSTR);

exports.IsAdded = IsAdded;

function _prepareRestAValFromArgs(node, curStatus, args, startIndex) {
    var restAVal = cGen.getRestAVal(node, curStatus);
    for (var i = startIndex; i < args.length; i++) {
        restAVal.propagate(new WriteProp(String(i - startIndex), args[i]));
        restAVal.propagate(new WriteProp(null, args[i]));
    }
    return restAVal;
}

function _connectToParameter(params, funStatus, args) {
    for (var i = 0; i < args.length && i < params.length; i++) {
        if (params[i].type === 'RestElement') {
            var restAVal = _prepareRestAValFromArgs(params[i], funStatus, args, i);
            cGen.connectPattern(params[i], funStatus, restAVal);
            break;
        }
        // Using funStatus for analyzing defaults is safe
        cGen.connectPattern(params[i], funStatus, args[i]);
    }
}

var IsCallee = (function (_CSTR4) {
    _inherits(IsCallee, _CSTR4);

    /**
     * Constructs IsCallee.
     * @param {AVal} self
     * @param {Array.<AVal>} args
     * @param {AVal} ret
     * @param {AVal} exc
     * @param {CallSiteContext} delta
     */

    function IsCallee(self, args, ret, exc, delta) {
        _classCallCheck(this, IsCallee);

        _CSTR4.call(this);
        this.self = self;
        this.args = args;
        this.ret = ret;
        this.exc = exc;
        this.delta = delta;
    }

    /**
     * @override
     */

    IsCallee.prototype.addType = function addType(f) {
        if (!(f instanceof types.FnType)) return;
        var fBlock = f.originNode.body['@block'];
        var cBlock = fBlock.hasParamScope ? fBlock.paren : fBlock;
        var deltaFn = this.delta.truncateFor(f);

        var _f$getFunEnv = f.getFunEnv(deltaFn);

        var selfAVal = _f$getFunEnv[0];
        var retAVal = _f$getFunEnv[1];
        var excAVal = _f$getFunEnv[2];

        var newSC = cBlock.getScopeInstance(f.sc, deltaFn);
        var funStatus = new status.Status(selfAVal, retAVal, excAVal, deltaFn, newSC);

        // arrow function should use boundThis and ignore the receiver AVal
        var effectiveSelf = f.boundThis ? f.boundThis : this.self;
        effectiveSelf.propagate(selfAVal);

        _connectToParameter(f.originNode.params, funStatus, this.args);

        // for arguments object
        if (f.originNode.body['@block'].useArgumentsObject) {
            var argObj = f.getArgumentsObject(deltaFn);
            newSC.getAValOf('arguments').addType(argObj);
            for (var i = 0; i < this.args.length; i++) {
                this.args[i].propagate(argObj.getProp(i + ''));
                this.args[i].propagate(argObj.getProp(null));
            }
            argObj.getProp('callee').addType(f);
            argObj.getProp('length').addType(types.PrimNumber);
        }

        // constraint generation for the function body
        cGen.addConstraints(f.originNode.body, funStatus);

        // get return
        retAVal.propagate(this.ret);
        // get exception
        excAVal.propagate(this.exc);
    };

    return IsCallee;
})(CSTR);

exports.IsCallee = IsCallee;

var IsCtor = (function (_CSTR5) {
    _inherits(IsCtor, _CSTR5);

    /**
     * Constructs IsCtor.
     * @param {Array.<AVal>}args
     * @param {AVal} ret
     * @param {AVal} exc
     * @param {AVal} delta
     */

    function IsCtor(args, ret, exc, delta) {
        _classCallCheck(this, IsCtor);

        _CSTR5.call(this);
        this.args = args;
        this.ret = ret;
        this.exc = exc;
        this.delta = delta;
    }

    // ignore non object types

    /**
     * @override
     */

    IsCtor.prototype.addType = function addType(f) {
        // Only non-arrow functions can create instances.
        if (!(f instanceof types.FnType) || f.boundThis) {
            return;
        }
        var deltaFn = this.delta.truncateFor(f);

        var _f$getFunEnv2 = f.getFunEnv(deltaFn);

        var selfAVal = _f$getFunEnv2[0];
        var retAVal = _f$getFunEnv2[1];
        var excAVal = _f$getFunEnv2[2];

        var newSC = f.originNode.body['@block'].getScopeInstance(f.sc, deltaFn);
        var funStatus = new status.Status(selfAVal,
        // In constructor, we can explicitly return only ObjType.
        new IfObjType(retAVal), excAVal, deltaFn, newSC);
        // f's instance is bound to 'this.'
        var newObj = f.getInstance();
        selfAVal.addType(newObj);

        _connectToParameter(f.originNode.params, funStatus, this.args);

        // for arguments object
        if (f.originNode.body['@block'].useArgumentsObject) {
            var argObj = f.getArgumentsObject(deltaFn);
            newSC.getAValOf('arguments').addType(argObj);
            for (var i = 0; i < this.args.length; i++) {
                this.args[i].propagate(argObj.getProp(i + ''));
                this.args[i].propagate(argObj.getProp(null));
            }
            argObj.getProp('callee').addType(f);
            argObj.getProp('length').addType(types.PrimNumber);
        }

        // constraint generation for the function body
        cGen.addConstraints(f.originNode.body, funStatus);

        // provide two kinds of result of 'new'
        this.ret.addType(newObj);
        retAVal.propagate(this.ret);
        // get exception
        excAVal.propagate(this.exc);
    };

    return IsCtor;
})(CSTR);

exports.IsCtor = IsCtor;

var IfObjType = (function (_CSTR6) {
    _inherits(IfObjType, _CSTR6);

    /**
     * Constructs IfObjType.
     * @param {AVal} aval
     */

    function IfObjType(aval) {
        _classCallCheck(this, IfObjType);

        _CSTR6.call(this);
        this.aval = aval;
    }

    /**
     * @override
     */

    IfObjType.prototype.addType = function addType(type) {
        if (!(type instanceof types.ObjType)) return;
        this.aval.addType(type);
    };

    return IfObjType;
})(CSTR);

},{"../domains/context":4,"../domains/status":5,"../domains/types":6,"./cGen":2}],4:[function(require,module,exports){
/**
 * @file Defines context for k-CFA analysis
 * @author sewon326.kim@samsung.com
 */

/**
 * Initial sensitivity parameter.
 * @type {{maxDepthK: number, contextLengthOfFunc: sensitivityParameter.contextLengthOfFunc}}
 */
"use strict";

exports.__esModule = true;
exports.changeSensitivityParameter = changeSensitivityParameter;

function _classCallCheck(instance, Constructor) { if (!(instance instanceof Constructor)) { throw new TypeError("Cannot call a class as a function"); } }

var sensitivityParameter = {
    // maximum length of context
    maxDepthK: 0,
    //
    contextLengthOfFunc: function contextLengthOfFunc(fn) {
        return 0;
    }
};

exports.sensitivityParameter = sensitivityParameter;
/**
 * Changes the sensitivity parameter.
 * @param param
 */

function changeSensitivityParameter(param) {
    sensitivityParameter.maxDepthK = param.maxDepthK;
    sensitivityParameter.contextLengthOfFunc = param.contextLengthOfFunc;
}

var CallSiteContext = (function () {
    /**
     * Construct a CallSiteContext from `list`.
     * @param list
     */

    function CallSiteContext(list) {
        _classCallCheck(this, CallSiteContext);

        for (var _iterator = CallSiteContext.contextPool.values(), _isArray = Array.isArray(_iterator), _i = 0, _iterator = _isArray ? _iterator : _iterator[Symbol.iterator]();;) {
            var _ref;

            if (_isArray) {
                if (_i >= _iterator.length) break;
                _ref = _iterator[_i++];
            } else {
                _i = _iterator.next();
                if (_i.done) break;
                _ref = _i.value;
            }

            var ctx = _ref;

            if (ctx._hasSameList(list)) {
                // use existing context
                return ctx;
            }
        }
        // clone the given list
        if (list === null) {
            this.csList = null;
        } else {
            this.csList = list.slice(0);
        }
        // add the current instance to the pool
        CallSiteContext.contextPool.add(this);
    }

    /**
     * Declaring class fields for CallSiteContext
     * @static
     */

    /**
     * Check whether the list represent the same context.
     * @private
     * @param list - array composed of context elements
     * @return {boolean}
     */

    CallSiteContext.prototype._hasSameList = function _hasSameList(list) {
        if (this.csList === null) {
            return list === null;
        }
        if (list === null) {
            return this.csList === null;
        }
        if (this.csList.length !== list.length) {
            return false;
        }
        for (var i = 0; i < this.csList.length; i++) {
            if (this.csList[i] !== list[i]) return false;
        }
        return true;
    };

    /**
     * Returns the context which is myself + callSite.
     * If I am nullContext, the result is myself.
     * @param callSite - a call-site to append
     * @return {CallSiteContext}
     */

    CallSiteContext.prototype.appendOne = function appendOne(callSite) {
        // if null context, result is itself
        if (this === CallSiteContext.nullContext) {
            return this;
        }
        // use concat to create a new array
        // oldest one comes first
        var appended = this.csList.concat(callSite);
        if (appended.length > sensitivityParameter.maxDepthK) {
            appended.shift();
        }
        return new CallSiteContext(appended);
    };

    /**
     * Truncate context according to the given function.
     * @param {FnType} fn
     * @return {CallSiteContext}
     */

    CallSiteContext.prototype.truncateFor = function truncateFor(fn) {
        // for nullContext,
        if (this === CallSiteContext.nullContext) {
            return this;
        }
        // compute the length of the context
        var contextLength = sensitivityParameter.contextLengthOfFunc(fn);
        if (contextLength === 0) {
            // context of length 0
            return CallSiteContext.epsilonContext;
        } else {
            // choose last several call-sites
            return new CallSiteContext(this.csList.slice(-contextLength));
        }
    };

    /**
     * Returns the string representation
     * @return {string}
     */

    CallSiteContext.prototype.toString = function toString() {
        return this.csList.toString();
    };

    return CallSiteContext;
})();

exports.CallSiteContext = CallSiteContext;
CallSiteContext.contextPool = new Set();

/**
 * nullContext is for functions that never be called
 * @static
 */
CallSiteContext.nullContext = new CallSiteContext(null);

/**
 * epsilonContext is for context of length 0
 * @static
 */
CallSiteContext.epsilonContext = new CallSiteContext([]);

},{}],5:[function(require,module,exports){
/**
 * @file Defines Status.
 * @author sewon326.kim@samsung.com
 */
"use strict";

exports.__esModule = true;

function _classCallCheck(instance, Constructor) { if (!(instance instanceof Constructor)) { throw new TypeError("Cannot call a class as a function"); } }

var Status = (function () {
    /**
     * Constructs Status.
     * @param {AVal} self
     * @param {AVal} ret
     * @param {AVal} exc
     * @param {CallSiteContext} delta
     * @param {Scope} sc
     */

    function Status(self, ret, exc, delta, sc) {
        _classCallCheck(this, Status);

        this.self = self;
        this.ret = ret;
        this.exc = exc;
        this.delta = delta;
        this.sc = sc;
    }

    /**
     * Checks equality with other Status
     * @param {Status} other
     * @return {boolean}
     */

    Status.prototype.equals = function equals(other) {
        return this.self === other.self && this.ret === other.ret && this.exc === other.exc && this.delta === other.delta && this.sc === other.sc;
    };

    /**
     * Returns a new Status,
     * whose instance fields are changed from `this` using `changedStatus`.
     * @param changeStatus
     * @return {Status}
     */

    Status.prototype.getNewStatus = function getNewStatus(changeStatus) {
        var newStatus = new Status();
        for (var p in this) {
            if (this.hasOwnProperty(p)) {
                if (changeStatus.hasOwnProperty(p)) {
                    newStatus[p] = changeStatus[p];
                } else {
                    newStatus[p] = this[p];
                }
            }
        }
        return newStatus;
    };

    return Status;
})();

exports.Status = Status;

},{}],6:[function(require,module,exports){
/**
 * @file Defines domains for types.
 * @author sewon326.kim@samsung.com
 */

// for DEBUG
'use strict';

exports.__esModule = true;
exports.mkObjFromGlobalScope = mkObjFromGlobalScope;

function _inherits(subClass, superClass) { if (typeof superClass !== 'function' && superClass !== null) { throw new TypeError('Super expression must either be null or a function, not ' + typeof superClass); } subClass.prototype = Object.create(superClass && superClass.prototype, { constructor: { value: subClass, enumerable: false, writable: true, configurable: true } }); if (superClass) Object.setPrototypeOf ? Object.setPrototypeOf(subClass, superClass) : subClass.__proto__ = superClass; }

function _classCallCheck(instance, Constructor) { if (!(instance instanceof Constructor)) { throw new TypeError('Cannot call a class as a function'); } }

var count = 0;

/**
 * AVals represent sets of types.
 * Their forwards fields represent the propagation graph.
 */

var AVal = (function () {
    /**
     * Construct an AVal.
     * Parameter type is optional.
     * @param {Type} type - makes AVal containing the type
     */

    function AVal(type) {
        _classCallCheck(this, AVal);

        // type: contained types
        // We assume types are distinguishable by '==='
        if (type) this.types = new Set([type]);else this.types = new Set();
        // forwards: propagation targets
        // We assume targets are distinguishable by 'equals' method
        this.forwards = new Set();
        // for DEBUG
        this._id = count++;
    }

    /**
     * the super class of all types
     * each type should be distinguishable by '===' operation.
     */

    /**
     * Check whether it has any type
     * @return {boolean}
     */

    AVal.prototype.isEmpty = function isEmpty() {
        return this.types.size === 0;
    };

    /**
     * Returns the number of types it has.
     * @return {number}
     */

    AVal.prototype.getSize = function getSize() {
        return this.types.size;
    };

    /**
     * Returns the set of types.
     * @return {Set.<Type>}
     */

    AVal.prototype.getTypes = function getTypes() {
        return this.types;
    };

    /**
     * Checks whether it contains `type`.
     * @param {Type} type
     * @return {boolean}
     */

    AVal.prototype.hasType = function hasType(type) {
        return this.types.has(type);
    };

    /**
     * Add a type.
     * @param {Type} type
     * @return {boolean}
     */

    AVal.prototype.addType = function addType(type) {
        if (this.types.has(type)) {
            return false;
        }
        // given type is new
        this.types.add(type);
        // send to propagation targets
        this.forwards.forEach(function (fwd) {
            fwd.addType(type);
        });
        return true;
    };

    /**
     * @param {AVal} target
     */

    AVal.prototype.propagate = function propagate(target) {
        if (!this.addForward(target)) return;
        // target is newly added
        // send types to the new target
        this.types.forEach(function (type) {
            target.addType(type);
        });
    };

    /**
     * Add a propagation target
     * @param {AVal} fwd
     * @return {boolean} - returns false if it already has the target
     */

    AVal.prototype.addForward = function addForward(fwd) {
        for (var _iterator = this.forwards, _isArray = Array.isArray(_iterator), _i = 0, _iterator = _isArray ? _iterator : _iterator[Symbol.iterator]();;) {
            var _ref;

            if (_isArray) {
                if (_i >= _iterator.length) break;
                _ref = _iterator[_i++];
            } else {
                _i = _iterator.next();
                if (_i.done) break;
                _ref = _i.value;
            }

            var oldFwd = _ref;

            if (fwd.equals(oldFwd)) {
                return false;
            }
        }
        this.forwards.add(fwd);
        return true;
    };

    /**
     * Check if they are the same
     * @param {AVal} other
     * @return {boolean}
     */

    AVal.prototype.equals = function equals(other) {
        // simple reference comparison
        return this === other;
    };

    /**
     * TODO: check whether we really need this method.
     * @param {string|null} prop
     * @return {AVal}
     */

    AVal.prototype.getProp = function getProp(prop) {
        if (this.props.has(prop)) {
            return this.props.get(prop);
        } else {
            return AValNull;
        }
    };

    /**
     * Returns the string representation of the AVal
     * @return {string}
     */

    AVal.prototype.toString = function toString() {
        var visitedTypes = new Set();
        return this._toString(visitedTypes);
    };

    AVal.prototype._toString = function _toString(visitedTypes) {
        var typeStrings = [];
        for (var _iterator2 = this.types, _isArray2 = Array.isArray(_iterator2), _i2 = 0, _iterator2 = _isArray2 ? _iterator2 : _iterator2[Symbol.iterator]();;) {
            var _ref2;

            if (_isArray2) {
                if (_i2 >= _iterator2.length) break;
                _ref2 = _iterator2[_i2++];
            } else {
                _i2 = _iterator2.next();
                if (_i2.done) break;
                _ref2 = _i2.value;
            }

            var tp = _ref2;

            if (visitedTypes.has(tp)) {
                typeStrings.push('?');
            } else {
                typeStrings.push(tp._toString(visitedTypes));
            }
        }
        return typeStrings.join('|');
    };

    return AVal;
})();

exports.AVal = AVal;

var Type = (function () {
    /**
     * Create a new type
     * @param {string} name
     */

    function Type(name) {
        _classCallCheck(this, Type);

        this.name = name;
    }

    /**
     * 1. object types
     */

    /**
     * Returns the name of type
     * @return {string}
     */

    Type.prototype.getName = function getName() {
        return this.name;
    };

    /**
     * Default implementation for toString
     * This should be overridden for sophisticated types
     * @private
     * @return {string}
     */

    Type.prototype._toString = function _toString() {
        return this.getName();
    };

    return Type;
})();

var ObjType = (function (_Type) {
    _inherits(ObjType, _Type);

    /**
     * @param {AVal} proto - AVal of constructor's prototype
     * @param {string} name - guessed name
     */

    function ObjType(proto, name) {
        _classCallCheck(this, ObjType);

        _Type.call(this, name);
        this.props = new Map();
        // share proto with __proto__
        this.setProp('__proto__', proto);
        // remember whose prototype I am
        this.prototypeOf = new AVal();
    }

    /**
     * Makes an Obj from the global scope
     * @param {Scope} gScope - the global Scope object
     * @return {ObjType}
     */

    /**
     * @param {string|null} prop - null for computed props
     * @param {boolean} readOnly - if false, create AVal for prop if necessary
     * @return {AVal} AVal of the property
     */

    ObjType.prototype.getProp = function getProp(prop, readOnly) {
        if (this.props.has(prop)) {
            return this.props.get(prop);
        } else if (readOnly) {
            return null;
        } else {
            var newPropAVal = new AVal();
            this.props.set(prop, newPropAVal);
            return newPropAVal;
        }
    };

    /**
     * We use this function to share .prototype with instances __proto__
     * It is possible to use this function to merge AVals to optimize the analyzer.
     * @param {string|null} prop - null for computed props
     * @param {AVal} aval
     */

    ObjType.prototype.setProp = function setProp(prop, aval) {
        this.props.set(prop, aval);
    };

    /**
     * Returns iterator of its own property names
     * @return {Iterator.<string>}
     */

    ObjType.prototype.getOwnPropNames = function getOwnPropNames() {
        return this.props.keys();
    };

    /**
     * TODO: Check this function's necessity
     * @param {string|null} prop
     * @return {boolean}
     */

    ObjType.prototype.hasProp = function hasProp(prop) {
        return this.props.has(prop);
    };

    /**
     * TODO: Check this function's necessity
     * @param {Type} type
     * @param {string|null} prop
     */

    ObjType.prototype.addTypeToProp = function addTypeToProp(type, prop) {
        if (!this.props.has(prop)) {
            this.props.set(prop, new AVal());
        }
        if (this.props.get(prop).hasType(type)) return;
        this.props.get(prop).addType(type);
    };

    /**
     * TODO: Check this function's necessity
     * @param {AVal} aval
     * @param {string} prop
     */

    ObjType.prototype.joinAValToProp = function joinAValToProp(aval, prop) {
        var self = this;
        aval.getTypes().forEach(function (type) {
            self.addTypeToProp(type, prop);
        });
    };

    /**
     * Show object's own property names
     * @param {Set.<Type>} visitedTypes
     * @return {string}
     */

    ObjType.prototype._toString = function _toString(visitedTypes) {
        if (this.name === undefined) {
            var props = [];
            for (var _iterator3 = this.props.keys(), _isArray3 = Array.isArray(_iterator3), _i3 = 0, _iterator3 = _isArray3 ? _iterator3 : _iterator3[Symbol.iterator]();;) {
                var _ref3;

                if (_isArray3) {
                    if (_i3 >= _iterator3.length) break;
                    _ref3 = _iterator3[_i3++];
                } else {
                    _i3 = _iterator3.next();
                    if (_i3.done) break;
                    _ref3 = _i3.value;
                }

                var p = _ref3;

                // skipping __proto__
                if (p === '__proto__') continue;
                props.push(p);
            }
            return '{' + props.join() + '}';
        } else {
            return this.name;
        }
    };

    return ObjType;
})(Type);

exports.ObjType = ObjType;

function mkObjFromGlobalScope(gScope) {
    var gObj = new ObjType(AValNull, '*global scope*');
    gObj.props = gScope.varMap;
    // Override getProp method for global object
    // We ignore 'readOnly' parameter to always return its own prop AVal
    gObj.getProp = function (prop) {
        if (!gScope.vb.hasLocalVar(prop)) {
            // when we refer prop of the global object
            gScope.vb.addDeclaredLocalVar(prop);
        }
        return ObjType.prototype.getProp.call(this, prop);
    };
    return gObj;
}

/**
 * 2. primitive types
 */

var PrimType = (function (_Type2) {
    _inherits(PrimType, _Type2);

    /**
     * @param {string} name
     */

    function PrimType(name) {
        _classCallCheck(this, PrimType);

        _Type2.call(this, name);
    }

    /**
     * 3. function types
     * the name is used for the type of the instances from the function
     */
    return PrimType;
})(Type);

exports.PrimType = PrimType;

var FnType = (function (_ObjType) {
    _inherits(FnType, _ObjType);

    /**
     * @param {AVal} fn_proto - AVal for constructor's .prototype
     * @param {string} name - guessed name
     * @param {[string]} argNames - list of parameter names
     * @param {Scope} sc - functions scope chain, or closure
     * @param {node} originNode - AST node for the function
     * @param {Type} argProto - prototype for arguments object
     * @param {AVal} boundThis - remember thisAVal for arrow function
     */

    function FnType(fn_proto, name, argNames, sc, originNode, argProto, boundThis) {
        _classCallCheck(this, FnType);

        _ObjType.call(this, fn_proto, name);
        this.paramNames = argNames;
        this.sc = sc;
        this.originNode = originNode;
        if (argProto) {
            this.argProto = argProto;
        }
        if (boundThis) {
            this.boundThis = boundThis;
        }
        // funEnv : CallContext -> [self, ret, exc]
        this.funEnv = new Map();
    }

    /** 
     * 4. array types
     */

    /**
     * construct Status for function
     * @param {CallContext} delta - call context
     * @return {[AVal, AVal, AVal]} - for self, return and exception AVals
     */

    FnType.prototype.getFunEnv = function getFunEnv(delta) {
        if (this.funEnv.has(delta)) {
            return this.funEnv.get(delta);
        } else {
            var triple = [new AVal(), new AVal(), new AVal()];
            this.funEnv.set(delta, triple);
            return triple;
        }
    };

    /**
     * Returns the argument object for context delta
     * @param {CallSiteContext} delta
     * @return {ObjType}
     */

    FnType.prototype.getArgumentsObject = function getArgumentsObject(delta) {
        this.argObjMap = this.argObjMap || new Map();
        if (this.argObjMap.has(delta)) {
            return this.argObjMap.get(delta);
        } else {
            var argObj = new ObjType(new AVal(this.argProto), '*arguments object*');
            this.argObjMap.set(delta, argObj);
            return argObj;
        }
    };

    /**
     * get Object made by the function
     * TODO: use additional information to create multiple instances
     * @return {ObjType}
     */

    FnType.prototype.getInstance = function getInstance() {
        // objInstance is the object made by the function
        if (this.objInstance) return this.objInstance;
        // we unify constructor's .prototype and instance's __proto__
        this.objInstance = new ObjType(this.getProp('prototype'));
        return this.objInstance;
    };

    FnType.prototype._stringifyOneLevelStructure = function _stringifyOneLevelStructure(structure) {

        var params = structure.params.map(function (param) {
            if (param.type !== undefined) return param.name + ':' + param.type;else return param.name;
        });

        var resStr = 'fn(' + params.join(', ') + ')';
        if (structure.ret !== undefined) {
            resStr += ' -> ' + structure.ret;
        }
        return resStr;
    };

    FnType.prototype._toString = function _toString(visitedTypes) {
        if (visitedTypes.has(this)) {
            return '?';
        }
        var structure = this._getOneLevelStructure(visitedTypes);
        return this._stringifyOneLevelStructure(structure);
    };

    FnType.prototype._getOneLevelStructure = function _getOneLevelStructure(visitedTypes) {
        visitedTypes.add(this);
        var fBlock = this.originNode.body['@block'];
        var pBlock = fBlock.hasParamScope ? fBlock.paren : fBlock;
        var paramScopes = pBlock.getScopesWithParent(this.sc);
        var params = this.originNode.params;

        function _concatNameAndType(name, typeString) {
            return name + (typeString ? ':' + typeString : '');
        }

        function _patternName(pattern) {
            switch (pattern.type) {
                case 'Identifier':
                    return pattern.name;
                case 'AssignmentPattern':
                    return pattern.left.name;
                case 'ObjectPattern':
                    return '{' + pattern.properties.map(function (e) {
                        return _patternName(e.value);
                    }) + '}';
                case 'ArrayPattern':
                    return '[' + pattern.elements.map(_patternName) + ']';
                case 'RestElement':
                    return '...' + _patternName(pattern.argument);
            }
        }

        function _patternWithType(_x, _x2) {
            var _again = true;

            _function: while (_again) {
                var pattern = _x,
                    removeId = _x2;
                _again = false;

                switch (pattern.type) {
                    case 'Identifier':
                        if (removeId) return _getTypeStringForVar(pattern.name);else return _concatNameAndType(pattern.name, _getTypeStringForVar(pattern.name));
                    case 'AssignmentPattern':
                        _x = pattern.left;
                        _x2 = undefined;
                        _again = true;
                        continue _function;

                    case 'ObjectPattern':
                        return '{' + pattern.properties.map(function (e) {
                            return _patternWithType(e.value);
                        }) + '}';
                    case 'ArrayPattern':
                        return '[' + pattern.elements.map(function (e) {
                            return _patternWithType(e);
                        }) + ']';
                    case 'RestElement':
                        if (removeId) {
                            _x = pattern.argument;
                            _x2 = removeId;
                            _again = true;
                            continue _function;
                        } else {
                            return '...' + _patternWithType(pattern.argument);
                        }

                }
            }
        }

        function _getTypeStringForVar(varName) {
            var strings = [];
            var hasType = false;
            for (var _iterator4 = paramScopes, _isArray4 = Array.isArray(_iterator4), _i4 = 0, _iterator4 = _isArray4 ? _iterator4 : _iterator4[Symbol.iterator]();;) {
                var _ref4;

                if (_isArray4) {
                    if (_i4 >= _iterator4.length) break;
                    _ref4 = _iterator4[_i4++];
                } else {
                    _i4 = _iterator4.next();
                    if (_i4.done) break;
                    _ref4 = _i4.value;
                }

                var sc = _ref4;

                var aval = sc.getAValOf(varName);
                if (!aval.isEmpty()) {
                    strings.push(aval._toString(visitedTypes));
                    hasType = true;
                }
            }
            return hasType ? strings.join('|') : undefined;
        }

        var paramInfo = params.map(function (p) {
            return {
                name: _patternName(p),
                type: _patternWithType(p, true) };
        });

        // computing joined retAVal
        var retTypeStrings = [];
        var noRetTypes = true;
        for (var _iterator5 = this.funEnv.values(), _isArray5 = Array.isArray(_iterator5), _i5 = 0, _iterator5 = _isArray5 ? _iterator5 : _iterator5[Symbol.iterator]();;) {
            var _ref5;

            if (_isArray5) {
                if (_i5 >= _iterator5.length) break;
                _ref5 = _iterator5[_i5++];
            } else {
                _i5 = _iterator5.next();
                if (_i5.done) break;
                _ref5 = _i5.value;
            }

            var retAVal = _ref5[1];

            if (!retAVal.isEmpty()) {
                noRetTypes = false;
                retTypeStrings.push(retAVal._toString(visitedTypes));
            }
        }
        visitedTypes['delete'](this);
        return { params: paramInfo, ret: noRetTypes ? undefined : retTypeStrings.join('|') };
    };

    /**
     * Returns the parameter type strings and return type strings in an object
     * @return {{params, ret}|*}
     */

    FnType.prototype.getOneLevelStructure = function getOneLevelStructure() {
        var visitedTypes = new Set();
        return this._getOneLevelStructure(visitedTypes);
    };

    return FnType;
})(ObjType);

exports.FnType = FnType;

var ArrType = (function (_ObjType2) {
    _inherits(ArrType, _ObjType2);

    /**
     * Construct ArrType
     * @param {AVal} arr_proto
     */

    function ArrType(arr_proto) {
        _classCallCheck(this, ArrType);

        _ObjType2.call(this, arr_proto, 'Array');
    }

    // Make primitive types

    ArrType.prototype._toString = function _toString(visitedTypes) {
        if (visitedTypes.has(this)) {
            return '?';
        }
        visitedTypes.add(this);
        // prop null is used for array elements
        var eltTypes = this.getProp(null, true);
        var tpStr = '[' + eltTypes._toString(visitedTypes) + ']';
        visitedTypes['delete'](this);
        return tpStr;
    };

    return ArrType;
})(ObjType);

exports.ArrType = ArrType;
var PrimNumber = new PrimType('number');
exports.PrimNumber = PrimNumber;
var PrimString = new PrimType('string');
exports.PrimString = PrimString;
var PrimBoolean = new PrimType('boolean');

exports.PrimBoolean = PrimBoolean;
// AbsNull represents all empty abstract values.
var AValNull = new AVal();
exports.AValNull = AValNull;
// You should not add any properties to it.
AValNull.props = null;
// Adding types are ignored.
AValNull.addType = function () {};

var AbsCache = (function () {
    function AbsCache() {
        _classCallCheck(this, AbsCache);

        this.map = new Map();
    }

    /**
     * Get if one exists, if not create one
     * @param loc
     * @param ctx
     * @return {AVal}
     */

    AbsCache.prototype.get = function get(loc, ctx) {
        if (!this.map.has(loc)) {
            // create inner map
            this.map.set(loc, new Map());
        }
        var mapLoc = this.map.get(loc);
        if (!mapLoc.has(ctx)) {
            var av = new AVal();
            mapLoc.set(ctx, av);
            return av;
        } else {
            return mapLoc.get(ctx);
        }
    };

    /**
     * Use AVal made by others (e.g. scope)
     * @param loc
     * @param ctx
     * @param av
     */

    AbsCache.prototype.set = function set(loc, ctx, av) {
        if (!this.map.has(loc)) {
            // create inner map
            this.map.set(loc, new Map());
        }
        this.map.get(loc).set(ctx, av);
    };

    /**
     * Check whether it has one for loc and ctx
     * @param loc
     * @param ctx
     * @return {boolean}
     */

    AbsCache.prototype.has = function has(loc, ctx) {
        return this.map.has(loc) && this.map.get(loc).has(ctx);
    };

    /**
     * Merge all AVal of the loc
     * @param loc
     * @return {AVal}
     */

    AbsCache.prototype.getMergedAValOfLoc = function getMergedAValOfLoc(loc) {
        if (!this.map.has(loc)) {
            // no type is available
            return null;
        }
        var mergedAVal = new AVal();
        if (this.map.has(loc)) {
            for (var _iterator6 = this.map.get(loc).values(), _isArray6 = Array.isArray(_iterator6), _i6 = 0, _iterator6 = _isArray6 ? _iterator6 : _iterator6[Symbol.iterator]();;) {
                var _ref6;

                if (_isArray6) {
                    if (_i6 >= _iterator6.length) break;
                    _ref6 = _iterator6[_i6++];
                } else {
                    _i6 = _iterator6.next();
                    if (_i6.done) break;
                    _ref6 = _i6.value;
                }

                var av = _ref6;

                for (var _iterator7 = av.getTypes(), _isArray7 = Array.isArray(_iterator7), _i7 = 0, _iterator7 = _isArray7 ? _iterator7 : _iterator7[Symbol.iterator]();;) {
                    var _ref7;

                    if (_isArray7) {
                        if (_i7 >= _iterator7.length) break;
                        _ref7 = _iterator7[_i7++];
                    } else {
                        _i7 = _iterator7.next();
                        if (_i7.done) break;
                        _ref7 = _i7.value;
                    }

                    var tp = _ref7;

                    mergedAVal.addType(tp);
                }
            }
        }return mergedAVal;
    };

    return AbsCache;
})();

exports.AbsCache = AbsCache;

},{}],7:[function(require,module,exports){
/**
 * @file Defines functions that extract type information
 * @author sewon326.kim@samsung.com
 */

'use strict';

exports.__esModule = true;
exports.getTypeAtRange = getTypeAtRange;
exports.getFnTypeStructuresAt = getFnTypeStructuresAt;
exports.getPropFromNode = getPropFromNode;
exports.getCompletionAtPos = getCompletionAtPos;
exports.getDefinitionSitesAt = getDefinitionSitesAt;

function _interopRequireWildcard(obj) { if (obj && obj.__esModule) { return obj; } else { var newObj = {}; if (obj != null) { for (var key in obj) { if (Object.prototype.hasOwnProperty.call(obj, key)) newObj[key] = obj[key]; } } newObj['default'] = obj; return newObj; } }

var _utilMyWalker = require('./util/myWalker');

var myWalker = _interopRequireWildcard(_utilMyWalker);

var _domainsTypes = require('./domains/types');

var types = _interopRequireWildcard(_domainsTypes);

/**
 * Get types of expression at the given range
 * @param ast
 * @param Ĉ
 * @param start
 * @param end
 * @return {{hasType: boolean, typeString: string, nodeStart: number, nodeEnd: number}}
 */

function getTypeAtRange(ast, Ĉ, start, end) {
    'use strict';
    var node = myWalker.findSurroundingNode(ast, start, end);
    var nodeTypes = Ĉ.getMergedAValOfLoc(node);
    var hasType = undefined;
    var typeString = '';
    if (!nodeTypes) {
        hasType = false;
        typeString = 'No types at the given range';
    } else {
        hasType = true;
        typeString = nodeTypes.toString();
    }
    return {
        hasType: hasType,
        typeString: typeString,
        nodeStart: node.start,
        nodeEnd: node.end
    };
}

/**
 * Get the simple type structure for the function at `pos`.
 * @param ast
 * @param Ĉ
 * @param pos
 * @returns {Array}
 */

function getFnTypeStructuresAt(ast, Ĉ, pos) {
    var node = myWalker.findSurroundingNode(ast, pos, pos);
    var nodeTypes = Ĉ.getMergedAValOfLoc(node);
    var fnTypeStructures = [];

    nodeTypes.getTypes().forEach(function (fn) {
        if (fn instanceof types.FnType) {
            fnTypeStructures.push(fn.getOneLevelStructure());
        }
    });
    return fnTypeStructures;
}

function _computeIconOfProp(propMap) {
    var iconMap = new Map();

    function isObject(icon) {
        return icon === 'object' || icon === 'array' || icon === 'fn';
    }

    propMap.forEach(function (tps, p) {
        for (var _iterator = tps, _isArray = Array.isArray(_iterator), _i = 0, _iterator = _isArray ? _iterator : _iterator[Symbol.iterator]();;) {
            var _ref;

            if (_isArray) {
                if (_i >= _iterator.length) break;
                _ref = _iterator[_i++];
            } else {
                _i = _iterator.next();
                if (_i.done) break;
                _ref = _i.value;
            }

            var tp = _ref;

            var icon = undefined;
            if (tp === types.PrimNumber) icon = 'number';else if (tp === types.PrimBoolean) icon = 'bool';else if (tp === types.PrimString) icon = 'string';else if (tp instanceof types.FnType) icon = 'fn';else if (tp instanceof types.ArrType) icon = 'array';else if (tp instanceof types.ObjType) icon = 'object';

            if (!iconMap.has(p) || iconMap.get(p) === icon) {
                iconMap.set(p, icon);
                continue;
            }

            if (isObject(icon) && isObject(iconMap.get(p))) {
                iconMap.set(p, 'object');
            } else {
                iconMap.set(p, 'unknown');
                break;
            }
        }
        if (tps.size === 0) {
            iconMap.set(p, 'unknown');
        }
    });
    return iconMap;
}

/**
 * Get prop to icon map from given node
 * @param Ĉ - AbsCache
 * @param node - expression node
 * @return {Map.<string, string>} - Mapping from prop to icon
 */

function getPropFromNode(Ĉ, node) {
    // Since getTypeOfLoc can return null if node does not have any types
    var nodeTypes = Ĉ.getMergedAValOfLoc(node);
    var propMap = _getReadablePropMap(nodeTypes);
    return _computeIconOfProp(propMap);
}

/**
 * For debugging, show x
 * @param x
 */
function _SHOW(x) {
    console.info(x);
    return x;
}

/**
 * Returns the completion list at `pos`
 * @param result
 * @param {Array} pos
 */

function getCompletionAtPos(result, pos) {
    // find id or member node
    var nodeInfo = myWalker.findCompletionContext(result.AST, pos);

    if (nodeInfo.type === 'Identifier') {
        var prefix = undefined,
            from = undefined,
            to = undefined;

        if (nodeInfo.node === null) {
            prefix = '';
            from = pos;
            to = pos;
        } else if (myWalker.isDummyIdNode(nodeInfo.node)) {
            prefix = '';
            from = to = nodeInfo.node.end; // Here, end is correct for start position
        } else {
                prefix = nodeInfo.node.name;
                from = nodeInfo.node.start;
                to = nodeInfo.node.end;
            }
        var varMap = _computeIconOfProp(_getReadableVarMap(nodeInfo.vb));

        var list = [];
        for (var _iterator2 = varMap, _isArray2 = Array.isArray(_iterator2), _i2 = 0, _iterator2 = _isArray2 ? _iterator2 : _iterator2[Symbol.iterator]();;) {
            var _ref2;

            if (_isArray2) {
                if (_i2 >= _iterator2.length) break;
                _ref2 = _iterator2[_i2++];
            } else {
                _i2 = _iterator2.next();
                if (_i2.done) break;
                _ref2 = _i2.value;
            }

            var v = _ref2[0];
            var i = _ref2[1];

            if (v.startsWith(prefix)) {
                list.push({ text: v, icon: i });
            }
        }
        return _SHOW({ list: list, from: from, to: to });
    } else {
        // property completion
        var objectNode = nodeInfo.node.object;
        var props = getPropFromNode(result.Ĉ, objectNode);

        var propertyNode = nodeInfo.node.property;
        var prefix = undefined,
            from = undefined,
            to = undefined,
            filter = undefined;
        if (nodeInfo.type === 'usualProp') {
            var propName = propertyNode.name;
            if (myWalker.isDummyIdNode(propertyNode)) {
                prefix = '';
                from = propertyNode.end; // Here, end is correct for start position
            } else {
                    // prefix = propName.substr(0, pos - propertyNode.start);
                    prefix = propName;
                    from = propertyNode.start;
                }
            to = propertyNode.end;
            filter = function (p) {
                return (/^[$A-Z_][0-9A-Z_$]*$/i.test(p)
                );
            };
        } else if (nodeInfo.type === 'stringProp') {
            prefix = propertyNode.value;
            from = propertyNode.start + 1;
            to = propertyNode.end - 1;
            filter = function (p) {
                return true;
            };
        }

        var list = [];
        for (var _iterator3 = props, _isArray3 = Array.isArray(_iterator3), _i3 = 0, _iterator3 = _isArray3 ? _iterator3 : _iterator3[Symbol.iterator]();;) {
            var _ref3;

            if (_isArray3) {
                if (_i3 >= _iterator3.length) break;
                _ref3 = _iterator3[_i3++];
            } else {
                _i3 = _iterator3.next();
                if (_i3.done) break;
                _ref3 = _i3.value;
            }

            var p = _ref3[0];
            var i = _ref3[1];

            // unknown prop is null
            if (p !== null && p.startsWith(prefix) && filter(p)) {
                list.push({ text: p, icon: i });
            }
        }
        return _SHOW({ list: list, from: from, to: to });
    }
}

function _unionMap(m1, m2) {
    var ret = new Map();

    function unionSet(s1, s2) {
        var ret = new Set();
        if (s1) s1.forEach(function (e) {
            return ret.add(e);
        });
        if (s2) s2.forEach(function (e) {
            return ret.add(e);
        });
        return ret;
    }

    if (m1) m1.forEach(function (ts, p) {
        return ret.set(p, ts);
    });
    if (m2) m2.forEach(function (ts, p) {
        return ret.set(p, unionSet(ret.get(p), m2.get(p)));
    });
    return ret;
}

function _addOnlyMissingMappings(m1, m2) {
    var ret = new Map();
    m1.forEach(function (ts, p) {
        return ret.set(p, ts);
    });
    m2.forEach(function (ts, p) {
        if (!ret.has(p)) ret.set(p, ts);
    });
    return ret;
}

// convert a map of A -> AVal
// to a map of A -> Set.<Type>
function _convertMap(map) {
    var retMap = new Map();
    map.forEach(function (av, p) {
        retMap.set(p, av.getTypes());
    });
    return retMap;
}

// traverse abstract heap space
function _getReadablePropMap(tps) {

    var visitedTypes = [];

    function traverse(type) {
        if (type instanceof types.ObjType && type.getProp('__proto__', true)) {
            var _ret = (function () {
                var protoMap = new Map();
                var protoTypes = type.getProp('__proto__', true).getTypes();

                protoTypes.forEach(function (tp) {
                    if (visitedTypes.indexOf(tp) > -1) {
                        return;
                    }
                    visitedTypes.push(tp);
                    protoMap = _unionMap(protoMap, traverse(tp));
                    visitedTypes.pop();
                });
                return {
                    v: _addOnlyMissingMappings(_convertMap(type.props), protoMap)
                };
            })();

            if (typeof _ret === 'object') return _ret.v;
        } else {
            return new Map();
        }
    }

    var retMap = new Map();
    tps.getTypes().forEach(function (tp) {
        retMap = _unionMap(retMap, traverse(tp));
    });

    return retMap;
}

/**
 * Returns the definition sites of functions at `pos`.
 * @param ast
 * @param Ĉ
 * @param pos
 * @returns {Array}
 */

function getDefinitionSitesAt(ast, Ĉ, pos) {
    var node = myWalker.findSurroundingNode(ast, pos, pos);
    var nodeTypes = Ĉ.getMergedAValOfLoc(node);

    var ranges = [];
    if (nodeTypes === null) {
        return ranges;
    }
    nodeTypes.getTypes().forEach(function (tp) {
        if (tp instanceof types.FnType && tp.originNode) {
            var fnNode = tp.originNode;
            var at = undefined;
            switch (fnNode.type) {
                case 'FunctionExpression':
                    at = fnNode.start;break;
                case 'FunctionDeclaration':
                    at = fnNode.id.start;break;
            }
            var item = { start: fnNode.start, end: fnNode.end, at: at };
            ranges.push(item);
        }
    });
    return ranges;
}

// traverse abstract stack space
function _getReadableVarMap(vb) {
    var currVB = vb;
    var retMap = new Map();
    while (currVB !== null) {
        var mergedMap = new Map();
        for (var _iterator4 = currVB.instances.values(), _isArray4 = Array.isArray(_iterator4), _i4 = 0, _iterator4 = _isArray4 ? _iterator4 : _iterator4[Symbol.iterator]();;) {
            var _ref4;

            if (_isArray4) {
                if (_i4 >= _iterator4.length) break;
                _ref4 = _iterator4[_i4++];
            } else {
                _i4 = _iterator4.next();
                if (_i4.done) break;
                _ref4 = _i4.value;
            }

            var varMap = _ref4;

            mergedMap = _unionMap(mergedMap, _convertMap(varMap));
        }
        retMap = _addOnlyMissingMappings(retMap, mergedMap);
        currVB = currVB.paren;
    }
    return retMap;
}

},{"./domains/types":6,"./util/myWalker":12}],8:[function(require,module,exports){
/**
 * @file Some helper functions
 * @author sewon326.kim@samsung.com
 */

'use strict';

exports.__esModule = true;
exports.getNodeList = getNodeList;
exports.showUnfolded = showUnfolded;
var util = require('util');

function getNodeList(ast, startNum) {
    var nodeList = [];

    var num = startNum === undefined ? 0 : startNum;

    function assignId(node) {
        node['@label'] = num;
        nodeList.push(node);
        num++;
    }

    // Label every AST node with property 'type'
    function labelNodeWithType(node) {
        if (node && node.hasOwnProperty('type')) {
            assignId(node);
        }
        if (node && typeof node === 'object') {
            for (var p in node) {
                labelNodeWithType(node[p]);
            }
        }
    }

    labelNodeWithType(ast);

    return nodeList;
}

function showUnfolded(obj) {
    console.log(util.inspect(obj, { depth: null }));
}

},{"util":21}],9:[function(require,module,exports){
/**
 * @file Defines `analyze` function and exports query functions
 * @author sewon326.kim@samsung.com
 */

// import necessary libraries
'use strict';

exports.__esModule = true;
exports.analyze = analyze;

function _interopRequireWildcard(obj) { if (obj && obj.__esModule) { return obj; } else { var newObj = {}; if (obj != null) { for (var key in obj) { if (Object.prototype.hasOwnProperty.call(obj, key)) newObj[key] = obj[key]; } } newObj['default'] = obj; return newObj; } }

var _domainsTypes = require('./domains/types');

var types = _interopRequireWildcard(_domainsTypes);

var _domainsContext = require('./domains/context');

var context = _interopRequireWildcard(_domainsContext);

// const status = require('./domains/status');

var _domainsStatus = require('./domains/status');

var status = _interopRequireWildcard(_domainsStatus);

var _varBlock = require('./varBlock');

var varBlock = _interopRequireWildcard(_varBlock);

var _utilMyWalker = require('./util/myWalker');

var myWalker = _interopRequireWildcard(_utilMyWalker);

var _getTypeData = require('./getTypeData');

var getTypeData = _interopRequireWildcard(_getTypeData);

var _defaultOption = require('../defaultOption');

var defaultOption = _interopRequireWildcard(_defaultOption);

/**
 * Analyze a JavaScript code
 * @param {string} input - program code
 * @param {boolean} retAll - whether to return all analyzed data
 * @param option - analysis option
 * @returns {*}
 */
var acorn = require('acorn/dist/acorn');
var acorn_loose = require('acorn/dist/acorn_loose');
var aux = require('./helper');

var cGen = require('./constraint/cGen');
var varRefs = require('./varrefs');
var retOccur = require('./retOccur');
var thisOccur = require('./thisOccur');

function analyze(input, retAll, option) {
    // the Scope object for global scope
    // scope.Scope.globalScope = new scope.Scope(null);

    if (option === undefined) {
        // if no option is given, use the default option
        option = defaultOption.options;
    }
    // parsing input program
    var ast;
    try {
        ast = acorn.parse(input, option.acornOption);
    } catch (e) {
        ast = acorn_loose.parse_dammit(input, option.acornOption);
    }

    var nodeArrayIndexedByList = aux.getNodeList(ast);

    // Show AST before scope resolution
    // aux.showUnfolded(ast);

    var gVarBlock = new varBlock.VarBlock(null, ast, varBlock.VarBlock.blockTypes.globalBlock,
    // 'use strict' directive is checked in annotateBlockInfo.
    option.acornOption.sourceType === 'module');

    varBlock.annotateBlockInfo(ast, gVarBlock);

    // Setting up the sensitivity parameter
    // It is possible to compute the parameter by examining the code.
    context.changeSensitivityParameter(option.sensitivityParameter);

    var gBlock = ast['@block'];
    var initialContext = context.CallSiteContext.epsilonContext;
    var gScope = gBlock.getScopeInstance(null, initialContext);
    var gObject = types.mkObjFromGlobalScope(gScope);
    var initStatus = new status.Status(new types.AVal(gObject), types.AValNull, types.AValNull, initialContext, gScope);
    // the prototype object of Object
    var ObjProto = new types.ObjType(null, 'Object.prototype');
    var rtCX = {
        globalObject: gObject,
        // temporal
        protos: {
            Object: ObjProto,
            Function: new types.ObjType(new types.AVal(ObjProto), 'Function.prototype'),
            Array: new types.ObjType(new types.AVal(ObjProto), 'Array.prototype'),
            RegExp: new types.ObjType(new types.AVal(ObjProto), 'RegExp.prototype'),
            String: new types.ObjType(new types.AVal(ObjProto), 'String.prototype'),
            Number: new types.ObjType(new types.AVal(ObjProto), 'Number.prototype'),
            Boolean: new types.ObjType(new types.AVal(ObjProto), 'Boolean.prototype')
        },
        Ĉ: new types.AbsCache(),
        option: option
    };
    cGen.addConstraints(ast, initStatus, rtCX);
    //aux.showUnfolded(gBlockAndAnnotatedAST.ast);
    // aux.showUnfolded(constraints);
    // aux.showUnfolded(gBlock);
    // console.log(util.inspect(gBlock, {depth: 10}));
    if (retAll) {
        return {
            gObject: gObject,
            AST: ast,
            gBlock: gBlock,
            gScope: gScope,
            Ĉ: rtCX.Ĉ
        };
    } else {
        return gObject;
    }
}

// exports query functions
exports.findIdentifierAt = myWalker.findIdentifierAt;
exports.findVarRefsAt = varRefs.findVarRefsAt;
exports.onEscapingStatement = retOccur.onEscapingStatement;
exports.findEscapingStatements = retOccur.findEscapingStatements;
exports.onThisKeyword = thisOccur.onThisKeyword;
exports.findThisExpressions = thisOccur.findThisExpressions;
exports.findSurroundingNode = myWalker.findSurroundingNode;
exports.findMemberOrVariableAt = myWalker.findMemberOrVariableAt;
exports.getTypeData = getTypeData.getTypeAtRange;
exports.getCompletionAtPos = getTypeData.getCompletionAtPos;
exports.getFnTypeStructuresAt = getTypeData.getFnTypeStructuresAt;
exports.getDefinitionSitesAt = getTypeData.getDefinitionSitesAt;

},{"../defaultOption":1,"./constraint/cGen":2,"./domains/context":4,"./domains/status":5,"./domains/types":6,"./getTypeData":7,"./helper":8,"./retOccur":10,"./thisOccur":11,"./util/myWalker":12,"./varBlock":13,"./varrefs":14,"acorn/dist/acorn":15,"acorn/dist/acorn_loose":16}],10:[function(require,module,exports){
/**
 * @file Implements return / escaping statements finder
 * @author sewon326.kim@samsung.com
 */

'use strict';

exports.__esModule = true;
exports.onEscapingStatement = onEscapingStatement;
exports.findEscapingStatements = findEscapingStatements;

function _interopRequireWildcard(obj) { if (obj && obj.__esModule) { return obj; } else { var newObj = {}; if (obj != null) { for (var key in obj) { if (Object.prototype.hasOwnProperty.call(obj, key)) newObj[key] = obj[key]; } } newObj['default'] = obj; return newObj; } }

var _utilMyWalker = require('./util/myWalker');

var myWalker = _interopRequireWildcard(_utilMyWalker);

/**
 * auxiliary function for visitor's state change
 * @param node
 * @param st
 * @param nodeType
 * @return {*}
 */
var walk = require('acorn/dist/walk');
function _stChange(node, st, nodeType) {
    var fnNode = st[0];
    var tryNode = st[1];
    var outerTryNode = st[2];

    switch (nodeType) {
        case 'FunctionDeclaration':
        case 'FunctionExpression':
        case 'ArrowFunctionExpression':
            return [node, undefined];
        case 'TryStatement':
            // remember outer tryNode
            return [fnNode, node, tryNode];
        case 'CatchClause':
            // use outer try as its tryNode
            return [fnNode, outerTryNode];
        case 'BlockStatement':
            if (st.outer) {
                // it's finally block
                return [fnNode, outerTryNode];
            } else {
                // it's try block
                return [fnNode, tryNode, outerTryNode];
            }
        default:
            return [fnNode, tryNode, outerTryNode];
    }
}

/**
 * Check whether given pos is on a function keyword
 * @param ast - AST of a program
 * @param pos - index position
 * @return {*} - function node or null
 */

function onEscapingStatement(ast, pos) {
    'use strict';

    // find function node
    // st is the enclosing function
    var walker = myWalker.wrapWalker(walk.make({
        TryStatement: function TryStatement(node, st, c) {
            c(node.block, st);
            // set flag after processing try block
            st.outer = true;
            if (node.handler) c(node.handler, st);
            if (node.finalizer) c(node.finalizer, st);
        },
        CatchClause: function CatchClause(node, st, c) {
            c(node.body, st);
        }
    }, walk.base),
    // pre
    function (node, st, nodeType) {
        if (node.start > pos || node.end < pos) {
            return false;
        }

        // on a function keyword, 8 is the length of 'function'
        // or on return keyword, 6 is the length of 'return'
        // or on throw keyword, 5 is the length of 'throw'
        if ((nodeType === 'FunctionDeclaration' || nodeType === 'FunctionExpression') && (node.start <= pos && pos <= node.start + 8) || nodeType === 'ReturnStatement' && (node.start <= pos && pos <= node.start + 6) || nodeType === 'ThrowStatement' && (node.start <= pos && pos <= node.start + 5)) {
            // record the found node type
            st.type = node.type;
            throw st;
        }
        return true;
    },
    // post
    undefined, _stChange);

    try {
        walk.recursive(ast, [], walker);
    } catch (e) {
        if (e && e instanceof Array) {
            // found
            return e;
        } else {
            // other error
            throw e;
        }
    }
    // identifier not found
    return null;
}

/**
 * Given a node, find its escaping nodes
 *
 * @param nodePair - AST node of a function, possibly with no annotation
 * @return {*} - array of AST nodes
 */
function _getEscapingNodes(nodePair) {
    'use strict';
    var nodes = [];
    var fnNode = nodePair[0];
    var tryNode = nodePair[1];

    var walker = myWalker.wrapWalker(walk.make({
        TryStatement: function TryStatement(node, st, c) {
            c(node.block, st);
            // set flag after processing try block
            st.outer = true;
            // visit those BlockStatement
            if (node.handler) c(node.handler, st);
            if (node.finalizer) c(node.finalizer, st);
        },
        ReturnStatement: function ReturnStatement(node) {
            if (nodePair.type === 'ThrowStatement' && tryNode) return;
            nodes.push(node);
        },
        Function: function Function() {
            // not visit inner functions
        },
        ThrowStatement: function ThrowStatement(node, _ref) {
            var f = _ref[0];
            var t = _ref[1];

            if (nodePair.type === 'ThrowStatement' && tryNode === t || t === undefined) {
                nodes.push(node);
            }
        },
        CatchClause: function CatchClause(node, st, c) {
            c(node.body, st);
        }
    }, walk.base), undefined, undefined, _stChange);

    if (nodePair.type === 'ThrowStatement' && tryNode) {
        walk.recursive(tryNode.block, [undefined, tryNode], walker);
    } else {
        walk.recursive(fnNode.body, [fnNode, undefined], walker);
    }

    return nodes;
}

/**
 * Find return nodes corresponding to the position
 * if the pos is on a function keyword
 *
 * @param ast - AST node of a program, possibly with no annotation
 * @param pos - cursor position
 * @param includeKeyword - whether to include keyword range
 * @return {Array} - array of AST nodes of escaping statements
 */

function findEscapingStatements(ast, pos, includeKeyword) {
    'use strict';

    var nodePair = onEscapingStatement(ast, pos);
    if (!nodePair) {
        return null;
    }

    var ranges = _getEscapingNodes(nodePair).map(function (node) {
        return { start: node.start, end: node.end };
    });
    var fnNode = nodePair[0];
    var tryNode = nodePair[1];

    // If no explicit escaping exists
    // highlight the closing brace of the function body
    if (nodePair.type !== 'ThrowStatement' && ranges.length === 0) {
        ranges.push({ start: fnNode.end - 1, end: fnNode.end });
    }

    // highlighting 'catch'
    if (nodePair.type === 'ThrowStatement' && tryNode) {
        ranges.push({ start: tryNode.handler.start, end: tryNode.handler.start + 5 });
    } else if (includeKeyword) {
        if (fnNode.type !== 'ArrowFunctionExpression') {
            // add ranges for 'function'
            ranges.push({ start: fnNode.start, end: fnNode.start + 8 });
        } else {
            // TODO: add range for fat arrow
        }
    }
    return ranges;
}

},{"./util/myWalker":12,"acorn/dist/walk":17}],11:[function(require,module,exports){
/**
 * @file Implements this occurrence finder
 * @author sewon326.kim@samsung.com
 */

'use strict';

exports.__esModule = true;
exports.onThisKeyword = onThisKeyword;
exports.findThisExpressions = findThisExpressions;

function _interopRequireWildcard(obj) { if (obj && obj.__esModule) { return obj; } else { var newObj = {}; if (obj != null) { for (var key in obj) { if (Object.prototype.hasOwnProperty.call(obj, key)) newObj[key] = obj[key]; } } newObj['default'] = obj; return newObj; } }

var _utilMyWalker = require('./util/myWalker');

var myWalker = _interopRequireWildcard(_utilMyWalker);

/**
 * Check whether given pos is on a this keyword
 * @param ast - AST of a program
 * @param pos - index position
 * @return {*} - function node or null
 */
var walk = require('acorn/dist/walk');

function onThisKeyword(ast, pos) {
    'use strict';

    // find function node
    // st is the enclosing function
    var walker = myWalker.wrapWalker(walk.base,
    // pre
    function (node, st) {
        if (node.start > pos || node.end < pos) {
            return false;
        }

        if (node.type === 'ThisExpression') {
            throw st;
        }
        return true;
    },
    // post
    undefined,
    // stChange
    function (node, st) {
        if (node.type === 'FunctionDeclaration' || node.type === 'FunctionExpression') {
            return node;
        } else {
            return st;
        }
    });

    try {
        walk.recursive(ast, undefined, walker);
    } catch (e) {
        if (e && e.type && (e.type === 'FunctionExpression' || e.type === 'FunctionDeclaration')) {
            return e;
        } else {
            throw e;
        }
    }
    // identifier not found
    return null;
}

/**
 * Given a function node, find its this nodes
 *
 * @param fNode - AST node of a function, possibly with no annotation
 * @return {*} - array of AST nodes
 */
function _getThisNodes(fNode) {
    'use strict';
    var rets = [];
    if (fNode.type !== 'FunctionExpression' && fNode.type !== 'FunctionDeclaration') {
        throw Error('fNode should be a function node');
    }

    var walker = walk.make({
        ThisExpression: function ThisExpression(node) {
            return rets.push(node);
        },
        FunctionDeclaration: function FunctionDeclaration() {
            // not visit function declaration
        },
        FunctionExpression: function FunctionExpression() {
            // not visit function expression
        }
    }, walk.base);

    walk.recursive(fNode.body, undefined, walker);

    return rets;
}

/**
 * Find this nodes if the pos is on a this keyword
 *
 * @param ast - AST node of a program, possibly with no annotation
 * @param pos - cursor position
 * @param includeFunctionKeyword - whether to include function keyword range
 * @return {Array} - array of AST nodes of return statements
 */

function findThisExpressions(ast, pos, includeFunctionKeyword) {
    'use strict';

    var fNode = onThisKeyword(ast, pos);
    if (!fNode) {
        // pos is not on this keyword
        return null;
    }

    var rets = _getThisNodes(fNode);
    if (includeFunctionKeyword) {
        rets.push({ start: fNode.start, end: fNode.start + 8 });
    }
    return rets;
}

},{"./util/myWalker":12,"acorn/dist/walk":17}],12:[function(require,module,exports){
/**
 * @file Defines simple walkers for analysis
 * @author sewon326.kim@samsung.com
 */

'use strict';

exports.__esModule = true;
exports.patternHasDefaults = patternHasDefaults;
exports.wrapWalker = wrapWalker;
exports.isDummyIdNode = isDummyIdNode;
exports.findIdentifierAt = findIdentifierAt;
exports.findMemberOrVariableAt = findMemberOrVariableAt;
exports.findCompletionContext = findCompletionContext;
exports.findSurroundingNode = findSurroundingNode;
exports.recursiveWithReturn = recursiveWithReturn;

function _classCallCheck(instance, Constructor) { if (!(instance instanceof Constructor)) { throw new TypeError('Cannot call a class as a function'); } }

var walk = require('acorn/dist/walk');

/**
 * Returns a walker that does nothing for each node.
 * Use as a base walker when you need to walk on only some types of nodes.
 * @return {Object}
 */
function makeNoopWalker() {
    var walker = Object.create(null);
    var noopFunc = function noopFunc() {};
    for (var _name in Object.getOwnPropertyNames(walk.base)) {
        walker[_name] = noopFunc;
    }
    return walker;
}

/**
 * a walker that does nothing for each node
 */
var noopWalker = makeNoopWalker();

exports.noopWalker = noopWalker;
/**
 * Check whether the pattern uses defaults
 * @param ptnNode - a pattern node
 * @return {boolean}
 */

function patternHasDefaults(ptnNode) {
    var assignmentPatternFinder = walk.make(noopWalker, {
        AssignmentPattern: function AssignmentPattern(node, st, c) {
            throw new Found();
        },
        ObjectPattern: walk.base.ObjectPattern,
        ArrayPattern: walk.base.ArrayExpression,
        RestElement: walk.base.RestElement
    });

    try {
        walk.recursive(ptnNode, undefined, assignmentPatternFinder);
    } catch (e) {
        if (e instanceof Found) {
            return true;
        }
    }
    return false;
}

/**
 * a walker that visits each id even though it is var declaration
 * the parameter vb denote varBlock
 */
var varWalker = walk.make({
    Function: function Function(node, vb, c) {
        if (node.id) c(node.id, vb, 'Pattern');
        var paramVb = node['@block'] || node.body['@block'];
        for (var i = 0; i < node.params.length; i++) {
            c(node.params[i], paramVb, 'Pattern');
        }
        var innerVb = node.body['@block'];
        c(node.body, innerVb, node.expression ? 'ScopeExpression' : 'ScopeBody');
    },
    ForStatement: function ForStatement(node, vb, c) {
        var innerVb = node['@block'] || vb;
        // Use ForStatement of base walker
        walk.base.ForStatement(node, innerVb, c);
    },
    BlockStatement: function BlockStatement(node, vb, c) {
        var innerVb = node['@block'] || vb;
        // Use BlockStatement of base walker
        walk.base.BlockStatement(node, innerVb, c);
    },
    TryStatement: function TryStatement(node, vb, c) {
        c(node.block, vb);
        if (node.handler) {
            // Do not visit parameter with current vb
            // the parameter will be visited in CatchClause with changed vb
            c(node.handler, vb);
        }
        if (node.finalizer) {
            c(node.finalizer, vb);
        }
    },
    CatchClause: function CatchClause(node, vb, c) {
        var catchVb = node.body['@block'];
        // Need to handle the parameter in changed block
        c(node.param, catchVb);
        c(node.body, catchVb);
    },
    VariablePattern: function VariablePattern(node, vb, c) {
        // Note that walk.base.Identifier is 'ignore.'
        // varWalker should visit variables in LHS.
        c(node, vb, 'Identifier');
    }
});

exports.varWalker = varWalker;
/**
 * Wrap a walker with pre- and post- actions
 *
 * @param walker - base walker
 * @param preNode - Apply before visiting the current node.
 * If returns false, do not visit the node.
 * @param postNode - Apply after visiting the current node.
 * If given, return values are overridden.
 * @param stChange - state change function
 * @return {*} - a new walker
 */

function wrapWalker(walker, preNode, postNode, stChange) {
    'use strict';
    var retWalker = {};
    // wrapping each function preNode and postNode

    var _loop = function (nodeType) {
        if (!walker.hasOwnProperty(nodeType)) {
            return 'continue';
        }
        retWalker[nodeType] = function (node, st, c) {
            var ret = undefined;
            var newSt = st;
            if (stChange) {
                newSt = stChange(node, st, nodeType);
            }
            if (!preNode || preNode(node, newSt, nodeType)) {
                ret = walker[nodeType](node, newSt, c);
            } else {
                return;
            }
            if (postNode) {
                ret = postNode(node, newSt, nodeType);
            }
            return ret;
        };
    };

    for (var nodeType in walker) {
        var _ret = _loop(nodeType);

        if (_ret === 'continue') continue;
    }
    return retWalker;
}

/**
 * A utility class for searching ASTs.
 * We use info to record any useful information.
 */

var Found =
/**
 * @param info - any information to remember
 */
function Found(info) {
    _classCallCheck(this, Found);

    this.info = info;
}

/**
 * Checks whether it is a dummy Id node.
 * @param node
 * @return {boolean}
 */
;

exports.Found = Found;

function isDummyIdNode(node) {
    if (node.type !== 'Identifier') {
        throw new Error('Should be an Identifier node');
    }
    return node.name === '✖' && node.start >= node.end;
}

/**
 * Finds an identifier node at `pos`.
 * @param ast
 * @param pos
 * @return {*}
 */

function findIdentifierAt(ast, pos) {
    'use strict';
    return findNodeAt(ast, pos, function (node) {
        return node.type === 'Identifier' && !isDummyIdNode(node);
    });
}

/**
 * Returns a node at `pos` if it is member expr or variable.
 * @param ast
 * @param pos
 * @return {*}
 */

function findMemberOrVariableAt(ast, pos) {
    'use strict';
    return findNodeAt(ast, pos, function (node) {
        return node.type === 'Identifier' && !isDummyIdNode(node) || node.type === 'MemberExpression' && (node.property.start <= pos && pos <= node.property.end ||
        // when prop is ✖
        node.property.end <= pos && pos <= node.property.start);
    });
}

/**
 * Returns context information for completion.
 * @param ast
 * @param pos
 * @return {*}
 */

function findCompletionContext(ast, pos) {
    'use strict';
    // find the node
    var walker = wrapWalker(varWalker, function (node, vb) {
        if (node.start > pos || node.end < pos) {
            return false;
        }
        // at identifier?
        if (node.type === 'Identifier') {
            throw new Found({ type: 'Identifier', node: node, vb: vb });
        }
        // at member expression?
        if (node.type === 'MemberExpression' && (node.property.start <= pos && pos <= node.property.end ||
        // when prop is ✖
        node.property.end <= pos && pos <= node.property.start)) {
            // at usual prop? (after dot)
            if (!node.computed) {
                throw new Found({ type: 'usualProp', node: node, vb: vb });
            }
            // at obj[''] pattern?
            if (node.computed && typeof node.property.value === 'string') {
                throw new Found({ type: 'stringProp', node: node, vb: vb });
            }
        }
        return true;
    }, function (node, vb) {
        // no Identifier or Member Expression was found
        throw new Found({ type: 'Identifier', node: null, vb: vb });
    });

    try {
        walk.recursive(ast, ast['@block'], walker);
    } catch (e) {
        if (e instanceof Found) {
            return e.info;
        } else {
            throw e;
        }
    }
}

/**
 * Find a node at pos.
 * If found, it also returns its varBlock.
 * If not found, return null.
 * @param ast - AST node
 * @param pos - index position
 * @param nodeTest - Check whether the node is what we are looking for
 * @return {*}
 */
function findNodeAt(ast, pos, nodeTest) {
    'use strict';
    // find the node
    var walker = wrapWalker(varWalker, function (node, vb) {
        if (node.start > pos || node.end < pos) {
            return false;
        }
        if (nodeTest(node)) {
            throw new Found({ node: node, vb: vb });
        }
        return true;
    });

    try {
        walk.recursive(ast, ast['@block'], walker);
    } catch (e) {
        if (e instanceof Found) {
            return e.info;
        } else {
            throw e;
        }
    }
    // identifier not found
    return null;
}

/**
 * Find the smallest node that contains the range from start to end.
 * Note that we can find the node at the postNode instead of preNode.
 * @param ast
 * @param start
 * @param end
 * @return {*}
 */

function findSurroundingNode(ast, start, end) {
    'use strict';

    var walker = wrapWalker(varWalker, function (node) {
        return node.start <= start && end <= node.end;
    }, function (node) {
        throw new Found(node);
    });

    try {
        walk.recursive(ast, undefined, walker);
    } catch (e) {
        if (e instanceof Found) {
            return e.info;
        } else {
            throw e;
        }
    }
    // node not found
    return null;
}

/**
 * Makes a recursive visitor.
 * With this, we can use the return value from each node.
 * @param node
 * @param {Status} state
 * @param visitor
 * @return {*}
 */

function recursiveWithReturn(node, state, visitor) {
    function c(node, st, override) {
        return visitor[override || node.type](node, st, c);
    }
    return c(node, state);
}

},{"acorn/dist/walk":17}],13:[function(require,module,exports){
/**
 * @file Implements VarBlock and Scope
 * @author sewon326.kim@samsung.com
 */

'use strict';

exports.__esModule = true;
exports.annotateBlockInfo = annotateBlockInfo;

function _interopRequireWildcard(obj) { if (obj && obj.__esModule) { return obj; } else { var newObj = {}; if (obj != null) { for (var key in obj) { if (Object.prototype.hasOwnProperty.call(obj, key)) newObj[key] = obj[key]; } } newObj['default'] = obj; return newObj; } }

function _classCallCheck(instance, Constructor) { if (!(instance instanceof Constructor)) { throw new TypeError('Cannot call a class as a function'); } }

var _domainsTypes = require('./domains/types');

var types = _interopRequireWildcard(_domainsTypes);

var _utilMyWalker = require('./util/myWalker');

var myWalker = _interopRequireWildcard(_utilMyWalker);

var walk = require('acorn/dist/walk');

var VarBlock = (function () {
    /**
     * Constructs a VarBlock.
     * @param {VarBlock} paren
     * @param originNode
     * @param bType
     * @param {boolean} isStrict
     */

    function VarBlock(paren, originNode, bType, isStrict) {
        _classCallCheck(this, VarBlock);

        this.paren = paren;
        this.originNode = originNode;
        this.blockType = bType;
        this.isStrict = isStrict;

        this.originLabel = originNode['@label'];
        this.paramVarNames = [];
        this.localVarNames = [];

        this.usedVariables = [];
        // this.useArgumentsObject
        this.instances = new Map();
        this.scopeInstances = [];
    }

    /**
     * @static
     */

    /**
     * Checks whether it is a global block.
     * @return {boolean}
     */

    VarBlock.prototype.isGlobal = function isGlobal() {
        return this.blockType === VarBlock.blockTypes.globalBlock;
    };

    /**
     * Checks whether it is an ES5 function block.
     * @return {boolean}
     */

    VarBlock.prototype.isOldFunctionBlock = function isOldFunctionBlock() {
        return this.blockType === VarBlock.blockTypes.oldFunctionBlock;
    };

    /**
     * Checks whether it is a block of an arrow function.
     * @return {boolean}
     */

    VarBlock.prototype.isArrowFunctionBlock = function isArrowFunctionBlock() {
        return this.blockType === VarBlock.blockTypes.arrowFunctionBlock;
    };

    /**
     * Checks whether it is a catch block.
     * @return {boolean}
     */

    VarBlock.prototype.isCatchBlock = function isCatchBlock() {
        return this.blockType === VarBlock.blockTypes.catchBlock;
    };

    /** Checks whether is is a normal code block.
     * @return {boolean}
     */

    VarBlock.prototype.isNormalBlock = function isNormalBlock() {
        return this.blockType === VarBlock.blockTypes.normalBlock;
    };

    /**
     * Checks whether it is a parameter block.
     * @return {boolean}
     */

    VarBlock.prototype.isParameterBlock = function isParameterBlock() {
        return this.blockType === VarBlock.blockTypes.parameterBlock;
    };

    /**
     * Returns the names of local variables.
     * @return {Array.<string>}
     */

    VarBlock.prototype.getLocalVarNames = function getLocalVarNames() {
        return this.localVarNames;
    };

    /**
     * Returns the names of parameters.
     * @return {Array.<string>}
     */

    VarBlock.prototype.getParamVarNames = function getParamVarNames() {
        return this.paramVarNames;
    };

    /**
     * Returns the names of its parameter and local variables.
     * @return {Array.<string>}
     */

    VarBlock.prototype.getVarNames = function getVarNames() {
        return this.getLocalVarNames().concat(this.getParamVarNames());
    };

    /**
     * Checks whether it has a local variable whose name is `varName`.
     * @param {string} varName
     * @return {boolean}
     */

    VarBlock.prototype.hasLocalVar = function hasLocalVar(varName) {
        return this.localVarNames && this.localVarNames.indexOf(varName) > -1;
    };

    /**
     * Checks whether it has a parameter varialbe whose name is `varName`.
     * @param {string} varName
     * @return {boolean}
     */

    VarBlock.prototype.hasParamVar = function hasParamVar(varName) {
        return this.paramVarNames.indexOf(varName) > -1;
    };

    /**
     * Checks whether the block has variable named as `varName`.
     * @param {string} varName
     * @return {boolean}
     */

    VarBlock.prototype.hasVar = function hasVar(varName) {
        return this.hasParamVar(varName) || this.hasLocalVar(varName);
    };

    /**
     * Add a declared variable to the block.
     * It returns null if it does not add the variable.
     * @param {string} varName
     * @param dType - declaration type
     * @return {VarBlock|null}
     */

    VarBlock.prototype.addDeclaredLocalVar = function addDeclaredLocalVar(varName, dType) {
        var currBlock = this;
        switch (dType) {
            case VarBlock.declarationTypes.varDeclaration:
                // Go up until function or global
                while (!currBlock.isOldFunctionBlock() && !currBlock.isArrowFunctionBlock() && !currBlock.isParameterBlock() // to add 'arguments'
                 && !currBlock.isGlobal()) {
                    currBlock = currBlock.paren;
                }
                break;
            case VarBlock.declarationTypes.functionDeclaration:
                // Go up until function or global
                // or catch block having varName as its parameter
                while (currBlock.isNormalBlock() && !(currBlock.isCatchBlock() && currBlock.hasParamVar(varName))) {
                    currBlock = currBlock.paren;
                }
                break;
            case VarBlock.declarationTypes.letDeclaration:
            case VarBlock.declarationTypes.constDeclaration:
                break;
            case VarBlock.declarationTypes.implicitGlobalDeclaration:
                // not global or strict => do not add the variable
                if (!this.isGlobal() || this.isStrict) {
                    return null;
                }
                break;
        }

        // if already added, do not add
        if (!currBlock.hasVar(varName)) {
            currBlock.localVarNames.push(varName);
        }
        // returns the block object that contains the variable
        return currBlock;
    };

    /**
     * Adds a parameter variable.
     * @param {string} varName
     */

    VarBlock.prototype.addParamVar = function addParamVar(varName) {
        this.paramVarNames.push(varName);
    };

    /**
     * Returns the VarBlock that contains `varName`.
     * It can recursively look into `paren` VarBlocks.
     * @param varName
     * @return {VarBlock}
     */

    VarBlock.prototype.findVarInChain = function findVarInChain(varName) {
        var currBlock = this;
        while (currBlock && !currBlock.hasVar(varName)) {
            if (currBlock.isGlobal() && !currBlock.isStrict) {
                break;
            }
            currBlock = currBlock.paren;
        }
        // if not found
        // 1) global 'use strict' => returns null
        // 2) otherwise => returns the global
        return currBlock;
    };

    /**
     * Get all the variable names in the chain of VarBlock.
     * @return {Array.<string>}
     */

    VarBlock.prototype.getVarNamesInChain = function getVarNamesInChain() {
        var currBlock = this;
        var varNames = [];
        while (currBlock) {
            currBlock.getVarNames().forEach(function (name) {
                if (varNames.indexOf(name) === -1) {
                    varNames.push(name);
                }
            });
            currBlock = currBlock.paren;
        }
        return varNames;
    };

    /**
     * Add `varName` as one of the used variables.
     * @param {string} varName
     */

    VarBlock.prototype.addUsedVar = function addUsedVar(varName) {
        if (this.usedVariables.indexOf(varName) === -1) {
            this.usedVariables.push(varName);
        }
    };

    /**
     * Returns the used variables.
     * @return {Array.<string>}
     */

    VarBlock.prototype.getUsedVarNames = function getUsedVarNames() {
        return this.usedVariables;
    };

    /**
     * Checks whether `varName` is used.
     * @param varName
     * @return {boolean}
     */

    VarBlock.prototype.isUsedVar = function isUsedVar(varName) {
        return this.usedVariables.indexOf(varName) > -1;
    };

    /**
     * Returns a mapping from variable names to their AVals.
     * @param {CallSiteContext} delta
     * @return {Map.<string, AVal>}
     */

    VarBlock.prototype.getInstance = function getInstance(delta) {
        if (this.instances.has(delta)) {
            return this.instances.get(delta);
        }
        // construct VarMap
        var varMap = new Map();
        var varNames = this.getParamVarNames().concat(this.getLocalVarNames());

        for (var i = 0; i < varNames.length; i++) {
            varMap.set(varNames[i], new types.AVal());
        }
        // remember the instance
        this.instances.set(delta, varMap);
        return varMap;
    };

    /**
     * Returns an array of AVals for parameters
     * @param delta
     * @returns {Array.<AVal>}
     */

    VarBlock.prototype.getParamAVals = function getParamAVals(delta) {
        var instance = this.getInstance(delta);
        var params = [];
        this.getParamVarNames().forEach(function (name) {
            params.push(instance.get(name));
        });
        return params;
    };

    /**
     * Returns an AVal for `arguments`.
     * @param delta
     * @returns {AVal}
     */

    VarBlock.prototype.getArgumentsAVal = function getArgumentsAVal(delta) {
        if (!this.useArgumentsObject) {
            throw new Error('Not for this VarBlock');
        }
        return this.getInstance(delta).get('arguments');
    };

    /**
     * Get a Scope instance
     * @param paren
     * @param delta
     * @returns {*}
     */

    VarBlock.prototype.getScopeInstance = function getScopeInstance(paren, delta) {
        var varMap = this.getInstance(delta);
        var found = null;

        this.scopeInstances.forEach(function (sc) {
            if (sc.paren === paren && sc.varMap === varMap) found = sc;
        });

        if (found) {
            return found;
        } else {
            var newScopeInstance = new Scope(paren, varMap, this);
            this.scopeInstances.push(newScopeInstance);
            return newScopeInstance;
        }
    };

    /**
     * Get function's scope instances whose paren is `pScope`.
     * @param pScope
     * @returns {Set.<Scope>}
     */

    VarBlock.prototype.getScopesWithParent = function getScopesWithParent(pScope) {
        var instances = new Set();
        this.scopeInstances.forEach(function (sc) {
            if (sc.paren === pScope) instances.add(sc);
        });
        return instances;
    };

    return VarBlock;
})();

exports.VarBlock = VarBlock;
VarBlock.blockTypes = {
    globalBlock: Symbol('global'),
    oldFunctionBlock: Symbol('oldFunction'),
    arrowFunctionBlock: Symbol('arrowFunction'),
    parameterBlock: Symbol('parameter'), // though not really in braces
    catchBlock: Symbol('catch'),
    normalBlock: Symbol('normal')
};

/**
 * @static
 */
VarBlock.declarationTypes = {
    letDeclaration: Symbol('let'),
    constDeclaration: Symbol('const'),
    varDeclaration: Symbol('var'),
    functionDeclaration: Symbol('function'),
    parameterDeclaration: Symbol('parameter'),
    implicitGlobalDeclaration: Symbol('implicit global')
};

/**
 * Check whether the stmt is the directive for strictness.
 * Taken from acorn
 * @param stmt - the first statement of a body
 * @return {boolean}
 */
function _isUseStrict(stmt) {
    return stmt.type === 'ExpressionStatement' && stmt.expression.type === 'Literal' && stmt.expression.raw.slice(1, -1) === 'use strict';
}

var _declaredVariableFinder = walk.make({
    VariablePattern: function VariablePattern(node, _ref, c) {
        var dType = _ref[0];
        var currBlock = _ref[1];

        if (dType === VarBlock.declarationTypes.parameterDeclaration) {
            currBlock.addParamVar(node.name);
        } else if (dType) {
            currBlock.addDeclaredLocalVar(node.name, dType);
        }
    },
    Function: function Function(node, _ref2, c) {
        var dType = _ref2[0];
        var currBlock = _ref2[1];

        var parenBlock = currBlock,
            paramBlock = undefined;
        if (node.id) {
            var funcName = node.id.name;
            parenBlock = currBlock.addDeclaredLocalVar(funcName, VarBlock.declarationTypes.functionDeclaration);
        }
        var hasParamScope = node.params.some(function (ptn) {
            return myWalker.patternHasDefaults(ptn);
        });
        if (hasParamScope) {
            paramBlock = parenBlock = new VarBlock(parenBlock, node, VarBlock.blockTypes.parameterBlock, currBlock.isStrict);
            node['@block'] = paramBlock;
        }
        var strictInner = currBlock.isStrict || node.body.body && node.body.body[0] && _isUseStrict(node.body.body[0]);
        var funcBlock = new VarBlock(parenBlock, node, // same originNode with paramBlock, intended.
        node.type === 'ArrowFunctionExpression' ? VarBlock.blockTypes.arrowFunctionBlock : VarBlock.blockTypes.oldFunctionBlock, strictInner);
        funcBlock.hasParamScope = hasParamScope;
        node.body['@block'] = funcBlock;

        // add function parameters to corresponding scope
        var paramTargetBlock = paramBlock || funcBlock;
        for (var i = 0; i < node.params.length; i++) {
            c(node.params[i], [VarBlock.declarationTypes.parameterDeclaration, paramTargetBlock], 'Pattern');
        }

        if (node.expression) {
            c(node.body, [, funcBlock], 'Expression');
        } else {
            walk.base.BlockStatement(node.body, [, funcBlock], c);
        }
    },

    ForStatement: function ForStatement(node, _ref3, c) {
        var currBlock = _ref3[1];

        var forBlock = undefined;
        if (currBlock.isStrict) {
            forBlock = new VarBlock(currBlock, node, VarBlock.blockTypes.normalBlock, currBlock.isStrict);
            node['@block'] = forBlock;
        } else {
            forBlock = currBlock;
        }
        if (node.init) c(node.init, [, forBlock], 'ForInit');
        if (node.test) c(node.test, [, forBlock], 'Expression');
        if (node.update) c(node.update, [, forBlock], 'Expression');
        // its body can have a separate block.
        c(node.body, [, forBlock], undefined);
    },

    VariableDeclaration: function VariableDeclaration(node, _ref4, c) {
        var currBlock = _ref4[1];

        var dType = undefined;
        switch (node.kind) {
            case 'var':
                dType = VarBlock.declarationTypes.varDeclaration;
                break;
            case 'let':
                dType = VarBlock.declarationTypes.letDeclaration;
                break;
            case 'const':
                dType = VarBlock.declarationTypes.constDeclaration;
                break;
        }

        for (var i = 0; i < node.declarations.length; i++) {
            c(node.declarations[i], [dType, currBlock], undefined);
        }
    },

    TryStatement: function TryStatement(node, _ref5, c) {
        var currScope = _ref5[1];

        c(node.block, [, currScope], undefined);
        if (node.handler) {
            c(node.handler, [, currScope], undefined);
        }
        if (node.finalizer) {
            c(node.finalizer, [, currScope], undefined);
        }
    },

    CatchClause: function CatchClause(node, _ref6, c) {
        var currBlock = _ref6[1];

        var catchBlock = new VarBlock(currBlock, node, VarBlock.blockTypes.catchBlock, currBlock.isStrict);
        c(node.param, [VarBlock.declarationTypes.parameterDeclaration, catchBlock], 'Pattern');
        node.body['@block'] = catchBlock;
        walk.base.BlockStatement(node.body, [, catchBlock], c);
    },

    // Create VarBlock of type normalBlock
    BlockStatement: function BlockStatement(node, _ref7, c) {
        var currBlock = _ref7[1];

        var inBlock = undefined;
        if (currBlock.isStrict) {
            inBlock = new VarBlock(currBlock, node, VarBlock.blockTypes.normalBlock, currBlock.isStrict);
            node['@block'] = inBlock;
        } else {
            inBlock = currBlock;
        }
        walk.base.BlockStatement(node, [, inBlock], c);
    }
});

// For variables in global and arguments in functions
var _variableUsageCollector = walk.make({
    VariablePattern: function VariablePattern(node, currBlock, c) {
        c(node, currBlock, 'Identifier');
    },

    Identifier: function Identifier(node, currBlock, c) {
        if (myWalker.isDummyIdNode(node)) {
            // Skip dummy Id node
            return;
        }
        var block = currBlock;
        var varName = node.name;

        while (block && !block.hasVar(varName)) {
            if (varName === 'arguments' && (block.isOldFunctionBlock() || block.isParameterBlock())) {
                if (block.hasParamScope) {
                    block = block.paren;
                    if (block.hasVar(varName)) break;
                }
                block.useArgumentsObject = true;
                // consider 'var' is used for declaration of 'arguments.'
                block.addDeclaredLocalVar(varName, VarBlock.declarationTypes.varDeclaration);
                break;
            }
            if (block.isGlobal()) {
                block.addDeclaredLocalVar(varName, VarBlock.declarationTypes.implicitGlobalDeclaration);
                break;
            }
            block = block.paren;
        }
        if (block.hasVar(varName)) {
            block.addUsedVar(varName);
        }
    },

    ReturnStatement: function ReturnStatement(node, currBlock, c) {
        var block = currBlock;
        while (block.isCatchBlock() || block.isNormalBlock()) {
            block = block.paren;
        }
        if (!block.isGlobal() && node.argument !== null) {
            block.useReturnWithArgument = true;
        }
        if (node.argument) {
            c(node.argument, currBlock, undefined);
        }
    },

    Function: function Function(node, currBlock, c) {
        if (node.id) c(node.id, currBlock, 'Pattern');
        if (node['@block']) {
            var paramBlock = node['@block'];
            for (var i = 0; i < node.params.length; i++) {
                c(node.params[i], paramBlock, 'Pattern');
            }
        }
        c(node.body, currBlock);
    },

    ScopeBody: function ScopeBody(node, currBlock, c) {
        c(node, node['@block'] || currBlock);
    },

    BlockStatement: function BlockStatement(node, currBlock, c) {
        // Process BlockStatement with changed VarBlock
        walk.base.BlockStatement(node, node['@block'] || currBlock, c);
    }
});

/**
 * Analyzes `ast` and annotates it with VarBlocks.
 * @param ast
 * @param gVarBlock
 * @return {*}
 */

function annotateBlockInfo(ast, gVarBlock) {
    ast['@block'] = gVarBlock;

    gVarBlock.isStrict = gVarBlock.isStrict || ast.body[0] && _isUseStrict(ast.body[0]);

    walk.recursive(ast, [, gVarBlock], _declaredVariableFinder);
    walk.recursive(ast, gVarBlock, _variableUsageCollector);
    return ast;
}

var Scope = (function () {
    /**
     * Construct Scope instance.
     * @param {Scope} paren
     * @param {Map.<string, AVal>} varMap
     * @param {VarBlock} vb
     */

    function Scope(paren, varMap, vb) {
        _classCallCheck(this, Scope);

        this.paren = paren;
        this.varMap = varMap;
        this.vb = vb;
        if (vb.blockType === VarBlock.blockTypes.catchBlock) {
            // Collect thrown into .caughtAVal, and connect to parameter pattern
            this.caughtAVal = new types.AVal();
        }
    }

    /**
     * Find AVal of `varName` in the chain
     * @param {string} varName
     * @return {AVal}
     */

    Scope.prototype.getAValOf = function getAValOf(varName) {
        var curr = this;
        while (curr != null) {
            if (curr.varMap.has(varName)) {
                return curr.varMap.get(varName);
            }
            curr = curr.paren;
        }
        // returns dummy AVal for not found variables
        return types.AValNull;
    };

    /**
     * Finds the first scope that is not for catch or normal block.
     * @return {Scope}
     */

    Scope.prototype.removeInitialCatchOrNormalBlocks = function removeInitialCatchOrNormalBlocks() {
        var curr = this;
        while (curr.vb.isCatchBlock() || curr.vb.isNormalBlock()) {
            curr = curr.paren;
        }
        return curr;
    };

    return Scope;
})();

},{"./domains/types":6,"./util/myWalker":12,"acorn/dist/walk":17}],14:[function(require,module,exports){
/**
 * @file Implements variable occurrence finder.
 * @author sewon326.kim@samsung.com
 */

'use strict';

exports.__esModule = true;
exports.findVarRefsAt = findVarRefsAt;

function _interopRequireWildcard(obj) { if (obj && obj.__esModule) { return obj; } else { var newObj = {}; if (obj != null) { for (var key in obj) { if (Object.prototype.hasOwnProperty.call(obj, key)) newObj[key] = obj[key]; } } newObj['default'] = obj; return newObj; } }

var _utilMyWalker = require('./util/myWalker');

var myWalker = _interopRequireWildcard(_utilMyWalker);

/**
 * Finds occurrences of the variable at `pos`.
 * @param ast - scope annotated AST
 * @param {number} pos - character position
 * @return {*} - array of AST nodes
 */
var walk = require('acorn/dist/walk');

function findVarRefsAt(ast, pos) {
    'use strict';
    var found = myWalker.findIdentifierAt(ast, pos);
    if (!found) {
        // pos is not at a variable
        return null;
    }
    // find refs for the id node
    var refs = _findRefsToVariable(found).map(function (node) {
        return { start: node.start, end: node.end };
    });
    refs.varName = found.node.name;

    return refs;
}

/**
 * @param found - node and varBlock of the variable
 * @return {Array} - array of AST nodes
 */
function _findRefsToVariable(found) {
    'use strict';
    var varName = found.node.name;
    var vb1 = found.vb.findVarInChain(varName);
    if (!vb1) return [];

    var refs = [];

    var walker = walk.make({
        Identifier: function Identifier(node, vb) {
            if (node.name !== varName) return;
            if (vb1 === vb.findVarInChain(varName)) {
                refs.push(node);
            }
        }
    }, myWalker.varWalker);

    walk.recursive(vb1.originNode, vb1.originNode['@block'], walker);
    return refs;
}

},{"./util/myWalker":12,"acorn/dist/walk":17}],15:[function(require,module,exports){
(function (global){
(function(f){if(typeof exports==="object"&&typeof module!=="undefined"){module.exports=f()}else if(typeof define==="function"&&define.amd){define([],f)}else{var g;if(typeof window!=="undefined"){g=window}else if(typeof global!=="undefined"){g=global}else if(typeof self!=="undefined"){g=self}else{g=this}g.acorn = f()}})(function(){var define,module,exports;return (function e(t,n,r){function s(o,u){if(!n[o]){if(!t[o]){var a=typeof require=="function"&&require;if(!u&&a)return a(o,!0);if(i)return i(o,!0);var f=new Error("Cannot find module '"+o+"'");throw f.code="MODULE_NOT_FOUND",f}var l=n[o]={exports:{}};t[o][0].call(l.exports,function(e){var n=t[o][1][e];return s(n?n:e)},l,l.exports,e,t,n,r)}return n[o].exports}var i=typeof require=="function"&&require;for(var o=0;o<r.length;o++)s(r[o]);return s})({1:[function(_dereq_,module,exports){
// A recursive descent parser operates by defining functions for all
// syntactic elements, and recursively calling those, each function
// advancing the input stream and returning an AST node. Precedence
// of constructs (for example, the fact that `!x[1]` means `!(x[1])`
// instead of `(!x)[1]` is handled by the fact that the parser
// function that parses unary prefix operators is called first, and
// in turn calls the function that parses `[]` subscripts — that
// way, it'll receive the node for `x[1]` already parsed, and wraps
// *that* in the unary operator node.
//
// Acorn uses an [operator precedence parser][opp] to handle binary
// operator precedence, because it is much more compact than using
// the technique outlined above, which uses different, nesting
// functions to specify precedence, for all of the ten binary
// precedence levels that JavaScript defines.
//
// [opp]: http://en.wikipedia.org/wiki/Operator-precedence_parser

"use strict";

var _tokentype = _dereq_("./tokentype");

var _state = _dereq_("./state");

var _identifier = _dereq_("./identifier");

var _util = _dereq_("./util");

var pp = _state.Parser.prototype;

// Check if property name clashes with already added.
// Object/class getters and setters are not allowed to clash —
// either with each other or with an init property — and in
// strict mode, init properties are also not allowed to be repeated.

pp.checkPropClash = function (prop, propHash) {
  if (this.options.ecmaVersion >= 6 && (prop.computed || prop.method || prop.shorthand)) return;
  var key = prop.key,
      name = undefined;
  switch (key.type) {
    case "Identifier":
      name = key.name;break;
    case "Literal":
      name = String(key.value);break;
    default:
      return;
  }
  var kind = prop.kind;
  if (this.options.ecmaVersion >= 6) {
    if (name === "__proto__" && kind === "init") {
      if (propHash.proto) this.raise(key.start, "Redefinition of __proto__ property");
      propHash.proto = true;
    }
    return;
  }
  var other = undefined;
  if (_util.has(propHash, name)) {
    other = propHash[name];
    var isGetSet = kind !== "init";
    if ((this.strict || isGetSet) && other[kind] || !(isGetSet ^ other.init)) this.raise(key.start, "Redefinition of property");
  } else {
    other = propHash[name] = {
      init: false,
      get: false,
      set: false
    };
  }
  other[kind] = true;
};

// ### Expression parsing

// These nest, from the most general expression type at the top to
// 'atomic', nondivisible expression types at the bottom. Most of
// the functions will simply let the function(s) below them parse,
// and, *if* the syntactic construct they handle is present, wrap
// the AST node that the inner parser gave them in another node.

// Parse a full expression. The optional arguments are used to
// forbid the `in` operator (in for loops initalization expressions)
// and provide reference for storing '=' operator inside shorthand
// property assignment in contexts where both object expression
// and object pattern might appear (so it's possible to raise
// delayed syntax error at correct position).

pp.parseExpression = function (noIn, refShorthandDefaultPos) {
  var startPos = this.start,
      startLoc = this.startLoc;
  var expr = this.parseMaybeAssign(noIn, refShorthandDefaultPos);
  if (this.type === _tokentype.types.comma) {
    var node = this.startNodeAt(startPos, startLoc);
    node.expressions = [expr];
    while (this.eat(_tokentype.types.comma)) node.expressions.push(this.parseMaybeAssign(noIn, refShorthandDefaultPos));
    return this.finishNode(node, "SequenceExpression");
  }
  return expr;
};

// Parse an assignment expression. This includes applications of
// operators like `+=`.

pp.parseMaybeAssign = function (noIn, refShorthandDefaultPos, afterLeftParse) {
  if (this.type == _tokentype.types._yield && this.inGenerator) return this.parseYield();

  var failOnShorthandAssign = undefined;
  if (!refShorthandDefaultPos) {
    refShorthandDefaultPos = { start: 0 };
    failOnShorthandAssign = true;
  } else {
    failOnShorthandAssign = false;
  }
  var startPos = this.start,
      startLoc = this.startLoc;
  if (this.type == _tokentype.types.parenL || this.type == _tokentype.types.name) this.potentialArrowAt = this.start;
  var left = this.parseMaybeConditional(noIn, refShorthandDefaultPos);
  if (afterLeftParse) left = afterLeftParse.call(this, left, startPos, startLoc);
  if (this.type.isAssign) {
    var node = this.startNodeAt(startPos, startLoc);
    node.operator = this.value;
    node.left = this.type === _tokentype.types.eq ? this.toAssignable(left) : left;
    refShorthandDefaultPos.start = 0; // reset because shorthand default was used correctly
    this.checkLVal(left);
    this.next();
    node.right = this.parseMaybeAssign(noIn);
    return this.finishNode(node, "AssignmentExpression");
  } else if (failOnShorthandAssign && refShorthandDefaultPos.start) {
    this.unexpected(refShorthandDefaultPos.start);
  }
  return left;
};

// Parse a ternary conditional (`?:`) operator.

pp.parseMaybeConditional = function (noIn, refShorthandDefaultPos) {
  var startPos = this.start,
      startLoc = this.startLoc;
  var expr = this.parseExprOps(noIn, refShorthandDefaultPos);
  if (refShorthandDefaultPos && refShorthandDefaultPos.start) return expr;
  if (this.eat(_tokentype.types.question)) {
    var node = this.startNodeAt(startPos, startLoc);
    node.test = expr;
    node.consequent = this.parseMaybeAssign();
    this.expect(_tokentype.types.colon);
    node.alternate = this.parseMaybeAssign(noIn);
    return this.finishNode(node, "ConditionalExpression");
  }
  return expr;
};

// Start the precedence parser.

pp.parseExprOps = function (noIn, refShorthandDefaultPos) {
  var startPos = this.start,
      startLoc = this.startLoc;
  var expr = this.parseMaybeUnary(refShorthandDefaultPos);
  if (refShorthandDefaultPos && refShorthandDefaultPos.start) return expr;
  return this.parseExprOp(expr, startPos, startLoc, -1, noIn);
};

// Parse binary operators with the operator precedence parsing
// algorithm. `left` is the left-hand side of the operator.
// `minPrec` provides context that allows the function to stop and
// defer further parser to one of its callers when it encounters an
// operator that has a lower precedence than the set it is parsing.

pp.parseExprOp = function (left, leftStartPos, leftStartLoc, minPrec, noIn) {
  var prec = this.type.binop;
  if (prec != null && (!noIn || this.type !== _tokentype.types._in)) {
    if (prec > minPrec) {
      var node = this.startNodeAt(leftStartPos, leftStartLoc);
      node.left = left;
      node.operator = this.value;
      var op = this.type;
      this.next();
      var startPos = this.start,
          startLoc = this.startLoc;
      node.right = this.parseExprOp(this.parseMaybeUnary(), startPos, startLoc, prec, noIn);
      this.finishNode(node, op === _tokentype.types.logicalOR || op === _tokentype.types.logicalAND ? "LogicalExpression" : "BinaryExpression");
      return this.parseExprOp(node, leftStartPos, leftStartLoc, minPrec, noIn);
    }
  }
  return left;
};

// Parse unary operators, both prefix and postfix.

pp.parseMaybeUnary = function (refShorthandDefaultPos) {
  if (this.type.prefix) {
    var node = this.startNode(),
        update = this.type === _tokentype.types.incDec;
    node.operator = this.value;
    node.prefix = true;
    this.next();
    node.argument = this.parseMaybeUnary();
    if (refShorthandDefaultPos && refShorthandDefaultPos.start) this.unexpected(refShorthandDefaultPos.start);
    if (update) this.checkLVal(node.argument);else if (this.strict && node.operator === "delete" && node.argument.type === "Identifier") this.raise(node.start, "Deleting local variable in strict mode");
    return this.finishNode(node, update ? "UpdateExpression" : "UnaryExpression");
  }
  var startPos = this.start,
      startLoc = this.startLoc;
  var expr = this.parseExprSubscripts(refShorthandDefaultPos);
  if (refShorthandDefaultPos && refShorthandDefaultPos.start) return expr;
  while (this.type.postfix && !this.canInsertSemicolon()) {
    var node = this.startNodeAt(startPos, startLoc);
    node.operator = this.value;
    node.prefix = false;
    node.argument = expr;
    this.checkLVal(expr);
    this.next();
    expr = this.finishNode(node, "UpdateExpression");
  }
  return expr;
};

// Parse call, dot, and `[]`-subscript expressions.

pp.parseExprSubscripts = function (refShorthandDefaultPos) {
  var startPos = this.start,
      startLoc = this.startLoc;
  var expr = this.parseExprAtom(refShorthandDefaultPos);
  if (refShorthandDefaultPos && refShorthandDefaultPos.start) return expr;
  return this.parseSubscripts(expr, startPos, startLoc);
};

pp.parseSubscripts = function (base, startPos, startLoc, noCalls) {
  for (;;) {
    if (this.eat(_tokentype.types.dot)) {
      var node = this.startNodeAt(startPos, startLoc);
      node.object = base;
      node.property = this.parseIdent(true);
      node.computed = false;
      base = this.finishNode(node, "MemberExpression");
    } else if (this.eat(_tokentype.types.bracketL)) {
      var node = this.startNodeAt(startPos, startLoc);
      node.object = base;
      node.property = this.parseExpression();
      node.computed = true;
      this.expect(_tokentype.types.bracketR);
      base = this.finishNode(node, "MemberExpression");
    } else if (!noCalls && this.eat(_tokentype.types.parenL)) {
      var node = this.startNodeAt(startPos, startLoc);
      node.callee = base;
      node.arguments = this.parseExprList(_tokentype.types.parenR, false);
      base = this.finishNode(node, "CallExpression");
    } else if (this.type === _tokentype.types.backQuote) {
      var node = this.startNodeAt(startPos, startLoc);
      node.tag = base;
      node.quasi = this.parseTemplate();
      base = this.finishNode(node, "TaggedTemplateExpression");
    } else {
      return base;
    }
  }
};

// Parse an atomic expression — either a single token that is an
// expression, an expression started by a keyword like `function` or
// `new`, or an expression wrapped in punctuation like `()`, `[]`,
// or `{}`.

pp.parseExprAtom = function (refShorthandDefaultPos) {
  var node = undefined,
      canBeArrow = this.potentialArrowAt == this.start;
  switch (this.type) {
    case _tokentype.types._super:
      if (!this.inFunction) this.raise(this.start, "'super' outside of function or class");
    case _tokentype.types._this:
      var type = this.type === _tokentype.types._this ? "ThisExpression" : "Super";
      node = this.startNode();
      this.next();
      return this.finishNode(node, type);

    case _tokentype.types._yield:
      if (this.inGenerator) this.unexpected();

    case _tokentype.types.name:
      var startPos = this.start,
          startLoc = this.startLoc;
      var id = this.parseIdent(this.type !== _tokentype.types.name);
      if (canBeArrow && !this.canInsertSemicolon() && this.eat(_tokentype.types.arrow)) return this.parseArrowExpression(this.startNodeAt(startPos, startLoc), [id]);
      return id;

    case _tokentype.types.regexp:
      var value = this.value;
      node = this.parseLiteral(value.value);
      node.regex = { pattern: value.pattern, flags: value.flags };
      return node;

    case _tokentype.types.num:case _tokentype.types.string:
      return this.parseLiteral(this.value);

    case _tokentype.types._null:case _tokentype.types._true:case _tokentype.types._false:
      node = this.startNode();
      node.value = this.type === _tokentype.types._null ? null : this.type === _tokentype.types._true;
      node.raw = this.type.keyword;
      this.next();
      return this.finishNode(node, "Literal");

    case _tokentype.types.parenL:
      return this.parseParenAndDistinguishExpression(canBeArrow);

    case _tokentype.types.bracketL:
      node = this.startNode();
      this.next();
      // check whether this is array comprehension or regular array
      if (this.options.ecmaVersion >= 7 && this.type === _tokentype.types._for) {
        return this.parseComprehension(node, false);
      }
      node.elements = this.parseExprList(_tokentype.types.bracketR, true, true, refShorthandDefaultPos);
      return this.finishNode(node, "ArrayExpression");

    case _tokentype.types.braceL:
      return this.parseObj(false, refShorthandDefaultPos);

    case _tokentype.types._function:
      node = this.startNode();
      this.next();
      return this.parseFunction(node, false);

    case _tokentype.types._class:
      return this.parseClass(this.startNode(), false);

    case _tokentype.types._new:
      return this.parseNew();

    case _tokentype.types.backQuote:
      return this.parseTemplate();

    default:
      this.unexpected();
  }
};

pp.parseLiteral = function (value) {
  var node = this.startNode();
  node.value = value;
  node.raw = this.input.slice(this.start, this.end);
  this.next();
  return this.finishNode(node, "Literal");
};

pp.parseParenExpression = function () {
  this.expect(_tokentype.types.parenL);
  var val = this.parseExpression();
  this.expect(_tokentype.types.parenR);
  return val;
};

pp.parseParenAndDistinguishExpression = function (canBeArrow) {
  var startPos = this.start,
      startLoc = this.startLoc,
      val = undefined;
  if (this.options.ecmaVersion >= 6) {
    this.next();

    if (this.options.ecmaVersion >= 7 && this.type === _tokentype.types._for) {
      return this.parseComprehension(this.startNodeAt(startPos, startLoc), true);
    }

    var innerStartPos = this.start,
        innerStartLoc = this.startLoc;
    var exprList = [],
        first = true;
    var refShorthandDefaultPos = { start: 0 },
        spreadStart = undefined,
        innerParenStart = undefined;
    while (this.type !== _tokentype.types.parenR) {
      first ? first = false : this.expect(_tokentype.types.comma);
      if (this.type === _tokentype.types.ellipsis) {
        spreadStart = this.start;
        exprList.push(this.parseParenItem(this.parseRest()));
        break;
      } else {
        if (this.type === _tokentype.types.parenL && !innerParenStart) {
          innerParenStart = this.start;
        }
        exprList.push(this.parseMaybeAssign(false, refShorthandDefaultPos, this.parseParenItem));
      }
    }
    var innerEndPos = this.start,
        innerEndLoc = this.startLoc;
    this.expect(_tokentype.types.parenR);

    if (canBeArrow && !this.canInsertSemicolon() && this.eat(_tokentype.types.arrow)) {
      if (innerParenStart) this.unexpected(innerParenStart);
      return this.parseParenArrowList(startPos, startLoc, exprList);
    }

    if (!exprList.length) this.unexpected(this.lastTokStart);
    if (spreadStart) this.unexpected(spreadStart);
    if (refShorthandDefaultPos.start) this.unexpected(refShorthandDefaultPos.start);

    if (exprList.length > 1) {
      val = this.startNodeAt(innerStartPos, innerStartLoc);
      val.expressions = exprList;
      this.finishNodeAt(val, "SequenceExpression", innerEndPos, innerEndLoc);
    } else {
      val = exprList[0];
    }
  } else {
    val = this.parseParenExpression();
  }

  if (this.options.preserveParens) {
    var par = this.startNodeAt(startPos, startLoc);
    par.expression = val;
    return this.finishNode(par, "ParenthesizedExpression");
  } else {
    return val;
  }
};

pp.parseParenItem = function (item) {
  return item;
};

pp.parseParenArrowList = function (startPos, startLoc, exprList) {
  return this.parseArrowExpression(this.startNodeAt(startPos, startLoc), exprList);
};

// New's precedence is slightly tricky. It must allow its argument
// to be a `[]` or dot subscript expression, but not a call — at
// least, not without wrapping it in parentheses. Thus, it uses the

var empty = [];

pp.parseNew = function () {
  var node = this.startNode();
  var meta = this.parseIdent(true);
  if (this.options.ecmaVersion >= 6 && this.eat(_tokentype.types.dot)) {
    node.meta = meta;
    node.property = this.parseIdent(true);
    if (node.property.name !== "target") this.raise(node.property.start, "The only valid meta property for new is new.target");
    return this.finishNode(node, "MetaProperty");
  }
  var startPos = this.start,
      startLoc = this.startLoc;
  node.callee = this.parseSubscripts(this.parseExprAtom(), startPos, startLoc, true);
  if (this.eat(_tokentype.types.parenL)) node.arguments = this.parseExprList(_tokentype.types.parenR, false);else node.arguments = empty;
  return this.finishNode(node, "NewExpression");
};

// Parse template expression.

pp.parseTemplateElement = function () {
  var elem = this.startNode();
  elem.value = {
    raw: this.input.slice(this.start, this.end).replace(/\r\n?/g, "\n"),
    cooked: this.value
  };
  this.next();
  elem.tail = this.type === _tokentype.types.backQuote;
  return this.finishNode(elem, "TemplateElement");
};

pp.parseTemplate = function () {
  var node = this.startNode();
  this.next();
  node.expressions = [];
  var curElt = this.parseTemplateElement();
  node.quasis = [curElt];
  while (!curElt.tail) {
    this.expect(_tokentype.types.dollarBraceL);
    node.expressions.push(this.parseExpression());
    this.expect(_tokentype.types.braceR);
    node.quasis.push(curElt = this.parseTemplateElement());
  }
  this.next();
  return this.finishNode(node, "TemplateLiteral");
};

// Parse an object literal or binding pattern.

pp.parseObj = function (isPattern, refShorthandDefaultPos) {
  var node = this.startNode(),
      first = true,
      propHash = {};
  node.properties = [];
  this.next();
  while (!this.eat(_tokentype.types.braceR)) {
    if (!first) {
      this.expect(_tokentype.types.comma);
      if (this.afterTrailingComma(_tokentype.types.braceR)) break;
    } else first = false;

    var prop = this.startNode(),
        isGenerator = undefined,
        startPos = undefined,
        startLoc = undefined;
    if (this.options.ecmaVersion >= 6) {
      prop.method = false;
      prop.shorthand = false;
      if (isPattern || refShorthandDefaultPos) {
        startPos = this.start;
        startLoc = this.startLoc;
      }
      if (!isPattern) isGenerator = this.eat(_tokentype.types.star);
    }
    this.parsePropertyName(prop);
    this.parsePropertyValue(prop, isPattern, isGenerator, startPos, startLoc, refShorthandDefaultPos);
    this.checkPropClash(prop, propHash);
    node.properties.push(this.finishNode(prop, "Property"));
  }
  return this.finishNode(node, isPattern ? "ObjectPattern" : "ObjectExpression");
};

pp.parsePropertyValue = function (prop, isPattern, isGenerator, startPos, startLoc, refShorthandDefaultPos) {
  if (this.eat(_tokentype.types.colon)) {
    prop.value = isPattern ? this.parseMaybeDefault(this.start, this.startLoc) : this.parseMaybeAssign(false, refShorthandDefaultPos);
    prop.kind = "init";
  } else if (this.options.ecmaVersion >= 6 && this.type === _tokentype.types.parenL) {
    if (isPattern) this.unexpected();
    prop.kind = "init";
    prop.method = true;
    prop.value = this.parseMethod(isGenerator);
  } else if (this.options.ecmaVersion >= 5 && !prop.computed && prop.key.type === "Identifier" && (prop.key.name === "get" || prop.key.name === "set") && (this.type != _tokentype.types.comma && this.type != _tokentype.types.braceR)) {
    if (isGenerator || isPattern) this.unexpected();
    prop.kind = prop.key.name;
    this.parsePropertyName(prop);
    prop.value = this.parseMethod(false);
    var paramCount = prop.kind === "get" ? 0 : 1;
    if (prop.value.params.length !== paramCount) {
      var start = prop.value.start;
      if (prop.kind === "get") this.raise(start, "getter should have no params");else this.raise(start, "setter should have exactly one param");
    }
  } else if (this.options.ecmaVersion >= 6 && !prop.computed && prop.key.type === "Identifier") {
    prop.kind = "init";
    if (isPattern) {
      if (this.isKeyword(prop.key.name) || this.strict && (_identifier.reservedWords.strictBind(prop.key.name) || _identifier.reservedWords.strict(prop.key.name)) || !this.options.allowReserved && this.isReservedWord(prop.key.name)) this.raise(prop.key.start, "Binding " + prop.key.name);
      prop.value = this.parseMaybeDefault(startPos, startLoc, prop.key);
    } else if (this.type === _tokentype.types.eq && refShorthandDefaultPos) {
      if (!refShorthandDefaultPos.start) refShorthandDefaultPos.start = this.start;
      prop.value = this.parseMaybeDefault(startPos, startLoc, prop.key);
    } else {
      prop.value = prop.key;
    }
    prop.shorthand = true;
  } else this.unexpected();
};

pp.parsePropertyName = function (prop) {
  if (this.options.ecmaVersion >= 6) {
    if (this.eat(_tokentype.types.bracketL)) {
      prop.computed = true;
      prop.key = this.parseMaybeAssign();
      this.expect(_tokentype.types.bracketR);
      return prop.key;
    } else {
      prop.computed = false;
    }
  }
  return prop.key = this.type === _tokentype.types.num || this.type === _tokentype.types.string ? this.parseExprAtom() : this.parseIdent(true);
};

// Initialize empty function node.

pp.initFunction = function (node) {
  node.id = null;
  if (this.options.ecmaVersion >= 6) {
    node.generator = false;
    node.expression = false;
  }
};

// Parse object or class method.

pp.parseMethod = function (isGenerator) {
  var node = this.startNode();
  this.initFunction(node);
  this.expect(_tokentype.types.parenL);
  node.params = this.parseBindingList(_tokentype.types.parenR, false, false);
  var allowExpressionBody = undefined;
  if (this.options.ecmaVersion >= 6) {
    node.generator = isGenerator;
  }
  this.parseFunctionBody(node, false);
  return this.finishNode(node, "FunctionExpression");
};

// Parse arrow function expression with given parameters.

pp.parseArrowExpression = function (node, params) {
  this.initFunction(node);
  node.params = this.toAssignableList(params, true);
  this.parseFunctionBody(node, true);
  return this.finishNode(node, "ArrowFunctionExpression");
};

// Parse function body and check parameters.

pp.parseFunctionBody = function (node, allowExpression) {
  var isExpression = allowExpression && this.type !== _tokentype.types.braceL;

  if (isExpression) {
    node.body = this.parseMaybeAssign();
    node.expression = true;
  } else {
    // Start a new scope with regard to labels and the `inFunction`
    // flag (restore them to their old value afterwards).
    var oldInFunc = this.inFunction,
        oldInGen = this.inGenerator,
        oldLabels = this.labels;
    this.inFunction = true;this.inGenerator = node.generator;this.labels = [];
    node.body = this.parseBlock(true);
    node.expression = false;
    this.inFunction = oldInFunc;this.inGenerator = oldInGen;this.labels = oldLabels;
  }

  // If this is a strict mode function, verify that argument names
  // are not repeated, and it does not try to bind the words `eval`
  // or `arguments`.
  if (this.strict || !isExpression && node.body.body.length && this.isUseStrict(node.body.body[0])) {
    var nameHash = {},
        oldStrict = this.strict;
    this.strict = true;
    if (node.id) this.checkLVal(node.id, true);
    for (var i = 0; i < node.params.length; i++) {
      this.checkLVal(node.params[i], true, nameHash);
    }this.strict = oldStrict;
  }
};

// Parses a comma-separated list of expressions, and returns them as
// an array. `close` is the token type that ends the list, and
// `allowEmpty` can be turned on to allow subsequent commas with
// nothing in between them to be parsed as `null` (which is needed
// for array literals).

pp.parseExprList = function (close, allowTrailingComma, allowEmpty, refShorthandDefaultPos) {
  var elts = [],
      first = true;
  while (!this.eat(close)) {
    if (!first) {
      this.expect(_tokentype.types.comma);
      if (allowTrailingComma && this.afterTrailingComma(close)) break;
    } else first = false;

    var elt = undefined;
    if (allowEmpty && this.type === _tokentype.types.comma) elt = null;else if (this.type === _tokentype.types.ellipsis) elt = this.parseSpread(refShorthandDefaultPos);else elt = this.parseMaybeAssign(false, refShorthandDefaultPos);
    elts.push(elt);
  }
  return elts;
};

// Parse the next token as an identifier. If `liberal` is true (used
// when parsing properties), it will also convert keywords into
// identifiers.

pp.parseIdent = function (liberal) {
  var node = this.startNode();
  if (liberal && this.options.allowReserved == "never") liberal = false;
  if (this.type === _tokentype.types.name) {
    if (!liberal && (!this.options.allowReserved && this.isReservedWord(this.value) || this.strict && _identifier.reservedWords.strict(this.value) && (this.options.ecmaVersion >= 6 || this.input.slice(this.start, this.end).indexOf("\\") == -1))) this.raise(this.start, "The keyword '" + this.value + "' is reserved");
    node.name = this.value;
  } else if (liberal && this.type.keyword) {
    node.name = this.type.keyword;
  } else {
    this.unexpected();
  }
  this.next();
  return this.finishNode(node, "Identifier");
};

// Parses yield expression inside generator.

pp.parseYield = function () {
  var node = this.startNode();
  this.next();
  if (this.type == _tokentype.types.semi || this.canInsertSemicolon() || this.type != _tokentype.types.star && !this.type.startsExpr) {
    node.delegate = false;
    node.argument = null;
  } else {
    node.delegate = this.eat(_tokentype.types.star);
    node.argument = this.parseMaybeAssign();
  }
  return this.finishNode(node, "YieldExpression");
};

// Parses array and generator comprehensions.

pp.parseComprehension = function (node, isGenerator) {
  node.blocks = [];
  while (this.type === _tokentype.types._for) {
    var block = this.startNode();
    this.next();
    this.expect(_tokentype.types.parenL);
    block.left = this.parseBindingAtom();
    this.checkLVal(block.left, true);
    this.expectContextual("of");
    block.right = this.parseExpression();
    this.expect(_tokentype.types.parenR);
    node.blocks.push(this.finishNode(block, "ComprehensionBlock"));
  }
  node.filter = this.eat(_tokentype.types._if) ? this.parseParenExpression() : null;
  node.body = this.parseExpression();
  this.expect(isGenerator ? _tokentype.types.parenR : _tokentype.types.bracketR);
  node.generator = isGenerator;
  return this.finishNode(node, "ComprehensionExpression");
};

},{"./identifier":2,"./state":10,"./tokentype":14,"./util":15}],2:[function(_dereq_,module,exports){
// This is a trick taken from Esprima. It turns out that, on
// non-Chrome browsers, to check whether a string is in a set, a
// predicate containing a big ugly `switch` statement is faster than
// a regular expression, and on Chrome the two are about on par.
// This function uses `eval` (non-lexical) to produce such a
// predicate from a space-separated string of words.
//
// It starts by sorting the words by length.

"use strict";

exports.__esModule = true;
exports.isIdentifierStart = isIdentifierStart;
exports.isIdentifierChar = isIdentifierChar;
function makePredicate(words) {
  words = words.split(" ");
  var f = "",
      cats = [];
  out: for (var i = 0; i < words.length; ++i) {
    for (var j = 0; j < cats.length; ++j) {
      if (cats[j][0].length == words[i].length) {
        cats[j].push(words[i]);
        continue out;
      }
    }cats.push([words[i]]);
  }
  function compareTo(arr) {
    if (arr.length == 1) return f += "return str === " + JSON.stringify(arr[0]) + ";";
    f += "switch(str){";
    for (var i = 0; i < arr.length; ++i) {
      f += "case " + JSON.stringify(arr[i]) + ":";
    }f += "return true}return false;";
  }

  // When there are more than three length categories, an outer
  // switch first dispatches on the lengths, to save on comparisons.

  if (cats.length > 3) {
    cats.sort(function (a, b) {
      return b.length - a.length;
    });
    f += "switch(str.length){";
    for (var i = 0; i < cats.length; ++i) {
      var cat = cats[i];
      f += "case " + cat[0].length + ":";
      compareTo(cat);
    }
    f += "}"

    // Otherwise, simply generate a flat `switch` statement.

    ;
  } else {
    compareTo(words);
  }
  return new Function("str", f);
}

// Reserved word lists for various dialects of the language

var reservedWords = {
  3: makePredicate("abstract boolean byte char class double enum export extends final float goto implements import int interface long native package private protected public short static super synchronized throws transient volatile"),
  5: makePredicate("class enum extends super const export import"),
  6: makePredicate("enum await"),
  strict: makePredicate("implements interface let package private protected public static yield"),
  strictBind: makePredicate("eval arguments")
};

exports.reservedWords = reservedWords;
// And the keywords

var ecma5AndLessKeywords = "break case catch continue debugger default do else finally for function if return switch throw try var while with null true false instanceof typeof void delete new in this";

var keywords = {
  5: makePredicate(ecma5AndLessKeywords),
  6: makePredicate(ecma5AndLessKeywords + " let const class extends export import yield super")
};

exports.keywords = keywords;
// ## Character categories

// Big ugly regular expressions that match characters in the
// whitespace, identifier, and identifier-start categories. These
// are only applied when a character is found to actually have a
// code point above 128.
// Generated by `tools/generate-identifier-regex.js`.

var nonASCIIidentifierStartChars = "ªµºÀ-ÖØ-öø-ˁˆ-ˑˠ-ˤˬˮͰ-ʹͶͷͺ-ͽͿΆΈ-ΊΌΎ-ΡΣ-ϵϷ-ҁҊ-ԯԱ-Ֆՙա-ևא-תװ-ײؠ-يٮٯٱ-ۓەۥۦۮۯۺ-ۼۿܐܒ-ܯݍ-ޥޱߊ-ߪߴߵߺࠀ-ࠕࠚࠤࠨࡀ-ࡘࢠ-ࢲऄ-हऽॐक़-ॡॱ-ঀঅ-ঌএঐও-নপ-রলশ-হঽৎড়ঢ়য়-ৡৰৱਅ-ਊਏਐਓ-ਨਪ-ਰਲਲ਼ਵਸ਼ਸਹਖ਼-ੜਫ਼ੲ-ੴઅ-ઍએ-ઑઓ-નપ-રલળવ-હઽૐૠૡଅ-ଌଏଐଓ-ନପ-ରଲଳଵ-ହଽଡ଼ଢ଼ୟ-ୡୱஃஅ-ஊஎ-ஐஒ-கஙசஜஞடணதந-பம-ஹௐఅ-ఌఎ-ఐఒ-నప-హఽౘౙౠౡಅ-ಌಎ-ಐಒ-ನಪ-ಳವ-ಹಽೞೠೡೱೲഅ-ഌഎ-ഐഒ-ഺഽൎൠൡൺ-ൿඅ-ඖක-නඳ-රලව-ෆก-ะาำเ-ๆກຂຄງຈຊຍດ-ທນ-ຟມ-ຣລວສຫອ-ະາຳຽເ-ໄໆໜ-ໟༀཀ-ཇཉ-ཬྈ-ྌက-ဪဿၐ-ၕၚ-ၝၡၥၦၮ-ၰၵ-ႁႎႠ-ჅჇჍა-ჺჼ-ቈቊ-ቍቐ-ቖቘቚ-ቝበ-ኈኊ-ኍነ-ኰኲ-ኵኸ-ኾዀዂ-ዅወ-ዖዘ-ጐጒ-ጕጘ-ፚᎀ-ᎏᎠ-Ᏼᐁ-ᙬᙯ-ᙿᚁ-ᚚᚠ-ᛪᛮ-ᛸᜀ-ᜌᜎ-ᜑᜠ-ᜱᝀ-ᝑᝠ-ᝬᝮ-ᝰក-ឳៗៜᠠ-ᡷᢀ-ᢨᢪᢰ-ᣵᤀ-ᤞᥐ-ᥭᥰ-ᥴᦀ-ᦫᧁ-ᧇᨀ-ᨖᨠ-ᩔᪧᬅ-ᬳᭅ-ᭋᮃ-ᮠᮮᮯᮺ-ᯥᰀ-ᰣᱍ-ᱏᱚ-ᱽᳩ-ᳬᳮ-ᳱᳵᳶᴀ-ᶿḀ-ἕἘ-Ἕἠ-ὅὈ-Ὅὐ-ὗὙὛὝὟ-ώᾀ-ᾴᾶ-ᾼιῂ-ῄῆ-ῌῐ-ΐῖ-Ίῠ-Ῥῲ-ῴῶ-ῼⁱⁿₐ-ₜℂℇℊ-ℓℕ℘-ℝℤΩℨK-ℹℼ-ℿⅅ-ⅉⅎⅠ-ↈⰀ-Ⱞⰰ-ⱞⱠ-ⳤⳫ-ⳮⳲⳳⴀ-ⴥⴧⴭⴰ-ⵧⵯⶀ-ⶖⶠ-ⶦⶨ-ⶮⶰ-ⶶⶸ-ⶾⷀ-ⷆⷈ-ⷎⷐ-ⷖⷘ-ⷞ々-〇〡-〩〱-〵〸-〼ぁ-ゖ゛-ゟァ-ヺー-ヿㄅ-ㄭㄱ-ㆎㆠ-ㆺㇰ-ㇿ㐀-䶵一-鿌ꀀ-ꒌꓐ-ꓽꔀ-ꘌꘐ-ꘟꘪꘫꙀ-ꙮꙿ-ꚝꚠ-ꛯꜗ-ꜟꜢ-ꞈꞋ-ꞎꞐ-ꞭꞰꞱꟷ-ꠁꠃ-ꠅꠇ-ꠊꠌ-ꠢꡀ-ꡳꢂ-ꢳꣲ-ꣷꣻꤊ-ꤥꤰ-ꥆꥠ-ꥼꦄ-ꦲꧏꧠ-ꧤꧦ-ꧯꧺ-ꧾꨀ-ꨨꩀ-ꩂꩄ-ꩋꩠ-ꩶꩺꩾ-ꪯꪱꪵꪶꪹ-ꪽꫀꫂꫛ-ꫝꫠ-ꫪꫲ-ꫴꬁ-ꬆꬉ-ꬎꬑ-ꬖꬠ-ꬦꬨ-ꬮꬰ-ꭚꭜ-ꭟꭤꭥꯀ-ꯢ가-힣ힰ-ퟆퟋ-ퟻ豈-舘並-龎ﬀ-ﬆﬓ-ﬗיִײַ-ﬨשׁ-זּטּ-לּמּנּסּףּפּצּ-ﮱﯓ-ﴽﵐ-ﶏﶒ-ﷇﷰ-ﷻﹰ-ﹴﹶ-ﻼＡ-Ｚａ-ｚｦ-ﾾￂ-ￇￊ-ￏￒ-ￗￚ-ￜ";
var nonASCIIidentifierChars = "‌‍·̀-ͯ·҃-֑҇-ׇֽֿׁׂׅׄؐ-ًؚ-٩ٰۖ-ۜ۟-۪ۤۧۨ-ۭ۰-۹ܑܰ-݊ަ-ް߀-߉߫-߳ࠖ-࠙ࠛ-ࠣࠥ-ࠧࠩ-࡙࠭-࡛ࣤ-ःऺ-़ा-ॏ॑-ॗॢॣ०-९ঁ-ঃ়া-ৄেৈো-্ৗৢৣ০-৯ਁ-ਃ਼ਾ-ੂੇੈੋ-੍ੑ੦-ੱੵઁ-ઃ઼ા-ૅે-ૉો-્ૢૣ૦-૯ଁ-ଃ଼ା-ୄେୈୋ-୍ୖୗୢୣ୦-୯ஂா-ூெ-ைொ-்ௗ௦-௯ఀ-ఃా-ౄె-ైొ-్ౕౖౢౣ౦-౯ಁ-ಃ಼ಾ-ೄೆ-ೈೊ-್ೕೖೢೣ೦-೯ഁ-ഃാ-ൄെ-ൈൊ-്ൗൢൣ൦-൯ංඃ්ා-ුූෘ-ෟ෦-෯ෲෳัิ-ฺ็-๎๐-๙ັິ-ູົຼ່-ໍ໐-໙༘༙༠-༩༹༵༷༾༿ཱ-྄྆྇ྍ-ྗྙ-ྼ࿆ါ-ှ၀-၉ၖ-ၙၞ-ၠၢ-ၤၧ-ၭၱ-ၴႂ-ႍႏ-ႝ፝-፟፩-፱ᜒ-᜔ᜲ-᜴ᝒᝓᝲᝳ឴-៓៝០-៩᠋-᠍᠐-᠙ᢩᤠ-ᤫᤰ-᤻᥆-᥏ᦰ-ᧀᧈᧉ᧐-᧚ᨗ-ᨛᩕ-ᩞ᩠-᩿᩼-᪉᪐-᪙᪰-᪽ᬀ-ᬄ᬴-᭄᭐-᭙᭫-᭳ᮀ-ᮂᮡ-ᮭ᮰-᮹᯦-᯳ᰤ-᰷᱀-᱉᱐-᱙᳐-᳔᳒-᳨᳭ᳲ-᳴᳸᳹᷀-᷵᷼-᷿‿⁀⁔⃐-⃥⃜⃡-⃰⳯-⵿⳱ⷠ-〪ⷿ-゙゚〯꘠-꘩꙯ꙴ-꙽ꚟ꛰꛱ꠂ꠆ꠋꠣ-ꠧꢀꢁꢴ-꣄꣐-꣙꣠-꣱꤀-꤉ꤦ-꤭ꥇ-꥓ꦀ-ꦃ꦳-꧀꧐-꧙ꧥ꧰-꧹ꨩ-ꨶꩃꩌꩍ꩐-꩙ꩻ-ꩽꪰꪲ-ꪴꪷꪸꪾ꪿꫁ꫫ-ꫯꫵ꫶ꯣ-ꯪ꯬꯭꯰-꯹ﬞ︀-️︠-︭︳︴﹍-﹏０-９＿";

var nonASCIIidentifierStart = new RegExp("[" + nonASCIIidentifierStartChars + "]");
var nonASCIIidentifier = new RegExp("[" + nonASCIIidentifierStartChars + nonASCIIidentifierChars + "]");

nonASCIIidentifierStartChars = nonASCIIidentifierChars = null;

// These are a run-length and offset encoded representation of the
// >0xffff code points that are a valid part of identifiers. The
// offset starts at 0x10000, and each pair of numbers represents an
// offset to the next range, and then a size of the range. They were
// generated by tools/generate-identifier-regex.js
var astralIdentifierStartCodes = [0, 11, 2, 25, 2, 18, 2, 1, 2, 14, 3, 13, 35, 122, 70, 52, 268, 28, 4, 48, 48, 31, 17, 26, 6, 37, 11, 29, 3, 35, 5, 7, 2, 4, 43, 157, 99, 39, 9, 51, 157, 310, 10, 21, 11, 7, 153, 5, 3, 0, 2, 43, 2, 1, 4, 0, 3, 22, 11, 22, 10, 30, 98, 21, 11, 25, 71, 55, 7, 1, 65, 0, 16, 3, 2, 2, 2, 26, 45, 28, 4, 28, 36, 7, 2, 27, 28, 53, 11, 21, 11, 18, 14, 17, 111, 72, 955, 52, 76, 44, 33, 24, 27, 35, 42, 34, 4, 0, 13, 47, 15, 3, 22, 0, 38, 17, 2, 24, 133, 46, 39, 7, 3, 1, 3, 21, 2, 6, 2, 1, 2, 4, 4, 0, 32, 4, 287, 47, 21, 1, 2, 0, 185, 46, 82, 47, 21, 0, 60, 42, 502, 63, 32, 0, 449, 56, 1288, 920, 104, 110, 2962, 1070, 13266, 568, 8, 30, 114, 29, 19, 47, 17, 3, 32, 20, 6, 18, 881, 68, 12, 0, 67, 12, 16481, 1, 3071, 106, 6, 12, 4, 8, 8, 9, 5991, 84, 2, 70, 2, 1, 3, 0, 3, 1, 3, 3, 2, 11, 2, 0, 2, 6, 2, 64, 2, 3, 3, 7, 2, 6, 2, 27, 2, 3, 2, 4, 2, 0, 4, 6, 2, 339, 3, 24, 2, 24, 2, 30, 2, 24, 2, 30, 2, 24, 2, 30, 2, 24, 2, 30, 2, 24, 2, 7, 4149, 196, 1340, 3, 2, 26, 2, 1, 2, 0, 3, 0, 2, 9, 2, 3, 2, 0, 2, 0, 7, 0, 5, 0, 2, 0, 2, 0, 2, 2, 2, 1, 2, 0, 3, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 1, 2, 0, 3, 3, 2, 6, 2, 3, 2, 3, 2, 0, 2, 9, 2, 16, 6, 2, 2, 4, 2, 16, 4421, 42710, 42, 4148, 12, 221, 16355, 541];
var astralIdentifierCodes = [509, 0, 227, 0, 150, 4, 294, 9, 1368, 2, 2, 1, 6, 3, 41, 2, 5, 0, 166, 1, 1306, 2, 54, 14, 32, 9, 16, 3, 46, 10, 54, 9, 7, 2, 37, 13, 2, 9, 52, 0, 13, 2, 49, 13, 16, 9, 83, 11, 168, 11, 6, 9, 8, 2, 57, 0, 2, 6, 3, 1, 3, 2, 10, 0, 11, 1, 3, 6, 4, 4, 316, 19, 13, 9, 214, 6, 3, 8, 112, 16, 16, 9, 82, 12, 9, 9, 535, 9, 20855, 9, 135, 4, 60, 6, 26, 9, 1016, 45, 17, 3, 19723, 1, 5319, 4, 4, 5, 9, 7, 3, 6, 31, 3, 149, 2, 1418, 49, 4305, 6, 792618, 239];

// This has a complexity linear to the value of the code. The
// assumption is that looking up astral identifier characters is
// rare.
function isInAstralSet(code, set) {
  var pos = 0x10000;
  for (var i = 0; i < set.length; i += 2) {
    pos += set[i];
    if (pos > code) return false;
    pos += set[i + 1];
    if (pos >= code) return true;
  }
}

// Test whether a given character code starts an identifier.

function isIdentifierStart(code, astral) {
  if (code < 65) return code === 36;
  if (code < 91) return true;
  if (code < 97) return code === 95;
  if (code < 123) return true;
  if (code <= 0xffff) return code >= 0xaa && nonASCIIidentifierStart.test(String.fromCharCode(code));
  if (astral === false) return false;
  return isInAstralSet(code, astralIdentifierStartCodes);
}

// Test whether a given character is part of an identifier.

function isIdentifierChar(code, astral) {
  if (code < 48) return code === 36;
  if (code < 58) return true;
  if (code < 65) return false;
  if (code < 91) return true;
  if (code < 97) return code === 95;
  if (code < 123) return true;
  if (code <= 0xffff) return code >= 0xaa && nonASCIIidentifier.test(String.fromCharCode(code));
  if (astral === false) return false;
  return isInAstralSet(code, astralIdentifierStartCodes) || isInAstralSet(code, astralIdentifierCodes);
}

},{}],3:[function(_dereq_,module,exports){
// Acorn is a tiny, fast JavaScript parser written in JavaScript.
//
// Acorn was written by Marijn Haverbeke, Ingvar Stepanyan, and
// various contributors and released under an MIT license.
//
// Git repositories for Acorn are available at
//
//     http://marijnhaverbeke.nl/git/acorn
//     https://github.com/marijnh/acorn.git
//
// Please use the [github bug tracker][ghbt] to report issues.
//
// [ghbt]: https://github.com/marijnh/acorn/issues
//
// This file defines the main parser interface. The library also comes
// with a [error-tolerant parser][dammit] and an
// [abstract syntax tree walker][walk], defined in other files.
//
// [dammit]: acorn_loose.js
// [walk]: util/walk.js

"use strict";

exports.__esModule = true;
exports.parse = parse;
exports.parseExpressionAt = parseExpressionAt;
exports.tokenizer = tokenizer;

var _state = _dereq_("./state");

var _options = _dereq_("./options");

_dereq_("./parseutil");

_dereq_("./statement");

_dereq_("./lval");

_dereq_("./expression");

_dereq_("./location");

exports.Parser = _state.Parser;
exports.plugins = _state.plugins;
exports.defaultOptions = _options.defaultOptions;

var _locutil = _dereq_("./locutil");

exports.Position = _locutil.Position;
exports.SourceLocation = _locutil.SourceLocation;
exports.getLineInfo = _locutil.getLineInfo;

var _node = _dereq_("./node");

exports.Node = _node.Node;

var _tokentype = _dereq_("./tokentype");

exports.TokenType = _tokentype.TokenType;
exports.tokTypes = _tokentype.types;

var _tokencontext = _dereq_("./tokencontext");

exports.TokContext = _tokencontext.TokContext;
exports.tokContexts = _tokencontext.types;

var _identifier = _dereq_("./identifier");

exports.isIdentifierChar = _identifier.isIdentifierChar;
exports.isIdentifierStart = _identifier.isIdentifierStart;

var _tokenize = _dereq_("./tokenize");

exports.Token = _tokenize.Token;

var _whitespace = _dereq_("./whitespace");

exports.isNewLine = _whitespace.isNewLine;
exports.lineBreak = _whitespace.lineBreak;
exports.lineBreakG = _whitespace.lineBreakG;
var version = "2.4.0";

exports.version = version;
// The main exported interface (under `self.acorn` when in the
// browser) is a `parse` function that takes a code string and
// returns an abstract syntax tree as specified by [Mozilla parser
// API][api].
//
// [api]: https://developer.mozilla.org/en-US/docs/SpiderMonkey/Parser_API

function parse(input, options) {
  return new _state.Parser(options, input).parse();
}

// This function tries to parse a single expression at a given
// offset in a string. Useful for parsing mixed-language formats
// that embed JavaScript expressions.

function parseExpressionAt(input, pos, options) {
  var p = new _state.Parser(options, input, pos);
  p.nextToken();
  return p.parseExpression();
}

// Acorn is organized as a tokenizer and a recursive-descent parser.
// The `tokenize` export provides an interface to the tokenizer.

function tokenizer(input, options) {
  return new _state.Parser(options, input);
}

},{"./expression":1,"./identifier":2,"./location":4,"./locutil":5,"./lval":6,"./node":7,"./options":8,"./parseutil":9,"./state":10,"./statement":11,"./tokencontext":12,"./tokenize":13,"./tokentype":14,"./whitespace":16}],4:[function(_dereq_,module,exports){
"use strict";

var _state = _dereq_("./state");

var _locutil = _dereq_("./locutil");

var pp = _state.Parser.prototype;

// This function is used to raise exceptions on parse errors. It
// takes an offset integer (into the current `input`) to indicate
// the location of the error, attaches the position to the end
// of the error message, and then raises a `SyntaxError` with that
// message.

pp.raise = function (pos, message) {
  var loc = _locutil.getLineInfo(this.input, pos);
  message += " (" + loc.line + ":" + loc.column + ")";
  var err = new SyntaxError(message);
  err.pos = pos;err.loc = loc;err.raisedAt = this.pos;
  throw err;
};

pp.curPosition = function () {
  if (this.options.locations) {
    return new _locutil.Position(this.curLine, this.pos - this.lineStart);
  }
};

},{"./locutil":5,"./state":10}],5:[function(_dereq_,module,exports){
"use strict";

exports.__esModule = true;
exports.getLineInfo = getLineInfo;

function _classCallCheck(instance, Constructor) { if (!(instance instanceof Constructor)) { throw new TypeError("Cannot call a class as a function"); } }

var _whitespace = _dereq_("./whitespace");

// These are used when `options.locations` is on, for the
// `startLoc` and `endLoc` properties.

var Position = (function () {
  function Position(line, col) {
    _classCallCheck(this, Position);

    this.line = line;
    this.column = col;
  }

  Position.prototype.offset = function offset(n) {
    return new Position(this.line, this.column + n);
  };

  return Position;
})();

exports.Position = Position;

var SourceLocation = function SourceLocation(p, start, end) {
  _classCallCheck(this, SourceLocation);

  this.start = start;
  this.end = end;
  if (p.sourceFile !== null) this.source = p.sourceFile;
};

exports.SourceLocation = SourceLocation;

// The `getLineInfo` function is mostly useful when the
// `locations` option is off (for performance reasons) and you
// want to find the line/column position for a given character
// offset. `input` should be the code string that the offset refers
// into.

function getLineInfo(input, offset) {
  for (var line = 1, cur = 0;;) {
    _whitespace.lineBreakG.lastIndex = cur;
    var match = _whitespace.lineBreakG.exec(input);
    if (match && match.index < offset) {
      ++line;
      cur = match.index + match[0].length;
    } else {
      return new Position(line, offset - cur);
    }
  }
}

},{"./whitespace":16}],6:[function(_dereq_,module,exports){
"use strict";

var _tokentype = _dereq_("./tokentype");

var _state = _dereq_("./state");

var _identifier = _dereq_("./identifier");

var _util = _dereq_("./util");

var pp = _state.Parser.prototype;

// Convert existing expression atom to assignable pattern
// if possible.

pp.toAssignable = function (node, isBinding) {
  if (this.options.ecmaVersion >= 6 && node) {
    switch (node.type) {
      case "Identifier":
      case "ObjectPattern":
      case "ArrayPattern":
      case "AssignmentPattern":
        break;

      case "ObjectExpression":
        node.type = "ObjectPattern";
        for (var i = 0; i < node.properties.length; i++) {
          var prop = node.properties[i];
          if (prop.kind !== "init") this.raise(prop.key.start, "Object pattern can't contain getter or setter");
          this.toAssignable(prop.value, isBinding);
        }
        break;

      case "ArrayExpression":
        node.type = "ArrayPattern";
        this.toAssignableList(node.elements, isBinding);
        break;

      case "AssignmentExpression":
        if (node.operator === "=") {
          node.type = "AssignmentPattern";
          delete node.operator;
        } else {
          this.raise(node.left.end, "Only '=' operator can be used for specifying default value.");
        }
        break;

      case "ParenthesizedExpression":
        node.expression = this.toAssignable(node.expression, isBinding);
        break;

      case "MemberExpression":
        if (!isBinding) break;

      default:
        this.raise(node.start, "Assigning to rvalue");
    }
  }
  return node;
};

// Convert list of expression atoms to binding list.

pp.toAssignableList = function (exprList, isBinding) {
  var end = exprList.length;
  if (end) {
    var last = exprList[end - 1];
    if (last && last.type == "RestElement") {
      --end;
    } else if (last && last.type == "SpreadElement") {
      last.type = "RestElement";
      var arg = last.argument;
      this.toAssignable(arg, isBinding);
      if (arg.type !== "Identifier" && arg.type !== "MemberExpression" && arg.type !== "ArrayPattern") this.unexpected(arg.start);
      --end;
    }
  }
  for (var i = 0; i < end; i++) {
    var elt = exprList[i];
    if (elt) this.toAssignable(elt, isBinding);
  }
  return exprList;
};

// Parses spread element.

pp.parseSpread = function (refShorthandDefaultPos) {
  var node = this.startNode();
  this.next();
  node.argument = this.parseMaybeAssign(refShorthandDefaultPos);
  return this.finishNode(node, "SpreadElement");
};

pp.parseRest = function () {
  var node = this.startNode();
  this.next();
  node.argument = this.type === _tokentype.types.name || this.type === _tokentype.types.bracketL ? this.parseBindingAtom() : this.unexpected();
  return this.finishNode(node, "RestElement");
};

// Parses lvalue (assignable) atom.

pp.parseBindingAtom = function () {
  if (this.options.ecmaVersion < 6) return this.parseIdent();
  switch (this.type) {
    case _tokentype.types.name:
      return this.parseIdent();

    case _tokentype.types.bracketL:
      var node = this.startNode();
      this.next();
      node.elements = this.parseBindingList(_tokentype.types.bracketR, true, true);
      return this.finishNode(node, "ArrayPattern");

    case _tokentype.types.braceL:
      return this.parseObj(true);

    default:
      this.unexpected();
  }
};

pp.parseBindingList = function (close, allowEmpty, allowTrailingComma) {
  var elts = [],
      first = true;
  while (!this.eat(close)) {
    if (first) first = false;else this.expect(_tokentype.types.comma);
    if (allowEmpty && this.type === _tokentype.types.comma) {
      elts.push(null);
    } else if (allowTrailingComma && this.afterTrailingComma(close)) {
      break;
    } else if (this.type === _tokentype.types.ellipsis) {
      var rest = this.parseRest();
      this.parseBindingListItem(rest);
      elts.push(rest);
      this.expect(close);
      break;
    } else {
      var elem = this.parseMaybeDefault(this.start, this.startLoc);
      this.parseBindingListItem(elem);
      elts.push(elem);
    }
  }
  return elts;
};

pp.parseBindingListItem = function (param) {
  return param;
};

// Parses assignment pattern around given atom if possible.

pp.parseMaybeDefault = function (startPos, startLoc, left) {
  left = left || this.parseBindingAtom();
  if (this.options.ecmaVersion < 6 || !this.eat(_tokentype.types.eq)) return left;
  var node = this.startNodeAt(startPos, startLoc);
  node.left = left;
  node.right = this.parseMaybeAssign();
  return this.finishNode(node, "AssignmentPattern");
};

// Verify that a node is an lval — something that can be assigned
// to.

pp.checkLVal = function (expr, isBinding, checkClashes) {
  switch (expr.type) {
    case "Identifier":
      if (this.strict && (_identifier.reservedWords.strictBind(expr.name) || _identifier.reservedWords.strict(expr.name))) this.raise(expr.start, (isBinding ? "Binding " : "Assigning to ") + expr.name + " in strict mode");
      if (checkClashes) {
        if (_util.has(checkClashes, expr.name)) this.raise(expr.start, "Argument name clash in strict mode");
        checkClashes[expr.name] = true;
      }
      break;

    case "MemberExpression":
      if (isBinding) this.raise(expr.start, (isBinding ? "Binding" : "Assigning to") + " member expression");
      break;

    case "ObjectPattern":
      for (var i = 0; i < expr.properties.length; i++) {
        this.checkLVal(expr.properties[i].value, isBinding, checkClashes);
      }break;

    case "ArrayPattern":
      for (var i = 0; i < expr.elements.length; i++) {
        var elem = expr.elements[i];
        if (elem) this.checkLVal(elem, isBinding, checkClashes);
      }
      break;

    case "AssignmentPattern":
      this.checkLVal(expr.left, isBinding, checkClashes);
      break;

    case "RestElement":
      this.checkLVal(expr.argument, isBinding, checkClashes);
      break;

    case "ParenthesizedExpression":
      this.checkLVal(expr.expression, isBinding, checkClashes);
      break;

    default:
      this.raise(expr.start, (isBinding ? "Binding" : "Assigning to") + " rvalue");
  }
};

},{"./identifier":2,"./state":10,"./tokentype":14,"./util":15}],7:[function(_dereq_,module,exports){
"use strict";

exports.__esModule = true;

function _classCallCheck(instance, Constructor) { if (!(instance instanceof Constructor)) { throw new TypeError("Cannot call a class as a function"); } }

var _state = _dereq_("./state");

var _locutil = _dereq_("./locutil");

var Node = function Node(parser, pos, loc) {
  _classCallCheck(this, Node);

  this.type = "";
  this.start = pos;
  this.end = 0;
  if (parser.options.locations) this.loc = new _locutil.SourceLocation(parser, loc);
  if (parser.options.directSourceFile) this.sourceFile = parser.options.directSourceFile;
  if (parser.options.ranges) this.range = [pos, 0];
};

exports.Node = Node;

// Start an AST node, attaching a start offset.

var pp = _state.Parser.prototype;

pp.startNode = function () {
  return new Node(this, this.start, this.startLoc);
};

pp.startNodeAt = function (pos, loc) {
  return new Node(this, pos, loc);
};

// Finish an AST node, adding `type` and `end` properties.

function finishNodeAt(node, type, pos, loc) {
  node.type = type;
  node.end = pos;
  if (this.options.locations) node.loc.end = loc;
  if (this.options.ranges) node.range[1] = pos;
  return node;
}

pp.finishNode = function (node, type) {
  return finishNodeAt.call(this, node, type, this.lastTokEnd, this.lastTokEndLoc);
};

// Finish node at given position

pp.finishNodeAt = function (node, type, pos, loc) {
  return finishNodeAt.call(this, node, type, pos, loc);
};

},{"./locutil":5,"./state":10}],8:[function(_dereq_,module,exports){
"use strict";

exports.__esModule = true;
exports.getOptions = getOptions;

var _util = _dereq_("./util");

var _locutil = _dereq_("./locutil");

// A second optional argument can be given to further configure
// the parser process. These options are recognized:

var defaultOptions = {
  // `ecmaVersion` indicates the ECMAScript version to parse. Must
  // be either 3, or 5, or 6. This influences support for strict
  // mode, the set of reserved words, support for getters and
  // setters and other features.
  ecmaVersion: 5,
  // Source type ("script" or "module") for different semantics
  sourceType: "script",
  // `onInsertedSemicolon` can be a callback that will be called
  // when a semicolon is automatically inserted. It will be passed
  // th position of the comma as an offset, and if `locations` is
  // enabled, it is given the location as a `{line, column}` object
  // as second argument.
  onInsertedSemicolon: null,
  // `onTrailingComma` is similar to `onInsertedSemicolon`, but for
  // trailing commas.
  onTrailingComma: null,
  // By default, reserved words are not enforced. Disable
  // `allowReserved` to enforce them. When this option has the
  // value "never", reserved words and keywords can also not be
  // used as property names.
  allowReserved: true,
  // When enabled, a return at the top level is not considered an
  // error.
  allowReturnOutsideFunction: false,
  // When enabled, import/export statements are not constrained to
  // appearing at the top of the program.
  allowImportExportEverywhere: false,
  // When enabled, hashbang directive in the beginning of file
  // is allowed and treated as a line comment.
  allowHashBang: false,
  // When `locations` is on, `loc` properties holding objects with
  // `start` and `end` properties in `{line, column}` form (with
  // line being 1-based and column 0-based) will be attached to the
  // nodes.
  locations: false,
  // A function can be passed as `onToken` option, which will
  // cause Acorn to call that function with object in the same
  // format as tokenize() returns. Note that you are not
  // allowed to call the parser from the callback—that will
  // corrupt its internal state.
  onToken: null,
  // A function can be passed as `onComment` option, which will
  // cause Acorn to call that function with `(block, text, start,
  // end)` parameters whenever a comment is skipped. `block` is a
  // boolean indicating whether this is a block (`/* */`) comment,
  // `text` is the content of the comment, and `start` and `end` are
  // character offsets that denote the start and end of the comment.
  // When the `locations` option is on, two more parameters are
  // passed, the full `{line, column}` locations of the start and
  // end of the comments. Note that you are not allowed to call the
  // parser from the callback—that will corrupt its internal state.
  onComment: null,
  // Nodes have their start and end characters offsets recorded in
  // `start` and `end` properties (directly on the node, rather than
  // the `loc` object, which holds line/column data. To also add a
  // [semi-standardized][range] `range` property holding a `[start,
  // end]` array with the same numbers, set the `ranges` option to
  // `true`.
  //
  // [range]: https://bugzilla.mozilla.org/show_bug.cgi?id=745678
  ranges: false,
  // It is possible to parse multiple files into a single AST by
  // passing the tree produced by parsing the first file as
  // `program` option in subsequent parses. This will add the
  // toplevel forms of the parsed file to the `Program` (top) node
  // of an existing parse tree.
  program: null,
  // When `locations` is on, you can pass this to record the source
  // file in every node's `loc` object.
  sourceFile: null,
  // This value, if given, is stored in every node, whether
  // `locations` is on or off.
  directSourceFile: null,
  // When enabled, parenthesized expressions are represented by
  // (non-standard) ParenthesizedExpression nodes
  preserveParens: false,
  plugins: {}
};

exports.defaultOptions = defaultOptions;
// Interpret and default an options object

function getOptions(opts) {
  var options = {};
  for (var opt in defaultOptions) {
    options[opt] = opts && _util.has(opts, opt) ? opts[opt] : defaultOptions[opt];
  }if (_util.isArray(options.onToken)) {
    (function () {
      var tokens = options.onToken;
      options.onToken = function (token) {
        return tokens.push(token);
      };
    })();
  }
  if (_util.isArray(options.onComment)) options.onComment = pushComment(options, options.onComment);

  return options;
}

function pushComment(options, array) {
  return function (block, text, start, end, startLoc, endLoc) {
    var comment = {
      type: block ? "Block" : "Line",
      value: text,
      start: start,
      end: end
    };
    if (options.locations) comment.loc = new _locutil.SourceLocation(this, startLoc, endLoc);
    if (options.ranges) comment.range = [start, end];
    array.push(comment);
  };
}

},{"./locutil":5,"./util":15}],9:[function(_dereq_,module,exports){
"use strict";

var _tokentype = _dereq_("./tokentype");

var _state = _dereq_("./state");

var _whitespace = _dereq_("./whitespace");

var pp = _state.Parser.prototype;

// ## Parser utilities

// Test whether a statement node is the string literal `"use strict"`.

pp.isUseStrict = function (stmt) {
  return this.options.ecmaVersion >= 5 && stmt.type === "ExpressionStatement" && stmt.expression.type === "Literal" && stmt.expression.raw.slice(1, -1) === "use strict";
};

// Predicate that tests whether the next token is of the given
// type, and if yes, consumes it as a side effect.

pp.eat = function (type) {
  if (this.type === type) {
    this.next();
    return true;
  } else {
    return false;
  }
};

// Tests whether parsed token is a contextual keyword.

pp.isContextual = function (name) {
  return this.type === _tokentype.types.name && this.value === name;
};

// Consumes contextual keyword if possible.

pp.eatContextual = function (name) {
  return this.value === name && this.eat(_tokentype.types.name);
};

// Asserts that following token is given contextual keyword.

pp.expectContextual = function (name) {
  if (!this.eatContextual(name)) this.unexpected();
};

// Test whether a semicolon can be inserted at the current position.

pp.canInsertSemicolon = function () {
  return this.type === _tokentype.types.eof || this.type === _tokentype.types.braceR || _whitespace.lineBreak.test(this.input.slice(this.lastTokEnd, this.start));
};

pp.insertSemicolon = function () {
  if (this.canInsertSemicolon()) {
    if (this.options.onInsertedSemicolon) this.options.onInsertedSemicolon(this.lastTokEnd, this.lastTokEndLoc);
    return true;
  }
};

// Consume a semicolon, or, failing that, see if we are allowed to
// pretend that there is a semicolon at this position.

pp.semicolon = function () {
  if (!this.eat(_tokentype.types.semi) && !this.insertSemicolon()) this.unexpected();
};

pp.afterTrailingComma = function (tokType) {
  if (this.type == tokType) {
    if (this.options.onTrailingComma) this.options.onTrailingComma(this.lastTokStart, this.lastTokStartLoc);
    this.next();
    return true;
  }
};

// Expect a token of a given type. If found, consume it, otherwise,
// raise an unexpected token error.

pp.expect = function (type) {
  this.eat(type) || this.unexpected();
};

// Raise an unexpected token error.

pp.unexpected = function (pos) {
  this.raise(pos != null ? pos : this.start, "Unexpected token");
};

},{"./state":10,"./tokentype":14,"./whitespace":16}],10:[function(_dereq_,module,exports){
"use strict";

exports.__esModule = true;

function _classCallCheck(instance, Constructor) { if (!(instance instanceof Constructor)) { throw new TypeError("Cannot call a class as a function"); } }

var _identifier = _dereq_("./identifier");

var _tokentype = _dereq_("./tokentype");

var _whitespace = _dereq_("./whitespace");

var _options = _dereq_("./options");

// Registered plugins
var plugins = {};

exports.plugins = plugins;

var Parser = (function () {
  function Parser(options, input, startPos) {
    _classCallCheck(this, Parser);

    this.options = _options.getOptions(options);
    this.sourceFile = this.options.sourceFile;
    this.isKeyword = _identifier.keywords[this.options.ecmaVersion >= 6 ? 6 : 5];
    this.isReservedWord = _identifier.reservedWords[this.options.ecmaVersion];
    this.input = String(input);

    // Used to signal to callers of `readWord1` whether the word
    // contained any escape sequences. This is needed because words with
    // escape sequences must not be interpreted as keywords.
    this.containsEsc = false;

    // Load plugins
    this.loadPlugins(this.options.plugins);

    // Set up token state

    // The current position of the tokenizer in the input.
    if (startPos) {
      this.pos = startPos;
      this.lineStart = Math.max(0, this.input.lastIndexOf("\n", startPos));
      this.curLine = this.input.slice(0, this.lineStart).split(_whitespace.lineBreak).length;
    } else {
      this.pos = this.lineStart = 0;
      this.curLine = 1;
    }

    // Properties of the current token:
    // Its type
    this.type = _tokentype.types.eof;
    // For tokens that include more information than their type, the value
    this.value = null;
    // Its start and end offset
    this.start = this.end = this.pos;
    // And, if locations are used, the {line, column} object
    // corresponding to those offsets
    this.startLoc = this.endLoc = this.curPosition();

    // Position information for the previous token
    this.lastTokEndLoc = this.lastTokStartLoc = null;
    this.lastTokStart = this.lastTokEnd = this.pos;

    // The context stack is used to superficially track syntactic
    // context to predict whether a regular expression is allowed in a
    // given position.
    this.context = this.initialContext();
    this.exprAllowed = true;

    // Figure out if it's a module code.
    this.strict = this.inModule = this.options.sourceType === "module";

    // Used to signify the start of a potential arrow function
    this.potentialArrowAt = -1;

    // Flags to track whether we are in a function, a generator.
    this.inFunction = this.inGenerator = false;
    // Labels in scope.
    this.labels = [];

    // If enabled, skip leading hashbang line.
    if (this.pos === 0 && this.options.allowHashBang && this.input.slice(0, 2) === "#!") this.skipLineComment(2);
  }

  Parser.prototype.extend = function extend(name, f) {
    this[name] = f(this[name]);
  };

  Parser.prototype.loadPlugins = function loadPlugins(pluginConfigs) {
    for (var _name in pluginConfigs) {
      var plugin = plugins[_name];
      if (!plugin) throw new Error("Plugin '" + _name + "' not found");
      plugin(this, pluginConfigs[_name]);
    }
  };

  Parser.prototype.parse = function parse() {
    var node = this.options.program || this.startNode();
    this.nextToken();
    return this.parseTopLevel(node);
  };

  return Parser;
})();

exports.Parser = Parser;

},{"./identifier":2,"./options":8,"./tokentype":14,"./whitespace":16}],11:[function(_dereq_,module,exports){
"use strict";

var _tokentype = _dereq_("./tokentype");

var _state = _dereq_("./state");

var _whitespace = _dereq_("./whitespace");

var pp = _state.Parser.prototype;

// ### Statement parsing

// Parse a program. Initializes the parser, reads any number of
// statements, and wraps them in a Program node.  Optionally takes a
// `program` argument.  If present, the statements will be appended
// to its body instead of creating a new node.

pp.parseTopLevel = function (node) {
  var first = true;
  if (!node.body) node.body = [];
  while (this.type !== _tokentype.types.eof) {
    var stmt = this.parseStatement(true, true);
    node.body.push(stmt);
    if (first) {
      if (this.isUseStrict(stmt)) this.setStrict(true);
      first = false;
    }
  }
  this.next();
  if (this.options.ecmaVersion >= 6) {
    node.sourceType = this.options.sourceType;
  }
  return this.finishNode(node, "Program");
};

var loopLabel = { kind: "loop" },
    switchLabel = { kind: "switch" };

// Parse a single statement.
//
// If expecting a statement and finding a slash operator, parse a
// regular expression literal. This is to handle cases like
// `if (foo) /blah/.exec(foo)`, where looking at the previous token
// does not help.

pp.parseStatement = function (declaration, topLevel) {
  var starttype = this.type,
      node = this.startNode();

  // Most types of statements are recognized by the keyword they
  // start with. Many are trivial to parse, some require a bit of
  // complexity.

  switch (starttype) {
    case _tokentype.types._break:case _tokentype.types._continue:
      return this.parseBreakContinueStatement(node, starttype.keyword);
    case _tokentype.types._debugger:
      return this.parseDebuggerStatement(node);
    case _tokentype.types._do:
      return this.parseDoStatement(node);
    case _tokentype.types._for:
      return this.parseForStatement(node);
    case _tokentype.types._function:
      if (!declaration && this.options.ecmaVersion >= 6) this.unexpected();
      return this.parseFunctionStatement(node);
    case _tokentype.types._class:
      if (!declaration) this.unexpected();
      return this.parseClass(node, true);
    case _tokentype.types._if:
      return this.parseIfStatement(node);
    case _tokentype.types._return:
      return this.parseReturnStatement(node);
    case _tokentype.types._switch:
      return this.parseSwitchStatement(node);
    case _tokentype.types._throw:
      return this.parseThrowStatement(node);
    case _tokentype.types._try:
      return this.parseTryStatement(node);
    case _tokentype.types._let:case _tokentype.types._const:
      if (!declaration) this.unexpected(); // NOTE: falls through to _var
    case _tokentype.types._var:
      return this.parseVarStatement(node, starttype);
    case _tokentype.types._while:
      return this.parseWhileStatement(node);
    case _tokentype.types._with:
      return this.parseWithStatement(node);
    case _tokentype.types.braceL:
      return this.parseBlock();
    case _tokentype.types.semi:
      return this.parseEmptyStatement(node);
    case _tokentype.types._export:
    case _tokentype.types._import:
      if (!this.options.allowImportExportEverywhere) {
        if (!topLevel) this.raise(this.start, "'import' and 'export' may only appear at the top level");
        if (!this.inModule) this.raise(this.start, "'import' and 'export' may appear only with 'sourceType: module'");
      }
      return starttype === _tokentype.types._import ? this.parseImport(node) : this.parseExport(node);

    // If the statement does not start with a statement keyword or a
    // brace, it's an ExpressionStatement or LabeledStatement. We
    // simply start parsing an expression, and afterwards, if the
    // next token is a colon and the expression was a simple
    // Identifier node, we switch to interpreting it as a label.
    default:
      var maybeName = this.value,
          expr = this.parseExpression();
      if (starttype === _tokentype.types.name && expr.type === "Identifier" && this.eat(_tokentype.types.colon)) return this.parseLabeledStatement(node, maybeName, expr);else return this.parseExpressionStatement(node, expr);
  }
};

pp.parseBreakContinueStatement = function (node, keyword) {
  var isBreak = keyword == "break";
  this.next();
  if (this.eat(_tokentype.types.semi) || this.insertSemicolon()) node.label = null;else if (this.type !== _tokentype.types.name) this.unexpected();else {
    node.label = this.parseIdent();
    this.semicolon();
  }

  // Verify that there is an actual destination to break or
  // continue to.
  for (var i = 0; i < this.labels.length; ++i) {
    var lab = this.labels[i];
    if (node.label == null || lab.name === node.label.name) {
      if (lab.kind != null && (isBreak || lab.kind === "loop")) break;
      if (node.label && isBreak) break;
    }
  }
  if (i === this.labels.length) this.raise(node.start, "Unsyntactic " + keyword);
  return this.finishNode(node, isBreak ? "BreakStatement" : "ContinueStatement");
};

pp.parseDebuggerStatement = function (node) {
  this.next();
  this.semicolon();
  return this.finishNode(node, "DebuggerStatement");
};

pp.parseDoStatement = function (node) {
  this.next();
  this.labels.push(loopLabel);
  node.body = this.parseStatement(false);
  this.labels.pop();
  this.expect(_tokentype.types._while);
  node.test = this.parseParenExpression();
  if (this.options.ecmaVersion >= 6) this.eat(_tokentype.types.semi);else this.semicolon();
  return this.finishNode(node, "DoWhileStatement");
};

// Disambiguating between a `for` and a `for`/`in` or `for`/`of`
// loop is non-trivial. Basically, we have to parse the init `var`
// statement or expression, disallowing the `in` operator (see
// the second parameter to `parseExpression`), and then check
// whether the next token is `in` or `of`. When there is no init
// part (semicolon immediately after the opening parenthesis), it
// is a regular `for` loop.

pp.parseForStatement = function (node) {
  this.next();
  this.labels.push(loopLabel);
  this.expect(_tokentype.types.parenL);
  if (this.type === _tokentype.types.semi) return this.parseFor(node, null);
  if (this.type === _tokentype.types._var || this.type === _tokentype.types._let || this.type === _tokentype.types._const) {
    var _init = this.startNode(),
        varKind = this.type;
    this.next();
    this.parseVar(_init, true, varKind);
    this.finishNode(_init, "VariableDeclaration");
    if ((this.type === _tokentype.types._in || this.options.ecmaVersion >= 6 && this.isContextual("of")) && _init.declarations.length === 1 && !(varKind !== _tokentype.types._var && _init.declarations[0].init)) return this.parseForIn(node, _init);
    return this.parseFor(node, _init);
  }
  var refShorthandDefaultPos = { start: 0 };
  var init = this.parseExpression(true, refShorthandDefaultPos);
  if (this.type === _tokentype.types._in || this.options.ecmaVersion >= 6 && this.isContextual("of")) {
    this.toAssignable(init);
    this.checkLVal(init);
    return this.parseForIn(node, init);
  } else if (refShorthandDefaultPos.start) {
    this.unexpected(refShorthandDefaultPos.start);
  }
  return this.parseFor(node, init);
};

pp.parseFunctionStatement = function (node) {
  this.next();
  return this.parseFunction(node, true);
};

pp.parseIfStatement = function (node) {
  this.next();
  node.test = this.parseParenExpression();
  node.consequent = this.parseStatement(false);
  node.alternate = this.eat(_tokentype.types._else) ? this.parseStatement(false) : null;
  return this.finishNode(node, "IfStatement");
};

pp.parseReturnStatement = function (node) {
  if (!this.inFunction && !this.options.allowReturnOutsideFunction) this.raise(this.start, "'return' outside of function");
  this.next();

  // In `return` (and `break`/`continue`), the keywords with
  // optional arguments, we eagerly look for a semicolon or the
  // possibility to insert one.

  if (this.eat(_tokentype.types.semi) || this.insertSemicolon()) node.argument = null;else {
    node.argument = this.parseExpression();this.semicolon();
  }
  return this.finishNode(node, "ReturnStatement");
};

pp.parseSwitchStatement = function (node) {
  this.next();
  node.discriminant = this.parseParenExpression();
  node.cases = [];
  this.expect(_tokentype.types.braceL);
  this.labels.push(switchLabel);

  // Statements under must be grouped (by label) in SwitchCase
  // nodes. `cur` is used to keep the node that we are currently
  // adding statements to.

  for (var cur, sawDefault = false; this.type != _tokentype.types.braceR;) {
    if (this.type === _tokentype.types._case || this.type === _tokentype.types._default) {
      var isCase = this.type === _tokentype.types._case;
      if (cur) this.finishNode(cur, "SwitchCase");
      node.cases.push(cur = this.startNode());
      cur.consequent = [];
      this.next();
      if (isCase) {
        cur.test = this.parseExpression();
      } else {
        if (sawDefault) this.raise(this.lastTokStart, "Multiple default clauses");
        sawDefault = true;
        cur.test = null;
      }
      this.expect(_tokentype.types.colon);
    } else {
      if (!cur) this.unexpected();
      cur.consequent.push(this.parseStatement(true));
    }
  }
  if (cur) this.finishNode(cur, "SwitchCase");
  this.next(); // Closing brace
  this.labels.pop();
  return this.finishNode(node, "SwitchStatement");
};

pp.parseThrowStatement = function (node) {
  this.next();
  if (_whitespace.lineBreak.test(this.input.slice(this.lastTokEnd, this.start))) this.raise(this.lastTokEnd, "Illegal newline after throw");
  node.argument = this.parseExpression();
  this.semicolon();
  return this.finishNode(node, "ThrowStatement");
};

// Reused empty array added for node fields that are always empty.

var empty = [];

pp.parseTryStatement = function (node) {
  this.next();
  node.block = this.parseBlock();
  node.handler = null;
  if (this.type === _tokentype.types._catch) {
    var clause = this.startNode();
    this.next();
    this.expect(_tokentype.types.parenL);
    clause.param = this.parseBindingAtom();
    this.checkLVal(clause.param, true);
    this.expect(_tokentype.types.parenR);
    clause.guard = null;
    clause.body = this.parseBlock();
    node.handler = this.finishNode(clause, "CatchClause");
  }
  node.guardedHandlers = empty;
  node.finalizer = this.eat(_tokentype.types._finally) ? this.parseBlock() : null;
  if (!node.handler && !node.finalizer) this.raise(node.start, "Missing catch or finally clause");
  return this.finishNode(node, "TryStatement");
};

pp.parseVarStatement = function (node, kind) {
  this.next();
  this.parseVar(node, false, kind);
  this.semicolon();
  return this.finishNode(node, "VariableDeclaration");
};

pp.parseWhileStatement = function (node) {
  this.next();
  node.test = this.parseParenExpression();
  this.labels.push(loopLabel);
  node.body = this.parseStatement(false);
  this.labels.pop();
  return this.finishNode(node, "WhileStatement");
};

pp.parseWithStatement = function (node) {
  if (this.strict) this.raise(this.start, "'with' in strict mode");
  this.next();
  node.object = this.parseParenExpression();
  node.body = this.parseStatement(false);
  return this.finishNode(node, "WithStatement");
};

pp.parseEmptyStatement = function (node) {
  this.next();
  return this.finishNode(node, "EmptyStatement");
};

pp.parseLabeledStatement = function (node, maybeName, expr) {
  for (var i = 0; i < this.labels.length; ++i) {
    if (this.labels[i].name === maybeName) this.raise(expr.start, "Label '" + maybeName + "' is already declared");
  }var kind = this.type.isLoop ? "loop" : this.type === _tokentype.types._switch ? "switch" : null;
  for (var i = this.labels.length - 1; i >= 0; i--) {
    var label = this.labels[i];
    if (label.statementStart == node.start) {
      label.statementStart = this.start;
      label.kind = kind;
    } else break;
  }
  this.labels.push({ name: maybeName, kind: kind, statementStart: this.start });
  node.body = this.parseStatement(true);
  this.labels.pop();
  node.label = expr;
  return this.finishNode(node, "LabeledStatement");
};

pp.parseExpressionStatement = function (node, expr) {
  node.expression = expr;
  this.semicolon();
  return this.finishNode(node, "ExpressionStatement");
};

// Parse a semicolon-enclosed block of statements, handling `"use
// strict"` declarations when `allowStrict` is true (used for
// function bodies).

pp.parseBlock = function (allowStrict) {
  var node = this.startNode(),
      first = true,
      oldStrict = undefined;
  node.body = [];
  this.expect(_tokentype.types.braceL);
  while (!this.eat(_tokentype.types.braceR)) {
    var stmt = this.parseStatement(true);
    node.body.push(stmt);
    if (first && allowStrict && this.isUseStrict(stmt)) {
      oldStrict = this.strict;
      this.setStrict(this.strict = true);
    }
    first = false;
  }
  if (oldStrict === false) this.setStrict(false);
  return this.finishNode(node, "BlockStatement");
};

// Parse a regular `for` loop. The disambiguation code in
// `parseStatement` will already have parsed the init statement or
// expression.

pp.parseFor = function (node, init) {
  node.init = init;
  this.expect(_tokentype.types.semi);
  node.test = this.type === _tokentype.types.semi ? null : this.parseExpression();
  this.expect(_tokentype.types.semi);
  node.update = this.type === _tokentype.types.parenR ? null : this.parseExpression();
  this.expect(_tokentype.types.parenR);
  node.body = this.parseStatement(false);
  this.labels.pop();
  return this.finishNode(node, "ForStatement");
};

// Parse a `for`/`in` and `for`/`of` loop, which are almost
// same from parser's perspective.

pp.parseForIn = function (node, init) {
  var type = this.type === _tokentype.types._in ? "ForInStatement" : "ForOfStatement";
  this.next();
  node.left = init;
  node.right = this.parseExpression();
  this.expect(_tokentype.types.parenR);
  node.body = this.parseStatement(false);
  this.labels.pop();
  return this.finishNode(node, type);
};

// Parse a list of variable declarations.

pp.parseVar = function (node, isFor, kind) {
  node.declarations = [];
  node.kind = kind.keyword;
  for (;;) {
    var decl = this.startNode();
    this.parseVarId(decl);
    if (this.eat(_tokentype.types.eq)) {
      decl.init = this.parseMaybeAssign(isFor);
    } else if (kind === _tokentype.types._const && !(this.type === _tokentype.types._in || this.options.ecmaVersion >= 6 && this.isContextual("of"))) {
      this.unexpected();
    } else if (decl.id.type != "Identifier" && !(isFor && (this.type === _tokentype.types._in || this.isContextual("of")))) {
      this.raise(this.lastTokEnd, "Complex binding patterns require an initialization value");
    } else {
      decl.init = null;
    }
    node.declarations.push(this.finishNode(decl, "VariableDeclarator"));
    if (!this.eat(_tokentype.types.comma)) break;
  }
  return node;
};

pp.parseVarId = function (decl) {
  decl.id = this.parseBindingAtom();
  this.checkLVal(decl.id, true);
};

// Parse a function declaration or literal (depending on the
// `isStatement` parameter).

pp.parseFunction = function (node, isStatement, allowExpressionBody) {
  this.initFunction(node);
  if (this.options.ecmaVersion >= 6) node.generator = this.eat(_tokentype.types.star);
  if (isStatement || this.type === _tokentype.types.name) node.id = this.parseIdent();
  this.parseFunctionParams(node);
  this.parseFunctionBody(node, allowExpressionBody);
  return this.finishNode(node, isStatement ? "FunctionDeclaration" : "FunctionExpression");
};

pp.parseFunctionParams = function (node) {
  this.expect(_tokentype.types.parenL);
  node.params = this.parseBindingList(_tokentype.types.parenR, false, false);
};

// Parse a class declaration or literal (depending on the
// `isStatement` parameter).

pp.parseClass = function (node, isStatement) {
  this.next();
  this.parseClassId(node, isStatement);
  this.parseClassSuper(node);
  var classBody = this.startNode();
  var hadConstructor = false;
  classBody.body = [];
  this.expect(_tokentype.types.braceL);
  while (!this.eat(_tokentype.types.braceR)) {
    if (this.eat(_tokentype.types.semi)) continue;
    var method = this.startNode();
    var isGenerator = this.eat(_tokentype.types.star);
    var isMaybeStatic = this.type === _tokentype.types.name && this.value === "static";
    this.parsePropertyName(method);
    method["static"] = isMaybeStatic && this.type !== _tokentype.types.parenL;
    if (method["static"]) {
      if (isGenerator) this.unexpected();
      isGenerator = this.eat(_tokentype.types.star);
      this.parsePropertyName(method);
    }
    method.kind = "method";
    var isGetSet = false;
    if (!method.computed) {
      var key = method.key;

      if (!isGenerator && key.type === "Identifier" && this.type !== _tokentype.types.parenL && (key.name === "get" || key.name === "set")) {
        isGetSet = true;
        method.kind = key.name;
        key = this.parsePropertyName(method);
      }
      if (!method["static"] && (key.type === "Identifier" && key.name === "constructor" || key.type === "Literal" && key.value === "constructor")) {
        if (hadConstructor) this.raise(key.start, "Duplicate constructor in the same class");
        if (isGetSet) this.raise(key.start, "Constructor can't have get/set modifier");
        if (isGenerator) this.raise(key.start, "Constructor can't be a generator");
        method.kind = "constructor";
        hadConstructor = true;
      }
    }
    this.parseClassMethod(classBody, method, isGenerator);
    if (isGetSet) {
      var paramCount = method.kind === "get" ? 0 : 1;
      if (method.value.params.length !== paramCount) {
        var start = method.value.start;
        if (method.kind === "get") this.raise(start, "getter should have no params");else this.raise(start, "setter should have exactly one param");
      }
    }
  }
  node.body = this.finishNode(classBody, "ClassBody");
  return this.finishNode(node, isStatement ? "ClassDeclaration" : "ClassExpression");
};

pp.parseClassMethod = function (classBody, method, isGenerator) {
  method.value = this.parseMethod(isGenerator);
  classBody.body.push(this.finishNode(method, "MethodDefinition"));
};

pp.parseClassId = function (node, isStatement) {
  node.id = this.type === _tokentype.types.name ? this.parseIdent() : isStatement ? this.unexpected() : null;
};

pp.parseClassSuper = function (node) {
  node.superClass = this.eat(_tokentype.types._extends) ? this.parseExprSubscripts() : null;
};

// Parses module export declaration.

pp.parseExport = function (node) {
  this.next();
  // export * from '...'
  if (this.eat(_tokentype.types.star)) {
    this.expectContextual("from");
    node.source = this.type === _tokentype.types.string ? this.parseExprAtom() : this.unexpected();
    this.semicolon();
    return this.finishNode(node, "ExportAllDeclaration");
  }
  if (this.eat(_tokentype.types._default)) {
    // export default ...
    var expr = this.parseMaybeAssign();
    var needsSemi = true;
    if (expr.type == "FunctionExpression" || expr.type == "ClassExpression") {
      needsSemi = false;
      if (expr.id) {
        expr.type = expr.type == "FunctionExpression" ? "FunctionDeclaration" : "ClassDeclaration";
      }
    }
    node.declaration = expr;
    if (needsSemi) this.semicolon();
    return this.finishNode(node, "ExportDefaultDeclaration");
  }
  // export var|const|let|function|class ...
  if (this.shouldParseExportStatement()) {
    node.declaration = this.parseStatement(true);
    node.specifiers = [];
    node.source = null;
  } else {
    // export { x, y as z } [from '...']
    node.declaration = null;
    node.specifiers = this.parseExportSpecifiers();
    if (this.eatContextual("from")) {
      node.source = this.type === _tokentype.types.string ? this.parseExprAtom() : this.unexpected();
    } else {
      node.source = null;
    }
    this.semicolon();
  }
  return this.finishNode(node, "ExportNamedDeclaration");
};

pp.shouldParseExportStatement = function () {
  return this.type.keyword;
};

// Parses a comma-separated list of module exports.

pp.parseExportSpecifiers = function () {
  var nodes = [],
      first = true;
  // export { x, y as z } [from '...']
  this.expect(_tokentype.types.braceL);
  while (!this.eat(_tokentype.types.braceR)) {
    if (!first) {
      this.expect(_tokentype.types.comma);
      if (this.afterTrailingComma(_tokentype.types.braceR)) break;
    } else first = false;

    var node = this.startNode();
    node.local = this.parseIdent(this.type === _tokentype.types._default);
    node.exported = this.eatContextual("as") ? this.parseIdent(true) : node.local;
    nodes.push(this.finishNode(node, "ExportSpecifier"));
  }
  return nodes;
};

// Parses import declaration.

pp.parseImport = function (node) {
  this.next();
  // import '...'
  if (this.type === _tokentype.types.string) {
    node.specifiers = empty;
    node.source = this.parseExprAtom();
  } else {
    node.specifiers = this.parseImportSpecifiers();
    this.expectContextual("from");
    node.source = this.type === _tokentype.types.string ? this.parseExprAtom() : this.unexpected();
  }
  this.semicolon();
  return this.finishNode(node, "ImportDeclaration");
};

// Parses a comma-separated list of module imports.

pp.parseImportSpecifiers = function () {
  var nodes = [],
      first = true;
  if (this.type === _tokentype.types.name) {
    // import defaultObj, { x, y as z } from '...'
    var node = this.startNode();
    node.local = this.parseIdent();
    this.checkLVal(node.local, true);
    nodes.push(this.finishNode(node, "ImportDefaultSpecifier"));
    if (!this.eat(_tokentype.types.comma)) return nodes;
  }
  if (this.type === _tokentype.types.star) {
    var node = this.startNode();
    this.next();
    this.expectContextual("as");
    node.local = this.parseIdent();
    this.checkLVal(node.local, true);
    nodes.push(this.finishNode(node, "ImportNamespaceSpecifier"));
    return nodes;
  }
  this.expect(_tokentype.types.braceL);
  while (!this.eat(_tokentype.types.braceR)) {
    if (!first) {
      this.expect(_tokentype.types.comma);
      if (this.afterTrailingComma(_tokentype.types.braceR)) break;
    } else first = false;

    var node = this.startNode();
    node.imported = this.parseIdent(true);
    node.local = this.eatContextual("as") ? this.parseIdent() : node.imported;
    this.checkLVal(node.local, true);
    nodes.push(this.finishNode(node, "ImportSpecifier"));
  }
  return nodes;
};

},{"./state":10,"./tokentype":14,"./whitespace":16}],12:[function(_dereq_,module,exports){
// The algorithm used to determine whether a regexp can appear at a
// given point in the program is loosely based on sweet.js' approach.
// See https://github.com/mozilla/sweet.js/wiki/design

"use strict";

exports.__esModule = true;

function _classCallCheck(instance, Constructor) { if (!(instance instanceof Constructor)) { throw new TypeError("Cannot call a class as a function"); } }

var _state = _dereq_("./state");

var _tokentype = _dereq_("./tokentype");

var _whitespace = _dereq_("./whitespace");

var TokContext = function TokContext(token, isExpr, preserveSpace, override) {
  _classCallCheck(this, TokContext);

  this.token = token;
  this.isExpr = !!isExpr;
  this.preserveSpace = !!preserveSpace;
  this.override = override;
};

exports.TokContext = TokContext;
var types = {
  b_stat: new TokContext("{", false),
  b_expr: new TokContext("{", true),
  b_tmpl: new TokContext("${", true),
  p_stat: new TokContext("(", false),
  p_expr: new TokContext("(", true),
  q_tmpl: new TokContext("`", true, true, function (p) {
    return p.readTmplToken();
  }),
  f_expr: new TokContext("function", true)
};

exports.types = types;
var pp = _state.Parser.prototype;

pp.initialContext = function () {
  return [types.b_stat];
};

pp.braceIsBlock = function (prevType) {
  if (prevType === _tokentype.types.colon) {
    var _parent = this.curContext();
    if (_parent === types.b_stat || _parent === types.b_expr) return !_parent.isExpr;
  }
  if (prevType === _tokentype.types._return) return _whitespace.lineBreak.test(this.input.slice(this.lastTokEnd, this.start));
  if (prevType === _tokentype.types._else || prevType === _tokentype.types.semi || prevType === _tokentype.types.eof || prevType === _tokentype.types.parenR) return true;
  if (prevType == _tokentype.types.braceL) return this.curContext() === types.b_stat;
  return !this.exprAllowed;
};

pp.updateContext = function (prevType) {
  var update = undefined,
      type = this.type;
  if (type.keyword && prevType == _tokentype.types.dot) this.exprAllowed = false;else if (update = type.updateContext) update.call(this, prevType);else this.exprAllowed = type.beforeExpr;
};

// Token-specific context update code

_tokentype.types.parenR.updateContext = _tokentype.types.braceR.updateContext = function () {
  if (this.context.length == 1) {
    this.exprAllowed = true;
    return;
  }
  var out = this.context.pop();
  if (out === types.b_stat && this.curContext() === types.f_expr) {
    this.context.pop();
    this.exprAllowed = false;
  } else if (out === types.b_tmpl) {
    this.exprAllowed = true;
  } else {
    this.exprAllowed = !out.isExpr;
  }
};

_tokentype.types.braceL.updateContext = function (prevType) {
  this.context.push(this.braceIsBlock(prevType) ? types.b_stat : types.b_expr);
  this.exprAllowed = true;
};

_tokentype.types.dollarBraceL.updateContext = function () {
  this.context.push(types.b_tmpl);
  this.exprAllowed = true;
};

_tokentype.types.parenL.updateContext = function (prevType) {
  var statementParens = prevType === _tokentype.types._if || prevType === _tokentype.types._for || prevType === _tokentype.types._with || prevType === _tokentype.types._while;
  this.context.push(statementParens ? types.p_stat : types.p_expr);
  this.exprAllowed = true;
};

_tokentype.types.incDec.updateContext = function () {};

_tokentype.types._function.updateContext = function () {
  if (this.curContext() !== types.b_stat) this.context.push(types.f_expr);
  this.exprAllowed = false;
};

_tokentype.types.backQuote.updateContext = function () {
  if (this.curContext() === types.q_tmpl) this.context.pop();else this.context.push(types.q_tmpl);
  this.exprAllowed = false;
};

// tokExprAllowed stays unchanged

},{"./state":10,"./tokentype":14,"./whitespace":16}],13:[function(_dereq_,module,exports){
"use strict";

exports.__esModule = true;

function _classCallCheck(instance, Constructor) { if (!(instance instanceof Constructor)) { throw new TypeError("Cannot call a class as a function"); } }

var _identifier = _dereq_("./identifier");

var _tokentype = _dereq_("./tokentype");

var _state = _dereq_("./state");

var _locutil = _dereq_("./locutil");

var _whitespace = _dereq_("./whitespace");

// Object type used to represent tokens. Note that normally, tokens
// simply exist as properties on the parser object. This is only
// used for the onToken callback and the external tokenizer.

var Token = function Token(p) {
  _classCallCheck(this, Token);

  this.type = p.type;
  this.value = p.value;
  this.start = p.start;
  this.end = p.end;
  if (p.options.locations) this.loc = new _locutil.SourceLocation(p, p.startLoc, p.endLoc);
  if (p.options.ranges) this.range = [p.start, p.end];
};

exports.Token = Token;

// ## Tokenizer

var pp = _state.Parser.prototype;

// Are we running under Rhino?
var isRhino = typeof Packages == "object" && Object.prototype.toString.call(Packages) == "[object JavaPackage]";

// Move to the next token

pp.next = function () {
  if (this.options.onToken) this.options.onToken(new Token(this));

  this.lastTokEnd = this.end;
  this.lastTokStart = this.start;
  this.lastTokEndLoc = this.endLoc;
  this.lastTokStartLoc = this.startLoc;
  this.nextToken();
};

pp.getToken = function () {
  this.next();
  return new Token(this);
};

// If we're in an ES6 environment, make parsers iterable
if (typeof Symbol !== "undefined") pp[Symbol.iterator] = function () {
  var self = this;
  return { next: function next() {
      var token = self.getToken();
      return {
        done: token.type === _tokentype.types.eof,
        value: token
      };
    } };
};

// Toggle strict mode. Re-reads the next number or string to please
// pedantic tests (`"use strict"; 010;` should fail).

pp.setStrict = function (strict) {
  this.strict = strict;
  if (this.type !== _tokentype.types.num && this.type !== _tokentype.types.string) return;
  this.pos = this.start;
  if (this.options.locations) {
    while (this.pos < this.lineStart) {
      this.lineStart = this.input.lastIndexOf("\n", this.lineStart - 2) + 1;
      --this.curLine;
    }
  }
  this.nextToken();
};

pp.curContext = function () {
  return this.context[this.context.length - 1];
};

// Read a single token, updating the parser object's token-related
// properties.

pp.nextToken = function () {
  var curContext = this.curContext();
  if (!curContext || !curContext.preserveSpace) this.skipSpace();

  this.start = this.pos;
  if (this.options.locations) this.startLoc = this.curPosition();
  if (this.pos >= this.input.length) return this.finishToken(_tokentype.types.eof);

  if (curContext.override) return curContext.override(this);else this.readToken(this.fullCharCodeAtPos());
};

pp.readToken = function (code) {
  // Identifier or keyword. '\uXXXX' sequences are allowed in
  // identifiers, so '\' also dispatches to that.
  if (_identifier.isIdentifierStart(code, this.options.ecmaVersion >= 6) || code === 92 /* '\' */) return this.readWord();

  return this.getTokenFromCode(code);
};

pp.fullCharCodeAtPos = function () {
  var code = this.input.charCodeAt(this.pos);
  if (code <= 0xd7ff || code >= 0xe000) return code;
  var next = this.input.charCodeAt(this.pos + 1);
  return (code << 10) + next - 0x35fdc00;
};

pp.skipBlockComment = function () {
  var startLoc = this.options.onComment && this.curPosition();
  var start = this.pos,
      end = this.input.indexOf("*/", this.pos += 2);
  if (end === -1) this.raise(this.pos - 2, "Unterminated comment");
  this.pos = end + 2;
  if (this.options.locations) {
    _whitespace.lineBreakG.lastIndex = start;
    var match = undefined;
    while ((match = _whitespace.lineBreakG.exec(this.input)) && match.index < this.pos) {
      ++this.curLine;
      this.lineStart = match.index + match[0].length;
    }
  }
  if (this.options.onComment) this.options.onComment(true, this.input.slice(start + 2, end), start, this.pos, startLoc, this.curPosition());
};

pp.skipLineComment = function (startSkip) {
  var start = this.pos;
  var startLoc = this.options.onComment && this.curPosition();
  var ch = this.input.charCodeAt(this.pos += startSkip);
  while (this.pos < this.input.length && ch !== 10 && ch !== 13 && ch !== 8232 && ch !== 8233) {
    ++this.pos;
    ch = this.input.charCodeAt(this.pos);
  }
  if (this.options.onComment) this.options.onComment(false, this.input.slice(start + startSkip, this.pos), start, this.pos, startLoc, this.curPosition());
};

// Called at the start of the parse and after every token. Skips
// whitespace and comments, and.

pp.skipSpace = function () {
  loop: while (this.pos < this.input.length) {
    var ch = this.input.charCodeAt(this.pos);
    switch (ch) {
      case 32:case 160:
        // ' '
        ++this.pos;
        break;
      case 13:
        if (this.input.charCodeAt(this.pos + 1) === 10) {
          ++this.pos;
        }
      case 10:case 8232:case 8233:
        ++this.pos;
        if (this.options.locations) {
          ++this.curLine;
          this.lineStart = this.pos;
        }
        break;
      case 47:
        // '/'
        switch (this.input.charCodeAt(this.pos + 1)) {
          case 42:
            // '*'
            this.skipBlockComment();
            break;
          case 47:
            this.skipLineComment(2);
            break;
          default:
            break loop;
        }
        break;
      default:
        if (ch > 8 && ch < 14 || ch >= 5760 && _whitespace.nonASCIIwhitespace.test(String.fromCharCode(ch))) {
          ++this.pos;
        } else {
          break loop;
        }
    }
  }
};

// Called at the end of every token. Sets `end`, `val`, and
// maintains `context` and `exprAllowed`, and skips the space after
// the token, so that the next one's `start` will point at the
// right position.

pp.finishToken = function (type, val) {
  this.end = this.pos;
  if (this.options.locations) this.endLoc = this.curPosition();
  var prevType = this.type;
  this.type = type;
  this.value = val;

  this.updateContext(prevType);
};

// ### Token reading

// This is the function that is called to fetch the next token. It
// is somewhat obscure, because it works in character codes rather
// than characters, and because operator parsing has been inlined
// into it.
//
// All in the name of speed.
//
pp.readToken_dot = function () {
  var next = this.input.charCodeAt(this.pos + 1);
  if (next >= 48 && next <= 57) return this.readNumber(true);
  var next2 = this.input.charCodeAt(this.pos + 2);
  if (this.options.ecmaVersion >= 6 && next === 46 && next2 === 46) {
    // 46 = dot '.'
    this.pos += 3;
    return this.finishToken(_tokentype.types.ellipsis);
  } else {
    ++this.pos;
    return this.finishToken(_tokentype.types.dot);
  }
};

pp.readToken_slash = function () {
  // '/'
  var next = this.input.charCodeAt(this.pos + 1);
  if (this.exprAllowed) {
    ++this.pos;return this.readRegexp();
  }
  if (next === 61) return this.finishOp(_tokentype.types.assign, 2);
  return this.finishOp(_tokentype.types.slash, 1);
};

pp.readToken_mult_modulo = function (code) {
  // '%*'
  var next = this.input.charCodeAt(this.pos + 1);
  if (next === 61) return this.finishOp(_tokentype.types.assign, 2);
  return this.finishOp(code === 42 ? _tokentype.types.star : _tokentype.types.modulo, 1);
};

pp.readToken_pipe_amp = function (code) {
  // '|&'
  var next = this.input.charCodeAt(this.pos + 1);
  if (next === code) return this.finishOp(code === 124 ? _tokentype.types.logicalOR : _tokentype.types.logicalAND, 2);
  if (next === 61) return this.finishOp(_tokentype.types.assign, 2);
  return this.finishOp(code === 124 ? _tokentype.types.bitwiseOR : _tokentype.types.bitwiseAND, 1);
};

pp.readToken_caret = function () {
  // '^'
  var next = this.input.charCodeAt(this.pos + 1);
  if (next === 61) return this.finishOp(_tokentype.types.assign, 2);
  return this.finishOp(_tokentype.types.bitwiseXOR, 1);
};

pp.readToken_plus_min = function (code) {
  // '+-'
  var next = this.input.charCodeAt(this.pos + 1);
  if (next === code) {
    if (next == 45 && this.input.charCodeAt(this.pos + 2) == 62 && _whitespace.lineBreak.test(this.input.slice(this.lastTokEnd, this.pos))) {
      // A `-->` line comment
      this.skipLineComment(3);
      this.skipSpace();
      return this.nextToken();
    }
    return this.finishOp(_tokentype.types.incDec, 2);
  }
  if (next === 61) return this.finishOp(_tokentype.types.assign, 2);
  return this.finishOp(_tokentype.types.plusMin, 1);
};

pp.readToken_lt_gt = function (code) {
  // '<>'
  var next = this.input.charCodeAt(this.pos + 1);
  var size = 1;
  if (next === code) {
    size = code === 62 && this.input.charCodeAt(this.pos + 2) === 62 ? 3 : 2;
    if (this.input.charCodeAt(this.pos + size) === 61) return this.finishOp(_tokentype.types.assign, size + 1);
    return this.finishOp(_tokentype.types.bitShift, size);
  }
  if (next == 33 && code == 60 && this.input.charCodeAt(this.pos + 2) == 45 && this.input.charCodeAt(this.pos + 3) == 45) {
    if (this.inModule) this.unexpected();
    // `<!--`, an XML-style comment that should be interpreted as a line comment
    this.skipLineComment(4);
    this.skipSpace();
    return this.nextToken();
  }
  if (next === 61) size = this.input.charCodeAt(this.pos + 2) === 61 ? 3 : 2;
  return this.finishOp(_tokentype.types.relational, size);
};

pp.readToken_eq_excl = function (code) {
  // '=!'
  var next = this.input.charCodeAt(this.pos + 1);
  if (next === 61) return this.finishOp(_tokentype.types.equality, this.input.charCodeAt(this.pos + 2) === 61 ? 3 : 2);
  if (code === 61 && next === 62 && this.options.ecmaVersion >= 6) {
    // '=>'
    this.pos += 2;
    return this.finishToken(_tokentype.types.arrow);
  }
  return this.finishOp(code === 61 ? _tokentype.types.eq : _tokentype.types.prefix, 1);
};

pp.getTokenFromCode = function (code) {
  switch (code) {
    // The interpretation of a dot depends on whether it is followed
    // by a digit or another two dots.
    case 46:
      // '.'
      return this.readToken_dot();

    // Punctuation tokens.
    case 40:
      ++this.pos;return this.finishToken(_tokentype.types.parenL);
    case 41:
      ++this.pos;return this.finishToken(_tokentype.types.parenR);
    case 59:
      ++this.pos;return this.finishToken(_tokentype.types.semi);
    case 44:
      ++this.pos;return this.finishToken(_tokentype.types.comma);
    case 91:
      ++this.pos;return this.finishToken(_tokentype.types.bracketL);
    case 93:
      ++this.pos;return this.finishToken(_tokentype.types.bracketR);
    case 123:
      ++this.pos;return this.finishToken(_tokentype.types.braceL);
    case 125:
      ++this.pos;return this.finishToken(_tokentype.types.braceR);
    case 58:
      ++this.pos;return this.finishToken(_tokentype.types.colon);
    case 63:
      ++this.pos;return this.finishToken(_tokentype.types.question);

    case 96:
      // '`'
      if (this.options.ecmaVersion < 6) break;
      ++this.pos;
      return this.finishToken(_tokentype.types.backQuote);

    case 48:
      // '0'
      var next = this.input.charCodeAt(this.pos + 1);
      if (next === 120 || next === 88) return this.readRadixNumber(16); // '0x', '0X' - hex number
      if (this.options.ecmaVersion >= 6) {
        if (next === 111 || next === 79) return this.readRadixNumber(8); // '0o', '0O' - octal number
        if (next === 98 || next === 66) return this.readRadixNumber(2); // '0b', '0B' - binary number
      }
    // Anything else beginning with a digit is an integer, octal
    // number, or float.
    case 49:case 50:case 51:case 52:case 53:case 54:case 55:case 56:case 57:
      // 1-9
      return this.readNumber(false);

    // Quotes produce strings.
    case 34:case 39:
      // '"', "'"
      return this.readString(code);

    // Operators are parsed inline in tiny state machines. '=' (61) is
    // often referred to. `finishOp` simply skips the amount of
    // characters it is given as second argument, and returns a token
    // of the type given by its first argument.

    case 47:
      // '/'
      return this.readToken_slash();

    case 37:case 42:
      // '%*'
      return this.readToken_mult_modulo(code);

    case 124:case 38:
      // '|&'
      return this.readToken_pipe_amp(code);

    case 94:
      // '^'
      return this.readToken_caret();

    case 43:case 45:
      // '+-'
      return this.readToken_plus_min(code);

    case 60:case 62:
      // '<>'
      return this.readToken_lt_gt(code);

    case 61:case 33:
      // '=!'
      return this.readToken_eq_excl(code);

    case 126:
      // '~'
      return this.finishOp(_tokentype.types.prefix, 1);
  }

  this.raise(this.pos, "Unexpected character '" + codePointToString(code) + "'");
};

pp.finishOp = function (type, size) {
  var str = this.input.slice(this.pos, this.pos + size);
  this.pos += size;
  return this.finishToken(type, str);
};

// Parse a regular expression. Some context-awareness is necessary,
// since a '/' inside a '[]' set does not end the expression.

function tryCreateRegexp(src, flags, throwErrorAt) {
  try {
    return new RegExp(src, flags);
  } catch (e) {
    if (throwErrorAt !== undefined) {
      if (e instanceof SyntaxError) this.raise(throwErrorAt, "Error parsing regular expression: " + e.message);
      this.raise(e);
    }
  }
}

var regexpUnicodeSupport = !!tryCreateRegexp("￿", "u");

pp.readRegexp = function () {
  var _this = this;

  var escaped = undefined,
      inClass = undefined,
      start = this.pos;
  for (;;) {
    if (this.pos >= this.input.length) this.raise(start, "Unterminated regular expression");
    var ch = this.input.charAt(this.pos);
    if (_whitespace.lineBreak.test(ch)) this.raise(start, "Unterminated regular expression");
    if (!escaped) {
      if (ch === "[") inClass = true;else if (ch === "]" && inClass) inClass = false;else if (ch === "/" && !inClass) break;
      escaped = ch === "\\";
    } else escaped = false;
    ++this.pos;
  }
  var content = this.input.slice(start, this.pos);
  ++this.pos;
  // Need to use `readWord1` because '\uXXXX' sequences are allowed
  // here (don't ask).
  var mods = this.readWord1();
  var tmp = content;
  if (mods) {
    var validFlags = /^[gmsiy]*$/;
    if (this.options.ecmaVersion >= 6) validFlags = /^[gmsiyu]*$/;
    if (!validFlags.test(mods)) this.raise(start, "Invalid regular expression flag");
    if (mods.indexOf("u") >= 0 && !regexpUnicodeSupport) {
      // Replace each astral symbol and every Unicode escape sequence that
      // possibly represents an astral symbol or a paired surrogate with a
      // single ASCII symbol to avoid throwing on regular expressions that
      // are only valid in combination with the `/u` flag.
      // Note: replacing with the ASCII symbol `x` might cause false
      // negatives in unlikely scenarios. For example, `[\u{61}-b]` is a
      // perfectly valid pattern that is equivalent to `[a-b]`, but it would
      // be replaced by `[x-b]` which throws an error.
      tmp = tmp.replace(/\\u\{([0-9a-fA-F]+)\}/g, function (match, code, offset) {
        code = Number("0x" + code);
        if (code > 0x10FFFF) _this.raise(start + offset + 3, "Code point out of bounds");
        return "x";
      });
      tmp = tmp.replace(/\\u([a-fA-F0-9]{4})|[\uD800-\uDBFF][\uDC00-\uDFFF]/g, "x");
    }
  }
  // Detect invalid regular expressions.
  var value = null;
  // Rhino's regular expression parser is flaky and throws uncatchable exceptions,
  // so don't do detection if we are running under Rhino
  if (!isRhino) {
    tryCreateRegexp(tmp, undefined, start);
    // Get a regular expression object for this pattern-flag pair, or `null` in
    // case the current environment doesn't support the flags it uses.
    value = tryCreateRegexp(content, mods);
  }
  return this.finishToken(_tokentype.types.regexp, { pattern: content, flags: mods, value: value });
};

// Read an integer in the given radix. Return null if zero digits
// were read, the integer value otherwise. When `len` is given, this
// will return `null` unless the integer has exactly `len` digits.

pp.readInt = function (radix, len) {
  var start = this.pos,
      total = 0;
  for (var i = 0, e = len == null ? Infinity : len; i < e; ++i) {
    var code = this.input.charCodeAt(this.pos),
        val = undefined;
    if (code >= 97) val = code - 97 + 10; // a
    else if (code >= 65) val = code - 65 + 10; // A
    else if (code >= 48 && code <= 57) val = code - 48; // 0-9
    else val = Infinity;
    if (val >= radix) break;
    ++this.pos;
    total = total * radix + val;
  }
  if (this.pos === start || len != null && this.pos - start !== len) return null;

  return total;
};

pp.readRadixNumber = function (radix) {
  this.pos += 2; // 0x
  var val = this.readInt(radix);
  if (val == null) this.raise(this.start + 2, "Expected number in radix " + radix);
  if (_identifier.isIdentifierStart(this.fullCharCodeAtPos())) this.raise(this.pos, "Identifier directly after number");
  return this.finishToken(_tokentype.types.num, val);
};

// Read an integer, octal integer, or floating-point number.

pp.readNumber = function (startsWithDot) {
  var start = this.pos,
      isFloat = false,
      octal = this.input.charCodeAt(this.pos) === 48;
  if (!startsWithDot && this.readInt(10) === null) this.raise(start, "Invalid number");
  var next = this.input.charCodeAt(this.pos);
  if (next === 46) {
    // '.'
    ++this.pos;
    this.readInt(10);
    isFloat = true;
    next = this.input.charCodeAt(this.pos);
  }
  if (next === 69 || next === 101) {
    // 'eE'
    next = this.input.charCodeAt(++this.pos);
    if (next === 43 || next === 45) ++this.pos; // '+-'
    if (this.readInt(10) === null) this.raise(start, "Invalid number");
    isFloat = true;
  }
  if (_identifier.isIdentifierStart(this.fullCharCodeAtPos())) this.raise(this.pos, "Identifier directly after number");

  var str = this.input.slice(start, this.pos),
      val = undefined;
  if (isFloat) val = parseFloat(str);else if (!octal || str.length === 1) val = parseInt(str, 10);else if (/[89]/.test(str) || this.strict) this.raise(start, "Invalid number");else val = parseInt(str, 8);
  return this.finishToken(_tokentype.types.num, val);
};

// Read a string value, interpreting backslash-escapes.

pp.readCodePoint = function () {
  var ch = this.input.charCodeAt(this.pos),
      code = undefined;

  if (ch === 123) {
    if (this.options.ecmaVersion < 6) this.unexpected();
    var codePos = ++this.pos;
    code = this.readHexChar(this.input.indexOf("}", this.pos) - this.pos);
    ++this.pos;
    if (code > 0x10FFFF) this.raise(codePos, "Code point out of bounds");
  } else {
    code = this.readHexChar(4);
  }
  return code;
};

function codePointToString(code) {
  // UTF-16 Decoding
  if (code <= 0xFFFF) return String.fromCharCode(code);
  code -= 0x10000;
  return String.fromCharCode((code >> 10) + 0xD800, (code & 1023) + 0xDC00);
}

pp.readString = function (quote) {
  var out = "",
      chunkStart = ++this.pos;
  for (;;) {
    if (this.pos >= this.input.length) this.raise(this.start, "Unterminated string constant");
    var ch = this.input.charCodeAt(this.pos);
    if (ch === quote) break;
    if (ch === 92) {
      // '\'
      out += this.input.slice(chunkStart, this.pos);
      out += this.readEscapedChar(false);
      chunkStart = this.pos;
    } else {
      if (_whitespace.isNewLine(ch)) this.raise(this.start, "Unterminated string constant");
      ++this.pos;
    }
  }
  out += this.input.slice(chunkStart, this.pos++);
  return this.finishToken(_tokentype.types.string, out);
};

// Reads template string tokens.

pp.readTmplToken = function () {
  var out = "",
      chunkStart = this.pos;
  for (;;) {
    if (this.pos >= this.input.length) this.raise(this.start, "Unterminated template");
    var ch = this.input.charCodeAt(this.pos);
    if (ch === 96 || ch === 36 && this.input.charCodeAt(this.pos + 1) === 123) {
      // '`', '${'
      if (this.pos === this.start && this.type === _tokentype.types.template) {
        if (ch === 36) {
          this.pos += 2;
          return this.finishToken(_tokentype.types.dollarBraceL);
        } else {
          ++this.pos;
          return this.finishToken(_tokentype.types.backQuote);
        }
      }
      out += this.input.slice(chunkStart, this.pos);
      return this.finishToken(_tokentype.types.template, out);
    }
    if (ch === 92) {
      // '\'
      out += this.input.slice(chunkStart, this.pos);
      out += this.readEscapedChar(true);
      chunkStart = this.pos;
    } else if (_whitespace.isNewLine(ch)) {
      out += this.input.slice(chunkStart, this.pos);
      ++this.pos;
      switch (ch) {
        case 13:
          if (this.input.charCodeAt(this.pos) === 10) ++this.pos;
        case 10:
          out += "\n";
          break;
        default:
          out += String.fromCharCode(ch);
          break;
      }
      if (this.options.locations) {
        ++this.curLine;
        this.lineStart = this.pos;
      }
      chunkStart = this.pos;
    } else {
      ++this.pos;
    }
  }
};

// Used to read escaped characters

pp.readEscapedChar = function (inTemplate) {
  var ch = this.input.charCodeAt(++this.pos);
  ++this.pos;
  switch (ch) {
    case 110:
      return "\n"; // 'n' -> '\n'
    case 114:
      return "\r"; // 'r' -> '\r'
    case 120:
      return String.fromCharCode(this.readHexChar(2)); // 'x'
    case 117:
      return codePointToString(this.readCodePoint()); // 'u'
    case 116:
      return "\t"; // 't' -> '\t'
    case 98:
      return "\b"; // 'b' -> '\b'
    case 118:
      return "\u000b"; // 'v' -> '\u000b'
    case 102:
      return "\f"; // 'f' -> '\f'
    case 13:
      if (this.input.charCodeAt(this.pos) === 10) ++this.pos; // '\r\n'
    case 10:
      // ' \n'
      if (this.options.locations) {
        this.lineStart = this.pos;++this.curLine;
      }
      return "";
    default:
      if (ch >= 48 && ch <= 55) {
        var octalStr = this.input.substr(this.pos - 1, 3).match(/^[0-7]+/)[0];
        var octal = parseInt(octalStr, 8);
        if (octal > 255) {
          octalStr = octalStr.slice(0, -1);
          octal = parseInt(octalStr, 8);
        }
        if (octal > 0 && (this.strict || inTemplate)) {
          this.raise(this.pos - 2, "Octal literal in strict mode");
        }
        this.pos += octalStr.length - 1;
        return String.fromCharCode(octal);
      }
      return String.fromCharCode(ch);
  }
};

// Used to read character escape sequences ('\x', '\u', '\U').

pp.readHexChar = function (len) {
  var codePos = this.pos;
  var n = this.readInt(16, len);
  if (n === null) this.raise(codePos, "Bad character escape sequence");
  return n;
};

// Read an identifier, and return it as a string. Sets `this.containsEsc`
// to whether the word contained a '\u' escape.
//
// Incrementally adds only escaped chars, adding other chunks as-is
// as a micro-optimization.

pp.readWord1 = function () {
  this.containsEsc = false;
  var word = "",
      first = true,
      chunkStart = this.pos;
  var astral = this.options.ecmaVersion >= 6;
  while (this.pos < this.input.length) {
    var ch = this.fullCharCodeAtPos();
    if (_identifier.isIdentifierChar(ch, astral)) {
      this.pos += ch <= 0xffff ? 1 : 2;
    } else if (ch === 92) {
      // "\"
      this.containsEsc = true;
      word += this.input.slice(chunkStart, this.pos);
      var escStart = this.pos;
      if (this.input.charCodeAt(++this.pos) != 117) // "u"
        this.raise(this.pos, "Expecting Unicode escape sequence \\uXXXX");
      ++this.pos;
      var esc = this.readCodePoint();
      if (!(first ? _identifier.isIdentifierStart : _identifier.isIdentifierChar)(esc, astral)) this.raise(escStart, "Invalid Unicode escape");
      word += codePointToString(esc);
      chunkStart = this.pos;
    } else {
      break;
    }
    first = false;
  }
  return word + this.input.slice(chunkStart, this.pos);
};

// Read an identifier or keyword token. Will check for reserved
// words when necessary.

pp.readWord = function () {
  var word = this.readWord1();
  var type = _tokentype.types.name;
  if ((this.options.ecmaVersion >= 6 || !this.containsEsc) && this.isKeyword(word)) type = _tokentype.keywords[word];
  return this.finishToken(type, word);
};

},{"./identifier":2,"./locutil":5,"./state":10,"./tokentype":14,"./whitespace":16}],14:[function(_dereq_,module,exports){
// ## Token types

// The assignment of fine-grained, information-carrying type objects
// allows the tokenizer to store the information it has about a
// token in a way that is very cheap for the parser to look up.

// All token type variables start with an underscore, to make them
// easy to recognize.

// The `beforeExpr` property is used to disambiguate between regular
// expressions and divisions. It is set on all token types that can
// be followed by an expression (thus, a slash after them would be a
// regular expression).
//
// `isLoop` marks a keyword as starting a loop, which is important
// to know when parsing a label, in order to allow or disallow
// continue jumps to that label.

"use strict";

exports.__esModule = true;

function _classCallCheck(instance, Constructor) { if (!(instance instanceof Constructor)) { throw new TypeError("Cannot call a class as a function"); } }

var TokenType = function TokenType(label) {
  var conf = arguments.length <= 1 || arguments[1] === undefined ? {} : arguments[1];

  _classCallCheck(this, TokenType);

  this.label = label;
  this.keyword = conf.keyword;
  this.beforeExpr = !!conf.beforeExpr;
  this.startsExpr = !!conf.startsExpr;
  this.isLoop = !!conf.isLoop;
  this.isAssign = !!conf.isAssign;
  this.prefix = !!conf.prefix;
  this.postfix = !!conf.postfix;
  this.binop = conf.binop || null;
  this.updateContext = null;
};

exports.TokenType = TokenType;

function binop(name, prec) {
  return new TokenType(name, { beforeExpr: true, binop: prec });
}
var beforeExpr = { beforeExpr: true },
    startsExpr = { startsExpr: true };

var types = {
  num: new TokenType("num", startsExpr),
  regexp: new TokenType("regexp", startsExpr),
  string: new TokenType("string", startsExpr),
  name: new TokenType("name", startsExpr),
  eof: new TokenType("eof"),

  // Punctuation token types.
  bracketL: new TokenType("[", { beforeExpr: true, startsExpr: true }),
  bracketR: new TokenType("]"),
  braceL: new TokenType("{", { beforeExpr: true, startsExpr: true }),
  braceR: new TokenType("}"),
  parenL: new TokenType("(", { beforeExpr: true, startsExpr: true }),
  parenR: new TokenType(")"),
  comma: new TokenType(",", beforeExpr),
  semi: new TokenType(";", beforeExpr),
  colon: new TokenType(":", beforeExpr),
  dot: new TokenType("."),
  question: new TokenType("?", beforeExpr),
  arrow: new TokenType("=>", beforeExpr),
  template: new TokenType("template"),
  ellipsis: new TokenType("...", beforeExpr),
  backQuote: new TokenType("`", startsExpr),
  dollarBraceL: new TokenType("${", { beforeExpr: true, startsExpr: true }),

  // Operators. These carry several kinds of properties to help the
  // parser use them properly (the presence of these properties is
  // what categorizes them as operators).
  //
  // `binop`, when present, specifies that this operator is a binary
  // operator, and will refer to its precedence.
  //
  // `prefix` and `postfix` mark the operator as a prefix or postfix
  // unary operator.
  //
  // `isAssign` marks all of `=`, `+=`, `-=` etcetera, which act as
  // binary operators with a very low precedence, that should result
  // in AssignmentExpression nodes.

  eq: new TokenType("=", { beforeExpr: true, isAssign: true }),
  assign: new TokenType("_=", { beforeExpr: true, isAssign: true }),
  incDec: new TokenType("++/--", { prefix: true, postfix: true, startsExpr: true }),
  prefix: new TokenType("prefix", { beforeExpr: true, prefix: true, startsExpr: true }),
  logicalOR: binop("||", 1),
  logicalAND: binop("&&", 2),
  bitwiseOR: binop("|", 3),
  bitwiseXOR: binop("^", 4),
  bitwiseAND: binop("&", 5),
  equality: binop("==/!=", 6),
  relational: binop("</>", 7),
  bitShift: binop("<</>>", 8),
  plusMin: new TokenType("+/-", { beforeExpr: true, binop: 9, prefix: true, startsExpr: true }),
  modulo: binop("%", 10),
  star: binop("*", 10),
  slash: binop("/", 10)
};

exports.types = types;
// Map keyword names to token types.

var keywords = {};

exports.keywords = keywords;
// Succinct definitions of keyword token types
function kw(name) {
  var options = arguments.length <= 1 || arguments[1] === undefined ? {} : arguments[1];

  options.keyword = name;
  keywords[name] = types["_" + name] = new TokenType(name, options);
}

kw("break");
kw("case", beforeExpr);
kw("catch");
kw("continue");
kw("debugger");
kw("default", beforeExpr);
kw("do", { isLoop: true });
kw("else", beforeExpr);
kw("finally");
kw("for", { isLoop: true });
kw("function", startsExpr);
kw("if");
kw("return", beforeExpr);
kw("switch");
kw("throw", beforeExpr);
kw("try");
kw("var");
kw("let");
kw("const");
kw("while", { isLoop: true });
kw("with");
kw("new", { beforeExpr: true, startsExpr: true });
kw("this", startsExpr);
kw("super", startsExpr);
kw("class");
kw("extends", beforeExpr);
kw("export");
kw("import");
kw("yield", { beforeExpr: true, startsExpr: true });
kw("null", startsExpr);
kw("true", startsExpr);
kw("false", startsExpr);
kw("in", { beforeExpr: true, binop: 7 });
kw("instanceof", { beforeExpr: true, binop: 7 });
kw("typeof", { beforeExpr: true, prefix: true, startsExpr: true });
kw("void", { beforeExpr: true, prefix: true, startsExpr: true });
kw("delete", { beforeExpr: true, prefix: true, startsExpr: true });

},{}],15:[function(_dereq_,module,exports){
"use strict";

exports.__esModule = true;
exports.isArray = isArray;
exports.has = has;

function isArray(obj) {
  return Object.prototype.toString.call(obj) === "[object Array]";
}

// Checks if an object has a property.

function has(obj, propName) {
  return Object.prototype.hasOwnProperty.call(obj, propName);
}

},{}],16:[function(_dereq_,module,exports){
// Matches a whole line break (where CRLF is considered a single
// line break). Used to count lines.

"use strict";

exports.__esModule = true;
exports.isNewLine = isNewLine;
var lineBreak = /\r\n?|\n|\u2028|\u2029/;
exports.lineBreak = lineBreak;
var lineBreakG = new RegExp(lineBreak.source, "g");

exports.lineBreakG = lineBreakG;

function isNewLine(code) {
  return code === 10 || code === 13 || code === 0x2028 || code == 0x2029;
}

var nonASCIIwhitespace = /[\u1680\u180e\u2000-\u200a\u202f\u205f\u3000\ufeff]/;
exports.nonASCIIwhitespace = nonASCIIwhitespace;

},{}]},{},[3])(3)
});
}).call(this,typeof global !== "undefined" ? global : typeof self !== "undefined" ? self : typeof window !== "undefined" ? window : {})

},{}],16:[function(require,module,exports){
(function (global){
(function(f){if(typeof exports==="object"&&typeof module!=="undefined"){module.exports=f()}else if(typeof define==="function"&&define.amd){define([],f)}else{var g;if(typeof window!=="undefined"){g=window}else if(typeof global!=="undefined"){g=global}else if(typeof self!=="undefined"){g=self}else{g=this}(g.acorn || (g.acorn = {})).loose = f()}})(function(){var define,module,exports;return (function e(t,n,r){function s(o,u){if(!n[o]){if(!t[o]){var a=typeof require=="function"&&require;if(!u&&a)return a(o,!0);if(i)return i(o,!0);var f=new Error("Cannot find module '"+o+"'");throw f.code="MODULE_NOT_FOUND",f}var l=n[o]={exports:{}};t[o][0].call(l.exports,function(e){var n=t[o][1][e];return s(n?n:e)},l,l.exports,e,t,n,r)}return n[o].exports}var i=typeof require=="function"&&require;for(var o=0;o<r.length;o++)s(r[o]);return s})({1:[function(_dereq_,module,exports){
"use strict";

module.exports = typeof acorn != 'undefined' ? acorn : require("./acorn");

},{}],2:[function(_dereq_,module,exports){
"use strict";

var _state = _dereq_("./state");

var _parseutil = _dereq_("./parseutil");

var _ = _dereq_("..");

var lp = _state.LooseParser.prototype;

lp.checkLVal = function (expr, binding) {
  if (!expr) return expr;
  switch (expr.type) {
    case "Identifier":
      return expr;

    case "MemberExpression":
      return binding ? this.dummyIdent() : expr;

    case "ParenthesizedExpression":
      expr.expression = this.checkLVal(expr.expression, binding);
      return expr;

    // FIXME recursively check contents
    case "ObjectPattern":
    case "ArrayPattern":
    case "RestElement":
    case "AssignmentPattern":
      if (this.options.ecmaVersion >= 6) return expr;

    default:
      return this.dummyIdent();
  }
};

lp.parseExpression = function (noIn) {
  var start = this.storeCurrentPos();
  var expr = this.parseMaybeAssign(noIn);
  if (this.tok.type === _.tokTypes.comma) {
    var node = this.startNodeAt(start);
    node.expressions = [expr];
    while (this.eat(_.tokTypes.comma)) node.expressions.push(this.parseMaybeAssign(noIn));
    return this.finishNode(node, "SequenceExpression");
  }
  return expr;
};

lp.parseParenExpression = function () {
  this.pushCx();
  this.expect(_.tokTypes.parenL);
  var val = this.parseExpression();
  this.popCx();
  this.expect(_.tokTypes.parenR);
  return val;
};

lp.parseMaybeAssign = function (noIn) {
  var start = this.storeCurrentPos();
  var left = this.parseMaybeConditional(noIn);
  if (this.tok.type.isAssign) {
    var node = this.startNodeAt(start);
    node.operator = this.tok.value;
    node.left = this.tok.type === _.tokTypes.eq ? this.toAssignable(left) : this.checkLVal(left);
    this.next();
    node.right = this.parseMaybeAssign(noIn);
    return this.finishNode(node, "AssignmentExpression");
  }
  return left;
};

lp.parseMaybeConditional = function (noIn) {
  var start = this.storeCurrentPos();
  var expr = this.parseExprOps(noIn);
  if (this.eat(_.tokTypes.question)) {
    var node = this.startNodeAt(start);
    node.test = expr;
    node.consequent = this.parseMaybeAssign();
    node.alternate = this.expect(_.tokTypes.colon) ? this.parseMaybeAssign(noIn) : this.dummyIdent();
    return this.finishNode(node, "ConditionalExpression");
  }
  return expr;
};

lp.parseExprOps = function (noIn) {
  var start = this.storeCurrentPos();
  var indent = this.curIndent,
      line = this.curLineStart;
  return this.parseExprOp(this.parseMaybeUnary(noIn), start, -1, noIn, indent, line);
};

lp.parseExprOp = function (left, start, minPrec, noIn, indent, line) {
  if (this.curLineStart != line && this.curIndent < indent && this.tokenStartsLine()) return left;
  var prec = this.tok.type.binop;
  if (prec != null && (!noIn || this.tok.type !== _.tokTypes._in)) {
    if (prec > minPrec) {
      var node = this.startNodeAt(start);
      node.left = left;
      node.operator = this.tok.value;
      this.next();
      if (this.curLineStart != line && this.curIndent < indent && this.tokenStartsLine()) {
        node.right = this.dummyIdent();
      } else {
        var rightStart = this.storeCurrentPos();
        node.right = this.parseExprOp(this.parseMaybeUnary(noIn), rightStart, prec, noIn, indent, line);
      }
      this.finishNode(node, /&&|\|\|/.test(node.operator) ? "LogicalExpression" : "BinaryExpression");
      return this.parseExprOp(node, start, minPrec, noIn, indent, line);
    }
  }
  return left;
};

lp.parseMaybeUnary = function (noIn) {
  if (this.tok.type.prefix) {
    var node = this.startNode(),
        update = this.tok.type === _.tokTypes.incDec;
    node.operator = this.tok.value;
    node.prefix = true;
    this.next();
    node.argument = this.parseMaybeUnary(noIn);
    if (update) node.argument = this.checkLVal(node.argument);
    return this.finishNode(node, update ? "UpdateExpression" : "UnaryExpression");
  } else if (this.tok.type === _.tokTypes.ellipsis) {
    var node = this.startNode();
    this.next();
    node.argument = this.parseMaybeUnary(noIn);
    return this.finishNode(node, "SpreadElement");
  }
  var start = this.storeCurrentPos();
  var expr = this.parseExprSubscripts();
  while (this.tok.type.postfix && !this.canInsertSemicolon()) {
    var node = this.startNodeAt(start);
    node.operator = this.tok.value;
    node.prefix = false;
    node.argument = this.checkLVal(expr);
    this.next();
    expr = this.finishNode(node, "UpdateExpression");
  }
  return expr;
};

lp.parseExprSubscripts = function () {
  var start = this.storeCurrentPos();
  return this.parseSubscripts(this.parseExprAtom(), start, false, this.curIndent, this.curLineStart);
};

lp.parseSubscripts = function (base, start, noCalls, startIndent, line) {
  for (;;) {
    if (this.curLineStart != line && this.curIndent <= startIndent && this.tokenStartsLine()) {
      if (this.tok.type == _.tokTypes.dot && this.curIndent == startIndent) --startIndent;else return base;
    }

    if (this.eat(_.tokTypes.dot)) {
      var node = this.startNodeAt(start);
      node.object = base;
      if (this.curLineStart != line && this.curIndent <= startIndent && this.tokenStartsLine()) node.property = this.dummyIdent();else node.property = this.parsePropertyAccessor() || this.dummyIdent();
      node.computed = false;
      base = this.finishNode(node, "MemberExpression");
    } else if (this.tok.type == _.tokTypes.bracketL) {
      this.pushCx();
      this.next();
      var node = this.startNodeAt(start);
      node.object = base;
      node.property = this.parseExpression();
      node.computed = true;
      this.popCx();
      this.expect(_.tokTypes.bracketR);
      base = this.finishNode(node, "MemberExpression");
    } else if (!noCalls && this.tok.type == _.tokTypes.parenL) {
      var node = this.startNodeAt(start);
      node.callee = base;
      node.arguments = this.parseExprList(_.tokTypes.parenR);
      base = this.finishNode(node, "CallExpression");
    } else if (this.tok.type == _.tokTypes.backQuote) {
      var node = this.startNodeAt(start);
      node.tag = base;
      node.quasi = this.parseTemplate();
      base = this.finishNode(node, "TaggedTemplateExpression");
    } else {
      return base;
    }
  }
};

lp.parseExprAtom = function () {
  var node = undefined;
  switch (this.tok.type) {
    case _.tokTypes._this:
    case _.tokTypes._super:
      var type = this.tok.type === _.tokTypes._this ? "ThisExpression" : "Super";
      node = this.startNode();
      this.next();
      return this.finishNode(node, type);

    case _.tokTypes.name:
      var start = this.storeCurrentPos();
      var id = this.parseIdent();
      return this.eat(_.tokTypes.arrow) ? this.parseArrowExpression(this.startNodeAt(start), [id]) : id;

    case _.tokTypes.regexp:
      node = this.startNode();
      var val = this.tok.value;
      node.regex = { pattern: val.pattern, flags: val.flags };
      node.value = val.value;
      node.raw = this.input.slice(this.tok.start, this.tok.end);
      this.next();
      return this.finishNode(node, "Literal");

    case _.tokTypes.num:case _.tokTypes.string:
      node = this.startNode();
      node.value = this.tok.value;
      node.raw = this.input.slice(this.tok.start, this.tok.end);
      this.next();
      return this.finishNode(node, "Literal");

    case _.tokTypes._null:case _.tokTypes._true:case _.tokTypes._false:
      node = this.startNode();
      node.value = this.tok.type === _.tokTypes._null ? null : this.tok.type === _.tokTypes._true;
      node.raw = this.tok.type.keyword;
      this.next();
      return this.finishNode(node, "Literal");

    case _.tokTypes.parenL:
      var parenStart = this.storeCurrentPos();
      this.next();
      var inner = this.parseExpression();
      this.expect(_.tokTypes.parenR);
      if (this.eat(_.tokTypes.arrow)) {
        return this.parseArrowExpression(this.startNodeAt(parenStart), inner.expressions || (_parseutil.isDummy(inner) ? [] : [inner]));
      }
      if (this.options.preserveParens) {
        var par = this.startNodeAt(parenStart);
        par.expression = inner;
        inner = this.finishNode(par, "ParenthesizedExpression");
      }
      return inner;

    case _.tokTypes.bracketL:
      node = this.startNode();
      node.elements = this.parseExprList(_.tokTypes.bracketR, true);
      return this.finishNode(node, "ArrayExpression");

    case _.tokTypes.braceL:
      return this.parseObj();

    case _.tokTypes._class:
      return this.parseClass();

    case _.tokTypes._function:
      node = this.startNode();
      this.next();
      return this.parseFunction(node, false);

    case _.tokTypes._new:
      return this.parseNew();

    case _.tokTypes._yield:
      node = this.startNode();
      this.next();
      if (this.semicolon() || this.canInsertSemicolon() || this.tok.type != _.tokTypes.star && !this.tok.type.startsExpr) {
        node.delegate = false;
        node.argument = null;
      } else {
        node.delegate = this.eat(_.tokTypes.star);
        node.argument = this.parseMaybeAssign();
      }
      return this.finishNode(node, "YieldExpression");

    case _.tokTypes.backQuote:
      return this.parseTemplate();

    default:
      return this.dummyIdent();
  }
};

lp.parseNew = function () {
  var node = this.startNode(),
      startIndent = this.curIndent,
      line = this.curLineStart;
  var meta = this.parseIdent(true);
  if (this.options.ecmaVersion >= 6 && this.eat(_.tokTypes.dot)) {
    node.meta = meta;
    node.property = this.parseIdent(true);
    return this.finishNode(node, "MetaProperty");
  }
  var start = this.storeCurrentPos();
  node.callee = this.parseSubscripts(this.parseExprAtom(), start, true, startIndent, line);
  if (this.tok.type == _.tokTypes.parenL) {
    node.arguments = this.parseExprList(_.tokTypes.parenR);
  } else {
    node.arguments = [];
  }
  return this.finishNode(node, "NewExpression");
};

lp.parseTemplateElement = function () {
  var elem = this.startNode();
  elem.value = {
    raw: this.input.slice(this.tok.start, this.tok.end).replace(/\r\n?/g, "\n"),
    cooked: this.tok.value
  };
  this.next();
  elem.tail = this.tok.type === _.tokTypes.backQuote;
  return this.finishNode(elem, "TemplateElement");
};

lp.parseTemplate = function () {
  var node = this.startNode();
  this.next();
  node.expressions = [];
  var curElt = this.parseTemplateElement();
  node.quasis = [curElt];
  while (!curElt.tail) {
    this.next();
    node.expressions.push(this.parseExpression());
    if (this.expect(_.tokTypes.braceR)) {
      curElt = this.parseTemplateElement();
    } else {
      curElt = this.startNode();
      curElt.value = { cooked: "", raw: "" };
      curElt.tail = true;
    }
    node.quasis.push(curElt);
  }
  this.expect(_.tokTypes.backQuote);
  return this.finishNode(node, "TemplateLiteral");
};

lp.parseObj = function () {
  var node = this.startNode();
  node.properties = [];
  this.pushCx();
  var indent = this.curIndent + 1,
      line = this.curLineStart;
  this.eat(_.tokTypes.braceL);
  if (this.curIndent + 1 < indent) {
    indent = this.curIndent;line = this.curLineStart;
  }
  while (!this.closes(_.tokTypes.braceR, indent, line)) {
    var prop = this.startNode(),
        isGenerator = undefined,
        start = undefined;
    if (this.options.ecmaVersion >= 6) {
      start = this.storeCurrentPos();
      prop.method = false;
      prop.shorthand = false;
      isGenerator = this.eat(_.tokTypes.star);
    }
    this.parsePropertyName(prop);
    if (_parseutil.isDummy(prop.key)) {
      if (_parseutil.isDummy(this.parseMaybeAssign())) this.next();this.eat(_.tokTypes.comma);continue;
    }
    if (this.eat(_.tokTypes.colon)) {
      prop.kind = "init";
      prop.value = this.parseMaybeAssign();
    } else if (this.options.ecmaVersion >= 6 && (this.tok.type === _.tokTypes.parenL || this.tok.type === _.tokTypes.braceL)) {
      prop.kind = "init";
      prop.method = true;
      prop.value = this.parseMethod(isGenerator);
    } else if (this.options.ecmaVersion >= 5 && prop.key.type === "Identifier" && !prop.computed && (prop.key.name === "get" || prop.key.name === "set") && (this.tok.type != _.tokTypes.comma && this.tok.type != _.tokTypes.braceR)) {
      prop.kind = prop.key.name;
      this.parsePropertyName(prop);
      prop.value = this.parseMethod(false);
    } else {
      prop.kind = "init";
      if (this.options.ecmaVersion >= 6) {
        if (this.eat(_.tokTypes.eq)) {
          var assign = this.startNodeAt(start);
          assign.operator = "=";
          assign.left = prop.key;
          assign.right = this.parseMaybeAssign();
          prop.value = this.finishNode(assign, "AssignmentExpression");
        } else {
          prop.value = prop.key;
        }
      } else {
        prop.value = this.dummyIdent();
      }
      prop.shorthand = true;
    }
    node.properties.push(this.finishNode(prop, "Property"));
    this.eat(_.tokTypes.comma);
  }
  this.popCx();
  if (!this.eat(_.tokTypes.braceR)) {
    // If there is no closing brace, make the node span to the start
    // of the next token (this is useful for Tern)
    this.last.end = this.tok.start;
    if (this.options.locations) this.last.loc.end = this.tok.loc.start;
  }
  return this.finishNode(node, "ObjectExpression");
};

lp.parsePropertyName = function (prop) {
  if (this.options.ecmaVersion >= 6) {
    if (this.eat(_.tokTypes.bracketL)) {
      prop.computed = true;
      prop.key = this.parseExpression();
      this.expect(_.tokTypes.bracketR);
      return;
    } else {
      prop.computed = false;
    }
  }
  var key = this.tok.type === _.tokTypes.num || this.tok.type === _.tokTypes.string ? this.parseExprAtom() : this.parseIdent();
  prop.key = key || this.dummyIdent();
};

lp.parsePropertyAccessor = function () {
  if (this.tok.type === _.tokTypes.name || this.tok.type.keyword) return this.parseIdent();
};

lp.parseIdent = function () {
  var name = this.tok.type === _.tokTypes.name ? this.tok.value : this.tok.type.keyword;
  if (!name) return this.dummyIdent();
  var node = this.startNode();
  this.next();
  node.name = name;
  return this.finishNode(node, "Identifier");
};

lp.initFunction = function (node) {
  node.id = null;
  node.params = [];
  if (this.options.ecmaVersion >= 6) {
    node.generator = false;
    node.expression = false;
  }
};

// Convert existing expression atom to assignable pattern
// if possible.

lp.toAssignable = function (node, binding) {
  if (this.options.ecmaVersion >= 6 && node) {
    switch (node.type) {
      case "ObjectExpression":
        node.type = "ObjectPattern";
        var props = node.properties;
        for (var i = 0; i < props.length; i++) {
          this.toAssignable(props[i].value, binding);
        }break;

      case "ArrayExpression":
        node.type = "ArrayPattern";
        this.toAssignableList(node.elements, binding);
        break;

      case "SpreadElement":
        node.type = "RestElement";
        node.argument = this.toAssignable(node.argument, binding);
        break;

      case "AssignmentExpression":
        node.type = "AssignmentPattern";
        delete node.operator;
        break;
    }
  }
  return this.checkLVal(node, binding);
};

lp.toAssignableList = function (exprList, binding) {
  for (var i = 0; i < exprList.length; i++) {
    exprList[i] = this.toAssignable(exprList[i], binding);
  }return exprList;
};

lp.parseFunctionParams = function (params) {
  params = this.parseExprList(_.tokTypes.parenR);
  return this.toAssignableList(params, true);
};

lp.parseMethod = function (isGenerator) {
  var node = this.startNode();
  this.initFunction(node);
  node.params = this.parseFunctionParams();
  node.generator = isGenerator || false;
  node.expression = this.options.ecmaVersion >= 6 && this.tok.type !== _.tokTypes.braceL;
  node.body = node.expression ? this.parseMaybeAssign() : this.parseBlock();
  return this.finishNode(node, "FunctionExpression");
};

lp.parseArrowExpression = function (node, params) {
  this.initFunction(node);
  node.params = this.toAssignableList(params, true);
  node.expression = this.tok.type !== _.tokTypes.braceL;
  node.body = node.expression ? this.parseMaybeAssign() : this.parseBlock();
  return this.finishNode(node, "ArrowFunctionExpression");
};

lp.parseExprList = function (close, allowEmpty) {
  this.pushCx();
  var indent = this.curIndent,
      line = this.curLineStart,
      elts = [];
  this.next(); // Opening bracket
  while (!this.closes(close, indent + 1, line)) {
    if (this.eat(_.tokTypes.comma)) {
      elts.push(allowEmpty ? null : this.dummyIdent());
      continue;
    }
    var elt = this.parseMaybeAssign();
    if (_parseutil.isDummy(elt)) {
      if (this.closes(close, indent, line)) break;
      this.next();
    } else {
      elts.push(elt);
    }
    this.eat(_.tokTypes.comma);
  }
  this.popCx();
  if (!this.eat(close)) {
    // If there is no closing brace, make the node span to the start
    // of the next token (this is useful for Tern)
    this.last.end = this.tok.start;
    if (this.options.locations) this.last.loc.end = this.tok.loc.start;
  }
  return elts;
};

},{"..":1,"./parseutil":4,"./state":5}],3:[function(_dereq_,module,exports){
// Acorn: Loose parser
//
// This module provides an alternative parser (`parse_dammit`) that
// exposes that same interface as `parse`, but will try to parse
// anything as JavaScript, repairing syntax error the best it can.
// There are circumstances in which it will raise an error and give
// up, but they are very rare. The resulting AST will be a mostly
// valid JavaScript AST (as per the [Mozilla parser API][api], except
// that:
//
// - Return outside functions is allowed
//
// - Label consistency (no conflicts, break only to existing labels)
//   is not enforced.
//
// - Bogus Identifier nodes with a name of `"✖"` are inserted whenever
//   the parser got too confused to return anything meaningful.
//
// [api]: https://developer.mozilla.org/en-US/docs/SpiderMonkey/Parser_API
//
// The expected use for this is to *first* try `acorn.parse`, and only
// if that fails switch to `parse_dammit`. The loose parser might
// parse badly indented code incorrectly, so **don't** use it as
// your default parser.
//
// Quite a lot of acorn.js is duplicated here. The alternative was to
// add a *lot* of extra cruft to that file, making it less readable
// and slower. Copying and editing the code allowed me to make
// invasive changes and simplifications without creating a complicated
// tangle.

"use strict";

exports.__esModule = true;
exports.parse_dammit = parse_dammit;

function _interopRequireWildcard(obj) { if (obj && obj.__esModule) { return obj; } else { var newObj = {}; if (obj != null) { for (var key in obj) { if (Object.prototype.hasOwnProperty.call(obj, key)) newObj[key] = obj[key]; } } newObj["default"] = obj; return newObj; } }

var _ = _dereq_("..");

var acorn = _interopRequireWildcard(_);

var _state = _dereq_("./state");

_dereq_("./tokenize");

_dereq_("./statement");

_dereq_("./expression");

exports.LooseParser = _state.LooseParser;

acorn.defaultOptions.tabSize = 4;

function parse_dammit(input, options) {
  var p = new _state.LooseParser(input, options);
  p.next();
  return p.parseTopLevel();
}

acorn.parse_dammit = parse_dammit;
acorn.LooseParser = _state.LooseParser;

},{"..":1,"./expression":2,"./state":5,"./statement":6,"./tokenize":7}],4:[function(_dereq_,module,exports){
"use strict";

exports.__esModule = true;
exports.isDummy = isDummy;

function isDummy(node) {
  return node.name == "✖";
}

},{}],5:[function(_dereq_,module,exports){
"use strict";

exports.__esModule = true;

function _classCallCheck(instance, Constructor) { if (!(instance instanceof Constructor)) { throw new TypeError("Cannot call a class as a function"); } }

var _ = _dereq_("..");

var LooseParser = (function () {
  function LooseParser(input, options) {
    _classCallCheck(this, LooseParser);

    this.toks = _.tokenizer(input, options);
    this.options = this.toks.options;
    this.input = this.toks.input;
    this.tok = this.last = { type: _.tokTypes.eof, start: 0, end: 0 };
    if (this.options.locations) {
      var here = this.toks.curPosition();
      this.tok.loc = new _.SourceLocation(this.toks, here, here);
    }
    this.ahead = []; // Tokens ahead
    this.context = []; // Indentation contexted
    this.curIndent = 0;
    this.curLineStart = 0;
    this.nextLineStart = this.lineEnd(this.curLineStart) + 1;
  }

  LooseParser.prototype.startNode = function startNode() {
    return new _.Node(this.toks, this.tok.start, this.options.locations ? this.tok.loc.start : null);
  };

  LooseParser.prototype.storeCurrentPos = function storeCurrentPos() {
    return this.options.locations ? [this.tok.start, this.tok.loc.start] : this.tok.start;
  };

  LooseParser.prototype.startNodeAt = function startNodeAt(pos) {
    if (this.options.locations) {
      return new _.Node(this.toks, pos[0], pos[1]);
    } else {
      return new _.Node(this.toks, pos);
    }
  };

  LooseParser.prototype.finishNode = function finishNode(node, type) {
    node.type = type;
    node.end = this.last.end;
    if (this.options.locations) node.loc.end = this.last.loc.end;
    if (this.options.ranges) node.range[1] = this.last.end;
    return node;
  };

  LooseParser.prototype.dummyIdent = function dummyIdent() {
    var dummy = this.startNode();
    dummy.name = "✖";
    return this.finishNode(dummy, "Identifier");
  };

  LooseParser.prototype.dummyString = function dummyString() {
    var dummy = this.startNode();
    dummy.value = dummy.raw = "✖";
    return this.finishNode(dummy, "Literal");
  };

  LooseParser.prototype.eat = function eat(type) {
    if (this.tok.type === type) {
      this.next();
      return true;
    } else {
      return false;
    }
  };

  LooseParser.prototype.isContextual = function isContextual(name) {
    return this.tok.type === _.tokTypes.name && this.tok.value === name;
  };

  LooseParser.prototype.eatContextual = function eatContextual(name) {
    return this.tok.value === name && this.eat(_.tokTypes.name);
  };

  LooseParser.prototype.canInsertSemicolon = function canInsertSemicolon() {
    return this.tok.type === _.tokTypes.eof || this.tok.type === _.tokTypes.braceR || _.lineBreak.test(this.input.slice(this.last.end, this.tok.start));
  };

  LooseParser.prototype.semicolon = function semicolon() {
    return this.eat(_.tokTypes.semi);
  };

  LooseParser.prototype.expect = function expect(type) {
    if (this.eat(type)) return true;
    for (var i = 1; i <= 2; i++) {
      if (this.lookAhead(i).type == type) {
        for (var j = 0; j < i; j++) {
          this.next();
        }return true;
      }
    }
  };

  LooseParser.prototype.pushCx = function pushCx() {
    this.context.push(this.curIndent);
  };

  LooseParser.prototype.popCx = function popCx() {
    this.curIndent = this.context.pop();
  };

  LooseParser.prototype.lineEnd = function lineEnd(pos) {
    while (pos < this.input.length && !_.isNewLine(this.input.charCodeAt(pos))) ++pos;
    return pos;
  };

  LooseParser.prototype.indentationAfter = function indentationAfter(pos) {
    for (var count = 0;; ++pos) {
      var ch = this.input.charCodeAt(pos);
      if (ch === 32) ++count;else if (ch === 9) count += this.options.tabSize;else return count;
    }
  };

  LooseParser.prototype.closes = function closes(closeTok, indent, line, blockHeuristic) {
    if (this.tok.type === closeTok || this.tok.type === _.tokTypes.eof) return true;
    return line != this.curLineStart && this.curIndent < indent && this.tokenStartsLine() && (!blockHeuristic || this.nextLineStart >= this.input.length || this.indentationAfter(this.nextLineStart) < indent);
  };

  LooseParser.prototype.tokenStartsLine = function tokenStartsLine() {
    for (var p = this.tok.start - 1; p >= this.curLineStart; --p) {
      var ch = this.input.charCodeAt(p);
      if (ch !== 9 && ch !== 32) return false;
    }
    return true;
  };

  return LooseParser;
})();

exports.LooseParser = LooseParser;

},{"..":1}],6:[function(_dereq_,module,exports){
"use strict";

var _state = _dereq_("./state");

var _parseutil = _dereq_("./parseutil");

var _ = _dereq_("..");

var lp = _state.LooseParser.prototype;

lp.parseTopLevel = function () {
  var node = this.startNodeAt(this.options.locations ? [0, _.getLineInfo(this.input, 0)] : 0);
  node.body = [];
  while (this.tok.type !== _.tokTypes.eof) node.body.push(this.parseStatement());
  this.last = this.tok;
  if (this.options.ecmaVersion >= 6) {
    node.sourceType = this.options.sourceType;
  }
  return this.finishNode(node, "Program");
};

lp.parseStatement = function () {
  var starttype = this.tok.type,
      node = this.startNode();

  switch (starttype) {
    case _.tokTypes._break:case _.tokTypes._continue:
      this.next();
      var isBreak = starttype === _.tokTypes._break;
      if (this.semicolon() || this.canInsertSemicolon()) {
        node.label = null;
      } else {
        node.label = this.tok.type === _.tokTypes.name ? this.parseIdent() : null;
        this.semicolon();
      }
      return this.finishNode(node, isBreak ? "BreakStatement" : "ContinueStatement");

    case _.tokTypes._debugger:
      this.next();
      this.semicolon();
      return this.finishNode(node, "DebuggerStatement");

    case _.tokTypes._do:
      this.next();
      node.body = this.parseStatement();
      node.test = this.eat(_.tokTypes._while) ? this.parseParenExpression() : this.dummyIdent();
      this.semicolon();
      return this.finishNode(node, "DoWhileStatement");

    case _.tokTypes._for:
      this.next();
      this.pushCx();
      this.expect(_.tokTypes.parenL);
      if (this.tok.type === _.tokTypes.semi) return this.parseFor(node, null);
      if (this.tok.type === _.tokTypes._var || this.tok.type === _.tokTypes._let || this.tok.type === _.tokTypes._const) {
        var _init = this.parseVar(true);
        if (_init.declarations.length === 1 && (this.tok.type === _.tokTypes._in || this.isContextual("of"))) {
          return this.parseForIn(node, _init);
        }
        return this.parseFor(node, _init);
      }
      var init = this.parseExpression(true);
      if (this.tok.type === _.tokTypes._in || this.isContextual("of")) return this.parseForIn(node, this.toAssignable(init));
      return this.parseFor(node, init);

    case _.tokTypes._function:
      this.next();
      return this.parseFunction(node, true);

    case _.tokTypes._if:
      this.next();
      node.test = this.parseParenExpression();
      node.consequent = this.parseStatement();
      node.alternate = this.eat(_.tokTypes._else) ? this.parseStatement() : null;
      return this.finishNode(node, "IfStatement");

    case _.tokTypes._return:
      this.next();
      if (this.eat(_.tokTypes.semi) || this.canInsertSemicolon()) node.argument = null;else {
        node.argument = this.parseExpression();this.semicolon();
      }
      return this.finishNode(node, "ReturnStatement");

    case _.tokTypes._switch:
      var blockIndent = this.curIndent,
          line = this.curLineStart;
      this.next();
      node.discriminant = this.parseParenExpression();
      node.cases = [];
      this.pushCx();
      this.expect(_.tokTypes.braceL);

      var cur = undefined;
      while (!this.closes(_.tokTypes.braceR, blockIndent, line, true)) {
        if (this.tok.type === _.tokTypes._case || this.tok.type === _.tokTypes._default) {
          var isCase = this.tok.type === _.tokTypes._case;
          if (cur) this.finishNode(cur, "SwitchCase");
          node.cases.push(cur = this.startNode());
          cur.consequent = [];
          this.next();
          if (isCase) cur.test = this.parseExpression();else cur.test = null;
          this.expect(_.tokTypes.colon);
        } else {
          if (!cur) {
            node.cases.push(cur = this.startNode());
            cur.consequent = [];
            cur.test = null;
          }
          cur.consequent.push(this.parseStatement());
        }
      }
      if (cur) this.finishNode(cur, "SwitchCase");
      this.popCx();
      this.eat(_.tokTypes.braceR);
      return this.finishNode(node, "SwitchStatement");

    case _.tokTypes._throw:
      this.next();
      node.argument = this.parseExpression();
      this.semicolon();
      return this.finishNode(node, "ThrowStatement");

    case _.tokTypes._try:
      this.next();
      node.block = this.parseBlock();
      node.handler = null;
      if (this.tok.type === _.tokTypes._catch) {
        var clause = this.startNode();
        this.next();
        this.expect(_.tokTypes.parenL);
        clause.param = this.toAssignable(this.parseExprAtom(), true);
        this.expect(_.tokTypes.parenR);
        clause.guard = null;
        clause.body = this.parseBlock();
        node.handler = this.finishNode(clause, "CatchClause");
      }
      node.finalizer = this.eat(_.tokTypes._finally) ? this.parseBlock() : null;
      if (!node.handler && !node.finalizer) return node.block;
      return this.finishNode(node, "TryStatement");

    case _.tokTypes._var:
    case _.tokTypes._let:
    case _.tokTypes._const:
      return this.parseVar();

    case _.tokTypes._while:
      this.next();
      node.test = this.parseParenExpression();
      node.body = this.parseStatement();
      return this.finishNode(node, "WhileStatement");

    case _.tokTypes._with:
      this.next();
      node.object = this.parseParenExpression();
      node.body = this.parseStatement();
      return this.finishNode(node, "WithStatement");

    case _.tokTypes.braceL:
      return this.parseBlock();

    case _.tokTypes.semi:
      this.next();
      return this.finishNode(node, "EmptyStatement");

    case _.tokTypes._class:
      return this.parseClass(true);

    case _.tokTypes._import:
      return this.parseImport();

    case _.tokTypes._export:
      return this.parseExport();

    default:
      var expr = this.parseExpression();
      if (_parseutil.isDummy(expr)) {
        this.next();
        if (this.tok.type === _.tokTypes.eof) return this.finishNode(node, "EmptyStatement");
        return this.parseStatement();
      } else if (starttype === _.tokTypes.name && expr.type === "Identifier" && this.eat(_.tokTypes.colon)) {
        node.body = this.parseStatement();
        node.label = expr;
        return this.finishNode(node, "LabeledStatement");
      } else {
        node.expression = expr;
        this.semicolon();
        return this.finishNode(node, "ExpressionStatement");
      }
  }
};

lp.parseBlock = function () {
  var node = this.startNode();
  this.pushCx();
  this.expect(_.tokTypes.braceL);
  var blockIndent = this.curIndent,
      line = this.curLineStart;
  node.body = [];
  while (!this.closes(_.tokTypes.braceR, blockIndent, line, true)) node.body.push(this.parseStatement());
  this.popCx();
  this.eat(_.tokTypes.braceR);
  return this.finishNode(node, "BlockStatement");
};

lp.parseFor = function (node, init) {
  node.init = init;
  node.test = node.update = null;
  if (this.eat(_.tokTypes.semi) && this.tok.type !== _.tokTypes.semi) node.test = this.parseExpression();
  if (this.eat(_.tokTypes.semi) && this.tok.type !== _.tokTypes.parenR) node.update = this.parseExpression();
  this.popCx();
  this.expect(_.tokTypes.parenR);
  node.body = this.parseStatement();
  return this.finishNode(node, "ForStatement");
};

lp.parseForIn = function (node, init) {
  var type = this.tok.type === _.tokTypes._in ? "ForInStatement" : "ForOfStatement";
  this.next();
  node.left = init;
  node.right = this.parseExpression();
  this.popCx();
  this.expect(_.tokTypes.parenR);
  node.body = this.parseStatement();
  return this.finishNode(node, type);
};

lp.parseVar = function (noIn) {
  var node = this.startNode();
  node.kind = this.tok.type.keyword;
  this.next();
  node.declarations = [];
  do {
    var decl = this.startNode();
    decl.id = this.options.ecmaVersion >= 6 ? this.toAssignable(this.parseExprAtom(), true) : this.parseIdent();
    decl.init = this.eat(_.tokTypes.eq) ? this.parseMaybeAssign(noIn) : null;
    node.declarations.push(this.finishNode(decl, "VariableDeclarator"));
  } while (this.eat(_.tokTypes.comma));
  if (!node.declarations.length) {
    var decl = this.startNode();
    decl.id = this.dummyIdent();
    node.declarations.push(this.finishNode(decl, "VariableDeclarator"));
  }
  if (!noIn) this.semicolon();
  return this.finishNode(node, "VariableDeclaration");
};

lp.parseClass = function (isStatement) {
  var node = this.startNode();
  this.next();
  if (this.tok.type === _.tokTypes.name) node.id = this.parseIdent();else if (isStatement) node.id = this.dummyIdent();else node.id = null;
  node.superClass = this.eat(_.tokTypes._extends) ? this.parseExpression() : null;
  node.body = this.startNode();
  node.body.body = [];
  this.pushCx();
  var indent = this.curIndent + 1,
      line = this.curLineStart;
  this.eat(_.tokTypes.braceL);
  if (this.curIndent + 1 < indent) {
    indent = this.curIndent;line = this.curLineStart;
  }
  while (!this.closes(_.tokTypes.braceR, indent, line)) {
    if (this.semicolon()) continue;
    var method = this.startNode(),
        isGenerator = undefined;
    if (this.options.ecmaVersion >= 6) {
      method["static"] = false;
      isGenerator = this.eat(_.tokTypes.star);
    }
    this.parsePropertyName(method);
    if (_parseutil.isDummy(method.key)) {
      if (_parseutil.isDummy(this.parseMaybeAssign())) this.next();this.eat(_.tokTypes.comma);continue;
    }
    if (method.key.type === "Identifier" && !method.computed && method.key.name === "static" && (this.tok.type != _.tokTypes.parenL && this.tok.type != _.tokTypes.braceL)) {
      method["static"] = true;
      isGenerator = this.eat(_.tokTypes.star);
      this.parsePropertyName(method);
    } else {
      method["static"] = false;
    }
    if (this.options.ecmaVersion >= 5 && method.key.type === "Identifier" && !method.computed && (method.key.name === "get" || method.key.name === "set") && this.tok.type !== _.tokTypes.parenL && this.tok.type !== _.tokTypes.braceL) {
      method.kind = method.key.name;
      this.parsePropertyName(method);
      method.value = this.parseMethod(false);
    } else {
      if (!method.computed && !method["static"] && !isGenerator && (method.key.type === "Identifier" && method.key.name === "constructor" || method.key.type === "Literal" && method.key.value === "constructor")) {
        method.kind = "constructor";
      } else {
        method.kind = "method";
      }
      method.value = this.parseMethod(isGenerator);
    }
    node.body.body.push(this.finishNode(method, "MethodDefinition"));
  }
  this.popCx();
  if (!this.eat(_.tokTypes.braceR)) {
    // If there is no closing brace, make the node span to the start
    // of the next token (this is useful for Tern)
    this.last.end = this.tok.start;
    if (this.options.locations) this.last.loc.end = this.tok.loc.start;
  }
  this.semicolon();
  this.finishNode(node.body, "ClassBody");
  return this.finishNode(node, isStatement ? "ClassDeclaration" : "ClassExpression");
};

lp.parseFunction = function (node, isStatement) {
  this.initFunction(node);
  if (this.options.ecmaVersion >= 6) {
    node.generator = this.eat(_.tokTypes.star);
  }
  if (this.tok.type === _.tokTypes.name) node.id = this.parseIdent();else if (isStatement) node.id = this.dummyIdent();
  node.params = this.parseFunctionParams();
  node.body = this.parseBlock();
  return this.finishNode(node, isStatement ? "FunctionDeclaration" : "FunctionExpression");
};

lp.parseExport = function () {
  var node = this.startNode();
  this.next();
  if (this.eat(_.tokTypes.star)) {
    node.source = this.eatContextual("from") ? this.parseExprAtom() : null;
    return this.finishNode(node, "ExportAllDeclaration");
  }
  if (this.eat(_.tokTypes._default)) {
    var expr = this.parseMaybeAssign();
    if (expr.id) {
      switch (expr.type) {
        case "FunctionExpression":
          expr.type = "FunctionDeclaration";break;
        case "ClassExpression":
          expr.type = "ClassDeclaration";break;
      }
    }
    node.declaration = expr;
    this.semicolon();
    return this.finishNode(node, "ExportDefaultDeclaration");
  }
  if (this.tok.type.keyword) {
    node.declaration = this.parseStatement();
    node.specifiers = [];
    node.source = null;
  } else {
    node.declaration = null;
    node.specifiers = this.parseExportSpecifierList();
    node.source = this.eatContextual("from") ? this.parseExprAtom() : null;
    this.semicolon();
  }
  return this.finishNode(node, "ExportNamedDeclaration");
};

lp.parseImport = function () {
  var node = this.startNode();
  this.next();
  if (this.tok.type === _.tokTypes.string) {
    node.specifiers = [];
    node.source = this.parseExprAtom();
    node.kind = "";
  } else {
    var elt = undefined;
    if (this.tok.type === _.tokTypes.name && this.tok.value !== "from") {
      elt = this.startNode();
      elt.local = this.parseIdent();
      this.finishNode(elt, "ImportDefaultSpecifier");
      this.eat(_.tokTypes.comma);
    }
    node.specifiers = this.parseImportSpecifierList();
    node.source = this.eatContextual("from") ? this.parseExprAtom() : this.dummyString();
    if (elt) node.specifiers.unshift(elt);
  }
  this.semicolon();
  return this.finishNode(node, "ImportDeclaration");
};

lp.parseImportSpecifierList = function () {
  var elts = [];
  if (this.tok.type === _.tokTypes.star) {
    var elt = this.startNode();
    this.next();
    if (this.eatContextual("as")) elt.local = this.parseIdent();
    elts.push(this.finishNode(elt, "ImportNamespaceSpecifier"));
  } else {
    var indent = this.curIndent,
        line = this.curLineStart,
        continuedLine = this.nextLineStart;
    this.pushCx();
    this.eat(_.tokTypes.braceL);
    if (this.curLineStart > continuedLine) continuedLine = this.curLineStart;
    while (!this.closes(_.tokTypes.braceR, indent + (this.curLineStart <= continuedLine ? 1 : 0), line)) {
      var elt = this.startNode();
      if (this.eat(_.tokTypes.star)) {
        if (this.eatContextual("as")) elt.local = this.parseIdent();
        this.finishNode(elt, "ImportNamespaceSpecifier");
      } else {
        if (this.isContextual("from")) break;
        elt.imported = this.parseIdent();
        if (_parseutil.isDummy(elt.imported)) break;
        elt.local = this.eatContextual("as") ? this.parseIdent() : elt.imported;
        this.finishNode(elt, "ImportSpecifier");
      }
      elts.push(elt);
      this.eat(_.tokTypes.comma);
    }
    this.eat(_.tokTypes.braceR);
    this.popCx();
  }
  return elts;
};

lp.parseExportSpecifierList = function () {
  var elts = [];
  var indent = this.curIndent,
      line = this.curLineStart,
      continuedLine = this.nextLineStart;
  this.pushCx();
  this.eat(_.tokTypes.braceL);
  if (this.curLineStart > continuedLine) continuedLine = this.curLineStart;
  while (!this.closes(_.tokTypes.braceR, indent + (this.curLineStart <= continuedLine ? 1 : 0), line)) {
    if (this.isContextual("from")) break;
    var elt = this.startNode();
    elt.local = this.parseIdent();
    if (_parseutil.isDummy(elt.local)) break;
    elt.exported = this.eatContextual("as") ? this.parseIdent() : elt.local;
    this.finishNode(elt, "ExportSpecifier");
    elts.push(elt);
    this.eat(_.tokTypes.comma);
  }
  this.eat(_.tokTypes.braceR);
  this.popCx();
  return elts;
};

},{"..":1,"./parseutil":4,"./state":5}],7:[function(_dereq_,module,exports){
"use strict";

var _ = _dereq_("..");

var _state = _dereq_("./state");

var lp = _state.LooseParser.prototype;

function isSpace(ch) {
  return ch < 14 && ch > 8 || ch === 32 || ch === 160 || _.isNewLine(ch);
}

lp.next = function () {
  this.last = this.tok;
  if (this.ahead.length) this.tok = this.ahead.shift();else this.tok = this.readToken();

  if (this.tok.start >= this.nextLineStart) {
    while (this.tok.start >= this.nextLineStart) {
      this.curLineStart = this.nextLineStart;
      this.nextLineStart = this.lineEnd(this.curLineStart) + 1;
    }
    this.curIndent = this.indentationAfter(this.curLineStart);
  }
};

lp.readToken = function () {
  for (;;) {
    try {
      this.toks.next();
      if (this.toks.type === _.tokTypes.dot && this.input.substr(this.toks.end, 1) === "." && this.options.ecmaVersion >= 6) {
        this.toks.end++;
        this.toks.type = _.tokTypes.ellipsis;
      }
      return new _.Token(this.toks);
    } catch (e) {
      if (!(e instanceof SyntaxError)) throw e;

      // Try to skip some text, based on the error message, and then continue
      var msg = e.message,
          pos = e.raisedAt,
          replace = true;
      if (/unterminated/i.test(msg)) {
        pos = this.lineEnd(e.pos + 1);
        if (/string/.test(msg)) {
          replace = { start: e.pos, end: pos, type: _.tokTypes.string, value: this.input.slice(e.pos + 1, pos) };
        } else if (/regular expr/i.test(msg)) {
          var re = this.input.slice(e.pos, pos);
          try {
            re = new RegExp(re);
          } catch (e) {}
          replace = { start: e.pos, end: pos, type: _.tokTypes.regexp, value: re };
        } else if (/template/.test(msg)) {
          replace = { start: e.pos, end: pos,
            type: _.tokTypes.template,
            value: this.input.slice(e.pos, pos) };
        } else {
          replace = false;
        }
      } else if (/invalid (unicode|regexp|number)|expecting unicode|octal literal|is reserved|directly after number|expected number in radix/i.test(msg)) {
        while (pos < this.input.length && !isSpace(this.input.charCodeAt(pos))) ++pos;
      } else if (/character escape|expected hexadecimal/i.test(msg)) {
        while (pos < this.input.length) {
          var ch = this.input.charCodeAt(pos++);
          if (ch === 34 || ch === 39 || _.isNewLine(ch)) break;
        }
      } else if (/unexpected character/i.test(msg)) {
        pos++;
        replace = false;
      } else if (/regular expression/i.test(msg)) {
        replace = true;
      } else {
        throw e;
      }
      this.resetTo(pos);
      if (replace === true) replace = { start: pos, end: pos, type: _.tokTypes.name, value: "✖" };
      if (replace) {
        if (this.options.locations) replace.loc = new _.SourceLocation(this.toks, _.getLineInfo(this.input, replace.start), _.getLineInfo(this.input, replace.end));
        return replace;
      }
    }
  }
};

lp.resetTo = function (pos) {
  this.toks.pos = pos;
  var ch = this.input.charAt(pos - 1);
  this.toks.exprAllowed = !ch || /[\[\{\(,;:?\/*=+\-~!|&%^<>]/.test(ch) || /[enwfd]/.test(ch) && /\b(keywords|case|else|return|throw|new|in|(instance|type)of|delete|void)$/.test(this.input.slice(pos - 10, pos));

  if (this.options.locations) {
    this.toks.curLine = 1;
    this.toks.lineStart = _.lineBreakG.lastIndex = 0;
    var match = undefined;
    while ((match = _.lineBreakG.exec(this.input)) && match.index < pos) {
      ++this.toks.curLine;
      this.toks.lineStart = match.index + match[0].length;
    }
  }
};

lp.lookAhead = function (n) {
  while (n > this.ahead.length) this.ahead.push(this.readToken());
  return this.ahead[n - 1];
};

},{"..":1,"./state":5}]},{},[3])(3)
});
}).call(this,typeof global !== "undefined" ? global : typeof self !== "undefined" ? self : typeof window !== "undefined" ? window : {})

},{"./acorn":15}],17:[function(require,module,exports){
(function (global){
(function(f){if(typeof exports==="object"&&typeof module!=="undefined"){module.exports=f()}else if(typeof define==="function"&&define.amd){define([],f)}else{var g;if(typeof window!=="undefined"){g=window}else if(typeof global!=="undefined"){g=global}else if(typeof self!=="undefined"){g=self}else{g=this}(g.acorn || (g.acorn = {})).walk = f()}})(function(){var define,module,exports;return (function e(t,n,r){function s(o,u){if(!n[o]){if(!t[o]){var a=typeof require=="function"&&require;if(!u&&a)return a(o,!0);if(i)return i(o,!0);var f=new Error("Cannot find module '"+o+"'");throw f.code="MODULE_NOT_FOUND",f}var l=n[o]={exports:{}};t[o][0].call(l.exports,function(e){var n=t[o][1][e];return s(n?n:e)},l,l.exports,e,t,n,r)}return n[o].exports}var i=typeof require=="function"&&require;for(var o=0;o<r.length;o++)s(r[o]);return s})({1:[function(_dereq_,module,exports){
// AST walker module for Mozilla Parser API compatible trees

// A simple walk is one where you simply specify callbacks to be
// called on specific nodes. The last two arguments are optional. A
// simple use would be
//
//     walk.simple(myTree, {
//         Expression: function(node) { ... }
//     });
//
// to do something with all expressions. All Parser API node types
// can be used to identify node types, as well as Expression,
// Statement, and ScopeBody, which denote categories of nodes.
//
// The base argument can be used to pass a custom (recursive)
// walker, and state can be used to give this walked an initial
// state.

"use strict";

exports.__esModule = true;
exports.simple = simple;
exports.ancestor = ancestor;
exports.recursive = recursive;
exports.findNodeAt = findNodeAt;
exports.findNodeAround = findNodeAround;
exports.findNodeAfter = findNodeAfter;
exports.findNodeBefore = findNodeBefore;
exports.make = make;

function _classCallCheck(instance, Constructor) { if (!(instance instanceof Constructor)) { throw new TypeError("Cannot call a class as a function"); } }

function simple(node, visitors, base, state, override) {
  if (!base) base = exports.base;(function c(node, st, override) {
    var type = override || node.type,
        found = visitors[type];
    base[type](node, st, c);
    if (found) found(node, st);
  })(node, state, override);
}

// An ancestor walk builds up an array of ancestor nodes (including
// the current node) and passes them to the callback as the state parameter.

function ancestor(node, visitors, base, state) {
  if (!base) base = exports.base;
  if (!state) state = [];(function c(node, st, override) {
    var type = override || node.type,
        found = visitors[type];
    if (node != st[st.length - 1]) {
      st = st.slice();
      st.push(node);
    }
    base[type](node, st, c);
    if (found) found(node, st);
  })(node, state);
}

// A recursive walk is one where your functions override the default
// walkers. They can modify and replace the state parameter that's
// threaded through the walk, and can opt how and whether to walk
// their child nodes (by calling their third argument on these
// nodes).

function recursive(node, state, funcs, base, override) {
  var visitor = funcs ? exports.make(funcs, base) : base;(function c(node, st, override) {
    visitor[override || node.type](node, st, c);
  })(node, state, override);
}

function makeTest(test) {
  if (typeof test == "string") return function (type) {
    return type == test;
  };else if (!test) return function () {
    return true;
  };else return test;
}

var Found = function Found(node, state) {
  _classCallCheck(this, Found);

  this.node = node;this.state = state;
};

// Find a node with a given start, end, and type (all are optional,
// null can be used as wildcard). Returns a {node, state} object, or
// undefined when it doesn't find a matching node.

function findNodeAt(node, start, end, test, base, state) {
  test = makeTest(test);
  if (!base) base = exports.base;
  try {
    ;(function c(node, st, override) {
      var type = override || node.type;
      if ((start == null || node.start <= start) && (end == null || node.end >= end)) base[type](node, st, c);
      if ((start == null || node.start == start) && (end == null || node.end == end) && test(type, node)) throw new Found(node, st);
    })(node, state);
  } catch (e) {
    if (e instanceof Found) return e;
    throw e;
  }
}

// Find the innermost node of a given type that contains the given
// position. Interface similar to findNodeAt.

function findNodeAround(node, pos, test, base, state) {
  test = makeTest(test);
  if (!base) base = exports.base;
  try {
    ;(function c(node, st, override) {
      var type = override || node.type;
      if (node.start > pos || node.end < pos) return;
      base[type](node, st, c);
      if (test(type, node)) throw new Found(node, st);
    })(node, state);
  } catch (e) {
    if (e instanceof Found) return e;
    throw e;
  }
}

// Find the outermost matching node after a given position.

function findNodeAfter(node, pos, test, base, state) {
  test = makeTest(test);
  if (!base) base = exports.base;
  try {
    ;(function c(node, st, override) {
      if (node.end < pos) return;
      var type = override || node.type;
      if (node.start >= pos && test(type, node)) throw new Found(node, st);
      base[type](node, st, c);
    })(node, state);
  } catch (e) {
    if (e instanceof Found) return e;
    throw e;
  }
}

// Find the outermost matching node before a given position.

function findNodeBefore(node, pos, test, base, state) {
  test = makeTest(test);
  if (!base) base = exports.base;
  var max = undefined;(function c(node, st, override) {
    if (node.start > pos) return;
    var type = override || node.type;
    if (node.end <= pos && (!max || max.node.end < node.end) && test(type, node)) max = new Found(node, st);
    base[type](node, st, c);
  })(node, state);
  return max;
}

// Used to create a custom walker. Will fill in all missing node
// type properties with the defaults.

function make(funcs, base) {
  if (!base) base = exports.base;
  var visitor = {};
  for (var type in base) visitor[type] = base[type];
  for (var type in funcs) visitor[type] = funcs[type];
  return visitor;
}

function skipThrough(node, st, c) {
  c(node, st);
}
function ignore(_node, _st, _c) {}

// Node walkers.

var base = {};

exports.base = base;
base.Program = base.BlockStatement = function (node, st, c) {
  for (var i = 0; i < node.body.length; ++i) {
    c(node.body[i], st, "Statement");
  }
};
base.Statement = skipThrough;
base.EmptyStatement = ignore;
base.ExpressionStatement = base.ParenthesizedExpression = function (node, st, c) {
  return c(node.expression, st, "Expression");
};
base.IfStatement = function (node, st, c) {
  c(node.test, st, "Expression");
  c(node.consequent, st, "Statement");
  if (node.alternate) c(node.alternate, st, "Statement");
};
base.LabeledStatement = function (node, st, c) {
  return c(node.body, st, "Statement");
};
base.BreakStatement = base.ContinueStatement = ignore;
base.WithStatement = function (node, st, c) {
  c(node.object, st, "Expression");
  c(node.body, st, "Statement");
};
base.SwitchStatement = function (node, st, c) {
  c(node.discriminant, st, "Expression");
  for (var i = 0; i < node.cases.length; ++i) {
    var cs = node.cases[i];
    if (cs.test) c(cs.test, st, "Expression");
    for (var j = 0; j < cs.consequent.length; ++j) {
      c(cs.consequent[j], st, "Statement");
    }
  }
};
base.ReturnStatement = base.YieldExpression = function (node, st, c) {
  if (node.argument) c(node.argument, st, "Expression");
};
base.ThrowStatement = base.SpreadElement = function (node, st, c) {
  return c(node.argument, st, "Expression");
};
base.TryStatement = function (node, st, c) {
  c(node.block, st, "Statement");
  if (node.handler) {
    c(node.handler.param, st, "Pattern");
    c(node.handler.body, st, "ScopeBody");
  }
  if (node.finalizer) c(node.finalizer, st, "Statement");
};
base.WhileStatement = base.DoWhileStatement = function (node, st, c) {
  c(node.test, st, "Expression");
  c(node.body, st, "Statement");
};
base.ForStatement = function (node, st, c) {
  if (node.init) c(node.init, st, "ForInit");
  if (node.test) c(node.test, st, "Expression");
  if (node.update) c(node.update, st, "Expression");
  c(node.body, st, "Statement");
};
base.ForInStatement = base.ForOfStatement = function (node, st, c) {
  c(node.left, st, "ForInit");
  c(node.right, st, "Expression");
  c(node.body, st, "Statement");
};
base.ForInit = function (node, st, c) {
  if (node.type == "VariableDeclaration") c(node, st);else c(node, st, "Expression");
};
base.DebuggerStatement = ignore;

base.FunctionDeclaration = function (node, st, c) {
  return c(node, st, "Function");
};
base.VariableDeclaration = function (node, st, c) {
  for (var i = 0; i < node.declarations.length; ++i) {
    c(node.declarations[i], st);
  }
};
base.VariableDeclarator = function (node, st, c) {
  c(node.id, st, "Pattern");
  if (node.init) c(node.init, st, "Expression");
};

base.Function = function (node, st, c) {
  if (node.id) c(node.id, st, "Pattern");
  for (var i = 0; i < node.params.length; i++) {
    c(node.params[i], st, "Pattern");
  }c(node.body, st, node.expression ? "ScopeExpression" : "ScopeBody");
};
// FIXME drop these node types in next major version
// (They are awkward, and in ES6 every block can be a scope.)
base.ScopeBody = function (node, st, c) {
  return c(node, st, "Statement");
};
base.ScopeExpression = function (node, st, c) {
  return c(node, st, "Expression");
};

base.Pattern = function (node, st, c) {
  if (node.type == "Identifier") c(node, st, "VariablePattern");else if (node.type == "MemberExpression") c(node, st, "MemberPattern");else c(node, st);
};
base.VariablePattern = ignore;
base.MemberPattern = skipThrough;
base.RestElement = function (node, st, c) {
  return c(node.argument, st, "Pattern");
};
base.ArrayPattern = function (node, st, c) {
  for (var i = 0; i < node.elements.length; ++i) {
    var elt = node.elements[i];
    if (elt) c(elt, st, "Pattern");
  }
};
base.ObjectPattern = function (node, st, c) {
  for (var i = 0; i < node.properties.length; ++i) {
    c(node.properties[i].value, st, "Pattern");
  }
};

base.Expression = skipThrough;
base.ThisExpression = base.Super = base.MetaProperty = ignore;
base.ArrayExpression = function (node, st, c) {
  for (var i = 0; i < node.elements.length; ++i) {
    var elt = node.elements[i];
    if (elt) c(elt, st, "Expression");
  }
};
base.ObjectExpression = function (node, st, c) {
  for (var i = 0; i < node.properties.length; ++i) {
    c(node.properties[i], st);
  }
};
base.FunctionExpression = base.ArrowFunctionExpression = base.FunctionDeclaration;
base.SequenceExpression = base.TemplateLiteral = function (node, st, c) {
  for (var i = 0; i < node.expressions.length; ++i) {
    c(node.expressions[i], st, "Expression");
  }
};
base.UnaryExpression = base.UpdateExpression = function (node, st, c) {
  c(node.argument, st, "Expression");
};
base.BinaryExpression = base.LogicalExpression = function (node, st, c) {
  c(node.left, st, "Expression");
  c(node.right, st, "Expression");
};
base.AssignmentExpression = base.AssignmentPattern = function (node, st, c) {
  c(node.left, st, "Pattern");
  c(node.right, st, "Expression");
};
base.ConditionalExpression = function (node, st, c) {
  c(node.test, st, "Expression");
  c(node.consequent, st, "Expression");
  c(node.alternate, st, "Expression");
};
base.NewExpression = base.CallExpression = function (node, st, c) {
  c(node.callee, st, "Expression");
  if (node.arguments) for (var i = 0; i < node.arguments.length; ++i) {
    c(node.arguments[i], st, "Expression");
  }
};
base.MemberExpression = function (node, st, c) {
  c(node.object, st, "Expression");
  if (node.computed) c(node.property, st, "Expression");
};
base.ExportNamedDeclaration = base.ExportDefaultDeclaration = function (node, st, c) {
  if (node.declaration) c(node.declaration, st);
  if (node.source) c(node.source, st, "Expression");
};
base.ExportAllDeclaration = function (node, st, c) {
  c(node.source, st, "Expression");
};
base.ImportDeclaration = function (node, st, c) {
  for (var i = 0; i < node.specifiers.length; i++) {
    c(node.specifiers[i], st);
  }c(node.source, st, "Expression");
};
base.ImportSpecifier = base.ImportDefaultSpecifier = base.ImportNamespaceSpecifier = base.Identifier = base.Literal = ignore;

base.TaggedTemplateExpression = function (node, st, c) {
  c(node.tag, st, "Expression");
  c(node.quasi, st);
};
base.ClassDeclaration = base.ClassExpression = function (node, st, c) {
  return c(node, st, "Class");
};
base.Class = function (node, st, c) {
  if (node.id) c(node.id, st, "Pattern");
  if (node.superClass) c(node.superClass, st, "Expression");
  for (var i = 0; i < node.body.body.length; i++) {
    c(node.body.body[i], st);
  }
};
base.MethodDefinition = base.Property = function (node, st, c) {
  if (node.computed) c(node.key, st, "Expression");
  c(node.value, st, "Expression");
};
base.ComprehensionExpression = function (node, st, c) {
  for (var i = 0; i < node.blocks.length; i++) {
    c(node.blocks[i].right, st, "Expression");
  }c(node.body, st, "Expression");
};

},{}]},{},[1])(1)
});
}).call(this,typeof global !== "undefined" ? global : typeof self !== "undefined" ? self : typeof window !== "undefined" ? window : {})

},{}],18:[function(require,module,exports){
if (typeof Object.create === 'function') {
  // implementation from standard node.js 'util' module
  module.exports = function inherits(ctor, superCtor) {
    ctor.super_ = superCtor
    ctor.prototype = Object.create(superCtor.prototype, {
      constructor: {
        value: ctor,
        enumerable: false,
        writable: true,
        configurable: true
      }
    });
  };
} else {
  // old school shim for old browsers
  module.exports = function inherits(ctor, superCtor) {
    ctor.super_ = superCtor
    var TempCtor = function () {}
    TempCtor.prototype = superCtor.prototype
    ctor.prototype = new TempCtor()
    ctor.prototype.constructor = ctor
  }
}

},{}],19:[function(require,module,exports){
// shim for using process in browser

var process = module.exports = {};
var queue = [];
var draining = false;
var currentQueue;
var queueIndex = -1;

function cleanUpNextTick() {
    draining = false;
    if (currentQueue.length) {
        queue = currentQueue.concat(queue);
    } else {
        queueIndex = -1;
    }
    if (queue.length) {
        drainQueue();
    }
}

function drainQueue() {
    if (draining) {
        return;
    }
    var timeout = setTimeout(cleanUpNextTick);
    draining = true;

    var len = queue.length;
    while(len) {
        currentQueue = queue;
        queue = [];
        while (++queueIndex < len) {
            currentQueue[queueIndex].run();
        }
        queueIndex = -1;
        len = queue.length;
    }
    currentQueue = null;
    draining = false;
    clearTimeout(timeout);
}

process.nextTick = function (fun) {
    var args = new Array(arguments.length - 1);
    if (arguments.length > 1) {
        for (var i = 1; i < arguments.length; i++) {
            args[i - 1] = arguments[i];
        }
    }
    queue.push(new Item(fun, args));
    if (queue.length === 1 && !draining) {
        setTimeout(drainQueue, 0);
    }
};

// v8 likes predictible objects
function Item(fun, array) {
    this.fun = fun;
    this.array = array;
}
Item.prototype.run = function () {
    this.fun.apply(null, this.array);
};
process.title = 'browser';
process.browser = true;
process.env = {};
process.argv = [];
process.version = ''; // empty string to avoid regexp issues
process.versions = {};

function noop() {}

process.on = noop;
process.addListener = noop;
process.once = noop;
process.off = noop;
process.removeListener = noop;
process.removeAllListeners = noop;
process.emit = noop;

process.binding = function (name) {
    throw new Error('process.binding is not supported');
};

// TODO(shtylman)
process.cwd = function () { return '/' };
process.chdir = function (dir) {
    throw new Error('process.chdir is not supported');
};
process.umask = function() { return 0; };

},{}],20:[function(require,module,exports){
module.exports = function isBuffer(arg) {
  return arg && typeof arg === 'object'
    && typeof arg.copy === 'function'
    && typeof arg.fill === 'function'
    && typeof arg.readUInt8 === 'function';
}
},{}],21:[function(require,module,exports){
(function (process,global){
// Copyright Joyent, Inc. and other Node contributors.
//
// Permission is hereby granted, free of charge, to any person obtaining a
// copy of this software and associated documentation files (the
// "Software"), to deal in the Software without restriction, including
// without limitation the rights to use, copy, modify, merge, publish,
// distribute, sublicense, and/or sell copies of the Software, and to permit
// persons to whom the Software is furnished to do so, subject to the
// following conditions:
//
// The above copyright notice and this permission notice shall be included
// in all copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
// OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
// MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN
// NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
// DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR
// OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE
// USE OR OTHER DEALINGS IN THE SOFTWARE.

var formatRegExp = /%[sdj%]/g;
exports.format = function(f) {
  if (!isString(f)) {
    var objects = [];
    for (var i = 0; i < arguments.length; i++) {
      objects.push(inspect(arguments[i]));
    }
    return objects.join(' ');
  }

  var i = 1;
  var args = arguments;
  var len = args.length;
  var str = String(f).replace(formatRegExp, function(x) {
    if (x === '%%') return '%';
    if (i >= len) return x;
    switch (x) {
      case '%s': return String(args[i++]);
      case '%d': return Number(args[i++]);
      case '%j':
        try {
          return JSON.stringify(args[i++]);
        } catch (_) {
          return '[Circular]';
        }
      default:
        return x;
    }
  });
  for (var x = args[i]; i < len; x = args[++i]) {
    if (isNull(x) || !isObject(x)) {
      str += ' ' + x;
    } else {
      str += ' ' + inspect(x);
    }
  }
  return str;
};


// Mark that a method should not be used.
// Returns a modified function which warns once by default.
// If --no-deprecation is set, then it is a no-op.
exports.deprecate = function(fn, msg) {
  // Allow for deprecating things in the process of starting up.
  if (isUndefined(global.process)) {
    return function() {
      return exports.deprecate(fn, msg).apply(this, arguments);
    };
  }

  if (process.noDeprecation === true) {
    return fn;
  }

  var warned = false;
  function deprecated() {
    if (!warned) {
      if (process.throwDeprecation) {
        throw new Error(msg);
      } else if (process.traceDeprecation) {
        console.trace(msg);
      } else {
        console.error(msg);
      }
      warned = true;
    }
    return fn.apply(this, arguments);
  }

  return deprecated;
};


var debugs = {};
var debugEnviron;
exports.debuglog = function(set) {
  if (isUndefined(debugEnviron))
    debugEnviron = process.env.NODE_DEBUG || '';
  set = set.toUpperCase();
  if (!debugs[set]) {
    if (new RegExp('\\b' + set + '\\b', 'i').test(debugEnviron)) {
      var pid = process.pid;
      debugs[set] = function() {
        var msg = exports.format.apply(exports, arguments);
        console.error('%s %d: %s', set, pid, msg);
      };
    } else {
      debugs[set] = function() {};
    }
  }
  return debugs[set];
};


/**
 * Echos the value of a value. Trys to print the value out
 * in the best way possible given the different types.
 *
 * @param {Object} obj The object to print out.
 * @param {Object} opts Optional options object that alters the output.
 */
/* legacy: obj, showHidden, depth, colors*/
function inspect(obj, opts) {
  // default options
  var ctx = {
    seen: [],
    stylize: stylizeNoColor
  };
  // legacy...
  if (arguments.length >= 3) ctx.depth = arguments[2];
  if (arguments.length >= 4) ctx.colors = arguments[3];
  if (isBoolean(opts)) {
    // legacy...
    ctx.showHidden = opts;
  } else if (opts) {
    // got an "options" object
    exports._extend(ctx, opts);
  }
  // set default options
  if (isUndefined(ctx.showHidden)) ctx.showHidden = false;
  if (isUndefined(ctx.depth)) ctx.depth = 2;
  if (isUndefined(ctx.colors)) ctx.colors = false;
  if (isUndefined(ctx.customInspect)) ctx.customInspect = true;
  if (ctx.colors) ctx.stylize = stylizeWithColor;
  return formatValue(ctx, obj, ctx.depth);
}
exports.inspect = inspect;


// http://en.wikipedia.org/wiki/ANSI_escape_code#graphics
inspect.colors = {
  'bold' : [1, 22],
  'italic' : [3, 23],
  'underline' : [4, 24],
  'inverse' : [7, 27],
  'white' : [37, 39],
  'grey' : [90, 39],
  'black' : [30, 39],
  'blue' : [34, 39],
  'cyan' : [36, 39],
  'green' : [32, 39],
  'magenta' : [35, 39],
  'red' : [31, 39],
  'yellow' : [33, 39]
};

// Don't use 'blue' not visible on cmd.exe
inspect.styles = {
  'special': 'cyan',
  'number': 'yellow',
  'boolean': 'yellow',
  'undefined': 'grey',
  'null': 'bold',
  'string': 'green',
  'date': 'magenta',
  // "name": intentionally not styling
  'regexp': 'red'
};


function stylizeWithColor(str, styleType) {
  var style = inspect.styles[styleType];

  if (style) {
    return '\u001b[' + inspect.colors[style][0] + 'm' + str +
           '\u001b[' + inspect.colors[style][1] + 'm';
  } else {
    return str;
  }
}


function stylizeNoColor(str, styleType) {
  return str;
}


function arrayToHash(array) {
  var hash = {};

  array.forEach(function(val, idx) {
    hash[val] = true;
  });

  return hash;
}


function formatValue(ctx, value, recurseTimes) {
  // Provide a hook for user-specified inspect functions.
  // Check that value is an object with an inspect function on it
  if (ctx.customInspect &&
      value &&
      isFunction(value.inspect) &&
      // Filter out the util module, it's inspect function is special
      value.inspect !== exports.inspect &&
      // Also filter out any prototype objects using the circular check.
      !(value.constructor && value.constructor.prototype === value)) {
    var ret = value.inspect(recurseTimes, ctx);
    if (!isString(ret)) {
      ret = formatValue(ctx, ret, recurseTimes);
    }
    return ret;
  }

  // Primitive types cannot have properties
  var primitive = formatPrimitive(ctx, value);
  if (primitive) {
    return primitive;
  }

  // Look up the keys of the object.
  var keys = Object.keys(value);
  var visibleKeys = arrayToHash(keys);

  if (ctx.showHidden) {
    keys = Object.getOwnPropertyNames(value);
  }

  // IE doesn't make error fields non-enumerable
  // http://msdn.microsoft.com/en-us/library/ie/dww52sbt(v=vs.94).aspx
  if (isError(value)
      && (keys.indexOf('message') >= 0 || keys.indexOf('description') >= 0)) {
    return formatError(value);
  }

  // Some type of object without properties can be shortcutted.
  if (keys.length === 0) {
    if (isFunction(value)) {
      var name = value.name ? ': ' + value.name : '';
      return ctx.stylize('[Function' + name + ']', 'special');
    }
    if (isRegExp(value)) {
      return ctx.stylize(RegExp.prototype.toString.call(value), 'regexp');
    }
    if (isDate(value)) {
      return ctx.stylize(Date.prototype.toString.call(value), 'date');
    }
    if (isError(value)) {
      return formatError(value);
    }
  }

  var base = '', array = false, braces = ['{', '}'];

  // Make Array say that they are Array
  if (isArray(value)) {
    array = true;
    braces = ['[', ']'];
  }

  // Make functions say that they are functions
  if (isFunction(value)) {
    var n = value.name ? ': ' + value.name : '';
    base = ' [Function' + n + ']';
  }

  // Make RegExps say that they are RegExps
  if (isRegExp(value)) {
    base = ' ' + RegExp.prototype.toString.call(value);
  }

  // Make dates with properties first say the date
  if (isDate(value)) {
    base = ' ' + Date.prototype.toUTCString.call(value);
  }

  // Make error with message first say the error
  if (isError(value)) {
    base = ' ' + formatError(value);
  }

  if (keys.length === 0 && (!array || value.length == 0)) {
    return braces[0] + base + braces[1];
  }

  if (recurseTimes < 0) {
    if (isRegExp(value)) {
      return ctx.stylize(RegExp.prototype.toString.call(value), 'regexp');
    } else {
      return ctx.stylize('[Object]', 'special');
    }
  }

  ctx.seen.push(value);

  var output;
  if (array) {
    output = formatArray(ctx, value, recurseTimes, visibleKeys, keys);
  } else {
    output = keys.map(function(key) {
      return formatProperty(ctx, value, recurseTimes, visibleKeys, key, array);
    });
  }

  ctx.seen.pop();

  return reduceToSingleString(output, base, braces);
}


function formatPrimitive(ctx, value) {
  if (isUndefined(value))
    return ctx.stylize('undefined', 'undefined');
  if (isString(value)) {
    var simple = '\'' + JSON.stringify(value).replace(/^"|"$/g, '')
                                             .replace(/'/g, "\\'")
                                             .replace(/\\"/g, '"') + '\'';
    return ctx.stylize(simple, 'string');
  }
  if (isNumber(value))
    return ctx.stylize('' + value, 'number');
  if (isBoolean(value))
    return ctx.stylize('' + value, 'boolean');
  // For some reason typeof null is "object", so special case here.
  if (isNull(value))
    return ctx.stylize('null', 'null');
}


function formatError(value) {
  return '[' + Error.prototype.toString.call(value) + ']';
}


function formatArray(ctx, value, recurseTimes, visibleKeys, keys) {
  var output = [];
  for (var i = 0, l = value.length; i < l; ++i) {
    if (hasOwnProperty(value, String(i))) {
      output.push(formatProperty(ctx, value, recurseTimes, visibleKeys,
          String(i), true));
    } else {
      output.push('');
    }
  }
  keys.forEach(function(key) {
    if (!key.match(/^\d+$/)) {
      output.push(formatProperty(ctx, value, recurseTimes, visibleKeys,
          key, true));
    }
  });
  return output;
}


function formatProperty(ctx, value, recurseTimes, visibleKeys, key, array) {
  var name, str, desc;
  desc = Object.getOwnPropertyDescriptor(value, key) || { value: value[key] };
  if (desc.get) {
    if (desc.set) {
      str = ctx.stylize('[Getter/Setter]', 'special');
    } else {
      str = ctx.stylize('[Getter]', 'special');
    }
  } else {
    if (desc.set) {
      str = ctx.stylize('[Setter]', 'special');
    }
  }
  if (!hasOwnProperty(visibleKeys, key)) {
    name = '[' + key + ']';
  }
  if (!str) {
    if (ctx.seen.indexOf(desc.value) < 0) {
      if (isNull(recurseTimes)) {
        str = formatValue(ctx, desc.value, null);
      } else {
        str = formatValue(ctx, desc.value, recurseTimes - 1);
      }
      if (str.indexOf('\n') > -1) {
        if (array) {
          str = str.split('\n').map(function(line) {
            return '  ' + line;
          }).join('\n').substr(2);
        } else {
          str = '\n' + str.split('\n').map(function(line) {
            return '   ' + line;
          }).join('\n');
        }
      }
    } else {
      str = ctx.stylize('[Circular]', 'special');
    }
  }
  if (isUndefined(name)) {
    if (array && key.match(/^\d+$/)) {
      return str;
    }
    name = JSON.stringify('' + key);
    if (name.match(/^"([a-zA-Z_][a-zA-Z_0-9]*)"$/)) {
      name = name.substr(1, name.length - 2);
      name = ctx.stylize(name, 'name');
    } else {
      name = name.replace(/'/g, "\\'")
                 .replace(/\\"/g, '"')
                 .replace(/(^"|"$)/g, "'");
      name = ctx.stylize(name, 'string');
    }
  }

  return name + ': ' + str;
}


function reduceToSingleString(output, base, braces) {
  var numLinesEst = 0;
  var length = output.reduce(function(prev, cur) {
    numLinesEst++;
    if (cur.indexOf('\n') >= 0) numLinesEst++;
    return prev + cur.replace(/\u001b\[\d\d?m/g, '').length + 1;
  }, 0);

  if (length > 60) {
    return braces[0] +
           (base === '' ? '' : base + '\n ') +
           ' ' +
           output.join(',\n  ') +
           ' ' +
           braces[1];
  }

  return braces[0] + base + ' ' + output.join(', ') + ' ' + braces[1];
}


// NOTE: These type checking functions intentionally don't use `instanceof`
// because it is fragile and can be easily faked with `Object.create()`.
function isArray(ar) {
  return Array.isArray(ar);
}
exports.isArray = isArray;

function isBoolean(arg) {
  return typeof arg === 'boolean';
}
exports.isBoolean = isBoolean;

function isNull(arg) {
  return arg === null;
}
exports.isNull = isNull;

function isNullOrUndefined(arg) {
  return arg == null;
}
exports.isNullOrUndefined = isNullOrUndefined;

function isNumber(arg) {
  return typeof arg === 'number';
}
exports.isNumber = isNumber;

function isString(arg) {
  return typeof arg === 'string';
}
exports.isString = isString;

function isSymbol(arg) {
  return typeof arg === 'symbol';
}
exports.isSymbol = isSymbol;

function isUndefined(arg) {
  return arg === void 0;
}
exports.isUndefined = isUndefined;

function isRegExp(re) {
  return isObject(re) && objectToString(re) === '[object RegExp]';
}
exports.isRegExp = isRegExp;

function isObject(arg) {
  return typeof arg === 'object' && arg !== null;
}
exports.isObject = isObject;

function isDate(d) {
  return isObject(d) && objectToString(d) === '[object Date]';
}
exports.isDate = isDate;

function isError(e) {
  return isObject(e) &&
      (objectToString(e) === '[object Error]' || e instanceof Error);
}
exports.isError = isError;

function isFunction(arg) {
  return typeof arg === 'function';
}
exports.isFunction = isFunction;

function isPrimitive(arg) {
  return arg === null ||
         typeof arg === 'boolean' ||
         typeof arg === 'number' ||
         typeof arg === 'string' ||
         typeof arg === 'symbol' ||  // ES6 symbol
         typeof arg === 'undefined';
}
exports.isPrimitive = isPrimitive;

exports.isBuffer = require('./support/isBuffer');

function objectToString(o) {
  return Object.prototype.toString.call(o);
}


function pad(n) {
  return n < 10 ? '0' + n.toString(10) : n.toString(10);
}


var months = ['Jan', 'Feb', 'Mar', 'Apr', 'May', 'Jun', 'Jul', 'Aug', 'Sep',
              'Oct', 'Nov', 'Dec'];

// 26 Feb 16:19:34
function timestamp() {
  var d = new Date();
  var time = [pad(d.getHours()),
              pad(d.getMinutes()),
              pad(d.getSeconds())].join(':');
  return [d.getDate(), months[d.getMonth()], time].join(' ');
}


// log is just a thin wrapper to console.log that prepends a timestamp
exports.log = function() {
  console.log('%s - %s', timestamp(), exports.format.apply(exports, arguments));
};


/**
 * Inherit the prototype methods from one constructor into another.
 *
 * The Function.prototype.inherits from lang.js rewritten as a standalone
 * function (not on Function.prototype). NOTE: If this file is to be loaded
 * during bootstrapping this function needs to be rewritten using some native
 * functions as prototype setup using normal JavaScript does not work as
 * expected during bootstrapping (see mirror.js in r114903).
 *
 * @param {function} ctor Constructor function which needs to inherit the
 *     prototype.
 * @param {function} superCtor Constructor function to inherit prototype from.
 */
exports.inherits = require('inherits');

exports._extend = function(origin, add) {
  // Don't do anything if add isn't an object
  if (!add || !isObject(add)) return origin;

  var keys = Object.keys(add);
  var i = keys.length;
  while (i--) {
    origin[keys[i]] = add[keys[i]];
  }
  return origin;
};

function hasOwnProperty(obj, prop) {
  return Object.prototype.hasOwnProperty.call(obj, prop);
}

}).call(this,require('_process'),typeof global !== "undefined" ? global : typeof self !== "undefined" ? self : typeof window !== "undefined" ? window : {})

},{"./support/isBuffer":20,"_process":19,"inherits":18}]},{},[9])(9)
});
//# sourceMappingURL=data:application/json;charset:utf-8;base64,eyJ2ZXJzaW9uIjozLCJzb3VyY2VzIjpbIm5vZGVfbW9kdWxlcy9icm93c2VyaWZ5L25vZGVfbW9kdWxlcy9icm93c2VyLXBhY2svX3ByZWx1ZGUuanMiLCIvaG9tZS9zd2tpbS9XZWJzdG9ybVByb2plY3RzL2NhbGNpdW0vZGVmYXVsdE9wdGlvbi5qcyIsIi9ob21lL3N3a2ltL1dlYnN0b3JtUHJvamVjdHMvY2FsY2l1bS9saWIvY29uc3RyYWludC9jR2VuLmpzIiwiL2hvbWUvc3draW0vV2Vic3Rvcm1Qcm9qZWN0cy9jYWxjaXVtL2xpYi9jb25zdHJhaW50L2NvbnN0cmFpbnRzLmpzIiwiL2hvbWUvc3draW0vV2Vic3Rvcm1Qcm9qZWN0cy9jYWxjaXVtL2xpYi9kb21haW5zL2NvbnRleHQuanMiLCIvaG9tZS9zd2tpbS9XZWJzdG9ybVByb2plY3RzL2NhbGNpdW0vbGliL2RvbWFpbnMvc3RhdHVzLmpzIiwiL2hvbWUvc3draW0vV2Vic3Rvcm1Qcm9qZWN0cy9jYWxjaXVtL2xpYi9kb21haW5zL3R5cGVzLmpzIiwiL2hvbWUvc3draW0vV2Vic3Rvcm1Qcm9qZWN0cy9jYWxjaXVtL2xpYi9nZXRUeXBlRGF0YS5qcyIsIi9ob21lL3N3a2ltL1dlYnN0b3JtUHJvamVjdHMvY2FsY2l1bS9saWIvaGVscGVyLmpzIiwiL2hvbWUvc3draW0vV2Vic3Rvcm1Qcm9qZWN0cy9jYWxjaXVtL2xpYi9pbmZlci5qcyIsIi9ob21lL3N3a2ltL1dlYnN0b3JtUHJvamVjdHMvY2FsY2l1bS9saWIvcmV0T2NjdXIuanMiLCIvaG9tZS9zd2tpbS9XZWJzdG9ybVByb2plY3RzL2NhbGNpdW0vbGliL3RoaXNPY2N1ci5qcyIsIi9ob21lL3N3a2ltL1dlYnN0b3JtUHJvamVjdHMvY2FsY2l1bS9saWIvdXRpbC9teVdhbGtlci5qcyIsIi9ob21lL3N3a2ltL1dlYnN0b3JtUHJvamVjdHMvY2FsY2l1bS9saWIvdmFyQmxvY2suanMiLCIvaG9tZS9zd2tpbS9XZWJzdG9ybVByb2plY3RzL2NhbGNpdW0vbGliL3ZhcnJlZnMuanMiLCJub2RlX21vZHVsZXMvYWNvcm4vZGlzdC9hY29ybi5qcyIsIm5vZGVfbW9kdWxlcy9hY29ybi9kaXN0L2Fjb3JuX2xvb3NlLmpzIiwibm9kZV9tb2R1bGVzL2Fjb3JuL2Rpc3Qvd2Fsay5qcyIsIm5vZGVfbW9kdWxlcy9icm93c2VyaWZ5L25vZGVfbW9kdWxlcy9pbmhlcml0cy9pbmhlcml0c19icm93c2VyLmpzIiwibm9kZV9tb2R1bGVzL2Jyb3dzZXJpZnkvbm9kZV9tb2R1bGVzL3Byb2Nlc3MvYnJvd3Nlci5qcyIsIm5vZGVfbW9kdWxlcy9icm93c2VyaWZ5L25vZGVfbW9kdWxlcy91dGlsL3N1cHBvcnQvaXNCdWZmZXJCcm93c2VyLmpzIiwibm9kZV9tb2R1bGVzL2Jyb3dzZXJpZnkvbm9kZV9tb2R1bGVzL3V0aWwvdXRpbC5qcyJdLCJuYW1lcyI6W10sIm1hcHBpbmdzIjoiQUFBQTs7OztBQ0FPLElBQU0sT0FBTyxHQUFHO0FBQ25CLGVBQVcsRUFBRTtBQUNULG1CQUFXLEVBQUUsQ0FBQzs7Ozs7QUFLZCxrQkFBVSxFQUFFLFFBQVE7S0FDdkI7Ozs7QUFJRCxtQkFBZSxFQUFFLElBQUk7OztBQUdyQix3QkFBb0IsRUFBRTtBQUNsQixpQkFBUyxFQUFFLENBQUM7QUFDWiwyQkFBbUIsRUFBRSw2QkFBVSxFQUFFLEVBQUU7QUFDL0IsbUJBQU8sQ0FBQyxDQUFDO1NBQ1o7S0FDSjtDQUNKLENBQUM7Ozs7Ozs7OztBQ2hCRixZQUFZLENBQUM7Ozs7Ozs7NEJBQ1Usa0JBQWtCOztJQUE3QixLQUFLOzs0QkFDUyxrQkFBa0I7O0lBQWhDLFFBQVE7OzhCQUNDLG9CQUFvQjs7SUFBN0IsR0FBRzs7QUFDZixJQUFNLElBQUksR0FBRyxPQUFPLENBQUMsaUJBQWlCLENBQUMsQ0FBQztBQUN4QyxJQUFNLElBQUksR0FBRyxPQUFPLENBQUMsZUFBZSxDQUFDLENBQUM7OztBQUd0QyxTQUFTLFVBQVUsQ0FBQyxJQUFJLEVBQUU7QUFDdEIsUUFBTSxJQUFJLEdBQUcsSUFBSSxDQUFDLFFBQVEsQ0FBQztBQUMz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QUcsR0FBRyxJQUFJLEdBQUcsRUFBRSxDQUFDO0FBQ3RCLFlBQUksRUFBRSxFQUFFLEVBQUUsQ0FBQyxPQUFPLENBQUMsVUFBQSxDQUFDO21CQUFJLEdBQUcsQ0FBQyxHQUFHLENBQUMsQ0FBQyxDQUFDO1NBQUEsQ0FBQyxDQUFDO0FBQ3BDLFlBQUksRUFBRSxFQUFFLEVBQUUsQ0FBQyxPQUFPLENBQUMsVUFBQSxDQUFDO21CQUFJLEdBQUcsQ0FBQyxHQUFHLENBQUMsQ0FBQyxDQUFDO1NBQUEsQ0FBQyxDQUFDO0FBQ3BDLGVBQU8sR0FBRyxDQUFDO0tBQ2Q7O0FBRUQsUUFBSSxFQUFFLEVBQUUsRUFBRSxDQUFDLE9BQU8sQ0FBQyxVQUFDLEVBQUUsRUFBRSxDQUFDO2VBQUssR0FBRyxDQUFDLEdBQUcsQ0FBQyxDQUFDLEVBQUUsRUFBRSxDQUFDO0tBQUEsQ0FBQyxDQUFDO0FBQzlDLFFBQUksRUFBRSxFQUFFLEVBQUUsQ0FBQyxPQUFPLENBQUMsVUFBQyxFQUFFLEVBQUUsQ0FBQztlQUFLLEdBQUcsQ0FBQyxHQUFHLENBQUMsQ0FBQyxFQUFFLFFBQVEsQ0FBQyxHQUFHLENBQUMsR0FBRyxDQUFDLENBQUMsQ0FBQyxFQUFFLEVBQUUsQ0FBQyxHQUFHLENBQUMsQ0FBQyxDQUFDLENBQUMsQ0FBQztLQUFBLENBQUMsQ0FBQztBQUMzRSxXQUFPLEdBQUcsQ0FBQztDQUNkOztBQUVELFNBQVMsdUJBQXVCLENBQUMsRUFBRSxFQUFFLEVBQUUsRUFBRTtBQUNyQyxRQUFNLEdBQUcsR0FBRyxJQUFJLEdBQUcsRUFBRSxDQUFDO0FBQ3RCLE1BQUUsQ0FBQyxPQUFPLENBQUMsVUFBQyxFQUFFLEVBQUUsQ0FBQztlQUFLLEdBQUcsQ0FBQyxHQUFHLENBQUMsQ0FBQyxFQUFFLEVBQUUsQ0FBQztLQUFBLENBQUMsQ0FBQztBQUN0QyxNQUFFLENBQUMsT0FBTyxDQUFDLFVBQUMsRUFBRSxFQUFFLENBQUMsRUFBSztBQUNsQixZQUFJLENBQUMsR0FBRyxDQUFDLEdBQUcsQ0FBQyxDQUFDLENBQUMsRUFBRSxHQUFHLENB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QTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTs7Ozs7QUMvdUdBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBOzs7OztBQzl2Q0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7Ozs7QUN2WEE7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBOztBQ3ZCQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTs7QUMxRkE7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBOzs7QUNMQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBIiwiZmlsZSI6ImdlbmVyYXRlZC5qcyIsInNvdXJjZVJvb3QiOiIiLCJzb3VyY2VzQ29udGVudCI6WyIoZnVuY3Rpb24gZSh0LG4scil7ZnVuY3Rpb24gcyhvLHUpe2lmKCFuW29dKXtpZighdFtvXSl7dmFyIGE9dHlwZW9mIHJlcXVpcmU9PVwiZnVuY3Rpb25cIiYmcmVxdWlyZTtpZighdSYmYSlyZXR1cm4gYShvLCEwKTtpZihpKXJldHVybiBpKG8sITApO3ZhciBmPW5ldyBFcnJvcihcIkNhbm5vdCBmaW5kIG1vZHVsZSAnXCIrbytcIidcIik7dGhyb3cgZi5jb2RlPVwiTU9EVUxFX05PVF9GT1VORFwiLGZ9dmFyIGw9bltvXT17ZXhwb3J0czp7fX07dFtvXVswXS5jYWxsKGwuZXhwb3J0cyxmdW5jdGlvbihlKXt2YXIgbj10W29dWzFdW2VdO3JldHVybiBzKG4/bjplKX0sbCxsLmV4cG9ydHMsZSx0LG4scil9cmV0dXJuIG5bb10uZXhwb3J0c312YXIgaT10eXBlb2YgcmVxdWlyZT09XCJmdW5jdGlvblwiJiZyZXF1aXJlO2Zvcih2YXIgbz0wO288ci5sZW5ndGg7bysrKXMocltvXSk7cmV0dXJuIHN9KSIsImV4cG9ydCBjb25zdCBvcHRpb25zID0ge1xuICAgIGFjb3JuT3B0aW9uOiB7XG4gICAgICAgIGVjbWFWZXJzaW9uOiA2LFxuICAgICAgICAvLyBzb3VyY2VUeXBlOiAnc2NyaXB0JyBvciAnbW9kdWxlJ1xuICAgICAgICAvLyAnbW9kdWxlJyBpcyB1c2VkIGZvciBFUzYgbW9kdWxlcyBhbmRcbiAgICAgICAgLy8gJ3VzZSBzdHJpY3QnIGFzc3VtZWQgZm9yIHRob3NlIG1vZHVsZXMuXG4gICAgICAgIC8vIFRoaXMgb3B0aW9uIGlzIGFsc28gdXNlZCBieSB0aGUgYW5hbHl6ZXIuXG4gICAgICAgIHNvdXJjZVR5cGU6ICdzY3JpcHQnXG4gICAgfSxcbiAgICAvLyBBdCB0aGUgc3RhcnQgb2YgcHJvZ3JhbSBhbmQgZWFjaCBmdW5jdGlvbixcbiAgICAvLyBjaGVjayAndXNlIHN0cmljdCdcbiAgICAvLyBtYXliZSB3ZSBkbyBub3QgbmVlZCB0aGlzIG9wdGlvblxuICAgIGRldGVjdFVzZVN0cmljdDogdHJ1ZSxcblxuICAgIC8vIGNvbnRleHQgaW5zZW5zaXRpdmVcbiAgICBzZW5zaXRpdml0eVBhcmFtZXRlcjoge1xuICAgICAgICBtYXhEZXB0aEs6IDAsXG4gICAgICAgIGNvbnRleHRMZW5ndGhPZkZ1bmM6IGZ1bmN0aW9uIChmbikge1xuICAgICAgICAgICAgcmV0dXJuIDA7XG4gICAgICAgIH1cbiAgICB9XG59O1xuIiwiLyoqXG4gKiBAZmlsZSBHZW5lcmF0ZXMgY29uc3RyYWludHMgZnJvbSBBU1RzXG4gKiBAYXV0aG9yIHNld29uMzI2LmtpbUBzYW1zdW5nLmNvbVxuICovXG5cbid1c2Ugc3RyaWN0JztcbmltcG9ydCAqIGFzIHR5cGVzIGZyb20gJy4uL2RvbWFpbnMvdHlwZXMnXG5pbXBvcnQgKiBhcyBteVdhbGtlciBmcm9tICcuLi91dGlsL215V2Fsa2VyJ1xuaW1wb3J0ICogYXMgY3NjIGZyb20gJy4uL2RvbWFpbnMvY29udGV4dCdcbmNvbnN0IHdhbGsgPSByZXF1aXJlKCdhY29ybi9kaXN0L3dhbGsnKTtcbmNvbnN0IGNzdHIgPSByZXF1aXJlKCcuL2NvbnN0cmFpbnRzJyk7XG5cbi8vIHJldHVybnMgW2FjY2VzcyB0eXBlLCBwcm9wIHZhbHVlXVxuZnVuY3Rpb24gcHJvcEFjY2Vzcyhub2RlKSB7XG4gICAgY29uc3QgcHJvcCA9IG5vZGUucHJvcGVydHk7XG4gICAgaWYgKHByb3AudHlwZSA9PT0gJ0lkZW50aWZpZXInICYmIG15V2Fsa2VyLmlzRHVtbXlJZE5vZGUobm9kZS5wcm9wZXJ0eSkpIHtcbiAgICAgICAgcmV0dXJuIFsnZHVtbXlQcm9wZXJ0eSddXG4gICAgfVxuICAgIGlmICghbm9kZS5jb21wdXRlZCkge1xuICAgICAgICByZXR1cm4gWydkb3RBY2Nlc3MnLCBwcm9wLm5hbWVdO1xuICAgIH1cbiAgICBpZiAocHJvcC50eXBlID09PSAnTGl0ZXJhbCcpIHtcbiAgICAgICAgaWYgKHR5cGVvZiBwcm9wLnZhbHVlID09PSAnc3RyaW5nJylcbiAgICAgICAgICAgIHJldHVybiBbJ3N0cmluZ0xpdGVyYWwnLCBwcm9wLnZhbHVlXTtcbiAgICAgICAgaWYgKHR5cGVvZiBwcm9wLnZhbHVlID09PSAnbnVtYmVyJylcbiAgICAgICAgICAgIC8vIGNvbnZlcnQgbnVtYmVyIHRvIHN0cmluZ1xuICAgICAgICAgICAgcmV0dXJuIFsnbnVtYmVyTGl0ZXJhbCcsIHByb3AudmFsdWUgKyAnJ107XG4gICAgfVxuICAgIHJldHVybiBbJ2NvbXB1dGVkJywgbnVsbF07XG59XG5cbmZ1bmN0aW9uIHVub3BSZXN1bHRUeXBlKG9wKSB7XG4gICAgc3dpdGNoIChvcCkge1xuICAgICAgICBjYXNlICcrJzogY2FzZSAnLSc6IGNhc2UgJ34nOlxuICAgICAgICAgICAgcmV0dXJuIHR5cGVzLlByaW1OdW1iZXI7XG4gICAgICAgIGNhc2UgJyEnOlxuICAgICAgICAgICAgcmV0dXJuIHR5cGVzLlByaW1Cb29sZWFuO1xuICAgICAgICBjYXNlICd0eXBlb2YnOlxuICAgICAgICAgICAgcmV0dXJuIHR5cGVzLlByaW1TdHJpbmc7XG4gICAgICAgIGNhc2UgJ3ZvaWQnOiBjYXNlICdkZWxldGUnOlxuICAgICAgICAgICAgcmV0dXJuIG51bGw7XG4gICAgfVxufVxuXG5mdW5jdGlvbiBiaW5vcElzQm9vbGVhbihvcCkge1xuICAgIHN3aXRjaCAob3ApIHtcbiAgICAgICAgY2FzZSAnPT0nOiBjYXNlICchPSc6IGNhc2UgJz09PSc6IGNhc2UgJyE9PSc6XG4gICAgICAgIGNhc2UgJzwnOiBjYXNlICc+JzogY2FzZSAnPj0nOiBjYXNlICc8PSc6XG4gICAgICAgIGNhc2UgJ2luJzogY2FzZSAnaW5zdGFuY2VvZic6XG4gICAgICAgICAgICByZXR1cm4gdHJ1ZTtcbiAgICB9XG4gICAgcmV0dXJuIGZhbHNlO1xufVxuXG4vLyBUbyBwcmV2ZW50IHJlY3Vyc2lvbixcbi8vIHdlIHJlbWVtYmVyIHRoZSBzdGF0dXMgdXNlZCBpbiBhZGRDb25zdHJhaW50c1xuY29uc3QgdmlzaXRlZFN0YXR1cyA9IFtdO1xuXG5sZXQgcnRDWDtcbmV4cG9ydCBsZXQgY29ubmVjdFBhdHRlcm47XG5cbmV4cG9ydCBmdW5jdGlvbiBnZXRSZXN0QVZhbChub2RlLCBjdXJTdGF0dXMpIHtcbiAgICBpZiAobm9kZS50eXBlICE9PSBcIlJlc3RFbGVtZW50XCIpIHRocm93IG5ldyBFcnJvcignU2hvdWxkIGJlIFJlc3RFbGVtZW50Jyk7XG4gICAgaWYgKCFub2RlLnJlc3RBcnJheU1hcCkge1xuICAgICAgICBub2RlLnJlc3RBcnJheU1hcCA9IG5ldyBNYXAoKTtcbiAgICB9XG4gICAgbGV0IHJlc3RBVmFsO1xuICAgIGlmIChub2RlLnJlc3RBcnJheU1hcC5oYXMoY3VyU3RhdHVzLmRlbHRhKSkge1xuICAgICAgICByZXN0QVZhbCA9IG5vZGUucmVzdEFycmF5TWFwLmdldChjdXJTdGF0dXMuZGVsdGEpO1xuICAgIH0gZWxzZSB7XG4gICAgICAgIHJlc3RBVmFsID0gbmV3IHR5cGVzLkFWYWwoXG4gICAgICAgICAgICBuZXcgdHlwZXMuQXJyVHlwZShuZXcgdHlwZXMuQVZhbChydENYLnByb3Rvcy5BcnJheSkpKTtcbiAgICAgICAgbm9kZS5yZXN0QXJyYXlNYXAuc2V0KGN1clN0YXR1cy5kZWx0YSwgcmVzdEFWYWwpO1xuICAgIH1cbiAgICByZXR1cm4gcmVzdEFWYWw7XG59XG5cbi8qKlxuICogR2VuZXJhdGUgY29uc3RyYWludHMuXG4gKiBUaGlzIGZ1bmN0aW9uIHJldHVybnMgYHRydWVgIHdoZW4gaXQgYWN0dWFsbHkgYWRkZWQgY29uc3RyYWludHMuXG4gKiBAcGFyYW0gYXN0Tm9kZVxuICogQHBhcmFtIGluaXRTdGF0dXNcbiAqIEBwYXJhbSBuZXdSdENYXG4gKiBAcmV0dXJuIHtib29sZWFufVxuICovXG5leHBvcnQgZnVuY3Rpb24gYWRkQ29uc3RyYWludHMoYXN0Tm9kZSwgaW5pdFN0YXR1cywgbmV3UnRDWCkge1xuXG4gICAgLy8gc2V0IHJ0Q1hcbiAgICBydENYID0gbmV3UnRDWCB8fCBydENYO1xuICAgIGNvbnN0IMSIID0gcnRDWC7EiDtcblxuICAgIC8vIENoZWNrIHdoZXRoZXIgd2UgaGF2ZSBwcm9jZXNzZWQgJ2luaXRTdGF0dXMnIGJlZm9yZVxuICAgIGZvciAobGV0IGk9MDsgaSA8IHZpc2l0ZWRTdGF0dXMubGVuZ3RoOyBpKyspIHtcbiAgICAgICAgaWYgKGluaXRTdGF0dXMuZXF1YWxzKHZpc2l0ZWRTdGF0dXNbaV0pKSB7XG4gICAgICAgICAgICAgLy8gSWYgc28sIGRvIG5vdGhpbmdcbiAgICAgICAgICAgICAvLyBzaWduaWZ5aW5nIHdlIGRpZG4ndCBhZGQgY29uc3RyYWludHNcbiAgICAgICAgICAgICByZXR1cm4gZmFsc2U7XG4gICAgICAgICB9XG4gICAgfVxuICAgIC8vIElmIHRoZSBpbml0U3RhdHVzIGlzIG5ldywgcHVzaCBpdC5cbiAgICAvLyBXZSBkbyBub3QgcmVjb3JkIGFzdCBzaW5jZSBhc3Qgbm9kZSBkZXBlbmRzIG9uIHRoZSBzdGF0dXNcbiAgICB2aXNpdGVkU3RhdHVzLnB1c2goaW5pdFN0YXR1cyk7XG5cbiAgICBmdW5jdGlvbiByZWFkTWVtYmVyKG5vZGUsIGN1clN0YXR1cywgYykge1xuICAgICAgICBjb25zdCByZXQgPSDEiC5nZXQobm9kZSwgY3VyU3RhdHVzLmRlbHRhKTtcbiAgICAgICAgY29uc3Qgb2JqQVZhbCA9IGMobm9kZS5vYmplY3QsIGN1clN0YXR1cywgdW5kZWZpbmVkKTtcbiAgICAgICAgaWYgKG5vZGUucHJvcGVydHkudHlwZSAhPT0gJ0lkZW50aWZpZXInKSB7XG4gICAgICAgICAgICAvLyByZXR1cm4gZnJvbSBwcm9wZXJ0eSBpcyBpZ25vcmVkXG4gICAgICAgICAgICBjKG5vZGUucHJvcGVydHksIGN1clN0YXR1cywgdW5kZWZpbmVkKTtcbiAgICAgICAgfVxuICAgICAgICBjb25zdCBbYWNjVHlwZSwgcHJvcE5hbWVdID0gcHJvcEFjY2Vzcyhub2RlKTtcblxuICAgICAgICBpZiAoYWNjVHlwZSAhPT0gJ2R1bW15UHJvcGVydHknKSB7XG4gICAgICAgICAgICBvYmpBVmFsLnByb3BhZ2F0ZShuZXcgY3N0ci5SZWFkUHJvcChwcm9wTmFtZSwgcmV0KSk7XG4gICAgICAgIH1cblxuICAgICAgICAvLyByZXR1cm5zIEFWYWwgZm9yIHJlY2VpdmVyIGFuZCByZWFkIG1lbWJlclxuICAgICAgICByZXR1cm4gW29iakFWYWwsIHJldF07XG4gICAgfVxuXG4gICAgY29uc3QgcGF0dGVybldhbGsgPSB7XG4gICAgICAgIElkZW50aWZpZXI6IChub2RlLCBjdXJTdGF0dXMsIHNvdXJjZSkgPT4ge1xuICAgICAgICAgICAgY29uc3QgdmFyTmFtZSA9IG5vZGUubmFtZTtcbiAgICAgICAgICAgIGNvbnN0IGxoc0FWYWwgPSBjdXJTdGF0dXMuc2MuZ2V0QVZhbE9mKHZhck5hbWUpO1xuICAgICAgICAgICAgxIguc2V0KG5vZGUsIGN1clN0YXR1cy5kZWx0YSwgbGhzQVZhbCk7XG4gICAgICAgICAgICBzb3VyY2UucHJvcGFnYXRlKGxoc0FWYWwpO1xuICAgICAgICB9LFxuICAgICAgICBNZW1iZXJFeHByZXNzaW9uOiAobm9kZSwgY3VyU3RhdHVzLCBzb3VyY2UpID0+IHtcbiAgICAgICAgICAgIGNvbnN0IG9iakFWYWwgPSBzdG10RXhwcldhbGtlcihub2RlLm9iamVjdCwgY3VyU3RhdHVzKTtcbiAgICAgICAgICAgIGNvbnN0IFthY2NUeXBlLCBwcm9wTmFtZV0gPSBwcm9wQWNjZXNzKG5vZGUubGVmdCk7XG4gICAgICAgICAgICAvLyBhc3NpZ25tZW50IHRvIG1lbWJlclxuICAgICAgICAgICAgaWYgKGFjY1R5cGUgIT09ICdkdW1teVByb3BlcnR5Jykge1xuICAgICAgICAgICAgICAgIG9iakFWYWwucHJvcGFnYXRlKG5ldyBjc3RyLldyaXRlUHJvcChwcm9wTmFtZSwgc291cmNlKSk7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICAvLyBpZiBwcm9wZXJ0eSBpcyBudW1iZXIgbGl0ZXJhbCwgYWxzbyB3cml0ZSB0byAndW5rbm93bidcbiAgICAgICAgICAgIGlmIChhY2NUeXBlID09PSAnbnVtYmVyTGl0ZXJhbCcpIHtcbiAgICAgICAgICAgICAgICBvYmpBVmFsLnByb3BhZ2F0ZShuZXcgY3N0ci5Xcml0ZVByb3AobnVsbCwgc291cmNlKSk7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICAvLyBub2RlJ3MgQVZhbCBmcm9tIFJIU1xuICAgICAgICAgICAgxIguc2V0KG5vZGUsIGN1clN0YXR1cy5kZWx0YSwgc291cmNlKTtcbiAgICAgICAgfSxcbiAgICAgICAgT2JqZWN0UGF0dGVybjogKG5vZGUsIGN1clN0YXR1cywgc291cmNlKSA9PiB7XG4gICAgICAgICAgICBmb3IgKGxldCBpID0gMDsgaSA8IG5vZGUucHJvcGVydGllcy5sZW5ndGg7IGkrKykge1xuICAgICAgICAgICAgICAgIGNvbnN0IHByb3AgPSBub2RlLnByb3BlcnRpZXNbaV07XG4gICAgICAgICAgICAgICAgLy8gV2UgbmVlZCBhbiBBVmFsIGZvciBwcm9wIHJlYWQuXG4gICAgICAgICAgICAgICAgLy8gTm90IHN1cmUgYXR0YWNoaW5nIHRoZSBBVmFsIHRvIHByb3Aua2V5IG5vZGUgaXMgZ29vZC5cbiAgICAgICAgICAgICAgICBjb25zdCBwcm9wQVZhbCA9IMSILmdldChwcm9wLmtleSwgY3VyU3RhdHVzLmRlbHRhKTtcbiAgICAgICAgICAgICAgICBzb3VyY2UucHJvcGFnYXRlKG5ldyBjc3RyLlJlYWRQcm9wKHByb3Aua2V5Lm5hbWUsIHByb3BBVmFsKSk7XG4gICAgICAgICAgICAgICAgY29ubmVjdFBhdHRlcm4ocHJvcC52YWx1ZSwgY3VyU3RhdHVzLCBwcm9wQVZhbCk7XG4gICAgICAgICAgICB9XG4gICAgICAgIH0sXG4gICAgICAgIEFycmF5UGF0dGVybjogKG5vZGUsIGN1clN0YXR1cywgc291cmNlKSA9PiB7XG4gICAgICAgICAgICBmb3IgKGxldCBpID0gMDsgaSA8IG5vZGUuZWxlbWVudHMubGVuZ3RoOyBpKyspIHtcbiAgICAgICAgICAgICAgICBjb25zdCBlbHQgPSBub2RlLmVsZW1lbnRzW2ldO1xuICAgICAgICAgICAgICAgIGNvbnN0IGVsdEFWYWwgPSDEiC5nZXQoZWx0LCBjdXJTdGF0dXMuZGVsdGEpO1xuICAgICAgICAgICAgICAgIGlmIChlbHQudHlwZSA9PT0gJ1Jlc3RFbGVtZW50Jykge1xuICAgICAgICAgICAgICAgICAgICAvLyB1c2Ugb25seSBvbmUgZWxlbWVudFxuICAgICAgICAgICAgICAgICAgICBjb25zdCByZXN0QVZhbCA9IGdldFJlc3RBVmFsKG5vZGUsIGN1clN0YXR1cyk7XG4gICAgICAgICAgICAgICAgICAgIHJlc3RBVmFsLnByb3BhZ2F0ZShlbHRBVmFsKTtcblxuICAgICAgICAgICAgICAgICAgICBjb25zdCB0ZW1wQVZhbCA9IG5ldyB0eXBlcy5BVmFsKCk7XG4gICAgICAgICAgICAgICAgICAgIHNvdXJjZS5wcm9wYWdhdGUobmV3IGNzdHIuUmVhZFByb3AoU3RyaW5nKGkpLCB0ZW1wQVZhbCkpO1xuICAgICAgICAgICAgICAgICAgICByZXN0QVZhbC5wcm9wYWdhdGUobmV3IGNzdHIuV3JpdGVQcm9wKFN0cmluZygwKSwgdGVtcEFWYWwpKTtcbiAgICAgICAgICAgICAgICAgICAgcmVzdEFWYWwucHJvcGFnYXRlKG5ldyBjc3RyLldyaXRlUHJvcChudWxsLCB0ZW1wQVZhbCkpO1xuICAgICAgICAgICAgICAgICAgICBjb25uZWN0UGF0dGVybihlbHQsIGN1clN0YXR1cywgcmVzdEFWYWwpO1xuICAgICAgICAgICAgICAgICAgICBicmVhaztcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgaWYgKGVsdCkge1xuICAgICAgICAgICAgICAgICAgICAvLyBXZSBuZWVkIGFuIEFWYWwgZm9yIGluZGV4IHJlYWRcbiAgICAgICAgICAgICAgICAgICAgLy8gTm90IHN1cmUgYXR0YWNoaW5nIHRoZSBBVmFsIHRvIGVsdCBub2RlIGlzIGdvb2QuXG4gICAgICAgICAgICAgICAgICAgIHNvdXJjZS5wcm9wYWdhdGUobmV3IGNzdHIuUmVhZFByb3AoU3RyaW5nKGkpLCBlbHRBVmFsKSk7XG4gICAgICAgICAgICAgICAgICAgIGNvbm5lY3RQYXR0ZXJuKGVsdCwgY3VyU3RhdHVzLCBlbHRBVmFsKTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICB9XG4gICAgICAgIH0sXG4gICAgICAgIEFzc2lnbm1lbnRQYXR0ZXJuOiAobm9kZSwgY3VyU3RhdHVzLCBzb3VyY2UpID0+IHtcbiAgICAgICAgICAgIGNvbnN0IG1lcmdlZEFWYWwgPSDEiC5nZXQobm9kZSwgY3VyU3RhdHVzLmRlbHRhKTtcbiAgICAgICAgICAgIGNvbnN0IHJoc0FWYWwgPSBzdG10RXhwcldhbGtlcihub2RlLnJpZ2h0LCBjdXJTdGF0dXMpO1xuICAgICAgICAgICAgc291cmNlLnByb3BhZ2F0ZShtZXJnZWRBVmFsKTtcbiAgICAgICAgICAgIHJoc0FWYWwucHJvcGFnYXRlKG1lcmdlZEFWYWwpO1xuICAgICAgICAgICAgY29ubmVjdFBhdHRlcm4obm9kZS5sZWZ0LCBjdXJTdGF0dXMsIG1lcmdlZEFWYWwpXG4gICAgICAgIH0sXG4gICAgICAgIFJlc3RFbGVtZW50OiAobm9kZSwgY3VyU3RhdHVzLCBzb3VyY2UpID0+IHtcbiAgICAgICAgICAgIGNvbm5lY3RQYXR0ZXJuKG5vZGUuYXJndW1lbnQsIGN1clN0YXR1cywgc291cmNlKTtcbiAgICAgICAgfVxuICAgIH07XG5cbiAgICBjb25uZWN0UGF0dGVybiA9IChub2RlLCBjdXJTdGF0dXMsIHNvdXJjZSkgPT4ge1xuICAgICAgICBjb25zdCBjb25uZWN0b3IgPSBwYXR0ZXJuV2Fsa1tub2RlLnR5cGVdO1xuICAgICAgICBpZiAoY29ubmVjdG9yKSBjb25uZWN0b3Iobm9kZSwgY3VyU3RhdHVzLCBzb3VyY2UpO1xuICAgIH07XG5cbiAgICAvLyBjb25zdHJhaW50IGdlbmVyYXRpbmcgd2Fsa2VyIGZvciBleHByZXNzaW9uc1xuICAgIGNvbnN0IHN0bXRFeHByV2FsayA9IHdhbGsubWFrZSh7XG5cbiAgICAgICAgSWRlbnRpZmllcjogZnVuY3Rpb24gKG5vZGUsIGN1clN0YXR1cywgYykge1xuICAgICAgICAgICAgaWYgKG15V2Fsa2VyLmlzRHVtbXlJZE5vZGUobm9kZSkpIHtcbiAgICAgICAgICAgICAgICAvLyBSZXR1cm4gQVZhbE51bGwgZm9yIGR1bW15IGlkZW50aXR5IG5vZGVcbiAgICAgICAgICAgICAgICByZXR1cm4gdHlwZXMuQVZhbE51bGw7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBjb25zdCBhdiA9IGN1clN0YXR1cy5zYy5nZXRBVmFsT2Yobm9kZS5uYW1lKTtcbiAgICAgICAgICAgIC8vIHVzZSBhdmFsIGluIHRoZSBzY29wZVxuICAgICAgICAgICAgxIguc2V0KG5vZGUsIGN1clN0YXR1cy5kZWx0YSwgYXYpO1xuICAgICAgICAgICAgcmV0dXJuIGF2O1xuICAgICAgICB9LFxuXG4gICAgICAgIFRoaXNFeHByZXNzaW9uOiBmdW5jdGlvbiAobm9kZSwgY3VyU3RhdHVzLCBjKSB7XG4gICAgICAgICAgICBjb25zdCBhdiA9IGN1clN0YXR1cy5zZWxmO1xuICAgICAgICAgICAgLy8gdXNlIGF2YWwgZm9yICd0aGlzJ1xuICAgICAgICAgICAgxIguc2V0KG5vZGUsIGN1clN0YXR1cy5kZWx0YSwgYXYpO1xuICAgICAgICAgICAgcmV0dXJuIGF2O1xuICAgICAgICB9LFxuXG4gICAgICAgIExpdGVyYWw6IGZ1bmN0aW9uIChub2RlLCBjdXJTdGF0dXMsIGMpIHtcbiAgICAgICAgICAgIGNvbnN0IHJlcyA9IMSILmdldChub2RlLCBjdXJTdGF0dXMuZGVsdGEpO1xuICAgICAgICAgICAgaWYgKG5vZGUucmVnZXgpIHtcbiAgICAgICAgICAgICAgICAvLyBub3QgaW1wbGVtZW50ZWQgeWV0XG4gICAgICAgICAgICAgICAgLy8gdGhyb3cgbmV3IEVycm9yKCdyZWdleCBsaXRlcmFsIGlzIG5vdCBpbXBsZW1lbnRlZCB5ZXQnKTtcbiAgICAgICAgICAgICAgICByZXR1cm4gcmVzO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgc3dpdGNoICh0eXBlb2Ygbm9kZS52YWx1ZSkge1xuICAgICAgICAgICAgY2FzZSAnbnVtYmVyJzpcbiAgICAgICAgICAgICAgICByZXMuYWRkVHlwZSh0eXBlcy5QcmltTnVtYmVyKTtcbiAgICAgICAgICAgICAgICBicmVhaztcbiAgICAgICAgICAgIGNhc2UgJ3N0cmluZyc6XG4gICAgICAgICAgICAgICAgcmVzLmFkZFR5cGUodHlwZXMuUHJpbVN0cmluZyk7XG4gICAgICAgICAgICAgICAgYnJlYWs7XG4gICAgICAgICAgICBjYXNlICdib29sZWFuJzpcbiAgICAgICAgICAgICAgICByZXMuYWRkVHlwZSh0eXBlcy5QcmltQm9vbGVhbik7XG4gICAgICAgICAgICAgICAgYnJlYWs7XG4gICAgICAgICAgICBjYXNlICdvYmplY3QnOlxuICAgICAgICAgICAgICAgIC8vIEkgZ3Vlc3M6IExpdGVyYWwgJiYgb2JqZWN0ID09PiBub2RlLnZhbHVlID09IG51bGxcbiAgICAgICAgICAgICAgICAvLyBudWxsIGlzIGlnbm9yZWQsIHNvIG5vdGhpbmcgdG8gYWRkXG4gICAgICAgICAgICAgICAgYnJlYWs7XG4gICAgICAgICAgICBjYXNlICdmdW5jdGlvbic6XG4gICAgICAgICAgICAgICAgdGhyb3cgbmV3IEVycm9yKCdJIGd1ZXNzIGZ1bmN0aW9uIGlzIGltcG9zc2libGUgaGVyZS4nKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIHJldHVybiByZXM7XG4gICAgICAgIH0sXG5cbiAgICAgICAgQXNzaWdubWVudEV4cHJlc3Npb246IGZ1bmN0aW9uIChub2RlLCBjdXJTdGF0dXMsIGMpIHtcbiAgICAgICAgICAgIGNvbnN0IHJoc0FWYWwgPSBjKG5vZGUucmlnaHQsIGN1clN0YXR1cywgdW5kZWZpbmVkKTtcbiAgICAgICAgICAgIGlmIChub2RlLmxlZnQudHlwZSA9PT0gJ0lkZW50aWZpZXInKSB7XG4gICAgICAgICAgICAgICAgLy8gTEhTIGlzIGEgc2ltcGxlIHZhcmlhYmxlLlxuICAgICAgICAgICAgICAgIGNvbnN0IHZhck5hbWUgPSBub2RlLmxlZnQubmFtZTtcbiAgICAgICAgICAgICAgICBjb25zdCBsaHNBVmFsID0gY3VyU3RhdHVzLnNjLmdldEFWYWxPZih2YXJOYW1lKTtcbiAgICAgICAgICAgICAgICAvLyBsaHMgaXMgbm90IHZpc2l0ZWQuIE5lZWQgdG8gaGFuZGxlIGhlcmUuXG4gICAgICAgICAgICAgICAgLy8gVXNlIGF2YWwgZm91bmQgaW4gdGhlIHNjb3BlIGZvciBsaHNcbiAgICAgICAgICAgICAgICDEiC5zZXQobm9kZS5sZWZ0LCBjdXJTdGF0dXMuZGVsdGEsIGxoc0FWYWwpO1xuXG4gICAgICAgICAgICAgICAgaWYgKG5vZGUub3BlcmF0b3IgPT09ICc9Jykge1xuICAgICAgICAgICAgICAgICAgICAvLyBzaW1wbGUgYXNzaWdubWVudFxuICAgICAgICAgICAgICAgICAgICByaHNBVmFsLnByb3BhZ2F0ZShsaHNBVmFsKTtcbiAgICAgICAgICAgICAgICAgICAgLy8gbm9kZSdzIEFWYWwgZnJvbSBSSFNcbiAgICAgICAgICAgICAgICAgICAgxIguc2V0KG5vZGUsIGN1clN0YXR1cy5kZWx0YSwgcmhzQVZhbCk7XG4gICAgICAgICAgICAgICAgICAgIHJldHVybiByaHNBVmFsO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAvLyB1cGRhdGluZyBhc3NpZ25tZW50XG4gICAgICAgICAgICAgICAgY29uc3QgcmVzQVZhbCA9IMSILmdldChub2RlLCBjdXJTdGF0dXMuZGVsdGEpO1xuICAgICAgICAgICAgICAgIGlmIChub2RlLm9wZXJhdG9yID09PSAnKz0nKSB7XG4gICAgICAgICAgICAgICAgICAgIC8vIGNvbmNhdGVuYXRpbmcgdXBkYXRlXG4gICAgICAgICAgICAgICAgICAgIGxoc0FWYWwucHJvcGFnYXRlKG5ldyBjc3RyLklzQWRkZWQocmhzQVZhbCwgcmVzQVZhbCkpO1xuICAgICAgICAgICAgICAgICAgICByaHNBVmFsLnByb3BhZ2F0ZShuZXcgY3N0ci5Jc0FkZGVkKGxoc0FWYWwsIHJlc0FWYWwpKTtcbiAgICAgICAgICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgICAgICAgICAgICAvLyBhcml0aG1ldGljIHVwZGF0ZVxuICAgICAgICAgICAgICAgICAgICByZXNBVmFsLmFkZFR5cGUodHlwZXMuUHJpbU51bWJlcik7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIHJldHVybiByZXNBVmFsO1xuICAgICAgICAgICAgfSBlbHNlIGlmIChub2RlLmxlZnQudHlwZSA9PT0gJ01lbWJlckV4cHJlc3Npb24nKSB7XG4gICAgICAgICAgICAgICAgY29uc3Qgb2JqQVZhbCA9IGMobm9kZS5sZWZ0Lm9iamVjdCwgY3VyU3RhdHVzLCB1bmRlZmluZWQpO1xuICAgICAgICAgICAgICAgIGNvbnN0IFthY2NUeXBlLCBwcm9wTmFtZV0gPSBwcm9wQWNjZXNzKG5vZGUubGVmdCk7XG4gICAgICAgICAgICAgICAgaWYgKG5vZGUub3BlcmF0b3IgPT09ICc9Jykge1xuICAgICAgICAgICAgICAgICAgICAvLyBhc3NpZ25tZW50IHRvIG1lbWJlclxuICAgICAgICAgICAgICAgICAgICBpZiAoYWNjVHlwZSAhPT0gJ2R1bW15UHJvcGVydHknKSB7XG4gICAgICAgICAgICAgICAgICAgICAgICBvYmpBVmFsLnByb3BhZ2F0ZShuZXcgY3N0ci5Xcml0ZVByb3AocHJvcE5hbWUsIHJoc0FWYWwpKTtcbiAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAvLyBpZiBwcm9wZXJ0eSBpcyBudW1iZXIgbGl0ZXJhbCwgYWxzbyB3cml0ZSB0byAndW5rbm93bidcbiAgICAgICAgICAgICAgICAgICAgaWYgKGFjY1R5cGUgPT09ICdudW1iZXJMaXRlcmFsJykge1xuICAgICAgICAgICAgICAgICAgICAgICAgb2JqQVZhbC5wcm9wYWdhdGUobmV3IGNzdHIuV3JpdGVQcm9wKG51bGwsIHJoc0FWYWwpKTtcbiAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAvLyBub2RlJ3MgQVZhbCBmcm9tIFJIU1xuICAgICAgICAgICAgICAgICAgICDEiC5zZXQobm9kZSwgY3VyU3RhdHVzLmRlbHRhLCByaHNBVmFsKTtcbiAgICAgICAgICAgICAgICAgICAgcmV0dXJuIHJoc0FWYWw7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIC8vIHVwZGF0aW5nIGFzc2lnbm1lbnRcbiAgICAgICAgICAgICAgICBjb25zdCByZXNBVmFsID0gxIguZ2V0KG5vZGUsIGN1clN0YXR1cy5kZWx0YSk7XG4gICAgICAgICAgICAgICAgY29uc3QgWywgcmV0QVZhbF0gPSByZWFkTWVtYmVyKG5vZGUubGVmdCwgY3VyU3RhdHVzLCBjKTtcbiAgICAgICAgICAgICAgICBpZiAobm9kZS5vcGVyYXRvciA9PT0gJys9Jykge1xuICAgICAgICAgICAgICAgICAgICAvLyBjb25jYXRlbmF0aW5nIHVwZGF0ZVxuICAgICAgICAgICAgICAgICAgICByZXRBVmFsLnByb3BhZ2F0ZShuZXcgY3N0ci5Jc0FkZGVkKHJoc0FWYWwsIHJlc0FWYWwpKTtcbiAgICAgICAgICAgICAgICAgICAgcmhzQVZhbC5wcm9wYWdhdGUobmV3IGNzdHIuSXNBZGRlZChyZXRBVmFsLCByZXNBVmFsKSk7XG4gICAgICAgICAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgLy8gYXJpdGhtZXRpYyB1cGRhdGVcbiAgICAgICAgICAgICAgICAgICAgcmVzQVZhbC5hZGRUeXBlKHR5cGVzLlByaW1OdW1iZXIpO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICByZXR1cm4gcmVzQVZhbDtcbiAgICAgICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgICAgICAgY29ubmVjdFBhdHRlcm4obm9kZS5sZWZ0LCBjdXJTdGF0dXMsIHJoc0FWYWwpO1xuICAgICAgICAgICAgfVxuICAgICAgICB9LFxuXG4gICAgICAgIFZhcmlhYmxlRGVjbGFyYXRpb246IGZ1bmN0aW9uIChub2RlLCBjdXJTdGF0dXMsIGMpIHtcbiAgICAgICAgICAgIGZvciAobGV0IGkgPSAwOyBpIDwgbm9kZS5kZWNsYXJhdGlvbnMubGVuZ3RoOyBpKyspIHtcbiAgICAgICAgICAgICAgICBjb25zdCBkZWNsID0gbm9kZS5kZWNsYXJhdGlvbnNbaV07XG4gICAgICAgICAgICAgICAgLy8gY29uc3QgbGhzQVZhbCA9IGN1clN0YXR1cy5zYy5nZXRBVmFsT2YoZGVjbC5pZC5uYW1lKTtcbiAgICAgICAgICAgICAgICAvLyBkZWNsYXJlZCB2YXIgbm9kZSBpcyAnaWQnXG4gICAgICAgICAgICAgICAgLy8gxIguc2V0KGRlY2wuaWQsIGN1clN0YXR1cy5kZWx0YSwgbGhzQVZhbCk7XG4gICAgICAgICAgICAgICAgaWYgKGRlY2wuaW5pdCkge1xuICAgICAgICAgICAgICAgICAgICBjb25zdCByaHNBVmFsID0gYyhkZWNsLmluaXQsIGN1clN0YXR1cywgdW5kZWZpbmVkKTtcbiAgICAgICAgICAgICAgICAgICAgxIguc2V0KGRlY2wuaW5pdCwgY3VyU3RhdHVzLmRlbHRhLCByaHNBVmFsKTtcbiAgICAgICAgICAgICAgICAgICAgLy9yaHNBVmFsLnByb3BhZ2F0ZShsaHNBVmFsKTtcbiAgICAgICAgICAgICAgICAgICAgY29ubmVjdFBhdHRlcm4oZGVjbC5pZCwgY3VyU3RhdHVzLCByaHNBVmFsKTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICB9XG4gICAgICAgIH0sXG5cbiAgICAgICAgTG9naWNhbEV4cHJlc3Npb246IGZ1bmN0aW9uIChub2RlLCBjdXJTdGF0dXMsIGMpIHtcbiAgICAgICAgICAgIGNvbnN0IHJlcyA9IMSILmdldChub2RlLCBjdXJTdGF0dXMuZGVsdGEpO1xuICAgICAgICAgICAgY29uc3QgbGVmdCA9IGMobm9kZS5sZWZ0LCBjdXJTdGF0dXMsIHVuZGVmaW5lZCk7XG4gICAgICAgICAgICBjb25zdCByaWdodCA9IGMobm9kZS5yaWdodCwgY3VyU3RhdHVzLCB1bmRlZmluZWQpO1xuICAgICAgICAgICAgbGVmdC5wcm9wYWdhdGUocmVzKTtcbiAgICAgICAgICAgIHJpZ2h0LnByb3BhZ2F0ZShyZXMpO1xuICAgICAgICAgICAgcmV0dXJuIHJlcztcbiAgICAgICAgfSxcblxuICAgICAgICBDb25kaXRpb25hbEV4cHJlc3Npb246IGZ1bmN0aW9uIChub2RlLCBjdXJTdGF0dXMsIGMpIHtcbiAgICAgICAgICAgIGNvbnN0IHJlcyA9IMSILmdldChub2RlLCBjdXJTdGF0dXMuZGVsdGEpO1xuICAgICAgICAgICAgYyhub2RlLnRlc3QsIGN1clN0YXR1cywgdW5kZWZpbmVkKTtcbiAgICAgICAgICAgIGNvbnN0IGNvbnMgPSBjKG5vZGUuY29uc2VxdWVudCwgY3VyU3RhdHVzLCB1bmRlZmluZWQpO1xuICAgICAgICAgICAgY29uc3QgYWx0ID0gYyhub2RlLmFsdGVybmF0ZSwgY3VyU3RhdHVzLCB1bmRlZmluZWQpO1xuICAgICAgICAgICAgY29ucy5wcm9wYWdhdGUocmVzKTtcbiAgICAgICAgICAgIGFsdC5wcm9wYWdhdGUocmVzKTtcbiAgICAgICAgICAgIHJldHVybiByZXM7XG4gICAgICAgIH0sXG5cbiAgICAgICAgTmV3RXhwcmVzc2lvbjogZnVuY3Rpb24gKG5vZGUsIGN1clN0YXR1cywgYykge1xuICAgICAgICAgICAgY29uc3QgcmV0ID0gxIguZ2V0KG5vZGUsIGN1clN0YXR1cy5kZWx0YSk7XG4gICAgICAgICAgICBjb25zdCBjYWxsZWUgPSBjKG5vZGUuY2FsbGVlLCBjdXJTdGF0dXMsIHVuZGVmaW5lZCk7XG4gICAgICAgICAgICBjb25zdCBhcmdzID0gW107XG4gICAgICAgICAgICBmb3IgKGxldCBpID0gMDsgaSA8IG5vZGUuYXJndW1lbnRzLmxlbmd0aDsgaSsrKSB7XG4gICAgICAgICAgICAgICAgYXJncy5wdXNoKGMobm9kZS5hcmd1bWVudHNbaV0sIGN1clN0YXR1cywgdW5kZWZpbmVkKSk7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBjb25zdCBuZXdEZWx0YSA9IGN1clN0YXR1cy5kZWx0YS5hcHBlbmRPbmUobm9kZVsnQGxhYmVsJ10pO1xuICAgICAgICAgICAgY2FsbGVlLnByb3BhZ2F0ZShcbiAgICAgICAgICAgICAgICBuZXcgY3N0ci5Jc0N0b3IoXG4gICAgICAgICAgICAgICAgICAgIGFyZ3MsXG4gICAgICAgICAgICAgICAgICAgIHJldCxcbiAgICAgICAgICAgICAgICAgICAgY3VyU3RhdHVzLmV4YyxcbiAgICAgICAgICAgICAgICAgICAgbmV3RGVsdGEpKTtcbiAgICAgICAgICAgIHJldHVybiByZXQ7XG4gICAgICAgIH0sXG5cbiAgICAgICAgQXJyYXlFeHByZXNzaW9uOiBmdW5jdGlvbiAobm9kZSwgY3VyU3RhdHVzLCBjKSB7XG4gICAgICAgICAgICBjb25zdCByZXQgPSDEiC5nZXQobm9kZSwgY3VyU3RhdHVzLmRlbHRhKTtcbiAgICAgICAgICAgIC8vIE5PVEUgcHJvdG90eXBlIG9iamVjdCBpcyBub3QgcmVjb3JkZWQgaW4gxIhcbiAgICAgICAgICAgIGNvbnN0IGFyclR5cGUgPSBuZXcgdHlwZXMuQXJyVHlwZShuZXcgdHlwZXMuQVZhbChydENYLnByb3Rvcy5BcnJheSkpO1xuICAgICAgICAgICAgLy8gYWRkIGxlbmd0aCBwcm9wZXJ0eVxuICAgICAgICAgICAgYXJyVHlwZS5nZXRQcm9wKCdsZW5ndGgnKS5hZGRUeXBlKHR5cGVzLlByaW1OdW1iZXIpO1xuXG4gICAgICAgICAgICByZXQuYWRkVHlwZShhcnJUeXBlKTtcblxuICAgICAgICAgICAgLy8gYWRkIGFycmF5IGVsZW1lbnRzXG4gICAgICAgICAgICBmb3IgKGxldCBpID0gMDsgaSA8IG5vZGUuZWxlbWVudHMubGVuZ3RoOyBpKyspIHtcbiAgICAgICAgICAgICAgICBpZiAobm9kZS5lbGVtZW50c1tpXSA9PSBudWxsKSB7XG4gICAgICAgICAgICAgICAgICAgIGNvbnRpbnVlO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICBjb25zdCBlbHRBVmFsID0gYyhub2RlLmVsZW1lbnRzW2ldLCBjdXJTdGF0dXMsIHVuZGVmaW5lZCk7XG5cbiAgICAgICAgICAgICAgICBjb25zdCBwcm9wID0gaSArICcnO1xuICAgICAgICAgICAgICAgIHJldC5wcm9wYWdhdGUobmV3IGNzdHIuV3JpdGVQcm9wKHByb3AsIGVsdEFWYWwpKTtcbiAgICAgICAgICAgICAgICByZXQucHJvcGFnYXRlKG5ldyBjc3RyLldyaXRlUHJvcChudWxsLCBlbHRBVmFsKSk7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICByZXR1cm4gcmV0O1xuICAgICAgICB9LFxuXG4gICAgICAgIE9iamVjdEV4cHJlc3Npb246IGZ1bmN0aW9uIChub2RlLCBjdXJTdGF0dXMsIGMpIHtcbiAgICAgICAgICAgIGNvbnN0IHJldCA9IMSILmdldChub2RlLCBjdXJTdGF0dXMuZGVsdGEpO1xuICAgICAgICAgICAgLy8gTk9URSBwcm90b3R5cGUgb2JqZWN0IGlzIG5vdCByZWNvcmRlZCBpbiDEiFxuICAgICAgICAgICAgY29uc3Qgb2JqVHlwZSA9IG5ldyB0eXBlcy5PYmpUeXBlKG5ldyB0eXBlcy5BVmFsKHJ0Q1gucHJvdG9zLk9iamVjdCkpO1xuICAgICAgICAgICAgcmV0LmFkZFR5cGUob2JqVHlwZSk7XG5cbiAgICAgICAgICAgIGZvciAobGV0IGkgPSAwOyBpIDwgbm9kZS5wcm9wZXJ0aWVzLmxlbmd0aDsgaSsrKSB7XG4gICAgICAgICAgICAgICAgY29uc3QgcHJvcFBhaXIgPSBub2RlLnByb3BlcnRpZXNbaV07XG4gICAgICAgICAgICAgICAgY29uc3QgcHJvcEtleSA9IHByb3BQYWlyLmtleTtcbiAgICAgICAgICAgICAgICBsZXQgbmFtZTtcbiAgICAgICAgICAgICAgICBjb25zdCBwcm9wRXhwciA9IHByb3BQYWlyLnZhbHVlO1xuXG4gICAgICAgICAgICAgICAgY29uc3QgZmxkQVZhbCA9IGMocHJvcEV4cHIsIGN1clN0YXR1cywgdW5kZWZpbmVkKTtcblxuICAgICAgICAgICAgICAgIGlmIChwcm9wS2V5LnR5cGUgPT09ICdJZGVudGlmaWVyJykge1xuICAgICAgICAgICAgICAgICAgICBuYW1lID0gcHJvcEtleS5uYW1lO1xuICAgICAgICAgICAgICAgIH0gZWxzZSBpZiAodHlwZW9mIHByb3BLZXkudmFsdWUgPT09ICdzdHJpbmcnKSB7XG4gICAgICAgICAgICAgICAgICAgIG5hbWUgPSBwcm9wS2V5LnZhbHVlO1xuICAgICAgICAgICAgICAgIH0gZWxzZSBpZiAodHlwZW9mIHByb3BLZXkudmFsdWUgPT09ICdudW1iZXInKSB7XG4gICAgICAgICAgICAgICAgICAgIC8vIGNvbnZlcnQgbnVtYmVyIHRvIHN0cmluZ1xuICAgICAgICAgICAgICAgICAgICBuYW1lID0gcHJvcEtleS52YWx1ZSArICcnO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICByZXQucHJvcGFnYXRlKG5ldyBjc3RyLldyaXRlUHJvcChuYW1lLCBmbGRBVmFsKSk7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICByZXR1cm4gcmV0O1xuICAgICAgICB9LFxuXG4gICAgICAgIEFycm93RnVuY3Rpb25FeHByZXNzaW9uOiBmdW5jdGlvbiAobm9kZSwgY3VyU3RhdHVzLCBjKSB7XG4gICAgICAgICAgICBpZiAoIW5vZGUuZm5JbnN0YW5jZXMpIHtcbiAgICAgICAgICAgICAgICBub2RlLmZuSW5zdGFuY2VzID0gW107XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBsZXQgZm5JbnN0YW5jZSA9IG51bGw7XG4gICAgICAgICAgICBub2RlLmZuSW5zdGFuY2VzLmZvckVhY2goZnVuY3Rpb24gKGZuVHlwZSkge1xuICAgICAgICAgICAgICAgIGlmIChmblR5cGUuc2MgPT09IGN1clN0YXR1cy5zYykge1xuICAgICAgICAgICAgICAgICAgICBmbkluc3RhbmNlID0gZm5UeXBlO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgIH0pO1xuICAgICAgICAgICAgaWYgKCFmbkluc3RhbmNlKSB7XG4gICAgICAgICAgICAgICAgZm5JbnN0YW5jZVxuICAgICAgICAgICAgICAgICAgICA9IG5ldyB0eXBlcy5GblR5cGUobmV3IHR5cGVzLkFWYWwocnRDWC5wcm90b3MuRnVuY3Rpb24pLFxuICAgICAgICAgICAgICAgICAgICAnW2Fycm93IGZ1bmN0aW9uXScsXG4gICAgICAgICAgICAgICAgICAgIG5vZGUuYm9keVsnQGJsb2NrJ10uZ2V0UGFyYW1WYXJOYW1lcygpLFxuICAgICAgICAgICAgICAgICAgICBjdXJTdGF0dXMuc2MsXG4gICAgICAgICAgICAgICAgICAgIG5vZGUsXG4gICAgICAgICAgICAgICAgICAgIHVuZGVmaW5lZCxcbiAgICAgICAgICAgICAgICAgICAgY3VyU3RhdHVzLnNlbGYgICAgLy8gYXJyb3cgZnVuY3Rpb24gc2hvdWxkIHJlbWVtYmVyIEFWYWwgb2Ygb3V0ZXIgdGhpcy5cbiAgICAgICAgICAgICAgICApO1xuICAgICAgICAgICAgICAgIG5vZGUuZm5JbnN0YW5jZXMucHVzaChmbkluc3RhbmNlKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGNvbnN0IHJldCA9IMSILmdldChub2RlLCBjdXJTdGF0dXMuZGVsdGEpO1xuICAgICAgICAgICAgcmV0LmFkZFR5cGUoZm5JbnN0YW5jZSk7XG5cbiAgICAgICAgICAgIHJldC5wcm9wYWdhdGUoXG4gICAgICAgICAgICAgICAgbmV3IGNzdHIuSXNDYWxsZWUoXG4gICAgICAgICAgICAgICAgICAgIHR5cGVzLkFWYWxOdWxsLCAgICAgICAgICAgICAgICAgIC8vIG5vdGhpbmcgdG8gcHJvcGFnYXRlIHRvIHNlbGZcbiAgICAgICAgICAgICAgICAgICAgW10sICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgLy8gbm8gYXJndW1lbnRzXG4gICAgICAgICAgICAgICAgICAgIHR5cGVzLkFWYWxOdWxsLCAgICAgICAgICAgICAgICAgIC8vIHJldHVybiBpcyBpZ25vcmVkXG4gICAgICAgICAgICAgICAgICAgIHR5cGVzLkFWYWxOdWxsLCAgICAgICAgICAgICAgICAgIC8vIG5vIHZhbGlkIGNhbGxlciB3aXRoIGV4Y0FWYWxcbiAgICAgICAgICAgICAgICAgICAgY3NjLkNhbGxTaXRlQ29udGV4dC5udWxsQ29udGV4dCAgLy8gVXNpbmcgbnVsbENvbnRleHRcbiAgICAgICAgICAgICAgICApXG4gICAgICAgICAgICApO1xuXG4gICAgICAgICAgICByZXR1cm4gcmV0O1xuICAgICAgICB9LFxuXG4gICAgICAgIEZ1bmN0aW9uRXhwcmVzc2lvbjogZnVuY3Rpb24gKG5vZGUsIGN1clN0YXR1cywgYykge1xuICAgICAgICAgICAgaWYgKCFub2RlLmZuSW5zdGFuY2VzKSB7XG4gICAgICAgICAgICAgICAgbm9kZS5mbkluc3RhbmNlcyA9IFtdO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgbGV0IGZuSW5zdGFuY2UgPSBudWxsO1xuICAgICAgICAgICAgbm9kZS5mbkluc3RhbmNlcy5mb3JFYWNoKGZ1bmN0aW9uIChmblR5cGUpIHtcbiAgICAgICAgICAgICAgICBpZiAoZm5UeXBlLnNjID09PSBjdXJTdGF0dXMuc2MpIHtcbiAgICAgICAgICAgICAgICAgICAgZm5JbnN0YW5jZSA9IGZuVHlwZTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICB9KTtcbiAgICAgICAgICAgIGlmICghZm5JbnN0YW5jZSkge1xuICAgICAgICAgICAgICAgIC8vIE5PVEUgcHJvdG90eXBlIG9iamVjdCBpcyBub3QgcmVjb3JkZWQgaW4gxIhcbiAgICAgICAgICAgICAgICBmbkluc3RhbmNlXG4gICAgICAgICAgICAgICAgICAgID0gbmV3IHR5cGVzLkZuVHlwZShuZXcgdHlwZXMuQVZhbChydENYLnByb3Rvcy5GdW5jdGlvbiksXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAnW2Fub255bW91cyBmdW5jdGlvbl0nLFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgbm9kZS5ib2R5WydAYmxvY2snXS5nZXRQYXJhbVZhck5hbWVzKCksXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBjdXJTdGF0dXMuc2MsXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBub2RlLFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgcnRDWC5wcm90b3MuT2JqZWN0KTtcbiAgICAgICAgICAgICAgICBub2RlLmZuSW5zdGFuY2VzLnB1c2goZm5JbnN0YW5jZSk7XG4gICAgICAgICAgICAgICAgLy8gTk9URSBwcm90b3R5cGUgb2JqZWN0IGlzIG5vdCByZWNvcmRlZCBpbiDEiFxuICAgICAgICAgICAgICAgIGNvbnN0IHByb3RvdHlwZU9iamVjdCA9XG4gICAgICAgICAgICAgICAgICAgIG5ldyB0eXBlcy5PYmpUeXBlKG5ldyB0eXBlcy5BVmFsKHJ0Q1gucHJvdG9zLk9iamVjdCksXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICcucHJvdG90eXBlJyk7XG4gICAgICAgICAgICAgICAgLy8gRm9yIC5wcm90b3R5cGVcbiAgICAgICAgICAgICAgICBuZXcgdHlwZXMuQVZhbChmbkluc3RhbmNlKS5wcm9wYWdhdGUoXG4gICAgICAgICAgICAgICAgICAgIG5ldyBjc3RyLldyaXRlUHJvcCgncHJvdG90eXBlJyxuZXcgdHlwZXMuQVZhbChwcm90b3R5cGVPYmplY3QpKVxuICAgICAgICAgICAgICAgICk7XG4gICAgICAgICAgICAgICAgLy8gRm9yIC5wcm90b3R5cGUuY29uc3RydWN0b3JcbiAgICAgICAgICAgICAgICBjb25zdCBjb25zdHJ1Y3RvclByb3AgPSBwcm90b3R5cGVPYmplY3QuZ2V0UHJvcCgnY29uc3RydWN0b3InKTtcbiAgICAgICAgICAgICAgICBjb25zdHJ1Y3RvclByb3AuYWRkVHlwZShmbkluc3RhbmNlKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGNvbnN0IHJldCA9IMSILmdldChub2RlLCBjdXJTdGF0dXMuZGVsdGEpO1xuICAgICAgICAgICAgcmV0LmFkZFR5cGUoZm5JbnN0YW5jZSk7XG5cbiAgICAgICAgICAgIC8vIENhbGwgdGhlIGZ1bmN0aW9uIHVzaW5nIG51bGxDb250ZXh0XG4gICAgICAgICAgICBjb25zdCBbc2VsZkFWYWwsLF0gPSBmbkluc3RhbmNlLmdldEZ1bkVudihjc2MuQ2FsbFNpdGVDb250ZXh0Lm51bGxDb250ZXh0KTtcbiAgICAgICAgICAgIC8vIGFkZCB0aGUgZnVuY3Rpb24ncyBpbnN0YW5jZVxuICAgICAgICAgICAgc2VsZkFWYWwuYWRkVHlwZShmbkluc3RhbmNlLmdldEluc3RhbmNlKCkpO1xuICAgICAgICAgICAgcmV0LnByb3BhZ2F0ZShcbiAgICAgICAgICAgICAgICBuZXcgY3N0ci5Jc0NhbGxlZShcbiAgICAgICAgICAgICAgICAgICAgdHlwZXMuQVZhbE51bGwsICAgICAgICAgICAgICAgICAgLy8gbm90aGluZyB0byBwcm9wYWdhdGUgdG8gc2VsZlxuICAgICAgICAgICAgICAgICAgICBbXSwgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAvLyBubyBhcmd1bWVudHNcbiAgICAgICAgICAgICAgICAgICAgdHlwZXMuQVZhbE51bGwsICAgICAgICAgICAgICAgICAgLy8gcmV0dXJuIGlzIGlnbm9yZWRcbiAgICAgICAgICAgICAgICAgICAgdHlwZXMuQVZhbE51bGwsICAgICAgICAgICAgICAgICAgLy8gbm8gdmFsaWQgY2FsbGVyIHdpdGggZXhjQVZhbFxuICAgICAgICAgICAgICAgICAgICBjc2MuQ2FsbFNpdGVDb250ZXh0Lm51bGxDb250ZXh0ICAvLyBVc2luZyBudWxsQ29udGV4dFxuICAgICAgICAgICAgICAgIClcbiAgICAgICAgICAgICk7XG5cbiAgICAgICAgICAgIHJldHVybiByZXQ7XG4gICAgICAgIH0sXG5cbiAgICAgICAgRnVuY3Rpb25EZWNsYXJhdGlvbjogZnVuY3Rpb24gKG5vZGUsIGN1clN0YXR1cywgYykge1xuICAgICAgICAgICAgLy8gRHJvcCBpbml0aWFsIGNhdGNoIG9yIG5vcm1hbCBzY29wZXNcbiAgICAgICAgICAgIGNvbnN0IHNjMCA9IGN1clN0YXR1cy5zYy5yZW1vdmVJbml0aWFsQ2F0Y2hPck5vcm1hbEJsb2NrcygpO1xuICAgICAgICAgICAgaWYgKCFub2RlLmZuSW5zdGFuY2VzKSB7XG4gICAgICAgICAgICAgICAgbm9kZS5mbkluc3RhbmNlcyA9IFtdO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgbGV0IGZuSW5zdGFuY2UgPSBudWxsO1xuICAgICAgICAgICAgbm9kZS5mbkluc3RhbmNlcy5mb3JFYWNoKGZ1bmN0aW9uIChmblR5cGUpIHtcbiAgICAgICAgICAgICAgICBpZiAoZm5UeXBlLnNjID09PSBzYzApIHtcbiAgICAgICAgICAgICAgICAgICAgZm5JbnN0YW5jZSA9IGZuVHlwZTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICB9KTtcbiAgICAgICAgICAgIGlmICghZm5JbnN0YW5jZSkge1xuICAgICAgICAgICAgICAgIC8vIE5PVEUgcHJvdG90eXBlIG9iamVjdCBpcyBub3QgcmVjb3JkZWQgaW4gxIhcbiAgICAgICAgICAgICAgICBmbkluc3RhbmNlXG4gICAgICAgICAgICAgICAgICAgID0gbmV3IHR5cGVzLkZuVHlwZShuZXcgdHlwZXMuQVZhbChydENYLnByb3Rvcy5GdW5jdGlvbiksXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBub2RlLmlkLm5hbWUsXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBub2RlLmJvZHlbJ0BibG9jayddLmdldFBhcmFtVmFyTmFtZXMoKSxcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIHNjMCxcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIG5vZGUsXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBydENYLnByb3Rvcy5PYmplY3QpO1xuICAgICAgICAgICAgICAgIG5vZGUuZm5JbnN0YW5jZXMucHVzaChmbkluc3RhbmNlKTtcbiAgICAgICAgICAgICAgICAvLyBmb3IgZWFjaCBmbkluc3RhbmNlLCBhc3NpZ24gb25lIHByb3RvdHlwZSBvYmplY3RcbiAgICAgICAgICAgICAgICAvLyBOT1RFIHByb3RvdHlwZSBvYmplY3QgaXMgbm90IHJlY29yZGVkIGluIMSIXG4gICAgICAgICAgICAgICAgY29uc3QgcHJvdG90eXBlT2JqZWN0ID1cbiAgICAgICAgICAgICAgICAgICAgbmV3IHR5cGVzLk9ialR5cGUobmV3IHR5cGVzLkFWYWwocnRDWC5wcm90b3MuT2JqZWN0KSxcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgbm9kZS5pZC5uYW1lICsgJy5wcm90b3R5cGUnKTtcbiAgICAgICAgICAgICAgICAvLyBGb3IgLnByb3RvdHlwZVxuICAgICAgICAgICAgICAgIG5ldyB0eXBlcy5BVmFsKGZuSW5zdGFuY2UpLnByb3BhZ2F0ZShcbiAgICAgICAgICAgICAgICAgICAgbmV3IGNzdHIuV3JpdGVQcm9wKCdwcm90b3R5cGUnLCBuZXcgdHlwZXMuQVZhbChwcm90b3R5cGVPYmplY3QpKVxuICAgICAgICAgICAgICAgICk7XG4gICAgICAgICAgICAgICAgLy8gRm9yIC5wcm90b3R5cGUuY29uc3RydWN0b3JcbiAgICAgICAgICAgICAgICBjb25zdCBjb25zdHJ1Y3RvclByb3AgPSBwcm90b3R5cGVPYmplY3QuZ2V0UHJvcCgnY29uc3RydWN0b3InKTtcbiAgICAgICAgICAgICAgICBjb25zdHJ1Y3RvclByb3AuYWRkVHlwZShmbkluc3RhbmNlKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGNvbnN0IGxoc0FWYWwgPSBzYzAuZ2V0QVZhbE9mKG5vZGUuaWQubmFtZSk7XG4gICAgICAgICAgICBsaHNBVmFsLmFkZFR5cGUoZm5JbnN0YW5jZSk7XG5cbiAgICAgICAgICAgIC8vIENhbGwgdGhlIGZ1bmN0aW9uIHVzaW5nIG51bGxDb250ZXh0XG4gICAgICAgICAgICBjb25zdCBbc2VsZkFWYWwsLF0gPSBmbkluc3RhbmNlLmdldEZ1bkVudihjc2MuQ2FsbFNpdGVDb250ZXh0Lm51bGxDb250ZXh0KTtcbiAgICAgICAgICAgIC8vIGFkZCB0aGUgZnVuY3Rpb24ncyBpbnN0YW5jZVxuICAgICAgICAgICAgc2VsZkFWYWwuYWRkVHlwZShmbkluc3RhbmNlLmdldEluc3RhbmNlKCkpO1xuICAgICAgICAgICAgbGhzQVZhbC5wcm9wYWdhdGUoXG4gICAgICAgICAgICAgICAgbmV3IGNzdHIuSXNDYWxsZWUoXG4gICAgICAgICAgICAgICAgICAgIHR5cGVzLkFWYWxOdWxsLCAgICAgICAgICAgICAgICAgIC8vIG5vdGhpbmcgdG8gcHJvcGFnYXRlIHRvIHNlbGZcbiAgICAgICAgICAgICAgICAgICAgW10sICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgLy8gbm8gYXJndW1lbnRzXG4gICAgICAgICAgICAgICAgICAgIHR5cGVzLkFWYWxOdWxsLCAgICAgICAgICAgICAgICAgIC8vIHJldHVybiBpcyBpZ25vcmVkXG4gICAgICAgICAgICAgICAgICAgIHR5cGVzLkFWYWxOdWxsLCAgICAgICAgICAgICAgICAgIC8vIG5vIHZhbGlkIGNhbGxlciB3aXRoIGV4Y0FWYWxcbiAgICAgICAgICAgICAgICAgICAgY3NjLkNhbGxTaXRlQ29udGV4dC5udWxsQ29udGV4dCAgLy8gVXNpbmcgbnVsbENvbnRleHRcbiAgICAgICAgICAgICAgICApXG4gICAgICAgICAgICApO1xuXG4gICAgICAgICAgICAvLyBub3RoaW5nIHRvIHJldHVyblxuICAgICAgICAgICAgcmV0dXJuIHR5cGVzLkFWYWxOdWxsO1xuICAgICAgICB9LFxuXG4gICAgICAgIFNlcXVlbmNlRXhwcmVzc2lvbjogZnVuY3Rpb24gKG5vZGUsIGN1clN0YXR1cywgYykge1xuICAgICAgICAgICAgY29uc3QgbGFzdEluZGV4ID0gbm9kZS5leHByZXNzaW9ucy5sZW5ndGggLSAxO1xuICAgICAgICAgICAgZm9yIChsZXQgaSA9IDA7IGkgPCBsYXN0SW5kZXg7IGkrKykge1xuICAgICAgICAgICAgICAgIGMobm9kZS5leHByZXNzaW9uc1tpXSwgY3VyU3RhdHVzLCB1bmRlZmluZWQpO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgY29uc3QgbGFzdEFWYWwgPSBjKG5vZGUuZXhwcmVzc2lvbnNbbGFzdEluZGV4XSwgY3VyU3RhdHVzLCB1bmRlZmluZWQpO1xuICAgICAgICAgICAgxIguc2V0KG5vZGUsIGN1clN0YXR1cy5kZWx0YSwgbGFzdEFWYWwpO1xuICAgICAgICAgICAgcmV0dXJuIGxhc3RBVmFsO1xuICAgICAgICB9LFxuXG4gICAgICAgIFVuYXJ5RXhwcmVzc2lvbjogZnVuY3Rpb24gKG5vZGUsIGN1clN0YXR1cywgYykge1xuICAgICAgICAgICAgYyhub2RlLmFyZ3VtZW50LCBjdXJTdGF0dXMsIHVuZGVmaW5lZCk7XG4gICAgICAgICAgICBjb25zdCByZXMgPSDEiC5nZXQobm9kZSwgY3VyU3RhdHVzLmRlbHRhKTtcbiAgICAgICAgICAgIGNvbnN0IHR5cGUgPSB1bm9wUmVzdWx0VHlwZShub2RlLm9wZXJhdG9yKTtcbiAgICAgICAgICAgIGlmICh0eXBlKSB7XG4gICAgICAgICAgICAgICAgcmVzLmFkZFR5cGUodHlwZSk7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICByZXR1cm4gcmVzO1xuICAgICAgICB9LFxuXG4gICAgICAgIFVwZGF0ZUV4cHJlc3Npb246IGZ1bmN0aW9uIChub2RlLCBjdXJTdGF0dXMsIGMpIHtcbiAgICAgICAgICAgIGMobm9kZS5hcmd1bWVudCwgY3VyU3RhdHVzLCB1bmRlZmluZWQpO1xuICAgICAgICAgICAgY29uc3QgcmVzID0gxIguZ2V0KG5vZGUsIGN1clN0YXR1cy5kZWx0YSk7XG4gICAgICAgICAgICByZXMuYWRkVHlwZSh0eXBlcy5QcmltTnVtYmVyKTtcbiAgICAgICAgICAgIC8vIFdlIGlnbm9yZSB0aGUgZWZmZWN0IG9mIHVwZGF0aW5nIHRvIG51bWJlciB0eXBlXG4gICAgICAgICAgICByZXR1cm4gcmVzO1xuICAgICAgICB9LFxuXG4gICAgICAgIEJpbmFyeUV4cHJlc3Npb246IGZ1bmN0aW9uIChub2RlLCBjdXJTdGF0dXMsIGMpIHtcbiAgICAgICAgICAgIGNvbnN0IGxPcHJkID0gYyhub2RlLmxlZnQsIGN1clN0YXR1cywgdW5kZWZpbmVkKTtcbiAgICAgICAgICAgIGNvbnN0IHJPcHJkID0gYyhub2RlLnJpZ2h0LCBjdXJTdGF0dXMsIHVuZGVmaW5lZCk7XG4gICAgICAgICAgICBjb25zdCByZXMgPSDEiC5nZXQobm9kZSwgY3VyU3RhdHVzLmRlbHRhKTtcblxuICAgICAgICAgICAgaWYgKG5vZGUub3BlcmF0b3IgPT0gJysnKSB7XG4gICAgICAgICAgICAgICAgbE9wcmQucHJvcGFnYXRlKG5ldyBjc3RyLklzQWRkZWQock9wcmQsIHJlcykpO1xuICAgICAgICAgICAgICAgIHJPcHJkLnByb3BhZ2F0ZShuZXcgY3N0ci5Jc0FkZGVkKGxPcHJkLCByZXMpKTtcbiAgICAgICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgICAgICAgaWYgKGJpbm9wSXNCb29sZWFuKG5vZGUub3BlcmF0b3IpKSB7XG4gICAgICAgICAgICAgICAgICAgIHJlcy5hZGRUeXBlKHR5cGVzLlByaW1Cb29sZWFuKTtcbiAgICAgICAgICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgICAgICAgICAgICByZXMuYWRkVHlwZSh0eXBlcy5QcmltTnVtYmVyKTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICByZXR1cm4gcmVzO1xuICAgICAgICB9LFxuXG4gICAgICAgIEZvclN0YXRlbWVudDogZnVuY3Rpb24gKG5vZGUsIGN1clN0YXR1cywgYykge1xuICAgICAgICAgICAgaWYgKG5vZGVbJ0BibG9jayddKSB7XG4gICAgICAgICAgICAgICAgLy8gaWYgaXQgaGFzIEBibG9jayBwcm9wZXJ0eVxuICAgICAgICAgICAgICAgIGNvbnN0IGZvckJsb2NrU0MgPVxuICAgICAgICAgICAgICAgICAgICBub2RlWydAYmxvY2snXS5nZXRTY29wZUluc3RhbmNlKGN1clN0YXR1cy5zYywgY3VyU3RhdHVzLmRlbHRhKTtcbiAgICAgICAgICAgICAgICBjdXJTdGF0dXMgPSBjdXJTdGF0dXMuZ2V0TmV3U3RhdHVzKHtzYzogZm9yQmxvY2tTQ30pO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgd2Fsay5iYXNlLkZvclN0YXRlbWVudChub2RlLCBjdXJTdGF0dXMsIGMpO1xuICAgICAgICB9LFxuXG4gICAgICAgIEJsb2NrU3RhdGVtZW50OiBmdW5jdGlvbiAobm9kZSwgY3VyU3RhdHVzLCBjKSB7XG4gICAgICAgICAgICBpZiAobm9kZVsnQGJsb2NrJ10pIHtcbiAgICAgICAgICAgICAgICAvLyBpZiBpdCBoYXMgQGJsb2NrIHByb3BlcnR5XG4gICAgICAgICAgICAgICAgY29uc3Qgbm9ybWFsQmxvY2tTQyA9XG4gICAgICAgICAgICAgICAgICAgIG5vZGVbJ0BibG9jayddLmdldFNjb3BlSW5zdGFuY2UoY3VyU3RhdHVzLnNjLCBjdXJTdGF0dXMuZGVsdGEpO1xuICAgICAgICAgICAgICAgIGN1clN0YXR1cyA9IGN1clN0YXR1cy5nZXROZXdTdGF0dXMoe3NjOiBub3JtYWxCbG9ja1NDfSk7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICB3YWxrLmJhc2UuQmxvY2tTdGF0ZW1lbnQobm9kZSwgY3VyU3RhdHVzLCBjKTtcbiAgICAgICAgfSxcblxuICAgICAgICBUcnlTdGF0ZW1lbnQ6IGZ1bmN0aW9uIChub2RlLCBjdXJTdGF0dXMsIGMpIHtcbiAgICAgICAgICAgIC8vIGNvbnN0cnVjdCBzY29wZSBjaGFpbiBmb3IgY2F0Y2ggYmxvY2tcbiAgICAgICAgICAgIGNvbnN0IGNhdGNoQmxvY2tTQyA9XG4gICAgICAgICAgICAgICAgbm9kZS5oYW5kbGVyLmJvZHlbJ0BibG9jayddXG4gICAgICAgICAgICAgICAgLmdldFNjb3BlSW5zdGFuY2UoY3VyU3RhdHVzLnNjLCBjdXJTdGF0dXMuZGVsdGEpO1xuICAgICAgICAgICAgLy8gZ2V0IHRoZSBBVmFsIGZvciBleGNlcHRpb24gcGFyYW1ldGVyXG4gICAgICAgICAgICBjb25zdCBleGNBVmFsID0gY2F0Y2hCbG9ja1NDLmNhdWdodEFWYWw7XG5cbiAgICAgICAgICAgIC8vIGZvciB0cnkgYmxvY2tcbiAgICAgICAgICAgIGNvbnN0IHRyeVN0YXR1cyA9IGN1clN0YXR1cy5nZXROZXdTdGF0dXMoe2V4YzogZXhjQVZhbH0pO1xuICAgICAgICAgICAgYyhub2RlLmJsb2NrLCB0cnlTdGF0dXMsIHVuZGVmaW5lZCk7XG5cbiAgICAgICAgICAgIC8vIGZvciBjYXRjaCBibG9ja1xuICAgICAgICAgICAgY29uc3QgY2F0Y2hTdGF0dXMgPSBjdXJTdGF0dXMuZ2V0TmV3U3RhdHVzKHtzYzogY2F0Y2hCbG9ja1NDfSk7XG4gICAgICAgICAgICBjb25uZWN0UGF0dGVybihub2RlLmhhbmRsZXIucGFyYW0sIGNhdGNoU3RhdHVzLCBleGNBVmFsKTtcbiAgICAgICAgICAgIGMobm9kZS5oYW5kbGVyLmJvZHksIGNhdGNoU3RhdHVzLCB1bmRlZmluZWQpO1xuXG4gICAgICAgICAgICAvLyBmb3IgZmluYWxseSBibG9ja1xuICAgICAgICAgICAgaWYgKG5vZGUuZmluYWxpemVyICE9PSBudWxsKVxuICAgICAgICAgICAgICAgIGMobm9kZS5maW5hbGl6ZXIsIGN1clN0YXR1cywgdW5kZWZpbmVkKTtcbiAgICAgICAgfSxcblxuICAgICAgICBUaHJvd1N0YXRlbWVudDogZnVuY3Rpb24gKG5vZGUsIGN1clN0YXR1cywgYykge1xuICAgICAgICAgICAgY29uc3QgdGhyID0gYyhub2RlLmFyZ3VtZW50LCBjdXJTdGF0dXMsIHVuZGVmaW5lZCk7XG4gICAgICAgICAgICB0aHIucHJvcGFnYXRlKGN1clN0YXR1cy5leGMpO1xuICAgICAgICB9LFxuXG4gICAgICAgIENhbGxFeHByZXNzaW9uOiBmdW5jdGlvbiAobm9kZSwgY3VyU3RhdHVzLCBjKSB7XG4gICAgICAgICAgICBjb25zdCByZXNBVmFsID0gxIguZ2V0KG5vZGUsIGN1clN0YXR1cy5kZWx0YSk7XG4gICAgICAgICAgICBjb25zdCBhcmdBVmFscyA9IFtdO1xuXG4gICAgICAgICAgICAvLyBnZXQgQVZhbHMgZm9yIGVhY2ggYXJndW1lbnRzXG4gICAgICAgICAgICBmb3IgKGxldCBpID0gMDsgaSA8IG5vZGUuYXJndW1lbnRzLmxlbmd0aDsgaSsrKSB7XG4gICAgICAgICAgICAgICAgYXJnQVZhbHMucHVzaChcbiAgICAgICAgICAgICAgICAgICAgYyhub2RlLmFyZ3VtZW50c1tpXSwgY3VyU3RhdHVzLCB1bmRlZmluZWQpKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIC8vIGFwcGVuZCBjdXJyZW50IGNhbGwgc2l0ZSB0byB0aGUgY29udGV4dFxuICAgICAgICAgICAgY29uc3QgbmV3RGVsdGEgPSBjdXJTdGF0dXMuZGVsdGEuYXBwZW5kT25lKG5vZGVbJ0BsYWJlbCddKTtcblxuICAgICAgICAgICAgaWYgKG5vZGUuY2FsbGVlLnR5cGUgPT09ICdNZW1iZXJFeHByZXNzaW9uJykge1xuICAgICAgICAgICAgICAgIC8vIG1ldGhvZCBjYWxsXG4gICAgICAgICAgICAgICAgY29uc3QgW3JlY3ZBVmFsLCByZXRBVmFsXSA9IHJlYWRNZW1iZXIobm9kZS5jYWxsZWUsIGN1clN0YXR1cywgYyk7XG4gICAgICAgICAgICAgICAgcmV0QVZhbC5wcm9wYWdhdGUoXG4gICAgICAgICAgICAgICAgICAgIG5ldyBjc3RyLklzQ2FsbGVlKFxuICAgICAgICAgICAgICAgICAgICAgICAgcmVjdkFWYWwsXG4gICAgICAgICAgICAgICAgICAgICAgICBhcmdBVmFscyxcbiAgICAgICAgICAgICAgICAgICAgICAgIHJlc0FWYWwsXG4gICAgICAgICAgICAgICAgICAgICAgICBjdXJTdGF0dXMuZXhjLFxuICAgICAgICAgICAgICAgICAgICAgICAgbmV3RGVsdGEpKTtcbiAgICAgICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgICAgICAgLy8gbm9ybWFsIGZ1bmN0aW9uIGNhbGxcbiAgICAgICAgICAgICAgICBjb25zdCBjYWxsZWVBVmFsID0gYyhub2RlLmNhbGxlZSwgY3VyU3RhdHVzLCB1bmRlZmluZWQpO1xuICAgICAgICAgICAgICAgIC8vIGNhbGxlZeydmCByZXR1cm7snYQgY2FsbCBleHByZXNzaW9u7Jy866GcXG4gICAgICAgICAgICAgICAgLy8gY2FsbGVl7J2YIGV4Y2VwdGlvbuydhCDtmLjstpwg7Lih7J2YIGV4Y2VwdGlvbuyXkCDsoITri6ztlbTslbxcbiAgICAgICAgICAgICAgICBjYWxsZWVBVmFsLnByb3BhZ2F0ZShcbiAgICAgICAgICAgICAgICAgICAgbmV3IGNzdHIuSXNDYWxsZWUoXG4gICAgICAgICAgICAgICAgICAgICAgICBuZXcgdHlwZXMuQVZhbChydENYLmdsb2JhbE9iamVjdCksXG4gICAgICAgICAgICAgICAgICAgICAgICBhcmdBVmFscyxcbiAgICAgICAgICAgICAgICAgICAgICAgIHJlc0FWYWwsXG4gICAgICAgICAgICAgICAgICAgICAgICBjdXJTdGF0dXMuZXhjLFxuICAgICAgICAgICAgICAgICAgICAgICAgbmV3RGVsdGEpKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIHJldHVybiByZXNBVmFsO1xuICAgICAgICB9LFxuXG4gICAgICAgIE1lbWJlckV4cHJlc3Npb246IGZ1bmN0aW9uIChub2RlLCBjdXJTdGF0dXMsIGMpIHtcbiAgICAgICAgICAgIGNvbnN0IFssIHJldEFWYWxdID0gcmVhZE1lbWJlcihub2RlLCBjdXJTdGF0dXMsIGMpO1xuICAgICAgICAgICAgcmV0dXJuIHJldEFWYWw7XG4gICAgICAgIH0sXG5cbiAgICAgICAgUmV0dXJuU3RhdGVtZW50OiBmdW5jdGlvbiAobm9kZSwgY3VyU3RhdHVzLCBjKSB7XG4gICAgICAgICAgICBpZiAoIW5vZGUuYXJndW1lbnQpIHJldHVybjtcbiAgICAgICAgICAgIGNvbnN0IHJldCA9IGMobm9kZS5hcmd1bWVudCwgY3VyU3RhdHVzLCB1bmRlZmluZWQpO1xuICAgICAgICAgICAgcmV0LnByb3BhZ2F0ZShjdXJTdGF0dXMucmV0KTtcbiAgICAgICAgfVxuICAgIH0pO1xuXG4gICAgY29uc3Qgc3RtdEV4cHJXYWxrZXIgPSAobm9kZSwgY3VyU3RhdHVzKSA9PlxuICAgICAgICBteVdhbGtlci5yZWN1cnNpdmVXaXRoUmV0dXJuKG5vZGUsIGN1clN0YXR1cywgc3RtdEV4cHJXYWxrKTtcblxuXG4gICAgY29uc3Qgb3V0QVZhbCA9IHN0bXRFeHByV2Fsa2VyKGFzdE5vZGUsIGluaXRTdGF0dXMpO1xuICAgIGlmIChvdXRBVmFsKSB7XG4gICAgICAgIC8vIG11c3QgYmUgYW4gZXhwcmVzc2lvbiBib2R5XG4gICAgICAgIG91dEFWYWwucHJvcGFnYXRlKGluaXRTdGF0dXMucmV0KTtcbiAgICB9XG4gICAgLy8gV2UgYWN0dWFsbHkgYWRkZWQgY29uc3RyYWludHNcbiAgICByZXR1cm4gdHJ1ZTtcbn1cbiIsIi8qKlxuICogQGZpbGUgRGVmaW5lcyBDU1RSIGFuZCBpdHMgc3ViY2xhc3Nlcy5cbiAqIEBhdXRob3Igc2V3b24zMjYua2ltQHNhbXN1bmcuY29tXG4gKi9cblxuJ3VzZSBzdHJpY3QnO1xuaW1wb3J0ICogYXMgdHlwZXMgZnJvbSAnLi4vZG9tYWlucy90eXBlcydcbmltcG9ydCAqIGFzIHN0YXR1cyBmcm9tICcuLi9kb21haW5zL3N0YXR1cydcbmltcG9ydCAqIGFzIGNzYyBmcm9tICcuLi9kb21haW5zL2NvbnRleHQnXG5pbXBvcnQgKiBhcyBjR2VuIGZyb20gJy4vY0dlbidcblxuY2xhc3MgQ1NUUiB7XG4gICAgLyoqXG4gICAgICogQ2hlY2tzIHRoZSBlcXVhbGl0eSBiZXR3ZWVuIENTVFJzLlxuICAgICAqIEBwYXJhbSB7Q1NUUn0gb3RoZXJcbiAgICAgKiBAcmV0dXJuIHtib29sZWFufVxuICAgICAqL1xuICAgIGVxdWFscyhvdGhlcikge1xuICAgICAgICByZXR1cm4gdGhpcyA9PT0gb3RoZXI7XG4gICAgfVxuXG4gICAgLyoqXG4gICAgICogQWRkcyB0eXBlIHVzaW5nIHRoZSBpbmZvcm1hdGlvbiBvZiBDU1RSLlxuICAgICAqIEBhYnN0cmFjdFxuICAgICAqIEBwYXJhbSB7VHlwZX0gdHlwZVxuICAgICAqL1xuICAgIGFkZFR5cGUodHlwZSkge1xuICAgICAgICB0aHJvdyBuZXcgRXJyb3IoXCJjYWxsaW5nIGFic3RyYWN0IG1ldGhvZFwiKTtcbiAgICB9XG59XG5cbmV4cG9ydCBjbGFzcyBSZWFkUHJvcCBleHRlbmRzIENTVFIge1xuICAgIC8qKlxuICAgICAqIENvbnN0cnVjdHMgUmVhZFByb3AuXG4gICAgICogQHBhcmFtIHtzdHJpbmd8bnVsbH0gcHJvcFxuICAgICAqIEBwYXJhbSB7QVZhbH0gdG9cbiAgICAgKi9cbiAgICBjb25zdHJ1Y3Rvcihwcm9wLCB0bykge1xuICAgICAgICBzdXBlcigpO1xuICAgICAgICB0aGlzLnByb3AgPSBwcm9wO1xuICAgICAgICB0aGlzLnRvID0gdG87XG4gICAgfVxuXG4gICAgLyoqXG4gICAgICogQG92ZXJyaWRlXG4gICAgICovXG4gICAgYWRkVHlwZShvYmopIHtcbiAgICAgICAgaWYgKCEob2JqIGluc3RhbmNlb2YgKHR5cGVzLk9ialR5cGUpKSkgcmV0dXJuO1xuICAgICAgICAvLyB3aGVuIG9iaiBpcyBPYmpUeXBlLFxuICAgICAgICBjb25zdCBvd25Qcm9wID0gb2JqLmdldFByb3AodGhpcy5wcm9wLCB0cnVlKTtcbiAgICAgICAgaWYgKG93blByb3ApIHtcbiAgICAgICAgICAgIC8vIHdoZW4gdGhlIG9iamVjdCBoYXMgdGhlIHByb3AsXG4gICAgICAgICAgICBvd25Qcm9wLnByb3BhZ2F0ZSh0aGlzLnRvKTtcbiAgICAgICAgfSBlbHNlIGlmIChvYmouZ2V0UHJvcCgnX19wcm90b19fJywgdHJ1ZSkpIHtcbiAgICAgICAgICAgIC8vIFByb3BhZ2F0ZSBmcm9tIHVua25vd24gcHJvcCBpZiBvYmogaGFzIGl0LlxuICAgICAgICAgICAgaWYgKG9iai5oYXNQcm9wKG51bGwpKSB7XG4gICAgICAgICAgICAgICAgb2JqLmdldFByb3AobnVsbCwgdHJ1ZSkucHJvcGFnYXRlKHRoaXMudG8pO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgLy8gdXNlIHByb3RvdHlwZSBjaGFpblxuICAgICAgICAgICAgb2JqLmdldFByb3AoJ19fcHJvdG9fXycpLnByb3BhZ2F0ZSh0aGlzKTtcbiAgICAgICAgfVxuICAgIH1cblxuICAgIC8qKlxuICAgICAqIEBvdmVycmlkZVxuICAgICAqL1xuICAgIGVxdWFscyhvdGhlcikge1xuICAgICAgICBpZiAoIShvdGhlciBpbnN0YW5jZW9mIFJlYWRQcm9wKSkgcmV0dXJuIGZhbHNlO1xuICAgICAgICByZXR1cm4gdGhpcy5wcm9wID09PSBvdGhlci5wcm9wXG4gICAgICAgICAgICAmJiB0aGlzLnRvLmVxdWFscyhvdGhlci50byk7XG4gICAgfVxufVxuXG5leHBvcnQgY2xhc3MgV3JpdGVQcm9wIGV4dGVuZHMgQ1NUUiB7XG4gICAgLyoqXG4gICAgICogQ29uc3RydWN0cyBXcml0ZVByb3AuXG4gICAgICogQHBhcmFtIHtzdHJpbmd8bnVsbH0gcHJvcFxuICAgICAqIEBwYXJhbSB7QVZhbH0gZnJvbVxuICAgICAqL1xuICAgIGNvbnN0cnVjdG9yKHByb3AsIGZyb20pIHtcbiAgICAgICAgc3VwZXIoKTtcbiAgICAgICAgdGhpcy5wcm9wID0gcHJvcDtcbiAgICAgICAgdGhpcy5mcm9tID0gZnJvbTtcbiAgICB9XG5cbiAgICAvKipcbiAgICAgKiBAb3ZlcnJpZGVcbiAgICAgKi9cbiAgICBhZGRUeXBlKG9iaikge1xuICAgICAgICBpZiAoIShvYmogaW5zdGFuY2VvZiAodHlwZXMuT2JqVHlwZSkpKSByZXR1cm47XG4gICAgICAgIGNvbnN0IG93blByb3AgPSBvYmouZ2V0UHJvcCh0aGlzLnByb3ApO1xuICAgICAgICB0aGlzLmZyb20ucHJvcGFnYXRlKG93blByb3ApO1xuICAgICAgICAvLyBIYW5kbGUgJ3Byb3RvdHlwZU9mJyB3aGVuIHdyaXRpbmcgdG8gJ3Byb3RvdHlwZSdcbiAgICAgICAgaWYgKHRoaXMucHJvcCA9PT0gJ3Byb3RvdHlwZScpIHtcbiAgICAgICAgICAgIHRoaXMuZnJvbS5nZXRUeXBlcygpLmZvckVhY2goKHRwKSA9PiB7XG4gICAgICAgICAgICAgICAgdHAucHJvdG90eXBlT2YuYWRkVHlwZShvYmopO1xuICAgICAgICAgICAgfSk7XG4gICAgICAgIH1cbiAgICAgICAgLy8gV2hlbiBhc3NpZ25pbmcgRm5UeXBlIHRvIGEgcHJvcCxcbiAgICAgICAgdGhpcy5mcm9tLmdldFR5cGVzKCkuZm9yRWFjaCgoZm4pID0+IHtcbiAgICAgICAgICAgIGlmICghKGZuIGluc3RhbmNlb2YgKHR5cGVzLkZuVHlwZSkpKSByZXR1cm47XG4gICAgICAgICAgICAvLyBvYmoncyBwcm90b3R5cGVPZiA9PiBzZWxmQVZhbCBvZiBudWxsIGNvbnRleHRcbiAgICAgICAgICAgIGNvbnN0IFtzZWxmQVZhbCwsXSA9IGZuLmdldEZ1bkVudihjc2MuQ2FsbFNpdGVDb250ZXh0Lm51bGxDb250ZXh0KTtcbiAgICAgICAgICAgIG9iai5wcm90b3R5cGVPZi5nZXRUeXBlcygpLmZvckVhY2goKGN0b3IpID0+IHtcbiAgICAgICAgICAgICAgICBpZiAoY3RvciBpbnN0YW5jZW9mICh0eXBlcy5GblR5cGUpKVxuICAgICAgICAgICAgICAgICAgICBzZWxmQVZhbC5hZGRUeXBlKGN0b3IuZ2V0SW5zdGFuY2UoKSk7XG4gICAgICAgICAgICB9KTtcbiAgICAgICAgfSk7XG4gICAgfVxufVxuXG5leHBvcnQgY2xhc3MgSXNBZGRlZCBleHRlbmRzIENTVFIge1xuICAgIC8qKlxuICAgICAqIENvbnN0cnVjdHMgSXNBZGRlZC5cbiAgICAgKiBAcGFyYW0ge0FWYWx9IG90aGVyXG4gICAgICogQHBhcmFtIHtBVmFsfSB0YXJnZXRcbiAgICAgKi9cbiAgICBjb25zdHJ1Y3RvcihvdGhlciwgdGFyZ2V0KSB7XG4gICAgICAgIHN1cGVyKCk7XG4gICAgICAgIHRoaXMub3RoZXIgPSBvdGhlcjtcbiAgICAgICAgdGhpcy50YXJnZXQgPSB0YXJnZXQ7XG4gICAgfVxuXG4gICAgLyoqXG4gICAgICogQG92ZXJyaWRlXG4gICAgICovXG4gICAgYWRkVHlwZSh0eXBlKSB7XG4gICAgICAgIGlmICgodHlwZSA9PT0gdHlwZXMuUHJpbU51bWJlclxuICAgICAgICAgICAgfHwgdHlwZSA9PT0gdHlwZXMuUHJpbUJvb2xlYW4pXG4gICAgICAgICAgICAmJiAodGhpcy5vdGhlci5oYXNUeXBlKHR5cGVzLlByaW1OdW1iZXIpXG4gICAgICAgICAgICB8fCB0aGlzLm90aGVyLmhhc1R5cGUodHlwZXMuUHJpbUJvb2xlYW4pKSkge1xuICAgICAgICAgICAgdGhpcy50YXJnZXQuYWRkVHlwZSh0eXBlcy5QcmltTnVtYmVyKTtcbiAgICAgICAgfVxuICAgICAgICBpZiAodHlwZSA9PT0gdHlwZXMuUHJpbVN0cmluZ1xuICAgICAgICAgICAgJiYgIXRoaXMub3RoZXIuaXNFbXB0eSgpKSB7XG4gICAgICAgICAgICB0aGlzLnRhcmdldC5hZGRUeXBlKHR5cGVzLlByaW1TdHJpbmcpO1xuICAgICAgICB9XG4gICAgfVxufVxuXG5mdW5jdGlvbiBfcHJlcGFyZVJlc3RBVmFsRnJvbUFyZ3Mobm9kZSwgY3VyU3RhdHVzLCBhcmdzLCBzdGFydEluZGV4KSB7XG4gICAgY29uc3QgcmVzdEFWYWwgPSBjR2VuLmdldFJlc3RBVmFsKG5vZGUsIGN1clN0YXR1cyk7XG4gICAgZm9yIChsZXQgaSA9IHN0YXJ0SW5kZXg7IGkgPCBhcmdzLmxlbmd0aDsgaSsrKSB7XG4gICAgICAgIHJlc3RBVmFsLnByb3BhZ2F0ZShuZXcgV3JpdGVQcm9wKFN0cmluZyhpIC0gc3RhcnRJbmRleCksIGFyZ3NbaV0pKTtcbiAgICAgICAgcmVzdEFWYWwucHJvcGFnYXRlKG5ldyBXcml0ZVByb3AobnVsbCwgYXJnc1tpXSkpO1xuICAgIH1cbiAgICByZXR1cm4gcmVzdEFWYWw7XG59XG5cbmZ1bmN0aW9uIF9jb25uZWN0VG9QYXJhbWV0ZXIocGFyYW1zLCBmdW5TdGF0dXMsIGFyZ3MpIHtcbiAgICBmb3IgKGxldCBpID0gMDsgaSA8IGFyZ3MubGVuZ3RoICYmIGkgPCBwYXJhbXMubGVuZ3RoOyBpKyspIHtcbiAgICAgICAgaWYgKHBhcmFtc1tpXS50eXBlID09PSAnUmVzdEVsZW1lbnQnKSB7XG4gICAgICAgICAgICBsZXQgcmVzdEFWYWwgPSBfcHJlcGFyZVJlc3RBVmFsRnJvbUFyZ3MocGFyYW1zW2ldLCBmdW5TdGF0dXMsIGFyZ3MsIGkpO1xuICAgICAgICAgICAgY0dlbi5jb25uZWN0UGF0dGVybihwYXJhbXNbaV0sIGZ1blN0YXR1cywgcmVzdEFWYWwpO1xuICAgICAgICAgICAgYnJlYWs7XG4gICAgICAgIH1cbiAgICAgICAgLy8gVXNpbmcgZnVuU3RhdHVzIGZvciBhbmFseXppbmcgZGVmYXVsdHMgaXMgc2FmZVxuICAgICAgICBjR2VuLmNvbm5lY3RQYXR0ZXJuKHBhcmFtc1tpXSwgZnVuU3RhdHVzLCBhcmdzW2ldKTtcbiAgICB9XG59XG5cbmV4cG9ydCBjbGFzcyBJc0NhbGxlZSBleHRlbmRzIENTVFIge1xuICAgIC8qKlxuICAgICAqIENvbnN0cnVjdHMgSXNDYWxsZWUuXG4gICAgICogQHBhcmFtIHtBVmFsfSBzZWxmXG4gICAgICogQHBhcmFtIHtBcnJheS48QVZhbD59IGFyZ3NcbiAgICAgKiBAcGFyYW0ge0FWYWx9IHJldFxuICAgICAqIEBwYXJhbSB7QVZhbH0gZXhjXG4gICAgICogQHBhcmFtIHtDYWxsU2l0ZUNvbnRleHR9IGRlbHRhXG4gICAgICovXG4gICAgY29uc3RydWN0b3Ioc2VsZiwgYXJncywgcmV0LCBleGMsIGRlbHRhKSB7XG4gICAgICAgIHN1cGVyKCk7XG4gICAgICAgIHRoaXMuc2VsZiA9IHNlbGY7XG4gICAgICAgIHRoaXMuYXJncyA9IGFyZ3M7XG4gICAgICAgIHRoaXMucmV0ID0gcmV0O1xuICAgICAgICB0aGlzLmV4YyA9IGV4YztcbiAgICAgICAgdGhpcy5kZWx0YSA9IGRlbHRhO1xuICAgIH1cblxuICAgIC8qKlxuICAgICAqIEBvdmVycmlkZVxuICAgICAqL1xuICAgIGFkZFR5cGUoZikge1xuICAgICAgICBpZiAoIShmIGluc3RhbmNlb2YgKHR5cGVzLkZuVHlwZSkpKSByZXR1cm47XG4gICAgICAgIGNvbnN0IGZCbG9jayA9IGYub3JpZ2luTm9kZS5ib2R5WydAYmxvY2snXTtcbiAgICAgICAgY29uc3QgY0Jsb2NrID0gZkJsb2NrLmhhc1BhcmFtU2NvcGUgPyBmQmxvY2sucGFyZW4gOiBmQmxvY2s7XG4gICAgICAgIGNvbnN0IGRlbHRhRm4gPSB0aGlzLmRlbHRhLnRydW5jYXRlRm9yKGYpO1xuICAgICAgICBjb25zdCBbc2VsZkFWYWwsIHJldEFWYWwsIGV4Y0FWYWxdID0gZi5nZXRGdW5FbnYoZGVsdGFGbik7XG4gICAgICAgIGNvbnN0IG5ld1NDID0gY0Jsb2NrLmdldFNjb3BlSW5zdGFuY2UoZi5zYywgZGVsdGFGbik7XG4gICAgICAgIGNvbnN0IGZ1blN0YXR1c1xuICAgICAgICAgICAgPSBuZXcgc3RhdHVzLlN0YXR1cyhzZWxmQVZhbCwgcmV0QVZhbCwgZXhjQVZhbCxcbiAgICAgICAgICAgIGRlbHRhRm4sIG5ld1NDKTtcblxuICAgICAgICAvLyBhcnJvdyBmdW5jdGlvbiBzaG91bGQgdXNlIGJvdW5kVGhpcyBhbmQgaWdub3JlIHRoZSByZWNlaXZlciBBVmFsXG4gICAgICAgIGNvbnN0IGVmZmVjdGl2ZVNlbGYgPSBmLmJvdW5kVGhpcyA/IGYuYm91bmRUaGlzIDogdGhpcy5zZWxmO1xuICAgICAgICBlZmZlY3RpdmVTZWxmLnByb3BhZ2F0ZShzZWxmQVZhbCk7XG5cbiAgICAgICAgX2Nvbm5lY3RUb1BhcmFtZXRlcihmLm9yaWdpbk5vZGUucGFyYW1zLCBmdW5TdGF0dXMsIHRoaXMuYXJncyk7XG5cbiAgICAgICAgLy8gZm9yIGFyZ3VtZW50cyBvYmplY3RcbiAgICAgICAgaWYgKGYub3JpZ2luTm9kZS5ib2R5WydAYmxvY2snXS51c2VBcmd1bWVudHNPYmplY3QpIHtcbiAgICAgICAgICAgIGNvbnN0IGFyZ09iaiA9IGYuZ2V0QXJndW1lbnRzT2JqZWN0KGRlbHRhRm4pO1xuICAgICAgICAgICAgbmV3U0MuZ2V0QVZhbE9mKCdhcmd1bWVudHMnKS5hZGRUeXBlKGFyZ09iaik7XG4gICAgICAgICAgICBmb3IgKGxldCBpID0gMDsgaSA8IHRoaXMuYXJncy5sZW5ndGg7IGkrKykge1xuICAgICAgICAgICAgICAgIHRoaXMuYXJnc1tpXS5wcm9wYWdhdGUoYXJnT2JqLmdldFByb3AoaSArICcnKSk7XG4gICAgICAgICAgICAgICAgdGhpcy5hcmdzW2ldLnByb3BhZ2F0ZShhcmdPYmouZ2V0UHJvcChudWxsKSk7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBhcmdPYmouZ2V0UHJvcCgnY2FsbGVlJykuYWRkVHlwZShmKTtcbiAgICAgICAgICAgIGFyZ09iai5nZXRQcm9wKCdsZW5ndGgnKS5hZGRUeXBlKHR5cGVzLlByaW1OdW1iZXIpO1xuICAgICAgICB9XG5cbiAgICAgICAgLy8gY29uc3RyYWludCBnZW5lcmF0aW9uIGZvciB0aGUgZnVuY3Rpb24gYm9keVxuICAgICAgICBjR2VuLmFkZENvbnN0cmFpbnRzKGYub3JpZ2luTm9kZS5ib2R5LCBmdW5TdGF0dXMpO1xuXG4gICAgICAgIC8vIGdldCByZXR1cm5cbiAgICAgICAgcmV0QVZhbC5wcm9wYWdhdGUodGhpcy5yZXQpO1xuICAgICAgICAvLyBnZXQgZXhjZXB0aW9uXG4gICAgICAgIGV4Y0FWYWwucHJvcGFnYXRlKHRoaXMuZXhjKTtcbiAgICB9XG59XG5cbmV4cG9ydCBjbGFzcyBJc0N0b3IgZXh0ZW5kcyBDU1RSIHtcbiAgICAvKipcbiAgICAgKiBDb25zdHJ1Y3RzIElzQ3Rvci5cbiAgICAgKiBAcGFyYW0ge0FycmF5LjxBVmFsPn1hcmdzXG4gICAgICogQHBhcmFtIHtBVmFsfSByZXRcbiAgICAgKiBAcGFyYW0ge0FWYWx9IGV4Y1xuICAgICAqIEBwYXJhbSB7QVZhbH0gZGVsdGFcbiAgICAgKi9cbiAgICBjb25zdHJ1Y3RvcihhcmdzLCByZXQsIGV4YywgZGVsdGEpIHtcbiAgICAgICAgc3VwZXIoKTtcbiAgICAgICAgdGhpcy5hcmdzID0gYXJncztcbiAgICAgICAgdGhpcy5yZXQgPSByZXQ7XG4gICAgICAgIHRoaXMuZXhjID0gZXhjO1xuICAgICAgICB0aGlzLmRlbHRhID0gZGVsdGE7XG4gICAgfVxuXG4gICAgLyoqXG4gICAgICogQG92ZXJyaWRlXG4gICAgICovXG4gICAgYWRkVHlwZShmKSB7XG4gICAgICAgIC8vIE9ubHkgbm9uLWFycm93IGZ1bmN0aW9ucyBjYW4gY3JlYXRlIGluc3RhbmNlcy5cbiAgICAgICAgaWYgKCEoZiBpbnN0YW5jZW9mICh0eXBlcy5GblR5cGUpKSB8fCBmLmJvdW5kVGhpcykge1xuICAgICAgICAgICAgcmV0dXJuO1xuICAgICAgICB9XG4gICAgICAgIGNvbnN0IGRlbHRhRm4gPSB0aGlzLmRlbHRhLnRydW5jYXRlRm9yKGYpO1xuICAgICAgICBjb25zdCBbc2VsZkFWYWwsIHJldEFWYWwsIGV4Y0FWYWxdID0gZi5nZXRGdW5FbnYoZGVsdGFGbik7XG4gICAgICAgIGNvbnN0IG5ld1NDID0gZi5vcmlnaW5Ob2RlLmJvZHlbJ0BibG9jayddLmdldFNjb3BlSW5zdGFuY2UoZi5zYywgZGVsdGFGbik7XG4gICAgICAgIGNvbnN0IGZ1blN0YXR1c1xuICAgICAgICAgICAgPSBuZXcgc3RhdHVzLlN0YXR1cyhcbiAgICAgICAgICAgIHNlbGZBVmFsLFxuICAgICAgICAgICAgLy8gSW4gY29uc3RydWN0b3IsIHdlIGNhbiBleHBsaWNpdGx5IHJldHVybiBvbmx5IE9ialR5cGUuXG4gICAgICAgICAgICBuZXcgSWZPYmpUeXBlKHJldEFWYWwpLFxuICAgICAgICAgICAgZXhjQVZhbCxcbiAgICAgICAgICAgIGRlbHRhRm4sXG4gICAgICAgICAgICBuZXdTQyk7XG4gICAgICAgIC8vIGYncyBpbnN0YW5jZSBpcyBib3VuZCB0byAndGhpcy4nXG4gICAgICAgIGNvbnN0IG5ld09iaiA9IGYuZ2V0SW5zdGFuY2UoKTtcbiAgICAgICAgc2VsZkFWYWwuYWRkVHlwZShuZXdPYmopO1xuXG4gICAgICAgIF9jb25uZWN0VG9QYXJhbWV0ZXIoZi5vcmlnaW5Ob2RlLnBhcmFtcywgZnVuU3RhdHVzLCB0aGlzLmFyZ3MpO1xuXG4gICAgICAgIC8vIGZvciBhcmd1bWVudHMgb2JqZWN0XG4gICAgICAgIGlmIChmLm9yaWdpbk5vZGUuYm9keVsnQGJsb2NrJ10udXNlQXJndW1lbnRzT2JqZWN0KSB7XG4gICAgICAgICAgICBjb25zdCBhcmdPYmogPSBmLmdldEFyZ3VtZW50c09iamVjdChkZWx0YUZuKTtcbiAgICAgICAgICAgIG5ld1NDLmdldEFWYWxPZignYXJndW1lbnRzJykuYWRkVHlwZShhcmdPYmopO1xuICAgICAgICAgICAgZm9yIChsZXQgaSA9IDA7IGkgPCB0aGlzLmFyZ3MubGVuZ3RoOyBpKyspIHtcbiAgICAgICAgICAgICAgICB0aGlzLmFyZ3NbaV0ucHJvcGFnYXRlKGFyZ09iai5nZXRQcm9wKGkgKyAnJykpO1xuICAgICAgICAgICAgICAgIHRoaXMuYXJnc1tpXS5wcm9wYWdhdGUoYXJnT2JqLmdldFByb3AobnVsbCkpO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgYXJnT2JqLmdldFByb3AoJ2NhbGxlZScpLmFkZFR5cGUoZik7XG4gICAgICAgICAgICBhcmdPYmouZ2V0UHJvcCgnbGVuZ3RoJykuYWRkVHlwZSh0eXBlcy5QcmltTnVtYmVyKTtcbiAgICAgICAgfVxuXG4gICAgICAgIC8vIGNvbnN0cmFpbnQgZ2VuZXJhdGlvbiBmb3IgdGhlIGZ1bmN0aW9uIGJvZHlcbiAgICAgICAgY0dlbi5hZGRDb25zdHJhaW50cyhmLm9yaWdpbk5vZGUuYm9keSwgZnVuU3RhdHVzKTtcblxuICAgICAgICAvLyBwcm92aWRlIHR3byBraW5kcyBvZiByZXN1bHQgb2YgJ25ldydcbiAgICAgICAgdGhpcy5yZXQuYWRkVHlwZShuZXdPYmopO1xuICAgICAgICByZXRBVmFsLnByb3BhZ2F0ZSh0aGlzLnJldCk7XG4gICAgICAgIC8vIGdldCBleGNlcHRpb25cbiAgICAgICAgZXhjQVZhbC5wcm9wYWdhdGUodGhpcy5leGMpO1xuICAgIH1cbn1cblxuLy8gaWdub3JlIG5vbiBvYmplY3QgdHlwZXNcbmNsYXNzIElmT2JqVHlwZSBleHRlbmRzIENTVFIge1xuICAgIC8qKlxuICAgICAqIENvbnN0cnVjdHMgSWZPYmpUeXBlLlxuICAgICAqIEBwYXJhbSB7QVZhbH0gYXZhbFxuICAgICAqL1xuICAgIGNvbnN0cnVjdG9yKGF2YWwpIHtcbiAgICAgICAgc3VwZXIoKTtcbiAgICAgICAgdGhpcy5hdmFsID0gYXZhbDtcbiAgICB9XG5cbiAgICAvKipcbiAgICAgKiBAb3ZlcnJpZGVcbiAgICAgKi9cbiAgICBhZGRUeXBlKHR5cGUpIHtcbiAgICAgICAgaWYgKCEodHlwZSBpbnN0YW5jZW9mIHR5cGVzLk9ialR5cGUpKSByZXR1cm47XG4gICAgICAgIHRoaXMuYXZhbC5hZGRUeXBlKHR5cGUpO1xuICAgIH1cbn1cbiIsIi8qKlxuICogQGZpbGUgRGVmaW5lcyBjb250ZXh0IGZvciBrLUNGQSBhbmFseXNpc1xuICogQGF1dGhvciBzZXdvbjMyNi5raW1Ac2Ftc3VuZy5jb21cbiAqL1xuXG5cbi8qKlxuICogSW5pdGlhbCBzZW5zaXRpdml0eSBwYXJhbWV0ZXIuXG4gKiBAdHlwZSB7e21heERlcHRoSzogbnVtYmVyLCBjb250ZXh0TGVuZ3RoT2ZGdW5jOiBzZW5zaXRpdml0eVBhcmFtZXRlci5jb250ZXh0TGVuZ3RoT2ZGdW5jfX1cbiAqL1xuZXhwb3J0IGNvbnN0IHNlbnNpdGl2aXR5UGFyYW1ldGVyID0ge1xuICAgIC8vIG1heGltdW0gbGVuZ3RoIG9mIGNvbnRleHRcbiAgICBtYXhEZXB0aEs6IDAsXG4gICAgLy9cbiAgICBjb250ZXh0TGVuZ3RoT2ZGdW5jOiBmdW5jdGlvbiAoZm4pIHtcbiAgICAgICAgcmV0dXJuIDA7XG4gICAgfVxufTtcblxuLyoqXG4gKiBDaGFuZ2VzIHRoZSBzZW5zaXRpdml0eSBwYXJhbWV0ZXIuXG4gKiBAcGFyYW0gcGFyYW1cbiAqL1xuZXhwb3J0IGZ1bmN0aW9uIGNoYW5nZVNlbnNpdGl2aXR5UGFyYW1ldGVyKHBhcmFtKSB7XG4gICAgc2Vuc2l0aXZpdHlQYXJhbWV0ZXIubWF4RGVwdGhLID0gcGFyYW0ubWF4RGVwdGhLO1xuICAgIHNlbnNpdGl2aXR5UGFyYW1ldGVyLmNvbnRleHRMZW5ndGhPZkZ1bmMgPSBwYXJhbS5jb250ZXh0TGVuZ3RoT2ZGdW5jO1xufVxuXG5leHBvcnQgY2xhc3MgQ2FsbFNpdGVDb250ZXh0IHtcbiAgICAvKipcbiAgICAgKiBDb25zdHJ1Y3QgYSBDYWxsU2l0ZUNvbnRleHQgZnJvbSBgbGlzdGAuXG4gICAgICogQHBhcmFtIGxpc3RcbiAgICAgKi9cbiAgICBjb25zdHJ1Y3RvcihsaXN0KSB7XG4gICAgICAgIGZvciAobGV0IGN0eCBvZiBDYWxsU2l0ZUNvbnRleHQuY29udGV4dFBvb2wudmFsdWVzKCkpIHtcbiAgICAgICAgICAgIGlmIChjdHguX2hhc1NhbWVMaXN0KGxpc3QpKSB7XG4gICAgICAgICAgICAgICAgLy8gdXNlIGV4aXN0aW5nIGNvbnRleHRcbiAgICAgICAgICAgICAgICByZXR1cm4gY3R4O1xuICAgICAgICAgICAgfVxuICAgICAgICB9XG4gICAgICAgIC8vIGNsb25lIHRoZSBnaXZlbiBsaXN0XG4gICAgICAgIGlmIChsaXN0ID09PSBudWxsKSB7XG4gICAgICAgICAgICB0aGlzLmNzTGlzdCA9IG51bGw7XG4gICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgICB0aGlzLmNzTGlzdCA9IGxpc3Quc2xpY2UoMCk7XG4gICAgICAgIH1cbiAgICAgICAgLy8gYWRkIHRoZSBjdXJyZW50IGluc3RhbmNlIHRvIHRoZSBwb29sXG4gICAgICAgIENhbGxTaXRlQ29udGV4dC5jb250ZXh0UG9vbC5hZGQodGhpcyk7XG4gICAgfVxuXG4gICAgLyoqXG4gICAgICogQ2hlY2sgd2hldGhlciB0aGUgbGlzdCByZXByZXNlbnQgdGhlIHNhbWUgY29udGV4dC5cbiAgICAgKiBAcHJpdmF0ZVxuICAgICAqIEBwYXJhbSBsaXN0IC0gYXJyYXkgY29tcG9zZWQgb2YgY29udGV4dCBlbGVtZW50c1xuICAgICAqIEByZXR1cm4ge2Jvb2xlYW59XG4gICAgICovXG4gICAgX2hhc1NhbWVMaXN0KGxpc3QpIHtcbiAgICAgICAgaWYgKHRoaXMuY3NMaXN0ID09PSBudWxsKSB7XG4gICAgICAgICAgICByZXR1cm4gbGlzdCA9PT0gbnVsbDtcbiAgICAgICAgfVxuICAgICAgICBpZiAobGlzdCA9PT0gbnVsbCkge1xuICAgICAgICAgICAgcmV0dXJuIHRoaXMuY3NMaXN0ID09PSBudWxsO1xuICAgICAgICB9XG4gICAgICAgIGlmICh0aGlzLmNzTGlzdC5sZW5ndGggIT09IGxpc3QubGVuZ3RoKSB7XG4gICAgICAgICAgICByZXR1cm4gZmFsc2U7XG4gICAgICAgIH1cbiAgICAgICAgZm9yIChsZXQgaSA9IDA7IGkgPCB0aGlzLmNzTGlzdC5sZW5ndGg7IGkrKykge1xuICAgICAgICAgICAgaWYgKHRoaXMuY3NMaXN0W2ldICE9PSBsaXN0W2ldKSByZXR1cm4gZmFsc2U7XG4gICAgICAgIH1cbiAgICAgICAgcmV0dXJuIHRydWU7XG4gICAgfVxuXG4gICAgLyoqXG4gICAgICogUmV0dXJucyB0aGUgY29udGV4dCB3aGljaCBpcyBteXNlbGYgKyBjYWxsU2l0ZS5cbiAgICAgKiBJZiBJIGFtIG51bGxDb250ZXh0LCB0aGUgcmVzdWx0IGlzIG15c2VsZi5cbiAgICAgKiBAcGFyYW0gY2FsbFNpdGUgLSBhIGNhbGwtc2l0ZSB0byBhcHBlbmRcbiAgICAgKiBAcmV0dXJuIHtDYWxsU2l0ZUNvbnRleHR9XG4gICAgICovXG4gICAgYXBwZW5kT25lKGNhbGxTaXRlKSB7XG4gICAgICAgIC8vIGlmIG51bGwgY29udGV4dCwgcmVzdWx0IGlzIGl0c2VsZlxuICAgICAgICBpZiAodGhpcyA9PT0gQ2FsbFNpdGVDb250ZXh0Lm51bGxDb250ZXh0KSB7XG4gICAgICAgICAgICByZXR1cm4gdGhpcztcbiAgICAgICAgfVxuICAgICAgICAvLyB1c2UgY29uY2F0IHRvIGNyZWF0ZSBhIG5ldyBhcnJheVxuICAgICAgICAvLyBvbGRlc3Qgb25lIGNvbWVzIGZpcnN0XG4gICAgICAgIGNvbnN0IGFwcGVuZGVkID0gdGhpcy5jc0xpc3QuY29uY2F0KGNhbGxTaXRlKTtcbiAgICAgICAgaWYgKGFwcGVuZGVkLmxlbmd0aCA+IHNlbnNpdGl2aXR5UGFyYW1ldGVyLm1heERlcHRoSykge1xuICAgICAgICAgICAgYXBwZW5kZWQuc2hpZnQoKTtcbiAgICAgICAgfVxuICAgICAgICByZXR1cm4gbmV3IENhbGxTaXRlQ29udGV4dChhcHBlbmRlZCk7XG4gICAgfVxuXG4gICAgLyoqXG4gICAgICogVHJ1bmNhdGUgY29udGV4dCBhY2NvcmRpbmcgdG8gdGhlIGdpdmVuIGZ1bmN0aW9uLlxuICAgICAqIEBwYXJhbSB7Rm5UeXBlfSBmblxuICAgICAqIEByZXR1cm4ge0NhbGxTaXRlQ29udGV4dH1cbiAgICAgKi9cbiAgICB0cnVuY2F0ZUZvcihmbikge1xuICAgICAgICAvLyBmb3IgbnVsbENvbnRleHQsXG4gICAgICAgIGlmICh0aGlzID09PSBDYWxsU2l0ZUNvbnRleHQubnVsbENvbnRleHQpIHtcbiAgICAgICAgICAgIHJldHVybiB0aGlzO1xuICAgICAgICB9XG4gICAgICAgIC8vIGNvbXB1dGUgdGhlIGxlbmd0aCBvZiB0aGUgY29udGV4dFxuICAgICAgICBjb25zdCBjb250ZXh0TGVuZ3RoID0gc2Vuc2l0aXZpdHlQYXJhbWV0ZXIuY29udGV4dExlbmd0aE9mRnVuYyhmbik7XG4gICAgICAgIGlmIChjb250ZXh0TGVuZ3RoID09PSAwKSB7XG4gICAgICAgICAgICAvLyBjb250ZXh0IG9mIGxlbmd0aCAwXG4gICAgICAgICAgICByZXR1cm4gQ2FsbFNpdGVDb250ZXh0LmVwc2lsb25Db250ZXh0O1xuICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgICAgLy8gY2hvb3NlIGxhc3Qgc2V2ZXJhbCBjYWxsLXNpdGVzXG4gICAgICAgICAgICByZXR1cm4gbmV3IENhbGxTaXRlQ29udGV4dCh0aGlzLmNzTGlzdC5zbGljZSgtY29udGV4dExlbmd0aCkpO1xuICAgICAgICB9XG4gICAgfVxuXG4gICAgLyoqXG4gICAgICogUmV0dXJucyB0aGUgc3RyaW5nIHJlcHJlc2VudGF0aW9uXG4gICAgICogQHJldHVybiB7c3RyaW5nfVxuICAgICAqL1xuICAgIHRvU3RyaW5nKCkge1xuICAgICAgICByZXR1cm4gdGhpcy5jc0xpc3QudG9TdHJpbmcoKTtcbiAgICB9XG59XG5cbi8qKlxuICogRGVjbGFyaW5nIGNsYXNzIGZpZWxkcyBmb3IgQ2FsbFNpdGVDb250ZXh0XG4gKiBAc3RhdGljXG4gKi9cbkNhbGxTaXRlQ29udGV4dC5jb250ZXh0UG9vbCA9IG5ldyBTZXQoKTtcblxuLyoqXG4gKiBudWxsQ29udGV4dCBpcyBmb3IgZnVuY3Rpb25zIHRoYXQgbmV2ZXIgYmUgY2FsbGVkXG4gKiBAc3RhdGljXG4gKi9cbkNhbGxTaXRlQ29udGV4dC5udWxsQ29udGV4dCA9IG5ldyBDYWxsU2l0ZUNvbnRleHQobnVsbCk7XG5cbi8qKlxuICogZXBzaWxvbkNvbnRleHQgaXMgZm9yIGNvbnRleHQgb2YgbGVuZ3RoIDBcbiAqIEBzdGF0aWNcbiAqL1xuQ2FsbFNpdGVDb250ZXh0LmVwc2lsb25Db250ZXh0ID0gbmV3IENhbGxTaXRlQ29udGV4dChbXSk7XG4iLCIvKipcbiAqIEBmaWxlIERlZmluZXMgU3RhdHVzLlxuICogQGF1dGhvciBzZXdvbjMyNi5raW1Ac2Ftc3VuZy5jb21cbiAqL1xuZXhwb3J0IGNsYXNzIFN0YXR1cyB7XG4gICAgLyoqXG4gICAgICogQ29uc3RydWN0cyBTdGF0dXMuXG4gICAgICogQHBhcmFtIHtBVmFsfSBzZWxmXG4gICAgICogQHBhcmFtIHtBVmFsfSByZXRcbiAgICAgKiBAcGFyYW0ge0FWYWx9IGV4Y1xuICAgICAqIEBwYXJhbSB7Q2FsbFNpdGVDb250ZXh0fSBkZWx0YVxuICAgICAqIEBwYXJhbSB7U2NvcGV9IHNjXG4gICAgICovXG4gICAgY29uc3RydWN0b3Ioc2VsZiwgcmV0LCBleGMsIGRlbHRhLCBzYykge1xuICAgICAgICB0aGlzLnNlbGYgPSBzZWxmO1xuICAgICAgICB0aGlzLnJldCA9IHJldDtcbiAgICAgICAgdGhpcy5leGMgPSBleGM7XG4gICAgICAgIHRoaXMuZGVsdGEgPSBkZWx0YTtcbiAgICAgICAgdGhpcy5zYyA9IHNjO1xuICAgIH1cblxuICAgIC8qKlxuICAgICAqIENoZWNrcyBlcXVhbGl0eSB3aXRoIG90aGVyIFN0YXR1c1xuICAgICAqIEBwYXJhbSB7U3RhdHVzfSBvdGhlclxuICAgICAqIEByZXR1cm4ge2Jvb2xlYW59XG4gICAgICovXG4gICAgZXF1YWxzKG90aGVyKSB7XG4gICAgICAgIHJldHVybiB0aGlzLnNlbGYgPT09IG90aGVyLnNlbGYgJiZcbiAgICAgICAgICAgIHRoaXMucmV0ID09PSBvdGhlci5yZXQgJiZcbiAgICAgICAgICAgIHRoaXMuZXhjID09PSBvdGhlci5leGMgJiZcbiAgICAgICAgICAgIHRoaXMuZGVsdGEgPT09IG90aGVyLmRlbHRhICYmXG4gICAgICAgICAgICB0aGlzLnNjID09PSBvdGhlci5zYztcbiAgICB9XG5cbiAgICAvKipcbiAgICAgKiBSZXR1cm5zIGEgbmV3IFN0YXR1cyxcbiAgICAgKiB3aG9zZSBpbnN0YW5jZSBmaWVsZHMgYXJlIGNoYW5nZWQgZnJvbSBgdGhpc2AgdXNpbmcgYGNoYW5nZWRTdGF0dXNgLlxuICAgICAqIEBwYXJhbSBjaGFuZ2VTdGF0dXNcbiAgICAgKiBAcmV0dXJuIHtTdGF0dXN9XG4gICAgICovXG4gICAgZ2V0TmV3U3RhdHVzKGNoYW5nZVN0YXR1cykge1xuICAgICAgICBjb25zdCBuZXdTdGF0dXMgPSBuZXcgU3RhdHVzO1xuICAgICAgICBmb3IgKGxldCBwIGluIHRoaXMpIHtcbiAgICAgICAgICAgIGlmICh0aGlzLmhhc093blByb3BlcnR5KHApKSB7XG4gICAgICAgICAgICAgICAgaWYgKGNoYW5nZVN0YXR1cy5oYXNPd25Qcm9wZXJ0eShwKSkge1xuICAgICAgICAgICAgICAgICAgICBuZXdTdGF0dXNbcF0gPSBjaGFuZ2VTdGF0dXNbcF07XG4gICAgICAgICAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgbmV3U3RhdHVzW3BdID0gdGhpc1twXTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICB9XG4gICAgICAgIH1cbiAgICAgICAgcmV0dXJuIG5ld1N0YXR1cztcbiAgICB9XG59XG4iLCIvKipcbiAqIEBmaWxlIERlZmluZXMgZG9tYWlucyBmb3IgdHlwZXMuXG4gKiBAYXV0aG9yIHNld29uMzI2LmtpbUBzYW1zdW5nLmNvbVxuICovXG5cbi8vIGZvciBERUJVR1xudmFyIGNvdW50ID0gMDtcblxuLyoqXG4gKiBBVmFscyByZXByZXNlbnQgc2V0cyBvZiB0eXBlcy5cbiAqIFRoZWlyIGZvcndhcmRzIGZpZWxkcyByZXByZXNlbnQgdGhlIHByb3BhZ2F0aW9uIGdyYXBoLlxuICovXG5leHBvcnQgY2xhc3MgQVZhbCB7XG4gICAgLyoqXG4gICAgICogQ29uc3RydWN0IGFuIEFWYWwuXG4gICAgICogUGFyYW1ldGVyIHR5cGUgaXMgb3B0aW9uYWwuXG4gICAgICogQHBhcmFtIHtUeXBlfSB0eXBlIC0gbWFrZXMgQVZhbCBjb250YWluaW5nIHRoZSB0eXBlXG4gICAgICovXG4gICAgY29uc3RydWN0b3IodHlwZSkge1xuICAgICAgICAvLyB0eXBlOiBjb250YWluZWQgdHlwZXNcbiAgICAgICAgLy8gV2UgYXNzdW1lIHR5cGVzIGFyZSBkaXN0aW5ndWlzaGFibGUgYnkgJz09PSdcbiAgICAgICAgaWYgKHR5cGUpIHRoaXMudHlwZXMgPSBuZXcgU2V0KFt0eXBlXSk7XG4gICAgICAgIGVsc2UgdGhpcy50eXBlcyA9IG5ldyBTZXQoKTtcbiAgICAgICAgLy8gZm9yd2FyZHM6IHByb3BhZ2F0aW9uIHRhcmdldHNcbiAgICAgICAgLy8gV2UgYXNzdW1lIHRhcmdldHMgYXJlIGRpc3Rpbmd1aXNoYWJsZSBieSAnZXF1YWxzJyBtZXRob2RcbiAgICAgICAgdGhpcy5mb3J3YXJkcyA9IG5ldyBTZXQoKTtcbiAgICAgICAgLy8gZm9yIERFQlVHXG4gICAgICAgIHRoaXMuX2lkID0gY291bnQrKztcbiAgICB9XG5cbiAgICAvKipcbiAgICAgKiBDaGVjayB3aGV0aGVyIGl0IGhhcyBhbnkgdHlwZVxuICAgICAqIEByZXR1cm4ge2Jvb2xlYW59XG4gICAgICovXG4gICAgaXNFbXB0eSgpIHtcbiAgICAgICAgcmV0dXJuIHRoaXMudHlwZXMuc2l6ZSA9PT0gMDtcbiAgICB9XG5cbiAgICAvKipcbiAgICAgKiBSZXR1cm5zIHRoZSBudW1iZXIgb2YgdHlwZXMgaXQgaGFzLlxuICAgICAqIEByZXR1cm4ge251bWJlcn1cbiAgICAgKi9cbiAgICBnZXRTaXplKCkge1xuICAgICAgICByZXR1cm4gdGhpcy50eXBlcy5zaXplO1xuICAgIH1cblxuICAgIC8qKlxuICAgICAqIFJldHVybnMgdGhlIHNldCBvZiB0eXBlcy5cbiAgICAgKiBAcmV0dXJuIHtTZXQuPFR5cGU+fVxuICAgICAqL1xuICAgIGdldFR5cGVzKCkge1xuICAgICAgICByZXR1cm4gdGhpcy50eXBlcztcbiAgICB9XG5cbiAgICAvKipcbiAgICAgKiBDaGVja3Mgd2hldGhlciBpdCBjb250YWlucyBgdHlwZWAuXG4gICAgICogQHBhcmFtIHtUeXBlfSB0eXBlXG4gICAgICogQHJldHVybiB7Ym9vbGVhbn1cbiAgICAgKi9cbiAgICBoYXNUeXBlKHR5cGUpIHtcbiAgICAgICAgcmV0dXJuIHRoaXMudHlwZXMuaGFzKHR5cGUpO1xuICAgIH1cblxuICAgIC8qKlxuICAgICAqIEFkZCBhIHR5cGUuXG4gICAgICogQHBhcmFtIHtUeXBlfSB0eXBlXG4gICAgICogQHJldHVybiB7Ym9vbGVhbn1cbiAgICAgKi9cbiAgICBhZGRUeXBlKHR5cGUpIHtcbiAgICAgICAgaWYgKHRoaXMudHlwZXMuaGFzKHR5cGUpKSB7XG4gICAgICAgICAgICByZXR1cm4gZmFsc2U7XG4gICAgICAgIH1cbiAgICAgICAgLy8gZ2l2ZW4gdHlwZSBpcyBuZXdcbiAgICAgICAgdGhpcy50eXBlcy5hZGQodHlwZSk7XG4gICAgICAgIC8vIHNlbmQgdG8gcHJvcGFnYXRpb24gdGFyZ2V0c1xuICAgICAgICB0aGlzLmZvcndhcmRzLmZvckVhY2goZndkID0+IHtcbiAgICAgICAgICAgIGZ3ZC5hZGRUeXBlKHR5cGUpO1xuICAgICAgICB9KTtcbiAgICAgICAgcmV0dXJuIHRydWU7XG4gICAgfVxuXG4gICAgLyoqXG4gICAgICogQHBhcmFtIHtBVmFsfSB0YXJnZXRcbiAgICAgKi9cbiAgICBwcm9wYWdhdGUodGFyZ2V0KSB7XG4gICAgICAgIGlmICghdGhpcy5hZGRGb3J3YXJkKHRhcmdldCkpIHJldHVybjtcbiAgICAgICAgLy8gdGFyZ2V0IGlzIG5ld2x5IGFkZGVkXG4gICAgICAgIC8vIHNlbmQgdHlwZXMgdG8gdGhlIG5ldyB0YXJnZXRcbiAgICAgICAgdGhpcy50eXBlcy5mb3JFYWNoKHR5cGUgPT4ge1xuICAgICAgICAgICAgdGFyZ2V0LmFkZFR5cGUodHlwZSk7XG4gICAgICAgIH0pO1xuICAgIH1cblxuICAgIC8qKlxuICAgICAqIEFkZCBhIHByb3BhZ2F0aW9uIHRhcmdldFxuICAgICAqIEBwYXJhbSB7QVZhbH0gZndkXG4gICAgICogQHJldHVybiB7Ym9vbGVhbn0gLSByZXR1cm5zIGZhbHNlIGlmIGl0IGFscmVhZHkgaGFzIHRoZSB0YXJnZXRcbiAgICAgKi9cbiAgICBhZGRGb3J3YXJkKGZ3ZCkge1xuICAgICAgICBmb3IgKGxldCBvbGRGd2Qgb2YgdGhpcy5mb3J3YXJkcykge1xuICAgICAgICAgICAgaWYgKGZ3ZC5lcXVhbHMob2xkRndkKSkge1xuICAgICAgICAgICAgICAgIHJldHVybiBmYWxzZTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgfVxuICAgICAgICB0aGlzLmZvcndhcmRzLmFkZChmd2QpO1xuICAgICAgICByZXR1cm4gdHJ1ZTtcbiAgICB9XG5cbiAgICAvKipcbiAgICAgKiBDaGVjayBpZiB0aGV5IGFyZSB0aGUgc2FtZVxuICAgICAqIEBwYXJhbSB7QVZhbH0gb3RoZXJcbiAgICAgKiBAcmV0dXJuIHtib29sZWFufVxuICAgICAqL1xuICAgIGVxdWFscyhvdGhlcikge1xuICAgICAgICAvLyBzaW1wbGUgcmVmZXJlbmNlIGNvbXBhcmlzb25cbiAgICAgICAgcmV0dXJuIHRoaXMgPT09IG90aGVyO1xuICAgIH1cblxuICAgIC8qKlxuICAgICAqIFRPRE86IGNoZWNrIHdoZXRoZXIgd2UgcmVhbGx5IG5lZWQgdGhpcyBtZXRob2QuXG4gICAgICogQHBhcmFtIHtzdHJpbmd8bnVsbH0gcHJvcFxuICAgICAqIEByZXR1cm4ge0FWYWx9XG4gICAgICovXG4gICAgZ2V0UHJvcChwcm9wKSB7XG4gICAgICAgIGlmICh0aGlzLnByb3BzLmhhcyhwcm9wKSkge1xuICAgICAgICAgICAgcmV0dXJuIHRoaXMucHJvcHMuZ2V0KHByb3ApO1xuICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgICAgcmV0dXJuIEFWYWxOdWxsO1xuICAgICAgICB9XG4gICAgfVxuXG4gICAgLyoqXG4gICAgICogUmV0dXJucyB0aGUgc3RyaW5nIHJlcHJlc2VudGF0aW9uIG9mIHRoZSBBVmFsXG4gICAgICogQHJldHVybiB7c3RyaW5nfVxuICAgICAqL1xuICAgIHRvU3RyaW5nKCkge1xuICAgICAgICBjb25zdCB2aXNpdGVkVHlwZXMgPSBuZXcgU2V0KCk7XG4gICAgICAgIHJldHVybiB0aGlzLl90b1N0cmluZyh2aXNpdGVkVHlwZXMpO1xuICAgIH1cblxuICAgIF90b1N0cmluZyh2aXNpdGVkVHlwZXMpIHtcbiAgICAgICAgY29uc3QgdHlwZVN0cmluZ3MgPSBbXTtcbiAgICAgICAgZm9yIChsZXQgdHAgb2YgdGhpcy50eXBlcykge1xuICAgICAgICAgICAgaWYgKHZpc2l0ZWRUeXBlcy5oYXModHApKSB7XG4gICAgICAgICAgICAgICAgdHlwZVN0cmluZ3MucHVzaCgnPycpO1xuICAgICAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICAgICAgICB0eXBlU3RyaW5ncy5wdXNoKHRwLl90b1N0cmluZyh2aXNpdGVkVHlwZXMpKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgfVxuICAgICAgICByZXR1cm4gdHlwZVN0cmluZ3Muam9pbignfCcpO1xuICAgIH1cbn1cblxuLyoqXG4gKiB0aGUgc3VwZXIgY2xhc3Mgb2YgYWxsIHR5cGVzXG4gKiBlYWNoIHR5cGUgc2hvdWxkIGJlIGRpc3Rpbmd1aXNoYWJsZSBieSAnPT09JyBvcGVyYXRpb24uXG4gKi9cbmNsYXNzIFR5cGUge1xuICAgIC8qKlxuICAgICAqIENyZWF0ZSBhIG5ldyB0eXBlXG4gICAgICogQHBhcmFtIHtzdHJpbmd9IG5hbWVcbiAgICAgKi9cbiAgICBjb25zdHJ1Y3RvcihuYW1lKSB7XG4gICAgICAgIHRoaXMubmFtZSA9IG5hbWU7XG4gICAgfVxuXG4gICAgLyoqXG4gICAgICogUmV0dXJucyB0aGUgbmFtZSBvZiB0eXBlXG4gICAgICogQHJldHVybiB7c3RyaW5nfVxuICAgICAqL1xuICAgIGdldE5hbWUoKSB7XG4gICAgICAgIHJldHVybiB0aGlzLm5hbWU7XG4gICAgfVxuXG4gICAgLyoqXG4gICAgICogRGVmYXVsdCBpbXBsZW1lbnRhdGlvbiBmb3IgdG9TdHJpbmdcbiAgICAgKiBUaGlzIHNob3VsZCBiZSBvdmVycmlkZGVuIGZvciBzb3BoaXN0aWNhdGVkIHR5cGVzXG4gICAgICogQHByaXZhdGVcbiAgICAgKiBAcmV0dXJuIHtzdHJpbmd9XG4gICAgICovXG4gICAgX3RvU3RyaW5nKCkge1xuICAgICAgICByZXR1cm4gdGhpcy5nZXROYW1lKCk7XG4gICAgfVxufVxuXG5cbi8qKlxuICogMS4gb2JqZWN0IHR5cGVzXG4gKi9cbmV4cG9ydCBjbGFzcyBPYmpUeXBlIGV4dGVuZHMgVHlwZSB7XG4gICAgLyoqXG4gICAgICogQHBhcmFtIHtBVmFsfSBwcm90byAtIEFWYWwgb2YgY29uc3RydWN0b3IncyBwcm90b3R5cGVcbiAgICAgKiBAcGFyYW0ge3N0cmluZ30gbmFtZSAtIGd1ZXNzZWQgbmFtZVxuICAgICAqL1xuICAgIGNvbnN0cnVjdG9yKHByb3RvLCBuYW1lKSB7XG4gICAgICAgIHN1cGVyKG5hbWUpO1xuICAgICAgICB0aGlzLnByb3BzID0gbmV3IE1hcCgpO1xuICAgICAgICAvLyBzaGFyZSBwcm90byB3aXRoIF9fcHJvdG9fX1xuICAgICAgICB0aGlzLnNldFByb3AoJ19fcHJvdG9fXycsIHByb3RvKTtcbiAgICAgICAgLy8gcmVtZW1iZXIgd2hvc2UgcHJvdG90eXBlIEkgYW1cbiAgICAgICAgdGhpcy5wcm90b3R5cGVPZiA9IG5ldyBBVmFsKCk7XG4gICAgfVxuXG4gICAgLyoqXG4gICAgICogQHBhcmFtIHtzdHJpbmd8bnVsbH0gcHJvcCAtIG51bGwgZm9yIGNvbXB1dGVkIHByb3BzXG4gICAgICogQHBhcmFtIHtib29sZWFufSByZWFkT25seSAtIGlmIGZhbHNlLCBjcmVhdGUgQVZhbCBmb3IgcHJvcCBpZiBuZWNlc3NhcnlcbiAgICAgKiBAcmV0dXJuIHtBVmFsfSBBVmFsIG9mIHRoZSBwcm9wZXJ0eVxuICAgICAqL1xuICAgIGdldFByb3AocHJvcCwgcmVhZE9ubHkpIHtcbiAgICAgICAgaWYgKHRoaXMucHJvcHMuaGFzKHByb3ApKSB7XG4gICAgICAgICAgICByZXR1cm4gdGhpcy5wcm9wcy5nZXQocHJvcCk7XG4gICAgICAgIH0gZWxzZSBpZiAocmVhZE9ubHkpIHtcbiAgICAgICAgICAgIHJldHVybiBudWxsO1xuICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgICAgdmFyIG5ld1Byb3BBVmFsID0gbmV3IEFWYWw7XG4gICAgICAgICAgICB0aGlzLnByb3BzLnNldChwcm9wLCBuZXdQcm9wQVZhbCk7XG4gICAgICAgICAgICByZXR1cm4gbmV3UHJvcEFWYWw7XG4gICAgICAgIH1cbiAgICB9XG5cbiAgICAvKipcbiAgICAgKiBXZSB1c2UgdGhpcyBmdW5jdGlvbiB0byBzaGFyZSAucHJvdG90eXBlIHdpdGggaW5zdGFuY2VzIF9fcHJvdG9fX1xuICAgICAqIEl0IGlzIHBvc3NpYmxlIHRvIHVzZSB0aGlzIGZ1bmN0aW9uIHRvIG1lcmdlIEFWYWxzIHRvIG9wdGltaXplIHRoZSBhbmFseXplci5cbiAgICAgKiBAcGFyYW0ge3N0cmluZ3xudWxsfSBwcm9wIC0gbnVsbCBmb3IgY29tcHV0ZWQgcHJvcHNcbiAgICAgKiBAcGFyYW0ge0FWYWx9IGF2YWxcbiAgICAgKi9cbiAgICBzZXRQcm9wKHByb3AsIGF2YWwpIHtcbiAgICAgICAgdGhpcy5wcm9wcy5zZXQocHJvcCwgYXZhbCk7XG4gICAgfVxuXG4gICAgLyoqXG4gICAgICogUmV0dXJucyBpdGVyYXRvciBvZiBpdHMgb3duIHByb3BlcnR5IG5hbWVzXG4gICAgICogQHJldHVybiB7SXRlcmF0b3IuPHN0cmluZz59XG4gICAgICovXG4gICAgZ2V0T3duUHJvcE5hbWVzKCkge1xuICAgICAgICByZXR1cm4gdGhpcy5wcm9wcy5rZXlzKCk7XG4gICAgfVxuXG4gICAgLyoqXG4gICAgICogVE9ETzogQ2hlY2sgdGhpcyBmdW5jdGlvbidzIG5lY2Vzc2l0eVxuICAgICAqIEBwYXJhbSB7c3RyaW5nfG51bGx9IHByb3BcbiAgICAgKiBAcmV0dXJuIHtib29sZWFufVxuICAgICAqL1xuICAgIGhhc1Byb3AocHJvcCkge1xuICAgICAgICByZXR1cm4gdGhpcy5wcm9wcy5oYXMocHJvcCk7XG4gICAgfVxuXG4gICAgLyoqXG4gICAgICogVE9ETzogQ2hlY2sgdGhpcyBmdW5jdGlvbidzIG5lY2Vzc2l0eVxuICAgICAqIEBwYXJhbSB7VHlwZX0gdHlwZVxuICAgICAqIEBwYXJhbSB7c3RyaW5nfG51bGx9IHByb3BcbiAgICAgKi9cbiAgICBhZGRUeXBlVG9Qcm9wKHR5cGUsIHByb3ApIHtcbiAgICAgICAgaWYgKCF0aGlzLnByb3BzLmhhcyhwcm9wKSkge1xuICAgICAgICAgICAgdGhpcy5wcm9wcy5zZXQocHJvcCwgbmV3IEFWYWwpO1xuICAgICAgICB9XG4gICAgICAgIGlmICh0aGlzLnByb3BzLmdldChwcm9wKS5oYXNUeXBlKHR5cGUpKSByZXR1cm47XG4gICAgICAgIHRoaXMucHJvcHMuZ2V0KHByb3ApLmFkZFR5cGUodHlwZSk7XG4gICAgfVxuXG4gICAgLyoqXG4gICAgICogVE9ETzogQ2hlY2sgdGhpcyBmdW5jdGlvbidzIG5lY2Vzc2l0eVxuICAgICAqIEBwYXJhbSB7QVZhbH0gYXZhbFxuICAgICAqIEBwYXJhbSB7c3RyaW5nfSBwcm9wXG4gICAgICovXG4gICAgam9pbkFWYWxUb1Byb3AoYXZhbCwgcHJvcCkge1xuICAgICAgICB2YXIgc2VsZiA9IHRoaXM7XG4gICAgICAgIGF2YWwuZ2V0VHlwZXMoKS5mb3JFYWNoKGZ1bmN0aW9uICh0eXBlKSB7XG4gICAgICAgICAgICBzZWxmLmFkZFR5cGVUb1Byb3AodHlwZSwgcHJvcCk7XG4gICAgICAgIH0pO1xuICAgIH1cblxuICAgIC8qKlxuICAgICAqIFNob3cgb2JqZWN0J3Mgb3duIHByb3BlcnR5IG5hbWVzXG4gICAgICogQHBhcmFtIHtTZXQuPFR5cGU+fSB2aXNpdGVkVHlwZXNcbiAgICAgKiBAcmV0dXJuIHtzdHJpbmd9XG4gICAgICovXG4gICAgX3RvU3RyaW5nKHZpc2l0ZWRUeXBlcykge1xuICAgICAgICBpZiAodGhpcy5uYW1lID09PSB1bmRlZmluZWQpIHtcbiAgICAgICAgICAgIGNvbnN0IHByb3BzID0gW107XG4gICAgICAgICAgICBmb3IgKGxldCBwIG9mIHRoaXMucHJvcHMua2V5cygpKSB7XG4gICAgICAgICAgICAgICAgLy8gc2tpcHBpbmcgX19wcm90b19fXG4gICAgICAgICAgICAgICAgaWYgKHAgPT09ICdfX3Byb3RvX18nKSBjb250aW51ZTtcbiAgICAgICAgICAgICAgICBwcm9wcy5wdXNoKHApO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgcmV0dXJuICd7JyArIHByb3BzLmpvaW4oKSArICd9JztcbiAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICAgIHJldHVybiB0aGlzLm5hbWU7XG4gICAgICAgIH1cbiAgICB9XG59XG5cbi8qKlxuICogTWFrZXMgYW4gT2JqIGZyb20gdGhlIGdsb2JhbCBzY29wZVxuICogQHBhcmFtIHtTY29wZX0gZ1Njb3BlIC0gdGhlIGdsb2JhbCBTY29wZSBvYmplY3RcbiAqIEByZXR1cm4ge09ialR5cGV9XG4gKi9cbmV4cG9ydCBmdW5jdGlvbiBta09iakZyb21HbG9iYWxTY29wZShnU2NvcGUpIHtcbiAgICB2YXIgZ09iaiA9IG5ldyBPYmpUeXBlKEFWYWxOdWxsLCAnKmdsb2JhbCBzY29wZSonKTtcbiAgICBnT2JqLnByb3BzID0gZ1Njb3BlLnZhck1hcDtcbiAgICAvLyBPdmVycmlkZSBnZXRQcm9wIG1ldGhvZCBmb3IgZ2xvYmFsIG9iamVjdFxuICAgIC8vIFdlIGlnbm9yZSAncmVhZE9ubHknIHBhcmFtZXRlciB0byBhbHdheXMgcmV0dXJuIGl0cyBvd24gcHJvcCBBVmFsIFxuICAgIGdPYmouZ2V0UHJvcCA9IGZ1bmN0aW9uIChwcm9wKSB7XG4gICAgICAgIGlmICghZ1Njb3BlLnZiLmhhc0xvY2FsVmFyKHByb3ApKSB7XG4gICAgICAgICAgICAvLyB3aGVuIHdlIHJlZmVyIHByb3Agb2YgdGhlIGdsb2JhbCBvYmplY3RcbiAgICAgICAgICAgIGdTY29wZS52Yi5hZGREZWNsYXJlZExvY2FsVmFyKHByb3ApO1xuICAgICAgICB9XG4gICAgICAgIHJldHVybiBPYmpUeXBlLnByb3RvdHlwZS5nZXRQcm9wLmNhbGwodGhpcywgcHJvcCk7XG4gICAgfTtcbiAgICByZXR1cm4gZ09iajtcbn1cblxuLyoqXG4gKiAyLiBwcmltaXRpdmUgdHlwZXNcbiAqL1xuZXhwb3J0IGNsYXNzIFByaW1UeXBlIGV4dGVuZHMgVHlwZSB7XG4gICAgLyoqXG4gICAgICogQHBhcmFtIHtzdHJpbmd9IG5hbWVcbiAgICAgKi9cbiAgICBjb25zdHJ1Y3RvcihuYW1lKSB7XG4gICAgICAgIHN1cGVyKG5hbWUpO1xuICAgIH1cbn1cblxuLyoqXG4gKiAzLiBmdW5jdGlvbiB0eXBlc1xuICogdGhlIG5hbWUgaXMgdXNlZCBmb3IgdGhlIHR5cGUgb2YgdGhlIGluc3RhbmNlcyBmcm9tIHRoZSBmdW5jdGlvblxuICovXG5leHBvcnQgY2xhc3MgRm5UeXBlIGV4dGVuZHMgT2JqVHlwZSB7XG4gICAgLyoqXG4gICAgICogQHBhcmFtIHtBVmFsfSBmbl9wcm90byAtIEFWYWwgZm9yIGNvbnN0cnVjdG9yJ3MgLnByb3RvdHlwZVxuICAgICAqIEBwYXJhbSB7c3RyaW5nfSBuYW1lIC0gZ3Vlc3NlZCBuYW1lXG4gICAgICogQHBhcmFtIHtbc3RyaW5nXX0gYXJnTmFtZXMgLSBsaXN0IG9mIHBhcmFtZXRlciBuYW1lc1xuICAgICAqIEBwYXJhbSB7U2NvcGV9IHNjIC0gZnVuY3Rpb25zIHNjb3BlIGNoYWluLCBvciBjbG9zdXJlXG4gICAgICogQHBhcmFtIHtub2RlfSBvcmlnaW5Ob2RlIC0gQVNUIG5vZGUgZm9yIHRoZSBmdW5jdGlvblxuICAgICAqIEBwYXJhbSB7VHlwZX0gYXJnUHJvdG8gLSBwcm90b3R5cGUgZm9yIGFyZ3VtZW50cyBvYmplY3RcbiAgICAgKiBAcGFyYW0ge0FWYWx9IGJvdW5kVGhpcyAtIHJlbWVtYmVyIHRoaXNBVmFsIGZvciBhcnJvdyBmdW5jdGlvblxuICAgICAqL1xuICAgIGNvbnN0cnVjdG9yKGZuX3Byb3RvLCBuYW1lLCBhcmdOYW1lcywgc2MsIG9yaWdpbk5vZGUsIGFyZ1Byb3RvLCBib3VuZFRoaXMpIHtcbiAgICAgICAgc3VwZXIoZm5fcHJvdG8sIG5hbWUpO1xuICAgICAgICB0aGlzLnBhcmFtTmFtZXMgPSBhcmdOYW1lcztcbiAgICAgICAgdGhpcy5zYyA9IHNjO1xuICAgICAgICB0aGlzLm9yaWdpbk5vZGUgPSBvcmlnaW5Ob2RlO1xuICAgICAgICBpZiAoYXJnUHJvdG8pIHtcbiAgICAgICAgICAgIHRoaXMuYXJnUHJvdG8gPSBhcmdQcm90bztcbiAgICAgICAgfVxuICAgICAgICBpZiAoYm91bmRUaGlzKSB7XG4gICAgICAgICAgICB0aGlzLmJvdW5kVGhpcyA9IGJvdW5kVGhpcztcbiAgICAgICAgfVxuICAgICAgICAvLyBmdW5FbnYgOiBDYWxsQ29udGV4dCAtPiBbc2VsZiwgcmV0LCBleGNdXG4gICAgICAgIHRoaXMuZnVuRW52ID0gbmV3IE1hcDtcbiAgICB9XG5cbiAgICAvKipcbiAgICAgKiBjb25zdHJ1Y3QgU3RhdHVzIGZvciBmdW5jdGlvblxuICAgICAqIEBwYXJhbSB7Q2FsbENvbnRleHR9IGRlbHRhIC0gY2FsbCBjb250ZXh0XG4gICAgICogQHJldHVybiB7W0FWYWwsIEFWYWwsIEFWYWxdfSAtIGZvciBzZWxmLCByZXR1cm4gYW5kIGV4Y2VwdGlvbiBBVmFsc1xuICAgICAqL1xuICAgIGdldEZ1bkVudihkZWx0YSkge1xuICAgICAgICBpZiAodGhpcy5mdW5FbnYuaGFzKGRlbHRhKSkge1xuICAgICAgICAgICAgcmV0dXJuIHRoaXMuZnVuRW52LmdldChkZWx0YSk7XG4gICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgICB2YXIgdHJpcGxlID0gW25ldyBBVmFsLCBuZXcgQVZhbCwgbmV3IEFWYWxdO1xuICAgICAgICAgICAgdGhpcy5mdW5FbnYuc2V0KGRlbHRhLCB0cmlwbGUpO1xuICAgICAgICAgICAgcmV0dXJuIHRyaXBsZTtcbiAgICAgICAgfVxuICAgIH1cblxuICAgIC8qKlxuICAgICAqIFJldHVybnMgdGhlIGFyZ3VtZW50IG9iamVjdCBmb3IgY29udGV4dCBkZWx0YVxuICAgICAqIEBwYXJhbSB7Q2FsbFNpdGVDb250ZXh0fSBkZWx0YVxuICAgICAqIEByZXR1cm4ge09ialR5cGV9XG4gICAgICovXG4gICAgZ2V0QXJndW1lbnRzT2JqZWN0KGRlbHRhKSB7XG4gICAgICAgIHRoaXMuYXJnT2JqTWFwID0gdGhpcy5hcmdPYmpNYXAgfHwgbmV3IE1hcDtcbiAgICAgICAgaWYgKHRoaXMuYXJnT2JqTWFwLmhhcyhkZWx0YSkpIHtcbiAgICAgICAgICAgIHJldHVybiB0aGlzLmFyZ09iak1hcC5nZXQoZGVsdGEpO1xuICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgICAgdmFyIGFyZ09iaiA9IG5ldyBPYmpUeXBlKG5ldyBBVmFsKHRoaXMuYXJnUHJvdG8pLCAnKmFyZ3VtZW50cyBvYmplY3QqJyk7XG4gICAgICAgICAgICB0aGlzLmFyZ09iak1hcC5zZXQoZGVsdGEsIGFyZ09iaik7XG4gICAgICAgICAgICByZXR1cm4gYXJnT2JqO1xuICAgICAgICB9XG4gICAgfVxuXG4gICAgLyoqXG4gICAgICogZ2V0IE9iamVjdCBtYWRlIGJ5IHRoZSBmdW5jdGlvblxuICAgICAqIFRPRE86IHVzZSBhZGRpdGlvbmFsIGluZm9ybWF0aW9uIHRvIGNyZWF0ZSBtdWx0aXBsZSBpbnN0YW5jZXNcbiAgICAgKiBAcmV0dXJuIHtPYmpUeXBlfVxuICAgICAqL1xuICAgIGdldEluc3RhbmNlKCkge1xuICAgICAgICAvLyBvYmpJbnN0YW5jZSBpcyB0aGUgb2JqZWN0IG1hZGUgYnkgdGhlIGZ1bmN0aW9uXG4gICAgICAgIGlmICh0aGlzLm9iakluc3RhbmNlKSByZXR1cm4gdGhpcy5vYmpJbnN0YW5jZTtcbiAgICAgICAgLy8gd2UgdW5pZnkgY29uc3RydWN0b3IncyAucHJvdG90eXBlIGFuZCBpbnN0YW5jZSdzIF9fcHJvdG9fX1xuICAgICAgICB0aGlzLm9iakluc3RhbmNlID0gbmV3IE9ialR5cGUodGhpcy5nZXRQcm9wKCdwcm90b3R5cGUnKSk7XG4gICAgICAgIHJldHVybiB0aGlzLm9iakluc3RhbmNlO1xuICAgIH1cblxuICAgIF9zdHJpbmdpZnlPbmVMZXZlbFN0cnVjdHVyZShzdHJ1Y3R1cmUpIHtcblxuICAgICAgICBjb25zdCBwYXJhbXMgPSBzdHJ1Y3R1cmUucGFyYW1zLm1hcChmdW5jdGlvbiAocGFyYW0pIHtcbiAgICAgICAgICAgIGlmIChwYXJhbS50eXBlICE9PSB1bmRlZmluZWQpXG4gICAgICAgICAgICAgICAgcmV0dXJuIHBhcmFtLm5hbWUgKyAnOicgKyBwYXJhbS50eXBlO1xuICAgICAgICAgICAgZWxzZSByZXR1cm4gcGFyYW0ubmFtZTtcbiAgICAgICAgfSk7XG5cbiAgICAgICAgbGV0IHJlc1N0ciA9ICdmbignICsgcGFyYW1zLmpvaW4oJywgJykgKyAnKSc7XG4gICAgICAgIGlmIChzdHJ1Y3R1cmUucmV0ICE9PSB1bmRlZmluZWQpIHtcbiAgICAgICAgICAgIHJlc1N0ciArPSAnIC0+ICcgKyBzdHJ1Y3R1cmUucmV0O1xuICAgICAgICB9XG4gICAgICAgIHJldHVybiByZXNTdHI7XG4gICAgfVxuXG4gICAgX3RvU3RyaW5nKHZpc2l0ZWRUeXBlcykge1xuICAgICAgICBpZiAodmlzaXRlZFR5cGVzLmhhcyh0aGlzKSkge1xuICAgICAgICAgICAgcmV0dXJuICc/JztcbiAgICAgICAgfVxuICAgICAgICBjb25zdCBzdHJ1Y3R1cmUgPSB0aGlzLl9nZXRPbmVMZXZlbFN0cnVjdHVyZSh2aXNpdGVkVHlwZXMpO1xuICAgICAgICByZXR1cm4gdGhpcy5fc3RyaW5naWZ5T25lTGV2ZWxTdHJ1Y3R1cmUoc3RydWN0dXJlKTtcbiAgICB9XG5cbiAgICBfZ2V0T25lTGV2ZWxTdHJ1Y3R1cmUodmlzaXRlZFR5cGVzKSB7XG4gICAgICAgIHZpc2l0ZWRUeXBlcy5hZGQodGhpcyk7XG4gICAgICAgIGNvbnN0IGZCbG9jayA9IHRoaXMub3JpZ2luTm9kZS5ib2R5WydAYmxvY2snXTtcbiAgICAgICAgY29uc3QgcEJsb2NrID0gZkJsb2NrLmhhc1BhcmFtU2NvcGUgPyBmQmxvY2sucGFyZW4gOiBmQmxvY2s7XG4gICAgICAgIGNvbnN0IHBhcmFtU2NvcGVzID0gcEJsb2NrLmdldFNjb3Blc1dpdGhQYXJlbnQodGhpcy5zYyk7XG4gICAgICAgIGNvbnN0IHBhcmFtcyA9IHRoaXMub3JpZ2luTm9kZS5wYXJhbXM7XG5cblxuICAgICAgICBmdW5jdGlvbiBfY29uY2F0TmFtZUFuZFR5cGUobmFtZSwgdHlwZVN0cmluZykge1xuICAgICAgICAgICAgcmV0dXJuIG5hbWUgKyAodHlwZVN0cmluZyA/ICc6JyArIHR5cGVTdHJpbmcgOiAnJyk7XG4gICAgICAgIH1cblxuICAgICAgICBmdW5jdGlvbiBfcGF0dGVybk5hbWUocGF0dGVybikge1xuICAgICAgICAgICAgc3dpdGNoIChwYXR0ZXJuLnR5cGUpIHtcbiAgICAgICAgICAgICAgICBjYXNlICdJZGVudGlmaWVyJyA6XG4gICAgICAgICAgICAgICAgICAgIHJldHVybiBwYXR0ZXJuLm5hbWU7XG4gICAgICAgICAgICAgICAgY2FzZSAnQXNzaWdubWVudFBhdHRlcm4nIDpcbiAgICAgICAgICAgICAgICAgICAgcmV0dXJuIHBhdHRlcm4ubGVmdC5uYW1lO1xuICAgICAgICAgICAgICAgIGNhc2UgJ09iamVjdFBhdHRlcm4nIDpcbiAgICAgICAgICAgICAgICAgICAgcmV0dXJuICd7JyArIHBhdHRlcm4ucHJvcGVydGllcy5tYXAoKGUpID0+IF9wYXR0ZXJuTmFtZShlLnZhbHVlKSkgKyAnfSc7XG4gICAgICAgICAgICAgICAgY2FzZSAnQXJyYXlQYXR0ZXJuJyA6XG4gICAgICAgICAgICAgICAgICAgIHJldHVybiAnWycgKyBwYXR0ZXJuLmVsZW1lbnRzLm1hcChfcGF0dGVybk5hbWUpICsgJ10nO1xuICAgICAgICAgICAgICAgIGNhc2UgJ1Jlc3RFbGVtZW50JyA6XG4gICAgICAgICAgICAgICAgICAgIHJldHVybiAnLi4uJyArIF9wYXR0ZXJuTmFtZShwYXR0ZXJuLmFyZ3VtZW50KTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgfVxuXG4gICAgICAgIGZ1bmN0aW9uIF9wYXR0ZXJuV2l0aFR5cGUocGF0dGVybiwgcmVtb3ZlSWQpIHtcbiAgICAgICAgICAgIHN3aXRjaCAocGF0dGVybi50eXBlKSB7XG4gICAgICAgICAgICAgICAgY2FzZSAnSWRlbnRpZmllcicgOlxuICAgICAgICAgICAgICAgICAgICBpZiAocmVtb3ZlSWQpIHJldHVybiBfZ2V0VHlwZVN0cmluZ0ZvclZhcihwYXR0ZXJuLm5hbWUpO1xuICAgICAgICAgICAgICAgICAgICBlbHNlIHJldHVybiBfY29uY2F0TmFtZUFuZFR5cGUocGF0dGVybi5uYW1lLCBfZ2V0VHlwZVN0cmluZ0ZvclZhcihwYXR0ZXJuLm5hbWUpKTtcbiAgICAgICAgICAgICAgICBjYXNlICdBc3NpZ25tZW50UGF0dGVybicgOlxuICAgICAgICAgICAgICAgICAgICByZXR1cm4gX3BhdHRlcm5XaXRoVHlwZShwYXR0ZXJuLmxlZnQpO1xuICAgICAgICAgICAgICAgIGNhc2UgJ09iamVjdFBhdHRlcm4nIDpcbiAgICAgICAgICAgICAgICAgICAgcmV0dXJuICd7JyArIHBhdHRlcm4ucHJvcGVydGllcy5tYXAoKGUpID0+IF9wYXR0ZXJuV2l0aFR5cGUoZS52YWx1ZSkpICsgJ30nO1xuICAgICAgICAgICAgICAgIGNhc2UgJ0FycmF5UGF0dGVybicgOlxuICAgICAgICAgICAgICAgICAgICByZXR1cm4gJ1snICsgcGF0dGVybi5lbGVtZW50cy5tYXAoKGUpID0+IF9wYXR0ZXJuV2l0aFR5cGUoZSkpICsgJ10nO1xuICAgICAgICAgICAgICAgIGNhc2UgJ1Jlc3RFbGVtZW50JyA6XG4gICAgICAgICAgICAgICAgICAgIGlmIChyZW1vdmVJZCkge1xuICAgICAgICAgICAgICAgICAgICAgICAgcmV0dXJuIF9wYXR0ZXJuV2l0aFR5cGUocGF0dGVybi5hcmd1bWVudCwgcmVtb3ZlSWQpO1xuICAgICAgICAgICAgICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgICAgICAgICAgICAgICAgcmV0dXJuICcuLi4nICsgX3BhdHRlcm5XaXRoVHlwZShwYXR0ZXJuLmFyZ3VtZW50KTtcbiAgICAgICAgICAgICAgICAgICAgfVxuXG4gICAgICAgICAgICB9XG4gICAgICAgIH1cblxuICAgICAgICBmdW5jdGlvbiBfZ2V0VHlwZVN0cmluZ0ZvclZhcih2YXJOYW1lKSB7XG4gICAgICAgICAgICBjb25zdCBzdHJpbmdzID0gW107XG4gICAgICAgICAgICBsZXQgaGFzVHlwZSA9IGZhbHNlO1xuICAgICAgICAgICAgZm9yIChsZXQgc2Mgb2YgcGFyYW1TY29wZXMpIHtcbiAgICAgICAgICAgICAgICBjb25zdCBhdmFsID0gc2MuZ2V0QVZhbE9mKHZhck5hbWUpO1xuICAgICAgICAgICAgICAgIGlmICghYXZhbC5pc0VtcHR5KCkpIHtcbiAgICAgICAgICAgICAgICAgICAgc3RyaW5ncy5wdXNoKGF2YWwuX3RvU3RyaW5nKHZpc2l0ZWRUeXBlcykpO1xuICAgICAgICAgICAgICAgICAgICBoYXNUeXBlID0gdHJ1ZTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICByZXR1cm4gaGFzVHlwZSA/IHN0cmluZ3Muam9pbignfCcpIDogdW5kZWZpbmVkO1xuICAgICAgICB9XG5cbiAgICAgICAgY29uc3QgcGFyYW1JbmZvID0gcGFyYW1zLm1hcCgocCkgPT4gKHtcbiAgICAgICAgICAgIG5hbWU6IF9wYXR0ZXJuTmFtZShwKSxcbiAgICAgICAgICAgIHR5cGU6IF9wYXR0ZXJuV2l0aFR5cGUocCwgdHJ1ZSl9KSk7XG5cbiAgICAgICAgLy8gY29tcHV0aW5nIGpvaW5lZCByZXRBVmFsXG4gICAgICAgIGNvbnN0IHJldFR5cGVTdHJpbmdzID0gW107XG4gICAgICAgIGxldCBub1JldFR5cGVzID0gdHJ1ZTtcbiAgICAgICAgZm9yIChsZXQgWywgcmV0QVZhbCwgXSBvZiB0aGlzLmZ1bkVudi52YWx1ZXMoKSkge1xuICAgICAgICAgICAgaWYgKCFyZXRBVmFsLmlzRW1wdHkoKSkge1xuICAgICAgICAgICAgICAgIG5vUmV0VHlwZXMgPSBmYWxzZTtcbiAgICAgICAgICAgICAgICByZXRUeXBlU3RyaW5ncy5wdXNoKHJldEFWYWwuX3RvU3RyaW5nKHZpc2l0ZWRUeXBlcykpO1xuICAgICAgICAgICAgfVxuICAgICAgICB9XG4gICAgICAgIHZpc2l0ZWRUeXBlcy5kZWxldGUodGhpcyk7XG4gICAgICAgIHJldHVybiB7cGFyYW1zOiBwYXJhbUluZm8sIHJldDogKG5vUmV0VHlwZXMgPyB1bmRlZmluZWQgOiByZXRUeXBlU3RyaW5ncy5qb2luKCd8JykpfTtcblxuICAgIH1cblxuICAgIC8qKlxuICAgICAqIFJldHVybnMgdGhlIHBhcmFtZXRlciB0eXBlIHN0cmluZ3MgYW5kIHJldHVybiB0eXBlIHN0cmluZ3MgaW4gYW4gb2JqZWN0XG4gICAgICogQHJldHVybiB7e3BhcmFtcywgcmV0fXwqfVxuICAgICAqL1xuICAgIGdldE9uZUxldmVsU3RydWN0dXJlKCkge1xuICAgICAgICBjb25zdCB2aXNpdGVkVHlwZXMgPSBuZXcgU2V0KCk7XG4gICAgICAgIHJldHVybiB0aGlzLl9nZXRPbmVMZXZlbFN0cnVjdHVyZSh2aXNpdGVkVHlwZXMpO1xuICAgIH1cbn1cblxuLyoqIFxuICogNC4gYXJyYXkgdHlwZXNcbiAqL1xuZXhwb3J0IGNsYXNzIEFyclR5cGUgZXh0ZW5kcyBPYmpUeXBlIHtcbiAgICAvKipcbiAgICAgKiBDb25zdHJ1Y3QgQXJyVHlwZVxuICAgICAqIEBwYXJhbSB7QVZhbH0gYXJyX3Byb3RvXG4gICAgICovXG4gICAgY29uc3RydWN0b3IoYXJyX3Byb3RvKSB7XG4gICAgICAgIHN1cGVyKGFycl9wcm90bywgJ0FycmF5Jyk7XG4gICAgfVxuXG4gICAgX3RvU3RyaW5nKHZpc2l0ZWRUeXBlcykge1xuICAgICAgICBpZiAodmlzaXRlZFR5cGVzLmhhcyh0aGlzKSkge1xuICAgICAgICAgICAgcmV0dXJuICc/JztcbiAgICAgICAgfVxuICAgICAgICB2aXNpdGVkVHlwZXMuYWRkKHRoaXMpO1xuICAgICAgICAvLyBwcm9wIG51bGwgaXMgdXNlZCBmb3IgYXJyYXkgZWxlbWVudHNcbiAgICAgICAgY29uc3QgZWx0VHlwZXMgPSB0aGlzLmdldFByb3AobnVsbCwgdHJ1ZSk7XG4gICAgICAgIGNvbnN0IHRwU3RyID0gJ1snICsgZWx0VHlwZXMuX3RvU3RyaW5nKHZpc2l0ZWRUeXBlcykgKyAnXSc7XG4gICAgICAgIHZpc2l0ZWRUeXBlcy5kZWxldGUodGhpcyk7XG4gICAgICAgIHJldHVybiB0cFN0cjtcbiAgICB9XG59XG5cbi8vIE1ha2UgcHJpbWl0aXZlIHR5cGVzXG5leHBvcnQgY29uc3QgUHJpbU51bWJlciA9IG5ldyBQcmltVHlwZSgnbnVtYmVyJyk7XG5leHBvcnQgY29uc3QgUHJpbVN0cmluZyA9IG5ldyBQcmltVHlwZSgnc3RyaW5nJyk7XG5leHBvcnQgY29uc3QgUHJpbUJvb2xlYW4gPSBuZXcgUHJpbVR5cGUoJ2Jvb2xlYW4nKTtcblxuLy8gQWJzTnVsbCByZXByZXNlbnRzIGFsbCBlbXB0eSBhYnN0cmFjdCB2YWx1ZXMuXG5leHBvcnQgY29uc3QgQVZhbE51bGwgPSBuZXcgQVZhbCgpO1xuLy8gWW91IHNob3VsZCBub3QgYWRkIGFueSBwcm9wZXJ0aWVzIHRvIGl0LlxuQVZhbE51bGwucHJvcHMgPSBudWxsO1xuLy8gQWRkaW5nIHR5cGVzIGFyZSBpZ25vcmVkLlxuQVZhbE51bGwuYWRkVHlwZSA9IGZ1bmN0aW9uICgpIHt9O1xuXG5leHBvcnQgY2xhc3MgQWJzQ2FjaGUge1xuICAgIGNvbnN0cnVjdG9yKCkge1xuICAgICAgICB0aGlzLm1hcCA9IG5ldyBNYXAoKTtcbiAgICB9XG5cbiAgICAvKipcbiAgICAgKiBHZXQgaWYgb25lIGV4aXN0cywgaWYgbm90IGNyZWF0ZSBvbmVcbiAgICAgKiBAcGFyYW0gbG9jXG4gICAgICogQHBhcmFtIGN0eFxuICAgICAqIEByZXR1cm4ge0FWYWx9XG4gICAgICovXG4gICAgZ2V0KGxvYywgY3R4KSB7XG4gICAgICAgIGlmICghdGhpcy5tYXAuaGFzKGxvYykpIHtcbiAgICAgICAgICAgIC8vIGNyZWF0ZSBpbm5lciBtYXBcbiAgICAgICAgICAgIHRoaXMubWFwLnNldChsb2MsIG5ldyBNYXAoKSk7XG4gICAgICAgIH1cbiAgICAgICAgY29uc3QgbWFwTG9jID0gdGhpcy5tYXAuZ2V0KGxvYyk7XG4gICAgICAgIGlmICghbWFwTG9jLmhhcyhjdHgpKSB7XG4gICAgICAgICAgICBjb25zdCBhdiA9IG5ldyBBVmFsKCk7XG4gICAgICAgICAgICBtYXBMb2Muc2V0KGN0eCwgYXYpO1xuICAgICAgICAgICAgcmV0dXJuIGF2O1xuICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgICAgcmV0dXJuIG1hcExvYy5nZXQoY3R4KTtcbiAgICAgICAgfVxuICAgIH1cblxuICAgIC8qKlxuICAgICAqIFVzZSBBVmFsIG1hZGUgYnkgb3RoZXJzIChlLmcuIHNjb3BlKVxuICAgICAqIEBwYXJhbSBsb2NcbiAgICAgKiBAcGFyYW0gY3R4XG4gICAgICogQHBhcmFtIGF2XG4gICAgICovXG4gICAgc2V0KGxvYywgY3R4LCBhdikge1xuICAgICAgICBpZiAoIXRoaXMubWFwLmhhcyhsb2MpKSB7XG4gICAgICAgICAgICAvLyBjcmVhdGUgaW5uZXIgbWFwXG4gICAgICAgICAgICB0aGlzLm1hcC5zZXQobG9jLCBuZXcgTWFwKCkpO1xuICAgICAgICB9XG4gICAgICAgIHRoaXMubWFwLmdldChsb2MpLnNldChjdHgsIGF2KTtcbiAgICB9XG5cbiAgICAvKipcbiAgICAgKiBDaGVjayB3aGV0aGVyIGl0IGhhcyBvbmUgZm9yIGxvYyBhbmQgY3R4XG4gICAgICogQHBhcmFtIGxvY1xuICAgICAqIEBwYXJhbSBjdHhcbiAgICAgKiBAcmV0dXJuIHtib29sZWFufVxuICAgICAqL1xuICAgIGhhcyhsb2MsIGN0eCkge1xuICAgICAgICByZXR1cm4gdGhpcy5tYXAuaGFzKGxvYykgJiYgdGhpcy5tYXAuZ2V0KGxvYykuaGFzKGN0eCk7XG4gICAgfVxuXG4gICAgLyoqXG4gICAgICogTWVyZ2UgYWxsIEFWYWwgb2YgdGhlIGxvY1xuICAgICAqIEBwYXJhbSBsb2NcbiAgICAgKiBAcmV0dXJuIHtBVmFsfVxuICAgICAqL1xuICAgIGdldE1lcmdlZEFWYWxPZkxvYyhsb2MpIHtcbiAgICAgICAgaWYgKCF0aGlzLm1hcC5oYXMobG9jKSkge1xuICAgICAgICAgICAgLy8gbm8gdHlwZSBpcyBhdmFpbGFibGVcbiAgICAgICAgICAgIHJldHVybiBudWxsO1xuICAgICAgICB9XG4gICAgICAgIGNvbnN0IG1lcmdlZEFWYWwgPSBuZXcgQVZhbCgpO1xuICAgICAgICBpZiAodGhpcy5tYXAuaGFzKGxvYykpIHtcbiAgICAgICAgICAgIGZvciAobGV0IGF2IG9mIHRoaXMubWFwLmdldChsb2MpLnZhbHVlcygpKSB7XG4gICAgICAgICAgICAgICAgZm9yIChsZXQgdHAgb2YgYXYuZ2V0VHlwZXMoKSkge1xuICAgICAgICAgICAgICAgICAgICBtZXJnZWRBVmFsLmFkZFR5cGUodHApO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgIH1cbiAgICAgICAgfSAgICAgICAgcmV0dXJuIG1lcmdlZEFWYWw7XG4gICAgfVxufVxuIiwiLyoqXG4gKiBAZmlsZSBEZWZpbmVzIGZ1bmN0aW9ucyB0aGF0IGV4dHJhY3QgdHlwZSBpbmZvcm1hdGlvblxuICogQGF1dGhvciBzZXdvbjMyNi5raW1Ac2Ftc3VuZy5jb21cbiAqL1xuXG5pbXBvcnQgKiBhcyBteVdhbGtlciBmcm9tICcuL3V0aWwvbXlXYWxrZXInXG5pbXBvcnQgKiBhcyB0eXBlcyBmcm9tICcuL2RvbWFpbnMvdHlwZXMnXG5cbi8qKlxuICogR2V0IHR5cGVzIG9mIGV4cHJlc3Npb24gYXQgdGhlIGdpdmVuIHJhbmdlXG4gKiBAcGFyYW0gYXN0XG4gKiBAcGFyYW0gxIhcbiAqIEBwYXJhbSBzdGFydFxuICogQHBhcmFtIGVuZFxuICogQHJldHVybiB7e2hhc1R5cGU6IGJvb2xlYW4sIHR5cGVTdHJpbmc6IHN0cmluZywgbm9kZVN0YXJ0OiBudW1iZXIsIG5vZGVFbmQ6IG51bWJlcn19XG4gKi9cbmV4cG9ydCBmdW5jdGlvbiBnZXRUeXBlQXRSYW5nZShhc3QsIMSILCBzdGFydCwgZW5kKSB7XG4gICAgJ3VzZSBzdHJpY3QnO1xuICAgIGNvbnN0IG5vZGUgPSBteVdhbGtlci5maW5kU3Vycm91bmRpbmdOb2RlKGFzdCwgc3RhcnQsIGVuZCk7XG4gICAgY29uc3Qgbm9kZVR5cGVzID0gxIguZ2V0TWVyZ2VkQVZhbE9mTG9jKG5vZGUpO1xuICAgIGxldCBoYXNUeXBlO1xuICAgIGxldCB0eXBlU3RyaW5nID0gJyc7XG4gICAgaWYgKCFub2RlVHlwZXMpIHtcbiAgICAgICAgaGFzVHlwZSA9IGZhbHNlO1xuICAgICAgICB0eXBlU3RyaW5nID0gJ05vIHR5cGVzIGF0IHRoZSBnaXZlbiByYW5nZSc7XG4gICAgfSBlbHNlIHtcbiAgICAgICAgaGFzVHlwZSA9IHRydWU7XG4gICAgICAgIHR5cGVTdHJpbmcgPSBub2RlVHlwZXMudG9TdHJpbmcoKTtcbiAgICB9XG4gICAgcmV0dXJuIHtcbiAgICAgICAgaGFzVHlwZTogaGFzVHlwZSxcbiAgICAgICAgdHlwZVN0cmluZzogdHlwZVN0cmluZyxcbiAgICAgICAgbm9kZVN0YXJ0OiBub2RlLnN0YXJ0LFxuICAgICAgICBub2RlRW5kOiBub2RlLmVuZFxuICAgIH07XG59XG5cbi8qKlxuICogR2V0IHRoZSBzaW1wbGUgdHlwZSBzdHJ1Y3R1cmUgZm9yIHRoZSBmdW5jdGlvbiBhdCBgcG9zYC5cbiAqIEBwYXJhbSBhc3RcbiAqIEBwYXJhbSDEiFxuICogQHBhcmFtIHBvc1xuICogQHJldHVybnMge0FycmF5fVxuICovXG5leHBvcnQgZnVuY3Rpb24gZ2V0Rm5UeXBlU3RydWN0dXJlc0F0KGFzdCwgxIgsIHBvcykge1xuICAgIGNvbnN0IG5vZGUgPSBteVdhbGtlci5maW5kU3Vycm91bmRpbmdOb2RlKGFzdCwgcG9zLCBwb3MpO1xuICAgIGNvbnN0IG5vZGVUeXBlcyA9IMSILmdldE1lcmdlZEFWYWxPZkxvYyhub2RlKTtcbiAgICBjb25zdCBmblR5cGVTdHJ1Y3R1cmVzID0gW107XG5cbiAgICBub2RlVHlwZXMuZ2V0VHlwZXMoKS5mb3JFYWNoKGZ1bmN0aW9uIChmbikge1xuICAgICAgICBpZiAoZm4gaW5zdGFuY2VvZiB0eXBlcy5GblR5cGUpIHtcbiAgICAgICAgICAgIGZuVHlwZVN0cnVjdHVyZXMucHVzaChmbi5nZXRPbmVMZXZlbFN0cnVjdHVyZSgpKTtcbiAgICAgICAgfVxuICAgIH0pO1xuICAgIHJldHVybiBmblR5cGVTdHJ1Y3R1cmVzO1xufVxuXG5mdW5jdGlvbiBfY29tcHV0ZUljb25PZlByb3AocHJvcE1hcCkge1xuICAgIGNvbnN0IGljb25NYXAgPSBuZXcgTWFwKCk7XG5cbiAgICBmdW5jdGlvbiBpc09iamVjdChpY29uKSB7XG4gICAgICAgIHJldHVybiBpY29uID09PSAnb2JqZWN0JyB8fCBpY29uID09PSAnYXJyYXknIHx8IGljb24gPT09ICdmbic7XG4gICAgfVxuXG4gICAgcHJvcE1hcC5mb3JFYWNoKCh0cHMsIHApID0+IHtcbiAgICAgICAgZm9yIChsZXQgdHAgb2YgdHBzKSB7XG4gICAgICAgICAgICBsZXQgaWNvbjtcbiAgICAgICAgICAgIGlmICh0cCA9PT0gdHlwZXMuUHJpbU51bWJlcikgaWNvbiA9ICdudW1iZXInO1xuICAgICAgICAgICAgZWxzZSBpZiAodHAgPT09IHR5cGVzLlByaW1Cb29sZWFuKSBpY29uID0gJ2Jvb2wnO1xuICAgICAgICAgICAgZWxzZSBpZiAodHAgPT09IHR5cGVzLlByaW1TdHJpbmcpIGljb24gPSAnc3RyaW5nJztcbiAgICAgICAgICAgIGVsc2UgaWYgKHRwIGluc3RhbmNlb2YgdHlwZXMuRm5UeXBlKSBpY29uID0gJ2ZuJztcbiAgICAgICAgICAgIGVsc2UgaWYgKHRwIGluc3RhbmNlb2YgdHlwZXMuQXJyVHlwZSkgaWNvbiA9ICdhcnJheSc7XG4gICAgICAgICAgICBlbHNlIGlmICh0cCBpbnN0YW5jZW9mIHR5cGVzLk9ialR5cGUpIGljb24gPSAnb2JqZWN0JztcblxuICAgICAgICAgICAgaWYgKCFpY29uTWFwLmhhcyhwKSB8fCBpY29uTWFwLmdldChwKSA9PT0gaWNvbikge1xuICAgICAgICAgICAgICAgIGljb25NYXAuc2V0KHAsIGljb24pO1xuICAgICAgICAgICAgICAgIGNvbnRpbnVlO1xuICAgICAgICAgICAgfVxuXG4gICAgICAgICAgICBpZiAoaXNPYmplY3QoaWNvbikgJiYgaXNPYmplY3QoaWNvbk1hcC5nZXQocCkpKSB7XG4gICAgICAgICAgICAgICAgaWNvbk1hcC5zZXQocCwgJ29iamVjdCcpO1xuICAgICAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICAgICAgICBpY29uTWFwLnNldChwLCAndW5rbm93bicpO1xuICAgICAgICAgICAgICAgIGJyZWFrO1xuICAgICAgICAgICAgfVxuICAgICAgICB9XG4gICAgICAgIGlmICh0cHMuc2l6ZSA9PT0gMCkge1xuICAgICAgICAgICAgaWNvbk1hcC5zZXQocCwgJ3Vua25vd24nKTtcbiAgICAgICAgfVxuICAgIH0pO1xuICAgIHJldHVybiBpY29uTWFwO1xufVxuXG4vKipcbiAqIEdldCBwcm9wIHRvIGljb24gbWFwIGZyb20gZ2l2ZW4gbm9kZVxuICogQHBhcmFtIMSIIC0gQWJzQ2FjaGVcbiAqIEBwYXJhbSBub2RlIC0gZXhwcmVzc2lvbiBub2RlXG4gKiBAcmV0dXJuIHtNYXAuPHN0cmluZywgc3RyaW5nPn0gLSBNYXBwaW5nIGZyb20gcHJvcCB0byBpY29uXG4gKi9cbmV4cG9ydCBmdW5jdGlvbiBnZXRQcm9wRnJvbU5vZGUoxIgsIG5vZGUpIHtcbiAgICAvLyBTaW5jZSBnZXRUeXBlT2ZMb2MgY2FuIHJldHVybiBudWxsIGlmIG5vZGUgZG9lcyBub3QgaGF2ZSBhbnkgdHlwZXNcbiAgICBjb25zdCBub2RlVHlwZXMgPSDEiC5nZXRNZXJnZWRBVmFsT2ZMb2Mobm9kZSk7XG4gICAgY29uc3QgcHJvcE1hcCA9IF9nZXRSZWFkYWJsZVByb3BNYXAobm9kZVR5cGVzKTtcbiAgICByZXR1cm4gX2NvbXB1dGVJY29uT2ZQcm9wKHByb3BNYXApO1xufVxuXG4vKipcbiAqIEZvciBkZWJ1Z2dpbmcsIHNob3cgeFxuICogQHBhcmFtIHhcbiAqL1xuZnVuY3Rpb24gX1NIT1coeCkge1xuICAgIGNvbnNvbGUuaW5mbyh4KTtcbiAgICByZXR1cm4geDtcbn1cblxuLyoqXG4gKiBSZXR1cm5zIHRoZSBjb21wbGV0aW9uIGxpc3QgYXQgYHBvc2BcbiAqIEBwYXJhbSByZXN1bHRcbiAqIEBwYXJhbSB7QXJyYXl9IHBvc1xuICovXG5leHBvcnQgZnVuY3Rpb24gZ2V0Q29tcGxldGlvbkF0UG9zKHJlc3VsdCwgcG9zKSB7XG4gICAgLy8gZmluZCBpZCBvciBtZW1iZXIgbm9kZVxuICAgIGNvbnN0IG5vZGVJbmZvID0gbXlXYWxrZXIuZmluZENvbXBsZXRpb25Db250ZXh0KHJlc3VsdC5BU1QsIHBvcyk7XG5cbiAgICBpZiAobm9kZUluZm8udHlwZSA9PT0gJ0lkZW50aWZpZXInKSB7XG4gICAgICAgIGxldCBwcmVmaXgsIGZyb20sIHRvO1xuXG4gICAgICAgIGlmIChub2RlSW5mby5ub2RlID09PSBudWxsKSB7XG4gICAgICAgICAgICBwcmVmaXggPSAnJztcbiAgICAgICAgICAgIGZyb20gPSBwb3M7XG4gICAgICAgICAgICB0byA9IHBvcztcbiAgICAgICAgfSBlbHNlIGlmIChteVdhbGtlci5pc0R1bW15SWROb2RlKG5vZGVJbmZvLm5vZGUpKSB7XG4gICAgICAgICAgICBwcmVmaXggPSAnJztcbiAgICAgICAgICAgIGZyb20gPSB0byA9IG5vZGVJbmZvLm5vZGUuZW5kOyAvLyBIZXJlLCBlbmQgaXMgY29ycmVjdCBmb3Igc3RhcnQgcG9zaXRpb25cbiAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICAgIHByZWZpeCA9IG5vZGVJbmZvLm5vZGUubmFtZTtcbiAgICAgICAgICAgIGZyb20gPSBub2RlSW5mby5ub2RlLnN0YXJ0O1xuICAgICAgICAgICAgdG8gPSBub2RlSW5mby5ub2RlLmVuZDtcbiAgICAgICAgfVxuICAgICAgICBjb25zdCB2YXJNYXAgPSBfY29tcHV0ZUljb25PZlByb3AoX2dldFJlYWRhYmxlVmFyTWFwKG5vZGVJbmZvLnZiKSk7XG5cbiAgICAgICAgY29uc3QgbGlzdCA9IFtdO1xuICAgICAgICBmb3IgKGxldCBbdiwgaV0gb2YgdmFyTWFwKSB7XG4gICAgICAgICAgICBpZiAodi5zdGFydHNXaXRoKHByZWZpeCkpIHtcbiAgICAgICAgICAgICAgICBsaXN0LnB1c2goe3RleHQ6IHYsIGljb246IGl9KTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgfVxuICAgICAgICByZXR1cm4gX1NIT1coe2xpc3Q6IGxpc3QsIGZyb206IGZyb20sIHRvOiB0b30pO1xuXG4gICAgfSBlbHNlIHtcbiAgICAgICAgLy8gcHJvcGVydHkgY29tcGxldGlvblxuICAgICAgICBjb25zdCBvYmplY3ROb2RlID0gbm9kZUluZm8ubm9kZS5vYmplY3Q7XG4gICAgICAgIGNvbnN0IHByb3BzID0gZ2V0UHJvcEZyb21Ob2RlKHJlc3VsdC7EiCwgb2JqZWN0Tm9kZSk7XG5cbiAgICAgICAgY29uc3QgcHJvcGVydHlOb2RlID0gbm9kZUluZm8ubm9kZS5wcm9wZXJ0eTtcbiAgICAgICAgbGV0IHByZWZpeCwgZnJvbSwgdG8sIGZpbHRlcjtcbiAgICAgICAgaWYgKG5vZGVJbmZvLnR5cGUgPT09ICd1c3VhbFByb3AnKSB7XG4gICAgICAgICAgICBjb25zdCBwcm9wTmFtZSA9IHByb3BlcnR5Tm9kZS5uYW1lO1xuICAgICAgICAgICAgaWYgKG15V2Fsa2VyLmlzRHVtbXlJZE5vZGUocHJvcGVydHlOb2RlKSkge1xuICAgICAgICAgICAgICAgIHByZWZpeCA9ICcnO1xuICAgICAgICAgICAgICAgIGZyb20gPSBwcm9wZXJ0eU5vZGUuZW5kOyAvLyBIZXJlLCBlbmQgaXMgY29ycmVjdCBmb3Igc3RhcnQgcG9zaXRpb25cbiAgICAgICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgICAgICAgLy8gcHJlZml4ID0gcHJvcE5hbWUuc3Vic3RyKDAsIHBvcyAtIHByb3BlcnR5Tm9kZS5zdGFydCk7XG4gICAgICAgICAgICAgICAgcHJlZml4ID0gcHJvcE5hbWU7XG4gICAgICAgICAgICAgICAgZnJvbSA9IHByb3BlcnR5Tm9kZS5zdGFydDtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIHRvID0gcHJvcGVydHlOb2RlLmVuZDtcbiAgICAgICAgICAgIGZpbHRlciA9IHAgPT4gKC9eWyRBLVpfXVswLTlBLVpfJF0qJC9pKS50ZXN0KHApO1xuICAgICAgICB9IGVsc2UgaWYgKG5vZGVJbmZvLnR5cGUgPT09ICdzdHJpbmdQcm9wJykge1xuICAgICAgICAgICAgcHJlZml4ID0gcHJvcGVydHlOb2RlLnZhbHVlO1xuICAgICAgICAgICAgZnJvbSA9IHByb3BlcnR5Tm9kZS5zdGFydCArIDE7XG4gICAgICAgICAgICB0byA9IHByb3BlcnR5Tm9kZS5lbmQgLSAxO1xuICAgICAgICAgICAgZmlsdGVyID0gcCA9PiB0cnVlXG4gICAgICAgIH1cblxuICAgICAgICBjb25zdCBsaXN0ID0gW107XG4gICAgICAgIGZvciAobGV0IFtwLCBpXSBvZiBwcm9wcykge1xuICAgICAgICAgICAgLy8gdW5rbm93biBwcm9wIGlzIG51bGxcbiAgICAgICAgICAgIGlmIChwICE9PSBudWxsICYmIHAuc3RhcnRzV2l0aChwcmVmaXgpICYmIGZpbHRlcihwKSkge1xuICAgICAgICAgICAgICAgIGxpc3QucHVzaCh7dGV4dDogcCwgaWNvbjogaX0pO1xuICAgICAgICAgICAgfVxuICAgICAgICB9XG4gICAgICAgIHJldHVybiBfU0hPVyh7bGlzdDogbGlzdCwgZnJvbTogZnJvbSwgdG86IHRvfSk7XG4gICAgfVxufVxuXG5cbmZ1bmN0aW9uIF91bmlvbk1hcChtMSwgbTIpIHtcbiAgICBjb25zdCByZXQgPSBuZXcgTWFwKCk7XG5cbiAgICBmdW5jdGlvbiB1bmlvblNldChzMSwgczIpIHtcbiAgICAgICAgY29uc3QgcmV0ID0gbmV3IFNldCgpO1xuICAgICAgICBpZiAoczEpIHMxLmZvckVhY2goZSA9PiByZXQuYWRkKGUpKTtcbiAgICAgICAgaWYgKHMyKSBzMi5mb3JFYWNoKGUgPT4gcmV0LmFkZChlKSk7XG4gICAgICAgIHJldHVybiByZXQ7XG4gICAgfVxuXG4gICAgaWYgKG0xKSBtMS5mb3JFYWNoKCh0cywgcCkgPT4gcmV0LnNldChwLCB0cykpO1xuICAgIGlmIChtMikgbTIuZm9yRWFjaCgodHMsIHApID0+IHJldC5zZXQocCwgdW5pb25TZXQocmV0LmdldChwKSwgbTIuZ2V0KHApKSkpO1xuICAgIHJldHVybiByZXQ7XG59XG5cbmZ1bmN0aW9uIF9hZGRPbmx5TWlzc2luZ01hcHBpbmdzKG0xLCBtMikge1xuICAgIGNvbnN0IHJldCA9IG5ldyBNYXAoKTtcbiAgICBtMS5mb3JFYWNoKCh0cywgcCkgPT4gcmV0LnNldChwLCB0cykpO1xuICAgIG0yLmZvckVhY2goKHRzLCBwKSA9PiB7XG4gICAgICAgIGlmICghcmV0LmhhcyhwKSkgcmV0LnNldChwLCB0cylcbiAgICB9KTtcbiAgICByZXR1cm4gcmV0O1xufVxuXG4vLyBjb252ZXJ0IGEgbWFwIG9mIEEgLT4gQVZhbFxuLy8gdG8gYSBtYXAgb2YgQSAtPiBTZXQuPFR5cGU+XG5mdW5jdGlvbiBfY29udmVydE1hcChtYXApIHtcbiAgICBsZXQgcmV0TWFwID0gbmV3IE1hcCgpO1xuICAgIG1hcC5mb3JFYWNoKChhdiwgcCkgPT4ge1xuICAgICAgICByZXRNYXAuc2V0KHAsIGF2LmdldFR5cGVzKCkpO1xuICAgIH0pO1xuICAgIHJldHVybiByZXRNYXA7XG59XG5cbi8vIHRyYXZlcnNlIGFic3RyYWN0IGhlYXAgc3BhY2VcbmZ1bmN0aW9uIF9nZXRSZWFkYWJsZVByb3BNYXAodHBzKSB7XG5cbiAgICBjb25zdCB2aXNpdGVkVHlwZXMgPSBbXTtcblxuICAgIGZ1bmN0aW9uIHRyYXZlcnNlKHR5cGUpIHtcbiAgICAgICAgaWYgKHR5cGUgaW5zdGFuY2VvZiB0eXBlcy5PYmpUeXBlICYmXG4gICAgICAgICAgICB0eXBlLmdldFByb3AoJ19fcHJvdG9fXycsIHRydWUpKSB7XG4gICAgICAgICAgICBsZXQgcHJvdG9NYXAgPSBuZXcgTWFwKCk7XG4gICAgICAgICAgICBjb25zdCBwcm90b1R5cGVzID0gdHlwZS5nZXRQcm9wKCdfX3Byb3RvX18nLCB0cnVlKS5nZXRUeXBlcygpO1xuXG4gICAgICAgICAgICBwcm90b1R5cGVzLmZvckVhY2godHAgPT4ge1xuICAgICAgICAgICAgICAgIGlmICh2aXNpdGVkVHlwZXMuaW5kZXhPZih0cCkgPiAtMSkge1xuICAgICAgICAgICAgICAgICAgICByZXR1cm47XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIHZpc2l0ZWRUeXBlcy5wdXNoKHRwKTtcbiAgICAgICAgICAgICAgICBwcm90b01hcCA9IF91bmlvbk1hcChwcm90b01hcCwgdHJhdmVyc2UodHApKTtcbiAgICAgICAgICAgICAgICB2aXNpdGVkVHlwZXMucG9wKCk7XG4gICAgICAgICAgICB9KTtcbiAgICAgICAgICAgIHJldHVybiBfYWRkT25seU1pc3NpbmdNYXBwaW5ncyhfY29udmVydE1hcCh0eXBlLnByb3BzKSwgcHJvdG9NYXApO1xuICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgICAgcmV0dXJuIG5ldyBNYXAoKTtcbiAgICAgICAgfVxuICAgIH1cblxuICAgIGxldCByZXRNYXAgPSBuZXcgTWFwKCk7XG4gICAgdHBzLmdldFR5cGVzKCkuZm9yRWFjaCh0cCA9PiB7XG4gICAgICAgIHJldE1hcCA9IF91bmlvbk1hcChyZXRNYXAsIHRyYXZlcnNlKHRwKSlcbiAgICB9KTtcblxuICAgIHJldHVybiByZXRNYXA7XG59XG5cbi8qKlxuICogUmV0dXJucyB0aGUgZGVmaW5pdGlvbiBzaXRlcyBvZiBmdW5jdGlvbnMgYXQgYHBvc2AuXG4gKiBAcGFyYW0gYXN0XG4gKiBAcGFyYW0gxIhcbiAqIEBwYXJhbSBwb3NcbiAqIEByZXR1cm5zIHtBcnJheX1cbiAqL1xuZXhwb3J0IGZ1bmN0aW9uIGdldERlZmluaXRpb25TaXRlc0F0KGFzdCwgxIgsIHBvcykge1xuICAgIGNvbnN0IG5vZGUgPSBteVdhbGtlci5maW5kU3Vycm91bmRpbmdOb2RlKGFzdCwgcG9zLCBwb3MpO1xuICAgIGNvbnN0IG5vZGVUeXBlcyA9IMSILmdldE1lcmdlZEFWYWxPZkxvYyhub2RlKTtcblxuICAgIGNvbnN0IHJhbmdlcyA9IFtdO1xuICAgIGlmIChub2RlVHlwZXMgPT09IG51bGwpIHtcbiAgICAgICAgcmV0dXJuIHJhbmdlcztcbiAgICB9XG4gICAgbm9kZVR5cGVzLmdldFR5cGVzKCkuZm9yRWFjaChmdW5jdGlvbiAodHApIHtcbiAgICAgICAgaWYgKHRwIGluc3RhbmNlb2YgdHlwZXMuRm5UeXBlICYmIHRwLm9yaWdpbk5vZGUpIHtcbiAgICAgICAgICAgIGNvbnN0IGZuTm9kZSA9IHRwLm9yaWdpbk5vZGU7XG4gICAgICAgICAgICBsZXQgYXQ7XG4gICAgICAgICAgICBzd2l0Y2ggKGZuTm9kZS50eXBlKSB7XG4gICAgICAgICAgICAgICAgY2FzZSAnRnVuY3Rpb25FeHByZXNzaW9uJyA6IGF0ID0gZm5Ob2RlLnN0YXJ0OyBicmVhaztcbiAgICAgICAgICAgICAgICBjYXNlICdGdW5jdGlvbkRlY2xhcmF0aW9uJyA6IGF0ID0gZm5Ob2RlLmlkLnN0YXJ0OyBicmVhaztcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGNvbnN0IGl0ZW0gPSB7c3RhcnQ6IGZuTm9kZS5zdGFydCwgZW5kOiBmbk5vZGUuZW5kLCBhdDogYXR9O1xuICAgICAgICAgICAgcmFuZ2VzLnB1c2goaXRlbSk7XG4gICAgICAgIH1cbiAgICB9KTtcbiAgICByZXR1cm4gcmFuZ2VzO1xufVxuXG4vLyB0cmF2ZXJzZSBhYnN0cmFjdCBzdGFjayBzcGFjZVxuZnVuY3Rpb24gX2dldFJlYWRhYmxlVmFyTWFwKHZiKSB7XG4gICAgbGV0IGN1cnJWQiA9IHZiO1xuICAgIGxldCByZXRNYXAgPSBuZXcgTWFwKCk7XG4gICAgd2hpbGUgKGN1cnJWQiAhPT0gbnVsbCkge1xuICAgICAgICBsZXQgbWVyZ2VkTWFwID0gbmV3IE1hcCgpO1xuICAgICAgICBmb3IgKGxldCB2YXJNYXAgb2YgY3VyclZCLmluc3RhbmNlcy52YWx1ZXMoKSkge1xuICAgICAgICAgICAgbWVyZ2VkTWFwID0gX3VuaW9uTWFwKG1lcmdlZE1hcCwgX2NvbnZlcnRNYXAodmFyTWFwKSk7XG4gICAgICAgIH1cbiAgICAgICAgcmV0TWFwID0gX2FkZE9ubHlNaXNzaW5nTWFwcGluZ3MocmV0TWFwLCBtZXJnZWRNYXApO1xuICAgICAgICBjdXJyVkIgPSBjdXJyVkIucGFyZW47XG4gICAgfVxuICAgIHJldHVybiByZXRNYXA7XG59XG4iLCIvKipcbiAqIEBmaWxlIFNvbWUgaGVscGVyIGZ1bmN0aW9uc1xuICogQGF1dGhvciBzZXdvbjMyNi5raW1Ac2Ftc3VuZy5jb21cbiAqL1xuXG52YXIgdXRpbCA9IHJlcXVpcmUoJ3V0aWwnKTtcblxuZXhwb3J0IGZ1bmN0aW9uIGdldE5vZGVMaXN0KGFzdCwgc3RhcnROdW0pIHtcbiAgICB2YXIgbm9kZUxpc3QgPSBbXTtcblxuICAgIHZhciBudW0gPSBzdGFydE51bSA9PT0gdW5kZWZpbmVkID8gMCA6IHN0YXJ0TnVtO1xuXG4gICAgZnVuY3Rpb24gYXNzaWduSWQobm9kZSkge1xuICAgICAgICBub2RlWydAbGFiZWwnXSA9IG51bTtcbiAgICAgICAgbm9kZUxpc3QucHVzaChub2RlKTtcbiAgICAgICAgbnVtKys7XG4gICAgfVxuXG4gICAgLy8gTGFiZWwgZXZlcnkgQVNUIG5vZGUgd2l0aCBwcm9wZXJ0eSAndHlwZSdcbiAgICBmdW5jdGlvbiBsYWJlbE5vZGVXaXRoVHlwZShub2RlKSB7XG4gICAgICAgIGlmIChub2RlICYmIG5vZGUuaGFzT3duUHJvcGVydHkoJ3R5cGUnKSkge1xuICAgICAgICAgICAgYXNzaWduSWQobm9kZSk7XG4gICAgICAgIH1cbiAgICAgICAgaWYgKG5vZGUgJiYgdHlwZW9mIG5vZGUgPT09ICdvYmplY3QnKSB7XG4gICAgICAgICAgICBmb3IgKHZhciBwIGluIG5vZGUpIHtcbiAgICAgICAgICAgICAgICBsYWJlbE5vZGVXaXRoVHlwZShub2RlW3BdKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgfVxuICAgIH1cblxuICAgIGxhYmVsTm9kZVdpdGhUeXBlKGFzdCk7XG5cbiAgICByZXR1cm4gbm9kZUxpc3Q7XG59XG5cbmV4cG9ydCBmdW5jdGlvbiBzaG93VW5mb2xkZWQob2JqKSB7XG4gICAgY29uc29sZS5sb2codXRpbC5pbnNwZWN0KG9iaiwge2RlcHRoOiBudWxsfSkpO1xufVxuIiwiLyoqXG4gKiBAZmlsZSBEZWZpbmVzIGBhbmFseXplYCBmdW5jdGlvbiBhbmQgZXhwb3J0cyBxdWVyeSBmdW5jdGlvbnNcbiAqIEBhdXRob3Igc2V3b24zMjYua2ltQHNhbXN1bmcuY29tXG4gKi9cblxuLy8gaW1wb3J0IG5lY2Vzc2FyeSBsaWJyYXJpZXNcbmNvbnN0IGFjb3JuID0gcmVxdWlyZSgnYWNvcm4vZGlzdC9hY29ybicpO1xuY29uc3QgYWNvcm5fbG9vc2UgPSByZXF1aXJlKCdhY29ybi9kaXN0L2Fjb3JuX2xvb3NlJyk7XG5jb25zdCBhdXggPSByZXF1aXJlKCcuL2hlbHBlcicpO1xuaW1wb3J0ICogYXMgdHlwZXMgZnJvbSAnLi9kb21haW5zL3R5cGVzJ1xuaW1wb3J0ICogYXMgY29udGV4dCBmcm9tICcuL2RvbWFpbnMvY29udGV4dCdcbi8vIGNvbnN0IHN0YXR1cyA9IHJlcXVpcmUoJy4vZG9tYWlucy9zdGF0dXMnKTtcbmltcG9ydCAqIGFzIHN0YXR1cyBmcm9tICcuL2RvbWFpbnMvc3RhdHVzJ1xuaW1wb3J0ICogYXMgdmFyQmxvY2sgZnJvbSAnLi92YXJCbG9jaydcbmNvbnN0IGNHZW4gPSByZXF1aXJlKCcuL2NvbnN0cmFpbnQvY0dlbicpO1xuY29uc3QgdmFyUmVmcyA9IHJlcXVpcmUoJy4vdmFycmVmcycpO1xuY29uc3QgcmV0T2NjdXIgPSByZXF1aXJlKCcuL3JldE9jY3VyJyk7XG5jb25zdCB0aGlzT2NjdXIgPSByZXF1aXJlKCcuL3RoaXNPY2N1cicpO1xuaW1wb3J0ICogYXMgbXlXYWxrZXIgZnJvbSAnLi91dGlsL215V2Fsa2VyJ1xuaW1wb3J0ICogYXMgZ2V0VHlwZURhdGEgZnJvbSAnLi9nZXRUeXBlRGF0YSdcbmltcG9ydCAqIGFzIGRlZmF1bHRPcHRpb24gZnJvbSAnLi4vZGVmYXVsdE9wdGlvbidcblxuLyoqXG4gKiBBbmFseXplIGEgSmF2YVNjcmlwdCBjb2RlXG4gKiBAcGFyYW0ge3N0cmluZ30gaW5wdXQgLSBwcm9ncmFtIGNvZGVcbiAqIEBwYXJhbSB7Ym9vbGVhbn0gcmV0QWxsIC0gd2hldGhlciB0byByZXR1cm4gYWxsIGFuYWx5emVkIGRhdGFcbiAqIEBwYXJhbSBvcHRpb24gLSBhbmFseXNpcyBvcHRpb25cbiAqIEByZXR1cm5zIHsqfVxuICovXG5leHBvcnQgZnVuY3Rpb24gYW5hbHl6ZShpbnB1dCwgcmV0QWxsLCBvcHRpb24pIHtcbiAgICAvLyB0aGUgU2NvcGUgb2JqZWN0IGZvciBnbG9iYWwgc2NvcGVcbiAgICAvLyBzY29wZS5TY29wZS5nbG9iYWxTY29wZSA9IG5ldyBzY29wZS5TY29wZShudWxsKTtcblxuICAgIGlmIChvcHRpb24gPT09IHVuZGVmaW5lZCkge1xuICAgICAgICAvLyBpZiBubyBvcHRpb24gaXMgZ2l2ZW4sIHVzZSB0aGUgZGVmYXVsdCBvcHRpb25cbiAgICAgICAgb3B0aW9uID0gZGVmYXVsdE9wdGlvbi5vcHRpb25zO1xuICAgIH1cbiAgICAvLyBwYXJzaW5nIGlucHV0IHByb2dyYW1cbiAgICB2YXIgYXN0O1xuICAgIHRyeSB7XG4gICAgICAgIGFzdCA9IGFjb3JuLnBhcnNlKGlucHV0LCBvcHRpb24uYWNvcm5PcHRpb24pO1xuICAgIH0gY2F0Y2ggKGUpIHtcbiAgICAgICAgYXN0ID0gYWNvcm5fbG9vc2UucGFyc2VfZGFtbWl0KGlucHV0LCBvcHRpb24uYWNvcm5PcHRpb24pO1xuICAgIH1cblxuICAgIHZhciBub2RlQXJyYXlJbmRleGVkQnlMaXN0ID0gYXV4LmdldE5vZGVMaXN0KGFzdCk7XG5cbiAgICAvLyBTaG93IEFTVCBiZWZvcmUgc2NvcGUgcmVzb2x1dGlvblxuICAgIC8vIGF1eC5zaG93VW5mb2xkZWQoYXN0KTtcblxuICAgIHZhciBnVmFyQmxvY2sgPSBuZXcgdmFyQmxvY2suVmFyQmxvY2soXG4gICAgICAgIG51bGwsXG4gICAgICAgIGFzdCxcbiAgICAgICAgdmFyQmxvY2suVmFyQmxvY2suYmxvY2tUeXBlcy5nbG9iYWxCbG9jayxcbiAgICAgICAgLy8gJ3VzZSBzdHJpY3QnIGRpcmVjdGl2ZSBpcyBjaGVja2VkIGluIGFubm90YXRlQmxvY2tJbmZvLlxuICAgICAgICBvcHRpb24uYWNvcm5PcHRpb24uc291cmNlVHlwZSA9PT0gJ21vZHVsZSdcbiAgICApO1xuXG4gICAgdmFyQmxvY2suYW5ub3RhdGVCbG9ja0luZm8oYXN0LCBnVmFyQmxvY2spO1xuXG4gICAgLy8gU2V0dGluZyB1cCB0aGUgc2Vuc2l0aXZpdHkgcGFyYW1ldGVyXG4gICAgLy8gSXQgaXMgcG9zc2libGUgdG8gY29tcHV0ZSB0aGUgcGFyYW1ldGVyIGJ5IGV4YW1pbmluZyB0aGUgY29kZS5cbiAgICBjb250ZXh0LmNoYW5nZVNlbnNpdGl2aXR5UGFyYW1ldGVyKG9wdGlvbi5zZW5zaXRpdml0eVBhcmFtZXRlcik7XG5cbiAgICB2YXIgZ0Jsb2NrID0gYXN0WydAYmxvY2snXTtcbiAgICB2YXIgaW5pdGlhbENvbnRleHQgPSBjb250ZXh0LkNhbGxTaXRlQ29udGV4dC5lcHNpbG9uQ29udGV4dDtcbiAgICB2YXIgZ1Njb3BlID0gZ0Jsb2NrLmdldFNjb3BlSW5zdGFuY2UobnVsbCwgaW5pdGlhbENvbnRleHQpO1xuICAgIHZhciBnT2JqZWN0ID0gdHlwZXMubWtPYmpGcm9tR2xvYmFsU2NvcGUoZ1Njb3BlKTtcbiAgICB2YXIgaW5pdFN0YXR1cyA9IG5ldyBzdGF0dXMuU3RhdHVzKFxuICAgICAgICBuZXcgdHlwZXMuQVZhbChnT2JqZWN0KSxcbiAgICAgICAgdHlwZXMuQVZhbE51bGwsXG4gICAgICAgIHR5cGVzLkFWYWxOdWxsLFxuICAgICAgICBpbml0aWFsQ29udGV4dCxcbiAgICAgICAgZ1Njb3BlKTtcbiAgICAvLyB0aGUgcHJvdG90eXBlIG9iamVjdCBvZiBPYmplY3RcbiAgICB2YXIgT2JqUHJvdG8gPSBuZXcgdHlwZXMuT2JqVHlwZShudWxsLCAnT2JqZWN0LnByb3RvdHlwZScpO1xuICAgIHZhciBydENYID0ge1xuICAgICAgICBnbG9iYWxPYmplY3Q6IGdPYmplY3QsXG4gICAgICAgIC8vIHRlbXBvcmFsXG4gICAgICAgIHByb3Rvczoge1xuICAgICAgICAgICAgT2JqZWN0OiBPYmpQcm90byxcbiAgICAgICAgICAgIEZ1bmN0aW9uOiBuZXcgdHlwZXMuT2JqVHlwZShuZXcgdHlwZXMuQVZhbChPYmpQcm90byksICdGdW5jdGlvbi5wcm90b3R5cGUnKSxcbiAgICAgICAgICAgIEFycmF5OiBuZXcgdHlwZXMuT2JqVHlwZShuZXcgdHlwZXMuQVZhbChPYmpQcm90byksICdBcnJheS5wcm90b3R5cGUnKSxcbiAgICAgICAgICAgIFJlZ0V4cDogbmV3IHR5cGVzLk9ialR5cGUobmV3IHR5cGVzLkFWYWwoT2JqUHJvdG8pLCAnUmVnRXhwLnByb3RvdHlwZScpLFxuICAgICAgICAgICAgU3RyaW5nOiBuZXcgdHlwZXMuT2JqVHlwZShuZXcgdHlwZXMuQVZhbChPYmpQcm90byksICdTdHJpbmcucHJvdG90eXBlJyksXG4gICAgICAgICAgICBOdW1iZXI6IG5ldyB0eXBlcy5PYmpUeXBlKG5ldyB0eXBlcy5BVmFsKE9ialByb3RvKSwgJ051bWJlci5wcm90b3R5cGUnKSxcbiAgICAgICAgICAgIEJvb2xlYW46IG5ldyB0eXBlcy5PYmpUeXBlKG5ldyB0eXBlcy5BVmFsKE9ialByb3RvKSwgJ0Jvb2xlYW4ucHJvdG90eXBlJylcbiAgICAgICAgfSxcbiAgICAgICAgxIg6IG5ldyB0eXBlcy5BYnNDYWNoZSgpLFxuICAgICAgICBvcHRpb246IG9wdGlvblxuICAgIH07XG4gICAgY0dlbi5hZGRDb25zdHJhaW50cyhhc3QsIGluaXRTdGF0dXMsIHJ0Q1gpO1xuICAgIC8vYXV4LnNob3dVbmZvbGRlZChnQmxvY2tBbmRBbm5vdGF0ZWRBU1QuYXN0KTtcbiAgICAvLyBhdXguc2hvd1VuZm9sZGVkKGNvbnN0cmFpbnRzKTtcbiAgICAvLyBhdXguc2hvd1VuZm9sZGVkKGdCbG9jayk7XG4gICAgLy8gY29uc29sZS5sb2codXRpbC5pbnNwZWN0KGdCbG9jaywge2RlcHRoOiAxMH0pKTtcbiAgICBpZiAocmV0QWxsKSB7XG4gICAgICAgIHJldHVybiB7XG4gICAgICAgICAgICBnT2JqZWN0OiBnT2JqZWN0LFxuICAgICAgICAgICAgQVNUOiBhc3QsXG4gICAgICAgICAgICBnQmxvY2s6IGdCbG9jayxcbiAgICAgICAgICAgIGdTY29wZTogZ1Njb3BlLFxuICAgICAgICAgICAgxIg6IHJ0Q1guxIhcbiAgICAgICAgfTtcbiAgICB9IGVsc2Uge1xuICAgICAgICByZXR1cm4gZ09iamVjdDtcbiAgICB9XG59XG5cbi8vIGV4cG9ydHMgcXVlcnkgZnVuY3Rpb25zXG5leHBvcnRzLmZpbmRJZGVudGlmaWVyQXQgPSBteVdhbGtlci5maW5kSWRlbnRpZmllckF0O1xuZXhwb3J0cy5maW5kVmFyUmVmc0F0ID0gdmFyUmVmcy5maW5kVmFyUmVmc0F0O1xuZXhwb3J0cy5vbkVzY2FwaW5nU3RhdGVtZW50ID0gcmV0T2NjdXIub25Fc2NhcGluZ1N0YXRlbWVudDtcbmV4cG9ydHMuZmluZEVzY2FwaW5nU3RhdGVtZW50cyA9IHJldE9jY3VyLmZpbmRFc2NhcGluZ1N0YXRlbWVudHM7XG5leHBvcnRzLm9uVGhpc0tleXdvcmQgPSB0aGlzT2NjdXIub25UaGlzS2V5d29yZDtcbmV4cG9ydHMuZmluZFRoaXNFeHByZXNzaW9ucyA9IHRoaXNPY2N1ci5maW5kVGhpc0V4cHJlc3Npb25zO1xuZXhwb3J0cy5maW5kU3Vycm91bmRpbmdOb2RlID0gbXlXYWxrZXIuZmluZFN1cnJvdW5kaW5nTm9kZTtcbmV4cG9ydHMuZmluZE1lbWJlck9yVmFyaWFibGVBdCA9IG15V2Fsa2VyLmZpbmRNZW1iZXJPclZhcmlhYmxlQXQ7XG5leHBvcnRzLmdldFR5cGVEYXRhID0gZ2V0VHlwZURhdGEuZ2V0VHlwZUF0UmFuZ2U7XG5leHBvcnRzLmdldENvbXBsZXRpb25BdFBvcyA9IGdldFR5cGVEYXRhLmdldENvbXBsZXRpb25BdFBvcztcbmV4cG9ydHMuZ2V0Rm5UeXBlU3RydWN0dXJlc0F0ID0gZ2V0VHlwZURhdGEuZ2V0Rm5UeXBlU3RydWN0dXJlc0F0O1xuZXhwb3J0cy5nZXREZWZpbml0aW9uU2l0ZXNBdCA9IGdldFR5cGVEYXRhLmdldERlZmluaXRpb25TaXRlc0F0O1xuIiwiLyoqXG4gKiBAZmlsZSBJbXBsZW1lbnRzIHJldHVybiAvIGVzY2FwaW5nIHN0YXRlbWVudHMgZmluZGVyXG4gKiBAYXV0aG9yIHNld29uMzI2LmtpbUBzYW1zdW5nLmNvbVxuICovXG5cbmNvbnN0IHdhbGsgPSByZXF1aXJlKCdhY29ybi9kaXN0L3dhbGsnKTtcbmltcG9ydCAqIGFzIG15V2Fsa2VyIGZyb20gJy4vdXRpbC9teVdhbGtlcidcblxuLyoqXG4gKiBhdXhpbGlhcnkgZnVuY3Rpb24gZm9yIHZpc2l0b3IncyBzdGF0ZSBjaGFuZ2VcbiAqIEBwYXJhbSBub2RlXG4gKiBAcGFyYW0gc3RcbiAqIEBwYXJhbSBub2RlVHlwZVxuICogQHJldHVybiB7Kn1cbiAqL1xuZnVuY3Rpb24gX3N0Q2hhbmdlKG5vZGUsIHN0LCBub2RlVHlwZSkge1xuICAgIGNvbnN0IFtmbk5vZGUsIHRyeU5vZGUsIG91dGVyVHJ5Tm9kZV0gPSBzdDtcbiAgICBzd2l0Y2ggKG5vZGVUeXBlKSB7XG4gICAgICAgIGNhc2UgJ0Z1bmN0aW9uRGVjbGFyYXRpb24nOlxuICAgICAgICBjYXNlICdGdW5jdGlvbkV4cHJlc3Npb24nOlxuICAgICAgICBjYXNlICdBcnJvd0Z1bmN0aW9uRXhwcmVzc2lvbic6XG4gICAgICAgICAgICByZXR1cm4gW25vZGUsIHVuZGVmaW5lZF07XG4gICAgICAgIGNhc2UgJ1RyeVN0YXRlbWVudCc6XG4gICAgICAgICAgICAvLyByZW1lbWJlciBvdXRlciB0cnlOb2RlXG4gICAgICAgICAgICByZXR1cm4gW2ZuTm9kZSwgbm9kZSwgdHJ5Tm9kZV07XG4gICAgICAgIGNhc2UgJ0NhdGNoQ2xhdXNlJzpcbiAgICAgICAgICAgIC8vIHVzZSBvdXRlciB0cnkgYXMgaXRzIHRyeU5vZGVcbiAgICAgICAgICAgIHJldHVybiBbZm5Ob2RlLCBvdXRlclRyeU5vZGVdO1xuICAgICAgICBjYXNlICdCbG9ja1N0YXRlbWVudCc6XG4gICAgICAgICAgICBpZiAoc3Qub3V0ZXIpIHtcbiAgICAgICAgICAgICAgICAvLyBpdCdzIGZpbmFsbHkgYmxvY2tcbiAgICAgICAgICAgICAgICByZXR1cm4gW2ZuTm9kZSwgb3V0ZXJUcnlOb2RlXTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgIC8vIGl0J3MgdHJ5IGJsb2NrXG4gICAgICAgICAgICAgICAgcmV0dXJuIFtmbk5vZGUsIHRyeU5vZGUsIG91dGVyVHJ5Tm9kZV07XG4gICAgICAgICAgICB9XG4gICAgICAgIGRlZmF1bHQ6XG4gICAgICAgICAgICByZXR1cm4gW2ZuTm9kZSwgdHJ5Tm9kZSwgb3V0ZXJUcnlOb2RlXTtcbiAgICB9XG59XG5cbi8qKlxuICogQ2hlY2sgd2hldGhlciBnaXZlbiBwb3MgaXMgb24gYSBmdW5jdGlvbiBrZXl3b3JkXG4gKiBAcGFyYW0gYXN0IC0gQVNUIG9mIGEgcHJvZ3JhbVxuICogQHBhcmFtIHBvcyAtIGluZGV4IHBvc2l0aW9uXG4gKiBAcmV0dXJuIHsqfSAtIGZ1bmN0aW9uIG5vZGUgb3IgbnVsbFxuICovXG5leHBvcnQgZnVuY3Rpb24gb25Fc2NhcGluZ1N0YXRlbWVudChhc3QsIHBvcykge1xuICAgICd1c2Ugc3RyaWN0JztcblxuICAgIC8vIGZpbmQgZnVuY3Rpb24gbm9kZVxuICAgIC8vIHN0IGlzIHRoZSBlbmNsb3NpbmcgZnVuY3Rpb25cbiAgICBjb25zdCB3YWxrZXIgPSBteVdhbGtlci53cmFwV2Fsa2VyKHdhbGsubWFrZSh7XG4gICAgICAgICAgICBUcnlTdGF0ZW1lbnQ6IChub2RlLCBzdCwgYykgPT4ge1xuICAgICAgICAgICAgICAgIGMobm9kZS5ibG9jaywgc3QpO1xuICAgICAgICAgICAgICAgIC8vIHNldCBmbGFnIGFmdGVyIHByb2Nlc3NpbmcgdHJ5IGJsb2NrXG4gICAgICAgICAgICAgICAgc3Qub3V0ZXIgPSB0cnVlO1xuICAgICAgICAgICAgICAgIGlmIChub2RlLmhhbmRsZXIpIGMobm9kZS5oYW5kbGVyLCBzdCk7XG4gICAgICAgICAgICAgICAgaWYgKG5vZGUuZmluYWxpemVyKSBjKG5vZGUuZmluYWxpemVyLCBzdCk7XG4gICAgICAgICAgICB9LFxuICAgICAgICAgICAgQ2F0Y2hDbGF1c2U6IChub2RlLCBzdCwgYykgPT4ge1xuICAgICAgICAgICAgICAgIGMobm9kZS5ib2R5LCBzdCk7XG4gICAgICAgICAgICB9XG4gICAgICAgIH0sIHdhbGsuYmFzZSksXG4gICAgICAgIC8vIHByZVxuICAgICAgICAobm9kZSwgc3QsIG5vZGVUeXBlKSA9PiB7XG4gICAgICAgICAgICBpZiAobm9kZS5zdGFydCA+IHBvcyB8fCBub2RlLmVuZCA8IHBvcykge1xuICAgICAgICAgICAgICAgIHJldHVybiBmYWxzZTtcbiAgICAgICAgICAgIH1cblxuICAgICAgICAgICAgLy8gb24gYSBmdW5jdGlvbiBrZXl3b3JkLCA4IGlzIHRoZSBsZW5ndGggb2YgJ2Z1bmN0aW9uJ1xuICAgICAgICAgICAgLy8gb3Igb24gcmV0dXJuIGtleXdvcmQsIDYgaXMgdGhlIGxlbmd0aCBvZiAncmV0dXJuJ1xuICAgICAgICAgICAgLy8gb3Igb24gdGhyb3cga2V5d29yZCwgNSBpcyB0aGUgbGVuZ3RoIG9mICd0aHJvdydcbiAgICAgICAgICAgIGlmICgoKG5vZGVUeXBlID09PSAnRnVuY3Rpb25EZWNsYXJhdGlvbicgfHwgbm9kZVR5cGUgPT09ICdGdW5jdGlvbkV4cHJlc3Npb24nKVxuICAgICAgICAgICAgICAgICYmIChub2RlLnN0YXJ0IDw9IHBvcyAmJiBwb3MgPD0gbm9kZS5zdGFydCArIDgpKVxuICAgICAgICAgICAgICAgIHx8XG4gICAgICAgICAgICAgICAgKG5vZGVUeXBlID09PSAnUmV0dXJuU3RhdGVtZW50J1xuICAgICAgICAgICAgICAgICYmIChub2RlLnN0YXJ0IDw9IHBvcyAmJiBwb3MgPD0gbm9kZS5zdGFydCArIDYpKVxuICAgICAgICAgICAgICAgIHx8XG4gICAgICAgICAgICAgICAgKG5vZGVUeXBlID09PSAnVGhyb3dTdGF0ZW1lbnQnXG4gICAgICAgICAgICAgICAgJiYgKG5vZGUuc3RhcnQgPD0gcG9zICYmIHBvcyA8PSBub2RlLnN0YXJ0ICsgNSkpKSB7XG4gICAgICAgICAgICAgICAgLy8gcmVjb3JkIHRoZSBmb3VuZCBub2RlIHR5cGVcbiAgICAgICAgICAgICAgICBzdC50eXBlID0gbm9kZS50eXBlO1xuICAgICAgICAgICAgICAgIHRocm93IHN0O1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgcmV0dXJuIHRydWU7XG4gICAgICAgIH0sXG4gICAgICAgIC8vIHBvc3RcbiAgICAgICAgdW5kZWZpbmVkLFxuICAgICAgICBfc3RDaGFuZ2VcbiAgICApO1xuXG4gICAgdHJ5IHtcbiAgICAgICAgd2Fsay5yZWN1cnNpdmUoYXN0LCBbXSwgd2Fsa2VyKTtcbiAgICB9IGNhdGNoIChlKSB7XG4gICAgICAgIGlmIChlICYmIGUgaW5zdGFuY2VvZiBBcnJheSkge1xuICAgICAgICAgICAgLy8gZm91bmRcbiAgICAgICAgICAgIHJldHVybiBlO1xuICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgICAgLy8gb3RoZXIgZXJyb3JcbiAgICAgICAgICAgIHRocm93IGU7XG4gICAgICAgIH1cbiAgICB9XG4gICAgLy8gaWRlbnRpZmllciBub3QgZm91bmRcbiAgICByZXR1cm4gbnVsbDtcbn1cblxuLyoqXG4gKiBHaXZlbiBhIG5vZGUsIGZpbmQgaXRzIGVzY2FwaW5nIG5vZGVzXG4gKlxuICogQHBhcmFtIG5vZGVQYWlyIC0gQVNUIG5vZGUgb2YgYSBmdW5jdGlvbiwgcG9zc2libHkgd2l0aCBubyBhbm5vdGF0aW9uXG4gKiBAcmV0dXJuIHsqfSAtIGFycmF5IG9mIEFTVCBub2Rlc1xuICovXG5mdW5jdGlvbiBfZ2V0RXNjYXBpbmdOb2Rlcyhub2RlUGFpcikge1xuICAgICd1c2Ugc3RyaWN0JztcbiAgICBjb25zdCBub2RlcyA9IFtdO1xuICAgIGNvbnN0IFtmbk5vZGUsIHRyeU5vZGVdID0gbm9kZVBhaXI7XG5cbiAgICBjb25zdCB3YWxrZXIgPSBteVdhbGtlci53cmFwV2Fsa2VyKFxuICAgICAgICB3YWxrLm1ha2Uoe1xuICAgICAgICAgICAgVHJ5U3RhdGVtZW50OiAobm9kZSwgc3QsIGMpID0+IHtcbiAgICAgICAgICAgICAgICBjKG5vZGUuYmxvY2ssIHN0KTtcbiAgICAgICAgICAgICAgICAvLyBzZXQgZmxhZyBhZnRlciBwcm9jZXNzaW5nIHRyeSBibG9ja1xuICAgICAgICAgICAgICAgIHN0Lm91dGVyID0gdHJ1ZTtcbiAgICAgICAgICAgICAgICAvLyB2aXNpdCB0aG9zZSBCbG9ja1N0YXRlbWVudFxuICAgICAgICAgICAgICAgIGlmIChub2RlLmhhbmRsZXIpIGMobm9kZS5oYW5kbGVyLCBzdCk7XG4gICAgICAgICAgICAgICAgaWYgKG5vZGUuZmluYWxpemVyKSBjKG5vZGUuZmluYWxpemVyLCBzdCk7XG4gICAgICAgICAgICB9LFxuICAgICAgICAgICAgUmV0dXJuU3RhdGVtZW50OiAobm9kZSkgPT4ge1xuICAgICAgICAgICAgICAgIGlmIChub2RlUGFpci50eXBlID09PSAnVGhyb3dTdGF0ZW1lbnQnICYmIHRyeU5vZGUpIHJldHVybjtcbiAgICAgICAgICAgICAgICBub2Rlcy5wdXNoKG5vZGUpO1xuICAgICAgICAgICAgfSxcbiAgICAgICAgICAgIEZ1bmN0aW9uOiAoKSA9PiB7XG4gICAgICAgICAgICAgICAgLy8gbm90IHZpc2l0IGlubmVyIGZ1bmN0aW9uc1xuICAgICAgICAgICAgfSxcbiAgICAgICAgICAgIFRocm93U3RhdGVtZW50OiAobm9kZSwgW2YsdF0pID0+IHtcbiAgICAgICAgICAgICAgICBpZiAoKG5vZGVQYWlyLnR5cGUgPT09ICdUaHJvd1N0YXRlbWVudCcgJiYgdHJ5Tm9kZSA9PT0gdClcbiAgICAgICAgICAgICAgICAgICAgfHwgdCA9PT0gdW5kZWZpbmVkKSB7XG4gICAgICAgICAgICAgICAgICAgIG5vZGVzLnB1c2gobm9kZSk7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgfSxcbiAgICAgICAgICAgIENhdGNoQ2xhdXNlOiAobm9kZSwgc3QsIGMpID0+IHtcbiAgICAgICAgICAgICAgICBjKG5vZGUuYm9keSwgc3QpO1xuICAgICAgICAgICAgfVxuICAgICAgICB9LCB3YWxrLmJhc2UpLFxuICAgICAgICB1bmRlZmluZWQsXG4gICAgICAgIHVuZGVmaW5lZCxcbiAgICAgICAgX3N0Q2hhbmdlKTtcblxuICAgIGlmIChub2RlUGFpci50eXBlID09PSAnVGhyb3dTdGF0ZW1lbnQnICYmIHRyeU5vZGUpIHtcbiAgICAgICAgd2Fsay5yZWN1cnNpdmUodHJ5Tm9kZS5ibG9jaywgW3VuZGVmaW5lZCwgdHJ5Tm9kZV0sIHdhbGtlcik7XG4gICAgfSBlbHNlIHtcbiAgICAgICAgd2Fsay5yZWN1cnNpdmUoZm5Ob2RlLmJvZHksIFtmbk5vZGUsIHVuZGVmaW5lZF0sIHdhbGtlcik7XG4gICAgfVxuXG4gICAgcmV0dXJuIG5vZGVzO1xufVxuXG4vKipcbiAqIEZpbmQgcmV0dXJuIG5vZGVzIGNvcnJlc3BvbmRpbmcgdG8gdGhlIHBvc2l0aW9uXG4gKiBpZiB0aGUgcG9zIGlzIG9uIGEgZnVuY3Rpb24ga2V5d29yZFxuICpcbiAqIEBwYXJhbSBhc3QgLSBBU1Qgbm9kZSBvZiBhIHByb2dyYW0sIHBvc3NpYmx5IHdpdGggbm8gYW5ub3RhdGlvblxuICogQHBhcmFtIHBvcyAtIGN1cnNvciBwb3NpdGlvblxuICogQHBhcmFtIGluY2x1ZGVLZXl3b3JkIC0gd2hldGhlciB0byBpbmNsdWRlIGtleXdvcmQgcmFuZ2VcbiAqIEByZXR1cm4ge0FycmF5fSAtIGFycmF5IG9mIEFTVCBub2RlcyBvZiBlc2NhcGluZyBzdGF0ZW1lbnRzXG4gKi9cbmV4cG9ydCBmdW5jdGlvbiBmaW5kRXNjYXBpbmdTdGF0ZW1lbnRzKGFzdCwgcG9zLCBpbmNsdWRlS2V5d29yZCkge1xuICAgICd1c2Ugc3RyaWN0JztcblxuICAgIGNvbnN0IG5vZGVQYWlyID0gb25Fc2NhcGluZ1N0YXRlbWVudChhc3QsIHBvcyk7XG4gICAgaWYgKCFub2RlUGFpcikge1xuICAgICAgICByZXR1cm4gbnVsbDtcbiAgICB9XG5cbiAgICBjb25zdCByYW5nZXMgPSBfZ2V0RXNjYXBpbmdOb2Rlcyhub2RlUGFpcikubWFwKFxuICAgICAgICAgICAgbm9kZSA9PiB7XG4gICAgICAgICAgICAgICAgcmV0dXJuIHtzdGFydDogbm9kZS5zdGFydCwgZW5kOiBub2RlLmVuZH07XG4gICAgICAgICAgICB9KTtcbiAgICBjb25zdCBbZm5Ob2RlLCB0cnlOb2RlXSA9IG5vZGVQYWlyO1xuICAgIC8vIElmIG5vIGV4cGxpY2l0IGVzY2FwaW5nIGV4aXN0c1xuICAgIC8vIGhpZ2hsaWdodCB0aGUgY2xvc2luZyBicmFjZSBvZiB0aGUgZnVuY3Rpb24gYm9keVxuICAgIGlmIChub2RlUGFpci50eXBlICE9PSAnVGhyb3dTdGF0ZW1lbnQnICYmIHJhbmdlcy5sZW5ndGggPT09IDApIHtcbiAgICAgICAgcmFuZ2VzLnB1c2goe3N0YXJ0OiBmbk5vZGUuZW5kIC0gMSwgZW5kOiBmbk5vZGUuZW5kfSk7XG4gICAgfVxuXG4gICAgLy8gaGlnaGxpZ2h0aW5nICdjYXRjaCdcbiAgICBpZiAobm9kZVBhaXIudHlwZSA9PT0gJ1Rocm93U3RhdGVtZW50JyAmJiB0cnlOb2RlKSB7XG4gICAgICAgIHJhbmdlcy5wdXNoKHtzdGFydDogdHJ5Tm9kZS5oYW5kbGVyLnN0YXJ0LCBlbmQ6IHRyeU5vZGUuaGFuZGxlci5zdGFydCArIDV9KTtcbiAgICB9IGVsc2UgaWYgKGluY2x1ZGVLZXl3b3JkKSB7XG4gICAgICAgIGlmIChmbk5vZGUudHlwZSAhPT0gJ0Fycm93RnVuY3Rpb25FeHByZXNzaW9uJykge1xuICAgICAgICAgICAgLy8gYWRkIHJhbmdlcyBmb3IgJ2Z1bmN0aW9uJ1xuICAgICAgICAgICAgcmFuZ2VzLnB1c2goe3N0YXJ0OiBmbk5vZGUuc3RhcnQsIGVuZDogZm5Ob2RlLnN0YXJ0ICsgOH0pO1xuICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgICAgLy8gVE9ETzogYWRkIHJhbmdlIGZvciBmYXQgYXJyb3dcbiAgICAgICAgfVxuICAgIH1cbiAgICByZXR1cm4gcmFuZ2VzO1xufVxuIiwiLyoqXG4gKiBAZmlsZSBJbXBsZW1lbnRzIHRoaXMgb2NjdXJyZW5jZSBmaW5kZXJcbiAqIEBhdXRob3Igc2V3b24zMjYua2ltQHNhbXN1bmcuY29tXG4gKi9cblxuY29uc3Qgd2FsayA9IHJlcXVpcmUoJ2Fjb3JuL2Rpc3Qvd2FsaycpO1xuaW1wb3J0ICogYXMgbXlXYWxrZXIgZnJvbSAnLi91dGlsL215V2Fsa2VyJ1xuXG4vKipcbiAqIENoZWNrIHdoZXRoZXIgZ2l2ZW4gcG9zIGlzIG9uIGEgdGhpcyBrZXl3b3JkXG4gKiBAcGFyYW0gYXN0IC0gQVNUIG9mIGEgcHJvZ3JhbVxuICogQHBhcmFtIHBvcyAtIGluZGV4IHBvc2l0aW9uXG4gKiBAcmV0dXJuIHsqfSAtIGZ1bmN0aW9uIG5vZGUgb3IgbnVsbFxuICovXG5leHBvcnQgZnVuY3Rpb24gb25UaGlzS2V5d29yZChhc3QsIHBvcykge1xuICAgICd1c2Ugc3RyaWN0JztcblxuICAgIC8vIGZpbmQgZnVuY3Rpb24gbm9kZVxuICAgIC8vIHN0IGlzIHRoZSBlbmNsb3NpbmcgZnVuY3Rpb25cbiAgICBjb25zdCB3YWxrZXIgPSBteVdhbGtlci53cmFwV2Fsa2VyKHdhbGsuYmFzZSxcbiAgICAgICAgLy8gcHJlXG4gICAgICAgIChub2RlLCBzdCkgPT4ge1xuICAgICAgICAgICAgaWYgKG5vZGUuc3RhcnQgPiBwb3MgfHwgbm9kZS5lbmQgPCBwb3MpIHtcbiAgICAgICAgICAgICAgICByZXR1cm4gZmFsc2U7XG4gICAgICAgICAgICB9XG5cbiAgICAgICAgICAgIGlmIChub2RlLnR5cGUgPT09ICdUaGlzRXhwcmVzc2lvbicpIHtcbiAgICAgICAgICAgICAgICB0aHJvdyBzdDtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIHJldHVybiB0cnVlO1xuICAgICAgICB9LFxuICAgICAgICAvLyBwb3N0XG4gICAgICAgIHVuZGVmaW5lZCxcbiAgICAgICAgLy8gc3RDaGFuZ2VcbiAgICAgICAgKG5vZGUsIHN0KSA9PiB7XG4gICAgICAgICAgICBpZiAobm9kZS50eXBlID09PSAnRnVuY3Rpb25EZWNsYXJhdGlvbidcbiAgICAgICAgICAgICAgICB8fCBub2RlLnR5cGUgPT09ICdGdW5jdGlvbkV4cHJlc3Npb24nKSB7XG4gICAgICAgICAgICAgICAgcmV0dXJuIG5vZGU7XG4gICAgICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgICAgICAgIHJldHVybiBzdDtcbiAgICAgICAgICAgIH1cbiAgICAgICAgfSk7XG5cbiAgICB0cnkge1xuICAgICAgICB3YWxrLnJlY3Vyc2l2ZShhc3QsIHVuZGVmaW5lZCwgd2Fsa2VyKTtcbiAgICB9IGNhdGNoIChlKSB7XG4gICAgICAgIGlmIChlICYmIGUudHlwZSAmJlxuICAgICAgICAgICAgKGUudHlwZSA9PT0gJ0Z1bmN0aW9uRXhwcmVzc2lvbidcbiAgICAgICAgICAgIHx8IGUudHlwZSA9PT0gJ0Z1bmN0aW9uRGVjbGFyYXRpb24nKSkge1xuICAgICAgICAgICAgcmV0dXJuIGU7XG4gICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgICB0aHJvdyBlO1xuICAgICAgICB9XG4gICAgfVxuICAgIC8vIGlkZW50aWZpZXIgbm90IGZvdW5kXG4gICAgcmV0dXJuIG51bGw7XG59XG5cbi8qKlxuICogR2l2ZW4gYSBmdW5jdGlvbiBub2RlLCBmaW5kIGl0cyB0aGlzIG5vZGVzXG4gKlxuICogQHBhcmFtIGZOb2RlIC0gQVNUIG5vZGUgb2YgYSBmdW5jdGlvbiwgcG9zc2libHkgd2l0aCBubyBhbm5vdGF0aW9uXG4gKiBAcmV0dXJuIHsqfSAtIGFycmF5IG9mIEFTVCBub2Rlc1xuICovXG5mdW5jdGlvbiBfZ2V0VGhpc05vZGVzKGZOb2RlKSB7XG4gICAgJ3VzZSBzdHJpY3QnO1xuICAgIGNvbnN0IHJldHMgPSBbXTtcbiAgICBpZiAoZk5vZGUudHlwZSAhPT0gJ0Z1bmN0aW9uRXhwcmVzc2lvbidcbiAgICAgICAgJiYgZk5vZGUudHlwZSAhPT0gJ0Z1bmN0aW9uRGVjbGFyYXRpb24nKSB7XG4gICAgICAgIHRocm93IEVycm9yKCdmTm9kZSBzaG91bGQgYmUgYSBmdW5jdGlvbiBub2RlJyk7XG4gICAgfVxuXG4gICAgY29uc3Qgd2Fsa2VyID0gd2Fsay5tYWtlKHtcbiAgICAgICAgVGhpc0V4cHJlc3Npb246IChub2RlKSA9PiB7XG4gICAgICAgICAgICByZXR1cm4gcmV0cy5wdXNoKG5vZGUpO1xuICAgICAgICB9LFxuICAgICAgICBGdW5jdGlvbkRlY2xhcmF0aW9uOiAoKSA9PiB7XG4gICAgICAgICAgICAvLyBub3QgdmlzaXQgZnVuY3Rpb24gZGVjbGFyYXRpb25cbiAgICAgICAgfSxcbiAgICAgICAgRnVuY3Rpb25FeHByZXNzaW9uOiAoKSA9PiB7XG4gICAgICAgICAgICAvLyBub3QgdmlzaXQgZnVuY3Rpb24gZXhwcmVzc2lvblxuICAgICAgICB9XG4gICAgfSwgd2Fsay5iYXNlKTtcblxuICAgIHdhbGsucmVjdXJzaXZlKGZOb2RlLmJvZHksIHVuZGVmaW5lZCwgd2Fsa2VyKTtcblxuICAgIHJldHVybiByZXRzO1xufVxuXG4vKipcbiAqIEZpbmQgdGhpcyBub2RlcyBpZiB0aGUgcG9zIGlzIG9uIGEgdGhpcyBrZXl3b3JkXG4gKlxuICogQHBhcmFtIGFzdCAtIEFTVCBub2RlIG9mIGEgcHJvZ3JhbSwgcG9zc2libHkgd2l0aCBubyBhbm5vdGF0aW9uXG4gKiBAcGFyYW0gcG9zIC0gY3Vyc29yIHBvc2l0aW9uXG4gKiBAcGFyYW0gaW5jbHVkZUZ1bmN0aW9uS2V5d29yZCAtIHdoZXRoZXIgdG8gaW5jbHVkZSBmdW5jdGlvbiBrZXl3b3JkIHJhbmdlXG4gKiBAcmV0dXJuIHtBcnJheX0gLSBhcnJheSBvZiBBU1Qgbm9kZXMgb2YgcmV0dXJuIHN0YXRlbWVudHNcbiAqL1xuZXhwb3J0IGZ1bmN0aW9uIGZpbmRUaGlzRXhwcmVzc2lvbnMoYXN0LCBwb3MsIGluY2x1ZGVGdW5jdGlvbktleXdvcmQpIHtcbiAgICAndXNlIHN0cmljdCc7XG5cbiAgICBjb25zdCBmTm9kZSA9IG9uVGhpc0tleXdvcmQoYXN0LCBwb3MpO1xuICAgIGlmICghZk5vZGUpIHtcbiAgICAgICAgLy8gcG9zIGlzIG5vdCBvbiB0aGlzIGtleXdvcmRcbiAgICAgICAgcmV0dXJuIG51bGw7XG4gICAgfVxuXG4gICAgY29uc3QgcmV0cyA9IF9nZXRUaGlzTm9kZXMoZk5vZGUpO1xuICAgIGlmIChpbmNsdWRlRnVuY3Rpb25LZXl3b3JkKSB7XG4gICAgICAgIHJldHMucHVzaCh7c3RhcnQ6IGZOb2RlLnN0YXJ0LCBlbmQ6IGZOb2RlLnN0YXJ0ICsgOH0pO1xuICAgIH1cbiAgICByZXR1cm4gcmV0cztcbn1cblxuIiwiLyoqXG4gKiBAZmlsZSBEZWZpbmVzIHNpbXBsZSB3YWxrZXJzIGZvciBhbmFseXNpc1xuICogQGF1dGhvciBzZXdvbjMyNi5raW1Ac2Ftc3VuZy5jb21cbiAqL1xuXG5jb25zdCB3YWxrID0gcmVxdWlyZSgnYWNvcm4vZGlzdC93YWxrJyk7XG5cbi8qKlxuICogUmV0dXJucyBhIHdhbGtlciB0aGF0IGRvZXMgbm90aGluZyBmb3IgZWFjaCBub2RlLlxuICogVXNlIGFzIGEgYmFzZSB3YWxrZXIgd2hlbiB5b3UgbmVlZCB0byB3YWxrIG9uIG9ubHkgc29tZSB0eXBlcyBvZiBub2Rlcy5cbiAqIEByZXR1cm4ge09iamVjdH1cbiAqL1xuZnVuY3Rpb24gbWFrZU5vb3BXYWxrZXIoKSB7XG4gICAgY29uc3Qgd2Fsa2VyID0gT2JqZWN0LmNyZWF0ZShudWxsKTtcbiAgICBjb25zdCBub29wRnVuYyA9ICgpID0+IHt9O1xuICAgIGZvciAobGV0IG5hbWUgaW4gT2JqZWN0LmdldE93blByb3BlcnR5TmFtZXMod2Fsay5iYXNlKSkge1xuICAgICAgICB3YWxrZXJbbmFtZV0gPSBub29wRnVuYztcbiAgICB9XG4gICAgcmV0dXJuIHdhbGtlcjtcbn1cblxuLyoqXG4gKiBhIHdhbGtlciB0aGF0IGRvZXMgbm90aGluZyBmb3IgZWFjaCBub2RlXG4gKi9cbmV4cG9ydCBjb25zdCBub29wV2Fsa2VyID0gbWFrZU5vb3BXYWxrZXIoKTtcblxuLyoqXG4gKiBDaGVjayB3aGV0aGVyIHRoZSBwYXR0ZXJuIHVzZXMgZGVmYXVsdHNcbiAqIEBwYXJhbSBwdG5Ob2RlIC0gYSBwYXR0ZXJuIG5vZGVcbiAqIEByZXR1cm4ge2Jvb2xlYW59XG4gKi9cbmV4cG9ydCBmdW5jdGlvbiBwYXR0ZXJuSGFzRGVmYXVsdHMocHRuTm9kZSkge1xuICAgIGNvbnN0IGFzc2lnbm1lbnRQYXR0ZXJuRmluZGVyID0gd2Fsay5tYWtlKG5vb3BXYWxrZXIsIHtcbiAgICAgICAgQXNzaWdubWVudFBhdHRlcm46IChub2RlLCBzdCwgYykgPT4ge1xuICAgICAgICAgICAgdGhyb3cgbmV3IEZvdW5kKCk7XG4gICAgICAgIH0sXG4gICAgICAgIE9iamVjdFBhdHRlcm46IHdhbGsuYmFzZS5PYmplY3RQYXR0ZXJuLFxuICAgICAgICBBcnJheVBhdHRlcm46IHdhbGsuYmFzZS5BcnJheUV4cHJlc3Npb24sXG4gICAgICAgIFJlc3RFbGVtZW50OiB3YWxrLmJhc2UuUmVzdEVsZW1lbnRcbiAgICB9KTtcblxuICAgIHRyeSB7XG4gICAgICAgIHdhbGsucmVjdXJzaXZlKHB0bk5vZGUsIHVuZGVmaW5lZCwgYXNzaWdubWVudFBhdHRlcm5GaW5kZXIpO1xuICAgIH0gY2F0Y2ggKGUpIHtcbiAgICAgICAgaWYgKGUgaW5zdGFuY2VvZiBGb3VuZCkge1xuICAgICAgICAgICAgcmV0dXJuIHRydWU7XG4gICAgICAgIH1cbiAgICB9XG4gICAgcmV0dXJuIGZhbHNlO1xufVxuXG4vKipcbiAqIGEgd2Fsa2VyIHRoYXQgdmlzaXRzIGVhY2ggaWQgZXZlbiB0aG91Z2ggaXQgaXMgdmFyIGRlY2xhcmF0aW9uXG4gKiB0aGUgcGFyYW1ldGVyIHZiIGRlbm90ZSB2YXJCbG9ja1xuICovXG5leHBvcnQgY29uc3QgdmFyV2Fsa2VyID0gd2Fsay5tYWtlKHtcbiAgICBGdW5jdGlvbjogKG5vZGUsIHZiLCBjKSA9PiB7XG4gICAgICAgIGlmIChub2RlLmlkKSBjKG5vZGUuaWQsIHZiLCAnUGF0dGVybicpO1xuICAgICAgICBjb25zdCBwYXJhbVZiID0gbm9kZVsnQGJsb2NrJ10gfHwgbm9kZS5ib2R5WydAYmxvY2snXTtcbiAgICAgICAgZm9yIChsZXQgaSA9IDA7IGkgPCBub2RlLnBhcmFtcy5sZW5ndGg7IGkrKykge1xuICAgICAgICAgICAgYyhub2RlLnBhcmFtc1tpXSwgcGFyYW1WYiwgJ1BhdHRlcm4nKTtcbiAgICAgICAgfVxuICAgICAgICBjb25zdCBpbm5lclZiID0gbm9kZS5ib2R5WydAYmxvY2snXTtcbiAgICAgICAgYyhub2RlLmJvZHksIGlubmVyVmIsIG5vZGUuZXhwcmVzc2lvbiA/ICdTY29wZUV4cHJlc3Npb24nIDogJ1Njb3BlQm9keScpO1xuICAgIH0sXG4gICAgRm9yU3RhdGVtZW50OiAobm9kZSwgdmIsIGMpID0+IHtcbiAgICAgICAgY29uc3QgaW5uZXJWYiA9IG5vZGVbJ0BibG9jayddIHx8IHZiO1xuICAgICAgICAvLyBVc2UgRm9yU3RhdGVtZW50IG9mIGJhc2Ugd2Fsa2VyXG4gICAgICAgIHdhbGsuYmFzZS5Gb3JTdGF0ZW1lbnQobm9kZSwgaW5uZXJWYiwgYyk7XG4gICAgfSxcbiAgICBCbG9ja1N0YXRlbWVudDogKG5vZGUsIHZiLCBjKSA9PiB7XG4gICAgICAgIGNvbnN0IGlubmVyVmIgPSBub2RlWydAYmxvY2snXSB8fCB2YjtcbiAgICAgICAgLy8gVXNlIEJsb2NrU3RhdGVtZW50IG9mIGJhc2Ugd2Fsa2VyXG4gICAgICAgIHdhbGsuYmFzZS5CbG9ja1N0YXRlbWVudChub2RlLCBpbm5lclZiLCBjKTtcbiAgICB9LFxuICAgIFRyeVN0YXRlbWVudDogKG5vZGUsIHZiLCBjKSA9PiB7XG4gICAgICAgIGMobm9kZS5ibG9jaywgdmIpO1xuICAgICAgICBpZiAobm9kZS5oYW5kbGVyKSB7XG4gICAgICAgICAgICAvLyBEbyBub3QgdmlzaXQgcGFyYW1ldGVyIHdpdGggY3VycmVudCB2YlxuICAgICAgICAgICAgLy8gdGhlIHBhcmFtZXRlciB3aWxsIGJlIHZpc2l0ZWQgaW4gQ2F0Y2hDbGF1c2Ugd2l0aCBjaGFuZ2VkIHZiXG4gICAgICAgICAgICBjKG5vZGUuaGFuZGxlciwgdmIpO1xuICAgICAgICB9XG4gICAgICAgIGlmIChub2RlLmZpbmFsaXplcikge1xuICAgICAgICAgICAgYyhub2RlLmZpbmFsaXplciwgdmIpO1xuICAgICAgICB9XG4gICAgfSxcbiAgICBDYXRjaENsYXVzZTogKG5vZGUsIHZiLCBjKSA9PiB7XG4gICAgICAgIGNvbnN0IGNhdGNoVmIgPSBub2RlLmJvZHlbJ0BibG9jayddO1xuICAgICAgICAvLyBOZWVkIHRvIGhhbmRsZSB0aGUgcGFyYW1ldGVyIGluIGNoYW5nZWQgYmxvY2tcbiAgICAgICAgYyhub2RlLnBhcmFtLCBjYXRjaFZiKTtcbiAgICAgICAgYyhub2RlLmJvZHksIGNhdGNoVmIpO1xuICAgIH0sXG4gICAgVmFyaWFibGVQYXR0ZXJuOiAobm9kZSwgdmIsIGMpID0+IHtcbiAgICAgICAgLy8gTm90ZSB0aGF0IHdhbGsuYmFzZS5JZGVudGlmaWVyIGlzICdpZ25vcmUuJ1xuICAgICAgICAvLyB2YXJXYWxrZXIgc2hvdWxkIHZpc2l0IHZhcmlhYmxlcyBpbiBMSFMuXG4gICAgICAgIGMobm9kZSwgdmIsICdJZGVudGlmaWVyJyk7XG4gICAgfVxufSk7XG5cbi8qKlxuICogV3JhcCBhIHdhbGtlciB3aXRoIHByZS0gYW5kIHBvc3QtIGFjdGlvbnNcbiAqXG4gKiBAcGFyYW0gd2Fsa2VyIC0gYmFzZSB3YWxrZXJcbiAqIEBwYXJhbSBwcmVOb2RlIC0gQXBwbHkgYmVmb3JlIHZpc2l0aW5nIHRoZSBjdXJyZW50IG5vZGUuXG4gKiBJZiByZXR1cm5zIGZhbHNlLCBkbyBub3QgdmlzaXQgdGhlIG5vZGUuXG4gKiBAcGFyYW0gcG9zdE5vZGUgLSBBcHBseSBhZnRlciB2aXNpdGluZyB0aGUgY3VycmVudCBub2RlLlxuICogSWYgZ2l2ZW4sIHJldHVybiB2YWx1ZXMgYXJlIG92ZXJyaWRkZW4uXG4gKiBAcGFyYW0gc3RDaGFuZ2UgLSBzdGF0ZSBjaGFuZ2UgZnVuY3Rpb25cbiAqIEByZXR1cm4geyp9IC0gYSBuZXcgd2Fsa2VyXG4gKi9cbmV4cG9ydCBmdW5jdGlvbiB3cmFwV2Fsa2VyKHdhbGtlciwgcHJlTm9kZSwgcG9zdE5vZGUsIHN0Q2hhbmdlKSB7XG4gICAgJ3VzZSBzdHJpY3QnO1xuICAgIGNvbnN0IHJldFdhbGtlciA9IHt9O1xuICAgIC8vIHdyYXBwaW5nIGVhY2ggZnVuY3Rpb24gcHJlTm9kZSBhbmQgcG9zdE5vZGVcbiAgICBmb3IgKGxldCBub2RlVHlwZSBpbiB3YWxrZXIpIHtcbiAgICAgICAgaWYgKCF3YWxrZXIuaGFzT3duUHJvcGVydHkobm9kZVR5cGUpKSB7XG4gICAgICAgICAgICBjb250aW51ZTtcbiAgICAgICAgfVxuICAgICAgICByZXRXYWxrZXJbbm9kZVR5cGVdID0gKG5vZGUsIHN0LCBjKSA9PiB7XG4gICAgICAgICAgICBsZXQgcmV0O1xuICAgICAgICAgICAgbGV0IG5ld1N0ID0gc3Q7XG4gICAgICAgICAgICBpZiAoc3RDaGFuZ2UpIHtcbiAgICAgICAgICAgICAgICBuZXdTdCA9IHN0Q2hhbmdlKG5vZGUsIHN0LCBub2RlVHlwZSk7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBpZiAoIXByZU5vZGUgfHwgcHJlTm9kZShub2RlLCBuZXdTdCwgbm9kZVR5cGUpKSB7XG4gICAgICAgICAgICAgICAgcmV0ID0gd2Fsa2VyW25vZGVUeXBlXShub2RlLCBuZXdTdCwgYyk7XG4gICAgICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgICAgICAgIHJldHVybjtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGlmIChwb3N0Tm9kZSkge1xuICAgICAgICAgICAgICAgIHJldCA9IHBvc3ROb2RlKG5vZGUsIG5ld1N0LCBub2RlVHlwZSk7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICByZXR1cm4gcmV0O1xuICAgICAgICB9XG4gICAgfVxuICAgIHJldHVybiByZXRXYWxrZXI7XG59XG5cbi8qKlxuICogQSB1dGlsaXR5IGNsYXNzIGZvciBzZWFyY2hpbmcgQVNUcy5cbiAqIFdlIHVzZSBpbmZvIHRvIHJlY29yZCBhbnkgdXNlZnVsIGluZm9ybWF0aW9uLlxuICovXG5leHBvcnQgY2xhc3MgRm91bmQge1xuICAgIC8qKlxuICAgICAqIEBwYXJhbSBpbmZvIC0gYW55IGluZm9ybWF0aW9uIHRvIHJlbWVtYmVyXG4gICAgICovXG4gICAgY29uc3RydWN0b3IoaW5mbykge1xuICAgICAgICB0aGlzLmluZm8gPSBpbmZvO1xuICAgIH1cbn1cblxuLyoqXG4gKiBDaGVja3Mgd2hldGhlciBpdCBpcyBhIGR1bW15IElkIG5vZGUuXG4gKiBAcGFyYW0gbm9kZVxuICogQHJldHVybiB7Ym9vbGVhbn1cbiAqL1xuZXhwb3J0IGZ1bmN0aW9uIGlzRHVtbXlJZE5vZGUobm9kZSkge1xuICAgIGlmIChub2RlLnR5cGUgIT09ICdJZGVudGlmaWVyJykge1xuICAgICAgICB0aHJvdyBuZXcgRXJyb3IoJ1Nob3VsZCBiZSBhbiBJZGVudGlmaWVyIG5vZGUnKTtcbiAgICB9XG4gICAgcmV0dXJuIG5vZGUubmFtZSA9PT0gJ+KclicgJiYgbm9kZS5zdGFydCA+PSBub2RlLmVuZDtcbn1cblxuLyoqXG4gKiBGaW5kcyBhbiBpZGVudGlmaWVyIG5vZGUgYXQgYHBvc2AuXG4gKiBAcGFyYW0gYXN0XG4gKiBAcGFyYW0gcG9zXG4gKiBAcmV0dXJuIHsqfVxuICovXG5leHBvcnQgZnVuY3Rpb24gZmluZElkZW50aWZpZXJBdChhc3QsIHBvcykge1xuICAgICd1c2Ugc3RyaWN0JztcbiAgICByZXR1cm4gZmluZE5vZGVBdChhc3QsIHBvcyxcbiAgICAgICAgICAgIG5vZGUgPT4gbm9kZS50eXBlID09PSAnSWRlbnRpZmllcicgJiYgIWlzRHVtbXlJZE5vZGUobm9kZSlcbiAgICApO1xufVxuXG4vKipcbiAqIFJldHVybnMgYSBub2RlIGF0IGBwb3NgIGlmIGl0IGlzIG1lbWJlciBleHByIG9yIHZhcmlhYmxlLlxuICogQHBhcmFtIGFzdFxuICogQHBhcmFtIHBvc1xuICogQHJldHVybiB7Kn1cbiAqL1xuZXhwb3J0IGZ1bmN0aW9uIGZpbmRNZW1iZXJPclZhcmlhYmxlQXQoYXN0LCBwb3MpIHtcbiAgICAndXNlIHN0cmljdCc7XG4gICAgcmV0dXJuIGZpbmROb2RlQXQoYXN0LCBwb3MsXG4gICAgICAgICAgICBub2RlID0+IHtcbiAgICAgICAgICAgICAgICByZXR1cm4gKG5vZGUudHlwZSA9PT0gJ0lkZW50aWZpZXInICYmICFpc0R1bW15SWROb2RlKG5vZGUpKSB8fFxuICAgICAgICAgICAgICAgICAgICAobm9kZS50eXBlID09PSAnTWVtYmVyRXhwcmVzc2lvbicgJiZcbiAgICAgICAgICAgICAgICAgICAgKFxuICAgICAgICAgICAgICAgICAgICAgICAgKG5vZGUucHJvcGVydHkuc3RhcnQgPD0gcG9zICYmIHBvcyA8PSBub2RlLnByb3BlcnR5LmVuZCkgfHxcbiAgICAgICAgICAgICAgICAgICAgICAgIC8vIHdoZW4gcHJvcCBpcyDinJZcbiAgICAgICAgICAgICAgICAgICAgICAgIChub2RlLnByb3BlcnR5LmVuZCA8PSBwb3MgJiYgcG9zIDw9IG5vZGUucHJvcGVydHkuc3RhcnQpXG4gICAgICAgICAgICAgICAgICAgICkpO1xuICAgICAgICAgICAgfVxuICAgICk7XG59XG5cbi8qKlxuICogUmV0dXJucyBjb250ZXh0IGluZm9ybWF0aW9uIGZvciBjb21wbGV0aW9uLlxuICogQHBhcmFtIGFzdFxuICogQHBhcmFtIHBvc1xuICogQHJldHVybiB7Kn1cbiAqL1xuZXhwb3J0IGZ1bmN0aW9uIGZpbmRDb21wbGV0aW9uQ29udGV4dChhc3QsIHBvcykge1xuICAgICd1c2Ugc3RyaWN0JztcbiAgICAvLyBmaW5kIHRoZSBub2RlXG4gICAgY29uc3Qgd2Fsa2VyID0gd3JhcFdhbGtlcih2YXJXYWxrZXIsXG4gICAgICAgIChub2RlLCB2YikgPT4ge1xuICAgICAgICAgICAgaWYgKG5vZGUuc3RhcnQgPiBwb3MgfHwgbm9kZS5lbmQgPCBwb3MpIHtcbiAgICAgICAgICAgICAgICByZXR1cm4gZmFsc2U7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICAvLyBhdCBpZGVudGlmaWVyP1xuICAgICAgICAgICAgaWYgKG5vZGUudHlwZSA9PT0gJ0lkZW50aWZpZXInKSB7XG4gICAgICAgICAgICAgICAgdGhyb3cgbmV3IEZvdW5kKHt0eXBlOiAnSWRlbnRpZmllcicsIG5vZGU6IG5vZGUsIHZiOiB2Yn0pO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgLy8gYXQgbWVtYmVyIGV4cHJlc3Npb24/XG4gICAgICAgICAgICBpZiAobm9kZS50eXBlID09PSAnTWVtYmVyRXhwcmVzc2lvbicgJiZcbiAgICAgICAgICAgICAgICAoXG4gICAgICAgICAgICAgICAgICAgIChub2RlLnByb3BlcnR5LnN0YXJ0IDw9IHBvcyAmJiBwb3MgPD0gbm9kZS5wcm9wZXJ0eS5lbmQpIHx8XG4gICAgICAgICAgICAgICAgICAgICAgICAvLyB3aGVuIHByb3AgaXMg4pyWXG4gICAgICAgICAgICAgICAgICAgIChub2RlLnByb3BlcnR5LmVuZCA8PSBwb3MgJiYgcG9zIDw9IG5vZGUucHJvcGVydHkuc3RhcnQpXG4gICAgICAgICAgICAgICAgKVxuICAgICAgICAgICAgKSB7XG4gICAgICAgICAgICAgICAgLy8gYXQgdXN1YWwgcHJvcD8gKGFmdGVyIGRvdClcbiAgICAgICAgICAgICAgICBpZiAoIW5vZGUuY29tcHV0ZWQpIHtcbiAgICAgICAgICAgICAgICAgICAgdGhyb3cgbmV3IEZvdW5kKHt0eXBlOiAndXN1YWxQcm9wJywgbm9kZTogbm9kZSwgdmI6IHZifSk7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIC8vIGF0IG9ialsnJ10gcGF0dGVybj9cbiAgICAgICAgICAgICAgICBpZiAobm9kZS5jb21wdXRlZCAmJlxuICAgICAgICAgICAgICAgICAgICB0eXBlb2Ygbm9kZS5wcm9wZXJ0eS52YWx1ZSA9PT0gJ3N0cmluZycpIHtcbiAgICAgICAgICAgICAgICAgICAgdGhyb3cgbmV3IEZvdW5kKHt0eXBlOiAnc3RyaW5nUHJvcCcsIG5vZGU6IG5vZGUsIHZiOiB2Yn0pO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIHJldHVybiB0cnVlO1xuICAgICAgICB9LFxuICAgICAgICAobm9kZSwgdmIpID0+IHtcbiAgICAgICAgICAgIC8vIG5vIElkZW50aWZpZXIgb3IgTWVtYmVyIEV4cHJlc3Npb24gd2FzIGZvdW5kXG4gICAgICAgICAgICB0aHJvdyBuZXcgRm91bmQoe3R5cGU6ICdJZGVudGlmaWVyJywgbm9kZTogbnVsbCwgdmI6IHZifSk7XG4gICAgICAgIH0pO1xuXG4gICAgdHJ5IHtcbiAgICAgICAgd2Fsay5yZWN1cnNpdmUoYXN0LCBhc3RbJ0BibG9jayddLCB3YWxrZXIpO1xuICAgIH0gY2F0Y2ggKGUpIHtcbiAgICAgICAgaWYgKGUgaW5zdGFuY2VvZiBGb3VuZCkge1xuICAgICAgICAgICAgcmV0dXJuIGUuaW5mbztcbiAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICAgIHRocm93IGU7XG4gICAgICAgIH1cbiAgICB9XG59XG5cblxuLyoqXG4gKiBGaW5kIGEgbm9kZSBhdCBwb3MuXG4gKiBJZiBmb3VuZCwgaXQgYWxzbyByZXR1cm5zIGl0cyB2YXJCbG9jay5cbiAqIElmIG5vdCBmb3VuZCwgcmV0dXJuIG51bGwuXG4gKiBAcGFyYW0gYXN0IC0gQVNUIG5vZGVcbiAqIEBwYXJhbSBwb3MgLSBpbmRleCBwb3NpdGlvblxuICogQHBhcmFtIG5vZGVUZXN0IC0gQ2hlY2sgd2hldGhlciB0aGUgbm9kZSBpcyB3aGF0IHdlIGFyZSBsb29raW5nIGZvclxuICogQHJldHVybiB7Kn1cbiAqL1xuZnVuY3Rpb24gZmluZE5vZGVBdChhc3QsIHBvcywgbm9kZVRlc3QpIHtcbiAgICAndXNlIHN0cmljdCc7XG4gICAgLy8gZmluZCB0aGUgbm9kZVxuICAgIGNvbnN0IHdhbGtlciA9IHdyYXBXYWxrZXIodmFyV2Fsa2VyLFxuICAgICAgICAobm9kZSwgdmIpID0+IHtcbiAgICAgICAgICAgIGlmIChub2RlLnN0YXJ0ID4gcG9zIHx8IG5vZGUuZW5kIDwgcG9zKSB7XG4gICAgICAgICAgICAgICAgcmV0dXJuIGZhbHNlO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgaWYgKG5vZGVUZXN0KG5vZGUpKSB7XG4gICAgICAgICAgICAgICAgdGhyb3cgbmV3IEZvdW5kKHtub2RlOiBub2RlLCB2YjogdmJ9KTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIHJldHVybiB0cnVlO1xuICAgICAgICB9KTtcblxuICAgIHRyeSB7XG4gICAgICAgIHdhbGsucmVjdXJzaXZlKGFzdCwgYXN0WydAYmxvY2snXSwgd2Fsa2VyKTtcbiAgICB9IGNhdGNoIChlKSB7XG4gICAgICAgIGlmIChlIGluc3RhbmNlb2YgRm91bmQpIHtcbiAgICAgICAgICAgIHJldHVybiBlLmluZm87XG4gICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgICB0aHJvdyBlO1xuICAgICAgICB9XG4gICAgfVxuICAgIC8vIGlkZW50aWZpZXIgbm90IGZvdW5kXG4gICAgcmV0dXJuIG51bGw7XG59XG5cbi8qKlxuICogRmluZCB0aGUgc21hbGxlc3Qgbm9kZSB0aGF0IGNvbnRhaW5zIHRoZSByYW5nZSBmcm9tIHN0YXJ0IHRvIGVuZC5cbiAqIE5vdGUgdGhhdCB3ZSBjYW4gZmluZCB0aGUgbm9kZSBhdCB0aGUgcG9zdE5vZGUgaW5zdGVhZCBvZiBwcmVOb2RlLlxuICogQHBhcmFtIGFzdFxuICogQHBhcmFtIHN0YXJ0XG4gKiBAcGFyYW0gZW5kXG4gKiBAcmV0dXJuIHsqfVxuICovXG5leHBvcnQgZnVuY3Rpb24gZmluZFN1cnJvdW5kaW5nTm9kZShhc3QsIHN0YXJ0LCBlbmQpIHtcbiAgICAndXNlIHN0cmljdCc7XG5cbiAgICBjb25zdCB3YWxrZXIgPSB3cmFwV2Fsa2VyKHZhcldhbGtlcixcbiAgICAgICAgbm9kZSA9PiBub2RlLnN0YXJ0IDw9IHN0YXJ0ICYmIGVuZCA8PSBub2RlLmVuZCxcbiAgICAgICAgbm9kZSA9PiB7IHRocm93IG5ldyBGb3VuZChub2RlKTsgfVxuICAgICk7XG5cbiAgICB0cnkge1xuICAgICAgICB3YWxrLnJlY3Vyc2l2ZShhc3QsIHVuZGVmaW5lZCwgd2Fsa2VyKTtcbiAgICB9IGNhdGNoIChlKSB7XG4gICAgICAgIGlmIChlIGluc3RhbmNlb2YgRm91bmQpIHtcbiAgICAgICAgICAgIHJldHVybiBlLmluZm87XG4gICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgICB0aHJvdyBlO1xuICAgICAgICB9XG4gICAgfVxuICAgIC8vIG5vZGUgbm90IGZvdW5kXG4gICAgcmV0dXJuIG51bGw7XG59XG5cbi8qKlxuICogTWFrZXMgYSByZWN1cnNpdmUgdmlzaXRvci5cbiAqIFdpdGggdGhpcywgd2UgY2FuIHVzZSB0aGUgcmV0dXJuIHZhbHVlIGZyb20gZWFjaCBub2RlLlxuICogQHBhcmFtIG5vZGVcbiAqIEBwYXJhbSB7U3RhdHVzfSBzdGF0ZVxuICogQHBhcmFtIHZpc2l0b3JcbiAqIEByZXR1cm4geyp9XG4gKi9cbmV4cG9ydCBmdW5jdGlvbiByZWN1cnNpdmVXaXRoUmV0dXJuKG5vZGUsIHN0YXRlLCB2aXNpdG9yKSB7XG4gICAgZnVuY3Rpb24gYyhub2RlLCBzdCwgb3ZlcnJpZGUpIHtcbiAgICAgICAgcmV0dXJuIHZpc2l0b3Jbb3ZlcnJpZGUgfHwgbm9kZS50eXBlXShub2RlLCBzdCwgYyk7XG4gICAgfVxuICAgIHJldHVybiBjKG5vZGUsIHN0YXRlKTtcbn1cbiIsIi8qKlxuICogQGZpbGUgSW1wbGVtZW50cyBWYXJCbG9jayBhbmQgU2NvcGVcbiAqIEBhdXRob3Igc2V3b24zMjYua2ltQHNhbXN1bmcuY29tXG4gKi9cblxuJ3VzZSBzdHJpY3QnO1xuXG5pbXBvcnQgKiBhcyB0eXBlcyBmcm9tICcuL2RvbWFpbnMvdHlwZXMnXG5pbXBvcnQgKiBhcyBteVdhbGtlciBmcm9tICcuL3V0aWwvbXlXYWxrZXInXG5jb25zdCB3YWxrID0gcmVxdWlyZSgnYWNvcm4vZGlzdC93YWxrJyk7XG5cbmV4cG9ydCBjbGFzcyBWYXJCbG9jayB7XG4gICAgLyoqXG4gICAgICogQ29uc3RydWN0cyBhIFZhckJsb2NrLlxuICAgICAqIEBwYXJhbSB7VmFyQmxvY2t9IHBhcmVuXG4gICAgICogQHBhcmFtIG9yaWdpbk5vZGVcbiAgICAgKiBAcGFyYW0gYlR5cGVcbiAgICAgKiBAcGFyYW0ge2Jvb2xlYW59IGlzU3RyaWN0XG4gICAgICovXG4gICAgY29uc3RydWN0b3IocGFyZW4sIG9yaWdpbk5vZGUsIGJUeXBlLCBpc1N0cmljdCkge1xuICAgICAgICB0aGlzLnBhcmVuID0gcGFyZW47XG4gICAgICAgIHRoaXMub3JpZ2luTm9kZSA9IG9yaWdpbk5vZGU7XG4gICAgICAgIHRoaXMuYmxvY2tUeXBlID0gYlR5cGU7XG4gICAgICAgIHRoaXMuaXNTdHJpY3QgPSBpc1N0cmljdDtcblxuICAgICAgICB0aGlzLm9yaWdpbkxhYmVsID0gb3JpZ2luTm9kZVsnQGxhYmVsJ107XG4gICAgICAgIHRoaXMucGFyYW1WYXJOYW1lcyA9IFtdO1xuICAgICAgICB0aGlzLmxvY2FsVmFyTmFtZXMgPSBbXTtcblxuICAgICAgICB0aGlzLnVzZWRWYXJpYWJsZXMgPSBbXTtcbiAgICAgICAgLy8gdGhpcy51c2VBcmd1bWVudHNPYmplY3RcbiAgICAgICAgdGhpcy5pbnN0YW5jZXMgPSBuZXcgTWFwKCk7XG4gICAgICAgIHRoaXMuc2NvcGVJbnN0YW5jZXMgPSBbXTtcbiAgICB9XG5cbiAgICAvKipcbiAgICAgKiBDaGVja3Mgd2hldGhlciBpdCBpcyBhIGdsb2JhbCBibG9jay5cbiAgICAgKiBAcmV0dXJuIHtib29sZWFufVxuICAgICAqL1xuICAgIGlzR2xvYmFsKCkge1xuICAgICAgICByZXR1cm4gdGhpcy5ibG9ja1R5cGUgPT09IFZhckJsb2NrLmJsb2NrVHlwZXMuZ2xvYmFsQmxvY2s7XG4gICAgfVxuXG4gICAgLyoqXG4gICAgICogQ2hlY2tzIHdoZXRoZXIgaXQgaXMgYW4gRVM1IGZ1bmN0aW9uIGJsb2NrLlxuICAgICAqIEByZXR1cm4ge2Jvb2xlYW59XG4gICAgICovXG4gICAgaXNPbGRGdW5jdGlvbkJsb2NrKCkge1xuICAgICAgICByZXR1cm4gdGhpcy5ibG9ja1R5cGUgPT09IFZhckJsb2NrLmJsb2NrVHlwZXMub2xkRnVuY3Rpb25CbG9jaztcbiAgICB9XG5cbiAgICAvKipcbiAgICAgKiBDaGVja3Mgd2hldGhlciBpdCBpcyBhIGJsb2NrIG9mIGFuIGFycm93IGZ1bmN0aW9uLlxuICAgICAqIEByZXR1cm4ge2Jvb2xlYW59XG4gICAgICovXG4gICAgaXNBcnJvd0Z1bmN0aW9uQmxvY2soKSB7XG4gICAgICAgIHJldHVybiB0aGlzLmJsb2NrVHlwZSA9PT0gVmFyQmxvY2suYmxvY2tUeXBlcy5hcnJvd0Z1bmN0aW9uQmxvY2s7XG4gICAgfVxuXG4gICAgLyoqXG4gICAgICogQ2hlY2tzIHdoZXRoZXIgaXQgaXMgYSBjYXRjaCBibG9jay5cbiAgICAgKiBAcmV0dXJuIHtib29sZWFufVxuICAgICAqL1xuICAgIGlzQ2F0Y2hCbG9jaygpIHtcbiAgICAgICAgcmV0dXJuIHRoaXMuYmxvY2tUeXBlID09PSBWYXJCbG9jay5ibG9ja1R5cGVzLmNhdGNoQmxvY2s7XG4gICAgfVxuXG4gICAgLyoqIENoZWNrcyB3aGV0aGVyIGlzIGlzIGEgbm9ybWFsIGNvZGUgYmxvY2suXG4gICAgICogQHJldHVybiB7Ym9vbGVhbn1cbiAgICAgKi9cbiAgICBpc05vcm1hbEJsb2NrKCkge1xuICAgICAgICByZXR1cm4gdGhpcy5ibG9ja1R5cGUgPT09IFZhckJsb2NrLmJsb2NrVHlwZXMubm9ybWFsQmxvY2s7XG4gICAgfVxuXG4gICAgLyoqXG4gICAgICogQ2hlY2tzIHdoZXRoZXIgaXQgaXMgYSBwYXJhbWV0ZXIgYmxvY2suXG4gICAgICogQHJldHVybiB7Ym9vbGVhbn1cbiAgICAgKi9cbiAgICBpc1BhcmFtZXRlckJsb2NrKCkge1xuICAgICAgICByZXR1cm4gdGhpcy5ibG9ja1R5cGUgPT09IFZhckJsb2NrLmJsb2NrVHlwZXMucGFyYW1ldGVyQmxvY2s7XG4gICAgfVxuXG4gICAgLyoqXG4gICAgICogUmV0dXJucyB0aGUgbmFtZXMgb2YgbG9jYWwgdmFyaWFibGVzLlxuICAgICAqIEByZXR1cm4ge0FycmF5LjxzdHJpbmc+fVxuICAgICAqL1xuICAgIGdldExvY2FsVmFyTmFtZXMoKSB7XG4gICAgICAgIHJldHVybiB0aGlzLmxvY2FsVmFyTmFtZXM7XG4gICAgfVxuXG4gICAgLyoqXG4gICAgICogUmV0dXJucyB0aGUgbmFtZXMgb2YgcGFyYW1ldGVycy5cbiAgICAgKiBAcmV0dXJuIHtBcnJheS48c3RyaW5nPn1cbiAgICAgKi9cbiAgICBnZXRQYXJhbVZhck5hbWVzKCkge1xuICAgICAgICByZXR1cm4gdGhpcy5wYXJhbVZhck5hbWVzO1xuICAgIH1cblxuICAgIC8qKlxuICAgICAqIFJldHVybnMgdGhlIG5hbWVzIG9mIGl0cyBwYXJhbWV0ZXIgYW5kIGxvY2FsIHZhcmlhYmxlcy5cbiAgICAgKiBAcmV0dXJuIHtBcnJheS48c3RyaW5nPn1cbiAgICAgKi9cbiAgICBnZXRWYXJOYW1lcygpIHtcbiAgICAgICAgcmV0dXJuIHRoaXMuZ2V0TG9jYWxWYXJOYW1lcygpLmNvbmNhdCh0aGlzLmdldFBhcmFtVmFyTmFtZXMoKSk7XG4gICAgfVxuXG4gICAgLyoqXG4gICAgICogQ2hlY2tzIHdoZXRoZXIgaXQgaGFzIGEgbG9jYWwgdmFyaWFibGUgd2hvc2UgbmFtZSBpcyBgdmFyTmFtZWAuXG4gICAgICogQHBhcmFtIHtzdHJpbmd9IHZhck5hbWVcbiAgICAgKiBAcmV0dXJuIHtib29sZWFufVxuICAgICAqL1xuICAgIGhhc0xvY2FsVmFyKHZhck5hbWUpIHtcbiAgICAgICAgcmV0dXJuIHRoaXMubG9jYWxWYXJOYW1lcyAmJiB0aGlzLmxvY2FsVmFyTmFtZXMuaW5kZXhPZih2YXJOYW1lKSA+IC0xO1xuICAgIH1cblxuICAgIC8qKlxuICAgICAqIENoZWNrcyB3aGV0aGVyIGl0IGhhcyBhIHBhcmFtZXRlciB2YXJpYWxiZSB3aG9zZSBuYW1lIGlzIGB2YXJOYW1lYC5cbiAgICAgKiBAcGFyYW0ge3N0cmluZ30gdmFyTmFtZVxuICAgICAqIEByZXR1cm4ge2Jvb2xlYW59XG4gICAgICovXG4gICAgaGFzUGFyYW1WYXIodmFyTmFtZSkge1xuICAgICAgICByZXR1cm4gdGhpcy5wYXJhbVZhck5hbWVzLmluZGV4T2YodmFyTmFtZSkgPiAtMTtcbiAgICB9XG5cbiAgICAvKipcbiAgICAgKiBDaGVja3Mgd2hldGhlciB0aGUgYmxvY2sgaGFzIHZhcmlhYmxlIG5hbWVkIGFzIGB2YXJOYW1lYC5cbiAgICAgKiBAcGFyYW0ge3N0cmluZ30gdmFyTmFtZVxuICAgICAqIEByZXR1cm4ge2Jvb2xlYW59XG4gICAgICovXG4gICAgaGFzVmFyKHZhck5hbWUpIHtcbiAgICAgICAgcmV0dXJuIHRoaXMuaGFzUGFyYW1WYXIodmFyTmFtZSkgfHwgdGhpcy5oYXNMb2NhbFZhcih2YXJOYW1lKTtcbiAgICB9XG5cbiAgICAvKipcbiAgICAgKiBBZGQgYSBkZWNsYXJlZCB2YXJpYWJsZSB0byB0aGUgYmxvY2suXG4gICAgICogSXQgcmV0dXJucyBudWxsIGlmIGl0IGRvZXMgbm90IGFkZCB0aGUgdmFyaWFibGUuXG4gICAgICogQHBhcmFtIHtzdHJpbmd9IHZhck5hbWVcbiAgICAgKiBAcGFyYW0gZFR5cGUgLSBkZWNsYXJhdGlvbiB0eXBlXG4gICAgICogQHJldHVybiB7VmFyQmxvY2t8bnVsbH1cbiAgICAgKi9cbiAgICBhZGREZWNsYXJlZExvY2FsVmFyKHZhck5hbWUsIGRUeXBlKSB7XG4gICAgICAgIGxldCBjdXJyQmxvY2sgPSB0aGlzO1xuICAgICAgICBzd2l0Y2goZFR5cGUpIHtcbiAgICAgICAgICAgIGNhc2UgVmFyQmxvY2suZGVjbGFyYXRpb25UeXBlcy52YXJEZWNsYXJhdGlvbjpcbiAgICAgICAgICAgICAgICAvLyBHbyB1cCB1bnRpbCBmdW5jdGlvbiBvciBnbG9iYWxcbiAgICAgICAgICAgICAgICB3aGlsZSAoIWN1cnJCbG9jay5pc09sZEZ1bmN0aW9uQmxvY2soKVxuICAgICAgICAgICAgICAgICAgICAmJiAhY3VyckJsb2NrLmlzQXJyb3dGdW5jdGlvbkJsb2NrKClcbiAgICAgICAgICAgICAgICAgICAgJiYgIWN1cnJCbG9jay5pc1BhcmFtZXRlckJsb2NrKCkgIC8vIHRvIGFkZCAnYXJndW1lbnRzJ1xuICAgICAgICAgICAgICAgICAgICAmJiAhY3VyckJsb2NrLmlzR2xvYmFsKCkpIHtcbiAgICAgICAgICAgICAgICAgICAgY3VyckJsb2NrID0gY3VyckJsb2NrLnBhcmVuO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICBicmVhaztcbiAgICAgICAgICAgIGNhc2UgVmFyQmxvY2suZGVjbGFyYXRpb25UeXBlcy5mdW5jdGlvbkRlY2xhcmF0aW9uOlxuICAgICAgICAgICAgICAgIC8vIEdvIHVwIHVudGlsIGZ1bmN0aW9uIG9yIGdsb2JhbFxuICAgICAgICAgICAgICAgIC8vIG9yIGNhdGNoIGJsb2NrIGhhdmluZyB2YXJOYW1lIGFzIGl0cyBwYXJhbWV0ZXJcbiAgICAgICAgICAgICAgICB3aGlsZSAoY3VyckJsb2NrLmlzTm9ybWFsQmxvY2soKSAmJlxuICAgICAgICAgICAgICAgICAgICAgICAhKGN1cnJCbG9jay5pc0NhdGNoQmxvY2soKSAmJiBjdXJyQmxvY2suaGFzUGFyYW1WYXIodmFyTmFtZSkpKSB7XG4gICAgICAgICAgICAgICAgICAgIGN1cnJCbG9jayA9IGN1cnJCbG9jay5wYXJlbjtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgYnJlYWs7XG4gICAgICAgICAgICBjYXNlIFZhckJsb2NrLmRlY2xhcmF0aW9uVHlwZXMubGV0RGVjbGFyYXRpb246XG4gICAgICAgICAgICBjYXNlIFZhckJsb2NrLmRlY2xhcmF0aW9uVHlwZXMuY29uc3REZWNsYXJhdGlvbjpcbiAgICAgICAgICAgICAgICBicmVhaztcbiAgICAgICAgICAgIGNhc2UgVmFyQmxvY2suZGVjbGFyYXRpb25UeXBlcy5pbXBsaWNpdEdsb2JhbERlY2xhcmF0aW9uOlxuICAgICAgICAgICAgICAgIC8vIG5vdCBnbG9iYWwgb3Igc3RyaWN0ID0+IGRvIG5vdCBhZGQgdGhlIHZhcmlhYmxlXG4gICAgICAgICAgICAgICAgaWYgKCF0aGlzLmlzR2xvYmFsKCkgfHwgdGhpcy5pc1N0cmljdCkge1xuICAgICAgICAgICAgICAgICAgICByZXR1cm4gbnVsbDtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgYnJlYWs7XG4gICAgICAgIH1cblxuICAgICAgICAvLyBpZiBhbHJlYWR5IGFkZGVkLCBkbyBub3QgYWRkXG4gICAgICAgIGlmICghY3VyckJsb2NrLmhhc1Zhcih2YXJOYW1lKSkge1xuICAgICAgICAgICAgY3VyckJsb2NrLmxvY2FsVmFyTmFtZXMucHVzaCh2YXJOYW1lKTtcbiAgICAgICAgfVxuICAgICAgICAvLyByZXR1cm5zIHRoZSBibG9jayBvYmplY3QgdGhhdCBjb250YWlucyB0aGUgdmFyaWFibGVcbiAgICAgICAgcmV0dXJuIGN1cnJCbG9jaztcbiAgICB9XG5cbiAgICAvKipcbiAgICAgKiBBZGRzIGEgcGFyYW1ldGVyIHZhcmlhYmxlLlxuICAgICAqIEBwYXJhbSB7c3RyaW5nfSB2YXJOYW1lXG4gICAgICovXG4gICAgYWRkUGFyYW1WYXIodmFyTmFtZSkge1xuICAgICAgICB0aGlzLnBhcmFtVmFyTmFtZXMucHVzaCh2YXJOYW1lKTtcbiAgICB9XG5cbiAgICAvKipcbiAgICAgKiBSZXR1cm5zIHRoZSBWYXJCbG9jayB0aGF0IGNvbnRhaW5zIGB2YXJOYW1lYC5cbiAgICAgKiBJdCBjYW4gcmVjdXJzaXZlbHkgbG9vayBpbnRvIGBwYXJlbmAgVmFyQmxvY2tzLlxuICAgICAqIEBwYXJhbSB2YXJOYW1lXG4gICAgICogQHJldHVybiB7VmFyQmxvY2t9XG4gICAgICovXG4gICAgZmluZFZhckluQ2hhaW4odmFyTmFtZSkge1xuICAgICAgICBsZXQgY3VyckJsb2NrID0gdGhpcztcbiAgICAgICAgd2hpbGUgKGN1cnJCbG9jayAmJiAhY3VyckJsb2NrLmhhc1Zhcih2YXJOYW1lKSkge1xuICAgICAgICAgICAgaWYgKGN1cnJCbG9jay5pc0dsb2JhbCgpICYmICFjdXJyQmxvY2suaXNTdHJpY3QpIHtcbiAgICAgICAgICAgICAgICBicmVhaztcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGN1cnJCbG9jayA9IGN1cnJCbG9jay5wYXJlbjtcbiAgICAgICAgfVxuICAgICAgICAvLyBpZiBub3QgZm91bmRcbiAgICAgICAgLy8gMSkgZ2xvYmFsICd1c2Ugc3RyaWN0JyA9PiByZXR1cm5zIG51bGxcbiAgICAgICAgLy8gMikgb3RoZXJ3aXNlID0+IHJldHVybnMgdGhlIGdsb2JhbFxuICAgICAgICByZXR1cm4gY3VyckJsb2NrO1xuICAgIH1cblxuICAgIC8qKlxuICAgICAqIEdldCBhbGwgdGhlIHZhcmlhYmxlIG5hbWVzIGluIHRoZSBjaGFpbiBvZiBWYXJCbG9jay5cbiAgICAgKiBAcmV0dXJuIHtBcnJheS48c3RyaW5nPn1cbiAgICAgKi9cbiAgICBnZXRWYXJOYW1lc0luQ2hhaW4oKSB7XG4gICAgICAgIGxldCBjdXJyQmxvY2sgPSB0aGlzO1xuICAgICAgICBjb25zdCB2YXJOYW1lcyA9IFtdO1xuICAgICAgICB3aGlsZSAoY3VyckJsb2NrKSB7XG4gICAgICAgICAgICBjdXJyQmxvY2suZ2V0VmFyTmFtZXMoKS5mb3JFYWNoKGZ1bmN0aW9uIChuYW1lKSB7XG4gICAgICAgICAgICAgICAgaWYgKHZhck5hbWVzLmluZGV4T2YobmFtZSkgPT09IC0xKSB7XG4gICAgICAgICAgICAgICAgICAgIHZhck5hbWVzLnB1c2gobmFtZSk7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgfSk7XG4gICAgICAgICAgICBjdXJyQmxvY2sgPSBjdXJyQmxvY2sucGFyZW47XG4gICAgICAgIH1cbiAgICAgICAgcmV0dXJuIHZhck5hbWVzO1xuICAgIH1cblxuICAgIC8qKlxuICAgICAqIEFkZCBgdmFyTmFtZWAgYXMgb25lIG9mIHRoZSB1c2VkIHZhcmlhYmxlcy5cbiAgICAgKiBAcGFyYW0ge3N0cmluZ30gdmFyTmFtZVxuICAgICAqL1xuICAgIGFkZFVzZWRWYXIodmFyTmFtZSkge1xuICAgICAgICBpZiAodGhpcy51c2VkVmFyaWFibGVzLmluZGV4T2YodmFyTmFtZSkgPT09IC0xKSB7XG4gICAgICAgICAgICB0aGlzLnVzZWRWYXJpYWJsZXMucHVzaCh2YXJOYW1lKTtcbiAgICAgICAgfVxuICAgIH1cblxuICAgIC8qKlxuICAgICAqIFJldHVybnMgdGhlIHVzZWQgdmFyaWFibGVzLlxuICAgICAqIEByZXR1cm4ge0FycmF5LjxzdHJpbmc+fVxuICAgICAqL1xuICAgIGdldFVzZWRWYXJOYW1lcygpIHtcbiAgICAgICAgcmV0dXJuIHRoaXMudXNlZFZhcmlhYmxlcztcbiAgICB9XG5cbiAgICAvKipcbiAgICAgKiBDaGVja3Mgd2hldGhlciBgdmFyTmFtZWAgaXMgdXNlZC5cbiAgICAgKiBAcGFyYW0gdmFyTmFtZVxuICAgICAqIEByZXR1cm4ge2Jvb2xlYW59XG4gICAgICovXG4gICAgaXNVc2VkVmFyKHZhck5hbWUpIHtcbiAgICAgICAgcmV0dXJuIHRoaXMudXNlZFZhcmlhYmxlcy5pbmRleE9mKHZhck5hbWUpID4gLTE7XG4gICAgfVxuXG4gICAgLyoqXG4gICAgICogUmV0dXJucyBhIG1hcHBpbmcgZnJvbSB2YXJpYWJsZSBuYW1lcyB0byB0aGVpciBBVmFscy5cbiAgICAgKiBAcGFyYW0ge0NhbGxTaXRlQ29udGV4dH0gZGVsdGFcbiAgICAgKiBAcmV0dXJuIHtNYXAuPHN0cmluZywgQVZhbD59XG4gICAgICovXG4gICAgZ2V0SW5zdGFuY2UoZGVsdGEpIHtcbiAgICAgICAgaWYgKHRoaXMuaW5zdGFuY2VzLmhhcyhkZWx0YSkpIHtcbiAgICAgICAgICAgIHJldHVybiB0aGlzLmluc3RhbmNlcy5nZXQoZGVsdGEpO1xuICAgICAgICB9XG4gICAgICAgIC8vIGNvbnN0cnVjdCBWYXJNYXBcbiAgICAgICAgY29uc3QgdmFyTWFwID0gbmV3IE1hcCgpO1xuICAgICAgICBjb25zdCB2YXJOYW1lcyA9IHRoaXMuZ2V0UGFyYW1WYXJOYW1lcygpLmNvbmNhdCh0aGlzLmdldExvY2FsVmFyTmFtZXMoKSk7XG5cbiAgICAgICAgZm9yIChsZXQgaSA9IDA7IGkgPCB2YXJOYW1lcy5sZW5ndGg7IGkrKykge1xuICAgICAgICAgICAgdmFyTWFwLnNldCh2YXJOYW1lc1tpXSwgbmV3IHR5cGVzLkFWYWwoKSk7XG4gICAgICAgIH1cbiAgICAgICAgLy8gcmVtZW1iZXIgdGhlIGluc3RhbmNlXG4gICAgICAgIHRoaXMuaW5zdGFuY2VzLnNldChkZWx0YSx2YXJNYXApO1xuICAgICAgICByZXR1cm4gdmFyTWFwO1xuICAgIH1cblxuICAgIC8qKlxuICAgICAqIFJldHVybnMgYW4gYXJyYXkgb2YgQVZhbHMgZm9yIHBhcmFtZXRlcnNcbiAgICAgKiBAcGFyYW0gZGVsdGFcbiAgICAgKiBAcmV0dXJucyB7QXJyYXkuPEFWYWw+fVxuICAgICAqL1xuICAgIGdldFBhcmFtQVZhbHMoZGVsdGEpIHtcbiAgICAgICAgY29uc3QgaW5zdGFuY2UgPSB0aGlzLmdldEluc3RhbmNlKGRlbHRhKTtcbiAgICAgICAgY29uc3QgcGFyYW1zID0gW107XG4gICAgICAgIHRoaXMuZ2V0UGFyYW1WYXJOYW1lcygpLmZvckVhY2gobmFtZSA9PiB7XG4gICAgICAgICAgICBwYXJhbXMucHVzaChpbnN0YW5jZS5nZXQobmFtZSkpO1xuICAgICAgICB9KTtcbiAgICAgICAgcmV0dXJuIHBhcmFtcztcbiAgICB9XG5cbiAgICAvKipcbiAgICAgKiBSZXR1cm5zIGFuIEFWYWwgZm9yIGBhcmd1bWVudHNgLlxuICAgICAqIEBwYXJhbSBkZWx0YVxuICAgICAqIEByZXR1cm5zIHtBVmFsfVxuICAgICAqL1xuICAgIGdldEFyZ3VtZW50c0FWYWwoZGVsdGEpIHtcbiAgICAgICAgaWYgKCF0aGlzLnVzZUFyZ3VtZW50c09iamVjdCkge1xuICAgICAgICAgICAgdGhyb3cgbmV3IEVycm9yKCdOb3QgZm9yIHRoaXMgVmFyQmxvY2snKTtcbiAgICAgICAgfVxuICAgICAgICByZXR1cm4gdGhpcy5nZXRJbnN0YW5jZShkZWx0YSkuZ2V0KCdhcmd1bWVudHMnKTtcbiAgICB9XG5cbiAgICAvKipcbiAgICAgKiBHZXQgYSBTY29wZSBpbnN0YW5jZVxuICAgICAqIEBwYXJhbSBwYXJlblxuICAgICAqIEBwYXJhbSBkZWx0YVxuICAgICAqIEByZXR1cm5zIHsqfVxuICAgICAqL1xuICAgIGdldFNjb3BlSW5zdGFuY2UocGFyZW4sIGRlbHRhKSB7XG4gICAgICAgIGNvbnN0IHZhck1hcCA9IHRoaXMuZ2V0SW5zdGFuY2UoZGVsdGEpO1xuICAgICAgICBsZXQgZm91bmQgPSBudWxsO1xuXG4gICAgICAgIHRoaXMuc2NvcGVJbnN0YW5jZXMuZm9yRWFjaChmdW5jdGlvbiAoc2MpIHtcbiAgICAgICAgICAgIGlmIChzYy5wYXJlbiA9PT0gcGFyZW4gJiYgc2MudmFyTWFwID09PSB2YXJNYXApIGZvdW5kID0gc2M7XG4gICAgICAgIH0pO1xuXG4gICAgICAgIGlmIChmb3VuZCkge1xuICAgICAgICAgICAgcmV0dXJuIGZvdW5kO1xuICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgICAgbGV0IG5ld1Njb3BlSW5zdGFuY2UgPSBuZXcgU2NvcGUocGFyZW4sIHZhck1hcCwgdGhpcyk7XG4gICAgICAgICAgICB0aGlzLnNjb3BlSW5zdGFuY2VzLnB1c2gobmV3U2NvcGVJbnN0YW5jZSk7XG4gICAgICAgICAgICByZXR1cm4gbmV3U2NvcGVJbnN0YW5jZTtcbiAgICAgICAgfVxuICAgIH1cblxuICAgIC8qKlxuICAgICAqIEdldCBmdW5jdGlvbidzIHNjb3BlIGluc3RhbmNlcyB3aG9zZSBwYXJlbiBpcyBgcFNjb3BlYC5cbiAgICAgKiBAcGFyYW0gcFNjb3BlXG4gICAgICogQHJldHVybnMge1NldC48U2NvcGU+fVxuICAgICAqL1xuICAgIGdldFNjb3Blc1dpdGhQYXJlbnQocFNjb3BlKSB7XG4gICAgICAgIGNvbnN0IGluc3RhbmNlcyA9IG5ldyBTZXQoKTtcbiAgICAgICAgdGhpcy5zY29wZUluc3RhbmNlcy5mb3JFYWNoKHNjID0+IHtcbiAgICAgICAgICAgIGlmIChzYy5wYXJlbiA9PT0gcFNjb3BlKSBpbnN0YW5jZXMuYWRkKHNjKTtcbiAgICAgICAgfSk7XG4gICAgICAgIHJldHVybiBpbnN0YW5jZXM7XG4gICAgfVxufVxuXG4vKipcbiAqIEBzdGF0aWNcbiAqL1xuVmFyQmxvY2suYmxvY2tUeXBlcyA9IHtcbiAgICBnbG9iYWxCbG9jazogU3ltYm9sKCdnbG9iYWwnKSxcbiAgICBvbGRGdW5jdGlvbkJsb2NrOiBTeW1ib2woJ29sZEZ1bmN0aW9uJyksXG4gICAgYXJyb3dGdW5jdGlvbkJsb2NrOiBTeW1ib2woJ2Fycm93RnVuY3Rpb24nKSxcbiAgICBwYXJhbWV0ZXJCbG9jazogU3ltYm9sKCdwYXJhbWV0ZXInKSwgIC8vIHRob3VnaCBub3QgcmVhbGx5IGluIGJyYWNlc1xuICAgIGNhdGNoQmxvY2s6IFN5bWJvbCgnY2F0Y2gnKSxcbiAgICBub3JtYWxCbG9jazogU3ltYm9sKCdub3JtYWwnKVxufTtcblxuLyoqXG4gKiBAc3RhdGljXG4gKi9cblZhckJsb2NrLmRlY2xhcmF0aW9uVHlwZXMgPSB7XG4gICAgbGV0RGVjbGFyYXRpb246IFN5bWJvbCgnbGV0JyksXG4gICAgY29uc3REZWNsYXJhdGlvbjogU3ltYm9sKCdjb25zdCcpLFxuICAgIHZhckRlY2xhcmF0aW9uOiBTeW1ib2woJ3ZhcicpLFxuICAgIGZ1bmN0aW9uRGVjbGFyYXRpb246IFN5bWJvbCgnZnVuY3Rpb24nKSxcbiAgICBwYXJhbWV0ZXJEZWNsYXJhdGlvbjogU3ltYm9sKCdwYXJhbWV0ZXInKSxcbiAgICBpbXBsaWNpdEdsb2JhbERlY2xhcmF0aW9uOiBTeW1ib2woJ2ltcGxpY2l0IGdsb2JhbCcpXG59O1xuXG4vKipcbiAqIENoZWNrIHdoZXRoZXIgdGhlIHN0bXQgaXMgdGhlIGRpcmVjdGl2ZSBmb3Igc3RyaWN0bmVzcy5cbiAqIFRha2VuIGZyb20gYWNvcm5cbiAqIEBwYXJhbSBzdG10IC0gdGhlIGZpcnN0IHN0YXRlbWVudCBvZiBhIGJvZHlcbiAqIEByZXR1cm4ge2Jvb2xlYW59XG4gKi9cbmZ1bmN0aW9uIF9pc1VzZVN0cmljdChzdG10KSB7XG4gICAgcmV0dXJuIHN0bXQudHlwZSA9PT0gJ0V4cHJlc3Npb25TdGF0ZW1lbnQnICYmXG4gICAgICAgIHN0bXQuZXhwcmVzc2lvbi50eXBlID09PSAnTGl0ZXJhbCcgJiZcbiAgICAgICAgc3RtdC5leHByZXNzaW9uLnJhdy5zbGljZSgxLCAtMSkgPT09ICd1c2Ugc3RyaWN0Jztcbn1cblxuXG5jb25zdCBfZGVjbGFyZWRWYXJpYWJsZUZpbmRlciA9IHdhbGsubWFrZSh7XG4gICAgVmFyaWFibGVQYXR0ZXJuOiAobm9kZSwgW2RUeXBlLCBjdXJyQmxvY2tdLCBjKSA9PiB7XG4gICAgICAgIGlmIChkVHlwZSA9PT0gVmFyQmxvY2suZGVjbGFyYXRpb25UeXBlcy5wYXJhbWV0ZXJEZWNsYXJhdGlvbikge1xuICAgICAgICAgICAgY3VyckJsb2NrLmFkZFBhcmFtVmFyKG5vZGUubmFtZSk7XG4gICAgICAgIH0gZWxzZSBpZiAoZFR5cGUpIHtcbiAgICAgICAgICAgIGN1cnJCbG9jay5hZGREZWNsYXJlZExvY2FsVmFyKG5vZGUubmFtZSwgZFR5cGUpO1xuICAgICAgICB9XG4gICAgfSxcbiAgICBGdW5jdGlvbjogKG5vZGUsIFtkVHlwZSwgY3VyckJsb2NrXSwgYykgPT4ge1xuICAgICAgICBsZXQgcGFyZW5CbG9jayA9IGN1cnJCbG9jaywgcGFyYW1CbG9jaztcbiAgICAgICAgaWYgKG5vZGUuaWQpIHtcbiAgICAgICAgICAgIGNvbnN0IGZ1bmNOYW1lID0gbm9kZS5pZC5uYW1lO1xuICAgICAgICAgICAgcGFyZW5CbG9jayA9IGN1cnJCbG9jay5hZGREZWNsYXJlZExvY2FsVmFyKGZ1bmNOYW1lLFxuICAgICAgICAgICAgICAgIFZhckJsb2NrLmRlY2xhcmF0aW9uVHlwZXMuZnVuY3Rpb25EZWNsYXJhdGlvbik7XG4gICAgICAgIH1cbiAgICAgICAgY29uc3QgaGFzUGFyYW1TY29wZSA9IG5vZGUucGFyYW1zLnNvbWUoKHB0bikgPT5cbiAgICAgICAgICAgIG15V2Fsa2VyLnBhdHRlcm5IYXNEZWZhdWx0cyhwdG4pKTtcbiAgICAgICAgaWYgKGhhc1BhcmFtU2NvcGUpIHtcbiAgICAgICAgICAgIHBhcmFtQmxvY2sgPSBwYXJlbkJsb2NrID0gbmV3IFZhckJsb2NrKFxuICAgICAgICAgICAgICAgIHBhcmVuQmxvY2ssXG4gICAgICAgICAgICAgICAgbm9kZSxcbiAgICAgICAgICAgICAgICBWYXJCbG9jay5ibG9ja1R5cGVzLnBhcmFtZXRlckJsb2NrLFxuICAgICAgICAgICAgICAgIGN1cnJCbG9jay5pc1N0cmljdFxuICAgICAgICAgICAgKTtcbiAgICAgICAgICAgIG5vZGVbJ0BibG9jayddID0gcGFyYW1CbG9jaztcbiAgICAgICAgfVxuICAgICAgICBjb25zdCBzdHJpY3RJbm5lciA9IGN1cnJCbG9jay5pc1N0cmljdCB8fFxuICAgICAgICAgICAgKG5vZGUuYm9keS5ib2R5ICYmXG4gICAgICAgICAgICAgbm9kZS5ib2R5LmJvZHlbMF0gJiZcbiAgICAgICAgICAgICBfaXNVc2VTdHJpY3Qobm9kZS5ib2R5LmJvZHlbMF0pKTtcbiAgICAgICAgY29uc3QgZnVuY0Jsb2NrID0gbmV3IFZhckJsb2NrKFxuICAgICAgICAgICAgcGFyZW5CbG9jayxcbiAgICAgICAgICAgIG5vZGUsICAvLyBzYW1lIG9yaWdpbk5vZGUgd2l0aCBwYXJhbUJsb2NrLCBpbnRlbmRlZC5cbiAgICAgICAgICAgIG5vZGUudHlwZSA9PT0gJ0Fycm93RnVuY3Rpb25FeHByZXNzaW9uJz9cbiAgICAgICAgICAgICAgICBWYXJCbG9jay5ibG9ja1R5cGVzLmFycm93RnVuY3Rpb25CbG9ja1xuICAgICAgICAgICAgICAgIDogVmFyQmxvY2suYmxvY2tUeXBlcy5vbGRGdW5jdGlvbkJsb2NrLFxuICAgICAgICAgICAgc3RyaWN0SW5uZXJcbiAgICAgICAgKTtcbiAgICAgICAgZnVuY0Jsb2NrLmhhc1BhcmFtU2NvcGUgPSBoYXNQYXJhbVNjb3BlO1xuICAgICAgICBub2RlLmJvZHlbJ0BibG9jayddID0gZnVuY0Jsb2NrO1xuXG4gICAgICAgIC8vIGFkZCBmdW5jdGlvbiBwYXJhbWV0ZXJzIHRvIGNvcnJlc3BvbmRpbmcgc2NvcGVcbiAgICAgICAgY29uc3QgcGFyYW1UYXJnZXRCbG9jayA9IHBhcmFtQmxvY2sgfHwgZnVuY0Jsb2NrO1xuICAgICAgICBmb3IgKGxldCBpID0gMDsgaSA8IG5vZGUucGFyYW1zLmxlbmd0aDsgaSsrKSB7XG4gICAgICAgICAgICBjKG5vZGUucGFyYW1zW2ldLFxuICAgICAgICAgICAgICAgIFtcbiAgICAgICAgICAgICAgICAgICAgVmFyQmxvY2suZGVjbGFyYXRpb25UeXBlcy5wYXJhbWV0ZXJEZWNsYXJhdGlvbixcbiAgICAgICAgICAgICAgICAgICAgcGFyYW1UYXJnZXRCbG9ja1xuICAgICAgICAgICAgICAgIF0sXG4gICAgICAgICAgICAgICAgJ1BhdHRlcm4nKTtcbiAgICAgICAgfVxuXG4gICAgICAgIGlmIChub2RlLmV4cHJlc3Npb24pIHtcbiAgICAgICAgICAgIGMobm9kZS5ib2R5LCBbLCBmdW5jQmxvY2tdLCAnRXhwcmVzc2lvbicpO1xuICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgICAgd2Fsay5iYXNlLkJsb2NrU3RhdGVtZW50KG5vZGUuYm9keSwgWywgZnVuY0Jsb2NrXSwgYyk7XG4gICAgICAgIH1cbiAgICB9LFxuXG4gICAgRm9yU3RhdGVtZW50OiAobm9kZSwgWywgY3VyckJsb2NrXSwgYykgPT4ge1xuICAgICAgICBsZXQgZm9yQmxvY2s7XG4gICAgICAgIGlmIChjdXJyQmxvY2suaXNTdHJpY3QpIHtcbiAgICAgICAgICAgIGZvckJsb2NrID0gbmV3IFZhckJsb2NrKFxuICAgICAgICAgICAgICAgIGN1cnJCbG9jayxcbiAgICAgICAgICAgICAgICBub2RlLFxuICAgICAgICAgICAgICAgIFZhckJsb2NrLmJsb2NrVHlwZXMubm9ybWFsQmxvY2ssXG4gICAgICAgICAgICAgICAgY3VyckJsb2NrLmlzU3RyaWN0XG4gICAgICAgICAgICApO1xuICAgICAgICAgICAgbm9kZVsnQGJsb2NrJ10gPSBmb3JCbG9jaztcbiAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICAgIGZvckJsb2NrID0gY3VyckJsb2NrO1xuICAgICAgICB9XG4gICAgICAgIGlmIChub2RlLmluaXQpIGMobm9kZS5pbml0LCBbLCBmb3JCbG9ja10sICdGb3JJbml0Jyk7XG4gICAgICAgIGlmIChub2RlLnRlc3QpIGMobm9kZS50ZXN0LCBbLCBmb3JCbG9ja10sICdFeHByZXNzaW9uJyk7XG4gICAgICAgIGlmIChub2RlLnVwZGF0ZSkgYyhub2RlLnVwZGF0ZSwgWywgZm9yQmxvY2tdLCAnRXhwcmVzc2lvbicpO1xuICAgICAgICAvLyBpdHMgYm9keSBjYW4gaGF2ZSBhIHNlcGFyYXRlIGJsb2NrLlxuICAgICAgICBjKG5vZGUuYm9keSwgWywgZm9yQmxvY2tdLCB1bmRlZmluZWQpO1xuICAgIH0sXG5cbiAgICBWYXJpYWJsZURlY2xhcmF0aW9uOiAobm9kZSwgWywgY3VyckJsb2NrXSwgYykgPT4ge1xuICAgICAgICBsZXQgZFR5cGU7XG4gICAgICAgIHN3aXRjaChub2RlLmtpbmQpIHtcbiAgICAgICAgICAgIGNhc2UgJ3Zhcic6XG4gICAgICAgICAgICAgICAgZFR5cGUgPSBWYXJCbG9jay5kZWNsYXJhdGlvblR5cGVzLnZhckRlY2xhcmF0aW9uO1xuICAgICAgICAgICAgICAgIGJyZWFrO1xuICAgICAgICAgICAgY2FzZSAnbGV0JzpcbiAgICAgICAgICAgICAgICBkVHlwZSA9IFZhckJsb2NrLmRlY2xhcmF0aW9uVHlwZXMubGV0RGVjbGFyYXRpb247XG4gICAgICAgICAgICAgICAgYnJlYWs7XG4gICAgICAgICAgICBjYXNlICdjb25zdCc6XG4gICAgICAgICAgICAgICAgZFR5cGUgPSBWYXJCbG9jay5kZWNsYXJhdGlvblR5cGVzLmNvbnN0RGVjbGFyYXRpb247XG4gICAgICAgICAgICAgICAgYnJlYWs7XG4gICAgICAgIH1cblxuICAgICAgICBmb3IgKGxldCBpID0gMDsgaSA8IG5vZGUuZGVjbGFyYXRpb25zLmxlbmd0aDsgaSsrKSB7XG4gICAgICAgICAgICBjKG5vZGUuZGVjbGFyYXRpb25zW2ldLCBbZFR5cGUsIGN1cnJCbG9ja10sIHVuZGVmaW5lZCk7XG4gICAgICAgIH1cbiAgICB9LFxuXG4gICAgVHJ5U3RhdGVtZW50OiAobm9kZSwgWywgY3VyclNjb3BlXSwgYykgPT4ge1xuICAgICAgICBjKG5vZGUuYmxvY2ssIFssIGN1cnJTY29wZV0sIHVuZGVmaW5lZCk7XG4gICAgICAgIGlmIChub2RlLmhhbmRsZXIpIHtcbiAgICAgICAgICAgIGMobm9kZS5oYW5kbGVyLCBbLCBjdXJyU2NvcGVdLCB1bmRlZmluZWQpO1xuICAgICAgICB9XG4gICAgICAgIGlmIChub2RlLmZpbmFsaXplcikge1xuICAgICAgICAgICAgYyhub2RlLmZpbmFsaXplciwgWywgY3VyclNjb3BlXSwgdW5kZWZpbmVkKTtcbiAgICAgICAgfVxuICAgIH0sXG5cbiAgICBDYXRjaENsYXVzZTogKG5vZGUsIFssIGN1cnJCbG9ja10sIGMpID0+IHtcbiAgICAgICAgY29uc3QgY2F0Y2hCbG9jayA9IG5ldyBWYXJCbG9jayhcbiAgICAgICAgICAgIGN1cnJCbG9jayxcbiAgICAgICAgICAgIG5vZGUsXG4gICAgICAgICAgICBWYXJCbG9jay5ibG9ja1R5cGVzLmNhdGNoQmxvY2ssXG4gICAgICAgICAgICBjdXJyQmxvY2suaXNTdHJpY3RcbiAgICAgICAgKTtcbiAgICAgICAgYyhub2RlLnBhcmFtLFxuICAgICAgICAgICAgW1xuICAgICAgICAgICAgICAgIFZhckJsb2NrLmRlY2xhcmF0aW9uVHlwZXMucGFyYW1ldGVyRGVjbGFyYXRpb24sXG4gICAgICAgICAgICAgICAgY2F0Y2hCbG9ja1xuICAgICAgICAgICAgXSxcbiAgICAgICAgICAgICdQYXR0ZXJuJyk7XG4gICAgICAgIG5vZGUuYm9keVsnQGJsb2NrJ10gPSBjYXRjaEJsb2NrO1xuICAgICAgICB3YWxrLmJhc2UuQmxvY2tTdGF0ZW1lbnQobm9kZS5ib2R5LCBbLCBjYXRjaEJsb2NrXSwgYyk7XG4gICAgfSxcblxuICAgIC8vIENyZWF0ZSBWYXJCbG9jayBvZiB0eXBlIG5vcm1hbEJsb2NrXG4gICAgQmxvY2tTdGF0ZW1lbnQ6IChub2RlLCBbLCBjdXJyQmxvY2tdLCBjKSA9PiB7XG4gICAgICAgIGxldCBpbkJsb2NrO1xuICAgICAgICBpZiAoY3VyckJsb2NrLmlzU3RyaWN0KSB7XG4gICAgICAgICAgICBpbkJsb2NrID0gbmV3IFZhckJsb2NrKFxuICAgICAgICAgICAgICAgIGN1cnJCbG9jayxcbiAgICAgICAgICAgICAgICBub2RlLFxuICAgICAgICAgICAgICAgIFZhckJsb2NrLmJsb2NrVHlwZXMubm9ybWFsQmxvY2ssXG4gICAgICAgICAgICAgICAgY3VyckJsb2NrLmlzU3RyaWN0XG4gICAgICAgICAgICApO1xuICAgICAgICAgICAgbm9kZVsnQGJsb2NrJ10gPSBpbkJsb2NrO1xuICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgICAgaW5CbG9jayA9IGN1cnJCbG9jaztcbiAgICAgICAgfVxuICAgICAgICB3YWxrLmJhc2UuQmxvY2tTdGF0ZW1lbnQobm9kZSwgWywgaW5CbG9ja10sIGMpO1xuICAgIH1cbn0pO1xuXG4vLyBGb3IgdmFyaWFibGVzIGluIGdsb2JhbCBhbmQgYXJndW1lbnRzIGluIGZ1bmN0aW9uc1xuY29uc3QgX3ZhcmlhYmxlVXNhZ2VDb2xsZWN0b3IgPSB3YWxrLm1ha2Uoe1xuICAgIFZhcmlhYmxlUGF0dGVybjogKG5vZGUsIGN1cnJCbG9jaywgYykgPT4ge1xuICAgICAgICBjKG5vZGUsIGN1cnJCbG9jaywgJ0lkZW50aWZpZXInKTtcbiAgICB9LFxuXG4gICAgSWRlbnRpZmllcjogKG5vZGUsIGN1cnJCbG9jaywgYykgPT4ge1xuICAgICAgICBpZiAobXlXYWxrZXIuaXNEdW1teUlkTm9kZShub2RlKSkge1xuICAgICAgICAgICAgLy8gU2tpcCBkdW1teSBJZCBub2RlXG4gICAgICAgICAgICByZXR1cm47XG4gICAgICAgIH1cbiAgICAgICAgbGV0IGJsb2NrID0gY3VyckJsb2NrO1xuICAgICAgICBjb25zdCB2YXJOYW1lID0gbm9kZS5uYW1lO1xuXG4gICAgICAgIHdoaWxlIChibG9jayAmJiAhYmxvY2suaGFzVmFyKHZhck5hbWUpKSB7XG4gICAgICAgICAgICBpZiAodmFyTmFtZSA9PT0gJ2FyZ3VtZW50cycgJiZcbiAgICAgICAgICAgICAgICAoYmxvY2suaXNPbGRGdW5jdGlvbkJsb2NrKCkgfHxcbiAgICAgICAgICAgICAgICAgYmxvY2suaXNQYXJhbWV0ZXJCbG9jaygpKSkge1xuICAgICAgICAgICAgICAgIGlmIChibG9jay5oYXNQYXJhbVNjb3BlKSB7XG4gICAgICAgICAgICAgICAgICAgIGJsb2NrID0gYmxvY2sucGFyZW47XG4gICAgICAgICAgICAgICAgICAgIGlmIChibG9jay5oYXNWYXIodmFyTmFtZSkpIGJyZWFrO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICBibG9jay51c2VBcmd1bWVudHNPYmplY3QgPSB0cnVlO1xuICAgICAgICAgICAgICAgIC8vIGNvbnNpZGVyICd2YXInIGlzIHVzZWQgZm9yIGRlY2xhcmF0aW9uIG9mICdhcmd1bWVudHMuJ1xuICAgICAgICAgICAgICAgIGJsb2NrLmFkZERlY2xhcmVkTG9jYWxWYXIodmFyTmFtZSwgVmFyQmxvY2suZGVjbGFyYXRpb25UeXBlcy52YXJEZWNsYXJhdGlvbik7XG4gICAgICAgICAgICAgICAgYnJlYWs7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBpZiAoYmxvY2suaXNHbG9iYWwoKSkge1xuICAgICAgICAgICAgICAgIGJsb2NrLmFkZERlY2xhcmVkTG9jYWxWYXIodmFyTmFtZSwgVmFyQmxvY2suZGVjbGFyYXRpb25UeXBlcy5pbXBsaWNpdEdsb2JhbERlY2xhcmF0aW9uKTtcbiAgICAgICAgICAgICAgICBicmVhaztcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGJsb2NrID0gYmxvY2sucGFyZW47XG4gICAgICAgIH1cbiAgICAgICAgaWYgKGJsb2NrLmhhc1Zhcih2YXJOYW1lKSkge1xuICAgICAgICAgICAgYmxvY2suYWRkVXNlZFZhcih2YXJOYW1lKTtcbiAgICAgICAgfVxuICAgIH0sXG5cbiAgICBSZXR1cm5TdGF0ZW1lbnQ6IChub2RlLCBjdXJyQmxvY2ssIGMpID0+IHtcbiAgICAgICAgbGV0IGJsb2NrID0gY3VyckJsb2NrO1xuICAgICAgICB3aGlsZSAoYmxvY2suaXNDYXRjaEJsb2NrKCkgfHwgYmxvY2suaXNOb3JtYWxCbG9jaygpKSB7XG4gICAgICAgICAgICBibG9jayA9IGJsb2NrLnBhcmVuO1xuICAgICAgICB9XG4gICAgICAgIGlmICghYmxvY2suaXNHbG9iYWwoKSAmJiBub2RlLmFyZ3VtZW50ICE9PSBudWxsKSB7XG4gICAgICAgICAgICBibG9jay51c2VSZXR1cm5XaXRoQXJndW1lbnQgPSB0cnVlO1xuICAgICAgICB9XG4gICAgICAgIGlmIChub2RlLmFyZ3VtZW50KSB7XG4gICAgICAgICAgICBjKG5vZGUuYXJndW1lbnQsIGN1cnJCbG9jaywgdW5kZWZpbmVkKTtcbiAgICAgICAgfVxuICAgIH0sXG5cbiAgICBGdW5jdGlvbjogKG5vZGUsIGN1cnJCbG9jaywgYykgPT4ge1xuICAgICAgICBpZiAobm9kZS5pZCkgYyhub2RlLmlkLCBjdXJyQmxvY2ssICdQYXR0ZXJuJyk7XG4gICAgICAgIGlmIChub2RlWydAYmxvY2snXSkge1xuICAgICAgICAgICAgY29uc3QgcGFyYW1CbG9jayA9IG5vZGVbJ0BibG9jayddO1xuICAgICAgICAgICAgZm9yIChsZXQgaSA9IDA7IGkgPCBub2RlLnBhcmFtcy5sZW5ndGg7IGkrKykge1xuICAgICAgICAgICAgICAgIGMobm9kZS5wYXJhbXNbaV0sIHBhcmFtQmxvY2ssICdQYXR0ZXJuJyk7XG4gICAgICAgICAgICB9XG4gICAgICAgIH1cbiAgICAgICAgYyhub2RlLmJvZHksIGN1cnJCbG9jayk7XG4gICAgfSxcblxuICAgIFNjb3BlQm9keTogKG5vZGUsIGN1cnJCbG9jaywgYykgPT4ge1xuICAgICAgICBjKG5vZGUsIG5vZGVbJ0BibG9jayddIHx8IGN1cnJCbG9jayk7XG4gICAgfSxcblxuICAgIEJsb2NrU3RhdGVtZW50OiAobm9kZSwgY3VyckJsb2NrLCBjKSA9PiB7XG4gICAgICAgIC8vIFByb2Nlc3MgQmxvY2tTdGF0ZW1lbnQgd2l0aCBjaGFuZ2VkIFZhckJsb2NrXG4gICAgICAgIHdhbGsuYmFzZS5CbG9ja1N0YXRlbWVudChub2RlLCBub2RlWydAYmxvY2snXSB8fCBjdXJyQmxvY2ssIGMpO1xuICAgIH1cbn0pO1xuXG4vKipcbiAqIEFuYWx5emVzIGBhc3RgIGFuZCBhbm5vdGF0ZXMgaXQgd2l0aCBWYXJCbG9ja3MuXG4gKiBAcGFyYW0gYXN0XG4gKiBAcGFyYW0gZ1ZhckJsb2NrXG4gKiBAcmV0dXJuIHsqfVxuICovXG5leHBvcnQgZnVuY3Rpb24gYW5ub3RhdGVCbG9ja0luZm8oYXN0LCBnVmFyQmxvY2spIHtcbiAgICBhc3RbJ0BibG9jayddID0gZ1ZhckJsb2NrO1xuXG4gICAgZ1ZhckJsb2NrLmlzU3RyaWN0ID0gZ1ZhckJsb2NrLmlzU3RyaWN0IHx8XG4gICAgICAgIChhc3QuYm9keVswXSAmJiBfaXNVc2VTdHJpY3QoYXN0LmJvZHlbMF0pKTtcblxuICAgIHdhbGsucmVjdXJzaXZlKGFzdCwgWywgZ1ZhckJsb2NrXSwgX2RlY2xhcmVkVmFyaWFibGVGaW5kZXIpO1xuICAgIHdhbGsucmVjdXJzaXZlKGFzdCwgZ1ZhckJsb2NrLCBfdmFyaWFibGVVc2FnZUNvbGxlY3Rvcik7XG4gICAgcmV0dXJuIGFzdDtcbn1cblxuY2xhc3MgU2NvcGUge1xuICAgIC8qKlxuICAgICAqIENvbnN0cnVjdCBTY29wZSBpbnN0YW5jZS5cbiAgICAgKiBAcGFyYW0ge1Njb3BlfSBwYXJlblxuICAgICAqIEBwYXJhbSB7TWFwLjxzdHJpbmcsIEFWYWw+fSB2YXJNYXBcbiAgICAgKiBAcGFyYW0ge1ZhckJsb2NrfSB2YlxuICAgICAqL1xuICAgIGNvbnN0cnVjdG9yKHBhcmVuLCB2YXJNYXAsIHZiKSB7XG4gICAgICAgIHRoaXMucGFyZW4gPSBwYXJlbjtcbiAgICAgICAgdGhpcy52YXJNYXAgPSB2YXJNYXA7XG4gICAgICAgIHRoaXMudmIgPSB2YjtcbiAgICAgICAgaWYgKHZiLmJsb2NrVHlwZSA9PT0gVmFyQmxvY2suYmxvY2tUeXBlcy5jYXRjaEJsb2NrKSB7XG4gICAgICAgICAgICAvLyBDb2xsZWN0IHRocm93biBpbnRvIC5jYXVnaHRBVmFsLCBhbmQgY29ubmVjdCB0byBwYXJhbWV0ZXIgcGF0dGVyblxuICAgICAgICAgICAgdGhpcy5jYXVnaHRBVmFsID0gbmV3IHR5cGVzLkFWYWw7XG4gICAgICAgIH1cbiAgICB9XG5cbiAgICAvKipcbiAgICAgKiBGaW5kIEFWYWwgb2YgYHZhck5hbWVgIGluIHRoZSBjaGFpblxuICAgICAqIEBwYXJhbSB7c3RyaW5nfSB2YXJOYW1lXG4gICAgICogQHJldHVybiB7QVZhbH1cbiAgICAgKi9cbiAgICBnZXRBVmFsT2YodmFyTmFtZSkge1xuICAgICAgICBsZXQgY3VyciA9IHRoaXM7XG4gICAgICAgIHdoaWxlIChjdXJyICE9IG51bGwpIHtcbiAgICAgICAgICAgIGlmIChjdXJyLnZhck1hcC5oYXModmFyTmFtZSkpIHtcbiAgICAgICAgICAgICAgICByZXR1cm4gY3Vyci52YXJNYXAuZ2V0KHZhck5hbWUpO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgY3VyciA9IGN1cnIucGFyZW47XG4gICAgICAgIH1cbiAgICAgICAgLy8gcmV0dXJucyBkdW1teSBBVmFsIGZvciBub3QgZm91bmQgdmFyaWFibGVzXG4gICAgICAgIHJldHVybiB0eXBlcy5BVmFsTnVsbDtcbiAgICB9XG5cbiAgICAvKipcbiAgICAgKiBGaW5kcyB0aGUgZmlyc3Qgc2NvcGUgdGhhdCBpcyBub3QgZm9yIGNhdGNoIG9yIG5vcm1hbCBibG9jay5cbiAgICAgKiBAcmV0dXJuIHtTY29wZX1cbiAgICAgKi9cbiAgICByZW1vdmVJbml0aWFsQ2F0Y2hPck5vcm1hbEJsb2NrcygpIHtcbiAgICAgICAgbGV0IGN1cnIgPSB0aGlzO1xuICAgICAgICB3aGlsZSAoY3Vyci52Yi5pc0NhdGNoQmxvY2soKSB8fCBjdXJyLnZiLmlzTm9ybWFsQmxvY2soKSkge1xuICAgICAgICAgICAgY3VyciA9IGN1cnIucGFyZW47XG4gICAgICAgIH1cbiAgICAgICAgcmV0dXJuIGN1cnI7XG4gICAgfVxufVxuIiwiLyoqXG4gKiBAZmlsZSBJbXBsZW1lbnRzIHZhcmlhYmxlIG9jY3VycmVuY2UgZmluZGVyLlxuICogQGF1dGhvciBzZXdvbjMyNi5raW1Ac2Ftc3VuZy5jb21cbiAqL1xuXG5jb25zdCB3YWxrID0gcmVxdWlyZSgnYWNvcm4vZGlzdC93YWxrJyk7XG5pbXBvcnQgKiBhcyBteVdhbGtlciBmcm9tICcuL3V0aWwvbXlXYWxrZXInXG5cbi8qKlxuICogRmluZHMgb2NjdXJyZW5jZXMgb2YgdGhlIHZhcmlhYmxlIGF0IGBwb3NgLlxuICogQHBhcmFtIGFzdCAtIHNjb3BlIGFubm90YXRlZCBBU1RcbiAqIEBwYXJhbSB7bnVtYmVyfSBwb3MgLSBjaGFyYWN0ZXIgcG9zaXRpb25cbiAqIEByZXR1cm4geyp9IC0gYXJyYXkgb2YgQVNUIG5vZGVzXG4gKi9cbmV4cG9ydCBmdW5jdGlvbiBmaW5kVmFyUmVmc0F0KGFzdCwgcG9zKSB7XG4gICAgJ3VzZSBzdHJpY3QnO1xuICAgIGNvbnN0IGZvdW5kID0gbXlXYWxrZXIuZmluZElkZW50aWZpZXJBdChhc3QsIHBvcyk7XG4gICAgaWYgKCFmb3VuZCkge1xuICAgICAgICAvLyBwb3MgaXMgbm90IGF0IGEgdmFyaWFibGVcbiAgICAgICAgcmV0dXJuIG51bGw7XG4gICAgfVxuICAgIC8vIGZpbmQgcmVmcyBmb3IgdGhlIGlkIG5vZGVcbiAgICBjb25zdCByZWZzID0gX2ZpbmRSZWZzVG9WYXJpYWJsZShmb3VuZCkubWFwKG5vZGUgPT5cbiAgICAgICAgKHtzdGFydDogbm9kZS5zdGFydCwgZW5kOiBub2RlLmVuZH0pXG4gICAgKTtcbiAgICByZWZzLnZhck5hbWUgPSBmb3VuZC5ub2RlLm5hbWU7XG5cbiAgICByZXR1cm4gcmVmcztcbn1cblxuLyoqXG4gKiBAcGFyYW0gZm91bmQgLSBub2RlIGFuZCB2YXJCbG9jayBvZiB0aGUgdmFyaWFibGVcbiAqIEByZXR1cm4ge0FycmF5fSAtIGFycmF5IG9mIEFTVCBub2Rlc1xuICovXG5mdW5jdGlvbiBfZmluZFJlZnNUb1ZhcmlhYmxlKGZvdW5kKSB7XG4gICAgJ3VzZSBzdHJpY3QnO1xuICAgIGNvbnN0IHZhck5hbWUgPSBmb3VuZC5ub2RlLm5hbWU7XG4gICAgY29uc3QgdmIxID0gZm91bmQudmIuZmluZFZhckluQ2hhaW4odmFyTmFtZSk7XG4gICAgaWYgKCF2YjEpIHJldHVybiBbXTtcblxuICAgIGNvbnN0IHJlZnMgPSBbXTtcblxuICAgIGNvbnN0IHdhbGtlciA9IHdhbGsubWFrZSh7XG4gICAgICAgIElkZW50aWZpZXI6IChub2RlLCB2YikgPT4ge1xuICAgICAgICAgICAgaWYgKG5vZGUubmFtZSAhPT0gdmFyTmFtZSkgcmV0dXJuO1xuICAgICAgICAgICAgaWYgKHZiMSA9PT0gdmIuZmluZFZhckluQ2hhaW4odmFyTmFtZSkpIHtcbiAgICAgICAgICAgICAgICByZWZzLnB1c2gobm9kZSk7XG4gICAgICAgICAgICB9XG4gICAgICAgIH1cbiAgICB9LCBteVdhbGtlci52YXJXYWxrZXIpO1xuXG4gICAgd2Fsay5yZWN1cnNpdmUodmIxLm9yaWdpbk5vZGUsIHZiMS5vcmlnaW5Ob2RlWydAYmxvY2snXSwgd2Fsa2VyKTtcbiAgICByZXR1cm4gcmVmcztcbn1cbiIsIihmdW5jdGlvbihmKXtpZih0eXBlb2YgZXhwb3J0cz09PVwib2JqZWN0XCImJnR5cGVvZiBtb2R1bGUhPT1cInVuZGVmaW5lZFwiKXttb2R1bGUuZXhwb3J0cz1mKCl9ZWxzZSBpZih0eXBlb2YgZGVmaW5lPT09XCJmdW5jdGlvblwiJiZkZWZpbmUuYW1kKXtkZWZpbmUoW10sZil9ZWxzZXt2YXIgZztpZih0eXBlb2Ygd2luZG93IT09XCJ1bmRlZmluZWRcIil7Zz13aW5kb3d9ZWxzZSBpZih0eXBlb2YgZ2xvYmFsIT09XCJ1bmRlZmluZWRcIil7Zz1nbG9iYWx9ZWxzZSBpZih0eXBlb2Ygc2VsZiE9PVwidW5kZWZpbmVkXCIpe2c9c2VsZn1lbHNle2c9dGhpc31nLmFjb3JuID0gZigpfX0pKGZ1bmN0aW9uKCl7dmFyIGRlZmluZSxtb2R1bGUsZXhwb3J0cztyZXR1cm4gKGZ1bmN0aW9uIGUodCxuLHIpe2Z1bmN0aW9uIHMobyx1KXtpZighbltvXSl7aWYoIXRbb10pe3ZhciBhPXR5cGVvZiByZXF1aXJlPT1cImZ1bmN0aW9uXCImJnJlcXVpcmU7aWYoIXUmJmEpcmV0dXJuIGEobywhMCk7aWYoaSlyZXR1cm4gaShvLCEwKTt2YXIgZj1uZXcgRXJyb3IoXCJDYW5ub3QgZmluZCBtb2R1bGUgJ1wiK28rXCInXCIpO3Rocm93IGYuY29kZT1cIk1PRFVMRV9OT1RfRk9VTkRcIixmfXZhciBsPW5bb109e2V4cG9ydHM6e319O3Rbb11bMF0uY2FsbChsLmV4cG9ydHMsZnVuY3Rpb24oZSl7dmFyIG49dFtvXVsxXVtlXTtyZXR1cm4gcyhuP246ZSl9LGwsbC5leHBvcnRzLGUsdCxuLHIpfXJldHVybiBuW29dLmV4cG9ydHN9dmFyIGk9dHlwZW9mIHJlcXVpcmU9PVwiZnVuY3Rpb25cIiYmcmVxdWlyZTtmb3IodmFyIG89MDtvPHIubGVuZ3RoO28rKylzKHJbb10pO3JldHVybiBzfSkoezE6W2Z1bmN0aW9uKF9kZXJlcV8sbW9kdWxlLGV4cG9ydHMpe1xuLy8gQSByZWN1cnNpdmUgZGVzY2VudCBwYXJzZXIgb3BlcmF0ZXMgYnkgZGVmaW5pbmcgZnVuY3Rpb25zIGZvciBhbGxcbi8vIHN5bnRhY3RpYyBlbGVtZW50cywgYW5kIHJlY3Vyc2l2ZWx5IGNhbGxpbmcgdGhvc2UsIGVhY2ggZnVuY3Rpb25cbi8vIGFkdmFuY2luZyB0aGUgaW5wdXQgc3RyZWFtIGFuZCByZXR1cm5pbmcgYW4gQVNUIG5vZGUuIFByZWNlZGVuY2Vcbi8vIG9mIGNvbnN0cnVjdHMgKGZvciBleGFtcGxlLCB0aGUgZmFjdCB0aGF0IGAheFsxXWAgbWVhbnMgYCEoeFsxXSlgXG4vLyBpbnN0ZWFkIG9mIGAoIXgpWzFdYCBpcyBoYW5kbGVkIGJ5IHRoZSBmYWN0IHRoYXQgdGhlIHBhcnNlclxuLy8gZnVuY3Rpb24gdGhhdCBwYXJzZXMgdW5hcnkgcHJlZml4IG9wZXJhdG9ycyBpcyBjYWxsZWQgZmlyc3QsIGFuZFxuLy8gaW4gdHVybiBjYWxscyB0aGUgZnVuY3Rpb24gdGhhdCBwYXJzZXMgYFtdYCBzdWJzY3JpcHRzIOKAlCB0aGF0XG4vLyB3YXksIGl0J2xsIHJlY2VpdmUgdGhlIG5vZGUgZm9yIGB4WzFdYCBhbHJlYWR5IHBhcnNlZCwgYW5kIHdyYXBzXG4vLyAqdGhhdCogaW4gdGhlIHVuYXJ5IG9wZXJhdG9yIG5vZGUuXG4vL1xuLy8gQWNvcm4gdXNlcyBhbiBbb3BlcmF0b3IgcHJlY2VkZW5jZSBwYXJzZXJdW29wcF0gdG8gaGFuZGxlIGJpbmFyeVxuLy8gb3BlcmF0b3IgcHJlY2VkZW5jZSwgYmVjYXVzZSBpdCBpcyBtdWNoIG1vcmUgY29tcGFjdCB0aGFuIHVzaW5nXG4vLyB0aGUgdGVjaG5pcXVlIG91dGxpbmVkIGFib3ZlLCB3aGljaCB1c2VzIGRpZmZlcmVudCwgbmVzdGluZ1xuLy8gZnVuY3Rpb25zIHRvIHNwZWNpZnkgcHJlY2VkZW5jZSwgZm9yIGFsbCBvZiB0aGUgdGVuIGJpbmFyeVxuLy8gcHJlY2VkZW5jZSBsZXZlbHMgdGhhdCBKYXZhU2NyaXB0IGRlZmluZXMuXG4vL1xuLy8gW29wcF06IGh0dHA6Ly9lbi53aWtpcGVkaWEub3JnL3dpa2kvT3BlcmF0b3ItcHJlY2VkZW5jZV9wYXJzZXJcblxuXCJ1c2Ugc3RyaWN0XCI7XG5cbnZhciBfdG9rZW50eXBlID0gX2RlcmVxXyhcIi4vdG9rZW50eXBlXCIpO1xuXG52YXIgX3N0YXRlID0gX2RlcmVxXyhcIi4vc3RhdGVcIik7XG5cbnZhciBfaWRlbnRpZmllciA9IF9kZXJlcV8oXCIuL2lkZW50aWZpZXJcIik7XG5cbnZhciBfdXRpbCA9IF9kZXJlcV8oXCIuL3V0aWxcIik7XG5cbnZhciBwcCA9IF9zdGF0ZS5QYXJzZXIucHJvdG90eXBlO1xuXG4vLyBDaGVjayBpZiBwcm9wZXJ0eSBuYW1lIGNsYXNoZXMgd2l0aCBhbHJlYWR5IGFkZGVkLlxuLy8gT2JqZWN0L2NsYXNzIGdldHRlcnMgYW5kIHNldHRlcnMgYXJlIG5vdCBhbGxvd2VkIHRvIGNsYXNoIOKAlFxuLy8gZWl0aGVyIHdpdGggZWFjaCBvdGhlciBvciB3aXRoIGFuIGluaXQgcHJvcGVydHkg4oCUIGFuZCBpblxuLy8gc3RyaWN0IG1vZGUsIGluaXQgcHJvcGVydGllcyBhcmUgYWxzbyBub3QgYWxsb3dlZCB0byBiZSByZXBlYXRlZC5cblxucHAuY2hlY2tQcm9wQ2xhc2ggPSBmdW5jdGlvbiAocHJvcCwgcHJvcEhhc2gpIHtcbiAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2ICYmIChwcm9wLmNvbXB1dGVkIHx8IHByb3AubWV0aG9kIHx8IHByb3Auc2hvcnRoYW5kKSkgcmV0dXJuO1xuICB2YXIga2V5ID0gcHJvcC5rZXksXG4gICAgICBuYW1lID0gdW5kZWZpbmVkO1xuICBzd2l0Y2ggKGtleS50eXBlKSB7XG4gICAgY2FzZSBcIklkZW50aWZpZXJcIjpcbiAgICAgIG5hbWUgPSBrZXkubmFtZTticmVhaztcbiAgICBjYXNlIFwiTGl0ZXJhbFwiOlxuICAgICAgbmFtZSA9IFN0cmluZyhrZXkudmFsdWUpO2JyZWFrO1xuICAgIGRlZmF1bHQ6XG4gICAgICByZXR1cm47XG4gIH1cbiAgdmFyIGtpbmQgPSBwcm9wLmtpbmQ7XG4gIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNikge1xuICAgIGlmIChuYW1lID09PSBcIl9fcHJvdG9fX1wiICYmIGtpbmQgPT09IFwiaW5pdFwiKSB7XG4gICAgICBpZiAocHJvcEhhc2gucHJvdG8pIHRoaXMucmFpc2Uoa2V5LnN0YXJ0LCBcIlJlZGVmaW5pdGlvbiBvZiBfX3Byb3RvX18gcHJvcGVydHlcIik7XG4gICAgICBwcm9wSGFzaC5wcm90byA9IHRydWU7XG4gICAgfVxuICAgIHJldHVybjtcbiAgfVxuICB2YXIgb3RoZXIgPSB1bmRlZmluZWQ7XG4gIGlmIChfdXRpbC5oYXMocHJvcEhhc2gsIG5hbWUpKSB7XG4gICAgb3RoZXIgPSBwcm9wSGFzaFtuYW1lXTtcbiAgICB2YXIgaXNHZXRTZXQgPSBraW5kICE9PSBcImluaXRcIjtcbiAgICBpZiAoKHRoaXMuc3RyaWN0IHx8IGlzR2V0U2V0KSAmJiBvdGhlcltraW5kXSB8fCAhKGlzR2V0U2V0IF4gb3RoZXIuaW5pdCkpIHRoaXMucmFpc2Uoa2V5LnN0YXJ0LCBcIlJlZGVmaW5pdGlvbiBvZiBwcm9wZXJ0eVwiKTtcbiAgfSBlbHNlIHtcbiAgICBvdGhlciA9IHByb3BIYXNoW25hbWVdID0ge1xuICAgICAgaW5pdDogZmFsc2UsXG4gICAgICBnZXQ6IGZhbHNlLFxuICAgICAgc2V0OiBmYWxzZVxuICAgIH07XG4gIH1cbiAgb3RoZXJba2luZF0gPSB0cnVlO1xufTtcblxuLy8gIyMjIEV4cHJlc3Npb24gcGFyc2luZ1xuXG4vLyBUaGVzZSBuZXN0LCBmcm9tIHRoZSBtb3N0IGdlbmVyYWwgZXhwcmVzc2lvbiB0eXBlIGF0IHRoZSB0b3AgdG9cbi8vICdhdG9taWMnLCBub25kaXZpc2libGUgZXhwcmVzc2lvbiB0eXBlcyBhdCB0aGUgYm90dG9tLiBNb3N0IG9mXG4vLyB0aGUgZnVuY3Rpb25zIHdpbGwgc2ltcGx5IGxldCB0aGUgZnVuY3Rpb24ocykgYmVsb3cgdGhlbSBwYXJzZSxcbi8vIGFuZCwgKmlmKiB0aGUgc3ludGFjdGljIGNvbnN0cnVjdCB0aGV5IGhhbmRsZSBpcyBwcmVzZW50LCB3cmFwXG4vLyB0aGUgQVNUIG5vZGUgdGhhdCB0aGUgaW5uZXIgcGFyc2VyIGdhdmUgdGhlbSBpbiBhbm90aGVyIG5vZGUuXG5cbi8vIFBhcnNlIGEgZnVsbCBleHByZXNzaW9uLiBUaGUgb3B0aW9uYWwgYXJndW1lbnRzIGFyZSB1c2VkIHRvXG4vLyBmb3JiaWQgdGhlIGBpbmAgb3BlcmF0b3IgKGluIGZvciBsb29wcyBpbml0YWxpemF0aW9uIGV4cHJlc3Npb25zKVxuLy8gYW5kIHByb3ZpZGUgcmVmZXJlbmNlIGZvciBzdG9yaW5nICc9JyBvcGVyYXRvciBpbnNpZGUgc2hvcnRoYW5kXG4vLyBwcm9wZXJ0eSBhc3NpZ25tZW50IGluIGNvbnRleHRzIHdoZXJlIGJvdGggb2JqZWN0IGV4cHJlc3Npb25cbi8vIGFuZCBvYmplY3QgcGF0dGVybiBtaWdodCBhcHBlYXIgKHNvIGl0J3MgcG9zc2libGUgdG8gcmFpc2Vcbi8vIGRlbGF5ZWQgc3ludGF4IGVycm9yIGF0IGNvcnJlY3QgcG9zaXRpb24pLlxuXG5wcC5wYXJzZUV4cHJlc3Npb24gPSBmdW5jdGlvbiAobm9JbiwgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcykge1xuICB2YXIgc3RhcnRQb3MgPSB0aGlzLnN0YXJ0LFxuICAgICAgc3RhcnRMb2MgPSB0aGlzLnN0YXJ0TG9jO1xuICB2YXIgZXhwciA9IHRoaXMucGFyc2VNYXliZUFzc2lnbihub0luLCByZWZTaG9ydGhhbmREZWZhdWx0UG9zKTtcbiAgaWYgKHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5jb21tYSkge1xuICAgIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGVBdChzdGFydFBvcywgc3RhcnRMb2MpO1xuICAgIG5vZGUuZXhwcmVzc2lvbnMgPSBbZXhwcl07XG4gICAgd2hpbGUgKHRoaXMuZWF0KF90b2tlbnR5cGUudHlwZXMuY29tbWEpKSBub2RlLmV4cHJlc3Npb25zLnB1c2godGhpcy5wYXJzZU1heWJlQXNzaWduKG5vSW4sIHJlZlNob3J0aGFuZERlZmF1bHRQb3MpKTtcbiAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiU2VxdWVuY2VFeHByZXNzaW9uXCIpO1xuICB9XG4gIHJldHVybiBleHByO1xufTtcblxuLy8gUGFyc2UgYW4gYXNzaWdubWVudCBleHByZXNzaW9uLiBUaGlzIGluY2x1ZGVzIGFwcGxpY2F0aW9ucyBvZlxuLy8gb3BlcmF0b3JzIGxpa2UgYCs9YC5cblxucHAucGFyc2VNYXliZUFzc2lnbiA9IGZ1bmN0aW9uIChub0luLCByZWZTaG9ydGhhbmREZWZhdWx0UG9zLCBhZnRlckxlZnRQYXJzZSkge1xuICBpZiAodGhpcy50eXBlID09IF90b2tlbnR5cGUudHlwZXMuX3lpZWxkICYmIHRoaXMuaW5HZW5lcmF0b3IpIHJldHVybiB0aGlzLnBhcnNlWWllbGQoKTtcblxuICB2YXIgZmFpbE9uU2hvcnRoYW5kQXNzaWduID0gdW5kZWZpbmVkO1xuICBpZiAoIXJlZlNob3J0aGFuZERlZmF1bHRQb3MpIHtcbiAgICByZWZTaG9ydGhhbmREZWZhdWx0UG9zID0geyBzdGFydDogMCB9O1xuICAgIGZhaWxPblNob3J0aGFuZEFzc2lnbiA9IHRydWU7XG4gIH0gZWxzZSB7XG4gICAgZmFpbE9uU2hvcnRoYW5kQXNzaWduID0gZmFsc2U7XG4gIH1cbiAgdmFyIHN0YXJ0UG9zID0gdGhpcy5zdGFydCxcbiAgICAgIHN0YXJ0TG9jID0gdGhpcy5zdGFydExvYztcbiAgaWYgKHRoaXMudHlwZSA9PSBfdG9rZW50eXBlLnR5cGVzLnBhcmVuTCB8fCB0aGlzLnR5cGUgPT0gX3Rva2VudHlwZS50eXBlcy5uYW1lKSB0aGlzLnBvdGVudGlhbEFycm93QXQgPSB0aGlzLnN0YXJ0O1xuICB2YXIgbGVmdCA9IHRoaXMucGFyc2VNYXliZUNvbmRpdGlvbmFsKG5vSW4sIHJlZlNob3J0aGFuZERlZmF1bHRQb3MpO1xuICBpZiAoYWZ0ZXJMZWZ0UGFyc2UpIGxlZnQgPSBhZnRlckxlZnRQYXJzZS5jYWxsKHRoaXMsIGxlZnQsIHN0YXJ0UG9zLCBzdGFydExvYyk7XG4gIGlmICh0aGlzLnR5cGUuaXNBc3NpZ24pIHtcbiAgICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlQXQoc3RhcnRQb3MsIHN0YXJ0TG9jKTtcbiAgICBub2RlLm9wZXJhdG9yID0gdGhpcy52YWx1ZTtcbiAgICBub2RlLmxlZnQgPSB0aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuZXEgPyB0aGlzLnRvQXNzaWduYWJsZShsZWZ0KSA6IGxlZnQ7XG4gICAgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcy5zdGFydCA9IDA7IC8vIHJlc2V0IGJlY2F1c2Ugc2hvcnRoYW5kIGRlZmF1bHQgd2FzIHVzZWQgY29ycmVjdGx5XG4gICAgdGhpcy5jaGVja0xWYWwobGVmdCk7XG4gICAgdGhpcy5uZXh0KCk7XG4gICAgbm9kZS5yaWdodCA9IHRoaXMucGFyc2VNYXliZUFzc2lnbihub0luKTtcbiAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiQXNzaWdubWVudEV4cHJlc3Npb25cIik7XG4gIH0gZWxzZSBpZiAoZmFpbE9uU2hvcnRoYW5kQXNzaWduICYmIHJlZlNob3J0aGFuZERlZmF1bHRQb3Muc3RhcnQpIHtcbiAgICB0aGlzLnVuZXhwZWN0ZWQocmVmU2hvcnRoYW5kRGVmYXVsdFBvcy5zdGFydCk7XG4gIH1cbiAgcmV0dXJuIGxlZnQ7XG59O1xuXG4vLyBQYXJzZSBhIHRlcm5hcnkgY29uZGl0aW9uYWwgKGA/OmApIG9wZXJhdG9yLlxuXG5wcC5wYXJzZU1heWJlQ29uZGl0aW9uYWwgPSBmdW5jdGlvbiAobm9JbiwgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcykge1xuICB2YXIgc3RhcnRQb3MgPSB0aGlzLnN0YXJ0LFxuICAgICAgc3RhcnRMb2MgPSB0aGlzLnN0YXJ0TG9jO1xuICB2YXIgZXhwciA9IHRoaXMucGFyc2VFeHByT3BzKG5vSW4sIHJlZlNob3J0aGFuZERlZmF1bHRQb3MpO1xuICBpZiAocmVmU2hvcnRoYW5kRGVmYXVsdFBvcyAmJiByZWZTaG9ydGhhbmREZWZhdWx0UG9zLnN0YXJ0KSByZXR1cm4gZXhwcjtcbiAgaWYgKHRoaXMuZWF0KF90b2tlbnR5cGUudHlwZXMucXVlc3Rpb24pKSB7XG4gICAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0UG9zLCBzdGFydExvYyk7XG4gICAgbm9kZS50ZXN0ID0gZXhwcjtcbiAgICBub2RlLmNvbnNlcXVlbnQgPSB0aGlzLnBhcnNlTWF5YmVBc3NpZ24oKTtcbiAgICB0aGlzLmV4cGVjdChfdG9rZW50eXBlLnR5cGVzLmNvbG9uKTtcbiAgICBub2RlLmFsdGVybmF0ZSA9IHRoaXMucGFyc2VNYXliZUFzc2lnbihub0luKTtcbiAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiQ29uZGl0aW9uYWxFeHByZXNzaW9uXCIpO1xuICB9XG4gIHJldHVybiBleHByO1xufTtcblxuLy8gU3RhcnQgdGhlIHByZWNlZGVuY2UgcGFyc2VyLlxuXG5wcC5wYXJzZUV4cHJPcHMgPSBmdW5jdGlvbiAobm9JbiwgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcykge1xuICB2YXIgc3RhcnRQb3MgPSB0aGlzLnN0YXJ0LFxuICAgICAgc3RhcnRMb2MgPSB0aGlzLnN0YXJ0TG9jO1xuICB2YXIgZXhwciA9IHRoaXMucGFyc2VNYXliZVVuYXJ5KHJlZlNob3J0aGFuZERlZmF1bHRQb3MpO1xuICBpZiAocmVmU2hvcnRoYW5kRGVmYXVsdFBvcyAmJiByZWZTaG9ydGhhbmREZWZhdWx0UG9zLnN0YXJ0KSByZXR1cm4gZXhwcjtcbiAgcmV0dXJuIHRoaXMucGFyc2VFeHByT3AoZXhwciwgc3RhcnRQb3MsIHN0YXJ0TG9jLCAtMSwgbm9Jbik7XG59O1xuXG4vLyBQYXJzZSBiaW5hcnkgb3BlcmF0b3JzIHdpdGggdGhlIG9wZXJhdG9yIHByZWNlZGVuY2UgcGFyc2luZ1xuLy8gYWxnb3JpdGhtLiBgbGVmdGAgaXMgdGhlIGxlZnQtaGFuZCBzaWRlIG9mIHRoZSBvcGVyYXRvci5cbi8vIGBtaW5QcmVjYCBwcm92aWRlcyBjb250ZXh0IHRoYXQgYWxsb3dzIHRoZSBmdW5jdGlvbiB0byBzdG9wIGFuZFxuLy8gZGVmZXIgZnVydGhlciBwYXJzZXIgdG8gb25lIG9mIGl0cyBjYWxsZXJzIHdoZW4gaXQgZW5jb3VudGVycyBhblxuLy8gb3BlcmF0b3IgdGhhdCBoYXMgYSBsb3dlciBwcmVjZWRlbmNlIHRoYW4gdGhlIHNldCBpdCBpcyBwYXJzaW5nLlxuXG5wcC5wYXJzZUV4cHJPcCA9IGZ1bmN0aW9uIChsZWZ0LCBsZWZ0U3RhcnRQb3MsIGxlZnRTdGFydExvYywgbWluUHJlYywgbm9Jbikge1xuICB2YXIgcHJlYyA9IHRoaXMudHlwZS5iaW5vcDtcbiAgaWYgKHByZWMgIT0gbnVsbCAmJiAoIW5vSW4gfHwgdGhpcy50eXBlICE9PSBfdG9rZW50eXBlLnR5cGVzLl9pbikpIHtcbiAgICBpZiAocHJlYyA+IG1pblByZWMpIHtcbiAgICAgIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGVBdChsZWZ0U3RhcnRQb3MsIGxlZnRTdGFydExvYyk7XG4gICAgICBub2RlLmxlZnQgPSBsZWZ0O1xuICAgICAgbm9kZS5vcGVyYXRvciA9IHRoaXMudmFsdWU7XG4gICAgICB2YXIgb3AgPSB0aGlzLnR5cGU7XG4gICAgICB0aGlzLm5leHQoKTtcbiAgICAgIHZhciBzdGFydFBvcyA9IHRoaXMuc3RhcnQsXG4gICAgICAgICAgc3RhcnRMb2MgPSB0aGlzLnN0YXJ0TG9jO1xuICAgICAgbm9kZS5yaWdodCA9IHRoaXMucGFyc2VFeHByT3AodGhpcy5wYXJzZU1heWJlVW5hcnkoKSwgc3RhcnRQb3MsIHN0YXJ0TG9jLCBwcmVjLCBub0luKTtcbiAgICAgIHRoaXMuZmluaXNoTm9kZShub2RlLCBvcCA9PT0gX3Rva2VudHlwZS50eXBlcy5sb2dpY2FsT1IgfHwgb3AgPT09IF90b2tlbnR5cGUudHlwZXMubG9naWNhbEFORCA/IFwiTG9naWNhbEV4cHJlc3Npb25cIiA6IFwiQmluYXJ5RXhwcmVzc2lvblwiKTtcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlRXhwck9wKG5vZGUsIGxlZnRTdGFydFBvcywgbGVmdFN0YXJ0TG9jLCBtaW5QcmVjLCBub0luKTtcbiAgICB9XG4gIH1cbiAgcmV0dXJuIGxlZnQ7XG59O1xuXG4vLyBQYXJzZSB1bmFyeSBvcGVyYXRvcnMsIGJvdGggcHJlZml4IGFuZCBwb3N0Zml4LlxuXG5wcC5wYXJzZU1heWJlVW5hcnkgPSBmdW5jdGlvbiAocmVmU2hvcnRoYW5kRGVmYXVsdFBvcykge1xuICBpZiAodGhpcy50eXBlLnByZWZpeCkge1xuICAgIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGUoKSxcbiAgICAgICAgdXBkYXRlID0gdGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLmluY0RlYztcbiAgICBub2RlLm9wZXJhdG9yID0gdGhpcy52YWx1ZTtcbiAgICBub2RlLnByZWZpeCA9IHRydWU7XG4gICAgdGhpcy5uZXh0KCk7XG4gICAgbm9kZS5hcmd1bWVudCA9IHRoaXMucGFyc2VNYXliZVVuYXJ5KCk7XG4gICAgaWYgKHJlZlNob3J0aGFuZERlZmF1bHRQb3MgJiYgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcy5zdGFydCkgdGhpcy51bmV4cGVjdGVkKHJlZlNob3J0aGFuZERlZmF1bHRQb3Muc3RhcnQpO1xuICAgIGlmICh1cGRhdGUpIHRoaXMuY2hlY2tMVmFsKG5vZGUuYXJndW1lbnQpO2Vsc2UgaWYgKHRoaXMuc3RyaWN0ICYmIG5vZGUub3BlcmF0b3IgPT09IFwiZGVsZXRlXCIgJiYgbm9kZS5hcmd1bWVudC50eXBlID09PSBcIklkZW50aWZpZXJcIikgdGhpcy5yYWlzZShub2RlLnN0YXJ0LCBcIkRlbGV0aW5nIGxvY2FsIHZhcmlhYmxlIGluIHN0cmljdCBtb2RlXCIpO1xuICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgdXBkYXRlID8gXCJVcGRhdGVFeHByZXNzaW9uXCIgOiBcIlVuYXJ5RXhwcmVzc2lvblwiKTtcbiAgfVxuICB2YXIgc3RhcnRQb3MgPSB0aGlzLnN0YXJ0LFxuICAgICAgc3RhcnRMb2MgPSB0aGlzLnN0YXJ0TG9jO1xuICB2YXIgZXhwciA9IHRoaXMucGFyc2VFeHByU3Vic2NyaXB0cyhyZWZTaG9ydGhhbmREZWZhdWx0UG9zKTtcbiAgaWYgKHJlZlNob3J0aGFuZERlZmF1bHRQb3MgJiYgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcy5zdGFydCkgcmV0dXJuIGV4cHI7XG4gIHdoaWxlICh0aGlzLnR5cGUucG9zdGZpeCAmJiAhdGhpcy5jYW5JbnNlcnRTZW1pY29sb24oKSkge1xuICAgIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGVBdChzdGFydFBvcywgc3RhcnRMb2MpO1xuICAgIG5vZGUub3BlcmF0b3IgPSB0aGlzLnZhbHVlO1xuICAgIG5vZGUucHJlZml4ID0gZmFsc2U7XG4gICAgbm9kZS5hcmd1bWVudCA9IGV4cHI7XG4gICAgdGhpcy5jaGVja0xWYWwoZXhwcik7XG4gICAgdGhpcy5uZXh0KCk7XG4gICAgZXhwciA9IHRoaXMuZmluaXNoTm9kZShub2RlLCBcIlVwZGF0ZUV4cHJlc3Npb25cIik7XG4gIH1cbiAgcmV0dXJuIGV4cHI7XG59O1xuXG4vLyBQYXJzZSBjYWxsLCBkb3QsIGFuZCBgW11gLXN1YnNjcmlwdCBleHByZXNzaW9ucy5cblxucHAucGFyc2VFeHByU3Vic2NyaXB0cyA9IGZ1bmN0aW9uIChyZWZTaG9ydGhhbmREZWZhdWx0UG9zKSB7XG4gIHZhciBzdGFydFBvcyA9IHRoaXMuc3RhcnQsXG4gICAgICBzdGFydExvYyA9IHRoaXMuc3RhcnRMb2M7XG4gIHZhciBleHByID0gdGhpcy5wYXJzZUV4cHJBdG9tKHJlZlNob3J0aGFuZERlZmF1bHRQb3MpO1xuICBpZiAocmVmU2hvcnRoYW5kRGVmYXVsdFBvcyAmJiByZWZTaG9ydGhhbmREZWZhdWx0UG9zLnN0YXJ0KSByZXR1cm4gZXhwcjtcbiAgcmV0dXJuIHRoaXMucGFyc2VTdWJzY3JpcHRzKGV4cHIsIHN0YXJ0UG9zLCBzdGFydExvYyk7XG59O1xuXG5wcC5wYXJzZVN1YnNjcmlwdHMgPSBmdW5jdGlvbiAoYmFzZSwgc3RhcnRQb3MsIHN0YXJ0TG9jLCBub0NhbGxzKSB7XG4gIGZvciAoOzspIHtcbiAgICBpZiAodGhpcy5lYXQoX3Rva2VudHlwZS50eXBlcy5kb3QpKSB7XG4gICAgICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlQXQoc3RhcnRQb3MsIHN0YXJ0TG9jKTtcbiAgICAgIG5vZGUub2JqZWN0ID0gYmFzZTtcbiAgICAgIG5vZGUucHJvcGVydHkgPSB0aGlzLnBhcnNlSWRlbnQodHJ1ZSk7XG4gICAgICBub2RlLmNvbXB1dGVkID0gZmFsc2U7XG4gICAgICBiYXNlID0gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiTWVtYmVyRXhwcmVzc2lvblwiKTtcbiAgICB9IGVsc2UgaWYgKHRoaXMuZWF0KF90b2tlbnR5cGUudHlwZXMuYnJhY2tldEwpKSB7XG4gICAgICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlQXQoc3RhcnRQb3MsIHN0YXJ0TG9jKTtcbiAgICAgIG5vZGUub2JqZWN0ID0gYmFzZTtcbiAgICAgIG5vZGUucHJvcGVydHkgPSB0aGlzLnBhcnNlRXhwcmVzc2lvbigpO1xuICAgICAgbm9kZS5jb21wdXRlZCA9IHRydWU7XG4gICAgICB0aGlzLmV4cGVjdChfdG9rZW50eXBlLnR5cGVzLmJyYWNrZXRSKTtcbiAgICAgIGJhc2UgPSB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJNZW1iZXJFeHByZXNzaW9uXCIpO1xuICAgIH0gZWxzZSBpZiAoIW5vQ2FsbHMgJiYgdGhpcy5lYXQoX3Rva2VudHlwZS50eXBlcy5wYXJlbkwpKSB7XG4gICAgICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlQXQoc3RhcnRQb3MsIHN0YXJ0TG9jKTtcbiAgICAgIG5vZGUuY2FsbGVlID0gYmFzZTtcbiAgICAgIG5vZGUuYXJndW1lbnRzID0gdGhpcy5wYXJzZUV4cHJMaXN0KF90b2tlbnR5cGUudHlwZXMucGFyZW5SLCBmYWxzZSk7XG4gICAgICBiYXNlID0gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiQ2FsbEV4cHJlc3Npb25cIik7XG4gICAgfSBlbHNlIGlmICh0aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuYmFja1F1b3RlKSB7XG4gICAgICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlQXQoc3RhcnRQb3MsIHN0YXJ0TG9jKTtcbiAgICAgIG5vZGUudGFnID0gYmFzZTtcbiAgICAgIG5vZGUucXVhc2kgPSB0aGlzLnBhcnNlVGVtcGxhdGUoKTtcbiAgICAgIGJhc2UgPSB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJUYWdnZWRUZW1wbGF0ZUV4cHJlc3Npb25cIik7XG4gICAgfSBlbHNlIHtcbiAgICAgIHJldHVybiBiYXNlO1xuICAgIH1cbiAgfVxufTtcblxuLy8gUGFyc2UgYW4gYXRvbWljIGV4cHJlc3Npb24g4oCUIGVpdGhlciBhIHNpbmdsZSB0b2tlbiB0aGF0IGlzIGFuXG4vLyBleHByZXNzaW9uLCBhbiBleHByZXNzaW9uIHN0YXJ0ZWQgYnkgYSBrZXl3b3JkIGxpa2UgYGZ1bmN0aW9uYCBvclxuLy8gYG5ld2AsIG9yIGFuIGV4cHJlc3Npb24gd3JhcHBlZCBpbiBwdW5jdHVhdGlvbiBsaWtlIGAoKWAsIGBbXWAsXG4vLyBvciBge31gLlxuXG5wcC5wYXJzZUV4cHJBdG9tID0gZnVuY3Rpb24gKHJlZlNob3J0aGFuZERlZmF1bHRQb3MpIHtcbiAgdmFyIG5vZGUgPSB1bmRlZmluZWQsXG4gICAgICBjYW5CZUFycm93ID0gdGhpcy5wb3RlbnRpYWxBcnJvd0F0ID09IHRoaXMuc3RhcnQ7XG4gIHN3aXRjaCAodGhpcy50eXBlKSB7XG4gICAgY2FzZSBfdG9rZW50eXBlLnR5cGVzLl9zdXBlcjpcbiAgICAgIGlmICghdGhpcy5pbkZ1bmN0aW9uKSB0aGlzLnJhaXNlKHRoaXMuc3RhcnQsIFwiJ3N1cGVyJyBvdXRzaWRlIG9mIGZ1bmN0aW9uIG9yIGNsYXNzXCIpO1xuICAgIGNhc2UgX3Rva2VudHlwZS50eXBlcy5fdGhpczpcbiAgICAgIHZhciB0eXBlID0gdGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLl90aGlzID8gXCJUaGlzRXhwcmVzc2lvblwiIDogXCJTdXBlclwiO1xuICAgICAgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gICAgICB0aGlzLm5leHQoKTtcbiAgICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgdHlwZSk7XG5cbiAgICBjYXNlIF90b2tlbnR5cGUudHlwZXMuX3lpZWxkOlxuICAgICAgaWYgKHRoaXMuaW5HZW5lcmF0b3IpIHRoaXMudW5leHBlY3RlZCgpO1xuXG4gICAgY2FzZSBfdG9rZW50eXBlLnR5cGVzLm5hbWU6XG4gICAgICB2YXIgc3RhcnRQb3MgPSB0aGlzLnN0YXJ0LFxuICAgICAgICAgIHN0YXJ0TG9jID0gdGhpcy5zdGFydExvYztcbiAgICAgIHZhciBpZCA9IHRoaXMucGFyc2VJZGVudCh0aGlzLnR5cGUgIT09IF90b2tlbnR5cGUudHlwZXMubmFtZSk7XG4gICAgICBpZiAoY2FuQmVBcnJvdyAmJiAhdGhpcy5jYW5JbnNlcnRTZW1pY29sb24oKSAmJiB0aGlzLmVhdChfdG9rZW50eXBlLnR5cGVzLmFycm93KSkgcmV0dXJuIHRoaXMucGFyc2VBcnJvd0V4cHJlc3Npb24odGhpcy5zdGFydE5vZGVBdChzdGFydFBvcywgc3RhcnRMb2MpLCBbaWRdKTtcbiAgICAgIHJldHVybiBpZDtcblxuICAgIGNhc2UgX3Rva2VudHlwZS50eXBlcy5yZWdleHA6XG4gICAgICB2YXIgdmFsdWUgPSB0aGlzLnZhbHVlO1xuICAgICAgbm9kZSA9IHRoaXMucGFyc2VMaXRlcmFsKHZhbHVlLnZhbHVlKTtcbiAgICAgIG5vZGUucmVnZXggPSB7IHBhdHRlcm46IHZhbHVlLnBhdHRlcm4sIGZsYWdzOiB2YWx1ZS5mbGFncyB9O1xuICAgICAgcmV0dXJuIG5vZGU7XG5cbiAgICBjYXNlIF90b2tlbnR5cGUudHlwZXMubnVtOmNhc2UgX3Rva2VudHlwZS50eXBlcy5zdHJpbmc6XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZUxpdGVyYWwodGhpcy52YWx1ZSk7XG5cbiAgICBjYXNlIF90b2tlbnR5cGUudHlwZXMuX251bGw6Y2FzZSBfdG9rZW50eXBlLnR5cGVzLl90cnVlOmNhc2UgX3Rva2VudHlwZS50eXBlcy5fZmFsc2U6XG4gICAgICBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgICAgIG5vZGUudmFsdWUgPSB0aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuX251bGwgPyBudWxsIDogdGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLl90cnVlO1xuICAgICAgbm9kZS5yYXcgPSB0aGlzLnR5cGUua2V5d29yZDtcbiAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkxpdGVyYWxcIik7XG5cbiAgICBjYXNlIF90b2tlbnR5cGUudHlwZXMucGFyZW5MOlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VQYXJlbkFuZERpc3Rpbmd1aXNoRXhwcmVzc2lvbihjYW5CZUFycm93KTtcblxuICAgIGNhc2UgX3Rva2VudHlwZS50eXBlcy5icmFja2V0TDpcbiAgICAgIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICAvLyBjaGVjayB3aGV0aGVyIHRoaXMgaXMgYXJyYXkgY29tcHJlaGVuc2lvbiBvciByZWd1bGFyIGFycmF5XG4gICAgICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDcgJiYgdGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLl9mb3IpIHtcbiAgICAgICAgcmV0dXJuIHRoaXMucGFyc2VDb21wcmVoZW5zaW9uKG5vZGUsIGZhbHNlKTtcbiAgICAgIH1cbiAgICAgIG5vZGUuZWxlbWVudHMgPSB0aGlzLnBhcnNlRXhwckxpc3QoX3Rva2VudHlwZS50eXBlcy5icmFja2V0UiwgdHJ1ZSwgdHJ1ZSwgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcyk7XG4gICAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiQXJyYXlFeHByZXNzaW9uXCIpO1xuXG4gICAgY2FzZSBfdG9rZW50eXBlLnR5cGVzLmJyYWNlTDpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlT2JqKGZhbHNlLCByZWZTaG9ydGhhbmREZWZhdWx0UG9zKTtcblxuICAgIGNhc2UgX3Rva2VudHlwZS50eXBlcy5fZnVuY3Rpb246XG4gICAgICBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgcmV0dXJuIHRoaXMucGFyc2VGdW5jdGlvbihub2RlLCBmYWxzZSk7XG5cbiAgICBjYXNlIF90b2tlbnR5cGUudHlwZXMuX2NsYXNzOlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VDbGFzcyh0aGlzLnN0YXJ0Tm9kZSgpLCBmYWxzZSk7XG5cbiAgICBjYXNlIF90b2tlbnR5cGUudHlwZXMuX25ldzpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlTmV3KCk7XG5cbiAgICBjYXNlIF90b2tlbnR5cGUudHlwZXMuYmFja1F1b3RlOlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VUZW1wbGF0ZSgpO1xuXG4gICAgZGVmYXVsdDpcbiAgICAgIHRoaXMudW5leHBlY3RlZCgpO1xuICB9XG59O1xuXG5wcC5wYXJzZUxpdGVyYWwgPSBmdW5jdGlvbiAodmFsdWUpIHtcbiAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICBub2RlLnZhbHVlID0gdmFsdWU7XG4gIG5vZGUucmF3ID0gdGhpcy5pbnB1dC5zbGljZSh0aGlzLnN0YXJ0LCB0aGlzLmVuZCk7XG4gIHRoaXMubmV4dCgpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiTGl0ZXJhbFwiKTtcbn07XG5cbnBwLnBhcnNlUGFyZW5FeHByZXNzaW9uID0gZnVuY3Rpb24gKCkge1xuICB0aGlzLmV4cGVjdChfdG9rZW50eXBlLnR5cGVzLnBhcmVuTCk7XG4gIHZhciB2YWwgPSB0aGlzLnBhcnNlRXhwcmVzc2lvbigpO1xuICB0aGlzLmV4cGVjdChfdG9rZW50eXBlLnR5cGVzLnBhcmVuUik7XG4gIHJldHVybiB2YWw7XG59O1xuXG5wcC5wYXJzZVBhcmVuQW5kRGlzdGluZ3Vpc2hFeHByZXNzaW9uID0gZnVuY3Rpb24gKGNhbkJlQXJyb3cpIHtcbiAgdmFyIHN0YXJ0UG9zID0gdGhpcy5zdGFydCxcbiAgICAgIHN0YXJ0TG9jID0gdGhpcy5zdGFydExvYyxcbiAgICAgIHZhbCA9IHVuZGVmaW5lZDtcbiAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KSB7XG4gICAgdGhpcy5uZXh0KCk7XG5cbiAgICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDcgJiYgdGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLl9mb3IpIHtcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlQ29tcHJlaGVuc2lvbih0aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0UG9zLCBzdGFydExvYyksIHRydWUpO1xuICAgIH1cblxuICAgIHZhciBpbm5lclN0YXJ0UG9zID0gdGhpcy5zdGFydCxcbiAgICAgICAgaW5uZXJTdGFydExvYyA9IHRoaXMuc3RhcnRMb2M7XG4gICAgdmFyIGV4cHJMaXN0ID0gW10sXG4gICAgICAgIGZpcnN0ID0gdHJ1ZTtcbiAgICB2YXIgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcyA9IHsgc3RhcnQ6IDAgfSxcbiAgICAgICAgc3ByZWFkU3RhcnQgPSB1bmRlZmluZWQsXG4gICAgICAgIGlubmVyUGFyZW5TdGFydCA9IHVuZGVmaW5lZDtcbiAgICB3aGlsZSAodGhpcy50eXBlICE9PSBfdG9rZW50eXBlLnR5cGVzLnBhcmVuUikge1xuICAgICAgZmlyc3QgPyBmaXJzdCA9IGZhbHNlIDogdGhpcy5leHBlY3QoX3Rva2VudHlwZS50eXBlcy5jb21tYSk7XG4gICAgICBpZiAodGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLmVsbGlwc2lzKSB7XG4gICAgICAgIHNwcmVhZFN0YXJ0ID0gdGhpcy5zdGFydDtcbiAgICAgICAgZXhwckxpc3QucHVzaCh0aGlzLnBhcnNlUGFyZW5JdGVtKHRoaXMucGFyc2VSZXN0KCkpKTtcbiAgICAgICAgYnJlYWs7XG4gICAgICB9IGVsc2Uge1xuICAgICAgICBpZiAodGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLnBhcmVuTCAmJiAhaW5uZXJQYXJlblN0YXJ0KSB7XG4gICAgICAgICAgaW5uZXJQYXJlblN0YXJ0ID0gdGhpcy5zdGFydDtcbiAgICAgICAgfVxuICAgICAgICBleHByTGlzdC5wdXNoKHRoaXMucGFyc2VNYXliZUFzc2lnbihmYWxzZSwgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcywgdGhpcy5wYXJzZVBhcmVuSXRlbSkpO1xuICAgICAgfVxuICAgIH1cbiAgICB2YXIgaW5uZXJFbmRQb3MgPSB0aGlzLnN0YXJ0LFxuICAgICAgICBpbm5lckVuZExvYyA9IHRoaXMuc3RhcnRMb2M7XG4gICAgdGhpcy5leHBlY3QoX3Rva2VudHlwZS50eXBlcy5wYXJlblIpO1xuXG4gICAgaWYgKGNhbkJlQXJyb3cgJiYgIXRoaXMuY2FuSW5zZXJ0U2VtaWNvbG9uKCkgJiYgdGhpcy5lYXQoX3Rva2VudHlwZS50eXBlcy5hcnJvdykpIHtcbiAgICAgIGlmIChpbm5lclBhcmVuU3RhcnQpIHRoaXMudW5leHBlY3RlZChpbm5lclBhcmVuU3RhcnQpO1xuICAgICAgcmV0dXJuIHRoaXMucGFyc2VQYXJlbkFycm93TGlzdChzdGFydFBvcywgc3RhcnRMb2MsIGV4cHJMaXN0KTtcbiAgICB9XG5cbiAgICBpZiAoIWV4cHJMaXN0Lmxlbmd0aCkgdGhpcy51bmV4cGVjdGVkKHRoaXMubGFzdFRva1N0YXJ0KTtcbiAgICBpZiAoc3ByZWFkU3RhcnQpIHRoaXMudW5leHBlY3RlZChzcHJlYWRTdGFydCk7XG4gICAgaWYgKHJlZlNob3J0aGFuZERlZmF1bHRQb3Muc3RhcnQpIHRoaXMudW5leHBlY3RlZChyZWZTaG9ydGhhbmREZWZhdWx0UG9zLnN0YXJ0KTtcblxuICAgIGlmIChleHByTGlzdC5sZW5ndGggPiAxKSB7XG4gICAgICB2YWwgPSB0aGlzLnN0YXJ0Tm9kZUF0KGlubmVyU3RhcnRQb3MsIGlubmVyU3RhcnRMb2MpO1xuICAgICAgdmFsLmV4cHJlc3Npb25zID0gZXhwckxpc3Q7XG4gICAgICB0aGlzLmZpbmlzaE5vZGVBdCh2YWwsIFwiU2VxdWVuY2VFeHByZXNzaW9uXCIsIGlubmVyRW5kUG9zLCBpbm5lckVuZExvYyk7XG4gICAgfSBlbHNlIHtcbiAgICAgIHZhbCA9IGV4cHJMaXN0WzBdO1xuICAgIH1cbiAgfSBlbHNlIHtcbiAgICB2YWwgPSB0aGlzLnBhcnNlUGFyZW5FeHByZXNzaW9uKCk7XG4gIH1cblxuICBpZiAodGhpcy5vcHRpb25zLnByZXNlcnZlUGFyZW5zKSB7XG4gICAgdmFyIHBhciA9IHRoaXMuc3RhcnROb2RlQXQoc3RhcnRQb3MsIHN0YXJ0TG9jKTtcbiAgICBwYXIuZXhwcmVzc2lvbiA9IHZhbDtcbiAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKHBhciwgXCJQYXJlbnRoZXNpemVkRXhwcmVzc2lvblwiKTtcbiAgfSBlbHNlIHtcbiAgICByZXR1cm4gdmFsO1xuICB9XG59O1xuXG5wcC5wYXJzZVBhcmVuSXRlbSA9IGZ1bmN0aW9uIChpdGVtKSB7XG4gIHJldHVybiBpdGVtO1xufTtcblxucHAucGFyc2VQYXJlbkFycm93TGlzdCA9IGZ1bmN0aW9uIChzdGFydFBvcywgc3RhcnRMb2MsIGV4cHJMaXN0KSB7XG4gIHJldHVybiB0aGlzLnBhcnNlQXJyb3dFeHByZXNzaW9uKHRoaXMuc3RhcnROb2RlQXQoc3RhcnRQb3MsIHN0YXJ0TG9jKSwgZXhwckxpc3QpO1xufTtcblxuLy8gTmV3J3MgcHJlY2VkZW5jZSBpcyBzbGlnaHRseSB0cmlja3kuIEl0IG11c3QgYWxsb3cgaXRzIGFyZ3VtZW50XG4vLyB0byBiZSBhIGBbXWAgb3IgZG90IHN1YnNjcmlwdCBleHByZXNzaW9uLCBidXQgbm90IGEgY2FsbCDigJQgYXRcbi8vIGxlYXN0LCBub3Qgd2l0aG91dCB3cmFwcGluZyBpdCBpbiBwYXJlbnRoZXNlcy4gVGh1cywgaXQgdXNlcyB0aGVcblxudmFyIGVtcHR5ID0gW107XG5cbnBwLnBhcnNlTmV3ID0gZnVuY3Rpb24gKCkge1xuICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gIHZhciBtZXRhID0gdGhpcy5wYXJzZUlkZW50KHRydWUpO1xuICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYgJiYgdGhpcy5lYXQoX3Rva2VudHlwZS50eXBlcy5kb3QpKSB7XG4gICAgbm9kZS5tZXRhID0gbWV0YTtcbiAgICBub2RlLnByb3BlcnR5ID0gdGhpcy5wYXJzZUlkZW50KHRydWUpO1xuICAgIGlmIChub2RlLnByb3BlcnR5Lm5hbWUgIT09IFwidGFyZ2V0XCIpIHRoaXMucmFpc2Uobm9kZS5wcm9wZXJ0eS5zdGFydCwgXCJUaGUgb25seSB2YWxpZCBtZXRhIHByb3BlcnR5IGZvciBuZXcgaXMgbmV3LnRhcmdldFwiKTtcbiAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiTWV0YVByb3BlcnR5XCIpO1xuICB9XG4gIHZhciBzdGFydFBvcyA9IHRoaXMuc3RhcnQsXG4gICAgICBzdGFydExvYyA9IHRoaXMuc3RhcnRMb2M7XG4gIG5vZGUuY2FsbGVlID0gdGhpcy5wYXJzZVN1YnNjcmlwdHModGhpcy5wYXJzZUV4cHJBdG9tKCksIHN0YXJ0UG9zLCBzdGFydExvYywgdHJ1ZSk7XG4gIGlmICh0aGlzLmVhdChfdG9rZW50eXBlLnR5cGVzLnBhcmVuTCkpIG5vZGUuYXJndW1lbnRzID0gdGhpcy5wYXJzZUV4cHJMaXN0KF90b2tlbnR5cGUudHlwZXMucGFyZW5SLCBmYWxzZSk7ZWxzZSBub2RlLmFyZ3VtZW50cyA9IGVtcHR5O1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiTmV3RXhwcmVzc2lvblwiKTtcbn07XG5cbi8vIFBhcnNlIHRlbXBsYXRlIGV4cHJlc3Npb24uXG5cbnBwLnBhcnNlVGVtcGxhdGVFbGVtZW50ID0gZnVuY3Rpb24gKCkge1xuICB2YXIgZWxlbSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gIGVsZW0udmFsdWUgPSB7XG4gICAgcmF3OiB0aGlzLmlucHV0LnNsaWNlKHRoaXMuc3RhcnQsIHRoaXMuZW5kKS5yZXBsYWNlKC9cXHJcXG4/L2csIFwiXFxuXCIpLFxuICAgIGNvb2tlZDogdGhpcy52YWx1ZVxuICB9O1xuICB0aGlzLm5leHQoKTtcbiAgZWxlbS50YWlsID0gdGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLmJhY2tRdW90ZTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShlbGVtLCBcIlRlbXBsYXRlRWxlbWVudFwiKTtcbn07XG5cbnBwLnBhcnNlVGVtcGxhdGUgPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgdGhpcy5uZXh0KCk7XG4gIG5vZGUuZXhwcmVzc2lvbnMgPSBbXTtcbiAgdmFyIGN1ckVsdCA9IHRoaXMucGFyc2VUZW1wbGF0ZUVsZW1lbnQoKTtcbiAgbm9kZS5xdWFzaXMgPSBbY3VyRWx0XTtcbiAgd2hpbGUgKCFjdXJFbHQudGFpbCkge1xuICAgIHRoaXMuZXhwZWN0KF90b2tlbnR5cGUudHlwZXMuZG9sbGFyQnJhY2VMKTtcbiAgICBub2RlLmV4cHJlc3Npb25zLnB1c2godGhpcy5wYXJzZUV4cHJlc3Npb24oKSk7XG4gICAgdGhpcy5leHBlY3QoX3Rva2VudHlwZS50eXBlcy5icmFjZVIpO1xuICAgIG5vZGUucXVhc2lzLnB1c2goY3VyRWx0ID0gdGhpcy5wYXJzZVRlbXBsYXRlRWxlbWVudCgpKTtcbiAgfVxuICB0aGlzLm5leHQoKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIlRlbXBsYXRlTGl0ZXJhbFwiKTtcbn07XG5cbi8vIFBhcnNlIGFuIG9iamVjdCBsaXRlcmFsIG9yIGJpbmRpbmcgcGF0dGVybi5cblxucHAucGFyc2VPYmogPSBmdW5jdGlvbiAoaXNQYXR0ZXJuLCByZWZTaG9ydGhhbmREZWZhdWx0UG9zKSB7XG4gIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGUoKSxcbiAgICAgIGZpcnN0ID0gdHJ1ZSxcbiAgICAgIHByb3BIYXNoID0ge307XG4gIG5vZGUucHJvcGVydGllcyA9IFtdO1xuICB0aGlzLm5leHQoKTtcbiAgd2hpbGUgKCF0aGlzLmVhdChfdG9rZW50eXBlLnR5cGVzLmJyYWNlUikpIHtcbiAgICBpZiAoIWZpcnN0KSB7XG4gICAgICB0aGlzLmV4cGVjdChfdG9rZW50eXBlLnR5cGVzLmNvbW1hKTtcbiAgICAgIGlmICh0aGlzLmFmdGVyVHJhaWxpbmdDb21tYShfdG9rZW50eXBlLnR5cGVzLmJyYWNlUikpIGJyZWFrO1xuICAgIH0gZWxzZSBmaXJzdCA9IGZhbHNlO1xuXG4gICAgdmFyIHByb3AgPSB0aGlzLnN0YXJ0Tm9kZSgpLFxuICAgICAgICBpc0dlbmVyYXRvciA9IHVuZGVmaW5lZCxcbiAgICAgICAgc3RhcnRQb3MgPSB1bmRlZmluZWQsXG4gICAgICAgIHN0YXJ0TG9jID0gdW5kZWZpbmVkO1xuICAgIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNikge1xuICAgICAgcHJvcC5tZXRob2QgPSBmYWxzZTtcbiAgICAgIHByb3Auc2hvcnRoYW5kID0gZmFsc2U7XG4gICAgICBpZiAoaXNQYXR0ZXJuIHx8IHJlZlNob3J0aGFuZERlZmF1bHRQb3MpIHtcbiAgICAgICAgc3RhcnRQb3MgPSB0aGlzLnN0YXJ0O1xuICAgICAgICBzdGFydExvYyA9IHRoaXMuc3RhcnRMb2M7XG4gICAgICB9XG4gICAgICBpZiAoIWlzUGF0dGVybikgaXNHZW5lcmF0b3IgPSB0aGlzLmVhdChfdG9rZW50eXBlLnR5cGVzLnN0YXIpO1xuICAgIH1cbiAgICB0aGlzLnBhcnNlUHJvcGVydHlOYW1lKHByb3ApO1xuICAgIHRoaXMucGFyc2VQcm9wZXJ0eVZhbHVlKHByb3AsIGlzUGF0dGVybiwgaXNHZW5lcmF0b3IsIHN0YXJ0UG9zLCBzdGFydExvYywgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcyk7XG4gICAgdGhpcy5jaGVja1Byb3BDbGFzaChwcm9wLCBwcm9wSGFzaCk7XG4gICAgbm9kZS5wcm9wZXJ0aWVzLnB1c2godGhpcy5maW5pc2hOb2RlKHByb3AsIFwiUHJvcGVydHlcIikpO1xuICB9XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgaXNQYXR0ZXJuID8gXCJPYmplY3RQYXR0ZXJuXCIgOiBcIk9iamVjdEV4cHJlc3Npb25cIik7XG59O1xuXG5wcC5wYXJzZVByb3BlcnR5VmFsdWUgPSBmdW5jdGlvbiAocHJvcCwgaXNQYXR0ZXJuLCBpc0dlbmVyYXRvciwgc3RhcnRQb3MsIHN0YXJ0TG9jLCByZWZTaG9ydGhhbmREZWZhdWx0UG9zKSB7XG4gIGlmICh0aGlzLmVhdChfdG9rZW50eXBlLnR5cGVzLmNvbG9uKSkge1xuICAgIHByb3AudmFsdWUgPSBpc1BhdHRlcm4gPyB0aGlzLnBhcnNlTWF5YmVEZWZhdWx0KHRoaXMuc3RhcnQsIHRoaXMuc3RhcnRMb2MpIDogdGhpcy5wYXJzZU1heWJlQXNzaWduKGZhbHNlLCByZWZTaG9ydGhhbmREZWZhdWx0UG9zKTtcbiAgICBwcm9wLmtpbmQgPSBcImluaXRcIjtcbiAgfSBlbHNlIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNiAmJiB0aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMucGFyZW5MKSB7XG4gICAgaWYgKGlzUGF0dGVybikgdGhpcy51bmV4cGVjdGVkKCk7XG4gICAgcHJvcC5raW5kID0gXCJpbml0XCI7XG4gICAgcHJvcC5tZXRob2QgPSB0cnVlO1xuICAgIHByb3AudmFsdWUgPSB0aGlzLnBhcnNlTWV0aG9kKGlzR2VuZXJhdG9yKTtcbiAgfSBlbHNlIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNSAmJiAhcHJvcC5jb21wdXRlZCAmJiBwcm9wLmtleS50eXBlID09PSBcIklkZW50aWZpZXJcIiAmJiAocHJvcC5rZXkubmFtZSA9PT0gXCJnZXRcIiB8fCBwcm9wLmtleS5uYW1lID09PSBcInNldFwiKSAmJiAodGhpcy50eXBlICE9IF90b2tlbnR5cGUudHlwZXMuY29tbWEgJiYgdGhpcy50eXBlICE9IF90b2tlbnR5cGUudHlwZXMuYnJhY2VSKSkge1xuICAgIGlmIChpc0dlbmVyYXRvciB8fCBpc1BhdHRlcm4pIHRoaXMudW5leHBlY3RlZCgpO1xuICAgIHByb3Aua2luZCA9IHByb3Aua2V5Lm5hbWU7XG4gICAgdGhpcy5wYXJzZVByb3BlcnR5TmFtZShwcm9wKTtcbiAgICBwcm9wLnZhbHVlID0gdGhpcy5wYXJzZU1ldGhvZChmYWxzZSk7XG4gICAgdmFyIHBhcmFtQ291bnQgPSBwcm9wLmtpbmQgPT09IFwiZ2V0XCIgPyAwIDogMTtcbiAgICBpZiAocHJvcC52YWx1ZS5wYXJhbXMubGVuZ3RoICE9PSBwYXJhbUNvdW50KSB7XG4gICAgICB2YXIgc3RhcnQgPSBwcm9wLnZhbHVlLnN0YXJ0O1xuICAgICAgaWYgKHByb3Aua2luZCA9PT0gXCJnZXRcIikgdGhpcy5yYWlzZShzdGFydCwgXCJnZXR0ZXIgc2hvdWxkIGhhdmUgbm8gcGFyYW1zXCIpO2Vsc2UgdGhpcy5yYWlzZShzdGFydCwgXCJzZXR0ZXIgc2hvdWxkIGhhdmUgZXhhY3RseSBvbmUgcGFyYW1cIik7XG4gICAgfVxuICB9IGVsc2UgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2ICYmICFwcm9wLmNvbXB1dGVkICYmIHByb3Aua2V5LnR5cGUgPT09IFwiSWRlbnRpZmllclwiKSB7XG4gICAgcHJvcC5raW5kID0gXCJpbml0XCI7XG4gICAgaWYgKGlzUGF0dGVybikge1xuICAgICAgaWYgKHRoaXMuaXNLZXl3b3JkKHByb3Aua2V5Lm5hbWUpIHx8IHRoaXMuc3RyaWN0ICYmIChfaWRlbnRpZmllci5yZXNlcnZlZFdvcmRzLnN0cmljdEJpbmQocHJvcC5rZXkubmFtZSkgfHwgX2lkZW50aWZpZXIucmVzZXJ2ZWRXb3Jkcy5zdHJpY3QocHJvcC5rZXkubmFtZSkpIHx8ICF0aGlzLm9wdGlvbnMuYWxsb3dSZXNlcnZlZCAmJiB0aGlzLmlzUmVzZXJ2ZWRXb3JkKHByb3Aua2V5Lm5hbWUpKSB0aGlzLnJhaXNlKHByb3Aua2V5LnN0YXJ0LCBcIkJpbmRpbmcgXCIgKyBwcm9wLmtleS5uYW1lKTtcbiAgICAgIHByb3AudmFsdWUgPSB0aGlzLnBhcnNlTWF5YmVEZWZhdWx0KHN0YXJ0UG9zLCBzdGFydExvYywgcHJvcC5rZXkpO1xuICAgIH0gZWxzZSBpZiAodGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLmVxICYmIHJlZlNob3J0aGFuZERlZmF1bHRQb3MpIHtcbiAgICAgIGlmICghcmVmU2hvcnRoYW5kRGVmYXVsdFBvcy5zdGFydCkgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcy5zdGFydCA9IHRoaXMuc3RhcnQ7XG4gICAgICBwcm9wLnZhbHVlID0gdGhpcy5wYXJzZU1heWJlRGVmYXVsdChzdGFydFBvcywgc3RhcnRMb2MsIHByb3Aua2V5KTtcbiAgICB9IGVsc2Uge1xuICAgICAgcHJvcC52YWx1ZSA9IHByb3Aua2V5O1xuICAgIH1cbiAgICBwcm9wLnNob3J0aGFuZCA9IHRydWU7XG4gIH0gZWxzZSB0aGlzLnVuZXhwZWN0ZWQoKTtcbn07XG5cbnBwLnBhcnNlUHJvcGVydHlOYW1lID0gZnVuY3Rpb24gKHByb3ApIHtcbiAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KSB7XG4gICAgaWYgKHRoaXMuZWF0KF90b2tlbnR5cGUudHlwZXMuYnJhY2tldEwpKSB7XG4gICAgICBwcm9wLmNvbXB1dGVkID0gdHJ1ZTtcbiAgICAgIHByb3Aua2V5ID0gdGhpcy5wYXJzZU1heWJlQXNzaWduKCk7XG4gICAgICB0aGlzLmV4cGVjdChfdG9rZW50eXBlLnR5cGVzLmJyYWNrZXRSKTtcbiAgICAgIHJldHVybiBwcm9wLmtleTtcbiAgICB9IGVsc2Uge1xuICAgICAgcHJvcC5jb21wdXRlZCA9IGZhbHNlO1xuICAgIH1cbiAgfVxuICByZXR1cm4gcHJvcC5rZXkgPSB0aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMubnVtIHx8IHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5zdHJpbmcgPyB0aGlzLnBhcnNlRXhwckF0b20oKSA6IHRoaXMucGFyc2VJZGVudCh0cnVlKTtcbn07XG5cbi8vIEluaXRpYWxpemUgZW1wdHkgZnVuY3Rpb24gbm9kZS5cblxucHAuaW5pdEZ1bmN0aW9uID0gZnVuY3Rpb24gKG5vZGUpIHtcbiAgbm9kZS5pZCA9IG51bGw7XG4gIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNikge1xuICAgIG5vZGUuZ2VuZXJhdG9yID0gZmFsc2U7XG4gICAgbm9kZS5leHByZXNzaW9uID0gZmFsc2U7XG4gIH1cbn07XG5cbi8vIFBhcnNlIG9iamVjdCBvciBjbGFzcyBtZXRob2QuXG5cbnBwLnBhcnNlTWV0aG9kID0gZnVuY3Rpb24gKGlzR2VuZXJhdG9yKSB7XG4gIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgdGhpcy5pbml0RnVuY3Rpb24obm9kZSk7XG4gIHRoaXMuZXhwZWN0KF90b2tlbnR5cGUudHlwZXMucGFyZW5MKTtcbiAgbm9kZS5wYXJhbXMgPSB0aGlzLnBhcnNlQmluZGluZ0xpc3QoX3Rva2VudHlwZS50eXBlcy5wYXJlblIsIGZhbHNlLCBmYWxzZSk7XG4gIHZhciBhbGxvd0V4cHJlc3Npb25Cb2R5ID0gdW5kZWZpbmVkO1xuICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYpIHtcbiAgICBub2RlLmdlbmVyYXRvciA9IGlzR2VuZXJhdG9yO1xuICB9XG4gIHRoaXMucGFyc2VGdW5jdGlvbkJvZHkobm9kZSwgZmFsc2UpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiRnVuY3Rpb25FeHByZXNzaW9uXCIpO1xufTtcblxuLy8gUGFyc2UgYXJyb3cgZnVuY3Rpb24gZXhwcmVzc2lvbiB3aXRoIGdpdmVuIHBhcmFtZXRlcnMuXG5cbnBwLnBhcnNlQXJyb3dFeHByZXNzaW9uID0gZnVuY3Rpb24gKG5vZGUsIHBhcmFtcykge1xuICB0aGlzLmluaXRGdW5jdGlvbihub2RlKTtcbiAgbm9kZS5wYXJhbXMgPSB0aGlzLnRvQXNzaWduYWJsZUxpc3QocGFyYW1zLCB0cnVlKTtcbiAgdGhpcy5wYXJzZUZ1bmN0aW9uQm9keShub2RlLCB0cnVlKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkFycm93RnVuY3Rpb25FeHByZXNzaW9uXCIpO1xufTtcblxuLy8gUGFyc2UgZnVuY3Rpb24gYm9keSBhbmQgY2hlY2sgcGFyYW1ldGVycy5cblxucHAucGFyc2VGdW5jdGlvbkJvZHkgPSBmdW5jdGlvbiAobm9kZSwgYWxsb3dFeHByZXNzaW9uKSB7XG4gIHZhciBpc0V4cHJlc3Npb24gPSBhbGxvd0V4cHJlc3Npb24gJiYgdGhpcy50eXBlICE9PSBfdG9rZW50eXBlLnR5cGVzLmJyYWNlTDtcblxuICBpZiAoaXNFeHByZXNzaW9uKSB7XG4gICAgbm9kZS5ib2R5ID0gdGhpcy5wYXJzZU1heWJlQXNzaWduKCk7XG4gICAgbm9kZS5leHByZXNzaW9uID0gdHJ1ZTtcbiAgfSBlbHNlIHtcbiAgICAvLyBTdGFydCBhIG5ldyBzY29wZSB3aXRoIHJlZ2FyZCB0byBsYWJlbHMgYW5kIHRoZSBgaW5GdW5jdGlvbmBcbiAgICAvLyBmbGFnIChyZXN0b3JlIHRoZW0gdG8gdGhlaXIgb2xkIHZhbHVlIGFmdGVyd2FyZHMpLlxuICAgIHZhciBvbGRJbkZ1bmMgPSB0aGlzLmluRnVuY3Rpb24sXG4gICAgICAgIG9sZEluR2VuID0gdGhpcy5pbkdlbmVyYXRvcixcbiAgICAgICAgb2xkTGFiZWxzID0gdGhpcy5sYWJlbHM7XG4gICAgdGhpcy5pbkZ1bmN0aW9uID0gdHJ1ZTt0aGlzLmluR2VuZXJhdG9yID0gbm9kZS5nZW5lcmF0b3I7dGhpcy5sYWJlbHMgPSBbXTtcbiAgICBub2RlLmJvZHkgPSB0aGlzLnBhcnNlQmxvY2sodHJ1ZSk7XG4gICAgbm9kZS5leHByZXNzaW9uID0gZmFsc2U7XG4gICAgdGhpcy5pbkZ1bmN0aW9uID0gb2xkSW5GdW5jO3RoaXMuaW5HZW5lcmF0b3IgPSBvbGRJbkdlbjt0aGlzLmxhYmVscyA9IG9sZExhYmVscztcbiAgfVxuXG4gIC8vIElmIHRoaXMgaXMgYSBzdHJpY3QgbW9kZSBmdW5jdGlvbiwgdmVyaWZ5IHRoYXQgYXJndW1lbnQgbmFtZXNcbiAgLy8gYXJlIG5vdCByZXBlYXRlZCwgYW5kIGl0IGRvZXMgbm90IHRyeSB0byBiaW5kIHRoZSB3b3JkcyBgZXZhbGBcbiAgLy8gb3IgYGFyZ3VtZW50c2AuXG4gIGlmICh0aGlzLnN0cmljdCB8fCAhaXNFeHByZXNzaW9uICYmIG5vZGUuYm9keS5ib2R5Lmxlbmd0aCAmJiB0aGlzLmlzVXNlU3RyaWN0KG5vZGUuYm9keS5ib2R5WzBdKSkge1xuICAgIHZhciBuYW1lSGFzaCA9IHt9LFxuICAgICAgICBvbGRTdHJpY3QgPSB0aGlzLnN0cmljdDtcbiAgICB0aGlzLnN0cmljdCA9IHRydWU7XG4gICAgaWYgKG5vZGUuaWQpIHRoaXMuY2hlY2tMVmFsKG5vZGUuaWQsIHRydWUpO1xuICAgIGZvciAodmFyIGkgPSAwOyBpIDwgbm9kZS5wYXJhbXMubGVuZ3RoOyBpKyspIHtcbiAgICAgIHRoaXMuY2hlY2tMVmFsKG5vZGUucGFyYW1zW2ldLCB0cnVlLCBuYW1lSGFzaCk7XG4gICAgfXRoaXMuc3RyaWN0ID0gb2xkU3RyaWN0O1xuICB9XG59O1xuXG4vLyBQYXJzZXMgYSBjb21tYS1zZXBhcmF0ZWQgbGlzdCBvZiBleHByZXNzaW9ucywgYW5kIHJldHVybnMgdGhlbSBhc1xuLy8gYW4gYXJyYXkuIGBjbG9zZWAgaXMgdGhlIHRva2VuIHR5cGUgdGhhdCBlbmRzIHRoZSBsaXN0LCBhbmRcbi8vIGBhbGxvd0VtcHR5YCBjYW4gYmUgdHVybmVkIG9uIHRvIGFsbG93IHN1YnNlcXVlbnQgY29tbWFzIHdpdGhcbi8vIG5vdGhpbmcgaW4gYmV0d2VlbiB0aGVtIHRvIGJlIHBhcnNlZCBhcyBgbnVsbGAgKHdoaWNoIGlzIG5lZWRlZFxuLy8gZm9yIGFycmF5IGxpdGVyYWxzKS5cblxucHAucGFyc2VFeHByTGlzdCA9IGZ1bmN0aW9uIChjbG9zZSwgYWxsb3dUcmFpbGluZ0NvbW1hLCBhbGxvd0VtcHR5LCByZWZTaG9ydGhhbmREZWZhdWx0UG9zKSB7XG4gIHZhciBlbHRzID0gW10sXG4gICAgICBmaXJzdCA9IHRydWU7XG4gIHdoaWxlICghdGhpcy5lYXQoY2xvc2UpKSB7XG4gICAgaWYgKCFmaXJzdCkge1xuICAgICAgdGhpcy5leHBlY3QoX3Rva2VudHlwZS50eXBlcy5jb21tYSk7XG4gICAgICBpZiAoYWxsb3dUcmFpbGluZ0NvbW1hICYmIHRoaXMuYWZ0ZXJUcmFpbGluZ0NvbW1hKGNsb3NlKSkgYnJlYWs7XG4gICAgfSBlbHNlIGZpcnN0ID0gZmFsc2U7XG5cbiAgICB2YXIgZWx0ID0gdW5kZWZpbmVkO1xuICAgIGlmIChhbGxvd0VtcHR5ICYmIHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5jb21tYSkgZWx0ID0gbnVsbDtlbHNlIGlmICh0aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuZWxsaXBzaXMpIGVsdCA9IHRoaXMucGFyc2VTcHJlYWQocmVmU2hvcnRoYW5kRGVmYXVsdFBvcyk7ZWxzZSBlbHQgPSB0aGlzLnBhcnNlTWF5YmVBc3NpZ24oZmFsc2UsIHJlZlNob3J0aGFuZERlZmF1bHRQb3MpO1xuICAgIGVsdHMucHVzaChlbHQpO1xuICB9XG4gIHJldHVybiBlbHRzO1xufTtcblxuLy8gUGFyc2UgdGhlIG5leHQgdG9rZW4gYXMgYW4gaWRlbnRpZmllci4gSWYgYGxpYmVyYWxgIGlzIHRydWUgKHVzZWRcbi8vIHdoZW4gcGFyc2luZyBwcm9wZXJ0aWVzKSwgaXQgd2lsbCBhbHNvIGNvbnZlcnQga2V5d29yZHMgaW50b1xuLy8gaWRlbnRpZmllcnMuXG5cbnBwLnBhcnNlSWRlbnQgPSBmdW5jdGlvbiAobGliZXJhbCkge1xuICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gIGlmIChsaWJlcmFsICYmIHRoaXMub3B0aW9ucy5hbGxvd1Jlc2VydmVkID09IFwibmV2ZXJcIikgbGliZXJhbCA9IGZhbHNlO1xuICBpZiAodGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLm5hbWUpIHtcbiAgICBpZiAoIWxpYmVyYWwgJiYgKCF0aGlzLm9wdGlvbnMuYWxsb3dSZXNlcnZlZCAmJiB0aGlzLmlzUmVzZXJ2ZWRXb3JkKHRoaXMudmFsdWUpIHx8IHRoaXMuc3RyaWN0ICYmIF9pZGVudGlmaWVyLnJlc2VydmVkV29yZHMuc3RyaWN0KHRoaXMudmFsdWUpICYmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNiB8fCB0aGlzLmlucHV0LnNsaWNlKHRoaXMuc3RhcnQsIHRoaXMuZW5kKS5pbmRleE9mKFwiXFxcXFwiKSA9PSAtMSkpKSB0aGlzLnJhaXNlKHRoaXMuc3RhcnQsIFwiVGhlIGtleXdvcmQgJ1wiICsgdGhpcy52YWx1ZSArIFwiJyBpcyByZXNlcnZlZFwiKTtcbiAgICBub2RlLm5hbWUgPSB0aGlzLnZhbHVlO1xuICB9IGVsc2UgaWYgKGxpYmVyYWwgJiYgdGhpcy50eXBlLmtleXdvcmQpIHtcbiAgICBub2RlLm5hbWUgPSB0aGlzLnR5cGUua2V5d29yZDtcbiAgfSBlbHNlIHtcbiAgICB0aGlzLnVuZXhwZWN0ZWQoKTtcbiAgfVxuICB0aGlzLm5leHQoKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIklkZW50aWZpZXJcIik7XG59O1xuXG4vLyBQYXJzZXMgeWllbGQgZXhwcmVzc2lvbiBpbnNpZGUgZ2VuZXJhdG9yLlxuXG5wcC5wYXJzZVlpZWxkID0gZnVuY3Rpb24gKCkge1xuICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gIHRoaXMubmV4dCgpO1xuICBpZiAodGhpcy50eXBlID09IF90b2tlbnR5cGUudHlwZXMuc2VtaSB8fCB0aGlzLmNhbkluc2VydFNlbWljb2xvbigpIHx8IHRoaXMudHlwZSAhPSBfdG9rZW50eXBlLnR5cGVzLnN0YXIgJiYgIXRoaXMudHlwZS5zdGFydHNFeHByKSB7XG4gICAgbm9kZS5kZWxlZ2F0ZSA9IGZhbHNlO1xuICAgIG5vZGUuYXJndW1lbnQgPSBudWxsO1xuICB9IGVsc2Uge1xuICAgIG5vZGUuZGVsZWdhdGUgPSB0aGlzLmVhdChfdG9rZW50eXBlLnR5cGVzLnN0YXIpO1xuICAgIG5vZGUuYXJndW1lbnQgPSB0aGlzLnBhcnNlTWF5YmVBc3NpZ24oKTtcbiAgfVxuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiWWllbGRFeHByZXNzaW9uXCIpO1xufTtcblxuLy8gUGFyc2VzIGFycmF5IGFuZCBnZW5lcmF0b3IgY29tcHJlaGVuc2lvbnMuXG5cbnBwLnBhcnNlQ29tcHJlaGVuc2lvbiA9IGZ1bmN0aW9uIChub2RlLCBpc0dlbmVyYXRvcikge1xuICBub2RlLmJsb2NrcyA9IFtdO1xuICB3aGlsZSAodGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLl9mb3IpIHtcbiAgICB2YXIgYmxvY2sgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICAgIHRoaXMubmV4dCgpO1xuICAgIHRoaXMuZXhwZWN0KF90b2tlbnR5cGUudHlwZXMucGFyZW5MKTtcbiAgICBibG9jay5sZWZ0ID0gdGhpcy5wYXJzZUJpbmRpbmdBdG9tKCk7XG4gICAgdGhpcy5jaGVja0xWYWwoYmxvY2subGVmdCwgdHJ1ZSk7XG4gICAgdGhpcy5leHBlY3RDb250ZXh0dWFsKFwib2ZcIik7XG4gICAgYmxvY2sucmlnaHQgPSB0aGlzLnBhcnNlRXhwcmVzc2lvbigpO1xuICAgIHRoaXMuZXhwZWN0KF90b2tlbnR5cGUudHlwZXMucGFyZW5SKTtcbiAgICBub2RlLmJsb2Nrcy5wdXNoKHRoaXMuZmluaXNoTm9kZShibG9jaywgXCJDb21wcmVoZW5zaW9uQmxvY2tcIikpO1xuICB9XG4gIG5vZGUuZmlsdGVyID0gdGhpcy5lYXQoX3Rva2VudHlwZS50eXBlcy5faWYpID8gdGhpcy5wYXJzZVBhcmVuRXhwcmVzc2lvbigpIDogbnVsbDtcbiAgbm9kZS5ib2R5ID0gdGhpcy5wYXJzZUV4cHJlc3Npb24oKTtcbiAgdGhpcy5leHBlY3QoaXNHZW5lcmF0b3IgPyBfdG9rZW50eXBlLnR5cGVzLnBhcmVuUiA6IF90b2tlbnR5cGUudHlwZXMuYnJhY2tldFIpO1xuICBub2RlLmdlbmVyYXRvciA9IGlzR2VuZXJhdG9yO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiQ29tcHJlaGVuc2lvbkV4cHJlc3Npb25cIik7XG59O1xuXG59LHtcIi4vaWRlbnRpZmllclwiOjIsXCIuL3N0YXRlXCI6MTAsXCIuL3Rva2VudHlwZVwiOjE0LFwiLi91dGlsXCI6MTV9XSwyOltmdW5jdGlvbihfZGVyZXFfLG1vZHVsZSxleHBvcnRzKXtcbi8vIFRoaXMgaXMgYSB0cmljayB0YWtlbiBmcm9tIEVzcHJpbWEuIEl0IHR1cm5zIG91dCB0aGF0LCBvblxuLy8gbm9uLUNocm9tZSBicm93c2VycywgdG8gY2hlY2sgd2hldGhlciBhIHN0cmluZyBpcyBpbiBhIHNldCwgYVxuLy8gcHJlZGljYXRlIGNvbnRhaW5pbmcgYSBiaWcgdWdseSBgc3dpdGNoYCBzdGF0ZW1lbnQgaXMgZmFzdGVyIHRoYW5cbi8vIGEgcmVndWxhciBleHByZXNzaW9uLCBhbmQgb24gQ2hyb21lIHRoZSB0d28gYXJlIGFib3V0IG9uIHBhci5cbi8vIFRoaXMgZnVuY3Rpb24gdXNlcyBgZXZhbGAgKG5vbi1sZXhpY2FsKSB0byBwcm9kdWNlIHN1Y2ggYVxuLy8gcHJlZGljYXRlIGZyb20gYSBzcGFjZS1zZXBhcmF0ZWQgc3RyaW5nIG9mIHdvcmRzLlxuLy9cbi8vIEl0IHN0YXJ0cyBieSBzb3J0aW5nIHRoZSB3b3JkcyBieSBsZW5ndGguXG5cblwidXNlIHN0cmljdFwiO1xuXG5leHBvcnRzLl9fZXNNb2R1bGUgPSB0cnVlO1xuZXhwb3J0cy5pc0lkZW50aWZpZXJTdGFydCA9IGlzSWRlbnRpZmllclN0YXJ0O1xuZXhwb3J0cy5pc0lkZW50aWZpZXJDaGFyID0gaXNJZGVudGlmaWVyQ2hhcjtcbmZ1bmN0aW9uIG1ha2VQcmVkaWNhdGUod29yZHMpIHtcbiAgd29yZHMgPSB3b3Jkcy5zcGxpdChcIiBcIik7XG4gIHZhciBmID0gXCJcIixcbiAgICAgIGNhdHMgPSBbXTtcbiAgb3V0OiBmb3IgKHZhciBpID0gMDsgaSA8IHdvcmRzLmxlbmd0aDsgKytpKSB7XG4gICAgZm9yICh2YXIgaiA9IDA7IGogPCBjYXRzLmxlbmd0aDsgKytqKSB7XG4gICAgICBpZiAoY2F0c1tqXVswXS5sZW5ndGggPT0gd29yZHNbaV0ubGVuZ3RoKSB7XG4gICAgICAgIGNhdHNbal0ucHVzaCh3b3Jkc1tpXSk7XG4gICAgICAgIGNvbnRpbnVlIG91dDtcbiAgICAgIH1cbiAgICB9Y2F0cy5wdXNoKFt3b3Jkc1tpXV0pO1xuICB9XG4gIGZ1bmN0aW9uIGNvbXBhcmVUbyhhcnIpIHtcbiAgICBpZiAoYXJyLmxlbmd0aCA9PSAxKSByZXR1cm4gZiArPSBcInJldHVybiBzdHIgPT09IFwiICsgSlNPTi5zdHJpbmdpZnkoYXJyWzBdKSArIFwiO1wiO1xuICAgIGYgKz0gXCJzd2l0Y2goc3RyKXtcIjtcbiAgICBmb3IgKHZhciBpID0gMDsgaSA8IGFyci5sZW5ndGg7ICsraSkge1xuICAgICAgZiArPSBcImNhc2UgXCIgKyBKU09OLnN0cmluZ2lmeShhcnJbaV0pICsgXCI6XCI7XG4gICAgfWYgKz0gXCJyZXR1cm4gdHJ1ZX1yZXR1cm4gZmFsc2U7XCI7XG4gIH1cblxuICAvLyBXaGVuIHRoZXJlIGFyZSBtb3JlIHRoYW4gdGhyZWUgbGVuZ3RoIGNhdGVnb3JpZXMsIGFuIG91dGVyXG4gIC8vIHN3aXRjaCBmaXJzdCBkaXNwYXRjaGVzIG9uIHRoZSBsZW5ndGhzLCB0byBzYXZlIG9uIGNvbXBhcmlzb25zLlxuXG4gIGlmIChjYXRzLmxlbmd0aCA+IDMpIHtcbiAgICBjYXRzLnNvcnQoZnVuY3Rpb24gKGEsIGIpIHtcbiAgICAgIHJldHVybiBiLmxlbmd0aCAtIGEubGVuZ3RoO1xuICAgIH0pO1xuICAgIGYgKz0gXCJzd2l0Y2goc3RyLmxlbmd0aCl7XCI7XG4gICAgZm9yICh2YXIgaSA9IDA7IGkgPCBjYXRzLmxlbmd0aDsgKytpKSB7XG4gICAgICB2YXIgY2F0ID0gY2F0c1tpXTtcbiAgICAgIGYgKz0gXCJjYXNlIFwiICsgY2F0WzBdLmxlbmd0aCArIFwiOlwiO1xuICAgICAgY29tcGFyZVRvKGNhdCk7XG4gICAgfVxuICAgIGYgKz0gXCJ9XCJcblxuICAgIC8vIE90aGVyd2lzZSwgc2ltcGx5IGdlbmVyYXRlIGEgZmxhdCBgc3dpdGNoYCBzdGF0ZW1lbnQuXG5cbiAgICA7XG4gIH0gZWxzZSB7XG4gICAgY29tcGFyZVRvKHdvcmRzKTtcbiAgfVxuICByZXR1cm4gbmV3IEZ1bmN0aW9uKFwic3RyXCIsIGYpO1xufVxuXG4vLyBSZXNlcnZlZCB3b3JkIGxpc3RzIGZvciB2YXJpb3VzIGRpYWxlY3RzIG9mIHRoZSBsYW5ndWFnZVxuXG52YXIgcmVzZXJ2ZWRXb3JkcyA9IHtcbiAgMzogbWFrZVByZWRpY2F0ZShcImFic3RyYWN0IGJvb2xlYW4gYnl0ZSBjaGFyIGNsYXNzIGRvdWJsZSBlbnVtIGV4cG9ydCBleHRlbmRzIGZpbmFsIGZsb2F0IGdvdG8gaW1wbGVtZW50cyBpbXBvcnQgaW50IGludGVyZmFjZSBsb25nIG5hdGl2ZSBwYWNrYWdlIHByaXZhdGUgcHJvdGVjdGVkIHB1YmxpYyBzaG9ydCBzdGF0aWMgc3VwZXIgc3luY2hyb25pemVkIHRocm93cyB0cmFuc2llbnQgdm9sYXRpbGVcIiksXG4gIDU6IG1ha2VQcmVkaWNhdGUoXCJjbGFzcyBlbnVtIGV4dGVuZHMgc3VwZXIgY29uc3QgZXhwb3J0IGltcG9ydFwiKSxcbiAgNjogbWFrZVByZWRpY2F0ZShcImVudW0gYXdhaXRcIiksXG4gIHN0cmljdDogbWFrZVByZWRpY2F0ZShcImltcGxlbWVudHMgaW50ZXJmYWNlIGxldCBwYWNrYWdlIHByaXZhdGUgcHJvdGVjdGVkIHB1YmxpYyBzdGF0aWMgeWllbGRcIiksXG4gIHN0cmljdEJpbmQ6IG1ha2VQcmVkaWNhdGUoXCJldmFsIGFyZ3VtZW50c1wiKVxufTtcblxuZXhwb3J0cy5yZXNlcnZlZFdvcmRzID0gcmVzZXJ2ZWRXb3Jkcztcbi8vIEFuZCB0aGUga2V5d29yZHNcblxudmFyIGVjbWE1QW5kTGVzc0tleXdvcmRzID0gXCJicmVhayBjYXNlIGNhdGNoIGNvbnRpbnVlIGRlYnVnZ2VyIGRlZmF1bHQgZG8gZWxzZSBmaW5hbGx5IGZvciBmdW5jdGlvbiBpZiByZXR1cm4gc3dpdGNoIHRocm93IHRyeSB2YXIgd2hpbGUgd2l0aCBudWxsIHRydWUgZmFsc2UgaW5zdGFuY2VvZiB0eXBlb2Ygdm9pZCBkZWxldGUgbmV3IGluIHRoaXNcIjtcblxudmFyIGtleXdvcmRzID0ge1xuICA1OiBtYWtlUHJlZGljYXRlKGVjbWE1QW5kTGVzc0tleXdvcmRzKSxcbiAgNjogbWFrZVByZWRpY2F0ZShlY21hNUFuZExlc3NLZXl3b3JkcyArIFwiIGxldCBjb25zdCBjbGFzcyBleHRlbmRzIGV4cG9ydCBpbXBvcnQgeWllbGQgc3VwZXJcIilcbn07XG5cbmV4cG9ydHMua2V5d29yZHMgPSBrZXl3b3Jkcztcbi8vICMjIENoYXJhY3RlciBjYXRlZ29yaWVzXG5cbi8vIEJpZyB1Z2x5IHJlZ3VsYXIgZXhwcmVzc2lvbnMgdGhhdCBtYXRjaCBjaGFyYWN0ZXJzIGluIHRoZVxuLy8gd2hpdGVzcGFjZSwgaWRlbnRpZmllciwgYW5kIGlkZW50aWZpZXItc3RhcnQgY2F0ZWdvcmllcy4gVGhlc2Vcbi8vIGFyZSBvbmx5IGFwcGxpZWQgd2hlbiBhIGNoYXJhY3RlciBpcyBmb3VuZCB0byBhY3R1YWxseSBoYXZlIGFcbi8vIGNvZGUgcG9pbnQgYWJvdmUgMTI4LlxuLy8gR2VuZXJhdGVkIGJ5IGB0b29scy9nZW5lcmF0ZS1pZGVudGlmaWVyLXJlZ2V4LmpzYC5cblxudmFyIG5vbkFTQ0lJaWRlbnRpZmllclN0YXJ0Q2hhcnMgPSBcIsKqwrXCusOALcOWw5gtw7bDuC3LgcuGLcuRy6Aty6TLrMuuzbAtzbTNts23zbotzb3Nv86GzogtzorOjM6OLc6hzqMtz7XPty3SgdKKLdSv1LEt1ZbVmdWhLdaH15At16rXsC3XstigLdmK2a7Zr9mxLduT25Xbpdum267br9u6Ldu827/ckNySLdyv3Y0t3qXesd+KLd+q37Tftd+64KCALeCgleCgmuCgpOCgqOChgC3goZjgoqAt4KKy4KSELeCkueCkveClkOClmC3gpaHgpbEt4KaA4KaFLeCmjOCmj+CmkOCmky3gpqjgpqot4Kaw4Kay4Ka2LeCmueCmveCnjuCnnOCnneCnny3gp6Hgp7Dgp7HgqIUt4KiK4KiP4KiQ4KiTLeCoqOCoqi3gqLDgqLLgqLPgqLXgqLbgqLjgqLngqZkt4Kmc4Kme4KmyLeCptOCqhS3gqo3gqo8t4KqR4KqTLeCqqOCqqi3gqrDgqrLgqrPgqrUt4Kq54Kq94KuQ4Kug4Kuh4KyFLeCsjOCsj+CskOCsky3grKjgrKot4Kyw4Kyy4Kyz4Ky1LeCsueCsveCtnOCtneCtny3graHgrbHgroPgroUt4K6K4K6OLeCukOCuki3grpXgrpngrprgrpzgrp7grp/grqPgrqTgrqgt4K6q4K6uLeCuueCvkOCwhS3gsIzgsI4t4LCQ4LCSLeCwqOCwqi3gsLngsL3gsZjgsZngsaDgsaHgsoUt4LKM4LKOLeCykOCyki3gsqjgsqot4LKz4LK1LeCyueCyveCznuCzoOCzoeCzseCzsuC0hS3gtIzgtI4t4LSQ4LSSLeC0uuC0veC1juC1oOC1oeC1ui3gtb/gtoUt4LaW4LaaLeC2seC2sy3gtrvgtr3gt4At4LeG4LiBLeC4sOC4suC4s+C5gC3guYbguoHguoLguoTguofguojguorguo3gupQt4LqX4LqZLeC6n+C6oS3guqPguqXguqfguqrguqvguq0t4Lqw4Lqy4Lqz4Lq94LuALeC7hOC7huC7nC3gu5/gvIDgvYAt4L2H4L2JLeC9rOC+iC3gvozhgIAt4YCq4YC/4YGQLeGBleGBmi3hgZ3hgaHhgaXhgabhga4t4YGw4YG1LeGCgeGCjuGCoC3hg4Xhg4fhg43hg5At4YO64YO8LeGJiOGJii3hiY3hiZAt4YmW4YmY4YmaLeGJneGJoC3hiojhioot4YqN4YqQLeGKsOGKsi3hirXhirgt4Yq+4YuA4YuCLeGLheGLiC3hi5bhi5gt4YyQ4YySLeGMleGMmC3hjZrhjoAt4Y6P4Y6gLeGPtOGQgS3hmazhma8t4Zm/4ZqBLeGamuGaoC3hm6rhm64t4Zu44ZyALeGcjOGcji3hnJHhnKAt4Zyx4Z2ALeGdkeGdoC3hnazhna4t4Z2w4Z6ALeGes+Gfl+GfnOGgoC3hobfhooAt4aKo4aKq4aKwLeGjteGkgC3hpJ7hpZAt4aWt4aWwLeGltOGmgC3hpqvhp4Et4aeH4aiALeGoluGooC3hqZThqqfhrIUt4ayz4a2FLeGti+Gugy3hrqDhrq7hrq/hrrot4a+l4bCALeGwo+GxjS3hsY/hsZot4bG94bOpLeGzrOGzri3hs7Hhs7Xhs7bhtIAt4ba/4biALeG8leG8mC3hvJ3hvKAt4b2F4b2ILeG9jeG9kC3hvZfhvZnhvZvhvZ3hvZ8t4b294b6ALeG+tOG+ti3hvrzhvr7hv4It4b+E4b+GLeG/jOG/kC3hv5Phv5Yt4b+b4b+gLeG/rOG/si3hv7Thv7Yt4b+84oGx4oG/4oKQLeKCnOKEguKEh+KEii3ihJPihJXihJgt4oSd4oSk4oSm4oSo4oSqLeKEueKEvC3ihL/ihYUt4oWJ4oWO4oWgLeKGiOKwgC3isK7isLAt4rGe4rGgLeKzpOKzqy3is67is7Lis7PitIAt4rSl4rSn4rSt4rSwLeK1p+K1r+K2gC3itpbitqAt4ram4raoLeK2ruK2sC3itrbitrgt4ra+4reALeK3huK3iC3it47it5At4reW4reYLeK3nuOAhS3jgIfjgKEt44Cp44CxLeOAteOAuC3jgLzjgYEt44KW44KbLeOCn+OCoS3jg7rjg7wt44O/44SFLeOEreOEsS3jho7jhqAt44a644ewLeOHv+OQgC3ktrXkuIAt6b+M6oCALeqSjOqTkC3qk73qlIAt6piM6piQLeqYn+qYquqYq+qZgC3qma7qmb8t6pqd6pqgLeqbr+qcly3qnJ/qnKIt6p6I6p6LLeqejuqekC3qnq3qnrDqnrHqn7ct6qCB6qCDLeqgheqghy3qoIrqoIwt6qCi6qGALeqhs+qigi3qorPqo7It6qO36qO76qSKLeqkpeqksC3qpYbqpaAt6qW86qaELeqmsuqnj+qnoC3qp6Tqp6Yt6qev6qe6LeqnvuqogC3qqKjqqYAt6qmC6qmELeqpi+qpoC3qqbbqqbrqqb4t6qqv6qqx6qq16qq26qq5LeqqveqrgOqrguqrmy3qq53qq6At6quq6quyLeqrtOqsgS3qrIbqrIkt6qyO6qyRLeqsluqsoC3qrKbqrKgt6qyu6qywLeqtmuqtnC3qrZ/qraTqraXqr4At6q+i6rCALe2eo+2esC3tn4btn4st7Z+776SALe+pre+psC3vq5nvrIAt76yG76yTLe+sl++sne+sny3vrKjvrKot76y276y4Le+svO+svu+tgO+tge+tg++thO+thi3vrrHvr5Mt77S977WQLe+2j++2ki3vt4fvt7At77e777mwLe+5tO+5ti3vu7zvvKEt77y6772BLe+9mu+9pi3vvr7vv4It77+H77+KLe+/j++/ki3vv5fvv5ot77+cXCI7XG52YXIgbm9uQVNDSUlpZGVudGlmaWVyQ2hhcnMgPSBcIuKAjOKAjcK3zIAtza/Oh9KDLdKH1pEt1r3Wv9eB14LXhNeF14fYkC3YmtmLLdmp2bDbli3bnNufLduk26fbqNuqLdut27At27nckdywLd2K3qYt3rDfgC3fid+rLd+z4KCWLeCgmeCgmy3goKPgoKUt4KCn4KCpLeCgreChmS3goZvgo6Qt4KSD4KS6LeCkvOCkvi3gpY/gpZEt4KWX4KWi4KWj4KWmLeClr+CmgS3gpoPgprzgpr4t4KeE4KeH4KeI4KeLLeCnjeCnl+CnouCno+Cnpi3gp6/gqIEt4KiD4Ki84Ki+LeCpguCph+CpiOCpiy3gqY3gqZHgqaYt4Kmx4Km14KqBLeCqg+CqvOCqvi3gq4Xgq4ct4KuJ4KuLLeCrjeCrouCro+Crpi3gq6/grIEt4KyD4Ky84Ky+LeCthOCth+CtiOCtiy3grY3grZbgrZfgraLgraPgraYt4K2v4K6C4K6+LeCvguCvhi3gr4jgr4ot4K+N4K+X4K+mLeCvr+CwgC3gsIPgsL4t4LGE4LGGLeCxiOCxii3gsY3gsZXgsZbgsaLgsaPgsaYt4LGv4LKBLeCyg+CyvOCyvi3gs4Tgs4Yt4LOI4LOKLeCzjeCzleCzluCzouCzo+Czpi3gs6/gtIEt4LSD4LS+LeC1hOC1hi3gtYjgtYot4LWN4LWX4LWi4LWj4LWmLeC1r+C2guC2g+C3iuC3jy3gt5Tgt5bgt5gt4Lef4LemLeC3r+C3suC3s+C4seC4tC3guLrguYct4LmO4LmQLeC5meC6seC6tC3gurngurvgurzgu4gt4LuN4LuQLeC7meC8mOC8meC8oC3gvKngvLXgvLfgvLngvL7gvL/gvbEt4L6E4L6G4L6H4L6NLeC+l+C+mS3gvrzgv4bhgKst4YC+4YGALeGBieGBli3hgZnhgZ4t4YGg4YGiLeGBpOGBpy3hga3hgbEt4YG04YKCLeGCjeGCjy3hgp3hjZ0t4Y2f4Y2pLeGNseGcki3hnJThnLIt4Zy04Z2S4Z2T4Z2y4Z2z4Z60LeGfk+GfneGfoC3hn6nhoIst4aCN4aCQLeGgmeGiqeGkoC3hpKvhpLAt4aS74aWGLeGlj+GmsC3hp4Dhp4jhp4nhp5At4aea4aiXLeGom+GplS3hqZ7hqaAt4am84am/LeGqieGqkC3hqpnhqrAt4aq94ayALeGshOGstC3hrYThrZAt4a2Z4a2rLeGts+GugC3hroLhrqEt4a6t4a6wLeGuueGvpi3hr7PhsKQt4bC34bGALeGxieGxkC3hsZnhs5At4bOS4bOULeGzqOGzreGzsi3hs7Ths7jhs7nht4At4be14be8LeG3v+KAv+KBgOKBlOKDkC3ig5zig6Hig6Ut4oOw4rOvLeKzseK1v+K3oC3it7/jgKot44Cv44KZ44Ka6pigLeqYqeqZr+qZtC3qmb3qmp/qm7Dqm7HqoILqoIbqoIvqoKMt6qCn6qKA6qKB6qK0LeqjhOqjkC3qo5nqo6At6qOx6qSALeqkieqkpi3qpK3qpYct6qWT6qaALeqmg+qmsy3qp4Dqp5At6qeZ6qel6qewLeqnueqoqS3qqLbqqYPqqYzqqY3qqZAt6qmZ6qm7LeqpveqqsOqqsi3qqrTqqrfqqrjqqr7qqr/qq4Hqq6st6quv6qu16qu26q+jLeqvquqvrOqvreqvsC3qr7nvrJ7vuIAt77iP77igLe+4re+4s++4tO+5jS3vuY/vvJAt77yZ77y/XCI7XG5cbnZhciBub25BU0NJSWlkZW50aWZpZXJTdGFydCA9IG5ldyBSZWdFeHAoXCJbXCIgKyBub25BU0NJSWlkZW50aWZpZXJTdGFydENoYXJzICsgXCJdXCIpO1xudmFyIG5vbkFTQ0lJaWRlbnRpZmllciA9IG5ldyBSZWdFeHAoXCJbXCIgKyBub25BU0NJSWlkZW50aWZpZXJTdGFydENoYXJzICsgbm9uQVNDSUlpZGVudGlmaWVyQ2hhcnMgKyBcIl1cIik7XG5cbm5vbkFTQ0lJaWRlbnRpZmllclN0YXJ0Q2hhcnMgPSBub25BU0NJSWlkZW50aWZpZXJDaGFycyA9IG51bGw7XG5cbi8vIFRoZXNlIGFyZSBhIHJ1bi1sZW5ndGggYW5kIG9mZnNldCBlbmNvZGVkIHJlcHJlc2VudGF0aW9uIG9mIHRoZVxuLy8gPjB4ZmZmZiBjb2RlIHBvaW50cyB0aGF0IGFyZSBhIHZhbGlkIHBhcnQgb2YgaWRlbnRpZmllcnMuIFRoZVxuLy8gb2Zmc2V0IHN0YXJ0cyBhdCAweDEwMDAwLCBhbmQgZWFjaCBwYWlyIG9mIG51bWJlcnMgcmVwcmVzZW50cyBhblxuLy8gb2Zmc2V0IHRvIHRoZSBuZXh0IHJhbmdlLCBhbmQgdGhlbiBhIHNpemUgb2YgdGhlIHJhbmdlLiBUaGV5IHdlcmVcbi8vIGdlbmVyYXRlZCBieSB0b29scy9nZW5lcmF0ZS1pZGVudGlmaWVyLXJlZ2V4LmpzXG52YXIgYXN0cmFsSWRlbnRpZmllclN0YXJ0Q29kZXMgPSBbMCwgMTEsIDIsIDI1LCAyLCAxOCwgMiwgMSwgMiwgMTQsIDMsIDEzLCAzNSwgMTIyLCA3MCwgNTIsIDI2OCwgMjgsIDQsIDQ4LCA0OCwgMzEsIDE3LCAyNiwgNiwgMzcsIDExLCAyOSwgMywgMzUsIDUsIDcsIDIsIDQsIDQzLCAxNTcsIDk5LCAzOSwgOSwgNTEsIDE1NywgMzEwLCAxMCwgMjEsIDExLCA3LCAxNTMsIDUsIDMsIDAsIDIsIDQzLCAyLCAxLCA0LCAwLCAzLCAyMiwgMTEsIDIyLCAxMCwgMzAsIDk4LCAyMSwgMTEsIDI1LCA3MSwgNTUsIDcsIDEsIDY1LCAwLCAxNiwgMywgMiwgMiwgMiwgMjYsIDQ1LCAyOCwgNCwgMjgsIDM2LCA3LCAyLCAyNywgMjgsIDUzLCAxMSwgMjEsIDExLCAxOCwgMTQsIDE3LCAxMTEsIDcyLCA5NTUsIDUyLCA3NiwgNDQsIDMzLCAyNCwgMjcsIDM1LCA0MiwgMzQsIDQsIDAsIDEzLCA0NywgMTUsIDMsIDIyLCAwLCAzOCwgMTcsIDIsIDI0LCAxMzMsIDQ2LCAzOSwgNywgMywgMSwgMywgMjEsIDIsIDYsIDIsIDEsIDIsIDQsIDQsIDAsIDMyLCA0LCAyODcsIDQ3LCAyMSwgMSwgMiwgMCwgMTg1LCA0NiwgODIsIDQ3LCAyMSwgMCwgNjAsIDQyLCA1MDIsIDYzLCAzMiwgMCwgNDQ5LCA1NiwgMTI4OCwgOTIwLCAxMDQsIDExMCwgMjk2MiwgMTA3MCwgMTMyNjYsIDU2OCwgOCwgMzAsIDExNCwgMjksIDE5LCA0NywgMTcsIDMsIDMyLCAyMCwgNiwgMTgsIDg4MSwgNjgsIDEyLCAwLCA2NywgMTIsIDE2NDgxLCAxLCAzMDcxLCAxMDYsIDYsIDEyLCA0LCA4LCA4LCA5LCA1OTkxLCA4NCwgMiwgNzAsIDIsIDEsIDMsIDAsIDMsIDEsIDMsIDMsIDIsIDExLCAyLCAwLCAyLCA2LCAyLCA2NCwgMiwgMywgMywgNywgMiwgNiwgMiwgMjcsIDIsIDMsIDIsIDQsIDIsIDAsIDQsIDYsIDIsIDMzOSwgMywgMjQsIDIsIDI0LCAyLCAzMCwgMiwgMjQsIDIsIDMwLCAyLCAyNCwgMiwgMzAsIDIsIDI0LCAyLCAzMCwgMiwgMjQsIDIsIDcsIDQxNDksIDE5NiwgMTM0MCwgMywgMiwgMjYsIDIsIDEsIDIsIDAsIDMsIDAsIDIsIDksIDIsIDMsIDIsIDAsIDIsIDAsIDcsIDAsIDUsIDAsIDIsIDAsIDIsIDAsIDIsIDIsIDIsIDEsIDIsIDAsIDMsIDAsIDIsIDAsIDIsIDAsIDIsIDAsIDIsIDAsIDIsIDEsIDIsIDAsIDMsIDMsIDIsIDYsIDIsIDMsIDIsIDMsIDIsIDAsIDIsIDksIDIsIDE2LCA2LCAyLCAyLCA0LCAyLCAxNiwgNDQyMSwgNDI3MTAsIDQyLCA0MTQ4LCAxMiwgMjIxLCAxNjM1NSwgNTQxXTtcbnZhciBhc3RyYWxJZGVudGlmaWVyQ29kZXMgPSBbNTA5LCAwLCAyMjcsIDAsIDE1MCwgNCwgMjk0LCA5LCAxMzY4LCAyLCAyLCAxLCA2LCAzLCA0MSwgMiwgNSwgMCwgMTY2LCAxLCAxMzA2LCAyLCA1NCwgMTQsIDMyLCA5LCAxNiwgMywgNDYsIDEwLCA1NCwgOSwgNywgMiwgMzcsIDEzLCAyLCA5LCA1MiwgMCwgMTMsIDIsIDQ5LCAxMywgMTYsIDksIDgzLCAxMSwgMTY4LCAxMSwgNiwgOSwgOCwgMiwgNTcsIDAsIDIsIDYsIDMsIDEsIDMsIDIsIDEwLCAwLCAxMSwgMSwgMywgNiwgNCwgNCwgMzE2LCAxOSwgMTMsIDksIDIxNCwgNiwgMywgOCwgMTEyLCAxNiwgMTYsIDksIDgyLCAxMiwgOSwgOSwgNTM1LCA5LCAyMDg1NSwgOSwgMTM1LCA0LCA2MCwgNiwgMjYsIDksIDEwMTYsIDQ1LCAxNywgMywgMTk3MjMsIDEsIDUzMTksIDQsIDQsIDUsIDksIDcsIDMsIDYsIDMxLCAzLCAxNDksIDIsIDE0MTgsIDQ5LCA0MzA1LCA2LCA3OTI2MTgsIDIzOV07XG5cbi8vIFRoaXMgaGFzIGEgY29tcGxleGl0eSBsaW5lYXIgdG8gdGhlIHZhbHVlIG9mIHRoZSBjb2RlLiBUaGVcbi8vIGFzc3VtcHRpb24gaXMgdGhhdCBsb29raW5nIHVwIGFzdHJhbCBpZGVudGlmaWVyIGNoYXJhY3RlcnMgaXNcbi8vIHJhcmUuXG5mdW5jdGlvbiBpc0luQXN0cmFsU2V0KGNvZGUsIHNldCkge1xuICB2YXIgcG9zID0gMHgxMDAwMDtcbiAgZm9yICh2YXIgaSA9IDA7IGkgPCBzZXQubGVuZ3RoOyBpICs9IDIpIHtcbiAgICBwb3MgKz0gc2V0W2ldO1xuICAgIGlmIChwb3MgPiBjb2RlKSByZXR1cm4gZmFsc2U7XG4gICAgcG9zICs9IHNldFtpICsgMV07XG4gICAgaWYgKHBvcyA+PSBjb2RlKSByZXR1cm4gdHJ1ZTtcbiAgfVxufVxuXG4vLyBUZXN0IHdoZXRoZXIgYSBnaXZlbiBjaGFyYWN0ZXIgY29kZSBzdGFydHMgYW4gaWRlbnRpZmllci5cblxuZnVuY3Rpb24gaXNJZGVudGlmaWVyU3RhcnQoY29kZSwgYXN0cmFsKSB7XG4gIGlmIChjb2RlIDwgNjUpIHJldHVybiBjb2RlID09PSAzNjtcbiAgaWYgKGNvZGUgPCA5MSkgcmV0dXJuIHRydWU7XG4gIGlmIChjb2RlIDwgOTcpIHJldHVybiBjb2RlID09PSA5NTtcbiAgaWYgKGNvZGUgPCAxMjMpIHJldHVybiB0cnVlO1xuICBpZiAoY29kZSA8PSAweGZmZmYpIHJldHVybiBjb2RlID49IDB4YWEgJiYgbm9uQVNDSUlpZGVudGlmaWVyU3RhcnQudGVzdChTdHJpbmcuZnJvbUNoYXJDb2RlKGNvZGUpKTtcbiAgaWYgKGFzdHJhbCA9PT0gZmFsc2UpIHJldHVybiBmYWxzZTtcbiAgcmV0dXJuIGlzSW5Bc3RyYWxTZXQoY29kZSwgYXN0cmFsSWRlbnRpZmllclN0YXJ0Q29kZXMpO1xufVxuXG4vLyBUZXN0IHdoZXRoZXIgYSBnaXZlbiBjaGFyYWN0ZXIgaXMgcGFydCBvZiBhbiBpZGVudGlmaWVyLlxuXG5mdW5jdGlvbiBpc0lkZW50aWZpZXJDaGFyKGNvZGUsIGFzdHJhbCkge1xuICBpZiAoY29kZSA8IDQ4KSByZXR1cm4gY29kZSA9PT0gMzY7XG4gIGlmIChjb2RlIDwgNTgpIHJldHVybiB0cnVlO1xuICBpZiAoY29kZSA8IDY1KSByZXR1cm4gZmFsc2U7XG4gIGlmIChjb2RlIDwgOTEpIHJldHVybiB0cnVlO1xuICBpZiAoY29kZSA8IDk3KSByZXR1cm4gY29kZSA9PT0gOTU7XG4gIGlmIChjb2RlIDwgMTIzKSByZXR1cm4gdHJ1ZTtcbiAgaWYgKGNvZGUgPD0gMHhmZmZmKSByZXR1cm4gY29kZSA+PSAweGFhICYmIG5vbkFTQ0lJaWRlbnRpZmllci50ZXN0KFN0cmluZy5mcm9tQ2hhckNvZGUoY29kZSkpO1xuICBpZiAoYXN0cmFsID09PSBmYWxzZSkgcmV0dXJuIGZhbHNlO1xuICByZXR1cm4gaXNJbkFzdHJhbFNldChjb2RlLCBhc3RyYWxJZGVudGlmaWVyU3RhcnRDb2RlcykgfHwgaXNJbkFzdHJhbFNldChjb2RlLCBhc3RyYWxJZGVudGlmaWVyQ29kZXMpO1xufVxuXG59LHt9XSwzOltmdW5jdGlvbihfZGVyZXFfLG1vZHVsZSxleHBvcnRzKXtcbi8vIEFjb3JuIGlzIGEgdGlueSwgZmFzdCBKYXZhU2NyaXB0IHBhcnNlciB3cml0dGVuIGluIEphdmFTY3JpcHQuXG4vL1xuLy8gQWNvcm4gd2FzIHdyaXR0ZW4gYnkgTWFyaWpuIEhhdmVyYmVrZSwgSW5ndmFyIFN0ZXBhbnlhbiwgYW5kXG4vLyB2YXJpb3VzIGNvbnRyaWJ1dG9ycyBhbmQgcmVsZWFzZWQgdW5kZXIgYW4gTUlUIGxpY2Vuc2UuXG4vL1xuLy8gR2l0IHJlcG9zaXRvcmllcyBmb3IgQWNvcm4gYXJlIGF2YWlsYWJsZSBhdFxuLy9cbi8vICAgICBodHRwOi8vbWFyaWpuaGF2ZXJiZWtlLm5sL2dpdC9hY29yblxuLy8gICAgIGh0dHBzOi8vZ2l0aHViLmNvbS9tYXJpam5oL2Fjb3JuLmdpdFxuLy9cbi8vIFBsZWFzZSB1c2UgdGhlIFtnaXRodWIgYnVnIHRyYWNrZXJdW2doYnRdIHRvIHJlcG9ydCBpc3N1ZXMuXG4vL1xuLy8gW2doYnRdOiBodHRwczovL2dpdGh1Yi5jb20vbWFyaWpuaC9hY29ybi9pc3N1ZXNcbi8vXG4vLyBUaGlzIGZpbGUgZGVmaW5lcyB0aGUgbWFpbiBwYXJzZXIgaW50ZXJmYWNlLiBUaGUgbGlicmFyeSBhbHNvIGNvbWVzXG4vLyB3aXRoIGEgW2Vycm9yLXRvbGVyYW50IHBhcnNlcl1bZGFtbWl0XSBhbmQgYW5cbi8vIFthYnN0cmFjdCBzeW50YXggdHJlZSB3YWxrZXJdW3dhbGtdLCBkZWZpbmVkIGluIG90aGVyIGZpbGVzLlxuLy9cbi8vIFtkYW1taXRdOiBhY29ybl9sb29zZS5qc1xuLy8gW3dhbGtdOiB1dGlsL3dhbGsuanNcblxuXCJ1c2Ugc3RyaWN0XCI7XG5cbmV4cG9ydHMuX19lc01vZHVsZSA9IHRydWU7XG5leHBvcnRzLnBhcnNlID0gcGFyc2U7XG5leHBvcnRzLnBhcnNlRXhwcmVzc2lvbkF0ID0gcGFyc2VFeHByZXNzaW9uQXQ7XG5leHBvcnRzLnRva2VuaXplciA9IHRva2VuaXplcjtcblxudmFyIF9zdGF0ZSA9IF9kZXJlcV8oXCIuL3N0YXRlXCIpO1xuXG52YXIgX29wdGlvbnMgPSBfZGVyZXFfKFwiLi9vcHRpb25zXCIpO1xuXG5fZGVyZXFfKFwiLi9wYXJzZXV0aWxcIik7XG5cbl9kZXJlcV8oXCIuL3N0YXRlbWVudFwiKTtcblxuX2RlcmVxXyhcIi4vbHZhbFwiKTtcblxuX2RlcmVxXyhcIi4vZXhwcmVzc2lvblwiKTtcblxuX2RlcmVxXyhcIi4vbG9jYXRpb25cIik7XG5cbmV4cG9ydHMuUGFyc2VyID0gX3N0YXRlLlBhcnNlcjtcbmV4cG9ydHMucGx1Z2lucyA9IF9zdGF0ZS5wbHVnaW5zO1xuZXhwb3J0cy5kZWZhdWx0T3B0aW9ucyA9IF9vcHRpb25zLmRlZmF1bHRPcHRpb25zO1xuXG52YXIgX2xvY3V0aWwgPSBfZGVyZXFfKFwiLi9sb2N1dGlsXCIpO1xuXG5leHBvcnRzLlBvc2l0aW9uID0gX2xvY3V0aWwuUG9zaXRpb247XG5leHBvcnRzLlNvdXJjZUxvY2F0aW9uID0gX2xvY3V0aWwuU291cmNlTG9jYXRpb247XG5leHBvcnRzLmdldExpbmVJbmZvID0gX2xvY3V0aWwuZ2V0TGluZUluZm87XG5cbnZhciBfbm9kZSA9IF9kZXJlcV8oXCIuL25vZGVcIik7XG5cbmV4cG9ydHMuTm9kZSA9IF9ub2RlLk5vZGU7XG5cbnZhciBfdG9rZW50eXBlID0gX2RlcmVxXyhcIi4vdG9rZW50eXBlXCIpO1xuXG5leHBvcnRzLlRva2VuVHlwZSA9IF90b2tlbnR5cGUuVG9rZW5UeXBlO1xuZXhwb3J0cy50b2tUeXBlcyA9IF90b2tlbnR5cGUudHlwZXM7XG5cbnZhciBfdG9rZW5jb250ZXh0ID0gX2RlcmVxXyhcIi4vdG9rZW5jb250ZXh0XCIpO1xuXG5leHBvcnRzLlRva0NvbnRleHQgPSBfdG9rZW5jb250ZXh0LlRva0NvbnRleHQ7XG5leHBvcnRzLnRva0NvbnRleHRzID0gX3Rva2VuY29udGV4dC50eXBlcztcblxudmFyIF9pZGVudGlmaWVyID0gX2RlcmVxXyhcIi4vaWRlbnRpZmllclwiKTtcblxuZXhwb3J0cy5pc0lkZW50aWZpZXJDaGFyID0gX2lkZW50aWZpZXIuaXNJZGVudGlmaWVyQ2hhcjtcbmV4cG9ydHMuaXNJZGVudGlmaWVyU3RhcnQgPSBfaWRlbnRpZmllci5pc0lkZW50aWZpZXJTdGFydDtcblxudmFyIF90b2tlbml6ZSA9IF9kZXJlcV8oXCIuL3Rva2VuaXplXCIpO1xuXG5leHBvcnRzLlRva2VuID0gX3Rva2VuaXplLlRva2VuO1xuXG52YXIgX3doaXRlc3BhY2UgPSBfZGVyZXFfKFwiLi93aGl0ZXNwYWNlXCIpO1xuXG5leHBvcnRzLmlzTmV3TGluZSA9IF93aGl0ZXNwYWNlLmlzTmV3TGluZTtcbmV4cG9ydHMubGluZUJyZWFrID0gX3doaXRlc3BhY2UubGluZUJyZWFrO1xuZXhwb3J0cy5saW5lQnJlYWtHID0gX3doaXRlc3BhY2UubGluZUJyZWFrRztcbnZhciB2ZXJzaW9uID0gXCIyLjQuMFwiO1xuXG5leHBvcnRzLnZlcnNpb24gPSB2ZXJzaW9uO1xuLy8gVGhlIG1haW4gZXhwb3J0ZWQgaW50ZXJmYWNlICh1bmRlciBgc2VsZi5hY29ybmAgd2hlbiBpbiB0aGVcbi8vIGJyb3dzZXIpIGlzIGEgYHBhcnNlYCBmdW5jdGlvbiB0aGF0IHRha2VzIGEgY29kZSBzdHJpbmcgYW5kXG4vLyByZXR1cm5zIGFuIGFic3RyYWN0IHN5bnRheCB0cmVlIGFzIHNwZWNpZmllZCBieSBbTW96aWxsYSBwYXJzZXJcbi8vIEFQSV1bYXBpXS5cbi8vXG4vLyBbYXBpXTogaHR0cHM6Ly9kZXZlbG9wZXIubW96aWxsYS5vcmcvZW4tVVMvZG9jcy9TcGlkZXJNb25rZXkvUGFyc2VyX0FQSVxuXG5mdW5jdGlvbiBwYXJzZShpbnB1dCwgb3B0aW9ucykge1xuICByZXR1cm4gbmV3IF9zdGF0ZS5QYXJzZXIob3B0aW9ucywgaW5wdXQpLnBhcnNlKCk7XG59XG5cbi8vIFRoaXMgZnVuY3Rpb24gdHJpZXMgdG8gcGFyc2UgYSBzaW5nbGUgZXhwcmVzc2lvbiBhdCBhIGdpdmVuXG4vLyBvZmZzZXQgaW4gYSBzdHJpbmcuIFVzZWZ1bCBmb3IgcGFyc2luZyBtaXhlZC1sYW5ndWFnZSBmb3JtYXRzXG4vLyB0aGF0IGVtYmVkIEphdmFTY3JpcHQgZXhwcmVzc2lvbnMuXG5cbmZ1bmN0aW9uIHBhcnNlRXhwcmVzc2lvbkF0KGlucHV0LCBwb3MsIG9wdGlvbnMpIHtcbiAgdmFyIHAgPSBuZXcgX3N0YXRlLlBhcnNlcihvcHRpb25zLCBpbnB1dCwgcG9zKTtcbiAgcC5uZXh0VG9rZW4oKTtcbiAgcmV0dXJuIHAucGFyc2VFeHByZXNzaW9uKCk7XG59XG5cbi8vIEFjb3JuIGlzIG9yZ2FuaXplZCBhcyBhIHRva2VuaXplciBhbmQgYSByZWN1cnNpdmUtZGVzY2VudCBwYXJzZXIuXG4vLyBUaGUgYHRva2VuaXplYCBleHBvcnQgcHJvdmlkZXMgYW4gaW50ZXJmYWNlIHRvIHRoZSB0b2tlbml6ZXIuXG5cbmZ1bmN0aW9uIHRva2VuaXplcihpbnB1dCwgb3B0aW9ucykge1xuICByZXR1cm4gbmV3IF9zdGF0ZS5QYXJzZXIob3B0aW9ucywgaW5wdXQpO1xufVxuXG59LHtcIi4vZXhwcmVzc2lvblwiOjEsXCIuL2lkZW50aWZpZXJcIjoyLFwiLi9sb2NhdGlvblwiOjQsXCIuL2xvY3V0aWxcIjo1LFwiLi9sdmFsXCI6NixcIi4vbm9kZVwiOjcsXCIuL29wdGlvbnNcIjo4LFwiLi9wYXJzZXV0aWxcIjo5LFwiLi9zdGF0ZVwiOjEwLFwiLi9zdGF0ZW1lbnRcIjoxMSxcIi4vdG9rZW5jb250ZXh0XCI6MTIsXCIuL3Rva2VuaXplXCI6MTMsXCIuL3Rva2VudHlwZVwiOjE0LFwiLi93aGl0ZXNwYWNlXCI6MTZ9XSw0OltmdW5jdGlvbihfZGVyZXFfLG1vZHVsZSxleHBvcnRzKXtcblwidXNlIHN0cmljdFwiO1xuXG52YXIgX3N0YXRlID0gX2RlcmVxXyhcIi4vc3RhdGVcIik7XG5cbnZhciBfbG9jdXRpbCA9IF9kZXJlcV8oXCIuL2xvY3V0aWxcIik7XG5cbnZhciBwcCA9IF9zdGF0ZS5QYXJzZXIucHJvdG90eXBlO1xuXG4vLyBUaGlzIGZ1bmN0aW9uIGlzIHVzZWQgdG8gcmFpc2UgZXhjZXB0aW9ucyBvbiBwYXJzZSBlcnJvcnMuIEl0XG4vLyB0YWtlcyBhbiBvZmZzZXQgaW50ZWdlciAoaW50byB0aGUgY3VycmVudCBgaW5wdXRgKSB0byBpbmRpY2F0ZVxuLy8gdGhlIGxvY2F0aW9uIG9mIHRoZSBlcnJvciwgYXR0YWNoZXMgdGhlIHBvc2l0aW9uIHRvIHRoZSBlbmRcbi8vIG9mIHRoZSBlcnJvciBtZXNzYWdlLCBhbmQgdGhlbiByYWlzZXMgYSBgU3ludGF4RXJyb3JgIHdpdGggdGhhdFxuLy8gbWVzc2FnZS5cblxucHAucmFpc2UgPSBmdW5jdGlvbiAocG9zLCBtZXNzYWdlKSB7XG4gIHZhciBsb2MgPSBfbG9jdXRpbC5nZXRMaW5lSW5mbyh0aGlzLmlucHV0LCBwb3MpO1xuICBtZXNzYWdlICs9IFwiIChcIiArIGxvYy5saW5lICsgXCI6XCIgKyBsb2MuY29sdW1uICsgXCIpXCI7XG4gIHZhciBlcnIgPSBuZXcgU3ludGF4RXJyb3IobWVzc2FnZSk7XG4gIGVyci5wb3MgPSBwb3M7ZXJyLmxvYyA9IGxvYztlcnIucmFpc2VkQXQgPSB0aGlzLnBvcztcbiAgdGhyb3cgZXJyO1xufTtcblxucHAuY3VyUG9zaXRpb24gPSBmdW5jdGlvbiAoKSB7XG4gIGlmICh0aGlzLm9wdGlvbnMubG9jYXRpb25zKSB7XG4gICAgcmV0dXJuIG5ldyBfbG9jdXRpbC5Qb3NpdGlvbih0aGlzLmN1ckxpbmUsIHRoaXMucG9zIC0gdGhpcy5saW5lU3RhcnQpO1xuICB9XG59O1xuXG59LHtcIi4vbG9jdXRpbFwiOjUsXCIuL3N0YXRlXCI6MTB9XSw1OltmdW5jdGlvbihfZGVyZXFfLG1vZHVsZSxleHBvcnRzKXtcblwidXNlIHN0cmljdFwiO1xuXG5leHBvcnRzLl9fZXNNb2R1bGUgPSB0cnVlO1xuZXhwb3J0cy5nZXRMaW5lSW5mbyA9IGdldExpbmVJbmZvO1xuXG5mdW5jdGlvbiBfY2xhc3NDYWxsQ2hlY2soaW5zdGFuY2UsIENvbnN0cnVjdG9yKSB7IGlmICghKGluc3RhbmNlIGluc3RhbmNlb2YgQ29uc3RydWN0b3IpKSB7IHRocm93IG5ldyBUeXBlRXJyb3IoXCJDYW5ub3QgY2FsbCBhIGNsYXNzIGFzIGEgZnVuY3Rpb25cIik7IH0gfVxuXG52YXIgX3doaXRlc3BhY2UgPSBfZGVyZXFfKFwiLi93aGl0ZXNwYWNlXCIpO1xuXG4vLyBUaGVzZSBhcmUgdXNlZCB3aGVuIGBvcHRpb25zLmxvY2F0aW9uc2AgaXMgb24sIGZvciB0aGVcbi8vIGBzdGFydExvY2AgYW5kIGBlbmRMb2NgIHByb3BlcnRpZXMuXG5cbnZhciBQb3NpdGlvbiA9IChmdW5jdGlvbiAoKSB7XG4gIGZ1bmN0aW9uIFBvc2l0aW9uKGxpbmUsIGNvbCkge1xuICAgIF9jbGFzc0NhbGxDaGVjayh0aGlzLCBQb3NpdGlvbik7XG5cbiAgICB0aGlzLmxpbmUgPSBsaW5lO1xuICAgIHRoaXMuY29sdW1uID0gY29sO1xuICB9XG5cbiAgUG9zaXRpb24ucHJvdG90eXBlLm9mZnNldCA9IGZ1bmN0aW9uIG9mZnNldChuKSB7XG4gICAgcmV0dXJuIG5ldyBQb3NpdGlvbih0aGlzLmxpbmUsIHRoaXMuY29sdW1uICsgbik7XG4gIH07XG5cbiAgcmV0dXJuIFBvc2l0aW9uO1xufSkoKTtcblxuZXhwb3J0cy5Qb3NpdGlvbiA9IFBvc2l0aW9uO1xuXG52YXIgU291cmNlTG9jYXRpb24gPSBmdW5jdGlvbiBTb3VyY2VMb2NhdGlvbihwLCBzdGFydCwgZW5kKSB7XG4gIF9jbGFzc0NhbGxDaGVjayh0aGlzLCBTb3VyY2VMb2NhdGlvbik7XG5cbiAgdGhpcy5zdGFydCA9IHN0YXJ0O1xuICB0aGlzLmVuZCA9IGVuZDtcbiAgaWYgKHAuc291cmNlRmlsZSAhPT0gbnVsbCkgdGhpcy5zb3VyY2UgPSBwLnNvdXJjZUZpbGU7XG59O1xuXG5leHBvcnRzLlNvdXJjZUxvY2F0aW9uID0gU291cmNlTG9jYXRpb247XG5cbi8vIFRoZSBgZ2V0TGluZUluZm9gIGZ1bmN0aW9uIGlzIG1vc3RseSB1c2VmdWwgd2hlbiB0aGVcbi8vIGBsb2NhdGlvbnNgIG9wdGlvbiBpcyBvZmYgKGZvciBwZXJmb3JtYW5jZSByZWFzb25zKSBhbmQgeW91XG4vLyB3YW50IHRvIGZpbmQgdGhlIGxpbmUvY29sdW1uIHBvc2l0aW9uIGZvciBhIGdpdmVuIGNoYXJhY3RlclxuLy8gb2Zmc2V0LiBgaW5wdXRgIHNob3VsZCBiZSB0aGUgY29kZSBzdHJpbmcgdGhhdCB0aGUgb2Zmc2V0IHJlZmVyc1xuLy8gaW50by5cblxuZnVuY3Rpb24gZ2V0TGluZUluZm8oaW5wdXQsIG9mZnNldCkge1xuICBmb3IgKHZhciBsaW5lID0gMSwgY3VyID0gMDs7KSB7XG4gICAgX3doaXRlc3BhY2UubGluZUJyZWFrRy5sYXN0SW5kZXggPSBjdXI7XG4gICAgdmFyIG1hdGNoID0gX3doaXRlc3BhY2UubGluZUJyZWFrRy5leGVjKGlucHV0KTtcbiAgICBpZiAobWF0Y2ggJiYgbWF0Y2guaW5kZXggPCBvZmZzZXQpIHtcbiAgICAgICsrbGluZTtcbiAgICAgIGN1ciA9IG1hdGNoLmluZGV4ICsgbWF0Y2hbMF0ubGVuZ3RoO1xuICAgIH0gZWxzZSB7XG4gICAgICByZXR1cm4gbmV3IFBvc2l0aW9uKGxpbmUsIG9mZnNldCAtIGN1cik7XG4gICAgfVxuICB9XG59XG5cbn0se1wiLi93aGl0ZXNwYWNlXCI6MTZ9XSw2OltmdW5jdGlvbihfZGVyZXFfLG1vZHVsZSxleHBvcnRzKXtcblwidXNlIHN0cmljdFwiO1xuXG52YXIgX3Rva2VudHlwZSA9IF9kZXJlcV8oXCIuL3Rva2VudHlwZVwiKTtcblxudmFyIF9zdGF0ZSA9IF9kZXJlcV8oXCIuL3N0YXRlXCIpO1xuXG52YXIgX2lkZW50aWZpZXIgPSBfZGVyZXFfKFwiLi9pZGVudGlmaWVyXCIpO1xuXG52YXIgX3V0aWwgPSBfZGVyZXFfKFwiLi91dGlsXCIpO1xuXG52YXIgcHAgPSBfc3RhdGUuUGFyc2VyLnByb3RvdHlwZTtcblxuLy8gQ29udmVydCBleGlzdGluZyBleHByZXNzaW9uIGF0b20gdG8gYXNzaWduYWJsZSBwYXR0ZXJuXG4vLyBpZiBwb3NzaWJsZS5cblxucHAudG9Bc3NpZ25hYmxlID0gZnVuY3Rpb24gKG5vZGUsIGlzQmluZGluZykge1xuICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYgJiYgbm9kZSkge1xuICAgIHN3aXRjaCAobm9kZS50eXBlKSB7XG4gICAgICBjYXNlIFwiSWRlbnRpZmllclwiOlxuICAgICAgY2FzZSBcIk9iamVjdFBhdHRlcm5cIjpcbiAgICAgIGNhc2UgXCJBcnJheVBhdHRlcm5cIjpcbiAgICAgIGNhc2UgXCJBc3NpZ25tZW50UGF0dGVyblwiOlxuICAgICAgICBicmVhaztcblxuICAgICAgY2FzZSBcIk9iamVjdEV4cHJlc3Npb25cIjpcbiAgICAgICAgbm9kZS50eXBlID0gXCJPYmplY3RQYXR0ZXJuXCI7XG4gICAgICAgIGZvciAodmFyIGkgPSAwOyBpIDwgbm9kZS5wcm9wZXJ0aWVzLmxlbmd0aDsgaSsrKSB7XG4gICAgICAgICAgdmFyIHByb3AgPSBub2RlLnByb3BlcnRpZXNbaV07XG4gICAgICAgICAgaWYgKHByb3Aua2luZCAhPT0gXCJpbml0XCIpIHRoaXMucmFpc2UocHJvcC5rZXkuc3RhcnQsIFwiT2JqZWN0IHBhdHRlcm4gY2FuJ3QgY29udGFpbiBnZXR0ZXIgb3Igc2V0dGVyXCIpO1xuICAgICAgICAgIHRoaXMudG9Bc3NpZ25hYmxlKHByb3AudmFsdWUsIGlzQmluZGluZyk7XG4gICAgICAgIH1cbiAgICAgICAgYnJlYWs7XG5cbiAgICAgIGNhc2UgXCJBcnJheUV4cHJlc3Npb25cIjpcbiAgICAgICAgbm9kZS50eXBlID0gXCJBcnJheVBhdHRlcm5cIjtcbiAgICAgICAgdGhpcy50b0Fzc2lnbmFibGVMaXN0KG5vZGUuZWxlbWVudHMsIGlzQmluZGluZyk7XG4gICAgICAgIGJyZWFrO1xuXG4gICAgICBjYXNlIFwiQXNzaWdubWVudEV4cHJlc3Npb25cIjpcbiAgICAgICAgaWYgKG5vZGUub3BlcmF0b3IgPT09IFwiPVwiKSB7XG4gICAgICAgICAgbm9kZS50eXBlID0gXCJBc3NpZ25tZW50UGF0dGVyblwiO1xuICAgICAgICAgIGRlbGV0ZSBub2RlLm9wZXJhdG9yO1xuICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgIHRoaXMucmFpc2Uobm9kZS5sZWZ0LmVuZCwgXCJPbmx5ICc9JyBvcGVyYXRvciBjYW4gYmUgdXNlZCBmb3Igc3BlY2lmeWluZyBkZWZhdWx0IHZhbHVlLlwiKTtcbiAgICAgICAgfVxuICAgICAgICBicmVhaztcblxuICAgICAgY2FzZSBcIlBhcmVudGhlc2l6ZWRFeHByZXNzaW9uXCI6XG4gICAgICAgIG5vZGUuZXhwcmVzc2lvbiA9IHRoaXMudG9Bc3NpZ25hYmxlKG5vZGUuZXhwcmVzc2lvbiwgaXNCaW5kaW5nKTtcbiAgICAgICAgYnJlYWs7XG5cbiAgICAgIGNhc2UgXCJNZW1iZXJFeHByZXNzaW9uXCI6XG4gICAgICAgIGlmICghaXNCaW5kaW5nKSBicmVhaztcblxuICAgICAgZGVmYXVsdDpcbiAgICAgICAgdGhpcy5yYWlzZShub2RlLnN0YXJ0LCBcIkFzc2lnbmluZyB0byBydmFsdWVcIik7XG4gICAgfVxuICB9XG4gIHJldHVybiBub2RlO1xufTtcblxuLy8gQ29udmVydCBsaXN0IG9mIGV4cHJlc3Npb24gYXRvbXMgdG8gYmluZGluZyBsaXN0LlxuXG5wcC50b0Fzc2lnbmFibGVMaXN0ID0gZnVuY3Rpb24gKGV4cHJMaXN0LCBpc0JpbmRpbmcpIHtcbiAgdmFyIGVuZCA9IGV4cHJMaXN0Lmxlbmd0aDtcbiAgaWYgKGVuZCkge1xuICAgIHZhciBsYXN0ID0gZXhwckxpc3RbZW5kIC0gMV07XG4gICAgaWYgKGxhc3QgJiYgbGFzdC50eXBlID09IFwiUmVzdEVsZW1lbnRcIikge1xuICAgICAgLS1lbmQ7XG4gICAgfSBlbHNlIGlmIChsYXN0ICYmIGxhc3QudHlwZSA9PSBcIlNwcmVhZEVsZW1lbnRcIikge1xuICAgICAgbGFzdC50eXBlID0gXCJSZXN0RWxlbWVudFwiO1xuICAgICAgdmFyIGFyZyA9IGxhc3QuYXJndW1lbnQ7XG4gICAgICB0aGlzLnRvQXNzaWduYWJsZShhcmcsIGlzQmluZGluZyk7XG4gICAgICBpZiAoYXJnLnR5cGUgIT09IFwiSWRlbnRpZmllclwiICYmIGFyZy50eXBlICE9PSBcIk1lbWJlckV4cHJlc3Npb25cIiAmJiBhcmcudHlwZSAhPT0gXCJBcnJheVBhdHRlcm5cIikgdGhpcy51bmV4cGVjdGVkKGFyZy5zdGFydCk7XG4gICAgICAtLWVuZDtcbiAgICB9XG4gIH1cbiAgZm9yICh2YXIgaSA9IDA7IGkgPCBlbmQ7IGkrKykge1xuICAgIHZhciBlbHQgPSBleHByTGlzdFtpXTtcbiAgICBpZiAoZWx0KSB0aGlzLnRvQXNzaWduYWJsZShlbHQsIGlzQmluZGluZyk7XG4gIH1cbiAgcmV0dXJuIGV4cHJMaXN0O1xufTtcblxuLy8gUGFyc2VzIHNwcmVhZCBlbGVtZW50LlxuXG5wcC5wYXJzZVNwcmVhZCA9IGZ1bmN0aW9uIChyZWZTaG9ydGhhbmREZWZhdWx0UG9zKSB7XG4gIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgdGhpcy5uZXh0KCk7XG4gIG5vZGUuYXJndW1lbnQgPSB0aGlzLnBhcnNlTWF5YmVBc3NpZ24ocmVmU2hvcnRoYW5kRGVmYXVsdFBvcyk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJTcHJlYWRFbGVtZW50XCIpO1xufTtcblxucHAucGFyc2VSZXN0ID0gZnVuY3Rpb24gKCkge1xuICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gIHRoaXMubmV4dCgpO1xuICBub2RlLmFyZ3VtZW50ID0gdGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLm5hbWUgfHwgdGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLmJyYWNrZXRMID8gdGhpcy5wYXJzZUJpbmRpbmdBdG9tKCkgOiB0aGlzLnVuZXhwZWN0ZWQoKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIlJlc3RFbGVtZW50XCIpO1xufTtcblxuLy8gUGFyc2VzIGx2YWx1ZSAoYXNzaWduYWJsZSkgYXRvbS5cblxucHAucGFyc2VCaW5kaW5nQXRvbSA9IGZ1bmN0aW9uICgpIHtcbiAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA8IDYpIHJldHVybiB0aGlzLnBhcnNlSWRlbnQoKTtcbiAgc3dpdGNoICh0aGlzLnR5cGUpIHtcbiAgICBjYXNlIF90b2tlbnR5cGUudHlwZXMubmFtZTpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlSWRlbnQoKTtcblxuICAgIGNhc2UgX3Rva2VudHlwZS50eXBlcy5icmFja2V0TDpcbiAgICAgIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgbm9kZS5lbGVtZW50cyA9IHRoaXMucGFyc2VCaW5kaW5nTGlzdChfdG9rZW50eXBlLnR5cGVzLmJyYWNrZXRSLCB0cnVlLCB0cnVlKTtcbiAgICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJBcnJheVBhdHRlcm5cIik7XG5cbiAgICBjYXNlIF90b2tlbnR5cGUudHlwZXMuYnJhY2VMOlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VPYmoodHJ1ZSk7XG5cbiAgICBkZWZhdWx0OlxuICAgICAgdGhpcy51bmV4cGVjdGVkKCk7XG4gIH1cbn07XG5cbnBwLnBhcnNlQmluZGluZ0xpc3QgPSBmdW5jdGlvbiAoY2xvc2UsIGFsbG93RW1wdHksIGFsbG93VHJhaWxpbmdDb21tYSkge1xuICB2YXIgZWx0cyA9IFtdLFxuICAgICAgZmlyc3QgPSB0cnVlO1xuICB3aGlsZSAoIXRoaXMuZWF0KGNsb3NlKSkge1xuICAgIGlmIChmaXJzdCkgZmlyc3QgPSBmYWxzZTtlbHNlIHRoaXMuZXhwZWN0KF90b2tlbnR5cGUudHlwZXMuY29tbWEpO1xuICAgIGlmIChhbGxvd0VtcHR5ICYmIHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5jb21tYSkge1xuICAgICAgZWx0cy5wdXNoKG51bGwpO1xuICAgIH0gZWxzZSBpZiAoYWxsb3dUcmFpbGluZ0NvbW1hICYmIHRoaXMuYWZ0ZXJUcmFpbGluZ0NvbW1hKGNsb3NlKSkge1xuICAgICAgYnJlYWs7XG4gICAgfSBlbHNlIGlmICh0aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuZWxsaXBzaXMpIHtcbiAgICAgIHZhciByZXN0ID0gdGhpcy5wYXJzZVJlc3QoKTtcbiAgICAgIHRoaXMucGFyc2VCaW5kaW5nTGlzdEl0ZW0ocmVzdCk7XG4gICAgICBlbHRzLnB1c2gocmVzdCk7XG4gICAgICB0aGlzLmV4cGVjdChjbG9zZSk7XG4gICAgICBicmVhaztcbiAgICB9IGVsc2Uge1xuICAgICAgdmFyIGVsZW0gPSB0aGlzLnBhcnNlTWF5YmVEZWZhdWx0KHRoaXMuc3RhcnQsIHRoaXMuc3RhcnRMb2MpO1xuICAgICAgdGhpcy5wYXJzZUJpbmRpbmdMaXN0SXRlbShlbGVtKTtcbiAgICAgIGVsdHMucHVzaChlbGVtKTtcbiAgICB9XG4gIH1cbiAgcmV0dXJuIGVsdHM7XG59O1xuXG5wcC5wYXJzZUJpbmRpbmdMaXN0SXRlbSA9IGZ1bmN0aW9uIChwYXJhbSkge1xuICByZXR1cm4gcGFyYW07XG59O1xuXG4vLyBQYXJzZXMgYXNzaWdubWVudCBwYXR0ZXJuIGFyb3VuZCBnaXZlbiBhdG9tIGlmIHBvc3NpYmxlLlxuXG5wcC5wYXJzZU1heWJlRGVmYXVsdCA9IGZ1bmN0aW9uIChzdGFydFBvcywgc3RhcnRMb2MsIGxlZnQpIHtcbiAgbGVmdCA9IGxlZnQgfHwgdGhpcy5wYXJzZUJpbmRpbmdBdG9tKCk7XG4gIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPCA2IHx8ICF0aGlzLmVhdChfdG9rZW50eXBlLnR5cGVzLmVxKSkgcmV0dXJuIGxlZnQ7XG4gIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGVBdChzdGFydFBvcywgc3RhcnRMb2MpO1xuICBub2RlLmxlZnQgPSBsZWZ0O1xuICBub2RlLnJpZ2h0ID0gdGhpcy5wYXJzZU1heWJlQXNzaWduKCk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJBc3NpZ25tZW50UGF0dGVyblwiKTtcbn07XG5cbi8vIFZlcmlmeSB0aGF0IGEgbm9kZSBpcyBhbiBsdmFsIOKAlCBzb21ldGhpbmcgdGhhdCBjYW4gYmUgYXNzaWduZWRcbi8vIHRvLlxuXG5wcC5jaGVja0xWYWwgPSBmdW5jdGlvbiAoZXhwciwgaXNCaW5kaW5nLCBjaGVja0NsYXNoZXMpIHtcbiAgc3dpdGNoIChleHByLnR5cGUpIHtcbiAgICBjYXNlIFwiSWRlbnRpZmllclwiOlxuICAgICAgaWYgKHRoaXMuc3RyaWN0ICYmIChfaWRlbnRpZmllci5yZXNlcnZlZFdvcmRzLnN0cmljdEJpbmQoZXhwci5uYW1lKSB8fCBfaWRlbnRpZmllci5yZXNlcnZlZFdvcmRzLnN0cmljdChleHByLm5hbWUpKSkgdGhpcy5yYWlzZShleHByLnN0YXJ0LCAoaXNCaW5kaW5nID8gXCJCaW5kaW5nIFwiIDogXCJBc3NpZ25pbmcgdG8gXCIpICsgZXhwci5uYW1lICsgXCIgaW4gc3RyaWN0IG1vZGVcIik7XG4gICAgICBpZiAoY2hlY2tDbGFzaGVzKSB7XG4gICAgICAgIGlmIChfdXRpbC5oYXMoY2hlY2tDbGFzaGVzLCBleHByLm5hbWUpKSB0aGlzLnJhaXNlKGV4cHIuc3RhcnQsIFwiQXJndW1lbnQgbmFtZSBjbGFzaCBpbiBzdHJpY3QgbW9kZVwiKTtcbiAgICAgICAgY2hlY2tDbGFzaGVzW2V4cHIubmFtZV0gPSB0cnVlO1xuICAgICAgfVxuICAgICAgYnJlYWs7XG5cbiAgICBjYXNlIFwiTWVtYmVyRXhwcmVzc2lvblwiOlxuICAgICAgaWYgKGlzQmluZGluZykgdGhpcy5yYWlzZShleHByLnN0YXJ0LCAoaXNCaW5kaW5nID8gXCJCaW5kaW5nXCIgOiBcIkFzc2lnbmluZyB0b1wiKSArIFwiIG1lbWJlciBleHByZXNzaW9uXCIpO1xuICAgICAgYnJlYWs7XG5cbiAgICBjYXNlIFwiT2JqZWN0UGF0dGVyblwiOlxuICAgICAgZm9yICh2YXIgaSA9IDA7IGkgPCBleHByLnByb3BlcnRpZXMubGVuZ3RoOyBpKyspIHtcbiAgICAgICAgdGhpcy5jaGVja0xWYWwoZXhwci5wcm9wZXJ0aWVzW2ldLnZhbHVlLCBpc0JpbmRpbmcsIGNoZWNrQ2xhc2hlcyk7XG4gICAgICB9YnJlYWs7XG5cbiAgICBjYXNlIFwiQXJyYXlQYXR0ZXJuXCI6XG4gICAgICBmb3IgKHZhciBpID0gMDsgaSA8IGV4cHIuZWxlbWVudHMubGVuZ3RoOyBpKyspIHtcbiAgICAgICAgdmFyIGVsZW0gPSBleHByLmVsZW1lbnRzW2ldO1xuICAgICAgICBpZiAoZWxlbSkgdGhpcy5jaGVja0xWYWwoZWxlbSwgaXNCaW5kaW5nLCBjaGVja0NsYXNoZXMpO1xuICAgICAgfVxuICAgICAgYnJlYWs7XG5cbiAgICBjYXNlIFwiQXNzaWdubWVudFBhdHRlcm5cIjpcbiAgICAgIHRoaXMuY2hlY2tMVmFsKGV4cHIubGVmdCwgaXNCaW5kaW5nLCBjaGVja0NsYXNoZXMpO1xuICAgICAgYnJlYWs7XG5cbiAgICBjYXNlIFwiUmVzdEVsZW1lbnRcIjpcbiAgICAgIHRoaXMuY2hlY2tMVmFsKGV4cHIuYXJndW1lbnQsIGlzQmluZGluZywgY2hlY2tDbGFzaGVzKTtcbiAgICAgIGJyZWFrO1xuXG4gICAgY2FzZSBcIlBhcmVudGhlc2l6ZWRFeHByZXNzaW9uXCI6XG4gICAgICB0aGlzLmNoZWNrTFZhbChleHByLmV4cHJlc3Npb24sIGlzQmluZGluZywgY2hlY2tDbGFzaGVzKTtcbiAgICAgIGJyZWFrO1xuXG4gICAgZGVmYXVsdDpcbiAgICAgIHRoaXMucmFpc2UoZXhwci5zdGFydCwgKGlzQmluZGluZyA/IFwiQmluZGluZ1wiIDogXCJBc3NpZ25pbmcgdG9cIikgKyBcIiBydmFsdWVcIik7XG4gIH1cbn07XG5cbn0se1wiLi9pZGVudGlmaWVyXCI6MixcIi4vc3RhdGVcIjoxMCxcIi4vdG9rZW50eXBlXCI6MTQsXCIuL3V0aWxcIjoxNX1dLDc6W2Z1bmN0aW9uKF9kZXJlcV8sbW9kdWxlLGV4cG9ydHMpe1xuXCJ1c2Ugc3RyaWN0XCI7XG5cbmV4cG9ydHMuX19lc01vZHVsZSA9IHRydWU7XG5cbmZ1bmN0aW9uIF9jbGFzc0NhbGxDaGVjayhpbnN0YW5jZSwgQ29uc3RydWN0b3IpIHsgaWYgKCEoaW5zdGFuY2UgaW5zdGFuY2VvZiBDb25zdHJ1Y3RvcikpIHsgdGhyb3cgbmV3IFR5cGVFcnJvcihcIkNhbm5vdCBjYWxsIGEgY2xhc3MgYXMgYSBmdW5jdGlvblwiKTsgfSB9XG5cbnZhciBfc3RhdGUgPSBfZGVyZXFfKFwiLi9zdGF0ZVwiKTtcblxudmFyIF9sb2N1dGlsID0gX2RlcmVxXyhcIi4vbG9jdXRpbFwiKTtcblxudmFyIE5vZGUgPSBmdW5jdGlvbiBOb2RlKHBhcnNlciwgcG9zLCBsb2MpIHtcbiAgX2NsYXNzQ2FsbENoZWNrKHRoaXMsIE5vZGUpO1xuXG4gIHRoaXMudHlwZSA9IFwiXCI7XG4gIHRoaXMuc3RhcnQgPSBwb3M7XG4gIHRoaXMuZW5kID0gMDtcbiAgaWYgKHBhcnNlci5vcHRpb25zLmxvY2F0aW9ucykgdGhpcy5sb2MgPSBuZXcgX2xvY3V0aWwuU291cmNlTG9jYXRpb24ocGFyc2VyLCBsb2MpO1xuICBpZiAocGFyc2VyLm9wdGlvbnMuZGlyZWN0U291cmNlRmlsZSkgdGhpcy5zb3VyY2VGaWxlID0gcGFyc2VyLm9wdGlvbnMuZGlyZWN0U291cmNlRmlsZTtcbiAgaWYgKHBhcnNlci5vcHRpb25zLnJhbmdlcykgdGhpcy5yYW5nZSA9IFtwb3MsIDBdO1xufTtcblxuZXhwb3J0cy5Ob2RlID0gTm9kZTtcblxuLy8gU3RhcnQgYW4gQVNUIG5vZGUsIGF0dGFjaGluZyBhIHN0YXJ0IG9mZnNldC5cblxudmFyIHBwID0gX3N0YXRlLlBhcnNlci5wcm90b3R5cGU7XG5cbnBwLnN0YXJ0Tm9kZSA9IGZ1bmN0aW9uICgpIHtcbiAgcmV0dXJuIG5ldyBOb2RlKHRoaXMsIHRoaXMuc3RhcnQsIHRoaXMuc3RhcnRMb2MpO1xufTtcblxucHAuc3RhcnROb2RlQXQgPSBmdW5jdGlvbiAocG9zLCBsb2MpIHtcbiAgcmV0dXJuIG5ldyBOb2RlKHRoaXMsIHBvcywgbG9jKTtcbn07XG5cbi8vIEZpbmlzaCBhbiBBU1Qgbm9kZSwgYWRkaW5nIGB0eXBlYCBhbmQgYGVuZGAgcHJvcGVydGllcy5cblxuZnVuY3Rpb24gZmluaXNoTm9kZUF0KG5vZGUsIHR5cGUsIHBvcywgbG9jKSB7XG4gIG5vZGUudHlwZSA9IHR5cGU7XG4gIG5vZGUuZW5kID0gcG9zO1xuICBpZiAodGhpcy5vcHRpb25zLmxvY2F0aW9ucykgbm9kZS5sb2MuZW5kID0gbG9jO1xuICBpZiAodGhpcy5vcHRpb25zLnJhbmdlcykgbm9kZS5yYW5nZVsxXSA9IHBvcztcbiAgcmV0dXJuIG5vZGU7XG59XG5cbnBwLmZpbmlzaE5vZGUgPSBmdW5jdGlvbiAobm9kZSwgdHlwZSkge1xuICByZXR1cm4gZmluaXNoTm9kZUF0LmNhbGwodGhpcywgbm9kZSwgdHlwZSwgdGhpcy5sYXN0VG9rRW5kLCB0aGlzLmxhc3RUb2tFbmRMb2MpO1xufTtcblxuLy8gRmluaXNoIG5vZGUgYXQgZ2l2ZW4gcG9zaXRpb25cblxucHAuZmluaXNoTm9kZUF0ID0gZnVuY3Rpb24gKG5vZGUsIHR5cGUsIHBvcywgbG9jKSB7XG4gIHJldHVybiBmaW5pc2hOb2RlQXQuY2FsbCh0aGlzLCBub2RlLCB0eXBlLCBwb3MsIGxvYyk7XG59O1xuXG59LHtcIi4vbG9jdXRpbFwiOjUsXCIuL3N0YXRlXCI6MTB9XSw4OltmdW5jdGlvbihfZGVyZXFfLG1vZHVsZSxleHBvcnRzKXtcblwidXNlIHN0cmljdFwiO1xuXG5leHBvcnRzLl9fZXNNb2R1bGUgPSB0cnVlO1xuZXhwb3J0cy5nZXRPcHRpb25zID0gZ2V0T3B0aW9ucztcblxudmFyIF91dGlsID0gX2RlcmVxXyhcIi4vdXRpbFwiKTtcblxudmFyIF9sb2N1dGlsID0gX2RlcmVxXyhcIi4vbG9jdXRpbFwiKTtcblxuLy8gQSBzZWNvbmQgb3B0aW9uYWwgYXJndW1lbnQgY2FuIGJlIGdpdmVuIHRvIGZ1cnRoZXIgY29uZmlndXJlXG4vLyB0aGUgcGFyc2VyIHByb2Nlc3MuIFRoZXNlIG9wdGlvbnMgYXJlIHJlY29nbml6ZWQ6XG5cbnZhciBkZWZhdWx0T3B0aW9ucyA9IHtcbiAgLy8gYGVjbWFWZXJzaW9uYCBpbmRpY2F0ZXMgdGhlIEVDTUFTY3JpcHQgdmVyc2lvbiB0byBwYXJzZS4gTXVzdFxuICAvLyBiZSBlaXRoZXIgMywgb3IgNSwgb3IgNi4gVGhpcyBpbmZsdWVuY2VzIHN1cHBvcnQgZm9yIHN0cmljdFxuICAvLyBtb2RlLCB0aGUgc2V0IG9mIHJlc2VydmVkIHdvcmRzLCBzdXBwb3J0IGZvciBnZXR0ZXJzIGFuZFxuICAvLyBzZXR0ZXJzIGFuZCBvdGhlciBmZWF0dXJlcy5cbiAgZWNtYVZlcnNpb246IDUsXG4gIC8vIFNvdXJjZSB0eXBlIChcInNjcmlwdFwiIG9yIFwibW9kdWxlXCIpIGZvciBkaWZmZXJlbnQgc2VtYW50aWNzXG4gIHNvdXJjZVR5cGU6IFwic2NyaXB0XCIsXG4gIC8vIGBvbkluc2VydGVkU2VtaWNvbG9uYCBjYW4gYmUgYSBjYWxsYmFjayB0aGF0IHdpbGwgYmUgY2FsbGVkXG4gIC8vIHdoZW4gYSBzZW1pY29sb24gaXMgYXV0b21hdGljYWxseSBpbnNlcnRlZC4gSXQgd2lsbCBiZSBwYXNzZWRcbiAgLy8gdGggcG9zaXRpb24gb2YgdGhlIGNvbW1hIGFzIGFuIG9mZnNldCwgYW5kIGlmIGBsb2NhdGlvbnNgIGlzXG4gIC8vIGVuYWJsZWQsIGl0IGlzIGdpdmVuIHRoZSBsb2NhdGlvbiBhcyBhIGB7bGluZSwgY29sdW1ufWAgb2JqZWN0XG4gIC8vIGFzIHNlY29uZCBhcmd1bWVudC5cbiAgb25JbnNlcnRlZFNlbWljb2xvbjogbnVsbCxcbiAgLy8gYG9uVHJhaWxpbmdDb21tYWAgaXMgc2ltaWxhciB0byBgb25JbnNlcnRlZFNlbWljb2xvbmAsIGJ1dCBmb3JcbiAgLy8gdHJhaWxpbmcgY29tbWFzLlxuICBvblRyYWlsaW5nQ29tbWE6IG51bGwsXG4gIC8vIEJ5IGRlZmF1bHQsIHJlc2VydmVkIHdvcmRzIGFyZSBub3QgZW5mb3JjZWQuIERpc2FibGVcbiAgLy8gYGFsbG93UmVzZXJ2ZWRgIHRvIGVuZm9yY2UgdGhlbS4gV2hlbiB0aGlzIG9wdGlvbiBoYXMgdGhlXG4gIC8vIHZhbHVlIFwibmV2ZXJcIiwgcmVzZXJ2ZWQgd29yZHMgYW5kIGtleXdvcmRzIGNhbiBhbHNvIG5vdCBiZVxuICAvLyB1c2VkIGFzIHByb3BlcnR5IG5hbWVzLlxuICBhbGxvd1Jlc2VydmVkOiB0cnVlLFxuICAvLyBXaGVuIGVuYWJsZWQsIGEgcmV0dXJuIGF0IHRoZSB0b3AgbGV2ZWwgaXMgbm90IGNvbnNpZGVyZWQgYW5cbiAgLy8gZXJyb3IuXG4gIGFsbG93UmV0dXJuT3V0c2lkZUZ1bmN0aW9uOiBmYWxzZSxcbiAgLy8gV2hlbiBlbmFibGVkLCBpbXBvcnQvZXhwb3J0IHN0YXRlbWVudHMgYXJlIG5vdCBjb25zdHJhaW5lZCB0b1xuICAvLyBhcHBlYXJpbmcgYXQgdGhlIHRvcCBvZiB0aGUgcHJvZ3JhbS5cbiAgYWxsb3dJbXBvcnRFeHBvcnRFdmVyeXdoZXJlOiBmYWxzZSxcbiAgLy8gV2hlbiBlbmFibGVkLCBoYXNoYmFuZyBkaXJlY3RpdmUgaW4gdGhlIGJlZ2lubmluZyBvZiBmaWxlXG4gIC8vIGlzIGFsbG93ZWQgYW5kIHRyZWF0ZWQgYXMgYSBsaW5lIGNvbW1lbnQuXG4gIGFsbG93SGFzaEJhbmc6IGZhbHNlLFxuICAvLyBXaGVuIGBsb2NhdGlvbnNgIGlzIG9uLCBgbG9jYCBwcm9wZXJ0aWVzIGhvbGRpbmcgb2JqZWN0cyB3aXRoXG4gIC8vIGBzdGFydGAgYW5kIGBlbmRgIHByb3BlcnRpZXMgaW4gYHtsaW5lLCBjb2x1bW59YCBmb3JtICh3aXRoXG4gIC8vIGxpbmUgYmVpbmcgMS1iYXNlZCBhbmQgY29sdW1uIDAtYmFzZWQpIHdpbGwgYmUgYXR0YWNoZWQgdG8gdGhlXG4gIC8vIG5vZGVzLlxuICBsb2NhdGlvbnM6IGZhbHNlLFxuICAvLyBBIGZ1bmN0aW9uIGNhbiBiZSBwYXNzZWQgYXMgYG9uVG9rZW5gIG9wdGlvbiwgd2hpY2ggd2lsbFxuICAvLyBjYXVzZSBBY29ybiB0byBjYWxsIHRoYXQgZnVuY3Rpb24gd2l0aCBvYmplY3QgaW4gdGhlIHNhbWVcbiAgLy8gZm9ybWF0IGFzIHRva2VuaXplKCkgcmV0dXJucy4gTm90ZSB0aGF0IHlvdSBhcmUgbm90XG4gIC8vIGFsbG93ZWQgdG8gY2FsbCB0aGUgcGFyc2VyIGZyb20gdGhlIGNhbGxiYWNr4oCUdGhhdCB3aWxsXG4gIC8vIGNvcnJ1cHQgaXRzIGludGVybmFsIHN0YXRlLlxuICBvblRva2VuOiBudWxsLFxuICAvLyBBIGZ1bmN0aW9uIGNhbiBiZSBwYXNzZWQgYXMgYG9uQ29tbWVudGAgb3B0aW9uLCB3aGljaCB3aWxsXG4gIC8vIGNhdXNlIEFjb3JuIHRvIGNhbGwgdGhhdCBmdW5jdGlvbiB3aXRoIGAoYmxvY2ssIHRleHQsIHN0YXJ0LFxuICAvLyBlbmQpYCBwYXJhbWV0ZXJzIHdoZW5ldmVyIGEgY29tbWVudCBpcyBza2lwcGVkLiBgYmxvY2tgIGlzIGFcbiAgLy8gYm9vbGVhbiBpbmRpY2F0aW5nIHdoZXRoZXIgdGhpcyBpcyBhIGJsb2NrIChgLyogKi9gKSBjb21tZW50LFxuICAvLyBgdGV4dGAgaXMgdGhlIGNvbnRlbnQgb2YgdGhlIGNvbW1lbnQsIGFuZCBgc3RhcnRgIGFuZCBgZW5kYCBhcmVcbiAgLy8gY2hhcmFjdGVyIG9mZnNldHMgdGhhdCBkZW5vdGUgdGhlIHN0YXJ0IGFuZCBlbmQgb2YgdGhlIGNvbW1lbnQuXG4gIC8vIFdoZW4gdGhlIGBsb2NhdGlvbnNgIG9wdGlvbiBpcyBvbiwgdHdvIG1vcmUgcGFyYW1ldGVycyBhcmVcbiAgLy8gcGFzc2VkLCB0aGUgZnVsbCBge2xpbmUsIGNvbHVtbn1gIGxvY2F0aW9ucyBvZiB0aGUgc3RhcnQgYW5kXG4gIC8vIGVuZCBvZiB0aGUgY29tbWVudHMuIE5vdGUgdGhhdCB5b3UgYXJlIG5vdCBhbGxvd2VkIHRvIGNhbGwgdGhlXG4gIC8vIHBhcnNlciBmcm9tIHRoZSBjYWxsYmFja+KAlHRoYXQgd2lsbCBjb3JydXB0IGl0cyBpbnRlcm5hbCBzdGF0ZS5cbiAgb25Db21tZW50OiBudWxsLFxuICAvLyBOb2RlcyBoYXZlIHRoZWlyIHN0YXJ0IGFuZCBlbmQgY2hhcmFjdGVycyBvZmZzZXRzIHJlY29yZGVkIGluXG4gIC8vIGBzdGFydGAgYW5kIGBlbmRgIHByb3BlcnRpZXMgKGRpcmVjdGx5IG9uIHRoZSBub2RlLCByYXRoZXIgdGhhblxuICAvLyB0aGUgYGxvY2Agb2JqZWN0LCB3aGljaCBob2xkcyBsaW5lL2NvbHVtbiBkYXRhLiBUbyBhbHNvIGFkZCBhXG4gIC8vIFtzZW1pLXN0YW5kYXJkaXplZF1bcmFuZ2VdIGByYW5nZWAgcHJvcGVydHkgaG9sZGluZyBhIGBbc3RhcnQsXG4gIC8vIGVuZF1gIGFycmF5IHdpdGggdGhlIHNhbWUgbnVtYmVycywgc2V0IHRoZSBgcmFuZ2VzYCBvcHRpb24gdG9cbiAgLy8gYHRydWVgLlxuICAvL1xuICAvLyBbcmFuZ2VdOiBodHRwczovL2J1Z3ppbGxhLm1vemlsbGEub3JnL3Nob3dfYnVnLmNnaT9pZD03NDU2NzhcbiAgcmFuZ2VzOiBmYWxzZSxcbiAgLy8gSXQgaXMgcG9zc2libGUgdG8gcGFyc2UgbXVsdGlwbGUgZmlsZXMgaW50byBhIHNpbmdsZSBBU1QgYnlcbiAgLy8gcGFzc2luZyB0aGUgdHJlZSBwcm9kdWNlZCBieSBwYXJzaW5nIHRoZSBmaXJzdCBmaWxlIGFzXG4gIC8vIGBwcm9ncmFtYCBvcHRpb24gaW4gc3Vic2VxdWVudCBwYXJzZXMuIFRoaXMgd2lsbCBhZGQgdGhlXG4gIC8vIHRvcGxldmVsIGZvcm1zIG9mIHRoZSBwYXJzZWQgZmlsZSB0byB0aGUgYFByb2dyYW1gICh0b3ApIG5vZGVcbiAgLy8gb2YgYW4gZXhpc3RpbmcgcGFyc2UgdHJlZS5cbiAgcHJvZ3JhbTogbnVsbCxcbiAgLy8gV2hlbiBgbG9jYXRpb25zYCBpcyBvbiwgeW91IGNhbiBwYXNzIHRoaXMgdG8gcmVjb3JkIHRoZSBzb3VyY2VcbiAgLy8gZmlsZSBpbiBldmVyeSBub2RlJ3MgYGxvY2Agb2JqZWN0LlxuICBzb3VyY2VGaWxlOiBudWxsLFxuICAvLyBUaGlzIHZhbHVlLCBpZiBnaXZlbiwgaXMgc3RvcmVkIGluIGV2ZXJ5IG5vZGUsIHdoZXRoZXJcbiAgLy8gYGxvY2F0aW9uc2AgaXMgb24gb3Igb2ZmLlxuICBkaXJlY3RTb3VyY2VGaWxlOiBudWxsLFxuICAvLyBXaGVuIGVuYWJsZWQsIHBhcmVudGhlc2l6ZWQgZXhwcmVzc2lvbnMgYXJlIHJlcHJlc2VudGVkIGJ5XG4gIC8vIChub24tc3RhbmRhcmQpIFBhcmVudGhlc2l6ZWRFeHByZXNzaW9uIG5vZGVzXG4gIHByZXNlcnZlUGFyZW5zOiBmYWxzZSxcbiAgcGx1Z2luczoge31cbn07XG5cbmV4cG9ydHMuZGVmYXVsdE9wdGlvbnMgPSBkZWZhdWx0T3B0aW9ucztcbi8vIEludGVycHJldCBhbmQgZGVmYXVsdCBhbiBvcHRpb25zIG9iamVjdFxuXG5mdW5jdGlvbiBnZXRPcHRpb25zKG9wdHMpIHtcbiAgdmFyIG9wdGlvbnMgPSB7fTtcbiAgZm9yICh2YXIgb3B0IGluIGRlZmF1bHRPcHRpb25zKSB7XG4gICAgb3B0aW9uc1tvcHRdID0gb3B0cyAmJiBfdXRpbC5oYXMob3B0cywgb3B0KSA/IG9wdHNbb3B0XSA6IGRlZmF1bHRPcHRpb25zW29wdF07XG4gIH1pZiAoX3V0aWwuaXNBcnJheShvcHRpb25zLm9uVG9rZW4pKSB7XG4gICAgKGZ1bmN0aW9uICgpIHtcbiAgICAgIHZhciB0b2tlbnMgPSBvcHRpb25zLm9uVG9rZW47XG4gICAgICBvcHRpb25zLm9uVG9rZW4gPSBmdW5jdGlvbiAodG9rZW4pIHtcbiAgICAgICAgcmV0dXJuIHRva2Vucy5wdXNoKHRva2VuKTtcbiAgICAgIH07XG4gICAgfSkoKTtcbiAgfVxuICBpZiAoX3V0aWwuaXNBcnJheShvcHRpb25zLm9uQ29tbWVudCkpIG9wdGlvbnMub25Db21tZW50ID0gcHVzaENvbW1lbnQob3B0aW9ucywgb3B0aW9ucy5vbkNvbW1lbnQpO1xuXG4gIHJldHVybiBvcHRpb25zO1xufVxuXG5mdW5jdGlvbiBwdXNoQ29tbWVudChvcHRpb25zLCBhcnJheSkge1xuICByZXR1cm4gZnVuY3Rpb24gKGJsb2NrLCB0ZXh0LCBzdGFydCwgZW5kLCBzdGFydExvYywgZW5kTG9jKSB7XG4gICAgdmFyIGNvbW1lbnQgPSB7XG4gICAgICB0eXBlOiBibG9jayA/IFwiQmxvY2tcIiA6IFwiTGluZVwiLFxuICAgICAgdmFsdWU6IHRleHQsXG4gICAgICBzdGFydDogc3RhcnQsXG4gICAgICBlbmQ6IGVuZFxuICAgIH07XG4gICAgaWYgKG9wdGlvbnMubG9jYXRpb25zKSBjb21tZW50LmxvYyA9IG5ldyBfbG9jdXRpbC5Tb3VyY2VMb2NhdGlvbih0aGlzLCBzdGFydExvYywgZW5kTG9jKTtcbiAgICBpZiAob3B0aW9ucy5yYW5nZXMpIGNvbW1lbnQucmFuZ2UgPSBbc3RhcnQsIGVuZF07XG4gICAgYXJyYXkucHVzaChjb21tZW50KTtcbiAgfTtcbn1cblxufSx7XCIuL2xvY3V0aWxcIjo1LFwiLi91dGlsXCI6MTV9XSw5OltmdW5jdGlvbihfZGVyZXFfLG1vZHVsZSxleHBvcnRzKXtcblwidXNlIHN0cmljdFwiO1xuXG52YXIgX3Rva2VudHlwZSA9IF9kZXJlcV8oXCIuL3Rva2VudHlwZVwiKTtcblxudmFyIF9zdGF0ZSA9IF9kZXJlcV8oXCIuL3N0YXRlXCIpO1xuXG52YXIgX3doaXRlc3BhY2UgPSBfZGVyZXFfKFwiLi93aGl0ZXNwYWNlXCIpO1xuXG52YXIgcHAgPSBfc3RhdGUuUGFyc2VyLnByb3RvdHlwZTtcblxuLy8gIyMgUGFyc2VyIHV0aWxpdGllc1xuXG4vLyBUZXN0IHdoZXRoZXIgYSBzdGF0ZW1lbnQgbm9kZSBpcyB0aGUgc3RyaW5nIGxpdGVyYWwgYFwidXNlIHN0cmljdFwiYC5cblxucHAuaXNVc2VTdHJpY3QgPSBmdW5jdGlvbiAoc3RtdCkge1xuICByZXR1cm4gdGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDUgJiYgc3RtdC50eXBlID09PSBcIkV4cHJlc3Npb25TdGF0ZW1lbnRcIiAmJiBzdG10LmV4cHJlc3Npb24udHlwZSA9PT0gXCJMaXRlcmFsXCIgJiYgc3RtdC5leHByZXNzaW9uLnJhdy5zbGljZSgxLCAtMSkgPT09IFwidXNlIHN0cmljdFwiO1xufTtcblxuLy8gUHJlZGljYXRlIHRoYXQgdGVzdHMgd2hldGhlciB0aGUgbmV4dCB0b2tlbiBpcyBvZiB0aGUgZ2l2ZW5cbi8vIHR5cGUsIGFuZCBpZiB5ZXMsIGNvbnN1bWVzIGl0IGFzIGEgc2lkZSBlZmZlY3QuXG5cbnBwLmVhdCA9IGZ1bmN0aW9uICh0eXBlKSB7XG4gIGlmICh0aGlzLnR5cGUgPT09IHR5cGUpIHtcbiAgICB0aGlzLm5leHQoKTtcbiAgICByZXR1cm4gdHJ1ZTtcbiAgfSBlbHNlIHtcbiAgICByZXR1cm4gZmFsc2U7XG4gIH1cbn07XG5cbi8vIFRlc3RzIHdoZXRoZXIgcGFyc2VkIHRva2VuIGlzIGEgY29udGV4dHVhbCBrZXl3b3JkLlxuXG5wcC5pc0NvbnRleHR1YWwgPSBmdW5jdGlvbiAobmFtZSkge1xuICByZXR1cm4gdGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLm5hbWUgJiYgdGhpcy52YWx1ZSA9PT0gbmFtZTtcbn07XG5cbi8vIENvbnN1bWVzIGNvbnRleHR1YWwga2V5d29yZCBpZiBwb3NzaWJsZS5cblxucHAuZWF0Q29udGV4dHVhbCA9IGZ1bmN0aW9uIChuYW1lKSB7XG4gIHJldHVybiB0aGlzLnZhbHVlID09PSBuYW1lICYmIHRoaXMuZWF0KF90b2tlbnR5cGUudHlwZXMubmFtZSk7XG59O1xuXG4vLyBBc3NlcnRzIHRoYXQgZm9sbG93aW5nIHRva2VuIGlzIGdpdmVuIGNvbnRleHR1YWwga2V5d29yZC5cblxucHAuZXhwZWN0Q29udGV4dHVhbCA9IGZ1bmN0aW9uIChuYW1lKSB7XG4gIGlmICghdGhpcy5lYXRDb250ZXh0dWFsKG5hbWUpKSB0aGlzLnVuZXhwZWN0ZWQoKTtcbn07XG5cbi8vIFRlc3Qgd2hldGhlciBhIHNlbWljb2xvbiBjYW4gYmUgaW5zZXJ0ZWQgYXQgdGhlIGN1cnJlbnQgcG9zaXRpb24uXG5cbnBwLmNhbkluc2VydFNlbWljb2xvbiA9IGZ1bmN0aW9uICgpIHtcbiAgcmV0dXJuIHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5lb2YgfHwgdGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLmJyYWNlUiB8fCBfd2hpdGVzcGFjZS5saW5lQnJlYWsudGVzdCh0aGlzLmlucHV0LnNsaWNlKHRoaXMubGFzdFRva0VuZCwgdGhpcy5zdGFydCkpO1xufTtcblxucHAuaW5zZXJ0U2VtaWNvbG9uID0gZnVuY3Rpb24gKCkge1xuICBpZiAodGhpcy5jYW5JbnNlcnRTZW1pY29sb24oKSkge1xuICAgIGlmICh0aGlzLm9wdGlvbnMub25JbnNlcnRlZFNlbWljb2xvbikgdGhpcy5vcHRpb25zLm9uSW5zZXJ0ZWRTZW1pY29sb24odGhpcy5sYXN0VG9rRW5kLCB0aGlzLmxhc3RUb2tFbmRMb2MpO1xuICAgIHJldHVybiB0cnVlO1xuICB9XG59O1xuXG4vLyBDb25zdW1lIGEgc2VtaWNvbG9uLCBvciwgZmFpbGluZyB0aGF0LCBzZWUgaWYgd2UgYXJlIGFsbG93ZWQgdG9cbi8vIHByZXRlbmQgdGhhdCB0aGVyZSBpcyBhIHNlbWljb2xvbiBhdCB0aGlzIHBvc2l0aW9uLlxuXG5wcC5zZW1pY29sb24gPSBmdW5jdGlvbiAoKSB7XG4gIGlmICghdGhpcy5lYXQoX3Rva2VudHlwZS50eXBlcy5zZW1pKSAmJiAhdGhpcy5pbnNlcnRTZW1pY29sb24oKSkgdGhpcy51bmV4cGVjdGVkKCk7XG59O1xuXG5wcC5hZnRlclRyYWlsaW5nQ29tbWEgPSBmdW5jdGlvbiAodG9rVHlwZSkge1xuICBpZiAodGhpcy50eXBlID09IHRva1R5cGUpIHtcbiAgICBpZiAodGhpcy5vcHRpb25zLm9uVHJhaWxpbmdDb21tYSkgdGhpcy5vcHRpb25zLm9uVHJhaWxpbmdDb21tYSh0aGlzLmxhc3RUb2tTdGFydCwgdGhpcy5sYXN0VG9rU3RhcnRMb2MpO1xuICAgIHRoaXMubmV4dCgpO1xuICAgIHJldHVybiB0cnVlO1xuICB9XG59O1xuXG4vLyBFeHBlY3QgYSB0b2tlbiBvZiBhIGdpdmVuIHR5cGUuIElmIGZvdW5kLCBjb25zdW1lIGl0LCBvdGhlcndpc2UsXG4vLyByYWlzZSBhbiB1bmV4cGVjdGVkIHRva2VuIGVycm9yLlxuXG5wcC5leHBlY3QgPSBmdW5jdGlvbiAodHlwZSkge1xuICB0aGlzLmVhdCh0eXBlKSB8fCB0aGlzLnVuZXhwZWN0ZWQoKTtcbn07XG5cbi8vIFJhaXNlIGFuIHVuZXhwZWN0ZWQgdG9rZW4gZXJyb3IuXG5cbnBwLnVuZXhwZWN0ZWQgPSBmdW5jdGlvbiAocG9zKSB7XG4gIHRoaXMucmFpc2UocG9zICE9IG51bGwgPyBwb3MgOiB0aGlzLnN0YXJ0LCBcIlVuZXhwZWN0ZWQgdG9rZW5cIik7XG59O1xuXG59LHtcIi4vc3RhdGVcIjoxMCxcIi4vdG9rZW50eXBlXCI6MTQsXCIuL3doaXRlc3BhY2VcIjoxNn1dLDEwOltmdW5jdGlvbihfZGVyZXFfLG1vZHVsZSxleHBvcnRzKXtcblwidXNlIHN0cmljdFwiO1xuXG5leHBvcnRzLl9fZXNNb2R1bGUgPSB0cnVlO1xuXG5mdW5jdGlvbiBfY2xhc3NDYWxsQ2hlY2soaW5zdGFuY2UsIENvbnN0cnVjdG9yKSB7IGlmICghKGluc3RhbmNlIGluc3RhbmNlb2YgQ29uc3RydWN0b3IpKSB7IHRocm93IG5ldyBUeXBlRXJyb3IoXCJDYW5ub3QgY2FsbCBhIGNsYXNzIGFzIGEgZnVuY3Rpb25cIik7IH0gfVxuXG52YXIgX2lkZW50aWZpZXIgPSBfZGVyZXFfKFwiLi9pZGVudGlmaWVyXCIpO1xuXG52YXIgX3Rva2VudHlwZSA9IF9kZXJlcV8oXCIuL3Rva2VudHlwZVwiKTtcblxudmFyIF93aGl0ZXNwYWNlID0gX2RlcmVxXyhcIi4vd2hpdGVzcGFjZVwiKTtcblxudmFyIF9vcHRpb25zID0gX2RlcmVxXyhcIi4vb3B0aW9uc1wiKTtcblxuLy8gUmVnaXN0ZXJlZCBwbHVnaW5zXG52YXIgcGx1Z2lucyA9IHt9O1xuXG5leHBvcnRzLnBsdWdpbnMgPSBwbHVnaW5zO1xuXG52YXIgUGFyc2VyID0gKGZ1bmN0aW9uICgpIHtcbiAgZnVuY3Rpb24gUGFyc2VyKG9wdGlvbnMsIGlucHV0LCBzdGFydFBvcykge1xuICAgIF9jbGFzc0NhbGxDaGVjayh0aGlzLCBQYXJzZXIpO1xuXG4gICAgdGhpcy5vcHRpb25zID0gX29wdGlvbnMuZ2V0T3B0aW9ucyhvcHRpb25zKTtcbiAgICB0aGlzLnNvdXJjZUZpbGUgPSB0aGlzLm9wdGlvbnMuc291cmNlRmlsZTtcbiAgICB0aGlzLmlzS2V5d29yZCA9IF9pZGVudGlmaWVyLmtleXdvcmRzW3RoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2ID8gNiA6IDVdO1xuICAgIHRoaXMuaXNSZXNlcnZlZFdvcmQgPSBfaWRlbnRpZmllci5yZXNlcnZlZFdvcmRzW3RoaXMub3B0aW9ucy5lY21hVmVyc2lvbl07XG4gICAgdGhpcy5pbnB1dCA9IFN0cmluZyhpbnB1dCk7XG5cbiAgICAvLyBVc2VkIHRvIHNpZ25hbCB0byBjYWxsZXJzIG9mIGByZWFkV29yZDFgIHdoZXRoZXIgdGhlIHdvcmRcbiAgICAvLyBjb250YWluZWQgYW55IGVzY2FwZSBzZXF1ZW5jZXMuIFRoaXMgaXMgbmVlZGVkIGJlY2F1c2Ugd29yZHMgd2l0aFxuICAgIC8vIGVzY2FwZSBzZXF1ZW5jZXMgbXVzdCBub3QgYmUgaW50ZXJwcmV0ZWQgYXMga2V5d29yZHMuXG4gICAgdGhpcy5jb250YWluc0VzYyA9IGZhbHNlO1xuXG4gICAgLy8gTG9hZCBwbHVnaW5zXG4gICAgdGhpcy5sb2FkUGx1Z2lucyh0aGlzLm9wdGlvbnMucGx1Z2lucyk7XG5cbiAgICAvLyBTZXQgdXAgdG9rZW4gc3RhdGVcblxuICAgIC8vIFRoZSBjdXJyZW50IHBvc2l0aW9uIG9mIHRoZSB0b2tlbml6ZXIgaW4gdGhlIGlucHV0LlxuICAgIGlmIChzdGFydFBvcykge1xuICAgICAgdGhpcy5wb3MgPSBzdGFydFBvcztcbiAgICAgIHRoaXMubGluZVN0YXJ0ID0gTWF0aC5tYXgoMCwgdGhpcy5pbnB1dC5sYXN0SW5kZXhPZihcIlxcblwiLCBzdGFydFBvcykpO1xuICAgICAgdGhpcy5jdXJMaW5lID0gdGhpcy5pbnB1dC5zbGljZSgwLCB0aGlzLmxpbmVTdGFydCkuc3BsaXQoX3doaXRlc3BhY2UubGluZUJyZWFrKS5sZW5ndGg7XG4gICAgfSBlbHNlIHtcbiAgICAgIHRoaXMucG9zID0gdGhpcy5saW5lU3RhcnQgPSAwO1xuICAgICAgdGhpcy5jdXJMaW5lID0gMTtcbiAgICB9XG5cbiAgICAvLyBQcm9wZXJ0aWVzIG9mIHRoZSBjdXJyZW50IHRva2VuOlxuICAgIC8vIEl0cyB0eXBlXG4gICAgdGhpcy50eXBlID0gX3Rva2VudHlwZS50eXBlcy5lb2Y7XG4gICAgLy8gRm9yIHRva2VucyB0aGF0IGluY2x1ZGUgbW9yZSBpbmZvcm1hdGlvbiB0aGFuIHRoZWlyIHR5cGUsIHRoZSB2YWx1ZVxuICAgIHRoaXMudmFsdWUgPSBudWxsO1xuICAgIC8vIEl0cyBzdGFydCBhbmQgZW5kIG9mZnNldFxuICAgIHRoaXMuc3RhcnQgPSB0aGlzLmVuZCA9IHRoaXMucG9zO1xuICAgIC8vIEFuZCwgaWYgbG9jYXRpb25zIGFyZSB1c2VkLCB0aGUge2xpbmUsIGNvbHVtbn0gb2JqZWN0XG4gICAgLy8gY29ycmVzcG9uZGluZyB0byB0aG9zZSBvZmZzZXRzXG4gICAgdGhpcy5zdGFydExvYyA9IHRoaXMuZW5kTG9jID0gdGhpcy5jdXJQb3NpdGlvbigpO1xuXG4gICAgLy8gUG9zaXRpb24gaW5mb3JtYXRpb24gZm9yIHRoZSBwcmV2aW91cyB0b2tlblxuICAgIHRoaXMubGFzdFRva0VuZExvYyA9IHRoaXMubGFzdFRva1N0YXJ0TG9jID0gbnVsbDtcbiAgICB0aGlzLmxhc3RUb2tTdGFydCA9IHRoaXMubGFzdFRva0VuZCA9IHRoaXMucG9zO1xuXG4gICAgLy8gVGhlIGNvbnRleHQgc3RhY2sgaXMgdXNlZCB0byBzdXBlcmZpY2lhbGx5IHRyYWNrIHN5bnRhY3RpY1xuICAgIC8vIGNvbnRleHQgdG8gcHJlZGljdCB3aGV0aGVyIGEgcmVndWxhciBleHByZXNzaW9uIGlzIGFsbG93ZWQgaW4gYVxuICAgIC8vIGdpdmVuIHBvc2l0aW9uLlxuICAgIHRoaXMuY29udGV4dCA9IHRoaXMuaW5pdGlhbENvbnRleHQoKTtcbiAgICB0aGlzLmV4cHJBbGxvd2VkID0gdHJ1ZTtcblxuICAgIC8vIEZpZ3VyZSBvdXQgaWYgaXQncyBhIG1vZHVsZSBjb2RlLlxuICAgIHRoaXMuc3RyaWN0ID0gdGhpcy5pbk1vZHVsZSA9IHRoaXMub3B0aW9ucy5zb3VyY2VUeXBlID09PSBcIm1vZHVsZVwiO1xuXG4gICAgLy8gVXNlZCB0byBzaWduaWZ5IHRoZSBzdGFydCBvZiBhIHBvdGVudGlhbCBhcnJvdyBmdW5jdGlvblxuICAgIHRoaXMucG90ZW50aWFsQXJyb3dBdCA9IC0xO1xuXG4gICAgLy8gRmxhZ3MgdG8gdHJhY2sgd2hldGhlciB3ZSBhcmUgaW4gYSBmdW5jdGlvbiwgYSBnZW5lcmF0b3IuXG4gICAgdGhpcy5pbkZ1bmN0aW9uID0gdGhpcy5pbkdlbmVyYXRvciA9IGZhbHNlO1xuICAgIC8vIExhYmVscyBpbiBzY29wZS5cbiAgICB0aGlzLmxhYmVscyA9IFtdO1xuXG4gICAgLy8gSWYgZW5hYmxlZCwgc2tpcCBsZWFkaW5nIGhhc2hiYW5nIGxpbmUuXG4gICAgaWYgKHRoaXMucG9zID09PSAwICYmIHRoaXMub3B0aW9ucy5hbGxvd0hhc2hCYW5nICYmIHRoaXMuaW5wdXQuc2xpY2UoMCwgMikgPT09IFwiIyFcIikgdGhpcy5za2lwTGluZUNvbW1lbnQoMik7XG4gIH1cblxuICBQYXJzZXIucHJvdG90eXBlLmV4dGVuZCA9IGZ1bmN0aW9uIGV4dGVuZChuYW1lLCBmKSB7XG4gICAgdGhpc1tuYW1lXSA9IGYodGhpc1tuYW1lXSk7XG4gIH07XG5cbiAgUGFyc2VyLnByb3RvdHlwZS5sb2FkUGx1Z2lucyA9IGZ1bmN0aW9uIGxvYWRQbHVnaW5zKHBsdWdpbkNvbmZpZ3MpIHtcbiAgICBmb3IgKHZhciBfbmFtZSBpbiBwbHVnaW5Db25maWdzKSB7XG4gICAgICB2YXIgcGx1Z2luID0gcGx1Z2luc1tfbmFtZV07XG4gICAgICBpZiAoIXBsdWdpbikgdGhyb3cgbmV3IEVycm9yKFwiUGx1Z2luICdcIiArIF9uYW1lICsgXCInIG5vdCBmb3VuZFwiKTtcbiAgICAgIHBsdWdpbih0aGlzLCBwbHVnaW5Db25maWdzW19uYW1lXSk7XG4gICAgfVxuICB9O1xuXG4gIFBhcnNlci5wcm90b3R5cGUucGFyc2UgPSBmdW5jdGlvbiBwYXJzZSgpIHtcbiAgICB2YXIgbm9kZSA9IHRoaXMub3B0aW9ucy5wcm9ncmFtIHx8IHRoaXMuc3RhcnROb2RlKCk7XG4gICAgdGhpcy5uZXh0VG9rZW4oKTtcbiAgICByZXR1cm4gdGhpcy5wYXJzZVRvcExldmVsKG5vZGUpO1xuICB9O1xuXG4gIHJldHVybiBQYXJzZXI7XG59KSgpO1xuXG5leHBvcnRzLlBhcnNlciA9IFBhcnNlcjtcblxufSx7XCIuL2lkZW50aWZpZXJcIjoyLFwiLi9vcHRpb25zXCI6OCxcIi4vdG9rZW50eXBlXCI6MTQsXCIuL3doaXRlc3BhY2VcIjoxNn1dLDExOltmdW5jdGlvbihfZGVyZXFfLG1vZHVsZSxleHBvcnRzKXtcblwidXNlIHN0cmljdFwiO1xuXG52YXIgX3Rva2VudHlwZSA9IF9kZXJlcV8oXCIuL3Rva2VudHlwZVwiKTtcblxudmFyIF9zdGF0ZSA9IF9kZXJlcV8oXCIuL3N0YXRlXCIpO1xuXG52YXIgX3doaXRlc3BhY2UgPSBfZGVyZXFfKFwiLi93aGl0ZXNwYWNlXCIpO1xuXG52YXIgcHAgPSBfc3RhdGUuUGFyc2VyLnByb3RvdHlwZTtcblxuLy8gIyMjIFN0YXRlbWVudCBwYXJzaW5nXG5cbi8vIFBhcnNlIGEgcHJvZ3JhbS4gSW5pdGlhbGl6ZXMgdGhlIHBhcnNlciwgcmVhZHMgYW55IG51bWJlciBvZlxuLy8gc3RhdGVtZW50cywgYW5kIHdyYXBzIHRoZW0gaW4gYSBQcm9ncmFtIG5vZGUuICBPcHRpb25hbGx5IHRha2VzIGFcbi8vIGBwcm9ncmFtYCBhcmd1bWVudC4gIElmIHByZXNlbnQsIHRoZSBzdGF0ZW1lbnRzIHdpbGwgYmUgYXBwZW5kZWRcbi8vIHRvIGl0cyBib2R5IGluc3RlYWQgb2YgY3JlYXRpbmcgYSBuZXcgbm9kZS5cblxucHAucGFyc2VUb3BMZXZlbCA9IGZ1bmN0aW9uIChub2RlKSB7XG4gIHZhciBmaXJzdCA9IHRydWU7XG4gIGlmICghbm9kZS5ib2R5KSBub2RlLmJvZHkgPSBbXTtcbiAgd2hpbGUgKHRoaXMudHlwZSAhPT0gX3Rva2VudHlwZS50eXBlcy5lb2YpIHtcbiAgICB2YXIgc3RtdCA9IHRoaXMucGFyc2VTdGF0ZW1lbnQodHJ1ZSwgdHJ1ZSk7XG4gICAgbm9kZS5ib2R5LnB1c2goc3RtdCk7XG4gICAgaWYgKGZpcnN0KSB7XG4gICAgICBpZiAodGhpcy5pc1VzZVN0cmljdChzdG10KSkgdGhpcy5zZXRTdHJpY3QodHJ1ZSk7XG4gICAgICBmaXJzdCA9IGZhbHNlO1xuICAgIH1cbiAgfVxuICB0aGlzLm5leHQoKTtcbiAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KSB7XG4gICAgbm9kZS5zb3VyY2VUeXBlID0gdGhpcy5vcHRpb25zLnNvdXJjZVR5cGU7XG4gIH1cbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIlByb2dyYW1cIik7XG59O1xuXG52YXIgbG9vcExhYmVsID0geyBraW5kOiBcImxvb3BcIiB9LFxuICAgIHN3aXRjaExhYmVsID0geyBraW5kOiBcInN3aXRjaFwiIH07XG5cbi8vIFBhcnNlIGEgc2luZ2xlIHN0YXRlbWVudC5cbi8vXG4vLyBJZiBleHBlY3RpbmcgYSBzdGF0ZW1lbnQgYW5kIGZpbmRpbmcgYSBzbGFzaCBvcGVyYXRvciwgcGFyc2UgYVxuLy8gcmVndWxhciBleHByZXNzaW9uIGxpdGVyYWwuIFRoaXMgaXMgdG8gaGFuZGxlIGNhc2VzIGxpa2Vcbi8vIGBpZiAoZm9vKSAvYmxhaC8uZXhlYyhmb28pYCwgd2hlcmUgbG9va2luZyBhdCB0aGUgcHJldmlvdXMgdG9rZW5cbi8vIGRvZXMgbm90IGhlbHAuXG5cbnBwLnBhcnNlU3RhdGVtZW50ID0gZnVuY3Rpb24gKGRlY2xhcmF0aW9uLCB0b3BMZXZlbCkge1xuICB2YXIgc3RhcnR0eXBlID0gdGhpcy50eXBlLFxuICAgICAgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG5cbiAgLy8gTW9zdCB0eXBlcyBvZiBzdGF0ZW1lbnRzIGFyZSByZWNvZ25pemVkIGJ5IHRoZSBrZXl3b3JkIHRoZXlcbiAgLy8gc3RhcnQgd2l0aC4gTWFueSBhcmUgdHJpdmlhbCB0byBwYXJzZSwgc29tZSByZXF1aXJlIGEgYml0IG9mXG4gIC8vIGNvbXBsZXhpdHkuXG5cbiAgc3dpdGNoIChzdGFydHR5cGUpIHtcbiAgICBjYXNlIF90b2tlbnR5cGUudHlwZXMuX2JyZWFrOmNhc2UgX3Rva2VudHlwZS50eXBlcy5fY29udGludWU6XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZUJyZWFrQ29udGludWVTdGF0ZW1lbnQobm9kZSwgc3RhcnR0eXBlLmtleXdvcmQpO1xuICAgIGNhc2UgX3Rva2VudHlwZS50eXBlcy5fZGVidWdnZXI6XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZURlYnVnZ2VyU3RhdGVtZW50KG5vZGUpO1xuICAgIGNhc2UgX3Rva2VudHlwZS50eXBlcy5fZG86XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZURvU3RhdGVtZW50KG5vZGUpO1xuICAgIGNhc2UgX3Rva2VudHlwZS50eXBlcy5fZm9yOlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VGb3JTdGF0ZW1lbnQobm9kZSk7XG4gICAgY2FzZSBfdG9rZW50eXBlLnR5cGVzLl9mdW5jdGlvbjpcbiAgICAgIGlmICghZGVjbGFyYXRpb24gJiYgdGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYpIHRoaXMudW5leHBlY3RlZCgpO1xuICAgICAgcmV0dXJuIHRoaXMucGFyc2VGdW5jdGlvblN0YXRlbWVudChub2RlKTtcbiAgICBjYXNlIF90b2tlbnR5cGUudHlwZXMuX2NsYXNzOlxuICAgICAgaWYgKCFkZWNsYXJhdGlvbikgdGhpcy51bmV4cGVjdGVkKCk7XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZUNsYXNzKG5vZGUsIHRydWUpO1xuICAgIGNhc2UgX3Rva2VudHlwZS50eXBlcy5faWY6XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZUlmU3RhdGVtZW50KG5vZGUpO1xuICAgIGNhc2UgX3Rva2VudHlwZS50eXBlcy5fcmV0dXJuOlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VSZXR1cm5TdGF0ZW1lbnQobm9kZSk7XG4gICAgY2FzZSBfdG9rZW50eXBlLnR5cGVzLl9zd2l0Y2g6XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZVN3aXRjaFN0YXRlbWVudChub2RlKTtcbiAgICBjYXNlIF90b2tlbnR5cGUudHlwZXMuX3Rocm93OlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VUaHJvd1N0YXRlbWVudChub2RlKTtcbiAgICBjYXNlIF90b2tlbnR5cGUudHlwZXMuX3RyeTpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlVHJ5U3RhdGVtZW50KG5vZGUpO1xuICAgIGNhc2UgX3Rva2VudHlwZS50eXBlcy5fbGV0OmNhc2UgX3Rva2VudHlwZS50eXBlcy5fY29uc3Q6XG4gICAgICBpZiAoIWRlY2xhcmF0aW9uKSB0aGlzLnVuZXhwZWN0ZWQoKTsgLy8gTk9URTogZmFsbHMgdGhyb3VnaCB0byBfdmFyXG4gICAgY2FzZSBfdG9rZW50eXBlLnR5cGVzLl92YXI6XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZVZhclN0YXRlbWVudChub2RlLCBzdGFydHR5cGUpO1xuICAgIGNhc2UgX3Rva2VudHlwZS50eXBlcy5fd2hpbGU6XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZVdoaWxlU3RhdGVtZW50KG5vZGUpO1xuICAgIGNhc2UgX3Rva2VudHlwZS50eXBlcy5fd2l0aDpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlV2l0aFN0YXRlbWVudChub2RlKTtcbiAgICBjYXNlIF90b2tlbnR5cGUudHlwZXMuYnJhY2VMOlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VCbG9jaygpO1xuICAgIGNhc2UgX3Rva2VudHlwZS50eXBlcy5zZW1pOlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VFbXB0eVN0YXRlbWVudChub2RlKTtcbiAgICBjYXNlIF90b2tlbnR5cGUudHlwZXMuX2V4cG9ydDpcbiAgICBjYXNlIF90b2tlbnR5cGUudHlwZXMuX2ltcG9ydDpcbiAgICAgIGlmICghdGhpcy5vcHRpb25zLmFsbG93SW1wb3J0RXhwb3J0RXZlcnl3aGVyZSkge1xuICAgICAgICBpZiAoIXRvcExldmVsKSB0aGlzLnJhaXNlKHRoaXMuc3RhcnQsIFwiJ2ltcG9ydCcgYW5kICdleHBvcnQnIG1heSBvbmx5IGFwcGVhciBhdCB0aGUgdG9wIGxldmVsXCIpO1xuICAgICAgICBpZiAoIXRoaXMuaW5Nb2R1bGUpIHRoaXMucmFpc2UodGhpcy5zdGFydCwgXCInaW1wb3J0JyBhbmQgJ2V4cG9ydCcgbWF5IGFwcGVhciBvbmx5IHdpdGggJ3NvdXJjZVR5cGU6IG1vZHVsZSdcIik7XG4gICAgICB9XG4gICAgICByZXR1cm4gc3RhcnR0eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLl9pbXBvcnQgPyB0aGlzLnBhcnNlSW1wb3J0KG5vZGUpIDogdGhpcy5wYXJzZUV4cG9ydChub2RlKTtcblxuICAgIC8vIElmIHRoZSBzdGF0ZW1lbnQgZG9lcyBub3Qgc3RhcnQgd2l0aCBhIHN0YXRlbWVudCBrZXl3b3JkIG9yIGFcbiAgICAvLyBicmFjZSwgaXQncyBhbiBFeHByZXNzaW9uU3RhdGVtZW50IG9yIExhYmVsZWRTdGF0ZW1lbnQuIFdlXG4gICAgLy8gc2ltcGx5IHN0YXJ0IHBhcnNpbmcgYW4gZXhwcmVzc2lvbiwgYW5kIGFmdGVyd2FyZHMsIGlmIHRoZVxuICAgIC8vIG5leHQgdG9rZW4gaXMgYSBjb2xvbiBhbmQgdGhlIGV4cHJlc3Npb24gd2FzIGEgc2ltcGxlXG4gICAgLy8gSWRlbnRpZmllciBub2RlLCB3ZSBzd2l0Y2ggdG8gaW50ZXJwcmV0aW5nIGl0IGFzIGEgbGFiZWwuXG4gICAgZGVmYXVsdDpcbiAgICAgIHZhciBtYXliZU5hbWUgPSB0aGlzLnZhbHVlLFxuICAgICAgICAgIGV4cHIgPSB0aGlzLnBhcnNlRXhwcmVzc2lvbigpO1xuICAgICAgaWYgKHN0YXJ0dHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5uYW1lICYmIGV4cHIudHlwZSA9PT0gXCJJZGVudGlmaWVyXCIgJiYgdGhpcy5lYXQoX3Rva2VudHlwZS50eXBlcy5jb2xvbikpIHJldHVybiB0aGlzLnBhcnNlTGFiZWxlZFN0YXRlbWVudChub2RlLCBtYXliZU5hbWUsIGV4cHIpO2Vsc2UgcmV0dXJuIHRoaXMucGFyc2VFeHByZXNzaW9uU3RhdGVtZW50KG5vZGUsIGV4cHIpO1xuICB9XG59O1xuXG5wcC5wYXJzZUJyZWFrQ29udGludWVTdGF0ZW1lbnQgPSBmdW5jdGlvbiAobm9kZSwga2V5d29yZCkge1xuICB2YXIgaXNCcmVhayA9IGtleXdvcmQgPT0gXCJicmVha1wiO1xuICB0aGlzLm5leHQoKTtcbiAgaWYgKHRoaXMuZWF0KF90b2tlbnR5cGUudHlwZXMuc2VtaSkgfHwgdGhpcy5pbnNlcnRTZW1pY29sb24oKSkgbm9kZS5sYWJlbCA9IG51bGw7ZWxzZSBpZiAodGhpcy50eXBlICE9PSBfdG9rZW50eXBlLnR5cGVzLm5hbWUpIHRoaXMudW5leHBlY3RlZCgpO2Vsc2Uge1xuICAgIG5vZGUubGFiZWwgPSB0aGlzLnBhcnNlSWRlbnQoKTtcbiAgICB0aGlzLnNlbWljb2xvbigpO1xuICB9XG5cbiAgLy8gVmVyaWZ5IHRoYXQgdGhlcmUgaXMgYW4gYWN0dWFsIGRlc3RpbmF0aW9uIHRvIGJyZWFrIG9yXG4gIC8vIGNvbnRpbnVlIHRvLlxuICBmb3IgKHZhciBpID0gMDsgaSA8IHRoaXMubGFiZWxzLmxlbmd0aDsgKytpKSB7XG4gICAgdmFyIGxhYiA9IHRoaXMubGFiZWxzW2ldO1xuICAgIGlmIChub2RlLmxhYmVsID09IG51bGwgfHwgbGFiLm5hbWUgPT09IG5vZGUubGFiZWwubmFtZSkge1xuICAgICAgaWYgKGxhYi5raW5kICE9IG51bGwgJiYgKGlzQnJlYWsgfHwgbGFiLmtpbmQgPT09IFwibG9vcFwiKSkgYnJlYWs7XG4gICAgICBpZiAobm9kZS5sYWJlbCAmJiBpc0JyZWFrKSBicmVhaztcbiAgICB9XG4gIH1cbiAgaWYgKGkgPT09IHRoaXMubGFiZWxzLmxlbmd0aCkgdGhpcy5yYWlzZShub2RlLnN0YXJ0LCBcIlVuc3ludGFjdGljIFwiICsga2V5d29yZCk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgaXNCcmVhayA/IFwiQnJlYWtTdGF0ZW1lbnRcIiA6IFwiQ29udGludWVTdGF0ZW1lbnRcIik7XG59O1xuXG5wcC5wYXJzZURlYnVnZ2VyU3RhdGVtZW50ID0gZnVuY3Rpb24gKG5vZGUpIHtcbiAgdGhpcy5uZXh0KCk7XG4gIHRoaXMuc2VtaWNvbG9uKCk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJEZWJ1Z2dlclN0YXRlbWVudFwiKTtcbn07XG5cbnBwLnBhcnNlRG9TdGF0ZW1lbnQgPSBmdW5jdGlvbiAobm9kZSkge1xuICB0aGlzLm5leHQoKTtcbiAgdGhpcy5sYWJlbHMucHVzaChsb29wTGFiZWwpO1xuICBub2RlLmJvZHkgPSB0aGlzLnBhcnNlU3RhdGVtZW50KGZhbHNlKTtcbiAgdGhpcy5sYWJlbHMucG9wKCk7XG4gIHRoaXMuZXhwZWN0KF90b2tlbnR5cGUudHlwZXMuX3doaWxlKTtcbiAgbm9kZS50ZXN0ID0gdGhpcy5wYXJzZVBhcmVuRXhwcmVzc2lvbigpO1xuICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYpIHRoaXMuZWF0KF90b2tlbnR5cGUudHlwZXMuc2VtaSk7ZWxzZSB0aGlzLnNlbWljb2xvbigpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiRG9XaGlsZVN0YXRlbWVudFwiKTtcbn07XG5cbi8vIERpc2FtYmlndWF0aW5nIGJldHdlZW4gYSBgZm9yYCBhbmQgYSBgZm9yYC9gaW5gIG9yIGBmb3JgL2BvZmBcbi8vIGxvb3AgaXMgbm9uLXRyaXZpYWwuIEJhc2ljYWxseSwgd2UgaGF2ZSB0byBwYXJzZSB0aGUgaW5pdCBgdmFyYFxuLy8gc3RhdGVtZW50IG9yIGV4cHJlc3Npb24sIGRpc2FsbG93aW5nIHRoZSBgaW5gIG9wZXJhdG9yIChzZWVcbi8vIHRoZSBzZWNvbmQgcGFyYW1ldGVyIHRvIGBwYXJzZUV4cHJlc3Npb25gKSwgYW5kIHRoZW4gY2hlY2tcbi8vIHdoZXRoZXIgdGhlIG5leHQgdG9rZW4gaXMgYGluYCBvciBgb2ZgLiBXaGVuIHRoZXJlIGlzIG5vIGluaXRcbi8vIHBhcnQgKHNlbWljb2xvbiBpbW1lZGlhdGVseSBhZnRlciB0aGUgb3BlbmluZyBwYXJlbnRoZXNpcyksIGl0XG4vLyBpcyBhIHJlZ3VsYXIgYGZvcmAgbG9vcC5cblxucHAucGFyc2VGb3JTdGF0ZW1lbnQgPSBmdW5jdGlvbiAobm9kZSkge1xuICB0aGlzLm5leHQoKTtcbiAgdGhpcy5sYWJlbHMucHVzaChsb29wTGFiZWwpO1xuICB0aGlzLmV4cGVjdChfdG9rZW50eXBlLnR5cGVzLnBhcmVuTCk7XG4gIGlmICh0aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuc2VtaSkgcmV0dXJuIHRoaXMucGFyc2VGb3Iobm9kZSwgbnVsbCk7XG4gIGlmICh0aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuX3ZhciB8fCB0aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuX2xldCB8fCB0aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuX2NvbnN0KSB7XG4gICAgdmFyIF9pbml0ID0gdGhpcy5zdGFydE5vZGUoKSxcbiAgICAgICAgdmFyS2luZCA9IHRoaXMudHlwZTtcbiAgICB0aGlzLm5leHQoKTtcbiAgICB0aGlzLnBhcnNlVmFyKF9pbml0LCB0cnVlLCB2YXJLaW5kKTtcbiAgICB0aGlzLmZpbmlzaE5vZGUoX2luaXQsIFwiVmFyaWFibGVEZWNsYXJhdGlvblwiKTtcbiAgICBpZiAoKHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5faW4gfHwgdGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYgJiYgdGhpcy5pc0NvbnRleHR1YWwoXCJvZlwiKSkgJiYgX2luaXQuZGVjbGFyYXRpb25zLmxlbmd0aCA9PT0gMSAmJiAhKHZhcktpbmQgIT09IF90b2tlbnR5cGUudHlwZXMuX3ZhciAmJiBfaW5pdC5kZWNsYXJhdGlvbnNbMF0uaW5pdCkpIHJldHVybiB0aGlzLnBhcnNlRm9ySW4obm9kZSwgX2luaXQpO1xuICAgIHJldHVybiB0aGlzLnBhcnNlRm9yKG5vZGUsIF9pbml0KTtcbiAgfVxuICB2YXIgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcyA9IHsgc3RhcnQ6IDAgfTtcbiAgdmFyIGluaXQgPSB0aGlzLnBhcnNlRXhwcmVzc2lvbih0cnVlLCByZWZTaG9ydGhhbmREZWZhdWx0UG9zKTtcbiAgaWYgKHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5faW4gfHwgdGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYgJiYgdGhpcy5pc0NvbnRleHR1YWwoXCJvZlwiKSkge1xuICAgIHRoaXMudG9Bc3NpZ25hYmxlKGluaXQpO1xuICAgIHRoaXMuY2hlY2tMVmFsKGluaXQpO1xuICAgIHJldHVybiB0aGlzLnBhcnNlRm9ySW4obm9kZSwgaW5pdCk7XG4gIH0gZWxzZSBpZiAocmVmU2hvcnRoYW5kRGVmYXVsdFBvcy5zdGFydCkge1xuICAgIHRoaXMudW5leHBlY3RlZChyZWZTaG9ydGhhbmREZWZhdWx0UG9zLnN0YXJ0KTtcbiAgfVxuICByZXR1cm4gdGhpcy5wYXJzZUZvcihub2RlLCBpbml0KTtcbn07XG5cbnBwLnBhcnNlRnVuY3Rpb25TdGF0ZW1lbnQgPSBmdW5jdGlvbiAobm9kZSkge1xuICB0aGlzLm5leHQoKTtcbiAgcmV0dXJuIHRoaXMucGFyc2VGdW5jdGlvbihub2RlLCB0cnVlKTtcbn07XG5cbnBwLnBhcnNlSWZTdGF0ZW1lbnQgPSBmdW5jdGlvbiAobm9kZSkge1xuICB0aGlzLm5leHQoKTtcbiAgbm9kZS50ZXN0ID0gdGhpcy5wYXJzZVBhcmVuRXhwcmVzc2lvbigpO1xuICBub2RlLmNvbnNlcXVlbnQgPSB0aGlzLnBhcnNlU3RhdGVtZW50KGZhbHNlKTtcbiAgbm9kZS5hbHRlcm5hdGUgPSB0aGlzLmVhdChfdG9rZW50eXBlLnR5cGVzLl9lbHNlKSA/IHRoaXMucGFyc2VTdGF0ZW1lbnQoZmFsc2UpIDogbnVsbDtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIklmU3RhdGVtZW50XCIpO1xufTtcblxucHAucGFyc2VSZXR1cm5TdGF0ZW1lbnQgPSBmdW5jdGlvbiAobm9kZSkge1xuICBpZiAoIXRoaXMuaW5GdW5jdGlvbiAmJiAhdGhpcy5vcHRpb25zLmFsbG93UmV0dXJuT3V0c2lkZUZ1bmN0aW9uKSB0aGlzLnJhaXNlKHRoaXMuc3RhcnQsIFwiJ3JldHVybicgb3V0c2lkZSBvZiBmdW5jdGlvblwiKTtcbiAgdGhpcy5uZXh0KCk7XG5cbiAgLy8gSW4gYHJldHVybmAgKGFuZCBgYnJlYWtgL2Bjb250aW51ZWApLCB0aGUga2V5d29yZHMgd2l0aFxuICAvLyBvcHRpb25hbCBhcmd1bWVudHMsIHdlIGVhZ2VybHkgbG9vayBmb3IgYSBzZW1pY29sb24gb3IgdGhlXG4gIC8vIHBvc3NpYmlsaXR5IHRvIGluc2VydCBvbmUuXG5cbiAgaWYgKHRoaXMuZWF0KF90b2tlbnR5cGUudHlwZXMuc2VtaSkgfHwgdGhpcy5pbnNlcnRTZW1pY29sb24oKSkgbm9kZS5hcmd1bWVudCA9IG51bGw7ZWxzZSB7XG4gICAgbm9kZS5hcmd1bWVudCA9IHRoaXMucGFyc2VFeHByZXNzaW9uKCk7dGhpcy5zZW1pY29sb24oKTtcbiAgfVxuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiUmV0dXJuU3RhdGVtZW50XCIpO1xufTtcblxucHAucGFyc2VTd2l0Y2hTdGF0ZW1lbnQgPSBmdW5jdGlvbiAobm9kZSkge1xuICB0aGlzLm5leHQoKTtcbiAgbm9kZS5kaXNjcmltaW5hbnQgPSB0aGlzLnBhcnNlUGFyZW5FeHByZXNzaW9uKCk7XG4gIG5vZGUuY2FzZXMgPSBbXTtcbiAgdGhpcy5leHBlY3QoX3Rva2VudHlwZS50eXBlcy5icmFjZUwpO1xuICB0aGlzLmxhYmVscy5wdXNoKHN3aXRjaExhYmVsKTtcblxuICAvLyBTdGF0ZW1lbnRzIHVuZGVyIG11c3QgYmUgZ3JvdXBlZCAoYnkgbGFiZWwpIGluIFN3aXRjaENhc2VcbiAgLy8gbm9kZXMuIGBjdXJgIGlzIHVzZWQgdG8ga2VlcCB0aGUgbm9kZSB0aGF0IHdlIGFyZSBjdXJyZW50bHlcbiAgLy8gYWRkaW5nIHN0YXRlbWVudHMgdG8uXG5cbiAgZm9yICh2YXIgY3VyLCBzYXdEZWZhdWx0ID0gZmFsc2U7IHRoaXMudHlwZSAhPSBfdG9rZW50eXBlLnR5cGVzLmJyYWNlUjspIHtcbiAgICBpZiAodGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLl9jYXNlIHx8IHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5fZGVmYXVsdCkge1xuICAgICAgdmFyIGlzQ2FzZSA9IHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5fY2FzZTtcbiAgICAgIGlmIChjdXIpIHRoaXMuZmluaXNoTm9kZShjdXIsIFwiU3dpdGNoQ2FzZVwiKTtcbiAgICAgIG5vZGUuY2FzZXMucHVzaChjdXIgPSB0aGlzLnN0YXJ0Tm9kZSgpKTtcbiAgICAgIGN1ci5jb25zZXF1ZW50ID0gW107XG4gICAgICB0aGlzLm5leHQoKTtcbiAgICAgIGlmIChpc0Nhc2UpIHtcbiAgICAgICAgY3VyLnRlc3QgPSB0aGlzLnBhcnNlRXhwcmVzc2lvbigpO1xuICAgICAgfSBlbHNlIHtcbiAgICAgICAgaWYgKHNhd0RlZmF1bHQpIHRoaXMucmFpc2UodGhpcy5sYXN0VG9rU3RhcnQsIFwiTXVsdGlwbGUgZGVmYXVsdCBjbGF1c2VzXCIpO1xuICAgICAgICBzYXdEZWZhdWx0ID0gdHJ1ZTtcbiAgICAgICAgY3VyLnRlc3QgPSBudWxsO1xuICAgICAgfVxuICAgICAgdGhpcy5leHBlY3QoX3Rva2VudHlwZS50eXBlcy5jb2xvbik7XG4gICAgfSBlbHNlIHtcbiAgICAgIGlmICghY3VyKSB0aGlzLnVuZXhwZWN0ZWQoKTtcbiAgICAgIGN1ci5jb25zZXF1ZW50LnB1c2godGhpcy5wYXJzZVN0YXRlbWVudCh0cnVlKSk7XG4gICAgfVxuICB9XG4gIGlmIChjdXIpIHRoaXMuZmluaXNoTm9kZShjdXIsIFwiU3dpdGNoQ2FzZVwiKTtcbiAgdGhpcy5uZXh0KCk7IC8vIENsb3NpbmcgYnJhY2VcbiAgdGhpcy5sYWJlbHMucG9wKCk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJTd2l0Y2hTdGF0ZW1lbnRcIik7XG59O1xuXG5wcC5wYXJzZVRocm93U3RhdGVtZW50ID0gZnVuY3Rpb24gKG5vZGUpIHtcbiAgdGhpcy5uZXh0KCk7XG4gIGlmIChfd2hpdGVzcGFjZS5saW5lQnJlYWsudGVzdCh0aGlzLmlucHV0LnNsaWNlKHRoaXMubGFzdFRva0VuZCwgdGhpcy5zdGFydCkpKSB0aGlzLnJhaXNlKHRoaXMubGFzdFRva0VuZCwgXCJJbGxlZ2FsIG5ld2xpbmUgYWZ0ZXIgdGhyb3dcIik7XG4gIG5vZGUuYXJndW1lbnQgPSB0aGlzLnBhcnNlRXhwcmVzc2lvbigpO1xuICB0aGlzLnNlbWljb2xvbigpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiVGhyb3dTdGF0ZW1lbnRcIik7XG59O1xuXG4vLyBSZXVzZWQgZW1wdHkgYXJyYXkgYWRkZWQgZm9yIG5vZGUgZmllbGRzIHRoYXQgYXJlIGFsd2F5cyBlbXB0eS5cblxudmFyIGVtcHR5ID0gW107XG5cbnBwLnBhcnNlVHJ5U3RhdGVtZW50ID0gZnVuY3Rpb24gKG5vZGUpIHtcbiAgdGhpcy5uZXh0KCk7XG4gIG5vZGUuYmxvY2sgPSB0aGlzLnBhcnNlQmxvY2soKTtcbiAgbm9kZS5oYW5kbGVyID0gbnVsbDtcbiAgaWYgKHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5fY2F0Y2gpIHtcbiAgICB2YXIgY2xhdXNlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgICB0aGlzLm5leHQoKTtcbiAgICB0aGlzLmV4cGVjdChfdG9rZW50eXBlLnR5cGVzLnBhcmVuTCk7XG4gICAgY2xhdXNlLnBhcmFtID0gdGhpcy5wYXJzZUJpbmRpbmdBdG9tKCk7XG4gICAgdGhpcy5jaGVja0xWYWwoY2xhdXNlLnBhcmFtLCB0cnVlKTtcbiAgICB0aGlzLmV4cGVjdChfdG9rZW50eXBlLnR5cGVzLnBhcmVuUik7XG4gICAgY2xhdXNlLmd1YXJkID0gbnVsbDtcbiAgICBjbGF1c2UuYm9keSA9IHRoaXMucGFyc2VCbG9jaygpO1xuICAgIG5vZGUuaGFuZGxlciA9IHRoaXMuZmluaXNoTm9kZShjbGF1c2UsIFwiQ2F0Y2hDbGF1c2VcIik7XG4gIH1cbiAgbm9kZS5ndWFyZGVkSGFuZGxlcnMgPSBlbXB0eTtcbiAgbm9kZS5maW5hbGl6ZXIgPSB0aGlzLmVhdChfdG9rZW50eXBlLnR5cGVzLl9maW5hbGx5KSA/IHRoaXMucGFyc2VCbG9jaygpIDogbnVsbDtcbiAgaWYgKCFub2RlLmhhbmRsZXIgJiYgIW5vZGUuZmluYWxpemVyKSB0aGlzLnJhaXNlKG5vZGUuc3RhcnQsIFwiTWlzc2luZyBjYXRjaCBvciBmaW5hbGx5IGNsYXVzZVwiKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIlRyeVN0YXRlbWVudFwiKTtcbn07XG5cbnBwLnBhcnNlVmFyU3RhdGVtZW50ID0gZnVuY3Rpb24gKG5vZGUsIGtpbmQpIHtcbiAgdGhpcy5uZXh0KCk7XG4gIHRoaXMucGFyc2VWYXIobm9kZSwgZmFsc2UsIGtpbmQpO1xuICB0aGlzLnNlbWljb2xvbigpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiVmFyaWFibGVEZWNsYXJhdGlvblwiKTtcbn07XG5cbnBwLnBhcnNlV2hpbGVTdGF0ZW1lbnQgPSBmdW5jdGlvbiAobm9kZSkge1xuICB0aGlzLm5leHQoKTtcbiAgbm9kZS50ZXN0ID0gdGhpcy5wYXJzZVBhcmVuRXhwcmVzc2lvbigpO1xuICB0aGlzLmxhYmVscy5wdXNoKGxvb3BMYWJlbCk7XG4gIG5vZGUuYm9keSA9IHRoaXMucGFyc2VTdGF0ZW1lbnQoZmFsc2UpO1xuICB0aGlzLmxhYmVscy5wb3AoKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIldoaWxlU3RhdGVtZW50XCIpO1xufTtcblxucHAucGFyc2VXaXRoU3RhdGVtZW50ID0gZnVuY3Rpb24gKG5vZGUpIHtcbiAgaWYgKHRoaXMuc3RyaWN0KSB0aGlzLnJhaXNlKHRoaXMuc3RhcnQsIFwiJ3dpdGgnIGluIHN0cmljdCBtb2RlXCIpO1xuICB0aGlzLm5leHQoKTtcbiAgbm9kZS5vYmplY3QgPSB0aGlzLnBhcnNlUGFyZW5FeHByZXNzaW9uKCk7XG4gIG5vZGUuYm9keSA9IHRoaXMucGFyc2VTdGF0ZW1lbnQoZmFsc2UpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiV2l0aFN0YXRlbWVudFwiKTtcbn07XG5cbnBwLnBhcnNlRW1wdHlTdGF0ZW1lbnQgPSBmdW5jdGlvbiAobm9kZSkge1xuICB0aGlzLm5leHQoKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkVtcHR5U3RhdGVtZW50XCIpO1xufTtcblxucHAucGFyc2VMYWJlbGVkU3RhdGVtZW50ID0gZnVuY3Rpb24gKG5vZGUsIG1heWJlTmFtZSwgZXhwcikge1xuICBmb3IgKHZhciBpID0gMDsgaSA8IHRoaXMubGFiZWxzLmxlbmd0aDsgKytpKSB7XG4gICAgaWYgKHRoaXMubGFiZWxzW2ldLm5hbWUgPT09IG1heWJlTmFtZSkgdGhpcy5yYWlzZShleHByLnN0YXJ0LCBcIkxhYmVsICdcIiArIG1heWJlTmFtZSArIFwiJyBpcyBhbHJlYWR5IGRlY2xhcmVkXCIpO1xuICB9dmFyIGtpbmQgPSB0aGlzLnR5cGUuaXNMb29wID8gXCJsb29wXCIgOiB0aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuX3N3aXRjaCA/IFwic3dpdGNoXCIgOiBudWxsO1xuICBmb3IgKHZhciBpID0gdGhpcy5sYWJlbHMubGVuZ3RoIC0gMTsgaSA+PSAwOyBpLS0pIHtcbiAgICB2YXIgbGFiZWwgPSB0aGlzLmxhYmVsc1tpXTtcbiAgICBpZiAobGFiZWwuc3RhdGVtZW50U3RhcnQgPT0gbm9kZS5zdGFydCkge1xuICAgICAgbGFiZWwuc3RhdGVtZW50U3RhcnQgPSB0aGlzLnN0YXJ0O1xuICAgICAgbGFiZWwua2luZCA9IGtpbmQ7XG4gICAgfSBlbHNlIGJyZWFrO1xuICB9XG4gIHRoaXMubGFiZWxzLnB1c2goeyBuYW1lOiBtYXliZU5hbWUsIGtpbmQ6IGtpbmQsIHN0YXRlbWVudFN0YXJ0OiB0aGlzLnN0YXJ0IH0pO1xuICBub2RlLmJvZHkgPSB0aGlzLnBhcnNlU3RhdGVtZW50KHRydWUpO1xuICB0aGlzLmxhYmVscy5wb3AoKTtcbiAgbm9kZS5sYWJlbCA9IGV4cHI7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJMYWJlbGVkU3RhdGVtZW50XCIpO1xufTtcblxucHAucGFyc2VFeHByZXNzaW9uU3RhdGVtZW50ID0gZnVuY3Rpb24gKG5vZGUsIGV4cHIpIHtcbiAgbm9kZS5leHByZXNzaW9uID0gZXhwcjtcbiAgdGhpcy5zZW1pY29sb24oKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkV4cHJlc3Npb25TdGF0ZW1lbnRcIik7XG59O1xuXG4vLyBQYXJzZSBhIHNlbWljb2xvbi1lbmNsb3NlZCBibG9jayBvZiBzdGF0ZW1lbnRzLCBoYW5kbGluZyBgXCJ1c2Vcbi8vIHN0cmljdFwiYCBkZWNsYXJhdGlvbnMgd2hlbiBgYWxsb3dTdHJpY3RgIGlzIHRydWUgKHVzZWQgZm9yXG4vLyBmdW5jdGlvbiBib2RpZXMpLlxuXG5wcC5wYXJzZUJsb2NrID0gZnVuY3Rpb24gKGFsbG93U3RyaWN0KSB7XG4gIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGUoKSxcbiAgICAgIGZpcnN0ID0gdHJ1ZSxcbiAgICAgIG9sZFN0cmljdCA9IHVuZGVmaW5lZDtcbiAgbm9kZS5ib2R5ID0gW107XG4gIHRoaXMuZXhwZWN0KF90b2tlbnR5cGUudHlwZXMuYnJhY2VMKTtcbiAgd2hpbGUgKCF0aGlzLmVhdChfdG9rZW50eXBlLnR5cGVzLmJyYWNlUikpIHtcbiAgICB2YXIgc3RtdCA9IHRoaXMucGFyc2VTdGF0ZW1lbnQodHJ1ZSk7XG4gICAgbm9kZS5ib2R5LnB1c2goc3RtdCk7XG4gICAgaWYgKGZpcnN0ICYmIGFsbG93U3RyaWN0ICYmIHRoaXMuaXNVc2VTdHJpY3Qoc3RtdCkpIHtcbiAgICAgIG9sZFN0cmljdCA9IHRoaXMuc3RyaWN0O1xuICAgICAgdGhpcy5zZXRTdHJpY3QodGhpcy5zdHJpY3QgPSB0cnVlKTtcbiAgICB9XG4gICAgZmlyc3QgPSBmYWxzZTtcbiAgfVxuICBpZiAob2xkU3RyaWN0ID09PSBmYWxzZSkgdGhpcy5zZXRTdHJpY3QoZmFsc2UpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiQmxvY2tTdGF0ZW1lbnRcIik7XG59O1xuXG4vLyBQYXJzZSBhIHJlZ3VsYXIgYGZvcmAgbG9vcC4gVGhlIGRpc2FtYmlndWF0aW9uIGNvZGUgaW5cbi8vIGBwYXJzZVN0YXRlbWVudGAgd2lsbCBhbHJlYWR5IGhhdmUgcGFyc2VkIHRoZSBpbml0IHN0YXRlbWVudCBvclxuLy8gZXhwcmVzc2lvbi5cblxucHAucGFyc2VGb3IgPSBmdW5jdGlvbiAobm9kZSwgaW5pdCkge1xuICBub2RlLmluaXQgPSBpbml0O1xuICB0aGlzLmV4cGVjdChfdG9rZW50eXBlLnR5cGVzLnNlbWkpO1xuICBub2RlLnRlc3QgPSB0aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuc2VtaSA/IG51bGwgOiB0aGlzLnBhcnNlRXhwcmVzc2lvbigpO1xuICB0aGlzLmV4cGVjdChfdG9rZW50eXBlLnR5cGVzLnNlbWkpO1xuICBub2RlLnVwZGF0ZSA9IHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5wYXJlblIgPyBudWxsIDogdGhpcy5wYXJzZUV4cHJlc3Npb24oKTtcbiAgdGhpcy5leHBlY3QoX3Rva2VudHlwZS50eXBlcy5wYXJlblIpO1xuICBub2RlLmJvZHkgPSB0aGlzLnBhcnNlU3RhdGVtZW50KGZhbHNlKTtcbiAgdGhpcy5sYWJlbHMucG9wKCk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJGb3JTdGF0ZW1lbnRcIik7XG59O1xuXG4vLyBQYXJzZSBhIGBmb3JgL2BpbmAgYW5kIGBmb3JgL2BvZmAgbG9vcCwgd2hpY2ggYXJlIGFsbW9zdFxuLy8gc2FtZSBmcm9tIHBhcnNlcidzIHBlcnNwZWN0aXZlLlxuXG5wcC5wYXJzZUZvckluID0gZnVuY3Rpb24gKG5vZGUsIGluaXQpIHtcbiAgdmFyIHR5cGUgPSB0aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuX2luID8gXCJGb3JJblN0YXRlbWVudFwiIDogXCJGb3JPZlN0YXRlbWVudFwiO1xuICB0aGlzLm5leHQoKTtcbiAgbm9kZS5sZWZ0ID0gaW5pdDtcbiAgbm9kZS5yaWdodCA9IHRoaXMucGFyc2VFeHByZXNzaW9uKCk7XG4gIHRoaXMuZXhwZWN0KF90b2tlbnR5cGUudHlwZXMucGFyZW5SKTtcbiAgbm9kZS5ib2R5ID0gdGhpcy5wYXJzZVN0YXRlbWVudChmYWxzZSk7XG4gIHRoaXMubGFiZWxzLnBvcCgpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIHR5cGUpO1xufTtcblxuLy8gUGFyc2UgYSBsaXN0IG9mIHZhcmlhYmxlIGRlY2xhcmF0aW9ucy5cblxucHAucGFyc2VWYXIgPSBmdW5jdGlvbiAobm9kZSwgaXNGb3IsIGtpbmQpIHtcbiAgbm9kZS5kZWNsYXJhdGlvbnMgPSBbXTtcbiAgbm9kZS5raW5kID0ga2luZC5rZXl3b3JkO1xuICBmb3IgKDs7KSB7XG4gICAgdmFyIGRlY2wgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICAgIHRoaXMucGFyc2VWYXJJZChkZWNsKTtcbiAgICBpZiAodGhpcy5lYXQoX3Rva2VudHlwZS50eXBlcy5lcSkpIHtcbiAgICAgIGRlY2wuaW5pdCA9IHRoaXMucGFyc2VNYXliZUFzc2lnbihpc0Zvcik7XG4gICAgfSBlbHNlIGlmIChraW5kID09PSBfdG9rZW50eXBlLnR5cGVzLl9jb25zdCAmJiAhKHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5faW4gfHwgdGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYgJiYgdGhpcy5pc0NvbnRleHR1YWwoXCJvZlwiKSkpIHtcbiAgICAgIHRoaXMudW5leHBlY3RlZCgpO1xuICAgIH0gZWxzZSBpZiAoZGVjbC5pZC50eXBlICE9IFwiSWRlbnRpZmllclwiICYmICEoaXNGb3IgJiYgKHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5faW4gfHwgdGhpcy5pc0NvbnRleHR1YWwoXCJvZlwiKSkpKSB7XG4gICAgICB0aGlzLnJhaXNlKHRoaXMubGFzdFRva0VuZCwgXCJDb21wbGV4IGJpbmRpbmcgcGF0dGVybnMgcmVxdWlyZSBhbiBpbml0aWFsaXphdGlvbiB2YWx1ZVwiKTtcbiAgICB9IGVsc2Uge1xuICAgICAgZGVjbC5pbml0ID0gbnVsbDtcbiAgICB9XG4gICAgbm9kZS5kZWNsYXJhdGlvbnMucHVzaCh0aGlzLmZpbmlzaE5vZGUoZGVjbCwgXCJWYXJpYWJsZURlY2xhcmF0b3JcIikpO1xuICAgIGlmICghdGhpcy5lYXQoX3Rva2VudHlwZS50eXBlcy5jb21tYSkpIGJyZWFrO1xuICB9XG4gIHJldHVybiBub2RlO1xufTtcblxucHAucGFyc2VWYXJJZCA9IGZ1bmN0aW9uIChkZWNsKSB7XG4gIGRlY2wuaWQgPSB0aGlzLnBhcnNlQmluZGluZ0F0b20oKTtcbiAgdGhpcy5jaGVja0xWYWwoZGVjbC5pZCwgdHJ1ZSk7XG59O1xuXG4vLyBQYXJzZSBhIGZ1bmN0aW9uIGRlY2xhcmF0aW9uIG9yIGxpdGVyYWwgKGRlcGVuZGluZyBvbiB0aGVcbi8vIGBpc1N0YXRlbWVudGAgcGFyYW1ldGVyKS5cblxucHAucGFyc2VGdW5jdGlvbiA9IGZ1bmN0aW9uIChub2RlLCBpc1N0YXRlbWVudCwgYWxsb3dFeHByZXNzaW9uQm9keSkge1xuICB0aGlzLmluaXRGdW5jdGlvbihub2RlKTtcbiAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KSBub2RlLmdlbmVyYXRvciA9IHRoaXMuZWF0KF90b2tlbnR5cGUudHlwZXMuc3Rhcik7XG4gIGlmIChpc1N0YXRlbWVudCB8fCB0aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMubmFtZSkgbm9kZS5pZCA9IHRoaXMucGFyc2VJZGVudCgpO1xuICB0aGlzLnBhcnNlRnVuY3Rpb25QYXJhbXMobm9kZSk7XG4gIHRoaXMucGFyc2VGdW5jdGlvbkJvZHkobm9kZSwgYWxsb3dFeHByZXNzaW9uQm9keSk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgaXNTdGF0ZW1lbnQgPyBcIkZ1bmN0aW9uRGVjbGFyYXRpb25cIiA6IFwiRnVuY3Rpb25FeHByZXNzaW9uXCIpO1xufTtcblxucHAucGFyc2VGdW5jdGlvblBhcmFtcyA9IGZ1bmN0aW9uIChub2RlKSB7XG4gIHRoaXMuZXhwZWN0KF90b2tlbnR5cGUudHlwZXMucGFyZW5MKTtcbiAgbm9kZS5wYXJhbXMgPSB0aGlzLnBhcnNlQmluZGluZ0xpc3QoX3Rva2VudHlwZS50eXBlcy5wYXJlblIsIGZhbHNlLCBmYWxzZSk7XG59O1xuXG4vLyBQYXJzZSBhIGNsYXNzIGRlY2xhcmF0aW9uIG9yIGxpdGVyYWwgKGRlcGVuZGluZyBvbiB0aGVcbi8vIGBpc1N0YXRlbWVudGAgcGFyYW1ldGVyKS5cblxucHAucGFyc2VDbGFzcyA9IGZ1bmN0aW9uIChub2RlLCBpc1N0YXRlbWVudCkge1xuICB0aGlzLm5leHQoKTtcbiAgdGhpcy5wYXJzZUNsYXNzSWQobm9kZSwgaXNTdGF0ZW1lbnQpO1xuICB0aGlzLnBhcnNlQ2xhc3NTdXBlcihub2RlKTtcbiAgdmFyIGNsYXNzQm9keSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gIHZhciBoYWRDb25zdHJ1Y3RvciA9IGZhbHNlO1xuICBjbGFzc0JvZHkuYm9keSA9IFtdO1xuICB0aGlzLmV4cGVjdChfdG9rZW50eXBlLnR5cGVzLmJyYWNlTCk7XG4gIHdoaWxlICghdGhpcy5lYXQoX3Rva2VudHlwZS50eXBlcy5icmFjZVIpKSB7XG4gICAgaWYgKHRoaXMuZWF0KF90b2tlbnR5cGUudHlwZXMuc2VtaSkpIGNvbnRpbnVlO1xuICAgIHZhciBtZXRob2QgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICAgIHZhciBpc0dlbmVyYXRvciA9IHRoaXMuZWF0KF90b2tlbnR5cGUudHlwZXMuc3Rhcik7XG4gICAgdmFyIGlzTWF5YmVTdGF0aWMgPSB0aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMubmFtZSAmJiB0aGlzLnZhbHVlID09PSBcInN0YXRpY1wiO1xuICAgIHRoaXMucGFyc2VQcm9wZXJ0eU5hbWUobWV0aG9kKTtcbiAgICBtZXRob2RbXCJzdGF0aWNcIl0gPSBpc01heWJlU3RhdGljICYmIHRoaXMudHlwZSAhPT0gX3Rva2VudHlwZS50eXBlcy5wYXJlbkw7XG4gICAgaWYgKG1ldGhvZFtcInN0YXRpY1wiXSkge1xuICAgICAgaWYgKGlzR2VuZXJhdG9yKSB0aGlzLnVuZXhwZWN0ZWQoKTtcbiAgICAgIGlzR2VuZXJhdG9yID0gdGhpcy5lYXQoX3Rva2VudHlwZS50eXBlcy5zdGFyKTtcbiAgICAgIHRoaXMucGFyc2VQcm9wZXJ0eU5hbWUobWV0aG9kKTtcbiAgICB9XG4gICAgbWV0aG9kLmtpbmQgPSBcIm1ldGhvZFwiO1xuICAgIHZhciBpc0dldFNldCA9IGZhbHNlO1xuICAgIGlmICghbWV0aG9kLmNvbXB1dGVkKSB7XG4gICAgICB2YXIga2V5ID0gbWV0aG9kLmtleTtcblxuICAgICAgaWYgKCFpc0dlbmVyYXRvciAmJiBrZXkudHlwZSA9PT0gXCJJZGVudGlmaWVyXCIgJiYgdGhpcy50eXBlICE9PSBfdG9rZW50eXBlLnR5cGVzLnBhcmVuTCAmJiAoa2V5Lm5hbWUgPT09IFwiZ2V0XCIgfHwga2V5Lm5hbWUgPT09IFwic2V0XCIpKSB7XG4gICAgICAgIGlzR2V0U2V0ID0gdHJ1ZTtcbiAgICAgICAgbWV0aG9kLmtpbmQgPSBrZXkubmFtZTtcbiAgICAgICAga2V5ID0gdGhpcy5wYXJzZVByb3BlcnR5TmFtZShtZXRob2QpO1xuICAgICAgfVxuICAgICAgaWYgKCFtZXRob2RbXCJzdGF0aWNcIl0gJiYgKGtleS50eXBlID09PSBcIklkZW50aWZpZXJcIiAmJiBrZXkubmFtZSA9PT0gXCJjb25zdHJ1Y3RvclwiIHx8IGtleS50eXBlID09PSBcIkxpdGVyYWxcIiAmJiBrZXkudmFsdWUgPT09IFwiY29uc3RydWN0b3JcIikpIHtcbiAgICAgICAgaWYgKGhhZENvbnN0cnVjdG9yKSB0aGlzLnJhaXNlKGtleS5zdGFydCwgXCJEdXBsaWNhdGUgY29uc3RydWN0b3IgaW4gdGhlIHNhbWUgY2xhc3NcIik7XG4gICAgICAgIGlmIChpc0dldFNldCkgdGhpcy5yYWlzZShrZXkuc3RhcnQsIFwiQ29uc3RydWN0b3IgY2FuJ3QgaGF2ZSBnZXQvc2V0IG1vZGlmaWVyXCIpO1xuICAgICAgICBpZiAoaXNHZW5lcmF0b3IpIHRoaXMucmFpc2Uoa2V5LnN0YXJ0LCBcIkNvbnN0cnVjdG9yIGNhbid0IGJlIGEgZ2VuZXJhdG9yXCIpO1xuICAgICAgICBtZXRob2Qua2luZCA9IFwiY29uc3RydWN0b3JcIjtcbiAgICAgICAgaGFkQ29uc3RydWN0b3IgPSB0cnVlO1xuICAgICAgfVxuICAgIH1cbiAgICB0aGlzLnBhcnNlQ2xhc3NNZXRob2QoY2xhc3NCb2R5LCBtZXRob2QsIGlzR2VuZXJhdG9yKTtcbiAgICBpZiAoaXNHZXRTZXQpIHtcbiAgICAgIHZhciBwYXJhbUNvdW50ID0gbWV0aG9kLmtpbmQgPT09IFwiZ2V0XCIgPyAwIDogMTtcbiAgICAgIGlmIChtZXRob2QudmFsdWUucGFyYW1zLmxlbmd0aCAhPT0gcGFyYW1Db3VudCkge1xuICAgICAgICB2YXIgc3RhcnQgPSBtZXRob2QudmFsdWUuc3RhcnQ7XG4gICAgICAgIGlmIChtZXRob2Qua2luZCA9PT0gXCJnZXRcIikgdGhpcy5yYWlzZShzdGFydCwgXCJnZXR0ZXIgc2hvdWxkIGhhdmUgbm8gcGFyYW1zXCIpO2Vsc2UgdGhpcy5yYWlzZShzdGFydCwgXCJzZXR0ZXIgc2hvdWxkIGhhdmUgZXhhY3RseSBvbmUgcGFyYW1cIik7XG4gICAgICB9XG4gICAgfVxuICB9XG4gIG5vZGUuYm9keSA9IHRoaXMuZmluaXNoTm9kZShjbGFzc0JvZHksIFwiQ2xhc3NCb2R5XCIpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIGlzU3RhdGVtZW50ID8gXCJDbGFzc0RlY2xhcmF0aW9uXCIgOiBcIkNsYXNzRXhwcmVzc2lvblwiKTtcbn07XG5cbnBwLnBhcnNlQ2xhc3NNZXRob2QgPSBmdW5jdGlvbiAoY2xhc3NCb2R5LCBtZXRob2QsIGlzR2VuZXJhdG9yKSB7XG4gIG1ldGhvZC52YWx1ZSA9IHRoaXMucGFyc2VNZXRob2QoaXNHZW5lcmF0b3IpO1xuICBjbGFzc0JvZHkuYm9keS5wdXNoKHRoaXMuZmluaXNoTm9kZShtZXRob2QsIFwiTWV0aG9kRGVmaW5pdGlvblwiKSk7XG59O1xuXG5wcC5wYXJzZUNsYXNzSWQgPSBmdW5jdGlvbiAobm9kZSwgaXNTdGF0ZW1lbnQpIHtcbiAgbm9kZS5pZCA9IHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5uYW1lID8gdGhpcy5wYXJzZUlkZW50KCkgOiBpc1N0YXRlbWVudCA/IHRoaXMudW5leHBlY3RlZCgpIDogbnVsbDtcbn07XG5cbnBwLnBhcnNlQ2xhc3NTdXBlciA9IGZ1bmN0aW9uIChub2RlKSB7XG4gIG5vZGUuc3VwZXJDbGFzcyA9IHRoaXMuZWF0KF90b2tlbnR5cGUudHlwZXMuX2V4dGVuZHMpID8gdGhpcy5wYXJzZUV4cHJTdWJzY3JpcHRzKCkgOiBudWxsO1xufTtcblxuLy8gUGFyc2VzIG1vZHVsZSBleHBvcnQgZGVjbGFyYXRpb24uXG5cbnBwLnBhcnNlRXhwb3J0ID0gZnVuY3Rpb24gKG5vZGUpIHtcbiAgdGhpcy5uZXh0KCk7XG4gIC8vIGV4cG9ydCAqIGZyb20gJy4uLidcbiAgaWYgKHRoaXMuZWF0KF90b2tlbnR5cGUudHlwZXMuc3RhcikpIHtcbiAgICB0aGlzLmV4cGVjdENvbnRleHR1YWwoXCJmcm9tXCIpO1xuICAgIG5vZGUuc291cmNlID0gdGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLnN0cmluZyA/IHRoaXMucGFyc2VFeHByQXRvbSgpIDogdGhpcy51bmV4cGVjdGVkKCk7XG4gICAgdGhpcy5zZW1pY29sb24oKTtcbiAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiRXhwb3J0QWxsRGVjbGFyYXRpb25cIik7XG4gIH1cbiAgaWYgKHRoaXMuZWF0KF90b2tlbnR5cGUudHlwZXMuX2RlZmF1bHQpKSB7XG4gICAgLy8gZXhwb3J0IGRlZmF1bHQgLi4uXG4gICAgdmFyIGV4cHIgPSB0aGlzLnBhcnNlTWF5YmVBc3NpZ24oKTtcbiAgICB2YXIgbmVlZHNTZW1pID0gdHJ1ZTtcbiAgICBpZiAoZXhwci50eXBlID09IFwiRnVuY3Rpb25FeHByZXNzaW9uXCIgfHwgZXhwci50eXBlID09IFwiQ2xhc3NFeHByZXNzaW9uXCIpIHtcbiAgICAgIG5lZWRzU2VtaSA9IGZhbHNlO1xuICAgICAgaWYgKGV4cHIuaWQpIHtcbiAgICAgICAgZXhwci50eXBlID0gZXhwci50eXBlID09IFwiRnVuY3Rpb25FeHByZXNzaW9uXCIgPyBcIkZ1bmN0aW9uRGVjbGFyYXRpb25cIiA6IFwiQ2xhc3NEZWNsYXJhdGlvblwiO1xuICAgICAgfVxuICAgIH1cbiAgICBub2RlLmRlY2xhcmF0aW9uID0gZXhwcjtcbiAgICBpZiAobmVlZHNTZW1pKSB0aGlzLnNlbWljb2xvbigpO1xuICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJFeHBvcnREZWZhdWx0RGVjbGFyYXRpb25cIik7XG4gIH1cbiAgLy8gZXhwb3J0IHZhcnxjb25zdHxsZXR8ZnVuY3Rpb258Y2xhc3MgLi4uXG4gIGlmICh0aGlzLnNob3VsZFBhcnNlRXhwb3J0U3RhdGVtZW50KCkpIHtcbiAgICBub2RlLmRlY2xhcmF0aW9uID0gdGhpcy5wYXJzZVN0YXRlbWVudCh0cnVlKTtcbiAgICBub2RlLnNwZWNpZmllcnMgPSBbXTtcbiAgICBub2RlLnNvdXJjZSA9IG51bGw7XG4gIH0gZWxzZSB7XG4gICAgLy8gZXhwb3J0IHsgeCwgeSBhcyB6IH0gW2Zyb20gJy4uLiddXG4gICAgbm9kZS5kZWNsYXJhdGlvbiA9IG51bGw7XG4gICAgbm9kZS5zcGVjaWZpZXJzID0gdGhpcy5wYXJzZUV4cG9ydFNwZWNpZmllcnMoKTtcbiAgICBpZiAodGhpcy5lYXRDb250ZXh0dWFsKFwiZnJvbVwiKSkge1xuICAgICAgbm9kZS5zb3VyY2UgPSB0aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuc3RyaW5nID8gdGhpcy5wYXJzZUV4cHJBdG9tKCkgOiB0aGlzLnVuZXhwZWN0ZWQoKTtcbiAgICB9IGVsc2Uge1xuICAgICAgbm9kZS5zb3VyY2UgPSBudWxsO1xuICAgIH1cbiAgICB0aGlzLnNlbWljb2xvbigpO1xuICB9XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJFeHBvcnROYW1lZERlY2xhcmF0aW9uXCIpO1xufTtcblxucHAuc2hvdWxkUGFyc2VFeHBvcnRTdGF0ZW1lbnQgPSBmdW5jdGlvbiAoKSB7XG4gIHJldHVybiB0aGlzLnR5cGUua2V5d29yZDtcbn07XG5cbi8vIFBhcnNlcyBhIGNvbW1hLXNlcGFyYXRlZCBsaXN0IG9mIG1vZHVsZSBleHBvcnRzLlxuXG5wcC5wYXJzZUV4cG9ydFNwZWNpZmllcnMgPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBub2RlcyA9IFtdLFxuICAgICAgZmlyc3QgPSB0cnVlO1xuICAvLyBleHBvcnQgeyB4LCB5IGFzIHogfSBbZnJvbSAnLi4uJ11cbiAgdGhpcy5leHBlY3QoX3Rva2VudHlwZS50eXBlcy5icmFjZUwpO1xuICB3aGlsZSAoIXRoaXMuZWF0KF90b2tlbnR5cGUudHlwZXMuYnJhY2VSKSkge1xuICAgIGlmICghZmlyc3QpIHtcbiAgICAgIHRoaXMuZXhwZWN0KF90b2tlbnR5cGUudHlwZXMuY29tbWEpO1xuICAgICAgaWYgKHRoaXMuYWZ0ZXJUcmFpbGluZ0NvbW1hKF90b2tlbnR5cGUudHlwZXMuYnJhY2VSKSkgYnJlYWs7XG4gICAgfSBlbHNlIGZpcnN0ID0gZmFsc2U7XG5cbiAgICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gICAgbm9kZS5sb2NhbCA9IHRoaXMucGFyc2VJZGVudCh0aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuX2RlZmF1bHQpO1xuICAgIG5vZGUuZXhwb3J0ZWQgPSB0aGlzLmVhdENvbnRleHR1YWwoXCJhc1wiKSA/IHRoaXMucGFyc2VJZGVudCh0cnVlKSA6IG5vZGUubG9jYWw7XG4gICAgbm9kZXMucHVzaCh0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJFeHBvcnRTcGVjaWZpZXJcIikpO1xuICB9XG4gIHJldHVybiBub2Rlcztcbn07XG5cbi8vIFBhcnNlcyBpbXBvcnQgZGVjbGFyYXRpb24uXG5cbnBwLnBhcnNlSW1wb3J0ID0gZnVuY3Rpb24gKG5vZGUpIHtcbiAgdGhpcy5uZXh0KCk7XG4gIC8vIGltcG9ydCAnLi4uJ1xuICBpZiAodGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLnN0cmluZykge1xuICAgIG5vZGUuc3BlY2lmaWVycyA9IGVtcHR5O1xuICAgIG5vZGUuc291cmNlID0gdGhpcy5wYXJzZUV4cHJBdG9tKCk7XG4gIH0gZWxzZSB7XG4gICAgbm9kZS5zcGVjaWZpZXJzID0gdGhpcy5wYXJzZUltcG9ydFNwZWNpZmllcnMoKTtcbiAgICB0aGlzLmV4cGVjdENvbnRleHR1YWwoXCJmcm9tXCIpO1xuICAgIG5vZGUuc291cmNlID0gdGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLnN0cmluZyA/IHRoaXMucGFyc2VFeHByQXRvbSgpIDogdGhpcy51bmV4cGVjdGVkKCk7XG4gIH1cbiAgdGhpcy5zZW1pY29sb24oKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkltcG9ydERlY2xhcmF0aW9uXCIpO1xufTtcblxuLy8gUGFyc2VzIGEgY29tbWEtc2VwYXJhdGVkIGxpc3Qgb2YgbW9kdWxlIGltcG9ydHMuXG5cbnBwLnBhcnNlSW1wb3J0U3BlY2lmaWVycyA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIG5vZGVzID0gW10sXG4gICAgICBmaXJzdCA9IHRydWU7XG4gIGlmICh0aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMubmFtZSkge1xuICAgIC8vIGltcG9ydCBkZWZhdWx0T2JqLCB7IHgsIHkgYXMgeiB9IGZyb20gJy4uLidcbiAgICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gICAgbm9kZS5sb2NhbCA9IHRoaXMucGFyc2VJZGVudCgpO1xuICAgIHRoaXMuY2hlY2tMVmFsKG5vZGUubG9jYWwsIHRydWUpO1xuICAgIG5vZGVzLnB1c2godGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiSW1wb3J0RGVmYXVsdFNwZWNpZmllclwiKSk7XG4gICAgaWYgKCF0aGlzLmVhdChfdG9rZW50eXBlLnR5cGVzLmNvbW1hKSkgcmV0dXJuIG5vZGVzO1xuICB9XG4gIGlmICh0aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuc3Rhcikge1xuICAgIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgICB0aGlzLm5leHQoKTtcbiAgICB0aGlzLmV4cGVjdENvbnRleHR1YWwoXCJhc1wiKTtcbiAgICBub2RlLmxvY2FsID0gdGhpcy5wYXJzZUlkZW50KCk7XG4gICAgdGhpcy5jaGVja0xWYWwobm9kZS5sb2NhbCwgdHJ1ZSk7XG4gICAgbm9kZXMucHVzaCh0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJJbXBvcnROYW1lc3BhY2VTcGVjaWZpZXJcIikpO1xuICAgIHJldHVybiBub2RlcztcbiAgfVxuICB0aGlzLmV4cGVjdChfdG9rZW50eXBlLnR5cGVzLmJyYWNlTCk7XG4gIHdoaWxlICghdGhpcy5lYXQoX3Rva2VudHlwZS50eXBlcy5icmFjZVIpKSB7XG4gICAgaWYgKCFmaXJzdCkge1xuICAgICAgdGhpcy5leHBlY3QoX3Rva2VudHlwZS50eXBlcy5jb21tYSk7XG4gICAgICBpZiAodGhpcy5hZnRlclRyYWlsaW5nQ29tbWEoX3Rva2VudHlwZS50eXBlcy5icmFjZVIpKSBicmVhaztcbiAgICB9IGVsc2UgZmlyc3QgPSBmYWxzZTtcblxuICAgIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgICBub2RlLmltcG9ydGVkID0gdGhpcy5wYXJzZUlkZW50KHRydWUpO1xuICAgIG5vZGUubG9jYWwgPSB0aGlzLmVhdENvbnRleHR1YWwoXCJhc1wiKSA/IHRoaXMucGFyc2VJZGVudCgpIDogbm9kZS5pbXBvcnRlZDtcbiAgICB0aGlzLmNoZWNrTFZhbChub2RlLmxvY2FsLCB0cnVlKTtcbiAgICBub2Rlcy5wdXNoKHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkltcG9ydFNwZWNpZmllclwiKSk7XG4gIH1cbiAgcmV0dXJuIG5vZGVzO1xufTtcblxufSx7XCIuL3N0YXRlXCI6MTAsXCIuL3Rva2VudHlwZVwiOjE0LFwiLi93aGl0ZXNwYWNlXCI6MTZ9XSwxMjpbZnVuY3Rpb24oX2RlcmVxXyxtb2R1bGUsZXhwb3J0cyl7XG4vLyBUaGUgYWxnb3JpdGhtIHVzZWQgdG8gZGV0ZXJtaW5lIHdoZXRoZXIgYSByZWdleHAgY2FuIGFwcGVhciBhdCBhXG4vLyBnaXZlbiBwb2ludCBpbiB0aGUgcHJvZ3JhbSBpcyBsb29zZWx5IGJhc2VkIG9uIHN3ZWV0LmpzJyBhcHByb2FjaC5cbi8vIFNlZSBodHRwczovL2dpdGh1Yi5jb20vbW96aWxsYS9zd2VldC5qcy93aWtpL2Rlc2lnblxuXG5cInVzZSBzdHJpY3RcIjtcblxuZXhwb3J0cy5fX2VzTW9kdWxlID0gdHJ1ZTtcblxuZnVuY3Rpb24gX2NsYXNzQ2FsbENoZWNrKGluc3RhbmNlLCBDb25zdHJ1Y3RvcikgeyBpZiAoIShpbnN0YW5jZSBpbnN0YW5jZW9mIENvbnN0cnVjdG9yKSkgeyB0aHJvdyBuZXcgVHlwZUVycm9yKFwiQ2Fubm90IGNhbGwgYSBjbGFzcyBhcyBhIGZ1bmN0aW9uXCIpOyB9IH1cblxudmFyIF9zdGF0ZSA9IF9kZXJlcV8oXCIuL3N0YXRlXCIpO1xuXG52YXIgX3Rva2VudHlwZSA9IF9kZXJlcV8oXCIuL3Rva2VudHlwZVwiKTtcblxudmFyIF93aGl0ZXNwYWNlID0gX2RlcmVxXyhcIi4vd2hpdGVzcGFjZVwiKTtcblxudmFyIFRva0NvbnRleHQgPSBmdW5jdGlvbiBUb2tDb250ZXh0KHRva2VuLCBpc0V4cHIsIHByZXNlcnZlU3BhY2UsIG92ZXJyaWRlKSB7XG4gIF9jbGFzc0NhbGxDaGVjayh0aGlzLCBUb2tDb250ZXh0KTtcblxuICB0aGlzLnRva2VuID0gdG9rZW47XG4gIHRoaXMuaXNFeHByID0gISFpc0V4cHI7XG4gIHRoaXMucHJlc2VydmVTcGFjZSA9ICEhcHJlc2VydmVTcGFjZTtcbiAgdGhpcy5vdmVycmlkZSA9IG92ZXJyaWRlO1xufTtcblxuZXhwb3J0cy5Ub2tDb250ZXh0ID0gVG9rQ29udGV4dDtcbnZhciB0eXBlcyA9IHtcbiAgYl9zdGF0OiBuZXcgVG9rQ29udGV4dChcIntcIiwgZmFsc2UpLFxuICBiX2V4cHI6IG5ldyBUb2tDb250ZXh0KFwie1wiLCB0cnVlKSxcbiAgYl90bXBsOiBuZXcgVG9rQ29udGV4dChcIiR7XCIsIHRydWUpLFxuICBwX3N0YXQ6IG5ldyBUb2tDb250ZXh0KFwiKFwiLCBmYWxzZSksXG4gIHBfZXhwcjogbmV3IFRva0NvbnRleHQoXCIoXCIsIHRydWUpLFxuICBxX3RtcGw6IG5ldyBUb2tDb250ZXh0KFwiYFwiLCB0cnVlLCB0cnVlLCBmdW5jdGlvbiAocCkge1xuICAgIHJldHVybiBwLnJlYWRUbXBsVG9rZW4oKTtcbiAgfSksXG4gIGZfZXhwcjogbmV3IFRva0NvbnRleHQoXCJmdW5jdGlvblwiLCB0cnVlKVxufTtcblxuZXhwb3J0cy50eXBlcyA9IHR5cGVzO1xudmFyIHBwID0gX3N0YXRlLlBhcnNlci5wcm90b3R5cGU7XG5cbnBwLmluaXRpYWxDb250ZXh0ID0gZnVuY3Rpb24gKCkge1xuICByZXR1cm4gW3R5cGVzLmJfc3RhdF07XG59O1xuXG5wcC5icmFjZUlzQmxvY2sgPSBmdW5jdGlvbiAocHJldlR5cGUpIHtcbiAgaWYgKHByZXZUeXBlID09PSBfdG9rZW50eXBlLnR5cGVzLmNvbG9uKSB7XG4gICAgdmFyIF9wYXJlbnQgPSB0aGlzLmN1ckNvbnRleHQoKTtcbiAgICBpZiAoX3BhcmVudCA9PT0gdHlwZXMuYl9zdGF0IHx8IF9wYXJlbnQgPT09IHR5cGVzLmJfZXhwcikgcmV0dXJuICFfcGFyZW50LmlzRXhwcjtcbiAgfVxuICBpZiAocHJldlR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuX3JldHVybikgcmV0dXJuIF93aGl0ZXNwYWNlLmxpbmVCcmVhay50ZXN0KHRoaXMuaW5wdXQuc2xpY2UodGhpcy5sYXN0VG9rRW5kLCB0aGlzLnN0YXJ0KSk7XG4gIGlmIChwcmV2VHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5fZWxzZSB8fCBwcmV2VHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5zZW1pIHx8IHByZXZUeXBlID09PSBfdG9rZW50eXBlLnR5cGVzLmVvZiB8fCBwcmV2VHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5wYXJlblIpIHJldHVybiB0cnVlO1xuICBpZiAocHJldlR5cGUgPT0gX3Rva2VudHlwZS50eXBlcy5icmFjZUwpIHJldHVybiB0aGlzLmN1ckNvbnRleHQoKSA9PT0gdHlwZXMuYl9zdGF0O1xuICByZXR1cm4gIXRoaXMuZXhwckFsbG93ZWQ7XG59O1xuXG5wcC51cGRhdGVDb250ZXh0ID0gZnVuY3Rpb24gKHByZXZUeXBlKSB7XG4gIHZhciB1cGRhdGUgPSB1bmRlZmluZWQsXG4gICAgICB0eXBlID0gdGhpcy50eXBlO1xuICBpZiAodHlwZS5rZXl3b3JkICYmIHByZXZUeXBlID09IF90b2tlbnR5cGUudHlwZXMuZG90KSB0aGlzLmV4cHJBbGxvd2VkID0gZmFsc2U7ZWxzZSBpZiAodXBkYXRlID0gdHlwZS51cGRhdGVDb250ZXh0KSB1cGRhdGUuY2FsbCh0aGlzLCBwcmV2VHlwZSk7ZWxzZSB0aGlzLmV4cHJBbGxvd2VkID0gdHlwZS5iZWZvcmVFeHByO1xufTtcblxuLy8gVG9rZW4tc3BlY2lmaWMgY29udGV4dCB1cGRhdGUgY29kZVxuXG5fdG9rZW50eXBlLnR5cGVzLnBhcmVuUi51cGRhdGVDb250ZXh0ID0gX3Rva2VudHlwZS50eXBlcy5icmFjZVIudXBkYXRlQ29udGV4dCA9IGZ1bmN0aW9uICgpIHtcbiAgaWYgKHRoaXMuY29udGV4dC5sZW5ndGggPT0gMSkge1xuICAgIHRoaXMuZXhwckFsbG93ZWQgPSB0cnVlO1xuICAgIHJldHVybjtcbiAgfVxuICB2YXIgb3V0ID0gdGhpcy5jb250ZXh0LnBvcCgpO1xuICBpZiAob3V0ID09PSB0eXBlcy5iX3N0YXQgJiYgdGhpcy5jdXJDb250ZXh0KCkgPT09IHR5cGVzLmZfZXhwcikge1xuICAgIHRoaXMuY29udGV4dC5wb3AoKTtcbiAgICB0aGlzLmV4cHJBbGxvd2VkID0gZmFsc2U7XG4gIH0gZWxzZSBpZiAob3V0ID09PSB0eXBlcy5iX3RtcGwpIHtcbiAgICB0aGlzLmV4cHJBbGxvd2VkID0gdHJ1ZTtcbiAgfSBlbHNlIHtcbiAgICB0aGlzLmV4cHJBbGxvd2VkID0gIW91dC5pc0V4cHI7XG4gIH1cbn07XG5cbl90b2tlbnR5cGUudHlwZXMuYnJhY2VMLnVwZGF0ZUNvbnRleHQgPSBmdW5jdGlvbiAocHJldlR5cGUpIHtcbiAgdGhpcy5jb250ZXh0LnB1c2godGhpcy5icmFjZUlzQmxvY2socHJldlR5cGUpID8gdHlwZXMuYl9zdGF0IDogdHlwZXMuYl9leHByKTtcbiAgdGhpcy5leHByQWxsb3dlZCA9IHRydWU7XG59O1xuXG5fdG9rZW50eXBlLnR5cGVzLmRvbGxhckJyYWNlTC51cGRhdGVDb250ZXh0ID0gZnVuY3Rpb24gKCkge1xuICB0aGlzLmNvbnRleHQucHVzaCh0eXBlcy5iX3RtcGwpO1xuICB0aGlzLmV4cHJBbGxvd2VkID0gdHJ1ZTtcbn07XG5cbl90b2tlbnR5cGUudHlwZXMucGFyZW5MLnVwZGF0ZUNvbnRleHQgPSBmdW5jdGlvbiAocHJldlR5cGUpIHtcbiAgdmFyIHN0YXRlbWVudFBhcmVucyA9IHByZXZUeXBlID09PSBfdG9rZW50eXBlLnR5cGVzLl9pZiB8fCBwcmV2VHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5fZm9yIHx8IHByZXZUeXBlID09PSBfdG9rZW50eXBlLnR5cGVzLl93aXRoIHx8IHByZXZUeXBlID09PSBfdG9rZW50eXBlLnR5cGVzLl93aGlsZTtcbiAgdGhpcy5jb250ZXh0LnB1c2goc3RhdGVtZW50UGFyZW5zID8gdHlwZXMucF9zdGF0IDogdHlwZXMucF9leHByKTtcbiAgdGhpcy5leHByQWxsb3dlZCA9IHRydWU7XG59O1xuXG5fdG9rZW50eXBlLnR5cGVzLmluY0RlYy51cGRhdGVDb250ZXh0ID0gZnVuY3Rpb24gKCkge307XG5cbl90b2tlbnR5cGUudHlwZXMuX2Z1bmN0aW9uLnVwZGF0ZUNvbnRleHQgPSBmdW5jdGlvbiAoKSB7XG4gIGlmICh0aGlzLmN1ckNvbnRleHQoKSAhPT0gdHlwZXMuYl9zdGF0KSB0aGlzLmNvbnRleHQucHVzaCh0eXBlcy5mX2V4cHIpO1xuICB0aGlzLmV4cHJBbGxvd2VkID0gZmFsc2U7XG59O1xuXG5fdG9rZW50eXBlLnR5cGVzLmJhY2tRdW90ZS51cGRhdGVDb250ZXh0ID0gZnVuY3Rpb24gKCkge1xuICBpZiAodGhpcy5jdXJDb250ZXh0KCkgPT09IHR5cGVzLnFfdG1wbCkgdGhpcy5jb250ZXh0LnBvcCgpO2Vsc2UgdGhpcy5jb250ZXh0LnB1c2godHlwZXMucV90bXBsKTtcbiAgdGhpcy5leHByQWxsb3dlZCA9IGZhbHNlO1xufTtcblxuLy8gdG9rRXhwckFsbG93ZWQgc3RheXMgdW5jaGFuZ2VkXG5cbn0se1wiLi9zdGF0ZVwiOjEwLFwiLi90b2tlbnR5cGVcIjoxNCxcIi4vd2hpdGVzcGFjZVwiOjE2fV0sMTM6W2Z1bmN0aW9uKF9kZXJlcV8sbW9kdWxlLGV4cG9ydHMpe1xuXCJ1c2Ugc3RyaWN0XCI7XG5cbmV4cG9ydHMuX19lc01vZHVsZSA9IHRydWU7XG5cbmZ1bmN0aW9uIF9jbGFzc0NhbGxDaGVjayhpbnN0YW5jZSwgQ29uc3RydWN0b3IpIHsgaWYgKCEoaW5zdGFuY2UgaW5zdGFuY2VvZiBDb25zdHJ1Y3RvcikpIHsgdGhyb3cgbmV3IFR5cGVFcnJvcihcIkNhbm5vdCBjYWxsIGEgY2xhc3MgYXMgYSBmdW5jdGlvblwiKTsgfSB9XG5cbnZhciBfaWRlbnRpZmllciA9IF9kZXJlcV8oXCIuL2lkZW50aWZpZXJcIik7XG5cbnZhciBfdG9rZW50eXBlID0gX2RlcmVxXyhcIi4vdG9rZW50eXBlXCIpO1xuXG52YXIgX3N0YXRlID0gX2RlcmVxXyhcIi4vc3RhdGVcIik7XG5cbnZhciBfbG9jdXRpbCA9IF9kZXJlcV8oXCIuL2xvY3V0aWxcIik7XG5cbnZhciBfd2hpdGVzcGFjZSA9IF9kZXJlcV8oXCIuL3doaXRlc3BhY2VcIik7XG5cbi8vIE9iamVjdCB0eXBlIHVzZWQgdG8gcmVwcmVzZW50IHRva2Vucy4gTm90ZSB0aGF0IG5vcm1hbGx5LCB0b2tlbnNcbi8vIHNpbXBseSBleGlzdCBhcyBwcm9wZXJ0aWVzIG9uIHRoZSBwYXJzZXIgb2JqZWN0LiBUaGlzIGlzIG9ubHlcbi8vIHVzZWQgZm9yIHRoZSBvblRva2VuIGNhbGxiYWNrIGFuZCB0aGUgZXh0ZXJuYWwgdG9rZW5pemVyLlxuXG52YXIgVG9rZW4gPSBmdW5jdGlvbiBUb2tlbihwKSB7XG4gIF9jbGFzc0NhbGxDaGVjayh0aGlzLCBUb2tlbik7XG5cbiAgdGhpcy50eXBlID0gcC50eXBlO1xuICB0aGlzLnZhbHVlID0gcC52YWx1ZTtcbiAgdGhpcy5zdGFydCA9IHAuc3RhcnQ7XG4gIHRoaXMuZW5kID0gcC5lbmQ7XG4gIGlmIChwLm9wdGlvbnMubG9jYXRpb25zKSB0aGlzLmxvYyA9IG5ldyBfbG9jdXRpbC5Tb3VyY2VMb2NhdGlvbihwLCBwLnN0YXJ0TG9jLCBwLmVuZExvYyk7XG4gIGlmIChwLm9wdGlvbnMucmFuZ2VzKSB0aGlzLnJhbmdlID0gW3Auc3RhcnQsIHAuZW5kXTtcbn07XG5cbmV4cG9ydHMuVG9rZW4gPSBUb2tlbjtcblxuLy8gIyMgVG9rZW5pemVyXG5cbnZhciBwcCA9IF9zdGF0ZS5QYXJzZXIucHJvdG90eXBlO1xuXG4vLyBBcmUgd2UgcnVubmluZyB1bmRlciBSaGlubz9cbnZhciBpc1JoaW5vID0gdHlwZW9mIFBhY2thZ2VzID09IFwib2JqZWN0XCIgJiYgT2JqZWN0LnByb3RvdHlwZS50b1N0cmluZy5jYWxsKFBhY2thZ2VzKSA9PSBcIltvYmplY3QgSmF2YVBhY2thZ2VdXCI7XG5cbi8vIE1vdmUgdG8gdGhlIG5leHQgdG9rZW5cblxucHAubmV4dCA9IGZ1bmN0aW9uICgpIHtcbiAgaWYgKHRoaXMub3B0aW9ucy5vblRva2VuKSB0aGlzLm9wdGlvbnMub25Ub2tlbihuZXcgVG9rZW4odGhpcykpO1xuXG4gIHRoaXMubGFzdFRva0VuZCA9IHRoaXMuZW5kO1xuICB0aGlzLmxhc3RUb2tTdGFydCA9IHRoaXMuc3RhcnQ7XG4gIHRoaXMubGFzdFRva0VuZExvYyA9IHRoaXMuZW5kTG9jO1xuICB0aGlzLmxhc3RUb2tTdGFydExvYyA9IHRoaXMuc3RhcnRMb2M7XG4gIHRoaXMubmV4dFRva2VuKCk7XG59O1xuXG5wcC5nZXRUb2tlbiA9IGZ1bmN0aW9uICgpIHtcbiAgdGhpcy5uZXh0KCk7XG4gIHJldHVybiBuZXcgVG9rZW4odGhpcyk7XG59O1xuXG4vLyBJZiB3ZSdyZSBpbiBhbiBFUzYgZW52aXJvbm1lbnQsIG1ha2UgcGFyc2VycyBpdGVyYWJsZVxuaWYgKHR5cGVvZiBTeW1ib2wgIT09IFwidW5kZWZpbmVkXCIpIHBwW1N5bWJvbC5pdGVyYXRvcl0gPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBzZWxmID0gdGhpcztcbiAgcmV0dXJuIHsgbmV4dDogZnVuY3Rpb24gbmV4dCgpIHtcbiAgICAgIHZhciB0b2tlbiA9IHNlbGYuZ2V0VG9rZW4oKTtcbiAgICAgIHJldHVybiB7XG4gICAgICAgIGRvbmU6IHRva2VuLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuZW9mLFxuICAgICAgICB2YWx1ZTogdG9rZW5cbiAgICAgIH07XG4gICAgfSB9O1xufTtcblxuLy8gVG9nZ2xlIHN0cmljdCBtb2RlLiBSZS1yZWFkcyB0aGUgbmV4dCBudW1iZXIgb3Igc3RyaW5nIHRvIHBsZWFzZVxuLy8gcGVkYW50aWMgdGVzdHMgKGBcInVzZSBzdHJpY3RcIjsgMDEwO2Agc2hvdWxkIGZhaWwpLlxuXG5wcC5zZXRTdHJpY3QgPSBmdW5jdGlvbiAoc3RyaWN0KSB7XG4gIHRoaXMuc3RyaWN0ID0gc3RyaWN0O1xuICBpZiAodGhpcy50eXBlICE9PSBfdG9rZW50eXBlLnR5cGVzLm51bSAmJiB0aGlzLnR5cGUgIT09IF90b2tlbnR5cGUudHlwZXMuc3RyaW5nKSByZXR1cm47XG4gIHRoaXMucG9zID0gdGhpcy5zdGFydDtcbiAgaWYgKHRoaXMub3B0aW9ucy5sb2NhdGlvbnMpIHtcbiAgICB3aGlsZSAodGhpcy5wb3MgPCB0aGlzLmxpbmVTdGFydCkge1xuICAgICAgdGhpcy5saW5lU3RhcnQgPSB0aGlzLmlucHV0Lmxhc3RJbmRleE9mKFwiXFxuXCIsIHRoaXMubGluZVN0YXJ0IC0gMikgKyAxO1xuICAgICAgLS10aGlzLmN1ckxpbmU7XG4gICAgfVxuICB9XG4gIHRoaXMubmV4dFRva2VuKCk7XG59O1xuXG5wcC5jdXJDb250ZXh0ID0gZnVuY3Rpb24gKCkge1xuICByZXR1cm4gdGhpcy5jb250ZXh0W3RoaXMuY29udGV4dC5sZW5ndGggLSAxXTtcbn07XG5cbi8vIFJlYWQgYSBzaW5nbGUgdG9rZW4sIHVwZGF0aW5nIHRoZSBwYXJzZXIgb2JqZWN0J3MgdG9rZW4tcmVsYXRlZFxuLy8gcHJvcGVydGllcy5cblxucHAubmV4dFRva2VuID0gZnVuY3Rpb24gKCkge1xuICB2YXIgY3VyQ29udGV4dCA9IHRoaXMuY3VyQ29udGV4dCgpO1xuICBpZiAoIWN1ckNvbnRleHQgfHwgIWN1ckNvbnRleHQucHJlc2VydmVTcGFjZSkgdGhpcy5za2lwU3BhY2UoKTtcblxuICB0aGlzLnN0YXJ0ID0gdGhpcy5wb3M7XG4gIGlmICh0aGlzLm9wdGlvbnMubG9jYXRpb25zKSB0aGlzLnN0YXJ0TG9jID0gdGhpcy5jdXJQb3NpdGlvbigpO1xuICBpZiAodGhpcy5wb3MgPj0gdGhpcy5pbnB1dC5sZW5ndGgpIHJldHVybiB0aGlzLmZpbmlzaFRva2VuKF90b2tlbnR5cGUudHlwZXMuZW9mKTtcblxuICBpZiAoY3VyQ29udGV4dC5vdmVycmlkZSkgcmV0dXJuIGN1ckNvbnRleHQub3ZlcnJpZGUodGhpcyk7ZWxzZSB0aGlzLnJlYWRUb2tlbih0aGlzLmZ1bGxDaGFyQ29kZUF0UG9zKCkpO1xufTtcblxucHAucmVhZFRva2VuID0gZnVuY3Rpb24gKGNvZGUpIHtcbiAgLy8gSWRlbnRpZmllciBvciBrZXl3b3JkLiAnXFx1WFhYWCcgc2VxdWVuY2VzIGFyZSBhbGxvd2VkIGluXG4gIC8vIGlkZW50aWZpZXJzLCBzbyAnXFwnIGFsc28gZGlzcGF0Y2hlcyB0byB0aGF0LlxuICBpZiAoX2lkZW50aWZpZXIuaXNJZGVudGlmaWVyU3RhcnQoY29kZSwgdGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYpIHx8IGNvZGUgPT09IDkyIC8qICdcXCcgKi8pIHJldHVybiB0aGlzLnJlYWRXb3JkKCk7XG5cbiAgcmV0dXJuIHRoaXMuZ2V0VG9rZW5Gcm9tQ29kZShjb2RlKTtcbn07XG5cbnBwLmZ1bGxDaGFyQ29kZUF0UG9zID0gZnVuY3Rpb24gKCkge1xuICB2YXIgY29kZSA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyk7XG4gIGlmIChjb2RlIDw9IDB4ZDdmZiB8fCBjb2RlID49IDB4ZTAwMCkgcmV0dXJuIGNvZGU7XG4gIHZhciBuZXh0ID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMSk7XG4gIHJldHVybiAoY29kZSA8PCAxMCkgKyBuZXh0IC0gMHgzNWZkYzAwO1xufTtcblxucHAuc2tpcEJsb2NrQ29tbWVudCA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIHN0YXJ0TG9jID0gdGhpcy5vcHRpb25zLm9uQ29tbWVudCAmJiB0aGlzLmN1clBvc2l0aW9uKCk7XG4gIHZhciBzdGFydCA9IHRoaXMucG9zLFxuICAgICAgZW5kID0gdGhpcy5pbnB1dC5pbmRleE9mKFwiKi9cIiwgdGhpcy5wb3MgKz0gMik7XG4gIGlmIChlbmQgPT09IC0xKSB0aGlzLnJhaXNlKHRoaXMucG9zIC0gMiwgXCJVbnRlcm1pbmF0ZWQgY29tbWVudFwiKTtcbiAgdGhpcy5wb3MgPSBlbmQgKyAyO1xuICBpZiAodGhpcy5vcHRpb25zLmxvY2F0aW9ucykge1xuICAgIF93aGl0ZXNwYWNlLmxpbmVCcmVha0cubGFzdEluZGV4ID0gc3RhcnQ7XG4gICAgdmFyIG1hdGNoID0gdW5kZWZpbmVkO1xuICAgIHdoaWxlICgobWF0Y2ggPSBfd2hpdGVzcGFjZS5saW5lQnJlYWtHLmV4ZWModGhpcy5pbnB1dCkpICYmIG1hdGNoLmluZGV4IDwgdGhpcy5wb3MpIHtcbiAgICAgICsrdGhpcy5jdXJMaW5lO1xuICAgICAgdGhpcy5saW5lU3RhcnQgPSBtYXRjaC5pbmRleCArIG1hdGNoWzBdLmxlbmd0aDtcbiAgICB9XG4gIH1cbiAgaWYgKHRoaXMub3B0aW9ucy5vbkNvbW1lbnQpIHRoaXMub3B0aW9ucy5vbkNvbW1lbnQodHJ1ZSwgdGhpcy5pbnB1dC5zbGljZShzdGFydCArIDIsIGVuZCksIHN0YXJ0LCB0aGlzLnBvcywgc3RhcnRMb2MsIHRoaXMuY3VyUG9zaXRpb24oKSk7XG59O1xuXG5wcC5za2lwTGluZUNvbW1lbnQgPSBmdW5jdGlvbiAoc3RhcnRTa2lwKSB7XG4gIHZhciBzdGFydCA9IHRoaXMucG9zO1xuICB2YXIgc3RhcnRMb2MgPSB0aGlzLm9wdGlvbnMub25Db21tZW50ICYmIHRoaXMuY3VyUG9zaXRpb24oKTtcbiAgdmFyIGNoID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICs9IHN0YXJ0U2tpcCk7XG4gIHdoaWxlICh0aGlzLnBvcyA8IHRoaXMuaW5wdXQubGVuZ3RoICYmIGNoICE9PSAxMCAmJiBjaCAhPT0gMTMgJiYgY2ggIT09IDgyMzIgJiYgY2ggIT09IDgyMzMpIHtcbiAgICArK3RoaXMucG9zO1xuICAgIGNoID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zKTtcbiAgfVxuICBpZiAodGhpcy5vcHRpb25zLm9uQ29tbWVudCkgdGhpcy5vcHRpb25zLm9uQ29tbWVudChmYWxzZSwgdGhpcy5pbnB1dC5zbGljZShzdGFydCArIHN0YXJ0U2tpcCwgdGhpcy5wb3MpLCBzdGFydCwgdGhpcy5wb3MsIHN0YXJ0TG9jLCB0aGlzLmN1clBvc2l0aW9uKCkpO1xufTtcblxuLy8gQ2FsbGVkIGF0IHRoZSBzdGFydCBvZiB0aGUgcGFyc2UgYW5kIGFmdGVyIGV2ZXJ5IHRva2VuLiBTa2lwc1xuLy8gd2hpdGVzcGFjZSBhbmQgY29tbWVudHMsIGFuZC5cblxucHAuc2tpcFNwYWNlID0gZnVuY3Rpb24gKCkge1xuICBsb29wOiB3aGlsZSAodGhpcy5wb3MgPCB0aGlzLmlucHV0Lmxlbmd0aCkge1xuICAgIHZhciBjaCA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyk7XG4gICAgc3dpdGNoIChjaCkge1xuICAgICAgY2FzZSAzMjpjYXNlIDE2MDpcbiAgICAgICAgLy8gJyAnXG4gICAgICAgICsrdGhpcy5wb3M7XG4gICAgICAgIGJyZWFrO1xuICAgICAgY2FzZSAxMzpcbiAgICAgICAgaWYgKHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIDEpID09PSAxMCkge1xuICAgICAgICAgICsrdGhpcy5wb3M7XG4gICAgICAgIH1cbiAgICAgIGNhc2UgMTA6Y2FzZSA4MjMyOmNhc2UgODIzMzpcbiAgICAgICAgKyt0aGlzLnBvcztcbiAgICAgICAgaWYgKHRoaXMub3B0aW9ucy5sb2NhdGlvbnMpIHtcbiAgICAgICAgICArK3RoaXMuY3VyTGluZTtcbiAgICAgICAgICB0aGlzLmxpbmVTdGFydCA9IHRoaXMucG9zO1xuICAgICAgICB9XG4gICAgICAgIGJyZWFrO1xuICAgICAgY2FzZSA0NzpcbiAgICAgICAgLy8gJy8nXG4gICAgICAgIHN3aXRjaCAodGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMSkpIHtcbiAgICAgICAgICBjYXNlIDQyOlxuICAgICAgICAgICAgLy8gJyonXG4gICAgICAgICAgICB0aGlzLnNraXBCbG9ja0NvbW1lbnQoKTtcbiAgICAgICAgICAgIGJyZWFrO1xuICAgICAgICAgIGNhc2UgNDc6XG4gICAgICAgICAgICB0aGlzLnNraXBMaW5lQ29tbWVudCgyKTtcbiAgICAgICAgICAgIGJyZWFrO1xuICAgICAgICAgIGRlZmF1bHQ6XG4gICAgICAgICAgICBicmVhayBsb29wO1xuICAgICAgICB9XG4gICAgICAgIGJyZWFrO1xuICAgICAgZGVmYXVsdDpcbiAgICAgICAgaWYgKGNoID4gOCAmJiBjaCA8IDE0IHx8IGNoID49IDU3NjAgJiYgX3doaXRlc3BhY2Uubm9uQVNDSUl3aGl0ZXNwYWNlLnRlc3QoU3RyaW5nLmZyb21DaGFyQ29kZShjaCkpKSB7XG4gICAgICAgICAgKyt0aGlzLnBvcztcbiAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICBicmVhayBsb29wO1xuICAgICAgICB9XG4gICAgfVxuICB9XG59O1xuXG4vLyBDYWxsZWQgYXQgdGhlIGVuZCBvZiBldmVyeSB0b2tlbi4gU2V0cyBgZW5kYCwgYHZhbGAsIGFuZFxuLy8gbWFpbnRhaW5zIGBjb250ZXh0YCBhbmQgYGV4cHJBbGxvd2VkYCwgYW5kIHNraXBzIHRoZSBzcGFjZSBhZnRlclxuLy8gdGhlIHRva2VuLCBzbyB0aGF0IHRoZSBuZXh0IG9uZSdzIGBzdGFydGAgd2lsbCBwb2ludCBhdCB0aGVcbi8vIHJpZ2h0IHBvc2l0aW9uLlxuXG5wcC5maW5pc2hUb2tlbiA9IGZ1bmN0aW9uICh0eXBlLCB2YWwpIHtcbiAgdGhpcy5lbmQgPSB0aGlzLnBvcztcbiAgaWYgKHRoaXMub3B0aW9ucy5sb2NhdGlvbnMpIHRoaXMuZW5kTG9jID0gdGhpcy5jdXJQb3NpdGlvbigpO1xuICB2YXIgcHJldlR5cGUgPSB0aGlzLnR5cGU7XG4gIHRoaXMudHlwZSA9IHR5cGU7XG4gIHRoaXMudmFsdWUgPSB2YWw7XG5cbiAgdGhpcy51cGRhdGVDb250ZXh0KHByZXZUeXBlKTtcbn07XG5cbi8vICMjIyBUb2tlbiByZWFkaW5nXG5cbi8vIFRoaXMgaXMgdGhlIGZ1bmN0aW9uIHRoYXQgaXMgY2FsbGVkIHRvIGZldGNoIHRoZSBuZXh0IHRva2VuLiBJdFxuLy8gaXMgc29tZXdoYXQgb2JzY3VyZSwgYmVjYXVzZSBpdCB3b3JrcyBpbiBjaGFyYWN0ZXIgY29kZXMgcmF0aGVyXG4vLyB0aGFuIGNoYXJhY3RlcnMsIGFuZCBiZWNhdXNlIG9wZXJhdG9yIHBhcnNpbmcgaGFzIGJlZW4gaW5saW5lZFxuLy8gaW50byBpdC5cbi8vXG4vLyBBbGwgaW4gdGhlIG5hbWUgb2Ygc3BlZWQuXG4vL1xucHAucmVhZFRva2VuX2RvdCA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIG5leHQgPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAxKTtcbiAgaWYgKG5leHQgPj0gNDggJiYgbmV4dCA8PSA1NykgcmV0dXJuIHRoaXMucmVhZE51bWJlcih0cnVlKTtcbiAgdmFyIG5leHQyID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMik7XG4gIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNiAmJiBuZXh0ID09PSA0NiAmJiBuZXh0MiA9PT0gNDYpIHtcbiAgICAvLyA0NiA9IGRvdCAnLidcbiAgICB0aGlzLnBvcyArPSAzO1xuICAgIHJldHVybiB0aGlzLmZpbmlzaFRva2VuKF90b2tlbnR5cGUudHlwZXMuZWxsaXBzaXMpO1xuICB9IGVsc2Uge1xuICAgICsrdGhpcy5wb3M7XG4gICAgcmV0dXJuIHRoaXMuZmluaXNoVG9rZW4oX3Rva2VudHlwZS50eXBlcy5kb3QpO1xuICB9XG59O1xuXG5wcC5yZWFkVG9rZW5fc2xhc2ggPSBmdW5jdGlvbiAoKSB7XG4gIC8vICcvJ1xuICB2YXIgbmV4dCA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIDEpO1xuICBpZiAodGhpcy5leHByQWxsb3dlZCkge1xuICAgICsrdGhpcy5wb3M7cmV0dXJuIHRoaXMucmVhZFJlZ2V4cCgpO1xuICB9XG4gIGlmIChuZXh0ID09PSA2MSkgcmV0dXJuIHRoaXMuZmluaXNoT3AoX3Rva2VudHlwZS50eXBlcy5hc3NpZ24sIDIpO1xuICByZXR1cm4gdGhpcy5maW5pc2hPcChfdG9rZW50eXBlLnR5cGVzLnNsYXNoLCAxKTtcbn07XG5cbnBwLnJlYWRUb2tlbl9tdWx0X21vZHVsbyA9IGZ1bmN0aW9uIChjb2RlKSB7XG4gIC8vICclKidcbiAgdmFyIG5leHQgPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAxKTtcbiAgaWYgKG5leHQgPT09IDYxKSByZXR1cm4gdGhpcy5maW5pc2hPcChfdG9rZW50eXBlLnR5cGVzLmFzc2lnbiwgMik7XG4gIHJldHVybiB0aGlzLmZpbmlzaE9wKGNvZGUgPT09IDQyID8gX3Rva2VudHlwZS50eXBlcy5zdGFyIDogX3Rva2VudHlwZS50eXBlcy5tb2R1bG8sIDEpO1xufTtcblxucHAucmVhZFRva2VuX3BpcGVfYW1wID0gZnVuY3Rpb24gKGNvZGUpIHtcbiAgLy8gJ3wmJ1xuICB2YXIgbmV4dCA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIDEpO1xuICBpZiAobmV4dCA9PT0gY29kZSkgcmV0dXJuIHRoaXMuZmluaXNoT3AoY29kZSA9PT0gMTI0ID8gX3Rva2VudHlwZS50eXBlcy5sb2dpY2FsT1IgOiBfdG9rZW50eXBlLnR5cGVzLmxvZ2ljYWxBTkQsIDIpO1xuICBpZiAobmV4dCA9PT0gNjEpIHJldHVybiB0aGlzLmZpbmlzaE9wKF90b2tlbnR5cGUudHlwZXMuYXNzaWduLCAyKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoT3AoY29kZSA9PT0gMTI0ID8gX3Rva2VudHlwZS50eXBlcy5iaXR3aXNlT1IgOiBfdG9rZW50eXBlLnR5cGVzLmJpdHdpc2VBTkQsIDEpO1xufTtcblxucHAucmVhZFRva2VuX2NhcmV0ID0gZnVuY3Rpb24gKCkge1xuICAvLyAnXidcbiAgdmFyIG5leHQgPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAxKTtcbiAgaWYgKG5leHQgPT09IDYxKSByZXR1cm4gdGhpcy5maW5pc2hPcChfdG9rZW50eXBlLnR5cGVzLmFzc2lnbiwgMik7XG4gIHJldHVybiB0aGlzLmZpbmlzaE9wKF90b2tlbnR5cGUudHlwZXMuYml0d2lzZVhPUiwgMSk7XG59O1xuXG5wcC5yZWFkVG9rZW5fcGx1c19taW4gPSBmdW5jdGlvbiAoY29kZSkge1xuICAvLyAnKy0nXG4gIHZhciBuZXh0ID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMSk7XG4gIGlmIChuZXh0ID09PSBjb2RlKSB7XG4gICAgaWYgKG5leHQgPT0gNDUgJiYgdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMikgPT0gNjIgJiYgX3doaXRlc3BhY2UubGluZUJyZWFrLnRlc3QodGhpcy5pbnB1dC5zbGljZSh0aGlzLmxhc3RUb2tFbmQsIHRoaXMucG9zKSkpIHtcbiAgICAgIC8vIEEgYC0tPmAgbGluZSBjb21tZW50XG4gICAgICB0aGlzLnNraXBMaW5lQ29tbWVudCgzKTtcbiAgICAgIHRoaXMuc2tpcFNwYWNlKCk7XG4gICAgICByZXR1cm4gdGhpcy5uZXh0VG9rZW4oKTtcbiAgICB9XG4gICAgcmV0dXJuIHRoaXMuZmluaXNoT3AoX3Rva2VudHlwZS50eXBlcy5pbmNEZWMsIDIpO1xuICB9XG4gIGlmIChuZXh0ID09PSA2MSkgcmV0dXJuIHRoaXMuZmluaXNoT3AoX3Rva2VudHlwZS50eXBlcy5hc3NpZ24sIDIpO1xuICByZXR1cm4gdGhpcy5maW5pc2hPcChfdG9rZW50eXBlLnR5cGVzLnBsdXNNaW4sIDEpO1xufTtcblxucHAucmVhZFRva2VuX2x0X2d0ID0gZnVuY3Rpb24gKGNvZGUpIHtcbiAgLy8gJzw+J1xuICB2YXIgbmV4dCA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIDEpO1xuICB2YXIgc2l6ZSA9IDE7XG4gIGlmIChuZXh0ID09PSBjb2RlKSB7XG4gICAgc2l6ZSA9IGNvZGUgPT09IDYyICYmIHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIDIpID09PSA2MiA/IDMgOiAyO1xuICAgIGlmICh0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyBzaXplKSA9PT0gNjEpIHJldHVybiB0aGlzLmZpbmlzaE9wKF90b2tlbnR5cGUudHlwZXMuYXNzaWduLCBzaXplICsgMSk7XG4gICAgcmV0dXJuIHRoaXMuZmluaXNoT3AoX3Rva2VudHlwZS50eXBlcy5iaXRTaGlmdCwgc2l6ZSk7XG4gIH1cbiAgaWYgKG5leHQgPT0gMzMgJiYgY29kZSA9PSA2MCAmJiB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAyKSA9PSA0NSAmJiB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAzKSA9PSA0NSkge1xuICAgIGlmICh0aGlzLmluTW9kdWxlKSB0aGlzLnVuZXhwZWN0ZWQoKTtcbiAgICAvLyBgPCEtLWAsIGFuIFhNTC1zdHlsZSBjb21tZW50IHRoYXQgc2hvdWxkIGJlIGludGVycHJldGVkIGFzIGEgbGluZSBjb21tZW50XG4gICAgdGhpcy5za2lwTGluZUNvbW1lbnQoNCk7XG4gICAgdGhpcy5za2lwU3BhY2UoKTtcbiAgICByZXR1cm4gdGhpcy5uZXh0VG9rZW4oKTtcbiAgfVxuICBpZiAobmV4dCA9PT0gNjEpIHNpemUgPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAyKSA9PT0gNjEgPyAzIDogMjtcbiAgcmV0dXJuIHRoaXMuZmluaXNoT3AoX3Rva2VudHlwZS50eXBlcy5yZWxhdGlvbmFsLCBzaXplKTtcbn07XG5cbnBwLnJlYWRUb2tlbl9lcV9leGNsID0gZnVuY3Rpb24gKGNvZGUpIHtcbiAgLy8gJz0hJ1xuICB2YXIgbmV4dCA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIDEpO1xuICBpZiAobmV4dCA9PT0gNjEpIHJldHVybiB0aGlzLmZpbmlzaE9wKF90b2tlbnR5cGUudHlwZXMuZXF1YWxpdHksIHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIDIpID09PSA2MSA/IDMgOiAyKTtcbiAgaWYgKGNvZGUgPT09IDYxICYmIG5leHQgPT09IDYyICYmIHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KSB7XG4gICAgLy8gJz0+J1xuICAgIHRoaXMucG9zICs9IDI7XG4gICAgcmV0dXJuIHRoaXMuZmluaXNoVG9rZW4oX3Rva2VudHlwZS50eXBlcy5hcnJvdyk7XG4gIH1cbiAgcmV0dXJuIHRoaXMuZmluaXNoT3AoY29kZSA9PT0gNjEgPyBfdG9rZW50eXBlLnR5cGVzLmVxIDogX3Rva2VudHlwZS50eXBlcy5wcmVmaXgsIDEpO1xufTtcblxucHAuZ2V0VG9rZW5Gcm9tQ29kZSA9IGZ1bmN0aW9uIChjb2RlKSB7XG4gIHN3aXRjaCAoY29kZSkge1xuICAgIC8vIFRoZSBpbnRlcnByZXRhdGlvbiBvZiBhIGRvdCBkZXBlbmRzIG9uIHdoZXRoZXIgaXQgaXMgZm9sbG93ZWRcbiAgICAvLyBieSBhIGRpZ2l0IG9yIGFub3RoZXIgdHdvIGRvdHMuXG4gICAgY2FzZSA0NjpcbiAgICAgIC8vICcuJ1xuICAgICAgcmV0dXJuIHRoaXMucmVhZFRva2VuX2RvdCgpO1xuXG4gICAgLy8gUHVuY3R1YXRpb24gdG9rZW5zLlxuICAgIGNhc2UgNDA6XG4gICAgICArK3RoaXMucG9zO3JldHVybiB0aGlzLmZpbmlzaFRva2VuKF90b2tlbnR5cGUudHlwZXMucGFyZW5MKTtcbiAgICBjYXNlIDQxOlxuICAgICAgKyt0aGlzLnBvcztyZXR1cm4gdGhpcy5maW5pc2hUb2tlbihfdG9rZW50eXBlLnR5cGVzLnBhcmVuUik7XG4gICAgY2FzZSA1OTpcbiAgICAgICsrdGhpcy5wb3M7cmV0dXJuIHRoaXMuZmluaXNoVG9rZW4oX3Rva2VudHlwZS50eXBlcy5zZW1pKTtcbiAgICBjYXNlIDQ0OlxuICAgICAgKyt0aGlzLnBvcztyZXR1cm4gdGhpcy5maW5pc2hUb2tlbihfdG9rZW50eXBlLnR5cGVzLmNvbW1hKTtcbiAgICBjYXNlIDkxOlxuICAgICAgKyt0aGlzLnBvcztyZXR1cm4gdGhpcy5maW5pc2hUb2tlbihfdG9rZW50eXBlLnR5cGVzLmJyYWNrZXRMKTtcbiAgICBjYXNlIDkzOlxuICAgICAgKyt0aGlzLnBvcztyZXR1cm4gdGhpcy5maW5pc2hUb2tlbihfdG9rZW50eXBlLnR5cGVzLmJyYWNrZXRSKTtcbiAgICBjYXNlIDEyMzpcbiAgICAgICsrdGhpcy5wb3M7cmV0dXJuIHRoaXMuZmluaXNoVG9rZW4oX3Rva2VudHlwZS50eXBlcy5icmFjZUwpO1xuICAgIGNhc2UgMTI1OlxuICAgICAgKyt0aGlzLnBvcztyZXR1cm4gdGhpcy5maW5pc2hUb2tlbihfdG9rZW50eXBlLnR5cGVzLmJyYWNlUik7XG4gICAgY2FzZSA1ODpcbiAgICAgICsrdGhpcy5wb3M7cmV0dXJuIHRoaXMuZmluaXNoVG9rZW4oX3Rva2VudHlwZS50eXBlcy5jb2xvbik7XG4gICAgY2FzZSA2MzpcbiAgICAgICsrdGhpcy5wb3M7cmV0dXJuIHRoaXMuZmluaXNoVG9rZW4oX3Rva2VudHlwZS50eXBlcy5xdWVzdGlvbik7XG5cbiAgICBjYXNlIDk2OlxuICAgICAgLy8gJ2AnXG4gICAgICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uIDwgNikgYnJlYWs7XG4gICAgICArK3RoaXMucG9zO1xuICAgICAgcmV0dXJuIHRoaXMuZmluaXNoVG9rZW4oX3Rva2VudHlwZS50eXBlcy5iYWNrUXVvdGUpO1xuXG4gICAgY2FzZSA0ODpcbiAgICAgIC8vICcwJ1xuICAgICAgdmFyIG5leHQgPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAxKTtcbiAgICAgIGlmIChuZXh0ID09PSAxMjAgfHwgbmV4dCA9PT0gODgpIHJldHVybiB0aGlzLnJlYWRSYWRpeE51bWJlcigxNik7IC8vICcweCcsICcwWCcgLSBoZXggbnVtYmVyXG4gICAgICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYpIHtcbiAgICAgICAgaWYgKG5leHQgPT09IDExMSB8fCBuZXh0ID09PSA3OSkgcmV0dXJuIHRoaXMucmVhZFJhZGl4TnVtYmVyKDgpOyAvLyAnMG8nLCAnME8nIC0gb2N0YWwgbnVtYmVyXG4gICAgICAgIGlmIChuZXh0ID09PSA5OCB8fCBuZXh0ID09PSA2NikgcmV0dXJuIHRoaXMucmVhZFJhZGl4TnVtYmVyKDIpOyAvLyAnMGInLCAnMEInIC0gYmluYXJ5IG51bWJlclxuICAgICAgfVxuICAgIC8vIEFueXRoaW5nIGVsc2UgYmVnaW5uaW5nIHdpdGggYSBkaWdpdCBpcyBhbiBpbnRlZ2VyLCBvY3RhbFxuICAgIC8vIG51bWJlciwgb3IgZmxvYXQuXG4gICAgY2FzZSA0OTpjYXNlIDUwOmNhc2UgNTE6Y2FzZSA1MjpjYXNlIDUzOmNhc2UgNTQ6Y2FzZSA1NTpjYXNlIDU2OmNhc2UgNTc6XG4gICAgICAvLyAxLTlcbiAgICAgIHJldHVybiB0aGlzLnJlYWROdW1iZXIoZmFsc2UpO1xuXG4gICAgLy8gUXVvdGVzIHByb2R1Y2Ugc3RyaW5ncy5cbiAgICBjYXNlIDM0OmNhc2UgMzk6XG4gICAgICAvLyAnXCInLCBcIidcIlxuICAgICAgcmV0dXJuIHRoaXMucmVhZFN0cmluZyhjb2RlKTtcblxuICAgIC8vIE9wZXJhdG9ycyBhcmUgcGFyc2VkIGlubGluZSBpbiB0aW55IHN0YXRlIG1hY2hpbmVzLiAnPScgKDYxKSBpc1xuICAgIC8vIG9mdGVuIHJlZmVycmVkIHRvLiBgZmluaXNoT3BgIHNpbXBseSBza2lwcyB0aGUgYW1vdW50IG9mXG4gICAgLy8gY2hhcmFjdGVycyBpdCBpcyBnaXZlbiBhcyBzZWNvbmQgYXJndW1lbnQsIGFuZCByZXR1cm5zIGEgdG9rZW5cbiAgICAvLyBvZiB0aGUgdHlwZSBnaXZlbiBieSBpdHMgZmlyc3QgYXJndW1lbnQuXG5cbiAgICBjYXNlIDQ3OlxuICAgICAgLy8gJy8nXG4gICAgICByZXR1cm4gdGhpcy5yZWFkVG9rZW5fc2xhc2goKTtcblxuICAgIGNhc2UgMzc6Y2FzZSA0MjpcbiAgICAgIC8vICclKidcbiAgICAgIHJldHVybiB0aGlzLnJlYWRUb2tlbl9tdWx0X21vZHVsbyhjb2RlKTtcblxuICAgIGNhc2UgMTI0OmNhc2UgMzg6XG4gICAgICAvLyAnfCYnXG4gICAgICByZXR1cm4gdGhpcy5yZWFkVG9rZW5fcGlwZV9hbXAoY29kZSk7XG5cbiAgICBjYXNlIDk0OlxuICAgICAgLy8gJ14nXG4gICAgICByZXR1cm4gdGhpcy5yZWFkVG9rZW5fY2FyZXQoKTtcblxuICAgIGNhc2UgNDM6Y2FzZSA0NTpcbiAgICAgIC8vICcrLSdcbiAgICAgIHJldHVybiB0aGlzLnJlYWRUb2tlbl9wbHVzX21pbihjb2RlKTtcblxuICAgIGNhc2UgNjA6Y2FzZSA2MjpcbiAgICAgIC8vICc8PidcbiAgICAgIHJldHVybiB0aGlzLnJlYWRUb2tlbl9sdF9ndChjb2RlKTtcblxuICAgIGNhc2UgNjE6Y2FzZSAzMzpcbiAgICAgIC8vICc9ISdcbiAgICAgIHJldHVybiB0aGlzLnJlYWRUb2tlbl9lcV9leGNsKGNvZGUpO1xuXG4gICAgY2FzZSAxMjY6XG4gICAgICAvLyAnfidcbiAgICAgIHJldHVybiB0aGlzLmZpbmlzaE9wKF90b2tlbnR5cGUudHlwZXMucHJlZml4LCAxKTtcbiAgfVxuXG4gIHRoaXMucmFpc2UodGhpcy5wb3MsIFwiVW5leHBlY3RlZCBjaGFyYWN0ZXIgJ1wiICsgY29kZVBvaW50VG9TdHJpbmcoY29kZSkgKyBcIidcIik7XG59O1xuXG5wcC5maW5pc2hPcCA9IGZ1bmN0aW9uICh0eXBlLCBzaXplKSB7XG4gIHZhciBzdHIgPSB0aGlzLmlucHV0LnNsaWNlKHRoaXMucG9zLCB0aGlzLnBvcyArIHNpemUpO1xuICB0aGlzLnBvcyArPSBzaXplO1xuICByZXR1cm4gdGhpcy5maW5pc2hUb2tlbih0eXBlLCBzdHIpO1xufTtcblxuLy8gUGFyc2UgYSByZWd1bGFyIGV4cHJlc3Npb24uIFNvbWUgY29udGV4dC1hd2FyZW5lc3MgaXMgbmVjZXNzYXJ5LFxuLy8gc2luY2UgYSAnLycgaW5zaWRlIGEgJ1tdJyBzZXQgZG9lcyBub3QgZW5kIHRoZSBleHByZXNzaW9uLlxuXG5mdW5jdGlvbiB0cnlDcmVhdGVSZWdleHAoc3JjLCBmbGFncywgdGhyb3dFcnJvckF0KSB7XG4gIHRyeSB7XG4gICAgcmV0dXJuIG5ldyBSZWdFeHAoc3JjLCBmbGFncyk7XG4gIH0gY2F0Y2ggKGUpIHtcbiAgICBpZiAodGhyb3dFcnJvckF0ICE9PSB1bmRlZmluZWQpIHtcbiAgICAgIGlmIChlIGluc3RhbmNlb2YgU3ludGF4RXJyb3IpIHRoaXMucmFpc2UodGhyb3dFcnJvckF0LCBcIkVycm9yIHBhcnNpbmcgcmVndWxhciBleHByZXNzaW9uOiBcIiArIGUubWVzc2FnZSk7XG4gICAgICB0aGlzLnJhaXNlKGUpO1xuICAgIH1cbiAgfVxufVxuXG52YXIgcmVnZXhwVW5pY29kZVN1cHBvcnQgPSAhIXRyeUNyZWF0ZVJlZ2V4cChcIu+/v1wiLCBcInVcIik7XG5cbnBwLnJlYWRSZWdleHAgPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBfdGhpcyA9IHRoaXM7XG5cbiAgdmFyIGVzY2FwZWQgPSB1bmRlZmluZWQsXG4gICAgICBpbkNsYXNzID0gdW5kZWZpbmVkLFxuICAgICAgc3RhcnQgPSB0aGlzLnBvcztcbiAgZm9yICg7Oykge1xuICAgIGlmICh0aGlzLnBvcyA+PSB0aGlzLmlucHV0Lmxlbmd0aCkgdGhpcy5yYWlzZShzdGFydCwgXCJVbnRlcm1pbmF0ZWQgcmVndWxhciBleHByZXNzaW9uXCIpO1xuICAgIHZhciBjaCA9IHRoaXMuaW5wdXQuY2hhckF0KHRoaXMucG9zKTtcbiAgICBpZiAoX3doaXRlc3BhY2UubGluZUJyZWFrLnRlc3QoY2gpKSB0aGlzLnJhaXNlKHN0YXJ0LCBcIlVudGVybWluYXRlZCByZWd1bGFyIGV4cHJlc3Npb25cIik7XG4gICAgaWYgKCFlc2NhcGVkKSB7XG4gICAgICBpZiAoY2ggPT09IFwiW1wiKSBpbkNsYXNzID0gdHJ1ZTtlbHNlIGlmIChjaCA9PT0gXCJdXCIgJiYgaW5DbGFzcykgaW5DbGFzcyA9IGZhbHNlO2Vsc2UgaWYgKGNoID09PSBcIi9cIiAmJiAhaW5DbGFzcykgYnJlYWs7XG4gICAgICBlc2NhcGVkID0gY2ggPT09IFwiXFxcXFwiO1xuICAgIH0gZWxzZSBlc2NhcGVkID0gZmFsc2U7XG4gICAgKyt0aGlzLnBvcztcbiAgfVxuICB2YXIgY29udGVudCA9IHRoaXMuaW5wdXQuc2xpY2Uoc3RhcnQsIHRoaXMucG9zKTtcbiAgKyt0aGlzLnBvcztcbiAgLy8gTmVlZCB0byB1c2UgYHJlYWRXb3JkMWAgYmVjYXVzZSAnXFx1WFhYWCcgc2VxdWVuY2VzIGFyZSBhbGxvd2VkXG4gIC8vIGhlcmUgKGRvbid0IGFzaykuXG4gIHZhciBtb2RzID0gdGhpcy5yZWFkV29yZDEoKTtcbiAgdmFyIHRtcCA9IGNvbnRlbnQ7XG4gIGlmIChtb2RzKSB7XG4gICAgdmFyIHZhbGlkRmxhZ3MgPSAvXltnbXNpeV0qJC87XG4gICAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KSB2YWxpZEZsYWdzID0gL15bZ21zaXl1XSokLztcbiAgICBpZiAoIXZhbGlkRmxhZ3MudGVzdChtb2RzKSkgdGhpcy5yYWlzZShzdGFydCwgXCJJbnZhbGlkIHJlZ3VsYXIgZXhwcmVzc2lvbiBmbGFnXCIpO1xuICAgIGlmIChtb2RzLmluZGV4T2YoXCJ1XCIpID49IDAgJiYgIXJlZ2V4cFVuaWNvZGVTdXBwb3J0KSB7XG4gICAgICAvLyBSZXBsYWNlIGVhY2ggYXN0cmFsIHN5bWJvbCBhbmQgZXZlcnkgVW5pY29kZSBlc2NhcGUgc2VxdWVuY2UgdGhhdFxuICAgICAgLy8gcG9zc2libHkgcmVwcmVzZW50cyBhbiBhc3RyYWwgc3ltYm9sIG9yIGEgcGFpcmVkIHN1cnJvZ2F0ZSB3aXRoIGFcbiAgICAgIC8vIHNpbmdsZSBBU0NJSSBzeW1ib2wgdG8gYXZvaWQgdGhyb3dpbmcgb24gcmVndWxhciBleHByZXNzaW9ucyB0aGF0XG4gICAgICAvLyBhcmUgb25seSB2YWxpZCBpbiBjb21iaW5hdGlvbiB3aXRoIHRoZSBgL3VgIGZsYWcuXG4gICAgICAvLyBOb3RlOiByZXBsYWNpbmcgd2l0aCB0aGUgQVNDSUkgc3ltYm9sIGB4YCBtaWdodCBjYXVzZSBmYWxzZVxuICAgICAgLy8gbmVnYXRpdmVzIGluIHVubGlrZWx5IHNjZW5hcmlvcy4gRm9yIGV4YW1wbGUsIGBbXFx1ezYxfS1iXWAgaXMgYVxuICAgICAgLy8gcGVyZmVjdGx5IHZhbGlkIHBhdHRlcm4gdGhhdCBpcyBlcXVpdmFsZW50IHRvIGBbYS1iXWAsIGJ1dCBpdCB3b3VsZFxuICAgICAgLy8gYmUgcmVwbGFjZWQgYnkgYFt4LWJdYCB3aGljaCB0aHJvd3MgYW4gZXJyb3IuXG4gICAgICB0bXAgPSB0bXAucmVwbGFjZSgvXFxcXHVcXHsoWzAtOWEtZkEtRl0rKVxcfS9nLCBmdW5jdGlvbiAobWF0Y2gsIGNvZGUsIG9mZnNldCkge1xuICAgICAgICBjb2RlID0gTnVtYmVyKFwiMHhcIiArIGNvZGUpO1xuICAgICAgICBpZiAoY29kZSA+IDB4MTBGRkZGKSBfdGhpcy5yYWlzZShzdGFydCArIG9mZnNldCArIDMsIFwiQ29kZSBwb2ludCBvdXQgb2YgYm91bmRzXCIpO1xuICAgICAgICByZXR1cm4gXCJ4XCI7XG4gICAgICB9KTtcbiAgICAgIHRtcCA9IHRtcC5yZXBsYWNlKC9cXFxcdShbYS1mQS1GMC05XXs0fSl8W1xcdUQ4MDAtXFx1REJGRl1bXFx1REMwMC1cXHVERkZGXS9nLCBcInhcIik7XG4gICAgfVxuICB9XG4gIC8vIERldGVjdCBpbnZhbGlkIHJlZ3VsYXIgZXhwcmVzc2lvbnMuXG4gIHZhciB2YWx1ZSA9IG51bGw7XG4gIC8vIFJoaW5vJ3MgcmVndWxhciBleHByZXNzaW9uIHBhcnNlciBpcyBmbGFreSBhbmQgdGhyb3dzIHVuY2F0Y2hhYmxlIGV4Y2VwdGlvbnMsXG4gIC8vIHNvIGRvbid0IGRvIGRldGVjdGlvbiBpZiB3ZSBhcmUgcnVubmluZyB1bmRlciBSaGlub1xuICBpZiAoIWlzUmhpbm8pIHtcbiAgICB0cnlDcmVhdGVSZWdleHAodG1wLCB1bmRlZmluZWQsIHN0YXJ0KTtcbiAgICAvLyBHZXQgYSByZWd1bGFyIGV4cHJlc3Npb24gb2JqZWN0IGZvciB0aGlzIHBhdHRlcm4tZmxhZyBwYWlyLCBvciBgbnVsbGAgaW5cbiAgICAvLyBjYXNlIHRoZSBjdXJyZW50IGVudmlyb25tZW50IGRvZXNuJ3Qgc3VwcG9ydCB0aGUgZmxhZ3MgaXQgdXNlcy5cbiAgICB2YWx1ZSA9IHRyeUNyZWF0ZVJlZ2V4cChjb250ZW50LCBtb2RzKTtcbiAgfVxuICByZXR1cm4gdGhpcy5maW5pc2hUb2tlbihfdG9rZW50eXBlLnR5cGVzLnJlZ2V4cCwgeyBwYXR0ZXJuOiBjb250ZW50LCBmbGFnczogbW9kcywgdmFsdWU6IHZhbHVlIH0pO1xufTtcblxuLy8gUmVhZCBhbiBpbnRlZ2VyIGluIHRoZSBnaXZlbiByYWRpeC4gUmV0dXJuIG51bGwgaWYgemVybyBkaWdpdHNcbi8vIHdlcmUgcmVhZCwgdGhlIGludGVnZXIgdmFsdWUgb3RoZXJ3aXNlLiBXaGVuIGBsZW5gIGlzIGdpdmVuLCB0aGlzXG4vLyB3aWxsIHJldHVybiBgbnVsbGAgdW5sZXNzIHRoZSBpbnRlZ2VyIGhhcyBleGFjdGx5IGBsZW5gIGRpZ2l0cy5cblxucHAucmVhZEludCA9IGZ1bmN0aW9uIChyYWRpeCwgbGVuKSB7XG4gIHZhciBzdGFydCA9IHRoaXMucG9zLFxuICAgICAgdG90YWwgPSAwO1xuICBmb3IgKHZhciBpID0gMCwgZSA9IGxlbiA9PSBudWxsID8gSW5maW5pdHkgOiBsZW47IGkgPCBlOyArK2kpIHtcbiAgICB2YXIgY29kZSA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyksXG4gICAgICAgIHZhbCA9IHVuZGVmaW5lZDtcbiAgICBpZiAoY29kZSA+PSA5NykgdmFsID0gY29kZSAtIDk3ICsgMTA7IC8vIGFcbiAgICBlbHNlIGlmIChjb2RlID49IDY1KSB2YWwgPSBjb2RlIC0gNjUgKyAxMDsgLy8gQVxuICAgIGVsc2UgaWYgKGNvZGUgPj0gNDggJiYgY29kZSA8PSA1NykgdmFsID0gY29kZSAtIDQ4OyAvLyAwLTlcbiAgICBlbHNlIHZhbCA9IEluZmluaXR5O1xuICAgIGlmICh2YWwgPj0gcmFkaXgpIGJyZWFrO1xuICAgICsrdGhpcy5wb3M7XG4gICAgdG90YWwgPSB0b3RhbCAqIHJhZGl4ICsgdmFsO1xuICB9XG4gIGlmICh0aGlzLnBvcyA9PT0gc3RhcnQgfHwgbGVuICE9IG51bGwgJiYgdGhpcy5wb3MgLSBzdGFydCAhPT0gbGVuKSByZXR1cm4gbnVsbDtcblxuICByZXR1cm4gdG90YWw7XG59O1xuXG5wcC5yZWFkUmFkaXhOdW1iZXIgPSBmdW5jdGlvbiAocmFkaXgpIHtcbiAgdGhpcy5wb3MgKz0gMjsgLy8gMHhcbiAgdmFyIHZhbCA9IHRoaXMucmVhZEludChyYWRpeCk7XG4gIGlmICh2YWwgPT0gbnVsbCkgdGhpcy5yYWlzZSh0aGlzLnN0YXJ0ICsgMiwgXCJFeHBlY3RlZCBudW1iZXIgaW4gcmFkaXggXCIgKyByYWRpeCk7XG4gIGlmIChfaWRlbnRpZmllci5pc0lkZW50aWZpZXJTdGFydCh0aGlzLmZ1bGxDaGFyQ29kZUF0UG9zKCkpKSB0aGlzLnJhaXNlKHRoaXMucG9zLCBcIklkZW50aWZpZXIgZGlyZWN0bHkgYWZ0ZXIgbnVtYmVyXCIpO1xuICByZXR1cm4gdGhpcy5maW5pc2hUb2tlbihfdG9rZW50eXBlLnR5cGVzLm51bSwgdmFsKTtcbn07XG5cbi8vIFJlYWQgYW4gaW50ZWdlciwgb2N0YWwgaW50ZWdlciwgb3IgZmxvYXRpbmctcG9pbnQgbnVtYmVyLlxuXG5wcC5yZWFkTnVtYmVyID0gZnVuY3Rpb24gKHN0YXJ0c1dpdGhEb3QpIHtcbiAgdmFyIHN0YXJ0ID0gdGhpcy5wb3MsXG4gICAgICBpc0Zsb2F0ID0gZmFsc2UsXG4gICAgICBvY3RhbCA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcykgPT09IDQ4O1xuICBpZiAoIXN0YXJ0c1dpdGhEb3QgJiYgdGhpcy5yZWFkSW50KDEwKSA9PT0gbnVsbCkgdGhpcy5yYWlzZShzdGFydCwgXCJJbnZhbGlkIG51bWJlclwiKTtcbiAgdmFyIG5leHQgPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MpO1xuICBpZiAobmV4dCA9PT0gNDYpIHtcbiAgICAvLyAnLidcbiAgICArK3RoaXMucG9zO1xuICAgIHRoaXMucmVhZEludCgxMCk7XG4gICAgaXNGbG9hdCA9IHRydWU7XG4gICAgbmV4dCA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyk7XG4gIH1cbiAgaWYgKG5leHQgPT09IDY5IHx8IG5leHQgPT09IDEwMSkge1xuICAgIC8vICdlRSdcbiAgICBuZXh0ID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KCsrdGhpcy5wb3MpO1xuICAgIGlmIChuZXh0ID09PSA0MyB8fCBuZXh0ID09PSA0NSkgKyt0aGlzLnBvczsgLy8gJystJ1xuICAgIGlmICh0aGlzLnJlYWRJbnQoMTApID09PSBudWxsKSB0aGlzLnJhaXNlKHN0YXJ0LCBcIkludmFsaWQgbnVtYmVyXCIpO1xuICAgIGlzRmxvYXQgPSB0cnVlO1xuICB9XG4gIGlmIChfaWRlbnRpZmllci5pc0lkZW50aWZpZXJTdGFydCh0aGlzLmZ1bGxDaGFyQ29kZUF0UG9zKCkpKSB0aGlzLnJhaXNlKHRoaXMucG9zLCBcIklkZW50aWZpZXIgZGlyZWN0bHkgYWZ0ZXIgbnVtYmVyXCIpO1xuXG4gIHZhciBzdHIgPSB0aGlzLmlucHV0LnNsaWNlKHN0YXJ0LCB0aGlzLnBvcyksXG4gICAgICB2YWwgPSB1bmRlZmluZWQ7XG4gIGlmIChpc0Zsb2F0KSB2YWwgPSBwYXJzZUZsb2F0KHN0cik7ZWxzZSBpZiAoIW9jdGFsIHx8IHN0ci5sZW5ndGggPT09IDEpIHZhbCA9IHBhcnNlSW50KHN0ciwgMTApO2Vsc2UgaWYgKC9bODldLy50ZXN0KHN0cikgfHwgdGhpcy5zdHJpY3QpIHRoaXMucmFpc2Uoc3RhcnQsIFwiSW52YWxpZCBudW1iZXJcIik7ZWxzZSB2YWwgPSBwYXJzZUludChzdHIsIDgpO1xuICByZXR1cm4gdGhpcy5maW5pc2hUb2tlbihfdG9rZW50eXBlLnR5cGVzLm51bSwgdmFsKTtcbn07XG5cbi8vIFJlYWQgYSBzdHJpbmcgdmFsdWUsIGludGVycHJldGluZyBiYWNrc2xhc2gtZXNjYXBlcy5cblxucHAucmVhZENvZGVQb2ludCA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIGNoID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zKSxcbiAgICAgIGNvZGUgPSB1bmRlZmluZWQ7XG5cbiAgaWYgKGNoID09PSAxMjMpIHtcbiAgICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uIDwgNikgdGhpcy51bmV4cGVjdGVkKCk7XG4gICAgdmFyIGNvZGVQb3MgPSArK3RoaXMucG9zO1xuICAgIGNvZGUgPSB0aGlzLnJlYWRIZXhDaGFyKHRoaXMuaW5wdXQuaW5kZXhPZihcIn1cIiwgdGhpcy5wb3MpIC0gdGhpcy5wb3MpO1xuICAgICsrdGhpcy5wb3M7XG4gICAgaWYgKGNvZGUgPiAweDEwRkZGRikgdGhpcy5yYWlzZShjb2RlUG9zLCBcIkNvZGUgcG9pbnQgb3V0IG9mIGJvdW5kc1wiKTtcbiAgfSBlbHNlIHtcbiAgICBjb2RlID0gdGhpcy5yZWFkSGV4Q2hhcig0KTtcbiAgfVxuICByZXR1cm4gY29kZTtcbn07XG5cbmZ1bmN0aW9uIGNvZGVQb2ludFRvU3RyaW5nKGNvZGUpIHtcbiAgLy8gVVRGLTE2IERlY29kaW5nXG4gIGlmIChjb2RlIDw9IDB4RkZGRikgcmV0dXJuIFN0cmluZy5mcm9tQ2hhckNvZGUoY29kZSk7XG4gIGNvZGUgLT0gMHgxMDAwMDtcbiAgcmV0dXJuIFN0cmluZy5mcm9tQ2hhckNvZGUoKGNvZGUgPj4gMTApICsgMHhEODAwLCAoY29kZSAmIDEwMjMpICsgMHhEQzAwKTtcbn1cblxucHAucmVhZFN0cmluZyA9IGZ1bmN0aW9uIChxdW90ZSkge1xuICB2YXIgb3V0ID0gXCJcIixcbiAgICAgIGNodW5rU3RhcnQgPSArK3RoaXMucG9zO1xuICBmb3IgKDs7KSB7XG4gICAgaWYgKHRoaXMucG9zID49IHRoaXMuaW5wdXQubGVuZ3RoKSB0aGlzLnJhaXNlKHRoaXMuc3RhcnQsIFwiVW50ZXJtaW5hdGVkIHN0cmluZyBjb25zdGFudFwiKTtcbiAgICB2YXIgY2ggPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MpO1xuICAgIGlmIChjaCA9PT0gcXVvdGUpIGJyZWFrO1xuICAgIGlmIChjaCA9PT0gOTIpIHtcbiAgICAgIC8vICdcXCdcbiAgICAgIG91dCArPSB0aGlzLmlucHV0LnNsaWNlKGNodW5rU3RhcnQsIHRoaXMucG9zKTtcbiAgICAgIG91dCArPSB0aGlzLnJlYWRFc2NhcGVkQ2hhcihmYWxzZSk7XG4gICAgICBjaHVua1N0YXJ0ID0gdGhpcy5wb3M7XG4gICAgfSBlbHNlIHtcbiAgICAgIGlmIChfd2hpdGVzcGFjZS5pc05ld0xpbmUoY2gpKSB0aGlzLnJhaXNlKHRoaXMuc3RhcnQsIFwiVW50ZXJtaW5hdGVkIHN0cmluZyBjb25zdGFudFwiKTtcbiAgICAgICsrdGhpcy5wb3M7XG4gICAgfVxuICB9XG4gIG91dCArPSB0aGlzLmlucHV0LnNsaWNlKGNodW5rU3RhcnQsIHRoaXMucG9zKyspO1xuICByZXR1cm4gdGhpcy5maW5pc2hUb2tlbihfdG9rZW50eXBlLnR5cGVzLnN0cmluZywgb3V0KTtcbn07XG5cbi8vIFJlYWRzIHRlbXBsYXRlIHN0cmluZyB0b2tlbnMuXG5cbnBwLnJlYWRUbXBsVG9rZW4gPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBvdXQgPSBcIlwiLFxuICAgICAgY2h1bmtTdGFydCA9IHRoaXMucG9zO1xuICBmb3IgKDs7KSB7XG4gICAgaWYgKHRoaXMucG9zID49IHRoaXMuaW5wdXQubGVuZ3RoKSB0aGlzLnJhaXNlKHRoaXMuc3RhcnQsIFwiVW50ZXJtaW5hdGVkIHRlbXBsYXRlXCIpO1xuICAgIHZhciBjaCA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyk7XG4gICAgaWYgKGNoID09PSA5NiB8fCBjaCA9PT0gMzYgJiYgdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMSkgPT09IDEyMykge1xuICAgICAgLy8gJ2AnLCAnJHsnXG4gICAgICBpZiAodGhpcy5wb3MgPT09IHRoaXMuc3RhcnQgJiYgdGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLnRlbXBsYXRlKSB7XG4gICAgICAgIGlmIChjaCA9PT0gMzYpIHtcbiAgICAgICAgICB0aGlzLnBvcyArPSAyO1xuICAgICAgICAgIHJldHVybiB0aGlzLmZpbmlzaFRva2VuKF90b2tlbnR5cGUudHlwZXMuZG9sbGFyQnJhY2VMKTtcbiAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICArK3RoaXMucG9zO1xuICAgICAgICAgIHJldHVybiB0aGlzLmZpbmlzaFRva2VuKF90b2tlbnR5cGUudHlwZXMuYmFja1F1b3RlKTtcbiAgICAgICAgfVxuICAgICAgfVxuICAgICAgb3V0ICs9IHRoaXMuaW5wdXQuc2xpY2UoY2h1bmtTdGFydCwgdGhpcy5wb3MpO1xuICAgICAgcmV0dXJuIHRoaXMuZmluaXNoVG9rZW4oX3Rva2VudHlwZS50eXBlcy50ZW1wbGF0ZSwgb3V0KTtcbiAgICB9XG4gICAgaWYgKGNoID09PSA5Mikge1xuICAgICAgLy8gJ1xcJ1xuICAgICAgb3V0ICs9IHRoaXMuaW5wdXQuc2xpY2UoY2h1bmtTdGFydCwgdGhpcy5wb3MpO1xuICAgICAgb3V0ICs9IHRoaXMucmVhZEVzY2FwZWRDaGFyKHRydWUpO1xuICAgICAgY2h1bmtTdGFydCA9IHRoaXMucG9zO1xuICAgIH0gZWxzZSBpZiAoX3doaXRlc3BhY2UuaXNOZXdMaW5lKGNoKSkge1xuICAgICAgb3V0ICs9IHRoaXMuaW5wdXQuc2xpY2UoY2h1bmtTdGFydCwgdGhpcy5wb3MpO1xuICAgICAgKyt0aGlzLnBvcztcbiAgICAgIHN3aXRjaCAoY2gpIHtcbiAgICAgICAgY2FzZSAxMzpcbiAgICAgICAgICBpZiAodGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zKSA9PT0gMTApICsrdGhpcy5wb3M7XG4gICAgICAgIGNhc2UgMTA6XG4gICAgICAgICAgb3V0ICs9IFwiXFxuXCI7XG4gICAgICAgICAgYnJlYWs7XG4gICAgICAgIGRlZmF1bHQ6XG4gICAgICAgICAgb3V0ICs9IFN0cmluZy5mcm9tQ2hhckNvZGUoY2gpO1xuICAgICAgICAgIGJyZWFrO1xuICAgICAgfVxuICAgICAgaWYgKHRoaXMub3B0aW9ucy5sb2NhdGlvbnMpIHtcbiAgICAgICAgKyt0aGlzLmN1ckxpbmU7XG4gICAgICAgIHRoaXMubGluZVN0YXJ0ID0gdGhpcy5wb3M7XG4gICAgICB9XG4gICAgICBjaHVua1N0YXJ0ID0gdGhpcy5wb3M7XG4gICAgfSBlbHNlIHtcbiAgICAgICsrdGhpcy5wb3M7XG4gICAgfVxuICB9XG59O1xuXG4vLyBVc2VkIHRvIHJlYWQgZXNjYXBlZCBjaGFyYWN0ZXJzXG5cbnBwLnJlYWRFc2NhcGVkQ2hhciA9IGZ1bmN0aW9uIChpblRlbXBsYXRlKSB7XG4gIHZhciBjaCA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCgrK3RoaXMucG9zKTtcbiAgKyt0aGlzLnBvcztcbiAgc3dpdGNoIChjaCkge1xuICAgIGNhc2UgMTEwOlxuICAgICAgcmV0dXJuIFwiXFxuXCI7IC8vICduJyAtPiAnXFxuJ1xuICAgIGNhc2UgMTE0OlxuICAgICAgcmV0dXJuIFwiXFxyXCI7IC8vICdyJyAtPiAnXFxyJ1xuICAgIGNhc2UgMTIwOlxuICAgICAgcmV0dXJuIFN0cmluZy5mcm9tQ2hhckNvZGUodGhpcy5yZWFkSGV4Q2hhcigyKSk7IC8vICd4J1xuICAgIGNhc2UgMTE3OlxuICAgICAgcmV0dXJuIGNvZGVQb2ludFRvU3RyaW5nKHRoaXMucmVhZENvZGVQb2ludCgpKTsgLy8gJ3UnXG4gICAgY2FzZSAxMTY6XG4gICAgICByZXR1cm4gXCJcXHRcIjsgLy8gJ3QnIC0+ICdcXHQnXG4gICAgY2FzZSA5ODpcbiAgICAgIHJldHVybiBcIlxcYlwiOyAvLyAnYicgLT4gJ1xcYidcbiAgICBjYXNlIDExODpcbiAgICAgIHJldHVybiBcIlxcdTAwMGJcIjsgLy8gJ3YnIC0+ICdcXHUwMDBiJ1xuICAgIGNhc2UgMTAyOlxuICAgICAgcmV0dXJuIFwiXFxmXCI7IC8vICdmJyAtPiAnXFxmJ1xuICAgIGNhc2UgMTM6XG4gICAgICBpZiAodGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zKSA9PT0gMTApICsrdGhpcy5wb3M7IC8vICdcXHJcXG4nXG4gICAgY2FzZSAxMDpcbiAgICAgIC8vICcgXFxuJ1xuICAgICAgaWYgKHRoaXMub3B0aW9ucy5sb2NhdGlvbnMpIHtcbiAgICAgICAgdGhpcy5saW5lU3RhcnQgPSB0aGlzLnBvczsrK3RoaXMuY3VyTGluZTtcbiAgICAgIH1cbiAgICAgIHJldHVybiBcIlwiO1xuICAgIGRlZmF1bHQ6XG4gICAgICBpZiAoY2ggPj0gNDggJiYgY2ggPD0gNTUpIHtcbiAgICAgICAgdmFyIG9jdGFsU3RyID0gdGhpcy5pbnB1dC5zdWJzdHIodGhpcy5wb3MgLSAxLCAzKS5tYXRjaCgvXlswLTddKy8pWzBdO1xuICAgICAgICB2YXIgb2N0YWwgPSBwYXJzZUludChvY3RhbFN0ciwgOCk7XG4gICAgICAgIGlmIChvY3RhbCA+IDI1NSkge1xuICAgICAgICAgIG9jdGFsU3RyID0gb2N0YWxTdHIuc2xpY2UoMCwgLTEpO1xuICAgICAgICAgIG9jdGFsID0gcGFyc2VJbnQob2N0YWxTdHIsIDgpO1xuICAgICAgICB9XG4gICAgICAgIGlmIChvY3RhbCA+IDAgJiYgKHRoaXMuc3RyaWN0IHx8IGluVGVtcGxhdGUpKSB7XG4gICAgICAgICAgdGhpcy5yYWlzZSh0aGlzLnBvcyAtIDIsIFwiT2N0YWwgbGl0ZXJhbCBpbiBzdHJpY3QgbW9kZVwiKTtcbiAgICAgICAgfVxuICAgICAgICB0aGlzLnBvcyArPSBvY3RhbFN0ci5sZW5ndGggLSAxO1xuICAgICAgICByZXR1cm4gU3RyaW5nLmZyb21DaGFyQ29kZShvY3RhbCk7XG4gICAgICB9XG4gICAgICByZXR1cm4gU3RyaW5nLmZyb21DaGFyQ29kZShjaCk7XG4gIH1cbn07XG5cbi8vIFVzZWQgdG8gcmVhZCBjaGFyYWN0ZXIgZXNjYXBlIHNlcXVlbmNlcyAoJ1xceCcsICdcXHUnLCAnXFxVJykuXG5cbnBwLnJlYWRIZXhDaGFyID0gZnVuY3Rpb24gKGxlbikge1xuICB2YXIgY29kZVBvcyA9IHRoaXMucG9zO1xuICB2YXIgbiA9IHRoaXMucmVhZEludCgxNiwgbGVuKTtcbiAgaWYgKG4gPT09IG51bGwpIHRoaXMucmFpc2UoY29kZVBvcywgXCJCYWQgY2hhcmFjdGVyIGVzY2FwZSBzZXF1ZW5jZVwiKTtcbiAgcmV0dXJuIG47XG59O1xuXG4vLyBSZWFkIGFuIGlkZW50aWZpZXIsIGFuZCByZXR1cm4gaXQgYXMgYSBzdHJpbmcuIFNldHMgYHRoaXMuY29udGFpbnNFc2NgXG4vLyB0byB3aGV0aGVyIHRoZSB3b3JkIGNvbnRhaW5lZCBhICdcXHUnIGVzY2FwZS5cbi8vXG4vLyBJbmNyZW1lbnRhbGx5IGFkZHMgb25seSBlc2NhcGVkIGNoYXJzLCBhZGRpbmcgb3RoZXIgY2h1bmtzIGFzLWlzXG4vLyBhcyBhIG1pY3JvLW9wdGltaXphdGlvbi5cblxucHAucmVhZFdvcmQxID0gZnVuY3Rpb24gKCkge1xuICB0aGlzLmNvbnRhaW5zRXNjID0gZmFsc2U7XG4gIHZhciB3b3JkID0gXCJcIixcbiAgICAgIGZpcnN0ID0gdHJ1ZSxcbiAgICAgIGNodW5rU3RhcnQgPSB0aGlzLnBvcztcbiAgdmFyIGFzdHJhbCA9IHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2O1xuICB3aGlsZSAodGhpcy5wb3MgPCB0aGlzLmlucHV0Lmxlbmd0aCkge1xuICAgIHZhciBjaCA9IHRoaXMuZnVsbENoYXJDb2RlQXRQb3MoKTtcbiAgICBpZiAoX2lkZW50aWZpZXIuaXNJZGVudGlmaWVyQ2hhcihjaCwgYXN0cmFsKSkge1xuICAgICAgdGhpcy5wb3MgKz0gY2ggPD0gMHhmZmZmID8gMSA6IDI7XG4gICAgfSBlbHNlIGlmIChjaCA9PT0gOTIpIHtcbiAgICAgIC8vIFwiXFxcIlxuICAgICAgdGhpcy5jb250YWluc0VzYyA9IHRydWU7XG4gICAgICB3b3JkICs9IHRoaXMuaW5wdXQuc2xpY2UoY2h1bmtTdGFydCwgdGhpcy5wb3MpO1xuICAgICAgdmFyIGVzY1N0YXJ0ID0gdGhpcy5wb3M7XG4gICAgICBpZiAodGhpcy5pbnB1dC5jaGFyQ29kZUF0KCsrdGhpcy5wb3MpICE9IDExNykgLy8gXCJ1XCJcbiAgICAgICAgdGhpcy5yYWlzZSh0aGlzLnBvcywgXCJFeHBlY3RpbmcgVW5pY29kZSBlc2NhcGUgc2VxdWVuY2UgXFxcXHVYWFhYXCIpO1xuICAgICAgKyt0aGlzLnBvcztcbiAgICAgIHZhciBlc2MgPSB0aGlzLnJlYWRDb2RlUG9pbnQoKTtcbiAgICAgIGlmICghKGZpcnN0ID8gX2lkZW50aWZpZXIuaXNJZGVudGlmaWVyU3RhcnQgOiBfaWRlbnRpZmllci5pc0lkZW50aWZpZXJDaGFyKShlc2MsIGFzdHJhbCkpIHRoaXMucmFpc2UoZXNjU3RhcnQsIFwiSW52YWxpZCBVbmljb2RlIGVzY2FwZVwiKTtcbiAgICAgIHdvcmQgKz0gY29kZVBvaW50VG9TdHJpbmcoZXNjKTtcbiAgICAgIGNodW5rU3RhcnQgPSB0aGlzLnBvcztcbiAgICB9IGVsc2Uge1xuICAgICAgYnJlYWs7XG4gICAgfVxuICAgIGZpcnN0ID0gZmFsc2U7XG4gIH1cbiAgcmV0dXJuIHdvcmQgKyB0aGlzLmlucHV0LnNsaWNlKGNodW5rU3RhcnQsIHRoaXMucG9zKTtcbn07XG5cbi8vIFJlYWQgYW4gaWRlbnRpZmllciBvciBrZXl3b3JkIHRva2VuLiBXaWxsIGNoZWNrIGZvciByZXNlcnZlZFxuLy8gd29yZHMgd2hlbiBuZWNlc3NhcnkuXG5cbnBwLnJlYWRXb3JkID0gZnVuY3Rpb24gKCkge1xuICB2YXIgd29yZCA9IHRoaXMucmVhZFdvcmQxKCk7XG4gIHZhciB0eXBlID0gX3Rva2VudHlwZS50eXBlcy5uYW1lO1xuICBpZiAoKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2IHx8ICF0aGlzLmNvbnRhaW5zRXNjKSAmJiB0aGlzLmlzS2V5d29yZCh3b3JkKSkgdHlwZSA9IF90b2tlbnR5cGUua2V5d29yZHNbd29yZF07XG4gIHJldHVybiB0aGlzLmZpbmlzaFRva2VuKHR5cGUsIHdvcmQpO1xufTtcblxufSx7XCIuL2lkZW50aWZpZXJcIjoyLFwiLi9sb2N1dGlsXCI6NSxcIi4vc3RhdGVcIjoxMCxcIi4vdG9rZW50eXBlXCI6MTQsXCIuL3doaXRlc3BhY2VcIjoxNn1dLDE0OltmdW5jdGlvbihfZGVyZXFfLG1vZHVsZSxleHBvcnRzKXtcbi8vICMjIFRva2VuIHR5cGVzXG5cbi8vIFRoZSBhc3NpZ25tZW50IG9mIGZpbmUtZ3JhaW5lZCwgaW5mb3JtYXRpb24tY2FycnlpbmcgdHlwZSBvYmplY3RzXG4vLyBhbGxvd3MgdGhlIHRva2VuaXplciB0byBzdG9yZSB0aGUgaW5mb3JtYXRpb24gaXQgaGFzIGFib3V0IGFcbi8vIHRva2VuIGluIGEgd2F5IHRoYXQgaXMgdmVyeSBjaGVhcCBmb3IgdGhlIHBhcnNlciB0byBsb29rIHVwLlxuXG4vLyBBbGwgdG9rZW4gdHlwZSB2YXJpYWJsZXMgc3RhcnQgd2l0aCBhbiB1bmRlcnNjb3JlLCB0byBtYWtlIHRoZW1cbi8vIGVhc3kgdG8gcmVjb2duaXplLlxuXG4vLyBUaGUgYGJlZm9yZUV4cHJgIHByb3BlcnR5IGlzIHVzZWQgdG8gZGlzYW1iaWd1YXRlIGJldHdlZW4gcmVndWxhclxuLy8gZXhwcmVzc2lvbnMgYW5kIGRpdmlzaW9ucy4gSXQgaXMgc2V0IG9uIGFsbCB0b2tlbiB0eXBlcyB0aGF0IGNhblxuLy8gYmUgZm9sbG93ZWQgYnkgYW4gZXhwcmVzc2lvbiAodGh1cywgYSBzbGFzaCBhZnRlciB0aGVtIHdvdWxkIGJlIGFcbi8vIHJlZ3VsYXIgZXhwcmVzc2lvbikuXG4vL1xuLy8gYGlzTG9vcGAgbWFya3MgYSBrZXl3b3JkIGFzIHN0YXJ0aW5nIGEgbG9vcCwgd2hpY2ggaXMgaW1wb3J0YW50XG4vLyB0byBrbm93IHdoZW4gcGFyc2luZyBhIGxhYmVsLCBpbiBvcmRlciB0byBhbGxvdyBvciBkaXNhbGxvd1xuLy8gY29udGludWUganVtcHMgdG8gdGhhdCBsYWJlbC5cblxuXCJ1c2Ugc3RyaWN0XCI7XG5cbmV4cG9ydHMuX19lc01vZHVsZSA9IHRydWU7XG5cbmZ1bmN0aW9uIF9jbGFzc0NhbGxDaGVjayhpbnN0YW5jZSwgQ29uc3RydWN0b3IpIHsgaWYgKCEoaW5zdGFuY2UgaW5zdGFuY2VvZiBDb25zdHJ1Y3RvcikpIHsgdGhyb3cgbmV3IFR5cGVFcnJvcihcIkNhbm5vdCBjYWxsIGEgY2xhc3MgYXMgYSBmdW5jdGlvblwiKTsgfSB9XG5cbnZhciBUb2tlblR5cGUgPSBmdW5jdGlvbiBUb2tlblR5cGUobGFiZWwpIHtcbiAgdmFyIGNvbmYgPSBhcmd1bWVudHMubGVuZ3RoIDw9IDEgfHwgYXJndW1lbnRzWzFdID09PSB1bmRlZmluZWQgPyB7fSA6IGFyZ3VtZW50c1sxXTtcblxuICBfY2xhc3NDYWxsQ2hlY2sodGhpcywgVG9rZW5UeXBlKTtcblxuICB0aGlzLmxhYmVsID0gbGFiZWw7XG4gIHRoaXMua2V5d29yZCA9IGNvbmYua2V5d29yZDtcbiAgdGhpcy5iZWZvcmVFeHByID0gISFjb25mLmJlZm9yZUV4cHI7XG4gIHRoaXMuc3RhcnRzRXhwciA9ICEhY29uZi5zdGFydHNFeHByO1xuICB0aGlzLmlzTG9vcCA9ICEhY29uZi5pc0xvb3A7XG4gIHRoaXMuaXNBc3NpZ24gPSAhIWNvbmYuaXNBc3NpZ247XG4gIHRoaXMucHJlZml4ID0gISFjb25mLnByZWZpeDtcbiAgdGhpcy5wb3N0Zml4ID0gISFjb25mLnBvc3RmaXg7XG4gIHRoaXMuYmlub3AgPSBjb25mLmJpbm9wIHx8IG51bGw7XG4gIHRoaXMudXBkYXRlQ29udGV4dCA9IG51bGw7XG59O1xuXG5leHBvcnRzLlRva2VuVHlwZSA9IFRva2VuVHlwZTtcblxuZnVuY3Rpb24gYmlub3AobmFtZSwgcHJlYykge1xuICByZXR1cm4gbmV3IFRva2VuVHlwZShuYW1lLCB7IGJlZm9yZUV4cHI6IHRydWUsIGJpbm9wOiBwcmVjIH0pO1xufVxudmFyIGJlZm9yZUV4cHIgPSB7IGJlZm9yZUV4cHI6IHRydWUgfSxcbiAgICBzdGFydHNFeHByID0geyBzdGFydHNFeHByOiB0cnVlIH07XG5cbnZhciB0eXBlcyA9IHtcbiAgbnVtOiBuZXcgVG9rZW5UeXBlKFwibnVtXCIsIHN0YXJ0c0V4cHIpLFxuICByZWdleHA6IG5ldyBUb2tlblR5cGUoXCJyZWdleHBcIiwgc3RhcnRzRXhwciksXG4gIHN0cmluZzogbmV3IFRva2VuVHlwZShcInN0cmluZ1wiLCBzdGFydHNFeHByKSxcbiAgbmFtZTogbmV3IFRva2VuVHlwZShcIm5hbWVcIiwgc3RhcnRzRXhwciksXG4gIGVvZjogbmV3IFRva2VuVHlwZShcImVvZlwiKSxcblxuICAvLyBQdW5jdHVhdGlvbiB0b2tlbiB0eXBlcy5cbiAgYnJhY2tldEw6IG5ldyBUb2tlblR5cGUoXCJbXCIsIHsgYmVmb3JlRXhwcjogdHJ1ZSwgc3RhcnRzRXhwcjogdHJ1ZSB9KSxcbiAgYnJhY2tldFI6IG5ldyBUb2tlblR5cGUoXCJdXCIpLFxuICBicmFjZUw6IG5ldyBUb2tlblR5cGUoXCJ7XCIsIHsgYmVmb3JlRXhwcjogdHJ1ZSwgc3RhcnRzRXhwcjogdHJ1ZSB9KSxcbiAgYnJhY2VSOiBuZXcgVG9rZW5UeXBlKFwifVwiKSxcbiAgcGFyZW5MOiBuZXcgVG9rZW5UeXBlKFwiKFwiLCB7IGJlZm9yZUV4cHI6IHRydWUsIHN0YXJ0c0V4cHI6IHRydWUgfSksXG4gIHBhcmVuUjogbmV3IFRva2VuVHlwZShcIilcIiksXG4gIGNvbW1hOiBuZXcgVG9rZW5UeXBlKFwiLFwiLCBiZWZvcmVFeHByKSxcbiAgc2VtaTogbmV3IFRva2VuVHlwZShcIjtcIiwgYmVmb3JlRXhwciksXG4gIGNvbG9uOiBuZXcgVG9rZW5UeXBlKFwiOlwiLCBiZWZvcmVFeHByKSxcbiAgZG90OiBuZXcgVG9rZW5UeXBlKFwiLlwiKSxcbiAgcXVlc3Rpb246IG5ldyBUb2tlblR5cGUoXCI/XCIsIGJlZm9yZUV4cHIpLFxuICBhcnJvdzogbmV3IFRva2VuVHlwZShcIj0+XCIsIGJlZm9yZUV4cHIpLFxuICB0ZW1wbGF0ZTogbmV3IFRva2VuVHlwZShcInRlbXBsYXRlXCIpLFxuICBlbGxpcHNpczogbmV3IFRva2VuVHlwZShcIi4uLlwiLCBiZWZvcmVFeHByKSxcbiAgYmFja1F1b3RlOiBuZXcgVG9rZW5UeXBlKFwiYFwiLCBzdGFydHNFeHByKSxcbiAgZG9sbGFyQnJhY2VMOiBuZXcgVG9rZW5UeXBlKFwiJHtcIiwgeyBiZWZvcmVFeHByOiB0cnVlLCBzdGFydHNFeHByOiB0cnVlIH0pLFxuXG4gIC8vIE9wZXJhdG9ycy4gVGhlc2UgY2Fycnkgc2V2ZXJhbCBraW5kcyBvZiBwcm9wZXJ0aWVzIHRvIGhlbHAgdGhlXG4gIC8vIHBhcnNlciB1c2UgdGhlbSBwcm9wZXJseSAodGhlIHByZXNlbmNlIG9mIHRoZXNlIHByb3BlcnRpZXMgaXNcbiAgLy8gd2hhdCBjYXRlZ29yaXplcyB0aGVtIGFzIG9wZXJhdG9ycykuXG4gIC8vXG4gIC8vIGBiaW5vcGAsIHdoZW4gcHJlc2VudCwgc3BlY2lmaWVzIHRoYXQgdGhpcyBvcGVyYXRvciBpcyBhIGJpbmFyeVxuICAvLyBvcGVyYXRvciwgYW5kIHdpbGwgcmVmZXIgdG8gaXRzIHByZWNlZGVuY2UuXG4gIC8vXG4gIC8vIGBwcmVmaXhgIGFuZCBgcG9zdGZpeGAgbWFyayB0aGUgb3BlcmF0b3IgYXMgYSBwcmVmaXggb3IgcG9zdGZpeFxuICAvLyB1bmFyeSBvcGVyYXRvci5cbiAgLy9cbiAgLy8gYGlzQXNzaWduYCBtYXJrcyBhbGwgb2YgYD1gLCBgKz1gLCBgLT1gIGV0Y2V0ZXJhLCB3aGljaCBhY3QgYXNcbiAgLy8gYmluYXJ5IG9wZXJhdG9ycyB3aXRoIGEgdmVyeSBsb3cgcHJlY2VkZW5jZSwgdGhhdCBzaG91bGQgcmVzdWx0XG4gIC8vIGluIEFzc2lnbm1lbnRFeHByZXNzaW9uIG5vZGVzLlxuXG4gIGVxOiBuZXcgVG9rZW5UeXBlKFwiPVwiLCB7IGJlZm9yZUV4cHI6IHRydWUsIGlzQXNzaWduOiB0cnVlIH0pLFxuICBhc3NpZ246IG5ldyBUb2tlblR5cGUoXCJfPVwiLCB7IGJlZm9yZUV4cHI6IHRydWUsIGlzQXNzaWduOiB0cnVlIH0pLFxuICBpbmNEZWM6IG5ldyBUb2tlblR5cGUoXCIrKy8tLVwiLCB7IHByZWZpeDogdHJ1ZSwgcG9zdGZpeDogdHJ1ZSwgc3RhcnRzRXhwcjogdHJ1ZSB9KSxcbiAgcHJlZml4OiBuZXcgVG9rZW5UeXBlKFwicHJlZml4XCIsIHsgYmVmb3JlRXhwcjogdHJ1ZSwgcHJlZml4OiB0cnVlLCBzdGFydHNFeHByOiB0cnVlIH0pLFxuICBsb2dpY2FsT1I6IGJpbm9wKFwifHxcIiwgMSksXG4gIGxvZ2ljYWxBTkQ6IGJpbm9wKFwiJiZcIiwgMiksXG4gIGJpdHdpc2VPUjogYmlub3AoXCJ8XCIsIDMpLFxuICBiaXR3aXNlWE9SOiBiaW5vcChcIl5cIiwgNCksXG4gIGJpdHdpc2VBTkQ6IGJpbm9wKFwiJlwiLCA1KSxcbiAgZXF1YWxpdHk6IGJpbm9wKFwiPT0vIT1cIiwgNiksXG4gIHJlbGF0aW9uYWw6IGJpbm9wKFwiPC8+XCIsIDcpLFxuICBiaXRTaGlmdDogYmlub3AoXCI8PC8+PlwiLCA4KSxcbiAgcGx1c01pbjogbmV3IFRva2VuVHlwZShcIisvLVwiLCB7IGJlZm9yZUV4cHI6IHRydWUsIGJpbm9wOiA5LCBwcmVmaXg6IHRydWUsIHN0YXJ0c0V4cHI6IHRydWUgfSksXG4gIG1vZHVsbzogYmlub3AoXCIlXCIsIDEwKSxcbiAgc3RhcjogYmlub3AoXCIqXCIsIDEwKSxcbiAgc2xhc2g6IGJpbm9wKFwiL1wiLCAxMClcbn07XG5cbmV4cG9ydHMudHlwZXMgPSB0eXBlcztcbi8vIE1hcCBrZXl3b3JkIG5hbWVzIHRvIHRva2VuIHR5cGVzLlxuXG52YXIga2V5d29yZHMgPSB7fTtcblxuZXhwb3J0cy5rZXl3b3JkcyA9IGtleXdvcmRzO1xuLy8gU3VjY2luY3QgZGVmaW5pdGlvbnMgb2Yga2V5d29yZCB0b2tlbiB0eXBlc1xuZnVuY3Rpb24ga3cobmFtZSkge1xuICB2YXIgb3B0aW9ucyA9IGFyZ3VtZW50cy5sZW5ndGggPD0gMSB8fCBhcmd1bWVudHNbMV0gPT09IHVuZGVmaW5lZCA/IHt9IDogYXJndW1lbnRzWzFdO1xuXG4gIG9wdGlvbnMua2V5d29yZCA9IG5hbWU7XG4gIGtleXdvcmRzW25hbWVdID0gdHlwZXNbXCJfXCIgKyBuYW1lXSA9IG5ldyBUb2tlblR5cGUobmFtZSwgb3B0aW9ucyk7XG59XG5cbmt3KFwiYnJlYWtcIik7XG5rdyhcImNhc2VcIiwgYmVmb3JlRXhwcik7XG5rdyhcImNhdGNoXCIpO1xua3coXCJjb250aW51ZVwiKTtcbmt3KFwiZGVidWdnZXJcIik7XG5rdyhcImRlZmF1bHRcIiwgYmVmb3JlRXhwcik7XG5rdyhcImRvXCIsIHsgaXNMb29wOiB0cnVlIH0pO1xua3coXCJlbHNlXCIsIGJlZm9yZUV4cHIpO1xua3coXCJmaW5hbGx5XCIpO1xua3coXCJmb3JcIiwgeyBpc0xvb3A6IHRydWUgfSk7XG5rdyhcImZ1bmN0aW9uXCIsIHN0YXJ0c0V4cHIpO1xua3coXCJpZlwiKTtcbmt3KFwicmV0dXJuXCIsIGJlZm9yZUV4cHIpO1xua3coXCJzd2l0Y2hcIik7XG5rdyhcInRocm93XCIsIGJlZm9yZUV4cHIpO1xua3coXCJ0cnlcIik7XG5rdyhcInZhclwiKTtcbmt3KFwibGV0XCIpO1xua3coXCJjb25zdFwiKTtcbmt3KFwid2hpbGVcIiwgeyBpc0xvb3A6IHRydWUgfSk7XG5rdyhcIndpdGhcIik7XG5rdyhcIm5ld1wiLCB7IGJlZm9yZUV4cHI6IHRydWUsIHN0YXJ0c0V4cHI6IHRydWUgfSk7XG5rdyhcInRoaXNcIiwgc3RhcnRzRXhwcik7XG5rdyhcInN1cGVyXCIsIHN0YXJ0c0V4cHIpO1xua3coXCJjbGFzc1wiKTtcbmt3KFwiZXh0ZW5kc1wiLCBiZWZvcmVFeHByKTtcbmt3KFwiZXhwb3J0XCIpO1xua3coXCJpbXBvcnRcIik7XG5rdyhcInlpZWxkXCIsIHsgYmVmb3JlRXhwcjogdHJ1ZSwgc3RhcnRzRXhwcjogdHJ1ZSB9KTtcbmt3KFwibnVsbFwiLCBzdGFydHNFeHByKTtcbmt3KFwidHJ1ZVwiLCBzdGFydHNFeHByKTtcbmt3KFwiZmFsc2VcIiwgc3RhcnRzRXhwcik7XG5rdyhcImluXCIsIHsgYmVmb3JlRXhwcjogdHJ1ZSwgYmlub3A6IDcgfSk7XG5rdyhcImluc3RhbmNlb2ZcIiwgeyBiZWZvcmVFeHByOiB0cnVlLCBiaW5vcDogNyB9KTtcbmt3KFwidHlwZW9mXCIsIHsgYmVmb3JlRXhwcjogdHJ1ZSwgcHJlZml4OiB0cnVlLCBzdGFydHNFeHByOiB0cnVlIH0pO1xua3coXCJ2b2lkXCIsIHsgYmVmb3JlRXhwcjogdHJ1ZSwgcHJlZml4OiB0cnVlLCBzdGFydHNFeHByOiB0cnVlIH0pO1xua3coXCJkZWxldGVcIiwgeyBiZWZvcmVFeHByOiB0cnVlLCBwcmVmaXg6IHRydWUsIHN0YXJ0c0V4cHI6IHRydWUgfSk7XG5cbn0se31dLDE1OltmdW5jdGlvbihfZGVyZXFfLG1vZHVsZSxleHBvcnRzKXtcblwidXNlIHN0cmljdFwiO1xuXG5leHBvcnRzLl9fZXNNb2R1bGUgPSB0cnVlO1xuZXhwb3J0cy5pc0FycmF5ID0gaXNBcnJheTtcbmV4cG9ydHMuaGFzID0gaGFzO1xuXG5mdW5jdGlvbiBpc0FycmF5KG9iaikge1xuICByZXR1cm4gT2JqZWN0LnByb3RvdHlwZS50b1N0cmluZy5jYWxsKG9iaikgPT09IFwiW29iamVjdCBBcnJheV1cIjtcbn1cblxuLy8gQ2hlY2tzIGlmIGFuIG9iamVjdCBoYXMgYSBwcm9wZXJ0eS5cblxuZnVuY3Rpb24gaGFzKG9iaiwgcHJvcE5hbWUpIHtcbiAgcmV0dXJuIE9iamVjdC5wcm90b3R5cGUuaGFzT3duUHJvcGVydHkuY2FsbChvYmosIHByb3BOYW1lKTtcbn1cblxufSx7fV0sMTY6W2Z1bmN0aW9uKF9kZXJlcV8sbW9kdWxlLGV4cG9ydHMpe1xuLy8gTWF0Y2hlcyBhIHdob2xlIGxpbmUgYnJlYWsgKHdoZXJlIENSTEYgaXMgY29uc2lkZXJlZCBhIHNpbmdsZVxuLy8gbGluZSBicmVhaykuIFVzZWQgdG8gY291bnQgbGluZXMuXG5cblwidXNlIHN0cmljdFwiO1xuXG5leHBvcnRzLl9fZXNNb2R1bGUgPSB0cnVlO1xuZXhwb3J0cy5pc05ld0xpbmUgPSBpc05ld0xpbmU7XG52YXIgbGluZUJyZWFrID0gL1xcclxcbj98XFxufFxcdTIwMjh8XFx1MjAyOS87XG5leHBvcnRzLmxpbmVCcmVhayA9IGxpbmVCcmVhaztcbnZhciBsaW5lQnJlYWtHID0gbmV3IFJlZ0V4cChsaW5lQnJlYWsuc291cmNlLCBcImdcIik7XG5cbmV4cG9ydHMubGluZUJyZWFrRyA9IGxpbmVCcmVha0c7XG5cbmZ1bmN0aW9uIGlzTmV3TGluZShjb2RlKSB7XG4gIHJldHVybiBjb2RlID09PSAxMCB8fCBjb2RlID09PSAxMyB8fCBjb2RlID09PSAweDIwMjggfHwgY29kZSA9PSAweDIwMjk7XG59XG5cbnZhciBub25BU0NJSXdoaXRlc3BhY2UgPSAvW1xcdTE2ODBcXHUxODBlXFx1MjAwMC1cXHUyMDBhXFx1MjAyZlxcdTIwNWZcXHUzMDAwXFx1ZmVmZl0vO1xuZXhwb3J0cy5ub25BU0NJSXdoaXRlc3BhY2UgPSBub25BU0NJSXdoaXRlc3BhY2U7XG5cbn0se31dfSx7fSxbM10pKDMpXG59KTsiLCIoZnVuY3Rpb24oZil7aWYodHlwZW9mIGV4cG9ydHM9PT1cIm9iamVjdFwiJiZ0eXBlb2YgbW9kdWxlIT09XCJ1bmRlZmluZWRcIil7bW9kdWxlLmV4cG9ydHM9ZigpfWVsc2UgaWYodHlwZW9mIGRlZmluZT09PVwiZnVuY3Rpb25cIiYmZGVmaW5lLmFtZCl7ZGVmaW5lKFtdLGYpfWVsc2V7dmFyIGc7aWYodHlwZW9mIHdpbmRvdyE9PVwidW5kZWZpbmVkXCIpe2c9d2luZG93fWVsc2UgaWYodHlwZW9mIGdsb2JhbCE9PVwidW5kZWZpbmVkXCIpe2c9Z2xvYmFsfWVsc2UgaWYodHlwZW9mIHNlbGYhPT1cInVuZGVmaW5lZFwiKXtnPXNlbGZ9ZWxzZXtnPXRoaXN9KGcuYWNvcm4gfHwgKGcuYWNvcm4gPSB7fSkpLmxvb3NlID0gZigpfX0pKGZ1bmN0aW9uKCl7dmFyIGRlZmluZSxtb2R1bGUsZXhwb3J0cztyZXR1cm4gKGZ1bmN0aW9uIGUodCxuLHIpe2Z1bmN0aW9uIHMobyx1KXtpZighbltvXSl7aWYoIXRbb10pe3ZhciBhPXR5cGVvZiByZXF1aXJlPT1cImZ1bmN0aW9uXCImJnJlcXVpcmU7aWYoIXUmJmEpcmV0dXJuIGEobywhMCk7aWYoaSlyZXR1cm4gaShvLCEwKTt2YXIgZj1uZXcgRXJyb3IoXCJDYW5ub3QgZmluZCBtb2R1bGUgJ1wiK28rXCInXCIpO3Rocm93IGYuY29kZT1cIk1PRFVMRV9OT1RfRk9VTkRcIixmfXZhciBsPW5bb109e2V4cG9ydHM6e319O3Rbb11bMF0uY2FsbChsLmV4cG9ydHMsZnVuY3Rpb24oZSl7dmFyIG49dFtvXVsxXVtlXTtyZXR1cm4gcyhuP246ZSl9LGwsbC5leHBvcnRzLGUsdCxuLHIpfXJldHVybiBuW29dLmV4cG9ydHN9dmFyIGk9dHlwZW9mIHJlcXVpcmU9PVwiZnVuY3Rpb25cIiYmcmVxdWlyZTtmb3IodmFyIG89MDtvPHIubGVuZ3RoO28rKylzKHJbb10pO3JldHVybiBzfSkoezE6W2Z1bmN0aW9uKF9kZXJlcV8sbW9kdWxlLGV4cG9ydHMpe1xuXCJ1c2Ugc3RyaWN0XCI7XG5cbm1vZHVsZS5leHBvcnRzID0gdHlwZW9mIGFjb3JuICE9ICd1bmRlZmluZWQnID8gYWNvcm4gOiByZXF1aXJlKFwiLi9hY29yblwiKTtcblxufSx7fV0sMjpbZnVuY3Rpb24oX2RlcmVxXyxtb2R1bGUsZXhwb3J0cyl7XG5cInVzZSBzdHJpY3RcIjtcblxudmFyIF9zdGF0ZSA9IF9kZXJlcV8oXCIuL3N0YXRlXCIpO1xuXG52YXIgX3BhcnNldXRpbCA9IF9kZXJlcV8oXCIuL3BhcnNldXRpbFwiKTtcblxudmFyIF8gPSBfZGVyZXFfKFwiLi5cIik7XG5cbnZhciBscCA9IF9zdGF0ZS5Mb29zZVBhcnNlci5wcm90b3R5cGU7XG5cbmxwLmNoZWNrTFZhbCA9IGZ1bmN0aW9uIChleHByLCBiaW5kaW5nKSB7XG4gIGlmICghZXhwcikgcmV0dXJuIGV4cHI7XG4gIHN3aXRjaCAoZXhwci50eXBlKSB7XG4gICAgY2FzZSBcIklkZW50aWZpZXJcIjpcbiAgICAgIHJldHVybiBleHByO1xuXG4gICAgY2FzZSBcIk1lbWJlckV4cHJlc3Npb25cIjpcbiAgICAgIHJldHVybiBiaW5kaW5nID8gdGhpcy5kdW1teUlkZW50KCkgOiBleHByO1xuXG4gICAgY2FzZSBcIlBhcmVudGhlc2l6ZWRFeHByZXNzaW9uXCI6XG4gICAgICBleHByLmV4cHJlc3Npb24gPSB0aGlzLmNoZWNrTFZhbChleHByLmV4cHJlc3Npb24sIGJpbmRpbmcpO1xuICAgICAgcmV0dXJuIGV4cHI7XG5cbiAgICAvLyBGSVhNRSByZWN1cnNpdmVseSBjaGVjayBjb250ZW50c1xuICAgIGNhc2UgXCJPYmplY3RQYXR0ZXJuXCI6XG4gICAgY2FzZSBcIkFycmF5UGF0dGVyblwiOlxuICAgIGNhc2UgXCJSZXN0RWxlbWVudFwiOlxuICAgIGNhc2UgXCJBc3NpZ25tZW50UGF0dGVyblwiOlxuICAgICAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KSByZXR1cm4gZXhwcjtcblxuICAgIGRlZmF1bHQ6XG4gICAgICByZXR1cm4gdGhpcy5kdW1teUlkZW50KCk7XG4gIH1cbn07XG5cbmxwLnBhcnNlRXhwcmVzc2lvbiA9IGZ1bmN0aW9uIChub0luKSB7XG4gIHZhciBzdGFydCA9IHRoaXMuc3RvcmVDdXJyZW50UG9zKCk7XG4gIHZhciBleHByID0gdGhpcy5wYXJzZU1heWJlQXNzaWduKG5vSW4pO1xuICBpZiAodGhpcy50b2sudHlwZSA9PT0gXy50b2tUeXBlcy5jb21tYSkge1xuICAgIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGVBdChzdGFydCk7XG4gICAgbm9kZS5leHByZXNzaW9ucyA9IFtleHByXTtcbiAgICB3aGlsZSAodGhpcy5lYXQoXy50b2tUeXBlcy5jb21tYSkpIG5vZGUuZXhwcmVzc2lvbnMucHVzaCh0aGlzLnBhcnNlTWF5YmVBc3NpZ24obm9JbikpO1xuICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJTZXF1ZW5jZUV4cHJlc3Npb25cIik7XG4gIH1cbiAgcmV0dXJuIGV4cHI7XG59O1xuXG5scC5wYXJzZVBhcmVuRXhwcmVzc2lvbiA9IGZ1bmN0aW9uICgpIHtcbiAgdGhpcy5wdXNoQ3goKTtcbiAgdGhpcy5leHBlY3QoXy50b2tUeXBlcy5wYXJlbkwpO1xuICB2YXIgdmFsID0gdGhpcy5wYXJzZUV4cHJlc3Npb24oKTtcbiAgdGhpcy5wb3BDeCgpO1xuICB0aGlzLmV4cGVjdChfLnRva1R5cGVzLnBhcmVuUik7XG4gIHJldHVybiB2YWw7XG59O1xuXG5scC5wYXJzZU1heWJlQXNzaWduID0gZnVuY3Rpb24gKG5vSW4pIHtcbiAgdmFyIHN0YXJ0ID0gdGhpcy5zdG9yZUN1cnJlbnRQb3MoKTtcbiAgdmFyIGxlZnQgPSB0aGlzLnBhcnNlTWF5YmVDb25kaXRpb25hbChub0luKTtcbiAgaWYgKHRoaXMudG9rLnR5cGUuaXNBc3NpZ24pIHtcbiAgICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlQXQoc3RhcnQpO1xuICAgIG5vZGUub3BlcmF0b3IgPSB0aGlzLnRvay52YWx1ZTtcbiAgICBub2RlLmxlZnQgPSB0aGlzLnRvay50eXBlID09PSBfLnRva1R5cGVzLmVxID8gdGhpcy50b0Fzc2lnbmFibGUobGVmdCkgOiB0aGlzLmNoZWNrTFZhbChsZWZ0KTtcbiAgICB0aGlzLm5leHQoKTtcbiAgICBub2RlLnJpZ2h0ID0gdGhpcy5wYXJzZU1heWJlQXNzaWduKG5vSW4pO1xuICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJBc3NpZ25tZW50RXhwcmVzc2lvblwiKTtcbiAgfVxuICByZXR1cm4gbGVmdDtcbn07XG5cbmxwLnBhcnNlTWF5YmVDb25kaXRpb25hbCA9IGZ1bmN0aW9uIChub0luKSB7XG4gIHZhciBzdGFydCA9IHRoaXMuc3RvcmVDdXJyZW50UG9zKCk7XG4gIHZhciBleHByID0gdGhpcy5wYXJzZUV4cHJPcHMobm9Jbik7XG4gIGlmICh0aGlzLmVhdChfLnRva1R5cGVzLnF1ZXN0aW9uKSkge1xuICAgIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGVBdChzdGFydCk7XG4gICAgbm9kZS50ZXN0ID0gZXhwcjtcbiAgICBub2RlLmNvbnNlcXVlbnQgPSB0aGlzLnBhcnNlTWF5YmVBc3NpZ24oKTtcbiAgICBub2RlLmFsdGVybmF0ZSA9IHRoaXMuZXhwZWN0KF8udG9rVHlwZXMuY29sb24pID8gdGhpcy5wYXJzZU1heWJlQXNzaWduKG5vSW4pIDogdGhpcy5kdW1teUlkZW50KCk7XG4gICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkNvbmRpdGlvbmFsRXhwcmVzc2lvblwiKTtcbiAgfVxuICByZXR1cm4gZXhwcjtcbn07XG5cbmxwLnBhcnNlRXhwck9wcyA9IGZ1bmN0aW9uIChub0luKSB7XG4gIHZhciBzdGFydCA9IHRoaXMuc3RvcmVDdXJyZW50UG9zKCk7XG4gIHZhciBpbmRlbnQgPSB0aGlzLmN1ckluZGVudCxcbiAgICAgIGxpbmUgPSB0aGlzLmN1ckxpbmVTdGFydDtcbiAgcmV0dXJuIHRoaXMucGFyc2VFeHByT3AodGhpcy5wYXJzZU1heWJlVW5hcnkobm9JbiksIHN0YXJ0LCAtMSwgbm9JbiwgaW5kZW50LCBsaW5lKTtcbn07XG5cbmxwLnBhcnNlRXhwck9wID0gZnVuY3Rpb24gKGxlZnQsIHN0YXJ0LCBtaW5QcmVjLCBub0luLCBpbmRlbnQsIGxpbmUpIHtcbiAgaWYgKHRoaXMuY3VyTGluZVN0YXJ0ICE9IGxpbmUgJiYgdGhpcy5jdXJJbmRlbnQgPCBpbmRlbnQgJiYgdGhpcy50b2tlblN0YXJ0c0xpbmUoKSkgcmV0dXJuIGxlZnQ7XG4gIHZhciBwcmVjID0gdGhpcy50b2sudHlwZS5iaW5vcDtcbiAgaWYgKHByZWMgIT0gbnVsbCAmJiAoIW5vSW4gfHwgdGhpcy50b2sudHlwZSAhPT0gXy50b2tUeXBlcy5faW4pKSB7XG4gICAgaWYgKHByZWMgPiBtaW5QcmVjKSB7XG4gICAgICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlQXQoc3RhcnQpO1xuICAgICAgbm9kZS5sZWZ0ID0gbGVmdDtcbiAgICAgIG5vZGUub3BlcmF0b3IgPSB0aGlzLnRvay52YWx1ZTtcbiAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgaWYgKHRoaXMuY3VyTGluZVN0YXJ0ICE9IGxpbmUgJiYgdGhpcy5jdXJJbmRlbnQgPCBpbmRlbnQgJiYgdGhpcy50b2tlblN0YXJ0c0xpbmUoKSkge1xuICAgICAgICBub2RlLnJpZ2h0ID0gdGhpcy5kdW1teUlkZW50KCk7XG4gICAgICB9IGVsc2Uge1xuICAgICAgICB2YXIgcmlnaHRTdGFydCA9IHRoaXMuc3RvcmVDdXJyZW50UG9zKCk7XG4gICAgICAgIG5vZGUucmlnaHQgPSB0aGlzLnBhcnNlRXhwck9wKHRoaXMucGFyc2VNYXliZVVuYXJ5KG5vSW4pLCByaWdodFN0YXJ0LCBwcmVjLCBub0luLCBpbmRlbnQsIGxpbmUpO1xuICAgICAgfVxuICAgICAgdGhpcy5maW5pc2hOb2RlKG5vZGUsIC8mJnxcXHxcXHwvLnRlc3Qobm9kZS5vcGVyYXRvcikgPyBcIkxvZ2ljYWxFeHByZXNzaW9uXCIgOiBcIkJpbmFyeUV4cHJlc3Npb25cIik7XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZUV4cHJPcChub2RlLCBzdGFydCwgbWluUHJlYywgbm9JbiwgaW5kZW50LCBsaW5lKTtcbiAgICB9XG4gIH1cbiAgcmV0dXJuIGxlZnQ7XG59O1xuXG5scC5wYXJzZU1heWJlVW5hcnkgPSBmdW5jdGlvbiAobm9Jbikge1xuICBpZiAodGhpcy50b2sudHlwZS5wcmVmaXgpIHtcbiAgICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCksXG4gICAgICAgIHVwZGF0ZSA9IHRoaXMudG9rLnR5cGUgPT09IF8udG9rVHlwZXMuaW5jRGVjO1xuICAgIG5vZGUub3BlcmF0b3IgPSB0aGlzLnRvay52YWx1ZTtcbiAgICBub2RlLnByZWZpeCA9IHRydWU7XG4gICAgdGhpcy5uZXh0KCk7XG4gICAgbm9kZS5hcmd1bWVudCA9IHRoaXMucGFyc2VNYXliZVVuYXJ5KG5vSW4pO1xuICAgIGlmICh1cGRhdGUpIG5vZGUuYXJndW1lbnQgPSB0aGlzLmNoZWNrTFZhbChub2RlLmFyZ3VtZW50KTtcbiAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIHVwZGF0ZSA/IFwiVXBkYXRlRXhwcmVzc2lvblwiIDogXCJVbmFyeUV4cHJlc3Npb25cIik7XG4gIH0gZWxzZSBpZiAodGhpcy50b2sudHlwZSA9PT0gXy50b2tUeXBlcy5lbGxpcHNpcykge1xuICAgIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgICB0aGlzLm5leHQoKTtcbiAgICBub2RlLmFyZ3VtZW50ID0gdGhpcy5wYXJzZU1heWJlVW5hcnkobm9Jbik7XG4gICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIlNwcmVhZEVsZW1lbnRcIik7XG4gIH1cbiAgdmFyIHN0YXJ0ID0gdGhpcy5zdG9yZUN1cnJlbnRQb3MoKTtcbiAgdmFyIGV4cHIgPSB0aGlzLnBhcnNlRXhwclN1YnNjcmlwdHMoKTtcbiAgd2hpbGUgKHRoaXMudG9rLnR5cGUucG9zdGZpeCAmJiAhdGhpcy5jYW5JbnNlcnRTZW1pY29sb24oKSkge1xuICAgIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGVBdChzdGFydCk7XG4gICAgbm9kZS5vcGVyYXRvciA9IHRoaXMudG9rLnZhbHVlO1xuICAgIG5vZGUucHJlZml4ID0gZmFsc2U7XG4gICAgbm9kZS5hcmd1bWVudCA9IHRoaXMuY2hlY2tMVmFsKGV4cHIpO1xuICAgIHRoaXMubmV4dCgpO1xuICAgIGV4cHIgPSB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJVcGRhdGVFeHByZXNzaW9uXCIpO1xuICB9XG4gIHJldHVybiBleHByO1xufTtcblxubHAucGFyc2VFeHByU3Vic2NyaXB0cyA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIHN0YXJ0ID0gdGhpcy5zdG9yZUN1cnJlbnRQb3MoKTtcbiAgcmV0dXJuIHRoaXMucGFyc2VTdWJzY3JpcHRzKHRoaXMucGFyc2VFeHByQXRvbSgpLCBzdGFydCwgZmFsc2UsIHRoaXMuY3VySW5kZW50LCB0aGlzLmN1ckxpbmVTdGFydCk7XG59O1xuXG5scC5wYXJzZVN1YnNjcmlwdHMgPSBmdW5jdGlvbiAoYmFzZSwgc3RhcnQsIG5vQ2FsbHMsIHN0YXJ0SW5kZW50LCBsaW5lKSB7XG4gIGZvciAoOzspIHtcbiAgICBpZiAodGhpcy5jdXJMaW5lU3RhcnQgIT0gbGluZSAmJiB0aGlzLmN1ckluZGVudCA8PSBzdGFydEluZGVudCAmJiB0aGlzLnRva2VuU3RhcnRzTGluZSgpKSB7XG4gICAgICBpZiAodGhpcy50b2sudHlwZSA9PSBfLnRva1R5cGVzLmRvdCAmJiB0aGlzLmN1ckluZGVudCA9PSBzdGFydEluZGVudCkgLS1zdGFydEluZGVudDtlbHNlIHJldHVybiBiYXNlO1xuICAgIH1cblxuICAgIGlmICh0aGlzLmVhdChfLnRva1R5cGVzLmRvdCkpIHtcbiAgICAgIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGVBdChzdGFydCk7XG4gICAgICBub2RlLm9iamVjdCA9IGJhc2U7XG4gICAgICBpZiAodGhpcy5jdXJMaW5lU3RhcnQgIT0gbGluZSAmJiB0aGlzLmN1ckluZGVudCA8PSBzdGFydEluZGVudCAmJiB0aGlzLnRva2VuU3RhcnRzTGluZSgpKSBub2RlLnByb3BlcnR5ID0gdGhpcy5kdW1teUlkZW50KCk7ZWxzZSBub2RlLnByb3BlcnR5ID0gdGhpcy5wYXJzZVByb3BlcnR5QWNjZXNzb3IoKSB8fCB0aGlzLmR1bW15SWRlbnQoKTtcbiAgICAgIG5vZGUuY29tcHV0ZWQgPSBmYWxzZTtcbiAgICAgIGJhc2UgPSB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJNZW1iZXJFeHByZXNzaW9uXCIpO1xuICAgIH0gZWxzZSBpZiAodGhpcy50b2sudHlwZSA9PSBfLnRva1R5cGVzLmJyYWNrZXRMKSB7XG4gICAgICB0aGlzLnB1c2hDeCgpO1xuICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlQXQoc3RhcnQpO1xuICAgICAgbm9kZS5vYmplY3QgPSBiYXNlO1xuICAgICAgbm9kZS5wcm9wZXJ0eSA9IHRoaXMucGFyc2VFeHByZXNzaW9uKCk7XG4gICAgICBub2RlLmNvbXB1dGVkID0gdHJ1ZTtcbiAgICAgIHRoaXMucG9wQ3goKTtcbiAgICAgIHRoaXMuZXhwZWN0KF8udG9rVHlwZXMuYnJhY2tldFIpO1xuICAgICAgYmFzZSA9IHRoaXMuZmluaXNoTm9kZShub2RlLCBcIk1lbWJlckV4cHJlc3Npb25cIik7XG4gICAgfSBlbHNlIGlmICghbm9DYWxscyAmJiB0aGlzLnRvay50eXBlID09IF8udG9rVHlwZXMucGFyZW5MKSB7XG4gICAgICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlQXQoc3RhcnQpO1xuICAgICAgbm9kZS5jYWxsZWUgPSBiYXNlO1xuICAgICAgbm9kZS5hcmd1bWVudHMgPSB0aGlzLnBhcnNlRXhwckxpc3QoXy50b2tUeXBlcy5wYXJlblIpO1xuICAgICAgYmFzZSA9IHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkNhbGxFeHByZXNzaW9uXCIpO1xuICAgIH0gZWxzZSBpZiAodGhpcy50b2sudHlwZSA9PSBfLnRva1R5cGVzLmJhY2tRdW90ZSkge1xuICAgICAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0KTtcbiAgICAgIG5vZGUudGFnID0gYmFzZTtcbiAgICAgIG5vZGUucXVhc2kgPSB0aGlzLnBhcnNlVGVtcGxhdGUoKTtcbiAgICAgIGJhc2UgPSB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJUYWdnZWRUZW1wbGF0ZUV4cHJlc3Npb25cIik7XG4gICAgfSBlbHNlIHtcbiAgICAgIHJldHVybiBiYXNlO1xuICAgIH1cbiAgfVxufTtcblxubHAucGFyc2VFeHByQXRvbSA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIG5vZGUgPSB1bmRlZmluZWQ7XG4gIHN3aXRjaCAodGhpcy50b2sudHlwZSkge1xuICAgIGNhc2UgXy50b2tUeXBlcy5fdGhpczpcbiAgICBjYXNlIF8udG9rVHlwZXMuX3N1cGVyOlxuICAgICAgdmFyIHR5cGUgPSB0aGlzLnRvay50eXBlID09PSBfLnRva1R5cGVzLl90aGlzID8gXCJUaGlzRXhwcmVzc2lvblwiIDogXCJTdXBlclwiO1xuICAgICAgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gICAgICB0aGlzLm5leHQoKTtcbiAgICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgdHlwZSk7XG5cbiAgICBjYXNlIF8udG9rVHlwZXMubmFtZTpcbiAgICAgIHZhciBzdGFydCA9IHRoaXMuc3RvcmVDdXJyZW50UG9zKCk7XG4gICAgICB2YXIgaWQgPSB0aGlzLnBhcnNlSWRlbnQoKTtcbiAgICAgIHJldHVybiB0aGlzLmVhdChfLnRva1R5cGVzLmFycm93KSA/IHRoaXMucGFyc2VBcnJvd0V4cHJlc3Npb24odGhpcy5zdGFydE5vZGVBdChzdGFydCksIFtpZF0pIDogaWQ7XG5cbiAgICBjYXNlIF8udG9rVHlwZXMucmVnZXhwOlxuICAgICAgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gICAgICB2YXIgdmFsID0gdGhpcy50b2sudmFsdWU7XG4gICAgICBub2RlLnJlZ2V4ID0geyBwYXR0ZXJuOiB2YWwucGF0dGVybiwgZmxhZ3M6IHZhbC5mbGFncyB9O1xuICAgICAgbm9kZS52YWx1ZSA9IHZhbC52YWx1ZTtcbiAgICAgIG5vZGUucmF3ID0gdGhpcy5pbnB1dC5zbGljZSh0aGlzLnRvay5zdGFydCwgdGhpcy50b2suZW5kKTtcbiAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkxpdGVyYWxcIik7XG5cbiAgICBjYXNlIF8udG9rVHlwZXMubnVtOmNhc2UgXy50b2tUeXBlcy5zdHJpbmc6XG4gICAgICBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgICAgIG5vZGUudmFsdWUgPSB0aGlzLnRvay52YWx1ZTtcbiAgICAgIG5vZGUucmF3ID0gdGhpcy5pbnB1dC5zbGljZSh0aGlzLnRvay5zdGFydCwgdGhpcy50b2suZW5kKTtcbiAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkxpdGVyYWxcIik7XG5cbiAgICBjYXNlIF8udG9rVHlwZXMuX251bGw6Y2FzZSBfLnRva1R5cGVzLl90cnVlOmNhc2UgXy50b2tUeXBlcy5fZmFsc2U6XG4gICAgICBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgICAgIG5vZGUudmFsdWUgPSB0aGlzLnRvay50eXBlID09PSBfLnRva1R5cGVzLl9udWxsID8gbnVsbCA6IHRoaXMudG9rLnR5cGUgPT09IF8udG9rVHlwZXMuX3RydWU7XG4gICAgICBub2RlLnJhdyA9IHRoaXMudG9rLnR5cGUua2V5d29yZDtcbiAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkxpdGVyYWxcIik7XG5cbiAgICBjYXNlIF8udG9rVHlwZXMucGFyZW5MOlxuICAgICAgdmFyIHBhcmVuU3RhcnQgPSB0aGlzLnN0b3JlQ3VycmVudFBvcygpO1xuICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICB2YXIgaW5uZXIgPSB0aGlzLnBhcnNlRXhwcmVzc2lvbigpO1xuICAgICAgdGhpcy5leHBlY3QoXy50b2tUeXBlcy5wYXJlblIpO1xuICAgICAgaWYgKHRoaXMuZWF0KF8udG9rVHlwZXMuYXJyb3cpKSB7XG4gICAgICAgIHJldHVybiB0aGlzLnBhcnNlQXJyb3dFeHByZXNzaW9uKHRoaXMuc3RhcnROb2RlQXQocGFyZW5TdGFydCksIGlubmVyLmV4cHJlc3Npb25zIHx8IChfcGFyc2V1dGlsLmlzRHVtbXkoaW5uZXIpID8gW10gOiBbaW5uZXJdKSk7XG4gICAgICB9XG4gICAgICBpZiAodGhpcy5vcHRpb25zLnByZXNlcnZlUGFyZW5zKSB7XG4gICAgICAgIHZhciBwYXIgPSB0aGlzLnN0YXJ0Tm9kZUF0KHBhcmVuU3RhcnQpO1xuICAgICAgICBwYXIuZXhwcmVzc2lvbiA9IGlubmVyO1xuICAgICAgICBpbm5lciA9IHRoaXMuZmluaXNoTm9kZShwYXIsIFwiUGFyZW50aGVzaXplZEV4cHJlc3Npb25cIik7XG4gICAgICB9XG4gICAgICByZXR1cm4gaW5uZXI7XG5cbiAgICBjYXNlIF8udG9rVHlwZXMuYnJhY2tldEw6XG4gICAgICBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgICAgIG5vZGUuZWxlbWVudHMgPSB0aGlzLnBhcnNlRXhwckxpc3QoXy50b2tUeXBlcy5icmFja2V0UiwgdHJ1ZSk7XG4gICAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiQXJyYXlFeHByZXNzaW9uXCIpO1xuXG4gICAgY2FzZSBfLnRva1R5cGVzLmJyYWNlTDpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlT2JqKCk7XG5cbiAgICBjYXNlIF8udG9rVHlwZXMuX2NsYXNzOlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VDbGFzcygpO1xuXG4gICAgY2FzZSBfLnRva1R5cGVzLl9mdW5jdGlvbjpcbiAgICAgIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZUZ1bmN0aW9uKG5vZGUsIGZhbHNlKTtcblxuICAgIGNhc2UgXy50b2tUeXBlcy5fbmV3OlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VOZXcoKTtcblxuICAgIGNhc2UgXy50b2tUeXBlcy5feWllbGQ6XG4gICAgICBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgaWYgKHRoaXMuc2VtaWNvbG9uKCkgfHwgdGhpcy5jYW5JbnNlcnRTZW1pY29sb24oKSB8fCB0aGlzLnRvay50eXBlICE9IF8udG9rVHlwZXMuc3RhciAmJiAhdGhpcy50b2sudHlwZS5zdGFydHNFeHByKSB7XG4gICAgICAgIG5vZGUuZGVsZWdhdGUgPSBmYWxzZTtcbiAgICAgICAgbm9kZS5hcmd1bWVudCA9IG51bGw7XG4gICAgICB9IGVsc2Uge1xuICAgICAgICBub2RlLmRlbGVnYXRlID0gdGhpcy5lYXQoXy50b2tUeXBlcy5zdGFyKTtcbiAgICAgICAgbm9kZS5hcmd1bWVudCA9IHRoaXMucGFyc2VNYXliZUFzc2lnbigpO1xuICAgICAgfVxuICAgICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIllpZWxkRXhwcmVzc2lvblwiKTtcblxuICAgIGNhc2UgXy50b2tUeXBlcy5iYWNrUXVvdGU6XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZVRlbXBsYXRlKCk7XG5cbiAgICBkZWZhdWx0OlxuICAgICAgcmV0dXJuIHRoaXMuZHVtbXlJZGVudCgpO1xuICB9XG59O1xuXG5scC5wYXJzZU5ldyA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpLFxuICAgICAgc3RhcnRJbmRlbnQgPSB0aGlzLmN1ckluZGVudCxcbiAgICAgIGxpbmUgPSB0aGlzLmN1ckxpbmVTdGFydDtcbiAgdmFyIG1ldGEgPSB0aGlzLnBhcnNlSWRlbnQodHJ1ZSk7XG4gIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNiAmJiB0aGlzLmVhdChfLnRva1R5cGVzLmRvdCkpIHtcbiAgICBub2RlLm1ldGEgPSBtZXRhO1xuICAgIG5vZGUucHJvcGVydHkgPSB0aGlzLnBhcnNlSWRlbnQodHJ1ZSk7XG4gICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIk1ldGFQcm9wZXJ0eVwiKTtcbiAgfVxuICB2YXIgc3RhcnQgPSB0aGlzLnN0b3JlQ3VycmVudFBvcygpO1xuICBub2RlLmNhbGxlZSA9IHRoaXMucGFyc2VTdWJzY3JpcHRzKHRoaXMucGFyc2VFeHByQXRvbSgpLCBzdGFydCwgdHJ1ZSwgc3RhcnRJbmRlbnQsIGxpbmUpO1xuICBpZiAodGhpcy50b2sudHlwZSA9PSBfLnRva1R5cGVzLnBhcmVuTCkge1xuICAgIG5vZGUuYXJndW1lbnRzID0gdGhpcy5wYXJzZUV4cHJMaXN0KF8udG9rVHlwZXMucGFyZW5SKTtcbiAgfSBlbHNlIHtcbiAgICBub2RlLmFyZ3VtZW50cyA9IFtdO1xuICB9XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJOZXdFeHByZXNzaW9uXCIpO1xufTtcblxubHAucGFyc2VUZW1wbGF0ZUVsZW1lbnQgPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBlbGVtID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgZWxlbS52YWx1ZSA9IHtcbiAgICByYXc6IHRoaXMuaW5wdXQuc2xpY2UodGhpcy50b2suc3RhcnQsIHRoaXMudG9rLmVuZCkucmVwbGFjZSgvXFxyXFxuPy9nLCBcIlxcblwiKSxcbiAgICBjb29rZWQ6IHRoaXMudG9rLnZhbHVlXG4gIH07XG4gIHRoaXMubmV4dCgpO1xuICBlbGVtLnRhaWwgPSB0aGlzLnRvay50eXBlID09PSBfLnRva1R5cGVzLmJhY2tRdW90ZTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShlbGVtLCBcIlRlbXBsYXRlRWxlbWVudFwiKTtcbn07XG5cbmxwLnBhcnNlVGVtcGxhdGUgPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgdGhpcy5uZXh0KCk7XG4gIG5vZGUuZXhwcmVzc2lvbnMgPSBbXTtcbiAgdmFyIGN1ckVsdCA9IHRoaXMucGFyc2VUZW1wbGF0ZUVsZW1lbnQoKTtcbiAgbm9kZS5xdWFzaXMgPSBbY3VyRWx0XTtcbiAgd2hpbGUgKCFjdXJFbHQudGFpbCkge1xuICAgIHRoaXMubmV4dCgpO1xuICAgIG5vZGUuZXhwcmVzc2lvbnMucHVzaCh0aGlzLnBhcnNlRXhwcmVzc2lvbigpKTtcbiAgICBpZiAodGhpcy5leHBlY3QoXy50b2tUeXBlcy5icmFjZVIpKSB7XG4gICAgICBjdXJFbHQgPSB0aGlzLnBhcnNlVGVtcGxhdGVFbGVtZW50KCk7XG4gICAgfSBlbHNlIHtcbiAgICAgIGN1ckVsdCA9IHRoaXMuc3RhcnROb2RlKCk7XG4gICAgICBjdXJFbHQudmFsdWUgPSB7IGNvb2tlZDogXCJcIiwgcmF3OiBcIlwiIH07XG4gICAgICBjdXJFbHQudGFpbCA9IHRydWU7XG4gICAgfVxuICAgIG5vZGUucXVhc2lzLnB1c2goY3VyRWx0KTtcbiAgfVxuICB0aGlzLmV4cGVjdChfLnRva1R5cGVzLmJhY2tRdW90ZSk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJUZW1wbGF0ZUxpdGVyYWxcIik7XG59O1xuXG5scC5wYXJzZU9iaiA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICBub2RlLnByb3BlcnRpZXMgPSBbXTtcbiAgdGhpcy5wdXNoQ3goKTtcbiAgdmFyIGluZGVudCA9IHRoaXMuY3VySW5kZW50ICsgMSxcbiAgICAgIGxpbmUgPSB0aGlzLmN1ckxpbmVTdGFydDtcbiAgdGhpcy5lYXQoXy50b2tUeXBlcy5icmFjZUwpO1xuICBpZiAodGhpcy5jdXJJbmRlbnQgKyAxIDwgaW5kZW50KSB7XG4gICAgaW5kZW50ID0gdGhpcy5jdXJJbmRlbnQ7bGluZSA9IHRoaXMuY3VyTGluZVN0YXJ0O1xuICB9XG4gIHdoaWxlICghdGhpcy5jbG9zZXMoXy50b2tUeXBlcy5icmFjZVIsIGluZGVudCwgbGluZSkpIHtcbiAgICB2YXIgcHJvcCA9IHRoaXMuc3RhcnROb2RlKCksXG4gICAgICAgIGlzR2VuZXJhdG9yID0gdW5kZWZpbmVkLFxuICAgICAgICBzdGFydCA9IHVuZGVmaW5lZDtcbiAgICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYpIHtcbiAgICAgIHN0YXJ0ID0gdGhpcy5zdG9yZUN1cnJlbnRQb3MoKTtcbiAgICAgIHByb3AubWV0aG9kID0gZmFsc2U7XG4gICAgICBwcm9wLnNob3J0aGFuZCA9IGZhbHNlO1xuICAgICAgaXNHZW5lcmF0b3IgPSB0aGlzLmVhdChfLnRva1R5cGVzLnN0YXIpO1xuICAgIH1cbiAgICB0aGlzLnBhcnNlUHJvcGVydHlOYW1lKHByb3ApO1xuICAgIGlmIChfcGFyc2V1dGlsLmlzRHVtbXkocHJvcC5rZXkpKSB7XG4gICAgICBpZiAoX3BhcnNldXRpbC5pc0R1bW15KHRoaXMucGFyc2VNYXliZUFzc2lnbigpKSkgdGhpcy5uZXh0KCk7dGhpcy5lYXQoXy50b2tUeXBlcy5jb21tYSk7Y29udGludWU7XG4gICAgfVxuICAgIGlmICh0aGlzLmVhdChfLnRva1R5cGVzLmNvbG9uKSkge1xuICAgICAgcHJvcC5raW5kID0gXCJpbml0XCI7XG4gICAgICBwcm9wLnZhbHVlID0gdGhpcy5wYXJzZU1heWJlQXNzaWduKCk7XG4gICAgfSBlbHNlIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNiAmJiAodGhpcy50b2sudHlwZSA9PT0gXy50b2tUeXBlcy5wYXJlbkwgfHwgdGhpcy50b2sudHlwZSA9PT0gXy50b2tUeXBlcy5icmFjZUwpKSB7XG4gICAgICBwcm9wLmtpbmQgPSBcImluaXRcIjtcbiAgICAgIHByb3AubWV0aG9kID0gdHJ1ZTtcbiAgICAgIHByb3AudmFsdWUgPSB0aGlzLnBhcnNlTWV0aG9kKGlzR2VuZXJhdG9yKTtcbiAgICB9IGVsc2UgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA1ICYmIHByb3Aua2V5LnR5cGUgPT09IFwiSWRlbnRpZmllclwiICYmICFwcm9wLmNvbXB1dGVkICYmIChwcm9wLmtleS5uYW1lID09PSBcImdldFwiIHx8IHByb3Aua2V5Lm5hbWUgPT09IFwic2V0XCIpICYmICh0aGlzLnRvay50eXBlICE9IF8udG9rVHlwZXMuY29tbWEgJiYgdGhpcy50b2sudHlwZSAhPSBfLnRva1R5cGVzLmJyYWNlUikpIHtcbiAgICAgIHByb3Aua2luZCA9IHByb3Aua2V5Lm5hbWU7XG4gICAgICB0aGlzLnBhcnNlUHJvcGVydHlOYW1lKHByb3ApO1xuICAgICAgcHJvcC52YWx1ZSA9IHRoaXMucGFyc2VNZXRob2QoZmFsc2UpO1xuICAgIH0gZWxzZSB7XG4gICAgICBwcm9wLmtpbmQgPSBcImluaXRcIjtcbiAgICAgIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNikge1xuICAgICAgICBpZiAodGhpcy5lYXQoXy50b2tUeXBlcy5lcSkpIHtcbiAgICAgICAgICB2YXIgYXNzaWduID0gdGhpcy5zdGFydE5vZGVBdChzdGFydCk7XG4gICAgICAgICAgYXNzaWduLm9wZXJhdG9yID0gXCI9XCI7XG4gICAgICAgICAgYXNzaWduLmxlZnQgPSBwcm9wLmtleTtcbiAgICAgICAgICBhc3NpZ24ucmlnaHQgPSB0aGlzLnBhcnNlTWF5YmVBc3NpZ24oKTtcbiAgICAgICAgICBwcm9wLnZhbHVlID0gdGhpcy5maW5pc2hOb2RlKGFzc2lnbiwgXCJBc3NpZ25tZW50RXhwcmVzc2lvblwiKTtcbiAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICBwcm9wLnZhbHVlID0gcHJvcC5rZXk7XG4gICAgICAgIH1cbiAgICAgIH0gZWxzZSB7XG4gICAgICAgIHByb3AudmFsdWUgPSB0aGlzLmR1bW15SWRlbnQoKTtcbiAgICAgIH1cbiAgICAgIHByb3Auc2hvcnRoYW5kID0gdHJ1ZTtcbiAgICB9XG4gICAgbm9kZS5wcm9wZXJ0aWVzLnB1c2godGhpcy5maW5pc2hOb2RlKHByb3AsIFwiUHJvcGVydHlcIikpO1xuICAgIHRoaXMuZWF0KF8udG9rVHlwZXMuY29tbWEpO1xuICB9XG4gIHRoaXMucG9wQ3goKTtcbiAgaWYgKCF0aGlzLmVhdChfLnRva1R5cGVzLmJyYWNlUikpIHtcbiAgICAvLyBJZiB0aGVyZSBpcyBubyBjbG9zaW5nIGJyYWNlLCBtYWtlIHRoZSBub2RlIHNwYW4gdG8gdGhlIHN0YXJ0XG4gICAgLy8gb2YgdGhlIG5leHQgdG9rZW4gKHRoaXMgaXMgdXNlZnVsIGZvciBUZXJuKVxuICAgIHRoaXMubGFzdC5lbmQgPSB0aGlzLnRvay5zdGFydDtcbiAgICBpZiAodGhpcy5vcHRpb25zLmxvY2F0aW9ucykgdGhpcy5sYXN0LmxvYy5lbmQgPSB0aGlzLnRvay5sb2Muc3RhcnQ7XG4gIH1cbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIk9iamVjdEV4cHJlc3Npb25cIik7XG59O1xuXG5scC5wYXJzZVByb3BlcnR5TmFtZSA9IGZ1bmN0aW9uIChwcm9wKSB7XG4gIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNikge1xuICAgIGlmICh0aGlzLmVhdChfLnRva1R5cGVzLmJyYWNrZXRMKSkge1xuICAgICAgcHJvcC5jb21wdXRlZCA9IHRydWU7XG4gICAgICBwcm9wLmtleSA9IHRoaXMucGFyc2VFeHByZXNzaW9uKCk7XG4gICAgICB0aGlzLmV4cGVjdChfLnRva1R5cGVzLmJyYWNrZXRSKTtcbiAgICAgIHJldHVybjtcbiAgICB9IGVsc2Uge1xuICAgICAgcHJvcC5jb21wdXRlZCA9IGZhbHNlO1xuICAgIH1cbiAgfVxuICB2YXIga2V5ID0gdGhpcy50b2sudHlwZSA9PT0gXy50b2tUeXBlcy5udW0gfHwgdGhpcy50b2sudHlwZSA9PT0gXy50b2tUeXBlcy5zdHJpbmcgPyB0aGlzLnBhcnNlRXhwckF0b20oKSA6IHRoaXMucGFyc2VJZGVudCgpO1xuICBwcm9wLmtleSA9IGtleSB8fCB0aGlzLmR1bW15SWRlbnQoKTtcbn07XG5cbmxwLnBhcnNlUHJvcGVydHlBY2Nlc3NvciA9IGZ1bmN0aW9uICgpIHtcbiAgaWYgKHRoaXMudG9rLnR5cGUgPT09IF8udG9rVHlwZXMubmFtZSB8fCB0aGlzLnRvay50eXBlLmtleXdvcmQpIHJldHVybiB0aGlzLnBhcnNlSWRlbnQoKTtcbn07XG5cbmxwLnBhcnNlSWRlbnQgPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBuYW1lID0gdGhpcy50b2sudHlwZSA9PT0gXy50b2tUeXBlcy5uYW1lID8gdGhpcy50b2sudmFsdWUgOiB0aGlzLnRvay50eXBlLmtleXdvcmQ7XG4gIGlmICghbmFtZSkgcmV0dXJuIHRoaXMuZHVtbXlJZGVudCgpO1xuICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gIHRoaXMubmV4dCgpO1xuICBub2RlLm5hbWUgPSBuYW1lO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiSWRlbnRpZmllclwiKTtcbn07XG5cbmxwLmluaXRGdW5jdGlvbiA9IGZ1bmN0aW9uIChub2RlKSB7XG4gIG5vZGUuaWQgPSBudWxsO1xuICBub2RlLnBhcmFtcyA9IFtdO1xuICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYpIHtcbiAgICBub2RlLmdlbmVyYXRvciA9IGZhbHNlO1xuICAgIG5vZGUuZXhwcmVzc2lvbiA9IGZhbHNlO1xuICB9XG59O1xuXG4vLyBDb252ZXJ0IGV4aXN0aW5nIGV4cHJlc3Npb24gYXRvbSB0byBhc3NpZ25hYmxlIHBhdHRlcm5cbi8vIGlmIHBvc3NpYmxlLlxuXG5scC50b0Fzc2lnbmFibGUgPSBmdW5jdGlvbiAobm9kZSwgYmluZGluZykge1xuICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYgJiYgbm9kZSkge1xuICAgIHN3aXRjaCAobm9kZS50eXBlKSB7XG4gICAgICBjYXNlIFwiT2JqZWN0RXhwcmVzc2lvblwiOlxuICAgICAgICBub2RlLnR5cGUgPSBcIk9iamVjdFBhdHRlcm5cIjtcbiAgICAgICAgdmFyIHByb3BzID0gbm9kZS5wcm9wZXJ0aWVzO1xuICAgICAgICBmb3IgKHZhciBpID0gMDsgaSA8IHByb3BzLmxlbmd0aDsgaSsrKSB7XG4gICAgICAgICAgdGhpcy50b0Fzc2lnbmFibGUocHJvcHNbaV0udmFsdWUsIGJpbmRpbmcpO1xuICAgICAgICB9YnJlYWs7XG5cbiAgICAgIGNhc2UgXCJBcnJheUV4cHJlc3Npb25cIjpcbiAgICAgICAgbm9kZS50eXBlID0gXCJBcnJheVBhdHRlcm5cIjtcbiAgICAgICAgdGhpcy50b0Fzc2lnbmFibGVMaXN0KG5vZGUuZWxlbWVudHMsIGJpbmRpbmcpO1xuICAgICAgICBicmVhaztcblxuICAgICAgY2FzZSBcIlNwcmVhZEVsZW1lbnRcIjpcbiAgICAgICAgbm9kZS50eXBlID0gXCJSZXN0RWxlbWVudFwiO1xuICAgICAgICBub2RlLmFyZ3VtZW50ID0gdGhpcy50b0Fzc2lnbmFibGUobm9kZS5hcmd1bWVudCwgYmluZGluZyk7XG4gICAgICAgIGJyZWFrO1xuXG4gICAgICBjYXNlIFwiQXNzaWdubWVudEV4cHJlc3Npb25cIjpcbiAgICAgICAgbm9kZS50eXBlID0gXCJBc3NpZ25tZW50UGF0dGVyblwiO1xuICAgICAgICBkZWxldGUgbm9kZS5vcGVyYXRvcjtcbiAgICAgICAgYnJlYWs7XG4gICAgfVxuICB9XG4gIHJldHVybiB0aGlzLmNoZWNrTFZhbChub2RlLCBiaW5kaW5nKTtcbn07XG5cbmxwLnRvQXNzaWduYWJsZUxpc3QgPSBmdW5jdGlvbiAoZXhwckxpc3QsIGJpbmRpbmcpIHtcbiAgZm9yICh2YXIgaSA9IDA7IGkgPCBleHByTGlzdC5sZW5ndGg7IGkrKykge1xuICAgIGV4cHJMaXN0W2ldID0gdGhpcy50b0Fzc2lnbmFibGUoZXhwckxpc3RbaV0sIGJpbmRpbmcpO1xuICB9cmV0dXJuIGV4cHJMaXN0O1xufTtcblxubHAucGFyc2VGdW5jdGlvblBhcmFtcyA9IGZ1bmN0aW9uIChwYXJhbXMpIHtcbiAgcGFyYW1zID0gdGhpcy5wYXJzZUV4cHJMaXN0KF8udG9rVHlwZXMucGFyZW5SKTtcbiAgcmV0dXJuIHRoaXMudG9Bc3NpZ25hYmxlTGlzdChwYXJhbXMsIHRydWUpO1xufTtcblxubHAucGFyc2VNZXRob2QgPSBmdW5jdGlvbiAoaXNHZW5lcmF0b3IpIHtcbiAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICB0aGlzLmluaXRGdW5jdGlvbihub2RlKTtcbiAgbm9kZS5wYXJhbXMgPSB0aGlzLnBhcnNlRnVuY3Rpb25QYXJhbXMoKTtcbiAgbm9kZS5nZW5lcmF0b3IgPSBpc0dlbmVyYXRvciB8fCBmYWxzZTtcbiAgbm9kZS5leHByZXNzaW9uID0gdGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYgJiYgdGhpcy50b2sudHlwZSAhPT0gXy50b2tUeXBlcy5icmFjZUw7XG4gIG5vZGUuYm9keSA9IG5vZGUuZXhwcmVzc2lvbiA/IHRoaXMucGFyc2VNYXliZUFzc2lnbigpIDogdGhpcy5wYXJzZUJsb2NrKCk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJGdW5jdGlvbkV4cHJlc3Npb25cIik7XG59O1xuXG5scC5wYXJzZUFycm93RXhwcmVzc2lvbiA9IGZ1bmN0aW9uIChub2RlLCBwYXJhbXMpIHtcbiAgdGhpcy5pbml0RnVuY3Rpb24obm9kZSk7XG4gIG5vZGUucGFyYW1zID0gdGhpcy50b0Fzc2lnbmFibGVMaXN0KHBhcmFtcywgdHJ1ZSk7XG4gIG5vZGUuZXhwcmVzc2lvbiA9IHRoaXMudG9rLnR5cGUgIT09IF8udG9rVHlwZXMuYnJhY2VMO1xuICBub2RlLmJvZHkgPSBub2RlLmV4cHJlc3Npb24gPyB0aGlzLnBhcnNlTWF5YmVBc3NpZ24oKSA6IHRoaXMucGFyc2VCbG9jaygpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiQXJyb3dGdW5jdGlvbkV4cHJlc3Npb25cIik7XG59O1xuXG5scC5wYXJzZUV4cHJMaXN0ID0gZnVuY3Rpb24gKGNsb3NlLCBhbGxvd0VtcHR5KSB7XG4gIHRoaXMucHVzaEN4KCk7XG4gIHZhciBpbmRlbnQgPSB0aGlzLmN1ckluZGVudCxcbiAgICAgIGxpbmUgPSB0aGlzLmN1ckxpbmVTdGFydCxcbiAgICAgIGVsdHMgPSBbXTtcbiAgdGhpcy5uZXh0KCk7IC8vIE9wZW5pbmcgYnJhY2tldFxuICB3aGlsZSAoIXRoaXMuY2xvc2VzKGNsb3NlLCBpbmRlbnQgKyAxLCBsaW5lKSkge1xuICAgIGlmICh0aGlzLmVhdChfLnRva1R5cGVzLmNvbW1hKSkge1xuICAgICAgZWx0cy5wdXNoKGFsbG93RW1wdHkgPyBudWxsIDogdGhpcy5kdW1teUlkZW50KCkpO1xuICAgICAgY29udGludWU7XG4gICAgfVxuICAgIHZhciBlbHQgPSB0aGlzLnBhcnNlTWF5YmVBc3NpZ24oKTtcbiAgICBpZiAoX3BhcnNldXRpbC5pc0R1bW15KGVsdCkpIHtcbiAgICAgIGlmICh0aGlzLmNsb3NlcyhjbG9zZSwgaW5kZW50LCBsaW5lKSkgYnJlYWs7XG4gICAgICB0aGlzLm5leHQoKTtcbiAgICB9IGVsc2Uge1xuICAgICAgZWx0cy5wdXNoKGVsdCk7XG4gICAgfVxuICAgIHRoaXMuZWF0KF8udG9rVHlwZXMuY29tbWEpO1xuICB9XG4gIHRoaXMucG9wQ3goKTtcbiAgaWYgKCF0aGlzLmVhdChjbG9zZSkpIHtcbiAgICAvLyBJZiB0aGVyZSBpcyBubyBjbG9zaW5nIGJyYWNlLCBtYWtlIHRoZSBub2RlIHNwYW4gdG8gdGhlIHN0YXJ0XG4gICAgLy8gb2YgdGhlIG5leHQgdG9rZW4gKHRoaXMgaXMgdXNlZnVsIGZvciBUZXJuKVxuICAgIHRoaXMubGFzdC5lbmQgPSB0aGlzLnRvay5zdGFydDtcbiAgICBpZiAodGhpcy5vcHRpb25zLmxvY2F0aW9ucykgdGhpcy5sYXN0LmxvYy5lbmQgPSB0aGlzLnRvay5sb2Muc3RhcnQ7XG4gIH1cbiAgcmV0dXJuIGVsdHM7XG59O1xuXG59LHtcIi4uXCI6MSxcIi4vcGFyc2V1dGlsXCI6NCxcIi4vc3RhdGVcIjo1fV0sMzpbZnVuY3Rpb24oX2RlcmVxXyxtb2R1bGUsZXhwb3J0cyl7XG4vLyBBY29ybjogTG9vc2UgcGFyc2VyXG4vL1xuLy8gVGhpcyBtb2R1bGUgcHJvdmlkZXMgYW4gYWx0ZXJuYXRpdmUgcGFyc2VyIChgcGFyc2VfZGFtbWl0YCkgdGhhdFxuLy8gZXhwb3NlcyB0aGF0IHNhbWUgaW50ZXJmYWNlIGFzIGBwYXJzZWAsIGJ1dCB3aWxsIHRyeSB0byBwYXJzZVxuLy8gYW55dGhpbmcgYXMgSmF2YVNjcmlwdCwgcmVwYWlyaW5nIHN5bnRheCBlcnJvciB0aGUgYmVzdCBpdCBjYW4uXG4vLyBUaGVyZSBhcmUgY2lyY3Vtc3RhbmNlcyBpbiB3aGljaCBpdCB3aWxsIHJhaXNlIGFuIGVycm9yIGFuZCBnaXZlXG4vLyB1cCwgYnV0IHRoZXkgYXJlIHZlcnkgcmFyZS4gVGhlIHJlc3VsdGluZyBBU1Qgd2lsbCBiZSBhIG1vc3RseVxuLy8gdmFsaWQgSmF2YVNjcmlwdCBBU1QgKGFzIHBlciB0aGUgW01vemlsbGEgcGFyc2VyIEFQSV1bYXBpXSwgZXhjZXB0XG4vLyB0aGF0OlxuLy9cbi8vIC0gUmV0dXJuIG91dHNpZGUgZnVuY3Rpb25zIGlzIGFsbG93ZWRcbi8vXG4vLyAtIExhYmVsIGNvbnNpc3RlbmN5IChubyBjb25mbGljdHMsIGJyZWFrIG9ubHkgdG8gZXhpc3RpbmcgbGFiZWxzKVxuLy8gICBpcyBub3QgZW5mb3JjZWQuXG4vL1xuLy8gLSBCb2d1cyBJZGVudGlmaWVyIG5vZGVzIHdpdGggYSBuYW1lIG9mIGBcIuKcllwiYCBhcmUgaW5zZXJ0ZWQgd2hlbmV2ZXJcbi8vICAgdGhlIHBhcnNlciBnb3QgdG9vIGNvbmZ1c2VkIHRvIHJldHVybiBhbnl0aGluZyBtZWFuaW5nZnVsLlxuLy9cbi8vIFthcGldOiBodHRwczovL2RldmVsb3Blci5tb3ppbGxhLm9yZy9lbi1VUy9kb2NzL1NwaWRlck1vbmtleS9QYXJzZXJfQVBJXG4vL1xuLy8gVGhlIGV4cGVjdGVkIHVzZSBmb3IgdGhpcyBpcyB0byAqZmlyc3QqIHRyeSBgYWNvcm4ucGFyc2VgLCBhbmQgb25seVxuLy8gaWYgdGhhdCBmYWlscyBzd2l0Y2ggdG8gYHBhcnNlX2RhbW1pdGAuIFRoZSBsb29zZSBwYXJzZXIgbWlnaHRcbi8vIHBhcnNlIGJhZGx5IGluZGVudGVkIGNvZGUgaW5jb3JyZWN0bHksIHNvICoqZG9uJ3QqKiB1c2UgaXQgYXNcbi8vIHlvdXIgZGVmYXVsdCBwYXJzZXIuXG4vL1xuLy8gUXVpdGUgYSBsb3Qgb2YgYWNvcm4uanMgaXMgZHVwbGljYXRlZCBoZXJlLiBUaGUgYWx0ZXJuYXRpdmUgd2FzIHRvXG4vLyBhZGQgYSAqbG90KiBvZiBleHRyYSBjcnVmdCB0byB0aGF0IGZpbGUsIG1ha2luZyBpdCBsZXNzIHJlYWRhYmxlXG4vLyBhbmQgc2xvd2VyLiBDb3B5aW5nIGFuZCBlZGl0aW5nIHRoZSBjb2RlIGFsbG93ZWQgbWUgdG8gbWFrZVxuLy8gaW52YXNpdmUgY2hhbmdlcyBhbmQgc2ltcGxpZmljYXRpb25zIHdpdGhvdXQgY3JlYXRpbmcgYSBjb21wbGljYXRlZFxuLy8gdGFuZ2xlLlxuXG5cInVzZSBzdHJpY3RcIjtcblxuZXhwb3J0cy5fX2VzTW9kdWxlID0gdHJ1ZTtcbmV4cG9ydHMucGFyc2VfZGFtbWl0ID0gcGFyc2VfZGFtbWl0O1xuXG5mdW5jdGlvbiBfaW50ZXJvcFJlcXVpcmVXaWxkY2FyZChvYmopIHsgaWYgKG9iaiAmJiBvYmouX19lc01vZHVsZSkgeyByZXR1cm4gb2JqOyB9IGVsc2UgeyB2YXIgbmV3T2JqID0ge307IGlmIChvYmogIT0gbnVsbCkgeyBmb3IgKHZhciBrZXkgaW4gb2JqKSB7IGlmIChPYmplY3QucHJvdG90eXBlLmhhc093blByb3BlcnR5LmNhbGwob2JqLCBrZXkpKSBuZXdPYmpba2V5XSA9IG9ialtrZXldOyB9IH0gbmV3T2JqW1wiZGVmYXVsdFwiXSA9IG9iajsgcmV0dXJuIG5ld09iajsgfSB9XG5cbnZhciBfID0gX2RlcmVxXyhcIi4uXCIpO1xuXG52YXIgYWNvcm4gPSBfaW50ZXJvcFJlcXVpcmVXaWxkY2FyZChfKTtcblxudmFyIF9zdGF0ZSA9IF9kZXJlcV8oXCIuL3N0YXRlXCIpO1xuXG5fZGVyZXFfKFwiLi90b2tlbml6ZVwiKTtcblxuX2RlcmVxXyhcIi4vc3RhdGVtZW50XCIpO1xuXG5fZGVyZXFfKFwiLi9leHByZXNzaW9uXCIpO1xuXG5leHBvcnRzLkxvb3NlUGFyc2VyID0gX3N0YXRlLkxvb3NlUGFyc2VyO1xuXG5hY29ybi5kZWZhdWx0T3B0aW9ucy50YWJTaXplID0gNDtcblxuZnVuY3Rpb24gcGFyc2VfZGFtbWl0KGlucHV0LCBvcHRpb25zKSB7XG4gIHZhciBwID0gbmV3IF9zdGF0ZS5Mb29zZVBhcnNlcihpbnB1dCwgb3B0aW9ucyk7XG4gIHAubmV4dCgpO1xuICByZXR1cm4gcC5wYXJzZVRvcExldmVsKCk7XG59XG5cbmFjb3JuLnBhcnNlX2RhbW1pdCA9IHBhcnNlX2RhbW1pdDtcbmFjb3JuLkxvb3NlUGFyc2VyID0gX3N0YXRlLkxvb3NlUGFyc2VyO1xuXG59LHtcIi4uXCI6MSxcIi4vZXhwcmVzc2lvblwiOjIsXCIuL3N0YXRlXCI6NSxcIi4vc3RhdGVtZW50XCI6NixcIi4vdG9rZW5pemVcIjo3fV0sNDpbZnVuY3Rpb24oX2RlcmVxXyxtb2R1bGUsZXhwb3J0cyl7XG5cInVzZSBzdHJpY3RcIjtcblxuZXhwb3J0cy5fX2VzTW9kdWxlID0gdHJ1ZTtcbmV4cG9ydHMuaXNEdW1teSA9IGlzRHVtbXk7XG5cbmZ1bmN0aW9uIGlzRHVtbXkobm9kZSkge1xuICByZXR1cm4gbm9kZS5uYW1lID09IFwi4pyWXCI7XG59XG5cbn0se31dLDU6W2Z1bmN0aW9uKF9kZXJlcV8sbW9kdWxlLGV4cG9ydHMpe1xuXCJ1c2Ugc3RyaWN0XCI7XG5cbmV4cG9ydHMuX19lc01vZHVsZSA9IHRydWU7XG5cbmZ1bmN0aW9uIF9jbGFzc0NhbGxDaGVjayhpbnN0YW5jZSwgQ29uc3RydWN0b3IpIHsgaWYgKCEoaW5zdGFuY2UgaW5zdGFuY2VvZiBDb25zdHJ1Y3RvcikpIHsgdGhyb3cgbmV3IFR5cGVFcnJvcihcIkNhbm5vdCBjYWxsIGEgY2xhc3MgYXMgYSBmdW5jdGlvblwiKTsgfSB9XG5cbnZhciBfID0gX2RlcmVxXyhcIi4uXCIpO1xuXG52YXIgTG9vc2VQYXJzZXIgPSAoZnVuY3Rpb24gKCkge1xuICBmdW5jdGlvbiBMb29zZVBhcnNlcihpbnB1dCwgb3B0aW9ucykge1xuICAgIF9jbGFzc0NhbGxDaGVjayh0aGlzLCBMb29zZVBhcnNlcik7XG5cbiAgICB0aGlzLnRva3MgPSBfLnRva2VuaXplcihpbnB1dCwgb3B0aW9ucyk7XG4gICAgdGhpcy5vcHRpb25zID0gdGhpcy50b2tzLm9wdGlvbnM7XG4gICAgdGhpcy5pbnB1dCA9IHRoaXMudG9rcy5pbnB1dDtcbiAgICB0aGlzLnRvayA9IHRoaXMubGFzdCA9IHsgdHlwZTogXy50b2tUeXBlcy5lb2YsIHN0YXJ0OiAwLCBlbmQ6IDAgfTtcbiAgICBpZiAodGhpcy5vcHRpb25zLmxvY2F0aW9ucykge1xuICAgICAgdmFyIGhlcmUgPSB0aGlzLnRva3MuY3VyUG9zaXRpb24oKTtcbiAgICAgIHRoaXMudG9rLmxvYyA9IG5ldyBfLlNvdXJjZUxvY2F0aW9uKHRoaXMudG9rcywgaGVyZSwgaGVyZSk7XG4gICAgfVxuICAgIHRoaXMuYWhlYWQgPSBbXTsgLy8gVG9rZW5zIGFoZWFkXG4gICAgdGhpcy5jb250ZXh0ID0gW107IC8vIEluZGVudGF0aW9uIGNvbnRleHRlZFxuICAgIHRoaXMuY3VySW5kZW50ID0gMDtcbiAgICB0aGlzLmN1ckxpbmVTdGFydCA9IDA7XG4gICAgdGhpcy5uZXh0TGluZVN0YXJ0ID0gdGhpcy5saW5lRW5kKHRoaXMuY3VyTGluZVN0YXJ0KSArIDE7XG4gIH1cblxuICBMb29zZVBhcnNlci5wcm90b3R5cGUuc3RhcnROb2RlID0gZnVuY3Rpb24gc3RhcnROb2RlKCkge1xuICAgIHJldHVybiBuZXcgXy5Ob2RlKHRoaXMudG9rcywgdGhpcy50b2suc3RhcnQsIHRoaXMub3B0aW9ucy5sb2NhdGlvbnMgPyB0aGlzLnRvay5sb2Muc3RhcnQgOiBudWxsKTtcbiAgfTtcblxuICBMb29zZVBhcnNlci5wcm90b3R5cGUuc3RvcmVDdXJyZW50UG9zID0gZnVuY3Rpb24gc3RvcmVDdXJyZW50UG9zKCkge1xuICAgIHJldHVybiB0aGlzLm9wdGlvbnMubG9jYXRpb25zID8gW3RoaXMudG9rLnN0YXJ0LCB0aGlzLnRvay5sb2Muc3RhcnRdIDogdGhpcy50b2suc3RhcnQ7XG4gIH07XG5cbiAgTG9vc2VQYXJzZXIucHJvdG90eXBlLnN0YXJ0Tm9kZUF0ID0gZnVuY3Rpb24gc3RhcnROb2RlQXQocG9zKSB7XG4gICAgaWYgKHRoaXMub3B0aW9ucy5sb2NhdGlvbnMpIHtcbiAgICAgIHJldHVybiBuZXcgXy5Ob2RlKHRoaXMudG9rcywgcG9zWzBdLCBwb3NbMV0pO1xuICAgIH0gZWxzZSB7XG4gICAgICByZXR1cm4gbmV3IF8uTm9kZSh0aGlzLnRva3MsIHBvcyk7XG4gICAgfVxuICB9O1xuXG4gIExvb3NlUGFyc2VyLnByb3RvdHlwZS5maW5pc2hOb2RlID0gZnVuY3Rpb24gZmluaXNoTm9kZShub2RlLCB0eXBlKSB7XG4gICAgbm9kZS50eXBlID0gdHlwZTtcbiAgICBub2RlLmVuZCA9IHRoaXMubGFzdC5lbmQ7XG4gICAgaWYgKHRoaXMub3B0aW9ucy5sb2NhdGlvbnMpIG5vZGUubG9jLmVuZCA9IHRoaXMubGFzdC5sb2MuZW5kO1xuICAgIGlmICh0aGlzLm9wdGlvbnMucmFuZ2VzKSBub2RlLnJhbmdlWzFdID0gdGhpcy5sYXN0LmVuZDtcbiAgICByZXR1cm4gbm9kZTtcbiAgfTtcblxuICBMb29zZVBhcnNlci5wcm90b3R5cGUuZHVtbXlJZGVudCA9IGZ1bmN0aW9uIGR1bW15SWRlbnQoKSB7XG4gICAgdmFyIGR1bW15ID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgICBkdW1teS5uYW1lID0gXCLinJZcIjtcbiAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKGR1bW15LCBcIklkZW50aWZpZXJcIik7XG4gIH07XG5cbiAgTG9vc2VQYXJzZXIucHJvdG90eXBlLmR1bW15U3RyaW5nID0gZnVuY3Rpb24gZHVtbXlTdHJpbmcoKSB7XG4gICAgdmFyIGR1bW15ID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgICBkdW1teS52YWx1ZSA9IGR1bW15LnJhdyA9IFwi4pyWXCI7XG4gICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShkdW1teSwgXCJMaXRlcmFsXCIpO1xuICB9O1xuXG4gIExvb3NlUGFyc2VyLnByb3RvdHlwZS5lYXQgPSBmdW5jdGlvbiBlYXQodHlwZSkge1xuICAgIGlmICh0aGlzLnRvay50eXBlID09PSB0eXBlKSB7XG4gICAgICB0aGlzLm5leHQoKTtcbiAgICAgIHJldHVybiB0cnVlO1xuICAgIH0gZWxzZSB7XG4gICAgICByZXR1cm4gZmFsc2U7XG4gICAgfVxuICB9O1xuXG4gIExvb3NlUGFyc2VyLnByb3RvdHlwZS5pc0NvbnRleHR1YWwgPSBmdW5jdGlvbiBpc0NvbnRleHR1YWwobmFtZSkge1xuICAgIHJldHVybiB0aGlzLnRvay50eXBlID09PSBfLnRva1R5cGVzLm5hbWUgJiYgdGhpcy50b2sudmFsdWUgPT09IG5hbWU7XG4gIH07XG5cbiAgTG9vc2VQYXJzZXIucHJvdG90eXBlLmVhdENvbnRleHR1YWwgPSBmdW5jdGlvbiBlYXRDb250ZXh0dWFsKG5hbWUpIHtcbiAgICByZXR1cm4gdGhpcy50b2sudmFsdWUgPT09IG5hbWUgJiYgdGhpcy5lYXQoXy50b2tUeXBlcy5uYW1lKTtcbiAgfTtcblxuICBMb29zZVBhcnNlci5wcm90b3R5cGUuY2FuSW5zZXJ0U2VtaWNvbG9uID0gZnVuY3Rpb24gY2FuSW5zZXJ0U2VtaWNvbG9uKCkge1xuICAgIHJldHVybiB0aGlzLnRvay50eXBlID09PSBfLnRva1R5cGVzLmVvZiB8fCB0aGlzLnRvay50eXBlID09PSBfLnRva1R5cGVzLmJyYWNlUiB8fCBfLmxpbmVCcmVhay50ZXN0KHRoaXMuaW5wdXQuc2xpY2UodGhpcy5sYXN0LmVuZCwgdGhpcy50b2suc3RhcnQpKTtcbiAgfTtcblxuICBMb29zZVBhcnNlci5wcm90b3R5cGUuc2VtaWNvbG9uID0gZnVuY3Rpb24gc2VtaWNvbG9uKCkge1xuICAgIHJldHVybiB0aGlzLmVhdChfLnRva1R5cGVzLnNlbWkpO1xuICB9O1xuXG4gIExvb3NlUGFyc2VyLnByb3RvdHlwZS5leHBlY3QgPSBmdW5jdGlvbiBleHBlY3QodHlwZSkge1xuICAgIGlmICh0aGlzLmVhdCh0eXBlKSkgcmV0dXJuIHRydWU7XG4gICAgZm9yICh2YXIgaSA9IDE7IGkgPD0gMjsgaSsrKSB7XG4gICAgICBpZiAodGhpcy5sb29rQWhlYWQoaSkudHlwZSA9PSB0eXBlKSB7XG4gICAgICAgIGZvciAodmFyIGogPSAwOyBqIDwgaTsgaisrKSB7XG4gICAgICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICAgIH1yZXR1cm4gdHJ1ZTtcbiAgICAgIH1cbiAgICB9XG4gIH07XG5cbiAgTG9vc2VQYXJzZXIucHJvdG90eXBlLnB1c2hDeCA9IGZ1bmN0aW9uIHB1c2hDeCgpIHtcbiAgICB0aGlzLmNvbnRleHQucHVzaCh0aGlzLmN1ckluZGVudCk7XG4gIH07XG5cbiAgTG9vc2VQYXJzZXIucHJvdG90eXBlLnBvcEN4ID0gZnVuY3Rpb24gcG9wQ3goKSB7XG4gICAgdGhpcy5jdXJJbmRlbnQgPSB0aGlzLmNvbnRleHQucG9wKCk7XG4gIH07XG5cbiAgTG9vc2VQYXJzZXIucHJvdG90eXBlLmxpbmVFbmQgPSBmdW5jdGlvbiBsaW5lRW5kKHBvcykge1xuICAgIHdoaWxlIChwb3MgPCB0aGlzLmlucHV0Lmxlbmd0aCAmJiAhXy5pc05ld0xpbmUodGhpcy5pbnB1dC5jaGFyQ29kZUF0KHBvcykpKSArK3BvcztcbiAgICByZXR1cm4gcG9zO1xuICB9O1xuXG4gIExvb3NlUGFyc2VyLnByb3RvdHlwZS5pbmRlbnRhdGlvbkFmdGVyID0gZnVuY3Rpb24gaW5kZW50YXRpb25BZnRlcihwb3MpIHtcbiAgICBmb3IgKHZhciBjb3VudCA9IDA7OyArK3Bvcykge1xuICAgICAgdmFyIGNoID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHBvcyk7XG4gICAgICBpZiAoY2ggPT09IDMyKSArK2NvdW50O2Vsc2UgaWYgKGNoID09PSA5KSBjb3VudCArPSB0aGlzLm9wdGlvbnMudGFiU2l6ZTtlbHNlIHJldHVybiBjb3VudDtcbiAgICB9XG4gIH07XG5cbiAgTG9vc2VQYXJzZXIucHJvdG90eXBlLmNsb3NlcyA9IGZ1bmN0aW9uIGNsb3NlcyhjbG9zZVRvaywgaW5kZW50LCBsaW5lLCBibG9ja0hldXJpc3RpYykge1xuICAgIGlmICh0aGlzLnRvay50eXBlID09PSBjbG9zZVRvayB8fCB0aGlzLnRvay50eXBlID09PSBfLnRva1R5cGVzLmVvZikgcmV0dXJuIHRydWU7XG4gICAgcmV0dXJuIGxpbmUgIT0gdGhpcy5jdXJMaW5lU3RhcnQgJiYgdGhpcy5jdXJJbmRlbnQgPCBpbmRlbnQgJiYgdGhpcy50b2tlblN0YXJ0c0xpbmUoKSAmJiAoIWJsb2NrSGV1cmlzdGljIHx8IHRoaXMubmV4dExpbmVTdGFydCA+PSB0aGlzLmlucHV0Lmxlbmd0aCB8fCB0aGlzLmluZGVudGF0aW9uQWZ0ZXIodGhpcy5uZXh0TGluZVN0YXJ0KSA8IGluZGVudCk7XG4gIH07XG5cbiAgTG9vc2VQYXJzZXIucHJvdG90eXBlLnRva2VuU3RhcnRzTGluZSA9IGZ1bmN0aW9uIHRva2VuU3RhcnRzTGluZSgpIHtcbiAgICBmb3IgKHZhciBwID0gdGhpcy50b2suc3RhcnQgLSAxOyBwID49IHRoaXMuY3VyTGluZVN0YXJ0OyAtLXApIHtcbiAgICAgIHZhciBjaCA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdChwKTtcbiAgICAgIGlmIChjaCAhPT0gOSAmJiBjaCAhPT0gMzIpIHJldHVybiBmYWxzZTtcbiAgICB9XG4gICAgcmV0dXJuIHRydWU7XG4gIH07XG5cbiAgcmV0dXJuIExvb3NlUGFyc2VyO1xufSkoKTtcblxuZXhwb3J0cy5Mb29zZVBhcnNlciA9IExvb3NlUGFyc2VyO1xuXG59LHtcIi4uXCI6MX1dLDY6W2Z1bmN0aW9uKF9kZXJlcV8sbW9kdWxlLGV4cG9ydHMpe1xuXCJ1c2Ugc3RyaWN0XCI7XG5cbnZhciBfc3RhdGUgPSBfZGVyZXFfKFwiLi9zdGF0ZVwiKTtcblxudmFyIF9wYXJzZXV0aWwgPSBfZGVyZXFfKFwiLi9wYXJzZXV0aWxcIik7XG5cbnZhciBfID0gX2RlcmVxXyhcIi4uXCIpO1xuXG52YXIgbHAgPSBfc3RhdGUuTG9vc2VQYXJzZXIucHJvdG90eXBlO1xuXG5scC5wYXJzZVRvcExldmVsID0gZnVuY3Rpb24gKCkge1xuICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlQXQodGhpcy5vcHRpb25zLmxvY2F0aW9ucyA/IFswLCBfLmdldExpbmVJbmZvKHRoaXMuaW5wdXQsIDApXSA6IDApO1xuICBub2RlLmJvZHkgPSBbXTtcbiAgd2hpbGUgKHRoaXMudG9rLnR5cGUgIT09IF8udG9rVHlwZXMuZW9mKSBub2RlLmJvZHkucHVzaCh0aGlzLnBhcnNlU3RhdGVtZW50KCkpO1xuICB0aGlzLmxhc3QgPSB0aGlzLnRvaztcbiAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KSB7XG4gICAgbm9kZS5zb3VyY2VUeXBlID0gdGhpcy5vcHRpb25zLnNvdXJjZVR5cGU7XG4gIH1cbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIlByb2dyYW1cIik7XG59O1xuXG5scC5wYXJzZVN0YXRlbWVudCA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIHN0YXJ0dHlwZSA9IHRoaXMudG9rLnR5cGUsXG4gICAgICBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcblxuICBzd2l0Y2ggKHN0YXJ0dHlwZSkge1xuICAgIGNhc2UgXy50b2tUeXBlcy5fYnJlYWs6Y2FzZSBfLnRva1R5cGVzLl9jb250aW51ZTpcbiAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgdmFyIGlzQnJlYWsgPSBzdGFydHR5cGUgPT09IF8udG9rVHlwZXMuX2JyZWFrO1xuICAgICAgaWYgKHRoaXMuc2VtaWNvbG9uKCkgfHwgdGhpcy5jYW5JbnNlcnRTZW1pY29sb24oKSkge1xuICAgICAgICBub2RlLmxhYmVsID0gbnVsbDtcbiAgICAgIH0gZWxzZSB7XG4gICAgICAgIG5vZGUubGFiZWwgPSB0aGlzLnRvay50eXBlID09PSBfLnRva1R5cGVzLm5hbWUgPyB0aGlzLnBhcnNlSWRlbnQoKSA6IG51bGw7XG4gICAgICAgIHRoaXMuc2VtaWNvbG9uKCk7XG4gICAgICB9XG4gICAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIGlzQnJlYWsgPyBcIkJyZWFrU3RhdGVtZW50XCIgOiBcIkNvbnRpbnVlU3RhdGVtZW50XCIpO1xuXG4gICAgY2FzZSBfLnRva1R5cGVzLl9kZWJ1Z2dlcjpcbiAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgdGhpcy5zZW1pY29sb24oKTtcbiAgICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJEZWJ1Z2dlclN0YXRlbWVudFwiKTtcblxuICAgIGNhc2UgXy50b2tUeXBlcy5fZG86XG4gICAgICB0aGlzLm5leHQoKTtcbiAgICAgIG5vZGUuYm9keSA9IHRoaXMucGFyc2VTdGF0ZW1lbnQoKTtcbiAgICAgIG5vZGUudGVzdCA9IHRoaXMuZWF0KF8udG9rVHlwZXMuX3doaWxlKSA/IHRoaXMucGFyc2VQYXJlbkV4cHJlc3Npb24oKSA6IHRoaXMuZHVtbXlJZGVudCgpO1xuICAgICAgdGhpcy5zZW1pY29sb24oKTtcbiAgICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJEb1doaWxlU3RhdGVtZW50XCIpO1xuXG4gICAgY2FzZSBfLnRva1R5cGVzLl9mb3I6XG4gICAgICB0aGlzLm5leHQoKTtcbiAgICAgIHRoaXMucHVzaEN4KCk7XG4gICAgICB0aGlzLmV4cGVjdChfLnRva1R5cGVzLnBhcmVuTCk7XG4gICAgICBpZiAodGhpcy50b2sudHlwZSA9PT0gXy50b2tUeXBlcy5zZW1pKSByZXR1cm4gdGhpcy5wYXJzZUZvcihub2RlLCBudWxsKTtcbiAgICAgIGlmICh0aGlzLnRvay50eXBlID09PSBfLnRva1R5cGVzLl92YXIgfHwgdGhpcy50b2sudHlwZSA9PT0gXy50b2tUeXBlcy5fbGV0IHx8IHRoaXMudG9rLnR5cGUgPT09IF8udG9rVHlwZXMuX2NvbnN0KSB7XG4gICAgICAgIHZhciBfaW5pdCA9IHRoaXMucGFyc2VWYXIodHJ1ZSk7XG4gICAgICAgIGlmIChfaW5pdC5kZWNsYXJhdGlvbnMubGVuZ3RoID09PSAxICYmICh0aGlzLnRvay50eXBlID09PSBfLnRva1R5cGVzLl9pbiB8fCB0aGlzLmlzQ29udGV4dHVhbChcIm9mXCIpKSkge1xuICAgICAgICAgIHJldHVybiB0aGlzLnBhcnNlRm9ySW4obm9kZSwgX2luaXQpO1xuICAgICAgICB9XG4gICAgICAgIHJldHVybiB0aGlzLnBhcnNlRm9yKG5vZGUsIF9pbml0KTtcbiAgICAgIH1cbiAgICAgIHZhciBpbml0ID0gdGhpcy5wYXJzZUV4cHJlc3Npb24odHJ1ZSk7XG4gICAgICBpZiAodGhpcy50b2sudHlwZSA9PT0gXy50b2tUeXBlcy5faW4gfHwgdGhpcy5pc0NvbnRleHR1YWwoXCJvZlwiKSkgcmV0dXJuIHRoaXMucGFyc2VGb3JJbihub2RlLCB0aGlzLnRvQXNzaWduYWJsZShpbml0KSk7XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZUZvcihub2RlLCBpbml0KTtcblxuICAgIGNhc2UgXy50b2tUeXBlcy5fZnVuY3Rpb246XG4gICAgICB0aGlzLm5leHQoKTtcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlRnVuY3Rpb24obm9kZSwgdHJ1ZSk7XG5cbiAgICBjYXNlIF8udG9rVHlwZXMuX2lmOlxuICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICBub2RlLnRlc3QgPSB0aGlzLnBhcnNlUGFyZW5FeHByZXNzaW9uKCk7XG4gICAgICBub2RlLmNvbnNlcXVlbnQgPSB0aGlzLnBhcnNlU3RhdGVtZW50KCk7XG4gICAgICBub2RlLmFsdGVybmF0ZSA9IHRoaXMuZWF0KF8udG9rVHlwZXMuX2Vsc2UpID8gdGhpcy5wYXJzZVN0YXRlbWVudCgpIDogbnVsbDtcbiAgICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJJZlN0YXRlbWVudFwiKTtcblxuICAgIGNhc2UgXy50b2tUeXBlcy5fcmV0dXJuOlxuICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICBpZiAodGhpcy5lYXQoXy50b2tUeXBlcy5zZW1pKSB8fCB0aGlzLmNhbkluc2VydFNlbWljb2xvbigpKSBub2RlLmFyZ3VtZW50ID0gbnVsbDtlbHNlIHtcbiAgICAgICAgbm9kZS5hcmd1bWVudCA9IHRoaXMucGFyc2VFeHByZXNzaW9uKCk7dGhpcy5zZW1pY29sb24oKTtcbiAgICAgIH1cbiAgICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJSZXR1cm5TdGF0ZW1lbnRcIik7XG5cbiAgICBjYXNlIF8udG9rVHlwZXMuX3N3aXRjaDpcbiAgICAgIHZhciBibG9ja0luZGVudCA9IHRoaXMuY3VySW5kZW50LFxuICAgICAgICAgIGxpbmUgPSB0aGlzLmN1ckxpbmVTdGFydDtcbiAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgbm9kZS5kaXNjcmltaW5hbnQgPSB0aGlzLnBhcnNlUGFyZW5FeHByZXNzaW9uKCk7XG4gICAgICBub2RlLmNhc2VzID0gW107XG4gICAgICB0aGlzLnB1c2hDeCgpO1xuICAgICAgdGhpcy5leHBlY3QoXy50b2tUeXBlcy5icmFjZUwpO1xuXG4gICAgICB2YXIgY3VyID0gdW5kZWZpbmVkO1xuICAgICAgd2hpbGUgKCF0aGlzLmNsb3NlcyhfLnRva1R5cGVzLmJyYWNlUiwgYmxvY2tJbmRlbnQsIGxpbmUsIHRydWUpKSB7XG4gICAgICAgIGlmICh0aGlzLnRvay50eXBlID09PSBfLnRva1R5cGVzLl9jYXNlIHx8IHRoaXMudG9rLnR5cGUgPT09IF8udG9rVHlwZXMuX2RlZmF1bHQpIHtcbiAgICAgICAgICB2YXIgaXNDYXNlID0gdGhpcy50b2sudHlwZSA9PT0gXy50b2tUeXBlcy5fY2FzZTtcbiAgICAgICAgICBpZiAoY3VyKSB0aGlzLmZpbmlzaE5vZGUoY3VyLCBcIlN3aXRjaENhc2VcIik7XG4gICAgICAgICAgbm9kZS5jYXNlcy5wdXNoKGN1ciA9IHRoaXMuc3RhcnROb2RlKCkpO1xuICAgICAgICAgIGN1ci5jb25zZXF1ZW50ID0gW107XG4gICAgICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICAgICAgaWYgKGlzQ2FzZSkgY3VyLnRlc3QgPSB0aGlzLnBhcnNlRXhwcmVzc2lvbigpO2Vsc2UgY3VyLnRlc3QgPSBudWxsO1xuICAgICAgICAgIHRoaXMuZXhwZWN0KF8udG9rVHlwZXMuY29sb24pO1xuICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgIGlmICghY3VyKSB7XG4gICAgICAgICAgICBub2RlLmNhc2VzLnB1c2goY3VyID0gdGhpcy5zdGFydE5vZGUoKSk7XG4gICAgICAgICAgICBjdXIuY29uc2VxdWVudCA9IFtdO1xuICAgICAgICAgICAgY3VyLnRlc3QgPSBudWxsO1xuICAgICAgICAgIH1cbiAgICAgICAgICBjdXIuY29uc2VxdWVudC5wdXNoKHRoaXMucGFyc2VTdGF0ZW1lbnQoKSk7XG4gICAgICAgIH1cbiAgICAgIH1cbiAgICAgIGlmIChjdXIpIHRoaXMuZmluaXNoTm9kZShjdXIsIFwiU3dpdGNoQ2FzZVwiKTtcbiAgICAgIHRoaXMucG9wQ3goKTtcbiAgICAgIHRoaXMuZWF0KF8udG9rVHlwZXMuYnJhY2VSKTtcbiAgICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJTd2l0Y2hTdGF0ZW1lbnRcIik7XG5cbiAgICBjYXNlIF8udG9rVHlwZXMuX3Rocm93OlxuICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICBub2RlLmFyZ3VtZW50ID0gdGhpcy5wYXJzZUV4cHJlc3Npb24oKTtcbiAgICAgIHRoaXMuc2VtaWNvbG9uKCk7XG4gICAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiVGhyb3dTdGF0ZW1lbnRcIik7XG5cbiAgICBjYXNlIF8udG9rVHlwZXMuX3RyeTpcbiAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgbm9kZS5ibG9jayA9IHRoaXMucGFyc2VCbG9jaygpO1xuICAgICAgbm9kZS5oYW5kbGVyID0gbnVsbDtcbiAgICAgIGlmICh0aGlzLnRvay50eXBlID09PSBfLnRva1R5cGVzLl9jYXRjaCkge1xuICAgICAgICB2YXIgY2xhdXNlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICAgIHRoaXMuZXhwZWN0KF8udG9rVHlwZXMucGFyZW5MKTtcbiAgICAgICAgY2xhdXNlLnBhcmFtID0gdGhpcy50b0Fzc2lnbmFibGUodGhpcy5wYXJzZUV4cHJBdG9tKCksIHRydWUpO1xuICAgICAgICB0aGlzLmV4cGVjdChfLnRva1R5cGVzLnBhcmVuUik7XG4gICAgICAgIGNsYXVzZS5ndWFyZCA9IG51bGw7XG4gICAgICAgIGNsYXVzZS5ib2R5ID0gdGhpcy5wYXJzZUJsb2NrKCk7XG4gICAgICAgIG5vZGUuaGFuZGxlciA9IHRoaXMuZmluaXNoTm9kZShjbGF1c2UsIFwiQ2F0Y2hDbGF1c2VcIik7XG4gICAgICB9XG4gICAgICBub2RlLmZpbmFsaXplciA9IHRoaXMuZWF0KF8udG9rVHlwZXMuX2ZpbmFsbHkpID8gdGhpcy5wYXJzZUJsb2NrKCkgOiBudWxsO1xuICAgICAgaWYgKCFub2RlLmhhbmRsZXIgJiYgIW5vZGUuZmluYWxpemVyKSByZXR1cm4gbm9kZS5ibG9jaztcbiAgICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJUcnlTdGF0ZW1lbnRcIik7XG5cbiAgICBjYXNlIF8udG9rVHlwZXMuX3ZhcjpcbiAgICBjYXNlIF8udG9rVHlwZXMuX2xldDpcbiAgICBjYXNlIF8udG9rVHlwZXMuX2NvbnN0OlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VWYXIoKTtcblxuICAgIGNhc2UgXy50b2tUeXBlcy5fd2hpbGU6XG4gICAgICB0aGlzLm5leHQoKTtcbiAgICAgIG5vZGUudGVzdCA9IHRoaXMucGFyc2VQYXJlbkV4cHJlc3Npb24oKTtcbiAgICAgIG5vZGUuYm9keSA9IHRoaXMucGFyc2VTdGF0ZW1lbnQoKTtcbiAgICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJXaGlsZVN0YXRlbWVudFwiKTtcblxuICAgIGNhc2UgXy50b2tUeXBlcy5fd2l0aDpcbiAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgbm9kZS5vYmplY3QgPSB0aGlzLnBhcnNlUGFyZW5FeHByZXNzaW9uKCk7XG4gICAgICBub2RlLmJvZHkgPSB0aGlzLnBhcnNlU3RhdGVtZW50KCk7XG4gICAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiV2l0aFN0YXRlbWVudFwiKTtcblxuICAgIGNhc2UgXy50b2tUeXBlcy5icmFjZUw6XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZUJsb2NrKCk7XG5cbiAgICBjYXNlIF8udG9rVHlwZXMuc2VtaTpcbiAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkVtcHR5U3RhdGVtZW50XCIpO1xuXG4gICAgY2FzZSBfLnRva1R5cGVzLl9jbGFzczpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlQ2xhc3ModHJ1ZSk7XG5cbiAgICBjYXNlIF8udG9rVHlwZXMuX2ltcG9ydDpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlSW1wb3J0KCk7XG5cbiAgICBjYXNlIF8udG9rVHlwZXMuX2V4cG9ydDpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlRXhwb3J0KCk7XG5cbiAgICBkZWZhdWx0OlxuICAgICAgdmFyIGV4cHIgPSB0aGlzLnBhcnNlRXhwcmVzc2lvbigpO1xuICAgICAgaWYgKF9wYXJzZXV0aWwuaXNEdW1teShleHByKSkge1xuICAgICAgICB0aGlzLm5leHQoKTtcbiAgICAgICAgaWYgKHRoaXMudG9rLnR5cGUgPT09IF8udG9rVHlwZXMuZW9mKSByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiRW1wdHlTdGF0ZW1lbnRcIik7XG4gICAgICAgIHJldHVybiB0aGlzLnBhcnNlU3RhdGVtZW50KCk7XG4gICAgICB9IGVsc2UgaWYgKHN0YXJ0dHlwZSA9PT0gXy50b2tUeXBlcy5uYW1lICYmIGV4cHIudHlwZSA9PT0gXCJJZGVudGlmaWVyXCIgJiYgdGhpcy5lYXQoXy50b2tUeXBlcy5jb2xvbikpIHtcbiAgICAgICAgbm9kZS5ib2R5ID0gdGhpcy5wYXJzZVN0YXRlbWVudCgpO1xuICAgICAgICBub2RlLmxhYmVsID0gZXhwcjtcbiAgICAgICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkxhYmVsZWRTdGF0ZW1lbnRcIik7XG4gICAgICB9IGVsc2Uge1xuICAgICAgICBub2RlLmV4cHJlc3Npb24gPSBleHByO1xuICAgICAgICB0aGlzLnNlbWljb2xvbigpO1xuICAgICAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiRXhwcmVzc2lvblN0YXRlbWVudFwiKTtcbiAgICAgIH1cbiAgfVxufTtcblxubHAucGFyc2VCbG9jayA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICB0aGlzLnB1c2hDeCgpO1xuICB0aGlzLmV4cGVjdChfLnRva1R5cGVzLmJyYWNlTCk7XG4gIHZhciBibG9ja0luZGVudCA9IHRoaXMuY3VySW5kZW50LFxuICAgICAgbGluZSA9IHRoaXMuY3VyTGluZVN0YXJ0O1xuICBub2RlLmJvZHkgPSBbXTtcbiAgd2hpbGUgKCF0aGlzLmNsb3NlcyhfLnRva1R5cGVzLmJyYWNlUiwgYmxvY2tJbmRlbnQsIGxpbmUsIHRydWUpKSBub2RlLmJvZHkucHVzaCh0aGlzLnBhcnNlU3RhdGVtZW50KCkpO1xuICB0aGlzLnBvcEN4KCk7XG4gIHRoaXMuZWF0KF8udG9rVHlwZXMuYnJhY2VSKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkJsb2NrU3RhdGVtZW50XCIpO1xufTtcblxubHAucGFyc2VGb3IgPSBmdW5jdGlvbiAobm9kZSwgaW5pdCkge1xuICBub2RlLmluaXQgPSBpbml0O1xuICBub2RlLnRlc3QgPSBub2RlLnVwZGF0ZSA9IG51bGw7XG4gIGlmICh0aGlzLmVhdChfLnRva1R5cGVzLnNlbWkpICYmIHRoaXMudG9rLnR5cGUgIT09IF8udG9rVHlwZXMuc2VtaSkgbm9kZS50ZXN0ID0gdGhpcy5wYXJzZUV4cHJlc3Npb24oKTtcbiAgaWYgKHRoaXMuZWF0KF8udG9rVHlwZXMuc2VtaSkgJiYgdGhpcy50b2sudHlwZSAhPT0gXy50b2tUeXBlcy5wYXJlblIpIG5vZGUudXBkYXRlID0gdGhpcy5wYXJzZUV4cHJlc3Npb24oKTtcbiAgdGhpcy5wb3BDeCgpO1xuICB0aGlzLmV4cGVjdChfLnRva1R5cGVzLnBhcmVuUik7XG4gIG5vZGUuYm9keSA9IHRoaXMucGFyc2VTdGF0ZW1lbnQoKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkZvclN0YXRlbWVudFwiKTtcbn07XG5cbmxwLnBhcnNlRm9ySW4gPSBmdW5jdGlvbiAobm9kZSwgaW5pdCkge1xuICB2YXIgdHlwZSA9IHRoaXMudG9rLnR5cGUgPT09IF8udG9rVHlwZXMuX2luID8gXCJGb3JJblN0YXRlbWVudFwiIDogXCJGb3JPZlN0YXRlbWVudFwiO1xuICB0aGlzLm5leHQoKTtcbiAgbm9kZS5sZWZ0ID0gaW5pdDtcbiAgbm9kZS5yaWdodCA9IHRoaXMucGFyc2VFeHByZXNzaW9uKCk7XG4gIHRoaXMucG9wQ3goKTtcbiAgdGhpcy5leHBlY3QoXy50b2tUeXBlcy5wYXJlblIpO1xuICBub2RlLmJvZHkgPSB0aGlzLnBhcnNlU3RhdGVtZW50KCk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgdHlwZSk7XG59O1xuXG5scC5wYXJzZVZhciA9IGZ1bmN0aW9uIChub0luKSB7XG4gIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgbm9kZS5raW5kID0gdGhpcy50b2sudHlwZS5rZXl3b3JkO1xuICB0aGlzLm5leHQoKTtcbiAgbm9kZS5kZWNsYXJhdGlvbnMgPSBbXTtcbiAgZG8ge1xuICAgIHZhciBkZWNsID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgICBkZWNsLmlkID0gdGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYgPyB0aGlzLnRvQXNzaWduYWJsZSh0aGlzLnBhcnNlRXhwckF0b20oKSwgdHJ1ZSkgOiB0aGlzLnBhcnNlSWRlbnQoKTtcbiAgICBkZWNsLmluaXQgPSB0aGlzLmVhdChfLnRva1R5cGVzLmVxKSA/IHRoaXMucGFyc2VNYXliZUFzc2lnbihub0luKSA6IG51bGw7XG4gICAgbm9kZS5kZWNsYXJhdGlvbnMucHVzaCh0aGlzLmZpbmlzaE5vZGUoZGVjbCwgXCJWYXJpYWJsZURlY2xhcmF0b3JcIikpO1xuICB9IHdoaWxlICh0aGlzLmVhdChfLnRva1R5cGVzLmNvbW1hKSk7XG4gIGlmICghbm9kZS5kZWNsYXJhdGlvbnMubGVuZ3RoKSB7XG4gICAgdmFyIGRlY2wgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICAgIGRlY2wuaWQgPSB0aGlzLmR1bW15SWRlbnQoKTtcbiAgICBub2RlLmRlY2xhcmF0aW9ucy5wdXNoKHRoaXMuZmluaXNoTm9kZShkZWNsLCBcIlZhcmlhYmxlRGVjbGFyYXRvclwiKSk7XG4gIH1cbiAgaWYgKCFub0luKSB0aGlzLnNlbWljb2xvbigpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiVmFyaWFibGVEZWNsYXJhdGlvblwiKTtcbn07XG5cbmxwLnBhcnNlQ2xhc3MgPSBmdW5jdGlvbiAoaXNTdGF0ZW1lbnQpIHtcbiAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICB0aGlzLm5leHQoKTtcbiAgaWYgKHRoaXMudG9rLnR5cGUgPT09IF8udG9rVHlwZXMubmFtZSkgbm9kZS5pZCA9IHRoaXMucGFyc2VJZGVudCgpO2Vsc2UgaWYgKGlzU3RhdGVtZW50KSBub2RlLmlkID0gdGhpcy5kdW1teUlkZW50KCk7ZWxzZSBub2RlLmlkID0gbnVsbDtcbiAgbm9kZS5zdXBlckNsYXNzID0gdGhpcy5lYXQoXy50b2tUeXBlcy5fZXh0ZW5kcykgPyB0aGlzLnBhcnNlRXhwcmVzc2lvbigpIDogbnVsbDtcbiAgbm9kZS5ib2R5ID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgbm9kZS5ib2R5LmJvZHkgPSBbXTtcbiAgdGhpcy5wdXNoQ3goKTtcbiAgdmFyIGluZGVudCA9IHRoaXMuY3VySW5kZW50ICsgMSxcbiAgICAgIGxpbmUgPSB0aGlzLmN1ckxpbmVTdGFydDtcbiAgdGhpcy5lYXQoXy50b2tUeXBlcy5icmFjZUwpO1xuICBpZiAodGhpcy5jdXJJbmRlbnQgKyAxIDwgaW5kZW50KSB7XG4gICAgaW5kZW50ID0gdGhpcy5jdXJJbmRlbnQ7bGluZSA9IHRoaXMuY3VyTGluZVN0YXJ0O1xuICB9XG4gIHdoaWxlICghdGhpcy5jbG9zZXMoXy50b2tUeXBlcy5icmFjZVIsIGluZGVudCwgbGluZSkpIHtcbiAgICBpZiAodGhpcy5zZW1pY29sb24oKSkgY29udGludWU7XG4gICAgdmFyIG1ldGhvZCA9IHRoaXMuc3RhcnROb2RlKCksXG4gICAgICAgIGlzR2VuZXJhdG9yID0gdW5kZWZpbmVkO1xuICAgIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNikge1xuICAgICAgbWV0aG9kW1wic3RhdGljXCJdID0gZmFsc2U7XG4gICAgICBpc0dlbmVyYXRvciA9IHRoaXMuZWF0KF8udG9rVHlwZXMuc3Rhcik7XG4gICAgfVxuICAgIHRoaXMucGFyc2VQcm9wZXJ0eU5hbWUobWV0aG9kKTtcbiAgICBpZiAoX3BhcnNldXRpbC5pc0R1bW15KG1ldGhvZC5rZXkpKSB7XG4gICAgICBpZiAoX3BhcnNldXRpbC5pc0R1bW15KHRoaXMucGFyc2VNYXliZUFzc2lnbigpKSkgdGhpcy5uZXh0KCk7dGhpcy5lYXQoXy50b2tUeXBlcy5jb21tYSk7Y29udGludWU7XG4gICAgfVxuICAgIGlmIChtZXRob2Qua2V5LnR5cGUgPT09IFwiSWRlbnRpZmllclwiICYmICFtZXRob2QuY29tcHV0ZWQgJiYgbWV0aG9kLmtleS5uYW1lID09PSBcInN0YXRpY1wiICYmICh0aGlzLnRvay50eXBlICE9IF8udG9rVHlwZXMucGFyZW5MICYmIHRoaXMudG9rLnR5cGUgIT0gXy50b2tUeXBlcy5icmFjZUwpKSB7XG4gICAgICBtZXRob2RbXCJzdGF0aWNcIl0gPSB0cnVlO1xuICAgICAgaXNHZW5lcmF0b3IgPSB0aGlzLmVhdChfLnRva1R5cGVzLnN0YXIpO1xuICAgICAgdGhpcy5wYXJzZVByb3BlcnR5TmFtZShtZXRob2QpO1xuICAgIH0gZWxzZSB7XG4gICAgICBtZXRob2RbXCJzdGF0aWNcIl0gPSBmYWxzZTtcbiAgICB9XG4gICAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA1ICYmIG1ldGhvZC5rZXkudHlwZSA9PT0gXCJJZGVudGlmaWVyXCIgJiYgIW1ldGhvZC5jb21wdXRlZCAmJiAobWV0aG9kLmtleS5uYW1lID09PSBcImdldFwiIHx8IG1ldGhvZC5rZXkubmFtZSA9PT0gXCJzZXRcIikgJiYgdGhpcy50b2sudHlwZSAhPT0gXy50b2tUeXBlcy5wYXJlbkwgJiYgdGhpcy50b2sudHlwZSAhPT0gXy50b2tUeXBlcy5icmFjZUwpIHtcbiAgICAgIG1ldGhvZC5raW5kID0gbWV0aG9kLmtleS5uYW1lO1xuICAgICAgdGhpcy5wYXJzZVByb3BlcnR5TmFtZShtZXRob2QpO1xuICAgICAgbWV0aG9kLnZhbHVlID0gdGhpcy5wYXJzZU1ldGhvZChmYWxzZSk7XG4gICAgfSBlbHNlIHtcbiAgICAgIGlmICghbWV0aG9kLmNvbXB1dGVkICYmICFtZXRob2RbXCJzdGF0aWNcIl0gJiYgIWlzR2VuZXJhdG9yICYmIChtZXRob2Qua2V5LnR5cGUgPT09IFwiSWRlbnRpZmllclwiICYmIG1ldGhvZC5rZXkubmFtZSA9PT0gXCJjb25zdHJ1Y3RvclwiIHx8IG1ldGhvZC5rZXkudHlwZSA9PT0gXCJMaXRlcmFsXCIgJiYgbWV0aG9kLmtleS52YWx1ZSA9PT0gXCJjb25zdHJ1Y3RvclwiKSkge1xuICAgICAgICBtZXRob2Qua2luZCA9IFwiY29uc3RydWN0b3JcIjtcbiAgICAgIH0gZWxzZSB7XG4gICAgICAgIG1ldGhvZC5raW5kID0gXCJtZXRob2RcIjtcbiAgICAgIH1cbiAgICAgIG1ldGhvZC52YWx1ZSA9IHRoaXMucGFyc2VNZXRob2QoaXNHZW5lcmF0b3IpO1xuICAgIH1cbiAgICBub2RlLmJvZHkuYm9keS5wdXNoKHRoaXMuZmluaXNoTm9kZShtZXRob2QsIFwiTWV0aG9kRGVmaW5pdGlvblwiKSk7XG4gIH1cbiAgdGhpcy5wb3BDeCgpO1xuICBpZiAoIXRoaXMuZWF0KF8udG9rVHlwZXMuYnJhY2VSKSkge1xuICAgIC8vIElmIHRoZXJlIGlzIG5vIGNsb3NpbmcgYnJhY2UsIG1ha2UgdGhlIG5vZGUgc3BhbiB0byB0aGUgc3RhcnRcbiAgICAvLyBvZiB0aGUgbmV4dCB0b2tlbiAodGhpcyBpcyB1c2VmdWwgZm9yIFRlcm4pXG4gICAgdGhpcy5sYXN0LmVuZCA9IHRoaXMudG9rLnN0YXJ0O1xuICAgIGlmICh0aGlzLm9wdGlvbnMubG9jYXRpb25zKSB0aGlzLmxhc3QubG9jLmVuZCA9IHRoaXMudG9rLmxvYy5zdGFydDtcbiAgfVxuICB0aGlzLnNlbWljb2xvbigpO1xuICB0aGlzLmZpbmlzaE5vZGUobm9kZS5ib2R5LCBcIkNsYXNzQm9keVwiKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBpc1N0YXRlbWVudCA/IFwiQ2xhc3NEZWNsYXJhdGlvblwiIDogXCJDbGFzc0V4cHJlc3Npb25cIik7XG59O1xuXG5scC5wYXJzZUZ1bmN0aW9uID0gZnVuY3Rpb24gKG5vZGUsIGlzU3RhdGVtZW50KSB7XG4gIHRoaXMuaW5pdEZ1bmN0aW9uKG5vZGUpO1xuICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYpIHtcbiAgICBub2RlLmdlbmVyYXRvciA9IHRoaXMuZWF0KF8udG9rVHlwZXMuc3Rhcik7XG4gIH1cbiAgaWYgKHRoaXMudG9rLnR5cGUgPT09IF8udG9rVHlwZXMubmFtZSkgbm9kZS5pZCA9IHRoaXMucGFyc2VJZGVudCgpO2Vsc2UgaWYgKGlzU3RhdGVtZW50KSBub2RlLmlkID0gdGhpcy5kdW1teUlkZW50KCk7XG4gIG5vZGUucGFyYW1zID0gdGhpcy5wYXJzZUZ1bmN0aW9uUGFyYW1zKCk7XG4gIG5vZGUuYm9keSA9IHRoaXMucGFyc2VCbG9jaygpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIGlzU3RhdGVtZW50ID8gXCJGdW5jdGlvbkRlY2xhcmF0aW9uXCIgOiBcIkZ1bmN0aW9uRXhwcmVzc2lvblwiKTtcbn07XG5cbmxwLnBhcnNlRXhwb3J0ID0gZnVuY3Rpb24gKCkge1xuICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gIHRoaXMubmV4dCgpO1xuICBpZiAodGhpcy5lYXQoXy50b2tUeXBlcy5zdGFyKSkge1xuICAgIG5vZGUuc291cmNlID0gdGhpcy5lYXRDb250ZXh0dWFsKFwiZnJvbVwiKSA/IHRoaXMucGFyc2VFeHByQXRvbSgpIDogbnVsbDtcbiAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiRXhwb3J0QWxsRGVjbGFyYXRpb25cIik7XG4gIH1cbiAgaWYgKHRoaXMuZWF0KF8udG9rVHlwZXMuX2RlZmF1bHQpKSB7XG4gICAgdmFyIGV4cHIgPSB0aGlzLnBhcnNlTWF5YmVBc3NpZ24oKTtcbiAgICBpZiAoZXhwci5pZCkge1xuICAgICAgc3dpdGNoIChleHByLnR5cGUpIHtcbiAgICAgICAgY2FzZSBcIkZ1bmN0aW9uRXhwcmVzc2lvblwiOlxuICAgICAgICAgIGV4cHIudHlwZSA9IFwiRnVuY3Rpb25EZWNsYXJhdGlvblwiO2JyZWFrO1xuICAgICAgICBjYXNlIFwiQ2xhc3NFeHByZXNzaW9uXCI6XG4gICAgICAgICAgZXhwci50eXBlID0gXCJDbGFzc0RlY2xhcmF0aW9uXCI7YnJlYWs7XG4gICAgICB9XG4gICAgfVxuICAgIG5vZGUuZGVjbGFyYXRpb24gPSBleHByO1xuICAgIHRoaXMuc2VtaWNvbG9uKCk7XG4gICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkV4cG9ydERlZmF1bHREZWNsYXJhdGlvblwiKTtcbiAgfVxuICBpZiAodGhpcy50b2sudHlwZS5rZXl3b3JkKSB7XG4gICAgbm9kZS5kZWNsYXJhdGlvbiA9IHRoaXMucGFyc2VTdGF0ZW1lbnQoKTtcbiAgICBub2RlLnNwZWNpZmllcnMgPSBbXTtcbiAgICBub2RlLnNvdXJjZSA9IG51bGw7XG4gIH0gZWxzZSB7XG4gICAgbm9kZS5kZWNsYXJhdGlvbiA9IG51bGw7XG4gICAgbm9kZS5zcGVjaWZpZXJzID0gdGhpcy5wYXJzZUV4cG9ydFNwZWNpZmllckxpc3QoKTtcbiAgICBub2RlLnNvdXJjZSA9IHRoaXMuZWF0Q29udGV4dHVhbChcImZyb21cIikgPyB0aGlzLnBhcnNlRXhwckF0b20oKSA6IG51bGw7XG4gICAgdGhpcy5zZW1pY29sb24oKTtcbiAgfVxuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiRXhwb3J0TmFtZWREZWNsYXJhdGlvblwiKTtcbn07XG5cbmxwLnBhcnNlSW1wb3J0ID0gZnVuY3Rpb24gKCkge1xuICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gIHRoaXMubmV4dCgpO1xuICBpZiAodGhpcy50b2sudHlwZSA9PT0gXy50b2tUeXBlcy5zdHJpbmcpIHtcbiAgICBub2RlLnNwZWNpZmllcnMgPSBbXTtcbiAgICBub2RlLnNvdXJjZSA9IHRoaXMucGFyc2VFeHByQXRvbSgpO1xuICAgIG5vZGUua2luZCA9IFwiXCI7XG4gIH0gZWxzZSB7XG4gICAgdmFyIGVsdCA9IHVuZGVmaW5lZDtcbiAgICBpZiAodGhpcy50b2sudHlwZSA9PT0gXy50b2tUeXBlcy5uYW1lICYmIHRoaXMudG9rLnZhbHVlICE9PSBcImZyb21cIikge1xuICAgICAgZWx0ID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgICAgIGVsdC5sb2NhbCA9IHRoaXMucGFyc2VJZGVudCgpO1xuICAgICAgdGhpcy5maW5pc2hOb2RlKGVsdCwgXCJJbXBvcnREZWZhdWx0U3BlY2lmaWVyXCIpO1xuICAgICAgdGhpcy5lYXQoXy50b2tUeXBlcy5jb21tYSk7XG4gICAgfVxuICAgIG5vZGUuc3BlY2lmaWVycyA9IHRoaXMucGFyc2VJbXBvcnRTcGVjaWZpZXJMaXN0KCk7XG4gICAgbm9kZS5zb3VyY2UgPSB0aGlzLmVhdENvbnRleHR1YWwoXCJmcm9tXCIpID8gdGhpcy5wYXJzZUV4cHJBdG9tKCkgOiB0aGlzLmR1bW15U3RyaW5nKCk7XG4gICAgaWYgKGVsdCkgbm9kZS5zcGVjaWZpZXJzLnVuc2hpZnQoZWx0KTtcbiAgfVxuICB0aGlzLnNlbWljb2xvbigpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiSW1wb3J0RGVjbGFyYXRpb25cIik7XG59O1xuXG5scC5wYXJzZUltcG9ydFNwZWNpZmllckxpc3QgPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBlbHRzID0gW107XG4gIGlmICh0aGlzLnRvay50eXBlID09PSBfLnRva1R5cGVzLnN0YXIpIHtcbiAgICB2YXIgZWx0ID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgICB0aGlzLm5leHQoKTtcbiAgICBpZiAodGhpcy5lYXRDb250ZXh0dWFsKFwiYXNcIikpIGVsdC5sb2NhbCA9IHRoaXMucGFyc2VJZGVudCgpO1xuICAgIGVsdHMucHVzaCh0aGlzLmZpbmlzaE5vZGUoZWx0LCBcIkltcG9ydE5hbWVzcGFjZVNwZWNpZmllclwiKSk7XG4gIH0gZWxzZSB7XG4gICAgdmFyIGluZGVudCA9IHRoaXMuY3VySW5kZW50LFxuICAgICAgICBsaW5lID0gdGhpcy5jdXJMaW5lU3RhcnQsXG4gICAgICAgIGNvbnRpbnVlZExpbmUgPSB0aGlzLm5leHRMaW5lU3RhcnQ7XG4gICAgdGhpcy5wdXNoQ3goKTtcbiAgICB0aGlzLmVhdChfLnRva1R5cGVzLmJyYWNlTCk7XG4gICAgaWYgKHRoaXMuY3VyTGluZVN0YXJ0ID4gY29udGludWVkTGluZSkgY29udGludWVkTGluZSA9IHRoaXMuY3VyTGluZVN0YXJ0O1xuICAgIHdoaWxlICghdGhpcy5jbG9zZXMoXy50b2tUeXBlcy5icmFjZVIsIGluZGVudCArICh0aGlzLmN1ckxpbmVTdGFydCA8PSBjb250aW51ZWRMaW5lID8gMSA6IDApLCBsaW5lKSkge1xuICAgICAgdmFyIGVsdCA9IHRoaXMuc3RhcnROb2RlKCk7XG4gICAgICBpZiAodGhpcy5lYXQoXy50b2tUeXBlcy5zdGFyKSkge1xuICAgICAgICBpZiAodGhpcy5lYXRDb250ZXh0dWFsKFwiYXNcIikpIGVsdC5sb2NhbCA9IHRoaXMucGFyc2VJZGVudCgpO1xuICAgICAgICB0aGlzLmZpbmlzaE5vZGUoZWx0LCBcIkltcG9ydE5hbWVzcGFjZVNwZWNpZmllclwiKTtcbiAgICAgIH0gZWxzZSB7XG4gICAgICAgIGlmICh0aGlzLmlzQ29udGV4dHVhbChcImZyb21cIikpIGJyZWFrO1xuICAgICAgICBlbHQuaW1wb3J0ZWQgPSB0aGlzLnBhcnNlSWRlbnQoKTtcbiAgICAgICAgaWYgKF9wYXJzZXV0aWwuaXNEdW1teShlbHQuaW1wb3J0ZWQpKSBicmVhaztcbiAgICAgICAgZWx0LmxvY2FsID0gdGhpcy5lYXRDb250ZXh0dWFsKFwiYXNcIikgPyB0aGlzLnBhcnNlSWRlbnQoKSA6IGVsdC5pbXBvcnRlZDtcbiAgICAgICAgdGhpcy5maW5pc2hOb2RlKGVsdCwgXCJJbXBvcnRTcGVjaWZpZXJcIik7XG4gICAgICB9XG4gICAgICBlbHRzLnB1c2goZWx0KTtcbiAgICAgIHRoaXMuZWF0KF8udG9rVHlwZXMuY29tbWEpO1xuICAgIH1cbiAgICB0aGlzLmVhdChfLnRva1R5cGVzLmJyYWNlUik7XG4gICAgdGhpcy5wb3BDeCgpO1xuICB9XG4gIHJldHVybiBlbHRzO1xufTtcblxubHAucGFyc2VFeHBvcnRTcGVjaWZpZXJMaXN0ID0gZnVuY3Rpb24gKCkge1xuICB2YXIgZWx0cyA9IFtdO1xuICB2YXIgaW5kZW50ID0gdGhpcy5jdXJJbmRlbnQsXG4gICAgICBsaW5lID0gdGhpcy5jdXJMaW5lU3RhcnQsXG4gICAgICBjb250aW51ZWRMaW5lID0gdGhpcy5uZXh0TGluZVN0YXJ0O1xuICB0aGlzLnB1c2hDeCgpO1xuICB0aGlzLmVhdChfLnRva1R5cGVzLmJyYWNlTCk7XG4gIGlmICh0aGlzLmN1ckxpbmVTdGFydCA+IGNvbnRpbnVlZExpbmUpIGNvbnRpbnVlZExpbmUgPSB0aGlzLmN1ckxpbmVTdGFydDtcbiAgd2hpbGUgKCF0aGlzLmNsb3NlcyhfLnRva1R5cGVzLmJyYWNlUiwgaW5kZW50ICsgKHRoaXMuY3VyTGluZVN0YXJ0IDw9IGNvbnRpbnVlZExpbmUgPyAxIDogMCksIGxpbmUpKSB7XG4gICAgaWYgKHRoaXMuaXNDb250ZXh0dWFsKFwiZnJvbVwiKSkgYnJlYWs7XG4gICAgdmFyIGVsdCA9IHRoaXMuc3RhcnROb2RlKCk7XG4gICAgZWx0LmxvY2FsID0gdGhpcy5wYXJzZUlkZW50KCk7XG4gICAgaWYgKF9wYXJzZXV0aWwuaXNEdW1teShlbHQubG9jYWwpKSBicmVhaztcbiAgICBlbHQuZXhwb3J0ZWQgPSB0aGlzLmVhdENvbnRleHR1YWwoXCJhc1wiKSA/IHRoaXMucGFyc2VJZGVudCgpIDogZWx0LmxvY2FsO1xuICAgIHRoaXMuZmluaXNoTm9kZShlbHQsIFwiRXhwb3J0U3BlY2lmaWVyXCIpO1xuICAgIGVsdHMucHVzaChlbHQpO1xuICAgIHRoaXMuZWF0KF8udG9rVHlwZXMuY29tbWEpO1xuICB9XG4gIHRoaXMuZWF0KF8udG9rVHlwZXMuYnJhY2VSKTtcbiAgdGhpcy5wb3BDeCgpO1xuICByZXR1cm4gZWx0cztcbn07XG5cbn0se1wiLi5cIjoxLFwiLi9wYXJzZXV0aWxcIjo0LFwiLi9zdGF0ZVwiOjV9XSw3OltmdW5jdGlvbihfZGVyZXFfLG1vZHVsZSxleHBvcnRzKXtcblwidXNlIHN0cmljdFwiO1xuXG52YXIgXyA9IF9kZXJlcV8oXCIuLlwiKTtcblxudmFyIF9zdGF0ZSA9IF9kZXJlcV8oXCIuL3N0YXRlXCIpO1xuXG52YXIgbHAgPSBfc3RhdGUuTG9vc2VQYXJzZXIucHJvdG90eXBlO1xuXG5mdW5jdGlvbiBpc1NwYWNlKGNoKSB7XG4gIHJldHVybiBjaCA8IDE0ICYmIGNoID4gOCB8fCBjaCA9PT0gMzIgfHwgY2ggPT09IDE2MCB8fCBfLmlzTmV3TGluZShjaCk7XG59XG5cbmxwLm5leHQgPSBmdW5jdGlvbiAoKSB7XG4gIHRoaXMubGFzdCA9IHRoaXMudG9rO1xuICBpZiAodGhpcy5haGVhZC5sZW5ndGgpIHRoaXMudG9rID0gdGhpcy5haGVhZC5zaGlmdCgpO2Vsc2UgdGhpcy50b2sgPSB0aGlzLnJlYWRUb2tlbigpO1xuXG4gIGlmICh0aGlzLnRvay5zdGFydCA+PSB0aGlzLm5leHRMaW5lU3RhcnQpIHtcbiAgICB3aGlsZSAodGhpcy50b2suc3RhcnQgPj0gdGhpcy5uZXh0TGluZVN0YXJ0KSB7XG4gICAgICB0aGlzLmN1ckxpbmVTdGFydCA9IHRoaXMubmV4dExpbmVTdGFydDtcbiAgICAgIHRoaXMubmV4dExpbmVTdGFydCA9IHRoaXMubGluZUVuZCh0aGlzLmN1ckxpbmVTdGFydCkgKyAxO1xuICAgIH1cbiAgICB0aGlzLmN1ckluZGVudCA9IHRoaXMuaW5kZW50YXRpb25BZnRlcih0aGlzLmN1ckxpbmVTdGFydCk7XG4gIH1cbn07XG5cbmxwLnJlYWRUb2tlbiA9IGZ1bmN0aW9uICgpIHtcbiAgZm9yICg7Oykge1xuICAgIHRyeSB7XG4gICAgICB0aGlzLnRva3MubmV4dCgpO1xuICAgICAgaWYgKHRoaXMudG9rcy50eXBlID09PSBfLnRva1R5cGVzLmRvdCAmJiB0aGlzLmlucHV0LnN1YnN0cih0aGlzLnRva3MuZW5kLCAxKSA9PT0gXCIuXCIgJiYgdGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYpIHtcbiAgICAgICAgdGhpcy50b2tzLmVuZCsrO1xuICAgICAgICB0aGlzLnRva3MudHlwZSA9IF8udG9rVHlwZXMuZWxsaXBzaXM7XG4gICAgICB9XG4gICAgICByZXR1cm4gbmV3IF8uVG9rZW4odGhpcy50b2tzKTtcbiAgICB9IGNhdGNoIChlKSB7XG4gICAgICBpZiAoIShlIGluc3RhbmNlb2YgU3ludGF4RXJyb3IpKSB0aHJvdyBlO1xuXG4gICAgICAvLyBUcnkgdG8gc2tpcCBzb21lIHRleHQsIGJhc2VkIG9uIHRoZSBlcnJvciBtZXNzYWdlLCBhbmQgdGhlbiBjb250aW51ZVxuICAgICAgdmFyIG1zZyA9IGUubWVzc2FnZSxcbiAgICAgICAgICBwb3MgPSBlLnJhaXNlZEF0LFxuICAgICAgICAgIHJlcGxhY2UgPSB0cnVlO1xuICAgICAgaWYgKC91bnRlcm1pbmF0ZWQvaS50ZXN0KG1zZykpIHtcbiAgICAgICAgcG9zID0gdGhpcy5saW5lRW5kKGUucG9zICsgMSk7XG4gICAgICAgIGlmICgvc3RyaW5nLy50ZXN0KG1zZykpIHtcbiAgICAgICAgICByZXBsYWNlID0geyBzdGFydDogZS5wb3MsIGVuZDogcG9zLCB0eXBlOiBfLnRva1R5cGVzLnN0cmluZywgdmFsdWU6IHRoaXMuaW5wdXQuc2xpY2UoZS5wb3MgKyAxLCBwb3MpIH07XG4gICAgICAgIH0gZWxzZSBpZiAoL3JlZ3VsYXIgZXhwci9pLnRlc3QobXNnKSkge1xuICAgICAgICAgIHZhciByZSA9IHRoaXMuaW5wdXQuc2xpY2UoZS5wb3MsIHBvcyk7XG4gICAgICAgICAgdHJ5IHtcbiAgICAgICAgICAgIHJlID0gbmV3IFJlZ0V4cChyZSk7XG4gICAgICAgICAgfSBjYXRjaCAoZSkge31cbiAgICAgICAgICByZXBsYWNlID0geyBzdGFydDogZS5wb3MsIGVuZDogcG9zLCB0eXBlOiBfLnRva1R5cGVzLnJlZ2V4cCwgdmFsdWU6IHJlIH07XG4gICAgICAgIH0gZWxzZSBpZiAoL3RlbXBsYXRlLy50ZXN0KG1zZykpIHtcbiAgICAgICAgICByZXBsYWNlID0geyBzdGFydDogZS5wb3MsIGVuZDogcG9zLFxuICAgICAgICAgICAgdHlwZTogXy50b2tUeXBlcy50ZW1wbGF0ZSxcbiAgICAgICAgICAgIHZhbHVlOiB0aGlzLmlucHV0LnNsaWNlKGUucG9zLCBwb3MpIH07XG4gICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgcmVwbGFjZSA9IGZhbHNlO1xuICAgICAgICB9XG4gICAgICB9IGVsc2UgaWYgKC9pbnZhbGlkICh1bmljb2RlfHJlZ2V4cHxudW1iZXIpfGV4cGVjdGluZyB1bmljb2RlfG9jdGFsIGxpdGVyYWx8aXMgcmVzZXJ2ZWR8ZGlyZWN0bHkgYWZ0ZXIgbnVtYmVyfGV4cGVjdGVkIG51bWJlciBpbiByYWRpeC9pLnRlc3QobXNnKSkge1xuICAgICAgICB3aGlsZSAocG9zIDwgdGhpcy5pbnB1dC5sZW5ndGggJiYgIWlzU3BhY2UodGhpcy5pbnB1dC5jaGFyQ29kZUF0KHBvcykpKSArK3BvcztcbiAgICAgIH0gZWxzZSBpZiAoL2NoYXJhY3RlciBlc2NhcGV8ZXhwZWN0ZWQgaGV4YWRlY2ltYWwvaS50ZXN0KG1zZykpIHtcbiAgICAgICAgd2hpbGUgKHBvcyA8IHRoaXMuaW5wdXQubGVuZ3RoKSB7XG4gICAgICAgICAgdmFyIGNoID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHBvcysrKTtcbiAgICAgICAgICBpZiAoY2ggPT09IDM0IHx8IGNoID09PSAzOSB8fCBfLmlzTmV3TGluZShjaCkpIGJyZWFrO1xuICAgICAgICB9XG4gICAgICB9IGVsc2UgaWYgKC91bmV4cGVjdGVkIGNoYXJhY3Rlci9pLnRlc3QobXNnKSkge1xuICAgICAgICBwb3MrKztcbiAgICAgICAgcmVwbGFjZSA9IGZhbHNlO1xuICAgICAgfSBlbHNlIGlmICgvcmVndWxhciBleHByZXNzaW9uL2kudGVzdChtc2cpKSB7XG4gICAgICAgIHJlcGxhY2UgPSB0cnVlO1xuICAgICAgfSBlbHNlIHtcbiAgICAgICAgdGhyb3cgZTtcbiAgICAgIH1cbiAgICAgIHRoaXMucmVzZXRUbyhwb3MpO1xuICAgICAgaWYgKHJlcGxhY2UgPT09IHRydWUpIHJlcGxhY2UgPSB7IHN0YXJ0OiBwb3MsIGVuZDogcG9zLCB0eXBlOiBfLnRva1R5cGVzLm5hbWUsIHZhbHVlOiBcIuKcllwiIH07XG4gICAgICBpZiAocmVwbGFjZSkge1xuICAgICAgICBpZiAodGhpcy5vcHRpb25zLmxvY2F0aW9ucykgcmVwbGFjZS5sb2MgPSBuZXcgXy5Tb3VyY2VMb2NhdGlvbih0aGlzLnRva3MsIF8uZ2V0TGluZUluZm8odGhpcy5pbnB1dCwgcmVwbGFjZS5zdGFydCksIF8uZ2V0TGluZUluZm8odGhpcy5pbnB1dCwgcmVwbGFjZS5lbmQpKTtcbiAgICAgICAgcmV0dXJuIHJlcGxhY2U7XG4gICAgICB9XG4gICAgfVxuICB9XG59O1xuXG5scC5yZXNldFRvID0gZnVuY3Rpb24gKHBvcykge1xuICB0aGlzLnRva3MucG9zID0gcG9zO1xuICB2YXIgY2ggPSB0aGlzLmlucHV0LmNoYXJBdChwb3MgLSAxKTtcbiAgdGhpcy50b2tzLmV4cHJBbGxvd2VkID0gIWNoIHx8IC9bXFxbXFx7XFwoLDs6P1xcLyo9K1xcLX4hfCYlXjw+XS8udGVzdChjaCkgfHwgL1tlbndmZF0vLnRlc3QoY2gpICYmIC9cXGIoa2V5d29yZHN8Y2FzZXxlbHNlfHJldHVybnx0aHJvd3xuZXd8aW58KGluc3RhbmNlfHR5cGUpb2Z8ZGVsZXRlfHZvaWQpJC8udGVzdCh0aGlzLmlucHV0LnNsaWNlKHBvcyAtIDEwLCBwb3MpKTtcblxuICBpZiAodGhpcy5vcHRpb25zLmxvY2F0aW9ucykge1xuICAgIHRoaXMudG9rcy5jdXJMaW5lID0gMTtcbiAgICB0aGlzLnRva3MubGluZVN0YXJ0ID0gXy5saW5lQnJlYWtHLmxhc3RJbmRleCA9IDA7XG4gICAgdmFyIG1hdGNoID0gdW5kZWZpbmVkO1xuICAgIHdoaWxlICgobWF0Y2ggPSBfLmxpbmVCcmVha0cuZXhlYyh0aGlzLmlucHV0KSkgJiYgbWF0Y2guaW5kZXggPCBwb3MpIHtcbiAgICAgICsrdGhpcy50b2tzLmN1ckxpbmU7XG4gICAgICB0aGlzLnRva3MubGluZVN0YXJ0ID0gbWF0Y2guaW5kZXggKyBtYXRjaFswXS5sZW5ndGg7XG4gICAgfVxuICB9XG59O1xuXG5scC5sb29rQWhlYWQgPSBmdW5jdGlvbiAobikge1xuICB3aGlsZSAobiA+IHRoaXMuYWhlYWQubGVuZ3RoKSB0aGlzLmFoZWFkLnB1c2godGhpcy5yZWFkVG9rZW4oKSk7XG4gIHJldHVybiB0aGlzLmFoZWFkW24gLSAxXTtcbn07XG5cbn0se1wiLi5cIjoxLFwiLi9zdGF0ZVwiOjV9XX0se30sWzNdKSgzKVxufSk7IiwiKGZ1bmN0aW9uKGYpe2lmKHR5cGVvZiBleHBvcnRzPT09XCJvYmplY3RcIiYmdHlwZW9mIG1vZHVsZSE9PVwidW5kZWZpbmVkXCIpe21vZHVsZS5leHBvcnRzPWYoKX1lbHNlIGlmKHR5cGVvZiBkZWZpbmU9PT1cImZ1bmN0aW9uXCImJmRlZmluZS5hbWQpe2RlZmluZShbXSxmKX1lbHNle3ZhciBnO2lmKHR5cGVvZiB3aW5kb3chPT1cInVuZGVmaW5lZFwiKXtnPXdpbmRvd31lbHNlIGlmKHR5cGVvZiBnbG9iYWwhPT1cInVuZGVmaW5lZFwiKXtnPWdsb2JhbH1lbHNlIGlmKHR5cGVvZiBzZWxmIT09XCJ1bmRlZmluZWRcIil7Zz1zZWxmfWVsc2V7Zz10aGlzfShnLmFjb3JuIHx8IChnLmFjb3JuID0ge30pKS53YWxrID0gZigpfX0pKGZ1bmN0aW9uKCl7dmFyIGRlZmluZSxtb2R1bGUsZXhwb3J0cztyZXR1cm4gKGZ1bmN0aW9uIGUodCxuLHIpe2Z1bmN0aW9uIHMobyx1KXtpZighbltvXSl7aWYoIXRbb10pe3ZhciBhPXR5cGVvZiByZXF1aXJlPT1cImZ1bmN0aW9uXCImJnJlcXVpcmU7aWYoIXUmJmEpcmV0dXJuIGEobywhMCk7aWYoaSlyZXR1cm4gaShvLCEwKTt2YXIgZj1uZXcgRXJyb3IoXCJDYW5ub3QgZmluZCBtb2R1bGUgJ1wiK28rXCInXCIpO3Rocm93IGYuY29kZT1cIk1PRFVMRV9OT1RfRk9VTkRcIixmfXZhciBsPW5bb109e2V4cG9ydHM6e319O3Rbb11bMF0uY2FsbChsLmV4cG9ydHMsZnVuY3Rpb24oZSl7dmFyIG49dFtvXVsxXVtlXTtyZXR1cm4gcyhuP246ZSl9LGwsbC5leHBvcnRzLGUsdCxuLHIpfXJldHVybiBuW29dLmV4cG9ydHN9dmFyIGk9dHlwZW9mIHJlcXVpcmU9PVwiZnVuY3Rpb25cIiYmcmVxdWlyZTtmb3IodmFyIG89MDtvPHIubGVuZ3RoO28rKylzKHJbb10pO3JldHVybiBzfSkoezE6W2Z1bmN0aW9uKF9kZXJlcV8sbW9kdWxlLGV4cG9ydHMpe1xuLy8gQVNUIHdhbGtlciBtb2R1bGUgZm9yIE1vemlsbGEgUGFyc2VyIEFQSSBjb21wYXRpYmxlIHRyZWVzXG5cbi8vIEEgc2ltcGxlIHdhbGsgaXMgb25lIHdoZXJlIHlvdSBzaW1wbHkgc3BlY2lmeSBjYWxsYmFja3MgdG8gYmVcbi8vIGNhbGxlZCBvbiBzcGVjaWZpYyBub2Rlcy4gVGhlIGxhc3QgdHdvIGFyZ3VtZW50cyBhcmUgb3B0aW9uYWwuIEFcbi8vIHNpbXBsZSB1c2Ugd291bGQgYmVcbi8vXG4vLyAgICAgd2Fsay5zaW1wbGUobXlUcmVlLCB7XG4vLyAgICAgICAgIEV4cHJlc3Npb246IGZ1bmN0aW9uKG5vZGUpIHsgLi4uIH1cbi8vICAgICB9KTtcbi8vXG4vLyB0byBkbyBzb21ldGhpbmcgd2l0aCBhbGwgZXhwcmVzc2lvbnMuIEFsbCBQYXJzZXIgQVBJIG5vZGUgdHlwZXNcbi8vIGNhbiBiZSB1c2VkIHRvIGlkZW50aWZ5IG5vZGUgdHlwZXMsIGFzIHdlbGwgYXMgRXhwcmVzc2lvbixcbi8vIFN0YXRlbWVudCwgYW5kIFNjb3BlQm9keSwgd2hpY2ggZGVub3RlIGNhdGVnb3JpZXMgb2Ygbm9kZXMuXG4vL1xuLy8gVGhlIGJhc2UgYXJndW1lbnQgY2FuIGJlIHVzZWQgdG8gcGFzcyBhIGN1c3RvbSAocmVjdXJzaXZlKVxuLy8gd2Fsa2VyLCBhbmQgc3RhdGUgY2FuIGJlIHVzZWQgdG8gZ2l2ZSB0aGlzIHdhbGtlZCBhbiBpbml0aWFsXG4vLyBzdGF0ZS5cblxuXCJ1c2Ugc3RyaWN0XCI7XG5cbmV4cG9ydHMuX19lc01vZHVsZSA9IHRydWU7XG5leHBvcnRzLnNpbXBsZSA9IHNpbXBsZTtcbmV4cG9ydHMuYW5jZXN0b3IgPSBhbmNlc3RvcjtcbmV4cG9ydHMucmVjdXJzaXZlID0gcmVjdXJzaXZlO1xuZXhwb3J0cy5maW5kTm9kZUF0ID0gZmluZE5vZGVBdDtcbmV4cG9ydHMuZmluZE5vZGVBcm91bmQgPSBmaW5kTm9kZUFyb3VuZDtcbmV4cG9ydHMuZmluZE5vZGVBZnRlciA9IGZpbmROb2RlQWZ0ZXI7XG5leHBvcnRzLmZpbmROb2RlQmVmb3JlID0gZmluZE5vZGVCZWZvcmU7XG5leHBvcnRzLm1ha2UgPSBtYWtlO1xuXG5mdW5jdGlvbiBfY2xhc3NDYWxsQ2hlY2soaW5zdGFuY2UsIENvbnN0cnVjdG9yKSB7IGlmICghKGluc3RhbmNlIGluc3RhbmNlb2YgQ29uc3RydWN0b3IpKSB7IHRocm93IG5ldyBUeXBlRXJyb3IoXCJDYW5ub3QgY2FsbCBhIGNsYXNzIGFzIGEgZnVuY3Rpb25cIik7IH0gfVxuXG5mdW5jdGlvbiBzaW1wbGUobm9kZSwgdmlzaXRvcnMsIGJhc2UsIHN0YXRlLCBvdmVycmlkZSkge1xuICBpZiAoIWJhc2UpIGJhc2UgPSBleHBvcnRzLmJhc2U7KGZ1bmN0aW9uIGMobm9kZSwgc3QsIG92ZXJyaWRlKSB7XG4gICAgdmFyIHR5cGUgPSBvdmVycmlkZSB8fCBub2RlLnR5cGUsXG4gICAgICAgIGZvdW5kID0gdmlzaXRvcnNbdHlwZV07XG4gICAgYmFzZVt0eXBlXShub2RlLCBzdCwgYyk7XG4gICAgaWYgKGZvdW5kKSBmb3VuZChub2RlLCBzdCk7XG4gIH0pKG5vZGUsIHN0YXRlLCBvdmVycmlkZSk7XG59XG5cbi8vIEFuIGFuY2VzdG9yIHdhbGsgYnVpbGRzIHVwIGFuIGFycmF5IG9mIGFuY2VzdG9yIG5vZGVzIChpbmNsdWRpbmdcbi8vIHRoZSBjdXJyZW50IG5vZGUpIGFuZCBwYXNzZXMgdGhlbSB0byB0aGUgY2FsbGJhY2sgYXMgdGhlIHN0YXRlIHBhcmFtZXRlci5cblxuZnVuY3Rpb24gYW5jZXN0b3Iobm9kZSwgdmlzaXRvcnMsIGJhc2UsIHN0YXRlKSB7XG4gIGlmICghYmFzZSkgYmFzZSA9IGV4cG9ydHMuYmFzZTtcbiAgaWYgKCFzdGF0ZSkgc3RhdGUgPSBbXTsoZnVuY3Rpb24gYyhub2RlLCBzdCwgb3ZlcnJpZGUpIHtcbiAgICB2YXIgdHlwZSA9IG92ZXJyaWRlIHx8IG5vZGUudHlwZSxcbiAgICAgICAgZm91bmQgPSB2aXNpdG9yc1t0eXBlXTtcbiAgICBpZiAobm9kZSAhPSBzdFtzdC5sZW5ndGggLSAxXSkge1xuICAgICAgc3QgPSBzdC5zbGljZSgpO1xuICAgICAgc3QucHVzaChub2RlKTtcbiAgICB9XG4gICAgYmFzZVt0eXBlXShub2RlLCBzdCwgYyk7XG4gICAgaWYgKGZvdW5kKSBmb3VuZChub2RlLCBzdCk7XG4gIH0pKG5vZGUsIHN0YXRlKTtcbn1cblxuLy8gQSByZWN1cnNpdmUgd2FsayBpcyBvbmUgd2hlcmUgeW91ciBmdW5jdGlvbnMgb3ZlcnJpZGUgdGhlIGRlZmF1bHRcbi8vIHdhbGtlcnMuIFRoZXkgY2FuIG1vZGlmeSBhbmQgcmVwbGFjZSB0aGUgc3RhdGUgcGFyYW1ldGVyIHRoYXQnc1xuLy8gdGhyZWFkZWQgdGhyb3VnaCB0aGUgd2FsaywgYW5kIGNhbiBvcHQgaG93IGFuZCB3aGV0aGVyIHRvIHdhbGtcbi8vIHRoZWlyIGNoaWxkIG5vZGVzIChieSBjYWxsaW5nIHRoZWlyIHRoaXJkIGFyZ3VtZW50IG9uIHRoZXNlXG4vLyBub2RlcykuXG5cbmZ1bmN0aW9uIHJlY3Vyc2l2ZShub2RlLCBzdGF0ZSwgZnVuY3MsIGJhc2UsIG92ZXJyaWRlKSB7XG4gIHZhciB2aXNpdG9yID0gZnVuY3MgPyBleHBvcnRzLm1ha2UoZnVuY3MsIGJhc2UpIDogYmFzZTsoZnVuY3Rpb24gYyhub2RlLCBzdCwgb3ZlcnJpZGUpIHtcbiAgICB2aXNpdG9yW292ZXJyaWRlIHx8IG5vZGUudHlwZV0obm9kZSwgc3QsIGMpO1xuICB9KShub2RlLCBzdGF0ZSwgb3ZlcnJpZGUpO1xufVxuXG5mdW5jdGlvbiBtYWtlVGVzdCh0ZXN0KSB7XG4gIGlmICh0eXBlb2YgdGVzdCA9PSBcInN0cmluZ1wiKSByZXR1cm4gZnVuY3Rpb24gKHR5cGUpIHtcbiAgICByZXR1cm4gdHlwZSA9PSB0ZXN0O1xuICB9O2Vsc2UgaWYgKCF0ZXN0KSByZXR1cm4gZnVuY3Rpb24gKCkge1xuICAgIHJldHVybiB0cnVlO1xuICB9O2Vsc2UgcmV0dXJuIHRlc3Q7XG59XG5cbnZhciBGb3VuZCA9IGZ1bmN0aW9uIEZvdW5kKG5vZGUsIHN0YXRlKSB7XG4gIF9jbGFzc0NhbGxDaGVjayh0aGlzLCBGb3VuZCk7XG5cbiAgdGhpcy5ub2RlID0gbm9kZTt0aGlzLnN0YXRlID0gc3RhdGU7XG59O1xuXG4vLyBGaW5kIGEgbm9kZSB3aXRoIGEgZ2l2ZW4gc3RhcnQsIGVuZCwgYW5kIHR5cGUgKGFsbCBhcmUgb3B0aW9uYWwsXG4vLyBudWxsIGNhbiBiZSB1c2VkIGFzIHdpbGRjYXJkKS4gUmV0dXJucyBhIHtub2RlLCBzdGF0ZX0gb2JqZWN0LCBvclxuLy8gdW5kZWZpbmVkIHdoZW4gaXQgZG9lc24ndCBmaW5kIGEgbWF0Y2hpbmcgbm9kZS5cblxuZnVuY3Rpb24gZmluZE5vZGVBdChub2RlLCBzdGFydCwgZW5kLCB0ZXN0LCBiYXNlLCBzdGF0ZSkge1xuICB0ZXN0ID0gbWFrZVRlc3QodGVzdCk7XG4gIGlmICghYmFzZSkgYmFzZSA9IGV4cG9ydHMuYmFzZTtcbiAgdHJ5IHtcbiAgICA7KGZ1bmN0aW9uIGMobm9kZSwgc3QsIG92ZXJyaWRlKSB7XG4gICAgICB2YXIgdHlwZSA9IG92ZXJyaWRlIHx8IG5vZGUudHlwZTtcbiAgICAgIGlmICgoc3RhcnQgPT0gbnVsbCB8fCBub2RlLnN0YXJ0IDw9IHN0YXJ0KSAmJiAoZW5kID09IG51bGwgfHwgbm9kZS5lbmQgPj0gZW5kKSkgYmFzZVt0eXBlXShub2RlLCBzdCwgYyk7XG4gICAgICBpZiAoKHN0YXJ0ID09IG51bGwgfHwgbm9kZS5zdGFydCA9PSBzdGFydCkgJiYgKGVuZCA9PSBudWxsIHx8IG5vZGUuZW5kID09IGVuZCkgJiYgdGVzdCh0eXBlLCBub2RlKSkgdGhyb3cgbmV3IEZvdW5kKG5vZGUsIHN0KTtcbiAgICB9KShub2RlLCBzdGF0ZSk7XG4gIH0gY2F0Y2ggKGUpIHtcbiAgICBpZiAoZSBpbnN0YW5jZW9mIEZvdW5kKSByZXR1cm4gZTtcbiAgICB0aHJvdyBlO1xuICB9XG59XG5cbi8vIEZpbmQgdGhlIGlubmVybW9zdCBub2RlIG9mIGEgZ2l2ZW4gdHlwZSB0aGF0IGNvbnRhaW5zIHRoZSBnaXZlblxuLy8gcG9zaXRpb24uIEludGVyZmFjZSBzaW1pbGFyIHRvIGZpbmROb2RlQXQuXG5cbmZ1bmN0aW9uIGZpbmROb2RlQXJvdW5kKG5vZGUsIHBvcywgdGVzdCwgYmFzZSwgc3RhdGUpIHtcbiAgdGVzdCA9IG1ha2VUZXN0KHRlc3QpO1xuICBpZiAoIWJhc2UpIGJhc2UgPSBleHBvcnRzLmJhc2U7XG4gIHRyeSB7XG4gICAgOyhmdW5jdGlvbiBjKG5vZGUsIHN0LCBvdmVycmlkZSkge1xuICAgICAgdmFyIHR5cGUgPSBvdmVycmlkZSB8fCBub2RlLnR5cGU7XG4gICAgICBpZiAobm9kZS5zdGFydCA+IHBvcyB8fCBub2RlLmVuZCA8IHBvcykgcmV0dXJuO1xuICAgICAgYmFzZVt0eXBlXShub2RlLCBzdCwgYyk7XG4gICAgICBpZiAodGVzdCh0eXBlLCBub2RlKSkgdGhyb3cgbmV3IEZvdW5kKG5vZGUsIHN0KTtcbiAgICB9KShub2RlLCBzdGF0ZSk7XG4gIH0gY2F0Y2ggKGUpIHtcbiAgICBpZiAoZSBpbnN0YW5jZW9mIEZvdW5kKSByZXR1cm4gZTtcbiAgICB0aHJvdyBlO1xuICB9XG59XG5cbi8vIEZpbmQgdGhlIG91dGVybW9zdCBtYXRjaGluZyBub2RlIGFmdGVyIGEgZ2l2ZW4gcG9zaXRpb24uXG5cbmZ1bmN0aW9uIGZpbmROb2RlQWZ0ZXIobm9kZSwgcG9zLCB0ZXN0LCBiYXNlLCBzdGF0ZSkge1xuICB0ZXN0ID0gbWFrZVRlc3QodGVzdCk7XG4gIGlmICghYmFzZSkgYmFzZSA9IGV4cG9ydHMuYmFzZTtcbiAgdHJ5IHtcbiAgICA7KGZ1bmN0aW9uIGMobm9kZSwgc3QsIG92ZXJyaWRlKSB7XG4gICAgICBpZiAobm9kZS5lbmQgPCBwb3MpIHJldHVybjtcbiAgICAgIHZhciB0eXBlID0gb3ZlcnJpZGUgfHwgbm9kZS50eXBlO1xuICAgICAgaWYgKG5vZGUuc3RhcnQgPj0gcG9zICYmIHRlc3QodHlwZSwgbm9kZSkpIHRocm93IG5ldyBGb3VuZChub2RlLCBzdCk7XG4gICAgICBiYXNlW3R5cGVdKG5vZGUsIHN0LCBjKTtcbiAgICB9KShub2RlLCBzdGF0ZSk7XG4gIH0gY2F0Y2ggKGUpIHtcbiAgICBpZiAoZSBpbnN0YW5jZW9mIEZvdW5kKSByZXR1cm4gZTtcbiAgICB0aHJvdyBlO1xuICB9XG59XG5cbi8vIEZpbmQgdGhlIG91dGVybW9zdCBtYXRjaGluZyBub2RlIGJlZm9yZSBhIGdpdmVuIHBvc2l0aW9uLlxuXG5mdW5jdGlvbiBmaW5kTm9kZUJlZm9yZShub2RlLCBwb3MsIHRlc3QsIGJhc2UsIHN0YXRlKSB7XG4gIHRlc3QgPSBtYWtlVGVzdCh0ZXN0KTtcbiAgaWYgKCFiYXNlKSBiYXNlID0gZXhwb3J0cy5iYXNlO1xuICB2YXIgbWF4ID0gdW5kZWZpbmVkOyhmdW5jdGlvbiBjKG5vZGUsIHN0LCBvdmVycmlkZSkge1xuICAgIGlmIChub2RlLnN0YXJ0ID4gcG9zKSByZXR1cm47XG4gICAgdmFyIHR5cGUgPSBvdmVycmlkZSB8fCBub2RlLnR5cGU7XG4gICAgaWYgKG5vZGUuZW5kIDw9IHBvcyAmJiAoIW1heCB8fCBtYXgubm9kZS5lbmQgPCBub2RlLmVuZCkgJiYgdGVzdCh0eXBlLCBub2RlKSkgbWF4ID0gbmV3IEZvdW5kKG5vZGUsIHN0KTtcbiAgICBiYXNlW3R5cGVdKG5vZGUsIHN0LCBjKTtcbiAgfSkobm9kZSwgc3RhdGUpO1xuICByZXR1cm4gbWF4O1xufVxuXG4vLyBVc2VkIHRvIGNyZWF0ZSBhIGN1c3RvbSB3YWxrZXIuIFdpbGwgZmlsbCBpbiBhbGwgbWlzc2luZyBub2RlXG4vLyB0eXBlIHByb3BlcnRpZXMgd2l0aCB0aGUgZGVmYXVsdHMuXG5cbmZ1bmN0aW9uIG1ha2UoZnVuY3MsIGJhc2UpIHtcbiAgaWYgKCFiYXNlKSBiYXNlID0gZXhwb3J0cy5iYXNlO1xuICB2YXIgdmlzaXRvciA9IHt9O1xuICBmb3IgKHZhciB0eXBlIGluIGJhc2UpIHZpc2l0b3JbdHlwZV0gPSBiYXNlW3R5cGVdO1xuICBmb3IgKHZhciB0eXBlIGluIGZ1bmNzKSB2aXNpdG9yW3R5cGVdID0gZnVuY3NbdHlwZV07XG4gIHJldHVybiB2aXNpdG9yO1xufVxuXG5mdW5jdGlvbiBza2lwVGhyb3VnaChub2RlLCBzdCwgYykge1xuICBjKG5vZGUsIHN0KTtcbn1cbmZ1bmN0aW9uIGlnbm9yZShfbm9kZSwgX3N0LCBfYykge31cblxuLy8gTm9kZSB3YWxrZXJzLlxuXG52YXIgYmFzZSA9IHt9O1xuXG5leHBvcnRzLmJhc2UgPSBiYXNlO1xuYmFzZS5Qcm9ncmFtID0gYmFzZS5CbG9ja1N0YXRlbWVudCA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBmb3IgKHZhciBpID0gMDsgaSA8IG5vZGUuYm9keS5sZW5ndGg7ICsraSkge1xuICAgIGMobm9kZS5ib2R5W2ldLCBzdCwgXCJTdGF0ZW1lbnRcIik7XG4gIH1cbn07XG5iYXNlLlN0YXRlbWVudCA9IHNraXBUaHJvdWdoO1xuYmFzZS5FbXB0eVN0YXRlbWVudCA9IGlnbm9yZTtcbmJhc2UuRXhwcmVzc2lvblN0YXRlbWVudCA9IGJhc2UuUGFyZW50aGVzaXplZEV4cHJlc3Npb24gPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgcmV0dXJuIGMobm9kZS5leHByZXNzaW9uLCBzdCwgXCJFeHByZXNzaW9uXCIpO1xufTtcbmJhc2UuSWZTdGF0ZW1lbnQgPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgYyhub2RlLnRlc3QsIHN0LCBcIkV4cHJlc3Npb25cIik7XG4gIGMobm9kZS5jb25zZXF1ZW50LCBzdCwgXCJTdGF0ZW1lbnRcIik7XG4gIGlmIChub2RlLmFsdGVybmF0ZSkgYyhub2RlLmFsdGVybmF0ZSwgc3QsIFwiU3RhdGVtZW50XCIpO1xufTtcbmJhc2UuTGFiZWxlZFN0YXRlbWVudCA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICByZXR1cm4gYyhub2RlLmJvZHksIHN0LCBcIlN0YXRlbWVudFwiKTtcbn07XG5iYXNlLkJyZWFrU3RhdGVtZW50ID0gYmFzZS5Db250aW51ZVN0YXRlbWVudCA9IGlnbm9yZTtcbmJhc2UuV2l0aFN0YXRlbWVudCA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBjKG5vZGUub2JqZWN0LCBzdCwgXCJFeHByZXNzaW9uXCIpO1xuICBjKG5vZGUuYm9keSwgc3QsIFwiU3RhdGVtZW50XCIpO1xufTtcbmJhc2UuU3dpdGNoU3RhdGVtZW50ID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIGMobm9kZS5kaXNjcmltaW5hbnQsIHN0LCBcIkV4cHJlc3Npb25cIik7XG4gIGZvciAodmFyIGkgPSAwOyBpIDwgbm9kZS5jYXNlcy5sZW5ndGg7ICsraSkge1xuICAgIHZhciBjcyA9IG5vZGUuY2FzZXNbaV07XG4gICAgaWYgKGNzLnRlc3QpIGMoY3MudGVzdCwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbiAgICBmb3IgKHZhciBqID0gMDsgaiA8IGNzLmNvbnNlcXVlbnQubGVuZ3RoOyArK2opIHtcbiAgICAgIGMoY3MuY29uc2VxdWVudFtqXSwgc3QsIFwiU3RhdGVtZW50XCIpO1xuICAgIH1cbiAgfVxufTtcbmJhc2UuUmV0dXJuU3RhdGVtZW50ID0gYmFzZS5ZaWVsZEV4cHJlc3Npb24gPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgaWYgKG5vZGUuYXJndW1lbnQpIGMobm9kZS5hcmd1bWVudCwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbn07XG5iYXNlLlRocm93U3RhdGVtZW50ID0gYmFzZS5TcHJlYWRFbGVtZW50ID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIHJldHVybiBjKG5vZGUuYXJndW1lbnQsIHN0LCBcIkV4cHJlc3Npb25cIik7XG59O1xuYmFzZS5UcnlTdGF0ZW1lbnQgPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgYyhub2RlLmJsb2NrLCBzdCwgXCJTdGF0ZW1lbnRcIik7XG4gIGlmIChub2RlLmhhbmRsZXIpIHtcbiAgICBjKG5vZGUuaGFuZGxlci5wYXJhbSwgc3QsIFwiUGF0dGVyblwiKTtcbiAgICBjKG5vZGUuaGFuZGxlci5ib2R5LCBzdCwgXCJTY29wZUJvZHlcIik7XG4gIH1cbiAgaWYgKG5vZGUuZmluYWxpemVyKSBjKG5vZGUuZmluYWxpemVyLCBzdCwgXCJTdGF0ZW1lbnRcIik7XG59O1xuYmFzZS5XaGlsZVN0YXRlbWVudCA9IGJhc2UuRG9XaGlsZVN0YXRlbWVudCA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBjKG5vZGUudGVzdCwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbiAgYyhub2RlLmJvZHksIHN0LCBcIlN0YXRlbWVudFwiKTtcbn07XG5iYXNlLkZvclN0YXRlbWVudCA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBpZiAobm9kZS5pbml0KSBjKG5vZGUuaW5pdCwgc3QsIFwiRm9ySW5pdFwiKTtcbiAgaWYgKG5vZGUudGVzdCkgYyhub2RlLnRlc3QsIHN0LCBcIkV4cHJlc3Npb25cIik7XG4gIGlmIChub2RlLnVwZGF0ZSkgYyhub2RlLnVwZGF0ZSwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbiAgYyhub2RlLmJvZHksIHN0LCBcIlN0YXRlbWVudFwiKTtcbn07XG5iYXNlLkZvckluU3RhdGVtZW50ID0gYmFzZS5Gb3JPZlN0YXRlbWVudCA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBjKG5vZGUubGVmdCwgc3QsIFwiRm9ySW5pdFwiKTtcbiAgYyhub2RlLnJpZ2h0LCBzdCwgXCJFeHByZXNzaW9uXCIpO1xuICBjKG5vZGUuYm9keSwgc3QsIFwiU3RhdGVtZW50XCIpO1xufTtcbmJhc2UuRm9ySW5pdCA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBpZiAobm9kZS50eXBlID09IFwiVmFyaWFibGVEZWNsYXJhdGlvblwiKSBjKG5vZGUsIHN0KTtlbHNlIGMobm9kZSwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbn07XG5iYXNlLkRlYnVnZ2VyU3RhdGVtZW50ID0gaWdub3JlO1xuXG5iYXNlLkZ1bmN0aW9uRGVjbGFyYXRpb24gPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgcmV0dXJuIGMobm9kZSwgc3QsIFwiRnVuY3Rpb25cIik7XG59O1xuYmFzZS5WYXJpYWJsZURlY2xhcmF0aW9uID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIGZvciAodmFyIGkgPSAwOyBpIDwgbm9kZS5kZWNsYXJhdGlvbnMubGVuZ3RoOyArK2kpIHtcbiAgICBjKG5vZGUuZGVjbGFyYXRpb25zW2ldLCBzdCk7XG4gIH1cbn07XG5iYXNlLlZhcmlhYmxlRGVjbGFyYXRvciA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBjKG5vZGUuaWQsIHN0LCBcIlBhdHRlcm5cIik7XG4gIGlmIChub2RlLmluaXQpIGMobm9kZS5pbml0LCBzdCwgXCJFeHByZXNzaW9uXCIpO1xufTtcblxuYmFzZS5GdW5jdGlvbiA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBpZiAobm9kZS5pZCkgYyhub2RlLmlkLCBzdCwgXCJQYXR0ZXJuXCIpO1xuICBmb3IgKHZhciBpID0gMDsgaSA8IG5vZGUucGFyYW1zLmxlbmd0aDsgaSsrKSB7XG4gICAgYyhub2RlLnBhcmFtc1tpXSwgc3QsIFwiUGF0dGVyblwiKTtcbiAgfWMobm9kZS5ib2R5LCBzdCwgbm9kZS5leHByZXNzaW9uID8gXCJTY29wZUV4cHJlc3Npb25cIiA6IFwiU2NvcGVCb2R5XCIpO1xufTtcbi8vIEZJWE1FIGRyb3AgdGhlc2Ugbm9kZSB0eXBlcyBpbiBuZXh0IG1ham9yIHZlcnNpb25cbi8vIChUaGV5IGFyZSBhd2t3YXJkLCBhbmQgaW4gRVM2IGV2ZXJ5IGJsb2NrIGNhbiBiZSBhIHNjb3BlLilcbmJhc2UuU2NvcGVCb2R5ID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIHJldHVybiBjKG5vZGUsIHN0LCBcIlN0YXRlbWVudFwiKTtcbn07XG5iYXNlLlNjb3BlRXhwcmVzc2lvbiA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICByZXR1cm4gYyhub2RlLCBzdCwgXCJFeHByZXNzaW9uXCIpO1xufTtcblxuYmFzZS5QYXR0ZXJuID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIGlmIChub2RlLnR5cGUgPT0gXCJJZGVudGlmaWVyXCIpIGMobm9kZSwgc3QsIFwiVmFyaWFibGVQYXR0ZXJuXCIpO2Vsc2UgaWYgKG5vZGUudHlwZSA9PSBcIk1lbWJlckV4cHJlc3Npb25cIikgYyhub2RlLCBzdCwgXCJNZW1iZXJQYXR0ZXJuXCIpO2Vsc2UgYyhub2RlLCBzdCk7XG59O1xuYmFzZS5WYXJpYWJsZVBhdHRlcm4gPSBpZ25vcmU7XG5iYXNlLk1lbWJlclBhdHRlcm4gPSBza2lwVGhyb3VnaDtcbmJhc2UuUmVzdEVsZW1lbnQgPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgcmV0dXJuIGMobm9kZS5hcmd1bWVudCwgc3QsIFwiUGF0dGVyblwiKTtcbn07XG5iYXNlLkFycmF5UGF0dGVybiA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBmb3IgKHZhciBpID0gMDsgaSA8IG5vZGUuZWxlbWVudHMubGVuZ3RoOyArK2kpIHtcbiAgICB2YXIgZWx0ID0gbm9kZS5lbGVtZW50c1tpXTtcbiAgICBpZiAoZWx0KSBjKGVsdCwgc3QsIFwiUGF0dGVyblwiKTtcbiAgfVxufTtcbmJhc2UuT2JqZWN0UGF0dGVybiA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBmb3IgKHZhciBpID0gMDsgaSA8IG5vZGUucHJvcGVydGllcy5sZW5ndGg7ICsraSkge1xuICAgIGMobm9kZS5wcm9wZXJ0aWVzW2ldLnZhbHVlLCBzdCwgXCJQYXR0ZXJuXCIpO1xuICB9XG59O1xuXG5iYXNlLkV4cHJlc3Npb24gPSBza2lwVGhyb3VnaDtcbmJhc2UuVGhpc0V4cHJlc3Npb24gPSBiYXNlLlN1cGVyID0gYmFzZS5NZXRhUHJvcGVydHkgPSBpZ25vcmU7XG5iYXNlLkFycmF5RXhwcmVzc2lvbiA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBmb3IgKHZhciBpID0gMDsgaSA8IG5vZGUuZWxlbWVudHMubGVuZ3RoOyArK2kpIHtcbiAgICB2YXIgZWx0ID0gbm9kZS5lbGVtZW50c1tpXTtcbiAgICBpZiAoZWx0KSBjKGVsdCwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbiAgfVxufTtcbmJhc2UuT2JqZWN0RXhwcmVzc2lvbiA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBmb3IgKHZhciBpID0gMDsgaSA8IG5vZGUucHJvcGVydGllcy5sZW5ndGg7ICsraSkge1xuICAgIGMobm9kZS5wcm9wZXJ0aWVzW2ldLCBzdCk7XG4gIH1cbn07XG5iYXNlLkZ1bmN0aW9uRXhwcmVzc2lvbiA9IGJhc2UuQXJyb3dGdW5jdGlvbkV4cHJlc3Npb24gPSBiYXNlLkZ1bmN0aW9uRGVjbGFyYXRpb247XG5iYXNlLlNlcXVlbmNlRXhwcmVzc2lvbiA9IGJhc2UuVGVtcGxhdGVMaXRlcmFsID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIGZvciAodmFyIGkgPSAwOyBpIDwgbm9kZS5leHByZXNzaW9ucy5sZW5ndGg7ICsraSkge1xuICAgIGMobm9kZS5leHByZXNzaW9uc1tpXSwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbiAgfVxufTtcbmJhc2UuVW5hcnlFeHByZXNzaW9uID0gYmFzZS5VcGRhdGVFeHByZXNzaW9uID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIGMobm9kZS5hcmd1bWVudCwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbn07XG5iYXNlLkJpbmFyeUV4cHJlc3Npb24gPSBiYXNlLkxvZ2ljYWxFeHByZXNzaW9uID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIGMobm9kZS5sZWZ0LCBzdCwgXCJFeHByZXNzaW9uXCIpO1xuICBjKG5vZGUucmlnaHQsIHN0LCBcIkV4cHJlc3Npb25cIik7XG59O1xuYmFzZS5Bc3NpZ25tZW50RXhwcmVzc2lvbiA9IGJhc2UuQXNzaWdubWVudFBhdHRlcm4gPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgYyhub2RlLmxlZnQsIHN0LCBcIlBhdHRlcm5cIik7XG4gIGMobm9kZS5yaWdodCwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbn07XG5iYXNlLkNvbmRpdGlvbmFsRXhwcmVzc2lvbiA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBjKG5vZGUudGVzdCwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbiAgYyhub2RlLmNvbnNlcXVlbnQsIHN0LCBcIkV4cHJlc3Npb25cIik7XG4gIGMobm9kZS5hbHRlcm5hdGUsIHN0LCBcIkV4cHJlc3Npb25cIik7XG59O1xuYmFzZS5OZXdFeHByZXNzaW9uID0gYmFzZS5DYWxsRXhwcmVzc2lvbiA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBjKG5vZGUuY2FsbGVlLCBzdCwgXCJFeHByZXNzaW9uXCIpO1xuICBpZiAobm9kZS5hcmd1bWVudHMpIGZvciAodmFyIGkgPSAwOyBpIDwgbm9kZS5hcmd1bWVudHMubGVuZ3RoOyArK2kpIHtcbiAgICBjKG5vZGUuYXJndW1lbnRzW2ldLCBzdCwgXCJFeHByZXNzaW9uXCIpO1xuICB9XG59O1xuYmFzZS5NZW1iZXJFeHByZXNzaW9uID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIGMobm9kZS5vYmplY3QsIHN0LCBcIkV4cHJlc3Npb25cIik7XG4gIGlmIChub2RlLmNvbXB1dGVkKSBjKG5vZGUucHJvcGVydHksIHN0LCBcIkV4cHJlc3Npb25cIik7XG59O1xuYmFzZS5FeHBvcnROYW1lZERlY2xhcmF0aW9uID0gYmFzZS5FeHBvcnREZWZhdWx0RGVjbGFyYXRpb24gPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgaWYgKG5vZGUuZGVjbGFyYXRpb24pIGMobm9kZS5kZWNsYXJhdGlvbiwgc3QpO1xuICBpZiAobm9kZS5zb3VyY2UpIGMobm9kZS5zb3VyY2UsIHN0LCBcIkV4cHJlc3Npb25cIik7XG59O1xuYmFzZS5FeHBvcnRBbGxEZWNsYXJhdGlvbiA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBjKG5vZGUuc291cmNlLCBzdCwgXCJFeHByZXNzaW9uXCIpO1xufTtcbmJhc2UuSW1wb3J0RGVjbGFyYXRpb24gPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgZm9yICh2YXIgaSA9IDA7IGkgPCBub2RlLnNwZWNpZmllcnMubGVuZ3RoOyBpKyspIHtcbiAgICBjKG5vZGUuc3BlY2lmaWVyc1tpXSwgc3QpO1xuICB9Yyhub2RlLnNvdXJjZSwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbn07XG5iYXNlLkltcG9ydFNwZWNpZmllciA9IGJhc2UuSW1wb3J0RGVmYXVsdFNwZWNpZmllciA9IGJhc2UuSW1wb3J0TmFtZXNwYWNlU3BlY2lmaWVyID0gYmFzZS5JZGVudGlmaWVyID0gYmFzZS5MaXRlcmFsID0gaWdub3JlO1xuXG5iYXNlLlRhZ2dlZFRlbXBsYXRlRXhwcmVzc2lvbiA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBjKG5vZGUudGFnLCBzdCwgXCJFeHByZXNzaW9uXCIpO1xuICBjKG5vZGUucXVhc2ksIHN0KTtcbn07XG5iYXNlLkNsYXNzRGVjbGFyYXRpb24gPSBiYXNlLkNsYXNzRXhwcmVzc2lvbiA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICByZXR1cm4gYyhub2RlLCBzdCwgXCJDbGFzc1wiKTtcbn07XG5iYXNlLkNsYXNzID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIGlmIChub2RlLmlkKSBjKG5vZGUuaWQsIHN0LCBcIlBhdHRlcm5cIik7XG4gIGlmIChub2RlLnN1cGVyQ2xhc3MpIGMobm9kZS5zdXBlckNsYXNzLCBzdCwgXCJFeHByZXNzaW9uXCIpO1xuICBmb3IgKHZhciBpID0gMDsgaSA8IG5vZGUuYm9keS5ib2R5Lmxlbmd0aDsgaSsrKSB7XG4gICAgYyhub2RlLmJvZHkuYm9keVtpXSwgc3QpO1xuICB9XG59O1xuYmFzZS5NZXRob2REZWZpbml0aW9uID0gYmFzZS5Qcm9wZXJ0eSA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBpZiAobm9kZS5jb21wdXRlZCkgYyhub2RlLmtleSwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbiAgYyhub2RlLnZhbHVlLCBzdCwgXCJFeHByZXNzaW9uXCIpO1xufTtcbmJhc2UuQ29tcHJlaGVuc2lvbkV4cHJlc3Npb24gPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgZm9yICh2YXIgaSA9IDA7IGkgPCBub2RlLmJsb2Nrcy5sZW5ndGg7IGkrKykge1xuICAgIGMobm9kZS5ibG9ja3NbaV0ucmlnaHQsIHN0LCBcIkV4cHJlc3Npb25cIik7XG4gIH1jKG5vZGUuYm9keSwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbn07XG5cbn0se31dfSx7fSxbMV0pKDEpXG59KTsiLCJpZiAodHlwZW9mIE9iamVjdC5jcmVhdGUgPT09ICdmdW5jdGlvbicpIHtcbiAgLy8gaW1wbGVtZW50YXRpb24gZnJvbSBzdGFuZGFyZCBub2RlLmpzICd1dGlsJyBtb2R1bGVcbiAgbW9kdWxlLmV4cG9ydHMgPSBmdW5jdGlvbiBpbmhlcml0cyhjdG9yLCBzdXBlckN0b3IpIHtcbiAgICBjdG9yLnN1cGVyXyA9IHN1cGVyQ3RvclxuICAgIGN0b3IucHJvdG90eXBlID0gT2JqZWN0LmNyZWF0ZShzdXBlckN0b3IucHJvdG90eXBlLCB7XG4gICAgICBjb25zdHJ1Y3Rvcjoge1xuICAgICAgICB2YWx1ZTogY3RvcixcbiAgICAgICAgZW51bWVyYWJsZTogZmFsc2UsXG4gICAgICAgIHdyaXRhYmxlOiB0cnVlLFxuICAgICAgICBjb25maWd1cmFibGU6IHRydWVcbiAgICAgIH1cbiAgICB9KTtcbiAgfTtcbn0gZWxzZSB7XG4gIC8vIG9sZCBzY2hvb2wgc2hpbSBmb3Igb2xkIGJyb3dzZXJzXG4gIG1vZHVsZS5leHBvcnRzID0gZnVuY3Rpb24gaW5oZXJpdHMoY3Rvciwgc3VwZXJDdG9yKSB7XG4gICAgY3Rvci5zdXBlcl8gPSBzdXBlckN0b3JcbiAgICB2YXIgVGVtcEN0b3IgPSBmdW5jdGlvbiAoKSB7fVxuICAgIFRlbXBDdG9yLnByb3RvdHlwZSA9IHN1cGVyQ3Rvci5wcm90b3R5cGVcbiAgICBjdG9yLnByb3RvdHlwZSA9IG5ldyBUZW1wQ3RvcigpXG4gICAgY3Rvci5wcm90b3R5cGUuY29uc3RydWN0b3IgPSBjdG9yXG4gIH1cbn1cbiIsIi8vIHNoaW0gZm9yIHVzaW5nIHByb2Nlc3MgaW4gYnJvd3NlclxuXG52YXIgcHJvY2VzcyA9IG1vZHVsZS5leHBvcnRzID0ge307XG52YXIgcXVldWUgPSBbXTtcbnZhciBkcmFpbmluZyA9IGZhbHNlO1xudmFyIGN1cnJlbnRRdWV1ZTtcbnZhciBxdWV1ZUluZGV4ID0gLTE7XG5cbmZ1bmN0aW9uIGNsZWFuVXBOZXh0VGljaygpIHtcbiAgICBkcmFpbmluZyA9IGZhbHNlO1xuICAgIGlmIChjdXJyZW50UXVldWUubGVuZ3RoKSB7XG4gICAgICAgIHF1ZXVlID0gY3VycmVudFF1ZXVlLmNvbmNhdChxdWV1ZSk7XG4gICAgfSBlbHNlIHtcbiAgICAgICAgcXVldWVJbmRleCA9IC0xO1xuICAgIH1cbiAgICBpZiAocXVldWUubGVuZ3RoKSB7XG4gICAgICAgIGRyYWluUXVldWUoKTtcbiAgICB9XG59XG5cbmZ1bmN0aW9uIGRyYWluUXVldWUoKSB7XG4gICAgaWYgKGRyYWluaW5nKSB7XG4gICAgICAgIHJldHVybjtcbiAgICB9XG4gICAgdmFyIHRpbWVvdXQgPSBzZXRUaW1lb3V0KGNsZWFuVXBOZXh0VGljayk7XG4gICAgZHJhaW5pbmcgPSB0cnVlO1xuXG4gICAgdmFyIGxlbiA9IHF1ZXVlLmxlbmd0aDtcbiAgICB3aGlsZShsZW4pIHtcbiAgICAgICAgY3VycmVudFF1ZXVlID0gcXVldWU7XG4gICAgICAgIHF1ZXVlID0gW107XG4gICAgICAgIHdoaWxlICgrK3F1ZXVlSW5kZXggPCBsZW4pIHtcbiAgICAgICAgICAgIGN1cnJlbnRRdWV1ZVtxdWV1ZUluZGV4XS5ydW4oKTtcbiAgICAgICAgfVxuICAgICAgICBxdWV1ZUluZGV4ID0gLTE7XG4gICAgICAgIGxlbiA9IHF1ZXVlLmxlbmd0aDtcbiAgICB9XG4gICAgY3VycmVudFF1ZXVlID0gbnVsbDtcbiAgICBkcmFpbmluZyA9IGZhbHNlO1xuICAgIGNsZWFyVGltZW91dCh0aW1lb3V0KTtcbn1cblxucHJvY2Vzcy5uZXh0VGljayA9IGZ1bmN0aW9uIChmdW4pIHtcbiAgICB2YXIgYXJncyA9IG5ldyBBcnJheShhcmd1bWVudHMubGVuZ3RoIC0gMSk7XG4gICAgaWYgKGFyZ3VtZW50cy5sZW5ndGggPiAxKSB7XG4gICAgICAgIGZvciAodmFyIGkgPSAxOyBpIDwgYXJndW1lbnRzLmxlbmd0aDsgaSsrKSB7XG4gICAgICAgICAgICBhcmdzW2kgLSAxXSA9IGFyZ3VtZW50c1tpXTtcbiAgICAgICAgfVxuICAgIH1cbiAgICBxdWV1ZS5wdXNoKG5ldyBJdGVtKGZ1biwgYXJncykpO1xuICAgIGlmIChxdWV1ZS5sZW5ndGggPT09IDEgJiYgIWRyYWluaW5nKSB7XG4gICAgICAgIHNldFRpbWVvdXQoZHJhaW5RdWV1ZSwgMCk7XG4gICAgfVxufTtcblxuLy8gdjggbGlrZXMgcHJlZGljdGlibGUgb2JqZWN0c1xuZnVuY3Rpb24gSXRlbShmdW4sIGFycmF5KSB7XG4gICAgdGhpcy5mdW4gPSBmdW47XG4gICAgdGhpcy5hcnJheSA9IGFycmF5O1xufVxuSXRlbS5wcm90b3R5cGUucnVuID0gZnVuY3Rpb24gKCkge1xuICAgIHRoaXMuZnVuLmFwcGx5KG51bGwsIHRoaXMuYXJyYXkpO1xufTtcbnByb2Nlc3MudGl0bGUgPSAnYnJvd3Nlcic7XG5wcm9jZXNzLmJyb3dzZXIgPSB0cnVlO1xucHJvY2Vzcy5lbnYgPSB7fTtcbnByb2Nlc3MuYXJndiA9IFtdO1xucHJvY2Vzcy52ZXJzaW9uID0gJyc7IC8vIGVtcHR5IHN0cmluZyB0byBhdm9pZCByZWdleHAgaXNzdWVzXG5wcm9jZXNzLnZlcnNpb25zID0ge307XG5cbmZ1bmN0aW9uIG5vb3AoKSB7fVxuXG5wcm9jZXNzLm9uID0gbm9vcDtcbnByb2Nlc3MuYWRkTGlzdGVuZXIgPSBub29wO1xucHJvY2Vzcy5vbmNlID0gbm9vcDtcbnByb2Nlc3Mub2ZmID0gbm9vcDtcbnByb2Nlc3MucmVtb3ZlTGlzdGVuZXIgPSBub29wO1xucHJvY2Vzcy5yZW1vdmVBbGxMaXN0ZW5lcnMgPSBub29wO1xucHJvY2Vzcy5lbWl0ID0gbm9vcDtcblxucHJvY2Vzcy5iaW5kaW5nID0gZnVuY3Rpb24gKG5hbWUpIHtcbiAgICB0aHJvdyBuZXcgRXJyb3IoJ3Byb2Nlc3MuYmluZGluZyBpcyBub3Qgc3VwcG9ydGVkJyk7XG59O1xuXG4vLyBUT0RPKHNodHlsbWFuKVxucHJvY2Vzcy5jd2QgPSBmdW5jdGlvbiAoKSB7IHJldHVybiAnLycgfTtcbnByb2Nlc3MuY2hkaXIgPSBmdW5jdGlvbiAoZGlyKSB7XG4gICAgdGhyb3cgbmV3IEVycm9yKCdwcm9jZXNzLmNoZGlyIGlzIG5vdCBzdXBwb3J0ZWQnKTtcbn07XG5wcm9jZXNzLnVtYXNrID0gZnVuY3Rpb24oKSB7IHJldHVybiAwOyB9O1xuIiwibW9kdWxlLmV4cG9ydHMgPSBmdW5jdGlvbiBpc0J1ZmZlcihhcmcpIHtcbiAgcmV0dXJuIGFyZyAmJiB0eXBlb2YgYXJnID09PSAnb2JqZWN0J1xuICAgICYmIHR5cGVvZiBhcmcuY29weSA9PT0gJ2Z1bmN0aW9uJ1xuICAgICYmIHR5cGVvZiBhcmcuZmlsbCA9PT0gJ2Z1bmN0aW9uJ1xuICAgICYmIHR5cGVvZiBhcmcucmVhZFVJbnQ4ID09PSAnZnVuY3Rpb24nO1xufSIsIi8vIENvcHlyaWdodCBKb3llbnQsIEluYy4gYW5kIG90aGVyIE5vZGUgY29udHJpYnV0b3JzLlxuLy9cbi8vIFBlcm1pc3Npb24gaXMgaGVyZWJ5IGdyYW50ZWQsIGZyZWUgb2YgY2hhcmdlLCB0byBhbnkgcGVyc29uIG9idGFpbmluZyBhXG4vLyBjb3B5IG9mIHRoaXMgc29mdHdhcmUgYW5kIGFzc29jaWF0ZWQgZG9jdW1lbnRhdGlvbiBmaWxlcyAodGhlXG4vLyBcIlNvZnR3YXJlXCIpLCB0byBkZWFsIGluIHRoZSBTb2Z0d2FyZSB3aXRob3V0IHJlc3RyaWN0aW9uLCBpbmNsdWRpbmdcbi8vIHdpdGhvdXQgbGltaXRhdGlvbiB0aGUgcmlnaHRzIHRvIHVzZSwgY29weSwgbW9kaWZ5LCBtZXJnZSwgcHVibGlzaCxcbi8vIGRpc3RyaWJ1dGUsIHN1YmxpY2Vuc2UsIGFuZC9vciBzZWxsIGNvcGllcyBvZiB0aGUgU29mdHdhcmUsIGFuZCB0byBwZXJtaXRcbi8vIHBlcnNvbnMgdG8gd2hvbSB0aGUgU29mdHdhcmUgaXMgZnVybmlzaGVkIHRvIGRvIHNvLCBzdWJqZWN0IHRvIHRoZVxuLy8gZm9sbG93aW5nIGNvbmRpdGlvbnM6XG4vL1xuLy8gVGhlIGFib3ZlIGNvcHlyaWdodCBub3RpY2UgYW5kIHRoaXMgcGVybWlzc2lvbiBub3RpY2Ugc2hhbGwgYmUgaW5jbHVkZWRcbi8vIGluIGFsbCBjb3BpZXMgb3Igc3Vic3RhbnRpYWwgcG9ydGlvbnMgb2YgdGhlIFNvZnR3YXJlLlxuLy9cbi8vIFRIRSBTT0ZUV0FSRSBJUyBQUk9WSURFRCBcIkFTIElTXCIsIFdJVEhPVVQgV0FSUkFOVFkgT0YgQU5ZIEtJTkQsIEVYUFJFU1Ncbi8vIE9SIElNUExJRUQsIElOQ0xVRElORyBCVVQgTk9UIExJTUlURUQgVE8gVEhFIFdBUlJBTlRJRVMgT0Zcbi8vIE1FUkNIQU5UQUJJTElUWSwgRklUTkVTUyBGT1IgQSBQQVJUSUNVTEFSIFBVUlBPU0UgQU5EIE5PTklORlJJTkdFTUVOVC4gSU5cbi8vIE5PIEVWRU5UIFNIQUxMIFRIRSBBVVRIT1JTIE9SIENPUFlSSUdIVCBIT0xERVJTIEJFIExJQUJMRSBGT1IgQU5ZIENMQUlNLFxuLy8gREFNQUdFUyBPUiBPVEhFUiBMSUFCSUxJVFksIFdIRVRIRVIgSU4gQU4gQUNUSU9OIE9GIENPTlRSQUNULCBUT1JUIE9SXG4vLyBPVEhFUldJU0UsIEFSSVNJTkcgRlJPTSwgT1VUIE9GIE9SIElOIENPTk5FQ1RJT04gV0lUSCBUSEUgU09GVFdBUkUgT1IgVEhFXG4vLyBVU0UgT1IgT1RIRVIgREVBTElOR1MgSU4gVEhFIFNPRlRXQVJFLlxuXG52YXIgZm9ybWF0UmVnRXhwID0gLyVbc2RqJV0vZztcbmV4cG9ydHMuZm9ybWF0ID0gZnVuY3Rpb24oZikge1xuICBpZiAoIWlzU3RyaW5nKGYpKSB7XG4gICAgdmFyIG9iamVjdHMgPSBbXTtcbiAgICBmb3IgKHZhciBpID0gMDsgaSA8IGFyZ3VtZW50cy5sZW5ndGg7IGkrKykge1xuICAgICAgb2JqZWN0cy5wdXNoKGluc3BlY3QoYXJndW1lbnRzW2ldKSk7XG4gICAgfVxuICAgIHJldHVybiBvYmplY3RzLmpvaW4oJyAnKTtcbiAgfVxuXG4gIHZhciBpID0gMTtcbiAgdmFyIGFyZ3MgPSBhcmd1bWVudHM7XG4gIHZhciBsZW4gPSBhcmdzLmxlbmd0aDtcbiAgdmFyIHN0ciA9IFN0cmluZyhmKS5yZXBsYWNlKGZvcm1hdFJlZ0V4cCwgZnVuY3Rpb24oeCkge1xuICAgIGlmICh4ID09PSAnJSUnKSByZXR1cm4gJyUnO1xuICAgIGlmIChpID49IGxlbikgcmV0dXJuIHg7XG4gICAgc3dpdGNoICh4KSB7XG4gICAgICBjYXNlICclcyc6IHJldHVybiBTdHJpbmcoYXJnc1tpKytdKTtcbiAgICAgIGNhc2UgJyVkJzogcmV0dXJuIE51bWJlcihhcmdzW2krK10pO1xuICAgICAgY2FzZSAnJWonOlxuICAgICAgICB0cnkge1xuICAgICAgICAgIHJldHVybiBKU09OLnN0cmluZ2lmeShhcmdzW2krK10pO1xuICAgICAgICB9IGNhdGNoIChfKSB7XG4gICAgICAgICAgcmV0dXJuICdbQ2lyY3VsYXJdJztcbiAgICAgICAgfVxuICAgICAgZGVmYXVsdDpcbiAgICAgICAgcmV0dXJuIHg7XG4gICAgfVxuICB9KTtcbiAgZm9yICh2YXIgeCA9IGFyZ3NbaV07IGkgPCBsZW47IHggPSBhcmdzWysraV0pIHtcbiAgICBpZiAoaXNOdWxsKHgpIHx8ICFpc09iamVjdCh4KSkge1xuICAgICAgc3RyICs9ICcgJyArIHg7XG4gICAgfSBlbHNlIHtcbiAgICAgIHN0ciArPSAnICcgKyBpbnNwZWN0KHgpO1xuICAgIH1cbiAgfVxuICByZXR1cm4gc3RyO1xufTtcblxuXG4vLyBNYXJrIHRoYXQgYSBtZXRob2Qgc2hvdWxkIG5vdCBiZSB1c2VkLlxuLy8gUmV0dXJucyBhIG1vZGlmaWVkIGZ1bmN0aW9uIHdoaWNoIHdhcm5zIG9uY2UgYnkgZGVmYXVsdC5cbi8vIElmIC0tbm8tZGVwcmVjYXRpb24gaXMgc2V0LCB0aGVuIGl0IGlzIGEgbm8tb3AuXG5leHBvcnRzLmRlcHJlY2F0ZSA9IGZ1bmN0aW9uKGZuLCBtc2cpIHtcbiAgLy8gQWxsb3cgZm9yIGRlcHJlY2F0aW5nIHRoaW5ncyBpbiB0aGUgcHJvY2VzcyBvZiBzdGFydGluZyB1cC5cbiAgaWYgKGlzVW5kZWZpbmVkKGdsb2JhbC5wcm9jZXNzKSkge1xuICAgIHJldHVybiBmdW5jdGlvbigpIHtcbiAgICAgIHJldHVybiBleHBvcnRzLmRlcHJlY2F0ZShmbiwgbXNnKS5hcHBseSh0aGlzLCBhcmd1bWVudHMpO1xuICAgIH07XG4gIH1cblxuICBpZiAocHJvY2Vzcy5ub0RlcHJlY2F0aW9uID09PSB0cnVlKSB7XG4gICAgcmV0dXJuIGZuO1xuICB9XG5cbiAgdmFyIHdhcm5lZCA9IGZhbHNlO1xuICBmdW5jdGlvbiBkZXByZWNhdGVkKCkge1xuICAgIGlmICghd2FybmVkKSB7XG4gICAgICBpZiAocHJvY2Vzcy50aHJvd0RlcHJlY2F0aW9uKSB7XG4gICAgICAgIHRocm93IG5ldyBFcnJvcihtc2cpO1xuICAgICAgfSBlbHNlIGlmIChwcm9jZXNzLnRyYWNlRGVwcmVjYXRpb24pIHtcbiAgICAgICAgY29uc29sZS50cmFjZShtc2cpO1xuICAgICAgfSBlbHNlIHtcbiAgICAgICAgY29uc29sZS5lcnJvcihtc2cpO1xuICAgICAgfVxuICAgICAgd2FybmVkID0gdHJ1ZTtcbiAgICB9XG4gICAgcmV0dXJuIGZuLmFwcGx5KHRoaXMsIGFyZ3VtZW50cyk7XG4gIH1cblxuICByZXR1cm4gZGVwcmVjYXRlZDtcbn07XG5cblxudmFyIGRlYnVncyA9IHt9O1xudmFyIGRlYnVnRW52aXJvbjtcbmV4cG9ydHMuZGVidWdsb2cgPSBmdW5jdGlvbihzZXQpIHtcbiAgaWYgKGlzVW5kZWZpbmVkKGRlYnVnRW52aXJvbikpXG4gICAgZGVidWdFbnZpcm9uID0gcHJvY2Vzcy5lbnYuTk9ERV9ERUJVRyB8fCAnJztcbiAgc2V0ID0gc2V0LnRvVXBwZXJDYXNlKCk7XG4gIGlmICghZGVidWdzW3NldF0pIHtcbiAgICBpZiAobmV3IFJlZ0V4cCgnXFxcXGInICsgc2V0ICsgJ1xcXFxiJywgJ2knKS50ZXN0KGRlYnVnRW52aXJvbikpIHtcbiAgICAgIHZhciBwaWQgPSBwcm9jZXNzLnBpZDtcbiAgICAgIGRlYnVnc1tzZXRdID0gZnVuY3Rpb24oKSB7XG4gICAgICAgIHZhciBtc2cgPSBleHBvcnRzLmZvcm1hdC5hcHBseShleHBvcnRzLCBhcmd1bWVudHMpO1xuICAgICAgICBjb25zb2xlLmVycm9yKCclcyAlZDogJXMnLCBzZXQsIHBpZCwgbXNnKTtcbiAgICAgIH07XG4gICAgfSBlbHNlIHtcbiAgICAgIGRlYnVnc1tzZXRdID0gZnVuY3Rpb24oKSB7fTtcbiAgICB9XG4gIH1cbiAgcmV0dXJuIGRlYnVnc1tzZXRdO1xufTtcblxuXG4vKipcbiAqIEVjaG9zIHRoZSB2YWx1ZSBvZiBhIHZhbHVlLiBUcnlzIHRvIHByaW50IHRoZSB2YWx1ZSBvdXRcbiAqIGluIHRoZSBiZXN0IHdheSBwb3NzaWJsZSBnaXZlbiB0aGUgZGlmZmVyZW50IHR5cGVzLlxuICpcbiAqIEBwYXJhbSB7T2JqZWN0fSBvYmogVGhlIG9iamVjdCB0byBwcmludCBvdXQuXG4gKiBAcGFyYW0ge09iamVjdH0gb3B0cyBPcHRpb25hbCBvcHRpb25zIG9iamVjdCB0aGF0IGFsdGVycyB0aGUgb3V0cHV0LlxuICovXG4vKiBsZWdhY3k6IG9iaiwgc2hvd0hpZGRlbiwgZGVwdGgsIGNvbG9ycyovXG5mdW5jdGlvbiBpbnNwZWN0KG9iaiwgb3B0cykge1xuICAvLyBkZWZhdWx0IG9wdGlvbnNcbiAgdmFyIGN0eCA9IHtcbiAgICBzZWVuOiBbXSxcbiAgICBzdHlsaXplOiBzdHlsaXplTm9Db2xvclxuICB9O1xuICAvLyBsZWdhY3kuLi5cbiAgaWYgKGFyZ3VtZW50cy5sZW5ndGggPj0gMykgY3R4LmRlcHRoID0gYXJndW1lbnRzWzJdO1xuICBpZiAoYXJndW1lbnRzLmxlbmd0aCA+PSA0KSBjdHguY29sb3JzID0gYXJndW1lbnRzWzNdO1xuICBpZiAoaXNCb29sZWFuKG9wdHMpKSB7XG4gICAgLy8gbGVnYWN5Li4uXG4gICAgY3R4LnNob3dIaWRkZW4gPSBvcHRzO1xuICB9IGVsc2UgaWYgKG9wdHMpIHtcbiAgICAvLyBnb3QgYW4gXCJvcHRpb25zXCIgb2JqZWN0XG4gICAgZXhwb3J0cy5fZXh0ZW5kKGN0eCwgb3B0cyk7XG4gIH1cbiAgLy8gc2V0IGRlZmF1bHQgb3B0aW9uc1xuICBpZiAoaXNVbmRlZmluZWQoY3R4LnNob3dIaWRkZW4pKSBjdHguc2hvd0hpZGRlbiA9IGZhbHNlO1xuICBpZiAoaXNVbmRlZmluZWQoY3R4LmRlcHRoKSkgY3R4LmRlcHRoID0gMjtcbiAgaWYgKGlzVW5kZWZpbmVkKGN0eC5jb2xvcnMpKSBjdHguY29sb3JzID0gZmFsc2U7XG4gIGlmIChpc1VuZGVmaW5lZChjdHguY3VzdG9tSW5zcGVjdCkpIGN0eC5jdXN0b21JbnNwZWN0ID0gdHJ1ZTtcbiAgaWYgKGN0eC5jb2xvcnMpIGN0eC5zdHlsaXplID0gc3R5bGl6ZVdpdGhDb2xvcjtcbiAgcmV0dXJuIGZvcm1hdFZhbHVlKGN0eCwgb2JqLCBjdHguZGVwdGgpO1xufVxuZXhwb3J0cy5pbnNwZWN0ID0gaW5zcGVjdDtcblxuXG4vLyBodHRwOi8vZW4ud2lraXBlZGlhLm9yZy93aWtpL0FOU0lfZXNjYXBlX2NvZGUjZ3JhcGhpY3Ncbmluc3BlY3QuY29sb3JzID0ge1xuICAnYm9sZCcgOiBbMSwgMjJdLFxuICAnaXRhbGljJyA6IFszLCAyM10sXG4gICd1bmRlcmxpbmUnIDogWzQsIDI0XSxcbiAgJ2ludmVyc2UnIDogWzcsIDI3XSxcbiAgJ3doaXRlJyA6IFszNywgMzldLFxuICAnZ3JleScgOiBbOTAsIDM5XSxcbiAgJ2JsYWNrJyA6IFszMCwgMzldLFxuICAnYmx1ZScgOiBbMzQsIDM5XSxcbiAgJ2N5YW4nIDogWzM2LCAzOV0sXG4gICdncmVlbicgOiBbMzIsIDM5XSxcbiAgJ21hZ2VudGEnIDogWzM1LCAzOV0sXG4gICdyZWQnIDogWzMxLCAzOV0sXG4gICd5ZWxsb3cnIDogWzMzLCAzOV1cbn07XG5cbi8vIERvbid0IHVzZSAnYmx1ZScgbm90IHZpc2libGUgb24gY21kLmV4ZVxuaW5zcGVjdC5zdHlsZXMgPSB7XG4gICdzcGVjaWFsJzogJ2N5YW4nLFxuICAnbnVtYmVyJzogJ3llbGxvdycsXG4gICdib29sZWFuJzogJ3llbGxvdycsXG4gICd1bmRlZmluZWQnOiAnZ3JleScsXG4gICdudWxsJzogJ2JvbGQnLFxuICAnc3RyaW5nJzogJ2dyZWVuJyxcbiAgJ2RhdGUnOiAnbWFnZW50YScsXG4gIC8vIFwibmFtZVwiOiBpbnRlbnRpb25hbGx5IG5vdCBzdHlsaW5nXG4gICdyZWdleHAnOiAncmVkJ1xufTtcblxuXG5mdW5jdGlvbiBzdHlsaXplV2l0aENvbG9yKHN0ciwgc3R5bGVUeXBlKSB7XG4gIHZhciBzdHlsZSA9IGluc3BlY3Quc3R5bGVzW3N0eWxlVHlwZV07XG5cbiAgaWYgKHN0eWxlKSB7XG4gICAgcmV0dXJuICdcXHUwMDFiWycgKyBpbnNwZWN0LmNvbG9yc1tzdHlsZV1bMF0gKyAnbScgKyBzdHIgK1xuICAgICAgICAgICAnXFx1MDAxYlsnICsgaW5zcGVjdC5jb2xvcnNbc3R5bGVdWzFdICsgJ20nO1xuICB9IGVsc2Uge1xuICAgIHJldHVybiBzdHI7XG4gIH1cbn1cblxuXG5mdW5jdGlvbiBzdHlsaXplTm9Db2xvcihzdHIsIHN0eWxlVHlwZSkge1xuICByZXR1cm4gc3RyO1xufVxuXG5cbmZ1bmN0aW9uIGFycmF5VG9IYXNoKGFycmF5KSB7XG4gIHZhciBoYXNoID0ge307XG5cbiAgYXJyYXkuZm9yRWFjaChmdW5jdGlvbih2YWwsIGlkeCkge1xuICAgIGhhc2hbdmFsXSA9IHRydWU7XG4gIH0pO1xuXG4gIHJldHVybiBoYXNoO1xufVxuXG5cbmZ1bmN0aW9uIGZvcm1hdFZhbHVlKGN0eCwgdmFsdWUsIHJlY3Vyc2VUaW1lcykge1xuICAvLyBQcm92aWRlIGEgaG9vayBmb3IgdXNlci1zcGVjaWZpZWQgaW5zcGVjdCBmdW5jdGlvbnMuXG4gIC8vIENoZWNrIHRoYXQgdmFsdWUgaXMgYW4gb2JqZWN0IHdpdGggYW4gaW5zcGVjdCBmdW5jdGlvbiBvbiBpdFxuICBpZiAoY3R4LmN1c3RvbUluc3BlY3QgJiZcbiAgICAgIHZhbHVlICYmXG4gICAgICBpc0Z1bmN0aW9uKHZhbHVlLmluc3BlY3QpICYmXG4gICAgICAvLyBGaWx0ZXIgb3V0IHRoZSB1dGlsIG1vZHVsZSwgaXQncyBpbnNwZWN0IGZ1bmN0aW9uIGlzIHNwZWNpYWxcbiAgICAgIHZhbHVlLmluc3BlY3QgIT09IGV4cG9ydHMuaW5zcGVjdCAmJlxuICAgICAgLy8gQWxzbyBmaWx0ZXIgb3V0IGFueSBwcm90b3R5cGUgb2JqZWN0cyB1c2luZyB0aGUgY2lyY3VsYXIgY2hlY2suXG4gICAgICAhKHZhbHVlLmNvbnN0cnVjdG9yICYmIHZhbHVlLmNvbnN0cnVjdG9yLnByb3RvdHlwZSA9PT0gdmFsdWUpKSB7XG4gICAgdmFyIHJldCA9IHZhbHVlLmluc3BlY3QocmVjdXJzZVRpbWVzLCBjdHgpO1xuICAgIGlmICghaXNTdHJpbmcocmV0KSkge1xuICAgICAgcmV0ID0gZm9ybWF0VmFsdWUoY3R4LCByZXQsIHJlY3Vyc2VUaW1lcyk7XG4gICAgfVxuICAgIHJldHVybiByZXQ7XG4gIH1cblxuICAvLyBQcmltaXRpdmUgdHlwZXMgY2Fubm90IGhhdmUgcHJvcGVydGllc1xuICB2YXIgcHJpbWl0aXZlID0gZm9ybWF0UHJpbWl0aXZlKGN0eCwgdmFsdWUpO1xuICBpZiAocHJpbWl0aXZlKSB7XG4gICAgcmV0dXJuIHByaW1pdGl2ZTtcbiAgfVxuXG4gIC8vIExvb2sgdXAgdGhlIGtleXMgb2YgdGhlIG9iamVjdC5cbiAgdmFyIGtleXMgPSBPYmplY3Qua2V5cyh2YWx1ZSk7XG4gIHZhciB2aXNpYmxlS2V5cyA9IGFycmF5VG9IYXNoKGtleXMpO1xuXG4gIGlmIChjdHguc2hvd0hpZGRlbikge1xuICAgIGtleXMgPSBPYmplY3QuZ2V0T3duUHJvcGVydHlOYW1lcyh2YWx1ZSk7XG4gIH1cblxuICAvLyBJRSBkb2Vzbid0IG1ha2UgZXJyb3IgZmllbGRzIG5vbi1lbnVtZXJhYmxlXG4gIC8vIGh0dHA6Ly9tc2RuLm1pY3Jvc29mdC5jb20vZW4tdXMvbGlicmFyeS9pZS9kd3c1MnNidCh2PXZzLjk0KS5hc3B4XG4gIGlmIChpc0Vycm9yKHZhbHVlKVxuICAgICAgJiYgKGtleXMuaW5kZXhPZignbWVzc2FnZScpID49IDAgfHwga2V5cy5pbmRleE9mKCdkZXNjcmlwdGlvbicpID49IDApKSB7XG4gICAgcmV0dXJuIGZvcm1hdEVycm9yKHZhbHVlKTtcbiAgfVxuXG4gIC8vIFNvbWUgdHlwZSBvZiBvYmplY3Qgd2l0aG91dCBwcm9wZXJ0aWVzIGNhbiBiZSBzaG9ydGN1dHRlZC5cbiAgaWYgKGtleXMubGVuZ3RoID09PSAwKSB7XG4gICAgaWYgKGlzRnVuY3Rpb24odmFsdWUpKSB7XG4gICAgICB2YXIgbmFtZSA9IHZhbHVlLm5hbWUgPyAnOiAnICsgdmFsdWUubmFtZSA6ICcnO1xuICAgICAgcmV0dXJuIGN0eC5zdHlsaXplKCdbRnVuY3Rpb24nICsgbmFtZSArICddJywgJ3NwZWNpYWwnKTtcbiAgICB9XG4gICAgaWYgKGlzUmVnRXhwKHZhbHVlKSkge1xuICAgICAgcmV0dXJuIGN0eC5zdHlsaXplKFJlZ0V4cC5wcm90b3R5cGUudG9TdHJpbmcuY2FsbCh2YWx1ZSksICdyZWdleHAnKTtcbiAgICB9XG4gICAgaWYgKGlzRGF0ZSh2YWx1ZSkpIHtcbiAgICAgIHJldHVybiBjdHguc3R5bGl6ZShEYXRlLnByb3RvdHlwZS50b1N0cmluZy5jYWxsKHZhbHVlKSwgJ2RhdGUnKTtcbiAgICB9XG4gICAgaWYgKGlzRXJyb3IodmFsdWUpKSB7XG4gICAgICByZXR1cm4gZm9ybWF0RXJyb3IodmFsdWUpO1xuICAgIH1cbiAgfVxuXG4gIHZhciBiYXNlID0gJycsIGFycmF5ID0gZmFsc2UsIGJyYWNlcyA9IFsneycsICd9J107XG5cbiAgLy8gTWFrZSBBcnJheSBzYXkgdGhhdCB0aGV5IGFyZSBBcnJheVxuICBpZiAoaXNBcnJheSh2YWx1ZSkpIHtcbiAgICBhcnJheSA9IHRydWU7XG4gICAgYnJhY2VzID0gWydbJywgJ10nXTtcbiAgfVxuXG4gIC8vIE1ha2UgZnVuY3Rpb25zIHNheSB0aGF0IHRoZXkgYXJlIGZ1bmN0aW9uc1xuICBpZiAoaXNGdW5jdGlvbih2YWx1ZSkpIHtcbiAgICB2YXIgbiA9IHZhbHVlLm5hbWUgPyAnOiAnICsgdmFsdWUubmFtZSA6ICcnO1xuICAgIGJhc2UgPSAnIFtGdW5jdGlvbicgKyBuICsgJ10nO1xuICB9XG5cbiAgLy8gTWFrZSBSZWdFeHBzIHNheSB0aGF0IHRoZXkgYXJlIFJlZ0V4cHNcbiAgaWYgKGlzUmVnRXhwKHZhbHVlKSkge1xuICAgIGJhc2UgPSAnICcgKyBSZWdFeHAucHJvdG90eXBlLnRvU3RyaW5nLmNhbGwodmFsdWUpO1xuICB9XG5cbiAgLy8gTWFrZSBkYXRlcyB3aXRoIHByb3BlcnRpZXMgZmlyc3Qgc2F5IHRoZSBkYXRlXG4gIGlmIChpc0RhdGUodmFsdWUpKSB7XG4gICAgYmFzZSA9ICcgJyArIERhdGUucHJvdG90eXBlLnRvVVRDU3RyaW5nLmNhbGwodmFsdWUpO1xuICB9XG5cbiAgLy8gTWFrZSBlcnJvciB3aXRoIG1lc3NhZ2UgZmlyc3Qgc2F5IHRoZSBlcnJvclxuICBpZiAoaXNFcnJvcih2YWx1ZSkpIHtcbiAgICBiYXNlID0gJyAnICsgZm9ybWF0RXJyb3IodmFsdWUpO1xuICB9XG5cbiAgaWYgKGtleXMubGVuZ3RoID09PSAwICYmICghYXJyYXkgfHwgdmFsdWUubGVuZ3RoID09IDApKSB7XG4gICAgcmV0dXJuIGJyYWNlc1swXSArIGJhc2UgKyBicmFjZXNbMV07XG4gIH1cblxuICBpZiAocmVjdXJzZVRpbWVzIDwgMCkge1xuICAgIGlmIChpc1JlZ0V4cCh2YWx1ZSkpIHtcbiAgICAgIHJldHVybiBjdHguc3R5bGl6ZShSZWdFeHAucHJvdG90eXBlLnRvU3RyaW5nLmNhbGwodmFsdWUpLCAncmVnZXhwJyk7XG4gICAgfSBlbHNlIHtcbiAgICAgIHJldHVybiBjdHguc3R5bGl6ZSgnW09iamVjdF0nLCAnc3BlY2lhbCcpO1xuICAgIH1cbiAgfVxuXG4gIGN0eC5zZWVuLnB1c2godmFsdWUpO1xuXG4gIHZhciBvdXRwdXQ7XG4gIGlmIChhcnJheSkge1xuICAgIG91dHB1dCA9IGZvcm1hdEFycmF5KGN0eCwgdmFsdWUsIHJlY3Vyc2VUaW1lcywgdmlzaWJsZUtleXMsIGtleXMpO1xuICB9IGVsc2Uge1xuICAgIG91dHB1dCA9IGtleXMubWFwKGZ1bmN0aW9uKGtleSkge1xuICAgICAgcmV0dXJuIGZvcm1hdFByb3BlcnR5KGN0eCwgdmFsdWUsIHJlY3Vyc2VUaW1lcywgdmlzaWJsZUtleXMsIGtleSwgYXJyYXkpO1xuICAgIH0pO1xuICB9XG5cbiAgY3R4LnNlZW4ucG9wKCk7XG5cbiAgcmV0dXJuIHJlZHVjZVRvU2luZ2xlU3RyaW5nKG91dHB1dCwgYmFzZSwgYnJhY2VzKTtcbn1cblxuXG5mdW5jdGlvbiBmb3JtYXRQcmltaXRpdmUoY3R4LCB2YWx1ZSkge1xuICBpZiAoaXNVbmRlZmluZWQodmFsdWUpKVxuICAgIHJldHVybiBjdHguc3R5bGl6ZSgndW5kZWZpbmVkJywgJ3VuZGVmaW5lZCcpO1xuICBpZiAoaXNTdHJpbmcodmFsdWUpKSB7XG4gICAgdmFyIHNpbXBsZSA9ICdcXCcnICsgSlNPTi5zdHJpbmdpZnkodmFsdWUpLnJlcGxhY2UoL15cInxcIiQvZywgJycpXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAucmVwbGFjZSgvJy9nLCBcIlxcXFwnXCIpXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAucmVwbGFjZSgvXFxcXFwiL2csICdcIicpICsgJ1xcJyc7XG4gICAgcmV0dXJuIGN0eC5zdHlsaXplKHNpbXBsZSwgJ3N0cmluZycpO1xuICB9XG4gIGlmIChpc051bWJlcih2YWx1ZSkpXG4gICAgcmV0dXJuIGN0eC5zdHlsaXplKCcnICsgdmFsdWUsICdudW1iZXInKTtcbiAgaWYgKGlzQm9vbGVhbih2YWx1ZSkpXG4gICAgcmV0dXJuIGN0eC5zdHlsaXplKCcnICsgdmFsdWUsICdib29sZWFuJyk7XG4gIC8vIEZvciBzb21lIHJlYXNvbiB0eXBlb2YgbnVsbCBpcyBcIm9iamVjdFwiLCBzbyBzcGVjaWFsIGNhc2UgaGVyZS5cbiAgaWYgKGlzTnVsbCh2YWx1ZSkpXG4gICAgcmV0dXJuIGN0eC5zdHlsaXplKCdudWxsJywgJ251bGwnKTtcbn1cblxuXG5mdW5jdGlvbiBmb3JtYXRFcnJvcih2YWx1ZSkge1xuICByZXR1cm4gJ1snICsgRXJyb3IucHJvdG90eXBlLnRvU3RyaW5nLmNhbGwodmFsdWUpICsgJ10nO1xufVxuXG5cbmZ1bmN0aW9uIGZvcm1hdEFycmF5KGN0eCwgdmFsdWUsIHJlY3Vyc2VUaW1lcywgdmlzaWJsZUtleXMsIGtleXMpIHtcbiAgdmFyIG91dHB1dCA9IFtdO1xuICBmb3IgKHZhciBpID0gMCwgbCA9IHZhbHVlLmxlbmd0aDsgaSA8IGw7ICsraSkge1xuICAgIGlmIChoYXNPd25Qcm9wZXJ0eSh2YWx1ZSwgU3RyaW5nKGkpKSkge1xuICAgICAgb3V0cHV0LnB1c2goZm9ybWF0UHJvcGVydHkoY3R4LCB2YWx1ZSwgcmVjdXJzZVRpbWVzLCB2aXNpYmxlS2V5cyxcbiAgICAgICAgICBTdHJpbmcoaSksIHRydWUpKTtcbiAgICB9IGVsc2Uge1xuICAgICAgb3V0cHV0LnB1c2goJycpO1xuICAgIH1cbiAgfVxuICBrZXlzLmZvckVhY2goZnVuY3Rpb24oa2V5KSB7XG4gICAgaWYgKCFrZXkubWF0Y2goL15cXGQrJC8pKSB7XG4gICAgICBvdXRwdXQucHVzaChmb3JtYXRQcm9wZXJ0eShjdHgsIHZhbHVlLCByZWN1cnNlVGltZXMsIHZpc2libGVLZXlzLFxuICAgICAgICAgIGtleSwgdHJ1ZSkpO1xuICAgIH1cbiAgfSk7XG4gIHJldHVybiBvdXRwdXQ7XG59XG5cblxuZnVuY3Rpb24gZm9ybWF0UHJvcGVydHkoY3R4LCB2YWx1ZSwgcmVjdXJzZVRpbWVzLCB2aXNpYmxlS2V5cywga2V5LCBhcnJheSkge1xuICB2YXIgbmFtZSwgc3RyLCBkZXNjO1xuICBkZXNjID0gT2JqZWN0LmdldE93blByb3BlcnR5RGVzY3JpcHRvcih2YWx1ZSwga2V5KSB8fCB7IHZhbHVlOiB2YWx1ZVtrZXldIH07XG4gIGlmIChkZXNjLmdldCkge1xuICAgIGlmIChkZXNjLnNldCkge1xuICAgICAgc3RyID0gY3R4LnN0eWxpemUoJ1tHZXR0ZXIvU2V0dGVyXScsICdzcGVjaWFsJyk7XG4gICAgfSBlbHNlIHtcbiAgICAgIHN0ciA9IGN0eC5zdHlsaXplKCdbR2V0dGVyXScsICdzcGVjaWFsJyk7XG4gICAgfVxuICB9IGVsc2Uge1xuICAgIGlmIChkZXNjLnNldCkge1xuICAgICAgc3RyID0gY3R4LnN0eWxpemUoJ1tTZXR0ZXJdJywgJ3NwZWNpYWwnKTtcbiAgICB9XG4gIH1cbiAgaWYgKCFoYXNPd25Qcm9wZXJ0eSh2aXNpYmxlS2V5cywga2V5KSkge1xuICAgIG5hbWUgPSAnWycgKyBrZXkgKyAnXSc7XG4gIH1cbiAgaWYgKCFzdHIpIHtcbiAgICBpZiAoY3R4LnNlZW4uaW5kZXhPZihkZXNjLnZhbHVlKSA8IDApIHtcbiAgICAgIGlmIChpc051bGwocmVjdXJzZVRpbWVzKSkge1xuICAgICAgICBzdHIgPSBmb3JtYXRWYWx1ZShjdHgsIGRlc2MudmFsdWUsIG51bGwpO1xuICAgICAgfSBlbHNlIHtcbiAgICAgICAgc3RyID0gZm9ybWF0VmFsdWUoY3R4LCBkZXNjLnZhbHVlLCByZWN1cnNlVGltZXMgLSAxKTtcbiAgICAgIH1cbiAgICAgIGlmIChzdHIuaW5kZXhPZignXFxuJykgPiAtMSkge1xuICAgICAgICBpZiAoYXJyYXkpIHtcbiAgICAgICAgICBzdHIgPSBzdHIuc3BsaXQoJ1xcbicpLm1hcChmdW5jdGlvbihsaW5lKSB7XG4gICAgICAgICAgICByZXR1cm4gJyAgJyArIGxpbmU7XG4gICAgICAgICAgfSkuam9pbignXFxuJykuc3Vic3RyKDIpO1xuICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgIHN0ciA9ICdcXG4nICsgc3RyLnNwbGl0KCdcXG4nKS5tYXAoZnVuY3Rpb24obGluZSkge1xuICAgICAgICAgICAgcmV0dXJuICcgICAnICsgbGluZTtcbiAgICAgICAgICB9KS5qb2luKCdcXG4nKTtcbiAgICAgICAgfVxuICAgICAgfVxuICAgIH0gZWxzZSB7XG4gICAgICBzdHIgPSBjdHguc3R5bGl6ZSgnW0NpcmN1bGFyXScsICdzcGVjaWFsJyk7XG4gICAgfVxuICB9XG4gIGlmIChpc1VuZGVmaW5lZChuYW1lKSkge1xuICAgIGlmIChhcnJheSAmJiBrZXkubWF0Y2goL15cXGQrJC8pKSB7XG4gICAgICByZXR1cm4gc3RyO1xuICAgIH1cbiAgICBuYW1lID0gSlNPTi5zdHJpbmdpZnkoJycgKyBrZXkpO1xuICAgIGlmIChuYW1lLm1hdGNoKC9eXCIoW2EtekEtWl9dW2EtekEtWl8wLTldKilcIiQvKSkge1xuICAgICAgbmFtZSA9IG5hbWUuc3Vic3RyKDEsIG5hbWUubGVuZ3RoIC0gMik7XG4gICAgICBuYW1lID0gY3R4LnN0eWxpemUobmFtZSwgJ25hbWUnKTtcbiAgICB9IGVsc2Uge1xuICAgICAgbmFtZSA9IG5hbWUucmVwbGFjZSgvJy9nLCBcIlxcXFwnXCIpXG4gICAgICAgICAgICAgICAgIC5yZXBsYWNlKC9cXFxcXCIvZywgJ1wiJylcbiAgICAgICAgICAgICAgICAgLnJlcGxhY2UoLyheXCJ8XCIkKS9nLCBcIidcIik7XG4gICAgICBuYW1lID0gY3R4LnN0eWxpemUobmFtZSwgJ3N0cmluZycpO1xuICAgIH1cbiAgfVxuXG4gIHJldHVybiBuYW1lICsgJzogJyArIHN0cjtcbn1cblxuXG5mdW5jdGlvbiByZWR1Y2VUb1NpbmdsZVN0cmluZyhvdXRwdXQsIGJhc2UsIGJyYWNlcykge1xuICB2YXIgbnVtTGluZXNFc3QgPSAwO1xuICB2YXIgbGVuZ3RoID0gb3V0cHV0LnJlZHVjZShmdW5jdGlvbihwcmV2LCBjdXIpIHtcbiAgICBudW1MaW5lc0VzdCsrO1xuICAgIGlmIChjdXIuaW5kZXhPZignXFxuJykgPj0gMCkgbnVtTGluZXNFc3QrKztcbiAgICByZXR1cm4gcHJldiArIGN1ci5yZXBsYWNlKC9cXHUwMDFiXFxbXFxkXFxkP20vZywgJycpLmxlbmd0aCArIDE7XG4gIH0sIDApO1xuXG4gIGlmIChsZW5ndGggPiA2MCkge1xuICAgIHJldHVybiBicmFjZXNbMF0gK1xuICAgICAgICAgICAoYmFzZSA9PT0gJycgPyAnJyA6IGJhc2UgKyAnXFxuICcpICtcbiAgICAgICAgICAgJyAnICtcbiAgICAgICAgICAgb3V0cHV0LmpvaW4oJyxcXG4gICcpICtcbiAgICAgICAgICAgJyAnICtcbiAgICAgICAgICAgYnJhY2VzWzFdO1xuICB9XG5cbiAgcmV0dXJuIGJyYWNlc1swXSArIGJhc2UgKyAnICcgKyBvdXRwdXQuam9pbignLCAnKSArICcgJyArIGJyYWNlc1sxXTtcbn1cblxuXG4vLyBOT1RFOiBUaGVzZSB0eXBlIGNoZWNraW5nIGZ1bmN0aW9ucyBpbnRlbnRpb25hbGx5IGRvbid0IHVzZSBgaW5zdGFuY2VvZmBcbi8vIGJlY2F1c2UgaXQgaXMgZnJhZ2lsZSBhbmQgY2FuIGJlIGVhc2lseSBmYWtlZCB3aXRoIGBPYmplY3QuY3JlYXRlKClgLlxuZnVuY3Rpb24gaXNBcnJheShhcikge1xuICByZXR1cm4gQXJyYXkuaXNBcnJheShhcik7XG59XG5leHBvcnRzLmlzQXJyYXkgPSBpc0FycmF5O1xuXG5mdW5jdGlvbiBpc0Jvb2xlYW4oYXJnKSB7XG4gIHJldHVybiB0eXBlb2YgYXJnID09PSAnYm9vbGVhbic7XG59XG5leHBvcnRzLmlzQm9vbGVhbiA9IGlzQm9vbGVhbjtcblxuZnVuY3Rpb24gaXNOdWxsKGFyZykge1xuICByZXR1cm4gYXJnID09PSBudWxsO1xufVxuZXhwb3J0cy5pc051bGwgPSBpc051bGw7XG5cbmZ1bmN0aW9uIGlzTnVsbE9yVW5kZWZpbmVkKGFyZykge1xuICByZXR1cm4gYXJnID09IG51bGw7XG59XG5leHBvcnRzLmlzTnVsbE9yVW5kZWZpbmVkID0gaXNOdWxsT3JVbmRlZmluZWQ7XG5cbmZ1bmN0aW9uIGlzTnVtYmVyKGFyZykge1xuICByZXR1cm4gdHlwZW9mIGFyZyA9PT0gJ251bWJlcic7XG59XG5leHBvcnRzLmlzTnVtYmVyID0gaXNOdW1iZXI7XG5cbmZ1bmN0aW9uIGlzU3RyaW5nKGFyZykge1xuICByZXR1cm4gdHlwZW9mIGFyZyA9PT0gJ3N0cmluZyc7XG59XG5leHBvcnRzLmlzU3RyaW5nID0gaXNTdHJpbmc7XG5cbmZ1bmN0aW9uIGlzU3ltYm9sKGFyZykge1xuICByZXR1cm4gdHlwZW9mIGFyZyA9PT0gJ3N5bWJvbCc7XG59XG5leHBvcnRzLmlzU3ltYm9sID0gaXNTeW1ib2w7XG5cbmZ1bmN0aW9uIGlzVW5kZWZpbmVkKGFyZykge1xuICByZXR1cm4gYXJnID09PSB2b2lkIDA7XG59XG5leHBvcnRzLmlzVW5kZWZpbmVkID0gaXNVbmRlZmluZWQ7XG5cbmZ1bmN0aW9uIGlzUmVnRXhwKHJlKSB7XG4gIHJldHVybiBpc09iamVjdChyZSkgJiYgb2JqZWN0VG9TdHJpbmcocmUpID09PSAnW29iamVjdCBSZWdFeHBdJztcbn1cbmV4cG9ydHMuaXNSZWdFeHAgPSBpc1JlZ0V4cDtcblxuZnVuY3Rpb24gaXNPYmplY3QoYXJnKSB7XG4gIHJldHVybiB0eXBlb2YgYXJnID09PSAnb2JqZWN0JyAmJiBhcmcgIT09IG51bGw7XG59XG5leHBvcnRzLmlzT2JqZWN0ID0gaXNPYmplY3Q7XG5cbmZ1bmN0aW9uIGlzRGF0ZShkKSB7XG4gIHJldHVybiBpc09iamVjdChkKSAmJiBvYmplY3RUb1N0cmluZyhkKSA9PT0gJ1tvYmplY3QgRGF0ZV0nO1xufVxuZXhwb3J0cy5pc0RhdGUgPSBpc0RhdGU7XG5cbmZ1bmN0aW9uIGlzRXJyb3IoZSkge1xuICByZXR1cm4gaXNPYmplY3QoZSkgJiZcbiAgICAgIChvYmplY3RUb1N0cmluZyhlKSA9PT0gJ1tvYmplY3QgRXJyb3JdJyB8fCBlIGluc3RhbmNlb2YgRXJyb3IpO1xufVxuZXhwb3J0cy5pc0Vycm9yID0gaXNFcnJvcjtcblxuZnVuY3Rpb24gaXNGdW5jdGlvbihhcmcpIHtcbiAgcmV0dXJuIHR5cGVvZiBhcmcgPT09ICdmdW5jdGlvbic7XG59XG5leHBvcnRzLmlzRnVuY3Rpb24gPSBpc0Z1bmN0aW9uO1xuXG5mdW5jdGlvbiBpc1ByaW1pdGl2ZShhcmcpIHtcbiAgcmV0dXJuIGFyZyA9PT0gbnVsbCB8fFxuICAgICAgICAgdHlwZW9mIGFyZyA9PT0gJ2Jvb2xlYW4nIHx8XG4gICAgICAgICB0eXBlb2YgYXJnID09PSAnbnVtYmVyJyB8fFxuICAgICAgICAgdHlwZW9mIGFyZyA9PT0gJ3N0cmluZycgfHxcbiAgICAgICAgIHR5cGVvZiBhcmcgPT09ICdzeW1ib2wnIHx8ICAvLyBFUzYgc3ltYm9sXG4gICAgICAgICB0eXBlb2YgYXJnID09PSAndW5kZWZpbmVkJztcbn1cbmV4cG9ydHMuaXNQcmltaXRpdmUgPSBpc1ByaW1pdGl2ZTtcblxuZXhwb3J0cy5pc0J1ZmZlciA9IHJlcXVpcmUoJy4vc3VwcG9ydC9pc0J1ZmZlcicpO1xuXG5mdW5jdGlvbiBvYmplY3RUb1N0cmluZyhvKSB7XG4gIHJldHVybiBPYmplY3QucHJvdG90eXBlLnRvU3RyaW5nLmNhbGwobyk7XG59XG5cblxuZnVuY3Rpb24gcGFkKG4pIHtcbiAgcmV0dXJuIG4gPCAxMCA/ICcwJyArIG4udG9TdHJpbmcoMTApIDogbi50b1N0cmluZygxMCk7XG59XG5cblxudmFyIG1vbnRocyA9IFsnSmFuJywgJ0ZlYicsICdNYXInLCAnQXByJywgJ01heScsICdKdW4nLCAnSnVsJywgJ0F1ZycsICdTZXAnLFxuICAgICAgICAgICAgICAnT2N0JywgJ05vdicsICdEZWMnXTtcblxuLy8gMjYgRmViIDE2OjE5OjM0XG5mdW5jdGlvbiB0aW1lc3RhbXAoKSB7XG4gIHZhciBkID0gbmV3IERhdGUoKTtcbiAgdmFyIHRpbWUgPSBbcGFkKGQuZ2V0SG91cnMoKSksXG4gICAgICAgICAgICAgIHBhZChkLmdldE1pbnV0ZXMoKSksXG4gICAgICAgICAgICAgIHBhZChkLmdldFNlY29uZHMoKSldLmpvaW4oJzonKTtcbiAgcmV0dXJuIFtkLmdldERhdGUoKSwgbW9udGhzW2QuZ2V0TW9udGgoKV0sIHRpbWVdLmpvaW4oJyAnKTtcbn1cblxuXG4vLyBsb2cgaXMganVzdCBhIHRoaW4gd3JhcHBlciB0byBjb25zb2xlLmxvZyB0aGF0IHByZXBlbmRzIGEgdGltZXN0YW1wXG5leHBvcnRzLmxvZyA9IGZ1bmN0aW9uKCkge1xuICBjb25zb2xlLmxvZygnJXMgLSAlcycsIHRpbWVzdGFtcCgpLCBleHBvcnRzLmZvcm1hdC5hcHBseShleHBvcnRzLCBhcmd1bWVudHMpKTtcbn07XG5cblxuLyoqXG4gKiBJbmhlcml0IHRoZSBwcm90b3R5cGUgbWV0aG9kcyBmcm9tIG9uZSBjb25zdHJ1Y3RvciBpbnRvIGFub3RoZXIuXG4gKlxuICogVGhlIEZ1bmN0aW9uLnByb3RvdHlwZS5pbmhlcml0cyBmcm9tIGxhbmcuanMgcmV3cml0dGVuIGFzIGEgc3RhbmRhbG9uZVxuICogZnVuY3Rpb24gKG5vdCBvbiBGdW5jdGlvbi5wcm90b3R5cGUpLiBOT1RFOiBJZiB0aGlzIGZpbGUgaXMgdG8gYmUgbG9hZGVkXG4gKiBkdXJpbmcgYm9vdHN0cmFwcGluZyB0aGlzIGZ1bmN0aW9uIG5lZWRzIHRvIGJlIHJld3JpdHRlbiB1c2luZyBzb21lIG5hdGl2ZVxuICogZnVuY3Rpb25zIGFzIHByb3RvdHlwZSBzZXR1cCB1c2luZyBub3JtYWwgSmF2YVNjcmlwdCBkb2VzIG5vdCB3b3JrIGFzXG4gKiBleHBlY3RlZCBkdXJpbmcgYm9vdHN0cmFwcGluZyAoc2VlIG1pcnJvci5qcyBpbiByMTE0OTAzKS5cbiAqXG4gKiBAcGFyYW0ge2Z1bmN0aW9ufSBjdG9yIENvbnN0cnVjdG9yIGZ1bmN0aW9uIHdoaWNoIG5lZWRzIHRvIGluaGVyaXQgdGhlXG4gKiAgICAgcHJvdG90eXBlLlxuICogQHBhcmFtIHtmdW5jdGlvbn0gc3VwZXJDdG9yIENvbnN0cnVjdG9yIGZ1bmN0aW9uIHRvIGluaGVyaXQgcHJvdG90eXBlIGZyb20uXG4gKi9cbmV4cG9ydHMuaW5oZXJpdHMgPSByZXF1aXJlKCdpbmhlcml0cycpO1xuXG5leHBvcnRzLl9leHRlbmQgPSBmdW5jdGlvbihvcmlnaW4sIGFkZCkge1xuICAvLyBEb24ndCBkbyBhbnl0aGluZyBpZiBhZGQgaXNuJ3QgYW4gb2JqZWN0XG4gIGlmICghYWRkIHx8ICFpc09iamVjdChhZGQpKSByZXR1cm4gb3JpZ2luO1xuXG4gIHZhciBrZXlzID0gT2JqZWN0LmtleXMoYWRkKTtcbiAgdmFyIGkgPSBrZXlzLmxlbmd0aDtcbiAgd2hpbGUgKGktLSkge1xuICAgIG9yaWdpbltrZXlzW2ldXSA9IGFkZFtrZXlzW2ldXTtcbiAgfVxuICByZXR1cm4gb3JpZ2luO1xufTtcblxuZnVuY3Rpb24gaGFzT3duUHJvcGVydHkob2JqLCBwcm9wKSB7XG4gIHJldHVybiBPYmplY3QucHJvdG90eXBlLmhhc093blByb3BlcnR5LmNhbGwob2JqLCBwcm9wKTtcbn1cbiJdfQ==
