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
'use strict';

function _interopRequireWildcard(obj) { if (obj && obj.__esModule) { return obj; } else { var newObj = {}; if (obj != null) { for (var key in obj) { if (Object.prototype.hasOwnProperty.call(obj, key)) newObj[key] = obj[key]; } } newObj['default'] = obj; return newObj; } }

var _domainsTypes = require('../domains/types');

var types = _interopRequireWildcard(_domainsTypes);

var _utilMyWalker = require('../util/myWalker');

var myWalker = _interopRequireWildcard(_utilMyWalker);

var _domainsContext = require('../domains/context');

var csc = _interopRequireWildcard(_domainsContext);

var walk = require('acorn/dist/walk');
var status = require('../domains/status');
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
function clearConstraints() {
    visitedStatus.length = 0;
}

var rtCX = undefined;
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

    // constraint generating walker for expressions
    var constraintGenerator = walk.make({

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

                var _propAccess2 = propAccess(node.left);

                var accType = _propAccess2[0];
                var propName = _propAccess2[1];

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
                console.info('Assignment using pattern is not implemented');
            }
        },

        VariableDeclaration: function VariableDeclaration(node, curStatus, c) {
            for (var i = 0; i < node.declarations.length; i++) {
                var decl = node.declarations[i];
                var lhsAVal = curStatus.sc.getAValOf(decl.id.name);
                // declared var node is 'id'
                Ĉ.set(decl.id, curStatus.delta, lhsAVal);
                if (decl.init) {
                    var rhsAVal = c(decl.init, curStatus, undefined);
                    Ĉ.set(decl.init, curStatus.delta, rhsAVal);
                    rhsAVal.propagate(lhsAVal);
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
            var excAVal = catchBlockSC.getAValOf(node.handler.param.name);

            // for try block
            var tryStatus = curStatus.getNewStatus({ exc: excAVal });
            c(node.block, tryStatus, undefined);

            // for catch block
            var catchStatus = curStatus.getNewStatus({ sc: catchBlockSC });
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

    var outAVal = myWalker.recursiveWithReturn(astNode, initStatus, constraintGenerator);
    if (outAVal) {
        // must be an expression body
        outAVal.propagate(initStatus.ret);
    }
    // We actually added constraints
    return true;
}

exports.addConstraints = addConstraints;
exports.clearConstraints = clearConstraints;

},{"../domains/context":4,"../domains/status":5,"../domains/types":6,"../util/myWalker":12,"./constraints":3,"acorn/dist/walk":17}],3:[function(require,module,exports){
'use strict';

function _interopRequireWildcard(obj) { if (obj && obj.__esModule) { return obj; } else { var newObj = {}; if (obj != null) { for (var key in obj) { if (Object.prototype.hasOwnProperty.call(obj, key)) newObj[key] = obj[key]; } } newObj['default'] = obj; return newObj; } }

var _domainsTypes = require('../domains/types');

var types = _interopRequireWildcard(_domainsTypes);

var _domainsStatus = require('../domains/status');

var status = _interopRequireWildcard(_domainsStatus);

var _domainsContext = require('../domains/context');

var csc = _interopRequireWildcard(_domainsContext);

var cGen = require('./cGen');

function CSTR() {}
CSTR.prototype = Object.create(null);
CSTR.prototype.equals = function (other) {
    return this === other;
};

function ReadProp(prop, to) {
    this.prop = prop;
    this.to = to;
}
ReadProp.prototype = Object.create(CSTR.prototype);
ReadProp.prototype.addType = function (obj) {
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
        obj.getProp('__proto__').propagate(new ReadProp(this.prop, this.to));
    }
};
ReadProp.prototype.equals = function (other) {
    if (!(other instanceof ReadProp)) return false;
    return this.prop === other.prop && this.to.equals(other.to);
};

function WriteProp(prop, from) {
    this.prop = prop;
    this.from = from;
}
WriteProp.prototype = Object.create(CSTR.prototype);
WriteProp.prototype.addType = function (obj) {
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

function IsAdded(other, target) {
    this.other = other;
    this.target = target;
}
IsAdded.prototype = Object.create(CSTR.prototype);
IsAdded.prototype.addType = function (type) {
    if ((type === types.PrimNumber || type === types.PrimBoolean) && (this.other.hasType(types.PrimNumber) || this.other.hasType(types.PrimBoolean))) {
        this.target.addType(types.PrimNumber);
    }
    if (type === types.PrimString && !this.other.isEmpty()) {
        this.target.addType(types.PrimString);
    }
};

function IsCallee(self, args, ret, exc, delta) {
    this.self = self;
    this.args = args;
    this.ret = ret;
    this.exc = exc;
    this.delta = delta;
}
IsCallee.prototype = Object.create(CSTR.prototype);
IsCallee.prototype.addType = function (f) {
    if (!(f instanceof types.FnType)) return;
    var deltaFn = this.delta.truncateFor(f);

    var _f$getFunEnv = f.getFunEnv(deltaFn);

    var selfAVal = _f$getFunEnv[0];
    var retAVal = _f$getFunEnv[1];
    var excAVal = _f$getFunEnv[2];

    var newSC = f.originNode.body['@block'].getScopeInstance(f.sc, deltaFn);
    var funStatus = new status.Status(selfAVal, retAVal, excAVal, deltaFn, newSC);

    // arrow function should use boundThis and ignore the receiver AVal
    if (f.boundThis) {
        f.boundThis.propagate(selfAVal);
    } else {
        this.self.propagate(selfAVal);
    }

    var minLen = Math.min(this.args.length, f.paramNames.length);
    for (var i = 0; i < minLen; i++) {
        this.args[i].propagate(newSC.getAValOf(f.paramNames[i]));
    }

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

function IsCtor(args, ret, exc, delta) {
    this.args = args;
    this.ret = ret;
    this.exc = exc;
    this.delta = delta;
}
IsCtor.prototype = Object.create(CSTR.prototype);
IsCtor.prototype.addType = function (f) {
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

    var minLen = Math.min(this.args.length, f.paramNames.length);
    for (var i = 0; i < minLen; i++) {
        this.args[i].propagate(newSC.getAValOf(f.paramNames[i]));
    }

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

// ignore non object types
function IfObjType(aval) {
    this.aval = aval;
}
IfObjType.prototype = Object.create(CSTR.prototype);
IfObjType.prototype.addType = function (type) {
    if (!(type instanceof types.ObjType)) return;
    this.aval.addType(type);
};

exports.ReadProp = ReadProp;
exports.WriteProp = WriteProp;
exports.IsAdded = IsAdded;
exports.IsCallee = IsCallee;
exports.IsCtor = IsCtor;

},{"../domains/context":4,"../domains/status":5,"../domains/types":6,"./cGen":2}],4:[function(require,module,exports){
// Context for k-CFA analysis
//
// Assume a context is an array of numbers.
// A number in such list denotes a call site, that is @label of a CallExpression.
// We keep the most recent 'k' call-sites.
// Equality on contexts should look into the numbers.

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

function changeSensitivityParameter(param) {
    sensitivityParameter.maxDepthK = param.maxDepthK;
    sensitivityParameter.contextLengthOfFunc = param.contextLengthOfFunc;
}

// Functional objects for call-site context

var CallSiteContext = (function () {
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

    // Declaring class fields for CallSiteContext

    /**
     * A private method for context equality
     * @param list - array composed of context elements
     * @returns {boolean}
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
     * Return the context which is myself + callSite.
     * If I am nullContext, the result is myself.
     * @param callSite - a call-site to append
     * @returns {CallSiteContext}
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
     * @returns {CallSiteContext}
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

    CallSiteContext.prototype.toString = function toString() {
        return this.csList.toString();
    };

    return CallSiteContext;
})();

exports.CallSiteContext = CallSiteContext;
CallSiteContext.contextPool = new Set();
// nullContext is for functions that never be called
CallSiteContext.nullContext = new CallSiteContext(null);
// epsilonContext is for context of length 0
CallSiteContext.epsilonContext = new CallSiteContext([]);

},{}],5:[function(require,module,exports){
// Status:
// { self  : AVal,
//   ret   : AVal,
//   exc   : AVal,
//   delta : Context,
//   sc    : Scope }

"use strict";

exports.__esModule = true;

function _classCallCheck(instance, Constructor) { if (!(instance instanceof Constructor)) { throw new TypeError("Cannot call a class as a function"); } }

var Status = (function () {
    function Status(self, ret, exc, delta, sc) {
        _classCallCheck(this, Status);

        this.self = self;
        this.ret = ret;
        this.exc = exc;
        this.delta = delta;
        this.sc = sc;
    }

    Status.prototype.equals = function equals(other) {
        return this.self === other.self && this.ret === other.ret && this.exc === other.exc && this.delta === other.delta && this.sc === other.sc;
    };

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
// for DEBUG
'use strict';

exports.__esModule = true;
exports.mkObjFromGlobalScope = mkObjFromGlobalScope;

function _inherits(subClass, superClass) { if (typeof superClass !== 'function' && superClass !== null) { throw new TypeError('Super expression must either be null or a function, not ' + typeof superClass); } subClass.prototype = Object.create(superClass && superClass.prototype, { constructor: { value: subClass, enumerable: false, writable: true, configurable: true } }); if (superClass) Object.setPrototypeOf ? Object.setPrototypeOf(subClass, superClass) : subClass.__proto__ = superClass; }

function _classCallCheck(instance, Constructor) { if (!(instance instanceof Constructor)) { throw new TypeError('Cannot call a class as a function'); } }

var count = 0;
/**
 * the abstract value for a concrete value
 * which is a set of types.
 */

var AVal = (function () {
    /**
     * @param {Type} type - give a type to make AVal with a single type
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

    /** Check whether it has any type
     * @returns {boolean}
     */

    AVal.prototype.isEmpty = function isEmpty() {
        return this.types.size === 0;
    };

    AVal.prototype.getSize = function getSize() {
        return this.types.size;
    };

    /**
     * @returns {Set.<Type>}
     */

    AVal.prototype.getTypes = function getTypes() {
        return this.types;
    };

    /**
     * @param {Type} type
     * @returns {boolean}
     */

    AVal.prototype.hasType = function hasType(type) {
        return this.types.has(type);
    };

    /**
     * Add a type.
     * @param {Type} type
     * @returns {boolean}
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
     * @returns {boolean} - returns false if it already has the target
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
     * @returns {boolean}
     */

    AVal.prototype.equals = function equals(other) {
        // simple reference comparison
        return this === other;
    };

    /**
     * TODO: check whether we really need this method.
     * @param {string|null} prop
     * @returns {AVal}
     */

    AVal.prototype.getProp = function getProp(prop) {
        if (this.props.has(prop)) {
            return this.props.get(prop);
        } else {
            return AValNull;
        }
    };

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
     * @returns {string}
     */

    Type.prototype.getName = function getName() {
        return this.name;
    };

    /**
     * Default implementation for toString
     * This should be overridden for sophisticated types
     * @returns {string}
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

    // make an Obj from the global scope

    /**
     * @param {string|null} prop - null for computed props
     * @param {boolean} readOnly - if false, create AVal for prop if necessary
     * @returns {AVal} AVal of the property
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
     * @returns {Iterator.<string>}
     */

    ObjType.prototype.getOwnPropNames = function getOwnPropNames() {
        return this.props.keys();
    };

    /**
     * TODO: Check this function's necessity
     * @param {string|null} prop
     * @returns {boolean}
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
     * @returns {string}
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
     * @constructor
     */

    /**
     * construct Status for function
     * @param {CallContext} delta - call context
     * @returns {[AVal, AVal, AVal]} - for self, return and exception AVals
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
     * @returns {ObjType}
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
        var innerScopes = this.originNode.body['@block'].getScopeWithParent(this.sc);
        var paramInfo = [];
        for (var i = 0; i < this.paramNames.length; i++) {
            var paramName = this.paramNames[i];
            var strings = [];
            var hasType = false;
            for (var _iterator4 = innerScopes, _isArray4 = Array.isArray(_iterator4), _i4 = 0, _iterator4 = _isArray4 ? _iterator4 : _iterator4[Symbol.iterator]();;) {
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

                var aval = sc.getAValOf(paramName);
                if (!aval.isEmpty()) {
                    strings.push(aval._toString(visitedTypes));
                    hasType = true;
                }
            }
            var typeString = hasType ? strings.join('|') : undefined;
            paramInfo.push({ name: paramName, type: typeString });
        }
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

    FnType.prototype.getOneLevelStructure = function getOneLevelStructure() {
        var visitedTypes = new Set();
        return this._getOneLevelStructure(visitedTypes);
    };

    return FnType;
})(ObjType);

exports.FnType = FnType;

var ArrType = (function (_ObjType2) {
    _inherits(ArrType, _ObjType2);

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
     * @returns {*}
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
     * To use av made by others (e.g. scope)
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
     * @returns {boolean}
     */

    AbsCache.prototype.has = function has(loc, ctx) {
        return this.map.has(loc) && this.map.get(loc).has(ctx);
    };

    /**
     * Merge all AVal of the loc
     * @param loc
     * @returns {AVal}
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
        }
        return mergedAVal;
    };

    return AbsCache;
})();

exports.AbsCache = AbsCache;

},{}],7:[function(require,module,exports){
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
 * @returns {{hasType: boolean, typeString: string, nodeStart: number, nodeEnd: number}}
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

function computeIconOfProp(propMap) {
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
 * @returns {Map.<string, string>} - Mapping from prop to icon
 */

function getPropFromNode(Ĉ, node) {
    // Since getTypeOfLoc can return null if node does not have any types
    var nodeTypes = Ĉ.getMergedAValOfLoc(node);
    var propMap = getReadablePropMap(nodeTypes);
    return computeIconOfProp(propMap);
}

/**
 * For debugging, show x
 * @param x
 */
function SHOW(x) {
    console.info(x);
    return x;
}

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
        var varMap = computeIconOfProp(getReadableVarMap(nodeInfo.vb));

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
        return SHOW({ list: list, from: from, to: to });
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
        return SHOW({ list: list, from: from, to: to });
    }
}

function unionMap(m1, m2) {
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

function addOnlyMissingMappings(m1, m2) {
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
function convertMap(map) {
    var retMap = new Map();
    map.forEach(function (av, p) {
        retMap.set(p, av.getTypes());
    });
    return retMap;
}

// traverse abstract heap space
function getReadablePropMap(tps) {

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
                    protoMap = unionMap(protoMap, traverse(tp));
                    visitedTypes.pop();
                });
                return {
                    v: addOnlyMissingMappings(convertMap(type.props), protoMap)
                };
            })();

            if (typeof _ret === 'object') return _ret.v;
        } else {
            return new Map();
        }
    }

    var retMap = new Map();
    tps.getTypes().forEach(function (tp) {
        retMap = unionMap(retMap, traverse(tp));
    });

    return retMap;
}

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
function getReadableVarMap(vb) {
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

            mergedMap = unionMap(mergedMap, convertMap(varMap));
        }
        retMap = addOnlyMissingMappings(retMap, mergedMap);
        currVB = currVB.paren;
    }
    return retMap;
}

},{"./domains/types":6,"./util/myWalker":12}],8:[function(require,module,exports){
'use strict';

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

exports.getNodeList = getNodeList;
exports.showUnfolded = showUnfolded;

},{"util":21}],9:[function(require,module,exports){
// import necessary libraries
'use strict';

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

exports.analyze = analyze;
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
'use strict';

function _interopRequireWildcard(obj) { if (obj && obj.__esModule) { return obj; } else { var newObj = {}; if (obj != null) { for (var key in obj) { if (Object.prototype.hasOwnProperty.call(obj, key)) newObj[key] = obj[key]; } } newObj['default'] = obj; return newObj; } }

var _utilMyWalker = require('./util/myWalker');

var myWalker = _interopRequireWildcard(_utilMyWalker);

/**
 * auxiliary function for visitor's state change
 * @param node
 * @param st
 * @param nodeType
 * @returns {*}
 */
var walk = require('acorn/dist/walk');
function stChange(node, st, nodeType) {
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
 * @returns {*} - function node or null
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
    undefined,
    // stChange
    stChange);

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
 * @returns {*} - array of AST nodes
 */
function getEscapingNodes(nodePair) {
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
    }, walk.base), undefined, undefined, stChange);

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
 * @returns {Array} - array of AST nodes of escaping statements
 */
function findEscapingStatements(ast, pos, includeKeyword) {
    'use strict';

    var nodePair = onEscapingStatement(ast, pos);
    if (!nodePair) {
        return null;
    }

    var ranges = getEscapingNodes(nodePair).map(function (node) {
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

exports.onEscapingStatement = onEscapingStatement;
exports.findEscapingStatements = findEscapingStatements;

},{"./util/myWalker":12,"acorn/dist/walk":17}],11:[function(require,module,exports){
'use strict';

function _interopRequireWildcard(obj) { if (obj && obj.__esModule) { return obj; } else { var newObj = {}; if (obj != null) { for (var key in obj) { if (Object.prototype.hasOwnProperty.call(obj, key)) newObj[key] = obj[key]; } } newObj['default'] = obj; return newObj; } }

var _utilMyWalker = require('./util/myWalker');

var myWalker = _interopRequireWildcard(_utilMyWalker);

/**
 * Check whether given pos is on a this keyword
 * @param ast - AST of a program
 * @param pos - index position
 * @returns {*} - function node or null
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
 * @returns {*} - array of AST nodes
 */
function getThisNodes(fNode) {
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
 * @returns {Array} - array of AST nodes of return statements
 */
function findThisExpressions(ast, pos, includeFunctionKeyword) {
    'use strict';

    var fNode = onThisKeyword(ast, pos);
    if (!fNode) {
        // pos is not on this keyword
        return null;
    }

    var rets = getThisNodes(fNode);
    if (includeFunctionKeyword) {
        rets.push({ start: fNode.start, end: fNode.start + 8 });
    }
    return rets;
}

exports.onThisKeyword = onThisKeyword;
exports.findThisExpressions = findThisExpressions;

},{"./util/myWalker":12,"acorn/dist/walk":17}],12:[function(require,module,exports){
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
 * @returns {Object}
 */
function makeNoopWalker() {
    var walker = Object.create(null);
    var noopFunc = function noopFunc() {};
    for (var _name in Object.getOwnPropertyNames(walk.base)) {
        walker[_name] = noopFunc;
    }
    return walker;
}
var noopWalker = makeNoopWalker();

exports.noopWalker = noopWalker;
/**
 * Check whether the pattern uses defaults
 * @param ptnNode - a pattern node
 * @returns {boolean}
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
 * @returns {*} - a new walker
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

var Found = function Found(info) {
    _classCallCheck(this, Found);

    this.info = info;
};

exports.Found = Found;

function isDummyIdNode(node) {
    if (node.type !== 'Identifier') {
        throw new Error('Should be an Identifier node');
    }
    return node.name === '✖' && node.start >= node.end;
}

function findIdentifierAt(ast, pos) {
    'use strict';
    return findNodeAt(ast, pos, function (node) {
        return node.type === 'Identifier' && !isDummyIdNode(node);
    });
}

function findMemberOrVariableAt(ast, pos) {
    'use strict';
    return findNodeAt(ast, pos, function (node) {
        return node.type === 'Identifier' && !isDummyIdNode(node) || node.type === 'MemberExpression' && (node.property.start <= pos && pos <= node.property.end ||
        // when prop is ✖
        node.property.end <= pos && pos <= node.property.start);
    });
}

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
 * @returns {*}
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
 * @returns {*}
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

function recursiveWithReturn(node, state, visitor) {
    function c(node, st, override) {
        return visitor[override || node.type](node, st, c);
    }
    return c(node, state);
}

},{"acorn/dist/walk":17}],13:[function(require,module,exports){
/*
 JavaScript는 global, function block, catch block에 변수가 달린다.
 ES6는 일반 block에도 달린다.

 VarBlock는 각 block에 달린 변수들을 나타낸다.
 - paren      : BlockVars, 바깥 block을 나타내는 객체
 - originLabel: number, 해당 BlockVars가 선언된 AST node의 @label
    origin이 될 수 있는 node는
    Function.body, CatchClause.block 두가지다.
    두가지 모두 BlockStatement이다.
 - isCatch    : boolean,
   * true  -> catch block
   * false -> function block, or global

 - paramVarNames : 매개변수 이름 목록, 매개 변수 순서대로
 - localVarNames : 지역 변수 이름 목록, 순서 무의미
    arguments를 사용하는 경우 localVarNames에 등장하고,
    arguments object를 사용하면 useArgumentsObject == true

 - (optional) useArgumentsObject: boolean
    함수 body block인 경우에만 사용 가능
    * true  : arguments object가 사용되었다.
      즉 함수 body에서 변수 arguments를 선언 없이 사용했다.
      이 경우, arguments는 함수의 지역 변수로 등록된다.
    * false 인 경우는 없다. 그럴거면 아예 변수 자체가 없다.

 - usedVariables : 각 block의 매개변수, 지역변수 중
   사용되는 위치가 있는 것들의 목록

 - instances : Delta -> VarBlock의 변수들 -> AVal
   getInstance(delta) 를 통해 같은 delta는 같은 mapping 주게 만듬

 - scopeInstances : [Scope]
   현재 VarBlock을 마지막으로 하는 Scope를 모두 모은다.
   getScopeInstance(delta, paren) 을 통해 같은 scope chain은
   같은 객체가 되도록 만든다.
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

    VarBlock.prototype.isGlobal = function isGlobal() {
        return this.blockType === VarBlock.blockTypes.globalBlock;
    };

    VarBlock.prototype.isOldFunctionBlock = function isOldFunctionBlock() {
        return this.blockType === VarBlock.blockTypes.oldFunctionBlock;
    };

    VarBlock.prototype.isArrowFunctionBlock = function isArrowFunctionBlock() {
        return this.blockType === VarBlock.blockTypes.arrowFunctionBlock;
    };

    VarBlock.prototype.isCatchBlock = function isCatchBlock() {
        return this.blockType === VarBlock.blockTypes.catchBlock;
    };

    VarBlock.prototype.isNormalBlock = function isNormalBlock() {
        return this.blockType === VarBlock.blockTypes.normalBlock;
    };

    VarBlock.prototype.isParameterBlock = function isParameterBlock() {
        return this.blockType === VarBlock.blockTypes.parameterBlock;
    };

    VarBlock.prototype.getLocalVarNames = function getLocalVarNames() {
        return this.localVarNames;
    };

    VarBlock.prototype.getParamVarNames = function getParamVarNames() {
        return this.paramVarNames;
    };

    VarBlock.prototype.getVarNames = function getVarNames() {
        return this.getLocalVarNames().concat(this.getParamVarNames());
    };

    VarBlock.prototype.hasLocalVar = function hasLocalVar(varName) {
        return this.localVarNames && this.localVarNames.indexOf(varName) > -1;
    };

    VarBlock.prototype.hasParamVar = function hasParamVar(varName) {
        return this.paramVarNames.indexOf(varName) > -1;
    };

    VarBlock.prototype.hasVar = function hasVar(varName) {
        return this.hasParamVar(varName) || this.hasLocalVar(varName);
    };

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

    VarBlock.prototype.addParamVar = function addParamVar(varName) {
        this.paramVarNames.push(varName);
    };

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

    VarBlock.prototype.addUsedVar = function addUsedVar(varName) {
        if (this.usedVariables.indexOf(varName) === -1) {
            this.usedVariables.push(varName);
        }
    };

    VarBlock.prototype.getUsedVarNames = function getUsedVarNames() {
        return this.usedVariables;
    };

    VarBlock.prototype.isUsedVar = function isUsedVar(varName) {
        return this.usedVariables.indexOf(varName) > -1;
    };

    // returns a mapping

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

    // returns an array

    VarBlock.prototype.getParamAVals = function getParamAVals(delta) {
        var instance = this.getInstance(delta);
        var params = [];
        this.getParamVarNames().forEach(function (name) {
            params.push(instance.get(name));
        });
        return params;
    };

    // returns an AVal

    VarBlock.prototype.getArgumentsAVal = function getArgumentsAVal(delta) {
        if (!this.useArgumentsObject) {
            throw new Error('Not for this VarBlock');
        }
        return this.getInstance(delta).get('arguments');
    };

    // get a Scope instance

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

    // get function's scope instances

    VarBlock.prototype.getScopeWithParent = function getScopeWithParent(pScope) {
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
 * @returns {boolean}
 */
function isUseStrict(stmt) {
    return stmt.type === 'ExpressionStatement' && stmt.expression.type === 'Literal' && stmt.expression.raw.slice(1, -1) === 'use strict';
}

var declaredVariableFinder = walk.make({
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
        var strictInner = currBlock.isStrict || node.body.body && node.body.body[0] && isUseStrict(node.body.body[0]);
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
var variableUsageCollector = walk.make({
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

function annotateBlockInfo(ast, gVarBlock) {
    ast['@block'] = gVarBlock;

    gVarBlock.isStrict = gVarBlock.isStrict || ast.body[0] && isUseStrict(ast.body[0]);

    walk.recursive(ast, [, gVarBlock], declaredVariableFinder);
    walk.recursive(ast, gVarBlock, variableUsageCollector);
    return ast;
}

// define Scope class

var Scope = (function () {
    function Scope(paren, varMap, vb) {
        _classCallCheck(this, Scope);

        this.paren = paren;
        this.varMap = varMap;
        this.vb = vb;
    }

    // find AVal of a variable in the chain

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

    // remove initial catch scopes from the chain

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
'use strict';

function _interopRequireWildcard(obj) { if (obj && obj.__esModule) { return obj; } else { var newObj = {}; if (obj != null) { for (var key in obj) { if (Object.prototype.hasOwnProperty.call(obj, key)) newObj[key] = obj[key]; } } newObj['default'] = obj; return newObj; } }

var _utilMyWalker = require('./util/myWalker');

var myWalker = _interopRequireWildcard(_utilMyWalker);

/**
 *
 * @param ast - scope annotated AST
 * @param {number} pos - character position
 * @returns {*} - array of AST nodes
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
    var refs = findRefsToVariable(found).map(function (node) {
        return { start: node.start, end: node.end };
    });
    refs.varName = found.node.name;

    return refs;
}

/**
 *
 * @param found - node and varBlock of the variable
 * @returns {Array} - array of AST nodes
 */
function findRefsToVariable(found) {
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

exports.findVarRefsAt = findVarRefsAt;

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
//# sourceMappingURL=data:application/json;charset:utf-8;base64,eyJ2ZXJzaW9uIjozLCJzb3VyY2VzIjpbIm5vZGVfbW9kdWxlcy9icm93c2VyaWZ5L25vZGVfbW9kdWxlcy9icm93c2VyLXBhY2svX3ByZWx1ZGUuanMiLCIvaG9tZS9zd2tpbS9XZWJzdG9ybVByb2plY3RzL2NhbGNpdW0vZGVmYXVsdE9wdGlvbi5qcyIsIi9ob21lL3N3a2ltL1dlYnN0b3JtUHJvamVjdHMvY2FsY2l1bS9saWIvY29uc3RyYWludC9jR2VuLmpzIiwiL2hvbWUvc3draW0vV2Vic3Rvcm1Qcm9qZWN0cy9jYWxjaXVtL2xpYi9jb25zdHJhaW50L2NvbnN0cmFpbnRzLmpzIiwiL2hvbWUvc3draW0vV2Vic3Rvcm1Qcm9qZWN0cy9jYWxjaXVtL2xpYi9kb21haW5zL2NvbnRleHQuanMiLCIvaG9tZS9zd2tpbS9XZWJzdG9ybVByb2plY3RzL2NhbGNpdW0vbGliL2RvbWFpbnMvc3RhdHVzLmpzIiwiL2hvbWUvc3draW0vV2Vic3Rvcm1Qcm9qZWN0cy9jYWxjaXVtL2xpYi9kb21haW5zL3R5cGVzLmpzIiwiL2hvbWUvc3draW0vV2Vic3Rvcm1Qcm9qZWN0cy9jYWxjaXVtL2xpYi9nZXRUeXBlRGF0YS5qcyIsIi9ob21lL3N3a2ltL1dlYnN0b3JtUHJvamVjdHMvY2FsY2l1bS9saWIvaGVscGVyLmpzIiwiL2hvbWUvc3draW0vV2Vic3Rvcm1Qcm9qZWN0cy9jYWxjaXVtL2xpYi9pbmZlci5qcyIsIi9ob21lL3N3a2ltL1dlYnN0b3JtUHJvamVjdHMvY2FsY2l1bS9saWIvcmV0T2NjdXIuanMiLCIvaG9tZS9zd2tpbS9XZWJzdG9ybVByb2plY3RzL2NhbGNpdW0vbGliL3RoaXNPY2N1ci5qcyIsIi9ob21lL3N3a2ltL1dlYnN0b3JtUHJvamVjdHMvY2FsY2l1bS9saWIvdXRpbC9teVdhbGtlci5qcyIsIi9ob21lL3N3a2ltL1dlYnN0b3JtUHJvamVjdHMvY2FsY2l1bS9saWIvdmFyQmxvY2suanMiLCIvaG9tZS9zd2tpbS9XZWJzdG9ybVByb2plY3RzL2NhbGNpdW0vbGliL3ZhcnJlZnMuanMiLCJub2RlX21vZHVsZXMvYWNvcm4vZGlzdC9hY29ybi5qcyIsIm5vZGVfbW9kdWxlcy9hY29ybi9kaXN0L2Fjb3JuX2xvb3NlLmpzIiwibm9kZV9tb2R1bGVzL2Fjb3JuL2Rpc3Qvd2Fsay5qcyIsIm5vZGVfbW9kdWxlcy9icm93c2VyaWZ5L25vZGVfbW9kdWxlcy9pbmhlcml0cy9pbmhlcml0c19icm93c2VyLmpzIiwibm9kZV9tb2R1bGVzL2Jyb3dzZXJpZnkvbm9kZV9tb2R1bGVzL3Byb2Nlc3MvYnJvd3Nlci5qcyIsIm5vZGVfbW9kdWxlcy9icm93c2VyaWZ5L25vZGVfbW9kdWxlcy91dGlsL3N1cHBvcnQvaXNCdWZmZXJCcm93c2VyLmpzIiwibm9kZV9tb2R1bGVzL2Jyb3dzZXJpZnkvbm9kZV9tb2R1bGVzL3V0aWwvdXRpbC5qcyJdLCJuYW1lcyI6W10sIm1hcHBpbmdzIjoiQUFBQTs7OztBQ0FPLElBQU0sT0FBTyxHQUFHO0FBQ25CLGVBQVcsRUFBRTtBQUNULG1CQUFXLEVBQUUsQ0FBQzs7Ozs7QUFLZCxrQkFBVSxFQUFFLFFBQVE7S0FDdkI7Ozs7QUFJRCxtQkFBZSxFQUFFLElBQUk7OztBQUdyQix3QkFBb0IsRUFBRTtBQUNsQixpQkFBUyxFQUFFLENBQUM7QUFDWiwyQkFBbUIsRUFBRSw2QkFBVSxFQUFFLEVBQUU7QUFDL0IsbUJBQU8sQ0FBQyxDQUFDO1NBQ1o7S0FDSjtDQUNKLENBQUM7Ozs7QUNyQkYsWUFBWSxDQUFDOzs7OzRCQUVVLGtCQUFrQjs7SUFBN0IsS0FBSzs7NEJBQ1Msa0JBQWtCOztJQUFoQyxRQUFROzs4QkFDQyxvQkFBb0I7O0lBQTdCLEdBQUc7O0FBQ2YsSUFBTSxJQUFJLEdBQUcsT0FBTyxDQUFDLGlCQUFpQixDQUFDLENBQUM7QUFDeEMsSUFBTSxNQUFNLEdBQUcsT0FBTyxDQUFDLG1CQUFtQixDQUFDLENBQUM7QUFDNUMsSUFBTSxJQUFJLEdBQUcsT0FBTyxDQUFDLGVBQWUsQ0FBQyxDQUFDOzs7QUFHdEMsU0FBUyxVQUFVLENBQUMsSUFBSSxFQUFFO0FBQ3RCLFFBQU0sSUFBSSxHQUFHLElBQUksQ0FBQyxRQUFRLENBQUM7QUFDM0IsUUFBSSxJQUFJLENBQUMsSUFBSSxLQUFLLFlBQVksSUFBSSxRQUFRLENBQUMsYUFBYSxDQUFDLElBQUksQ0FBQyxRQUFRLENBQUMsRUFBRTtBQUNyRSxlQUFPLENBQUMsZUFBZSxDQUFDLENBQUE7S0FDM0I7QUFDRCxRQUFJLENBQUMsSUFBSSxDQUFDLFFBQVEsRUFBRTtBQUNoQixlQUFPLENBQUMsV0FBVyxFQUFFLElBQUksQ0FBQyxJQUFJLENBQUMsQ0FBQztLQUNuQztBQUNELFFBQUksSUFBSSxDQUFDLElBQUksS0FBSyxTQUFTLEVBQUU7QUFDekIsWUFBSSxPQUFPLElBQUksQ0FBQyxLQUFLLEtBQUssUUFBUSxFQUM5QixPQUFPLENBQUMsZUFBZSxFQUFFLElBQUksQ0FBQyxLQUFLLENBQUMsQ0FBQztBQUN6QyxZQUFJLE9BQU8sSUFBSSxDQUFDLEtBQUssS0FBSyxRQUFROztBQUU5QixtQkFBTyxDQUFDLGVBQWUsRUFBRSxJQUFJLENBQUMsS0FBSyxHQUFHLEVBQUUsQ0FBQyxDQUFDO0tBQ2pEO0FBQ0QsV0FBTyxDQUFDLFVBQVUsRUFBRSxJQUFJLENBQUMsQ0FBQztDQUM3Qjs7QUFFRCxTQUFTLGNBQWMsQ0FBQyxFQUFFLEVBQUU7QUFDeEIsWUFBUSxFQUFFO0FBQ04sYUFBSyxHQUFHLENBQUMsQUFBQyxLQUFLLEdBQUcsQ0FBQyxBQUFDLEtBQUssR0FBRztBQUN4QixtQkFBTyxLQUFLLENBQUMsVUFBVSxDQUFDO0FBQUEsQUFDNUIsYUFBSyxHQUFHO0FBQ0osbUJBQU8sS0FBSyxDQUFDLFdBQVcsQ0FBQztBQUFBLEFBQzdCLGFBQUssUUFBUTtBQUNULG1CQUFPLEtBQUssQ0FBQyxVQUFVLENBQUM7QUFBQSxBQUM1QixhQUFLLE1BQU0sQ0FBQyxBQUFDLEtBQUssUUFBUTtBQUN0QixtQkFBTyxJQUFJLENBQUM7QUFBQSxLQUNuQjtDQUNKOztBQUVELFNBQVMsY0FBYyxDQUFDLEVBQUUsRUFBRTtBQUN4QixZQUFRLEVBQUU7QUFDTixhQUFLLElBQUksQ0FBQyxBQUFDLEtBQUssSUFBSSxDQUFDLEFBQUMsS0FBSyxLQUFLLENBQUMsQUFBQyxLQUFLLEtBQUssQ0FBQztBQUM3QyxhQUFLLEdBQUcsQ0FBQyxBQUFDLEtBQUssR0FBRyxDQUFDLEFBQUMsS0FBSyxJQUFJLENBQUMsQUFBQyxLQUFLLElBQUksQ0FBQztBQUN6QyxhQUFLLElBQUksQ0FBQyxBQUFDLEtBQUssWUFBWTtBQUN4QixtQkFBTyxJQUFJLENBQUM7QUFBQSxLQUNuQjtBQUNELFdBQU8sS0FBSyxDQUFDO0NBQ2hCOzs7O0FBSUQsSUFBTSxhQUFhLEdBQUcsRUFBRSxDQUFDO0FBQ3pCLFNBQVMsZ0JBQWdCLEdBQUc7QUFDeEIsaUJBQWEsQ0FBQyxNQUFNLEdBQUcsQ0FBQyxDQUFDO0NBQzVCOztBQUVELElBQUksSUFBSSxZQUFBLENBQUM7QUFDVCxTQUFTLGNBQWMsQ0FBQyxPQUFPLEVBQUUsVUFBVSxFQUFFLE9BQU8sRUFBRTs7O0FBR2xELFFBQUksR0FBRyxPQUFPLElBQUksSUFBSSxDQUFDO0FBQ3ZCLFFBQU0sQ0FBQyxHQUFHLElBQUksQ0FBQyxDQUFDLENBQUM7OztBQUdqQixTQUFLLElBQUksQ0FBQyxHQUFDLENBQUMsRUFBRSxDQUFDLEdBQUcsYUFBYSxDQUFDLE1BQU0sRUFBRSxDQUFDLEVBQUUsRUFBRTtBQUN6QyxZQUFJLFVBQVUsQ0FBQyxNQUFNLENBQUMsYUFBYSxDQUFDLENBQUMsQ0FBQyxDQUFDLEVBQUU7OztBQUdwQyxtQkFBTyxLQUFLLENBQUM7U0FDaEI7S0FDTDs7O0FBR0QsaUJBQWEsQ0FBQyxJQUFJLENBQUMsVUFBVSxDQUFDLENBQUM7O0FBRS9CLGFBQVMsVUFBVSxDQUFDLElBQUksRUFBRSxTQUFTLEVBQUUsQ0FBQyxFQUFFO0FBQ3BDLFlBQU0sR0FBRyxHQUFHLENBQUMsQ0FBQyxHQUFHLENBQUMsSUFBSSxFQUFFLFNBQVMsQ0FBQyxLQUFLLENBQUMsQ0FBQztBQUN6QyxZQUFNLE9BQU8sR0FBRyxDQUFDLENBQUMsSUFBSSxDQUFDLE1BQU0sRUFBRSxTQUFTLEVBQUUsU0FBUyxDQUFDLENBQUM7QUFDckQsWUFBSSxJQUFJLENBQUMsUUFBUSxDQUFDLElBQUksS0FBSyxZQUFZLEVBQUU7O0FBRXJDLGFBQUMsQ0FBQyxJQUFJLENBQUMsUUFBUSxFQUFFLFNBQVMsRUFBRSxTQUFTLENBQUMsQ0FBQztTQUMxQzs7MEJBQzJCLFVBQVUsQ0FBQyxJQUFJLENBQUM7O1lBQXJDLE9BQU87WUFBRSxRQUFROztBQUV4QixZQUFJLE9BQU8sS0FBSyxlQUFlLEVBQUU7QUFDN0IsbUJBQU8sQ0FBQyxTQUFTLENBQUMsSUFBSSxJQUFJLENBQUMsUUFBUSxDQUFDLFFBQVEsRUFBRSxHQUFHLENBQUMsQ0FBQyxDQUFDO1NBQ3ZEOzs7QUFHRCxlQUFPLENBQUMsT0FBTyxFQUFFLEdBQUcsQ0FBQyxDQUFDO0tBQ3pCOzs7QUFHRCxRQUFNLG1CQUFtQixHQUFHLElBQUksQ0FBQyxJQUFJLENBQUM7O0FBRWxDLGtCQUFVLEVBQUUsb0JBQVUsSUFBSSxFQUFFLFNBQVMsRUFBRSxDQUFDLEVBQUU7QUFDdEMsZ0JBQUksUUFBUSxDQUFDLGFBQWEsQ0FBQyxJQUFJLENBQUMsRUFBRTs7QUFFOUIsdUJBQU8sS0FBSyxDQUFDLFFBQVEsQ0FBQzthQUN6QjtBQUNELGdCQUFNLEVBQUUsR0FBRyxTQUFTLENBQUMsRUFBRSxDQUFDLFNBQVMsQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDLENBQUM7O0FBRTdDLGFBQUMsQ0FBQyxHQUFHLENBQUMsSUFBSSxFQUFFLFNBQVMsQ0FBQyxLQUFLLEVBQUUsRUFBRSxDQUFDLENBQUM7QUFDakMsbUJBQU8sRUFBRSxDQUFDO1NBQ2I7O0FBRUQsc0JBQWMsRUFBRSx3QkFBVSxJQUFJLEVBQUUsU0FBUyxFQUFFLENBQUMsRUFBRTtBQUMxQyxnQkFBTSxFQUFFLEdBQUcsU0FBUyxDQUFDLElBQUksQ0FBQzs7QUFFMUIsYUFBQyxDQUFDLEdBQUcsQ0FBQyxJQUFJLEVBQUUsU0FBUyxDQUFDLEtBQUssRUFBRSxFQUFFLENBQUMsQ0FBQztBQUNqQyxtQkFBTyxFQUFFLENBQUM7U0FDYjs7QUFFRCxlQUFPLEVBQUUsaUJBQVUsSUFBSSxFQUFFLFNBQVMsRUFBRSxDQUFDLEVBQUU7QUFDbkMsZ0JBQU0sR0FBRyxHQUFHLENBQUMsQ0FBQyxHQUFHLENBQUMsSUFBSSxFQUFFLFNBQVMsQ0FBQyxLQUFLLENBQUMsQ0FBQztBQUN6QyxnQkFBSSxJQUFJLENBQUMsS0FBSyxFQUFFOzs7QUFHWix1QkFBTyxHQUFHLENBQUM7YUFDZDtBQUNELG9CQUFRLE9BQU8sSUFBSSxDQUFDLEtBQUs7QUFDekIscUJBQUssUUFBUTtBQUNULHVCQUFHLENBQUMsT0FBTyxDQUFDLEtBQUssQ0FBQyxVQUFVLENBQUMsQ0FBQztBQUM5QiwwQkFBTTtBQUFBLEFBQ1YscUJBQUssUUFBUTtBQUNULHVCQUFHLENBQUMsT0FBTyxDQUFDLEtBQUssQ0FBQyxVQUFVLENBQUMsQ0FBQztBQUM5QiwwQkFBTTtBQUFBLEFBQ1YscUJBQUssU0FBUztBQUNWLHVCQUFHLENBQUMsT0FBTyxDQUFDLEtBQUssQ0FBQyxXQUFXLENBQUMsQ0FBQztBQUMvQiwwQkFBTTtBQUFBLEFBQ1YscUJBQUssUUFBUTs7O0FBR1QsMEJBQU07QUFBQSxBQUNWLHFCQUFLLFVBQVU7QUFDWCwwQkFBTSxJQUFJLEtBQUssQ0FBQyxzQ0FBc0MsQ0FBQyxDQUFDO0FBQUEsYUFDM0Q7QUFDRCxtQkFBTyxHQUFHLENBQUM7U0FDZDs7QUFFRCw0QkFBb0IsRUFBRSw4QkFBVSxJQUFJLEVBQUUsU0FBUyxFQUFFLENBQUMsRUFBRTtBQUNoRCxnQkFBTSxPQUFPLEdBQUcsQ0FBQyxDQUFDLElBQUksQ0FBQyxLQUFLLEVBQUUsU0FBUyxFQUFFLFNBQVMsQ0FBQyxDQUFDO0FBQ3BELGdCQUFJLElBQUksQ0FBQyxJQUFJLENBQUMsSUFBSSxLQUFLLFlBQVksRUFBRTs7QUFFakMsb0JBQU0sT0FBTyxHQUFHLElBQUksQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDO0FBQy9CLG9CQUFNLE9BQU8sR0FBRyxTQUFTLENBQUMsRUFBRSxDQUFDLFNBQVMsQ0FBQyxPQUFPLENBQUMsQ0FBQzs7O0FBR2hELGlCQUFDLENBQUMsR0FBRyxDQUFDLElBQUksQ0FBQyxJQUFJLEVBQUUsU0FBUyxDQUFDLEtBQUssRUFBRSxPQUFPLENBQUMsQ0FBQzs7QUFFM0Msb0JBQUksSUFBSSxDQUFDLFFBQVEsS0FBSyxHQUFHLEVBQUU7O0FBRXZCLDJCQUFPLENBQUMsU0FBUyxDQUFDLE9BQU8sQ0FBQyxDQUFDOztBQUUzQixxQkFBQyxDQUFDLEdBQUcsQ0FBQyxJQUFJLEVBQUUsU0FBUyxDQUFDLEtBQUssRUFBRSxPQUFPLENBQUMsQ0FBQztBQUN0QywyQkFBTyxPQUFPLENBQUM7aUJBQ2xCOztBQUVELG9CQUFNLE9BQU8sR0FBRyxDQUFDLENBQUMsR0FBRyxDQUFDLElBQUksRUFBRSxTQUFTLENBQUMsS0FBSyxDQUFDLENBQUM7QUFDN0Msb0JBQUksSUFBSSxDQUFDLFFBQVEsS0FBSyxJQUFJLEVBQUU7O0FBRXhCLDJCQUFPLENBQUMsU0FBUyxDQUFDLElBQUksSUFBSSxDQUFDLE9BQU8sQ0FBQyxPQUFPLEVBQUUsT0FBTyxDQUFDLENBQUMsQ0FBQztBQUN0RCwyQkFBTyxDQUFDLFNBQVMsQ0FBQyxJQUFJLElBQUksQ0FBQyxPQUFPLENBQUMsT0FBTyxFQUFFLE9BQU8sQ0FBQyxDQUFDLENBQUM7aUJBQ3pELE1BQU07O0FBRUgsMkJBQU8sQ0FBQyxPQUFPLENBQUMsS0FBSyxDQUFDLFVBQVUsQ0FBQyxDQUFDO2lCQUNyQztBQUNELHVCQUFPLE9BQU8sQ0FBQzthQUNsQixNQUFNLElBQUksSUFBSSxDQUFDLElBQUksQ0FBQyxJQUFJLEtBQUssa0JBQWtCLEVBQUU7QUFDOUMsb0JBQU0sT0FBTyxHQUFHLENBQUMsQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDLE1BQU0sRUFBRSxTQUFTLEVBQUUsU0FBUyxDQUFDLENBQUM7O21DQUM5QixVQUFVLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQzs7b0JBQTFDLE9BQU87b0JBQUUsUUFBUTs7QUFDeEIsb0JBQUksSUFBSSxDQUFDLFFBQVEsS0FBSyxHQUFHLEVBQUU7O0FBRXZCLHdCQUFJLE9BQU8sS0FBSyxlQUFlLEVBQUU7QUFDN0IsK0JBQU8sQ0FBQyxTQUFTLENBQUMsSUFBSSxJQUFJLENBQUMsU0FBUyxDQUFDLFFBQVEsRUFBRSxPQUFPLENBQUMsQ0FBQyxDQUFDO3FCQUM1RDs7QUFFRCx3QkFBSSxPQUFPLEtBQUssZUFBZSxFQUFFO0FBQzdCLCtCQUFPLENBQUMsU0FBUyxDQUFDLElBQUksSUFBSSxDQUFDLFNBQVMsQ0FBQyxJQUFJLEVBQUUsT0FBTyxDQUFDLENBQUMsQ0FBQztxQkFDeEQ7O0FBRUQscUJBQUMsQ0FBQyxHQUFHLENBQUMsSUFBSSxFQUFFLFNBQVMsQ0FBQyxLQUFLLEVBQUUsT0FBTyxDQUFDLENBQUM7QUFDdEMsMkJBQU8sT0FBTyxDQUFDO2lCQUNsQjs7QUFFRCxvQkFBTSxPQUFPLEdBQUcsQ0FBQyxDQUFDLEdBQUcsQ0FBQyxJQUFJLEVBQUUsU0FBUyxDQUFDLEtBQUssQ0FBQyxDQUFDOztrQ0FDekIsVUFBVSxDQUFDLElBQUksQ0FBQyxJQUFJLEVBQUUsU0FBUyxFQUFFLENBQUMsQ0FBQzs7b0JBQTlDLE9BQU87O0FBQ2hCLG9CQUFJLElBQUksQ0FBQyxRQUFRLEtBQUssSUFBSSxFQUFFOztBQUV4QiwyQkFBTyxDQUFDLFNBQVMsQ0FBQyxJQUFJLElBQUksQ0FBQyxPQUFPLENBQUMsT0FBTyxFQUFFLE9BQU8sQ0FBQyxDQUFDLENBQUM7QUFDdEQsMkJBQU8sQ0FBQyxTQUFTLENBQUMsSUFBSSxJQUFJLENBQUMsT0FBTyxDQUFDLE9BQU8sRUFBRSxPQUFPLENBQUMsQ0FBQyxDQUFDO2lCQUN6RCxNQUFNOztBQUVILDJCQUFPLENBQUMsT0FBTyxDQUFDLEtBQUssQ0FBQyxVQUFVLENBQUMsQ0FBQztpQkFDckM7QUFDRCx1QkFBTyxPQUFPLENBQUM7YUFDbEIsTUFBTTtBQUNILHVCQUFPLENBQUMsSUFBSSxDQUFDLDZDQUE2QyxDQUFDLENBQUM7YUFDL0Q7U0FDSjs7QUFFRCwyQkFBbUIsRUFBRSw2QkFBVSxJQUFJLEVBQUUsU0FBUyxFQUFFLENBQUMsRUFBRTtBQUMvQyxpQkFBSyxJQUFJLENBQUMsR0FBRyxDQUFDLEVBQUUsQ0FBQyxHQUFHLElBQUksQ0FBQyxZQUFZLENBQUMsTUFBTSxFQUFFLENBQUMsRUFBRSxFQUFFO0FBQy9DLG9CQUFNLElBQUksR0FBRyxJQUFJLENBQUMsWUFBWSxDQUFDLENBQUMsQ0FBQyxDQUFDO0FBQ2xDLG9CQUFNLE9BQU8sR0FBRyxTQUFTLENBQUMsRUFBRSxDQUFDLFNBQVMsQ0FBQyxJQUFJLENBQUMsRUFBRSxDQUFDLElBQUksQ0FBQyxDQUFDOztBQUVyRCxpQkFBQyxDQUFDLEdBQUcsQ0FBQyxJQUFJLENBQUMsRUFBRSxFQUFFLFNBQVMsQ0FBQyxLQUFLLEVBQUUsT0FBTyxDQUFDLENBQUM7QUFDekMsb0JBQUksSUFBSSxDQUFDLElBQUksRUFBRTtBQUNYLHdCQUFNLE9BQU8sR0FBRyxDQUFDLENBQUMsSUFBSSxDQUFDLElBQUksRUFBRSxTQUFTLEVBQUUsU0FBUyxDQUFDLENBQUM7QUFDbkQscUJBQUMsQ0FBQyxHQUFHLENBQUMsSUFBSSxDQUFDLElBQUksRUFBRSxTQUFTLENBQUMsS0FBSyxFQUFFLE9BQU8sQ0FBQyxDQUFDO0FBQzNDLDJCQUFPLENBQUMsU0FBUyxDQUFDLE9BQU8sQ0FBQyxDQUFDO2lCQUM5QjthQUNKO1NBQ0o7O0FBRUQseUJBQWlCLEVBQUUsMkJBQVUsSUFBSSxFQUFFLFNBQVMsRUFBRSxDQUFDLEVBQUU7QUFDN0MsZ0JBQU0sR0FBRyxHQUFHLENBQUMsQ0FBQyxHQUFHLENBQUMsSUFBSSxFQUFFLFNBQVMsQ0FBQyxLQUFLLENBQUMsQ0FBQztBQUN6QyxnQkFBTSxJQUFJLEdBQUcsQ0FBQyxDQUFDLElBQUksQ0FBQyxJQUFJLEVBQUUsU0FBUyxFQUFFLFNBQVMsQ0FBQyxDQUFDO0FBQ2hELGdCQUFNLEtBQUssR0FBRyxDQUFDLENBQUMsSUFBSSxDQUFDLEtBQUssRUFBRSxTQUFTLEVBQUUsU0FBUyxDQUFDLENBQUM7QUFDbEQsZ0JBQUksQ0FBQyxTQUFTLENBQUMsR0FBRyxDQUFDLENBQUM7QUFDcEIsaUJBQUssQ0FBQyxTQUFTLENBQUMsR0FBRyxDQUFDLENBQUM7QUFDckIsbUJBQU8sR0FBRyxDQUFDO1NBQ2Q7O0FBRUQsNkJBQXFCLEVBQUUsK0JBQVUsSUFBSSxFQUFFLFNBQVMsRUFBRSxDQUFDLEVBQUU7QUFDakQsZ0JBQU0sR0FBRyxHQUFHLENBQUMsQ0FBQyxHQUFHLENBQUMsSUFBSSxFQUFFLFNBQVMsQ0FBQyxLQUFLLENBQUMsQ0FBQztBQUN6QyxhQUFDLENBQUMsSUFBSSxDQUFDLElBQUksRUFBRSxTQUFTLEVBQUUsU0FBUyxDQUFDLENBQUM7QUFDbkMsZ0JBQU0sSUFBSSxHQUFHLENBQUMsQ0FBQyxJQUFJLENBQUMsVUFBVSxFQUFFLFNBQVMsRUFBRSxTQUFTLENBQUMsQ0FBQztBQUN0RCxnQkFBTSxHQUFHLEdBQUcsQ0FBQyxDQUFDLElBQUksQ0FBQyxTQUFTLEVBQUUsU0FBUyxFQUFFLFNBQVMsQ0FBQyxDQUFDO0FBQ3BELGdCQUFJLENBQUMsU0FBUyxDQUFDLEdBQUcsQ0FBQyxDQUFDO0FBQ3BCLGVBQUcsQ0FBQyxTQUFTLENBQUMsR0FBRyxDQUFDLENBQUM7QUFDbkIsbUJBQU8sR0FBRyxDQUFDO1NBQ2Q7O0FBRUQscUJBQWEsRUFBRSx1QkFBVSxJQUFJLEVBQUUsU0FBUyxFQUFFLENBQUMsRUFBRTtBQUN6QyxnQkFBTSxHQUFHLEdBQUcsQ0FBQyxDQUFDLEdBQUcsQ0FBQyxJQUFJLEVBQUUsU0FBUyxDQUFDLEtBQUssQ0FBQyxDQUFDO0FBQ3pDLGdCQUFNLE1BQU0sR0FBRyxDQUFDLENBQUMsSUFBSSxDQUFDLE1BQU0sRUFBRSxTQUFTLEVBQUUsU0FBUyxDQUFDLENBQUM7QUFDcEQsZ0JBQU0sSUFBSSxHQUFHLEVBQUUsQ0FBQztBQUNoQixpQkFBSyxJQUFJLENBQUMsR0FBRyxDQUFDLEVBQUUsQ0FBQyxHQUFHLElBQUksQ0FBQyxTQUFTLENBQUMsTUFBTSxFQUFFLENBQUMsRUFBRSxFQUFFO0FBQzVDLG9CQUFJLENBQUMsSUFBSSxDQUFDLENBQUMsQ0FBQyxJQUFJLENBQUMsU0FBUyxDQUFDLENBQUMsQ0FBQyxFQUFFLFNBQVMsRUFBRSxTQUFTLENBQUMsQ0FBQyxDQUFDO2FBQ3pEO0FBQ0QsZ0JBQU0sUUFBUSxHQUFHLFNBQVMsQ0FBQyxLQUFLLENBQUMsU0FBUyxDQUFDLElBQUksQ0FBQyxRQUFRLENBQUMsQ0FBQyxDQUFDO0FBQzNELGtCQUFNLENBQUMsU0FBUyxDQUNaLElBQUksSUFBSSxDQUFDLE1BQU0sQ0FDWCxJQUFJLEVBQ0osR0FBRyxFQUNILFNBQVMsQ0FBQyxHQUFHLEVBQ2IsUUFBUSxDQUFDLENBQUMsQ0FBQztBQUNuQixtQkFBTyxHQUFHLENBQUM7U0FDZDs7QUFFRCx1QkFBZSxFQUFFLHlCQUFVLElBQUksRUFBRSxTQUFTLEVBQUUsQ0FBQyxFQUFFO0FBQzNDLGdCQUFNLEdBQUcsR0FBRyxDQUFDLENBQUMsR0FBRyxDQUFDLElBQUksRUFBRSxTQUFTLENBQUMsS0FBSyxDQUFDLENBQUM7O0FBRXpDLGdCQUFNLE9BQU8sR0FBRyxJQUFJLEtBQUssQ0FBQyxPQUFPLENBQUMsSUFBSSxLQUFLLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQyxNQUFNLENBQUMsS0FBSyxDQUFDLENBQUMsQ0FBQzs7QUFFckUsbUJBQU8sQ0FBQyxPQUFPLENBQUMsUUFBUSxDQUFDLENBQUMsT0FBTyxDQUFDLEtBQUssQ0FBQyxVQUFVLENBQUMsQ0FBQzs7QUFFcEQsZUFBRyxDQUFDLE9BQU8sQ0FBQyxPQUFPLENBQUMsQ0FBQzs7O0FBR3JCLGlCQUFLLElBQUksQ0FBQyxHQUFHLENBQUMsRUFBRSxDQUFDLEdBQUcsSUFBSSxDQUFDLFFBQVEsQ0FBQyxNQUFNLEVBQUUsQ0FBQyxFQUFFLEVBQUU7QUFDM0Msb0JBQUksSUFBSSxDQUFDLFFBQVEsQ0FBQyxDQUFDLENBQUMsSUFBSSxJQUFJLEVBQUU7QUFDMUIsNkJBQVM7aUJBQ1o7QUFDRCxvQkFBTSxPQUFPLEdBQUcsQ0FBQyxDQUFDLElBQUksQ0FBQyxRQUFRLENBQUMsQ0FBQyxDQUFDLEVBQUUsU0FBUyxFQUFFLFNBQVMsQ0FBQyxDQUFDOztBQUUxRCxvQkFBTSxJQUFJLEdBQUcsQ0FBQyxHQUFHLEVBQUUsQ0FBQztBQUNwQixtQkFBRyxDQUFDLFNBQVMsQ0FBQyxJQUFJLElBQUksQ0FBQyxTQUFTLENBQUMsSUFBSSxFQUFFLE9BQU8sQ0FBQyxDQUFDLENBQUM7QUFDakQsbUJBQUcsQ0FBQyxTQUFTLENBQUMsSUFBSSxJQUFJLENBQUMsU0FBUyxDQUFDLElBQUksRUFBRSxPQUFPLENBQUMsQ0FBQyxDQUFDO2FBQ3BEO0FBQ0QsbUJBQU8sR0FBRyxDQUFDO1NBQ2Q7O0FBRUQsd0JBQWdCLEVBQUUsMEJBQVUsSUFBSSxFQUFFLFNBQVMsRUFBRSxDQUFDLEVBQUU7QUFDNUMsZ0JBQU0sR0FBRyxHQUFHLENBQUMsQ0FBQyxHQUFHLENBQUMsSUFBSSxFQUFFLFNBQVMsQ0FBQyxLQUFLLENBQUMsQ0FBQzs7QUFFekMsZ0JBQU0sT0FBTyxHQUFHLElBQUksS0FBSyxDQUFDLE9BQU8sQ0FBQyxJQUFJLEtBQUssQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDLE1BQU0sQ0FBQyxNQUFNLENBQUMsQ0FBQyxDQUFDO0FBQ3RFLGVBQUcsQ0FBQyxPQUFPLENBQUMsT0FBTyxDQUFDLENBQUM7O0FBRXJCLGlCQUFLLElBQUksQ0FBQyxHQUFHLENBQUMsRUFBRSxDQUFDLEdBQUcsSUFBSSxDQUFDLFVBQVUsQ0FBQyxNQUFNLEVBQUUsQ0FBQyxFQUFFLEVBQUU7QUFDN0Msb0JBQU0sUUFBUSxHQUFHLElBQUksQ0FBQyxVQUFVLENBQUMsQ0FBQyxDQUFDLENBQUM7QUFDcEMsb0JBQU0sT0FBTyxHQUFHLFFBQVEsQ0FBQyxHQUFHLENBQUM7QUFDN0Isb0JBQUksS0FBSSxZQUFBLENBQUM7QUFDVCxvQkFBTSxRQUFRLEdBQUcsUUFBUSxDQUFDLEtBQUssQ0FBQzs7QUFFaEMsb0JBQU0sT0FBTyxHQUFHLENBQUMsQ0FBQyxRQUFRLEVBQUUsU0FBUyxFQUFFLFNBQVMsQ0FBQyxDQUFDOztBQUVsRCxvQkFBSSxPQUFPLENBQUMsSUFBSSxLQUFLLFlBQVksRUFBRTtBQUMvQix5QkFBSSxHQUFHLE9BQU8sQ0FBQyxJQUFJLENBQUM7aUJBQ3ZCLE1BQU0sSUFBSSxPQUFPLE9BQU8sQ0FBQyxLQUFLLEtBQUssUUFBUSxFQUFFO0FBQzFDLHlCQUFJLEdBQUcsT0FBTyxDQUFDLEtBQUssQ0FBQztpQkFDeEIsTUFBTSxJQUFJLE9BQU8sT0FBTyxDQUFDLEtBQUssS0FBSyxRQUFRLEVBQUU7O0FBRTFDLHlCQUFJLEdBQUcsT0FBTyxDQUFDLEtBQUssR0FBRyxFQUFFLENBQUM7aUJBQzdCO0FBQ0QsbUJBQUcsQ0FBQyxTQUFTLENBQUMsSUFBSSxJQUFJLENBQUMsU0FBUyxDQUFDLEtBQUksRUFBRSxPQUFPLENBQUMsQ0FBQyxDQUFDO2FBQ3BEO0FBQ0QsbUJBQU8sR0FBRyxDQUFDO1NBQ2Q7O0FBRUQsK0JBQXVCLEVBQUUsaUNBQVUsSUFBSSxFQUFFLFNBQVMsRUFBRSxDQUFDLEVBQUU7QUFDbkQsZ0JBQUksQ0FBQyxJQUFJLENBQUMsV0FBVyxFQUFFO0FBQ25CLG9CQUFJLENBQUMsV0FBVyxHQUFHLEVBQUUsQ0FBQzthQUN6QjtBQUNELGdCQUFJLFVBQVUsR0FBRyxJQUFJLENBQUM7QUFDdEIsZ0JBQUksQ0FBQyxXQUFXLENBQUMsT0FBTyxDQUFDLFVBQVUsTUFBTSxFQUFFO0FBQ3ZDLG9CQUFJLE1BQU0sQ0FBQyxFQUFFLEtBQUssU0FBUyxDQUFDLEVBQUUsRUFBRTtBQUM1Qiw4QkFBVSxHQUFHLE1BQU0sQ0FBQztpQkFDdkI7YUFDSixDQUFDLENBQUM7QUFDSCxnQkFBSSxDQUFDLFVBQVUsRUFBRTtBQUNiLDBCQUFVLEdBQ0osSUFBSSxLQUFLLENBQUMsTUFBTSxDQUFDLElBQUksS0FBSyxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsTUFBTSxDQUFDLFFBQVEsQ0FBQyxFQUN2RCxrQkFBa0IsRUFDbEIsSUFBSSxDQUFDLElBQUksQ0FBQyxRQUFRLENBQUMsQ0FBQyxnQkFBZ0IsRUFBRSxFQUN0QyxTQUFTLENBQUMsRUFBRSxFQUNaLElBQUksRUFDSixTQUFTLEVBQ1QsU0FBUyxDQUFDLElBQUk7aUJBQ2pCLENBQUM7QUFDRixvQkFBSSxDQUFDLFdBQVcsQ0FBQyxJQUFJLENBQUMsVUFBVSxDQUFDLENBQUM7YUFDckM7QUFDRCxnQkFBTSxHQUFHLEdBQUcsQ0FBQyxDQUFDLEdBQUcsQ0FBQyxJQUFJLEVBQUUsU0FBUyxDQUFDLEtBQUssQ0FBQyxDQUFDO0FBQ3pDLGVBQUcsQ0FBQyxPQUFPLENBQUMsVUFBVSxDQUFDLENBQUM7O0FBRXhCLGVBQUcsQ0FBQyxTQUFTLENBQ1QsSUFBSSxJQUFJLENBQUMsUUFBUSxDQUNiLEtBQUssQ0FBQyxRQUFRO0FBQ2QsY0FBRTtBQUNGLGlCQUFLLENBQUMsUUFBUTtBQUNkLGlCQUFLLENBQUMsUUFBUTtBQUNkLGVBQUcsQ0FBQyxlQUFlLENBQUMsV0FBVzthQUNsQyxDQUNKLENBQUM7O0FBRUYsbUJBQU8sR0FBRyxDQUFDO1NBQ2Q7O0FBRUQsMEJBQWtCLEVBQUUsNEJBQVUsSUFBSSxFQUFFLFNBQVMsRUFBRSxDQUFDLEVBQUU7QUFDOUMsZ0JBQUksQ0FBQyxJQUFJLENBQUMsV0FBVyxFQUFFO0FBQ25CLG9CQUFJLENBQUMsV0FBVyxHQUFHLEVBQUUsQ0FBQzthQUN6QjtBQUNELGdCQUFJLFVBQVUsR0FBRyxJQUFJLENBQUM7QUFDdEIsZ0JBQUksQ0FBQyxXQUFXLENBQUMsT0FBTyxDQUFDLFVBQVUsTUFBTSxFQUFFO0FBQ3ZDLG9CQUFJLE1BQU0sQ0FBQyxFQUFFLEtBQUssU0FBUyxDQUFDLEVBQUUsRUFBRTtBQUM1Qiw4QkFBVSxHQUFHLE1BQU0sQ0FBQztpQkFDdkI7YUFDSixDQUFDLENBQUM7QUFDSCxnQkFBSSxDQUFDLFVBQVUsRUFBRTs7QUFFYiwwQkFBVSxHQUNKLElBQUksS0FBSyxDQUFDLE1BQU0sQ0FBQyxJQUFJLEtBQUssQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDLE1BQU0sQ0FBQyxRQUFRLENBQUMsRUFDcEMsc0JBQXNCLEVBQ3RCLElBQUksQ0FBQyxJQUFJLENBQUMsUUFBUSxDQUFDLENBQUMsZ0JBQWdCLEVBQUUsRUFDdEMsU0FBUyxDQUFDLEVBQUUsRUFDWixJQUFJLEVBQ0osSUFBSSxDQUFDLE1BQU0sQ0FBQyxNQUFNLENBQUMsQ0FBQztBQUMzQyxvQkFBSSxDQUFDLFdBQVcsQ0FBQyxJQUFJLENBQUMsVUFBVSxDQUFDLENBQUM7O0FBRWxDLG9CQUFNLGVBQWUsR0FDakIsSUFBSSxLQUFLLENBQUMsT0FBTyxDQUFDLElBQUksS0FBSyxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsTUFBTSxDQUFDLE1BQU0sQ0FBQyxFQUNsQyxZQUFZLENBQUMsQ0FBQzs7QUFFcEMsb0JBQUksS0FBSyxDQUFDLElBQUksQ0FBQyxVQUFVLENBQUMsQ0FBQyxTQUFTLENBQ2hDLElBQUksSUFBSSxDQUFDLFNBQVMsQ0FBQyxXQUFXLEVBQUMsSUFBSSxLQUFLLENBQUMsSUFBSSxDQUFDLGVBQWUsQ0FBQyxDQUFDLENBQ2xFLENBQUM7O0FBRUYsb0JBQU0sZUFBZSxHQUFHLGVBQWUsQ0FBQyxPQUFPLENBQUMsYUFBYSxDQUFDLENBQUM7QUFDL0QsK0JBQWUsQ0FBQyxPQUFPLENBQUMsVUFBVSxDQUFDLENBQUM7YUFDdkM7QUFDRCxnQkFBTSxHQUFHLEdBQUcsQ0FBQyxDQUFDLEdBQUcsQ0FBQyxJQUFJLEVBQUUsU0FBUyxDQUFDLEtBQUssQ0FBQyxDQUFDO0FBQ3pDLGVBQUcsQ0FBQyxPQUFPLENBQUMsVUFBVSxDQUFDLENBQUM7Ozs7d0NBR0gsVUFBVSxDQUFDLFNBQVMsQ0FBQyxHQUFHLENBQUMsZUFBZSxDQUFDLFdBQVcsQ0FBQzs7Z0JBQW5FLFFBQVE7OztBQUVmLG9CQUFRLENBQUMsT0FBTyxDQUFDLFVBQVUsQ0FBQyxXQUFXLEVBQUUsQ0FBQyxDQUFDO0FBQzNDLGVBQUcsQ0FBQyxTQUFTLENBQ1QsSUFBSSxJQUFJLENBQUMsUUFBUSxDQUNiLEtBQUssQ0FBQyxRQUFRO0FBQ2QsY0FBRTtBQUNGLGlCQUFLLENBQUMsUUFBUTtBQUNkLGlCQUFLLENBQUMsUUFBUTtBQUNkLGVBQUcsQ0FBQyxlQUFlLENBQUMsV0FBVzthQUNsQyxDQUNKLENBQUM7O0FBRUYsbUJBQU8sR0FBRyxDQUFDO1NBQ2Q7O0FBRUQsMkJBQW1CLEVBQUUsNkJBQVUsSUFBSSxFQUFFLFNBQVMsRUFBRSxDQUFDLEVBQUU7O0FBRS9DLGdCQUFNLEdBQUcsR0FBRyxTQUFTLENBQUMsRUFBRSxDQUFDLGdDQUFnQyxFQUFFLENBQUM7QUFDNUQsZ0JBQUksQ0FBQyxJQUFJLENBQUMsV0FBVyxFQUFFO0FBQ25CLG9CQUFJLENBQUMsV0FBVyxHQUFHLEVBQUUsQ0FBQzthQUN6QjtBQUNELGdCQUFJLFVBQVUsR0FBRyxJQUFJLENBQUM7QUFDdEIsZ0JBQUksQ0FBQyxXQUFXLENBQUMsT0FBTyxDQUFDLFVBQVUsTUFBTSxFQUFFO0FBQ3ZDLG9CQUFJLE1BQU0sQ0FBQyxFQUFFLEtBQUssR0FBRyxFQUFFO0FBQ25CLDhCQUFVLEdBQUcsTUFBTSxDQUFDO2lCQUN2QjthQUNKLENBQUMsQ0FBQztBQUNILGdCQUFJLENBQUMsVUFBVSxFQUFFOztBQUViLDBCQUFVLEdBQ0osSUFBSSxLQUFLLENBQUMsTUFBTSxDQUFDLElBQUksS0FBSyxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsTUFBTSxDQUFDLFFBQVEsQ0FBQyxFQUNwQyxJQUFJLENBQUMsRUFBRSxDQUFDLElBQUksRUFDWixJQUFJLENBQUMsSUFBSSxDQUFDLFFBQVEsQ0FBQyxDQUFDLGdCQUFnQixFQUFFLEVBQ3RDLEdBQUcsRUFDSCxJQUFJLEVBQ0osSUFBSSxDQUFDLE1BQU0sQ0FBQyxNQUFNLENBQUMsQ0FBQztBQUMzQyxvQkFBSSxDQUFDLFdBQVcsQ0FBQyxJQUFJLENBQUMsVUFBVSxDQUFDLENBQUM7OztBQUdsQyxvQkFBTSxlQUFlLEdBQ2pCLElBQUksS0FBSyxDQUFDLE9BQU8sQ0FBQyxJQUFJLEtBQUssQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDLE1BQU0sQ0FBQyxNQUFNLENBQUMsRUFDbEMsSUFBSSxDQUFDLEVBQUUsQ0FBQyxJQUFJLEdBQUcsWUFBWSxDQUFDLENBQUM7O0FBRW5ELG9CQUFJLEtBQUssQ0FBQyxJQUFJLENBQUMsVUFBVSxDQUFDLENBQUMsU0FBUyxDQUNoQyxJQUFJLElBQUksQ0FBQyxTQUFTLENBQUMsV0FBVyxFQUFFLElBQUksS0FBSyxDQUFDLElBQUksQ0FBQyxlQUFlLENBQUMsQ0FBQyxDQUNuRSxDQUFDOztBQUVGLG9CQUFNLGVBQWUsR0FBRyxlQUFlLENBQUMsT0FBTyxDQUFDLGFBQWEsQ0FBQyxDQUFDO0FBQy9ELCtCQUFlLENBQUMsT0FBTyxDQUFDLFVBQVUsQ0FBQyxDQUFDO2FBQ3ZDO0FBQ0QsZ0JBQU0sT0FBTyxHQUFHLEdBQUcsQ0FBQyxTQUFTLENBQUMsSUFBSSxDQUFDLEVBQUUsQ0FBQyxJQUFJLENBQUMsQ0FBQztBQUM1QyxtQkFBTyxDQUFDLE9BQU8sQ0FBQyxVQUFVLENBQUMsQ0FBQzs7Ozt5Q0FHUCxVQUFVLENBQUMsU0FBUyxDQUFDLEdBQUcsQ0FBQyxlQUFlLENBQUMsV0FBVyxDQUFDOztnQkFBbkUsUUFBUTs7O0FBRWYsb0JBQVEsQ0FBQyxPQUFPLENBQUMsVUFBVSxDQUFDLFdBQVcsRUFBRSxDQUFDLENBQUM7QUFDM0MsbUJBQU8sQ0FBQyxTQUFTLENBQ2IsSUFBSSxJQUFJLENBQUMsUUFBUSxDQUNiLEtBQUssQ0FBQyxRQUFRO0FBQ2QsY0FBRTtBQUNGLGlCQUFLLENBQUMsUUFBUTtBQUNkLGlCQUFLLENBQUMsUUFBUTtBQUNkLGVBQUcsQ0FBQyxlQUFlLENBQUMsV0FBVzthQUNsQyxDQUNKLENBQUM7OztBQUdGLG1CQUFPLEtBQUssQ0FBQyxRQUFRLENBQUM7U0FDekI7O0FBRUQsMEJBQWtCLEVBQUUsNEJBQVUsSUFBSSxFQUFFLFNBQVMsRUFBRSxDQUFDLEVBQUU7QUFDOUMsZ0JBQU0sU0FBUyxHQUFHLElBQUksQ0FBQyxXQUFXLENBQUMsTUFBTSxHQUFHLENBQUMsQ0FBQztBQUM5QyxpQkFBSyxJQUFJLENBQUMsR0FBRyxDQUFDLEVBQUUsQ0FBQyxHQUFHLFNBQVMsRUFBRSxDQUFDLEVBQUUsRUFBRTtBQUNoQyxpQkFBQyxDQUFDLElBQUksQ0FBQyxXQUFXLENBQUMsQ0FBQyxDQUFDLEVBQUUsU0FBUyxFQUFFLFNBQVMsQ0FBQyxDQUFDO2FBQ2hEO0FBQ0QsZ0JBQU0sUUFBUSxHQUFHLENBQUMsQ0FBQyxJQUFJLENBQUMsV0FBVyxDQUFDLFNBQVMsQ0FBQyxFQUFFLFNBQVMsRUFBRSxTQUFTLENBQUMsQ0FBQztBQUN0RSxhQUFDLENBQUMsR0FBRyxDQUFDLElBQUksRUFBRSxTQUFTLENBQUMsS0FBSyxFQUFFLFFBQVEsQ0FBQyxDQUFDO0FBQ3ZDLG1CQUFPLFFBQVEsQ0FBQztTQUNuQjs7QUFFRCx1QkFBZSxFQUFFLHlCQUFVLElBQUksRUFBRSxTQUFTLEVBQUUsQ0FBQyxFQUFFO0FBQzNDLGFBQUMsQ0FBQyxJQUFJLENBQUMsUUFBUSxFQUFFLFNBQVMsRUFBRSxTQUFTLENBQUMsQ0FBQztBQUN2QyxnQkFBTSxHQUFHLEdBQUcsQ0FBQyxDQUFDLEdBQUcsQ0FBQyxJQUFJLEVBQUUsU0FBUyxDQUFDLEtBQUssQ0FBQyxDQUFDO0FBQ3pDLGdCQUFNLElBQUksR0FBRyxjQUFjLENBQUMsSUFBSSxDQUFDLFFBQVEsQ0FBQyxDQUFDO0FBQzNDLGdCQUFJLElBQUksRUFBRTtBQUNOLG1CQUFHLENBQUMsT0FBTyxDQUFDLElBQUksQ0FBQyxDQUFDO2FBQ3JCO0FBQ0QsbUJBQU8sR0FBRyxDQUFDO1NBQ2Q7O0FBRUQsd0JBQWdCLEVBQUUsMEJBQVUsSUFBSSxFQUFFLFNBQVMsRUFBRSxDQUFDLEVBQUU7QUFDNUMsYUFBQyxDQUFDLElBQUksQ0FBQyxRQUFRLEVBQUUsU0FBUyxFQUFFLFNBQVMsQ0FBQyxDQUFDO0FBQ3ZDLGdCQUFNLEdBQUcsR0FBRyxDQUFDLENBQUMsR0FBRyxDQUFDLElBQUksRUFBRSxTQUFTLENBQUMsS0FBSyxDQUFDLENBQUM7QUFDekMsZUFBRyxDQUFDLE9BQU8sQ0FBQyxLQUFLLENBQUMsVUFBVSxDQUFDLENBQUM7O0FBRTlCLG1CQUFPLEdBQUcsQ0FBQztTQUNkOztBQUVELHdCQUFnQixFQUFFLDBCQUFVLElBQUksRUFBRSxTQUFTLEVBQUUsQ0FBQyxFQUFFO0FBQzVDLGdCQUFNLEtBQUssR0FBRyxDQUFDLENBQUMsSUFBSSxDQUFDLElBQUksRUFBRSxTQUFTLEVBQUUsU0FBUyxDQUFDLENBQUM7QUFDakQsZ0JBQU0sS0FBSyxHQUFHLENBQUMsQ0FBQyxJQUFJLENBQUMsS0FBSyxFQUFFLFNBQVMsRUFBRSxTQUFTLENBQUMsQ0FBQztBQUNsRCxnQkFBTSxHQUFHLEdBQUcsQ0FBQyxDQUFDLEdBQUcsQ0FBQyxJQUFJLEVBQUUsU0FBUyxDQUFDLEtBQUssQ0FBQyxDQUFDOztBQUV6QyxnQkFBSSxJQUFJLENBQUMsUUFBUSxJQUFJLEdBQUcsRUFBRTtBQUN0QixxQkFBSyxDQUFDLFNBQVMsQ0FBQyxJQUFJLElBQUksQ0FBQyxPQUFPLENBQUMsS0FBSyxFQUFFLEdBQUcsQ0FBQyxDQUFDLENBQUM7QUFDOUMscUJBQUssQ0FBQyxTQUFTLENBQUMsSUFBSSxJQUFJLENBQUMsT0FBTyxDQUFDLEtBQUssRUFBRSxHQUFHLENBQUMsQ0FBQyxDQUFDO2FBQ2pELE1BQU07QUFDSCxvQkFBSSxjQUFjLENBQUMsSUFBSSxDQUFDLFFBQVEsQ0FBQyxFQUFFO0FBQy9CLHVCQUFHLENBQUMsT0FBTyxDQUFDLEtBQUssQ0FBQyxXQUFXLENBQUMsQ0FBQztpQkFDbEMsTUFBTTtBQUNILHVCQUFHLENBQUMsT0FBTyxDQUFDLEtBQUssQ0FBQyxVQUFVLENBQUMsQ0FBQztpQkFDakM7YUFDSjtBQUNELG1CQUFPLEdBQUcsQ0FBQztTQUNkOztBQUVELG9CQUFZLEVBQUUsc0JBQVUsSUFBSSxFQUFFLFNBQVMsRUFBRSxDQUFDLEVBQUU7QUFDeEMsZ0JBQUksSUFBSSxDQUFDLFFBQVEsQ0FBQyxFQUFFOztBQUVoQixvQkFBTSxVQUFVLEdBQ1osSUFBSSxDQUFDLFFBQVEsQ0FBQyxDQUFDLGdCQUFnQixDQUFDLFNBQVMsQ0FBQyxFQUFFLEVBQUUsU0FBUyxDQUFDLEtBQUssQ0FBQyxDQUFDO0FBQ25FLHlCQUFTLEdBQUcsU0FBUyxDQUFDLFlBQVksQ0FBQyxFQUFDLEVBQUUsRUFBRSxVQUFVLEVBQUMsQ0FBQyxDQUFDO2FBQ3hEO0FBQ0QsZ0JBQUksQ0FBQyxJQUFJLENBQUMsWUFBWSxDQUFDLElBQUksRUFBRSxTQUFTLEVBQUUsQ0FBQyxDQUFDLENBQUM7U0FDOUM7O0FBRUQsc0JBQWMsRUFBRSx3QkFBVSxJQUFJLEVBQUUsU0FBUyxFQUFFLENBQUMsRUFBRTtBQUMxQyxnQkFBSSxJQUFJLENBQUMsUUFBUSxDQUFDLEVBQUU7O0FBRWhCLG9CQUFNLGFBQWEsR0FDZixJQUFJLENBQUMsUUFBUSxDQUFDLENBQUMsZ0JBQWdCLENBQUMsU0FBUyxDQUFDLEVBQUUsRUFBRSxTQUFTLENBQUMsS0FBSyxDQUFDLENBQUM7QUFDbkUseUJBQVMsR0FBRyxTQUFTLENBQUMsWUFBWSxDQUFDLEVBQUMsRUFBRSxFQUFFLGFBQWEsRUFBQyxDQUFDLENBQUM7YUFDM0Q7QUFDRCxnQkFBSSxDQUFDLElBQUksQ0FBQyxjQUFjLENBQUMsSUFBSSxFQUFFLFNBQVMsRUFBRSxDQUFDLENBQUMsQ0FBQztTQUNoRDs7QUFFRCxvQkFBWSxFQUFFLHNCQUFVLElBQUksRUFBRSxTQUFTLEVBQUUsQ0FBQyxFQUFFOztBQUV4QyxnQkFBTSxZQUFZLEdBQ2QsSUFBSSxDQUFDLE9BQU8sQ0FBQyxJQUFJLENBQUMsUUFBUSxDQUFDLENBQzFCLGdCQUFnQixDQUFDLFNBQVMsQ0FBQyxFQUFFLEVBQUUsU0FBUyxDQUFDLEtBQUssQ0FBQyxDQUFDOztBQUVyRCxnQkFBTSxPQUFPLEdBQUcsWUFBWSxDQUFDLFNBQVMsQ0FBQyxJQUFJLENBQUMsT0FBTyxDQUFDLEtBQUssQ0FBQyxJQUFJLENBQUMsQ0FBQzs7O0FBR2hFLGdCQUFNLFNBQVMsR0FBRyxTQUFTLENBQUMsWUFBWSxDQUFDLEVBQUMsR0FBRyxFQUFFLE9BQU8sRUFBQyxDQUFDLENBQUM7QUFDekQsYUFBQyxDQUFDLElBQUksQ0FBQyxLQUFLLEVBQUUsU0FBUyxFQUFFLFNBQVMsQ0FBQyxDQUFDOzs7QUFHcEMsZ0JBQU0sV0FBVyxHQUFHLFNBQVMsQ0FBQyxZQUFZLENBQUMsRUFBQyxFQUFFLEVBQUUsWUFBWSxFQUFDLENBQUMsQ0FBQztBQUMvRCxhQUFDLENBQUMsSUFBSSxDQUFDLE9BQU8sQ0FBQyxJQUFJLEVBQUUsV0FBVyxFQUFFLFNBQVMsQ0FBQyxDQUFDOzs7QUFHN0MsZ0JBQUksSUFBSSxDQUFDLFNBQVMsS0FBSyxJQUFJLEVBQ3ZCLENBQUMsQ0FBQyxJQUFJLENBQUMsU0FBUyxFQUFFLFNBQVMsRUFBRSxTQUFTLENBQUMsQ0FBQztTQUMvQzs7QUFFRCxzQkFBYyxFQUFFLHdCQUFVLElBQUksRUFBRSxTQUFTLEVBQUUsQ0FBQyxFQUFFO0FBQzFDLGdCQUFNLEdBQUcsR0FBRyxDQUFDLENBQUMsSUFBSSxDQUFDLFFBQVEsRUFBRSxTQUFTLEVBQUUsU0FBUyxDQUFDLENBQUM7QUFDbkQsZUFBRyxDQUFDLFNBQVMsQ0FBQyxTQUFTLENBQUMsR0FBRyxDQUFDLENBQUM7U0FDaEM7O0FBRUQsc0JBQWMsRUFBRSx3QkFBVSxJQUFJLEVBQUUsU0FBUyxFQUFFLENBQUMsRUFBRTtBQUMxQyxnQkFBTSxPQUFPLEdBQUcsQ0FBQyxDQUFDLEdBQUcsQ0FBQyxJQUFJLEVBQUUsU0FBUyxDQUFDLEtBQUssQ0FBQyxDQUFDO0FBQzdDLGdCQUFNLFFBQVEsR0FBRyxFQUFFLENBQUM7OztBQUdwQixpQkFBSyxJQUFJLENBQUMsR0FBRyxDQUFDLEVBQUUsQ0FBQyxHQUFHLElBQUksQ0FBQyxTQUFTLENBQUMsTUFBTSxFQUFFLENBQUMsRUFBRSxFQUFFO0FBQzVDLHdCQUFRLENBQUMsSUFBSSxDQUNULENBQUMsQ0FBQyxJQUFJLENBQUMsU0FBUyxDQUFDLENBQUMsQ0FBQyxFQUFFLFNBQVMsRUFBRSxTQUFTLENBQUMsQ0FBQyxDQUFDO2FBQ25EOztBQUVELGdCQUFNLFFBQVEsR0FBRyxTQUFTLENBQUMsS0FBSyxDQUFDLFNBQVMsQ0FBQyxJQUFJLENBQUMsUUFBUSxDQUFDLENBQUMsQ0FBQzs7QUFFM0QsZ0JBQUksSUFBSSxDQUFDLE1BQU0sQ0FBQyxJQUFJLEtBQUssa0JBQWtCLEVBQUU7OzttQ0FFYixVQUFVLENBQUMsSUFBSSxDQUFDLE1BQU0sRUFBRSxTQUFTLEVBQUUsQ0FBQyxDQUFDOztvQkFBMUQsUUFBUTtvQkFBRSxPQUFPOztBQUN4Qix1QkFBTyxDQUFDLFNBQVMsQ0FDYixJQUFJLElBQUksQ0FBQyxRQUFRLENBQ2IsUUFBUSxFQUNSLFFBQVEsRUFDUixPQUFPLEVBQ1AsU0FBUyxDQUFDLEdBQUcsRUFDYixRQUFRLENBQUMsQ0FBQyxDQUFDO2FBQ3RCLE1BQU07O0FBRUgsb0JBQU0sVUFBVSxHQUFHLENBQUMsQ0FBQyxJQUFJLENBQUMsTUFBTSxFQUFFLFNBQVMsRUFBRSxTQUFTLENBQUMsQ0FBQzs7O0FBR3hELDBCQUFVLENBQUMsU0FBUyxDQUNoQixJQUFJLElBQUksQ0FBQyxRQUFRLENBQ2IsSUFBSSxLQUFLLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQyxZQUFZLENBQUMsRUFDakMsUUFBUSxFQUNSLE9BQU8sRUFDUCxTQUFTLENBQUMsR0FBRyxFQUNiLFFBQVEsQ0FBQyxDQUFDLENBQUM7YUFDdEI7QUFDRCxtQkFBTyxPQUFPLENBQUM7U0FDbEI7O0FBRUQsd0JBQWdCLEVBQUUsMEJBQVUsSUFBSSxFQUFFLFNBQVMsRUFBRSxDQUFDLEVBQUU7K0JBQ3hCLFVBQVUsQ0FBQyxJQUFJLEVBQUUsU0FBUyxFQUFFLENBQUMsQ0FBQzs7Z0JBQXpDLE9BQU87O0FBQ2hCLG1CQUFPLE9BQU8sQ0FBQztTQUNsQjs7QUFFRCx1QkFBZSxFQUFFLHlCQUFVLElBQUksRUFBRSxTQUFTLEVBQUUsQ0FBQyxFQUFFO0FBQzNDLGdCQUFJLENBQUMsSUFBSSxDQUFDLFFBQVEsRUFBRSxPQUFPO0FBQzNCLGdCQUFNLEdBQUcsR0FBRyxDQUFDLENBQUMsSUFBSSxDQUFDLFFBQVEsRUFBRSxTQUFTLEVBQUUsU0FBUyxDQUFDLENBQUM7QUFDbkQsZUFBRyxDQUFDLFNBQVMsQ0FBQyxTQUFTLENBQUMsR0FBRyxDQUFDLENBQUM7U0FDaEM7S0FDSixDQUFDLENBQUM7O0FBRUgsUUFBTSxPQUFPLEdBQUcsUUFBUSxDQUFDLG1CQUFtQixDQUFDLE9BQU8sRUFBRSxVQUFVLEVBQUUsbUJBQW1CLENBQUMsQ0FBQztBQUN2RixRQUFJLE9BQU8sRUFBRTs7QUFFVCxlQUFPLENBQUMsU0FBUyxDQUFDLFVBQVUsQ0FBQyxHQUFHLENBQUMsQ0FBQztLQUNyQzs7QUFFRCxXQUFPLElBQUksQ0FBQztDQUNmOztBQUVELE9BQU8sQ0FBQyxjQUFjLEdBQUcsY0FBYyxDQUFDO0FBQ3hDLE9BQU8sQ0FBQyxnQkFBZ0IsR0FBRyxnQkFBZ0IsQ0FBQzs7O0FDemxCNUMsWUFBWSxDQUFDOzs7OzRCQUVVLGtCQUFrQjs7SUFBN0IsS0FBSzs7NkJBQ08sbUJBQW1COztJQUEvQixNQUFNOzs4QkFDRyxvQkFBb0I7O0lBQTdCLEdBQUc7O0FBQ2YsSUFBTSxJQUFJLEdBQUcsT0FBTyxDQUFDLFFBQVEsQ0FBQyxDQUFDOztBQUUvQixTQUFTLElBQUksR0FBRyxFQUFFO0FBQ2xCLElBQUksQ0FBQyxTQUFTLEdBQUcsTUFBTSxDQUFDLE1BQU0sQ0FBQyxJQUFJLENBQUMsQ0FBQztBQUNyQyxJQUFJLENBQUMsU0FBUyxDQUFDLE1BQU0sR0FBRyxVQUFVLEtBQUssRUFBRTtBQUNyQyxXQUFPLElBQUksS0FBSyxLQUFLLENBQUM7Q0FDekIsQ0FBQzs7QUFFRixTQUFTLFFBQVEsQ0FBQyxJQUFJLEVBQUUsRUFBRSxFQUFFO0FBQ3hCLFFBQUksQ0FBQyxJQUFJLEdBQUcsSUFBSSxDQUFDO0FBQ2pCLFFBQUksQ0FBQyxFQUFFLEdBQUcsRUFBRSxDQUFDO0NBQ2hCO0FBQ0QsUUFBUSxDQUFDLFNBQVMsR0FBRyxNQUFNLENBQUMsTUFBTSxDQUFDLElBQUksQ0FBQyxTQUFTLENBQUMsQ0FBQztBQUNuRCxRQUFRLENBQUMsU0FBUyxDQUFDLE9BQU8sR0FBRyxVQUFVLEdBQUcsRUFBRTtBQUN4QyxRQUFJLEVBQUUsR0FBRyxZQUFhLEtBQUssQ0FBQyxPQUFPLENBQUMsQUFBQyxFQUFFLE9BQU87O0FBRTlDLFFBQU0sT0FBTyxHQUFHLEdBQUcsQ0FBQyxPQUFPLENBQUMsSUFBSSxDQUFDLElBQUksRUFBRSxJQUFJLENBQUMsQ0FBQztBQUM3QyxRQUFJLE9BQU8sRUFBRTs7QUFFVCxlQUFPLENBQUMsU0FBUyxDQUFDLElBQUksQ0FBQyxFQUFFLENBQUMsQ0FBQztLQUM5QixNQUFNLElBQUksR0FBRyxDQUFDLE9BQU8sQ0FBQyxXQUFXLEVBQUUsSUFBSSxDQUFDLEVBQUU7O0FBRXZDLFlBQUksR0FBRyxDQUFDLE9BQU8sQ0FBQyxJQUFJLENBQUMsRUFBRTtBQUNuQixlQUFHLENBQUMsT0FBTyxDQUFDLElBQUksRUFBRSxJQUFJLENBQUMsQ0FBQyxTQUFTLENBQUMsSUFBSSxDQUFDLEVBQUUsQ0FBQyxDQUFDO1NBQzlDOztBQUVELFdBQUcsQ0FBQyxPQUFPLENBQUMsV0FBVyxDQUFDLENBQ3JCLFNBQVMsQ0FBQyxJQUFJLFFBQVEsQ0FBQyxJQUFJLENBQUMsSUFBSSxFQUFFLElBQUksQ0FBQyxFQUFFLENBQUMsQ0FBQyxDQUFDO0tBQ2xEO0NBQ0osQ0FBQztBQUNGLFFBQVEsQ0FBQyxTQUFTLENBQUMsTUFBTSxHQUFHLFVBQVUsS0FBSyxFQUFFO0FBQ3pDLFFBQUksRUFBRSxLQUFLLFlBQVksUUFBUSxDQUFBLEFBQUMsRUFBRSxPQUFPLEtBQUssQ0FBQztBQUMvQyxXQUFPLElBQUksQ0FBQyxJQUFJLEtBQUssS0FBSyxDQUFDLElBQUksSUFDeEIsSUFBSSxDQUFDLEVBQUUsQ0FBQyxNQUFNLENBQUMsS0FBSyxDQUFDLEVBQUUsQ0FBQyxDQUFDO0NBQ25DLENBQUM7O0FBRUYsU0FBUyxTQUFTLENBQUMsSUFBSSxFQUFFLElBQUksRUFBRTtBQUMzQixRQUFJLENBQUMsSUFBSSxHQUFHLElBQUksQ0FBQztBQUNqQixRQUFJLENBQUMsSUFBSSxHQUFHLElBQUksQ0FBQztDQUNwQjtBQUNELFNBQVMsQ0FBQyxTQUFTLEdBQUcsTUFBTSxDQUFDLE1BQU0sQ0FBQyxJQUFJLENBQUMsU0FBUyxDQUFDLENBQUM7QUFDcEQsU0FBUyxDQUFDLFNBQVMsQ0FBQyxPQUFPLEdBQUcsVUFBVSxHQUFHLEVBQUU7QUFDekMsUUFBSSxFQUFFLEdBQUcsWUFBYSxLQUFLLENBQUMsT0FBTyxDQUFDLEFBQUMsRUFBRSxPQUFPO0FBQzlDLFFBQU0sT0FBTyxHQUFHLEdBQUcsQ0FBQyxPQUFPLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQyxDQUFDO0FBQ3ZDLFFBQUksQ0FBQyxJQUFJLENBQUMsU0FBUyxDQUFDLE9BQU8sQ0FBQyxDQUFDOztBQUU3QixRQUFJLElBQUksQ0FBQyxJQUFJLEtBQUssV0FBVyxFQUFFO0FBQzNCLFlBQUksQ0FBQyxJQUFJLENBQUMsUUFBUSxFQUFFLENBQUMsT0FBTyxDQUFDLFVBQUMsRUFBRSxFQUFLO0FBQ2pDLGNBQUUsQ0FBQyxXQUFXLENBQUMsT0FBTyxDQUFDLEdBQUcsQ0FBQyxDQUFDO1NBQy9CLENBQUMsQ0FBQztLQUNOOztBQUVELFFBQUksQ0FBQyxJQUFJLENBQUMsUUFBUSxFQUFFLENBQUMsT0FBTyxDQUFDLFVBQUMsRUFBRSxFQUFLO0FBQ2pDLFlBQUksRUFBRSxFQUFFLFlBQWEsS0FBSyxDQUFDLE1BQU0sQ0FBQyxBQUFDLEVBQUUsT0FBTzs7OzRCQUV2QixFQUFFLENBQUMsU0FBUyxDQUFDLEdBQUcsQ0FBQyxlQUFlLENBQUMsV0FBVyxDQUFDOztZQUEzRCxRQUFROztBQUNmLFdBQUcsQ0FBQyxXQUFXLENBQUMsUUFBUSxFQUFFLENBQUMsT0FBTyxDQUFDLFVBQUMsSUFBSSxFQUFLO0FBQ3pDLGdCQUFJLElBQUksWUFBYSxLQUFLLENBQUMsTUFBTSxBQUFDLEVBQzlCLFFBQVEsQ0FBQyxPQUFPLENBQUMsSUFBSSxDQUFDLFdBQVcsRUFBRSxDQUFDLENBQUM7U0FDNUMsQ0FBQyxDQUFDO0tBQ04sQ0FBQyxDQUFDO0NBQ04sQ0FBQzs7QUFFRixTQUFTLE9BQU8sQ0FBQyxLQUFLLEVBQUUsTUFBTSxFQUFFO0FBQzVCLFFBQUksQ0FBQyxLQUFLLEdBQUcsS0FBSyxDQUFDO0FBQ25CLFFBQUksQ0FBQyxNQUFNLEdBQUcsTUFBTSxDQUFDO0NBQ3hCO0FBQ0QsT0FBTyxDQUFDLFNBQVMsR0FBRyxNQUFNLENBQUMsTUFBTSxDQUFDLElBQUksQ0FBQyxTQUFTLENBQUMsQ0FBQztBQUNsRCxPQUFPLENBQUMsU0FBUyxDQUFDLE9BQU8sR0FBRyxVQUFVLElBQUksRUFBRTtBQUN4QyxRQUFJLENBQUMsSUFBSSxLQUFLLEtBQUssQ0FBQyxVQUFVLElBQ3RCLElBQUksS0FBSyxLQUFLLENBQUMsV0FBVyxDQUFBLEtBQzdCLElBQUksQ0FBQyxLQUFLLENBQUMsT0FBTyxDQUFDLEtBQUssQ0FBQyxVQUFVLENBQUMsSUFDakMsSUFBSSxDQUFDLEtBQUssQ0FBQyxPQUFPLENBQUMsS0FBSyxDQUFDLFdBQVcsQ0FBQyxDQUFBLEFBQUMsRUFBRTtBQUM1QyxZQUFJLENBQUMsTUFBTSxDQUFDLE9BQU8sQ0FBQyxLQUFLLENBQUMsVUFBVSxDQUFDLENBQUM7S0FDekM7QUFDRCxRQUFJLElBQUksS0FBSyxLQUFLLENBQUMsVUFBVSxJQUN6QixDQUFDLElBQUksQ0FBQyxLQUFLLENBQUMsT0FBTyxFQUFFLEVBQUU7QUFDdEIsWUFBSSxDQUFDLE1BQU0sQ0FBQyxPQUFPLENBQUMsS0FBSyxDQUFDLFVBQVUsQ0FBQyxDQUFDO0tBQzFDO0NBQ0osQ0FBQzs7QUFFRixTQUFTLFFBQVEsQ0FBQyxJQUFJLEVBQUUsSUFBSSxFQUFFLEdBQUcsRUFBRSxHQUFHLEVBQUUsS0FBSyxFQUFFO0FBQzNDLFFBQUksQ0FBQyxJQUFJLEdBQUcsSUFBSSxDQUFDO0FBQ2pCLFFBQUksQ0FBQyxJQUFJLEdBQUcsSUFBSSxDQUFDO0FBQ2pCLFFBQUksQ0FBQyxHQUFHLEdBQUcsR0FBRyxDQUFDO0FBQ2YsUUFBSSxDQUFDLEdBQUcsR0FBRyxHQUFHLENBQUM7QUFDZixRQUFJLENBQUMsS0FBSyxHQUFHLEtBQUssQ0FBQztDQUN0QjtBQUNELFFBQVEsQ0FBQyxTQUFTLEdBQUcsTUFBTSxDQUFDLE1BQU0sQ0FBQyxJQUFJLENBQUMsU0FBUyxDQUFDLENBQUM7QUFDbkQsUUFBUSxDQUFDLFNBQVMsQ0FBQyxPQUFPLEdBQUcsVUFBVSxDQUFDLEVBQUU7QUFDdEMsUUFBSSxFQUFFLENBQUMsWUFBYSxLQUFLLENBQUMsTUFBTSxDQUFDLEFBQUMsRUFBRSxPQUFPO0FBQzNDLFFBQU0sT0FBTyxHQUFHLElBQUksQ0FBQyxLQUFLLENBQUMsV0FBVyxDQUFDLENBQUMsQ0FBQyxDQUFDOzt1QkFDTCxDQUFDLENBQUMsU0FBUyxDQUFDLE9BQU8sQ0FBQzs7UUFBbEQsUUFBUTtRQUFFLE9BQU87UUFBRSxPQUFPOztBQUNqQyxRQUFNLEtBQUssR0FBRyxDQUFDLENBQUMsVUFBVSxDQUFDLElBQUksQ0FBQyxRQUFRLENBQUMsQ0FBQyxnQkFBZ0IsQ0FBQyxDQUFDLENBQUMsRUFBRSxFQUFFLE9BQU8sQ0FBQyxDQUFDO0FBQzFFLFFBQU0sU0FBUyxHQUNULElBQUksTUFBTSxDQUFDLE1BQU0sQ0FBQyxRQUFRLEVBQUUsT0FBTyxFQUFFLE9BQU8sRUFDMUIsT0FBTyxFQUFFLEtBQUssQ0FBQyxDQUFDOzs7QUFHeEMsUUFBSSxDQUFDLENBQUMsU0FBUyxFQUFFO0FBQ2IsU0FBQyxDQUFDLFNBQVMsQ0FBQyxTQUFTLENBQUMsUUFBUSxDQUFDLENBQUM7S0FDbkMsTUFBTTtBQUNILFlBQUksQ0FBQyxJQUFJLENBQUMsU0FBUyxDQUFDLFFBQVEsQ0FBQyxDQUFDO0tBQ2pDOztBQUVELFFBQU0sTUFBTSxHQUFHLElBQUksQ0FBQyxHQUFHLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQyxNQUFNLEVBQUUsQ0FBQyxDQUFDLFVBQVUsQ0FBQyxNQUFNLENBQUMsQ0FBQztBQUMvRCxTQUFLLElBQUksQ0FBQyxHQUFHLENBQUMsRUFBRSxDQUFDLEdBQUcsTUFBTSxFQUFFLENBQUMsRUFBRSxFQUFFO0FBQzdCLFlBQUksQ0FBQyxJQUFJLENBQUMsQ0FBQyxDQUFDLENBQUMsU0FBUyxDQUFDLEtBQUssQ0FBQyxTQUFTLENBQUMsQ0FBQyxDQUFDLFVBQVUsQ0FBQyxDQUFDLENBQUMsQ0FBQyxDQUFDLENBQUM7S0FDNUQ7OztBQUdELFFBQUksQ0FBQyxDQUFDLFVBQVUsQ0FBQyxJQUFJLENBQUMsUUFBUSxDQUFDLENBQUMsa0JBQWtCLEVBQUU7QUFDaEQsWUFBTSxNQUFNLEdBQUcsQ0FBQyxDQUFDLGtCQUFrQixDQUFDLE9BQU8sQ0FBQyxDQUFDO0FBQzdDLGFBQUssQ0FBQyxTQUFTLENBQUMsV0FBVyxDQUFDLENBQUMsT0FBTyxDQUFDLE1BQU0sQ0FBQyxDQUFDO0FBQzdDLGFBQUssSUFBSSxDQUFDLEdBQUcsQ0FBQyxFQUFFLENBQUMsR0FBRyxJQUFJLENBQUMsSUFBSSxDQUFDLE1BQU0sRUFBRSxDQUFDLEVBQUUsRUFBRTtBQUN2QyxnQkFBSSxDQUFDLElBQUksQ0FBQyxDQUFDLENBQUMsQ0FBQyxTQUFTLENBQUMsTUFBTSxDQUFDLE9BQU8sQ0FBQyxDQUFDLEdBQUcsRUFBRSxDQUFDLENBQUMsQ0FBQztBQUMvQyxnQkFBSSxDQUFDLElBQUksQ0FBQyxDQUFDLENBQUMsQ0FBQyxTQUFTLENBQUMsTUFBTSxDQUFDLE9BQU8sQ0FBQyxJQUFJLENBQUMsQ0FBQyxDQUFDO1NBQ2hEO0FBQ0QsY0FBTSxDQUFDLE9BQU8sQ0FBQyxRQUFRLENBQUMsQ0FBQyxPQUFPLENBQUMsQ0FBQyxDQUFDLENBQUM7QUFDcEMsY0FBTSxDQUFDLE9BQU8sQ0FBQyxRQUFRLENBQUMsQ0FBQyxPQUFPLENBQUMsS0FBSyxDQUFDLFVBQVUsQ0FBQyxDQUFDO0tBQ3REOzs7QUFHRCxRQUFJLENBQUMsY0FBYyxDQUFDLENBQUMsQ0FBQyxVQUFVLENBQUMsSUFBSSxFQUFFLFNBQVMsQ0FBQyxDQUFDOzs7QUFHbEQsV0FBTyxDQUFDLFNBQVMsQ0FBQyxJQUFJLENBQUMsR0FBRyxDQUFDLENBQUM7O0FBRTVCLFdBQU8sQ0FBQyxTQUFTLENBQUMsSUFBSSxDQUFDLEdBQUcsQ0FBQyxDQUFDO0NBQy9CLENBQUM7O0FBRUYsU0FBUyxNQUFNLENBQUMsSUFBSSxFQUFFLEdBQUcsRUFBRSxHQUFHLEVBQUUsS0FBSyxFQUFFO0FBQ25DLFFBQUksQ0FBQyxJQUFJLEdBQUcsSUFBSSxDQUFDO0FBQ2pCLFFBQUksQ0FBQyxHQUFHLEdBQUcsR0FBRyxDQUFDO0FBQ2YsUUFBSSxDQUFDLEdBQUcsR0FBRyxHQUFHLENBQUM7QUFDZixRQUFJLENBQUMsS0FBSyxHQUFHLEtBQUssQ0FBQztDQUN0QjtBQUNELE1BQU0sQ0FBQyxTQUFTLEdBQUcsTUFBTSxDQUFDLE1BQU0sQ0FBQyxJQUFJLENBQUMsU0FBUyxDQUFDLENBQUM7QUFDakQsTUFBTSxDQUFDLFNBQVMsQ0FBQyxPQUFPLEdBQUcsVUFBVSxDQUFDLEVBQUU7O0FBRXBDLFFBQUksRUFBRSxDQUFDLFlBQWEsS0FBSyxDQUFDLE1BQU0sQ0FBQyxBQUFDLElBQUksQ0FBQyxDQUFDLFNBQVMsRUFBRTtBQUMvQyxlQUFPO0tBQ1Y7QUFDRCxRQUFNLE9BQU8sR0FBRyxJQUFJLENBQUMsS0FBSyxDQUFDLFdBQVcsQ0FBQyxDQUFDLENBQUMsQ0FBQzs7d0JBQ0wsQ0FBQyxDQUFDLFNBQVMsQ0FBQyxPQUFPLENBQUM7O1FBQWxELFFBQVE7UUFBRSxPQUFPO1FBQUUsT0FBTzs7QUFDakMsUUFBTSxLQUFLLEdBQUcsQ0FBQyxDQUFDLFVBQVUsQ0FBQyxJQUFJLENBQUMsUUFBUSxDQUFDLENBQUMsZ0JBQWdCLENBQUMsQ0FBQyxDQUFDLEVBQUUsRUFBRSxPQUFPLENBQUMsQ0FBQztBQUMxRSxRQUFNLFNBQVMsR0FDVCxJQUFJLE1BQU0sQ0FBQyxNQUFNLENBQ2YsUUFBUTs7QUFFUixRQUFJLFNBQVMsQ0FBQyxPQUFPLENBQUMsRUFDdEIsT0FBTyxFQUNQLE9BQU8sRUFDUCxLQUFLLENBQUMsQ0FBQzs7QUFFZixRQUFNLE1BQU0sR0FBRyxDQUFDLENBQUMsV0FBVyxFQUFFLENBQUM7QUFDL0IsWUFBUSxDQUFDLE9BQU8sQ0FBQyxNQUFNLENBQUMsQ0FBQzs7QUFFekIsUUFBTSxNQUFNLEdBQUcsSUFBSSxDQUFDLEdBQUcsQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDLE1BQU0sRUFBRSxDQUFDLENBQUMsVUFBVSxDQUFDLE1BQU0sQ0FBQyxDQUFDO0FBQy9ELFNBQUssSUFBSSxDQUFDLEdBQUcsQ0FBQyxFQUFFLENBQUMsR0FBRyxNQUFNLEVBQUUsQ0FBQyxFQUFFLEVBQUU7QUFDN0IsWUFBSSxDQUFDLElBQUksQ0FBQyxDQUFDLENBQUMsQ0FBQyxTQUFTLENBQUMsS0FBSyxDQUFDLFNBQVMsQ0FBQyxDQUFDLENBQUMsVUFBVSxDQUFDLENBQUMsQ0FBQyxDQUFDLENBQUMsQ0FBQztLQUM1RDs7O0FBR0QsUUFBSSxDQUFDLENBQUMsVUFBVSxDQUFDLElBQUksQ0FBQyxRQUFRLENBQUMsQ0FBQyxrQkFBa0IsRUFBRTtBQUNoRCxZQUFNLE1BQU0sR0FBRyxDQUFDLENBQUMsa0JBQWtCLENBQUMsT0FBTyxDQUFDLENBQUM7QUFDN0MsYUFBSyxDQUFDLFNBQVMsQ0FBQyxXQUFXLENBQUMsQ0FBQyxPQUFPLENBQUMsTUFBTSxDQUFDLENBQUM7QUFDN0MsYUFBSyxJQUFJLENBQUMsR0FBRyxDQUFDLEVBQUUsQ0FBQyxHQUFHLElBQUksQ0FBQyxJQUFJLENBQUMsTUFBTSxFQUFFLENBQUMsRUFBRSxFQUFFO0FBQ3ZDLGdCQUFJLENBQUMsSUFBSSxDQUFDLENBQUMsQ0FBQyxDQUFDLFNBQVMsQ0FBQyxNQUFNLENBQUMsT0FBTyxDQUFDLENBQUMsR0FBRyxFQUFFLENBQUMsQ0FBQyxDQUFDO0FBQy9DLGdCQUFJLENBQUMsSUFBSSxDQUFDLENBQUMsQ0FBQyxDQUFDLFNBQVMsQ0FBQyxNQUFNLENBQUMsT0FBTyxDQUFDLElBQUksQ0FBQyxDQUFDLENBQUM7U0FDaEQ7QUFDRCxjQUFNLENBQUMsT0FBTyxDQUFDLFFBQVEsQ0FBQyxDQUFDLE9BQU8sQ0FBQyxDQUFDLENBQUMsQ0FBQztBQUNwQyxjQUFNLENBQUMsT0FBTyxDQUFDLFFBQVEsQ0FBQyxDQUFDLE9BQU8sQ0FBQyxLQUFLLENBQUMsVUFBVSxDQUFDLENBQUM7S0FDdEQ7OztBQUdELFFBQUksQ0FBQyxjQUFjLENBQUMsQ0FBQyxDQUFDLFVBQVUsQ0FBQyxJQUFJLEVBQUUsU0FBUyxDQUFDLENBQUM7OztBQUdsRCxRQUFJLENBQUMsR0FBRyxDQUFDLE9BQU8sQ0FBQyxNQUFNLENBQUMsQ0FBQztBQUN6QixXQUFPLENBQUMsU0FBUyxDQUFDLElBQUksQ0FBQyxHQUFHLENBQUMsQ0FBQzs7QUFFNUIsV0FBTyxDQUFDLFNBQVMsQ0FBQyxJQUFJLENBQUMsR0FBRyxDQUFDLENBQUM7Q0FDL0IsQ0FBQzs7O0FBR0YsU0FBUyxTQUFTLENBQUMsSUFBSSxFQUFFO0FBQ3JCLFFBQUksQ0FBQyxJQUFJLEdBQUcsSUFBSSxDQUFDO0NBQ3BCO0FBQ0QsU0FBUyxDQUFDLFNBQVMsR0FBRyxNQUFNLENBQUMsTUFBTSxDQUFDLElBQUksQ0FBQyxTQUFTLENBQUMsQ0FBQztBQUNwRCxTQUFTLENBQUMsU0FBUyxDQUFDLE9BQU8sR0FBRyxVQUFVLElBQUksRUFBRTtBQUMxQyxRQUFJLEVBQUUsSUFBSSxZQUFZLEtBQUssQ0FBQyxPQUFPLENBQUEsQUFBQyxFQUFFLE9BQU87QUFDN0MsUUFBSSxDQUFDLElBQUksQ0FBQyxPQUFPLENBQUMsSUFBSSxDQUFDLENBQUM7Q0FDM0IsQ0FBQzs7QUFFRixPQUFPLENBQUMsUUFBUSxHQUFHLFFBQVEsQ0FBQztBQUM1QixPQUFPLENBQUMsU0FBUyxHQUFHLFNBQVMsQ0FBQztBQUM5QixPQUFPLENBQUMsT0FBTyxHQUFHLE9BQU8sQ0FBQztBQUMxQixPQUFPLENBQUMsUUFBUSxHQUFHLFFBQVEsQ0FBQztBQUM1QixPQUFPLENBQUMsTUFBTSxHQUFHLE1BQU0sQ0FBQzs7Ozs7Ozs7Ozs7Ozs7Ozs7QUNyTWpCLElBQU0sb0JBQW9CLEdBQUc7O0FBRWhDLGFBQVMsRUFBRSxDQUFDOztBQUVaLHVCQUFtQixFQUFFLDZCQUFVLEVBQUUsRUFBRTtBQUMvQixlQUFPLENBQUMsQ0FBQztLQUNaO0NBQ0osQ0FBQzs7OztBQUVLLFNBQVMsMEJBQTBCLENBQUMsS0FBSyxFQUFFO0FBQzlDLHdCQUFvQixDQUFDLFNBQVMsR0FBRyxLQUFLLENBQUMsU0FBUyxDQUFDO0FBQ2pELHdCQUFvQixDQUFDLG1CQUFtQixHQUFHLEtBQUssQ0FBQyxtQkFBbUIsQ0FBQztDQUN4RTs7OztJQUdZLGVBQWU7QUFFYixhQUZGLGVBQWUsQ0FFWixJQUFJLEVBQUU7OEJBRlQsZUFBZTs7QUFHcEIsNkJBQWdCLGVBQWUsQ0FBQyxXQUFXLENBQUMsTUFBTSxFQUFFLGtIQUFFOzs7Ozs7Ozs7Ozs7Z0JBQTdDLEdBQUc7O0FBQ1IsZ0JBQUksR0FBRyxDQUFDLFlBQVksQ0FBQyxJQUFJLENBQUMsRUFBRTs7QUFFeEIsdUJBQU8sR0FBRyxDQUFDO2FBQ2Q7U0FDSjs7QUFFRCxZQUFJLElBQUksS0FBSyxJQUFJLEVBQUU7QUFDZixnQkFBSSxDQUFDLE1BQU0sR0FBRyxJQUFJLENBQUM7U0FDdEIsTUFBTTtBQUNILGdCQUFJLENBQUMsTUFBTSxHQUFHLElBQUksQ0FBQyxLQUFLLENBQUMsQ0FBQyxDQUFDLENBQUM7U0FDL0I7O0FBRUQsdUJBQWUsQ0FBQyxXQUFXLENBQUMsR0FBRyxDQUFDLElBQUksQ0FBQyxDQUFDO0tBQ3pDOzs7Ozs7Ozs7O0FBakJRLG1CQUFlLFdBd0J4QixZQUFZLEdBQUEsc0JBQUMsSUFBSSxFQUFFO0FBQ2YsWUFBSSxJQUFJLENBQUMsTUFBTSxLQUFLLElBQUksRUFBRTtBQUN0QixtQkFBTyxJQUFJLEtBQUssSUFBSSxDQUFDO1NBQ3hCO0FBQ0QsWUFBSSxJQUFJLEtBQUssSUFBSSxFQUFFO0FBQ2YsbUJBQU8sSUFBSSxDQUFDLE1BQU0sS0FBSyxJQUFJLENBQUM7U0FDL0I7QUFDRCxZQUFJLElBQUksQ0FBQyxNQUFNLENBQUMsTUFBTSxLQUFLLElBQUksQ0FBQyxNQUFNLEVBQUU7QUFDcEMsbUJBQU8sS0FBSyxDQUFDO1NBQ2hCO0FBQ0QsYUFBSyxJQUFJLENBQUMsR0FBRyxDQUFDLEVBQUUsQ0FBQyxHQUFHLElBQUksQ0FBQyxNQUFNLENBQUMsTUFBTSxFQUFFLENBQUMsRUFBRSxFQUFFO0FBQ3pDLGdCQUFJLElBQUksQ0FBQyxNQUFNLENBQUMsQ0FBQyxDQUFDLEtBQUssSUFBSSxDQUFDLENBQUMsQ0FBQyxFQUFFLE9BQU8sS0FBSyxDQUFDO1NBQ2hEO0FBQ0QsZUFBTyxJQUFJLENBQUM7S0FDZjs7Ozs7Ozs7O0FBdENRLG1CQUFlLFdBOEN4QixTQUFTLEdBQUEsbUJBQUMsUUFBUSxFQUFFOztBQUVoQixZQUFJLElBQUksS0FBSyxlQUFlLENBQUMsV0FBVyxFQUFFO0FBQ3RDLG1CQUFPLElBQUksQ0FBQztTQUNmOzs7QUFHRCxZQUFNLFFBQVEsR0FBRyxJQUFJLENBQUMsTUFBTSxDQUFDLE1BQU0sQ0FBQyxRQUFRLENBQUMsQ0FBQztBQUM5QyxZQUFJLFFBQVEsQ0FBQyxNQUFNLEdBQUcsb0JBQW9CLENBQUMsU0FBUyxFQUFFO0FBQ2xELG9CQUFRLENBQUMsS0FBSyxFQUFFLENBQUM7U0FDcEI7QUFDRCxlQUFPLElBQUksZUFBZSxDQUFDLFFBQVEsQ0FBQyxDQUFDO0tBQ3hDOzs7Ozs7OztBQTFEUSxtQkFBZSxXQWlFeEIsV0FBVyxHQUFBLHFCQUFDLEVBQUUsRUFBRTs7QUFFWixZQUFJLElBQUksS0FBSyxlQUFlLENBQUMsV0FBVyxFQUFFO0FBQ3RDLG1CQUFPLElBQUksQ0FBQztTQUNmOztBQUVELFlBQU0sYUFBYSxHQUFHLG9CQUFvQixDQUFDLG1CQUFtQixDQUFDLEVBQUUsQ0FBQyxDQUFDO0FBQ25FLFlBQUksYUFBYSxLQUFLLENBQUMsRUFBRTs7QUFFckIsbUJBQU8sZUFBZSxDQUFDLGNBQWMsQ0FBQztTQUN6QyxNQUFNOztBQUVILG1CQUFPLElBQUksZUFBZSxDQUFDLElBQUksQ0FBQyxNQUFNLENBQUMsS0FBSyxDQUFDLENBQUMsYUFBYSxDQUFDLENBQUMsQ0FBQztTQUNqRTtLQUNKOztBQS9FUSxtQkFBZSxXQWlGeEIsUUFBUSxHQUFBLG9CQUFHO0FBQ1AsZUFBTyxJQUFJLENBQUMsTUFBTSxDQUFDLFFBQVEsRUFBRSxDQUFDO0tBQ2pDOztXQW5GUSxlQUFlOzs7O0FBdUY1QixlQUFlLENBQUMsV0FBVyxHQUFHLElBQUksR0FBRyxFQUFFLENBQUM7O0FBRXhDLGVBQWUsQ0FBQyxXQUFXLEdBQUcsSUFBSSxlQUFlLENBQUMsSUFBSSxDQUFDLENBQUM7O0FBRXhELGVBQWUsQ0FBQyxjQUFjLEdBQUcsSUFBSSxlQUFlLENBQUMsRUFBRSxDQUFDLENBQUM7Ozs7Ozs7Ozs7Ozs7Ozs7SUMxRzVDLE1BQU07QUFDSixhQURGLE1BQU0sQ0FDSCxJQUFJLEVBQUUsR0FBRyxFQUFFLEdBQUcsRUFBRSxLQUFLLEVBQUUsRUFBRSxFQUFFOzhCQUQ5QixNQUFNOztBQUVYLFlBQUksQ0FBQyxJQUFJLEdBQUcsSUFBSSxDQUFDO0FBQ2pCLFlBQUksQ0FBQyxHQUFHLEdBQUcsR0FBRyxDQUFDO0FBQ2YsWUFBSSxDQUFDLEdBQUcsR0FBRyxHQUFHLENBQUM7QUFDZixZQUFJLENBQUMsS0FBSyxHQUFHLEtBQUssQ0FBQztBQUNuQixZQUFJLENBQUMsRUFBRSxHQUFHLEVBQUUsQ0FBQztLQUNoQjs7QUFQUSxVQUFNLFdBU2YsTUFBTSxHQUFBLGdCQUFDLEtBQUssRUFBRTtBQUNWLGVBQU8sSUFBSSxDQUFDLElBQUksS0FBSyxLQUFLLENBQUMsSUFBSSxJQUMzQixJQUFJLENBQUMsR0FBRyxLQUFLLEtBQUssQ0FBQyxHQUFHLElBQ3RCLElBQUksQ0FBQyxHQUFHLEtBQUssS0FBSyxDQUFDLEdBQUcsSUFDdEIsSUFBSSxDQUFDLEtBQUssS0FBSyxLQUFLLENBQUMsS0FBSyxJQUMxQixJQUFJLENBQUMsRUFBRSxLQUFLLEtBQUssQ0FBQyxFQUFFLENBQUM7S0FDNUI7O0FBZlEsVUFBTSxXQWlCZixZQUFZLEdBQUEsc0JBQUMsWUFBWSxFQUFFO0FBQ3ZCLFlBQU0sU0FBUyxHQUFHLElBQUksTUFBTSxFQUFBLENBQUM7QUFDN0IsYUFBSyxJQUFJLENBQUMsSUFBSSxJQUFJLEVBQUU7QUFDaEIsZ0JBQUksSUFBSSxDQUFDLGNBQWMsQ0FBQyxDQUFDLENBQUMsRUFBRTtBQUN4QixvQkFBSSxZQUFZLENBQUMsY0FBYyxDQUFDLENBQUMsQ0FBQyxFQUFFO0FBQ2hDLDZCQUFTLENBQUMsQ0FBQyxDQUFDLEdBQUcsWUFBWSxDQUFDLENBQUMsQ0FBQyxDQUFDO2lCQUNsQyxNQUFNO0FBQ0gsNkJBQVMsQ0FBQyxDQUFDLENBQUMsR0FBRyxJQUFJLENBQUMsQ0FBQyxDQUFDLENBQUM7aUJBQzFCO2FBQ0o7U0FDSjtBQUNELGVBQU8sU0FBUyxDQUFDO0tBQ3BCOztXQTdCUSxNQUFNOzs7Ozs7Ozs7Ozs7Ozs7O0FDTm5CLElBQUksS0FBSyxHQUFHLENBQUMsQ0FBQzs7Ozs7O0lBS0QsSUFBSTs7Ozs7QUFJRixhQUpGLElBQUksQ0FJRCxJQUFJLEVBQUU7OEJBSlQsSUFBSTs7OztBQU9ULFlBQUksSUFBSSxFQUFFLElBQUksQ0FBQyxLQUFLLEdBQUcsSUFBSSxHQUFHLENBQUMsQ0FBQyxJQUFJLENBQUMsQ0FBQyxDQUFDLEtBQ2xDLElBQUksQ0FBQyxLQUFLLEdBQUcsSUFBSSxHQUFHLEVBQUUsQ0FBQzs7O0FBRzVCLFlBQUksQ0FBQyxRQUFRLEdBQUcsSUFBSSxHQUFHLEVBQUUsQ0FBQzs7QUFFMUIsWUFBSSxDQUFDLEdBQUcsR0FBRyxLQUFLLEVBQUUsQ0FBQztLQUN0Qjs7Ozs7Ozs7Ozs7QUFkUSxRQUFJLFdBbUJiLE9BQU8sR0FBQSxtQkFBRztBQUNOLGVBQU8sSUFBSSxDQUFDLEtBQUssQ0FBQyxJQUFJLEtBQUssQ0FBQyxDQUFDO0tBQ2hDOztBQXJCUSxRQUFJLFdBdUJiLE9BQU8sR0FBQSxtQkFBRztBQUNOLGVBQU8sSUFBSSxDQUFDLEtBQUssQ0FBQyxJQUFJLENBQUM7S0FDMUI7Ozs7OztBQXpCUSxRQUFJLFdBOEJiLFFBQVEsR0FBQSxvQkFBRztBQUNQLGVBQU8sSUFBSSxDQUFDLEtBQUssQ0FBQztLQUNyQjs7Ozs7OztBQWhDUSxRQUFJLFdBc0NiLE9BQU8sR0FBQSxpQkFBQyxJQUFJLEVBQUU7QUFDVixlQUFPLElBQUksQ0FBQyxLQUFLLENBQUMsR0FBRyxDQUFDLElBQUksQ0FBQyxDQUFDO0tBQy9COzs7Ozs7OztBQXhDUSxRQUFJLFdBK0NiLE9BQU8sR0FBQSxpQkFBQyxJQUFJLEVBQUU7QUFDVixZQUFJLElBQUksQ0FBQyxLQUFLLENBQUMsR0FBRyxDQUFDLElBQUksQ0FBQyxFQUFFO0FBQ3RCLG1CQUFPLEtBQUssQ0FBQztTQUNoQjs7QUFFRCxZQUFJLENBQUMsS0FBSyxDQUFDLEdBQUcsQ0FBQyxJQUFJLENBQUMsQ0FBQzs7QUFFckIsWUFBSSxDQUFDLFFBQVEsQ0FBQyxPQUFPLENBQUMsVUFBQSxHQUFHLEVBQUk7QUFDekIsZUFBRyxDQUFDLE9BQU8sQ0FBQyxJQUFJLENBQUMsQ0FBQztTQUNyQixDQUFDLENBQUM7QUFDSCxlQUFPLElBQUksQ0FBQztLQUNmOzs7Ozs7QUExRFEsUUFBSSxXQStEYixTQUFTLEdBQUEsbUJBQUMsTUFBTSxFQUFFO0FBQ2QsWUFBSSxDQUFDLElBQUksQ0FBQyxVQUFVLENBQUMsTUFBTSxDQUFDLEVBQUUsT0FBTzs7O0FBR3JDLFlBQUksQ0FBQyxLQUFLLENBQUMsT0FBTyxDQUFDLFVBQUEsSUFBSSxFQUFJO0FBQ3ZCLGtCQUFNLENBQUMsT0FBTyxDQUFDLElBQUksQ0FBQyxDQUFDO1NBQ3hCLENBQUMsQ0FBQztLQUNOOzs7Ozs7OztBQXRFUSxRQUFJLFdBNkViLFVBQVUsR0FBQSxvQkFBQyxHQUFHLEVBQUU7QUFDWiw2QkFBbUIsSUFBSSxDQUFDLFFBQVEsa0hBQUU7Ozs7Ozs7Ozs7OztnQkFBekIsTUFBTTs7QUFDWCxnQkFBSSxHQUFHLENBQUMsTUFBTSxDQUFDLE1BQU0sQ0FBQyxFQUFFO0FBQ3BCLHVCQUFPLEtBQUssQ0FBQzthQUNoQjtTQUNKO0FBQ0QsWUFBSSxDQUFDLFFBQVEsQ0FBQyxHQUFHLENBQUMsR0FBRyxDQUFDLENBQUM7QUFDdkIsZUFBTyxJQUFJLENBQUM7S0FDZjs7Ozs7Ozs7QUFyRlEsUUFBSSxXQTRGYixNQUFNLEdBQUEsZ0JBQUMsS0FBSyxFQUFFOztBQUVWLGVBQU8sSUFBSSxLQUFLLEtBQUssQ0FBQztLQUN6Qjs7Ozs7Ozs7QUEvRlEsUUFBSSxXQXNHYixPQUFPLEdBQUEsaUJBQUMsSUFBSSxFQUFFO0FBQ1YsWUFBSSxJQUFJLENBQUMsS0FBSyxDQUFDLEdBQUcsQ0FBQyxJQUFJLENBQUMsRUFBRTtBQUN0QixtQkFBTyxJQUFJLENBQUMsS0FBSyxDQUFDLEdBQUcsQ0FBQyxJQUFJLENBQUMsQ0FBQztTQUMvQixNQUFNO0FBQ0gsbUJBQU8sUUFBUSxDQUFDO1NBQ25CO0tBQ0o7O0FBNUdRLFFBQUksV0E4R2IsUUFBUSxHQUFBLG9CQUFHO0FBQ1AsWUFBTSxZQUFZLEdBQUcsSUFBSSxHQUFHLEVBQUUsQ0FBQztBQUMvQixlQUFPLElBQUksQ0FBQyxTQUFTLENBQUMsWUFBWSxDQUFDLENBQUM7S0FDdkM7O0FBakhRLFFBQUksV0FtSGIsU0FBUyxHQUFBLG1CQUFDLFlBQVksRUFBRTtBQUNwQixZQUFNLFdBQVcsR0FBRyxFQUFFLENBQUM7QUFDdkIsOEJBQWUsSUFBSSxDQUFDLEtBQUsseUhBQUU7Ozs7Ozs7Ozs7OztnQkFBbEIsRUFBRTs7QUFDUCxnQkFBSSxZQUFZLENBQUMsR0FBRyxDQUFDLEVBQUUsQ0FBQyxFQUFFO0FBQ3RCLDJCQUFXLENBQUMsSUFBSSxDQUFDLEdBQUcsQ0FBQyxDQUFDO2FBQ3pCLE1BQU07QUFDSCwyQkFBVyxDQUFDLElBQUksQ0FBQyxFQUFFLENBQUMsU0FBUyxDQUFDLFlBQVksQ0FBQyxDQUFDLENBQUM7YUFDaEQ7U0FDSjtBQUNELGVBQU8sV0FBVyxDQUFDLElBQUksQ0FBQyxHQUFHLENBQUMsQ0FBQztLQUNoQzs7V0E3SFEsSUFBSTs7Ozs7SUFvSVgsSUFBSTs7Ozs7O0FBS0ssYUFMVCxJQUFJLENBS00sSUFBSSxFQUFFOzhCQUxoQixJQUFJOztBQU1GLFlBQUksQ0FBQyxJQUFJLEdBQUcsSUFBSSxDQUFDO0tBQ3BCOzs7Ozs7Ozs7OztBQVBDLFFBQUksV0FhTixPQUFPLEdBQUEsbUJBQUc7QUFDTixlQUFPLElBQUksQ0FBQyxJQUFJLENBQUM7S0FDcEI7Ozs7Ozs7O0FBZkMsUUFBSSxXQXNCTixTQUFTLEdBQUEscUJBQUc7QUFDUixlQUFPLElBQUksQ0FBQyxPQUFPLEVBQUUsQ0FBQztLQUN6Qjs7V0F4QkMsSUFBSTs7O0lBK0JHLE9BQU87Y0FBUCxPQUFPOzs7Ozs7O0FBS0wsYUFMRixPQUFPLENBS0osS0FBSyxFQUFFLElBQUksRUFBRTs4QkFMaEIsT0FBTzs7QUFNWix5QkFBTSxJQUFJLENBQUMsQ0FBQztBQUNaLFlBQUksQ0FBQyxLQUFLLEdBQUcsSUFBSSxHQUFHLEVBQUUsQ0FBQzs7QUFFdkIsWUFBSSxDQUFDLE9BQU8sQ0FBQyxXQUFXLEVBQUUsS0FBSyxDQUFDLENBQUM7O0FBRWpDLFlBQUksQ0FBQyxXQUFXLEdBQUcsSUFBSSxJQUFJLEVBQUUsQ0FBQztLQUNqQzs7Ozs7Ozs7OztBQVpRLFdBQU8sV0FtQmhCLE9BQU8sR0FBQSxpQkFBQyxJQUFJLEVBQUUsUUFBUSxFQUFFO0FBQ3BCLFlBQUksSUFBSSxDQUFDLEtBQUssQ0FBQyxHQUFHLENBQUMsSUFBSSxDQUFDLEVBQUU7QUFDdEIsbUJBQU8sSUFBSSxDQUFDLEtBQUssQ0FBQyxHQUFHLENBQUMsSUFBSSxDQUFDLENBQUM7U0FDL0IsTUFBTSxJQUFJLFFBQVEsRUFBRTtBQUNqQixtQkFBTyxJQUFJLENBQUM7U0FDZixNQUFNO0FBQ0gsZ0JBQUksV0FBVyxHQUFHLElBQUksSUFBSSxFQUFBLENBQUM7QUFDM0IsZ0JBQUksQ0FBQyxLQUFLLENBQUMsR0FBRyxDQUFDLElBQUksRUFBRSxXQUFXLENBQUMsQ0FBQztBQUNsQyxtQkFBTyxXQUFXLENBQUM7U0FDdEI7S0FDSjs7Ozs7Ozs7O0FBN0JRLFdBQU8sV0FxQ2hCLE9BQU8sR0FBQSxpQkFBQyxJQUFJLEVBQUUsSUFBSSxFQUFFO0FBQ2hCLFlBQUksQ0FBQyxLQUFLLENBQUMsR0FBRyxDQUFDLElBQUksRUFBRSxJQUFJLENBQUMsQ0FBQztLQUM5Qjs7Ozs7OztBQXZDUSxXQUFPLFdBNkNoQixlQUFlLEdBQUEsMkJBQUc7QUFDZCxlQUFPLElBQUksQ0FBQyxLQUFLLENBQUMsSUFBSSxFQUFFLENBQUM7S0FDNUI7Ozs7Ozs7O0FBL0NRLFdBQU8sV0FzRGhCLE9BQU8sR0FBQSxpQkFBQyxJQUFJLEVBQUU7QUFDVixlQUFPLElBQUksQ0FBQyxLQUFLLENBQUMsR0FBRyxDQUFDLElBQUksQ0FBQyxDQUFDO0tBQy9COzs7Ozs7OztBQXhEUSxXQUFPLFdBK0RoQixhQUFhLEdBQUEsdUJBQUMsSUFBSSxFQUFFLElBQUksRUFBRTtBQUN0QixZQUFJLENBQUMsSUFBSSxDQUFDLEtBQUssQ0FBQyxHQUFHLENBQUMsSUFBSSxDQUFDLEVBQUU7QUFDdkIsZ0JBQUksQ0FBQyxLQUFLLENBQUMsR0FBRyxDQUFDLElBQUksRUFBRSxJQUFJLElBQUksRUFBQSxDQUFDLENBQUM7U0FDbEM7QUFDRCxZQUFJLElBQUksQ0FBQyxLQUFLLENBQUMsR0FBRyxDQUFDLElBQUksQ0FBQyxDQUFDLE9BQU8sQ0FBQyxJQUFJLENBQUMsRUFBRSxPQUFPO0FBQy9DLFlBQUksQ0FBQyxLQUFLLENBQUMsR0FBRyxDQUFDLElBQUksQ0FBQyxDQUFDLE9BQU8sQ0FBQyxJQUFJLENBQUMsQ0FBQztLQUN0Qzs7Ozs7Ozs7QUFyRVEsV0FBTyxXQTRFaEIsY0FBYyxHQUFBLHdCQUFDLElBQUksRUFBRSxJQUFJLEVBQUU7QUFDdkIsWUFBSSxJQUFJLEdBQUcsSUFBSSxDQUFDO0FBQ2hCLFlBQUksQ0FBQyxRQUFRLEVBQUUsQ0FBQyxPQUFPLENBQUMsVUFBVSxJQUFJLEVBQUU7QUFDcEMsZ0JBQUksQ0FBQyxhQUFhLENBQUMsSUFBSSxFQUFFLElBQUksQ0FBQyxDQUFDO1NBQ2xDLENBQUMsQ0FBQztLQUNOOzs7Ozs7OztBQWpGUSxXQUFPLFdBd0ZoQixTQUFTLEdBQUEsbUJBQUMsWUFBWSxFQUFFO0FBQ3BCLFlBQUksSUFBSSxDQUFDLElBQUksS0FBSyxTQUFTLEVBQUU7QUFDekIsZ0JBQU0sS0FBSyxHQUFHLEVBQUUsQ0FBQztBQUNqQixrQ0FBYyxJQUFJLENBQUMsS0FBSyxDQUFDLElBQUksRUFBRSx5SEFBRTs7Ozs7Ozs7Ozs7O29CQUF4QixDQUFDOzs7QUFFTixvQkFBSSxDQUFDLEtBQUssV0FBVyxFQUFFLFNBQVM7QUFDaEMscUJBQUssQ0FBQyxJQUFJLENBQUMsQ0FBQyxDQUFDLENBQUM7YUFDakI7QUFDRCxtQkFBTyxHQUFHLEdBQUcsS0FBSyxDQUFDLElBQUksRUFBRSxHQUFHLEdBQUcsQ0FBQztTQUNuQyxNQUFNO0FBQ0gsbUJBQU8sSUFBSSxDQUFDLElBQUksQ0FBQztTQUNwQjtLQUNKOztXQXBHUSxPQUFPO0dBQVMsSUFBSTs7OztBQXdHMUIsU0FBUyxvQkFBb0IsQ0FBQyxNQUFNLEVBQUU7QUFDekMsUUFBSSxJQUFJLEdBQUcsSUFBSSxPQUFPLENBQUMsUUFBUSxFQUFFLGdCQUFnQixDQUFDLENBQUM7QUFDbkQsUUFBSSxDQUFDLEtBQUssR0FBRyxNQUFNLENBQUMsTUFBTSxDQUFDOzs7QUFHM0IsUUFBSSxDQUFDLE9BQU8sR0FBRyxVQUFVLElBQUksRUFBRTtBQUMzQixZQUFJLENBQUMsTUFBTSxDQUFDLEVBQUUsQ0FBQyxXQUFXLENBQUMsSUFBSSxDQUFDLEVBQUU7O0FBRTlCLGtCQUFNLENBQUMsRUFBRSxDQUFDLG1CQUFtQixDQUFDLElBQUksQ0FBQyxDQUFDO1NBQ3ZDO0FBQ0QsZUFBTyxPQUFPLENBQUMsU0FBUyxDQUFDLE9BQU8sQ0FBQyxJQUFJLENBQUMsSUFBSSxFQUFFLElBQUksQ0FBQyxDQUFDO0tBQ3JELENBQUM7QUFDRixXQUFPLElBQUksQ0FBQztDQUNmOzs7Ozs7SUFLWSxRQUFRO2NBQVIsUUFBUTs7Ozs7O0FBSU4sYUFKRixRQUFRLENBSUwsSUFBSSxFQUFFOzhCQUpULFFBQVE7O0FBS2IsMEJBQU0sSUFBSSxDQUFDLENBQUM7S0FDZjs7Ozs7O1dBTlEsUUFBUTtHQUFTLElBQUk7Ozs7SUFhckIsTUFBTTtjQUFOLE1BQU07Ozs7Ozs7Ozs7OztBQVVKLGFBVkYsTUFBTSxDQVVILFFBQVEsRUFBRSxJQUFJLEVBQUUsUUFBUSxFQUFFLEVBQUUsRUFBRSxVQUFVLEVBQUUsUUFBUSxFQUFFLFNBQVMsRUFBRTs4QkFWbEUsTUFBTTs7QUFXWCw0QkFBTSxRQUFRLEVBQUUsSUFBSSxDQUFDLENBQUM7QUFDdEIsWUFBSSxDQUFDLFVBQVUsR0FBRyxRQUFRLENBQUM7QUFDM0IsWUFBSSxDQUFDLEVBQUUsR0FBRyxFQUFFLENBQUM7QUFDYixZQUFJLENBQUMsVUFBVSxHQUFHLFVBQVUsQ0FBQztBQUM3QixZQUFJLFFBQVEsRUFBRTtBQUNWLGdCQUFJLENBQUMsUUFBUSxHQUFHLFFBQVEsQ0FBQztTQUM1QjtBQUNELFlBQUksU0FBUyxFQUFFO0FBQ1gsZ0JBQUksQ0FBQyxTQUFTLEdBQUcsU0FBUyxDQUFDO1NBQzlCOztBQUVELFlBQUksQ0FBQyxNQUFNLEdBQUcsSUFBSSxHQUFHLEVBQUEsQ0FBQztLQUN6Qjs7Ozs7Ozs7Ozs7OztBQXZCUSxVQUFNLFdBOEJmLFNBQVMsR0FBQSxtQkFBQyxLQUFLLEVBQUU7QUFDYixZQUFJLElBQUksQ0FBQyxNQUFNLENBQUMsR0FBRyxDQUFDLEtBQUssQ0FBQyxFQUFFO0FBQ3hCLG1CQUFPLElBQUksQ0FBQyxNQUFNLENBQUMsR0FBRyxDQUFDLEtBQUssQ0FBQyxDQUFDO1NBQ2pDLE1BQU07QUFDSCxnQkFBSSxNQUFNLEdBQUcsQ0FBQyxJQUFJLElBQUksRUFBQSxFQUFFLElBQUksSUFBSSxFQUFBLEVBQUUsSUFBSSxJQUFJLEVBQUEsQ0FBQyxDQUFDO0FBQzVDLGdCQUFJLENBQUMsTUFBTSxDQUFDLEdBQUcsQ0FBQyxLQUFLLEVBQUUsTUFBTSxDQUFDLENBQUM7QUFDL0IsbUJBQU8sTUFBTSxDQUFDO1NBQ2pCO0tBQ0o7O0FBdENRLFVBQU0sV0F3Q2Ysa0JBQWtCLEdBQUEsNEJBQUMsS0FBSyxFQUFFO0FBQ3RCLFlBQUksQ0FBQyxTQUFTLEdBQUcsSUFBSSxDQUFDLFNBQVMsSUFBSSxJQUFJLEdBQUcsRUFBQSxDQUFDO0FBQzNDLFlBQUksSUFBSSxDQUFDLFNBQVMsQ0FBQyxHQUFHLENBQUMsS0FBSyxDQUFDLEVBQUU7QUFDM0IsbUJBQU8sSUFBSSxDQUFDLFNBQVMsQ0FBQyxHQUFHLENBQUMsS0FBSyxDQUFDLENBQUM7U0FDcEMsTUFBTTtBQUNILGdCQUFJLE1BQU0sR0FBRyxJQUFJLE9BQU8sQ0FBQyxJQUFJLElBQUksQ0FBQyxJQUFJLENBQUMsUUFBUSxDQUFDLEVBQUUsb0JBQW9CLENBQUMsQ0FBQztBQUN4RSxnQkFBSSxDQUFDLFNBQVMsQ0FBQyxHQUFHLENBQUMsS0FBSyxFQUFFLE1BQU0sQ0FBQyxDQUFDO0FBQ2xDLG1CQUFPLE1BQU0sQ0FBQztTQUNqQjtLQUNKOzs7Ozs7OztBQWpEUSxVQUFNLFdBd0RmLFdBQVcsR0FBQSx1QkFBRzs7QUFFVixZQUFJLElBQUksQ0FBQyxXQUFXLEVBQUUsT0FBTyxJQUFJLENBQUMsV0FBVyxDQUFDOztBQUU5QyxZQUFJLENBQUMsV0FBVyxHQUFHLElBQUksT0FBTyxDQUFDLElBQUksQ0FBQyxPQUFPLENBQUMsV0FBVyxDQUFDLENBQUMsQ0FBQztBQUMxRCxlQUFPLElBQUksQ0FBQyxXQUFXLENBQUM7S0FDM0I7O0FBOURRLFVBQU0sV0FnRWYsMkJBQTJCLEdBQUEscUNBQUMsU0FBUyxFQUFFOztBQUVuQyxZQUFNLE1BQU0sR0FBRyxTQUFTLENBQUMsTUFBTSxDQUFDLEdBQUcsQ0FBQyxVQUFVLEtBQUssRUFBRTtBQUNqRCxnQkFBSSxLQUFLLENBQUMsSUFBSSxLQUFLLFNBQVMsRUFDeEIsT0FBTyxLQUFLLENBQUMsSUFBSSxHQUFHLEdBQUcsR0FBRyxLQUFLLENBQUMsSUFBSSxDQUFDLEtBQ3BDLE9BQU8sS0FBSyxDQUFDLElBQUksQ0FBQztTQUMxQixDQUFDLENBQUM7O0FBRUgsWUFBSSxNQUFNLEdBQUcsS0FBSyxHQUFHLE1BQU0sQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDLEdBQUcsR0FBRyxDQUFDO0FBQzdDLFlBQUksU0FBUyxDQUFDLEdBQUcsS0FBSyxTQUFTLEVBQUU7QUFDN0Isa0JBQU0sSUFBSSxNQUFNLEdBQUcsU0FBUyxDQUFDLEdBQUcsQ0FBQztTQUNwQztBQUNELGVBQU8sTUFBTSxDQUFDO0tBQ2pCOztBQTdFUSxVQUFNLFdBK0VmLFNBQVMsR0FBQSxtQkFBQyxZQUFZLEVBQUU7QUFDcEIsWUFBSSxZQUFZLENBQUMsR0FBRyxDQUFDLElBQUksQ0FBQyxFQUFFO0FBQ3hCLG1CQUFPLEdBQUcsQ0FBQztTQUNkO0FBQ0QsWUFBTSxTQUFTLEdBQUcsSUFBSSxDQUFDLHFCQUFxQixDQUFDLFlBQVksQ0FBQyxDQUFDO0FBQzNELGVBQU8sSUFBSSxDQUFDLDJCQUEyQixDQUFDLFNBQVMsQ0FBQyxDQUFDO0tBQ3REOztBQXJGUSxVQUFNLFdBdUZmLHFCQUFxQixHQUFBLCtCQUFDLFlBQVksRUFBRTtBQUNoQyxvQkFBWSxDQUFDLEdBQUcsQ0FBQyxJQUFJLENBQUMsQ0FBQztBQUN2QixZQUFNLFdBQVcsR0FBRyxJQUFJLENBQUMsVUFBVSxDQUFDLElBQUksQ0FBQyxRQUFRLENBQUMsQ0FBQyxrQkFBa0IsQ0FBQyxJQUFJLENBQUMsRUFBRSxDQUFDLENBQUM7QUFDL0UsWUFBTSxTQUFTLEdBQUcsRUFBRSxDQUFDO0FBQ3JCLGFBQUssSUFBSSxDQUFDLEdBQUcsQ0FBQyxFQUFFLENBQUMsR0FBRyxJQUFJLENBQUMsVUFBVSxDQUFDLE1BQU0sRUFBRSxDQUFDLEVBQUUsRUFBRTtBQUM3QyxnQkFBTSxTQUFTLEdBQUcsSUFBSSxDQUFDLFVBQVUsQ0FBQyxDQUFDLENBQUMsQ0FBQztBQUNyQyxnQkFBTSxPQUFPLEdBQUcsRUFBRSxDQUFDO0FBQ25CLGdCQUFJLE9BQU8sR0FBRyxLQUFLLENBQUM7QUFDcEIsa0NBQWUsV0FBVyx5SEFBRTs7Ozs7Ozs7Ozs7O29CQUFuQixFQUFFOztBQUNQLG9CQUFNLElBQUksR0FBRyxFQUFFLENBQUMsU0FBUyxDQUFDLFNBQVMsQ0FBQyxDQUFDO0FBQ3JDLG9CQUFJLENBQUMsSUFBSSxDQUFDLE9BQU8sRUFBRSxFQUFFO0FBQ2pCLDJCQUFPLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQyxTQUFTLENBQUMsWUFBWSxDQUFDLENBQUMsQ0FBQztBQUMzQywyQkFBTyxHQUFHLElBQUksQ0FBQztpQkFDbEI7YUFDSjtBQUNELGdCQUFNLFVBQVUsR0FBRyxPQUFPLEdBQUcsT0FBTyxDQUFDLElBQUksQ0FBQyxHQUFHLENBQUMsR0FBRyxTQUFTLENBQUM7QUFDM0QscUJBQVMsQ0FBQyxJQUFJLENBQUMsRUFBQyxJQUFJLEVBQUUsU0FBUyxFQUFFLElBQUksRUFBRSxVQUFVLEVBQUMsQ0FBQyxDQUFDO1NBQ3ZEOztBQUVELFlBQU0sY0FBYyxHQUFHLEVBQUUsQ0FBQztBQUMxQixZQUFJLFVBQVUsR0FBRyxJQUFJLENBQUM7QUFDdEIsOEJBQTBCLElBQUksQ0FBQyxNQUFNLENBQUMsTUFBTSxFQUFFLHlIQUFFOzs7Ozs7Ozs7Ozs7Z0JBQXBDLE9BQU87O0FBQ2YsZ0JBQUksQ0FBQyxPQUFPLENBQUMsT0FBTyxFQUFFLEVBQUU7QUFDcEIsMEJBQVUsR0FBRyxLQUFLLENBQUM7QUFDbkIsOEJBQWMsQ0FBQyxJQUFJLENBQUMsT0FBTyxDQUFDLFNBQVMsQ0FBQyxZQUFZLENBQUMsQ0FBQyxDQUFDO2FBQ3hEO1NBQ0o7QUFDRCxvQkFBWSxVQUFPLENBQUMsSUFBSSxDQUFDLENBQUM7QUFDMUIsZUFBTyxFQUFDLE1BQU0sRUFBRSxTQUFTLEVBQUUsR0FBRyxFQUFHLFVBQVUsR0FBRyxTQUFTLEdBQUcsY0FBYyxDQUFDLElBQUksQ0FBQyxHQUFHLENBQUMsQUFBQyxFQUFDLENBQUM7S0FFeEY7O0FBckhRLFVBQU0sV0F1SGYsb0JBQW9CLEdBQUEsZ0NBQUc7QUFDbkIsWUFBTSxZQUFZLEdBQUcsSUFBSSxHQUFHLEVBQUUsQ0FBQztBQUMvQixlQUFPLElBQUksQ0FBQyxxQkFBcUIsQ0FBQyxZQUFZLENBQUMsQ0FBQztLQUNuRDs7V0ExSFEsTUFBTTtHQUFTLE9BQU87Ozs7SUFpSXRCLE9BQU87Y0FBUCxPQUFPOztBQUNMLGFBREYsT0FBTyxDQUNKLFNBQVMsRUFBRTs4QkFEZCxPQUFPOztBQUVaLDZCQUFNLFNBQVMsRUFBRSxPQUFPLENBQUMsQ0FBQztLQUM3Qjs7OztBQUhRLFdBQU8sV0FLaEIsU0FBUyxHQUFBLG1CQUFDLFlBQVksRUFBRTtBQUNwQixZQUFJLFlBQVksQ0FBQyxHQUFHLENBQUMsSUFBSSxDQUFDLEVBQUU7QUFDeEIsbUJBQU8sR0FBRyxDQUFDO1NBQ2Q7QUFDRCxvQkFBWSxDQUFDLEdBQUcsQ0FBQyxJQUFJLENBQUMsQ0FBQzs7QUFFdkIsWUFBTSxRQUFRLEdBQUcsSUFBSSxDQUFDLE9BQU8sQ0FBQyxJQUFJLEVBQUUsSUFBSSxDQUFDLENBQUM7QUFDMUMsWUFBTSxLQUFLLEdBQUcsR0FBRyxHQUFHLFFBQVEsQ0FBQyxTQUFTLENBQUMsWUFBWSxDQUFDLEdBQUcsR0FBRyxDQUFDO0FBQzNELG9CQUFZLFVBQU8sQ0FBQyxJQUFJLENBQUMsQ0FBQztBQUMxQixlQUFPLEtBQUssQ0FBQztLQUNoQjs7V0FmUSxPQUFPO0dBQVMsT0FBTzs7O0FBbUI3QixJQUFNLFVBQVUsR0FBRyxJQUFJLFFBQVEsQ0FBQyxRQUFRLENBQUMsQ0FBQzs7QUFDMUMsSUFBTSxVQUFVLEdBQUcsSUFBSSxRQUFRLENBQUMsUUFBUSxDQUFDLENBQUM7O0FBQzFDLElBQU0sV0FBVyxHQUFHLElBQUksUUFBUSxDQUFDLFNBQVMsQ0FBQyxDQUFDOzs7O0FBRzVDLElBQU0sUUFBUSxHQUFHLElBQUksSUFBSSxFQUFFLENBQUM7OztBQUVuQyxRQUFRLENBQUMsS0FBSyxHQUFHLElBQUksQ0FBQzs7QUFFdEIsUUFBUSxDQUFDLE9BQU8sR0FBRyxZQUFZLEVBQUUsQ0FBQzs7SUFFckIsUUFBUTtBQUNOLGFBREYsUUFBUSxHQUNIOzhCQURMLFFBQVE7O0FBRWIsWUFBSSxDQUFDLEdBQUcsR0FBRyxJQUFJLEdBQUcsRUFBRSxDQUFDO0tBQ3hCOzs7Ozs7Ozs7QUFIUSxZQUFRLFdBV2pCLEdBQUcsR0FBQSxhQUFDLEdBQUcsRUFBRSxHQUFHLEVBQUU7QUFDVixZQUFJLENBQUMsSUFBSSxDQUFDLEdBQUcsQ0FBQyxHQUFHLENBQUMsR0FBRyxDQUFDLEVBQUU7O0FBRXBCLGdCQUFJLENBQUMsR0FBRyxDQUFDLEdBQUcsQ0FBQyxHQUFHLEVBQUUsSUFBSSxHQUFHLEVBQUUsQ0FBQyxDQUFDO1NBQ2hDO0FBQ0QsWUFBTSxNQUFNLEdBQUcsSUFBSSxDQUFDLEdBQUcsQ0FBQyxHQUFHLENBQUMsR0FBRyxDQUFDLENBQUM7QUFDakMsWUFBSSxDQUFDLE1BQU0sQ0FBQyxHQUFHLENBQUMsR0FBRyxDQUFDLEVBQUU7QUFDbEIsZ0JBQU0sRUFBRSxHQUFHLElBQUksSUFBSSxFQUFFLENBQUM7QUFDdEIsa0JBQU0sQ0FBQyxHQUFHLENBQUMsR0FBRyxFQUFFLEVBQUUsQ0FBQyxDQUFDO0FBQ3BCLG1CQUFPLEVBQUUsQ0FBQztTQUNiLE1BQU07QUFDSCxtQkFBTyxNQUFNLENBQUMsR0FBRyxDQUFDLEdBQUcsQ0FBQyxDQUFDO1NBQzFCO0tBQ0o7Ozs7Ozs7OztBQXhCUSxZQUFRLFdBZ0NqQixHQUFHLEdBQUEsYUFBQyxHQUFHLEVBQUUsR0FBRyxFQUFFLEVBQUUsRUFBRTtBQUNkLFlBQUksQ0FBQyxJQUFJLENBQUMsR0FBRyxDQUFDLEdBQUcsQ0FBQyxHQUFHLENBQUMsRUFBRTs7QUFFcEIsZ0JBQUksQ0FBQyxHQUFHLENBQUMsR0FBRyxDQUFDLEdBQUcsRUFBRSxJQUFJLEdBQUcsRUFBRSxDQUFDLENBQUM7U0FDaEM7QUFDRCxZQUFJLENBQUMsR0FBRyxDQUFDLEdBQUcsQ0FBQyxHQUFHLENBQUMsQ0FBQyxHQUFHLENBQUMsR0FBRyxFQUFFLEVBQUUsQ0FBQyxDQUFDO0tBQ2xDOzs7Ozs7Ozs7QUF0Q1EsWUFBUSxXQThDakIsR0FBRyxHQUFBLGFBQUMsR0FBRyxFQUFFLEdBQUcsRUFBRTtBQUNWLGVBQU8sSUFBSSxDQUFDLEdBQUcsQ0FBQyxHQUFHLENBQUMsR0FBRyxDQUFDLElBQUksSUFBSSxDQUFDLEdBQUcsQ0FBQyxHQUFHLENBQUMsR0FBRyxDQUFDLENBQUMsR0FBRyxDQUFDLEdBQUcsQ0FBQyxDQUFDO0tBQzFEOzs7Ozs7OztBQWhEUSxZQUFRLFdBdURqQixrQkFBa0IsR0FBQSw0QkFBQyxHQUFHLEVBQUU7QUFDcEIsWUFBSSxDQUFDLElBQUksQ0FBQyxHQUFHLENBQUMsR0FBRyxDQUFDLEdBQUcsQ0FBQyxFQUFFOztBQUVwQixtQkFBTyxJQUFJLENBQUM7U0FDZjtBQUNELFlBQU0sVUFBVSxHQUFHLElBQUksSUFBSSxFQUFFLENBQUM7QUFDOUIsWUFBSSxJQUFJLENBQUMsR0FBRyxDQUFDLEdBQUcsQ0FBQyxHQUFHLENBQUMsRUFBRTtBQUNuQixrQ0FBZSxJQUFJLENBQUMsR0FBRyxDQUFDLEdBQUcsQ0FBQyxHQUFHLENBQUMsQ0FBQyxNQUFNLEVBQUUseUhBQUU7Ozs7Ozs7Ozs7OztvQkFBbEMsRUFBRTs7QUFDUCxzQ0FBZSxFQUFFLENBQUMsUUFBUSxFQUFFLHlIQUFFOzs7Ozs7Ozs7Ozs7d0JBQXJCLEVBQUU7O0FBQ1AsOEJBQVUsQ0FBQyxPQUFPLENBQUMsRUFBRSxDQUFDLENBQUM7aUJBQzFCO2FBQ0o7U0FDSjtBQUNELGVBQU8sVUFBVSxDQUFDO0tBQ3JCOztXQXJFUSxRQUFROzs7Ozs7Ozs7Ozs7Ozs7Ozs0QkMvY0ssaUJBQWlCOztJQUEvQixRQUFROzs0QkFDRyxpQkFBaUI7O0lBQTVCLEtBQUs7Ozs7Ozs7Ozs7O0FBVVYsU0FBUyxjQUFjLENBQUMsR0FBRyxFQUFFLENBQUMsRUFBRSxLQUFLLEVBQUUsR0FBRyxFQUFFO0FBQy9DLGdCQUFZLENBQUM7QUFDYixRQUFNLElBQUksR0FBRyxRQUFRLENBQUMsbUJBQW1CLENBQUMsR0FBRyxFQUFFLEtBQUssRUFBRSxHQUFHLENBQUMsQ0FBQztBQUMzRCxRQUFNLFNBQVMsR0FBRyxDQUFDLENBQUMsa0JBQWtCLENBQUMsSUFBSSxDQUFDLENBQUM7QUFDN0MsUUFBSSxPQUFPLFlBQUEsQ0FBQztBQUNaLFFBQUksVUFBVSxHQUFHLEVBQUUsQ0FBQztBQUNwQixRQUFJLENBQUMsU0FBUyxFQUFFO0FBQ1osZUFBTyxHQUFHLEtBQUssQ0FBQztBQUNoQixrQkFBVSxHQUFHLDZCQUE2QixDQUFDO0tBQzlDLE1BQU07QUFDSCxlQUFPLEdBQUcsSUFBSSxDQUFDO0FBQ2Ysa0JBQVUsR0FBRyxTQUFTLENBQUMsUUFBUSxFQUFFLENBQUM7S0FDckM7QUFDRCxXQUFPO0FBQ0gsZUFBTyxFQUFFLE9BQU87QUFDaEIsa0JBQVUsRUFBRSxVQUFVO0FBQ3RCLGlCQUFTLEVBQUUsSUFBSSxDQUFDLEtBQUs7QUFDckIsZUFBTyxFQUFFLElBQUksQ0FBQyxHQUFHO0tBQ3BCLENBQUM7Q0FDTDs7QUFFTSxTQUFTLHFCQUFxQixDQUFDLEdBQUcsRUFBRSxDQUFDLEVBQUUsR0FBRyxFQUFFO0FBQy9DLFFBQU0sSUFBSSxHQUFHLFFBQVEsQ0FBQyxtQkFBbUIsQ0FBQyxHQUFHLEVBQUUsR0FBRyxFQUFFLEdBQUcsQ0FBQyxDQUFDO0FBQ3pELFFBQU0sU0FBUyxHQUFHLENBQUMsQ0FBQyxrQkFBa0IsQ0FBQyxJQUFJLENBQUMsQ0FBQztBQUM3QyxRQUFNLGdCQUFnQixHQUFHLEVBQUUsQ0FBQzs7QUFFNUIsYUFBUyxDQUFDLFFBQVEsRUFBRSxDQUFDLE9BQU8sQ0FBQyxVQUFVLEVBQUUsRUFBRTtBQUN2QyxZQUFJLEVBQUUsWUFBWSxLQUFLLENBQUMsTUFBTSxFQUFFO0FBQzVCLDRCQUFnQixDQUFDLElBQUksQ0FBQyxFQUFFLENBQUMsb0JBQW9CLEVBQUUsQ0FBQyxDQUFDO1NBQ3BEO0tBQ0osQ0FBQyxDQUFDO0FBQ0gsV0FBTyxnQkFBZ0IsQ0FBQztDQUMzQjs7QUFFRCxTQUFTLGlCQUFpQixDQUFDLE9BQU8sRUFBRTtBQUNoQyxRQUFNLE9BQU8sR0FBRyxJQUFJLEdBQUcsRUFBRSxDQUFDOztBQUUxQixhQUFTLFFBQVEsQ0FBQyxJQUFJLEVBQUU7QUFDcEIsZUFBTyxJQUFJLEtBQUssUUFBUSxJQUFJLElBQUksS0FBSyxPQUFPLElBQUksSUFBSSxLQUFLLElBQUksQ0FBQztLQUNqRTs7QUFFRCxXQUFPLENBQUMsT0FBTyxDQUFDLFVBQUMsR0FBRyxFQUFFLENBQUMsRUFBSztBQUN4Qiw2QkFBZSxHQUFHLGtIQUFFOzs7Ozs7Ozs7Ozs7Z0JBQVgsRUFBRTs7QUFDUCxnQkFBSSxJQUFJLFlBQUEsQ0FBQztBQUNULGdCQUFJLEVBQUUsS0FBSyxLQUFLLENBQUMsVUFBVSxFQUFFLElBQUksR0FBRyxRQUFRLENBQUMsS0FDeEMsSUFBSSxFQUFFLEtBQUssS0FBSyxDQUFDLFdBQVcsRUFBRSxJQUFJLEdBQUcsTUFBTSxDQUFDLEtBQzVDLElBQUksRUFBRSxLQUFLLEtBQUssQ0FBQyxVQUFVLEVBQUUsSUFBSSxHQUFHLFFBQVEsQ0FBQyxLQUM3QyxJQUFJLEVBQUUsWUFBWSxLQUFLLENBQUMsTUFBTSxFQUFFLElBQUksR0FBRyxJQUFJLENBQUMsS0FDNUMsSUFBSSxFQUFFLFlBQVksS0FBSyxDQUFDLE9BQU8sRUFBRSxJQUFJLEdBQUcsT0FBTyxDQUFDLEtBQ2hELElBQUksRUFBRSxZQUFZLEtBQUssQ0FBQyxPQUFPLEVBQUUsSUFBSSxHQUFHLFFBQVEsQ0FBQzs7QUFFdEQsZ0JBQUksQ0FBQyxPQUFPLENBQUMsR0FBRyxDQUFDLENBQUMsQ0FBQyxJQUFJLE9BQU8sQ0FBQyxHQUFHLENBQUMsQ0FBQyxDQUFDLEtBQUssSUFBSSxFQUFFO0FBQzVDLHVCQUFPLENBQUMsR0FBRyxDQUFDLENBQUMsRUFBRSxJQUFJLENBQUMsQ0FBQztBQUNyQix5QkFBUzthQUNaOztBQUVELGdCQUFJLFFBQVEsQ0FBQyxJQUFJLENBQUMsSUFBSSxRQUFRLENBQUMsT0FBTyxDQUFDLEdBQUcsQ0FBQyxDQUFDLENBQUMsQ0FBQyxFQUFFO0FBQzVDLHVCQUFPLENBQUMsR0FBRyxDQUFDLENBQUMsRUFBRSxRQUFRLENBQUMsQ0FBQzthQUM1QixNQUFNO0FBQ0gsdUJBQU8sQ0FBQyxHQUFHLENBQUMsQ0FBQyxFQUFFLFNBQVMsQ0FBQyxDQUFDO0FBQzFCLHNCQUFNO2FBQ1Q7U0FDSjtBQUNELFlBQUksR0FBRyxDQUFDLElBQUksS0FBSyxDQUFDLEVBQUU7QUFDaEIsbUJBQU8sQ0FBQyxHQUFHLENBQUMsQ0FBQyxFQUFFLFNBQVMsQ0FBQyxDQUFDO1NBQzdCO0tBQ0osQ0FBQyxDQUFDO0FBQ0gsV0FBTyxPQUFPLENBQUM7Q0FDbEI7Ozs7Ozs7OztBQVFNLFNBQVMsZUFBZSxDQUFDLENBQUMsRUFBRSxJQUFJLEVBQUU7O0FBRXJDLFFBQU0sU0FBUyxHQUFHLENBQUMsQ0FBQyxrQkFBa0IsQ0FBQyxJQUFJLENBQUMsQ0FBQztBQUM3QyxRQUFNLE9BQU8sR0FBRyxrQkFBa0IsQ0FBQyxTQUFTLENBQUMsQ0FBQztBQUM5QyxXQUFPLGlCQUFpQixDQUFDLE9BQU8sQ0FBQyxDQUFDO0NBQ3JDOzs7Ozs7QUFNRCxTQUFTLElBQUksQ0FBQyxDQUFDLEVBQUU7QUFDYixXQUFPLENBQUMsSUFBSSxDQUFDLENBQUMsQ0FBQyxDQUFDO0FBQ2hCLFdBQU8sQ0FBQyxDQUFDO0NBQ1o7O0FBRU0sU0FBUyxrQkFBa0IsQ0FBQyxNQUFNLEVBQUUsR0FBRyxFQUFFOztBQUU1QyxRQUFNLFFBQVEsR0FBRyxRQUFRLENBQUMscUJBQXFCLENBQUMsTUFBTSxDQUFDLEdBQUcsRUFBRSxHQUFHLENBQUMsQ0FBQzs7QUFFakUsUUFBSSxRQUFRLENBQUMsSUFBSSxLQUFLLFlBQVksRUFBRTtBQUNoQyxZQUFJLE1BQU0sWUFBQTtZQUFFLElBQUksWUFBQTtZQUFFLEVBQUUsWUFBQSxDQUFDOztBQUVyQixZQUFJLFFBQVEsQ0FBQyxJQUFJLEtBQUssSUFBSSxFQUFFO0FBQ3hCLGtCQUFNLEdBQUcsRUFBRSxDQUFDO0FBQ1osZ0JBQUksR0FBRyxHQUFHLENBQUM7QUFDWCxjQUFFLEdBQUcsR0FBRyxDQUFDO1NBQ1osTUFBTSxJQUFJLFFBQVEsQ0FBQyxhQUFhLENBQUMsUUFBUSxDQUFDLElBQUksQ0FBQyxFQUFFO0FBQzlDLGtCQUFNLEdBQUcsRUFBRSxDQUFDO0FBQ1osZ0JBQUksR0FBRyxFQUFFLEdBQUcsUUFBUSxDQUFDLElBQUksQ0FBQyxHQUFHLENBQUM7U0FDakMsTUFBTTtBQUNILHNCQUFNLEdBQUcsUUFBUSxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUM7QUFDNUIsb0JBQUksR0FBRyxRQUFRLENBQUMsSUFBSSxDQUFDLEtBQUssQ0FBQztBQUMzQixrQkFBRSxHQUFHLFFBQVEsQ0FBQyxJQUFJLENBQUMsR0FBRyxDQUFDO2FBQzFCO0FBQ0QsWUFBTSxNQUFNLEdBQUcsaUJBQWlCLENBQUMsaUJBQWlCLENBQUMsUUFBUSxDQUFDLEVBQUUsQ0FBQyxDQUFDLENBQUM7O0FBRWpFLFlBQU0sSUFBSSxHQUFHLEVBQUUsQ0FBQztBQUNoQiw4QkFBbUIsTUFBTSx5SEFBRTs7Ozs7Ozs7Ozs7O2dCQUFqQixDQUFDO2dCQUFFLENBQUM7O0FBQ1YsZ0JBQUksQ0FBQyxDQUFDLFVBQVUsQ0FBQyxNQUFNLENBQUMsRUFBRTtBQUN0QixvQkFBSSxDQUFDLElBQUksQ0FBQyxFQUFDLElBQUksRUFBRSxDQUFDLEVBQUUsSUFBSSxFQUFFLENBQUMsRUFBQyxDQUFDLENBQUM7YUFDakM7U0FDSjtBQUNELGVBQU8sSUFBSSxDQUFDLEVBQUMsSUFBSSxFQUFFLElBQUksRUFBRSxJQUFJLEVBQUUsSUFBSSxFQUFFLEVBQUUsRUFBRSxFQUFFLEVBQUMsQ0FBQyxDQUFDO0tBRWpELE1BQU07O0FBRUgsWUFBTSxVQUFVLEdBQUcsUUFBUSxDQUFDLElBQUksQ0FBQyxNQUFNLENBQUM7QUFDeEMsWUFBTSxLQUFLLEdBQUcsZUFBZSxDQUFDLE1BQU0sQ0FBQyxDQUFDLEVBQUUsVUFBVSxDQUFDLENBQUM7O0FBRXBELFlBQU0sWUFBWSxHQUFHLFFBQVEsQ0FBQyxJQUFJLENBQUMsUUFBUSxDQUFDO0FBQzVDLFlBQUksTUFBTSxZQUFBO1lBQUUsSUFBSSxZQUFBO1lBQUUsRUFBRSxZQUFBO1lBQUUsTUFBTSxZQUFBLENBQUM7QUFDN0IsWUFBSSxRQUFRLENBQUMsSUFBSSxLQUFLLFdBQVcsRUFBRTtBQUMvQixnQkFBTSxRQUFRLEdBQUcsWUFBWSxDQUFDLElBQUksQ0FBQztBQUNuQyxnQkFBSSxRQUFRLENBQUMsYUFBYSxDQUFDLFlBQVksQ0FBQyxFQUFFO0FBQ3RDLHNCQUFNLEdBQUcsRUFBRSxDQUFDO0FBQ1osb0JBQUksR0FBRyxZQUFZLENBQUMsR0FBRyxDQUFDO2FBQzNCLE1BQU07O0FBRUgsMEJBQU0sR0FBRyxRQUFRLENBQUM7QUFDbEIsd0JBQUksR0FBRyxZQUFZLENBQUMsS0FBSyxDQUFDO2lCQUM3QjtBQUNELGNBQUUsR0FBRyxZQUFZLENBQUMsR0FBRyxDQUFDO0FBQ3RCLGtCQUFNLEdBQUcsVUFBQSxDQUFDO3VCQUFJLEFBQUMsd0JBQXVCLENBQUUsSUFBSSxDQUFDLENBQUMsQ0FBQzs7YUFBQSxDQUFDO1NBQ25ELE1BQU0sSUFBSSxRQUFRLENBQUMsSUFBSSxLQUFLLFlBQVksRUFBRTtBQUN2QyxrQkFBTSxHQUFHLFlBQVksQ0FBQyxLQUFLLENBQUM7QUFDNUIsZ0JBQUksR0FBRyxZQUFZLENBQUMsS0FBSyxHQUFHLENBQUMsQ0FBQztBQUM5QixjQUFFLEdBQUcsWUFBWSxDQUFDLEdBQUcsR0FBRyxDQUFDLENBQUM7QUFDMUIsa0JBQU0sR0FBRyxVQUFBLENBQUM7dUJBQUksSUFBSTthQUFBLENBQUE7U0FDckI7O0FBRUQsWUFBTSxJQUFJLEdBQUcsRUFBRSxDQUFDO0FBQ2hCLDhCQUFtQixLQUFLLHlIQUFFOzs7Ozs7Ozs7Ozs7Z0JBQWhCLENBQUM7Z0JBQUUsQ0FBQzs7O0FBRVYsZ0JBQUksQ0FBQyxLQUFLLElBQUksSUFBSSxDQUFDLENBQUMsVUFBVSxDQUFDLE1BQU0sQ0FBQyxJQUFJLE1BQU0sQ0FBQyxDQUFDLENBQUMsRUFBRTtBQUNqRCxvQkFBSSxDQUFDLElBQUksQ0FBQyxFQUFDLElBQUksRUFBRSxDQUFDLEVBQUUsSUFBSSxFQUFFLENBQUMsRUFBQyxDQUFDLENBQUM7YUFDakM7U0FDSjtBQUNELGVBQU8sSUFBSSxDQUFDLEVBQUMsSUFBSSxFQUFFLElBQUksRUFBRSxJQUFJLEVBQUUsSUFBSSxFQUFFLEVBQUUsRUFBRSxFQUFFLEVBQUMsQ0FBQyxDQUFDO0tBQ2pEO0NBQ0o7O0FBR0QsU0FBUyxRQUFRLENBQUMsRUFBRSxFQUFFLEVBQUUsRUFBRTtBQUN0QixRQUFNLEdBQUcsR0FBRyxJQUFJLEdBQUcsRUFBRSxDQUFDOztBQUV0QixhQUFTLFFBQVEsQ0FBQyxFQUFFLEVBQUUsRUFBRSxFQUFFO0FBQ3RCLFlBQU0sR0FBRyxHQUFHLElBQUksR0FBRyxFQUFFLENBQUM7QUFDdEIsWUFBSSxFQUFFLEVBQUUsRUFBRSxDQUFDLE9BQU8sQ0FBQyxVQUFBLENBQUM7bUJBQUksR0FBRyxDQUFDLEdBQUcsQ0FBQyxDQUFDLENBQUM7U0FBQSxDQUFDLENBQUM7QUFDcEMsWUFBSSxFQUFFLEVBQUUsRUFBRSxDQUFDLE9BQU8sQ0FBQyxVQUFBLENBQUM7bUJBQUksR0FBRyxDQUFDLEdBQUcsQ0FBQyxDQUFDLENBQUM7U0FBQSxDQUFDLENBQUM7QUFDcEMsZUFBTyxHQUFHLENBQUM7S0FDZDs7QUFFRCxRQUFJLEVBQUUsRUFBRSxFQUFFLENBQUMsT0FBTyxDQUFDLFVBQUMsRUFBRSxFQUFFLENBQUM7ZUFBSyxHQUFHLENBQUMsR0FBRyxDQUFDLENBQUMsRUFBRSxFQUFFLENBQUM7S0FBQSxDQUFDLENBQUM7QUFDOUMsUUFBSSxFQUFFLEVBQUUsRUFBRSxDQUFDLE9BQU8sQ0FBQyxVQUFDLEVBQUUsRUFBRSxDQUFDO2VBQUssR0FBRyxDQUFDLEdBQUcsQ0FBQyxDQUFDLEVBQUUsUUFBUSxDQUFDLEdBQUcsQ0FBQyxHQUFHLENBQUMsQ0FBQyxDQUFDLEVBQUUsRUFBRSxDQUFDLEdBQUcsQ0FBQyxDQUFDLENBQUMsQ0FBQyxDQUFDO0tBQUEsQ0FBQyxDQUFDO0FBQzNFLFdBQU8sR0FBRyxDQUFDO0NBQ2Q7O0FBRUQsU0FBUyxzQkFBc0IsQ0FBQyxFQUFFLEVBQUUsRUFBRSxFQUFFO0FBQ3BDLFFBQU0sR0FBRyxHQUFHLElBQUksR0FBRyxFQUFFLENBQUM7QUFDdEIsTUFBRSxDQUFDLE9BQU8sQ0FBQyxVQUFDLEVBQUUsRUFBRSxDQUFDO2VBQUssR0FBRyxDQUFDLEdBQUcsQ0FBQyxDQUFDLEVBQUUsRUFBRSxDQUFDO0tBQUEsQ0FBQyxDQUFDO0FBQ3RDLE1BQUUsQ0FBQyxPQUFPLENBQUMsVUFBQyxFQUFFLEVBQUUsQ0FBQyxFQUFLO0FBQ2xCLFlBQUksQ0FBQyxHQUFHLENBQUMsR0FBRyxDQUFDLENBQUMsQ0FBQyxFQUFFLEdBQUcsQ0FBQyxHQUFHLENBQUMsQ0FBQyxFQUFFLEVBQUUsQ0FBQyxDQUFBO0tBQ2xDLENBQUMsQ0FBQztBQUNILFdBQU8sR0FBRyxDQUFDO0NBQ2Q7Ozs7QUFJRCxTQUFTLFVBQVUsQ0FBQyxHQUFHLEVBQUU7QUFDckIsUUFBSSxNQUFNLEdBQUcsSUFBSSxHQUFHLEVBQUUsQ0FBQztBQUN2QixPQUFHLENBQUMsT0FBTyxDQUFDLFVBQUMsRUFBRSxFQUFFLENBQUMsRUFBSztBQUNuQixjQUFNLENBQUMsR0FBRyxDQUFDLENBQUMsRUFBRSxFQUFFLENBQUMsUUFBUSxFQUFFLENBQUMsQ0FBQztLQUNoQyxDQUFDLENBQUM7QUFDSCxXQUFPLE1BQU0sQ0FBQztDQUNqQjs7O0FBR0QsU0FBUyxrQkFBa0IsQ0FBQyxHQUFHLEVBQUU7O0FBRTdCLFFBQU0sWUFBWSxHQUFHLEVBQUUsQ0FBQzs7QUFFeEIsYUFBUyxRQUFRLENBQUMsSUFBSSxFQUFFO0FBQ3BCLFlBQUksSUFBSSxZQUFZLEtBQUssQ0FBQyxPQUFPLElBQzdCLElBQUksQ0FBQyxPQUFPLENBQUMsV0FBVyxFQUFFLElBQUksQ0FBQyxFQUFFOztBQUNqQyxvQkFBSSxRQUFRLEdBQUcsSUFBSSxHQUFHLEVBQUUsQ0FBQztBQUN6QixvQkFBTSxVQUFVLEdBQUcsSUFBSSxDQUFDLE9BQU8sQ0FBQyxXQUFXLEVBQUUsSUFBSSxDQUFDLENBQUMsUUFBUSxFQUFFLENBQUM7O0FBRTlELDBCQUFVLENBQUMsT0FBTyxDQUFDLFVBQUEsRUFBRSxFQUFJO0FBQ3JCLHdCQUFJLFlBQVksQ0FBQyxPQUFPLENBQUMsRUFBRSxDQUFDLEdBQUcsQ0FBQyxDQUFDLEVBQUU7QUFDL0IsK0JBQU87cUJBQ1Y7QUFDRCxnQ0FBWSxDQUFDLElBQUksQ0FBQyxFQUFFLENBQUMsQ0FBQztBQUN0Qiw0QkFBUSxHQUFHLFFBQVEsQ0FBQyxRQUFRLEVBQUUsUUFBUSxDQUFDLEVBQUUsQ0FBQyxDQUFDLENBQUM7QUFDNUMsZ0NBQVksQ0FBQyxHQUFHLEVBQUUsQ0FBQztpQkFDdEIsQ0FBQyxDQUFDO0FBQ0g7dUJBQU8sc0JBQXNCLENBQUMsVUFBVSxDQUFDLElBQUksQ0FBQyxLQUFLLENBQUMsRUFBRSxRQUFRLENBQUM7a0JBQUM7Ozs7U0FDbkUsTUFBTTtBQUNILG1CQUFPLElBQUksR0FBRyxFQUFFLENBQUM7U0FDcEI7S0FDSjs7QUFFRCxRQUFJLE1BQU0sR0FBRyxJQUFJLEdBQUcsRUFBRSxDQUFDO0FBQ3ZCLE9BQUcsQ0FBQyxRQUFRLEVBQUUsQ0FBQyxPQUFPLENBQUMsVUFBQSxFQUFFLEVBQUk7QUFDekIsY0FBTSxHQUFHLFFBQVEsQ0FBQyxNQUFNLEVBQUUsUUFBUSxDQUFDLEVBQUUsQ0FBQyxDQUFDLENBQUE7S0FDMUMsQ0FBQyxDQUFDOztBQUVILFdBQU8sTUFBTSxDQUFDO0NBQ2pCOztBQUVNLFNBQVMsb0JBQW9CLENBQUMsR0FBRyxFQUFFLENBQUMsRUFBRSxHQUFHLEVBQUU7QUFDOUMsUUFBTSxJQUFJLEdBQUcsUUFBUSxDQUFDLG1CQUFtQixDQUFDLEdBQUcsRUFBRSxHQUFHLEVBQUUsR0FBRyxDQUFDLENBQUM7QUFDekQsUUFBTSxTQUFTLEdBQUcsQ0FBQyxDQUFDLGtCQUFrQixDQUFDLElBQUksQ0FBQyxDQUFDOztBQUU3QyxRQUFNLE1BQU0sR0FBRyxFQUFFLENBQUM7QUFDbEIsUUFBSSxTQUFTLEtBQUssSUFBSSxFQUFFO0FBQ3BCLGVBQU8sTUFBTSxDQUFDO0tBQ2pCO0FBQ0QsYUFBUyxDQUFDLFFBQVEsRUFBRSxDQUFDLE9BQU8sQ0FBQyxVQUFVLEVBQUUsRUFBRTtBQUN2QyxZQUFJLEVBQUUsWUFBWSxLQUFLLENBQUMsTUFBTSxJQUFJLEVBQUUsQ0FBQyxVQUFVLEVBQUU7QUFDN0MsZ0JBQU0sTUFBTSxHQUFHLEVBQUUsQ0FBQyxVQUFVLENBQUM7QUFDN0IsZ0JBQUksRUFBRSxZQUFBLENBQUM7QUFDUCxvQkFBUSxNQUFNLENBQUMsSUFBSTtBQUNmLHFCQUFLLG9CQUFvQjtBQUFHLHNCQUFFLEdBQUcsTUFBTSxDQUFDLEtBQUssQ0FBQyxBQUFDLE1BQU07QUFBQSxBQUNyRCxxQkFBSyxxQkFBcUI7QUFBRyxzQkFBRSxHQUFHLE1BQU0sQ0FBQyxFQUFFLENBQUMsS0FBSyxDQUFDLEFBQUMsTUFBTTtBQUFBLGFBQzVEO0FBQ0QsZ0JBQU0sSUFBSSxHQUFHLEVBQUMsS0FBSyxFQUFFLE1BQU0sQ0FBQyxLQUFLLEVBQUUsR0FBRyxFQUFFLE1BQU0sQ0FBQyxHQUFHLEVBQUUsRUFBRSxFQUFFLEVBQUUsRUFBQyxDQUFDO0FBQzVELGtCQUFNLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQyxDQUFDO1NBQ3JCO0tBQ0osQ0FBQyxDQUFDO0FBQ0gsV0FBTyxNQUFNLENBQUM7Q0FDakI7OztBQUdELFNBQVMsaUJBQWlCLENBQUMsRUFBRSxFQUFFO0FBQzNCLFFBQUksTUFBTSxHQUFHLEVBQUUsQ0FBQztBQUNoQixRQUFJLE1BQU0sR0FBRyxJQUFJLEdBQUcsRUFBRSxDQUFDO0FBQ3ZCLFdBQU8sTUFBTSxLQUFLLElBQUksRUFBRTtBQUNwQixZQUFJLFNBQVMsR0FBRyxJQUFJLEdBQUcsRUFBRSxDQUFDO0FBQzFCLDhCQUFtQixNQUFNLENBQUMsU0FBUyxDQUFDLE1BQU0sRUFBRSx5SEFBRTs7Ozs7Ozs7Ozs7O2dCQUFyQyxNQUFNOztBQUNYLHFCQUFTLEdBQUcsUUFBUSxDQUFDLFNBQVMsRUFBRSxVQUFVLENBQUMsTUFBTSxDQUFDLENBQUMsQ0FBQztTQUN2RDtBQUNELGNBQU0sR0FBRyxzQkFBc0IsQ0FBQyxNQUFNLEVBQUUsU0FBUyxDQUFDLENBQUM7QUFDbkQsY0FBTSxHQUFHLE1BQU0sQ0FBQyxLQUFLLENBQUM7S0FDekI7QUFDRCxXQUFPLE1BQU0sQ0FBQztDQUNqQjs7Ozs7QUNqUkQsSUFBSSxJQUFJLEdBQUcsT0FBTyxDQUFDLE1BQU0sQ0FBQyxDQUFDOztBQUUzQixTQUFTLFdBQVcsQ0FBQyxHQUFHLEVBQUUsUUFBUSxFQUFFO0FBQ2hDLFFBQUksUUFBUSxHQUFHLEVBQUUsQ0FBQzs7QUFFbEIsUUFBSSxHQUFHLEdBQUcsUUFBUSxLQUFLLFNBQVMsR0FBRyxDQUFDLEdBQUcsUUFBUSxDQUFDOztBQUVoRCxhQUFTLFFBQVEsQ0FBQyxJQUFJLEVBQUU7QUFDcEIsWUFBSSxDQUFDLFFBQVEsQ0FBQyxHQUFHLEdBQUcsQ0FBQztBQUNyQixnQkFBUSxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsQ0FBQztBQUNwQixXQUFHLEVBQUUsQ0FBQztLQUNUOzs7QUFHRCxhQUFTLGlCQUFpQixDQUFDLElBQUksRUFBRTtBQUM3QixZQUFJLElBQUksSUFBSSxJQUFJLENBQUMsY0FBYyxDQUFDLE1BQU0sQ0FBQyxFQUFFO0FBQ3JDLG9CQUFRLENBQUMsSUFBSSxDQUFDLENBQUM7U0FDbEI7QUFDRCxZQUFJLElBQUksSUFBSSxPQUFPLElBQUksS0FBSyxRQUFRLEVBQUU7QUFDbEMsaUJBQUssSUFBSSxDQUFDLElBQUksSUFBSSxFQUFFO0FBQ2hCLGlDQUFpQixDQUFDLElBQUksQ0FBQyxDQUFDLENBQUMsQ0FBQyxDQUFDO2FBQzlCO1NBQ0o7S0FDSjs7QUFFRCxxQkFBaUIsQ0FBQyxHQUFHLENBQUMsQ0FBQzs7QUFFdkIsV0FBTyxRQUFRLENBQUM7Q0FDbkI7O0FBRUQsU0FBUyxZQUFZLENBQUMsR0FBRyxFQUFFO0FBQ3ZCLFdBQU8sQ0FBQyxHQUFHLENBQUMsSUFBSSxDQUFDLE9BQU8sQ0FBQyxHQUFHLEVBQUUsRUFBQyxLQUFLLEVBQUUsSUFBSSxFQUFDLENBQUMsQ0FBQyxDQUFDO0NBQ2pEOztBQUVELE9BQU8sQ0FBQyxXQUFXLEdBQUcsV0FBVyxDQUFDO0FBQ2xDLE9BQU8sQ0FBQyxZQUFZLEdBQUcsWUFBWSxDQUFDOzs7Ozs7Ozs0QkMvQmIsaUJBQWlCOztJQUE1QixLQUFLOzs4QkFDUSxtQkFBbUI7O0lBQWhDLE9BQU87Ozs7NkJBRUssa0JBQWtCOztJQUE5QixNQUFNOzt3QkFDUSxZQUFZOztJQUExQixRQUFROzs0QkFLTSxpQkFBaUI7O0lBQS9CLFFBQVE7OzJCQUNTLGVBQWU7O0lBQWhDLFdBQVc7OzZCQUNRLGtCQUFrQjs7SUFBckMsYUFBYTs7QUFkekIsSUFBTSxLQUFLLEdBQUcsT0FBTyxDQUFDLGtCQUFrQixDQUFDLENBQUM7QUFDMUMsSUFBTSxXQUFXLEdBQUcsT0FBTyxDQUFDLHdCQUF3QixDQUFDLENBQUM7QUFDdEQsSUFBTSxHQUFHLEdBQUcsT0FBTyxDQUFDLFVBQVUsQ0FBQyxDQUFDOztBQU1oQyxJQUFNLElBQUksR0FBRyxPQUFPLENBQUMsbUJBQW1CLENBQUMsQ0FBQztBQUMxQyxJQUFNLE9BQU8sR0FBRyxPQUFPLENBQUMsV0FBVyxDQUFDLENBQUM7QUFDckMsSUFBTSxRQUFRLEdBQUcsT0FBTyxDQUFDLFlBQVksQ0FBQyxDQUFDO0FBQ3ZDLElBQU0sU0FBUyxHQUFHLE9BQU8sQ0FBQyxhQUFhLENBQUMsQ0FBQzs7QUFLekMsU0FBUyxPQUFPLENBQUMsS0FBSyxFQUFFLE1BQU0sRUFBRSxNQUFNLEVBQUU7Ozs7QUFJcEMsUUFBSSxNQUFNLEtBQUssU0FBUyxFQUFFOztBQUV0QixjQUFNLEdBQUcsYUFBYSxDQUFDLE9BQU8sQ0FBQztLQUNsQzs7QUFFRCxRQUFJLEdBQUcsQ0FBQztBQUNSLFFBQUk7QUFDQSxXQUFHLEdBQUcsS0FBSyxDQUFDLEtBQUssQ0FBQyxLQUFLLEVBQUUsTUFBTSxDQUFDLFdBQVcsQ0FBQyxDQUFDO0tBQ2hELENBQUMsT0FBTyxDQUFDLEVBQUU7QUFDUixXQUFHLEdBQUcsV0FBVyxDQUFDLFlBQVksQ0FBQyxLQUFLLEVBQUUsTUFBTSxDQUFDLFdBQVcsQ0FBQyxDQUFDO0tBQzdEOztBQUVELFFBQUksc0JBQXNCLEdBQUcsR0FBRyxDQUFDLFdBQVcsQ0FBQyxHQUFHLENBQUMsQ0FBQzs7Ozs7QUFLbEQsUUFBSSxTQUFTLEdBQUcsSUFBSSxRQUFRLENBQUMsUUFBUSxDQUNqQyxJQUFJLEVBQ0osR0FBRyxFQUNILFFBQVEsQ0FBQyxRQUFRLENBQUMsVUFBVSxDQUFDLFdBQVc7O0FBRXhDLFVBQU0sQ0FBQyxXQUFXLENBQUMsVUFBVSxLQUFLLFFBQVEsQ0FDN0MsQ0FBQzs7QUFFRixZQUFRLENBQUMsaUJBQWlCLENBQUMsR0FBRyxFQUFFLFNBQVMsQ0FBQyxDQUFDOzs7O0FBSTNDLFdBQU8sQ0FBQywwQkFBMEIsQ0FBQyxNQUFNLENBQUMsb0JBQW9CLENBQUMsQ0FBQzs7QUFFaEUsUUFBSSxNQUFNLEdBQUcsR0FBRyxDQUFDLFFBQVEsQ0FBQyxDQUFDO0FBQzNCLFFBQUksY0FBYyxHQUFHLE9BQU8sQ0FBQyxlQUFlLENBQUMsY0FBYyxDQUFDO0FBQzVELFFBQUksTUFBTSxHQUFHLE1BQU0sQ0FBQyxnQkFBZ0IsQ0FBQyxJQUFJLEVBQUUsY0FBYyxDQUFDLENBQUM7QUFDM0QsUUFBSSxPQUFPLEdBQUcsS0FBSyxDQUFDLG9CQUFvQixDQUFDLE1BQU0sQ0FBQyxDQUFDO0FBQ2pELFFBQUksVUFBVSxHQUFHLElBQUksTUFBTSxDQUFDLE1BQU0sQ0FDOUIsSUFBSSxLQUFLLENBQUMsSUFBSSxDQUFDLE9BQU8sQ0FBQyxFQUN2QixLQUFLLENBQUMsUUFBUSxFQUNkLEtBQUssQ0FBQyxRQUFRLEVBQ2QsY0FBYyxFQUNkLE1BQU0sQ0FBQyxDQUFDOztBQUVaLFFBQUksUUFBUSxHQUFHLElBQUksS0FBSyxDQUFDLE9BQU8sQ0FBQyxJQUFJLEVBQUUsa0JBQWtCLENBQUMsQ0FBQztBQUMzRCxRQUFJLElBQUksR0FBRztBQUNQLG9CQUFZLEVBQUUsT0FBTzs7QUFFckIsY0FBTSxFQUFFO0FBQ0osa0JBQU0sRUFBRSxRQUFRO0FBQ2hCLG9CQUFRLEVBQUUsSUFBSSxLQUFLLENBQUMsT0FBTyxDQUFDLElBQUksS0FBSyxDQUFDLElBQUksQ0FBQyxRQUFRLENBQUMsRUFBRSxvQkFBb0IsQ0FBQztBQUMzRSxpQkFBSyxFQUFFLElBQUksS0FBSyxDQUFDLE9BQU8sQ0FBQyxJQUFJLEtBQUssQ0FBQyxJQUFJLENBQUMsUUFBUSxDQUFDLEVBQUUsaUJBQWlCLENBQUM7QUFDckUsa0JBQU0sRUFBRSxJQUFJLEtBQUssQ0FBQyxPQUFPLENBQUMsSUFBSSxLQUFLLENBQUMsSUFBSSxDQUFDLFFBQVEsQ0FBQyxFQUFFLGtCQUFrQixDQUFDO0FBQ3ZFLGtCQUFNLEVBQUUsSUFBSSxLQUFLLENBQUMsT0FBTyxDQUFDLElBQUksS0FBSyxDQUFDLElBQUksQ0FBQyxRQUFRLENBQUMsRUFBRSxrQkFBa0IsQ0FBQztBQUN2RSxrQkFBTSxFQUFFLElBQUksS0FBSyxDQUFDLE9BQU8sQ0FBQyxJQUFJLEtBQUssQ0FBQyxJQUFJLENBQUMsUUFBUSxDQUFDLEVBQUUsa0JBQWtCLENBQUM7QUFDdkUsbUJBQU8sRUFBRSxJQUFJLEtBQUssQ0FBQyxPQUFPLENBQUMsSUFBSSxLQUFLLENBQUMsSUFBSSxDQUFDLFFBQVEsQ0FBQyxFQUFFLG1CQUFtQixDQUFDO1NBQzVFO0FBQ0QsU0FBQyxFQUFFLElBQUksS0FBSyxDQUFDLFFBQVEsRUFBRTtBQUN2QixjQUFNLEVBQUUsTUFBTTtLQUNqQixDQUFDO0FBQ0YsUUFBSSxDQUFDLGNBQWMsQ0FBQyxHQUFHLEVBQUUsVUFBVSxFQUFFLElBQUksQ0FBQyxDQUFDOzs7OztBQUszQyxRQUFJLE1BQU0sRUFBRTtBQUNSLGVBQU87QUFDSCxtQkFBTyxFQUFFLE9BQU87QUFDaEIsZUFBRyxFQUFFLEdBQUc7QUFDUixrQkFBTSxFQUFFLE1BQU07QUFDZCxrQkFBTSxFQUFFLE1BQU07QUFDZCxhQUFDLEVBQUUsSUFBSSxDQUFDLENBQUM7U0FDWixDQUFDO0tBQ0wsTUFBTTtBQUNILGVBQU8sT0FBTyxDQUFDO0tBQ2xCO0NBQ0o7O0FBRUQsT0FBTyxDQUFDLE9BQU8sR0FBRyxPQUFPLENBQUM7QUFDMUIsT0FBTyxDQUFDLGdCQUFnQixHQUFHLFFBQVEsQ0FBQyxnQkFBZ0IsQ0FBQztBQUNyRCxPQUFPLENBQUMsYUFBYSxHQUFHLE9BQU8sQ0FBQyxhQUFhLENBQUM7QUFDOUMsT0FBTyxDQUFDLG1CQUFtQixHQUFHLFFBQVEsQ0FBQyxtQkFBbUIsQ0FBQztBQUMzRCxPQUFPLENBQUMsc0JBQXNCLEdBQUcsUUFBUSxDQUFDLHNCQUFzQixDQUFDO0FBQ2pFLE9BQU8sQ0FBQyxhQUFhLEdBQUcsU0FBUyxDQUFDLGFBQWEsQ0FBQztBQUNoRCxPQUFPLENBQUMsbUJBQW1CLEdBQUcsU0FBUyxDQUFDLG1CQUFtQixDQUFDO0FBQzVELE9BQU8sQ0FBQyxtQkFBbUIsR0FBRyxRQUFRLENBQUMsbUJBQW1CLENBQUM7QUFDM0QsT0FBTyxDQUFDLHNCQUFzQixHQUFHLFFBQVEsQ0FBQyxzQkFBc0IsQ0FBQztBQUNqRSxPQUFPLENBQUMsV0FBVyxHQUFHLFdBQVcsQ0FBQyxjQUFjLENBQUM7QUFDakQsT0FBTyxDQUFDLGtCQUFrQixHQUFHLFdBQVcsQ0FBQyxrQkFBa0IsQ0FBQztBQUM1RCxPQUFPLENBQUMscUJBQXFCLEdBQUcsV0FBVyxDQUFDLHFCQUFxQixDQUFDO0FBQ2xFLE9BQU8sQ0FBQyxvQkFBb0IsR0FBRyxXQUFXLENBQUMsb0JBQW9CLENBQUM7Ozs7Ozs7NEJDNUd0QyxpQkFBaUI7O0lBQS9CLFFBQVE7Ozs7Ozs7OztBQURwQixJQUFNLElBQUksR0FBRyxPQUFPLENBQUMsaUJBQWlCLENBQUMsQ0FBQztBQVV4QyxTQUFTLFFBQVEsQ0FBQyxJQUFJLEVBQUUsRUFBRSxFQUFFLFFBQVEsRUFBRTtRQUMzQixNQUFNLEdBQTJCLEVBQUU7UUFBM0IsT0FBTyxHQUFrQixFQUFFO1FBQWxCLFlBQVksR0FBSSxFQUFFOztBQUMxQyxZQUFRLFFBQVE7QUFDWixhQUFLLHFCQUFxQixDQUFDO0FBQzNCLGFBQUssb0JBQW9CLENBQUM7QUFDMUIsYUFBSyx5QkFBeUI7QUFDMUIsbUJBQU8sQ0FBQyxJQUFJLEVBQUUsU0FBUyxDQUFDLENBQUM7QUFBQSxBQUM3QixhQUFLLGNBQWM7O0FBRWYsbUJBQU8sQ0FBQyxNQUFNLEVBQUUsSUFBSSxFQUFFLE9BQU8sQ0FBQyxDQUFDO0FBQUEsQUFDbkMsYUFBSyxhQUFhOztBQUVkLG1CQUFPLENBQUMsTUFBTSxFQUFFLFlBQVksQ0FBQyxDQUFDO0FBQUEsQUFDbEMsYUFBSyxnQkFBZ0I7QUFDakIsZ0JBQUksRUFBRSxDQUFDLEtBQUssRUFBRTs7QUFFVix1QkFBTyxDQUFDLE1BQU0sRUFBRSxZQUFZLENBQUMsQ0FBQzthQUNqQyxNQUNJOztBQUVELHVCQUFPLENBQUMsTUFBTSxFQUFFLE9BQU8sRUFBRSxZQUFZLENBQUMsQ0FBQzthQUMxQztBQUFBLEFBQ0w7QUFDSSxtQkFBTyxDQUFDLE1BQU0sRUFBRSxPQUFPLEVBQUUsWUFBWSxDQUFDLENBQUM7QUFBQSxLQUM5QztDQUNKOzs7Ozs7OztBQVFELFNBQVMsbUJBQW1CLENBQUMsR0FBRyxFQUFFLEdBQUcsRUFBRTtBQUNuQyxnQkFBWSxDQUFDOzs7O0FBSWIsUUFBTSxNQUFNLEdBQUcsUUFBUSxDQUFDLFVBQVUsQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDO0FBQ3JDLG9CQUFZLEVBQUUsc0JBQUMsSUFBSSxFQUFFLEVBQUUsRUFBRSxDQUFDLEVBQUs7QUFDM0IsYUFBQyxDQUFDLElBQUksQ0FBQyxLQUFLLEVBQUUsRUFBRSxDQUFDLENBQUM7O0FBRWxCLGNBQUUsQ0FBQyxLQUFLLEdBQUcsSUFBSSxDQUFDO0FBQ2hCLGdCQUFJLElBQUksQ0FBQyxPQUFPLEVBQUUsQ0FBQyxDQUFDLElBQUksQ0FBQyxPQUFPLEVBQUUsRUFBRSxDQUFDLENBQUM7QUFDdEMsZ0JBQUksSUFBSSxDQUFDLFNBQVMsRUFBRSxDQUFDLENBQUMsSUFBSSxDQUFDLFNBQVMsRUFBRSxFQUFFLENBQUMsQ0FBQztTQUM3QztBQUNELG1CQUFXLEVBQUUscUJBQUMsSUFBSSxFQUFFLEVBQUUsRUFBRSxDQUFDLEVBQUs7QUFDMUIsYUFBQyxDQUFDLElBQUksQ0FBQyxJQUFJLEVBQUUsRUFBRSxDQUFDLENBQUM7U0FDcEI7S0FDSixFQUFFLElBQUksQ0FBQyxJQUFJLENBQUM7O0FBRWIsY0FBQyxJQUFJLEVBQUUsRUFBRSxFQUFFLFFBQVEsRUFBSztBQUNwQixZQUFJLElBQUksQ0FBQyxLQUFLLEdBQUcsR0FBRyxJQUFJLElBQUksQ0FBQyxHQUFHLEdBQUcsR0FBRyxFQUFFO0FBQ3BDLG1CQUFPLEtBQUssQ0FBQztTQUNoQjs7Ozs7QUFLRCxZQUFJLEFBQUMsQ0FBQyxRQUFRLEtBQUsscUJBQXFCLElBQUksUUFBUSxLQUFLLG9CQUFvQixDQUFBLEtBQ3JFLElBQUksQ0FBQyxLQUFLLElBQUksR0FBRyxJQUFJLEdBQUcsSUFBSSxJQUFJLENBQUMsS0FBSyxHQUFHLENBQUMsQ0FBQSxBQUFDLElBRTlDLFFBQVEsS0FBSyxpQkFBaUIsS0FDM0IsSUFBSSxDQUFDLEtBQUssSUFBSSxHQUFHLElBQUksR0FBRyxJQUFJLElBQUksQ0FBQyxLQUFLLEdBQUcsQ0FBQyxDQUFBLEFBQUMsQUFBQyxJQUUvQyxRQUFRLEtBQUssZ0JBQWdCLEtBQzFCLElBQUksQ0FBQyxLQUFLLElBQUksR0FBRyxJQUFJLEdBQUcsSUFBSSxJQUFJLENBQUMsS0FBSyxHQUFHLENBQUMsQ0FBQSxBQUFDLEFBQUMsRUFBRTs7QUFFbEQsY0FBRSxDQUFDLElBQUksR0FBRyxJQUFJLENBQUMsSUFBSSxDQUFDO0FBQ3BCLGtCQUFNLEVBQUUsQ0FBQztTQUNaO0FBQ0QsZUFBTyxJQUFJLENBQUM7S0FDZjs7QUFFRCxhQUFTOztBQUVULFlBQVEsQ0FDWCxDQUFDOztBQUVGLFFBQUk7QUFDQSxZQUFJLENBQUMsU0FBUyxDQUFDLEdBQUcsRUFBRSxFQUFFLEVBQUUsTUFBTSxDQUFDLENBQUM7S0FDbkMsQ0FBQyxPQUFPLENBQUMsRUFBRTtBQUNSLFlBQUksQ0FBQyxJQUFJLENBQUMsWUFBWSxLQUFLLEVBQUU7O0FBRXpCLG1CQUFPLENBQUMsQ0FBQztTQUNaLE1BQU07O0FBRUgsa0JBQU0sQ0FBQyxDQUFDO1NBQ1g7S0FDSjs7QUFFRCxXQUFPLElBQUksQ0FBQztDQUNmOzs7Ozs7OztBQVFELFNBQVMsZ0JBQWdCLENBQUMsUUFBUSxFQUFFO0FBQ2hDLGdCQUFZLENBQUM7QUFDYixRQUFNLEtBQUssR0FBRyxFQUFFLENBQUM7UUFDVixNQUFNLEdBQWEsUUFBUTtRQUFuQixPQUFPLEdBQUksUUFBUTs7QUFFbEMsUUFBTSxNQUFNLEdBQUcsUUFBUSxDQUFDLFVBQVUsQ0FDOUIsSUFBSSxDQUFDLElBQUksQ0FBQztBQUNOLG9CQUFZLEVBQUUsc0JBQUMsSUFBSSxFQUFFLEVBQUUsRUFBRSxDQUFDLEVBQUs7QUFDM0IsYUFBQyxDQUFDLElBQUksQ0FBQyxLQUFLLEVBQUUsRUFBRSxDQUFDLENBQUM7O0FBRWxCLGNBQUUsQ0FBQyxLQUFLLEdBQUcsSUFBSSxDQUFDOztBQUVoQixnQkFBSSxJQUFJLENBQUMsT0FBTyxFQUFFLENBQUMsQ0FBQyxJQUFJLENBQUMsT0FBTyxFQUFFLEVBQUUsQ0FBQyxDQUFDO0FBQ3RDLGdCQUFJLElBQUksQ0FBQyxTQUFTLEVBQUUsQ0FBQyxDQUFDLElBQUksQ0FBQyxTQUFTLEVBQUUsRUFBRSxDQUFDLENBQUM7U0FDN0M7QUFDRCx1QkFBZSxFQUFFLHlCQUFDLElBQUksRUFBSztBQUN2QixnQkFBSSxRQUFRLENBQUMsSUFBSSxLQUFLLGdCQUFnQixJQUFJLE9BQU8sRUFBRSxPQUFPO0FBQzFELGlCQUFLLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQyxDQUFDO1NBQ3BCO0FBQ0QsZ0JBQVEsRUFBRSxvQkFBTTs7U0FFZjtBQUNELHNCQUFjLEVBQUUsd0JBQUMsSUFBSSxFQUFFLElBQUssRUFBSztnQkFBVCxDQUFDLEdBQUYsSUFBSztnQkFBRixDQUFDLEdBQUosSUFBSzs7QUFDeEIsZ0JBQUksQUFBQyxRQUFRLENBQUMsSUFBSSxLQUFLLGdCQUFnQixJQUFJLE9BQU8sS0FBSyxDQUFDLElBQ2pELENBQUMsS0FBSyxTQUFTLEVBQUU7QUFDcEIscUJBQUssQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDLENBQUM7YUFDcEI7U0FDSjtBQUNELG1CQUFXLEVBQUUscUJBQUMsSUFBSSxFQUFFLEVBQUUsRUFBRSxDQUFDLEVBQUs7QUFDMUIsYUFBQyxDQUFDLElBQUksQ0FBQyxJQUFJLEVBQUUsRUFBRSxDQUFDLENBQUM7U0FDcEI7S0FDSixFQUFFLElBQUksQ0FBQyxJQUFJLENBQUMsRUFDYixTQUFTLEVBQ1QsU0FBUyxFQUNULFFBQVEsQ0FBQyxDQUFDOztBQUVkLFFBQUksUUFBUSxDQUFDLElBQUksS0FBSyxnQkFBZ0IsSUFBSSxPQUFPLEVBQUU7QUFDL0MsWUFBSSxDQUFDLFNBQVMsQ0FBQyxPQUFPLENBQUMsS0FBSyxFQUFFLENBQUMsU0FBUyxFQUFFLE9BQU8sQ0FBQyxFQUFFLE1BQU0sQ0FBQyxDQUFDO0tBQy9ELE1BQU07QUFDSCxZQUFJLENBQUMsU0FBUyxDQUFDLE1BQU0sQ0FBQyxJQUFJLEVBQUUsQ0FBQyxNQUFNLEVBQUUsU0FBUyxDQUFDLEVBQUUsTUFBTSxDQUFDLENBQUM7S0FDNUQ7O0FBRUQsV0FBTyxLQUFLLENBQUM7Q0FDaEI7Ozs7Ozs7Ozs7O0FBV0QsU0FBUyxzQkFBc0IsQ0FBQyxHQUFHLEVBQUUsR0FBRyxFQUFFLGNBQWMsRUFBRTtBQUN0RCxnQkFBWSxDQUFDOztBQUViLFFBQU0sUUFBUSxHQUFHLG1CQUFtQixDQUFDLEdBQUcsRUFBRSxHQUFHLENBQUMsQ0FBQztBQUMvQyxRQUFJLENBQUMsUUFBUSxFQUFFO0FBQ1gsZUFBTyxJQUFJLENBQUM7S0FDZjs7QUFFRCxRQUFNLE1BQU0sR0FBRyxnQkFBZ0IsQ0FBQyxRQUFRLENBQUMsQ0FBQyxHQUFHLENBQ3JDLFVBQUEsSUFBSSxFQUFJO0FBQ0osZUFBTyxFQUFDLEtBQUssRUFBRSxJQUFJLENBQUMsS0FBSyxFQUFFLEdBQUcsRUFBRSxJQUFJLENBQUMsR0FBRyxFQUFDLENBQUM7S0FDN0MsQ0FBQyxDQUFDO1FBQ0osTUFBTSxHQUFhLFFBQVE7UUFBbkIsT0FBTyxHQUFJLFFBQVE7Ozs7QUFHbEMsUUFBSSxRQUFRLENBQUMsSUFBSSxLQUFLLGdCQUFnQixJQUFJLE1BQU0sQ0FBQyxNQUFNLEtBQUssQ0FBQyxFQUFFO0FBQzNELGNBQU0sQ0FBQyxJQUFJLENBQUMsRUFBQyxLQUFLLEVBQUUsTUFBTSxDQUFDLEdBQUcsR0FBRyxDQUFDLEVBQUUsR0FBRyxFQUFFLE1BQU0sQ0FBQyxHQUFHLEVBQUMsQ0FBQyxDQUFDO0tBQ3pEOzs7QUFHRCxRQUFJLFFBQVEsQ0FBQyxJQUFJLEtBQUssZ0JBQWdCLElBQUksT0FBTyxFQUFFO0FBQy9DLGNBQU0sQ0FBQyxJQUFJLENBQUMsRUFBQyxLQUFLLEVBQUUsT0FBTyxDQUFDLE9BQU8sQ0FBQyxLQUFLLEVBQUUsR0FBRyxFQUFFLE9BQU8sQ0FBQyxPQUFPLENBQUMsS0FBSyxHQUFHLENBQUMsRUFBQyxDQUFDLENBQUM7S0FDL0UsTUFBTSxJQUFJLGNBQWMsRUFBRTtBQUN2QixZQUFJLE1BQU0sQ0FBQyxJQUFJLEtBQUsseUJBQXlCLEVBQUU7O0FBRTNDLGtCQUFNLENBQUMsSUFBSSxDQUFDLEVBQUMsS0FBSyxFQUFFLE1BQU0sQ0FBQyxLQUFLLEVBQUUsR0FBRyxFQUFFLE1BQU0sQ0FBQyxLQUFLLEdBQUcsQ0FBQyxFQUFDLENBQUMsQ0FBQztTQUM3RCxNQUFNOztTQUVOO0tBQ0o7QUFDRCxXQUFPLE1BQU0sQ0FBQztDQUNqQjs7QUFFRCxPQUFPLENBQUMsbUJBQW1CLEdBQUcsbUJBQW1CLENBQUM7QUFDbEQsT0FBTyxDQUFDLHNCQUFzQixHQUFHLHNCQUFzQixDQUFDOzs7Ozs7OzRCQ3JNOUIsaUJBQWlCOztJQUEvQixRQUFROzs7Ozs7OztBQURwQixJQUFNLElBQUksR0FBRyxPQUFPLENBQUMsaUJBQWlCLENBQUMsQ0FBQztBQVN4QyxTQUFTLGFBQWEsQ0FBQyxHQUFHLEVBQUUsR0FBRyxFQUFFO0FBQzdCLGdCQUFZLENBQUM7Ozs7QUFJYixRQUFNLE1BQU0sR0FBRyxRQUFRLENBQUMsVUFBVSxDQUFDLElBQUksQ0FBQyxJQUFJOztBQUV4QyxjQUFDLElBQUksRUFBRSxFQUFFLEVBQUs7QUFDVixZQUFJLElBQUksQ0FBQyxLQUFLLEdBQUcsR0FBRyxJQUFJLElBQUksQ0FBQyxHQUFHLEdBQUcsR0FBRyxFQUFFO0FBQ3BDLG1CQUFPLEtBQUssQ0FBQztTQUNoQjs7QUFFRCxZQUFJLElBQUksQ0FBQyxJQUFJLEtBQUssZ0JBQWdCLEVBQUU7QUFDaEMsa0JBQU0sRUFBRSxDQUFDO1NBQ1o7QUFDRCxlQUFPLElBQUksQ0FBQztLQUNmOztBQUVELGFBQVM7O0FBRVQsY0FBQyxJQUFJLEVBQUUsRUFBRSxFQUFLO0FBQ1YsWUFBSSxJQUFJLENBQUMsSUFBSSxLQUFLLHFCQUFxQixJQUNoQyxJQUFJLENBQUMsSUFBSSxLQUFLLG9CQUFvQixFQUFFO0FBQ3ZDLG1CQUFPLElBQUksQ0FBQztTQUNmLE1BQU07QUFDSCxtQkFBTyxFQUFFLENBQUM7U0FDYjtLQUNKLENBQUMsQ0FBQzs7QUFFUCxRQUFJO0FBQ0EsWUFBSSxDQUFDLFNBQVMsQ0FBQyxHQUFHLEVBQUUsU0FBUyxFQUFFLE1BQU0sQ0FBQyxDQUFDO0tBQzFDLENBQUMsT0FBTyxDQUFDLEVBQUU7QUFDUixZQUFJLENBQUMsSUFBSSxDQUFDLENBQUMsSUFBSSxLQUNWLENBQUMsQ0FBQyxJQUFJLEtBQUssb0JBQW9CLElBQzdCLENBQUMsQ0FBQyxJQUFJLEtBQUsscUJBQXFCLENBQUEsQUFBQyxFQUFFO0FBQ3RDLG1CQUFPLENBQUMsQ0FBQztTQUNaLE1BQU07QUFDSCxrQkFBTSxDQUFDLENBQUM7U0FDWDtLQUNKOztBQUVELFdBQU8sSUFBSSxDQUFDO0NBQ2Y7Ozs7Ozs7O0FBUUQsU0FBUyxZQUFZLENBQUMsS0FBSyxFQUFFO0FBQ3pCLGdCQUFZLENBQUM7QUFDYixRQUFNLElBQUksR0FBRyxFQUFFLENBQUM7QUFDaEIsUUFBSSxLQUFLLENBQUMsSUFBSSxLQUFLLG9CQUFvQixJQUNoQyxLQUFLLENBQUMsSUFBSSxLQUFLLHFCQUFxQixFQUFFO0FBQ3pDLGNBQU0sS0FBSyxDQUFDLGlDQUFpQyxDQUFDLENBQUM7S0FDbEQ7O0FBRUQsUUFBTSxNQUFNLEdBQUcsSUFBSSxDQUFDLElBQUksQ0FBQztBQUNyQixzQkFBYyxFQUFFLHdCQUFDLElBQUksRUFBSztBQUN0QixtQkFBTyxJQUFJLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQyxDQUFDO1NBQzFCO0FBQ0QsMkJBQW1CLEVBQUUsK0JBQU07O1NBRTFCO0FBQ0QsMEJBQWtCLEVBQUUsOEJBQU07O1NBRXpCO0tBQ0osRUFBRSxJQUFJLENBQUMsSUFBSSxDQUFDLENBQUM7O0FBRWQsUUFBSSxDQUFDLFNBQVMsQ0FBQyxLQUFLLENBQUMsSUFBSSxFQUFFLFNBQVMsRUFBRSxNQUFNLENBQUMsQ0FBQzs7QUFFOUMsV0FBTyxJQUFJLENBQUM7Q0FDZjs7Ozs7Ozs7OztBQVVELFNBQVMsbUJBQW1CLENBQUMsR0FBRyxFQUFFLEdBQUcsRUFBRSxzQkFBc0IsRUFBRTtBQUMzRCxnQkFBWSxDQUFDOztBQUViLFFBQU0sS0FBSyxHQUFHLGFBQWEsQ0FBQyxHQUFHLEVBQUUsR0FBRyxDQUFDLENBQUM7QUFDdEMsUUFBSSxDQUFDLEtBQUssRUFBRTs7QUFFUixlQUFPLElBQUksQ0FBQztLQUNmOztBQUVELFFBQU0sSUFBSSxHQUFHLFlBQVksQ0FBQyxLQUFLLENBQUMsQ0FBQztBQUNqQyxRQUFJLHNCQUFzQixFQUFFO0FBQ3hCLFlBQUksQ0FBQyxJQUFJLENBQUMsRUFBQyxLQUFLLEVBQUUsS0FBSyxDQUFDLEtBQUssRUFBRSxHQUFHLEVBQUUsS0FBSyxDQUFDLEtBQUssR0FBRyxDQUFDLEVBQUMsQ0FBQyxDQUFDO0tBQ3pEO0FBQ0QsV0FBTyxJQUFJLENBQUM7Q0FDZjs7QUFFRCxPQUFPLENBQUMsYUFBYSxHQUFHLGFBQWEsQ0FBQztBQUN0QyxPQUFPLENBQUMsbUJBQW1CLEdBQUcsbUJBQW1CLENBQUM7Ozs7Ozs7Ozs7Ozs7Ozs7O0FDN0dsRCxJQUFNLElBQUksR0FBRyxPQUFPLENBQUMsaUJBQWlCLENBQUMsQ0FBQzs7Ozs7OztBQU94QyxTQUFTLGNBQWMsR0FBRztBQUN0QixRQUFNLE1BQU0sR0FBRyxNQUFNLENBQUMsTUFBTSxDQUFDLElBQUksQ0FBQyxDQUFDO0FBQ25DLFFBQU0sUUFBUSxHQUFHLFNBQVgsUUFBUSxHQUFTLEVBQUUsQ0FBQztBQUMxQixTQUFLLElBQUksS0FBSSxJQUFJLE1BQU0sQ0FBQyxtQkFBbUIsQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDLEVBQUU7QUFDcEQsY0FBTSxDQUFDLEtBQUksQ0FBQyxHQUFHLFFBQVEsQ0FBQztLQUMzQjtBQUNELFdBQU8sTUFBTSxDQUFDO0NBQ2pCO0FBQ00sSUFBTSxVQUFVLEdBQUcsY0FBYyxFQUFFLENBQUM7Ozs7Ozs7OztBQU9wQyxTQUFTLGtCQUFrQixDQUFDLE9BQU8sRUFBRTtBQUN4QyxRQUFNLHVCQUF1QixHQUFHLElBQUksQ0FBQyxJQUFJLENBQUMsVUFBVSxFQUFFO0FBQ2xELHlCQUFpQixFQUFFLDJCQUFDLElBQUksRUFBRSxFQUFFLEVBQUUsQ0FBQyxFQUFLO0FBQ2hDLGtCQUFNLElBQUksS0FBSyxFQUFFLENBQUM7U0FDckI7QUFDRCxxQkFBYSxFQUFFLElBQUksQ0FBQyxJQUFJLENBQUMsYUFBYTtBQUN0QyxvQkFBWSxFQUFFLElBQUksQ0FBQyxJQUFJLENBQUMsZUFBZTtBQUN2QyxtQkFBVyxFQUFFLElBQUksQ0FBQyxJQUFJLENBQUMsV0FBVztLQUNyQyxDQUFDLENBQUM7O0FBRUgsUUFBSTtBQUNBLFlBQUksQ0FBQyxTQUFTLENBQUMsT0FBTyxFQUFFLFNBQVMsRUFBRSx1QkFBdUIsQ0FBQyxDQUFDO0tBQy9ELENBQUMsT0FBTyxDQUFDLEVBQUU7QUFDUixZQUFJLENBQUMsWUFBWSxLQUFLLEVBQUU7QUFDcEIsbUJBQU8sSUFBSSxDQUFDO1NBQ2Y7S0FDSjtBQUNELFdBQU8sS0FBSyxDQUFDO0NBQ2hCOzs7Ozs7QUFNTSxJQUFNLFNBQVMsR0FBRyxJQUFJLENBQUMsSUFBSSxDQUFDO0FBQy9CLFlBQVEsRUFBRSxrQkFBQyxJQUFJLEVBQUUsRUFBRSxFQUFFLENBQUMsRUFBSztBQUN2QixZQUFJLElBQUksQ0FBQyxFQUFFLEVBQUUsQ0FBQyxDQUFDLElBQUksQ0FBQyxFQUFFLEVBQUUsRUFBRSxFQUFFLFNBQVMsQ0FBQyxDQUFDO0FBQ3ZDLFlBQU0sT0FBTyxHQUFHLElBQUksQ0FBQyxRQUFRLENBQUMsSUFBSSxJQUFJLENBQUMsSUFBSSxDQUFDLFFBQVEsQ0FBQyxDQUFDO0FBQ3RELGFBQUssSUFBSSxDQUFDLEdBQUcsQ0FBQyxFQUFFLENBQUMsR0FBRyxJQUFJLENBQUMsTUFBTSxDQUFDLE1BQU0sRUFBRSxDQUFDLEVBQUUsRUFBRTtBQUN6QyxhQUFDLENBQUMsSUFBSSxDQUFDLE1BQU0sQ0FBQyxDQUFDLENBQUMsRUFBRSxPQUFPLEVBQUUsU0FBUyxDQUFDLENBQUM7U0FDekM7QUFDRCxZQUFNLE9BQU8sR0FBRyxJQUFJLENBQUMsSUFBSSxDQUFDLFFBQVEsQ0FBQyxDQUFDO0FBQ3BDLFNBQUMsQ0FBQyxJQUFJLENBQUMsSUFBSSxFQUFFLE9BQU8sRUFBRSxJQUFJLENBQUMsVUFBVSxHQUFHLGlCQUFpQixHQUFHLFdBQVcsQ0FBQyxDQUFDO0tBQzVFO0FBQ0QsZ0JBQVksRUFBRSxzQkFBQyxJQUFJLEVBQUUsRUFBRSxFQUFFLENBQUMsRUFBSztBQUMzQixZQUFNLE9BQU8sR0FBRyxJQUFJLENBQUMsUUFBUSxDQUFDLElBQUksRUFBRSxDQUFDOztBQUVyQyxZQUFJLENBQUMsSUFBSSxDQUFDLFlBQVksQ0FBQyxJQUFJLEVBQUUsT0FBTyxFQUFFLENBQUMsQ0FBQyxDQUFDO0tBQzVDO0FBQ0Qsa0JBQWMsRUFBRSx3QkFBQyxJQUFJLEVBQUUsRUFBRSxFQUFFLENBQUMsRUFBSztBQUM3QixZQUFNLE9BQU8sR0FBRyxJQUFJLENBQUMsUUFBUSxDQUFDLElBQUksRUFBRSxDQUFDOztBQUVyQyxZQUFJLENBQUMsSUFBSSxDQUFDLGNBQWMsQ0FBQyxJQUFJLEVBQUUsT0FBTyxFQUFFLENBQUMsQ0FBQyxDQUFDO0tBQzlDO0FBQ0QsZ0JBQVksRUFBRSxzQkFBQyxJQUFJLEVBQUUsRUFBRSxFQUFFLENBQUMsRUFBSztBQUMzQixTQUFDLENBQUMsSUFBSSxDQUFDLEtBQUssRUFBRSxFQUFFLENBQUMsQ0FBQztBQUNsQixZQUFJLElBQUksQ0FBQyxPQUFPLEVBQUU7OztBQUdkLGFBQUMsQ0FBQyxJQUFJLENBQUMsT0FBTyxFQUFFLEVBQUUsQ0FBQyxDQUFDO1NBQ3ZCO0FBQ0QsWUFBSSxJQUFJLENBQUMsU0FBUyxFQUFFO0FBQ2hCLGFBQUMsQ0FBQyxJQUFJLENBQUMsU0FBUyxFQUFFLEVBQUUsQ0FBQyxDQUFDO1NBQ3pCO0tBQ0o7QUFDRCxlQUFXLEVBQUUscUJBQUMsSUFBSSxFQUFFLEVBQUUsRUFBRSxDQUFDLEVBQUs7QUFDMUIsWUFBTSxPQUFPLEdBQUcsSUFBSSxDQUFDLElBQUksQ0FBQyxRQUFRLENBQUMsQ0FBQzs7QUFFcEMsU0FBQyxDQUFDLElBQUksQ0FBQyxLQUFLLEVBQUUsT0FBTyxDQUFDLENBQUM7QUFDdkIsU0FBQyxDQUFDLElBQUksQ0FBQyxJQUFJLEVBQUUsT0FBTyxDQUFDLENBQUM7S0FDekI7QUFDRCxtQkFBZSxFQUFFLHlCQUFDLElBQUksRUFBRSxFQUFFLEVBQUUsQ0FBQyxFQUFLOzs7QUFHOUIsU0FBQyxDQUFDLElBQUksRUFBRSxFQUFFLEVBQUUsWUFBWSxDQUFDLENBQUM7S0FDN0I7Q0FDSixDQUFDLENBQUM7Ozs7Ozs7Ozs7Ozs7OztBQWFJLFNBQVMsVUFBVSxDQUFDLE1BQU0sRUFBRSxPQUFPLEVBQUUsUUFBUSxFQUFFLFFBQVEsRUFBRTtBQUM1RCxnQkFBWSxDQUFDO0FBQ2IsUUFBTSxTQUFTLEdBQUcsRUFBRSxDQUFDOzs7MEJBRVosUUFBUTtBQUNiLFlBQUksQ0FBQyxNQUFNLENBQUMsY0FBYyxDQUFDLFFBQVEsQ0FBQyxFQUFFO0FBQ2xDLDhCQUFTO1NBQ1o7QUFDRCxpQkFBUyxDQUFDLFFBQVEsQ0FBQyxHQUFHLFVBQUMsSUFBSSxFQUFFLEVBQUUsRUFBRSxDQUFDLEVBQUs7QUFDbkMsZ0JBQUksR0FBRyxZQUFBLENBQUM7QUFDUixnQkFBSSxLQUFLLEdBQUcsRUFBRSxDQUFDO0FBQ2YsZ0JBQUksUUFBUSxFQUFFO0FBQ1YscUJBQUssR0FBRyxRQUFRLENBQUMsSUFBSSxFQUFFLEVBQUUsRUFBRSxRQUFRLENBQUMsQ0FBQzthQUN4QztBQUNELGdCQUFJLENBQUMsT0FBTyxJQUFJLE9BQU8sQ0FBQyxJQUFJLEVBQUUsS0FBSyxFQUFFLFFBQVEsQ0FBQyxFQUFFO0FBQzVDLG1CQUFHLEdBQUcsTUFBTSxDQUFDLFFBQVEsQ0FBQyxDQUFDLElBQUksRUFBRSxLQUFLLEVBQUUsQ0FBQyxDQUFDLENBQUM7YUFDMUMsTUFBTTtBQUNILHVCQUFPO2FBQ1Y7QUFDRCxnQkFBSSxRQUFRLEVBQUU7QUFDVixtQkFBRyxHQUFHLFFBQVEsQ0FBQyxJQUFJLEVBQUUsS0FBSyxFQUFFLFFBQVEsQ0FBQyxDQUFDO2FBQ3pDO0FBQ0QsbUJBQU8sR0FBRyxDQUFDO1NBQ2QsQ0FBQTs7O0FBbkJMLFNBQUssSUFBSSxRQUFRLElBQUksTUFBTSxFQUFFO3lCQUFwQixRQUFROztpQ0FFVCxTQUFTO0tBa0JoQjtBQUNELFdBQU8sU0FBUyxDQUFDO0NBQ3BCOzs7Ozs7O0lBTVksS0FBSyxHQUNILFNBREYsS0FBSyxDQUNGLElBQUksRUFBRTswQkFEVCxLQUFLOztBQUVWLFFBQUksQ0FBQyxJQUFJLEdBQUcsSUFBSSxDQUFDO0NBQ3BCOzs7O0FBR0UsU0FBUyxhQUFhLENBQUMsSUFBSSxFQUFFO0FBQ2hDLFFBQUksSUFBSSxDQUFDLElBQUksS0FBSyxZQUFZLEVBQUU7QUFDNUIsY0FBTSxJQUFJLEtBQUssQ0FBQyw4QkFBOEIsQ0FBQyxDQUFDO0tBQ25EO0FBQ0QsV0FBTyxJQUFJLENBQUMsSUFBSSxLQUFLLEdBQUcsSUFBSSxJQUFJLENBQUMsS0FBSyxJQUFJLElBQUksQ0FBQyxHQUFHLENBQUM7Q0FDdEQ7O0FBRU0sU0FBUyxnQkFBZ0IsQ0FBQyxHQUFHLEVBQUUsR0FBRyxFQUFFO0FBQ3ZDLGdCQUFZLENBQUM7QUFDYixXQUFPLFVBQVUsQ0FBQyxHQUFHLEVBQUUsR0FBRyxFQUNsQixVQUFBLElBQUk7ZUFBSSxJQUFJLENBQUMsSUFBSSxLQUFLLFlBQVksSUFBSSxDQUFDLGFBQWEsQ0FBQyxJQUFJLENBQUM7S0FBQSxDQUNqRSxDQUFDO0NBQ0w7O0FBRU0sU0FBUyxzQkFBc0IsQ0FBQyxHQUFHLEVBQUUsR0FBRyxFQUFFO0FBQzdDLGdCQUFZLENBQUM7QUFDYixXQUFPLFVBQVUsQ0FBQyxHQUFHLEVBQUUsR0FBRyxFQUNsQixVQUFBLElBQUksRUFBSTtBQUNKLGVBQU8sQUFBQyxJQUFJLENBQUMsSUFBSSxLQUFLLFlBQVksSUFBSSxDQUFDLGFBQWEsQ0FBQyxJQUFJLENBQUMsSUFDckQsSUFBSSxDQUFDLElBQUksS0FBSyxrQkFBa0IsS0FFN0IsQUFBQyxJQUFJLENBQUMsUUFBUSxDQUFDLEtBQUssSUFBSSxHQUFHLElBQUksR0FBRyxJQUFJLElBQUksQ0FBQyxRQUFRLENBQUMsR0FBRzs7QUFFdEQsWUFBSSxDQUFDLFFBQVEsQ0FBQyxHQUFHLElBQUksR0FBRyxJQUFJLEdBQUcsSUFBSSxJQUFJLENBQUMsUUFBUSxDQUFDLEtBQUssQ0FBQyxBQUMzRCxBQUFDLENBQUM7S0FDVixDQUNSLENBQUM7Q0FDTDs7QUFFTSxTQUFTLHFCQUFxQixDQUFDLEdBQUcsRUFBRSxHQUFHLEVBQUU7QUFDNUMsZ0JBQVksQ0FBQzs7QUFFYixRQUFNLE1BQU0sR0FBRyxVQUFVLENBQUMsU0FBUyxFQUMvQixVQUFDLElBQUksRUFBRSxFQUFFLEVBQUs7QUFDVixZQUFJLElBQUksQ0FBQyxLQUFLLEdBQUcsR0FBRyxJQUFJLElBQUksQ0FBQyxHQUFHLEdBQUcsR0FBRyxFQUFFO0FBQ3BDLG1CQUFPLEtBQUssQ0FBQztTQUNoQjs7QUFFRCxZQUFJLElBQUksQ0FBQyxJQUFJLEtBQUssWUFBWSxFQUFFO0FBQzVCLGtCQUFNLElBQUksS0FBSyxDQUFDLEVBQUMsSUFBSSxFQUFFLFlBQVksRUFBRSxJQUFJLEVBQUUsSUFBSSxFQUFFLEVBQUUsRUFBRSxFQUFFLEVBQUMsQ0FBQyxDQUFDO1NBQzdEOztBQUVELFlBQUksSUFBSSxDQUFDLElBQUksS0FBSyxrQkFBa0IsS0FFNUIsQUFBQyxJQUFJLENBQUMsUUFBUSxDQUFDLEtBQUssSUFBSSxHQUFHLElBQUksR0FBRyxJQUFJLElBQUksQ0FBQyxRQUFRLENBQUMsR0FBRzs7QUFFdEQsWUFBSSxDQUFDLFFBQVEsQ0FBQyxHQUFHLElBQUksR0FBRyxJQUFJLEdBQUcsSUFBSSxJQUFJLENBQUMsUUFBUSxDQUFDLEtBQUssQ0FBQyxBQUMzRCxFQUNIOztBQUVFLGdCQUFJLENBQUMsSUFBSSxDQUFDLFFBQVEsRUFBRTtBQUNoQixzQkFBTSxJQUFJLEtBQUssQ0FBQyxFQUFDLElBQUksRUFBRSxXQUFXLEVBQUUsSUFBSSxFQUFFLElBQUksRUFBRSxFQUFFLEVBQUUsRUFBRSxFQUFDLENBQUMsQ0FBQzthQUM1RDs7QUFFRCxnQkFBSSxJQUFJLENBQUMsUUFBUSxJQUNiLE9BQU8sSUFBSSxDQUFDLFFBQVEsQ0FBQyxLQUFLLEtBQUssUUFBUSxFQUFFO0FBQ3pDLHNCQUFNLElBQUksS0FBSyxDQUFDLEVBQUMsSUFBSSxFQUFFLFlBQVksRUFBRSxJQUFJLEVBQUUsSUFBSSxFQUFFLEVBQUUsRUFBRSxFQUFFLEVBQUMsQ0FBQyxDQUFDO2FBQzdEO1NBQ0o7QUFDRCxlQUFPLElBQUksQ0FBQztLQUNmLEVBQ0QsVUFBQyxJQUFJLEVBQUUsRUFBRSxFQUFLOztBQUVWLGNBQU0sSUFBSSxLQUFLLENBQUMsRUFBQyxJQUFJLEVBQUUsWUFBWSxFQUFFLElBQUksRUFBRSxJQUFJLEVBQUUsRUFBRSxFQUFFLEVBQUUsRUFBQyxDQUFDLENBQUM7S0FDN0QsQ0FBQyxDQUFDOztBQUVQLFFBQUk7QUFDQSxZQUFJLENBQUMsU0FBUyxDQUFDLEdBQUcsRUFBRSxHQUFHLENBQUMsUUFBUSxDQUFDLEVBQUUsTUFBTSxDQUFDLENBQUM7S0FDOUMsQ0FBQyxPQUFPLENBQUMsRUFBRTtBQUNSLFlBQUksQ0FBQyxZQUFZLEtBQUssRUFBRTtBQUNwQixtQkFBTyxDQUFDLENBQUMsSUFBSSxDQUFDO1NBQ2pCLE1BQU07QUFDSCxrQkFBTSxDQUFDLENBQUM7U0FDWDtLQUNKO0NBQ0o7Ozs7Ozs7Ozs7O0FBWUQsU0FBUyxVQUFVLENBQUMsR0FBRyxFQUFFLEdBQUcsRUFBRSxRQUFRLEVBQUU7QUFDcEMsZ0JBQVksQ0FBQzs7QUFFYixRQUFNLE1BQU0sR0FBRyxVQUFVLENBQUMsU0FBUyxFQUMvQixVQUFDLElBQUksRUFBRSxFQUFFLEVBQUs7QUFDVixZQUFJLElBQUksQ0FBQyxLQUFLLEdBQUcsR0FBRyxJQUFJLElBQUksQ0FBQyxHQUFHLEdBQUcsR0FBRyxFQUFFO0FBQ3BDLG1CQUFPLEtBQUssQ0FBQztTQUNoQjtBQUNELFlBQUksUUFBUSxDQUFDLElBQUksQ0FBQyxFQUFFO0FBQ2hCLGtCQUFNLElBQUksS0FBSyxDQUFDLEVBQUMsSUFBSSxFQUFFLElBQUksRUFBRSxFQUFFLEVBQUUsRUFBRSxFQUFDLENBQUMsQ0FBQztTQUN6QztBQUNELGVBQU8sSUFBSSxDQUFDO0tBQ2YsQ0FBQyxDQUFDOztBQUVQLFFBQUk7QUFDQSxZQUFJLENBQUMsU0FBUyxDQUFDLEdBQUcsRUFBRSxHQUFHLENBQUMsUUFBUSxDQUFDLEVBQUUsTUFBTSxDQUFDLENBQUM7S0FDOUMsQ0FBQyxPQUFPLENBQUMsRUFBRTtBQUNSLFlBQUksQ0FBQyxZQUFZLEtBQUssRUFBRTtBQUNwQixtQkFBTyxDQUFDLENBQUMsSUFBSSxDQUFDO1NBQ2pCLE1BQU07QUFDSCxrQkFBTSxDQUFDLENBQUM7U0FDWDtLQUNKOztBQUVELFdBQU8sSUFBSSxDQUFDO0NBQ2Y7Ozs7Ozs7Ozs7O0FBVU0sU0FBUyxtQkFBbUIsQ0FBQyxHQUFHLEVBQUUsS0FBSyxFQUFFLEdBQUcsRUFBRTtBQUNqRCxnQkFBWSxDQUFDOztBQUViLFFBQU0sTUFBTSxHQUFHLFVBQVUsQ0FBQyxTQUFTLEVBQy9CLFVBQUEsSUFBSTtlQUFJLElBQUksQ0FBQyxLQUFLLElBQUksS0FBSyxJQUFJLEdBQUcsSUFBSSxJQUFJLENBQUMsR0FBRztLQUFBLEVBQzlDLFVBQUEsSUFBSSxFQUFJO0FBQUUsY0FBTSxJQUFJLEtBQUssQ0FBQyxJQUFJLENBQUMsQ0FBQztLQUFFLENBQ3JDLENBQUM7O0FBRUYsUUFBSTtBQUNBLFlBQUksQ0FBQyxTQUFTLENBQUMsR0FBRyxFQUFFLFNBQVMsRUFBRSxNQUFNLENBQUMsQ0FBQztLQUMxQyxDQUFDLE9BQU8sQ0FBQyxFQUFFO0FBQ1IsWUFBSSxDQUFDLFlBQVksS0FBSyxFQUFFO0FBQ3BCLG1CQUFPLENBQUMsQ0FBQyxJQUFJLENBQUM7U0FDakIsTUFBTTtBQUNILGtCQUFNLENBQUMsQ0FBQztTQUNYO0tBQ0o7O0FBRUQsV0FBTyxJQUFJLENBQUM7Q0FDZjs7QUFFTSxTQUFTLG1CQUFtQixDQUFDLElBQUksRUFBRSxLQUFLLEVBQUUsT0FBTyxFQUFFO0FBQ3RELGFBQVMsQ0FBQyxDQUFDLElBQUksRUFBRSxFQUFFLEVBQUUsUUFBUSxFQUFFO0FBQzNCLGVBQU8sT0FBTyxDQUFDLFFBQVEsSUFBSSxJQUFJLENBQUMsSUFBSSxDQUFDLENBQUMsSUFBSSxFQUFFLEVBQUUsRUFBRSxDQUFDLENBQUMsQ0FBQztLQUN0RDtBQUNELFdBQU8sQ0FBQyxDQUFDLElBQUksRUFBRSxLQUFLLENBQUMsQ0FBQztDQUN6Qjs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7OztBQzFQRCxZQUFZLENBQUM7Ozs7Ozs7Ozs0QkFFVSxpQkFBaUI7O0lBQTVCLEtBQUs7OzRCQUNTLGlCQUFpQjs7SUFBL0IsUUFBUTs7QUFDcEIsSUFBTSxJQUFJLEdBQUcsT0FBTyxDQUFDLGlCQUFpQixDQUFDLENBQUM7O0lBRTNCLFFBQVE7QUFDTixhQURGLFFBQVEsQ0FDTCxLQUFLLEVBQUUsVUFBVSxFQUFFLEtBQUssRUFBRSxRQUFRLEVBQUU7OEJBRHZDLFFBQVE7O0FBRWIsWUFBSSxDQUFDLEtBQUssR0FBRyxLQUFLLENBQUM7QUFDbkIsWUFBSSxDQUFDLFVBQVUsR0FBRyxVQUFVLENBQUM7QUFDN0IsWUFBSSxDQUFDLFNBQVMsR0FBRyxLQUFLLENBQUM7QUFDdkIsWUFBSSxDQUFDLFFBQVEsR0FBRyxRQUFRLENBQUM7O0FBRXpCLFlBQUksQ0FBQyxXQUFXLEdBQUcsVUFBVSxDQUFDLFFBQVEsQ0FBQyxDQUFDO0FBQ3hDLFlBQUksQ0FBQyxhQUFhLEdBQUcsRUFBRSxDQUFDO0FBQ3hCLFlBQUksQ0FBQyxhQUFhLEdBQUcsRUFBRSxDQUFDOztBQUV4QixZQUFJLENBQUMsYUFBYSxHQUFHLEVBQUUsQ0FBQzs7QUFFeEIsWUFBSSxDQUFDLFNBQVMsR0FBRyxJQUFJLEdBQUcsRUFBRSxDQUFDO0FBQzNCLFlBQUksQ0FBQyxjQUFjLEdBQUcsRUFBRSxDQUFDO0tBQzVCOztBQWZRLFlBQVEsV0FpQmpCLFFBQVEsR0FBQSxvQkFBRztBQUNQLGVBQU8sSUFBSSxDQUFDLFNBQVMsS0FBSyxRQUFRLENBQUMsVUFBVSxDQUFDLFdBQVcsQ0FBQztLQUM3RDs7QUFuQlEsWUFBUSxXQXFCakIsa0JBQWtCLEdBQUEsOEJBQUc7QUFDakIsZUFBTyxJQUFJLENBQUMsU0FBUyxLQUFLLFFBQVEsQ0FBQyxVQUFVLENBQUMsZ0JBQWdCLENBQUM7S0FDbEU7O0FBdkJRLFlBQVEsV0F5QmpCLG9CQUFvQixHQUFBLGdDQUFHO0FBQ25CLGVBQU8sSUFBSSxDQUFDLFNBQVMsS0FBSyxRQUFRLENBQUMsVUFBVSxDQUFDLGtCQUFrQixDQUFDO0tBQ3BFOztBQTNCUSxZQUFRLFdBNkJqQixZQUFZLEdBQUEsd0JBQUc7QUFDWCxlQUFPLElBQUksQ0FBQyxTQUFTLEtBQUssUUFBUSxDQUFDLFVBQVUsQ0FBQyxVQUFVLENBQUM7S0FDNUQ7O0FBL0JRLFlBQVEsV0FpQ2pCLGFBQWEsR0FBQSx5QkFBRztBQUNaLGVBQU8sSUFBSSxDQUFDLFNBQVMsS0FBSyxRQUFRLENBQUMsVUFBVSxDQUFDLFdBQVcsQ0FBQztLQUM3RDs7QUFuQ1EsWUFBUSxXQXFDakIsZ0JBQWdCLEdBQUEsNEJBQUc7QUFDZixlQUFPLElBQUksQ0FBQyxTQUFTLEtBQUssUUFBUSxDQUFDLFVBQVUsQ0FBQyxjQUFjLENBQUM7S0FDaEU7O0FBdkNRLFlBQVEsV0F5Q2pCLGdCQUFnQixHQUFBLDRCQUFHO0FBQ2YsZUFBTyxJQUFJLENBQUMsYUFBYSxDQUFDO0tBQzdCOztBQTNDUSxZQUFRLFdBNkNqQixnQkFBZ0IsR0FBQSw0QkFBRztBQUNmLGVBQU8sSUFBSSxDQUFDLGFBQWEsQ0FBQztLQUM3Qjs7QUEvQ1EsWUFBUSxXQWlEakIsV0FBVyxHQUFBLHVCQUFHO0FBQ1YsZUFBTyxJQUFJLENBQUMsZ0JBQWdCLEVBQUUsQ0FBQyxNQUFNLENBQUMsSUFBSSxDQUFDLGdCQUFnQixFQUFFLENBQUMsQ0FBQztLQUNsRTs7QUFuRFEsWUFBUSxXQXFEakIsV0FBVyxHQUFBLHFCQUFDLE9BQU8sRUFBRTtBQUNqQixlQUFPLElBQUksQ0FBQyxhQUFhLElBQUksSUFBSSxDQUFDLGFBQWEsQ0FBQyxPQUFPLENBQUMsT0FBTyxDQUFDLEdBQUcsQ0FBQyxDQUFDLENBQUM7S0FDekU7O0FBdkRRLFlBQVEsV0F5RGpCLFdBQVcsR0FBQSxxQkFBQyxPQUFPLEVBQUU7QUFDakIsZUFBTyxJQUFJLENBQUMsYUFBYSxDQUFDLE9BQU8sQ0FBQyxPQUFPLENBQUMsR0FBRyxDQUFDLENBQUMsQ0FBQztLQUNuRDs7QUEzRFEsWUFBUSxXQTZEakIsTUFBTSxHQUFBLGdCQUFDLE9BQU8sRUFBRTtBQUNaLGVBQU8sSUFBSSxDQUFDLFdBQVcsQ0FBQyxPQUFPLENBQUMsSUFBSSxJQUFJLENBQUMsV0FBVyxDQUFDLE9BQU8sQ0FBQyxDQUFDO0tBQ2pFOztBQS9EUSxZQUFRLFdBaUVqQixtQkFBbUIsR0FBQSw2QkFBQyxPQUFPLEVBQUUsS0FBSyxFQUFFO0FBQ2hDLFlBQUksU0FBUyxHQUFHLElBQUksQ0FBQztBQUNyQixnQkFBTyxLQUFLO0FBQ1IsaUJBQUssUUFBUSxDQUFDLGdCQUFnQixDQUFDLGNBQWM7O0FBRXpDLHVCQUFPLENBQUMsU0FBUyxDQUFDLGtCQUFrQixFQUFFLElBQy9CLENBQUMsU0FBUyxDQUFDLG9CQUFvQixFQUFFLElBQ2pDLENBQUMsU0FBUyxDQUFDLGdCQUFnQixFQUFFO29CQUM3QixDQUFDLFNBQVMsQ0FBQyxRQUFRLEVBQUUsRUFBRTtBQUMxQiw2QkFBUyxHQUFHLFNBQVMsQ0FBQyxLQUFLLENBQUM7aUJBQy9CO0FBQ0Qsc0JBQU07QUFBQSxBQUNWLGlCQUFLLFFBQVEsQ0FBQyxnQkFBZ0IsQ0FBQyxtQkFBbUI7OztBQUc5Qyx1QkFBTyxTQUFTLENBQUMsYUFBYSxFQUFFLElBQ3pCLEVBQUUsU0FBUyxDQUFDLFlBQVksRUFBRSxJQUFJLFNBQVMsQ0FBQyxXQUFXLENBQUMsT0FBTyxDQUFDLENBQUEsQUFBQyxFQUFFO0FBQ2xFLDZCQUFTLEdBQUcsU0FBUyxDQUFDLEtBQUssQ0FBQztpQkFDL0I7QUFDRCxzQkFBTTtBQUFBLEFBQ1YsaUJBQUssUUFBUSxDQUFDLGdCQUFnQixDQUFDLGNBQWMsQ0FBQztBQUM5QyxpQkFBSyxRQUFRLENBQUMsZ0JBQWdCLENBQUMsZ0JBQWdCO0FBQzNDLHNCQUFNO0FBQUEsQUFDVixpQkFBSyxRQUFRLENBQUMsZ0JBQWdCLENBQUMseUJBQXlCOztBQUVwRCxvQkFBSSxDQUFDLElBQUksQ0FBQyxRQUFRLEVBQUUsSUFBSSxJQUFJLENBQUMsUUFBUSxFQUFFO0FBQ25DLDJCQUFPLElBQUksQ0FBQztpQkFDZjtBQUNELHNCQUFNO0FBQUEsU0FDYjs7O0FBR0QsWUFBSSxDQUFDLFNBQVMsQ0FBQyxNQUFNLENBQUMsT0FBTyxDQUFDLEVBQUU7QUFDNUIscUJBQVMsQ0FBQyxhQUFhLENBQUMsSUFBSSxDQUFDLE9BQU8sQ0FBQyxDQUFDO1NBQ3pDOztBQUVELGVBQU8sU0FBUyxDQUFDO0tBQ3BCOztBQXRHUSxZQUFRLFdBd0dqQixXQUFXLEdBQUEscUJBQUMsT0FBTyxFQUFFO0FBQ2pCLFlBQUksQ0FBQyxhQUFhLENBQUMsSUFBSSxDQUFDLE9BQU8sQ0FBQyxDQUFDO0tBQ3BDOztBQTFHUSxZQUFRLFdBNEdqQixjQUFjLEdBQUEsd0JBQUMsT0FBTyxFQUFFO0FBQ3BCLFlBQUksU0FBUyxHQUFHLElBQUksQ0FBQztBQUNyQixlQUFPLFNBQVMsSUFBSSxDQUFDLFNBQVMsQ0FBQyxNQUFNLENBQUMsT0FBTyxDQUFDLEVBQUU7QUFDNUMsZ0JBQUksU0FBUyxDQUFDLFFBQVEsRUFBRSxJQUFJLENBQUMsU0FBUyxDQUFDLFFBQVEsRUFBRTtBQUM3QyxzQkFBTTthQUNUO0FBQ0QscUJBQVMsR0FBRyxTQUFTLENBQUMsS0FBSyxDQUFDO1NBQy9COzs7O0FBSUQsZUFBTyxTQUFTLENBQUM7S0FDcEI7O0FBeEhRLFlBQVEsV0EwSGpCLGtCQUFrQixHQUFBLDhCQUFHO0FBQ2pCLFlBQUksU0FBUyxHQUFHLElBQUksQ0FBQztBQUNyQixZQUFNLFFBQVEsR0FBRyxFQUFFLENBQUM7QUFDcEIsZUFBTyxTQUFTLEVBQUU7QUFDZCxxQkFBUyxDQUFDLFdBQVcsRUFBRSxDQUFDLE9BQU8sQ0FBQyxVQUFVLElBQUksRUFBRTtBQUM1QyxvQkFBSSxRQUFRLENBQUMsT0FBTyxDQUFDLElBQUksQ0FBQyxLQUFLLENBQUMsQ0FBQyxFQUFFO0FBQy9CLDRCQUFRLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQyxDQUFDO2lCQUN2QjthQUNKLENBQUMsQ0FBQztBQUNILHFCQUFTLEdBQUcsU0FBUyxDQUFDLEtBQUssQ0FBQztTQUMvQjtBQUNELGVBQU8sUUFBUSxDQUFDO0tBQ25COztBQXRJUSxZQUFRLFdBd0lqQixVQUFVLEdBQUEsb0JBQUMsT0FBTyxFQUFFO0FBQ2hCLFlBQUksSUFBSSxDQUFDLGFBQWEsQ0FBQyxPQUFPLENBQUMsT0FBTyxDQUFDLEtBQUssQ0FBQyxDQUFDLEVBQUU7QUFDNUMsZ0JBQUksQ0FBQyxhQUFhLENBQUMsSUFBSSxDQUFDLE9BQU8sQ0FBQyxDQUFDO1NBQ3BDO0tBQ0o7O0FBNUlRLFlBQVEsV0E4SWpCLGVBQWUsR0FBQSwyQkFBRztBQUNkLGVBQU8sSUFBSSxDQUFDLGFBQWEsQ0FBQztLQUM3Qjs7QUFoSlEsWUFBUSxXQWtKakIsU0FBUyxHQUFBLG1CQUFDLE9BQU8sRUFBRTtBQUNmLGVBQU8sSUFBSSxDQUFDLGFBQWEsQ0FBQyxPQUFPLENBQUMsT0FBTyxDQUFDLEdBQUcsQ0FBQyxDQUFDLENBQUM7S0FDbkQ7Ozs7QUFwSlEsWUFBUSxXQXVKakIsV0FBVyxHQUFBLHFCQUFDLEtBQUssRUFBRTtBQUNmLFlBQUksSUFBSSxDQUFDLFNBQVMsQ0FBQyxHQUFHLENBQUMsS0FBSyxDQUFDLEVBQUU7QUFDM0IsbUJBQU8sSUFBSSxDQUFDLFNBQVMsQ0FBQyxHQUFHLENBQUMsS0FBSyxDQUFDLENBQUM7U0FDcEM7O0FBRUQsWUFBTSxNQUFNLEdBQUcsSUFBSSxHQUFHLEVBQUUsQ0FBQztBQUN6QixZQUFNLFFBQVEsR0FBRyxJQUFJLENBQUMsZ0JBQWdCLEVBQUUsQ0FBQyxNQUFNLENBQUMsSUFBSSxDQUFDLGdCQUFnQixFQUFFLENBQUMsQ0FBQzs7QUFFekUsYUFBSyxJQUFJLENBQUMsR0FBRyxDQUFDLEVBQUUsQ0FBQyxHQUFHLFFBQVEsQ0FBQyxNQUFNLEVBQUUsQ0FBQyxFQUFFLEVBQUU7QUFDdEMsa0JBQU0sQ0FBQyxHQUFHLENBQUMsUUFBUSxDQUFDLENBQUMsQ0FBQyxFQUFFLElBQUksS0FBSyxDQUFDLElBQUksRUFBRSxDQUFDLENBQUM7U0FDN0M7O0FBRUQsWUFBSSxDQUFDLFNBQVMsQ0FBQyxHQUFHLENBQUMsS0FBSyxFQUFDLE1BQU0sQ0FBQyxDQUFDO0FBQ2pDLGVBQU8sTUFBTSxDQUFDO0tBQ2pCOzs7O0FBcktRLFlBQVEsV0F3S2pCLGFBQWEsR0FBQSx1QkFBQyxLQUFLLEVBQUU7QUFDakIsWUFBTSxRQUFRLEdBQUcsSUFBSSxDQUFDLFdBQVcsQ0FBQyxLQUFLLENBQUMsQ0FBQztBQUN6QyxZQUFNLE1BQU0sR0FBRyxFQUFFLENBQUM7QUFDbEIsWUFBSSxDQUFDLGdCQUFnQixFQUFFLENBQUMsT0FBTyxDQUFDLFVBQUEsSUFBSSxFQUFJO0FBQ3BDLGtCQUFNLENBQUMsSUFBSSxDQUFDLFFBQVEsQ0FBQyxHQUFHLENBQUMsSUFBSSxDQUFDLENBQUMsQ0FBQztTQUNuQyxDQUFDLENBQUM7QUFDSCxlQUFPLE1BQU0sQ0FBQztLQUNqQjs7OztBQS9LUSxZQUFRLFdBa0xqQixnQkFBZ0IsR0FBQSwwQkFBQyxLQUFLLEVBQUU7QUFDcEIsWUFBSSxDQUFDLElBQUksQ0FBQyxrQkFBa0IsRUFBRTtBQUMxQixrQkFBTSxJQUFJLEtBQUssQ0FBQyx1QkFBdUIsQ0FBQyxDQUFDO1NBQzVDO0FBQ0QsZUFBTyxJQUFJLENBQUMsV0FBVyxDQUFDLEtBQUssQ0FBQyxDQUFDLEdBQUcsQ0FBQyxXQUFXLENBQUMsQ0FBQztLQUNuRDs7OztBQXZMUSxZQUFRLFdBMExqQixnQkFBZ0IsR0FBQSwwQkFBQyxLQUFLLEVBQUUsS0FBSyxFQUFFO0FBQzNCLFlBQU0sTUFBTSxHQUFHLElBQUksQ0FBQyxXQUFXLENBQUMsS0FBSyxDQUFDLENBQUM7QUFDdkMsWUFBSSxLQUFLLEdBQUcsSUFBSSxDQUFDOztBQUVqQixZQUFJLENBQUMsY0FBYyxDQUFDLE9BQU8sQ0FBQyxVQUFVLEVBQUUsRUFBRTtBQUN0QyxnQkFBSSxFQUFFLENBQUMsS0FBSyxLQUFLLEtBQUssSUFBSSxFQUFFLENBQUMsTUFBTSxLQUFLLE1BQU0sRUFBRSxLQUFLLEdBQUcsRUFBRSxDQUFDO1NBQzlELENBQUMsQ0FBQzs7QUFFSCxZQUFJLEtBQUssRUFBRTtBQUNQLG1CQUFPLEtBQUssQ0FBQztTQUNoQixNQUFNO0FBQ0gsZ0JBQUksZ0JBQWdCLEdBQUcsSUFBSSxLQUFLLENBQUMsS0FBSyxFQUFFLE1BQU0sRUFBRSxJQUFJLENBQUMsQ0FBQztBQUN0RCxnQkFBSSxDQUFDLGNBQWMsQ0FBQyxJQUFJLENBQUMsZ0JBQWdCLENBQUMsQ0FBQztBQUMzQyxtQkFBTyxnQkFBZ0IsQ0FBQztTQUMzQjtLQUNKOzs7O0FBek1RLFlBQVEsV0E0TWpCLGtCQUFrQixHQUFBLDRCQUFDLE1BQU0sRUFBRTtBQUN2QixZQUFNLFNBQVMsR0FBRyxJQUFJLEdBQUcsRUFBRSxDQUFDO0FBQzVCLFlBQUksQ0FBQyxjQUFjLENBQUMsT0FBTyxDQUFDLFVBQUEsRUFBRSxFQUFJO0FBQzlCLGdCQUFJLEVBQUUsQ0FBQyxLQUFLLEtBQUssTUFBTSxFQUFFLFNBQVMsQ0FBQyxHQUFHLENBQUMsRUFBRSxDQUFDLENBQUM7U0FDOUMsQ0FBQyxDQUFDO0FBQ0gsZUFBTyxTQUFTLENBQUM7S0FDcEI7O1dBbE5RLFFBQVE7Ozs7O0FBcU5yQixRQUFRLENBQUMsVUFBVSxHQUFHO0FBQ2xCLGVBQVcsRUFBRSxNQUFNLENBQUMsUUFBUSxDQUFDO0FBQzdCLG9CQUFnQixFQUFFLE1BQU0sQ0FBQyxhQUFhLENBQUM7QUFDdkMsc0JBQWtCLEVBQUUsTUFBTSxDQUFDLGVBQWUsQ0FBQztBQUMzQyxrQkFBYyxFQUFFLE1BQU0sQ0FBQyxXQUFXLENBQUM7QUFDbkMsY0FBVSxFQUFFLE1BQU0sQ0FBQyxPQUFPLENBQUM7QUFDM0IsZUFBVyxFQUFFLE1BQU0sQ0FBQyxRQUFRLENBQUM7Q0FDaEMsQ0FBQzs7QUFFRixRQUFRLENBQUMsZ0JBQWdCLEdBQUc7QUFDeEIsa0JBQWMsRUFBRSxNQUFNLENBQUMsS0FBSyxDQUFDO0FBQzdCLG9CQUFnQixFQUFFLE1BQU0sQ0FBQyxPQUFPLENBQUM7QUFDakMsa0JBQWMsRUFBRSxNQUFNLENBQUMsS0FBSyxDQUFDO0FBQzdCLHVCQUFtQixFQUFFLE1BQU0sQ0FBQyxVQUFVLENBQUM7QUFDdkMsd0JBQW9CLEVBQUUsTUFBTSxDQUFDLFdBQVcsQ0FBQztBQUN6Qyw2QkFBeUIsRUFBRSxNQUFNLENBQUMsaUJBQWlCLENBQUM7Q0FDdkQsQ0FBQzs7Ozs7Ozs7QUFRRixTQUFTLFdBQVcsQ0FBQyxJQUFJLEVBQUU7QUFDdkIsV0FBTyxJQUFJLENBQUMsSUFBSSxLQUFLLHFCQUFxQixJQUN0QyxJQUFJLENBQUMsVUFBVSxDQUFDLElBQUksS0FBSyxTQUFTLElBQ2xDLElBQUksQ0FBQyxVQUFVLENBQUMsR0FBRyxDQUFDLEtBQUssQ0FBQyxDQUFDLEVBQUUsQ0FBQyxDQUFDLENBQUMsS0FBSyxZQUFZLENBQUM7Q0FDekQ7O0FBR0QsSUFBTSxzQkFBc0IsR0FBRyxJQUFJLENBQUMsSUFBSSxDQUFDO0FBQ3JDLG1CQUFlLEVBQUUseUJBQUMsSUFBSSxFQUFFLElBQWtCLEVBQUUsQ0FBQyxFQUFLO1lBQXpCLEtBQUssR0FBTixJQUFrQjtZQUFWLFNBQVMsR0FBakIsSUFBa0I7O0FBQ3RDLFlBQUksS0FBSyxLQUFLLFFBQVEsQ0FBQyxnQkFBZ0IsQ0FBQyxvQkFBb0IsRUFBRTtBQUMxRCxxQkFBUyxDQUFDLFdBQVcsQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDLENBQUM7U0FDcEMsTUFBTSxJQUFJLEtBQUssRUFBRTtBQUNkLHFCQUFTLENBQUMsbUJBQW1CLENBQUMsSUFBSSxDQUFDLElBQUksRUFBRSxLQUFLLENBQUMsQ0FBQztTQUNuRDtLQUNKO0FBQ0QsWUFBUSxFQUFFLGtCQUFDLElBQUksRUFBRSxLQUFrQixFQUFFLENBQUMsRUFBSztZQUF6QixLQUFLLEdBQU4sS0FBa0I7WUFBVixTQUFTLEdBQWpCLEtBQWtCOztBQUMvQixZQUFJLFVBQVUsR0FBRyxTQUFTO1lBQUUsVUFBVSxZQUFBLENBQUM7QUFDdkMsWUFBSSxJQUFJLENBQUMsRUFBRSxFQUFFO0FBQ1QsZ0JBQU0sUUFBUSxHQUFHLElBQUksQ0FBQyxFQUFFLENBQUMsSUFBSSxDQUFDO0FBQzlCLHNCQUFVLEdBQUcsU0FBUyxDQUFDLG1CQUFtQixDQUFDLFFBQVEsRUFDL0MsUUFBUSxDQUFDLGdCQUFnQixDQUFDLG1CQUFtQixDQUFDLENBQUM7U0FDdEQ7QUFDRCxZQUFNLGFBQWEsR0FBRyxJQUFJLENBQUMsTUFBTSxDQUFDLElBQUksQ0FBQyxVQUFDLEdBQUc7bUJBQ3ZDLFFBQVEsQ0FBQyxrQkFBa0IsQ0FBQyxHQUFHLENBQUM7U0FBQSxDQUFDLENBQUM7QUFDdEMsWUFBSSxhQUFhLEVBQUU7QUFDZixzQkFBVSxHQUFHLFVBQVUsR0FBRyxJQUFJLFFBQVEsQ0FDbEMsVUFBVSxFQUNWLElBQUksRUFDSixRQUFRLENBQUMsVUFBVSxDQUFDLGNBQWMsRUFDbEMsU0FBUyxDQUFDLFFBQVEsQ0FDckIsQ0FBQztBQUNGLGdCQUFJLENBQUMsUUFBUSxDQUFDLEdBQUcsVUFBVSxDQUFDO1NBQy9CO0FBQ0QsWUFBTSxXQUFXLEdBQUcsU0FBUyxDQUFDLFFBQVEsSUFDakMsSUFBSSxDQUFDLElBQUksQ0FBQyxJQUFJLElBQ2QsSUFBSSxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsQ0FBQyxDQUFDLElBQ2pCLFdBQVcsQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQyxDQUFDLENBQUMsQ0FBQyxBQUFDLENBQUM7QUFDckMsWUFBTSxTQUFTLEdBQUcsSUFBSSxRQUFRLENBQzFCLFVBQVUsRUFDVixJQUFJO0FBQ0osWUFBSSxDQUFDLElBQUksS0FBSyx5QkFBeUIsR0FDbkMsUUFBUSxDQUFDLFVBQVUsQ0FBQyxrQkFBa0IsR0FDcEMsUUFBUSxDQUFDLFVBQVUsQ0FBQyxnQkFBZ0IsRUFDMUMsV0FBVyxDQUNkLENBQUM7QUFDRixpQkFBUyxDQUFDLGFBQWEsR0FBRyxhQUFhLENBQUM7QUFDeEMsWUFBSSxDQUFDLElBQUksQ0FBQyxRQUFRLENBQUMsR0FBRyxTQUFTLENBQUM7OztBQUdoQyxZQUFNLGdCQUFnQixHQUFHLFVBQVUsSUFBSSxTQUFTLENBQUM7QUFDakQsYUFBSyxJQUFJLENBQUMsR0FBRyxDQUFDLEVBQUUsQ0FBQyxHQUFHLElBQUksQ0FBQyxNQUFNLENBQUMsTUFBTSxFQUFFLENBQUMsRUFBRSxFQUFFO0FBQ3pDLGFBQUMsQ0FBQyxJQUFJLENBQUMsTUFBTSxDQUFDLENBQUMsQ0FBQyxFQUNaLENBQ0ksUUFBUSxDQUFDLGdCQUFnQixDQUFDLG9CQUFvQixFQUM5QyxnQkFBZ0IsQ0FDbkIsRUFDRCxTQUFTLENBQUMsQ0FBQztTQUNsQjs7QUFFRCxZQUFJLElBQUksQ0FBQyxVQUFVLEVBQUU7QUFDakIsYUFBQyxDQUFDLElBQUksQ0FBQyxJQUFJLEVBQUUsR0FBRyxTQUFTLENBQUMsRUFBRSxZQUFZLENBQUMsQ0FBQztTQUM3QyxNQUFNO0FBQ0gsZ0JBQUksQ0FBQyxJQUFJLENBQUMsY0FBYyxDQUFDLElBQUksQ0FBQyxJQUFJLEVBQUUsR0FBRyxTQUFTLENBQUMsRUFBRSxDQUFDLENBQUMsQ0FBQztTQUN6RDtLQUNKOztBQUVELGdCQUFZLEVBQUUsc0JBQUMsSUFBSSxFQUFFLEtBQWEsRUFBRSxDQUFDLEVBQUs7WUFBbEIsU0FBUyxHQUFaLEtBQWE7O0FBQzlCLFlBQUksUUFBUSxZQUFBLENBQUM7QUFDYixZQUFJLFNBQVMsQ0FBQyxRQUFRLEVBQUU7QUFDcEIsb0JBQVEsR0FBRyxJQUFJLFFBQVEsQ0FDbkIsU0FBUyxFQUNULElBQUksRUFDSixRQUFRLENBQUMsVUFBVSxDQUFDLFdBQVcsRUFDL0IsU0FBUyxDQUFDLFFBQVEsQ0FDckIsQ0FBQztBQUNGLGdCQUFJLENBQUMsUUFBUSxDQUFDLEdBQUcsUUFBUSxDQUFDO1NBQzdCLE1BQU07QUFDSCxvQkFBUSxHQUFHLFNBQVMsQ0FBQztTQUN4QjtBQUNELFlBQUksSUFBSSxDQUFDLElBQUksRUFBRSxDQUFDLENBQUMsSUFBSSxDQUFDLElBQUksRUFBRSxHQUFHLFFBQVEsQ0FBQyxFQUFFLFNBQVMsQ0FBQyxDQUFDO0FBQ3JELFlBQUksSUFBSSxDQUFDLElBQUksRUFBRSxDQUFDLENBQUMsSUFBSSxDQUFDLElBQUksRUFBRSxHQUFHLFFBQVEsQ0FBQyxFQUFFLFlBQVksQ0FBQyxDQUFDO0FBQ3hELFlBQUksSUFBSSxDQUFDLE1BQU0sRUFBRSxDQUFDLENBQUMsSUFBSSxDQUFDLE1BQU0sRUFBRSxHQUFHLFFBQVEsQ0FBQyxFQUFFLFlBQVksQ0FBQyxDQUFDOztBQUU1RCxTQUFDLENBQUMsSUFBSSxDQUFDLElBQUksRUFBRSxHQUFHLFFBQVEsQ0FBQyxFQUFFLFNBQVMsQ0FBQyxDQUFDO0tBQ3pDOztBQUVELHVCQUFtQixFQUFFLDZCQUFDLElBQUksRUFBRSxLQUFhLEVBQUUsQ0FBQyxFQUFLO1lBQWxCLFNBQVMsR0FBWixLQUFhOztBQUNyQyxZQUFJLEtBQUssWUFBQSxDQUFDO0FBQ1YsZ0JBQU8sSUFBSSxDQUFDLElBQUk7QUFDWixpQkFBSyxLQUFLO0FBQ04scUJBQUssR0FBRyxRQUFRLENBQUMsZ0JBQWdCLENBQUMsY0FBYyxDQUFDO0FBQ2pELHNCQUFNO0FBQUEsQUFDVixpQkFBSyxLQUFLO0FBQ04scUJBQUssR0FBRyxRQUFRLENBQUMsZ0JBQWdCLENBQUMsY0FBYyxDQUFDO0FBQ2pELHNCQUFNO0FBQUEsQUFDVixpQkFBSyxPQUFPO0FBQ1IscUJBQUssR0FBRyxRQUFRLENBQUMsZ0JBQWdCLENBQUMsZ0JBQWdCLENBQUM7QUFDbkQsc0JBQU07QUFBQSxTQUNiOztBQUVELGFBQUssSUFBSSxDQUFDLEdBQUcsQ0FBQyxFQUFFLENBQUMsR0FBRyxJQUFJLENBQUMsWUFBWSxDQUFDLE1BQU0sRUFBRSxDQUFDLEVBQUUsRUFBRTtBQUMvQyxhQUFDLENBQUMsSUFBSSxDQUFDLFlBQVksQ0FBQyxDQUFDLENBQUMsRUFBRSxDQUFDLEtBQUssRUFBRSxTQUFTLENBQUMsRUFBRSxTQUFTLENBQUMsQ0FBQztTQUMxRDtLQUNKOztBQUVELGdCQUFZLEVBQUUsc0JBQUMsSUFBSSxFQUFFLEtBQWEsRUFBRSxDQUFDLEVBQUs7WUFBbEIsU0FBUyxHQUFaLEtBQWE7O0FBQzlCLFNBQUMsQ0FBQyxJQUFJLENBQUMsS0FBSyxFQUFFLEdBQUcsU0FBUyxDQUFDLEVBQUUsU0FBUyxDQUFDLENBQUM7QUFDeEMsWUFBSSxJQUFJLENBQUMsT0FBTyxFQUFFO0FBQ2QsYUFBQyxDQUFDLElBQUksQ0FBQyxPQUFPLEVBQUUsR0FBRyxTQUFTLENBQUMsRUFBRSxTQUFTLENBQUMsQ0FBQztTQUM3QztBQUNELFlBQUksSUFBSSxDQUFDLFNBQVMsRUFBRTtBQUNoQixhQUFDLENBQUMsSUFBSSxDQUFDLFNBQVMsRUFBRSxHQUFHLFNBQVMsQ0FBQyxFQUFFLFNBQVMsQ0FBQyxDQUFDO1NBQy9DO0tBQ0o7O0FBRUQsZUFBVyxFQUFFLHFCQUFDLElBQUksRUFBRSxLQUFhLEVBQUUsQ0FBQyxFQUFLO1lBQWxCLFNBQVMsR0FBWixLQUFhOztBQUM3QixZQUFNLFVBQVUsR0FBRyxJQUFJLFFBQVEsQ0FDM0IsU0FBUyxFQUNULElBQUksRUFDSixRQUFRLENBQUMsVUFBVSxDQUFDLFVBQVUsRUFDOUIsU0FBUyxDQUFDLFFBQVEsQ0FDckIsQ0FBQztBQUNGLFNBQUMsQ0FBQyxJQUFJLENBQUMsS0FBSyxFQUNSLENBQ0ksUUFBUSxDQUFDLGdCQUFnQixDQUFDLG9CQUFvQixFQUM5QyxVQUFVLENBQ2IsRUFDRCxTQUFTLENBQUMsQ0FBQztBQUNmLFlBQUksQ0FBQyxJQUFJLENBQUMsUUFBUSxDQUFDLEdBQUcsVUFBVSxDQUFDO0FBQ2pDLFlBQUksQ0FBQyxJQUFJLENBQUMsY0FBYyxDQUFDLElBQUksQ0FBQyxJQUFJLEVBQUUsR0FBRyxVQUFVLENBQUMsRUFBRSxDQUFDLENBQUMsQ0FBQztLQUMxRDs7O0FBR0Qsa0JBQWMsRUFBRSx3QkFBQyxJQUFJLEVBQUUsS0FBYSxFQUFFLENBQUMsRUFBSztZQUFsQixTQUFTLEdBQVosS0FBYTs7QUFDaEMsWUFBSSxPQUFPLFlBQUEsQ0FBQztBQUNaLFlBQUksU0FBUyxDQUFDLFFBQVEsRUFBRTtBQUNwQixtQkFBTyxHQUFHLElBQUksUUFBUSxDQUNsQixTQUFTLEVBQ1QsSUFBSSxFQUNKLFFBQVEsQ0FBQyxVQUFVLENBQUMsV0FBVyxFQUMvQixTQUFTLENBQUMsUUFBUSxDQUNyQixDQUFDO0FBQ0YsZ0JBQUksQ0FBQyxRQUFRLENBQUMsR0FBRyxPQUFPLENBQUM7U0FDNUIsTUFBTTtBQUNILG1CQUFPLEdBQUcsU0FBUyxDQUFDO1NBQ3ZCO0FBQ0QsWUFBSSxDQUFDLElBQUksQ0FBQyxjQUFjLENBQUMsSUFBSSxFQUFFLEdBQUcsT0FBTyxDQUFDLEVBQUUsQ0FBQyxDQUFDLENBQUM7S0FDbEQ7Q0FDSixDQUFDLENBQUM7OztBQUdILElBQU0sc0JBQXNCLEdBQUcsSUFBSSxDQUFDLElBQUksQ0FBQztBQUNyQyxtQkFBZSxFQUFFLHlCQUFDLElBQUksRUFBRSxTQUFTLEVBQUUsQ0FBQyxFQUFLO0FBQ3JDLFNBQUMsQ0FBQyxJQUFJLEVBQUUsU0FBUyxFQUFFLFlBQVksQ0FBQyxDQUFDO0tBQ3BDOztBQUVELGNBQVUsRUFBRSxvQkFBQyxJQUFJLEVBQUUsU0FBUyxFQUFFLENBQUMsRUFBSztBQUNoQyxZQUFJLFFBQVEsQ0FBQyxhQUFhLENBQUMsSUFBSSxDQUFDLEVBQUU7O0FBRTlCLG1CQUFPO1NBQ1Y7QUFDRCxZQUFJLEtBQUssR0FBRyxTQUFTLENBQUM7QUFDdEIsWUFBTSxPQUFPLEdBQUcsSUFBSSxDQUFDLElBQUksQ0FBQzs7QUFFMUIsZUFBTyxLQUFLLElBQUksQ0FBQyxLQUFLLENBQUMsTUFBTSxDQUFDLE9BQU8sQ0FBQyxFQUFFO0FBQ3BDLGdCQUFJLE9BQU8sS0FBSyxXQUFXLEtBQ3RCLEtBQUssQ0FBQyxrQkFBa0IsRUFBRSxJQUMxQixLQUFLLENBQUMsZ0JBQWdCLEVBQUUsQ0FBQSxBQUFDLEVBQUU7QUFDNUIsb0JBQUksS0FBSyxDQUFDLGFBQWEsRUFBRTtBQUNyQix5QkFBSyxHQUFHLEtBQUssQ0FBQyxLQUFLLENBQUM7QUFDcEIsd0JBQUksS0FBSyxDQUFDLE1BQU0sQ0FBQyxPQUFPLENBQUMsRUFBRSxNQUFNO2lCQUNwQztBQUNELHFCQUFLLENBQUMsa0JBQWtCLEdBQUcsSUFBSSxDQUFDOztBQUVoQyxxQkFBSyxDQUFDLG1CQUFtQixDQUFDLE9BQU8sRUFBRSxRQUFRLENBQUMsZ0JBQWdCLENBQUMsY0FBYyxDQUFDLENBQUM7QUFDN0Usc0JBQU07YUFDVDtBQUNELGdCQUFJLEtBQUssQ0FBQyxRQUFRLEVBQUUsRUFBRTtBQUNsQixxQkFBSyxDQUFDLG1CQUFtQixDQUFDLE9BQU8sRUFBRSxRQUFRLENBQUMsZ0JBQWdCLENBQUMseUJBQXlCLENBQUMsQ0FBQztBQUN4RixzQkFBTTthQUNUO0FBQ0QsaUJBQUssR0FBRyxLQUFLLENBQUMsS0FBSyxDQUFDO1NBQ3ZCO0FBQ0QsWUFBSSxLQUFLLENBQUMsTUFBTSxDQUFDLE9BQU8sQ0FBQyxFQUFFO0FBQ3ZCLGlCQUFLLENBQUMsVUFBVSxDQUFDLE9BQU8sQ0FBQyxDQUFDO1NBQzdCO0tBQ0o7O0FBRUQsbUJBQWUsRUFBRSx5QkFBQyxJQUFJLEVBQUUsU0FBUyxFQUFFLENBQUMsRUFBSztBQUNyQyxZQUFJLEtBQUssR0FBRyxTQUFTLENBQUM7QUFDdEIsZUFBTyxLQUFLLENBQUMsWUFBWSxFQUFFLElBQUksS0FBSyxDQUFDLGFBQWEsRUFBRSxFQUFFO0FBQ2xELGlCQUFLLEdBQUcsS0FBSyxDQUFDLEtBQUssQ0FBQztTQUN2QjtBQUNELFlBQUksQ0FBQyxLQUFLLENBQUMsUUFBUSxFQUFFLElBQUksSUFBSSxDQUFDLFFBQVEsS0FBSyxJQUFJLEVBQUU7QUFDN0MsaUJBQUssQ0FBQyxxQkFBcUIsR0FBRyxJQUFJLENBQUM7U0FDdEM7QUFDRCxZQUFJLElBQUksQ0FBQyxRQUFRLEVBQUU7QUFDZixhQUFDLENBQUMsSUFBSSxDQUFDLFFBQVEsRUFBRSxTQUFTLEVBQUUsU0FBUyxDQUFDLENBQUM7U0FDMUM7S0FDSjs7QUFFRCxZQUFRLEVBQUUsa0JBQUMsSUFBSSxFQUFFLFNBQVMsRUFBRSxDQUFDLEVBQUs7QUFDOUIsWUFBSSxJQUFJLENBQUMsRUFBRSxFQUFFLENBQUMsQ0FBQyxJQUFJLENBQUMsRUFBRSxFQUFFLFNBQVMsRUFBRSxTQUFTLENBQUMsQ0FBQztBQUM5QyxZQUFJLElBQUksQ0FBQyxRQUFRLENBQUMsRUFBRTtBQUNoQixnQkFBTSxVQUFVLEdBQUcsSUFBSSxDQUFDLFFBQVEsQ0FBQyxDQUFDO0FBQ2xDLGlCQUFLLElBQUksQ0FBQyxHQUFHLENBQUMsRUFBRSxDQUFDLEdBQUcsSUFBSSxDQUFDLE1BQU0sQ0FBQyxNQUFNLEVBQUUsQ0FBQyxFQUFFLEVBQUU7QUFDekMsaUJBQUMsQ0FBQyxJQUFJLENBQUMsTUFBTSxDQUFDLENBQUMsQ0FBQyxFQUFFLFVBQVUsRUFBRSxTQUFTLENBQUMsQ0FBQzthQUM1QztTQUNKO0FBQ0QsU0FBQyxDQUFDLElBQUksQ0FBQyxJQUFJLEVBQUUsU0FBUyxDQUFDLENBQUM7S0FDM0I7O0FBRUQsYUFBUyxFQUFFLG1CQUFDLElBQUksRUFBRSxTQUFTLEVBQUUsQ0FBQyxFQUFLO0FBQy9CLFNBQUMsQ0FBQyxJQUFJLEVBQUUsSUFBSSxDQUFDLFFBQVEsQ0FBQyxJQUFJLFNBQVMsQ0FBQyxDQUFDO0tBQ3hDOztBQUVELGtCQUFjLEVBQUUsd0JBQUMsSUFBSSxFQUFFLFNBQVMsRUFBRSxDQUFDLEVBQUs7O0FBRXBDLFlBQUksQ0FBQyxJQUFJLENBQUMsY0FBYyxDQUFDLElBQUksRUFBRSxJQUFJLENBQUMsUUFBUSxDQUFDLElBQUksU0FBUyxFQUFFLENBQUMsQ0FBQyxDQUFDO0tBQ2xFO0NBQ0osQ0FBQyxDQUFDOztBQUdJLFNBQVMsaUJBQWlCLENBQUMsR0FBRyxFQUFFLFNBQVMsRUFBRTtBQUM5QyxPQUFHLENBQUMsUUFBUSxDQUFDLEdBQUcsU0FBUyxDQUFDOztBQUUxQixhQUFTLENBQUMsUUFBUSxHQUFHLFNBQVMsQ0FBQyxRQUFRLElBQ2xDLEdBQUcsQ0FBQyxJQUFJLENBQUMsQ0FBQyxDQUFDLElBQUksV0FBVyxDQUFDLEdBQUcsQ0FBQyxJQUFJLENBQUMsQ0FBQyxDQUFDLENBQUMsQUFBQyxDQUFDOztBQUU5QyxRQUFJLENBQUMsU0FBUyxDQUFDLEdBQUcsRUFBRSxHQUFHLFNBQVMsQ0FBQyxFQUFFLHNCQUFzQixDQUFDLENBQUM7QUFDM0QsUUFBSSxDQUFDLFNBQVMsQ0FBQyxHQUFHLEVBQUUsU0FBUyxFQUFFLHNCQUFzQixDQUFDLENBQUM7QUFDdkQsV0FBTyxHQUFHLENBQUM7Q0FDZDs7OztJQUdLLEtBQUs7QUFDSSxhQURULEtBQUssQ0FDSyxLQUFLLEVBQUUsTUFBTSxFQUFFLEVBQUUsRUFBRTs4QkFEN0IsS0FBSzs7QUFFSCxZQUFJLENBQUMsS0FBSyxHQUFHLEtBQUssQ0FBQztBQUNuQixZQUFJLENBQUMsTUFBTSxHQUFHLE1BQU0sQ0FBQztBQUNyQixZQUFJLENBQUMsRUFBRSxHQUFHLEVBQUUsQ0FBQztLQUNoQjs7OztBQUxDLFNBQUssV0FRUCxTQUFTLEdBQUEsbUJBQUMsT0FBTyxFQUFFO0FBQ2YsWUFBSSxJQUFJLEdBQUcsSUFBSSxDQUFDO0FBQ2hCLGVBQU8sSUFBSSxJQUFJLElBQUksRUFBRTtBQUNqQixnQkFBSSxJQUFJLENBQUMsTUFBTSxDQUFDLEdBQUcsQ0FBQyxPQUFPLENBQUMsRUFBRTtBQUMxQix1QkFBTyxJQUFJLENBQUMsTUFBTSxDQUFDLEdBQUcsQ0FBQyxPQUFPLENBQUMsQ0FBQzthQUNuQztBQUNELGdCQUFJLEdBQUcsSUFBSSxDQUFDLEtBQUssQ0FBQztTQUNyQjs7QUFFRCxlQUFPLEtBQUssQ0FBQyxRQUFRLENBQUM7S0FDekI7Ozs7QUFsQkMsU0FBSyxXQXFCUCxnQ0FBZ0MsR0FBQSw0Q0FBRztBQUMvQixZQUFJLElBQUksR0FBRyxJQUFJLENBQUM7QUFDaEIsZUFBTyxJQUFJLENBQUMsRUFBRSxDQUFDLFlBQVksRUFBRSxJQUFJLElBQUksQ0FBQyxFQUFFLENBQUMsYUFBYSxFQUFFLEVBQUU7QUFDdEQsZ0JBQUksR0FBRyxJQUFJLENBQUMsS0FBSyxDQUFDO1NBQ3JCO0FBQ0QsZUFBTyxJQUFJLENBQUM7S0FDZjs7V0EzQkMsS0FBSzs7Ozs7Ozs7NEJDbGdCZSxpQkFBaUI7O0lBQS9CLFFBQVE7Ozs7Ozs7O0FBRHBCLElBQU0sSUFBSSxHQUFHLE9BQU8sQ0FBQyxpQkFBaUIsQ0FBQyxDQUFDO0FBU3hDLFNBQVMsYUFBYSxDQUFDLEdBQUcsRUFBRSxHQUFHLEVBQUU7QUFDN0IsZ0JBQVksQ0FBQztBQUNiLFFBQU0sS0FBSyxHQUFHLFFBQVEsQ0FBQyxnQkFBZ0IsQ0FBQyxHQUFHLEVBQUUsR0FBRyxDQUFDLENBQUM7QUFDbEQsUUFBSSxDQUFDLEtBQUssRUFBRTs7QUFFUixlQUFPLElBQUksQ0FBQztLQUNmOztBQUVELFFBQU0sSUFBSSxHQUFHLGtCQUFrQixDQUFDLEtBQUssQ0FBQyxDQUFDLEdBQUcsQ0FBQyxVQUFBLElBQUk7ZUFDMUMsRUFBQyxLQUFLLEVBQUUsSUFBSSxDQUFDLEtBQUssRUFBRSxHQUFHLEVBQUUsSUFBSSxDQUFDLEdBQUcsRUFBQztLQUFDLENBQ3ZDLENBQUM7QUFDRixRQUFJLENBQUMsT0FBTyxHQUFHLEtBQUssQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDOztBQUUvQixXQUFPLElBQUksQ0FBQztDQUNmOzs7Ozs7O0FBT0QsU0FBUyxrQkFBa0IsQ0FBQyxLQUFLLEVBQUU7QUFDL0IsZ0JBQVksQ0FBQztBQUNiLFFBQU0sT0FBTyxHQUFHLEtBQUssQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDO0FBQ2hDLFFBQU0sR0FBRyxHQUFHLEtBQUssQ0FBQyxFQUFFLENBQUMsY0FBYyxDQUFDLE9BQU8sQ0FBQyxDQUFDO0FBQzdDLFFBQUksQ0FBQyxHQUFHLEVBQUUsT0FBTyxFQUFFLENBQUM7O0FBRXBCLFFBQU0sSUFBSSxHQUFHLEVBQUUsQ0FBQzs7QUFFaEIsUUFBTSxNQUFNLEdBQUcsSUFBSSxDQUFDLElBQUksQ0FBQztBQUNyQixrQkFBVSxFQUFFLG9CQUFDLElBQUksRUFBRSxFQUFFLEVBQUs7QUFDdEIsZ0JBQUksSUFBSSxDQUFDLElBQUksS0FBSyxPQUFPLEVBQUUsT0FBTztBQUNsQyxnQkFBSSxHQUFHLEtBQUssRUFBRSxDQUFDLGNBQWMsQ0FBQyxPQUFPLENBQUMsRUFBRTtBQUNwQyxvQkFBSSxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsQ0FBQzthQUNuQjtTQUNKO0tBQ0osRUFBRSxRQUFRLENBQUMsU0FBUyxDQUFDLENBQUM7O0FBRXZCLFFBQUksQ0FBQyxTQUFTLENBQUMsR0FBRyxDQUFDLFVBQVUsRUFBRSxHQUFHLENBQUMsVUFBVSxDQUFDLFFBQVEsQ0FBQyxFQUFFLE1BQU0sQ0FBQyxDQUFDO0FBQ2pFLFdBQU8sSUFBSSxDQUFDO0NBQ2Y7O0FBRUQsT0FBTyxDQUFDLGFBQWEsR0FBRyxhQUFhLENBQUM7Ozs7QUNuRHRDO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTs7Ozs7QUMvdUdBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBOzs7OztBQzl2Q0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7Ozs7QUN2WEE7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBOztBQ3ZCQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTs7QUMxRkE7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBOzs7QUNMQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBIiwiZmlsZSI6ImdlbmVyYXRlZC5qcyIsInNvdXJjZVJvb3QiOiIiLCJzb3VyY2VzQ29udGVudCI6WyIoZnVuY3Rpb24gZSh0LG4scil7ZnVuY3Rpb24gcyhvLHUpe2lmKCFuW29dKXtpZighdFtvXSl7dmFyIGE9dHlwZW9mIHJlcXVpcmU9PVwiZnVuY3Rpb25cIiYmcmVxdWlyZTtpZighdSYmYSlyZXR1cm4gYShvLCEwKTtpZihpKXJldHVybiBpKG8sITApO3ZhciBmPW5ldyBFcnJvcihcIkNhbm5vdCBmaW5kIG1vZHVsZSAnXCIrbytcIidcIik7dGhyb3cgZi5jb2RlPVwiTU9EVUxFX05PVF9GT1VORFwiLGZ9dmFyIGw9bltvXT17ZXhwb3J0czp7fX07dFtvXVswXS5jYWxsKGwuZXhwb3J0cyxmdW5jdGlvbihlKXt2YXIgbj10W29dWzFdW2VdO3JldHVybiBzKG4/bjplKX0sbCxsLmV4cG9ydHMsZSx0LG4scil9cmV0dXJuIG5bb10uZXhwb3J0c312YXIgaT10eXBlb2YgcmVxdWlyZT09XCJmdW5jdGlvblwiJiZyZXF1aXJlO2Zvcih2YXIgbz0wO288ci5sZW5ndGg7bysrKXMocltvXSk7cmV0dXJuIHN9KSIsImV4cG9ydCBjb25zdCBvcHRpb25zID0ge1xuICAgIGFjb3JuT3B0aW9uOiB7XG4gICAgICAgIGVjbWFWZXJzaW9uOiA2LFxuICAgICAgICAvLyBzb3VyY2VUeXBlOiAnc2NyaXB0JyBvciAnbW9kdWxlJ1xuICAgICAgICAvLyAnbW9kdWxlJyBpcyB1c2VkIGZvciBFUzYgbW9kdWxlcyBhbmRcbiAgICAgICAgLy8gJ3VzZSBzdHJpY3QnIGFzc3VtZWQgZm9yIHRob3NlIG1vZHVsZXMuXG4gICAgICAgIC8vIFRoaXMgb3B0aW9uIGlzIGFsc28gdXNlZCBieSB0aGUgYW5hbHl6ZXIuXG4gICAgICAgIHNvdXJjZVR5cGU6ICdzY3JpcHQnXG4gICAgfSxcbiAgICAvLyBBdCB0aGUgc3RhcnQgb2YgcHJvZ3JhbSBhbmQgZWFjaCBmdW5jdGlvbixcbiAgICAvLyBjaGVjayAndXNlIHN0cmljdCdcbiAgICAvLyBtYXliZSB3ZSBkbyBub3QgbmVlZCB0aGlzIG9wdGlvblxuICAgIGRldGVjdFVzZVN0cmljdDogdHJ1ZSxcblxuICAgIC8vIGNvbnRleHQgaW5zZW5zaXRpdmVcbiAgICBzZW5zaXRpdml0eVBhcmFtZXRlcjoge1xuICAgICAgICBtYXhEZXB0aEs6IDAsXG4gICAgICAgIGNvbnRleHRMZW5ndGhPZkZ1bmM6IGZ1bmN0aW9uIChmbikge1xuICAgICAgICAgICAgcmV0dXJuIDA7XG4gICAgICAgIH1cbiAgICB9XG59O1xuIiwiJ3VzZSBzdHJpY3QnO1xuXG5pbXBvcnQgKiBhcyB0eXBlcyBmcm9tICcuLi9kb21haW5zL3R5cGVzJ1xuaW1wb3J0ICogYXMgbXlXYWxrZXIgZnJvbSAnLi4vdXRpbC9teVdhbGtlcidcbmltcG9ydCAqIGFzIGNzYyBmcm9tICcuLi9kb21haW5zL2NvbnRleHQnXG5jb25zdCB3YWxrID0gcmVxdWlyZSgnYWNvcm4vZGlzdC93YWxrJyk7XG5jb25zdCBzdGF0dXMgPSByZXF1aXJlKCcuLi9kb21haW5zL3N0YXR1cycpO1xuY29uc3QgY3N0ciA9IHJlcXVpcmUoJy4vY29uc3RyYWludHMnKTtcblxuLy8gcmV0dXJucyBbYWNjZXNzIHR5cGUsIHByb3AgdmFsdWVdXG5mdW5jdGlvbiBwcm9wQWNjZXNzKG5vZGUpIHtcbiAgICBjb25zdCBwcm9wID0gbm9kZS5wcm9wZXJ0eTtcbiAgICBpZiAocHJvcC50eXBlID09PSAnSWRlbnRpZmllcicgJiYgbXlXYWxrZXIuaXNEdW1teUlkTm9kZShub2RlLnByb3BlcnR5KSkge1xuICAgICAgICByZXR1cm4gWydkdW1teVByb3BlcnR5J11cbiAgICB9XG4gICAgaWYgKCFub2RlLmNvbXB1dGVkKSB7XG4gICAgICAgIHJldHVybiBbJ2RvdEFjY2VzcycsIHByb3AubmFtZV07XG4gICAgfVxuICAgIGlmIChwcm9wLnR5cGUgPT09ICdMaXRlcmFsJykge1xuICAgICAgICBpZiAodHlwZW9mIHByb3AudmFsdWUgPT09ICdzdHJpbmcnKVxuICAgICAgICAgICAgcmV0dXJuIFsnc3RyaW5nTGl0ZXJhbCcsIHByb3AudmFsdWVdO1xuICAgICAgICBpZiAodHlwZW9mIHByb3AudmFsdWUgPT09ICdudW1iZXInKVxuICAgICAgICAgICAgLy8gY29udmVydCBudW1iZXIgdG8gc3RyaW5nXG4gICAgICAgICAgICByZXR1cm4gWydudW1iZXJMaXRlcmFsJywgcHJvcC52YWx1ZSArICcnXTtcbiAgICB9XG4gICAgcmV0dXJuIFsnY29tcHV0ZWQnLCBudWxsXTtcbn1cblxuZnVuY3Rpb24gdW5vcFJlc3VsdFR5cGUob3ApIHtcbiAgICBzd2l0Y2ggKG9wKSB7XG4gICAgICAgIGNhc2UgJysnOiBjYXNlICctJzogY2FzZSAnfic6XG4gICAgICAgICAgICByZXR1cm4gdHlwZXMuUHJpbU51bWJlcjtcbiAgICAgICAgY2FzZSAnISc6XG4gICAgICAgICAgICByZXR1cm4gdHlwZXMuUHJpbUJvb2xlYW47XG4gICAgICAgIGNhc2UgJ3R5cGVvZic6XG4gICAgICAgICAgICByZXR1cm4gdHlwZXMuUHJpbVN0cmluZztcbiAgICAgICAgY2FzZSAndm9pZCc6IGNhc2UgJ2RlbGV0ZSc6XG4gICAgICAgICAgICByZXR1cm4gbnVsbDtcbiAgICB9XG59XG5cbmZ1bmN0aW9uIGJpbm9wSXNCb29sZWFuKG9wKSB7XG4gICAgc3dpdGNoIChvcCkge1xuICAgICAgICBjYXNlICc9PSc6IGNhc2UgJyE9JzogY2FzZSAnPT09JzogY2FzZSAnIT09JzpcbiAgICAgICAgY2FzZSAnPCc6IGNhc2UgJz4nOiBjYXNlICc+PSc6IGNhc2UgJzw9JzpcbiAgICAgICAgY2FzZSAnaW4nOiBjYXNlICdpbnN0YW5jZW9mJzpcbiAgICAgICAgICAgIHJldHVybiB0cnVlO1xuICAgIH1cbiAgICByZXR1cm4gZmFsc2U7XG59XG5cbi8vIFRvIHByZXZlbnQgcmVjdXJzaW9uLFxuLy8gd2UgcmVtZW1iZXIgdGhlIHN0YXR1cyB1c2VkIGluIGFkZENvbnN0cmFpbnRzXG5jb25zdCB2aXNpdGVkU3RhdHVzID0gW107XG5mdW5jdGlvbiBjbGVhckNvbnN0cmFpbnRzKCkge1xuICAgIHZpc2l0ZWRTdGF0dXMubGVuZ3RoID0gMDtcbn1cblxubGV0IHJ0Q1g7XG5mdW5jdGlvbiBhZGRDb25zdHJhaW50cyhhc3ROb2RlLCBpbml0U3RhdHVzLCBuZXdSdENYKSB7XG5cbiAgICAvLyBzZXQgcnRDWFxuICAgIHJ0Q1ggPSBuZXdSdENYIHx8IHJ0Q1g7XG4gICAgY29uc3QgxIggPSBydENYLsSIO1xuXG4gICAgLy8gQ2hlY2sgd2hldGhlciB3ZSBoYXZlIHByb2Nlc3NlZCAnaW5pdFN0YXR1cycgYmVmb3JlXG4gICAgZm9yIChsZXQgaT0wOyBpIDwgdmlzaXRlZFN0YXR1cy5sZW5ndGg7IGkrKykge1xuICAgICAgICBpZiAoaW5pdFN0YXR1cy5lcXVhbHModmlzaXRlZFN0YXR1c1tpXSkpIHtcbiAgICAgICAgICAgICAvLyBJZiBzbywgZG8gbm90aGluZ1xuICAgICAgICAgICAgIC8vIHNpZ25pZnlpbmcgd2UgZGlkbid0IGFkZCBjb25zdHJhaW50c1xuICAgICAgICAgICAgIHJldHVybiBmYWxzZTtcbiAgICAgICAgIH1cbiAgICB9XG4gICAgLy8gSWYgdGhlIGluaXRTdGF0dXMgaXMgbmV3LCBwdXNoIGl0LlxuICAgIC8vIFdlIGRvIG5vdCByZWNvcmQgYXN0IHNpbmNlIGFzdCBub2RlIGRlcGVuZHMgb24gdGhlIHN0YXR1c1xuICAgIHZpc2l0ZWRTdGF0dXMucHVzaChpbml0U3RhdHVzKTtcblxuICAgIGZ1bmN0aW9uIHJlYWRNZW1iZXIobm9kZSwgY3VyU3RhdHVzLCBjKSB7XG4gICAgICAgIGNvbnN0IHJldCA9IMSILmdldChub2RlLCBjdXJTdGF0dXMuZGVsdGEpO1xuICAgICAgICBjb25zdCBvYmpBVmFsID0gYyhub2RlLm9iamVjdCwgY3VyU3RhdHVzLCB1bmRlZmluZWQpO1xuICAgICAgICBpZiAobm9kZS5wcm9wZXJ0eS50eXBlICE9PSAnSWRlbnRpZmllcicpIHtcbiAgICAgICAgICAgIC8vIHJldHVybiBmcm9tIHByb3BlcnR5IGlzIGlnbm9yZWRcbiAgICAgICAgICAgIGMobm9kZS5wcm9wZXJ0eSwgY3VyU3RhdHVzLCB1bmRlZmluZWQpO1xuICAgICAgICB9XG4gICAgICAgIGNvbnN0IFthY2NUeXBlLCBwcm9wTmFtZV0gPSBwcm9wQWNjZXNzKG5vZGUpO1xuXG4gICAgICAgIGlmIChhY2NUeXBlICE9PSAnZHVtbXlQcm9wZXJ0eScpIHtcbiAgICAgICAgICAgIG9iakFWYWwucHJvcGFnYXRlKG5ldyBjc3RyLlJlYWRQcm9wKHByb3BOYW1lLCByZXQpKTtcbiAgICAgICAgfVxuXG4gICAgICAgIC8vIHJldHVybnMgQVZhbCBmb3IgcmVjZWl2ZXIgYW5kIHJlYWQgbWVtYmVyXG4gICAgICAgIHJldHVybiBbb2JqQVZhbCwgcmV0XTtcbiAgICB9XG5cbiAgICAvLyBjb25zdHJhaW50IGdlbmVyYXRpbmcgd2Fsa2VyIGZvciBleHByZXNzaW9uc1xuICAgIGNvbnN0IGNvbnN0cmFpbnRHZW5lcmF0b3IgPSB3YWxrLm1ha2Uoe1xuXG4gICAgICAgIElkZW50aWZpZXI6IGZ1bmN0aW9uIChub2RlLCBjdXJTdGF0dXMsIGMpIHtcbiAgICAgICAgICAgIGlmIChteVdhbGtlci5pc0R1bW15SWROb2RlKG5vZGUpKSB7XG4gICAgICAgICAgICAgICAgLy8gUmV0dXJuIEFWYWxOdWxsIGZvciBkdW1teSBpZGVudGl0eSBub2RlXG4gICAgICAgICAgICAgICAgcmV0dXJuIHR5cGVzLkFWYWxOdWxsO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgY29uc3QgYXYgPSBjdXJTdGF0dXMuc2MuZ2V0QVZhbE9mKG5vZGUubmFtZSk7XG4gICAgICAgICAgICAvLyB1c2UgYXZhbCBpbiB0aGUgc2NvcGVcbiAgICAgICAgICAgIMSILnNldChub2RlLCBjdXJTdGF0dXMuZGVsdGEsIGF2KTtcbiAgICAgICAgICAgIHJldHVybiBhdjtcbiAgICAgICAgfSxcblxuICAgICAgICBUaGlzRXhwcmVzc2lvbjogZnVuY3Rpb24gKG5vZGUsIGN1clN0YXR1cywgYykge1xuICAgICAgICAgICAgY29uc3QgYXYgPSBjdXJTdGF0dXMuc2VsZjtcbiAgICAgICAgICAgIC8vIHVzZSBhdmFsIGZvciAndGhpcydcbiAgICAgICAgICAgIMSILnNldChub2RlLCBjdXJTdGF0dXMuZGVsdGEsIGF2KTtcbiAgICAgICAgICAgIHJldHVybiBhdjtcbiAgICAgICAgfSxcblxuICAgICAgICBMaXRlcmFsOiBmdW5jdGlvbiAobm9kZSwgY3VyU3RhdHVzLCBjKSB7XG4gICAgICAgICAgICBjb25zdCByZXMgPSDEiC5nZXQobm9kZSwgY3VyU3RhdHVzLmRlbHRhKTtcbiAgICAgICAgICAgIGlmIChub2RlLnJlZ2V4KSB7XG4gICAgICAgICAgICAgICAgLy8gbm90IGltcGxlbWVudGVkIHlldFxuICAgICAgICAgICAgICAgIC8vIHRocm93IG5ldyBFcnJvcigncmVnZXggbGl0ZXJhbCBpcyBub3QgaW1wbGVtZW50ZWQgeWV0Jyk7XG4gICAgICAgICAgICAgICAgcmV0dXJuIHJlcztcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIHN3aXRjaCAodHlwZW9mIG5vZGUudmFsdWUpIHtcbiAgICAgICAgICAgIGNhc2UgJ251bWJlcic6XG4gICAgICAgICAgICAgICAgcmVzLmFkZFR5cGUodHlwZXMuUHJpbU51bWJlcik7XG4gICAgICAgICAgICAgICAgYnJlYWs7XG4gICAgICAgICAgICBjYXNlICdzdHJpbmcnOlxuICAgICAgICAgICAgICAgIHJlcy5hZGRUeXBlKHR5cGVzLlByaW1TdHJpbmcpO1xuICAgICAgICAgICAgICAgIGJyZWFrO1xuICAgICAgICAgICAgY2FzZSAnYm9vbGVhbic6XG4gICAgICAgICAgICAgICAgcmVzLmFkZFR5cGUodHlwZXMuUHJpbUJvb2xlYW4pO1xuICAgICAgICAgICAgICAgIGJyZWFrO1xuICAgICAgICAgICAgY2FzZSAnb2JqZWN0JzpcbiAgICAgICAgICAgICAgICAvLyBJIGd1ZXNzOiBMaXRlcmFsICYmIG9iamVjdCA9PT4gbm9kZS52YWx1ZSA9PSBudWxsXG4gICAgICAgICAgICAgICAgLy8gbnVsbCBpcyBpZ25vcmVkLCBzbyBub3RoaW5nIHRvIGFkZFxuICAgICAgICAgICAgICAgIGJyZWFrO1xuICAgICAgICAgICAgY2FzZSAnZnVuY3Rpb24nOlxuICAgICAgICAgICAgICAgIHRocm93IG5ldyBFcnJvcignSSBndWVzcyBmdW5jdGlvbiBpcyBpbXBvc3NpYmxlIGhlcmUuJyk7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICByZXR1cm4gcmVzO1xuICAgICAgICB9LFxuXG4gICAgICAgIEFzc2lnbm1lbnRFeHByZXNzaW9uOiBmdW5jdGlvbiAobm9kZSwgY3VyU3RhdHVzLCBjKSB7XG4gICAgICAgICAgICBjb25zdCByaHNBVmFsID0gYyhub2RlLnJpZ2h0LCBjdXJTdGF0dXMsIHVuZGVmaW5lZCk7XG4gICAgICAgICAgICBpZiAobm9kZS5sZWZ0LnR5cGUgPT09ICdJZGVudGlmaWVyJykge1xuICAgICAgICAgICAgICAgIC8vIExIUyBpcyBhIHNpbXBsZSB2YXJpYWJsZS5cbiAgICAgICAgICAgICAgICBjb25zdCB2YXJOYW1lID0gbm9kZS5sZWZ0Lm5hbWU7XG4gICAgICAgICAgICAgICAgY29uc3QgbGhzQVZhbCA9IGN1clN0YXR1cy5zYy5nZXRBVmFsT2YodmFyTmFtZSk7XG4gICAgICAgICAgICAgICAgLy8gbGhzIGlzIG5vdCB2aXNpdGVkLiBOZWVkIHRvIGhhbmRsZSBoZXJlLlxuICAgICAgICAgICAgICAgIC8vIFVzZSBhdmFsIGZvdW5kIGluIHRoZSBzY29wZSBmb3IgbGhzXG4gICAgICAgICAgICAgICAgxIguc2V0KG5vZGUubGVmdCwgY3VyU3RhdHVzLmRlbHRhLCBsaHNBVmFsKTtcblxuICAgICAgICAgICAgICAgIGlmIChub2RlLm9wZXJhdG9yID09PSAnPScpIHtcbiAgICAgICAgICAgICAgICAgICAgLy8gc2ltcGxlIGFzc2lnbm1lbnRcbiAgICAgICAgICAgICAgICAgICAgcmhzQVZhbC5wcm9wYWdhdGUobGhzQVZhbCk7XG4gICAgICAgICAgICAgICAgICAgIC8vIG5vZGUncyBBVmFsIGZyb20gUkhTXG4gICAgICAgICAgICAgICAgICAgIMSILnNldChub2RlLCBjdXJTdGF0dXMuZGVsdGEsIHJoc0FWYWwpO1xuICAgICAgICAgICAgICAgICAgICByZXR1cm4gcmhzQVZhbDtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgLy8gdXBkYXRpbmcgYXNzaWdubWVudFxuICAgICAgICAgICAgICAgIGNvbnN0IHJlc0FWYWwgPSDEiC5nZXQobm9kZSwgY3VyU3RhdHVzLmRlbHRhKTtcbiAgICAgICAgICAgICAgICBpZiAobm9kZS5vcGVyYXRvciA9PT0gJys9Jykge1xuICAgICAgICAgICAgICAgICAgICAvLyBjb25jYXRlbmF0aW5nIHVwZGF0ZVxuICAgICAgICAgICAgICAgICAgICBsaHNBVmFsLnByb3BhZ2F0ZShuZXcgY3N0ci5Jc0FkZGVkKHJoc0FWYWwsIHJlc0FWYWwpKTtcbiAgICAgICAgICAgICAgICAgICAgcmhzQVZhbC5wcm9wYWdhdGUobmV3IGNzdHIuSXNBZGRlZChsaHNBVmFsLCByZXNBVmFsKSk7XG4gICAgICAgICAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgLy8gYXJpdGhtZXRpYyB1cGRhdGVcbiAgICAgICAgICAgICAgICAgICAgcmVzQVZhbC5hZGRUeXBlKHR5cGVzLlByaW1OdW1iZXIpO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICByZXR1cm4gcmVzQVZhbDtcbiAgICAgICAgICAgIH0gZWxzZSBpZiAobm9kZS5sZWZ0LnR5cGUgPT09ICdNZW1iZXJFeHByZXNzaW9uJykge1xuICAgICAgICAgICAgICAgIGNvbnN0IG9iakFWYWwgPSBjKG5vZGUubGVmdC5vYmplY3QsIGN1clN0YXR1cywgdW5kZWZpbmVkKTtcbiAgICAgICAgICAgICAgICBjb25zdCBbYWNjVHlwZSwgcHJvcE5hbWVdID0gcHJvcEFjY2Vzcyhub2RlLmxlZnQpO1xuICAgICAgICAgICAgICAgIGlmIChub2RlLm9wZXJhdG9yID09PSAnPScpIHtcbiAgICAgICAgICAgICAgICAgICAgLy8gYXNzaWdubWVudCB0byBtZW1iZXJcbiAgICAgICAgICAgICAgICAgICAgaWYgKGFjY1R5cGUgIT09ICdkdW1teVByb3BlcnR5Jykge1xuICAgICAgICAgICAgICAgICAgICAgICAgb2JqQVZhbC5wcm9wYWdhdGUobmV3IGNzdHIuV3JpdGVQcm9wKHByb3BOYW1lLCByaHNBVmFsKSk7XG4gICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgLy8gaWYgcHJvcGVydHkgaXMgbnVtYmVyIGxpdGVyYWwsIGFsc28gd3JpdGUgdG8gJ3Vua25vd24nXG4gICAgICAgICAgICAgICAgICAgIGlmIChhY2NUeXBlID09PSAnbnVtYmVyTGl0ZXJhbCcpIHtcbiAgICAgICAgICAgICAgICAgICAgICAgIG9iakFWYWwucHJvcGFnYXRlKG5ldyBjc3RyLldyaXRlUHJvcChudWxsLCByaHNBVmFsKSk7XG4gICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgLy8gbm9kZSdzIEFWYWwgZnJvbSBSSFNcbiAgICAgICAgICAgICAgICAgICAgxIguc2V0KG5vZGUsIGN1clN0YXR1cy5kZWx0YSwgcmhzQVZhbCk7XG4gICAgICAgICAgICAgICAgICAgIHJldHVybiByaHNBVmFsO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAvLyB1cGRhdGluZyBhc3NpZ25tZW50XG4gICAgICAgICAgICAgICAgY29uc3QgcmVzQVZhbCA9IMSILmdldChub2RlLCBjdXJTdGF0dXMuZGVsdGEpO1xuICAgICAgICAgICAgICAgIGNvbnN0IFssIHJldEFWYWxdID0gcmVhZE1lbWJlcihub2RlLmxlZnQsIGN1clN0YXR1cywgYyk7XG4gICAgICAgICAgICAgICAgaWYgKG5vZGUub3BlcmF0b3IgPT09ICcrPScpIHtcbiAgICAgICAgICAgICAgICAgICAgLy8gY29uY2F0ZW5hdGluZyB1cGRhdGVcbiAgICAgICAgICAgICAgICAgICAgcmV0QVZhbC5wcm9wYWdhdGUobmV3IGNzdHIuSXNBZGRlZChyaHNBVmFsLCByZXNBVmFsKSk7XG4gICAgICAgICAgICAgICAgICAgIHJoc0FWYWwucHJvcGFnYXRlKG5ldyBjc3RyLklzQWRkZWQocmV0QVZhbCwgcmVzQVZhbCkpO1xuICAgICAgICAgICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgICAgICAgICAgIC8vIGFyaXRobWV0aWMgdXBkYXRlXG4gICAgICAgICAgICAgICAgICAgIHJlc0FWYWwuYWRkVHlwZSh0eXBlcy5QcmltTnVtYmVyKTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgcmV0dXJuIHJlc0FWYWw7XG4gICAgICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgICAgICAgIGNvbnNvbGUuaW5mbygnQXNzaWdubWVudCB1c2luZyBwYXR0ZXJuIGlzIG5vdCBpbXBsZW1lbnRlZCcpO1xuICAgICAgICAgICAgfVxuICAgICAgICB9LFxuXG4gICAgICAgIFZhcmlhYmxlRGVjbGFyYXRpb246IGZ1bmN0aW9uIChub2RlLCBjdXJTdGF0dXMsIGMpIHtcbiAgICAgICAgICAgIGZvciAobGV0IGkgPSAwOyBpIDwgbm9kZS5kZWNsYXJhdGlvbnMubGVuZ3RoOyBpKyspIHtcbiAgICAgICAgICAgICAgICBjb25zdCBkZWNsID0gbm9kZS5kZWNsYXJhdGlvbnNbaV07XG4gICAgICAgICAgICAgICAgY29uc3QgbGhzQVZhbCA9IGN1clN0YXR1cy5zYy5nZXRBVmFsT2YoZGVjbC5pZC5uYW1lKTtcbiAgICAgICAgICAgICAgICAvLyBkZWNsYXJlZCB2YXIgbm9kZSBpcyAnaWQnXG4gICAgICAgICAgICAgICAgxIguc2V0KGRlY2wuaWQsIGN1clN0YXR1cy5kZWx0YSwgbGhzQVZhbCk7XG4gICAgICAgICAgICAgICAgaWYgKGRlY2wuaW5pdCkge1xuICAgICAgICAgICAgICAgICAgICBjb25zdCByaHNBVmFsID0gYyhkZWNsLmluaXQsIGN1clN0YXR1cywgdW5kZWZpbmVkKTtcbiAgICAgICAgICAgICAgICAgICAgxIguc2V0KGRlY2wuaW5pdCwgY3VyU3RhdHVzLmRlbHRhLCByaHNBVmFsKTtcbiAgICAgICAgICAgICAgICAgICAgcmhzQVZhbC5wcm9wYWdhdGUobGhzQVZhbCk7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgfVxuICAgICAgICB9LFxuXG4gICAgICAgIExvZ2ljYWxFeHByZXNzaW9uOiBmdW5jdGlvbiAobm9kZSwgY3VyU3RhdHVzLCBjKSB7XG4gICAgICAgICAgICBjb25zdCByZXMgPSDEiC5nZXQobm9kZSwgY3VyU3RhdHVzLmRlbHRhKTtcbiAgICAgICAgICAgIGNvbnN0IGxlZnQgPSBjKG5vZGUubGVmdCwgY3VyU3RhdHVzLCB1bmRlZmluZWQpO1xuICAgICAgICAgICAgY29uc3QgcmlnaHQgPSBjKG5vZGUucmlnaHQsIGN1clN0YXR1cywgdW5kZWZpbmVkKTtcbiAgICAgICAgICAgIGxlZnQucHJvcGFnYXRlKHJlcyk7XG4gICAgICAgICAgICByaWdodC5wcm9wYWdhdGUocmVzKTtcbiAgICAgICAgICAgIHJldHVybiByZXM7XG4gICAgICAgIH0sXG5cbiAgICAgICAgQ29uZGl0aW9uYWxFeHByZXNzaW9uOiBmdW5jdGlvbiAobm9kZSwgY3VyU3RhdHVzLCBjKSB7XG4gICAgICAgICAgICBjb25zdCByZXMgPSDEiC5nZXQobm9kZSwgY3VyU3RhdHVzLmRlbHRhKTtcbiAgICAgICAgICAgIGMobm9kZS50ZXN0LCBjdXJTdGF0dXMsIHVuZGVmaW5lZCk7XG4gICAgICAgICAgICBjb25zdCBjb25zID0gYyhub2RlLmNvbnNlcXVlbnQsIGN1clN0YXR1cywgdW5kZWZpbmVkKTtcbiAgICAgICAgICAgIGNvbnN0IGFsdCA9IGMobm9kZS5hbHRlcm5hdGUsIGN1clN0YXR1cywgdW5kZWZpbmVkKTtcbiAgICAgICAgICAgIGNvbnMucHJvcGFnYXRlKHJlcyk7XG4gICAgICAgICAgICBhbHQucHJvcGFnYXRlKHJlcyk7XG4gICAgICAgICAgICByZXR1cm4gcmVzO1xuICAgICAgICB9LFxuXG4gICAgICAgIE5ld0V4cHJlc3Npb246IGZ1bmN0aW9uIChub2RlLCBjdXJTdGF0dXMsIGMpIHtcbiAgICAgICAgICAgIGNvbnN0IHJldCA9IMSILmdldChub2RlLCBjdXJTdGF0dXMuZGVsdGEpO1xuICAgICAgICAgICAgY29uc3QgY2FsbGVlID0gYyhub2RlLmNhbGxlZSwgY3VyU3RhdHVzLCB1bmRlZmluZWQpO1xuICAgICAgICAgICAgY29uc3QgYXJncyA9IFtdO1xuICAgICAgICAgICAgZm9yIChsZXQgaSA9IDA7IGkgPCBub2RlLmFyZ3VtZW50cy5sZW5ndGg7IGkrKykge1xuICAgICAgICAgICAgICAgIGFyZ3MucHVzaChjKG5vZGUuYXJndW1lbnRzW2ldLCBjdXJTdGF0dXMsIHVuZGVmaW5lZCkpO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgY29uc3QgbmV3RGVsdGEgPSBjdXJTdGF0dXMuZGVsdGEuYXBwZW5kT25lKG5vZGVbJ0BsYWJlbCddKTtcbiAgICAgICAgICAgIGNhbGxlZS5wcm9wYWdhdGUoXG4gICAgICAgICAgICAgICAgbmV3IGNzdHIuSXNDdG9yKFxuICAgICAgICAgICAgICAgICAgICBhcmdzLFxuICAgICAgICAgICAgICAgICAgICByZXQsXG4gICAgICAgICAgICAgICAgICAgIGN1clN0YXR1cy5leGMsXG4gICAgICAgICAgICAgICAgICAgIG5ld0RlbHRhKSk7XG4gICAgICAgICAgICByZXR1cm4gcmV0O1xuICAgICAgICB9LFxuXG4gICAgICAgIEFycmF5RXhwcmVzc2lvbjogZnVuY3Rpb24gKG5vZGUsIGN1clN0YXR1cywgYykge1xuICAgICAgICAgICAgY29uc3QgcmV0ID0gxIguZ2V0KG5vZGUsIGN1clN0YXR1cy5kZWx0YSk7XG4gICAgICAgICAgICAvLyBOT1RFIHByb3RvdHlwZSBvYmplY3QgaXMgbm90IHJlY29yZGVkIGluIMSIXG4gICAgICAgICAgICBjb25zdCBhcnJUeXBlID0gbmV3IHR5cGVzLkFyclR5cGUobmV3IHR5cGVzLkFWYWwocnRDWC5wcm90b3MuQXJyYXkpKTtcbiAgICAgICAgICAgIC8vIGFkZCBsZW5ndGggcHJvcGVydHlcbiAgICAgICAgICAgIGFyclR5cGUuZ2V0UHJvcCgnbGVuZ3RoJykuYWRkVHlwZSh0eXBlcy5QcmltTnVtYmVyKTtcblxuICAgICAgICAgICAgcmV0LmFkZFR5cGUoYXJyVHlwZSk7XG5cbiAgICAgICAgICAgIC8vIGFkZCBhcnJheSBlbGVtZW50c1xuICAgICAgICAgICAgZm9yIChsZXQgaSA9IDA7IGkgPCBub2RlLmVsZW1lbnRzLmxlbmd0aDsgaSsrKSB7XG4gICAgICAgICAgICAgICAgaWYgKG5vZGUuZWxlbWVudHNbaV0gPT0gbnVsbCkge1xuICAgICAgICAgICAgICAgICAgICBjb250aW51ZTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgY29uc3QgZWx0QVZhbCA9IGMobm9kZS5lbGVtZW50c1tpXSwgY3VyU3RhdHVzLCB1bmRlZmluZWQpO1xuXG4gICAgICAgICAgICAgICAgY29uc3QgcHJvcCA9IGkgKyAnJztcbiAgICAgICAgICAgICAgICByZXQucHJvcGFnYXRlKG5ldyBjc3RyLldyaXRlUHJvcChwcm9wLCBlbHRBVmFsKSk7XG4gICAgICAgICAgICAgICAgcmV0LnByb3BhZ2F0ZShuZXcgY3N0ci5Xcml0ZVByb3AobnVsbCwgZWx0QVZhbCkpO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgcmV0dXJuIHJldDtcbiAgICAgICAgfSxcblxuICAgICAgICBPYmplY3RFeHByZXNzaW9uOiBmdW5jdGlvbiAobm9kZSwgY3VyU3RhdHVzLCBjKSB7XG4gICAgICAgICAgICBjb25zdCByZXQgPSDEiC5nZXQobm9kZSwgY3VyU3RhdHVzLmRlbHRhKTtcbiAgICAgICAgICAgIC8vIE5PVEUgcHJvdG90eXBlIG9iamVjdCBpcyBub3QgcmVjb3JkZWQgaW4gxIhcbiAgICAgICAgICAgIGNvbnN0IG9ialR5cGUgPSBuZXcgdHlwZXMuT2JqVHlwZShuZXcgdHlwZXMuQVZhbChydENYLnByb3Rvcy5PYmplY3QpKTtcbiAgICAgICAgICAgIHJldC5hZGRUeXBlKG9ialR5cGUpO1xuXG4gICAgICAgICAgICBmb3IgKGxldCBpID0gMDsgaSA8IG5vZGUucHJvcGVydGllcy5sZW5ndGg7IGkrKykge1xuICAgICAgICAgICAgICAgIGNvbnN0IHByb3BQYWlyID0gbm9kZS5wcm9wZXJ0aWVzW2ldO1xuICAgICAgICAgICAgICAgIGNvbnN0IHByb3BLZXkgPSBwcm9wUGFpci5rZXk7XG4gICAgICAgICAgICAgICAgbGV0IG5hbWU7XG4gICAgICAgICAgICAgICAgY29uc3QgcHJvcEV4cHIgPSBwcm9wUGFpci52YWx1ZTtcblxuICAgICAgICAgICAgICAgIGNvbnN0IGZsZEFWYWwgPSBjKHByb3BFeHByLCBjdXJTdGF0dXMsIHVuZGVmaW5lZCk7XG5cbiAgICAgICAgICAgICAgICBpZiAocHJvcEtleS50eXBlID09PSAnSWRlbnRpZmllcicpIHtcbiAgICAgICAgICAgICAgICAgICAgbmFtZSA9IHByb3BLZXkubmFtZTtcbiAgICAgICAgICAgICAgICB9IGVsc2UgaWYgKHR5cGVvZiBwcm9wS2V5LnZhbHVlID09PSAnc3RyaW5nJykge1xuICAgICAgICAgICAgICAgICAgICBuYW1lID0gcHJvcEtleS52YWx1ZTtcbiAgICAgICAgICAgICAgICB9IGVsc2UgaWYgKHR5cGVvZiBwcm9wS2V5LnZhbHVlID09PSAnbnVtYmVyJykge1xuICAgICAgICAgICAgICAgICAgICAvLyBjb252ZXJ0IG51bWJlciB0byBzdHJpbmdcbiAgICAgICAgICAgICAgICAgICAgbmFtZSA9IHByb3BLZXkudmFsdWUgKyAnJztcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgcmV0LnByb3BhZ2F0ZShuZXcgY3N0ci5Xcml0ZVByb3AobmFtZSwgZmxkQVZhbCkpO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgcmV0dXJuIHJldDtcbiAgICAgICAgfSxcblxuICAgICAgICBBcnJvd0Z1bmN0aW9uRXhwcmVzc2lvbjogZnVuY3Rpb24gKG5vZGUsIGN1clN0YXR1cywgYykge1xuICAgICAgICAgICAgaWYgKCFub2RlLmZuSW5zdGFuY2VzKSB7XG4gICAgICAgICAgICAgICAgbm9kZS5mbkluc3RhbmNlcyA9IFtdO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgbGV0IGZuSW5zdGFuY2UgPSBudWxsO1xuICAgICAgICAgICAgbm9kZS5mbkluc3RhbmNlcy5mb3JFYWNoKGZ1bmN0aW9uIChmblR5cGUpIHtcbiAgICAgICAgICAgICAgICBpZiAoZm5UeXBlLnNjID09PSBjdXJTdGF0dXMuc2MpIHtcbiAgICAgICAgICAgICAgICAgICAgZm5JbnN0YW5jZSA9IGZuVHlwZTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICB9KTtcbiAgICAgICAgICAgIGlmICghZm5JbnN0YW5jZSkge1xuICAgICAgICAgICAgICAgIGZuSW5zdGFuY2VcbiAgICAgICAgICAgICAgICAgICAgPSBuZXcgdHlwZXMuRm5UeXBlKG5ldyB0eXBlcy5BVmFsKHJ0Q1gucHJvdG9zLkZ1bmN0aW9uKSxcbiAgICAgICAgICAgICAgICAgICAgJ1thcnJvdyBmdW5jdGlvbl0nLFxuICAgICAgICAgICAgICAgICAgICBub2RlLmJvZHlbJ0BibG9jayddLmdldFBhcmFtVmFyTmFtZXMoKSxcbiAgICAgICAgICAgICAgICAgICAgY3VyU3RhdHVzLnNjLFxuICAgICAgICAgICAgICAgICAgICBub2RlLFxuICAgICAgICAgICAgICAgICAgICB1bmRlZmluZWQsXG4gICAgICAgICAgICAgICAgICAgIGN1clN0YXR1cy5zZWxmICAgIC8vIGFycm93IGZ1bmN0aW9uIHNob3VsZCByZW1lbWJlciBBVmFsIG9mIG91dGVyIHRoaXMuXG4gICAgICAgICAgICAgICAgKTtcbiAgICAgICAgICAgICAgICBub2RlLmZuSW5zdGFuY2VzLnB1c2goZm5JbnN0YW5jZSk7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBjb25zdCByZXQgPSDEiC5nZXQobm9kZSwgY3VyU3RhdHVzLmRlbHRhKTtcbiAgICAgICAgICAgIHJldC5hZGRUeXBlKGZuSW5zdGFuY2UpO1xuXG4gICAgICAgICAgICByZXQucHJvcGFnYXRlKFxuICAgICAgICAgICAgICAgIG5ldyBjc3RyLklzQ2FsbGVlKFxuICAgICAgICAgICAgICAgICAgICB0eXBlcy5BVmFsTnVsbCwgICAgICAgICAgICAgICAgICAvLyBub3RoaW5nIHRvIHByb3BhZ2F0ZSB0byBzZWxmXG4gICAgICAgICAgICAgICAgICAgIFtdLCAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIC8vIG5vIGFyZ3VtZW50c1xuICAgICAgICAgICAgICAgICAgICB0eXBlcy5BVmFsTnVsbCwgICAgICAgICAgICAgICAgICAvLyByZXR1cm4gaXMgaWdub3JlZFxuICAgICAgICAgICAgICAgICAgICB0eXBlcy5BVmFsTnVsbCwgICAgICAgICAgICAgICAgICAvLyBubyB2YWxpZCBjYWxsZXIgd2l0aCBleGNBVmFsXG4gICAgICAgICAgICAgICAgICAgIGNzYy5DYWxsU2l0ZUNvbnRleHQubnVsbENvbnRleHQgIC8vIFVzaW5nIG51bGxDb250ZXh0XG4gICAgICAgICAgICAgICAgKVxuICAgICAgICAgICAgKTtcblxuICAgICAgICAgICAgcmV0dXJuIHJldDtcbiAgICAgICAgfSxcblxuICAgICAgICBGdW5jdGlvbkV4cHJlc3Npb246IGZ1bmN0aW9uIChub2RlLCBjdXJTdGF0dXMsIGMpIHtcbiAgICAgICAgICAgIGlmICghbm9kZS5mbkluc3RhbmNlcykge1xuICAgICAgICAgICAgICAgIG5vZGUuZm5JbnN0YW5jZXMgPSBbXTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGxldCBmbkluc3RhbmNlID0gbnVsbDtcbiAgICAgICAgICAgIG5vZGUuZm5JbnN0YW5jZXMuZm9yRWFjaChmdW5jdGlvbiAoZm5UeXBlKSB7XG4gICAgICAgICAgICAgICAgaWYgKGZuVHlwZS5zYyA9PT0gY3VyU3RhdHVzLnNjKSB7XG4gICAgICAgICAgICAgICAgICAgIGZuSW5zdGFuY2UgPSBmblR5cGU7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgfSk7XG4gICAgICAgICAgICBpZiAoIWZuSW5zdGFuY2UpIHtcbiAgICAgICAgICAgICAgICAvLyBOT1RFIHByb3RvdHlwZSBvYmplY3QgaXMgbm90IHJlY29yZGVkIGluIMSIXG4gICAgICAgICAgICAgICAgZm5JbnN0YW5jZVxuICAgICAgICAgICAgICAgICAgICA9IG5ldyB0eXBlcy5GblR5cGUobmV3IHR5cGVzLkFWYWwocnRDWC5wcm90b3MuRnVuY3Rpb24pLFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgJ1thbm9ueW1vdXMgZnVuY3Rpb25dJyxcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIG5vZGUuYm9keVsnQGJsb2NrJ10uZ2V0UGFyYW1WYXJOYW1lcygpLFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgY3VyU3RhdHVzLnNjLFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgbm9kZSxcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIHJ0Q1gucHJvdG9zLk9iamVjdCk7XG4gICAgICAgICAgICAgICAgbm9kZS5mbkluc3RhbmNlcy5wdXNoKGZuSW5zdGFuY2UpO1xuICAgICAgICAgICAgICAgIC8vIE5PVEUgcHJvdG90eXBlIG9iamVjdCBpcyBub3QgcmVjb3JkZWQgaW4gxIhcbiAgICAgICAgICAgICAgICBjb25zdCBwcm90b3R5cGVPYmplY3QgPVxuICAgICAgICAgICAgICAgICAgICBuZXcgdHlwZXMuT2JqVHlwZShuZXcgdHlwZXMuQVZhbChydENYLnByb3Rvcy5PYmplY3QpLFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAnLnByb3RvdHlwZScpO1xuICAgICAgICAgICAgICAgIC8vIEZvciAucHJvdG90eXBlXG4gICAgICAgICAgICAgICAgbmV3IHR5cGVzLkFWYWwoZm5JbnN0YW5jZSkucHJvcGFnYXRlKFxuICAgICAgICAgICAgICAgICAgICBuZXcgY3N0ci5Xcml0ZVByb3AoJ3Byb3RvdHlwZScsbmV3IHR5cGVzLkFWYWwocHJvdG90eXBlT2JqZWN0KSlcbiAgICAgICAgICAgICAgICApO1xuICAgICAgICAgICAgICAgIC8vIEZvciAucHJvdG90eXBlLmNvbnN0cnVjdG9yXG4gICAgICAgICAgICAgICAgY29uc3QgY29uc3RydWN0b3JQcm9wID0gcHJvdG90eXBlT2JqZWN0LmdldFByb3AoJ2NvbnN0cnVjdG9yJyk7XG4gICAgICAgICAgICAgICAgY29uc3RydWN0b3JQcm9wLmFkZFR5cGUoZm5JbnN0YW5jZSk7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBjb25zdCByZXQgPSDEiC5nZXQobm9kZSwgY3VyU3RhdHVzLmRlbHRhKTtcbiAgICAgICAgICAgIHJldC5hZGRUeXBlKGZuSW5zdGFuY2UpO1xuXG4gICAgICAgICAgICAvLyBDYWxsIHRoZSBmdW5jdGlvbiB1c2luZyBudWxsQ29udGV4dFxuICAgICAgICAgICAgY29uc3QgW3NlbGZBVmFsLCxdID0gZm5JbnN0YW5jZS5nZXRGdW5FbnYoY3NjLkNhbGxTaXRlQ29udGV4dC5udWxsQ29udGV4dCk7XG4gICAgICAgICAgICAvLyBhZGQgdGhlIGZ1bmN0aW9uJ3MgaW5zdGFuY2VcbiAgICAgICAgICAgIHNlbGZBVmFsLmFkZFR5cGUoZm5JbnN0YW5jZS5nZXRJbnN0YW5jZSgpKTtcbiAgICAgICAgICAgIHJldC5wcm9wYWdhdGUoXG4gICAgICAgICAgICAgICAgbmV3IGNzdHIuSXNDYWxsZWUoXG4gICAgICAgICAgICAgICAgICAgIHR5cGVzLkFWYWxOdWxsLCAgICAgICAgICAgICAgICAgIC8vIG5vdGhpbmcgdG8gcHJvcGFnYXRlIHRvIHNlbGZcbiAgICAgICAgICAgICAgICAgICAgW10sICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgLy8gbm8gYXJndW1lbnRzXG4gICAgICAgICAgICAgICAgICAgIHR5cGVzLkFWYWxOdWxsLCAgICAgICAgICAgICAgICAgIC8vIHJldHVybiBpcyBpZ25vcmVkXG4gICAgICAgICAgICAgICAgICAgIHR5cGVzLkFWYWxOdWxsLCAgICAgICAgICAgICAgICAgIC8vIG5vIHZhbGlkIGNhbGxlciB3aXRoIGV4Y0FWYWxcbiAgICAgICAgICAgICAgICAgICAgY3NjLkNhbGxTaXRlQ29udGV4dC5udWxsQ29udGV4dCAgLy8gVXNpbmcgbnVsbENvbnRleHRcbiAgICAgICAgICAgICAgICApXG4gICAgICAgICAgICApO1xuXG4gICAgICAgICAgICByZXR1cm4gcmV0O1xuICAgICAgICB9LFxuXG4gICAgICAgIEZ1bmN0aW9uRGVjbGFyYXRpb246IGZ1bmN0aW9uIChub2RlLCBjdXJTdGF0dXMsIGMpIHtcbiAgICAgICAgICAgIC8vIERyb3AgaW5pdGlhbCBjYXRjaCBvciBub3JtYWwgc2NvcGVzXG4gICAgICAgICAgICBjb25zdCBzYzAgPSBjdXJTdGF0dXMuc2MucmVtb3ZlSW5pdGlhbENhdGNoT3JOb3JtYWxCbG9ja3MoKTtcbiAgICAgICAgICAgIGlmICghbm9kZS5mbkluc3RhbmNlcykge1xuICAgICAgICAgICAgICAgIG5vZGUuZm5JbnN0YW5jZXMgPSBbXTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGxldCBmbkluc3RhbmNlID0gbnVsbDtcbiAgICAgICAgICAgIG5vZGUuZm5JbnN0YW5jZXMuZm9yRWFjaChmdW5jdGlvbiAoZm5UeXBlKSB7XG4gICAgICAgICAgICAgICAgaWYgKGZuVHlwZS5zYyA9PT0gc2MwKSB7XG4gICAgICAgICAgICAgICAgICAgIGZuSW5zdGFuY2UgPSBmblR5cGU7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgfSk7XG4gICAgICAgICAgICBpZiAoIWZuSW5zdGFuY2UpIHtcbiAgICAgICAgICAgICAgICAvLyBOT1RFIHByb3RvdHlwZSBvYmplY3QgaXMgbm90IHJlY29yZGVkIGluIMSIXG4gICAgICAgICAgICAgICAgZm5JbnN0YW5jZVxuICAgICAgICAgICAgICAgICAgICA9IG5ldyB0eXBlcy5GblR5cGUobmV3IHR5cGVzLkFWYWwocnRDWC5wcm90b3MuRnVuY3Rpb24pLFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgbm9kZS5pZC5uYW1lLFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgbm9kZS5ib2R5WydAYmxvY2snXS5nZXRQYXJhbVZhck5hbWVzKCksXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBzYzAsXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBub2RlLFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgcnRDWC5wcm90b3MuT2JqZWN0KTtcbiAgICAgICAgICAgICAgICBub2RlLmZuSW5zdGFuY2VzLnB1c2goZm5JbnN0YW5jZSk7XG4gICAgICAgICAgICAgICAgLy8gZm9yIGVhY2ggZm5JbnN0YW5jZSwgYXNzaWduIG9uZSBwcm90b3R5cGUgb2JqZWN0XG4gICAgICAgICAgICAgICAgLy8gTk9URSBwcm90b3R5cGUgb2JqZWN0IGlzIG5vdCByZWNvcmRlZCBpbiDEiFxuICAgICAgICAgICAgICAgIGNvbnN0IHByb3RvdHlwZU9iamVjdCA9XG4gICAgICAgICAgICAgICAgICAgIG5ldyB0eXBlcy5PYmpUeXBlKG5ldyB0eXBlcy5BVmFsKHJ0Q1gucHJvdG9zLk9iamVjdCksXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIG5vZGUuaWQubmFtZSArICcucHJvdG90eXBlJyk7XG4gICAgICAgICAgICAgICAgLy8gRm9yIC5wcm90b3R5cGVcbiAgICAgICAgICAgICAgICBuZXcgdHlwZXMuQVZhbChmbkluc3RhbmNlKS5wcm9wYWdhdGUoXG4gICAgICAgICAgICAgICAgICAgIG5ldyBjc3RyLldyaXRlUHJvcCgncHJvdG90eXBlJywgbmV3IHR5cGVzLkFWYWwocHJvdG90eXBlT2JqZWN0KSlcbiAgICAgICAgICAgICAgICApO1xuICAgICAgICAgICAgICAgIC8vIEZvciAucHJvdG90eXBlLmNvbnN0cnVjdG9yXG4gICAgICAgICAgICAgICAgY29uc3QgY29uc3RydWN0b3JQcm9wID0gcHJvdG90eXBlT2JqZWN0LmdldFByb3AoJ2NvbnN0cnVjdG9yJyk7XG4gICAgICAgICAgICAgICAgY29uc3RydWN0b3JQcm9wLmFkZFR5cGUoZm5JbnN0YW5jZSk7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBjb25zdCBsaHNBVmFsID0gc2MwLmdldEFWYWxPZihub2RlLmlkLm5hbWUpO1xuICAgICAgICAgICAgbGhzQVZhbC5hZGRUeXBlKGZuSW5zdGFuY2UpO1xuXG4gICAgICAgICAgICAvLyBDYWxsIHRoZSBmdW5jdGlvbiB1c2luZyBudWxsQ29udGV4dFxuICAgICAgICAgICAgY29uc3QgW3NlbGZBVmFsLCxdID0gZm5JbnN0YW5jZS5nZXRGdW5FbnYoY3NjLkNhbGxTaXRlQ29udGV4dC5udWxsQ29udGV4dCk7XG4gICAgICAgICAgICAvLyBhZGQgdGhlIGZ1bmN0aW9uJ3MgaW5zdGFuY2VcbiAgICAgICAgICAgIHNlbGZBVmFsLmFkZFR5cGUoZm5JbnN0YW5jZS5nZXRJbnN0YW5jZSgpKTtcbiAgICAgICAgICAgIGxoc0FWYWwucHJvcGFnYXRlKFxuICAgICAgICAgICAgICAgIG5ldyBjc3RyLklzQ2FsbGVlKFxuICAgICAgICAgICAgICAgICAgICB0eXBlcy5BVmFsTnVsbCwgICAgICAgICAgICAgICAgICAvLyBub3RoaW5nIHRvIHByb3BhZ2F0ZSB0byBzZWxmXG4gICAgICAgICAgICAgICAgICAgIFtdLCAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIC8vIG5vIGFyZ3VtZW50c1xuICAgICAgICAgICAgICAgICAgICB0eXBlcy5BVmFsTnVsbCwgICAgICAgICAgICAgICAgICAvLyByZXR1cm4gaXMgaWdub3JlZFxuICAgICAgICAgICAgICAgICAgICB0eXBlcy5BVmFsTnVsbCwgICAgICAgICAgICAgICAgICAvLyBubyB2YWxpZCBjYWxsZXIgd2l0aCBleGNBVmFsXG4gICAgICAgICAgICAgICAgICAgIGNzYy5DYWxsU2l0ZUNvbnRleHQubnVsbENvbnRleHQgIC8vIFVzaW5nIG51bGxDb250ZXh0XG4gICAgICAgICAgICAgICAgKVxuICAgICAgICAgICAgKTtcblxuICAgICAgICAgICAgLy8gbm90aGluZyB0byByZXR1cm5cbiAgICAgICAgICAgIHJldHVybiB0eXBlcy5BVmFsTnVsbDtcbiAgICAgICAgfSxcblxuICAgICAgICBTZXF1ZW5jZUV4cHJlc3Npb246IGZ1bmN0aW9uIChub2RlLCBjdXJTdGF0dXMsIGMpIHtcbiAgICAgICAgICAgIGNvbnN0IGxhc3RJbmRleCA9IG5vZGUuZXhwcmVzc2lvbnMubGVuZ3RoIC0gMTtcbiAgICAgICAgICAgIGZvciAobGV0IGkgPSAwOyBpIDwgbGFzdEluZGV4OyBpKyspIHtcbiAgICAgICAgICAgICAgICBjKG5vZGUuZXhwcmVzc2lvbnNbaV0sIGN1clN0YXR1cywgdW5kZWZpbmVkKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGNvbnN0IGxhc3RBVmFsID0gYyhub2RlLmV4cHJlc3Npb25zW2xhc3RJbmRleF0sIGN1clN0YXR1cywgdW5kZWZpbmVkKTtcbiAgICAgICAgICAgIMSILnNldChub2RlLCBjdXJTdGF0dXMuZGVsdGEsIGxhc3RBVmFsKTtcbiAgICAgICAgICAgIHJldHVybiBsYXN0QVZhbDtcbiAgICAgICAgfSxcblxuICAgICAgICBVbmFyeUV4cHJlc3Npb246IGZ1bmN0aW9uIChub2RlLCBjdXJTdGF0dXMsIGMpIHtcbiAgICAgICAgICAgIGMobm9kZS5hcmd1bWVudCwgY3VyU3RhdHVzLCB1bmRlZmluZWQpO1xuICAgICAgICAgICAgY29uc3QgcmVzID0gxIguZ2V0KG5vZGUsIGN1clN0YXR1cy5kZWx0YSk7XG4gICAgICAgICAgICBjb25zdCB0eXBlID0gdW5vcFJlc3VsdFR5cGUobm9kZS5vcGVyYXRvcik7XG4gICAgICAgICAgICBpZiAodHlwZSkge1xuICAgICAgICAgICAgICAgIHJlcy5hZGRUeXBlKHR5cGUpO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgcmV0dXJuIHJlcztcbiAgICAgICAgfSxcblxuICAgICAgICBVcGRhdGVFeHByZXNzaW9uOiBmdW5jdGlvbiAobm9kZSwgY3VyU3RhdHVzLCBjKSB7XG4gICAgICAgICAgICBjKG5vZGUuYXJndW1lbnQsIGN1clN0YXR1cywgdW5kZWZpbmVkKTtcbiAgICAgICAgICAgIGNvbnN0IHJlcyA9IMSILmdldChub2RlLCBjdXJTdGF0dXMuZGVsdGEpO1xuICAgICAgICAgICAgcmVzLmFkZFR5cGUodHlwZXMuUHJpbU51bWJlcik7XG4gICAgICAgICAgICAvLyBXZSBpZ25vcmUgdGhlIGVmZmVjdCBvZiB1cGRhdGluZyB0byBudW1iZXIgdHlwZVxuICAgICAgICAgICAgcmV0dXJuIHJlcztcbiAgICAgICAgfSxcblxuICAgICAgICBCaW5hcnlFeHByZXNzaW9uOiBmdW5jdGlvbiAobm9kZSwgY3VyU3RhdHVzLCBjKSB7XG4gICAgICAgICAgICBjb25zdCBsT3ByZCA9IGMobm9kZS5sZWZ0LCBjdXJTdGF0dXMsIHVuZGVmaW5lZCk7XG4gICAgICAgICAgICBjb25zdCByT3ByZCA9IGMobm9kZS5yaWdodCwgY3VyU3RhdHVzLCB1bmRlZmluZWQpO1xuICAgICAgICAgICAgY29uc3QgcmVzID0gxIguZ2V0KG5vZGUsIGN1clN0YXR1cy5kZWx0YSk7XG5cbiAgICAgICAgICAgIGlmIChub2RlLm9wZXJhdG9yID09ICcrJykge1xuICAgICAgICAgICAgICAgIGxPcHJkLnByb3BhZ2F0ZShuZXcgY3N0ci5Jc0FkZGVkKHJPcHJkLCByZXMpKTtcbiAgICAgICAgICAgICAgICByT3ByZC5wcm9wYWdhdGUobmV3IGNzdHIuSXNBZGRlZChsT3ByZCwgcmVzKSk7XG4gICAgICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgICAgICAgIGlmIChiaW5vcElzQm9vbGVhbihub2RlLm9wZXJhdG9yKSkge1xuICAgICAgICAgICAgICAgICAgICByZXMuYWRkVHlwZSh0eXBlcy5QcmltQm9vbGVhbik7XG4gICAgICAgICAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgcmVzLmFkZFR5cGUodHlwZXMuUHJpbU51bWJlcik7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgfVxuICAgICAgICAgICAgcmV0dXJuIHJlcztcbiAgICAgICAgfSxcblxuICAgICAgICBGb3JTdGF0ZW1lbnQ6IGZ1bmN0aW9uIChub2RlLCBjdXJTdGF0dXMsIGMpIHtcbiAgICAgICAgICAgIGlmIChub2RlWydAYmxvY2snXSkge1xuICAgICAgICAgICAgICAgIC8vIGlmIGl0IGhhcyBAYmxvY2sgcHJvcGVydHlcbiAgICAgICAgICAgICAgICBjb25zdCBmb3JCbG9ja1NDID1cbiAgICAgICAgICAgICAgICAgICAgbm9kZVsnQGJsb2NrJ10uZ2V0U2NvcGVJbnN0YW5jZShjdXJTdGF0dXMuc2MsIGN1clN0YXR1cy5kZWx0YSk7XG4gICAgICAgICAgICAgICAgY3VyU3RhdHVzID0gY3VyU3RhdHVzLmdldE5ld1N0YXR1cyh7c2M6IGZvckJsb2NrU0N9KTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIHdhbGsuYmFzZS5Gb3JTdGF0ZW1lbnQobm9kZSwgY3VyU3RhdHVzLCBjKTtcbiAgICAgICAgfSxcblxuICAgICAgICBCbG9ja1N0YXRlbWVudDogZnVuY3Rpb24gKG5vZGUsIGN1clN0YXR1cywgYykge1xuICAgICAgICAgICAgaWYgKG5vZGVbJ0BibG9jayddKSB7XG4gICAgICAgICAgICAgICAgLy8gaWYgaXQgaGFzIEBibG9jayBwcm9wZXJ0eVxuICAgICAgICAgICAgICAgIGNvbnN0IG5vcm1hbEJsb2NrU0MgPVxuICAgICAgICAgICAgICAgICAgICBub2RlWydAYmxvY2snXS5nZXRTY29wZUluc3RhbmNlKGN1clN0YXR1cy5zYywgY3VyU3RhdHVzLmRlbHRhKTtcbiAgICAgICAgICAgICAgICBjdXJTdGF0dXMgPSBjdXJTdGF0dXMuZ2V0TmV3U3RhdHVzKHtzYzogbm9ybWFsQmxvY2tTQ30pO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgd2Fsay5iYXNlLkJsb2NrU3RhdGVtZW50KG5vZGUsIGN1clN0YXR1cywgYyk7XG4gICAgICAgIH0sXG5cbiAgICAgICAgVHJ5U3RhdGVtZW50OiBmdW5jdGlvbiAobm9kZSwgY3VyU3RhdHVzLCBjKSB7XG4gICAgICAgICAgICAvLyBjb25zdHJ1Y3Qgc2NvcGUgY2hhaW4gZm9yIGNhdGNoIGJsb2NrXG4gICAgICAgICAgICBjb25zdCBjYXRjaEJsb2NrU0MgPVxuICAgICAgICAgICAgICAgIG5vZGUuaGFuZGxlci5ib2R5WydAYmxvY2snXVxuICAgICAgICAgICAgICAgIC5nZXRTY29wZUluc3RhbmNlKGN1clN0YXR1cy5zYywgY3VyU3RhdHVzLmRlbHRhKTtcbiAgICAgICAgICAgIC8vIGdldCB0aGUgQVZhbCBmb3IgZXhjZXB0aW9uIHBhcmFtZXRlclxuICAgICAgICAgICAgY29uc3QgZXhjQVZhbCA9IGNhdGNoQmxvY2tTQy5nZXRBVmFsT2Yobm9kZS5oYW5kbGVyLnBhcmFtLm5hbWUpO1xuXG4gICAgICAgICAgICAvLyBmb3IgdHJ5IGJsb2NrXG4gICAgICAgICAgICBjb25zdCB0cnlTdGF0dXMgPSBjdXJTdGF0dXMuZ2V0TmV3U3RhdHVzKHtleGM6IGV4Y0FWYWx9KTtcbiAgICAgICAgICAgIGMobm9kZS5ibG9jaywgdHJ5U3RhdHVzLCB1bmRlZmluZWQpO1xuXG4gICAgICAgICAgICAvLyBmb3IgY2F0Y2ggYmxvY2tcbiAgICAgICAgICAgIGNvbnN0IGNhdGNoU3RhdHVzID0gY3VyU3RhdHVzLmdldE5ld1N0YXR1cyh7c2M6IGNhdGNoQmxvY2tTQ30pO1xuICAgICAgICAgICAgYyhub2RlLmhhbmRsZXIuYm9keSwgY2F0Y2hTdGF0dXMsIHVuZGVmaW5lZCk7XG5cbiAgICAgICAgICAgIC8vIGZvciBmaW5hbGx5IGJsb2NrXG4gICAgICAgICAgICBpZiAobm9kZS5maW5hbGl6ZXIgIT09IG51bGwpXG4gICAgICAgICAgICAgICAgYyhub2RlLmZpbmFsaXplciwgY3VyU3RhdHVzLCB1bmRlZmluZWQpO1xuICAgICAgICB9LFxuXG4gICAgICAgIFRocm93U3RhdGVtZW50OiBmdW5jdGlvbiAobm9kZSwgY3VyU3RhdHVzLCBjKSB7XG4gICAgICAgICAgICBjb25zdCB0aHIgPSBjKG5vZGUuYXJndW1lbnQsIGN1clN0YXR1cywgdW5kZWZpbmVkKTtcbiAgICAgICAgICAgIHRoci5wcm9wYWdhdGUoY3VyU3RhdHVzLmV4Yyk7XG4gICAgICAgIH0sXG5cbiAgICAgICAgQ2FsbEV4cHJlc3Npb246IGZ1bmN0aW9uIChub2RlLCBjdXJTdGF0dXMsIGMpIHtcbiAgICAgICAgICAgIGNvbnN0IHJlc0FWYWwgPSDEiC5nZXQobm9kZSwgY3VyU3RhdHVzLmRlbHRhKTtcbiAgICAgICAgICAgIGNvbnN0IGFyZ0FWYWxzID0gW107XG5cbiAgICAgICAgICAgIC8vIGdldCBBVmFscyBmb3IgZWFjaCBhcmd1bWVudHNcbiAgICAgICAgICAgIGZvciAobGV0IGkgPSAwOyBpIDwgbm9kZS5hcmd1bWVudHMubGVuZ3RoOyBpKyspIHtcbiAgICAgICAgICAgICAgICBhcmdBVmFscy5wdXNoKFxuICAgICAgICAgICAgICAgICAgICBjKG5vZGUuYXJndW1lbnRzW2ldLCBjdXJTdGF0dXMsIHVuZGVmaW5lZCkpO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgLy8gYXBwZW5kIGN1cnJlbnQgY2FsbCBzaXRlIHRvIHRoZSBjb250ZXh0XG4gICAgICAgICAgICBjb25zdCBuZXdEZWx0YSA9IGN1clN0YXR1cy5kZWx0YS5hcHBlbmRPbmUobm9kZVsnQGxhYmVsJ10pO1xuXG4gICAgICAgICAgICBpZiAobm9kZS5jYWxsZWUudHlwZSA9PT0gJ01lbWJlckV4cHJlc3Npb24nKSB7XG4gICAgICAgICAgICAgICAgLy8gbWV0aG9kIGNhbGxcbiAgICAgICAgICAgICAgICBjb25zdCBbcmVjdkFWYWwsIHJldEFWYWxdID0gcmVhZE1lbWJlcihub2RlLmNhbGxlZSwgY3VyU3RhdHVzLCBjKTtcbiAgICAgICAgICAgICAgICByZXRBVmFsLnByb3BhZ2F0ZShcbiAgICAgICAgICAgICAgICAgICAgbmV3IGNzdHIuSXNDYWxsZWUoXG4gICAgICAgICAgICAgICAgICAgICAgICByZWN2QVZhbCxcbiAgICAgICAgICAgICAgICAgICAgICAgIGFyZ0FWYWxzLFxuICAgICAgICAgICAgICAgICAgICAgICAgcmVzQVZhbCxcbiAgICAgICAgICAgICAgICAgICAgICAgIGN1clN0YXR1cy5leGMsXG4gICAgICAgICAgICAgICAgICAgICAgICBuZXdEZWx0YSkpO1xuICAgICAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICAgICAgICAvLyBub3JtYWwgZnVuY3Rpb24gY2FsbFxuICAgICAgICAgICAgICAgIGNvbnN0IGNhbGxlZUFWYWwgPSBjKG5vZGUuY2FsbGVlLCBjdXJTdGF0dXMsIHVuZGVmaW5lZCk7XG4gICAgICAgICAgICAgICAgLy8gY2FsbGVl7J2YIHJldHVybuydhCBjYWxsIGV4cHJlc3Npb27snLzroZxcbiAgICAgICAgICAgICAgICAvLyBjYWxsZWXsnZggZXhjZXB0aW9u7J2EIO2YuOy2nCDsuKHsnZggZXhjZXB0aW9u7JeQIOyghOuLrO2VtOyVvFxuICAgICAgICAgICAgICAgIGNhbGxlZUFWYWwucHJvcGFnYXRlKFxuICAgICAgICAgICAgICAgICAgICBuZXcgY3N0ci5Jc0NhbGxlZShcbiAgICAgICAgICAgICAgICAgICAgICAgIG5ldyB0eXBlcy5BVmFsKHJ0Q1guZ2xvYmFsT2JqZWN0KSxcbiAgICAgICAgICAgICAgICAgICAgICAgIGFyZ0FWYWxzLFxuICAgICAgICAgICAgICAgICAgICAgICAgcmVzQVZhbCxcbiAgICAgICAgICAgICAgICAgICAgICAgIGN1clN0YXR1cy5leGMsXG4gICAgICAgICAgICAgICAgICAgICAgICBuZXdEZWx0YSkpO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgcmV0dXJuIHJlc0FWYWw7XG4gICAgICAgIH0sXG5cbiAgICAgICAgTWVtYmVyRXhwcmVzc2lvbjogZnVuY3Rpb24gKG5vZGUsIGN1clN0YXR1cywgYykge1xuICAgICAgICAgICAgY29uc3QgWywgcmV0QVZhbF0gPSByZWFkTWVtYmVyKG5vZGUsIGN1clN0YXR1cywgYyk7XG4gICAgICAgICAgICByZXR1cm4gcmV0QVZhbDtcbiAgICAgICAgfSxcblxuICAgICAgICBSZXR1cm5TdGF0ZW1lbnQ6IGZ1bmN0aW9uIChub2RlLCBjdXJTdGF0dXMsIGMpIHtcbiAgICAgICAgICAgIGlmICghbm9kZS5hcmd1bWVudCkgcmV0dXJuO1xuICAgICAgICAgICAgY29uc3QgcmV0ID0gYyhub2RlLmFyZ3VtZW50LCBjdXJTdGF0dXMsIHVuZGVmaW5lZCk7XG4gICAgICAgICAgICByZXQucHJvcGFnYXRlKGN1clN0YXR1cy5yZXQpO1xuICAgICAgICB9XG4gICAgfSk7XG5cbiAgICBjb25zdCBvdXRBVmFsID0gbXlXYWxrZXIucmVjdXJzaXZlV2l0aFJldHVybihhc3ROb2RlLCBpbml0U3RhdHVzLCBjb25zdHJhaW50R2VuZXJhdG9yKTtcbiAgICBpZiAob3V0QVZhbCkge1xuICAgICAgICAvLyBtdXN0IGJlIGFuIGV4cHJlc3Npb24gYm9keVxuICAgICAgICBvdXRBVmFsLnByb3BhZ2F0ZShpbml0U3RhdHVzLnJldCk7XG4gICAgfVxuICAgIC8vIFdlIGFjdHVhbGx5IGFkZGVkIGNvbnN0cmFpbnRzXG4gICAgcmV0dXJuIHRydWU7XG59XG5cbmV4cG9ydHMuYWRkQ29uc3RyYWludHMgPSBhZGRDb25zdHJhaW50cztcbmV4cG9ydHMuY2xlYXJDb25zdHJhaW50cyA9IGNsZWFyQ29uc3RyYWludHM7XG4iLCIndXNlIHN0cmljdCc7XG5cbmltcG9ydCAqIGFzIHR5cGVzIGZyb20gJy4uL2RvbWFpbnMvdHlwZXMnXG5pbXBvcnQgKiBhcyBzdGF0dXMgZnJvbSAnLi4vZG9tYWlucy9zdGF0dXMnXG5pbXBvcnQgKiBhcyBjc2MgZnJvbSAnLi4vZG9tYWlucy9jb250ZXh0J1xuY29uc3QgY0dlbiA9IHJlcXVpcmUoJy4vY0dlbicpO1xuXG5mdW5jdGlvbiBDU1RSKCkge31cbkNTVFIucHJvdG90eXBlID0gT2JqZWN0LmNyZWF0ZShudWxsKTtcbkNTVFIucHJvdG90eXBlLmVxdWFscyA9IGZ1bmN0aW9uIChvdGhlcikge1xuICAgIHJldHVybiB0aGlzID09PSBvdGhlcjtcbn07XG5cbmZ1bmN0aW9uIFJlYWRQcm9wKHByb3AsIHRvKSB7XG4gICAgdGhpcy5wcm9wID0gcHJvcDtcbiAgICB0aGlzLnRvID0gdG87XG59XG5SZWFkUHJvcC5wcm90b3R5cGUgPSBPYmplY3QuY3JlYXRlKENTVFIucHJvdG90eXBlKTtcblJlYWRQcm9wLnByb3RvdHlwZS5hZGRUeXBlID0gZnVuY3Rpb24gKG9iaikge1xuICAgIGlmICghKG9iaiBpbnN0YW5jZW9mICh0eXBlcy5PYmpUeXBlKSkpIHJldHVybjtcbiAgICAvLyB3aGVuIG9iaiBpcyBPYmpUeXBlLFxuICAgIGNvbnN0IG93blByb3AgPSBvYmouZ2V0UHJvcCh0aGlzLnByb3AsIHRydWUpO1xuICAgIGlmIChvd25Qcm9wKSB7XG4gICAgICAgIC8vIHdoZW4gdGhlIG9iamVjdCBoYXMgdGhlIHByb3AsXG4gICAgICAgIG93blByb3AucHJvcGFnYXRlKHRoaXMudG8pO1xuICAgIH0gZWxzZSBpZiAob2JqLmdldFByb3AoJ19fcHJvdG9fXycsIHRydWUpKSB7XG4gICAgICAgIC8vIFByb3BhZ2F0ZSBmcm9tIHVua25vd24gcHJvcCBpZiBvYmogaGFzIGl0LlxuICAgICAgICBpZiAob2JqLmhhc1Byb3AobnVsbCkpIHtcbiAgICAgICAgICAgIG9iai5nZXRQcm9wKG51bGwsIHRydWUpLnByb3BhZ2F0ZSh0aGlzLnRvKTtcbiAgICAgICAgfVxuICAgICAgICAvLyB1c2UgcHJvdG90eXBlIGNoYWluXG4gICAgICAgIG9iai5nZXRQcm9wKCdfX3Byb3RvX18nKVxuICAgICAgICAgIC5wcm9wYWdhdGUobmV3IFJlYWRQcm9wKHRoaXMucHJvcCwgdGhpcy50bykpO1xuICAgIH1cbn07XG5SZWFkUHJvcC5wcm90b3R5cGUuZXF1YWxzID0gZnVuY3Rpb24gKG90aGVyKSB7XG4gICAgaWYgKCEob3RoZXIgaW5zdGFuY2VvZiBSZWFkUHJvcCkpIHJldHVybiBmYWxzZTtcbiAgICByZXR1cm4gdGhpcy5wcm9wID09PSBvdGhlci5wcm9wXG4gICAgICAgICYmIHRoaXMudG8uZXF1YWxzKG90aGVyLnRvKTtcbn07XG5cbmZ1bmN0aW9uIFdyaXRlUHJvcChwcm9wLCBmcm9tKSB7XG4gICAgdGhpcy5wcm9wID0gcHJvcDtcbiAgICB0aGlzLmZyb20gPSBmcm9tO1xufVxuV3JpdGVQcm9wLnByb3RvdHlwZSA9IE9iamVjdC5jcmVhdGUoQ1NUUi5wcm90b3R5cGUpO1xuV3JpdGVQcm9wLnByb3RvdHlwZS5hZGRUeXBlID0gZnVuY3Rpb24gKG9iaikge1xuICAgIGlmICghKG9iaiBpbnN0YW5jZW9mICh0eXBlcy5PYmpUeXBlKSkpIHJldHVybjtcbiAgICBjb25zdCBvd25Qcm9wID0gb2JqLmdldFByb3AodGhpcy5wcm9wKTtcbiAgICB0aGlzLmZyb20ucHJvcGFnYXRlKG93blByb3ApO1xuICAgIC8vIEhhbmRsZSAncHJvdG90eXBlT2YnIHdoZW4gd3JpdGluZyB0byAncHJvdG90eXBlJ1xuICAgIGlmICh0aGlzLnByb3AgPT09ICdwcm90b3R5cGUnKSB7XG4gICAgICAgIHRoaXMuZnJvbS5nZXRUeXBlcygpLmZvckVhY2goKHRwKSA9PiB7XG4gICAgICAgICAgICB0cC5wcm90b3R5cGVPZi5hZGRUeXBlKG9iaik7XG4gICAgICAgIH0pO1xuICAgIH1cbiAgICAvLyBXaGVuIGFzc2lnbmluZyBGblR5cGUgdG8gYSBwcm9wLFxuICAgIHRoaXMuZnJvbS5nZXRUeXBlcygpLmZvckVhY2goKGZuKSA9PiB7XG4gICAgICAgIGlmICghKGZuIGluc3RhbmNlb2YgKHR5cGVzLkZuVHlwZSkpKSByZXR1cm47XG4gICAgICAgIC8vIG9iaidzIHByb3RvdHlwZU9mID0+IHNlbGZBVmFsIG9mIG51bGwgY29udGV4dFxuICAgICAgICBjb25zdCBbc2VsZkFWYWwsLF0gPSBmbi5nZXRGdW5FbnYoY3NjLkNhbGxTaXRlQ29udGV4dC5udWxsQ29udGV4dCk7XG4gICAgICAgIG9iai5wcm90b3R5cGVPZi5nZXRUeXBlcygpLmZvckVhY2goKGN0b3IpID0+IHtcbiAgICAgICAgICAgIGlmIChjdG9yIGluc3RhbmNlb2YgKHR5cGVzLkZuVHlwZSkpXG4gICAgICAgICAgICAgICAgc2VsZkFWYWwuYWRkVHlwZShjdG9yLmdldEluc3RhbmNlKCkpO1xuICAgICAgICB9KTtcbiAgICB9KTtcbn07XG5cbmZ1bmN0aW9uIElzQWRkZWQob3RoZXIsIHRhcmdldCkge1xuICAgIHRoaXMub3RoZXIgPSBvdGhlcjtcbiAgICB0aGlzLnRhcmdldCA9IHRhcmdldDtcbn1cbklzQWRkZWQucHJvdG90eXBlID0gT2JqZWN0LmNyZWF0ZShDU1RSLnByb3RvdHlwZSk7XG5Jc0FkZGVkLnByb3RvdHlwZS5hZGRUeXBlID0gZnVuY3Rpb24gKHR5cGUpIHtcbiAgICBpZiAoKHR5cGUgPT09IHR5cGVzLlByaW1OdW1iZXIgXG4gICAgICAgICB8fCB0eXBlID09PSB0eXBlcy5QcmltQm9vbGVhbilcbiAgICAgJiYgKHRoaXMub3RoZXIuaGFzVHlwZSh0eXBlcy5QcmltTnVtYmVyKSBcbiAgICAgICAgIHx8IHRoaXMub3RoZXIuaGFzVHlwZSh0eXBlcy5QcmltQm9vbGVhbikpKSB7XG4gICAgICAgIHRoaXMudGFyZ2V0LmFkZFR5cGUodHlwZXMuUHJpbU51bWJlcik7XG4gICAgfVxuICAgIGlmICh0eXBlID09PSB0eXBlcy5QcmltU3RyaW5nXG4gICAgICYmICF0aGlzLm90aGVyLmlzRW1wdHkoKSkge1xuICAgICAgICAgdGhpcy50YXJnZXQuYWRkVHlwZSh0eXBlcy5QcmltU3RyaW5nKTtcbiAgICB9XG59O1xuXG5mdW5jdGlvbiBJc0NhbGxlZShzZWxmLCBhcmdzLCByZXQsIGV4YywgZGVsdGEpIHtcbiAgICB0aGlzLnNlbGYgPSBzZWxmO1xuICAgIHRoaXMuYXJncyA9IGFyZ3M7XG4gICAgdGhpcy5yZXQgPSByZXQ7XG4gICAgdGhpcy5leGMgPSBleGM7XG4gICAgdGhpcy5kZWx0YSA9IGRlbHRhO1xufVxuSXNDYWxsZWUucHJvdG90eXBlID0gT2JqZWN0LmNyZWF0ZShDU1RSLnByb3RvdHlwZSk7XG5Jc0NhbGxlZS5wcm90b3R5cGUuYWRkVHlwZSA9IGZ1bmN0aW9uIChmKSB7XG4gICAgaWYgKCEoZiBpbnN0YW5jZW9mICh0eXBlcy5GblR5cGUpKSkgcmV0dXJuO1xuICAgIGNvbnN0IGRlbHRhRm4gPSB0aGlzLmRlbHRhLnRydW5jYXRlRm9yKGYpO1xuICAgIGNvbnN0IFtzZWxmQVZhbCwgcmV0QVZhbCwgZXhjQVZhbF0gPSBmLmdldEZ1bkVudihkZWx0YUZuKTtcbiAgICBjb25zdCBuZXdTQyA9IGYub3JpZ2luTm9kZS5ib2R5WydAYmxvY2snXS5nZXRTY29wZUluc3RhbmNlKGYuc2MsIGRlbHRhRm4pO1xuICAgIGNvbnN0IGZ1blN0YXR1c1xuICAgICAgICA9IG5ldyBzdGF0dXMuU3RhdHVzKHNlbGZBVmFsLCByZXRBVmFsLCBleGNBVmFsLFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIGRlbHRhRm4sIG5ld1NDKTtcblxuICAgIC8vIGFycm93IGZ1bmN0aW9uIHNob3VsZCB1c2UgYm91bmRUaGlzIGFuZCBpZ25vcmUgdGhlIHJlY2VpdmVyIEFWYWxcbiAgICBpZiAoZi5ib3VuZFRoaXMpIHtcbiAgICAgICAgZi5ib3VuZFRoaXMucHJvcGFnYXRlKHNlbGZBVmFsKTtcbiAgICB9IGVsc2Uge1xuICAgICAgICB0aGlzLnNlbGYucHJvcGFnYXRlKHNlbGZBVmFsKTtcbiAgICB9XG5cbiAgICBjb25zdCBtaW5MZW4gPSBNYXRoLm1pbih0aGlzLmFyZ3MubGVuZ3RoLCBmLnBhcmFtTmFtZXMubGVuZ3RoKTtcbiAgICBmb3IgKGxldCBpID0gMDsgaSA8IG1pbkxlbjsgaSsrKSB7XG4gICAgICAgIHRoaXMuYXJnc1tpXS5wcm9wYWdhdGUobmV3U0MuZ2V0QVZhbE9mKGYucGFyYW1OYW1lc1tpXSkpO1xuICAgIH1cblxuICAgIC8vIGZvciBhcmd1bWVudHMgb2JqZWN0XG4gICAgaWYgKGYub3JpZ2luTm9kZS5ib2R5WydAYmxvY2snXS51c2VBcmd1bWVudHNPYmplY3QpIHtcbiAgICAgICAgY29uc3QgYXJnT2JqID0gZi5nZXRBcmd1bWVudHNPYmplY3QoZGVsdGFGbik7XG4gICAgICAgIG5ld1NDLmdldEFWYWxPZignYXJndW1lbnRzJykuYWRkVHlwZShhcmdPYmopO1xuICAgICAgICBmb3IgKGxldCBpID0gMDsgaSA8IHRoaXMuYXJncy5sZW5ndGg7IGkrKykge1xuICAgICAgICAgICAgdGhpcy5hcmdzW2ldLnByb3BhZ2F0ZShhcmdPYmouZ2V0UHJvcChpICsgJycpKTtcbiAgICAgICAgICAgIHRoaXMuYXJnc1tpXS5wcm9wYWdhdGUoYXJnT2JqLmdldFByb3AobnVsbCkpO1xuICAgICAgICB9XG4gICAgICAgIGFyZ09iai5nZXRQcm9wKCdjYWxsZWUnKS5hZGRUeXBlKGYpO1xuICAgICAgICBhcmdPYmouZ2V0UHJvcCgnbGVuZ3RoJykuYWRkVHlwZSh0eXBlcy5QcmltTnVtYmVyKTtcbiAgICB9XG5cbiAgICAvLyBjb25zdHJhaW50IGdlbmVyYXRpb24gZm9yIHRoZSBmdW5jdGlvbiBib2R5XG4gICAgY0dlbi5hZGRDb25zdHJhaW50cyhmLm9yaWdpbk5vZGUuYm9keSwgZnVuU3RhdHVzKTtcblxuICAgIC8vIGdldCByZXR1cm5cbiAgICByZXRBVmFsLnByb3BhZ2F0ZSh0aGlzLnJldCk7XG4gICAgLy8gZ2V0IGV4Y2VwdGlvblxuICAgIGV4Y0FWYWwucHJvcGFnYXRlKHRoaXMuZXhjKTtcbn07XG5cbmZ1bmN0aW9uIElzQ3RvcihhcmdzLCByZXQsIGV4YywgZGVsdGEpIHtcbiAgICB0aGlzLmFyZ3MgPSBhcmdzO1xuICAgIHRoaXMucmV0ID0gcmV0O1xuICAgIHRoaXMuZXhjID0gZXhjO1xuICAgIHRoaXMuZGVsdGEgPSBkZWx0YTtcbn1cbklzQ3Rvci5wcm90b3R5cGUgPSBPYmplY3QuY3JlYXRlKENTVFIucHJvdG90eXBlKTtcbklzQ3Rvci5wcm90b3R5cGUuYWRkVHlwZSA9IGZ1bmN0aW9uIChmKSB7XG4gICAgLy8gT25seSBub24tYXJyb3cgZnVuY3Rpb25zIGNhbiBjcmVhdGUgaW5zdGFuY2VzLlxuICAgIGlmICghKGYgaW5zdGFuY2VvZiAodHlwZXMuRm5UeXBlKSkgfHwgZi5ib3VuZFRoaXMpIHtcbiAgICAgICAgcmV0dXJuO1xuICAgIH1cbiAgICBjb25zdCBkZWx0YUZuID0gdGhpcy5kZWx0YS50cnVuY2F0ZUZvcihmKTtcbiAgICBjb25zdCBbc2VsZkFWYWwsIHJldEFWYWwsIGV4Y0FWYWxdID0gZi5nZXRGdW5FbnYoZGVsdGFGbik7XG4gICAgY29uc3QgbmV3U0MgPSBmLm9yaWdpbk5vZGUuYm9keVsnQGJsb2NrJ10uZ2V0U2NvcGVJbnN0YW5jZShmLnNjLCBkZWx0YUZuKTtcbiAgICBjb25zdCBmdW5TdGF0dXNcbiAgICAgICAgPSBuZXcgc3RhdHVzLlN0YXR1cyhcbiAgICAgICAgICAgIHNlbGZBVmFsLFxuICAgICAgICAgICAgLy8gSW4gY29uc3RydWN0b3IsIHdlIGNhbiBleHBsaWNpdGx5IHJldHVybiBvbmx5IE9ialR5cGUuXG4gICAgICAgICAgICBuZXcgSWZPYmpUeXBlKHJldEFWYWwpLFxuICAgICAgICAgICAgZXhjQVZhbCxcbiAgICAgICAgICAgIGRlbHRhRm4sXG4gICAgICAgICAgICBuZXdTQyk7XG4gICAgLy8gZidzIGluc3RhbmNlIGlzIGJvdW5kIHRvICd0aGlzLidcbiAgICBjb25zdCBuZXdPYmogPSBmLmdldEluc3RhbmNlKCk7XG4gICAgc2VsZkFWYWwuYWRkVHlwZShuZXdPYmopO1xuXG4gICAgY29uc3QgbWluTGVuID0gTWF0aC5taW4odGhpcy5hcmdzLmxlbmd0aCwgZi5wYXJhbU5hbWVzLmxlbmd0aCk7XG4gICAgZm9yIChsZXQgaSA9IDA7IGkgPCBtaW5MZW47IGkrKykge1xuICAgICAgICB0aGlzLmFyZ3NbaV0ucHJvcGFnYXRlKG5ld1NDLmdldEFWYWxPZihmLnBhcmFtTmFtZXNbaV0pKTtcbiAgICB9XG5cbiAgICAvLyBmb3IgYXJndW1lbnRzIG9iamVjdFxuICAgIGlmIChmLm9yaWdpbk5vZGUuYm9keVsnQGJsb2NrJ10udXNlQXJndW1lbnRzT2JqZWN0KSB7XG4gICAgICAgIGNvbnN0IGFyZ09iaiA9IGYuZ2V0QXJndW1lbnRzT2JqZWN0KGRlbHRhRm4pO1xuICAgICAgICBuZXdTQy5nZXRBVmFsT2YoJ2FyZ3VtZW50cycpLmFkZFR5cGUoYXJnT2JqKTtcbiAgICAgICAgZm9yIChsZXQgaSA9IDA7IGkgPCB0aGlzLmFyZ3MubGVuZ3RoOyBpKyspIHtcbiAgICAgICAgICAgIHRoaXMuYXJnc1tpXS5wcm9wYWdhdGUoYXJnT2JqLmdldFByb3AoaSArICcnKSk7XG4gICAgICAgICAgICB0aGlzLmFyZ3NbaV0ucHJvcGFnYXRlKGFyZ09iai5nZXRQcm9wKG51bGwpKTtcbiAgICAgICAgfVxuICAgICAgICBhcmdPYmouZ2V0UHJvcCgnY2FsbGVlJykuYWRkVHlwZShmKTtcbiAgICAgICAgYXJnT2JqLmdldFByb3AoJ2xlbmd0aCcpLmFkZFR5cGUodHlwZXMuUHJpbU51bWJlcik7XG4gICAgfVxuXG4gICAgLy8gY29uc3RyYWludCBnZW5lcmF0aW9uIGZvciB0aGUgZnVuY3Rpb24gYm9keVxuICAgIGNHZW4uYWRkQ29uc3RyYWludHMoZi5vcmlnaW5Ob2RlLmJvZHksIGZ1blN0YXR1cyk7XG5cbiAgICAvLyBwcm92aWRlIHR3byBraW5kcyBvZiByZXN1bHQgb2YgJ25ldydcbiAgICB0aGlzLnJldC5hZGRUeXBlKG5ld09iaik7XG4gICAgcmV0QVZhbC5wcm9wYWdhdGUodGhpcy5yZXQpO1xuICAgIC8vIGdldCBleGNlcHRpb25cbiAgICBleGNBVmFsLnByb3BhZ2F0ZSh0aGlzLmV4Yyk7XG59O1xuXG4vLyBpZ25vcmUgbm9uIG9iamVjdCB0eXBlc1xuZnVuY3Rpb24gSWZPYmpUeXBlKGF2YWwpIHtcbiAgICB0aGlzLmF2YWwgPSBhdmFsO1xufVxuSWZPYmpUeXBlLnByb3RvdHlwZSA9IE9iamVjdC5jcmVhdGUoQ1NUUi5wcm90b3R5cGUpO1xuSWZPYmpUeXBlLnByb3RvdHlwZS5hZGRUeXBlID0gZnVuY3Rpb24gKHR5cGUpIHtcbiAgICBpZiAoISh0eXBlIGluc3RhbmNlb2YgdHlwZXMuT2JqVHlwZSkpIHJldHVybjtcbiAgICB0aGlzLmF2YWwuYWRkVHlwZSh0eXBlKTtcbn07XG5cbmV4cG9ydHMuUmVhZFByb3AgPSBSZWFkUHJvcDtcbmV4cG9ydHMuV3JpdGVQcm9wID0gV3JpdGVQcm9wO1xuZXhwb3J0cy5Jc0FkZGVkID0gSXNBZGRlZDtcbmV4cG9ydHMuSXNDYWxsZWUgPSBJc0NhbGxlZTtcbmV4cG9ydHMuSXNDdG9yID0gSXNDdG9yO1xuIiwiLy8gQ29udGV4dCBmb3Igay1DRkEgYW5hbHlzaXNcbi8vXG4vLyBBc3N1bWUgYSBjb250ZXh0IGlzIGFuIGFycmF5IG9mIG51bWJlcnMuXG4vLyBBIG51bWJlciBpbiBzdWNoIGxpc3QgZGVub3RlcyBhIGNhbGwgc2l0ZSwgdGhhdCBpcyBAbGFiZWwgb2YgYSBDYWxsRXhwcmVzc2lvbi5cbi8vIFdlIGtlZXAgdGhlIG1vc3QgcmVjZW50ICdrJyBjYWxsLXNpdGVzLlxuLy8gRXF1YWxpdHkgb24gY29udGV4dHMgc2hvdWxkIGxvb2sgaW50byB0aGUgbnVtYmVycy5cblxuZXhwb3J0IGNvbnN0IHNlbnNpdGl2aXR5UGFyYW1ldGVyID0ge1xuICAgIC8vIG1heGltdW0gbGVuZ3RoIG9mIGNvbnRleHRcbiAgICBtYXhEZXB0aEs6IDAsXG4gICAgLy9cbiAgICBjb250ZXh0TGVuZ3RoT2ZGdW5jOiBmdW5jdGlvbiAoZm4pIHtcbiAgICAgICAgcmV0dXJuIDA7XG4gICAgfVxufTtcblxuZXhwb3J0IGZ1bmN0aW9uIGNoYW5nZVNlbnNpdGl2aXR5UGFyYW1ldGVyKHBhcmFtKSB7XG4gICAgc2Vuc2l0aXZpdHlQYXJhbWV0ZXIubWF4RGVwdGhLID0gcGFyYW0ubWF4RGVwdGhLO1xuICAgIHNlbnNpdGl2aXR5UGFyYW1ldGVyLmNvbnRleHRMZW5ndGhPZkZ1bmMgPSBwYXJhbS5jb250ZXh0TGVuZ3RoT2ZGdW5jO1xufVxuXG4vLyBGdW5jdGlvbmFsIG9iamVjdHMgZm9yIGNhbGwtc2l0ZSBjb250ZXh0XG5leHBvcnQgY2xhc3MgQ2FsbFNpdGVDb250ZXh0IHtcblxuICAgIGNvbnN0cnVjdG9yKGxpc3QpIHtcbiAgICAgICAgZm9yIChsZXQgY3R4IG9mIENhbGxTaXRlQ29udGV4dC5jb250ZXh0UG9vbC52YWx1ZXMoKSkge1xuICAgICAgICAgICAgaWYgKGN0eC5faGFzU2FtZUxpc3QobGlzdCkpIHtcbiAgICAgICAgICAgICAgICAvLyB1c2UgZXhpc3RpbmcgY29udGV4dFxuICAgICAgICAgICAgICAgIHJldHVybiBjdHg7XG4gICAgICAgICAgICB9XG4gICAgICAgIH1cbiAgICAgICAgLy8gY2xvbmUgdGhlIGdpdmVuIGxpc3RcbiAgICAgICAgaWYgKGxpc3QgPT09IG51bGwpIHtcbiAgICAgICAgICAgIHRoaXMuY3NMaXN0ID0gbnVsbDtcbiAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICAgIHRoaXMuY3NMaXN0ID0gbGlzdC5zbGljZSgwKTtcbiAgICAgICAgfVxuICAgICAgICAvLyBhZGQgdGhlIGN1cnJlbnQgaW5zdGFuY2UgdG8gdGhlIHBvb2xcbiAgICAgICAgQ2FsbFNpdGVDb250ZXh0LmNvbnRleHRQb29sLmFkZCh0aGlzKTtcbiAgICB9XG5cbiAgICAvKipcbiAgICAgKiBBIHByaXZhdGUgbWV0aG9kIGZvciBjb250ZXh0IGVxdWFsaXR5XG4gICAgICogQHBhcmFtIGxpc3QgLSBhcnJheSBjb21wb3NlZCBvZiBjb250ZXh0IGVsZW1lbnRzXG4gICAgICogQHJldHVybnMge2Jvb2xlYW59XG4gICAgICovXG4gICAgX2hhc1NhbWVMaXN0KGxpc3QpIHtcbiAgICAgICAgaWYgKHRoaXMuY3NMaXN0ID09PSBudWxsKSB7XG4gICAgICAgICAgICByZXR1cm4gbGlzdCA9PT0gbnVsbDtcbiAgICAgICAgfVxuICAgICAgICBpZiAobGlzdCA9PT0gbnVsbCkge1xuICAgICAgICAgICAgcmV0dXJuIHRoaXMuY3NMaXN0ID09PSBudWxsO1xuICAgICAgICB9XG4gICAgICAgIGlmICh0aGlzLmNzTGlzdC5sZW5ndGggIT09IGxpc3QubGVuZ3RoKSB7XG4gICAgICAgICAgICByZXR1cm4gZmFsc2U7XG4gICAgICAgIH1cbiAgICAgICAgZm9yIChsZXQgaSA9IDA7IGkgPCB0aGlzLmNzTGlzdC5sZW5ndGg7IGkrKykge1xuICAgICAgICAgICAgaWYgKHRoaXMuY3NMaXN0W2ldICE9PSBsaXN0W2ldKSByZXR1cm4gZmFsc2U7XG4gICAgICAgIH1cbiAgICAgICAgcmV0dXJuIHRydWU7XG4gICAgfVxuXG4gICAgLyoqXG4gICAgICogUmV0dXJuIHRoZSBjb250ZXh0IHdoaWNoIGlzIG15c2VsZiArIGNhbGxTaXRlLlxuICAgICAqIElmIEkgYW0gbnVsbENvbnRleHQsIHRoZSByZXN1bHQgaXMgbXlzZWxmLlxuICAgICAqIEBwYXJhbSBjYWxsU2l0ZSAtIGEgY2FsbC1zaXRlIHRvIGFwcGVuZFxuICAgICAqIEByZXR1cm5zIHtDYWxsU2l0ZUNvbnRleHR9XG4gICAgICovXG4gICAgYXBwZW5kT25lKGNhbGxTaXRlKSB7XG4gICAgICAgIC8vIGlmIG51bGwgY29udGV4dCwgcmVzdWx0IGlzIGl0c2VsZlxuICAgICAgICBpZiAodGhpcyA9PT0gQ2FsbFNpdGVDb250ZXh0Lm51bGxDb250ZXh0KSB7XG4gICAgICAgICAgICByZXR1cm4gdGhpcztcbiAgICAgICAgfVxuICAgICAgICAvLyB1c2UgY29uY2F0IHRvIGNyZWF0ZSBhIG5ldyBhcnJheVxuICAgICAgICAvLyBvbGRlc3Qgb25lIGNvbWVzIGZpcnN0XG4gICAgICAgIGNvbnN0IGFwcGVuZGVkID0gdGhpcy5jc0xpc3QuY29uY2F0KGNhbGxTaXRlKTtcbiAgICAgICAgaWYgKGFwcGVuZGVkLmxlbmd0aCA+IHNlbnNpdGl2aXR5UGFyYW1ldGVyLm1heERlcHRoSykge1xuICAgICAgICAgICAgYXBwZW5kZWQuc2hpZnQoKTtcbiAgICAgICAgfVxuICAgICAgICByZXR1cm4gbmV3IENhbGxTaXRlQ29udGV4dChhcHBlbmRlZCk7XG4gICAgfVxuXG4gICAgLyoqXG4gICAgICogVHJ1bmNhdGUgY29udGV4dCBhY2NvcmRpbmcgdG8gdGhlIGdpdmVuIGZ1bmN0aW9uLlxuICAgICAqIEBwYXJhbSB7Rm5UeXBlfSBmblxuICAgICAqIEByZXR1cm5zIHtDYWxsU2l0ZUNvbnRleHR9XG4gICAgICovXG4gICAgdHJ1bmNhdGVGb3IoZm4pIHtcbiAgICAgICAgLy8gZm9yIG51bGxDb250ZXh0LFxuICAgICAgICBpZiAodGhpcyA9PT0gQ2FsbFNpdGVDb250ZXh0Lm51bGxDb250ZXh0KSB7XG4gICAgICAgICAgICByZXR1cm4gdGhpcztcbiAgICAgICAgfVxuICAgICAgICAvLyBjb21wdXRlIHRoZSBsZW5ndGggb2YgdGhlIGNvbnRleHRcbiAgICAgICAgY29uc3QgY29udGV4dExlbmd0aCA9IHNlbnNpdGl2aXR5UGFyYW1ldGVyLmNvbnRleHRMZW5ndGhPZkZ1bmMoZm4pO1xuICAgICAgICBpZiAoY29udGV4dExlbmd0aCA9PT0gMCkge1xuICAgICAgICAgICAgLy8gY29udGV4dCBvZiBsZW5ndGggMFxuICAgICAgICAgICAgcmV0dXJuIENhbGxTaXRlQ29udGV4dC5lcHNpbG9uQ29udGV4dDtcbiAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICAgIC8vIGNob29zZSBsYXN0IHNldmVyYWwgY2FsbC1zaXRlc1xuICAgICAgICAgICAgcmV0dXJuIG5ldyBDYWxsU2l0ZUNvbnRleHQodGhpcy5jc0xpc3Quc2xpY2UoLWNvbnRleHRMZW5ndGgpKTtcbiAgICAgICAgfVxuICAgIH1cblxuICAgIHRvU3RyaW5nKCkge1xuICAgICAgICByZXR1cm4gdGhpcy5jc0xpc3QudG9TdHJpbmcoKTtcbiAgICB9XG59XG5cbi8vIERlY2xhcmluZyBjbGFzcyBmaWVsZHMgZm9yIENhbGxTaXRlQ29udGV4dFxuQ2FsbFNpdGVDb250ZXh0LmNvbnRleHRQb29sID0gbmV3IFNldCgpO1xuLy8gbnVsbENvbnRleHQgaXMgZm9yIGZ1bmN0aW9ucyB0aGF0IG5ldmVyIGJlIGNhbGxlZFxuQ2FsbFNpdGVDb250ZXh0Lm51bGxDb250ZXh0ID0gbmV3IENhbGxTaXRlQ29udGV4dChudWxsKTtcbi8vIGVwc2lsb25Db250ZXh0IGlzIGZvciBjb250ZXh0IG9mIGxlbmd0aCAwXG5DYWxsU2l0ZUNvbnRleHQuZXBzaWxvbkNvbnRleHQgPSBuZXcgQ2FsbFNpdGVDb250ZXh0KFtdKTtcbiIsIi8vIFN0YXR1czpcbi8vIHsgc2VsZiAgOiBBVmFsLFxuLy8gICByZXQgICA6IEFWYWwsXG4vLyAgIGV4YyAgIDogQVZhbCxcbi8vICAgZGVsdGEgOiBDb250ZXh0LFxuLy8gICBzYyAgICA6IFNjb3BlIH1cblxuZXhwb3J0IGNsYXNzIFN0YXR1cyB7XG4gICAgY29uc3RydWN0b3Ioc2VsZiwgcmV0LCBleGMsIGRlbHRhLCBzYykge1xuICAgICAgICB0aGlzLnNlbGYgPSBzZWxmO1xuICAgICAgICB0aGlzLnJldCA9IHJldDtcbiAgICAgICAgdGhpcy5leGMgPSBleGM7XG4gICAgICAgIHRoaXMuZGVsdGEgPSBkZWx0YTtcbiAgICAgICAgdGhpcy5zYyA9IHNjO1xuICAgIH1cblxuICAgIGVxdWFscyhvdGhlcikge1xuICAgICAgICByZXR1cm4gdGhpcy5zZWxmID09PSBvdGhlci5zZWxmICYmXG4gICAgICAgICAgICB0aGlzLnJldCA9PT0gb3RoZXIucmV0ICYmXG4gICAgICAgICAgICB0aGlzLmV4YyA9PT0gb3RoZXIuZXhjICYmXG4gICAgICAgICAgICB0aGlzLmRlbHRhID09PSBvdGhlci5kZWx0YSAmJlxuICAgICAgICAgICAgdGhpcy5zYyA9PT0gb3RoZXIuc2M7XG4gICAgfVxuXG4gICAgZ2V0TmV3U3RhdHVzKGNoYW5nZVN0YXR1cykge1xuICAgICAgICBjb25zdCBuZXdTdGF0dXMgPSBuZXcgU3RhdHVzO1xuICAgICAgICBmb3IgKGxldCBwIGluIHRoaXMpIHtcbiAgICAgICAgICAgIGlmICh0aGlzLmhhc093blByb3BlcnR5KHApKSB7XG4gICAgICAgICAgICAgICAgaWYgKGNoYW5nZVN0YXR1cy5oYXNPd25Qcm9wZXJ0eShwKSkge1xuICAgICAgICAgICAgICAgICAgICBuZXdTdGF0dXNbcF0gPSBjaGFuZ2VTdGF0dXNbcF07XG4gICAgICAgICAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgbmV3U3RhdHVzW3BdID0gdGhpc1twXTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICB9XG4gICAgICAgIH1cbiAgICAgICAgcmV0dXJuIG5ld1N0YXR1cztcbiAgICB9XG59XG4iLCIvLyBmb3IgREVCVUdcbnZhciBjb3VudCA9IDA7XG4vKipcbiAqIHRoZSBhYnN0cmFjdCB2YWx1ZSBmb3IgYSBjb25jcmV0ZSB2YWx1ZVxuICogd2hpY2ggaXMgYSBzZXQgb2YgdHlwZXMuXG4gKi9cbmV4cG9ydCBjbGFzcyBBVmFsIHtcbiAgICAvKipcbiAgICAgKiBAcGFyYW0ge1R5cGV9IHR5cGUgLSBnaXZlIGEgdHlwZSB0byBtYWtlIEFWYWwgd2l0aCBhIHNpbmdsZSB0eXBlXG4gICAgICovXG4gICAgY29uc3RydWN0b3IodHlwZSkge1xuICAgICAgICAvLyB0eXBlOiBjb250YWluZWQgdHlwZXNcbiAgICAgICAgLy8gV2UgYXNzdW1lIHR5cGVzIGFyZSBkaXN0aW5ndWlzaGFibGUgYnkgJz09PSdcbiAgICAgICAgaWYgKHR5cGUpIHRoaXMudHlwZXMgPSBuZXcgU2V0KFt0eXBlXSk7XG4gICAgICAgIGVsc2UgdGhpcy50eXBlcyA9IG5ldyBTZXQoKTtcbiAgICAgICAgLy8gZm9yd2FyZHM6IHByb3BhZ2F0aW9uIHRhcmdldHNcbiAgICAgICAgLy8gV2UgYXNzdW1lIHRhcmdldHMgYXJlIGRpc3Rpbmd1aXNoYWJsZSBieSAnZXF1YWxzJyBtZXRob2RcbiAgICAgICAgdGhpcy5mb3J3YXJkcyA9IG5ldyBTZXQoKTtcbiAgICAgICAgLy8gZm9yIERFQlVHXG4gICAgICAgIHRoaXMuX2lkID0gY291bnQrKztcbiAgICB9XG5cbiAgICAvKiogQ2hlY2sgd2hldGhlciBpdCBoYXMgYW55IHR5cGVcbiAgICAgKiBAcmV0dXJucyB7Ym9vbGVhbn1cbiAgICAgKi9cbiAgICBpc0VtcHR5KCkge1xuICAgICAgICByZXR1cm4gdGhpcy50eXBlcy5zaXplID09PSAwO1xuICAgIH1cblxuICAgIGdldFNpemUoKSB7XG4gICAgICAgIHJldHVybiB0aGlzLnR5cGVzLnNpemU7XG4gICAgfVxuXG4gICAgLyoqXG4gICAgICogQHJldHVybnMge1NldC48VHlwZT59XG4gICAgICovXG4gICAgZ2V0VHlwZXMoKSB7XG4gICAgICAgIHJldHVybiB0aGlzLnR5cGVzO1xuICAgIH1cblxuICAgIC8qKlxuICAgICAqIEBwYXJhbSB7VHlwZX0gdHlwZVxuICAgICAqIEByZXR1cm5zIHtib29sZWFufVxuICAgICAqL1xuICAgIGhhc1R5cGUodHlwZSkge1xuICAgICAgICByZXR1cm4gdGhpcy50eXBlcy5oYXModHlwZSk7XG4gICAgfVxuXG4gICAgLyoqXG4gICAgICogQWRkIGEgdHlwZS5cbiAgICAgKiBAcGFyYW0ge1R5cGV9IHR5cGVcbiAgICAgKiBAcmV0dXJucyB7Ym9vbGVhbn1cbiAgICAgKi9cbiAgICBhZGRUeXBlKHR5cGUpIHtcbiAgICAgICAgaWYgKHRoaXMudHlwZXMuaGFzKHR5cGUpKSB7XG4gICAgICAgICAgICByZXR1cm4gZmFsc2U7XG4gICAgICAgIH1cbiAgICAgICAgLy8gZ2l2ZW4gdHlwZSBpcyBuZXdcbiAgICAgICAgdGhpcy50eXBlcy5hZGQodHlwZSk7XG4gICAgICAgIC8vIHNlbmQgdG8gcHJvcGFnYXRpb24gdGFyZ2V0c1xuICAgICAgICB0aGlzLmZvcndhcmRzLmZvckVhY2goZndkID0+IHtcbiAgICAgICAgICAgIGZ3ZC5hZGRUeXBlKHR5cGUpO1xuICAgICAgICB9KTtcbiAgICAgICAgcmV0dXJuIHRydWU7XG4gICAgfVxuXG4gICAgLyoqXG4gICAgICogQHBhcmFtIHtBVmFsfSB0YXJnZXRcbiAgICAgKi9cbiAgICBwcm9wYWdhdGUodGFyZ2V0KSB7XG4gICAgICAgIGlmICghdGhpcy5hZGRGb3J3YXJkKHRhcmdldCkpIHJldHVybjtcbiAgICAgICAgLy8gdGFyZ2V0IGlzIG5ld2x5IGFkZGVkXG4gICAgICAgIC8vIHNlbmQgdHlwZXMgdG8gdGhlIG5ldyB0YXJnZXRcbiAgICAgICAgdGhpcy50eXBlcy5mb3JFYWNoKHR5cGUgPT4ge1xuICAgICAgICAgICAgdGFyZ2V0LmFkZFR5cGUodHlwZSk7XG4gICAgICAgIH0pO1xuICAgIH1cblxuICAgIC8qKlxuICAgICAqIEFkZCBhIHByb3BhZ2F0aW9uIHRhcmdldFxuICAgICAqIEBwYXJhbSB7QVZhbH0gZndkXG4gICAgICogQHJldHVybnMge2Jvb2xlYW59IC0gcmV0dXJucyBmYWxzZSBpZiBpdCBhbHJlYWR5IGhhcyB0aGUgdGFyZ2V0XG4gICAgICovXG4gICAgYWRkRm9yd2FyZChmd2QpIHtcbiAgICAgICAgZm9yIChsZXQgb2xkRndkIG9mIHRoaXMuZm9yd2FyZHMpIHtcbiAgICAgICAgICAgIGlmIChmd2QuZXF1YWxzKG9sZEZ3ZCkpIHtcbiAgICAgICAgICAgICAgICByZXR1cm4gZmFsc2U7XG4gICAgICAgICAgICB9XG4gICAgICAgIH1cbiAgICAgICAgdGhpcy5mb3J3YXJkcy5hZGQoZndkKTtcbiAgICAgICAgcmV0dXJuIHRydWU7XG4gICAgfVxuXG4gICAgLyoqXG4gICAgICogQ2hlY2sgaWYgdGhleSBhcmUgdGhlIHNhbWVcbiAgICAgKiBAcGFyYW0ge0FWYWx9IG90aGVyXG4gICAgICogQHJldHVybnMge2Jvb2xlYW59XG4gICAgICovXG4gICAgZXF1YWxzKG90aGVyKSB7XG4gICAgICAgIC8vIHNpbXBsZSByZWZlcmVuY2UgY29tcGFyaXNvblxuICAgICAgICByZXR1cm4gdGhpcyA9PT0gb3RoZXI7XG4gICAgfVxuXG4gICAgLyoqXG4gICAgICogVE9ETzogY2hlY2sgd2hldGhlciB3ZSByZWFsbHkgbmVlZCB0aGlzIG1ldGhvZC5cbiAgICAgKiBAcGFyYW0ge3N0cmluZ3xudWxsfSBwcm9wXG4gICAgICogQHJldHVybnMge0FWYWx9XG4gICAgICovXG4gICAgZ2V0UHJvcChwcm9wKSB7XG4gICAgICAgIGlmICh0aGlzLnByb3BzLmhhcyhwcm9wKSkge1xuICAgICAgICAgICAgcmV0dXJuIHRoaXMucHJvcHMuZ2V0KHByb3ApO1xuICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgICAgcmV0dXJuIEFWYWxOdWxsO1xuICAgICAgICB9XG4gICAgfVxuXG4gICAgdG9TdHJpbmcoKSB7XG4gICAgICAgIGNvbnN0IHZpc2l0ZWRUeXBlcyA9IG5ldyBTZXQoKTtcbiAgICAgICAgcmV0dXJuIHRoaXMuX3RvU3RyaW5nKHZpc2l0ZWRUeXBlcyk7XG4gICAgfVxuXG4gICAgX3RvU3RyaW5nKHZpc2l0ZWRUeXBlcykge1xuICAgICAgICBjb25zdCB0eXBlU3RyaW5ncyA9IFtdO1xuICAgICAgICBmb3IgKGxldCB0cCBvZiB0aGlzLnR5cGVzKSB7XG4gICAgICAgICAgICBpZiAodmlzaXRlZFR5cGVzLmhhcyh0cCkpIHtcbiAgICAgICAgICAgICAgICB0eXBlU3RyaW5ncy5wdXNoKCc/Jyk7XG4gICAgICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgICAgICAgIHR5cGVTdHJpbmdzLnB1c2godHAuX3RvU3RyaW5nKHZpc2l0ZWRUeXBlcykpO1xuICAgICAgICAgICAgfVxuICAgICAgICB9XG4gICAgICAgIHJldHVybiB0eXBlU3RyaW5ncy5qb2luKCd8Jyk7XG4gICAgfVxufVxuXG4vKipcbiAqIHRoZSBzdXBlciBjbGFzcyBvZiBhbGwgdHlwZXNcbiAqIGVhY2ggdHlwZSBzaG91bGQgYmUgZGlzdGluZ3Vpc2hhYmxlIGJ5ICc9PT0nIG9wZXJhdGlvbi5cbiAqL1xuY2xhc3MgVHlwZSB7XG4gICAgLyoqXG4gICAgICogQ3JlYXRlIGEgbmV3IHR5cGVcbiAgICAgKiBAcGFyYW0ge3N0cmluZ30gbmFtZVxuICAgICAqL1xuICAgIGNvbnN0cnVjdG9yKG5hbWUpIHtcbiAgICAgICAgdGhpcy5uYW1lID0gbmFtZTtcbiAgICB9XG5cbiAgICAvKipcbiAgICAgKiBSZXR1cm5zIHRoZSBuYW1lIG9mIHR5cGVcbiAgICAgKiBAcmV0dXJucyB7c3RyaW5nfVxuICAgICAqL1xuICAgIGdldE5hbWUoKSB7XG4gICAgICAgIHJldHVybiB0aGlzLm5hbWU7XG4gICAgfVxuXG4gICAgLyoqXG4gICAgICogRGVmYXVsdCBpbXBsZW1lbnRhdGlvbiBmb3IgdG9TdHJpbmdcbiAgICAgKiBUaGlzIHNob3VsZCBiZSBvdmVycmlkZGVuIGZvciBzb3BoaXN0aWNhdGVkIHR5cGVzXG4gICAgICogQHJldHVybnMge3N0cmluZ31cbiAgICAgKi9cbiAgICBfdG9TdHJpbmcoKSB7XG4gICAgICAgIHJldHVybiB0aGlzLmdldE5hbWUoKTtcbiAgICB9XG59XG5cblxuLyoqXG4gKiAxLiBvYmplY3QgdHlwZXNcbiAqL1xuZXhwb3J0IGNsYXNzIE9ialR5cGUgZXh0ZW5kcyBUeXBlIHtcbiAgICAvKipcbiAgICAgKiBAcGFyYW0ge0FWYWx9IHByb3RvIC0gQVZhbCBvZiBjb25zdHJ1Y3RvcidzIHByb3RvdHlwZVxuICAgICAqIEBwYXJhbSB7c3RyaW5nfSBuYW1lIC0gZ3Vlc3NlZCBuYW1lXG4gICAgICovXG4gICAgY29uc3RydWN0b3IocHJvdG8sIG5hbWUpIHtcbiAgICAgICAgc3VwZXIobmFtZSk7XG4gICAgICAgIHRoaXMucHJvcHMgPSBuZXcgTWFwKCk7XG4gICAgICAgIC8vIHNoYXJlIHByb3RvIHdpdGggX19wcm90b19fXG4gICAgICAgIHRoaXMuc2V0UHJvcCgnX19wcm90b19fJywgcHJvdG8pO1xuICAgICAgICAvLyByZW1lbWJlciB3aG9zZSBwcm90b3R5cGUgSSBhbVxuICAgICAgICB0aGlzLnByb3RvdHlwZU9mID0gbmV3IEFWYWwoKTtcbiAgICB9XG5cbiAgICAvKipcbiAgICAgKiBAcGFyYW0ge3N0cmluZ3xudWxsfSBwcm9wIC0gbnVsbCBmb3IgY29tcHV0ZWQgcHJvcHNcbiAgICAgKiBAcGFyYW0ge2Jvb2xlYW59IHJlYWRPbmx5IC0gaWYgZmFsc2UsIGNyZWF0ZSBBVmFsIGZvciBwcm9wIGlmIG5lY2Vzc2FyeVxuICAgICAqIEByZXR1cm5zIHtBVmFsfSBBVmFsIG9mIHRoZSBwcm9wZXJ0eVxuICAgICAqL1xuICAgIGdldFByb3AocHJvcCwgcmVhZE9ubHkpIHtcbiAgICAgICAgaWYgKHRoaXMucHJvcHMuaGFzKHByb3ApKSB7XG4gICAgICAgICAgICByZXR1cm4gdGhpcy5wcm9wcy5nZXQocHJvcCk7XG4gICAgICAgIH0gZWxzZSBpZiAocmVhZE9ubHkpIHtcbiAgICAgICAgICAgIHJldHVybiBudWxsO1xuICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgICAgdmFyIG5ld1Byb3BBVmFsID0gbmV3IEFWYWw7XG4gICAgICAgICAgICB0aGlzLnByb3BzLnNldChwcm9wLCBuZXdQcm9wQVZhbCk7XG4gICAgICAgICAgICByZXR1cm4gbmV3UHJvcEFWYWw7XG4gICAgICAgIH1cbiAgICB9XG5cbiAgICAvKipcbiAgICAgKiBXZSB1c2UgdGhpcyBmdW5jdGlvbiB0byBzaGFyZSAucHJvdG90eXBlIHdpdGggaW5zdGFuY2VzIF9fcHJvdG9fX1xuICAgICAqIEl0IGlzIHBvc3NpYmxlIHRvIHVzZSB0aGlzIGZ1bmN0aW9uIHRvIG1lcmdlIEFWYWxzIHRvIG9wdGltaXplIHRoZSBhbmFseXplci5cbiAgICAgKiBAcGFyYW0ge3N0cmluZ3xudWxsfSBwcm9wIC0gbnVsbCBmb3IgY29tcHV0ZWQgcHJvcHNcbiAgICAgKiBAcGFyYW0ge0FWYWx9IGF2YWxcbiAgICAgKi9cbiAgICBzZXRQcm9wKHByb3AsIGF2YWwpIHtcbiAgICAgICAgdGhpcy5wcm9wcy5zZXQocHJvcCwgYXZhbCk7XG4gICAgfVxuXG4gICAgLyoqXG4gICAgICogUmV0dXJucyBpdGVyYXRvciBvZiBpdHMgb3duIHByb3BlcnR5IG5hbWVzXG4gICAgICogQHJldHVybnMge0l0ZXJhdG9yLjxzdHJpbmc+fVxuICAgICAqL1xuICAgIGdldE93blByb3BOYW1lcygpIHtcbiAgICAgICAgcmV0dXJuIHRoaXMucHJvcHMua2V5cygpO1xuICAgIH1cblxuICAgIC8qKlxuICAgICAqIFRPRE86IENoZWNrIHRoaXMgZnVuY3Rpb24ncyBuZWNlc3NpdHlcbiAgICAgKiBAcGFyYW0ge3N0cmluZ3xudWxsfSBwcm9wXG4gICAgICogQHJldHVybnMge2Jvb2xlYW59XG4gICAgICovXG4gICAgaGFzUHJvcChwcm9wKSB7XG4gICAgICAgIHJldHVybiB0aGlzLnByb3BzLmhhcyhwcm9wKTtcbiAgICB9XG5cbiAgICAvKipcbiAgICAgKiBUT0RPOiBDaGVjayB0aGlzIGZ1bmN0aW9uJ3MgbmVjZXNzaXR5XG4gICAgICogQHBhcmFtIHtUeXBlfSB0eXBlXG4gICAgICogQHBhcmFtIHtzdHJpbmd8bnVsbH0gcHJvcFxuICAgICAqL1xuICAgIGFkZFR5cGVUb1Byb3AodHlwZSwgcHJvcCkge1xuICAgICAgICBpZiAoIXRoaXMucHJvcHMuaGFzKHByb3ApKSB7XG4gICAgICAgICAgICB0aGlzLnByb3BzLnNldChwcm9wLCBuZXcgQVZhbCk7XG4gICAgICAgIH1cbiAgICAgICAgaWYgKHRoaXMucHJvcHMuZ2V0KHByb3ApLmhhc1R5cGUodHlwZSkpIHJldHVybjtcbiAgICAgICAgdGhpcy5wcm9wcy5nZXQocHJvcCkuYWRkVHlwZSh0eXBlKTtcbiAgICB9XG5cbiAgICAvKipcbiAgICAgKiBUT0RPOiBDaGVjayB0aGlzIGZ1bmN0aW9uJ3MgbmVjZXNzaXR5XG4gICAgICogQHBhcmFtIHtBVmFsfSBhdmFsXG4gICAgICogQHBhcmFtIHtzdHJpbmd9IHByb3BcbiAgICAgKi9cbiAgICBqb2luQVZhbFRvUHJvcChhdmFsLCBwcm9wKSB7XG4gICAgICAgIHZhciBzZWxmID0gdGhpcztcbiAgICAgICAgYXZhbC5nZXRUeXBlcygpLmZvckVhY2goZnVuY3Rpb24gKHR5cGUpIHtcbiAgICAgICAgICAgIHNlbGYuYWRkVHlwZVRvUHJvcCh0eXBlLCBwcm9wKTtcbiAgICAgICAgfSk7XG4gICAgfVxuXG4gICAgLyoqXG4gICAgICogU2hvdyBvYmplY3QncyBvd24gcHJvcGVydHkgbmFtZXNcbiAgICAgKiBAcGFyYW0ge1NldC48VHlwZT59IHZpc2l0ZWRUeXBlc1xuICAgICAqIEByZXR1cm5zIHtzdHJpbmd9XG4gICAgICovXG4gICAgX3RvU3RyaW5nKHZpc2l0ZWRUeXBlcykge1xuICAgICAgICBpZiAodGhpcy5uYW1lID09PSB1bmRlZmluZWQpIHtcbiAgICAgICAgICAgIGNvbnN0IHByb3BzID0gW107XG4gICAgICAgICAgICBmb3IgKGxldCBwIG9mIHRoaXMucHJvcHMua2V5cygpKSB7XG4gICAgICAgICAgICAgICAgLy8gc2tpcHBpbmcgX19wcm90b19fXG4gICAgICAgICAgICAgICAgaWYgKHAgPT09ICdfX3Byb3RvX18nKSBjb250aW51ZTtcbiAgICAgICAgICAgICAgICBwcm9wcy5wdXNoKHApO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgcmV0dXJuICd7JyArIHByb3BzLmpvaW4oKSArICd9JztcbiAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICAgIHJldHVybiB0aGlzLm5hbWU7XG4gICAgICAgIH1cbiAgICB9XG59XG5cbi8vIG1ha2UgYW4gT2JqIGZyb20gdGhlIGdsb2JhbCBzY29wZVxuZXhwb3J0IGZ1bmN0aW9uIG1rT2JqRnJvbUdsb2JhbFNjb3BlKGdTY29wZSkge1xuICAgIHZhciBnT2JqID0gbmV3IE9ialR5cGUoQVZhbE51bGwsICcqZ2xvYmFsIHNjb3BlKicpO1xuICAgIGdPYmoucHJvcHMgPSBnU2NvcGUudmFyTWFwO1xuICAgIC8vIE92ZXJyaWRlIGdldFByb3AgbWV0aG9kIGZvciBnbG9iYWwgb2JqZWN0XG4gICAgLy8gV2UgaWdub3JlICdyZWFkT25seScgcGFyYW1ldGVyIHRvIGFsd2F5cyByZXR1cm4gaXRzIG93biBwcm9wIEFWYWwgXG4gICAgZ09iai5nZXRQcm9wID0gZnVuY3Rpb24gKHByb3ApIHtcbiAgICAgICAgaWYgKCFnU2NvcGUudmIuaGFzTG9jYWxWYXIocHJvcCkpIHtcbiAgICAgICAgICAgIC8vIHdoZW4gd2UgcmVmZXIgcHJvcCBvZiB0aGUgZ2xvYmFsIG9iamVjdFxuICAgICAgICAgICAgZ1Njb3BlLnZiLmFkZERlY2xhcmVkTG9jYWxWYXIocHJvcCk7XG4gICAgICAgIH1cbiAgICAgICAgcmV0dXJuIE9ialR5cGUucHJvdG90eXBlLmdldFByb3AuY2FsbCh0aGlzLCBwcm9wKTtcbiAgICB9O1xuICAgIHJldHVybiBnT2JqO1xufVxuXG4vKipcbiAqIDIuIHByaW1pdGl2ZSB0eXBlc1xuICovXG5leHBvcnQgY2xhc3MgUHJpbVR5cGUgZXh0ZW5kcyBUeXBlIHtcbiAgICAvKipcbiAgICAgKiBAcGFyYW0ge3N0cmluZ30gbmFtZVxuICAgICAqL1xuICAgIGNvbnN0cnVjdG9yKG5hbWUpIHtcbiAgICAgICAgc3VwZXIobmFtZSk7XG4gICAgfVxufVxuXG4vKipcbiAqIDMuIGZ1bmN0aW9uIHR5cGVzXG4gKiB0aGUgbmFtZSBpcyB1c2VkIGZvciB0aGUgdHlwZSBvZiB0aGUgaW5zdGFuY2VzIGZyb20gdGhlIGZ1bmN0aW9uXG4gKi9cbmV4cG9ydCBjbGFzcyBGblR5cGUgZXh0ZW5kcyBPYmpUeXBlIHtcbiAgICAvKipcbiAgICAgKiBAcGFyYW0ge0FWYWx9IGZuX3Byb3RvIC0gQVZhbCBmb3IgY29uc3RydWN0b3IncyAucHJvdG90eXBlXG4gICAgICogQHBhcmFtIHtzdHJpbmd9IG5hbWUgLSBndWVzc2VkIG5hbWVcbiAgICAgKiBAcGFyYW0ge1tzdHJpbmddfSBhcmdOYW1lcyAtIGxpc3Qgb2YgcGFyYW1ldGVyIG5hbWVzXG4gICAgICogQHBhcmFtIHtTY29wZX0gc2MgLSBmdW5jdGlvbnMgc2NvcGUgY2hhaW4sIG9yIGNsb3N1cmVcbiAgICAgKiBAcGFyYW0ge25vZGV9IG9yaWdpbk5vZGUgLSBBU1Qgbm9kZSBmb3IgdGhlIGZ1bmN0aW9uXG4gICAgICogQHBhcmFtIHtUeXBlfSBhcmdQcm90byAtIHByb3RvdHlwZSBmb3IgYXJndW1lbnRzIG9iamVjdFxuICAgICAqIEBwYXJhbSB7QVZhbH0gYm91bmRUaGlzIC0gcmVtZW1iZXIgdGhpc0FWYWwgZm9yIGFycm93IGZ1bmN0aW9uXG4gICAgICovXG4gICAgY29uc3RydWN0b3IoZm5fcHJvdG8sIG5hbWUsIGFyZ05hbWVzLCBzYywgb3JpZ2luTm9kZSwgYXJnUHJvdG8sIGJvdW5kVGhpcykge1xuICAgICAgICBzdXBlcihmbl9wcm90bywgbmFtZSk7XG4gICAgICAgIHRoaXMucGFyYW1OYW1lcyA9IGFyZ05hbWVzO1xuICAgICAgICB0aGlzLnNjID0gc2M7XG4gICAgICAgIHRoaXMub3JpZ2luTm9kZSA9IG9yaWdpbk5vZGU7XG4gICAgICAgIGlmIChhcmdQcm90bykge1xuICAgICAgICAgICAgdGhpcy5hcmdQcm90byA9IGFyZ1Byb3RvO1xuICAgICAgICB9XG4gICAgICAgIGlmIChib3VuZFRoaXMpIHtcbiAgICAgICAgICAgIHRoaXMuYm91bmRUaGlzID0gYm91bmRUaGlzO1xuICAgICAgICB9XG4gICAgICAgIC8vIGZ1bkVudiA6IENhbGxDb250ZXh0IC0+IFtzZWxmLCByZXQsIGV4Y11cbiAgICAgICAgdGhpcy5mdW5FbnYgPSBuZXcgTWFwO1xuICAgIH1cblxuICAgIC8qKlxuICAgICAqIGNvbnN0cnVjdCBTdGF0dXMgZm9yIGZ1bmN0aW9uXG4gICAgICogQHBhcmFtIHtDYWxsQ29udGV4dH0gZGVsdGEgLSBjYWxsIGNvbnRleHRcbiAgICAgKiBAcmV0dXJucyB7W0FWYWwsIEFWYWwsIEFWYWxdfSAtIGZvciBzZWxmLCByZXR1cm4gYW5kIGV4Y2VwdGlvbiBBVmFsc1xuICAgICAqL1xuICAgIGdldEZ1bkVudihkZWx0YSkge1xuICAgICAgICBpZiAodGhpcy5mdW5FbnYuaGFzKGRlbHRhKSkge1xuICAgICAgICAgICAgcmV0dXJuIHRoaXMuZnVuRW52LmdldChkZWx0YSk7XG4gICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgICB2YXIgdHJpcGxlID0gW25ldyBBVmFsLCBuZXcgQVZhbCwgbmV3IEFWYWxdO1xuICAgICAgICAgICAgdGhpcy5mdW5FbnYuc2V0KGRlbHRhLCB0cmlwbGUpO1xuICAgICAgICAgICAgcmV0dXJuIHRyaXBsZTtcbiAgICAgICAgfVxuICAgIH1cblxuICAgIGdldEFyZ3VtZW50c09iamVjdChkZWx0YSkge1xuICAgICAgICB0aGlzLmFyZ09iak1hcCA9IHRoaXMuYXJnT2JqTWFwIHx8IG5ldyBNYXA7XG4gICAgICAgIGlmICh0aGlzLmFyZ09iak1hcC5oYXMoZGVsdGEpKSB7XG4gICAgICAgICAgICByZXR1cm4gdGhpcy5hcmdPYmpNYXAuZ2V0KGRlbHRhKTtcbiAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICAgIHZhciBhcmdPYmogPSBuZXcgT2JqVHlwZShuZXcgQVZhbCh0aGlzLmFyZ1Byb3RvKSwgJyphcmd1bWVudHMgb2JqZWN0KicpO1xuICAgICAgICAgICAgdGhpcy5hcmdPYmpNYXAuc2V0KGRlbHRhLCBhcmdPYmopO1xuICAgICAgICAgICAgcmV0dXJuIGFyZ09iajtcbiAgICAgICAgfVxuICAgIH1cblxuICAgIC8qKlxuICAgICAqIGdldCBPYmplY3QgbWFkZSBieSB0aGUgZnVuY3Rpb25cbiAgICAgKiBUT0RPOiB1c2UgYWRkaXRpb25hbCBpbmZvcm1hdGlvbiB0byBjcmVhdGUgbXVsdGlwbGUgaW5zdGFuY2VzXG4gICAgICogQHJldHVybnMge09ialR5cGV9XG4gICAgICovXG4gICAgZ2V0SW5zdGFuY2UoKSB7XG4gICAgICAgIC8vIG9iakluc3RhbmNlIGlzIHRoZSBvYmplY3QgbWFkZSBieSB0aGUgZnVuY3Rpb25cbiAgICAgICAgaWYgKHRoaXMub2JqSW5zdGFuY2UpIHJldHVybiB0aGlzLm9iakluc3RhbmNlO1xuICAgICAgICAvLyB3ZSB1bmlmeSBjb25zdHJ1Y3RvcidzIC5wcm90b3R5cGUgYW5kIGluc3RhbmNlJ3MgX19wcm90b19fXG4gICAgICAgIHRoaXMub2JqSW5zdGFuY2UgPSBuZXcgT2JqVHlwZSh0aGlzLmdldFByb3AoJ3Byb3RvdHlwZScpKTtcbiAgICAgICAgcmV0dXJuIHRoaXMub2JqSW5zdGFuY2U7XG4gICAgfVxuXG4gICAgX3N0cmluZ2lmeU9uZUxldmVsU3RydWN0dXJlKHN0cnVjdHVyZSkge1xuXG4gICAgICAgIGNvbnN0IHBhcmFtcyA9IHN0cnVjdHVyZS5wYXJhbXMubWFwKGZ1bmN0aW9uIChwYXJhbSkge1xuICAgICAgICAgICAgaWYgKHBhcmFtLnR5cGUgIT09IHVuZGVmaW5lZClcbiAgICAgICAgICAgICAgICByZXR1cm4gcGFyYW0ubmFtZSArICc6JyArIHBhcmFtLnR5cGU7XG4gICAgICAgICAgICBlbHNlIHJldHVybiBwYXJhbS5uYW1lO1xuICAgICAgICB9KTtcblxuICAgICAgICBsZXQgcmVzU3RyID0gJ2ZuKCcgKyBwYXJhbXMuam9pbignLCAnKSArICcpJztcbiAgICAgICAgaWYgKHN0cnVjdHVyZS5yZXQgIT09IHVuZGVmaW5lZCkge1xuICAgICAgICAgICAgcmVzU3RyICs9ICcgLT4gJyArIHN0cnVjdHVyZS5yZXQ7XG4gICAgICAgIH1cbiAgICAgICAgcmV0dXJuIHJlc1N0cjtcbiAgICB9XG5cbiAgICBfdG9TdHJpbmcodmlzaXRlZFR5cGVzKSB7XG4gICAgICAgIGlmICh2aXNpdGVkVHlwZXMuaGFzKHRoaXMpKSB7XG4gICAgICAgICAgICByZXR1cm4gJz8nO1xuICAgICAgICB9XG4gICAgICAgIGNvbnN0IHN0cnVjdHVyZSA9IHRoaXMuX2dldE9uZUxldmVsU3RydWN0dXJlKHZpc2l0ZWRUeXBlcyk7XG4gICAgICAgIHJldHVybiB0aGlzLl9zdHJpbmdpZnlPbmVMZXZlbFN0cnVjdHVyZShzdHJ1Y3R1cmUpO1xuICAgIH1cblxuICAgIF9nZXRPbmVMZXZlbFN0cnVjdHVyZSh2aXNpdGVkVHlwZXMpIHtcbiAgICAgICAgdmlzaXRlZFR5cGVzLmFkZCh0aGlzKTtcbiAgICAgICAgY29uc3QgaW5uZXJTY29wZXMgPSB0aGlzLm9yaWdpbk5vZGUuYm9keVsnQGJsb2NrJ10uZ2V0U2NvcGVXaXRoUGFyZW50KHRoaXMuc2MpO1xuICAgICAgICBjb25zdCBwYXJhbUluZm8gPSBbXTtcbiAgICAgICAgZm9yIChsZXQgaSA9IDA7IGkgPCB0aGlzLnBhcmFtTmFtZXMubGVuZ3RoOyBpKyspIHtcbiAgICAgICAgICAgIGNvbnN0IHBhcmFtTmFtZSA9IHRoaXMucGFyYW1OYW1lc1tpXTtcbiAgICAgICAgICAgIGNvbnN0IHN0cmluZ3MgPSBbXTtcbiAgICAgICAgICAgIGxldCBoYXNUeXBlID0gZmFsc2U7XG4gICAgICAgICAgICBmb3IgKGxldCBzYyBvZiBpbm5lclNjb3Blcykge1xuICAgICAgICAgICAgICAgIGNvbnN0IGF2YWwgPSBzYy5nZXRBVmFsT2YocGFyYW1OYW1lKTtcbiAgICAgICAgICAgICAgICBpZiAoIWF2YWwuaXNFbXB0eSgpKSB7XG4gICAgICAgICAgICAgICAgICAgIHN0cmluZ3MucHVzaChhdmFsLl90b1N0cmluZyh2aXNpdGVkVHlwZXMpKTtcbiAgICAgICAgICAgICAgICAgICAgaGFzVHlwZSA9IHRydWU7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgfVxuICAgICAgICAgICAgY29uc3QgdHlwZVN0cmluZyA9IGhhc1R5cGUgPyBzdHJpbmdzLmpvaW4oJ3wnKSA6IHVuZGVmaW5lZDtcbiAgICAgICAgICAgIHBhcmFtSW5mby5wdXNoKHtuYW1lOiBwYXJhbU5hbWUsIHR5cGU6IHR5cGVTdHJpbmd9KTtcbiAgICAgICAgfVxuICAgICAgICAvLyBjb21wdXRpbmcgam9pbmVkIHJldEFWYWxcbiAgICAgICAgY29uc3QgcmV0VHlwZVN0cmluZ3MgPSBbXTtcbiAgICAgICAgbGV0IG5vUmV0VHlwZXMgPSB0cnVlO1xuICAgICAgICBmb3IgKGxldCBbLCByZXRBVmFsLCBdIG9mIHRoaXMuZnVuRW52LnZhbHVlcygpKSB7XG4gICAgICAgICAgICBpZiAoIXJldEFWYWwuaXNFbXB0eSgpKSB7XG4gICAgICAgICAgICAgICAgbm9SZXRUeXBlcyA9IGZhbHNlO1xuICAgICAgICAgICAgICAgIHJldFR5cGVTdHJpbmdzLnB1c2gocmV0QVZhbC5fdG9TdHJpbmcodmlzaXRlZFR5cGVzKSk7XG4gICAgICAgICAgICB9XG4gICAgICAgIH1cbiAgICAgICAgdmlzaXRlZFR5cGVzLmRlbGV0ZSh0aGlzKTtcbiAgICAgICAgcmV0dXJuIHtwYXJhbXM6IHBhcmFtSW5mbywgcmV0OiAobm9SZXRUeXBlcyA/IHVuZGVmaW5lZCA6IHJldFR5cGVTdHJpbmdzLmpvaW4oJ3wnKSl9O1xuXG4gICAgfVxuXG4gICAgZ2V0T25lTGV2ZWxTdHJ1Y3R1cmUoKSB7XG4gICAgICAgIGNvbnN0IHZpc2l0ZWRUeXBlcyA9IG5ldyBTZXQoKTtcbiAgICAgICAgcmV0dXJuIHRoaXMuX2dldE9uZUxldmVsU3RydWN0dXJlKHZpc2l0ZWRUeXBlcyk7XG4gICAgfVxufVxuXG4vKiogXG4gKiA0LiBhcnJheSB0eXBlc1xuICogQGNvbnN0cnVjdG9yXG4gKi9cbmV4cG9ydCBjbGFzcyBBcnJUeXBlIGV4dGVuZHMgT2JqVHlwZSB7XG4gICAgY29uc3RydWN0b3IoYXJyX3Byb3RvKSB7XG4gICAgICAgIHN1cGVyKGFycl9wcm90bywgJ0FycmF5Jyk7XG4gICAgfVxuXG4gICAgX3RvU3RyaW5nKHZpc2l0ZWRUeXBlcykge1xuICAgICAgICBpZiAodmlzaXRlZFR5cGVzLmhhcyh0aGlzKSkge1xuICAgICAgICAgICAgcmV0dXJuICc/JztcbiAgICAgICAgfVxuICAgICAgICB2aXNpdGVkVHlwZXMuYWRkKHRoaXMpO1xuICAgICAgICAvLyBwcm9wIG51bGwgaXMgdXNlZCBmb3IgYXJyYXkgZWxlbWVudHNcbiAgICAgICAgY29uc3QgZWx0VHlwZXMgPSB0aGlzLmdldFByb3AobnVsbCwgdHJ1ZSk7XG4gICAgICAgIGNvbnN0IHRwU3RyID0gJ1snICsgZWx0VHlwZXMuX3RvU3RyaW5nKHZpc2l0ZWRUeXBlcykgKyAnXSc7XG4gICAgICAgIHZpc2l0ZWRUeXBlcy5kZWxldGUodGhpcyk7XG4gICAgICAgIHJldHVybiB0cFN0cjtcbiAgICB9XG59XG5cbi8vIE1ha2UgcHJpbWl0aXZlIHR5cGVzXG5leHBvcnQgY29uc3QgUHJpbU51bWJlciA9IG5ldyBQcmltVHlwZSgnbnVtYmVyJyk7XG5leHBvcnQgY29uc3QgUHJpbVN0cmluZyA9IG5ldyBQcmltVHlwZSgnc3RyaW5nJyk7XG5leHBvcnQgY29uc3QgUHJpbUJvb2xlYW4gPSBuZXcgUHJpbVR5cGUoJ2Jvb2xlYW4nKTtcblxuLy8gQWJzTnVsbCByZXByZXNlbnRzIGFsbCBlbXB0eSBhYnN0cmFjdCB2YWx1ZXMuXG5leHBvcnQgY29uc3QgQVZhbE51bGwgPSBuZXcgQVZhbCgpO1xuLy8gWW91IHNob3VsZCBub3QgYWRkIGFueSBwcm9wZXJ0aWVzIHRvIGl0LlxuQVZhbE51bGwucHJvcHMgPSBudWxsO1xuLy8gQWRkaW5nIHR5cGVzIGFyZSBpZ25vcmVkLlxuQVZhbE51bGwuYWRkVHlwZSA9IGZ1bmN0aW9uICgpIHt9O1xuXG5leHBvcnQgY2xhc3MgQWJzQ2FjaGUge1xuICAgIGNvbnN0cnVjdG9yKCkge1xuICAgICAgICB0aGlzLm1hcCA9IG5ldyBNYXAoKTtcbiAgICB9XG5cbiAgICAvKipcbiAgICAgKiBHZXQgaWYgb25lIGV4aXN0cywgaWYgbm90IGNyZWF0ZSBvbmVcbiAgICAgKiBAcGFyYW0gbG9jXG4gICAgICogQHBhcmFtIGN0eFxuICAgICAqIEByZXR1cm5zIHsqfVxuICAgICAqL1xuICAgIGdldChsb2MsIGN0eCkge1xuICAgICAgICBpZiAoIXRoaXMubWFwLmhhcyhsb2MpKSB7XG4gICAgICAgICAgICAvLyBjcmVhdGUgaW5uZXIgbWFwXG4gICAgICAgICAgICB0aGlzLm1hcC5zZXQobG9jLCBuZXcgTWFwKCkpO1xuICAgICAgICB9XG4gICAgICAgIGNvbnN0IG1hcExvYyA9IHRoaXMubWFwLmdldChsb2MpO1xuICAgICAgICBpZiAoIW1hcExvYy5oYXMoY3R4KSkge1xuICAgICAgICAgICAgY29uc3QgYXYgPSBuZXcgQVZhbCgpO1xuICAgICAgICAgICAgbWFwTG9jLnNldChjdHgsIGF2KTtcbiAgICAgICAgICAgIHJldHVybiBhdjtcbiAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICAgIHJldHVybiBtYXBMb2MuZ2V0KGN0eCk7XG4gICAgICAgIH1cbiAgICB9XG5cbiAgICAvKipcbiAgICAgKiBUbyB1c2UgYXYgbWFkZSBieSBvdGhlcnMgKGUuZy4gc2NvcGUpXG4gICAgICogQHBhcmFtIGxvY1xuICAgICAqIEBwYXJhbSBjdHhcbiAgICAgKiBAcGFyYW0gYXZcbiAgICAgKi9cbiAgICBzZXQobG9jLCBjdHgsIGF2KSB7XG4gICAgICAgIGlmICghdGhpcy5tYXAuaGFzKGxvYykpIHtcbiAgICAgICAgICAgIC8vIGNyZWF0ZSBpbm5lciBtYXBcbiAgICAgICAgICAgIHRoaXMubWFwLnNldChsb2MsIG5ldyBNYXAoKSk7XG4gICAgICAgIH1cbiAgICAgICAgdGhpcy5tYXAuZ2V0KGxvYykuc2V0KGN0eCwgYXYpO1xuICAgIH1cblxuICAgIC8qKlxuICAgICAqIENoZWNrIHdoZXRoZXIgaXQgaGFzIG9uZSBmb3IgbG9jIGFuZCBjdHhcbiAgICAgKiBAcGFyYW0gbG9jXG4gICAgICogQHBhcmFtIGN0eFxuICAgICAqIEByZXR1cm5zIHtib29sZWFufVxuICAgICAqL1xuICAgIGhhcyhsb2MsIGN0eCkge1xuICAgICAgICByZXR1cm4gdGhpcy5tYXAuaGFzKGxvYykgJiYgdGhpcy5tYXAuZ2V0KGxvYykuaGFzKGN0eCk7XG4gICAgfVxuXG4gICAgLyoqXG4gICAgICogTWVyZ2UgYWxsIEFWYWwgb2YgdGhlIGxvY1xuICAgICAqIEBwYXJhbSBsb2NcbiAgICAgKiBAcmV0dXJucyB7QVZhbH1cbiAgICAgKi9cbiAgICBnZXRNZXJnZWRBVmFsT2ZMb2MobG9jKSB7XG4gICAgICAgIGlmICghdGhpcy5tYXAuaGFzKGxvYykpIHtcbiAgICAgICAgICAgIC8vIG5vIHR5cGUgaXMgYXZhaWxhYmxlXG4gICAgICAgICAgICByZXR1cm4gbnVsbDtcbiAgICAgICAgfVxuICAgICAgICBjb25zdCBtZXJnZWRBVmFsID0gbmV3IEFWYWwoKTtcbiAgICAgICAgaWYgKHRoaXMubWFwLmhhcyhsb2MpKSB7XG4gICAgICAgICAgICBmb3IgKGxldCBhdiBvZiB0aGlzLm1hcC5nZXQobG9jKS52YWx1ZXMoKSkge1xuICAgICAgICAgICAgICAgIGZvciAobGV0IHRwIG9mIGF2LmdldFR5cGVzKCkpIHtcbiAgICAgICAgICAgICAgICAgICAgbWVyZ2VkQVZhbC5hZGRUeXBlKHRwKTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICB9XG4gICAgICAgIH1cbiAgICAgICAgcmV0dXJuIG1lcmdlZEFWYWw7XG4gICAgfVxuXG59XG4iLCJpbXBvcnQgKiBhcyBteVdhbGtlciBmcm9tICcuL3V0aWwvbXlXYWxrZXInXG5pbXBvcnQgKiBhcyB0eXBlcyBmcm9tICcuL2RvbWFpbnMvdHlwZXMnXG5cbi8qKlxuICogR2V0IHR5cGVzIG9mIGV4cHJlc3Npb24gYXQgdGhlIGdpdmVuIHJhbmdlXG4gKiBAcGFyYW0gYXN0XG4gKiBAcGFyYW0gxIhcbiAqIEBwYXJhbSBzdGFydFxuICogQHBhcmFtIGVuZFxuICogQHJldHVybnMge3toYXNUeXBlOiBib29sZWFuLCB0eXBlU3RyaW5nOiBzdHJpbmcsIG5vZGVTdGFydDogbnVtYmVyLCBub2RlRW5kOiBudW1iZXJ9fVxuICovXG5leHBvcnQgZnVuY3Rpb24gZ2V0VHlwZUF0UmFuZ2UoYXN0LCDEiCwgc3RhcnQsIGVuZCkge1xuICAgICd1c2Ugc3RyaWN0JztcbiAgICBjb25zdCBub2RlID0gbXlXYWxrZXIuZmluZFN1cnJvdW5kaW5nTm9kZShhc3QsIHN0YXJ0LCBlbmQpO1xuICAgIGNvbnN0IG5vZGVUeXBlcyA9IMSILmdldE1lcmdlZEFWYWxPZkxvYyhub2RlKTtcbiAgICBsZXQgaGFzVHlwZTtcbiAgICBsZXQgdHlwZVN0cmluZyA9ICcnO1xuICAgIGlmICghbm9kZVR5cGVzKSB7XG4gICAgICAgIGhhc1R5cGUgPSBmYWxzZTtcbiAgICAgICAgdHlwZVN0cmluZyA9ICdObyB0eXBlcyBhdCB0aGUgZ2l2ZW4gcmFuZ2UnO1xuICAgIH0gZWxzZSB7XG4gICAgICAgIGhhc1R5cGUgPSB0cnVlO1xuICAgICAgICB0eXBlU3RyaW5nID0gbm9kZVR5cGVzLnRvU3RyaW5nKCk7XG4gICAgfVxuICAgIHJldHVybiB7XG4gICAgICAgIGhhc1R5cGU6IGhhc1R5cGUsXG4gICAgICAgIHR5cGVTdHJpbmc6IHR5cGVTdHJpbmcsXG4gICAgICAgIG5vZGVTdGFydDogbm9kZS5zdGFydCxcbiAgICAgICAgbm9kZUVuZDogbm9kZS5lbmRcbiAgICB9O1xufVxuXG5leHBvcnQgZnVuY3Rpb24gZ2V0Rm5UeXBlU3RydWN0dXJlc0F0KGFzdCwgxIgsIHBvcykge1xuICAgIGNvbnN0IG5vZGUgPSBteVdhbGtlci5maW5kU3Vycm91bmRpbmdOb2RlKGFzdCwgcG9zLCBwb3MpO1xuICAgIGNvbnN0IG5vZGVUeXBlcyA9IMSILmdldE1lcmdlZEFWYWxPZkxvYyhub2RlKTtcbiAgICBjb25zdCBmblR5cGVTdHJ1Y3R1cmVzID0gW107XG5cbiAgICBub2RlVHlwZXMuZ2V0VHlwZXMoKS5mb3JFYWNoKGZ1bmN0aW9uIChmbikge1xuICAgICAgICBpZiAoZm4gaW5zdGFuY2VvZiB0eXBlcy5GblR5cGUpIHtcbiAgICAgICAgICAgIGZuVHlwZVN0cnVjdHVyZXMucHVzaChmbi5nZXRPbmVMZXZlbFN0cnVjdHVyZSgpKTtcbiAgICAgICAgfVxuICAgIH0pO1xuICAgIHJldHVybiBmblR5cGVTdHJ1Y3R1cmVzO1xufVxuXG5mdW5jdGlvbiBjb21wdXRlSWNvbk9mUHJvcChwcm9wTWFwKSB7XG4gICAgY29uc3QgaWNvbk1hcCA9IG5ldyBNYXAoKTtcblxuICAgIGZ1bmN0aW9uIGlzT2JqZWN0KGljb24pIHtcbiAgICAgICAgcmV0dXJuIGljb24gPT09ICdvYmplY3QnIHx8IGljb24gPT09ICdhcnJheScgfHwgaWNvbiA9PT0gJ2ZuJztcbiAgICB9XG5cbiAgICBwcm9wTWFwLmZvckVhY2goKHRwcywgcCkgPT4ge1xuICAgICAgICBmb3IgKGxldCB0cCBvZiB0cHMpIHtcbiAgICAgICAgICAgIGxldCBpY29uO1xuICAgICAgICAgICAgaWYgKHRwID09PSB0eXBlcy5QcmltTnVtYmVyKSBpY29uID0gJ251bWJlcic7XG4gICAgICAgICAgICBlbHNlIGlmICh0cCA9PT0gdHlwZXMuUHJpbUJvb2xlYW4pIGljb24gPSAnYm9vbCc7XG4gICAgICAgICAgICBlbHNlIGlmICh0cCA9PT0gdHlwZXMuUHJpbVN0cmluZykgaWNvbiA9ICdzdHJpbmcnO1xuICAgICAgICAgICAgZWxzZSBpZiAodHAgaW5zdGFuY2VvZiB0eXBlcy5GblR5cGUpIGljb24gPSAnZm4nO1xuICAgICAgICAgICAgZWxzZSBpZiAodHAgaW5zdGFuY2VvZiB0eXBlcy5BcnJUeXBlKSBpY29uID0gJ2FycmF5JztcbiAgICAgICAgICAgIGVsc2UgaWYgKHRwIGluc3RhbmNlb2YgdHlwZXMuT2JqVHlwZSkgaWNvbiA9ICdvYmplY3QnO1xuXG4gICAgICAgICAgICBpZiAoIWljb25NYXAuaGFzKHApIHx8IGljb25NYXAuZ2V0KHApID09PSBpY29uKSB7XG4gICAgICAgICAgICAgICAgaWNvbk1hcC5zZXQocCwgaWNvbik7XG4gICAgICAgICAgICAgICAgY29udGludWU7XG4gICAgICAgICAgICB9XG5cbiAgICAgICAgICAgIGlmIChpc09iamVjdChpY29uKSAmJiBpc09iamVjdChpY29uTWFwLmdldChwKSkpIHtcbiAgICAgICAgICAgICAgICBpY29uTWFwLnNldChwLCAnb2JqZWN0Jyk7XG4gICAgICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgICAgICAgIGljb25NYXAuc2V0KHAsICd1bmtub3duJyk7XG4gICAgICAgICAgICAgICAgYnJlYWs7XG4gICAgICAgICAgICB9XG4gICAgICAgIH1cbiAgICAgICAgaWYgKHRwcy5zaXplID09PSAwKSB7XG4gICAgICAgICAgICBpY29uTWFwLnNldChwLCAndW5rbm93bicpO1xuICAgICAgICB9XG4gICAgfSk7XG4gICAgcmV0dXJuIGljb25NYXA7XG59XG5cbi8qKlxuICogR2V0IHByb3AgdG8gaWNvbiBtYXAgZnJvbSBnaXZlbiBub2RlXG4gKiBAcGFyYW0gxIggLSBBYnNDYWNoZVxuICogQHBhcmFtIG5vZGUgLSBleHByZXNzaW9uIG5vZGVcbiAqIEByZXR1cm5zIHtNYXAuPHN0cmluZywgc3RyaW5nPn0gLSBNYXBwaW5nIGZyb20gcHJvcCB0byBpY29uXG4gKi9cbmV4cG9ydCBmdW5jdGlvbiBnZXRQcm9wRnJvbU5vZGUoxIgsIG5vZGUpIHtcbiAgICAvLyBTaW5jZSBnZXRUeXBlT2ZMb2MgY2FuIHJldHVybiBudWxsIGlmIG5vZGUgZG9lcyBub3QgaGF2ZSBhbnkgdHlwZXNcbiAgICBjb25zdCBub2RlVHlwZXMgPSDEiC5nZXRNZXJnZWRBVmFsT2ZMb2Mobm9kZSk7XG4gICAgY29uc3QgcHJvcE1hcCA9IGdldFJlYWRhYmxlUHJvcE1hcChub2RlVHlwZXMpO1xuICAgIHJldHVybiBjb21wdXRlSWNvbk9mUHJvcChwcm9wTWFwKTtcbn1cblxuLyoqXG4gKiBGb3IgZGVidWdnaW5nLCBzaG93IHhcbiAqIEBwYXJhbSB4XG4gKi9cbmZ1bmN0aW9uIFNIT1coeCkge1xuICAgIGNvbnNvbGUuaW5mbyh4KTtcbiAgICByZXR1cm4geDtcbn1cblxuZXhwb3J0IGZ1bmN0aW9uIGdldENvbXBsZXRpb25BdFBvcyhyZXN1bHQsIHBvcykge1xuICAgIC8vIGZpbmQgaWQgb3IgbWVtYmVyIG5vZGVcbiAgICBjb25zdCBub2RlSW5mbyA9IG15V2Fsa2VyLmZpbmRDb21wbGV0aW9uQ29udGV4dChyZXN1bHQuQVNULCBwb3MpO1xuXG4gICAgaWYgKG5vZGVJbmZvLnR5cGUgPT09ICdJZGVudGlmaWVyJykge1xuICAgICAgICBsZXQgcHJlZml4LCBmcm9tLCB0bztcblxuICAgICAgICBpZiAobm9kZUluZm8ubm9kZSA9PT0gbnVsbCkge1xuICAgICAgICAgICAgcHJlZml4ID0gJyc7XG4gICAgICAgICAgICBmcm9tID0gcG9zO1xuICAgICAgICAgICAgdG8gPSBwb3M7XG4gICAgICAgIH0gZWxzZSBpZiAobXlXYWxrZXIuaXNEdW1teUlkTm9kZShub2RlSW5mby5ub2RlKSkge1xuICAgICAgICAgICAgcHJlZml4ID0gJyc7XG4gICAgICAgICAgICBmcm9tID0gdG8gPSBub2RlSW5mby5ub2RlLmVuZDsgLy8gSGVyZSwgZW5kIGlzIGNvcnJlY3QgZm9yIHN0YXJ0IHBvc2l0aW9uXG4gICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgICBwcmVmaXggPSBub2RlSW5mby5ub2RlLm5hbWU7XG4gICAgICAgICAgICBmcm9tID0gbm9kZUluZm8ubm9kZS5zdGFydDtcbiAgICAgICAgICAgIHRvID0gbm9kZUluZm8ubm9kZS5lbmQ7XG4gICAgICAgIH1cbiAgICAgICAgY29uc3QgdmFyTWFwID0gY29tcHV0ZUljb25PZlByb3AoZ2V0UmVhZGFibGVWYXJNYXAobm9kZUluZm8udmIpKTtcblxuICAgICAgICBjb25zdCBsaXN0ID0gW107XG4gICAgICAgIGZvciAobGV0IFt2LCBpXSBvZiB2YXJNYXApIHtcbiAgICAgICAgICAgIGlmICh2LnN0YXJ0c1dpdGgocHJlZml4KSkge1xuICAgICAgICAgICAgICAgIGxpc3QucHVzaCh7dGV4dDogdiwgaWNvbjogaX0pO1xuICAgICAgICAgICAgfVxuICAgICAgICB9XG4gICAgICAgIHJldHVybiBTSE9XKHtsaXN0OiBsaXN0LCBmcm9tOiBmcm9tLCB0bzogdG99KTtcblxuICAgIH0gZWxzZSB7XG4gICAgICAgIC8vIHByb3BlcnR5IGNvbXBsZXRpb25cbiAgICAgICAgY29uc3Qgb2JqZWN0Tm9kZSA9IG5vZGVJbmZvLm5vZGUub2JqZWN0O1xuICAgICAgICBjb25zdCBwcm9wcyA9IGdldFByb3BGcm9tTm9kZShyZXN1bHQuxIgsIG9iamVjdE5vZGUpO1xuXG4gICAgICAgIGNvbnN0IHByb3BlcnR5Tm9kZSA9IG5vZGVJbmZvLm5vZGUucHJvcGVydHk7XG4gICAgICAgIGxldCBwcmVmaXgsIGZyb20sIHRvLCBmaWx0ZXI7XG4gICAgICAgIGlmIChub2RlSW5mby50eXBlID09PSAndXN1YWxQcm9wJykge1xuICAgICAgICAgICAgY29uc3QgcHJvcE5hbWUgPSBwcm9wZXJ0eU5vZGUubmFtZTtcbiAgICAgICAgICAgIGlmIChteVdhbGtlci5pc0R1bW15SWROb2RlKHByb3BlcnR5Tm9kZSkpIHtcbiAgICAgICAgICAgICAgICBwcmVmaXggPSAnJztcbiAgICAgICAgICAgICAgICBmcm9tID0gcHJvcGVydHlOb2RlLmVuZDsgLy8gSGVyZSwgZW5kIGlzIGNvcnJlY3QgZm9yIHN0YXJ0IHBvc2l0aW9uXG4gICAgICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgICAgICAgIC8vIHByZWZpeCA9IHByb3BOYW1lLnN1YnN0cigwLCBwb3MgLSBwcm9wZXJ0eU5vZGUuc3RhcnQpO1xuICAgICAgICAgICAgICAgIHByZWZpeCA9IHByb3BOYW1lO1xuICAgICAgICAgICAgICAgIGZyb20gPSBwcm9wZXJ0eU5vZGUuc3RhcnQ7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICB0byA9IHByb3BlcnR5Tm9kZS5lbmQ7XG4gICAgICAgICAgICBmaWx0ZXIgPSBwID0+ICgvXlskQS1aX11bMC05QS1aXyRdKiQvaSkudGVzdChwKTtcbiAgICAgICAgfSBlbHNlIGlmIChub2RlSW5mby50eXBlID09PSAnc3RyaW5nUHJvcCcpIHtcbiAgICAgICAgICAgIHByZWZpeCA9IHByb3BlcnR5Tm9kZS52YWx1ZTtcbiAgICAgICAgICAgIGZyb20gPSBwcm9wZXJ0eU5vZGUuc3RhcnQgKyAxO1xuICAgICAgICAgICAgdG8gPSBwcm9wZXJ0eU5vZGUuZW5kIC0gMTtcbiAgICAgICAgICAgIGZpbHRlciA9IHAgPT4gdHJ1ZVxuICAgICAgICB9XG5cbiAgICAgICAgY29uc3QgbGlzdCA9IFtdO1xuICAgICAgICBmb3IgKGxldCBbcCwgaV0gb2YgcHJvcHMpIHtcbiAgICAgICAgICAgIC8vIHVua25vd24gcHJvcCBpcyBudWxsXG4gICAgICAgICAgICBpZiAocCAhPT0gbnVsbCAmJiBwLnN0YXJ0c1dpdGgocHJlZml4KSAmJiBmaWx0ZXIocCkpIHtcbiAgICAgICAgICAgICAgICBsaXN0LnB1c2goe3RleHQ6IHAsIGljb246IGl9KTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgfVxuICAgICAgICByZXR1cm4gU0hPVyh7bGlzdDogbGlzdCwgZnJvbTogZnJvbSwgdG86IHRvfSk7XG4gICAgfVxufVxuXG5cbmZ1bmN0aW9uIHVuaW9uTWFwKG0xLCBtMikge1xuICAgIGNvbnN0IHJldCA9IG5ldyBNYXAoKTtcblxuICAgIGZ1bmN0aW9uIHVuaW9uU2V0KHMxLCBzMikge1xuICAgICAgICBjb25zdCByZXQgPSBuZXcgU2V0KCk7XG4gICAgICAgIGlmIChzMSkgczEuZm9yRWFjaChlID0+IHJldC5hZGQoZSkpO1xuICAgICAgICBpZiAoczIpIHMyLmZvckVhY2goZSA9PiByZXQuYWRkKGUpKTtcbiAgICAgICAgcmV0dXJuIHJldDtcbiAgICB9XG5cbiAgICBpZiAobTEpIG0xLmZvckVhY2goKHRzLCBwKSA9PiByZXQuc2V0KHAsIHRzKSk7XG4gICAgaWYgKG0yKSBtMi5mb3JFYWNoKCh0cywgcCkgPT4gcmV0LnNldChwLCB1bmlvblNldChyZXQuZ2V0KHApLCBtMi5nZXQocCkpKSk7XG4gICAgcmV0dXJuIHJldDtcbn1cblxuZnVuY3Rpb24gYWRkT25seU1pc3NpbmdNYXBwaW5ncyhtMSwgbTIpIHtcbiAgICBjb25zdCByZXQgPSBuZXcgTWFwKCk7XG4gICAgbTEuZm9yRWFjaCgodHMsIHApID0+IHJldC5zZXQocCwgdHMpKTtcbiAgICBtMi5mb3JFYWNoKCh0cywgcCkgPT4ge1xuICAgICAgICBpZiAoIXJldC5oYXMocCkpIHJldC5zZXQocCwgdHMpXG4gICAgfSk7XG4gICAgcmV0dXJuIHJldDtcbn1cblxuLy8gY29udmVydCBhIG1hcCBvZiBBIC0+IEFWYWxcbi8vIHRvIGEgbWFwIG9mIEEgLT4gU2V0LjxUeXBlPlxuZnVuY3Rpb24gY29udmVydE1hcChtYXApIHtcbiAgICBsZXQgcmV0TWFwID0gbmV3IE1hcCgpO1xuICAgIG1hcC5mb3JFYWNoKChhdiwgcCkgPT4ge1xuICAgICAgICByZXRNYXAuc2V0KHAsIGF2LmdldFR5cGVzKCkpO1xuICAgIH0pO1xuICAgIHJldHVybiByZXRNYXA7XG59XG5cbi8vIHRyYXZlcnNlIGFic3RyYWN0IGhlYXAgc3BhY2VcbmZ1bmN0aW9uIGdldFJlYWRhYmxlUHJvcE1hcCh0cHMpIHtcblxuICAgIGNvbnN0IHZpc2l0ZWRUeXBlcyA9IFtdO1xuXG4gICAgZnVuY3Rpb24gdHJhdmVyc2UodHlwZSkge1xuICAgICAgICBpZiAodHlwZSBpbnN0YW5jZW9mIHR5cGVzLk9ialR5cGUgJiZcbiAgICAgICAgICAgIHR5cGUuZ2V0UHJvcCgnX19wcm90b19fJywgdHJ1ZSkpIHtcbiAgICAgICAgICAgIGxldCBwcm90b01hcCA9IG5ldyBNYXAoKTtcbiAgICAgICAgICAgIGNvbnN0IHByb3RvVHlwZXMgPSB0eXBlLmdldFByb3AoJ19fcHJvdG9fXycsIHRydWUpLmdldFR5cGVzKCk7XG5cbiAgICAgICAgICAgIHByb3RvVHlwZXMuZm9yRWFjaCh0cCA9PiB7XG4gICAgICAgICAgICAgICAgaWYgKHZpc2l0ZWRUeXBlcy5pbmRleE9mKHRwKSA+IC0xKSB7XG4gICAgICAgICAgICAgICAgICAgIHJldHVybjtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgdmlzaXRlZFR5cGVzLnB1c2godHApO1xuICAgICAgICAgICAgICAgIHByb3RvTWFwID0gdW5pb25NYXAocHJvdG9NYXAsIHRyYXZlcnNlKHRwKSk7XG4gICAgICAgICAgICAgICAgdmlzaXRlZFR5cGVzLnBvcCgpO1xuICAgICAgICAgICAgfSk7XG4gICAgICAgICAgICByZXR1cm4gYWRkT25seU1pc3NpbmdNYXBwaW5ncyhjb252ZXJ0TWFwKHR5cGUucHJvcHMpLCBwcm90b01hcCk7XG4gICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgICByZXR1cm4gbmV3IE1hcCgpO1xuICAgICAgICB9XG4gICAgfVxuXG4gICAgbGV0IHJldE1hcCA9IG5ldyBNYXAoKTtcbiAgICB0cHMuZ2V0VHlwZXMoKS5mb3JFYWNoKHRwID0+IHtcbiAgICAgICAgcmV0TWFwID0gdW5pb25NYXAocmV0TWFwLCB0cmF2ZXJzZSh0cCkpXG4gICAgfSk7XG5cbiAgICByZXR1cm4gcmV0TWFwO1xufVxuXG5leHBvcnQgZnVuY3Rpb24gZ2V0RGVmaW5pdGlvblNpdGVzQXQoYXN0LCDEiCwgcG9zKSB7XG4gICAgY29uc3Qgbm9kZSA9IG15V2Fsa2VyLmZpbmRTdXJyb3VuZGluZ05vZGUoYXN0LCBwb3MsIHBvcyk7XG4gICAgY29uc3Qgbm9kZVR5cGVzID0gxIguZ2V0TWVyZ2VkQVZhbE9mTG9jKG5vZGUpO1xuXG4gICAgY29uc3QgcmFuZ2VzID0gW107XG4gICAgaWYgKG5vZGVUeXBlcyA9PT0gbnVsbCkge1xuICAgICAgICByZXR1cm4gcmFuZ2VzO1xuICAgIH1cbiAgICBub2RlVHlwZXMuZ2V0VHlwZXMoKS5mb3JFYWNoKGZ1bmN0aW9uICh0cCkge1xuICAgICAgICBpZiAodHAgaW5zdGFuY2VvZiB0eXBlcy5GblR5cGUgJiYgdHAub3JpZ2luTm9kZSkge1xuICAgICAgICAgICAgY29uc3QgZm5Ob2RlID0gdHAub3JpZ2luTm9kZTtcbiAgICAgICAgICAgIGxldCBhdDtcbiAgICAgICAgICAgIHN3aXRjaCAoZm5Ob2RlLnR5cGUpIHtcbiAgICAgICAgICAgICAgICBjYXNlICdGdW5jdGlvbkV4cHJlc3Npb24nIDogYXQgPSBmbk5vZGUuc3RhcnQ7IGJyZWFrO1xuICAgICAgICAgICAgICAgIGNhc2UgJ0Z1bmN0aW9uRGVjbGFyYXRpb24nIDogYXQgPSBmbk5vZGUuaWQuc3RhcnQ7IGJyZWFrO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgY29uc3QgaXRlbSA9IHtzdGFydDogZm5Ob2RlLnN0YXJ0LCBlbmQ6IGZuTm9kZS5lbmQsIGF0OiBhdH07XG4gICAgICAgICAgICByYW5nZXMucHVzaChpdGVtKTtcbiAgICAgICAgfVxuICAgIH0pO1xuICAgIHJldHVybiByYW5nZXM7XG59XG5cbi8vIHRyYXZlcnNlIGFic3RyYWN0IHN0YWNrIHNwYWNlXG5mdW5jdGlvbiBnZXRSZWFkYWJsZVZhck1hcCh2Yikge1xuICAgIGxldCBjdXJyVkIgPSB2YjtcbiAgICBsZXQgcmV0TWFwID0gbmV3IE1hcCgpO1xuICAgIHdoaWxlIChjdXJyVkIgIT09IG51bGwpIHtcbiAgICAgICAgbGV0IG1lcmdlZE1hcCA9IG5ldyBNYXAoKTtcbiAgICAgICAgZm9yIChsZXQgdmFyTWFwIG9mIGN1cnJWQi5pbnN0YW5jZXMudmFsdWVzKCkpIHtcbiAgICAgICAgICAgIG1lcmdlZE1hcCA9IHVuaW9uTWFwKG1lcmdlZE1hcCwgY29udmVydE1hcCh2YXJNYXApKTtcbiAgICAgICAgfVxuICAgICAgICByZXRNYXAgPSBhZGRPbmx5TWlzc2luZ01hcHBpbmdzKHJldE1hcCwgbWVyZ2VkTWFwKTtcbiAgICAgICAgY3VyclZCID0gY3VyclZCLnBhcmVuO1xuICAgIH1cbiAgICByZXR1cm4gcmV0TWFwO1xufVxuIiwidmFyIHV0aWwgPSByZXF1aXJlKCd1dGlsJyk7XG5cbmZ1bmN0aW9uIGdldE5vZGVMaXN0KGFzdCwgc3RhcnROdW0pIHtcbiAgICB2YXIgbm9kZUxpc3QgPSBbXTtcblxuICAgIHZhciBudW0gPSBzdGFydE51bSA9PT0gdW5kZWZpbmVkID8gMCA6IHN0YXJ0TnVtO1xuXG4gICAgZnVuY3Rpb24gYXNzaWduSWQobm9kZSkge1xuICAgICAgICBub2RlWydAbGFiZWwnXSA9IG51bTtcbiAgICAgICAgbm9kZUxpc3QucHVzaChub2RlKTtcbiAgICAgICAgbnVtKys7XG4gICAgfVxuXG4gICAgLy8gTGFiZWwgZXZlcnkgQVNUIG5vZGUgd2l0aCBwcm9wZXJ0eSAndHlwZSdcbiAgICBmdW5jdGlvbiBsYWJlbE5vZGVXaXRoVHlwZShub2RlKSB7XG4gICAgICAgIGlmIChub2RlICYmIG5vZGUuaGFzT3duUHJvcGVydHkoJ3R5cGUnKSkge1xuICAgICAgICAgICAgYXNzaWduSWQobm9kZSk7XG4gICAgICAgIH1cbiAgICAgICAgaWYgKG5vZGUgJiYgdHlwZW9mIG5vZGUgPT09ICdvYmplY3QnKSB7XG4gICAgICAgICAgICBmb3IgKHZhciBwIGluIG5vZGUpIHtcbiAgICAgICAgICAgICAgICBsYWJlbE5vZGVXaXRoVHlwZShub2RlW3BdKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgfVxuICAgIH1cblxuICAgIGxhYmVsTm9kZVdpdGhUeXBlKGFzdCk7XG5cbiAgICByZXR1cm4gbm9kZUxpc3Q7XG59XG5cbmZ1bmN0aW9uIHNob3dVbmZvbGRlZChvYmopIHtcbiAgICBjb25zb2xlLmxvZyh1dGlsLmluc3BlY3Qob2JqLCB7ZGVwdGg6IG51bGx9KSk7XG59XG5cbmV4cG9ydHMuZ2V0Tm9kZUxpc3QgPSBnZXROb2RlTGlzdDtcbmV4cG9ydHMuc2hvd1VuZm9sZGVkID0gc2hvd1VuZm9sZGVkO1xuIiwiLy8gaW1wb3J0IG5lY2Vzc2FyeSBsaWJyYXJpZXNcbmNvbnN0IGFjb3JuID0gcmVxdWlyZSgnYWNvcm4vZGlzdC9hY29ybicpO1xuY29uc3QgYWNvcm5fbG9vc2UgPSByZXF1aXJlKCdhY29ybi9kaXN0L2Fjb3JuX2xvb3NlJyk7XG5jb25zdCBhdXggPSByZXF1aXJlKCcuL2hlbHBlcicpO1xuaW1wb3J0ICogYXMgdHlwZXMgZnJvbSAnLi9kb21haW5zL3R5cGVzJ1xuaW1wb3J0ICogYXMgY29udGV4dCBmcm9tICcuL2RvbWFpbnMvY29udGV4dCdcbi8vIGNvbnN0IHN0YXR1cyA9IHJlcXVpcmUoJy4vZG9tYWlucy9zdGF0dXMnKTtcbmltcG9ydCAqIGFzIHN0YXR1cyBmcm9tICcuL2RvbWFpbnMvc3RhdHVzJ1xuaW1wb3J0ICogYXMgdmFyQmxvY2sgZnJvbSAnLi92YXJCbG9jaydcbmNvbnN0IGNHZW4gPSByZXF1aXJlKCcuL2NvbnN0cmFpbnQvY0dlbicpO1xuY29uc3QgdmFyUmVmcyA9IHJlcXVpcmUoJy4vdmFycmVmcycpO1xuY29uc3QgcmV0T2NjdXIgPSByZXF1aXJlKCcuL3JldE9jY3VyJyk7XG5jb25zdCB0aGlzT2NjdXIgPSByZXF1aXJlKCcuL3RoaXNPY2N1cicpO1xuaW1wb3J0ICogYXMgbXlXYWxrZXIgZnJvbSAnLi91dGlsL215V2Fsa2VyJ1xuaW1wb3J0ICogYXMgZ2V0VHlwZURhdGEgZnJvbSAnLi9nZXRUeXBlRGF0YSdcbmltcG9ydCAqIGFzIGRlZmF1bHRPcHRpb24gZnJvbSAnLi4vZGVmYXVsdE9wdGlvbidcblxuZnVuY3Rpb24gYW5hbHl6ZShpbnB1dCwgcmV0QWxsLCBvcHRpb24pIHtcbiAgICAvLyB0aGUgU2NvcGUgb2JqZWN0IGZvciBnbG9iYWwgc2NvcGVcbiAgICAvLyBzY29wZS5TY29wZS5nbG9iYWxTY29wZSA9IG5ldyBzY29wZS5TY29wZShudWxsKTtcblxuICAgIGlmIChvcHRpb24gPT09IHVuZGVmaW5lZCkge1xuICAgICAgICAvLyBpZiBubyBvcHRpb24gaXMgZ2l2ZW4sIHVzZSB0aGUgZGVmYXVsdCBvcHRpb25cbiAgICAgICAgb3B0aW9uID0gZGVmYXVsdE9wdGlvbi5vcHRpb25zO1xuICAgIH1cbiAgICAvLyBwYXJzaW5nIGlucHV0IHByb2dyYW1cbiAgICB2YXIgYXN0O1xuICAgIHRyeSB7XG4gICAgICAgIGFzdCA9IGFjb3JuLnBhcnNlKGlucHV0LCBvcHRpb24uYWNvcm5PcHRpb24pO1xuICAgIH0gY2F0Y2ggKGUpIHtcbiAgICAgICAgYXN0ID0gYWNvcm5fbG9vc2UucGFyc2VfZGFtbWl0KGlucHV0LCBvcHRpb24uYWNvcm5PcHRpb24pO1xuICAgIH1cblxuICAgIHZhciBub2RlQXJyYXlJbmRleGVkQnlMaXN0ID0gYXV4LmdldE5vZGVMaXN0KGFzdCk7XG5cbiAgICAvLyBTaG93IEFTVCBiZWZvcmUgc2NvcGUgcmVzb2x1dGlvblxuICAgIC8vIGF1eC5zaG93VW5mb2xkZWQoYXN0KTtcblxuICAgIHZhciBnVmFyQmxvY2sgPSBuZXcgdmFyQmxvY2suVmFyQmxvY2soXG4gICAgICAgIG51bGwsXG4gICAgICAgIGFzdCxcbiAgICAgICAgdmFyQmxvY2suVmFyQmxvY2suYmxvY2tUeXBlcy5nbG9iYWxCbG9jayxcbiAgICAgICAgLy8gJ3VzZSBzdHJpY3QnIGRpcmVjdGl2ZSBpcyBjaGVja2VkIGluIGFubm90YXRlQmxvY2tJbmZvLlxuICAgICAgICBvcHRpb24uYWNvcm5PcHRpb24uc291cmNlVHlwZSA9PT0gJ21vZHVsZSdcbiAgICApO1xuXG4gICAgdmFyQmxvY2suYW5ub3RhdGVCbG9ja0luZm8oYXN0LCBnVmFyQmxvY2spO1xuXG4gICAgLy8gU2V0dGluZyB1cCB0aGUgc2Vuc2l0aXZpdHkgcGFyYW1ldGVyXG4gICAgLy8gSXQgaXMgcG9zc2libGUgdG8gY29tcHV0ZSB0aGUgcGFyYW1ldGVyIGJ5IGV4YW1pbmluZyB0aGUgY29kZS5cbiAgICBjb250ZXh0LmNoYW5nZVNlbnNpdGl2aXR5UGFyYW1ldGVyKG9wdGlvbi5zZW5zaXRpdml0eVBhcmFtZXRlcik7XG5cbiAgICB2YXIgZ0Jsb2NrID0gYXN0WydAYmxvY2snXTtcbiAgICB2YXIgaW5pdGlhbENvbnRleHQgPSBjb250ZXh0LkNhbGxTaXRlQ29udGV4dC5lcHNpbG9uQ29udGV4dDtcbiAgICB2YXIgZ1Njb3BlID0gZ0Jsb2NrLmdldFNjb3BlSW5zdGFuY2UobnVsbCwgaW5pdGlhbENvbnRleHQpO1xuICAgIHZhciBnT2JqZWN0ID0gdHlwZXMubWtPYmpGcm9tR2xvYmFsU2NvcGUoZ1Njb3BlKTtcbiAgICB2YXIgaW5pdFN0YXR1cyA9IG5ldyBzdGF0dXMuU3RhdHVzKFxuICAgICAgICBuZXcgdHlwZXMuQVZhbChnT2JqZWN0KSxcbiAgICAgICAgdHlwZXMuQVZhbE51bGwsXG4gICAgICAgIHR5cGVzLkFWYWxOdWxsLFxuICAgICAgICBpbml0aWFsQ29udGV4dCxcbiAgICAgICAgZ1Njb3BlKTtcbiAgICAvLyB0aGUgcHJvdG90eXBlIG9iamVjdCBvZiBPYmplY3RcbiAgICB2YXIgT2JqUHJvdG8gPSBuZXcgdHlwZXMuT2JqVHlwZShudWxsLCAnT2JqZWN0LnByb3RvdHlwZScpO1xuICAgIHZhciBydENYID0ge1xuICAgICAgICBnbG9iYWxPYmplY3Q6IGdPYmplY3QsXG4gICAgICAgIC8vIHRlbXBvcmFsXG4gICAgICAgIHByb3Rvczoge1xuICAgICAgICAgICAgT2JqZWN0OiBPYmpQcm90byxcbiAgICAgICAgICAgIEZ1bmN0aW9uOiBuZXcgdHlwZXMuT2JqVHlwZShuZXcgdHlwZXMuQVZhbChPYmpQcm90byksICdGdW5jdGlvbi5wcm90b3R5cGUnKSxcbiAgICAgICAgICAgIEFycmF5OiBuZXcgdHlwZXMuT2JqVHlwZShuZXcgdHlwZXMuQVZhbChPYmpQcm90byksICdBcnJheS5wcm90b3R5cGUnKSxcbiAgICAgICAgICAgIFJlZ0V4cDogbmV3IHR5cGVzLk9ialR5cGUobmV3IHR5cGVzLkFWYWwoT2JqUHJvdG8pLCAnUmVnRXhwLnByb3RvdHlwZScpLFxuICAgICAgICAgICAgU3RyaW5nOiBuZXcgdHlwZXMuT2JqVHlwZShuZXcgdHlwZXMuQVZhbChPYmpQcm90byksICdTdHJpbmcucHJvdG90eXBlJyksXG4gICAgICAgICAgICBOdW1iZXI6IG5ldyB0eXBlcy5PYmpUeXBlKG5ldyB0eXBlcy5BVmFsKE9ialByb3RvKSwgJ051bWJlci5wcm90b3R5cGUnKSxcbiAgICAgICAgICAgIEJvb2xlYW46IG5ldyB0eXBlcy5PYmpUeXBlKG5ldyB0eXBlcy5BVmFsKE9ialByb3RvKSwgJ0Jvb2xlYW4ucHJvdG90eXBlJylcbiAgICAgICAgfSxcbiAgICAgICAgxIg6IG5ldyB0eXBlcy5BYnNDYWNoZSgpLFxuICAgICAgICBvcHRpb246IG9wdGlvblxuICAgIH07XG4gICAgY0dlbi5hZGRDb25zdHJhaW50cyhhc3QsIGluaXRTdGF0dXMsIHJ0Q1gpO1xuICAgIC8vYXV4LnNob3dVbmZvbGRlZChnQmxvY2tBbmRBbm5vdGF0ZWRBU1QuYXN0KTtcbiAgICAvLyBhdXguc2hvd1VuZm9sZGVkKGNvbnN0cmFpbnRzKTtcbiAgICAvLyBhdXguc2hvd1VuZm9sZGVkKGdCbG9jayk7XG4gICAgLy8gY29uc29sZS5sb2codXRpbC5pbnNwZWN0KGdCbG9jaywge2RlcHRoOiAxMH0pKTtcbiAgICBpZiAocmV0QWxsKSB7XG4gICAgICAgIHJldHVybiB7XG4gICAgICAgICAgICBnT2JqZWN0OiBnT2JqZWN0LFxuICAgICAgICAgICAgQVNUOiBhc3QsXG4gICAgICAgICAgICBnQmxvY2s6IGdCbG9jayxcbiAgICAgICAgICAgIGdTY29wZTogZ1Njb3BlLFxuICAgICAgICAgICAgxIg6IHJ0Q1guxIhcbiAgICAgICAgfTtcbiAgICB9IGVsc2Uge1xuICAgICAgICByZXR1cm4gZ09iamVjdDtcbiAgICB9XG59XG5cbmV4cG9ydHMuYW5hbHl6ZSA9IGFuYWx5emU7XG5leHBvcnRzLmZpbmRJZGVudGlmaWVyQXQgPSBteVdhbGtlci5maW5kSWRlbnRpZmllckF0O1xuZXhwb3J0cy5maW5kVmFyUmVmc0F0ID0gdmFyUmVmcy5maW5kVmFyUmVmc0F0O1xuZXhwb3J0cy5vbkVzY2FwaW5nU3RhdGVtZW50ID0gcmV0T2NjdXIub25Fc2NhcGluZ1N0YXRlbWVudDtcbmV4cG9ydHMuZmluZEVzY2FwaW5nU3RhdGVtZW50cyA9IHJldE9jY3VyLmZpbmRFc2NhcGluZ1N0YXRlbWVudHM7XG5leHBvcnRzLm9uVGhpc0tleXdvcmQgPSB0aGlzT2NjdXIub25UaGlzS2V5d29yZDtcbmV4cG9ydHMuZmluZFRoaXNFeHByZXNzaW9ucyA9IHRoaXNPY2N1ci5maW5kVGhpc0V4cHJlc3Npb25zO1xuZXhwb3J0cy5maW5kU3Vycm91bmRpbmdOb2RlID0gbXlXYWxrZXIuZmluZFN1cnJvdW5kaW5nTm9kZTtcbmV4cG9ydHMuZmluZE1lbWJlck9yVmFyaWFibGVBdCA9IG15V2Fsa2VyLmZpbmRNZW1iZXJPclZhcmlhYmxlQXQ7XG5leHBvcnRzLmdldFR5cGVEYXRhID0gZ2V0VHlwZURhdGEuZ2V0VHlwZUF0UmFuZ2U7XG5leHBvcnRzLmdldENvbXBsZXRpb25BdFBvcyA9IGdldFR5cGVEYXRhLmdldENvbXBsZXRpb25BdFBvcztcbmV4cG9ydHMuZ2V0Rm5UeXBlU3RydWN0dXJlc0F0ID0gZ2V0VHlwZURhdGEuZ2V0Rm5UeXBlU3RydWN0dXJlc0F0O1xuZXhwb3J0cy5nZXREZWZpbml0aW9uU2l0ZXNBdCA9IGdldFR5cGVEYXRhLmdldERlZmluaXRpb25TaXRlc0F0O1xuIiwiY29uc3Qgd2FsayA9IHJlcXVpcmUoJ2Fjb3JuL2Rpc3Qvd2FsaycpO1xuaW1wb3J0ICogYXMgbXlXYWxrZXIgZnJvbSAnLi91dGlsL215V2Fsa2VyJ1xuXG4vKipcbiAqIGF1eGlsaWFyeSBmdW5jdGlvbiBmb3IgdmlzaXRvcidzIHN0YXRlIGNoYW5nZVxuICogQHBhcmFtIG5vZGVcbiAqIEBwYXJhbSBzdFxuICogQHBhcmFtIG5vZGVUeXBlXG4gKiBAcmV0dXJucyB7Kn1cbiAqL1xuZnVuY3Rpb24gc3RDaGFuZ2Uobm9kZSwgc3QsIG5vZGVUeXBlKSB7XG4gICAgY29uc3QgW2ZuTm9kZSwgdHJ5Tm9kZSwgb3V0ZXJUcnlOb2RlXSA9IHN0O1xuICAgIHN3aXRjaCAobm9kZVR5cGUpIHtcbiAgICAgICAgY2FzZSAnRnVuY3Rpb25EZWNsYXJhdGlvbic6XG4gICAgICAgIGNhc2UgJ0Z1bmN0aW9uRXhwcmVzc2lvbic6XG4gICAgICAgIGNhc2UgJ0Fycm93RnVuY3Rpb25FeHByZXNzaW9uJzpcbiAgICAgICAgICAgIHJldHVybiBbbm9kZSwgdW5kZWZpbmVkXTtcbiAgICAgICAgY2FzZSAnVHJ5U3RhdGVtZW50JzpcbiAgICAgICAgICAgIC8vIHJlbWVtYmVyIG91dGVyIHRyeU5vZGVcbiAgICAgICAgICAgIHJldHVybiBbZm5Ob2RlLCBub2RlLCB0cnlOb2RlXTtcbiAgICAgICAgY2FzZSAnQ2F0Y2hDbGF1c2UnOlxuICAgICAgICAgICAgLy8gdXNlIG91dGVyIHRyeSBhcyBpdHMgdHJ5Tm9kZVxuICAgICAgICAgICAgcmV0dXJuIFtmbk5vZGUsIG91dGVyVHJ5Tm9kZV07XG4gICAgICAgIGNhc2UgJ0Jsb2NrU3RhdGVtZW50JzpcbiAgICAgICAgICAgIGlmIChzdC5vdXRlcikge1xuICAgICAgICAgICAgICAgIC8vIGl0J3MgZmluYWxseSBibG9ja1xuICAgICAgICAgICAgICAgIHJldHVybiBbZm5Ob2RlLCBvdXRlclRyeU5vZGVdO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgLy8gaXQncyB0cnkgYmxvY2tcbiAgICAgICAgICAgICAgICByZXR1cm4gW2ZuTm9kZSwgdHJ5Tm9kZSwgb3V0ZXJUcnlOb2RlXTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgZGVmYXVsdDpcbiAgICAgICAgICAgIHJldHVybiBbZm5Ob2RlLCB0cnlOb2RlLCBvdXRlclRyeU5vZGVdO1xuICAgIH1cbn1cblxuLyoqXG4gKiBDaGVjayB3aGV0aGVyIGdpdmVuIHBvcyBpcyBvbiBhIGZ1bmN0aW9uIGtleXdvcmRcbiAqIEBwYXJhbSBhc3QgLSBBU1Qgb2YgYSBwcm9ncmFtXG4gKiBAcGFyYW0gcG9zIC0gaW5kZXggcG9zaXRpb25cbiAqIEByZXR1cm5zIHsqfSAtIGZ1bmN0aW9uIG5vZGUgb3IgbnVsbFxuICovXG5mdW5jdGlvbiBvbkVzY2FwaW5nU3RhdGVtZW50KGFzdCwgcG9zKSB7XG4gICAgJ3VzZSBzdHJpY3QnO1xuXG4gICAgLy8gZmluZCBmdW5jdGlvbiBub2RlXG4gICAgLy8gc3QgaXMgdGhlIGVuY2xvc2luZyBmdW5jdGlvblxuICAgIGNvbnN0IHdhbGtlciA9IG15V2Fsa2VyLndyYXBXYWxrZXIod2Fsay5tYWtlKHtcbiAgICAgICAgICAgIFRyeVN0YXRlbWVudDogKG5vZGUsIHN0LCBjKSA9PiB7XG4gICAgICAgICAgICAgICAgYyhub2RlLmJsb2NrLCBzdCk7XG4gICAgICAgICAgICAgICAgLy8gc2V0IGZsYWcgYWZ0ZXIgcHJvY2Vzc2luZyB0cnkgYmxvY2tcbiAgICAgICAgICAgICAgICBzdC5vdXRlciA9IHRydWU7XG4gICAgICAgICAgICAgICAgaWYgKG5vZGUuaGFuZGxlcikgYyhub2RlLmhhbmRsZXIsIHN0KTtcbiAgICAgICAgICAgICAgICBpZiAobm9kZS5maW5hbGl6ZXIpIGMobm9kZS5maW5hbGl6ZXIsIHN0KTtcbiAgICAgICAgICAgIH0sXG4gICAgICAgICAgICBDYXRjaENsYXVzZTogKG5vZGUsIHN0LCBjKSA9PiB7XG4gICAgICAgICAgICAgICAgYyhub2RlLmJvZHksIHN0KTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgfSwgd2Fsay5iYXNlKSxcbiAgICAgICAgLy8gcHJlXG4gICAgICAgIChub2RlLCBzdCwgbm9kZVR5cGUpID0+IHtcbiAgICAgICAgICAgIGlmIChub2RlLnN0YXJ0ID4gcG9zIHx8IG5vZGUuZW5kIDwgcG9zKSB7XG4gICAgICAgICAgICAgICAgcmV0dXJuIGZhbHNlO1xuICAgICAgICAgICAgfVxuXG4gICAgICAgICAgICAvLyBvbiBhIGZ1bmN0aW9uIGtleXdvcmQsIDggaXMgdGhlIGxlbmd0aCBvZiAnZnVuY3Rpb24nXG4gICAgICAgICAgICAvLyBvciBvbiByZXR1cm4ga2V5d29yZCwgNiBpcyB0aGUgbGVuZ3RoIG9mICdyZXR1cm4nXG4gICAgICAgICAgICAvLyBvciBvbiB0aHJvdyBrZXl3b3JkLCA1IGlzIHRoZSBsZW5ndGggb2YgJ3Rocm93J1xuICAgICAgICAgICAgaWYgKCgobm9kZVR5cGUgPT09ICdGdW5jdGlvbkRlY2xhcmF0aW9uJyB8fCBub2RlVHlwZSA9PT0gJ0Z1bmN0aW9uRXhwcmVzc2lvbicpXG4gICAgICAgICAgICAgICAgJiYgKG5vZGUuc3RhcnQgPD0gcG9zICYmIHBvcyA8PSBub2RlLnN0YXJ0ICsgOCkpXG4gICAgICAgICAgICAgICAgfHxcbiAgICAgICAgICAgICAgICAobm9kZVR5cGUgPT09ICdSZXR1cm5TdGF0ZW1lbnQnXG4gICAgICAgICAgICAgICAgJiYgKG5vZGUuc3RhcnQgPD0gcG9zICYmIHBvcyA8PSBub2RlLnN0YXJ0ICsgNikpXG4gICAgICAgICAgICAgICAgfHxcbiAgICAgICAgICAgICAgICAobm9kZVR5cGUgPT09ICdUaHJvd1N0YXRlbWVudCdcbiAgICAgICAgICAgICAgICAmJiAobm9kZS5zdGFydCA8PSBwb3MgJiYgcG9zIDw9IG5vZGUuc3RhcnQgKyA1KSkpIHtcbiAgICAgICAgICAgICAgICAvLyByZWNvcmQgdGhlIGZvdW5kIG5vZGUgdHlwZVxuICAgICAgICAgICAgICAgIHN0LnR5cGUgPSBub2RlLnR5cGU7XG4gICAgICAgICAgICAgICAgdGhyb3cgc3Q7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICByZXR1cm4gdHJ1ZTtcbiAgICAgICAgfSxcbiAgICAgICAgLy8gcG9zdFxuICAgICAgICB1bmRlZmluZWQsXG4gICAgICAgIC8vIHN0Q2hhbmdlXG4gICAgICAgIHN0Q2hhbmdlXG4gICAgKTtcblxuICAgIHRyeSB7XG4gICAgICAgIHdhbGsucmVjdXJzaXZlKGFzdCwgW10sIHdhbGtlcik7XG4gICAgfSBjYXRjaCAoZSkge1xuICAgICAgICBpZiAoZSAmJiBlIGluc3RhbmNlb2YgQXJyYXkpIHtcbiAgICAgICAgICAgIC8vIGZvdW5kXG4gICAgICAgICAgICByZXR1cm4gZTtcbiAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICAgIC8vIG90aGVyIGVycm9yXG4gICAgICAgICAgICB0aHJvdyBlO1xuICAgICAgICB9XG4gICAgfVxuICAgIC8vIGlkZW50aWZpZXIgbm90IGZvdW5kXG4gICAgcmV0dXJuIG51bGw7XG59XG5cbi8qKlxuICogR2l2ZW4gYSBub2RlLCBmaW5kIGl0cyBlc2NhcGluZyBub2Rlc1xuICpcbiAqIEBwYXJhbSBub2RlUGFpciAtIEFTVCBub2RlIG9mIGEgZnVuY3Rpb24sIHBvc3NpYmx5IHdpdGggbm8gYW5ub3RhdGlvblxuICogQHJldHVybnMgeyp9IC0gYXJyYXkgb2YgQVNUIG5vZGVzXG4gKi9cbmZ1bmN0aW9uIGdldEVzY2FwaW5nTm9kZXMobm9kZVBhaXIpIHtcbiAgICAndXNlIHN0cmljdCc7XG4gICAgY29uc3Qgbm9kZXMgPSBbXTtcbiAgICBjb25zdCBbZm5Ob2RlLCB0cnlOb2RlXSA9IG5vZGVQYWlyO1xuXG4gICAgY29uc3Qgd2Fsa2VyID0gbXlXYWxrZXIud3JhcFdhbGtlcihcbiAgICAgICAgd2Fsay5tYWtlKHtcbiAgICAgICAgICAgIFRyeVN0YXRlbWVudDogKG5vZGUsIHN0LCBjKSA9PiB7XG4gICAgICAgICAgICAgICAgYyhub2RlLmJsb2NrLCBzdCk7XG4gICAgICAgICAgICAgICAgLy8gc2V0IGZsYWcgYWZ0ZXIgcHJvY2Vzc2luZyB0cnkgYmxvY2tcbiAgICAgICAgICAgICAgICBzdC5vdXRlciA9IHRydWU7XG4gICAgICAgICAgICAgICAgLy8gdmlzaXQgdGhvc2UgQmxvY2tTdGF0ZW1lbnRcbiAgICAgICAgICAgICAgICBpZiAobm9kZS5oYW5kbGVyKSBjKG5vZGUuaGFuZGxlciwgc3QpO1xuICAgICAgICAgICAgICAgIGlmIChub2RlLmZpbmFsaXplcikgYyhub2RlLmZpbmFsaXplciwgc3QpO1xuICAgICAgICAgICAgfSxcbiAgICAgICAgICAgIFJldHVyblN0YXRlbWVudDogKG5vZGUpID0+IHtcbiAgICAgICAgICAgICAgICBpZiAobm9kZVBhaXIudHlwZSA9PT0gJ1Rocm93U3RhdGVtZW50JyAmJiB0cnlOb2RlKSByZXR1cm47XG4gICAgICAgICAgICAgICAgbm9kZXMucHVzaChub2RlKTtcbiAgICAgICAgICAgIH0sXG4gICAgICAgICAgICBGdW5jdGlvbjogKCkgPT4ge1xuICAgICAgICAgICAgICAgIC8vIG5vdCB2aXNpdCBpbm5lciBmdW5jdGlvbnNcbiAgICAgICAgICAgIH0sXG4gICAgICAgICAgICBUaHJvd1N0YXRlbWVudDogKG5vZGUsIFtmLHRdKSA9PiB7XG4gICAgICAgICAgICAgICAgaWYgKChub2RlUGFpci50eXBlID09PSAnVGhyb3dTdGF0ZW1lbnQnICYmIHRyeU5vZGUgPT09IHQpXG4gICAgICAgICAgICAgICAgICAgIHx8IHQgPT09IHVuZGVmaW5lZCkge1xuICAgICAgICAgICAgICAgICAgICBub2Rlcy5wdXNoKG5vZGUpO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgIH0sXG4gICAgICAgICAgICBDYXRjaENsYXVzZTogKG5vZGUsIHN0LCBjKSA9PiB7XG4gICAgICAgICAgICAgICAgYyhub2RlLmJvZHksIHN0KTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgfSwgd2Fsay5iYXNlKSxcbiAgICAgICAgdW5kZWZpbmVkLFxuICAgICAgICB1bmRlZmluZWQsXG4gICAgICAgIHN0Q2hhbmdlKTtcblxuICAgIGlmIChub2RlUGFpci50eXBlID09PSAnVGhyb3dTdGF0ZW1lbnQnICYmIHRyeU5vZGUpIHtcbiAgICAgICAgd2Fsay5yZWN1cnNpdmUodHJ5Tm9kZS5ibG9jaywgW3VuZGVmaW5lZCwgdHJ5Tm9kZV0sIHdhbGtlcik7XG4gICAgfSBlbHNlIHtcbiAgICAgICAgd2Fsay5yZWN1cnNpdmUoZm5Ob2RlLmJvZHksIFtmbk5vZGUsIHVuZGVmaW5lZF0sIHdhbGtlcik7XG4gICAgfVxuXG4gICAgcmV0dXJuIG5vZGVzO1xufVxuXG4vKipcbiAqIEZpbmQgcmV0dXJuIG5vZGVzIGNvcnJlc3BvbmRpbmcgdG8gdGhlIHBvc2l0aW9uXG4gKiBpZiB0aGUgcG9zIGlzIG9uIGEgZnVuY3Rpb24ga2V5d29yZFxuICpcbiAqIEBwYXJhbSBhc3QgLSBBU1Qgbm9kZSBvZiBhIHByb2dyYW0sIHBvc3NpYmx5IHdpdGggbm8gYW5ub3RhdGlvblxuICogQHBhcmFtIHBvcyAtIGN1cnNvciBwb3NpdGlvblxuICogQHBhcmFtIGluY2x1ZGVLZXl3b3JkIC0gd2hldGhlciB0byBpbmNsdWRlIGtleXdvcmQgcmFuZ2VcbiAqIEByZXR1cm5zIHtBcnJheX0gLSBhcnJheSBvZiBBU1Qgbm9kZXMgb2YgZXNjYXBpbmcgc3RhdGVtZW50c1xuICovXG5mdW5jdGlvbiBmaW5kRXNjYXBpbmdTdGF0ZW1lbnRzKGFzdCwgcG9zLCBpbmNsdWRlS2V5d29yZCkge1xuICAgICd1c2Ugc3RyaWN0JztcblxuICAgIGNvbnN0IG5vZGVQYWlyID0gb25Fc2NhcGluZ1N0YXRlbWVudChhc3QsIHBvcyk7XG4gICAgaWYgKCFub2RlUGFpcikge1xuICAgICAgICByZXR1cm4gbnVsbDtcbiAgICB9XG5cbiAgICBjb25zdCByYW5nZXMgPSBnZXRFc2NhcGluZ05vZGVzKG5vZGVQYWlyKS5tYXAoXG4gICAgICAgICAgICBub2RlID0+IHtcbiAgICAgICAgICAgICAgICByZXR1cm4ge3N0YXJ0OiBub2RlLnN0YXJ0LCBlbmQ6IG5vZGUuZW5kfTtcbiAgICAgICAgICAgIH0pO1xuICAgIGNvbnN0IFtmbk5vZGUsIHRyeU5vZGVdID0gbm9kZVBhaXI7XG4gICAgLy8gSWYgbm8gZXhwbGljaXQgZXNjYXBpbmcgZXhpc3RzXG4gICAgLy8gaGlnaGxpZ2h0IHRoZSBjbG9zaW5nIGJyYWNlIG9mIHRoZSBmdW5jdGlvbiBib2R5XG4gICAgaWYgKG5vZGVQYWlyLnR5cGUgIT09ICdUaHJvd1N0YXRlbWVudCcgJiYgcmFuZ2VzLmxlbmd0aCA9PT0gMCkge1xuICAgICAgICByYW5nZXMucHVzaCh7c3RhcnQ6IGZuTm9kZS5lbmQgLSAxLCBlbmQ6IGZuTm9kZS5lbmR9KTtcbiAgICB9XG5cbiAgICAvLyBoaWdobGlnaHRpbmcgJ2NhdGNoJ1xuICAgIGlmIChub2RlUGFpci50eXBlID09PSAnVGhyb3dTdGF0ZW1lbnQnICYmIHRyeU5vZGUpIHtcbiAgICAgICAgcmFuZ2VzLnB1c2goe3N0YXJ0OiB0cnlOb2RlLmhhbmRsZXIuc3RhcnQsIGVuZDogdHJ5Tm9kZS5oYW5kbGVyLnN0YXJ0ICsgNX0pO1xuICAgIH0gZWxzZSBpZiAoaW5jbHVkZUtleXdvcmQpIHtcbiAgICAgICAgaWYgKGZuTm9kZS50eXBlICE9PSAnQXJyb3dGdW5jdGlvbkV4cHJlc3Npb24nKSB7XG4gICAgICAgICAgICAvLyBhZGQgcmFuZ2VzIGZvciAnZnVuY3Rpb24nXG4gICAgICAgICAgICByYW5nZXMucHVzaCh7c3RhcnQ6IGZuTm9kZS5zdGFydCwgZW5kOiBmbk5vZGUuc3RhcnQgKyA4fSk7XG4gICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgICAvLyBUT0RPOiBhZGQgcmFuZ2UgZm9yIGZhdCBhcnJvd1xuICAgICAgICB9XG4gICAgfVxuICAgIHJldHVybiByYW5nZXM7XG59XG5cbmV4cG9ydHMub25Fc2NhcGluZ1N0YXRlbWVudCA9IG9uRXNjYXBpbmdTdGF0ZW1lbnQ7XG5leHBvcnRzLmZpbmRFc2NhcGluZ1N0YXRlbWVudHMgPSBmaW5kRXNjYXBpbmdTdGF0ZW1lbnRzO1xuIiwiY29uc3Qgd2FsayA9IHJlcXVpcmUoJ2Fjb3JuL2Rpc3Qvd2FsaycpO1xuaW1wb3J0ICogYXMgbXlXYWxrZXIgZnJvbSAnLi91dGlsL215V2Fsa2VyJ1xuXG4vKipcbiAqIENoZWNrIHdoZXRoZXIgZ2l2ZW4gcG9zIGlzIG9uIGEgdGhpcyBrZXl3b3JkXG4gKiBAcGFyYW0gYXN0IC0gQVNUIG9mIGEgcHJvZ3JhbVxuICogQHBhcmFtIHBvcyAtIGluZGV4IHBvc2l0aW9uXG4gKiBAcmV0dXJucyB7Kn0gLSBmdW5jdGlvbiBub2RlIG9yIG51bGxcbiAqL1xuZnVuY3Rpb24gb25UaGlzS2V5d29yZChhc3QsIHBvcykge1xuICAgICd1c2Ugc3RyaWN0JztcblxuICAgIC8vIGZpbmQgZnVuY3Rpb24gbm9kZVxuICAgIC8vIHN0IGlzIHRoZSBlbmNsb3NpbmcgZnVuY3Rpb25cbiAgICBjb25zdCB3YWxrZXIgPSBteVdhbGtlci53cmFwV2Fsa2VyKHdhbGsuYmFzZSxcbiAgICAgICAgLy8gcHJlXG4gICAgICAgIChub2RlLCBzdCkgPT4ge1xuICAgICAgICAgICAgaWYgKG5vZGUuc3RhcnQgPiBwb3MgfHwgbm9kZS5lbmQgPCBwb3MpIHtcbiAgICAgICAgICAgICAgICByZXR1cm4gZmFsc2U7XG4gICAgICAgICAgICB9XG5cbiAgICAgICAgICAgIGlmIChub2RlLnR5cGUgPT09ICdUaGlzRXhwcmVzc2lvbicpIHtcbiAgICAgICAgICAgICAgICB0aHJvdyBzdDtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIHJldHVybiB0cnVlO1xuICAgICAgICB9LFxuICAgICAgICAvLyBwb3N0XG4gICAgICAgIHVuZGVmaW5lZCxcbiAgICAgICAgLy8gc3RDaGFuZ2VcbiAgICAgICAgKG5vZGUsIHN0KSA9PiB7XG4gICAgICAgICAgICBpZiAobm9kZS50eXBlID09PSAnRnVuY3Rpb25EZWNsYXJhdGlvbidcbiAgICAgICAgICAgICAgICB8fCBub2RlLnR5cGUgPT09ICdGdW5jdGlvbkV4cHJlc3Npb24nKSB7XG4gICAgICAgICAgICAgICAgcmV0dXJuIG5vZGU7XG4gICAgICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgICAgICAgIHJldHVybiBzdDtcbiAgICAgICAgICAgIH1cbiAgICAgICAgfSk7XG5cbiAgICB0cnkge1xuICAgICAgICB3YWxrLnJlY3Vyc2l2ZShhc3QsIHVuZGVmaW5lZCwgd2Fsa2VyKTtcbiAgICB9IGNhdGNoIChlKSB7XG4gICAgICAgIGlmIChlICYmIGUudHlwZSAmJlxuICAgICAgICAgICAgKGUudHlwZSA9PT0gJ0Z1bmN0aW9uRXhwcmVzc2lvbidcbiAgICAgICAgICAgIHx8IGUudHlwZSA9PT0gJ0Z1bmN0aW9uRGVjbGFyYXRpb24nKSkge1xuICAgICAgICAgICAgcmV0dXJuIGU7XG4gICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgICB0aHJvdyBlO1xuICAgICAgICB9XG4gICAgfVxuICAgIC8vIGlkZW50aWZpZXIgbm90IGZvdW5kXG4gICAgcmV0dXJuIG51bGw7XG59XG5cbi8qKlxuICogR2l2ZW4gYSBmdW5jdGlvbiBub2RlLCBmaW5kIGl0cyB0aGlzIG5vZGVzXG4gKlxuICogQHBhcmFtIGZOb2RlIC0gQVNUIG5vZGUgb2YgYSBmdW5jdGlvbiwgcG9zc2libHkgd2l0aCBubyBhbm5vdGF0aW9uXG4gKiBAcmV0dXJucyB7Kn0gLSBhcnJheSBvZiBBU1Qgbm9kZXNcbiAqL1xuZnVuY3Rpb24gZ2V0VGhpc05vZGVzKGZOb2RlKSB7XG4gICAgJ3VzZSBzdHJpY3QnO1xuICAgIGNvbnN0IHJldHMgPSBbXTtcbiAgICBpZiAoZk5vZGUudHlwZSAhPT0gJ0Z1bmN0aW9uRXhwcmVzc2lvbidcbiAgICAgICAgJiYgZk5vZGUudHlwZSAhPT0gJ0Z1bmN0aW9uRGVjbGFyYXRpb24nKSB7XG4gICAgICAgIHRocm93IEVycm9yKCdmTm9kZSBzaG91bGQgYmUgYSBmdW5jdGlvbiBub2RlJyk7XG4gICAgfVxuXG4gICAgY29uc3Qgd2Fsa2VyID0gd2Fsay5tYWtlKHtcbiAgICAgICAgVGhpc0V4cHJlc3Npb246IChub2RlKSA9PiB7XG4gICAgICAgICAgICByZXR1cm4gcmV0cy5wdXNoKG5vZGUpO1xuICAgICAgICB9LFxuICAgICAgICBGdW5jdGlvbkRlY2xhcmF0aW9uOiAoKSA9PiB7XG4gICAgICAgICAgICAvLyBub3QgdmlzaXQgZnVuY3Rpb24gZGVjbGFyYXRpb25cbiAgICAgICAgfSxcbiAgICAgICAgRnVuY3Rpb25FeHByZXNzaW9uOiAoKSA9PiB7XG4gICAgICAgICAgICAvLyBub3QgdmlzaXQgZnVuY3Rpb24gZXhwcmVzc2lvblxuICAgICAgICB9XG4gICAgfSwgd2Fsay5iYXNlKTtcblxuICAgIHdhbGsucmVjdXJzaXZlKGZOb2RlLmJvZHksIHVuZGVmaW5lZCwgd2Fsa2VyKTtcblxuICAgIHJldHVybiByZXRzO1xufVxuXG4vKipcbiAqIEZpbmQgdGhpcyBub2RlcyBpZiB0aGUgcG9zIGlzIG9uIGEgdGhpcyBrZXl3b3JkXG4gKlxuICogQHBhcmFtIGFzdCAtIEFTVCBub2RlIG9mIGEgcHJvZ3JhbSwgcG9zc2libHkgd2l0aCBubyBhbm5vdGF0aW9uXG4gKiBAcGFyYW0gcG9zIC0gY3Vyc29yIHBvc2l0aW9uXG4gKiBAcGFyYW0gaW5jbHVkZUZ1bmN0aW9uS2V5d29yZCAtIHdoZXRoZXIgdG8gaW5jbHVkZSBmdW5jdGlvbiBrZXl3b3JkIHJhbmdlXG4gKiBAcmV0dXJucyB7QXJyYXl9IC0gYXJyYXkgb2YgQVNUIG5vZGVzIG9mIHJldHVybiBzdGF0ZW1lbnRzXG4gKi9cbmZ1bmN0aW9uIGZpbmRUaGlzRXhwcmVzc2lvbnMoYXN0LCBwb3MsIGluY2x1ZGVGdW5jdGlvbktleXdvcmQpIHtcbiAgICAndXNlIHN0cmljdCc7XG5cbiAgICBjb25zdCBmTm9kZSA9IG9uVGhpc0tleXdvcmQoYXN0LCBwb3MpO1xuICAgIGlmICghZk5vZGUpIHtcbiAgICAgICAgLy8gcG9zIGlzIG5vdCBvbiB0aGlzIGtleXdvcmRcbiAgICAgICAgcmV0dXJuIG51bGw7XG4gICAgfVxuXG4gICAgY29uc3QgcmV0cyA9IGdldFRoaXNOb2RlcyhmTm9kZSk7XG4gICAgaWYgKGluY2x1ZGVGdW5jdGlvbktleXdvcmQpIHtcbiAgICAgICAgcmV0cy5wdXNoKHtzdGFydDogZk5vZGUuc3RhcnQsIGVuZDogZk5vZGUuc3RhcnQgKyA4fSk7XG4gICAgfVxuICAgIHJldHVybiByZXRzO1xufVxuXG5leHBvcnRzLm9uVGhpc0tleXdvcmQgPSBvblRoaXNLZXl3b3JkO1xuZXhwb3J0cy5maW5kVGhpc0V4cHJlc3Npb25zID0gZmluZFRoaXNFeHByZXNzaW9ucztcbiIsImNvbnN0IHdhbGsgPSByZXF1aXJlKCdhY29ybi9kaXN0L3dhbGsnKTtcblxuLyoqXG4gKiBSZXR1cm5zIGEgd2Fsa2VyIHRoYXQgZG9lcyBub3RoaW5nIGZvciBlYWNoIG5vZGUuXG4gKiBVc2UgYXMgYSBiYXNlIHdhbGtlciB3aGVuIHlvdSBuZWVkIHRvIHdhbGsgb24gb25seSBzb21lIHR5cGVzIG9mIG5vZGVzLlxuICogQHJldHVybnMge09iamVjdH1cbiAqL1xuZnVuY3Rpb24gbWFrZU5vb3BXYWxrZXIoKSB7XG4gICAgY29uc3Qgd2Fsa2VyID0gT2JqZWN0LmNyZWF0ZShudWxsKTtcbiAgICBjb25zdCBub29wRnVuYyA9ICgpID0+IHt9O1xuICAgIGZvciAobGV0IG5hbWUgaW4gT2JqZWN0LmdldE93blByb3BlcnR5TmFtZXMod2Fsay5iYXNlKSkge1xuICAgICAgICB3YWxrZXJbbmFtZV0gPSBub29wRnVuYztcbiAgICB9XG4gICAgcmV0dXJuIHdhbGtlcjtcbn1cbmV4cG9ydCBjb25zdCBub29wV2Fsa2VyID0gbWFrZU5vb3BXYWxrZXIoKTtcblxuLyoqXG4gKiBDaGVjayB3aGV0aGVyIHRoZSBwYXR0ZXJuIHVzZXMgZGVmYXVsdHNcbiAqIEBwYXJhbSBwdG5Ob2RlIC0gYSBwYXR0ZXJuIG5vZGVcbiAqIEByZXR1cm5zIHtib29sZWFufVxuICovXG5leHBvcnQgZnVuY3Rpb24gcGF0dGVybkhhc0RlZmF1bHRzKHB0bk5vZGUpIHtcbiAgICBjb25zdCBhc3NpZ25tZW50UGF0dGVybkZpbmRlciA9IHdhbGsubWFrZShub29wV2Fsa2VyLCB7XG4gICAgICAgIEFzc2lnbm1lbnRQYXR0ZXJuOiAobm9kZSwgc3QsIGMpID0+IHtcbiAgICAgICAgICAgIHRocm93IG5ldyBGb3VuZCgpO1xuICAgICAgICB9LFxuICAgICAgICBPYmplY3RQYXR0ZXJuOiB3YWxrLmJhc2UuT2JqZWN0UGF0dGVybixcbiAgICAgICAgQXJyYXlQYXR0ZXJuOiB3YWxrLmJhc2UuQXJyYXlFeHByZXNzaW9uLFxuICAgICAgICBSZXN0RWxlbWVudDogd2Fsay5iYXNlLlJlc3RFbGVtZW50XG4gICAgfSk7XG5cbiAgICB0cnkge1xuICAgICAgICB3YWxrLnJlY3Vyc2l2ZShwdG5Ob2RlLCB1bmRlZmluZWQsIGFzc2lnbm1lbnRQYXR0ZXJuRmluZGVyKTtcbiAgICB9IGNhdGNoIChlKSB7XG4gICAgICAgIGlmIChlIGluc3RhbmNlb2YgRm91bmQpIHtcbiAgICAgICAgICAgIHJldHVybiB0cnVlO1xuICAgICAgICB9XG4gICAgfVxuICAgIHJldHVybiBmYWxzZTtcbn1cblxuLyoqXG4gKiBhIHdhbGtlciB0aGF0IHZpc2l0cyBlYWNoIGlkIGV2ZW4gdGhvdWdoIGl0IGlzIHZhciBkZWNsYXJhdGlvblxuICogdGhlIHBhcmFtZXRlciB2YiBkZW5vdGUgdmFyQmxvY2tcbiAqL1xuZXhwb3J0IGNvbnN0IHZhcldhbGtlciA9IHdhbGsubWFrZSh7XG4gICAgRnVuY3Rpb246IChub2RlLCB2YiwgYykgPT4ge1xuICAgICAgICBpZiAobm9kZS5pZCkgYyhub2RlLmlkLCB2YiwgJ1BhdHRlcm4nKTtcbiAgICAgICAgY29uc3QgcGFyYW1WYiA9IG5vZGVbJ0BibG9jayddIHx8IG5vZGUuYm9keVsnQGJsb2NrJ107XG4gICAgICAgIGZvciAobGV0IGkgPSAwOyBpIDwgbm9kZS5wYXJhbXMubGVuZ3RoOyBpKyspIHtcbiAgICAgICAgICAgIGMobm9kZS5wYXJhbXNbaV0sIHBhcmFtVmIsICdQYXR0ZXJuJyk7XG4gICAgICAgIH1cbiAgICAgICAgY29uc3QgaW5uZXJWYiA9IG5vZGUuYm9keVsnQGJsb2NrJ107XG4gICAgICAgIGMobm9kZS5ib2R5LCBpbm5lclZiLCBub2RlLmV4cHJlc3Npb24gPyAnU2NvcGVFeHByZXNzaW9uJyA6ICdTY29wZUJvZHknKTtcbiAgICB9LFxuICAgIEZvclN0YXRlbWVudDogKG5vZGUsIHZiLCBjKSA9PiB7XG4gICAgICAgIGNvbnN0IGlubmVyVmIgPSBub2RlWydAYmxvY2snXSB8fCB2YjtcbiAgICAgICAgLy8gVXNlIEZvclN0YXRlbWVudCBvZiBiYXNlIHdhbGtlclxuICAgICAgICB3YWxrLmJhc2UuRm9yU3RhdGVtZW50KG5vZGUsIGlubmVyVmIsIGMpO1xuICAgIH0sXG4gICAgQmxvY2tTdGF0ZW1lbnQ6IChub2RlLCB2YiwgYykgPT4ge1xuICAgICAgICBjb25zdCBpbm5lclZiID0gbm9kZVsnQGJsb2NrJ10gfHwgdmI7XG4gICAgICAgIC8vIFVzZSBCbG9ja1N0YXRlbWVudCBvZiBiYXNlIHdhbGtlclxuICAgICAgICB3YWxrLmJhc2UuQmxvY2tTdGF0ZW1lbnQobm9kZSwgaW5uZXJWYiwgYyk7XG4gICAgfSxcbiAgICBUcnlTdGF0ZW1lbnQ6IChub2RlLCB2YiwgYykgPT4ge1xuICAgICAgICBjKG5vZGUuYmxvY2ssIHZiKTtcbiAgICAgICAgaWYgKG5vZGUuaGFuZGxlcikge1xuICAgICAgICAgICAgLy8gRG8gbm90IHZpc2l0IHBhcmFtZXRlciB3aXRoIGN1cnJlbnQgdmJcbiAgICAgICAgICAgIC8vIHRoZSBwYXJhbWV0ZXIgd2lsbCBiZSB2aXNpdGVkIGluIENhdGNoQ2xhdXNlIHdpdGggY2hhbmdlZCB2YlxuICAgICAgICAgICAgYyhub2RlLmhhbmRsZXIsIHZiKTtcbiAgICAgICAgfVxuICAgICAgICBpZiAobm9kZS5maW5hbGl6ZXIpIHtcbiAgICAgICAgICAgIGMobm9kZS5maW5hbGl6ZXIsIHZiKTtcbiAgICAgICAgfVxuICAgIH0sXG4gICAgQ2F0Y2hDbGF1c2U6IChub2RlLCB2YiwgYykgPT4ge1xuICAgICAgICBjb25zdCBjYXRjaFZiID0gbm9kZS5ib2R5WydAYmxvY2snXTtcbiAgICAgICAgLy8gTmVlZCB0byBoYW5kbGUgdGhlIHBhcmFtZXRlciBpbiBjaGFuZ2VkIGJsb2NrXG4gICAgICAgIGMobm9kZS5wYXJhbSwgY2F0Y2hWYik7XG4gICAgICAgIGMobm9kZS5ib2R5LCBjYXRjaFZiKTtcbiAgICB9LFxuICAgIFZhcmlhYmxlUGF0dGVybjogKG5vZGUsIHZiLCBjKSA9PiB7XG4gICAgICAgIC8vIE5vdGUgdGhhdCB3YWxrLmJhc2UuSWRlbnRpZmllciBpcyAnaWdub3JlLidcbiAgICAgICAgLy8gdmFyV2Fsa2VyIHNob3VsZCB2aXNpdCB2YXJpYWJsZXMgaW4gTEhTLlxuICAgICAgICBjKG5vZGUsIHZiLCAnSWRlbnRpZmllcicpO1xuICAgIH1cbn0pO1xuXG4vKipcbiAqIFdyYXAgYSB3YWxrZXIgd2l0aCBwcmUtIGFuZCBwb3N0LSBhY3Rpb25zXG4gKlxuICogQHBhcmFtIHdhbGtlciAtIGJhc2Ugd2Fsa2VyXG4gKiBAcGFyYW0gcHJlTm9kZSAtIEFwcGx5IGJlZm9yZSB2aXNpdGluZyB0aGUgY3VycmVudCBub2RlLlxuICogSWYgcmV0dXJucyBmYWxzZSwgZG8gbm90IHZpc2l0IHRoZSBub2RlLlxuICogQHBhcmFtIHBvc3ROb2RlIC0gQXBwbHkgYWZ0ZXIgdmlzaXRpbmcgdGhlIGN1cnJlbnQgbm9kZS5cbiAqIElmIGdpdmVuLCByZXR1cm4gdmFsdWVzIGFyZSBvdmVycmlkZGVuLlxuICogQHBhcmFtIHN0Q2hhbmdlIC0gc3RhdGUgY2hhbmdlIGZ1bmN0aW9uXG4gKiBAcmV0dXJucyB7Kn0gLSBhIG5ldyB3YWxrZXJcbiAqL1xuZXhwb3J0IGZ1bmN0aW9uIHdyYXBXYWxrZXIod2Fsa2VyLCBwcmVOb2RlLCBwb3N0Tm9kZSwgc3RDaGFuZ2UpIHtcbiAgICAndXNlIHN0cmljdCc7XG4gICAgY29uc3QgcmV0V2Fsa2VyID0ge307XG4gICAgLy8gd3JhcHBpbmcgZWFjaCBmdW5jdGlvbiBwcmVOb2RlIGFuZCBwb3N0Tm9kZVxuICAgIGZvciAobGV0IG5vZGVUeXBlIGluIHdhbGtlcikge1xuICAgICAgICBpZiAoIXdhbGtlci5oYXNPd25Qcm9wZXJ0eShub2RlVHlwZSkpIHtcbiAgICAgICAgICAgIGNvbnRpbnVlO1xuICAgICAgICB9XG4gICAgICAgIHJldFdhbGtlcltub2RlVHlwZV0gPSAobm9kZSwgc3QsIGMpID0+IHtcbiAgICAgICAgICAgIGxldCByZXQ7XG4gICAgICAgICAgICBsZXQgbmV3U3QgPSBzdDtcbiAgICAgICAgICAgIGlmIChzdENoYW5nZSkge1xuICAgICAgICAgICAgICAgIG5ld1N0ID0gc3RDaGFuZ2Uobm9kZSwgc3QsIG5vZGVUeXBlKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGlmICghcHJlTm9kZSB8fCBwcmVOb2RlKG5vZGUsIG5ld1N0LCBub2RlVHlwZSkpIHtcbiAgICAgICAgICAgICAgICByZXQgPSB3YWxrZXJbbm9kZVR5cGVdKG5vZGUsIG5ld1N0LCBjKTtcbiAgICAgICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgICAgICAgcmV0dXJuO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgaWYgKHBvc3ROb2RlKSB7XG4gICAgICAgICAgICAgICAgcmV0ID0gcG9zdE5vZGUobm9kZSwgbmV3U3QsIG5vZGVUeXBlKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIHJldHVybiByZXQ7XG4gICAgICAgIH1cbiAgICB9XG4gICAgcmV0dXJuIHJldFdhbGtlcjtcbn1cblxuLyoqXG4gKiBBIHV0aWxpdHkgY2xhc3MgZm9yIHNlYXJjaGluZyBBU1RzLlxuICogV2UgdXNlIGluZm8gdG8gcmVjb3JkIGFueSB1c2VmdWwgaW5mb3JtYXRpb24uXG4gKi9cbmV4cG9ydCBjbGFzcyBGb3VuZCB7XG4gICAgY29uc3RydWN0b3IoaW5mbykge1xuICAgICAgICB0aGlzLmluZm8gPSBpbmZvO1xuICAgIH1cbn1cblxuZXhwb3J0IGZ1bmN0aW9uIGlzRHVtbXlJZE5vZGUobm9kZSkge1xuICAgIGlmIChub2RlLnR5cGUgIT09ICdJZGVudGlmaWVyJykge1xuICAgICAgICB0aHJvdyBuZXcgRXJyb3IoJ1Nob3VsZCBiZSBhbiBJZGVudGlmaWVyIG5vZGUnKTtcbiAgICB9XG4gICAgcmV0dXJuIG5vZGUubmFtZSA9PT0gJ+KclicgJiYgbm9kZS5zdGFydCA+PSBub2RlLmVuZDtcbn1cblxuZXhwb3J0IGZ1bmN0aW9uIGZpbmRJZGVudGlmaWVyQXQoYXN0LCBwb3MpIHtcbiAgICAndXNlIHN0cmljdCc7XG4gICAgcmV0dXJuIGZpbmROb2RlQXQoYXN0LCBwb3MsXG4gICAgICAgICAgICBub2RlID0+IG5vZGUudHlwZSA9PT0gJ0lkZW50aWZpZXInICYmICFpc0R1bW15SWROb2RlKG5vZGUpXG4gICAgKTtcbn1cblxuZXhwb3J0IGZ1bmN0aW9uIGZpbmRNZW1iZXJPclZhcmlhYmxlQXQoYXN0LCBwb3MpIHtcbiAgICAndXNlIHN0cmljdCc7XG4gICAgcmV0dXJuIGZpbmROb2RlQXQoYXN0LCBwb3MsXG4gICAgICAgICAgICBub2RlID0+IHtcbiAgICAgICAgICAgICAgICByZXR1cm4gKG5vZGUudHlwZSA9PT0gJ0lkZW50aWZpZXInICYmICFpc0R1bW15SWROb2RlKG5vZGUpKSB8fFxuICAgICAgICAgICAgICAgICAgICAobm9kZS50eXBlID09PSAnTWVtYmVyRXhwcmVzc2lvbicgJiZcbiAgICAgICAgICAgICAgICAgICAgKFxuICAgICAgICAgICAgICAgICAgICAgICAgKG5vZGUucHJvcGVydHkuc3RhcnQgPD0gcG9zICYmIHBvcyA8PSBub2RlLnByb3BlcnR5LmVuZCkgfHxcbiAgICAgICAgICAgICAgICAgICAgICAgIC8vIHdoZW4gcHJvcCBpcyDinJZcbiAgICAgICAgICAgICAgICAgICAgICAgIChub2RlLnByb3BlcnR5LmVuZCA8PSBwb3MgJiYgcG9zIDw9IG5vZGUucHJvcGVydHkuc3RhcnQpXG4gICAgICAgICAgICAgICAgICAgICkpO1xuICAgICAgICAgICAgfVxuICAgICk7XG59XG5cbmV4cG9ydCBmdW5jdGlvbiBmaW5kQ29tcGxldGlvbkNvbnRleHQoYXN0LCBwb3MpIHtcbiAgICAndXNlIHN0cmljdCc7XG4gICAgLy8gZmluZCB0aGUgbm9kZVxuICAgIGNvbnN0IHdhbGtlciA9IHdyYXBXYWxrZXIodmFyV2Fsa2VyLFxuICAgICAgICAobm9kZSwgdmIpID0+IHtcbiAgICAgICAgICAgIGlmIChub2RlLnN0YXJ0ID4gcG9zIHx8IG5vZGUuZW5kIDwgcG9zKSB7XG4gICAgICAgICAgICAgICAgcmV0dXJuIGZhbHNlO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgLy8gYXQgaWRlbnRpZmllcj9cbiAgICAgICAgICAgIGlmIChub2RlLnR5cGUgPT09ICdJZGVudGlmaWVyJykge1xuICAgICAgICAgICAgICAgIHRocm93IG5ldyBGb3VuZCh7dHlwZTogJ0lkZW50aWZpZXInLCBub2RlOiBub2RlLCB2YjogdmJ9KTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIC8vIGF0IG1lbWJlciBleHByZXNzaW9uP1xuICAgICAgICAgICAgaWYgKG5vZGUudHlwZSA9PT0gJ01lbWJlckV4cHJlc3Npb24nICYmXG4gICAgICAgICAgICAgICAgKFxuICAgICAgICAgICAgICAgICAgICAobm9kZS5wcm9wZXJ0eS5zdGFydCA8PSBwb3MgJiYgcG9zIDw9IG5vZGUucHJvcGVydHkuZW5kKSB8fFxuICAgICAgICAgICAgICAgICAgICAgICAgLy8gd2hlbiBwcm9wIGlzIOKcllxuICAgICAgICAgICAgICAgICAgICAobm9kZS5wcm9wZXJ0eS5lbmQgPD0gcG9zICYmIHBvcyA8PSBub2RlLnByb3BlcnR5LnN0YXJ0KVxuICAgICAgICAgICAgICAgIClcbiAgICAgICAgICAgICkge1xuICAgICAgICAgICAgICAgIC8vIGF0IHVzdWFsIHByb3A/IChhZnRlciBkb3QpXG4gICAgICAgICAgICAgICAgaWYgKCFub2RlLmNvbXB1dGVkKSB7XG4gICAgICAgICAgICAgICAgICAgIHRocm93IG5ldyBGb3VuZCh7dHlwZTogJ3VzdWFsUHJvcCcsIG5vZGU6IG5vZGUsIHZiOiB2Yn0pO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAvLyBhdCBvYmpbJyddIHBhdHRlcm4/XG4gICAgICAgICAgICAgICAgaWYgKG5vZGUuY29tcHV0ZWQgJiZcbiAgICAgICAgICAgICAgICAgICAgdHlwZW9mIG5vZGUucHJvcGVydHkudmFsdWUgPT09ICdzdHJpbmcnKSB7XG4gICAgICAgICAgICAgICAgICAgIHRocm93IG5ldyBGb3VuZCh7dHlwZTogJ3N0cmluZ1Byb3AnLCBub2RlOiBub2RlLCB2YjogdmJ9KTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICByZXR1cm4gdHJ1ZTtcbiAgICAgICAgfSxcbiAgICAgICAgKG5vZGUsIHZiKSA9PiB7XG4gICAgICAgICAgICAvLyBubyBJZGVudGlmaWVyIG9yIE1lbWJlciBFeHByZXNzaW9uIHdhcyBmb3VuZFxuICAgICAgICAgICAgdGhyb3cgbmV3IEZvdW5kKHt0eXBlOiAnSWRlbnRpZmllcicsIG5vZGU6IG51bGwsIHZiOiB2Yn0pO1xuICAgICAgICB9KTtcblxuICAgIHRyeSB7XG4gICAgICAgIHdhbGsucmVjdXJzaXZlKGFzdCwgYXN0WydAYmxvY2snXSwgd2Fsa2VyKTtcbiAgICB9IGNhdGNoIChlKSB7XG4gICAgICAgIGlmIChlIGluc3RhbmNlb2YgRm91bmQpIHtcbiAgICAgICAgICAgIHJldHVybiBlLmluZm87XG4gICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgICB0aHJvdyBlO1xuICAgICAgICB9XG4gICAgfVxufVxuXG5cbi8qKlxuICogRmluZCBhIG5vZGUgYXQgcG9zLlxuICogSWYgZm91bmQsIGl0IGFsc28gcmV0dXJucyBpdHMgdmFyQmxvY2suXG4gKiBJZiBub3QgZm91bmQsIHJldHVybiBudWxsLlxuICogQHBhcmFtIGFzdCAtIEFTVCBub2RlXG4gKiBAcGFyYW0gcG9zIC0gaW5kZXggcG9zaXRpb25cbiAqIEBwYXJhbSBub2RlVGVzdCAtIENoZWNrIHdoZXRoZXIgdGhlIG5vZGUgaXMgd2hhdCB3ZSBhcmUgbG9va2luZyBmb3JcbiAqIEByZXR1cm5zIHsqfVxuICovXG5mdW5jdGlvbiBmaW5kTm9kZUF0KGFzdCwgcG9zLCBub2RlVGVzdCkge1xuICAgICd1c2Ugc3RyaWN0JztcbiAgICAvLyBmaW5kIHRoZSBub2RlXG4gICAgY29uc3Qgd2Fsa2VyID0gd3JhcFdhbGtlcih2YXJXYWxrZXIsXG4gICAgICAgIChub2RlLCB2YikgPT4ge1xuICAgICAgICAgICAgaWYgKG5vZGUuc3RhcnQgPiBwb3MgfHwgbm9kZS5lbmQgPCBwb3MpIHtcbiAgICAgICAgICAgICAgICByZXR1cm4gZmFsc2U7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBpZiAobm9kZVRlc3Qobm9kZSkpIHtcbiAgICAgICAgICAgICAgICB0aHJvdyBuZXcgRm91bmQoe25vZGU6IG5vZGUsIHZiOiB2Yn0pO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgcmV0dXJuIHRydWU7XG4gICAgICAgIH0pO1xuXG4gICAgdHJ5IHtcbiAgICAgICAgd2Fsay5yZWN1cnNpdmUoYXN0LCBhc3RbJ0BibG9jayddLCB3YWxrZXIpO1xuICAgIH0gY2F0Y2ggKGUpIHtcbiAgICAgICAgaWYgKGUgaW5zdGFuY2VvZiBGb3VuZCkge1xuICAgICAgICAgICAgcmV0dXJuIGUuaW5mbztcbiAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICAgIHRocm93IGU7XG4gICAgICAgIH1cbiAgICB9XG4gICAgLy8gaWRlbnRpZmllciBub3QgZm91bmRcbiAgICByZXR1cm4gbnVsbDtcbn1cblxuLyoqXG4gKiBGaW5kIHRoZSBzbWFsbGVzdCBub2RlIHRoYXQgY29udGFpbnMgdGhlIHJhbmdlIGZyb20gc3RhcnQgdG8gZW5kLlxuICogTm90ZSB0aGF0IHdlIGNhbiBmaW5kIHRoZSBub2RlIGF0IHRoZSBwb3N0Tm9kZSBpbnN0ZWFkIG9mIHByZU5vZGUuXG4gKiBAcGFyYW0gYXN0XG4gKiBAcGFyYW0gc3RhcnRcbiAqIEBwYXJhbSBlbmRcbiAqIEByZXR1cm5zIHsqfVxuICovXG5leHBvcnQgZnVuY3Rpb24gZmluZFN1cnJvdW5kaW5nTm9kZShhc3QsIHN0YXJ0LCBlbmQpIHtcbiAgICAndXNlIHN0cmljdCc7XG5cbiAgICBjb25zdCB3YWxrZXIgPSB3cmFwV2Fsa2VyKHZhcldhbGtlcixcbiAgICAgICAgbm9kZSA9PiBub2RlLnN0YXJ0IDw9IHN0YXJ0ICYmIGVuZCA8PSBub2RlLmVuZCxcbiAgICAgICAgbm9kZSA9PiB7IHRocm93IG5ldyBGb3VuZChub2RlKTsgfVxuICAgICk7XG5cbiAgICB0cnkge1xuICAgICAgICB3YWxrLnJlY3Vyc2l2ZShhc3QsIHVuZGVmaW5lZCwgd2Fsa2VyKTtcbiAgICB9IGNhdGNoIChlKSB7XG4gICAgICAgIGlmIChlIGluc3RhbmNlb2YgRm91bmQpIHtcbiAgICAgICAgICAgIHJldHVybiBlLmluZm87XG4gICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgICB0aHJvdyBlO1xuICAgICAgICB9XG4gICAgfVxuICAgIC8vIG5vZGUgbm90IGZvdW5kXG4gICAgcmV0dXJuIG51bGw7XG59XG5cbmV4cG9ydCBmdW5jdGlvbiByZWN1cnNpdmVXaXRoUmV0dXJuKG5vZGUsIHN0YXRlLCB2aXNpdG9yKSB7XG4gICAgZnVuY3Rpb24gYyhub2RlLCBzdCwgb3ZlcnJpZGUpIHtcbiAgICAgICAgcmV0dXJuIHZpc2l0b3Jbb3ZlcnJpZGUgfHwgbm9kZS50eXBlXShub2RlLCBzdCwgYyk7XG4gICAgfVxuICAgIHJldHVybiBjKG5vZGUsIHN0YXRlKTtcbn1cbiIsIi8qXG4gSmF2YVNjcmlwdOuKlCBnbG9iYWwsIGZ1bmN0aW9uIGJsb2NrLCBjYXRjaCBibG9ja+yXkCDrs4DsiJjqsIAg64us66aw64ukLlxuIEVTNuuKlCDsnbzrsJggYmxvY2vsl5Drj4Qg64us66aw64ukLlxuXG4gVmFyQmxvY2vripQg6rCBIGJsb2Nr7JeQIOuLrOumsCDrs4DsiJjrk6TsnYQg64KY7YOA64K464ukLlxuIC0gcGFyZW4gICAgICA6IEJsb2NrVmFycywg67CU6rmlIGJsb2Nr7J2EIOuCmO2DgOuCtOuKlCDqsJ3ssrRcbiAtIG9yaWdpbkxhYmVsOiBudW1iZXIsIO2VtOuLuSBCbG9ja1ZhcnPqsIAg7ISg7Ja465CcIEFTVCBub2Rl7J2YIEBsYWJlbFxuICAgIG9yaWdpbuydtCDrkKAg7IiYIOyeiOuKlCBub2Rl64qUXG4gICAgRnVuY3Rpb24uYm9keSwgQ2F0Y2hDbGF1c2UuYmxvY2sg65GQ6rCA7KeA64ukLlxuICAgIOuRkOqwgOyngCDrqqjrkZAgQmxvY2tTdGF0ZW1lbnTsnbTri6QuXG4gLSBpc0NhdGNoICAgIDogYm9vbGVhbixcbiAgICogdHJ1ZSAgLT4gY2F0Y2ggYmxvY2tcbiAgICogZmFsc2UgLT4gZnVuY3Rpb24gYmxvY2ssIG9yIGdsb2JhbFxuXG4gLSBwYXJhbVZhck5hbWVzIDog66ek6rCc67OA7IiYIOydtOumhCDrqqnroZ0sIOunpOqwnCDrs4DsiJgg7Iic7ISc64yA66GcXG4gLSBsb2NhbFZhck5hbWVzIDog7KeA7JetIOuzgOyImCDsnbTrpoQg66qp66GdLCDsiJzshJwg66y07J2Y66+4XG4gICAgYXJndW1lbnRz66W8IOyCrOyaqe2VmOuKlCDqsr3smrAgbG9jYWxWYXJOYW1lc+yXkCDrk7HsnqXtlZjqs6AsXG4gICAgYXJndW1lbnRzIG9iamVjdOulvCDsgqzsmqntlZjrqbQgdXNlQXJndW1lbnRzT2JqZWN0ID09IHRydWVcblxuIC0gKG9wdGlvbmFsKSB1c2VBcmd1bWVudHNPYmplY3Q6IGJvb2xlYW5cbiAgICDtlajsiJggYm9keSBibG9ja+yduCDqsr3smrDsl5Drp4wg7IKs7JqpIOqwgOuKpVxuICAgICogdHJ1ZSAgOiBhcmd1bWVudHMgb2JqZWN06rCAIOyCrOyaqeuQmOyXiOuLpC5cbiAgICAgIOymiSDtlajsiJggYm9keeyXkOyEnCDrs4DsiJggYXJndW1lbnRz66W8IOyEoOyWuCDsl4bsnbQg7IKs7Jqp7ZaI64ukLlxuICAgICAg7J20IOqyveyasCwgYXJndW1lbnRz64qUIO2VqOyImOydmCDsp4Dsl60g67OA7IiY66GcIOuTseuhneuQnOuLpC5cbiAgICAqIGZhbHNlIOyduCDqsr3smrDripQg7JeG64ukLiDqt7jrn7TqsbDrqbQg7JWE7JiIIOuzgOyImCDsnpDssrTqsIAg7JeG64ukLlxuXG4gLSB1c2VkVmFyaWFibGVzIDog6rCBIGJsb2Nr7J2YIOunpOqwnOuzgOyImCwg7KeA7Jet67OA7IiYIOykkVxuICAg7IKs7Jqp65CY64qUIOychOy5mOqwgCDsnojripQg6rKD65Ok7J2YIOuqqeuhnVxuXG4gLSBpbnN0YW5jZXMgOiBEZWx0YSAtPiBWYXJCbG9ja+ydmCDrs4DsiJjrk6QgLT4gQVZhbFxuICAgZ2V0SW5zdGFuY2UoZGVsdGEpIOulvCDthrXtlbQg6rCZ7J2AIGRlbHRh64qUIOqwmeydgCBtYXBwaW5nIOyjvOqyjCDrp4zrk6xcblxuIC0gc2NvcGVJbnN0YW5jZXMgOiBbU2NvcGVdXG4gICDtmITsnqwgVmFyQmxvY2vsnYQg66eI7KeA66eJ7Jy866GcIO2VmOuKlCBTY29wZeulvCDrqqjrkZAg66qo7J2A64ukLlxuICAgZ2V0U2NvcGVJbnN0YW5jZShkZWx0YSwgcGFyZW4pIOydhCDthrXtlbQg6rCZ7J2AIHNjb3BlIGNoYWlu7J2AXG4gICDqsJnsnYAg6rCd7LK06rCAIOuQmOuPhOuhnSDrp4zrk6Dri6QuXG4qL1xuJ3VzZSBzdHJpY3QnO1xuXG5pbXBvcnQgKiBhcyB0eXBlcyBmcm9tICcuL2RvbWFpbnMvdHlwZXMnXG5pbXBvcnQgKiBhcyBteVdhbGtlciBmcm9tICcuL3V0aWwvbXlXYWxrZXInXG5jb25zdCB3YWxrID0gcmVxdWlyZSgnYWNvcm4vZGlzdC93YWxrJyk7XG5cbmV4cG9ydCBjbGFzcyBWYXJCbG9jayB7XG4gICAgY29uc3RydWN0b3IocGFyZW4sIG9yaWdpbk5vZGUsIGJUeXBlLCBpc1N0cmljdCkge1xuICAgICAgICB0aGlzLnBhcmVuID0gcGFyZW47XG4gICAgICAgIHRoaXMub3JpZ2luTm9kZSA9IG9yaWdpbk5vZGU7XG4gICAgICAgIHRoaXMuYmxvY2tUeXBlID0gYlR5cGU7XG4gICAgICAgIHRoaXMuaXNTdHJpY3QgPSBpc1N0cmljdDtcblxuICAgICAgICB0aGlzLm9yaWdpbkxhYmVsID0gb3JpZ2luTm9kZVsnQGxhYmVsJ107XG4gICAgICAgIHRoaXMucGFyYW1WYXJOYW1lcyA9IFtdO1xuICAgICAgICB0aGlzLmxvY2FsVmFyTmFtZXMgPSBbXTtcblxuICAgICAgICB0aGlzLnVzZWRWYXJpYWJsZXMgPSBbXTtcbiAgICAgICAgLy8gdGhpcy51c2VBcmd1bWVudHNPYmplY3RcbiAgICAgICAgdGhpcy5pbnN0YW5jZXMgPSBuZXcgTWFwKCk7XG4gICAgICAgIHRoaXMuc2NvcGVJbnN0YW5jZXMgPSBbXTtcbiAgICB9XG5cbiAgICBpc0dsb2JhbCgpIHtcbiAgICAgICAgcmV0dXJuIHRoaXMuYmxvY2tUeXBlID09PSBWYXJCbG9jay5ibG9ja1R5cGVzLmdsb2JhbEJsb2NrO1xuICAgIH1cblxuICAgIGlzT2xkRnVuY3Rpb25CbG9jaygpIHtcbiAgICAgICAgcmV0dXJuIHRoaXMuYmxvY2tUeXBlID09PSBWYXJCbG9jay5ibG9ja1R5cGVzLm9sZEZ1bmN0aW9uQmxvY2s7XG4gICAgfVxuXG4gICAgaXNBcnJvd0Z1bmN0aW9uQmxvY2soKSB7XG4gICAgICAgIHJldHVybiB0aGlzLmJsb2NrVHlwZSA9PT0gVmFyQmxvY2suYmxvY2tUeXBlcy5hcnJvd0Z1bmN0aW9uQmxvY2s7XG4gICAgfVxuXG4gICAgaXNDYXRjaEJsb2NrKCkge1xuICAgICAgICByZXR1cm4gdGhpcy5ibG9ja1R5cGUgPT09IFZhckJsb2NrLmJsb2NrVHlwZXMuY2F0Y2hCbG9jaztcbiAgICB9XG5cbiAgICBpc05vcm1hbEJsb2NrKCkge1xuICAgICAgICByZXR1cm4gdGhpcy5ibG9ja1R5cGUgPT09IFZhckJsb2NrLmJsb2NrVHlwZXMubm9ybWFsQmxvY2s7XG4gICAgfVxuXG4gICAgaXNQYXJhbWV0ZXJCbG9jaygpIHtcbiAgICAgICAgcmV0dXJuIHRoaXMuYmxvY2tUeXBlID09PSBWYXJCbG9jay5ibG9ja1R5cGVzLnBhcmFtZXRlckJsb2NrO1xuICAgIH1cblxuICAgIGdldExvY2FsVmFyTmFtZXMoKSB7XG4gICAgICAgIHJldHVybiB0aGlzLmxvY2FsVmFyTmFtZXM7XG4gICAgfVxuXG4gICAgZ2V0UGFyYW1WYXJOYW1lcygpIHtcbiAgICAgICAgcmV0dXJuIHRoaXMucGFyYW1WYXJOYW1lcztcbiAgICB9XG5cbiAgICBnZXRWYXJOYW1lcygpIHtcbiAgICAgICAgcmV0dXJuIHRoaXMuZ2V0TG9jYWxWYXJOYW1lcygpLmNvbmNhdCh0aGlzLmdldFBhcmFtVmFyTmFtZXMoKSk7XG4gICAgfVxuXG4gICAgaGFzTG9jYWxWYXIodmFyTmFtZSkge1xuICAgICAgICByZXR1cm4gdGhpcy5sb2NhbFZhck5hbWVzICYmIHRoaXMubG9jYWxWYXJOYW1lcy5pbmRleE9mKHZhck5hbWUpID4gLTE7XG4gICAgfVxuXG4gICAgaGFzUGFyYW1WYXIodmFyTmFtZSkge1xuICAgICAgICByZXR1cm4gdGhpcy5wYXJhbVZhck5hbWVzLmluZGV4T2YodmFyTmFtZSkgPiAtMTtcbiAgICB9XG5cbiAgICBoYXNWYXIodmFyTmFtZSkge1xuICAgICAgICByZXR1cm4gdGhpcy5oYXNQYXJhbVZhcih2YXJOYW1lKSB8fCB0aGlzLmhhc0xvY2FsVmFyKHZhck5hbWUpO1xuICAgIH1cblxuICAgIGFkZERlY2xhcmVkTG9jYWxWYXIodmFyTmFtZSwgZFR5cGUpIHtcbiAgICAgICAgbGV0IGN1cnJCbG9jayA9IHRoaXM7XG4gICAgICAgIHN3aXRjaChkVHlwZSkge1xuICAgICAgICAgICAgY2FzZSBWYXJCbG9jay5kZWNsYXJhdGlvblR5cGVzLnZhckRlY2xhcmF0aW9uOlxuICAgICAgICAgICAgICAgIC8vIEdvIHVwIHVudGlsIGZ1bmN0aW9uIG9yIGdsb2JhbFxuICAgICAgICAgICAgICAgIHdoaWxlICghY3VyckJsb2NrLmlzT2xkRnVuY3Rpb25CbG9jaygpXG4gICAgICAgICAgICAgICAgICAgICYmICFjdXJyQmxvY2suaXNBcnJvd0Z1bmN0aW9uQmxvY2soKVxuICAgICAgICAgICAgICAgICAgICAmJiAhY3VyckJsb2NrLmlzUGFyYW1ldGVyQmxvY2soKSAgLy8gdG8gYWRkICdhcmd1bWVudHMnXG4gICAgICAgICAgICAgICAgICAgICYmICFjdXJyQmxvY2suaXNHbG9iYWwoKSkge1xuICAgICAgICAgICAgICAgICAgICBjdXJyQmxvY2sgPSBjdXJyQmxvY2sucGFyZW47XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIGJyZWFrO1xuICAgICAgICAgICAgY2FzZSBWYXJCbG9jay5kZWNsYXJhdGlvblR5cGVzLmZ1bmN0aW9uRGVjbGFyYXRpb246XG4gICAgICAgICAgICAgICAgLy8gR28gdXAgdW50aWwgZnVuY3Rpb24gb3IgZ2xvYmFsXG4gICAgICAgICAgICAgICAgLy8gb3IgY2F0Y2ggYmxvY2sgaGF2aW5nIHZhck5hbWUgYXMgaXRzIHBhcmFtZXRlclxuICAgICAgICAgICAgICAgIHdoaWxlIChjdXJyQmxvY2suaXNOb3JtYWxCbG9jaygpICYmXG4gICAgICAgICAgICAgICAgICAgICAgICEoY3VyckJsb2NrLmlzQ2F0Y2hCbG9jaygpICYmIGN1cnJCbG9jay5oYXNQYXJhbVZhcih2YXJOYW1lKSkpIHtcbiAgICAgICAgICAgICAgICAgICAgY3VyckJsb2NrID0gY3VyckJsb2NrLnBhcmVuO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICBicmVhaztcbiAgICAgICAgICAgIGNhc2UgVmFyQmxvY2suZGVjbGFyYXRpb25UeXBlcy5sZXREZWNsYXJhdGlvbjpcbiAgICAgICAgICAgIGNhc2UgVmFyQmxvY2suZGVjbGFyYXRpb25UeXBlcy5jb25zdERlY2xhcmF0aW9uOlxuICAgICAgICAgICAgICAgIGJyZWFrO1xuICAgICAgICAgICAgY2FzZSBWYXJCbG9jay5kZWNsYXJhdGlvblR5cGVzLmltcGxpY2l0R2xvYmFsRGVjbGFyYXRpb246XG4gICAgICAgICAgICAgICAgLy8gbm90IGdsb2JhbCBvciBzdHJpY3QgPT4gZG8gbm90IGFkZCB0aGUgdmFyaWFibGVcbiAgICAgICAgICAgICAgICBpZiAoIXRoaXMuaXNHbG9iYWwoKSB8fCB0aGlzLmlzU3RyaWN0KSB7XG4gICAgICAgICAgICAgICAgICAgIHJldHVybiBudWxsO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICBicmVhaztcbiAgICAgICAgfVxuXG4gICAgICAgIC8vIGlmIGFscmVhZHkgYWRkZWQsIGRvIG5vdCBhZGRcbiAgICAgICAgaWYgKCFjdXJyQmxvY2suaGFzVmFyKHZhck5hbWUpKSB7XG4gICAgICAgICAgICBjdXJyQmxvY2subG9jYWxWYXJOYW1lcy5wdXNoKHZhck5hbWUpO1xuICAgICAgICB9XG4gICAgICAgIC8vIHJldHVybnMgdGhlIGJsb2NrIG9iamVjdCB0aGF0IGNvbnRhaW5zIHRoZSB2YXJpYWJsZVxuICAgICAgICByZXR1cm4gY3VyckJsb2NrO1xuICAgIH1cblxuICAgIGFkZFBhcmFtVmFyKHZhck5hbWUpIHtcbiAgICAgICAgdGhpcy5wYXJhbVZhck5hbWVzLnB1c2godmFyTmFtZSk7XG4gICAgfVxuXG4gICAgZmluZFZhckluQ2hhaW4odmFyTmFtZSkge1xuICAgICAgICBsZXQgY3VyckJsb2NrID0gdGhpcztcbiAgICAgICAgd2hpbGUgKGN1cnJCbG9jayAmJiAhY3VyckJsb2NrLmhhc1Zhcih2YXJOYW1lKSkge1xuICAgICAgICAgICAgaWYgKGN1cnJCbG9jay5pc0dsb2JhbCgpICYmICFjdXJyQmxvY2suaXNTdHJpY3QpIHtcbiAgICAgICAgICAgICAgICBicmVhaztcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGN1cnJCbG9jayA9IGN1cnJCbG9jay5wYXJlbjtcbiAgICAgICAgfVxuICAgICAgICAvLyBpZiBub3QgZm91bmRcbiAgICAgICAgLy8gMSkgZ2xvYmFsICd1c2Ugc3RyaWN0JyA9PiByZXR1cm5zIG51bGxcbiAgICAgICAgLy8gMikgb3RoZXJ3aXNlID0+IHJldHVybnMgdGhlIGdsb2JhbFxuICAgICAgICByZXR1cm4gY3VyckJsb2NrO1xuICAgIH1cblxuICAgIGdldFZhck5hbWVzSW5DaGFpbigpIHtcbiAgICAgICAgbGV0IGN1cnJCbG9jayA9IHRoaXM7XG4gICAgICAgIGNvbnN0IHZhck5hbWVzID0gW107XG4gICAgICAgIHdoaWxlIChjdXJyQmxvY2spIHtcbiAgICAgICAgICAgIGN1cnJCbG9jay5nZXRWYXJOYW1lcygpLmZvckVhY2goZnVuY3Rpb24gKG5hbWUpIHtcbiAgICAgICAgICAgICAgICBpZiAodmFyTmFtZXMuaW5kZXhPZihuYW1lKSA9PT0gLTEpIHtcbiAgICAgICAgICAgICAgICAgICAgdmFyTmFtZXMucHVzaChuYW1lKTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICB9KTtcbiAgICAgICAgICAgIGN1cnJCbG9jayA9IGN1cnJCbG9jay5wYXJlbjtcbiAgICAgICAgfVxuICAgICAgICByZXR1cm4gdmFyTmFtZXM7XG4gICAgfVxuXG4gICAgYWRkVXNlZFZhcih2YXJOYW1lKSB7XG4gICAgICAgIGlmICh0aGlzLnVzZWRWYXJpYWJsZXMuaW5kZXhPZih2YXJOYW1lKSA9PT0gLTEpIHtcbiAgICAgICAgICAgIHRoaXMudXNlZFZhcmlhYmxlcy5wdXNoKHZhck5hbWUpO1xuICAgICAgICB9XG4gICAgfVxuXG4gICAgZ2V0VXNlZFZhck5hbWVzKCkge1xuICAgICAgICByZXR1cm4gdGhpcy51c2VkVmFyaWFibGVzO1xuICAgIH1cblxuICAgIGlzVXNlZFZhcih2YXJOYW1lKSB7XG4gICAgICAgIHJldHVybiB0aGlzLnVzZWRWYXJpYWJsZXMuaW5kZXhPZih2YXJOYW1lKSA+IC0xO1xuICAgIH1cblxuICAgIC8vIHJldHVybnMgYSBtYXBwaW5nXG4gICAgZ2V0SW5zdGFuY2UoZGVsdGEpIHtcbiAgICAgICAgaWYgKHRoaXMuaW5zdGFuY2VzLmhhcyhkZWx0YSkpIHtcbiAgICAgICAgICAgIHJldHVybiB0aGlzLmluc3RhbmNlcy5nZXQoZGVsdGEpO1xuICAgICAgICB9XG4gICAgICAgIC8vIGNvbnN0cnVjdCBWYXJNYXBcbiAgICAgICAgY29uc3QgdmFyTWFwID0gbmV3IE1hcCgpO1xuICAgICAgICBjb25zdCB2YXJOYW1lcyA9IHRoaXMuZ2V0UGFyYW1WYXJOYW1lcygpLmNvbmNhdCh0aGlzLmdldExvY2FsVmFyTmFtZXMoKSk7XG5cbiAgICAgICAgZm9yIChsZXQgaSA9IDA7IGkgPCB2YXJOYW1lcy5sZW5ndGg7IGkrKykge1xuICAgICAgICAgICAgdmFyTWFwLnNldCh2YXJOYW1lc1tpXSwgbmV3IHR5cGVzLkFWYWwoKSk7XG4gICAgICAgIH1cbiAgICAgICAgLy8gcmVtZW1iZXIgdGhlIGluc3RhbmNlXG4gICAgICAgIHRoaXMuaW5zdGFuY2VzLnNldChkZWx0YSx2YXJNYXApO1xuICAgICAgICByZXR1cm4gdmFyTWFwO1xuICAgIH1cblxuICAgIC8vIHJldHVybnMgYW4gYXJyYXlcbiAgICBnZXRQYXJhbUFWYWxzKGRlbHRhKSB7XG4gICAgICAgIGNvbnN0IGluc3RhbmNlID0gdGhpcy5nZXRJbnN0YW5jZShkZWx0YSk7XG4gICAgICAgIGNvbnN0IHBhcmFtcyA9IFtdO1xuICAgICAgICB0aGlzLmdldFBhcmFtVmFyTmFtZXMoKS5mb3JFYWNoKG5hbWUgPT4ge1xuICAgICAgICAgICAgcGFyYW1zLnB1c2goaW5zdGFuY2UuZ2V0KG5hbWUpKTtcbiAgICAgICAgfSk7XG4gICAgICAgIHJldHVybiBwYXJhbXM7XG4gICAgfVxuXG4gICAgLy8gcmV0dXJucyBhbiBBVmFsXG4gICAgZ2V0QXJndW1lbnRzQVZhbChkZWx0YSkge1xuICAgICAgICBpZiAoIXRoaXMudXNlQXJndW1lbnRzT2JqZWN0KSB7XG4gICAgICAgICAgICB0aHJvdyBuZXcgRXJyb3IoJ05vdCBmb3IgdGhpcyBWYXJCbG9jaycpO1xuICAgICAgICB9XG4gICAgICAgIHJldHVybiB0aGlzLmdldEluc3RhbmNlKGRlbHRhKS5nZXQoJ2FyZ3VtZW50cycpO1xuICAgIH1cblxuICAgIC8vIGdldCBhIFNjb3BlIGluc3RhbmNlXG4gICAgZ2V0U2NvcGVJbnN0YW5jZShwYXJlbiwgZGVsdGEpIHtcbiAgICAgICAgY29uc3QgdmFyTWFwID0gdGhpcy5nZXRJbnN0YW5jZShkZWx0YSk7XG4gICAgICAgIGxldCBmb3VuZCA9IG51bGw7XG5cbiAgICAgICAgdGhpcy5zY29wZUluc3RhbmNlcy5mb3JFYWNoKGZ1bmN0aW9uIChzYykge1xuICAgICAgICAgICAgaWYgKHNjLnBhcmVuID09PSBwYXJlbiAmJiBzYy52YXJNYXAgPT09IHZhck1hcCkgZm91bmQgPSBzYztcbiAgICAgICAgfSk7XG5cbiAgICAgICAgaWYgKGZvdW5kKSB7XG4gICAgICAgICAgICByZXR1cm4gZm91bmQ7XG4gICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgICBsZXQgbmV3U2NvcGVJbnN0YW5jZSA9IG5ldyBTY29wZShwYXJlbiwgdmFyTWFwLCB0aGlzKTtcbiAgICAgICAgICAgIHRoaXMuc2NvcGVJbnN0YW5jZXMucHVzaChuZXdTY29wZUluc3RhbmNlKTtcbiAgICAgICAgICAgIHJldHVybiBuZXdTY29wZUluc3RhbmNlO1xuICAgICAgICB9XG4gICAgfVxuXG4gICAgLy8gZ2V0IGZ1bmN0aW9uJ3Mgc2NvcGUgaW5zdGFuY2VzXG4gICAgZ2V0U2NvcGVXaXRoUGFyZW50KHBTY29wZSkge1xuICAgICAgICBjb25zdCBpbnN0YW5jZXMgPSBuZXcgU2V0KCk7XG4gICAgICAgIHRoaXMuc2NvcGVJbnN0YW5jZXMuZm9yRWFjaChzYyA9PiB7XG4gICAgICAgICAgICBpZiAoc2MucGFyZW4gPT09IHBTY29wZSkgaW5zdGFuY2VzLmFkZChzYyk7XG4gICAgICAgIH0pO1xuICAgICAgICByZXR1cm4gaW5zdGFuY2VzO1xuICAgIH1cbn1cblxuVmFyQmxvY2suYmxvY2tUeXBlcyA9IHtcbiAgICBnbG9iYWxCbG9jazogU3ltYm9sKCdnbG9iYWwnKSxcbiAgICBvbGRGdW5jdGlvbkJsb2NrOiBTeW1ib2woJ29sZEZ1bmN0aW9uJyksXG4gICAgYXJyb3dGdW5jdGlvbkJsb2NrOiBTeW1ib2woJ2Fycm93RnVuY3Rpb24nKSxcbiAgICBwYXJhbWV0ZXJCbG9jazogU3ltYm9sKCdwYXJhbWV0ZXInKSwgIC8vIHRob3VnaCBub3QgcmVhbGx5IGluIGJyYWNlc1xuICAgIGNhdGNoQmxvY2s6IFN5bWJvbCgnY2F0Y2gnKSxcbiAgICBub3JtYWxCbG9jazogU3ltYm9sKCdub3JtYWwnKVxufTtcblxuVmFyQmxvY2suZGVjbGFyYXRpb25UeXBlcyA9IHtcbiAgICBsZXREZWNsYXJhdGlvbjogU3ltYm9sKCdsZXQnKSxcbiAgICBjb25zdERlY2xhcmF0aW9uOiBTeW1ib2woJ2NvbnN0JyksXG4gICAgdmFyRGVjbGFyYXRpb246IFN5bWJvbCgndmFyJyksXG4gICAgZnVuY3Rpb25EZWNsYXJhdGlvbjogU3ltYm9sKCdmdW5jdGlvbicpLFxuICAgIHBhcmFtZXRlckRlY2xhcmF0aW9uOiBTeW1ib2woJ3BhcmFtZXRlcicpLFxuICAgIGltcGxpY2l0R2xvYmFsRGVjbGFyYXRpb246IFN5bWJvbCgnaW1wbGljaXQgZ2xvYmFsJylcbn07XG5cbi8qKlxuICogQ2hlY2sgd2hldGhlciB0aGUgc3RtdCBpcyB0aGUgZGlyZWN0aXZlIGZvciBzdHJpY3RuZXNzLlxuICogVGFrZW4gZnJvbSBhY29yblxuICogQHBhcmFtIHN0bXQgLSB0aGUgZmlyc3Qgc3RhdGVtZW50IG9mIGEgYm9keVxuICogQHJldHVybnMge2Jvb2xlYW59XG4gKi9cbmZ1bmN0aW9uIGlzVXNlU3RyaWN0KHN0bXQpIHtcbiAgICByZXR1cm4gc3RtdC50eXBlID09PSAnRXhwcmVzc2lvblN0YXRlbWVudCcgJiZcbiAgICAgICAgc3RtdC5leHByZXNzaW9uLnR5cGUgPT09ICdMaXRlcmFsJyAmJlxuICAgICAgICBzdG10LmV4cHJlc3Npb24ucmF3LnNsaWNlKDEsIC0xKSA9PT0gJ3VzZSBzdHJpY3QnO1xufVxuXG5cbmNvbnN0IGRlY2xhcmVkVmFyaWFibGVGaW5kZXIgPSB3YWxrLm1ha2Uoe1xuICAgIFZhcmlhYmxlUGF0dGVybjogKG5vZGUsIFtkVHlwZSwgY3VyckJsb2NrXSwgYykgPT4ge1xuICAgICAgICBpZiAoZFR5cGUgPT09IFZhckJsb2NrLmRlY2xhcmF0aW9uVHlwZXMucGFyYW1ldGVyRGVjbGFyYXRpb24pIHtcbiAgICAgICAgICAgIGN1cnJCbG9jay5hZGRQYXJhbVZhcihub2RlLm5hbWUpO1xuICAgICAgICB9IGVsc2UgaWYgKGRUeXBlKSB7XG4gICAgICAgICAgICBjdXJyQmxvY2suYWRkRGVjbGFyZWRMb2NhbFZhcihub2RlLm5hbWUsIGRUeXBlKTtcbiAgICAgICAgfVxuICAgIH0sXG4gICAgRnVuY3Rpb246IChub2RlLCBbZFR5cGUsIGN1cnJCbG9ja10sIGMpID0+IHtcbiAgICAgICAgbGV0IHBhcmVuQmxvY2sgPSBjdXJyQmxvY2ssIHBhcmFtQmxvY2s7XG4gICAgICAgIGlmIChub2RlLmlkKSB7XG4gICAgICAgICAgICBjb25zdCBmdW5jTmFtZSA9IG5vZGUuaWQubmFtZTtcbiAgICAgICAgICAgIHBhcmVuQmxvY2sgPSBjdXJyQmxvY2suYWRkRGVjbGFyZWRMb2NhbFZhcihmdW5jTmFtZSxcbiAgICAgICAgICAgICAgICBWYXJCbG9jay5kZWNsYXJhdGlvblR5cGVzLmZ1bmN0aW9uRGVjbGFyYXRpb24pO1xuICAgICAgICB9XG4gICAgICAgIGNvbnN0IGhhc1BhcmFtU2NvcGUgPSBub2RlLnBhcmFtcy5zb21lKChwdG4pID0+XG4gICAgICAgICAgICBteVdhbGtlci5wYXR0ZXJuSGFzRGVmYXVsdHMocHRuKSk7XG4gICAgICAgIGlmIChoYXNQYXJhbVNjb3BlKSB7XG4gICAgICAgICAgICBwYXJhbUJsb2NrID0gcGFyZW5CbG9jayA9IG5ldyBWYXJCbG9jayhcbiAgICAgICAgICAgICAgICBwYXJlbkJsb2NrLFxuICAgICAgICAgICAgICAgIG5vZGUsXG4gICAgICAgICAgICAgICAgVmFyQmxvY2suYmxvY2tUeXBlcy5wYXJhbWV0ZXJCbG9jayxcbiAgICAgICAgICAgICAgICBjdXJyQmxvY2suaXNTdHJpY3RcbiAgICAgICAgICAgICk7XG4gICAgICAgICAgICBub2RlWydAYmxvY2snXSA9IHBhcmFtQmxvY2s7XG4gICAgICAgIH1cbiAgICAgICAgY29uc3Qgc3RyaWN0SW5uZXIgPSBjdXJyQmxvY2suaXNTdHJpY3QgfHxcbiAgICAgICAgICAgIChub2RlLmJvZHkuYm9keSAmJlxuICAgICAgICAgICAgIG5vZGUuYm9keS5ib2R5WzBdICYmXG4gICAgICAgICAgICAgaXNVc2VTdHJpY3Qobm9kZS5ib2R5LmJvZHlbMF0pKTtcbiAgICAgICAgY29uc3QgZnVuY0Jsb2NrID0gbmV3IFZhckJsb2NrKFxuICAgICAgICAgICAgcGFyZW5CbG9jayxcbiAgICAgICAgICAgIG5vZGUsICAvLyBzYW1lIG9yaWdpbk5vZGUgd2l0aCBwYXJhbUJsb2NrLCBpbnRlbmRlZC5cbiAgICAgICAgICAgIG5vZGUudHlwZSA9PT0gJ0Fycm93RnVuY3Rpb25FeHByZXNzaW9uJz9cbiAgICAgICAgICAgICAgICBWYXJCbG9jay5ibG9ja1R5cGVzLmFycm93RnVuY3Rpb25CbG9ja1xuICAgICAgICAgICAgICAgIDogVmFyQmxvY2suYmxvY2tUeXBlcy5vbGRGdW5jdGlvbkJsb2NrLFxuICAgICAgICAgICAgc3RyaWN0SW5uZXJcbiAgICAgICAgKTtcbiAgICAgICAgZnVuY0Jsb2NrLmhhc1BhcmFtU2NvcGUgPSBoYXNQYXJhbVNjb3BlO1xuICAgICAgICBub2RlLmJvZHlbJ0BibG9jayddID0gZnVuY0Jsb2NrO1xuXG4gICAgICAgIC8vIGFkZCBmdW5jdGlvbiBwYXJhbWV0ZXJzIHRvIGNvcnJlc3BvbmRpbmcgc2NvcGVcbiAgICAgICAgY29uc3QgcGFyYW1UYXJnZXRCbG9jayA9IHBhcmFtQmxvY2sgfHwgZnVuY0Jsb2NrO1xuICAgICAgICBmb3IgKGxldCBpID0gMDsgaSA8IG5vZGUucGFyYW1zLmxlbmd0aDsgaSsrKSB7XG4gICAgICAgICAgICBjKG5vZGUucGFyYW1zW2ldLFxuICAgICAgICAgICAgICAgIFtcbiAgICAgICAgICAgICAgICAgICAgVmFyQmxvY2suZGVjbGFyYXRpb25UeXBlcy5wYXJhbWV0ZXJEZWNsYXJhdGlvbixcbiAgICAgICAgICAgICAgICAgICAgcGFyYW1UYXJnZXRCbG9ja1xuICAgICAgICAgICAgICAgIF0sXG4gICAgICAgICAgICAgICAgJ1BhdHRlcm4nKTtcbiAgICAgICAgfVxuXG4gICAgICAgIGlmIChub2RlLmV4cHJlc3Npb24pIHtcbiAgICAgICAgICAgIGMobm9kZS5ib2R5LCBbLCBmdW5jQmxvY2tdLCAnRXhwcmVzc2lvbicpO1xuICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgICAgd2Fsay5iYXNlLkJsb2NrU3RhdGVtZW50KG5vZGUuYm9keSwgWywgZnVuY0Jsb2NrXSwgYyk7XG4gICAgICAgIH1cbiAgICB9LFxuXG4gICAgRm9yU3RhdGVtZW50OiAobm9kZSwgWywgY3VyckJsb2NrXSwgYykgPT4ge1xuICAgICAgICBsZXQgZm9yQmxvY2s7XG4gICAgICAgIGlmIChjdXJyQmxvY2suaXNTdHJpY3QpIHtcbiAgICAgICAgICAgIGZvckJsb2NrID0gbmV3IFZhckJsb2NrKFxuICAgICAgICAgICAgICAgIGN1cnJCbG9jayxcbiAgICAgICAgICAgICAgICBub2RlLFxuICAgICAgICAgICAgICAgIFZhckJsb2NrLmJsb2NrVHlwZXMubm9ybWFsQmxvY2ssXG4gICAgICAgICAgICAgICAgY3VyckJsb2NrLmlzU3RyaWN0XG4gICAgICAgICAgICApO1xuICAgICAgICAgICAgbm9kZVsnQGJsb2NrJ10gPSBmb3JCbG9jaztcbiAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICAgIGZvckJsb2NrID0gY3VyckJsb2NrO1xuICAgICAgICB9XG4gICAgICAgIGlmIChub2RlLmluaXQpIGMobm9kZS5pbml0LCBbLCBmb3JCbG9ja10sICdGb3JJbml0Jyk7XG4gICAgICAgIGlmIChub2RlLnRlc3QpIGMobm9kZS50ZXN0LCBbLCBmb3JCbG9ja10sICdFeHByZXNzaW9uJyk7XG4gICAgICAgIGlmIChub2RlLnVwZGF0ZSkgYyhub2RlLnVwZGF0ZSwgWywgZm9yQmxvY2tdLCAnRXhwcmVzc2lvbicpO1xuICAgICAgICAvLyBpdHMgYm9keSBjYW4gaGF2ZSBhIHNlcGFyYXRlIGJsb2NrLlxuICAgICAgICBjKG5vZGUuYm9keSwgWywgZm9yQmxvY2tdLCB1bmRlZmluZWQpO1xuICAgIH0sXG5cbiAgICBWYXJpYWJsZURlY2xhcmF0aW9uOiAobm9kZSwgWywgY3VyckJsb2NrXSwgYykgPT4ge1xuICAgICAgICBsZXQgZFR5cGU7XG4gICAgICAgIHN3aXRjaChub2RlLmtpbmQpIHtcbiAgICAgICAgICAgIGNhc2UgJ3Zhcic6XG4gICAgICAgICAgICAgICAgZFR5cGUgPSBWYXJCbG9jay5kZWNsYXJhdGlvblR5cGVzLnZhckRlY2xhcmF0aW9uO1xuICAgICAgICAgICAgICAgIGJyZWFrO1xuICAgICAgICAgICAgY2FzZSAnbGV0JzpcbiAgICAgICAgICAgICAgICBkVHlwZSA9IFZhckJsb2NrLmRlY2xhcmF0aW9uVHlwZXMubGV0RGVjbGFyYXRpb247XG4gICAgICAgICAgICAgICAgYnJlYWs7XG4gICAgICAgICAgICBjYXNlICdjb25zdCc6XG4gICAgICAgICAgICAgICAgZFR5cGUgPSBWYXJCbG9jay5kZWNsYXJhdGlvblR5cGVzLmNvbnN0RGVjbGFyYXRpb247XG4gICAgICAgICAgICAgICAgYnJlYWs7XG4gICAgICAgIH1cblxuICAgICAgICBmb3IgKGxldCBpID0gMDsgaSA8IG5vZGUuZGVjbGFyYXRpb25zLmxlbmd0aDsgaSsrKSB7XG4gICAgICAgICAgICBjKG5vZGUuZGVjbGFyYXRpb25zW2ldLCBbZFR5cGUsIGN1cnJCbG9ja10sIHVuZGVmaW5lZCk7XG4gICAgICAgIH1cbiAgICB9LFxuXG4gICAgVHJ5U3RhdGVtZW50OiAobm9kZSwgWywgY3VyclNjb3BlXSwgYykgPT4ge1xuICAgICAgICBjKG5vZGUuYmxvY2ssIFssIGN1cnJTY29wZV0sIHVuZGVmaW5lZCk7XG4gICAgICAgIGlmIChub2RlLmhhbmRsZXIpIHtcbiAgICAgICAgICAgIGMobm9kZS5oYW5kbGVyLCBbLCBjdXJyU2NvcGVdLCB1bmRlZmluZWQpO1xuICAgICAgICB9XG4gICAgICAgIGlmIChub2RlLmZpbmFsaXplcikge1xuICAgICAgICAgICAgYyhub2RlLmZpbmFsaXplciwgWywgY3VyclNjb3BlXSwgdW5kZWZpbmVkKTtcbiAgICAgICAgfVxuICAgIH0sXG5cbiAgICBDYXRjaENsYXVzZTogKG5vZGUsIFssIGN1cnJCbG9ja10sIGMpID0+IHtcbiAgICAgICAgY29uc3QgY2F0Y2hCbG9jayA9IG5ldyBWYXJCbG9jayhcbiAgICAgICAgICAgIGN1cnJCbG9jayxcbiAgICAgICAgICAgIG5vZGUsXG4gICAgICAgICAgICBWYXJCbG9jay5ibG9ja1R5cGVzLmNhdGNoQmxvY2ssXG4gICAgICAgICAgICBjdXJyQmxvY2suaXNTdHJpY3RcbiAgICAgICAgKTtcbiAgICAgICAgYyhub2RlLnBhcmFtLFxuICAgICAgICAgICAgW1xuICAgICAgICAgICAgICAgIFZhckJsb2NrLmRlY2xhcmF0aW9uVHlwZXMucGFyYW1ldGVyRGVjbGFyYXRpb24sXG4gICAgICAgICAgICAgICAgY2F0Y2hCbG9ja1xuICAgICAgICAgICAgXSxcbiAgICAgICAgICAgICdQYXR0ZXJuJyk7XG4gICAgICAgIG5vZGUuYm9keVsnQGJsb2NrJ10gPSBjYXRjaEJsb2NrO1xuICAgICAgICB3YWxrLmJhc2UuQmxvY2tTdGF0ZW1lbnQobm9kZS5ib2R5LCBbLCBjYXRjaEJsb2NrXSwgYyk7XG4gICAgfSxcblxuICAgIC8vIENyZWF0ZSBWYXJCbG9jayBvZiB0eXBlIG5vcm1hbEJsb2NrXG4gICAgQmxvY2tTdGF0ZW1lbnQ6IChub2RlLCBbLCBjdXJyQmxvY2tdLCBjKSA9PiB7XG4gICAgICAgIGxldCBpbkJsb2NrO1xuICAgICAgICBpZiAoY3VyckJsb2NrLmlzU3RyaWN0KSB7XG4gICAgICAgICAgICBpbkJsb2NrID0gbmV3IFZhckJsb2NrKFxuICAgICAgICAgICAgICAgIGN1cnJCbG9jayxcbiAgICAgICAgICAgICAgICBub2RlLFxuICAgICAgICAgICAgICAgIFZhckJsb2NrLmJsb2NrVHlwZXMubm9ybWFsQmxvY2ssXG4gICAgICAgICAgICAgICAgY3VyckJsb2NrLmlzU3RyaWN0XG4gICAgICAgICAgICApO1xuICAgICAgICAgICAgbm9kZVsnQGJsb2NrJ10gPSBpbkJsb2NrO1xuICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgICAgaW5CbG9jayA9IGN1cnJCbG9jaztcbiAgICAgICAgfVxuICAgICAgICB3YWxrLmJhc2UuQmxvY2tTdGF0ZW1lbnQobm9kZSwgWywgaW5CbG9ja10sIGMpO1xuICAgIH1cbn0pO1xuXG4vLyBGb3IgdmFyaWFibGVzIGluIGdsb2JhbCBhbmQgYXJndW1lbnRzIGluIGZ1bmN0aW9uc1xuY29uc3QgdmFyaWFibGVVc2FnZUNvbGxlY3RvciA9IHdhbGsubWFrZSh7XG4gICAgVmFyaWFibGVQYXR0ZXJuOiAobm9kZSwgY3VyckJsb2NrLCBjKSA9PiB7XG4gICAgICAgIGMobm9kZSwgY3VyckJsb2NrLCAnSWRlbnRpZmllcicpO1xuICAgIH0sXG5cbiAgICBJZGVudGlmaWVyOiAobm9kZSwgY3VyckJsb2NrLCBjKSA9PiB7XG4gICAgICAgIGlmIChteVdhbGtlci5pc0R1bW15SWROb2RlKG5vZGUpKSB7XG4gICAgICAgICAgICAvLyBTa2lwIGR1bW15IElkIG5vZGVcbiAgICAgICAgICAgIHJldHVybjtcbiAgICAgICAgfVxuICAgICAgICBsZXQgYmxvY2sgPSBjdXJyQmxvY2s7XG4gICAgICAgIGNvbnN0IHZhck5hbWUgPSBub2RlLm5hbWU7XG5cbiAgICAgICAgd2hpbGUgKGJsb2NrICYmICFibG9jay5oYXNWYXIodmFyTmFtZSkpIHtcbiAgICAgICAgICAgIGlmICh2YXJOYW1lID09PSAnYXJndW1lbnRzJyAmJlxuICAgICAgICAgICAgICAgIChibG9jay5pc09sZEZ1bmN0aW9uQmxvY2soKSB8fFxuICAgICAgICAgICAgICAgICBibG9jay5pc1BhcmFtZXRlckJsb2NrKCkpKSB7XG4gICAgICAgICAgICAgICAgaWYgKGJsb2NrLmhhc1BhcmFtU2NvcGUpIHtcbiAgICAgICAgICAgICAgICAgICAgYmxvY2sgPSBibG9jay5wYXJlbjtcbiAgICAgICAgICAgICAgICAgICAgaWYgKGJsb2NrLmhhc1Zhcih2YXJOYW1lKSkgYnJlYWs7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIGJsb2NrLnVzZUFyZ3VtZW50c09iamVjdCA9IHRydWU7XG4gICAgICAgICAgICAgICAgLy8gY29uc2lkZXIgJ3ZhcicgaXMgdXNlZCBmb3IgZGVjbGFyYXRpb24gb2YgJ2FyZ3VtZW50cy4nXG4gICAgICAgICAgICAgICAgYmxvY2suYWRkRGVjbGFyZWRMb2NhbFZhcih2YXJOYW1lLCBWYXJCbG9jay5kZWNsYXJhdGlvblR5cGVzLnZhckRlY2xhcmF0aW9uKTtcbiAgICAgICAgICAgICAgICBicmVhaztcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGlmIChibG9jay5pc0dsb2JhbCgpKSB7XG4gICAgICAgICAgICAgICAgYmxvY2suYWRkRGVjbGFyZWRMb2NhbFZhcih2YXJOYW1lLCBWYXJCbG9jay5kZWNsYXJhdGlvblR5cGVzLmltcGxpY2l0R2xvYmFsRGVjbGFyYXRpb24pO1xuICAgICAgICAgICAgICAgIGJyZWFrO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgYmxvY2sgPSBibG9jay5wYXJlbjtcbiAgICAgICAgfVxuICAgICAgICBpZiAoYmxvY2suaGFzVmFyKHZhck5hbWUpKSB7XG4gICAgICAgICAgICBibG9jay5hZGRVc2VkVmFyKHZhck5hbWUpO1xuICAgICAgICB9XG4gICAgfSxcblxuICAgIFJldHVyblN0YXRlbWVudDogKG5vZGUsIGN1cnJCbG9jaywgYykgPT4ge1xuICAgICAgICBsZXQgYmxvY2sgPSBjdXJyQmxvY2s7XG4gICAgICAgIHdoaWxlIChibG9jay5pc0NhdGNoQmxvY2soKSB8fCBibG9jay5pc05vcm1hbEJsb2NrKCkpIHtcbiAgICAgICAgICAgIGJsb2NrID0gYmxvY2sucGFyZW47XG4gICAgICAgIH1cbiAgICAgICAgaWYgKCFibG9jay5pc0dsb2JhbCgpICYmIG5vZGUuYXJndW1lbnQgIT09IG51bGwpIHtcbiAgICAgICAgICAgIGJsb2NrLnVzZVJldHVybldpdGhBcmd1bWVudCA9IHRydWU7XG4gICAgICAgIH1cbiAgICAgICAgaWYgKG5vZGUuYXJndW1lbnQpIHtcbiAgICAgICAgICAgIGMobm9kZS5hcmd1bWVudCwgY3VyckJsb2NrLCB1bmRlZmluZWQpO1xuICAgICAgICB9XG4gICAgfSxcblxuICAgIEZ1bmN0aW9uOiAobm9kZSwgY3VyckJsb2NrLCBjKSA9PiB7XG4gICAgICAgIGlmIChub2RlLmlkKSBjKG5vZGUuaWQsIGN1cnJCbG9jaywgJ1BhdHRlcm4nKTtcbiAgICAgICAgaWYgKG5vZGVbJ0BibG9jayddKSB7XG4gICAgICAgICAgICBjb25zdCBwYXJhbUJsb2NrID0gbm9kZVsnQGJsb2NrJ107XG4gICAgICAgICAgICBmb3IgKGxldCBpID0gMDsgaSA8IG5vZGUucGFyYW1zLmxlbmd0aDsgaSsrKSB7XG4gICAgICAgICAgICAgICAgYyhub2RlLnBhcmFtc1tpXSwgcGFyYW1CbG9jaywgJ1BhdHRlcm4nKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgfVxuICAgICAgICBjKG5vZGUuYm9keSwgY3VyckJsb2NrKTtcbiAgICB9LFxuXG4gICAgU2NvcGVCb2R5OiAobm9kZSwgY3VyckJsb2NrLCBjKSA9PiB7XG4gICAgICAgIGMobm9kZSwgbm9kZVsnQGJsb2NrJ10gfHwgY3VyckJsb2NrKTtcbiAgICB9LFxuXG4gICAgQmxvY2tTdGF0ZW1lbnQ6IChub2RlLCBjdXJyQmxvY2ssIGMpID0+IHtcbiAgICAgICAgLy8gUHJvY2VzcyBCbG9ja1N0YXRlbWVudCB3aXRoIGNoYW5nZWQgVmFyQmxvY2tcbiAgICAgICAgd2Fsay5iYXNlLkJsb2NrU3RhdGVtZW50KG5vZGUsIG5vZGVbJ0BibG9jayddIHx8IGN1cnJCbG9jaywgYyk7XG4gICAgfVxufSk7XG5cblxuZXhwb3J0IGZ1bmN0aW9uIGFubm90YXRlQmxvY2tJbmZvKGFzdCwgZ1ZhckJsb2NrKSB7XG4gICAgYXN0WydAYmxvY2snXSA9IGdWYXJCbG9jaztcblxuICAgIGdWYXJCbG9jay5pc1N0cmljdCA9IGdWYXJCbG9jay5pc1N0cmljdCB8fFxuICAgICAgICAoYXN0LmJvZHlbMF0gJiYgaXNVc2VTdHJpY3QoYXN0LmJvZHlbMF0pKTtcblxuICAgIHdhbGsucmVjdXJzaXZlKGFzdCwgWywgZ1ZhckJsb2NrXSwgZGVjbGFyZWRWYXJpYWJsZUZpbmRlcik7XG4gICAgd2Fsay5yZWN1cnNpdmUoYXN0LCBnVmFyQmxvY2ssIHZhcmlhYmxlVXNhZ2VDb2xsZWN0b3IpO1xuICAgIHJldHVybiBhc3Q7XG59XG5cbi8vIGRlZmluZSBTY29wZSBjbGFzc1xuY2xhc3MgU2NvcGUge1xuICAgIGNvbnN0cnVjdG9yKHBhcmVuLCB2YXJNYXAsIHZiKSB7XG4gICAgICAgIHRoaXMucGFyZW4gPSBwYXJlbjtcbiAgICAgICAgdGhpcy52YXJNYXAgPSB2YXJNYXA7XG4gICAgICAgIHRoaXMudmIgPSB2YjtcbiAgICB9XG5cbiAgICAvLyBmaW5kIEFWYWwgb2YgYSB2YXJpYWJsZSBpbiB0aGUgY2hhaW5cbiAgICBnZXRBVmFsT2YodmFyTmFtZSkge1xuICAgICAgICBsZXQgY3VyciA9IHRoaXM7XG4gICAgICAgIHdoaWxlIChjdXJyICE9IG51bGwpIHtcbiAgICAgICAgICAgIGlmIChjdXJyLnZhck1hcC5oYXModmFyTmFtZSkpIHtcbiAgICAgICAgICAgICAgICByZXR1cm4gY3Vyci52YXJNYXAuZ2V0KHZhck5hbWUpO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgY3VyciA9IGN1cnIucGFyZW47XG4gICAgICAgIH1cbiAgICAgICAgLy8gcmV0dXJucyBkdW1teSBBVmFsIGZvciBub3QgZm91bmQgdmFyaWFibGVzXG4gICAgICAgIHJldHVybiB0eXBlcy5BVmFsTnVsbDtcbiAgICB9XG5cbiAgICAvLyByZW1vdmUgaW5pdGlhbCBjYXRjaCBzY29wZXMgZnJvbSB0aGUgY2hhaW5cbiAgICByZW1vdmVJbml0aWFsQ2F0Y2hPck5vcm1hbEJsb2NrcygpIHtcbiAgICAgICAgbGV0IGN1cnIgPSB0aGlzO1xuICAgICAgICB3aGlsZSAoY3Vyci52Yi5pc0NhdGNoQmxvY2soKSB8fCBjdXJyLnZiLmlzTm9ybWFsQmxvY2soKSkge1xuICAgICAgICAgICAgY3VyciA9IGN1cnIucGFyZW47XG4gICAgICAgIH1cbiAgICAgICAgcmV0dXJuIGN1cnI7XG4gICAgfVxufVxuIiwiY29uc3Qgd2FsayA9IHJlcXVpcmUoJ2Fjb3JuL2Rpc3Qvd2FsaycpO1xuaW1wb3J0ICogYXMgbXlXYWxrZXIgZnJvbSAnLi91dGlsL215V2Fsa2VyJ1xuXG4vKipcbiAqXG4gKiBAcGFyYW0gYXN0IC0gc2NvcGUgYW5ub3RhdGVkIEFTVFxuICogQHBhcmFtIHtudW1iZXJ9IHBvcyAtIGNoYXJhY3RlciBwb3NpdGlvblxuICogQHJldHVybnMgeyp9IC0gYXJyYXkgb2YgQVNUIG5vZGVzXG4gKi9cbmZ1bmN0aW9uIGZpbmRWYXJSZWZzQXQoYXN0LCBwb3MpIHtcbiAgICAndXNlIHN0cmljdCc7XG4gICAgY29uc3QgZm91bmQgPSBteVdhbGtlci5maW5kSWRlbnRpZmllckF0KGFzdCwgcG9zKTtcbiAgICBpZiAoIWZvdW5kKSB7XG4gICAgICAgIC8vIHBvcyBpcyBub3QgYXQgYSB2YXJpYWJsZVxuICAgICAgICByZXR1cm4gbnVsbDtcbiAgICB9XG4gICAgLy8gZmluZCByZWZzIGZvciB0aGUgaWQgbm9kZVxuICAgIGNvbnN0IHJlZnMgPSBmaW5kUmVmc1RvVmFyaWFibGUoZm91bmQpLm1hcChub2RlID0+XG4gICAgICAgICh7c3RhcnQ6IG5vZGUuc3RhcnQsIGVuZDogbm9kZS5lbmR9KVxuICAgICk7XG4gICAgcmVmcy52YXJOYW1lID0gZm91bmQubm9kZS5uYW1lO1xuXG4gICAgcmV0dXJuIHJlZnM7XG59XG5cbi8qKlxuICpcbiAqIEBwYXJhbSBmb3VuZCAtIG5vZGUgYW5kIHZhckJsb2NrIG9mIHRoZSB2YXJpYWJsZVxuICogQHJldHVybnMge0FycmF5fSAtIGFycmF5IG9mIEFTVCBub2Rlc1xuICovXG5mdW5jdGlvbiBmaW5kUmVmc1RvVmFyaWFibGUoZm91bmQpIHtcbiAgICAndXNlIHN0cmljdCc7XG4gICAgY29uc3QgdmFyTmFtZSA9IGZvdW5kLm5vZGUubmFtZTtcbiAgICBjb25zdCB2YjEgPSBmb3VuZC52Yi5maW5kVmFySW5DaGFpbih2YXJOYW1lKTtcbiAgICBpZiAoIXZiMSkgcmV0dXJuIFtdO1xuXG4gICAgY29uc3QgcmVmcyA9IFtdO1xuXG4gICAgY29uc3Qgd2Fsa2VyID0gd2Fsay5tYWtlKHtcbiAgICAgICAgSWRlbnRpZmllcjogKG5vZGUsIHZiKSA9PiB7XG4gICAgICAgICAgICBpZiAobm9kZS5uYW1lICE9PSB2YXJOYW1lKSByZXR1cm47XG4gICAgICAgICAgICBpZiAodmIxID09PSB2Yi5maW5kVmFySW5DaGFpbih2YXJOYW1lKSkge1xuICAgICAgICAgICAgICAgIHJlZnMucHVzaChub2RlKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgfVxuICAgIH0sIG15V2Fsa2VyLnZhcldhbGtlcik7XG5cbiAgICB3YWxrLnJlY3Vyc2l2ZSh2YjEub3JpZ2luTm9kZSwgdmIxLm9yaWdpbk5vZGVbJ0BibG9jayddLCB3YWxrZXIpO1xuICAgIHJldHVybiByZWZzO1xufVxuXG5leHBvcnRzLmZpbmRWYXJSZWZzQXQgPSBmaW5kVmFyUmVmc0F0O1xuIiwiKGZ1bmN0aW9uKGYpe2lmKHR5cGVvZiBleHBvcnRzPT09XCJvYmplY3RcIiYmdHlwZW9mIG1vZHVsZSE9PVwidW5kZWZpbmVkXCIpe21vZHVsZS5leHBvcnRzPWYoKX1lbHNlIGlmKHR5cGVvZiBkZWZpbmU9PT1cImZ1bmN0aW9uXCImJmRlZmluZS5hbWQpe2RlZmluZShbXSxmKX1lbHNle3ZhciBnO2lmKHR5cGVvZiB3aW5kb3chPT1cInVuZGVmaW5lZFwiKXtnPXdpbmRvd31lbHNlIGlmKHR5cGVvZiBnbG9iYWwhPT1cInVuZGVmaW5lZFwiKXtnPWdsb2JhbH1lbHNlIGlmKHR5cGVvZiBzZWxmIT09XCJ1bmRlZmluZWRcIil7Zz1zZWxmfWVsc2V7Zz10aGlzfWcuYWNvcm4gPSBmKCl9fSkoZnVuY3Rpb24oKXt2YXIgZGVmaW5lLG1vZHVsZSxleHBvcnRzO3JldHVybiAoZnVuY3Rpb24gZSh0LG4scil7ZnVuY3Rpb24gcyhvLHUpe2lmKCFuW29dKXtpZighdFtvXSl7dmFyIGE9dHlwZW9mIHJlcXVpcmU9PVwiZnVuY3Rpb25cIiYmcmVxdWlyZTtpZighdSYmYSlyZXR1cm4gYShvLCEwKTtpZihpKXJldHVybiBpKG8sITApO3ZhciBmPW5ldyBFcnJvcihcIkNhbm5vdCBmaW5kIG1vZHVsZSAnXCIrbytcIidcIik7dGhyb3cgZi5jb2RlPVwiTU9EVUxFX05PVF9GT1VORFwiLGZ9dmFyIGw9bltvXT17ZXhwb3J0czp7fX07dFtvXVswXS5jYWxsKGwuZXhwb3J0cyxmdW5jdGlvbihlKXt2YXIgbj10W29dWzFdW2VdO3JldHVybiBzKG4/bjplKX0sbCxsLmV4cG9ydHMsZSx0LG4scil9cmV0dXJuIG5bb10uZXhwb3J0c312YXIgaT10eXBlb2YgcmVxdWlyZT09XCJmdW5jdGlvblwiJiZyZXF1aXJlO2Zvcih2YXIgbz0wO288ci5sZW5ndGg7bysrKXMocltvXSk7cmV0dXJuIHN9KSh7MTpbZnVuY3Rpb24oX2RlcmVxXyxtb2R1bGUsZXhwb3J0cyl7XG4vLyBBIHJlY3Vyc2l2ZSBkZXNjZW50IHBhcnNlciBvcGVyYXRlcyBieSBkZWZpbmluZyBmdW5jdGlvbnMgZm9yIGFsbFxuLy8gc3ludGFjdGljIGVsZW1lbnRzLCBhbmQgcmVjdXJzaXZlbHkgY2FsbGluZyB0aG9zZSwgZWFjaCBmdW5jdGlvblxuLy8gYWR2YW5jaW5nIHRoZSBpbnB1dCBzdHJlYW0gYW5kIHJldHVybmluZyBhbiBBU1Qgbm9kZS4gUHJlY2VkZW5jZVxuLy8gb2YgY29uc3RydWN0cyAoZm9yIGV4YW1wbGUsIHRoZSBmYWN0IHRoYXQgYCF4WzFdYCBtZWFucyBgISh4WzFdKWBcbi8vIGluc3RlYWQgb2YgYCgheClbMV1gIGlzIGhhbmRsZWQgYnkgdGhlIGZhY3QgdGhhdCB0aGUgcGFyc2VyXG4vLyBmdW5jdGlvbiB0aGF0IHBhcnNlcyB1bmFyeSBwcmVmaXggb3BlcmF0b3JzIGlzIGNhbGxlZCBmaXJzdCwgYW5kXG4vLyBpbiB0dXJuIGNhbGxzIHRoZSBmdW5jdGlvbiB0aGF0IHBhcnNlcyBgW11gIHN1YnNjcmlwdHMg4oCUIHRoYXRcbi8vIHdheSwgaXQnbGwgcmVjZWl2ZSB0aGUgbm9kZSBmb3IgYHhbMV1gIGFscmVhZHkgcGFyc2VkLCBhbmQgd3JhcHNcbi8vICp0aGF0KiBpbiB0aGUgdW5hcnkgb3BlcmF0b3Igbm9kZS5cbi8vXG4vLyBBY29ybiB1c2VzIGFuIFtvcGVyYXRvciBwcmVjZWRlbmNlIHBhcnNlcl1bb3BwXSB0byBoYW5kbGUgYmluYXJ5XG4vLyBvcGVyYXRvciBwcmVjZWRlbmNlLCBiZWNhdXNlIGl0IGlzIG11Y2ggbW9yZSBjb21wYWN0IHRoYW4gdXNpbmdcbi8vIHRoZSB0ZWNobmlxdWUgb3V0bGluZWQgYWJvdmUsIHdoaWNoIHVzZXMgZGlmZmVyZW50LCBuZXN0aW5nXG4vLyBmdW5jdGlvbnMgdG8gc3BlY2lmeSBwcmVjZWRlbmNlLCBmb3IgYWxsIG9mIHRoZSB0ZW4gYmluYXJ5XG4vLyBwcmVjZWRlbmNlIGxldmVscyB0aGF0IEphdmFTY3JpcHQgZGVmaW5lcy5cbi8vXG4vLyBbb3BwXTogaHR0cDovL2VuLndpa2lwZWRpYS5vcmcvd2lraS9PcGVyYXRvci1wcmVjZWRlbmNlX3BhcnNlclxuXG5cInVzZSBzdHJpY3RcIjtcblxudmFyIF90b2tlbnR5cGUgPSBfZGVyZXFfKFwiLi90b2tlbnR5cGVcIik7XG5cbnZhciBfc3RhdGUgPSBfZGVyZXFfKFwiLi9zdGF0ZVwiKTtcblxudmFyIF9pZGVudGlmaWVyID0gX2RlcmVxXyhcIi4vaWRlbnRpZmllclwiKTtcblxudmFyIF91dGlsID0gX2RlcmVxXyhcIi4vdXRpbFwiKTtcblxudmFyIHBwID0gX3N0YXRlLlBhcnNlci5wcm90b3R5cGU7XG5cbi8vIENoZWNrIGlmIHByb3BlcnR5IG5hbWUgY2xhc2hlcyB3aXRoIGFscmVhZHkgYWRkZWQuXG4vLyBPYmplY3QvY2xhc3MgZ2V0dGVycyBhbmQgc2V0dGVycyBhcmUgbm90IGFsbG93ZWQgdG8gY2xhc2gg4oCUXG4vLyBlaXRoZXIgd2l0aCBlYWNoIG90aGVyIG9yIHdpdGggYW4gaW5pdCBwcm9wZXJ0eSDigJQgYW5kIGluXG4vLyBzdHJpY3QgbW9kZSwgaW5pdCBwcm9wZXJ0aWVzIGFyZSBhbHNvIG5vdCBhbGxvd2VkIHRvIGJlIHJlcGVhdGVkLlxuXG5wcC5jaGVja1Byb3BDbGFzaCA9IGZ1bmN0aW9uIChwcm9wLCBwcm9wSGFzaCkge1xuICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYgJiYgKHByb3AuY29tcHV0ZWQgfHwgcHJvcC5tZXRob2QgfHwgcHJvcC5zaG9ydGhhbmQpKSByZXR1cm47XG4gIHZhciBrZXkgPSBwcm9wLmtleSxcbiAgICAgIG5hbWUgPSB1bmRlZmluZWQ7XG4gIHN3aXRjaCAoa2V5LnR5cGUpIHtcbiAgICBjYXNlIFwiSWRlbnRpZmllclwiOlxuICAgICAgbmFtZSA9IGtleS5uYW1lO2JyZWFrO1xuICAgIGNhc2UgXCJMaXRlcmFsXCI6XG4gICAgICBuYW1lID0gU3RyaW5nKGtleS52YWx1ZSk7YnJlYWs7XG4gICAgZGVmYXVsdDpcbiAgICAgIHJldHVybjtcbiAgfVxuICB2YXIga2luZCA9IHByb3Aua2luZDtcbiAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KSB7XG4gICAgaWYgKG5hbWUgPT09IFwiX19wcm90b19fXCIgJiYga2luZCA9PT0gXCJpbml0XCIpIHtcbiAgICAgIGlmIChwcm9wSGFzaC5wcm90bykgdGhpcy5yYWlzZShrZXkuc3RhcnQsIFwiUmVkZWZpbml0aW9uIG9mIF9fcHJvdG9fXyBwcm9wZXJ0eVwiKTtcbiAgICAgIHByb3BIYXNoLnByb3RvID0gdHJ1ZTtcbiAgICB9XG4gICAgcmV0dXJuO1xuICB9XG4gIHZhciBvdGhlciA9IHVuZGVmaW5lZDtcbiAgaWYgKF91dGlsLmhhcyhwcm9wSGFzaCwgbmFtZSkpIHtcbiAgICBvdGhlciA9IHByb3BIYXNoW25hbWVdO1xuICAgIHZhciBpc0dldFNldCA9IGtpbmQgIT09IFwiaW5pdFwiO1xuICAgIGlmICgodGhpcy5zdHJpY3QgfHwgaXNHZXRTZXQpICYmIG90aGVyW2tpbmRdIHx8ICEoaXNHZXRTZXQgXiBvdGhlci5pbml0KSkgdGhpcy5yYWlzZShrZXkuc3RhcnQsIFwiUmVkZWZpbml0aW9uIG9mIHByb3BlcnR5XCIpO1xuICB9IGVsc2Uge1xuICAgIG90aGVyID0gcHJvcEhhc2hbbmFtZV0gPSB7XG4gICAgICBpbml0OiBmYWxzZSxcbiAgICAgIGdldDogZmFsc2UsXG4gICAgICBzZXQ6IGZhbHNlXG4gICAgfTtcbiAgfVxuICBvdGhlcltraW5kXSA9IHRydWU7XG59O1xuXG4vLyAjIyMgRXhwcmVzc2lvbiBwYXJzaW5nXG5cbi8vIFRoZXNlIG5lc3QsIGZyb20gdGhlIG1vc3QgZ2VuZXJhbCBleHByZXNzaW9uIHR5cGUgYXQgdGhlIHRvcCB0b1xuLy8gJ2F0b21pYycsIG5vbmRpdmlzaWJsZSBleHByZXNzaW9uIHR5cGVzIGF0IHRoZSBib3R0b20uIE1vc3Qgb2Zcbi8vIHRoZSBmdW5jdGlvbnMgd2lsbCBzaW1wbHkgbGV0IHRoZSBmdW5jdGlvbihzKSBiZWxvdyB0aGVtIHBhcnNlLFxuLy8gYW5kLCAqaWYqIHRoZSBzeW50YWN0aWMgY29uc3RydWN0IHRoZXkgaGFuZGxlIGlzIHByZXNlbnQsIHdyYXBcbi8vIHRoZSBBU1Qgbm9kZSB0aGF0IHRoZSBpbm5lciBwYXJzZXIgZ2F2ZSB0aGVtIGluIGFub3RoZXIgbm9kZS5cblxuLy8gUGFyc2UgYSBmdWxsIGV4cHJlc3Npb24uIFRoZSBvcHRpb25hbCBhcmd1bWVudHMgYXJlIHVzZWQgdG9cbi8vIGZvcmJpZCB0aGUgYGluYCBvcGVyYXRvciAoaW4gZm9yIGxvb3BzIGluaXRhbGl6YXRpb24gZXhwcmVzc2lvbnMpXG4vLyBhbmQgcHJvdmlkZSByZWZlcmVuY2UgZm9yIHN0b3JpbmcgJz0nIG9wZXJhdG9yIGluc2lkZSBzaG9ydGhhbmRcbi8vIHByb3BlcnR5IGFzc2lnbm1lbnQgaW4gY29udGV4dHMgd2hlcmUgYm90aCBvYmplY3QgZXhwcmVzc2lvblxuLy8gYW5kIG9iamVjdCBwYXR0ZXJuIG1pZ2h0IGFwcGVhciAoc28gaXQncyBwb3NzaWJsZSB0byByYWlzZVxuLy8gZGVsYXllZCBzeW50YXggZXJyb3IgYXQgY29ycmVjdCBwb3NpdGlvbikuXG5cbnBwLnBhcnNlRXhwcmVzc2lvbiA9IGZ1bmN0aW9uIChub0luLCByZWZTaG9ydGhhbmREZWZhdWx0UG9zKSB7XG4gIHZhciBzdGFydFBvcyA9IHRoaXMuc3RhcnQsXG4gICAgICBzdGFydExvYyA9IHRoaXMuc3RhcnRMb2M7XG4gIHZhciBleHByID0gdGhpcy5wYXJzZU1heWJlQXNzaWduKG5vSW4sIHJlZlNob3J0aGFuZERlZmF1bHRQb3MpO1xuICBpZiAodGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLmNvbW1hKSB7XG4gICAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0UG9zLCBzdGFydExvYyk7XG4gICAgbm9kZS5leHByZXNzaW9ucyA9IFtleHByXTtcbiAgICB3aGlsZSAodGhpcy5lYXQoX3Rva2VudHlwZS50eXBlcy5jb21tYSkpIG5vZGUuZXhwcmVzc2lvbnMucHVzaCh0aGlzLnBhcnNlTWF5YmVBc3NpZ24obm9JbiwgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcykpO1xuICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJTZXF1ZW5jZUV4cHJlc3Npb25cIik7XG4gIH1cbiAgcmV0dXJuIGV4cHI7XG59O1xuXG4vLyBQYXJzZSBhbiBhc3NpZ25tZW50IGV4cHJlc3Npb24uIFRoaXMgaW5jbHVkZXMgYXBwbGljYXRpb25zIG9mXG4vLyBvcGVyYXRvcnMgbGlrZSBgKz1gLlxuXG5wcC5wYXJzZU1heWJlQXNzaWduID0gZnVuY3Rpb24gKG5vSW4sIHJlZlNob3J0aGFuZERlZmF1bHRQb3MsIGFmdGVyTGVmdFBhcnNlKSB7XG4gIGlmICh0aGlzLnR5cGUgPT0gX3Rva2VudHlwZS50eXBlcy5feWllbGQgJiYgdGhpcy5pbkdlbmVyYXRvcikgcmV0dXJuIHRoaXMucGFyc2VZaWVsZCgpO1xuXG4gIHZhciBmYWlsT25TaG9ydGhhbmRBc3NpZ24gPSB1bmRlZmluZWQ7XG4gIGlmICghcmVmU2hvcnRoYW5kRGVmYXVsdFBvcykge1xuICAgIHJlZlNob3J0aGFuZERlZmF1bHRQb3MgPSB7IHN0YXJ0OiAwIH07XG4gICAgZmFpbE9uU2hvcnRoYW5kQXNzaWduID0gdHJ1ZTtcbiAgfSBlbHNlIHtcbiAgICBmYWlsT25TaG9ydGhhbmRBc3NpZ24gPSBmYWxzZTtcbiAgfVxuICB2YXIgc3RhcnRQb3MgPSB0aGlzLnN0YXJ0LFxuICAgICAgc3RhcnRMb2MgPSB0aGlzLnN0YXJ0TG9jO1xuICBpZiAodGhpcy50eXBlID09IF90b2tlbnR5cGUudHlwZXMucGFyZW5MIHx8IHRoaXMudHlwZSA9PSBfdG9rZW50eXBlLnR5cGVzLm5hbWUpIHRoaXMucG90ZW50aWFsQXJyb3dBdCA9IHRoaXMuc3RhcnQ7XG4gIHZhciBsZWZ0ID0gdGhpcy5wYXJzZU1heWJlQ29uZGl0aW9uYWwobm9JbiwgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcyk7XG4gIGlmIChhZnRlckxlZnRQYXJzZSkgbGVmdCA9IGFmdGVyTGVmdFBhcnNlLmNhbGwodGhpcywgbGVmdCwgc3RhcnRQb3MsIHN0YXJ0TG9jKTtcbiAgaWYgKHRoaXMudHlwZS5pc0Fzc2lnbikge1xuICAgIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGVBdChzdGFydFBvcywgc3RhcnRMb2MpO1xuICAgIG5vZGUub3BlcmF0b3IgPSB0aGlzLnZhbHVlO1xuICAgIG5vZGUubGVmdCA9IHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5lcSA/IHRoaXMudG9Bc3NpZ25hYmxlKGxlZnQpIDogbGVmdDtcbiAgICByZWZTaG9ydGhhbmREZWZhdWx0UG9zLnN0YXJ0ID0gMDsgLy8gcmVzZXQgYmVjYXVzZSBzaG9ydGhhbmQgZGVmYXVsdCB3YXMgdXNlZCBjb3JyZWN0bHlcbiAgICB0aGlzLmNoZWNrTFZhbChsZWZ0KTtcbiAgICB0aGlzLm5leHQoKTtcbiAgICBub2RlLnJpZ2h0ID0gdGhpcy5wYXJzZU1heWJlQXNzaWduKG5vSW4pO1xuICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJBc3NpZ25tZW50RXhwcmVzc2lvblwiKTtcbiAgfSBlbHNlIGlmIChmYWlsT25TaG9ydGhhbmRBc3NpZ24gJiYgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcy5zdGFydCkge1xuICAgIHRoaXMudW5leHBlY3RlZChyZWZTaG9ydGhhbmREZWZhdWx0UG9zLnN0YXJ0KTtcbiAgfVxuICByZXR1cm4gbGVmdDtcbn07XG5cbi8vIFBhcnNlIGEgdGVybmFyeSBjb25kaXRpb25hbCAoYD86YCkgb3BlcmF0b3IuXG5cbnBwLnBhcnNlTWF5YmVDb25kaXRpb25hbCA9IGZ1bmN0aW9uIChub0luLCByZWZTaG9ydGhhbmREZWZhdWx0UG9zKSB7XG4gIHZhciBzdGFydFBvcyA9IHRoaXMuc3RhcnQsXG4gICAgICBzdGFydExvYyA9IHRoaXMuc3RhcnRMb2M7XG4gIHZhciBleHByID0gdGhpcy5wYXJzZUV4cHJPcHMobm9JbiwgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcyk7XG4gIGlmIChyZWZTaG9ydGhhbmREZWZhdWx0UG9zICYmIHJlZlNob3J0aGFuZERlZmF1bHRQb3Muc3RhcnQpIHJldHVybiBleHByO1xuICBpZiAodGhpcy5lYXQoX3Rva2VudHlwZS50eXBlcy5xdWVzdGlvbikpIHtcbiAgICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlQXQoc3RhcnRQb3MsIHN0YXJ0TG9jKTtcbiAgICBub2RlLnRlc3QgPSBleHByO1xuICAgIG5vZGUuY29uc2VxdWVudCA9IHRoaXMucGFyc2VNYXliZUFzc2lnbigpO1xuICAgIHRoaXMuZXhwZWN0KF90b2tlbnR5cGUudHlwZXMuY29sb24pO1xuICAgIG5vZGUuYWx0ZXJuYXRlID0gdGhpcy5wYXJzZU1heWJlQXNzaWduKG5vSW4pO1xuICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJDb25kaXRpb25hbEV4cHJlc3Npb25cIik7XG4gIH1cbiAgcmV0dXJuIGV4cHI7XG59O1xuXG4vLyBTdGFydCB0aGUgcHJlY2VkZW5jZSBwYXJzZXIuXG5cbnBwLnBhcnNlRXhwck9wcyA9IGZ1bmN0aW9uIChub0luLCByZWZTaG9ydGhhbmREZWZhdWx0UG9zKSB7XG4gIHZhciBzdGFydFBvcyA9IHRoaXMuc3RhcnQsXG4gICAgICBzdGFydExvYyA9IHRoaXMuc3RhcnRMb2M7XG4gIHZhciBleHByID0gdGhpcy5wYXJzZU1heWJlVW5hcnkocmVmU2hvcnRoYW5kRGVmYXVsdFBvcyk7XG4gIGlmIChyZWZTaG9ydGhhbmREZWZhdWx0UG9zICYmIHJlZlNob3J0aGFuZERlZmF1bHRQb3Muc3RhcnQpIHJldHVybiBleHByO1xuICByZXR1cm4gdGhpcy5wYXJzZUV4cHJPcChleHByLCBzdGFydFBvcywgc3RhcnRMb2MsIC0xLCBub0luKTtcbn07XG5cbi8vIFBhcnNlIGJpbmFyeSBvcGVyYXRvcnMgd2l0aCB0aGUgb3BlcmF0b3IgcHJlY2VkZW5jZSBwYXJzaW5nXG4vLyBhbGdvcml0aG0uIGBsZWZ0YCBpcyB0aGUgbGVmdC1oYW5kIHNpZGUgb2YgdGhlIG9wZXJhdG9yLlxuLy8gYG1pblByZWNgIHByb3ZpZGVzIGNvbnRleHQgdGhhdCBhbGxvd3MgdGhlIGZ1bmN0aW9uIHRvIHN0b3AgYW5kXG4vLyBkZWZlciBmdXJ0aGVyIHBhcnNlciB0byBvbmUgb2YgaXRzIGNhbGxlcnMgd2hlbiBpdCBlbmNvdW50ZXJzIGFuXG4vLyBvcGVyYXRvciB0aGF0IGhhcyBhIGxvd2VyIHByZWNlZGVuY2UgdGhhbiB0aGUgc2V0IGl0IGlzIHBhcnNpbmcuXG5cbnBwLnBhcnNlRXhwck9wID0gZnVuY3Rpb24gKGxlZnQsIGxlZnRTdGFydFBvcywgbGVmdFN0YXJ0TG9jLCBtaW5QcmVjLCBub0luKSB7XG4gIHZhciBwcmVjID0gdGhpcy50eXBlLmJpbm9wO1xuICBpZiAocHJlYyAhPSBudWxsICYmICghbm9JbiB8fCB0aGlzLnR5cGUgIT09IF90b2tlbnR5cGUudHlwZXMuX2luKSkge1xuICAgIGlmIChwcmVjID4gbWluUHJlYykge1xuICAgICAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZUF0KGxlZnRTdGFydFBvcywgbGVmdFN0YXJ0TG9jKTtcbiAgICAgIG5vZGUubGVmdCA9IGxlZnQ7XG4gICAgICBub2RlLm9wZXJhdG9yID0gdGhpcy52YWx1ZTtcbiAgICAgIHZhciBvcCA9IHRoaXMudHlwZTtcbiAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgdmFyIHN0YXJ0UG9zID0gdGhpcy5zdGFydCxcbiAgICAgICAgICBzdGFydExvYyA9IHRoaXMuc3RhcnRMb2M7XG4gICAgICBub2RlLnJpZ2h0ID0gdGhpcy5wYXJzZUV4cHJPcCh0aGlzLnBhcnNlTWF5YmVVbmFyeSgpLCBzdGFydFBvcywgc3RhcnRMb2MsIHByZWMsIG5vSW4pO1xuICAgICAgdGhpcy5maW5pc2hOb2RlKG5vZGUsIG9wID09PSBfdG9rZW50eXBlLnR5cGVzLmxvZ2ljYWxPUiB8fCBvcCA9PT0gX3Rva2VudHlwZS50eXBlcy5sb2dpY2FsQU5EID8gXCJMb2dpY2FsRXhwcmVzc2lvblwiIDogXCJCaW5hcnlFeHByZXNzaW9uXCIpO1xuICAgICAgcmV0dXJuIHRoaXMucGFyc2VFeHByT3Aobm9kZSwgbGVmdFN0YXJ0UG9zLCBsZWZ0U3RhcnRMb2MsIG1pblByZWMsIG5vSW4pO1xuICAgIH1cbiAgfVxuICByZXR1cm4gbGVmdDtcbn07XG5cbi8vIFBhcnNlIHVuYXJ5IG9wZXJhdG9ycywgYm90aCBwcmVmaXggYW5kIHBvc3RmaXguXG5cbnBwLnBhcnNlTWF5YmVVbmFyeSA9IGZ1bmN0aW9uIChyZWZTaG9ydGhhbmREZWZhdWx0UG9zKSB7XG4gIGlmICh0aGlzLnR5cGUucHJlZml4KSB7XG4gICAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpLFxuICAgICAgICB1cGRhdGUgPSB0aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuaW5jRGVjO1xuICAgIG5vZGUub3BlcmF0b3IgPSB0aGlzLnZhbHVlO1xuICAgIG5vZGUucHJlZml4ID0gdHJ1ZTtcbiAgICB0aGlzLm5leHQoKTtcbiAgICBub2RlLmFyZ3VtZW50ID0gdGhpcy5wYXJzZU1heWJlVW5hcnkoKTtcbiAgICBpZiAocmVmU2hvcnRoYW5kRGVmYXVsdFBvcyAmJiByZWZTaG9ydGhhbmREZWZhdWx0UG9zLnN0YXJ0KSB0aGlzLnVuZXhwZWN0ZWQocmVmU2hvcnRoYW5kRGVmYXVsdFBvcy5zdGFydCk7XG4gICAgaWYgKHVwZGF0ZSkgdGhpcy5jaGVja0xWYWwobm9kZS5hcmd1bWVudCk7ZWxzZSBpZiAodGhpcy5zdHJpY3QgJiYgbm9kZS5vcGVyYXRvciA9PT0gXCJkZWxldGVcIiAmJiBub2RlLmFyZ3VtZW50LnR5cGUgPT09IFwiSWRlbnRpZmllclwiKSB0aGlzLnJhaXNlKG5vZGUuc3RhcnQsIFwiRGVsZXRpbmcgbG9jYWwgdmFyaWFibGUgaW4gc3RyaWN0IG1vZGVcIik7XG4gICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCB1cGRhdGUgPyBcIlVwZGF0ZUV4cHJlc3Npb25cIiA6IFwiVW5hcnlFeHByZXNzaW9uXCIpO1xuICB9XG4gIHZhciBzdGFydFBvcyA9IHRoaXMuc3RhcnQsXG4gICAgICBzdGFydExvYyA9IHRoaXMuc3RhcnRMb2M7XG4gIHZhciBleHByID0gdGhpcy5wYXJzZUV4cHJTdWJzY3JpcHRzKHJlZlNob3J0aGFuZERlZmF1bHRQb3MpO1xuICBpZiAocmVmU2hvcnRoYW5kRGVmYXVsdFBvcyAmJiByZWZTaG9ydGhhbmREZWZhdWx0UG9zLnN0YXJ0KSByZXR1cm4gZXhwcjtcbiAgd2hpbGUgKHRoaXMudHlwZS5wb3N0Zml4ICYmICF0aGlzLmNhbkluc2VydFNlbWljb2xvbigpKSB7XG4gICAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0UG9zLCBzdGFydExvYyk7XG4gICAgbm9kZS5vcGVyYXRvciA9IHRoaXMudmFsdWU7XG4gICAgbm9kZS5wcmVmaXggPSBmYWxzZTtcbiAgICBub2RlLmFyZ3VtZW50ID0gZXhwcjtcbiAgICB0aGlzLmNoZWNrTFZhbChleHByKTtcbiAgICB0aGlzLm5leHQoKTtcbiAgICBleHByID0gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiVXBkYXRlRXhwcmVzc2lvblwiKTtcbiAgfVxuICByZXR1cm4gZXhwcjtcbn07XG5cbi8vIFBhcnNlIGNhbGwsIGRvdCwgYW5kIGBbXWAtc3Vic2NyaXB0IGV4cHJlc3Npb25zLlxuXG5wcC5wYXJzZUV4cHJTdWJzY3JpcHRzID0gZnVuY3Rpb24gKHJlZlNob3J0aGFuZERlZmF1bHRQb3MpIHtcbiAgdmFyIHN0YXJ0UG9zID0gdGhpcy5zdGFydCxcbiAgICAgIHN0YXJ0TG9jID0gdGhpcy5zdGFydExvYztcbiAgdmFyIGV4cHIgPSB0aGlzLnBhcnNlRXhwckF0b20ocmVmU2hvcnRoYW5kRGVmYXVsdFBvcyk7XG4gIGlmIChyZWZTaG9ydGhhbmREZWZhdWx0UG9zICYmIHJlZlNob3J0aGFuZERlZmF1bHRQb3Muc3RhcnQpIHJldHVybiBleHByO1xuICByZXR1cm4gdGhpcy5wYXJzZVN1YnNjcmlwdHMoZXhwciwgc3RhcnRQb3MsIHN0YXJ0TG9jKTtcbn07XG5cbnBwLnBhcnNlU3Vic2NyaXB0cyA9IGZ1bmN0aW9uIChiYXNlLCBzdGFydFBvcywgc3RhcnRMb2MsIG5vQ2FsbHMpIHtcbiAgZm9yICg7Oykge1xuICAgIGlmICh0aGlzLmVhdChfdG9rZW50eXBlLnR5cGVzLmRvdCkpIHtcbiAgICAgIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGVBdChzdGFydFBvcywgc3RhcnRMb2MpO1xuICAgICAgbm9kZS5vYmplY3QgPSBiYXNlO1xuICAgICAgbm9kZS5wcm9wZXJ0eSA9IHRoaXMucGFyc2VJZGVudCh0cnVlKTtcbiAgICAgIG5vZGUuY29tcHV0ZWQgPSBmYWxzZTtcbiAgICAgIGJhc2UgPSB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJNZW1iZXJFeHByZXNzaW9uXCIpO1xuICAgIH0gZWxzZSBpZiAodGhpcy5lYXQoX3Rva2VudHlwZS50eXBlcy5icmFja2V0TCkpIHtcbiAgICAgIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGVBdChzdGFydFBvcywgc3RhcnRMb2MpO1xuICAgICAgbm9kZS5vYmplY3QgPSBiYXNlO1xuICAgICAgbm9kZS5wcm9wZXJ0eSA9IHRoaXMucGFyc2VFeHByZXNzaW9uKCk7XG4gICAgICBub2RlLmNvbXB1dGVkID0gdHJ1ZTtcbiAgICAgIHRoaXMuZXhwZWN0KF90b2tlbnR5cGUudHlwZXMuYnJhY2tldFIpO1xuICAgICAgYmFzZSA9IHRoaXMuZmluaXNoTm9kZShub2RlLCBcIk1lbWJlckV4cHJlc3Npb25cIik7XG4gICAgfSBlbHNlIGlmICghbm9DYWxscyAmJiB0aGlzLmVhdChfdG9rZW50eXBlLnR5cGVzLnBhcmVuTCkpIHtcbiAgICAgIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGVBdChzdGFydFBvcywgc3RhcnRMb2MpO1xuICAgICAgbm9kZS5jYWxsZWUgPSBiYXNlO1xuICAgICAgbm9kZS5hcmd1bWVudHMgPSB0aGlzLnBhcnNlRXhwckxpc3QoX3Rva2VudHlwZS50eXBlcy5wYXJlblIsIGZhbHNlKTtcbiAgICAgIGJhc2UgPSB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJDYWxsRXhwcmVzc2lvblwiKTtcbiAgICB9IGVsc2UgaWYgKHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5iYWNrUXVvdGUpIHtcbiAgICAgIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGVBdChzdGFydFBvcywgc3RhcnRMb2MpO1xuICAgICAgbm9kZS50YWcgPSBiYXNlO1xuICAgICAgbm9kZS5xdWFzaSA9IHRoaXMucGFyc2VUZW1wbGF0ZSgpO1xuICAgICAgYmFzZSA9IHRoaXMuZmluaXNoTm9kZShub2RlLCBcIlRhZ2dlZFRlbXBsYXRlRXhwcmVzc2lvblwiKTtcbiAgICB9IGVsc2Uge1xuICAgICAgcmV0dXJuIGJhc2U7XG4gICAgfVxuICB9XG59O1xuXG4vLyBQYXJzZSBhbiBhdG9taWMgZXhwcmVzc2lvbiDigJQgZWl0aGVyIGEgc2luZ2xlIHRva2VuIHRoYXQgaXMgYW5cbi8vIGV4cHJlc3Npb24sIGFuIGV4cHJlc3Npb24gc3RhcnRlZCBieSBhIGtleXdvcmQgbGlrZSBgZnVuY3Rpb25gIG9yXG4vLyBgbmV3YCwgb3IgYW4gZXhwcmVzc2lvbiB3cmFwcGVkIGluIHB1bmN0dWF0aW9uIGxpa2UgYCgpYCwgYFtdYCxcbi8vIG9yIGB7fWAuXG5cbnBwLnBhcnNlRXhwckF0b20gPSBmdW5jdGlvbiAocmVmU2hvcnRoYW5kRGVmYXVsdFBvcykge1xuICB2YXIgbm9kZSA9IHVuZGVmaW5lZCxcbiAgICAgIGNhbkJlQXJyb3cgPSB0aGlzLnBvdGVudGlhbEFycm93QXQgPT0gdGhpcy5zdGFydDtcbiAgc3dpdGNoICh0aGlzLnR5cGUpIHtcbiAgICBjYXNlIF90b2tlbnR5cGUudHlwZXMuX3N1cGVyOlxuICAgICAgaWYgKCF0aGlzLmluRnVuY3Rpb24pIHRoaXMucmFpc2UodGhpcy5zdGFydCwgXCInc3VwZXInIG91dHNpZGUgb2YgZnVuY3Rpb24gb3IgY2xhc3NcIik7XG4gICAgY2FzZSBfdG9rZW50eXBlLnR5cGVzLl90aGlzOlxuICAgICAgdmFyIHR5cGUgPSB0aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuX3RoaXMgPyBcIlRoaXNFeHByZXNzaW9uXCIgOiBcIlN1cGVyXCI7XG4gICAgICBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCB0eXBlKTtcblxuICAgIGNhc2UgX3Rva2VudHlwZS50eXBlcy5feWllbGQ6XG4gICAgICBpZiAodGhpcy5pbkdlbmVyYXRvcikgdGhpcy51bmV4cGVjdGVkKCk7XG5cbiAgICBjYXNlIF90b2tlbnR5cGUudHlwZXMubmFtZTpcbiAgICAgIHZhciBzdGFydFBvcyA9IHRoaXMuc3RhcnQsXG4gICAgICAgICAgc3RhcnRMb2MgPSB0aGlzLnN0YXJ0TG9jO1xuICAgICAgdmFyIGlkID0gdGhpcy5wYXJzZUlkZW50KHRoaXMudHlwZSAhPT0gX3Rva2VudHlwZS50eXBlcy5uYW1lKTtcbiAgICAgIGlmIChjYW5CZUFycm93ICYmICF0aGlzLmNhbkluc2VydFNlbWljb2xvbigpICYmIHRoaXMuZWF0KF90b2tlbnR5cGUudHlwZXMuYXJyb3cpKSByZXR1cm4gdGhpcy5wYXJzZUFycm93RXhwcmVzc2lvbih0aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0UG9zLCBzdGFydExvYyksIFtpZF0pO1xuICAgICAgcmV0dXJuIGlkO1xuXG4gICAgY2FzZSBfdG9rZW50eXBlLnR5cGVzLnJlZ2V4cDpcbiAgICAgIHZhciB2YWx1ZSA9IHRoaXMudmFsdWU7XG4gICAgICBub2RlID0gdGhpcy5wYXJzZUxpdGVyYWwodmFsdWUudmFsdWUpO1xuICAgICAgbm9kZS5yZWdleCA9IHsgcGF0dGVybjogdmFsdWUucGF0dGVybiwgZmxhZ3M6IHZhbHVlLmZsYWdzIH07XG4gICAgICByZXR1cm4gbm9kZTtcblxuICAgIGNhc2UgX3Rva2VudHlwZS50eXBlcy5udW06Y2FzZSBfdG9rZW50eXBlLnR5cGVzLnN0cmluZzpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlTGl0ZXJhbCh0aGlzLnZhbHVlKTtcblxuICAgIGNhc2UgX3Rva2VudHlwZS50eXBlcy5fbnVsbDpjYXNlIF90b2tlbnR5cGUudHlwZXMuX3RydWU6Y2FzZSBfdG9rZW50eXBlLnR5cGVzLl9mYWxzZTpcbiAgICAgIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICAgICAgbm9kZS52YWx1ZSA9IHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5fbnVsbCA/IG51bGwgOiB0aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuX3RydWU7XG4gICAgICBub2RlLnJhdyA9IHRoaXMudHlwZS5rZXl3b3JkO1xuICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiTGl0ZXJhbFwiKTtcblxuICAgIGNhc2UgX3Rva2VudHlwZS50eXBlcy5wYXJlbkw6XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZVBhcmVuQW5kRGlzdGluZ3Vpc2hFeHByZXNzaW9uKGNhbkJlQXJyb3cpO1xuXG4gICAgY2FzZSBfdG9rZW50eXBlLnR5cGVzLmJyYWNrZXRMOlxuICAgICAgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gICAgICB0aGlzLm5leHQoKTtcbiAgICAgIC8vIGNoZWNrIHdoZXRoZXIgdGhpcyBpcyBhcnJheSBjb21wcmVoZW5zaW9uIG9yIHJlZ3VsYXIgYXJyYXlcbiAgICAgIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNyAmJiB0aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuX2Zvcikge1xuICAgICAgICByZXR1cm4gdGhpcy5wYXJzZUNvbXByZWhlbnNpb24obm9kZSwgZmFsc2UpO1xuICAgICAgfVxuICAgICAgbm9kZS5lbGVtZW50cyA9IHRoaXMucGFyc2VFeHByTGlzdChfdG9rZW50eXBlLnR5cGVzLmJyYWNrZXRSLCB0cnVlLCB0cnVlLCByZWZTaG9ydGhhbmREZWZhdWx0UG9zKTtcbiAgICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJBcnJheUV4cHJlc3Npb25cIik7XG5cbiAgICBjYXNlIF90b2tlbnR5cGUudHlwZXMuYnJhY2VMOlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VPYmooZmFsc2UsIHJlZlNob3J0aGFuZERlZmF1bHRQb3MpO1xuXG4gICAgY2FzZSBfdG9rZW50eXBlLnR5cGVzLl9mdW5jdGlvbjpcbiAgICAgIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZUZ1bmN0aW9uKG5vZGUsIGZhbHNlKTtcblxuICAgIGNhc2UgX3Rva2VudHlwZS50eXBlcy5fY2xhc3M6XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZUNsYXNzKHRoaXMuc3RhcnROb2RlKCksIGZhbHNlKTtcblxuICAgIGNhc2UgX3Rva2VudHlwZS50eXBlcy5fbmV3OlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VOZXcoKTtcblxuICAgIGNhc2UgX3Rva2VudHlwZS50eXBlcy5iYWNrUXVvdGU6XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZVRlbXBsYXRlKCk7XG5cbiAgICBkZWZhdWx0OlxuICAgICAgdGhpcy51bmV4cGVjdGVkKCk7XG4gIH1cbn07XG5cbnBwLnBhcnNlTGl0ZXJhbCA9IGZ1bmN0aW9uICh2YWx1ZSkge1xuICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gIG5vZGUudmFsdWUgPSB2YWx1ZTtcbiAgbm9kZS5yYXcgPSB0aGlzLmlucHV0LnNsaWNlKHRoaXMuc3RhcnQsIHRoaXMuZW5kKTtcbiAgdGhpcy5uZXh0KCk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJMaXRlcmFsXCIpO1xufTtcblxucHAucGFyc2VQYXJlbkV4cHJlc3Npb24gPSBmdW5jdGlvbiAoKSB7XG4gIHRoaXMuZXhwZWN0KF90b2tlbnR5cGUudHlwZXMucGFyZW5MKTtcbiAgdmFyIHZhbCA9IHRoaXMucGFyc2VFeHByZXNzaW9uKCk7XG4gIHRoaXMuZXhwZWN0KF90b2tlbnR5cGUudHlwZXMucGFyZW5SKTtcbiAgcmV0dXJuIHZhbDtcbn07XG5cbnBwLnBhcnNlUGFyZW5BbmREaXN0aW5ndWlzaEV4cHJlc3Npb24gPSBmdW5jdGlvbiAoY2FuQmVBcnJvdykge1xuICB2YXIgc3RhcnRQb3MgPSB0aGlzLnN0YXJ0LFxuICAgICAgc3RhcnRMb2MgPSB0aGlzLnN0YXJ0TG9jLFxuICAgICAgdmFsID0gdW5kZWZpbmVkO1xuICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYpIHtcbiAgICB0aGlzLm5leHQoKTtcblxuICAgIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNyAmJiB0aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuX2Zvcikge1xuICAgICAgcmV0dXJuIHRoaXMucGFyc2VDb21wcmVoZW5zaW9uKHRoaXMuc3RhcnROb2RlQXQoc3RhcnRQb3MsIHN0YXJ0TG9jKSwgdHJ1ZSk7XG4gICAgfVxuXG4gICAgdmFyIGlubmVyU3RhcnRQb3MgPSB0aGlzLnN0YXJ0LFxuICAgICAgICBpbm5lclN0YXJ0TG9jID0gdGhpcy5zdGFydExvYztcbiAgICB2YXIgZXhwckxpc3QgPSBbXSxcbiAgICAgICAgZmlyc3QgPSB0cnVlO1xuICAgIHZhciByZWZTaG9ydGhhbmREZWZhdWx0UG9zID0geyBzdGFydDogMCB9LFxuICAgICAgICBzcHJlYWRTdGFydCA9IHVuZGVmaW5lZCxcbiAgICAgICAgaW5uZXJQYXJlblN0YXJ0ID0gdW5kZWZpbmVkO1xuICAgIHdoaWxlICh0aGlzLnR5cGUgIT09IF90b2tlbnR5cGUudHlwZXMucGFyZW5SKSB7XG4gICAgICBmaXJzdCA/IGZpcnN0ID0gZmFsc2UgOiB0aGlzLmV4cGVjdChfdG9rZW50eXBlLnR5cGVzLmNvbW1hKTtcbiAgICAgIGlmICh0aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuZWxsaXBzaXMpIHtcbiAgICAgICAgc3ByZWFkU3RhcnQgPSB0aGlzLnN0YXJ0O1xuICAgICAgICBleHByTGlzdC5wdXNoKHRoaXMucGFyc2VQYXJlbkl0ZW0odGhpcy5wYXJzZVJlc3QoKSkpO1xuICAgICAgICBicmVhaztcbiAgICAgIH0gZWxzZSB7XG4gICAgICAgIGlmICh0aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMucGFyZW5MICYmICFpbm5lclBhcmVuU3RhcnQpIHtcbiAgICAgICAgICBpbm5lclBhcmVuU3RhcnQgPSB0aGlzLnN0YXJ0O1xuICAgICAgICB9XG4gICAgICAgIGV4cHJMaXN0LnB1c2godGhpcy5wYXJzZU1heWJlQXNzaWduKGZhbHNlLCByZWZTaG9ydGhhbmREZWZhdWx0UG9zLCB0aGlzLnBhcnNlUGFyZW5JdGVtKSk7XG4gICAgICB9XG4gICAgfVxuICAgIHZhciBpbm5lckVuZFBvcyA9IHRoaXMuc3RhcnQsXG4gICAgICAgIGlubmVyRW5kTG9jID0gdGhpcy5zdGFydExvYztcbiAgICB0aGlzLmV4cGVjdChfdG9rZW50eXBlLnR5cGVzLnBhcmVuUik7XG5cbiAgICBpZiAoY2FuQmVBcnJvdyAmJiAhdGhpcy5jYW5JbnNlcnRTZW1pY29sb24oKSAmJiB0aGlzLmVhdChfdG9rZW50eXBlLnR5cGVzLmFycm93KSkge1xuICAgICAgaWYgKGlubmVyUGFyZW5TdGFydCkgdGhpcy51bmV4cGVjdGVkKGlubmVyUGFyZW5TdGFydCk7XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZVBhcmVuQXJyb3dMaXN0KHN0YXJ0UG9zLCBzdGFydExvYywgZXhwckxpc3QpO1xuICAgIH1cblxuICAgIGlmICghZXhwckxpc3QubGVuZ3RoKSB0aGlzLnVuZXhwZWN0ZWQodGhpcy5sYXN0VG9rU3RhcnQpO1xuICAgIGlmIChzcHJlYWRTdGFydCkgdGhpcy51bmV4cGVjdGVkKHNwcmVhZFN0YXJ0KTtcbiAgICBpZiAocmVmU2hvcnRoYW5kRGVmYXVsdFBvcy5zdGFydCkgdGhpcy51bmV4cGVjdGVkKHJlZlNob3J0aGFuZERlZmF1bHRQb3Muc3RhcnQpO1xuXG4gICAgaWYgKGV4cHJMaXN0Lmxlbmd0aCA+IDEpIHtcbiAgICAgIHZhbCA9IHRoaXMuc3RhcnROb2RlQXQoaW5uZXJTdGFydFBvcywgaW5uZXJTdGFydExvYyk7XG4gICAgICB2YWwuZXhwcmVzc2lvbnMgPSBleHByTGlzdDtcbiAgICAgIHRoaXMuZmluaXNoTm9kZUF0KHZhbCwgXCJTZXF1ZW5jZUV4cHJlc3Npb25cIiwgaW5uZXJFbmRQb3MsIGlubmVyRW5kTG9jKTtcbiAgICB9IGVsc2Uge1xuICAgICAgdmFsID0gZXhwckxpc3RbMF07XG4gICAgfVxuICB9IGVsc2Uge1xuICAgIHZhbCA9IHRoaXMucGFyc2VQYXJlbkV4cHJlc3Npb24oKTtcbiAgfVxuXG4gIGlmICh0aGlzLm9wdGlvbnMucHJlc2VydmVQYXJlbnMpIHtcbiAgICB2YXIgcGFyID0gdGhpcy5zdGFydE5vZGVBdChzdGFydFBvcywgc3RhcnRMb2MpO1xuICAgIHBhci5leHByZXNzaW9uID0gdmFsO1xuICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUocGFyLCBcIlBhcmVudGhlc2l6ZWRFeHByZXNzaW9uXCIpO1xuICB9IGVsc2Uge1xuICAgIHJldHVybiB2YWw7XG4gIH1cbn07XG5cbnBwLnBhcnNlUGFyZW5JdGVtID0gZnVuY3Rpb24gKGl0ZW0pIHtcbiAgcmV0dXJuIGl0ZW07XG59O1xuXG5wcC5wYXJzZVBhcmVuQXJyb3dMaXN0ID0gZnVuY3Rpb24gKHN0YXJ0UG9zLCBzdGFydExvYywgZXhwckxpc3QpIHtcbiAgcmV0dXJuIHRoaXMucGFyc2VBcnJvd0V4cHJlc3Npb24odGhpcy5zdGFydE5vZGVBdChzdGFydFBvcywgc3RhcnRMb2MpLCBleHByTGlzdCk7XG59O1xuXG4vLyBOZXcncyBwcmVjZWRlbmNlIGlzIHNsaWdodGx5IHRyaWNreS4gSXQgbXVzdCBhbGxvdyBpdHMgYXJndW1lbnRcbi8vIHRvIGJlIGEgYFtdYCBvciBkb3Qgc3Vic2NyaXB0IGV4cHJlc3Npb24sIGJ1dCBub3QgYSBjYWxsIOKAlCBhdFxuLy8gbGVhc3QsIG5vdCB3aXRob3V0IHdyYXBwaW5nIGl0IGluIHBhcmVudGhlc2VzLiBUaHVzLCBpdCB1c2VzIHRoZVxuXG52YXIgZW1wdHkgPSBbXTtcblxucHAucGFyc2VOZXcgPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgdmFyIG1ldGEgPSB0aGlzLnBhcnNlSWRlbnQodHJ1ZSk7XG4gIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNiAmJiB0aGlzLmVhdChfdG9rZW50eXBlLnR5cGVzLmRvdCkpIHtcbiAgICBub2RlLm1ldGEgPSBtZXRhO1xuICAgIG5vZGUucHJvcGVydHkgPSB0aGlzLnBhcnNlSWRlbnQodHJ1ZSk7XG4gICAgaWYgKG5vZGUucHJvcGVydHkubmFtZSAhPT0gXCJ0YXJnZXRcIikgdGhpcy5yYWlzZShub2RlLnByb3BlcnR5LnN0YXJ0LCBcIlRoZSBvbmx5IHZhbGlkIG1ldGEgcHJvcGVydHkgZm9yIG5ldyBpcyBuZXcudGFyZ2V0XCIpO1xuICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJNZXRhUHJvcGVydHlcIik7XG4gIH1cbiAgdmFyIHN0YXJ0UG9zID0gdGhpcy5zdGFydCxcbiAgICAgIHN0YXJ0TG9jID0gdGhpcy5zdGFydExvYztcbiAgbm9kZS5jYWxsZWUgPSB0aGlzLnBhcnNlU3Vic2NyaXB0cyh0aGlzLnBhcnNlRXhwckF0b20oKSwgc3RhcnRQb3MsIHN0YXJ0TG9jLCB0cnVlKTtcbiAgaWYgKHRoaXMuZWF0KF90b2tlbnR5cGUudHlwZXMucGFyZW5MKSkgbm9kZS5hcmd1bWVudHMgPSB0aGlzLnBhcnNlRXhwckxpc3QoX3Rva2VudHlwZS50eXBlcy5wYXJlblIsIGZhbHNlKTtlbHNlIG5vZGUuYXJndW1lbnRzID0gZW1wdHk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJOZXdFeHByZXNzaW9uXCIpO1xufTtcblxuLy8gUGFyc2UgdGVtcGxhdGUgZXhwcmVzc2lvbi5cblxucHAucGFyc2VUZW1wbGF0ZUVsZW1lbnQgPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBlbGVtID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgZWxlbS52YWx1ZSA9IHtcbiAgICByYXc6IHRoaXMuaW5wdXQuc2xpY2UodGhpcy5zdGFydCwgdGhpcy5lbmQpLnJlcGxhY2UoL1xcclxcbj8vZywgXCJcXG5cIiksXG4gICAgY29va2VkOiB0aGlzLnZhbHVlXG4gIH07XG4gIHRoaXMubmV4dCgpO1xuICBlbGVtLnRhaWwgPSB0aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuYmFja1F1b3RlO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKGVsZW0sIFwiVGVtcGxhdGVFbGVtZW50XCIpO1xufTtcblxucHAucGFyc2VUZW1wbGF0ZSA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICB0aGlzLm5leHQoKTtcbiAgbm9kZS5leHByZXNzaW9ucyA9IFtdO1xuICB2YXIgY3VyRWx0ID0gdGhpcy5wYXJzZVRlbXBsYXRlRWxlbWVudCgpO1xuICBub2RlLnF1YXNpcyA9IFtjdXJFbHRdO1xuICB3aGlsZSAoIWN1ckVsdC50YWlsKSB7XG4gICAgdGhpcy5leHBlY3QoX3Rva2VudHlwZS50eXBlcy5kb2xsYXJCcmFjZUwpO1xuICAgIG5vZGUuZXhwcmVzc2lvbnMucHVzaCh0aGlzLnBhcnNlRXhwcmVzc2lvbigpKTtcbiAgICB0aGlzLmV4cGVjdChfdG9rZW50eXBlLnR5cGVzLmJyYWNlUik7XG4gICAgbm9kZS5xdWFzaXMucHVzaChjdXJFbHQgPSB0aGlzLnBhcnNlVGVtcGxhdGVFbGVtZW50KCkpO1xuICB9XG4gIHRoaXMubmV4dCgpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiVGVtcGxhdGVMaXRlcmFsXCIpO1xufTtcblxuLy8gUGFyc2UgYW4gb2JqZWN0IGxpdGVyYWwgb3IgYmluZGluZyBwYXR0ZXJuLlxuXG5wcC5wYXJzZU9iaiA9IGZ1bmN0aW9uIChpc1BhdHRlcm4sIHJlZlNob3J0aGFuZERlZmF1bHRQb3MpIHtcbiAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpLFxuICAgICAgZmlyc3QgPSB0cnVlLFxuICAgICAgcHJvcEhhc2ggPSB7fTtcbiAgbm9kZS5wcm9wZXJ0aWVzID0gW107XG4gIHRoaXMubmV4dCgpO1xuICB3aGlsZSAoIXRoaXMuZWF0KF90b2tlbnR5cGUudHlwZXMuYnJhY2VSKSkge1xuICAgIGlmICghZmlyc3QpIHtcbiAgICAgIHRoaXMuZXhwZWN0KF90b2tlbnR5cGUudHlwZXMuY29tbWEpO1xuICAgICAgaWYgKHRoaXMuYWZ0ZXJUcmFpbGluZ0NvbW1hKF90b2tlbnR5cGUudHlwZXMuYnJhY2VSKSkgYnJlYWs7XG4gICAgfSBlbHNlIGZpcnN0ID0gZmFsc2U7XG5cbiAgICB2YXIgcHJvcCA9IHRoaXMuc3RhcnROb2RlKCksXG4gICAgICAgIGlzR2VuZXJhdG9yID0gdW5kZWZpbmVkLFxuICAgICAgICBzdGFydFBvcyA9IHVuZGVmaW5lZCxcbiAgICAgICAgc3RhcnRMb2MgPSB1bmRlZmluZWQ7XG4gICAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KSB7XG4gICAgICBwcm9wLm1ldGhvZCA9IGZhbHNlO1xuICAgICAgcHJvcC5zaG9ydGhhbmQgPSBmYWxzZTtcbiAgICAgIGlmIChpc1BhdHRlcm4gfHwgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcykge1xuICAgICAgICBzdGFydFBvcyA9IHRoaXMuc3RhcnQ7XG4gICAgICAgIHN0YXJ0TG9jID0gdGhpcy5zdGFydExvYztcbiAgICAgIH1cbiAgICAgIGlmICghaXNQYXR0ZXJuKSBpc0dlbmVyYXRvciA9IHRoaXMuZWF0KF90b2tlbnR5cGUudHlwZXMuc3Rhcik7XG4gICAgfVxuICAgIHRoaXMucGFyc2VQcm9wZXJ0eU5hbWUocHJvcCk7XG4gICAgdGhpcy5wYXJzZVByb3BlcnR5VmFsdWUocHJvcCwgaXNQYXR0ZXJuLCBpc0dlbmVyYXRvciwgc3RhcnRQb3MsIHN0YXJ0TG9jLCByZWZTaG9ydGhhbmREZWZhdWx0UG9zKTtcbiAgICB0aGlzLmNoZWNrUHJvcENsYXNoKHByb3AsIHByb3BIYXNoKTtcbiAgICBub2RlLnByb3BlcnRpZXMucHVzaCh0aGlzLmZpbmlzaE5vZGUocHJvcCwgXCJQcm9wZXJ0eVwiKSk7XG4gIH1cbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBpc1BhdHRlcm4gPyBcIk9iamVjdFBhdHRlcm5cIiA6IFwiT2JqZWN0RXhwcmVzc2lvblwiKTtcbn07XG5cbnBwLnBhcnNlUHJvcGVydHlWYWx1ZSA9IGZ1bmN0aW9uIChwcm9wLCBpc1BhdHRlcm4sIGlzR2VuZXJhdG9yLCBzdGFydFBvcywgc3RhcnRMb2MsIHJlZlNob3J0aGFuZERlZmF1bHRQb3MpIHtcbiAgaWYgKHRoaXMuZWF0KF90b2tlbnR5cGUudHlwZXMuY29sb24pKSB7XG4gICAgcHJvcC52YWx1ZSA9IGlzUGF0dGVybiA/IHRoaXMucGFyc2VNYXliZURlZmF1bHQodGhpcy5zdGFydCwgdGhpcy5zdGFydExvYykgOiB0aGlzLnBhcnNlTWF5YmVBc3NpZ24oZmFsc2UsIHJlZlNob3J0aGFuZERlZmF1bHRQb3MpO1xuICAgIHByb3Aua2luZCA9IFwiaW5pdFwiO1xuICB9IGVsc2UgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2ICYmIHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5wYXJlbkwpIHtcbiAgICBpZiAoaXNQYXR0ZXJuKSB0aGlzLnVuZXhwZWN0ZWQoKTtcbiAgICBwcm9wLmtpbmQgPSBcImluaXRcIjtcbiAgICBwcm9wLm1ldGhvZCA9IHRydWU7XG4gICAgcHJvcC52YWx1ZSA9IHRoaXMucGFyc2VNZXRob2QoaXNHZW5lcmF0b3IpO1xuICB9IGVsc2UgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA1ICYmICFwcm9wLmNvbXB1dGVkICYmIHByb3Aua2V5LnR5cGUgPT09IFwiSWRlbnRpZmllclwiICYmIChwcm9wLmtleS5uYW1lID09PSBcImdldFwiIHx8IHByb3Aua2V5Lm5hbWUgPT09IFwic2V0XCIpICYmICh0aGlzLnR5cGUgIT0gX3Rva2VudHlwZS50eXBlcy5jb21tYSAmJiB0aGlzLnR5cGUgIT0gX3Rva2VudHlwZS50eXBlcy5icmFjZVIpKSB7XG4gICAgaWYgKGlzR2VuZXJhdG9yIHx8IGlzUGF0dGVybikgdGhpcy51bmV4cGVjdGVkKCk7XG4gICAgcHJvcC5raW5kID0gcHJvcC5rZXkubmFtZTtcbiAgICB0aGlzLnBhcnNlUHJvcGVydHlOYW1lKHByb3ApO1xuICAgIHByb3AudmFsdWUgPSB0aGlzLnBhcnNlTWV0aG9kKGZhbHNlKTtcbiAgICB2YXIgcGFyYW1Db3VudCA9IHByb3Aua2luZCA9PT0gXCJnZXRcIiA/IDAgOiAxO1xuICAgIGlmIChwcm9wLnZhbHVlLnBhcmFtcy5sZW5ndGggIT09IHBhcmFtQ291bnQpIHtcbiAgICAgIHZhciBzdGFydCA9IHByb3AudmFsdWUuc3RhcnQ7XG4gICAgICBpZiAocHJvcC5raW5kID09PSBcImdldFwiKSB0aGlzLnJhaXNlKHN0YXJ0LCBcImdldHRlciBzaG91bGQgaGF2ZSBubyBwYXJhbXNcIik7ZWxzZSB0aGlzLnJhaXNlKHN0YXJ0LCBcInNldHRlciBzaG91bGQgaGF2ZSBleGFjdGx5IG9uZSBwYXJhbVwiKTtcbiAgICB9XG4gIH0gZWxzZSBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYgJiYgIXByb3AuY29tcHV0ZWQgJiYgcHJvcC5rZXkudHlwZSA9PT0gXCJJZGVudGlmaWVyXCIpIHtcbiAgICBwcm9wLmtpbmQgPSBcImluaXRcIjtcbiAgICBpZiAoaXNQYXR0ZXJuKSB7XG4gICAgICBpZiAodGhpcy5pc0tleXdvcmQocHJvcC5rZXkubmFtZSkgfHwgdGhpcy5zdHJpY3QgJiYgKF9pZGVudGlmaWVyLnJlc2VydmVkV29yZHMuc3RyaWN0QmluZChwcm9wLmtleS5uYW1lKSB8fCBfaWRlbnRpZmllci5yZXNlcnZlZFdvcmRzLnN0cmljdChwcm9wLmtleS5uYW1lKSkgfHwgIXRoaXMub3B0aW9ucy5hbGxvd1Jlc2VydmVkICYmIHRoaXMuaXNSZXNlcnZlZFdvcmQocHJvcC5rZXkubmFtZSkpIHRoaXMucmFpc2UocHJvcC5rZXkuc3RhcnQsIFwiQmluZGluZyBcIiArIHByb3Aua2V5Lm5hbWUpO1xuICAgICAgcHJvcC52YWx1ZSA9IHRoaXMucGFyc2VNYXliZURlZmF1bHQoc3RhcnRQb3MsIHN0YXJ0TG9jLCBwcm9wLmtleSk7XG4gICAgfSBlbHNlIGlmICh0aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuZXEgJiYgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcykge1xuICAgICAgaWYgKCFyZWZTaG9ydGhhbmREZWZhdWx0UG9zLnN0YXJ0KSByZWZTaG9ydGhhbmREZWZhdWx0UG9zLnN0YXJ0ID0gdGhpcy5zdGFydDtcbiAgICAgIHByb3AudmFsdWUgPSB0aGlzLnBhcnNlTWF5YmVEZWZhdWx0KHN0YXJ0UG9zLCBzdGFydExvYywgcHJvcC5rZXkpO1xuICAgIH0gZWxzZSB7XG4gICAgICBwcm9wLnZhbHVlID0gcHJvcC5rZXk7XG4gICAgfVxuICAgIHByb3Auc2hvcnRoYW5kID0gdHJ1ZTtcbiAgfSBlbHNlIHRoaXMudW5leHBlY3RlZCgpO1xufTtcblxucHAucGFyc2VQcm9wZXJ0eU5hbWUgPSBmdW5jdGlvbiAocHJvcCkge1xuICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYpIHtcbiAgICBpZiAodGhpcy5lYXQoX3Rva2VudHlwZS50eXBlcy5icmFja2V0TCkpIHtcbiAgICAgIHByb3AuY29tcHV0ZWQgPSB0cnVlO1xuICAgICAgcHJvcC5rZXkgPSB0aGlzLnBhcnNlTWF5YmVBc3NpZ24oKTtcbiAgICAgIHRoaXMuZXhwZWN0KF90b2tlbnR5cGUudHlwZXMuYnJhY2tldFIpO1xuICAgICAgcmV0dXJuIHByb3Aua2V5O1xuICAgIH0gZWxzZSB7XG4gICAgICBwcm9wLmNvbXB1dGVkID0gZmFsc2U7XG4gICAgfVxuICB9XG4gIHJldHVybiBwcm9wLmtleSA9IHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5udW0gfHwgdGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLnN0cmluZyA/IHRoaXMucGFyc2VFeHByQXRvbSgpIDogdGhpcy5wYXJzZUlkZW50KHRydWUpO1xufTtcblxuLy8gSW5pdGlhbGl6ZSBlbXB0eSBmdW5jdGlvbiBub2RlLlxuXG5wcC5pbml0RnVuY3Rpb24gPSBmdW5jdGlvbiAobm9kZSkge1xuICBub2RlLmlkID0gbnVsbDtcbiAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KSB7XG4gICAgbm9kZS5nZW5lcmF0b3IgPSBmYWxzZTtcbiAgICBub2RlLmV4cHJlc3Npb24gPSBmYWxzZTtcbiAgfVxufTtcblxuLy8gUGFyc2Ugb2JqZWN0IG9yIGNsYXNzIG1ldGhvZC5cblxucHAucGFyc2VNZXRob2QgPSBmdW5jdGlvbiAoaXNHZW5lcmF0b3IpIHtcbiAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICB0aGlzLmluaXRGdW5jdGlvbihub2RlKTtcbiAgdGhpcy5leHBlY3QoX3Rva2VudHlwZS50eXBlcy5wYXJlbkwpO1xuICBub2RlLnBhcmFtcyA9IHRoaXMucGFyc2VCaW5kaW5nTGlzdChfdG9rZW50eXBlLnR5cGVzLnBhcmVuUiwgZmFsc2UsIGZhbHNlKTtcbiAgdmFyIGFsbG93RXhwcmVzc2lvbkJvZHkgPSB1bmRlZmluZWQ7XG4gIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNikge1xuICAgIG5vZGUuZ2VuZXJhdG9yID0gaXNHZW5lcmF0b3I7XG4gIH1cbiAgdGhpcy5wYXJzZUZ1bmN0aW9uQm9keShub2RlLCBmYWxzZSk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJGdW5jdGlvbkV4cHJlc3Npb25cIik7XG59O1xuXG4vLyBQYXJzZSBhcnJvdyBmdW5jdGlvbiBleHByZXNzaW9uIHdpdGggZ2l2ZW4gcGFyYW1ldGVycy5cblxucHAucGFyc2VBcnJvd0V4cHJlc3Npb24gPSBmdW5jdGlvbiAobm9kZSwgcGFyYW1zKSB7XG4gIHRoaXMuaW5pdEZ1bmN0aW9uKG5vZGUpO1xuICBub2RlLnBhcmFtcyA9IHRoaXMudG9Bc3NpZ25hYmxlTGlzdChwYXJhbXMsIHRydWUpO1xuICB0aGlzLnBhcnNlRnVuY3Rpb25Cb2R5KG5vZGUsIHRydWUpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiQXJyb3dGdW5jdGlvbkV4cHJlc3Npb25cIik7XG59O1xuXG4vLyBQYXJzZSBmdW5jdGlvbiBib2R5IGFuZCBjaGVjayBwYXJhbWV0ZXJzLlxuXG5wcC5wYXJzZUZ1bmN0aW9uQm9keSA9IGZ1bmN0aW9uIChub2RlLCBhbGxvd0V4cHJlc3Npb24pIHtcbiAgdmFyIGlzRXhwcmVzc2lvbiA9IGFsbG93RXhwcmVzc2lvbiAmJiB0aGlzLnR5cGUgIT09IF90b2tlbnR5cGUudHlwZXMuYnJhY2VMO1xuXG4gIGlmIChpc0V4cHJlc3Npb24pIHtcbiAgICBub2RlLmJvZHkgPSB0aGlzLnBhcnNlTWF5YmVBc3NpZ24oKTtcbiAgICBub2RlLmV4cHJlc3Npb24gPSB0cnVlO1xuICB9IGVsc2Uge1xuICAgIC8vIFN0YXJ0IGEgbmV3IHNjb3BlIHdpdGggcmVnYXJkIHRvIGxhYmVscyBhbmQgdGhlIGBpbkZ1bmN0aW9uYFxuICAgIC8vIGZsYWcgKHJlc3RvcmUgdGhlbSB0byB0aGVpciBvbGQgdmFsdWUgYWZ0ZXJ3YXJkcykuXG4gICAgdmFyIG9sZEluRnVuYyA9IHRoaXMuaW5GdW5jdGlvbixcbiAgICAgICAgb2xkSW5HZW4gPSB0aGlzLmluR2VuZXJhdG9yLFxuICAgICAgICBvbGRMYWJlbHMgPSB0aGlzLmxhYmVscztcbiAgICB0aGlzLmluRnVuY3Rpb24gPSB0cnVlO3RoaXMuaW5HZW5lcmF0b3IgPSBub2RlLmdlbmVyYXRvcjt0aGlzLmxhYmVscyA9IFtdO1xuICAgIG5vZGUuYm9keSA9IHRoaXMucGFyc2VCbG9jayh0cnVlKTtcbiAgICBub2RlLmV4cHJlc3Npb24gPSBmYWxzZTtcbiAgICB0aGlzLmluRnVuY3Rpb24gPSBvbGRJbkZ1bmM7dGhpcy5pbkdlbmVyYXRvciA9IG9sZEluR2VuO3RoaXMubGFiZWxzID0gb2xkTGFiZWxzO1xuICB9XG5cbiAgLy8gSWYgdGhpcyBpcyBhIHN0cmljdCBtb2RlIGZ1bmN0aW9uLCB2ZXJpZnkgdGhhdCBhcmd1bWVudCBuYW1lc1xuICAvLyBhcmUgbm90IHJlcGVhdGVkLCBhbmQgaXQgZG9lcyBub3QgdHJ5IHRvIGJpbmQgdGhlIHdvcmRzIGBldmFsYFxuICAvLyBvciBgYXJndW1lbnRzYC5cbiAgaWYgKHRoaXMuc3RyaWN0IHx8ICFpc0V4cHJlc3Npb24gJiYgbm9kZS5ib2R5LmJvZHkubGVuZ3RoICYmIHRoaXMuaXNVc2VTdHJpY3Qobm9kZS5ib2R5LmJvZHlbMF0pKSB7XG4gICAgdmFyIG5hbWVIYXNoID0ge30sXG4gICAgICAgIG9sZFN0cmljdCA9IHRoaXMuc3RyaWN0O1xuICAgIHRoaXMuc3RyaWN0ID0gdHJ1ZTtcbiAgICBpZiAobm9kZS5pZCkgdGhpcy5jaGVja0xWYWwobm9kZS5pZCwgdHJ1ZSk7XG4gICAgZm9yICh2YXIgaSA9IDA7IGkgPCBub2RlLnBhcmFtcy5sZW5ndGg7IGkrKykge1xuICAgICAgdGhpcy5jaGVja0xWYWwobm9kZS5wYXJhbXNbaV0sIHRydWUsIG5hbWVIYXNoKTtcbiAgICB9dGhpcy5zdHJpY3QgPSBvbGRTdHJpY3Q7XG4gIH1cbn07XG5cbi8vIFBhcnNlcyBhIGNvbW1hLXNlcGFyYXRlZCBsaXN0IG9mIGV4cHJlc3Npb25zLCBhbmQgcmV0dXJucyB0aGVtIGFzXG4vLyBhbiBhcnJheS4gYGNsb3NlYCBpcyB0aGUgdG9rZW4gdHlwZSB0aGF0IGVuZHMgdGhlIGxpc3QsIGFuZFxuLy8gYGFsbG93RW1wdHlgIGNhbiBiZSB0dXJuZWQgb24gdG8gYWxsb3cgc3Vic2VxdWVudCBjb21tYXMgd2l0aFxuLy8gbm90aGluZyBpbiBiZXR3ZWVuIHRoZW0gdG8gYmUgcGFyc2VkIGFzIGBudWxsYCAod2hpY2ggaXMgbmVlZGVkXG4vLyBmb3IgYXJyYXkgbGl0ZXJhbHMpLlxuXG5wcC5wYXJzZUV4cHJMaXN0ID0gZnVuY3Rpb24gKGNsb3NlLCBhbGxvd1RyYWlsaW5nQ29tbWEsIGFsbG93RW1wdHksIHJlZlNob3J0aGFuZERlZmF1bHRQb3MpIHtcbiAgdmFyIGVsdHMgPSBbXSxcbiAgICAgIGZpcnN0ID0gdHJ1ZTtcbiAgd2hpbGUgKCF0aGlzLmVhdChjbG9zZSkpIHtcbiAgICBpZiAoIWZpcnN0KSB7XG4gICAgICB0aGlzLmV4cGVjdChfdG9rZW50eXBlLnR5cGVzLmNvbW1hKTtcbiAgICAgIGlmIChhbGxvd1RyYWlsaW5nQ29tbWEgJiYgdGhpcy5hZnRlclRyYWlsaW5nQ29tbWEoY2xvc2UpKSBicmVhaztcbiAgICB9IGVsc2UgZmlyc3QgPSBmYWxzZTtcblxuICAgIHZhciBlbHQgPSB1bmRlZmluZWQ7XG4gICAgaWYgKGFsbG93RW1wdHkgJiYgdGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLmNvbW1hKSBlbHQgPSBudWxsO2Vsc2UgaWYgKHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5lbGxpcHNpcykgZWx0ID0gdGhpcy5wYXJzZVNwcmVhZChyZWZTaG9ydGhhbmREZWZhdWx0UG9zKTtlbHNlIGVsdCA9IHRoaXMucGFyc2VNYXliZUFzc2lnbihmYWxzZSwgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcyk7XG4gICAgZWx0cy5wdXNoKGVsdCk7XG4gIH1cbiAgcmV0dXJuIGVsdHM7XG59O1xuXG4vLyBQYXJzZSB0aGUgbmV4dCB0b2tlbiBhcyBhbiBpZGVudGlmaWVyLiBJZiBgbGliZXJhbGAgaXMgdHJ1ZSAodXNlZFxuLy8gd2hlbiBwYXJzaW5nIHByb3BlcnRpZXMpLCBpdCB3aWxsIGFsc28gY29udmVydCBrZXl3b3JkcyBpbnRvXG4vLyBpZGVudGlmaWVycy5cblxucHAucGFyc2VJZGVudCA9IGZ1bmN0aW9uIChsaWJlcmFsKSB7XG4gIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgaWYgKGxpYmVyYWwgJiYgdGhpcy5vcHRpb25zLmFsbG93UmVzZXJ2ZWQgPT0gXCJuZXZlclwiKSBsaWJlcmFsID0gZmFsc2U7XG4gIGlmICh0aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMubmFtZSkge1xuICAgIGlmICghbGliZXJhbCAmJiAoIXRoaXMub3B0aW9ucy5hbGxvd1Jlc2VydmVkICYmIHRoaXMuaXNSZXNlcnZlZFdvcmQodGhpcy52YWx1ZSkgfHwgdGhpcy5zdHJpY3QgJiYgX2lkZW50aWZpZXIucmVzZXJ2ZWRXb3Jkcy5zdHJpY3QodGhpcy52YWx1ZSkgJiYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2IHx8IHRoaXMuaW5wdXQuc2xpY2UodGhpcy5zdGFydCwgdGhpcy5lbmQpLmluZGV4T2YoXCJcXFxcXCIpID09IC0xKSkpIHRoaXMucmFpc2UodGhpcy5zdGFydCwgXCJUaGUga2V5d29yZCAnXCIgKyB0aGlzLnZhbHVlICsgXCInIGlzIHJlc2VydmVkXCIpO1xuICAgIG5vZGUubmFtZSA9IHRoaXMudmFsdWU7XG4gIH0gZWxzZSBpZiAobGliZXJhbCAmJiB0aGlzLnR5cGUua2V5d29yZCkge1xuICAgIG5vZGUubmFtZSA9IHRoaXMudHlwZS5rZXl3b3JkO1xuICB9IGVsc2Uge1xuICAgIHRoaXMudW5leHBlY3RlZCgpO1xuICB9XG4gIHRoaXMubmV4dCgpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiSWRlbnRpZmllclwiKTtcbn07XG5cbi8vIFBhcnNlcyB5aWVsZCBleHByZXNzaW9uIGluc2lkZSBnZW5lcmF0b3IuXG5cbnBwLnBhcnNlWWllbGQgPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgdGhpcy5uZXh0KCk7XG4gIGlmICh0aGlzLnR5cGUgPT0gX3Rva2VudHlwZS50eXBlcy5zZW1pIHx8IHRoaXMuY2FuSW5zZXJ0U2VtaWNvbG9uKCkgfHwgdGhpcy50eXBlICE9IF90b2tlbnR5cGUudHlwZXMuc3RhciAmJiAhdGhpcy50eXBlLnN0YXJ0c0V4cHIpIHtcbiAgICBub2RlLmRlbGVnYXRlID0gZmFsc2U7XG4gICAgbm9kZS5hcmd1bWVudCA9IG51bGw7XG4gIH0gZWxzZSB7XG4gICAgbm9kZS5kZWxlZ2F0ZSA9IHRoaXMuZWF0KF90b2tlbnR5cGUudHlwZXMuc3Rhcik7XG4gICAgbm9kZS5hcmd1bWVudCA9IHRoaXMucGFyc2VNYXliZUFzc2lnbigpO1xuICB9XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJZaWVsZEV4cHJlc3Npb25cIik7XG59O1xuXG4vLyBQYXJzZXMgYXJyYXkgYW5kIGdlbmVyYXRvciBjb21wcmVoZW5zaW9ucy5cblxucHAucGFyc2VDb21wcmVoZW5zaW9uID0gZnVuY3Rpb24gKG5vZGUsIGlzR2VuZXJhdG9yKSB7XG4gIG5vZGUuYmxvY2tzID0gW107XG4gIHdoaWxlICh0aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuX2Zvcikge1xuICAgIHZhciBibG9jayA9IHRoaXMuc3RhcnROb2RlKCk7XG4gICAgdGhpcy5uZXh0KCk7XG4gICAgdGhpcy5leHBlY3QoX3Rva2VudHlwZS50eXBlcy5wYXJlbkwpO1xuICAgIGJsb2NrLmxlZnQgPSB0aGlzLnBhcnNlQmluZGluZ0F0b20oKTtcbiAgICB0aGlzLmNoZWNrTFZhbChibG9jay5sZWZ0LCB0cnVlKTtcbiAgICB0aGlzLmV4cGVjdENvbnRleHR1YWwoXCJvZlwiKTtcbiAgICBibG9jay5yaWdodCA9IHRoaXMucGFyc2VFeHByZXNzaW9uKCk7XG4gICAgdGhpcy5leHBlY3QoX3Rva2VudHlwZS50eXBlcy5wYXJlblIpO1xuICAgIG5vZGUuYmxvY2tzLnB1c2godGhpcy5maW5pc2hOb2RlKGJsb2NrLCBcIkNvbXByZWhlbnNpb25CbG9ja1wiKSk7XG4gIH1cbiAgbm9kZS5maWx0ZXIgPSB0aGlzLmVhdChfdG9rZW50eXBlLnR5cGVzLl9pZikgPyB0aGlzLnBhcnNlUGFyZW5FeHByZXNzaW9uKCkgOiBudWxsO1xuICBub2RlLmJvZHkgPSB0aGlzLnBhcnNlRXhwcmVzc2lvbigpO1xuICB0aGlzLmV4cGVjdChpc0dlbmVyYXRvciA/IF90b2tlbnR5cGUudHlwZXMucGFyZW5SIDogX3Rva2VudHlwZS50eXBlcy5icmFja2V0Uik7XG4gIG5vZGUuZ2VuZXJhdG9yID0gaXNHZW5lcmF0b3I7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJDb21wcmVoZW5zaW9uRXhwcmVzc2lvblwiKTtcbn07XG5cbn0se1wiLi9pZGVudGlmaWVyXCI6MixcIi4vc3RhdGVcIjoxMCxcIi4vdG9rZW50eXBlXCI6MTQsXCIuL3V0aWxcIjoxNX1dLDI6W2Z1bmN0aW9uKF9kZXJlcV8sbW9kdWxlLGV4cG9ydHMpe1xuLy8gVGhpcyBpcyBhIHRyaWNrIHRha2VuIGZyb20gRXNwcmltYS4gSXQgdHVybnMgb3V0IHRoYXQsIG9uXG4vLyBub24tQ2hyb21lIGJyb3dzZXJzLCB0byBjaGVjayB3aGV0aGVyIGEgc3RyaW5nIGlzIGluIGEgc2V0LCBhXG4vLyBwcmVkaWNhdGUgY29udGFpbmluZyBhIGJpZyB1Z2x5IGBzd2l0Y2hgIHN0YXRlbWVudCBpcyBmYXN0ZXIgdGhhblxuLy8gYSByZWd1bGFyIGV4cHJlc3Npb24sIGFuZCBvbiBDaHJvbWUgdGhlIHR3byBhcmUgYWJvdXQgb24gcGFyLlxuLy8gVGhpcyBmdW5jdGlvbiB1c2VzIGBldmFsYCAobm9uLWxleGljYWwpIHRvIHByb2R1Y2Ugc3VjaCBhXG4vLyBwcmVkaWNhdGUgZnJvbSBhIHNwYWNlLXNlcGFyYXRlZCBzdHJpbmcgb2Ygd29yZHMuXG4vL1xuLy8gSXQgc3RhcnRzIGJ5IHNvcnRpbmcgdGhlIHdvcmRzIGJ5IGxlbmd0aC5cblxuXCJ1c2Ugc3RyaWN0XCI7XG5cbmV4cG9ydHMuX19lc01vZHVsZSA9IHRydWU7XG5leHBvcnRzLmlzSWRlbnRpZmllclN0YXJ0ID0gaXNJZGVudGlmaWVyU3RhcnQ7XG5leHBvcnRzLmlzSWRlbnRpZmllckNoYXIgPSBpc0lkZW50aWZpZXJDaGFyO1xuZnVuY3Rpb24gbWFrZVByZWRpY2F0ZSh3b3Jkcykge1xuICB3b3JkcyA9IHdvcmRzLnNwbGl0KFwiIFwiKTtcbiAgdmFyIGYgPSBcIlwiLFxuICAgICAgY2F0cyA9IFtdO1xuICBvdXQ6IGZvciAodmFyIGkgPSAwOyBpIDwgd29yZHMubGVuZ3RoOyArK2kpIHtcbiAgICBmb3IgKHZhciBqID0gMDsgaiA8IGNhdHMubGVuZ3RoOyArK2opIHtcbiAgICAgIGlmIChjYXRzW2pdWzBdLmxlbmd0aCA9PSB3b3Jkc1tpXS5sZW5ndGgpIHtcbiAgICAgICAgY2F0c1tqXS5wdXNoKHdvcmRzW2ldKTtcbiAgICAgICAgY29udGludWUgb3V0O1xuICAgICAgfVxuICAgIH1jYXRzLnB1c2goW3dvcmRzW2ldXSk7XG4gIH1cbiAgZnVuY3Rpb24gY29tcGFyZVRvKGFycikge1xuICAgIGlmIChhcnIubGVuZ3RoID09IDEpIHJldHVybiBmICs9IFwicmV0dXJuIHN0ciA9PT0gXCIgKyBKU09OLnN0cmluZ2lmeShhcnJbMF0pICsgXCI7XCI7XG4gICAgZiArPSBcInN3aXRjaChzdHIpe1wiO1xuICAgIGZvciAodmFyIGkgPSAwOyBpIDwgYXJyLmxlbmd0aDsgKytpKSB7XG4gICAgICBmICs9IFwiY2FzZSBcIiArIEpTT04uc3RyaW5naWZ5KGFycltpXSkgKyBcIjpcIjtcbiAgICB9ZiArPSBcInJldHVybiB0cnVlfXJldHVybiBmYWxzZTtcIjtcbiAgfVxuXG4gIC8vIFdoZW4gdGhlcmUgYXJlIG1vcmUgdGhhbiB0aHJlZSBsZW5ndGggY2F0ZWdvcmllcywgYW4gb3V0ZXJcbiAgLy8gc3dpdGNoIGZpcnN0IGRpc3BhdGNoZXMgb24gdGhlIGxlbmd0aHMsIHRvIHNhdmUgb24gY29tcGFyaXNvbnMuXG5cbiAgaWYgKGNhdHMubGVuZ3RoID4gMykge1xuICAgIGNhdHMuc29ydChmdW5jdGlvbiAoYSwgYikge1xuICAgICAgcmV0dXJuIGIubGVuZ3RoIC0gYS5sZW5ndGg7XG4gICAgfSk7XG4gICAgZiArPSBcInN3aXRjaChzdHIubGVuZ3RoKXtcIjtcbiAgICBmb3IgKHZhciBpID0gMDsgaSA8IGNhdHMubGVuZ3RoOyArK2kpIHtcbiAgICAgIHZhciBjYXQgPSBjYXRzW2ldO1xuICAgICAgZiArPSBcImNhc2UgXCIgKyBjYXRbMF0ubGVuZ3RoICsgXCI6XCI7XG4gICAgICBjb21wYXJlVG8oY2F0KTtcbiAgICB9XG4gICAgZiArPSBcIn1cIlxuXG4gICAgLy8gT3RoZXJ3aXNlLCBzaW1wbHkgZ2VuZXJhdGUgYSBmbGF0IGBzd2l0Y2hgIHN0YXRlbWVudC5cblxuICAgIDtcbiAgfSBlbHNlIHtcbiAgICBjb21wYXJlVG8od29yZHMpO1xuICB9XG4gIHJldHVybiBuZXcgRnVuY3Rpb24oXCJzdHJcIiwgZik7XG59XG5cbi8vIFJlc2VydmVkIHdvcmQgbGlzdHMgZm9yIHZhcmlvdXMgZGlhbGVjdHMgb2YgdGhlIGxhbmd1YWdlXG5cbnZhciByZXNlcnZlZFdvcmRzID0ge1xuICAzOiBtYWtlUHJlZGljYXRlKFwiYWJzdHJhY3QgYm9vbGVhbiBieXRlIGNoYXIgY2xhc3MgZG91YmxlIGVudW0gZXhwb3J0IGV4dGVuZHMgZmluYWwgZmxvYXQgZ290byBpbXBsZW1lbnRzIGltcG9ydCBpbnQgaW50ZXJmYWNlIGxvbmcgbmF0aXZlIHBhY2thZ2UgcHJpdmF0ZSBwcm90ZWN0ZWQgcHVibGljIHNob3J0IHN0YXRpYyBzdXBlciBzeW5jaHJvbml6ZWQgdGhyb3dzIHRyYW5zaWVudCB2b2xhdGlsZVwiKSxcbiAgNTogbWFrZVByZWRpY2F0ZShcImNsYXNzIGVudW0gZXh0ZW5kcyBzdXBlciBjb25zdCBleHBvcnQgaW1wb3J0XCIpLFxuICA2OiBtYWtlUHJlZGljYXRlKFwiZW51bSBhd2FpdFwiKSxcbiAgc3RyaWN0OiBtYWtlUHJlZGljYXRlKFwiaW1wbGVtZW50cyBpbnRlcmZhY2UgbGV0IHBhY2thZ2UgcHJpdmF0ZSBwcm90ZWN0ZWQgcHVibGljIHN0YXRpYyB5aWVsZFwiKSxcbiAgc3RyaWN0QmluZDogbWFrZVByZWRpY2F0ZShcImV2YWwgYXJndW1lbnRzXCIpXG59O1xuXG5leHBvcnRzLnJlc2VydmVkV29yZHMgPSByZXNlcnZlZFdvcmRzO1xuLy8gQW5kIHRoZSBrZXl3b3Jkc1xuXG52YXIgZWNtYTVBbmRMZXNzS2V5d29yZHMgPSBcImJyZWFrIGNhc2UgY2F0Y2ggY29udGludWUgZGVidWdnZXIgZGVmYXVsdCBkbyBlbHNlIGZpbmFsbHkgZm9yIGZ1bmN0aW9uIGlmIHJldHVybiBzd2l0Y2ggdGhyb3cgdHJ5IHZhciB3aGlsZSB3aXRoIG51bGwgdHJ1ZSBmYWxzZSBpbnN0YW5jZW9mIHR5cGVvZiB2b2lkIGRlbGV0ZSBuZXcgaW4gdGhpc1wiO1xuXG52YXIga2V5d29yZHMgPSB7XG4gIDU6IG1ha2VQcmVkaWNhdGUoZWNtYTVBbmRMZXNzS2V5d29yZHMpLFxuICA2OiBtYWtlUHJlZGljYXRlKGVjbWE1QW5kTGVzc0tleXdvcmRzICsgXCIgbGV0IGNvbnN0IGNsYXNzIGV4dGVuZHMgZXhwb3J0IGltcG9ydCB5aWVsZCBzdXBlclwiKVxufTtcblxuZXhwb3J0cy5rZXl3b3JkcyA9IGtleXdvcmRzO1xuLy8gIyMgQ2hhcmFjdGVyIGNhdGVnb3JpZXNcblxuLy8gQmlnIHVnbHkgcmVndWxhciBleHByZXNzaW9ucyB0aGF0IG1hdGNoIGNoYXJhY3RlcnMgaW4gdGhlXG4vLyB3aGl0ZXNwYWNlLCBpZGVudGlmaWVyLCBhbmQgaWRlbnRpZmllci1zdGFydCBjYXRlZ29yaWVzLiBUaGVzZVxuLy8gYXJlIG9ubHkgYXBwbGllZCB3aGVuIGEgY2hhcmFjdGVyIGlzIGZvdW5kIHRvIGFjdHVhbGx5IGhhdmUgYVxuLy8gY29kZSBwb2ludCBhYm92ZSAxMjguXG4vLyBHZW5lcmF0ZWQgYnkgYHRvb2xzL2dlbmVyYXRlLWlkZW50aWZpZXItcmVnZXguanNgLlxuXG52YXIgbm9uQVNDSUlpZGVudGlmaWVyU3RhcnRDaGFycyA9IFwiwqrCtcK6w4Atw5bDmC3DtsO4LcuBy4Yty5HLoC3LpMusy67NsC3NtM22zbfNui3Nvc2/zobOiC3Ois6Mzo4tzqHOoy3Ptc+3LdKB0oot1K/UsS3VltWZ1aEt1ofXkC3XqtewLdey2KAt2YrZrtmv2bEt25Pbldul26bbrtuv27ot27zbv9yQ3JIt3K/djS3epd6x34ot36rftN+137rgoIAt4KCV4KCa4KCk4KCo4KGALeChmOCioC3gorLgpIQt4KS54KS94KWQ4KWYLeCloeClsS3gpoDgpoUt4KaM4KaP4KaQ4KaTLeCmqOCmqi3gprDgprLgprYt4Ka54Ka94KeO4Kec4Ked4KefLeCnoeCnsOCnseCohS3gqIrgqI/gqJDgqJMt4Kio4KiqLeCosOCosuCos+CoteCotuCouOCoueCpmS3gqZzgqZ7gqbIt4Km04KqFLeCqjeCqjy3gqpHgqpMt4Kqo4KqqLeCqsOCqsuCqs+CqtS3gqrngqr3gq5Dgq6Dgq6HgrIUt4KyM4KyP4KyQ4KyTLeCsqOCsqi3grLDgrLLgrLPgrLUt4Ky54Ky94K2c4K2d4K2fLeCtoeCtseCug+CuhS3grorgro4t4K6Q4K6SLeCuleCumeCumuCunOCunuCun+Cuo+CupOCuqC3grqrgrq4t4K654K+Q4LCFLeCwjOCwji3gsJDgsJIt4LCo4LCqLeCwueCwveCxmOCxmeCxoOCxoeCyhS3gsozgso4t4LKQ4LKSLeCyqOCyqi3gsrPgsrUt4LK54LK94LOe4LOg4LOh4LOx4LOy4LSFLeC0jOC0ji3gtJDgtJIt4LS64LS94LWO4LWg4LWh4LW6LeC1v+C2hS3gtpbgtpot4Lax4LazLeC2u+C2veC3gC3gt4bguIEt4Liw4Liy4Liz4LmALeC5huC6geC6guC6hOC6h+C6iOC6iuC6jeC6lC3gupfgupkt4Lqf4LqhLeC6o+C6peC6p+C6quC6q+C6rS3gurDgurLgurPgur3gu4At4LuE4LuG4LucLeC7n+C8gOC9gC3gvYfgvYkt4L2s4L6ILeC+jOGAgC3hgKrhgL/hgZAt4YGV4YGaLeGBneGBoeGBpeGBpuGBri3hgbDhgbUt4YKB4YKO4YKgLeGDheGDh+GDjeGDkC3hg7rhg7wt4YmI4YmKLeGJjeGJkC3hiZbhiZjhiZot4Ymd4YmgLeGKiOGKii3hio3hipAt4Yqw4YqyLeGKteGKuC3hir7hi4Dhi4It4YuF4YuILeGLluGLmC3hjJDhjJIt4YyV4YyYLeGNmuGOgC3hjo/hjqAt4Y+04ZCBLeGZrOGZry3hmb/hmoEt4Zqa4ZqgLeGbquGbri3hm7jhnIAt4ZyM4ZyOLeGckeGcoC3hnLHhnYAt4Z2R4Z2gLeGdrOGdri3hnbDhnoAt4Z6z4Z+X4Z+c4aCgLeGht+GigC3hoqjhoqrhorAt4aO14aSALeGknuGlkC3hpa3hpbAt4aW04aaALeGmq+GngS3hp4fhqIAt4aiW4aigLeGplOGqp+GshS3hrLPhrYUt4a2L4a6DLeGuoOGuruGur+Guui3hr6XhsIAt4bCj4bGNLeGxj+Gxmi3hsb3hs6kt4bOs4bOuLeGzseGzteGztuG0gC3htr/huIAt4byV4byYLeG8neG8oC3hvYXhvYgt4b2N4b2QLeG9l+G9meG9m+G9neG9ny3hvb3hvoAt4b604b62LeG+vOG+vuG/gi3hv4Thv4Yt4b+M4b+QLeG/k+G/li3hv5vhv6At4b+s4b+yLeG/tOG/ti3hv7zigbHigb/igpAt4oKc4oSC4oSH4oSKLeKEk+KEleKEmC3ihJ3ihKTihKbihKjihKot4oS54oS8LeKEv+KFhS3ihYnihY7ihaAt4oaI4rCALeKwruKwsC3isZ7isaAt4rOk4rOrLeKzruKzsuKzs+K0gC3itKXitKfitK3itLAt4rWn4rWv4raALeK2luK2oC3itqbitqgt4rau4rawLeK2tuK2uC3itr7it4At4reG4reILeK3juK3kC3it5bit5gt4ree44CFLeOAh+OAoS3jgKnjgLEt44C144C4LeOAvOOBgS3jgpbjgpst44Kf44KhLeODuuODvC3jg7/jhIUt44St44SxLeOGjuOGoC3jhrrjh7At44e/45CALeS2teS4gC3pv4zqgIAt6pKM6pOQLeqTveqUgC3qmIzqmJAt6pif6piq6pir6pmALeqZruqZvy3qmp3qmqAt6puv6pyXLeqcn+qcoi3qnojqnost6p6O6p6QLeqereqesOqeseqfty3qoIHqoIMt6qCF6qCHLeqgiuqgjC3qoKLqoYAt6qGz6qKCLeqis+qjsi3qo7fqo7vqpIot6qSl6qSwLeqlhuqloC3qpbzqpoQt6qay6qeP6qegLeqnpOqnpi3qp6/qp7ot6qe+6qiALeqoqOqpgC3qqYLqqYQt6qmL6qmgLeqptuqpuuqpvi3qqq/qqrHqqrXqqrbqqrkt6qq96quA6quC6qubLeqrneqroC3qq6rqq7It6qu06qyBLeqshuqsiS3qrI7qrJEt6qyW6qygLeqspuqsqC3qrK7qrLAt6q2a6q2cLeqtn+qtpOqtpeqvgC3qr6LqsIAt7Z6j7Z6wLe2fhu2fiy3tn7vvpIAt76mt76mwLe+rme+sgC3vrIbvrJMt76yX76yd76yfLe+sqO+sqi3vrLbvrLgt76y876y+762A762B762D762E762GLe+use+vky3vtL3vtZAt77aP77aSLe+3h++3sC3vt7vvubAt77m077m2Le+7vO+8oS3vvLrvvYEt772a772mLe++vu+/gi3vv4fvv4ot77+P77+SLe+/l++/mi3vv5xcIjtcbnZhciBub25BU0NJSWlkZW50aWZpZXJDaGFycyA9IFwi4oCM4oCNwrfMgC3Nr86H0oMt0ofWkS3Wvda/14HXgteE14XXh9iQLdia2Yst2anZsNuWLduc258t26Tbp9uo26ot263bsC3budyR3LAt3Yrepi3esN+ALd+J36st37PgoJYt4KCZ4KCbLeCgo+CgpS3goKfgoKkt4KCt4KGZLeChm+CjpC3gpIPgpLot4KS84KS+LeClj+ClkS3gpZfgpaLgpaPgpaYt4KWv4KaBLeCmg+CmvOCmvi3gp4Tgp4fgp4jgp4st4KeN4KeX4Kei4Kej4KemLeCnr+CogS3gqIPgqLzgqL4t4KmC4KmH4KmI4KmLLeCpjeCpkeCppi3gqbHgqbXgqoEt4KqD4Kq84Kq+LeCrheCrhy3gq4ngq4st4KuN4Kui4Kuj4KumLeCrr+CsgS3grIPgrLzgrL4t4K2E4K2H4K2I4K2LLeCtjeCtluCtl+CtouCto+Ctpi3gra/groLgrr4t4K+C4K+GLeCviOCvii3gr43gr5fgr6Yt4K+v4LCALeCwg+Cwvi3gsYTgsYYt4LGI4LGKLeCxjeCxleCxluCxouCxo+Cxpi3gsa/gsoEt4LKD4LK84LK+LeCzhOCzhi3gs4jgs4ot4LON4LOV4LOW4LOi4LOj4LOmLeCzr+C0gS3gtIPgtL4t4LWE4LWGLeC1iOC1ii3gtY3gtZfgtaLgtaPgtaYt4LWv4LaC4LaD4LeK4LePLeC3lOC3luC3mC3gt5/gt6Yt4Lev4Ley4Lez4Lix4Li0LeC4uuC5hy3guY7guZAt4LmZ4Lqx4Lq0LeC6ueC6u+C6vOC7iC3gu43gu5At4LuZ4LyY4LyZ4LygLeC8qeC8teC8t+C8ueC8vuC8v+C9sS3gvoTgvobgvofgvo0t4L6X4L6ZLeC+vOC/huGAqy3hgL7hgYAt4YGJ4YGWLeGBmeGBni3hgaDhgaIt4YGk4YGnLeGBreGBsS3hgbThgoIt4YKN4YKPLeGCneGNnS3hjZ/hjakt4Y2x4ZySLeGclOGcsi3hnLThnZLhnZPhnbLhnbPhnrQt4Z+T4Z+d4Z+gLeGfqeGgiy3hoI3hoJAt4aCZ4aKp4aSgLeGkq+GksC3hpLvhpYYt4aWP4aawLeGngOGniOGnieGnkC3hp5rhqJct4aib4amVLeGpnuGpoC3hqbzhqb8t4aqJ4aqQLeGqmeGqsC3hqr3hrIAt4ayE4ay0LeGthOGtkC3hrZnhrast4a2z4a6ALeGuguGuoS3hrq3hrrAt4a654a+mLeGvs+GwpC3hsLfhsYAt4bGJ4bGQLeGxmeGzkC3hs5Lhs5Qt4bOo4bOt4bOyLeGztOGzuOGzueG3gC3ht7Xht7wt4be/4oC/4oGA4oGU4oOQLeKDnOKDoeKDpS3ig7Dis68t4rOx4rW/4regLeK3v+OAqi3jgK/jgpnjgprqmKAt6pip6pmv6pm0LeqZveqan+qbsOqbseqgguqghuqgi+qgoy3qoKfqooDqooHqorQt6qOE6qOQLeqjmeqjoC3qo7HqpIAt6qSJ6qSmLeqkreqlhy3qpZPqpoAt6qaD6qazLeqngOqnkC3qp5nqp6Xqp7At6qe56qipLeqotuqpg+qpjOqpjeqpkC3qqZnqqbst6qm96qqw6qqyLeqqtOqqt+qquOqqvuqqv+qrgeqrqy3qq6/qq7Xqq7bqr6Mt6q+q6q+s6q+t6q+wLeqvue+snu+4gC3vuI/vuKAt77it77iz77i077mNLe+5j++8kC3vvJnvvL9cIjtcblxudmFyIG5vbkFTQ0lJaWRlbnRpZmllclN0YXJ0ID0gbmV3IFJlZ0V4cChcIltcIiArIG5vbkFTQ0lJaWRlbnRpZmllclN0YXJ0Q2hhcnMgKyBcIl1cIik7XG52YXIgbm9uQVNDSUlpZGVudGlmaWVyID0gbmV3IFJlZ0V4cChcIltcIiArIG5vbkFTQ0lJaWRlbnRpZmllclN0YXJ0Q2hhcnMgKyBub25BU0NJSWlkZW50aWZpZXJDaGFycyArIFwiXVwiKTtcblxubm9uQVNDSUlpZGVudGlmaWVyU3RhcnRDaGFycyA9IG5vbkFTQ0lJaWRlbnRpZmllckNoYXJzID0gbnVsbDtcblxuLy8gVGhlc2UgYXJlIGEgcnVuLWxlbmd0aCBhbmQgb2Zmc2V0IGVuY29kZWQgcmVwcmVzZW50YXRpb24gb2YgdGhlXG4vLyA+MHhmZmZmIGNvZGUgcG9pbnRzIHRoYXQgYXJlIGEgdmFsaWQgcGFydCBvZiBpZGVudGlmaWVycy4gVGhlXG4vLyBvZmZzZXQgc3RhcnRzIGF0IDB4MTAwMDAsIGFuZCBlYWNoIHBhaXIgb2YgbnVtYmVycyByZXByZXNlbnRzIGFuXG4vLyBvZmZzZXQgdG8gdGhlIG5leHQgcmFuZ2UsIGFuZCB0aGVuIGEgc2l6ZSBvZiB0aGUgcmFuZ2UuIFRoZXkgd2VyZVxuLy8gZ2VuZXJhdGVkIGJ5IHRvb2xzL2dlbmVyYXRlLWlkZW50aWZpZXItcmVnZXguanNcbnZhciBhc3RyYWxJZGVudGlmaWVyU3RhcnRDb2RlcyA9IFswLCAxMSwgMiwgMjUsIDIsIDE4LCAyLCAxLCAyLCAxNCwgMywgMTMsIDM1LCAxMjIsIDcwLCA1MiwgMjY4LCAyOCwgNCwgNDgsIDQ4LCAzMSwgMTcsIDI2LCA2LCAzNywgMTEsIDI5LCAzLCAzNSwgNSwgNywgMiwgNCwgNDMsIDE1NywgOTksIDM5LCA5LCA1MSwgMTU3LCAzMTAsIDEwLCAyMSwgMTEsIDcsIDE1MywgNSwgMywgMCwgMiwgNDMsIDIsIDEsIDQsIDAsIDMsIDIyLCAxMSwgMjIsIDEwLCAzMCwgOTgsIDIxLCAxMSwgMjUsIDcxLCA1NSwgNywgMSwgNjUsIDAsIDE2LCAzLCAyLCAyLCAyLCAyNiwgNDUsIDI4LCA0LCAyOCwgMzYsIDcsIDIsIDI3LCAyOCwgNTMsIDExLCAyMSwgMTEsIDE4LCAxNCwgMTcsIDExMSwgNzIsIDk1NSwgNTIsIDc2LCA0NCwgMzMsIDI0LCAyNywgMzUsIDQyLCAzNCwgNCwgMCwgMTMsIDQ3LCAxNSwgMywgMjIsIDAsIDM4LCAxNywgMiwgMjQsIDEzMywgNDYsIDM5LCA3LCAzLCAxLCAzLCAyMSwgMiwgNiwgMiwgMSwgMiwgNCwgNCwgMCwgMzIsIDQsIDI4NywgNDcsIDIxLCAxLCAyLCAwLCAxODUsIDQ2LCA4MiwgNDcsIDIxLCAwLCA2MCwgNDIsIDUwMiwgNjMsIDMyLCAwLCA0NDksIDU2LCAxMjg4LCA5MjAsIDEwNCwgMTEwLCAyOTYyLCAxMDcwLCAxMzI2NiwgNTY4LCA4LCAzMCwgMTE0LCAyOSwgMTksIDQ3LCAxNywgMywgMzIsIDIwLCA2LCAxOCwgODgxLCA2OCwgMTIsIDAsIDY3LCAxMiwgMTY0ODEsIDEsIDMwNzEsIDEwNiwgNiwgMTIsIDQsIDgsIDgsIDksIDU5OTEsIDg0LCAyLCA3MCwgMiwgMSwgMywgMCwgMywgMSwgMywgMywgMiwgMTEsIDIsIDAsIDIsIDYsIDIsIDY0LCAyLCAzLCAzLCA3LCAyLCA2LCAyLCAyNywgMiwgMywgMiwgNCwgMiwgMCwgNCwgNiwgMiwgMzM5LCAzLCAyNCwgMiwgMjQsIDIsIDMwLCAyLCAyNCwgMiwgMzAsIDIsIDI0LCAyLCAzMCwgMiwgMjQsIDIsIDMwLCAyLCAyNCwgMiwgNywgNDE0OSwgMTk2LCAxMzQwLCAzLCAyLCAyNiwgMiwgMSwgMiwgMCwgMywgMCwgMiwgOSwgMiwgMywgMiwgMCwgMiwgMCwgNywgMCwgNSwgMCwgMiwgMCwgMiwgMCwgMiwgMiwgMiwgMSwgMiwgMCwgMywgMCwgMiwgMCwgMiwgMCwgMiwgMCwgMiwgMCwgMiwgMSwgMiwgMCwgMywgMywgMiwgNiwgMiwgMywgMiwgMywgMiwgMCwgMiwgOSwgMiwgMTYsIDYsIDIsIDIsIDQsIDIsIDE2LCA0NDIxLCA0MjcxMCwgNDIsIDQxNDgsIDEyLCAyMjEsIDE2MzU1LCA1NDFdO1xudmFyIGFzdHJhbElkZW50aWZpZXJDb2RlcyA9IFs1MDksIDAsIDIyNywgMCwgMTUwLCA0LCAyOTQsIDksIDEzNjgsIDIsIDIsIDEsIDYsIDMsIDQxLCAyLCA1LCAwLCAxNjYsIDEsIDEzMDYsIDIsIDU0LCAxNCwgMzIsIDksIDE2LCAzLCA0NiwgMTAsIDU0LCA5LCA3LCAyLCAzNywgMTMsIDIsIDksIDUyLCAwLCAxMywgMiwgNDksIDEzLCAxNiwgOSwgODMsIDExLCAxNjgsIDExLCA2LCA5LCA4LCAyLCA1NywgMCwgMiwgNiwgMywgMSwgMywgMiwgMTAsIDAsIDExLCAxLCAzLCA2LCA0LCA0LCAzMTYsIDE5LCAxMywgOSwgMjE0LCA2LCAzLCA4LCAxMTIsIDE2LCAxNiwgOSwgODIsIDEyLCA5LCA5LCA1MzUsIDksIDIwODU1LCA5LCAxMzUsIDQsIDYwLCA2LCAyNiwgOSwgMTAxNiwgNDUsIDE3LCAzLCAxOTcyMywgMSwgNTMxOSwgNCwgNCwgNSwgOSwgNywgMywgNiwgMzEsIDMsIDE0OSwgMiwgMTQxOCwgNDksIDQzMDUsIDYsIDc5MjYxOCwgMjM5XTtcblxuLy8gVGhpcyBoYXMgYSBjb21wbGV4aXR5IGxpbmVhciB0byB0aGUgdmFsdWUgb2YgdGhlIGNvZGUuIFRoZVxuLy8gYXNzdW1wdGlvbiBpcyB0aGF0IGxvb2tpbmcgdXAgYXN0cmFsIGlkZW50aWZpZXIgY2hhcmFjdGVycyBpc1xuLy8gcmFyZS5cbmZ1bmN0aW9uIGlzSW5Bc3RyYWxTZXQoY29kZSwgc2V0KSB7XG4gIHZhciBwb3MgPSAweDEwMDAwO1xuICBmb3IgKHZhciBpID0gMDsgaSA8IHNldC5sZW5ndGg7IGkgKz0gMikge1xuICAgIHBvcyArPSBzZXRbaV07XG4gICAgaWYgKHBvcyA+IGNvZGUpIHJldHVybiBmYWxzZTtcbiAgICBwb3MgKz0gc2V0W2kgKyAxXTtcbiAgICBpZiAocG9zID49IGNvZGUpIHJldHVybiB0cnVlO1xuICB9XG59XG5cbi8vIFRlc3Qgd2hldGhlciBhIGdpdmVuIGNoYXJhY3RlciBjb2RlIHN0YXJ0cyBhbiBpZGVudGlmaWVyLlxuXG5mdW5jdGlvbiBpc0lkZW50aWZpZXJTdGFydChjb2RlLCBhc3RyYWwpIHtcbiAgaWYgKGNvZGUgPCA2NSkgcmV0dXJuIGNvZGUgPT09IDM2O1xuICBpZiAoY29kZSA8IDkxKSByZXR1cm4gdHJ1ZTtcbiAgaWYgKGNvZGUgPCA5NykgcmV0dXJuIGNvZGUgPT09IDk1O1xuICBpZiAoY29kZSA8IDEyMykgcmV0dXJuIHRydWU7XG4gIGlmIChjb2RlIDw9IDB4ZmZmZikgcmV0dXJuIGNvZGUgPj0gMHhhYSAmJiBub25BU0NJSWlkZW50aWZpZXJTdGFydC50ZXN0KFN0cmluZy5mcm9tQ2hhckNvZGUoY29kZSkpO1xuICBpZiAoYXN0cmFsID09PSBmYWxzZSkgcmV0dXJuIGZhbHNlO1xuICByZXR1cm4gaXNJbkFzdHJhbFNldChjb2RlLCBhc3RyYWxJZGVudGlmaWVyU3RhcnRDb2Rlcyk7XG59XG5cbi8vIFRlc3Qgd2hldGhlciBhIGdpdmVuIGNoYXJhY3RlciBpcyBwYXJ0IG9mIGFuIGlkZW50aWZpZXIuXG5cbmZ1bmN0aW9uIGlzSWRlbnRpZmllckNoYXIoY29kZSwgYXN0cmFsKSB7XG4gIGlmIChjb2RlIDwgNDgpIHJldHVybiBjb2RlID09PSAzNjtcbiAgaWYgKGNvZGUgPCA1OCkgcmV0dXJuIHRydWU7XG4gIGlmIChjb2RlIDwgNjUpIHJldHVybiBmYWxzZTtcbiAgaWYgKGNvZGUgPCA5MSkgcmV0dXJuIHRydWU7XG4gIGlmIChjb2RlIDwgOTcpIHJldHVybiBjb2RlID09PSA5NTtcbiAgaWYgKGNvZGUgPCAxMjMpIHJldHVybiB0cnVlO1xuICBpZiAoY29kZSA8PSAweGZmZmYpIHJldHVybiBjb2RlID49IDB4YWEgJiYgbm9uQVNDSUlpZGVudGlmaWVyLnRlc3QoU3RyaW5nLmZyb21DaGFyQ29kZShjb2RlKSk7XG4gIGlmIChhc3RyYWwgPT09IGZhbHNlKSByZXR1cm4gZmFsc2U7XG4gIHJldHVybiBpc0luQXN0cmFsU2V0KGNvZGUsIGFzdHJhbElkZW50aWZpZXJTdGFydENvZGVzKSB8fCBpc0luQXN0cmFsU2V0KGNvZGUsIGFzdHJhbElkZW50aWZpZXJDb2Rlcyk7XG59XG5cbn0se31dLDM6W2Z1bmN0aW9uKF9kZXJlcV8sbW9kdWxlLGV4cG9ydHMpe1xuLy8gQWNvcm4gaXMgYSB0aW55LCBmYXN0IEphdmFTY3JpcHQgcGFyc2VyIHdyaXR0ZW4gaW4gSmF2YVNjcmlwdC5cbi8vXG4vLyBBY29ybiB3YXMgd3JpdHRlbiBieSBNYXJpam4gSGF2ZXJiZWtlLCBJbmd2YXIgU3RlcGFueWFuLCBhbmRcbi8vIHZhcmlvdXMgY29udHJpYnV0b3JzIGFuZCByZWxlYXNlZCB1bmRlciBhbiBNSVQgbGljZW5zZS5cbi8vXG4vLyBHaXQgcmVwb3NpdG9yaWVzIGZvciBBY29ybiBhcmUgYXZhaWxhYmxlIGF0XG4vL1xuLy8gICAgIGh0dHA6Ly9tYXJpam5oYXZlcmJla2UubmwvZ2l0L2Fjb3JuXG4vLyAgICAgaHR0cHM6Ly9naXRodWIuY29tL21hcmlqbmgvYWNvcm4uZ2l0XG4vL1xuLy8gUGxlYXNlIHVzZSB0aGUgW2dpdGh1YiBidWcgdHJhY2tlcl1bZ2hidF0gdG8gcmVwb3J0IGlzc3Vlcy5cbi8vXG4vLyBbZ2hidF06IGh0dHBzOi8vZ2l0aHViLmNvbS9tYXJpam5oL2Fjb3JuL2lzc3Vlc1xuLy9cbi8vIFRoaXMgZmlsZSBkZWZpbmVzIHRoZSBtYWluIHBhcnNlciBpbnRlcmZhY2UuIFRoZSBsaWJyYXJ5IGFsc28gY29tZXNcbi8vIHdpdGggYSBbZXJyb3ItdG9sZXJhbnQgcGFyc2VyXVtkYW1taXRdIGFuZCBhblxuLy8gW2Fic3RyYWN0IHN5bnRheCB0cmVlIHdhbGtlcl1bd2Fsa10sIGRlZmluZWQgaW4gb3RoZXIgZmlsZXMuXG4vL1xuLy8gW2RhbW1pdF06IGFjb3JuX2xvb3NlLmpzXG4vLyBbd2Fsa106IHV0aWwvd2Fsay5qc1xuXG5cInVzZSBzdHJpY3RcIjtcblxuZXhwb3J0cy5fX2VzTW9kdWxlID0gdHJ1ZTtcbmV4cG9ydHMucGFyc2UgPSBwYXJzZTtcbmV4cG9ydHMucGFyc2VFeHByZXNzaW9uQXQgPSBwYXJzZUV4cHJlc3Npb25BdDtcbmV4cG9ydHMudG9rZW5pemVyID0gdG9rZW5pemVyO1xuXG52YXIgX3N0YXRlID0gX2RlcmVxXyhcIi4vc3RhdGVcIik7XG5cbnZhciBfb3B0aW9ucyA9IF9kZXJlcV8oXCIuL29wdGlvbnNcIik7XG5cbl9kZXJlcV8oXCIuL3BhcnNldXRpbFwiKTtcblxuX2RlcmVxXyhcIi4vc3RhdGVtZW50XCIpO1xuXG5fZGVyZXFfKFwiLi9sdmFsXCIpO1xuXG5fZGVyZXFfKFwiLi9leHByZXNzaW9uXCIpO1xuXG5fZGVyZXFfKFwiLi9sb2NhdGlvblwiKTtcblxuZXhwb3J0cy5QYXJzZXIgPSBfc3RhdGUuUGFyc2VyO1xuZXhwb3J0cy5wbHVnaW5zID0gX3N0YXRlLnBsdWdpbnM7XG5leHBvcnRzLmRlZmF1bHRPcHRpb25zID0gX29wdGlvbnMuZGVmYXVsdE9wdGlvbnM7XG5cbnZhciBfbG9jdXRpbCA9IF9kZXJlcV8oXCIuL2xvY3V0aWxcIik7XG5cbmV4cG9ydHMuUG9zaXRpb24gPSBfbG9jdXRpbC5Qb3NpdGlvbjtcbmV4cG9ydHMuU291cmNlTG9jYXRpb24gPSBfbG9jdXRpbC5Tb3VyY2VMb2NhdGlvbjtcbmV4cG9ydHMuZ2V0TGluZUluZm8gPSBfbG9jdXRpbC5nZXRMaW5lSW5mbztcblxudmFyIF9ub2RlID0gX2RlcmVxXyhcIi4vbm9kZVwiKTtcblxuZXhwb3J0cy5Ob2RlID0gX25vZGUuTm9kZTtcblxudmFyIF90b2tlbnR5cGUgPSBfZGVyZXFfKFwiLi90b2tlbnR5cGVcIik7XG5cbmV4cG9ydHMuVG9rZW5UeXBlID0gX3Rva2VudHlwZS5Ub2tlblR5cGU7XG5leHBvcnRzLnRva1R5cGVzID0gX3Rva2VudHlwZS50eXBlcztcblxudmFyIF90b2tlbmNvbnRleHQgPSBfZGVyZXFfKFwiLi90b2tlbmNvbnRleHRcIik7XG5cbmV4cG9ydHMuVG9rQ29udGV4dCA9IF90b2tlbmNvbnRleHQuVG9rQ29udGV4dDtcbmV4cG9ydHMudG9rQ29udGV4dHMgPSBfdG9rZW5jb250ZXh0LnR5cGVzO1xuXG52YXIgX2lkZW50aWZpZXIgPSBfZGVyZXFfKFwiLi9pZGVudGlmaWVyXCIpO1xuXG5leHBvcnRzLmlzSWRlbnRpZmllckNoYXIgPSBfaWRlbnRpZmllci5pc0lkZW50aWZpZXJDaGFyO1xuZXhwb3J0cy5pc0lkZW50aWZpZXJTdGFydCA9IF9pZGVudGlmaWVyLmlzSWRlbnRpZmllclN0YXJ0O1xuXG52YXIgX3Rva2VuaXplID0gX2RlcmVxXyhcIi4vdG9rZW5pemVcIik7XG5cbmV4cG9ydHMuVG9rZW4gPSBfdG9rZW5pemUuVG9rZW47XG5cbnZhciBfd2hpdGVzcGFjZSA9IF9kZXJlcV8oXCIuL3doaXRlc3BhY2VcIik7XG5cbmV4cG9ydHMuaXNOZXdMaW5lID0gX3doaXRlc3BhY2UuaXNOZXdMaW5lO1xuZXhwb3J0cy5saW5lQnJlYWsgPSBfd2hpdGVzcGFjZS5saW5lQnJlYWs7XG5leHBvcnRzLmxpbmVCcmVha0cgPSBfd2hpdGVzcGFjZS5saW5lQnJlYWtHO1xudmFyIHZlcnNpb24gPSBcIjIuNC4wXCI7XG5cbmV4cG9ydHMudmVyc2lvbiA9IHZlcnNpb247XG4vLyBUaGUgbWFpbiBleHBvcnRlZCBpbnRlcmZhY2UgKHVuZGVyIGBzZWxmLmFjb3JuYCB3aGVuIGluIHRoZVxuLy8gYnJvd3NlcikgaXMgYSBgcGFyc2VgIGZ1bmN0aW9uIHRoYXQgdGFrZXMgYSBjb2RlIHN0cmluZyBhbmRcbi8vIHJldHVybnMgYW4gYWJzdHJhY3Qgc3ludGF4IHRyZWUgYXMgc3BlY2lmaWVkIGJ5IFtNb3ppbGxhIHBhcnNlclxuLy8gQVBJXVthcGldLlxuLy9cbi8vIFthcGldOiBodHRwczovL2RldmVsb3Blci5tb3ppbGxhLm9yZy9lbi1VUy9kb2NzL1NwaWRlck1vbmtleS9QYXJzZXJfQVBJXG5cbmZ1bmN0aW9uIHBhcnNlKGlucHV0LCBvcHRpb25zKSB7XG4gIHJldHVybiBuZXcgX3N0YXRlLlBhcnNlcihvcHRpb25zLCBpbnB1dCkucGFyc2UoKTtcbn1cblxuLy8gVGhpcyBmdW5jdGlvbiB0cmllcyB0byBwYXJzZSBhIHNpbmdsZSBleHByZXNzaW9uIGF0IGEgZ2l2ZW5cbi8vIG9mZnNldCBpbiBhIHN0cmluZy4gVXNlZnVsIGZvciBwYXJzaW5nIG1peGVkLWxhbmd1YWdlIGZvcm1hdHNcbi8vIHRoYXQgZW1iZWQgSmF2YVNjcmlwdCBleHByZXNzaW9ucy5cblxuZnVuY3Rpb24gcGFyc2VFeHByZXNzaW9uQXQoaW5wdXQsIHBvcywgb3B0aW9ucykge1xuICB2YXIgcCA9IG5ldyBfc3RhdGUuUGFyc2VyKG9wdGlvbnMsIGlucHV0LCBwb3MpO1xuICBwLm5leHRUb2tlbigpO1xuICByZXR1cm4gcC5wYXJzZUV4cHJlc3Npb24oKTtcbn1cblxuLy8gQWNvcm4gaXMgb3JnYW5pemVkIGFzIGEgdG9rZW5pemVyIGFuZCBhIHJlY3Vyc2l2ZS1kZXNjZW50IHBhcnNlci5cbi8vIFRoZSBgdG9rZW5pemVgIGV4cG9ydCBwcm92aWRlcyBhbiBpbnRlcmZhY2UgdG8gdGhlIHRva2VuaXplci5cblxuZnVuY3Rpb24gdG9rZW5pemVyKGlucHV0LCBvcHRpb25zKSB7XG4gIHJldHVybiBuZXcgX3N0YXRlLlBhcnNlcihvcHRpb25zLCBpbnB1dCk7XG59XG5cbn0se1wiLi9leHByZXNzaW9uXCI6MSxcIi4vaWRlbnRpZmllclwiOjIsXCIuL2xvY2F0aW9uXCI6NCxcIi4vbG9jdXRpbFwiOjUsXCIuL2x2YWxcIjo2LFwiLi9ub2RlXCI6NyxcIi4vb3B0aW9uc1wiOjgsXCIuL3BhcnNldXRpbFwiOjksXCIuL3N0YXRlXCI6MTAsXCIuL3N0YXRlbWVudFwiOjExLFwiLi90b2tlbmNvbnRleHRcIjoxMixcIi4vdG9rZW5pemVcIjoxMyxcIi4vdG9rZW50eXBlXCI6MTQsXCIuL3doaXRlc3BhY2VcIjoxNn1dLDQ6W2Z1bmN0aW9uKF9kZXJlcV8sbW9kdWxlLGV4cG9ydHMpe1xuXCJ1c2Ugc3RyaWN0XCI7XG5cbnZhciBfc3RhdGUgPSBfZGVyZXFfKFwiLi9zdGF0ZVwiKTtcblxudmFyIF9sb2N1dGlsID0gX2RlcmVxXyhcIi4vbG9jdXRpbFwiKTtcblxudmFyIHBwID0gX3N0YXRlLlBhcnNlci5wcm90b3R5cGU7XG5cbi8vIFRoaXMgZnVuY3Rpb24gaXMgdXNlZCB0byByYWlzZSBleGNlcHRpb25zIG9uIHBhcnNlIGVycm9ycy4gSXRcbi8vIHRha2VzIGFuIG9mZnNldCBpbnRlZ2VyIChpbnRvIHRoZSBjdXJyZW50IGBpbnB1dGApIHRvIGluZGljYXRlXG4vLyB0aGUgbG9jYXRpb24gb2YgdGhlIGVycm9yLCBhdHRhY2hlcyB0aGUgcG9zaXRpb24gdG8gdGhlIGVuZFxuLy8gb2YgdGhlIGVycm9yIG1lc3NhZ2UsIGFuZCB0aGVuIHJhaXNlcyBhIGBTeW50YXhFcnJvcmAgd2l0aCB0aGF0XG4vLyBtZXNzYWdlLlxuXG5wcC5yYWlzZSA9IGZ1bmN0aW9uIChwb3MsIG1lc3NhZ2UpIHtcbiAgdmFyIGxvYyA9IF9sb2N1dGlsLmdldExpbmVJbmZvKHRoaXMuaW5wdXQsIHBvcyk7XG4gIG1lc3NhZ2UgKz0gXCIgKFwiICsgbG9jLmxpbmUgKyBcIjpcIiArIGxvYy5jb2x1bW4gKyBcIilcIjtcbiAgdmFyIGVyciA9IG5ldyBTeW50YXhFcnJvcihtZXNzYWdlKTtcbiAgZXJyLnBvcyA9IHBvcztlcnIubG9jID0gbG9jO2Vyci5yYWlzZWRBdCA9IHRoaXMucG9zO1xuICB0aHJvdyBlcnI7XG59O1xuXG5wcC5jdXJQb3NpdGlvbiA9IGZ1bmN0aW9uICgpIHtcbiAgaWYgKHRoaXMub3B0aW9ucy5sb2NhdGlvbnMpIHtcbiAgICByZXR1cm4gbmV3IF9sb2N1dGlsLlBvc2l0aW9uKHRoaXMuY3VyTGluZSwgdGhpcy5wb3MgLSB0aGlzLmxpbmVTdGFydCk7XG4gIH1cbn07XG5cbn0se1wiLi9sb2N1dGlsXCI6NSxcIi4vc3RhdGVcIjoxMH1dLDU6W2Z1bmN0aW9uKF9kZXJlcV8sbW9kdWxlLGV4cG9ydHMpe1xuXCJ1c2Ugc3RyaWN0XCI7XG5cbmV4cG9ydHMuX19lc01vZHVsZSA9IHRydWU7XG5leHBvcnRzLmdldExpbmVJbmZvID0gZ2V0TGluZUluZm87XG5cbmZ1bmN0aW9uIF9jbGFzc0NhbGxDaGVjayhpbnN0YW5jZSwgQ29uc3RydWN0b3IpIHsgaWYgKCEoaW5zdGFuY2UgaW5zdGFuY2VvZiBDb25zdHJ1Y3RvcikpIHsgdGhyb3cgbmV3IFR5cGVFcnJvcihcIkNhbm5vdCBjYWxsIGEgY2xhc3MgYXMgYSBmdW5jdGlvblwiKTsgfSB9XG5cbnZhciBfd2hpdGVzcGFjZSA9IF9kZXJlcV8oXCIuL3doaXRlc3BhY2VcIik7XG5cbi8vIFRoZXNlIGFyZSB1c2VkIHdoZW4gYG9wdGlvbnMubG9jYXRpb25zYCBpcyBvbiwgZm9yIHRoZVxuLy8gYHN0YXJ0TG9jYCBhbmQgYGVuZExvY2AgcHJvcGVydGllcy5cblxudmFyIFBvc2l0aW9uID0gKGZ1bmN0aW9uICgpIHtcbiAgZnVuY3Rpb24gUG9zaXRpb24obGluZSwgY29sKSB7XG4gICAgX2NsYXNzQ2FsbENoZWNrKHRoaXMsIFBvc2l0aW9uKTtcblxuICAgIHRoaXMubGluZSA9IGxpbmU7XG4gICAgdGhpcy5jb2x1bW4gPSBjb2w7XG4gIH1cblxuICBQb3NpdGlvbi5wcm90b3R5cGUub2Zmc2V0ID0gZnVuY3Rpb24gb2Zmc2V0KG4pIHtcbiAgICByZXR1cm4gbmV3IFBvc2l0aW9uKHRoaXMubGluZSwgdGhpcy5jb2x1bW4gKyBuKTtcbiAgfTtcblxuICByZXR1cm4gUG9zaXRpb247XG59KSgpO1xuXG5leHBvcnRzLlBvc2l0aW9uID0gUG9zaXRpb247XG5cbnZhciBTb3VyY2VMb2NhdGlvbiA9IGZ1bmN0aW9uIFNvdXJjZUxvY2F0aW9uKHAsIHN0YXJ0LCBlbmQpIHtcbiAgX2NsYXNzQ2FsbENoZWNrKHRoaXMsIFNvdXJjZUxvY2F0aW9uKTtcblxuICB0aGlzLnN0YXJ0ID0gc3RhcnQ7XG4gIHRoaXMuZW5kID0gZW5kO1xuICBpZiAocC5zb3VyY2VGaWxlICE9PSBudWxsKSB0aGlzLnNvdXJjZSA9IHAuc291cmNlRmlsZTtcbn07XG5cbmV4cG9ydHMuU291cmNlTG9jYXRpb24gPSBTb3VyY2VMb2NhdGlvbjtcblxuLy8gVGhlIGBnZXRMaW5lSW5mb2AgZnVuY3Rpb24gaXMgbW9zdGx5IHVzZWZ1bCB3aGVuIHRoZVxuLy8gYGxvY2F0aW9uc2Agb3B0aW9uIGlzIG9mZiAoZm9yIHBlcmZvcm1hbmNlIHJlYXNvbnMpIGFuZCB5b3Vcbi8vIHdhbnQgdG8gZmluZCB0aGUgbGluZS9jb2x1bW4gcG9zaXRpb24gZm9yIGEgZ2l2ZW4gY2hhcmFjdGVyXG4vLyBvZmZzZXQuIGBpbnB1dGAgc2hvdWxkIGJlIHRoZSBjb2RlIHN0cmluZyB0aGF0IHRoZSBvZmZzZXQgcmVmZXJzXG4vLyBpbnRvLlxuXG5mdW5jdGlvbiBnZXRMaW5lSW5mbyhpbnB1dCwgb2Zmc2V0KSB7XG4gIGZvciAodmFyIGxpbmUgPSAxLCBjdXIgPSAwOzspIHtcbiAgICBfd2hpdGVzcGFjZS5saW5lQnJlYWtHLmxhc3RJbmRleCA9IGN1cjtcbiAgICB2YXIgbWF0Y2ggPSBfd2hpdGVzcGFjZS5saW5lQnJlYWtHLmV4ZWMoaW5wdXQpO1xuICAgIGlmIChtYXRjaCAmJiBtYXRjaC5pbmRleCA8IG9mZnNldCkge1xuICAgICAgKytsaW5lO1xuICAgICAgY3VyID0gbWF0Y2guaW5kZXggKyBtYXRjaFswXS5sZW5ndGg7XG4gICAgfSBlbHNlIHtcbiAgICAgIHJldHVybiBuZXcgUG9zaXRpb24obGluZSwgb2Zmc2V0IC0gY3VyKTtcbiAgICB9XG4gIH1cbn1cblxufSx7XCIuL3doaXRlc3BhY2VcIjoxNn1dLDY6W2Z1bmN0aW9uKF9kZXJlcV8sbW9kdWxlLGV4cG9ydHMpe1xuXCJ1c2Ugc3RyaWN0XCI7XG5cbnZhciBfdG9rZW50eXBlID0gX2RlcmVxXyhcIi4vdG9rZW50eXBlXCIpO1xuXG52YXIgX3N0YXRlID0gX2RlcmVxXyhcIi4vc3RhdGVcIik7XG5cbnZhciBfaWRlbnRpZmllciA9IF9kZXJlcV8oXCIuL2lkZW50aWZpZXJcIik7XG5cbnZhciBfdXRpbCA9IF9kZXJlcV8oXCIuL3V0aWxcIik7XG5cbnZhciBwcCA9IF9zdGF0ZS5QYXJzZXIucHJvdG90eXBlO1xuXG4vLyBDb252ZXJ0IGV4aXN0aW5nIGV4cHJlc3Npb24gYXRvbSB0byBhc3NpZ25hYmxlIHBhdHRlcm5cbi8vIGlmIHBvc3NpYmxlLlxuXG5wcC50b0Fzc2lnbmFibGUgPSBmdW5jdGlvbiAobm9kZSwgaXNCaW5kaW5nKSB7XG4gIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNiAmJiBub2RlKSB7XG4gICAgc3dpdGNoIChub2RlLnR5cGUpIHtcbiAgICAgIGNhc2UgXCJJZGVudGlmaWVyXCI6XG4gICAgICBjYXNlIFwiT2JqZWN0UGF0dGVyblwiOlxuICAgICAgY2FzZSBcIkFycmF5UGF0dGVyblwiOlxuICAgICAgY2FzZSBcIkFzc2lnbm1lbnRQYXR0ZXJuXCI6XG4gICAgICAgIGJyZWFrO1xuXG4gICAgICBjYXNlIFwiT2JqZWN0RXhwcmVzc2lvblwiOlxuICAgICAgICBub2RlLnR5cGUgPSBcIk9iamVjdFBhdHRlcm5cIjtcbiAgICAgICAgZm9yICh2YXIgaSA9IDA7IGkgPCBub2RlLnByb3BlcnRpZXMubGVuZ3RoOyBpKyspIHtcbiAgICAgICAgICB2YXIgcHJvcCA9IG5vZGUucHJvcGVydGllc1tpXTtcbiAgICAgICAgICBpZiAocHJvcC5raW5kICE9PSBcImluaXRcIikgdGhpcy5yYWlzZShwcm9wLmtleS5zdGFydCwgXCJPYmplY3QgcGF0dGVybiBjYW4ndCBjb250YWluIGdldHRlciBvciBzZXR0ZXJcIik7XG4gICAgICAgICAgdGhpcy50b0Fzc2lnbmFibGUocHJvcC52YWx1ZSwgaXNCaW5kaW5nKTtcbiAgICAgICAgfVxuICAgICAgICBicmVhaztcblxuICAgICAgY2FzZSBcIkFycmF5RXhwcmVzc2lvblwiOlxuICAgICAgICBub2RlLnR5cGUgPSBcIkFycmF5UGF0dGVyblwiO1xuICAgICAgICB0aGlzLnRvQXNzaWduYWJsZUxpc3Qobm9kZS5lbGVtZW50cywgaXNCaW5kaW5nKTtcbiAgICAgICAgYnJlYWs7XG5cbiAgICAgIGNhc2UgXCJBc3NpZ25tZW50RXhwcmVzc2lvblwiOlxuICAgICAgICBpZiAobm9kZS5vcGVyYXRvciA9PT0gXCI9XCIpIHtcbiAgICAgICAgICBub2RlLnR5cGUgPSBcIkFzc2lnbm1lbnRQYXR0ZXJuXCI7XG4gICAgICAgICAgZGVsZXRlIG5vZGUub3BlcmF0b3I7XG4gICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgdGhpcy5yYWlzZShub2RlLmxlZnQuZW5kLCBcIk9ubHkgJz0nIG9wZXJhdG9yIGNhbiBiZSB1c2VkIGZvciBzcGVjaWZ5aW5nIGRlZmF1bHQgdmFsdWUuXCIpO1xuICAgICAgICB9XG4gICAgICAgIGJyZWFrO1xuXG4gICAgICBjYXNlIFwiUGFyZW50aGVzaXplZEV4cHJlc3Npb25cIjpcbiAgICAgICAgbm9kZS5leHByZXNzaW9uID0gdGhpcy50b0Fzc2lnbmFibGUobm9kZS5leHByZXNzaW9uLCBpc0JpbmRpbmcpO1xuICAgICAgICBicmVhaztcblxuICAgICAgY2FzZSBcIk1lbWJlckV4cHJlc3Npb25cIjpcbiAgICAgICAgaWYgKCFpc0JpbmRpbmcpIGJyZWFrO1xuXG4gICAgICBkZWZhdWx0OlxuICAgICAgICB0aGlzLnJhaXNlKG5vZGUuc3RhcnQsIFwiQXNzaWduaW5nIHRvIHJ2YWx1ZVwiKTtcbiAgICB9XG4gIH1cbiAgcmV0dXJuIG5vZGU7XG59O1xuXG4vLyBDb252ZXJ0IGxpc3Qgb2YgZXhwcmVzc2lvbiBhdG9tcyB0byBiaW5kaW5nIGxpc3QuXG5cbnBwLnRvQXNzaWduYWJsZUxpc3QgPSBmdW5jdGlvbiAoZXhwckxpc3QsIGlzQmluZGluZykge1xuICB2YXIgZW5kID0gZXhwckxpc3QubGVuZ3RoO1xuICBpZiAoZW5kKSB7XG4gICAgdmFyIGxhc3QgPSBleHByTGlzdFtlbmQgLSAxXTtcbiAgICBpZiAobGFzdCAmJiBsYXN0LnR5cGUgPT0gXCJSZXN0RWxlbWVudFwiKSB7XG4gICAgICAtLWVuZDtcbiAgICB9IGVsc2UgaWYgKGxhc3QgJiYgbGFzdC50eXBlID09IFwiU3ByZWFkRWxlbWVudFwiKSB7XG4gICAgICBsYXN0LnR5cGUgPSBcIlJlc3RFbGVtZW50XCI7XG4gICAgICB2YXIgYXJnID0gbGFzdC5hcmd1bWVudDtcbiAgICAgIHRoaXMudG9Bc3NpZ25hYmxlKGFyZywgaXNCaW5kaW5nKTtcbiAgICAgIGlmIChhcmcudHlwZSAhPT0gXCJJZGVudGlmaWVyXCIgJiYgYXJnLnR5cGUgIT09IFwiTWVtYmVyRXhwcmVzc2lvblwiICYmIGFyZy50eXBlICE9PSBcIkFycmF5UGF0dGVyblwiKSB0aGlzLnVuZXhwZWN0ZWQoYXJnLnN0YXJ0KTtcbiAgICAgIC0tZW5kO1xuICAgIH1cbiAgfVxuICBmb3IgKHZhciBpID0gMDsgaSA8IGVuZDsgaSsrKSB7XG4gICAgdmFyIGVsdCA9IGV4cHJMaXN0W2ldO1xuICAgIGlmIChlbHQpIHRoaXMudG9Bc3NpZ25hYmxlKGVsdCwgaXNCaW5kaW5nKTtcbiAgfVxuICByZXR1cm4gZXhwckxpc3Q7XG59O1xuXG4vLyBQYXJzZXMgc3ByZWFkIGVsZW1lbnQuXG5cbnBwLnBhcnNlU3ByZWFkID0gZnVuY3Rpb24gKHJlZlNob3J0aGFuZERlZmF1bHRQb3MpIHtcbiAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICB0aGlzLm5leHQoKTtcbiAgbm9kZS5hcmd1bWVudCA9IHRoaXMucGFyc2VNYXliZUFzc2lnbihyZWZTaG9ydGhhbmREZWZhdWx0UG9zKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIlNwcmVhZEVsZW1lbnRcIik7XG59O1xuXG5wcC5wYXJzZVJlc3QgPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgdGhpcy5uZXh0KCk7XG4gIG5vZGUuYXJndW1lbnQgPSB0aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMubmFtZSB8fCB0aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuYnJhY2tldEwgPyB0aGlzLnBhcnNlQmluZGluZ0F0b20oKSA6IHRoaXMudW5leHBlY3RlZCgpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiUmVzdEVsZW1lbnRcIik7XG59O1xuXG4vLyBQYXJzZXMgbHZhbHVlIChhc3NpZ25hYmxlKSBhdG9tLlxuXG5wcC5wYXJzZUJpbmRpbmdBdG9tID0gZnVuY3Rpb24gKCkge1xuICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uIDwgNikgcmV0dXJuIHRoaXMucGFyc2VJZGVudCgpO1xuICBzd2l0Y2ggKHRoaXMudHlwZSkge1xuICAgIGNhc2UgX3Rva2VudHlwZS50eXBlcy5uYW1lOlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VJZGVudCgpO1xuXG4gICAgY2FzZSBfdG9rZW50eXBlLnR5cGVzLmJyYWNrZXRMOlxuICAgICAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICBub2RlLmVsZW1lbnRzID0gdGhpcy5wYXJzZUJpbmRpbmdMaXN0KF90b2tlbnR5cGUudHlwZXMuYnJhY2tldFIsIHRydWUsIHRydWUpO1xuICAgICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkFycmF5UGF0dGVyblwiKTtcblxuICAgIGNhc2UgX3Rva2VudHlwZS50eXBlcy5icmFjZUw6XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZU9iaih0cnVlKTtcblxuICAgIGRlZmF1bHQ6XG4gICAgICB0aGlzLnVuZXhwZWN0ZWQoKTtcbiAgfVxufTtcblxucHAucGFyc2VCaW5kaW5nTGlzdCA9IGZ1bmN0aW9uIChjbG9zZSwgYWxsb3dFbXB0eSwgYWxsb3dUcmFpbGluZ0NvbW1hKSB7XG4gIHZhciBlbHRzID0gW10sXG4gICAgICBmaXJzdCA9IHRydWU7XG4gIHdoaWxlICghdGhpcy5lYXQoY2xvc2UpKSB7XG4gICAgaWYgKGZpcnN0KSBmaXJzdCA9IGZhbHNlO2Vsc2UgdGhpcy5leHBlY3QoX3Rva2VudHlwZS50eXBlcy5jb21tYSk7XG4gICAgaWYgKGFsbG93RW1wdHkgJiYgdGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLmNvbW1hKSB7XG4gICAgICBlbHRzLnB1c2gobnVsbCk7XG4gICAgfSBlbHNlIGlmIChhbGxvd1RyYWlsaW5nQ29tbWEgJiYgdGhpcy5hZnRlclRyYWlsaW5nQ29tbWEoY2xvc2UpKSB7XG4gICAgICBicmVhaztcbiAgICB9IGVsc2UgaWYgKHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5lbGxpcHNpcykge1xuICAgICAgdmFyIHJlc3QgPSB0aGlzLnBhcnNlUmVzdCgpO1xuICAgICAgdGhpcy5wYXJzZUJpbmRpbmdMaXN0SXRlbShyZXN0KTtcbiAgICAgIGVsdHMucHVzaChyZXN0KTtcbiAgICAgIHRoaXMuZXhwZWN0KGNsb3NlKTtcbiAgICAgIGJyZWFrO1xuICAgIH0gZWxzZSB7XG4gICAgICB2YXIgZWxlbSA9IHRoaXMucGFyc2VNYXliZURlZmF1bHQodGhpcy5zdGFydCwgdGhpcy5zdGFydExvYyk7XG4gICAgICB0aGlzLnBhcnNlQmluZGluZ0xpc3RJdGVtKGVsZW0pO1xuICAgICAgZWx0cy5wdXNoKGVsZW0pO1xuICAgIH1cbiAgfVxuICByZXR1cm4gZWx0cztcbn07XG5cbnBwLnBhcnNlQmluZGluZ0xpc3RJdGVtID0gZnVuY3Rpb24gKHBhcmFtKSB7XG4gIHJldHVybiBwYXJhbTtcbn07XG5cbi8vIFBhcnNlcyBhc3NpZ25tZW50IHBhdHRlcm4gYXJvdW5kIGdpdmVuIGF0b20gaWYgcG9zc2libGUuXG5cbnBwLnBhcnNlTWF5YmVEZWZhdWx0ID0gZnVuY3Rpb24gKHN0YXJ0UG9zLCBzdGFydExvYywgbGVmdCkge1xuICBsZWZ0ID0gbGVmdCB8fCB0aGlzLnBhcnNlQmluZGluZ0F0b20oKTtcbiAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA8IDYgfHwgIXRoaXMuZWF0KF90b2tlbnR5cGUudHlwZXMuZXEpKSByZXR1cm4gbGVmdDtcbiAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0UG9zLCBzdGFydExvYyk7XG4gIG5vZGUubGVmdCA9IGxlZnQ7XG4gIG5vZGUucmlnaHQgPSB0aGlzLnBhcnNlTWF5YmVBc3NpZ24oKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkFzc2lnbm1lbnRQYXR0ZXJuXCIpO1xufTtcblxuLy8gVmVyaWZ5IHRoYXQgYSBub2RlIGlzIGFuIGx2YWwg4oCUIHNvbWV0aGluZyB0aGF0IGNhbiBiZSBhc3NpZ25lZFxuLy8gdG8uXG5cbnBwLmNoZWNrTFZhbCA9IGZ1bmN0aW9uIChleHByLCBpc0JpbmRpbmcsIGNoZWNrQ2xhc2hlcykge1xuICBzd2l0Y2ggKGV4cHIudHlwZSkge1xuICAgIGNhc2UgXCJJZGVudGlmaWVyXCI6XG4gICAgICBpZiAodGhpcy5zdHJpY3QgJiYgKF9pZGVudGlmaWVyLnJlc2VydmVkV29yZHMuc3RyaWN0QmluZChleHByLm5hbWUpIHx8IF9pZGVudGlmaWVyLnJlc2VydmVkV29yZHMuc3RyaWN0KGV4cHIubmFtZSkpKSB0aGlzLnJhaXNlKGV4cHIuc3RhcnQsIChpc0JpbmRpbmcgPyBcIkJpbmRpbmcgXCIgOiBcIkFzc2lnbmluZyB0byBcIikgKyBleHByLm5hbWUgKyBcIiBpbiBzdHJpY3QgbW9kZVwiKTtcbiAgICAgIGlmIChjaGVja0NsYXNoZXMpIHtcbiAgICAgICAgaWYgKF91dGlsLmhhcyhjaGVja0NsYXNoZXMsIGV4cHIubmFtZSkpIHRoaXMucmFpc2UoZXhwci5zdGFydCwgXCJBcmd1bWVudCBuYW1lIGNsYXNoIGluIHN0cmljdCBtb2RlXCIpO1xuICAgICAgICBjaGVja0NsYXNoZXNbZXhwci5uYW1lXSA9IHRydWU7XG4gICAgICB9XG4gICAgICBicmVhaztcblxuICAgIGNhc2UgXCJNZW1iZXJFeHByZXNzaW9uXCI6XG4gICAgICBpZiAoaXNCaW5kaW5nKSB0aGlzLnJhaXNlKGV4cHIuc3RhcnQsIChpc0JpbmRpbmcgPyBcIkJpbmRpbmdcIiA6IFwiQXNzaWduaW5nIHRvXCIpICsgXCIgbWVtYmVyIGV4cHJlc3Npb25cIik7XG4gICAgICBicmVhaztcblxuICAgIGNhc2UgXCJPYmplY3RQYXR0ZXJuXCI6XG4gICAgICBmb3IgKHZhciBpID0gMDsgaSA8IGV4cHIucHJvcGVydGllcy5sZW5ndGg7IGkrKykge1xuICAgICAgICB0aGlzLmNoZWNrTFZhbChleHByLnByb3BlcnRpZXNbaV0udmFsdWUsIGlzQmluZGluZywgY2hlY2tDbGFzaGVzKTtcbiAgICAgIH1icmVhaztcblxuICAgIGNhc2UgXCJBcnJheVBhdHRlcm5cIjpcbiAgICAgIGZvciAodmFyIGkgPSAwOyBpIDwgZXhwci5lbGVtZW50cy5sZW5ndGg7IGkrKykge1xuICAgICAgICB2YXIgZWxlbSA9IGV4cHIuZWxlbWVudHNbaV07XG4gICAgICAgIGlmIChlbGVtKSB0aGlzLmNoZWNrTFZhbChlbGVtLCBpc0JpbmRpbmcsIGNoZWNrQ2xhc2hlcyk7XG4gICAgICB9XG4gICAgICBicmVhaztcblxuICAgIGNhc2UgXCJBc3NpZ25tZW50UGF0dGVyblwiOlxuICAgICAgdGhpcy5jaGVja0xWYWwoZXhwci5sZWZ0LCBpc0JpbmRpbmcsIGNoZWNrQ2xhc2hlcyk7XG4gICAgICBicmVhaztcblxuICAgIGNhc2UgXCJSZXN0RWxlbWVudFwiOlxuICAgICAgdGhpcy5jaGVja0xWYWwoZXhwci5hcmd1bWVudCwgaXNCaW5kaW5nLCBjaGVja0NsYXNoZXMpO1xuICAgICAgYnJlYWs7XG5cbiAgICBjYXNlIFwiUGFyZW50aGVzaXplZEV4cHJlc3Npb25cIjpcbiAgICAgIHRoaXMuY2hlY2tMVmFsKGV4cHIuZXhwcmVzc2lvbiwgaXNCaW5kaW5nLCBjaGVja0NsYXNoZXMpO1xuICAgICAgYnJlYWs7XG5cbiAgICBkZWZhdWx0OlxuICAgICAgdGhpcy5yYWlzZShleHByLnN0YXJ0LCAoaXNCaW5kaW5nID8gXCJCaW5kaW5nXCIgOiBcIkFzc2lnbmluZyB0b1wiKSArIFwiIHJ2YWx1ZVwiKTtcbiAgfVxufTtcblxufSx7XCIuL2lkZW50aWZpZXJcIjoyLFwiLi9zdGF0ZVwiOjEwLFwiLi90b2tlbnR5cGVcIjoxNCxcIi4vdXRpbFwiOjE1fV0sNzpbZnVuY3Rpb24oX2RlcmVxXyxtb2R1bGUsZXhwb3J0cyl7XG5cInVzZSBzdHJpY3RcIjtcblxuZXhwb3J0cy5fX2VzTW9kdWxlID0gdHJ1ZTtcblxuZnVuY3Rpb24gX2NsYXNzQ2FsbENoZWNrKGluc3RhbmNlLCBDb25zdHJ1Y3RvcikgeyBpZiAoIShpbnN0YW5jZSBpbnN0YW5jZW9mIENvbnN0cnVjdG9yKSkgeyB0aHJvdyBuZXcgVHlwZUVycm9yKFwiQ2Fubm90IGNhbGwgYSBjbGFzcyBhcyBhIGZ1bmN0aW9uXCIpOyB9IH1cblxudmFyIF9zdGF0ZSA9IF9kZXJlcV8oXCIuL3N0YXRlXCIpO1xuXG52YXIgX2xvY3V0aWwgPSBfZGVyZXFfKFwiLi9sb2N1dGlsXCIpO1xuXG52YXIgTm9kZSA9IGZ1bmN0aW9uIE5vZGUocGFyc2VyLCBwb3MsIGxvYykge1xuICBfY2xhc3NDYWxsQ2hlY2sodGhpcywgTm9kZSk7XG5cbiAgdGhpcy50eXBlID0gXCJcIjtcbiAgdGhpcy5zdGFydCA9IHBvcztcbiAgdGhpcy5lbmQgPSAwO1xuICBpZiAocGFyc2VyLm9wdGlvbnMubG9jYXRpb25zKSB0aGlzLmxvYyA9IG5ldyBfbG9jdXRpbC5Tb3VyY2VMb2NhdGlvbihwYXJzZXIsIGxvYyk7XG4gIGlmIChwYXJzZXIub3B0aW9ucy5kaXJlY3RTb3VyY2VGaWxlKSB0aGlzLnNvdXJjZUZpbGUgPSBwYXJzZXIub3B0aW9ucy5kaXJlY3RTb3VyY2VGaWxlO1xuICBpZiAocGFyc2VyLm9wdGlvbnMucmFuZ2VzKSB0aGlzLnJhbmdlID0gW3BvcywgMF07XG59O1xuXG5leHBvcnRzLk5vZGUgPSBOb2RlO1xuXG4vLyBTdGFydCBhbiBBU1Qgbm9kZSwgYXR0YWNoaW5nIGEgc3RhcnQgb2Zmc2V0LlxuXG52YXIgcHAgPSBfc3RhdGUuUGFyc2VyLnByb3RvdHlwZTtcblxucHAuc3RhcnROb2RlID0gZnVuY3Rpb24gKCkge1xuICByZXR1cm4gbmV3IE5vZGUodGhpcywgdGhpcy5zdGFydCwgdGhpcy5zdGFydExvYyk7XG59O1xuXG5wcC5zdGFydE5vZGVBdCA9IGZ1bmN0aW9uIChwb3MsIGxvYykge1xuICByZXR1cm4gbmV3IE5vZGUodGhpcywgcG9zLCBsb2MpO1xufTtcblxuLy8gRmluaXNoIGFuIEFTVCBub2RlLCBhZGRpbmcgYHR5cGVgIGFuZCBgZW5kYCBwcm9wZXJ0aWVzLlxuXG5mdW5jdGlvbiBmaW5pc2hOb2RlQXQobm9kZSwgdHlwZSwgcG9zLCBsb2MpIHtcbiAgbm9kZS50eXBlID0gdHlwZTtcbiAgbm9kZS5lbmQgPSBwb3M7XG4gIGlmICh0aGlzLm9wdGlvbnMubG9jYXRpb25zKSBub2RlLmxvYy5lbmQgPSBsb2M7XG4gIGlmICh0aGlzLm9wdGlvbnMucmFuZ2VzKSBub2RlLnJhbmdlWzFdID0gcG9zO1xuICByZXR1cm4gbm9kZTtcbn1cblxucHAuZmluaXNoTm9kZSA9IGZ1bmN0aW9uIChub2RlLCB0eXBlKSB7XG4gIHJldHVybiBmaW5pc2hOb2RlQXQuY2FsbCh0aGlzLCBub2RlLCB0eXBlLCB0aGlzLmxhc3RUb2tFbmQsIHRoaXMubGFzdFRva0VuZExvYyk7XG59O1xuXG4vLyBGaW5pc2ggbm9kZSBhdCBnaXZlbiBwb3NpdGlvblxuXG5wcC5maW5pc2hOb2RlQXQgPSBmdW5jdGlvbiAobm9kZSwgdHlwZSwgcG9zLCBsb2MpIHtcbiAgcmV0dXJuIGZpbmlzaE5vZGVBdC5jYWxsKHRoaXMsIG5vZGUsIHR5cGUsIHBvcywgbG9jKTtcbn07XG5cbn0se1wiLi9sb2N1dGlsXCI6NSxcIi4vc3RhdGVcIjoxMH1dLDg6W2Z1bmN0aW9uKF9kZXJlcV8sbW9kdWxlLGV4cG9ydHMpe1xuXCJ1c2Ugc3RyaWN0XCI7XG5cbmV4cG9ydHMuX19lc01vZHVsZSA9IHRydWU7XG5leHBvcnRzLmdldE9wdGlvbnMgPSBnZXRPcHRpb25zO1xuXG52YXIgX3V0aWwgPSBfZGVyZXFfKFwiLi91dGlsXCIpO1xuXG52YXIgX2xvY3V0aWwgPSBfZGVyZXFfKFwiLi9sb2N1dGlsXCIpO1xuXG4vLyBBIHNlY29uZCBvcHRpb25hbCBhcmd1bWVudCBjYW4gYmUgZ2l2ZW4gdG8gZnVydGhlciBjb25maWd1cmVcbi8vIHRoZSBwYXJzZXIgcHJvY2Vzcy4gVGhlc2Ugb3B0aW9ucyBhcmUgcmVjb2duaXplZDpcblxudmFyIGRlZmF1bHRPcHRpb25zID0ge1xuICAvLyBgZWNtYVZlcnNpb25gIGluZGljYXRlcyB0aGUgRUNNQVNjcmlwdCB2ZXJzaW9uIHRvIHBhcnNlLiBNdXN0XG4gIC8vIGJlIGVpdGhlciAzLCBvciA1LCBvciA2LiBUaGlzIGluZmx1ZW5jZXMgc3VwcG9ydCBmb3Igc3RyaWN0XG4gIC8vIG1vZGUsIHRoZSBzZXQgb2YgcmVzZXJ2ZWQgd29yZHMsIHN1cHBvcnQgZm9yIGdldHRlcnMgYW5kXG4gIC8vIHNldHRlcnMgYW5kIG90aGVyIGZlYXR1cmVzLlxuICBlY21hVmVyc2lvbjogNSxcbiAgLy8gU291cmNlIHR5cGUgKFwic2NyaXB0XCIgb3IgXCJtb2R1bGVcIikgZm9yIGRpZmZlcmVudCBzZW1hbnRpY3NcbiAgc291cmNlVHlwZTogXCJzY3JpcHRcIixcbiAgLy8gYG9uSW5zZXJ0ZWRTZW1pY29sb25gIGNhbiBiZSBhIGNhbGxiYWNrIHRoYXQgd2lsbCBiZSBjYWxsZWRcbiAgLy8gd2hlbiBhIHNlbWljb2xvbiBpcyBhdXRvbWF0aWNhbGx5IGluc2VydGVkLiBJdCB3aWxsIGJlIHBhc3NlZFxuICAvLyB0aCBwb3NpdGlvbiBvZiB0aGUgY29tbWEgYXMgYW4gb2Zmc2V0LCBhbmQgaWYgYGxvY2F0aW9uc2AgaXNcbiAgLy8gZW5hYmxlZCwgaXQgaXMgZ2l2ZW4gdGhlIGxvY2F0aW9uIGFzIGEgYHtsaW5lLCBjb2x1bW59YCBvYmplY3RcbiAgLy8gYXMgc2Vjb25kIGFyZ3VtZW50LlxuICBvbkluc2VydGVkU2VtaWNvbG9uOiBudWxsLFxuICAvLyBgb25UcmFpbGluZ0NvbW1hYCBpcyBzaW1pbGFyIHRvIGBvbkluc2VydGVkU2VtaWNvbG9uYCwgYnV0IGZvclxuICAvLyB0cmFpbGluZyBjb21tYXMuXG4gIG9uVHJhaWxpbmdDb21tYTogbnVsbCxcbiAgLy8gQnkgZGVmYXVsdCwgcmVzZXJ2ZWQgd29yZHMgYXJlIG5vdCBlbmZvcmNlZC4gRGlzYWJsZVxuICAvLyBgYWxsb3dSZXNlcnZlZGAgdG8gZW5mb3JjZSB0aGVtLiBXaGVuIHRoaXMgb3B0aW9uIGhhcyB0aGVcbiAgLy8gdmFsdWUgXCJuZXZlclwiLCByZXNlcnZlZCB3b3JkcyBhbmQga2V5d29yZHMgY2FuIGFsc28gbm90IGJlXG4gIC8vIHVzZWQgYXMgcHJvcGVydHkgbmFtZXMuXG4gIGFsbG93UmVzZXJ2ZWQ6IHRydWUsXG4gIC8vIFdoZW4gZW5hYmxlZCwgYSByZXR1cm4gYXQgdGhlIHRvcCBsZXZlbCBpcyBub3QgY29uc2lkZXJlZCBhblxuICAvLyBlcnJvci5cbiAgYWxsb3dSZXR1cm5PdXRzaWRlRnVuY3Rpb246IGZhbHNlLFxuICAvLyBXaGVuIGVuYWJsZWQsIGltcG9ydC9leHBvcnQgc3RhdGVtZW50cyBhcmUgbm90IGNvbnN0cmFpbmVkIHRvXG4gIC8vIGFwcGVhcmluZyBhdCB0aGUgdG9wIG9mIHRoZSBwcm9ncmFtLlxuICBhbGxvd0ltcG9ydEV4cG9ydEV2ZXJ5d2hlcmU6IGZhbHNlLFxuICAvLyBXaGVuIGVuYWJsZWQsIGhhc2hiYW5nIGRpcmVjdGl2ZSBpbiB0aGUgYmVnaW5uaW5nIG9mIGZpbGVcbiAgLy8gaXMgYWxsb3dlZCBhbmQgdHJlYXRlZCBhcyBhIGxpbmUgY29tbWVudC5cbiAgYWxsb3dIYXNoQmFuZzogZmFsc2UsXG4gIC8vIFdoZW4gYGxvY2F0aW9uc2AgaXMgb24sIGBsb2NgIHByb3BlcnRpZXMgaG9sZGluZyBvYmplY3RzIHdpdGhcbiAgLy8gYHN0YXJ0YCBhbmQgYGVuZGAgcHJvcGVydGllcyBpbiBge2xpbmUsIGNvbHVtbn1gIGZvcm0gKHdpdGhcbiAgLy8gbGluZSBiZWluZyAxLWJhc2VkIGFuZCBjb2x1bW4gMC1iYXNlZCkgd2lsbCBiZSBhdHRhY2hlZCB0byB0aGVcbiAgLy8gbm9kZXMuXG4gIGxvY2F0aW9uczogZmFsc2UsXG4gIC8vIEEgZnVuY3Rpb24gY2FuIGJlIHBhc3NlZCBhcyBgb25Ub2tlbmAgb3B0aW9uLCB3aGljaCB3aWxsXG4gIC8vIGNhdXNlIEFjb3JuIHRvIGNhbGwgdGhhdCBmdW5jdGlvbiB3aXRoIG9iamVjdCBpbiB0aGUgc2FtZVxuICAvLyBmb3JtYXQgYXMgdG9rZW5pemUoKSByZXR1cm5zLiBOb3RlIHRoYXQgeW91IGFyZSBub3RcbiAgLy8gYWxsb3dlZCB0byBjYWxsIHRoZSBwYXJzZXIgZnJvbSB0aGUgY2FsbGJhY2vigJR0aGF0IHdpbGxcbiAgLy8gY29ycnVwdCBpdHMgaW50ZXJuYWwgc3RhdGUuXG4gIG9uVG9rZW46IG51bGwsXG4gIC8vIEEgZnVuY3Rpb24gY2FuIGJlIHBhc3NlZCBhcyBgb25Db21tZW50YCBvcHRpb24sIHdoaWNoIHdpbGxcbiAgLy8gY2F1c2UgQWNvcm4gdG8gY2FsbCB0aGF0IGZ1bmN0aW9uIHdpdGggYChibG9jaywgdGV4dCwgc3RhcnQsXG4gIC8vIGVuZClgIHBhcmFtZXRlcnMgd2hlbmV2ZXIgYSBjb21tZW50IGlzIHNraXBwZWQuIGBibG9ja2AgaXMgYVxuICAvLyBib29sZWFuIGluZGljYXRpbmcgd2hldGhlciB0aGlzIGlzIGEgYmxvY2sgKGAvKiAqL2ApIGNvbW1lbnQsXG4gIC8vIGB0ZXh0YCBpcyB0aGUgY29udGVudCBvZiB0aGUgY29tbWVudCwgYW5kIGBzdGFydGAgYW5kIGBlbmRgIGFyZVxuICAvLyBjaGFyYWN0ZXIgb2Zmc2V0cyB0aGF0IGRlbm90ZSB0aGUgc3RhcnQgYW5kIGVuZCBvZiB0aGUgY29tbWVudC5cbiAgLy8gV2hlbiB0aGUgYGxvY2F0aW9uc2Agb3B0aW9uIGlzIG9uLCB0d28gbW9yZSBwYXJhbWV0ZXJzIGFyZVxuICAvLyBwYXNzZWQsIHRoZSBmdWxsIGB7bGluZSwgY29sdW1ufWAgbG9jYXRpb25zIG9mIHRoZSBzdGFydCBhbmRcbiAgLy8gZW5kIG9mIHRoZSBjb21tZW50cy4gTm90ZSB0aGF0IHlvdSBhcmUgbm90IGFsbG93ZWQgdG8gY2FsbCB0aGVcbiAgLy8gcGFyc2VyIGZyb20gdGhlIGNhbGxiYWNr4oCUdGhhdCB3aWxsIGNvcnJ1cHQgaXRzIGludGVybmFsIHN0YXRlLlxuICBvbkNvbW1lbnQ6IG51bGwsXG4gIC8vIE5vZGVzIGhhdmUgdGhlaXIgc3RhcnQgYW5kIGVuZCBjaGFyYWN0ZXJzIG9mZnNldHMgcmVjb3JkZWQgaW5cbiAgLy8gYHN0YXJ0YCBhbmQgYGVuZGAgcHJvcGVydGllcyAoZGlyZWN0bHkgb24gdGhlIG5vZGUsIHJhdGhlciB0aGFuXG4gIC8vIHRoZSBgbG9jYCBvYmplY3QsIHdoaWNoIGhvbGRzIGxpbmUvY29sdW1uIGRhdGEuIFRvIGFsc28gYWRkIGFcbiAgLy8gW3NlbWktc3RhbmRhcmRpemVkXVtyYW5nZV0gYHJhbmdlYCBwcm9wZXJ0eSBob2xkaW5nIGEgYFtzdGFydCxcbiAgLy8gZW5kXWAgYXJyYXkgd2l0aCB0aGUgc2FtZSBudW1iZXJzLCBzZXQgdGhlIGByYW5nZXNgIG9wdGlvbiB0b1xuICAvLyBgdHJ1ZWAuXG4gIC8vXG4gIC8vIFtyYW5nZV06IGh0dHBzOi8vYnVnemlsbGEubW96aWxsYS5vcmcvc2hvd19idWcuY2dpP2lkPTc0NTY3OFxuICByYW5nZXM6IGZhbHNlLFxuICAvLyBJdCBpcyBwb3NzaWJsZSB0byBwYXJzZSBtdWx0aXBsZSBmaWxlcyBpbnRvIGEgc2luZ2xlIEFTVCBieVxuICAvLyBwYXNzaW5nIHRoZSB0cmVlIHByb2R1Y2VkIGJ5IHBhcnNpbmcgdGhlIGZpcnN0IGZpbGUgYXNcbiAgLy8gYHByb2dyYW1gIG9wdGlvbiBpbiBzdWJzZXF1ZW50IHBhcnNlcy4gVGhpcyB3aWxsIGFkZCB0aGVcbiAgLy8gdG9wbGV2ZWwgZm9ybXMgb2YgdGhlIHBhcnNlZCBmaWxlIHRvIHRoZSBgUHJvZ3JhbWAgKHRvcCkgbm9kZVxuICAvLyBvZiBhbiBleGlzdGluZyBwYXJzZSB0cmVlLlxuICBwcm9ncmFtOiBudWxsLFxuICAvLyBXaGVuIGBsb2NhdGlvbnNgIGlzIG9uLCB5b3UgY2FuIHBhc3MgdGhpcyB0byByZWNvcmQgdGhlIHNvdXJjZVxuICAvLyBmaWxlIGluIGV2ZXJ5IG5vZGUncyBgbG9jYCBvYmplY3QuXG4gIHNvdXJjZUZpbGU6IG51bGwsXG4gIC8vIFRoaXMgdmFsdWUsIGlmIGdpdmVuLCBpcyBzdG9yZWQgaW4gZXZlcnkgbm9kZSwgd2hldGhlclxuICAvLyBgbG9jYXRpb25zYCBpcyBvbiBvciBvZmYuXG4gIGRpcmVjdFNvdXJjZUZpbGU6IG51bGwsXG4gIC8vIFdoZW4gZW5hYmxlZCwgcGFyZW50aGVzaXplZCBleHByZXNzaW9ucyBhcmUgcmVwcmVzZW50ZWQgYnlcbiAgLy8gKG5vbi1zdGFuZGFyZCkgUGFyZW50aGVzaXplZEV4cHJlc3Npb24gbm9kZXNcbiAgcHJlc2VydmVQYXJlbnM6IGZhbHNlLFxuICBwbHVnaW5zOiB7fVxufTtcblxuZXhwb3J0cy5kZWZhdWx0T3B0aW9ucyA9IGRlZmF1bHRPcHRpb25zO1xuLy8gSW50ZXJwcmV0IGFuZCBkZWZhdWx0IGFuIG9wdGlvbnMgb2JqZWN0XG5cbmZ1bmN0aW9uIGdldE9wdGlvbnMob3B0cykge1xuICB2YXIgb3B0aW9ucyA9IHt9O1xuICBmb3IgKHZhciBvcHQgaW4gZGVmYXVsdE9wdGlvbnMpIHtcbiAgICBvcHRpb25zW29wdF0gPSBvcHRzICYmIF91dGlsLmhhcyhvcHRzLCBvcHQpID8gb3B0c1tvcHRdIDogZGVmYXVsdE9wdGlvbnNbb3B0XTtcbiAgfWlmIChfdXRpbC5pc0FycmF5KG9wdGlvbnMub25Ub2tlbikpIHtcbiAgICAoZnVuY3Rpb24gKCkge1xuICAgICAgdmFyIHRva2VucyA9IG9wdGlvbnMub25Ub2tlbjtcbiAgICAgIG9wdGlvbnMub25Ub2tlbiA9IGZ1bmN0aW9uICh0b2tlbikge1xuICAgICAgICByZXR1cm4gdG9rZW5zLnB1c2godG9rZW4pO1xuICAgICAgfTtcbiAgICB9KSgpO1xuICB9XG4gIGlmIChfdXRpbC5pc0FycmF5KG9wdGlvbnMub25Db21tZW50KSkgb3B0aW9ucy5vbkNvbW1lbnQgPSBwdXNoQ29tbWVudChvcHRpb25zLCBvcHRpb25zLm9uQ29tbWVudCk7XG5cbiAgcmV0dXJuIG9wdGlvbnM7XG59XG5cbmZ1bmN0aW9uIHB1c2hDb21tZW50KG9wdGlvbnMsIGFycmF5KSB7XG4gIHJldHVybiBmdW5jdGlvbiAoYmxvY2ssIHRleHQsIHN0YXJ0LCBlbmQsIHN0YXJ0TG9jLCBlbmRMb2MpIHtcbiAgICB2YXIgY29tbWVudCA9IHtcbiAgICAgIHR5cGU6IGJsb2NrID8gXCJCbG9ja1wiIDogXCJMaW5lXCIsXG4gICAgICB2YWx1ZTogdGV4dCxcbiAgICAgIHN0YXJ0OiBzdGFydCxcbiAgICAgIGVuZDogZW5kXG4gICAgfTtcbiAgICBpZiAob3B0aW9ucy5sb2NhdGlvbnMpIGNvbW1lbnQubG9jID0gbmV3IF9sb2N1dGlsLlNvdXJjZUxvY2F0aW9uKHRoaXMsIHN0YXJ0TG9jLCBlbmRMb2MpO1xuICAgIGlmIChvcHRpb25zLnJhbmdlcykgY29tbWVudC5yYW5nZSA9IFtzdGFydCwgZW5kXTtcbiAgICBhcnJheS5wdXNoKGNvbW1lbnQpO1xuICB9O1xufVxuXG59LHtcIi4vbG9jdXRpbFwiOjUsXCIuL3V0aWxcIjoxNX1dLDk6W2Z1bmN0aW9uKF9kZXJlcV8sbW9kdWxlLGV4cG9ydHMpe1xuXCJ1c2Ugc3RyaWN0XCI7XG5cbnZhciBfdG9rZW50eXBlID0gX2RlcmVxXyhcIi4vdG9rZW50eXBlXCIpO1xuXG52YXIgX3N0YXRlID0gX2RlcmVxXyhcIi4vc3RhdGVcIik7XG5cbnZhciBfd2hpdGVzcGFjZSA9IF9kZXJlcV8oXCIuL3doaXRlc3BhY2VcIik7XG5cbnZhciBwcCA9IF9zdGF0ZS5QYXJzZXIucHJvdG90eXBlO1xuXG4vLyAjIyBQYXJzZXIgdXRpbGl0aWVzXG5cbi8vIFRlc3Qgd2hldGhlciBhIHN0YXRlbWVudCBub2RlIGlzIHRoZSBzdHJpbmcgbGl0ZXJhbCBgXCJ1c2Ugc3RyaWN0XCJgLlxuXG5wcC5pc1VzZVN0cmljdCA9IGZ1bmN0aW9uIChzdG10KSB7XG4gIHJldHVybiB0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNSAmJiBzdG10LnR5cGUgPT09IFwiRXhwcmVzc2lvblN0YXRlbWVudFwiICYmIHN0bXQuZXhwcmVzc2lvbi50eXBlID09PSBcIkxpdGVyYWxcIiAmJiBzdG10LmV4cHJlc3Npb24ucmF3LnNsaWNlKDEsIC0xKSA9PT0gXCJ1c2Ugc3RyaWN0XCI7XG59O1xuXG4vLyBQcmVkaWNhdGUgdGhhdCB0ZXN0cyB3aGV0aGVyIHRoZSBuZXh0IHRva2VuIGlzIG9mIHRoZSBnaXZlblxuLy8gdHlwZSwgYW5kIGlmIHllcywgY29uc3VtZXMgaXQgYXMgYSBzaWRlIGVmZmVjdC5cblxucHAuZWF0ID0gZnVuY3Rpb24gKHR5cGUpIHtcbiAgaWYgKHRoaXMudHlwZSA9PT0gdHlwZSkge1xuICAgIHRoaXMubmV4dCgpO1xuICAgIHJldHVybiB0cnVlO1xuICB9IGVsc2Uge1xuICAgIHJldHVybiBmYWxzZTtcbiAgfVxufTtcblxuLy8gVGVzdHMgd2hldGhlciBwYXJzZWQgdG9rZW4gaXMgYSBjb250ZXh0dWFsIGtleXdvcmQuXG5cbnBwLmlzQ29udGV4dHVhbCA9IGZ1bmN0aW9uIChuYW1lKSB7XG4gIHJldHVybiB0aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMubmFtZSAmJiB0aGlzLnZhbHVlID09PSBuYW1lO1xufTtcblxuLy8gQ29uc3VtZXMgY29udGV4dHVhbCBrZXl3b3JkIGlmIHBvc3NpYmxlLlxuXG5wcC5lYXRDb250ZXh0dWFsID0gZnVuY3Rpb24gKG5hbWUpIHtcbiAgcmV0dXJuIHRoaXMudmFsdWUgPT09IG5hbWUgJiYgdGhpcy5lYXQoX3Rva2VudHlwZS50eXBlcy5uYW1lKTtcbn07XG5cbi8vIEFzc2VydHMgdGhhdCBmb2xsb3dpbmcgdG9rZW4gaXMgZ2l2ZW4gY29udGV4dHVhbCBrZXl3b3JkLlxuXG5wcC5leHBlY3RDb250ZXh0dWFsID0gZnVuY3Rpb24gKG5hbWUpIHtcbiAgaWYgKCF0aGlzLmVhdENvbnRleHR1YWwobmFtZSkpIHRoaXMudW5leHBlY3RlZCgpO1xufTtcblxuLy8gVGVzdCB3aGV0aGVyIGEgc2VtaWNvbG9uIGNhbiBiZSBpbnNlcnRlZCBhdCB0aGUgY3VycmVudCBwb3NpdGlvbi5cblxucHAuY2FuSW5zZXJ0U2VtaWNvbG9uID0gZnVuY3Rpb24gKCkge1xuICByZXR1cm4gdGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLmVvZiB8fCB0aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuYnJhY2VSIHx8IF93aGl0ZXNwYWNlLmxpbmVCcmVhay50ZXN0KHRoaXMuaW5wdXQuc2xpY2UodGhpcy5sYXN0VG9rRW5kLCB0aGlzLnN0YXJ0KSk7XG59O1xuXG5wcC5pbnNlcnRTZW1pY29sb24gPSBmdW5jdGlvbiAoKSB7XG4gIGlmICh0aGlzLmNhbkluc2VydFNlbWljb2xvbigpKSB7XG4gICAgaWYgKHRoaXMub3B0aW9ucy5vbkluc2VydGVkU2VtaWNvbG9uKSB0aGlzLm9wdGlvbnMub25JbnNlcnRlZFNlbWljb2xvbih0aGlzLmxhc3RUb2tFbmQsIHRoaXMubGFzdFRva0VuZExvYyk7XG4gICAgcmV0dXJuIHRydWU7XG4gIH1cbn07XG5cbi8vIENvbnN1bWUgYSBzZW1pY29sb24sIG9yLCBmYWlsaW5nIHRoYXQsIHNlZSBpZiB3ZSBhcmUgYWxsb3dlZCB0b1xuLy8gcHJldGVuZCB0aGF0IHRoZXJlIGlzIGEgc2VtaWNvbG9uIGF0IHRoaXMgcG9zaXRpb24uXG5cbnBwLnNlbWljb2xvbiA9IGZ1bmN0aW9uICgpIHtcbiAgaWYgKCF0aGlzLmVhdChfdG9rZW50eXBlLnR5cGVzLnNlbWkpICYmICF0aGlzLmluc2VydFNlbWljb2xvbigpKSB0aGlzLnVuZXhwZWN0ZWQoKTtcbn07XG5cbnBwLmFmdGVyVHJhaWxpbmdDb21tYSA9IGZ1bmN0aW9uICh0b2tUeXBlKSB7XG4gIGlmICh0aGlzLnR5cGUgPT0gdG9rVHlwZSkge1xuICAgIGlmICh0aGlzLm9wdGlvbnMub25UcmFpbGluZ0NvbW1hKSB0aGlzLm9wdGlvbnMub25UcmFpbGluZ0NvbW1hKHRoaXMubGFzdFRva1N0YXJ0LCB0aGlzLmxhc3RUb2tTdGFydExvYyk7XG4gICAgdGhpcy5uZXh0KCk7XG4gICAgcmV0dXJuIHRydWU7XG4gIH1cbn07XG5cbi8vIEV4cGVjdCBhIHRva2VuIG9mIGEgZ2l2ZW4gdHlwZS4gSWYgZm91bmQsIGNvbnN1bWUgaXQsIG90aGVyd2lzZSxcbi8vIHJhaXNlIGFuIHVuZXhwZWN0ZWQgdG9rZW4gZXJyb3IuXG5cbnBwLmV4cGVjdCA9IGZ1bmN0aW9uICh0eXBlKSB7XG4gIHRoaXMuZWF0KHR5cGUpIHx8IHRoaXMudW5leHBlY3RlZCgpO1xufTtcblxuLy8gUmFpc2UgYW4gdW5leHBlY3RlZCB0b2tlbiBlcnJvci5cblxucHAudW5leHBlY3RlZCA9IGZ1bmN0aW9uIChwb3MpIHtcbiAgdGhpcy5yYWlzZShwb3MgIT0gbnVsbCA/IHBvcyA6IHRoaXMuc3RhcnQsIFwiVW5leHBlY3RlZCB0b2tlblwiKTtcbn07XG5cbn0se1wiLi9zdGF0ZVwiOjEwLFwiLi90b2tlbnR5cGVcIjoxNCxcIi4vd2hpdGVzcGFjZVwiOjE2fV0sMTA6W2Z1bmN0aW9uKF9kZXJlcV8sbW9kdWxlLGV4cG9ydHMpe1xuXCJ1c2Ugc3RyaWN0XCI7XG5cbmV4cG9ydHMuX19lc01vZHVsZSA9IHRydWU7XG5cbmZ1bmN0aW9uIF9jbGFzc0NhbGxDaGVjayhpbnN0YW5jZSwgQ29uc3RydWN0b3IpIHsgaWYgKCEoaW5zdGFuY2UgaW5zdGFuY2VvZiBDb25zdHJ1Y3RvcikpIHsgdGhyb3cgbmV3IFR5cGVFcnJvcihcIkNhbm5vdCBjYWxsIGEgY2xhc3MgYXMgYSBmdW5jdGlvblwiKTsgfSB9XG5cbnZhciBfaWRlbnRpZmllciA9IF9kZXJlcV8oXCIuL2lkZW50aWZpZXJcIik7XG5cbnZhciBfdG9rZW50eXBlID0gX2RlcmVxXyhcIi4vdG9rZW50eXBlXCIpO1xuXG52YXIgX3doaXRlc3BhY2UgPSBfZGVyZXFfKFwiLi93aGl0ZXNwYWNlXCIpO1xuXG52YXIgX29wdGlvbnMgPSBfZGVyZXFfKFwiLi9vcHRpb25zXCIpO1xuXG4vLyBSZWdpc3RlcmVkIHBsdWdpbnNcbnZhciBwbHVnaW5zID0ge307XG5cbmV4cG9ydHMucGx1Z2lucyA9IHBsdWdpbnM7XG5cbnZhciBQYXJzZXIgPSAoZnVuY3Rpb24gKCkge1xuICBmdW5jdGlvbiBQYXJzZXIob3B0aW9ucywgaW5wdXQsIHN0YXJ0UG9zKSB7XG4gICAgX2NsYXNzQ2FsbENoZWNrKHRoaXMsIFBhcnNlcik7XG5cbiAgICB0aGlzLm9wdGlvbnMgPSBfb3B0aW9ucy5nZXRPcHRpb25zKG9wdGlvbnMpO1xuICAgIHRoaXMuc291cmNlRmlsZSA9IHRoaXMub3B0aW9ucy5zb3VyY2VGaWxlO1xuICAgIHRoaXMuaXNLZXl3b3JkID0gX2lkZW50aWZpZXIua2V5d29yZHNbdGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYgPyA2IDogNV07XG4gICAgdGhpcy5pc1Jlc2VydmVkV29yZCA9IF9pZGVudGlmaWVyLnJlc2VydmVkV29yZHNbdGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uXTtcbiAgICB0aGlzLmlucHV0ID0gU3RyaW5nKGlucHV0KTtcblxuICAgIC8vIFVzZWQgdG8gc2lnbmFsIHRvIGNhbGxlcnMgb2YgYHJlYWRXb3JkMWAgd2hldGhlciB0aGUgd29yZFxuICAgIC8vIGNvbnRhaW5lZCBhbnkgZXNjYXBlIHNlcXVlbmNlcy4gVGhpcyBpcyBuZWVkZWQgYmVjYXVzZSB3b3JkcyB3aXRoXG4gICAgLy8gZXNjYXBlIHNlcXVlbmNlcyBtdXN0IG5vdCBiZSBpbnRlcnByZXRlZCBhcyBrZXl3b3Jkcy5cbiAgICB0aGlzLmNvbnRhaW5zRXNjID0gZmFsc2U7XG5cbiAgICAvLyBMb2FkIHBsdWdpbnNcbiAgICB0aGlzLmxvYWRQbHVnaW5zKHRoaXMub3B0aW9ucy5wbHVnaW5zKTtcblxuICAgIC8vIFNldCB1cCB0b2tlbiBzdGF0ZVxuXG4gICAgLy8gVGhlIGN1cnJlbnQgcG9zaXRpb24gb2YgdGhlIHRva2VuaXplciBpbiB0aGUgaW5wdXQuXG4gICAgaWYgKHN0YXJ0UG9zKSB7XG4gICAgICB0aGlzLnBvcyA9IHN0YXJ0UG9zO1xuICAgICAgdGhpcy5saW5lU3RhcnQgPSBNYXRoLm1heCgwLCB0aGlzLmlucHV0Lmxhc3RJbmRleE9mKFwiXFxuXCIsIHN0YXJ0UG9zKSk7XG4gICAgICB0aGlzLmN1ckxpbmUgPSB0aGlzLmlucHV0LnNsaWNlKDAsIHRoaXMubGluZVN0YXJ0KS5zcGxpdChfd2hpdGVzcGFjZS5saW5lQnJlYWspLmxlbmd0aDtcbiAgICB9IGVsc2Uge1xuICAgICAgdGhpcy5wb3MgPSB0aGlzLmxpbmVTdGFydCA9IDA7XG4gICAgICB0aGlzLmN1ckxpbmUgPSAxO1xuICAgIH1cblxuICAgIC8vIFByb3BlcnRpZXMgb2YgdGhlIGN1cnJlbnQgdG9rZW46XG4gICAgLy8gSXRzIHR5cGVcbiAgICB0aGlzLnR5cGUgPSBfdG9rZW50eXBlLnR5cGVzLmVvZjtcbiAgICAvLyBGb3IgdG9rZW5zIHRoYXQgaW5jbHVkZSBtb3JlIGluZm9ybWF0aW9uIHRoYW4gdGhlaXIgdHlwZSwgdGhlIHZhbHVlXG4gICAgdGhpcy52YWx1ZSA9IG51bGw7XG4gICAgLy8gSXRzIHN0YXJ0IGFuZCBlbmQgb2Zmc2V0XG4gICAgdGhpcy5zdGFydCA9IHRoaXMuZW5kID0gdGhpcy5wb3M7XG4gICAgLy8gQW5kLCBpZiBsb2NhdGlvbnMgYXJlIHVzZWQsIHRoZSB7bGluZSwgY29sdW1ufSBvYmplY3RcbiAgICAvLyBjb3JyZXNwb25kaW5nIHRvIHRob3NlIG9mZnNldHNcbiAgICB0aGlzLnN0YXJ0TG9jID0gdGhpcy5lbmRMb2MgPSB0aGlzLmN1clBvc2l0aW9uKCk7XG5cbiAgICAvLyBQb3NpdGlvbiBpbmZvcm1hdGlvbiBmb3IgdGhlIHByZXZpb3VzIHRva2VuXG4gICAgdGhpcy5sYXN0VG9rRW5kTG9jID0gdGhpcy5sYXN0VG9rU3RhcnRMb2MgPSBudWxsO1xuICAgIHRoaXMubGFzdFRva1N0YXJ0ID0gdGhpcy5sYXN0VG9rRW5kID0gdGhpcy5wb3M7XG5cbiAgICAvLyBUaGUgY29udGV4dCBzdGFjayBpcyB1c2VkIHRvIHN1cGVyZmljaWFsbHkgdHJhY2sgc3ludGFjdGljXG4gICAgLy8gY29udGV4dCB0byBwcmVkaWN0IHdoZXRoZXIgYSByZWd1bGFyIGV4cHJlc3Npb24gaXMgYWxsb3dlZCBpbiBhXG4gICAgLy8gZ2l2ZW4gcG9zaXRpb24uXG4gICAgdGhpcy5jb250ZXh0ID0gdGhpcy5pbml0aWFsQ29udGV4dCgpO1xuICAgIHRoaXMuZXhwckFsbG93ZWQgPSB0cnVlO1xuXG4gICAgLy8gRmlndXJlIG91dCBpZiBpdCdzIGEgbW9kdWxlIGNvZGUuXG4gICAgdGhpcy5zdHJpY3QgPSB0aGlzLmluTW9kdWxlID0gdGhpcy5vcHRpb25zLnNvdXJjZVR5cGUgPT09IFwibW9kdWxlXCI7XG5cbiAgICAvLyBVc2VkIHRvIHNpZ25pZnkgdGhlIHN0YXJ0IG9mIGEgcG90ZW50aWFsIGFycm93IGZ1bmN0aW9uXG4gICAgdGhpcy5wb3RlbnRpYWxBcnJvd0F0ID0gLTE7XG5cbiAgICAvLyBGbGFncyB0byB0cmFjayB3aGV0aGVyIHdlIGFyZSBpbiBhIGZ1bmN0aW9uLCBhIGdlbmVyYXRvci5cbiAgICB0aGlzLmluRnVuY3Rpb24gPSB0aGlzLmluR2VuZXJhdG9yID0gZmFsc2U7XG4gICAgLy8gTGFiZWxzIGluIHNjb3BlLlxuICAgIHRoaXMubGFiZWxzID0gW107XG5cbiAgICAvLyBJZiBlbmFibGVkLCBza2lwIGxlYWRpbmcgaGFzaGJhbmcgbGluZS5cbiAgICBpZiAodGhpcy5wb3MgPT09IDAgJiYgdGhpcy5vcHRpb25zLmFsbG93SGFzaEJhbmcgJiYgdGhpcy5pbnB1dC5zbGljZSgwLCAyKSA9PT0gXCIjIVwiKSB0aGlzLnNraXBMaW5lQ29tbWVudCgyKTtcbiAgfVxuXG4gIFBhcnNlci5wcm90b3R5cGUuZXh0ZW5kID0gZnVuY3Rpb24gZXh0ZW5kKG5hbWUsIGYpIHtcbiAgICB0aGlzW25hbWVdID0gZih0aGlzW25hbWVdKTtcbiAgfTtcblxuICBQYXJzZXIucHJvdG90eXBlLmxvYWRQbHVnaW5zID0gZnVuY3Rpb24gbG9hZFBsdWdpbnMocGx1Z2luQ29uZmlncykge1xuICAgIGZvciAodmFyIF9uYW1lIGluIHBsdWdpbkNvbmZpZ3MpIHtcbiAgICAgIHZhciBwbHVnaW4gPSBwbHVnaW5zW19uYW1lXTtcbiAgICAgIGlmICghcGx1Z2luKSB0aHJvdyBuZXcgRXJyb3IoXCJQbHVnaW4gJ1wiICsgX25hbWUgKyBcIicgbm90IGZvdW5kXCIpO1xuICAgICAgcGx1Z2luKHRoaXMsIHBsdWdpbkNvbmZpZ3NbX25hbWVdKTtcbiAgICB9XG4gIH07XG5cbiAgUGFyc2VyLnByb3RvdHlwZS5wYXJzZSA9IGZ1bmN0aW9uIHBhcnNlKCkge1xuICAgIHZhciBub2RlID0gdGhpcy5vcHRpb25zLnByb2dyYW0gfHwgdGhpcy5zdGFydE5vZGUoKTtcbiAgICB0aGlzLm5leHRUb2tlbigpO1xuICAgIHJldHVybiB0aGlzLnBhcnNlVG9wTGV2ZWwobm9kZSk7XG4gIH07XG5cbiAgcmV0dXJuIFBhcnNlcjtcbn0pKCk7XG5cbmV4cG9ydHMuUGFyc2VyID0gUGFyc2VyO1xuXG59LHtcIi4vaWRlbnRpZmllclwiOjIsXCIuL29wdGlvbnNcIjo4LFwiLi90b2tlbnR5cGVcIjoxNCxcIi4vd2hpdGVzcGFjZVwiOjE2fV0sMTE6W2Z1bmN0aW9uKF9kZXJlcV8sbW9kdWxlLGV4cG9ydHMpe1xuXCJ1c2Ugc3RyaWN0XCI7XG5cbnZhciBfdG9rZW50eXBlID0gX2RlcmVxXyhcIi4vdG9rZW50eXBlXCIpO1xuXG52YXIgX3N0YXRlID0gX2RlcmVxXyhcIi4vc3RhdGVcIik7XG5cbnZhciBfd2hpdGVzcGFjZSA9IF9kZXJlcV8oXCIuL3doaXRlc3BhY2VcIik7XG5cbnZhciBwcCA9IF9zdGF0ZS5QYXJzZXIucHJvdG90eXBlO1xuXG4vLyAjIyMgU3RhdGVtZW50IHBhcnNpbmdcblxuLy8gUGFyc2UgYSBwcm9ncmFtLiBJbml0aWFsaXplcyB0aGUgcGFyc2VyLCByZWFkcyBhbnkgbnVtYmVyIG9mXG4vLyBzdGF0ZW1lbnRzLCBhbmQgd3JhcHMgdGhlbSBpbiBhIFByb2dyYW0gbm9kZS4gIE9wdGlvbmFsbHkgdGFrZXMgYVxuLy8gYHByb2dyYW1gIGFyZ3VtZW50LiAgSWYgcHJlc2VudCwgdGhlIHN0YXRlbWVudHMgd2lsbCBiZSBhcHBlbmRlZFxuLy8gdG8gaXRzIGJvZHkgaW5zdGVhZCBvZiBjcmVhdGluZyBhIG5ldyBub2RlLlxuXG5wcC5wYXJzZVRvcExldmVsID0gZnVuY3Rpb24gKG5vZGUpIHtcbiAgdmFyIGZpcnN0ID0gdHJ1ZTtcbiAgaWYgKCFub2RlLmJvZHkpIG5vZGUuYm9keSA9IFtdO1xuICB3aGlsZSAodGhpcy50eXBlICE9PSBfdG9rZW50eXBlLnR5cGVzLmVvZikge1xuICAgIHZhciBzdG10ID0gdGhpcy5wYXJzZVN0YXRlbWVudCh0cnVlLCB0cnVlKTtcbiAgICBub2RlLmJvZHkucHVzaChzdG10KTtcbiAgICBpZiAoZmlyc3QpIHtcbiAgICAgIGlmICh0aGlzLmlzVXNlU3RyaWN0KHN0bXQpKSB0aGlzLnNldFN0cmljdCh0cnVlKTtcbiAgICAgIGZpcnN0ID0gZmFsc2U7XG4gICAgfVxuICB9XG4gIHRoaXMubmV4dCgpO1xuICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYpIHtcbiAgICBub2RlLnNvdXJjZVR5cGUgPSB0aGlzLm9wdGlvbnMuc291cmNlVHlwZTtcbiAgfVxuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiUHJvZ3JhbVwiKTtcbn07XG5cbnZhciBsb29wTGFiZWwgPSB7IGtpbmQ6IFwibG9vcFwiIH0sXG4gICAgc3dpdGNoTGFiZWwgPSB7IGtpbmQ6IFwic3dpdGNoXCIgfTtcblxuLy8gUGFyc2UgYSBzaW5nbGUgc3RhdGVtZW50LlxuLy9cbi8vIElmIGV4cGVjdGluZyBhIHN0YXRlbWVudCBhbmQgZmluZGluZyBhIHNsYXNoIG9wZXJhdG9yLCBwYXJzZSBhXG4vLyByZWd1bGFyIGV4cHJlc3Npb24gbGl0ZXJhbC4gVGhpcyBpcyB0byBoYW5kbGUgY2FzZXMgbGlrZVxuLy8gYGlmIChmb28pIC9ibGFoLy5leGVjKGZvbylgLCB3aGVyZSBsb29raW5nIGF0IHRoZSBwcmV2aW91cyB0b2tlblxuLy8gZG9lcyBub3QgaGVscC5cblxucHAucGFyc2VTdGF0ZW1lbnQgPSBmdW5jdGlvbiAoZGVjbGFyYXRpb24sIHRvcExldmVsKSB7XG4gIHZhciBzdGFydHR5cGUgPSB0aGlzLnR5cGUsXG4gICAgICBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcblxuICAvLyBNb3N0IHR5cGVzIG9mIHN0YXRlbWVudHMgYXJlIHJlY29nbml6ZWQgYnkgdGhlIGtleXdvcmQgdGhleVxuICAvLyBzdGFydCB3aXRoLiBNYW55IGFyZSB0cml2aWFsIHRvIHBhcnNlLCBzb21lIHJlcXVpcmUgYSBiaXQgb2ZcbiAgLy8gY29tcGxleGl0eS5cblxuICBzd2l0Y2ggKHN0YXJ0dHlwZSkge1xuICAgIGNhc2UgX3Rva2VudHlwZS50eXBlcy5fYnJlYWs6Y2FzZSBfdG9rZW50eXBlLnR5cGVzLl9jb250aW51ZTpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlQnJlYWtDb250aW51ZVN0YXRlbWVudChub2RlLCBzdGFydHR5cGUua2V5d29yZCk7XG4gICAgY2FzZSBfdG9rZW50eXBlLnR5cGVzLl9kZWJ1Z2dlcjpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlRGVidWdnZXJTdGF0ZW1lbnQobm9kZSk7XG4gICAgY2FzZSBfdG9rZW50eXBlLnR5cGVzLl9kbzpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlRG9TdGF0ZW1lbnQobm9kZSk7XG4gICAgY2FzZSBfdG9rZW50eXBlLnR5cGVzLl9mb3I6XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZUZvclN0YXRlbWVudChub2RlKTtcbiAgICBjYXNlIF90b2tlbnR5cGUudHlwZXMuX2Z1bmN0aW9uOlxuICAgICAgaWYgKCFkZWNsYXJhdGlvbiAmJiB0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNikgdGhpcy51bmV4cGVjdGVkKCk7XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZUZ1bmN0aW9uU3RhdGVtZW50KG5vZGUpO1xuICAgIGNhc2UgX3Rva2VudHlwZS50eXBlcy5fY2xhc3M6XG4gICAgICBpZiAoIWRlY2xhcmF0aW9uKSB0aGlzLnVuZXhwZWN0ZWQoKTtcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlQ2xhc3Mobm9kZSwgdHJ1ZSk7XG4gICAgY2FzZSBfdG9rZW50eXBlLnR5cGVzLl9pZjpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlSWZTdGF0ZW1lbnQobm9kZSk7XG4gICAgY2FzZSBfdG9rZW50eXBlLnR5cGVzLl9yZXR1cm46XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZVJldHVyblN0YXRlbWVudChub2RlKTtcbiAgICBjYXNlIF90b2tlbnR5cGUudHlwZXMuX3N3aXRjaDpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlU3dpdGNoU3RhdGVtZW50KG5vZGUpO1xuICAgIGNhc2UgX3Rva2VudHlwZS50eXBlcy5fdGhyb3c6XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZVRocm93U3RhdGVtZW50KG5vZGUpO1xuICAgIGNhc2UgX3Rva2VudHlwZS50eXBlcy5fdHJ5OlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VUcnlTdGF0ZW1lbnQobm9kZSk7XG4gICAgY2FzZSBfdG9rZW50eXBlLnR5cGVzLl9sZXQ6Y2FzZSBfdG9rZW50eXBlLnR5cGVzLl9jb25zdDpcbiAgICAgIGlmICghZGVjbGFyYXRpb24pIHRoaXMudW5leHBlY3RlZCgpOyAvLyBOT1RFOiBmYWxscyB0aHJvdWdoIHRvIF92YXJcbiAgICBjYXNlIF90b2tlbnR5cGUudHlwZXMuX3ZhcjpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlVmFyU3RhdGVtZW50KG5vZGUsIHN0YXJ0dHlwZSk7XG4gICAgY2FzZSBfdG9rZW50eXBlLnR5cGVzLl93aGlsZTpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlV2hpbGVTdGF0ZW1lbnQobm9kZSk7XG4gICAgY2FzZSBfdG9rZW50eXBlLnR5cGVzLl93aXRoOlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VXaXRoU3RhdGVtZW50KG5vZGUpO1xuICAgIGNhc2UgX3Rva2VudHlwZS50eXBlcy5icmFjZUw6XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZUJsb2NrKCk7XG4gICAgY2FzZSBfdG9rZW50eXBlLnR5cGVzLnNlbWk6XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZUVtcHR5U3RhdGVtZW50KG5vZGUpO1xuICAgIGNhc2UgX3Rva2VudHlwZS50eXBlcy5fZXhwb3J0OlxuICAgIGNhc2UgX3Rva2VudHlwZS50eXBlcy5faW1wb3J0OlxuICAgICAgaWYgKCF0aGlzLm9wdGlvbnMuYWxsb3dJbXBvcnRFeHBvcnRFdmVyeXdoZXJlKSB7XG4gICAgICAgIGlmICghdG9wTGV2ZWwpIHRoaXMucmFpc2UodGhpcy5zdGFydCwgXCInaW1wb3J0JyBhbmQgJ2V4cG9ydCcgbWF5IG9ubHkgYXBwZWFyIGF0IHRoZSB0b3AgbGV2ZWxcIik7XG4gICAgICAgIGlmICghdGhpcy5pbk1vZHVsZSkgdGhpcy5yYWlzZSh0aGlzLnN0YXJ0LCBcIidpbXBvcnQnIGFuZCAnZXhwb3J0JyBtYXkgYXBwZWFyIG9ubHkgd2l0aCAnc291cmNlVHlwZTogbW9kdWxlJ1wiKTtcbiAgICAgIH1cbiAgICAgIHJldHVybiBzdGFydHR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuX2ltcG9ydCA/IHRoaXMucGFyc2VJbXBvcnQobm9kZSkgOiB0aGlzLnBhcnNlRXhwb3J0KG5vZGUpO1xuXG4gICAgLy8gSWYgdGhlIHN0YXRlbWVudCBkb2VzIG5vdCBzdGFydCB3aXRoIGEgc3RhdGVtZW50IGtleXdvcmQgb3IgYVxuICAgIC8vIGJyYWNlLCBpdCdzIGFuIEV4cHJlc3Npb25TdGF0ZW1lbnQgb3IgTGFiZWxlZFN0YXRlbWVudC4gV2VcbiAgICAvLyBzaW1wbHkgc3RhcnQgcGFyc2luZyBhbiBleHByZXNzaW9uLCBhbmQgYWZ0ZXJ3YXJkcywgaWYgdGhlXG4gICAgLy8gbmV4dCB0b2tlbiBpcyBhIGNvbG9uIGFuZCB0aGUgZXhwcmVzc2lvbiB3YXMgYSBzaW1wbGVcbiAgICAvLyBJZGVudGlmaWVyIG5vZGUsIHdlIHN3aXRjaCB0byBpbnRlcnByZXRpbmcgaXQgYXMgYSBsYWJlbC5cbiAgICBkZWZhdWx0OlxuICAgICAgdmFyIG1heWJlTmFtZSA9IHRoaXMudmFsdWUsXG4gICAgICAgICAgZXhwciA9IHRoaXMucGFyc2VFeHByZXNzaW9uKCk7XG4gICAgICBpZiAoc3RhcnR0eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLm5hbWUgJiYgZXhwci50eXBlID09PSBcIklkZW50aWZpZXJcIiAmJiB0aGlzLmVhdChfdG9rZW50eXBlLnR5cGVzLmNvbG9uKSkgcmV0dXJuIHRoaXMucGFyc2VMYWJlbGVkU3RhdGVtZW50KG5vZGUsIG1heWJlTmFtZSwgZXhwcik7ZWxzZSByZXR1cm4gdGhpcy5wYXJzZUV4cHJlc3Npb25TdGF0ZW1lbnQobm9kZSwgZXhwcik7XG4gIH1cbn07XG5cbnBwLnBhcnNlQnJlYWtDb250aW51ZVN0YXRlbWVudCA9IGZ1bmN0aW9uIChub2RlLCBrZXl3b3JkKSB7XG4gIHZhciBpc0JyZWFrID0ga2V5d29yZCA9PSBcImJyZWFrXCI7XG4gIHRoaXMubmV4dCgpO1xuICBpZiAodGhpcy5lYXQoX3Rva2VudHlwZS50eXBlcy5zZW1pKSB8fCB0aGlzLmluc2VydFNlbWljb2xvbigpKSBub2RlLmxhYmVsID0gbnVsbDtlbHNlIGlmICh0aGlzLnR5cGUgIT09IF90b2tlbnR5cGUudHlwZXMubmFtZSkgdGhpcy51bmV4cGVjdGVkKCk7ZWxzZSB7XG4gICAgbm9kZS5sYWJlbCA9IHRoaXMucGFyc2VJZGVudCgpO1xuICAgIHRoaXMuc2VtaWNvbG9uKCk7XG4gIH1cblxuICAvLyBWZXJpZnkgdGhhdCB0aGVyZSBpcyBhbiBhY3R1YWwgZGVzdGluYXRpb24gdG8gYnJlYWsgb3JcbiAgLy8gY29udGludWUgdG8uXG4gIGZvciAodmFyIGkgPSAwOyBpIDwgdGhpcy5sYWJlbHMubGVuZ3RoOyArK2kpIHtcbiAgICB2YXIgbGFiID0gdGhpcy5sYWJlbHNbaV07XG4gICAgaWYgKG5vZGUubGFiZWwgPT0gbnVsbCB8fCBsYWIubmFtZSA9PT0gbm9kZS5sYWJlbC5uYW1lKSB7XG4gICAgICBpZiAobGFiLmtpbmQgIT0gbnVsbCAmJiAoaXNCcmVhayB8fCBsYWIua2luZCA9PT0gXCJsb29wXCIpKSBicmVhaztcbiAgICAgIGlmIChub2RlLmxhYmVsICYmIGlzQnJlYWspIGJyZWFrO1xuICAgIH1cbiAgfVxuICBpZiAoaSA9PT0gdGhpcy5sYWJlbHMubGVuZ3RoKSB0aGlzLnJhaXNlKG5vZGUuc3RhcnQsIFwiVW5zeW50YWN0aWMgXCIgKyBrZXl3b3JkKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBpc0JyZWFrID8gXCJCcmVha1N0YXRlbWVudFwiIDogXCJDb250aW51ZVN0YXRlbWVudFwiKTtcbn07XG5cbnBwLnBhcnNlRGVidWdnZXJTdGF0ZW1lbnQgPSBmdW5jdGlvbiAobm9kZSkge1xuICB0aGlzLm5leHQoKTtcbiAgdGhpcy5zZW1pY29sb24oKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkRlYnVnZ2VyU3RhdGVtZW50XCIpO1xufTtcblxucHAucGFyc2VEb1N0YXRlbWVudCA9IGZ1bmN0aW9uIChub2RlKSB7XG4gIHRoaXMubmV4dCgpO1xuICB0aGlzLmxhYmVscy5wdXNoKGxvb3BMYWJlbCk7XG4gIG5vZGUuYm9keSA9IHRoaXMucGFyc2VTdGF0ZW1lbnQoZmFsc2UpO1xuICB0aGlzLmxhYmVscy5wb3AoKTtcbiAgdGhpcy5leHBlY3QoX3Rva2VudHlwZS50eXBlcy5fd2hpbGUpO1xuICBub2RlLnRlc3QgPSB0aGlzLnBhcnNlUGFyZW5FeHByZXNzaW9uKCk7XG4gIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNikgdGhpcy5lYXQoX3Rva2VudHlwZS50eXBlcy5zZW1pKTtlbHNlIHRoaXMuc2VtaWNvbG9uKCk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJEb1doaWxlU3RhdGVtZW50XCIpO1xufTtcblxuLy8gRGlzYW1iaWd1YXRpbmcgYmV0d2VlbiBhIGBmb3JgIGFuZCBhIGBmb3JgL2BpbmAgb3IgYGZvcmAvYG9mYFxuLy8gbG9vcCBpcyBub24tdHJpdmlhbC4gQmFzaWNhbGx5LCB3ZSBoYXZlIHRvIHBhcnNlIHRoZSBpbml0IGB2YXJgXG4vLyBzdGF0ZW1lbnQgb3IgZXhwcmVzc2lvbiwgZGlzYWxsb3dpbmcgdGhlIGBpbmAgb3BlcmF0b3IgKHNlZVxuLy8gdGhlIHNlY29uZCBwYXJhbWV0ZXIgdG8gYHBhcnNlRXhwcmVzc2lvbmApLCBhbmQgdGhlbiBjaGVja1xuLy8gd2hldGhlciB0aGUgbmV4dCB0b2tlbiBpcyBgaW5gIG9yIGBvZmAuIFdoZW4gdGhlcmUgaXMgbm8gaW5pdFxuLy8gcGFydCAoc2VtaWNvbG9uIGltbWVkaWF0ZWx5IGFmdGVyIHRoZSBvcGVuaW5nIHBhcmVudGhlc2lzKSwgaXRcbi8vIGlzIGEgcmVndWxhciBgZm9yYCBsb29wLlxuXG5wcC5wYXJzZUZvclN0YXRlbWVudCA9IGZ1bmN0aW9uIChub2RlKSB7XG4gIHRoaXMubmV4dCgpO1xuICB0aGlzLmxhYmVscy5wdXNoKGxvb3BMYWJlbCk7XG4gIHRoaXMuZXhwZWN0KF90b2tlbnR5cGUudHlwZXMucGFyZW5MKTtcbiAgaWYgKHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5zZW1pKSByZXR1cm4gdGhpcy5wYXJzZUZvcihub2RlLCBudWxsKTtcbiAgaWYgKHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5fdmFyIHx8IHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5fbGV0IHx8IHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5fY29uc3QpIHtcbiAgICB2YXIgX2luaXQgPSB0aGlzLnN0YXJ0Tm9kZSgpLFxuICAgICAgICB2YXJLaW5kID0gdGhpcy50eXBlO1xuICAgIHRoaXMubmV4dCgpO1xuICAgIHRoaXMucGFyc2VWYXIoX2luaXQsIHRydWUsIHZhcktpbmQpO1xuICAgIHRoaXMuZmluaXNoTm9kZShfaW5pdCwgXCJWYXJpYWJsZURlY2xhcmF0aW9uXCIpO1xuICAgIGlmICgodGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLl9pbiB8fCB0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNiAmJiB0aGlzLmlzQ29udGV4dHVhbChcIm9mXCIpKSAmJiBfaW5pdC5kZWNsYXJhdGlvbnMubGVuZ3RoID09PSAxICYmICEodmFyS2luZCAhPT0gX3Rva2VudHlwZS50eXBlcy5fdmFyICYmIF9pbml0LmRlY2xhcmF0aW9uc1swXS5pbml0KSkgcmV0dXJuIHRoaXMucGFyc2VGb3JJbihub2RlLCBfaW5pdCk7XG4gICAgcmV0dXJuIHRoaXMucGFyc2VGb3Iobm9kZSwgX2luaXQpO1xuICB9XG4gIHZhciByZWZTaG9ydGhhbmREZWZhdWx0UG9zID0geyBzdGFydDogMCB9O1xuICB2YXIgaW5pdCA9IHRoaXMucGFyc2VFeHByZXNzaW9uKHRydWUsIHJlZlNob3J0aGFuZERlZmF1bHRQb3MpO1xuICBpZiAodGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLl9pbiB8fCB0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNiAmJiB0aGlzLmlzQ29udGV4dHVhbChcIm9mXCIpKSB7XG4gICAgdGhpcy50b0Fzc2lnbmFibGUoaW5pdCk7XG4gICAgdGhpcy5jaGVja0xWYWwoaW5pdCk7XG4gICAgcmV0dXJuIHRoaXMucGFyc2VGb3JJbihub2RlLCBpbml0KTtcbiAgfSBlbHNlIGlmIChyZWZTaG9ydGhhbmREZWZhdWx0UG9zLnN0YXJ0KSB7XG4gICAgdGhpcy51bmV4cGVjdGVkKHJlZlNob3J0aGFuZERlZmF1bHRQb3Muc3RhcnQpO1xuICB9XG4gIHJldHVybiB0aGlzLnBhcnNlRm9yKG5vZGUsIGluaXQpO1xufTtcblxucHAucGFyc2VGdW5jdGlvblN0YXRlbWVudCA9IGZ1bmN0aW9uIChub2RlKSB7XG4gIHRoaXMubmV4dCgpO1xuICByZXR1cm4gdGhpcy5wYXJzZUZ1bmN0aW9uKG5vZGUsIHRydWUpO1xufTtcblxucHAucGFyc2VJZlN0YXRlbWVudCA9IGZ1bmN0aW9uIChub2RlKSB7XG4gIHRoaXMubmV4dCgpO1xuICBub2RlLnRlc3QgPSB0aGlzLnBhcnNlUGFyZW5FeHByZXNzaW9uKCk7XG4gIG5vZGUuY29uc2VxdWVudCA9IHRoaXMucGFyc2VTdGF0ZW1lbnQoZmFsc2UpO1xuICBub2RlLmFsdGVybmF0ZSA9IHRoaXMuZWF0KF90b2tlbnR5cGUudHlwZXMuX2Vsc2UpID8gdGhpcy5wYXJzZVN0YXRlbWVudChmYWxzZSkgOiBudWxsO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiSWZTdGF0ZW1lbnRcIik7XG59O1xuXG5wcC5wYXJzZVJldHVyblN0YXRlbWVudCA9IGZ1bmN0aW9uIChub2RlKSB7XG4gIGlmICghdGhpcy5pbkZ1bmN0aW9uICYmICF0aGlzLm9wdGlvbnMuYWxsb3dSZXR1cm5PdXRzaWRlRnVuY3Rpb24pIHRoaXMucmFpc2UodGhpcy5zdGFydCwgXCIncmV0dXJuJyBvdXRzaWRlIG9mIGZ1bmN0aW9uXCIpO1xuICB0aGlzLm5leHQoKTtcblxuICAvLyBJbiBgcmV0dXJuYCAoYW5kIGBicmVha2AvYGNvbnRpbnVlYCksIHRoZSBrZXl3b3JkcyB3aXRoXG4gIC8vIG9wdGlvbmFsIGFyZ3VtZW50cywgd2UgZWFnZXJseSBsb29rIGZvciBhIHNlbWljb2xvbiBvciB0aGVcbiAgLy8gcG9zc2liaWxpdHkgdG8gaW5zZXJ0IG9uZS5cblxuICBpZiAodGhpcy5lYXQoX3Rva2VudHlwZS50eXBlcy5zZW1pKSB8fCB0aGlzLmluc2VydFNlbWljb2xvbigpKSBub2RlLmFyZ3VtZW50ID0gbnVsbDtlbHNlIHtcbiAgICBub2RlLmFyZ3VtZW50ID0gdGhpcy5wYXJzZUV4cHJlc3Npb24oKTt0aGlzLnNlbWljb2xvbigpO1xuICB9XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJSZXR1cm5TdGF0ZW1lbnRcIik7XG59O1xuXG5wcC5wYXJzZVN3aXRjaFN0YXRlbWVudCA9IGZ1bmN0aW9uIChub2RlKSB7XG4gIHRoaXMubmV4dCgpO1xuICBub2RlLmRpc2NyaW1pbmFudCA9IHRoaXMucGFyc2VQYXJlbkV4cHJlc3Npb24oKTtcbiAgbm9kZS5jYXNlcyA9IFtdO1xuICB0aGlzLmV4cGVjdChfdG9rZW50eXBlLnR5cGVzLmJyYWNlTCk7XG4gIHRoaXMubGFiZWxzLnB1c2goc3dpdGNoTGFiZWwpO1xuXG4gIC8vIFN0YXRlbWVudHMgdW5kZXIgbXVzdCBiZSBncm91cGVkIChieSBsYWJlbCkgaW4gU3dpdGNoQ2FzZVxuICAvLyBub2Rlcy4gYGN1cmAgaXMgdXNlZCB0byBrZWVwIHRoZSBub2RlIHRoYXQgd2UgYXJlIGN1cnJlbnRseVxuICAvLyBhZGRpbmcgc3RhdGVtZW50cyB0by5cblxuICBmb3IgKHZhciBjdXIsIHNhd0RlZmF1bHQgPSBmYWxzZTsgdGhpcy50eXBlICE9IF90b2tlbnR5cGUudHlwZXMuYnJhY2VSOykge1xuICAgIGlmICh0aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuX2Nhc2UgfHwgdGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLl9kZWZhdWx0KSB7XG4gICAgICB2YXIgaXNDYXNlID0gdGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLl9jYXNlO1xuICAgICAgaWYgKGN1cikgdGhpcy5maW5pc2hOb2RlKGN1ciwgXCJTd2l0Y2hDYXNlXCIpO1xuICAgICAgbm9kZS5jYXNlcy5wdXNoKGN1ciA9IHRoaXMuc3RhcnROb2RlKCkpO1xuICAgICAgY3VyLmNvbnNlcXVlbnQgPSBbXTtcbiAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgaWYgKGlzQ2FzZSkge1xuICAgICAgICBjdXIudGVzdCA9IHRoaXMucGFyc2VFeHByZXNzaW9uKCk7XG4gICAgICB9IGVsc2Uge1xuICAgICAgICBpZiAoc2F3RGVmYXVsdCkgdGhpcy5yYWlzZSh0aGlzLmxhc3RUb2tTdGFydCwgXCJNdWx0aXBsZSBkZWZhdWx0IGNsYXVzZXNcIik7XG4gICAgICAgIHNhd0RlZmF1bHQgPSB0cnVlO1xuICAgICAgICBjdXIudGVzdCA9IG51bGw7XG4gICAgICB9XG4gICAgICB0aGlzLmV4cGVjdChfdG9rZW50eXBlLnR5cGVzLmNvbG9uKTtcbiAgICB9IGVsc2Uge1xuICAgICAgaWYgKCFjdXIpIHRoaXMudW5leHBlY3RlZCgpO1xuICAgICAgY3VyLmNvbnNlcXVlbnQucHVzaCh0aGlzLnBhcnNlU3RhdGVtZW50KHRydWUpKTtcbiAgICB9XG4gIH1cbiAgaWYgKGN1cikgdGhpcy5maW5pc2hOb2RlKGN1ciwgXCJTd2l0Y2hDYXNlXCIpO1xuICB0aGlzLm5leHQoKTsgLy8gQ2xvc2luZyBicmFjZVxuICB0aGlzLmxhYmVscy5wb3AoKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIlN3aXRjaFN0YXRlbWVudFwiKTtcbn07XG5cbnBwLnBhcnNlVGhyb3dTdGF0ZW1lbnQgPSBmdW5jdGlvbiAobm9kZSkge1xuICB0aGlzLm5leHQoKTtcbiAgaWYgKF93aGl0ZXNwYWNlLmxpbmVCcmVhay50ZXN0KHRoaXMuaW5wdXQuc2xpY2UodGhpcy5sYXN0VG9rRW5kLCB0aGlzLnN0YXJ0KSkpIHRoaXMucmFpc2UodGhpcy5sYXN0VG9rRW5kLCBcIklsbGVnYWwgbmV3bGluZSBhZnRlciB0aHJvd1wiKTtcbiAgbm9kZS5hcmd1bWVudCA9IHRoaXMucGFyc2VFeHByZXNzaW9uKCk7XG4gIHRoaXMuc2VtaWNvbG9uKCk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJUaHJvd1N0YXRlbWVudFwiKTtcbn07XG5cbi8vIFJldXNlZCBlbXB0eSBhcnJheSBhZGRlZCBmb3Igbm9kZSBmaWVsZHMgdGhhdCBhcmUgYWx3YXlzIGVtcHR5LlxuXG52YXIgZW1wdHkgPSBbXTtcblxucHAucGFyc2VUcnlTdGF0ZW1lbnQgPSBmdW5jdGlvbiAobm9kZSkge1xuICB0aGlzLm5leHQoKTtcbiAgbm9kZS5ibG9jayA9IHRoaXMucGFyc2VCbG9jaygpO1xuICBub2RlLmhhbmRsZXIgPSBudWxsO1xuICBpZiAodGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLl9jYXRjaCkge1xuICAgIHZhciBjbGF1c2UgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICAgIHRoaXMubmV4dCgpO1xuICAgIHRoaXMuZXhwZWN0KF90b2tlbnR5cGUudHlwZXMucGFyZW5MKTtcbiAgICBjbGF1c2UucGFyYW0gPSB0aGlzLnBhcnNlQmluZGluZ0F0b20oKTtcbiAgICB0aGlzLmNoZWNrTFZhbChjbGF1c2UucGFyYW0sIHRydWUpO1xuICAgIHRoaXMuZXhwZWN0KF90b2tlbnR5cGUudHlwZXMucGFyZW5SKTtcbiAgICBjbGF1c2UuZ3VhcmQgPSBudWxsO1xuICAgIGNsYXVzZS5ib2R5ID0gdGhpcy5wYXJzZUJsb2NrKCk7XG4gICAgbm9kZS5oYW5kbGVyID0gdGhpcy5maW5pc2hOb2RlKGNsYXVzZSwgXCJDYXRjaENsYXVzZVwiKTtcbiAgfVxuICBub2RlLmd1YXJkZWRIYW5kbGVycyA9IGVtcHR5O1xuICBub2RlLmZpbmFsaXplciA9IHRoaXMuZWF0KF90b2tlbnR5cGUudHlwZXMuX2ZpbmFsbHkpID8gdGhpcy5wYXJzZUJsb2NrKCkgOiBudWxsO1xuICBpZiAoIW5vZGUuaGFuZGxlciAmJiAhbm9kZS5maW5hbGl6ZXIpIHRoaXMucmFpc2Uobm9kZS5zdGFydCwgXCJNaXNzaW5nIGNhdGNoIG9yIGZpbmFsbHkgY2xhdXNlXCIpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiVHJ5U3RhdGVtZW50XCIpO1xufTtcblxucHAucGFyc2VWYXJTdGF0ZW1lbnQgPSBmdW5jdGlvbiAobm9kZSwga2luZCkge1xuICB0aGlzLm5leHQoKTtcbiAgdGhpcy5wYXJzZVZhcihub2RlLCBmYWxzZSwga2luZCk7XG4gIHRoaXMuc2VtaWNvbG9uKCk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJWYXJpYWJsZURlY2xhcmF0aW9uXCIpO1xufTtcblxucHAucGFyc2VXaGlsZVN0YXRlbWVudCA9IGZ1bmN0aW9uIChub2RlKSB7XG4gIHRoaXMubmV4dCgpO1xuICBub2RlLnRlc3QgPSB0aGlzLnBhcnNlUGFyZW5FeHByZXNzaW9uKCk7XG4gIHRoaXMubGFiZWxzLnB1c2gobG9vcExhYmVsKTtcbiAgbm9kZS5ib2R5ID0gdGhpcy5wYXJzZVN0YXRlbWVudChmYWxzZSk7XG4gIHRoaXMubGFiZWxzLnBvcCgpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiV2hpbGVTdGF0ZW1lbnRcIik7XG59O1xuXG5wcC5wYXJzZVdpdGhTdGF0ZW1lbnQgPSBmdW5jdGlvbiAobm9kZSkge1xuICBpZiAodGhpcy5zdHJpY3QpIHRoaXMucmFpc2UodGhpcy5zdGFydCwgXCInd2l0aCcgaW4gc3RyaWN0IG1vZGVcIik7XG4gIHRoaXMubmV4dCgpO1xuICBub2RlLm9iamVjdCA9IHRoaXMucGFyc2VQYXJlbkV4cHJlc3Npb24oKTtcbiAgbm9kZS5ib2R5ID0gdGhpcy5wYXJzZVN0YXRlbWVudChmYWxzZSk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJXaXRoU3RhdGVtZW50XCIpO1xufTtcblxucHAucGFyc2VFbXB0eVN0YXRlbWVudCA9IGZ1bmN0aW9uIChub2RlKSB7XG4gIHRoaXMubmV4dCgpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiRW1wdHlTdGF0ZW1lbnRcIik7XG59O1xuXG5wcC5wYXJzZUxhYmVsZWRTdGF0ZW1lbnQgPSBmdW5jdGlvbiAobm9kZSwgbWF5YmVOYW1lLCBleHByKSB7XG4gIGZvciAodmFyIGkgPSAwOyBpIDwgdGhpcy5sYWJlbHMubGVuZ3RoOyArK2kpIHtcbiAgICBpZiAodGhpcy5sYWJlbHNbaV0ubmFtZSA9PT0gbWF5YmVOYW1lKSB0aGlzLnJhaXNlKGV4cHIuc3RhcnQsIFwiTGFiZWwgJ1wiICsgbWF5YmVOYW1lICsgXCInIGlzIGFscmVhZHkgZGVjbGFyZWRcIik7XG4gIH12YXIga2luZCA9IHRoaXMudHlwZS5pc0xvb3AgPyBcImxvb3BcIiA6IHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5fc3dpdGNoID8gXCJzd2l0Y2hcIiA6IG51bGw7XG4gIGZvciAodmFyIGkgPSB0aGlzLmxhYmVscy5sZW5ndGggLSAxOyBpID49IDA7IGktLSkge1xuICAgIHZhciBsYWJlbCA9IHRoaXMubGFiZWxzW2ldO1xuICAgIGlmIChsYWJlbC5zdGF0ZW1lbnRTdGFydCA9PSBub2RlLnN0YXJ0KSB7XG4gICAgICBsYWJlbC5zdGF0ZW1lbnRTdGFydCA9IHRoaXMuc3RhcnQ7XG4gICAgICBsYWJlbC5raW5kID0ga2luZDtcbiAgICB9IGVsc2UgYnJlYWs7XG4gIH1cbiAgdGhpcy5sYWJlbHMucHVzaCh7IG5hbWU6IG1heWJlTmFtZSwga2luZDoga2luZCwgc3RhdGVtZW50U3RhcnQ6IHRoaXMuc3RhcnQgfSk7XG4gIG5vZGUuYm9keSA9IHRoaXMucGFyc2VTdGF0ZW1lbnQodHJ1ZSk7XG4gIHRoaXMubGFiZWxzLnBvcCgpO1xuICBub2RlLmxhYmVsID0gZXhwcjtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkxhYmVsZWRTdGF0ZW1lbnRcIik7XG59O1xuXG5wcC5wYXJzZUV4cHJlc3Npb25TdGF0ZW1lbnQgPSBmdW5jdGlvbiAobm9kZSwgZXhwcikge1xuICBub2RlLmV4cHJlc3Npb24gPSBleHByO1xuICB0aGlzLnNlbWljb2xvbigpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiRXhwcmVzc2lvblN0YXRlbWVudFwiKTtcbn07XG5cbi8vIFBhcnNlIGEgc2VtaWNvbG9uLWVuY2xvc2VkIGJsb2NrIG9mIHN0YXRlbWVudHMsIGhhbmRsaW5nIGBcInVzZVxuLy8gc3RyaWN0XCJgIGRlY2xhcmF0aW9ucyB3aGVuIGBhbGxvd1N0cmljdGAgaXMgdHJ1ZSAodXNlZCBmb3Jcbi8vIGZ1bmN0aW9uIGJvZGllcykuXG5cbnBwLnBhcnNlQmxvY2sgPSBmdW5jdGlvbiAoYWxsb3dTdHJpY3QpIHtcbiAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpLFxuICAgICAgZmlyc3QgPSB0cnVlLFxuICAgICAgb2xkU3RyaWN0ID0gdW5kZWZpbmVkO1xuICBub2RlLmJvZHkgPSBbXTtcbiAgdGhpcy5leHBlY3QoX3Rva2VudHlwZS50eXBlcy5icmFjZUwpO1xuICB3aGlsZSAoIXRoaXMuZWF0KF90b2tlbnR5cGUudHlwZXMuYnJhY2VSKSkge1xuICAgIHZhciBzdG10ID0gdGhpcy5wYXJzZVN0YXRlbWVudCh0cnVlKTtcbiAgICBub2RlLmJvZHkucHVzaChzdG10KTtcbiAgICBpZiAoZmlyc3QgJiYgYWxsb3dTdHJpY3QgJiYgdGhpcy5pc1VzZVN0cmljdChzdG10KSkge1xuICAgICAgb2xkU3RyaWN0ID0gdGhpcy5zdHJpY3Q7XG4gICAgICB0aGlzLnNldFN0cmljdCh0aGlzLnN0cmljdCA9IHRydWUpO1xuICAgIH1cbiAgICBmaXJzdCA9IGZhbHNlO1xuICB9XG4gIGlmIChvbGRTdHJpY3QgPT09IGZhbHNlKSB0aGlzLnNldFN0cmljdChmYWxzZSk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJCbG9ja1N0YXRlbWVudFwiKTtcbn07XG5cbi8vIFBhcnNlIGEgcmVndWxhciBgZm9yYCBsb29wLiBUaGUgZGlzYW1iaWd1YXRpb24gY29kZSBpblxuLy8gYHBhcnNlU3RhdGVtZW50YCB3aWxsIGFscmVhZHkgaGF2ZSBwYXJzZWQgdGhlIGluaXQgc3RhdGVtZW50IG9yXG4vLyBleHByZXNzaW9uLlxuXG5wcC5wYXJzZUZvciA9IGZ1bmN0aW9uIChub2RlLCBpbml0KSB7XG4gIG5vZGUuaW5pdCA9IGluaXQ7XG4gIHRoaXMuZXhwZWN0KF90b2tlbnR5cGUudHlwZXMuc2VtaSk7XG4gIG5vZGUudGVzdCA9IHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5zZW1pID8gbnVsbCA6IHRoaXMucGFyc2VFeHByZXNzaW9uKCk7XG4gIHRoaXMuZXhwZWN0KF90b2tlbnR5cGUudHlwZXMuc2VtaSk7XG4gIG5vZGUudXBkYXRlID0gdGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLnBhcmVuUiA/IG51bGwgOiB0aGlzLnBhcnNlRXhwcmVzc2lvbigpO1xuICB0aGlzLmV4cGVjdChfdG9rZW50eXBlLnR5cGVzLnBhcmVuUik7XG4gIG5vZGUuYm9keSA9IHRoaXMucGFyc2VTdGF0ZW1lbnQoZmFsc2UpO1xuICB0aGlzLmxhYmVscy5wb3AoKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkZvclN0YXRlbWVudFwiKTtcbn07XG5cbi8vIFBhcnNlIGEgYGZvcmAvYGluYCBhbmQgYGZvcmAvYG9mYCBsb29wLCB3aGljaCBhcmUgYWxtb3N0XG4vLyBzYW1lIGZyb20gcGFyc2VyJ3MgcGVyc3BlY3RpdmUuXG5cbnBwLnBhcnNlRm9ySW4gPSBmdW5jdGlvbiAobm9kZSwgaW5pdCkge1xuICB2YXIgdHlwZSA9IHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5faW4gPyBcIkZvckluU3RhdGVtZW50XCIgOiBcIkZvck9mU3RhdGVtZW50XCI7XG4gIHRoaXMubmV4dCgpO1xuICBub2RlLmxlZnQgPSBpbml0O1xuICBub2RlLnJpZ2h0ID0gdGhpcy5wYXJzZUV4cHJlc3Npb24oKTtcbiAgdGhpcy5leHBlY3QoX3Rva2VudHlwZS50eXBlcy5wYXJlblIpO1xuICBub2RlLmJvZHkgPSB0aGlzLnBhcnNlU3RhdGVtZW50KGZhbHNlKTtcbiAgdGhpcy5sYWJlbHMucG9wKCk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgdHlwZSk7XG59O1xuXG4vLyBQYXJzZSBhIGxpc3Qgb2YgdmFyaWFibGUgZGVjbGFyYXRpb25zLlxuXG5wcC5wYXJzZVZhciA9IGZ1bmN0aW9uIChub2RlLCBpc0Zvciwga2luZCkge1xuICBub2RlLmRlY2xhcmF0aW9ucyA9IFtdO1xuICBub2RlLmtpbmQgPSBraW5kLmtleXdvcmQ7XG4gIGZvciAoOzspIHtcbiAgICB2YXIgZGVjbCA9IHRoaXMuc3RhcnROb2RlKCk7XG4gICAgdGhpcy5wYXJzZVZhcklkKGRlY2wpO1xuICAgIGlmICh0aGlzLmVhdChfdG9rZW50eXBlLnR5cGVzLmVxKSkge1xuICAgICAgZGVjbC5pbml0ID0gdGhpcy5wYXJzZU1heWJlQXNzaWduKGlzRm9yKTtcbiAgICB9IGVsc2UgaWYgKGtpbmQgPT09IF90b2tlbnR5cGUudHlwZXMuX2NvbnN0ICYmICEodGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLl9pbiB8fCB0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNiAmJiB0aGlzLmlzQ29udGV4dHVhbChcIm9mXCIpKSkge1xuICAgICAgdGhpcy51bmV4cGVjdGVkKCk7XG4gICAgfSBlbHNlIGlmIChkZWNsLmlkLnR5cGUgIT0gXCJJZGVudGlmaWVyXCIgJiYgIShpc0ZvciAmJiAodGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLl9pbiB8fCB0aGlzLmlzQ29udGV4dHVhbChcIm9mXCIpKSkpIHtcbiAgICAgIHRoaXMucmFpc2UodGhpcy5sYXN0VG9rRW5kLCBcIkNvbXBsZXggYmluZGluZyBwYXR0ZXJucyByZXF1aXJlIGFuIGluaXRpYWxpemF0aW9uIHZhbHVlXCIpO1xuICAgIH0gZWxzZSB7XG4gICAgICBkZWNsLmluaXQgPSBudWxsO1xuICAgIH1cbiAgICBub2RlLmRlY2xhcmF0aW9ucy5wdXNoKHRoaXMuZmluaXNoTm9kZShkZWNsLCBcIlZhcmlhYmxlRGVjbGFyYXRvclwiKSk7XG4gICAgaWYgKCF0aGlzLmVhdChfdG9rZW50eXBlLnR5cGVzLmNvbW1hKSkgYnJlYWs7XG4gIH1cbiAgcmV0dXJuIG5vZGU7XG59O1xuXG5wcC5wYXJzZVZhcklkID0gZnVuY3Rpb24gKGRlY2wpIHtcbiAgZGVjbC5pZCA9IHRoaXMucGFyc2VCaW5kaW5nQXRvbSgpO1xuICB0aGlzLmNoZWNrTFZhbChkZWNsLmlkLCB0cnVlKTtcbn07XG5cbi8vIFBhcnNlIGEgZnVuY3Rpb24gZGVjbGFyYXRpb24gb3IgbGl0ZXJhbCAoZGVwZW5kaW5nIG9uIHRoZVxuLy8gYGlzU3RhdGVtZW50YCBwYXJhbWV0ZXIpLlxuXG5wcC5wYXJzZUZ1bmN0aW9uID0gZnVuY3Rpb24gKG5vZGUsIGlzU3RhdGVtZW50LCBhbGxvd0V4cHJlc3Npb25Cb2R5KSB7XG4gIHRoaXMuaW5pdEZ1bmN0aW9uKG5vZGUpO1xuICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYpIG5vZGUuZ2VuZXJhdG9yID0gdGhpcy5lYXQoX3Rva2VudHlwZS50eXBlcy5zdGFyKTtcbiAgaWYgKGlzU3RhdGVtZW50IHx8IHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5uYW1lKSBub2RlLmlkID0gdGhpcy5wYXJzZUlkZW50KCk7XG4gIHRoaXMucGFyc2VGdW5jdGlvblBhcmFtcyhub2RlKTtcbiAgdGhpcy5wYXJzZUZ1bmN0aW9uQm9keShub2RlLCBhbGxvd0V4cHJlc3Npb25Cb2R5KTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBpc1N0YXRlbWVudCA/IFwiRnVuY3Rpb25EZWNsYXJhdGlvblwiIDogXCJGdW5jdGlvbkV4cHJlc3Npb25cIik7XG59O1xuXG5wcC5wYXJzZUZ1bmN0aW9uUGFyYW1zID0gZnVuY3Rpb24gKG5vZGUpIHtcbiAgdGhpcy5leHBlY3QoX3Rva2VudHlwZS50eXBlcy5wYXJlbkwpO1xuICBub2RlLnBhcmFtcyA9IHRoaXMucGFyc2VCaW5kaW5nTGlzdChfdG9rZW50eXBlLnR5cGVzLnBhcmVuUiwgZmFsc2UsIGZhbHNlKTtcbn07XG5cbi8vIFBhcnNlIGEgY2xhc3MgZGVjbGFyYXRpb24gb3IgbGl0ZXJhbCAoZGVwZW5kaW5nIG9uIHRoZVxuLy8gYGlzU3RhdGVtZW50YCBwYXJhbWV0ZXIpLlxuXG5wcC5wYXJzZUNsYXNzID0gZnVuY3Rpb24gKG5vZGUsIGlzU3RhdGVtZW50KSB7XG4gIHRoaXMubmV4dCgpO1xuICB0aGlzLnBhcnNlQ2xhc3NJZChub2RlLCBpc1N0YXRlbWVudCk7XG4gIHRoaXMucGFyc2VDbGFzc1N1cGVyKG5vZGUpO1xuICB2YXIgY2xhc3NCb2R5ID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgdmFyIGhhZENvbnN0cnVjdG9yID0gZmFsc2U7XG4gIGNsYXNzQm9keS5ib2R5ID0gW107XG4gIHRoaXMuZXhwZWN0KF90b2tlbnR5cGUudHlwZXMuYnJhY2VMKTtcbiAgd2hpbGUgKCF0aGlzLmVhdChfdG9rZW50eXBlLnR5cGVzLmJyYWNlUikpIHtcbiAgICBpZiAodGhpcy5lYXQoX3Rva2VudHlwZS50eXBlcy5zZW1pKSkgY29udGludWU7XG4gICAgdmFyIG1ldGhvZCA9IHRoaXMuc3RhcnROb2RlKCk7XG4gICAgdmFyIGlzR2VuZXJhdG9yID0gdGhpcy5lYXQoX3Rva2VudHlwZS50eXBlcy5zdGFyKTtcbiAgICB2YXIgaXNNYXliZVN0YXRpYyA9IHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5uYW1lICYmIHRoaXMudmFsdWUgPT09IFwic3RhdGljXCI7XG4gICAgdGhpcy5wYXJzZVByb3BlcnR5TmFtZShtZXRob2QpO1xuICAgIG1ldGhvZFtcInN0YXRpY1wiXSA9IGlzTWF5YmVTdGF0aWMgJiYgdGhpcy50eXBlICE9PSBfdG9rZW50eXBlLnR5cGVzLnBhcmVuTDtcbiAgICBpZiAobWV0aG9kW1wic3RhdGljXCJdKSB7XG4gICAgICBpZiAoaXNHZW5lcmF0b3IpIHRoaXMudW5leHBlY3RlZCgpO1xuICAgICAgaXNHZW5lcmF0b3IgPSB0aGlzLmVhdChfdG9rZW50eXBlLnR5cGVzLnN0YXIpO1xuICAgICAgdGhpcy5wYXJzZVByb3BlcnR5TmFtZShtZXRob2QpO1xuICAgIH1cbiAgICBtZXRob2Qua2luZCA9IFwibWV0aG9kXCI7XG4gICAgdmFyIGlzR2V0U2V0ID0gZmFsc2U7XG4gICAgaWYgKCFtZXRob2QuY29tcHV0ZWQpIHtcbiAgICAgIHZhciBrZXkgPSBtZXRob2Qua2V5O1xuXG4gICAgICBpZiAoIWlzR2VuZXJhdG9yICYmIGtleS50eXBlID09PSBcIklkZW50aWZpZXJcIiAmJiB0aGlzLnR5cGUgIT09IF90b2tlbnR5cGUudHlwZXMucGFyZW5MICYmIChrZXkubmFtZSA9PT0gXCJnZXRcIiB8fCBrZXkubmFtZSA9PT0gXCJzZXRcIikpIHtcbiAgICAgICAgaXNHZXRTZXQgPSB0cnVlO1xuICAgICAgICBtZXRob2Qua2luZCA9IGtleS5uYW1lO1xuICAgICAgICBrZXkgPSB0aGlzLnBhcnNlUHJvcGVydHlOYW1lKG1ldGhvZCk7XG4gICAgICB9XG4gICAgICBpZiAoIW1ldGhvZFtcInN0YXRpY1wiXSAmJiAoa2V5LnR5cGUgPT09IFwiSWRlbnRpZmllclwiICYmIGtleS5uYW1lID09PSBcImNvbnN0cnVjdG9yXCIgfHwga2V5LnR5cGUgPT09IFwiTGl0ZXJhbFwiICYmIGtleS52YWx1ZSA9PT0gXCJjb25zdHJ1Y3RvclwiKSkge1xuICAgICAgICBpZiAoaGFkQ29uc3RydWN0b3IpIHRoaXMucmFpc2Uoa2V5LnN0YXJ0LCBcIkR1cGxpY2F0ZSBjb25zdHJ1Y3RvciBpbiB0aGUgc2FtZSBjbGFzc1wiKTtcbiAgICAgICAgaWYgKGlzR2V0U2V0KSB0aGlzLnJhaXNlKGtleS5zdGFydCwgXCJDb25zdHJ1Y3RvciBjYW4ndCBoYXZlIGdldC9zZXQgbW9kaWZpZXJcIik7XG4gICAgICAgIGlmIChpc0dlbmVyYXRvcikgdGhpcy5yYWlzZShrZXkuc3RhcnQsIFwiQ29uc3RydWN0b3IgY2FuJ3QgYmUgYSBnZW5lcmF0b3JcIik7XG4gICAgICAgIG1ldGhvZC5raW5kID0gXCJjb25zdHJ1Y3RvclwiO1xuICAgICAgICBoYWRDb25zdHJ1Y3RvciA9IHRydWU7XG4gICAgICB9XG4gICAgfVxuICAgIHRoaXMucGFyc2VDbGFzc01ldGhvZChjbGFzc0JvZHksIG1ldGhvZCwgaXNHZW5lcmF0b3IpO1xuICAgIGlmIChpc0dldFNldCkge1xuICAgICAgdmFyIHBhcmFtQ291bnQgPSBtZXRob2Qua2luZCA9PT0gXCJnZXRcIiA/IDAgOiAxO1xuICAgICAgaWYgKG1ldGhvZC52YWx1ZS5wYXJhbXMubGVuZ3RoICE9PSBwYXJhbUNvdW50KSB7XG4gICAgICAgIHZhciBzdGFydCA9IG1ldGhvZC52YWx1ZS5zdGFydDtcbiAgICAgICAgaWYgKG1ldGhvZC5raW5kID09PSBcImdldFwiKSB0aGlzLnJhaXNlKHN0YXJ0LCBcImdldHRlciBzaG91bGQgaGF2ZSBubyBwYXJhbXNcIik7ZWxzZSB0aGlzLnJhaXNlKHN0YXJ0LCBcInNldHRlciBzaG91bGQgaGF2ZSBleGFjdGx5IG9uZSBwYXJhbVwiKTtcbiAgICAgIH1cbiAgICB9XG4gIH1cbiAgbm9kZS5ib2R5ID0gdGhpcy5maW5pc2hOb2RlKGNsYXNzQm9keSwgXCJDbGFzc0JvZHlcIik7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgaXNTdGF0ZW1lbnQgPyBcIkNsYXNzRGVjbGFyYXRpb25cIiA6IFwiQ2xhc3NFeHByZXNzaW9uXCIpO1xufTtcblxucHAucGFyc2VDbGFzc01ldGhvZCA9IGZ1bmN0aW9uIChjbGFzc0JvZHksIG1ldGhvZCwgaXNHZW5lcmF0b3IpIHtcbiAgbWV0aG9kLnZhbHVlID0gdGhpcy5wYXJzZU1ldGhvZChpc0dlbmVyYXRvcik7XG4gIGNsYXNzQm9keS5ib2R5LnB1c2godGhpcy5maW5pc2hOb2RlKG1ldGhvZCwgXCJNZXRob2REZWZpbml0aW9uXCIpKTtcbn07XG5cbnBwLnBhcnNlQ2xhc3NJZCA9IGZ1bmN0aW9uIChub2RlLCBpc1N0YXRlbWVudCkge1xuICBub2RlLmlkID0gdGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLm5hbWUgPyB0aGlzLnBhcnNlSWRlbnQoKSA6IGlzU3RhdGVtZW50ID8gdGhpcy51bmV4cGVjdGVkKCkgOiBudWxsO1xufTtcblxucHAucGFyc2VDbGFzc1N1cGVyID0gZnVuY3Rpb24gKG5vZGUpIHtcbiAgbm9kZS5zdXBlckNsYXNzID0gdGhpcy5lYXQoX3Rva2VudHlwZS50eXBlcy5fZXh0ZW5kcykgPyB0aGlzLnBhcnNlRXhwclN1YnNjcmlwdHMoKSA6IG51bGw7XG59O1xuXG4vLyBQYXJzZXMgbW9kdWxlIGV4cG9ydCBkZWNsYXJhdGlvbi5cblxucHAucGFyc2VFeHBvcnQgPSBmdW5jdGlvbiAobm9kZSkge1xuICB0aGlzLm5leHQoKTtcbiAgLy8gZXhwb3J0ICogZnJvbSAnLi4uJ1xuICBpZiAodGhpcy5lYXQoX3Rva2VudHlwZS50eXBlcy5zdGFyKSkge1xuICAgIHRoaXMuZXhwZWN0Q29udGV4dHVhbChcImZyb21cIik7XG4gICAgbm9kZS5zb3VyY2UgPSB0aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuc3RyaW5nID8gdGhpcy5wYXJzZUV4cHJBdG9tKCkgOiB0aGlzLnVuZXhwZWN0ZWQoKTtcbiAgICB0aGlzLnNlbWljb2xvbigpO1xuICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJFeHBvcnRBbGxEZWNsYXJhdGlvblwiKTtcbiAgfVxuICBpZiAodGhpcy5lYXQoX3Rva2VudHlwZS50eXBlcy5fZGVmYXVsdCkpIHtcbiAgICAvLyBleHBvcnQgZGVmYXVsdCAuLi5cbiAgICB2YXIgZXhwciA9IHRoaXMucGFyc2VNYXliZUFzc2lnbigpO1xuICAgIHZhciBuZWVkc1NlbWkgPSB0cnVlO1xuICAgIGlmIChleHByLnR5cGUgPT0gXCJGdW5jdGlvbkV4cHJlc3Npb25cIiB8fCBleHByLnR5cGUgPT0gXCJDbGFzc0V4cHJlc3Npb25cIikge1xuICAgICAgbmVlZHNTZW1pID0gZmFsc2U7XG4gICAgICBpZiAoZXhwci5pZCkge1xuICAgICAgICBleHByLnR5cGUgPSBleHByLnR5cGUgPT0gXCJGdW5jdGlvbkV4cHJlc3Npb25cIiA/IFwiRnVuY3Rpb25EZWNsYXJhdGlvblwiIDogXCJDbGFzc0RlY2xhcmF0aW9uXCI7XG4gICAgICB9XG4gICAgfVxuICAgIG5vZGUuZGVjbGFyYXRpb24gPSBleHByO1xuICAgIGlmIChuZWVkc1NlbWkpIHRoaXMuc2VtaWNvbG9uKCk7XG4gICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkV4cG9ydERlZmF1bHREZWNsYXJhdGlvblwiKTtcbiAgfVxuICAvLyBleHBvcnQgdmFyfGNvbnN0fGxldHxmdW5jdGlvbnxjbGFzcyAuLi5cbiAgaWYgKHRoaXMuc2hvdWxkUGFyc2VFeHBvcnRTdGF0ZW1lbnQoKSkge1xuICAgIG5vZGUuZGVjbGFyYXRpb24gPSB0aGlzLnBhcnNlU3RhdGVtZW50KHRydWUpO1xuICAgIG5vZGUuc3BlY2lmaWVycyA9IFtdO1xuICAgIG5vZGUuc291cmNlID0gbnVsbDtcbiAgfSBlbHNlIHtcbiAgICAvLyBleHBvcnQgeyB4LCB5IGFzIHogfSBbZnJvbSAnLi4uJ11cbiAgICBub2RlLmRlY2xhcmF0aW9uID0gbnVsbDtcbiAgICBub2RlLnNwZWNpZmllcnMgPSB0aGlzLnBhcnNlRXhwb3J0U3BlY2lmaWVycygpO1xuICAgIGlmICh0aGlzLmVhdENvbnRleHR1YWwoXCJmcm9tXCIpKSB7XG4gICAgICBub2RlLnNvdXJjZSA9IHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5zdHJpbmcgPyB0aGlzLnBhcnNlRXhwckF0b20oKSA6IHRoaXMudW5leHBlY3RlZCgpO1xuICAgIH0gZWxzZSB7XG4gICAgICBub2RlLnNvdXJjZSA9IG51bGw7XG4gICAgfVxuICAgIHRoaXMuc2VtaWNvbG9uKCk7XG4gIH1cbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkV4cG9ydE5hbWVkRGVjbGFyYXRpb25cIik7XG59O1xuXG5wcC5zaG91bGRQYXJzZUV4cG9ydFN0YXRlbWVudCA9IGZ1bmN0aW9uICgpIHtcbiAgcmV0dXJuIHRoaXMudHlwZS5rZXl3b3JkO1xufTtcblxuLy8gUGFyc2VzIGEgY29tbWEtc2VwYXJhdGVkIGxpc3Qgb2YgbW9kdWxlIGV4cG9ydHMuXG5cbnBwLnBhcnNlRXhwb3J0U3BlY2lmaWVycyA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIG5vZGVzID0gW10sXG4gICAgICBmaXJzdCA9IHRydWU7XG4gIC8vIGV4cG9ydCB7IHgsIHkgYXMgeiB9IFtmcm9tICcuLi4nXVxuICB0aGlzLmV4cGVjdChfdG9rZW50eXBlLnR5cGVzLmJyYWNlTCk7XG4gIHdoaWxlICghdGhpcy5lYXQoX3Rva2VudHlwZS50eXBlcy5icmFjZVIpKSB7XG4gICAgaWYgKCFmaXJzdCkge1xuICAgICAgdGhpcy5leHBlY3QoX3Rva2VudHlwZS50eXBlcy5jb21tYSk7XG4gICAgICBpZiAodGhpcy5hZnRlclRyYWlsaW5nQ29tbWEoX3Rva2VudHlwZS50eXBlcy5icmFjZVIpKSBicmVhaztcbiAgICB9IGVsc2UgZmlyc3QgPSBmYWxzZTtcblxuICAgIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgICBub2RlLmxvY2FsID0gdGhpcy5wYXJzZUlkZW50KHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5fZGVmYXVsdCk7XG4gICAgbm9kZS5leHBvcnRlZCA9IHRoaXMuZWF0Q29udGV4dHVhbChcImFzXCIpID8gdGhpcy5wYXJzZUlkZW50KHRydWUpIDogbm9kZS5sb2NhbDtcbiAgICBub2Rlcy5wdXNoKHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkV4cG9ydFNwZWNpZmllclwiKSk7XG4gIH1cbiAgcmV0dXJuIG5vZGVzO1xufTtcblxuLy8gUGFyc2VzIGltcG9ydCBkZWNsYXJhdGlvbi5cblxucHAucGFyc2VJbXBvcnQgPSBmdW5jdGlvbiAobm9kZSkge1xuICB0aGlzLm5leHQoKTtcbiAgLy8gaW1wb3J0ICcuLi4nXG4gIGlmICh0aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuc3RyaW5nKSB7XG4gICAgbm9kZS5zcGVjaWZpZXJzID0gZW1wdHk7XG4gICAgbm9kZS5zb3VyY2UgPSB0aGlzLnBhcnNlRXhwckF0b20oKTtcbiAgfSBlbHNlIHtcbiAgICBub2RlLnNwZWNpZmllcnMgPSB0aGlzLnBhcnNlSW1wb3J0U3BlY2lmaWVycygpO1xuICAgIHRoaXMuZXhwZWN0Q29udGV4dHVhbChcImZyb21cIik7XG4gICAgbm9kZS5zb3VyY2UgPSB0aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuc3RyaW5nID8gdGhpcy5wYXJzZUV4cHJBdG9tKCkgOiB0aGlzLnVuZXhwZWN0ZWQoKTtcbiAgfVxuICB0aGlzLnNlbWljb2xvbigpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiSW1wb3J0RGVjbGFyYXRpb25cIik7XG59O1xuXG4vLyBQYXJzZXMgYSBjb21tYS1zZXBhcmF0ZWQgbGlzdCBvZiBtb2R1bGUgaW1wb3J0cy5cblxucHAucGFyc2VJbXBvcnRTcGVjaWZpZXJzID0gZnVuY3Rpb24gKCkge1xuICB2YXIgbm9kZXMgPSBbXSxcbiAgICAgIGZpcnN0ID0gdHJ1ZTtcbiAgaWYgKHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5uYW1lKSB7XG4gICAgLy8gaW1wb3J0IGRlZmF1bHRPYmosIHsgeCwgeSBhcyB6IH0gZnJvbSAnLi4uJ1xuICAgIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgICBub2RlLmxvY2FsID0gdGhpcy5wYXJzZUlkZW50KCk7XG4gICAgdGhpcy5jaGVja0xWYWwobm9kZS5sb2NhbCwgdHJ1ZSk7XG4gICAgbm9kZXMucHVzaCh0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJJbXBvcnREZWZhdWx0U3BlY2lmaWVyXCIpKTtcbiAgICBpZiAoIXRoaXMuZWF0KF90b2tlbnR5cGUudHlwZXMuY29tbWEpKSByZXR1cm4gbm9kZXM7XG4gIH1cbiAgaWYgKHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5zdGFyKSB7XG4gICAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICAgIHRoaXMubmV4dCgpO1xuICAgIHRoaXMuZXhwZWN0Q29udGV4dHVhbChcImFzXCIpO1xuICAgIG5vZGUubG9jYWwgPSB0aGlzLnBhcnNlSWRlbnQoKTtcbiAgICB0aGlzLmNoZWNrTFZhbChub2RlLmxvY2FsLCB0cnVlKTtcbiAgICBub2Rlcy5wdXNoKHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkltcG9ydE5hbWVzcGFjZVNwZWNpZmllclwiKSk7XG4gICAgcmV0dXJuIG5vZGVzO1xuICB9XG4gIHRoaXMuZXhwZWN0KF90b2tlbnR5cGUudHlwZXMuYnJhY2VMKTtcbiAgd2hpbGUgKCF0aGlzLmVhdChfdG9rZW50eXBlLnR5cGVzLmJyYWNlUikpIHtcbiAgICBpZiAoIWZpcnN0KSB7XG4gICAgICB0aGlzLmV4cGVjdChfdG9rZW50eXBlLnR5cGVzLmNvbW1hKTtcbiAgICAgIGlmICh0aGlzLmFmdGVyVHJhaWxpbmdDb21tYShfdG9rZW50eXBlLnR5cGVzLmJyYWNlUikpIGJyZWFrO1xuICAgIH0gZWxzZSBmaXJzdCA9IGZhbHNlO1xuXG4gICAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICAgIG5vZGUuaW1wb3J0ZWQgPSB0aGlzLnBhcnNlSWRlbnQodHJ1ZSk7XG4gICAgbm9kZS5sb2NhbCA9IHRoaXMuZWF0Q29udGV4dHVhbChcImFzXCIpID8gdGhpcy5wYXJzZUlkZW50KCkgOiBub2RlLmltcG9ydGVkO1xuICAgIHRoaXMuY2hlY2tMVmFsKG5vZGUubG9jYWwsIHRydWUpO1xuICAgIG5vZGVzLnB1c2godGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiSW1wb3J0U3BlY2lmaWVyXCIpKTtcbiAgfVxuICByZXR1cm4gbm9kZXM7XG59O1xuXG59LHtcIi4vc3RhdGVcIjoxMCxcIi4vdG9rZW50eXBlXCI6MTQsXCIuL3doaXRlc3BhY2VcIjoxNn1dLDEyOltmdW5jdGlvbihfZGVyZXFfLG1vZHVsZSxleHBvcnRzKXtcbi8vIFRoZSBhbGdvcml0aG0gdXNlZCB0byBkZXRlcm1pbmUgd2hldGhlciBhIHJlZ2V4cCBjYW4gYXBwZWFyIGF0IGFcbi8vIGdpdmVuIHBvaW50IGluIHRoZSBwcm9ncmFtIGlzIGxvb3NlbHkgYmFzZWQgb24gc3dlZXQuanMnIGFwcHJvYWNoLlxuLy8gU2VlIGh0dHBzOi8vZ2l0aHViLmNvbS9tb3ppbGxhL3N3ZWV0LmpzL3dpa2kvZGVzaWduXG5cblwidXNlIHN0cmljdFwiO1xuXG5leHBvcnRzLl9fZXNNb2R1bGUgPSB0cnVlO1xuXG5mdW5jdGlvbiBfY2xhc3NDYWxsQ2hlY2soaW5zdGFuY2UsIENvbnN0cnVjdG9yKSB7IGlmICghKGluc3RhbmNlIGluc3RhbmNlb2YgQ29uc3RydWN0b3IpKSB7IHRocm93IG5ldyBUeXBlRXJyb3IoXCJDYW5ub3QgY2FsbCBhIGNsYXNzIGFzIGEgZnVuY3Rpb25cIik7IH0gfVxuXG52YXIgX3N0YXRlID0gX2RlcmVxXyhcIi4vc3RhdGVcIik7XG5cbnZhciBfdG9rZW50eXBlID0gX2RlcmVxXyhcIi4vdG9rZW50eXBlXCIpO1xuXG52YXIgX3doaXRlc3BhY2UgPSBfZGVyZXFfKFwiLi93aGl0ZXNwYWNlXCIpO1xuXG52YXIgVG9rQ29udGV4dCA9IGZ1bmN0aW9uIFRva0NvbnRleHQodG9rZW4sIGlzRXhwciwgcHJlc2VydmVTcGFjZSwgb3ZlcnJpZGUpIHtcbiAgX2NsYXNzQ2FsbENoZWNrKHRoaXMsIFRva0NvbnRleHQpO1xuXG4gIHRoaXMudG9rZW4gPSB0b2tlbjtcbiAgdGhpcy5pc0V4cHIgPSAhIWlzRXhwcjtcbiAgdGhpcy5wcmVzZXJ2ZVNwYWNlID0gISFwcmVzZXJ2ZVNwYWNlO1xuICB0aGlzLm92ZXJyaWRlID0gb3ZlcnJpZGU7XG59O1xuXG5leHBvcnRzLlRva0NvbnRleHQgPSBUb2tDb250ZXh0O1xudmFyIHR5cGVzID0ge1xuICBiX3N0YXQ6IG5ldyBUb2tDb250ZXh0KFwie1wiLCBmYWxzZSksXG4gIGJfZXhwcjogbmV3IFRva0NvbnRleHQoXCJ7XCIsIHRydWUpLFxuICBiX3RtcGw6IG5ldyBUb2tDb250ZXh0KFwiJHtcIiwgdHJ1ZSksXG4gIHBfc3RhdDogbmV3IFRva0NvbnRleHQoXCIoXCIsIGZhbHNlKSxcbiAgcF9leHByOiBuZXcgVG9rQ29udGV4dChcIihcIiwgdHJ1ZSksXG4gIHFfdG1wbDogbmV3IFRva0NvbnRleHQoXCJgXCIsIHRydWUsIHRydWUsIGZ1bmN0aW9uIChwKSB7XG4gICAgcmV0dXJuIHAucmVhZFRtcGxUb2tlbigpO1xuICB9KSxcbiAgZl9leHByOiBuZXcgVG9rQ29udGV4dChcImZ1bmN0aW9uXCIsIHRydWUpXG59O1xuXG5leHBvcnRzLnR5cGVzID0gdHlwZXM7XG52YXIgcHAgPSBfc3RhdGUuUGFyc2VyLnByb3RvdHlwZTtcblxucHAuaW5pdGlhbENvbnRleHQgPSBmdW5jdGlvbiAoKSB7XG4gIHJldHVybiBbdHlwZXMuYl9zdGF0XTtcbn07XG5cbnBwLmJyYWNlSXNCbG9jayA9IGZ1bmN0aW9uIChwcmV2VHlwZSkge1xuICBpZiAocHJldlR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuY29sb24pIHtcbiAgICB2YXIgX3BhcmVudCA9IHRoaXMuY3VyQ29udGV4dCgpO1xuICAgIGlmIChfcGFyZW50ID09PSB0eXBlcy5iX3N0YXQgfHwgX3BhcmVudCA9PT0gdHlwZXMuYl9leHByKSByZXR1cm4gIV9wYXJlbnQuaXNFeHByO1xuICB9XG4gIGlmIChwcmV2VHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5fcmV0dXJuKSByZXR1cm4gX3doaXRlc3BhY2UubGluZUJyZWFrLnRlc3QodGhpcy5pbnB1dC5zbGljZSh0aGlzLmxhc3RUb2tFbmQsIHRoaXMuc3RhcnQpKTtcbiAgaWYgKHByZXZUeXBlID09PSBfdG9rZW50eXBlLnR5cGVzLl9lbHNlIHx8IHByZXZUeXBlID09PSBfdG9rZW50eXBlLnR5cGVzLnNlbWkgfHwgcHJldlR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuZW9mIHx8IHByZXZUeXBlID09PSBfdG9rZW50eXBlLnR5cGVzLnBhcmVuUikgcmV0dXJuIHRydWU7XG4gIGlmIChwcmV2VHlwZSA9PSBfdG9rZW50eXBlLnR5cGVzLmJyYWNlTCkgcmV0dXJuIHRoaXMuY3VyQ29udGV4dCgpID09PSB0eXBlcy5iX3N0YXQ7XG4gIHJldHVybiAhdGhpcy5leHByQWxsb3dlZDtcbn07XG5cbnBwLnVwZGF0ZUNvbnRleHQgPSBmdW5jdGlvbiAocHJldlR5cGUpIHtcbiAgdmFyIHVwZGF0ZSA9IHVuZGVmaW5lZCxcbiAgICAgIHR5cGUgPSB0aGlzLnR5cGU7XG4gIGlmICh0eXBlLmtleXdvcmQgJiYgcHJldlR5cGUgPT0gX3Rva2VudHlwZS50eXBlcy5kb3QpIHRoaXMuZXhwckFsbG93ZWQgPSBmYWxzZTtlbHNlIGlmICh1cGRhdGUgPSB0eXBlLnVwZGF0ZUNvbnRleHQpIHVwZGF0ZS5jYWxsKHRoaXMsIHByZXZUeXBlKTtlbHNlIHRoaXMuZXhwckFsbG93ZWQgPSB0eXBlLmJlZm9yZUV4cHI7XG59O1xuXG4vLyBUb2tlbi1zcGVjaWZpYyBjb250ZXh0IHVwZGF0ZSBjb2RlXG5cbl90b2tlbnR5cGUudHlwZXMucGFyZW5SLnVwZGF0ZUNvbnRleHQgPSBfdG9rZW50eXBlLnR5cGVzLmJyYWNlUi51cGRhdGVDb250ZXh0ID0gZnVuY3Rpb24gKCkge1xuICBpZiAodGhpcy5jb250ZXh0Lmxlbmd0aCA9PSAxKSB7XG4gICAgdGhpcy5leHByQWxsb3dlZCA9IHRydWU7XG4gICAgcmV0dXJuO1xuICB9XG4gIHZhciBvdXQgPSB0aGlzLmNvbnRleHQucG9wKCk7XG4gIGlmIChvdXQgPT09IHR5cGVzLmJfc3RhdCAmJiB0aGlzLmN1ckNvbnRleHQoKSA9PT0gdHlwZXMuZl9leHByKSB7XG4gICAgdGhpcy5jb250ZXh0LnBvcCgpO1xuICAgIHRoaXMuZXhwckFsbG93ZWQgPSBmYWxzZTtcbiAgfSBlbHNlIGlmIChvdXQgPT09IHR5cGVzLmJfdG1wbCkge1xuICAgIHRoaXMuZXhwckFsbG93ZWQgPSB0cnVlO1xuICB9IGVsc2Uge1xuICAgIHRoaXMuZXhwckFsbG93ZWQgPSAhb3V0LmlzRXhwcjtcbiAgfVxufTtcblxuX3Rva2VudHlwZS50eXBlcy5icmFjZUwudXBkYXRlQ29udGV4dCA9IGZ1bmN0aW9uIChwcmV2VHlwZSkge1xuICB0aGlzLmNvbnRleHQucHVzaCh0aGlzLmJyYWNlSXNCbG9jayhwcmV2VHlwZSkgPyB0eXBlcy5iX3N0YXQgOiB0eXBlcy5iX2V4cHIpO1xuICB0aGlzLmV4cHJBbGxvd2VkID0gdHJ1ZTtcbn07XG5cbl90b2tlbnR5cGUudHlwZXMuZG9sbGFyQnJhY2VMLnVwZGF0ZUNvbnRleHQgPSBmdW5jdGlvbiAoKSB7XG4gIHRoaXMuY29udGV4dC5wdXNoKHR5cGVzLmJfdG1wbCk7XG4gIHRoaXMuZXhwckFsbG93ZWQgPSB0cnVlO1xufTtcblxuX3Rva2VudHlwZS50eXBlcy5wYXJlbkwudXBkYXRlQ29udGV4dCA9IGZ1bmN0aW9uIChwcmV2VHlwZSkge1xuICB2YXIgc3RhdGVtZW50UGFyZW5zID0gcHJldlR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuX2lmIHx8IHByZXZUeXBlID09PSBfdG9rZW50eXBlLnR5cGVzLl9mb3IgfHwgcHJldlR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuX3dpdGggfHwgcHJldlR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuX3doaWxlO1xuICB0aGlzLmNvbnRleHQucHVzaChzdGF0ZW1lbnRQYXJlbnMgPyB0eXBlcy5wX3N0YXQgOiB0eXBlcy5wX2V4cHIpO1xuICB0aGlzLmV4cHJBbGxvd2VkID0gdHJ1ZTtcbn07XG5cbl90b2tlbnR5cGUudHlwZXMuaW5jRGVjLnVwZGF0ZUNvbnRleHQgPSBmdW5jdGlvbiAoKSB7fTtcblxuX3Rva2VudHlwZS50eXBlcy5fZnVuY3Rpb24udXBkYXRlQ29udGV4dCA9IGZ1bmN0aW9uICgpIHtcbiAgaWYgKHRoaXMuY3VyQ29udGV4dCgpICE9PSB0eXBlcy5iX3N0YXQpIHRoaXMuY29udGV4dC5wdXNoKHR5cGVzLmZfZXhwcik7XG4gIHRoaXMuZXhwckFsbG93ZWQgPSBmYWxzZTtcbn07XG5cbl90b2tlbnR5cGUudHlwZXMuYmFja1F1b3RlLnVwZGF0ZUNvbnRleHQgPSBmdW5jdGlvbiAoKSB7XG4gIGlmICh0aGlzLmN1ckNvbnRleHQoKSA9PT0gdHlwZXMucV90bXBsKSB0aGlzLmNvbnRleHQucG9wKCk7ZWxzZSB0aGlzLmNvbnRleHQucHVzaCh0eXBlcy5xX3RtcGwpO1xuICB0aGlzLmV4cHJBbGxvd2VkID0gZmFsc2U7XG59O1xuXG4vLyB0b2tFeHByQWxsb3dlZCBzdGF5cyB1bmNoYW5nZWRcblxufSx7XCIuL3N0YXRlXCI6MTAsXCIuL3Rva2VudHlwZVwiOjE0LFwiLi93aGl0ZXNwYWNlXCI6MTZ9XSwxMzpbZnVuY3Rpb24oX2RlcmVxXyxtb2R1bGUsZXhwb3J0cyl7XG5cInVzZSBzdHJpY3RcIjtcblxuZXhwb3J0cy5fX2VzTW9kdWxlID0gdHJ1ZTtcblxuZnVuY3Rpb24gX2NsYXNzQ2FsbENoZWNrKGluc3RhbmNlLCBDb25zdHJ1Y3RvcikgeyBpZiAoIShpbnN0YW5jZSBpbnN0YW5jZW9mIENvbnN0cnVjdG9yKSkgeyB0aHJvdyBuZXcgVHlwZUVycm9yKFwiQ2Fubm90IGNhbGwgYSBjbGFzcyBhcyBhIGZ1bmN0aW9uXCIpOyB9IH1cblxudmFyIF9pZGVudGlmaWVyID0gX2RlcmVxXyhcIi4vaWRlbnRpZmllclwiKTtcblxudmFyIF90b2tlbnR5cGUgPSBfZGVyZXFfKFwiLi90b2tlbnR5cGVcIik7XG5cbnZhciBfc3RhdGUgPSBfZGVyZXFfKFwiLi9zdGF0ZVwiKTtcblxudmFyIF9sb2N1dGlsID0gX2RlcmVxXyhcIi4vbG9jdXRpbFwiKTtcblxudmFyIF93aGl0ZXNwYWNlID0gX2RlcmVxXyhcIi4vd2hpdGVzcGFjZVwiKTtcblxuLy8gT2JqZWN0IHR5cGUgdXNlZCB0byByZXByZXNlbnQgdG9rZW5zLiBOb3RlIHRoYXQgbm9ybWFsbHksIHRva2Vuc1xuLy8gc2ltcGx5IGV4aXN0IGFzIHByb3BlcnRpZXMgb24gdGhlIHBhcnNlciBvYmplY3QuIFRoaXMgaXMgb25seVxuLy8gdXNlZCBmb3IgdGhlIG9uVG9rZW4gY2FsbGJhY2sgYW5kIHRoZSBleHRlcm5hbCB0b2tlbml6ZXIuXG5cbnZhciBUb2tlbiA9IGZ1bmN0aW9uIFRva2VuKHApIHtcbiAgX2NsYXNzQ2FsbENoZWNrKHRoaXMsIFRva2VuKTtcblxuICB0aGlzLnR5cGUgPSBwLnR5cGU7XG4gIHRoaXMudmFsdWUgPSBwLnZhbHVlO1xuICB0aGlzLnN0YXJ0ID0gcC5zdGFydDtcbiAgdGhpcy5lbmQgPSBwLmVuZDtcbiAgaWYgKHAub3B0aW9ucy5sb2NhdGlvbnMpIHRoaXMubG9jID0gbmV3IF9sb2N1dGlsLlNvdXJjZUxvY2F0aW9uKHAsIHAuc3RhcnRMb2MsIHAuZW5kTG9jKTtcbiAgaWYgKHAub3B0aW9ucy5yYW5nZXMpIHRoaXMucmFuZ2UgPSBbcC5zdGFydCwgcC5lbmRdO1xufTtcblxuZXhwb3J0cy5Ub2tlbiA9IFRva2VuO1xuXG4vLyAjIyBUb2tlbml6ZXJcblxudmFyIHBwID0gX3N0YXRlLlBhcnNlci5wcm90b3R5cGU7XG5cbi8vIEFyZSB3ZSBydW5uaW5nIHVuZGVyIFJoaW5vP1xudmFyIGlzUmhpbm8gPSB0eXBlb2YgUGFja2FnZXMgPT0gXCJvYmplY3RcIiAmJiBPYmplY3QucHJvdG90eXBlLnRvU3RyaW5nLmNhbGwoUGFja2FnZXMpID09IFwiW29iamVjdCBKYXZhUGFja2FnZV1cIjtcblxuLy8gTW92ZSB0byB0aGUgbmV4dCB0b2tlblxuXG5wcC5uZXh0ID0gZnVuY3Rpb24gKCkge1xuICBpZiAodGhpcy5vcHRpb25zLm9uVG9rZW4pIHRoaXMub3B0aW9ucy5vblRva2VuKG5ldyBUb2tlbih0aGlzKSk7XG5cbiAgdGhpcy5sYXN0VG9rRW5kID0gdGhpcy5lbmQ7XG4gIHRoaXMubGFzdFRva1N0YXJ0ID0gdGhpcy5zdGFydDtcbiAgdGhpcy5sYXN0VG9rRW5kTG9jID0gdGhpcy5lbmRMb2M7XG4gIHRoaXMubGFzdFRva1N0YXJ0TG9jID0gdGhpcy5zdGFydExvYztcbiAgdGhpcy5uZXh0VG9rZW4oKTtcbn07XG5cbnBwLmdldFRva2VuID0gZnVuY3Rpb24gKCkge1xuICB0aGlzLm5leHQoKTtcbiAgcmV0dXJuIG5ldyBUb2tlbih0aGlzKTtcbn07XG5cbi8vIElmIHdlJ3JlIGluIGFuIEVTNiBlbnZpcm9ubWVudCwgbWFrZSBwYXJzZXJzIGl0ZXJhYmxlXG5pZiAodHlwZW9mIFN5bWJvbCAhPT0gXCJ1bmRlZmluZWRcIikgcHBbU3ltYm9sLml0ZXJhdG9yXSA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIHNlbGYgPSB0aGlzO1xuICByZXR1cm4geyBuZXh0OiBmdW5jdGlvbiBuZXh0KCkge1xuICAgICAgdmFyIHRva2VuID0gc2VsZi5nZXRUb2tlbigpO1xuICAgICAgcmV0dXJuIHtcbiAgICAgICAgZG9uZTogdG9rZW4udHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5lb2YsXG4gICAgICAgIHZhbHVlOiB0b2tlblxuICAgICAgfTtcbiAgICB9IH07XG59O1xuXG4vLyBUb2dnbGUgc3RyaWN0IG1vZGUuIFJlLXJlYWRzIHRoZSBuZXh0IG51bWJlciBvciBzdHJpbmcgdG8gcGxlYXNlXG4vLyBwZWRhbnRpYyB0ZXN0cyAoYFwidXNlIHN0cmljdFwiOyAwMTA7YCBzaG91bGQgZmFpbCkuXG5cbnBwLnNldFN0cmljdCA9IGZ1bmN0aW9uIChzdHJpY3QpIHtcbiAgdGhpcy5zdHJpY3QgPSBzdHJpY3Q7XG4gIGlmICh0aGlzLnR5cGUgIT09IF90b2tlbnR5cGUudHlwZXMubnVtICYmIHRoaXMudHlwZSAhPT0gX3Rva2VudHlwZS50eXBlcy5zdHJpbmcpIHJldHVybjtcbiAgdGhpcy5wb3MgPSB0aGlzLnN0YXJ0O1xuICBpZiAodGhpcy5vcHRpb25zLmxvY2F0aW9ucykge1xuICAgIHdoaWxlICh0aGlzLnBvcyA8IHRoaXMubGluZVN0YXJ0KSB7XG4gICAgICB0aGlzLmxpbmVTdGFydCA9IHRoaXMuaW5wdXQubGFzdEluZGV4T2YoXCJcXG5cIiwgdGhpcy5saW5lU3RhcnQgLSAyKSArIDE7XG4gICAgICAtLXRoaXMuY3VyTGluZTtcbiAgICB9XG4gIH1cbiAgdGhpcy5uZXh0VG9rZW4oKTtcbn07XG5cbnBwLmN1ckNvbnRleHQgPSBmdW5jdGlvbiAoKSB7XG4gIHJldHVybiB0aGlzLmNvbnRleHRbdGhpcy5jb250ZXh0Lmxlbmd0aCAtIDFdO1xufTtcblxuLy8gUmVhZCBhIHNpbmdsZSB0b2tlbiwgdXBkYXRpbmcgdGhlIHBhcnNlciBvYmplY3QncyB0b2tlbi1yZWxhdGVkXG4vLyBwcm9wZXJ0aWVzLlxuXG5wcC5uZXh0VG9rZW4gPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBjdXJDb250ZXh0ID0gdGhpcy5jdXJDb250ZXh0KCk7XG4gIGlmICghY3VyQ29udGV4dCB8fCAhY3VyQ29udGV4dC5wcmVzZXJ2ZVNwYWNlKSB0aGlzLnNraXBTcGFjZSgpO1xuXG4gIHRoaXMuc3RhcnQgPSB0aGlzLnBvcztcbiAgaWYgKHRoaXMub3B0aW9ucy5sb2NhdGlvbnMpIHRoaXMuc3RhcnRMb2MgPSB0aGlzLmN1clBvc2l0aW9uKCk7XG4gIGlmICh0aGlzLnBvcyA+PSB0aGlzLmlucHV0Lmxlbmd0aCkgcmV0dXJuIHRoaXMuZmluaXNoVG9rZW4oX3Rva2VudHlwZS50eXBlcy5lb2YpO1xuXG4gIGlmIChjdXJDb250ZXh0Lm92ZXJyaWRlKSByZXR1cm4gY3VyQ29udGV4dC5vdmVycmlkZSh0aGlzKTtlbHNlIHRoaXMucmVhZFRva2VuKHRoaXMuZnVsbENoYXJDb2RlQXRQb3MoKSk7XG59O1xuXG5wcC5yZWFkVG9rZW4gPSBmdW5jdGlvbiAoY29kZSkge1xuICAvLyBJZGVudGlmaWVyIG9yIGtleXdvcmQuICdcXHVYWFhYJyBzZXF1ZW5jZXMgYXJlIGFsbG93ZWQgaW5cbiAgLy8gaWRlbnRpZmllcnMsIHNvICdcXCcgYWxzbyBkaXNwYXRjaGVzIHRvIHRoYXQuXG4gIGlmIChfaWRlbnRpZmllci5pc0lkZW50aWZpZXJTdGFydChjb2RlLCB0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNikgfHwgY29kZSA9PT0gOTIgLyogJ1xcJyAqLykgcmV0dXJuIHRoaXMucmVhZFdvcmQoKTtcblxuICByZXR1cm4gdGhpcy5nZXRUb2tlbkZyb21Db2RlKGNvZGUpO1xufTtcblxucHAuZnVsbENoYXJDb2RlQXRQb3MgPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBjb2RlID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zKTtcbiAgaWYgKGNvZGUgPD0gMHhkN2ZmIHx8IGNvZGUgPj0gMHhlMDAwKSByZXR1cm4gY29kZTtcbiAgdmFyIG5leHQgPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAxKTtcbiAgcmV0dXJuIChjb2RlIDw8IDEwKSArIG5leHQgLSAweDM1ZmRjMDA7XG59O1xuXG5wcC5za2lwQmxvY2tDb21tZW50ID0gZnVuY3Rpb24gKCkge1xuICB2YXIgc3RhcnRMb2MgPSB0aGlzLm9wdGlvbnMub25Db21tZW50ICYmIHRoaXMuY3VyUG9zaXRpb24oKTtcbiAgdmFyIHN0YXJ0ID0gdGhpcy5wb3MsXG4gICAgICBlbmQgPSB0aGlzLmlucHV0LmluZGV4T2YoXCIqL1wiLCB0aGlzLnBvcyArPSAyKTtcbiAgaWYgKGVuZCA9PT0gLTEpIHRoaXMucmFpc2UodGhpcy5wb3MgLSAyLCBcIlVudGVybWluYXRlZCBjb21tZW50XCIpO1xuICB0aGlzLnBvcyA9IGVuZCArIDI7XG4gIGlmICh0aGlzLm9wdGlvbnMubG9jYXRpb25zKSB7XG4gICAgX3doaXRlc3BhY2UubGluZUJyZWFrRy5sYXN0SW5kZXggPSBzdGFydDtcbiAgICB2YXIgbWF0Y2ggPSB1bmRlZmluZWQ7XG4gICAgd2hpbGUgKChtYXRjaCA9IF93aGl0ZXNwYWNlLmxpbmVCcmVha0cuZXhlYyh0aGlzLmlucHV0KSkgJiYgbWF0Y2guaW5kZXggPCB0aGlzLnBvcykge1xuICAgICAgKyt0aGlzLmN1ckxpbmU7XG4gICAgICB0aGlzLmxpbmVTdGFydCA9IG1hdGNoLmluZGV4ICsgbWF0Y2hbMF0ubGVuZ3RoO1xuICAgIH1cbiAgfVxuICBpZiAodGhpcy5vcHRpb25zLm9uQ29tbWVudCkgdGhpcy5vcHRpb25zLm9uQ29tbWVudCh0cnVlLCB0aGlzLmlucHV0LnNsaWNlKHN0YXJ0ICsgMiwgZW5kKSwgc3RhcnQsIHRoaXMucG9zLCBzdGFydExvYywgdGhpcy5jdXJQb3NpdGlvbigpKTtcbn07XG5cbnBwLnNraXBMaW5lQ29tbWVudCA9IGZ1bmN0aW9uIChzdGFydFNraXApIHtcbiAgdmFyIHN0YXJ0ID0gdGhpcy5wb3M7XG4gIHZhciBzdGFydExvYyA9IHRoaXMub3B0aW9ucy5vbkNvbW1lbnQgJiYgdGhpcy5jdXJQb3NpdGlvbigpO1xuICB2YXIgY2ggPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKz0gc3RhcnRTa2lwKTtcbiAgd2hpbGUgKHRoaXMucG9zIDwgdGhpcy5pbnB1dC5sZW5ndGggJiYgY2ggIT09IDEwICYmIGNoICE9PSAxMyAmJiBjaCAhPT0gODIzMiAmJiBjaCAhPT0gODIzMykge1xuICAgICsrdGhpcy5wb3M7XG4gICAgY2ggPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MpO1xuICB9XG4gIGlmICh0aGlzLm9wdGlvbnMub25Db21tZW50KSB0aGlzLm9wdGlvbnMub25Db21tZW50KGZhbHNlLCB0aGlzLmlucHV0LnNsaWNlKHN0YXJ0ICsgc3RhcnRTa2lwLCB0aGlzLnBvcyksIHN0YXJ0LCB0aGlzLnBvcywgc3RhcnRMb2MsIHRoaXMuY3VyUG9zaXRpb24oKSk7XG59O1xuXG4vLyBDYWxsZWQgYXQgdGhlIHN0YXJ0IG9mIHRoZSBwYXJzZSBhbmQgYWZ0ZXIgZXZlcnkgdG9rZW4uIFNraXBzXG4vLyB3aGl0ZXNwYWNlIGFuZCBjb21tZW50cywgYW5kLlxuXG5wcC5za2lwU3BhY2UgPSBmdW5jdGlvbiAoKSB7XG4gIGxvb3A6IHdoaWxlICh0aGlzLnBvcyA8IHRoaXMuaW5wdXQubGVuZ3RoKSB7XG4gICAgdmFyIGNoID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zKTtcbiAgICBzd2l0Y2ggKGNoKSB7XG4gICAgICBjYXNlIDMyOmNhc2UgMTYwOlxuICAgICAgICAvLyAnICdcbiAgICAgICAgKyt0aGlzLnBvcztcbiAgICAgICAgYnJlYWs7XG4gICAgICBjYXNlIDEzOlxuICAgICAgICBpZiAodGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMSkgPT09IDEwKSB7XG4gICAgICAgICAgKyt0aGlzLnBvcztcbiAgICAgICAgfVxuICAgICAgY2FzZSAxMDpjYXNlIDgyMzI6Y2FzZSA4MjMzOlxuICAgICAgICArK3RoaXMucG9zO1xuICAgICAgICBpZiAodGhpcy5vcHRpb25zLmxvY2F0aW9ucykge1xuICAgICAgICAgICsrdGhpcy5jdXJMaW5lO1xuICAgICAgICAgIHRoaXMubGluZVN0YXJ0ID0gdGhpcy5wb3M7XG4gICAgICAgIH1cbiAgICAgICAgYnJlYWs7XG4gICAgICBjYXNlIDQ3OlxuICAgICAgICAvLyAnLydcbiAgICAgICAgc3dpdGNoICh0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAxKSkge1xuICAgICAgICAgIGNhc2UgNDI6XG4gICAgICAgICAgICAvLyAnKidcbiAgICAgICAgICAgIHRoaXMuc2tpcEJsb2NrQ29tbWVudCgpO1xuICAgICAgICAgICAgYnJlYWs7XG4gICAgICAgICAgY2FzZSA0NzpcbiAgICAgICAgICAgIHRoaXMuc2tpcExpbmVDb21tZW50KDIpO1xuICAgICAgICAgICAgYnJlYWs7XG4gICAgICAgICAgZGVmYXVsdDpcbiAgICAgICAgICAgIGJyZWFrIGxvb3A7XG4gICAgICAgIH1cbiAgICAgICAgYnJlYWs7XG4gICAgICBkZWZhdWx0OlxuICAgICAgICBpZiAoY2ggPiA4ICYmIGNoIDwgMTQgfHwgY2ggPj0gNTc2MCAmJiBfd2hpdGVzcGFjZS5ub25BU0NJSXdoaXRlc3BhY2UudGVzdChTdHJpbmcuZnJvbUNoYXJDb2RlKGNoKSkpIHtcbiAgICAgICAgICArK3RoaXMucG9zO1xuICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgIGJyZWFrIGxvb3A7XG4gICAgICAgIH1cbiAgICB9XG4gIH1cbn07XG5cbi8vIENhbGxlZCBhdCB0aGUgZW5kIG9mIGV2ZXJ5IHRva2VuLiBTZXRzIGBlbmRgLCBgdmFsYCwgYW5kXG4vLyBtYWludGFpbnMgYGNvbnRleHRgIGFuZCBgZXhwckFsbG93ZWRgLCBhbmQgc2tpcHMgdGhlIHNwYWNlIGFmdGVyXG4vLyB0aGUgdG9rZW4sIHNvIHRoYXQgdGhlIG5leHQgb25lJ3MgYHN0YXJ0YCB3aWxsIHBvaW50IGF0IHRoZVxuLy8gcmlnaHQgcG9zaXRpb24uXG5cbnBwLmZpbmlzaFRva2VuID0gZnVuY3Rpb24gKHR5cGUsIHZhbCkge1xuICB0aGlzLmVuZCA9IHRoaXMucG9zO1xuICBpZiAodGhpcy5vcHRpb25zLmxvY2F0aW9ucykgdGhpcy5lbmRMb2MgPSB0aGlzLmN1clBvc2l0aW9uKCk7XG4gIHZhciBwcmV2VHlwZSA9IHRoaXMudHlwZTtcbiAgdGhpcy50eXBlID0gdHlwZTtcbiAgdGhpcy52YWx1ZSA9IHZhbDtcblxuICB0aGlzLnVwZGF0ZUNvbnRleHQocHJldlR5cGUpO1xufTtcblxuLy8gIyMjIFRva2VuIHJlYWRpbmdcblxuLy8gVGhpcyBpcyB0aGUgZnVuY3Rpb24gdGhhdCBpcyBjYWxsZWQgdG8gZmV0Y2ggdGhlIG5leHQgdG9rZW4uIEl0XG4vLyBpcyBzb21ld2hhdCBvYnNjdXJlLCBiZWNhdXNlIGl0IHdvcmtzIGluIGNoYXJhY3RlciBjb2RlcyByYXRoZXJcbi8vIHRoYW4gY2hhcmFjdGVycywgYW5kIGJlY2F1c2Ugb3BlcmF0b3IgcGFyc2luZyBoYXMgYmVlbiBpbmxpbmVkXG4vLyBpbnRvIGl0LlxuLy9cbi8vIEFsbCBpbiB0aGUgbmFtZSBvZiBzcGVlZC5cbi8vXG5wcC5yZWFkVG9rZW5fZG90ID0gZnVuY3Rpb24gKCkge1xuICB2YXIgbmV4dCA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIDEpO1xuICBpZiAobmV4dCA+PSA0OCAmJiBuZXh0IDw9IDU3KSByZXR1cm4gdGhpcy5yZWFkTnVtYmVyKHRydWUpO1xuICB2YXIgbmV4dDIgPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAyKTtcbiAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2ICYmIG5leHQgPT09IDQ2ICYmIG5leHQyID09PSA0Nikge1xuICAgIC8vIDQ2ID0gZG90ICcuJ1xuICAgIHRoaXMucG9zICs9IDM7XG4gICAgcmV0dXJuIHRoaXMuZmluaXNoVG9rZW4oX3Rva2VudHlwZS50eXBlcy5lbGxpcHNpcyk7XG4gIH0gZWxzZSB7XG4gICAgKyt0aGlzLnBvcztcbiAgICByZXR1cm4gdGhpcy5maW5pc2hUb2tlbihfdG9rZW50eXBlLnR5cGVzLmRvdCk7XG4gIH1cbn07XG5cbnBwLnJlYWRUb2tlbl9zbGFzaCA9IGZ1bmN0aW9uICgpIHtcbiAgLy8gJy8nXG4gIHZhciBuZXh0ID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMSk7XG4gIGlmICh0aGlzLmV4cHJBbGxvd2VkKSB7XG4gICAgKyt0aGlzLnBvcztyZXR1cm4gdGhpcy5yZWFkUmVnZXhwKCk7XG4gIH1cbiAgaWYgKG5leHQgPT09IDYxKSByZXR1cm4gdGhpcy5maW5pc2hPcChfdG9rZW50eXBlLnR5cGVzLmFzc2lnbiwgMik7XG4gIHJldHVybiB0aGlzLmZpbmlzaE9wKF90b2tlbnR5cGUudHlwZXMuc2xhc2gsIDEpO1xufTtcblxucHAucmVhZFRva2VuX211bHRfbW9kdWxvID0gZnVuY3Rpb24gKGNvZGUpIHtcbiAgLy8gJyUqJ1xuICB2YXIgbmV4dCA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIDEpO1xuICBpZiAobmV4dCA9PT0gNjEpIHJldHVybiB0aGlzLmZpbmlzaE9wKF90b2tlbnR5cGUudHlwZXMuYXNzaWduLCAyKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoT3AoY29kZSA9PT0gNDIgPyBfdG9rZW50eXBlLnR5cGVzLnN0YXIgOiBfdG9rZW50eXBlLnR5cGVzLm1vZHVsbywgMSk7XG59O1xuXG5wcC5yZWFkVG9rZW5fcGlwZV9hbXAgPSBmdW5jdGlvbiAoY29kZSkge1xuICAvLyAnfCYnXG4gIHZhciBuZXh0ID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMSk7XG4gIGlmIChuZXh0ID09PSBjb2RlKSByZXR1cm4gdGhpcy5maW5pc2hPcChjb2RlID09PSAxMjQgPyBfdG9rZW50eXBlLnR5cGVzLmxvZ2ljYWxPUiA6IF90b2tlbnR5cGUudHlwZXMubG9naWNhbEFORCwgMik7XG4gIGlmIChuZXh0ID09PSA2MSkgcmV0dXJuIHRoaXMuZmluaXNoT3AoX3Rva2VudHlwZS50eXBlcy5hc3NpZ24sIDIpO1xuICByZXR1cm4gdGhpcy5maW5pc2hPcChjb2RlID09PSAxMjQgPyBfdG9rZW50eXBlLnR5cGVzLmJpdHdpc2VPUiA6IF90b2tlbnR5cGUudHlwZXMuYml0d2lzZUFORCwgMSk7XG59O1xuXG5wcC5yZWFkVG9rZW5fY2FyZXQgPSBmdW5jdGlvbiAoKSB7XG4gIC8vICdeJ1xuICB2YXIgbmV4dCA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIDEpO1xuICBpZiAobmV4dCA9PT0gNjEpIHJldHVybiB0aGlzLmZpbmlzaE9wKF90b2tlbnR5cGUudHlwZXMuYXNzaWduLCAyKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoT3AoX3Rva2VudHlwZS50eXBlcy5iaXR3aXNlWE9SLCAxKTtcbn07XG5cbnBwLnJlYWRUb2tlbl9wbHVzX21pbiA9IGZ1bmN0aW9uIChjb2RlKSB7XG4gIC8vICcrLSdcbiAgdmFyIG5leHQgPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAxKTtcbiAgaWYgKG5leHQgPT09IGNvZGUpIHtcbiAgICBpZiAobmV4dCA9PSA0NSAmJiB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAyKSA9PSA2MiAmJiBfd2hpdGVzcGFjZS5saW5lQnJlYWsudGVzdCh0aGlzLmlucHV0LnNsaWNlKHRoaXMubGFzdFRva0VuZCwgdGhpcy5wb3MpKSkge1xuICAgICAgLy8gQSBgLS0+YCBsaW5lIGNvbW1lbnRcbiAgICAgIHRoaXMuc2tpcExpbmVDb21tZW50KDMpO1xuICAgICAgdGhpcy5za2lwU3BhY2UoKTtcbiAgICAgIHJldHVybiB0aGlzLm5leHRUb2tlbigpO1xuICAgIH1cbiAgICByZXR1cm4gdGhpcy5maW5pc2hPcChfdG9rZW50eXBlLnR5cGVzLmluY0RlYywgMik7XG4gIH1cbiAgaWYgKG5leHQgPT09IDYxKSByZXR1cm4gdGhpcy5maW5pc2hPcChfdG9rZW50eXBlLnR5cGVzLmFzc2lnbiwgMik7XG4gIHJldHVybiB0aGlzLmZpbmlzaE9wKF90b2tlbnR5cGUudHlwZXMucGx1c01pbiwgMSk7XG59O1xuXG5wcC5yZWFkVG9rZW5fbHRfZ3QgPSBmdW5jdGlvbiAoY29kZSkge1xuICAvLyAnPD4nXG4gIHZhciBuZXh0ID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMSk7XG4gIHZhciBzaXplID0gMTtcbiAgaWYgKG5leHQgPT09IGNvZGUpIHtcbiAgICBzaXplID0gY29kZSA9PT0gNjIgJiYgdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMikgPT09IDYyID8gMyA6IDI7XG4gICAgaWYgKHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIHNpemUpID09PSA2MSkgcmV0dXJuIHRoaXMuZmluaXNoT3AoX3Rva2VudHlwZS50eXBlcy5hc3NpZ24sIHNpemUgKyAxKTtcbiAgICByZXR1cm4gdGhpcy5maW5pc2hPcChfdG9rZW50eXBlLnR5cGVzLmJpdFNoaWZ0LCBzaXplKTtcbiAgfVxuICBpZiAobmV4dCA9PSAzMyAmJiBjb2RlID09IDYwICYmIHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIDIpID09IDQ1ICYmIHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIDMpID09IDQ1KSB7XG4gICAgaWYgKHRoaXMuaW5Nb2R1bGUpIHRoaXMudW5leHBlY3RlZCgpO1xuICAgIC8vIGA8IS0tYCwgYW4gWE1MLXN0eWxlIGNvbW1lbnQgdGhhdCBzaG91bGQgYmUgaW50ZXJwcmV0ZWQgYXMgYSBsaW5lIGNvbW1lbnRcbiAgICB0aGlzLnNraXBMaW5lQ29tbWVudCg0KTtcbiAgICB0aGlzLnNraXBTcGFjZSgpO1xuICAgIHJldHVybiB0aGlzLm5leHRUb2tlbigpO1xuICB9XG4gIGlmIChuZXh0ID09PSA2MSkgc2l6ZSA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIDIpID09PSA2MSA/IDMgOiAyO1xuICByZXR1cm4gdGhpcy5maW5pc2hPcChfdG9rZW50eXBlLnR5cGVzLnJlbGF0aW9uYWwsIHNpemUpO1xufTtcblxucHAucmVhZFRva2VuX2VxX2V4Y2wgPSBmdW5jdGlvbiAoY29kZSkge1xuICAvLyAnPSEnXG4gIHZhciBuZXh0ID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMSk7XG4gIGlmIChuZXh0ID09PSA2MSkgcmV0dXJuIHRoaXMuZmluaXNoT3AoX3Rva2VudHlwZS50eXBlcy5lcXVhbGl0eSwgdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMikgPT09IDYxID8gMyA6IDIpO1xuICBpZiAoY29kZSA9PT0gNjEgJiYgbmV4dCA9PT0gNjIgJiYgdGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYpIHtcbiAgICAvLyAnPT4nXG4gICAgdGhpcy5wb3MgKz0gMjtcbiAgICByZXR1cm4gdGhpcy5maW5pc2hUb2tlbihfdG9rZW50eXBlLnR5cGVzLmFycm93KTtcbiAgfVxuICByZXR1cm4gdGhpcy5maW5pc2hPcChjb2RlID09PSA2MSA/IF90b2tlbnR5cGUudHlwZXMuZXEgOiBfdG9rZW50eXBlLnR5cGVzLnByZWZpeCwgMSk7XG59O1xuXG5wcC5nZXRUb2tlbkZyb21Db2RlID0gZnVuY3Rpb24gKGNvZGUpIHtcbiAgc3dpdGNoIChjb2RlKSB7XG4gICAgLy8gVGhlIGludGVycHJldGF0aW9uIG9mIGEgZG90IGRlcGVuZHMgb24gd2hldGhlciBpdCBpcyBmb2xsb3dlZFxuICAgIC8vIGJ5IGEgZGlnaXQgb3IgYW5vdGhlciB0d28gZG90cy5cbiAgICBjYXNlIDQ2OlxuICAgICAgLy8gJy4nXG4gICAgICByZXR1cm4gdGhpcy5yZWFkVG9rZW5fZG90KCk7XG5cbiAgICAvLyBQdW5jdHVhdGlvbiB0b2tlbnMuXG4gICAgY2FzZSA0MDpcbiAgICAgICsrdGhpcy5wb3M7cmV0dXJuIHRoaXMuZmluaXNoVG9rZW4oX3Rva2VudHlwZS50eXBlcy5wYXJlbkwpO1xuICAgIGNhc2UgNDE6XG4gICAgICArK3RoaXMucG9zO3JldHVybiB0aGlzLmZpbmlzaFRva2VuKF90b2tlbnR5cGUudHlwZXMucGFyZW5SKTtcbiAgICBjYXNlIDU5OlxuICAgICAgKyt0aGlzLnBvcztyZXR1cm4gdGhpcy5maW5pc2hUb2tlbihfdG9rZW50eXBlLnR5cGVzLnNlbWkpO1xuICAgIGNhc2UgNDQ6XG4gICAgICArK3RoaXMucG9zO3JldHVybiB0aGlzLmZpbmlzaFRva2VuKF90b2tlbnR5cGUudHlwZXMuY29tbWEpO1xuICAgIGNhc2UgOTE6XG4gICAgICArK3RoaXMucG9zO3JldHVybiB0aGlzLmZpbmlzaFRva2VuKF90b2tlbnR5cGUudHlwZXMuYnJhY2tldEwpO1xuICAgIGNhc2UgOTM6XG4gICAgICArK3RoaXMucG9zO3JldHVybiB0aGlzLmZpbmlzaFRva2VuKF90b2tlbnR5cGUudHlwZXMuYnJhY2tldFIpO1xuICAgIGNhc2UgMTIzOlxuICAgICAgKyt0aGlzLnBvcztyZXR1cm4gdGhpcy5maW5pc2hUb2tlbihfdG9rZW50eXBlLnR5cGVzLmJyYWNlTCk7XG4gICAgY2FzZSAxMjU6XG4gICAgICArK3RoaXMucG9zO3JldHVybiB0aGlzLmZpbmlzaFRva2VuKF90b2tlbnR5cGUudHlwZXMuYnJhY2VSKTtcbiAgICBjYXNlIDU4OlxuICAgICAgKyt0aGlzLnBvcztyZXR1cm4gdGhpcy5maW5pc2hUb2tlbihfdG9rZW50eXBlLnR5cGVzLmNvbG9uKTtcbiAgICBjYXNlIDYzOlxuICAgICAgKyt0aGlzLnBvcztyZXR1cm4gdGhpcy5maW5pc2hUb2tlbihfdG9rZW50eXBlLnR5cGVzLnF1ZXN0aW9uKTtcblxuICAgIGNhc2UgOTY6XG4gICAgICAvLyAnYCdcbiAgICAgIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPCA2KSBicmVhaztcbiAgICAgICsrdGhpcy5wb3M7XG4gICAgICByZXR1cm4gdGhpcy5maW5pc2hUb2tlbihfdG9rZW50eXBlLnR5cGVzLmJhY2tRdW90ZSk7XG5cbiAgICBjYXNlIDQ4OlxuICAgICAgLy8gJzAnXG4gICAgICB2YXIgbmV4dCA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIDEpO1xuICAgICAgaWYgKG5leHQgPT09IDEyMCB8fCBuZXh0ID09PSA4OCkgcmV0dXJuIHRoaXMucmVhZFJhZGl4TnVtYmVyKDE2KTsgLy8gJzB4JywgJzBYJyAtIGhleCBudW1iZXJcbiAgICAgIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNikge1xuICAgICAgICBpZiAobmV4dCA9PT0gMTExIHx8IG5leHQgPT09IDc5KSByZXR1cm4gdGhpcy5yZWFkUmFkaXhOdW1iZXIoOCk7IC8vICcwbycsICcwTycgLSBvY3RhbCBudW1iZXJcbiAgICAgICAgaWYgKG5leHQgPT09IDk4IHx8IG5leHQgPT09IDY2KSByZXR1cm4gdGhpcy5yZWFkUmFkaXhOdW1iZXIoMik7IC8vICcwYicsICcwQicgLSBiaW5hcnkgbnVtYmVyXG4gICAgICB9XG4gICAgLy8gQW55dGhpbmcgZWxzZSBiZWdpbm5pbmcgd2l0aCBhIGRpZ2l0IGlzIGFuIGludGVnZXIsIG9jdGFsXG4gICAgLy8gbnVtYmVyLCBvciBmbG9hdC5cbiAgICBjYXNlIDQ5OmNhc2UgNTA6Y2FzZSA1MTpjYXNlIDUyOmNhc2UgNTM6Y2FzZSA1NDpjYXNlIDU1OmNhc2UgNTY6Y2FzZSA1NzpcbiAgICAgIC8vIDEtOVxuICAgICAgcmV0dXJuIHRoaXMucmVhZE51bWJlcihmYWxzZSk7XG5cbiAgICAvLyBRdW90ZXMgcHJvZHVjZSBzdHJpbmdzLlxuICAgIGNhc2UgMzQ6Y2FzZSAzOTpcbiAgICAgIC8vICdcIicsIFwiJ1wiXG4gICAgICByZXR1cm4gdGhpcy5yZWFkU3RyaW5nKGNvZGUpO1xuXG4gICAgLy8gT3BlcmF0b3JzIGFyZSBwYXJzZWQgaW5saW5lIGluIHRpbnkgc3RhdGUgbWFjaGluZXMuICc9JyAoNjEpIGlzXG4gICAgLy8gb2Z0ZW4gcmVmZXJyZWQgdG8uIGBmaW5pc2hPcGAgc2ltcGx5IHNraXBzIHRoZSBhbW91bnQgb2ZcbiAgICAvLyBjaGFyYWN0ZXJzIGl0IGlzIGdpdmVuIGFzIHNlY29uZCBhcmd1bWVudCwgYW5kIHJldHVybnMgYSB0b2tlblxuICAgIC8vIG9mIHRoZSB0eXBlIGdpdmVuIGJ5IGl0cyBmaXJzdCBhcmd1bWVudC5cblxuICAgIGNhc2UgNDc6XG4gICAgICAvLyAnLydcbiAgICAgIHJldHVybiB0aGlzLnJlYWRUb2tlbl9zbGFzaCgpO1xuXG4gICAgY2FzZSAzNzpjYXNlIDQyOlxuICAgICAgLy8gJyUqJ1xuICAgICAgcmV0dXJuIHRoaXMucmVhZFRva2VuX211bHRfbW9kdWxvKGNvZGUpO1xuXG4gICAgY2FzZSAxMjQ6Y2FzZSAzODpcbiAgICAgIC8vICd8JidcbiAgICAgIHJldHVybiB0aGlzLnJlYWRUb2tlbl9waXBlX2FtcChjb2RlKTtcblxuICAgIGNhc2UgOTQ6XG4gICAgICAvLyAnXidcbiAgICAgIHJldHVybiB0aGlzLnJlYWRUb2tlbl9jYXJldCgpO1xuXG4gICAgY2FzZSA0MzpjYXNlIDQ1OlxuICAgICAgLy8gJystJ1xuICAgICAgcmV0dXJuIHRoaXMucmVhZFRva2VuX3BsdXNfbWluKGNvZGUpO1xuXG4gICAgY2FzZSA2MDpjYXNlIDYyOlxuICAgICAgLy8gJzw+J1xuICAgICAgcmV0dXJuIHRoaXMucmVhZFRva2VuX2x0X2d0KGNvZGUpO1xuXG4gICAgY2FzZSA2MTpjYXNlIDMzOlxuICAgICAgLy8gJz0hJ1xuICAgICAgcmV0dXJuIHRoaXMucmVhZFRva2VuX2VxX2V4Y2woY29kZSk7XG5cbiAgICBjYXNlIDEyNjpcbiAgICAgIC8vICd+J1xuICAgICAgcmV0dXJuIHRoaXMuZmluaXNoT3AoX3Rva2VudHlwZS50eXBlcy5wcmVmaXgsIDEpO1xuICB9XG5cbiAgdGhpcy5yYWlzZSh0aGlzLnBvcywgXCJVbmV4cGVjdGVkIGNoYXJhY3RlciAnXCIgKyBjb2RlUG9pbnRUb1N0cmluZyhjb2RlKSArIFwiJ1wiKTtcbn07XG5cbnBwLmZpbmlzaE9wID0gZnVuY3Rpb24gKHR5cGUsIHNpemUpIHtcbiAgdmFyIHN0ciA9IHRoaXMuaW5wdXQuc2xpY2UodGhpcy5wb3MsIHRoaXMucG9zICsgc2l6ZSk7XG4gIHRoaXMucG9zICs9IHNpemU7XG4gIHJldHVybiB0aGlzLmZpbmlzaFRva2VuKHR5cGUsIHN0cik7XG59O1xuXG4vLyBQYXJzZSBhIHJlZ3VsYXIgZXhwcmVzc2lvbi4gU29tZSBjb250ZXh0LWF3YXJlbmVzcyBpcyBuZWNlc3NhcnksXG4vLyBzaW5jZSBhICcvJyBpbnNpZGUgYSAnW10nIHNldCBkb2VzIG5vdCBlbmQgdGhlIGV4cHJlc3Npb24uXG5cbmZ1bmN0aW9uIHRyeUNyZWF0ZVJlZ2V4cChzcmMsIGZsYWdzLCB0aHJvd0Vycm9yQXQpIHtcbiAgdHJ5IHtcbiAgICByZXR1cm4gbmV3IFJlZ0V4cChzcmMsIGZsYWdzKTtcbiAgfSBjYXRjaCAoZSkge1xuICAgIGlmICh0aHJvd0Vycm9yQXQgIT09IHVuZGVmaW5lZCkge1xuICAgICAgaWYgKGUgaW5zdGFuY2VvZiBTeW50YXhFcnJvcikgdGhpcy5yYWlzZSh0aHJvd0Vycm9yQXQsIFwiRXJyb3IgcGFyc2luZyByZWd1bGFyIGV4cHJlc3Npb246IFwiICsgZS5tZXNzYWdlKTtcbiAgICAgIHRoaXMucmFpc2UoZSk7XG4gICAgfVxuICB9XG59XG5cbnZhciByZWdleHBVbmljb2RlU3VwcG9ydCA9ICEhdHJ5Q3JlYXRlUmVnZXhwKFwi77+/XCIsIFwidVwiKTtcblxucHAucmVhZFJlZ2V4cCA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIF90aGlzID0gdGhpcztcblxuICB2YXIgZXNjYXBlZCA9IHVuZGVmaW5lZCxcbiAgICAgIGluQ2xhc3MgPSB1bmRlZmluZWQsXG4gICAgICBzdGFydCA9IHRoaXMucG9zO1xuICBmb3IgKDs7KSB7XG4gICAgaWYgKHRoaXMucG9zID49IHRoaXMuaW5wdXQubGVuZ3RoKSB0aGlzLnJhaXNlKHN0YXJ0LCBcIlVudGVybWluYXRlZCByZWd1bGFyIGV4cHJlc3Npb25cIik7XG4gICAgdmFyIGNoID0gdGhpcy5pbnB1dC5jaGFyQXQodGhpcy5wb3MpO1xuICAgIGlmIChfd2hpdGVzcGFjZS5saW5lQnJlYWsudGVzdChjaCkpIHRoaXMucmFpc2Uoc3RhcnQsIFwiVW50ZXJtaW5hdGVkIHJlZ3VsYXIgZXhwcmVzc2lvblwiKTtcbiAgICBpZiAoIWVzY2FwZWQpIHtcbiAgICAgIGlmIChjaCA9PT0gXCJbXCIpIGluQ2xhc3MgPSB0cnVlO2Vsc2UgaWYgKGNoID09PSBcIl1cIiAmJiBpbkNsYXNzKSBpbkNsYXNzID0gZmFsc2U7ZWxzZSBpZiAoY2ggPT09IFwiL1wiICYmICFpbkNsYXNzKSBicmVhaztcbiAgICAgIGVzY2FwZWQgPSBjaCA9PT0gXCJcXFxcXCI7XG4gICAgfSBlbHNlIGVzY2FwZWQgPSBmYWxzZTtcbiAgICArK3RoaXMucG9zO1xuICB9XG4gIHZhciBjb250ZW50ID0gdGhpcy5pbnB1dC5zbGljZShzdGFydCwgdGhpcy5wb3MpO1xuICArK3RoaXMucG9zO1xuICAvLyBOZWVkIHRvIHVzZSBgcmVhZFdvcmQxYCBiZWNhdXNlICdcXHVYWFhYJyBzZXF1ZW5jZXMgYXJlIGFsbG93ZWRcbiAgLy8gaGVyZSAoZG9uJ3QgYXNrKS5cbiAgdmFyIG1vZHMgPSB0aGlzLnJlYWRXb3JkMSgpO1xuICB2YXIgdG1wID0gY29udGVudDtcbiAgaWYgKG1vZHMpIHtcbiAgICB2YXIgdmFsaWRGbGFncyA9IC9eW2dtc2l5XSokLztcbiAgICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYpIHZhbGlkRmxhZ3MgPSAvXltnbXNpeXVdKiQvO1xuICAgIGlmICghdmFsaWRGbGFncy50ZXN0KG1vZHMpKSB0aGlzLnJhaXNlKHN0YXJ0LCBcIkludmFsaWQgcmVndWxhciBleHByZXNzaW9uIGZsYWdcIik7XG4gICAgaWYgKG1vZHMuaW5kZXhPZihcInVcIikgPj0gMCAmJiAhcmVnZXhwVW5pY29kZVN1cHBvcnQpIHtcbiAgICAgIC8vIFJlcGxhY2UgZWFjaCBhc3RyYWwgc3ltYm9sIGFuZCBldmVyeSBVbmljb2RlIGVzY2FwZSBzZXF1ZW5jZSB0aGF0XG4gICAgICAvLyBwb3NzaWJseSByZXByZXNlbnRzIGFuIGFzdHJhbCBzeW1ib2wgb3IgYSBwYWlyZWQgc3Vycm9nYXRlIHdpdGggYVxuICAgICAgLy8gc2luZ2xlIEFTQ0lJIHN5bWJvbCB0byBhdm9pZCB0aHJvd2luZyBvbiByZWd1bGFyIGV4cHJlc3Npb25zIHRoYXRcbiAgICAgIC8vIGFyZSBvbmx5IHZhbGlkIGluIGNvbWJpbmF0aW9uIHdpdGggdGhlIGAvdWAgZmxhZy5cbiAgICAgIC8vIE5vdGU6IHJlcGxhY2luZyB3aXRoIHRoZSBBU0NJSSBzeW1ib2wgYHhgIG1pZ2h0IGNhdXNlIGZhbHNlXG4gICAgICAvLyBuZWdhdGl2ZXMgaW4gdW5saWtlbHkgc2NlbmFyaW9zLiBGb3IgZXhhbXBsZSwgYFtcXHV7NjF9LWJdYCBpcyBhXG4gICAgICAvLyBwZXJmZWN0bHkgdmFsaWQgcGF0dGVybiB0aGF0IGlzIGVxdWl2YWxlbnQgdG8gYFthLWJdYCwgYnV0IGl0IHdvdWxkXG4gICAgICAvLyBiZSByZXBsYWNlZCBieSBgW3gtYl1gIHdoaWNoIHRocm93cyBhbiBlcnJvci5cbiAgICAgIHRtcCA9IHRtcC5yZXBsYWNlKC9cXFxcdVxceyhbMC05YS1mQS1GXSspXFx9L2csIGZ1bmN0aW9uIChtYXRjaCwgY29kZSwgb2Zmc2V0KSB7XG4gICAgICAgIGNvZGUgPSBOdW1iZXIoXCIweFwiICsgY29kZSk7XG4gICAgICAgIGlmIChjb2RlID4gMHgxMEZGRkYpIF90aGlzLnJhaXNlKHN0YXJ0ICsgb2Zmc2V0ICsgMywgXCJDb2RlIHBvaW50IG91dCBvZiBib3VuZHNcIik7XG4gICAgICAgIHJldHVybiBcInhcIjtcbiAgICAgIH0pO1xuICAgICAgdG1wID0gdG1wLnJlcGxhY2UoL1xcXFx1KFthLWZBLUYwLTldezR9KXxbXFx1RDgwMC1cXHVEQkZGXVtcXHVEQzAwLVxcdURGRkZdL2csIFwieFwiKTtcbiAgICB9XG4gIH1cbiAgLy8gRGV0ZWN0IGludmFsaWQgcmVndWxhciBleHByZXNzaW9ucy5cbiAgdmFyIHZhbHVlID0gbnVsbDtcbiAgLy8gUmhpbm8ncyByZWd1bGFyIGV4cHJlc3Npb24gcGFyc2VyIGlzIGZsYWt5IGFuZCB0aHJvd3MgdW5jYXRjaGFibGUgZXhjZXB0aW9ucyxcbiAgLy8gc28gZG9uJ3QgZG8gZGV0ZWN0aW9uIGlmIHdlIGFyZSBydW5uaW5nIHVuZGVyIFJoaW5vXG4gIGlmICghaXNSaGlubykge1xuICAgIHRyeUNyZWF0ZVJlZ2V4cCh0bXAsIHVuZGVmaW5lZCwgc3RhcnQpO1xuICAgIC8vIEdldCBhIHJlZ3VsYXIgZXhwcmVzc2lvbiBvYmplY3QgZm9yIHRoaXMgcGF0dGVybi1mbGFnIHBhaXIsIG9yIGBudWxsYCBpblxuICAgIC8vIGNhc2UgdGhlIGN1cnJlbnQgZW52aXJvbm1lbnQgZG9lc24ndCBzdXBwb3J0IHRoZSBmbGFncyBpdCB1c2VzLlxuICAgIHZhbHVlID0gdHJ5Q3JlYXRlUmVnZXhwKGNvbnRlbnQsIG1vZHMpO1xuICB9XG4gIHJldHVybiB0aGlzLmZpbmlzaFRva2VuKF90b2tlbnR5cGUudHlwZXMucmVnZXhwLCB7IHBhdHRlcm46IGNvbnRlbnQsIGZsYWdzOiBtb2RzLCB2YWx1ZTogdmFsdWUgfSk7XG59O1xuXG4vLyBSZWFkIGFuIGludGVnZXIgaW4gdGhlIGdpdmVuIHJhZGl4LiBSZXR1cm4gbnVsbCBpZiB6ZXJvIGRpZ2l0c1xuLy8gd2VyZSByZWFkLCB0aGUgaW50ZWdlciB2YWx1ZSBvdGhlcndpc2UuIFdoZW4gYGxlbmAgaXMgZ2l2ZW4sIHRoaXNcbi8vIHdpbGwgcmV0dXJuIGBudWxsYCB1bmxlc3MgdGhlIGludGVnZXIgaGFzIGV4YWN0bHkgYGxlbmAgZGlnaXRzLlxuXG5wcC5yZWFkSW50ID0gZnVuY3Rpb24gKHJhZGl4LCBsZW4pIHtcbiAgdmFyIHN0YXJ0ID0gdGhpcy5wb3MsXG4gICAgICB0b3RhbCA9IDA7XG4gIGZvciAodmFyIGkgPSAwLCBlID0gbGVuID09IG51bGwgPyBJbmZpbml0eSA6IGxlbjsgaSA8IGU7ICsraSkge1xuICAgIHZhciBjb2RlID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zKSxcbiAgICAgICAgdmFsID0gdW5kZWZpbmVkO1xuICAgIGlmIChjb2RlID49IDk3KSB2YWwgPSBjb2RlIC0gOTcgKyAxMDsgLy8gYVxuICAgIGVsc2UgaWYgKGNvZGUgPj0gNjUpIHZhbCA9IGNvZGUgLSA2NSArIDEwOyAvLyBBXG4gICAgZWxzZSBpZiAoY29kZSA+PSA0OCAmJiBjb2RlIDw9IDU3KSB2YWwgPSBjb2RlIC0gNDg7IC8vIDAtOVxuICAgIGVsc2UgdmFsID0gSW5maW5pdHk7XG4gICAgaWYgKHZhbCA+PSByYWRpeCkgYnJlYWs7XG4gICAgKyt0aGlzLnBvcztcbiAgICB0b3RhbCA9IHRvdGFsICogcmFkaXggKyB2YWw7XG4gIH1cbiAgaWYgKHRoaXMucG9zID09PSBzdGFydCB8fCBsZW4gIT0gbnVsbCAmJiB0aGlzLnBvcyAtIHN0YXJ0ICE9PSBsZW4pIHJldHVybiBudWxsO1xuXG4gIHJldHVybiB0b3RhbDtcbn07XG5cbnBwLnJlYWRSYWRpeE51bWJlciA9IGZ1bmN0aW9uIChyYWRpeCkge1xuICB0aGlzLnBvcyArPSAyOyAvLyAweFxuICB2YXIgdmFsID0gdGhpcy5yZWFkSW50KHJhZGl4KTtcbiAgaWYgKHZhbCA9PSBudWxsKSB0aGlzLnJhaXNlKHRoaXMuc3RhcnQgKyAyLCBcIkV4cGVjdGVkIG51bWJlciBpbiByYWRpeCBcIiArIHJhZGl4KTtcbiAgaWYgKF9pZGVudGlmaWVyLmlzSWRlbnRpZmllclN0YXJ0KHRoaXMuZnVsbENoYXJDb2RlQXRQb3MoKSkpIHRoaXMucmFpc2UodGhpcy5wb3MsIFwiSWRlbnRpZmllciBkaXJlY3RseSBhZnRlciBudW1iZXJcIik7XG4gIHJldHVybiB0aGlzLmZpbmlzaFRva2VuKF90b2tlbnR5cGUudHlwZXMubnVtLCB2YWwpO1xufTtcblxuLy8gUmVhZCBhbiBpbnRlZ2VyLCBvY3RhbCBpbnRlZ2VyLCBvciBmbG9hdGluZy1wb2ludCBudW1iZXIuXG5cbnBwLnJlYWROdW1iZXIgPSBmdW5jdGlvbiAoc3RhcnRzV2l0aERvdCkge1xuICB2YXIgc3RhcnQgPSB0aGlzLnBvcyxcbiAgICAgIGlzRmxvYXQgPSBmYWxzZSxcbiAgICAgIG9jdGFsID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zKSA9PT0gNDg7XG4gIGlmICghc3RhcnRzV2l0aERvdCAmJiB0aGlzLnJlYWRJbnQoMTApID09PSBudWxsKSB0aGlzLnJhaXNlKHN0YXJ0LCBcIkludmFsaWQgbnVtYmVyXCIpO1xuICB2YXIgbmV4dCA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyk7XG4gIGlmIChuZXh0ID09PSA0Nikge1xuICAgIC8vICcuJ1xuICAgICsrdGhpcy5wb3M7XG4gICAgdGhpcy5yZWFkSW50KDEwKTtcbiAgICBpc0Zsb2F0ID0gdHJ1ZTtcbiAgICBuZXh0ID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zKTtcbiAgfVxuICBpZiAobmV4dCA9PT0gNjkgfHwgbmV4dCA9PT0gMTAxKSB7XG4gICAgLy8gJ2VFJ1xuICAgIG5leHQgPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQoKyt0aGlzLnBvcyk7XG4gICAgaWYgKG5leHQgPT09IDQzIHx8IG5leHQgPT09IDQ1KSArK3RoaXMucG9zOyAvLyAnKy0nXG4gICAgaWYgKHRoaXMucmVhZEludCgxMCkgPT09IG51bGwpIHRoaXMucmFpc2Uoc3RhcnQsIFwiSW52YWxpZCBudW1iZXJcIik7XG4gICAgaXNGbG9hdCA9IHRydWU7XG4gIH1cbiAgaWYgKF9pZGVudGlmaWVyLmlzSWRlbnRpZmllclN0YXJ0KHRoaXMuZnVsbENoYXJDb2RlQXRQb3MoKSkpIHRoaXMucmFpc2UodGhpcy5wb3MsIFwiSWRlbnRpZmllciBkaXJlY3RseSBhZnRlciBudW1iZXJcIik7XG5cbiAgdmFyIHN0ciA9IHRoaXMuaW5wdXQuc2xpY2Uoc3RhcnQsIHRoaXMucG9zKSxcbiAgICAgIHZhbCA9IHVuZGVmaW5lZDtcbiAgaWYgKGlzRmxvYXQpIHZhbCA9IHBhcnNlRmxvYXQoc3RyKTtlbHNlIGlmICghb2N0YWwgfHwgc3RyLmxlbmd0aCA9PT0gMSkgdmFsID0gcGFyc2VJbnQoc3RyLCAxMCk7ZWxzZSBpZiAoL1s4OV0vLnRlc3Qoc3RyKSB8fCB0aGlzLnN0cmljdCkgdGhpcy5yYWlzZShzdGFydCwgXCJJbnZhbGlkIG51bWJlclwiKTtlbHNlIHZhbCA9IHBhcnNlSW50KHN0ciwgOCk7XG4gIHJldHVybiB0aGlzLmZpbmlzaFRva2VuKF90b2tlbnR5cGUudHlwZXMubnVtLCB2YWwpO1xufTtcblxuLy8gUmVhZCBhIHN0cmluZyB2YWx1ZSwgaW50ZXJwcmV0aW5nIGJhY2tzbGFzaC1lc2NhcGVzLlxuXG5wcC5yZWFkQ29kZVBvaW50ID0gZnVuY3Rpb24gKCkge1xuICB2YXIgY2ggPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MpLFxuICAgICAgY29kZSA9IHVuZGVmaW5lZDtcblxuICBpZiAoY2ggPT09IDEyMykge1xuICAgIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPCA2KSB0aGlzLnVuZXhwZWN0ZWQoKTtcbiAgICB2YXIgY29kZVBvcyA9ICsrdGhpcy5wb3M7XG4gICAgY29kZSA9IHRoaXMucmVhZEhleENoYXIodGhpcy5pbnB1dC5pbmRleE9mKFwifVwiLCB0aGlzLnBvcykgLSB0aGlzLnBvcyk7XG4gICAgKyt0aGlzLnBvcztcbiAgICBpZiAoY29kZSA+IDB4MTBGRkZGKSB0aGlzLnJhaXNlKGNvZGVQb3MsIFwiQ29kZSBwb2ludCBvdXQgb2YgYm91bmRzXCIpO1xuICB9IGVsc2Uge1xuICAgIGNvZGUgPSB0aGlzLnJlYWRIZXhDaGFyKDQpO1xuICB9XG4gIHJldHVybiBjb2RlO1xufTtcblxuZnVuY3Rpb24gY29kZVBvaW50VG9TdHJpbmcoY29kZSkge1xuICAvLyBVVEYtMTYgRGVjb2RpbmdcbiAgaWYgKGNvZGUgPD0gMHhGRkZGKSByZXR1cm4gU3RyaW5nLmZyb21DaGFyQ29kZShjb2RlKTtcbiAgY29kZSAtPSAweDEwMDAwO1xuICByZXR1cm4gU3RyaW5nLmZyb21DaGFyQ29kZSgoY29kZSA+PiAxMCkgKyAweEQ4MDAsIChjb2RlICYgMTAyMykgKyAweERDMDApO1xufVxuXG5wcC5yZWFkU3RyaW5nID0gZnVuY3Rpb24gKHF1b3RlKSB7XG4gIHZhciBvdXQgPSBcIlwiLFxuICAgICAgY2h1bmtTdGFydCA9ICsrdGhpcy5wb3M7XG4gIGZvciAoOzspIHtcbiAgICBpZiAodGhpcy5wb3MgPj0gdGhpcy5pbnB1dC5sZW5ndGgpIHRoaXMucmFpc2UodGhpcy5zdGFydCwgXCJVbnRlcm1pbmF0ZWQgc3RyaW5nIGNvbnN0YW50XCIpO1xuICAgIHZhciBjaCA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyk7XG4gICAgaWYgKGNoID09PSBxdW90ZSkgYnJlYWs7XG4gICAgaWYgKGNoID09PSA5Mikge1xuICAgICAgLy8gJ1xcJ1xuICAgICAgb3V0ICs9IHRoaXMuaW5wdXQuc2xpY2UoY2h1bmtTdGFydCwgdGhpcy5wb3MpO1xuICAgICAgb3V0ICs9IHRoaXMucmVhZEVzY2FwZWRDaGFyKGZhbHNlKTtcbiAgICAgIGNodW5rU3RhcnQgPSB0aGlzLnBvcztcbiAgICB9IGVsc2Uge1xuICAgICAgaWYgKF93aGl0ZXNwYWNlLmlzTmV3TGluZShjaCkpIHRoaXMucmFpc2UodGhpcy5zdGFydCwgXCJVbnRlcm1pbmF0ZWQgc3RyaW5nIGNvbnN0YW50XCIpO1xuICAgICAgKyt0aGlzLnBvcztcbiAgICB9XG4gIH1cbiAgb3V0ICs9IHRoaXMuaW5wdXQuc2xpY2UoY2h1bmtTdGFydCwgdGhpcy5wb3MrKyk7XG4gIHJldHVybiB0aGlzLmZpbmlzaFRva2VuKF90b2tlbnR5cGUudHlwZXMuc3RyaW5nLCBvdXQpO1xufTtcblxuLy8gUmVhZHMgdGVtcGxhdGUgc3RyaW5nIHRva2Vucy5cblxucHAucmVhZFRtcGxUb2tlbiA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIG91dCA9IFwiXCIsXG4gICAgICBjaHVua1N0YXJ0ID0gdGhpcy5wb3M7XG4gIGZvciAoOzspIHtcbiAgICBpZiAodGhpcy5wb3MgPj0gdGhpcy5pbnB1dC5sZW5ndGgpIHRoaXMucmFpc2UodGhpcy5zdGFydCwgXCJVbnRlcm1pbmF0ZWQgdGVtcGxhdGVcIik7XG4gICAgdmFyIGNoID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zKTtcbiAgICBpZiAoY2ggPT09IDk2IHx8IGNoID09PSAzNiAmJiB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAxKSA9PT0gMTIzKSB7XG4gICAgICAvLyAnYCcsICckeydcbiAgICAgIGlmICh0aGlzLnBvcyA9PT0gdGhpcy5zdGFydCAmJiB0aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMudGVtcGxhdGUpIHtcbiAgICAgICAgaWYgKGNoID09PSAzNikge1xuICAgICAgICAgIHRoaXMucG9zICs9IDI7XG4gICAgICAgICAgcmV0dXJuIHRoaXMuZmluaXNoVG9rZW4oX3Rva2VudHlwZS50eXBlcy5kb2xsYXJCcmFjZUwpO1xuICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgICsrdGhpcy5wb3M7XG4gICAgICAgICAgcmV0dXJuIHRoaXMuZmluaXNoVG9rZW4oX3Rva2VudHlwZS50eXBlcy5iYWNrUXVvdGUpO1xuICAgICAgICB9XG4gICAgICB9XG4gICAgICBvdXQgKz0gdGhpcy5pbnB1dC5zbGljZShjaHVua1N0YXJ0LCB0aGlzLnBvcyk7XG4gICAgICByZXR1cm4gdGhpcy5maW5pc2hUb2tlbihfdG9rZW50eXBlLnR5cGVzLnRlbXBsYXRlLCBvdXQpO1xuICAgIH1cbiAgICBpZiAoY2ggPT09IDkyKSB7XG4gICAgICAvLyAnXFwnXG4gICAgICBvdXQgKz0gdGhpcy5pbnB1dC5zbGljZShjaHVua1N0YXJ0LCB0aGlzLnBvcyk7XG4gICAgICBvdXQgKz0gdGhpcy5yZWFkRXNjYXBlZENoYXIodHJ1ZSk7XG4gICAgICBjaHVua1N0YXJ0ID0gdGhpcy5wb3M7XG4gICAgfSBlbHNlIGlmIChfd2hpdGVzcGFjZS5pc05ld0xpbmUoY2gpKSB7XG4gICAgICBvdXQgKz0gdGhpcy5pbnB1dC5zbGljZShjaHVua1N0YXJ0LCB0aGlzLnBvcyk7XG4gICAgICArK3RoaXMucG9zO1xuICAgICAgc3dpdGNoIChjaCkge1xuICAgICAgICBjYXNlIDEzOlxuICAgICAgICAgIGlmICh0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MpID09PSAxMCkgKyt0aGlzLnBvcztcbiAgICAgICAgY2FzZSAxMDpcbiAgICAgICAgICBvdXQgKz0gXCJcXG5cIjtcbiAgICAgICAgICBicmVhaztcbiAgICAgICAgZGVmYXVsdDpcbiAgICAgICAgICBvdXQgKz0gU3RyaW5nLmZyb21DaGFyQ29kZShjaCk7XG4gICAgICAgICAgYnJlYWs7XG4gICAgICB9XG4gICAgICBpZiAodGhpcy5vcHRpb25zLmxvY2F0aW9ucykge1xuICAgICAgICArK3RoaXMuY3VyTGluZTtcbiAgICAgICAgdGhpcy5saW5lU3RhcnQgPSB0aGlzLnBvcztcbiAgICAgIH1cbiAgICAgIGNodW5rU3RhcnQgPSB0aGlzLnBvcztcbiAgICB9IGVsc2Uge1xuICAgICAgKyt0aGlzLnBvcztcbiAgICB9XG4gIH1cbn07XG5cbi8vIFVzZWQgdG8gcmVhZCBlc2NhcGVkIGNoYXJhY3RlcnNcblxucHAucmVhZEVzY2FwZWRDaGFyID0gZnVuY3Rpb24gKGluVGVtcGxhdGUpIHtcbiAgdmFyIGNoID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KCsrdGhpcy5wb3MpO1xuICArK3RoaXMucG9zO1xuICBzd2l0Y2ggKGNoKSB7XG4gICAgY2FzZSAxMTA6XG4gICAgICByZXR1cm4gXCJcXG5cIjsgLy8gJ24nIC0+ICdcXG4nXG4gICAgY2FzZSAxMTQ6XG4gICAgICByZXR1cm4gXCJcXHJcIjsgLy8gJ3InIC0+ICdcXHInXG4gICAgY2FzZSAxMjA6XG4gICAgICByZXR1cm4gU3RyaW5nLmZyb21DaGFyQ29kZSh0aGlzLnJlYWRIZXhDaGFyKDIpKTsgLy8gJ3gnXG4gICAgY2FzZSAxMTc6XG4gICAgICByZXR1cm4gY29kZVBvaW50VG9TdHJpbmcodGhpcy5yZWFkQ29kZVBvaW50KCkpOyAvLyAndSdcbiAgICBjYXNlIDExNjpcbiAgICAgIHJldHVybiBcIlxcdFwiOyAvLyAndCcgLT4gJ1xcdCdcbiAgICBjYXNlIDk4OlxuICAgICAgcmV0dXJuIFwiXFxiXCI7IC8vICdiJyAtPiAnXFxiJ1xuICAgIGNhc2UgMTE4OlxuICAgICAgcmV0dXJuIFwiXFx1MDAwYlwiOyAvLyAndicgLT4gJ1xcdTAwMGInXG4gICAgY2FzZSAxMDI6XG4gICAgICByZXR1cm4gXCJcXGZcIjsgLy8gJ2YnIC0+ICdcXGYnXG4gICAgY2FzZSAxMzpcbiAgICAgIGlmICh0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MpID09PSAxMCkgKyt0aGlzLnBvczsgLy8gJ1xcclxcbidcbiAgICBjYXNlIDEwOlxuICAgICAgLy8gJyBcXG4nXG4gICAgICBpZiAodGhpcy5vcHRpb25zLmxvY2F0aW9ucykge1xuICAgICAgICB0aGlzLmxpbmVTdGFydCA9IHRoaXMucG9zOysrdGhpcy5jdXJMaW5lO1xuICAgICAgfVxuICAgICAgcmV0dXJuIFwiXCI7XG4gICAgZGVmYXVsdDpcbiAgICAgIGlmIChjaCA+PSA0OCAmJiBjaCA8PSA1NSkge1xuICAgICAgICB2YXIgb2N0YWxTdHIgPSB0aGlzLmlucHV0LnN1YnN0cih0aGlzLnBvcyAtIDEsIDMpLm1hdGNoKC9eWzAtN10rLylbMF07XG4gICAgICAgIHZhciBvY3RhbCA9IHBhcnNlSW50KG9jdGFsU3RyLCA4KTtcbiAgICAgICAgaWYgKG9jdGFsID4gMjU1KSB7XG4gICAgICAgICAgb2N0YWxTdHIgPSBvY3RhbFN0ci5zbGljZSgwLCAtMSk7XG4gICAgICAgICAgb2N0YWwgPSBwYXJzZUludChvY3RhbFN0ciwgOCk7XG4gICAgICAgIH1cbiAgICAgICAgaWYgKG9jdGFsID4gMCAmJiAodGhpcy5zdHJpY3QgfHwgaW5UZW1wbGF0ZSkpIHtcbiAgICAgICAgICB0aGlzLnJhaXNlKHRoaXMucG9zIC0gMiwgXCJPY3RhbCBsaXRlcmFsIGluIHN0cmljdCBtb2RlXCIpO1xuICAgICAgICB9XG4gICAgICAgIHRoaXMucG9zICs9IG9jdGFsU3RyLmxlbmd0aCAtIDE7XG4gICAgICAgIHJldHVybiBTdHJpbmcuZnJvbUNoYXJDb2RlKG9jdGFsKTtcbiAgICAgIH1cbiAgICAgIHJldHVybiBTdHJpbmcuZnJvbUNoYXJDb2RlKGNoKTtcbiAgfVxufTtcblxuLy8gVXNlZCB0byByZWFkIGNoYXJhY3RlciBlc2NhcGUgc2VxdWVuY2VzICgnXFx4JywgJ1xcdScsICdcXFUnKS5cblxucHAucmVhZEhleENoYXIgPSBmdW5jdGlvbiAobGVuKSB7XG4gIHZhciBjb2RlUG9zID0gdGhpcy5wb3M7XG4gIHZhciBuID0gdGhpcy5yZWFkSW50KDE2LCBsZW4pO1xuICBpZiAobiA9PT0gbnVsbCkgdGhpcy5yYWlzZShjb2RlUG9zLCBcIkJhZCBjaGFyYWN0ZXIgZXNjYXBlIHNlcXVlbmNlXCIpO1xuICByZXR1cm4gbjtcbn07XG5cbi8vIFJlYWQgYW4gaWRlbnRpZmllciwgYW5kIHJldHVybiBpdCBhcyBhIHN0cmluZy4gU2V0cyBgdGhpcy5jb250YWluc0VzY2Bcbi8vIHRvIHdoZXRoZXIgdGhlIHdvcmQgY29udGFpbmVkIGEgJ1xcdScgZXNjYXBlLlxuLy9cbi8vIEluY3JlbWVudGFsbHkgYWRkcyBvbmx5IGVzY2FwZWQgY2hhcnMsIGFkZGluZyBvdGhlciBjaHVua3MgYXMtaXNcbi8vIGFzIGEgbWljcm8tb3B0aW1pemF0aW9uLlxuXG5wcC5yZWFkV29yZDEgPSBmdW5jdGlvbiAoKSB7XG4gIHRoaXMuY29udGFpbnNFc2MgPSBmYWxzZTtcbiAgdmFyIHdvcmQgPSBcIlwiLFxuICAgICAgZmlyc3QgPSB0cnVlLFxuICAgICAgY2h1bmtTdGFydCA9IHRoaXMucG9zO1xuICB2YXIgYXN0cmFsID0gdGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDY7XG4gIHdoaWxlICh0aGlzLnBvcyA8IHRoaXMuaW5wdXQubGVuZ3RoKSB7XG4gICAgdmFyIGNoID0gdGhpcy5mdWxsQ2hhckNvZGVBdFBvcygpO1xuICAgIGlmIChfaWRlbnRpZmllci5pc0lkZW50aWZpZXJDaGFyKGNoLCBhc3RyYWwpKSB7XG4gICAgICB0aGlzLnBvcyArPSBjaCA8PSAweGZmZmYgPyAxIDogMjtcbiAgICB9IGVsc2UgaWYgKGNoID09PSA5Mikge1xuICAgICAgLy8gXCJcXFwiXG4gICAgICB0aGlzLmNvbnRhaW5zRXNjID0gdHJ1ZTtcbiAgICAgIHdvcmQgKz0gdGhpcy5pbnB1dC5zbGljZShjaHVua1N0YXJ0LCB0aGlzLnBvcyk7XG4gICAgICB2YXIgZXNjU3RhcnQgPSB0aGlzLnBvcztcbiAgICAgIGlmICh0aGlzLmlucHV0LmNoYXJDb2RlQXQoKyt0aGlzLnBvcykgIT0gMTE3KSAvLyBcInVcIlxuICAgICAgICB0aGlzLnJhaXNlKHRoaXMucG9zLCBcIkV4cGVjdGluZyBVbmljb2RlIGVzY2FwZSBzZXF1ZW5jZSBcXFxcdVhYWFhcIik7XG4gICAgICArK3RoaXMucG9zO1xuICAgICAgdmFyIGVzYyA9IHRoaXMucmVhZENvZGVQb2ludCgpO1xuICAgICAgaWYgKCEoZmlyc3QgPyBfaWRlbnRpZmllci5pc0lkZW50aWZpZXJTdGFydCA6IF9pZGVudGlmaWVyLmlzSWRlbnRpZmllckNoYXIpKGVzYywgYXN0cmFsKSkgdGhpcy5yYWlzZShlc2NTdGFydCwgXCJJbnZhbGlkIFVuaWNvZGUgZXNjYXBlXCIpO1xuICAgICAgd29yZCArPSBjb2RlUG9pbnRUb1N0cmluZyhlc2MpO1xuICAgICAgY2h1bmtTdGFydCA9IHRoaXMucG9zO1xuICAgIH0gZWxzZSB7XG4gICAgICBicmVhaztcbiAgICB9XG4gICAgZmlyc3QgPSBmYWxzZTtcbiAgfVxuICByZXR1cm4gd29yZCArIHRoaXMuaW5wdXQuc2xpY2UoY2h1bmtTdGFydCwgdGhpcy5wb3MpO1xufTtcblxuLy8gUmVhZCBhbiBpZGVudGlmaWVyIG9yIGtleXdvcmQgdG9rZW4uIFdpbGwgY2hlY2sgZm9yIHJlc2VydmVkXG4vLyB3b3JkcyB3aGVuIG5lY2Vzc2FyeS5cblxucHAucmVhZFdvcmQgPSBmdW5jdGlvbiAoKSB7XG4gIHZhciB3b3JkID0gdGhpcy5yZWFkV29yZDEoKTtcbiAgdmFyIHR5cGUgPSBfdG9rZW50eXBlLnR5cGVzLm5hbWU7XG4gIGlmICgodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYgfHwgIXRoaXMuY29udGFpbnNFc2MpICYmIHRoaXMuaXNLZXl3b3JkKHdvcmQpKSB0eXBlID0gX3Rva2VudHlwZS5rZXl3b3Jkc1t3b3JkXTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoVG9rZW4odHlwZSwgd29yZCk7XG59O1xuXG59LHtcIi4vaWRlbnRpZmllclwiOjIsXCIuL2xvY3V0aWxcIjo1LFwiLi9zdGF0ZVwiOjEwLFwiLi90b2tlbnR5cGVcIjoxNCxcIi4vd2hpdGVzcGFjZVwiOjE2fV0sMTQ6W2Z1bmN0aW9uKF9kZXJlcV8sbW9kdWxlLGV4cG9ydHMpe1xuLy8gIyMgVG9rZW4gdHlwZXNcblxuLy8gVGhlIGFzc2lnbm1lbnQgb2YgZmluZS1ncmFpbmVkLCBpbmZvcm1hdGlvbi1jYXJyeWluZyB0eXBlIG9iamVjdHNcbi8vIGFsbG93cyB0aGUgdG9rZW5pemVyIHRvIHN0b3JlIHRoZSBpbmZvcm1hdGlvbiBpdCBoYXMgYWJvdXQgYVxuLy8gdG9rZW4gaW4gYSB3YXkgdGhhdCBpcyB2ZXJ5IGNoZWFwIGZvciB0aGUgcGFyc2VyIHRvIGxvb2sgdXAuXG5cbi8vIEFsbCB0b2tlbiB0eXBlIHZhcmlhYmxlcyBzdGFydCB3aXRoIGFuIHVuZGVyc2NvcmUsIHRvIG1ha2UgdGhlbVxuLy8gZWFzeSB0byByZWNvZ25pemUuXG5cbi8vIFRoZSBgYmVmb3JlRXhwcmAgcHJvcGVydHkgaXMgdXNlZCB0byBkaXNhbWJpZ3VhdGUgYmV0d2VlbiByZWd1bGFyXG4vLyBleHByZXNzaW9ucyBhbmQgZGl2aXNpb25zLiBJdCBpcyBzZXQgb24gYWxsIHRva2VuIHR5cGVzIHRoYXQgY2FuXG4vLyBiZSBmb2xsb3dlZCBieSBhbiBleHByZXNzaW9uICh0aHVzLCBhIHNsYXNoIGFmdGVyIHRoZW0gd291bGQgYmUgYVxuLy8gcmVndWxhciBleHByZXNzaW9uKS5cbi8vXG4vLyBgaXNMb29wYCBtYXJrcyBhIGtleXdvcmQgYXMgc3RhcnRpbmcgYSBsb29wLCB3aGljaCBpcyBpbXBvcnRhbnRcbi8vIHRvIGtub3cgd2hlbiBwYXJzaW5nIGEgbGFiZWwsIGluIG9yZGVyIHRvIGFsbG93IG9yIGRpc2FsbG93XG4vLyBjb250aW51ZSBqdW1wcyB0byB0aGF0IGxhYmVsLlxuXG5cInVzZSBzdHJpY3RcIjtcblxuZXhwb3J0cy5fX2VzTW9kdWxlID0gdHJ1ZTtcblxuZnVuY3Rpb24gX2NsYXNzQ2FsbENoZWNrKGluc3RhbmNlLCBDb25zdHJ1Y3RvcikgeyBpZiAoIShpbnN0YW5jZSBpbnN0YW5jZW9mIENvbnN0cnVjdG9yKSkgeyB0aHJvdyBuZXcgVHlwZUVycm9yKFwiQ2Fubm90IGNhbGwgYSBjbGFzcyBhcyBhIGZ1bmN0aW9uXCIpOyB9IH1cblxudmFyIFRva2VuVHlwZSA9IGZ1bmN0aW9uIFRva2VuVHlwZShsYWJlbCkge1xuICB2YXIgY29uZiA9IGFyZ3VtZW50cy5sZW5ndGggPD0gMSB8fCBhcmd1bWVudHNbMV0gPT09IHVuZGVmaW5lZCA/IHt9IDogYXJndW1lbnRzWzFdO1xuXG4gIF9jbGFzc0NhbGxDaGVjayh0aGlzLCBUb2tlblR5cGUpO1xuXG4gIHRoaXMubGFiZWwgPSBsYWJlbDtcbiAgdGhpcy5rZXl3b3JkID0gY29uZi5rZXl3b3JkO1xuICB0aGlzLmJlZm9yZUV4cHIgPSAhIWNvbmYuYmVmb3JlRXhwcjtcbiAgdGhpcy5zdGFydHNFeHByID0gISFjb25mLnN0YXJ0c0V4cHI7XG4gIHRoaXMuaXNMb29wID0gISFjb25mLmlzTG9vcDtcbiAgdGhpcy5pc0Fzc2lnbiA9ICEhY29uZi5pc0Fzc2lnbjtcbiAgdGhpcy5wcmVmaXggPSAhIWNvbmYucHJlZml4O1xuICB0aGlzLnBvc3RmaXggPSAhIWNvbmYucG9zdGZpeDtcbiAgdGhpcy5iaW5vcCA9IGNvbmYuYmlub3AgfHwgbnVsbDtcbiAgdGhpcy51cGRhdGVDb250ZXh0ID0gbnVsbDtcbn07XG5cbmV4cG9ydHMuVG9rZW5UeXBlID0gVG9rZW5UeXBlO1xuXG5mdW5jdGlvbiBiaW5vcChuYW1lLCBwcmVjKSB7XG4gIHJldHVybiBuZXcgVG9rZW5UeXBlKG5hbWUsIHsgYmVmb3JlRXhwcjogdHJ1ZSwgYmlub3A6IHByZWMgfSk7XG59XG52YXIgYmVmb3JlRXhwciA9IHsgYmVmb3JlRXhwcjogdHJ1ZSB9LFxuICAgIHN0YXJ0c0V4cHIgPSB7IHN0YXJ0c0V4cHI6IHRydWUgfTtcblxudmFyIHR5cGVzID0ge1xuICBudW06IG5ldyBUb2tlblR5cGUoXCJudW1cIiwgc3RhcnRzRXhwciksXG4gIHJlZ2V4cDogbmV3IFRva2VuVHlwZShcInJlZ2V4cFwiLCBzdGFydHNFeHByKSxcbiAgc3RyaW5nOiBuZXcgVG9rZW5UeXBlKFwic3RyaW5nXCIsIHN0YXJ0c0V4cHIpLFxuICBuYW1lOiBuZXcgVG9rZW5UeXBlKFwibmFtZVwiLCBzdGFydHNFeHByKSxcbiAgZW9mOiBuZXcgVG9rZW5UeXBlKFwiZW9mXCIpLFxuXG4gIC8vIFB1bmN0dWF0aW9uIHRva2VuIHR5cGVzLlxuICBicmFja2V0TDogbmV3IFRva2VuVHlwZShcIltcIiwgeyBiZWZvcmVFeHByOiB0cnVlLCBzdGFydHNFeHByOiB0cnVlIH0pLFxuICBicmFja2V0UjogbmV3IFRva2VuVHlwZShcIl1cIiksXG4gIGJyYWNlTDogbmV3IFRva2VuVHlwZShcIntcIiwgeyBiZWZvcmVFeHByOiB0cnVlLCBzdGFydHNFeHByOiB0cnVlIH0pLFxuICBicmFjZVI6IG5ldyBUb2tlblR5cGUoXCJ9XCIpLFxuICBwYXJlbkw6IG5ldyBUb2tlblR5cGUoXCIoXCIsIHsgYmVmb3JlRXhwcjogdHJ1ZSwgc3RhcnRzRXhwcjogdHJ1ZSB9KSxcbiAgcGFyZW5SOiBuZXcgVG9rZW5UeXBlKFwiKVwiKSxcbiAgY29tbWE6IG5ldyBUb2tlblR5cGUoXCIsXCIsIGJlZm9yZUV4cHIpLFxuICBzZW1pOiBuZXcgVG9rZW5UeXBlKFwiO1wiLCBiZWZvcmVFeHByKSxcbiAgY29sb246IG5ldyBUb2tlblR5cGUoXCI6XCIsIGJlZm9yZUV4cHIpLFxuICBkb3Q6IG5ldyBUb2tlblR5cGUoXCIuXCIpLFxuICBxdWVzdGlvbjogbmV3IFRva2VuVHlwZShcIj9cIiwgYmVmb3JlRXhwciksXG4gIGFycm93OiBuZXcgVG9rZW5UeXBlKFwiPT5cIiwgYmVmb3JlRXhwciksXG4gIHRlbXBsYXRlOiBuZXcgVG9rZW5UeXBlKFwidGVtcGxhdGVcIiksXG4gIGVsbGlwc2lzOiBuZXcgVG9rZW5UeXBlKFwiLi4uXCIsIGJlZm9yZUV4cHIpLFxuICBiYWNrUXVvdGU6IG5ldyBUb2tlblR5cGUoXCJgXCIsIHN0YXJ0c0V4cHIpLFxuICBkb2xsYXJCcmFjZUw6IG5ldyBUb2tlblR5cGUoXCIke1wiLCB7IGJlZm9yZUV4cHI6IHRydWUsIHN0YXJ0c0V4cHI6IHRydWUgfSksXG5cbiAgLy8gT3BlcmF0b3JzLiBUaGVzZSBjYXJyeSBzZXZlcmFsIGtpbmRzIG9mIHByb3BlcnRpZXMgdG8gaGVscCB0aGVcbiAgLy8gcGFyc2VyIHVzZSB0aGVtIHByb3Blcmx5ICh0aGUgcHJlc2VuY2Ugb2YgdGhlc2UgcHJvcGVydGllcyBpc1xuICAvLyB3aGF0IGNhdGVnb3JpemVzIHRoZW0gYXMgb3BlcmF0b3JzKS5cbiAgLy9cbiAgLy8gYGJpbm9wYCwgd2hlbiBwcmVzZW50LCBzcGVjaWZpZXMgdGhhdCB0aGlzIG9wZXJhdG9yIGlzIGEgYmluYXJ5XG4gIC8vIG9wZXJhdG9yLCBhbmQgd2lsbCByZWZlciB0byBpdHMgcHJlY2VkZW5jZS5cbiAgLy9cbiAgLy8gYHByZWZpeGAgYW5kIGBwb3N0Zml4YCBtYXJrIHRoZSBvcGVyYXRvciBhcyBhIHByZWZpeCBvciBwb3N0Zml4XG4gIC8vIHVuYXJ5IG9wZXJhdG9yLlxuICAvL1xuICAvLyBgaXNBc3NpZ25gIG1hcmtzIGFsbCBvZiBgPWAsIGArPWAsIGAtPWAgZXRjZXRlcmEsIHdoaWNoIGFjdCBhc1xuICAvLyBiaW5hcnkgb3BlcmF0b3JzIHdpdGggYSB2ZXJ5IGxvdyBwcmVjZWRlbmNlLCB0aGF0IHNob3VsZCByZXN1bHRcbiAgLy8gaW4gQXNzaWdubWVudEV4cHJlc3Npb24gbm9kZXMuXG5cbiAgZXE6IG5ldyBUb2tlblR5cGUoXCI9XCIsIHsgYmVmb3JlRXhwcjogdHJ1ZSwgaXNBc3NpZ246IHRydWUgfSksXG4gIGFzc2lnbjogbmV3IFRva2VuVHlwZShcIl89XCIsIHsgYmVmb3JlRXhwcjogdHJ1ZSwgaXNBc3NpZ246IHRydWUgfSksXG4gIGluY0RlYzogbmV3IFRva2VuVHlwZShcIisrLy0tXCIsIHsgcHJlZml4OiB0cnVlLCBwb3N0Zml4OiB0cnVlLCBzdGFydHNFeHByOiB0cnVlIH0pLFxuICBwcmVmaXg6IG5ldyBUb2tlblR5cGUoXCJwcmVmaXhcIiwgeyBiZWZvcmVFeHByOiB0cnVlLCBwcmVmaXg6IHRydWUsIHN0YXJ0c0V4cHI6IHRydWUgfSksXG4gIGxvZ2ljYWxPUjogYmlub3AoXCJ8fFwiLCAxKSxcbiAgbG9naWNhbEFORDogYmlub3AoXCImJlwiLCAyKSxcbiAgYml0d2lzZU9SOiBiaW5vcChcInxcIiwgMyksXG4gIGJpdHdpc2VYT1I6IGJpbm9wKFwiXlwiLCA0KSxcbiAgYml0d2lzZUFORDogYmlub3AoXCImXCIsIDUpLFxuICBlcXVhbGl0eTogYmlub3AoXCI9PS8hPVwiLCA2KSxcbiAgcmVsYXRpb25hbDogYmlub3AoXCI8Lz5cIiwgNyksXG4gIGJpdFNoaWZ0OiBiaW5vcChcIjw8Lz4+XCIsIDgpLFxuICBwbHVzTWluOiBuZXcgVG9rZW5UeXBlKFwiKy8tXCIsIHsgYmVmb3JlRXhwcjogdHJ1ZSwgYmlub3A6IDksIHByZWZpeDogdHJ1ZSwgc3RhcnRzRXhwcjogdHJ1ZSB9KSxcbiAgbW9kdWxvOiBiaW5vcChcIiVcIiwgMTApLFxuICBzdGFyOiBiaW5vcChcIipcIiwgMTApLFxuICBzbGFzaDogYmlub3AoXCIvXCIsIDEwKVxufTtcblxuZXhwb3J0cy50eXBlcyA9IHR5cGVzO1xuLy8gTWFwIGtleXdvcmQgbmFtZXMgdG8gdG9rZW4gdHlwZXMuXG5cbnZhciBrZXl3b3JkcyA9IHt9O1xuXG5leHBvcnRzLmtleXdvcmRzID0ga2V5d29yZHM7XG4vLyBTdWNjaW5jdCBkZWZpbml0aW9ucyBvZiBrZXl3b3JkIHRva2VuIHR5cGVzXG5mdW5jdGlvbiBrdyhuYW1lKSB7XG4gIHZhciBvcHRpb25zID0gYXJndW1lbnRzLmxlbmd0aCA8PSAxIHx8IGFyZ3VtZW50c1sxXSA9PT0gdW5kZWZpbmVkID8ge30gOiBhcmd1bWVudHNbMV07XG5cbiAgb3B0aW9ucy5rZXl3b3JkID0gbmFtZTtcbiAga2V5d29yZHNbbmFtZV0gPSB0eXBlc1tcIl9cIiArIG5hbWVdID0gbmV3IFRva2VuVHlwZShuYW1lLCBvcHRpb25zKTtcbn1cblxua3coXCJicmVha1wiKTtcbmt3KFwiY2FzZVwiLCBiZWZvcmVFeHByKTtcbmt3KFwiY2F0Y2hcIik7XG5rdyhcImNvbnRpbnVlXCIpO1xua3coXCJkZWJ1Z2dlclwiKTtcbmt3KFwiZGVmYXVsdFwiLCBiZWZvcmVFeHByKTtcbmt3KFwiZG9cIiwgeyBpc0xvb3A6IHRydWUgfSk7XG5rdyhcImVsc2VcIiwgYmVmb3JlRXhwcik7XG5rdyhcImZpbmFsbHlcIik7XG5rdyhcImZvclwiLCB7IGlzTG9vcDogdHJ1ZSB9KTtcbmt3KFwiZnVuY3Rpb25cIiwgc3RhcnRzRXhwcik7XG5rdyhcImlmXCIpO1xua3coXCJyZXR1cm5cIiwgYmVmb3JlRXhwcik7XG5rdyhcInN3aXRjaFwiKTtcbmt3KFwidGhyb3dcIiwgYmVmb3JlRXhwcik7XG5rdyhcInRyeVwiKTtcbmt3KFwidmFyXCIpO1xua3coXCJsZXRcIik7XG5rdyhcImNvbnN0XCIpO1xua3coXCJ3aGlsZVwiLCB7IGlzTG9vcDogdHJ1ZSB9KTtcbmt3KFwid2l0aFwiKTtcbmt3KFwibmV3XCIsIHsgYmVmb3JlRXhwcjogdHJ1ZSwgc3RhcnRzRXhwcjogdHJ1ZSB9KTtcbmt3KFwidGhpc1wiLCBzdGFydHNFeHByKTtcbmt3KFwic3VwZXJcIiwgc3RhcnRzRXhwcik7XG5rdyhcImNsYXNzXCIpO1xua3coXCJleHRlbmRzXCIsIGJlZm9yZUV4cHIpO1xua3coXCJleHBvcnRcIik7XG5rdyhcImltcG9ydFwiKTtcbmt3KFwieWllbGRcIiwgeyBiZWZvcmVFeHByOiB0cnVlLCBzdGFydHNFeHByOiB0cnVlIH0pO1xua3coXCJudWxsXCIsIHN0YXJ0c0V4cHIpO1xua3coXCJ0cnVlXCIsIHN0YXJ0c0V4cHIpO1xua3coXCJmYWxzZVwiLCBzdGFydHNFeHByKTtcbmt3KFwiaW5cIiwgeyBiZWZvcmVFeHByOiB0cnVlLCBiaW5vcDogNyB9KTtcbmt3KFwiaW5zdGFuY2VvZlwiLCB7IGJlZm9yZUV4cHI6IHRydWUsIGJpbm9wOiA3IH0pO1xua3coXCJ0eXBlb2ZcIiwgeyBiZWZvcmVFeHByOiB0cnVlLCBwcmVmaXg6IHRydWUsIHN0YXJ0c0V4cHI6IHRydWUgfSk7XG5rdyhcInZvaWRcIiwgeyBiZWZvcmVFeHByOiB0cnVlLCBwcmVmaXg6IHRydWUsIHN0YXJ0c0V4cHI6IHRydWUgfSk7XG5rdyhcImRlbGV0ZVwiLCB7IGJlZm9yZUV4cHI6IHRydWUsIHByZWZpeDogdHJ1ZSwgc3RhcnRzRXhwcjogdHJ1ZSB9KTtcblxufSx7fV0sMTU6W2Z1bmN0aW9uKF9kZXJlcV8sbW9kdWxlLGV4cG9ydHMpe1xuXCJ1c2Ugc3RyaWN0XCI7XG5cbmV4cG9ydHMuX19lc01vZHVsZSA9IHRydWU7XG5leHBvcnRzLmlzQXJyYXkgPSBpc0FycmF5O1xuZXhwb3J0cy5oYXMgPSBoYXM7XG5cbmZ1bmN0aW9uIGlzQXJyYXkob2JqKSB7XG4gIHJldHVybiBPYmplY3QucHJvdG90eXBlLnRvU3RyaW5nLmNhbGwob2JqKSA9PT0gXCJbb2JqZWN0IEFycmF5XVwiO1xufVxuXG4vLyBDaGVja3MgaWYgYW4gb2JqZWN0IGhhcyBhIHByb3BlcnR5LlxuXG5mdW5jdGlvbiBoYXMob2JqLCBwcm9wTmFtZSkge1xuICByZXR1cm4gT2JqZWN0LnByb3RvdHlwZS5oYXNPd25Qcm9wZXJ0eS5jYWxsKG9iaiwgcHJvcE5hbWUpO1xufVxuXG59LHt9XSwxNjpbZnVuY3Rpb24oX2RlcmVxXyxtb2R1bGUsZXhwb3J0cyl7XG4vLyBNYXRjaGVzIGEgd2hvbGUgbGluZSBicmVhayAod2hlcmUgQ1JMRiBpcyBjb25zaWRlcmVkIGEgc2luZ2xlXG4vLyBsaW5lIGJyZWFrKS4gVXNlZCB0byBjb3VudCBsaW5lcy5cblxuXCJ1c2Ugc3RyaWN0XCI7XG5cbmV4cG9ydHMuX19lc01vZHVsZSA9IHRydWU7XG5leHBvcnRzLmlzTmV3TGluZSA9IGlzTmV3TGluZTtcbnZhciBsaW5lQnJlYWsgPSAvXFxyXFxuP3xcXG58XFx1MjAyOHxcXHUyMDI5LztcbmV4cG9ydHMubGluZUJyZWFrID0gbGluZUJyZWFrO1xudmFyIGxpbmVCcmVha0cgPSBuZXcgUmVnRXhwKGxpbmVCcmVhay5zb3VyY2UsIFwiZ1wiKTtcblxuZXhwb3J0cy5saW5lQnJlYWtHID0gbGluZUJyZWFrRztcblxuZnVuY3Rpb24gaXNOZXdMaW5lKGNvZGUpIHtcbiAgcmV0dXJuIGNvZGUgPT09IDEwIHx8IGNvZGUgPT09IDEzIHx8IGNvZGUgPT09IDB4MjAyOCB8fCBjb2RlID09IDB4MjAyOTtcbn1cblxudmFyIG5vbkFTQ0lJd2hpdGVzcGFjZSA9IC9bXFx1MTY4MFxcdTE4MGVcXHUyMDAwLVxcdTIwMGFcXHUyMDJmXFx1MjA1ZlxcdTMwMDBcXHVmZWZmXS87XG5leHBvcnRzLm5vbkFTQ0lJd2hpdGVzcGFjZSA9IG5vbkFTQ0lJd2hpdGVzcGFjZTtcblxufSx7fV19LHt9LFszXSkoMylcbn0pOyIsIihmdW5jdGlvbihmKXtpZih0eXBlb2YgZXhwb3J0cz09PVwib2JqZWN0XCImJnR5cGVvZiBtb2R1bGUhPT1cInVuZGVmaW5lZFwiKXttb2R1bGUuZXhwb3J0cz1mKCl9ZWxzZSBpZih0eXBlb2YgZGVmaW5lPT09XCJmdW5jdGlvblwiJiZkZWZpbmUuYW1kKXtkZWZpbmUoW10sZil9ZWxzZXt2YXIgZztpZih0eXBlb2Ygd2luZG93IT09XCJ1bmRlZmluZWRcIil7Zz13aW5kb3d9ZWxzZSBpZih0eXBlb2YgZ2xvYmFsIT09XCJ1bmRlZmluZWRcIil7Zz1nbG9iYWx9ZWxzZSBpZih0eXBlb2Ygc2VsZiE9PVwidW5kZWZpbmVkXCIpe2c9c2VsZn1lbHNle2c9dGhpc30oZy5hY29ybiB8fCAoZy5hY29ybiA9IHt9KSkubG9vc2UgPSBmKCl9fSkoZnVuY3Rpb24oKXt2YXIgZGVmaW5lLG1vZHVsZSxleHBvcnRzO3JldHVybiAoZnVuY3Rpb24gZSh0LG4scil7ZnVuY3Rpb24gcyhvLHUpe2lmKCFuW29dKXtpZighdFtvXSl7dmFyIGE9dHlwZW9mIHJlcXVpcmU9PVwiZnVuY3Rpb25cIiYmcmVxdWlyZTtpZighdSYmYSlyZXR1cm4gYShvLCEwKTtpZihpKXJldHVybiBpKG8sITApO3ZhciBmPW5ldyBFcnJvcihcIkNhbm5vdCBmaW5kIG1vZHVsZSAnXCIrbytcIidcIik7dGhyb3cgZi5jb2RlPVwiTU9EVUxFX05PVF9GT1VORFwiLGZ9dmFyIGw9bltvXT17ZXhwb3J0czp7fX07dFtvXVswXS5jYWxsKGwuZXhwb3J0cyxmdW5jdGlvbihlKXt2YXIgbj10W29dWzFdW2VdO3JldHVybiBzKG4/bjplKX0sbCxsLmV4cG9ydHMsZSx0LG4scil9cmV0dXJuIG5bb10uZXhwb3J0c312YXIgaT10eXBlb2YgcmVxdWlyZT09XCJmdW5jdGlvblwiJiZyZXF1aXJlO2Zvcih2YXIgbz0wO288ci5sZW5ndGg7bysrKXMocltvXSk7cmV0dXJuIHN9KSh7MTpbZnVuY3Rpb24oX2RlcmVxXyxtb2R1bGUsZXhwb3J0cyl7XG5cInVzZSBzdHJpY3RcIjtcblxubW9kdWxlLmV4cG9ydHMgPSB0eXBlb2YgYWNvcm4gIT0gJ3VuZGVmaW5lZCcgPyBhY29ybiA6IHJlcXVpcmUoXCIuL2Fjb3JuXCIpO1xuXG59LHt9XSwyOltmdW5jdGlvbihfZGVyZXFfLG1vZHVsZSxleHBvcnRzKXtcblwidXNlIHN0cmljdFwiO1xuXG52YXIgX3N0YXRlID0gX2RlcmVxXyhcIi4vc3RhdGVcIik7XG5cbnZhciBfcGFyc2V1dGlsID0gX2RlcmVxXyhcIi4vcGFyc2V1dGlsXCIpO1xuXG52YXIgXyA9IF9kZXJlcV8oXCIuLlwiKTtcblxudmFyIGxwID0gX3N0YXRlLkxvb3NlUGFyc2VyLnByb3RvdHlwZTtcblxubHAuY2hlY2tMVmFsID0gZnVuY3Rpb24gKGV4cHIsIGJpbmRpbmcpIHtcbiAgaWYgKCFleHByKSByZXR1cm4gZXhwcjtcbiAgc3dpdGNoIChleHByLnR5cGUpIHtcbiAgICBjYXNlIFwiSWRlbnRpZmllclwiOlxuICAgICAgcmV0dXJuIGV4cHI7XG5cbiAgICBjYXNlIFwiTWVtYmVyRXhwcmVzc2lvblwiOlxuICAgICAgcmV0dXJuIGJpbmRpbmcgPyB0aGlzLmR1bW15SWRlbnQoKSA6IGV4cHI7XG5cbiAgICBjYXNlIFwiUGFyZW50aGVzaXplZEV4cHJlc3Npb25cIjpcbiAgICAgIGV4cHIuZXhwcmVzc2lvbiA9IHRoaXMuY2hlY2tMVmFsKGV4cHIuZXhwcmVzc2lvbiwgYmluZGluZyk7XG4gICAgICByZXR1cm4gZXhwcjtcblxuICAgIC8vIEZJWE1FIHJlY3Vyc2l2ZWx5IGNoZWNrIGNvbnRlbnRzXG4gICAgY2FzZSBcIk9iamVjdFBhdHRlcm5cIjpcbiAgICBjYXNlIFwiQXJyYXlQYXR0ZXJuXCI6XG4gICAgY2FzZSBcIlJlc3RFbGVtZW50XCI6XG4gICAgY2FzZSBcIkFzc2lnbm1lbnRQYXR0ZXJuXCI6XG4gICAgICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYpIHJldHVybiBleHByO1xuXG4gICAgZGVmYXVsdDpcbiAgICAgIHJldHVybiB0aGlzLmR1bW15SWRlbnQoKTtcbiAgfVxufTtcblxubHAucGFyc2VFeHByZXNzaW9uID0gZnVuY3Rpb24gKG5vSW4pIHtcbiAgdmFyIHN0YXJ0ID0gdGhpcy5zdG9yZUN1cnJlbnRQb3MoKTtcbiAgdmFyIGV4cHIgPSB0aGlzLnBhcnNlTWF5YmVBc3NpZ24obm9Jbik7XG4gIGlmICh0aGlzLnRvay50eXBlID09PSBfLnRva1R5cGVzLmNvbW1hKSB7XG4gICAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0KTtcbiAgICBub2RlLmV4cHJlc3Npb25zID0gW2V4cHJdO1xuICAgIHdoaWxlICh0aGlzLmVhdChfLnRva1R5cGVzLmNvbW1hKSkgbm9kZS5leHByZXNzaW9ucy5wdXNoKHRoaXMucGFyc2VNYXliZUFzc2lnbihub0luKSk7XG4gICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIlNlcXVlbmNlRXhwcmVzc2lvblwiKTtcbiAgfVxuICByZXR1cm4gZXhwcjtcbn07XG5cbmxwLnBhcnNlUGFyZW5FeHByZXNzaW9uID0gZnVuY3Rpb24gKCkge1xuICB0aGlzLnB1c2hDeCgpO1xuICB0aGlzLmV4cGVjdChfLnRva1R5cGVzLnBhcmVuTCk7XG4gIHZhciB2YWwgPSB0aGlzLnBhcnNlRXhwcmVzc2lvbigpO1xuICB0aGlzLnBvcEN4KCk7XG4gIHRoaXMuZXhwZWN0KF8udG9rVHlwZXMucGFyZW5SKTtcbiAgcmV0dXJuIHZhbDtcbn07XG5cbmxwLnBhcnNlTWF5YmVBc3NpZ24gPSBmdW5jdGlvbiAobm9Jbikge1xuICB2YXIgc3RhcnQgPSB0aGlzLnN0b3JlQ3VycmVudFBvcygpO1xuICB2YXIgbGVmdCA9IHRoaXMucGFyc2VNYXliZUNvbmRpdGlvbmFsKG5vSW4pO1xuICBpZiAodGhpcy50b2sudHlwZS5pc0Fzc2lnbikge1xuICAgIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGVBdChzdGFydCk7XG4gICAgbm9kZS5vcGVyYXRvciA9IHRoaXMudG9rLnZhbHVlO1xuICAgIG5vZGUubGVmdCA9IHRoaXMudG9rLnR5cGUgPT09IF8udG9rVHlwZXMuZXEgPyB0aGlzLnRvQXNzaWduYWJsZShsZWZ0KSA6IHRoaXMuY2hlY2tMVmFsKGxlZnQpO1xuICAgIHRoaXMubmV4dCgpO1xuICAgIG5vZGUucmlnaHQgPSB0aGlzLnBhcnNlTWF5YmVBc3NpZ24obm9Jbik7XG4gICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkFzc2lnbm1lbnRFeHByZXNzaW9uXCIpO1xuICB9XG4gIHJldHVybiBsZWZ0O1xufTtcblxubHAucGFyc2VNYXliZUNvbmRpdGlvbmFsID0gZnVuY3Rpb24gKG5vSW4pIHtcbiAgdmFyIHN0YXJ0ID0gdGhpcy5zdG9yZUN1cnJlbnRQb3MoKTtcbiAgdmFyIGV4cHIgPSB0aGlzLnBhcnNlRXhwck9wcyhub0luKTtcbiAgaWYgKHRoaXMuZWF0KF8udG9rVHlwZXMucXVlc3Rpb24pKSB7XG4gICAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0KTtcbiAgICBub2RlLnRlc3QgPSBleHByO1xuICAgIG5vZGUuY29uc2VxdWVudCA9IHRoaXMucGFyc2VNYXliZUFzc2lnbigpO1xuICAgIG5vZGUuYWx0ZXJuYXRlID0gdGhpcy5leHBlY3QoXy50b2tUeXBlcy5jb2xvbikgPyB0aGlzLnBhcnNlTWF5YmVBc3NpZ24obm9JbikgOiB0aGlzLmR1bW15SWRlbnQoKTtcbiAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiQ29uZGl0aW9uYWxFeHByZXNzaW9uXCIpO1xuICB9XG4gIHJldHVybiBleHByO1xufTtcblxubHAucGFyc2VFeHByT3BzID0gZnVuY3Rpb24gKG5vSW4pIHtcbiAgdmFyIHN0YXJ0ID0gdGhpcy5zdG9yZUN1cnJlbnRQb3MoKTtcbiAgdmFyIGluZGVudCA9IHRoaXMuY3VySW5kZW50LFxuICAgICAgbGluZSA9IHRoaXMuY3VyTGluZVN0YXJ0O1xuICByZXR1cm4gdGhpcy5wYXJzZUV4cHJPcCh0aGlzLnBhcnNlTWF5YmVVbmFyeShub0luKSwgc3RhcnQsIC0xLCBub0luLCBpbmRlbnQsIGxpbmUpO1xufTtcblxubHAucGFyc2VFeHByT3AgPSBmdW5jdGlvbiAobGVmdCwgc3RhcnQsIG1pblByZWMsIG5vSW4sIGluZGVudCwgbGluZSkge1xuICBpZiAodGhpcy5jdXJMaW5lU3RhcnQgIT0gbGluZSAmJiB0aGlzLmN1ckluZGVudCA8IGluZGVudCAmJiB0aGlzLnRva2VuU3RhcnRzTGluZSgpKSByZXR1cm4gbGVmdDtcbiAgdmFyIHByZWMgPSB0aGlzLnRvay50eXBlLmJpbm9wO1xuICBpZiAocHJlYyAhPSBudWxsICYmICghbm9JbiB8fCB0aGlzLnRvay50eXBlICE9PSBfLnRva1R5cGVzLl9pbikpIHtcbiAgICBpZiAocHJlYyA+IG1pblByZWMpIHtcbiAgICAgIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGVBdChzdGFydCk7XG4gICAgICBub2RlLmxlZnQgPSBsZWZ0O1xuICAgICAgbm9kZS5vcGVyYXRvciA9IHRoaXMudG9rLnZhbHVlO1xuICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICBpZiAodGhpcy5jdXJMaW5lU3RhcnQgIT0gbGluZSAmJiB0aGlzLmN1ckluZGVudCA8IGluZGVudCAmJiB0aGlzLnRva2VuU3RhcnRzTGluZSgpKSB7XG4gICAgICAgIG5vZGUucmlnaHQgPSB0aGlzLmR1bW15SWRlbnQoKTtcbiAgICAgIH0gZWxzZSB7XG4gICAgICAgIHZhciByaWdodFN0YXJ0ID0gdGhpcy5zdG9yZUN1cnJlbnRQb3MoKTtcbiAgICAgICAgbm9kZS5yaWdodCA9IHRoaXMucGFyc2VFeHByT3AodGhpcy5wYXJzZU1heWJlVW5hcnkobm9JbiksIHJpZ2h0U3RhcnQsIHByZWMsIG5vSW4sIGluZGVudCwgbGluZSk7XG4gICAgICB9XG4gICAgICB0aGlzLmZpbmlzaE5vZGUobm9kZSwgLyYmfFxcfFxcfC8udGVzdChub2RlLm9wZXJhdG9yKSA/IFwiTG9naWNhbEV4cHJlc3Npb25cIiA6IFwiQmluYXJ5RXhwcmVzc2lvblwiKTtcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlRXhwck9wKG5vZGUsIHN0YXJ0LCBtaW5QcmVjLCBub0luLCBpbmRlbnQsIGxpbmUpO1xuICAgIH1cbiAgfVxuICByZXR1cm4gbGVmdDtcbn07XG5cbmxwLnBhcnNlTWF5YmVVbmFyeSA9IGZ1bmN0aW9uIChub0luKSB7XG4gIGlmICh0aGlzLnRvay50eXBlLnByZWZpeCkge1xuICAgIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGUoKSxcbiAgICAgICAgdXBkYXRlID0gdGhpcy50b2sudHlwZSA9PT0gXy50b2tUeXBlcy5pbmNEZWM7XG4gICAgbm9kZS5vcGVyYXRvciA9IHRoaXMudG9rLnZhbHVlO1xuICAgIG5vZGUucHJlZml4ID0gdHJ1ZTtcbiAgICB0aGlzLm5leHQoKTtcbiAgICBub2RlLmFyZ3VtZW50ID0gdGhpcy5wYXJzZU1heWJlVW5hcnkobm9Jbik7XG4gICAgaWYgKHVwZGF0ZSkgbm9kZS5hcmd1bWVudCA9IHRoaXMuY2hlY2tMVmFsKG5vZGUuYXJndW1lbnQpO1xuICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgdXBkYXRlID8gXCJVcGRhdGVFeHByZXNzaW9uXCIgOiBcIlVuYXJ5RXhwcmVzc2lvblwiKTtcbiAgfSBlbHNlIGlmICh0aGlzLnRvay50eXBlID09PSBfLnRva1R5cGVzLmVsbGlwc2lzKSB7XG4gICAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICAgIHRoaXMubmV4dCgpO1xuICAgIG5vZGUuYXJndW1lbnQgPSB0aGlzLnBhcnNlTWF5YmVVbmFyeShub0luKTtcbiAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiU3ByZWFkRWxlbWVudFwiKTtcbiAgfVxuICB2YXIgc3RhcnQgPSB0aGlzLnN0b3JlQ3VycmVudFBvcygpO1xuICB2YXIgZXhwciA9IHRoaXMucGFyc2VFeHByU3Vic2NyaXB0cygpO1xuICB3aGlsZSAodGhpcy50b2sudHlwZS5wb3N0Zml4ICYmICF0aGlzLmNhbkluc2VydFNlbWljb2xvbigpKSB7XG4gICAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0KTtcbiAgICBub2RlLm9wZXJhdG9yID0gdGhpcy50b2sudmFsdWU7XG4gICAgbm9kZS5wcmVmaXggPSBmYWxzZTtcbiAgICBub2RlLmFyZ3VtZW50ID0gdGhpcy5jaGVja0xWYWwoZXhwcik7XG4gICAgdGhpcy5uZXh0KCk7XG4gICAgZXhwciA9IHRoaXMuZmluaXNoTm9kZShub2RlLCBcIlVwZGF0ZUV4cHJlc3Npb25cIik7XG4gIH1cbiAgcmV0dXJuIGV4cHI7XG59O1xuXG5scC5wYXJzZUV4cHJTdWJzY3JpcHRzID0gZnVuY3Rpb24gKCkge1xuICB2YXIgc3RhcnQgPSB0aGlzLnN0b3JlQ3VycmVudFBvcygpO1xuICByZXR1cm4gdGhpcy5wYXJzZVN1YnNjcmlwdHModGhpcy5wYXJzZUV4cHJBdG9tKCksIHN0YXJ0LCBmYWxzZSwgdGhpcy5jdXJJbmRlbnQsIHRoaXMuY3VyTGluZVN0YXJ0KTtcbn07XG5cbmxwLnBhcnNlU3Vic2NyaXB0cyA9IGZ1bmN0aW9uIChiYXNlLCBzdGFydCwgbm9DYWxscywgc3RhcnRJbmRlbnQsIGxpbmUpIHtcbiAgZm9yICg7Oykge1xuICAgIGlmICh0aGlzLmN1ckxpbmVTdGFydCAhPSBsaW5lICYmIHRoaXMuY3VySW5kZW50IDw9IHN0YXJ0SW5kZW50ICYmIHRoaXMudG9rZW5TdGFydHNMaW5lKCkpIHtcbiAgICAgIGlmICh0aGlzLnRvay50eXBlID09IF8udG9rVHlwZXMuZG90ICYmIHRoaXMuY3VySW5kZW50ID09IHN0YXJ0SW5kZW50KSAtLXN0YXJ0SW5kZW50O2Vsc2UgcmV0dXJuIGJhc2U7XG4gICAgfVxuXG4gICAgaWYgKHRoaXMuZWF0KF8udG9rVHlwZXMuZG90KSkge1xuICAgICAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0KTtcbiAgICAgIG5vZGUub2JqZWN0ID0gYmFzZTtcbiAgICAgIGlmICh0aGlzLmN1ckxpbmVTdGFydCAhPSBsaW5lICYmIHRoaXMuY3VySW5kZW50IDw9IHN0YXJ0SW5kZW50ICYmIHRoaXMudG9rZW5TdGFydHNMaW5lKCkpIG5vZGUucHJvcGVydHkgPSB0aGlzLmR1bW15SWRlbnQoKTtlbHNlIG5vZGUucHJvcGVydHkgPSB0aGlzLnBhcnNlUHJvcGVydHlBY2Nlc3NvcigpIHx8IHRoaXMuZHVtbXlJZGVudCgpO1xuICAgICAgbm9kZS5jb21wdXRlZCA9IGZhbHNlO1xuICAgICAgYmFzZSA9IHRoaXMuZmluaXNoTm9kZShub2RlLCBcIk1lbWJlckV4cHJlc3Npb25cIik7XG4gICAgfSBlbHNlIGlmICh0aGlzLnRvay50eXBlID09IF8udG9rVHlwZXMuYnJhY2tldEwpIHtcbiAgICAgIHRoaXMucHVzaEN4KCk7XG4gICAgICB0aGlzLm5leHQoKTtcbiAgICAgIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGVBdChzdGFydCk7XG4gICAgICBub2RlLm9iamVjdCA9IGJhc2U7XG4gICAgICBub2RlLnByb3BlcnR5ID0gdGhpcy5wYXJzZUV4cHJlc3Npb24oKTtcbiAgICAgIG5vZGUuY29tcHV0ZWQgPSB0cnVlO1xuICAgICAgdGhpcy5wb3BDeCgpO1xuICAgICAgdGhpcy5leHBlY3QoXy50b2tUeXBlcy5icmFja2V0Uik7XG4gICAgICBiYXNlID0gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiTWVtYmVyRXhwcmVzc2lvblwiKTtcbiAgICB9IGVsc2UgaWYgKCFub0NhbGxzICYmIHRoaXMudG9rLnR5cGUgPT0gXy50b2tUeXBlcy5wYXJlbkwpIHtcbiAgICAgIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGVBdChzdGFydCk7XG4gICAgICBub2RlLmNhbGxlZSA9IGJhc2U7XG4gICAgICBub2RlLmFyZ3VtZW50cyA9IHRoaXMucGFyc2VFeHByTGlzdChfLnRva1R5cGVzLnBhcmVuUik7XG4gICAgICBiYXNlID0gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiQ2FsbEV4cHJlc3Npb25cIik7XG4gICAgfSBlbHNlIGlmICh0aGlzLnRvay50eXBlID09IF8udG9rVHlwZXMuYmFja1F1b3RlKSB7XG4gICAgICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlQXQoc3RhcnQpO1xuICAgICAgbm9kZS50YWcgPSBiYXNlO1xuICAgICAgbm9kZS5xdWFzaSA9IHRoaXMucGFyc2VUZW1wbGF0ZSgpO1xuICAgICAgYmFzZSA9IHRoaXMuZmluaXNoTm9kZShub2RlLCBcIlRhZ2dlZFRlbXBsYXRlRXhwcmVzc2lvblwiKTtcbiAgICB9IGVsc2Uge1xuICAgICAgcmV0dXJuIGJhc2U7XG4gICAgfVxuICB9XG59O1xuXG5scC5wYXJzZUV4cHJBdG9tID0gZnVuY3Rpb24gKCkge1xuICB2YXIgbm9kZSA9IHVuZGVmaW5lZDtcbiAgc3dpdGNoICh0aGlzLnRvay50eXBlKSB7XG4gICAgY2FzZSBfLnRva1R5cGVzLl90aGlzOlxuICAgIGNhc2UgXy50b2tUeXBlcy5fc3VwZXI6XG4gICAgICB2YXIgdHlwZSA9IHRoaXMudG9rLnR5cGUgPT09IF8udG9rVHlwZXMuX3RoaXMgPyBcIlRoaXNFeHByZXNzaW9uXCIgOiBcIlN1cGVyXCI7XG4gICAgICBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCB0eXBlKTtcblxuICAgIGNhc2UgXy50b2tUeXBlcy5uYW1lOlxuICAgICAgdmFyIHN0YXJ0ID0gdGhpcy5zdG9yZUN1cnJlbnRQb3MoKTtcbiAgICAgIHZhciBpZCA9IHRoaXMucGFyc2VJZGVudCgpO1xuICAgICAgcmV0dXJuIHRoaXMuZWF0KF8udG9rVHlwZXMuYXJyb3cpID8gdGhpcy5wYXJzZUFycm93RXhwcmVzc2lvbih0aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0KSwgW2lkXSkgOiBpZDtcblxuICAgIGNhc2UgXy50b2tUeXBlcy5yZWdleHA6XG4gICAgICBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgICAgIHZhciB2YWwgPSB0aGlzLnRvay52YWx1ZTtcbiAgICAgIG5vZGUucmVnZXggPSB7IHBhdHRlcm46IHZhbC5wYXR0ZXJuLCBmbGFnczogdmFsLmZsYWdzIH07XG4gICAgICBub2RlLnZhbHVlID0gdmFsLnZhbHVlO1xuICAgICAgbm9kZS5yYXcgPSB0aGlzLmlucHV0LnNsaWNlKHRoaXMudG9rLnN0YXJ0LCB0aGlzLnRvay5lbmQpO1xuICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiTGl0ZXJhbFwiKTtcblxuICAgIGNhc2UgXy50b2tUeXBlcy5udW06Y2FzZSBfLnRva1R5cGVzLnN0cmluZzpcbiAgICAgIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICAgICAgbm9kZS52YWx1ZSA9IHRoaXMudG9rLnZhbHVlO1xuICAgICAgbm9kZS5yYXcgPSB0aGlzLmlucHV0LnNsaWNlKHRoaXMudG9rLnN0YXJ0LCB0aGlzLnRvay5lbmQpO1xuICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiTGl0ZXJhbFwiKTtcblxuICAgIGNhc2UgXy50b2tUeXBlcy5fbnVsbDpjYXNlIF8udG9rVHlwZXMuX3RydWU6Y2FzZSBfLnRva1R5cGVzLl9mYWxzZTpcbiAgICAgIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICAgICAgbm9kZS52YWx1ZSA9IHRoaXMudG9rLnR5cGUgPT09IF8udG9rVHlwZXMuX251bGwgPyBudWxsIDogdGhpcy50b2sudHlwZSA9PT0gXy50b2tUeXBlcy5fdHJ1ZTtcbiAgICAgIG5vZGUucmF3ID0gdGhpcy50b2sudHlwZS5rZXl3b3JkO1xuICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiTGl0ZXJhbFwiKTtcblxuICAgIGNhc2UgXy50b2tUeXBlcy5wYXJlbkw6XG4gICAgICB2YXIgcGFyZW5TdGFydCA9IHRoaXMuc3RvcmVDdXJyZW50UG9zKCk7XG4gICAgICB0aGlzLm5leHQoKTtcbiAgICAgIHZhciBpbm5lciA9IHRoaXMucGFyc2VFeHByZXNzaW9uKCk7XG4gICAgICB0aGlzLmV4cGVjdChfLnRva1R5cGVzLnBhcmVuUik7XG4gICAgICBpZiAodGhpcy5lYXQoXy50b2tUeXBlcy5hcnJvdykpIHtcbiAgICAgICAgcmV0dXJuIHRoaXMucGFyc2VBcnJvd0V4cHJlc3Npb24odGhpcy5zdGFydE5vZGVBdChwYXJlblN0YXJ0KSwgaW5uZXIuZXhwcmVzc2lvbnMgfHwgKF9wYXJzZXV0aWwuaXNEdW1teShpbm5lcikgPyBbXSA6IFtpbm5lcl0pKTtcbiAgICAgIH1cbiAgICAgIGlmICh0aGlzLm9wdGlvbnMucHJlc2VydmVQYXJlbnMpIHtcbiAgICAgICAgdmFyIHBhciA9IHRoaXMuc3RhcnROb2RlQXQocGFyZW5TdGFydCk7XG4gICAgICAgIHBhci5leHByZXNzaW9uID0gaW5uZXI7XG4gICAgICAgIGlubmVyID0gdGhpcy5maW5pc2hOb2RlKHBhciwgXCJQYXJlbnRoZXNpemVkRXhwcmVzc2lvblwiKTtcbiAgICAgIH1cbiAgICAgIHJldHVybiBpbm5lcjtcblxuICAgIGNhc2UgXy50b2tUeXBlcy5icmFja2V0TDpcbiAgICAgIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICAgICAgbm9kZS5lbGVtZW50cyA9IHRoaXMucGFyc2VFeHByTGlzdChfLnRva1R5cGVzLmJyYWNrZXRSLCB0cnVlKTtcbiAgICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJBcnJheUV4cHJlc3Npb25cIik7XG5cbiAgICBjYXNlIF8udG9rVHlwZXMuYnJhY2VMOlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VPYmooKTtcblxuICAgIGNhc2UgXy50b2tUeXBlcy5fY2xhc3M6XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZUNsYXNzKCk7XG5cbiAgICBjYXNlIF8udG9rVHlwZXMuX2Z1bmN0aW9uOlxuICAgICAgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gICAgICB0aGlzLm5leHQoKTtcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlRnVuY3Rpb24obm9kZSwgZmFsc2UpO1xuXG4gICAgY2FzZSBfLnRva1R5cGVzLl9uZXc6XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZU5ldygpO1xuXG4gICAgY2FzZSBfLnRva1R5cGVzLl95aWVsZDpcbiAgICAgIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICBpZiAodGhpcy5zZW1pY29sb24oKSB8fCB0aGlzLmNhbkluc2VydFNlbWljb2xvbigpIHx8IHRoaXMudG9rLnR5cGUgIT0gXy50b2tUeXBlcy5zdGFyICYmICF0aGlzLnRvay50eXBlLnN0YXJ0c0V4cHIpIHtcbiAgICAgICAgbm9kZS5kZWxlZ2F0ZSA9IGZhbHNlO1xuICAgICAgICBub2RlLmFyZ3VtZW50ID0gbnVsbDtcbiAgICAgIH0gZWxzZSB7XG4gICAgICAgIG5vZGUuZGVsZWdhdGUgPSB0aGlzLmVhdChfLnRva1R5cGVzLnN0YXIpO1xuICAgICAgICBub2RlLmFyZ3VtZW50ID0gdGhpcy5wYXJzZU1heWJlQXNzaWduKCk7XG4gICAgICB9XG4gICAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiWWllbGRFeHByZXNzaW9uXCIpO1xuXG4gICAgY2FzZSBfLnRva1R5cGVzLmJhY2tRdW90ZTpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlVGVtcGxhdGUoKTtcblxuICAgIGRlZmF1bHQ6XG4gICAgICByZXR1cm4gdGhpcy5kdW1teUlkZW50KCk7XG4gIH1cbn07XG5cbmxwLnBhcnNlTmV3ID0gZnVuY3Rpb24gKCkge1xuICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCksXG4gICAgICBzdGFydEluZGVudCA9IHRoaXMuY3VySW5kZW50LFxuICAgICAgbGluZSA9IHRoaXMuY3VyTGluZVN0YXJ0O1xuICB2YXIgbWV0YSA9IHRoaXMucGFyc2VJZGVudCh0cnVlKTtcbiAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2ICYmIHRoaXMuZWF0KF8udG9rVHlwZXMuZG90KSkge1xuICAgIG5vZGUubWV0YSA9IG1ldGE7XG4gICAgbm9kZS5wcm9wZXJ0eSA9IHRoaXMucGFyc2VJZGVudCh0cnVlKTtcbiAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiTWV0YVByb3BlcnR5XCIpO1xuICB9XG4gIHZhciBzdGFydCA9IHRoaXMuc3RvcmVDdXJyZW50UG9zKCk7XG4gIG5vZGUuY2FsbGVlID0gdGhpcy5wYXJzZVN1YnNjcmlwdHModGhpcy5wYXJzZUV4cHJBdG9tKCksIHN0YXJ0LCB0cnVlLCBzdGFydEluZGVudCwgbGluZSk7XG4gIGlmICh0aGlzLnRvay50eXBlID09IF8udG9rVHlwZXMucGFyZW5MKSB7XG4gICAgbm9kZS5hcmd1bWVudHMgPSB0aGlzLnBhcnNlRXhwckxpc3QoXy50b2tUeXBlcy5wYXJlblIpO1xuICB9IGVsc2Uge1xuICAgIG5vZGUuYXJndW1lbnRzID0gW107XG4gIH1cbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIk5ld0V4cHJlc3Npb25cIik7XG59O1xuXG5scC5wYXJzZVRlbXBsYXRlRWxlbWVudCA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIGVsZW0gPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICBlbGVtLnZhbHVlID0ge1xuICAgIHJhdzogdGhpcy5pbnB1dC5zbGljZSh0aGlzLnRvay5zdGFydCwgdGhpcy50b2suZW5kKS5yZXBsYWNlKC9cXHJcXG4/L2csIFwiXFxuXCIpLFxuICAgIGNvb2tlZDogdGhpcy50b2sudmFsdWVcbiAgfTtcbiAgdGhpcy5uZXh0KCk7XG4gIGVsZW0udGFpbCA9IHRoaXMudG9rLnR5cGUgPT09IF8udG9rVHlwZXMuYmFja1F1b3RlO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKGVsZW0sIFwiVGVtcGxhdGVFbGVtZW50XCIpO1xufTtcblxubHAucGFyc2VUZW1wbGF0ZSA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICB0aGlzLm5leHQoKTtcbiAgbm9kZS5leHByZXNzaW9ucyA9IFtdO1xuICB2YXIgY3VyRWx0ID0gdGhpcy5wYXJzZVRlbXBsYXRlRWxlbWVudCgpO1xuICBub2RlLnF1YXNpcyA9IFtjdXJFbHRdO1xuICB3aGlsZSAoIWN1ckVsdC50YWlsKSB7XG4gICAgdGhpcy5uZXh0KCk7XG4gICAgbm9kZS5leHByZXNzaW9ucy5wdXNoKHRoaXMucGFyc2VFeHByZXNzaW9uKCkpO1xuICAgIGlmICh0aGlzLmV4cGVjdChfLnRva1R5cGVzLmJyYWNlUikpIHtcbiAgICAgIGN1ckVsdCA9IHRoaXMucGFyc2VUZW1wbGF0ZUVsZW1lbnQoKTtcbiAgICB9IGVsc2Uge1xuICAgICAgY3VyRWx0ID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgICAgIGN1ckVsdC52YWx1ZSA9IHsgY29va2VkOiBcIlwiLCByYXc6IFwiXCIgfTtcbiAgICAgIGN1ckVsdC50YWlsID0gdHJ1ZTtcbiAgICB9XG4gICAgbm9kZS5xdWFzaXMucHVzaChjdXJFbHQpO1xuICB9XG4gIHRoaXMuZXhwZWN0KF8udG9rVHlwZXMuYmFja1F1b3RlKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIlRlbXBsYXRlTGl0ZXJhbFwiKTtcbn07XG5cbmxwLnBhcnNlT2JqID0gZnVuY3Rpb24gKCkge1xuICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gIG5vZGUucHJvcGVydGllcyA9IFtdO1xuICB0aGlzLnB1c2hDeCgpO1xuICB2YXIgaW5kZW50ID0gdGhpcy5jdXJJbmRlbnQgKyAxLFxuICAgICAgbGluZSA9IHRoaXMuY3VyTGluZVN0YXJ0O1xuICB0aGlzLmVhdChfLnRva1R5cGVzLmJyYWNlTCk7XG4gIGlmICh0aGlzLmN1ckluZGVudCArIDEgPCBpbmRlbnQpIHtcbiAgICBpbmRlbnQgPSB0aGlzLmN1ckluZGVudDtsaW5lID0gdGhpcy5jdXJMaW5lU3RhcnQ7XG4gIH1cbiAgd2hpbGUgKCF0aGlzLmNsb3NlcyhfLnRva1R5cGVzLmJyYWNlUiwgaW5kZW50LCBsaW5lKSkge1xuICAgIHZhciBwcm9wID0gdGhpcy5zdGFydE5vZGUoKSxcbiAgICAgICAgaXNHZW5lcmF0b3IgPSB1bmRlZmluZWQsXG4gICAgICAgIHN0YXJ0ID0gdW5kZWZpbmVkO1xuICAgIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNikge1xuICAgICAgc3RhcnQgPSB0aGlzLnN0b3JlQ3VycmVudFBvcygpO1xuICAgICAgcHJvcC5tZXRob2QgPSBmYWxzZTtcbiAgICAgIHByb3Auc2hvcnRoYW5kID0gZmFsc2U7XG4gICAgICBpc0dlbmVyYXRvciA9IHRoaXMuZWF0KF8udG9rVHlwZXMuc3Rhcik7XG4gICAgfVxuICAgIHRoaXMucGFyc2VQcm9wZXJ0eU5hbWUocHJvcCk7XG4gICAgaWYgKF9wYXJzZXV0aWwuaXNEdW1teShwcm9wLmtleSkpIHtcbiAgICAgIGlmIChfcGFyc2V1dGlsLmlzRHVtbXkodGhpcy5wYXJzZU1heWJlQXNzaWduKCkpKSB0aGlzLm5leHQoKTt0aGlzLmVhdChfLnRva1R5cGVzLmNvbW1hKTtjb250aW51ZTtcbiAgICB9XG4gICAgaWYgKHRoaXMuZWF0KF8udG9rVHlwZXMuY29sb24pKSB7XG4gICAgICBwcm9wLmtpbmQgPSBcImluaXRcIjtcbiAgICAgIHByb3AudmFsdWUgPSB0aGlzLnBhcnNlTWF5YmVBc3NpZ24oKTtcbiAgICB9IGVsc2UgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2ICYmICh0aGlzLnRvay50eXBlID09PSBfLnRva1R5cGVzLnBhcmVuTCB8fCB0aGlzLnRvay50eXBlID09PSBfLnRva1R5cGVzLmJyYWNlTCkpIHtcbiAgICAgIHByb3Aua2luZCA9IFwiaW5pdFwiO1xuICAgICAgcHJvcC5tZXRob2QgPSB0cnVlO1xuICAgICAgcHJvcC52YWx1ZSA9IHRoaXMucGFyc2VNZXRob2QoaXNHZW5lcmF0b3IpO1xuICAgIH0gZWxzZSBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDUgJiYgcHJvcC5rZXkudHlwZSA9PT0gXCJJZGVudGlmaWVyXCIgJiYgIXByb3AuY29tcHV0ZWQgJiYgKHByb3Aua2V5Lm5hbWUgPT09IFwiZ2V0XCIgfHwgcHJvcC5rZXkubmFtZSA9PT0gXCJzZXRcIikgJiYgKHRoaXMudG9rLnR5cGUgIT0gXy50b2tUeXBlcy5jb21tYSAmJiB0aGlzLnRvay50eXBlICE9IF8udG9rVHlwZXMuYnJhY2VSKSkge1xuICAgICAgcHJvcC5raW5kID0gcHJvcC5rZXkubmFtZTtcbiAgICAgIHRoaXMucGFyc2VQcm9wZXJ0eU5hbWUocHJvcCk7XG4gICAgICBwcm9wLnZhbHVlID0gdGhpcy5wYXJzZU1ldGhvZChmYWxzZSk7XG4gICAgfSBlbHNlIHtcbiAgICAgIHByb3Aua2luZCA9IFwiaW5pdFwiO1xuICAgICAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KSB7XG4gICAgICAgIGlmICh0aGlzLmVhdChfLnRva1R5cGVzLmVxKSkge1xuICAgICAgICAgIHZhciBhc3NpZ24gPSB0aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0KTtcbiAgICAgICAgICBhc3NpZ24ub3BlcmF0b3IgPSBcIj1cIjtcbiAgICAgICAgICBhc3NpZ24ubGVmdCA9IHByb3Aua2V5O1xuICAgICAgICAgIGFzc2lnbi5yaWdodCA9IHRoaXMucGFyc2VNYXliZUFzc2lnbigpO1xuICAgICAgICAgIHByb3AudmFsdWUgPSB0aGlzLmZpbmlzaE5vZGUoYXNzaWduLCBcIkFzc2lnbm1lbnRFeHByZXNzaW9uXCIpO1xuICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgIHByb3AudmFsdWUgPSBwcm9wLmtleTtcbiAgICAgICAgfVxuICAgICAgfSBlbHNlIHtcbiAgICAgICAgcHJvcC52YWx1ZSA9IHRoaXMuZHVtbXlJZGVudCgpO1xuICAgICAgfVxuICAgICAgcHJvcC5zaG9ydGhhbmQgPSB0cnVlO1xuICAgIH1cbiAgICBub2RlLnByb3BlcnRpZXMucHVzaCh0aGlzLmZpbmlzaE5vZGUocHJvcCwgXCJQcm9wZXJ0eVwiKSk7XG4gICAgdGhpcy5lYXQoXy50b2tUeXBlcy5jb21tYSk7XG4gIH1cbiAgdGhpcy5wb3BDeCgpO1xuICBpZiAoIXRoaXMuZWF0KF8udG9rVHlwZXMuYnJhY2VSKSkge1xuICAgIC8vIElmIHRoZXJlIGlzIG5vIGNsb3NpbmcgYnJhY2UsIG1ha2UgdGhlIG5vZGUgc3BhbiB0byB0aGUgc3RhcnRcbiAgICAvLyBvZiB0aGUgbmV4dCB0b2tlbiAodGhpcyBpcyB1c2VmdWwgZm9yIFRlcm4pXG4gICAgdGhpcy5sYXN0LmVuZCA9IHRoaXMudG9rLnN0YXJ0O1xuICAgIGlmICh0aGlzLm9wdGlvbnMubG9jYXRpb25zKSB0aGlzLmxhc3QubG9jLmVuZCA9IHRoaXMudG9rLmxvYy5zdGFydDtcbiAgfVxuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiT2JqZWN0RXhwcmVzc2lvblwiKTtcbn07XG5cbmxwLnBhcnNlUHJvcGVydHlOYW1lID0gZnVuY3Rpb24gKHByb3ApIHtcbiAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KSB7XG4gICAgaWYgKHRoaXMuZWF0KF8udG9rVHlwZXMuYnJhY2tldEwpKSB7XG4gICAgICBwcm9wLmNvbXB1dGVkID0gdHJ1ZTtcbiAgICAgIHByb3Aua2V5ID0gdGhpcy5wYXJzZUV4cHJlc3Npb24oKTtcbiAgICAgIHRoaXMuZXhwZWN0KF8udG9rVHlwZXMuYnJhY2tldFIpO1xuICAgICAgcmV0dXJuO1xuICAgIH0gZWxzZSB7XG4gICAgICBwcm9wLmNvbXB1dGVkID0gZmFsc2U7XG4gICAgfVxuICB9XG4gIHZhciBrZXkgPSB0aGlzLnRvay50eXBlID09PSBfLnRva1R5cGVzLm51bSB8fCB0aGlzLnRvay50eXBlID09PSBfLnRva1R5cGVzLnN0cmluZyA/IHRoaXMucGFyc2VFeHByQXRvbSgpIDogdGhpcy5wYXJzZUlkZW50KCk7XG4gIHByb3Aua2V5ID0ga2V5IHx8IHRoaXMuZHVtbXlJZGVudCgpO1xufTtcblxubHAucGFyc2VQcm9wZXJ0eUFjY2Vzc29yID0gZnVuY3Rpb24gKCkge1xuICBpZiAodGhpcy50b2sudHlwZSA9PT0gXy50b2tUeXBlcy5uYW1lIHx8IHRoaXMudG9rLnR5cGUua2V5d29yZCkgcmV0dXJuIHRoaXMucGFyc2VJZGVudCgpO1xufTtcblxubHAucGFyc2VJZGVudCA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIG5hbWUgPSB0aGlzLnRvay50eXBlID09PSBfLnRva1R5cGVzLm5hbWUgPyB0aGlzLnRvay52YWx1ZSA6IHRoaXMudG9rLnR5cGUua2V5d29yZDtcbiAgaWYgKCFuYW1lKSByZXR1cm4gdGhpcy5kdW1teUlkZW50KCk7XG4gIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgdGhpcy5uZXh0KCk7XG4gIG5vZGUubmFtZSA9IG5hbWU7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJJZGVudGlmaWVyXCIpO1xufTtcblxubHAuaW5pdEZ1bmN0aW9uID0gZnVuY3Rpb24gKG5vZGUpIHtcbiAgbm9kZS5pZCA9IG51bGw7XG4gIG5vZGUucGFyYW1zID0gW107XG4gIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNikge1xuICAgIG5vZGUuZ2VuZXJhdG9yID0gZmFsc2U7XG4gICAgbm9kZS5leHByZXNzaW9uID0gZmFsc2U7XG4gIH1cbn07XG5cbi8vIENvbnZlcnQgZXhpc3RpbmcgZXhwcmVzc2lvbiBhdG9tIHRvIGFzc2lnbmFibGUgcGF0dGVyblxuLy8gaWYgcG9zc2libGUuXG5cbmxwLnRvQXNzaWduYWJsZSA9IGZ1bmN0aW9uIChub2RlLCBiaW5kaW5nKSB7XG4gIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNiAmJiBub2RlKSB7XG4gICAgc3dpdGNoIChub2RlLnR5cGUpIHtcbiAgICAgIGNhc2UgXCJPYmplY3RFeHByZXNzaW9uXCI6XG4gICAgICAgIG5vZGUudHlwZSA9IFwiT2JqZWN0UGF0dGVyblwiO1xuICAgICAgICB2YXIgcHJvcHMgPSBub2RlLnByb3BlcnRpZXM7XG4gICAgICAgIGZvciAodmFyIGkgPSAwOyBpIDwgcHJvcHMubGVuZ3RoOyBpKyspIHtcbiAgICAgICAgICB0aGlzLnRvQXNzaWduYWJsZShwcm9wc1tpXS52YWx1ZSwgYmluZGluZyk7XG4gICAgICAgIH1icmVhaztcblxuICAgICAgY2FzZSBcIkFycmF5RXhwcmVzc2lvblwiOlxuICAgICAgICBub2RlLnR5cGUgPSBcIkFycmF5UGF0dGVyblwiO1xuICAgICAgICB0aGlzLnRvQXNzaWduYWJsZUxpc3Qobm9kZS5lbGVtZW50cywgYmluZGluZyk7XG4gICAgICAgIGJyZWFrO1xuXG4gICAgICBjYXNlIFwiU3ByZWFkRWxlbWVudFwiOlxuICAgICAgICBub2RlLnR5cGUgPSBcIlJlc3RFbGVtZW50XCI7XG4gICAgICAgIG5vZGUuYXJndW1lbnQgPSB0aGlzLnRvQXNzaWduYWJsZShub2RlLmFyZ3VtZW50LCBiaW5kaW5nKTtcbiAgICAgICAgYnJlYWs7XG5cbiAgICAgIGNhc2UgXCJBc3NpZ25tZW50RXhwcmVzc2lvblwiOlxuICAgICAgICBub2RlLnR5cGUgPSBcIkFzc2lnbm1lbnRQYXR0ZXJuXCI7XG4gICAgICAgIGRlbGV0ZSBub2RlLm9wZXJhdG9yO1xuICAgICAgICBicmVhaztcbiAgICB9XG4gIH1cbiAgcmV0dXJuIHRoaXMuY2hlY2tMVmFsKG5vZGUsIGJpbmRpbmcpO1xufTtcblxubHAudG9Bc3NpZ25hYmxlTGlzdCA9IGZ1bmN0aW9uIChleHByTGlzdCwgYmluZGluZykge1xuICBmb3IgKHZhciBpID0gMDsgaSA8IGV4cHJMaXN0Lmxlbmd0aDsgaSsrKSB7XG4gICAgZXhwckxpc3RbaV0gPSB0aGlzLnRvQXNzaWduYWJsZShleHByTGlzdFtpXSwgYmluZGluZyk7XG4gIH1yZXR1cm4gZXhwckxpc3Q7XG59O1xuXG5scC5wYXJzZUZ1bmN0aW9uUGFyYW1zID0gZnVuY3Rpb24gKHBhcmFtcykge1xuICBwYXJhbXMgPSB0aGlzLnBhcnNlRXhwckxpc3QoXy50b2tUeXBlcy5wYXJlblIpO1xuICByZXR1cm4gdGhpcy50b0Fzc2lnbmFibGVMaXN0KHBhcmFtcywgdHJ1ZSk7XG59O1xuXG5scC5wYXJzZU1ldGhvZCA9IGZ1bmN0aW9uIChpc0dlbmVyYXRvcikge1xuICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gIHRoaXMuaW5pdEZ1bmN0aW9uKG5vZGUpO1xuICBub2RlLnBhcmFtcyA9IHRoaXMucGFyc2VGdW5jdGlvblBhcmFtcygpO1xuICBub2RlLmdlbmVyYXRvciA9IGlzR2VuZXJhdG9yIHx8IGZhbHNlO1xuICBub2RlLmV4cHJlc3Npb24gPSB0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNiAmJiB0aGlzLnRvay50eXBlICE9PSBfLnRva1R5cGVzLmJyYWNlTDtcbiAgbm9kZS5ib2R5ID0gbm9kZS5leHByZXNzaW9uID8gdGhpcy5wYXJzZU1heWJlQXNzaWduKCkgOiB0aGlzLnBhcnNlQmxvY2soKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkZ1bmN0aW9uRXhwcmVzc2lvblwiKTtcbn07XG5cbmxwLnBhcnNlQXJyb3dFeHByZXNzaW9uID0gZnVuY3Rpb24gKG5vZGUsIHBhcmFtcykge1xuICB0aGlzLmluaXRGdW5jdGlvbihub2RlKTtcbiAgbm9kZS5wYXJhbXMgPSB0aGlzLnRvQXNzaWduYWJsZUxpc3QocGFyYW1zLCB0cnVlKTtcbiAgbm9kZS5leHByZXNzaW9uID0gdGhpcy50b2sudHlwZSAhPT0gXy50b2tUeXBlcy5icmFjZUw7XG4gIG5vZGUuYm9keSA9IG5vZGUuZXhwcmVzc2lvbiA/IHRoaXMucGFyc2VNYXliZUFzc2lnbigpIDogdGhpcy5wYXJzZUJsb2NrKCk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJBcnJvd0Z1bmN0aW9uRXhwcmVzc2lvblwiKTtcbn07XG5cbmxwLnBhcnNlRXhwckxpc3QgPSBmdW5jdGlvbiAoY2xvc2UsIGFsbG93RW1wdHkpIHtcbiAgdGhpcy5wdXNoQ3goKTtcbiAgdmFyIGluZGVudCA9IHRoaXMuY3VySW5kZW50LFxuICAgICAgbGluZSA9IHRoaXMuY3VyTGluZVN0YXJ0LFxuICAgICAgZWx0cyA9IFtdO1xuICB0aGlzLm5leHQoKTsgLy8gT3BlbmluZyBicmFja2V0XG4gIHdoaWxlICghdGhpcy5jbG9zZXMoY2xvc2UsIGluZGVudCArIDEsIGxpbmUpKSB7XG4gICAgaWYgKHRoaXMuZWF0KF8udG9rVHlwZXMuY29tbWEpKSB7XG4gICAgICBlbHRzLnB1c2goYWxsb3dFbXB0eSA/IG51bGwgOiB0aGlzLmR1bW15SWRlbnQoKSk7XG4gICAgICBjb250aW51ZTtcbiAgICB9XG4gICAgdmFyIGVsdCA9IHRoaXMucGFyc2VNYXliZUFzc2lnbigpO1xuICAgIGlmIChfcGFyc2V1dGlsLmlzRHVtbXkoZWx0KSkge1xuICAgICAgaWYgKHRoaXMuY2xvc2VzKGNsb3NlLCBpbmRlbnQsIGxpbmUpKSBicmVhaztcbiAgICAgIHRoaXMubmV4dCgpO1xuICAgIH0gZWxzZSB7XG4gICAgICBlbHRzLnB1c2goZWx0KTtcbiAgICB9XG4gICAgdGhpcy5lYXQoXy50b2tUeXBlcy5jb21tYSk7XG4gIH1cbiAgdGhpcy5wb3BDeCgpO1xuICBpZiAoIXRoaXMuZWF0KGNsb3NlKSkge1xuICAgIC8vIElmIHRoZXJlIGlzIG5vIGNsb3NpbmcgYnJhY2UsIG1ha2UgdGhlIG5vZGUgc3BhbiB0byB0aGUgc3RhcnRcbiAgICAvLyBvZiB0aGUgbmV4dCB0b2tlbiAodGhpcyBpcyB1c2VmdWwgZm9yIFRlcm4pXG4gICAgdGhpcy5sYXN0LmVuZCA9IHRoaXMudG9rLnN0YXJ0O1xuICAgIGlmICh0aGlzLm9wdGlvbnMubG9jYXRpb25zKSB0aGlzLmxhc3QubG9jLmVuZCA9IHRoaXMudG9rLmxvYy5zdGFydDtcbiAgfVxuICByZXR1cm4gZWx0cztcbn07XG5cbn0se1wiLi5cIjoxLFwiLi9wYXJzZXV0aWxcIjo0LFwiLi9zdGF0ZVwiOjV9XSwzOltmdW5jdGlvbihfZGVyZXFfLG1vZHVsZSxleHBvcnRzKXtcbi8vIEFjb3JuOiBMb29zZSBwYXJzZXJcbi8vXG4vLyBUaGlzIG1vZHVsZSBwcm92aWRlcyBhbiBhbHRlcm5hdGl2ZSBwYXJzZXIgKGBwYXJzZV9kYW1taXRgKSB0aGF0XG4vLyBleHBvc2VzIHRoYXQgc2FtZSBpbnRlcmZhY2UgYXMgYHBhcnNlYCwgYnV0IHdpbGwgdHJ5IHRvIHBhcnNlXG4vLyBhbnl0aGluZyBhcyBKYXZhU2NyaXB0LCByZXBhaXJpbmcgc3ludGF4IGVycm9yIHRoZSBiZXN0IGl0IGNhbi5cbi8vIFRoZXJlIGFyZSBjaXJjdW1zdGFuY2VzIGluIHdoaWNoIGl0IHdpbGwgcmFpc2UgYW4gZXJyb3IgYW5kIGdpdmVcbi8vIHVwLCBidXQgdGhleSBhcmUgdmVyeSByYXJlLiBUaGUgcmVzdWx0aW5nIEFTVCB3aWxsIGJlIGEgbW9zdGx5XG4vLyB2YWxpZCBKYXZhU2NyaXB0IEFTVCAoYXMgcGVyIHRoZSBbTW96aWxsYSBwYXJzZXIgQVBJXVthcGldLCBleGNlcHRcbi8vIHRoYXQ6XG4vL1xuLy8gLSBSZXR1cm4gb3V0c2lkZSBmdW5jdGlvbnMgaXMgYWxsb3dlZFxuLy9cbi8vIC0gTGFiZWwgY29uc2lzdGVuY3kgKG5vIGNvbmZsaWN0cywgYnJlYWsgb25seSB0byBleGlzdGluZyBsYWJlbHMpXG4vLyAgIGlzIG5vdCBlbmZvcmNlZC5cbi8vXG4vLyAtIEJvZ3VzIElkZW50aWZpZXIgbm9kZXMgd2l0aCBhIG5hbWUgb2YgYFwi4pyWXCJgIGFyZSBpbnNlcnRlZCB3aGVuZXZlclxuLy8gICB0aGUgcGFyc2VyIGdvdCB0b28gY29uZnVzZWQgdG8gcmV0dXJuIGFueXRoaW5nIG1lYW5pbmdmdWwuXG4vL1xuLy8gW2FwaV06IGh0dHBzOi8vZGV2ZWxvcGVyLm1vemlsbGEub3JnL2VuLVVTL2RvY3MvU3BpZGVyTW9ua2V5L1BhcnNlcl9BUElcbi8vXG4vLyBUaGUgZXhwZWN0ZWQgdXNlIGZvciB0aGlzIGlzIHRvICpmaXJzdCogdHJ5IGBhY29ybi5wYXJzZWAsIGFuZCBvbmx5XG4vLyBpZiB0aGF0IGZhaWxzIHN3aXRjaCB0byBgcGFyc2VfZGFtbWl0YC4gVGhlIGxvb3NlIHBhcnNlciBtaWdodFxuLy8gcGFyc2UgYmFkbHkgaW5kZW50ZWQgY29kZSBpbmNvcnJlY3RseSwgc28gKipkb24ndCoqIHVzZSBpdCBhc1xuLy8geW91ciBkZWZhdWx0IHBhcnNlci5cbi8vXG4vLyBRdWl0ZSBhIGxvdCBvZiBhY29ybi5qcyBpcyBkdXBsaWNhdGVkIGhlcmUuIFRoZSBhbHRlcm5hdGl2ZSB3YXMgdG9cbi8vIGFkZCBhICpsb3QqIG9mIGV4dHJhIGNydWZ0IHRvIHRoYXQgZmlsZSwgbWFraW5nIGl0IGxlc3MgcmVhZGFibGVcbi8vIGFuZCBzbG93ZXIuIENvcHlpbmcgYW5kIGVkaXRpbmcgdGhlIGNvZGUgYWxsb3dlZCBtZSB0byBtYWtlXG4vLyBpbnZhc2l2ZSBjaGFuZ2VzIGFuZCBzaW1wbGlmaWNhdGlvbnMgd2l0aG91dCBjcmVhdGluZyBhIGNvbXBsaWNhdGVkXG4vLyB0YW5nbGUuXG5cblwidXNlIHN0cmljdFwiO1xuXG5leHBvcnRzLl9fZXNNb2R1bGUgPSB0cnVlO1xuZXhwb3J0cy5wYXJzZV9kYW1taXQgPSBwYXJzZV9kYW1taXQ7XG5cbmZ1bmN0aW9uIF9pbnRlcm9wUmVxdWlyZVdpbGRjYXJkKG9iaikgeyBpZiAob2JqICYmIG9iai5fX2VzTW9kdWxlKSB7IHJldHVybiBvYmo7IH0gZWxzZSB7IHZhciBuZXdPYmogPSB7fTsgaWYgKG9iaiAhPSBudWxsKSB7IGZvciAodmFyIGtleSBpbiBvYmopIHsgaWYgKE9iamVjdC5wcm90b3R5cGUuaGFzT3duUHJvcGVydHkuY2FsbChvYmosIGtleSkpIG5ld09ialtrZXldID0gb2JqW2tleV07IH0gfSBuZXdPYmpbXCJkZWZhdWx0XCJdID0gb2JqOyByZXR1cm4gbmV3T2JqOyB9IH1cblxudmFyIF8gPSBfZGVyZXFfKFwiLi5cIik7XG5cbnZhciBhY29ybiA9IF9pbnRlcm9wUmVxdWlyZVdpbGRjYXJkKF8pO1xuXG52YXIgX3N0YXRlID0gX2RlcmVxXyhcIi4vc3RhdGVcIik7XG5cbl9kZXJlcV8oXCIuL3Rva2VuaXplXCIpO1xuXG5fZGVyZXFfKFwiLi9zdGF0ZW1lbnRcIik7XG5cbl9kZXJlcV8oXCIuL2V4cHJlc3Npb25cIik7XG5cbmV4cG9ydHMuTG9vc2VQYXJzZXIgPSBfc3RhdGUuTG9vc2VQYXJzZXI7XG5cbmFjb3JuLmRlZmF1bHRPcHRpb25zLnRhYlNpemUgPSA0O1xuXG5mdW5jdGlvbiBwYXJzZV9kYW1taXQoaW5wdXQsIG9wdGlvbnMpIHtcbiAgdmFyIHAgPSBuZXcgX3N0YXRlLkxvb3NlUGFyc2VyKGlucHV0LCBvcHRpb25zKTtcbiAgcC5uZXh0KCk7XG4gIHJldHVybiBwLnBhcnNlVG9wTGV2ZWwoKTtcbn1cblxuYWNvcm4ucGFyc2VfZGFtbWl0ID0gcGFyc2VfZGFtbWl0O1xuYWNvcm4uTG9vc2VQYXJzZXIgPSBfc3RhdGUuTG9vc2VQYXJzZXI7XG5cbn0se1wiLi5cIjoxLFwiLi9leHByZXNzaW9uXCI6MixcIi4vc3RhdGVcIjo1LFwiLi9zdGF0ZW1lbnRcIjo2LFwiLi90b2tlbml6ZVwiOjd9XSw0OltmdW5jdGlvbihfZGVyZXFfLG1vZHVsZSxleHBvcnRzKXtcblwidXNlIHN0cmljdFwiO1xuXG5leHBvcnRzLl9fZXNNb2R1bGUgPSB0cnVlO1xuZXhwb3J0cy5pc0R1bW15ID0gaXNEdW1teTtcblxuZnVuY3Rpb24gaXNEdW1teShub2RlKSB7XG4gIHJldHVybiBub2RlLm5hbWUgPT0gXCLinJZcIjtcbn1cblxufSx7fV0sNTpbZnVuY3Rpb24oX2RlcmVxXyxtb2R1bGUsZXhwb3J0cyl7XG5cInVzZSBzdHJpY3RcIjtcblxuZXhwb3J0cy5fX2VzTW9kdWxlID0gdHJ1ZTtcblxuZnVuY3Rpb24gX2NsYXNzQ2FsbENoZWNrKGluc3RhbmNlLCBDb25zdHJ1Y3RvcikgeyBpZiAoIShpbnN0YW5jZSBpbnN0YW5jZW9mIENvbnN0cnVjdG9yKSkgeyB0aHJvdyBuZXcgVHlwZUVycm9yKFwiQ2Fubm90IGNhbGwgYSBjbGFzcyBhcyBhIGZ1bmN0aW9uXCIpOyB9IH1cblxudmFyIF8gPSBfZGVyZXFfKFwiLi5cIik7XG5cbnZhciBMb29zZVBhcnNlciA9IChmdW5jdGlvbiAoKSB7XG4gIGZ1bmN0aW9uIExvb3NlUGFyc2VyKGlucHV0LCBvcHRpb25zKSB7XG4gICAgX2NsYXNzQ2FsbENoZWNrKHRoaXMsIExvb3NlUGFyc2VyKTtcblxuICAgIHRoaXMudG9rcyA9IF8udG9rZW5pemVyKGlucHV0LCBvcHRpb25zKTtcbiAgICB0aGlzLm9wdGlvbnMgPSB0aGlzLnRva3Mub3B0aW9ucztcbiAgICB0aGlzLmlucHV0ID0gdGhpcy50b2tzLmlucHV0O1xuICAgIHRoaXMudG9rID0gdGhpcy5sYXN0ID0geyB0eXBlOiBfLnRva1R5cGVzLmVvZiwgc3RhcnQ6IDAsIGVuZDogMCB9O1xuICAgIGlmICh0aGlzLm9wdGlvbnMubG9jYXRpb25zKSB7XG4gICAgICB2YXIgaGVyZSA9IHRoaXMudG9rcy5jdXJQb3NpdGlvbigpO1xuICAgICAgdGhpcy50b2subG9jID0gbmV3IF8uU291cmNlTG9jYXRpb24odGhpcy50b2tzLCBoZXJlLCBoZXJlKTtcbiAgICB9XG4gICAgdGhpcy5haGVhZCA9IFtdOyAvLyBUb2tlbnMgYWhlYWRcbiAgICB0aGlzLmNvbnRleHQgPSBbXTsgLy8gSW5kZW50YXRpb24gY29udGV4dGVkXG4gICAgdGhpcy5jdXJJbmRlbnQgPSAwO1xuICAgIHRoaXMuY3VyTGluZVN0YXJ0ID0gMDtcbiAgICB0aGlzLm5leHRMaW5lU3RhcnQgPSB0aGlzLmxpbmVFbmQodGhpcy5jdXJMaW5lU3RhcnQpICsgMTtcbiAgfVxuXG4gIExvb3NlUGFyc2VyLnByb3RvdHlwZS5zdGFydE5vZGUgPSBmdW5jdGlvbiBzdGFydE5vZGUoKSB7XG4gICAgcmV0dXJuIG5ldyBfLk5vZGUodGhpcy50b2tzLCB0aGlzLnRvay5zdGFydCwgdGhpcy5vcHRpb25zLmxvY2F0aW9ucyA/IHRoaXMudG9rLmxvYy5zdGFydCA6IG51bGwpO1xuICB9O1xuXG4gIExvb3NlUGFyc2VyLnByb3RvdHlwZS5zdG9yZUN1cnJlbnRQb3MgPSBmdW5jdGlvbiBzdG9yZUN1cnJlbnRQb3MoKSB7XG4gICAgcmV0dXJuIHRoaXMub3B0aW9ucy5sb2NhdGlvbnMgPyBbdGhpcy50b2suc3RhcnQsIHRoaXMudG9rLmxvYy5zdGFydF0gOiB0aGlzLnRvay5zdGFydDtcbiAgfTtcblxuICBMb29zZVBhcnNlci5wcm90b3R5cGUuc3RhcnROb2RlQXQgPSBmdW5jdGlvbiBzdGFydE5vZGVBdChwb3MpIHtcbiAgICBpZiAodGhpcy5vcHRpb25zLmxvY2F0aW9ucykge1xuICAgICAgcmV0dXJuIG5ldyBfLk5vZGUodGhpcy50b2tzLCBwb3NbMF0sIHBvc1sxXSk7XG4gICAgfSBlbHNlIHtcbiAgICAgIHJldHVybiBuZXcgXy5Ob2RlKHRoaXMudG9rcywgcG9zKTtcbiAgICB9XG4gIH07XG5cbiAgTG9vc2VQYXJzZXIucHJvdG90eXBlLmZpbmlzaE5vZGUgPSBmdW5jdGlvbiBmaW5pc2hOb2RlKG5vZGUsIHR5cGUpIHtcbiAgICBub2RlLnR5cGUgPSB0eXBlO1xuICAgIG5vZGUuZW5kID0gdGhpcy5sYXN0LmVuZDtcbiAgICBpZiAodGhpcy5vcHRpb25zLmxvY2F0aW9ucykgbm9kZS5sb2MuZW5kID0gdGhpcy5sYXN0LmxvYy5lbmQ7XG4gICAgaWYgKHRoaXMub3B0aW9ucy5yYW5nZXMpIG5vZGUucmFuZ2VbMV0gPSB0aGlzLmxhc3QuZW5kO1xuICAgIHJldHVybiBub2RlO1xuICB9O1xuXG4gIExvb3NlUGFyc2VyLnByb3RvdHlwZS5kdW1teUlkZW50ID0gZnVuY3Rpb24gZHVtbXlJZGVudCgpIHtcbiAgICB2YXIgZHVtbXkgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICAgIGR1bW15Lm5hbWUgPSBcIuKcllwiO1xuICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUoZHVtbXksIFwiSWRlbnRpZmllclwiKTtcbiAgfTtcblxuICBMb29zZVBhcnNlci5wcm90b3R5cGUuZHVtbXlTdHJpbmcgPSBmdW5jdGlvbiBkdW1teVN0cmluZygpIHtcbiAgICB2YXIgZHVtbXkgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICAgIGR1bW15LnZhbHVlID0gZHVtbXkucmF3ID0gXCLinJZcIjtcbiAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKGR1bW15LCBcIkxpdGVyYWxcIik7XG4gIH07XG5cbiAgTG9vc2VQYXJzZXIucHJvdG90eXBlLmVhdCA9IGZ1bmN0aW9uIGVhdCh0eXBlKSB7XG4gICAgaWYgKHRoaXMudG9rLnR5cGUgPT09IHR5cGUpIHtcbiAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgcmV0dXJuIHRydWU7XG4gICAgfSBlbHNlIHtcbiAgICAgIHJldHVybiBmYWxzZTtcbiAgICB9XG4gIH07XG5cbiAgTG9vc2VQYXJzZXIucHJvdG90eXBlLmlzQ29udGV4dHVhbCA9IGZ1bmN0aW9uIGlzQ29udGV4dHVhbChuYW1lKSB7XG4gICAgcmV0dXJuIHRoaXMudG9rLnR5cGUgPT09IF8udG9rVHlwZXMubmFtZSAmJiB0aGlzLnRvay52YWx1ZSA9PT0gbmFtZTtcbiAgfTtcblxuICBMb29zZVBhcnNlci5wcm90b3R5cGUuZWF0Q29udGV4dHVhbCA9IGZ1bmN0aW9uIGVhdENvbnRleHR1YWwobmFtZSkge1xuICAgIHJldHVybiB0aGlzLnRvay52YWx1ZSA9PT0gbmFtZSAmJiB0aGlzLmVhdChfLnRva1R5cGVzLm5hbWUpO1xuICB9O1xuXG4gIExvb3NlUGFyc2VyLnByb3RvdHlwZS5jYW5JbnNlcnRTZW1pY29sb24gPSBmdW5jdGlvbiBjYW5JbnNlcnRTZW1pY29sb24oKSB7XG4gICAgcmV0dXJuIHRoaXMudG9rLnR5cGUgPT09IF8udG9rVHlwZXMuZW9mIHx8IHRoaXMudG9rLnR5cGUgPT09IF8udG9rVHlwZXMuYnJhY2VSIHx8IF8ubGluZUJyZWFrLnRlc3QodGhpcy5pbnB1dC5zbGljZSh0aGlzLmxhc3QuZW5kLCB0aGlzLnRvay5zdGFydCkpO1xuICB9O1xuXG4gIExvb3NlUGFyc2VyLnByb3RvdHlwZS5zZW1pY29sb24gPSBmdW5jdGlvbiBzZW1pY29sb24oKSB7XG4gICAgcmV0dXJuIHRoaXMuZWF0KF8udG9rVHlwZXMuc2VtaSk7XG4gIH07XG5cbiAgTG9vc2VQYXJzZXIucHJvdG90eXBlLmV4cGVjdCA9IGZ1bmN0aW9uIGV4cGVjdCh0eXBlKSB7XG4gICAgaWYgKHRoaXMuZWF0KHR5cGUpKSByZXR1cm4gdHJ1ZTtcbiAgICBmb3IgKHZhciBpID0gMTsgaSA8PSAyOyBpKyspIHtcbiAgICAgIGlmICh0aGlzLmxvb2tBaGVhZChpKS50eXBlID09IHR5cGUpIHtcbiAgICAgICAgZm9yICh2YXIgaiA9IDA7IGogPCBpOyBqKyspIHtcbiAgICAgICAgICB0aGlzLm5leHQoKTtcbiAgICAgICAgfXJldHVybiB0cnVlO1xuICAgICAgfVxuICAgIH1cbiAgfTtcblxuICBMb29zZVBhcnNlci5wcm90b3R5cGUucHVzaEN4ID0gZnVuY3Rpb24gcHVzaEN4KCkge1xuICAgIHRoaXMuY29udGV4dC5wdXNoKHRoaXMuY3VySW5kZW50KTtcbiAgfTtcblxuICBMb29zZVBhcnNlci5wcm90b3R5cGUucG9wQ3ggPSBmdW5jdGlvbiBwb3BDeCgpIHtcbiAgICB0aGlzLmN1ckluZGVudCA9IHRoaXMuY29udGV4dC5wb3AoKTtcbiAgfTtcblxuICBMb29zZVBhcnNlci5wcm90b3R5cGUubGluZUVuZCA9IGZ1bmN0aW9uIGxpbmVFbmQocG9zKSB7XG4gICAgd2hpbGUgKHBvcyA8IHRoaXMuaW5wdXQubGVuZ3RoICYmICFfLmlzTmV3TGluZSh0aGlzLmlucHV0LmNoYXJDb2RlQXQocG9zKSkpICsrcG9zO1xuICAgIHJldHVybiBwb3M7XG4gIH07XG5cbiAgTG9vc2VQYXJzZXIucHJvdG90eXBlLmluZGVudGF0aW9uQWZ0ZXIgPSBmdW5jdGlvbiBpbmRlbnRhdGlvbkFmdGVyKHBvcykge1xuICAgIGZvciAodmFyIGNvdW50ID0gMDs7ICsrcG9zKSB7XG4gICAgICB2YXIgY2ggPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQocG9zKTtcbiAgICAgIGlmIChjaCA9PT0gMzIpICsrY291bnQ7ZWxzZSBpZiAoY2ggPT09IDkpIGNvdW50ICs9IHRoaXMub3B0aW9ucy50YWJTaXplO2Vsc2UgcmV0dXJuIGNvdW50O1xuICAgIH1cbiAgfTtcblxuICBMb29zZVBhcnNlci5wcm90b3R5cGUuY2xvc2VzID0gZnVuY3Rpb24gY2xvc2VzKGNsb3NlVG9rLCBpbmRlbnQsIGxpbmUsIGJsb2NrSGV1cmlzdGljKSB7XG4gICAgaWYgKHRoaXMudG9rLnR5cGUgPT09IGNsb3NlVG9rIHx8IHRoaXMudG9rLnR5cGUgPT09IF8udG9rVHlwZXMuZW9mKSByZXR1cm4gdHJ1ZTtcbiAgICByZXR1cm4gbGluZSAhPSB0aGlzLmN1ckxpbmVTdGFydCAmJiB0aGlzLmN1ckluZGVudCA8IGluZGVudCAmJiB0aGlzLnRva2VuU3RhcnRzTGluZSgpICYmICghYmxvY2tIZXVyaXN0aWMgfHwgdGhpcy5uZXh0TGluZVN0YXJ0ID49IHRoaXMuaW5wdXQubGVuZ3RoIHx8IHRoaXMuaW5kZW50YXRpb25BZnRlcih0aGlzLm5leHRMaW5lU3RhcnQpIDwgaW5kZW50KTtcbiAgfTtcblxuICBMb29zZVBhcnNlci5wcm90b3R5cGUudG9rZW5TdGFydHNMaW5lID0gZnVuY3Rpb24gdG9rZW5TdGFydHNMaW5lKCkge1xuICAgIGZvciAodmFyIHAgPSB0aGlzLnRvay5zdGFydCAtIDE7IHAgPj0gdGhpcy5jdXJMaW5lU3RhcnQ7IC0tcCkge1xuICAgICAgdmFyIGNoID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHApO1xuICAgICAgaWYgKGNoICE9PSA5ICYmIGNoICE9PSAzMikgcmV0dXJuIGZhbHNlO1xuICAgIH1cbiAgICByZXR1cm4gdHJ1ZTtcbiAgfTtcblxuICByZXR1cm4gTG9vc2VQYXJzZXI7XG59KSgpO1xuXG5leHBvcnRzLkxvb3NlUGFyc2VyID0gTG9vc2VQYXJzZXI7XG5cbn0se1wiLi5cIjoxfV0sNjpbZnVuY3Rpb24oX2RlcmVxXyxtb2R1bGUsZXhwb3J0cyl7XG5cInVzZSBzdHJpY3RcIjtcblxudmFyIF9zdGF0ZSA9IF9kZXJlcV8oXCIuL3N0YXRlXCIpO1xuXG52YXIgX3BhcnNldXRpbCA9IF9kZXJlcV8oXCIuL3BhcnNldXRpbFwiKTtcblxudmFyIF8gPSBfZGVyZXFfKFwiLi5cIik7XG5cbnZhciBscCA9IF9zdGF0ZS5Mb29zZVBhcnNlci5wcm90b3R5cGU7XG5cbmxwLnBhcnNlVG9wTGV2ZWwgPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGVBdCh0aGlzLm9wdGlvbnMubG9jYXRpb25zID8gWzAsIF8uZ2V0TGluZUluZm8odGhpcy5pbnB1dCwgMCldIDogMCk7XG4gIG5vZGUuYm9keSA9IFtdO1xuICB3aGlsZSAodGhpcy50b2sudHlwZSAhPT0gXy50b2tUeXBlcy5lb2YpIG5vZGUuYm9keS5wdXNoKHRoaXMucGFyc2VTdGF0ZW1lbnQoKSk7XG4gIHRoaXMubGFzdCA9IHRoaXMudG9rO1xuICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYpIHtcbiAgICBub2RlLnNvdXJjZVR5cGUgPSB0aGlzLm9wdGlvbnMuc291cmNlVHlwZTtcbiAgfVxuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiUHJvZ3JhbVwiKTtcbn07XG5cbmxwLnBhcnNlU3RhdGVtZW50ID0gZnVuY3Rpb24gKCkge1xuICB2YXIgc3RhcnR0eXBlID0gdGhpcy50b2sudHlwZSxcbiAgICAgIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuXG4gIHN3aXRjaCAoc3RhcnR0eXBlKSB7XG4gICAgY2FzZSBfLnRva1R5cGVzLl9icmVhazpjYXNlIF8udG9rVHlwZXMuX2NvbnRpbnVlOlxuICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICB2YXIgaXNCcmVhayA9IHN0YXJ0dHlwZSA9PT0gXy50b2tUeXBlcy5fYnJlYWs7XG4gICAgICBpZiAodGhpcy5zZW1pY29sb24oKSB8fCB0aGlzLmNhbkluc2VydFNlbWljb2xvbigpKSB7XG4gICAgICAgIG5vZGUubGFiZWwgPSBudWxsO1xuICAgICAgfSBlbHNlIHtcbiAgICAgICAgbm9kZS5sYWJlbCA9IHRoaXMudG9rLnR5cGUgPT09IF8udG9rVHlwZXMubmFtZSA/IHRoaXMucGFyc2VJZGVudCgpIDogbnVsbDtcbiAgICAgICAgdGhpcy5zZW1pY29sb24oKTtcbiAgICAgIH1cbiAgICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgaXNCcmVhayA/IFwiQnJlYWtTdGF0ZW1lbnRcIiA6IFwiQ29udGludWVTdGF0ZW1lbnRcIik7XG5cbiAgICBjYXNlIF8udG9rVHlwZXMuX2RlYnVnZ2VyOlxuICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICB0aGlzLnNlbWljb2xvbigpO1xuICAgICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkRlYnVnZ2VyU3RhdGVtZW50XCIpO1xuXG4gICAgY2FzZSBfLnRva1R5cGVzLl9kbzpcbiAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgbm9kZS5ib2R5ID0gdGhpcy5wYXJzZVN0YXRlbWVudCgpO1xuICAgICAgbm9kZS50ZXN0ID0gdGhpcy5lYXQoXy50b2tUeXBlcy5fd2hpbGUpID8gdGhpcy5wYXJzZVBhcmVuRXhwcmVzc2lvbigpIDogdGhpcy5kdW1teUlkZW50KCk7XG4gICAgICB0aGlzLnNlbWljb2xvbigpO1xuICAgICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkRvV2hpbGVTdGF0ZW1lbnRcIik7XG5cbiAgICBjYXNlIF8udG9rVHlwZXMuX2ZvcjpcbiAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgdGhpcy5wdXNoQ3goKTtcbiAgICAgIHRoaXMuZXhwZWN0KF8udG9rVHlwZXMucGFyZW5MKTtcbiAgICAgIGlmICh0aGlzLnRvay50eXBlID09PSBfLnRva1R5cGVzLnNlbWkpIHJldHVybiB0aGlzLnBhcnNlRm9yKG5vZGUsIG51bGwpO1xuICAgICAgaWYgKHRoaXMudG9rLnR5cGUgPT09IF8udG9rVHlwZXMuX3ZhciB8fCB0aGlzLnRvay50eXBlID09PSBfLnRva1R5cGVzLl9sZXQgfHwgdGhpcy50b2sudHlwZSA9PT0gXy50b2tUeXBlcy5fY29uc3QpIHtcbiAgICAgICAgdmFyIF9pbml0ID0gdGhpcy5wYXJzZVZhcih0cnVlKTtcbiAgICAgICAgaWYgKF9pbml0LmRlY2xhcmF0aW9ucy5sZW5ndGggPT09IDEgJiYgKHRoaXMudG9rLnR5cGUgPT09IF8udG9rVHlwZXMuX2luIHx8IHRoaXMuaXNDb250ZXh0dWFsKFwib2ZcIikpKSB7XG4gICAgICAgICAgcmV0dXJuIHRoaXMucGFyc2VGb3JJbihub2RlLCBfaW5pdCk7XG4gICAgICAgIH1cbiAgICAgICAgcmV0dXJuIHRoaXMucGFyc2VGb3Iobm9kZSwgX2luaXQpO1xuICAgICAgfVxuICAgICAgdmFyIGluaXQgPSB0aGlzLnBhcnNlRXhwcmVzc2lvbih0cnVlKTtcbiAgICAgIGlmICh0aGlzLnRvay50eXBlID09PSBfLnRva1R5cGVzLl9pbiB8fCB0aGlzLmlzQ29udGV4dHVhbChcIm9mXCIpKSByZXR1cm4gdGhpcy5wYXJzZUZvckluKG5vZGUsIHRoaXMudG9Bc3NpZ25hYmxlKGluaXQpKTtcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlRm9yKG5vZGUsIGluaXQpO1xuXG4gICAgY2FzZSBfLnRva1R5cGVzLl9mdW5jdGlvbjpcbiAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgcmV0dXJuIHRoaXMucGFyc2VGdW5jdGlvbihub2RlLCB0cnVlKTtcblxuICAgIGNhc2UgXy50b2tUeXBlcy5faWY6XG4gICAgICB0aGlzLm5leHQoKTtcbiAgICAgIG5vZGUudGVzdCA9IHRoaXMucGFyc2VQYXJlbkV4cHJlc3Npb24oKTtcbiAgICAgIG5vZGUuY29uc2VxdWVudCA9IHRoaXMucGFyc2VTdGF0ZW1lbnQoKTtcbiAgICAgIG5vZGUuYWx0ZXJuYXRlID0gdGhpcy5lYXQoXy50b2tUeXBlcy5fZWxzZSkgPyB0aGlzLnBhcnNlU3RhdGVtZW50KCkgOiBudWxsO1xuICAgICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIklmU3RhdGVtZW50XCIpO1xuXG4gICAgY2FzZSBfLnRva1R5cGVzLl9yZXR1cm46XG4gICAgICB0aGlzLm5leHQoKTtcbiAgICAgIGlmICh0aGlzLmVhdChfLnRva1R5cGVzLnNlbWkpIHx8IHRoaXMuY2FuSW5zZXJ0U2VtaWNvbG9uKCkpIG5vZGUuYXJndW1lbnQgPSBudWxsO2Vsc2Uge1xuICAgICAgICBub2RlLmFyZ3VtZW50ID0gdGhpcy5wYXJzZUV4cHJlc3Npb24oKTt0aGlzLnNlbWljb2xvbigpO1xuICAgICAgfVxuICAgICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIlJldHVyblN0YXRlbWVudFwiKTtcblxuICAgIGNhc2UgXy50b2tUeXBlcy5fc3dpdGNoOlxuICAgICAgdmFyIGJsb2NrSW5kZW50ID0gdGhpcy5jdXJJbmRlbnQsXG4gICAgICAgICAgbGluZSA9IHRoaXMuY3VyTGluZVN0YXJ0O1xuICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICBub2RlLmRpc2NyaW1pbmFudCA9IHRoaXMucGFyc2VQYXJlbkV4cHJlc3Npb24oKTtcbiAgICAgIG5vZGUuY2FzZXMgPSBbXTtcbiAgICAgIHRoaXMucHVzaEN4KCk7XG4gICAgICB0aGlzLmV4cGVjdChfLnRva1R5cGVzLmJyYWNlTCk7XG5cbiAgICAgIHZhciBjdXIgPSB1bmRlZmluZWQ7XG4gICAgICB3aGlsZSAoIXRoaXMuY2xvc2VzKF8udG9rVHlwZXMuYnJhY2VSLCBibG9ja0luZGVudCwgbGluZSwgdHJ1ZSkpIHtcbiAgICAgICAgaWYgKHRoaXMudG9rLnR5cGUgPT09IF8udG9rVHlwZXMuX2Nhc2UgfHwgdGhpcy50b2sudHlwZSA9PT0gXy50b2tUeXBlcy5fZGVmYXVsdCkge1xuICAgICAgICAgIHZhciBpc0Nhc2UgPSB0aGlzLnRvay50eXBlID09PSBfLnRva1R5cGVzLl9jYXNlO1xuICAgICAgICAgIGlmIChjdXIpIHRoaXMuZmluaXNoTm9kZShjdXIsIFwiU3dpdGNoQ2FzZVwiKTtcbiAgICAgICAgICBub2RlLmNhc2VzLnB1c2goY3VyID0gdGhpcy5zdGFydE5vZGUoKSk7XG4gICAgICAgICAgY3VyLmNvbnNlcXVlbnQgPSBbXTtcbiAgICAgICAgICB0aGlzLm5leHQoKTtcbiAgICAgICAgICBpZiAoaXNDYXNlKSBjdXIudGVzdCA9IHRoaXMucGFyc2VFeHByZXNzaW9uKCk7ZWxzZSBjdXIudGVzdCA9IG51bGw7XG4gICAgICAgICAgdGhpcy5leHBlY3QoXy50b2tUeXBlcy5jb2xvbik7XG4gICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgaWYgKCFjdXIpIHtcbiAgICAgICAgICAgIG5vZGUuY2FzZXMucHVzaChjdXIgPSB0aGlzLnN0YXJ0Tm9kZSgpKTtcbiAgICAgICAgICAgIGN1ci5jb25zZXF1ZW50ID0gW107XG4gICAgICAgICAgICBjdXIudGVzdCA9IG51bGw7XG4gICAgICAgICAgfVxuICAgICAgICAgIGN1ci5jb25zZXF1ZW50LnB1c2godGhpcy5wYXJzZVN0YXRlbWVudCgpKTtcbiAgICAgICAgfVxuICAgICAgfVxuICAgICAgaWYgKGN1cikgdGhpcy5maW5pc2hOb2RlKGN1ciwgXCJTd2l0Y2hDYXNlXCIpO1xuICAgICAgdGhpcy5wb3BDeCgpO1xuICAgICAgdGhpcy5lYXQoXy50b2tUeXBlcy5icmFjZVIpO1xuICAgICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIlN3aXRjaFN0YXRlbWVudFwiKTtcblxuICAgIGNhc2UgXy50b2tUeXBlcy5fdGhyb3c6XG4gICAgICB0aGlzLm5leHQoKTtcbiAgICAgIG5vZGUuYXJndW1lbnQgPSB0aGlzLnBhcnNlRXhwcmVzc2lvbigpO1xuICAgICAgdGhpcy5zZW1pY29sb24oKTtcbiAgICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJUaHJvd1N0YXRlbWVudFwiKTtcblxuICAgIGNhc2UgXy50b2tUeXBlcy5fdHJ5OlxuICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICBub2RlLmJsb2NrID0gdGhpcy5wYXJzZUJsb2NrKCk7XG4gICAgICBub2RlLmhhbmRsZXIgPSBudWxsO1xuICAgICAgaWYgKHRoaXMudG9rLnR5cGUgPT09IF8udG9rVHlwZXMuX2NhdGNoKSB7XG4gICAgICAgIHZhciBjbGF1c2UgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICAgICAgICB0aGlzLm5leHQoKTtcbiAgICAgICAgdGhpcy5leHBlY3QoXy50b2tUeXBlcy5wYXJlbkwpO1xuICAgICAgICBjbGF1c2UucGFyYW0gPSB0aGlzLnRvQXNzaWduYWJsZSh0aGlzLnBhcnNlRXhwckF0b20oKSwgdHJ1ZSk7XG4gICAgICAgIHRoaXMuZXhwZWN0KF8udG9rVHlwZXMucGFyZW5SKTtcbiAgICAgICAgY2xhdXNlLmd1YXJkID0gbnVsbDtcbiAgICAgICAgY2xhdXNlLmJvZHkgPSB0aGlzLnBhcnNlQmxvY2soKTtcbiAgICAgICAgbm9kZS5oYW5kbGVyID0gdGhpcy5maW5pc2hOb2RlKGNsYXVzZSwgXCJDYXRjaENsYXVzZVwiKTtcbiAgICAgIH1cbiAgICAgIG5vZGUuZmluYWxpemVyID0gdGhpcy5lYXQoXy50b2tUeXBlcy5fZmluYWxseSkgPyB0aGlzLnBhcnNlQmxvY2soKSA6IG51bGw7XG4gICAgICBpZiAoIW5vZGUuaGFuZGxlciAmJiAhbm9kZS5maW5hbGl6ZXIpIHJldHVybiBub2RlLmJsb2NrO1xuICAgICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIlRyeVN0YXRlbWVudFwiKTtcblxuICAgIGNhc2UgXy50b2tUeXBlcy5fdmFyOlxuICAgIGNhc2UgXy50b2tUeXBlcy5fbGV0OlxuICAgIGNhc2UgXy50b2tUeXBlcy5fY29uc3Q6XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZVZhcigpO1xuXG4gICAgY2FzZSBfLnRva1R5cGVzLl93aGlsZTpcbiAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgbm9kZS50ZXN0ID0gdGhpcy5wYXJzZVBhcmVuRXhwcmVzc2lvbigpO1xuICAgICAgbm9kZS5ib2R5ID0gdGhpcy5wYXJzZVN0YXRlbWVudCgpO1xuICAgICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIldoaWxlU3RhdGVtZW50XCIpO1xuXG4gICAgY2FzZSBfLnRva1R5cGVzLl93aXRoOlxuICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICBub2RlLm9iamVjdCA9IHRoaXMucGFyc2VQYXJlbkV4cHJlc3Npb24oKTtcbiAgICAgIG5vZGUuYm9keSA9IHRoaXMucGFyc2VTdGF0ZW1lbnQoKTtcbiAgICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJXaXRoU3RhdGVtZW50XCIpO1xuXG4gICAgY2FzZSBfLnRva1R5cGVzLmJyYWNlTDpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlQmxvY2soKTtcblxuICAgIGNhc2UgXy50b2tUeXBlcy5zZW1pOlxuICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiRW1wdHlTdGF0ZW1lbnRcIik7XG5cbiAgICBjYXNlIF8udG9rVHlwZXMuX2NsYXNzOlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VDbGFzcyh0cnVlKTtcblxuICAgIGNhc2UgXy50b2tUeXBlcy5faW1wb3J0OlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VJbXBvcnQoKTtcblxuICAgIGNhc2UgXy50b2tUeXBlcy5fZXhwb3J0OlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VFeHBvcnQoKTtcblxuICAgIGRlZmF1bHQ6XG4gICAgICB2YXIgZXhwciA9IHRoaXMucGFyc2VFeHByZXNzaW9uKCk7XG4gICAgICBpZiAoX3BhcnNldXRpbC5pc0R1bW15KGV4cHIpKSB7XG4gICAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgICBpZiAodGhpcy50b2sudHlwZSA9PT0gXy50b2tUeXBlcy5lb2YpIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJFbXB0eVN0YXRlbWVudFwiKTtcbiAgICAgICAgcmV0dXJuIHRoaXMucGFyc2VTdGF0ZW1lbnQoKTtcbiAgICAgIH0gZWxzZSBpZiAoc3RhcnR0eXBlID09PSBfLnRva1R5cGVzLm5hbWUgJiYgZXhwci50eXBlID09PSBcIklkZW50aWZpZXJcIiAmJiB0aGlzLmVhdChfLnRva1R5cGVzLmNvbG9uKSkge1xuICAgICAgICBub2RlLmJvZHkgPSB0aGlzLnBhcnNlU3RhdGVtZW50KCk7XG4gICAgICAgIG5vZGUubGFiZWwgPSBleHByO1xuICAgICAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiTGFiZWxlZFN0YXRlbWVudFwiKTtcbiAgICAgIH0gZWxzZSB7XG4gICAgICAgIG5vZGUuZXhwcmVzc2lvbiA9IGV4cHI7XG4gICAgICAgIHRoaXMuc2VtaWNvbG9uKCk7XG4gICAgICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJFeHByZXNzaW9uU3RhdGVtZW50XCIpO1xuICAgICAgfVxuICB9XG59O1xuXG5scC5wYXJzZUJsb2NrID0gZnVuY3Rpb24gKCkge1xuICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gIHRoaXMucHVzaEN4KCk7XG4gIHRoaXMuZXhwZWN0KF8udG9rVHlwZXMuYnJhY2VMKTtcbiAgdmFyIGJsb2NrSW5kZW50ID0gdGhpcy5jdXJJbmRlbnQsXG4gICAgICBsaW5lID0gdGhpcy5jdXJMaW5lU3RhcnQ7XG4gIG5vZGUuYm9keSA9IFtdO1xuICB3aGlsZSAoIXRoaXMuY2xvc2VzKF8udG9rVHlwZXMuYnJhY2VSLCBibG9ja0luZGVudCwgbGluZSwgdHJ1ZSkpIG5vZGUuYm9keS5wdXNoKHRoaXMucGFyc2VTdGF0ZW1lbnQoKSk7XG4gIHRoaXMucG9wQ3goKTtcbiAgdGhpcy5lYXQoXy50b2tUeXBlcy5icmFjZVIpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiQmxvY2tTdGF0ZW1lbnRcIik7XG59O1xuXG5scC5wYXJzZUZvciA9IGZ1bmN0aW9uIChub2RlLCBpbml0KSB7XG4gIG5vZGUuaW5pdCA9IGluaXQ7XG4gIG5vZGUudGVzdCA9IG5vZGUudXBkYXRlID0gbnVsbDtcbiAgaWYgKHRoaXMuZWF0KF8udG9rVHlwZXMuc2VtaSkgJiYgdGhpcy50b2sudHlwZSAhPT0gXy50b2tUeXBlcy5zZW1pKSBub2RlLnRlc3QgPSB0aGlzLnBhcnNlRXhwcmVzc2lvbigpO1xuICBpZiAodGhpcy5lYXQoXy50b2tUeXBlcy5zZW1pKSAmJiB0aGlzLnRvay50eXBlICE9PSBfLnRva1R5cGVzLnBhcmVuUikgbm9kZS51cGRhdGUgPSB0aGlzLnBhcnNlRXhwcmVzc2lvbigpO1xuICB0aGlzLnBvcEN4KCk7XG4gIHRoaXMuZXhwZWN0KF8udG9rVHlwZXMucGFyZW5SKTtcbiAgbm9kZS5ib2R5ID0gdGhpcy5wYXJzZVN0YXRlbWVudCgpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiRm9yU3RhdGVtZW50XCIpO1xufTtcblxubHAucGFyc2VGb3JJbiA9IGZ1bmN0aW9uIChub2RlLCBpbml0KSB7XG4gIHZhciB0eXBlID0gdGhpcy50b2sudHlwZSA9PT0gXy50b2tUeXBlcy5faW4gPyBcIkZvckluU3RhdGVtZW50XCIgOiBcIkZvck9mU3RhdGVtZW50XCI7XG4gIHRoaXMubmV4dCgpO1xuICBub2RlLmxlZnQgPSBpbml0O1xuICBub2RlLnJpZ2h0ID0gdGhpcy5wYXJzZUV4cHJlc3Npb24oKTtcbiAgdGhpcy5wb3BDeCgpO1xuICB0aGlzLmV4cGVjdChfLnRva1R5cGVzLnBhcmVuUik7XG4gIG5vZGUuYm9keSA9IHRoaXMucGFyc2VTdGF0ZW1lbnQoKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCB0eXBlKTtcbn07XG5cbmxwLnBhcnNlVmFyID0gZnVuY3Rpb24gKG5vSW4pIHtcbiAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICBub2RlLmtpbmQgPSB0aGlzLnRvay50eXBlLmtleXdvcmQ7XG4gIHRoaXMubmV4dCgpO1xuICBub2RlLmRlY2xhcmF0aW9ucyA9IFtdO1xuICBkbyB7XG4gICAgdmFyIGRlY2wgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICAgIGRlY2wuaWQgPSB0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNiA/IHRoaXMudG9Bc3NpZ25hYmxlKHRoaXMucGFyc2VFeHByQXRvbSgpLCB0cnVlKSA6IHRoaXMucGFyc2VJZGVudCgpO1xuICAgIGRlY2wuaW5pdCA9IHRoaXMuZWF0KF8udG9rVHlwZXMuZXEpID8gdGhpcy5wYXJzZU1heWJlQXNzaWduKG5vSW4pIDogbnVsbDtcbiAgICBub2RlLmRlY2xhcmF0aW9ucy5wdXNoKHRoaXMuZmluaXNoTm9kZShkZWNsLCBcIlZhcmlhYmxlRGVjbGFyYXRvclwiKSk7XG4gIH0gd2hpbGUgKHRoaXMuZWF0KF8udG9rVHlwZXMuY29tbWEpKTtcbiAgaWYgKCFub2RlLmRlY2xhcmF0aW9ucy5sZW5ndGgpIHtcbiAgICB2YXIgZGVjbCA9IHRoaXMuc3RhcnROb2RlKCk7XG4gICAgZGVjbC5pZCA9IHRoaXMuZHVtbXlJZGVudCgpO1xuICAgIG5vZGUuZGVjbGFyYXRpb25zLnB1c2godGhpcy5maW5pc2hOb2RlKGRlY2wsIFwiVmFyaWFibGVEZWNsYXJhdG9yXCIpKTtcbiAgfVxuICBpZiAoIW5vSW4pIHRoaXMuc2VtaWNvbG9uKCk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJWYXJpYWJsZURlY2xhcmF0aW9uXCIpO1xufTtcblxubHAucGFyc2VDbGFzcyA9IGZ1bmN0aW9uIChpc1N0YXRlbWVudCkge1xuICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gIHRoaXMubmV4dCgpO1xuICBpZiAodGhpcy50b2sudHlwZSA9PT0gXy50b2tUeXBlcy5uYW1lKSBub2RlLmlkID0gdGhpcy5wYXJzZUlkZW50KCk7ZWxzZSBpZiAoaXNTdGF0ZW1lbnQpIG5vZGUuaWQgPSB0aGlzLmR1bW15SWRlbnQoKTtlbHNlIG5vZGUuaWQgPSBudWxsO1xuICBub2RlLnN1cGVyQ2xhc3MgPSB0aGlzLmVhdChfLnRva1R5cGVzLl9leHRlbmRzKSA/IHRoaXMucGFyc2VFeHByZXNzaW9uKCkgOiBudWxsO1xuICBub2RlLmJvZHkgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICBub2RlLmJvZHkuYm9keSA9IFtdO1xuICB0aGlzLnB1c2hDeCgpO1xuICB2YXIgaW5kZW50ID0gdGhpcy5jdXJJbmRlbnQgKyAxLFxuICAgICAgbGluZSA9IHRoaXMuY3VyTGluZVN0YXJ0O1xuICB0aGlzLmVhdChfLnRva1R5cGVzLmJyYWNlTCk7XG4gIGlmICh0aGlzLmN1ckluZGVudCArIDEgPCBpbmRlbnQpIHtcbiAgICBpbmRlbnQgPSB0aGlzLmN1ckluZGVudDtsaW5lID0gdGhpcy5jdXJMaW5lU3RhcnQ7XG4gIH1cbiAgd2hpbGUgKCF0aGlzLmNsb3NlcyhfLnRva1R5cGVzLmJyYWNlUiwgaW5kZW50LCBsaW5lKSkge1xuICAgIGlmICh0aGlzLnNlbWljb2xvbigpKSBjb250aW51ZTtcbiAgICB2YXIgbWV0aG9kID0gdGhpcy5zdGFydE5vZGUoKSxcbiAgICAgICAgaXNHZW5lcmF0b3IgPSB1bmRlZmluZWQ7XG4gICAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KSB7XG4gICAgICBtZXRob2RbXCJzdGF0aWNcIl0gPSBmYWxzZTtcbiAgICAgIGlzR2VuZXJhdG9yID0gdGhpcy5lYXQoXy50b2tUeXBlcy5zdGFyKTtcbiAgICB9XG4gICAgdGhpcy5wYXJzZVByb3BlcnR5TmFtZShtZXRob2QpO1xuICAgIGlmIChfcGFyc2V1dGlsLmlzRHVtbXkobWV0aG9kLmtleSkpIHtcbiAgICAgIGlmIChfcGFyc2V1dGlsLmlzRHVtbXkodGhpcy5wYXJzZU1heWJlQXNzaWduKCkpKSB0aGlzLm5leHQoKTt0aGlzLmVhdChfLnRva1R5cGVzLmNvbW1hKTtjb250aW51ZTtcbiAgICB9XG4gICAgaWYgKG1ldGhvZC5rZXkudHlwZSA9PT0gXCJJZGVudGlmaWVyXCIgJiYgIW1ldGhvZC5jb21wdXRlZCAmJiBtZXRob2Qua2V5Lm5hbWUgPT09IFwic3RhdGljXCIgJiYgKHRoaXMudG9rLnR5cGUgIT0gXy50b2tUeXBlcy5wYXJlbkwgJiYgdGhpcy50b2sudHlwZSAhPSBfLnRva1R5cGVzLmJyYWNlTCkpIHtcbiAgICAgIG1ldGhvZFtcInN0YXRpY1wiXSA9IHRydWU7XG4gICAgICBpc0dlbmVyYXRvciA9IHRoaXMuZWF0KF8udG9rVHlwZXMuc3Rhcik7XG4gICAgICB0aGlzLnBhcnNlUHJvcGVydHlOYW1lKG1ldGhvZCk7XG4gICAgfSBlbHNlIHtcbiAgICAgIG1ldGhvZFtcInN0YXRpY1wiXSA9IGZhbHNlO1xuICAgIH1cbiAgICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDUgJiYgbWV0aG9kLmtleS50eXBlID09PSBcIklkZW50aWZpZXJcIiAmJiAhbWV0aG9kLmNvbXB1dGVkICYmIChtZXRob2Qua2V5Lm5hbWUgPT09IFwiZ2V0XCIgfHwgbWV0aG9kLmtleS5uYW1lID09PSBcInNldFwiKSAmJiB0aGlzLnRvay50eXBlICE9PSBfLnRva1R5cGVzLnBhcmVuTCAmJiB0aGlzLnRvay50eXBlICE9PSBfLnRva1R5cGVzLmJyYWNlTCkge1xuICAgICAgbWV0aG9kLmtpbmQgPSBtZXRob2Qua2V5Lm5hbWU7XG4gICAgICB0aGlzLnBhcnNlUHJvcGVydHlOYW1lKG1ldGhvZCk7XG4gICAgICBtZXRob2QudmFsdWUgPSB0aGlzLnBhcnNlTWV0aG9kKGZhbHNlKTtcbiAgICB9IGVsc2Uge1xuICAgICAgaWYgKCFtZXRob2QuY29tcHV0ZWQgJiYgIW1ldGhvZFtcInN0YXRpY1wiXSAmJiAhaXNHZW5lcmF0b3IgJiYgKG1ldGhvZC5rZXkudHlwZSA9PT0gXCJJZGVudGlmaWVyXCIgJiYgbWV0aG9kLmtleS5uYW1lID09PSBcImNvbnN0cnVjdG9yXCIgfHwgbWV0aG9kLmtleS50eXBlID09PSBcIkxpdGVyYWxcIiAmJiBtZXRob2Qua2V5LnZhbHVlID09PSBcImNvbnN0cnVjdG9yXCIpKSB7XG4gICAgICAgIG1ldGhvZC5raW5kID0gXCJjb25zdHJ1Y3RvclwiO1xuICAgICAgfSBlbHNlIHtcbiAgICAgICAgbWV0aG9kLmtpbmQgPSBcIm1ldGhvZFwiO1xuICAgICAgfVxuICAgICAgbWV0aG9kLnZhbHVlID0gdGhpcy5wYXJzZU1ldGhvZChpc0dlbmVyYXRvcik7XG4gICAgfVxuICAgIG5vZGUuYm9keS5ib2R5LnB1c2godGhpcy5maW5pc2hOb2RlKG1ldGhvZCwgXCJNZXRob2REZWZpbml0aW9uXCIpKTtcbiAgfVxuICB0aGlzLnBvcEN4KCk7XG4gIGlmICghdGhpcy5lYXQoXy50b2tUeXBlcy5icmFjZVIpKSB7XG4gICAgLy8gSWYgdGhlcmUgaXMgbm8gY2xvc2luZyBicmFjZSwgbWFrZSB0aGUgbm9kZSBzcGFuIHRvIHRoZSBzdGFydFxuICAgIC8vIG9mIHRoZSBuZXh0IHRva2VuICh0aGlzIGlzIHVzZWZ1bCBmb3IgVGVybilcbiAgICB0aGlzLmxhc3QuZW5kID0gdGhpcy50b2suc3RhcnQ7XG4gICAgaWYgKHRoaXMub3B0aW9ucy5sb2NhdGlvbnMpIHRoaXMubGFzdC5sb2MuZW5kID0gdGhpcy50b2subG9jLnN0YXJ0O1xuICB9XG4gIHRoaXMuc2VtaWNvbG9uKCk7XG4gIHRoaXMuZmluaXNoTm9kZShub2RlLmJvZHksIFwiQ2xhc3NCb2R5XCIpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIGlzU3RhdGVtZW50ID8gXCJDbGFzc0RlY2xhcmF0aW9uXCIgOiBcIkNsYXNzRXhwcmVzc2lvblwiKTtcbn07XG5cbmxwLnBhcnNlRnVuY3Rpb24gPSBmdW5jdGlvbiAobm9kZSwgaXNTdGF0ZW1lbnQpIHtcbiAgdGhpcy5pbml0RnVuY3Rpb24obm9kZSk7XG4gIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNikge1xuICAgIG5vZGUuZ2VuZXJhdG9yID0gdGhpcy5lYXQoXy50b2tUeXBlcy5zdGFyKTtcbiAgfVxuICBpZiAodGhpcy50b2sudHlwZSA9PT0gXy50b2tUeXBlcy5uYW1lKSBub2RlLmlkID0gdGhpcy5wYXJzZUlkZW50KCk7ZWxzZSBpZiAoaXNTdGF0ZW1lbnQpIG5vZGUuaWQgPSB0aGlzLmR1bW15SWRlbnQoKTtcbiAgbm9kZS5wYXJhbXMgPSB0aGlzLnBhcnNlRnVuY3Rpb25QYXJhbXMoKTtcbiAgbm9kZS5ib2R5ID0gdGhpcy5wYXJzZUJsb2NrKCk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgaXNTdGF0ZW1lbnQgPyBcIkZ1bmN0aW9uRGVjbGFyYXRpb25cIiA6IFwiRnVuY3Rpb25FeHByZXNzaW9uXCIpO1xufTtcblxubHAucGFyc2VFeHBvcnQgPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgdGhpcy5uZXh0KCk7XG4gIGlmICh0aGlzLmVhdChfLnRva1R5cGVzLnN0YXIpKSB7XG4gICAgbm9kZS5zb3VyY2UgPSB0aGlzLmVhdENvbnRleHR1YWwoXCJmcm9tXCIpID8gdGhpcy5wYXJzZUV4cHJBdG9tKCkgOiBudWxsO1xuICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJFeHBvcnRBbGxEZWNsYXJhdGlvblwiKTtcbiAgfVxuICBpZiAodGhpcy5lYXQoXy50b2tUeXBlcy5fZGVmYXVsdCkpIHtcbiAgICB2YXIgZXhwciA9IHRoaXMucGFyc2VNYXliZUFzc2lnbigpO1xuICAgIGlmIChleHByLmlkKSB7XG4gICAgICBzd2l0Y2ggKGV4cHIudHlwZSkge1xuICAgICAgICBjYXNlIFwiRnVuY3Rpb25FeHByZXNzaW9uXCI6XG4gICAgICAgICAgZXhwci50eXBlID0gXCJGdW5jdGlvbkRlY2xhcmF0aW9uXCI7YnJlYWs7XG4gICAgICAgIGNhc2UgXCJDbGFzc0V4cHJlc3Npb25cIjpcbiAgICAgICAgICBleHByLnR5cGUgPSBcIkNsYXNzRGVjbGFyYXRpb25cIjticmVhaztcbiAgICAgIH1cbiAgICB9XG4gICAgbm9kZS5kZWNsYXJhdGlvbiA9IGV4cHI7XG4gICAgdGhpcy5zZW1pY29sb24oKTtcbiAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiRXhwb3J0RGVmYXVsdERlY2xhcmF0aW9uXCIpO1xuICB9XG4gIGlmICh0aGlzLnRvay50eXBlLmtleXdvcmQpIHtcbiAgICBub2RlLmRlY2xhcmF0aW9uID0gdGhpcy5wYXJzZVN0YXRlbWVudCgpO1xuICAgIG5vZGUuc3BlY2lmaWVycyA9IFtdO1xuICAgIG5vZGUuc291cmNlID0gbnVsbDtcbiAgfSBlbHNlIHtcbiAgICBub2RlLmRlY2xhcmF0aW9uID0gbnVsbDtcbiAgICBub2RlLnNwZWNpZmllcnMgPSB0aGlzLnBhcnNlRXhwb3J0U3BlY2lmaWVyTGlzdCgpO1xuICAgIG5vZGUuc291cmNlID0gdGhpcy5lYXRDb250ZXh0dWFsKFwiZnJvbVwiKSA/IHRoaXMucGFyc2VFeHByQXRvbSgpIDogbnVsbDtcbiAgICB0aGlzLnNlbWljb2xvbigpO1xuICB9XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJFeHBvcnROYW1lZERlY2xhcmF0aW9uXCIpO1xufTtcblxubHAucGFyc2VJbXBvcnQgPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgdGhpcy5uZXh0KCk7XG4gIGlmICh0aGlzLnRvay50eXBlID09PSBfLnRva1R5cGVzLnN0cmluZykge1xuICAgIG5vZGUuc3BlY2lmaWVycyA9IFtdO1xuICAgIG5vZGUuc291cmNlID0gdGhpcy5wYXJzZUV4cHJBdG9tKCk7XG4gICAgbm9kZS5raW5kID0gXCJcIjtcbiAgfSBlbHNlIHtcbiAgICB2YXIgZWx0ID0gdW5kZWZpbmVkO1xuICAgIGlmICh0aGlzLnRvay50eXBlID09PSBfLnRva1R5cGVzLm5hbWUgJiYgdGhpcy50b2sudmFsdWUgIT09IFwiZnJvbVwiKSB7XG4gICAgICBlbHQgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICAgICAgZWx0LmxvY2FsID0gdGhpcy5wYXJzZUlkZW50KCk7XG4gICAgICB0aGlzLmZpbmlzaE5vZGUoZWx0LCBcIkltcG9ydERlZmF1bHRTcGVjaWZpZXJcIik7XG4gICAgICB0aGlzLmVhdChfLnRva1R5cGVzLmNvbW1hKTtcbiAgICB9XG4gICAgbm9kZS5zcGVjaWZpZXJzID0gdGhpcy5wYXJzZUltcG9ydFNwZWNpZmllckxpc3QoKTtcbiAgICBub2RlLnNvdXJjZSA9IHRoaXMuZWF0Q29udGV4dHVhbChcImZyb21cIikgPyB0aGlzLnBhcnNlRXhwckF0b20oKSA6IHRoaXMuZHVtbXlTdHJpbmcoKTtcbiAgICBpZiAoZWx0KSBub2RlLnNwZWNpZmllcnMudW5zaGlmdChlbHQpO1xuICB9XG4gIHRoaXMuc2VtaWNvbG9uKCk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJJbXBvcnREZWNsYXJhdGlvblwiKTtcbn07XG5cbmxwLnBhcnNlSW1wb3J0U3BlY2lmaWVyTGlzdCA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIGVsdHMgPSBbXTtcbiAgaWYgKHRoaXMudG9rLnR5cGUgPT09IF8udG9rVHlwZXMuc3Rhcikge1xuICAgIHZhciBlbHQgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICAgIHRoaXMubmV4dCgpO1xuICAgIGlmICh0aGlzLmVhdENvbnRleHR1YWwoXCJhc1wiKSkgZWx0LmxvY2FsID0gdGhpcy5wYXJzZUlkZW50KCk7XG4gICAgZWx0cy5wdXNoKHRoaXMuZmluaXNoTm9kZShlbHQsIFwiSW1wb3J0TmFtZXNwYWNlU3BlY2lmaWVyXCIpKTtcbiAgfSBlbHNlIHtcbiAgICB2YXIgaW5kZW50ID0gdGhpcy5jdXJJbmRlbnQsXG4gICAgICAgIGxpbmUgPSB0aGlzLmN1ckxpbmVTdGFydCxcbiAgICAgICAgY29udGludWVkTGluZSA9IHRoaXMubmV4dExpbmVTdGFydDtcbiAgICB0aGlzLnB1c2hDeCgpO1xuICAgIHRoaXMuZWF0KF8udG9rVHlwZXMuYnJhY2VMKTtcbiAgICBpZiAodGhpcy5jdXJMaW5lU3RhcnQgPiBjb250aW51ZWRMaW5lKSBjb250aW51ZWRMaW5lID0gdGhpcy5jdXJMaW5lU3RhcnQ7XG4gICAgd2hpbGUgKCF0aGlzLmNsb3NlcyhfLnRva1R5cGVzLmJyYWNlUiwgaW5kZW50ICsgKHRoaXMuY3VyTGluZVN0YXJ0IDw9IGNvbnRpbnVlZExpbmUgPyAxIDogMCksIGxpbmUpKSB7XG4gICAgICB2YXIgZWx0ID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgICAgIGlmICh0aGlzLmVhdChfLnRva1R5cGVzLnN0YXIpKSB7XG4gICAgICAgIGlmICh0aGlzLmVhdENvbnRleHR1YWwoXCJhc1wiKSkgZWx0LmxvY2FsID0gdGhpcy5wYXJzZUlkZW50KCk7XG4gICAgICAgIHRoaXMuZmluaXNoTm9kZShlbHQsIFwiSW1wb3J0TmFtZXNwYWNlU3BlY2lmaWVyXCIpO1xuICAgICAgfSBlbHNlIHtcbiAgICAgICAgaWYgKHRoaXMuaXNDb250ZXh0dWFsKFwiZnJvbVwiKSkgYnJlYWs7XG4gICAgICAgIGVsdC5pbXBvcnRlZCA9IHRoaXMucGFyc2VJZGVudCgpO1xuICAgICAgICBpZiAoX3BhcnNldXRpbC5pc0R1bW15KGVsdC5pbXBvcnRlZCkpIGJyZWFrO1xuICAgICAgICBlbHQubG9jYWwgPSB0aGlzLmVhdENvbnRleHR1YWwoXCJhc1wiKSA/IHRoaXMucGFyc2VJZGVudCgpIDogZWx0LmltcG9ydGVkO1xuICAgICAgICB0aGlzLmZpbmlzaE5vZGUoZWx0LCBcIkltcG9ydFNwZWNpZmllclwiKTtcbiAgICAgIH1cbiAgICAgIGVsdHMucHVzaChlbHQpO1xuICAgICAgdGhpcy5lYXQoXy50b2tUeXBlcy5jb21tYSk7XG4gICAgfVxuICAgIHRoaXMuZWF0KF8udG9rVHlwZXMuYnJhY2VSKTtcbiAgICB0aGlzLnBvcEN4KCk7XG4gIH1cbiAgcmV0dXJuIGVsdHM7XG59O1xuXG5scC5wYXJzZUV4cG9ydFNwZWNpZmllckxpc3QgPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBlbHRzID0gW107XG4gIHZhciBpbmRlbnQgPSB0aGlzLmN1ckluZGVudCxcbiAgICAgIGxpbmUgPSB0aGlzLmN1ckxpbmVTdGFydCxcbiAgICAgIGNvbnRpbnVlZExpbmUgPSB0aGlzLm5leHRMaW5lU3RhcnQ7XG4gIHRoaXMucHVzaEN4KCk7XG4gIHRoaXMuZWF0KF8udG9rVHlwZXMuYnJhY2VMKTtcbiAgaWYgKHRoaXMuY3VyTGluZVN0YXJ0ID4gY29udGludWVkTGluZSkgY29udGludWVkTGluZSA9IHRoaXMuY3VyTGluZVN0YXJ0O1xuICB3aGlsZSAoIXRoaXMuY2xvc2VzKF8udG9rVHlwZXMuYnJhY2VSLCBpbmRlbnQgKyAodGhpcy5jdXJMaW5lU3RhcnQgPD0gY29udGludWVkTGluZSA/IDEgOiAwKSwgbGluZSkpIHtcbiAgICBpZiAodGhpcy5pc0NvbnRleHR1YWwoXCJmcm9tXCIpKSBicmVhaztcbiAgICB2YXIgZWx0ID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgICBlbHQubG9jYWwgPSB0aGlzLnBhcnNlSWRlbnQoKTtcbiAgICBpZiAoX3BhcnNldXRpbC5pc0R1bW15KGVsdC5sb2NhbCkpIGJyZWFrO1xuICAgIGVsdC5leHBvcnRlZCA9IHRoaXMuZWF0Q29udGV4dHVhbChcImFzXCIpID8gdGhpcy5wYXJzZUlkZW50KCkgOiBlbHQubG9jYWw7XG4gICAgdGhpcy5maW5pc2hOb2RlKGVsdCwgXCJFeHBvcnRTcGVjaWZpZXJcIik7XG4gICAgZWx0cy5wdXNoKGVsdCk7XG4gICAgdGhpcy5lYXQoXy50b2tUeXBlcy5jb21tYSk7XG4gIH1cbiAgdGhpcy5lYXQoXy50b2tUeXBlcy5icmFjZVIpO1xuICB0aGlzLnBvcEN4KCk7XG4gIHJldHVybiBlbHRzO1xufTtcblxufSx7XCIuLlwiOjEsXCIuL3BhcnNldXRpbFwiOjQsXCIuL3N0YXRlXCI6NX1dLDc6W2Z1bmN0aW9uKF9kZXJlcV8sbW9kdWxlLGV4cG9ydHMpe1xuXCJ1c2Ugc3RyaWN0XCI7XG5cbnZhciBfID0gX2RlcmVxXyhcIi4uXCIpO1xuXG52YXIgX3N0YXRlID0gX2RlcmVxXyhcIi4vc3RhdGVcIik7XG5cbnZhciBscCA9IF9zdGF0ZS5Mb29zZVBhcnNlci5wcm90b3R5cGU7XG5cbmZ1bmN0aW9uIGlzU3BhY2UoY2gpIHtcbiAgcmV0dXJuIGNoIDwgMTQgJiYgY2ggPiA4IHx8IGNoID09PSAzMiB8fCBjaCA9PT0gMTYwIHx8IF8uaXNOZXdMaW5lKGNoKTtcbn1cblxubHAubmV4dCA9IGZ1bmN0aW9uICgpIHtcbiAgdGhpcy5sYXN0ID0gdGhpcy50b2s7XG4gIGlmICh0aGlzLmFoZWFkLmxlbmd0aCkgdGhpcy50b2sgPSB0aGlzLmFoZWFkLnNoaWZ0KCk7ZWxzZSB0aGlzLnRvayA9IHRoaXMucmVhZFRva2VuKCk7XG5cbiAgaWYgKHRoaXMudG9rLnN0YXJ0ID49IHRoaXMubmV4dExpbmVTdGFydCkge1xuICAgIHdoaWxlICh0aGlzLnRvay5zdGFydCA+PSB0aGlzLm5leHRMaW5lU3RhcnQpIHtcbiAgICAgIHRoaXMuY3VyTGluZVN0YXJ0ID0gdGhpcy5uZXh0TGluZVN0YXJ0O1xuICAgICAgdGhpcy5uZXh0TGluZVN0YXJ0ID0gdGhpcy5saW5lRW5kKHRoaXMuY3VyTGluZVN0YXJ0KSArIDE7XG4gICAgfVxuICAgIHRoaXMuY3VySW5kZW50ID0gdGhpcy5pbmRlbnRhdGlvbkFmdGVyKHRoaXMuY3VyTGluZVN0YXJ0KTtcbiAgfVxufTtcblxubHAucmVhZFRva2VuID0gZnVuY3Rpb24gKCkge1xuICBmb3IgKDs7KSB7XG4gICAgdHJ5IHtcbiAgICAgIHRoaXMudG9rcy5uZXh0KCk7XG4gICAgICBpZiAodGhpcy50b2tzLnR5cGUgPT09IF8udG9rVHlwZXMuZG90ICYmIHRoaXMuaW5wdXQuc3Vic3RyKHRoaXMudG9rcy5lbmQsIDEpID09PSBcIi5cIiAmJiB0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNikge1xuICAgICAgICB0aGlzLnRva3MuZW5kKys7XG4gICAgICAgIHRoaXMudG9rcy50eXBlID0gXy50b2tUeXBlcy5lbGxpcHNpcztcbiAgICAgIH1cbiAgICAgIHJldHVybiBuZXcgXy5Ub2tlbih0aGlzLnRva3MpO1xuICAgIH0gY2F0Y2ggKGUpIHtcbiAgICAgIGlmICghKGUgaW5zdGFuY2VvZiBTeW50YXhFcnJvcikpIHRocm93IGU7XG5cbiAgICAgIC8vIFRyeSB0byBza2lwIHNvbWUgdGV4dCwgYmFzZWQgb24gdGhlIGVycm9yIG1lc3NhZ2UsIGFuZCB0aGVuIGNvbnRpbnVlXG4gICAgICB2YXIgbXNnID0gZS5tZXNzYWdlLFxuICAgICAgICAgIHBvcyA9IGUucmFpc2VkQXQsXG4gICAgICAgICAgcmVwbGFjZSA9IHRydWU7XG4gICAgICBpZiAoL3VudGVybWluYXRlZC9pLnRlc3QobXNnKSkge1xuICAgICAgICBwb3MgPSB0aGlzLmxpbmVFbmQoZS5wb3MgKyAxKTtcbiAgICAgICAgaWYgKC9zdHJpbmcvLnRlc3QobXNnKSkge1xuICAgICAgICAgIHJlcGxhY2UgPSB7IHN0YXJ0OiBlLnBvcywgZW5kOiBwb3MsIHR5cGU6IF8udG9rVHlwZXMuc3RyaW5nLCB2YWx1ZTogdGhpcy5pbnB1dC5zbGljZShlLnBvcyArIDEsIHBvcykgfTtcbiAgICAgICAgfSBlbHNlIGlmICgvcmVndWxhciBleHByL2kudGVzdChtc2cpKSB7XG4gICAgICAgICAgdmFyIHJlID0gdGhpcy5pbnB1dC5zbGljZShlLnBvcywgcG9zKTtcbiAgICAgICAgICB0cnkge1xuICAgICAgICAgICAgcmUgPSBuZXcgUmVnRXhwKHJlKTtcbiAgICAgICAgICB9IGNhdGNoIChlKSB7fVxuICAgICAgICAgIHJlcGxhY2UgPSB7IHN0YXJ0OiBlLnBvcywgZW5kOiBwb3MsIHR5cGU6IF8udG9rVHlwZXMucmVnZXhwLCB2YWx1ZTogcmUgfTtcbiAgICAgICAgfSBlbHNlIGlmICgvdGVtcGxhdGUvLnRlc3QobXNnKSkge1xuICAgICAgICAgIHJlcGxhY2UgPSB7IHN0YXJ0OiBlLnBvcywgZW5kOiBwb3MsXG4gICAgICAgICAgICB0eXBlOiBfLnRva1R5cGVzLnRlbXBsYXRlLFxuICAgICAgICAgICAgdmFsdWU6IHRoaXMuaW5wdXQuc2xpY2UoZS5wb3MsIHBvcykgfTtcbiAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICByZXBsYWNlID0gZmFsc2U7XG4gICAgICAgIH1cbiAgICAgIH0gZWxzZSBpZiAoL2ludmFsaWQgKHVuaWNvZGV8cmVnZXhwfG51bWJlcil8ZXhwZWN0aW5nIHVuaWNvZGV8b2N0YWwgbGl0ZXJhbHxpcyByZXNlcnZlZHxkaXJlY3RseSBhZnRlciBudW1iZXJ8ZXhwZWN0ZWQgbnVtYmVyIGluIHJhZGl4L2kudGVzdChtc2cpKSB7XG4gICAgICAgIHdoaWxlIChwb3MgPCB0aGlzLmlucHV0Lmxlbmd0aCAmJiAhaXNTcGFjZSh0aGlzLmlucHV0LmNoYXJDb2RlQXQocG9zKSkpICsrcG9zO1xuICAgICAgfSBlbHNlIGlmICgvY2hhcmFjdGVyIGVzY2FwZXxleHBlY3RlZCBoZXhhZGVjaW1hbC9pLnRlc3QobXNnKSkge1xuICAgICAgICB3aGlsZSAocG9zIDwgdGhpcy5pbnB1dC5sZW5ndGgpIHtcbiAgICAgICAgICB2YXIgY2ggPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQocG9zKyspO1xuICAgICAgICAgIGlmIChjaCA9PT0gMzQgfHwgY2ggPT09IDM5IHx8IF8uaXNOZXdMaW5lKGNoKSkgYnJlYWs7XG4gICAgICAgIH1cbiAgICAgIH0gZWxzZSBpZiAoL3VuZXhwZWN0ZWQgY2hhcmFjdGVyL2kudGVzdChtc2cpKSB7XG4gICAgICAgIHBvcysrO1xuICAgICAgICByZXBsYWNlID0gZmFsc2U7XG4gICAgICB9IGVsc2UgaWYgKC9yZWd1bGFyIGV4cHJlc3Npb24vaS50ZXN0KG1zZykpIHtcbiAgICAgICAgcmVwbGFjZSA9IHRydWU7XG4gICAgICB9IGVsc2Uge1xuICAgICAgICB0aHJvdyBlO1xuICAgICAgfVxuICAgICAgdGhpcy5yZXNldFRvKHBvcyk7XG4gICAgICBpZiAocmVwbGFjZSA9PT0gdHJ1ZSkgcmVwbGFjZSA9IHsgc3RhcnQ6IHBvcywgZW5kOiBwb3MsIHR5cGU6IF8udG9rVHlwZXMubmFtZSwgdmFsdWU6IFwi4pyWXCIgfTtcbiAgICAgIGlmIChyZXBsYWNlKSB7XG4gICAgICAgIGlmICh0aGlzLm9wdGlvbnMubG9jYXRpb25zKSByZXBsYWNlLmxvYyA9IG5ldyBfLlNvdXJjZUxvY2F0aW9uKHRoaXMudG9rcywgXy5nZXRMaW5lSW5mbyh0aGlzLmlucHV0LCByZXBsYWNlLnN0YXJ0KSwgXy5nZXRMaW5lSW5mbyh0aGlzLmlucHV0LCByZXBsYWNlLmVuZCkpO1xuICAgICAgICByZXR1cm4gcmVwbGFjZTtcbiAgICAgIH1cbiAgICB9XG4gIH1cbn07XG5cbmxwLnJlc2V0VG8gPSBmdW5jdGlvbiAocG9zKSB7XG4gIHRoaXMudG9rcy5wb3MgPSBwb3M7XG4gIHZhciBjaCA9IHRoaXMuaW5wdXQuY2hhckF0KHBvcyAtIDEpO1xuICB0aGlzLnRva3MuZXhwckFsbG93ZWQgPSAhY2ggfHwgL1tcXFtcXHtcXCgsOzo/XFwvKj0rXFwtfiF8JiVePD5dLy50ZXN0KGNoKSB8fCAvW2Vud2ZkXS8udGVzdChjaCkgJiYgL1xcYihrZXl3b3Jkc3xjYXNlfGVsc2V8cmV0dXJufHRocm93fG5ld3xpbnwoaW5zdGFuY2V8dHlwZSlvZnxkZWxldGV8dm9pZCkkLy50ZXN0KHRoaXMuaW5wdXQuc2xpY2UocG9zIC0gMTAsIHBvcykpO1xuXG4gIGlmICh0aGlzLm9wdGlvbnMubG9jYXRpb25zKSB7XG4gICAgdGhpcy50b2tzLmN1ckxpbmUgPSAxO1xuICAgIHRoaXMudG9rcy5saW5lU3RhcnQgPSBfLmxpbmVCcmVha0cubGFzdEluZGV4ID0gMDtcbiAgICB2YXIgbWF0Y2ggPSB1bmRlZmluZWQ7XG4gICAgd2hpbGUgKChtYXRjaCA9IF8ubGluZUJyZWFrRy5leGVjKHRoaXMuaW5wdXQpKSAmJiBtYXRjaC5pbmRleCA8IHBvcykge1xuICAgICAgKyt0aGlzLnRva3MuY3VyTGluZTtcbiAgICAgIHRoaXMudG9rcy5saW5lU3RhcnQgPSBtYXRjaC5pbmRleCArIG1hdGNoWzBdLmxlbmd0aDtcbiAgICB9XG4gIH1cbn07XG5cbmxwLmxvb2tBaGVhZCA9IGZ1bmN0aW9uIChuKSB7XG4gIHdoaWxlIChuID4gdGhpcy5haGVhZC5sZW5ndGgpIHRoaXMuYWhlYWQucHVzaCh0aGlzLnJlYWRUb2tlbigpKTtcbiAgcmV0dXJuIHRoaXMuYWhlYWRbbiAtIDFdO1xufTtcblxufSx7XCIuLlwiOjEsXCIuL3N0YXRlXCI6NX1dfSx7fSxbM10pKDMpXG59KTsiLCIoZnVuY3Rpb24oZil7aWYodHlwZW9mIGV4cG9ydHM9PT1cIm9iamVjdFwiJiZ0eXBlb2YgbW9kdWxlIT09XCJ1bmRlZmluZWRcIil7bW9kdWxlLmV4cG9ydHM9ZigpfWVsc2UgaWYodHlwZW9mIGRlZmluZT09PVwiZnVuY3Rpb25cIiYmZGVmaW5lLmFtZCl7ZGVmaW5lKFtdLGYpfWVsc2V7dmFyIGc7aWYodHlwZW9mIHdpbmRvdyE9PVwidW5kZWZpbmVkXCIpe2c9d2luZG93fWVsc2UgaWYodHlwZW9mIGdsb2JhbCE9PVwidW5kZWZpbmVkXCIpe2c9Z2xvYmFsfWVsc2UgaWYodHlwZW9mIHNlbGYhPT1cInVuZGVmaW5lZFwiKXtnPXNlbGZ9ZWxzZXtnPXRoaXN9KGcuYWNvcm4gfHwgKGcuYWNvcm4gPSB7fSkpLndhbGsgPSBmKCl9fSkoZnVuY3Rpb24oKXt2YXIgZGVmaW5lLG1vZHVsZSxleHBvcnRzO3JldHVybiAoZnVuY3Rpb24gZSh0LG4scil7ZnVuY3Rpb24gcyhvLHUpe2lmKCFuW29dKXtpZighdFtvXSl7dmFyIGE9dHlwZW9mIHJlcXVpcmU9PVwiZnVuY3Rpb25cIiYmcmVxdWlyZTtpZighdSYmYSlyZXR1cm4gYShvLCEwKTtpZihpKXJldHVybiBpKG8sITApO3ZhciBmPW5ldyBFcnJvcihcIkNhbm5vdCBmaW5kIG1vZHVsZSAnXCIrbytcIidcIik7dGhyb3cgZi5jb2RlPVwiTU9EVUxFX05PVF9GT1VORFwiLGZ9dmFyIGw9bltvXT17ZXhwb3J0czp7fX07dFtvXVswXS5jYWxsKGwuZXhwb3J0cyxmdW5jdGlvbihlKXt2YXIgbj10W29dWzFdW2VdO3JldHVybiBzKG4/bjplKX0sbCxsLmV4cG9ydHMsZSx0LG4scil9cmV0dXJuIG5bb10uZXhwb3J0c312YXIgaT10eXBlb2YgcmVxdWlyZT09XCJmdW5jdGlvblwiJiZyZXF1aXJlO2Zvcih2YXIgbz0wO288ci5sZW5ndGg7bysrKXMocltvXSk7cmV0dXJuIHN9KSh7MTpbZnVuY3Rpb24oX2RlcmVxXyxtb2R1bGUsZXhwb3J0cyl7XG4vLyBBU1Qgd2Fsa2VyIG1vZHVsZSBmb3IgTW96aWxsYSBQYXJzZXIgQVBJIGNvbXBhdGlibGUgdHJlZXNcblxuLy8gQSBzaW1wbGUgd2FsayBpcyBvbmUgd2hlcmUgeW91IHNpbXBseSBzcGVjaWZ5IGNhbGxiYWNrcyB0byBiZVxuLy8gY2FsbGVkIG9uIHNwZWNpZmljIG5vZGVzLiBUaGUgbGFzdCB0d28gYXJndW1lbnRzIGFyZSBvcHRpb25hbC4gQVxuLy8gc2ltcGxlIHVzZSB3b3VsZCBiZVxuLy9cbi8vICAgICB3YWxrLnNpbXBsZShteVRyZWUsIHtcbi8vICAgICAgICAgRXhwcmVzc2lvbjogZnVuY3Rpb24obm9kZSkgeyAuLi4gfVxuLy8gICAgIH0pO1xuLy9cbi8vIHRvIGRvIHNvbWV0aGluZyB3aXRoIGFsbCBleHByZXNzaW9ucy4gQWxsIFBhcnNlciBBUEkgbm9kZSB0eXBlc1xuLy8gY2FuIGJlIHVzZWQgdG8gaWRlbnRpZnkgbm9kZSB0eXBlcywgYXMgd2VsbCBhcyBFeHByZXNzaW9uLFxuLy8gU3RhdGVtZW50LCBhbmQgU2NvcGVCb2R5LCB3aGljaCBkZW5vdGUgY2F0ZWdvcmllcyBvZiBub2Rlcy5cbi8vXG4vLyBUaGUgYmFzZSBhcmd1bWVudCBjYW4gYmUgdXNlZCB0byBwYXNzIGEgY3VzdG9tIChyZWN1cnNpdmUpXG4vLyB3YWxrZXIsIGFuZCBzdGF0ZSBjYW4gYmUgdXNlZCB0byBnaXZlIHRoaXMgd2Fsa2VkIGFuIGluaXRpYWxcbi8vIHN0YXRlLlxuXG5cInVzZSBzdHJpY3RcIjtcblxuZXhwb3J0cy5fX2VzTW9kdWxlID0gdHJ1ZTtcbmV4cG9ydHMuc2ltcGxlID0gc2ltcGxlO1xuZXhwb3J0cy5hbmNlc3RvciA9IGFuY2VzdG9yO1xuZXhwb3J0cy5yZWN1cnNpdmUgPSByZWN1cnNpdmU7XG5leHBvcnRzLmZpbmROb2RlQXQgPSBmaW5kTm9kZUF0O1xuZXhwb3J0cy5maW5kTm9kZUFyb3VuZCA9IGZpbmROb2RlQXJvdW5kO1xuZXhwb3J0cy5maW5kTm9kZUFmdGVyID0gZmluZE5vZGVBZnRlcjtcbmV4cG9ydHMuZmluZE5vZGVCZWZvcmUgPSBmaW5kTm9kZUJlZm9yZTtcbmV4cG9ydHMubWFrZSA9IG1ha2U7XG5cbmZ1bmN0aW9uIF9jbGFzc0NhbGxDaGVjayhpbnN0YW5jZSwgQ29uc3RydWN0b3IpIHsgaWYgKCEoaW5zdGFuY2UgaW5zdGFuY2VvZiBDb25zdHJ1Y3RvcikpIHsgdGhyb3cgbmV3IFR5cGVFcnJvcihcIkNhbm5vdCBjYWxsIGEgY2xhc3MgYXMgYSBmdW5jdGlvblwiKTsgfSB9XG5cbmZ1bmN0aW9uIHNpbXBsZShub2RlLCB2aXNpdG9ycywgYmFzZSwgc3RhdGUsIG92ZXJyaWRlKSB7XG4gIGlmICghYmFzZSkgYmFzZSA9IGV4cG9ydHMuYmFzZTsoZnVuY3Rpb24gYyhub2RlLCBzdCwgb3ZlcnJpZGUpIHtcbiAgICB2YXIgdHlwZSA9IG92ZXJyaWRlIHx8IG5vZGUudHlwZSxcbiAgICAgICAgZm91bmQgPSB2aXNpdG9yc1t0eXBlXTtcbiAgICBiYXNlW3R5cGVdKG5vZGUsIHN0LCBjKTtcbiAgICBpZiAoZm91bmQpIGZvdW5kKG5vZGUsIHN0KTtcbiAgfSkobm9kZSwgc3RhdGUsIG92ZXJyaWRlKTtcbn1cblxuLy8gQW4gYW5jZXN0b3Igd2FsayBidWlsZHMgdXAgYW4gYXJyYXkgb2YgYW5jZXN0b3Igbm9kZXMgKGluY2x1ZGluZ1xuLy8gdGhlIGN1cnJlbnQgbm9kZSkgYW5kIHBhc3NlcyB0aGVtIHRvIHRoZSBjYWxsYmFjayBhcyB0aGUgc3RhdGUgcGFyYW1ldGVyLlxuXG5mdW5jdGlvbiBhbmNlc3Rvcihub2RlLCB2aXNpdG9ycywgYmFzZSwgc3RhdGUpIHtcbiAgaWYgKCFiYXNlKSBiYXNlID0gZXhwb3J0cy5iYXNlO1xuICBpZiAoIXN0YXRlKSBzdGF0ZSA9IFtdOyhmdW5jdGlvbiBjKG5vZGUsIHN0LCBvdmVycmlkZSkge1xuICAgIHZhciB0eXBlID0gb3ZlcnJpZGUgfHwgbm9kZS50eXBlLFxuICAgICAgICBmb3VuZCA9IHZpc2l0b3JzW3R5cGVdO1xuICAgIGlmIChub2RlICE9IHN0W3N0Lmxlbmd0aCAtIDFdKSB7XG4gICAgICBzdCA9IHN0LnNsaWNlKCk7XG4gICAgICBzdC5wdXNoKG5vZGUpO1xuICAgIH1cbiAgICBiYXNlW3R5cGVdKG5vZGUsIHN0LCBjKTtcbiAgICBpZiAoZm91bmQpIGZvdW5kKG5vZGUsIHN0KTtcbiAgfSkobm9kZSwgc3RhdGUpO1xufVxuXG4vLyBBIHJlY3Vyc2l2ZSB3YWxrIGlzIG9uZSB3aGVyZSB5b3VyIGZ1bmN0aW9ucyBvdmVycmlkZSB0aGUgZGVmYXVsdFxuLy8gd2Fsa2Vycy4gVGhleSBjYW4gbW9kaWZ5IGFuZCByZXBsYWNlIHRoZSBzdGF0ZSBwYXJhbWV0ZXIgdGhhdCdzXG4vLyB0aHJlYWRlZCB0aHJvdWdoIHRoZSB3YWxrLCBhbmQgY2FuIG9wdCBob3cgYW5kIHdoZXRoZXIgdG8gd2Fsa1xuLy8gdGhlaXIgY2hpbGQgbm9kZXMgKGJ5IGNhbGxpbmcgdGhlaXIgdGhpcmQgYXJndW1lbnQgb24gdGhlc2Vcbi8vIG5vZGVzKS5cblxuZnVuY3Rpb24gcmVjdXJzaXZlKG5vZGUsIHN0YXRlLCBmdW5jcywgYmFzZSwgb3ZlcnJpZGUpIHtcbiAgdmFyIHZpc2l0b3IgPSBmdW5jcyA/IGV4cG9ydHMubWFrZShmdW5jcywgYmFzZSkgOiBiYXNlOyhmdW5jdGlvbiBjKG5vZGUsIHN0LCBvdmVycmlkZSkge1xuICAgIHZpc2l0b3Jbb3ZlcnJpZGUgfHwgbm9kZS50eXBlXShub2RlLCBzdCwgYyk7XG4gIH0pKG5vZGUsIHN0YXRlLCBvdmVycmlkZSk7XG59XG5cbmZ1bmN0aW9uIG1ha2VUZXN0KHRlc3QpIHtcbiAgaWYgKHR5cGVvZiB0ZXN0ID09IFwic3RyaW5nXCIpIHJldHVybiBmdW5jdGlvbiAodHlwZSkge1xuICAgIHJldHVybiB0eXBlID09IHRlc3Q7XG4gIH07ZWxzZSBpZiAoIXRlc3QpIHJldHVybiBmdW5jdGlvbiAoKSB7XG4gICAgcmV0dXJuIHRydWU7XG4gIH07ZWxzZSByZXR1cm4gdGVzdDtcbn1cblxudmFyIEZvdW5kID0gZnVuY3Rpb24gRm91bmQobm9kZSwgc3RhdGUpIHtcbiAgX2NsYXNzQ2FsbENoZWNrKHRoaXMsIEZvdW5kKTtcblxuICB0aGlzLm5vZGUgPSBub2RlO3RoaXMuc3RhdGUgPSBzdGF0ZTtcbn07XG5cbi8vIEZpbmQgYSBub2RlIHdpdGggYSBnaXZlbiBzdGFydCwgZW5kLCBhbmQgdHlwZSAoYWxsIGFyZSBvcHRpb25hbCxcbi8vIG51bGwgY2FuIGJlIHVzZWQgYXMgd2lsZGNhcmQpLiBSZXR1cm5zIGEge25vZGUsIHN0YXRlfSBvYmplY3QsIG9yXG4vLyB1bmRlZmluZWQgd2hlbiBpdCBkb2Vzbid0IGZpbmQgYSBtYXRjaGluZyBub2RlLlxuXG5mdW5jdGlvbiBmaW5kTm9kZUF0KG5vZGUsIHN0YXJ0LCBlbmQsIHRlc3QsIGJhc2UsIHN0YXRlKSB7XG4gIHRlc3QgPSBtYWtlVGVzdCh0ZXN0KTtcbiAgaWYgKCFiYXNlKSBiYXNlID0gZXhwb3J0cy5iYXNlO1xuICB0cnkge1xuICAgIDsoZnVuY3Rpb24gYyhub2RlLCBzdCwgb3ZlcnJpZGUpIHtcbiAgICAgIHZhciB0eXBlID0gb3ZlcnJpZGUgfHwgbm9kZS50eXBlO1xuICAgICAgaWYgKChzdGFydCA9PSBudWxsIHx8IG5vZGUuc3RhcnQgPD0gc3RhcnQpICYmIChlbmQgPT0gbnVsbCB8fCBub2RlLmVuZCA+PSBlbmQpKSBiYXNlW3R5cGVdKG5vZGUsIHN0LCBjKTtcbiAgICAgIGlmICgoc3RhcnQgPT0gbnVsbCB8fCBub2RlLnN0YXJ0ID09IHN0YXJ0KSAmJiAoZW5kID09IG51bGwgfHwgbm9kZS5lbmQgPT0gZW5kKSAmJiB0ZXN0KHR5cGUsIG5vZGUpKSB0aHJvdyBuZXcgRm91bmQobm9kZSwgc3QpO1xuICAgIH0pKG5vZGUsIHN0YXRlKTtcbiAgfSBjYXRjaCAoZSkge1xuICAgIGlmIChlIGluc3RhbmNlb2YgRm91bmQpIHJldHVybiBlO1xuICAgIHRocm93IGU7XG4gIH1cbn1cblxuLy8gRmluZCB0aGUgaW5uZXJtb3N0IG5vZGUgb2YgYSBnaXZlbiB0eXBlIHRoYXQgY29udGFpbnMgdGhlIGdpdmVuXG4vLyBwb3NpdGlvbi4gSW50ZXJmYWNlIHNpbWlsYXIgdG8gZmluZE5vZGVBdC5cblxuZnVuY3Rpb24gZmluZE5vZGVBcm91bmQobm9kZSwgcG9zLCB0ZXN0LCBiYXNlLCBzdGF0ZSkge1xuICB0ZXN0ID0gbWFrZVRlc3QodGVzdCk7XG4gIGlmICghYmFzZSkgYmFzZSA9IGV4cG9ydHMuYmFzZTtcbiAgdHJ5IHtcbiAgICA7KGZ1bmN0aW9uIGMobm9kZSwgc3QsIG92ZXJyaWRlKSB7XG4gICAgICB2YXIgdHlwZSA9IG92ZXJyaWRlIHx8IG5vZGUudHlwZTtcbiAgICAgIGlmIChub2RlLnN0YXJ0ID4gcG9zIHx8IG5vZGUuZW5kIDwgcG9zKSByZXR1cm47XG4gICAgICBiYXNlW3R5cGVdKG5vZGUsIHN0LCBjKTtcbiAgICAgIGlmICh0ZXN0KHR5cGUsIG5vZGUpKSB0aHJvdyBuZXcgRm91bmQobm9kZSwgc3QpO1xuICAgIH0pKG5vZGUsIHN0YXRlKTtcbiAgfSBjYXRjaCAoZSkge1xuICAgIGlmIChlIGluc3RhbmNlb2YgRm91bmQpIHJldHVybiBlO1xuICAgIHRocm93IGU7XG4gIH1cbn1cblxuLy8gRmluZCB0aGUgb3V0ZXJtb3N0IG1hdGNoaW5nIG5vZGUgYWZ0ZXIgYSBnaXZlbiBwb3NpdGlvbi5cblxuZnVuY3Rpb24gZmluZE5vZGVBZnRlcihub2RlLCBwb3MsIHRlc3QsIGJhc2UsIHN0YXRlKSB7XG4gIHRlc3QgPSBtYWtlVGVzdCh0ZXN0KTtcbiAgaWYgKCFiYXNlKSBiYXNlID0gZXhwb3J0cy5iYXNlO1xuICB0cnkge1xuICAgIDsoZnVuY3Rpb24gYyhub2RlLCBzdCwgb3ZlcnJpZGUpIHtcbiAgICAgIGlmIChub2RlLmVuZCA8IHBvcykgcmV0dXJuO1xuICAgICAgdmFyIHR5cGUgPSBvdmVycmlkZSB8fCBub2RlLnR5cGU7XG4gICAgICBpZiAobm9kZS5zdGFydCA+PSBwb3MgJiYgdGVzdCh0eXBlLCBub2RlKSkgdGhyb3cgbmV3IEZvdW5kKG5vZGUsIHN0KTtcbiAgICAgIGJhc2VbdHlwZV0obm9kZSwgc3QsIGMpO1xuICAgIH0pKG5vZGUsIHN0YXRlKTtcbiAgfSBjYXRjaCAoZSkge1xuICAgIGlmIChlIGluc3RhbmNlb2YgRm91bmQpIHJldHVybiBlO1xuICAgIHRocm93IGU7XG4gIH1cbn1cblxuLy8gRmluZCB0aGUgb3V0ZXJtb3N0IG1hdGNoaW5nIG5vZGUgYmVmb3JlIGEgZ2l2ZW4gcG9zaXRpb24uXG5cbmZ1bmN0aW9uIGZpbmROb2RlQmVmb3JlKG5vZGUsIHBvcywgdGVzdCwgYmFzZSwgc3RhdGUpIHtcbiAgdGVzdCA9IG1ha2VUZXN0KHRlc3QpO1xuICBpZiAoIWJhc2UpIGJhc2UgPSBleHBvcnRzLmJhc2U7XG4gIHZhciBtYXggPSB1bmRlZmluZWQ7KGZ1bmN0aW9uIGMobm9kZSwgc3QsIG92ZXJyaWRlKSB7XG4gICAgaWYgKG5vZGUuc3RhcnQgPiBwb3MpIHJldHVybjtcbiAgICB2YXIgdHlwZSA9IG92ZXJyaWRlIHx8IG5vZGUudHlwZTtcbiAgICBpZiAobm9kZS5lbmQgPD0gcG9zICYmICghbWF4IHx8IG1heC5ub2RlLmVuZCA8IG5vZGUuZW5kKSAmJiB0ZXN0KHR5cGUsIG5vZGUpKSBtYXggPSBuZXcgRm91bmQobm9kZSwgc3QpO1xuICAgIGJhc2VbdHlwZV0obm9kZSwgc3QsIGMpO1xuICB9KShub2RlLCBzdGF0ZSk7XG4gIHJldHVybiBtYXg7XG59XG5cbi8vIFVzZWQgdG8gY3JlYXRlIGEgY3VzdG9tIHdhbGtlci4gV2lsbCBmaWxsIGluIGFsbCBtaXNzaW5nIG5vZGVcbi8vIHR5cGUgcHJvcGVydGllcyB3aXRoIHRoZSBkZWZhdWx0cy5cblxuZnVuY3Rpb24gbWFrZShmdW5jcywgYmFzZSkge1xuICBpZiAoIWJhc2UpIGJhc2UgPSBleHBvcnRzLmJhc2U7XG4gIHZhciB2aXNpdG9yID0ge307XG4gIGZvciAodmFyIHR5cGUgaW4gYmFzZSkgdmlzaXRvclt0eXBlXSA9IGJhc2VbdHlwZV07XG4gIGZvciAodmFyIHR5cGUgaW4gZnVuY3MpIHZpc2l0b3JbdHlwZV0gPSBmdW5jc1t0eXBlXTtcbiAgcmV0dXJuIHZpc2l0b3I7XG59XG5cbmZ1bmN0aW9uIHNraXBUaHJvdWdoKG5vZGUsIHN0LCBjKSB7XG4gIGMobm9kZSwgc3QpO1xufVxuZnVuY3Rpb24gaWdub3JlKF9ub2RlLCBfc3QsIF9jKSB7fVxuXG4vLyBOb2RlIHdhbGtlcnMuXG5cbnZhciBiYXNlID0ge307XG5cbmV4cG9ydHMuYmFzZSA9IGJhc2U7XG5iYXNlLlByb2dyYW0gPSBiYXNlLkJsb2NrU3RhdGVtZW50ID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIGZvciAodmFyIGkgPSAwOyBpIDwgbm9kZS5ib2R5Lmxlbmd0aDsgKytpKSB7XG4gICAgYyhub2RlLmJvZHlbaV0sIHN0LCBcIlN0YXRlbWVudFwiKTtcbiAgfVxufTtcbmJhc2UuU3RhdGVtZW50ID0gc2tpcFRocm91Z2g7XG5iYXNlLkVtcHR5U3RhdGVtZW50ID0gaWdub3JlO1xuYmFzZS5FeHByZXNzaW9uU3RhdGVtZW50ID0gYmFzZS5QYXJlbnRoZXNpemVkRXhwcmVzc2lvbiA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICByZXR1cm4gYyhub2RlLmV4cHJlc3Npb24sIHN0LCBcIkV4cHJlc3Npb25cIik7XG59O1xuYmFzZS5JZlN0YXRlbWVudCA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBjKG5vZGUudGVzdCwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbiAgYyhub2RlLmNvbnNlcXVlbnQsIHN0LCBcIlN0YXRlbWVudFwiKTtcbiAgaWYgKG5vZGUuYWx0ZXJuYXRlKSBjKG5vZGUuYWx0ZXJuYXRlLCBzdCwgXCJTdGF0ZW1lbnRcIik7XG59O1xuYmFzZS5MYWJlbGVkU3RhdGVtZW50ID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIHJldHVybiBjKG5vZGUuYm9keSwgc3QsIFwiU3RhdGVtZW50XCIpO1xufTtcbmJhc2UuQnJlYWtTdGF0ZW1lbnQgPSBiYXNlLkNvbnRpbnVlU3RhdGVtZW50ID0gaWdub3JlO1xuYmFzZS5XaXRoU3RhdGVtZW50ID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIGMobm9kZS5vYmplY3QsIHN0LCBcIkV4cHJlc3Npb25cIik7XG4gIGMobm9kZS5ib2R5LCBzdCwgXCJTdGF0ZW1lbnRcIik7XG59O1xuYmFzZS5Td2l0Y2hTdGF0ZW1lbnQgPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgYyhub2RlLmRpc2NyaW1pbmFudCwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbiAgZm9yICh2YXIgaSA9IDA7IGkgPCBub2RlLmNhc2VzLmxlbmd0aDsgKytpKSB7XG4gICAgdmFyIGNzID0gbm9kZS5jYXNlc1tpXTtcbiAgICBpZiAoY3MudGVzdCkgYyhjcy50ZXN0LCBzdCwgXCJFeHByZXNzaW9uXCIpO1xuICAgIGZvciAodmFyIGogPSAwOyBqIDwgY3MuY29uc2VxdWVudC5sZW5ndGg7ICsraikge1xuICAgICAgYyhjcy5jb25zZXF1ZW50W2pdLCBzdCwgXCJTdGF0ZW1lbnRcIik7XG4gICAgfVxuICB9XG59O1xuYmFzZS5SZXR1cm5TdGF0ZW1lbnQgPSBiYXNlLllpZWxkRXhwcmVzc2lvbiA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBpZiAobm9kZS5hcmd1bWVudCkgYyhub2RlLmFyZ3VtZW50LCBzdCwgXCJFeHByZXNzaW9uXCIpO1xufTtcbmJhc2UuVGhyb3dTdGF0ZW1lbnQgPSBiYXNlLlNwcmVhZEVsZW1lbnQgPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgcmV0dXJuIGMobm9kZS5hcmd1bWVudCwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbn07XG5iYXNlLlRyeVN0YXRlbWVudCA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBjKG5vZGUuYmxvY2ssIHN0LCBcIlN0YXRlbWVudFwiKTtcbiAgaWYgKG5vZGUuaGFuZGxlcikge1xuICAgIGMobm9kZS5oYW5kbGVyLnBhcmFtLCBzdCwgXCJQYXR0ZXJuXCIpO1xuICAgIGMobm9kZS5oYW5kbGVyLmJvZHksIHN0LCBcIlNjb3BlQm9keVwiKTtcbiAgfVxuICBpZiAobm9kZS5maW5hbGl6ZXIpIGMobm9kZS5maW5hbGl6ZXIsIHN0LCBcIlN0YXRlbWVudFwiKTtcbn07XG5iYXNlLldoaWxlU3RhdGVtZW50ID0gYmFzZS5Eb1doaWxlU3RhdGVtZW50ID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIGMobm9kZS50ZXN0LCBzdCwgXCJFeHByZXNzaW9uXCIpO1xuICBjKG5vZGUuYm9keSwgc3QsIFwiU3RhdGVtZW50XCIpO1xufTtcbmJhc2UuRm9yU3RhdGVtZW50ID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIGlmIChub2RlLmluaXQpIGMobm9kZS5pbml0LCBzdCwgXCJGb3JJbml0XCIpO1xuICBpZiAobm9kZS50ZXN0KSBjKG5vZGUudGVzdCwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbiAgaWYgKG5vZGUudXBkYXRlKSBjKG5vZGUudXBkYXRlLCBzdCwgXCJFeHByZXNzaW9uXCIpO1xuICBjKG5vZGUuYm9keSwgc3QsIFwiU3RhdGVtZW50XCIpO1xufTtcbmJhc2UuRm9ySW5TdGF0ZW1lbnQgPSBiYXNlLkZvck9mU3RhdGVtZW50ID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIGMobm9kZS5sZWZ0LCBzdCwgXCJGb3JJbml0XCIpO1xuICBjKG5vZGUucmlnaHQsIHN0LCBcIkV4cHJlc3Npb25cIik7XG4gIGMobm9kZS5ib2R5LCBzdCwgXCJTdGF0ZW1lbnRcIik7XG59O1xuYmFzZS5Gb3JJbml0ID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIGlmIChub2RlLnR5cGUgPT0gXCJWYXJpYWJsZURlY2xhcmF0aW9uXCIpIGMobm9kZSwgc3QpO2Vsc2UgYyhub2RlLCBzdCwgXCJFeHByZXNzaW9uXCIpO1xufTtcbmJhc2UuRGVidWdnZXJTdGF0ZW1lbnQgPSBpZ25vcmU7XG5cbmJhc2UuRnVuY3Rpb25EZWNsYXJhdGlvbiA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICByZXR1cm4gYyhub2RlLCBzdCwgXCJGdW5jdGlvblwiKTtcbn07XG5iYXNlLlZhcmlhYmxlRGVjbGFyYXRpb24gPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgZm9yICh2YXIgaSA9IDA7IGkgPCBub2RlLmRlY2xhcmF0aW9ucy5sZW5ndGg7ICsraSkge1xuICAgIGMobm9kZS5kZWNsYXJhdGlvbnNbaV0sIHN0KTtcbiAgfVxufTtcbmJhc2UuVmFyaWFibGVEZWNsYXJhdG9yID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIGMobm9kZS5pZCwgc3QsIFwiUGF0dGVyblwiKTtcbiAgaWYgKG5vZGUuaW5pdCkgYyhub2RlLmluaXQsIHN0LCBcIkV4cHJlc3Npb25cIik7XG59O1xuXG5iYXNlLkZ1bmN0aW9uID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIGlmIChub2RlLmlkKSBjKG5vZGUuaWQsIHN0LCBcIlBhdHRlcm5cIik7XG4gIGZvciAodmFyIGkgPSAwOyBpIDwgbm9kZS5wYXJhbXMubGVuZ3RoOyBpKyspIHtcbiAgICBjKG5vZGUucGFyYW1zW2ldLCBzdCwgXCJQYXR0ZXJuXCIpO1xuICB9Yyhub2RlLmJvZHksIHN0LCBub2RlLmV4cHJlc3Npb24gPyBcIlNjb3BlRXhwcmVzc2lvblwiIDogXCJTY29wZUJvZHlcIik7XG59O1xuLy8gRklYTUUgZHJvcCB0aGVzZSBub2RlIHR5cGVzIGluIG5leHQgbWFqb3IgdmVyc2lvblxuLy8gKFRoZXkgYXJlIGF3a3dhcmQsIGFuZCBpbiBFUzYgZXZlcnkgYmxvY2sgY2FuIGJlIGEgc2NvcGUuKVxuYmFzZS5TY29wZUJvZHkgPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgcmV0dXJuIGMobm9kZSwgc3QsIFwiU3RhdGVtZW50XCIpO1xufTtcbmJhc2UuU2NvcGVFeHByZXNzaW9uID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIHJldHVybiBjKG5vZGUsIHN0LCBcIkV4cHJlc3Npb25cIik7XG59O1xuXG5iYXNlLlBhdHRlcm4gPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgaWYgKG5vZGUudHlwZSA9PSBcIklkZW50aWZpZXJcIikgYyhub2RlLCBzdCwgXCJWYXJpYWJsZVBhdHRlcm5cIik7ZWxzZSBpZiAobm9kZS50eXBlID09IFwiTWVtYmVyRXhwcmVzc2lvblwiKSBjKG5vZGUsIHN0LCBcIk1lbWJlclBhdHRlcm5cIik7ZWxzZSBjKG5vZGUsIHN0KTtcbn07XG5iYXNlLlZhcmlhYmxlUGF0dGVybiA9IGlnbm9yZTtcbmJhc2UuTWVtYmVyUGF0dGVybiA9IHNraXBUaHJvdWdoO1xuYmFzZS5SZXN0RWxlbWVudCA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICByZXR1cm4gYyhub2RlLmFyZ3VtZW50LCBzdCwgXCJQYXR0ZXJuXCIpO1xufTtcbmJhc2UuQXJyYXlQYXR0ZXJuID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIGZvciAodmFyIGkgPSAwOyBpIDwgbm9kZS5lbGVtZW50cy5sZW5ndGg7ICsraSkge1xuICAgIHZhciBlbHQgPSBub2RlLmVsZW1lbnRzW2ldO1xuICAgIGlmIChlbHQpIGMoZWx0LCBzdCwgXCJQYXR0ZXJuXCIpO1xuICB9XG59O1xuYmFzZS5PYmplY3RQYXR0ZXJuID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIGZvciAodmFyIGkgPSAwOyBpIDwgbm9kZS5wcm9wZXJ0aWVzLmxlbmd0aDsgKytpKSB7XG4gICAgYyhub2RlLnByb3BlcnRpZXNbaV0udmFsdWUsIHN0LCBcIlBhdHRlcm5cIik7XG4gIH1cbn07XG5cbmJhc2UuRXhwcmVzc2lvbiA9IHNraXBUaHJvdWdoO1xuYmFzZS5UaGlzRXhwcmVzc2lvbiA9IGJhc2UuU3VwZXIgPSBiYXNlLk1ldGFQcm9wZXJ0eSA9IGlnbm9yZTtcbmJhc2UuQXJyYXlFeHByZXNzaW9uID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIGZvciAodmFyIGkgPSAwOyBpIDwgbm9kZS5lbGVtZW50cy5sZW5ndGg7ICsraSkge1xuICAgIHZhciBlbHQgPSBub2RlLmVsZW1lbnRzW2ldO1xuICAgIGlmIChlbHQpIGMoZWx0LCBzdCwgXCJFeHByZXNzaW9uXCIpO1xuICB9XG59O1xuYmFzZS5PYmplY3RFeHByZXNzaW9uID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIGZvciAodmFyIGkgPSAwOyBpIDwgbm9kZS5wcm9wZXJ0aWVzLmxlbmd0aDsgKytpKSB7XG4gICAgYyhub2RlLnByb3BlcnRpZXNbaV0sIHN0KTtcbiAgfVxufTtcbmJhc2UuRnVuY3Rpb25FeHByZXNzaW9uID0gYmFzZS5BcnJvd0Z1bmN0aW9uRXhwcmVzc2lvbiA9IGJhc2UuRnVuY3Rpb25EZWNsYXJhdGlvbjtcbmJhc2UuU2VxdWVuY2VFeHByZXNzaW9uID0gYmFzZS5UZW1wbGF0ZUxpdGVyYWwgPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgZm9yICh2YXIgaSA9IDA7IGkgPCBub2RlLmV4cHJlc3Npb25zLmxlbmd0aDsgKytpKSB7XG4gICAgYyhub2RlLmV4cHJlc3Npb25zW2ldLCBzdCwgXCJFeHByZXNzaW9uXCIpO1xuICB9XG59O1xuYmFzZS5VbmFyeUV4cHJlc3Npb24gPSBiYXNlLlVwZGF0ZUV4cHJlc3Npb24gPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgYyhub2RlLmFyZ3VtZW50LCBzdCwgXCJFeHByZXNzaW9uXCIpO1xufTtcbmJhc2UuQmluYXJ5RXhwcmVzc2lvbiA9IGJhc2UuTG9naWNhbEV4cHJlc3Npb24gPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgYyhub2RlLmxlZnQsIHN0LCBcIkV4cHJlc3Npb25cIik7XG4gIGMobm9kZS5yaWdodCwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbn07XG5iYXNlLkFzc2lnbm1lbnRFeHByZXNzaW9uID0gYmFzZS5Bc3NpZ25tZW50UGF0dGVybiA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBjKG5vZGUubGVmdCwgc3QsIFwiUGF0dGVyblwiKTtcbiAgYyhub2RlLnJpZ2h0LCBzdCwgXCJFeHByZXNzaW9uXCIpO1xufTtcbmJhc2UuQ29uZGl0aW9uYWxFeHByZXNzaW9uID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIGMobm9kZS50ZXN0LCBzdCwgXCJFeHByZXNzaW9uXCIpO1xuICBjKG5vZGUuY29uc2VxdWVudCwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbiAgYyhub2RlLmFsdGVybmF0ZSwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbn07XG5iYXNlLk5ld0V4cHJlc3Npb24gPSBiYXNlLkNhbGxFeHByZXNzaW9uID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIGMobm9kZS5jYWxsZWUsIHN0LCBcIkV4cHJlc3Npb25cIik7XG4gIGlmIChub2RlLmFyZ3VtZW50cykgZm9yICh2YXIgaSA9IDA7IGkgPCBub2RlLmFyZ3VtZW50cy5sZW5ndGg7ICsraSkge1xuICAgIGMobm9kZS5hcmd1bWVudHNbaV0sIHN0LCBcIkV4cHJlc3Npb25cIik7XG4gIH1cbn07XG5iYXNlLk1lbWJlckV4cHJlc3Npb24gPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgYyhub2RlLm9iamVjdCwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbiAgaWYgKG5vZGUuY29tcHV0ZWQpIGMobm9kZS5wcm9wZXJ0eSwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbn07XG5iYXNlLkV4cG9ydE5hbWVkRGVjbGFyYXRpb24gPSBiYXNlLkV4cG9ydERlZmF1bHREZWNsYXJhdGlvbiA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBpZiAobm9kZS5kZWNsYXJhdGlvbikgYyhub2RlLmRlY2xhcmF0aW9uLCBzdCk7XG4gIGlmIChub2RlLnNvdXJjZSkgYyhub2RlLnNvdXJjZSwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbn07XG5iYXNlLkV4cG9ydEFsbERlY2xhcmF0aW9uID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIGMobm9kZS5zb3VyY2UsIHN0LCBcIkV4cHJlc3Npb25cIik7XG59O1xuYmFzZS5JbXBvcnREZWNsYXJhdGlvbiA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBmb3IgKHZhciBpID0gMDsgaSA8IG5vZGUuc3BlY2lmaWVycy5sZW5ndGg7IGkrKykge1xuICAgIGMobm9kZS5zcGVjaWZpZXJzW2ldLCBzdCk7XG4gIH1jKG5vZGUuc291cmNlLCBzdCwgXCJFeHByZXNzaW9uXCIpO1xufTtcbmJhc2UuSW1wb3J0U3BlY2lmaWVyID0gYmFzZS5JbXBvcnREZWZhdWx0U3BlY2lmaWVyID0gYmFzZS5JbXBvcnROYW1lc3BhY2VTcGVjaWZpZXIgPSBiYXNlLklkZW50aWZpZXIgPSBiYXNlLkxpdGVyYWwgPSBpZ25vcmU7XG5cbmJhc2UuVGFnZ2VkVGVtcGxhdGVFeHByZXNzaW9uID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIGMobm9kZS50YWcsIHN0LCBcIkV4cHJlc3Npb25cIik7XG4gIGMobm9kZS5xdWFzaSwgc3QpO1xufTtcbmJhc2UuQ2xhc3NEZWNsYXJhdGlvbiA9IGJhc2UuQ2xhc3NFeHByZXNzaW9uID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIHJldHVybiBjKG5vZGUsIHN0LCBcIkNsYXNzXCIpO1xufTtcbmJhc2UuQ2xhc3MgPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgaWYgKG5vZGUuaWQpIGMobm9kZS5pZCwgc3QsIFwiUGF0dGVyblwiKTtcbiAgaWYgKG5vZGUuc3VwZXJDbGFzcykgYyhub2RlLnN1cGVyQ2xhc3MsIHN0LCBcIkV4cHJlc3Npb25cIik7XG4gIGZvciAodmFyIGkgPSAwOyBpIDwgbm9kZS5ib2R5LmJvZHkubGVuZ3RoOyBpKyspIHtcbiAgICBjKG5vZGUuYm9keS5ib2R5W2ldLCBzdCk7XG4gIH1cbn07XG5iYXNlLk1ldGhvZERlZmluaXRpb24gPSBiYXNlLlByb3BlcnR5ID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIGlmIChub2RlLmNvbXB1dGVkKSBjKG5vZGUua2V5LCBzdCwgXCJFeHByZXNzaW9uXCIpO1xuICBjKG5vZGUudmFsdWUsIHN0LCBcIkV4cHJlc3Npb25cIik7XG59O1xuYmFzZS5Db21wcmVoZW5zaW9uRXhwcmVzc2lvbiA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBmb3IgKHZhciBpID0gMDsgaSA8IG5vZGUuYmxvY2tzLmxlbmd0aDsgaSsrKSB7XG4gICAgYyhub2RlLmJsb2Nrc1tpXS5yaWdodCwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbiAgfWMobm9kZS5ib2R5LCBzdCwgXCJFeHByZXNzaW9uXCIpO1xufTtcblxufSx7fV19LHt9LFsxXSkoMSlcbn0pOyIsImlmICh0eXBlb2YgT2JqZWN0LmNyZWF0ZSA9PT0gJ2Z1bmN0aW9uJykge1xuICAvLyBpbXBsZW1lbnRhdGlvbiBmcm9tIHN0YW5kYXJkIG5vZGUuanMgJ3V0aWwnIG1vZHVsZVxuICBtb2R1bGUuZXhwb3J0cyA9IGZ1bmN0aW9uIGluaGVyaXRzKGN0b3IsIHN1cGVyQ3Rvcikge1xuICAgIGN0b3Iuc3VwZXJfID0gc3VwZXJDdG9yXG4gICAgY3Rvci5wcm90b3R5cGUgPSBPYmplY3QuY3JlYXRlKHN1cGVyQ3Rvci5wcm90b3R5cGUsIHtcbiAgICAgIGNvbnN0cnVjdG9yOiB7XG4gICAgICAgIHZhbHVlOiBjdG9yLFxuICAgICAgICBlbnVtZXJhYmxlOiBmYWxzZSxcbiAgICAgICAgd3JpdGFibGU6IHRydWUsXG4gICAgICAgIGNvbmZpZ3VyYWJsZTogdHJ1ZVxuICAgICAgfVxuICAgIH0pO1xuICB9O1xufSBlbHNlIHtcbiAgLy8gb2xkIHNjaG9vbCBzaGltIGZvciBvbGQgYnJvd3NlcnNcbiAgbW9kdWxlLmV4cG9ydHMgPSBmdW5jdGlvbiBpbmhlcml0cyhjdG9yLCBzdXBlckN0b3IpIHtcbiAgICBjdG9yLnN1cGVyXyA9IHN1cGVyQ3RvclxuICAgIHZhciBUZW1wQ3RvciA9IGZ1bmN0aW9uICgpIHt9XG4gICAgVGVtcEN0b3IucHJvdG90eXBlID0gc3VwZXJDdG9yLnByb3RvdHlwZVxuICAgIGN0b3IucHJvdG90eXBlID0gbmV3IFRlbXBDdG9yKClcbiAgICBjdG9yLnByb3RvdHlwZS5jb25zdHJ1Y3RvciA9IGN0b3JcbiAgfVxufVxuIiwiLy8gc2hpbSBmb3IgdXNpbmcgcHJvY2VzcyBpbiBicm93c2VyXG5cbnZhciBwcm9jZXNzID0gbW9kdWxlLmV4cG9ydHMgPSB7fTtcbnZhciBxdWV1ZSA9IFtdO1xudmFyIGRyYWluaW5nID0gZmFsc2U7XG52YXIgY3VycmVudFF1ZXVlO1xudmFyIHF1ZXVlSW5kZXggPSAtMTtcblxuZnVuY3Rpb24gY2xlYW5VcE5leHRUaWNrKCkge1xuICAgIGRyYWluaW5nID0gZmFsc2U7XG4gICAgaWYgKGN1cnJlbnRRdWV1ZS5sZW5ndGgpIHtcbiAgICAgICAgcXVldWUgPSBjdXJyZW50UXVldWUuY29uY2F0KHF1ZXVlKTtcbiAgICB9IGVsc2Uge1xuICAgICAgICBxdWV1ZUluZGV4ID0gLTE7XG4gICAgfVxuICAgIGlmIChxdWV1ZS5sZW5ndGgpIHtcbiAgICAgICAgZHJhaW5RdWV1ZSgpO1xuICAgIH1cbn1cblxuZnVuY3Rpb24gZHJhaW5RdWV1ZSgpIHtcbiAgICBpZiAoZHJhaW5pbmcpIHtcbiAgICAgICAgcmV0dXJuO1xuICAgIH1cbiAgICB2YXIgdGltZW91dCA9IHNldFRpbWVvdXQoY2xlYW5VcE5leHRUaWNrKTtcbiAgICBkcmFpbmluZyA9IHRydWU7XG5cbiAgICB2YXIgbGVuID0gcXVldWUubGVuZ3RoO1xuICAgIHdoaWxlKGxlbikge1xuICAgICAgICBjdXJyZW50UXVldWUgPSBxdWV1ZTtcbiAgICAgICAgcXVldWUgPSBbXTtcbiAgICAgICAgd2hpbGUgKCsrcXVldWVJbmRleCA8IGxlbikge1xuICAgICAgICAgICAgY3VycmVudFF1ZXVlW3F1ZXVlSW5kZXhdLnJ1bigpO1xuICAgICAgICB9XG4gICAgICAgIHF1ZXVlSW5kZXggPSAtMTtcbiAgICAgICAgbGVuID0gcXVldWUubGVuZ3RoO1xuICAgIH1cbiAgICBjdXJyZW50UXVldWUgPSBudWxsO1xuICAgIGRyYWluaW5nID0gZmFsc2U7XG4gICAgY2xlYXJUaW1lb3V0KHRpbWVvdXQpO1xufVxuXG5wcm9jZXNzLm5leHRUaWNrID0gZnVuY3Rpb24gKGZ1bikge1xuICAgIHZhciBhcmdzID0gbmV3IEFycmF5KGFyZ3VtZW50cy5sZW5ndGggLSAxKTtcbiAgICBpZiAoYXJndW1lbnRzLmxlbmd0aCA+IDEpIHtcbiAgICAgICAgZm9yICh2YXIgaSA9IDE7IGkgPCBhcmd1bWVudHMubGVuZ3RoOyBpKyspIHtcbiAgICAgICAgICAgIGFyZ3NbaSAtIDFdID0gYXJndW1lbnRzW2ldO1xuICAgICAgICB9XG4gICAgfVxuICAgIHF1ZXVlLnB1c2gobmV3IEl0ZW0oZnVuLCBhcmdzKSk7XG4gICAgaWYgKHF1ZXVlLmxlbmd0aCA9PT0gMSAmJiAhZHJhaW5pbmcpIHtcbiAgICAgICAgc2V0VGltZW91dChkcmFpblF1ZXVlLCAwKTtcbiAgICB9XG59O1xuXG4vLyB2OCBsaWtlcyBwcmVkaWN0aWJsZSBvYmplY3RzXG5mdW5jdGlvbiBJdGVtKGZ1biwgYXJyYXkpIHtcbiAgICB0aGlzLmZ1biA9IGZ1bjtcbiAgICB0aGlzLmFycmF5ID0gYXJyYXk7XG59XG5JdGVtLnByb3RvdHlwZS5ydW4gPSBmdW5jdGlvbiAoKSB7XG4gICAgdGhpcy5mdW4uYXBwbHkobnVsbCwgdGhpcy5hcnJheSk7XG59O1xucHJvY2Vzcy50aXRsZSA9ICdicm93c2VyJztcbnByb2Nlc3MuYnJvd3NlciA9IHRydWU7XG5wcm9jZXNzLmVudiA9IHt9O1xucHJvY2Vzcy5hcmd2ID0gW107XG5wcm9jZXNzLnZlcnNpb24gPSAnJzsgLy8gZW1wdHkgc3RyaW5nIHRvIGF2b2lkIHJlZ2V4cCBpc3N1ZXNcbnByb2Nlc3MudmVyc2lvbnMgPSB7fTtcblxuZnVuY3Rpb24gbm9vcCgpIHt9XG5cbnByb2Nlc3Mub24gPSBub29wO1xucHJvY2Vzcy5hZGRMaXN0ZW5lciA9IG5vb3A7XG5wcm9jZXNzLm9uY2UgPSBub29wO1xucHJvY2Vzcy5vZmYgPSBub29wO1xucHJvY2Vzcy5yZW1vdmVMaXN0ZW5lciA9IG5vb3A7XG5wcm9jZXNzLnJlbW92ZUFsbExpc3RlbmVycyA9IG5vb3A7XG5wcm9jZXNzLmVtaXQgPSBub29wO1xuXG5wcm9jZXNzLmJpbmRpbmcgPSBmdW5jdGlvbiAobmFtZSkge1xuICAgIHRocm93IG5ldyBFcnJvcigncHJvY2Vzcy5iaW5kaW5nIGlzIG5vdCBzdXBwb3J0ZWQnKTtcbn07XG5cbi8vIFRPRE8oc2h0eWxtYW4pXG5wcm9jZXNzLmN3ZCA9IGZ1bmN0aW9uICgpIHsgcmV0dXJuICcvJyB9O1xucHJvY2Vzcy5jaGRpciA9IGZ1bmN0aW9uIChkaXIpIHtcbiAgICB0aHJvdyBuZXcgRXJyb3IoJ3Byb2Nlc3MuY2hkaXIgaXMgbm90IHN1cHBvcnRlZCcpO1xufTtcbnByb2Nlc3MudW1hc2sgPSBmdW5jdGlvbigpIHsgcmV0dXJuIDA7IH07XG4iLCJtb2R1bGUuZXhwb3J0cyA9IGZ1bmN0aW9uIGlzQnVmZmVyKGFyZykge1xuICByZXR1cm4gYXJnICYmIHR5cGVvZiBhcmcgPT09ICdvYmplY3QnXG4gICAgJiYgdHlwZW9mIGFyZy5jb3B5ID09PSAnZnVuY3Rpb24nXG4gICAgJiYgdHlwZW9mIGFyZy5maWxsID09PSAnZnVuY3Rpb24nXG4gICAgJiYgdHlwZW9mIGFyZy5yZWFkVUludDggPT09ICdmdW5jdGlvbic7XG59IiwiLy8gQ29weXJpZ2h0IEpveWVudCwgSW5jLiBhbmQgb3RoZXIgTm9kZSBjb250cmlidXRvcnMuXG4vL1xuLy8gUGVybWlzc2lvbiBpcyBoZXJlYnkgZ3JhbnRlZCwgZnJlZSBvZiBjaGFyZ2UsIHRvIGFueSBwZXJzb24gb2J0YWluaW5nIGFcbi8vIGNvcHkgb2YgdGhpcyBzb2Z0d2FyZSBhbmQgYXNzb2NpYXRlZCBkb2N1bWVudGF0aW9uIGZpbGVzICh0aGVcbi8vIFwiU29mdHdhcmVcIiksIHRvIGRlYWwgaW4gdGhlIFNvZnR3YXJlIHdpdGhvdXQgcmVzdHJpY3Rpb24sIGluY2x1ZGluZ1xuLy8gd2l0aG91dCBsaW1pdGF0aW9uIHRoZSByaWdodHMgdG8gdXNlLCBjb3B5LCBtb2RpZnksIG1lcmdlLCBwdWJsaXNoLFxuLy8gZGlzdHJpYnV0ZSwgc3VibGljZW5zZSwgYW5kL29yIHNlbGwgY29waWVzIG9mIHRoZSBTb2Z0d2FyZSwgYW5kIHRvIHBlcm1pdFxuLy8gcGVyc29ucyB0byB3aG9tIHRoZSBTb2Z0d2FyZSBpcyBmdXJuaXNoZWQgdG8gZG8gc28sIHN1YmplY3QgdG8gdGhlXG4vLyBmb2xsb3dpbmcgY29uZGl0aW9uczpcbi8vXG4vLyBUaGUgYWJvdmUgY29weXJpZ2h0IG5vdGljZSBhbmQgdGhpcyBwZXJtaXNzaW9uIG5vdGljZSBzaGFsbCBiZSBpbmNsdWRlZFxuLy8gaW4gYWxsIGNvcGllcyBvciBzdWJzdGFudGlhbCBwb3J0aW9ucyBvZiB0aGUgU29mdHdhcmUuXG4vL1xuLy8gVEhFIFNPRlRXQVJFIElTIFBST1ZJREVEIFwiQVMgSVNcIiwgV0lUSE9VVCBXQVJSQU5UWSBPRiBBTlkgS0lORCwgRVhQUkVTU1xuLy8gT1IgSU1QTElFRCwgSU5DTFVESU5HIEJVVCBOT1QgTElNSVRFRCBUTyBUSEUgV0FSUkFOVElFUyBPRlxuLy8gTUVSQ0hBTlRBQklMSVRZLCBGSVRORVNTIEZPUiBBIFBBUlRJQ1VMQVIgUFVSUE9TRSBBTkQgTk9OSU5GUklOR0VNRU5ULiBJTlxuLy8gTk8gRVZFTlQgU0hBTEwgVEhFIEFVVEhPUlMgT1IgQ09QWVJJR0hUIEhPTERFUlMgQkUgTElBQkxFIEZPUiBBTlkgQ0xBSU0sXG4vLyBEQU1BR0VTIE9SIE9USEVSIExJQUJJTElUWSwgV0hFVEhFUiBJTiBBTiBBQ1RJT04gT0YgQ09OVFJBQ1QsIFRPUlQgT1Jcbi8vIE9USEVSV0lTRSwgQVJJU0lORyBGUk9NLCBPVVQgT0YgT1IgSU4gQ09OTkVDVElPTiBXSVRIIFRIRSBTT0ZUV0FSRSBPUiBUSEVcbi8vIFVTRSBPUiBPVEhFUiBERUFMSU5HUyBJTiBUSEUgU09GVFdBUkUuXG5cbnZhciBmb3JtYXRSZWdFeHAgPSAvJVtzZGolXS9nO1xuZXhwb3J0cy5mb3JtYXQgPSBmdW5jdGlvbihmKSB7XG4gIGlmICghaXNTdHJpbmcoZikpIHtcbiAgICB2YXIgb2JqZWN0cyA9IFtdO1xuICAgIGZvciAodmFyIGkgPSAwOyBpIDwgYXJndW1lbnRzLmxlbmd0aDsgaSsrKSB7XG4gICAgICBvYmplY3RzLnB1c2goaW5zcGVjdChhcmd1bWVudHNbaV0pKTtcbiAgICB9XG4gICAgcmV0dXJuIG9iamVjdHMuam9pbignICcpO1xuICB9XG5cbiAgdmFyIGkgPSAxO1xuICB2YXIgYXJncyA9IGFyZ3VtZW50cztcbiAgdmFyIGxlbiA9IGFyZ3MubGVuZ3RoO1xuICB2YXIgc3RyID0gU3RyaW5nKGYpLnJlcGxhY2UoZm9ybWF0UmVnRXhwLCBmdW5jdGlvbih4KSB7XG4gICAgaWYgKHggPT09ICclJScpIHJldHVybiAnJSc7XG4gICAgaWYgKGkgPj0gbGVuKSByZXR1cm4geDtcbiAgICBzd2l0Y2ggKHgpIHtcbiAgICAgIGNhc2UgJyVzJzogcmV0dXJuIFN0cmluZyhhcmdzW2krK10pO1xuICAgICAgY2FzZSAnJWQnOiByZXR1cm4gTnVtYmVyKGFyZ3NbaSsrXSk7XG4gICAgICBjYXNlICclaic6XG4gICAgICAgIHRyeSB7XG4gICAgICAgICAgcmV0dXJuIEpTT04uc3RyaW5naWZ5KGFyZ3NbaSsrXSk7XG4gICAgICAgIH0gY2F0Y2ggKF8pIHtcbiAgICAgICAgICByZXR1cm4gJ1tDaXJjdWxhcl0nO1xuICAgICAgICB9XG4gICAgICBkZWZhdWx0OlxuICAgICAgICByZXR1cm4geDtcbiAgICB9XG4gIH0pO1xuICBmb3IgKHZhciB4ID0gYXJnc1tpXTsgaSA8IGxlbjsgeCA9IGFyZ3NbKytpXSkge1xuICAgIGlmIChpc051bGwoeCkgfHwgIWlzT2JqZWN0KHgpKSB7XG4gICAgICBzdHIgKz0gJyAnICsgeDtcbiAgICB9IGVsc2Uge1xuICAgICAgc3RyICs9ICcgJyArIGluc3BlY3QoeCk7XG4gICAgfVxuICB9XG4gIHJldHVybiBzdHI7XG59O1xuXG5cbi8vIE1hcmsgdGhhdCBhIG1ldGhvZCBzaG91bGQgbm90IGJlIHVzZWQuXG4vLyBSZXR1cm5zIGEgbW9kaWZpZWQgZnVuY3Rpb24gd2hpY2ggd2FybnMgb25jZSBieSBkZWZhdWx0LlxuLy8gSWYgLS1uby1kZXByZWNhdGlvbiBpcyBzZXQsIHRoZW4gaXQgaXMgYSBuby1vcC5cbmV4cG9ydHMuZGVwcmVjYXRlID0gZnVuY3Rpb24oZm4sIG1zZykge1xuICAvLyBBbGxvdyBmb3IgZGVwcmVjYXRpbmcgdGhpbmdzIGluIHRoZSBwcm9jZXNzIG9mIHN0YXJ0aW5nIHVwLlxuICBpZiAoaXNVbmRlZmluZWQoZ2xvYmFsLnByb2Nlc3MpKSB7XG4gICAgcmV0dXJuIGZ1bmN0aW9uKCkge1xuICAgICAgcmV0dXJuIGV4cG9ydHMuZGVwcmVjYXRlKGZuLCBtc2cpLmFwcGx5KHRoaXMsIGFyZ3VtZW50cyk7XG4gICAgfTtcbiAgfVxuXG4gIGlmIChwcm9jZXNzLm5vRGVwcmVjYXRpb24gPT09IHRydWUpIHtcbiAgICByZXR1cm4gZm47XG4gIH1cblxuICB2YXIgd2FybmVkID0gZmFsc2U7XG4gIGZ1bmN0aW9uIGRlcHJlY2F0ZWQoKSB7XG4gICAgaWYgKCF3YXJuZWQpIHtcbiAgICAgIGlmIChwcm9jZXNzLnRocm93RGVwcmVjYXRpb24pIHtcbiAgICAgICAgdGhyb3cgbmV3IEVycm9yKG1zZyk7XG4gICAgICB9IGVsc2UgaWYgKHByb2Nlc3MudHJhY2VEZXByZWNhdGlvbikge1xuICAgICAgICBjb25zb2xlLnRyYWNlKG1zZyk7XG4gICAgICB9IGVsc2Uge1xuICAgICAgICBjb25zb2xlLmVycm9yKG1zZyk7XG4gICAgICB9XG4gICAgICB3YXJuZWQgPSB0cnVlO1xuICAgIH1cbiAgICByZXR1cm4gZm4uYXBwbHkodGhpcywgYXJndW1lbnRzKTtcbiAgfVxuXG4gIHJldHVybiBkZXByZWNhdGVkO1xufTtcblxuXG52YXIgZGVidWdzID0ge307XG52YXIgZGVidWdFbnZpcm9uO1xuZXhwb3J0cy5kZWJ1Z2xvZyA9IGZ1bmN0aW9uKHNldCkge1xuICBpZiAoaXNVbmRlZmluZWQoZGVidWdFbnZpcm9uKSlcbiAgICBkZWJ1Z0Vudmlyb24gPSBwcm9jZXNzLmVudi5OT0RFX0RFQlVHIHx8ICcnO1xuICBzZXQgPSBzZXQudG9VcHBlckNhc2UoKTtcbiAgaWYgKCFkZWJ1Z3Nbc2V0XSkge1xuICAgIGlmIChuZXcgUmVnRXhwKCdcXFxcYicgKyBzZXQgKyAnXFxcXGInLCAnaScpLnRlc3QoZGVidWdFbnZpcm9uKSkge1xuICAgICAgdmFyIHBpZCA9IHByb2Nlc3MucGlkO1xuICAgICAgZGVidWdzW3NldF0gPSBmdW5jdGlvbigpIHtcbiAgICAgICAgdmFyIG1zZyA9IGV4cG9ydHMuZm9ybWF0LmFwcGx5KGV4cG9ydHMsIGFyZ3VtZW50cyk7XG4gICAgICAgIGNvbnNvbGUuZXJyb3IoJyVzICVkOiAlcycsIHNldCwgcGlkLCBtc2cpO1xuICAgICAgfTtcbiAgICB9IGVsc2Uge1xuICAgICAgZGVidWdzW3NldF0gPSBmdW5jdGlvbigpIHt9O1xuICAgIH1cbiAgfVxuICByZXR1cm4gZGVidWdzW3NldF07XG59O1xuXG5cbi8qKlxuICogRWNob3MgdGhlIHZhbHVlIG9mIGEgdmFsdWUuIFRyeXMgdG8gcHJpbnQgdGhlIHZhbHVlIG91dFxuICogaW4gdGhlIGJlc3Qgd2F5IHBvc3NpYmxlIGdpdmVuIHRoZSBkaWZmZXJlbnQgdHlwZXMuXG4gKlxuICogQHBhcmFtIHtPYmplY3R9IG9iaiBUaGUgb2JqZWN0IHRvIHByaW50IG91dC5cbiAqIEBwYXJhbSB7T2JqZWN0fSBvcHRzIE9wdGlvbmFsIG9wdGlvbnMgb2JqZWN0IHRoYXQgYWx0ZXJzIHRoZSBvdXRwdXQuXG4gKi9cbi8qIGxlZ2FjeTogb2JqLCBzaG93SGlkZGVuLCBkZXB0aCwgY29sb3JzKi9cbmZ1bmN0aW9uIGluc3BlY3Qob2JqLCBvcHRzKSB7XG4gIC8vIGRlZmF1bHQgb3B0aW9uc1xuICB2YXIgY3R4ID0ge1xuICAgIHNlZW46IFtdLFxuICAgIHN0eWxpemU6IHN0eWxpemVOb0NvbG9yXG4gIH07XG4gIC8vIGxlZ2FjeS4uLlxuICBpZiAoYXJndW1lbnRzLmxlbmd0aCA+PSAzKSBjdHguZGVwdGggPSBhcmd1bWVudHNbMl07XG4gIGlmIChhcmd1bWVudHMubGVuZ3RoID49IDQpIGN0eC5jb2xvcnMgPSBhcmd1bWVudHNbM107XG4gIGlmIChpc0Jvb2xlYW4ob3B0cykpIHtcbiAgICAvLyBsZWdhY3kuLi5cbiAgICBjdHguc2hvd0hpZGRlbiA9IG9wdHM7XG4gIH0gZWxzZSBpZiAob3B0cykge1xuICAgIC8vIGdvdCBhbiBcIm9wdGlvbnNcIiBvYmplY3RcbiAgICBleHBvcnRzLl9leHRlbmQoY3R4LCBvcHRzKTtcbiAgfVxuICAvLyBzZXQgZGVmYXVsdCBvcHRpb25zXG4gIGlmIChpc1VuZGVmaW5lZChjdHguc2hvd0hpZGRlbikpIGN0eC5zaG93SGlkZGVuID0gZmFsc2U7XG4gIGlmIChpc1VuZGVmaW5lZChjdHguZGVwdGgpKSBjdHguZGVwdGggPSAyO1xuICBpZiAoaXNVbmRlZmluZWQoY3R4LmNvbG9ycykpIGN0eC5jb2xvcnMgPSBmYWxzZTtcbiAgaWYgKGlzVW5kZWZpbmVkKGN0eC5jdXN0b21JbnNwZWN0KSkgY3R4LmN1c3RvbUluc3BlY3QgPSB0cnVlO1xuICBpZiAoY3R4LmNvbG9ycykgY3R4LnN0eWxpemUgPSBzdHlsaXplV2l0aENvbG9yO1xuICByZXR1cm4gZm9ybWF0VmFsdWUoY3R4LCBvYmosIGN0eC5kZXB0aCk7XG59XG5leHBvcnRzLmluc3BlY3QgPSBpbnNwZWN0O1xuXG5cbi8vIGh0dHA6Ly9lbi53aWtpcGVkaWEub3JnL3dpa2kvQU5TSV9lc2NhcGVfY29kZSNncmFwaGljc1xuaW5zcGVjdC5jb2xvcnMgPSB7XG4gICdib2xkJyA6IFsxLCAyMl0sXG4gICdpdGFsaWMnIDogWzMsIDIzXSxcbiAgJ3VuZGVybGluZScgOiBbNCwgMjRdLFxuICAnaW52ZXJzZScgOiBbNywgMjddLFxuICAnd2hpdGUnIDogWzM3LCAzOV0sXG4gICdncmV5JyA6IFs5MCwgMzldLFxuICAnYmxhY2snIDogWzMwLCAzOV0sXG4gICdibHVlJyA6IFszNCwgMzldLFxuICAnY3lhbicgOiBbMzYsIDM5XSxcbiAgJ2dyZWVuJyA6IFszMiwgMzldLFxuICAnbWFnZW50YScgOiBbMzUsIDM5XSxcbiAgJ3JlZCcgOiBbMzEsIDM5XSxcbiAgJ3llbGxvdycgOiBbMzMsIDM5XVxufTtcblxuLy8gRG9uJ3QgdXNlICdibHVlJyBub3QgdmlzaWJsZSBvbiBjbWQuZXhlXG5pbnNwZWN0LnN0eWxlcyA9IHtcbiAgJ3NwZWNpYWwnOiAnY3lhbicsXG4gICdudW1iZXInOiAneWVsbG93JyxcbiAgJ2Jvb2xlYW4nOiAneWVsbG93JyxcbiAgJ3VuZGVmaW5lZCc6ICdncmV5JyxcbiAgJ251bGwnOiAnYm9sZCcsXG4gICdzdHJpbmcnOiAnZ3JlZW4nLFxuICAnZGF0ZSc6ICdtYWdlbnRhJyxcbiAgLy8gXCJuYW1lXCI6IGludGVudGlvbmFsbHkgbm90IHN0eWxpbmdcbiAgJ3JlZ2V4cCc6ICdyZWQnXG59O1xuXG5cbmZ1bmN0aW9uIHN0eWxpemVXaXRoQ29sb3Ioc3RyLCBzdHlsZVR5cGUpIHtcbiAgdmFyIHN0eWxlID0gaW5zcGVjdC5zdHlsZXNbc3R5bGVUeXBlXTtcblxuICBpZiAoc3R5bGUpIHtcbiAgICByZXR1cm4gJ1xcdTAwMWJbJyArIGluc3BlY3QuY29sb3JzW3N0eWxlXVswXSArICdtJyArIHN0ciArXG4gICAgICAgICAgICdcXHUwMDFiWycgKyBpbnNwZWN0LmNvbG9yc1tzdHlsZV1bMV0gKyAnbSc7XG4gIH0gZWxzZSB7XG4gICAgcmV0dXJuIHN0cjtcbiAgfVxufVxuXG5cbmZ1bmN0aW9uIHN0eWxpemVOb0NvbG9yKHN0ciwgc3R5bGVUeXBlKSB7XG4gIHJldHVybiBzdHI7XG59XG5cblxuZnVuY3Rpb24gYXJyYXlUb0hhc2goYXJyYXkpIHtcbiAgdmFyIGhhc2ggPSB7fTtcblxuICBhcnJheS5mb3JFYWNoKGZ1bmN0aW9uKHZhbCwgaWR4KSB7XG4gICAgaGFzaFt2YWxdID0gdHJ1ZTtcbiAgfSk7XG5cbiAgcmV0dXJuIGhhc2g7XG59XG5cblxuZnVuY3Rpb24gZm9ybWF0VmFsdWUoY3R4LCB2YWx1ZSwgcmVjdXJzZVRpbWVzKSB7XG4gIC8vIFByb3ZpZGUgYSBob29rIGZvciB1c2VyLXNwZWNpZmllZCBpbnNwZWN0IGZ1bmN0aW9ucy5cbiAgLy8gQ2hlY2sgdGhhdCB2YWx1ZSBpcyBhbiBvYmplY3Qgd2l0aCBhbiBpbnNwZWN0IGZ1bmN0aW9uIG9uIGl0XG4gIGlmIChjdHguY3VzdG9tSW5zcGVjdCAmJlxuICAgICAgdmFsdWUgJiZcbiAgICAgIGlzRnVuY3Rpb24odmFsdWUuaW5zcGVjdCkgJiZcbiAgICAgIC8vIEZpbHRlciBvdXQgdGhlIHV0aWwgbW9kdWxlLCBpdCdzIGluc3BlY3QgZnVuY3Rpb24gaXMgc3BlY2lhbFxuICAgICAgdmFsdWUuaW5zcGVjdCAhPT0gZXhwb3J0cy5pbnNwZWN0ICYmXG4gICAgICAvLyBBbHNvIGZpbHRlciBvdXQgYW55IHByb3RvdHlwZSBvYmplY3RzIHVzaW5nIHRoZSBjaXJjdWxhciBjaGVjay5cbiAgICAgICEodmFsdWUuY29uc3RydWN0b3IgJiYgdmFsdWUuY29uc3RydWN0b3IucHJvdG90eXBlID09PSB2YWx1ZSkpIHtcbiAgICB2YXIgcmV0ID0gdmFsdWUuaW5zcGVjdChyZWN1cnNlVGltZXMsIGN0eCk7XG4gICAgaWYgKCFpc1N0cmluZyhyZXQpKSB7XG4gICAgICByZXQgPSBmb3JtYXRWYWx1ZShjdHgsIHJldCwgcmVjdXJzZVRpbWVzKTtcbiAgICB9XG4gICAgcmV0dXJuIHJldDtcbiAgfVxuXG4gIC8vIFByaW1pdGl2ZSB0eXBlcyBjYW5ub3QgaGF2ZSBwcm9wZXJ0aWVzXG4gIHZhciBwcmltaXRpdmUgPSBmb3JtYXRQcmltaXRpdmUoY3R4LCB2YWx1ZSk7XG4gIGlmIChwcmltaXRpdmUpIHtcbiAgICByZXR1cm4gcHJpbWl0aXZlO1xuICB9XG5cbiAgLy8gTG9vayB1cCB0aGUga2V5cyBvZiB0aGUgb2JqZWN0LlxuICB2YXIga2V5cyA9IE9iamVjdC5rZXlzKHZhbHVlKTtcbiAgdmFyIHZpc2libGVLZXlzID0gYXJyYXlUb0hhc2goa2V5cyk7XG5cbiAgaWYgKGN0eC5zaG93SGlkZGVuKSB7XG4gICAga2V5cyA9IE9iamVjdC5nZXRPd25Qcm9wZXJ0eU5hbWVzKHZhbHVlKTtcbiAgfVxuXG4gIC8vIElFIGRvZXNuJ3QgbWFrZSBlcnJvciBmaWVsZHMgbm9uLWVudW1lcmFibGVcbiAgLy8gaHR0cDovL21zZG4ubWljcm9zb2Z0LmNvbS9lbi11cy9saWJyYXJ5L2llL2R3dzUyc2J0KHY9dnMuOTQpLmFzcHhcbiAgaWYgKGlzRXJyb3IodmFsdWUpXG4gICAgICAmJiAoa2V5cy5pbmRleE9mKCdtZXNzYWdlJykgPj0gMCB8fCBrZXlzLmluZGV4T2YoJ2Rlc2NyaXB0aW9uJykgPj0gMCkpIHtcbiAgICByZXR1cm4gZm9ybWF0RXJyb3IodmFsdWUpO1xuICB9XG5cbiAgLy8gU29tZSB0eXBlIG9mIG9iamVjdCB3aXRob3V0IHByb3BlcnRpZXMgY2FuIGJlIHNob3J0Y3V0dGVkLlxuICBpZiAoa2V5cy5sZW5ndGggPT09IDApIHtcbiAgICBpZiAoaXNGdW5jdGlvbih2YWx1ZSkpIHtcbiAgICAgIHZhciBuYW1lID0gdmFsdWUubmFtZSA/ICc6ICcgKyB2YWx1ZS5uYW1lIDogJyc7XG4gICAgICByZXR1cm4gY3R4LnN0eWxpemUoJ1tGdW5jdGlvbicgKyBuYW1lICsgJ10nLCAnc3BlY2lhbCcpO1xuICAgIH1cbiAgICBpZiAoaXNSZWdFeHAodmFsdWUpKSB7XG4gICAgICByZXR1cm4gY3R4LnN0eWxpemUoUmVnRXhwLnByb3RvdHlwZS50b1N0cmluZy5jYWxsKHZhbHVlKSwgJ3JlZ2V4cCcpO1xuICAgIH1cbiAgICBpZiAoaXNEYXRlKHZhbHVlKSkge1xuICAgICAgcmV0dXJuIGN0eC5zdHlsaXplKERhdGUucHJvdG90eXBlLnRvU3RyaW5nLmNhbGwodmFsdWUpLCAnZGF0ZScpO1xuICAgIH1cbiAgICBpZiAoaXNFcnJvcih2YWx1ZSkpIHtcbiAgICAgIHJldHVybiBmb3JtYXRFcnJvcih2YWx1ZSk7XG4gICAgfVxuICB9XG5cbiAgdmFyIGJhc2UgPSAnJywgYXJyYXkgPSBmYWxzZSwgYnJhY2VzID0gWyd7JywgJ30nXTtcblxuICAvLyBNYWtlIEFycmF5IHNheSB0aGF0IHRoZXkgYXJlIEFycmF5XG4gIGlmIChpc0FycmF5KHZhbHVlKSkge1xuICAgIGFycmF5ID0gdHJ1ZTtcbiAgICBicmFjZXMgPSBbJ1snLCAnXSddO1xuICB9XG5cbiAgLy8gTWFrZSBmdW5jdGlvbnMgc2F5IHRoYXQgdGhleSBhcmUgZnVuY3Rpb25zXG4gIGlmIChpc0Z1bmN0aW9uKHZhbHVlKSkge1xuICAgIHZhciBuID0gdmFsdWUubmFtZSA/ICc6ICcgKyB2YWx1ZS5uYW1lIDogJyc7XG4gICAgYmFzZSA9ICcgW0Z1bmN0aW9uJyArIG4gKyAnXSc7XG4gIH1cblxuICAvLyBNYWtlIFJlZ0V4cHMgc2F5IHRoYXQgdGhleSBhcmUgUmVnRXhwc1xuICBpZiAoaXNSZWdFeHAodmFsdWUpKSB7XG4gICAgYmFzZSA9ICcgJyArIFJlZ0V4cC5wcm90b3R5cGUudG9TdHJpbmcuY2FsbCh2YWx1ZSk7XG4gIH1cblxuICAvLyBNYWtlIGRhdGVzIHdpdGggcHJvcGVydGllcyBmaXJzdCBzYXkgdGhlIGRhdGVcbiAgaWYgKGlzRGF0ZSh2YWx1ZSkpIHtcbiAgICBiYXNlID0gJyAnICsgRGF0ZS5wcm90b3R5cGUudG9VVENTdHJpbmcuY2FsbCh2YWx1ZSk7XG4gIH1cblxuICAvLyBNYWtlIGVycm9yIHdpdGggbWVzc2FnZSBmaXJzdCBzYXkgdGhlIGVycm9yXG4gIGlmIChpc0Vycm9yKHZhbHVlKSkge1xuICAgIGJhc2UgPSAnICcgKyBmb3JtYXRFcnJvcih2YWx1ZSk7XG4gIH1cblxuICBpZiAoa2V5cy5sZW5ndGggPT09IDAgJiYgKCFhcnJheSB8fCB2YWx1ZS5sZW5ndGggPT0gMCkpIHtcbiAgICByZXR1cm4gYnJhY2VzWzBdICsgYmFzZSArIGJyYWNlc1sxXTtcbiAgfVxuXG4gIGlmIChyZWN1cnNlVGltZXMgPCAwKSB7XG4gICAgaWYgKGlzUmVnRXhwKHZhbHVlKSkge1xuICAgICAgcmV0dXJuIGN0eC5zdHlsaXplKFJlZ0V4cC5wcm90b3R5cGUudG9TdHJpbmcuY2FsbCh2YWx1ZSksICdyZWdleHAnKTtcbiAgICB9IGVsc2Uge1xuICAgICAgcmV0dXJuIGN0eC5zdHlsaXplKCdbT2JqZWN0XScsICdzcGVjaWFsJyk7XG4gICAgfVxuICB9XG5cbiAgY3R4LnNlZW4ucHVzaCh2YWx1ZSk7XG5cbiAgdmFyIG91dHB1dDtcbiAgaWYgKGFycmF5KSB7XG4gICAgb3V0cHV0ID0gZm9ybWF0QXJyYXkoY3R4LCB2YWx1ZSwgcmVjdXJzZVRpbWVzLCB2aXNpYmxlS2V5cywga2V5cyk7XG4gIH0gZWxzZSB7XG4gICAgb3V0cHV0ID0ga2V5cy5tYXAoZnVuY3Rpb24oa2V5KSB7XG4gICAgICByZXR1cm4gZm9ybWF0UHJvcGVydHkoY3R4LCB2YWx1ZSwgcmVjdXJzZVRpbWVzLCB2aXNpYmxlS2V5cywga2V5LCBhcnJheSk7XG4gICAgfSk7XG4gIH1cblxuICBjdHguc2Vlbi5wb3AoKTtcblxuICByZXR1cm4gcmVkdWNlVG9TaW5nbGVTdHJpbmcob3V0cHV0LCBiYXNlLCBicmFjZXMpO1xufVxuXG5cbmZ1bmN0aW9uIGZvcm1hdFByaW1pdGl2ZShjdHgsIHZhbHVlKSB7XG4gIGlmIChpc1VuZGVmaW5lZCh2YWx1ZSkpXG4gICAgcmV0dXJuIGN0eC5zdHlsaXplKCd1bmRlZmluZWQnLCAndW5kZWZpbmVkJyk7XG4gIGlmIChpc1N0cmluZyh2YWx1ZSkpIHtcbiAgICB2YXIgc2ltcGxlID0gJ1xcJycgKyBKU09OLnN0cmluZ2lmeSh2YWx1ZSkucmVwbGFjZSgvXlwifFwiJC9nLCAnJylcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIC5yZXBsYWNlKC8nL2csIFwiXFxcXCdcIilcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIC5yZXBsYWNlKC9cXFxcXCIvZywgJ1wiJykgKyAnXFwnJztcbiAgICByZXR1cm4gY3R4LnN0eWxpemUoc2ltcGxlLCAnc3RyaW5nJyk7XG4gIH1cbiAgaWYgKGlzTnVtYmVyKHZhbHVlKSlcbiAgICByZXR1cm4gY3R4LnN0eWxpemUoJycgKyB2YWx1ZSwgJ251bWJlcicpO1xuICBpZiAoaXNCb29sZWFuKHZhbHVlKSlcbiAgICByZXR1cm4gY3R4LnN0eWxpemUoJycgKyB2YWx1ZSwgJ2Jvb2xlYW4nKTtcbiAgLy8gRm9yIHNvbWUgcmVhc29uIHR5cGVvZiBudWxsIGlzIFwib2JqZWN0XCIsIHNvIHNwZWNpYWwgY2FzZSBoZXJlLlxuICBpZiAoaXNOdWxsKHZhbHVlKSlcbiAgICByZXR1cm4gY3R4LnN0eWxpemUoJ251bGwnLCAnbnVsbCcpO1xufVxuXG5cbmZ1bmN0aW9uIGZvcm1hdEVycm9yKHZhbHVlKSB7XG4gIHJldHVybiAnWycgKyBFcnJvci5wcm90b3R5cGUudG9TdHJpbmcuY2FsbCh2YWx1ZSkgKyAnXSc7XG59XG5cblxuZnVuY3Rpb24gZm9ybWF0QXJyYXkoY3R4LCB2YWx1ZSwgcmVjdXJzZVRpbWVzLCB2aXNpYmxlS2V5cywga2V5cykge1xuICB2YXIgb3V0cHV0ID0gW107XG4gIGZvciAodmFyIGkgPSAwLCBsID0gdmFsdWUubGVuZ3RoOyBpIDwgbDsgKytpKSB7XG4gICAgaWYgKGhhc093blByb3BlcnR5KHZhbHVlLCBTdHJpbmcoaSkpKSB7XG4gICAgICBvdXRwdXQucHVzaChmb3JtYXRQcm9wZXJ0eShjdHgsIHZhbHVlLCByZWN1cnNlVGltZXMsIHZpc2libGVLZXlzLFxuICAgICAgICAgIFN0cmluZyhpKSwgdHJ1ZSkpO1xuICAgIH0gZWxzZSB7XG4gICAgICBvdXRwdXQucHVzaCgnJyk7XG4gICAgfVxuICB9XG4gIGtleXMuZm9yRWFjaChmdW5jdGlvbihrZXkpIHtcbiAgICBpZiAoIWtleS5tYXRjaCgvXlxcZCskLykpIHtcbiAgICAgIG91dHB1dC5wdXNoKGZvcm1hdFByb3BlcnR5KGN0eCwgdmFsdWUsIHJlY3Vyc2VUaW1lcywgdmlzaWJsZUtleXMsXG4gICAgICAgICAga2V5LCB0cnVlKSk7XG4gICAgfVxuICB9KTtcbiAgcmV0dXJuIG91dHB1dDtcbn1cblxuXG5mdW5jdGlvbiBmb3JtYXRQcm9wZXJ0eShjdHgsIHZhbHVlLCByZWN1cnNlVGltZXMsIHZpc2libGVLZXlzLCBrZXksIGFycmF5KSB7XG4gIHZhciBuYW1lLCBzdHIsIGRlc2M7XG4gIGRlc2MgPSBPYmplY3QuZ2V0T3duUHJvcGVydHlEZXNjcmlwdG9yKHZhbHVlLCBrZXkpIHx8IHsgdmFsdWU6IHZhbHVlW2tleV0gfTtcbiAgaWYgKGRlc2MuZ2V0KSB7XG4gICAgaWYgKGRlc2Muc2V0KSB7XG4gICAgICBzdHIgPSBjdHguc3R5bGl6ZSgnW0dldHRlci9TZXR0ZXJdJywgJ3NwZWNpYWwnKTtcbiAgICB9IGVsc2Uge1xuICAgICAgc3RyID0gY3R4LnN0eWxpemUoJ1tHZXR0ZXJdJywgJ3NwZWNpYWwnKTtcbiAgICB9XG4gIH0gZWxzZSB7XG4gICAgaWYgKGRlc2Muc2V0KSB7XG4gICAgICBzdHIgPSBjdHguc3R5bGl6ZSgnW1NldHRlcl0nLCAnc3BlY2lhbCcpO1xuICAgIH1cbiAgfVxuICBpZiAoIWhhc093blByb3BlcnR5KHZpc2libGVLZXlzLCBrZXkpKSB7XG4gICAgbmFtZSA9ICdbJyArIGtleSArICddJztcbiAgfVxuICBpZiAoIXN0cikge1xuICAgIGlmIChjdHguc2Vlbi5pbmRleE9mKGRlc2MudmFsdWUpIDwgMCkge1xuICAgICAgaWYgKGlzTnVsbChyZWN1cnNlVGltZXMpKSB7XG4gICAgICAgIHN0ciA9IGZvcm1hdFZhbHVlKGN0eCwgZGVzYy52YWx1ZSwgbnVsbCk7XG4gICAgICB9IGVsc2Uge1xuICAgICAgICBzdHIgPSBmb3JtYXRWYWx1ZShjdHgsIGRlc2MudmFsdWUsIHJlY3Vyc2VUaW1lcyAtIDEpO1xuICAgICAgfVxuICAgICAgaWYgKHN0ci5pbmRleE9mKCdcXG4nKSA+IC0xKSB7XG4gICAgICAgIGlmIChhcnJheSkge1xuICAgICAgICAgIHN0ciA9IHN0ci5zcGxpdCgnXFxuJykubWFwKGZ1bmN0aW9uKGxpbmUpIHtcbiAgICAgICAgICAgIHJldHVybiAnICAnICsgbGluZTtcbiAgICAgICAgICB9KS5qb2luKCdcXG4nKS5zdWJzdHIoMik7XG4gICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgc3RyID0gJ1xcbicgKyBzdHIuc3BsaXQoJ1xcbicpLm1hcChmdW5jdGlvbihsaW5lKSB7XG4gICAgICAgICAgICByZXR1cm4gJyAgICcgKyBsaW5lO1xuICAgICAgICAgIH0pLmpvaW4oJ1xcbicpO1xuICAgICAgICB9XG4gICAgICB9XG4gICAgfSBlbHNlIHtcbiAgICAgIHN0ciA9IGN0eC5zdHlsaXplKCdbQ2lyY3VsYXJdJywgJ3NwZWNpYWwnKTtcbiAgICB9XG4gIH1cbiAgaWYgKGlzVW5kZWZpbmVkKG5hbWUpKSB7XG4gICAgaWYgKGFycmF5ICYmIGtleS5tYXRjaCgvXlxcZCskLykpIHtcbiAgICAgIHJldHVybiBzdHI7XG4gICAgfVxuICAgIG5hbWUgPSBKU09OLnN0cmluZ2lmeSgnJyArIGtleSk7XG4gICAgaWYgKG5hbWUubWF0Y2goL15cIihbYS16QS1aX11bYS16QS1aXzAtOV0qKVwiJC8pKSB7XG4gICAgICBuYW1lID0gbmFtZS5zdWJzdHIoMSwgbmFtZS5sZW5ndGggLSAyKTtcbiAgICAgIG5hbWUgPSBjdHguc3R5bGl6ZShuYW1lLCAnbmFtZScpO1xuICAgIH0gZWxzZSB7XG4gICAgICBuYW1lID0gbmFtZS5yZXBsYWNlKC8nL2csIFwiXFxcXCdcIilcbiAgICAgICAgICAgICAgICAgLnJlcGxhY2UoL1xcXFxcIi9nLCAnXCInKVxuICAgICAgICAgICAgICAgICAucmVwbGFjZSgvKF5cInxcIiQpL2csIFwiJ1wiKTtcbiAgICAgIG5hbWUgPSBjdHguc3R5bGl6ZShuYW1lLCAnc3RyaW5nJyk7XG4gICAgfVxuICB9XG5cbiAgcmV0dXJuIG5hbWUgKyAnOiAnICsgc3RyO1xufVxuXG5cbmZ1bmN0aW9uIHJlZHVjZVRvU2luZ2xlU3RyaW5nKG91dHB1dCwgYmFzZSwgYnJhY2VzKSB7XG4gIHZhciBudW1MaW5lc0VzdCA9IDA7XG4gIHZhciBsZW5ndGggPSBvdXRwdXQucmVkdWNlKGZ1bmN0aW9uKHByZXYsIGN1cikge1xuICAgIG51bUxpbmVzRXN0Kys7XG4gICAgaWYgKGN1ci5pbmRleE9mKCdcXG4nKSA+PSAwKSBudW1MaW5lc0VzdCsrO1xuICAgIHJldHVybiBwcmV2ICsgY3VyLnJlcGxhY2UoL1xcdTAwMWJcXFtcXGRcXGQ/bS9nLCAnJykubGVuZ3RoICsgMTtcbiAgfSwgMCk7XG5cbiAgaWYgKGxlbmd0aCA+IDYwKSB7XG4gICAgcmV0dXJuIGJyYWNlc1swXSArXG4gICAgICAgICAgIChiYXNlID09PSAnJyA/ICcnIDogYmFzZSArICdcXG4gJykgK1xuICAgICAgICAgICAnICcgK1xuICAgICAgICAgICBvdXRwdXQuam9pbignLFxcbiAgJykgK1xuICAgICAgICAgICAnICcgK1xuICAgICAgICAgICBicmFjZXNbMV07XG4gIH1cblxuICByZXR1cm4gYnJhY2VzWzBdICsgYmFzZSArICcgJyArIG91dHB1dC5qb2luKCcsICcpICsgJyAnICsgYnJhY2VzWzFdO1xufVxuXG5cbi8vIE5PVEU6IFRoZXNlIHR5cGUgY2hlY2tpbmcgZnVuY3Rpb25zIGludGVudGlvbmFsbHkgZG9uJ3QgdXNlIGBpbnN0YW5jZW9mYFxuLy8gYmVjYXVzZSBpdCBpcyBmcmFnaWxlIGFuZCBjYW4gYmUgZWFzaWx5IGZha2VkIHdpdGggYE9iamVjdC5jcmVhdGUoKWAuXG5mdW5jdGlvbiBpc0FycmF5KGFyKSB7XG4gIHJldHVybiBBcnJheS5pc0FycmF5KGFyKTtcbn1cbmV4cG9ydHMuaXNBcnJheSA9IGlzQXJyYXk7XG5cbmZ1bmN0aW9uIGlzQm9vbGVhbihhcmcpIHtcbiAgcmV0dXJuIHR5cGVvZiBhcmcgPT09ICdib29sZWFuJztcbn1cbmV4cG9ydHMuaXNCb29sZWFuID0gaXNCb29sZWFuO1xuXG5mdW5jdGlvbiBpc051bGwoYXJnKSB7XG4gIHJldHVybiBhcmcgPT09IG51bGw7XG59XG5leHBvcnRzLmlzTnVsbCA9IGlzTnVsbDtcblxuZnVuY3Rpb24gaXNOdWxsT3JVbmRlZmluZWQoYXJnKSB7XG4gIHJldHVybiBhcmcgPT0gbnVsbDtcbn1cbmV4cG9ydHMuaXNOdWxsT3JVbmRlZmluZWQgPSBpc051bGxPclVuZGVmaW5lZDtcblxuZnVuY3Rpb24gaXNOdW1iZXIoYXJnKSB7XG4gIHJldHVybiB0eXBlb2YgYXJnID09PSAnbnVtYmVyJztcbn1cbmV4cG9ydHMuaXNOdW1iZXIgPSBpc051bWJlcjtcblxuZnVuY3Rpb24gaXNTdHJpbmcoYXJnKSB7XG4gIHJldHVybiB0eXBlb2YgYXJnID09PSAnc3RyaW5nJztcbn1cbmV4cG9ydHMuaXNTdHJpbmcgPSBpc1N0cmluZztcblxuZnVuY3Rpb24gaXNTeW1ib2woYXJnKSB7XG4gIHJldHVybiB0eXBlb2YgYXJnID09PSAnc3ltYm9sJztcbn1cbmV4cG9ydHMuaXNTeW1ib2wgPSBpc1N5bWJvbDtcblxuZnVuY3Rpb24gaXNVbmRlZmluZWQoYXJnKSB7XG4gIHJldHVybiBhcmcgPT09IHZvaWQgMDtcbn1cbmV4cG9ydHMuaXNVbmRlZmluZWQgPSBpc1VuZGVmaW5lZDtcblxuZnVuY3Rpb24gaXNSZWdFeHAocmUpIHtcbiAgcmV0dXJuIGlzT2JqZWN0KHJlKSAmJiBvYmplY3RUb1N0cmluZyhyZSkgPT09ICdbb2JqZWN0IFJlZ0V4cF0nO1xufVxuZXhwb3J0cy5pc1JlZ0V4cCA9IGlzUmVnRXhwO1xuXG5mdW5jdGlvbiBpc09iamVjdChhcmcpIHtcbiAgcmV0dXJuIHR5cGVvZiBhcmcgPT09ICdvYmplY3QnICYmIGFyZyAhPT0gbnVsbDtcbn1cbmV4cG9ydHMuaXNPYmplY3QgPSBpc09iamVjdDtcblxuZnVuY3Rpb24gaXNEYXRlKGQpIHtcbiAgcmV0dXJuIGlzT2JqZWN0KGQpICYmIG9iamVjdFRvU3RyaW5nKGQpID09PSAnW29iamVjdCBEYXRlXSc7XG59XG5leHBvcnRzLmlzRGF0ZSA9IGlzRGF0ZTtcblxuZnVuY3Rpb24gaXNFcnJvcihlKSB7XG4gIHJldHVybiBpc09iamVjdChlKSAmJlxuICAgICAgKG9iamVjdFRvU3RyaW5nKGUpID09PSAnW29iamVjdCBFcnJvcl0nIHx8IGUgaW5zdGFuY2VvZiBFcnJvcik7XG59XG5leHBvcnRzLmlzRXJyb3IgPSBpc0Vycm9yO1xuXG5mdW5jdGlvbiBpc0Z1bmN0aW9uKGFyZykge1xuICByZXR1cm4gdHlwZW9mIGFyZyA9PT0gJ2Z1bmN0aW9uJztcbn1cbmV4cG9ydHMuaXNGdW5jdGlvbiA9IGlzRnVuY3Rpb247XG5cbmZ1bmN0aW9uIGlzUHJpbWl0aXZlKGFyZykge1xuICByZXR1cm4gYXJnID09PSBudWxsIHx8XG4gICAgICAgICB0eXBlb2YgYXJnID09PSAnYm9vbGVhbicgfHxcbiAgICAgICAgIHR5cGVvZiBhcmcgPT09ICdudW1iZXInIHx8XG4gICAgICAgICB0eXBlb2YgYXJnID09PSAnc3RyaW5nJyB8fFxuICAgICAgICAgdHlwZW9mIGFyZyA9PT0gJ3N5bWJvbCcgfHwgIC8vIEVTNiBzeW1ib2xcbiAgICAgICAgIHR5cGVvZiBhcmcgPT09ICd1bmRlZmluZWQnO1xufVxuZXhwb3J0cy5pc1ByaW1pdGl2ZSA9IGlzUHJpbWl0aXZlO1xuXG5leHBvcnRzLmlzQnVmZmVyID0gcmVxdWlyZSgnLi9zdXBwb3J0L2lzQnVmZmVyJyk7XG5cbmZ1bmN0aW9uIG9iamVjdFRvU3RyaW5nKG8pIHtcbiAgcmV0dXJuIE9iamVjdC5wcm90b3R5cGUudG9TdHJpbmcuY2FsbChvKTtcbn1cblxuXG5mdW5jdGlvbiBwYWQobikge1xuICByZXR1cm4gbiA8IDEwID8gJzAnICsgbi50b1N0cmluZygxMCkgOiBuLnRvU3RyaW5nKDEwKTtcbn1cblxuXG52YXIgbW9udGhzID0gWydKYW4nLCAnRmViJywgJ01hcicsICdBcHInLCAnTWF5JywgJ0p1bicsICdKdWwnLCAnQXVnJywgJ1NlcCcsXG4gICAgICAgICAgICAgICdPY3QnLCAnTm92JywgJ0RlYyddO1xuXG4vLyAyNiBGZWIgMTY6MTk6MzRcbmZ1bmN0aW9uIHRpbWVzdGFtcCgpIHtcbiAgdmFyIGQgPSBuZXcgRGF0ZSgpO1xuICB2YXIgdGltZSA9IFtwYWQoZC5nZXRIb3VycygpKSxcbiAgICAgICAgICAgICAgcGFkKGQuZ2V0TWludXRlcygpKSxcbiAgICAgICAgICAgICAgcGFkKGQuZ2V0U2Vjb25kcygpKV0uam9pbignOicpO1xuICByZXR1cm4gW2QuZ2V0RGF0ZSgpLCBtb250aHNbZC5nZXRNb250aCgpXSwgdGltZV0uam9pbignICcpO1xufVxuXG5cbi8vIGxvZyBpcyBqdXN0IGEgdGhpbiB3cmFwcGVyIHRvIGNvbnNvbGUubG9nIHRoYXQgcHJlcGVuZHMgYSB0aW1lc3RhbXBcbmV4cG9ydHMubG9nID0gZnVuY3Rpb24oKSB7XG4gIGNvbnNvbGUubG9nKCclcyAtICVzJywgdGltZXN0YW1wKCksIGV4cG9ydHMuZm9ybWF0LmFwcGx5KGV4cG9ydHMsIGFyZ3VtZW50cykpO1xufTtcblxuXG4vKipcbiAqIEluaGVyaXQgdGhlIHByb3RvdHlwZSBtZXRob2RzIGZyb20gb25lIGNvbnN0cnVjdG9yIGludG8gYW5vdGhlci5cbiAqXG4gKiBUaGUgRnVuY3Rpb24ucHJvdG90eXBlLmluaGVyaXRzIGZyb20gbGFuZy5qcyByZXdyaXR0ZW4gYXMgYSBzdGFuZGFsb25lXG4gKiBmdW5jdGlvbiAobm90IG9uIEZ1bmN0aW9uLnByb3RvdHlwZSkuIE5PVEU6IElmIHRoaXMgZmlsZSBpcyB0byBiZSBsb2FkZWRcbiAqIGR1cmluZyBib290c3RyYXBwaW5nIHRoaXMgZnVuY3Rpb24gbmVlZHMgdG8gYmUgcmV3cml0dGVuIHVzaW5nIHNvbWUgbmF0aXZlXG4gKiBmdW5jdGlvbnMgYXMgcHJvdG90eXBlIHNldHVwIHVzaW5nIG5vcm1hbCBKYXZhU2NyaXB0IGRvZXMgbm90IHdvcmsgYXNcbiAqIGV4cGVjdGVkIGR1cmluZyBib290c3RyYXBwaW5nIChzZWUgbWlycm9yLmpzIGluIHIxMTQ5MDMpLlxuICpcbiAqIEBwYXJhbSB7ZnVuY3Rpb259IGN0b3IgQ29uc3RydWN0b3IgZnVuY3Rpb24gd2hpY2ggbmVlZHMgdG8gaW5oZXJpdCB0aGVcbiAqICAgICBwcm90b3R5cGUuXG4gKiBAcGFyYW0ge2Z1bmN0aW9ufSBzdXBlckN0b3IgQ29uc3RydWN0b3IgZnVuY3Rpb24gdG8gaW5oZXJpdCBwcm90b3R5cGUgZnJvbS5cbiAqL1xuZXhwb3J0cy5pbmhlcml0cyA9IHJlcXVpcmUoJ2luaGVyaXRzJyk7XG5cbmV4cG9ydHMuX2V4dGVuZCA9IGZ1bmN0aW9uKG9yaWdpbiwgYWRkKSB7XG4gIC8vIERvbid0IGRvIGFueXRoaW5nIGlmIGFkZCBpc24ndCBhbiBvYmplY3RcbiAgaWYgKCFhZGQgfHwgIWlzT2JqZWN0KGFkZCkpIHJldHVybiBvcmlnaW47XG5cbiAgdmFyIGtleXMgPSBPYmplY3Qua2V5cyhhZGQpO1xuICB2YXIgaSA9IGtleXMubGVuZ3RoO1xuICB3aGlsZSAoaS0tKSB7XG4gICAgb3JpZ2luW2tleXNbaV1dID0gYWRkW2tleXNbaV1dO1xuICB9XG4gIHJldHVybiBvcmlnaW47XG59O1xuXG5mdW5jdGlvbiBoYXNPd25Qcm9wZXJ0eShvYmosIHByb3ApIHtcbiAgcmV0dXJuIE9iamVjdC5wcm90b3R5cGUuaGFzT3duUHJvcGVydHkuY2FsbChvYmosIHByb3ApO1xufVxuIl19
