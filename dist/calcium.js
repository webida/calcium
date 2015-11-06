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
                while (!currBlock.isOldFunctionBlock() && !currBlock.isArrowFunctionBlock() && !currBlock.isGlobal()) {
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
        var someHasDefaults = node.params.some(function (ptn) {
            return myWalker.patternHasDefaults(ptn);
        });
        if (someHasDefaults) {
            paramBlock = parenBlock = new VarBlock(parenBlock, node, VarBlock.blockTypes.parameterBlock, currBlock.isStrict);
            node['@block'] = paramBlock;
        }
        var strictInner = currBlock.isStrict || node.body.body && node.body.body[0] && isUseStrict(node.body.body[0]);
        var funcBlock = new VarBlock(parenBlock, node, // same originNode with paramBlock, intended.
        node.type === 'ArrowFunctionExpression' ? VarBlock.blockTypes.arrowFunctionBlock : VarBlock.blockTypes.oldFunctionBlock, strictInner);
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
            if (varName === 'arguments' && block.isOldFunctionBlock()) {
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
        // Since we are looking for variable usage, we don't need to look at formal parameters.
        if (node.id) c(node.id, currBlock);
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
//# sourceMappingURL=data:application/json;charset:utf-8;base64,eyJ2ZXJzaW9uIjozLCJzb3VyY2VzIjpbIm5vZGVfbW9kdWxlcy9icm93c2VyaWZ5L25vZGVfbW9kdWxlcy9icm93c2VyLXBhY2svX3ByZWx1ZGUuanMiLCIvaG9tZS9zd2tpbS9XZWJzdG9ybVByb2plY3RzL2NhbGNpdW0vZGVmYXVsdE9wdGlvbi5qcyIsIi9ob21lL3N3a2ltL1dlYnN0b3JtUHJvamVjdHMvY2FsY2l1bS9saWIvY29uc3RyYWludC9jR2VuLmpzIiwiL2hvbWUvc3draW0vV2Vic3Rvcm1Qcm9qZWN0cy9jYWxjaXVtL2xpYi9jb25zdHJhaW50L2NvbnN0cmFpbnRzLmpzIiwiL2hvbWUvc3draW0vV2Vic3Rvcm1Qcm9qZWN0cy9jYWxjaXVtL2xpYi9kb21haW5zL2NvbnRleHQuanMiLCIvaG9tZS9zd2tpbS9XZWJzdG9ybVByb2plY3RzL2NhbGNpdW0vbGliL2RvbWFpbnMvc3RhdHVzLmpzIiwiL2hvbWUvc3draW0vV2Vic3Rvcm1Qcm9qZWN0cy9jYWxjaXVtL2xpYi9kb21haW5zL3R5cGVzLmpzIiwiL2hvbWUvc3draW0vV2Vic3Rvcm1Qcm9qZWN0cy9jYWxjaXVtL2xpYi9nZXRUeXBlRGF0YS5qcyIsIi9ob21lL3N3a2ltL1dlYnN0b3JtUHJvamVjdHMvY2FsY2l1bS9saWIvaGVscGVyLmpzIiwiL2hvbWUvc3draW0vV2Vic3Rvcm1Qcm9qZWN0cy9jYWxjaXVtL2xpYi9pbmZlci5qcyIsIi9ob21lL3N3a2ltL1dlYnN0b3JtUHJvamVjdHMvY2FsY2l1bS9saWIvcmV0T2NjdXIuanMiLCIvaG9tZS9zd2tpbS9XZWJzdG9ybVByb2plY3RzL2NhbGNpdW0vbGliL3RoaXNPY2N1ci5qcyIsIi9ob21lL3N3a2ltL1dlYnN0b3JtUHJvamVjdHMvY2FsY2l1bS9saWIvdXRpbC9teVdhbGtlci5qcyIsIi9ob21lL3N3a2ltL1dlYnN0b3JtUHJvamVjdHMvY2FsY2l1bS9saWIvdmFyQmxvY2suanMiLCIvaG9tZS9zd2tpbS9XZWJzdG9ybVByb2plY3RzL2NhbGNpdW0vbGliL3ZhcnJlZnMuanMiLCJub2RlX21vZHVsZXMvYWNvcm4vZGlzdC9hY29ybi5qcyIsIm5vZGVfbW9kdWxlcy9hY29ybi9kaXN0L2Fjb3JuX2xvb3NlLmpzIiwibm9kZV9tb2R1bGVzL2Fjb3JuL2Rpc3Qvd2Fsay5qcyIsIm5vZGVfbW9kdWxlcy9icm93c2VyaWZ5L25vZGVfbW9kdWxlcy9pbmhlcml0cy9pbmhlcml0c19icm93c2VyLmpzIiwibm9kZV9tb2R1bGVzL2Jyb3dzZXJpZnkvbm9kZV9tb2R1bGVzL3Byb2Nlc3MvYnJvd3Nlci5qcyIsIm5vZGVfbW9kdWxlcy9icm93c2VyaWZ5L25vZGVfbW9kdWxlcy91dGlsL3N1cHBvcnQvaXNCdWZmZXJCcm93c2VyLmpzIiwibm9kZV9tb2R1bGVzL2Jyb3dzZXJpZnkvbm9kZV9tb2R1bGVzL3V0aWwvdXRpbC5qcyJdLCJuYW1lcyI6W10sIm1hcHBpbmdzIjoiQUFBQTs7OztBQ0FPLElBQU0sT0FBTyxHQUFHO0FBQ25CLGVBQVcsRUFBRTtBQUNULG1CQUFXLEVBQUUsQ0FBQzs7Ozs7QUFLZCxrQkFBVSxFQUFFLFFBQVE7S0FDdkI7Ozs7QUFJRCxtQkFBZSxFQUFFLElBQUk7OztBQUdyQix3QkFBb0IsRUFBRTtBQUNsQixpQkFBUyxFQUFFLENBQUM7QUFDWiwyQkFBbUIsRUFBRSw2QkFBVSxFQUFFLEVBQUU7QUFDL0IsbUJBQU8sQ0FBQyxDQUFDO1NBQ1o7S0FDSjtDQUNKLENBQUM7Ozs7QUNyQkYsWUFBWSxDQUFDOzs7OzRCQUVVLGtCQUFrQjs7SUFBN0IsS0FBSzs7NEJBQ1Msa0JBQWtCOztJQUFoQyxRQUFROzs4QkFDQyxvQkFBb0I7O0lBQTdCLEdBQUc7O0FBQ2YsSUFBTSxJQUFJLEdBQUcsT0FBTyxDQUFDLGlCQUFpQixDQUFDLENBQUM7QUFDeEMsSUFBTSxNQUFNLEdBQUcsT0FBTyxDQUFDLG1CQUFtQixDQUFDLENBQUM7QUFDNUMsSUFBTSxJQUFJLEdBQUcsT0FBTyxDQUFDLGVBQWUsQ0FBQyxDQUFDOzs7QUFHdEMsU0FBUyxVQUFVLENBQUMsSUFBSSxFQUFFO0FBQ3RC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QUFDdEIsWUFBSSxFQUFFLEVBQUUsRUFBRSxDQUFDLE9BQU8sQ0FBQyxVQUFBLENBQUM7bUJBQUksR0FBRyxDQUFDLEdBQUcsQ0FBQyxDQUFDLENBQUM7U0FBQSxDQUFDLENBQUM7QUFDcEMsWUFBSSxFQUFFLEVBQUUsRUFBRSxDQUFDLE9BQU8sQ0FBQyxVQUFBLENBQUM7bUJBQUksR0FBRyxDQUFDLEdBQUcsQ0FBQyxDQUFDLENBQUM7U0FBQSxDQUFDLENBQUM7QUFDcEMsZUFBTyxHQUFHLENBQUM7S0FDZDs7QUFFRCxRQUFJLEVBQUUsRUFBRSxFQUFFLENBQUMsT0FBTyxDQUFDLFVBQUMsRUFBRSxFQUFFLENBQUM7ZUFBSyxHQUFHLENBQUMsR0FBRyxDQUFDLENBQUMsRUFBRSxFQUFFLENBQUM7S0FBQSxDQUFDLENBQUM7QUFDOUMsUUFBSSxFQUFFLEVBQUUsRUFBRSxDQUFDLE9BQU8sQ0FBQyxVQUFDLEVBQUUsRUFBRSxDQUFDO2VBQUssR0FBRyxDQUFDLEdBQUcsQ0FBQyxDQUFDLEVBQUUsUUFBUSxDQUFDLEdBQUcsQ0FBQyxHQUFHLENBQUMsQ0FBQyxDQUFDLEVBQUUsRUFBRSxDQUFDLEdBQUcsQ0FBQyxDQUFDLENBQUMsQ0FBQyxDQUFDO0tBQUEsQ0FBQyxDQUFDO0FBQzNFLFdBQU8sR0FBRyxDQUFDO0NBQ2Q7O0FBRUQsU0FBUyxzQkFBc0IsQ0FBQyxFQUFFLEVBQUUsRUFBRSxFQUFFO0FBQ3BDLFFBQU0sR0FBRyxHQUFHLElBQUksR0FBRyxFQUFFLENBQUM7QUFDdEIsTUFBRSxDQUFDLE9BQU8sQ0FBQyxVQUFDLEVBQUUsRUFBRSxDQUFDO2VBQUssR0FBRyxDQUFDLEdBQUcsQ0FBQyxDQUFDLEVBQUUsRUFBRSxDQUFDO0tBQUEsQ0FBQyxDQUFDO0FBQ3RDLE1BQUUsQ0FBQyxPQUFPLENBQUMsVUFBQyxFQUFFLEVBQUUsQ0FBQyxFQUFLO0FBQ2xCLFlBQUksQ0FBQyxHQUFHLENBQUMsR0FBRyxDQUFDLENBQUMsQ0FBQyxFQUFFLEdBQUcsQ0FBQyxHQUFHLENBQUMsQ0FBQyxFQUFFLEVBQUUsQ0FBQyxDQUFBO0tBQ2xDLENBQUMsQ0FBQztBQUNILFdBQU8sR0FBRyxDQUFDO0NBQ2Q7Ozs7QUFJRCxTQUFTLFVBQVUsQ0FBQyxHQUFHLEVBQUU7QUFDckIsUUFBSSxNQUFNLEdBQUcsSUFBSSxHQUFHLEVBQUUsQ0FBQztBQUN2QixPQUFHLENBQUMsT0FBTyxDQUFDLFVBQUMsRUFBRSxFQUFFLENBQUMsRUFBSztBQUNuQixjQUFNLENBQUMsR0FBRyxDQUFDLENBQUMsRUFBRSxFQUFFLENBQUMsUUFBUSxFQUFFLENBQUMsQ0FBQztLQUNoQyxDQUFDLENBQUM7QUFDSCxXQUFPLE1BQU0sQ0FBQztDQUNqQjs7O0FBR0QsU0FBUyxrQkFBa0IsQ0FBQyxHQUFHLEVBQUU7O0FBRTdCLFFBQU0sWUFBWSxHQUFHLEVBQUUsQ0FBQzs7QUFFeEIsYUFBUyxRQUFRLENBQUMsSUFBSSxFQUFFO0FBQ3BCLFlBQUksSUFBSSxZQUFZLEtBQUssQ0FBQyxPQUFPLElBQzdCLElBQUksQ0FBQyxPQUFPLENBQUMsV0FBVyxFQUFFLElBQUksQ0FBQyxFQUFFOztBQUNqQyxvQkFBSSxRQUFRLEdBQUcsSUFBSSxHQUFHLEVBQUUsQ0FBQztBQUN6QixvQkFBTSxVQUFVLEdBQUcsSUFBSSxDQUFDLE9BQU8sQ0FBQyxXQUFXLEVBQUUsSUFBSSxDQUFDLENBQUMsUUFBUSxFQUFFLENBQUM7O0FBRTlELDBCQUFVLENBQUMsT0FBTyxDQUFDLFVBQUEsRUFBRSxFQUFJO0FBQ3JCLHdCQUFJLFlBQVksQ0FBQyxPQUFPLENBQUMsRUFBRSxDQUFDLEdBQUcsQ0FBQyxDQUFDLEVBQUU7QUFDL0IsK0JBQU87cUJBQ1Y7QUFDRCxnQ0FBWSxDQUFDLElBQUksQ0FBQyxFQUFFLENBQUMsQ0FBQztBQUN0Qiw0QkFBUSxHQUFHLFFBQVEsQ0FBQyxRQUFRLEVBQUUsUUFBUSxDQUFDLEVBQUUsQ0FBQyxDQUFDLENBQUM7QUFDNUMsZ0NBQVksQ0FBQyxHQUFHLEVBQUUsQ0FBQztpQkFDdEIsQ0FBQyxDQUFDO0FBQ0g7dUJBQU8sc0JBQXNCLENBQUMsVUFBVSxDQUFDLElBQUksQ0FBQyxLQUFLLENBQUMsRUFBRSxRQUFRLENBQUM7a0JBQUM7Ozs7U0FDbkUsTUFBTTtBQUNILG1CQUFPLElBQUksR0FBRyxFQUFFLENBQUM7U0FDcEI7S0FDSjs7QUFFRCxRQUFJLE1BQU0sR0FBRyxJQUFJLEdBQUcsRUFBRSxDQUFDO0FBQ3ZCLE9BQUcsQ0FBQyxRQUFRLEVBQUUsQ0FBQyxPQUFPLENBQUMsVUFBQSxFQUFFLEVBQUk7QUFDekIsY0FBTSxHQUFHLFFBQVEsQ0FBQyxNQUFNLEVBQUUsUUFBUSxDQUFDLEVBQUUsQ0FBQyxDQUFDLENBQUE7S0FDMUMsQ0FBQyxDQUFDOztBQUVILFdBQU8sTUFBTSxDQUFDO0NBQ2pCOztBQUVNLFNBQVMsb0JBQW9CLENBQUMsR0FBRyxFQUFFLENBQUMsRUFBRSxHQUFHLEVBQUU7QUFDOUMsUUFBTSxJQUFJLEdBQUcsUUFBUSxDQUFDLG1CQUFtQixDQUFDLEdBQUcsRUFBRSxHQUFHLEVBQUUsR0FBRyxDQUFDLENBQUM7QUFDekQsUUFBTSxTQUFTLEdBQUcsQ0FBQyxDQUFDLGtCQUFrQixDQUFDLElBQUksQ0FBQyxDQUFDOztBQUU3QyxRQUFNLE1BQU0sR0FBRyxFQUFFLENBQUM7QUFDbEIsUUFBSSxTQUFTLEtBQUssSUFBSSxFQUFFO0FBQ3BCLGVBQU8sTUFBTSxDQUFDO0tBQ2pCO0FBQ0QsYUFBUyxDQUFDLFFBQVEsRUFBRSxDQUFDLE9BQU8sQ0FBQyxVQUFVLEVBQUUsRUFBRTtBQUN2QyxZQUFJLEVBQUUsWUFBWSxLQUFLLENBQUMsTUFBTSxJQUFJLEVBQUUsQ0FBQyxVQUFVLEVBQUU7QUFDN0MsZ0JBQU0sTUFBTSxHQUFHLEVBQUUsQ0FBQyxVQUFVLENBQUM7QUFDN0IsZ0JBQUksRUFBRSxZQUFBLENBQUM7QUFDUCxvQkFBUSxNQUFNLENBQUMsSUFBSTtBQUNmLHFCQUFLLG9CQUFvQjtBQUFHLHNCQUFFLEdBQUcsTUFBTSxDQUFDLEtBQUssQ0FBQyxBQUFDLE1BQU07QUFBQSxBQUNyRCxxQkFBSyxxQkFBcUI7QUFBRyxzQkFBRSxHQUFHLE1BQU0sQ0FBQyxFQUFFLENBQUMsS0FBSyxDQUFDLEFBQUMsTUFBTTtBQUFBLGFBQzVEO0FBQ0QsZ0JBQU0sSUFBSSxHQUFHLEVBQUMsS0FBSyxFQUFFLE1BQU0sQ0FBQyxLQUFLLEVBQUUsR0FBRyxFQUFFLE1BQU0sQ0FBQyxHQUFHLEVBQUUsRUFBRSxFQUFFLEVBQUUsRUFBQyxDQUFDO0FBQzVELGtCQUFNLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQyxDQUFDO1NBQ3JCO0tBQ0osQ0FBQyxDQUFDO0FBQ0gsV0FBTyxNQUFNLENBQUM7Q0FDakI7OztBQUdELFNBQVMsaUJBQWlCLENBQUMsRUFBRSxFQUFFO0FBQzNCLFFBQUksTUFBTSxHQUFHLEVBQUUsQ0FBQztBQUNoQixRQUFJLE1BQU0sR0FBRyxJQUFJLEdBQUcsRUFBRSxDQUFDO0FBQ3ZCLFdBQU8sTUFBTSxLQUFLLElBQUksRUFBRTtBQUNwQixZQUFJLFNBQVMsR0FBRyxJQUFJLEdBQUcsRUFBRSxDQUFDO0FBQzFCLDhCQUFtQixNQUFNLENBQUMsU0FBUyxDQUFDLE1BQU0sRUFBRSx5SEFBRTs7Ozs7Ozs7Ozs7O2dCQUFyQyxNQUFNOztBQUNYLHFCQUFTLEdBQUcsUUFBUSxDQUFDLFNBQVMsRUFBRSxVQUFVLENBQUMsTUFBTSxDQUFDLENBQUMsQ0FBQztTQUN2RDtBQUNELGNBQU0sR0FBRyxzQkFBc0IsQ0FBQyxNQUFNLEVBQUUsU0FBUyxDQUFDLENBQUM7QUFDbkQsY0FBTSxHQUFHLE1BQU0sQ0FBQyxLQUFLLENBQUM7S0FDekI7QUFDRCxXQUFPLE1BQU0sQ0FBQztDQUNqQjs7Ozs7QUNqUkQsSUFBSSxJQUFJLEdBQUcsT0FBTyxDQUFDLE1BQU0sQ0FBQyxDQUFDOztBQUUzQixTQUFTLFdBQVcsQ0FBQyxHQUFHLEVBQUUsUUFBUSxFQUFFO0FBQ2hDLFFBQUksUUFBUSxHQUFHLEVBQUUsQ0FBQzs7QUFFbEIsUUFBSSxHQUFHLEdBQUcsUUFBUSxLQUFLLFNBQVMsR0FBRyxDQUFDLEdBQUcsUUFBUSxDQUFDOztBQUVoRCxhQUFTLFFBQVEsQ0FBQyxJQUFJLEVBQUU7QUFDcEIsWUFBSSxDQUFDLFFBQVEsQ0FBQyxHQUFHLEdBQUcsQ0FBQztBQUNyQixnQkFBUSxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsQ0FBQztBQUNwQixXQUFHLEVBQUUsQ0FBQztLQUNUOzs7QUFHRCxhQUFTLGlCQUFpQixDQUFDLElBQUksRUFBRTtBQUM3QixZQUFJLElBQUksSUFBSSxJQUFJLENBQUMsY0FBYyxDQUFDLE1BQU0sQ0FBQyxFQUFFO0FBQ3JDLG9CQUFRLENBQUMsSUFBSSxDQUFDLENBQUM7U0FDbEI7QUFDRCxZQUFJLElBQUksSUFBSSxPQUFPLElBQUksS0FBSyxRQUFRLEVBQUU7QUFDbEMsaUJBQUssSUFBSSxDQUFDLElBQUksSUFBSSxFQUFFO0FBQ2hCLGlDQUFpQixDQUFDLElBQUksQ0FBQyxDQUFDLENBQUMsQ0FBQyxDQUFDO2FBQzlCO1NBQ0o7S0FDSjs7QUFFRCxxQkFBaUIsQ0FBQyxHQUFHLENBQUMsQ0FBQzs7QUFFdkIsV0FBTyxRQUFRLENBQUM7Q0FDbkI7O0FBRUQsU0FBUyxZQUFZLENBQUMsR0FBRyxFQUFFO0FBQ3ZCLFdBQU8sQ0FBQyxHQUFHLENBQUMsSUFBSSxDQUFDLE9BQU8sQ0FBQyxHQUFHLEVBQUUsRUFBQyxLQUFLLEVBQUUsSUFBSSxFQUFDLENBQUMsQ0FBQyxDQUFDO0NBQ2pEOztBQUVELE9BQU8sQ0FBQyxXQUFXLEdBQUcsV0FBVyxDQUFDO0FBQ2xDLE9BQU8sQ0FBQyxZQUFZLEdBQUcsWUFBWSxDQUFDOzs7Ozs7Ozs0QkMvQmIsaUJBQWlCOztJQUE1QixLQUFLOzs4QkFDUSxtQkFBbUI7O0lBQWhDLE9BQU87Ozs7NkJBRUssa0JBQWtCOztJQUE5QixNQUFNOzt3QkFDUSxZQUFZOztJQUExQixRQUFROzs0QkFLTSxpQkFBaUI7O0lBQS9CLFFBQVE7OzJCQUNTLGVBQWU7O0lBQWhDLFdBQVc7OzZCQUNRLGtCQUFrQjs7SUFBckMsYUFBYTs7QUFkekIsSUFBTSxLQUFLLEdBQUcsT0FBTyxDQUFDLGtCQUFrQixDQUFDLENBQUM7QUFDMUMsSUFBTSxXQUFXLEdBQUcsT0FBTyxDQUFDLHdCQUF3QixDQUFDLENBQUM7QUFDdEQsSUFBTSxHQUFHLEdBQUcsT0FBTyxDQUFDLFVBQVUsQ0FBQyxDQUFDOztBQU1oQyxJQUFNLElBQUksR0FBRyxPQUFPLENBQUMsbUJBQW1CLENBQUMsQ0FBQztBQUMxQyxJQUFNLE9BQU8sR0FBRyxPQUFPLENBQUMsV0FBVyxDQUFDLENBQUM7QUFDckMsSUFBTSxRQUFRLEdBQUcsT0FBTyxDQUFDLFlBQVksQ0FBQyxDQUFDO0FBQ3ZDLElBQU0sU0FBUyxHQUFHLE9BQU8sQ0FBQyxhQUFhLENBQUMsQ0FBQzs7QUFLekMsU0FBUyxPQUFPLENBQUMsS0FBSyxFQUFFLE1BQU0sRUFBRSxNQUFNLEVBQUU7Ozs7QUFJcEMsUUFBSSxNQUFNLEtBQUssU0FBUyxFQUFFOztBQUV0QixjQUFNLEdBQUcsYUFBYSxDQUFDLE9BQU8sQ0FBQztLQUNsQzs7QUFFRCxRQUFJLEdBQUcsQ0FBQztBQUNSLFFBQUk7QUFDQSxXQUFHLEdBQUcsS0FBSyxDQUFDLEtBQUssQ0FBQyxLQUFLLEVBQUUsTUFBTSxDQUFDLFdBQVcsQ0FBQyxDQUFDO0tBQ2hELENBQUMsT0FBTyxDQUFDLEVBQUU7QUFDUixXQUFHLEdBQUcsV0FBVyxDQUFDLFlBQVksQ0FBQyxLQUFLLEVBQUUsTUFBTSxDQUFDLFdBQVcsQ0FBQyxDQUFDO0tBQzdEOztBQUVELFFBQUksc0JBQXNCLEdBQUcsR0FBRyxDQUFDLFdBQVcsQ0FBQyxHQUFHLENBQUMsQ0FBQzs7Ozs7QUFLbEQsUUFBSSxTQUFTLEdBQUcsSUFBSSxRQUFRLENBQUMsUUFBUSxDQUNqQyxJQUFJLEVBQ0osR0FBRyxFQUNILFFBQVEsQ0FBQyxRQUFRLENBQUMsVUFBVSxDQUFDLFdBQVc7O0FBRXhDLFVBQU0sQ0FBQyxXQUFXLENBQUMsVUFBVSxLQUFLLFFBQVEsQ0FDN0MsQ0FBQzs7QUFFRixZQUFRLENBQUMsaUJBQWlCLENBQUMsR0FBRyxFQUFFLFNBQVMsQ0FBQyxDQUFDOzs7O0FBSTNDLFdBQU8sQ0FBQywwQkFBMEIsQ0FBQyxNQUFNLENBQUMsb0JBQW9CLENBQUMsQ0FBQzs7QUFFaEUsUUFBSSxNQUFNLEdBQUcsR0FBRyxDQUFDLFFBQVEsQ0FBQyxDQUFDO0FBQzNCLFFBQUksY0FBYyxHQUFHLE9BQU8sQ0FBQyxlQUFlLENBQUMsY0FBYyxDQUFDO0FBQzVELFFBQUksTUFBTSxHQUFHLE1BQU0sQ0FBQyxnQkFBZ0IsQ0FBQyxJQUFJLEVBQUUsY0FBYyxDQUFDLENBQUM7QUFDM0QsUUFBSSxPQUFPLEdBQUcsS0FBSyxDQUFDLG9CQUFvQixDQUFDLE1BQU0sQ0FBQyxDQUFDO0FBQ2pELFFBQUksVUFBVSxHQUFHLElBQUksTUFBTSxDQUFDLE1BQU0sQ0FDOUIsSUFBSSxLQUFLLENBQUMsSUFBSSxDQUFDLE9BQU8sQ0FBQyxFQUN2QixLQUFLLENBQUMsUUFBUSxFQUNkLEtBQUssQ0FBQyxRQUFRLEVBQ2QsY0FBYyxFQUNkLE1BQU0sQ0FBQyxDQUFDOztBQUVaLFFBQUksUUFBUSxHQUFHLElBQUksS0FBSyxDQUFDLE9BQU8sQ0FBQyxJQUFJLEVBQUUsa0JBQWtCLENBQUMsQ0FBQztBQUMzRCxRQUFJLElBQUksR0FBRztBQUNQLG9CQUFZLEVBQUUsT0FBTzs7QUFFckIsY0FBTSxFQUFFO0FBQ0osa0JBQU0sRUFBRSxRQUFRO0FBQ2hCLG9CQUFRLEVBQUUsSUFBSSxLQUFLLENBQUMsT0FBTyxDQUFDLElBQUksS0FBSyxDQUFDLElBQUksQ0FBQyxRQUFRLENBQUMsRUFBRSxvQkFBb0IsQ0FBQztBQUMzRSxpQkFBSyxFQUFFLElBQUksS0FBSyxDQUFDLE9BQU8sQ0FBQyxJQUFJLEtBQUssQ0FBQyxJQUFJLENBQUMsUUFBUSxDQUFDLEVBQUUsaUJBQWlCLENBQUM7QUFDckUsa0JBQU0sRUFBRSxJQUFJLEtBQUssQ0FBQyxPQUFPLENBQUMsSUFBSSxLQUFLLENBQUMsSUFBSSxDQUFDLFFBQVEsQ0FBQyxFQUFFLGtCQUFrQixDQUFDO0FBQ3ZFLGtCQUFNLEVBQUUsSUFBSSxLQUFLLENBQUMsT0FBTyxDQUFDLElBQUksS0FBSyxDQUFDLElBQUksQ0FBQyxRQUFRLENBQUMsRUFBRSxrQkFBa0IsQ0FBQztBQUN2RSxrQkFBTSxFQUFFLElBQUksS0FBSyxDQUFDLE9BQU8sQ0FBQyxJQUFJLEtBQUssQ0FBQyxJQUFJLENBQUMsUUFBUSxDQUFDLEVBQUUsa0JBQWtCLENBQUM7QUFDdkUsbUJBQU8sRUFBRSxJQUFJLEtBQUssQ0FBQyxPQUFPLENBQUMsSUFBSSxLQUFLLENBQUMsSUFBSSxDQUFDLFFBQVEsQ0FBQyxFQUFFLG1CQUFtQixDQUFDO1NBQzVFO0FBQ0QsU0FBQyxFQUFFLElBQUksS0FBSyxDQUFDLFFBQVEsRUFBRTtBQUN2QixjQUFNLEVBQUUsTUFBTTtLQUNqQixDQUFDO0FBQ0YsUUFBSSxDQUFDLGNBQWMsQ0FBQyxHQUFHLEVBQUUsVUFBVSxFQUFFLElBQUksQ0FBQyxDQUFDOzs7OztBQUszQyxRQUFJLE1BQU0sRUFBRTtBQUNSLGVBQU87QUFDSCxtQkFBTyxFQUFFLE9BQU87QUFDaEIsZUFBRyxFQUFFLEdBQUc7QUFDUixrQkFBTSxFQUFFLE1BQU07QUFDZCxrQkFBTSxFQUFFLE1BQU07QUFDZCxhQUFDLEVBQUUsSUFBSSxDQUFDLENBQUM7U0FDWixDQUFDO0tBQ0wsTUFBTTtBQUNILGVBQU8sT0FBTyxDQUFDO0tBQ2xCO0NBQ0o7O0FBRUQsT0FBTyxDQUFDLE9BQU8sR0FBRyxPQUFPLENBQUM7QUFDMUIsT0FBTyxDQUFDLGdCQUFnQixHQUFHLFFBQVEsQ0FBQyxnQkFBZ0IsQ0FBQztBQUNyRCxPQUFPLENBQUMsYUFBYSxHQUFHLE9BQU8sQ0FBQyxhQUFhLENBQUM7QUFDOUMsT0FBTyxDQUFDLG1CQUFtQixHQUFHLFFBQVEsQ0FBQyxtQkFBbUIsQ0FBQztBQUMzRCxPQUFPLENBQUMsc0JBQXNCLEdBQUcsUUFBUSxDQUFDLHNCQUFzQixDQUFDO0FBQ2pFLE9BQU8sQ0FBQyxhQUFhLEdBQUcsU0FBUyxDQUFDLGFBQWEsQ0FBQztBQUNoRCxPQUFPLENBQUMsbUJBQW1CLEdBQUcsU0FBUyxDQUFDLG1CQUFtQixDQUFDO0FBQzVELE9BQU8sQ0FBQyxtQkFBbUIsR0FBRyxRQUFRLENBQUMsbUJBQW1CLENBQUM7QUFDM0QsT0FBTyxDQUFDLHNCQUFzQixHQUFHLFFBQVEsQ0FBQyxzQkFBc0IsQ0FBQztBQUNqRSxPQUFPLENBQUMsV0FBVyxHQUFHLFdBQVcsQ0FBQyxjQUFjLENBQUM7QUFDakQsT0FBTyxDQUFDLGtCQUFrQixHQUFHLFdBQVcsQ0FBQyxrQkFBa0IsQ0FBQztBQUM1RCxPQUFPLENBQUMscUJBQXFCLEdBQUcsV0FBVyxDQUFDLHFCQUFxQixDQUFDO0FBQ2xFLE9BQU8sQ0FBQyxvQkFBb0IsR0FBRyxXQUFXLENBQUMsb0JBQW9CLENBQUM7Ozs7Ozs7NEJDNUd0QyxpQkFBaUI7O0lBQS9CLFFBQVE7Ozs7Ozs7OztBQURwQixJQUFNLElBQUksR0FBRyxPQUFPLENBQUMsaUJBQWlCLENBQUMsQ0FBQztBQVV4QyxTQUFTLFFBQVEsQ0FBQyxJQUFJLEVBQUUsRUFBRSxFQUFFLFFBQVEsRUFBRTtRQUMzQixNQUFNLEdBQTJCLEVBQUU7UUFBM0IsT0FBTyxHQUFrQixFQUFFO1FBQWxCLFlBQVksR0FBSSxFQUFFOztBQUMxQyxZQUFRLFFBQVE7QUFDWixhQUFLLHFCQUFxQixDQUFDO0FBQzNCLGFBQUssb0JBQW9CLENBQUM7QUFDMUIsYUFBSyx5QkFBeUI7QUFDMUIsbUJBQU8sQ0FBQyxJQUFJLEVBQUUsU0FBUyxDQUFDLENBQUM7QUFBQSxBQUM3QixhQUFLLGNBQWM7O0FBRWYsbUJBQU8sQ0FBQyxNQUFNLEVBQUUsSUFBSSxFQUFFLE9BQU8sQ0FBQyxDQUFDO0FBQUEsQUFDbkMsYUFBSyxhQUFhOztBQUVkLG1CQUFPLENBQUMsTUFBTSxFQUFFLFlBQVksQ0FBQyxDQUFDO0FBQUEsQUFDbEMsYUFBSyxnQkFBZ0I7QUFDakIsZ0JBQUksRUFBRSxDQUFDLEtBQUssRUFBRTs7QUFFVix1QkFBTyxDQUFDLE1BQU0sRUFBRSxZQUFZLENBQUMsQ0FBQzthQUNqQyxNQUNJOztBQUVELHVCQUFPLENBQUMsTUFBTSxFQUFFLE9BQU8sRUFBRSxZQUFZLENBQUMsQ0FBQzthQUMxQztBQUFBLEFBQ0w7QUFDSSxtQkFBTyxDQUFDLE1BQU0sRUFBRSxPQUFPLEVBQUUsWUFBWSxDQUFDLENBQUM7QUFBQSxLQUM5QztDQUNKOzs7Ozs7OztBQVFELFNBQVMsbUJBQW1CLENBQUMsR0FBRyxFQUFFLEdBQUcsRUFBRTtBQUNuQyxnQkFBWSxDQUFDOzs7O0FBSWIsUUFBTSxNQUFNLEdBQUcsUUFBUSxDQUFDLFVBQVUsQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDO0FBQ3JDLG9CQUFZLEVBQUUsc0JBQUMsSUFBSSxFQUFFLEVBQUUsRUFBRSxDQUFDLEVBQUs7QUFDM0IsYUFBQyxDQUFDLElBQUksQ0FBQyxLQUFLLEVBQUUsRUFBRSxDQUFDLENBQUM7O0FBRWxCLGNBQUUsQ0FBQyxLQUFLLEdBQUcsSUFBSSxDQUFDO0FBQ2hCLGdCQUFJLElBQUksQ0FBQyxPQUFPLEVBQUUsQ0FBQyxDQUFDLElBQUksQ0FBQyxPQUFPLEVBQUUsRUFBRSxDQUFDLENBQUM7QUFDdEMsZ0JBQUksSUFBSSxDQUFDLFNBQVMsRUFBRSxDQUFDLENBQUMsSUFBSSxDQUFDLFNBQVMsRUFBRSxFQUFFLENBQUMsQ0FBQztTQUM3QztBQUNELG1CQUFXLEVBQUUscUJBQUMsSUFBSSxFQUFFLEVBQUUsRUFBRSxDQUFDLEVBQUs7QUFDMUIsYUFBQyxDQUFDLElBQUksQ0FBQyxJQUFJLEVBQUUsRUFBRSxDQUFDLENBQUM7U0FDcEI7S0FDSixFQUFFLElBQUksQ0FBQyxJQUFJLENBQUM7O0FBRWIsY0FBQyxJQUFJLEVBQUUsRUFBRSxFQUFFLFFBQVEsRUFBSztBQUNwQixZQUFJLElBQUksQ0FBQyxLQUFLLEdBQUcsR0FBRyxJQUFJLElBQUksQ0FBQyxHQUFHLEdBQUcsR0FBRyxFQUFFO0FBQ3BDLG1CQUFPLEtBQUssQ0FBQztTQUNoQjs7Ozs7QUFLRCxZQUFJLEFBQUMsQ0FBQyxRQUFRLEtBQUsscUJBQXFCLElBQUksUUFBUSxLQUFLLG9CQUFvQixDQUFBLEtBQ3JFLElBQUksQ0FBQyxLQUFLLElBQUksR0FBRyxJQUFJLEdBQUcsSUFBSSxJQUFJLENBQUMsS0FBSyxHQUFHLENBQUMsQ0FBQSxBQUFDLElBRTlDLFFBQVEsS0FBSyxpQkFBaUIsS0FDM0IsSUFBSSxDQUFDLEtBQUssSUFBSSxHQUFHLElBQUksR0FBRyxJQUFJLElBQUksQ0FBQyxLQUFLLEdBQUcsQ0FBQyxDQUFBLEFBQUMsQUFBQyxJQUUvQyxRQUFRLEtBQUssZ0JBQWdCLEtBQzFCLElBQUksQ0FBQyxLQUFLLElBQUksR0FBRyxJQUFJLEdBQUcsSUFBSSxJQUFJLENBQUMsS0FBSyxHQUFHLENBQUMsQ0FBQSxBQUFDLEFBQUMsRUFBRTs7QUFFbEQsY0FBRSxDQUFDLElBQUksR0FBRyxJQUFJLENBQUMsSUFBSSxDQUFDO0FBQ3BCLGtCQUFNLEVBQUUsQ0FBQztTQUNaO0FBQ0QsZUFBTyxJQUFJLENBQUM7S0FDZjs7QUFFRCxhQUFTOztBQUVULFlBQVEsQ0FDWCxDQUFDOztBQUVGLFFBQUk7QUFDQSxZQUFJLENBQUMsU0FBUyxDQUFDLEdBQUcsRUFBRSxFQUFFLEVBQUUsTUFBTSxDQUFDLENBQUM7S0FDbkMsQ0FBQyxPQUFPLENBQUMsRUFBRTtBQUNSLFlBQUksQ0FBQyxJQUFJLENBQUMsWUFBWSxLQUFLLEVBQUU7O0FBRXpCLG1CQUFPLENBQUMsQ0FBQztTQUNaLE1BQU07O0FBRUgsa0JBQU0sQ0FBQyxDQUFDO1NBQ1g7S0FDSjs7QUFFRCxXQUFPLElBQUksQ0FBQztDQUNmOzs7Ozs7OztBQVFELFNBQVMsZ0JBQWdCLENBQUMsUUFBUSxFQUFFO0FBQ2hDLGdCQUFZLENBQUM7QUFDYixRQUFNLEtBQUssR0FBRyxFQUFFLENBQUM7UUFDVixNQUFNLEdBQWEsUUFBUTtRQUFuQixPQUFPLEdBQUksUUFBUTs7QUFFbEMsUUFBTSxNQUFNLEdBQUcsUUFBUSxDQUFDLFVBQVUsQ0FDOUIsSUFBSSxDQUFDLElBQUksQ0FBQztBQUNOLG9CQUFZLEVBQUUsc0JBQUMsSUFBSSxFQUFFLEVBQUUsRUFBRSxDQUFDLEVBQUs7QUFDM0IsYUFBQyxDQUFDLElBQUksQ0FBQyxLQUFLLEVBQUUsRUFBRSxDQUFDLENBQUM7O0FBRWxCLGNBQUUsQ0FBQyxLQUFLLEdBQUcsSUFBSSxDQUFDOztBQUVoQixnQkFBSSxJQUFJLENBQUMsT0FBTyxFQUFFLENBQUMsQ0FBQyxJQUFJLENBQUMsT0FBTyxFQUFFLEVBQUUsQ0FBQyxDQUFDO0FBQ3RDLGdCQUFJLElBQUksQ0FBQyxTQUFTLEVBQUUsQ0FBQyxDQUFDLElBQUksQ0FBQyxTQUFTLEVBQUUsRUFBRSxDQUFDLENBQUM7U0FDN0M7QUFDRCx1QkFBZSxFQUFFLHlCQUFDLElBQUksRUFBSztBQUN2QixnQkFBSSxRQUFRLENBQUMsSUFBSSxLQUFLLGdCQUFnQixJQUFJLE9BQU8sRUFBRSxPQUFPO0FBQzFELGlCQUFLLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQyxDQUFDO1NBQ3BCO0FBQ0QsZ0JBQVEsRUFBRSxvQkFBTTs7U0FFZjtBQUNELHNCQUFjLEVBQUUsd0JBQUMsSUFBSSxFQUFFLElBQUssRUFBSztnQkFBVCxDQUFDLEdBQUYsSUFBSztnQkFBRixDQUFDLEdBQUosSUFBSzs7QUFDeEIsZ0JBQUksQUFBQyxRQUFRLENBQUMsSUFBSSxLQUFLLGdCQUFnQixJQUFJLE9BQU8sS0FBSyxDQUFDLElBQ2pELENBQUMsS0FBSyxTQUFTLEVBQUU7QUFDcEIscUJBQUssQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDLENBQUM7YUFDcEI7U0FDSjtBQUNELG1CQUFXLEVBQUUscUJBQUMsSUFBSSxFQUFFLEVBQUUsRUFBRSxDQUFDLEVBQUs7QUFDMUIsYUFBQyxDQUFDLElBQUksQ0FBQyxJQUFJLEVBQUUsRUFBRSxDQUFDLENBQUM7U0FDcEI7S0FDSixFQUFFLElBQUksQ0FBQyxJQUFJLENBQUMsRUFDYixTQUFTLEVBQ1QsU0FBUyxFQUNULFFBQVEsQ0FBQyxDQUFDOztBQUVkLFFBQUksUUFBUSxDQUFDLElBQUksS0FBSyxnQkFBZ0IsSUFBSSxPQUFPLEVBQUU7QUFDL0MsWUFBSSxDQUFDLFNBQVMsQ0FBQyxPQUFPLENBQUMsS0FBSyxFQUFFLENBQUMsU0FBUyxFQUFFLE9BQU8sQ0FBQyxFQUFFLE1BQU0sQ0FBQyxDQUFDO0tBQy9ELE1BQU07QUFDSCxZQUFJLENBQUMsU0FBUyxDQUFDLE1BQU0sQ0FBQyxJQUFJLEVBQUUsQ0FBQyxNQUFNLEVBQUUsU0FBUyxDQUFDLEVBQUUsTUFBTSxDQUFDLENBQUM7S0FDNUQ7O0FBRUQsV0FBTyxLQUFLLENBQUM7Q0FDaEI7Ozs7Ozs7Ozs7O0FBV0QsU0FBUyxzQkFBc0IsQ0FBQyxHQUFHLEVBQUUsR0FBRyxFQUFFLGNBQWMsRUFBRTtBQUN0RCxnQkFBWSxDQUFDOztBQUViLFFBQU0sUUFBUSxHQUFHLG1CQUFtQixDQUFDLEdBQUcsRUFBRSxHQUFHLENBQUMsQ0FBQztBQUMvQyxRQUFJLENBQUMsUUFBUSxFQUFFO0FBQ1gsZUFBTyxJQUFJLENBQUM7S0FDZjs7QUFFRCxRQUFNLE1BQU0sR0FBRyxnQkFBZ0IsQ0FBQyxRQUFRLENBQUMsQ0FBQyxHQUFHLENBQ3JDLFVBQUEsSUFBSSxFQUFJO0FBQ0osZUFBTyxFQUFDLEtBQUssRUFBRSxJQUFJLENBQUMsS0FBSyxFQUFFLEdBQUcsRUFBRSxJQUFJLENBQUMsR0FBRyxFQUFDLENBQUM7S0FDN0MsQ0FBQyxDQUFDO1FBQ0osTUFBTSxHQUFhLFFBQVE7UUFBbkIsT0FBTyxHQUFJLFFBQVE7Ozs7QUFHbEMsUUFBSSxRQUFRLENBQUMsSUFBSSxLQUFLLGdCQUFnQixJQUFJLE1BQU0sQ0FBQyxNQUFNLEtBQUssQ0FBQyxFQUFFO0FBQzNELGNBQU0sQ0FBQyxJQUFJLENBQUMsRUFBQyxLQUFLLEVBQUUsTUFBTSxDQUFDLEdBQUcsR0FBRyxDQUFDLEVBQUUsR0FBRyxFQUFFLE1BQU0sQ0FBQyxHQUFHLEVBQUMsQ0FBQyxDQUFDO0tBQ3pEOzs7QUFHRCxRQUFJLFFBQVEsQ0FBQyxJQUFJLEtBQUssZ0JBQWdCLElBQUksT0FBTyxFQUFFO0FBQy9DLGNBQU0sQ0FBQyxJQUFJLENBQUMsRUFBQyxLQUFLLEVBQUUsT0FBTyxDQUFDLE9BQU8sQ0FBQyxLQUFLLEVBQUUsR0FBRyxFQUFFLE9BQU8sQ0FBQyxPQUFPLENBQUMsS0FBSyxHQUFHLENBQUMsRUFBQyxDQUFDLENBQUM7S0FDL0UsTUFBTSxJQUFJLGNBQWMsRUFBRTtBQUN2QixZQUFJLE1BQU0sQ0FBQyxJQUFJLEtBQUsseUJBQXlCLEVBQUU7O0FBRTNDLGtCQUFNLENBQUMsSUFBSSxDQUFDLEVBQUMsS0FBSyxFQUFFLE1BQU0sQ0FBQyxLQUFLLEVBQUUsR0FBRyxFQUFFLE1BQU0sQ0FBQyxLQUFLLEdBQUcsQ0FBQyxFQUFDLENBQUMsQ0FBQztTQUM3RCxNQUFNOztTQUVOO0tBQ0o7QUFDRCxXQUFPLE1BQU0sQ0FBQztDQUNqQjs7QUFFRCxPQUFPLENBQUMsbUJBQW1CLEdBQUcsbUJBQW1CLENBQUM7QUFDbEQsT0FBTyxDQUFDLHNCQUFzQixHQUFHLHNCQUFzQixDQUFDOzs7Ozs7OzRCQ3JNOUIsaUJBQWlCOztJQUEvQixRQUFROzs7Ozs7OztBQURwQixJQUFNLElBQUksR0FBRyxPQUFPLENBQUMsaUJBQWlCLENBQUMsQ0FBQztBQVN4QyxTQUFTLGFBQWEsQ0FBQyxHQUFHLEVBQUUsR0FBRyxFQUFFO0FBQzdCLGdCQUFZLENBQUM7Ozs7QUFJYixRQUFNLE1BQU0sR0FBRyxRQUFRLENBQUMsVUFBVSxDQUFDLElBQUksQ0FBQyxJQUFJOztBQUV4QyxjQUFDLElBQUksRUFBRSxFQUFFLEVBQUs7QUFDVixZQUFJLElBQUksQ0FBQyxLQUFLLEdBQUcsR0FBRyxJQUFJLElBQUksQ0FBQyxHQUFHLEdBQUcsR0FBRyxFQUFFO0FBQ3BDLG1CQUFPLEtBQUssQ0FBQztTQUNoQjs7QUFFRCxZQUFJLElBQUksQ0FBQyxJQUFJLEtBQUssZ0JBQWdCLEVBQUU7QUFDaEMsa0JBQU0sRUFBRSxDQUFDO1NBQ1o7QUFDRCxlQUFPLElBQUksQ0FBQztLQUNmOztBQUVELGFBQVM7O0FBRVQsY0FBQyxJQUFJLEVBQUUsRUFBRSxFQUFLO0FBQ1YsWUFBSSxJQUFJLENBQUMsSUFBSSxLQUFLLHFCQUFxQixJQUNoQyxJQUFJLENBQUMsSUFBSSxLQUFLLG9CQUFvQixFQUFFO0FBQ3ZDLG1CQUFPLElBQUksQ0FBQztTQUNmLE1BQU07QUFDSCxtQkFBTyxFQUFFLENBQUM7U0FDYjtLQUNKLENBQUMsQ0FBQzs7QUFFUCxRQUFJO0FBQ0EsWUFBSSxDQUFDLFNBQVMsQ0FBQyxHQUFHLEVBQUUsU0FBUyxFQUFFLE1BQU0sQ0FBQyxDQUFDO0tBQzFDLENBQUMsT0FBTyxDQUFDLEVBQUU7QUFDUixZQUFJLENBQUMsSUFBSSxDQUFDLENBQUMsSUFBSSxLQUNWLENBQUMsQ0FBQyxJQUFJLEtBQUssb0JBQW9CLElBQzdCLENBQUMsQ0FBQyxJQUFJLEtBQUsscUJBQXFCLENBQUEsQUFBQyxFQUFFO0FBQ3RDLG1CQUFPLENBQUMsQ0FBQztTQUNaLE1BQU07QUFDSCxrQkFBTSxDQUFDLENBQUM7U0FDWDtLQUNKOztBQUVELFdBQU8sSUFBSSxDQUFDO0NBQ2Y7Ozs7Ozs7O0FBUUQsU0FBUyxZQUFZLENBQUMsS0FBSyxFQUFFO0FBQ3pCLGdCQUFZLENBQUM7QUFDYixRQUFNLElBQUksR0FBRyxFQUFFLENBQUM7QUFDaEIsUUFBSSxLQUFLLENBQUMsSUFBSSxLQUFLLG9CQUFvQixJQUNoQyxLQUFLLENBQUMsSUFBSSxLQUFLLHFCQUFxQixFQUFFO0FBQ3pDLGNBQU0sS0FBSyxDQUFDLGlDQUFpQyxDQUFDLENBQUM7S0FDbEQ7O0FBRUQsUUFBTSxNQUFNLEdBQUcsSUFBSSxDQUFDLElBQUksQ0FBQztBQUNyQixzQkFBYyxFQUFFLHdCQUFDLElBQUksRUFBSztBQUN0QixtQkFBTyxJQUFJLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQyxDQUFDO1NBQzFCO0FBQ0QsMkJBQW1CLEVBQUUsK0JBQU07O1NBRTFCO0FBQ0QsMEJBQWtCLEVBQUUsOEJBQU07O1NBRXpCO0tBQ0osRUFBRSxJQUFJLENBQUMsSUFBSSxDQUFDLENBQUM7O0FBRWQsUUFBSSxDQUFDLFNBQVMsQ0FBQyxLQUFLLENBQUMsSUFBSSxFQUFFLFNBQVMsRUFBRSxNQUFNLENBQUMsQ0FBQzs7QUFFOUMsV0FBTyxJQUFJLENBQUM7Q0FDZjs7Ozs7Ozs7OztBQVVELFNBQVMsbUJBQW1CLENBQUMsR0FBRyxFQUFFLEdBQUcsRUFBRSxzQkFBc0IsRUFBRTtBQUMzRCxnQkFBWSxDQUFDOztBQUViLFFBQU0sS0FBSyxHQUFHLGFBQWEsQ0FBQyxHQUFHLEVBQUUsR0FBRyxDQUFDLENBQUM7QUFDdEMsUUFBSSxDQUFDLEtBQUssRUFBRTs7QUFFUixlQUFPLElBQUksQ0FBQztLQUNmOztBQUVELFFBQU0sSUFBSSxHQUFHLFlBQVksQ0FBQyxLQUFLLENBQUMsQ0FBQztBQUNqQyxRQUFJLHNCQUFzQixFQUFFO0FBQ3hCLFlBQUksQ0FBQyxJQUFJLENBQUMsRUFBQyxLQUFLLEVBQUUsS0FBSyxDQUFDLEtBQUssRUFBRSxHQUFHLEVBQUUsS0FBSyxDQUFDLEtBQUssR0FBRyxDQUFDLEVBQUMsQ0FBQyxDQUFDO0tBQ3pEO0FBQ0QsV0FBTyxJQUFJLENBQUM7Q0FDZjs7QUFFRCxPQUFPLENBQUMsYUFBYSxHQUFHLGFBQWEsQ0FBQztBQUN0QyxPQUFPLENBQUMsbUJBQW1CLEdBQUcsbUJBQW1CLENBQUM7Ozs7Ozs7Ozs7Ozs7Ozs7O0FDN0dsRCxJQUFNLElBQUksR0FBRyxPQUFPLENBQUMsaUJBQWlCLENBQUMsQ0FBQzs7Ozs7OztBQU94QyxTQUFTLGNBQWMsR0FBRztBQUN0QixRQUFNLE1BQU0sR0FBRyxNQUFNLENBQUMsTUFBTSxDQUFDLElBQUksQ0FBQyxDQUFDO0FBQ25DLFFBQU0sUUFBUSxHQUFHLFNBQVgsUUFBUSxHQUFTLEVBQUUsQ0FBQztBQUMxQixTQUFLLElBQUksS0FBSSxJQUFJLE1BQU0sQ0FBQyxtQkFBbUIsQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDLEVBQUU7QUFDcEQsY0FBTSxDQUFDLEtBQUksQ0FBQyxHQUFHLFFBQVEsQ0FBQztLQUMzQjtBQUNELFdBQU8sTUFBTSxDQUFDO0NBQ2pCO0FBQ00sSUFBTSxVQUFVLEdBQUcsY0FBYyxFQUFFLENBQUM7Ozs7Ozs7OztBQU9wQyxTQUFTLGtCQUFrQixDQUFDLE9BQU8sRUFBRTtBQUN4QyxRQUFNLHVCQUF1QixHQUFHLElBQUksQ0FBQyxJQUFJLENBQUMsVUFBVSxFQUFFO0FBQ2xELHlCQUFpQixFQUFFLDJCQUFDLElBQUksRUFBRSxFQUFFLEVBQUUsQ0FBQyxFQUFLO0FBQ2hDLGtCQUFNLElBQUksS0FBSyxFQUFFLENBQUM7U0FDckI7QUFDRCxxQkFBYSxFQUFFLElBQUksQ0FBQyxJQUFJLENBQUMsYUFBYTtBQUN0QyxvQkFBWSxFQUFFLElBQUksQ0FBQyxJQUFJLENBQUMsZUFBZTtBQUN2QyxtQkFBVyxFQUFFLElBQUksQ0FBQyxJQUFJLENBQUMsV0FBVztLQUNyQyxDQUFDLENBQUM7O0FBRUgsUUFBSTtBQUNBLFlBQUksQ0FBQyxTQUFTLENBQUMsT0FBTyxFQUFFLFNBQVMsRUFBRSx1QkFBdUIsQ0FBQyxDQUFDO0tBQy9ELENBQUMsT0FBTyxDQUFDLEVBQUU7QUFDUixZQUFJLENBQUMsWUFBWSxLQUFLLEVBQUU7QUFDcEIsbUJBQU8sSUFBSSxDQUFDO1NBQ2Y7S0FDSjtBQUNELFdBQU8sS0FBSyxDQUFDO0NBQ2hCOzs7Ozs7QUFNTSxJQUFNLFNBQVMsR0FBRyxJQUFJLENBQUMsSUFBSSxDQUFDO0FBQy9CLFlBQVEsRUFBRSxrQkFBQyxJQUFJLEVBQUUsRUFBRSxFQUFFLENBQUMsRUFBSztBQUN2QixZQUFJLElBQUksQ0FBQyxFQUFFLEVBQUUsQ0FBQyxDQUFDLElBQUksQ0FBQyxFQUFFLEVBQUUsRUFBRSxFQUFFLFNBQVMsQ0FBQyxDQUFDO0FBQ3ZDLFlBQU0sT0FBTyxHQUFHLElBQUksQ0FBQyxRQUFRLENBQUMsSUFBSSxJQUFJLENBQUMsSUFBSSxDQUFDLFFBQVEsQ0FBQyxDQUFDO0FBQ3RELGFBQUssSUFBSSxDQUFDLEdBQUcsQ0FBQyxFQUFFLENBQUMsR0FBRyxJQUFJLENBQUMsTUFBTSxDQUFDLE1BQU0sRUFBRSxDQUFDLEVBQUUsRUFBRTtBQUN6QyxhQUFDLENBQUMsSUFBSSxDQUFDLE1BQU0sQ0FBQyxDQUFDLENBQUMsRUFBRSxPQUFPLEVBQUUsU0FBUyxDQUFDLENBQUM7U0FDekM7QUFDRCxZQUFNLE9BQU8sR0FBRyxJQUFJLENBQUMsSUFBSSxDQUFDLFFBQVEsQ0FBQyxDQUFDO0FBQ3BDLFNBQUMsQ0FBQyxJQUFJLENBQUMsSUFBSSxFQUFFLE9BQU8sRUFBRSxJQUFJLENBQUMsVUFBVSxHQUFHLGlCQUFpQixHQUFHLFdBQVcsQ0FBQyxDQUFDO0tBQzVFO0FBQ0QsZ0JBQVksRUFBRSxzQkFBQyxJQUFJLEVBQUUsRUFBRSxFQUFFLENBQUMsRUFBSztBQUMzQixZQUFNLE9BQU8sR0FBRyxJQUFJLENBQUMsUUFBUSxDQUFDLElBQUksRUFBRSxDQUFDOztBQUVyQyxZQUFJLENBQUMsSUFBSSxDQUFDLFlBQVksQ0FBQyxJQUFJLEVBQUUsT0FBTyxFQUFFLENBQUMsQ0FBQyxDQUFDO0tBQzVDO0FBQ0Qsa0JBQWMsRUFBRSx3QkFBQyxJQUFJLEVBQUUsRUFBRSxFQUFFLENBQUMsRUFBSztBQUM3QixZQUFNLE9BQU8sR0FBRyxJQUFJLENBQUMsUUFBUSxDQUFDLElBQUksRUFBRSxDQUFDOztBQUVyQyxZQUFJLENBQUMsSUFBSSxDQUFDLGNBQWMsQ0FBQyxJQUFJLEVBQUUsT0FBTyxFQUFFLENBQUMsQ0FBQyxDQUFDO0tBQzlDO0FBQ0QsZ0JBQVksRUFBRSxzQkFBQyxJQUFJLEVBQUUsRUFBRSxFQUFFLENBQUMsRUFBSztBQUMzQixTQUFDLENBQUMsSUFBSSxDQUFDLEtBQUssRUFBRSxFQUFFLENBQUMsQ0FBQztBQUNsQixZQUFJLElBQUksQ0FBQyxPQUFPLEVBQUU7OztBQUdkLGFBQUMsQ0FBQyxJQUFJLENBQUMsT0FBTyxFQUFFLEVBQUUsQ0FBQyxDQUFDO1NBQ3ZCO0FBQ0QsWUFBSSxJQUFJLENBQUMsU0FBUyxFQUFFO0FBQ2hCLGFBQUMsQ0FBQyxJQUFJLENBQUMsU0FBUyxFQUFFLEVBQUUsQ0FBQyxDQUFDO1NBQ3pCO0tBQ0o7QUFDRCxlQUFXLEVBQUUscUJBQUMsSUFBSSxFQUFFLEVBQUUsRUFBRSxDQUFDLEVBQUs7QUFDMUIsWUFBTSxPQUFPLEdBQUcsSUFBSSxDQUFDLElBQUksQ0FBQyxRQUFRLENBQUMsQ0FBQzs7QUFFcEMsU0FBQyxDQUFDLElBQUksQ0FBQyxLQUFLLEVBQUUsT0FBTyxDQUFDLENBQUM7QUFDdkIsU0FBQyxDQUFDLElBQUksQ0FBQyxJQUFJLEVBQUUsT0FBTyxDQUFDLENBQUM7S0FDekI7QUFDRCxtQkFBZSxFQUFFLHlCQUFDLElBQUksRUFBRSxFQUFFLEVBQUUsQ0FBQyxFQUFLOzs7QUFHOUIsU0FBQyxDQUFDLElBQUksRUFBRSxFQUFFLEVBQUUsWUFBWSxDQUFDLENBQUM7S0FDN0I7Q0FDSixDQUFDLENBQUM7Ozs7Ozs7Ozs7Ozs7OztBQWFJLFNBQVMsVUFBVSxDQUFDLE1BQU0sRUFBRSxPQUFPLEVBQUUsUUFBUSxFQUFFLFFBQVEsRUFBRTtBQUM1RCxnQkFBWSxDQUFDO0FBQ2IsUUFBTSxTQUFTLEdBQUcsRUFBRSxDQUFDOzs7MEJBRVosUUFBUTtBQUNiLFlBQUksQ0FBQyxNQUFNLENBQUMsY0FBYyxDQUFDLFFBQVEsQ0FBQyxFQUFFO0FBQ2xDLDhCQUFTO1NBQ1o7QUFDRCxpQkFBUyxDQUFDLFFBQVEsQ0FBQyxHQUFHLFVBQUMsSUFBSSxFQUFFLEVBQUUsRUFBRSxDQUFDLEVBQUs7QUFDbkMsZ0JBQUksR0FBRyxZQUFBLENBQUM7QUFDUixnQkFBSSxLQUFLLEdBQUcsRUFBRSxDQUFDO0FBQ2YsZ0JBQUksUUFBUSxFQUFFO0FBQ1YscUJBQUssR0FBRyxRQUFRLENBQUMsSUFBSSxFQUFFLEVBQUUsRUFBRSxRQUFRLENBQUMsQ0FBQzthQUN4QztBQUNELGdCQUFJLENBQUMsT0FBTyxJQUFJLE9BQU8sQ0FBQyxJQUFJLEVBQUUsS0FBSyxFQUFFLFFBQVEsQ0FBQyxFQUFFO0FBQzVDLG1CQUFHLEdBQUcsTUFBTSxDQUFDLFFBQVEsQ0FBQyxDQUFDLElBQUksRUFBRSxLQUFLLEVBQUUsQ0FBQyxDQUFDLENBQUM7YUFDMUMsTUFBTTtBQUNILHVCQUFPO2FBQ1Y7QUFDRCxnQkFBSSxRQUFRLEVBQUU7QUFDVixtQkFBRyxHQUFHLFFBQVEsQ0FBQyxJQUFJLEVBQUUsS0FBSyxFQUFFLFFBQVEsQ0FBQyxDQUFDO2FBQ3pDO0FBQ0QsbUJBQU8sR0FBRyxDQUFDO1NBQ2QsQ0FBQTs7O0FBbkJMLFNBQUssSUFBSSxRQUFRLElBQUksTUFBTSxFQUFFO3lCQUFwQixRQUFROztpQ0FFVCxTQUFTO0tBa0JoQjtBQUNELFdBQU8sU0FBUyxDQUFDO0NBQ3BCOzs7Ozs7O0lBTVksS0FBSyxHQUNILFNBREYsS0FBSyxDQUNGLElBQUksRUFBRTswQkFEVCxLQUFLOztBQUVWLFFBQUksQ0FBQyxJQUFJLEdBQUcsSUFBSSxDQUFDO0NBQ3BCOzs7O0FBR0UsU0FBUyxhQUFhLENBQUMsSUFBSSxFQUFFO0FBQ2hDLFFBQUksSUFBSSxDQUFDLElBQUksS0FBSyxZQUFZLEVBQUU7QUFDNUIsY0FBTSxJQUFJLEtBQUssQ0FBQyw4QkFBOEIsQ0FBQyxDQUFDO0tBQ25EO0FBQ0QsV0FBTyxJQUFJLENBQUMsSUFBSSxLQUFLLEdBQUcsSUFBSSxJQUFJLENBQUMsS0FBSyxJQUFJLElBQUksQ0FBQyxHQUFHLENBQUM7Q0FDdEQ7O0FBRU0sU0FBUyxnQkFBZ0IsQ0FBQyxHQUFHLEVBQUUsR0FBRyxFQUFFO0FBQ3ZDLGdCQUFZLENBQUM7QUFDYixXQUFPLFVBQVUsQ0FBQyxHQUFHLEVBQUUsR0FBRyxFQUNsQixVQUFBLElBQUk7ZUFBSSxJQUFJLENBQUMsSUFBSSxLQUFLLFlBQVksSUFBSSxDQUFDLGFBQWEsQ0FBQyxJQUFJLENBQUM7S0FBQSxDQUNqRSxDQUFDO0NBQ0w7O0FBRU0sU0FBUyxzQkFBc0IsQ0FBQyxHQUFHLEVBQUUsR0FBRyxFQUFFO0FBQzdDLGdCQUFZLENBQUM7QUFDYixXQUFPLFVBQVUsQ0FBQyxHQUFHLEVBQUUsR0FBRyxFQUNsQixVQUFBLElBQUksRUFBSTtBQUNKLGVBQU8sQUFBQyxJQUFJLENBQUMsSUFBSSxLQUFLLFlBQVksSUFBSSxDQUFDLGFBQWEsQ0FBQyxJQUFJLENBQUMsSUFDckQsSUFBSSxDQUFDLElBQUksS0FBSyxrQkFBa0IsS0FFN0IsQUFBQyxJQUFJLENBQUMsUUFBUSxDQUFDLEtBQUssSUFBSSxHQUFHLElBQUksR0FBRyxJQUFJLElBQUksQ0FBQyxRQUFRLENBQUMsR0FBRzs7QUFFdEQsWUFBSSxDQUFDLFFBQVEsQ0FBQyxHQUFHLElBQUksR0FBRyxJQUFJLEdBQUcsSUFBSSxJQUFJLENBQUMsUUFBUSxDQUFDLEtBQUssQ0FBQyxBQUMzRCxBQUFDLENBQUM7S0FDVixDQUNSLENBQUM7Q0FDTDs7QUFFTSxTQUFTLHFCQUFxQixDQUFDLEdBQUcsRUFBRSxHQUFHLEVBQUU7QUFDNUMsZ0JBQVksQ0FBQzs7QUFFYixRQUFNLE1BQU0sR0FBRyxVQUFVLENBQUMsU0FBUyxFQUMvQixVQUFDLElBQUksRUFBRSxFQUFFLEVBQUs7QUFDVixZQUFJLElBQUksQ0FBQyxLQUFLLEdBQUcsR0FBRyxJQUFJLElBQUksQ0FBQyxHQUFHLEdBQUcsR0FBRyxFQUFFO0FBQ3BDLG1CQUFPLEtBQUssQ0FBQztTQUNoQjs7QUFFRCxZQUFJLElBQUksQ0FBQyxJQUFJLEtBQUssWUFBWSxFQUFFO0FBQzVCLGtCQUFNLElBQUksS0FBSyxDQUFDLEVBQUMsSUFBSSxFQUFFLFlBQVksRUFBRSxJQUFJLEVBQUUsSUFBSSxFQUFFLEVBQUUsRUFBRSxFQUFFLEVBQUMsQ0FBQyxDQUFDO1NBQzdEOztBQUVELFlBQUksSUFBSSxDQUFDLElBQUksS0FBSyxrQkFBa0IsS0FFNUIsQUFBQyxJQUFJLENBQUMsUUFBUSxDQUFDLEtBQUssSUFBSSxHQUFHLElBQUksR0FBRyxJQUFJLElBQUksQ0FBQyxRQUFRLENBQUMsR0FBRzs7QUFFdEQsWUFBSSxDQUFDLFFBQVEsQ0FBQyxHQUFHLElBQUksR0FBRyxJQUFJLEdBQUcsSUFBSSxJQUFJLENBQUMsUUFBUSxDQUFDLEtBQUssQ0FBQyxBQUMzRCxFQUNIOztBQUVFLGdCQUFJLENBQUMsSUFBSSxDQUFDLFFBQVEsRUFBRTtBQUNoQixzQkFBTSxJQUFJLEtBQUssQ0FBQyxFQUFDLElBQUksRUFBRSxXQUFXLEVBQUUsSUFBSSxFQUFFLElBQUksRUFBRSxFQUFFLEVBQUUsRUFBRSxFQUFDLENBQUMsQ0FBQzthQUM1RDs7QUFFRCxnQkFBSSxJQUFJLENBQUMsUUFBUSxJQUNiLE9BQU8sSUFBSSxDQUFDLFFBQVEsQ0FBQyxLQUFLLEtBQUssUUFBUSxFQUFFO0FBQ3pDLHNCQUFNLElBQUksS0FBSyxDQUFDLEVBQUMsSUFBSSxFQUFFLFlBQVksRUFBRSxJQUFJLEVBQUUsSUFBSSxFQUFFLEVBQUUsRUFBRSxFQUFFLEVBQUMsQ0FBQyxDQUFDO2FBQzdEO1NBQ0o7QUFDRCxlQUFPLElBQUksQ0FBQztLQUNmLEVBQ0QsVUFBQyxJQUFJLEVBQUUsRUFBRSxFQUFLOztBQUVWLGNBQU0sSUFBSSxLQUFLLENBQUMsRUFBQyxJQUFJLEVBQUUsWUFBWSxFQUFFLElBQUksRUFBRSxJQUFJLEVBQUUsRUFBRSxFQUFFLEVBQUUsRUFBQyxDQUFDLENBQUM7S0FDN0QsQ0FBQyxDQUFDOztBQUVQLFFBQUk7QUFDQSxZQUFJLENBQUMsU0FBUyxDQUFDLEdBQUcsRUFBRSxHQUFHLENBQUMsUUFBUSxDQUFDLEVBQUUsTUFBTSxDQUFDLENBQUM7S0FDOUMsQ0FBQyxPQUFPLENBQUMsRUFBRTtBQUNSLFlBQUksQ0FBQyxZQUFZLEtBQUssRUFBRTtBQUNwQixtQkFBTyxDQUFDLENBQUMsSUFBSSxDQUFDO1NBQ2pCLE1BQU07QUFDSCxrQkFBTSxDQUFDLENBQUM7U0FDWDtLQUNKO0NBQ0o7Ozs7Ozs7Ozs7O0FBWUQsU0FBUyxVQUFVLENBQUMsR0FBRyxFQUFFLEdBQUcsRUFBRSxRQUFRLEVBQUU7QUFDcEMsZ0JBQVksQ0FBQzs7QUFFYixRQUFNLE1BQU0sR0FBRyxVQUFVLENBQUMsU0FBUyxFQUMvQixVQUFDLElBQUksRUFBRSxFQUFFLEVBQUs7QUFDVixZQUFJLElBQUksQ0FBQyxLQUFLLEdBQUcsR0FBRyxJQUFJLElBQUksQ0FBQyxHQUFHLEdBQUcsR0FBRyxFQUFFO0FBQ3BDLG1CQUFPLEtBQUssQ0FBQztTQUNoQjtBQUNELFlBQUksUUFBUSxDQUFDLElBQUksQ0FBQyxFQUFFO0FBQ2hCLGtCQUFNLElBQUksS0FBSyxDQUFDLEVBQUMsSUFBSSxFQUFFLElBQUksRUFBRSxFQUFFLEVBQUUsRUFBRSxFQUFDLENBQUMsQ0FBQztTQUN6QztBQUNELGVBQU8sSUFBSSxDQUFDO0tBQ2YsQ0FBQyxDQUFDOztBQUVQLFFBQUk7QUFDQSxZQUFJLENBQUMsU0FBUyxDQUFDLEdBQUcsRUFBRSxHQUFHLENBQUMsUUFBUSxDQUFDLEVBQUUsTUFBTSxDQUFDLENBQUM7S0FDOUMsQ0FBQyxPQUFPLENBQUMsRUFBRTtBQUNSLFlBQUksQ0FBQyxZQUFZLEtBQUssRUFBRTtBQUNwQixtQkFBTyxDQUFDLENBQUMsSUFBSSxDQUFDO1NBQ2pCLE1BQU07QUFDSCxrQkFBTSxDQUFDLENBQUM7U0FDWDtLQUNKOztBQUVELFdBQU8sSUFBSSxDQUFDO0NBQ2Y7Ozs7Ozs7Ozs7O0FBVU0sU0FBUyxtQkFBbUIsQ0FBQyxHQUFHLEVBQUUsS0FBSyxFQUFFLEdBQUcsRUFBRTtBQUNqRCxnQkFBWSxDQUFDOztBQUViLFFBQU0sTUFBTSxHQUFHLFVBQVUsQ0FBQyxTQUFTLEVBQy9CLFVBQUEsSUFBSTtlQUFJLElBQUksQ0FBQyxLQUFLLElBQUksS0FBSyxJQUFJLEdBQUcsSUFBSSxJQUFJLENBQUMsR0FBRztLQUFBLEVBQzlDLFVBQUEsSUFBSSxFQUFJO0FBQUUsY0FBTSxJQUFJLEtBQUssQ0FBQyxJQUFJLENBQUMsQ0FBQztLQUFFLENBQ3JDLENBQUM7O0FBRUYsUUFBSTtBQUNBLFlBQUksQ0FBQyxTQUFTLENBQUMsR0FBRyxFQUFFLFNBQVMsRUFBRSxNQUFNLENBQUMsQ0FBQztLQUMxQyxDQUFDLE9BQU8sQ0FBQyxFQUFFO0FBQ1IsWUFBSSxDQUFDLFlBQVksS0FBSyxFQUFFO0FBQ3BCLG1CQUFPLENBQUMsQ0FBQyxJQUFJLENBQUM7U0FDakIsTUFBTTtBQUNILGtCQUFNLENBQUMsQ0FBQztTQUNYO0tBQ0o7O0FBRUQsV0FBTyxJQUFJLENBQUM7Q0FDZjs7QUFFTSxTQUFTLG1CQUFtQixDQUFDLElBQUksRUFBRSxLQUFLLEVBQUUsT0FBTyxFQUFFO0FBQ3RELGFBQVMsQ0FBQyxDQUFDLElBQUksRUFBRSxFQUFFLEVBQUUsUUFBUSxFQUFFO0FBQzNCLGVBQU8sT0FBTyxDQUFDLFFBQVEsSUFBSSxJQUFJLENBQUMsSUFBSSxDQUFDLENBQUMsSUFBSSxFQUFFLEVBQUUsRUFBRSxDQUFDLENBQUMsQ0FBQztLQUN0RDtBQUNELFdBQU8sQ0FBQyxDQUFDLElBQUksRUFBRSxLQUFLLENBQUMsQ0FBQztDQUN6Qjs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7OztBQzFQRCxZQUFZLENBQUM7Ozs7Ozs7Ozs0QkFFVSxpQkFBaUI7O0lBQTVCLEtBQUs7OzRCQUNTLGlCQUFpQjs7SUFBL0IsUUFBUTs7QUFDcEIsSUFBTSxJQUFJLEdBQUcsT0FBTyxDQUFDLGlCQUFpQixDQUFDLENBQUM7O0lBRTNCLFFBQVE7QUFDTixhQURGLFFBQVEsQ0FDTCxLQUFLLEVBQUUsVUFBVSxFQUFFLEtBQUssRUFBRSxRQUFRLEVBQUU7OEJBRHZDLFFBQVE7O0FBRWIsWUFBSSxDQUFDLEtBQUssR0FBRyxLQUFLLENBQUM7QUFDbkIsWUFBSSxDQUFDLFVBQVUsR0FBRyxVQUFVLENBQUM7QUFDN0IsWUFBSSxDQUFDLFNBQVMsR0FBRyxLQUFLLENBQUM7QUFDdkIsWUFBSSxDQUFDLFFBQVEsR0FBRyxRQUFRLENBQUM7O0FBRXpCLFlBQUksQ0FBQyxXQUFXLEdBQUcsVUFBVSxDQUFDLFFBQVEsQ0FBQyxDQUFDO0FBQ3hDLFlBQUksQ0FBQyxhQUFhLEdBQUcsRUFBRSxDQUFDO0FBQ3hCLFlBQUksQ0FBQyxhQUFhLEdBQUcsRUFBRSxDQUFDOztBQUV4QixZQUFJLENBQUMsYUFBYSxHQUFHLEVBQUUsQ0FBQzs7QUFFeEIsWUFBSSxDQUFDLFNBQVMsR0FBRyxJQUFJLEdBQUcsRUFBRSxDQUFDO0FBQzNCLFlBQUksQ0FBQyxjQUFjLEdBQUcsRUFBRSxDQUFDO0tBQzVCOztBQWZRLFlBQVEsV0FpQmpCLFFBQVEsR0FBQSxvQkFBRztBQUNQLGVBQU8sSUFBSSxDQUFDLFNBQVMsS0FBSyxRQUFRLENBQUMsVUFBVSxDQUFDLFdBQVcsQ0FBQztLQUM3RDs7QUFuQlEsWUFBUSxXQXFCakIsa0JBQWtCLEdBQUEsOEJBQUc7QUFDakIsZUFBTyxJQUFJLENBQUMsU0FBUyxLQUFLLFFBQVEsQ0FBQyxVQUFVLENBQUMsZ0JBQWdCLENBQUM7S0FDbEU7O0FBdkJRLFlBQVEsV0F5QmpCLG9CQUFvQixHQUFBLGdDQUFHO0FBQ25CLGVBQU8sSUFBSSxDQUFDLFNBQVMsS0FBSyxRQUFRLENBQUMsVUFBVSxDQUFDLGtCQUFrQixDQUFDO0tBQ3BFOztBQTNCUSxZQUFRLFdBNkJqQixZQUFZLEdBQUEsd0JBQUc7QUFDWCxlQUFPLElBQUksQ0FBQyxTQUFTLEtBQUssUUFBUSxDQUFDLFVBQVUsQ0FBQyxVQUFVLENBQUM7S0FDNUQ7O0FBL0JRLFlBQVEsV0FpQ2pCLGFBQWEsR0FBQSx5QkFBRztBQUNaLGVBQU8sSUFBSSxDQUFDLFNBQVMsS0FBSyxRQUFRLENBQUMsVUFBVSxDQUFDLFdBQVcsQ0FBQztLQUM3RDs7QUFuQ1EsWUFBUSxXQXFDakIsZ0JBQWdCLEdBQUEsNEJBQUc7QUFDZixlQUFPLElBQUksQ0FBQyxTQUFTLEtBQUssUUFBUSxDQUFDLFVBQVUsQ0FBQyxjQUFjLENBQUM7S0FDaEU7O0FBdkNRLFlBQVEsV0F5Q2pCLGdCQUFnQixHQUFBLDRCQUFHO0FBQ2YsZUFBTyxJQUFJLENBQUMsYUFBYSxDQUFDO0tBQzdCOztBQTNDUSxZQUFRLFdBNkNqQixnQkFBZ0IsR0FBQSw0QkFBRztBQUNmLGVBQU8sSUFBSSxDQUFDLGFBQWEsQ0FBQztLQUM3Qjs7QUEvQ1EsWUFBUSxXQWlEakIsV0FBVyxHQUFBLHVCQUFHO0FBQ1YsZUFBTyxJQUFJLENBQUMsZ0JBQWdCLEVBQUUsQ0FBQyxNQUFNLENBQUMsSUFBSSxDQUFDLGdCQUFnQixFQUFFLENBQUMsQ0FBQztLQUNsRTs7QUFuRFEsWUFBUSxXQXFEakIsV0FBVyxHQUFBLHFCQUFDLE9BQU8sRUFBRTtBQUNqQixlQUFPLElBQUksQ0FBQyxhQUFhLElBQUksSUFBSSxDQUFDLGFBQWEsQ0FBQyxPQUFPLENBQUMsT0FBTyxDQUFDLEdBQUcsQ0FBQyxDQUFDLENBQUM7S0FDekU7O0FBdkRRLFlBQVEsV0F5RGpCLFdBQVcsR0FBQSxxQkFBQyxPQUFPLEVBQUU7QUFDakIsZUFBTyxJQUFJLENBQUMsYUFBYSxDQUFDLE9BQU8sQ0FBQyxPQUFPLENBQUMsR0FBRyxDQUFDLENBQUMsQ0FBQztLQUNuRDs7QUEzRFEsWUFBUSxXQTZEakIsTUFBTSxHQUFBLGdCQUFDLE9BQU8sRUFBRTtBQUNaLGVBQU8sSUFBSSxDQUFDLFdBQVcsQ0FBQyxPQUFPLENBQUMsSUFBSSxJQUFJLENBQUMsV0FBVyxDQUFDLE9BQU8sQ0FBQyxDQUFDO0tBQ2pFOztBQS9EUSxZQUFRLFdBaUVqQixtQkFBbUIsR0FBQSw2QkFBQyxPQUFPLEVBQUUsS0FBSyxFQUFFO0FBQ2hDLFlBQUksU0FBUyxHQUFHLElBQUksQ0FBQztBQUNyQixnQkFBTyxLQUFLO0FBQ1IsaUJBQUssUUFBUSxDQUFDLGdCQUFnQixDQUFDLGNBQWM7O0FBRXpDLHVCQUFPLENBQUMsU0FBUyxDQUFDLGtCQUFrQixFQUFFLElBQy9CLENBQUMsU0FBUyxDQUFDLG9CQUFvQixFQUFFLElBQ2pDLENBQUMsU0FBUyxDQUFDLFFBQVEsRUFBRSxFQUFFO0FBQzFCLDZCQUFTLEdBQUcsU0FBUyxDQUFDLEtBQUssQ0FBQztpQkFDL0I7QUFDRCxzQkFBTTtBQUFBLEFBQ1YsaUJBQUssUUFBUSxDQUFDLGdCQUFnQixDQUFDLG1CQUFtQjs7O0FBRzlDLHVCQUFPLFNBQVMsQ0FBQyxhQUFhLEVBQUUsSUFDekIsRUFBRSxTQUFTLENBQUMsWUFBWSxFQUFFLElBQUksU0FBUyxDQUFDLFdBQVcsQ0FBQyxPQUFPLENBQUMsQ0FBQSxBQUFDLEVBQUU7QUFDbEUsNkJBQVMsR0FBRyxTQUFTLENBQUMsS0FBSyxDQUFDO2lCQUMvQjtBQUNELHNCQUFNO0FBQUEsQUFDVixpQkFBSyxRQUFRLENBQUMsZ0JBQWdCLENBQUMsY0FBYyxDQUFDO0FBQzlDLGlCQUFLLFFBQVEsQ0FBQyxnQkFBZ0IsQ0FBQyxnQkFBZ0I7QUFDM0Msc0JBQU07QUFBQSxBQUNWLGlCQUFLLFFBQVEsQ0FBQyxnQkFBZ0IsQ0FBQyx5QkFBeUI7O0FBRXBELG9CQUFJLENBQUMsSUFBSSxDQUFDLFFBQVEsRUFBRSxJQUFJLElBQUksQ0FBQyxRQUFRLEVBQUU7QUFDbkMsMkJBQU8sSUFBSSxDQUFDO2lCQUNmO0FBQ0Qsc0JBQU07QUFBQSxTQUNiOzs7QUFHRCxZQUFJLENBQUMsU0FBUyxDQUFDLE1BQU0sQ0FBQyxPQUFPLENBQUMsRUFBRTtBQUM1QixxQkFBUyxDQUFDLGFBQWEsQ0FBQyxJQUFJLENBQUMsT0FBTyxDQUFDLENBQUM7U0FDekM7O0FBRUQsZUFBTyxTQUFTLENBQUM7S0FDcEI7O0FBckdRLFlBQVEsV0F1R2pCLFdBQVcsR0FBQSxxQkFBQyxPQUFPLEVBQUU7QUFDakIsWUFBSSxDQUFDLGFBQWEsQ0FBQyxJQUFJLENBQUMsT0FBTyxDQUFDLENBQUM7S0FDcEM7O0FBekdRLFlBQVEsV0EyR2pCLGNBQWMsR0FBQSx3QkFBQyxPQUFPLEVBQUU7QUFDcEIsWUFBSSxTQUFTLEdBQUcsSUFBSSxDQUFDO0FBQ3JCLGVBQU8sU0FBUyxJQUFJLENBQUMsU0FBUyxDQUFDLE1BQU0sQ0FBQyxPQUFPLENBQUMsRUFBRTtBQUM1QyxnQkFBSSxTQUFTLENBQUMsUUFBUSxFQUFFLElBQUksQ0FBQyxTQUFTLENBQUMsUUFBUSxFQUFFO0FBQzdDLHNCQUFNO2FBQ1Q7QUFDRCxxQkFBUyxHQUFHLFNBQVMsQ0FBQyxLQUFLLENBQUM7U0FDL0I7Ozs7QUFJRCxlQUFPLFNBQVMsQ0FBQztLQUNwQjs7QUF2SFEsWUFBUSxXQXlIakIsa0JBQWtCLEdBQUEsOEJBQUc7QUFDakIsWUFBSSxTQUFTLEdBQUcsSUFBSSxDQUFDO0FBQ3JCLFlBQU0sUUFBUSxHQUFHLEVBQUUsQ0FBQztBQUNwQixlQUFPLFNBQVMsRUFBRTtBQUNkLHFCQUFTLENBQUMsV0FBVyxFQUFFLENBQUMsT0FBTyxDQUFDLFVBQVUsSUFBSSxFQUFFO0FBQzVDLG9CQUFJLFFBQVEsQ0FBQyxPQUFPLENBQUMsSUFBSSxDQUFDLEtBQUssQ0FBQyxDQUFDLEVBQUU7QUFDL0IsNEJBQVEsQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDLENBQUM7aUJBQ3ZCO2FBQ0osQ0FBQyxDQUFDO0FBQ0gscUJBQVMsR0FBRyxTQUFTLENBQUMsS0FBSyxDQUFDO1NBQy9CO0FBQ0QsZUFBTyxRQUFRLENBQUM7S0FDbkI7O0FBcklRLFlBQVEsV0F1SWpCLFVBQVUsR0FBQSxvQkFBQyxPQUFPLEVBQUU7QUFDaEIsWUFBSSxJQUFJLENBQUMsYUFBYSxDQUFDLE9BQU8sQ0FBQyxPQUFPLENBQUMsS0FBSyxDQUFDLENBQUMsRUFBRTtBQUM1QyxnQkFBSSxDQUFDLGFBQWEsQ0FBQyxJQUFJLENBQUMsT0FBTyxDQUFDLENBQUM7U0FDcEM7S0FDSjs7QUEzSVEsWUFBUSxXQTZJakIsZUFBZSxHQUFBLDJCQUFHO0FBQ2QsZUFBTyxJQUFJLENBQUMsYUFBYSxDQUFDO0tBQzdCOztBQS9JUSxZQUFRLFdBaUpqQixTQUFTLEdBQUEsbUJBQUMsT0FBTyxFQUFFO0FBQ2YsZUFBTyxJQUFJLENBQUMsYUFBYSxDQUFDLE9BQU8sQ0FBQyxPQUFPLENBQUMsR0FBRyxDQUFDLENBQUMsQ0FBQztLQUNuRDs7OztBQW5KUSxZQUFRLFdBc0pqQixXQUFXLEdBQUEscUJBQUMsS0FBSyxFQUFFO0FBQ2YsWUFBSSxJQUFJLENBQUMsU0FBUyxDQUFDLEdBQUcsQ0FBQyxLQUFLLENBQUMsRUFBRTtBQUMzQixtQkFBTyxJQUFJLENBQUMsU0FBUyxDQUFDLEdBQUcsQ0FBQyxLQUFLLENBQUMsQ0FBQztTQUNwQzs7QUFFRCxZQUFNLE1BQU0sR0FBRyxJQUFJLEdBQUcsRUFBRSxDQUFDO0FBQ3pCLFlBQU0sUUFBUSxHQUFHLElBQUksQ0FBQyxnQkFBZ0IsRUFBRSxDQUFDLE1BQU0sQ0FBQyxJQUFJLENBQUMsZ0JBQWdCLEVBQUUsQ0FBQyxDQUFDOztBQUV6RSxhQUFLLElBQUksQ0FBQyxHQUFHLENBQUMsRUFBRSxDQUFDLEdBQUcsUUFBUSxDQUFDLE1BQU0sRUFBRSxDQUFDLEVBQUUsRUFBRTtBQUN0QyxrQkFBTSxDQUFDLEdBQUcsQ0FBQyxRQUFRLENBQUMsQ0FBQyxDQUFDLEVBQUUsSUFBSSxLQUFLLENBQUMsSUFBSSxFQUFFLENBQUMsQ0FBQztTQUM3Qzs7QUFFRCxZQUFJLENBQUMsU0FBUyxDQUFDLEdBQUcsQ0FBQyxLQUFLLEVBQUMsTUFBTSxDQUFDLENBQUM7QUFDakMsZUFBTyxNQUFNLENBQUM7S0FDakI7Ozs7QUFwS1EsWUFBUSxXQXVLakIsYUFBYSxHQUFBLHVCQUFDLEtBQUssRUFBRTtBQUNqQixZQUFNLFFBQVEsR0FBRyxJQUFJLENBQUMsV0FBVyxDQUFDLEtBQUssQ0FBQyxDQUFDO0FBQ3pDLFlBQU0sTUFBTSxHQUFHLEVBQUUsQ0FBQztBQUNsQixZQUFJLENBQUMsZ0JBQWdCLEVBQUUsQ0FBQyxPQUFPLENBQUMsVUFBQSxJQUFJLEVBQUk7QUFDcEMsa0JBQU0sQ0FBQyxJQUFJLENBQUMsUUFBUSxDQUFDLEdBQUcsQ0FBQyxJQUFJLENBQUMsQ0FBQyxDQUFDO1NBQ25DLENBQUMsQ0FBQztBQUNILGVBQU8sTUFBTSxDQUFDO0tBQ2pCOzs7O0FBOUtRLFlBQVEsV0FpTGpCLGdCQUFnQixHQUFBLDBCQUFDLEtBQUssRUFBRTtBQUNwQixZQUFJLENBQUMsSUFBSSxDQUFDLGtCQUFrQixFQUFFO0FBQzFCLGtCQUFNLElBQUksS0FBSyxDQUFDLHVCQUF1QixDQUFDLENBQUM7U0FDNUM7QUFDRCxlQUFPLElBQUksQ0FBQyxXQUFXLENBQUMsS0FBSyxDQUFDLENBQUMsR0FBRyxDQUFDLFdBQVcsQ0FBQyxDQUFDO0tBQ25EOzs7O0FBdExRLFlBQVEsV0F5TGpCLGdCQUFnQixHQUFBLDBCQUFDLEtBQUssRUFBRSxLQUFLLEVBQUU7QUFDM0IsWUFBTSxNQUFNLEdBQUcsSUFBSSxDQUFDLFdBQVcsQ0FBQyxLQUFLLENBQUMsQ0FBQztBQUN2QyxZQUFJLEtBQUssR0FBRyxJQUFJLENBQUM7O0FBRWpCLFlBQUksQ0FBQyxjQUFjLENBQUMsT0FBTyxDQUFDLFVBQVUsRUFBRSxFQUFFO0FBQ3RDLGdCQUFJLEVBQUUsQ0FBQyxLQUFLLEtBQUssS0FBSyxJQUFJLEVBQUUsQ0FBQyxNQUFNLEtBQUssTUFBTSxFQUFFLEtBQUssR0FBRyxFQUFFLENBQUM7U0FDOUQsQ0FBQyxDQUFDOztBQUVILFlBQUksS0FBSyxFQUFFO0FBQ1AsbUJBQU8sS0FBSyxDQUFDO1NBQ2hCLE1BQU07QUFDSCxnQkFBSSxnQkFBZ0IsR0FBRyxJQUFJLEtBQUssQ0FBQyxLQUFLLEVBQUUsTUFBTSxFQUFFLElBQUksQ0FBQyxDQUFDO0FBQ3RELGdCQUFJLENBQUMsY0FBYyxDQUFDLElBQUksQ0FBQyxnQkFBZ0IsQ0FBQyxDQUFDO0FBQzNDLG1CQUFPLGdCQUFnQixDQUFDO1NBQzNCO0tBQ0o7Ozs7QUF4TVEsWUFBUSxXQTJNakIsa0JBQWtCLEdBQUEsNEJBQUMsTUFBTSxFQUFFO0FBQ3ZCLFlBQU0sU0FBUyxHQUFHLElBQUksR0FBRyxFQUFFLENBQUM7QUFDNUIsWUFBSSxDQUFDLGNBQWMsQ0FBQyxPQUFPLENBQUMsVUFBQSxFQUFFLEVBQUk7QUFDOUIsZ0JBQUksRUFBRSxDQUFDLEtBQUssS0FBSyxNQUFNLEVBQUUsU0FBUyxDQUFDLEdBQUcsQ0FBQyxFQUFFLENBQUMsQ0FBQztTQUM5QyxDQUFDLENBQUM7QUFDSCxlQUFPLFNBQVMsQ0FBQztLQUNwQjs7V0FqTlEsUUFBUTs7Ozs7QUFvTnJCLFFBQVEsQ0FBQyxVQUFVLEdBQUc7QUFDbEIsZUFBVyxFQUFFLE1BQU0sQ0FBQyxRQUFRLENBQUM7QUFDN0Isb0JBQWdCLEVBQUUsTUFBTSxDQUFDLGFBQWEsQ0FBQztBQUN2QyxzQkFBa0IsRUFBRSxNQUFNLENBQUMsZUFBZSxDQUFDO0FBQzNDLGtCQUFjLEVBQUUsTUFBTSxDQUFDLFdBQVcsQ0FBQztBQUNuQyxjQUFVLEVBQUUsTUFBTSxDQUFDLE9BQU8sQ0FBQztBQUMzQixlQUFXLEVBQUUsTUFBTSxDQUFDLFFBQVEsQ0FBQztDQUNoQyxDQUFDOztBQUVGLFFBQVEsQ0FBQyxnQkFBZ0IsR0FBRztBQUN4QixrQkFBYyxFQUFFLE1BQU0sQ0FBQyxLQUFLLENBQUM7QUFDN0Isb0JBQWdCLEVBQUUsTUFBTSxDQUFDLE9BQU8sQ0FBQztBQUNqQyxrQkFBYyxFQUFFLE1BQU0sQ0FBQyxLQUFLLENBQUM7QUFDN0IsdUJBQW1CLEVBQUUsTUFBTSxDQUFDLFVBQVUsQ0FBQztBQUN2Qyx3QkFBb0IsRUFBRSxNQUFNLENBQUMsV0FBVyxDQUFDO0FBQ3pDLDZCQUF5QixFQUFFLE1BQU0sQ0FBQyxpQkFBaUIsQ0FBQztDQUN2RCxDQUFDOzs7Ozs7OztBQVFGLFNBQVMsV0FBVyxDQUFDLElBQUksRUFBRTtBQUN2QixXQUFPLElBQUksQ0FBQyxJQUFJLEtBQUsscUJBQXFCLElBQ3RDLElBQUksQ0FBQyxVQUFVLENBQUMsSUFBSSxLQUFLLFNBQVMsSUFDbEMsSUFBSSxDQUFDLFVBQVUsQ0FBQyxHQUFHLENBQUMsS0FBSyxDQUFDLENBQUMsRUFBRSxDQUFDLENBQUMsQ0FBQyxLQUFLLFlBQVksQ0FBQztDQUN6RDs7QUFHRCxJQUFNLHNCQUFzQixHQUFHLElBQUksQ0FBQyxJQUFJLENBQUM7QUFDckMsbUJBQWUsRUFBRSx5QkFBQyxJQUFJLEVBQUUsSUFBa0IsRUFBRSxDQUFDLEVBQUs7WUFBekIsS0FBSyxHQUFOLElBQWtCO1lBQVYsU0FBUyxHQUFqQixJQUFrQjs7QUFDdEMsWUFBSSxLQUFLLEtBQUssUUFBUSxDQUFDLGdCQUFnQixDQUFDLG9CQUFvQixFQUFFO0FBQzFELHFCQUFTLENBQUMsV0FBVyxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsQ0FBQztTQUNwQyxNQUFNLElBQUksS0FBSyxFQUFFO0FBQ2QscUJBQVMsQ0FBQyxtQkFBbUIsQ0FBQyxJQUFJLENBQUMsSUFBSSxFQUFFLEtBQUssQ0FBQyxDQUFDO1NBQ25EO0tBQ0o7QUFDRCxZQUFRLEVBQUUsa0JBQUMsSUFBSSxFQUFFLEtBQWtCLEVBQUUsQ0FBQyxFQUFLO1lBQXpCLEtBQUssR0FBTixLQUFrQjtZQUFWLFNBQVMsR0FBakIsS0FBa0I7O0FBQy9CLFlBQUksVUFBVSxHQUFHLFNBQVM7WUFBRSxVQUFVLFlBQUEsQ0FBQztBQUN2QyxZQUFJLElBQUksQ0FBQyxFQUFFLEVBQUU7QUFDVCxnQkFBTSxRQUFRLEdBQUcsSUFBSSxDQUFDLEVBQUUsQ0FBQyxJQUFJLENBQUM7QUFDOUIsc0JBQVUsR0FBRyxTQUFTLENBQUMsbUJBQW1CLENBQUMsUUFBUSxFQUMvQyxRQUFRLENBQUMsZ0JBQWdCLENBQUMsbUJBQW1CLENBQUMsQ0FBQztTQUN0RDtBQUNELFlBQU0sZUFBZSxHQUFHLElBQUksQ0FBQyxNQUFNLENBQUMsSUFBSSxDQUFDLFVBQUMsR0FBRzttQkFDekMsUUFBUSxDQUFDLGtCQUFrQixDQUFDLEdBQUcsQ0FBQztTQUFBLENBQUMsQ0FBQztBQUN0QyxZQUFJLGVBQWUsRUFBRTtBQUNqQixzQkFBVSxHQUFHLFVBQVUsR0FBRyxJQUFJLFFBQVEsQ0FDbEMsVUFBVSxFQUNWLElBQUksRUFDSixRQUFRLENBQUMsVUFBVSxDQUFDLGNBQWMsRUFDbEMsU0FBUyxDQUFDLFFBQVEsQ0FDckIsQ0FBQztBQUNGLGdCQUFJLENBQUMsUUFBUSxDQUFDLEdBQUcsVUFBVSxDQUFDO1NBQy9CO0FBQ0QsWUFBTSxXQUFXLEdBQUcsU0FBUyxDQUFDLFFBQVEsSUFDakMsSUFBSSxDQUFDLElBQUksQ0FBQyxJQUFJLElBQ2QsSUFBSSxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsQ0FBQyxDQUFDLElBQ2pCLFdBQVcsQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQyxDQUFDLENBQUMsQ0FBQyxBQUFDLENBQUM7QUFDckMsWUFBTSxTQUFTLEdBQUcsSUFBSSxRQUFRLENBQzFCLFVBQVUsRUFDVixJQUFJO0FBQ0osWUFBSSxDQUFDLElBQUksS0FBSyx5QkFBeUIsR0FDbkMsUUFBUSxDQUFDLFVBQVUsQ0FBQyxrQkFBa0IsR0FDcEMsUUFBUSxDQUFDLFVBQVUsQ0FBQyxnQkFBZ0IsRUFDMUMsV0FBVyxDQUNkLENBQUM7QUFDRixZQUFJLENBQUMsSUFBSSxDQUFDLFFBQVEsQ0FBQyxHQUFHLFNBQVMsQ0FBQzs7O0FBR2hDLFlBQU0sZ0JBQWdCLEdBQUcsVUFBVSxJQUFJLFNBQVMsQ0FBQztBQUNqRCxhQUFLLElBQUksQ0FBQyxHQUFHLENBQUMsRUFBRSxDQUFDLEdBQUcsSUFBSSxDQUFDLE1BQU0sQ0FBQyxNQUFNLEVBQUUsQ0FBQyxFQUFFLEVBQUU7QUFDekMsYUFBQyxDQUFDLElBQUksQ0FBQyxNQUFNLENBQUMsQ0FBQyxDQUFDLEVBQ1osQ0FDSSxRQUFRLENBQUMsZ0JBQWdCLENBQUMsb0JBQW9CLEVBQzlDLGdCQUFnQixDQUNuQixFQUNELFNBQVMsQ0FBQyxDQUFDO1NBQ2xCOztBQUVELFlBQUksSUFBSSxDQUFDLFVBQVUsRUFBRTtBQUNqQixhQUFDLENBQUMsSUFBSSxDQUFDLElBQUksRUFBRSxHQUFHLFNBQVMsQ0FBQyxFQUFFLFlBQVksQ0FBQyxDQUFDO1NBQzdDLE1BQU07QUFDSCxnQkFBSSxDQUFDLElBQUksQ0FBQyxjQUFjLENBQUMsSUFBSSxDQUFDLElBQUksRUFBRSxHQUFHLFNBQVMsQ0FBQyxFQUFFLENBQUMsQ0FBQyxDQUFDO1NBQ3pEO0tBQ0o7O0FBRUQsZ0JBQVksRUFBRSxzQkFBQyxJQUFJLEVBQUUsS0FBYSxFQUFFLENBQUMsRUFBSztZQUFsQixTQUFTLEdBQVosS0FBYTs7QUFDOUIsWUFBSSxRQUFRLFlBQUEsQ0FBQztBQUNiLFlBQUksU0FBUyxDQUFDLFFBQVEsRUFBRTtBQUNwQixvQkFBUSxHQUFHLElBQUksUUFBUSxDQUNuQixTQUFTLEVBQ1QsSUFBSSxFQUNKLFFBQVEsQ0FBQyxVQUFVLENBQUMsV0FBVyxFQUMvQixTQUFTLENBQUMsUUFBUSxDQUNyQixDQUFDO0FBQ0YsZ0JBQUksQ0FBQyxRQUFRLENBQUMsR0FBRyxRQUFRLENBQUM7U0FDN0IsTUFBTTtBQUNILG9CQUFRLEdBQUcsU0FBUyxDQUFDO1NBQ3hCO0FBQ0QsWUFBSSxJQUFJLENBQUMsSUFBSSxFQUFFLENBQUMsQ0FBQyxJQUFJLENBQUMsSUFBSSxFQUFFLEdBQUcsUUFBUSxDQUFDLEVBQUUsU0FBUyxDQUFDLENBQUM7QUFDckQsWUFBSSxJQUFJLENBQUMsSUFBSSxFQUFFLENBQUMsQ0FBQyxJQUFJLENBQUMsSUFBSSxFQUFFLEdBQUcsUUFBUSxDQUFDLEVBQUUsWUFBWSxDQUFDLENBQUM7QUFDeEQsWUFBSSxJQUFJLENBQUMsTUFBTSxFQUFFLENBQUMsQ0FBQyxJQUFJLENBQUMsTUFBTSxFQUFFLEdBQUcsUUFBUSxDQUFDLEVBQUUsWUFBWSxDQUFDLENBQUM7O0FBRTVELFNBQUMsQ0FBQyxJQUFJLENBQUMsSUFBSSxFQUFFLEdBQUcsUUFBUSxDQUFDLEVBQUUsU0FBUyxDQUFDLENBQUM7S0FDekM7O0FBRUQsdUJBQW1CLEVBQUUsNkJBQUMsSUFBSSxFQUFFLEtBQWEsRUFBRSxDQUFDLEVBQUs7WUFBbEIsU0FBUyxHQUFaLEtBQWE7O0FBQ3JDLFlBQUksS0FBSyxZQUFBLENBQUM7QUFDVixnQkFBTyxJQUFJLENBQUMsSUFBSTtBQUNaLGlCQUFLLEtBQUs7QUFDTixxQkFBSyxHQUFHLFFBQVEsQ0FBQyxnQkFBZ0IsQ0FBQyxjQUFjLENBQUM7QUFDakQsc0JBQU07QUFBQSxBQUNWLGlCQUFLLEtBQUs7QUFDTixxQkFBSyxHQUFHLFFBQVEsQ0FBQyxnQkFBZ0IsQ0FBQyxjQUFjLENBQUM7QUFDakQsc0JBQU07QUFBQSxBQUNWLGlCQUFLLE9BQU87QUFDUixxQkFBSyxHQUFHLFFBQVEsQ0FBQyxnQkFBZ0IsQ0FBQyxnQkFBZ0IsQ0FBQztBQUNuRCxzQkFBTTtBQUFBLFNBQ2I7O0FBRUQsYUFBSyxJQUFJLENBQUMsR0FBRyxDQUFDLEVBQUUsQ0FBQyxHQUFHLElBQUksQ0FBQyxZQUFZLENBQUMsTUFBTSxFQUFFLENBQUMsRUFBRSxFQUFFO0FBQy9DLGFBQUMsQ0FBQyxJQUFJLENBQUMsWUFBWSxDQUFDLENBQUMsQ0FBQyxFQUFFLENBQUMsS0FBSyxFQUFFLFNBQVMsQ0FBQyxFQUFFLFNBQVMsQ0FBQyxDQUFDO1NBQzFEO0tBQ0o7O0FBRUQsZ0JBQVksRUFBRSxzQkFBQyxJQUFJLEVBQUUsS0FBYSxFQUFFLENBQUMsRUFBSztZQUFsQixTQUFTLEdBQVosS0FBYTs7QUFDOUIsU0FBQyxDQUFDLElBQUksQ0FBQyxLQUFLLEVBQUUsR0FBRyxTQUFTLENBQUMsRUFBRSxTQUFTLENBQUMsQ0FBQztBQUN4QyxZQUFJLElBQUksQ0FBQyxPQUFPLEVBQUU7QUFDZCxhQUFDLENBQUMsSUFBSSxDQUFDLE9BQU8sRUFBRSxHQUFHLFNBQVMsQ0FBQyxFQUFFLFNBQVMsQ0FBQyxDQUFDO1NBQzdDO0FBQ0QsWUFBSSxJQUFJLENBQUMsU0FBUyxFQUFFO0FBQ2hCLGFBQUMsQ0FBQyxJQUFJLENBQUMsU0FBUyxFQUFFLEdBQUcsU0FBUyxDQUFDLEVBQUUsU0FBUyxDQUFDLENBQUM7U0FDL0M7S0FDSjs7QUFFRCxlQUFXLEVBQUUscUJBQUMsSUFBSSxFQUFFLEtBQWEsRUFBRSxDQUFDLEVBQUs7WUFBbEIsU0FBUyxHQUFaLEtBQWE7O0FBQzdCLFlBQU0sVUFBVSxHQUFHLElBQUksUUFBUSxDQUMzQixTQUFTLEVBQ1QsSUFBSSxFQUNKLFFBQVEsQ0FBQyxVQUFVLENBQUMsVUFBVSxFQUM5QixTQUFTLENBQUMsUUFBUSxDQUNyQixDQUFDO0FBQ0YsU0FBQyxDQUFDLElBQUksQ0FBQyxLQUFLLEVBQ1IsQ0FDSSxRQUFRLENBQUMsZ0JBQWdCLENBQUMsb0JBQW9CLEVBQzlDLFVBQVUsQ0FDYixFQUNELFNBQVMsQ0FBQyxDQUFDO0FBQ2YsWUFBSSxDQUFDLElBQUksQ0FBQyxRQUFRLENBQUMsR0FBRyxVQUFVLENBQUM7QUFDakMsWUFBSSxDQUFDLElBQUksQ0FBQyxjQUFjLENBQUMsSUFBSSxDQUFDLElBQUksRUFBRSxHQUFHLFVBQVUsQ0FBQyxFQUFFLENBQUMsQ0FBQyxDQUFDO0tBQzFEOzs7QUFHRCxrQkFBYyxFQUFFLHdCQUFDLElBQUksRUFBRSxLQUFhLEVBQUUsQ0FBQyxFQUFLO1lBQWxCLFNBQVMsR0FBWixLQUFhOztBQUNoQyxZQUFJLE9BQU8sWUFBQSxDQUFDO0FBQ1osWUFBSSxTQUFTLENBQUMsUUFBUSxFQUFFO0FBQ3BCLG1CQUFPLEdBQUcsSUFBSSxRQUFRLENBQ2xCLFNBQVMsRUFDVCxJQUFJLEVBQ0osUUFBUSxDQUFDLFVBQVUsQ0FBQyxXQUFXLEVBQy9CLFNBQVMsQ0FBQyxRQUFRLENBQ3JCLENBQUM7QUFDRixnQkFBSSxDQUFDLFFBQVEsQ0FBQyxHQUFHLE9BQU8sQ0FBQztTQUM1QixNQUFNO0FBQ0gsbUJBQU8sR0FBRyxTQUFTLENBQUM7U0FDdkI7QUFDRCxZQUFJLENBQUMsSUFBSSxDQUFDLGNBQWMsQ0FBQyxJQUFJLEVBQUUsR0FBRyxPQUFPLENBQUMsRUFBRSxDQUFDLENBQUMsQ0FBQztLQUNsRDtDQUNKLENBQUMsQ0FBQzs7O0FBR0gsSUFBTSxzQkFBc0IsR0FBRyxJQUFJLENBQUMsSUFBSSxDQUFDO0FBQ3JDLG1CQUFlLEVBQUUseUJBQUMsSUFBSSxFQUFFLFNBQVMsRUFBRSxDQUFDLEVBQUs7QUFDckMsU0FBQyxDQUFDLElBQUksRUFBRSxTQUFTLEVBQUUsWUFBWSxDQUFDLENBQUM7S0FDcEM7O0FBRUQsY0FBVSxFQUFFLG9CQUFDLElBQUksRUFBRSxTQUFTLEVBQUUsQ0FBQyxFQUFLO0FBQ2hDLFlBQUksUUFBUSxDQUFDLGFBQWEsQ0FBQyxJQUFJLENBQUMsRUFBRTs7QUFFOUIsbUJBQU87U0FDVjtBQUNELFlBQUksS0FBSyxHQUFHLFNBQVMsQ0FBQztBQUN0QixZQUFNLE9BQU8sR0FBRyxJQUFJLENBQUMsSUFBSSxDQUFDOztBQUUxQixlQUFPLEtBQUssSUFBSSxDQUFDLEtBQUssQ0FBQyxNQUFNLENBQUMsT0FBTyxDQUFDLEVBQUU7QUFDcEMsZ0JBQUksT0FBTyxLQUFLLFdBQVcsSUFBSSxLQUFLLENBQUMsa0JBQWtCLEVBQUUsRUFBRTtBQUN2RCxxQkFBSyxDQUFDLGtCQUFrQixHQUFHLElBQUksQ0FBQzs7QUFFaEMscUJBQUssQ0FBQyxtQkFBbUIsQ0FBQyxPQUFPLEVBQUUsUUFBUSxDQUFDLGdCQUFnQixDQUFDLGNBQWMsQ0FBQyxDQUFDO0FBQzdFLHNCQUFNO2FBQ1Q7QUFDRCxnQkFBSSxLQUFLLENBQUMsUUFBUSxFQUFFLEVBQUU7QUFDbEIscUJBQUssQ0FBQyxtQkFBbUIsQ0FBQyxPQUFPLEVBQUUsUUFBUSxDQUFDLGdCQUFnQixDQUFDLHlCQUF5QixDQUFDLENBQUM7QUFDeEYsc0JBQU07YUFDVDtBQUNELGlCQUFLLEdBQUcsS0FBSyxDQUFDLEtBQUssQ0FBQztTQUN2QjtBQUNELFlBQUksS0FBSyxDQUFDLE1BQU0sQ0FBQyxPQUFPLENBQUMsRUFBRTtBQUN2QixpQkFBSyxDQUFDLFVBQVUsQ0FBQyxPQUFPLENBQUMsQ0FBQztTQUM3QjtLQUNKOztBQUVELG1CQUFlLEVBQUUseUJBQUMsSUFBSSxFQUFFLFNBQVMsRUFBRSxDQUFDLEVBQUs7QUFDckMsWUFBSSxLQUFLLEdBQUcsU0FBUyxDQUFDO0FBQ3RCLGVBQU8sS0FBSyxDQUFDLFlBQVksRUFBRSxJQUFJLEtBQUssQ0FBQyxhQUFhLEVBQUUsRUFBRTtBQUNsRCxpQkFBSyxHQUFHLEtBQUssQ0FBQyxLQUFLLENBQUM7U0FDdkI7QUFDRCxZQUFJLENBQUMsS0FBSyxDQUFDLFFBQVEsRUFBRSxJQUFJLElBQUksQ0FBQyxRQUFRLEtBQUssSUFBSSxFQUFFO0FBQzdDLGlCQUFLLENBQUMscUJBQXFCLEdBQUcsSUFBSSxDQUFDO1NBQ3RDO0FBQ0QsWUFBSSxJQUFJLENBQUMsUUFBUSxFQUFFO0FBQ2YsYUFBQyxDQUFDLElBQUksQ0FBQyxRQUFRLEVBQUUsU0FBUyxFQUFFLFNBQVMsQ0FBQyxDQUFDO1NBQzFDO0tBQ0o7O0FBRUQsWUFBUSxFQUFFLGtCQUFDLElBQUksRUFBRSxTQUFTLEVBQUUsQ0FBQyxFQUFLOztBQUU5QixZQUFJLElBQUksQ0FBQyxFQUFFLEVBQUUsQ0FBQyxDQUFDLElBQUksQ0FBQyxFQUFFLEVBQUUsU0FBUyxDQUFDLENBQUM7QUFDbkMsU0FBQyxDQUFDLElBQUksQ0FBQyxJQUFJLEVBQUUsU0FBUyxDQUFDLENBQUM7S0FDM0I7O0FBRUQsYUFBUyxFQUFFLG1CQUFDLElBQUksRUFBRSxTQUFTLEVBQUUsQ0FBQyxFQUFLO0FBQy9CLFNBQUMsQ0FBQyxJQUFJLEVBQUUsSUFBSSxDQUFDLFFBQVEsQ0FBQyxJQUFJLFNBQVMsQ0FBQyxDQUFDO0tBQ3hDOztBQUVELGtCQUFjLEVBQUUsd0JBQUMsSUFBSSxFQUFFLFNBQVMsRUFBRSxDQUFDLEVBQUs7O0FBRXBDLFlBQUksQ0FBQyxJQUFJLENBQUMsY0FBYyxDQUFDLElBQUksRUFBRSxJQUFJLENBQUMsUUFBUSxDQUFDLElBQUksU0FBUyxFQUFFLENBQUMsQ0FBQyxDQUFDO0tBQ2xFO0NBQ0osQ0FBQyxDQUFDOztBQUdJLFNBQVMsaUJBQWlCLENBQUMsR0FBRyxFQUFFLFNBQVMsRUFBRTtBQUM5QyxPQUFHLENBQUMsUUFBUSxDQUFDLEdBQUcsU0FBUyxDQUFDOztBQUUxQixhQUFTLENBQUMsUUFBUSxHQUFHLFNBQVMsQ0FBQyxRQUFRLElBQ2xDLEdBQUcsQ0FBQyxJQUFJLENBQUMsQ0FBQyxDQUFDLElBQUksV0FBVyxDQUFDLEdBQUcsQ0FBQyxJQUFJLENBQUMsQ0FBQyxDQUFDLENBQUMsQUFBQyxDQUFDOztBQUU5QyxRQUFJLENBQUMsU0FBUyxDQUFDLEdBQUcsRUFBRSxHQUFHLFNBQVMsQ0FBQyxFQUFFLHNCQUFzQixDQUFDLENBQUM7QUFDM0QsUUFBSSxDQUFDLFNBQVMsQ0FBQyxHQUFHLEVBQUUsU0FBUyxFQUFFLHNCQUFzQixDQUFDLENBQUM7QUFDdkQsV0FBTyxHQUFHLENBQUM7Q0FDZDs7OztJQUdLLEtBQUs7QUFDSSxhQURULEtBQUssQ0FDSyxLQUFLLEVBQUUsTUFBTSxFQUFFLEVBQUUsRUFBRTs4QkFEN0IsS0FBSzs7QUFFSCxZQUFJLENBQUMsS0FBSyxHQUFHLEtBQUssQ0FBQztBQUNuQixZQUFJLENBQUMsTUFBTSxHQUFHLE1BQU0sQ0FBQztBQUNyQixZQUFJLENBQUMsRUFBRSxHQUFHLEVBQUUsQ0FBQztLQUNoQjs7OztBQUxDLFNBQUssV0FRUCxTQUFTLEdBQUEsbUJBQUMsT0FBTyxFQUFFO0FBQ2YsWUFBSSxJQUFJLEdBQUcsSUFBSSxDQUFDO0FBQ2hCLGVBQU8sSUFBSSxJQUFJLElBQUksRUFBRTtBQUNqQixnQkFBSSxJQUFJLENBQUMsTUFBTSxDQUFDLEdBQUcsQ0FBQyxPQUFPLENBQUMsRUFBRTtBQUMxQix1QkFBTyxJQUFJLENBQUMsTUFBTSxDQUFDLEdBQUcsQ0FBQyxPQUFPLENBQUMsQ0FBQzthQUNuQztBQUNELGdCQUFJLEdBQUcsSUFBSSxDQUFDLEtBQUssQ0FBQztTQUNyQjs7QUFFRCxlQUFPLEtBQUssQ0FBQyxRQUFRLENBQUM7S0FDekI7Ozs7QUFsQkMsU0FBSyxXQXFCUCxnQ0FBZ0MsR0FBQSw0Q0FBRztBQUMvQixZQUFJLElBQUksR0FBRyxJQUFJLENBQUM7QUFDaEIsZUFBTyxJQUFJLENBQUMsRUFBRSxDQUFDLFlBQVksRUFBRSxJQUFJLElBQUksQ0FBQyxFQUFFLENBQUMsYUFBYSxFQUFFLEVBQUU7QUFDdEQsZ0JBQUksR0FBRyxJQUFJLENBQUMsS0FBSyxDQUFDO1NBQ3JCO0FBQ0QsZUFBTyxJQUFJLENBQUM7S0FDZjs7V0EzQkMsS0FBSzs7Ozs7Ozs7NEJDcmZlLGlCQUFpQjs7SUFBL0IsUUFBUTs7Ozs7Ozs7QUFEcEIsSUFBTSxJQUFJLEdBQUcsT0FBTyxDQUFDLGlCQUFpQixDQUFDLENBQUM7QUFTeEMsU0FBUyxhQUFhLENBQUMsR0FBRyxFQUFFLEdBQUcsRUFBRTtBQUM3QixnQkFBWSxDQUFDO0FBQ2IsUUFBTSxLQUFLLEdBQUcsUUFBUSxDQUFDLGdCQUFnQixDQUFDLEdBQUcsRUFBRSxHQUFHLENBQUMsQ0FBQztBQUNsRCxRQUFJLENBQUMsS0FBSyxFQUFFOztBQUVSLGVBQU8sSUFBSSxDQUFDO0tBQ2Y7O0FBRUQsUUFBTSxJQUFJLEdBQUcsa0JBQWtCLENBQUMsS0FBSyxDQUFDLENBQUMsR0FBRyxDQUFDLFVBQUEsSUFBSTtlQUMxQyxFQUFDLEtBQUssRUFBRSxJQUFJLENBQUMsS0FBSyxFQUFFLEdBQUcsRUFBRSxJQUFJLENBQUMsR0FBRyxFQUFDO0tBQUMsQ0FDdkMsQ0FBQztBQUNGLFFBQUksQ0FBQyxPQUFPLEdBQUcsS0FBSyxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUM7O0FBRS9CLFdBQU8sSUFBSSxDQUFDO0NBQ2Y7Ozs7Ozs7QUFPRCxTQUFTLGtCQUFrQixDQUFDLEtBQUssRUFBRTtBQUMvQixnQkFBWSxDQUFDO0FBQ2IsUUFBTSxPQUFPLEdBQUcsS0FBSyxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUM7QUFDaEMsUUFBTSxHQUFHLEdBQUcsS0FBSyxDQUFDLEVBQUUsQ0FBQyxjQUFjLENBQUMsT0FBTyxDQUFDLENBQUM7QUFDN0MsUUFBSSxDQUFDLEdBQUcsRUFBRSxPQUFPLEVBQUUsQ0FBQzs7QUFFcEIsUUFBTSxJQUFJLEdBQUcsRUFBRSxDQUFDOztBQUVoQixRQUFNLE1BQU0sR0FBRyxJQUFJLENBQUMsSUFBSSxDQUFDO0FBQ3JCLGtCQUFVLEVBQUUsb0JBQUMsSUFBSSxFQUFFLEVBQUUsRUFBSztBQUN0QixnQkFBSSxJQUFJLENBQUMsSUFBSSxLQUFLLE9BQU8sRUFBRSxPQUFPO0FBQ2xDLGdCQUFJLEdBQUcsS0FBSyxFQUFFLENBQUMsY0FBYyxDQUFDLE9BQU8sQ0FBQyxFQUFFO0FBQ3BDLG9CQUFJLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQyxDQUFDO2FBQ25CO1NBQ0o7S0FDSixFQUFFLFFBQVEsQ0FBQyxTQUFTLENBQUMsQ0FBQzs7QUFFdkIsUUFBSSxDQUFDLFNBQVMsQ0FBQyxHQUFHLENBQUMsVUFBVSxFQUFFLEdBQUcsQ0FBQyxVQUFVLENBQUMsUUFBUSxDQUFDLEVBQUUsTUFBTSxDQUFDLENBQUM7QUFDakUsV0FBTyxJQUFJLENBQUM7Q0FDZjs7QUFFRCxPQUFPLENBQUMsYUFBYSxHQUFHLGFBQWEsQ0FBQzs7OztBQ25EdEM7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBOzs7OztBQy91R0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7Ozs7O0FDOXZDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTs7OztBQ3ZYQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7O0FDdkJBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBOztBQzFGQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7OztBQ0xBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0EiLCJmaWxlIjoiZ2VuZXJhdGVkLmpzIiwic291cmNlUm9vdCI6IiIsInNvdXJjZXNDb250ZW50IjpbIihmdW5jdGlvbiBlKHQsbixyKXtmdW5jdGlvbiBzKG8sdSl7aWYoIW5bb10pe2lmKCF0W29dKXt2YXIgYT10eXBlb2YgcmVxdWlyZT09XCJmdW5jdGlvblwiJiZyZXF1aXJlO2lmKCF1JiZhKXJldHVybiBhKG8sITApO2lmKGkpcmV0dXJuIGkobywhMCk7dmFyIGY9bmV3IEVycm9yKFwiQ2Fubm90IGZpbmQgbW9kdWxlICdcIitvK1wiJ1wiKTt0aHJvdyBmLmNvZGU9XCJNT0RVTEVfTk9UX0ZPVU5EXCIsZn12YXIgbD1uW29dPXtleHBvcnRzOnt9fTt0W29dWzBdLmNhbGwobC5leHBvcnRzLGZ1bmN0aW9uKGUpe3ZhciBuPXRbb11bMV1bZV07cmV0dXJuIHMobj9uOmUpfSxsLGwuZXhwb3J0cyxlLHQsbixyKX1yZXR1cm4gbltvXS5leHBvcnRzfXZhciBpPXR5cGVvZiByZXF1aXJlPT1cImZ1bmN0aW9uXCImJnJlcXVpcmU7Zm9yKHZhciBvPTA7bzxyLmxlbmd0aDtvKyspcyhyW29dKTtyZXR1cm4gc30pIiwiZXhwb3J0IGNvbnN0IG9wdGlvbnMgPSB7XG4gICAgYWNvcm5PcHRpb246IHtcbiAgICAgICAgZWNtYVZlcnNpb246IDYsXG4gICAgICAgIC8vIHNvdXJjZVR5cGU6ICdzY3JpcHQnIG9yICdtb2R1bGUnXG4gICAgICAgIC8vICdtb2R1bGUnIGlzIHVzZWQgZm9yIEVTNiBtb2R1bGVzIGFuZFxuICAgICAgICAvLyAndXNlIHN0cmljdCcgYXNzdW1lZCBmb3IgdGhvc2UgbW9kdWxlcy5cbiAgICAgICAgLy8gVGhpcyBvcHRpb24gaXMgYWxzbyB1c2VkIGJ5IHRoZSBhbmFseXplci5cbiAgICAgICAgc291cmNlVHlwZTogJ3NjcmlwdCdcbiAgICB9LFxuICAgIC8vIEF0IHRoZSBzdGFydCBvZiBwcm9ncmFtIGFuZCBlYWNoIGZ1bmN0aW9uLFxuICAgIC8vIGNoZWNrICd1c2Ugc3RyaWN0J1xuICAgIC8vIG1heWJlIHdlIGRvIG5vdCBuZWVkIHRoaXMgb3B0aW9uXG4gICAgZGV0ZWN0VXNlU3RyaWN0OiB0cnVlLFxuXG4gICAgLy8gY29udGV4dCBpbnNlbnNpdGl2ZVxuICAgIHNlbnNpdGl2aXR5UGFyYW1ldGVyOiB7XG4gICAgICAgIG1heERlcHRoSzogMCxcbiAgICAgICAgY29udGV4dExlbmd0aE9mRnVuYzogZnVuY3Rpb24gKGZuKSB7XG4gICAgICAgICAgICByZXR1cm4gMDtcbiAgICAgICAgfVxuICAgIH1cbn07XG4iLCIndXNlIHN0cmljdCc7XG5cbmltcG9ydCAqIGFzIHR5cGVzIGZyb20gJy4uL2RvbWFpbnMvdHlwZXMnXG5pbXBvcnQgKiBhcyBteVdhbGtlciBmcm9tICcuLi91dGlsL215V2Fsa2VyJ1xuaW1wb3J0ICogYXMgY3NjIGZyb20gJy4uL2RvbWFpbnMvY29udGV4dCdcbmNvbnN0IHdhbGsgPSByZXF1aXJlKCdhY29ybi9kaXN0L3dhbGsnKTtcbmNvbnN0IHN0YXR1cyA9IHJlcXVpcmUoJy4uL2RvbWFpbnMvc3RhdHVzJyk7XG5jb25zdCBjc3RyID0gcmVxdWlyZSgnLi9jb25zdHJhaW50cycpO1xuXG4vLyByZXR1cm5zIFthY2Nlc3MgdHlwZSwgcHJvcCB2YWx1ZV1cbmZ1bmN0aW9uIHByb3BBY2Nlc3Mobm9kZSkge1xuICAgIGNvbnN0IHByb3AgPSBub2RlLnByb3BlcnR5O1xuICAgIGlmIChwcm9wLnR5cGUgPT09ICdJZGVudGlmaWVyJyAmJiBteVdhbGtlci5pc0R1bW15SWROb2RlKG5vZGUucHJvcGVydHkpKSB7XG4gICAgICAgIHJldHVybiBbJ2R1bW15UHJvcGVydHknXVxuICAgIH1cbiAgICBpZiAoIW5vZGUuY29tcHV0ZWQpIHtcbiAgICAgICAgcmV0dXJuIFsnZG90QWNjZXNzJywgcHJvcC5uYW1lXTtcbiAgICB9XG4gICAgaWYgKHByb3AudHlwZSA9PT0gJ0xpdGVyYWwnKSB7XG4gICAgICAgIGlmICh0eXBlb2YgcHJvcC52YWx1ZSA9PT0gJ3N0cmluZycpXG4gICAgICAgICAgICByZXR1cm4gWydzdHJpbmdMaXRlcmFsJywgcHJvcC52YWx1ZV07XG4gICAgICAgIGlmICh0eXBlb2YgcHJvcC52YWx1ZSA9PT0gJ251bWJlcicpXG4gICAgICAgICAgICAvLyBjb252ZXJ0IG51bWJlciB0byBzdHJpbmdcbiAgICAgICAgICAgIHJldHVybiBbJ251bWJlckxpdGVyYWwnLCBwcm9wLnZhbHVlICsgJyddO1xuICAgIH1cbiAgICByZXR1cm4gWydjb21wdXRlZCcsIG51bGxdO1xufVxuXG5mdW5jdGlvbiB1bm9wUmVzdWx0VHlwZShvcCkge1xuICAgIHN3aXRjaCAob3ApIHtcbiAgICAgICAgY2FzZSAnKyc6IGNhc2UgJy0nOiBjYXNlICd+JzpcbiAgICAgICAgICAgIHJldHVybiB0eXBlcy5QcmltTnVtYmVyO1xuICAgICAgICBjYXNlICchJzpcbiAgICAgICAgICAgIHJldHVybiB0eXBlcy5QcmltQm9vbGVhbjtcbiAgICAgICAgY2FzZSAndHlwZW9mJzpcbiAgICAgICAgICAgIHJldHVybiB0eXBlcy5QcmltU3RyaW5nO1xuICAgICAgICBjYXNlICd2b2lkJzogY2FzZSAnZGVsZXRlJzpcbiAgICAgICAgICAgIHJldHVybiBudWxsO1xuICAgIH1cbn1cblxuZnVuY3Rpb24gYmlub3BJc0Jvb2xlYW4ob3ApIHtcbiAgICBzd2l0Y2ggKG9wKSB7XG4gICAgICAgIGNhc2UgJz09JzogY2FzZSAnIT0nOiBjYXNlICc9PT0nOiBjYXNlICchPT0nOlxuICAgICAgICBjYXNlICc8JzogY2FzZSAnPic6IGNhc2UgJz49JzogY2FzZSAnPD0nOlxuICAgICAgICBjYXNlICdpbic6IGNhc2UgJ2luc3RhbmNlb2YnOlxuICAgICAgICAgICAgcmV0dXJuIHRydWU7XG4gICAgfVxuICAgIHJldHVybiBmYWxzZTtcbn1cblxuLy8gVG8gcHJldmVudCByZWN1cnNpb24sXG4vLyB3ZSByZW1lbWJlciB0aGUgc3RhdHVzIHVzZWQgaW4gYWRkQ29uc3RyYWludHNcbmNvbnN0IHZpc2l0ZWRTdGF0dXMgPSBbXTtcbmZ1bmN0aW9uIGNsZWFyQ29uc3RyYWludHMoKSB7XG4gICAgdmlzaXRlZFN0YXR1cy5sZW5ndGggPSAwO1xufVxuXG5sZXQgcnRDWDtcbmZ1bmN0aW9uIGFkZENvbnN0cmFpbnRzKGFzdE5vZGUsIGluaXRTdGF0dXMsIG5ld1J0Q1gpIHtcblxuICAgIC8vIHNldCBydENYXG4gICAgcnRDWCA9IG5ld1J0Q1ggfHwgcnRDWDtcbiAgICBjb25zdCDEiCA9IHJ0Q1guxIg7XG5cbiAgICAvLyBDaGVjayB3aGV0aGVyIHdlIGhhdmUgcHJvY2Vzc2VkICdpbml0U3RhdHVzJyBiZWZvcmVcbiAgICBmb3IgKGxldCBpPTA7IGkgPCB2aXNpdGVkU3RhdHVzLmxlbmd0aDsgaSsrKSB7XG4gICAgICAgIGlmIChpbml0U3RhdHVzLmVxdWFscyh2aXNpdGVkU3RhdHVzW2ldKSkge1xuICAgICAgICAgICAgIC8vIElmIHNvLCBkbyBub3RoaW5nXG4gICAgICAgICAgICAgLy8gc2lnbmlmeWluZyB3ZSBkaWRuJ3QgYWRkIGNvbnN0cmFpbnRzXG4gICAgICAgICAgICAgcmV0dXJuIGZhbHNlO1xuICAgICAgICAgfVxuICAgIH1cbiAgICAvLyBJZiB0aGUgaW5pdFN0YXR1cyBpcyBuZXcsIHB1c2ggaXQuXG4gICAgLy8gV2UgZG8gbm90IHJlY29yZCBhc3Qgc2luY2UgYXN0IG5vZGUgZGVwZW5kcyBvbiB0aGUgc3RhdHVzXG4gICAgdmlzaXRlZFN0YXR1cy5wdXNoKGluaXRTdGF0dXMpO1xuXG4gICAgZnVuY3Rpb24gcmVhZE1lbWJlcihub2RlLCBjdXJTdGF0dXMsIGMpIHtcbiAgICAgICAgY29uc3QgcmV0ID0gxIguZ2V0KG5vZGUsIGN1clN0YXR1cy5kZWx0YSk7XG4gICAgICAgIGNvbnN0IG9iakFWYWwgPSBjKG5vZGUub2JqZWN0LCBjdXJTdGF0dXMsIHVuZGVmaW5lZCk7XG4gICAgICAgIGlmIChub2RlLnByb3BlcnR5LnR5cGUgIT09ICdJZGVudGlmaWVyJykge1xuICAgICAgICAgICAgLy8gcmV0dXJuIGZyb20gcHJvcGVydHkgaXMgaWdub3JlZFxuICAgICAgICAgICAgYyhub2RlLnByb3BlcnR5LCBjdXJTdGF0dXMsIHVuZGVmaW5lZCk7XG4gICAgICAgIH1cbiAgICAgICAgY29uc3QgW2FjY1R5cGUsIHByb3BOYW1lXSA9IHByb3BBY2Nlc3Mobm9kZSk7XG5cbiAgICAgICAgaWYgKGFjY1R5cGUgIT09ICdkdW1teVByb3BlcnR5Jykge1xuICAgICAgICAgICAgb2JqQVZhbC5wcm9wYWdhdGUobmV3IGNzdHIuUmVhZFByb3AocHJvcE5hbWUsIHJldCkpO1xuICAgICAgICB9XG5cbiAgICAgICAgLy8gcmV0dXJucyBBVmFsIGZvciByZWNlaXZlciBhbmQgcmVhZCBtZW1iZXJcbiAgICAgICAgcmV0dXJuIFtvYmpBVmFsLCByZXRdO1xuICAgIH1cblxuICAgIC8vIGNvbnN0cmFpbnQgZ2VuZXJhdGluZyB3YWxrZXIgZm9yIGV4cHJlc3Npb25zXG4gICAgY29uc3QgY29uc3RyYWludEdlbmVyYXRvciA9IHdhbGsubWFrZSh7XG5cbiAgICAgICAgSWRlbnRpZmllcjogZnVuY3Rpb24gKG5vZGUsIGN1clN0YXR1cywgYykge1xuICAgICAgICAgICAgaWYgKG15V2Fsa2VyLmlzRHVtbXlJZE5vZGUobm9kZSkpIHtcbiAgICAgICAgICAgICAgICAvLyBSZXR1cm4gQVZhbE51bGwgZm9yIGR1bW15IGlkZW50aXR5IG5vZGVcbiAgICAgICAgICAgICAgICByZXR1cm4gdHlwZXMuQVZhbE51bGw7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBjb25zdCBhdiA9IGN1clN0YXR1cy5zYy5nZXRBVmFsT2Yobm9kZS5uYW1lKTtcbiAgICAgICAgICAgIC8vIHVzZSBhdmFsIGluIHRoZSBzY29wZVxuICAgICAgICAgICAgxIguc2V0KG5vZGUsIGN1clN0YXR1cy5kZWx0YSwgYXYpO1xuICAgICAgICAgICAgcmV0dXJuIGF2O1xuICAgICAgICB9LFxuXG4gICAgICAgIFRoaXNFeHByZXNzaW9uOiBmdW5jdGlvbiAobm9kZSwgY3VyU3RhdHVzLCBjKSB7XG4gICAgICAgICAgICBjb25zdCBhdiA9IGN1clN0YXR1cy5zZWxmO1xuICAgICAgICAgICAgLy8gdXNlIGF2YWwgZm9yICd0aGlzJ1xuICAgICAgICAgICAgxIguc2V0KG5vZGUsIGN1clN0YXR1cy5kZWx0YSwgYXYpO1xuICAgICAgICAgICAgcmV0dXJuIGF2O1xuICAgICAgICB9LFxuXG4gICAgICAgIExpdGVyYWw6IGZ1bmN0aW9uIChub2RlLCBjdXJTdGF0dXMsIGMpIHtcbiAgICAgICAgICAgIGNvbnN0IHJlcyA9IMSILmdldChub2RlLCBjdXJTdGF0dXMuZGVsdGEpO1xuICAgICAgICAgICAgaWYgKG5vZGUucmVnZXgpIHtcbiAgICAgICAgICAgICAgICAvLyBub3QgaW1wbGVtZW50ZWQgeWV0XG4gICAgICAgICAgICAgICAgLy8gdGhyb3cgbmV3IEVycm9yKCdyZWdleCBsaXRlcmFsIGlzIG5vdCBpbXBsZW1lbnRlZCB5ZXQnKTtcbiAgICAgICAgICAgICAgICByZXR1cm4gcmVzO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgc3dpdGNoICh0eXBlb2Ygbm9kZS52YWx1ZSkge1xuICAgICAgICAgICAgY2FzZSAnbnVtYmVyJzpcbiAgICAgICAgICAgICAgICByZXMuYWRkVHlwZSh0eXBlcy5QcmltTnVtYmVyKTtcbiAgICAgICAgICAgICAgICBicmVhaztcbiAgICAgICAgICAgIGNhc2UgJ3N0cmluZyc6XG4gICAgICAgICAgICAgICAgcmVzLmFkZFR5cGUodHlwZXMuUHJpbVN0cmluZyk7XG4gICAgICAgICAgICAgICAgYnJlYWs7XG4gICAgICAgICAgICBjYXNlICdib29sZWFuJzpcbiAgICAgICAgICAgICAgICByZXMuYWRkVHlwZSh0eXBlcy5QcmltQm9vbGVhbik7XG4gICAgICAgICAgICAgICAgYnJlYWs7XG4gICAgICAgICAgICBjYXNlICdvYmplY3QnOlxuICAgICAgICAgICAgICAgIC8vIEkgZ3Vlc3M6IExpdGVyYWwgJiYgb2JqZWN0ID09PiBub2RlLnZhbHVlID09IG51bGxcbiAgICAgICAgICAgICAgICAvLyBudWxsIGlzIGlnbm9yZWQsIHNvIG5vdGhpbmcgdG8gYWRkXG4gICAgICAgICAgICAgICAgYnJlYWs7XG4gICAgICAgICAgICBjYXNlICdmdW5jdGlvbic6XG4gICAgICAgICAgICAgICAgdGhyb3cgbmV3IEVycm9yKCdJIGd1ZXNzIGZ1bmN0aW9uIGlzIGltcG9zc2libGUgaGVyZS4nKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIHJldHVybiByZXM7XG4gICAgICAgIH0sXG5cbiAgICAgICAgQXNzaWdubWVudEV4cHJlc3Npb246IGZ1bmN0aW9uIChub2RlLCBjdXJTdGF0dXMsIGMpIHtcbiAgICAgICAgICAgIGNvbnN0IHJoc0FWYWwgPSBjKG5vZGUucmlnaHQsIGN1clN0YXR1cywgdW5kZWZpbmVkKTtcbiAgICAgICAgICAgIGlmIChub2RlLmxlZnQudHlwZSA9PT0gJ0lkZW50aWZpZXInKSB7XG4gICAgICAgICAgICAgICAgLy8gTEhTIGlzIGEgc2ltcGxlIHZhcmlhYmxlLlxuICAgICAgICAgICAgICAgIGNvbnN0IHZhck5hbWUgPSBub2RlLmxlZnQubmFtZTtcbiAgICAgICAgICAgICAgICBjb25zdCBsaHNBVmFsID0gY3VyU3RhdHVzLnNjLmdldEFWYWxPZih2YXJOYW1lKTtcbiAgICAgICAgICAgICAgICAvLyBsaHMgaXMgbm90IHZpc2l0ZWQuIE5lZWQgdG8gaGFuZGxlIGhlcmUuXG4gICAgICAgICAgICAgICAgLy8gVXNlIGF2YWwgZm91bmQgaW4gdGhlIHNjb3BlIGZvciBsaHNcbiAgICAgICAgICAgICAgICDEiC5zZXQobm9kZS5sZWZ0LCBjdXJTdGF0dXMuZGVsdGEsIGxoc0FWYWwpO1xuXG4gICAgICAgICAgICAgICAgaWYgKG5vZGUub3BlcmF0b3IgPT09ICc9Jykge1xuICAgICAgICAgICAgICAgICAgICAvLyBzaW1wbGUgYXNzaWdubWVudFxuICAgICAgICAgICAgICAgICAgICByaHNBVmFsLnByb3BhZ2F0ZShsaHNBVmFsKTtcbiAgICAgICAgICAgICAgICAgICAgLy8gbm9kZSdzIEFWYWwgZnJvbSBSSFNcbiAgICAgICAgICAgICAgICAgICAgxIguc2V0KG5vZGUsIGN1clN0YXR1cy5kZWx0YSwgcmhzQVZhbCk7XG4gICAgICAgICAgICAgICAgICAgIHJldHVybiByaHNBVmFsO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAvLyB1cGRhdGluZyBhc3NpZ25tZW50XG4gICAgICAgICAgICAgICAgY29uc3QgcmVzQVZhbCA9IMSILmdldChub2RlLCBjdXJTdGF0dXMuZGVsdGEpO1xuICAgICAgICAgICAgICAgIGlmIChub2RlLm9wZXJhdG9yID09PSAnKz0nKSB7XG4gICAgICAgICAgICAgICAgICAgIC8vIGNvbmNhdGVuYXRpbmcgdXBkYXRlXG4gICAgICAgICAgICAgICAgICAgIGxoc0FWYWwucHJvcGFnYXRlKG5ldyBjc3RyLklzQWRkZWQocmhzQVZhbCwgcmVzQVZhbCkpO1xuICAgICAgICAgICAgICAgICAgICByaHNBVmFsLnByb3BhZ2F0ZShuZXcgY3N0ci5Jc0FkZGVkKGxoc0FWYWwsIHJlc0FWYWwpKTtcbiAgICAgICAgICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgICAgICAgICAgICAvLyBhcml0aG1ldGljIHVwZGF0ZVxuICAgICAgICAgICAgICAgICAgICByZXNBVmFsLmFkZFR5cGUodHlwZXMuUHJpbU51bWJlcik7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIHJldHVybiByZXNBVmFsO1xuICAgICAgICAgICAgfSBlbHNlIGlmIChub2RlLmxlZnQudHlwZSA9PT0gJ01lbWJlckV4cHJlc3Npb24nKSB7XG4gICAgICAgICAgICAgICAgY29uc3Qgb2JqQVZhbCA9IGMobm9kZS5sZWZ0Lm9iamVjdCwgY3VyU3RhdHVzLCB1bmRlZmluZWQpO1xuICAgICAgICAgICAgICAgIGNvbnN0IFthY2NUeXBlLCBwcm9wTmFtZV0gPSBwcm9wQWNjZXNzKG5vZGUubGVmdCk7XG4gICAgICAgICAgICAgICAgaWYgKG5vZGUub3BlcmF0b3IgPT09ICc9Jykge1xuICAgICAgICAgICAgICAgICAgICAvLyBhc3NpZ25tZW50IHRvIG1lbWJlclxuICAgICAgICAgICAgICAgICAgICBpZiAoYWNjVHlwZSAhPT0gJ2R1bW15UHJvcGVydHknKSB7XG4gICAgICAgICAgICAgICAgICAgICAgICBvYmpBVmFsLnByb3BhZ2F0ZShuZXcgY3N0ci5Xcml0ZVByb3AocHJvcE5hbWUsIHJoc0FWYWwpKTtcbiAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAvLyBpZiBwcm9wZXJ0eSBpcyBudW1iZXIgbGl0ZXJhbCwgYWxzbyB3cml0ZSB0byAndW5rbm93bidcbiAgICAgICAgICAgICAgICAgICAgaWYgKGFjY1R5cGUgPT09ICdudW1iZXJMaXRlcmFsJykge1xuICAgICAgICAgICAgICAgICAgICAgICAgb2JqQVZhbC5wcm9wYWdhdGUobmV3IGNzdHIuV3JpdGVQcm9wKG51bGwsIHJoc0FWYWwpKTtcbiAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAvLyBub2RlJ3MgQVZhbCBmcm9tIFJIU1xuICAgICAgICAgICAgICAgICAgICDEiC5zZXQobm9kZSwgY3VyU3RhdHVzLmRlbHRhLCByaHNBVmFsKTtcbiAgICAgICAgICAgICAgICAgICAgcmV0dXJuIHJoc0FWYWw7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIC8vIHVwZGF0aW5nIGFzc2lnbm1lbnRcbiAgICAgICAgICAgICAgICBjb25zdCByZXNBVmFsID0gxIguZ2V0KG5vZGUsIGN1clN0YXR1cy5kZWx0YSk7XG4gICAgICAgICAgICAgICAgY29uc3QgWywgcmV0QVZhbF0gPSByZWFkTWVtYmVyKG5vZGUubGVmdCwgY3VyU3RhdHVzLCBjKTtcbiAgICAgICAgICAgICAgICBpZiAobm9kZS5vcGVyYXRvciA9PT0gJys9Jykge1xuICAgICAgICAgICAgICAgICAgICAvLyBjb25jYXRlbmF0aW5nIHVwZGF0ZVxuICAgICAgICAgICAgICAgICAgICByZXRBVmFsLnByb3BhZ2F0ZShuZXcgY3N0ci5Jc0FkZGVkKHJoc0FWYWwsIHJlc0FWYWwpKTtcbiAgICAgICAgICAgICAgICAgICAgcmhzQVZhbC5wcm9wYWdhdGUobmV3IGNzdHIuSXNBZGRlZChyZXRBVmFsLCByZXNBVmFsKSk7XG4gICAgICAgICAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgLy8gYXJpdGhtZXRpYyB1cGRhdGVcbiAgICAgICAgICAgICAgICAgICAgcmVzQVZhbC5hZGRUeXBlKHR5cGVzLlByaW1OdW1iZXIpO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICByZXR1cm4gcmVzQVZhbDtcbiAgICAgICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgICAgICAgY29uc29sZS5pbmZvKCdBc3NpZ25tZW50IHVzaW5nIHBhdHRlcm4gaXMgbm90IGltcGxlbWVudGVkJyk7XG4gICAgICAgICAgICB9XG4gICAgICAgIH0sXG5cbiAgICAgICAgVmFyaWFibGVEZWNsYXJhdGlvbjogZnVuY3Rpb24gKG5vZGUsIGN1clN0YXR1cywgYykge1xuICAgICAgICAgICAgZm9yIChsZXQgaSA9IDA7IGkgPCBub2RlLmRlY2xhcmF0aW9ucy5sZW5ndGg7IGkrKykge1xuICAgICAgICAgICAgICAgIGNvbnN0IGRlY2wgPSBub2RlLmRlY2xhcmF0aW9uc1tpXTtcbiAgICAgICAgICAgICAgICBjb25zdCBsaHNBVmFsID0gY3VyU3RhdHVzLnNjLmdldEFWYWxPZihkZWNsLmlkLm5hbWUpO1xuICAgICAgICAgICAgICAgIC8vIGRlY2xhcmVkIHZhciBub2RlIGlzICdpZCdcbiAgICAgICAgICAgICAgICDEiC5zZXQoZGVjbC5pZCwgY3VyU3RhdHVzLmRlbHRhLCBsaHNBVmFsKTtcbiAgICAgICAgICAgICAgICBpZiAoZGVjbC5pbml0KSB7XG4gICAgICAgICAgICAgICAgICAgIGNvbnN0IHJoc0FWYWwgPSBjKGRlY2wuaW5pdCwgY3VyU3RhdHVzLCB1bmRlZmluZWQpO1xuICAgICAgICAgICAgICAgICAgICDEiC5zZXQoZGVjbC5pbml0LCBjdXJTdGF0dXMuZGVsdGEsIHJoc0FWYWwpO1xuICAgICAgICAgICAgICAgICAgICByaHNBVmFsLnByb3BhZ2F0ZShsaHNBVmFsKTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICB9XG4gICAgICAgIH0sXG5cbiAgICAgICAgTG9naWNhbEV4cHJlc3Npb246IGZ1bmN0aW9uIChub2RlLCBjdXJTdGF0dXMsIGMpIHtcbiAgICAgICAgICAgIGNvbnN0IHJlcyA9IMSILmdldChub2RlLCBjdXJTdGF0dXMuZGVsdGEpO1xuICAgICAgICAgICAgY29uc3QgbGVmdCA9IGMobm9kZS5sZWZ0LCBjdXJTdGF0dXMsIHVuZGVmaW5lZCk7XG4gICAgICAgICAgICBjb25zdCByaWdodCA9IGMobm9kZS5yaWdodCwgY3VyU3RhdHVzLCB1bmRlZmluZWQpO1xuICAgICAgICAgICAgbGVmdC5wcm9wYWdhdGUocmVzKTtcbiAgICAgICAgICAgIHJpZ2h0LnByb3BhZ2F0ZShyZXMpO1xuICAgICAgICAgICAgcmV0dXJuIHJlcztcbiAgICAgICAgfSxcblxuICAgICAgICBDb25kaXRpb25hbEV4cHJlc3Npb246IGZ1bmN0aW9uIChub2RlLCBjdXJTdGF0dXMsIGMpIHtcbiAgICAgICAgICAgIGNvbnN0IHJlcyA9IMSILmdldChub2RlLCBjdXJTdGF0dXMuZGVsdGEpO1xuICAgICAgICAgICAgYyhub2RlLnRlc3QsIGN1clN0YXR1cywgdW5kZWZpbmVkKTtcbiAgICAgICAgICAgIGNvbnN0IGNvbnMgPSBjKG5vZGUuY29uc2VxdWVudCwgY3VyU3RhdHVzLCB1bmRlZmluZWQpO1xuICAgICAgICAgICAgY29uc3QgYWx0ID0gYyhub2RlLmFsdGVybmF0ZSwgY3VyU3RhdHVzLCB1bmRlZmluZWQpO1xuICAgICAgICAgICAgY29ucy5wcm9wYWdhdGUocmVzKTtcbiAgICAgICAgICAgIGFsdC5wcm9wYWdhdGUocmVzKTtcbiAgICAgICAgICAgIHJldHVybiByZXM7XG4gICAgICAgIH0sXG5cbiAgICAgICAgTmV3RXhwcmVzc2lvbjogZnVuY3Rpb24gKG5vZGUsIGN1clN0YXR1cywgYykge1xuICAgICAgICAgICAgY29uc3QgcmV0ID0gxIguZ2V0KG5vZGUsIGN1clN0YXR1cy5kZWx0YSk7XG4gICAgICAgICAgICBjb25zdCBjYWxsZWUgPSBjKG5vZGUuY2FsbGVlLCBjdXJTdGF0dXMsIHVuZGVmaW5lZCk7XG4gICAgICAgICAgICBjb25zdCBhcmdzID0gW107XG4gICAgICAgICAgICBmb3IgKGxldCBpID0gMDsgaSA8IG5vZGUuYXJndW1lbnRzLmxlbmd0aDsgaSsrKSB7XG4gICAgICAgICAgICAgICAgYXJncy5wdXNoKGMobm9kZS5hcmd1bWVudHNbaV0sIGN1clN0YXR1cywgdW5kZWZpbmVkKSk7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBjb25zdCBuZXdEZWx0YSA9IGN1clN0YXR1cy5kZWx0YS5hcHBlbmRPbmUobm9kZVsnQGxhYmVsJ10pO1xuICAgICAgICAgICAgY2FsbGVlLnByb3BhZ2F0ZShcbiAgICAgICAgICAgICAgICBuZXcgY3N0ci5Jc0N0b3IoXG4gICAgICAgICAgICAgICAgICAgIGFyZ3MsXG4gICAgICAgICAgICAgICAgICAgIHJldCxcbiAgICAgICAgICAgICAgICAgICAgY3VyU3RhdHVzLmV4YyxcbiAgICAgICAgICAgICAgICAgICAgbmV3RGVsdGEpKTtcbiAgICAgICAgICAgIHJldHVybiByZXQ7XG4gICAgICAgIH0sXG5cbiAgICAgICAgQXJyYXlFeHByZXNzaW9uOiBmdW5jdGlvbiAobm9kZSwgY3VyU3RhdHVzLCBjKSB7XG4gICAgICAgICAgICBjb25zdCByZXQgPSDEiC5nZXQobm9kZSwgY3VyU3RhdHVzLmRlbHRhKTtcbiAgICAgICAgICAgIC8vIE5PVEUgcHJvdG90eXBlIG9iamVjdCBpcyBub3QgcmVjb3JkZWQgaW4gxIhcbiAgICAgICAgICAgIGNvbnN0IGFyclR5cGUgPSBuZXcgdHlwZXMuQXJyVHlwZShuZXcgdHlwZXMuQVZhbChydENYLnByb3Rvcy5BcnJheSkpO1xuICAgICAgICAgICAgLy8gYWRkIGxlbmd0aCBwcm9wZXJ0eVxuICAgICAgICAgICAgYXJyVHlwZS5nZXRQcm9wKCdsZW5ndGgnKS5hZGRUeXBlKHR5cGVzLlByaW1OdW1iZXIpO1xuXG4gICAgICAgICAgICByZXQuYWRkVHlwZShhcnJUeXBlKTtcblxuICAgICAgICAgICAgLy8gYWRkIGFycmF5IGVsZW1lbnRzXG4gICAgICAgICAgICBmb3IgKGxldCBpID0gMDsgaSA8IG5vZGUuZWxlbWVudHMubGVuZ3RoOyBpKyspIHtcbiAgICAgICAgICAgICAgICBpZiAobm9kZS5lbGVtZW50c1tpXSA9PSBudWxsKSB7XG4gICAgICAgICAgICAgICAgICAgIGNvbnRpbnVlO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICBjb25zdCBlbHRBVmFsID0gYyhub2RlLmVsZW1lbnRzW2ldLCBjdXJTdGF0dXMsIHVuZGVmaW5lZCk7XG5cbiAgICAgICAgICAgICAgICBjb25zdCBwcm9wID0gaSArICcnO1xuICAgICAgICAgICAgICAgIHJldC5wcm9wYWdhdGUobmV3IGNzdHIuV3JpdGVQcm9wKHByb3AsIGVsdEFWYWwpKTtcbiAgICAgICAgICAgICAgICByZXQucHJvcGFnYXRlKG5ldyBjc3RyLldyaXRlUHJvcChudWxsLCBlbHRBVmFsKSk7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICByZXR1cm4gcmV0O1xuICAgICAgICB9LFxuXG4gICAgICAgIE9iamVjdEV4cHJlc3Npb246IGZ1bmN0aW9uIChub2RlLCBjdXJTdGF0dXMsIGMpIHtcbiAgICAgICAgICAgIGNvbnN0IHJldCA9IMSILmdldChub2RlLCBjdXJTdGF0dXMuZGVsdGEpO1xuICAgICAgICAgICAgLy8gTk9URSBwcm90b3R5cGUgb2JqZWN0IGlzIG5vdCByZWNvcmRlZCBpbiDEiFxuICAgICAgICAgICAgY29uc3Qgb2JqVHlwZSA9IG5ldyB0eXBlcy5PYmpUeXBlKG5ldyB0eXBlcy5BVmFsKHJ0Q1gucHJvdG9zLk9iamVjdCkpO1xuICAgICAgICAgICAgcmV0LmFkZFR5cGUob2JqVHlwZSk7XG5cbiAgICAgICAgICAgIGZvciAobGV0IGkgPSAwOyBpIDwgbm9kZS5wcm9wZXJ0aWVzLmxlbmd0aDsgaSsrKSB7XG4gICAgICAgICAgICAgICAgY29uc3QgcHJvcFBhaXIgPSBub2RlLnByb3BlcnRpZXNbaV07XG4gICAgICAgICAgICAgICAgY29uc3QgcHJvcEtleSA9IHByb3BQYWlyLmtleTtcbiAgICAgICAgICAgICAgICBsZXQgbmFtZTtcbiAgICAgICAgICAgICAgICBjb25zdCBwcm9wRXhwciA9IHByb3BQYWlyLnZhbHVlO1xuXG4gICAgICAgICAgICAgICAgY29uc3QgZmxkQVZhbCA9IGMocHJvcEV4cHIsIGN1clN0YXR1cywgdW5kZWZpbmVkKTtcblxuICAgICAgICAgICAgICAgIGlmIChwcm9wS2V5LnR5cGUgPT09ICdJZGVudGlmaWVyJykge1xuICAgICAgICAgICAgICAgICAgICBuYW1lID0gcHJvcEtleS5uYW1lO1xuICAgICAgICAgICAgICAgIH0gZWxzZSBpZiAodHlwZW9mIHByb3BLZXkudmFsdWUgPT09ICdzdHJpbmcnKSB7XG4gICAgICAgICAgICAgICAgICAgIG5hbWUgPSBwcm9wS2V5LnZhbHVlO1xuICAgICAgICAgICAgICAgIH0gZWxzZSBpZiAodHlwZW9mIHByb3BLZXkudmFsdWUgPT09ICdudW1iZXInKSB7XG4gICAgICAgICAgICAgICAgICAgIC8vIGNvbnZlcnQgbnVtYmVyIHRvIHN0cmluZ1xuICAgICAgICAgICAgICAgICAgICBuYW1lID0gcHJvcEtleS52YWx1ZSArICcnO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICByZXQucHJvcGFnYXRlKG5ldyBjc3RyLldyaXRlUHJvcChuYW1lLCBmbGRBVmFsKSk7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICByZXR1cm4gcmV0O1xuICAgICAgICB9LFxuXG4gICAgICAgIEFycm93RnVuY3Rpb25FeHByZXNzaW9uOiBmdW5jdGlvbiAobm9kZSwgY3VyU3RhdHVzLCBjKSB7XG4gICAgICAgICAgICBpZiAoIW5vZGUuZm5JbnN0YW5jZXMpIHtcbiAgICAgICAgICAgICAgICBub2RlLmZuSW5zdGFuY2VzID0gW107XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBsZXQgZm5JbnN0YW5jZSA9IG51bGw7XG4gICAgICAgICAgICBub2RlLmZuSW5zdGFuY2VzLmZvckVhY2goZnVuY3Rpb24gKGZuVHlwZSkge1xuICAgICAgICAgICAgICAgIGlmIChmblR5cGUuc2MgPT09IGN1clN0YXR1cy5zYykge1xuICAgICAgICAgICAgICAgICAgICBmbkluc3RhbmNlID0gZm5UeXBlO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgIH0pO1xuICAgICAgICAgICAgaWYgKCFmbkluc3RhbmNlKSB7XG4gICAgICAgICAgICAgICAgZm5JbnN0YW5jZVxuICAgICAgICAgICAgICAgICAgICA9IG5ldyB0eXBlcy5GblR5cGUobmV3IHR5cGVzLkFWYWwocnRDWC5wcm90b3MuRnVuY3Rpb24pLFxuICAgICAgICAgICAgICAgICAgICAnW2Fycm93IGZ1bmN0aW9uXScsXG4gICAgICAgICAgICAgICAgICAgIG5vZGUuYm9keVsnQGJsb2NrJ10uZ2V0UGFyYW1WYXJOYW1lcygpLFxuICAgICAgICAgICAgICAgICAgICBjdXJTdGF0dXMuc2MsXG4gICAgICAgICAgICAgICAgICAgIG5vZGUsXG4gICAgICAgICAgICAgICAgICAgIHVuZGVmaW5lZCxcbiAgICAgICAgICAgICAgICAgICAgY3VyU3RhdHVzLnNlbGYgICAgLy8gYXJyb3cgZnVuY3Rpb24gc2hvdWxkIHJlbWVtYmVyIEFWYWwgb2Ygb3V0ZXIgdGhpcy5cbiAgICAgICAgICAgICAgICApO1xuICAgICAgICAgICAgICAgIG5vZGUuZm5JbnN0YW5jZXMucHVzaChmbkluc3RhbmNlKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGNvbnN0IHJldCA9IMSILmdldChub2RlLCBjdXJTdGF0dXMuZGVsdGEpO1xuICAgICAgICAgICAgcmV0LmFkZFR5cGUoZm5JbnN0YW5jZSk7XG5cbiAgICAgICAgICAgIHJldC5wcm9wYWdhdGUoXG4gICAgICAgICAgICAgICAgbmV3IGNzdHIuSXNDYWxsZWUoXG4gICAgICAgICAgICAgICAgICAgIHR5cGVzLkFWYWxOdWxsLCAgICAgICAgICAgICAgICAgIC8vIG5vdGhpbmcgdG8gcHJvcGFnYXRlIHRvIHNlbGZcbiAgICAgICAgICAgICAgICAgICAgW10sICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgLy8gbm8gYXJndW1lbnRzXG4gICAgICAgICAgICAgICAgICAgIHR5cGVzLkFWYWxOdWxsLCAgICAgICAgICAgICAgICAgIC8vIHJldHVybiBpcyBpZ25vcmVkXG4gICAgICAgICAgICAgICAgICAgIHR5cGVzLkFWYWxOdWxsLCAgICAgICAgICAgICAgICAgIC8vIG5vIHZhbGlkIGNhbGxlciB3aXRoIGV4Y0FWYWxcbiAgICAgICAgICAgICAgICAgICAgY3NjLkNhbGxTaXRlQ29udGV4dC5udWxsQ29udGV4dCAgLy8gVXNpbmcgbnVsbENvbnRleHRcbiAgICAgICAgICAgICAgICApXG4gICAgICAgICAgICApO1xuXG4gICAgICAgICAgICByZXR1cm4gcmV0O1xuICAgICAgICB9LFxuXG4gICAgICAgIEZ1bmN0aW9uRXhwcmVzc2lvbjogZnVuY3Rpb24gKG5vZGUsIGN1clN0YXR1cywgYykge1xuICAgICAgICAgICAgaWYgKCFub2RlLmZuSW5zdGFuY2VzKSB7XG4gICAgICAgICAgICAgICAgbm9kZS5mbkluc3RhbmNlcyA9IFtdO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgbGV0IGZuSW5zdGFuY2UgPSBudWxsO1xuICAgICAgICAgICAgbm9kZS5mbkluc3RhbmNlcy5mb3JFYWNoKGZ1bmN0aW9uIChmblR5cGUpIHtcbiAgICAgICAgICAgICAgICBpZiAoZm5UeXBlLnNjID09PSBjdXJTdGF0dXMuc2MpIHtcbiAgICAgICAgICAgICAgICAgICAgZm5JbnN0YW5jZSA9IGZuVHlwZTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICB9KTtcbiAgICAgICAgICAgIGlmICghZm5JbnN0YW5jZSkge1xuICAgICAgICAgICAgICAgIC8vIE5PVEUgcHJvdG90eXBlIG9iamVjdCBpcyBub3QgcmVjb3JkZWQgaW4gxIhcbiAgICAgICAgICAgICAgICBmbkluc3RhbmNlXG4gICAgICAgICAgICAgICAgICAgID0gbmV3IHR5cGVzLkZuVHlwZShuZXcgdHlwZXMuQVZhbChydENYLnByb3Rvcy5GdW5jdGlvbiksXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAnW2Fub255bW91cyBmdW5jdGlvbl0nLFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgbm9kZS5ib2R5WydAYmxvY2snXS5nZXRQYXJhbVZhck5hbWVzKCksXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBjdXJTdGF0dXMuc2MsXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBub2RlLFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgcnRDWC5wcm90b3MuT2JqZWN0KTtcbiAgICAgICAgICAgICAgICBub2RlLmZuSW5zdGFuY2VzLnB1c2goZm5JbnN0YW5jZSk7XG4gICAgICAgICAgICAgICAgLy8gTk9URSBwcm90b3R5cGUgb2JqZWN0IGlzIG5vdCByZWNvcmRlZCBpbiDEiFxuICAgICAgICAgICAgICAgIGNvbnN0IHByb3RvdHlwZU9iamVjdCA9XG4gICAgICAgICAgICAgICAgICAgIG5ldyB0eXBlcy5PYmpUeXBlKG5ldyB0eXBlcy5BVmFsKHJ0Q1gucHJvdG9zLk9iamVjdCksXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICcucHJvdG90eXBlJyk7XG4gICAgICAgICAgICAgICAgLy8gRm9yIC5wcm90b3R5cGVcbiAgICAgICAgICAgICAgICBuZXcgdHlwZXMuQVZhbChmbkluc3RhbmNlKS5wcm9wYWdhdGUoXG4gICAgICAgICAgICAgICAgICAgIG5ldyBjc3RyLldyaXRlUHJvcCgncHJvdG90eXBlJyxuZXcgdHlwZXMuQVZhbChwcm90b3R5cGVPYmplY3QpKVxuICAgICAgICAgICAgICAgICk7XG4gICAgICAgICAgICAgICAgLy8gRm9yIC5wcm90b3R5cGUuY29uc3RydWN0b3JcbiAgICAgICAgICAgICAgICBjb25zdCBjb25zdHJ1Y3RvclByb3AgPSBwcm90b3R5cGVPYmplY3QuZ2V0UHJvcCgnY29uc3RydWN0b3InKTtcbiAgICAgICAgICAgICAgICBjb25zdHJ1Y3RvclByb3AuYWRkVHlwZShmbkluc3RhbmNlKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGNvbnN0IHJldCA9IMSILmdldChub2RlLCBjdXJTdGF0dXMuZGVsdGEpO1xuICAgICAgICAgICAgcmV0LmFkZFR5cGUoZm5JbnN0YW5jZSk7XG5cbiAgICAgICAgICAgIC8vIENhbGwgdGhlIGZ1bmN0aW9uIHVzaW5nIG51bGxDb250ZXh0XG4gICAgICAgICAgICBjb25zdCBbc2VsZkFWYWwsLF0gPSBmbkluc3RhbmNlLmdldEZ1bkVudihjc2MuQ2FsbFNpdGVDb250ZXh0Lm51bGxDb250ZXh0KTtcbiAgICAgICAgICAgIC8vIGFkZCB0aGUgZnVuY3Rpb24ncyBpbnN0YW5jZVxuICAgICAgICAgICAgc2VsZkFWYWwuYWRkVHlwZShmbkluc3RhbmNlLmdldEluc3RhbmNlKCkpO1xuICAgICAgICAgICAgcmV0LnByb3BhZ2F0ZShcbiAgICAgICAgICAgICAgICBuZXcgY3N0ci5Jc0NhbGxlZShcbiAgICAgICAgICAgICAgICAgICAgdHlwZXMuQVZhbE51bGwsICAgICAgICAgICAgICAgICAgLy8gbm90aGluZyB0byBwcm9wYWdhdGUgdG8gc2VsZlxuICAgICAgICAgICAgICAgICAgICBbXSwgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAvLyBubyBhcmd1bWVudHNcbiAgICAgICAgICAgICAgICAgICAgdHlwZXMuQVZhbE51bGwsICAgICAgICAgICAgICAgICAgLy8gcmV0dXJuIGlzIGlnbm9yZWRcbiAgICAgICAgICAgICAgICAgICAgdHlwZXMuQVZhbE51bGwsICAgICAgICAgICAgICAgICAgLy8gbm8gdmFsaWQgY2FsbGVyIHdpdGggZXhjQVZhbFxuICAgICAgICAgICAgICAgICAgICBjc2MuQ2FsbFNpdGVDb250ZXh0Lm51bGxDb250ZXh0ICAvLyBVc2luZyBudWxsQ29udGV4dFxuICAgICAgICAgICAgICAgIClcbiAgICAgICAgICAgICk7XG5cbiAgICAgICAgICAgIHJldHVybiByZXQ7XG4gICAgICAgIH0sXG5cbiAgICAgICAgRnVuY3Rpb25EZWNsYXJhdGlvbjogZnVuY3Rpb24gKG5vZGUsIGN1clN0YXR1cywgYykge1xuICAgICAgICAgICAgLy8gRHJvcCBpbml0aWFsIGNhdGNoIG9yIG5vcm1hbCBzY29wZXNcbiAgICAgICAgICAgIGNvbnN0IHNjMCA9IGN1clN0YXR1cy5zYy5yZW1vdmVJbml0aWFsQ2F0Y2hPck5vcm1hbEJsb2NrcygpO1xuICAgICAgICAgICAgaWYgKCFub2RlLmZuSW5zdGFuY2VzKSB7XG4gICAgICAgICAgICAgICAgbm9kZS5mbkluc3RhbmNlcyA9IFtdO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgbGV0IGZuSW5zdGFuY2UgPSBudWxsO1xuICAgICAgICAgICAgbm9kZS5mbkluc3RhbmNlcy5mb3JFYWNoKGZ1bmN0aW9uIChmblR5cGUpIHtcbiAgICAgICAgICAgICAgICBpZiAoZm5UeXBlLnNjID09PSBzYzApIHtcbiAgICAgICAgICAgICAgICAgICAgZm5JbnN0YW5jZSA9IGZuVHlwZTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICB9KTtcbiAgICAgICAgICAgIGlmICghZm5JbnN0YW5jZSkge1xuICAgICAgICAgICAgICAgIC8vIE5PVEUgcHJvdG90eXBlIG9iamVjdCBpcyBub3QgcmVjb3JkZWQgaW4gxIhcbiAgICAgICAgICAgICAgICBmbkluc3RhbmNlXG4gICAgICAgICAgICAgICAgICAgID0gbmV3IHR5cGVzLkZuVHlwZShuZXcgdHlwZXMuQVZhbChydENYLnByb3Rvcy5GdW5jdGlvbiksXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBub2RlLmlkLm5hbWUsXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBub2RlLmJvZHlbJ0BibG9jayddLmdldFBhcmFtVmFyTmFtZXMoKSxcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIHNjMCxcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIG5vZGUsXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBydENYLnByb3Rvcy5PYmplY3QpO1xuICAgICAgICAgICAgICAgIG5vZGUuZm5JbnN0YW5jZXMucHVzaChmbkluc3RhbmNlKTtcbiAgICAgICAgICAgICAgICAvLyBmb3IgZWFjaCBmbkluc3RhbmNlLCBhc3NpZ24gb25lIHByb3RvdHlwZSBvYmplY3RcbiAgICAgICAgICAgICAgICAvLyBOT1RFIHByb3RvdHlwZSBvYmplY3QgaXMgbm90IHJlY29yZGVkIGluIMSIXG4gICAgICAgICAgICAgICAgY29uc3QgcHJvdG90eXBlT2JqZWN0ID1cbiAgICAgICAgICAgICAgICAgICAgbmV3IHR5cGVzLk9ialR5cGUobmV3IHR5cGVzLkFWYWwocnRDWC5wcm90b3MuT2JqZWN0KSxcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgbm9kZS5pZC5uYW1lICsgJy5wcm90b3R5cGUnKTtcbiAgICAgICAgICAgICAgICAvLyBGb3IgLnByb3RvdHlwZVxuICAgICAgICAgICAgICAgIG5ldyB0eXBlcy5BVmFsKGZuSW5zdGFuY2UpLnByb3BhZ2F0ZShcbiAgICAgICAgICAgICAgICAgICAgbmV3IGNzdHIuV3JpdGVQcm9wKCdwcm90b3R5cGUnLCBuZXcgdHlwZXMuQVZhbChwcm90b3R5cGVPYmplY3QpKVxuICAgICAgICAgICAgICAgICk7XG4gICAgICAgICAgICAgICAgLy8gRm9yIC5wcm90b3R5cGUuY29uc3RydWN0b3JcbiAgICAgICAgICAgICAgICBjb25zdCBjb25zdHJ1Y3RvclByb3AgPSBwcm90b3R5cGVPYmplY3QuZ2V0UHJvcCgnY29uc3RydWN0b3InKTtcbiAgICAgICAgICAgICAgICBjb25zdHJ1Y3RvclByb3AuYWRkVHlwZShmbkluc3RhbmNlKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGNvbnN0IGxoc0FWYWwgPSBzYzAuZ2V0QVZhbE9mKG5vZGUuaWQubmFtZSk7XG4gICAgICAgICAgICBsaHNBVmFsLmFkZFR5cGUoZm5JbnN0YW5jZSk7XG5cbiAgICAgICAgICAgIC8vIENhbGwgdGhlIGZ1bmN0aW9uIHVzaW5nIG51bGxDb250ZXh0XG4gICAgICAgICAgICBjb25zdCBbc2VsZkFWYWwsLF0gPSBmbkluc3RhbmNlLmdldEZ1bkVudihjc2MuQ2FsbFNpdGVDb250ZXh0Lm51bGxDb250ZXh0KTtcbiAgICAgICAgICAgIC8vIGFkZCB0aGUgZnVuY3Rpb24ncyBpbnN0YW5jZVxuICAgICAgICAgICAgc2VsZkFWYWwuYWRkVHlwZShmbkluc3RhbmNlLmdldEluc3RhbmNlKCkpO1xuICAgICAgICAgICAgbGhzQVZhbC5wcm9wYWdhdGUoXG4gICAgICAgICAgICAgICAgbmV3IGNzdHIuSXNDYWxsZWUoXG4gICAgICAgICAgICAgICAgICAgIHR5cGVzLkFWYWxOdWxsLCAgICAgICAgICAgICAgICAgIC8vIG5vdGhpbmcgdG8gcHJvcGFnYXRlIHRvIHNlbGZcbiAgICAgICAgICAgICAgICAgICAgW10sICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgLy8gbm8gYXJndW1lbnRzXG4gICAgICAgICAgICAgICAgICAgIHR5cGVzLkFWYWxOdWxsLCAgICAgICAgICAgICAgICAgIC8vIHJldHVybiBpcyBpZ25vcmVkXG4gICAgICAgICAgICAgICAgICAgIHR5cGVzLkFWYWxOdWxsLCAgICAgICAgICAgICAgICAgIC8vIG5vIHZhbGlkIGNhbGxlciB3aXRoIGV4Y0FWYWxcbiAgICAgICAgICAgICAgICAgICAgY3NjLkNhbGxTaXRlQ29udGV4dC5udWxsQ29udGV4dCAgLy8gVXNpbmcgbnVsbENvbnRleHRcbiAgICAgICAgICAgICAgICApXG4gICAgICAgICAgICApO1xuXG4gICAgICAgICAgICAvLyBub3RoaW5nIHRvIHJldHVyblxuICAgICAgICAgICAgcmV0dXJuIHR5cGVzLkFWYWxOdWxsO1xuICAgICAgICB9LFxuXG4gICAgICAgIFNlcXVlbmNlRXhwcmVzc2lvbjogZnVuY3Rpb24gKG5vZGUsIGN1clN0YXR1cywgYykge1xuICAgICAgICAgICAgY29uc3QgbGFzdEluZGV4ID0gbm9kZS5leHByZXNzaW9ucy5sZW5ndGggLSAxO1xuICAgICAgICAgICAgZm9yIChsZXQgaSA9IDA7IGkgPCBsYXN0SW5kZXg7IGkrKykge1xuICAgICAgICAgICAgICAgIGMobm9kZS5leHByZXNzaW9uc1tpXSwgY3VyU3RhdHVzLCB1bmRlZmluZWQpO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgY29uc3QgbGFzdEFWYWwgPSBjKG5vZGUuZXhwcmVzc2lvbnNbbGFzdEluZGV4XSwgY3VyU3RhdHVzLCB1bmRlZmluZWQpO1xuICAgICAgICAgICAgxIguc2V0KG5vZGUsIGN1clN0YXR1cy5kZWx0YSwgbGFzdEFWYWwpO1xuICAgICAgICAgICAgcmV0dXJuIGxhc3RBVmFsO1xuICAgICAgICB9LFxuXG4gICAgICAgIFVuYXJ5RXhwcmVzc2lvbjogZnVuY3Rpb24gKG5vZGUsIGN1clN0YXR1cywgYykge1xuICAgICAgICAgICAgYyhub2RlLmFyZ3VtZW50LCBjdXJTdGF0dXMsIHVuZGVmaW5lZCk7XG4gICAgICAgICAgICBjb25zdCByZXMgPSDEiC5nZXQobm9kZSwgY3VyU3RhdHVzLmRlbHRhKTtcbiAgICAgICAgICAgIGNvbnN0IHR5cGUgPSB1bm9wUmVzdWx0VHlwZShub2RlLm9wZXJhdG9yKTtcbiAgICAgICAgICAgIGlmICh0eXBlKSB7XG4gICAgICAgICAgICAgICAgcmVzLmFkZFR5cGUodHlwZSk7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICByZXR1cm4gcmVzO1xuICAgICAgICB9LFxuXG4gICAgICAgIFVwZGF0ZUV4cHJlc3Npb246IGZ1bmN0aW9uIChub2RlLCBjdXJTdGF0dXMsIGMpIHtcbiAgICAgICAgICAgIGMobm9kZS5hcmd1bWVudCwgY3VyU3RhdHVzLCB1bmRlZmluZWQpO1xuICAgICAgICAgICAgY29uc3QgcmVzID0gxIguZ2V0KG5vZGUsIGN1clN0YXR1cy5kZWx0YSk7XG4gICAgICAgICAgICByZXMuYWRkVHlwZSh0eXBlcy5QcmltTnVtYmVyKTtcbiAgICAgICAgICAgIC8vIFdlIGlnbm9yZSB0aGUgZWZmZWN0IG9mIHVwZGF0aW5nIHRvIG51bWJlciB0eXBlXG4gICAgICAgICAgICByZXR1cm4gcmVzO1xuICAgICAgICB9LFxuXG4gICAgICAgIEJpbmFyeUV4cHJlc3Npb246IGZ1bmN0aW9uIChub2RlLCBjdXJTdGF0dXMsIGMpIHtcbiAgICAgICAgICAgIGNvbnN0IGxPcHJkID0gYyhub2RlLmxlZnQsIGN1clN0YXR1cywgdW5kZWZpbmVkKTtcbiAgICAgICAgICAgIGNvbnN0IHJPcHJkID0gYyhub2RlLnJpZ2h0LCBjdXJTdGF0dXMsIHVuZGVmaW5lZCk7XG4gICAgICAgICAgICBjb25zdCByZXMgPSDEiC5nZXQobm9kZSwgY3VyU3RhdHVzLmRlbHRhKTtcblxuICAgICAgICAgICAgaWYgKG5vZGUub3BlcmF0b3IgPT0gJysnKSB7XG4gICAgICAgICAgICAgICAgbE9wcmQucHJvcGFnYXRlKG5ldyBjc3RyLklzQWRkZWQock9wcmQsIHJlcykpO1xuICAgICAgICAgICAgICAgIHJPcHJkLnByb3BhZ2F0ZShuZXcgY3N0ci5Jc0FkZGVkKGxPcHJkLCByZXMpKTtcbiAgICAgICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgICAgICAgaWYgKGJpbm9wSXNCb29sZWFuKG5vZGUub3BlcmF0b3IpKSB7XG4gICAgICAgICAgICAgICAgICAgIHJlcy5hZGRUeXBlKHR5cGVzLlByaW1Cb29sZWFuKTtcbiAgICAgICAgICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgICAgICAgICAgICByZXMuYWRkVHlwZSh0eXBlcy5QcmltTnVtYmVyKTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICByZXR1cm4gcmVzO1xuICAgICAgICB9LFxuXG4gICAgICAgIEZvclN0YXRlbWVudDogZnVuY3Rpb24gKG5vZGUsIGN1clN0YXR1cywgYykge1xuICAgICAgICAgICAgaWYgKG5vZGVbJ0BibG9jayddKSB7XG4gICAgICAgICAgICAgICAgLy8gaWYgaXQgaGFzIEBibG9jayBwcm9wZXJ0eVxuICAgICAgICAgICAgICAgIGNvbnN0IGZvckJsb2NrU0MgPVxuICAgICAgICAgICAgICAgICAgICBub2RlWydAYmxvY2snXS5nZXRTY29wZUluc3RhbmNlKGN1clN0YXR1cy5zYywgY3VyU3RhdHVzLmRlbHRhKTtcbiAgICAgICAgICAgICAgICBjdXJTdGF0dXMgPSBjdXJTdGF0dXMuZ2V0TmV3U3RhdHVzKHtzYzogZm9yQmxvY2tTQ30pO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgd2Fsay5iYXNlLkZvclN0YXRlbWVudChub2RlLCBjdXJTdGF0dXMsIGMpO1xuICAgICAgICB9LFxuXG4gICAgICAgIEJsb2NrU3RhdGVtZW50OiBmdW5jdGlvbiAobm9kZSwgY3VyU3RhdHVzLCBjKSB7XG4gICAgICAgICAgICBpZiAobm9kZVsnQGJsb2NrJ10pIHtcbiAgICAgICAgICAgICAgICAvLyBpZiBpdCBoYXMgQGJsb2NrIHByb3BlcnR5XG4gICAgICAgICAgICAgICAgY29uc3Qgbm9ybWFsQmxvY2tTQyA9XG4gICAgICAgICAgICAgICAgICAgIG5vZGVbJ0BibG9jayddLmdldFNjb3BlSW5zdGFuY2UoY3VyU3RhdHVzLnNjLCBjdXJTdGF0dXMuZGVsdGEpO1xuICAgICAgICAgICAgICAgIGN1clN0YXR1cyA9IGN1clN0YXR1cy5nZXROZXdTdGF0dXMoe3NjOiBub3JtYWxCbG9ja1NDfSk7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICB3YWxrLmJhc2UuQmxvY2tTdGF0ZW1lbnQobm9kZSwgY3VyU3RhdHVzLCBjKTtcbiAgICAgICAgfSxcblxuICAgICAgICBUcnlTdGF0ZW1lbnQ6IGZ1bmN0aW9uIChub2RlLCBjdXJTdGF0dXMsIGMpIHtcbiAgICAgICAgICAgIC8vIGNvbnN0cnVjdCBzY29wZSBjaGFpbiBmb3IgY2F0Y2ggYmxvY2tcbiAgICAgICAgICAgIGNvbnN0IGNhdGNoQmxvY2tTQyA9XG4gICAgICAgICAgICAgICAgbm9kZS5oYW5kbGVyLmJvZHlbJ0BibG9jayddXG4gICAgICAgICAgICAgICAgLmdldFNjb3BlSW5zdGFuY2UoY3VyU3RhdHVzLnNjLCBjdXJTdGF0dXMuZGVsdGEpO1xuICAgICAgICAgICAgLy8gZ2V0IHRoZSBBVmFsIGZvciBleGNlcHRpb24gcGFyYW1ldGVyXG4gICAgICAgICAgICBjb25zdCBleGNBVmFsID0gY2F0Y2hCbG9ja1NDLmdldEFWYWxPZihub2RlLmhhbmRsZXIucGFyYW0ubmFtZSk7XG5cbiAgICAgICAgICAgIC8vIGZvciB0cnkgYmxvY2tcbiAgICAgICAgICAgIGNvbnN0IHRyeVN0YXR1cyA9IGN1clN0YXR1cy5nZXROZXdTdGF0dXMoe2V4YzogZXhjQVZhbH0pO1xuICAgICAgICAgICAgYyhub2RlLmJsb2NrLCB0cnlTdGF0dXMsIHVuZGVmaW5lZCk7XG5cbiAgICAgICAgICAgIC8vIGZvciBjYXRjaCBibG9ja1xuICAgICAgICAgICAgY29uc3QgY2F0Y2hTdGF0dXMgPSBjdXJTdGF0dXMuZ2V0TmV3U3RhdHVzKHtzYzogY2F0Y2hCbG9ja1NDfSk7XG4gICAgICAgICAgICBjKG5vZGUuaGFuZGxlci5ib2R5LCBjYXRjaFN0YXR1cywgdW5kZWZpbmVkKTtcblxuICAgICAgICAgICAgLy8gZm9yIGZpbmFsbHkgYmxvY2tcbiAgICAgICAgICAgIGlmIChub2RlLmZpbmFsaXplciAhPT0gbnVsbClcbiAgICAgICAgICAgICAgICBjKG5vZGUuZmluYWxpemVyLCBjdXJTdGF0dXMsIHVuZGVmaW5lZCk7XG4gICAgICAgIH0sXG5cbiAgICAgICAgVGhyb3dTdGF0ZW1lbnQ6IGZ1bmN0aW9uIChub2RlLCBjdXJTdGF0dXMsIGMpIHtcbiAgICAgICAgICAgIGNvbnN0IHRociA9IGMobm9kZS5hcmd1bWVudCwgY3VyU3RhdHVzLCB1bmRlZmluZWQpO1xuICAgICAgICAgICAgdGhyLnByb3BhZ2F0ZShjdXJTdGF0dXMuZXhjKTtcbiAgICAgICAgfSxcblxuICAgICAgICBDYWxsRXhwcmVzc2lvbjogZnVuY3Rpb24gKG5vZGUsIGN1clN0YXR1cywgYykge1xuICAgICAgICAgICAgY29uc3QgcmVzQVZhbCA9IMSILmdldChub2RlLCBjdXJTdGF0dXMuZGVsdGEpO1xuICAgICAgICAgICAgY29uc3QgYXJnQVZhbHMgPSBbXTtcblxuICAgICAgICAgICAgLy8gZ2V0IEFWYWxzIGZvciBlYWNoIGFyZ3VtZW50c1xuICAgICAgICAgICAgZm9yIChsZXQgaSA9IDA7IGkgPCBub2RlLmFyZ3VtZW50cy5sZW5ndGg7IGkrKykge1xuICAgICAgICAgICAgICAgIGFyZ0FWYWxzLnB1c2goXG4gICAgICAgICAgICAgICAgICAgIGMobm9kZS5hcmd1bWVudHNbaV0sIGN1clN0YXR1cywgdW5kZWZpbmVkKSk7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICAvLyBhcHBlbmQgY3VycmVudCBjYWxsIHNpdGUgdG8gdGhlIGNvbnRleHRcbiAgICAgICAgICAgIGNvbnN0IG5ld0RlbHRhID0gY3VyU3RhdHVzLmRlbHRhLmFwcGVuZE9uZShub2RlWydAbGFiZWwnXSk7XG5cbiAgICAgICAgICAgIGlmIChub2RlLmNhbGxlZS50eXBlID09PSAnTWVtYmVyRXhwcmVzc2lvbicpIHtcbiAgICAgICAgICAgICAgICAvLyBtZXRob2QgY2FsbFxuICAgICAgICAgICAgICAgIGNvbnN0IFtyZWN2QVZhbCwgcmV0QVZhbF0gPSByZWFkTWVtYmVyKG5vZGUuY2FsbGVlLCBjdXJTdGF0dXMsIGMpO1xuICAgICAgICAgICAgICAgIHJldEFWYWwucHJvcGFnYXRlKFxuICAgICAgICAgICAgICAgICAgICBuZXcgY3N0ci5Jc0NhbGxlZShcbiAgICAgICAgICAgICAgICAgICAgICAgIHJlY3ZBVmFsLFxuICAgICAgICAgICAgICAgICAgICAgICAgYXJnQVZhbHMsXG4gICAgICAgICAgICAgICAgICAgICAgICByZXNBVmFsLFxuICAgICAgICAgICAgICAgICAgICAgICAgY3VyU3RhdHVzLmV4YyxcbiAgICAgICAgICAgICAgICAgICAgICAgIG5ld0RlbHRhKSk7XG4gICAgICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgICAgICAgIC8vIG5vcm1hbCBmdW5jdGlvbiBjYWxsXG4gICAgICAgICAgICAgICAgY29uc3QgY2FsbGVlQVZhbCA9IGMobm9kZS5jYWxsZWUsIGN1clN0YXR1cywgdW5kZWZpbmVkKTtcbiAgICAgICAgICAgICAgICAvLyBjYWxsZWXsnZggcmV0dXJu7J2EIGNhbGwgZXhwcmVzc2lvbuycvOuhnFxuICAgICAgICAgICAgICAgIC8vIGNhbGxlZeydmCBleGNlcHRpb27snYQg7Zi47LacIOy4oeydmCBleGNlcHRpb27sl5Ag7KCE64us7ZW07JW8XG4gICAgICAgICAgICAgICAgY2FsbGVlQVZhbC5wcm9wYWdhdGUoXG4gICAgICAgICAgICAgICAgICAgIG5ldyBjc3RyLklzQ2FsbGVlKFxuICAgICAgICAgICAgICAgICAgICAgICAgbmV3IHR5cGVzLkFWYWwocnRDWC5nbG9iYWxPYmplY3QpLFxuICAgICAgICAgICAgICAgICAgICAgICAgYXJnQVZhbHMsXG4gICAgICAgICAgICAgICAgICAgICAgICByZXNBVmFsLFxuICAgICAgICAgICAgICAgICAgICAgICAgY3VyU3RhdHVzLmV4YyxcbiAgICAgICAgICAgICAgICAgICAgICAgIG5ld0RlbHRhKSk7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICByZXR1cm4gcmVzQVZhbDtcbiAgICAgICAgfSxcblxuICAgICAgICBNZW1iZXJFeHByZXNzaW9uOiBmdW5jdGlvbiAobm9kZSwgY3VyU3RhdHVzLCBjKSB7XG4gICAgICAgICAgICBjb25zdCBbLCByZXRBVmFsXSA9IHJlYWRNZW1iZXIobm9kZSwgY3VyU3RhdHVzLCBjKTtcbiAgICAgICAgICAgIHJldHVybiByZXRBVmFsO1xuICAgICAgICB9LFxuXG4gICAgICAgIFJldHVyblN0YXRlbWVudDogZnVuY3Rpb24gKG5vZGUsIGN1clN0YXR1cywgYykge1xuICAgICAgICAgICAgaWYgKCFub2RlLmFyZ3VtZW50KSByZXR1cm47XG4gICAgICAgICAgICBjb25zdCByZXQgPSBjKG5vZGUuYXJndW1lbnQsIGN1clN0YXR1cywgdW5kZWZpbmVkKTtcbiAgICAgICAgICAgIHJldC5wcm9wYWdhdGUoY3VyU3RhdHVzLnJldCk7XG4gICAgICAgIH1cbiAgICB9KTtcblxuICAgIGNvbnN0IG91dEFWYWwgPSBteVdhbGtlci5yZWN1cnNpdmVXaXRoUmV0dXJuKGFzdE5vZGUsIGluaXRTdGF0dXMsIGNvbnN0cmFpbnRHZW5lcmF0b3IpO1xuICAgIGlmIChvdXRBVmFsKSB7XG4gICAgICAgIC8vIG11c3QgYmUgYW4gZXhwcmVzc2lvbiBib2R5XG4gICAgICAgIG91dEFWYWwucHJvcGFnYXRlKGluaXRTdGF0dXMucmV0KTtcbiAgICB9XG4gICAgLy8gV2UgYWN0dWFsbHkgYWRkZWQgY29uc3RyYWludHNcbiAgICByZXR1cm4gdHJ1ZTtcbn1cblxuZXhwb3J0cy5hZGRDb25zdHJhaW50cyA9IGFkZENvbnN0cmFpbnRzO1xuZXhwb3J0cy5jbGVhckNvbnN0cmFpbnRzID0gY2xlYXJDb25zdHJhaW50cztcbiIsIid1c2Ugc3RyaWN0JztcblxuaW1wb3J0ICogYXMgdHlwZXMgZnJvbSAnLi4vZG9tYWlucy90eXBlcydcbmltcG9ydCAqIGFzIHN0YXR1cyBmcm9tICcuLi9kb21haW5zL3N0YXR1cydcbmltcG9ydCAqIGFzIGNzYyBmcm9tICcuLi9kb21haW5zL2NvbnRleHQnXG5jb25zdCBjR2VuID0gcmVxdWlyZSgnLi9jR2VuJyk7XG5cbmZ1bmN0aW9uIENTVFIoKSB7fVxuQ1NUUi5wcm90b3R5cGUgPSBPYmplY3QuY3JlYXRlKG51bGwpO1xuQ1NUUi5wcm90b3R5cGUuZXF1YWxzID0gZnVuY3Rpb24gKG90aGVyKSB7XG4gICAgcmV0dXJuIHRoaXMgPT09IG90aGVyO1xufTtcblxuZnVuY3Rpb24gUmVhZFByb3AocHJvcCwgdG8pIHtcbiAgICB0aGlzLnByb3AgPSBwcm9wO1xuICAgIHRoaXMudG8gPSB0bztcbn1cblJlYWRQcm9wLnByb3RvdHlwZSA9IE9iamVjdC5jcmVhdGUoQ1NUUi5wcm90b3R5cGUpO1xuUmVhZFByb3AucHJvdG90eXBlLmFkZFR5cGUgPSBmdW5jdGlvbiAob2JqKSB7XG4gICAgaWYgKCEob2JqIGluc3RhbmNlb2YgKHR5cGVzLk9ialR5cGUpKSkgcmV0dXJuO1xuICAgIC8vIHdoZW4gb2JqIGlzIE9ialR5cGUsXG4gICAgY29uc3Qgb3duUHJvcCA9IG9iai5nZXRQcm9wKHRoaXMucHJvcCwgdHJ1ZSk7XG4gICAgaWYgKG93blByb3ApIHtcbiAgICAgICAgLy8gd2hlbiB0aGUgb2JqZWN0IGhhcyB0aGUgcHJvcCxcbiAgICAgICAgb3duUHJvcC5wcm9wYWdhdGUodGhpcy50byk7XG4gICAgfSBlbHNlIGlmIChvYmouZ2V0UHJvcCgnX19wcm90b19fJywgdHJ1ZSkpIHtcbiAgICAgICAgLy8gUHJvcGFnYXRlIGZyb20gdW5rbm93biBwcm9wIGlmIG9iaiBoYXMgaXQuXG4gICAgICAgIGlmIChvYmouaGFzUHJvcChudWxsKSkge1xuICAgICAgICAgICAgb2JqLmdldFByb3AobnVsbCwgdHJ1ZSkucHJvcGFnYXRlKHRoaXMudG8pO1xuICAgICAgICB9XG4gICAgICAgIC8vIHVzZSBwcm90b3R5cGUgY2hhaW5cbiAgICAgICAgb2JqLmdldFByb3AoJ19fcHJvdG9fXycpXG4gICAgICAgICAgLnByb3BhZ2F0ZShuZXcgUmVhZFByb3AodGhpcy5wcm9wLCB0aGlzLnRvKSk7XG4gICAgfVxufTtcblJlYWRQcm9wLnByb3RvdHlwZS5lcXVhbHMgPSBmdW5jdGlvbiAob3RoZXIpIHtcbiAgICBpZiAoIShvdGhlciBpbnN0YW5jZW9mIFJlYWRQcm9wKSkgcmV0dXJuIGZhbHNlO1xuICAgIHJldHVybiB0aGlzLnByb3AgPT09IG90aGVyLnByb3BcbiAgICAgICAgJiYgdGhpcy50by5lcXVhbHMob3RoZXIudG8pO1xufTtcblxuZnVuY3Rpb24gV3JpdGVQcm9wKHByb3AsIGZyb20pIHtcbiAgICB0aGlzLnByb3AgPSBwcm9wO1xuICAgIHRoaXMuZnJvbSA9IGZyb207XG59XG5Xcml0ZVByb3AucHJvdG90eXBlID0gT2JqZWN0LmNyZWF0ZShDU1RSLnByb3RvdHlwZSk7XG5Xcml0ZVByb3AucHJvdG90eXBlLmFkZFR5cGUgPSBmdW5jdGlvbiAob2JqKSB7XG4gICAgaWYgKCEob2JqIGluc3RhbmNlb2YgKHR5cGVzLk9ialR5cGUpKSkgcmV0dXJuO1xuICAgIGNvbnN0IG93blByb3AgPSBvYmouZ2V0UHJvcCh0aGlzLnByb3ApO1xuICAgIHRoaXMuZnJvbS5wcm9wYWdhdGUob3duUHJvcCk7XG4gICAgLy8gSGFuZGxlICdwcm90b3R5cGVPZicgd2hlbiB3cml0aW5nIHRvICdwcm90b3R5cGUnXG4gICAgaWYgKHRoaXMucHJvcCA9PT0gJ3Byb3RvdHlwZScpIHtcbiAgICAgICAgdGhpcy5mcm9tLmdldFR5cGVzKCkuZm9yRWFjaCgodHApID0+IHtcbiAgICAgICAgICAgIHRwLnByb3RvdHlwZU9mLmFkZFR5cGUob2JqKTtcbiAgICAgICAgfSk7XG4gICAgfVxuICAgIC8vIFdoZW4gYXNzaWduaW5nIEZuVHlwZSB0byBhIHByb3AsXG4gICAgdGhpcy5mcm9tLmdldFR5cGVzKCkuZm9yRWFjaCgoZm4pID0+IHtcbiAgICAgICAgaWYgKCEoZm4gaW5zdGFuY2VvZiAodHlwZXMuRm5UeXBlKSkpIHJldHVybjtcbiAgICAgICAgLy8gb2JqJ3MgcHJvdG90eXBlT2YgPT4gc2VsZkFWYWwgb2YgbnVsbCBjb250ZXh0XG4gICAgICAgIGNvbnN0IFtzZWxmQVZhbCwsXSA9IGZuLmdldEZ1bkVudihjc2MuQ2FsbFNpdGVDb250ZXh0Lm51bGxDb250ZXh0KTtcbiAgICAgICAgb2JqLnByb3RvdHlwZU9mLmdldFR5cGVzKCkuZm9yRWFjaCgoY3RvcikgPT4ge1xuICAgICAgICAgICAgaWYgKGN0b3IgaW5zdGFuY2VvZiAodHlwZXMuRm5UeXBlKSlcbiAgICAgICAgICAgICAgICBzZWxmQVZhbC5hZGRUeXBlKGN0b3IuZ2V0SW5zdGFuY2UoKSk7XG4gICAgICAgIH0pO1xuICAgIH0pO1xufTtcblxuZnVuY3Rpb24gSXNBZGRlZChvdGhlciwgdGFyZ2V0KSB7XG4gICAgdGhpcy5vdGhlciA9IG90aGVyO1xuICAgIHRoaXMudGFyZ2V0ID0gdGFyZ2V0O1xufVxuSXNBZGRlZC5wcm90b3R5cGUgPSBPYmplY3QuY3JlYXRlKENTVFIucHJvdG90eXBlKTtcbklzQWRkZWQucHJvdG90eXBlLmFkZFR5cGUgPSBmdW5jdGlvbiAodHlwZSkge1xuICAgIGlmICgodHlwZSA9PT0gdHlwZXMuUHJpbU51bWJlciBcbiAgICAgICAgIHx8IHR5cGUgPT09IHR5cGVzLlByaW1Cb29sZWFuKVxuICAgICAmJiAodGhpcy5vdGhlci5oYXNUeXBlKHR5cGVzLlByaW1OdW1iZXIpIFxuICAgICAgICAgfHwgdGhpcy5vdGhlci5oYXNUeXBlKHR5cGVzLlByaW1Cb29sZWFuKSkpIHtcbiAgICAgICAgdGhpcy50YXJnZXQuYWRkVHlwZSh0eXBlcy5QcmltTnVtYmVyKTtcbiAgICB9XG4gICAgaWYgKHR5cGUgPT09IHR5cGVzLlByaW1TdHJpbmdcbiAgICAgJiYgIXRoaXMub3RoZXIuaXNFbXB0eSgpKSB7XG4gICAgICAgICB0aGlzLnRhcmdldC5hZGRUeXBlKHR5cGVzLlByaW1TdHJpbmcpO1xuICAgIH1cbn07XG5cbmZ1bmN0aW9uIElzQ2FsbGVlKHNlbGYsIGFyZ3MsIHJldCwgZXhjLCBkZWx0YSkge1xuICAgIHRoaXMuc2VsZiA9IHNlbGY7XG4gICAgdGhpcy5hcmdzID0gYXJncztcbiAgICB0aGlzLnJldCA9IHJldDtcbiAgICB0aGlzLmV4YyA9IGV4YztcbiAgICB0aGlzLmRlbHRhID0gZGVsdGE7XG59XG5Jc0NhbGxlZS5wcm90b3R5cGUgPSBPYmplY3QuY3JlYXRlKENTVFIucHJvdG90eXBlKTtcbklzQ2FsbGVlLnByb3RvdHlwZS5hZGRUeXBlID0gZnVuY3Rpb24gKGYpIHtcbiAgICBpZiAoIShmIGluc3RhbmNlb2YgKHR5cGVzLkZuVHlwZSkpKSByZXR1cm47XG4gICAgY29uc3QgZGVsdGFGbiA9IHRoaXMuZGVsdGEudHJ1bmNhdGVGb3IoZik7XG4gICAgY29uc3QgW3NlbGZBVmFsLCByZXRBVmFsLCBleGNBVmFsXSA9IGYuZ2V0RnVuRW52KGRlbHRhRm4pO1xuICAgIGNvbnN0IG5ld1NDID0gZi5vcmlnaW5Ob2RlLmJvZHlbJ0BibG9jayddLmdldFNjb3BlSW5zdGFuY2UoZi5zYywgZGVsdGFGbik7XG4gICAgY29uc3QgZnVuU3RhdHVzXG4gICAgICAgID0gbmV3IHN0YXR1cy5TdGF0dXMoc2VsZkFWYWwsIHJldEFWYWwsIGV4Y0FWYWwsXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgZGVsdGFGbiwgbmV3U0MpO1xuXG4gICAgLy8gYXJyb3cgZnVuY3Rpb24gc2hvdWxkIHVzZSBib3VuZFRoaXMgYW5kIGlnbm9yZSB0aGUgcmVjZWl2ZXIgQVZhbFxuICAgIGlmIChmLmJvdW5kVGhpcykge1xuICAgICAgICBmLmJvdW5kVGhpcy5wcm9wYWdhdGUoc2VsZkFWYWwpO1xuICAgIH0gZWxzZSB7XG4gICAgICAgIHRoaXMuc2VsZi5wcm9wYWdhdGUoc2VsZkFWYWwpO1xuICAgIH1cblxuICAgIGNvbnN0IG1pbkxlbiA9IE1hdGgubWluKHRoaXMuYXJncy5sZW5ndGgsIGYucGFyYW1OYW1lcy5sZW5ndGgpO1xuICAgIGZvciAobGV0IGkgPSAwOyBpIDwgbWluTGVuOyBpKyspIHtcbiAgICAgICAgdGhpcy5hcmdzW2ldLnByb3BhZ2F0ZShuZXdTQy5nZXRBVmFsT2YoZi5wYXJhbU5hbWVzW2ldKSk7XG4gICAgfVxuXG4gICAgLy8gZm9yIGFyZ3VtZW50cyBvYmplY3RcbiAgICBpZiAoZi5vcmlnaW5Ob2RlLmJvZHlbJ0BibG9jayddLnVzZUFyZ3VtZW50c09iamVjdCkge1xuICAgICAgICBjb25zdCBhcmdPYmogPSBmLmdldEFyZ3VtZW50c09iamVjdChkZWx0YUZuKTtcbiAgICAgICAgbmV3U0MuZ2V0QVZhbE9mKCdhcmd1bWVudHMnKS5hZGRUeXBlKGFyZ09iaik7XG4gICAgICAgIGZvciAobGV0IGkgPSAwOyBpIDwgdGhpcy5hcmdzLmxlbmd0aDsgaSsrKSB7XG4gICAgICAgICAgICB0aGlzLmFyZ3NbaV0ucHJvcGFnYXRlKGFyZ09iai5nZXRQcm9wKGkgKyAnJykpO1xuICAgICAgICAgICAgdGhpcy5hcmdzW2ldLnByb3BhZ2F0ZShhcmdPYmouZ2V0UHJvcChudWxsKSk7XG4gICAgICAgIH1cbiAgICAgICAgYXJnT2JqLmdldFByb3AoJ2NhbGxlZScpLmFkZFR5cGUoZik7XG4gICAgICAgIGFyZ09iai5nZXRQcm9wKCdsZW5ndGgnKS5hZGRUeXBlKHR5cGVzLlByaW1OdW1iZXIpO1xuICAgIH1cblxuICAgIC8vIGNvbnN0cmFpbnQgZ2VuZXJhdGlvbiBmb3IgdGhlIGZ1bmN0aW9uIGJvZHlcbiAgICBjR2VuLmFkZENvbnN0cmFpbnRzKGYub3JpZ2luTm9kZS5ib2R5LCBmdW5TdGF0dXMpO1xuXG4gICAgLy8gZ2V0IHJldHVyblxuICAgIHJldEFWYWwucHJvcGFnYXRlKHRoaXMucmV0KTtcbiAgICAvLyBnZXQgZXhjZXB0aW9uXG4gICAgZXhjQVZhbC5wcm9wYWdhdGUodGhpcy5leGMpO1xufTtcblxuZnVuY3Rpb24gSXNDdG9yKGFyZ3MsIHJldCwgZXhjLCBkZWx0YSkge1xuICAgIHRoaXMuYXJncyA9IGFyZ3M7XG4gICAgdGhpcy5yZXQgPSByZXQ7XG4gICAgdGhpcy5leGMgPSBleGM7XG4gICAgdGhpcy5kZWx0YSA9IGRlbHRhO1xufVxuSXNDdG9yLnByb3RvdHlwZSA9IE9iamVjdC5jcmVhdGUoQ1NUUi5wcm90b3R5cGUpO1xuSXNDdG9yLnByb3RvdHlwZS5hZGRUeXBlID0gZnVuY3Rpb24gKGYpIHtcbiAgICAvLyBPbmx5IG5vbi1hcnJvdyBmdW5jdGlvbnMgY2FuIGNyZWF0ZSBpbnN0YW5jZXMuXG4gICAgaWYgKCEoZiBpbnN0YW5jZW9mICh0eXBlcy5GblR5cGUpKSB8fCBmLmJvdW5kVGhpcykge1xuICAgICAgICByZXR1cm47XG4gICAgfVxuICAgIGNvbnN0IGRlbHRhRm4gPSB0aGlzLmRlbHRhLnRydW5jYXRlRm9yKGYpO1xuICAgIGNvbnN0IFtzZWxmQVZhbCwgcmV0QVZhbCwgZXhjQVZhbF0gPSBmLmdldEZ1bkVudihkZWx0YUZuKTtcbiAgICBjb25zdCBuZXdTQyA9IGYub3JpZ2luTm9kZS5ib2R5WydAYmxvY2snXS5nZXRTY29wZUluc3RhbmNlKGYuc2MsIGRlbHRhRm4pO1xuICAgIGNvbnN0IGZ1blN0YXR1c1xuICAgICAgICA9IG5ldyBzdGF0dXMuU3RhdHVzKFxuICAgICAgICAgICAgc2VsZkFWYWwsXG4gICAgICAgICAgICAvLyBJbiBjb25zdHJ1Y3Rvciwgd2UgY2FuIGV4cGxpY2l0bHkgcmV0dXJuIG9ubHkgT2JqVHlwZS5cbiAgICAgICAgICAgIG5ldyBJZk9ialR5cGUocmV0QVZhbCksXG4gICAgICAgICAgICBleGNBVmFsLFxuICAgICAgICAgICAgZGVsdGFGbixcbiAgICAgICAgICAgIG5ld1NDKTtcbiAgICAvLyBmJ3MgaW5zdGFuY2UgaXMgYm91bmQgdG8gJ3RoaXMuJ1xuICAgIGNvbnN0IG5ld09iaiA9IGYuZ2V0SW5zdGFuY2UoKTtcbiAgICBzZWxmQVZhbC5hZGRUeXBlKG5ld09iaik7XG5cbiAgICBjb25zdCBtaW5MZW4gPSBNYXRoLm1pbih0aGlzLmFyZ3MubGVuZ3RoLCBmLnBhcmFtTmFtZXMubGVuZ3RoKTtcbiAgICBmb3IgKGxldCBpID0gMDsgaSA8IG1pbkxlbjsgaSsrKSB7XG4gICAgICAgIHRoaXMuYXJnc1tpXS5wcm9wYWdhdGUobmV3U0MuZ2V0QVZhbE9mKGYucGFyYW1OYW1lc1tpXSkpO1xuICAgIH1cblxuICAgIC8vIGZvciBhcmd1bWVudHMgb2JqZWN0XG4gICAgaWYgKGYub3JpZ2luTm9kZS5ib2R5WydAYmxvY2snXS51c2VBcmd1bWVudHNPYmplY3QpIHtcbiAgICAgICAgY29uc3QgYXJnT2JqID0gZi5nZXRBcmd1bWVudHNPYmplY3QoZGVsdGFGbik7XG4gICAgICAgIG5ld1NDLmdldEFWYWxPZignYXJndW1lbnRzJykuYWRkVHlwZShhcmdPYmopO1xuICAgICAgICBmb3IgKGxldCBpID0gMDsgaSA8IHRoaXMuYXJncy5sZW5ndGg7IGkrKykge1xuICAgICAgICAgICAgdGhpcy5hcmdzW2ldLnByb3BhZ2F0ZShhcmdPYmouZ2V0UHJvcChpICsgJycpKTtcbiAgICAgICAgICAgIHRoaXMuYXJnc1tpXS5wcm9wYWdhdGUoYXJnT2JqLmdldFByb3AobnVsbCkpO1xuICAgICAgICB9XG4gICAgICAgIGFyZ09iai5nZXRQcm9wKCdjYWxsZWUnKS5hZGRUeXBlKGYpO1xuICAgICAgICBhcmdPYmouZ2V0UHJvcCgnbGVuZ3RoJykuYWRkVHlwZSh0eXBlcy5QcmltTnVtYmVyKTtcbiAgICB9XG5cbiAgICAvLyBjb25zdHJhaW50IGdlbmVyYXRpb24gZm9yIHRoZSBmdW5jdGlvbiBib2R5XG4gICAgY0dlbi5hZGRDb25zdHJhaW50cyhmLm9yaWdpbk5vZGUuYm9keSwgZnVuU3RhdHVzKTtcblxuICAgIC8vIHByb3ZpZGUgdHdvIGtpbmRzIG9mIHJlc3VsdCBvZiAnbmV3J1xuICAgIHRoaXMucmV0LmFkZFR5cGUobmV3T2JqKTtcbiAgICByZXRBVmFsLnByb3BhZ2F0ZSh0aGlzLnJldCk7XG4gICAgLy8gZ2V0IGV4Y2VwdGlvblxuICAgIGV4Y0FWYWwucHJvcGFnYXRlKHRoaXMuZXhjKTtcbn07XG5cbi8vIGlnbm9yZSBub24gb2JqZWN0IHR5cGVzXG5mdW5jdGlvbiBJZk9ialR5cGUoYXZhbCkge1xuICAgIHRoaXMuYXZhbCA9IGF2YWw7XG59XG5JZk9ialR5cGUucHJvdG90eXBlID0gT2JqZWN0LmNyZWF0ZShDU1RSLnByb3RvdHlwZSk7XG5JZk9ialR5cGUucHJvdG90eXBlLmFkZFR5cGUgPSBmdW5jdGlvbiAodHlwZSkge1xuICAgIGlmICghKHR5cGUgaW5zdGFuY2VvZiB0eXBlcy5PYmpUeXBlKSkgcmV0dXJuO1xuICAgIHRoaXMuYXZhbC5hZGRUeXBlKHR5cGUpO1xufTtcblxuZXhwb3J0cy5SZWFkUHJvcCA9IFJlYWRQcm9wO1xuZXhwb3J0cy5Xcml0ZVByb3AgPSBXcml0ZVByb3A7XG5leHBvcnRzLklzQWRkZWQgPSBJc0FkZGVkO1xuZXhwb3J0cy5Jc0NhbGxlZSA9IElzQ2FsbGVlO1xuZXhwb3J0cy5Jc0N0b3IgPSBJc0N0b3I7XG4iLCIvLyBDb250ZXh0IGZvciBrLUNGQSBhbmFseXNpc1xuLy9cbi8vIEFzc3VtZSBhIGNvbnRleHQgaXMgYW4gYXJyYXkgb2YgbnVtYmVycy5cbi8vIEEgbnVtYmVyIGluIHN1Y2ggbGlzdCBkZW5vdGVzIGEgY2FsbCBzaXRlLCB0aGF0IGlzIEBsYWJlbCBvZiBhIENhbGxFeHByZXNzaW9uLlxuLy8gV2Uga2VlcCB0aGUgbW9zdCByZWNlbnQgJ2snIGNhbGwtc2l0ZXMuXG4vLyBFcXVhbGl0eSBvbiBjb250ZXh0cyBzaG91bGQgbG9vayBpbnRvIHRoZSBudW1iZXJzLlxuXG5leHBvcnQgY29uc3Qgc2Vuc2l0aXZpdHlQYXJhbWV0ZXIgPSB7XG4gICAgLy8gbWF4aW11bSBsZW5ndGggb2YgY29udGV4dFxuICAgIG1heERlcHRoSzogMCxcbiAgICAvL1xuICAgIGNvbnRleHRMZW5ndGhPZkZ1bmM6IGZ1bmN0aW9uIChmbikge1xuICAgICAgICByZXR1cm4gMDtcbiAgICB9XG59O1xuXG5leHBvcnQgZnVuY3Rpb24gY2hhbmdlU2Vuc2l0aXZpdHlQYXJhbWV0ZXIocGFyYW0pIHtcbiAgICBzZW5zaXRpdml0eVBhcmFtZXRlci5tYXhEZXB0aEsgPSBwYXJhbS5tYXhEZXB0aEs7XG4gICAgc2Vuc2l0aXZpdHlQYXJhbWV0ZXIuY29udGV4dExlbmd0aE9mRnVuYyA9IHBhcmFtLmNvbnRleHRMZW5ndGhPZkZ1bmM7XG59XG5cbi8vIEZ1bmN0aW9uYWwgb2JqZWN0cyBmb3IgY2FsbC1zaXRlIGNvbnRleHRcbmV4cG9ydCBjbGFzcyBDYWxsU2l0ZUNvbnRleHQge1xuXG4gICAgY29uc3RydWN0b3IobGlzdCkge1xuICAgICAgICBmb3IgKGxldCBjdHggb2YgQ2FsbFNpdGVDb250ZXh0LmNvbnRleHRQb29sLnZhbHVlcygpKSB7XG4gICAgICAgICAgICBpZiAoY3R4Ll9oYXNTYW1lTGlzdChsaXN0KSkge1xuICAgICAgICAgICAgICAgIC8vIHVzZSBleGlzdGluZyBjb250ZXh0XG4gICAgICAgICAgICAgICAgcmV0dXJuIGN0eDtcbiAgICAgICAgICAgIH1cbiAgICAgICAgfVxuICAgICAgICAvLyBjbG9uZSB0aGUgZ2l2ZW4gbGlzdFxuICAgICAgICBpZiAobGlzdCA9PT0gbnVsbCkge1xuICAgICAgICAgICAgdGhpcy5jc0xpc3QgPSBudWxsO1xuICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgICAgdGhpcy5jc0xpc3QgPSBsaXN0LnNsaWNlKDApO1xuICAgICAgICB9XG4gICAgICAgIC8vIGFkZCB0aGUgY3VycmVudCBpbnN0YW5jZSB0byB0aGUgcG9vbFxuICAgICAgICBDYWxsU2l0ZUNvbnRleHQuY29udGV4dFBvb2wuYWRkKHRoaXMpO1xuICAgIH1cblxuICAgIC8qKlxuICAgICAqIEEgcHJpdmF0ZSBtZXRob2QgZm9yIGNvbnRleHQgZXF1YWxpdHlcbiAgICAgKiBAcGFyYW0gbGlzdCAtIGFycmF5IGNvbXBvc2VkIG9mIGNvbnRleHQgZWxlbWVudHNcbiAgICAgKiBAcmV0dXJucyB7Ym9vbGVhbn1cbiAgICAgKi9cbiAgICBfaGFzU2FtZUxpc3QobGlzdCkge1xuICAgICAgICBpZiAodGhpcy5jc0xpc3QgPT09IG51bGwpIHtcbiAgICAgICAgICAgIHJldHVybiBsaXN0ID09PSBudWxsO1xuICAgICAgICB9XG4gICAgICAgIGlmIChsaXN0ID09PSBudWxsKSB7XG4gICAgICAgICAgICByZXR1cm4gdGhpcy5jc0xpc3QgPT09IG51bGw7XG4gICAgICAgIH1cbiAgICAgICAgaWYgKHRoaXMuY3NMaXN0Lmxlbmd0aCAhPT0gbGlzdC5sZW5ndGgpIHtcbiAgICAgICAgICAgIHJldHVybiBmYWxzZTtcbiAgICAgICAgfVxuICAgICAgICBmb3IgKGxldCBpID0gMDsgaSA8IHRoaXMuY3NMaXN0Lmxlbmd0aDsgaSsrKSB7XG4gICAgICAgICAgICBpZiAodGhpcy5jc0xpc3RbaV0gIT09IGxpc3RbaV0pIHJldHVybiBmYWxzZTtcbiAgICAgICAgfVxuICAgICAgICByZXR1cm4gdHJ1ZTtcbiAgICB9XG5cbiAgICAvKipcbiAgICAgKiBSZXR1cm4gdGhlIGNvbnRleHQgd2hpY2ggaXMgbXlzZWxmICsgY2FsbFNpdGUuXG4gICAgICogSWYgSSBhbSBudWxsQ29udGV4dCwgdGhlIHJlc3VsdCBpcyBteXNlbGYuXG4gICAgICogQHBhcmFtIGNhbGxTaXRlIC0gYSBjYWxsLXNpdGUgdG8gYXBwZW5kXG4gICAgICogQHJldHVybnMge0NhbGxTaXRlQ29udGV4dH1cbiAgICAgKi9cbiAgICBhcHBlbmRPbmUoY2FsbFNpdGUpIHtcbiAgICAgICAgLy8gaWYgbnVsbCBjb250ZXh0LCByZXN1bHQgaXMgaXRzZWxmXG4gICAgICAgIGlmICh0aGlzID09PSBDYWxsU2l0ZUNvbnRleHQubnVsbENvbnRleHQpIHtcbiAgICAgICAgICAgIHJldHVybiB0aGlzO1xuICAgICAgICB9XG4gICAgICAgIC8vIHVzZSBjb25jYXQgdG8gY3JlYXRlIGEgbmV3IGFycmF5XG4gICAgICAgIC8vIG9sZGVzdCBvbmUgY29tZXMgZmlyc3RcbiAgICAgICAgY29uc3QgYXBwZW5kZWQgPSB0aGlzLmNzTGlzdC5jb25jYXQoY2FsbFNpdGUpO1xuICAgICAgICBpZiAoYXBwZW5kZWQubGVuZ3RoID4gc2Vuc2l0aXZpdHlQYXJhbWV0ZXIubWF4RGVwdGhLKSB7XG4gICAgICAgICAgICBhcHBlbmRlZC5zaGlmdCgpO1xuICAgICAgICB9XG4gICAgICAgIHJldHVybiBuZXcgQ2FsbFNpdGVDb250ZXh0KGFwcGVuZGVkKTtcbiAgICB9XG5cbiAgICAvKipcbiAgICAgKiBUcnVuY2F0ZSBjb250ZXh0IGFjY29yZGluZyB0byB0aGUgZ2l2ZW4gZnVuY3Rpb24uXG4gICAgICogQHBhcmFtIHtGblR5cGV9IGZuXG4gICAgICogQHJldHVybnMge0NhbGxTaXRlQ29udGV4dH1cbiAgICAgKi9cbiAgICB0cnVuY2F0ZUZvcihmbikge1xuICAgICAgICAvLyBmb3IgbnVsbENvbnRleHQsXG4gICAgICAgIGlmICh0aGlzID09PSBDYWxsU2l0ZUNvbnRleHQubnVsbENvbnRleHQpIHtcbiAgICAgICAgICAgIHJldHVybiB0aGlzO1xuICAgICAgICB9XG4gICAgICAgIC8vIGNvbXB1dGUgdGhlIGxlbmd0aCBvZiB0aGUgY29udGV4dFxuICAgICAgICBjb25zdCBjb250ZXh0TGVuZ3RoID0gc2Vuc2l0aXZpdHlQYXJhbWV0ZXIuY29udGV4dExlbmd0aE9mRnVuYyhmbik7XG4gICAgICAgIGlmIChjb250ZXh0TGVuZ3RoID09PSAwKSB7XG4gICAgICAgICAgICAvLyBjb250ZXh0IG9mIGxlbmd0aCAwXG4gICAgICAgICAgICByZXR1cm4gQ2FsbFNpdGVDb250ZXh0LmVwc2lsb25Db250ZXh0O1xuICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgICAgLy8gY2hvb3NlIGxhc3Qgc2V2ZXJhbCBjYWxsLXNpdGVzXG4gICAgICAgICAgICByZXR1cm4gbmV3IENhbGxTaXRlQ29udGV4dCh0aGlzLmNzTGlzdC5zbGljZSgtY29udGV4dExlbmd0aCkpO1xuICAgICAgICB9XG4gICAgfVxuXG4gICAgdG9TdHJpbmcoKSB7XG4gICAgICAgIHJldHVybiB0aGlzLmNzTGlzdC50b1N0cmluZygpO1xuICAgIH1cbn1cblxuLy8gRGVjbGFyaW5nIGNsYXNzIGZpZWxkcyBmb3IgQ2FsbFNpdGVDb250ZXh0XG5DYWxsU2l0ZUNvbnRleHQuY29udGV4dFBvb2wgPSBuZXcgU2V0KCk7XG4vLyBudWxsQ29udGV4dCBpcyBmb3IgZnVuY3Rpb25zIHRoYXQgbmV2ZXIgYmUgY2FsbGVkXG5DYWxsU2l0ZUNvbnRleHQubnVsbENvbnRleHQgPSBuZXcgQ2FsbFNpdGVDb250ZXh0KG51bGwpO1xuLy8gZXBzaWxvbkNvbnRleHQgaXMgZm9yIGNvbnRleHQgb2YgbGVuZ3RoIDBcbkNhbGxTaXRlQ29udGV4dC5lcHNpbG9uQ29udGV4dCA9IG5ldyBDYWxsU2l0ZUNvbnRleHQoW10pO1xuIiwiLy8gU3RhdHVzOlxuLy8geyBzZWxmICA6IEFWYWwsXG4vLyAgIHJldCAgIDogQVZhbCxcbi8vICAgZXhjICAgOiBBVmFsLFxuLy8gICBkZWx0YSA6IENvbnRleHQsXG4vLyAgIHNjICAgIDogU2NvcGUgfVxuXG5leHBvcnQgY2xhc3MgU3RhdHVzIHtcbiAgICBjb25zdHJ1Y3RvcihzZWxmLCByZXQsIGV4YywgZGVsdGEsIHNjKSB7XG4gICAgICAgIHRoaXMuc2VsZiA9IHNlbGY7XG4gICAgICAgIHRoaXMucmV0ID0gcmV0O1xuICAgICAgICB0aGlzLmV4YyA9IGV4YztcbiAgICAgICAgdGhpcy5kZWx0YSA9IGRlbHRhO1xuICAgICAgICB0aGlzLnNjID0gc2M7XG4gICAgfVxuXG4gICAgZXF1YWxzKG90aGVyKSB7XG4gICAgICAgIHJldHVybiB0aGlzLnNlbGYgPT09IG90aGVyLnNlbGYgJiZcbiAgICAgICAgICAgIHRoaXMucmV0ID09PSBvdGhlci5yZXQgJiZcbiAgICAgICAgICAgIHRoaXMuZXhjID09PSBvdGhlci5leGMgJiZcbiAgICAgICAgICAgIHRoaXMuZGVsdGEgPT09IG90aGVyLmRlbHRhICYmXG4gICAgICAgICAgICB0aGlzLnNjID09PSBvdGhlci5zYztcbiAgICB9XG5cbiAgICBnZXROZXdTdGF0dXMoY2hhbmdlU3RhdHVzKSB7XG4gICAgICAgIGNvbnN0IG5ld1N0YXR1cyA9IG5ldyBTdGF0dXM7XG4gICAgICAgIGZvciAobGV0IHAgaW4gdGhpcykge1xuICAgICAgICAgICAgaWYgKHRoaXMuaGFzT3duUHJvcGVydHkocCkpIHtcbiAgICAgICAgICAgICAgICBpZiAoY2hhbmdlU3RhdHVzLmhhc093blByb3BlcnR5KHApKSB7XG4gICAgICAgICAgICAgICAgICAgIG5ld1N0YXR1c1twXSA9IGNoYW5nZVN0YXR1c1twXTtcbiAgICAgICAgICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgICAgICAgICAgICBuZXdTdGF0dXNbcF0gPSB0aGlzW3BdO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgIH1cbiAgICAgICAgfVxuICAgICAgICByZXR1cm4gbmV3U3RhdHVzO1xuICAgIH1cbn1cbiIsIi8vIGZvciBERUJVR1xudmFyIGNvdW50ID0gMDtcbi8qKlxuICogdGhlIGFic3RyYWN0IHZhbHVlIGZvciBhIGNvbmNyZXRlIHZhbHVlXG4gKiB3aGljaCBpcyBhIHNldCBvZiB0eXBlcy5cbiAqL1xuZXhwb3J0IGNsYXNzIEFWYWwge1xuICAgIC8qKlxuICAgICAqIEBwYXJhbSB7VHlwZX0gdHlwZSAtIGdpdmUgYSB0eXBlIHRvIG1ha2UgQVZhbCB3aXRoIGEgc2luZ2xlIHR5cGVcbiAgICAgKi9cbiAgICBjb25zdHJ1Y3Rvcih0eXBlKSB7XG4gICAgICAgIC8vIHR5cGU6IGNvbnRhaW5lZCB0eXBlc1xuICAgICAgICAvLyBXZSBhc3N1bWUgdHlwZXMgYXJlIGRpc3Rpbmd1aXNoYWJsZSBieSAnPT09J1xuICAgICAgICBpZiAodHlwZSkgdGhpcy50eXBlcyA9IG5ldyBTZXQoW3R5cGVdKTtcbiAgICAgICAgZWxzZSB0aGlzLnR5cGVzID0gbmV3IFNldCgpO1xuICAgICAgICAvLyBmb3J3YXJkczogcHJvcGFnYXRpb24gdGFyZ2V0c1xuICAgICAgICAvLyBXZSBhc3N1bWUgdGFyZ2V0cyBhcmUgZGlzdGluZ3Vpc2hhYmxlIGJ5ICdlcXVhbHMnIG1ldGhvZFxuICAgICAgICB0aGlzLmZvcndhcmRzID0gbmV3IFNldCgpO1xuICAgICAgICAvLyBmb3IgREVCVUdcbiAgICAgICAgdGhpcy5faWQgPSBjb3VudCsrO1xuICAgIH1cblxuICAgIC8qKiBDaGVjayB3aGV0aGVyIGl0IGhhcyBhbnkgdHlwZVxuICAgICAqIEByZXR1cm5zIHtib29sZWFufVxuICAgICAqL1xuICAgIGlzRW1wdHkoKSB7XG4gICAgICAgIHJldHVybiB0aGlzLnR5cGVzLnNpemUgPT09IDA7XG4gICAgfVxuXG4gICAgZ2V0U2l6ZSgpIHtcbiAgICAgICAgcmV0dXJuIHRoaXMudHlwZXMuc2l6ZTtcbiAgICB9XG5cbiAgICAvKipcbiAgICAgKiBAcmV0dXJucyB7U2V0LjxUeXBlPn1cbiAgICAgKi9cbiAgICBnZXRUeXBlcygpIHtcbiAgICAgICAgcmV0dXJuIHRoaXMudHlwZXM7XG4gICAgfVxuXG4gICAgLyoqXG4gICAgICogQHBhcmFtIHtUeXBlfSB0eXBlXG4gICAgICogQHJldHVybnMge2Jvb2xlYW59XG4gICAgICovXG4gICAgaGFzVHlwZSh0eXBlKSB7XG4gICAgICAgIHJldHVybiB0aGlzLnR5cGVzLmhhcyh0eXBlKTtcbiAgICB9XG5cbiAgICAvKipcbiAgICAgKiBBZGQgYSB0eXBlLlxuICAgICAqIEBwYXJhbSB7VHlwZX0gdHlwZVxuICAgICAqIEByZXR1cm5zIHtib29sZWFufVxuICAgICAqL1xuICAgIGFkZFR5cGUodHlwZSkge1xuICAgICAgICBpZiAodGhpcy50eXBlcy5oYXModHlwZSkpIHtcbiAgICAgICAgICAgIHJldHVybiBmYWxzZTtcbiAgICAgICAgfVxuICAgICAgICAvLyBnaXZlbiB0eXBlIGlzIG5ld1xuICAgICAgICB0aGlzLnR5cGVzLmFkZCh0eXBlKTtcbiAgICAgICAgLy8gc2VuZCB0byBwcm9wYWdhdGlvbiB0YXJnZXRzXG4gICAgICAgIHRoaXMuZm9yd2FyZHMuZm9yRWFjaChmd2QgPT4ge1xuICAgICAgICAgICAgZndkLmFkZFR5cGUodHlwZSk7XG4gICAgICAgIH0pO1xuICAgICAgICByZXR1cm4gdHJ1ZTtcbiAgICB9XG5cbiAgICAvKipcbiAgICAgKiBAcGFyYW0ge0FWYWx9IHRhcmdldFxuICAgICAqL1xuICAgIHByb3BhZ2F0ZSh0YXJnZXQpIHtcbiAgICAgICAgaWYgKCF0aGlzLmFkZEZvcndhcmQodGFyZ2V0KSkgcmV0dXJuO1xuICAgICAgICAvLyB0YXJnZXQgaXMgbmV3bHkgYWRkZWRcbiAgICAgICAgLy8gc2VuZCB0eXBlcyB0byB0aGUgbmV3IHRhcmdldFxuICAgICAgICB0aGlzLnR5cGVzLmZvckVhY2godHlwZSA9PiB7XG4gICAgICAgICAgICB0YXJnZXQuYWRkVHlwZSh0eXBlKTtcbiAgICAgICAgfSk7XG4gICAgfVxuXG4gICAgLyoqXG4gICAgICogQWRkIGEgcHJvcGFnYXRpb24gdGFyZ2V0XG4gICAgICogQHBhcmFtIHtBVmFsfSBmd2RcbiAgICAgKiBAcmV0dXJucyB7Ym9vbGVhbn0gLSByZXR1cm5zIGZhbHNlIGlmIGl0IGFscmVhZHkgaGFzIHRoZSB0YXJnZXRcbiAgICAgKi9cbiAgICBhZGRGb3J3YXJkKGZ3ZCkge1xuICAgICAgICBmb3IgKGxldCBvbGRGd2Qgb2YgdGhpcy5mb3J3YXJkcykge1xuICAgICAgICAgICAgaWYgKGZ3ZC5lcXVhbHMob2xkRndkKSkge1xuICAgICAgICAgICAgICAgIHJldHVybiBmYWxzZTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgfVxuICAgICAgICB0aGlzLmZvcndhcmRzLmFkZChmd2QpO1xuICAgICAgICByZXR1cm4gdHJ1ZTtcbiAgICB9XG5cbiAgICAvKipcbiAgICAgKiBDaGVjayBpZiB0aGV5IGFyZSB0aGUgc2FtZVxuICAgICAqIEBwYXJhbSB7QVZhbH0gb3RoZXJcbiAgICAgKiBAcmV0dXJucyB7Ym9vbGVhbn1cbiAgICAgKi9cbiAgICBlcXVhbHMob3RoZXIpIHtcbiAgICAgICAgLy8gc2ltcGxlIHJlZmVyZW5jZSBjb21wYXJpc29uXG4gICAgICAgIHJldHVybiB0aGlzID09PSBvdGhlcjtcbiAgICB9XG5cbiAgICAvKipcbiAgICAgKiBUT0RPOiBjaGVjayB3aGV0aGVyIHdlIHJlYWxseSBuZWVkIHRoaXMgbWV0aG9kLlxuICAgICAqIEBwYXJhbSB7c3RyaW5nfG51bGx9IHByb3BcbiAgICAgKiBAcmV0dXJucyB7QVZhbH1cbiAgICAgKi9cbiAgICBnZXRQcm9wKHByb3ApIHtcbiAgICAgICAgaWYgKHRoaXMucHJvcHMuaGFzKHByb3ApKSB7XG4gICAgICAgICAgICByZXR1cm4gdGhpcy5wcm9wcy5nZXQocHJvcCk7XG4gICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgICByZXR1cm4gQVZhbE51bGw7XG4gICAgICAgIH1cbiAgICB9XG5cbiAgICB0b1N0cmluZygpIHtcbiAgICAgICAgY29uc3QgdmlzaXRlZFR5cGVzID0gbmV3IFNldCgpO1xuICAgICAgICByZXR1cm4gdGhpcy5fdG9TdHJpbmcodmlzaXRlZFR5cGVzKTtcbiAgICB9XG5cbiAgICBfdG9TdHJpbmcodmlzaXRlZFR5cGVzKSB7XG4gICAgICAgIGNvbnN0IHR5cGVTdHJpbmdzID0gW107XG4gICAgICAgIGZvciAobGV0IHRwIG9mIHRoaXMudHlwZXMpIHtcbiAgICAgICAgICAgIGlmICh2aXNpdGVkVHlwZXMuaGFzKHRwKSkge1xuICAgICAgICAgICAgICAgIHR5cGVTdHJpbmdzLnB1c2goJz8nKTtcbiAgICAgICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgICAgICAgdHlwZVN0cmluZ3MucHVzaCh0cC5fdG9TdHJpbmcodmlzaXRlZFR5cGVzKSk7XG4gICAgICAgICAgICB9XG4gICAgICAgIH1cbiAgICAgICAgcmV0dXJuIHR5cGVTdHJpbmdzLmpvaW4oJ3wnKTtcbiAgICB9XG59XG5cbi8qKlxuICogdGhlIHN1cGVyIGNsYXNzIG9mIGFsbCB0eXBlc1xuICogZWFjaCB0eXBlIHNob3VsZCBiZSBkaXN0aW5ndWlzaGFibGUgYnkgJz09PScgb3BlcmF0aW9uLlxuICovXG5jbGFzcyBUeXBlIHtcbiAgICAvKipcbiAgICAgKiBDcmVhdGUgYSBuZXcgdHlwZVxuICAgICAqIEBwYXJhbSB7c3RyaW5nfSBuYW1lXG4gICAgICovXG4gICAgY29uc3RydWN0b3IobmFtZSkge1xuICAgICAgICB0aGlzLm5hbWUgPSBuYW1lO1xuICAgIH1cblxuICAgIC8qKlxuICAgICAqIFJldHVybnMgdGhlIG5hbWUgb2YgdHlwZVxuICAgICAqIEByZXR1cm5zIHtzdHJpbmd9XG4gICAgICovXG4gICAgZ2V0TmFtZSgpIHtcbiAgICAgICAgcmV0dXJuIHRoaXMubmFtZTtcbiAgICB9XG5cbiAgICAvKipcbiAgICAgKiBEZWZhdWx0IGltcGxlbWVudGF0aW9uIGZvciB0b1N0cmluZ1xuICAgICAqIFRoaXMgc2hvdWxkIGJlIG92ZXJyaWRkZW4gZm9yIHNvcGhpc3RpY2F0ZWQgdHlwZXNcbiAgICAgKiBAcmV0dXJucyB7c3RyaW5nfVxuICAgICAqL1xuICAgIF90b1N0cmluZygpIHtcbiAgICAgICAgcmV0dXJuIHRoaXMuZ2V0TmFtZSgpO1xuICAgIH1cbn1cblxuXG4vKipcbiAqIDEuIG9iamVjdCB0eXBlc1xuICovXG5leHBvcnQgY2xhc3MgT2JqVHlwZSBleHRlbmRzIFR5cGUge1xuICAgIC8qKlxuICAgICAqIEBwYXJhbSB7QVZhbH0gcHJvdG8gLSBBVmFsIG9mIGNvbnN0cnVjdG9yJ3MgcHJvdG90eXBlXG4gICAgICogQHBhcmFtIHtzdHJpbmd9IG5hbWUgLSBndWVzc2VkIG5hbWVcbiAgICAgKi9cbiAgICBjb25zdHJ1Y3Rvcihwcm90bywgbmFtZSkge1xuICAgICAgICBzdXBlcihuYW1lKTtcbiAgICAgICAgdGhpcy5wcm9wcyA9IG5ldyBNYXAoKTtcbiAgICAgICAgLy8gc2hhcmUgcHJvdG8gd2l0aCBfX3Byb3RvX19cbiAgICAgICAgdGhpcy5zZXRQcm9wKCdfX3Byb3RvX18nLCBwcm90byk7XG4gICAgICAgIC8vIHJlbWVtYmVyIHdob3NlIHByb3RvdHlwZSBJIGFtXG4gICAgICAgIHRoaXMucHJvdG90eXBlT2YgPSBuZXcgQVZhbCgpO1xuICAgIH1cblxuICAgIC8qKlxuICAgICAqIEBwYXJhbSB7c3RyaW5nfG51bGx9IHByb3AgLSBudWxsIGZvciBjb21wdXRlZCBwcm9wc1xuICAgICAqIEBwYXJhbSB7Ym9vbGVhbn0gcmVhZE9ubHkgLSBpZiBmYWxzZSwgY3JlYXRlIEFWYWwgZm9yIHByb3AgaWYgbmVjZXNzYXJ5XG4gICAgICogQHJldHVybnMge0FWYWx9IEFWYWwgb2YgdGhlIHByb3BlcnR5XG4gICAgICovXG4gICAgZ2V0UHJvcChwcm9wLCByZWFkT25seSkge1xuICAgICAgICBpZiAodGhpcy5wcm9wcy5oYXMocHJvcCkpIHtcbiAgICAgICAgICAgIHJldHVybiB0aGlzLnByb3BzLmdldChwcm9wKTtcbiAgICAgICAgfSBlbHNlIGlmIChyZWFkT25seSkge1xuICAgICAgICAgICAgcmV0dXJuIG51bGw7XG4gICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgICB2YXIgbmV3UHJvcEFWYWwgPSBuZXcgQVZhbDtcbiAgICAgICAgICAgIHRoaXMucHJvcHMuc2V0KHByb3AsIG5ld1Byb3BBVmFsKTtcbiAgICAgICAgICAgIHJldHVybiBuZXdQcm9wQVZhbDtcbiAgICAgICAgfVxuICAgIH1cblxuICAgIC8qKlxuICAgICAqIFdlIHVzZSB0aGlzIGZ1bmN0aW9uIHRvIHNoYXJlIC5wcm90b3R5cGUgd2l0aCBpbnN0YW5jZXMgX19wcm90b19fXG4gICAgICogSXQgaXMgcG9zc2libGUgdG8gdXNlIHRoaXMgZnVuY3Rpb24gdG8gbWVyZ2UgQVZhbHMgdG8gb3B0aW1pemUgdGhlIGFuYWx5emVyLlxuICAgICAqIEBwYXJhbSB7c3RyaW5nfG51bGx9IHByb3AgLSBudWxsIGZvciBjb21wdXRlZCBwcm9wc1xuICAgICAqIEBwYXJhbSB7QVZhbH0gYXZhbFxuICAgICAqL1xuICAgIHNldFByb3AocHJvcCwgYXZhbCkge1xuICAgICAgICB0aGlzLnByb3BzLnNldChwcm9wLCBhdmFsKTtcbiAgICB9XG5cbiAgICAvKipcbiAgICAgKiBSZXR1cm5zIGl0ZXJhdG9yIG9mIGl0cyBvd24gcHJvcGVydHkgbmFtZXNcbiAgICAgKiBAcmV0dXJucyB7SXRlcmF0b3IuPHN0cmluZz59XG4gICAgICovXG4gICAgZ2V0T3duUHJvcE5hbWVzKCkge1xuICAgICAgICByZXR1cm4gdGhpcy5wcm9wcy5rZXlzKCk7XG4gICAgfVxuXG4gICAgLyoqXG4gICAgICogVE9ETzogQ2hlY2sgdGhpcyBmdW5jdGlvbidzIG5lY2Vzc2l0eVxuICAgICAqIEBwYXJhbSB7c3RyaW5nfG51bGx9IHByb3BcbiAgICAgKiBAcmV0dXJucyB7Ym9vbGVhbn1cbiAgICAgKi9cbiAgICBoYXNQcm9wKHByb3ApIHtcbiAgICAgICAgcmV0dXJuIHRoaXMucHJvcHMuaGFzKHByb3ApO1xuICAgIH1cblxuICAgIC8qKlxuICAgICAqIFRPRE86IENoZWNrIHRoaXMgZnVuY3Rpb24ncyBuZWNlc3NpdHlcbiAgICAgKiBAcGFyYW0ge1R5cGV9IHR5cGVcbiAgICAgKiBAcGFyYW0ge3N0cmluZ3xudWxsfSBwcm9wXG4gICAgICovXG4gICAgYWRkVHlwZVRvUHJvcCh0eXBlLCBwcm9wKSB7XG4gICAgICAgIGlmICghdGhpcy5wcm9wcy5oYXMocHJvcCkpIHtcbiAgICAgICAgICAgIHRoaXMucHJvcHMuc2V0KHByb3AsIG5ldyBBVmFsKTtcbiAgICAgICAgfVxuICAgICAgICBpZiAodGhpcy5wcm9wcy5nZXQocHJvcCkuaGFzVHlwZSh0eXBlKSkgcmV0dXJuO1xuICAgICAgICB0aGlzLnByb3BzLmdldChwcm9wKS5hZGRUeXBlKHR5cGUpO1xuICAgIH1cblxuICAgIC8qKlxuICAgICAqIFRPRE86IENoZWNrIHRoaXMgZnVuY3Rpb24ncyBuZWNlc3NpdHlcbiAgICAgKiBAcGFyYW0ge0FWYWx9IGF2YWxcbiAgICAgKiBAcGFyYW0ge3N0cmluZ30gcHJvcFxuICAgICAqL1xuICAgIGpvaW5BVmFsVG9Qcm9wKGF2YWwsIHByb3ApIHtcbiAgICAgICAgdmFyIHNlbGYgPSB0aGlzO1xuICAgICAgICBhdmFsLmdldFR5cGVzKCkuZm9yRWFjaChmdW5jdGlvbiAodHlwZSkge1xuICAgICAgICAgICAgc2VsZi5hZGRUeXBlVG9Qcm9wKHR5cGUsIHByb3ApO1xuICAgICAgICB9KTtcbiAgICB9XG5cbiAgICAvKipcbiAgICAgKiBTaG93IG9iamVjdCdzIG93biBwcm9wZXJ0eSBuYW1lc1xuICAgICAqIEBwYXJhbSB7U2V0LjxUeXBlPn0gdmlzaXRlZFR5cGVzXG4gICAgICogQHJldHVybnMge3N0cmluZ31cbiAgICAgKi9cbiAgICBfdG9TdHJpbmcodmlzaXRlZFR5cGVzKSB7XG4gICAgICAgIGlmICh0aGlzLm5hbWUgPT09IHVuZGVmaW5lZCkge1xuICAgICAgICAgICAgY29uc3QgcHJvcHMgPSBbXTtcbiAgICAgICAgICAgIGZvciAobGV0IHAgb2YgdGhpcy5wcm9wcy5rZXlzKCkpIHtcbiAgICAgICAgICAgICAgICAvLyBza2lwcGluZyBfX3Byb3RvX19cbiAgICAgICAgICAgICAgICBpZiAocCA9PT0gJ19fcHJvdG9fXycpIGNvbnRpbnVlO1xuICAgICAgICAgICAgICAgIHByb3BzLnB1c2gocCk7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICByZXR1cm4gJ3snICsgcHJvcHMuam9pbigpICsgJ30nO1xuICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgICAgcmV0dXJuIHRoaXMubmFtZTtcbiAgICAgICAgfVxuICAgIH1cbn1cblxuLy8gbWFrZSBhbiBPYmogZnJvbSB0aGUgZ2xvYmFsIHNjb3BlXG5leHBvcnQgZnVuY3Rpb24gbWtPYmpGcm9tR2xvYmFsU2NvcGUoZ1Njb3BlKSB7XG4gICAgdmFyIGdPYmogPSBuZXcgT2JqVHlwZShBVmFsTnVsbCwgJypnbG9iYWwgc2NvcGUqJyk7XG4gICAgZ09iai5wcm9wcyA9IGdTY29wZS52YXJNYXA7XG4gICAgLy8gT3ZlcnJpZGUgZ2V0UHJvcCBtZXRob2QgZm9yIGdsb2JhbCBvYmplY3RcbiAgICAvLyBXZSBpZ25vcmUgJ3JlYWRPbmx5JyBwYXJhbWV0ZXIgdG8gYWx3YXlzIHJldHVybiBpdHMgb3duIHByb3AgQVZhbCBcbiAgICBnT2JqLmdldFByb3AgPSBmdW5jdGlvbiAocHJvcCkge1xuICAgICAgICBpZiAoIWdTY29wZS52Yi5oYXNMb2NhbFZhcihwcm9wKSkge1xuICAgICAgICAgICAgLy8gd2hlbiB3ZSByZWZlciBwcm9wIG9mIHRoZSBnbG9iYWwgb2JqZWN0XG4gICAgICAgICAgICBnU2NvcGUudmIuYWRkRGVjbGFyZWRMb2NhbFZhcihwcm9wKTtcbiAgICAgICAgfVxuICAgICAgICByZXR1cm4gT2JqVHlwZS5wcm90b3R5cGUuZ2V0UHJvcC5jYWxsKHRoaXMsIHByb3ApO1xuICAgIH07XG4gICAgcmV0dXJuIGdPYmo7XG59XG5cbi8qKlxuICogMi4gcHJpbWl0aXZlIHR5cGVzXG4gKi9cbmV4cG9ydCBjbGFzcyBQcmltVHlwZSBleHRlbmRzIFR5cGUge1xuICAgIC8qKlxuICAgICAqIEBwYXJhbSB7c3RyaW5nfSBuYW1lXG4gICAgICovXG4gICAgY29uc3RydWN0b3IobmFtZSkge1xuICAgICAgICBzdXBlcihuYW1lKTtcbiAgICB9XG59XG5cbi8qKlxuICogMy4gZnVuY3Rpb24gdHlwZXNcbiAqIHRoZSBuYW1lIGlzIHVzZWQgZm9yIHRoZSB0eXBlIG9mIHRoZSBpbnN0YW5jZXMgZnJvbSB0aGUgZnVuY3Rpb25cbiAqL1xuZXhwb3J0IGNsYXNzIEZuVHlwZSBleHRlbmRzIE9ialR5cGUge1xuICAgIC8qKlxuICAgICAqIEBwYXJhbSB7QVZhbH0gZm5fcHJvdG8gLSBBVmFsIGZvciBjb25zdHJ1Y3RvcidzIC5wcm90b3R5cGVcbiAgICAgKiBAcGFyYW0ge3N0cmluZ30gbmFtZSAtIGd1ZXNzZWQgbmFtZVxuICAgICAqIEBwYXJhbSB7W3N0cmluZ119IGFyZ05hbWVzIC0gbGlzdCBvZiBwYXJhbWV0ZXIgbmFtZXNcbiAgICAgKiBAcGFyYW0ge1Njb3BlfSBzYyAtIGZ1bmN0aW9ucyBzY29wZSBjaGFpbiwgb3IgY2xvc3VyZVxuICAgICAqIEBwYXJhbSB7bm9kZX0gb3JpZ2luTm9kZSAtIEFTVCBub2RlIGZvciB0aGUgZnVuY3Rpb25cbiAgICAgKiBAcGFyYW0ge1R5cGV9IGFyZ1Byb3RvIC0gcHJvdG90eXBlIGZvciBhcmd1bWVudHMgb2JqZWN0XG4gICAgICogQHBhcmFtIHtBVmFsfSBib3VuZFRoaXMgLSByZW1lbWJlciB0aGlzQVZhbCBmb3IgYXJyb3cgZnVuY3Rpb25cbiAgICAgKi9cbiAgICBjb25zdHJ1Y3Rvcihmbl9wcm90bywgbmFtZSwgYXJnTmFtZXMsIHNjLCBvcmlnaW5Ob2RlLCBhcmdQcm90bywgYm91bmRUaGlzKSB7XG4gICAgICAgIHN1cGVyKGZuX3Byb3RvLCBuYW1lKTtcbiAgICAgICAgdGhpcy5wYXJhbU5hbWVzID0gYXJnTmFtZXM7XG4gICAgICAgIHRoaXMuc2MgPSBzYztcbiAgICAgICAgdGhpcy5vcmlnaW5Ob2RlID0gb3JpZ2luTm9kZTtcbiAgICAgICAgaWYgKGFyZ1Byb3RvKSB7XG4gICAgICAgICAgICB0aGlzLmFyZ1Byb3RvID0gYXJnUHJvdG87XG4gICAgICAgIH1cbiAgICAgICAgaWYgKGJvdW5kVGhpcykge1xuICAgICAgICAgICAgdGhpcy5ib3VuZFRoaXMgPSBib3VuZFRoaXM7XG4gICAgICAgIH1cbiAgICAgICAgLy8gZnVuRW52IDogQ2FsbENvbnRleHQgLT4gW3NlbGYsIHJldCwgZXhjXVxuICAgICAgICB0aGlzLmZ1bkVudiA9IG5ldyBNYXA7XG4gICAgfVxuXG4gICAgLyoqXG4gICAgICogY29uc3RydWN0IFN0YXR1cyBmb3IgZnVuY3Rpb25cbiAgICAgKiBAcGFyYW0ge0NhbGxDb250ZXh0fSBkZWx0YSAtIGNhbGwgY29udGV4dFxuICAgICAqIEByZXR1cm5zIHtbQVZhbCwgQVZhbCwgQVZhbF19IC0gZm9yIHNlbGYsIHJldHVybiBhbmQgZXhjZXB0aW9uIEFWYWxzXG4gICAgICovXG4gICAgZ2V0RnVuRW52KGRlbHRhKSB7XG4gICAgICAgIGlmICh0aGlzLmZ1bkVudi5oYXMoZGVsdGEpKSB7XG4gICAgICAgICAgICByZXR1cm4gdGhpcy5mdW5FbnYuZ2V0KGRlbHRhKTtcbiAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICAgIHZhciB0cmlwbGUgPSBbbmV3IEFWYWwsIG5ldyBBVmFsLCBuZXcgQVZhbF07XG4gICAgICAgICAgICB0aGlzLmZ1bkVudi5zZXQoZGVsdGEsIHRyaXBsZSk7XG4gICAgICAgICAgICByZXR1cm4gdHJpcGxlO1xuICAgICAgICB9XG4gICAgfVxuXG4gICAgZ2V0QXJndW1lbnRzT2JqZWN0KGRlbHRhKSB7XG4gICAgICAgIHRoaXMuYXJnT2JqTWFwID0gdGhpcy5hcmdPYmpNYXAgfHwgbmV3IE1hcDtcbiAgICAgICAgaWYgKHRoaXMuYXJnT2JqTWFwLmhhcyhkZWx0YSkpIHtcbiAgICAgICAgICAgIHJldHVybiB0aGlzLmFyZ09iak1hcC5nZXQoZGVsdGEpO1xuICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgICAgdmFyIGFyZ09iaiA9IG5ldyBPYmpUeXBlKG5ldyBBVmFsKHRoaXMuYXJnUHJvdG8pLCAnKmFyZ3VtZW50cyBvYmplY3QqJyk7XG4gICAgICAgICAgICB0aGlzLmFyZ09iak1hcC5zZXQoZGVsdGEsIGFyZ09iaik7XG4gICAgICAgICAgICByZXR1cm4gYXJnT2JqO1xuICAgICAgICB9XG4gICAgfVxuXG4gICAgLyoqXG4gICAgICogZ2V0IE9iamVjdCBtYWRlIGJ5IHRoZSBmdW5jdGlvblxuICAgICAqIFRPRE86IHVzZSBhZGRpdGlvbmFsIGluZm9ybWF0aW9uIHRvIGNyZWF0ZSBtdWx0aXBsZSBpbnN0YW5jZXNcbiAgICAgKiBAcmV0dXJucyB7T2JqVHlwZX1cbiAgICAgKi9cbiAgICBnZXRJbnN0YW5jZSgpIHtcbiAgICAgICAgLy8gb2JqSW5zdGFuY2UgaXMgdGhlIG9iamVjdCBtYWRlIGJ5IHRoZSBmdW5jdGlvblxuICAgICAgICBpZiAodGhpcy5vYmpJbnN0YW5jZSkgcmV0dXJuIHRoaXMub2JqSW5zdGFuY2U7XG4gICAgICAgIC8vIHdlIHVuaWZ5IGNvbnN0cnVjdG9yJ3MgLnByb3RvdHlwZSBhbmQgaW5zdGFuY2UncyBfX3Byb3RvX19cbiAgICAgICAgdGhpcy5vYmpJbnN0YW5jZSA9IG5ldyBPYmpUeXBlKHRoaXMuZ2V0UHJvcCgncHJvdG90eXBlJykpO1xuICAgICAgICByZXR1cm4gdGhpcy5vYmpJbnN0YW5jZTtcbiAgICB9XG5cbiAgICBfc3RyaW5naWZ5T25lTGV2ZWxTdHJ1Y3R1cmUoc3RydWN0dXJlKSB7XG5cbiAgICAgICAgY29uc3QgcGFyYW1zID0gc3RydWN0dXJlLnBhcmFtcy5tYXAoZnVuY3Rpb24gKHBhcmFtKSB7XG4gICAgICAgICAgICBpZiAocGFyYW0udHlwZSAhPT0gdW5kZWZpbmVkKVxuICAgICAgICAgICAgICAgIHJldHVybiBwYXJhbS5uYW1lICsgJzonICsgcGFyYW0udHlwZTtcbiAgICAgICAgICAgIGVsc2UgcmV0dXJuIHBhcmFtLm5hbWU7XG4gICAgICAgIH0pO1xuXG4gICAgICAgIGxldCByZXNTdHIgPSAnZm4oJyArIHBhcmFtcy5qb2luKCcsICcpICsgJyknO1xuICAgICAgICBpZiAoc3RydWN0dXJlLnJldCAhPT0gdW5kZWZpbmVkKSB7XG4gICAgICAgICAgICByZXNTdHIgKz0gJyAtPiAnICsgc3RydWN0dXJlLnJldDtcbiAgICAgICAgfVxuICAgICAgICByZXR1cm4gcmVzU3RyO1xuICAgIH1cblxuICAgIF90b1N0cmluZyh2aXNpdGVkVHlwZXMpIHtcbiAgICAgICAgaWYgKHZpc2l0ZWRUeXBlcy5oYXModGhpcykpIHtcbiAgICAgICAgICAgIHJldHVybiAnPyc7XG4gICAgICAgIH1cbiAgICAgICAgY29uc3Qgc3RydWN0dXJlID0gdGhpcy5fZ2V0T25lTGV2ZWxTdHJ1Y3R1cmUodmlzaXRlZFR5cGVzKTtcbiAgICAgICAgcmV0dXJuIHRoaXMuX3N0cmluZ2lmeU9uZUxldmVsU3RydWN0dXJlKHN0cnVjdHVyZSk7XG4gICAgfVxuXG4gICAgX2dldE9uZUxldmVsU3RydWN0dXJlKHZpc2l0ZWRUeXBlcykge1xuICAgICAgICB2aXNpdGVkVHlwZXMuYWRkKHRoaXMpO1xuICAgICAgICBjb25zdCBpbm5lclNjb3BlcyA9IHRoaXMub3JpZ2luTm9kZS5ib2R5WydAYmxvY2snXS5nZXRTY29wZVdpdGhQYXJlbnQodGhpcy5zYyk7XG4gICAgICAgIGNvbnN0IHBhcmFtSW5mbyA9IFtdO1xuICAgICAgICBmb3IgKGxldCBpID0gMDsgaSA8IHRoaXMucGFyYW1OYW1lcy5sZW5ndGg7IGkrKykge1xuICAgICAgICAgICAgY29uc3QgcGFyYW1OYW1lID0gdGhpcy5wYXJhbU5hbWVzW2ldO1xuICAgICAgICAgICAgY29uc3Qgc3RyaW5ncyA9IFtdO1xuICAgICAgICAgICAgbGV0IGhhc1R5cGUgPSBmYWxzZTtcbiAgICAgICAgICAgIGZvciAobGV0IHNjIG9mIGlubmVyU2NvcGVzKSB7XG4gICAgICAgICAgICAgICAgY29uc3QgYXZhbCA9IHNjLmdldEFWYWxPZihwYXJhbU5hbWUpO1xuICAgICAgICAgICAgICAgIGlmICghYXZhbC5pc0VtcHR5KCkpIHtcbiAgICAgICAgICAgICAgICAgICAgc3RyaW5ncy5wdXNoKGF2YWwuX3RvU3RyaW5nKHZpc2l0ZWRUeXBlcykpO1xuICAgICAgICAgICAgICAgICAgICBoYXNUeXBlID0gdHJ1ZTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBjb25zdCB0eXBlU3RyaW5nID0gaGFzVHlwZSA/IHN0cmluZ3Muam9pbignfCcpIDogdW5kZWZpbmVkO1xuICAgICAgICAgICAgcGFyYW1JbmZvLnB1c2goe25hbWU6IHBhcmFtTmFtZSwgdHlwZTogdHlwZVN0cmluZ30pO1xuICAgICAgICB9XG4gICAgICAgIC8vIGNvbXB1dGluZyBqb2luZWQgcmV0QVZhbFxuICAgICAgICBjb25zdCByZXRUeXBlU3RyaW5ncyA9IFtdO1xuICAgICAgICBsZXQgbm9SZXRUeXBlcyA9IHRydWU7XG4gICAgICAgIGZvciAobGV0IFssIHJldEFWYWwsIF0gb2YgdGhpcy5mdW5FbnYudmFsdWVzKCkpIHtcbiAgICAgICAgICAgIGlmICghcmV0QVZhbC5pc0VtcHR5KCkpIHtcbiAgICAgICAgICAgICAgICBub1JldFR5cGVzID0gZmFsc2U7XG4gICAgICAgICAgICAgICAgcmV0VHlwZVN0cmluZ3MucHVzaChyZXRBVmFsLl90b1N0cmluZyh2aXNpdGVkVHlwZXMpKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgfVxuICAgICAgICB2aXNpdGVkVHlwZXMuZGVsZXRlKHRoaXMpO1xuICAgICAgICByZXR1cm4ge3BhcmFtczogcGFyYW1JbmZvLCByZXQ6IChub1JldFR5cGVzID8gdW5kZWZpbmVkIDogcmV0VHlwZVN0cmluZ3Muam9pbignfCcpKX07XG5cbiAgICB9XG5cbiAgICBnZXRPbmVMZXZlbFN0cnVjdHVyZSgpIHtcbiAgICAgICAgY29uc3QgdmlzaXRlZFR5cGVzID0gbmV3IFNldCgpO1xuICAgICAgICByZXR1cm4gdGhpcy5fZ2V0T25lTGV2ZWxTdHJ1Y3R1cmUodmlzaXRlZFR5cGVzKTtcbiAgICB9XG59XG5cbi8qKiBcbiAqIDQuIGFycmF5IHR5cGVzXG4gKiBAY29uc3RydWN0b3JcbiAqL1xuZXhwb3J0IGNsYXNzIEFyclR5cGUgZXh0ZW5kcyBPYmpUeXBlIHtcbiAgICBjb25zdHJ1Y3RvcihhcnJfcHJvdG8pIHtcbiAgICAgICAgc3VwZXIoYXJyX3Byb3RvLCAnQXJyYXknKTtcbiAgICB9XG5cbiAgICBfdG9TdHJpbmcodmlzaXRlZFR5cGVzKSB7XG4gICAgICAgIGlmICh2aXNpdGVkVHlwZXMuaGFzKHRoaXMpKSB7XG4gICAgICAgICAgICByZXR1cm4gJz8nO1xuICAgICAgICB9XG4gICAgICAgIHZpc2l0ZWRUeXBlcy5hZGQodGhpcyk7XG4gICAgICAgIC8vIHByb3AgbnVsbCBpcyB1c2VkIGZvciBhcnJheSBlbGVtZW50c1xuICAgICAgICBjb25zdCBlbHRUeXBlcyA9IHRoaXMuZ2V0UHJvcChudWxsLCB0cnVlKTtcbiAgICAgICAgY29uc3QgdHBTdHIgPSAnWycgKyBlbHRUeXBlcy5fdG9TdHJpbmcodmlzaXRlZFR5cGVzKSArICddJztcbiAgICAgICAgdmlzaXRlZFR5cGVzLmRlbGV0ZSh0aGlzKTtcbiAgICAgICAgcmV0dXJuIHRwU3RyO1xuICAgIH1cbn1cblxuLy8gTWFrZSBwcmltaXRpdmUgdHlwZXNcbmV4cG9ydCBjb25zdCBQcmltTnVtYmVyID0gbmV3IFByaW1UeXBlKCdudW1iZXInKTtcbmV4cG9ydCBjb25zdCBQcmltU3RyaW5nID0gbmV3IFByaW1UeXBlKCdzdHJpbmcnKTtcbmV4cG9ydCBjb25zdCBQcmltQm9vbGVhbiA9IG5ldyBQcmltVHlwZSgnYm9vbGVhbicpO1xuXG4vLyBBYnNOdWxsIHJlcHJlc2VudHMgYWxsIGVtcHR5IGFic3RyYWN0IHZhbHVlcy5cbmV4cG9ydCBjb25zdCBBVmFsTnVsbCA9IG5ldyBBVmFsKCk7XG4vLyBZb3Ugc2hvdWxkIG5vdCBhZGQgYW55IHByb3BlcnRpZXMgdG8gaXQuXG5BVmFsTnVsbC5wcm9wcyA9IG51bGw7XG4vLyBBZGRpbmcgdHlwZXMgYXJlIGlnbm9yZWQuXG5BVmFsTnVsbC5hZGRUeXBlID0gZnVuY3Rpb24gKCkge307XG5cbmV4cG9ydCBjbGFzcyBBYnNDYWNoZSB7XG4gICAgY29uc3RydWN0b3IoKSB7XG4gICAgICAgIHRoaXMubWFwID0gbmV3IE1hcCgpO1xuICAgIH1cblxuICAgIC8qKlxuICAgICAqIEdldCBpZiBvbmUgZXhpc3RzLCBpZiBub3QgY3JlYXRlIG9uZVxuICAgICAqIEBwYXJhbSBsb2NcbiAgICAgKiBAcGFyYW0gY3R4XG4gICAgICogQHJldHVybnMgeyp9XG4gICAgICovXG4gICAgZ2V0KGxvYywgY3R4KSB7XG4gICAgICAgIGlmICghdGhpcy5tYXAuaGFzKGxvYykpIHtcbiAgICAgICAgICAgIC8vIGNyZWF0ZSBpbm5lciBtYXBcbiAgICAgICAgICAgIHRoaXMubWFwLnNldChsb2MsIG5ldyBNYXAoKSk7XG4gICAgICAgIH1cbiAgICAgICAgY29uc3QgbWFwTG9jID0gdGhpcy5tYXAuZ2V0KGxvYyk7XG4gICAgICAgIGlmICghbWFwTG9jLmhhcyhjdHgpKSB7XG4gICAgICAgICAgICBjb25zdCBhdiA9IG5ldyBBVmFsKCk7XG4gICAgICAgICAgICBtYXBMb2Muc2V0KGN0eCwgYXYpO1xuICAgICAgICAgICAgcmV0dXJuIGF2O1xuICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgICAgcmV0dXJuIG1hcExvYy5nZXQoY3R4KTtcbiAgICAgICAgfVxuICAgIH1cblxuICAgIC8qKlxuICAgICAqIFRvIHVzZSBhdiBtYWRlIGJ5IG90aGVycyAoZS5nLiBzY29wZSlcbiAgICAgKiBAcGFyYW0gbG9jXG4gICAgICogQHBhcmFtIGN0eFxuICAgICAqIEBwYXJhbSBhdlxuICAgICAqL1xuICAgIHNldChsb2MsIGN0eCwgYXYpIHtcbiAgICAgICAgaWYgKCF0aGlzLm1hcC5oYXMobG9jKSkge1xuICAgICAgICAgICAgLy8gY3JlYXRlIGlubmVyIG1hcFxuICAgICAgICAgICAgdGhpcy5tYXAuc2V0KGxvYywgbmV3IE1hcCgpKTtcbiAgICAgICAgfVxuICAgICAgICB0aGlzLm1hcC5nZXQobG9jKS5zZXQoY3R4LCBhdik7XG4gICAgfVxuXG4gICAgLyoqXG4gICAgICogQ2hlY2sgd2hldGhlciBpdCBoYXMgb25lIGZvciBsb2MgYW5kIGN0eFxuICAgICAqIEBwYXJhbSBsb2NcbiAgICAgKiBAcGFyYW0gY3R4XG4gICAgICogQHJldHVybnMge2Jvb2xlYW59XG4gICAgICovXG4gICAgaGFzKGxvYywgY3R4KSB7XG4gICAgICAgIHJldHVybiB0aGlzLm1hcC5oYXMobG9jKSAmJiB0aGlzLm1hcC5nZXQobG9jKS5oYXMoY3R4KTtcbiAgICB9XG5cbiAgICAvKipcbiAgICAgKiBNZXJnZSBhbGwgQVZhbCBvZiB0aGUgbG9jXG4gICAgICogQHBhcmFtIGxvY1xuICAgICAqIEByZXR1cm5zIHtBVmFsfVxuICAgICAqL1xuICAgIGdldE1lcmdlZEFWYWxPZkxvYyhsb2MpIHtcbiAgICAgICAgaWYgKCF0aGlzLm1hcC5oYXMobG9jKSkge1xuICAgICAgICAgICAgLy8gbm8gdHlwZSBpcyBhdmFpbGFibGVcbiAgICAgICAgICAgIHJldHVybiBudWxsO1xuICAgICAgICB9XG4gICAgICAgIGNvbnN0IG1lcmdlZEFWYWwgPSBuZXcgQVZhbCgpO1xuICAgICAgICBpZiAodGhpcy5tYXAuaGFzKGxvYykpIHtcbiAgICAgICAgICAgIGZvciAobGV0IGF2IG9mIHRoaXMubWFwLmdldChsb2MpLnZhbHVlcygpKSB7XG4gICAgICAgICAgICAgICAgZm9yIChsZXQgdHAgb2YgYXYuZ2V0VHlwZXMoKSkge1xuICAgICAgICAgICAgICAgICAgICBtZXJnZWRBVmFsLmFkZFR5cGUodHApO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgIH1cbiAgICAgICAgfVxuICAgICAgICByZXR1cm4gbWVyZ2VkQVZhbDtcbiAgICB9XG5cbn1cbiIsImltcG9ydCAqIGFzIG15V2Fsa2VyIGZyb20gJy4vdXRpbC9teVdhbGtlcidcbmltcG9ydCAqIGFzIHR5cGVzIGZyb20gJy4vZG9tYWlucy90eXBlcydcblxuLyoqXG4gKiBHZXQgdHlwZXMgb2YgZXhwcmVzc2lvbiBhdCB0aGUgZ2l2ZW4gcmFuZ2VcbiAqIEBwYXJhbSBhc3RcbiAqIEBwYXJhbSDEiFxuICogQHBhcmFtIHN0YXJ0XG4gKiBAcGFyYW0gZW5kXG4gKiBAcmV0dXJucyB7e2hhc1R5cGU6IGJvb2xlYW4sIHR5cGVTdHJpbmc6IHN0cmluZywgbm9kZVN0YXJ0OiBudW1iZXIsIG5vZGVFbmQ6IG51bWJlcn19XG4gKi9cbmV4cG9ydCBmdW5jdGlvbiBnZXRUeXBlQXRSYW5nZShhc3QsIMSILCBzdGFydCwgZW5kKSB7XG4gICAgJ3VzZSBzdHJpY3QnO1xuICAgIGNvbnN0IG5vZGUgPSBteVdhbGtlci5maW5kU3Vycm91bmRpbmdOb2RlKGFzdCwgc3RhcnQsIGVuZCk7XG4gICAgY29uc3Qgbm9kZVR5cGVzID0gxIguZ2V0TWVyZ2VkQVZhbE9mTG9jKG5vZGUpO1xuICAgIGxldCBoYXNUeXBlO1xuICAgIGxldCB0eXBlU3RyaW5nID0gJyc7XG4gICAgaWYgKCFub2RlVHlwZXMpIHtcbiAgICAgICAgaGFzVHlwZSA9IGZhbHNlO1xuICAgICAgICB0eXBlU3RyaW5nID0gJ05vIHR5cGVzIGF0IHRoZSBnaXZlbiByYW5nZSc7XG4gICAgfSBlbHNlIHtcbiAgICAgICAgaGFzVHlwZSA9IHRydWU7XG4gICAgICAgIHR5cGVTdHJpbmcgPSBub2RlVHlwZXMudG9TdHJpbmcoKTtcbiAgICB9XG4gICAgcmV0dXJuIHtcbiAgICAgICAgaGFzVHlwZTogaGFzVHlwZSxcbiAgICAgICAgdHlwZVN0cmluZzogdHlwZVN0cmluZyxcbiAgICAgICAgbm9kZVN0YXJ0OiBub2RlLnN0YXJ0LFxuICAgICAgICBub2RlRW5kOiBub2RlLmVuZFxuICAgIH07XG59XG5cbmV4cG9ydCBmdW5jdGlvbiBnZXRGblR5cGVTdHJ1Y3R1cmVzQXQoYXN0LCDEiCwgcG9zKSB7XG4gICAgY29uc3Qgbm9kZSA9IG15V2Fsa2VyLmZpbmRTdXJyb3VuZGluZ05vZGUoYXN0LCBwb3MsIHBvcyk7XG4gICAgY29uc3Qgbm9kZVR5cGVzID0gxIguZ2V0TWVyZ2VkQVZhbE9mTG9jKG5vZGUpO1xuICAgIGNvbnN0IGZuVHlwZVN0cnVjdHVyZXMgPSBbXTtcblxuICAgIG5vZGVUeXBlcy5nZXRUeXBlcygpLmZvckVhY2goZnVuY3Rpb24gKGZuKSB7XG4gICAgICAgIGlmIChmbiBpbnN0YW5jZW9mIHR5cGVzLkZuVHlwZSkge1xuICAgICAgICAgICAgZm5UeXBlU3RydWN0dXJlcy5wdXNoKGZuLmdldE9uZUxldmVsU3RydWN0dXJlKCkpO1xuICAgICAgICB9XG4gICAgfSk7XG4gICAgcmV0dXJuIGZuVHlwZVN0cnVjdHVyZXM7XG59XG5cbmZ1bmN0aW9uIGNvbXB1dGVJY29uT2ZQcm9wKHByb3BNYXApIHtcbiAgICBjb25zdCBpY29uTWFwID0gbmV3IE1hcCgpO1xuXG4gICAgZnVuY3Rpb24gaXNPYmplY3QoaWNvbikge1xuICAgICAgICByZXR1cm4gaWNvbiA9PT0gJ29iamVjdCcgfHwgaWNvbiA9PT0gJ2FycmF5JyB8fCBpY29uID09PSAnZm4nO1xuICAgIH1cblxuICAgIHByb3BNYXAuZm9yRWFjaCgodHBzLCBwKSA9PiB7XG4gICAgICAgIGZvciAobGV0IHRwIG9mIHRwcykge1xuICAgICAgICAgICAgbGV0IGljb247XG4gICAgICAgICAgICBpZiAodHAgPT09IHR5cGVzLlByaW1OdW1iZXIpIGljb24gPSAnbnVtYmVyJztcbiAgICAgICAgICAgIGVsc2UgaWYgKHRwID09PSB0eXBlcy5QcmltQm9vbGVhbikgaWNvbiA9ICdib29sJztcbiAgICAgICAgICAgIGVsc2UgaWYgKHRwID09PSB0eXBlcy5QcmltU3RyaW5nKSBpY29uID0gJ3N0cmluZyc7XG4gICAgICAgICAgICBlbHNlIGlmICh0cCBpbnN0YW5jZW9mIHR5cGVzLkZuVHlwZSkgaWNvbiA9ICdmbic7XG4gICAgICAgICAgICBlbHNlIGlmICh0cCBpbnN0YW5jZW9mIHR5cGVzLkFyclR5cGUpIGljb24gPSAnYXJyYXknO1xuICAgICAgICAgICAgZWxzZSBpZiAodHAgaW5zdGFuY2VvZiB0eXBlcy5PYmpUeXBlKSBpY29uID0gJ29iamVjdCc7XG5cbiAgICAgICAgICAgIGlmICghaWNvbk1hcC5oYXMocCkgfHwgaWNvbk1hcC5nZXQocCkgPT09IGljb24pIHtcbiAgICAgICAgICAgICAgICBpY29uTWFwLnNldChwLCBpY29uKTtcbiAgICAgICAgICAgICAgICBjb250aW51ZTtcbiAgICAgICAgICAgIH1cblxuICAgICAgICAgICAgaWYgKGlzT2JqZWN0KGljb24pICYmIGlzT2JqZWN0KGljb25NYXAuZ2V0KHApKSkge1xuICAgICAgICAgICAgICAgIGljb25NYXAuc2V0KHAsICdvYmplY3QnKTtcbiAgICAgICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgICAgICAgaWNvbk1hcC5zZXQocCwgJ3Vua25vd24nKTtcbiAgICAgICAgICAgICAgICBicmVhaztcbiAgICAgICAgICAgIH1cbiAgICAgICAgfVxuICAgICAgICBpZiAodHBzLnNpemUgPT09IDApIHtcbiAgICAgICAgICAgIGljb25NYXAuc2V0KHAsICd1bmtub3duJyk7XG4gICAgICAgIH1cbiAgICB9KTtcbiAgICByZXR1cm4gaWNvbk1hcDtcbn1cblxuLyoqXG4gKiBHZXQgcHJvcCB0byBpY29uIG1hcCBmcm9tIGdpdmVuIG5vZGVcbiAqIEBwYXJhbSDEiCAtIEFic0NhY2hlXG4gKiBAcGFyYW0gbm9kZSAtIGV4cHJlc3Npb24gbm9kZVxuICogQHJldHVybnMge01hcC48c3RyaW5nLCBzdHJpbmc+fSAtIE1hcHBpbmcgZnJvbSBwcm9wIHRvIGljb25cbiAqL1xuZXhwb3J0IGZ1bmN0aW9uIGdldFByb3BGcm9tTm9kZSjEiCwgbm9kZSkge1xuICAgIC8vIFNpbmNlIGdldFR5cGVPZkxvYyBjYW4gcmV0dXJuIG51bGwgaWYgbm9kZSBkb2VzIG5vdCBoYXZlIGFueSB0eXBlc1xuICAgIGNvbnN0IG5vZGVUeXBlcyA9IMSILmdldE1lcmdlZEFWYWxPZkxvYyhub2RlKTtcbiAgICBjb25zdCBwcm9wTWFwID0gZ2V0UmVhZGFibGVQcm9wTWFwKG5vZGVUeXBlcyk7XG4gICAgcmV0dXJuIGNvbXB1dGVJY29uT2ZQcm9wKHByb3BNYXApO1xufVxuXG4vKipcbiAqIEZvciBkZWJ1Z2dpbmcsIHNob3cgeFxuICogQHBhcmFtIHhcbiAqL1xuZnVuY3Rpb24gU0hPVyh4KSB7XG4gICAgY29uc29sZS5pbmZvKHgpO1xuICAgIHJldHVybiB4O1xufVxuXG5leHBvcnQgZnVuY3Rpb24gZ2V0Q29tcGxldGlvbkF0UG9zKHJlc3VsdCwgcG9zKSB7XG4gICAgLy8gZmluZCBpZCBvciBtZW1iZXIgbm9kZVxuICAgIGNvbnN0IG5vZGVJbmZvID0gbXlXYWxrZXIuZmluZENvbXBsZXRpb25Db250ZXh0KHJlc3VsdC5BU1QsIHBvcyk7XG5cbiAgICBpZiAobm9kZUluZm8udHlwZSA9PT0gJ0lkZW50aWZpZXInKSB7XG4gICAgICAgIGxldCBwcmVmaXgsIGZyb20sIHRvO1xuXG4gICAgICAgIGlmIChub2RlSW5mby5ub2RlID09PSBudWxsKSB7XG4gICAgICAgICAgICBwcmVmaXggPSAnJztcbiAgICAgICAgICAgIGZyb20gPSBwb3M7XG4gICAgICAgICAgICB0byA9IHBvcztcbiAgICAgICAgfSBlbHNlIGlmIChteVdhbGtlci5pc0R1bW15SWROb2RlKG5vZGVJbmZvLm5vZGUpKSB7XG4gICAgICAgICAgICBwcmVmaXggPSAnJztcbiAgICAgICAgICAgIGZyb20gPSB0byA9IG5vZGVJbmZvLm5vZGUuZW5kOyAvLyBIZXJlLCBlbmQgaXMgY29ycmVjdCBmb3Igc3RhcnQgcG9zaXRpb25cbiAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICAgIHByZWZpeCA9IG5vZGVJbmZvLm5vZGUubmFtZTtcbiAgICAgICAgICAgIGZyb20gPSBub2RlSW5mby5ub2RlLnN0YXJ0O1xuICAgICAgICAgICAgdG8gPSBub2RlSW5mby5ub2RlLmVuZDtcbiAgICAgICAgfVxuICAgICAgICBjb25zdCB2YXJNYXAgPSBjb21wdXRlSWNvbk9mUHJvcChnZXRSZWFkYWJsZVZhck1hcChub2RlSW5mby52YikpO1xuXG4gICAgICAgIGNvbnN0IGxpc3QgPSBbXTtcbiAgICAgICAgZm9yIChsZXQgW3YsIGldIG9mIHZhck1hcCkge1xuICAgICAgICAgICAgaWYgKHYuc3RhcnRzV2l0aChwcmVmaXgpKSB7XG4gICAgICAgICAgICAgICAgbGlzdC5wdXNoKHt0ZXh0OiB2LCBpY29uOiBpfSk7XG4gICAgICAgICAgICB9XG4gICAgICAgIH1cbiAgICAgICAgcmV0dXJuIFNIT1coe2xpc3Q6IGxpc3QsIGZyb206IGZyb20sIHRvOiB0b30pO1xuXG4gICAgfSBlbHNlIHtcbiAgICAgICAgLy8gcHJvcGVydHkgY29tcGxldGlvblxuICAgICAgICBjb25zdCBvYmplY3ROb2RlID0gbm9kZUluZm8ubm9kZS5vYmplY3Q7XG4gICAgICAgIGNvbnN0IHByb3BzID0gZ2V0UHJvcEZyb21Ob2RlKHJlc3VsdC7EiCwgb2JqZWN0Tm9kZSk7XG5cbiAgICAgICAgY29uc3QgcHJvcGVydHlOb2RlID0gbm9kZUluZm8ubm9kZS5wcm9wZXJ0eTtcbiAgICAgICAgbGV0IHByZWZpeCwgZnJvbSwgdG8sIGZpbHRlcjtcbiAgICAgICAgaWYgKG5vZGVJbmZvLnR5cGUgPT09ICd1c3VhbFByb3AnKSB7XG4gICAgICAgICAgICBjb25zdCBwcm9wTmFtZSA9IHByb3BlcnR5Tm9kZS5uYW1lO1xuICAgICAgICAgICAgaWYgKG15V2Fsa2VyLmlzRHVtbXlJZE5vZGUocHJvcGVydHlOb2RlKSkge1xuICAgICAgICAgICAgICAgIHByZWZpeCA9ICcnO1xuICAgICAgICAgICAgICAgIGZyb20gPSBwcm9wZXJ0eU5vZGUuZW5kOyAvLyBIZXJlLCBlbmQgaXMgY29ycmVjdCBmb3Igc3RhcnQgcG9zaXRpb25cbiAgICAgICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgICAgICAgLy8gcHJlZml4ID0gcHJvcE5hbWUuc3Vic3RyKDAsIHBvcyAtIHByb3BlcnR5Tm9kZS5zdGFydCk7XG4gICAgICAgICAgICAgICAgcHJlZml4ID0gcHJvcE5hbWU7XG4gICAgICAgICAgICAgICAgZnJvbSA9IHByb3BlcnR5Tm9kZS5zdGFydDtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIHRvID0gcHJvcGVydHlOb2RlLmVuZDtcbiAgICAgICAgICAgIGZpbHRlciA9IHAgPT4gKC9eWyRBLVpfXVswLTlBLVpfJF0qJC9pKS50ZXN0KHApO1xuICAgICAgICB9IGVsc2UgaWYgKG5vZGVJbmZvLnR5cGUgPT09ICdzdHJpbmdQcm9wJykge1xuICAgICAgICAgICAgcHJlZml4ID0gcHJvcGVydHlOb2RlLnZhbHVlO1xuICAgICAgICAgICAgZnJvbSA9IHByb3BlcnR5Tm9kZS5zdGFydCArIDE7XG4gICAgICAgICAgICB0byA9IHByb3BlcnR5Tm9kZS5lbmQgLSAxO1xuICAgICAgICAgICAgZmlsdGVyID0gcCA9PiB0cnVlXG4gICAgICAgIH1cblxuICAgICAgICBjb25zdCBsaXN0ID0gW107XG4gICAgICAgIGZvciAobGV0IFtwLCBpXSBvZiBwcm9wcykge1xuICAgICAgICAgICAgLy8gdW5rbm93biBwcm9wIGlzIG51bGxcbiAgICAgICAgICAgIGlmIChwICE9PSBudWxsICYmIHAuc3RhcnRzV2l0aChwcmVmaXgpICYmIGZpbHRlcihwKSkge1xuICAgICAgICAgICAgICAgIGxpc3QucHVzaCh7dGV4dDogcCwgaWNvbjogaX0pO1xuICAgICAgICAgICAgfVxuICAgICAgICB9XG4gICAgICAgIHJldHVybiBTSE9XKHtsaXN0OiBsaXN0LCBmcm9tOiBmcm9tLCB0bzogdG99KTtcbiAgICB9XG59XG5cblxuZnVuY3Rpb24gdW5pb25NYXAobTEsIG0yKSB7XG4gICAgY29uc3QgcmV0ID0gbmV3IE1hcCgpO1xuXG4gICAgZnVuY3Rpb24gdW5pb25TZXQoczEsIHMyKSB7XG4gICAgICAgIGNvbnN0IHJldCA9IG5ldyBTZXQoKTtcbiAgICAgICAgaWYgKHMxKSBzMS5mb3JFYWNoKGUgPT4gcmV0LmFkZChlKSk7XG4gICAgICAgIGlmIChzMikgczIuZm9yRWFjaChlID0+IHJldC5hZGQoZSkpO1xuICAgICAgICByZXR1cm4gcmV0O1xuICAgIH1cblxuICAgIGlmIChtMSkgbTEuZm9yRWFjaCgodHMsIHApID0+IHJldC5zZXQocCwgdHMpKTtcbiAgICBpZiAobTIpIG0yLmZvckVhY2goKHRzLCBwKSA9PiByZXQuc2V0KHAsIHVuaW9uU2V0KHJldC5nZXQocCksIG0yLmdldChwKSkpKTtcbiAgICByZXR1cm4gcmV0O1xufVxuXG5mdW5jdGlvbiBhZGRPbmx5TWlzc2luZ01hcHBpbmdzKG0xLCBtMikge1xuICAgIGNvbnN0IHJldCA9IG5ldyBNYXAoKTtcbiAgICBtMS5mb3JFYWNoKCh0cywgcCkgPT4gcmV0LnNldChwLCB0cykpO1xuICAgIG0yLmZvckVhY2goKHRzLCBwKSA9PiB7XG4gICAgICAgIGlmICghcmV0LmhhcyhwKSkgcmV0LnNldChwLCB0cylcbiAgICB9KTtcbiAgICByZXR1cm4gcmV0O1xufVxuXG4vLyBjb252ZXJ0IGEgbWFwIG9mIEEgLT4gQVZhbFxuLy8gdG8gYSBtYXAgb2YgQSAtPiBTZXQuPFR5cGU+XG5mdW5jdGlvbiBjb252ZXJ0TWFwKG1hcCkge1xuICAgIGxldCByZXRNYXAgPSBuZXcgTWFwKCk7XG4gICAgbWFwLmZvckVhY2goKGF2LCBwKSA9PiB7XG4gICAgICAgIHJldE1hcC5zZXQocCwgYXYuZ2V0VHlwZXMoKSk7XG4gICAgfSk7XG4gICAgcmV0dXJuIHJldE1hcDtcbn1cblxuLy8gdHJhdmVyc2UgYWJzdHJhY3QgaGVhcCBzcGFjZVxuZnVuY3Rpb24gZ2V0UmVhZGFibGVQcm9wTWFwKHRwcykge1xuXG4gICAgY29uc3QgdmlzaXRlZFR5cGVzID0gW107XG5cbiAgICBmdW5jdGlvbiB0cmF2ZXJzZSh0eXBlKSB7XG4gICAgICAgIGlmICh0eXBlIGluc3RhbmNlb2YgdHlwZXMuT2JqVHlwZSAmJlxuICAgICAgICAgICAgdHlwZS5nZXRQcm9wKCdfX3Byb3RvX18nLCB0cnVlKSkge1xuICAgICAgICAgICAgbGV0IHByb3RvTWFwID0gbmV3IE1hcCgpO1xuICAgICAgICAgICAgY29uc3QgcHJvdG9UeXBlcyA9IHR5cGUuZ2V0UHJvcCgnX19wcm90b19fJywgdHJ1ZSkuZ2V0VHlwZXMoKTtcblxuICAgICAgICAgICAgcHJvdG9UeXBlcy5mb3JFYWNoKHRwID0+IHtcbiAgICAgICAgICAgICAgICBpZiAodmlzaXRlZFR5cGVzLmluZGV4T2YodHApID4gLTEpIHtcbiAgICAgICAgICAgICAgICAgICAgcmV0dXJuO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICB2aXNpdGVkVHlwZXMucHVzaCh0cCk7XG4gICAgICAgICAgICAgICAgcHJvdG9NYXAgPSB1bmlvbk1hcChwcm90b01hcCwgdHJhdmVyc2UodHApKTtcbiAgICAgICAgICAgICAgICB2aXNpdGVkVHlwZXMucG9wKCk7XG4gICAgICAgICAgICB9KTtcbiAgICAgICAgICAgIHJldHVybiBhZGRPbmx5TWlzc2luZ01hcHBpbmdzKGNvbnZlcnRNYXAodHlwZS5wcm9wcyksIHByb3RvTWFwKTtcbiAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICAgIHJldHVybiBuZXcgTWFwKCk7XG4gICAgICAgIH1cbiAgICB9XG5cbiAgICBsZXQgcmV0TWFwID0gbmV3IE1hcCgpO1xuICAgIHRwcy5nZXRUeXBlcygpLmZvckVhY2godHAgPT4ge1xuICAgICAgICByZXRNYXAgPSB1bmlvbk1hcChyZXRNYXAsIHRyYXZlcnNlKHRwKSlcbiAgICB9KTtcblxuICAgIHJldHVybiByZXRNYXA7XG59XG5cbmV4cG9ydCBmdW5jdGlvbiBnZXREZWZpbml0aW9uU2l0ZXNBdChhc3QsIMSILCBwb3MpIHtcbiAgICBjb25zdCBub2RlID0gbXlXYWxrZXIuZmluZFN1cnJvdW5kaW5nTm9kZShhc3QsIHBvcywgcG9zKTtcbiAgICBjb25zdCBub2RlVHlwZXMgPSDEiC5nZXRNZXJnZWRBVmFsT2ZMb2Mobm9kZSk7XG5cbiAgICBjb25zdCByYW5nZXMgPSBbXTtcbiAgICBpZiAobm9kZVR5cGVzID09PSBudWxsKSB7XG4gICAgICAgIHJldHVybiByYW5nZXM7XG4gICAgfVxuICAgIG5vZGVUeXBlcy5nZXRUeXBlcygpLmZvckVhY2goZnVuY3Rpb24gKHRwKSB7XG4gICAgICAgIGlmICh0cCBpbnN0YW5jZW9mIHR5cGVzLkZuVHlwZSAmJiB0cC5vcmlnaW5Ob2RlKSB7XG4gICAgICAgICAgICBjb25zdCBmbk5vZGUgPSB0cC5vcmlnaW5Ob2RlO1xuICAgICAgICAgICAgbGV0IGF0O1xuICAgICAgICAgICAgc3dpdGNoIChmbk5vZGUudHlwZSkge1xuICAgICAgICAgICAgICAgIGNhc2UgJ0Z1bmN0aW9uRXhwcmVzc2lvbicgOiBhdCA9IGZuTm9kZS5zdGFydDsgYnJlYWs7XG4gICAgICAgICAgICAgICAgY2FzZSAnRnVuY3Rpb25EZWNsYXJhdGlvbicgOiBhdCA9IGZuTm9kZS5pZC5zdGFydDsgYnJlYWs7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBjb25zdCBpdGVtID0ge3N0YXJ0OiBmbk5vZGUuc3RhcnQsIGVuZDogZm5Ob2RlLmVuZCwgYXQ6IGF0fTtcbiAgICAgICAgICAgIHJhbmdlcy5wdXNoKGl0ZW0pO1xuICAgICAgICB9XG4gICAgfSk7XG4gICAgcmV0dXJuIHJhbmdlcztcbn1cblxuLy8gdHJhdmVyc2UgYWJzdHJhY3Qgc3RhY2sgc3BhY2VcbmZ1bmN0aW9uIGdldFJlYWRhYmxlVmFyTWFwKHZiKSB7XG4gICAgbGV0IGN1cnJWQiA9IHZiO1xuICAgIGxldCByZXRNYXAgPSBuZXcgTWFwKCk7XG4gICAgd2hpbGUgKGN1cnJWQiAhPT0gbnVsbCkge1xuICAgICAgICBsZXQgbWVyZ2VkTWFwID0gbmV3IE1hcCgpO1xuICAgICAgICBmb3IgKGxldCB2YXJNYXAgb2YgY3VyclZCLmluc3RhbmNlcy52YWx1ZXMoKSkge1xuICAgICAgICAgICAgbWVyZ2VkTWFwID0gdW5pb25NYXAobWVyZ2VkTWFwLCBjb252ZXJ0TWFwKHZhck1hcCkpO1xuICAgICAgICB9XG4gICAgICAgIHJldE1hcCA9IGFkZE9ubHlNaXNzaW5nTWFwcGluZ3MocmV0TWFwLCBtZXJnZWRNYXApO1xuICAgICAgICBjdXJyVkIgPSBjdXJyVkIucGFyZW47XG4gICAgfVxuICAgIHJldHVybiByZXRNYXA7XG59XG4iLCJ2YXIgdXRpbCA9IHJlcXVpcmUoJ3V0aWwnKTtcblxuZnVuY3Rpb24gZ2V0Tm9kZUxpc3QoYXN0LCBzdGFydE51bSkge1xuICAgIHZhciBub2RlTGlzdCA9IFtdO1xuXG4gICAgdmFyIG51bSA9IHN0YXJ0TnVtID09PSB1bmRlZmluZWQgPyAwIDogc3RhcnROdW07XG5cbiAgICBmdW5jdGlvbiBhc3NpZ25JZChub2RlKSB7XG4gICAgICAgIG5vZGVbJ0BsYWJlbCddID0gbnVtO1xuICAgICAgICBub2RlTGlzdC5wdXNoKG5vZGUpO1xuICAgICAgICBudW0rKztcbiAgICB9XG5cbiAgICAvLyBMYWJlbCBldmVyeSBBU1Qgbm9kZSB3aXRoIHByb3BlcnR5ICd0eXBlJ1xuICAgIGZ1bmN0aW9uIGxhYmVsTm9kZVdpdGhUeXBlKG5vZGUpIHtcbiAgICAgICAgaWYgKG5vZGUgJiYgbm9kZS5oYXNPd25Qcm9wZXJ0eSgndHlwZScpKSB7XG4gICAgICAgICAgICBhc3NpZ25JZChub2RlKTtcbiAgICAgICAgfVxuICAgICAgICBpZiAobm9kZSAmJiB0eXBlb2Ygbm9kZSA9PT0gJ29iamVjdCcpIHtcbiAgICAgICAgICAgIGZvciAodmFyIHAgaW4gbm9kZSkge1xuICAgICAgICAgICAgICAgIGxhYmVsTm9kZVdpdGhUeXBlKG5vZGVbcF0pO1xuICAgICAgICAgICAgfVxuICAgICAgICB9XG4gICAgfVxuXG4gICAgbGFiZWxOb2RlV2l0aFR5cGUoYXN0KTtcblxuICAgIHJldHVybiBub2RlTGlzdDtcbn1cblxuZnVuY3Rpb24gc2hvd1VuZm9sZGVkKG9iaikge1xuICAgIGNvbnNvbGUubG9nKHV0aWwuaW5zcGVjdChvYmosIHtkZXB0aDogbnVsbH0pKTtcbn1cblxuZXhwb3J0cy5nZXROb2RlTGlzdCA9IGdldE5vZGVMaXN0O1xuZXhwb3J0cy5zaG93VW5mb2xkZWQgPSBzaG93VW5mb2xkZWQ7XG4iLCIvLyBpbXBvcnQgbmVjZXNzYXJ5IGxpYnJhcmllc1xuY29uc3QgYWNvcm4gPSByZXF1aXJlKCdhY29ybi9kaXN0L2Fjb3JuJyk7XG5jb25zdCBhY29ybl9sb29zZSA9IHJlcXVpcmUoJ2Fjb3JuL2Rpc3QvYWNvcm5fbG9vc2UnKTtcbmNvbnN0IGF1eCA9IHJlcXVpcmUoJy4vaGVscGVyJyk7XG5pbXBvcnQgKiBhcyB0eXBlcyBmcm9tICcuL2RvbWFpbnMvdHlwZXMnXG5pbXBvcnQgKiBhcyBjb250ZXh0IGZyb20gJy4vZG9tYWlucy9jb250ZXh0J1xuLy8gY29uc3Qgc3RhdHVzID0gcmVxdWlyZSgnLi9kb21haW5zL3N0YXR1cycpO1xuaW1wb3J0ICogYXMgc3RhdHVzIGZyb20gJy4vZG9tYWlucy9zdGF0dXMnXG5pbXBvcnQgKiBhcyB2YXJCbG9jayBmcm9tICcuL3ZhckJsb2NrJ1xuY29uc3QgY0dlbiA9IHJlcXVpcmUoJy4vY29uc3RyYWludC9jR2VuJyk7XG5jb25zdCB2YXJSZWZzID0gcmVxdWlyZSgnLi92YXJyZWZzJyk7XG5jb25zdCByZXRPY2N1ciA9IHJlcXVpcmUoJy4vcmV0T2NjdXInKTtcbmNvbnN0IHRoaXNPY2N1ciA9IHJlcXVpcmUoJy4vdGhpc09jY3VyJyk7XG5pbXBvcnQgKiBhcyBteVdhbGtlciBmcm9tICcuL3V0aWwvbXlXYWxrZXInXG5pbXBvcnQgKiBhcyBnZXRUeXBlRGF0YSBmcm9tICcuL2dldFR5cGVEYXRhJ1xuaW1wb3J0ICogYXMgZGVmYXVsdE9wdGlvbiBmcm9tICcuLi9kZWZhdWx0T3B0aW9uJ1xuXG5mdW5jdGlvbiBhbmFseXplKGlucHV0LCByZXRBbGwsIG9wdGlvbikge1xuICAgIC8vIHRoZSBTY29wZSBvYmplY3QgZm9yIGdsb2JhbCBzY29wZVxuICAgIC8vIHNjb3BlLlNjb3BlLmdsb2JhbFNjb3BlID0gbmV3IHNjb3BlLlNjb3BlKG51bGwpO1xuXG4gICAgaWYgKG9wdGlvbiA9PT0gdW5kZWZpbmVkKSB7XG4gICAgICAgIC8vIGlmIG5vIG9wdGlvbiBpcyBnaXZlbiwgdXNlIHRoZSBkZWZhdWx0IG9wdGlvblxuICAgICAgICBvcHRpb24gPSBkZWZhdWx0T3B0aW9uLm9wdGlvbnM7XG4gICAgfVxuICAgIC8vIHBhcnNpbmcgaW5wdXQgcHJvZ3JhbVxuICAgIHZhciBhc3Q7XG4gICAgdHJ5IHtcbiAgICAgICAgYXN0ID0gYWNvcm4ucGFyc2UoaW5wdXQsIG9wdGlvbi5hY29ybk9wdGlvbik7XG4gICAgfSBjYXRjaCAoZSkge1xuICAgICAgICBhc3QgPSBhY29ybl9sb29zZS5wYXJzZV9kYW1taXQoaW5wdXQsIG9wdGlvbi5hY29ybk9wdGlvbik7XG4gICAgfVxuXG4gICAgdmFyIG5vZGVBcnJheUluZGV4ZWRCeUxpc3QgPSBhdXguZ2V0Tm9kZUxpc3QoYXN0KTtcblxuICAgIC8vIFNob3cgQVNUIGJlZm9yZSBzY29wZSByZXNvbHV0aW9uXG4gICAgLy8gYXV4LnNob3dVbmZvbGRlZChhc3QpO1xuXG4gICAgdmFyIGdWYXJCbG9jayA9IG5ldyB2YXJCbG9jay5WYXJCbG9jayhcbiAgICAgICAgbnVsbCxcbiAgICAgICAgYXN0LFxuICAgICAgICB2YXJCbG9jay5WYXJCbG9jay5ibG9ja1R5cGVzLmdsb2JhbEJsb2NrLFxuICAgICAgICAvLyAndXNlIHN0cmljdCcgZGlyZWN0aXZlIGlzIGNoZWNrZWQgaW4gYW5ub3RhdGVCbG9ja0luZm8uXG4gICAgICAgIG9wdGlvbi5hY29ybk9wdGlvbi5zb3VyY2VUeXBlID09PSAnbW9kdWxlJ1xuICAgICk7XG5cbiAgICB2YXJCbG9jay5hbm5vdGF0ZUJsb2NrSW5mbyhhc3QsIGdWYXJCbG9jayk7XG5cbiAgICAvLyBTZXR0aW5nIHVwIHRoZSBzZW5zaXRpdml0eSBwYXJhbWV0ZXJcbiAgICAvLyBJdCBpcyBwb3NzaWJsZSB0byBjb21wdXRlIHRoZSBwYXJhbWV0ZXIgYnkgZXhhbWluaW5nIHRoZSBjb2RlLlxuICAgIGNvbnRleHQuY2hhbmdlU2Vuc2l0aXZpdHlQYXJhbWV0ZXIob3B0aW9uLnNlbnNpdGl2aXR5UGFyYW1ldGVyKTtcblxuICAgIHZhciBnQmxvY2sgPSBhc3RbJ0BibG9jayddO1xuICAgIHZhciBpbml0aWFsQ29udGV4dCA9IGNvbnRleHQuQ2FsbFNpdGVDb250ZXh0LmVwc2lsb25Db250ZXh0O1xuICAgIHZhciBnU2NvcGUgPSBnQmxvY2suZ2V0U2NvcGVJbnN0YW5jZShudWxsLCBpbml0aWFsQ29udGV4dCk7XG4gICAgdmFyIGdPYmplY3QgPSB0eXBlcy5ta09iakZyb21HbG9iYWxTY29wZShnU2NvcGUpO1xuICAgIHZhciBpbml0U3RhdHVzID0gbmV3IHN0YXR1cy5TdGF0dXMoXG4gICAgICAgIG5ldyB0eXBlcy5BVmFsKGdPYmplY3QpLFxuICAgICAgICB0eXBlcy5BVmFsTnVsbCxcbiAgICAgICAgdHlwZXMuQVZhbE51bGwsXG4gICAgICAgIGluaXRpYWxDb250ZXh0LFxuICAgICAgICBnU2NvcGUpO1xuICAgIC8vIHRoZSBwcm90b3R5cGUgb2JqZWN0IG9mIE9iamVjdFxuICAgIHZhciBPYmpQcm90byA9IG5ldyB0eXBlcy5PYmpUeXBlKG51bGwsICdPYmplY3QucHJvdG90eXBlJyk7XG4gICAgdmFyIHJ0Q1ggPSB7XG4gICAgICAgIGdsb2JhbE9iamVjdDogZ09iamVjdCxcbiAgICAgICAgLy8gdGVtcG9yYWxcbiAgICAgICAgcHJvdG9zOiB7XG4gICAgICAgICAgICBPYmplY3Q6IE9ialByb3RvLFxuICAgICAgICAgICAgRnVuY3Rpb246IG5ldyB0eXBlcy5PYmpUeXBlKG5ldyB0eXBlcy5BVmFsKE9ialByb3RvKSwgJ0Z1bmN0aW9uLnByb3RvdHlwZScpLFxuICAgICAgICAgICAgQXJyYXk6IG5ldyB0eXBlcy5PYmpUeXBlKG5ldyB0eXBlcy5BVmFsKE9ialByb3RvKSwgJ0FycmF5LnByb3RvdHlwZScpLFxuICAgICAgICAgICAgUmVnRXhwOiBuZXcgdHlwZXMuT2JqVHlwZShuZXcgdHlwZXMuQVZhbChPYmpQcm90byksICdSZWdFeHAucHJvdG90eXBlJyksXG4gICAgICAgICAgICBTdHJpbmc6IG5ldyB0eXBlcy5PYmpUeXBlKG5ldyB0eXBlcy5BVmFsKE9ialByb3RvKSwgJ1N0cmluZy5wcm90b3R5cGUnKSxcbiAgICAgICAgICAgIE51bWJlcjogbmV3IHR5cGVzLk9ialR5cGUobmV3IHR5cGVzLkFWYWwoT2JqUHJvdG8pLCAnTnVtYmVyLnByb3RvdHlwZScpLFxuICAgICAgICAgICAgQm9vbGVhbjogbmV3IHR5cGVzLk9ialR5cGUobmV3IHR5cGVzLkFWYWwoT2JqUHJvdG8pLCAnQm9vbGVhbi5wcm90b3R5cGUnKVxuICAgICAgICB9LFxuICAgICAgICDEiDogbmV3IHR5cGVzLkFic0NhY2hlKCksXG4gICAgICAgIG9wdGlvbjogb3B0aW9uXG4gICAgfTtcbiAgICBjR2VuLmFkZENvbnN0cmFpbnRzKGFzdCwgaW5pdFN0YXR1cywgcnRDWCk7XG4gICAgLy9hdXguc2hvd1VuZm9sZGVkKGdCbG9ja0FuZEFubm90YXRlZEFTVC5hc3QpO1xuICAgIC8vIGF1eC5zaG93VW5mb2xkZWQoY29uc3RyYWludHMpO1xuICAgIC8vIGF1eC5zaG93VW5mb2xkZWQoZ0Jsb2NrKTtcbiAgICAvLyBjb25zb2xlLmxvZyh1dGlsLmluc3BlY3QoZ0Jsb2NrLCB7ZGVwdGg6IDEwfSkpO1xuICAgIGlmIChyZXRBbGwpIHtcbiAgICAgICAgcmV0dXJuIHtcbiAgICAgICAgICAgIGdPYmplY3Q6IGdPYmplY3QsXG4gICAgICAgICAgICBBU1Q6IGFzdCxcbiAgICAgICAgICAgIGdCbG9jazogZ0Jsb2NrLFxuICAgICAgICAgICAgZ1Njb3BlOiBnU2NvcGUsXG4gICAgICAgICAgICDEiDogcnRDWC7EiFxuICAgICAgICB9O1xuICAgIH0gZWxzZSB7XG4gICAgICAgIHJldHVybiBnT2JqZWN0O1xuICAgIH1cbn1cblxuZXhwb3J0cy5hbmFseXplID0gYW5hbHl6ZTtcbmV4cG9ydHMuZmluZElkZW50aWZpZXJBdCA9IG15V2Fsa2VyLmZpbmRJZGVudGlmaWVyQXQ7XG5leHBvcnRzLmZpbmRWYXJSZWZzQXQgPSB2YXJSZWZzLmZpbmRWYXJSZWZzQXQ7XG5leHBvcnRzLm9uRXNjYXBpbmdTdGF0ZW1lbnQgPSByZXRPY2N1ci5vbkVzY2FwaW5nU3RhdGVtZW50O1xuZXhwb3J0cy5maW5kRXNjYXBpbmdTdGF0ZW1lbnRzID0gcmV0T2NjdXIuZmluZEVzY2FwaW5nU3RhdGVtZW50cztcbmV4cG9ydHMub25UaGlzS2V5d29yZCA9IHRoaXNPY2N1ci5vblRoaXNLZXl3b3JkO1xuZXhwb3J0cy5maW5kVGhpc0V4cHJlc3Npb25zID0gdGhpc09jY3VyLmZpbmRUaGlzRXhwcmVzc2lvbnM7XG5leHBvcnRzLmZpbmRTdXJyb3VuZGluZ05vZGUgPSBteVdhbGtlci5maW5kU3Vycm91bmRpbmdOb2RlO1xuZXhwb3J0cy5maW5kTWVtYmVyT3JWYXJpYWJsZUF0ID0gbXlXYWxrZXIuZmluZE1lbWJlck9yVmFyaWFibGVBdDtcbmV4cG9ydHMuZ2V0VHlwZURhdGEgPSBnZXRUeXBlRGF0YS5nZXRUeXBlQXRSYW5nZTtcbmV4cG9ydHMuZ2V0Q29tcGxldGlvbkF0UG9zID0gZ2V0VHlwZURhdGEuZ2V0Q29tcGxldGlvbkF0UG9zO1xuZXhwb3J0cy5nZXRGblR5cGVTdHJ1Y3R1cmVzQXQgPSBnZXRUeXBlRGF0YS5nZXRGblR5cGVTdHJ1Y3R1cmVzQXQ7XG5leHBvcnRzLmdldERlZmluaXRpb25TaXRlc0F0ID0gZ2V0VHlwZURhdGEuZ2V0RGVmaW5pdGlvblNpdGVzQXQ7XG4iLCJjb25zdCB3YWxrID0gcmVxdWlyZSgnYWNvcm4vZGlzdC93YWxrJyk7XG5pbXBvcnQgKiBhcyBteVdhbGtlciBmcm9tICcuL3V0aWwvbXlXYWxrZXInXG5cbi8qKlxuICogYXV4aWxpYXJ5IGZ1bmN0aW9uIGZvciB2aXNpdG9yJ3Mgc3RhdGUgY2hhbmdlXG4gKiBAcGFyYW0gbm9kZVxuICogQHBhcmFtIHN0XG4gKiBAcGFyYW0gbm9kZVR5cGVcbiAqIEByZXR1cm5zIHsqfVxuICovXG5mdW5jdGlvbiBzdENoYW5nZShub2RlLCBzdCwgbm9kZVR5cGUpIHtcbiAgICBjb25zdCBbZm5Ob2RlLCB0cnlOb2RlLCBvdXRlclRyeU5vZGVdID0gc3Q7XG4gICAgc3dpdGNoIChub2RlVHlwZSkge1xuICAgICAgICBjYXNlICdGdW5jdGlvbkRlY2xhcmF0aW9uJzpcbiAgICAgICAgY2FzZSAnRnVuY3Rpb25FeHByZXNzaW9uJzpcbiAgICAgICAgY2FzZSAnQXJyb3dGdW5jdGlvbkV4cHJlc3Npb24nOlxuICAgICAgICAgICAgcmV0dXJuIFtub2RlLCB1bmRlZmluZWRdO1xuICAgICAgICBjYXNlICdUcnlTdGF0ZW1lbnQnOlxuICAgICAgICAgICAgLy8gcmVtZW1iZXIgb3V0ZXIgdHJ5Tm9kZVxuICAgICAgICAgICAgcmV0dXJuIFtmbk5vZGUsIG5vZGUsIHRyeU5vZGVdO1xuICAgICAgICBjYXNlICdDYXRjaENsYXVzZSc6XG4gICAgICAgICAgICAvLyB1c2Ugb3V0ZXIgdHJ5IGFzIGl0cyB0cnlOb2RlXG4gICAgICAgICAgICByZXR1cm4gW2ZuTm9kZSwgb3V0ZXJUcnlOb2RlXTtcbiAgICAgICAgY2FzZSAnQmxvY2tTdGF0ZW1lbnQnOlxuICAgICAgICAgICAgaWYgKHN0Lm91dGVyKSB7XG4gICAgICAgICAgICAgICAgLy8gaXQncyBmaW5hbGx5IGJsb2NrXG4gICAgICAgICAgICAgICAgcmV0dXJuIFtmbk5vZGUsIG91dGVyVHJ5Tm9kZV07XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICAvLyBpdCdzIHRyeSBibG9ja1xuICAgICAgICAgICAgICAgIHJldHVybiBbZm5Ob2RlLCB0cnlOb2RlLCBvdXRlclRyeU5vZGVdO1xuICAgICAgICAgICAgfVxuICAgICAgICBkZWZhdWx0OlxuICAgICAgICAgICAgcmV0dXJuIFtmbk5vZGUsIHRyeU5vZGUsIG91dGVyVHJ5Tm9kZV07XG4gICAgfVxufVxuXG4vKipcbiAqIENoZWNrIHdoZXRoZXIgZ2l2ZW4gcG9zIGlzIG9uIGEgZnVuY3Rpb24ga2V5d29yZFxuICogQHBhcmFtIGFzdCAtIEFTVCBvZiBhIHByb2dyYW1cbiAqIEBwYXJhbSBwb3MgLSBpbmRleCBwb3NpdGlvblxuICogQHJldHVybnMgeyp9IC0gZnVuY3Rpb24gbm9kZSBvciBudWxsXG4gKi9cbmZ1bmN0aW9uIG9uRXNjYXBpbmdTdGF0ZW1lbnQoYXN0LCBwb3MpIHtcbiAgICAndXNlIHN0cmljdCc7XG5cbiAgICAvLyBmaW5kIGZ1bmN0aW9uIG5vZGVcbiAgICAvLyBzdCBpcyB0aGUgZW5jbG9zaW5nIGZ1bmN0aW9uXG4gICAgY29uc3Qgd2Fsa2VyID0gbXlXYWxrZXIud3JhcFdhbGtlcih3YWxrLm1ha2Uoe1xuICAgICAgICAgICAgVHJ5U3RhdGVtZW50OiAobm9kZSwgc3QsIGMpID0+IHtcbiAgICAgICAgICAgICAgICBjKG5vZGUuYmxvY2ssIHN0KTtcbiAgICAgICAgICAgICAgICAvLyBzZXQgZmxhZyBhZnRlciBwcm9jZXNzaW5nIHRyeSBibG9ja1xuICAgICAgICAgICAgICAgIHN0Lm91dGVyID0gdHJ1ZTtcbiAgICAgICAgICAgICAgICBpZiAobm9kZS5oYW5kbGVyKSBjKG5vZGUuaGFuZGxlciwgc3QpO1xuICAgICAgICAgICAgICAgIGlmIChub2RlLmZpbmFsaXplcikgYyhub2RlLmZpbmFsaXplciwgc3QpO1xuICAgICAgICAgICAgfSxcbiAgICAgICAgICAgIENhdGNoQ2xhdXNlOiAobm9kZSwgc3QsIGMpID0+IHtcbiAgICAgICAgICAgICAgICBjKG5vZGUuYm9keSwgc3QpO1xuICAgICAgICAgICAgfVxuICAgICAgICB9LCB3YWxrLmJhc2UpLFxuICAgICAgICAvLyBwcmVcbiAgICAgICAgKG5vZGUsIHN0LCBub2RlVHlwZSkgPT4ge1xuICAgICAgICAgICAgaWYgKG5vZGUuc3RhcnQgPiBwb3MgfHwgbm9kZS5lbmQgPCBwb3MpIHtcbiAgICAgICAgICAgICAgICByZXR1cm4gZmFsc2U7XG4gICAgICAgICAgICB9XG5cbiAgICAgICAgICAgIC8vIG9uIGEgZnVuY3Rpb24ga2V5d29yZCwgOCBpcyB0aGUgbGVuZ3RoIG9mICdmdW5jdGlvbidcbiAgICAgICAgICAgIC8vIG9yIG9uIHJldHVybiBrZXl3b3JkLCA2IGlzIHRoZSBsZW5ndGggb2YgJ3JldHVybidcbiAgICAgICAgICAgIC8vIG9yIG9uIHRocm93IGtleXdvcmQsIDUgaXMgdGhlIGxlbmd0aCBvZiAndGhyb3cnXG4gICAgICAgICAgICBpZiAoKChub2RlVHlwZSA9PT0gJ0Z1bmN0aW9uRGVjbGFyYXRpb24nIHx8IG5vZGVUeXBlID09PSAnRnVuY3Rpb25FeHByZXNzaW9uJylcbiAgICAgICAgICAgICAgICAmJiAobm9kZS5zdGFydCA8PSBwb3MgJiYgcG9zIDw9IG5vZGUuc3RhcnQgKyA4KSlcbiAgICAgICAgICAgICAgICB8fFxuICAgICAgICAgICAgICAgIChub2RlVHlwZSA9PT0gJ1JldHVyblN0YXRlbWVudCdcbiAgICAgICAgICAgICAgICAmJiAobm9kZS5zdGFydCA8PSBwb3MgJiYgcG9zIDw9IG5vZGUuc3RhcnQgKyA2KSlcbiAgICAgICAgICAgICAgICB8fFxuICAgICAgICAgICAgICAgIChub2RlVHlwZSA9PT0gJ1Rocm93U3RhdGVtZW50J1xuICAgICAgICAgICAgICAgICYmIChub2RlLnN0YXJ0IDw9IHBvcyAmJiBwb3MgPD0gbm9kZS5zdGFydCArIDUpKSkge1xuICAgICAgICAgICAgICAgIC8vIHJlY29yZCB0aGUgZm91bmQgbm9kZSB0eXBlXG4gICAgICAgICAgICAgICAgc3QudHlwZSA9IG5vZGUudHlwZTtcbiAgICAgICAgICAgICAgICB0aHJvdyBzdDtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIHJldHVybiB0cnVlO1xuICAgICAgICB9LFxuICAgICAgICAvLyBwb3N0XG4gICAgICAgIHVuZGVmaW5lZCxcbiAgICAgICAgLy8gc3RDaGFuZ2VcbiAgICAgICAgc3RDaGFuZ2VcbiAgICApO1xuXG4gICAgdHJ5IHtcbiAgICAgICAgd2Fsay5yZWN1cnNpdmUoYXN0LCBbXSwgd2Fsa2VyKTtcbiAgICB9IGNhdGNoIChlKSB7XG4gICAgICAgIGlmIChlICYmIGUgaW5zdGFuY2VvZiBBcnJheSkge1xuICAgICAgICAgICAgLy8gZm91bmRcbiAgICAgICAgICAgIHJldHVybiBlO1xuICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgICAgLy8gb3RoZXIgZXJyb3JcbiAgICAgICAgICAgIHRocm93IGU7XG4gICAgICAgIH1cbiAgICB9XG4gICAgLy8gaWRlbnRpZmllciBub3QgZm91bmRcbiAgICByZXR1cm4gbnVsbDtcbn1cblxuLyoqXG4gKiBHaXZlbiBhIG5vZGUsIGZpbmQgaXRzIGVzY2FwaW5nIG5vZGVzXG4gKlxuICogQHBhcmFtIG5vZGVQYWlyIC0gQVNUIG5vZGUgb2YgYSBmdW5jdGlvbiwgcG9zc2libHkgd2l0aCBubyBhbm5vdGF0aW9uXG4gKiBAcmV0dXJucyB7Kn0gLSBhcnJheSBvZiBBU1Qgbm9kZXNcbiAqL1xuZnVuY3Rpb24gZ2V0RXNjYXBpbmdOb2Rlcyhub2RlUGFpcikge1xuICAgICd1c2Ugc3RyaWN0JztcbiAgICBjb25zdCBub2RlcyA9IFtdO1xuICAgIGNvbnN0IFtmbk5vZGUsIHRyeU5vZGVdID0gbm9kZVBhaXI7XG5cbiAgICBjb25zdCB3YWxrZXIgPSBteVdhbGtlci53cmFwV2Fsa2VyKFxuICAgICAgICB3YWxrLm1ha2Uoe1xuICAgICAgICAgICAgVHJ5U3RhdGVtZW50OiAobm9kZSwgc3QsIGMpID0+IHtcbiAgICAgICAgICAgICAgICBjKG5vZGUuYmxvY2ssIHN0KTtcbiAgICAgICAgICAgICAgICAvLyBzZXQgZmxhZyBhZnRlciBwcm9jZXNzaW5nIHRyeSBibG9ja1xuICAgICAgICAgICAgICAgIHN0Lm91dGVyID0gdHJ1ZTtcbiAgICAgICAgICAgICAgICAvLyB2aXNpdCB0aG9zZSBCbG9ja1N0YXRlbWVudFxuICAgICAgICAgICAgICAgIGlmIChub2RlLmhhbmRsZXIpIGMobm9kZS5oYW5kbGVyLCBzdCk7XG4gICAgICAgICAgICAgICAgaWYgKG5vZGUuZmluYWxpemVyKSBjKG5vZGUuZmluYWxpemVyLCBzdCk7XG4gICAgICAgICAgICB9LFxuICAgICAgICAgICAgUmV0dXJuU3RhdGVtZW50OiAobm9kZSkgPT4ge1xuICAgICAgICAgICAgICAgIGlmIChub2RlUGFpci50eXBlID09PSAnVGhyb3dTdGF0ZW1lbnQnICYmIHRyeU5vZGUpIHJldHVybjtcbiAgICAgICAgICAgICAgICBub2Rlcy5wdXNoKG5vZGUpO1xuICAgICAgICAgICAgfSxcbiAgICAgICAgICAgIEZ1bmN0aW9uOiAoKSA9PiB7XG4gICAgICAgICAgICAgICAgLy8gbm90IHZpc2l0IGlubmVyIGZ1bmN0aW9uc1xuICAgICAgICAgICAgfSxcbiAgICAgICAgICAgIFRocm93U3RhdGVtZW50OiAobm9kZSwgW2YsdF0pID0+IHtcbiAgICAgICAgICAgICAgICBpZiAoKG5vZGVQYWlyLnR5cGUgPT09ICdUaHJvd1N0YXRlbWVudCcgJiYgdHJ5Tm9kZSA9PT0gdClcbiAgICAgICAgICAgICAgICAgICAgfHwgdCA9PT0gdW5kZWZpbmVkKSB7XG4gICAgICAgICAgICAgICAgICAgIG5vZGVzLnB1c2gobm9kZSk7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgfSxcbiAgICAgICAgICAgIENhdGNoQ2xhdXNlOiAobm9kZSwgc3QsIGMpID0+IHtcbiAgICAgICAgICAgICAgICBjKG5vZGUuYm9keSwgc3QpO1xuICAgICAgICAgICAgfVxuICAgICAgICB9LCB3YWxrLmJhc2UpLFxuICAgICAgICB1bmRlZmluZWQsXG4gICAgICAgIHVuZGVmaW5lZCxcbiAgICAgICAgc3RDaGFuZ2UpO1xuXG4gICAgaWYgKG5vZGVQYWlyLnR5cGUgPT09ICdUaHJvd1N0YXRlbWVudCcgJiYgdHJ5Tm9kZSkge1xuICAgICAgICB3YWxrLnJlY3Vyc2l2ZSh0cnlOb2RlLmJsb2NrLCBbdW5kZWZpbmVkLCB0cnlOb2RlXSwgd2Fsa2VyKTtcbiAgICB9IGVsc2Uge1xuICAgICAgICB3YWxrLnJlY3Vyc2l2ZShmbk5vZGUuYm9keSwgW2ZuTm9kZSwgdW5kZWZpbmVkXSwgd2Fsa2VyKTtcbiAgICB9XG5cbiAgICByZXR1cm4gbm9kZXM7XG59XG5cbi8qKlxuICogRmluZCByZXR1cm4gbm9kZXMgY29ycmVzcG9uZGluZyB0byB0aGUgcG9zaXRpb25cbiAqIGlmIHRoZSBwb3MgaXMgb24gYSBmdW5jdGlvbiBrZXl3b3JkXG4gKlxuICogQHBhcmFtIGFzdCAtIEFTVCBub2RlIG9mIGEgcHJvZ3JhbSwgcG9zc2libHkgd2l0aCBubyBhbm5vdGF0aW9uXG4gKiBAcGFyYW0gcG9zIC0gY3Vyc29yIHBvc2l0aW9uXG4gKiBAcGFyYW0gaW5jbHVkZUtleXdvcmQgLSB3aGV0aGVyIHRvIGluY2x1ZGUga2V5d29yZCByYW5nZVxuICogQHJldHVybnMge0FycmF5fSAtIGFycmF5IG9mIEFTVCBub2RlcyBvZiBlc2NhcGluZyBzdGF0ZW1lbnRzXG4gKi9cbmZ1bmN0aW9uIGZpbmRFc2NhcGluZ1N0YXRlbWVudHMoYXN0LCBwb3MsIGluY2x1ZGVLZXl3b3JkKSB7XG4gICAgJ3VzZSBzdHJpY3QnO1xuXG4gICAgY29uc3Qgbm9kZVBhaXIgPSBvbkVzY2FwaW5nU3RhdGVtZW50KGFzdCwgcG9zKTtcbiAgICBpZiAoIW5vZGVQYWlyKSB7XG4gICAgICAgIHJldHVybiBudWxsO1xuICAgIH1cblxuICAgIGNvbnN0IHJhbmdlcyA9IGdldEVzY2FwaW5nTm9kZXMobm9kZVBhaXIpLm1hcChcbiAgICAgICAgICAgIG5vZGUgPT4ge1xuICAgICAgICAgICAgICAgIHJldHVybiB7c3RhcnQ6IG5vZGUuc3RhcnQsIGVuZDogbm9kZS5lbmR9O1xuICAgICAgICAgICAgfSk7XG4gICAgY29uc3QgW2ZuTm9kZSwgdHJ5Tm9kZV0gPSBub2RlUGFpcjtcbiAgICAvLyBJZiBubyBleHBsaWNpdCBlc2NhcGluZyBleGlzdHNcbiAgICAvLyBoaWdobGlnaHQgdGhlIGNsb3NpbmcgYnJhY2Ugb2YgdGhlIGZ1bmN0aW9uIGJvZHlcbiAgICBpZiAobm9kZVBhaXIudHlwZSAhPT0gJ1Rocm93U3RhdGVtZW50JyAmJiByYW5nZXMubGVuZ3RoID09PSAwKSB7XG4gICAgICAgIHJhbmdlcy5wdXNoKHtzdGFydDogZm5Ob2RlLmVuZCAtIDEsIGVuZDogZm5Ob2RlLmVuZH0pO1xuICAgIH1cblxuICAgIC8vIGhpZ2hsaWdodGluZyAnY2F0Y2gnXG4gICAgaWYgKG5vZGVQYWlyLnR5cGUgPT09ICdUaHJvd1N0YXRlbWVudCcgJiYgdHJ5Tm9kZSkge1xuICAgICAgICByYW5nZXMucHVzaCh7c3RhcnQ6IHRyeU5vZGUuaGFuZGxlci5zdGFydCwgZW5kOiB0cnlOb2RlLmhhbmRsZXIuc3RhcnQgKyA1fSk7XG4gICAgfSBlbHNlIGlmIChpbmNsdWRlS2V5d29yZCkge1xuICAgICAgICBpZiAoZm5Ob2RlLnR5cGUgIT09ICdBcnJvd0Z1bmN0aW9uRXhwcmVzc2lvbicpIHtcbiAgICAgICAgICAgIC8vIGFkZCByYW5nZXMgZm9yICdmdW5jdGlvbidcbiAgICAgICAgICAgIHJhbmdlcy5wdXNoKHtzdGFydDogZm5Ob2RlLnN0YXJ0LCBlbmQ6IGZuTm9kZS5zdGFydCArIDh9KTtcbiAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICAgIC8vIFRPRE86IGFkZCByYW5nZSBmb3IgZmF0IGFycm93XG4gICAgICAgIH1cbiAgICB9XG4gICAgcmV0dXJuIHJhbmdlcztcbn1cblxuZXhwb3J0cy5vbkVzY2FwaW5nU3RhdGVtZW50ID0gb25Fc2NhcGluZ1N0YXRlbWVudDtcbmV4cG9ydHMuZmluZEVzY2FwaW5nU3RhdGVtZW50cyA9IGZpbmRFc2NhcGluZ1N0YXRlbWVudHM7XG4iLCJjb25zdCB3YWxrID0gcmVxdWlyZSgnYWNvcm4vZGlzdC93YWxrJyk7XG5pbXBvcnQgKiBhcyBteVdhbGtlciBmcm9tICcuL3V0aWwvbXlXYWxrZXInXG5cbi8qKlxuICogQ2hlY2sgd2hldGhlciBnaXZlbiBwb3MgaXMgb24gYSB0aGlzIGtleXdvcmRcbiAqIEBwYXJhbSBhc3QgLSBBU1Qgb2YgYSBwcm9ncmFtXG4gKiBAcGFyYW0gcG9zIC0gaW5kZXggcG9zaXRpb25cbiAqIEByZXR1cm5zIHsqfSAtIGZ1bmN0aW9uIG5vZGUgb3IgbnVsbFxuICovXG5mdW5jdGlvbiBvblRoaXNLZXl3b3JkKGFzdCwgcG9zKSB7XG4gICAgJ3VzZSBzdHJpY3QnO1xuXG4gICAgLy8gZmluZCBmdW5jdGlvbiBub2RlXG4gICAgLy8gc3QgaXMgdGhlIGVuY2xvc2luZyBmdW5jdGlvblxuICAgIGNvbnN0IHdhbGtlciA9IG15V2Fsa2VyLndyYXBXYWxrZXIod2Fsay5iYXNlLFxuICAgICAgICAvLyBwcmVcbiAgICAgICAgKG5vZGUsIHN0KSA9PiB7XG4gICAgICAgICAgICBpZiAobm9kZS5zdGFydCA+IHBvcyB8fCBub2RlLmVuZCA8IHBvcykge1xuICAgICAgICAgICAgICAgIHJldHVybiBmYWxzZTtcbiAgICAgICAgICAgIH1cblxuICAgICAgICAgICAgaWYgKG5vZGUudHlwZSA9PT0gJ1RoaXNFeHByZXNzaW9uJykge1xuICAgICAgICAgICAgICAgIHRocm93IHN0O1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgcmV0dXJuIHRydWU7XG4gICAgICAgIH0sXG4gICAgICAgIC8vIHBvc3RcbiAgICAgICAgdW5kZWZpbmVkLFxuICAgICAgICAvLyBzdENoYW5nZVxuICAgICAgICAobm9kZSwgc3QpID0+IHtcbiAgICAgICAgICAgIGlmIChub2RlLnR5cGUgPT09ICdGdW5jdGlvbkRlY2xhcmF0aW9uJ1xuICAgICAgICAgICAgICAgIHx8IG5vZGUudHlwZSA9PT0gJ0Z1bmN0aW9uRXhwcmVzc2lvbicpIHtcbiAgICAgICAgICAgICAgICByZXR1cm4gbm9kZTtcbiAgICAgICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgICAgICAgcmV0dXJuIHN0O1xuICAgICAgICAgICAgfVxuICAgICAgICB9KTtcblxuICAgIHRyeSB7XG4gICAgICAgIHdhbGsucmVjdXJzaXZlKGFzdCwgdW5kZWZpbmVkLCB3YWxrZXIpO1xuICAgIH0gY2F0Y2ggKGUpIHtcbiAgICAgICAgaWYgKGUgJiYgZS50eXBlICYmXG4gICAgICAgICAgICAoZS50eXBlID09PSAnRnVuY3Rpb25FeHByZXNzaW9uJ1xuICAgICAgICAgICAgfHwgZS50eXBlID09PSAnRnVuY3Rpb25EZWNsYXJhdGlvbicpKSB7XG4gICAgICAgICAgICByZXR1cm4gZTtcbiAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICAgIHRocm93IGU7XG4gICAgICAgIH1cbiAgICB9XG4gICAgLy8gaWRlbnRpZmllciBub3QgZm91bmRcbiAgICByZXR1cm4gbnVsbDtcbn1cblxuLyoqXG4gKiBHaXZlbiBhIGZ1bmN0aW9uIG5vZGUsIGZpbmQgaXRzIHRoaXMgbm9kZXNcbiAqXG4gKiBAcGFyYW0gZk5vZGUgLSBBU1Qgbm9kZSBvZiBhIGZ1bmN0aW9uLCBwb3NzaWJseSB3aXRoIG5vIGFubm90YXRpb25cbiAqIEByZXR1cm5zIHsqfSAtIGFycmF5IG9mIEFTVCBub2Rlc1xuICovXG5mdW5jdGlvbiBnZXRUaGlzTm9kZXMoZk5vZGUpIHtcbiAgICAndXNlIHN0cmljdCc7XG4gICAgY29uc3QgcmV0cyA9IFtdO1xuICAgIGlmIChmTm9kZS50eXBlICE9PSAnRnVuY3Rpb25FeHByZXNzaW9uJ1xuICAgICAgICAmJiBmTm9kZS50eXBlICE9PSAnRnVuY3Rpb25EZWNsYXJhdGlvbicpIHtcbiAgICAgICAgdGhyb3cgRXJyb3IoJ2ZOb2RlIHNob3VsZCBiZSBhIGZ1bmN0aW9uIG5vZGUnKTtcbiAgICB9XG5cbiAgICBjb25zdCB3YWxrZXIgPSB3YWxrLm1ha2Uoe1xuICAgICAgICBUaGlzRXhwcmVzc2lvbjogKG5vZGUpID0+IHtcbiAgICAgICAgICAgIHJldHVybiByZXRzLnB1c2gobm9kZSk7XG4gICAgICAgIH0sXG4gICAgICAgIEZ1bmN0aW9uRGVjbGFyYXRpb246ICgpID0+IHtcbiAgICAgICAgICAgIC8vIG5vdCB2aXNpdCBmdW5jdGlvbiBkZWNsYXJhdGlvblxuICAgICAgICB9LFxuICAgICAgICBGdW5jdGlvbkV4cHJlc3Npb246ICgpID0+IHtcbiAgICAgICAgICAgIC8vIG5vdCB2aXNpdCBmdW5jdGlvbiBleHByZXNzaW9uXG4gICAgICAgIH1cbiAgICB9LCB3YWxrLmJhc2UpO1xuXG4gICAgd2Fsay5yZWN1cnNpdmUoZk5vZGUuYm9keSwgdW5kZWZpbmVkLCB3YWxrZXIpO1xuXG4gICAgcmV0dXJuIHJldHM7XG59XG5cbi8qKlxuICogRmluZCB0aGlzIG5vZGVzIGlmIHRoZSBwb3MgaXMgb24gYSB0aGlzIGtleXdvcmRcbiAqXG4gKiBAcGFyYW0gYXN0IC0gQVNUIG5vZGUgb2YgYSBwcm9ncmFtLCBwb3NzaWJseSB3aXRoIG5vIGFubm90YXRpb25cbiAqIEBwYXJhbSBwb3MgLSBjdXJzb3IgcG9zaXRpb25cbiAqIEBwYXJhbSBpbmNsdWRlRnVuY3Rpb25LZXl3b3JkIC0gd2hldGhlciB0byBpbmNsdWRlIGZ1bmN0aW9uIGtleXdvcmQgcmFuZ2VcbiAqIEByZXR1cm5zIHtBcnJheX0gLSBhcnJheSBvZiBBU1Qgbm9kZXMgb2YgcmV0dXJuIHN0YXRlbWVudHNcbiAqL1xuZnVuY3Rpb24gZmluZFRoaXNFeHByZXNzaW9ucyhhc3QsIHBvcywgaW5jbHVkZUZ1bmN0aW9uS2V5d29yZCkge1xuICAgICd1c2Ugc3RyaWN0JztcblxuICAgIGNvbnN0IGZOb2RlID0gb25UaGlzS2V5d29yZChhc3QsIHBvcyk7XG4gICAgaWYgKCFmTm9kZSkge1xuICAgICAgICAvLyBwb3MgaXMgbm90IG9uIHRoaXMga2V5d29yZFxuICAgICAgICByZXR1cm4gbnVsbDtcbiAgICB9XG5cbiAgICBjb25zdCByZXRzID0gZ2V0VGhpc05vZGVzKGZOb2RlKTtcbiAgICBpZiAoaW5jbHVkZUZ1bmN0aW9uS2V5d29yZCkge1xuICAgICAgICByZXRzLnB1c2goe3N0YXJ0OiBmTm9kZS5zdGFydCwgZW5kOiBmTm9kZS5zdGFydCArIDh9KTtcbiAgICB9XG4gICAgcmV0dXJuIHJldHM7XG59XG5cbmV4cG9ydHMub25UaGlzS2V5d29yZCA9IG9uVGhpc0tleXdvcmQ7XG5leHBvcnRzLmZpbmRUaGlzRXhwcmVzc2lvbnMgPSBmaW5kVGhpc0V4cHJlc3Npb25zO1xuIiwiY29uc3Qgd2FsayA9IHJlcXVpcmUoJ2Fjb3JuL2Rpc3Qvd2FsaycpO1xuXG4vKipcbiAqIFJldHVybnMgYSB3YWxrZXIgdGhhdCBkb2VzIG5vdGhpbmcgZm9yIGVhY2ggbm9kZS5cbiAqIFVzZSBhcyBhIGJhc2Ugd2Fsa2VyIHdoZW4geW91IG5lZWQgdG8gd2FsayBvbiBvbmx5IHNvbWUgdHlwZXMgb2Ygbm9kZXMuXG4gKiBAcmV0dXJucyB7T2JqZWN0fVxuICovXG5mdW5jdGlvbiBtYWtlTm9vcFdhbGtlcigpIHtcbiAgICBjb25zdCB3YWxrZXIgPSBPYmplY3QuY3JlYXRlKG51bGwpO1xuICAgIGNvbnN0IG5vb3BGdW5jID0gKCkgPT4ge307XG4gICAgZm9yIChsZXQgbmFtZSBpbiBPYmplY3QuZ2V0T3duUHJvcGVydHlOYW1lcyh3YWxrLmJhc2UpKSB7XG4gICAgICAgIHdhbGtlcltuYW1lXSA9IG5vb3BGdW5jO1xuICAgIH1cbiAgICByZXR1cm4gd2Fsa2VyO1xufVxuZXhwb3J0IGNvbnN0IG5vb3BXYWxrZXIgPSBtYWtlTm9vcFdhbGtlcigpO1xuXG4vKipcbiAqIENoZWNrIHdoZXRoZXIgdGhlIHBhdHRlcm4gdXNlcyBkZWZhdWx0c1xuICogQHBhcmFtIHB0bk5vZGUgLSBhIHBhdHRlcm4gbm9kZVxuICogQHJldHVybnMge2Jvb2xlYW59XG4gKi9cbmV4cG9ydCBmdW5jdGlvbiBwYXR0ZXJuSGFzRGVmYXVsdHMocHRuTm9kZSkge1xuICAgIGNvbnN0IGFzc2lnbm1lbnRQYXR0ZXJuRmluZGVyID0gd2Fsay5tYWtlKG5vb3BXYWxrZXIsIHtcbiAgICAgICAgQXNzaWdubWVudFBhdHRlcm46IChub2RlLCBzdCwgYykgPT4ge1xuICAgICAgICAgICAgdGhyb3cgbmV3IEZvdW5kKCk7XG4gICAgICAgIH0sXG4gICAgICAgIE9iamVjdFBhdHRlcm46IHdhbGsuYmFzZS5PYmplY3RQYXR0ZXJuLFxuICAgICAgICBBcnJheVBhdHRlcm46IHdhbGsuYmFzZS5BcnJheUV4cHJlc3Npb24sXG4gICAgICAgIFJlc3RFbGVtZW50OiB3YWxrLmJhc2UuUmVzdEVsZW1lbnRcbiAgICB9KTtcblxuICAgIHRyeSB7XG4gICAgICAgIHdhbGsucmVjdXJzaXZlKHB0bk5vZGUsIHVuZGVmaW5lZCwgYXNzaWdubWVudFBhdHRlcm5GaW5kZXIpO1xuICAgIH0gY2F0Y2ggKGUpIHtcbiAgICAgICAgaWYgKGUgaW5zdGFuY2VvZiBGb3VuZCkge1xuICAgICAgICAgICAgcmV0dXJuIHRydWU7XG4gICAgICAgIH1cbiAgICB9XG4gICAgcmV0dXJuIGZhbHNlO1xufVxuXG4vKipcbiAqIGEgd2Fsa2VyIHRoYXQgdmlzaXRzIGVhY2ggaWQgZXZlbiB0aG91Z2ggaXQgaXMgdmFyIGRlY2xhcmF0aW9uXG4gKiB0aGUgcGFyYW1ldGVyIHZiIGRlbm90ZSB2YXJCbG9ja1xuICovXG5leHBvcnQgY29uc3QgdmFyV2Fsa2VyID0gd2Fsay5tYWtlKHtcbiAgICBGdW5jdGlvbjogKG5vZGUsIHZiLCBjKSA9PiB7XG4gICAgICAgIGlmIChub2RlLmlkKSBjKG5vZGUuaWQsIHZiLCAnUGF0dGVybicpO1xuICAgICAgICBjb25zdCBwYXJhbVZiID0gbm9kZVsnQGJsb2NrJ10gfHwgbm9kZS5ib2R5WydAYmxvY2snXTtcbiAgICAgICAgZm9yIChsZXQgaSA9IDA7IGkgPCBub2RlLnBhcmFtcy5sZW5ndGg7IGkrKykge1xuICAgICAgICAgICAgYyhub2RlLnBhcmFtc1tpXSwgcGFyYW1WYiwgJ1BhdHRlcm4nKTtcbiAgICAgICAgfVxuICAgICAgICBjb25zdCBpbm5lclZiID0gbm9kZS5ib2R5WydAYmxvY2snXTtcbiAgICAgICAgYyhub2RlLmJvZHksIGlubmVyVmIsIG5vZGUuZXhwcmVzc2lvbiA/ICdTY29wZUV4cHJlc3Npb24nIDogJ1Njb3BlQm9keScpO1xuICAgIH0sXG4gICAgRm9yU3RhdGVtZW50OiAobm9kZSwgdmIsIGMpID0+IHtcbiAgICAgICAgY29uc3QgaW5uZXJWYiA9IG5vZGVbJ0BibG9jayddIHx8IHZiO1xuICAgICAgICAvLyBVc2UgRm9yU3RhdGVtZW50IG9mIGJhc2Ugd2Fsa2VyXG4gICAgICAgIHdhbGsuYmFzZS5Gb3JTdGF0ZW1lbnQobm9kZSwgaW5uZXJWYiwgYyk7XG4gICAgfSxcbiAgICBCbG9ja1N0YXRlbWVudDogKG5vZGUsIHZiLCBjKSA9PiB7XG4gICAgICAgIGNvbnN0IGlubmVyVmIgPSBub2RlWydAYmxvY2snXSB8fCB2YjtcbiAgICAgICAgLy8gVXNlIEJsb2NrU3RhdGVtZW50IG9mIGJhc2Ugd2Fsa2VyXG4gICAgICAgIHdhbGsuYmFzZS5CbG9ja1N0YXRlbWVudChub2RlLCBpbm5lclZiLCBjKTtcbiAgICB9LFxuICAgIFRyeVN0YXRlbWVudDogKG5vZGUsIHZiLCBjKSA9PiB7XG4gICAgICAgIGMobm9kZS5ibG9jaywgdmIpO1xuICAgICAgICBpZiAobm9kZS5oYW5kbGVyKSB7XG4gICAgICAgICAgICAvLyBEbyBub3QgdmlzaXQgcGFyYW1ldGVyIHdpdGggY3VycmVudCB2YlxuICAgICAgICAgICAgLy8gdGhlIHBhcmFtZXRlciB3aWxsIGJlIHZpc2l0ZWQgaW4gQ2F0Y2hDbGF1c2Ugd2l0aCBjaGFuZ2VkIHZiXG4gICAgICAgICAgICBjKG5vZGUuaGFuZGxlciwgdmIpO1xuICAgICAgICB9XG4gICAgICAgIGlmIChub2RlLmZpbmFsaXplcikge1xuICAgICAgICAgICAgYyhub2RlLmZpbmFsaXplciwgdmIpO1xuICAgICAgICB9XG4gICAgfSxcbiAgICBDYXRjaENsYXVzZTogKG5vZGUsIHZiLCBjKSA9PiB7XG4gICAgICAgIGNvbnN0IGNhdGNoVmIgPSBub2RlLmJvZHlbJ0BibG9jayddO1xuICAgICAgICAvLyBOZWVkIHRvIGhhbmRsZSB0aGUgcGFyYW1ldGVyIGluIGNoYW5nZWQgYmxvY2tcbiAgICAgICAgYyhub2RlLnBhcmFtLCBjYXRjaFZiKTtcbiAgICAgICAgYyhub2RlLmJvZHksIGNhdGNoVmIpO1xuICAgIH0sXG4gICAgVmFyaWFibGVQYXR0ZXJuOiAobm9kZSwgdmIsIGMpID0+IHtcbiAgICAgICAgLy8gTm90ZSB0aGF0IHdhbGsuYmFzZS5JZGVudGlmaWVyIGlzICdpZ25vcmUuJ1xuICAgICAgICAvLyB2YXJXYWxrZXIgc2hvdWxkIHZpc2l0IHZhcmlhYmxlcyBpbiBMSFMuXG4gICAgICAgIGMobm9kZSwgdmIsICdJZGVudGlmaWVyJyk7XG4gICAgfVxufSk7XG5cbi8qKlxuICogV3JhcCBhIHdhbGtlciB3aXRoIHByZS0gYW5kIHBvc3QtIGFjdGlvbnNcbiAqXG4gKiBAcGFyYW0gd2Fsa2VyIC0gYmFzZSB3YWxrZXJcbiAqIEBwYXJhbSBwcmVOb2RlIC0gQXBwbHkgYmVmb3JlIHZpc2l0aW5nIHRoZSBjdXJyZW50IG5vZGUuXG4gKiBJZiByZXR1cm5zIGZhbHNlLCBkbyBub3QgdmlzaXQgdGhlIG5vZGUuXG4gKiBAcGFyYW0gcG9zdE5vZGUgLSBBcHBseSBhZnRlciB2aXNpdGluZyB0aGUgY3VycmVudCBub2RlLlxuICogSWYgZ2l2ZW4sIHJldHVybiB2YWx1ZXMgYXJlIG92ZXJyaWRkZW4uXG4gKiBAcGFyYW0gc3RDaGFuZ2UgLSBzdGF0ZSBjaGFuZ2UgZnVuY3Rpb25cbiAqIEByZXR1cm5zIHsqfSAtIGEgbmV3IHdhbGtlclxuICovXG5leHBvcnQgZnVuY3Rpb24gd3JhcFdhbGtlcih3YWxrZXIsIHByZU5vZGUsIHBvc3ROb2RlLCBzdENoYW5nZSkge1xuICAgICd1c2Ugc3RyaWN0JztcbiAgICBjb25zdCByZXRXYWxrZXIgPSB7fTtcbiAgICAvLyB3cmFwcGluZyBlYWNoIGZ1bmN0aW9uIHByZU5vZGUgYW5kIHBvc3ROb2RlXG4gICAgZm9yIChsZXQgbm9kZVR5cGUgaW4gd2Fsa2VyKSB7XG4gICAgICAgIGlmICghd2Fsa2VyLmhhc093blByb3BlcnR5KG5vZGVUeXBlKSkge1xuICAgICAgICAgICAgY29udGludWU7XG4gICAgICAgIH1cbiAgICAgICAgcmV0V2Fsa2VyW25vZGVUeXBlXSA9IChub2RlLCBzdCwgYykgPT4ge1xuICAgICAgICAgICAgbGV0IHJldDtcbiAgICAgICAgICAgIGxldCBuZXdTdCA9IHN0O1xuICAgICAgICAgICAgaWYgKHN0Q2hhbmdlKSB7XG4gICAgICAgICAgICAgICAgbmV3U3QgPSBzdENoYW5nZShub2RlLCBzdCwgbm9kZVR5cGUpO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgaWYgKCFwcmVOb2RlIHx8IHByZU5vZGUobm9kZSwgbmV3U3QsIG5vZGVUeXBlKSkge1xuICAgICAgICAgICAgICAgIHJldCA9IHdhbGtlcltub2RlVHlwZV0obm9kZSwgbmV3U3QsIGMpO1xuICAgICAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICAgICAgICByZXR1cm47XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBpZiAocG9zdE5vZGUpIHtcbiAgICAgICAgICAgICAgICByZXQgPSBwb3N0Tm9kZShub2RlLCBuZXdTdCwgbm9kZVR5cGUpO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgcmV0dXJuIHJldDtcbiAgICAgICAgfVxuICAgIH1cbiAgICByZXR1cm4gcmV0V2Fsa2VyO1xufVxuXG4vKipcbiAqIEEgdXRpbGl0eSBjbGFzcyBmb3Igc2VhcmNoaW5nIEFTVHMuXG4gKiBXZSB1c2UgaW5mbyB0byByZWNvcmQgYW55IHVzZWZ1bCBpbmZvcm1hdGlvbi5cbiAqL1xuZXhwb3J0IGNsYXNzIEZvdW5kIHtcbiAgICBjb25zdHJ1Y3RvcihpbmZvKSB7XG4gICAgICAgIHRoaXMuaW5mbyA9IGluZm87XG4gICAgfVxufVxuXG5leHBvcnQgZnVuY3Rpb24gaXNEdW1teUlkTm9kZShub2RlKSB7XG4gICAgaWYgKG5vZGUudHlwZSAhPT0gJ0lkZW50aWZpZXInKSB7XG4gICAgICAgIHRocm93IG5ldyBFcnJvcignU2hvdWxkIGJlIGFuIElkZW50aWZpZXIgbm9kZScpO1xuICAgIH1cbiAgICByZXR1cm4gbm9kZS5uYW1lID09PSAn4pyWJyAmJiBub2RlLnN0YXJ0ID49IG5vZGUuZW5kO1xufVxuXG5leHBvcnQgZnVuY3Rpb24gZmluZElkZW50aWZpZXJBdChhc3QsIHBvcykge1xuICAgICd1c2Ugc3RyaWN0JztcbiAgICByZXR1cm4gZmluZE5vZGVBdChhc3QsIHBvcyxcbiAgICAgICAgICAgIG5vZGUgPT4gbm9kZS50eXBlID09PSAnSWRlbnRpZmllcicgJiYgIWlzRHVtbXlJZE5vZGUobm9kZSlcbiAgICApO1xufVxuXG5leHBvcnQgZnVuY3Rpb24gZmluZE1lbWJlck9yVmFyaWFibGVBdChhc3QsIHBvcykge1xuICAgICd1c2Ugc3RyaWN0JztcbiAgICByZXR1cm4gZmluZE5vZGVBdChhc3QsIHBvcyxcbiAgICAgICAgICAgIG5vZGUgPT4ge1xuICAgICAgICAgICAgICAgIHJldHVybiAobm9kZS50eXBlID09PSAnSWRlbnRpZmllcicgJiYgIWlzRHVtbXlJZE5vZGUobm9kZSkpIHx8XG4gICAgICAgICAgICAgICAgICAgIChub2RlLnR5cGUgPT09ICdNZW1iZXJFeHByZXNzaW9uJyAmJlxuICAgICAgICAgICAgICAgICAgICAoXG4gICAgICAgICAgICAgICAgICAgICAgICAobm9kZS5wcm9wZXJ0eS5zdGFydCA8PSBwb3MgJiYgcG9zIDw9IG5vZGUucHJvcGVydHkuZW5kKSB8fFxuICAgICAgICAgICAgICAgICAgICAgICAgLy8gd2hlbiBwcm9wIGlzIOKcllxuICAgICAgICAgICAgICAgICAgICAgICAgKG5vZGUucHJvcGVydHkuZW5kIDw9IHBvcyAmJiBwb3MgPD0gbm9kZS5wcm9wZXJ0eS5zdGFydClcbiAgICAgICAgICAgICAgICAgICAgKSk7XG4gICAgICAgICAgICB9XG4gICAgKTtcbn1cblxuZXhwb3J0IGZ1bmN0aW9uIGZpbmRDb21wbGV0aW9uQ29udGV4dChhc3QsIHBvcykge1xuICAgICd1c2Ugc3RyaWN0JztcbiAgICAvLyBmaW5kIHRoZSBub2RlXG4gICAgY29uc3Qgd2Fsa2VyID0gd3JhcFdhbGtlcih2YXJXYWxrZXIsXG4gICAgICAgIChub2RlLCB2YikgPT4ge1xuICAgICAgICAgICAgaWYgKG5vZGUuc3RhcnQgPiBwb3MgfHwgbm9kZS5lbmQgPCBwb3MpIHtcbiAgICAgICAgICAgICAgICByZXR1cm4gZmFsc2U7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICAvLyBhdCBpZGVudGlmaWVyP1xuICAgICAgICAgICAgaWYgKG5vZGUudHlwZSA9PT0gJ0lkZW50aWZpZXInKSB7XG4gICAgICAgICAgICAgICAgdGhyb3cgbmV3IEZvdW5kKHt0eXBlOiAnSWRlbnRpZmllcicsIG5vZGU6IG5vZGUsIHZiOiB2Yn0pO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgLy8gYXQgbWVtYmVyIGV4cHJlc3Npb24/XG4gICAgICAgICAgICBpZiAobm9kZS50eXBlID09PSAnTWVtYmVyRXhwcmVzc2lvbicgJiZcbiAgICAgICAgICAgICAgICAoXG4gICAgICAgICAgICAgICAgICAgIChub2RlLnByb3BlcnR5LnN0YXJ0IDw9IHBvcyAmJiBwb3MgPD0gbm9kZS5wcm9wZXJ0eS5lbmQpIHx8XG4gICAgICAgICAgICAgICAgICAgICAgICAvLyB3aGVuIHByb3AgaXMg4pyWXG4gICAgICAgICAgICAgICAgICAgIChub2RlLnByb3BlcnR5LmVuZCA8PSBwb3MgJiYgcG9zIDw9IG5vZGUucHJvcGVydHkuc3RhcnQpXG4gICAgICAgICAgICAgICAgKVxuICAgICAgICAgICAgKSB7XG4gICAgICAgICAgICAgICAgLy8gYXQgdXN1YWwgcHJvcD8gKGFmdGVyIGRvdClcbiAgICAgICAgICAgICAgICBpZiAoIW5vZGUuY29tcHV0ZWQpIHtcbiAgICAgICAgICAgICAgICAgICAgdGhyb3cgbmV3IEZvdW5kKHt0eXBlOiAndXN1YWxQcm9wJywgbm9kZTogbm9kZSwgdmI6IHZifSk7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIC8vIGF0IG9ialsnJ10gcGF0dGVybj9cbiAgICAgICAgICAgICAgICBpZiAobm9kZS5jb21wdXRlZCAmJlxuICAgICAgICAgICAgICAgICAgICB0eXBlb2Ygbm9kZS5wcm9wZXJ0eS52YWx1ZSA9PT0gJ3N0cmluZycpIHtcbiAgICAgICAgICAgICAgICAgICAgdGhyb3cgbmV3IEZvdW5kKHt0eXBlOiAnc3RyaW5nUHJvcCcsIG5vZGU6IG5vZGUsIHZiOiB2Yn0pO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIHJldHVybiB0cnVlO1xuICAgICAgICB9LFxuICAgICAgICAobm9kZSwgdmIpID0+IHtcbiAgICAgICAgICAgIC8vIG5vIElkZW50aWZpZXIgb3IgTWVtYmVyIEV4cHJlc3Npb24gd2FzIGZvdW5kXG4gICAgICAgICAgICB0aHJvdyBuZXcgRm91bmQoe3R5cGU6ICdJZGVudGlmaWVyJywgbm9kZTogbnVsbCwgdmI6IHZifSk7XG4gICAgICAgIH0pO1xuXG4gICAgdHJ5IHtcbiAgICAgICAgd2Fsay5yZWN1cnNpdmUoYXN0LCBhc3RbJ0BibG9jayddLCB3YWxrZXIpO1xuICAgIH0gY2F0Y2ggKGUpIHtcbiAgICAgICAgaWYgKGUgaW5zdGFuY2VvZiBGb3VuZCkge1xuICAgICAgICAgICAgcmV0dXJuIGUuaW5mbztcbiAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICAgIHRocm93IGU7XG4gICAgICAgIH1cbiAgICB9XG59XG5cblxuLyoqXG4gKiBGaW5kIGEgbm9kZSBhdCBwb3MuXG4gKiBJZiBmb3VuZCwgaXQgYWxzbyByZXR1cm5zIGl0cyB2YXJCbG9jay5cbiAqIElmIG5vdCBmb3VuZCwgcmV0dXJuIG51bGwuXG4gKiBAcGFyYW0gYXN0IC0gQVNUIG5vZGVcbiAqIEBwYXJhbSBwb3MgLSBpbmRleCBwb3NpdGlvblxuICogQHBhcmFtIG5vZGVUZXN0IC0gQ2hlY2sgd2hldGhlciB0aGUgbm9kZSBpcyB3aGF0IHdlIGFyZSBsb29raW5nIGZvclxuICogQHJldHVybnMgeyp9XG4gKi9cbmZ1bmN0aW9uIGZpbmROb2RlQXQoYXN0LCBwb3MsIG5vZGVUZXN0KSB7XG4gICAgJ3VzZSBzdHJpY3QnO1xuICAgIC8vIGZpbmQgdGhlIG5vZGVcbiAgICBjb25zdCB3YWxrZXIgPSB3cmFwV2Fsa2VyKHZhcldhbGtlcixcbiAgICAgICAgKG5vZGUsIHZiKSA9PiB7XG4gICAgICAgICAgICBpZiAobm9kZS5zdGFydCA+IHBvcyB8fCBub2RlLmVuZCA8IHBvcykge1xuICAgICAgICAgICAgICAgIHJldHVybiBmYWxzZTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGlmIChub2RlVGVzdChub2RlKSkge1xuICAgICAgICAgICAgICAgIHRocm93IG5ldyBGb3VuZCh7bm9kZTogbm9kZSwgdmI6IHZifSk7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICByZXR1cm4gdHJ1ZTtcbiAgICAgICAgfSk7XG5cbiAgICB0cnkge1xuICAgICAgICB3YWxrLnJlY3Vyc2l2ZShhc3QsIGFzdFsnQGJsb2NrJ10sIHdhbGtlcik7XG4gICAgfSBjYXRjaCAoZSkge1xuICAgICAgICBpZiAoZSBpbnN0YW5jZW9mIEZvdW5kKSB7XG4gICAgICAgICAgICByZXR1cm4gZS5pbmZvO1xuICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgICAgdGhyb3cgZTtcbiAgICAgICAgfVxuICAgIH1cbiAgICAvLyBpZGVudGlmaWVyIG5vdCBmb3VuZFxuICAgIHJldHVybiBudWxsO1xufVxuXG4vKipcbiAqIEZpbmQgdGhlIHNtYWxsZXN0IG5vZGUgdGhhdCBjb250YWlucyB0aGUgcmFuZ2UgZnJvbSBzdGFydCB0byBlbmQuXG4gKiBOb3RlIHRoYXQgd2UgY2FuIGZpbmQgdGhlIG5vZGUgYXQgdGhlIHBvc3ROb2RlIGluc3RlYWQgb2YgcHJlTm9kZS5cbiAqIEBwYXJhbSBhc3RcbiAqIEBwYXJhbSBzdGFydFxuICogQHBhcmFtIGVuZFxuICogQHJldHVybnMgeyp9XG4gKi9cbmV4cG9ydCBmdW5jdGlvbiBmaW5kU3Vycm91bmRpbmdOb2RlKGFzdCwgc3RhcnQsIGVuZCkge1xuICAgICd1c2Ugc3RyaWN0JztcblxuICAgIGNvbnN0IHdhbGtlciA9IHdyYXBXYWxrZXIodmFyV2Fsa2VyLFxuICAgICAgICBub2RlID0+IG5vZGUuc3RhcnQgPD0gc3RhcnQgJiYgZW5kIDw9IG5vZGUuZW5kLFxuICAgICAgICBub2RlID0+IHsgdGhyb3cgbmV3IEZvdW5kKG5vZGUpOyB9XG4gICAgKTtcblxuICAgIHRyeSB7XG4gICAgICAgIHdhbGsucmVjdXJzaXZlKGFzdCwgdW5kZWZpbmVkLCB3YWxrZXIpO1xuICAgIH0gY2F0Y2ggKGUpIHtcbiAgICAgICAgaWYgKGUgaW5zdGFuY2VvZiBGb3VuZCkge1xuICAgICAgICAgICAgcmV0dXJuIGUuaW5mbztcbiAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICAgIHRocm93IGU7XG4gICAgICAgIH1cbiAgICB9XG4gICAgLy8gbm9kZSBub3QgZm91bmRcbiAgICByZXR1cm4gbnVsbDtcbn1cblxuZXhwb3J0IGZ1bmN0aW9uIHJlY3Vyc2l2ZVdpdGhSZXR1cm4obm9kZSwgc3RhdGUsIHZpc2l0b3IpIHtcbiAgICBmdW5jdGlvbiBjKG5vZGUsIHN0LCBvdmVycmlkZSkge1xuICAgICAgICByZXR1cm4gdmlzaXRvcltvdmVycmlkZSB8fCBub2RlLnR5cGVdKG5vZGUsIHN0LCBjKTtcbiAgICB9XG4gICAgcmV0dXJuIGMobm9kZSwgc3RhdGUpO1xufVxuIiwiLypcbiBKYXZhU2NyaXB064qUIGdsb2JhbCwgZnVuY3Rpb24gYmxvY2ssIGNhdGNoIGJsb2Nr7JeQIOuzgOyImOqwgCDri6zrprDri6QuXG4gRVM264qUIOydvOuwmCBibG9ja+yXkOuPhCDri6zrprDri6QuXG5cbiBWYXJCbG9ja+uKlCDqsIEgYmxvY2vsl5Ag64us66awIOuzgOyImOuTpOydhCDrgpjtg4Drgrjri6QuXG4gLSBwYXJlbiAgICAgIDogQmxvY2tWYXJzLCDrsJTquaUgYmxvY2vsnYQg64KY7YOA64K064qUIOqwneyytFxuIC0gb3JpZ2luTGFiZWw6IG51bWJlciwg7ZW064u5IEJsb2NrVmFyc+qwgCDshKDslrjrkJwgQVNUIG5vZGXsnZggQGxhYmVsXG4gICAgb3JpZ2lu7J20IOuQoCDsiJgg7J6I64qUIG5vZGXripRcbiAgICBGdW5jdGlvbi5ib2R5LCBDYXRjaENsYXVzZS5ibG9jayDrkZDqsIDsp4Dri6QuXG4gICAg65GQ6rCA7KeAIOuqqOuRkCBCbG9ja1N0YXRlbWVudOydtOuLpC5cbiAtIGlzQ2F0Y2ggICAgOiBib29sZWFuLFxuICAgKiB0cnVlICAtPiBjYXRjaCBibG9ja1xuICAgKiBmYWxzZSAtPiBmdW5jdGlvbiBibG9jaywgb3IgZ2xvYmFsXG5cbiAtIHBhcmFtVmFyTmFtZXMgOiDrp6TqsJzrs4DsiJgg7J2066aEIOuqqeuhnSwg66ek6rCcIOuzgOyImCDsiJzshJzrjIDroZxcbiAtIGxvY2FsVmFyTmFtZXMgOiDsp4Dsl60g67OA7IiYIOydtOumhCDrqqnroZ0sIOyInOyEnCDrrLTsnZjrr7hcbiAgICBhcmd1bWVudHPrpbwg7IKs7Jqp7ZWY64qUIOqyveyasCBsb2NhbFZhck5hbWVz7JeQIOuTseyepe2VmOqzoCxcbiAgICBhcmd1bWVudHMgb2JqZWN066W8IOyCrOyaqe2VmOuptCB1c2VBcmd1bWVudHNPYmplY3QgPT0gdHJ1ZVxuXG4gLSAob3B0aW9uYWwpIHVzZUFyZ3VtZW50c09iamVjdDogYm9vbGVhblxuICAgIO2VqOyImCBib2R5IGJsb2Nr7J24IOqyveyasOyXkOunjCDsgqzsmqkg6rCA64qlXG4gICAgKiB0cnVlICA6IGFyZ3VtZW50cyBvYmplY3TqsIAg7IKs7Jqp65CY7JeI64ukLlxuICAgICAg7KaJIO2VqOyImCBib2R57JeQ7IScIOuzgOyImCBhcmd1bWVudHPrpbwg7ISg7Ja4IOyXhuydtCDsgqzsmqntlojri6QuXG4gICAgICDsnbQg6rK97JqwLCBhcmd1bWVudHPripQg7ZWo7IiY7J2YIOyngOyXrSDrs4DsiJjroZwg65Ox66Gd65Cc64ukLlxuICAgICogZmFsc2Ug7J24IOqyveyasOuKlCDsl4bri6QuIOq3uOuftOqxsOuptCDslYTsmIgg67OA7IiYIOyekOyytOqwgCDsl4bri6QuXG5cbiAtIHVzZWRWYXJpYWJsZXMgOiDqsIEgYmxvY2vsnZgg66ek6rCc67OA7IiYLCDsp4Dsl63rs4DsiJgg7KSRXG4gICDsgqzsmqnrkJjripQg7JyE7LmY6rCAIOyeiOuKlCDqsoPrk6TsnZgg66qp66GdXG5cbiAtIGluc3RhbmNlcyA6IERlbHRhIC0+IFZhckJsb2Nr7J2YIOuzgOyImOuTpCAtPiBBVmFsXG4gICBnZXRJbnN0YW5jZShkZWx0YSkg66W8IO2Gte2VtCDqsJnsnYAgZGVsdGHripQg6rCZ7J2AIG1hcHBpbmcg7KO86rKMIOunjOuTrFxuXG4gLSBzY29wZUluc3RhbmNlcyA6IFtTY29wZV1cbiAgIO2YhOyerCBWYXJCbG9ja+ydhCDrp4jsp4Drp4nsnLzroZwg7ZWY64qUIFNjb3Bl66W8IOuqqOuRkCDrqqjsnYDri6QuXG4gICBnZXRTY29wZUluc3RhbmNlKGRlbHRhLCBwYXJlbikg7J2EIO2Gte2VtCDqsJnsnYAgc2NvcGUgY2hhaW7snYBcbiAgIOqwmeydgCDqsJ3ssrTqsIAg65CY64+E66GdIOunjOuToOuLpC5cbiovXG4ndXNlIHN0cmljdCc7XG5cbmltcG9ydCAqIGFzIHR5cGVzIGZyb20gJy4vZG9tYWlucy90eXBlcydcbmltcG9ydCAqIGFzIG15V2Fsa2VyIGZyb20gJy4vdXRpbC9teVdhbGtlcidcbmNvbnN0IHdhbGsgPSByZXF1aXJlKCdhY29ybi9kaXN0L3dhbGsnKTtcblxuZXhwb3J0IGNsYXNzIFZhckJsb2NrIHtcbiAgICBjb25zdHJ1Y3RvcihwYXJlbiwgb3JpZ2luTm9kZSwgYlR5cGUsIGlzU3RyaWN0KSB7XG4gICAgICAgIHRoaXMucGFyZW4gPSBwYXJlbjtcbiAgICAgICAgdGhpcy5vcmlnaW5Ob2RlID0gb3JpZ2luTm9kZTtcbiAgICAgICAgdGhpcy5ibG9ja1R5cGUgPSBiVHlwZTtcbiAgICAgICAgdGhpcy5pc1N0cmljdCA9IGlzU3RyaWN0O1xuXG4gICAgICAgIHRoaXMub3JpZ2luTGFiZWwgPSBvcmlnaW5Ob2RlWydAbGFiZWwnXTtcbiAgICAgICAgdGhpcy5wYXJhbVZhck5hbWVzID0gW107XG4gICAgICAgIHRoaXMubG9jYWxWYXJOYW1lcyA9IFtdO1xuXG4gICAgICAgIHRoaXMudXNlZFZhcmlhYmxlcyA9IFtdO1xuICAgICAgICAvLyB0aGlzLnVzZUFyZ3VtZW50c09iamVjdFxuICAgICAgICB0aGlzLmluc3RhbmNlcyA9IG5ldyBNYXAoKTtcbiAgICAgICAgdGhpcy5zY29wZUluc3RhbmNlcyA9IFtdO1xuICAgIH1cblxuICAgIGlzR2xvYmFsKCkge1xuICAgICAgICByZXR1cm4gdGhpcy5ibG9ja1R5cGUgPT09IFZhckJsb2NrLmJsb2NrVHlwZXMuZ2xvYmFsQmxvY2s7XG4gICAgfVxuXG4gICAgaXNPbGRGdW5jdGlvbkJsb2NrKCkge1xuICAgICAgICByZXR1cm4gdGhpcy5ibG9ja1R5cGUgPT09IFZhckJsb2NrLmJsb2NrVHlwZXMub2xkRnVuY3Rpb25CbG9jaztcbiAgICB9XG5cbiAgICBpc0Fycm93RnVuY3Rpb25CbG9jaygpIHtcbiAgICAgICAgcmV0dXJuIHRoaXMuYmxvY2tUeXBlID09PSBWYXJCbG9jay5ibG9ja1R5cGVzLmFycm93RnVuY3Rpb25CbG9jaztcbiAgICB9XG5cbiAgICBpc0NhdGNoQmxvY2soKSB7XG4gICAgICAgIHJldHVybiB0aGlzLmJsb2NrVHlwZSA9PT0gVmFyQmxvY2suYmxvY2tUeXBlcy5jYXRjaEJsb2NrO1xuICAgIH1cblxuICAgIGlzTm9ybWFsQmxvY2soKSB7XG4gICAgICAgIHJldHVybiB0aGlzLmJsb2NrVHlwZSA9PT0gVmFyQmxvY2suYmxvY2tUeXBlcy5ub3JtYWxCbG9jaztcbiAgICB9XG5cbiAgICBpc1BhcmFtZXRlckJsb2NrKCkge1xuICAgICAgICByZXR1cm4gdGhpcy5ibG9ja1R5cGUgPT09IFZhckJsb2NrLmJsb2NrVHlwZXMucGFyYW1ldGVyQmxvY2s7XG4gICAgfVxuXG4gICAgZ2V0TG9jYWxWYXJOYW1lcygpIHtcbiAgICAgICAgcmV0dXJuIHRoaXMubG9jYWxWYXJOYW1lcztcbiAgICB9XG5cbiAgICBnZXRQYXJhbVZhck5hbWVzKCkge1xuICAgICAgICByZXR1cm4gdGhpcy5wYXJhbVZhck5hbWVzO1xuICAgIH1cblxuICAgIGdldFZhck5hbWVzKCkge1xuICAgICAgICByZXR1cm4gdGhpcy5nZXRMb2NhbFZhck5hbWVzKCkuY29uY2F0KHRoaXMuZ2V0UGFyYW1WYXJOYW1lcygpKTtcbiAgICB9XG5cbiAgICBoYXNMb2NhbFZhcih2YXJOYW1lKSB7XG4gICAgICAgIHJldHVybiB0aGlzLmxvY2FsVmFyTmFtZXMgJiYgdGhpcy5sb2NhbFZhck5hbWVzLmluZGV4T2YodmFyTmFtZSkgPiAtMTtcbiAgICB9XG5cbiAgICBoYXNQYXJhbVZhcih2YXJOYW1lKSB7XG4gICAgICAgIHJldHVybiB0aGlzLnBhcmFtVmFyTmFtZXMuaW5kZXhPZih2YXJOYW1lKSA+IC0xO1xuICAgIH1cblxuICAgIGhhc1Zhcih2YXJOYW1lKSB7XG4gICAgICAgIHJldHVybiB0aGlzLmhhc1BhcmFtVmFyKHZhck5hbWUpIHx8IHRoaXMuaGFzTG9jYWxWYXIodmFyTmFtZSk7XG4gICAgfVxuXG4gICAgYWRkRGVjbGFyZWRMb2NhbFZhcih2YXJOYW1lLCBkVHlwZSkge1xuICAgICAgICBsZXQgY3VyckJsb2NrID0gdGhpcztcbiAgICAgICAgc3dpdGNoKGRUeXBlKSB7XG4gICAgICAgICAgICBjYXNlIFZhckJsb2NrLmRlY2xhcmF0aW9uVHlwZXMudmFyRGVjbGFyYXRpb246XG4gICAgICAgICAgICAgICAgLy8gR28gdXAgdW50aWwgZnVuY3Rpb24gb3IgZ2xvYmFsXG4gICAgICAgICAgICAgICAgd2hpbGUgKCFjdXJyQmxvY2suaXNPbGRGdW5jdGlvbkJsb2NrKClcbiAgICAgICAgICAgICAgICAgICAgJiYgIWN1cnJCbG9jay5pc0Fycm93RnVuY3Rpb25CbG9jaygpXG4gICAgICAgICAgICAgICAgICAgICYmICFjdXJyQmxvY2suaXNHbG9iYWwoKSkge1xuICAgICAgICAgICAgICAgICAgICBjdXJyQmxvY2sgPSBjdXJyQmxvY2sucGFyZW47XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIGJyZWFrO1xuICAgICAgICAgICAgY2FzZSBWYXJCbG9jay5kZWNsYXJhdGlvblR5cGVzLmZ1bmN0aW9uRGVjbGFyYXRpb246XG4gICAgICAgICAgICAgICAgLy8gR28gdXAgdW50aWwgZnVuY3Rpb24gb3IgZ2xvYmFsXG4gICAgICAgICAgICAgICAgLy8gb3IgY2F0Y2ggYmxvY2sgaGF2aW5nIHZhck5hbWUgYXMgaXRzIHBhcmFtZXRlclxuICAgICAgICAgICAgICAgIHdoaWxlIChjdXJyQmxvY2suaXNOb3JtYWxCbG9jaygpICYmXG4gICAgICAgICAgICAgICAgICAgICAgICEoY3VyckJsb2NrLmlzQ2F0Y2hCbG9jaygpICYmIGN1cnJCbG9jay5oYXNQYXJhbVZhcih2YXJOYW1lKSkpIHtcbiAgICAgICAgICAgICAgICAgICAgY3VyckJsb2NrID0gY3VyckJsb2NrLnBhcmVuO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICBicmVhaztcbiAgICAgICAgICAgIGNhc2UgVmFyQmxvY2suZGVjbGFyYXRpb25UeXBlcy5sZXREZWNsYXJhdGlvbjpcbiAgICAgICAgICAgIGNhc2UgVmFyQmxvY2suZGVjbGFyYXRpb25UeXBlcy5jb25zdERlY2xhcmF0aW9uOlxuICAgICAgICAgICAgICAgIGJyZWFrO1xuICAgICAgICAgICAgY2FzZSBWYXJCbG9jay5kZWNsYXJhdGlvblR5cGVzLmltcGxpY2l0R2xvYmFsRGVjbGFyYXRpb246XG4gICAgICAgICAgICAgICAgLy8gbm90IGdsb2JhbCBvciBzdHJpY3QgPT4gZG8gbm90IGFkZCB0aGUgdmFyaWFibGVcbiAgICAgICAgICAgICAgICBpZiAoIXRoaXMuaXNHbG9iYWwoKSB8fCB0aGlzLmlzU3RyaWN0KSB7XG4gICAgICAgICAgICAgICAgICAgIHJldHVybiBudWxsO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICBicmVhaztcbiAgICAgICAgfVxuXG4gICAgICAgIC8vIGlmIGFscmVhZHkgYWRkZWQsIGRvIG5vdCBhZGRcbiAgICAgICAgaWYgKCFjdXJyQmxvY2suaGFzVmFyKHZhck5hbWUpKSB7XG4gICAgICAgICAgICBjdXJyQmxvY2subG9jYWxWYXJOYW1lcy5wdXNoKHZhck5hbWUpO1xuICAgICAgICB9XG4gICAgICAgIC8vIHJldHVybnMgdGhlIGJsb2NrIG9iamVjdCB0aGF0IGNvbnRhaW5zIHRoZSB2YXJpYWJsZVxuICAgICAgICByZXR1cm4gY3VyckJsb2NrO1xuICAgIH1cblxuICAgIGFkZFBhcmFtVmFyKHZhck5hbWUpIHtcbiAgICAgICAgdGhpcy5wYXJhbVZhck5hbWVzLnB1c2godmFyTmFtZSk7XG4gICAgfVxuXG4gICAgZmluZFZhckluQ2hhaW4odmFyTmFtZSkge1xuICAgICAgICBsZXQgY3VyckJsb2NrID0gdGhpcztcbiAgICAgICAgd2hpbGUgKGN1cnJCbG9jayAmJiAhY3VyckJsb2NrLmhhc1Zhcih2YXJOYW1lKSkge1xuICAgICAgICAgICAgaWYgKGN1cnJCbG9jay5pc0dsb2JhbCgpICYmICFjdXJyQmxvY2suaXNTdHJpY3QpIHtcbiAgICAgICAgICAgICAgICBicmVhaztcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGN1cnJCbG9jayA9IGN1cnJCbG9jay5wYXJlbjtcbiAgICAgICAgfVxuICAgICAgICAvLyBpZiBub3QgZm91bmRcbiAgICAgICAgLy8gMSkgZ2xvYmFsICd1c2Ugc3RyaWN0JyA9PiByZXR1cm5zIG51bGxcbiAgICAgICAgLy8gMikgb3RoZXJ3aXNlID0+IHJldHVybnMgdGhlIGdsb2JhbFxuICAgICAgICByZXR1cm4gY3VyckJsb2NrO1xuICAgIH1cblxuICAgIGdldFZhck5hbWVzSW5DaGFpbigpIHtcbiAgICAgICAgbGV0IGN1cnJCbG9jayA9IHRoaXM7XG4gICAgICAgIGNvbnN0IHZhck5hbWVzID0gW107XG4gICAgICAgIHdoaWxlIChjdXJyQmxvY2spIHtcbiAgICAgICAgICAgIGN1cnJCbG9jay5nZXRWYXJOYW1lcygpLmZvckVhY2goZnVuY3Rpb24gKG5hbWUpIHtcbiAgICAgICAgICAgICAgICBpZiAodmFyTmFtZXMuaW5kZXhPZihuYW1lKSA9PT0gLTEpIHtcbiAgICAgICAgICAgICAgICAgICAgdmFyTmFtZXMucHVzaChuYW1lKTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICB9KTtcbiAgICAgICAgICAgIGN1cnJCbG9jayA9IGN1cnJCbG9jay5wYXJlbjtcbiAgICAgICAgfVxuICAgICAgICByZXR1cm4gdmFyTmFtZXM7XG4gICAgfVxuXG4gICAgYWRkVXNlZFZhcih2YXJOYW1lKSB7XG4gICAgICAgIGlmICh0aGlzLnVzZWRWYXJpYWJsZXMuaW5kZXhPZih2YXJOYW1lKSA9PT0gLTEpIHtcbiAgICAgICAgICAgIHRoaXMudXNlZFZhcmlhYmxlcy5wdXNoKHZhck5hbWUpO1xuICAgICAgICB9XG4gICAgfVxuXG4gICAgZ2V0VXNlZFZhck5hbWVzKCkge1xuICAgICAgICByZXR1cm4gdGhpcy51c2VkVmFyaWFibGVzO1xuICAgIH1cblxuICAgIGlzVXNlZFZhcih2YXJOYW1lKSB7XG4gICAgICAgIHJldHVybiB0aGlzLnVzZWRWYXJpYWJsZXMuaW5kZXhPZih2YXJOYW1lKSA+IC0xO1xuICAgIH1cblxuICAgIC8vIHJldHVybnMgYSBtYXBwaW5nXG4gICAgZ2V0SW5zdGFuY2UoZGVsdGEpIHtcbiAgICAgICAgaWYgKHRoaXMuaW5zdGFuY2VzLmhhcyhkZWx0YSkpIHtcbiAgICAgICAgICAgIHJldHVybiB0aGlzLmluc3RhbmNlcy5nZXQoZGVsdGEpO1xuICAgICAgICB9XG4gICAgICAgIC8vIGNvbnN0cnVjdCBWYXJNYXBcbiAgICAgICAgY29uc3QgdmFyTWFwID0gbmV3IE1hcCgpO1xuICAgICAgICBjb25zdCB2YXJOYW1lcyA9IHRoaXMuZ2V0UGFyYW1WYXJOYW1lcygpLmNvbmNhdCh0aGlzLmdldExvY2FsVmFyTmFtZXMoKSk7XG5cbiAgICAgICAgZm9yIChsZXQgaSA9IDA7IGkgPCB2YXJOYW1lcy5sZW5ndGg7IGkrKykge1xuICAgICAgICAgICAgdmFyTWFwLnNldCh2YXJOYW1lc1tpXSwgbmV3IHR5cGVzLkFWYWwoKSk7XG4gICAgICAgIH1cbiAgICAgICAgLy8gcmVtZW1iZXIgdGhlIGluc3RhbmNlXG4gICAgICAgIHRoaXMuaW5zdGFuY2VzLnNldChkZWx0YSx2YXJNYXApO1xuICAgICAgICByZXR1cm4gdmFyTWFwO1xuICAgIH1cblxuICAgIC8vIHJldHVybnMgYW4gYXJyYXlcbiAgICBnZXRQYXJhbUFWYWxzKGRlbHRhKSB7XG4gICAgICAgIGNvbnN0IGluc3RhbmNlID0gdGhpcy5nZXRJbnN0YW5jZShkZWx0YSk7XG4gICAgICAgIGNvbnN0IHBhcmFtcyA9IFtdO1xuICAgICAgICB0aGlzLmdldFBhcmFtVmFyTmFtZXMoKS5mb3JFYWNoKG5hbWUgPT4ge1xuICAgICAgICAgICAgcGFyYW1zLnB1c2goaW5zdGFuY2UuZ2V0KG5hbWUpKTtcbiAgICAgICAgfSk7XG4gICAgICAgIHJldHVybiBwYXJhbXM7XG4gICAgfVxuXG4gICAgLy8gcmV0dXJucyBhbiBBVmFsXG4gICAgZ2V0QXJndW1lbnRzQVZhbChkZWx0YSkge1xuICAgICAgICBpZiAoIXRoaXMudXNlQXJndW1lbnRzT2JqZWN0KSB7XG4gICAgICAgICAgICB0aHJvdyBuZXcgRXJyb3IoJ05vdCBmb3IgdGhpcyBWYXJCbG9jaycpO1xuICAgICAgICB9XG4gICAgICAgIHJldHVybiB0aGlzLmdldEluc3RhbmNlKGRlbHRhKS5nZXQoJ2FyZ3VtZW50cycpO1xuICAgIH1cblxuICAgIC8vIGdldCBhIFNjb3BlIGluc3RhbmNlXG4gICAgZ2V0U2NvcGVJbnN0YW5jZShwYXJlbiwgZGVsdGEpIHtcbiAgICAgICAgY29uc3QgdmFyTWFwID0gdGhpcy5nZXRJbnN0YW5jZShkZWx0YSk7XG4gICAgICAgIGxldCBmb3VuZCA9IG51bGw7XG5cbiAgICAgICAgdGhpcy5zY29wZUluc3RhbmNlcy5mb3JFYWNoKGZ1bmN0aW9uIChzYykge1xuICAgICAgICAgICAgaWYgKHNjLnBhcmVuID09PSBwYXJlbiAmJiBzYy52YXJNYXAgPT09IHZhck1hcCkgZm91bmQgPSBzYztcbiAgICAgICAgfSk7XG5cbiAgICAgICAgaWYgKGZvdW5kKSB7XG4gICAgICAgICAgICByZXR1cm4gZm91bmQ7XG4gICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgICBsZXQgbmV3U2NvcGVJbnN0YW5jZSA9IG5ldyBTY29wZShwYXJlbiwgdmFyTWFwLCB0aGlzKTtcbiAgICAgICAgICAgIHRoaXMuc2NvcGVJbnN0YW5jZXMucHVzaChuZXdTY29wZUluc3RhbmNlKTtcbiAgICAgICAgICAgIHJldHVybiBuZXdTY29wZUluc3RhbmNlO1xuICAgICAgICB9XG4gICAgfVxuXG4gICAgLy8gZ2V0IGZ1bmN0aW9uJ3Mgc2NvcGUgaW5zdGFuY2VzXG4gICAgZ2V0U2NvcGVXaXRoUGFyZW50KHBTY29wZSkge1xuICAgICAgICBjb25zdCBpbnN0YW5jZXMgPSBuZXcgU2V0KCk7XG4gICAgICAgIHRoaXMuc2NvcGVJbnN0YW5jZXMuZm9yRWFjaChzYyA9PiB7XG4gICAgICAgICAgICBpZiAoc2MucGFyZW4gPT09IHBTY29wZSkgaW5zdGFuY2VzLmFkZChzYyk7XG4gICAgICAgIH0pO1xuICAgICAgICByZXR1cm4gaW5zdGFuY2VzO1xuICAgIH1cbn1cblxuVmFyQmxvY2suYmxvY2tUeXBlcyA9IHtcbiAgICBnbG9iYWxCbG9jazogU3ltYm9sKCdnbG9iYWwnKSxcbiAgICBvbGRGdW5jdGlvbkJsb2NrOiBTeW1ib2woJ29sZEZ1bmN0aW9uJyksXG4gICAgYXJyb3dGdW5jdGlvbkJsb2NrOiBTeW1ib2woJ2Fycm93RnVuY3Rpb24nKSxcbiAgICBwYXJhbWV0ZXJCbG9jazogU3ltYm9sKCdwYXJhbWV0ZXInKSwgIC8vIHRob3VnaCBub3QgcmVhbGx5IGluIGJyYWNlc1xuICAgIGNhdGNoQmxvY2s6IFN5bWJvbCgnY2F0Y2gnKSxcbiAgICBub3JtYWxCbG9jazogU3ltYm9sKCdub3JtYWwnKVxufTtcblxuVmFyQmxvY2suZGVjbGFyYXRpb25UeXBlcyA9IHtcbiAgICBsZXREZWNsYXJhdGlvbjogU3ltYm9sKCdsZXQnKSxcbiAgICBjb25zdERlY2xhcmF0aW9uOiBTeW1ib2woJ2NvbnN0JyksXG4gICAgdmFyRGVjbGFyYXRpb246IFN5bWJvbCgndmFyJyksXG4gICAgZnVuY3Rpb25EZWNsYXJhdGlvbjogU3ltYm9sKCdmdW5jdGlvbicpLFxuICAgIHBhcmFtZXRlckRlY2xhcmF0aW9uOiBTeW1ib2woJ3BhcmFtZXRlcicpLFxuICAgIGltcGxpY2l0R2xvYmFsRGVjbGFyYXRpb246IFN5bWJvbCgnaW1wbGljaXQgZ2xvYmFsJylcbn07XG5cbi8qKlxuICogQ2hlY2sgd2hldGhlciB0aGUgc3RtdCBpcyB0aGUgZGlyZWN0aXZlIGZvciBzdHJpY3RuZXNzLlxuICogVGFrZW4gZnJvbSBhY29yblxuICogQHBhcmFtIHN0bXQgLSB0aGUgZmlyc3Qgc3RhdGVtZW50IG9mIGEgYm9keVxuICogQHJldHVybnMge2Jvb2xlYW59XG4gKi9cbmZ1bmN0aW9uIGlzVXNlU3RyaWN0KHN0bXQpIHtcbiAgICByZXR1cm4gc3RtdC50eXBlID09PSAnRXhwcmVzc2lvblN0YXRlbWVudCcgJiZcbiAgICAgICAgc3RtdC5leHByZXNzaW9uLnR5cGUgPT09ICdMaXRlcmFsJyAmJlxuICAgICAgICBzdG10LmV4cHJlc3Npb24ucmF3LnNsaWNlKDEsIC0xKSA9PT0gJ3VzZSBzdHJpY3QnO1xufVxuXG5cbmNvbnN0IGRlY2xhcmVkVmFyaWFibGVGaW5kZXIgPSB3YWxrLm1ha2Uoe1xuICAgIFZhcmlhYmxlUGF0dGVybjogKG5vZGUsIFtkVHlwZSwgY3VyckJsb2NrXSwgYykgPT4ge1xuICAgICAgICBpZiAoZFR5cGUgPT09IFZhckJsb2NrLmRlY2xhcmF0aW9uVHlwZXMucGFyYW1ldGVyRGVjbGFyYXRpb24pIHtcbiAgICAgICAgICAgIGN1cnJCbG9jay5hZGRQYXJhbVZhcihub2RlLm5hbWUpO1xuICAgICAgICB9IGVsc2UgaWYgKGRUeXBlKSB7XG4gICAgICAgICAgICBjdXJyQmxvY2suYWRkRGVjbGFyZWRMb2NhbFZhcihub2RlLm5hbWUsIGRUeXBlKTtcbiAgICAgICAgfVxuICAgIH0sXG4gICAgRnVuY3Rpb246IChub2RlLCBbZFR5cGUsIGN1cnJCbG9ja10sIGMpID0+IHtcbiAgICAgICAgbGV0IHBhcmVuQmxvY2sgPSBjdXJyQmxvY2ssIHBhcmFtQmxvY2s7XG4gICAgICAgIGlmIChub2RlLmlkKSB7XG4gICAgICAgICAgICBjb25zdCBmdW5jTmFtZSA9IG5vZGUuaWQubmFtZTtcbiAgICAgICAgICAgIHBhcmVuQmxvY2sgPSBjdXJyQmxvY2suYWRkRGVjbGFyZWRMb2NhbFZhcihmdW5jTmFtZSxcbiAgICAgICAgICAgICAgICBWYXJCbG9jay5kZWNsYXJhdGlvblR5cGVzLmZ1bmN0aW9uRGVjbGFyYXRpb24pO1xuICAgICAgICB9XG4gICAgICAgIGNvbnN0IHNvbWVIYXNEZWZhdWx0cyA9IG5vZGUucGFyYW1zLnNvbWUoKHB0bikgPT5cbiAgICAgICAgICAgIG15V2Fsa2VyLnBhdHRlcm5IYXNEZWZhdWx0cyhwdG4pKTtcbiAgICAgICAgaWYgKHNvbWVIYXNEZWZhdWx0cykge1xuICAgICAgICAgICAgcGFyYW1CbG9jayA9IHBhcmVuQmxvY2sgPSBuZXcgVmFyQmxvY2soXG4gICAgICAgICAgICAgICAgcGFyZW5CbG9jayxcbiAgICAgICAgICAgICAgICBub2RlLFxuICAgICAgICAgICAgICAgIFZhckJsb2NrLmJsb2NrVHlwZXMucGFyYW1ldGVyQmxvY2ssXG4gICAgICAgICAgICAgICAgY3VyckJsb2NrLmlzU3RyaWN0XG4gICAgICAgICAgICApO1xuICAgICAgICAgICAgbm9kZVsnQGJsb2NrJ10gPSBwYXJhbUJsb2NrO1xuICAgICAgICB9XG4gICAgICAgIGNvbnN0IHN0cmljdElubmVyID0gY3VyckJsb2NrLmlzU3RyaWN0IHx8XG4gICAgICAgICAgICAobm9kZS5ib2R5LmJvZHkgJiZcbiAgICAgICAgICAgICBub2RlLmJvZHkuYm9keVswXSAmJlxuICAgICAgICAgICAgIGlzVXNlU3RyaWN0KG5vZGUuYm9keS5ib2R5WzBdKSk7XG4gICAgICAgIGNvbnN0IGZ1bmNCbG9jayA9IG5ldyBWYXJCbG9jayhcbiAgICAgICAgICAgIHBhcmVuQmxvY2ssXG4gICAgICAgICAgICBub2RlLCAgLy8gc2FtZSBvcmlnaW5Ob2RlIHdpdGggcGFyYW1CbG9jaywgaW50ZW5kZWQuXG4gICAgICAgICAgICBub2RlLnR5cGUgPT09ICdBcnJvd0Z1bmN0aW9uRXhwcmVzc2lvbic/XG4gICAgICAgICAgICAgICAgVmFyQmxvY2suYmxvY2tUeXBlcy5hcnJvd0Z1bmN0aW9uQmxvY2tcbiAgICAgICAgICAgICAgICA6IFZhckJsb2NrLmJsb2NrVHlwZXMub2xkRnVuY3Rpb25CbG9jayxcbiAgICAgICAgICAgIHN0cmljdElubmVyXG4gICAgICAgICk7XG4gICAgICAgIG5vZGUuYm9keVsnQGJsb2NrJ10gPSBmdW5jQmxvY2s7XG5cbiAgICAgICAgLy8gYWRkIGZ1bmN0aW9uIHBhcmFtZXRlcnMgdG8gY29ycmVzcG9uZGluZyBzY29wZVxuICAgICAgICBjb25zdCBwYXJhbVRhcmdldEJsb2NrID0gcGFyYW1CbG9jayB8fCBmdW5jQmxvY2s7XG4gICAgICAgIGZvciAobGV0IGkgPSAwOyBpIDwgbm9kZS5wYXJhbXMubGVuZ3RoOyBpKyspIHtcbiAgICAgICAgICAgIGMobm9kZS5wYXJhbXNbaV0sXG4gICAgICAgICAgICAgICAgW1xuICAgICAgICAgICAgICAgICAgICBWYXJCbG9jay5kZWNsYXJhdGlvblR5cGVzLnBhcmFtZXRlckRlY2xhcmF0aW9uLFxuICAgICAgICAgICAgICAgICAgICBwYXJhbVRhcmdldEJsb2NrXG4gICAgICAgICAgICAgICAgXSxcbiAgICAgICAgICAgICAgICAnUGF0dGVybicpO1xuICAgICAgICB9XG5cbiAgICAgICAgaWYgKG5vZGUuZXhwcmVzc2lvbikge1xuICAgICAgICAgICAgYyhub2RlLmJvZHksIFssIGZ1bmNCbG9ja10sICdFeHByZXNzaW9uJyk7XG4gICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgICB3YWxrLmJhc2UuQmxvY2tTdGF0ZW1lbnQobm9kZS5ib2R5LCBbLCBmdW5jQmxvY2tdLCBjKTtcbiAgICAgICAgfVxuICAgIH0sXG5cbiAgICBGb3JTdGF0ZW1lbnQ6IChub2RlLCBbLCBjdXJyQmxvY2tdLCBjKSA9PiB7XG4gICAgICAgIGxldCBmb3JCbG9jaztcbiAgICAgICAgaWYgKGN1cnJCbG9jay5pc1N0cmljdCkge1xuICAgICAgICAgICAgZm9yQmxvY2sgPSBuZXcgVmFyQmxvY2soXG4gICAgICAgICAgICAgICAgY3VyckJsb2NrLFxuICAgICAgICAgICAgICAgIG5vZGUsXG4gICAgICAgICAgICAgICAgVmFyQmxvY2suYmxvY2tUeXBlcy5ub3JtYWxCbG9jayxcbiAgICAgICAgICAgICAgICBjdXJyQmxvY2suaXNTdHJpY3RcbiAgICAgICAgICAgICk7XG4gICAgICAgICAgICBub2RlWydAYmxvY2snXSA9IGZvckJsb2NrO1xuICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgICAgZm9yQmxvY2sgPSBjdXJyQmxvY2s7XG4gICAgICAgIH1cbiAgICAgICAgaWYgKG5vZGUuaW5pdCkgYyhub2RlLmluaXQsIFssIGZvckJsb2NrXSwgJ0ZvckluaXQnKTtcbiAgICAgICAgaWYgKG5vZGUudGVzdCkgYyhub2RlLnRlc3QsIFssIGZvckJsb2NrXSwgJ0V4cHJlc3Npb24nKTtcbiAgICAgICAgaWYgKG5vZGUudXBkYXRlKSBjKG5vZGUudXBkYXRlLCBbLCBmb3JCbG9ja10sICdFeHByZXNzaW9uJyk7XG4gICAgICAgIC8vIGl0cyBib2R5IGNhbiBoYXZlIGEgc2VwYXJhdGUgYmxvY2suXG4gICAgICAgIGMobm9kZS5ib2R5LCBbLCBmb3JCbG9ja10sIHVuZGVmaW5lZCk7XG4gICAgfSxcblxuICAgIFZhcmlhYmxlRGVjbGFyYXRpb246IChub2RlLCBbLCBjdXJyQmxvY2tdLCBjKSA9PiB7XG4gICAgICAgIGxldCBkVHlwZTtcbiAgICAgICAgc3dpdGNoKG5vZGUua2luZCkge1xuICAgICAgICAgICAgY2FzZSAndmFyJzpcbiAgICAgICAgICAgICAgICBkVHlwZSA9IFZhckJsb2NrLmRlY2xhcmF0aW9uVHlwZXMudmFyRGVjbGFyYXRpb247XG4gICAgICAgICAgICAgICAgYnJlYWs7XG4gICAgICAgICAgICBjYXNlICdsZXQnOlxuICAgICAgICAgICAgICAgIGRUeXBlID0gVmFyQmxvY2suZGVjbGFyYXRpb25UeXBlcy5sZXREZWNsYXJhdGlvbjtcbiAgICAgICAgICAgICAgICBicmVhaztcbiAgICAgICAgICAgIGNhc2UgJ2NvbnN0JzpcbiAgICAgICAgICAgICAgICBkVHlwZSA9IFZhckJsb2NrLmRlY2xhcmF0aW9uVHlwZXMuY29uc3REZWNsYXJhdGlvbjtcbiAgICAgICAgICAgICAgICBicmVhaztcbiAgICAgICAgfVxuXG4gICAgICAgIGZvciAobGV0IGkgPSAwOyBpIDwgbm9kZS5kZWNsYXJhdGlvbnMubGVuZ3RoOyBpKyspIHtcbiAgICAgICAgICAgIGMobm9kZS5kZWNsYXJhdGlvbnNbaV0sIFtkVHlwZSwgY3VyckJsb2NrXSwgdW5kZWZpbmVkKTtcbiAgICAgICAgfVxuICAgIH0sXG5cbiAgICBUcnlTdGF0ZW1lbnQ6IChub2RlLCBbLCBjdXJyU2NvcGVdLCBjKSA9PiB7XG4gICAgICAgIGMobm9kZS5ibG9jaywgWywgY3VyclNjb3BlXSwgdW5kZWZpbmVkKTtcbiAgICAgICAgaWYgKG5vZGUuaGFuZGxlcikge1xuICAgICAgICAgICAgYyhub2RlLmhhbmRsZXIsIFssIGN1cnJTY29wZV0sIHVuZGVmaW5lZCk7XG4gICAgICAgIH1cbiAgICAgICAgaWYgKG5vZGUuZmluYWxpemVyKSB7XG4gICAgICAgICAgICBjKG5vZGUuZmluYWxpemVyLCBbLCBjdXJyU2NvcGVdLCB1bmRlZmluZWQpO1xuICAgICAgICB9XG4gICAgfSxcblxuICAgIENhdGNoQ2xhdXNlOiAobm9kZSwgWywgY3VyckJsb2NrXSwgYykgPT4ge1xuICAgICAgICBjb25zdCBjYXRjaEJsb2NrID0gbmV3IFZhckJsb2NrKFxuICAgICAgICAgICAgY3VyckJsb2NrLFxuICAgICAgICAgICAgbm9kZSxcbiAgICAgICAgICAgIFZhckJsb2NrLmJsb2NrVHlwZXMuY2F0Y2hCbG9jayxcbiAgICAgICAgICAgIGN1cnJCbG9jay5pc1N0cmljdFxuICAgICAgICApO1xuICAgICAgICBjKG5vZGUucGFyYW0sXG4gICAgICAgICAgICBbXG4gICAgICAgICAgICAgICAgVmFyQmxvY2suZGVjbGFyYXRpb25UeXBlcy5wYXJhbWV0ZXJEZWNsYXJhdGlvbixcbiAgICAgICAgICAgICAgICBjYXRjaEJsb2NrXG4gICAgICAgICAgICBdLFxuICAgICAgICAgICAgJ1BhdHRlcm4nKTtcbiAgICAgICAgbm9kZS5ib2R5WydAYmxvY2snXSA9IGNhdGNoQmxvY2s7XG4gICAgICAgIHdhbGsuYmFzZS5CbG9ja1N0YXRlbWVudChub2RlLmJvZHksIFssIGNhdGNoQmxvY2tdLCBjKTtcbiAgICB9LFxuXG4gICAgLy8gQ3JlYXRlIFZhckJsb2NrIG9mIHR5cGUgbm9ybWFsQmxvY2tcbiAgICBCbG9ja1N0YXRlbWVudDogKG5vZGUsIFssIGN1cnJCbG9ja10sIGMpID0+IHtcbiAgICAgICAgbGV0IGluQmxvY2s7XG4gICAgICAgIGlmIChjdXJyQmxvY2suaXNTdHJpY3QpIHtcbiAgICAgICAgICAgIGluQmxvY2sgPSBuZXcgVmFyQmxvY2soXG4gICAgICAgICAgICAgICAgY3VyckJsb2NrLFxuICAgICAgICAgICAgICAgIG5vZGUsXG4gICAgICAgICAgICAgICAgVmFyQmxvY2suYmxvY2tUeXBlcy5ub3JtYWxCbG9jayxcbiAgICAgICAgICAgICAgICBjdXJyQmxvY2suaXNTdHJpY3RcbiAgICAgICAgICAgICk7XG4gICAgICAgICAgICBub2RlWydAYmxvY2snXSA9IGluQmxvY2s7XG4gICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgICBpbkJsb2NrID0gY3VyckJsb2NrO1xuICAgICAgICB9XG4gICAgICAgIHdhbGsuYmFzZS5CbG9ja1N0YXRlbWVudChub2RlLCBbLCBpbkJsb2NrXSwgYyk7XG4gICAgfVxufSk7XG5cbi8vIEZvciB2YXJpYWJsZXMgaW4gZ2xvYmFsIGFuZCBhcmd1bWVudHMgaW4gZnVuY3Rpb25zXG5jb25zdCB2YXJpYWJsZVVzYWdlQ29sbGVjdG9yID0gd2Fsay5tYWtlKHtcbiAgICBWYXJpYWJsZVBhdHRlcm46IChub2RlLCBjdXJyQmxvY2ssIGMpID0+IHtcbiAgICAgICAgYyhub2RlLCBjdXJyQmxvY2ssICdJZGVudGlmaWVyJyk7XG4gICAgfSxcblxuICAgIElkZW50aWZpZXI6IChub2RlLCBjdXJyQmxvY2ssIGMpID0+IHtcbiAgICAgICAgaWYgKG15V2Fsa2VyLmlzRHVtbXlJZE5vZGUobm9kZSkpIHtcbiAgICAgICAgICAgIC8vIFNraXAgZHVtbXkgSWQgbm9kZVxuICAgICAgICAgICAgcmV0dXJuO1xuICAgICAgICB9XG4gICAgICAgIGxldCBibG9jayA9IGN1cnJCbG9jaztcbiAgICAgICAgY29uc3QgdmFyTmFtZSA9IG5vZGUubmFtZTtcblxuICAgICAgICB3aGlsZSAoYmxvY2sgJiYgIWJsb2NrLmhhc1Zhcih2YXJOYW1lKSkge1xuICAgICAgICAgICAgaWYgKHZhck5hbWUgPT09ICdhcmd1bWVudHMnICYmIGJsb2NrLmlzT2xkRnVuY3Rpb25CbG9jaygpKSB7XG4gICAgICAgICAgICAgICAgYmxvY2sudXNlQXJndW1lbnRzT2JqZWN0ID0gdHJ1ZTtcbiAgICAgICAgICAgICAgICAvLyBjb25zaWRlciAndmFyJyBpcyB1c2VkIGZvciBkZWNsYXJhdGlvbiBvZiAnYXJndW1lbnRzLidcbiAgICAgICAgICAgICAgICBibG9jay5hZGREZWNsYXJlZExvY2FsVmFyKHZhck5hbWUsIFZhckJsb2NrLmRlY2xhcmF0aW9uVHlwZXMudmFyRGVjbGFyYXRpb24pO1xuICAgICAgICAgICAgICAgIGJyZWFrO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgaWYgKGJsb2NrLmlzR2xvYmFsKCkpIHtcbiAgICAgICAgICAgICAgICBibG9jay5hZGREZWNsYXJlZExvY2FsVmFyKHZhck5hbWUsIFZhckJsb2NrLmRlY2xhcmF0aW9uVHlwZXMuaW1wbGljaXRHbG9iYWxEZWNsYXJhdGlvbik7XG4gICAgICAgICAgICAgICAgYnJlYWs7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBibG9jayA9IGJsb2NrLnBhcmVuO1xuICAgICAgICB9XG4gICAgICAgIGlmIChibG9jay5oYXNWYXIodmFyTmFtZSkpIHtcbiAgICAgICAgICAgIGJsb2NrLmFkZFVzZWRWYXIodmFyTmFtZSk7XG4gICAgICAgIH1cbiAgICB9LFxuXG4gICAgUmV0dXJuU3RhdGVtZW50OiAobm9kZSwgY3VyckJsb2NrLCBjKSA9PiB7XG4gICAgICAgIGxldCBibG9jayA9IGN1cnJCbG9jaztcbiAgICAgICAgd2hpbGUgKGJsb2NrLmlzQ2F0Y2hCbG9jaygpIHx8IGJsb2NrLmlzTm9ybWFsQmxvY2soKSkge1xuICAgICAgICAgICAgYmxvY2sgPSBibG9jay5wYXJlbjtcbiAgICAgICAgfVxuICAgICAgICBpZiAoIWJsb2NrLmlzR2xvYmFsKCkgJiYgbm9kZS5hcmd1bWVudCAhPT0gbnVsbCkge1xuICAgICAgICAgICAgYmxvY2sudXNlUmV0dXJuV2l0aEFyZ3VtZW50ID0gdHJ1ZTtcbiAgICAgICAgfVxuICAgICAgICBpZiAobm9kZS5hcmd1bWVudCkge1xuICAgICAgICAgICAgYyhub2RlLmFyZ3VtZW50LCBjdXJyQmxvY2ssIHVuZGVmaW5lZCk7XG4gICAgICAgIH1cbiAgICB9LFxuXG4gICAgRnVuY3Rpb246IChub2RlLCBjdXJyQmxvY2ssIGMpID0+IHtcbiAgICAgICAgLy8gU2luY2Ugd2UgYXJlIGxvb2tpbmcgZm9yIHZhcmlhYmxlIHVzYWdlLCB3ZSBkb24ndCBuZWVkIHRvIGxvb2sgYXQgZm9ybWFsIHBhcmFtZXRlcnMuXG4gICAgICAgIGlmIChub2RlLmlkKSBjKG5vZGUuaWQsIGN1cnJCbG9jayk7XG4gICAgICAgIGMobm9kZS5ib2R5LCBjdXJyQmxvY2spO1xuICAgIH0sXG5cbiAgICBTY29wZUJvZHk6IChub2RlLCBjdXJyQmxvY2ssIGMpID0+IHtcbiAgICAgICAgYyhub2RlLCBub2RlWydAYmxvY2snXSB8fCBjdXJyQmxvY2spO1xuICAgIH0sXG5cbiAgICBCbG9ja1N0YXRlbWVudDogKG5vZGUsIGN1cnJCbG9jaywgYykgPT4ge1xuICAgICAgICAvLyBQcm9jZXNzIEJsb2NrU3RhdGVtZW50IHdpdGggY2hhbmdlZCBWYXJCbG9ja1xuICAgICAgICB3YWxrLmJhc2UuQmxvY2tTdGF0ZW1lbnQobm9kZSwgbm9kZVsnQGJsb2NrJ10gfHwgY3VyckJsb2NrLCBjKTtcbiAgICB9XG59KTtcblxuXG5leHBvcnQgZnVuY3Rpb24gYW5ub3RhdGVCbG9ja0luZm8oYXN0LCBnVmFyQmxvY2spIHtcbiAgICBhc3RbJ0BibG9jayddID0gZ1ZhckJsb2NrO1xuXG4gICAgZ1ZhckJsb2NrLmlzU3RyaWN0ID0gZ1ZhckJsb2NrLmlzU3RyaWN0IHx8XG4gICAgICAgIChhc3QuYm9keVswXSAmJiBpc1VzZVN0cmljdChhc3QuYm9keVswXSkpO1xuXG4gICAgd2Fsay5yZWN1cnNpdmUoYXN0LCBbLCBnVmFyQmxvY2tdLCBkZWNsYXJlZFZhcmlhYmxlRmluZGVyKTtcbiAgICB3YWxrLnJlY3Vyc2l2ZShhc3QsIGdWYXJCbG9jaywgdmFyaWFibGVVc2FnZUNvbGxlY3Rvcik7XG4gICAgcmV0dXJuIGFzdDtcbn1cblxuLy8gZGVmaW5lIFNjb3BlIGNsYXNzXG5jbGFzcyBTY29wZSB7XG4gICAgY29uc3RydWN0b3IocGFyZW4sIHZhck1hcCwgdmIpIHtcbiAgICAgICAgdGhpcy5wYXJlbiA9IHBhcmVuO1xuICAgICAgICB0aGlzLnZhck1hcCA9IHZhck1hcDtcbiAgICAgICAgdGhpcy52YiA9IHZiO1xuICAgIH1cblxuICAgIC8vIGZpbmQgQVZhbCBvZiBhIHZhcmlhYmxlIGluIHRoZSBjaGFpblxuICAgIGdldEFWYWxPZih2YXJOYW1lKSB7XG4gICAgICAgIGxldCBjdXJyID0gdGhpcztcbiAgICAgICAgd2hpbGUgKGN1cnIgIT0gbnVsbCkge1xuICAgICAgICAgICAgaWYgKGN1cnIudmFyTWFwLmhhcyh2YXJOYW1lKSkge1xuICAgICAgICAgICAgICAgIHJldHVybiBjdXJyLnZhck1hcC5nZXQodmFyTmFtZSk7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBjdXJyID0gY3Vyci5wYXJlbjtcbiAgICAgICAgfVxuICAgICAgICAvLyByZXR1cm5zIGR1bW15IEFWYWwgZm9yIG5vdCBmb3VuZCB2YXJpYWJsZXNcbiAgICAgICAgcmV0dXJuIHR5cGVzLkFWYWxOdWxsO1xuICAgIH1cblxuICAgIC8vIHJlbW92ZSBpbml0aWFsIGNhdGNoIHNjb3BlcyBmcm9tIHRoZSBjaGFpblxuICAgIHJlbW92ZUluaXRpYWxDYXRjaE9yTm9ybWFsQmxvY2tzKCkge1xuICAgICAgICBsZXQgY3VyciA9IHRoaXM7XG4gICAgICAgIHdoaWxlIChjdXJyLnZiLmlzQ2F0Y2hCbG9jaygpIHx8IGN1cnIudmIuaXNOb3JtYWxCbG9jaygpKSB7XG4gICAgICAgICAgICBjdXJyID0gY3Vyci5wYXJlbjtcbiAgICAgICAgfVxuICAgICAgICByZXR1cm4gY3VycjtcbiAgICB9XG59XG4iLCJjb25zdCB3YWxrID0gcmVxdWlyZSgnYWNvcm4vZGlzdC93YWxrJyk7XG5pbXBvcnQgKiBhcyBteVdhbGtlciBmcm9tICcuL3V0aWwvbXlXYWxrZXInXG5cbi8qKlxuICpcbiAqIEBwYXJhbSBhc3QgLSBzY29wZSBhbm5vdGF0ZWQgQVNUXG4gKiBAcGFyYW0ge251bWJlcn0gcG9zIC0gY2hhcmFjdGVyIHBvc2l0aW9uXG4gKiBAcmV0dXJucyB7Kn0gLSBhcnJheSBvZiBBU1Qgbm9kZXNcbiAqL1xuZnVuY3Rpb24gZmluZFZhclJlZnNBdChhc3QsIHBvcykge1xuICAgICd1c2Ugc3RyaWN0JztcbiAgICBjb25zdCBmb3VuZCA9IG15V2Fsa2VyLmZpbmRJZGVudGlmaWVyQXQoYXN0LCBwb3MpO1xuICAgIGlmICghZm91bmQpIHtcbiAgICAgICAgLy8gcG9zIGlzIG5vdCBhdCBhIHZhcmlhYmxlXG4gICAgICAgIHJldHVybiBudWxsO1xuICAgIH1cbiAgICAvLyBmaW5kIHJlZnMgZm9yIHRoZSBpZCBub2RlXG4gICAgY29uc3QgcmVmcyA9IGZpbmRSZWZzVG9WYXJpYWJsZShmb3VuZCkubWFwKG5vZGUgPT5cbiAgICAgICAgKHtzdGFydDogbm9kZS5zdGFydCwgZW5kOiBub2RlLmVuZH0pXG4gICAgKTtcbiAgICByZWZzLnZhck5hbWUgPSBmb3VuZC5ub2RlLm5hbWU7XG5cbiAgICByZXR1cm4gcmVmcztcbn1cblxuLyoqXG4gKlxuICogQHBhcmFtIGZvdW5kIC0gbm9kZSBhbmQgdmFyQmxvY2sgb2YgdGhlIHZhcmlhYmxlXG4gKiBAcmV0dXJucyB7QXJyYXl9IC0gYXJyYXkgb2YgQVNUIG5vZGVzXG4gKi9cbmZ1bmN0aW9uIGZpbmRSZWZzVG9WYXJpYWJsZShmb3VuZCkge1xuICAgICd1c2Ugc3RyaWN0JztcbiAgICBjb25zdCB2YXJOYW1lID0gZm91bmQubm9kZS5uYW1lO1xuICAgIGNvbnN0IHZiMSA9IGZvdW5kLnZiLmZpbmRWYXJJbkNoYWluKHZhck5hbWUpO1xuICAgIGlmICghdmIxKSByZXR1cm4gW107XG5cbiAgICBjb25zdCByZWZzID0gW107XG5cbiAgICBjb25zdCB3YWxrZXIgPSB3YWxrLm1ha2Uoe1xuICAgICAgICBJZGVudGlmaWVyOiAobm9kZSwgdmIpID0+IHtcbiAgICAgICAgICAgIGlmIChub2RlLm5hbWUgIT09IHZhck5hbWUpIHJldHVybjtcbiAgICAgICAgICAgIGlmICh2YjEgPT09IHZiLmZpbmRWYXJJbkNoYWluKHZhck5hbWUpKSB7XG4gICAgICAgICAgICAgICAgcmVmcy5wdXNoKG5vZGUpO1xuICAgICAgICAgICAgfVxuICAgICAgICB9XG4gICAgfSwgbXlXYWxrZXIudmFyV2Fsa2VyKTtcblxuICAgIHdhbGsucmVjdXJzaXZlKHZiMS5vcmlnaW5Ob2RlLCB2YjEub3JpZ2luTm9kZVsnQGJsb2NrJ10sIHdhbGtlcik7XG4gICAgcmV0dXJuIHJlZnM7XG59XG5cbmV4cG9ydHMuZmluZFZhclJlZnNBdCA9IGZpbmRWYXJSZWZzQXQ7XG4iLCIoZnVuY3Rpb24oZil7aWYodHlwZW9mIGV4cG9ydHM9PT1cIm9iamVjdFwiJiZ0eXBlb2YgbW9kdWxlIT09XCJ1bmRlZmluZWRcIil7bW9kdWxlLmV4cG9ydHM9ZigpfWVsc2UgaWYodHlwZW9mIGRlZmluZT09PVwiZnVuY3Rpb25cIiYmZGVmaW5lLmFtZCl7ZGVmaW5lKFtdLGYpfWVsc2V7dmFyIGc7aWYodHlwZW9mIHdpbmRvdyE9PVwidW5kZWZpbmVkXCIpe2c9d2luZG93fWVsc2UgaWYodHlwZW9mIGdsb2JhbCE9PVwidW5kZWZpbmVkXCIpe2c9Z2xvYmFsfWVsc2UgaWYodHlwZW9mIHNlbGYhPT1cInVuZGVmaW5lZFwiKXtnPXNlbGZ9ZWxzZXtnPXRoaXN9Zy5hY29ybiA9IGYoKX19KShmdW5jdGlvbigpe3ZhciBkZWZpbmUsbW9kdWxlLGV4cG9ydHM7cmV0dXJuIChmdW5jdGlvbiBlKHQsbixyKXtmdW5jdGlvbiBzKG8sdSl7aWYoIW5bb10pe2lmKCF0W29dKXt2YXIgYT10eXBlb2YgcmVxdWlyZT09XCJmdW5jdGlvblwiJiZyZXF1aXJlO2lmKCF1JiZhKXJldHVybiBhKG8sITApO2lmKGkpcmV0dXJuIGkobywhMCk7dmFyIGY9bmV3IEVycm9yKFwiQ2Fubm90IGZpbmQgbW9kdWxlICdcIitvK1wiJ1wiKTt0aHJvdyBmLmNvZGU9XCJNT0RVTEVfTk9UX0ZPVU5EXCIsZn12YXIgbD1uW29dPXtleHBvcnRzOnt9fTt0W29dWzBdLmNhbGwobC5leHBvcnRzLGZ1bmN0aW9uKGUpe3ZhciBuPXRbb11bMV1bZV07cmV0dXJuIHMobj9uOmUpfSxsLGwuZXhwb3J0cyxlLHQsbixyKX1yZXR1cm4gbltvXS5leHBvcnRzfXZhciBpPXR5cGVvZiByZXF1aXJlPT1cImZ1bmN0aW9uXCImJnJlcXVpcmU7Zm9yKHZhciBvPTA7bzxyLmxlbmd0aDtvKyspcyhyW29dKTtyZXR1cm4gc30pKHsxOltmdW5jdGlvbihfZGVyZXFfLG1vZHVsZSxleHBvcnRzKXtcbi8vIEEgcmVjdXJzaXZlIGRlc2NlbnQgcGFyc2VyIG9wZXJhdGVzIGJ5IGRlZmluaW5nIGZ1bmN0aW9ucyBmb3IgYWxsXG4vLyBzeW50YWN0aWMgZWxlbWVudHMsIGFuZCByZWN1cnNpdmVseSBjYWxsaW5nIHRob3NlLCBlYWNoIGZ1bmN0aW9uXG4vLyBhZHZhbmNpbmcgdGhlIGlucHV0IHN0cmVhbSBhbmQgcmV0dXJuaW5nIGFuIEFTVCBub2RlLiBQcmVjZWRlbmNlXG4vLyBvZiBjb25zdHJ1Y3RzIChmb3IgZXhhbXBsZSwgdGhlIGZhY3QgdGhhdCBgIXhbMV1gIG1lYW5zIGAhKHhbMV0pYFxuLy8gaW5zdGVhZCBvZiBgKCF4KVsxXWAgaXMgaGFuZGxlZCBieSB0aGUgZmFjdCB0aGF0IHRoZSBwYXJzZXJcbi8vIGZ1bmN0aW9uIHRoYXQgcGFyc2VzIHVuYXJ5IHByZWZpeCBvcGVyYXRvcnMgaXMgY2FsbGVkIGZpcnN0LCBhbmRcbi8vIGluIHR1cm4gY2FsbHMgdGhlIGZ1bmN0aW9uIHRoYXQgcGFyc2VzIGBbXWAgc3Vic2NyaXB0cyDigJQgdGhhdFxuLy8gd2F5LCBpdCdsbCByZWNlaXZlIHRoZSBub2RlIGZvciBgeFsxXWAgYWxyZWFkeSBwYXJzZWQsIGFuZCB3cmFwc1xuLy8gKnRoYXQqIGluIHRoZSB1bmFyeSBvcGVyYXRvciBub2RlLlxuLy9cbi8vIEFjb3JuIHVzZXMgYW4gW29wZXJhdG9yIHByZWNlZGVuY2UgcGFyc2VyXVtvcHBdIHRvIGhhbmRsZSBiaW5hcnlcbi8vIG9wZXJhdG9yIHByZWNlZGVuY2UsIGJlY2F1c2UgaXQgaXMgbXVjaCBtb3JlIGNvbXBhY3QgdGhhbiB1c2luZ1xuLy8gdGhlIHRlY2huaXF1ZSBvdXRsaW5lZCBhYm92ZSwgd2hpY2ggdXNlcyBkaWZmZXJlbnQsIG5lc3Rpbmdcbi8vIGZ1bmN0aW9ucyB0byBzcGVjaWZ5IHByZWNlZGVuY2UsIGZvciBhbGwgb2YgdGhlIHRlbiBiaW5hcnlcbi8vIHByZWNlZGVuY2UgbGV2ZWxzIHRoYXQgSmF2YVNjcmlwdCBkZWZpbmVzLlxuLy9cbi8vIFtvcHBdOiBodHRwOi8vZW4ud2lraXBlZGlhLm9yZy93aWtpL09wZXJhdG9yLXByZWNlZGVuY2VfcGFyc2VyXG5cblwidXNlIHN0cmljdFwiO1xuXG52YXIgX3Rva2VudHlwZSA9IF9kZXJlcV8oXCIuL3Rva2VudHlwZVwiKTtcblxudmFyIF9zdGF0ZSA9IF9kZXJlcV8oXCIuL3N0YXRlXCIpO1xuXG52YXIgX2lkZW50aWZpZXIgPSBfZGVyZXFfKFwiLi9pZGVudGlmaWVyXCIpO1xuXG52YXIgX3V0aWwgPSBfZGVyZXFfKFwiLi91dGlsXCIpO1xuXG52YXIgcHAgPSBfc3RhdGUuUGFyc2VyLnByb3RvdHlwZTtcblxuLy8gQ2hlY2sgaWYgcHJvcGVydHkgbmFtZSBjbGFzaGVzIHdpdGggYWxyZWFkeSBhZGRlZC5cbi8vIE9iamVjdC9jbGFzcyBnZXR0ZXJzIGFuZCBzZXR0ZXJzIGFyZSBub3QgYWxsb3dlZCB0byBjbGFzaCDigJRcbi8vIGVpdGhlciB3aXRoIGVhY2ggb3RoZXIgb3Igd2l0aCBhbiBpbml0IHByb3BlcnR5IOKAlCBhbmQgaW5cbi8vIHN0cmljdCBtb2RlLCBpbml0IHByb3BlcnRpZXMgYXJlIGFsc28gbm90IGFsbG93ZWQgdG8gYmUgcmVwZWF0ZWQuXG5cbnBwLmNoZWNrUHJvcENsYXNoID0gZnVuY3Rpb24gKHByb3AsIHByb3BIYXNoKSB7XG4gIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNiAmJiAocHJvcC5jb21wdXRlZCB8fCBwcm9wLm1ldGhvZCB8fCBwcm9wLnNob3J0aGFuZCkpIHJldHVybjtcbiAgdmFyIGtleSA9IHByb3Aua2V5LFxuICAgICAgbmFtZSA9IHVuZGVmaW5lZDtcbiAgc3dpdGNoIChrZXkudHlwZSkge1xuICAgIGNhc2UgXCJJZGVudGlmaWVyXCI6XG4gICAgICBuYW1lID0ga2V5Lm5hbWU7YnJlYWs7XG4gICAgY2FzZSBcIkxpdGVyYWxcIjpcbiAgICAgIG5hbWUgPSBTdHJpbmcoa2V5LnZhbHVlKTticmVhaztcbiAgICBkZWZhdWx0OlxuICAgICAgcmV0dXJuO1xuICB9XG4gIHZhciBraW5kID0gcHJvcC5raW5kO1xuICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYpIHtcbiAgICBpZiAobmFtZSA9PT0gXCJfX3Byb3RvX19cIiAmJiBraW5kID09PSBcImluaXRcIikge1xuICAgICAgaWYgKHByb3BIYXNoLnByb3RvKSB0aGlzLnJhaXNlKGtleS5zdGFydCwgXCJSZWRlZmluaXRpb24gb2YgX19wcm90b19fIHByb3BlcnR5XCIpO1xuICAgICAgcHJvcEhhc2gucHJvdG8gPSB0cnVlO1xuICAgIH1cbiAgICByZXR1cm47XG4gIH1cbiAgdmFyIG90aGVyID0gdW5kZWZpbmVkO1xuICBpZiAoX3V0aWwuaGFzKHByb3BIYXNoLCBuYW1lKSkge1xuICAgIG90aGVyID0gcHJvcEhhc2hbbmFtZV07XG4gICAgdmFyIGlzR2V0U2V0ID0ga2luZCAhPT0gXCJpbml0XCI7XG4gICAgaWYgKCh0aGlzLnN0cmljdCB8fCBpc0dldFNldCkgJiYgb3RoZXJba2luZF0gfHwgIShpc0dldFNldCBeIG90aGVyLmluaXQpKSB0aGlzLnJhaXNlKGtleS5zdGFydCwgXCJSZWRlZmluaXRpb24gb2YgcHJvcGVydHlcIik7XG4gIH0gZWxzZSB7XG4gICAgb3RoZXIgPSBwcm9wSGFzaFtuYW1lXSA9IHtcbiAgICAgIGluaXQ6IGZhbHNlLFxuICAgICAgZ2V0OiBmYWxzZSxcbiAgICAgIHNldDogZmFsc2VcbiAgICB9O1xuICB9XG4gIG90aGVyW2tpbmRdID0gdHJ1ZTtcbn07XG5cbi8vICMjIyBFeHByZXNzaW9uIHBhcnNpbmdcblxuLy8gVGhlc2UgbmVzdCwgZnJvbSB0aGUgbW9zdCBnZW5lcmFsIGV4cHJlc3Npb24gdHlwZSBhdCB0aGUgdG9wIHRvXG4vLyAnYXRvbWljJywgbm9uZGl2aXNpYmxlIGV4cHJlc3Npb24gdHlwZXMgYXQgdGhlIGJvdHRvbS4gTW9zdCBvZlxuLy8gdGhlIGZ1bmN0aW9ucyB3aWxsIHNpbXBseSBsZXQgdGhlIGZ1bmN0aW9uKHMpIGJlbG93IHRoZW0gcGFyc2UsXG4vLyBhbmQsICppZiogdGhlIHN5bnRhY3RpYyBjb25zdHJ1Y3QgdGhleSBoYW5kbGUgaXMgcHJlc2VudCwgd3JhcFxuLy8gdGhlIEFTVCBub2RlIHRoYXQgdGhlIGlubmVyIHBhcnNlciBnYXZlIHRoZW0gaW4gYW5vdGhlciBub2RlLlxuXG4vLyBQYXJzZSBhIGZ1bGwgZXhwcmVzc2lvbi4gVGhlIG9wdGlvbmFsIGFyZ3VtZW50cyBhcmUgdXNlZCB0b1xuLy8gZm9yYmlkIHRoZSBgaW5gIG9wZXJhdG9yIChpbiBmb3IgbG9vcHMgaW5pdGFsaXphdGlvbiBleHByZXNzaW9ucylcbi8vIGFuZCBwcm92aWRlIHJlZmVyZW5jZSBmb3Igc3RvcmluZyAnPScgb3BlcmF0b3IgaW5zaWRlIHNob3J0aGFuZFxuLy8gcHJvcGVydHkgYXNzaWdubWVudCBpbiBjb250ZXh0cyB3aGVyZSBib3RoIG9iamVjdCBleHByZXNzaW9uXG4vLyBhbmQgb2JqZWN0IHBhdHRlcm4gbWlnaHQgYXBwZWFyIChzbyBpdCdzIHBvc3NpYmxlIHRvIHJhaXNlXG4vLyBkZWxheWVkIHN5bnRheCBlcnJvciBhdCBjb3JyZWN0IHBvc2l0aW9uKS5cblxucHAucGFyc2VFeHByZXNzaW9uID0gZnVuY3Rpb24gKG5vSW4sIHJlZlNob3J0aGFuZERlZmF1bHRQb3MpIHtcbiAgdmFyIHN0YXJ0UG9zID0gdGhpcy5zdGFydCxcbiAgICAgIHN0YXJ0TG9jID0gdGhpcy5zdGFydExvYztcbiAgdmFyIGV4cHIgPSB0aGlzLnBhcnNlTWF5YmVBc3NpZ24obm9JbiwgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcyk7XG4gIGlmICh0aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuY29tbWEpIHtcbiAgICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlQXQoc3RhcnRQb3MsIHN0YXJ0TG9jKTtcbiAgICBub2RlLmV4cHJlc3Npb25zID0gW2V4cHJdO1xuICAgIHdoaWxlICh0aGlzLmVhdChfdG9rZW50eXBlLnR5cGVzLmNvbW1hKSkgbm9kZS5leHByZXNzaW9ucy5wdXNoKHRoaXMucGFyc2VNYXliZUFzc2lnbihub0luLCByZWZTaG9ydGhhbmREZWZhdWx0UG9zKSk7XG4gICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIlNlcXVlbmNlRXhwcmVzc2lvblwiKTtcbiAgfVxuICByZXR1cm4gZXhwcjtcbn07XG5cbi8vIFBhcnNlIGFuIGFzc2lnbm1lbnQgZXhwcmVzc2lvbi4gVGhpcyBpbmNsdWRlcyBhcHBsaWNhdGlvbnMgb2Zcbi8vIG9wZXJhdG9ycyBsaWtlIGArPWAuXG5cbnBwLnBhcnNlTWF5YmVBc3NpZ24gPSBmdW5jdGlvbiAobm9JbiwgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcywgYWZ0ZXJMZWZ0UGFyc2UpIHtcbiAgaWYgKHRoaXMudHlwZSA9PSBfdG9rZW50eXBlLnR5cGVzLl95aWVsZCAmJiB0aGlzLmluR2VuZXJhdG9yKSByZXR1cm4gdGhpcy5wYXJzZVlpZWxkKCk7XG5cbiAgdmFyIGZhaWxPblNob3J0aGFuZEFzc2lnbiA9IHVuZGVmaW5lZDtcbiAgaWYgKCFyZWZTaG9ydGhhbmREZWZhdWx0UG9zKSB7XG4gICAgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcyA9IHsgc3RhcnQ6IDAgfTtcbiAgICBmYWlsT25TaG9ydGhhbmRBc3NpZ24gPSB0cnVlO1xuICB9IGVsc2Uge1xuICAgIGZhaWxPblNob3J0aGFuZEFzc2lnbiA9IGZhbHNlO1xuICB9XG4gIHZhciBzdGFydFBvcyA9IHRoaXMuc3RhcnQsXG4gICAgICBzdGFydExvYyA9IHRoaXMuc3RhcnRMb2M7XG4gIGlmICh0aGlzLnR5cGUgPT0gX3Rva2VudHlwZS50eXBlcy5wYXJlbkwgfHwgdGhpcy50eXBlID09IF90b2tlbnR5cGUudHlwZXMubmFtZSkgdGhpcy5wb3RlbnRpYWxBcnJvd0F0ID0gdGhpcy5zdGFydDtcbiAgdmFyIGxlZnQgPSB0aGlzLnBhcnNlTWF5YmVDb25kaXRpb25hbChub0luLCByZWZTaG9ydGhhbmREZWZhdWx0UG9zKTtcbiAgaWYgKGFmdGVyTGVmdFBhcnNlKSBsZWZ0ID0gYWZ0ZXJMZWZ0UGFyc2UuY2FsbCh0aGlzLCBsZWZ0LCBzdGFydFBvcywgc3RhcnRMb2MpO1xuICBpZiAodGhpcy50eXBlLmlzQXNzaWduKSB7XG4gICAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0UG9zLCBzdGFydExvYyk7XG4gICAgbm9kZS5vcGVyYXRvciA9IHRoaXMudmFsdWU7XG4gICAgbm9kZS5sZWZ0ID0gdGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLmVxID8gdGhpcy50b0Fzc2lnbmFibGUobGVmdCkgOiBsZWZ0O1xuICAgIHJlZlNob3J0aGFuZERlZmF1bHRQb3Muc3RhcnQgPSAwOyAvLyByZXNldCBiZWNhdXNlIHNob3J0aGFuZCBkZWZhdWx0IHdhcyB1c2VkIGNvcnJlY3RseVxuICAgIHRoaXMuY2hlY2tMVmFsKGxlZnQpO1xuICAgIHRoaXMubmV4dCgpO1xuICAgIG5vZGUucmlnaHQgPSB0aGlzLnBhcnNlTWF5YmVBc3NpZ24obm9Jbik7XG4gICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkFzc2lnbm1lbnRFeHByZXNzaW9uXCIpO1xuICB9IGVsc2UgaWYgKGZhaWxPblNob3J0aGFuZEFzc2lnbiAmJiByZWZTaG9ydGhhbmREZWZhdWx0UG9zLnN0YXJ0KSB7XG4gICAgdGhpcy51bmV4cGVjdGVkKHJlZlNob3J0aGFuZERlZmF1bHRQb3Muc3RhcnQpO1xuICB9XG4gIHJldHVybiBsZWZ0O1xufTtcblxuLy8gUGFyc2UgYSB0ZXJuYXJ5IGNvbmRpdGlvbmFsIChgPzpgKSBvcGVyYXRvci5cblxucHAucGFyc2VNYXliZUNvbmRpdGlvbmFsID0gZnVuY3Rpb24gKG5vSW4sIHJlZlNob3J0aGFuZERlZmF1bHRQb3MpIHtcbiAgdmFyIHN0YXJ0UG9zID0gdGhpcy5zdGFydCxcbiAgICAgIHN0YXJ0TG9jID0gdGhpcy5zdGFydExvYztcbiAgdmFyIGV4cHIgPSB0aGlzLnBhcnNlRXhwck9wcyhub0luLCByZWZTaG9ydGhhbmREZWZhdWx0UG9zKTtcbiAgaWYgKHJlZlNob3J0aGFuZERlZmF1bHRQb3MgJiYgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcy5zdGFydCkgcmV0dXJuIGV4cHI7XG4gIGlmICh0aGlzLmVhdChfdG9rZW50eXBlLnR5cGVzLnF1ZXN0aW9uKSkge1xuICAgIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGVBdChzdGFydFBvcywgc3RhcnRMb2MpO1xuICAgIG5vZGUudGVzdCA9IGV4cHI7XG4gICAgbm9kZS5jb25zZXF1ZW50ID0gdGhpcy5wYXJzZU1heWJlQXNzaWduKCk7XG4gICAgdGhpcy5leHBlY3QoX3Rva2VudHlwZS50eXBlcy5jb2xvbik7XG4gICAgbm9kZS5hbHRlcm5hdGUgPSB0aGlzLnBhcnNlTWF5YmVBc3NpZ24obm9Jbik7XG4gICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkNvbmRpdGlvbmFsRXhwcmVzc2lvblwiKTtcbiAgfVxuICByZXR1cm4gZXhwcjtcbn07XG5cbi8vIFN0YXJ0IHRoZSBwcmVjZWRlbmNlIHBhcnNlci5cblxucHAucGFyc2VFeHByT3BzID0gZnVuY3Rpb24gKG5vSW4sIHJlZlNob3J0aGFuZERlZmF1bHRQb3MpIHtcbiAgdmFyIHN0YXJ0UG9zID0gdGhpcy5zdGFydCxcbiAgICAgIHN0YXJ0TG9jID0gdGhpcy5zdGFydExvYztcbiAgdmFyIGV4cHIgPSB0aGlzLnBhcnNlTWF5YmVVbmFyeShyZWZTaG9ydGhhbmREZWZhdWx0UG9zKTtcbiAgaWYgKHJlZlNob3J0aGFuZERlZmF1bHRQb3MgJiYgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcy5zdGFydCkgcmV0dXJuIGV4cHI7XG4gIHJldHVybiB0aGlzLnBhcnNlRXhwck9wKGV4cHIsIHN0YXJ0UG9zLCBzdGFydExvYywgLTEsIG5vSW4pO1xufTtcblxuLy8gUGFyc2UgYmluYXJ5IG9wZXJhdG9ycyB3aXRoIHRoZSBvcGVyYXRvciBwcmVjZWRlbmNlIHBhcnNpbmdcbi8vIGFsZ29yaXRobS4gYGxlZnRgIGlzIHRoZSBsZWZ0LWhhbmQgc2lkZSBvZiB0aGUgb3BlcmF0b3IuXG4vLyBgbWluUHJlY2AgcHJvdmlkZXMgY29udGV4dCB0aGF0IGFsbG93cyB0aGUgZnVuY3Rpb24gdG8gc3RvcCBhbmRcbi8vIGRlZmVyIGZ1cnRoZXIgcGFyc2VyIHRvIG9uZSBvZiBpdHMgY2FsbGVycyB3aGVuIGl0IGVuY291bnRlcnMgYW5cbi8vIG9wZXJhdG9yIHRoYXQgaGFzIGEgbG93ZXIgcHJlY2VkZW5jZSB0aGFuIHRoZSBzZXQgaXQgaXMgcGFyc2luZy5cblxucHAucGFyc2VFeHByT3AgPSBmdW5jdGlvbiAobGVmdCwgbGVmdFN0YXJ0UG9zLCBsZWZ0U3RhcnRMb2MsIG1pblByZWMsIG5vSW4pIHtcbiAgdmFyIHByZWMgPSB0aGlzLnR5cGUuYmlub3A7XG4gIGlmIChwcmVjICE9IG51bGwgJiYgKCFub0luIHx8IHRoaXMudHlwZSAhPT0gX3Rva2VudHlwZS50eXBlcy5faW4pKSB7XG4gICAgaWYgKHByZWMgPiBtaW5QcmVjKSB7XG4gICAgICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlQXQobGVmdFN0YXJ0UG9zLCBsZWZ0U3RhcnRMb2MpO1xuICAgICAgbm9kZS5sZWZ0ID0gbGVmdDtcbiAgICAgIG5vZGUub3BlcmF0b3IgPSB0aGlzLnZhbHVlO1xuICAgICAgdmFyIG9wID0gdGhpcy50eXBlO1xuICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICB2YXIgc3RhcnRQb3MgPSB0aGlzLnN0YXJ0LFxuICAgICAgICAgIHN0YXJ0TG9jID0gdGhpcy5zdGFydExvYztcbiAgICAgIG5vZGUucmlnaHQgPSB0aGlzLnBhcnNlRXhwck9wKHRoaXMucGFyc2VNYXliZVVuYXJ5KCksIHN0YXJ0UG9zLCBzdGFydExvYywgcHJlYywgbm9Jbik7XG4gICAgICB0aGlzLmZpbmlzaE5vZGUobm9kZSwgb3AgPT09IF90b2tlbnR5cGUudHlwZXMubG9naWNhbE9SIHx8IG9wID09PSBfdG9rZW50eXBlLnR5cGVzLmxvZ2ljYWxBTkQgPyBcIkxvZ2ljYWxFeHByZXNzaW9uXCIgOiBcIkJpbmFyeUV4cHJlc3Npb25cIik7XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZUV4cHJPcChub2RlLCBsZWZ0U3RhcnRQb3MsIGxlZnRTdGFydExvYywgbWluUHJlYywgbm9Jbik7XG4gICAgfVxuICB9XG4gIHJldHVybiBsZWZ0O1xufTtcblxuLy8gUGFyc2UgdW5hcnkgb3BlcmF0b3JzLCBib3RoIHByZWZpeCBhbmQgcG9zdGZpeC5cblxucHAucGFyc2VNYXliZVVuYXJ5ID0gZnVuY3Rpb24gKHJlZlNob3J0aGFuZERlZmF1bHRQb3MpIHtcbiAgaWYgKHRoaXMudHlwZS5wcmVmaXgpIHtcbiAgICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCksXG4gICAgICAgIHVwZGF0ZSA9IHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5pbmNEZWM7XG4gICAgbm9kZS5vcGVyYXRvciA9IHRoaXMudmFsdWU7XG4gICAgbm9kZS5wcmVmaXggPSB0cnVlO1xuICAgIHRoaXMubmV4dCgpO1xuICAgIG5vZGUuYXJndW1lbnQgPSB0aGlzLnBhcnNlTWF5YmVVbmFyeSgpO1xuICAgIGlmIChyZWZTaG9ydGhhbmREZWZhdWx0UG9zICYmIHJlZlNob3J0aGFuZERlZmF1bHRQb3Muc3RhcnQpIHRoaXMudW5leHBlY3RlZChyZWZTaG9ydGhhbmREZWZhdWx0UG9zLnN0YXJ0KTtcbiAgICBpZiAodXBkYXRlKSB0aGlzLmNoZWNrTFZhbChub2RlLmFyZ3VtZW50KTtlbHNlIGlmICh0aGlzLnN0cmljdCAmJiBub2RlLm9wZXJhdG9yID09PSBcImRlbGV0ZVwiICYmIG5vZGUuYXJndW1lbnQudHlwZSA9PT0gXCJJZGVudGlmaWVyXCIpIHRoaXMucmFpc2Uobm9kZS5zdGFydCwgXCJEZWxldGluZyBsb2NhbCB2YXJpYWJsZSBpbiBzdHJpY3QgbW9kZVwiKTtcbiAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIHVwZGF0ZSA/IFwiVXBkYXRlRXhwcmVzc2lvblwiIDogXCJVbmFyeUV4cHJlc3Npb25cIik7XG4gIH1cbiAgdmFyIHN0YXJ0UG9zID0gdGhpcy5zdGFydCxcbiAgICAgIHN0YXJ0TG9jID0gdGhpcy5zdGFydExvYztcbiAgdmFyIGV4cHIgPSB0aGlzLnBhcnNlRXhwclN1YnNjcmlwdHMocmVmU2hvcnRoYW5kRGVmYXVsdFBvcyk7XG4gIGlmIChyZWZTaG9ydGhhbmREZWZhdWx0UG9zICYmIHJlZlNob3J0aGFuZERlZmF1bHRQb3Muc3RhcnQpIHJldHVybiBleHByO1xuICB3aGlsZSAodGhpcy50eXBlLnBvc3RmaXggJiYgIXRoaXMuY2FuSW5zZXJ0U2VtaWNvbG9uKCkpIHtcbiAgICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlQXQoc3RhcnRQb3MsIHN0YXJ0TG9jKTtcbiAgICBub2RlLm9wZXJhdG9yID0gdGhpcy52YWx1ZTtcbiAgICBub2RlLnByZWZpeCA9IGZhbHNlO1xuICAgIG5vZGUuYXJndW1lbnQgPSBleHByO1xuICAgIHRoaXMuY2hlY2tMVmFsKGV4cHIpO1xuICAgIHRoaXMubmV4dCgpO1xuICAgIGV4cHIgPSB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJVcGRhdGVFeHByZXNzaW9uXCIpO1xuICB9XG4gIHJldHVybiBleHByO1xufTtcblxuLy8gUGFyc2UgY2FsbCwgZG90LCBhbmQgYFtdYC1zdWJzY3JpcHQgZXhwcmVzc2lvbnMuXG5cbnBwLnBhcnNlRXhwclN1YnNjcmlwdHMgPSBmdW5jdGlvbiAocmVmU2hvcnRoYW5kRGVmYXVsdFBvcykge1xuICB2YXIgc3RhcnRQb3MgPSB0aGlzLnN0YXJ0LFxuICAgICAgc3RhcnRMb2MgPSB0aGlzLnN0YXJ0TG9jO1xuICB2YXIgZXhwciA9IHRoaXMucGFyc2VFeHByQXRvbShyZWZTaG9ydGhhbmREZWZhdWx0UG9zKTtcbiAgaWYgKHJlZlNob3J0aGFuZERlZmF1bHRQb3MgJiYgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcy5zdGFydCkgcmV0dXJuIGV4cHI7XG4gIHJldHVybiB0aGlzLnBhcnNlU3Vic2NyaXB0cyhleHByLCBzdGFydFBvcywgc3RhcnRMb2MpO1xufTtcblxucHAucGFyc2VTdWJzY3JpcHRzID0gZnVuY3Rpb24gKGJhc2UsIHN0YXJ0UG9zLCBzdGFydExvYywgbm9DYWxscykge1xuICBmb3IgKDs7KSB7XG4gICAgaWYgKHRoaXMuZWF0KF90b2tlbnR5cGUudHlwZXMuZG90KSkge1xuICAgICAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0UG9zLCBzdGFydExvYyk7XG4gICAgICBub2RlLm9iamVjdCA9IGJhc2U7XG4gICAgICBub2RlLnByb3BlcnR5ID0gdGhpcy5wYXJzZUlkZW50KHRydWUpO1xuICAgICAgbm9kZS5jb21wdXRlZCA9IGZhbHNlO1xuICAgICAgYmFzZSA9IHRoaXMuZmluaXNoTm9kZShub2RlLCBcIk1lbWJlckV4cHJlc3Npb25cIik7XG4gICAgfSBlbHNlIGlmICh0aGlzLmVhdChfdG9rZW50eXBlLnR5cGVzLmJyYWNrZXRMKSkge1xuICAgICAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0UG9zLCBzdGFydExvYyk7XG4gICAgICBub2RlLm9iamVjdCA9IGJhc2U7XG4gICAgICBub2RlLnByb3BlcnR5ID0gdGhpcy5wYXJzZUV4cHJlc3Npb24oKTtcbiAgICAgIG5vZGUuY29tcHV0ZWQgPSB0cnVlO1xuICAgICAgdGhpcy5leHBlY3QoX3Rva2VudHlwZS50eXBlcy5icmFja2V0Uik7XG4gICAgICBiYXNlID0gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiTWVtYmVyRXhwcmVzc2lvblwiKTtcbiAgICB9IGVsc2UgaWYgKCFub0NhbGxzICYmIHRoaXMuZWF0KF90b2tlbnR5cGUudHlwZXMucGFyZW5MKSkge1xuICAgICAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0UG9zLCBzdGFydExvYyk7XG4gICAgICBub2RlLmNhbGxlZSA9IGJhc2U7XG4gICAgICBub2RlLmFyZ3VtZW50cyA9IHRoaXMucGFyc2VFeHByTGlzdChfdG9rZW50eXBlLnR5cGVzLnBhcmVuUiwgZmFsc2UpO1xuICAgICAgYmFzZSA9IHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkNhbGxFeHByZXNzaW9uXCIpO1xuICAgIH0gZWxzZSBpZiAodGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLmJhY2tRdW90ZSkge1xuICAgICAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0UG9zLCBzdGFydExvYyk7XG4gICAgICBub2RlLnRhZyA9IGJhc2U7XG4gICAgICBub2RlLnF1YXNpID0gdGhpcy5wYXJzZVRlbXBsYXRlKCk7XG4gICAgICBiYXNlID0gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiVGFnZ2VkVGVtcGxhdGVFeHByZXNzaW9uXCIpO1xuICAgIH0gZWxzZSB7XG4gICAgICByZXR1cm4gYmFzZTtcbiAgICB9XG4gIH1cbn07XG5cbi8vIFBhcnNlIGFuIGF0b21pYyBleHByZXNzaW9uIOKAlCBlaXRoZXIgYSBzaW5nbGUgdG9rZW4gdGhhdCBpcyBhblxuLy8gZXhwcmVzc2lvbiwgYW4gZXhwcmVzc2lvbiBzdGFydGVkIGJ5IGEga2V5d29yZCBsaWtlIGBmdW5jdGlvbmAgb3Jcbi8vIGBuZXdgLCBvciBhbiBleHByZXNzaW9uIHdyYXBwZWQgaW4gcHVuY3R1YXRpb24gbGlrZSBgKClgLCBgW11gLFxuLy8gb3IgYHt9YC5cblxucHAucGFyc2VFeHByQXRvbSA9IGZ1bmN0aW9uIChyZWZTaG9ydGhhbmREZWZhdWx0UG9zKSB7XG4gIHZhciBub2RlID0gdW5kZWZpbmVkLFxuICAgICAgY2FuQmVBcnJvdyA9IHRoaXMucG90ZW50aWFsQXJyb3dBdCA9PSB0aGlzLnN0YXJ0O1xuICBzd2l0Y2ggKHRoaXMudHlwZSkge1xuICAgIGNhc2UgX3Rva2VudHlwZS50eXBlcy5fc3VwZXI6XG4gICAgICBpZiAoIXRoaXMuaW5GdW5jdGlvbikgdGhpcy5yYWlzZSh0aGlzLnN0YXJ0LCBcIidzdXBlcicgb3V0c2lkZSBvZiBmdW5jdGlvbiBvciBjbGFzc1wiKTtcbiAgICBjYXNlIF90b2tlbnR5cGUudHlwZXMuX3RoaXM6XG4gICAgICB2YXIgdHlwZSA9IHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5fdGhpcyA/IFwiVGhpc0V4cHJlc3Npb25cIiA6IFwiU3VwZXJcIjtcbiAgICAgIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIHR5cGUpO1xuXG4gICAgY2FzZSBfdG9rZW50eXBlLnR5cGVzLl95aWVsZDpcbiAgICAgIGlmICh0aGlzLmluR2VuZXJhdG9yKSB0aGlzLnVuZXhwZWN0ZWQoKTtcblxuICAgIGNhc2UgX3Rva2VudHlwZS50eXBlcy5uYW1lOlxuICAgICAgdmFyIHN0YXJ0UG9zID0gdGhpcy5zdGFydCxcbiAgICAgICAgICBzdGFydExvYyA9IHRoaXMuc3RhcnRMb2M7XG4gICAgICB2YXIgaWQgPSB0aGlzLnBhcnNlSWRlbnQodGhpcy50eXBlICE9PSBfdG9rZW50eXBlLnR5cGVzLm5hbWUpO1xuICAgICAgaWYgKGNhbkJlQXJyb3cgJiYgIXRoaXMuY2FuSW5zZXJ0U2VtaWNvbG9uKCkgJiYgdGhpcy5lYXQoX3Rva2VudHlwZS50eXBlcy5hcnJvdykpIHJldHVybiB0aGlzLnBhcnNlQXJyb3dFeHByZXNzaW9uKHRoaXMuc3RhcnROb2RlQXQoc3RhcnRQb3MsIHN0YXJ0TG9jKSwgW2lkXSk7XG4gICAgICByZXR1cm4gaWQ7XG5cbiAgICBjYXNlIF90b2tlbnR5cGUudHlwZXMucmVnZXhwOlxuICAgICAgdmFyIHZhbHVlID0gdGhpcy52YWx1ZTtcbiAgICAgIG5vZGUgPSB0aGlzLnBhcnNlTGl0ZXJhbCh2YWx1ZS52YWx1ZSk7XG4gICAgICBub2RlLnJlZ2V4ID0geyBwYXR0ZXJuOiB2YWx1ZS5wYXR0ZXJuLCBmbGFnczogdmFsdWUuZmxhZ3MgfTtcbiAgICAgIHJldHVybiBub2RlO1xuXG4gICAgY2FzZSBfdG9rZW50eXBlLnR5cGVzLm51bTpjYXNlIF90b2tlbnR5cGUudHlwZXMuc3RyaW5nOlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VMaXRlcmFsKHRoaXMudmFsdWUpO1xuXG4gICAgY2FzZSBfdG9rZW50eXBlLnR5cGVzLl9udWxsOmNhc2UgX3Rva2VudHlwZS50eXBlcy5fdHJ1ZTpjYXNlIF90b2tlbnR5cGUudHlwZXMuX2ZhbHNlOlxuICAgICAgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gICAgICBub2RlLnZhbHVlID0gdGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLl9udWxsID8gbnVsbCA6IHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5fdHJ1ZTtcbiAgICAgIG5vZGUucmF3ID0gdGhpcy50eXBlLmtleXdvcmQ7XG4gICAgICB0aGlzLm5leHQoKTtcbiAgICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJMaXRlcmFsXCIpO1xuXG4gICAgY2FzZSBfdG9rZW50eXBlLnR5cGVzLnBhcmVuTDpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlUGFyZW5BbmREaXN0aW5ndWlzaEV4cHJlc3Npb24oY2FuQmVBcnJvdyk7XG5cbiAgICBjYXNlIF90b2tlbnR5cGUudHlwZXMuYnJhY2tldEw6XG4gICAgICBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgLy8gY2hlY2sgd2hldGhlciB0aGlzIGlzIGFycmF5IGNvbXByZWhlbnNpb24gb3IgcmVndWxhciBhcnJheVxuICAgICAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA3ICYmIHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5fZm9yKSB7XG4gICAgICAgIHJldHVybiB0aGlzLnBhcnNlQ29tcHJlaGVuc2lvbihub2RlLCBmYWxzZSk7XG4gICAgICB9XG4gICAgICBub2RlLmVsZW1lbnRzID0gdGhpcy5wYXJzZUV4cHJMaXN0KF90b2tlbnR5cGUudHlwZXMuYnJhY2tldFIsIHRydWUsIHRydWUsIHJlZlNob3J0aGFuZERlZmF1bHRQb3MpO1xuICAgICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkFycmF5RXhwcmVzc2lvblwiKTtcblxuICAgIGNhc2UgX3Rva2VudHlwZS50eXBlcy5icmFjZUw6XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZU9iaihmYWxzZSwgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcyk7XG5cbiAgICBjYXNlIF90b2tlbnR5cGUudHlwZXMuX2Z1bmN0aW9uOlxuICAgICAgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gICAgICB0aGlzLm5leHQoKTtcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlRnVuY3Rpb24obm9kZSwgZmFsc2UpO1xuXG4gICAgY2FzZSBfdG9rZW50eXBlLnR5cGVzLl9jbGFzczpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlQ2xhc3ModGhpcy5zdGFydE5vZGUoKSwgZmFsc2UpO1xuXG4gICAgY2FzZSBfdG9rZW50eXBlLnR5cGVzLl9uZXc6XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZU5ldygpO1xuXG4gICAgY2FzZSBfdG9rZW50eXBlLnR5cGVzLmJhY2tRdW90ZTpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlVGVtcGxhdGUoKTtcblxuICAgIGRlZmF1bHQ6XG4gICAgICB0aGlzLnVuZXhwZWN0ZWQoKTtcbiAgfVxufTtcblxucHAucGFyc2VMaXRlcmFsID0gZnVuY3Rpb24gKHZhbHVlKSB7XG4gIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgbm9kZS52YWx1ZSA9IHZhbHVlO1xuICBub2RlLnJhdyA9IHRoaXMuaW5wdXQuc2xpY2UodGhpcy5zdGFydCwgdGhpcy5lbmQpO1xuICB0aGlzLm5leHQoKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkxpdGVyYWxcIik7XG59O1xuXG5wcC5wYXJzZVBhcmVuRXhwcmVzc2lvbiA9IGZ1bmN0aW9uICgpIHtcbiAgdGhpcy5leHBlY3QoX3Rva2VudHlwZS50eXBlcy5wYXJlbkwpO1xuICB2YXIgdmFsID0gdGhpcy5wYXJzZUV4cHJlc3Npb24oKTtcbiAgdGhpcy5leHBlY3QoX3Rva2VudHlwZS50eXBlcy5wYXJlblIpO1xuICByZXR1cm4gdmFsO1xufTtcblxucHAucGFyc2VQYXJlbkFuZERpc3Rpbmd1aXNoRXhwcmVzc2lvbiA9IGZ1bmN0aW9uIChjYW5CZUFycm93KSB7XG4gIHZhciBzdGFydFBvcyA9IHRoaXMuc3RhcnQsXG4gICAgICBzdGFydExvYyA9IHRoaXMuc3RhcnRMb2MsXG4gICAgICB2YWwgPSB1bmRlZmluZWQ7XG4gIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNikge1xuICAgIHRoaXMubmV4dCgpO1xuXG4gICAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA3ICYmIHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5fZm9yKSB7XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZUNvbXByZWhlbnNpb24odGhpcy5zdGFydE5vZGVBdChzdGFydFBvcywgc3RhcnRMb2MpLCB0cnVlKTtcbiAgICB9XG5cbiAgICB2YXIgaW5uZXJTdGFydFBvcyA9IHRoaXMuc3RhcnQsXG4gICAgICAgIGlubmVyU3RhcnRMb2MgPSB0aGlzLnN0YXJ0TG9jO1xuICAgIHZhciBleHByTGlzdCA9IFtdLFxuICAgICAgICBmaXJzdCA9IHRydWU7XG4gICAgdmFyIHJlZlNob3J0aGFuZERlZmF1bHRQb3MgPSB7IHN0YXJ0OiAwIH0sXG4gICAgICAgIHNwcmVhZFN0YXJ0ID0gdW5kZWZpbmVkLFxuICAgICAgICBpbm5lclBhcmVuU3RhcnQgPSB1bmRlZmluZWQ7XG4gICAgd2hpbGUgKHRoaXMudHlwZSAhPT0gX3Rva2VudHlwZS50eXBlcy5wYXJlblIpIHtcbiAgICAgIGZpcnN0ID8gZmlyc3QgPSBmYWxzZSA6IHRoaXMuZXhwZWN0KF90b2tlbnR5cGUudHlwZXMuY29tbWEpO1xuICAgICAgaWYgKHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5lbGxpcHNpcykge1xuICAgICAgICBzcHJlYWRTdGFydCA9IHRoaXMuc3RhcnQ7XG4gICAgICAgIGV4cHJMaXN0LnB1c2godGhpcy5wYXJzZVBhcmVuSXRlbSh0aGlzLnBhcnNlUmVzdCgpKSk7XG4gICAgICAgIGJyZWFrO1xuICAgICAgfSBlbHNlIHtcbiAgICAgICAgaWYgKHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5wYXJlbkwgJiYgIWlubmVyUGFyZW5TdGFydCkge1xuICAgICAgICAgIGlubmVyUGFyZW5TdGFydCA9IHRoaXMuc3RhcnQ7XG4gICAgICAgIH1cbiAgICAgICAgZXhwckxpc3QucHVzaCh0aGlzLnBhcnNlTWF5YmVBc3NpZ24oZmFsc2UsIHJlZlNob3J0aGFuZERlZmF1bHRQb3MsIHRoaXMucGFyc2VQYXJlbkl0ZW0pKTtcbiAgICAgIH1cbiAgICB9XG4gICAgdmFyIGlubmVyRW5kUG9zID0gdGhpcy5zdGFydCxcbiAgICAgICAgaW5uZXJFbmRMb2MgPSB0aGlzLnN0YXJ0TG9jO1xuICAgIHRoaXMuZXhwZWN0KF90b2tlbnR5cGUudHlwZXMucGFyZW5SKTtcblxuICAgIGlmIChjYW5CZUFycm93ICYmICF0aGlzLmNhbkluc2VydFNlbWljb2xvbigpICYmIHRoaXMuZWF0KF90b2tlbnR5cGUudHlwZXMuYXJyb3cpKSB7XG4gICAgICBpZiAoaW5uZXJQYXJlblN0YXJ0KSB0aGlzLnVuZXhwZWN0ZWQoaW5uZXJQYXJlblN0YXJ0KTtcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlUGFyZW5BcnJvd0xpc3Qoc3RhcnRQb3MsIHN0YXJ0TG9jLCBleHByTGlzdCk7XG4gICAgfVxuXG4gICAgaWYgKCFleHByTGlzdC5sZW5ndGgpIHRoaXMudW5leHBlY3RlZCh0aGlzLmxhc3RUb2tTdGFydCk7XG4gICAgaWYgKHNwcmVhZFN0YXJ0KSB0aGlzLnVuZXhwZWN0ZWQoc3ByZWFkU3RhcnQpO1xuICAgIGlmIChyZWZTaG9ydGhhbmREZWZhdWx0UG9zLnN0YXJ0KSB0aGlzLnVuZXhwZWN0ZWQocmVmU2hvcnRoYW5kRGVmYXVsdFBvcy5zdGFydCk7XG5cbiAgICBpZiAoZXhwckxpc3QubGVuZ3RoID4gMSkge1xuICAgICAgdmFsID0gdGhpcy5zdGFydE5vZGVBdChpbm5lclN0YXJ0UG9zLCBpbm5lclN0YXJ0TG9jKTtcbiAgICAgIHZhbC5leHByZXNzaW9ucyA9IGV4cHJMaXN0O1xuICAgICAgdGhpcy5maW5pc2hOb2RlQXQodmFsLCBcIlNlcXVlbmNlRXhwcmVzc2lvblwiLCBpbm5lckVuZFBvcywgaW5uZXJFbmRMb2MpO1xuICAgIH0gZWxzZSB7XG4gICAgICB2YWwgPSBleHByTGlzdFswXTtcbiAgICB9XG4gIH0gZWxzZSB7XG4gICAgdmFsID0gdGhpcy5wYXJzZVBhcmVuRXhwcmVzc2lvbigpO1xuICB9XG5cbiAgaWYgKHRoaXMub3B0aW9ucy5wcmVzZXJ2ZVBhcmVucykge1xuICAgIHZhciBwYXIgPSB0aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0UG9zLCBzdGFydExvYyk7XG4gICAgcGFyLmV4cHJlc3Npb24gPSB2YWw7XG4gICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShwYXIsIFwiUGFyZW50aGVzaXplZEV4cHJlc3Npb25cIik7XG4gIH0gZWxzZSB7XG4gICAgcmV0dXJuIHZhbDtcbiAgfVxufTtcblxucHAucGFyc2VQYXJlbkl0ZW0gPSBmdW5jdGlvbiAoaXRlbSkge1xuICByZXR1cm4gaXRlbTtcbn07XG5cbnBwLnBhcnNlUGFyZW5BcnJvd0xpc3QgPSBmdW5jdGlvbiAoc3RhcnRQb3MsIHN0YXJ0TG9jLCBleHByTGlzdCkge1xuICByZXR1cm4gdGhpcy5wYXJzZUFycm93RXhwcmVzc2lvbih0aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0UG9zLCBzdGFydExvYyksIGV4cHJMaXN0KTtcbn07XG5cbi8vIE5ldydzIHByZWNlZGVuY2UgaXMgc2xpZ2h0bHkgdHJpY2t5LiBJdCBtdXN0IGFsbG93IGl0cyBhcmd1bWVudFxuLy8gdG8gYmUgYSBgW11gIG9yIGRvdCBzdWJzY3JpcHQgZXhwcmVzc2lvbiwgYnV0IG5vdCBhIGNhbGwg4oCUIGF0XG4vLyBsZWFzdCwgbm90IHdpdGhvdXQgd3JhcHBpbmcgaXQgaW4gcGFyZW50aGVzZXMuIFRodXMsIGl0IHVzZXMgdGhlXG5cbnZhciBlbXB0eSA9IFtdO1xuXG5wcC5wYXJzZU5ldyA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICB2YXIgbWV0YSA9IHRoaXMucGFyc2VJZGVudCh0cnVlKTtcbiAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2ICYmIHRoaXMuZWF0KF90b2tlbnR5cGUudHlwZXMuZG90KSkge1xuICAgIG5vZGUubWV0YSA9IG1ldGE7XG4gICAgbm9kZS5wcm9wZXJ0eSA9IHRoaXMucGFyc2VJZGVudCh0cnVlKTtcbiAgICBpZiAobm9kZS5wcm9wZXJ0eS5uYW1lICE9PSBcInRhcmdldFwiKSB0aGlzLnJhaXNlKG5vZGUucHJvcGVydHkuc3RhcnQsIFwiVGhlIG9ubHkgdmFsaWQgbWV0YSBwcm9wZXJ0eSBmb3IgbmV3IGlzIG5ldy50YXJnZXRcIik7XG4gICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIk1ldGFQcm9wZXJ0eVwiKTtcbiAgfVxuICB2YXIgc3RhcnRQb3MgPSB0aGlzLnN0YXJ0LFxuICAgICAgc3RhcnRMb2MgPSB0aGlzLnN0YXJ0TG9jO1xuICBub2RlLmNhbGxlZSA9IHRoaXMucGFyc2VTdWJzY3JpcHRzKHRoaXMucGFyc2VFeHByQXRvbSgpLCBzdGFydFBvcywgc3RhcnRMb2MsIHRydWUpO1xuICBpZiAodGhpcy5lYXQoX3Rva2VudHlwZS50eXBlcy5wYXJlbkwpKSBub2RlLmFyZ3VtZW50cyA9IHRoaXMucGFyc2VFeHByTGlzdChfdG9rZW50eXBlLnR5cGVzLnBhcmVuUiwgZmFsc2UpO2Vsc2Ugbm9kZS5hcmd1bWVudHMgPSBlbXB0eTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIk5ld0V4cHJlc3Npb25cIik7XG59O1xuXG4vLyBQYXJzZSB0ZW1wbGF0ZSBleHByZXNzaW9uLlxuXG5wcC5wYXJzZVRlbXBsYXRlRWxlbWVudCA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIGVsZW0gPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICBlbGVtLnZhbHVlID0ge1xuICAgIHJhdzogdGhpcy5pbnB1dC5zbGljZSh0aGlzLnN0YXJ0LCB0aGlzLmVuZCkucmVwbGFjZSgvXFxyXFxuPy9nLCBcIlxcblwiKSxcbiAgICBjb29rZWQ6IHRoaXMudmFsdWVcbiAgfTtcbiAgdGhpcy5uZXh0KCk7XG4gIGVsZW0udGFpbCA9IHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5iYWNrUXVvdGU7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUoZWxlbSwgXCJUZW1wbGF0ZUVsZW1lbnRcIik7XG59O1xuXG5wcC5wYXJzZVRlbXBsYXRlID0gZnVuY3Rpb24gKCkge1xuICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gIHRoaXMubmV4dCgpO1xuICBub2RlLmV4cHJlc3Npb25zID0gW107XG4gIHZhciBjdXJFbHQgPSB0aGlzLnBhcnNlVGVtcGxhdGVFbGVtZW50KCk7XG4gIG5vZGUucXVhc2lzID0gW2N1ckVsdF07XG4gIHdoaWxlICghY3VyRWx0LnRhaWwpIHtcbiAgICB0aGlzLmV4cGVjdChfdG9rZW50eXBlLnR5cGVzLmRvbGxhckJyYWNlTCk7XG4gICAgbm9kZS5leHByZXNzaW9ucy5wdXNoKHRoaXMucGFyc2VFeHByZXNzaW9uKCkpO1xuICAgIHRoaXMuZXhwZWN0KF90b2tlbnR5cGUudHlwZXMuYnJhY2VSKTtcbiAgICBub2RlLnF1YXNpcy5wdXNoKGN1ckVsdCA9IHRoaXMucGFyc2VUZW1wbGF0ZUVsZW1lbnQoKSk7XG4gIH1cbiAgdGhpcy5uZXh0KCk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJUZW1wbGF0ZUxpdGVyYWxcIik7XG59O1xuXG4vLyBQYXJzZSBhbiBvYmplY3QgbGl0ZXJhbCBvciBiaW5kaW5nIHBhdHRlcm4uXG5cbnBwLnBhcnNlT2JqID0gZnVuY3Rpb24gKGlzUGF0dGVybiwgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcykge1xuICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCksXG4gICAgICBmaXJzdCA9IHRydWUsXG4gICAgICBwcm9wSGFzaCA9IHt9O1xuICBub2RlLnByb3BlcnRpZXMgPSBbXTtcbiAgdGhpcy5uZXh0KCk7XG4gIHdoaWxlICghdGhpcy5lYXQoX3Rva2VudHlwZS50eXBlcy5icmFjZVIpKSB7XG4gICAgaWYgKCFmaXJzdCkge1xuICAgICAgdGhpcy5leHBlY3QoX3Rva2VudHlwZS50eXBlcy5jb21tYSk7XG4gICAgICBpZiAodGhpcy5hZnRlclRyYWlsaW5nQ29tbWEoX3Rva2VudHlwZS50eXBlcy5icmFjZVIpKSBicmVhaztcbiAgICB9IGVsc2UgZmlyc3QgPSBmYWxzZTtcblxuICAgIHZhciBwcm9wID0gdGhpcy5zdGFydE5vZGUoKSxcbiAgICAgICAgaXNHZW5lcmF0b3IgPSB1bmRlZmluZWQsXG4gICAgICAgIHN0YXJ0UG9zID0gdW5kZWZpbmVkLFxuICAgICAgICBzdGFydExvYyA9IHVuZGVmaW5lZDtcbiAgICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYpIHtcbiAgICAgIHByb3AubWV0aG9kID0gZmFsc2U7XG4gICAgICBwcm9wLnNob3J0aGFuZCA9IGZhbHNlO1xuICAgICAgaWYgKGlzUGF0dGVybiB8fCByZWZTaG9ydGhhbmREZWZhdWx0UG9zKSB7XG4gICAgICAgIHN0YXJ0UG9zID0gdGhpcy5zdGFydDtcbiAgICAgICAgc3RhcnRMb2MgPSB0aGlzLnN0YXJ0TG9jO1xuICAgICAgfVxuICAgICAgaWYgKCFpc1BhdHRlcm4pIGlzR2VuZXJhdG9yID0gdGhpcy5lYXQoX3Rva2VudHlwZS50eXBlcy5zdGFyKTtcbiAgICB9XG4gICAgdGhpcy5wYXJzZVByb3BlcnR5TmFtZShwcm9wKTtcbiAgICB0aGlzLnBhcnNlUHJvcGVydHlWYWx1ZShwcm9wLCBpc1BhdHRlcm4sIGlzR2VuZXJhdG9yLCBzdGFydFBvcywgc3RhcnRMb2MsIHJlZlNob3J0aGFuZERlZmF1bHRQb3MpO1xuICAgIHRoaXMuY2hlY2tQcm9wQ2xhc2gocHJvcCwgcHJvcEhhc2gpO1xuICAgIG5vZGUucHJvcGVydGllcy5wdXNoKHRoaXMuZmluaXNoTm9kZShwcm9wLCBcIlByb3BlcnR5XCIpKTtcbiAgfVxuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIGlzUGF0dGVybiA/IFwiT2JqZWN0UGF0dGVyblwiIDogXCJPYmplY3RFeHByZXNzaW9uXCIpO1xufTtcblxucHAucGFyc2VQcm9wZXJ0eVZhbHVlID0gZnVuY3Rpb24gKHByb3AsIGlzUGF0dGVybiwgaXNHZW5lcmF0b3IsIHN0YXJ0UG9zLCBzdGFydExvYywgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcykge1xuICBpZiAodGhpcy5lYXQoX3Rva2VudHlwZS50eXBlcy5jb2xvbikpIHtcbiAgICBwcm9wLnZhbHVlID0gaXNQYXR0ZXJuID8gdGhpcy5wYXJzZU1heWJlRGVmYXVsdCh0aGlzLnN0YXJ0LCB0aGlzLnN0YXJ0TG9jKSA6IHRoaXMucGFyc2VNYXliZUFzc2lnbihmYWxzZSwgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcyk7XG4gICAgcHJvcC5raW5kID0gXCJpbml0XCI7XG4gIH0gZWxzZSBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYgJiYgdGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLnBhcmVuTCkge1xuICAgIGlmIChpc1BhdHRlcm4pIHRoaXMudW5leHBlY3RlZCgpO1xuICAgIHByb3Aua2luZCA9IFwiaW5pdFwiO1xuICAgIHByb3AubWV0aG9kID0gdHJ1ZTtcbiAgICBwcm9wLnZhbHVlID0gdGhpcy5wYXJzZU1ldGhvZChpc0dlbmVyYXRvcik7XG4gIH0gZWxzZSBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDUgJiYgIXByb3AuY29tcHV0ZWQgJiYgcHJvcC5rZXkudHlwZSA9PT0gXCJJZGVudGlmaWVyXCIgJiYgKHByb3Aua2V5Lm5hbWUgPT09IFwiZ2V0XCIgfHwgcHJvcC5rZXkubmFtZSA9PT0gXCJzZXRcIikgJiYgKHRoaXMudHlwZSAhPSBfdG9rZW50eXBlLnR5cGVzLmNvbW1hICYmIHRoaXMudHlwZSAhPSBfdG9rZW50eXBlLnR5cGVzLmJyYWNlUikpIHtcbiAgICBpZiAoaXNHZW5lcmF0b3IgfHwgaXNQYXR0ZXJuKSB0aGlzLnVuZXhwZWN0ZWQoKTtcbiAgICBwcm9wLmtpbmQgPSBwcm9wLmtleS5uYW1lO1xuICAgIHRoaXMucGFyc2VQcm9wZXJ0eU5hbWUocHJvcCk7XG4gICAgcHJvcC52YWx1ZSA9IHRoaXMucGFyc2VNZXRob2QoZmFsc2UpO1xuICAgIHZhciBwYXJhbUNvdW50ID0gcHJvcC5raW5kID09PSBcImdldFwiID8gMCA6IDE7XG4gICAgaWYgKHByb3AudmFsdWUucGFyYW1zLmxlbmd0aCAhPT0gcGFyYW1Db3VudCkge1xuICAgICAgdmFyIHN0YXJ0ID0gcHJvcC52YWx1ZS5zdGFydDtcbiAgICAgIGlmIChwcm9wLmtpbmQgPT09IFwiZ2V0XCIpIHRoaXMucmFpc2Uoc3RhcnQsIFwiZ2V0dGVyIHNob3VsZCBoYXZlIG5vIHBhcmFtc1wiKTtlbHNlIHRoaXMucmFpc2Uoc3RhcnQsIFwic2V0dGVyIHNob3VsZCBoYXZlIGV4YWN0bHkgb25lIHBhcmFtXCIpO1xuICAgIH1cbiAgfSBlbHNlIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNiAmJiAhcHJvcC5jb21wdXRlZCAmJiBwcm9wLmtleS50eXBlID09PSBcIklkZW50aWZpZXJcIikge1xuICAgIHByb3Aua2luZCA9IFwiaW5pdFwiO1xuICAgIGlmIChpc1BhdHRlcm4pIHtcbiAgICAgIGlmICh0aGlzLmlzS2V5d29yZChwcm9wLmtleS5uYW1lKSB8fCB0aGlzLnN0cmljdCAmJiAoX2lkZW50aWZpZXIucmVzZXJ2ZWRXb3Jkcy5zdHJpY3RCaW5kKHByb3Aua2V5Lm5hbWUpIHx8IF9pZGVudGlmaWVyLnJlc2VydmVkV29yZHMuc3RyaWN0KHByb3Aua2V5Lm5hbWUpKSB8fCAhdGhpcy5vcHRpb25zLmFsbG93UmVzZXJ2ZWQgJiYgdGhpcy5pc1Jlc2VydmVkV29yZChwcm9wLmtleS5uYW1lKSkgdGhpcy5yYWlzZShwcm9wLmtleS5zdGFydCwgXCJCaW5kaW5nIFwiICsgcHJvcC5rZXkubmFtZSk7XG4gICAgICBwcm9wLnZhbHVlID0gdGhpcy5wYXJzZU1heWJlRGVmYXVsdChzdGFydFBvcywgc3RhcnRMb2MsIHByb3Aua2V5KTtcbiAgICB9IGVsc2UgaWYgKHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5lcSAmJiByZWZTaG9ydGhhbmREZWZhdWx0UG9zKSB7XG4gICAgICBpZiAoIXJlZlNob3J0aGFuZERlZmF1bHRQb3Muc3RhcnQpIHJlZlNob3J0aGFuZERlZmF1bHRQb3Muc3RhcnQgPSB0aGlzLnN0YXJ0O1xuICAgICAgcHJvcC52YWx1ZSA9IHRoaXMucGFyc2VNYXliZURlZmF1bHQoc3RhcnRQb3MsIHN0YXJ0TG9jLCBwcm9wLmtleSk7XG4gICAgfSBlbHNlIHtcbiAgICAgIHByb3AudmFsdWUgPSBwcm9wLmtleTtcbiAgICB9XG4gICAgcHJvcC5zaG9ydGhhbmQgPSB0cnVlO1xuICB9IGVsc2UgdGhpcy51bmV4cGVjdGVkKCk7XG59O1xuXG5wcC5wYXJzZVByb3BlcnR5TmFtZSA9IGZ1bmN0aW9uIChwcm9wKSB7XG4gIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNikge1xuICAgIGlmICh0aGlzLmVhdChfdG9rZW50eXBlLnR5cGVzLmJyYWNrZXRMKSkge1xuICAgICAgcHJvcC5jb21wdXRlZCA9IHRydWU7XG4gICAgICBwcm9wLmtleSA9IHRoaXMucGFyc2VNYXliZUFzc2lnbigpO1xuICAgICAgdGhpcy5leHBlY3QoX3Rva2VudHlwZS50eXBlcy5icmFja2V0Uik7XG4gICAgICByZXR1cm4gcHJvcC5rZXk7XG4gICAgfSBlbHNlIHtcbiAgICAgIHByb3AuY29tcHV0ZWQgPSBmYWxzZTtcbiAgICB9XG4gIH1cbiAgcmV0dXJuIHByb3Aua2V5ID0gdGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLm51bSB8fCB0aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuc3RyaW5nID8gdGhpcy5wYXJzZUV4cHJBdG9tKCkgOiB0aGlzLnBhcnNlSWRlbnQodHJ1ZSk7XG59O1xuXG4vLyBJbml0aWFsaXplIGVtcHR5IGZ1bmN0aW9uIG5vZGUuXG5cbnBwLmluaXRGdW5jdGlvbiA9IGZ1bmN0aW9uIChub2RlKSB7XG4gIG5vZGUuaWQgPSBudWxsO1xuICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYpIHtcbiAgICBub2RlLmdlbmVyYXRvciA9IGZhbHNlO1xuICAgIG5vZGUuZXhwcmVzc2lvbiA9IGZhbHNlO1xuICB9XG59O1xuXG4vLyBQYXJzZSBvYmplY3Qgb3IgY2xhc3MgbWV0aG9kLlxuXG5wcC5wYXJzZU1ldGhvZCA9IGZ1bmN0aW9uIChpc0dlbmVyYXRvcikge1xuICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gIHRoaXMuaW5pdEZ1bmN0aW9uKG5vZGUpO1xuICB0aGlzLmV4cGVjdChfdG9rZW50eXBlLnR5cGVzLnBhcmVuTCk7XG4gIG5vZGUucGFyYW1zID0gdGhpcy5wYXJzZUJpbmRpbmdMaXN0KF90b2tlbnR5cGUudHlwZXMucGFyZW5SLCBmYWxzZSwgZmFsc2UpO1xuICB2YXIgYWxsb3dFeHByZXNzaW9uQm9keSA9IHVuZGVmaW5lZDtcbiAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KSB7XG4gICAgbm9kZS5nZW5lcmF0b3IgPSBpc0dlbmVyYXRvcjtcbiAgfVxuICB0aGlzLnBhcnNlRnVuY3Rpb25Cb2R5KG5vZGUsIGZhbHNlKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkZ1bmN0aW9uRXhwcmVzc2lvblwiKTtcbn07XG5cbi8vIFBhcnNlIGFycm93IGZ1bmN0aW9uIGV4cHJlc3Npb24gd2l0aCBnaXZlbiBwYXJhbWV0ZXJzLlxuXG5wcC5wYXJzZUFycm93RXhwcmVzc2lvbiA9IGZ1bmN0aW9uIChub2RlLCBwYXJhbXMpIHtcbiAgdGhpcy5pbml0RnVuY3Rpb24obm9kZSk7XG4gIG5vZGUucGFyYW1zID0gdGhpcy50b0Fzc2lnbmFibGVMaXN0KHBhcmFtcywgdHJ1ZSk7XG4gIHRoaXMucGFyc2VGdW5jdGlvbkJvZHkobm9kZSwgdHJ1ZSk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJBcnJvd0Z1bmN0aW9uRXhwcmVzc2lvblwiKTtcbn07XG5cbi8vIFBhcnNlIGZ1bmN0aW9uIGJvZHkgYW5kIGNoZWNrIHBhcmFtZXRlcnMuXG5cbnBwLnBhcnNlRnVuY3Rpb25Cb2R5ID0gZnVuY3Rpb24gKG5vZGUsIGFsbG93RXhwcmVzc2lvbikge1xuICB2YXIgaXNFeHByZXNzaW9uID0gYWxsb3dFeHByZXNzaW9uICYmIHRoaXMudHlwZSAhPT0gX3Rva2VudHlwZS50eXBlcy5icmFjZUw7XG5cbiAgaWYgKGlzRXhwcmVzc2lvbikge1xuICAgIG5vZGUuYm9keSA9IHRoaXMucGFyc2VNYXliZUFzc2lnbigpO1xuICAgIG5vZGUuZXhwcmVzc2lvbiA9IHRydWU7XG4gIH0gZWxzZSB7XG4gICAgLy8gU3RhcnQgYSBuZXcgc2NvcGUgd2l0aCByZWdhcmQgdG8gbGFiZWxzIGFuZCB0aGUgYGluRnVuY3Rpb25gXG4gICAgLy8gZmxhZyAocmVzdG9yZSB0aGVtIHRvIHRoZWlyIG9sZCB2YWx1ZSBhZnRlcndhcmRzKS5cbiAgICB2YXIgb2xkSW5GdW5jID0gdGhpcy5pbkZ1bmN0aW9uLFxuICAgICAgICBvbGRJbkdlbiA9IHRoaXMuaW5HZW5lcmF0b3IsXG4gICAgICAgIG9sZExhYmVscyA9IHRoaXMubGFiZWxzO1xuICAgIHRoaXMuaW5GdW5jdGlvbiA9IHRydWU7dGhpcy5pbkdlbmVyYXRvciA9IG5vZGUuZ2VuZXJhdG9yO3RoaXMubGFiZWxzID0gW107XG4gICAgbm9kZS5ib2R5ID0gdGhpcy5wYXJzZUJsb2NrKHRydWUpO1xuICAgIG5vZGUuZXhwcmVzc2lvbiA9IGZhbHNlO1xuICAgIHRoaXMuaW5GdW5jdGlvbiA9IG9sZEluRnVuYzt0aGlzLmluR2VuZXJhdG9yID0gb2xkSW5HZW47dGhpcy5sYWJlbHMgPSBvbGRMYWJlbHM7XG4gIH1cblxuICAvLyBJZiB0aGlzIGlzIGEgc3RyaWN0IG1vZGUgZnVuY3Rpb24sIHZlcmlmeSB0aGF0IGFyZ3VtZW50IG5hbWVzXG4gIC8vIGFyZSBub3QgcmVwZWF0ZWQsIGFuZCBpdCBkb2VzIG5vdCB0cnkgdG8gYmluZCB0aGUgd29yZHMgYGV2YWxgXG4gIC8vIG9yIGBhcmd1bWVudHNgLlxuICBpZiAodGhpcy5zdHJpY3QgfHwgIWlzRXhwcmVzc2lvbiAmJiBub2RlLmJvZHkuYm9keS5sZW5ndGggJiYgdGhpcy5pc1VzZVN0cmljdChub2RlLmJvZHkuYm9keVswXSkpIHtcbiAgICB2YXIgbmFtZUhhc2ggPSB7fSxcbiAgICAgICAgb2xkU3RyaWN0ID0gdGhpcy5zdHJpY3Q7XG4gICAgdGhpcy5zdHJpY3QgPSB0cnVlO1xuICAgIGlmIChub2RlLmlkKSB0aGlzLmNoZWNrTFZhbChub2RlLmlkLCB0cnVlKTtcbiAgICBmb3IgKHZhciBpID0gMDsgaSA8IG5vZGUucGFyYW1zLmxlbmd0aDsgaSsrKSB7XG4gICAgICB0aGlzLmNoZWNrTFZhbChub2RlLnBhcmFtc1tpXSwgdHJ1ZSwgbmFtZUhhc2gpO1xuICAgIH10aGlzLnN0cmljdCA9IG9sZFN0cmljdDtcbiAgfVxufTtcblxuLy8gUGFyc2VzIGEgY29tbWEtc2VwYXJhdGVkIGxpc3Qgb2YgZXhwcmVzc2lvbnMsIGFuZCByZXR1cm5zIHRoZW0gYXNcbi8vIGFuIGFycmF5LiBgY2xvc2VgIGlzIHRoZSB0b2tlbiB0eXBlIHRoYXQgZW5kcyB0aGUgbGlzdCwgYW5kXG4vLyBgYWxsb3dFbXB0eWAgY2FuIGJlIHR1cm5lZCBvbiB0byBhbGxvdyBzdWJzZXF1ZW50IGNvbW1hcyB3aXRoXG4vLyBub3RoaW5nIGluIGJldHdlZW4gdGhlbSB0byBiZSBwYXJzZWQgYXMgYG51bGxgICh3aGljaCBpcyBuZWVkZWRcbi8vIGZvciBhcnJheSBsaXRlcmFscykuXG5cbnBwLnBhcnNlRXhwckxpc3QgPSBmdW5jdGlvbiAoY2xvc2UsIGFsbG93VHJhaWxpbmdDb21tYSwgYWxsb3dFbXB0eSwgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcykge1xuICB2YXIgZWx0cyA9IFtdLFxuICAgICAgZmlyc3QgPSB0cnVlO1xuICB3aGlsZSAoIXRoaXMuZWF0KGNsb3NlKSkge1xuICAgIGlmICghZmlyc3QpIHtcbiAgICAgIHRoaXMuZXhwZWN0KF90b2tlbnR5cGUudHlwZXMuY29tbWEpO1xuICAgICAgaWYgKGFsbG93VHJhaWxpbmdDb21tYSAmJiB0aGlzLmFmdGVyVHJhaWxpbmdDb21tYShjbG9zZSkpIGJyZWFrO1xuICAgIH0gZWxzZSBmaXJzdCA9IGZhbHNlO1xuXG4gICAgdmFyIGVsdCA9IHVuZGVmaW5lZDtcbiAgICBpZiAoYWxsb3dFbXB0eSAmJiB0aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuY29tbWEpIGVsdCA9IG51bGw7ZWxzZSBpZiAodGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLmVsbGlwc2lzKSBlbHQgPSB0aGlzLnBhcnNlU3ByZWFkKHJlZlNob3J0aGFuZERlZmF1bHRQb3MpO2Vsc2UgZWx0ID0gdGhpcy5wYXJzZU1heWJlQXNzaWduKGZhbHNlLCByZWZTaG9ydGhhbmREZWZhdWx0UG9zKTtcbiAgICBlbHRzLnB1c2goZWx0KTtcbiAgfVxuICByZXR1cm4gZWx0cztcbn07XG5cbi8vIFBhcnNlIHRoZSBuZXh0IHRva2VuIGFzIGFuIGlkZW50aWZpZXIuIElmIGBsaWJlcmFsYCBpcyB0cnVlICh1c2VkXG4vLyB3aGVuIHBhcnNpbmcgcHJvcGVydGllcyksIGl0IHdpbGwgYWxzbyBjb252ZXJ0IGtleXdvcmRzIGludG9cbi8vIGlkZW50aWZpZXJzLlxuXG5wcC5wYXJzZUlkZW50ID0gZnVuY3Rpb24gKGxpYmVyYWwpIHtcbiAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICBpZiAobGliZXJhbCAmJiB0aGlzLm9wdGlvbnMuYWxsb3dSZXNlcnZlZCA9PSBcIm5ldmVyXCIpIGxpYmVyYWwgPSBmYWxzZTtcbiAgaWYgKHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5uYW1lKSB7XG4gICAgaWYgKCFsaWJlcmFsICYmICghdGhpcy5vcHRpb25zLmFsbG93UmVzZXJ2ZWQgJiYgdGhpcy5pc1Jlc2VydmVkV29yZCh0aGlzLnZhbHVlKSB8fCB0aGlzLnN0cmljdCAmJiBfaWRlbnRpZmllci5yZXNlcnZlZFdvcmRzLnN0cmljdCh0aGlzLnZhbHVlKSAmJiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYgfHwgdGhpcy5pbnB1dC5zbGljZSh0aGlzLnN0YXJ0LCB0aGlzLmVuZCkuaW5kZXhPZihcIlxcXFxcIikgPT0gLTEpKSkgdGhpcy5yYWlzZSh0aGlzLnN0YXJ0LCBcIlRoZSBrZXl3b3JkICdcIiArIHRoaXMudmFsdWUgKyBcIicgaXMgcmVzZXJ2ZWRcIik7XG4gICAgbm9kZS5uYW1lID0gdGhpcy52YWx1ZTtcbiAgfSBlbHNlIGlmIChsaWJlcmFsICYmIHRoaXMudHlwZS5rZXl3b3JkKSB7XG4gICAgbm9kZS5uYW1lID0gdGhpcy50eXBlLmtleXdvcmQ7XG4gIH0gZWxzZSB7XG4gICAgdGhpcy51bmV4cGVjdGVkKCk7XG4gIH1cbiAgdGhpcy5uZXh0KCk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJJZGVudGlmaWVyXCIpO1xufTtcblxuLy8gUGFyc2VzIHlpZWxkIGV4cHJlc3Npb24gaW5zaWRlIGdlbmVyYXRvci5cblxucHAucGFyc2VZaWVsZCA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICB0aGlzLm5leHQoKTtcbiAgaWYgKHRoaXMudHlwZSA9PSBfdG9rZW50eXBlLnR5cGVzLnNlbWkgfHwgdGhpcy5jYW5JbnNlcnRTZW1pY29sb24oKSB8fCB0aGlzLnR5cGUgIT0gX3Rva2VudHlwZS50eXBlcy5zdGFyICYmICF0aGlzLnR5cGUuc3RhcnRzRXhwcikge1xuICAgIG5vZGUuZGVsZWdhdGUgPSBmYWxzZTtcbiAgICBub2RlLmFyZ3VtZW50ID0gbnVsbDtcbiAgfSBlbHNlIHtcbiAgICBub2RlLmRlbGVnYXRlID0gdGhpcy5lYXQoX3Rva2VudHlwZS50eXBlcy5zdGFyKTtcbiAgICBub2RlLmFyZ3VtZW50ID0gdGhpcy5wYXJzZU1heWJlQXNzaWduKCk7XG4gIH1cbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIllpZWxkRXhwcmVzc2lvblwiKTtcbn07XG5cbi8vIFBhcnNlcyBhcnJheSBhbmQgZ2VuZXJhdG9yIGNvbXByZWhlbnNpb25zLlxuXG5wcC5wYXJzZUNvbXByZWhlbnNpb24gPSBmdW5jdGlvbiAobm9kZSwgaXNHZW5lcmF0b3IpIHtcbiAgbm9kZS5ibG9ja3MgPSBbXTtcbiAgd2hpbGUgKHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5fZm9yKSB7XG4gICAgdmFyIGJsb2NrID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgICB0aGlzLm5leHQoKTtcbiAgICB0aGlzLmV4cGVjdChfdG9rZW50eXBlLnR5cGVzLnBhcmVuTCk7XG4gICAgYmxvY2subGVmdCA9IHRoaXMucGFyc2VCaW5kaW5nQXRvbSgpO1xuICAgIHRoaXMuY2hlY2tMVmFsKGJsb2NrLmxlZnQsIHRydWUpO1xuICAgIHRoaXMuZXhwZWN0Q29udGV4dHVhbChcIm9mXCIpO1xuICAgIGJsb2NrLnJpZ2h0ID0gdGhpcy5wYXJzZUV4cHJlc3Npb24oKTtcbiAgICB0aGlzLmV4cGVjdChfdG9rZW50eXBlLnR5cGVzLnBhcmVuUik7XG4gICAgbm9kZS5ibG9ja3MucHVzaCh0aGlzLmZpbmlzaE5vZGUoYmxvY2ssIFwiQ29tcHJlaGVuc2lvbkJsb2NrXCIpKTtcbiAgfVxuICBub2RlLmZpbHRlciA9IHRoaXMuZWF0KF90b2tlbnR5cGUudHlwZXMuX2lmKSA/IHRoaXMucGFyc2VQYXJlbkV4cHJlc3Npb24oKSA6IG51bGw7XG4gIG5vZGUuYm9keSA9IHRoaXMucGFyc2VFeHByZXNzaW9uKCk7XG4gIHRoaXMuZXhwZWN0KGlzR2VuZXJhdG9yID8gX3Rva2VudHlwZS50eXBlcy5wYXJlblIgOiBfdG9rZW50eXBlLnR5cGVzLmJyYWNrZXRSKTtcbiAgbm9kZS5nZW5lcmF0b3IgPSBpc0dlbmVyYXRvcjtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkNvbXByZWhlbnNpb25FeHByZXNzaW9uXCIpO1xufTtcblxufSx7XCIuL2lkZW50aWZpZXJcIjoyLFwiLi9zdGF0ZVwiOjEwLFwiLi90b2tlbnR5cGVcIjoxNCxcIi4vdXRpbFwiOjE1fV0sMjpbZnVuY3Rpb24oX2RlcmVxXyxtb2R1bGUsZXhwb3J0cyl7XG4vLyBUaGlzIGlzIGEgdHJpY2sgdGFrZW4gZnJvbSBFc3ByaW1hLiBJdCB0dXJucyBvdXQgdGhhdCwgb25cbi8vIG5vbi1DaHJvbWUgYnJvd3NlcnMsIHRvIGNoZWNrIHdoZXRoZXIgYSBzdHJpbmcgaXMgaW4gYSBzZXQsIGFcbi8vIHByZWRpY2F0ZSBjb250YWluaW5nIGEgYmlnIHVnbHkgYHN3aXRjaGAgc3RhdGVtZW50IGlzIGZhc3RlciB0aGFuXG4vLyBhIHJlZ3VsYXIgZXhwcmVzc2lvbiwgYW5kIG9uIENocm9tZSB0aGUgdHdvIGFyZSBhYm91dCBvbiBwYXIuXG4vLyBUaGlzIGZ1bmN0aW9uIHVzZXMgYGV2YWxgIChub24tbGV4aWNhbCkgdG8gcHJvZHVjZSBzdWNoIGFcbi8vIHByZWRpY2F0ZSBmcm9tIGEgc3BhY2Utc2VwYXJhdGVkIHN0cmluZyBvZiB3b3Jkcy5cbi8vXG4vLyBJdCBzdGFydHMgYnkgc29ydGluZyB0aGUgd29yZHMgYnkgbGVuZ3RoLlxuXG5cInVzZSBzdHJpY3RcIjtcblxuZXhwb3J0cy5fX2VzTW9kdWxlID0gdHJ1ZTtcbmV4cG9ydHMuaXNJZGVudGlmaWVyU3RhcnQgPSBpc0lkZW50aWZpZXJTdGFydDtcbmV4cG9ydHMuaXNJZGVudGlmaWVyQ2hhciA9IGlzSWRlbnRpZmllckNoYXI7XG5mdW5jdGlvbiBtYWtlUHJlZGljYXRlKHdvcmRzKSB7XG4gIHdvcmRzID0gd29yZHMuc3BsaXQoXCIgXCIpO1xuICB2YXIgZiA9IFwiXCIsXG4gICAgICBjYXRzID0gW107XG4gIG91dDogZm9yICh2YXIgaSA9IDA7IGkgPCB3b3Jkcy5sZW5ndGg7ICsraSkge1xuICAgIGZvciAodmFyIGogPSAwOyBqIDwgY2F0cy5sZW5ndGg7ICsraikge1xuICAgICAgaWYgKGNhdHNbal1bMF0ubGVuZ3RoID09IHdvcmRzW2ldLmxlbmd0aCkge1xuICAgICAgICBjYXRzW2pdLnB1c2god29yZHNbaV0pO1xuICAgICAgICBjb250aW51ZSBvdXQ7XG4gICAgICB9XG4gICAgfWNhdHMucHVzaChbd29yZHNbaV1dKTtcbiAgfVxuICBmdW5jdGlvbiBjb21wYXJlVG8oYXJyKSB7XG4gICAgaWYgKGFyci5sZW5ndGggPT0gMSkgcmV0dXJuIGYgKz0gXCJyZXR1cm4gc3RyID09PSBcIiArIEpTT04uc3RyaW5naWZ5KGFyclswXSkgKyBcIjtcIjtcbiAgICBmICs9IFwic3dpdGNoKHN0cil7XCI7XG4gICAgZm9yICh2YXIgaSA9IDA7IGkgPCBhcnIubGVuZ3RoOyArK2kpIHtcbiAgICAgIGYgKz0gXCJjYXNlIFwiICsgSlNPTi5zdHJpbmdpZnkoYXJyW2ldKSArIFwiOlwiO1xuICAgIH1mICs9IFwicmV0dXJuIHRydWV9cmV0dXJuIGZhbHNlO1wiO1xuICB9XG5cbiAgLy8gV2hlbiB0aGVyZSBhcmUgbW9yZSB0aGFuIHRocmVlIGxlbmd0aCBjYXRlZ29yaWVzLCBhbiBvdXRlclxuICAvLyBzd2l0Y2ggZmlyc3QgZGlzcGF0Y2hlcyBvbiB0aGUgbGVuZ3RocywgdG8gc2F2ZSBvbiBjb21wYXJpc29ucy5cblxuICBpZiAoY2F0cy5sZW5ndGggPiAzKSB7XG4gICAgY2F0cy5zb3J0KGZ1bmN0aW9uIChhLCBiKSB7XG4gICAgICByZXR1cm4gYi5sZW5ndGggLSBhLmxlbmd0aDtcbiAgICB9KTtcbiAgICBmICs9IFwic3dpdGNoKHN0ci5sZW5ndGgpe1wiO1xuICAgIGZvciAodmFyIGkgPSAwOyBpIDwgY2F0cy5sZW5ndGg7ICsraSkge1xuICAgICAgdmFyIGNhdCA9IGNhdHNbaV07XG4gICAgICBmICs9IFwiY2FzZSBcIiArIGNhdFswXS5sZW5ndGggKyBcIjpcIjtcbiAgICAgIGNvbXBhcmVUbyhjYXQpO1xuICAgIH1cbiAgICBmICs9IFwifVwiXG5cbiAgICAvLyBPdGhlcndpc2UsIHNpbXBseSBnZW5lcmF0ZSBhIGZsYXQgYHN3aXRjaGAgc3RhdGVtZW50LlxuXG4gICAgO1xuICB9IGVsc2Uge1xuICAgIGNvbXBhcmVUbyh3b3Jkcyk7XG4gIH1cbiAgcmV0dXJuIG5ldyBGdW5jdGlvbihcInN0clwiLCBmKTtcbn1cblxuLy8gUmVzZXJ2ZWQgd29yZCBsaXN0cyBmb3IgdmFyaW91cyBkaWFsZWN0cyBvZiB0aGUgbGFuZ3VhZ2VcblxudmFyIHJlc2VydmVkV29yZHMgPSB7XG4gIDM6IG1ha2VQcmVkaWNhdGUoXCJhYnN0cmFjdCBib29sZWFuIGJ5dGUgY2hhciBjbGFzcyBkb3VibGUgZW51bSBleHBvcnQgZXh0ZW5kcyBmaW5hbCBmbG9hdCBnb3RvIGltcGxlbWVudHMgaW1wb3J0IGludCBpbnRlcmZhY2UgbG9uZyBuYXRpdmUgcGFja2FnZSBwcml2YXRlIHByb3RlY3RlZCBwdWJsaWMgc2hvcnQgc3RhdGljIHN1cGVyIHN5bmNocm9uaXplZCB0aHJvd3MgdHJhbnNpZW50IHZvbGF0aWxlXCIpLFxuICA1OiBtYWtlUHJlZGljYXRlKFwiY2xhc3MgZW51bSBleHRlbmRzIHN1cGVyIGNvbnN0IGV4cG9ydCBpbXBvcnRcIiksXG4gIDY6IG1ha2VQcmVkaWNhdGUoXCJlbnVtIGF3YWl0XCIpLFxuICBzdHJpY3Q6IG1ha2VQcmVkaWNhdGUoXCJpbXBsZW1lbnRzIGludGVyZmFjZSBsZXQgcGFja2FnZSBwcml2YXRlIHByb3RlY3RlZCBwdWJsaWMgc3RhdGljIHlpZWxkXCIpLFxuICBzdHJpY3RCaW5kOiBtYWtlUHJlZGljYXRlKFwiZXZhbCBhcmd1bWVudHNcIilcbn07XG5cbmV4cG9ydHMucmVzZXJ2ZWRXb3JkcyA9IHJlc2VydmVkV29yZHM7XG4vLyBBbmQgdGhlIGtleXdvcmRzXG5cbnZhciBlY21hNUFuZExlc3NLZXl3b3JkcyA9IFwiYnJlYWsgY2FzZSBjYXRjaCBjb250aW51ZSBkZWJ1Z2dlciBkZWZhdWx0IGRvIGVsc2UgZmluYWxseSBmb3IgZnVuY3Rpb24gaWYgcmV0dXJuIHN3aXRjaCB0aHJvdyB0cnkgdmFyIHdoaWxlIHdpdGggbnVsbCB0cnVlIGZhbHNlIGluc3RhbmNlb2YgdHlwZW9mIHZvaWQgZGVsZXRlIG5ldyBpbiB0aGlzXCI7XG5cbnZhciBrZXl3b3JkcyA9IHtcbiAgNTogbWFrZVByZWRpY2F0ZShlY21hNUFuZExlc3NLZXl3b3JkcyksXG4gIDY6IG1ha2VQcmVkaWNhdGUoZWNtYTVBbmRMZXNzS2V5d29yZHMgKyBcIiBsZXQgY29uc3QgY2xhc3MgZXh0ZW5kcyBleHBvcnQgaW1wb3J0IHlpZWxkIHN1cGVyXCIpXG59O1xuXG5leHBvcnRzLmtleXdvcmRzID0ga2V5d29yZHM7XG4vLyAjIyBDaGFyYWN0ZXIgY2F0ZWdvcmllc1xuXG4vLyBCaWcgdWdseSByZWd1bGFyIGV4cHJlc3Npb25zIHRoYXQgbWF0Y2ggY2hhcmFjdGVycyBpbiB0aGVcbi8vIHdoaXRlc3BhY2UsIGlkZW50aWZpZXIsIGFuZCBpZGVudGlmaWVyLXN0YXJ0IGNhdGVnb3JpZXMuIFRoZXNlXG4vLyBhcmUgb25seSBhcHBsaWVkIHdoZW4gYSBjaGFyYWN0ZXIgaXMgZm91bmQgdG8gYWN0dWFsbHkgaGF2ZSBhXG4vLyBjb2RlIHBvaW50IGFib3ZlIDEyOC5cbi8vIEdlbmVyYXRlZCBieSBgdG9vbHMvZ2VuZXJhdGUtaWRlbnRpZmllci1yZWdleC5qc2AuXG5cbnZhciBub25BU0NJSWlkZW50aWZpZXJTdGFydENoYXJzID0gXCLCqsK1wrrDgC3DlsOYLcO2w7gty4HLhi3LkcugLcuky6zLrs2wLc20zbbNt826Lc29zb/Ohs6ILc6KzozOji3Ooc6jLc+1z7ct0oHSii3Ur9SxLdWW1ZnVoS3Wh9eQLdeq17At17LYoC3Zitmu2a/ZsS3bk9uV26Xbptuu26/bui3bvNu/3JDcki3cr92NLd6l3rHfii3fqt+037XfuuCggC3goJXgoJrgoKTgoKjgoYAt4KGY4KKgLeCisuCkhC3gpLngpL3gpZDgpZgt4KWh4KWxLeCmgOCmhS3gpozgpo/gppDgppMt4Kao4KaqLeCmsOCmsuCmti3gprngpr3gp47gp5zgp53gp58t4Keh4Kew4Kex4KiFLeCoiuCoj+CokOCoky3gqKjgqKot4Kiw4Kiy4Kiz4Ki14Ki24Ki44Ki54KmZLeCpnOCpnuCpsi3gqbTgqoUt4KqN4KqPLeCqkeCqky3gqqjgqqot4Kqw4Kqy4Kqz4Kq1LeCqueCqveCrkOCroOCroeCshS3grIzgrI/grJDgrJMt4Kyo4KyqLeCssOCssuCss+CstS3grLngrL3grZzgrZ3grZ8t4K2h4K2x4K6D4K6FLeCuiuCuji3grpDgrpIt4K6V4K6Z4K6a4K6c4K6e4K6f4K6j4K6k4K6oLeCuquCuri3grrngr5DgsIUt4LCM4LCOLeCwkOCwki3gsKjgsKot4LC54LC94LGY4LGZ4LGg4LGh4LKFLeCyjOCyji3gspDgspIt4LKo4LKqLeCys+CytS3gsrngsr3gs57gs6Dgs6Hgs7Hgs7LgtIUt4LSM4LSOLeC0kOC0ki3gtLrgtL3gtY7gtaDgtaHgtbot4LW/4LaFLeC2luC2mi3gtrHgtrMt4La74La94LeALeC3huC4gS3guLDguLLguLPguYAt4LmG4LqB4LqC4LqE4LqH4LqI4LqK4LqN4LqULeC6l+C6mS3gup/guqEt4Lqj4Lql4Lqn4Lqq4Lqr4LqtLeC6sOC6suC6s+C6veC7gC3gu4Tgu4bgu5wt4Luf4LyA4L2ALeC9h+C9iS3gvazgvogt4L6M4YCALeGAquGAv+GBkC3hgZXhgZot4YGd4YGh4YGl4YGm4YGuLeGBsOGBtS3hgoHhgo7hgqAt4YOF4YOH4YON4YOQLeGDuuGDvC3hiYjhiYot4YmN4YmQLeGJluGJmOGJmi3hiZ3hiaAt4YqI4YqKLeGKjeGKkC3hirDhirIt4Yq14Yq4LeGKvuGLgOGLgi3hi4Xhi4gt4YuW4YuYLeGMkOGMki3hjJXhjJgt4Y2a4Y6ALeGOj+GOoC3hj7ThkIEt4Zms4ZmvLeGZv+GagS3hmprhmqAt4Zuq4ZuuLeGbuOGcgC3hnIzhnI4t4ZyR4ZygLeGcseGdgC3hnZHhnaAt4Z2s4Z2uLeGdsOGegC3hnrPhn5fhn5zhoKAt4aG34aKALeGiqOGiquGisC3ho7XhpIAt4aSe4aWQLeGlreGlsC3hpbThpoAt4aar4aeBLeGnh+GogC3hqJbhqKAt4amU4aqn4ayFLeGss+GthS3hrYvhroMt4a6g4a6u4a6v4a66LeGvpeGwgC3hsKPhsY0t4bGP4bGaLeGxveGzqS3hs6zhs64t4bOx4bO14bO24bSALeG2v+G4gC3hvJXhvJgt4byd4bygLeG9heG9iC3hvY3hvZAt4b2X4b2Z4b2b4b2d4b2fLeG9veG+gC3hvrThvrYt4b684b6+4b+CLeG/hOG/hi3hv4zhv5At4b+T4b+WLeG/m+G/oC3hv6zhv7It4b+04b+2LeG/vOKBseKBv+KCkC3igpzihILihIfihIot4oST4oSV4oSYLeKEneKEpOKEpuKEqOKEqi3ihLnihLwt4oS/4oWFLeKFieKFjuKFoC3ihojisIAt4rCu4rCwLeKxnuKxoC3is6Tis6st4rOu4rOy4rOz4rSALeK0peK0p+K0reK0sC3itafita/itoAt4raW4ragLeK2puK2qC3itq7itrAt4ra24ra4LeK2vuK3gC3it4bit4gt4reO4reQLeK3luK3mC3it57jgIUt44CH44ChLeOAqeOAsS3jgLXjgLgt44C844GBLeOCluOCmy3jgp/jgqEt44O644O8LeODv+OEhS3jhK3jhLEt44aO44agLeOGuuOHsC3jh7/jkIAt5La15LiALem/jOqAgC3qkozqk5At6pO96pSALeqYjOqYkC3qmJ/qmKrqmKvqmYAt6pmu6pm/LeqaneqaoC3qm6/qnJct6pyf6pyiLeqeiOqeiy3qno7qnpAt6p6t6p6w6p6x6p+3Leqggeqggy3qoIXqoIct6qCK6qCMLeqgouqhgC3qobPqooIt6qKz6qOyLeqjt+qju+qkii3qpKXqpLAt6qWG6qWgLeqlvOqmhC3qprLqp4/qp6At6qek6qemLeqnr+qnui3qp77qqIAt6qio6qmALeqpguqphC3qqYvqqaAt6qm26qm66qm+Leqqr+qqseqqteqqtuqquS3qqr3qq4Dqq4Lqq5st6qud6qugLeqrquqrsi3qq7TqrIEt6qyG6qyJLeqsjuqskS3qrJbqrKAt6qym6qyoLeqsruqssC3qrZrqrZwt6q2f6q2k6q2l6q+ALeqvouqwgC3tnqPtnrAt7Z+G7Z+LLe2fu++kgC3vqa3vqbAt76uZ76yALe+shu+sky3vrJfvrJ3vrJ8t76yo76yqLe+stu+suC3vrLzvrL7vrYDvrYHvrYPvrYTvrYYt766x76+TLe+0ve+1kC3vto/vtpIt77eH77ewLe+3u++5sC3vubTvubYt77u877yhLe+8uu+9gS3vvZrvvaYt776+77+CLe+/h++/ii3vv4/vv5It77+X77+aLe+/nFwiO1xudmFyIG5vbkFTQ0lJaWRlbnRpZmllckNoYXJzID0gXCLigIzigI3Ct8yALc2vzofSgy3Sh9aRLda91r/XgdeC14TXhdeH2JAt2JrZiy3Zqdmw25Yt25zbny3bpNun26jbqi3brduwLdu53JHcsC3dit6mLd6w34At34nfqy3fs+Cgli3goJngoJst4KCj4KClLeCgp+CgqS3goK3goZkt4KGb4KOkLeCkg+Ckui3gpLzgpL4t4KWP4KWRLeCll+ClouClo+Clpi3gpa/gpoEt4KaD4Ka84Ka+LeCnhOCnh+CniOCniy3gp43gp5fgp6Lgp6Pgp6Yt4Kev4KiBLeCog+CovOCovi3gqYLgqYfgqYjgqYst4KmN4KmR4KmmLeCpseCpteCqgS3gqoPgqrzgqr4t4KuF4KuHLeCrieCriy3gq43gq6Lgq6Pgq6Yt4Kuv4KyBLeCsg+CsvOCsvi3grYTgrYfgrYjgrYst4K2N4K2W4K2X4K2i4K2j4K2mLeCtr+CuguCuvi3gr4Lgr4Yt4K+I4K+KLeCvjeCvl+Cvpi3gr6/gsIAt4LCD4LC+LeCxhOCxhi3gsYjgsYot4LGN4LGV4LGW4LGi4LGj4LGmLeCxr+CygS3gsoPgsrzgsr4t4LOE4LOGLeCziOCzii3gs43gs5Xgs5bgs6Lgs6Pgs6Yt4LOv4LSBLeC0g+C0vi3gtYTgtYYt4LWI4LWKLeC1jeC1l+C1ouC1o+C1pi3gta/gtoLgtoPgt4rgt48t4LeU4LeW4LeYLeC3n+C3pi3gt6/gt7Lgt7PguLHguLQt4Li64LmHLeC5juC5kC3guZngurHgurQt4Lq54Lq74Lq84LuILeC7jeC7kC3gu5ngvJjgvJngvKAt4Lyp4Ly14Ly34Ly54Ly+4Ly/4L2xLeC+hOC+huC+h+C+jS3gvpfgvpkt4L684L+G4YCrLeGAvuGBgC3hgYnhgZYt4YGZ4YGeLeGBoOGBoi3hgaThgact4YGt4YGxLeGBtOGCgi3hgo3hgo8t4YKd4Y2dLeGNn+GNqS3hjbHhnJIt4ZyU4ZyyLeGctOGdkuGdk+GdsuGds+GetC3hn5Phn53hn6At4Z+p4aCLLeGgjeGgkC3hoJnhoqnhpKAt4aSr4aSwLeGku+Glhi3hpY/hprAt4aeA4aeI4aeJ4aeQLeGnmuGoly3hqJvhqZUt4ame4amgLeGpvOGpvy3hqonhqpAt4aqZ4aqwLeGqveGsgC3hrIThrLQt4a2E4a2QLeGtmeGtqy3hrbPhroAt4a6C4a6hLeGureGusC3hrrnhr6Yt4a+z4bCkLeGwt+GxgC3hsYnhsZAt4bGZ4bOQLeGzkuGzlC3hs6jhs63hs7It4bO04bO44bO54beALeG3teG3vC3ht7/igL/igYDigZTig5At4oOc4oOh4oOlLeKDsOKzry3is7Hitb/it6At4re/44CqLeOAr+OCmeOCmuqYoC3qmKnqma/qmbQt6pm96pqf6puw6pux6qCC6qCG6qCL6qCjLeqgp+qigOqigeqitC3qo4Tqo5At6qOZ6qOgLeqjseqkgC3qpInqpKYt6qSt6qWHLeqlk+qmgC3qpoPqprMt6qeA6qeQLeqnmeqnpeqnsC3qp7nqqKkt6qi26qmD6qmM6qmN6qmQLeqpmeqpuy3qqb3qqrDqqrIt6qq06qq36qq46qq+6qq/6quB6qurLeqrr+qrteqrtuqvoy3qr6rqr6zqr63qr7At6q+576ye77iALe+4j++4oC3vuK3vuLPvuLTvuY0t77mP77yQLe+8me+8v1wiO1xuXG52YXIgbm9uQVNDSUlpZGVudGlmaWVyU3RhcnQgPSBuZXcgUmVnRXhwKFwiW1wiICsgbm9uQVNDSUlpZGVudGlmaWVyU3RhcnRDaGFycyArIFwiXVwiKTtcbnZhciBub25BU0NJSWlkZW50aWZpZXIgPSBuZXcgUmVnRXhwKFwiW1wiICsgbm9uQVNDSUlpZGVudGlmaWVyU3RhcnRDaGFycyArIG5vbkFTQ0lJaWRlbnRpZmllckNoYXJzICsgXCJdXCIpO1xuXG5ub25BU0NJSWlkZW50aWZpZXJTdGFydENoYXJzID0gbm9uQVNDSUlpZGVudGlmaWVyQ2hhcnMgPSBudWxsO1xuXG4vLyBUaGVzZSBhcmUgYSBydW4tbGVuZ3RoIGFuZCBvZmZzZXQgZW5jb2RlZCByZXByZXNlbnRhdGlvbiBvZiB0aGVcbi8vID4weGZmZmYgY29kZSBwb2ludHMgdGhhdCBhcmUgYSB2YWxpZCBwYXJ0IG9mIGlkZW50aWZpZXJzLiBUaGVcbi8vIG9mZnNldCBzdGFydHMgYXQgMHgxMDAwMCwgYW5kIGVhY2ggcGFpciBvZiBudW1iZXJzIHJlcHJlc2VudHMgYW5cbi8vIG9mZnNldCB0byB0aGUgbmV4dCByYW5nZSwgYW5kIHRoZW4gYSBzaXplIG9mIHRoZSByYW5nZS4gVGhleSB3ZXJlXG4vLyBnZW5lcmF0ZWQgYnkgdG9vbHMvZ2VuZXJhdGUtaWRlbnRpZmllci1yZWdleC5qc1xudmFyIGFzdHJhbElkZW50aWZpZXJTdGFydENvZGVzID0gWzAsIDExLCAyLCAyNSwgMiwgMTgsIDIsIDEsIDIsIDE0LCAzLCAxMywgMzUsIDEyMiwgNzAsIDUyLCAyNjgsIDI4LCA0LCA0OCwgNDgsIDMxLCAxNywgMjYsIDYsIDM3LCAxMSwgMjksIDMsIDM1LCA1LCA3LCAyLCA0LCA0MywgMTU3LCA5OSwgMzksIDksIDUxLCAxNTcsIDMxMCwgMTAsIDIxLCAxMSwgNywgMTUzLCA1LCAzLCAwLCAyLCA0MywgMiwgMSwgNCwgMCwgMywgMjIsIDExLCAyMiwgMTAsIDMwLCA5OCwgMjEsIDExLCAyNSwgNzEsIDU1LCA3LCAxLCA2NSwgMCwgMTYsIDMsIDIsIDIsIDIsIDI2LCA0NSwgMjgsIDQsIDI4LCAzNiwgNywgMiwgMjcsIDI4LCA1MywgMTEsIDIxLCAxMSwgMTgsIDE0LCAxNywgMTExLCA3MiwgOTU1LCA1MiwgNzYsIDQ0LCAzMywgMjQsIDI3LCAzNSwgNDIsIDM0LCA0LCAwLCAxMywgNDcsIDE1LCAzLCAyMiwgMCwgMzgsIDE3LCAyLCAyNCwgMTMzLCA0NiwgMzksIDcsIDMsIDEsIDMsIDIxLCAyLCA2LCAyLCAxLCAyLCA0LCA0LCAwLCAzMiwgNCwgMjg3LCA0NywgMjEsIDEsIDIsIDAsIDE4NSwgNDYsIDgyLCA0NywgMjEsIDAsIDYwLCA0MiwgNTAyLCA2MywgMzIsIDAsIDQ0OSwgNTYsIDEyODgsIDkyMCwgMTA0LCAxMTAsIDI5NjIsIDEwNzAsIDEzMjY2LCA1NjgsIDgsIDMwLCAxMTQsIDI5LCAxOSwgNDcsIDE3LCAzLCAzMiwgMjAsIDYsIDE4LCA4ODEsIDY4LCAxMiwgMCwgNjcsIDEyLCAxNjQ4MSwgMSwgMzA3MSwgMTA2LCA2LCAxMiwgNCwgOCwgOCwgOSwgNTk5MSwgODQsIDIsIDcwLCAyLCAxLCAzLCAwLCAzLCAxLCAzLCAzLCAyLCAxMSwgMiwgMCwgMiwgNiwgMiwgNjQsIDIsIDMsIDMsIDcsIDIsIDYsIDIsIDI3LCAyLCAzLCAyLCA0LCAyLCAwLCA0LCA2LCAyLCAzMzksIDMsIDI0LCAyLCAyNCwgMiwgMzAsIDIsIDI0LCAyLCAzMCwgMiwgMjQsIDIsIDMwLCAyLCAyNCwgMiwgMzAsIDIsIDI0LCAyLCA3LCA0MTQ5LCAxOTYsIDEzNDAsIDMsIDIsIDI2LCAyLCAxLCAyLCAwLCAzLCAwLCAyLCA5LCAyLCAzLCAyLCAwLCAyLCAwLCA3LCAwLCA1LCAwLCAyLCAwLCAyLCAwLCAyLCAyLCAyLCAxLCAyLCAwLCAzLCAwLCAyLCAwLCAyLCAwLCAyLCAwLCAyLCAwLCAyLCAxLCAyLCAwLCAzLCAzLCAyLCA2LCAyLCAzLCAyLCAzLCAyLCAwLCAyLCA5LCAyLCAxNiwgNiwgMiwgMiwgNCwgMiwgMTYsIDQ0MjEsIDQyNzEwLCA0MiwgNDE0OCwgMTIsIDIyMSwgMTYzNTUsIDU0MV07XG52YXIgYXN0cmFsSWRlbnRpZmllckNvZGVzID0gWzUwOSwgMCwgMjI3LCAwLCAxNTAsIDQsIDI5NCwgOSwgMTM2OCwgMiwgMiwgMSwgNiwgMywgNDEsIDIsIDUsIDAsIDE2NiwgMSwgMTMwNiwgMiwgNTQsIDE0LCAzMiwgOSwgMTYsIDMsIDQ2LCAxMCwgNTQsIDksIDcsIDIsIDM3LCAxMywgMiwgOSwgNTIsIDAsIDEzLCAyLCA0OSwgMTMsIDE2LCA5LCA4MywgMTEsIDE2OCwgMTEsIDYsIDksIDgsIDIsIDU3LCAwLCAyLCA2LCAzLCAxLCAzLCAyLCAxMCwgMCwgMTEsIDEsIDMsIDYsIDQsIDQsIDMxNiwgMTksIDEzLCA5LCAyMTQsIDYsIDMsIDgsIDExMiwgMTYsIDE2LCA5LCA4MiwgMTIsIDksIDksIDUzNSwgOSwgMjA4NTUsIDksIDEzNSwgNCwgNjAsIDYsIDI2LCA5LCAxMDE2LCA0NSwgMTcsIDMsIDE5NzIzLCAxLCA1MzE5LCA0LCA0LCA1LCA5LCA3LCAzLCA2LCAzMSwgMywgMTQ5LCAyLCAxNDE4LCA0OSwgNDMwNSwgNiwgNzkyNjE4LCAyMzldO1xuXG4vLyBUaGlzIGhhcyBhIGNvbXBsZXhpdHkgbGluZWFyIHRvIHRoZSB2YWx1ZSBvZiB0aGUgY29kZS4gVGhlXG4vLyBhc3N1bXB0aW9uIGlzIHRoYXQgbG9va2luZyB1cCBhc3RyYWwgaWRlbnRpZmllciBjaGFyYWN0ZXJzIGlzXG4vLyByYXJlLlxuZnVuY3Rpb24gaXNJbkFzdHJhbFNldChjb2RlLCBzZXQpIHtcbiAgdmFyIHBvcyA9IDB4MTAwMDA7XG4gIGZvciAodmFyIGkgPSAwOyBpIDwgc2V0Lmxlbmd0aDsgaSArPSAyKSB7XG4gICAgcG9zICs9IHNldFtpXTtcbiAgICBpZiAocG9zID4gY29kZSkgcmV0dXJuIGZhbHNlO1xuICAgIHBvcyArPSBzZXRbaSArIDFdO1xuICAgIGlmIChwb3MgPj0gY29kZSkgcmV0dXJuIHRydWU7XG4gIH1cbn1cblxuLy8gVGVzdCB3aGV0aGVyIGEgZ2l2ZW4gY2hhcmFjdGVyIGNvZGUgc3RhcnRzIGFuIGlkZW50aWZpZXIuXG5cbmZ1bmN0aW9uIGlzSWRlbnRpZmllclN0YXJ0KGNvZGUsIGFzdHJhbCkge1xuICBpZiAoY29kZSA8IDY1KSByZXR1cm4gY29kZSA9PT0gMzY7XG4gIGlmIChjb2RlIDwgOTEpIHJldHVybiB0cnVlO1xuICBpZiAoY29kZSA8IDk3KSByZXR1cm4gY29kZSA9PT0gOTU7XG4gIGlmIChjb2RlIDwgMTIzKSByZXR1cm4gdHJ1ZTtcbiAgaWYgKGNvZGUgPD0gMHhmZmZmKSByZXR1cm4gY29kZSA+PSAweGFhICYmIG5vbkFTQ0lJaWRlbnRpZmllclN0YXJ0LnRlc3QoU3RyaW5nLmZyb21DaGFyQ29kZShjb2RlKSk7XG4gIGlmIChhc3RyYWwgPT09IGZhbHNlKSByZXR1cm4gZmFsc2U7XG4gIHJldHVybiBpc0luQXN0cmFsU2V0KGNvZGUsIGFzdHJhbElkZW50aWZpZXJTdGFydENvZGVzKTtcbn1cblxuLy8gVGVzdCB3aGV0aGVyIGEgZ2l2ZW4gY2hhcmFjdGVyIGlzIHBhcnQgb2YgYW4gaWRlbnRpZmllci5cblxuZnVuY3Rpb24gaXNJZGVudGlmaWVyQ2hhcihjb2RlLCBhc3RyYWwpIHtcbiAgaWYgKGNvZGUgPCA0OCkgcmV0dXJuIGNvZGUgPT09IDM2O1xuICBpZiAoY29kZSA8IDU4KSByZXR1cm4gdHJ1ZTtcbiAgaWYgKGNvZGUgPCA2NSkgcmV0dXJuIGZhbHNlO1xuICBpZiAoY29kZSA8IDkxKSByZXR1cm4gdHJ1ZTtcbiAgaWYgKGNvZGUgPCA5NykgcmV0dXJuIGNvZGUgPT09IDk1O1xuICBpZiAoY29kZSA8IDEyMykgcmV0dXJuIHRydWU7XG4gIGlmIChjb2RlIDw9IDB4ZmZmZikgcmV0dXJuIGNvZGUgPj0gMHhhYSAmJiBub25BU0NJSWlkZW50aWZpZXIudGVzdChTdHJpbmcuZnJvbUNoYXJDb2RlKGNvZGUpKTtcbiAgaWYgKGFzdHJhbCA9PT0gZmFsc2UpIHJldHVybiBmYWxzZTtcbiAgcmV0dXJuIGlzSW5Bc3RyYWxTZXQoY29kZSwgYXN0cmFsSWRlbnRpZmllclN0YXJ0Q29kZXMpIHx8IGlzSW5Bc3RyYWxTZXQoY29kZSwgYXN0cmFsSWRlbnRpZmllckNvZGVzKTtcbn1cblxufSx7fV0sMzpbZnVuY3Rpb24oX2RlcmVxXyxtb2R1bGUsZXhwb3J0cyl7XG4vLyBBY29ybiBpcyBhIHRpbnksIGZhc3QgSmF2YVNjcmlwdCBwYXJzZXIgd3JpdHRlbiBpbiBKYXZhU2NyaXB0LlxuLy9cbi8vIEFjb3JuIHdhcyB3cml0dGVuIGJ5IE1hcmlqbiBIYXZlcmJla2UsIEluZ3ZhciBTdGVwYW55YW4sIGFuZFxuLy8gdmFyaW91cyBjb250cmlidXRvcnMgYW5kIHJlbGVhc2VkIHVuZGVyIGFuIE1JVCBsaWNlbnNlLlxuLy9cbi8vIEdpdCByZXBvc2l0b3JpZXMgZm9yIEFjb3JuIGFyZSBhdmFpbGFibGUgYXRcbi8vXG4vLyAgICAgaHR0cDovL21hcmlqbmhhdmVyYmVrZS5ubC9naXQvYWNvcm5cbi8vICAgICBodHRwczovL2dpdGh1Yi5jb20vbWFyaWpuaC9hY29ybi5naXRcbi8vXG4vLyBQbGVhc2UgdXNlIHRoZSBbZ2l0aHViIGJ1ZyB0cmFja2VyXVtnaGJ0XSB0byByZXBvcnQgaXNzdWVzLlxuLy9cbi8vIFtnaGJ0XTogaHR0cHM6Ly9naXRodWIuY29tL21hcmlqbmgvYWNvcm4vaXNzdWVzXG4vL1xuLy8gVGhpcyBmaWxlIGRlZmluZXMgdGhlIG1haW4gcGFyc2VyIGludGVyZmFjZS4gVGhlIGxpYnJhcnkgYWxzbyBjb21lc1xuLy8gd2l0aCBhIFtlcnJvci10b2xlcmFudCBwYXJzZXJdW2RhbW1pdF0gYW5kIGFuXG4vLyBbYWJzdHJhY3Qgc3ludGF4IHRyZWUgd2Fsa2VyXVt3YWxrXSwgZGVmaW5lZCBpbiBvdGhlciBmaWxlcy5cbi8vXG4vLyBbZGFtbWl0XTogYWNvcm5fbG9vc2UuanNcbi8vIFt3YWxrXTogdXRpbC93YWxrLmpzXG5cblwidXNlIHN0cmljdFwiO1xuXG5leHBvcnRzLl9fZXNNb2R1bGUgPSB0cnVlO1xuZXhwb3J0cy5wYXJzZSA9IHBhcnNlO1xuZXhwb3J0cy5wYXJzZUV4cHJlc3Npb25BdCA9IHBhcnNlRXhwcmVzc2lvbkF0O1xuZXhwb3J0cy50b2tlbml6ZXIgPSB0b2tlbml6ZXI7XG5cbnZhciBfc3RhdGUgPSBfZGVyZXFfKFwiLi9zdGF0ZVwiKTtcblxudmFyIF9vcHRpb25zID0gX2RlcmVxXyhcIi4vb3B0aW9uc1wiKTtcblxuX2RlcmVxXyhcIi4vcGFyc2V1dGlsXCIpO1xuXG5fZGVyZXFfKFwiLi9zdGF0ZW1lbnRcIik7XG5cbl9kZXJlcV8oXCIuL2x2YWxcIik7XG5cbl9kZXJlcV8oXCIuL2V4cHJlc3Npb25cIik7XG5cbl9kZXJlcV8oXCIuL2xvY2F0aW9uXCIpO1xuXG5leHBvcnRzLlBhcnNlciA9IF9zdGF0ZS5QYXJzZXI7XG5leHBvcnRzLnBsdWdpbnMgPSBfc3RhdGUucGx1Z2lucztcbmV4cG9ydHMuZGVmYXVsdE9wdGlvbnMgPSBfb3B0aW9ucy5kZWZhdWx0T3B0aW9ucztcblxudmFyIF9sb2N1dGlsID0gX2RlcmVxXyhcIi4vbG9jdXRpbFwiKTtcblxuZXhwb3J0cy5Qb3NpdGlvbiA9IF9sb2N1dGlsLlBvc2l0aW9uO1xuZXhwb3J0cy5Tb3VyY2VMb2NhdGlvbiA9IF9sb2N1dGlsLlNvdXJjZUxvY2F0aW9uO1xuZXhwb3J0cy5nZXRMaW5lSW5mbyA9IF9sb2N1dGlsLmdldExpbmVJbmZvO1xuXG52YXIgX25vZGUgPSBfZGVyZXFfKFwiLi9ub2RlXCIpO1xuXG5leHBvcnRzLk5vZGUgPSBfbm9kZS5Ob2RlO1xuXG52YXIgX3Rva2VudHlwZSA9IF9kZXJlcV8oXCIuL3Rva2VudHlwZVwiKTtcblxuZXhwb3J0cy5Ub2tlblR5cGUgPSBfdG9rZW50eXBlLlRva2VuVHlwZTtcbmV4cG9ydHMudG9rVHlwZXMgPSBfdG9rZW50eXBlLnR5cGVzO1xuXG52YXIgX3Rva2VuY29udGV4dCA9IF9kZXJlcV8oXCIuL3Rva2VuY29udGV4dFwiKTtcblxuZXhwb3J0cy5Ub2tDb250ZXh0ID0gX3Rva2VuY29udGV4dC5Ub2tDb250ZXh0O1xuZXhwb3J0cy50b2tDb250ZXh0cyA9IF90b2tlbmNvbnRleHQudHlwZXM7XG5cbnZhciBfaWRlbnRpZmllciA9IF9kZXJlcV8oXCIuL2lkZW50aWZpZXJcIik7XG5cbmV4cG9ydHMuaXNJZGVudGlmaWVyQ2hhciA9IF9pZGVudGlmaWVyLmlzSWRlbnRpZmllckNoYXI7XG5leHBvcnRzLmlzSWRlbnRpZmllclN0YXJ0ID0gX2lkZW50aWZpZXIuaXNJZGVudGlmaWVyU3RhcnQ7XG5cbnZhciBfdG9rZW5pemUgPSBfZGVyZXFfKFwiLi90b2tlbml6ZVwiKTtcblxuZXhwb3J0cy5Ub2tlbiA9IF90b2tlbml6ZS5Ub2tlbjtcblxudmFyIF93aGl0ZXNwYWNlID0gX2RlcmVxXyhcIi4vd2hpdGVzcGFjZVwiKTtcblxuZXhwb3J0cy5pc05ld0xpbmUgPSBfd2hpdGVzcGFjZS5pc05ld0xpbmU7XG5leHBvcnRzLmxpbmVCcmVhayA9IF93aGl0ZXNwYWNlLmxpbmVCcmVhaztcbmV4cG9ydHMubGluZUJyZWFrRyA9IF93aGl0ZXNwYWNlLmxpbmVCcmVha0c7XG52YXIgdmVyc2lvbiA9IFwiMi40LjBcIjtcblxuZXhwb3J0cy52ZXJzaW9uID0gdmVyc2lvbjtcbi8vIFRoZSBtYWluIGV4cG9ydGVkIGludGVyZmFjZSAodW5kZXIgYHNlbGYuYWNvcm5gIHdoZW4gaW4gdGhlXG4vLyBicm93c2VyKSBpcyBhIGBwYXJzZWAgZnVuY3Rpb24gdGhhdCB0YWtlcyBhIGNvZGUgc3RyaW5nIGFuZFxuLy8gcmV0dXJucyBhbiBhYnN0cmFjdCBzeW50YXggdHJlZSBhcyBzcGVjaWZpZWQgYnkgW01vemlsbGEgcGFyc2VyXG4vLyBBUEldW2FwaV0uXG4vL1xuLy8gW2FwaV06IGh0dHBzOi8vZGV2ZWxvcGVyLm1vemlsbGEub3JnL2VuLVVTL2RvY3MvU3BpZGVyTW9ua2V5L1BhcnNlcl9BUElcblxuZnVuY3Rpb24gcGFyc2UoaW5wdXQsIG9wdGlvbnMpIHtcbiAgcmV0dXJuIG5ldyBfc3RhdGUuUGFyc2VyKG9wdGlvbnMsIGlucHV0KS5wYXJzZSgpO1xufVxuXG4vLyBUaGlzIGZ1bmN0aW9uIHRyaWVzIHRvIHBhcnNlIGEgc2luZ2xlIGV4cHJlc3Npb24gYXQgYSBnaXZlblxuLy8gb2Zmc2V0IGluIGEgc3RyaW5nLiBVc2VmdWwgZm9yIHBhcnNpbmcgbWl4ZWQtbGFuZ3VhZ2UgZm9ybWF0c1xuLy8gdGhhdCBlbWJlZCBKYXZhU2NyaXB0IGV4cHJlc3Npb25zLlxuXG5mdW5jdGlvbiBwYXJzZUV4cHJlc3Npb25BdChpbnB1dCwgcG9zLCBvcHRpb25zKSB7XG4gIHZhciBwID0gbmV3IF9zdGF0ZS5QYXJzZXIob3B0aW9ucywgaW5wdXQsIHBvcyk7XG4gIHAubmV4dFRva2VuKCk7XG4gIHJldHVybiBwLnBhcnNlRXhwcmVzc2lvbigpO1xufVxuXG4vLyBBY29ybiBpcyBvcmdhbml6ZWQgYXMgYSB0b2tlbml6ZXIgYW5kIGEgcmVjdXJzaXZlLWRlc2NlbnQgcGFyc2VyLlxuLy8gVGhlIGB0b2tlbml6ZWAgZXhwb3J0IHByb3ZpZGVzIGFuIGludGVyZmFjZSB0byB0aGUgdG9rZW5pemVyLlxuXG5mdW5jdGlvbiB0b2tlbml6ZXIoaW5wdXQsIG9wdGlvbnMpIHtcbiAgcmV0dXJuIG5ldyBfc3RhdGUuUGFyc2VyKG9wdGlvbnMsIGlucHV0KTtcbn1cblxufSx7XCIuL2V4cHJlc3Npb25cIjoxLFwiLi9pZGVudGlmaWVyXCI6MixcIi4vbG9jYXRpb25cIjo0LFwiLi9sb2N1dGlsXCI6NSxcIi4vbHZhbFwiOjYsXCIuL25vZGVcIjo3LFwiLi9vcHRpb25zXCI6OCxcIi4vcGFyc2V1dGlsXCI6OSxcIi4vc3RhdGVcIjoxMCxcIi4vc3RhdGVtZW50XCI6MTEsXCIuL3Rva2VuY29udGV4dFwiOjEyLFwiLi90b2tlbml6ZVwiOjEzLFwiLi90b2tlbnR5cGVcIjoxNCxcIi4vd2hpdGVzcGFjZVwiOjE2fV0sNDpbZnVuY3Rpb24oX2RlcmVxXyxtb2R1bGUsZXhwb3J0cyl7XG5cInVzZSBzdHJpY3RcIjtcblxudmFyIF9zdGF0ZSA9IF9kZXJlcV8oXCIuL3N0YXRlXCIpO1xuXG52YXIgX2xvY3V0aWwgPSBfZGVyZXFfKFwiLi9sb2N1dGlsXCIpO1xuXG52YXIgcHAgPSBfc3RhdGUuUGFyc2VyLnByb3RvdHlwZTtcblxuLy8gVGhpcyBmdW5jdGlvbiBpcyB1c2VkIHRvIHJhaXNlIGV4Y2VwdGlvbnMgb24gcGFyc2UgZXJyb3JzLiBJdFxuLy8gdGFrZXMgYW4gb2Zmc2V0IGludGVnZXIgKGludG8gdGhlIGN1cnJlbnQgYGlucHV0YCkgdG8gaW5kaWNhdGVcbi8vIHRoZSBsb2NhdGlvbiBvZiB0aGUgZXJyb3IsIGF0dGFjaGVzIHRoZSBwb3NpdGlvbiB0byB0aGUgZW5kXG4vLyBvZiB0aGUgZXJyb3IgbWVzc2FnZSwgYW5kIHRoZW4gcmFpc2VzIGEgYFN5bnRheEVycm9yYCB3aXRoIHRoYXRcbi8vIG1lc3NhZ2UuXG5cbnBwLnJhaXNlID0gZnVuY3Rpb24gKHBvcywgbWVzc2FnZSkge1xuICB2YXIgbG9jID0gX2xvY3V0aWwuZ2V0TGluZUluZm8odGhpcy5pbnB1dCwgcG9zKTtcbiAgbWVzc2FnZSArPSBcIiAoXCIgKyBsb2MubGluZSArIFwiOlwiICsgbG9jLmNvbHVtbiArIFwiKVwiO1xuICB2YXIgZXJyID0gbmV3IFN5bnRheEVycm9yKG1lc3NhZ2UpO1xuICBlcnIucG9zID0gcG9zO2Vyci5sb2MgPSBsb2M7ZXJyLnJhaXNlZEF0ID0gdGhpcy5wb3M7XG4gIHRocm93IGVycjtcbn07XG5cbnBwLmN1clBvc2l0aW9uID0gZnVuY3Rpb24gKCkge1xuICBpZiAodGhpcy5vcHRpb25zLmxvY2F0aW9ucykge1xuICAgIHJldHVybiBuZXcgX2xvY3V0aWwuUG9zaXRpb24odGhpcy5jdXJMaW5lLCB0aGlzLnBvcyAtIHRoaXMubGluZVN0YXJ0KTtcbiAgfVxufTtcblxufSx7XCIuL2xvY3V0aWxcIjo1LFwiLi9zdGF0ZVwiOjEwfV0sNTpbZnVuY3Rpb24oX2RlcmVxXyxtb2R1bGUsZXhwb3J0cyl7XG5cInVzZSBzdHJpY3RcIjtcblxuZXhwb3J0cy5fX2VzTW9kdWxlID0gdHJ1ZTtcbmV4cG9ydHMuZ2V0TGluZUluZm8gPSBnZXRMaW5lSW5mbztcblxuZnVuY3Rpb24gX2NsYXNzQ2FsbENoZWNrKGluc3RhbmNlLCBDb25zdHJ1Y3RvcikgeyBpZiAoIShpbnN0YW5jZSBpbnN0YW5jZW9mIENvbnN0cnVjdG9yKSkgeyB0aHJvdyBuZXcgVHlwZUVycm9yKFwiQ2Fubm90IGNhbGwgYSBjbGFzcyBhcyBhIGZ1bmN0aW9uXCIpOyB9IH1cblxudmFyIF93aGl0ZXNwYWNlID0gX2RlcmVxXyhcIi4vd2hpdGVzcGFjZVwiKTtcblxuLy8gVGhlc2UgYXJlIHVzZWQgd2hlbiBgb3B0aW9ucy5sb2NhdGlvbnNgIGlzIG9uLCBmb3IgdGhlXG4vLyBgc3RhcnRMb2NgIGFuZCBgZW5kTG9jYCBwcm9wZXJ0aWVzLlxuXG52YXIgUG9zaXRpb24gPSAoZnVuY3Rpb24gKCkge1xuICBmdW5jdGlvbiBQb3NpdGlvbihsaW5lLCBjb2wpIHtcbiAgICBfY2xhc3NDYWxsQ2hlY2sodGhpcywgUG9zaXRpb24pO1xuXG4gICAgdGhpcy5saW5lID0gbGluZTtcbiAgICB0aGlzLmNvbHVtbiA9IGNvbDtcbiAgfVxuXG4gIFBvc2l0aW9uLnByb3RvdHlwZS5vZmZzZXQgPSBmdW5jdGlvbiBvZmZzZXQobikge1xuICAgIHJldHVybiBuZXcgUG9zaXRpb24odGhpcy5saW5lLCB0aGlzLmNvbHVtbiArIG4pO1xuICB9O1xuXG4gIHJldHVybiBQb3NpdGlvbjtcbn0pKCk7XG5cbmV4cG9ydHMuUG9zaXRpb24gPSBQb3NpdGlvbjtcblxudmFyIFNvdXJjZUxvY2F0aW9uID0gZnVuY3Rpb24gU291cmNlTG9jYXRpb24ocCwgc3RhcnQsIGVuZCkge1xuICBfY2xhc3NDYWxsQ2hlY2sodGhpcywgU291cmNlTG9jYXRpb24pO1xuXG4gIHRoaXMuc3RhcnQgPSBzdGFydDtcbiAgdGhpcy5lbmQgPSBlbmQ7XG4gIGlmIChwLnNvdXJjZUZpbGUgIT09IG51bGwpIHRoaXMuc291cmNlID0gcC5zb3VyY2VGaWxlO1xufTtcblxuZXhwb3J0cy5Tb3VyY2VMb2NhdGlvbiA9IFNvdXJjZUxvY2F0aW9uO1xuXG4vLyBUaGUgYGdldExpbmVJbmZvYCBmdW5jdGlvbiBpcyBtb3N0bHkgdXNlZnVsIHdoZW4gdGhlXG4vLyBgbG9jYXRpb25zYCBvcHRpb24gaXMgb2ZmIChmb3IgcGVyZm9ybWFuY2UgcmVhc29ucykgYW5kIHlvdVxuLy8gd2FudCB0byBmaW5kIHRoZSBsaW5lL2NvbHVtbiBwb3NpdGlvbiBmb3IgYSBnaXZlbiBjaGFyYWN0ZXJcbi8vIG9mZnNldC4gYGlucHV0YCBzaG91bGQgYmUgdGhlIGNvZGUgc3RyaW5nIHRoYXQgdGhlIG9mZnNldCByZWZlcnNcbi8vIGludG8uXG5cbmZ1bmN0aW9uIGdldExpbmVJbmZvKGlucHV0LCBvZmZzZXQpIHtcbiAgZm9yICh2YXIgbGluZSA9IDEsIGN1ciA9IDA7Oykge1xuICAgIF93aGl0ZXNwYWNlLmxpbmVCcmVha0cubGFzdEluZGV4ID0gY3VyO1xuICAgIHZhciBtYXRjaCA9IF93aGl0ZXNwYWNlLmxpbmVCcmVha0cuZXhlYyhpbnB1dCk7XG4gICAgaWYgKG1hdGNoICYmIG1hdGNoLmluZGV4IDwgb2Zmc2V0KSB7XG4gICAgICArK2xpbmU7XG4gICAgICBjdXIgPSBtYXRjaC5pbmRleCArIG1hdGNoWzBdLmxlbmd0aDtcbiAgICB9IGVsc2Uge1xuICAgICAgcmV0dXJuIG5ldyBQb3NpdGlvbihsaW5lLCBvZmZzZXQgLSBjdXIpO1xuICAgIH1cbiAgfVxufVxuXG59LHtcIi4vd2hpdGVzcGFjZVwiOjE2fV0sNjpbZnVuY3Rpb24oX2RlcmVxXyxtb2R1bGUsZXhwb3J0cyl7XG5cInVzZSBzdHJpY3RcIjtcblxudmFyIF90b2tlbnR5cGUgPSBfZGVyZXFfKFwiLi90b2tlbnR5cGVcIik7XG5cbnZhciBfc3RhdGUgPSBfZGVyZXFfKFwiLi9zdGF0ZVwiKTtcblxudmFyIF9pZGVudGlmaWVyID0gX2RlcmVxXyhcIi4vaWRlbnRpZmllclwiKTtcblxudmFyIF91dGlsID0gX2RlcmVxXyhcIi4vdXRpbFwiKTtcblxudmFyIHBwID0gX3N0YXRlLlBhcnNlci5wcm90b3R5cGU7XG5cbi8vIENvbnZlcnQgZXhpc3RpbmcgZXhwcmVzc2lvbiBhdG9tIHRvIGFzc2lnbmFibGUgcGF0dGVyblxuLy8gaWYgcG9zc2libGUuXG5cbnBwLnRvQXNzaWduYWJsZSA9IGZ1bmN0aW9uIChub2RlLCBpc0JpbmRpbmcpIHtcbiAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2ICYmIG5vZGUpIHtcbiAgICBzd2l0Y2ggKG5vZGUudHlwZSkge1xuICAgICAgY2FzZSBcIklkZW50aWZpZXJcIjpcbiAgICAgIGNhc2UgXCJPYmplY3RQYXR0ZXJuXCI6XG4gICAgICBjYXNlIFwiQXJyYXlQYXR0ZXJuXCI6XG4gICAgICBjYXNlIFwiQXNzaWdubWVudFBhdHRlcm5cIjpcbiAgICAgICAgYnJlYWs7XG5cbiAgICAgIGNhc2UgXCJPYmplY3RFeHByZXNzaW9uXCI6XG4gICAgICAgIG5vZGUudHlwZSA9IFwiT2JqZWN0UGF0dGVyblwiO1xuICAgICAgICBmb3IgKHZhciBpID0gMDsgaSA8IG5vZGUucHJvcGVydGllcy5sZW5ndGg7IGkrKykge1xuICAgICAgICAgIHZhciBwcm9wID0gbm9kZS5wcm9wZXJ0aWVzW2ldO1xuICAgICAgICAgIGlmIChwcm9wLmtpbmQgIT09IFwiaW5pdFwiKSB0aGlzLnJhaXNlKHByb3Aua2V5LnN0YXJ0LCBcIk9iamVjdCBwYXR0ZXJuIGNhbid0IGNvbnRhaW4gZ2V0dGVyIG9yIHNldHRlclwiKTtcbiAgICAgICAgICB0aGlzLnRvQXNzaWduYWJsZShwcm9wLnZhbHVlLCBpc0JpbmRpbmcpO1xuICAgICAgICB9XG4gICAgICAgIGJyZWFrO1xuXG4gICAgICBjYXNlIFwiQXJyYXlFeHByZXNzaW9uXCI6XG4gICAgICAgIG5vZGUudHlwZSA9IFwiQXJyYXlQYXR0ZXJuXCI7XG4gICAgICAgIHRoaXMudG9Bc3NpZ25hYmxlTGlzdChub2RlLmVsZW1lbnRzLCBpc0JpbmRpbmcpO1xuICAgICAgICBicmVhaztcblxuICAgICAgY2FzZSBcIkFzc2lnbm1lbnRFeHByZXNzaW9uXCI6XG4gICAgICAgIGlmIChub2RlLm9wZXJhdG9yID09PSBcIj1cIikge1xuICAgICAgICAgIG5vZGUudHlwZSA9IFwiQXNzaWdubWVudFBhdHRlcm5cIjtcbiAgICAgICAgICBkZWxldGUgbm9kZS5vcGVyYXRvcjtcbiAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICB0aGlzLnJhaXNlKG5vZGUubGVmdC5lbmQsIFwiT25seSAnPScgb3BlcmF0b3IgY2FuIGJlIHVzZWQgZm9yIHNwZWNpZnlpbmcgZGVmYXVsdCB2YWx1ZS5cIik7XG4gICAgICAgIH1cbiAgICAgICAgYnJlYWs7XG5cbiAgICAgIGNhc2UgXCJQYXJlbnRoZXNpemVkRXhwcmVzc2lvblwiOlxuICAgICAgICBub2RlLmV4cHJlc3Npb24gPSB0aGlzLnRvQXNzaWduYWJsZShub2RlLmV4cHJlc3Npb24sIGlzQmluZGluZyk7XG4gICAgICAgIGJyZWFrO1xuXG4gICAgICBjYXNlIFwiTWVtYmVyRXhwcmVzc2lvblwiOlxuICAgICAgICBpZiAoIWlzQmluZGluZykgYnJlYWs7XG5cbiAgICAgIGRlZmF1bHQ6XG4gICAgICAgIHRoaXMucmFpc2Uobm9kZS5zdGFydCwgXCJBc3NpZ25pbmcgdG8gcnZhbHVlXCIpO1xuICAgIH1cbiAgfVxuICByZXR1cm4gbm9kZTtcbn07XG5cbi8vIENvbnZlcnQgbGlzdCBvZiBleHByZXNzaW9uIGF0b21zIHRvIGJpbmRpbmcgbGlzdC5cblxucHAudG9Bc3NpZ25hYmxlTGlzdCA9IGZ1bmN0aW9uIChleHByTGlzdCwgaXNCaW5kaW5nKSB7XG4gIHZhciBlbmQgPSBleHByTGlzdC5sZW5ndGg7XG4gIGlmIChlbmQpIHtcbiAgICB2YXIgbGFzdCA9IGV4cHJMaXN0W2VuZCAtIDFdO1xuICAgIGlmIChsYXN0ICYmIGxhc3QudHlwZSA9PSBcIlJlc3RFbGVtZW50XCIpIHtcbiAgICAgIC0tZW5kO1xuICAgIH0gZWxzZSBpZiAobGFzdCAmJiBsYXN0LnR5cGUgPT0gXCJTcHJlYWRFbGVtZW50XCIpIHtcbiAgICAgIGxhc3QudHlwZSA9IFwiUmVzdEVsZW1lbnRcIjtcbiAgICAgIHZhciBhcmcgPSBsYXN0LmFyZ3VtZW50O1xuICAgICAgdGhpcy50b0Fzc2lnbmFibGUoYXJnLCBpc0JpbmRpbmcpO1xuICAgICAgaWYgKGFyZy50eXBlICE9PSBcIklkZW50aWZpZXJcIiAmJiBhcmcudHlwZSAhPT0gXCJNZW1iZXJFeHByZXNzaW9uXCIgJiYgYXJnLnR5cGUgIT09IFwiQXJyYXlQYXR0ZXJuXCIpIHRoaXMudW5leHBlY3RlZChhcmcuc3RhcnQpO1xuICAgICAgLS1lbmQ7XG4gICAgfVxuICB9XG4gIGZvciAodmFyIGkgPSAwOyBpIDwgZW5kOyBpKyspIHtcbiAgICB2YXIgZWx0ID0gZXhwckxpc3RbaV07XG4gICAgaWYgKGVsdCkgdGhpcy50b0Fzc2lnbmFibGUoZWx0LCBpc0JpbmRpbmcpO1xuICB9XG4gIHJldHVybiBleHByTGlzdDtcbn07XG5cbi8vIFBhcnNlcyBzcHJlYWQgZWxlbWVudC5cblxucHAucGFyc2VTcHJlYWQgPSBmdW5jdGlvbiAocmVmU2hvcnRoYW5kRGVmYXVsdFBvcykge1xuICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gIHRoaXMubmV4dCgpO1xuICBub2RlLmFyZ3VtZW50ID0gdGhpcy5wYXJzZU1heWJlQXNzaWduKHJlZlNob3J0aGFuZERlZmF1bHRQb3MpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiU3ByZWFkRWxlbWVudFwiKTtcbn07XG5cbnBwLnBhcnNlUmVzdCA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICB0aGlzLm5leHQoKTtcbiAgbm9kZS5hcmd1bWVudCA9IHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5uYW1lIHx8IHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5icmFja2V0TCA/IHRoaXMucGFyc2VCaW5kaW5nQXRvbSgpIDogdGhpcy51bmV4cGVjdGVkKCk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJSZXN0RWxlbWVudFwiKTtcbn07XG5cbi8vIFBhcnNlcyBsdmFsdWUgKGFzc2lnbmFibGUpIGF0b20uXG5cbnBwLnBhcnNlQmluZGluZ0F0b20gPSBmdW5jdGlvbiAoKSB7XG4gIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPCA2KSByZXR1cm4gdGhpcy5wYXJzZUlkZW50KCk7XG4gIHN3aXRjaCAodGhpcy50eXBlKSB7XG4gICAgY2FzZSBfdG9rZW50eXBlLnR5cGVzLm5hbWU6XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZUlkZW50KCk7XG5cbiAgICBjYXNlIF90b2tlbnR5cGUudHlwZXMuYnJhY2tldEw6XG4gICAgICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gICAgICB0aGlzLm5leHQoKTtcbiAgICAgIG5vZGUuZWxlbWVudHMgPSB0aGlzLnBhcnNlQmluZGluZ0xpc3QoX3Rva2VudHlwZS50eXBlcy5icmFja2V0UiwgdHJ1ZSwgdHJ1ZSk7XG4gICAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiQXJyYXlQYXR0ZXJuXCIpO1xuXG4gICAgY2FzZSBfdG9rZW50eXBlLnR5cGVzLmJyYWNlTDpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlT2JqKHRydWUpO1xuXG4gICAgZGVmYXVsdDpcbiAgICAgIHRoaXMudW5leHBlY3RlZCgpO1xuICB9XG59O1xuXG5wcC5wYXJzZUJpbmRpbmdMaXN0ID0gZnVuY3Rpb24gKGNsb3NlLCBhbGxvd0VtcHR5LCBhbGxvd1RyYWlsaW5nQ29tbWEpIHtcbiAgdmFyIGVsdHMgPSBbXSxcbiAgICAgIGZpcnN0ID0gdHJ1ZTtcbiAgd2hpbGUgKCF0aGlzLmVhdChjbG9zZSkpIHtcbiAgICBpZiAoZmlyc3QpIGZpcnN0ID0gZmFsc2U7ZWxzZSB0aGlzLmV4cGVjdChfdG9rZW50eXBlLnR5cGVzLmNvbW1hKTtcbiAgICBpZiAoYWxsb3dFbXB0eSAmJiB0aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuY29tbWEpIHtcbiAgICAgIGVsdHMucHVzaChudWxsKTtcbiAgICB9IGVsc2UgaWYgKGFsbG93VHJhaWxpbmdDb21tYSAmJiB0aGlzLmFmdGVyVHJhaWxpbmdDb21tYShjbG9zZSkpIHtcbiAgICAgIGJyZWFrO1xuICAgIH0gZWxzZSBpZiAodGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLmVsbGlwc2lzKSB7XG4gICAgICB2YXIgcmVzdCA9IHRoaXMucGFyc2VSZXN0KCk7XG4gICAgICB0aGlzLnBhcnNlQmluZGluZ0xpc3RJdGVtKHJlc3QpO1xuICAgICAgZWx0cy5wdXNoKHJlc3QpO1xuICAgICAgdGhpcy5leHBlY3QoY2xvc2UpO1xuICAgICAgYnJlYWs7XG4gICAgfSBlbHNlIHtcbiAgICAgIHZhciBlbGVtID0gdGhpcy5wYXJzZU1heWJlRGVmYXVsdCh0aGlzLnN0YXJ0LCB0aGlzLnN0YXJ0TG9jKTtcbiAgICAgIHRoaXMucGFyc2VCaW5kaW5nTGlzdEl0ZW0oZWxlbSk7XG4gICAgICBlbHRzLnB1c2goZWxlbSk7XG4gICAgfVxuICB9XG4gIHJldHVybiBlbHRzO1xufTtcblxucHAucGFyc2VCaW5kaW5nTGlzdEl0ZW0gPSBmdW5jdGlvbiAocGFyYW0pIHtcbiAgcmV0dXJuIHBhcmFtO1xufTtcblxuLy8gUGFyc2VzIGFzc2lnbm1lbnQgcGF0dGVybiBhcm91bmQgZ2l2ZW4gYXRvbSBpZiBwb3NzaWJsZS5cblxucHAucGFyc2VNYXliZURlZmF1bHQgPSBmdW5jdGlvbiAoc3RhcnRQb3MsIHN0YXJ0TG9jLCBsZWZ0KSB7XG4gIGxlZnQgPSBsZWZ0IHx8IHRoaXMucGFyc2VCaW5kaW5nQXRvbSgpO1xuICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uIDwgNiB8fCAhdGhpcy5lYXQoX3Rva2VudHlwZS50eXBlcy5lcSkpIHJldHVybiBsZWZ0O1xuICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlQXQoc3RhcnRQb3MsIHN0YXJ0TG9jKTtcbiAgbm9kZS5sZWZ0ID0gbGVmdDtcbiAgbm9kZS5yaWdodCA9IHRoaXMucGFyc2VNYXliZUFzc2lnbigpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiQXNzaWdubWVudFBhdHRlcm5cIik7XG59O1xuXG4vLyBWZXJpZnkgdGhhdCBhIG5vZGUgaXMgYW4gbHZhbCDigJQgc29tZXRoaW5nIHRoYXQgY2FuIGJlIGFzc2lnbmVkXG4vLyB0by5cblxucHAuY2hlY2tMVmFsID0gZnVuY3Rpb24gKGV4cHIsIGlzQmluZGluZywgY2hlY2tDbGFzaGVzKSB7XG4gIHN3aXRjaCAoZXhwci50eXBlKSB7XG4gICAgY2FzZSBcIklkZW50aWZpZXJcIjpcbiAgICAgIGlmICh0aGlzLnN0cmljdCAmJiAoX2lkZW50aWZpZXIucmVzZXJ2ZWRXb3Jkcy5zdHJpY3RCaW5kKGV4cHIubmFtZSkgfHwgX2lkZW50aWZpZXIucmVzZXJ2ZWRXb3Jkcy5zdHJpY3QoZXhwci5uYW1lKSkpIHRoaXMucmFpc2UoZXhwci5zdGFydCwgKGlzQmluZGluZyA/IFwiQmluZGluZyBcIiA6IFwiQXNzaWduaW5nIHRvIFwiKSArIGV4cHIubmFtZSArIFwiIGluIHN0cmljdCBtb2RlXCIpO1xuICAgICAgaWYgKGNoZWNrQ2xhc2hlcykge1xuICAgICAgICBpZiAoX3V0aWwuaGFzKGNoZWNrQ2xhc2hlcywgZXhwci5uYW1lKSkgdGhpcy5yYWlzZShleHByLnN0YXJ0LCBcIkFyZ3VtZW50IG5hbWUgY2xhc2ggaW4gc3RyaWN0IG1vZGVcIik7XG4gICAgICAgIGNoZWNrQ2xhc2hlc1tleHByLm5hbWVdID0gdHJ1ZTtcbiAgICAgIH1cbiAgICAgIGJyZWFrO1xuXG4gICAgY2FzZSBcIk1lbWJlckV4cHJlc3Npb25cIjpcbiAgICAgIGlmIChpc0JpbmRpbmcpIHRoaXMucmFpc2UoZXhwci5zdGFydCwgKGlzQmluZGluZyA/IFwiQmluZGluZ1wiIDogXCJBc3NpZ25pbmcgdG9cIikgKyBcIiBtZW1iZXIgZXhwcmVzc2lvblwiKTtcbiAgICAgIGJyZWFrO1xuXG4gICAgY2FzZSBcIk9iamVjdFBhdHRlcm5cIjpcbiAgICAgIGZvciAodmFyIGkgPSAwOyBpIDwgZXhwci5wcm9wZXJ0aWVzLmxlbmd0aDsgaSsrKSB7XG4gICAgICAgIHRoaXMuY2hlY2tMVmFsKGV4cHIucHJvcGVydGllc1tpXS52YWx1ZSwgaXNCaW5kaW5nLCBjaGVja0NsYXNoZXMpO1xuICAgICAgfWJyZWFrO1xuXG4gICAgY2FzZSBcIkFycmF5UGF0dGVyblwiOlxuICAgICAgZm9yICh2YXIgaSA9IDA7IGkgPCBleHByLmVsZW1lbnRzLmxlbmd0aDsgaSsrKSB7XG4gICAgICAgIHZhciBlbGVtID0gZXhwci5lbGVtZW50c1tpXTtcbiAgICAgICAgaWYgKGVsZW0pIHRoaXMuY2hlY2tMVmFsKGVsZW0sIGlzQmluZGluZywgY2hlY2tDbGFzaGVzKTtcbiAgICAgIH1cbiAgICAgIGJyZWFrO1xuXG4gICAgY2FzZSBcIkFzc2lnbm1lbnRQYXR0ZXJuXCI6XG4gICAgICB0aGlzLmNoZWNrTFZhbChleHByLmxlZnQsIGlzQmluZGluZywgY2hlY2tDbGFzaGVzKTtcbiAgICAgIGJyZWFrO1xuXG4gICAgY2FzZSBcIlJlc3RFbGVtZW50XCI6XG4gICAgICB0aGlzLmNoZWNrTFZhbChleHByLmFyZ3VtZW50LCBpc0JpbmRpbmcsIGNoZWNrQ2xhc2hlcyk7XG4gICAgICBicmVhaztcblxuICAgIGNhc2UgXCJQYXJlbnRoZXNpemVkRXhwcmVzc2lvblwiOlxuICAgICAgdGhpcy5jaGVja0xWYWwoZXhwci5leHByZXNzaW9uLCBpc0JpbmRpbmcsIGNoZWNrQ2xhc2hlcyk7XG4gICAgICBicmVhaztcblxuICAgIGRlZmF1bHQ6XG4gICAgICB0aGlzLnJhaXNlKGV4cHIuc3RhcnQsIChpc0JpbmRpbmcgPyBcIkJpbmRpbmdcIiA6IFwiQXNzaWduaW5nIHRvXCIpICsgXCIgcnZhbHVlXCIpO1xuICB9XG59O1xuXG59LHtcIi4vaWRlbnRpZmllclwiOjIsXCIuL3N0YXRlXCI6MTAsXCIuL3Rva2VudHlwZVwiOjE0LFwiLi91dGlsXCI6MTV9XSw3OltmdW5jdGlvbihfZGVyZXFfLG1vZHVsZSxleHBvcnRzKXtcblwidXNlIHN0cmljdFwiO1xuXG5leHBvcnRzLl9fZXNNb2R1bGUgPSB0cnVlO1xuXG5mdW5jdGlvbiBfY2xhc3NDYWxsQ2hlY2soaW5zdGFuY2UsIENvbnN0cnVjdG9yKSB7IGlmICghKGluc3RhbmNlIGluc3RhbmNlb2YgQ29uc3RydWN0b3IpKSB7IHRocm93IG5ldyBUeXBlRXJyb3IoXCJDYW5ub3QgY2FsbCBhIGNsYXNzIGFzIGEgZnVuY3Rpb25cIik7IH0gfVxuXG52YXIgX3N0YXRlID0gX2RlcmVxXyhcIi4vc3RhdGVcIik7XG5cbnZhciBfbG9jdXRpbCA9IF9kZXJlcV8oXCIuL2xvY3V0aWxcIik7XG5cbnZhciBOb2RlID0gZnVuY3Rpb24gTm9kZShwYXJzZXIsIHBvcywgbG9jKSB7XG4gIF9jbGFzc0NhbGxDaGVjayh0aGlzLCBOb2RlKTtcblxuICB0aGlzLnR5cGUgPSBcIlwiO1xuICB0aGlzLnN0YXJ0ID0gcG9zO1xuICB0aGlzLmVuZCA9IDA7XG4gIGlmIChwYXJzZXIub3B0aW9ucy5sb2NhdGlvbnMpIHRoaXMubG9jID0gbmV3IF9sb2N1dGlsLlNvdXJjZUxvY2F0aW9uKHBhcnNlciwgbG9jKTtcbiAgaWYgKHBhcnNlci5vcHRpb25zLmRpcmVjdFNvdXJjZUZpbGUpIHRoaXMuc291cmNlRmlsZSA9IHBhcnNlci5vcHRpb25zLmRpcmVjdFNvdXJjZUZpbGU7XG4gIGlmIChwYXJzZXIub3B0aW9ucy5yYW5nZXMpIHRoaXMucmFuZ2UgPSBbcG9zLCAwXTtcbn07XG5cbmV4cG9ydHMuTm9kZSA9IE5vZGU7XG5cbi8vIFN0YXJ0IGFuIEFTVCBub2RlLCBhdHRhY2hpbmcgYSBzdGFydCBvZmZzZXQuXG5cbnZhciBwcCA9IF9zdGF0ZS5QYXJzZXIucHJvdG90eXBlO1xuXG5wcC5zdGFydE5vZGUgPSBmdW5jdGlvbiAoKSB7XG4gIHJldHVybiBuZXcgTm9kZSh0aGlzLCB0aGlzLnN0YXJ0LCB0aGlzLnN0YXJ0TG9jKTtcbn07XG5cbnBwLnN0YXJ0Tm9kZUF0ID0gZnVuY3Rpb24gKHBvcywgbG9jKSB7XG4gIHJldHVybiBuZXcgTm9kZSh0aGlzLCBwb3MsIGxvYyk7XG59O1xuXG4vLyBGaW5pc2ggYW4gQVNUIG5vZGUsIGFkZGluZyBgdHlwZWAgYW5kIGBlbmRgIHByb3BlcnRpZXMuXG5cbmZ1bmN0aW9uIGZpbmlzaE5vZGVBdChub2RlLCB0eXBlLCBwb3MsIGxvYykge1xuICBub2RlLnR5cGUgPSB0eXBlO1xuICBub2RlLmVuZCA9IHBvcztcbiAgaWYgKHRoaXMub3B0aW9ucy5sb2NhdGlvbnMpIG5vZGUubG9jLmVuZCA9IGxvYztcbiAgaWYgKHRoaXMub3B0aW9ucy5yYW5nZXMpIG5vZGUucmFuZ2VbMV0gPSBwb3M7XG4gIHJldHVybiBub2RlO1xufVxuXG5wcC5maW5pc2hOb2RlID0gZnVuY3Rpb24gKG5vZGUsIHR5cGUpIHtcbiAgcmV0dXJuIGZpbmlzaE5vZGVBdC5jYWxsKHRoaXMsIG5vZGUsIHR5cGUsIHRoaXMubGFzdFRva0VuZCwgdGhpcy5sYXN0VG9rRW5kTG9jKTtcbn07XG5cbi8vIEZpbmlzaCBub2RlIGF0IGdpdmVuIHBvc2l0aW9uXG5cbnBwLmZpbmlzaE5vZGVBdCA9IGZ1bmN0aW9uIChub2RlLCB0eXBlLCBwb3MsIGxvYykge1xuICByZXR1cm4gZmluaXNoTm9kZUF0LmNhbGwodGhpcywgbm9kZSwgdHlwZSwgcG9zLCBsb2MpO1xufTtcblxufSx7XCIuL2xvY3V0aWxcIjo1LFwiLi9zdGF0ZVwiOjEwfV0sODpbZnVuY3Rpb24oX2RlcmVxXyxtb2R1bGUsZXhwb3J0cyl7XG5cInVzZSBzdHJpY3RcIjtcblxuZXhwb3J0cy5fX2VzTW9kdWxlID0gdHJ1ZTtcbmV4cG9ydHMuZ2V0T3B0aW9ucyA9IGdldE9wdGlvbnM7XG5cbnZhciBfdXRpbCA9IF9kZXJlcV8oXCIuL3V0aWxcIik7XG5cbnZhciBfbG9jdXRpbCA9IF9kZXJlcV8oXCIuL2xvY3V0aWxcIik7XG5cbi8vIEEgc2Vjb25kIG9wdGlvbmFsIGFyZ3VtZW50IGNhbiBiZSBnaXZlbiB0byBmdXJ0aGVyIGNvbmZpZ3VyZVxuLy8gdGhlIHBhcnNlciBwcm9jZXNzLiBUaGVzZSBvcHRpb25zIGFyZSByZWNvZ25pemVkOlxuXG52YXIgZGVmYXVsdE9wdGlvbnMgPSB7XG4gIC8vIGBlY21hVmVyc2lvbmAgaW5kaWNhdGVzIHRoZSBFQ01BU2NyaXB0IHZlcnNpb24gdG8gcGFyc2UuIE11c3RcbiAgLy8gYmUgZWl0aGVyIDMsIG9yIDUsIG9yIDYuIFRoaXMgaW5mbHVlbmNlcyBzdXBwb3J0IGZvciBzdHJpY3RcbiAgLy8gbW9kZSwgdGhlIHNldCBvZiByZXNlcnZlZCB3b3Jkcywgc3VwcG9ydCBmb3IgZ2V0dGVycyBhbmRcbiAgLy8gc2V0dGVycyBhbmQgb3RoZXIgZmVhdHVyZXMuXG4gIGVjbWFWZXJzaW9uOiA1LFxuICAvLyBTb3VyY2UgdHlwZSAoXCJzY3JpcHRcIiBvciBcIm1vZHVsZVwiKSBmb3IgZGlmZmVyZW50IHNlbWFudGljc1xuICBzb3VyY2VUeXBlOiBcInNjcmlwdFwiLFxuICAvLyBgb25JbnNlcnRlZFNlbWljb2xvbmAgY2FuIGJlIGEgY2FsbGJhY2sgdGhhdCB3aWxsIGJlIGNhbGxlZFxuICAvLyB3aGVuIGEgc2VtaWNvbG9uIGlzIGF1dG9tYXRpY2FsbHkgaW5zZXJ0ZWQuIEl0IHdpbGwgYmUgcGFzc2VkXG4gIC8vIHRoIHBvc2l0aW9uIG9mIHRoZSBjb21tYSBhcyBhbiBvZmZzZXQsIGFuZCBpZiBgbG9jYXRpb25zYCBpc1xuICAvLyBlbmFibGVkLCBpdCBpcyBnaXZlbiB0aGUgbG9jYXRpb24gYXMgYSBge2xpbmUsIGNvbHVtbn1gIG9iamVjdFxuICAvLyBhcyBzZWNvbmQgYXJndW1lbnQuXG4gIG9uSW5zZXJ0ZWRTZW1pY29sb246IG51bGwsXG4gIC8vIGBvblRyYWlsaW5nQ29tbWFgIGlzIHNpbWlsYXIgdG8gYG9uSW5zZXJ0ZWRTZW1pY29sb25gLCBidXQgZm9yXG4gIC8vIHRyYWlsaW5nIGNvbW1hcy5cbiAgb25UcmFpbGluZ0NvbW1hOiBudWxsLFxuICAvLyBCeSBkZWZhdWx0LCByZXNlcnZlZCB3b3JkcyBhcmUgbm90IGVuZm9yY2VkLiBEaXNhYmxlXG4gIC8vIGBhbGxvd1Jlc2VydmVkYCB0byBlbmZvcmNlIHRoZW0uIFdoZW4gdGhpcyBvcHRpb24gaGFzIHRoZVxuICAvLyB2YWx1ZSBcIm5ldmVyXCIsIHJlc2VydmVkIHdvcmRzIGFuZCBrZXl3b3JkcyBjYW4gYWxzbyBub3QgYmVcbiAgLy8gdXNlZCBhcyBwcm9wZXJ0eSBuYW1lcy5cbiAgYWxsb3dSZXNlcnZlZDogdHJ1ZSxcbiAgLy8gV2hlbiBlbmFibGVkLCBhIHJldHVybiBhdCB0aGUgdG9wIGxldmVsIGlzIG5vdCBjb25zaWRlcmVkIGFuXG4gIC8vIGVycm9yLlxuICBhbGxvd1JldHVybk91dHNpZGVGdW5jdGlvbjogZmFsc2UsXG4gIC8vIFdoZW4gZW5hYmxlZCwgaW1wb3J0L2V4cG9ydCBzdGF0ZW1lbnRzIGFyZSBub3QgY29uc3RyYWluZWQgdG9cbiAgLy8gYXBwZWFyaW5nIGF0IHRoZSB0b3Agb2YgdGhlIHByb2dyYW0uXG4gIGFsbG93SW1wb3J0RXhwb3J0RXZlcnl3aGVyZTogZmFsc2UsXG4gIC8vIFdoZW4gZW5hYmxlZCwgaGFzaGJhbmcgZGlyZWN0aXZlIGluIHRoZSBiZWdpbm5pbmcgb2YgZmlsZVxuICAvLyBpcyBhbGxvd2VkIGFuZCB0cmVhdGVkIGFzIGEgbGluZSBjb21tZW50LlxuICBhbGxvd0hhc2hCYW5nOiBmYWxzZSxcbiAgLy8gV2hlbiBgbG9jYXRpb25zYCBpcyBvbiwgYGxvY2AgcHJvcGVydGllcyBob2xkaW5nIG9iamVjdHMgd2l0aFxuICAvLyBgc3RhcnRgIGFuZCBgZW5kYCBwcm9wZXJ0aWVzIGluIGB7bGluZSwgY29sdW1ufWAgZm9ybSAod2l0aFxuICAvLyBsaW5lIGJlaW5nIDEtYmFzZWQgYW5kIGNvbHVtbiAwLWJhc2VkKSB3aWxsIGJlIGF0dGFjaGVkIHRvIHRoZVxuICAvLyBub2Rlcy5cbiAgbG9jYXRpb25zOiBmYWxzZSxcbiAgLy8gQSBmdW5jdGlvbiBjYW4gYmUgcGFzc2VkIGFzIGBvblRva2VuYCBvcHRpb24sIHdoaWNoIHdpbGxcbiAgLy8gY2F1c2UgQWNvcm4gdG8gY2FsbCB0aGF0IGZ1bmN0aW9uIHdpdGggb2JqZWN0IGluIHRoZSBzYW1lXG4gIC8vIGZvcm1hdCBhcyB0b2tlbml6ZSgpIHJldHVybnMuIE5vdGUgdGhhdCB5b3UgYXJlIG5vdFxuICAvLyBhbGxvd2VkIHRvIGNhbGwgdGhlIHBhcnNlciBmcm9tIHRoZSBjYWxsYmFja+KAlHRoYXQgd2lsbFxuICAvLyBjb3JydXB0IGl0cyBpbnRlcm5hbCBzdGF0ZS5cbiAgb25Ub2tlbjogbnVsbCxcbiAgLy8gQSBmdW5jdGlvbiBjYW4gYmUgcGFzc2VkIGFzIGBvbkNvbW1lbnRgIG9wdGlvbiwgd2hpY2ggd2lsbFxuICAvLyBjYXVzZSBBY29ybiB0byBjYWxsIHRoYXQgZnVuY3Rpb24gd2l0aCBgKGJsb2NrLCB0ZXh0LCBzdGFydCxcbiAgLy8gZW5kKWAgcGFyYW1ldGVycyB3aGVuZXZlciBhIGNvbW1lbnQgaXMgc2tpcHBlZC4gYGJsb2NrYCBpcyBhXG4gIC8vIGJvb2xlYW4gaW5kaWNhdGluZyB3aGV0aGVyIHRoaXMgaXMgYSBibG9jayAoYC8qICovYCkgY29tbWVudCxcbiAgLy8gYHRleHRgIGlzIHRoZSBjb250ZW50IG9mIHRoZSBjb21tZW50LCBhbmQgYHN0YXJ0YCBhbmQgYGVuZGAgYXJlXG4gIC8vIGNoYXJhY3RlciBvZmZzZXRzIHRoYXQgZGVub3RlIHRoZSBzdGFydCBhbmQgZW5kIG9mIHRoZSBjb21tZW50LlxuICAvLyBXaGVuIHRoZSBgbG9jYXRpb25zYCBvcHRpb24gaXMgb24sIHR3byBtb3JlIHBhcmFtZXRlcnMgYXJlXG4gIC8vIHBhc3NlZCwgdGhlIGZ1bGwgYHtsaW5lLCBjb2x1bW59YCBsb2NhdGlvbnMgb2YgdGhlIHN0YXJ0IGFuZFxuICAvLyBlbmQgb2YgdGhlIGNvbW1lbnRzLiBOb3RlIHRoYXQgeW91IGFyZSBub3QgYWxsb3dlZCB0byBjYWxsIHRoZVxuICAvLyBwYXJzZXIgZnJvbSB0aGUgY2FsbGJhY2vigJR0aGF0IHdpbGwgY29ycnVwdCBpdHMgaW50ZXJuYWwgc3RhdGUuXG4gIG9uQ29tbWVudDogbnVsbCxcbiAgLy8gTm9kZXMgaGF2ZSB0aGVpciBzdGFydCBhbmQgZW5kIGNoYXJhY3RlcnMgb2Zmc2V0cyByZWNvcmRlZCBpblxuICAvLyBgc3RhcnRgIGFuZCBgZW5kYCBwcm9wZXJ0aWVzIChkaXJlY3RseSBvbiB0aGUgbm9kZSwgcmF0aGVyIHRoYW5cbiAgLy8gdGhlIGBsb2NgIG9iamVjdCwgd2hpY2ggaG9sZHMgbGluZS9jb2x1bW4gZGF0YS4gVG8gYWxzbyBhZGQgYVxuICAvLyBbc2VtaS1zdGFuZGFyZGl6ZWRdW3JhbmdlXSBgcmFuZ2VgIHByb3BlcnR5IGhvbGRpbmcgYSBgW3N0YXJ0LFxuICAvLyBlbmRdYCBhcnJheSB3aXRoIHRoZSBzYW1lIG51bWJlcnMsIHNldCB0aGUgYHJhbmdlc2Agb3B0aW9uIHRvXG4gIC8vIGB0cnVlYC5cbiAgLy9cbiAgLy8gW3JhbmdlXTogaHR0cHM6Ly9idWd6aWxsYS5tb3ppbGxhLm9yZy9zaG93X2J1Zy5jZ2k/aWQ9NzQ1Njc4XG4gIHJhbmdlczogZmFsc2UsXG4gIC8vIEl0IGlzIHBvc3NpYmxlIHRvIHBhcnNlIG11bHRpcGxlIGZpbGVzIGludG8gYSBzaW5nbGUgQVNUIGJ5XG4gIC8vIHBhc3NpbmcgdGhlIHRyZWUgcHJvZHVjZWQgYnkgcGFyc2luZyB0aGUgZmlyc3QgZmlsZSBhc1xuICAvLyBgcHJvZ3JhbWAgb3B0aW9uIGluIHN1YnNlcXVlbnQgcGFyc2VzLiBUaGlzIHdpbGwgYWRkIHRoZVxuICAvLyB0b3BsZXZlbCBmb3JtcyBvZiB0aGUgcGFyc2VkIGZpbGUgdG8gdGhlIGBQcm9ncmFtYCAodG9wKSBub2RlXG4gIC8vIG9mIGFuIGV4aXN0aW5nIHBhcnNlIHRyZWUuXG4gIHByb2dyYW06IG51bGwsXG4gIC8vIFdoZW4gYGxvY2F0aW9uc2AgaXMgb24sIHlvdSBjYW4gcGFzcyB0aGlzIHRvIHJlY29yZCB0aGUgc291cmNlXG4gIC8vIGZpbGUgaW4gZXZlcnkgbm9kZSdzIGBsb2NgIG9iamVjdC5cbiAgc291cmNlRmlsZTogbnVsbCxcbiAgLy8gVGhpcyB2YWx1ZSwgaWYgZ2l2ZW4sIGlzIHN0b3JlZCBpbiBldmVyeSBub2RlLCB3aGV0aGVyXG4gIC8vIGBsb2NhdGlvbnNgIGlzIG9uIG9yIG9mZi5cbiAgZGlyZWN0U291cmNlRmlsZTogbnVsbCxcbiAgLy8gV2hlbiBlbmFibGVkLCBwYXJlbnRoZXNpemVkIGV4cHJlc3Npb25zIGFyZSByZXByZXNlbnRlZCBieVxuICAvLyAobm9uLXN0YW5kYXJkKSBQYXJlbnRoZXNpemVkRXhwcmVzc2lvbiBub2Rlc1xuICBwcmVzZXJ2ZVBhcmVuczogZmFsc2UsXG4gIHBsdWdpbnM6IHt9XG59O1xuXG5leHBvcnRzLmRlZmF1bHRPcHRpb25zID0gZGVmYXVsdE9wdGlvbnM7XG4vLyBJbnRlcnByZXQgYW5kIGRlZmF1bHQgYW4gb3B0aW9ucyBvYmplY3RcblxuZnVuY3Rpb24gZ2V0T3B0aW9ucyhvcHRzKSB7XG4gIHZhciBvcHRpb25zID0ge307XG4gIGZvciAodmFyIG9wdCBpbiBkZWZhdWx0T3B0aW9ucykge1xuICAgIG9wdGlvbnNbb3B0XSA9IG9wdHMgJiYgX3V0aWwuaGFzKG9wdHMsIG9wdCkgPyBvcHRzW29wdF0gOiBkZWZhdWx0T3B0aW9uc1tvcHRdO1xuICB9aWYgKF91dGlsLmlzQXJyYXkob3B0aW9ucy5vblRva2VuKSkge1xuICAgIChmdW5jdGlvbiAoKSB7XG4gICAgICB2YXIgdG9rZW5zID0gb3B0aW9ucy5vblRva2VuO1xuICAgICAgb3B0aW9ucy5vblRva2VuID0gZnVuY3Rpb24gKHRva2VuKSB7XG4gICAgICAgIHJldHVybiB0b2tlbnMucHVzaCh0b2tlbik7XG4gICAgICB9O1xuICAgIH0pKCk7XG4gIH1cbiAgaWYgKF91dGlsLmlzQXJyYXkob3B0aW9ucy5vbkNvbW1lbnQpKSBvcHRpb25zLm9uQ29tbWVudCA9IHB1c2hDb21tZW50KG9wdGlvbnMsIG9wdGlvbnMub25Db21tZW50KTtcblxuICByZXR1cm4gb3B0aW9ucztcbn1cblxuZnVuY3Rpb24gcHVzaENvbW1lbnQob3B0aW9ucywgYXJyYXkpIHtcbiAgcmV0dXJuIGZ1bmN0aW9uIChibG9jaywgdGV4dCwgc3RhcnQsIGVuZCwgc3RhcnRMb2MsIGVuZExvYykge1xuICAgIHZhciBjb21tZW50ID0ge1xuICAgICAgdHlwZTogYmxvY2sgPyBcIkJsb2NrXCIgOiBcIkxpbmVcIixcbiAgICAgIHZhbHVlOiB0ZXh0LFxuICAgICAgc3RhcnQ6IHN0YXJ0LFxuICAgICAgZW5kOiBlbmRcbiAgICB9O1xuICAgIGlmIChvcHRpb25zLmxvY2F0aW9ucykgY29tbWVudC5sb2MgPSBuZXcgX2xvY3V0aWwuU291cmNlTG9jYXRpb24odGhpcywgc3RhcnRMb2MsIGVuZExvYyk7XG4gICAgaWYgKG9wdGlvbnMucmFuZ2VzKSBjb21tZW50LnJhbmdlID0gW3N0YXJ0LCBlbmRdO1xuICAgIGFycmF5LnB1c2goY29tbWVudCk7XG4gIH07XG59XG5cbn0se1wiLi9sb2N1dGlsXCI6NSxcIi4vdXRpbFwiOjE1fV0sOTpbZnVuY3Rpb24oX2RlcmVxXyxtb2R1bGUsZXhwb3J0cyl7XG5cInVzZSBzdHJpY3RcIjtcblxudmFyIF90b2tlbnR5cGUgPSBfZGVyZXFfKFwiLi90b2tlbnR5cGVcIik7XG5cbnZhciBfc3RhdGUgPSBfZGVyZXFfKFwiLi9zdGF0ZVwiKTtcblxudmFyIF93aGl0ZXNwYWNlID0gX2RlcmVxXyhcIi4vd2hpdGVzcGFjZVwiKTtcblxudmFyIHBwID0gX3N0YXRlLlBhcnNlci5wcm90b3R5cGU7XG5cbi8vICMjIFBhcnNlciB1dGlsaXRpZXNcblxuLy8gVGVzdCB3aGV0aGVyIGEgc3RhdGVtZW50IG5vZGUgaXMgdGhlIHN0cmluZyBsaXRlcmFsIGBcInVzZSBzdHJpY3RcImAuXG5cbnBwLmlzVXNlU3RyaWN0ID0gZnVuY3Rpb24gKHN0bXQpIHtcbiAgcmV0dXJuIHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA1ICYmIHN0bXQudHlwZSA9PT0gXCJFeHByZXNzaW9uU3RhdGVtZW50XCIgJiYgc3RtdC5leHByZXNzaW9uLnR5cGUgPT09IFwiTGl0ZXJhbFwiICYmIHN0bXQuZXhwcmVzc2lvbi5yYXcuc2xpY2UoMSwgLTEpID09PSBcInVzZSBzdHJpY3RcIjtcbn07XG5cbi8vIFByZWRpY2F0ZSB0aGF0IHRlc3RzIHdoZXRoZXIgdGhlIG5leHQgdG9rZW4gaXMgb2YgdGhlIGdpdmVuXG4vLyB0eXBlLCBhbmQgaWYgeWVzLCBjb25zdW1lcyBpdCBhcyBhIHNpZGUgZWZmZWN0LlxuXG5wcC5lYXQgPSBmdW5jdGlvbiAodHlwZSkge1xuICBpZiAodGhpcy50eXBlID09PSB0eXBlKSB7XG4gICAgdGhpcy5uZXh0KCk7XG4gICAgcmV0dXJuIHRydWU7XG4gIH0gZWxzZSB7XG4gICAgcmV0dXJuIGZhbHNlO1xuICB9XG59O1xuXG4vLyBUZXN0cyB3aGV0aGVyIHBhcnNlZCB0b2tlbiBpcyBhIGNvbnRleHR1YWwga2V5d29yZC5cblxucHAuaXNDb250ZXh0dWFsID0gZnVuY3Rpb24gKG5hbWUpIHtcbiAgcmV0dXJuIHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5uYW1lICYmIHRoaXMudmFsdWUgPT09IG5hbWU7XG59O1xuXG4vLyBDb25zdW1lcyBjb250ZXh0dWFsIGtleXdvcmQgaWYgcG9zc2libGUuXG5cbnBwLmVhdENvbnRleHR1YWwgPSBmdW5jdGlvbiAobmFtZSkge1xuICByZXR1cm4gdGhpcy52YWx1ZSA9PT0gbmFtZSAmJiB0aGlzLmVhdChfdG9rZW50eXBlLnR5cGVzLm5hbWUpO1xufTtcblxuLy8gQXNzZXJ0cyB0aGF0IGZvbGxvd2luZyB0b2tlbiBpcyBnaXZlbiBjb250ZXh0dWFsIGtleXdvcmQuXG5cbnBwLmV4cGVjdENvbnRleHR1YWwgPSBmdW5jdGlvbiAobmFtZSkge1xuICBpZiAoIXRoaXMuZWF0Q29udGV4dHVhbChuYW1lKSkgdGhpcy51bmV4cGVjdGVkKCk7XG59O1xuXG4vLyBUZXN0IHdoZXRoZXIgYSBzZW1pY29sb24gY2FuIGJlIGluc2VydGVkIGF0IHRoZSBjdXJyZW50IHBvc2l0aW9uLlxuXG5wcC5jYW5JbnNlcnRTZW1pY29sb24gPSBmdW5jdGlvbiAoKSB7XG4gIHJldHVybiB0aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuZW9mIHx8IHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5icmFjZVIgfHwgX3doaXRlc3BhY2UubGluZUJyZWFrLnRlc3QodGhpcy5pbnB1dC5zbGljZSh0aGlzLmxhc3RUb2tFbmQsIHRoaXMuc3RhcnQpKTtcbn07XG5cbnBwLmluc2VydFNlbWljb2xvbiA9IGZ1bmN0aW9uICgpIHtcbiAgaWYgKHRoaXMuY2FuSW5zZXJ0U2VtaWNvbG9uKCkpIHtcbiAgICBpZiAodGhpcy5vcHRpb25zLm9uSW5zZXJ0ZWRTZW1pY29sb24pIHRoaXMub3B0aW9ucy5vbkluc2VydGVkU2VtaWNvbG9uKHRoaXMubGFzdFRva0VuZCwgdGhpcy5sYXN0VG9rRW5kTG9jKTtcbiAgICByZXR1cm4gdHJ1ZTtcbiAgfVxufTtcblxuLy8gQ29uc3VtZSBhIHNlbWljb2xvbiwgb3IsIGZhaWxpbmcgdGhhdCwgc2VlIGlmIHdlIGFyZSBhbGxvd2VkIHRvXG4vLyBwcmV0ZW5kIHRoYXQgdGhlcmUgaXMgYSBzZW1pY29sb24gYXQgdGhpcyBwb3NpdGlvbi5cblxucHAuc2VtaWNvbG9uID0gZnVuY3Rpb24gKCkge1xuICBpZiAoIXRoaXMuZWF0KF90b2tlbnR5cGUudHlwZXMuc2VtaSkgJiYgIXRoaXMuaW5zZXJ0U2VtaWNvbG9uKCkpIHRoaXMudW5leHBlY3RlZCgpO1xufTtcblxucHAuYWZ0ZXJUcmFpbGluZ0NvbW1hID0gZnVuY3Rpb24gKHRva1R5cGUpIHtcbiAgaWYgKHRoaXMudHlwZSA9PSB0b2tUeXBlKSB7XG4gICAgaWYgKHRoaXMub3B0aW9ucy5vblRyYWlsaW5nQ29tbWEpIHRoaXMub3B0aW9ucy5vblRyYWlsaW5nQ29tbWEodGhpcy5sYXN0VG9rU3RhcnQsIHRoaXMubGFzdFRva1N0YXJ0TG9jKTtcbiAgICB0aGlzLm5leHQoKTtcbiAgICByZXR1cm4gdHJ1ZTtcbiAgfVxufTtcblxuLy8gRXhwZWN0IGEgdG9rZW4gb2YgYSBnaXZlbiB0eXBlLiBJZiBmb3VuZCwgY29uc3VtZSBpdCwgb3RoZXJ3aXNlLFxuLy8gcmFpc2UgYW4gdW5leHBlY3RlZCB0b2tlbiBlcnJvci5cblxucHAuZXhwZWN0ID0gZnVuY3Rpb24gKHR5cGUpIHtcbiAgdGhpcy5lYXQodHlwZSkgfHwgdGhpcy51bmV4cGVjdGVkKCk7XG59O1xuXG4vLyBSYWlzZSBhbiB1bmV4cGVjdGVkIHRva2VuIGVycm9yLlxuXG5wcC51bmV4cGVjdGVkID0gZnVuY3Rpb24gKHBvcykge1xuICB0aGlzLnJhaXNlKHBvcyAhPSBudWxsID8gcG9zIDogdGhpcy5zdGFydCwgXCJVbmV4cGVjdGVkIHRva2VuXCIpO1xufTtcblxufSx7XCIuL3N0YXRlXCI6MTAsXCIuL3Rva2VudHlwZVwiOjE0LFwiLi93aGl0ZXNwYWNlXCI6MTZ9XSwxMDpbZnVuY3Rpb24oX2RlcmVxXyxtb2R1bGUsZXhwb3J0cyl7XG5cInVzZSBzdHJpY3RcIjtcblxuZXhwb3J0cy5fX2VzTW9kdWxlID0gdHJ1ZTtcblxuZnVuY3Rpb24gX2NsYXNzQ2FsbENoZWNrKGluc3RhbmNlLCBDb25zdHJ1Y3RvcikgeyBpZiAoIShpbnN0YW5jZSBpbnN0YW5jZW9mIENvbnN0cnVjdG9yKSkgeyB0aHJvdyBuZXcgVHlwZUVycm9yKFwiQ2Fubm90IGNhbGwgYSBjbGFzcyBhcyBhIGZ1bmN0aW9uXCIpOyB9IH1cblxudmFyIF9pZGVudGlmaWVyID0gX2RlcmVxXyhcIi4vaWRlbnRpZmllclwiKTtcblxudmFyIF90b2tlbnR5cGUgPSBfZGVyZXFfKFwiLi90b2tlbnR5cGVcIik7XG5cbnZhciBfd2hpdGVzcGFjZSA9IF9kZXJlcV8oXCIuL3doaXRlc3BhY2VcIik7XG5cbnZhciBfb3B0aW9ucyA9IF9kZXJlcV8oXCIuL29wdGlvbnNcIik7XG5cbi8vIFJlZ2lzdGVyZWQgcGx1Z2luc1xudmFyIHBsdWdpbnMgPSB7fTtcblxuZXhwb3J0cy5wbHVnaW5zID0gcGx1Z2lucztcblxudmFyIFBhcnNlciA9IChmdW5jdGlvbiAoKSB7XG4gIGZ1bmN0aW9uIFBhcnNlcihvcHRpb25zLCBpbnB1dCwgc3RhcnRQb3MpIHtcbiAgICBfY2xhc3NDYWxsQ2hlY2sodGhpcywgUGFyc2VyKTtcblxuICAgIHRoaXMub3B0aW9ucyA9IF9vcHRpb25zLmdldE9wdGlvbnMob3B0aW9ucyk7XG4gICAgdGhpcy5zb3VyY2VGaWxlID0gdGhpcy5vcHRpb25zLnNvdXJjZUZpbGU7XG4gICAgdGhpcy5pc0tleXdvcmQgPSBfaWRlbnRpZmllci5rZXl3b3Jkc1t0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNiA/IDYgOiA1XTtcbiAgICB0aGlzLmlzUmVzZXJ2ZWRXb3JkID0gX2lkZW50aWZpZXIucmVzZXJ2ZWRXb3Jkc1t0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb25dO1xuICAgIHRoaXMuaW5wdXQgPSBTdHJpbmcoaW5wdXQpO1xuXG4gICAgLy8gVXNlZCB0byBzaWduYWwgdG8gY2FsbGVycyBvZiBgcmVhZFdvcmQxYCB3aGV0aGVyIHRoZSB3b3JkXG4gICAgLy8gY29udGFpbmVkIGFueSBlc2NhcGUgc2VxdWVuY2VzLiBUaGlzIGlzIG5lZWRlZCBiZWNhdXNlIHdvcmRzIHdpdGhcbiAgICAvLyBlc2NhcGUgc2VxdWVuY2VzIG11c3Qgbm90IGJlIGludGVycHJldGVkIGFzIGtleXdvcmRzLlxuICAgIHRoaXMuY29udGFpbnNFc2MgPSBmYWxzZTtcblxuICAgIC8vIExvYWQgcGx1Z2luc1xuICAgIHRoaXMubG9hZFBsdWdpbnModGhpcy5vcHRpb25zLnBsdWdpbnMpO1xuXG4gICAgLy8gU2V0IHVwIHRva2VuIHN0YXRlXG5cbiAgICAvLyBUaGUgY3VycmVudCBwb3NpdGlvbiBvZiB0aGUgdG9rZW5pemVyIGluIHRoZSBpbnB1dC5cbiAgICBpZiAoc3RhcnRQb3MpIHtcbiAgICAgIHRoaXMucG9zID0gc3RhcnRQb3M7XG4gICAgICB0aGlzLmxpbmVTdGFydCA9IE1hdGgubWF4KDAsIHRoaXMuaW5wdXQubGFzdEluZGV4T2YoXCJcXG5cIiwgc3RhcnRQb3MpKTtcbiAgICAgIHRoaXMuY3VyTGluZSA9IHRoaXMuaW5wdXQuc2xpY2UoMCwgdGhpcy5saW5lU3RhcnQpLnNwbGl0KF93aGl0ZXNwYWNlLmxpbmVCcmVhaykubGVuZ3RoO1xuICAgIH0gZWxzZSB7XG4gICAgICB0aGlzLnBvcyA9IHRoaXMubGluZVN0YXJ0ID0gMDtcbiAgICAgIHRoaXMuY3VyTGluZSA9IDE7XG4gICAgfVxuXG4gICAgLy8gUHJvcGVydGllcyBvZiB0aGUgY3VycmVudCB0b2tlbjpcbiAgICAvLyBJdHMgdHlwZVxuICAgIHRoaXMudHlwZSA9IF90b2tlbnR5cGUudHlwZXMuZW9mO1xuICAgIC8vIEZvciB0b2tlbnMgdGhhdCBpbmNsdWRlIG1vcmUgaW5mb3JtYXRpb24gdGhhbiB0aGVpciB0eXBlLCB0aGUgdmFsdWVcbiAgICB0aGlzLnZhbHVlID0gbnVsbDtcbiAgICAvLyBJdHMgc3RhcnQgYW5kIGVuZCBvZmZzZXRcbiAgICB0aGlzLnN0YXJ0ID0gdGhpcy5lbmQgPSB0aGlzLnBvcztcbiAgICAvLyBBbmQsIGlmIGxvY2F0aW9ucyBhcmUgdXNlZCwgdGhlIHtsaW5lLCBjb2x1bW59IG9iamVjdFxuICAgIC8vIGNvcnJlc3BvbmRpbmcgdG8gdGhvc2Ugb2Zmc2V0c1xuICAgIHRoaXMuc3RhcnRMb2MgPSB0aGlzLmVuZExvYyA9IHRoaXMuY3VyUG9zaXRpb24oKTtcblxuICAgIC8vIFBvc2l0aW9uIGluZm9ybWF0aW9uIGZvciB0aGUgcHJldmlvdXMgdG9rZW5cbiAgICB0aGlzLmxhc3RUb2tFbmRMb2MgPSB0aGlzLmxhc3RUb2tTdGFydExvYyA9IG51bGw7XG4gICAgdGhpcy5sYXN0VG9rU3RhcnQgPSB0aGlzLmxhc3RUb2tFbmQgPSB0aGlzLnBvcztcblxuICAgIC8vIFRoZSBjb250ZXh0IHN0YWNrIGlzIHVzZWQgdG8gc3VwZXJmaWNpYWxseSB0cmFjayBzeW50YWN0aWNcbiAgICAvLyBjb250ZXh0IHRvIHByZWRpY3Qgd2hldGhlciBhIHJlZ3VsYXIgZXhwcmVzc2lvbiBpcyBhbGxvd2VkIGluIGFcbiAgICAvLyBnaXZlbiBwb3NpdGlvbi5cbiAgICB0aGlzLmNvbnRleHQgPSB0aGlzLmluaXRpYWxDb250ZXh0KCk7XG4gICAgdGhpcy5leHByQWxsb3dlZCA9IHRydWU7XG5cbiAgICAvLyBGaWd1cmUgb3V0IGlmIGl0J3MgYSBtb2R1bGUgY29kZS5cbiAgICB0aGlzLnN0cmljdCA9IHRoaXMuaW5Nb2R1bGUgPSB0aGlzLm9wdGlvbnMuc291cmNlVHlwZSA9PT0gXCJtb2R1bGVcIjtcblxuICAgIC8vIFVzZWQgdG8gc2lnbmlmeSB0aGUgc3RhcnQgb2YgYSBwb3RlbnRpYWwgYXJyb3cgZnVuY3Rpb25cbiAgICB0aGlzLnBvdGVudGlhbEFycm93QXQgPSAtMTtcblxuICAgIC8vIEZsYWdzIHRvIHRyYWNrIHdoZXRoZXIgd2UgYXJlIGluIGEgZnVuY3Rpb24sIGEgZ2VuZXJhdG9yLlxuICAgIHRoaXMuaW5GdW5jdGlvbiA9IHRoaXMuaW5HZW5lcmF0b3IgPSBmYWxzZTtcbiAgICAvLyBMYWJlbHMgaW4gc2NvcGUuXG4gICAgdGhpcy5sYWJlbHMgPSBbXTtcblxuICAgIC8vIElmIGVuYWJsZWQsIHNraXAgbGVhZGluZyBoYXNoYmFuZyBsaW5lLlxuICAgIGlmICh0aGlzLnBvcyA9PT0gMCAmJiB0aGlzLm9wdGlvbnMuYWxsb3dIYXNoQmFuZyAmJiB0aGlzLmlucHV0LnNsaWNlKDAsIDIpID09PSBcIiMhXCIpIHRoaXMuc2tpcExpbmVDb21tZW50KDIpO1xuICB9XG5cbiAgUGFyc2VyLnByb3RvdHlwZS5leHRlbmQgPSBmdW5jdGlvbiBleHRlbmQobmFtZSwgZikge1xuICAgIHRoaXNbbmFtZV0gPSBmKHRoaXNbbmFtZV0pO1xuICB9O1xuXG4gIFBhcnNlci5wcm90b3R5cGUubG9hZFBsdWdpbnMgPSBmdW5jdGlvbiBsb2FkUGx1Z2lucyhwbHVnaW5Db25maWdzKSB7XG4gICAgZm9yICh2YXIgX25hbWUgaW4gcGx1Z2luQ29uZmlncykge1xuICAgICAgdmFyIHBsdWdpbiA9IHBsdWdpbnNbX25hbWVdO1xuICAgICAgaWYgKCFwbHVnaW4pIHRocm93IG5ldyBFcnJvcihcIlBsdWdpbiAnXCIgKyBfbmFtZSArIFwiJyBub3QgZm91bmRcIik7XG4gICAgICBwbHVnaW4odGhpcywgcGx1Z2luQ29uZmlnc1tfbmFtZV0pO1xuICAgIH1cbiAgfTtcblxuICBQYXJzZXIucHJvdG90eXBlLnBhcnNlID0gZnVuY3Rpb24gcGFyc2UoKSB7XG4gICAgdmFyIG5vZGUgPSB0aGlzLm9wdGlvbnMucHJvZ3JhbSB8fCB0aGlzLnN0YXJ0Tm9kZSgpO1xuICAgIHRoaXMubmV4dFRva2VuKCk7XG4gICAgcmV0dXJuIHRoaXMucGFyc2VUb3BMZXZlbChub2RlKTtcbiAgfTtcblxuICByZXR1cm4gUGFyc2VyO1xufSkoKTtcblxuZXhwb3J0cy5QYXJzZXIgPSBQYXJzZXI7XG5cbn0se1wiLi9pZGVudGlmaWVyXCI6MixcIi4vb3B0aW9uc1wiOjgsXCIuL3Rva2VudHlwZVwiOjE0LFwiLi93aGl0ZXNwYWNlXCI6MTZ9XSwxMTpbZnVuY3Rpb24oX2RlcmVxXyxtb2R1bGUsZXhwb3J0cyl7XG5cInVzZSBzdHJpY3RcIjtcblxudmFyIF90b2tlbnR5cGUgPSBfZGVyZXFfKFwiLi90b2tlbnR5cGVcIik7XG5cbnZhciBfc3RhdGUgPSBfZGVyZXFfKFwiLi9zdGF0ZVwiKTtcblxudmFyIF93aGl0ZXNwYWNlID0gX2RlcmVxXyhcIi4vd2hpdGVzcGFjZVwiKTtcblxudmFyIHBwID0gX3N0YXRlLlBhcnNlci5wcm90b3R5cGU7XG5cbi8vICMjIyBTdGF0ZW1lbnQgcGFyc2luZ1xuXG4vLyBQYXJzZSBhIHByb2dyYW0uIEluaXRpYWxpemVzIHRoZSBwYXJzZXIsIHJlYWRzIGFueSBudW1iZXIgb2Zcbi8vIHN0YXRlbWVudHMsIGFuZCB3cmFwcyB0aGVtIGluIGEgUHJvZ3JhbSBub2RlLiAgT3B0aW9uYWxseSB0YWtlcyBhXG4vLyBgcHJvZ3JhbWAgYXJndW1lbnQuICBJZiBwcmVzZW50LCB0aGUgc3RhdGVtZW50cyB3aWxsIGJlIGFwcGVuZGVkXG4vLyB0byBpdHMgYm9keSBpbnN0ZWFkIG9mIGNyZWF0aW5nIGEgbmV3IG5vZGUuXG5cbnBwLnBhcnNlVG9wTGV2ZWwgPSBmdW5jdGlvbiAobm9kZSkge1xuICB2YXIgZmlyc3QgPSB0cnVlO1xuICBpZiAoIW5vZGUuYm9keSkgbm9kZS5ib2R5ID0gW107XG4gIHdoaWxlICh0aGlzLnR5cGUgIT09IF90b2tlbnR5cGUudHlwZXMuZW9mKSB7XG4gICAgdmFyIHN0bXQgPSB0aGlzLnBhcnNlU3RhdGVtZW50KHRydWUsIHRydWUpO1xuICAgIG5vZGUuYm9keS5wdXNoKHN0bXQpO1xuICAgIGlmIChmaXJzdCkge1xuICAgICAgaWYgKHRoaXMuaXNVc2VTdHJpY3Qoc3RtdCkpIHRoaXMuc2V0U3RyaWN0KHRydWUpO1xuICAgICAgZmlyc3QgPSBmYWxzZTtcbiAgICB9XG4gIH1cbiAgdGhpcy5uZXh0KCk7XG4gIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNikge1xuICAgIG5vZGUuc291cmNlVHlwZSA9IHRoaXMub3B0aW9ucy5zb3VyY2VUeXBlO1xuICB9XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJQcm9ncmFtXCIpO1xufTtcblxudmFyIGxvb3BMYWJlbCA9IHsga2luZDogXCJsb29wXCIgfSxcbiAgICBzd2l0Y2hMYWJlbCA9IHsga2luZDogXCJzd2l0Y2hcIiB9O1xuXG4vLyBQYXJzZSBhIHNpbmdsZSBzdGF0ZW1lbnQuXG4vL1xuLy8gSWYgZXhwZWN0aW5nIGEgc3RhdGVtZW50IGFuZCBmaW5kaW5nIGEgc2xhc2ggb3BlcmF0b3IsIHBhcnNlIGFcbi8vIHJlZ3VsYXIgZXhwcmVzc2lvbiBsaXRlcmFsLiBUaGlzIGlzIHRvIGhhbmRsZSBjYXNlcyBsaWtlXG4vLyBgaWYgKGZvbykgL2JsYWgvLmV4ZWMoZm9vKWAsIHdoZXJlIGxvb2tpbmcgYXQgdGhlIHByZXZpb3VzIHRva2VuXG4vLyBkb2VzIG5vdCBoZWxwLlxuXG5wcC5wYXJzZVN0YXRlbWVudCA9IGZ1bmN0aW9uIChkZWNsYXJhdGlvbiwgdG9wTGV2ZWwpIHtcbiAgdmFyIHN0YXJ0dHlwZSA9IHRoaXMudHlwZSxcbiAgICAgIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuXG4gIC8vIE1vc3QgdHlwZXMgb2Ygc3RhdGVtZW50cyBhcmUgcmVjb2duaXplZCBieSB0aGUga2V5d29yZCB0aGV5XG4gIC8vIHN0YXJ0IHdpdGguIE1hbnkgYXJlIHRyaXZpYWwgdG8gcGFyc2UsIHNvbWUgcmVxdWlyZSBhIGJpdCBvZlxuICAvLyBjb21wbGV4aXR5LlxuXG4gIHN3aXRjaCAoc3RhcnR0eXBlKSB7XG4gICAgY2FzZSBfdG9rZW50eXBlLnR5cGVzLl9icmVhazpjYXNlIF90b2tlbnR5cGUudHlwZXMuX2NvbnRpbnVlOlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VCcmVha0NvbnRpbnVlU3RhdGVtZW50KG5vZGUsIHN0YXJ0dHlwZS5rZXl3b3JkKTtcbiAgICBjYXNlIF90b2tlbnR5cGUudHlwZXMuX2RlYnVnZ2VyOlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VEZWJ1Z2dlclN0YXRlbWVudChub2RlKTtcbiAgICBjYXNlIF90b2tlbnR5cGUudHlwZXMuX2RvOlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VEb1N0YXRlbWVudChub2RlKTtcbiAgICBjYXNlIF90b2tlbnR5cGUudHlwZXMuX2ZvcjpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlRm9yU3RhdGVtZW50KG5vZGUpO1xuICAgIGNhc2UgX3Rva2VudHlwZS50eXBlcy5fZnVuY3Rpb246XG4gICAgICBpZiAoIWRlY2xhcmF0aW9uICYmIHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KSB0aGlzLnVuZXhwZWN0ZWQoKTtcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlRnVuY3Rpb25TdGF0ZW1lbnQobm9kZSk7XG4gICAgY2FzZSBfdG9rZW50eXBlLnR5cGVzLl9jbGFzczpcbiAgICAgIGlmICghZGVjbGFyYXRpb24pIHRoaXMudW5leHBlY3RlZCgpO1xuICAgICAgcmV0dXJuIHRoaXMucGFyc2VDbGFzcyhub2RlLCB0cnVlKTtcbiAgICBjYXNlIF90b2tlbnR5cGUudHlwZXMuX2lmOlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VJZlN0YXRlbWVudChub2RlKTtcbiAgICBjYXNlIF90b2tlbnR5cGUudHlwZXMuX3JldHVybjpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlUmV0dXJuU3RhdGVtZW50KG5vZGUpO1xuICAgIGNhc2UgX3Rva2VudHlwZS50eXBlcy5fc3dpdGNoOlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VTd2l0Y2hTdGF0ZW1lbnQobm9kZSk7XG4gICAgY2FzZSBfdG9rZW50eXBlLnR5cGVzLl90aHJvdzpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlVGhyb3dTdGF0ZW1lbnQobm9kZSk7XG4gICAgY2FzZSBfdG9rZW50eXBlLnR5cGVzLl90cnk6XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZVRyeVN0YXRlbWVudChub2RlKTtcbiAgICBjYXNlIF90b2tlbnR5cGUudHlwZXMuX2xldDpjYXNlIF90b2tlbnR5cGUudHlwZXMuX2NvbnN0OlxuICAgICAgaWYgKCFkZWNsYXJhdGlvbikgdGhpcy51bmV4cGVjdGVkKCk7IC8vIE5PVEU6IGZhbGxzIHRocm91Z2ggdG8gX3ZhclxuICAgIGNhc2UgX3Rva2VudHlwZS50eXBlcy5fdmFyOlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VWYXJTdGF0ZW1lbnQobm9kZSwgc3RhcnR0eXBlKTtcbiAgICBjYXNlIF90b2tlbnR5cGUudHlwZXMuX3doaWxlOlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VXaGlsZVN0YXRlbWVudChub2RlKTtcbiAgICBjYXNlIF90b2tlbnR5cGUudHlwZXMuX3dpdGg6XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZVdpdGhTdGF0ZW1lbnQobm9kZSk7XG4gICAgY2FzZSBfdG9rZW50eXBlLnR5cGVzLmJyYWNlTDpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlQmxvY2soKTtcbiAgICBjYXNlIF90b2tlbnR5cGUudHlwZXMuc2VtaTpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlRW1wdHlTdGF0ZW1lbnQobm9kZSk7XG4gICAgY2FzZSBfdG9rZW50eXBlLnR5cGVzLl9leHBvcnQ6XG4gICAgY2FzZSBfdG9rZW50eXBlLnR5cGVzLl9pbXBvcnQ6XG4gICAgICBpZiAoIXRoaXMub3B0aW9ucy5hbGxvd0ltcG9ydEV4cG9ydEV2ZXJ5d2hlcmUpIHtcbiAgICAgICAgaWYgKCF0b3BMZXZlbCkgdGhpcy5yYWlzZSh0aGlzLnN0YXJ0LCBcIidpbXBvcnQnIGFuZCAnZXhwb3J0JyBtYXkgb25seSBhcHBlYXIgYXQgdGhlIHRvcCBsZXZlbFwiKTtcbiAgICAgICAgaWYgKCF0aGlzLmluTW9kdWxlKSB0aGlzLnJhaXNlKHRoaXMuc3RhcnQsIFwiJ2ltcG9ydCcgYW5kICdleHBvcnQnIG1heSBhcHBlYXIgb25seSB3aXRoICdzb3VyY2VUeXBlOiBtb2R1bGUnXCIpO1xuICAgICAgfVxuICAgICAgcmV0dXJuIHN0YXJ0dHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5faW1wb3J0ID8gdGhpcy5wYXJzZUltcG9ydChub2RlKSA6IHRoaXMucGFyc2VFeHBvcnQobm9kZSk7XG5cbiAgICAvLyBJZiB0aGUgc3RhdGVtZW50IGRvZXMgbm90IHN0YXJ0IHdpdGggYSBzdGF0ZW1lbnQga2V5d29yZCBvciBhXG4gICAgLy8gYnJhY2UsIGl0J3MgYW4gRXhwcmVzc2lvblN0YXRlbWVudCBvciBMYWJlbGVkU3RhdGVtZW50LiBXZVxuICAgIC8vIHNpbXBseSBzdGFydCBwYXJzaW5nIGFuIGV4cHJlc3Npb24sIGFuZCBhZnRlcndhcmRzLCBpZiB0aGVcbiAgICAvLyBuZXh0IHRva2VuIGlzIGEgY29sb24gYW5kIHRoZSBleHByZXNzaW9uIHdhcyBhIHNpbXBsZVxuICAgIC8vIElkZW50aWZpZXIgbm9kZSwgd2Ugc3dpdGNoIHRvIGludGVycHJldGluZyBpdCBhcyBhIGxhYmVsLlxuICAgIGRlZmF1bHQ6XG4gICAgICB2YXIgbWF5YmVOYW1lID0gdGhpcy52YWx1ZSxcbiAgICAgICAgICBleHByID0gdGhpcy5wYXJzZUV4cHJlc3Npb24oKTtcbiAgICAgIGlmIChzdGFydHR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMubmFtZSAmJiBleHByLnR5cGUgPT09IFwiSWRlbnRpZmllclwiICYmIHRoaXMuZWF0KF90b2tlbnR5cGUudHlwZXMuY29sb24pKSByZXR1cm4gdGhpcy5wYXJzZUxhYmVsZWRTdGF0ZW1lbnQobm9kZSwgbWF5YmVOYW1lLCBleHByKTtlbHNlIHJldHVybiB0aGlzLnBhcnNlRXhwcmVzc2lvblN0YXRlbWVudChub2RlLCBleHByKTtcbiAgfVxufTtcblxucHAucGFyc2VCcmVha0NvbnRpbnVlU3RhdGVtZW50ID0gZnVuY3Rpb24gKG5vZGUsIGtleXdvcmQpIHtcbiAgdmFyIGlzQnJlYWsgPSBrZXl3b3JkID09IFwiYnJlYWtcIjtcbiAgdGhpcy5uZXh0KCk7XG4gIGlmICh0aGlzLmVhdChfdG9rZW50eXBlLnR5cGVzLnNlbWkpIHx8IHRoaXMuaW5zZXJ0U2VtaWNvbG9uKCkpIG5vZGUubGFiZWwgPSBudWxsO2Vsc2UgaWYgKHRoaXMudHlwZSAhPT0gX3Rva2VudHlwZS50eXBlcy5uYW1lKSB0aGlzLnVuZXhwZWN0ZWQoKTtlbHNlIHtcbiAgICBub2RlLmxhYmVsID0gdGhpcy5wYXJzZUlkZW50KCk7XG4gICAgdGhpcy5zZW1pY29sb24oKTtcbiAgfVxuXG4gIC8vIFZlcmlmeSB0aGF0IHRoZXJlIGlzIGFuIGFjdHVhbCBkZXN0aW5hdGlvbiB0byBicmVhayBvclxuICAvLyBjb250aW51ZSB0by5cbiAgZm9yICh2YXIgaSA9IDA7IGkgPCB0aGlzLmxhYmVscy5sZW5ndGg7ICsraSkge1xuICAgIHZhciBsYWIgPSB0aGlzLmxhYmVsc1tpXTtcbiAgICBpZiAobm9kZS5sYWJlbCA9PSBudWxsIHx8IGxhYi5uYW1lID09PSBub2RlLmxhYmVsLm5hbWUpIHtcbiAgICAgIGlmIChsYWIua2luZCAhPSBudWxsICYmIChpc0JyZWFrIHx8IGxhYi5raW5kID09PSBcImxvb3BcIikpIGJyZWFrO1xuICAgICAgaWYgKG5vZGUubGFiZWwgJiYgaXNCcmVhaykgYnJlYWs7XG4gICAgfVxuICB9XG4gIGlmIChpID09PSB0aGlzLmxhYmVscy5sZW5ndGgpIHRoaXMucmFpc2Uobm9kZS5zdGFydCwgXCJVbnN5bnRhY3RpYyBcIiArIGtleXdvcmQpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIGlzQnJlYWsgPyBcIkJyZWFrU3RhdGVtZW50XCIgOiBcIkNvbnRpbnVlU3RhdGVtZW50XCIpO1xufTtcblxucHAucGFyc2VEZWJ1Z2dlclN0YXRlbWVudCA9IGZ1bmN0aW9uIChub2RlKSB7XG4gIHRoaXMubmV4dCgpO1xuICB0aGlzLnNlbWljb2xvbigpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiRGVidWdnZXJTdGF0ZW1lbnRcIik7XG59O1xuXG5wcC5wYXJzZURvU3RhdGVtZW50ID0gZnVuY3Rpb24gKG5vZGUpIHtcbiAgdGhpcy5uZXh0KCk7XG4gIHRoaXMubGFiZWxzLnB1c2gobG9vcExhYmVsKTtcbiAgbm9kZS5ib2R5ID0gdGhpcy5wYXJzZVN0YXRlbWVudChmYWxzZSk7XG4gIHRoaXMubGFiZWxzLnBvcCgpO1xuICB0aGlzLmV4cGVjdChfdG9rZW50eXBlLnR5cGVzLl93aGlsZSk7XG4gIG5vZGUudGVzdCA9IHRoaXMucGFyc2VQYXJlbkV4cHJlc3Npb24oKTtcbiAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KSB0aGlzLmVhdChfdG9rZW50eXBlLnR5cGVzLnNlbWkpO2Vsc2UgdGhpcy5zZW1pY29sb24oKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkRvV2hpbGVTdGF0ZW1lbnRcIik7XG59O1xuXG4vLyBEaXNhbWJpZ3VhdGluZyBiZXR3ZWVuIGEgYGZvcmAgYW5kIGEgYGZvcmAvYGluYCBvciBgZm9yYC9gb2ZgXG4vLyBsb29wIGlzIG5vbi10cml2aWFsLiBCYXNpY2FsbHksIHdlIGhhdmUgdG8gcGFyc2UgdGhlIGluaXQgYHZhcmBcbi8vIHN0YXRlbWVudCBvciBleHByZXNzaW9uLCBkaXNhbGxvd2luZyB0aGUgYGluYCBvcGVyYXRvciAoc2VlXG4vLyB0aGUgc2Vjb25kIHBhcmFtZXRlciB0byBgcGFyc2VFeHByZXNzaW9uYCksIGFuZCB0aGVuIGNoZWNrXG4vLyB3aGV0aGVyIHRoZSBuZXh0IHRva2VuIGlzIGBpbmAgb3IgYG9mYC4gV2hlbiB0aGVyZSBpcyBubyBpbml0XG4vLyBwYXJ0IChzZW1pY29sb24gaW1tZWRpYXRlbHkgYWZ0ZXIgdGhlIG9wZW5pbmcgcGFyZW50aGVzaXMpLCBpdFxuLy8gaXMgYSByZWd1bGFyIGBmb3JgIGxvb3AuXG5cbnBwLnBhcnNlRm9yU3RhdGVtZW50ID0gZnVuY3Rpb24gKG5vZGUpIHtcbiAgdGhpcy5uZXh0KCk7XG4gIHRoaXMubGFiZWxzLnB1c2gobG9vcExhYmVsKTtcbiAgdGhpcy5leHBlY3QoX3Rva2VudHlwZS50eXBlcy5wYXJlbkwpO1xuICBpZiAodGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLnNlbWkpIHJldHVybiB0aGlzLnBhcnNlRm9yKG5vZGUsIG51bGwpO1xuICBpZiAodGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLl92YXIgfHwgdGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLl9sZXQgfHwgdGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLl9jb25zdCkge1xuICAgIHZhciBfaW5pdCA9IHRoaXMuc3RhcnROb2RlKCksXG4gICAgICAgIHZhcktpbmQgPSB0aGlzLnR5cGU7XG4gICAgdGhpcy5uZXh0KCk7XG4gICAgdGhpcy5wYXJzZVZhcihfaW5pdCwgdHJ1ZSwgdmFyS2luZCk7XG4gICAgdGhpcy5maW5pc2hOb2RlKF9pbml0LCBcIlZhcmlhYmxlRGVjbGFyYXRpb25cIik7XG4gICAgaWYgKCh0aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuX2luIHx8IHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2ICYmIHRoaXMuaXNDb250ZXh0dWFsKFwib2ZcIikpICYmIF9pbml0LmRlY2xhcmF0aW9ucy5sZW5ndGggPT09IDEgJiYgISh2YXJLaW5kICE9PSBfdG9rZW50eXBlLnR5cGVzLl92YXIgJiYgX2luaXQuZGVjbGFyYXRpb25zWzBdLmluaXQpKSByZXR1cm4gdGhpcy5wYXJzZUZvckluKG5vZGUsIF9pbml0KTtcbiAgICByZXR1cm4gdGhpcy5wYXJzZUZvcihub2RlLCBfaW5pdCk7XG4gIH1cbiAgdmFyIHJlZlNob3J0aGFuZERlZmF1bHRQb3MgPSB7IHN0YXJ0OiAwIH07XG4gIHZhciBpbml0ID0gdGhpcy5wYXJzZUV4cHJlc3Npb24odHJ1ZSwgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcyk7XG4gIGlmICh0aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuX2luIHx8IHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2ICYmIHRoaXMuaXNDb250ZXh0dWFsKFwib2ZcIikpIHtcbiAgICB0aGlzLnRvQXNzaWduYWJsZShpbml0KTtcbiAgICB0aGlzLmNoZWNrTFZhbChpbml0KTtcbiAgICByZXR1cm4gdGhpcy5wYXJzZUZvckluKG5vZGUsIGluaXQpO1xuICB9IGVsc2UgaWYgKHJlZlNob3J0aGFuZERlZmF1bHRQb3Muc3RhcnQpIHtcbiAgICB0aGlzLnVuZXhwZWN0ZWQocmVmU2hvcnRoYW5kRGVmYXVsdFBvcy5zdGFydCk7XG4gIH1cbiAgcmV0dXJuIHRoaXMucGFyc2VGb3Iobm9kZSwgaW5pdCk7XG59O1xuXG5wcC5wYXJzZUZ1bmN0aW9uU3RhdGVtZW50ID0gZnVuY3Rpb24gKG5vZGUpIHtcbiAgdGhpcy5uZXh0KCk7XG4gIHJldHVybiB0aGlzLnBhcnNlRnVuY3Rpb24obm9kZSwgdHJ1ZSk7XG59O1xuXG5wcC5wYXJzZUlmU3RhdGVtZW50ID0gZnVuY3Rpb24gKG5vZGUpIHtcbiAgdGhpcy5uZXh0KCk7XG4gIG5vZGUudGVzdCA9IHRoaXMucGFyc2VQYXJlbkV4cHJlc3Npb24oKTtcbiAgbm9kZS5jb25zZXF1ZW50ID0gdGhpcy5wYXJzZVN0YXRlbWVudChmYWxzZSk7XG4gIG5vZGUuYWx0ZXJuYXRlID0gdGhpcy5lYXQoX3Rva2VudHlwZS50eXBlcy5fZWxzZSkgPyB0aGlzLnBhcnNlU3RhdGVtZW50KGZhbHNlKSA6IG51bGw7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJJZlN0YXRlbWVudFwiKTtcbn07XG5cbnBwLnBhcnNlUmV0dXJuU3RhdGVtZW50ID0gZnVuY3Rpb24gKG5vZGUpIHtcbiAgaWYgKCF0aGlzLmluRnVuY3Rpb24gJiYgIXRoaXMub3B0aW9ucy5hbGxvd1JldHVybk91dHNpZGVGdW5jdGlvbikgdGhpcy5yYWlzZSh0aGlzLnN0YXJ0LCBcIidyZXR1cm4nIG91dHNpZGUgb2YgZnVuY3Rpb25cIik7XG4gIHRoaXMubmV4dCgpO1xuXG4gIC8vIEluIGByZXR1cm5gIChhbmQgYGJyZWFrYC9gY29udGludWVgKSwgdGhlIGtleXdvcmRzIHdpdGhcbiAgLy8gb3B0aW9uYWwgYXJndW1lbnRzLCB3ZSBlYWdlcmx5IGxvb2sgZm9yIGEgc2VtaWNvbG9uIG9yIHRoZVxuICAvLyBwb3NzaWJpbGl0eSB0byBpbnNlcnQgb25lLlxuXG4gIGlmICh0aGlzLmVhdChfdG9rZW50eXBlLnR5cGVzLnNlbWkpIHx8IHRoaXMuaW5zZXJ0U2VtaWNvbG9uKCkpIG5vZGUuYXJndW1lbnQgPSBudWxsO2Vsc2Uge1xuICAgIG5vZGUuYXJndW1lbnQgPSB0aGlzLnBhcnNlRXhwcmVzc2lvbigpO3RoaXMuc2VtaWNvbG9uKCk7XG4gIH1cbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIlJldHVyblN0YXRlbWVudFwiKTtcbn07XG5cbnBwLnBhcnNlU3dpdGNoU3RhdGVtZW50ID0gZnVuY3Rpb24gKG5vZGUpIHtcbiAgdGhpcy5uZXh0KCk7XG4gIG5vZGUuZGlzY3JpbWluYW50ID0gdGhpcy5wYXJzZVBhcmVuRXhwcmVzc2lvbigpO1xuICBub2RlLmNhc2VzID0gW107XG4gIHRoaXMuZXhwZWN0KF90b2tlbnR5cGUudHlwZXMuYnJhY2VMKTtcbiAgdGhpcy5sYWJlbHMucHVzaChzd2l0Y2hMYWJlbCk7XG5cbiAgLy8gU3RhdGVtZW50cyB1bmRlciBtdXN0IGJlIGdyb3VwZWQgKGJ5IGxhYmVsKSBpbiBTd2l0Y2hDYXNlXG4gIC8vIG5vZGVzLiBgY3VyYCBpcyB1c2VkIHRvIGtlZXAgdGhlIG5vZGUgdGhhdCB3ZSBhcmUgY3VycmVudGx5XG4gIC8vIGFkZGluZyBzdGF0ZW1lbnRzIHRvLlxuXG4gIGZvciAodmFyIGN1ciwgc2F3RGVmYXVsdCA9IGZhbHNlOyB0aGlzLnR5cGUgIT0gX3Rva2VudHlwZS50eXBlcy5icmFjZVI7KSB7XG4gICAgaWYgKHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5fY2FzZSB8fCB0aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuX2RlZmF1bHQpIHtcbiAgICAgIHZhciBpc0Nhc2UgPSB0aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuX2Nhc2U7XG4gICAgICBpZiAoY3VyKSB0aGlzLmZpbmlzaE5vZGUoY3VyLCBcIlN3aXRjaENhc2VcIik7XG4gICAgICBub2RlLmNhc2VzLnB1c2goY3VyID0gdGhpcy5zdGFydE5vZGUoKSk7XG4gICAgICBjdXIuY29uc2VxdWVudCA9IFtdO1xuICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICBpZiAoaXNDYXNlKSB7XG4gICAgICAgIGN1ci50ZXN0ID0gdGhpcy5wYXJzZUV4cHJlc3Npb24oKTtcbiAgICAgIH0gZWxzZSB7XG4gICAgICAgIGlmIChzYXdEZWZhdWx0KSB0aGlzLnJhaXNlKHRoaXMubGFzdFRva1N0YXJ0LCBcIk11bHRpcGxlIGRlZmF1bHQgY2xhdXNlc1wiKTtcbiAgICAgICAgc2F3RGVmYXVsdCA9IHRydWU7XG4gICAgICAgIGN1ci50ZXN0ID0gbnVsbDtcbiAgICAgIH1cbiAgICAgIHRoaXMuZXhwZWN0KF90b2tlbnR5cGUudHlwZXMuY29sb24pO1xuICAgIH0gZWxzZSB7XG4gICAgICBpZiAoIWN1cikgdGhpcy51bmV4cGVjdGVkKCk7XG4gICAgICBjdXIuY29uc2VxdWVudC5wdXNoKHRoaXMucGFyc2VTdGF0ZW1lbnQodHJ1ZSkpO1xuICAgIH1cbiAgfVxuICBpZiAoY3VyKSB0aGlzLmZpbmlzaE5vZGUoY3VyLCBcIlN3aXRjaENhc2VcIik7XG4gIHRoaXMubmV4dCgpOyAvLyBDbG9zaW5nIGJyYWNlXG4gIHRoaXMubGFiZWxzLnBvcCgpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiU3dpdGNoU3RhdGVtZW50XCIpO1xufTtcblxucHAucGFyc2VUaHJvd1N0YXRlbWVudCA9IGZ1bmN0aW9uIChub2RlKSB7XG4gIHRoaXMubmV4dCgpO1xuICBpZiAoX3doaXRlc3BhY2UubGluZUJyZWFrLnRlc3QodGhpcy5pbnB1dC5zbGljZSh0aGlzLmxhc3RUb2tFbmQsIHRoaXMuc3RhcnQpKSkgdGhpcy5yYWlzZSh0aGlzLmxhc3RUb2tFbmQsIFwiSWxsZWdhbCBuZXdsaW5lIGFmdGVyIHRocm93XCIpO1xuICBub2RlLmFyZ3VtZW50ID0gdGhpcy5wYXJzZUV4cHJlc3Npb24oKTtcbiAgdGhpcy5zZW1pY29sb24oKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIlRocm93U3RhdGVtZW50XCIpO1xufTtcblxuLy8gUmV1c2VkIGVtcHR5IGFycmF5IGFkZGVkIGZvciBub2RlIGZpZWxkcyB0aGF0IGFyZSBhbHdheXMgZW1wdHkuXG5cbnZhciBlbXB0eSA9IFtdO1xuXG5wcC5wYXJzZVRyeVN0YXRlbWVudCA9IGZ1bmN0aW9uIChub2RlKSB7XG4gIHRoaXMubmV4dCgpO1xuICBub2RlLmJsb2NrID0gdGhpcy5wYXJzZUJsb2NrKCk7XG4gIG5vZGUuaGFuZGxlciA9IG51bGw7XG4gIGlmICh0aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuX2NhdGNoKSB7XG4gICAgdmFyIGNsYXVzZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gICAgdGhpcy5uZXh0KCk7XG4gICAgdGhpcy5leHBlY3QoX3Rva2VudHlwZS50eXBlcy5wYXJlbkwpO1xuICAgIGNsYXVzZS5wYXJhbSA9IHRoaXMucGFyc2VCaW5kaW5nQXRvbSgpO1xuICAgIHRoaXMuY2hlY2tMVmFsKGNsYXVzZS5wYXJhbSwgdHJ1ZSk7XG4gICAgdGhpcy5leHBlY3QoX3Rva2VudHlwZS50eXBlcy5wYXJlblIpO1xuICAgIGNsYXVzZS5ndWFyZCA9IG51bGw7XG4gICAgY2xhdXNlLmJvZHkgPSB0aGlzLnBhcnNlQmxvY2soKTtcbiAgICBub2RlLmhhbmRsZXIgPSB0aGlzLmZpbmlzaE5vZGUoY2xhdXNlLCBcIkNhdGNoQ2xhdXNlXCIpO1xuICB9XG4gIG5vZGUuZ3VhcmRlZEhhbmRsZXJzID0gZW1wdHk7XG4gIG5vZGUuZmluYWxpemVyID0gdGhpcy5lYXQoX3Rva2VudHlwZS50eXBlcy5fZmluYWxseSkgPyB0aGlzLnBhcnNlQmxvY2soKSA6IG51bGw7XG4gIGlmICghbm9kZS5oYW5kbGVyICYmICFub2RlLmZpbmFsaXplcikgdGhpcy5yYWlzZShub2RlLnN0YXJ0LCBcIk1pc3NpbmcgY2F0Y2ggb3IgZmluYWxseSBjbGF1c2VcIik7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJUcnlTdGF0ZW1lbnRcIik7XG59O1xuXG5wcC5wYXJzZVZhclN0YXRlbWVudCA9IGZ1bmN0aW9uIChub2RlLCBraW5kKSB7XG4gIHRoaXMubmV4dCgpO1xuICB0aGlzLnBhcnNlVmFyKG5vZGUsIGZhbHNlLCBraW5kKTtcbiAgdGhpcy5zZW1pY29sb24oKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIlZhcmlhYmxlRGVjbGFyYXRpb25cIik7XG59O1xuXG5wcC5wYXJzZVdoaWxlU3RhdGVtZW50ID0gZnVuY3Rpb24gKG5vZGUpIHtcbiAgdGhpcy5uZXh0KCk7XG4gIG5vZGUudGVzdCA9IHRoaXMucGFyc2VQYXJlbkV4cHJlc3Npb24oKTtcbiAgdGhpcy5sYWJlbHMucHVzaChsb29wTGFiZWwpO1xuICBub2RlLmJvZHkgPSB0aGlzLnBhcnNlU3RhdGVtZW50KGZhbHNlKTtcbiAgdGhpcy5sYWJlbHMucG9wKCk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJXaGlsZVN0YXRlbWVudFwiKTtcbn07XG5cbnBwLnBhcnNlV2l0aFN0YXRlbWVudCA9IGZ1bmN0aW9uIChub2RlKSB7XG4gIGlmICh0aGlzLnN0cmljdCkgdGhpcy5yYWlzZSh0aGlzLnN0YXJ0LCBcIid3aXRoJyBpbiBzdHJpY3QgbW9kZVwiKTtcbiAgdGhpcy5uZXh0KCk7XG4gIG5vZGUub2JqZWN0ID0gdGhpcy5wYXJzZVBhcmVuRXhwcmVzc2lvbigpO1xuICBub2RlLmJvZHkgPSB0aGlzLnBhcnNlU3RhdGVtZW50KGZhbHNlKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIldpdGhTdGF0ZW1lbnRcIik7XG59O1xuXG5wcC5wYXJzZUVtcHR5U3RhdGVtZW50ID0gZnVuY3Rpb24gKG5vZGUpIHtcbiAgdGhpcy5uZXh0KCk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJFbXB0eVN0YXRlbWVudFwiKTtcbn07XG5cbnBwLnBhcnNlTGFiZWxlZFN0YXRlbWVudCA9IGZ1bmN0aW9uIChub2RlLCBtYXliZU5hbWUsIGV4cHIpIHtcbiAgZm9yICh2YXIgaSA9IDA7IGkgPCB0aGlzLmxhYmVscy5sZW5ndGg7ICsraSkge1xuICAgIGlmICh0aGlzLmxhYmVsc1tpXS5uYW1lID09PSBtYXliZU5hbWUpIHRoaXMucmFpc2UoZXhwci5zdGFydCwgXCJMYWJlbCAnXCIgKyBtYXliZU5hbWUgKyBcIicgaXMgYWxyZWFkeSBkZWNsYXJlZFwiKTtcbiAgfXZhciBraW5kID0gdGhpcy50eXBlLmlzTG9vcCA/IFwibG9vcFwiIDogdGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLl9zd2l0Y2ggPyBcInN3aXRjaFwiIDogbnVsbDtcbiAgZm9yICh2YXIgaSA9IHRoaXMubGFiZWxzLmxlbmd0aCAtIDE7IGkgPj0gMDsgaS0tKSB7XG4gICAgdmFyIGxhYmVsID0gdGhpcy5sYWJlbHNbaV07XG4gICAgaWYgKGxhYmVsLnN0YXRlbWVudFN0YXJ0ID09IG5vZGUuc3RhcnQpIHtcbiAgICAgIGxhYmVsLnN0YXRlbWVudFN0YXJ0ID0gdGhpcy5zdGFydDtcbiAgICAgIGxhYmVsLmtpbmQgPSBraW5kO1xuICAgIH0gZWxzZSBicmVhaztcbiAgfVxuICB0aGlzLmxhYmVscy5wdXNoKHsgbmFtZTogbWF5YmVOYW1lLCBraW5kOiBraW5kLCBzdGF0ZW1lbnRTdGFydDogdGhpcy5zdGFydCB9KTtcbiAgbm9kZS5ib2R5ID0gdGhpcy5wYXJzZVN0YXRlbWVudCh0cnVlKTtcbiAgdGhpcy5sYWJlbHMucG9wKCk7XG4gIG5vZGUubGFiZWwgPSBleHByO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiTGFiZWxlZFN0YXRlbWVudFwiKTtcbn07XG5cbnBwLnBhcnNlRXhwcmVzc2lvblN0YXRlbWVudCA9IGZ1bmN0aW9uIChub2RlLCBleHByKSB7XG4gIG5vZGUuZXhwcmVzc2lvbiA9IGV4cHI7XG4gIHRoaXMuc2VtaWNvbG9uKCk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJFeHByZXNzaW9uU3RhdGVtZW50XCIpO1xufTtcblxuLy8gUGFyc2UgYSBzZW1pY29sb24tZW5jbG9zZWQgYmxvY2sgb2Ygc3RhdGVtZW50cywgaGFuZGxpbmcgYFwidXNlXG4vLyBzdHJpY3RcImAgZGVjbGFyYXRpb25zIHdoZW4gYGFsbG93U3RyaWN0YCBpcyB0cnVlICh1c2VkIGZvclxuLy8gZnVuY3Rpb24gYm9kaWVzKS5cblxucHAucGFyc2VCbG9jayA9IGZ1bmN0aW9uIChhbGxvd1N0cmljdCkge1xuICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCksXG4gICAgICBmaXJzdCA9IHRydWUsXG4gICAgICBvbGRTdHJpY3QgPSB1bmRlZmluZWQ7XG4gIG5vZGUuYm9keSA9IFtdO1xuICB0aGlzLmV4cGVjdChfdG9rZW50eXBlLnR5cGVzLmJyYWNlTCk7XG4gIHdoaWxlICghdGhpcy5lYXQoX3Rva2VudHlwZS50eXBlcy5icmFjZVIpKSB7XG4gICAgdmFyIHN0bXQgPSB0aGlzLnBhcnNlU3RhdGVtZW50KHRydWUpO1xuICAgIG5vZGUuYm9keS5wdXNoKHN0bXQpO1xuICAgIGlmIChmaXJzdCAmJiBhbGxvd1N0cmljdCAmJiB0aGlzLmlzVXNlU3RyaWN0KHN0bXQpKSB7XG4gICAgICBvbGRTdHJpY3QgPSB0aGlzLnN0cmljdDtcbiAgICAgIHRoaXMuc2V0U3RyaWN0KHRoaXMuc3RyaWN0ID0gdHJ1ZSk7XG4gICAgfVxuICAgIGZpcnN0ID0gZmFsc2U7XG4gIH1cbiAgaWYgKG9sZFN0cmljdCA9PT0gZmFsc2UpIHRoaXMuc2V0U3RyaWN0KGZhbHNlKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkJsb2NrU3RhdGVtZW50XCIpO1xufTtcblxuLy8gUGFyc2UgYSByZWd1bGFyIGBmb3JgIGxvb3AuIFRoZSBkaXNhbWJpZ3VhdGlvbiBjb2RlIGluXG4vLyBgcGFyc2VTdGF0ZW1lbnRgIHdpbGwgYWxyZWFkeSBoYXZlIHBhcnNlZCB0aGUgaW5pdCBzdGF0ZW1lbnQgb3Jcbi8vIGV4cHJlc3Npb24uXG5cbnBwLnBhcnNlRm9yID0gZnVuY3Rpb24gKG5vZGUsIGluaXQpIHtcbiAgbm9kZS5pbml0ID0gaW5pdDtcbiAgdGhpcy5leHBlY3QoX3Rva2VudHlwZS50eXBlcy5zZW1pKTtcbiAgbm9kZS50ZXN0ID0gdGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLnNlbWkgPyBudWxsIDogdGhpcy5wYXJzZUV4cHJlc3Npb24oKTtcbiAgdGhpcy5leHBlY3QoX3Rva2VudHlwZS50eXBlcy5zZW1pKTtcbiAgbm9kZS51cGRhdGUgPSB0aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMucGFyZW5SID8gbnVsbCA6IHRoaXMucGFyc2VFeHByZXNzaW9uKCk7XG4gIHRoaXMuZXhwZWN0KF90b2tlbnR5cGUudHlwZXMucGFyZW5SKTtcbiAgbm9kZS5ib2R5ID0gdGhpcy5wYXJzZVN0YXRlbWVudChmYWxzZSk7XG4gIHRoaXMubGFiZWxzLnBvcCgpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiRm9yU3RhdGVtZW50XCIpO1xufTtcblxuLy8gUGFyc2UgYSBgZm9yYC9gaW5gIGFuZCBgZm9yYC9gb2ZgIGxvb3AsIHdoaWNoIGFyZSBhbG1vc3Rcbi8vIHNhbWUgZnJvbSBwYXJzZXIncyBwZXJzcGVjdGl2ZS5cblxucHAucGFyc2VGb3JJbiA9IGZ1bmN0aW9uIChub2RlLCBpbml0KSB7XG4gIHZhciB0eXBlID0gdGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLl9pbiA/IFwiRm9ySW5TdGF0ZW1lbnRcIiA6IFwiRm9yT2ZTdGF0ZW1lbnRcIjtcbiAgdGhpcy5uZXh0KCk7XG4gIG5vZGUubGVmdCA9IGluaXQ7XG4gIG5vZGUucmlnaHQgPSB0aGlzLnBhcnNlRXhwcmVzc2lvbigpO1xuICB0aGlzLmV4cGVjdChfdG9rZW50eXBlLnR5cGVzLnBhcmVuUik7XG4gIG5vZGUuYm9keSA9IHRoaXMucGFyc2VTdGF0ZW1lbnQoZmFsc2UpO1xuICB0aGlzLmxhYmVscy5wb3AoKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCB0eXBlKTtcbn07XG5cbi8vIFBhcnNlIGEgbGlzdCBvZiB2YXJpYWJsZSBkZWNsYXJhdGlvbnMuXG5cbnBwLnBhcnNlVmFyID0gZnVuY3Rpb24gKG5vZGUsIGlzRm9yLCBraW5kKSB7XG4gIG5vZGUuZGVjbGFyYXRpb25zID0gW107XG4gIG5vZGUua2luZCA9IGtpbmQua2V5d29yZDtcbiAgZm9yICg7Oykge1xuICAgIHZhciBkZWNsID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgICB0aGlzLnBhcnNlVmFySWQoZGVjbCk7XG4gICAgaWYgKHRoaXMuZWF0KF90b2tlbnR5cGUudHlwZXMuZXEpKSB7XG4gICAgICBkZWNsLmluaXQgPSB0aGlzLnBhcnNlTWF5YmVBc3NpZ24oaXNGb3IpO1xuICAgIH0gZWxzZSBpZiAoa2luZCA9PT0gX3Rva2VudHlwZS50eXBlcy5fY29uc3QgJiYgISh0aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuX2luIHx8IHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2ICYmIHRoaXMuaXNDb250ZXh0dWFsKFwib2ZcIikpKSB7XG4gICAgICB0aGlzLnVuZXhwZWN0ZWQoKTtcbiAgICB9IGVsc2UgaWYgKGRlY2wuaWQudHlwZSAhPSBcIklkZW50aWZpZXJcIiAmJiAhKGlzRm9yICYmICh0aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuX2luIHx8IHRoaXMuaXNDb250ZXh0dWFsKFwib2ZcIikpKSkge1xuICAgICAgdGhpcy5yYWlzZSh0aGlzLmxhc3RUb2tFbmQsIFwiQ29tcGxleCBiaW5kaW5nIHBhdHRlcm5zIHJlcXVpcmUgYW4gaW5pdGlhbGl6YXRpb24gdmFsdWVcIik7XG4gICAgfSBlbHNlIHtcbiAgICAgIGRlY2wuaW5pdCA9IG51bGw7XG4gICAgfVxuICAgIG5vZGUuZGVjbGFyYXRpb25zLnB1c2godGhpcy5maW5pc2hOb2RlKGRlY2wsIFwiVmFyaWFibGVEZWNsYXJhdG9yXCIpKTtcbiAgICBpZiAoIXRoaXMuZWF0KF90b2tlbnR5cGUudHlwZXMuY29tbWEpKSBicmVhaztcbiAgfVxuICByZXR1cm4gbm9kZTtcbn07XG5cbnBwLnBhcnNlVmFySWQgPSBmdW5jdGlvbiAoZGVjbCkge1xuICBkZWNsLmlkID0gdGhpcy5wYXJzZUJpbmRpbmdBdG9tKCk7XG4gIHRoaXMuY2hlY2tMVmFsKGRlY2wuaWQsIHRydWUpO1xufTtcblxuLy8gUGFyc2UgYSBmdW5jdGlvbiBkZWNsYXJhdGlvbiBvciBsaXRlcmFsIChkZXBlbmRpbmcgb24gdGhlXG4vLyBgaXNTdGF0ZW1lbnRgIHBhcmFtZXRlcikuXG5cbnBwLnBhcnNlRnVuY3Rpb24gPSBmdW5jdGlvbiAobm9kZSwgaXNTdGF0ZW1lbnQsIGFsbG93RXhwcmVzc2lvbkJvZHkpIHtcbiAgdGhpcy5pbml0RnVuY3Rpb24obm9kZSk7XG4gIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNikgbm9kZS5nZW5lcmF0b3IgPSB0aGlzLmVhdChfdG9rZW50eXBlLnR5cGVzLnN0YXIpO1xuICBpZiAoaXNTdGF0ZW1lbnQgfHwgdGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLm5hbWUpIG5vZGUuaWQgPSB0aGlzLnBhcnNlSWRlbnQoKTtcbiAgdGhpcy5wYXJzZUZ1bmN0aW9uUGFyYW1zKG5vZGUpO1xuICB0aGlzLnBhcnNlRnVuY3Rpb25Cb2R5KG5vZGUsIGFsbG93RXhwcmVzc2lvbkJvZHkpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIGlzU3RhdGVtZW50ID8gXCJGdW5jdGlvbkRlY2xhcmF0aW9uXCIgOiBcIkZ1bmN0aW9uRXhwcmVzc2lvblwiKTtcbn07XG5cbnBwLnBhcnNlRnVuY3Rpb25QYXJhbXMgPSBmdW5jdGlvbiAobm9kZSkge1xuICB0aGlzLmV4cGVjdChfdG9rZW50eXBlLnR5cGVzLnBhcmVuTCk7XG4gIG5vZGUucGFyYW1zID0gdGhpcy5wYXJzZUJpbmRpbmdMaXN0KF90b2tlbnR5cGUudHlwZXMucGFyZW5SLCBmYWxzZSwgZmFsc2UpO1xufTtcblxuLy8gUGFyc2UgYSBjbGFzcyBkZWNsYXJhdGlvbiBvciBsaXRlcmFsIChkZXBlbmRpbmcgb24gdGhlXG4vLyBgaXNTdGF0ZW1lbnRgIHBhcmFtZXRlcikuXG5cbnBwLnBhcnNlQ2xhc3MgPSBmdW5jdGlvbiAobm9kZSwgaXNTdGF0ZW1lbnQpIHtcbiAgdGhpcy5uZXh0KCk7XG4gIHRoaXMucGFyc2VDbGFzc0lkKG5vZGUsIGlzU3RhdGVtZW50KTtcbiAgdGhpcy5wYXJzZUNsYXNzU3VwZXIobm9kZSk7XG4gIHZhciBjbGFzc0JvZHkgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICB2YXIgaGFkQ29uc3RydWN0b3IgPSBmYWxzZTtcbiAgY2xhc3NCb2R5LmJvZHkgPSBbXTtcbiAgdGhpcy5leHBlY3QoX3Rva2VudHlwZS50eXBlcy5icmFjZUwpO1xuICB3aGlsZSAoIXRoaXMuZWF0KF90b2tlbnR5cGUudHlwZXMuYnJhY2VSKSkge1xuICAgIGlmICh0aGlzLmVhdChfdG9rZW50eXBlLnR5cGVzLnNlbWkpKSBjb250aW51ZTtcbiAgICB2YXIgbWV0aG9kID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgICB2YXIgaXNHZW5lcmF0b3IgPSB0aGlzLmVhdChfdG9rZW50eXBlLnR5cGVzLnN0YXIpO1xuICAgIHZhciBpc01heWJlU3RhdGljID0gdGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLm5hbWUgJiYgdGhpcy52YWx1ZSA9PT0gXCJzdGF0aWNcIjtcbiAgICB0aGlzLnBhcnNlUHJvcGVydHlOYW1lKG1ldGhvZCk7XG4gICAgbWV0aG9kW1wic3RhdGljXCJdID0gaXNNYXliZVN0YXRpYyAmJiB0aGlzLnR5cGUgIT09IF90b2tlbnR5cGUudHlwZXMucGFyZW5MO1xuICAgIGlmIChtZXRob2RbXCJzdGF0aWNcIl0pIHtcbiAgICAgIGlmIChpc0dlbmVyYXRvcikgdGhpcy51bmV4cGVjdGVkKCk7XG4gICAgICBpc0dlbmVyYXRvciA9IHRoaXMuZWF0KF90b2tlbnR5cGUudHlwZXMuc3Rhcik7XG4gICAgICB0aGlzLnBhcnNlUHJvcGVydHlOYW1lKG1ldGhvZCk7XG4gICAgfVxuICAgIG1ldGhvZC5raW5kID0gXCJtZXRob2RcIjtcbiAgICB2YXIgaXNHZXRTZXQgPSBmYWxzZTtcbiAgICBpZiAoIW1ldGhvZC5jb21wdXRlZCkge1xuICAgICAgdmFyIGtleSA9IG1ldGhvZC5rZXk7XG5cbiAgICAgIGlmICghaXNHZW5lcmF0b3IgJiYga2V5LnR5cGUgPT09IFwiSWRlbnRpZmllclwiICYmIHRoaXMudHlwZSAhPT0gX3Rva2VudHlwZS50eXBlcy5wYXJlbkwgJiYgKGtleS5uYW1lID09PSBcImdldFwiIHx8IGtleS5uYW1lID09PSBcInNldFwiKSkge1xuICAgICAgICBpc0dldFNldCA9IHRydWU7XG4gICAgICAgIG1ldGhvZC5raW5kID0ga2V5Lm5hbWU7XG4gICAgICAgIGtleSA9IHRoaXMucGFyc2VQcm9wZXJ0eU5hbWUobWV0aG9kKTtcbiAgICAgIH1cbiAgICAgIGlmICghbWV0aG9kW1wic3RhdGljXCJdICYmIChrZXkudHlwZSA9PT0gXCJJZGVudGlmaWVyXCIgJiYga2V5Lm5hbWUgPT09IFwiY29uc3RydWN0b3JcIiB8fCBrZXkudHlwZSA9PT0gXCJMaXRlcmFsXCIgJiYga2V5LnZhbHVlID09PSBcImNvbnN0cnVjdG9yXCIpKSB7XG4gICAgICAgIGlmIChoYWRDb25zdHJ1Y3RvcikgdGhpcy5yYWlzZShrZXkuc3RhcnQsIFwiRHVwbGljYXRlIGNvbnN0cnVjdG9yIGluIHRoZSBzYW1lIGNsYXNzXCIpO1xuICAgICAgICBpZiAoaXNHZXRTZXQpIHRoaXMucmFpc2Uoa2V5LnN0YXJ0LCBcIkNvbnN0cnVjdG9yIGNhbid0IGhhdmUgZ2V0L3NldCBtb2RpZmllclwiKTtcbiAgICAgICAgaWYgKGlzR2VuZXJhdG9yKSB0aGlzLnJhaXNlKGtleS5zdGFydCwgXCJDb25zdHJ1Y3RvciBjYW4ndCBiZSBhIGdlbmVyYXRvclwiKTtcbiAgICAgICAgbWV0aG9kLmtpbmQgPSBcImNvbnN0cnVjdG9yXCI7XG4gICAgICAgIGhhZENvbnN0cnVjdG9yID0gdHJ1ZTtcbiAgICAgIH1cbiAgICB9XG4gICAgdGhpcy5wYXJzZUNsYXNzTWV0aG9kKGNsYXNzQm9keSwgbWV0aG9kLCBpc0dlbmVyYXRvcik7XG4gICAgaWYgKGlzR2V0U2V0KSB7XG4gICAgICB2YXIgcGFyYW1Db3VudCA9IG1ldGhvZC5raW5kID09PSBcImdldFwiID8gMCA6IDE7XG4gICAgICBpZiAobWV0aG9kLnZhbHVlLnBhcmFtcy5sZW5ndGggIT09IHBhcmFtQ291bnQpIHtcbiAgICAgICAgdmFyIHN0YXJ0ID0gbWV0aG9kLnZhbHVlLnN0YXJ0O1xuICAgICAgICBpZiAobWV0aG9kLmtpbmQgPT09IFwiZ2V0XCIpIHRoaXMucmFpc2Uoc3RhcnQsIFwiZ2V0dGVyIHNob3VsZCBoYXZlIG5vIHBhcmFtc1wiKTtlbHNlIHRoaXMucmFpc2Uoc3RhcnQsIFwic2V0dGVyIHNob3VsZCBoYXZlIGV4YWN0bHkgb25lIHBhcmFtXCIpO1xuICAgICAgfVxuICAgIH1cbiAgfVxuICBub2RlLmJvZHkgPSB0aGlzLmZpbmlzaE5vZGUoY2xhc3NCb2R5LCBcIkNsYXNzQm9keVwiKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBpc1N0YXRlbWVudCA/IFwiQ2xhc3NEZWNsYXJhdGlvblwiIDogXCJDbGFzc0V4cHJlc3Npb25cIik7XG59O1xuXG5wcC5wYXJzZUNsYXNzTWV0aG9kID0gZnVuY3Rpb24gKGNsYXNzQm9keSwgbWV0aG9kLCBpc0dlbmVyYXRvcikge1xuICBtZXRob2QudmFsdWUgPSB0aGlzLnBhcnNlTWV0aG9kKGlzR2VuZXJhdG9yKTtcbiAgY2xhc3NCb2R5LmJvZHkucHVzaCh0aGlzLmZpbmlzaE5vZGUobWV0aG9kLCBcIk1ldGhvZERlZmluaXRpb25cIikpO1xufTtcblxucHAucGFyc2VDbGFzc0lkID0gZnVuY3Rpb24gKG5vZGUsIGlzU3RhdGVtZW50KSB7XG4gIG5vZGUuaWQgPSB0aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMubmFtZSA/IHRoaXMucGFyc2VJZGVudCgpIDogaXNTdGF0ZW1lbnQgPyB0aGlzLnVuZXhwZWN0ZWQoKSA6IG51bGw7XG59O1xuXG5wcC5wYXJzZUNsYXNzU3VwZXIgPSBmdW5jdGlvbiAobm9kZSkge1xuICBub2RlLnN1cGVyQ2xhc3MgPSB0aGlzLmVhdChfdG9rZW50eXBlLnR5cGVzLl9leHRlbmRzKSA/IHRoaXMucGFyc2VFeHByU3Vic2NyaXB0cygpIDogbnVsbDtcbn07XG5cbi8vIFBhcnNlcyBtb2R1bGUgZXhwb3J0IGRlY2xhcmF0aW9uLlxuXG5wcC5wYXJzZUV4cG9ydCA9IGZ1bmN0aW9uIChub2RlKSB7XG4gIHRoaXMubmV4dCgpO1xuICAvLyBleHBvcnQgKiBmcm9tICcuLi4nXG4gIGlmICh0aGlzLmVhdChfdG9rZW50eXBlLnR5cGVzLnN0YXIpKSB7XG4gICAgdGhpcy5leHBlY3RDb250ZXh0dWFsKFwiZnJvbVwiKTtcbiAgICBub2RlLnNvdXJjZSA9IHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5zdHJpbmcgPyB0aGlzLnBhcnNlRXhwckF0b20oKSA6IHRoaXMudW5leHBlY3RlZCgpO1xuICAgIHRoaXMuc2VtaWNvbG9uKCk7XG4gICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkV4cG9ydEFsbERlY2xhcmF0aW9uXCIpO1xuICB9XG4gIGlmICh0aGlzLmVhdChfdG9rZW50eXBlLnR5cGVzLl9kZWZhdWx0KSkge1xuICAgIC8vIGV4cG9ydCBkZWZhdWx0IC4uLlxuICAgIHZhciBleHByID0gdGhpcy5wYXJzZU1heWJlQXNzaWduKCk7XG4gICAgdmFyIG5lZWRzU2VtaSA9IHRydWU7XG4gICAgaWYgKGV4cHIudHlwZSA9PSBcIkZ1bmN0aW9uRXhwcmVzc2lvblwiIHx8IGV4cHIudHlwZSA9PSBcIkNsYXNzRXhwcmVzc2lvblwiKSB7XG4gICAgICBuZWVkc1NlbWkgPSBmYWxzZTtcbiAgICAgIGlmIChleHByLmlkKSB7XG4gICAgICAgIGV4cHIudHlwZSA9IGV4cHIudHlwZSA9PSBcIkZ1bmN0aW9uRXhwcmVzc2lvblwiID8gXCJGdW5jdGlvbkRlY2xhcmF0aW9uXCIgOiBcIkNsYXNzRGVjbGFyYXRpb25cIjtcbiAgICAgIH1cbiAgICB9XG4gICAgbm9kZS5kZWNsYXJhdGlvbiA9IGV4cHI7XG4gICAgaWYgKG5lZWRzU2VtaSkgdGhpcy5zZW1pY29sb24oKTtcbiAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiRXhwb3J0RGVmYXVsdERlY2xhcmF0aW9uXCIpO1xuICB9XG4gIC8vIGV4cG9ydCB2YXJ8Y29uc3R8bGV0fGZ1bmN0aW9ufGNsYXNzIC4uLlxuICBpZiAodGhpcy5zaG91bGRQYXJzZUV4cG9ydFN0YXRlbWVudCgpKSB7XG4gICAgbm9kZS5kZWNsYXJhdGlvbiA9IHRoaXMucGFyc2VTdGF0ZW1lbnQodHJ1ZSk7XG4gICAgbm9kZS5zcGVjaWZpZXJzID0gW107XG4gICAgbm9kZS5zb3VyY2UgPSBudWxsO1xuICB9IGVsc2Uge1xuICAgIC8vIGV4cG9ydCB7IHgsIHkgYXMgeiB9IFtmcm9tICcuLi4nXVxuICAgIG5vZGUuZGVjbGFyYXRpb24gPSBudWxsO1xuICAgIG5vZGUuc3BlY2lmaWVycyA9IHRoaXMucGFyc2VFeHBvcnRTcGVjaWZpZXJzKCk7XG4gICAgaWYgKHRoaXMuZWF0Q29udGV4dHVhbChcImZyb21cIikpIHtcbiAgICAgIG5vZGUuc291cmNlID0gdGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLnN0cmluZyA/IHRoaXMucGFyc2VFeHByQXRvbSgpIDogdGhpcy51bmV4cGVjdGVkKCk7XG4gICAgfSBlbHNlIHtcbiAgICAgIG5vZGUuc291cmNlID0gbnVsbDtcbiAgICB9XG4gICAgdGhpcy5zZW1pY29sb24oKTtcbiAgfVxuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiRXhwb3J0TmFtZWREZWNsYXJhdGlvblwiKTtcbn07XG5cbnBwLnNob3VsZFBhcnNlRXhwb3J0U3RhdGVtZW50ID0gZnVuY3Rpb24gKCkge1xuICByZXR1cm4gdGhpcy50eXBlLmtleXdvcmQ7XG59O1xuXG4vLyBQYXJzZXMgYSBjb21tYS1zZXBhcmF0ZWQgbGlzdCBvZiBtb2R1bGUgZXhwb3J0cy5cblxucHAucGFyc2VFeHBvcnRTcGVjaWZpZXJzID0gZnVuY3Rpb24gKCkge1xuICB2YXIgbm9kZXMgPSBbXSxcbiAgICAgIGZpcnN0ID0gdHJ1ZTtcbiAgLy8gZXhwb3J0IHsgeCwgeSBhcyB6IH0gW2Zyb20gJy4uLiddXG4gIHRoaXMuZXhwZWN0KF90b2tlbnR5cGUudHlwZXMuYnJhY2VMKTtcbiAgd2hpbGUgKCF0aGlzLmVhdChfdG9rZW50eXBlLnR5cGVzLmJyYWNlUikpIHtcbiAgICBpZiAoIWZpcnN0KSB7XG4gICAgICB0aGlzLmV4cGVjdChfdG9rZW50eXBlLnR5cGVzLmNvbW1hKTtcbiAgICAgIGlmICh0aGlzLmFmdGVyVHJhaWxpbmdDb21tYShfdG9rZW50eXBlLnR5cGVzLmJyYWNlUikpIGJyZWFrO1xuICAgIH0gZWxzZSBmaXJzdCA9IGZhbHNlO1xuXG4gICAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICAgIG5vZGUubG9jYWwgPSB0aGlzLnBhcnNlSWRlbnQodGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLl9kZWZhdWx0KTtcbiAgICBub2RlLmV4cG9ydGVkID0gdGhpcy5lYXRDb250ZXh0dWFsKFwiYXNcIikgPyB0aGlzLnBhcnNlSWRlbnQodHJ1ZSkgOiBub2RlLmxvY2FsO1xuICAgIG5vZGVzLnB1c2godGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiRXhwb3J0U3BlY2lmaWVyXCIpKTtcbiAgfVxuICByZXR1cm4gbm9kZXM7XG59O1xuXG4vLyBQYXJzZXMgaW1wb3J0IGRlY2xhcmF0aW9uLlxuXG5wcC5wYXJzZUltcG9ydCA9IGZ1bmN0aW9uIChub2RlKSB7XG4gIHRoaXMubmV4dCgpO1xuICAvLyBpbXBvcnQgJy4uLidcbiAgaWYgKHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5zdHJpbmcpIHtcbiAgICBub2RlLnNwZWNpZmllcnMgPSBlbXB0eTtcbiAgICBub2RlLnNvdXJjZSA9IHRoaXMucGFyc2VFeHByQXRvbSgpO1xuICB9IGVsc2Uge1xuICAgIG5vZGUuc3BlY2lmaWVycyA9IHRoaXMucGFyc2VJbXBvcnRTcGVjaWZpZXJzKCk7XG4gICAgdGhpcy5leHBlY3RDb250ZXh0dWFsKFwiZnJvbVwiKTtcbiAgICBub2RlLnNvdXJjZSA9IHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5zdHJpbmcgPyB0aGlzLnBhcnNlRXhwckF0b20oKSA6IHRoaXMudW5leHBlY3RlZCgpO1xuICB9XG4gIHRoaXMuc2VtaWNvbG9uKCk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJJbXBvcnREZWNsYXJhdGlvblwiKTtcbn07XG5cbi8vIFBhcnNlcyBhIGNvbW1hLXNlcGFyYXRlZCBsaXN0IG9mIG1vZHVsZSBpbXBvcnRzLlxuXG5wcC5wYXJzZUltcG9ydFNwZWNpZmllcnMgPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBub2RlcyA9IFtdLFxuICAgICAgZmlyc3QgPSB0cnVlO1xuICBpZiAodGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLm5hbWUpIHtcbiAgICAvLyBpbXBvcnQgZGVmYXVsdE9iaiwgeyB4LCB5IGFzIHogfSBmcm9tICcuLi4nXG4gICAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICAgIG5vZGUubG9jYWwgPSB0aGlzLnBhcnNlSWRlbnQoKTtcbiAgICB0aGlzLmNoZWNrTFZhbChub2RlLmxvY2FsLCB0cnVlKTtcbiAgICBub2Rlcy5wdXNoKHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkltcG9ydERlZmF1bHRTcGVjaWZpZXJcIikpO1xuICAgIGlmICghdGhpcy5lYXQoX3Rva2VudHlwZS50eXBlcy5jb21tYSkpIHJldHVybiBub2RlcztcbiAgfVxuICBpZiAodGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLnN0YXIpIHtcbiAgICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gICAgdGhpcy5uZXh0KCk7XG4gICAgdGhpcy5leHBlY3RDb250ZXh0dWFsKFwiYXNcIik7XG4gICAgbm9kZS5sb2NhbCA9IHRoaXMucGFyc2VJZGVudCgpO1xuICAgIHRoaXMuY2hlY2tMVmFsKG5vZGUubG9jYWwsIHRydWUpO1xuICAgIG5vZGVzLnB1c2godGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiSW1wb3J0TmFtZXNwYWNlU3BlY2lmaWVyXCIpKTtcbiAgICByZXR1cm4gbm9kZXM7XG4gIH1cbiAgdGhpcy5leHBlY3QoX3Rva2VudHlwZS50eXBlcy5icmFjZUwpO1xuICB3aGlsZSAoIXRoaXMuZWF0KF90b2tlbnR5cGUudHlwZXMuYnJhY2VSKSkge1xuICAgIGlmICghZmlyc3QpIHtcbiAgICAgIHRoaXMuZXhwZWN0KF90b2tlbnR5cGUudHlwZXMuY29tbWEpO1xuICAgICAgaWYgKHRoaXMuYWZ0ZXJUcmFpbGluZ0NvbW1hKF90b2tlbnR5cGUudHlwZXMuYnJhY2VSKSkgYnJlYWs7XG4gICAgfSBlbHNlIGZpcnN0ID0gZmFsc2U7XG5cbiAgICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gICAgbm9kZS5pbXBvcnRlZCA9IHRoaXMucGFyc2VJZGVudCh0cnVlKTtcbiAgICBub2RlLmxvY2FsID0gdGhpcy5lYXRDb250ZXh0dWFsKFwiYXNcIikgPyB0aGlzLnBhcnNlSWRlbnQoKSA6IG5vZGUuaW1wb3J0ZWQ7XG4gICAgdGhpcy5jaGVja0xWYWwobm9kZS5sb2NhbCwgdHJ1ZSk7XG4gICAgbm9kZXMucHVzaCh0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJJbXBvcnRTcGVjaWZpZXJcIikpO1xuICB9XG4gIHJldHVybiBub2Rlcztcbn07XG5cbn0se1wiLi9zdGF0ZVwiOjEwLFwiLi90b2tlbnR5cGVcIjoxNCxcIi4vd2hpdGVzcGFjZVwiOjE2fV0sMTI6W2Z1bmN0aW9uKF9kZXJlcV8sbW9kdWxlLGV4cG9ydHMpe1xuLy8gVGhlIGFsZ29yaXRobSB1c2VkIHRvIGRldGVybWluZSB3aGV0aGVyIGEgcmVnZXhwIGNhbiBhcHBlYXIgYXQgYVxuLy8gZ2l2ZW4gcG9pbnQgaW4gdGhlIHByb2dyYW0gaXMgbG9vc2VseSBiYXNlZCBvbiBzd2VldC5qcycgYXBwcm9hY2guXG4vLyBTZWUgaHR0cHM6Ly9naXRodWIuY29tL21vemlsbGEvc3dlZXQuanMvd2lraS9kZXNpZ25cblxuXCJ1c2Ugc3RyaWN0XCI7XG5cbmV4cG9ydHMuX19lc01vZHVsZSA9IHRydWU7XG5cbmZ1bmN0aW9uIF9jbGFzc0NhbGxDaGVjayhpbnN0YW5jZSwgQ29uc3RydWN0b3IpIHsgaWYgKCEoaW5zdGFuY2UgaW5zdGFuY2VvZiBDb25zdHJ1Y3RvcikpIHsgdGhyb3cgbmV3IFR5cGVFcnJvcihcIkNhbm5vdCBjYWxsIGEgY2xhc3MgYXMgYSBmdW5jdGlvblwiKTsgfSB9XG5cbnZhciBfc3RhdGUgPSBfZGVyZXFfKFwiLi9zdGF0ZVwiKTtcblxudmFyIF90b2tlbnR5cGUgPSBfZGVyZXFfKFwiLi90b2tlbnR5cGVcIik7XG5cbnZhciBfd2hpdGVzcGFjZSA9IF9kZXJlcV8oXCIuL3doaXRlc3BhY2VcIik7XG5cbnZhciBUb2tDb250ZXh0ID0gZnVuY3Rpb24gVG9rQ29udGV4dCh0b2tlbiwgaXNFeHByLCBwcmVzZXJ2ZVNwYWNlLCBvdmVycmlkZSkge1xuICBfY2xhc3NDYWxsQ2hlY2sodGhpcywgVG9rQ29udGV4dCk7XG5cbiAgdGhpcy50b2tlbiA9IHRva2VuO1xuICB0aGlzLmlzRXhwciA9ICEhaXNFeHByO1xuICB0aGlzLnByZXNlcnZlU3BhY2UgPSAhIXByZXNlcnZlU3BhY2U7XG4gIHRoaXMub3ZlcnJpZGUgPSBvdmVycmlkZTtcbn07XG5cbmV4cG9ydHMuVG9rQ29udGV4dCA9IFRva0NvbnRleHQ7XG52YXIgdHlwZXMgPSB7XG4gIGJfc3RhdDogbmV3IFRva0NvbnRleHQoXCJ7XCIsIGZhbHNlKSxcbiAgYl9leHByOiBuZXcgVG9rQ29udGV4dChcIntcIiwgdHJ1ZSksXG4gIGJfdG1wbDogbmV3IFRva0NvbnRleHQoXCIke1wiLCB0cnVlKSxcbiAgcF9zdGF0OiBuZXcgVG9rQ29udGV4dChcIihcIiwgZmFsc2UpLFxuICBwX2V4cHI6IG5ldyBUb2tDb250ZXh0KFwiKFwiLCB0cnVlKSxcbiAgcV90bXBsOiBuZXcgVG9rQ29udGV4dChcImBcIiwgdHJ1ZSwgdHJ1ZSwgZnVuY3Rpb24gKHApIHtcbiAgICByZXR1cm4gcC5yZWFkVG1wbFRva2VuKCk7XG4gIH0pLFxuICBmX2V4cHI6IG5ldyBUb2tDb250ZXh0KFwiZnVuY3Rpb25cIiwgdHJ1ZSlcbn07XG5cbmV4cG9ydHMudHlwZXMgPSB0eXBlcztcbnZhciBwcCA9IF9zdGF0ZS5QYXJzZXIucHJvdG90eXBlO1xuXG5wcC5pbml0aWFsQ29udGV4dCA9IGZ1bmN0aW9uICgpIHtcbiAgcmV0dXJuIFt0eXBlcy5iX3N0YXRdO1xufTtcblxucHAuYnJhY2VJc0Jsb2NrID0gZnVuY3Rpb24gKHByZXZUeXBlKSB7XG4gIGlmIChwcmV2VHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5jb2xvbikge1xuICAgIHZhciBfcGFyZW50ID0gdGhpcy5jdXJDb250ZXh0KCk7XG4gICAgaWYgKF9wYXJlbnQgPT09IHR5cGVzLmJfc3RhdCB8fCBfcGFyZW50ID09PSB0eXBlcy5iX2V4cHIpIHJldHVybiAhX3BhcmVudC5pc0V4cHI7XG4gIH1cbiAgaWYgKHByZXZUeXBlID09PSBfdG9rZW50eXBlLnR5cGVzLl9yZXR1cm4pIHJldHVybiBfd2hpdGVzcGFjZS5saW5lQnJlYWsudGVzdCh0aGlzLmlucHV0LnNsaWNlKHRoaXMubGFzdFRva0VuZCwgdGhpcy5zdGFydCkpO1xuICBpZiAocHJldlR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuX2Vsc2UgfHwgcHJldlR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuc2VtaSB8fCBwcmV2VHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5lb2YgfHwgcHJldlR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMucGFyZW5SKSByZXR1cm4gdHJ1ZTtcbiAgaWYgKHByZXZUeXBlID09IF90b2tlbnR5cGUudHlwZXMuYnJhY2VMKSByZXR1cm4gdGhpcy5jdXJDb250ZXh0KCkgPT09IHR5cGVzLmJfc3RhdDtcbiAgcmV0dXJuICF0aGlzLmV4cHJBbGxvd2VkO1xufTtcblxucHAudXBkYXRlQ29udGV4dCA9IGZ1bmN0aW9uIChwcmV2VHlwZSkge1xuICB2YXIgdXBkYXRlID0gdW5kZWZpbmVkLFxuICAgICAgdHlwZSA9IHRoaXMudHlwZTtcbiAgaWYgKHR5cGUua2V5d29yZCAmJiBwcmV2VHlwZSA9PSBfdG9rZW50eXBlLnR5cGVzLmRvdCkgdGhpcy5leHByQWxsb3dlZCA9IGZhbHNlO2Vsc2UgaWYgKHVwZGF0ZSA9IHR5cGUudXBkYXRlQ29udGV4dCkgdXBkYXRlLmNhbGwodGhpcywgcHJldlR5cGUpO2Vsc2UgdGhpcy5leHByQWxsb3dlZCA9IHR5cGUuYmVmb3JlRXhwcjtcbn07XG5cbi8vIFRva2VuLXNwZWNpZmljIGNvbnRleHQgdXBkYXRlIGNvZGVcblxuX3Rva2VudHlwZS50eXBlcy5wYXJlblIudXBkYXRlQ29udGV4dCA9IF90b2tlbnR5cGUudHlwZXMuYnJhY2VSLnVwZGF0ZUNvbnRleHQgPSBmdW5jdGlvbiAoKSB7XG4gIGlmICh0aGlzLmNvbnRleHQubGVuZ3RoID09IDEpIHtcbiAgICB0aGlzLmV4cHJBbGxvd2VkID0gdHJ1ZTtcbiAgICByZXR1cm47XG4gIH1cbiAgdmFyIG91dCA9IHRoaXMuY29udGV4dC5wb3AoKTtcbiAgaWYgKG91dCA9PT0gdHlwZXMuYl9zdGF0ICYmIHRoaXMuY3VyQ29udGV4dCgpID09PSB0eXBlcy5mX2V4cHIpIHtcbiAgICB0aGlzLmNvbnRleHQucG9wKCk7XG4gICAgdGhpcy5leHByQWxsb3dlZCA9IGZhbHNlO1xuICB9IGVsc2UgaWYgKG91dCA9PT0gdHlwZXMuYl90bXBsKSB7XG4gICAgdGhpcy5leHByQWxsb3dlZCA9IHRydWU7XG4gIH0gZWxzZSB7XG4gICAgdGhpcy5leHByQWxsb3dlZCA9ICFvdXQuaXNFeHByO1xuICB9XG59O1xuXG5fdG9rZW50eXBlLnR5cGVzLmJyYWNlTC51cGRhdGVDb250ZXh0ID0gZnVuY3Rpb24gKHByZXZUeXBlKSB7XG4gIHRoaXMuY29udGV4dC5wdXNoKHRoaXMuYnJhY2VJc0Jsb2NrKHByZXZUeXBlKSA/IHR5cGVzLmJfc3RhdCA6IHR5cGVzLmJfZXhwcik7XG4gIHRoaXMuZXhwckFsbG93ZWQgPSB0cnVlO1xufTtcblxuX3Rva2VudHlwZS50eXBlcy5kb2xsYXJCcmFjZUwudXBkYXRlQ29udGV4dCA9IGZ1bmN0aW9uICgpIHtcbiAgdGhpcy5jb250ZXh0LnB1c2godHlwZXMuYl90bXBsKTtcbiAgdGhpcy5leHByQWxsb3dlZCA9IHRydWU7XG59O1xuXG5fdG9rZW50eXBlLnR5cGVzLnBhcmVuTC51cGRhdGVDb250ZXh0ID0gZnVuY3Rpb24gKHByZXZUeXBlKSB7XG4gIHZhciBzdGF0ZW1lbnRQYXJlbnMgPSBwcmV2VHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5faWYgfHwgcHJldlR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuX2ZvciB8fCBwcmV2VHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5fd2l0aCB8fCBwcmV2VHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5fd2hpbGU7XG4gIHRoaXMuY29udGV4dC5wdXNoKHN0YXRlbWVudFBhcmVucyA/IHR5cGVzLnBfc3RhdCA6IHR5cGVzLnBfZXhwcik7XG4gIHRoaXMuZXhwckFsbG93ZWQgPSB0cnVlO1xufTtcblxuX3Rva2VudHlwZS50eXBlcy5pbmNEZWMudXBkYXRlQ29udGV4dCA9IGZ1bmN0aW9uICgpIHt9O1xuXG5fdG9rZW50eXBlLnR5cGVzLl9mdW5jdGlvbi51cGRhdGVDb250ZXh0ID0gZnVuY3Rpb24gKCkge1xuICBpZiAodGhpcy5jdXJDb250ZXh0KCkgIT09IHR5cGVzLmJfc3RhdCkgdGhpcy5jb250ZXh0LnB1c2godHlwZXMuZl9leHByKTtcbiAgdGhpcy5leHByQWxsb3dlZCA9IGZhbHNlO1xufTtcblxuX3Rva2VudHlwZS50eXBlcy5iYWNrUXVvdGUudXBkYXRlQ29udGV4dCA9IGZ1bmN0aW9uICgpIHtcbiAgaWYgKHRoaXMuY3VyQ29udGV4dCgpID09PSB0eXBlcy5xX3RtcGwpIHRoaXMuY29udGV4dC5wb3AoKTtlbHNlIHRoaXMuY29udGV4dC5wdXNoKHR5cGVzLnFfdG1wbCk7XG4gIHRoaXMuZXhwckFsbG93ZWQgPSBmYWxzZTtcbn07XG5cbi8vIHRva0V4cHJBbGxvd2VkIHN0YXlzIHVuY2hhbmdlZFxuXG59LHtcIi4vc3RhdGVcIjoxMCxcIi4vdG9rZW50eXBlXCI6MTQsXCIuL3doaXRlc3BhY2VcIjoxNn1dLDEzOltmdW5jdGlvbihfZGVyZXFfLG1vZHVsZSxleHBvcnRzKXtcblwidXNlIHN0cmljdFwiO1xuXG5leHBvcnRzLl9fZXNNb2R1bGUgPSB0cnVlO1xuXG5mdW5jdGlvbiBfY2xhc3NDYWxsQ2hlY2soaW5zdGFuY2UsIENvbnN0cnVjdG9yKSB7IGlmICghKGluc3RhbmNlIGluc3RhbmNlb2YgQ29uc3RydWN0b3IpKSB7IHRocm93IG5ldyBUeXBlRXJyb3IoXCJDYW5ub3QgY2FsbCBhIGNsYXNzIGFzIGEgZnVuY3Rpb25cIik7IH0gfVxuXG52YXIgX2lkZW50aWZpZXIgPSBfZGVyZXFfKFwiLi9pZGVudGlmaWVyXCIpO1xuXG52YXIgX3Rva2VudHlwZSA9IF9kZXJlcV8oXCIuL3Rva2VudHlwZVwiKTtcblxudmFyIF9zdGF0ZSA9IF9kZXJlcV8oXCIuL3N0YXRlXCIpO1xuXG52YXIgX2xvY3V0aWwgPSBfZGVyZXFfKFwiLi9sb2N1dGlsXCIpO1xuXG52YXIgX3doaXRlc3BhY2UgPSBfZGVyZXFfKFwiLi93aGl0ZXNwYWNlXCIpO1xuXG4vLyBPYmplY3QgdHlwZSB1c2VkIHRvIHJlcHJlc2VudCB0b2tlbnMuIE5vdGUgdGhhdCBub3JtYWxseSwgdG9rZW5zXG4vLyBzaW1wbHkgZXhpc3QgYXMgcHJvcGVydGllcyBvbiB0aGUgcGFyc2VyIG9iamVjdC4gVGhpcyBpcyBvbmx5XG4vLyB1c2VkIGZvciB0aGUgb25Ub2tlbiBjYWxsYmFjayBhbmQgdGhlIGV4dGVybmFsIHRva2VuaXplci5cblxudmFyIFRva2VuID0gZnVuY3Rpb24gVG9rZW4ocCkge1xuICBfY2xhc3NDYWxsQ2hlY2sodGhpcywgVG9rZW4pO1xuXG4gIHRoaXMudHlwZSA9IHAudHlwZTtcbiAgdGhpcy52YWx1ZSA9IHAudmFsdWU7XG4gIHRoaXMuc3RhcnQgPSBwLnN0YXJ0O1xuICB0aGlzLmVuZCA9IHAuZW5kO1xuICBpZiAocC5vcHRpb25zLmxvY2F0aW9ucykgdGhpcy5sb2MgPSBuZXcgX2xvY3V0aWwuU291cmNlTG9jYXRpb24ocCwgcC5zdGFydExvYywgcC5lbmRMb2MpO1xuICBpZiAocC5vcHRpb25zLnJhbmdlcykgdGhpcy5yYW5nZSA9IFtwLnN0YXJ0LCBwLmVuZF07XG59O1xuXG5leHBvcnRzLlRva2VuID0gVG9rZW47XG5cbi8vICMjIFRva2VuaXplclxuXG52YXIgcHAgPSBfc3RhdGUuUGFyc2VyLnByb3RvdHlwZTtcblxuLy8gQXJlIHdlIHJ1bm5pbmcgdW5kZXIgUmhpbm8/XG52YXIgaXNSaGlubyA9IHR5cGVvZiBQYWNrYWdlcyA9PSBcIm9iamVjdFwiICYmIE9iamVjdC5wcm90b3R5cGUudG9TdHJpbmcuY2FsbChQYWNrYWdlcykgPT0gXCJbb2JqZWN0IEphdmFQYWNrYWdlXVwiO1xuXG4vLyBNb3ZlIHRvIHRoZSBuZXh0IHRva2VuXG5cbnBwLm5leHQgPSBmdW5jdGlvbiAoKSB7XG4gIGlmICh0aGlzLm9wdGlvbnMub25Ub2tlbikgdGhpcy5vcHRpb25zLm9uVG9rZW4obmV3IFRva2VuKHRoaXMpKTtcblxuICB0aGlzLmxhc3RUb2tFbmQgPSB0aGlzLmVuZDtcbiAgdGhpcy5sYXN0VG9rU3RhcnQgPSB0aGlzLnN0YXJ0O1xuICB0aGlzLmxhc3RUb2tFbmRMb2MgPSB0aGlzLmVuZExvYztcbiAgdGhpcy5sYXN0VG9rU3RhcnRMb2MgPSB0aGlzLnN0YXJ0TG9jO1xuICB0aGlzLm5leHRUb2tlbigpO1xufTtcblxucHAuZ2V0VG9rZW4gPSBmdW5jdGlvbiAoKSB7XG4gIHRoaXMubmV4dCgpO1xuICByZXR1cm4gbmV3IFRva2VuKHRoaXMpO1xufTtcblxuLy8gSWYgd2UncmUgaW4gYW4gRVM2IGVudmlyb25tZW50LCBtYWtlIHBhcnNlcnMgaXRlcmFibGVcbmlmICh0eXBlb2YgU3ltYm9sICE9PSBcInVuZGVmaW5lZFwiKSBwcFtTeW1ib2wuaXRlcmF0b3JdID0gZnVuY3Rpb24gKCkge1xuICB2YXIgc2VsZiA9IHRoaXM7XG4gIHJldHVybiB7IG5leHQ6IGZ1bmN0aW9uIG5leHQoKSB7XG4gICAgICB2YXIgdG9rZW4gPSBzZWxmLmdldFRva2VuKCk7XG4gICAgICByZXR1cm4ge1xuICAgICAgICBkb25lOiB0b2tlbi50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLmVvZixcbiAgICAgICAgdmFsdWU6IHRva2VuXG4gICAgICB9O1xuICAgIH0gfTtcbn07XG5cbi8vIFRvZ2dsZSBzdHJpY3QgbW9kZS4gUmUtcmVhZHMgdGhlIG5leHQgbnVtYmVyIG9yIHN0cmluZyB0byBwbGVhc2Vcbi8vIHBlZGFudGljIHRlc3RzIChgXCJ1c2Ugc3RyaWN0XCI7IDAxMDtgIHNob3VsZCBmYWlsKS5cblxucHAuc2V0U3RyaWN0ID0gZnVuY3Rpb24gKHN0cmljdCkge1xuICB0aGlzLnN0cmljdCA9IHN0cmljdDtcbiAgaWYgKHRoaXMudHlwZSAhPT0gX3Rva2VudHlwZS50eXBlcy5udW0gJiYgdGhpcy50eXBlICE9PSBfdG9rZW50eXBlLnR5cGVzLnN0cmluZykgcmV0dXJuO1xuICB0aGlzLnBvcyA9IHRoaXMuc3RhcnQ7XG4gIGlmICh0aGlzLm9wdGlvbnMubG9jYXRpb25zKSB7XG4gICAgd2hpbGUgKHRoaXMucG9zIDwgdGhpcy5saW5lU3RhcnQpIHtcbiAgICAgIHRoaXMubGluZVN0YXJ0ID0gdGhpcy5pbnB1dC5sYXN0SW5kZXhPZihcIlxcblwiLCB0aGlzLmxpbmVTdGFydCAtIDIpICsgMTtcbiAgICAgIC0tdGhpcy5jdXJMaW5lO1xuICAgIH1cbiAgfVxuICB0aGlzLm5leHRUb2tlbigpO1xufTtcblxucHAuY3VyQ29udGV4dCA9IGZ1bmN0aW9uICgpIHtcbiAgcmV0dXJuIHRoaXMuY29udGV4dFt0aGlzLmNvbnRleHQubGVuZ3RoIC0gMV07XG59O1xuXG4vLyBSZWFkIGEgc2luZ2xlIHRva2VuLCB1cGRhdGluZyB0aGUgcGFyc2VyIG9iamVjdCdzIHRva2VuLXJlbGF0ZWRcbi8vIHByb3BlcnRpZXMuXG5cbnBwLm5leHRUb2tlbiA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIGN1ckNvbnRleHQgPSB0aGlzLmN1ckNvbnRleHQoKTtcbiAgaWYgKCFjdXJDb250ZXh0IHx8ICFjdXJDb250ZXh0LnByZXNlcnZlU3BhY2UpIHRoaXMuc2tpcFNwYWNlKCk7XG5cbiAgdGhpcy5zdGFydCA9IHRoaXMucG9zO1xuICBpZiAodGhpcy5vcHRpb25zLmxvY2F0aW9ucykgdGhpcy5zdGFydExvYyA9IHRoaXMuY3VyUG9zaXRpb24oKTtcbiAgaWYgKHRoaXMucG9zID49IHRoaXMuaW5wdXQubGVuZ3RoKSByZXR1cm4gdGhpcy5maW5pc2hUb2tlbihfdG9rZW50eXBlLnR5cGVzLmVvZik7XG5cbiAgaWYgKGN1ckNvbnRleHQub3ZlcnJpZGUpIHJldHVybiBjdXJDb250ZXh0Lm92ZXJyaWRlKHRoaXMpO2Vsc2UgdGhpcy5yZWFkVG9rZW4odGhpcy5mdWxsQ2hhckNvZGVBdFBvcygpKTtcbn07XG5cbnBwLnJlYWRUb2tlbiA9IGZ1bmN0aW9uIChjb2RlKSB7XG4gIC8vIElkZW50aWZpZXIgb3Iga2V5d29yZC4gJ1xcdVhYWFgnIHNlcXVlbmNlcyBhcmUgYWxsb3dlZCBpblxuICAvLyBpZGVudGlmaWVycywgc28gJ1xcJyBhbHNvIGRpc3BhdGNoZXMgdG8gdGhhdC5cbiAgaWYgKF9pZGVudGlmaWVyLmlzSWRlbnRpZmllclN0YXJ0KGNvZGUsIHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KSB8fCBjb2RlID09PSA5MiAvKiAnXFwnICovKSByZXR1cm4gdGhpcy5yZWFkV29yZCgpO1xuXG4gIHJldHVybiB0aGlzLmdldFRva2VuRnJvbUNvZGUoY29kZSk7XG59O1xuXG5wcC5mdWxsQ2hhckNvZGVBdFBvcyA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIGNvZGUgPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MpO1xuICBpZiAoY29kZSA8PSAweGQ3ZmYgfHwgY29kZSA+PSAweGUwMDApIHJldHVybiBjb2RlO1xuICB2YXIgbmV4dCA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIDEpO1xuICByZXR1cm4gKGNvZGUgPDwgMTApICsgbmV4dCAtIDB4MzVmZGMwMDtcbn07XG5cbnBwLnNraXBCbG9ja0NvbW1lbnQgPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBzdGFydExvYyA9IHRoaXMub3B0aW9ucy5vbkNvbW1lbnQgJiYgdGhpcy5jdXJQb3NpdGlvbigpO1xuICB2YXIgc3RhcnQgPSB0aGlzLnBvcyxcbiAgICAgIGVuZCA9IHRoaXMuaW5wdXQuaW5kZXhPZihcIiovXCIsIHRoaXMucG9zICs9IDIpO1xuICBpZiAoZW5kID09PSAtMSkgdGhpcy5yYWlzZSh0aGlzLnBvcyAtIDIsIFwiVW50ZXJtaW5hdGVkIGNvbW1lbnRcIik7XG4gIHRoaXMucG9zID0gZW5kICsgMjtcbiAgaWYgKHRoaXMub3B0aW9ucy5sb2NhdGlvbnMpIHtcbiAgICBfd2hpdGVzcGFjZS5saW5lQnJlYWtHLmxhc3RJbmRleCA9IHN0YXJ0O1xuICAgIHZhciBtYXRjaCA9IHVuZGVmaW5lZDtcbiAgICB3aGlsZSAoKG1hdGNoID0gX3doaXRlc3BhY2UubGluZUJyZWFrRy5leGVjKHRoaXMuaW5wdXQpKSAmJiBtYXRjaC5pbmRleCA8IHRoaXMucG9zKSB7XG4gICAgICArK3RoaXMuY3VyTGluZTtcbiAgICAgIHRoaXMubGluZVN0YXJ0ID0gbWF0Y2guaW5kZXggKyBtYXRjaFswXS5sZW5ndGg7XG4gICAgfVxuICB9XG4gIGlmICh0aGlzLm9wdGlvbnMub25Db21tZW50KSB0aGlzLm9wdGlvbnMub25Db21tZW50KHRydWUsIHRoaXMuaW5wdXQuc2xpY2Uoc3RhcnQgKyAyLCBlbmQpLCBzdGFydCwgdGhpcy5wb3MsIHN0YXJ0TG9jLCB0aGlzLmN1clBvc2l0aW9uKCkpO1xufTtcblxucHAuc2tpcExpbmVDb21tZW50ID0gZnVuY3Rpb24gKHN0YXJ0U2tpcCkge1xuICB2YXIgc3RhcnQgPSB0aGlzLnBvcztcbiAgdmFyIHN0YXJ0TG9jID0gdGhpcy5vcHRpb25zLm9uQ29tbWVudCAmJiB0aGlzLmN1clBvc2l0aW9uKCk7XG4gIHZhciBjaCA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArPSBzdGFydFNraXApO1xuICB3aGlsZSAodGhpcy5wb3MgPCB0aGlzLmlucHV0Lmxlbmd0aCAmJiBjaCAhPT0gMTAgJiYgY2ggIT09IDEzICYmIGNoICE9PSA4MjMyICYmIGNoICE9PSA4MjMzKSB7XG4gICAgKyt0aGlzLnBvcztcbiAgICBjaCA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyk7XG4gIH1cbiAgaWYgKHRoaXMub3B0aW9ucy5vbkNvbW1lbnQpIHRoaXMub3B0aW9ucy5vbkNvbW1lbnQoZmFsc2UsIHRoaXMuaW5wdXQuc2xpY2Uoc3RhcnQgKyBzdGFydFNraXAsIHRoaXMucG9zKSwgc3RhcnQsIHRoaXMucG9zLCBzdGFydExvYywgdGhpcy5jdXJQb3NpdGlvbigpKTtcbn07XG5cbi8vIENhbGxlZCBhdCB0aGUgc3RhcnQgb2YgdGhlIHBhcnNlIGFuZCBhZnRlciBldmVyeSB0b2tlbi4gU2tpcHNcbi8vIHdoaXRlc3BhY2UgYW5kIGNvbW1lbnRzLCBhbmQuXG5cbnBwLnNraXBTcGFjZSA9IGZ1bmN0aW9uICgpIHtcbiAgbG9vcDogd2hpbGUgKHRoaXMucG9zIDwgdGhpcy5pbnB1dC5sZW5ndGgpIHtcbiAgICB2YXIgY2ggPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MpO1xuICAgIHN3aXRjaCAoY2gpIHtcbiAgICAgIGNhc2UgMzI6Y2FzZSAxNjA6XG4gICAgICAgIC8vICcgJ1xuICAgICAgICArK3RoaXMucG9zO1xuICAgICAgICBicmVhaztcbiAgICAgIGNhc2UgMTM6XG4gICAgICAgIGlmICh0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAxKSA9PT0gMTApIHtcbiAgICAgICAgICArK3RoaXMucG9zO1xuICAgICAgICB9XG4gICAgICBjYXNlIDEwOmNhc2UgODIzMjpjYXNlIDgyMzM6XG4gICAgICAgICsrdGhpcy5wb3M7XG4gICAgICAgIGlmICh0aGlzLm9wdGlvbnMubG9jYXRpb25zKSB7XG4gICAgICAgICAgKyt0aGlzLmN1ckxpbmU7XG4gICAgICAgICAgdGhpcy5saW5lU3RhcnQgPSB0aGlzLnBvcztcbiAgICAgICAgfVxuICAgICAgICBicmVhaztcbiAgICAgIGNhc2UgNDc6XG4gICAgICAgIC8vICcvJ1xuICAgICAgICBzd2l0Y2ggKHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIDEpKSB7XG4gICAgICAgICAgY2FzZSA0MjpcbiAgICAgICAgICAgIC8vICcqJ1xuICAgICAgICAgICAgdGhpcy5za2lwQmxvY2tDb21tZW50KCk7XG4gICAgICAgICAgICBicmVhaztcbiAgICAgICAgICBjYXNlIDQ3OlxuICAgICAgICAgICAgdGhpcy5za2lwTGluZUNvbW1lbnQoMik7XG4gICAgICAgICAgICBicmVhaztcbiAgICAgICAgICBkZWZhdWx0OlxuICAgICAgICAgICAgYnJlYWsgbG9vcDtcbiAgICAgICAgfVxuICAgICAgICBicmVhaztcbiAgICAgIGRlZmF1bHQ6XG4gICAgICAgIGlmIChjaCA+IDggJiYgY2ggPCAxNCB8fCBjaCA+PSA1NzYwICYmIF93aGl0ZXNwYWNlLm5vbkFTQ0lJd2hpdGVzcGFjZS50ZXN0KFN0cmluZy5mcm9tQ2hhckNvZGUoY2gpKSkge1xuICAgICAgICAgICsrdGhpcy5wb3M7XG4gICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgYnJlYWsgbG9vcDtcbiAgICAgICAgfVxuICAgIH1cbiAgfVxufTtcblxuLy8gQ2FsbGVkIGF0IHRoZSBlbmQgb2YgZXZlcnkgdG9rZW4uIFNldHMgYGVuZGAsIGB2YWxgLCBhbmRcbi8vIG1haW50YWlucyBgY29udGV4dGAgYW5kIGBleHByQWxsb3dlZGAsIGFuZCBza2lwcyB0aGUgc3BhY2UgYWZ0ZXJcbi8vIHRoZSB0b2tlbiwgc28gdGhhdCB0aGUgbmV4dCBvbmUncyBgc3RhcnRgIHdpbGwgcG9pbnQgYXQgdGhlXG4vLyByaWdodCBwb3NpdGlvbi5cblxucHAuZmluaXNoVG9rZW4gPSBmdW5jdGlvbiAodHlwZSwgdmFsKSB7XG4gIHRoaXMuZW5kID0gdGhpcy5wb3M7XG4gIGlmICh0aGlzLm9wdGlvbnMubG9jYXRpb25zKSB0aGlzLmVuZExvYyA9IHRoaXMuY3VyUG9zaXRpb24oKTtcbiAgdmFyIHByZXZUeXBlID0gdGhpcy50eXBlO1xuICB0aGlzLnR5cGUgPSB0eXBlO1xuICB0aGlzLnZhbHVlID0gdmFsO1xuXG4gIHRoaXMudXBkYXRlQ29udGV4dChwcmV2VHlwZSk7XG59O1xuXG4vLyAjIyMgVG9rZW4gcmVhZGluZ1xuXG4vLyBUaGlzIGlzIHRoZSBmdW5jdGlvbiB0aGF0IGlzIGNhbGxlZCB0byBmZXRjaCB0aGUgbmV4dCB0b2tlbi4gSXRcbi8vIGlzIHNvbWV3aGF0IG9ic2N1cmUsIGJlY2F1c2UgaXQgd29ya3MgaW4gY2hhcmFjdGVyIGNvZGVzIHJhdGhlclxuLy8gdGhhbiBjaGFyYWN0ZXJzLCBhbmQgYmVjYXVzZSBvcGVyYXRvciBwYXJzaW5nIGhhcyBiZWVuIGlubGluZWRcbi8vIGludG8gaXQuXG4vL1xuLy8gQWxsIGluIHRoZSBuYW1lIG9mIHNwZWVkLlxuLy9cbnBwLnJlYWRUb2tlbl9kb3QgPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBuZXh0ID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMSk7XG4gIGlmIChuZXh0ID49IDQ4ICYmIG5leHQgPD0gNTcpIHJldHVybiB0aGlzLnJlYWROdW1iZXIodHJ1ZSk7XG4gIHZhciBuZXh0MiA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIDIpO1xuICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYgJiYgbmV4dCA9PT0gNDYgJiYgbmV4dDIgPT09IDQ2KSB7XG4gICAgLy8gNDYgPSBkb3QgJy4nXG4gICAgdGhpcy5wb3MgKz0gMztcbiAgICByZXR1cm4gdGhpcy5maW5pc2hUb2tlbihfdG9rZW50eXBlLnR5cGVzLmVsbGlwc2lzKTtcbiAgfSBlbHNlIHtcbiAgICArK3RoaXMucG9zO1xuICAgIHJldHVybiB0aGlzLmZpbmlzaFRva2VuKF90b2tlbnR5cGUudHlwZXMuZG90KTtcbiAgfVxufTtcblxucHAucmVhZFRva2VuX3NsYXNoID0gZnVuY3Rpb24gKCkge1xuICAvLyAnLydcbiAgdmFyIG5leHQgPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAxKTtcbiAgaWYgKHRoaXMuZXhwckFsbG93ZWQpIHtcbiAgICArK3RoaXMucG9zO3JldHVybiB0aGlzLnJlYWRSZWdleHAoKTtcbiAgfVxuICBpZiAobmV4dCA9PT0gNjEpIHJldHVybiB0aGlzLmZpbmlzaE9wKF90b2tlbnR5cGUudHlwZXMuYXNzaWduLCAyKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoT3AoX3Rva2VudHlwZS50eXBlcy5zbGFzaCwgMSk7XG59O1xuXG5wcC5yZWFkVG9rZW5fbXVsdF9tb2R1bG8gPSBmdW5jdGlvbiAoY29kZSkge1xuICAvLyAnJSonXG4gIHZhciBuZXh0ID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMSk7XG4gIGlmIChuZXh0ID09PSA2MSkgcmV0dXJuIHRoaXMuZmluaXNoT3AoX3Rva2VudHlwZS50eXBlcy5hc3NpZ24sIDIpO1xuICByZXR1cm4gdGhpcy5maW5pc2hPcChjb2RlID09PSA0MiA/IF90b2tlbnR5cGUudHlwZXMuc3RhciA6IF90b2tlbnR5cGUudHlwZXMubW9kdWxvLCAxKTtcbn07XG5cbnBwLnJlYWRUb2tlbl9waXBlX2FtcCA9IGZ1bmN0aW9uIChjb2RlKSB7XG4gIC8vICd8JidcbiAgdmFyIG5leHQgPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAxKTtcbiAgaWYgKG5leHQgPT09IGNvZGUpIHJldHVybiB0aGlzLmZpbmlzaE9wKGNvZGUgPT09IDEyNCA/IF90b2tlbnR5cGUudHlwZXMubG9naWNhbE9SIDogX3Rva2VudHlwZS50eXBlcy5sb2dpY2FsQU5ELCAyKTtcbiAgaWYgKG5leHQgPT09IDYxKSByZXR1cm4gdGhpcy5maW5pc2hPcChfdG9rZW50eXBlLnR5cGVzLmFzc2lnbiwgMik7XG4gIHJldHVybiB0aGlzLmZpbmlzaE9wKGNvZGUgPT09IDEyNCA/IF90b2tlbnR5cGUudHlwZXMuYml0d2lzZU9SIDogX3Rva2VudHlwZS50eXBlcy5iaXR3aXNlQU5ELCAxKTtcbn07XG5cbnBwLnJlYWRUb2tlbl9jYXJldCA9IGZ1bmN0aW9uICgpIHtcbiAgLy8gJ14nXG4gIHZhciBuZXh0ID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMSk7XG4gIGlmIChuZXh0ID09PSA2MSkgcmV0dXJuIHRoaXMuZmluaXNoT3AoX3Rva2VudHlwZS50eXBlcy5hc3NpZ24sIDIpO1xuICByZXR1cm4gdGhpcy5maW5pc2hPcChfdG9rZW50eXBlLnR5cGVzLmJpdHdpc2VYT1IsIDEpO1xufTtcblxucHAucmVhZFRva2VuX3BsdXNfbWluID0gZnVuY3Rpb24gKGNvZGUpIHtcbiAgLy8gJystJ1xuICB2YXIgbmV4dCA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIDEpO1xuICBpZiAobmV4dCA9PT0gY29kZSkge1xuICAgIGlmIChuZXh0ID09IDQ1ICYmIHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIDIpID09IDYyICYmIF93aGl0ZXNwYWNlLmxpbmVCcmVhay50ZXN0KHRoaXMuaW5wdXQuc2xpY2UodGhpcy5sYXN0VG9rRW5kLCB0aGlzLnBvcykpKSB7XG4gICAgICAvLyBBIGAtLT5gIGxpbmUgY29tbWVudFxuICAgICAgdGhpcy5za2lwTGluZUNvbW1lbnQoMyk7XG4gICAgICB0aGlzLnNraXBTcGFjZSgpO1xuICAgICAgcmV0dXJuIHRoaXMubmV4dFRva2VuKCk7XG4gICAgfVxuICAgIHJldHVybiB0aGlzLmZpbmlzaE9wKF90b2tlbnR5cGUudHlwZXMuaW5jRGVjLCAyKTtcbiAgfVxuICBpZiAobmV4dCA9PT0gNjEpIHJldHVybiB0aGlzLmZpbmlzaE9wKF90b2tlbnR5cGUudHlwZXMuYXNzaWduLCAyKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoT3AoX3Rva2VudHlwZS50eXBlcy5wbHVzTWluLCAxKTtcbn07XG5cbnBwLnJlYWRUb2tlbl9sdF9ndCA9IGZ1bmN0aW9uIChjb2RlKSB7XG4gIC8vICc8PidcbiAgdmFyIG5leHQgPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAxKTtcbiAgdmFyIHNpemUgPSAxO1xuICBpZiAobmV4dCA9PT0gY29kZSkge1xuICAgIHNpemUgPSBjb2RlID09PSA2MiAmJiB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAyKSA9PT0gNjIgPyAzIDogMjtcbiAgICBpZiAodGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgc2l6ZSkgPT09IDYxKSByZXR1cm4gdGhpcy5maW5pc2hPcChfdG9rZW50eXBlLnR5cGVzLmFzc2lnbiwgc2l6ZSArIDEpO1xuICAgIHJldHVybiB0aGlzLmZpbmlzaE9wKF90b2tlbnR5cGUudHlwZXMuYml0U2hpZnQsIHNpemUpO1xuICB9XG4gIGlmIChuZXh0ID09IDMzICYmIGNvZGUgPT0gNjAgJiYgdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMikgPT0gNDUgJiYgdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMykgPT0gNDUpIHtcbiAgICBpZiAodGhpcy5pbk1vZHVsZSkgdGhpcy51bmV4cGVjdGVkKCk7XG4gICAgLy8gYDwhLS1gLCBhbiBYTUwtc3R5bGUgY29tbWVudCB0aGF0IHNob3VsZCBiZSBpbnRlcnByZXRlZCBhcyBhIGxpbmUgY29tbWVudFxuICAgIHRoaXMuc2tpcExpbmVDb21tZW50KDQpO1xuICAgIHRoaXMuc2tpcFNwYWNlKCk7XG4gICAgcmV0dXJuIHRoaXMubmV4dFRva2VuKCk7XG4gIH1cbiAgaWYgKG5leHQgPT09IDYxKSBzaXplID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMikgPT09IDYxID8gMyA6IDI7XG4gIHJldHVybiB0aGlzLmZpbmlzaE9wKF90b2tlbnR5cGUudHlwZXMucmVsYXRpb25hbCwgc2l6ZSk7XG59O1xuXG5wcC5yZWFkVG9rZW5fZXFfZXhjbCA9IGZ1bmN0aW9uIChjb2RlKSB7XG4gIC8vICc9ISdcbiAgdmFyIG5leHQgPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAxKTtcbiAgaWYgKG5leHQgPT09IDYxKSByZXR1cm4gdGhpcy5maW5pc2hPcChfdG9rZW50eXBlLnR5cGVzLmVxdWFsaXR5LCB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAyKSA9PT0gNjEgPyAzIDogMik7XG4gIGlmIChjb2RlID09PSA2MSAmJiBuZXh0ID09PSA2MiAmJiB0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNikge1xuICAgIC8vICc9PidcbiAgICB0aGlzLnBvcyArPSAyO1xuICAgIHJldHVybiB0aGlzLmZpbmlzaFRva2VuKF90b2tlbnR5cGUudHlwZXMuYXJyb3cpO1xuICB9XG4gIHJldHVybiB0aGlzLmZpbmlzaE9wKGNvZGUgPT09IDYxID8gX3Rva2VudHlwZS50eXBlcy5lcSA6IF90b2tlbnR5cGUudHlwZXMucHJlZml4LCAxKTtcbn07XG5cbnBwLmdldFRva2VuRnJvbUNvZGUgPSBmdW5jdGlvbiAoY29kZSkge1xuICBzd2l0Y2ggKGNvZGUpIHtcbiAgICAvLyBUaGUgaW50ZXJwcmV0YXRpb24gb2YgYSBkb3QgZGVwZW5kcyBvbiB3aGV0aGVyIGl0IGlzIGZvbGxvd2VkXG4gICAgLy8gYnkgYSBkaWdpdCBvciBhbm90aGVyIHR3byBkb3RzLlxuICAgIGNhc2UgNDY6XG4gICAgICAvLyAnLidcbiAgICAgIHJldHVybiB0aGlzLnJlYWRUb2tlbl9kb3QoKTtcblxuICAgIC8vIFB1bmN0dWF0aW9uIHRva2Vucy5cbiAgICBjYXNlIDQwOlxuICAgICAgKyt0aGlzLnBvcztyZXR1cm4gdGhpcy5maW5pc2hUb2tlbihfdG9rZW50eXBlLnR5cGVzLnBhcmVuTCk7XG4gICAgY2FzZSA0MTpcbiAgICAgICsrdGhpcy5wb3M7cmV0dXJuIHRoaXMuZmluaXNoVG9rZW4oX3Rva2VudHlwZS50eXBlcy5wYXJlblIpO1xuICAgIGNhc2UgNTk6XG4gICAgICArK3RoaXMucG9zO3JldHVybiB0aGlzLmZpbmlzaFRva2VuKF90b2tlbnR5cGUudHlwZXMuc2VtaSk7XG4gICAgY2FzZSA0NDpcbiAgICAgICsrdGhpcy5wb3M7cmV0dXJuIHRoaXMuZmluaXNoVG9rZW4oX3Rva2VudHlwZS50eXBlcy5jb21tYSk7XG4gICAgY2FzZSA5MTpcbiAgICAgICsrdGhpcy5wb3M7cmV0dXJuIHRoaXMuZmluaXNoVG9rZW4oX3Rva2VudHlwZS50eXBlcy5icmFja2V0TCk7XG4gICAgY2FzZSA5MzpcbiAgICAgICsrdGhpcy5wb3M7cmV0dXJuIHRoaXMuZmluaXNoVG9rZW4oX3Rva2VudHlwZS50eXBlcy5icmFja2V0Uik7XG4gICAgY2FzZSAxMjM6XG4gICAgICArK3RoaXMucG9zO3JldHVybiB0aGlzLmZpbmlzaFRva2VuKF90b2tlbnR5cGUudHlwZXMuYnJhY2VMKTtcbiAgICBjYXNlIDEyNTpcbiAgICAgICsrdGhpcy5wb3M7cmV0dXJuIHRoaXMuZmluaXNoVG9rZW4oX3Rva2VudHlwZS50eXBlcy5icmFjZVIpO1xuICAgIGNhc2UgNTg6XG4gICAgICArK3RoaXMucG9zO3JldHVybiB0aGlzLmZpbmlzaFRva2VuKF90b2tlbnR5cGUudHlwZXMuY29sb24pO1xuICAgIGNhc2UgNjM6XG4gICAgICArK3RoaXMucG9zO3JldHVybiB0aGlzLmZpbmlzaFRva2VuKF90b2tlbnR5cGUudHlwZXMucXVlc3Rpb24pO1xuXG4gICAgY2FzZSA5NjpcbiAgICAgIC8vICdgJ1xuICAgICAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA8IDYpIGJyZWFrO1xuICAgICAgKyt0aGlzLnBvcztcbiAgICAgIHJldHVybiB0aGlzLmZpbmlzaFRva2VuKF90b2tlbnR5cGUudHlwZXMuYmFja1F1b3RlKTtcblxuICAgIGNhc2UgNDg6XG4gICAgICAvLyAnMCdcbiAgICAgIHZhciBuZXh0ID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMSk7XG4gICAgICBpZiAobmV4dCA9PT0gMTIwIHx8IG5leHQgPT09IDg4KSByZXR1cm4gdGhpcy5yZWFkUmFkaXhOdW1iZXIoMTYpOyAvLyAnMHgnLCAnMFgnIC0gaGV4IG51bWJlclxuICAgICAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KSB7XG4gICAgICAgIGlmIChuZXh0ID09PSAxMTEgfHwgbmV4dCA9PT0gNzkpIHJldHVybiB0aGlzLnJlYWRSYWRpeE51bWJlcig4KTsgLy8gJzBvJywgJzBPJyAtIG9jdGFsIG51bWJlclxuICAgICAgICBpZiAobmV4dCA9PT0gOTggfHwgbmV4dCA9PT0gNjYpIHJldHVybiB0aGlzLnJlYWRSYWRpeE51bWJlcigyKTsgLy8gJzBiJywgJzBCJyAtIGJpbmFyeSBudW1iZXJcbiAgICAgIH1cbiAgICAvLyBBbnl0aGluZyBlbHNlIGJlZ2lubmluZyB3aXRoIGEgZGlnaXQgaXMgYW4gaW50ZWdlciwgb2N0YWxcbiAgICAvLyBudW1iZXIsIG9yIGZsb2F0LlxuICAgIGNhc2UgNDk6Y2FzZSA1MDpjYXNlIDUxOmNhc2UgNTI6Y2FzZSA1MzpjYXNlIDU0OmNhc2UgNTU6Y2FzZSA1NjpjYXNlIDU3OlxuICAgICAgLy8gMS05XG4gICAgICByZXR1cm4gdGhpcy5yZWFkTnVtYmVyKGZhbHNlKTtcblxuICAgIC8vIFF1b3RlcyBwcm9kdWNlIHN0cmluZ3MuXG4gICAgY2FzZSAzNDpjYXNlIDM5OlxuICAgICAgLy8gJ1wiJywgXCInXCJcbiAgICAgIHJldHVybiB0aGlzLnJlYWRTdHJpbmcoY29kZSk7XG5cbiAgICAvLyBPcGVyYXRvcnMgYXJlIHBhcnNlZCBpbmxpbmUgaW4gdGlueSBzdGF0ZSBtYWNoaW5lcy4gJz0nICg2MSkgaXNcbiAgICAvLyBvZnRlbiByZWZlcnJlZCB0by4gYGZpbmlzaE9wYCBzaW1wbHkgc2tpcHMgdGhlIGFtb3VudCBvZlxuICAgIC8vIGNoYXJhY3RlcnMgaXQgaXMgZ2l2ZW4gYXMgc2Vjb25kIGFyZ3VtZW50LCBhbmQgcmV0dXJucyBhIHRva2VuXG4gICAgLy8gb2YgdGhlIHR5cGUgZ2l2ZW4gYnkgaXRzIGZpcnN0IGFyZ3VtZW50LlxuXG4gICAgY2FzZSA0NzpcbiAgICAgIC8vICcvJ1xuICAgICAgcmV0dXJuIHRoaXMucmVhZFRva2VuX3NsYXNoKCk7XG5cbiAgICBjYXNlIDM3OmNhc2UgNDI6XG4gICAgICAvLyAnJSonXG4gICAgICByZXR1cm4gdGhpcy5yZWFkVG9rZW5fbXVsdF9tb2R1bG8oY29kZSk7XG5cbiAgICBjYXNlIDEyNDpjYXNlIDM4OlxuICAgICAgLy8gJ3wmJ1xuICAgICAgcmV0dXJuIHRoaXMucmVhZFRva2VuX3BpcGVfYW1wKGNvZGUpO1xuXG4gICAgY2FzZSA5NDpcbiAgICAgIC8vICdeJ1xuICAgICAgcmV0dXJuIHRoaXMucmVhZFRva2VuX2NhcmV0KCk7XG5cbiAgICBjYXNlIDQzOmNhc2UgNDU6XG4gICAgICAvLyAnKy0nXG4gICAgICByZXR1cm4gdGhpcy5yZWFkVG9rZW5fcGx1c19taW4oY29kZSk7XG5cbiAgICBjYXNlIDYwOmNhc2UgNjI6XG4gICAgICAvLyAnPD4nXG4gICAgICByZXR1cm4gdGhpcy5yZWFkVG9rZW5fbHRfZ3QoY29kZSk7XG5cbiAgICBjYXNlIDYxOmNhc2UgMzM6XG4gICAgICAvLyAnPSEnXG4gICAgICByZXR1cm4gdGhpcy5yZWFkVG9rZW5fZXFfZXhjbChjb2RlKTtcblxuICAgIGNhc2UgMTI2OlxuICAgICAgLy8gJ34nXG4gICAgICByZXR1cm4gdGhpcy5maW5pc2hPcChfdG9rZW50eXBlLnR5cGVzLnByZWZpeCwgMSk7XG4gIH1cblxuICB0aGlzLnJhaXNlKHRoaXMucG9zLCBcIlVuZXhwZWN0ZWQgY2hhcmFjdGVyICdcIiArIGNvZGVQb2ludFRvU3RyaW5nKGNvZGUpICsgXCInXCIpO1xufTtcblxucHAuZmluaXNoT3AgPSBmdW5jdGlvbiAodHlwZSwgc2l6ZSkge1xuICB2YXIgc3RyID0gdGhpcy5pbnB1dC5zbGljZSh0aGlzLnBvcywgdGhpcy5wb3MgKyBzaXplKTtcbiAgdGhpcy5wb3MgKz0gc2l6ZTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoVG9rZW4odHlwZSwgc3RyKTtcbn07XG5cbi8vIFBhcnNlIGEgcmVndWxhciBleHByZXNzaW9uLiBTb21lIGNvbnRleHQtYXdhcmVuZXNzIGlzIG5lY2Vzc2FyeSxcbi8vIHNpbmNlIGEgJy8nIGluc2lkZSBhICdbXScgc2V0IGRvZXMgbm90IGVuZCB0aGUgZXhwcmVzc2lvbi5cblxuZnVuY3Rpb24gdHJ5Q3JlYXRlUmVnZXhwKHNyYywgZmxhZ3MsIHRocm93RXJyb3JBdCkge1xuICB0cnkge1xuICAgIHJldHVybiBuZXcgUmVnRXhwKHNyYywgZmxhZ3MpO1xuICB9IGNhdGNoIChlKSB7XG4gICAgaWYgKHRocm93RXJyb3JBdCAhPT0gdW5kZWZpbmVkKSB7XG4gICAgICBpZiAoZSBpbnN0YW5jZW9mIFN5bnRheEVycm9yKSB0aGlzLnJhaXNlKHRocm93RXJyb3JBdCwgXCJFcnJvciBwYXJzaW5nIHJlZ3VsYXIgZXhwcmVzc2lvbjogXCIgKyBlLm1lc3NhZ2UpO1xuICAgICAgdGhpcy5yYWlzZShlKTtcbiAgICB9XG4gIH1cbn1cblxudmFyIHJlZ2V4cFVuaWNvZGVTdXBwb3J0ID0gISF0cnlDcmVhdGVSZWdleHAoXCLvv79cIiwgXCJ1XCIpO1xuXG5wcC5yZWFkUmVnZXhwID0gZnVuY3Rpb24gKCkge1xuICB2YXIgX3RoaXMgPSB0aGlzO1xuXG4gIHZhciBlc2NhcGVkID0gdW5kZWZpbmVkLFxuICAgICAgaW5DbGFzcyA9IHVuZGVmaW5lZCxcbiAgICAgIHN0YXJ0ID0gdGhpcy5wb3M7XG4gIGZvciAoOzspIHtcbiAgICBpZiAodGhpcy5wb3MgPj0gdGhpcy5pbnB1dC5sZW5ndGgpIHRoaXMucmFpc2Uoc3RhcnQsIFwiVW50ZXJtaW5hdGVkIHJlZ3VsYXIgZXhwcmVzc2lvblwiKTtcbiAgICB2YXIgY2ggPSB0aGlzLmlucHV0LmNoYXJBdCh0aGlzLnBvcyk7XG4gICAgaWYgKF93aGl0ZXNwYWNlLmxpbmVCcmVhay50ZXN0KGNoKSkgdGhpcy5yYWlzZShzdGFydCwgXCJVbnRlcm1pbmF0ZWQgcmVndWxhciBleHByZXNzaW9uXCIpO1xuICAgIGlmICghZXNjYXBlZCkge1xuICAgICAgaWYgKGNoID09PSBcIltcIikgaW5DbGFzcyA9IHRydWU7ZWxzZSBpZiAoY2ggPT09IFwiXVwiICYmIGluQ2xhc3MpIGluQ2xhc3MgPSBmYWxzZTtlbHNlIGlmIChjaCA9PT0gXCIvXCIgJiYgIWluQ2xhc3MpIGJyZWFrO1xuICAgICAgZXNjYXBlZCA9IGNoID09PSBcIlxcXFxcIjtcbiAgICB9IGVsc2UgZXNjYXBlZCA9IGZhbHNlO1xuICAgICsrdGhpcy5wb3M7XG4gIH1cbiAgdmFyIGNvbnRlbnQgPSB0aGlzLmlucHV0LnNsaWNlKHN0YXJ0LCB0aGlzLnBvcyk7XG4gICsrdGhpcy5wb3M7XG4gIC8vIE5lZWQgdG8gdXNlIGByZWFkV29yZDFgIGJlY2F1c2UgJ1xcdVhYWFgnIHNlcXVlbmNlcyBhcmUgYWxsb3dlZFxuICAvLyBoZXJlIChkb24ndCBhc2spLlxuICB2YXIgbW9kcyA9IHRoaXMucmVhZFdvcmQxKCk7XG4gIHZhciB0bXAgPSBjb250ZW50O1xuICBpZiAobW9kcykge1xuICAgIHZhciB2YWxpZEZsYWdzID0gL15bZ21zaXldKiQvO1xuICAgIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNikgdmFsaWRGbGFncyA9IC9eW2dtc2l5dV0qJC87XG4gICAgaWYgKCF2YWxpZEZsYWdzLnRlc3QobW9kcykpIHRoaXMucmFpc2Uoc3RhcnQsIFwiSW52YWxpZCByZWd1bGFyIGV4cHJlc3Npb24gZmxhZ1wiKTtcbiAgICBpZiAobW9kcy5pbmRleE9mKFwidVwiKSA+PSAwICYmICFyZWdleHBVbmljb2RlU3VwcG9ydCkge1xuICAgICAgLy8gUmVwbGFjZSBlYWNoIGFzdHJhbCBzeW1ib2wgYW5kIGV2ZXJ5IFVuaWNvZGUgZXNjYXBlIHNlcXVlbmNlIHRoYXRcbiAgICAgIC8vIHBvc3NpYmx5IHJlcHJlc2VudHMgYW4gYXN0cmFsIHN5bWJvbCBvciBhIHBhaXJlZCBzdXJyb2dhdGUgd2l0aCBhXG4gICAgICAvLyBzaW5nbGUgQVNDSUkgc3ltYm9sIHRvIGF2b2lkIHRocm93aW5nIG9uIHJlZ3VsYXIgZXhwcmVzc2lvbnMgdGhhdFxuICAgICAgLy8gYXJlIG9ubHkgdmFsaWQgaW4gY29tYmluYXRpb24gd2l0aCB0aGUgYC91YCBmbGFnLlxuICAgICAgLy8gTm90ZTogcmVwbGFjaW5nIHdpdGggdGhlIEFTQ0lJIHN5bWJvbCBgeGAgbWlnaHQgY2F1c2UgZmFsc2VcbiAgICAgIC8vIG5lZ2F0aXZlcyBpbiB1bmxpa2VseSBzY2VuYXJpb3MuIEZvciBleGFtcGxlLCBgW1xcdXs2MX0tYl1gIGlzIGFcbiAgICAgIC8vIHBlcmZlY3RseSB2YWxpZCBwYXR0ZXJuIHRoYXQgaXMgZXF1aXZhbGVudCB0byBgW2EtYl1gLCBidXQgaXQgd291bGRcbiAgICAgIC8vIGJlIHJlcGxhY2VkIGJ5IGBbeC1iXWAgd2hpY2ggdGhyb3dzIGFuIGVycm9yLlxuICAgICAgdG1wID0gdG1wLnJlcGxhY2UoL1xcXFx1XFx7KFswLTlhLWZBLUZdKylcXH0vZywgZnVuY3Rpb24gKG1hdGNoLCBjb2RlLCBvZmZzZXQpIHtcbiAgICAgICAgY29kZSA9IE51bWJlcihcIjB4XCIgKyBjb2RlKTtcbiAgICAgICAgaWYgKGNvZGUgPiAweDEwRkZGRikgX3RoaXMucmFpc2Uoc3RhcnQgKyBvZmZzZXQgKyAzLCBcIkNvZGUgcG9pbnQgb3V0IG9mIGJvdW5kc1wiKTtcbiAgICAgICAgcmV0dXJuIFwieFwiO1xuICAgICAgfSk7XG4gICAgICB0bXAgPSB0bXAucmVwbGFjZSgvXFxcXHUoW2EtZkEtRjAtOV17NH0pfFtcXHVEODAwLVxcdURCRkZdW1xcdURDMDAtXFx1REZGRl0vZywgXCJ4XCIpO1xuICAgIH1cbiAgfVxuICAvLyBEZXRlY3QgaW52YWxpZCByZWd1bGFyIGV4cHJlc3Npb25zLlxuICB2YXIgdmFsdWUgPSBudWxsO1xuICAvLyBSaGlubydzIHJlZ3VsYXIgZXhwcmVzc2lvbiBwYXJzZXIgaXMgZmxha3kgYW5kIHRocm93cyB1bmNhdGNoYWJsZSBleGNlcHRpb25zLFxuICAvLyBzbyBkb24ndCBkbyBkZXRlY3Rpb24gaWYgd2UgYXJlIHJ1bm5pbmcgdW5kZXIgUmhpbm9cbiAgaWYgKCFpc1JoaW5vKSB7XG4gICAgdHJ5Q3JlYXRlUmVnZXhwKHRtcCwgdW5kZWZpbmVkLCBzdGFydCk7XG4gICAgLy8gR2V0IGEgcmVndWxhciBleHByZXNzaW9uIG9iamVjdCBmb3IgdGhpcyBwYXR0ZXJuLWZsYWcgcGFpciwgb3IgYG51bGxgIGluXG4gICAgLy8gY2FzZSB0aGUgY3VycmVudCBlbnZpcm9ubWVudCBkb2Vzbid0IHN1cHBvcnQgdGhlIGZsYWdzIGl0IHVzZXMuXG4gICAgdmFsdWUgPSB0cnlDcmVhdGVSZWdleHAoY29udGVudCwgbW9kcyk7XG4gIH1cbiAgcmV0dXJuIHRoaXMuZmluaXNoVG9rZW4oX3Rva2VudHlwZS50eXBlcy5yZWdleHAsIHsgcGF0dGVybjogY29udGVudCwgZmxhZ3M6IG1vZHMsIHZhbHVlOiB2YWx1ZSB9KTtcbn07XG5cbi8vIFJlYWQgYW4gaW50ZWdlciBpbiB0aGUgZ2l2ZW4gcmFkaXguIFJldHVybiBudWxsIGlmIHplcm8gZGlnaXRzXG4vLyB3ZXJlIHJlYWQsIHRoZSBpbnRlZ2VyIHZhbHVlIG90aGVyd2lzZS4gV2hlbiBgbGVuYCBpcyBnaXZlbiwgdGhpc1xuLy8gd2lsbCByZXR1cm4gYG51bGxgIHVubGVzcyB0aGUgaW50ZWdlciBoYXMgZXhhY3RseSBgbGVuYCBkaWdpdHMuXG5cbnBwLnJlYWRJbnQgPSBmdW5jdGlvbiAocmFkaXgsIGxlbikge1xuICB2YXIgc3RhcnQgPSB0aGlzLnBvcyxcbiAgICAgIHRvdGFsID0gMDtcbiAgZm9yICh2YXIgaSA9IDAsIGUgPSBsZW4gPT0gbnVsbCA/IEluZmluaXR5IDogbGVuOyBpIDwgZTsgKytpKSB7XG4gICAgdmFyIGNvZGUgPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MpLFxuICAgICAgICB2YWwgPSB1bmRlZmluZWQ7XG4gICAgaWYgKGNvZGUgPj0gOTcpIHZhbCA9IGNvZGUgLSA5NyArIDEwOyAvLyBhXG4gICAgZWxzZSBpZiAoY29kZSA+PSA2NSkgdmFsID0gY29kZSAtIDY1ICsgMTA7IC8vIEFcbiAgICBlbHNlIGlmIChjb2RlID49IDQ4ICYmIGNvZGUgPD0gNTcpIHZhbCA9IGNvZGUgLSA0ODsgLy8gMC05XG4gICAgZWxzZSB2YWwgPSBJbmZpbml0eTtcbiAgICBpZiAodmFsID49IHJhZGl4KSBicmVhaztcbiAgICArK3RoaXMucG9zO1xuICAgIHRvdGFsID0gdG90YWwgKiByYWRpeCArIHZhbDtcbiAgfVxuICBpZiAodGhpcy5wb3MgPT09IHN0YXJ0IHx8IGxlbiAhPSBudWxsICYmIHRoaXMucG9zIC0gc3RhcnQgIT09IGxlbikgcmV0dXJuIG51bGw7XG5cbiAgcmV0dXJuIHRvdGFsO1xufTtcblxucHAucmVhZFJhZGl4TnVtYmVyID0gZnVuY3Rpb24gKHJhZGl4KSB7XG4gIHRoaXMucG9zICs9IDI7IC8vIDB4XG4gIHZhciB2YWwgPSB0aGlzLnJlYWRJbnQocmFkaXgpO1xuICBpZiAodmFsID09IG51bGwpIHRoaXMucmFpc2UodGhpcy5zdGFydCArIDIsIFwiRXhwZWN0ZWQgbnVtYmVyIGluIHJhZGl4IFwiICsgcmFkaXgpO1xuICBpZiAoX2lkZW50aWZpZXIuaXNJZGVudGlmaWVyU3RhcnQodGhpcy5mdWxsQ2hhckNvZGVBdFBvcygpKSkgdGhpcy5yYWlzZSh0aGlzLnBvcywgXCJJZGVudGlmaWVyIGRpcmVjdGx5IGFmdGVyIG51bWJlclwiKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoVG9rZW4oX3Rva2VudHlwZS50eXBlcy5udW0sIHZhbCk7XG59O1xuXG4vLyBSZWFkIGFuIGludGVnZXIsIG9jdGFsIGludGVnZXIsIG9yIGZsb2F0aW5nLXBvaW50IG51bWJlci5cblxucHAucmVhZE51bWJlciA9IGZ1bmN0aW9uIChzdGFydHNXaXRoRG90KSB7XG4gIHZhciBzdGFydCA9IHRoaXMucG9zLFxuICAgICAgaXNGbG9hdCA9IGZhbHNlLFxuICAgICAgb2N0YWwgPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MpID09PSA0ODtcbiAgaWYgKCFzdGFydHNXaXRoRG90ICYmIHRoaXMucmVhZEludCgxMCkgPT09IG51bGwpIHRoaXMucmFpc2Uoc3RhcnQsIFwiSW52YWxpZCBudW1iZXJcIik7XG4gIHZhciBuZXh0ID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zKTtcbiAgaWYgKG5leHQgPT09IDQ2KSB7XG4gICAgLy8gJy4nXG4gICAgKyt0aGlzLnBvcztcbiAgICB0aGlzLnJlYWRJbnQoMTApO1xuICAgIGlzRmxvYXQgPSB0cnVlO1xuICAgIG5leHQgPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MpO1xuICB9XG4gIGlmIChuZXh0ID09PSA2OSB8fCBuZXh0ID09PSAxMDEpIHtcbiAgICAvLyAnZUUnXG4gICAgbmV4dCA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCgrK3RoaXMucG9zKTtcbiAgICBpZiAobmV4dCA9PT0gNDMgfHwgbmV4dCA9PT0gNDUpICsrdGhpcy5wb3M7IC8vICcrLSdcbiAgICBpZiAodGhpcy5yZWFkSW50KDEwKSA9PT0gbnVsbCkgdGhpcy5yYWlzZShzdGFydCwgXCJJbnZhbGlkIG51bWJlclwiKTtcbiAgICBpc0Zsb2F0ID0gdHJ1ZTtcbiAgfVxuICBpZiAoX2lkZW50aWZpZXIuaXNJZGVudGlmaWVyU3RhcnQodGhpcy5mdWxsQ2hhckNvZGVBdFBvcygpKSkgdGhpcy5yYWlzZSh0aGlzLnBvcywgXCJJZGVudGlmaWVyIGRpcmVjdGx5IGFmdGVyIG51bWJlclwiKTtcblxuICB2YXIgc3RyID0gdGhpcy5pbnB1dC5zbGljZShzdGFydCwgdGhpcy5wb3MpLFxuICAgICAgdmFsID0gdW5kZWZpbmVkO1xuICBpZiAoaXNGbG9hdCkgdmFsID0gcGFyc2VGbG9hdChzdHIpO2Vsc2UgaWYgKCFvY3RhbCB8fCBzdHIubGVuZ3RoID09PSAxKSB2YWwgPSBwYXJzZUludChzdHIsIDEwKTtlbHNlIGlmICgvWzg5XS8udGVzdChzdHIpIHx8IHRoaXMuc3RyaWN0KSB0aGlzLnJhaXNlKHN0YXJ0LCBcIkludmFsaWQgbnVtYmVyXCIpO2Vsc2UgdmFsID0gcGFyc2VJbnQoc3RyLCA4KTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoVG9rZW4oX3Rva2VudHlwZS50eXBlcy5udW0sIHZhbCk7XG59O1xuXG4vLyBSZWFkIGEgc3RyaW5nIHZhbHVlLCBpbnRlcnByZXRpbmcgYmFja3NsYXNoLWVzY2FwZXMuXG5cbnBwLnJlYWRDb2RlUG9pbnQgPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBjaCA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyksXG4gICAgICBjb2RlID0gdW5kZWZpbmVkO1xuXG4gIGlmIChjaCA9PT0gMTIzKSB7XG4gICAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA8IDYpIHRoaXMudW5leHBlY3RlZCgpO1xuICAgIHZhciBjb2RlUG9zID0gKyt0aGlzLnBvcztcbiAgICBjb2RlID0gdGhpcy5yZWFkSGV4Q2hhcih0aGlzLmlucHV0LmluZGV4T2YoXCJ9XCIsIHRoaXMucG9zKSAtIHRoaXMucG9zKTtcbiAgICArK3RoaXMucG9zO1xuICAgIGlmIChjb2RlID4gMHgxMEZGRkYpIHRoaXMucmFpc2UoY29kZVBvcywgXCJDb2RlIHBvaW50IG91dCBvZiBib3VuZHNcIik7XG4gIH0gZWxzZSB7XG4gICAgY29kZSA9IHRoaXMucmVhZEhleENoYXIoNCk7XG4gIH1cbiAgcmV0dXJuIGNvZGU7XG59O1xuXG5mdW5jdGlvbiBjb2RlUG9pbnRUb1N0cmluZyhjb2RlKSB7XG4gIC8vIFVURi0xNiBEZWNvZGluZ1xuICBpZiAoY29kZSA8PSAweEZGRkYpIHJldHVybiBTdHJpbmcuZnJvbUNoYXJDb2RlKGNvZGUpO1xuICBjb2RlIC09IDB4MTAwMDA7XG4gIHJldHVybiBTdHJpbmcuZnJvbUNoYXJDb2RlKChjb2RlID4+IDEwKSArIDB4RDgwMCwgKGNvZGUgJiAxMDIzKSArIDB4REMwMCk7XG59XG5cbnBwLnJlYWRTdHJpbmcgPSBmdW5jdGlvbiAocXVvdGUpIHtcbiAgdmFyIG91dCA9IFwiXCIsXG4gICAgICBjaHVua1N0YXJ0ID0gKyt0aGlzLnBvcztcbiAgZm9yICg7Oykge1xuICAgIGlmICh0aGlzLnBvcyA+PSB0aGlzLmlucHV0Lmxlbmd0aCkgdGhpcy5yYWlzZSh0aGlzLnN0YXJ0LCBcIlVudGVybWluYXRlZCBzdHJpbmcgY29uc3RhbnRcIik7XG4gICAgdmFyIGNoID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zKTtcbiAgICBpZiAoY2ggPT09IHF1b3RlKSBicmVhaztcbiAgICBpZiAoY2ggPT09IDkyKSB7XG4gICAgICAvLyAnXFwnXG4gICAgICBvdXQgKz0gdGhpcy5pbnB1dC5zbGljZShjaHVua1N0YXJ0LCB0aGlzLnBvcyk7XG4gICAgICBvdXQgKz0gdGhpcy5yZWFkRXNjYXBlZENoYXIoZmFsc2UpO1xuICAgICAgY2h1bmtTdGFydCA9IHRoaXMucG9zO1xuICAgIH0gZWxzZSB7XG4gICAgICBpZiAoX3doaXRlc3BhY2UuaXNOZXdMaW5lKGNoKSkgdGhpcy5yYWlzZSh0aGlzLnN0YXJ0LCBcIlVudGVybWluYXRlZCBzdHJpbmcgY29uc3RhbnRcIik7XG4gICAgICArK3RoaXMucG9zO1xuICAgIH1cbiAgfVxuICBvdXQgKz0gdGhpcy5pbnB1dC5zbGljZShjaHVua1N0YXJ0LCB0aGlzLnBvcysrKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoVG9rZW4oX3Rva2VudHlwZS50eXBlcy5zdHJpbmcsIG91dCk7XG59O1xuXG4vLyBSZWFkcyB0ZW1wbGF0ZSBzdHJpbmcgdG9rZW5zLlxuXG5wcC5yZWFkVG1wbFRva2VuID0gZnVuY3Rpb24gKCkge1xuICB2YXIgb3V0ID0gXCJcIixcbiAgICAgIGNodW5rU3RhcnQgPSB0aGlzLnBvcztcbiAgZm9yICg7Oykge1xuICAgIGlmICh0aGlzLnBvcyA+PSB0aGlzLmlucHV0Lmxlbmd0aCkgdGhpcy5yYWlzZSh0aGlzLnN0YXJ0LCBcIlVudGVybWluYXRlZCB0ZW1wbGF0ZVwiKTtcbiAgICB2YXIgY2ggPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MpO1xuICAgIGlmIChjaCA9PT0gOTYgfHwgY2ggPT09IDM2ICYmIHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIDEpID09PSAxMjMpIHtcbiAgICAgIC8vICdgJywgJyR7J1xuICAgICAgaWYgKHRoaXMucG9zID09PSB0aGlzLnN0YXJ0ICYmIHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy50ZW1wbGF0ZSkge1xuICAgICAgICBpZiAoY2ggPT09IDM2KSB7XG4gICAgICAgICAgdGhpcy5wb3MgKz0gMjtcbiAgICAgICAgICByZXR1cm4gdGhpcy5maW5pc2hUb2tlbihfdG9rZW50eXBlLnR5cGVzLmRvbGxhckJyYWNlTCk7XG4gICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgKyt0aGlzLnBvcztcbiAgICAgICAgICByZXR1cm4gdGhpcy5maW5pc2hUb2tlbihfdG9rZW50eXBlLnR5cGVzLmJhY2tRdW90ZSk7XG4gICAgICAgIH1cbiAgICAgIH1cbiAgICAgIG91dCArPSB0aGlzLmlucHV0LnNsaWNlKGNodW5rU3RhcnQsIHRoaXMucG9zKTtcbiAgICAgIHJldHVybiB0aGlzLmZpbmlzaFRva2VuKF90b2tlbnR5cGUudHlwZXMudGVtcGxhdGUsIG91dCk7XG4gICAgfVxuICAgIGlmIChjaCA9PT0gOTIpIHtcbiAgICAgIC8vICdcXCdcbiAgICAgIG91dCArPSB0aGlzLmlucHV0LnNsaWNlKGNodW5rU3RhcnQsIHRoaXMucG9zKTtcbiAgICAgIG91dCArPSB0aGlzLnJlYWRFc2NhcGVkQ2hhcih0cnVlKTtcbiAgICAgIGNodW5rU3RhcnQgPSB0aGlzLnBvcztcbiAgICB9IGVsc2UgaWYgKF93aGl0ZXNwYWNlLmlzTmV3TGluZShjaCkpIHtcbiAgICAgIG91dCArPSB0aGlzLmlucHV0LnNsaWNlKGNodW5rU3RhcnQsIHRoaXMucG9zKTtcbiAgICAgICsrdGhpcy5wb3M7XG4gICAgICBzd2l0Y2ggKGNoKSB7XG4gICAgICAgIGNhc2UgMTM6XG4gICAgICAgICAgaWYgKHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcykgPT09IDEwKSArK3RoaXMucG9zO1xuICAgICAgICBjYXNlIDEwOlxuICAgICAgICAgIG91dCArPSBcIlxcblwiO1xuICAgICAgICAgIGJyZWFrO1xuICAgICAgICBkZWZhdWx0OlxuICAgICAgICAgIG91dCArPSBTdHJpbmcuZnJvbUNoYXJDb2RlKGNoKTtcbiAgICAgICAgICBicmVhaztcbiAgICAgIH1cbiAgICAgIGlmICh0aGlzLm9wdGlvbnMubG9jYXRpb25zKSB7XG4gICAgICAgICsrdGhpcy5jdXJMaW5lO1xuICAgICAgICB0aGlzLmxpbmVTdGFydCA9IHRoaXMucG9zO1xuICAgICAgfVxuICAgICAgY2h1bmtTdGFydCA9IHRoaXMucG9zO1xuICAgIH0gZWxzZSB7XG4gICAgICArK3RoaXMucG9zO1xuICAgIH1cbiAgfVxufTtcblxuLy8gVXNlZCB0byByZWFkIGVzY2FwZWQgY2hhcmFjdGVyc1xuXG5wcC5yZWFkRXNjYXBlZENoYXIgPSBmdW5jdGlvbiAoaW5UZW1wbGF0ZSkge1xuICB2YXIgY2ggPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQoKyt0aGlzLnBvcyk7XG4gICsrdGhpcy5wb3M7XG4gIHN3aXRjaCAoY2gpIHtcbiAgICBjYXNlIDExMDpcbiAgICAgIHJldHVybiBcIlxcblwiOyAvLyAnbicgLT4gJ1xcbidcbiAgICBjYXNlIDExNDpcbiAgICAgIHJldHVybiBcIlxcclwiOyAvLyAncicgLT4gJ1xccidcbiAgICBjYXNlIDEyMDpcbiAgICAgIHJldHVybiBTdHJpbmcuZnJvbUNoYXJDb2RlKHRoaXMucmVhZEhleENoYXIoMikpOyAvLyAneCdcbiAgICBjYXNlIDExNzpcbiAgICAgIHJldHVybiBjb2RlUG9pbnRUb1N0cmluZyh0aGlzLnJlYWRDb2RlUG9pbnQoKSk7IC8vICd1J1xuICAgIGNhc2UgMTE2OlxuICAgICAgcmV0dXJuIFwiXFx0XCI7IC8vICd0JyAtPiAnXFx0J1xuICAgIGNhc2UgOTg6XG4gICAgICByZXR1cm4gXCJcXGJcIjsgLy8gJ2InIC0+ICdcXGInXG4gICAgY2FzZSAxMTg6XG4gICAgICByZXR1cm4gXCJcXHUwMDBiXCI7IC8vICd2JyAtPiAnXFx1MDAwYidcbiAgICBjYXNlIDEwMjpcbiAgICAgIHJldHVybiBcIlxcZlwiOyAvLyAnZicgLT4gJ1xcZidcbiAgICBjYXNlIDEzOlxuICAgICAgaWYgKHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcykgPT09IDEwKSArK3RoaXMucG9zOyAvLyAnXFxyXFxuJ1xuICAgIGNhc2UgMTA6XG4gICAgICAvLyAnIFxcbidcbiAgICAgIGlmICh0aGlzLm9wdGlvbnMubG9jYXRpb25zKSB7XG4gICAgICAgIHRoaXMubGluZVN0YXJ0ID0gdGhpcy5wb3M7Kyt0aGlzLmN1ckxpbmU7XG4gICAgICB9XG4gICAgICByZXR1cm4gXCJcIjtcbiAgICBkZWZhdWx0OlxuICAgICAgaWYgKGNoID49IDQ4ICYmIGNoIDw9IDU1KSB7XG4gICAgICAgIHZhciBvY3RhbFN0ciA9IHRoaXMuaW5wdXQuc3Vic3RyKHRoaXMucG9zIC0gMSwgMykubWF0Y2goL15bMC03XSsvKVswXTtcbiAgICAgICAgdmFyIG9jdGFsID0gcGFyc2VJbnQob2N0YWxTdHIsIDgpO1xuICAgICAgICBpZiAob2N0YWwgPiAyNTUpIHtcbiAgICAgICAgICBvY3RhbFN0ciA9IG9jdGFsU3RyLnNsaWNlKDAsIC0xKTtcbiAgICAgICAgICBvY3RhbCA9IHBhcnNlSW50KG9jdGFsU3RyLCA4KTtcbiAgICAgICAgfVxuICAgICAgICBpZiAob2N0YWwgPiAwICYmICh0aGlzLnN0cmljdCB8fCBpblRlbXBsYXRlKSkge1xuICAgICAgICAgIHRoaXMucmFpc2UodGhpcy5wb3MgLSAyLCBcIk9jdGFsIGxpdGVyYWwgaW4gc3RyaWN0IG1vZGVcIik7XG4gICAgICAgIH1cbiAgICAgICAgdGhpcy5wb3MgKz0gb2N0YWxTdHIubGVuZ3RoIC0gMTtcbiAgICAgICAgcmV0dXJuIFN0cmluZy5mcm9tQ2hhckNvZGUob2N0YWwpO1xuICAgICAgfVxuICAgICAgcmV0dXJuIFN0cmluZy5mcm9tQ2hhckNvZGUoY2gpO1xuICB9XG59O1xuXG4vLyBVc2VkIHRvIHJlYWQgY2hhcmFjdGVyIGVzY2FwZSBzZXF1ZW5jZXMgKCdcXHgnLCAnXFx1JywgJ1xcVScpLlxuXG5wcC5yZWFkSGV4Q2hhciA9IGZ1bmN0aW9uIChsZW4pIHtcbiAgdmFyIGNvZGVQb3MgPSB0aGlzLnBvcztcbiAgdmFyIG4gPSB0aGlzLnJlYWRJbnQoMTYsIGxlbik7XG4gIGlmIChuID09PSBudWxsKSB0aGlzLnJhaXNlKGNvZGVQb3MsIFwiQmFkIGNoYXJhY3RlciBlc2NhcGUgc2VxdWVuY2VcIik7XG4gIHJldHVybiBuO1xufTtcblxuLy8gUmVhZCBhbiBpZGVudGlmaWVyLCBhbmQgcmV0dXJuIGl0IGFzIGEgc3RyaW5nLiBTZXRzIGB0aGlzLmNvbnRhaW5zRXNjYFxuLy8gdG8gd2hldGhlciB0aGUgd29yZCBjb250YWluZWQgYSAnXFx1JyBlc2NhcGUuXG4vL1xuLy8gSW5jcmVtZW50YWxseSBhZGRzIG9ubHkgZXNjYXBlZCBjaGFycywgYWRkaW5nIG90aGVyIGNodW5rcyBhcy1pc1xuLy8gYXMgYSBtaWNyby1vcHRpbWl6YXRpb24uXG5cbnBwLnJlYWRXb3JkMSA9IGZ1bmN0aW9uICgpIHtcbiAgdGhpcy5jb250YWluc0VzYyA9IGZhbHNlO1xuICB2YXIgd29yZCA9IFwiXCIsXG4gICAgICBmaXJzdCA9IHRydWUsXG4gICAgICBjaHVua1N0YXJ0ID0gdGhpcy5wb3M7XG4gIHZhciBhc3RyYWwgPSB0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNjtcbiAgd2hpbGUgKHRoaXMucG9zIDwgdGhpcy5pbnB1dC5sZW5ndGgpIHtcbiAgICB2YXIgY2ggPSB0aGlzLmZ1bGxDaGFyQ29kZUF0UG9zKCk7XG4gICAgaWYgKF9pZGVudGlmaWVyLmlzSWRlbnRpZmllckNoYXIoY2gsIGFzdHJhbCkpIHtcbiAgICAgIHRoaXMucG9zICs9IGNoIDw9IDB4ZmZmZiA/IDEgOiAyO1xuICAgIH0gZWxzZSBpZiAoY2ggPT09IDkyKSB7XG4gICAgICAvLyBcIlxcXCJcbiAgICAgIHRoaXMuY29udGFpbnNFc2MgPSB0cnVlO1xuICAgICAgd29yZCArPSB0aGlzLmlucHV0LnNsaWNlKGNodW5rU3RhcnQsIHRoaXMucG9zKTtcbiAgICAgIHZhciBlc2NTdGFydCA9IHRoaXMucG9zO1xuICAgICAgaWYgKHRoaXMuaW5wdXQuY2hhckNvZGVBdCgrK3RoaXMucG9zKSAhPSAxMTcpIC8vIFwidVwiXG4gICAgICAgIHRoaXMucmFpc2UodGhpcy5wb3MsIFwiRXhwZWN0aW5nIFVuaWNvZGUgZXNjYXBlIHNlcXVlbmNlIFxcXFx1WFhYWFwiKTtcbiAgICAgICsrdGhpcy5wb3M7XG4gICAgICB2YXIgZXNjID0gdGhpcy5yZWFkQ29kZVBvaW50KCk7XG4gICAgICBpZiAoIShmaXJzdCA/IF9pZGVudGlmaWVyLmlzSWRlbnRpZmllclN0YXJ0IDogX2lkZW50aWZpZXIuaXNJZGVudGlmaWVyQ2hhcikoZXNjLCBhc3RyYWwpKSB0aGlzLnJhaXNlKGVzY1N0YXJ0LCBcIkludmFsaWQgVW5pY29kZSBlc2NhcGVcIik7XG4gICAgICB3b3JkICs9IGNvZGVQb2ludFRvU3RyaW5nKGVzYyk7XG4gICAgICBjaHVua1N0YXJ0ID0gdGhpcy5wb3M7XG4gICAgfSBlbHNlIHtcbiAgICAgIGJyZWFrO1xuICAgIH1cbiAgICBmaXJzdCA9IGZhbHNlO1xuICB9XG4gIHJldHVybiB3b3JkICsgdGhpcy5pbnB1dC5zbGljZShjaHVua1N0YXJ0LCB0aGlzLnBvcyk7XG59O1xuXG4vLyBSZWFkIGFuIGlkZW50aWZpZXIgb3Iga2V5d29yZCB0b2tlbi4gV2lsbCBjaGVjayBmb3IgcmVzZXJ2ZWRcbi8vIHdvcmRzIHdoZW4gbmVjZXNzYXJ5LlxuXG5wcC5yZWFkV29yZCA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIHdvcmQgPSB0aGlzLnJlYWRXb3JkMSgpO1xuICB2YXIgdHlwZSA9IF90b2tlbnR5cGUudHlwZXMubmFtZTtcbiAgaWYgKCh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNiB8fCAhdGhpcy5jb250YWluc0VzYykgJiYgdGhpcy5pc0tleXdvcmQod29yZCkpIHR5cGUgPSBfdG9rZW50eXBlLmtleXdvcmRzW3dvcmRdO1xuICByZXR1cm4gdGhpcy5maW5pc2hUb2tlbih0eXBlLCB3b3JkKTtcbn07XG5cbn0se1wiLi9pZGVudGlmaWVyXCI6MixcIi4vbG9jdXRpbFwiOjUsXCIuL3N0YXRlXCI6MTAsXCIuL3Rva2VudHlwZVwiOjE0LFwiLi93aGl0ZXNwYWNlXCI6MTZ9XSwxNDpbZnVuY3Rpb24oX2RlcmVxXyxtb2R1bGUsZXhwb3J0cyl7XG4vLyAjIyBUb2tlbiB0eXBlc1xuXG4vLyBUaGUgYXNzaWdubWVudCBvZiBmaW5lLWdyYWluZWQsIGluZm9ybWF0aW9uLWNhcnJ5aW5nIHR5cGUgb2JqZWN0c1xuLy8gYWxsb3dzIHRoZSB0b2tlbml6ZXIgdG8gc3RvcmUgdGhlIGluZm9ybWF0aW9uIGl0IGhhcyBhYm91dCBhXG4vLyB0b2tlbiBpbiBhIHdheSB0aGF0IGlzIHZlcnkgY2hlYXAgZm9yIHRoZSBwYXJzZXIgdG8gbG9vayB1cC5cblxuLy8gQWxsIHRva2VuIHR5cGUgdmFyaWFibGVzIHN0YXJ0IHdpdGggYW4gdW5kZXJzY29yZSwgdG8gbWFrZSB0aGVtXG4vLyBlYXN5IHRvIHJlY29nbml6ZS5cblxuLy8gVGhlIGBiZWZvcmVFeHByYCBwcm9wZXJ0eSBpcyB1c2VkIHRvIGRpc2FtYmlndWF0ZSBiZXR3ZWVuIHJlZ3VsYXJcbi8vIGV4cHJlc3Npb25zIGFuZCBkaXZpc2lvbnMuIEl0IGlzIHNldCBvbiBhbGwgdG9rZW4gdHlwZXMgdGhhdCBjYW5cbi8vIGJlIGZvbGxvd2VkIGJ5IGFuIGV4cHJlc3Npb24gKHRodXMsIGEgc2xhc2ggYWZ0ZXIgdGhlbSB3b3VsZCBiZSBhXG4vLyByZWd1bGFyIGV4cHJlc3Npb24pLlxuLy9cbi8vIGBpc0xvb3BgIG1hcmtzIGEga2V5d29yZCBhcyBzdGFydGluZyBhIGxvb3AsIHdoaWNoIGlzIGltcG9ydGFudFxuLy8gdG8ga25vdyB3aGVuIHBhcnNpbmcgYSBsYWJlbCwgaW4gb3JkZXIgdG8gYWxsb3cgb3IgZGlzYWxsb3dcbi8vIGNvbnRpbnVlIGp1bXBzIHRvIHRoYXQgbGFiZWwuXG5cblwidXNlIHN0cmljdFwiO1xuXG5leHBvcnRzLl9fZXNNb2R1bGUgPSB0cnVlO1xuXG5mdW5jdGlvbiBfY2xhc3NDYWxsQ2hlY2soaW5zdGFuY2UsIENvbnN0cnVjdG9yKSB7IGlmICghKGluc3RhbmNlIGluc3RhbmNlb2YgQ29uc3RydWN0b3IpKSB7IHRocm93IG5ldyBUeXBlRXJyb3IoXCJDYW5ub3QgY2FsbCBhIGNsYXNzIGFzIGEgZnVuY3Rpb25cIik7IH0gfVxuXG52YXIgVG9rZW5UeXBlID0gZnVuY3Rpb24gVG9rZW5UeXBlKGxhYmVsKSB7XG4gIHZhciBjb25mID0gYXJndW1lbnRzLmxlbmd0aCA8PSAxIHx8IGFyZ3VtZW50c1sxXSA9PT0gdW5kZWZpbmVkID8ge30gOiBhcmd1bWVudHNbMV07XG5cbiAgX2NsYXNzQ2FsbENoZWNrKHRoaXMsIFRva2VuVHlwZSk7XG5cbiAgdGhpcy5sYWJlbCA9IGxhYmVsO1xuICB0aGlzLmtleXdvcmQgPSBjb25mLmtleXdvcmQ7XG4gIHRoaXMuYmVmb3JlRXhwciA9ICEhY29uZi5iZWZvcmVFeHByO1xuICB0aGlzLnN0YXJ0c0V4cHIgPSAhIWNvbmYuc3RhcnRzRXhwcjtcbiAgdGhpcy5pc0xvb3AgPSAhIWNvbmYuaXNMb29wO1xuICB0aGlzLmlzQXNzaWduID0gISFjb25mLmlzQXNzaWduO1xuICB0aGlzLnByZWZpeCA9ICEhY29uZi5wcmVmaXg7XG4gIHRoaXMucG9zdGZpeCA9ICEhY29uZi5wb3N0Zml4O1xuICB0aGlzLmJpbm9wID0gY29uZi5iaW5vcCB8fCBudWxsO1xuICB0aGlzLnVwZGF0ZUNvbnRleHQgPSBudWxsO1xufTtcblxuZXhwb3J0cy5Ub2tlblR5cGUgPSBUb2tlblR5cGU7XG5cbmZ1bmN0aW9uIGJpbm9wKG5hbWUsIHByZWMpIHtcbiAgcmV0dXJuIG5ldyBUb2tlblR5cGUobmFtZSwgeyBiZWZvcmVFeHByOiB0cnVlLCBiaW5vcDogcHJlYyB9KTtcbn1cbnZhciBiZWZvcmVFeHByID0geyBiZWZvcmVFeHByOiB0cnVlIH0sXG4gICAgc3RhcnRzRXhwciA9IHsgc3RhcnRzRXhwcjogdHJ1ZSB9O1xuXG52YXIgdHlwZXMgPSB7XG4gIG51bTogbmV3IFRva2VuVHlwZShcIm51bVwiLCBzdGFydHNFeHByKSxcbiAgcmVnZXhwOiBuZXcgVG9rZW5UeXBlKFwicmVnZXhwXCIsIHN0YXJ0c0V4cHIpLFxuICBzdHJpbmc6IG5ldyBUb2tlblR5cGUoXCJzdHJpbmdcIiwgc3RhcnRzRXhwciksXG4gIG5hbWU6IG5ldyBUb2tlblR5cGUoXCJuYW1lXCIsIHN0YXJ0c0V4cHIpLFxuICBlb2Y6IG5ldyBUb2tlblR5cGUoXCJlb2ZcIiksXG5cbiAgLy8gUHVuY3R1YXRpb24gdG9rZW4gdHlwZXMuXG4gIGJyYWNrZXRMOiBuZXcgVG9rZW5UeXBlKFwiW1wiLCB7IGJlZm9yZUV4cHI6IHRydWUsIHN0YXJ0c0V4cHI6IHRydWUgfSksXG4gIGJyYWNrZXRSOiBuZXcgVG9rZW5UeXBlKFwiXVwiKSxcbiAgYnJhY2VMOiBuZXcgVG9rZW5UeXBlKFwie1wiLCB7IGJlZm9yZUV4cHI6IHRydWUsIHN0YXJ0c0V4cHI6IHRydWUgfSksXG4gIGJyYWNlUjogbmV3IFRva2VuVHlwZShcIn1cIiksXG4gIHBhcmVuTDogbmV3IFRva2VuVHlwZShcIihcIiwgeyBiZWZvcmVFeHByOiB0cnVlLCBzdGFydHNFeHByOiB0cnVlIH0pLFxuICBwYXJlblI6IG5ldyBUb2tlblR5cGUoXCIpXCIpLFxuICBjb21tYTogbmV3IFRva2VuVHlwZShcIixcIiwgYmVmb3JlRXhwciksXG4gIHNlbWk6IG5ldyBUb2tlblR5cGUoXCI7XCIsIGJlZm9yZUV4cHIpLFxuICBjb2xvbjogbmV3IFRva2VuVHlwZShcIjpcIiwgYmVmb3JlRXhwciksXG4gIGRvdDogbmV3IFRva2VuVHlwZShcIi5cIiksXG4gIHF1ZXN0aW9uOiBuZXcgVG9rZW5UeXBlKFwiP1wiLCBiZWZvcmVFeHByKSxcbiAgYXJyb3c6IG5ldyBUb2tlblR5cGUoXCI9PlwiLCBiZWZvcmVFeHByKSxcbiAgdGVtcGxhdGU6IG5ldyBUb2tlblR5cGUoXCJ0ZW1wbGF0ZVwiKSxcbiAgZWxsaXBzaXM6IG5ldyBUb2tlblR5cGUoXCIuLi5cIiwgYmVmb3JlRXhwciksXG4gIGJhY2tRdW90ZTogbmV3IFRva2VuVHlwZShcImBcIiwgc3RhcnRzRXhwciksXG4gIGRvbGxhckJyYWNlTDogbmV3IFRva2VuVHlwZShcIiR7XCIsIHsgYmVmb3JlRXhwcjogdHJ1ZSwgc3RhcnRzRXhwcjogdHJ1ZSB9KSxcblxuICAvLyBPcGVyYXRvcnMuIFRoZXNlIGNhcnJ5IHNldmVyYWwga2luZHMgb2YgcHJvcGVydGllcyB0byBoZWxwIHRoZVxuICAvLyBwYXJzZXIgdXNlIHRoZW0gcHJvcGVybHkgKHRoZSBwcmVzZW5jZSBvZiB0aGVzZSBwcm9wZXJ0aWVzIGlzXG4gIC8vIHdoYXQgY2F0ZWdvcml6ZXMgdGhlbSBhcyBvcGVyYXRvcnMpLlxuICAvL1xuICAvLyBgYmlub3BgLCB3aGVuIHByZXNlbnQsIHNwZWNpZmllcyB0aGF0IHRoaXMgb3BlcmF0b3IgaXMgYSBiaW5hcnlcbiAgLy8gb3BlcmF0b3IsIGFuZCB3aWxsIHJlZmVyIHRvIGl0cyBwcmVjZWRlbmNlLlxuICAvL1xuICAvLyBgcHJlZml4YCBhbmQgYHBvc3RmaXhgIG1hcmsgdGhlIG9wZXJhdG9yIGFzIGEgcHJlZml4IG9yIHBvc3RmaXhcbiAgLy8gdW5hcnkgb3BlcmF0b3IuXG4gIC8vXG4gIC8vIGBpc0Fzc2lnbmAgbWFya3MgYWxsIG9mIGA9YCwgYCs9YCwgYC09YCBldGNldGVyYSwgd2hpY2ggYWN0IGFzXG4gIC8vIGJpbmFyeSBvcGVyYXRvcnMgd2l0aCBhIHZlcnkgbG93IHByZWNlZGVuY2UsIHRoYXQgc2hvdWxkIHJlc3VsdFxuICAvLyBpbiBBc3NpZ25tZW50RXhwcmVzc2lvbiBub2Rlcy5cblxuICBlcTogbmV3IFRva2VuVHlwZShcIj1cIiwgeyBiZWZvcmVFeHByOiB0cnVlLCBpc0Fzc2lnbjogdHJ1ZSB9KSxcbiAgYXNzaWduOiBuZXcgVG9rZW5UeXBlKFwiXz1cIiwgeyBiZWZvcmVFeHByOiB0cnVlLCBpc0Fzc2lnbjogdHJ1ZSB9KSxcbiAgaW5jRGVjOiBuZXcgVG9rZW5UeXBlKFwiKysvLS1cIiwgeyBwcmVmaXg6IHRydWUsIHBvc3RmaXg6IHRydWUsIHN0YXJ0c0V4cHI6IHRydWUgfSksXG4gIHByZWZpeDogbmV3IFRva2VuVHlwZShcInByZWZpeFwiLCB7IGJlZm9yZUV4cHI6IHRydWUsIHByZWZpeDogdHJ1ZSwgc3RhcnRzRXhwcjogdHJ1ZSB9KSxcbiAgbG9naWNhbE9SOiBiaW5vcChcInx8XCIsIDEpLFxuICBsb2dpY2FsQU5EOiBiaW5vcChcIiYmXCIsIDIpLFxuICBiaXR3aXNlT1I6IGJpbm9wKFwifFwiLCAzKSxcbiAgYml0d2lzZVhPUjogYmlub3AoXCJeXCIsIDQpLFxuICBiaXR3aXNlQU5EOiBiaW5vcChcIiZcIiwgNSksXG4gIGVxdWFsaXR5OiBiaW5vcChcIj09LyE9XCIsIDYpLFxuICByZWxhdGlvbmFsOiBiaW5vcChcIjwvPlwiLCA3KSxcbiAgYml0U2hpZnQ6IGJpbm9wKFwiPDwvPj5cIiwgOCksXG4gIHBsdXNNaW46IG5ldyBUb2tlblR5cGUoXCIrLy1cIiwgeyBiZWZvcmVFeHByOiB0cnVlLCBiaW5vcDogOSwgcHJlZml4OiB0cnVlLCBzdGFydHNFeHByOiB0cnVlIH0pLFxuICBtb2R1bG86IGJpbm9wKFwiJVwiLCAxMCksXG4gIHN0YXI6IGJpbm9wKFwiKlwiLCAxMCksXG4gIHNsYXNoOiBiaW5vcChcIi9cIiwgMTApXG59O1xuXG5leHBvcnRzLnR5cGVzID0gdHlwZXM7XG4vLyBNYXAga2V5d29yZCBuYW1lcyB0byB0b2tlbiB0eXBlcy5cblxudmFyIGtleXdvcmRzID0ge307XG5cbmV4cG9ydHMua2V5d29yZHMgPSBrZXl3b3Jkcztcbi8vIFN1Y2NpbmN0IGRlZmluaXRpb25zIG9mIGtleXdvcmQgdG9rZW4gdHlwZXNcbmZ1bmN0aW9uIGt3KG5hbWUpIHtcbiAgdmFyIG9wdGlvbnMgPSBhcmd1bWVudHMubGVuZ3RoIDw9IDEgfHwgYXJndW1lbnRzWzFdID09PSB1bmRlZmluZWQgPyB7fSA6IGFyZ3VtZW50c1sxXTtcblxuICBvcHRpb25zLmtleXdvcmQgPSBuYW1lO1xuICBrZXl3b3Jkc1tuYW1lXSA9IHR5cGVzW1wiX1wiICsgbmFtZV0gPSBuZXcgVG9rZW5UeXBlKG5hbWUsIG9wdGlvbnMpO1xufVxuXG5rdyhcImJyZWFrXCIpO1xua3coXCJjYXNlXCIsIGJlZm9yZUV4cHIpO1xua3coXCJjYXRjaFwiKTtcbmt3KFwiY29udGludWVcIik7XG5rdyhcImRlYnVnZ2VyXCIpO1xua3coXCJkZWZhdWx0XCIsIGJlZm9yZUV4cHIpO1xua3coXCJkb1wiLCB7IGlzTG9vcDogdHJ1ZSB9KTtcbmt3KFwiZWxzZVwiLCBiZWZvcmVFeHByKTtcbmt3KFwiZmluYWxseVwiKTtcbmt3KFwiZm9yXCIsIHsgaXNMb29wOiB0cnVlIH0pO1xua3coXCJmdW5jdGlvblwiLCBzdGFydHNFeHByKTtcbmt3KFwiaWZcIik7XG5rdyhcInJldHVyblwiLCBiZWZvcmVFeHByKTtcbmt3KFwic3dpdGNoXCIpO1xua3coXCJ0aHJvd1wiLCBiZWZvcmVFeHByKTtcbmt3KFwidHJ5XCIpO1xua3coXCJ2YXJcIik7XG5rdyhcImxldFwiKTtcbmt3KFwiY29uc3RcIik7XG5rdyhcIndoaWxlXCIsIHsgaXNMb29wOiB0cnVlIH0pO1xua3coXCJ3aXRoXCIpO1xua3coXCJuZXdcIiwgeyBiZWZvcmVFeHByOiB0cnVlLCBzdGFydHNFeHByOiB0cnVlIH0pO1xua3coXCJ0aGlzXCIsIHN0YXJ0c0V4cHIpO1xua3coXCJzdXBlclwiLCBzdGFydHNFeHByKTtcbmt3KFwiY2xhc3NcIik7XG5rdyhcImV4dGVuZHNcIiwgYmVmb3JlRXhwcik7XG5rdyhcImV4cG9ydFwiKTtcbmt3KFwiaW1wb3J0XCIpO1xua3coXCJ5aWVsZFwiLCB7IGJlZm9yZUV4cHI6IHRydWUsIHN0YXJ0c0V4cHI6IHRydWUgfSk7XG5rdyhcIm51bGxcIiwgc3RhcnRzRXhwcik7XG5rdyhcInRydWVcIiwgc3RhcnRzRXhwcik7XG5rdyhcImZhbHNlXCIsIHN0YXJ0c0V4cHIpO1xua3coXCJpblwiLCB7IGJlZm9yZUV4cHI6IHRydWUsIGJpbm9wOiA3IH0pO1xua3coXCJpbnN0YW5jZW9mXCIsIHsgYmVmb3JlRXhwcjogdHJ1ZSwgYmlub3A6IDcgfSk7XG5rdyhcInR5cGVvZlwiLCB7IGJlZm9yZUV4cHI6IHRydWUsIHByZWZpeDogdHJ1ZSwgc3RhcnRzRXhwcjogdHJ1ZSB9KTtcbmt3KFwidm9pZFwiLCB7IGJlZm9yZUV4cHI6IHRydWUsIHByZWZpeDogdHJ1ZSwgc3RhcnRzRXhwcjogdHJ1ZSB9KTtcbmt3KFwiZGVsZXRlXCIsIHsgYmVmb3JlRXhwcjogdHJ1ZSwgcHJlZml4OiB0cnVlLCBzdGFydHNFeHByOiB0cnVlIH0pO1xuXG59LHt9XSwxNTpbZnVuY3Rpb24oX2RlcmVxXyxtb2R1bGUsZXhwb3J0cyl7XG5cInVzZSBzdHJpY3RcIjtcblxuZXhwb3J0cy5fX2VzTW9kdWxlID0gdHJ1ZTtcbmV4cG9ydHMuaXNBcnJheSA9IGlzQXJyYXk7XG5leHBvcnRzLmhhcyA9IGhhcztcblxuZnVuY3Rpb24gaXNBcnJheShvYmopIHtcbiAgcmV0dXJuIE9iamVjdC5wcm90b3R5cGUudG9TdHJpbmcuY2FsbChvYmopID09PSBcIltvYmplY3QgQXJyYXldXCI7XG59XG5cbi8vIENoZWNrcyBpZiBhbiBvYmplY3QgaGFzIGEgcHJvcGVydHkuXG5cbmZ1bmN0aW9uIGhhcyhvYmosIHByb3BOYW1lKSB7XG4gIHJldHVybiBPYmplY3QucHJvdG90eXBlLmhhc093blByb3BlcnR5LmNhbGwob2JqLCBwcm9wTmFtZSk7XG59XG5cbn0se31dLDE2OltmdW5jdGlvbihfZGVyZXFfLG1vZHVsZSxleHBvcnRzKXtcbi8vIE1hdGNoZXMgYSB3aG9sZSBsaW5lIGJyZWFrICh3aGVyZSBDUkxGIGlzIGNvbnNpZGVyZWQgYSBzaW5nbGVcbi8vIGxpbmUgYnJlYWspLiBVc2VkIHRvIGNvdW50IGxpbmVzLlxuXG5cInVzZSBzdHJpY3RcIjtcblxuZXhwb3J0cy5fX2VzTW9kdWxlID0gdHJ1ZTtcbmV4cG9ydHMuaXNOZXdMaW5lID0gaXNOZXdMaW5lO1xudmFyIGxpbmVCcmVhayA9IC9cXHJcXG4/fFxcbnxcXHUyMDI4fFxcdTIwMjkvO1xuZXhwb3J0cy5saW5lQnJlYWsgPSBsaW5lQnJlYWs7XG52YXIgbGluZUJyZWFrRyA9IG5ldyBSZWdFeHAobGluZUJyZWFrLnNvdXJjZSwgXCJnXCIpO1xuXG5leHBvcnRzLmxpbmVCcmVha0cgPSBsaW5lQnJlYWtHO1xuXG5mdW5jdGlvbiBpc05ld0xpbmUoY29kZSkge1xuICByZXR1cm4gY29kZSA9PT0gMTAgfHwgY29kZSA9PT0gMTMgfHwgY29kZSA9PT0gMHgyMDI4IHx8IGNvZGUgPT0gMHgyMDI5O1xufVxuXG52YXIgbm9uQVNDSUl3aGl0ZXNwYWNlID0gL1tcXHUxNjgwXFx1MTgwZVxcdTIwMDAtXFx1MjAwYVxcdTIwMmZcXHUyMDVmXFx1MzAwMFxcdWZlZmZdLztcbmV4cG9ydHMubm9uQVNDSUl3aGl0ZXNwYWNlID0gbm9uQVNDSUl3aGl0ZXNwYWNlO1xuXG59LHt9XX0se30sWzNdKSgzKVxufSk7IiwiKGZ1bmN0aW9uKGYpe2lmKHR5cGVvZiBleHBvcnRzPT09XCJvYmplY3RcIiYmdHlwZW9mIG1vZHVsZSE9PVwidW5kZWZpbmVkXCIpe21vZHVsZS5leHBvcnRzPWYoKX1lbHNlIGlmKHR5cGVvZiBkZWZpbmU9PT1cImZ1bmN0aW9uXCImJmRlZmluZS5hbWQpe2RlZmluZShbXSxmKX1lbHNle3ZhciBnO2lmKHR5cGVvZiB3aW5kb3chPT1cInVuZGVmaW5lZFwiKXtnPXdpbmRvd31lbHNlIGlmKHR5cGVvZiBnbG9iYWwhPT1cInVuZGVmaW5lZFwiKXtnPWdsb2JhbH1lbHNlIGlmKHR5cGVvZiBzZWxmIT09XCJ1bmRlZmluZWRcIil7Zz1zZWxmfWVsc2V7Zz10aGlzfShnLmFjb3JuIHx8IChnLmFjb3JuID0ge30pKS5sb29zZSA9IGYoKX19KShmdW5jdGlvbigpe3ZhciBkZWZpbmUsbW9kdWxlLGV4cG9ydHM7cmV0dXJuIChmdW5jdGlvbiBlKHQsbixyKXtmdW5jdGlvbiBzKG8sdSl7aWYoIW5bb10pe2lmKCF0W29dKXt2YXIgYT10eXBlb2YgcmVxdWlyZT09XCJmdW5jdGlvblwiJiZyZXF1aXJlO2lmKCF1JiZhKXJldHVybiBhKG8sITApO2lmKGkpcmV0dXJuIGkobywhMCk7dmFyIGY9bmV3IEVycm9yKFwiQ2Fubm90IGZpbmQgbW9kdWxlICdcIitvK1wiJ1wiKTt0aHJvdyBmLmNvZGU9XCJNT0RVTEVfTk9UX0ZPVU5EXCIsZn12YXIgbD1uW29dPXtleHBvcnRzOnt9fTt0W29dWzBdLmNhbGwobC5leHBvcnRzLGZ1bmN0aW9uKGUpe3ZhciBuPXRbb11bMV1bZV07cmV0dXJuIHMobj9uOmUpfSxsLGwuZXhwb3J0cyxlLHQsbixyKX1yZXR1cm4gbltvXS5leHBvcnRzfXZhciBpPXR5cGVvZiByZXF1aXJlPT1cImZ1bmN0aW9uXCImJnJlcXVpcmU7Zm9yKHZhciBvPTA7bzxyLmxlbmd0aDtvKyspcyhyW29dKTtyZXR1cm4gc30pKHsxOltmdW5jdGlvbihfZGVyZXFfLG1vZHVsZSxleHBvcnRzKXtcblwidXNlIHN0cmljdFwiO1xuXG5tb2R1bGUuZXhwb3J0cyA9IHR5cGVvZiBhY29ybiAhPSAndW5kZWZpbmVkJyA/IGFjb3JuIDogcmVxdWlyZShcIi4vYWNvcm5cIik7XG5cbn0se31dLDI6W2Z1bmN0aW9uKF9kZXJlcV8sbW9kdWxlLGV4cG9ydHMpe1xuXCJ1c2Ugc3RyaWN0XCI7XG5cbnZhciBfc3RhdGUgPSBfZGVyZXFfKFwiLi9zdGF0ZVwiKTtcblxudmFyIF9wYXJzZXV0aWwgPSBfZGVyZXFfKFwiLi9wYXJzZXV0aWxcIik7XG5cbnZhciBfID0gX2RlcmVxXyhcIi4uXCIpO1xuXG52YXIgbHAgPSBfc3RhdGUuTG9vc2VQYXJzZXIucHJvdG90eXBlO1xuXG5scC5jaGVja0xWYWwgPSBmdW5jdGlvbiAoZXhwciwgYmluZGluZykge1xuICBpZiAoIWV4cHIpIHJldHVybiBleHByO1xuICBzd2l0Y2ggKGV4cHIudHlwZSkge1xuICAgIGNhc2UgXCJJZGVudGlmaWVyXCI6XG4gICAgICByZXR1cm4gZXhwcjtcblxuICAgIGNhc2UgXCJNZW1iZXJFeHByZXNzaW9uXCI6XG4gICAgICByZXR1cm4gYmluZGluZyA/IHRoaXMuZHVtbXlJZGVudCgpIDogZXhwcjtcblxuICAgIGNhc2UgXCJQYXJlbnRoZXNpemVkRXhwcmVzc2lvblwiOlxuICAgICAgZXhwci5leHByZXNzaW9uID0gdGhpcy5jaGVja0xWYWwoZXhwci5leHByZXNzaW9uLCBiaW5kaW5nKTtcbiAgICAgIHJldHVybiBleHByO1xuXG4gICAgLy8gRklYTUUgcmVjdXJzaXZlbHkgY2hlY2sgY29udGVudHNcbiAgICBjYXNlIFwiT2JqZWN0UGF0dGVyblwiOlxuICAgIGNhc2UgXCJBcnJheVBhdHRlcm5cIjpcbiAgICBjYXNlIFwiUmVzdEVsZW1lbnRcIjpcbiAgICBjYXNlIFwiQXNzaWdubWVudFBhdHRlcm5cIjpcbiAgICAgIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNikgcmV0dXJuIGV4cHI7XG5cbiAgICBkZWZhdWx0OlxuICAgICAgcmV0dXJuIHRoaXMuZHVtbXlJZGVudCgpO1xuICB9XG59O1xuXG5scC5wYXJzZUV4cHJlc3Npb24gPSBmdW5jdGlvbiAobm9Jbikge1xuICB2YXIgc3RhcnQgPSB0aGlzLnN0b3JlQ3VycmVudFBvcygpO1xuICB2YXIgZXhwciA9IHRoaXMucGFyc2VNYXliZUFzc2lnbihub0luKTtcbiAgaWYgKHRoaXMudG9rLnR5cGUgPT09IF8udG9rVHlwZXMuY29tbWEpIHtcbiAgICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlQXQoc3RhcnQpO1xuICAgIG5vZGUuZXhwcmVzc2lvbnMgPSBbZXhwcl07XG4gICAgd2hpbGUgKHRoaXMuZWF0KF8udG9rVHlwZXMuY29tbWEpKSBub2RlLmV4cHJlc3Npb25zLnB1c2godGhpcy5wYXJzZU1heWJlQXNzaWduKG5vSW4pKTtcbiAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiU2VxdWVuY2VFeHByZXNzaW9uXCIpO1xuICB9XG4gIHJldHVybiBleHByO1xufTtcblxubHAucGFyc2VQYXJlbkV4cHJlc3Npb24gPSBmdW5jdGlvbiAoKSB7XG4gIHRoaXMucHVzaEN4KCk7XG4gIHRoaXMuZXhwZWN0KF8udG9rVHlwZXMucGFyZW5MKTtcbiAgdmFyIHZhbCA9IHRoaXMucGFyc2VFeHByZXNzaW9uKCk7XG4gIHRoaXMucG9wQ3goKTtcbiAgdGhpcy5leHBlY3QoXy50b2tUeXBlcy5wYXJlblIpO1xuICByZXR1cm4gdmFsO1xufTtcblxubHAucGFyc2VNYXliZUFzc2lnbiA9IGZ1bmN0aW9uIChub0luKSB7XG4gIHZhciBzdGFydCA9IHRoaXMuc3RvcmVDdXJyZW50UG9zKCk7XG4gIHZhciBsZWZ0ID0gdGhpcy5wYXJzZU1heWJlQ29uZGl0aW9uYWwobm9Jbik7XG4gIGlmICh0aGlzLnRvay50eXBlLmlzQXNzaWduKSB7XG4gICAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0KTtcbiAgICBub2RlLm9wZXJhdG9yID0gdGhpcy50b2sudmFsdWU7XG4gICAgbm9kZS5sZWZ0ID0gdGhpcy50b2sudHlwZSA9PT0gXy50b2tUeXBlcy5lcSA/IHRoaXMudG9Bc3NpZ25hYmxlKGxlZnQpIDogdGhpcy5jaGVja0xWYWwobGVmdCk7XG4gICAgdGhpcy5uZXh0KCk7XG4gICAgbm9kZS5yaWdodCA9IHRoaXMucGFyc2VNYXliZUFzc2lnbihub0luKTtcbiAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiQXNzaWdubWVudEV4cHJlc3Npb25cIik7XG4gIH1cbiAgcmV0dXJuIGxlZnQ7XG59O1xuXG5scC5wYXJzZU1heWJlQ29uZGl0aW9uYWwgPSBmdW5jdGlvbiAobm9Jbikge1xuICB2YXIgc3RhcnQgPSB0aGlzLnN0b3JlQ3VycmVudFBvcygpO1xuICB2YXIgZXhwciA9IHRoaXMucGFyc2VFeHByT3BzKG5vSW4pO1xuICBpZiAodGhpcy5lYXQoXy50b2tUeXBlcy5xdWVzdGlvbikpIHtcbiAgICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlQXQoc3RhcnQpO1xuICAgIG5vZGUudGVzdCA9IGV4cHI7XG4gICAgbm9kZS5jb25zZXF1ZW50ID0gdGhpcy5wYXJzZU1heWJlQXNzaWduKCk7XG4gICAgbm9kZS5hbHRlcm5hdGUgPSB0aGlzLmV4cGVjdChfLnRva1R5cGVzLmNvbG9uKSA/IHRoaXMucGFyc2VNYXliZUFzc2lnbihub0luKSA6IHRoaXMuZHVtbXlJZGVudCgpO1xuICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJDb25kaXRpb25hbEV4cHJlc3Npb25cIik7XG4gIH1cbiAgcmV0dXJuIGV4cHI7XG59O1xuXG5scC5wYXJzZUV4cHJPcHMgPSBmdW5jdGlvbiAobm9Jbikge1xuICB2YXIgc3RhcnQgPSB0aGlzLnN0b3JlQ3VycmVudFBvcygpO1xuICB2YXIgaW5kZW50ID0gdGhpcy5jdXJJbmRlbnQsXG4gICAgICBsaW5lID0gdGhpcy5jdXJMaW5lU3RhcnQ7XG4gIHJldHVybiB0aGlzLnBhcnNlRXhwck9wKHRoaXMucGFyc2VNYXliZVVuYXJ5KG5vSW4pLCBzdGFydCwgLTEsIG5vSW4sIGluZGVudCwgbGluZSk7XG59O1xuXG5scC5wYXJzZUV4cHJPcCA9IGZ1bmN0aW9uIChsZWZ0LCBzdGFydCwgbWluUHJlYywgbm9JbiwgaW5kZW50LCBsaW5lKSB7XG4gIGlmICh0aGlzLmN1ckxpbmVTdGFydCAhPSBsaW5lICYmIHRoaXMuY3VySW5kZW50IDwgaW5kZW50ICYmIHRoaXMudG9rZW5TdGFydHNMaW5lKCkpIHJldHVybiBsZWZ0O1xuICB2YXIgcHJlYyA9IHRoaXMudG9rLnR5cGUuYmlub3A7XG4gIGlmIChwcmVjICE9IG51bGwgJiYgKCFub0luIHx8IHRoaXMudG9rLnR5cGUgIT09IF8udG9rVHlwZXMuX2luKSkge1xuICAgIGlmIChwcmVjID4gbWluUHJlYykge1xuICAgICAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0KTtcbiAgICAgIG5vZGUubGVmdCA9IGxlZnQ7XG4gICAgICBub2RlLm9wZXJhdG9yID0gdGhpcy50b2sudmFsdWU7XG4gICAgICB0aGlzLm5leHQoKTtcbiAgICAgIGlmICh0aGlzLmN1ckxpbmVTdGFydCAhPSBsaW5lICYmIHRoaXMuY3VySW5kZW50IDwgaW5kZW50ICYmIHRoaXMudG9rZW5TdGFydHNMaW5lKCkpIHtcbiAgICAgICAgbm9kZS5yaWdodCA9IHRoaXMuZHVtbXlJZGVudCgpO1xuICAgICAgfSBlbHNlIHtcbiAgICAgICAgdmFyIHJpZ2h0U3RhcnQgPSB0aGlzLnN0b3JlQ3VycmVudFBvcygpO1xuICAgICAgICBub2RlLnJpZ2h0ID0gdGhpcy5wYXJzZUV4cHJPcCh0aGlzLnBhcnNlTWF5YmVVbmFyeShub0luKSwgcmlnaHRTdGFydCwgcHJlYywgbm9JbiwgaW5kZW50LCBsaW5lKTtcbiAgICAgIH1cbiAgICAgIHRoaXMuZmluaXNoTm9kZShub2RlLCAvJiZ8XFx8XFx8Ly50ZXN0KG5vZGUub3BlcmF0b3IpID8gXCJMb2dpY2FsRXhwcmVzc2lvblwiIDogXCJCaW5hcnlFeHByZXNzaW9uXCIpO1xuICAgICAgcmV0dXJuIHRoaXMucGFyc2VFeHByT3Aobm9kZSwgc3RhcnQsIG1pblByZWMsIG5vSW4sIGluZGVudCwgbGluZSk7XG4gICAgfVxuICB9XG4gIHJldHVybiBsZWZ0O1xufTtcblxubHAucGFyc2VNYXliZVVuYXJ5ID0gZnVuY3Rpb24gKG5vSW4pIHtcbiAgaWYgKHRoaXMudG9rLnR5cGUucHJlZml4KSB7XG4gICAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpLFxuICAgICAgICB1cGRhdGUgPSB0aGlzLnRvay50eXBlID09PSBfLnRva1R5cGVzLmluY0RlYztcbiAgICBub2RlLm9wZXJhdG9yID0gdGhpcy50b2sudmFsdWU7XG4gICAgbm9kZS5wcmVmaXggPSB0cnVlO1xuICAgIHRoaXMubmV4dCgpO1xuICAgIG5vZGUuYXJndW1lbnQgPSB0aGlzLnBhcnNlTWF5YmVVbmFyeShub0luKTtcbiAgICBpZiAodXBkYXRlKSBub2RlLmFyZ3VtZW50ID0gdGhpcy5jaGVja0xWYWwobm9kZS5hcmd1bWVudCk7XG4gICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCB1cGRhdGUgPyBcIlVwZGF0ZUV4cHJlc3Npb25cIiA6IFwiVW5hcnlFeHByZXNzaW9uXCIpO1xuICB9IGVsc2UgaWYgKHRoaXMudG9rLnR5cGUgPT09IF8udG9rVHlwZXMuZWxsaXBzaXMpIHtcbiAgICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gICAgdGhpcy5uZXh0KCk7XG4gICAgbm9kZS5hcmd1bWVudCA9IHRoaXMucGFyc2VNYXliZVVuYXJ5KG5vSW4pO1xuICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJTcHJlYWRFbGVtZW50XCIpO1xuICB9XG4gIHZhciBzdGFydCA9IHRoaXMuc3RvcmVDdXJyZW50UG9zKCk7XG4gIHZhciBleHByID0gdGhpcy5wYXJzZUV4cHJTdWJzY3JpcHRzKCk7XG4gIHdoaWxlICh0aGlzLnRvay50eXBlLnBvc3RmaXggJiYgIXRoaXMuY2FuSW5zZXJ0U2VtaWNvbG9uKCkpIHtcbiAgICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlQXQoc3RhcnQpO1xuICAgIG5vZGUub3BlcmF0b3IgPSB0aGlzLnRvay52YWx1ZTtcbiAgICBub2RlLnByZWZpeCA9IGZhbHNlO1xuICAgIG5vZGUuYXJndW1lbnQgPSB0aGlzLmNoZWNrTFZhbChleHByKTtcbiAgICB0aGlzLm5leHQoKTtcbiAgICBleHByID0gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiVXBkYXRlRXhwcmVzc2lvblwiKTtcbiAgfVxuICByZXR1cm4gZXhwcjtcbn07XG5cbmxwLnBhcnNlRXhwclN1YnNjcmlwdHMgPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBzdGFydCA9IHRoaXMuc3RvcmVDdXJyZW50UG9zKCk7XG4gIHJldHVybiB0aGlzLnBhcnNlU3Vic2NyaXB0cyh0aGlzLnBhcnNlRXhwckF0b20oKSwgc3RhcnQsIGZhbHNlLCB0aGlzLmN1ckluZGVudCwgdGhpcy5jdXJMaW5lU3RhcnQpO1xufTtcblxubHAucGFyc2VTdWJzY3JpcHRzID0gZnVuY3Rpb24gKGJhc2UsIHN0YXJ0LCBub0NhbGxzLCBzdGFydEluZGVudCwgbGluZSkge1xuICBmb3IgKDs7KSB7XG4gICAgaWYgKHRoaXMuY3VyTGluZVN0YXJ0ICE9IGxpbmUgJiYgdGhpcy5jdXJJbmRlbnQgPD0gc3RhcnRJbmRlbnQgJiYgdGhpcy50b2tlblN0YXJ0c0xpbmUoKSkge1xuICAgICAgaWYgKHRoaXMudG9rLnR5cGUgPT0gXy50b2tUeXBlcy5kb3QgJiYgdGhpcy5jdXJJbmRlbnQgPT0gc3RhcnRJbmRlbnQpIC0tc3RhcnRJbmRlbnQ7ZWxzZSByZXR1cm4gYmFzZTtcbiAgICB9XG5cbiAgICBpZiAodGhpcy5lYXQoXy50b2tUeXBlcy5kb3QpKSB7XG4gICAgICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlQXQoc3RhcnQpO1xuICAgICAgbm9kZS5vYmplY3QgPSBiYXNlO1xuICAgICAgaWYgKHRoaXMuY3VyTGluZVN0YXJ0ICE9IGxpbmUgJiYgdGhpcy5jdXJJbmRlbnQgPD0gc3RhcnRJbmRlbnQgJiYgdGhpcy50b2tlblN0YXJ0c0xpbmUoKSkgbm9kZS5wcm9wZXJ0eSA9IHRoaXMuZHVtbXlJZGVudCgpO2Vsc2Ugbm9kZS5wcm9wZXJ0eSA9IHRoaXMucGFyc2VQcm9wZXJ0eUFjY2Vzc29yKCkgfHwgdGhpcy5kdW1teUlkZW50KCk7XG4gICAgICBub2RlLmNvbXB1dGVkID0gZmFsc2U7XG4gICAgICBiYXNlID0gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiTWVtYmVyRXhwcmVzc2lvblwiKTtcbiAgICB9IGVsc2UgaWYgKHRoaXMudG9rLnR5cGUgPT0gXy50b2tUeXBlcy5icmFja2V0TCkge1xuICAgICAgdGhpcy5wdXNoQ3goKTtcbiAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0KTtcbiAgICAgIG5vZGUub2JqZWN0ID0gYmFzZTtcbiAgICAgIG5vZGUucHJvcGVydHkgPSB0aGlzLnBhcnNlRXhwcmVzc2lvbigpO1xuICAgICAgbm9kZS5jb21wdXRlZCA9IHRydWU7XG4gICAgICB0aGlzLnBvcEN4KCk7XG4gICAgICB0aGlzLmV4cGVjdChfLnRva1R5cGVzLmJyYWNrZXRSKTtcbiAgICAgIGJhc2UgPSB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJNZW1iZXJFeHByZXNzaW9uXCIpO1xuICAgIH0gZWxzZSBpZiAoIW5vQ2FsbHMgJiYgdGhpcy50b2sudHlwZSA9PSBfLnRva1R5cGVzLnBhcmVuTCkge1xuICAgICAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0KTtcbiAgICAgIG5vZGUuY2FsbGVlID0gYmFzZTtcbiAgICAgIG5vZGUuYXJndW1lbnRzID0gdGhpcy5wYXJzZUV4cHJMaXN0KF8udG9rVHlwZXMucGFyZW5SKTtcbiAgICAgIGJhc2UgPSB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJDYWxsRXhwcmVzc2lvblwiKTtcbiAgICB9IGVsc2UgaWYgKHRoaXMudG9rLnR5cGUgPT0gXy50b2tUeXBlcy5iYWNrUXVvdGUpIHtcbiAgICAgIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGVBdChzdGFydCk7XG4gICAgICBub2RlLnRhZyA9IGJhc2U7XG4gICAgICBub2RlLnF1YXNpID0gdGhpcy5wYXJzZVRlbXBsYXRlKCk7XG4gICAgICBiYXNlID0gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiVGFnZ2VkVGVtcGxhdGVFeHByZXNzaW9uXCIpO1xuICAgIH0gZWxzZSB7XG4gICAgICByZXR1cm4gYmFzZTtcbiAgICB9XG4gIH1cbn07XG5cbmxwLnBhcnNlRXhwckF0b20gPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBub2RlID0gdW5kZWZpbmVkO1xuICBzd2l0Y2ggKHRoaXMudG9rLnR5cGUpIHtcbiAgICBjYXNlIF8udG9rVHlwZXMuX3RoaXM6XG4gICAgY2FzZSBfLnRva1R5cGVzLl9zdXBlcjpcbiAgICAgIHZhciB0eXBlID0gdGhpcy50b2sudHlwZSA9PT0gXy50b2tUeXBlcy5fdGhpcyA/IFwiVGhpc0V4cHJlc3Npb25cIiA6IFwiU3VwZXJcIjtcbiAgICAgIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIHR5cGUpO1xuXG4gICAgY2FzZSBfLnRva1R5cGVzLm5hbWU6XG4gICAgICB2YXIgc3RhcnQgPSB0aGlzLnN0b3JlQ3VycmVudFBvcygpO1xuICAgICAgdmFyIGlkID0gdGhpcy5wYXJzZUlkZW50KCk7XG4gICAgICByZXR1cm4gdGhpcy5lYXQoXy50b2tUeXBlcy5hcnJvdykgPyB0aGlzLnBhcnNlQXJyb3dFeHByZXNzaW9uKHRoaXMuc3RhcnROb2RlQXQoc3RhcnQpLCBbaWRdKSA6IGlkO1xuXG4gICAgY2FzZSBfLnRva1R5cGVzLnJlZ2V4cDpcbiAgICAgIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICAgICAgdmFyIHZhbCA9IHRoaXMudG9rLnZhbHVlO1xuICAgICAgbm9kZS5yZWdleCA9IHsgcGF0dGVybjogdmFsLnBhdHRlcm4sIGZsYWdzOiB2YWwuZmxhZ3MgfTtcbiAgICAgIG5vZGUudmFsdWUgPSB2YWwudmFsdWU7XG4gICAgICBub2RlLnJhdyA9IHRoaXMuaW5wdXQuc2xpY2UodGhpcy50b2suc3RhcnQsIHRoaXMudG9rLmVuZCk7XG4gICAgICB0aGlzLm5leHQoKTtcbiAgICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJMaXRlcmFsXCIpO1xuXG4gICAgY2FzZSBfLnRva1R5cGVzLm51bTpjYXNlIF8udG9rVHlwZXMuc3RyaW5nOlxuICAgICAgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gICAgICBub2RlLnZhbHVlID0gdGhpcy50b2sudmFsdWU7XG4gICAgICBub2RlLnJhdyA9IHRoaXMuaW5wdXQuc2xpY2UodGhpcy50b2suc3RhcnQsIHRoaXMudG9rLmVuZCk7XG4gICAgICB0aGlzLm5leHQoKTtcbiAgICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJMaXRlcmFsXCIpO1xuXG4gICAgY2FzZSBfLnRva1R5cGVzLl9udWxsOmNhc2UgXy50b2tUeXBlcy5fdHJ1ZTpjYXNlIF8udG9rVHlwZXMuX2ZhbHNlOlxuICAgICAgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gICAgICBub2RlLnZhbHVlID0gdGhpcy50b2sudHlwZSA9PT0gXy50b2tUeXBlcy5fbnVsbCA/IG51bGwgOiB0aGlzLnRvay50eXBlID09PSBfLnRva1R5cGVzLl90cnVlO1xuICAgICAgbm9kZS5yYXcgPSB0aGlzLnRvay50eXBlLmtleXdvcmQ7XG4gICAgICB0aGlzLm5leHQoKTtcbiAgICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJMaXRlcmFsXCIpO1xuXG4gICAgY2FzZSBfLnRva1R5cGVzLnBhcmVuTDpcbiAgICAgIHZhciBwYXJlblN0YXJ0ID0gdGhpcy5zdG9yZUN1cnJlbnRQb3MoKTtcbiAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgdmFyIGlubmVyID0gdGhpcy5wYXJzZUV4cHJlc3Npb24oKTtcbiAgICAgIHRoaXMuZXhwZWN0KF8udG9rVHlwZXMucGFyZW5SKTtcbiAgICAgIGlmICh0aGlzLmVhdChfLnRva1R5cGVzLmFycm93KSkge1xuICAgICAgICByZXR1cm4gdGhpcy5wYXJzZUFycm93RXhwcmVzc2lvbih0aGlzLnN0YXJ0Tm9kZUF0KHBhcmVuU3RhcnQpLCBpbm5lci5leHByZXNzaW9ucyB8fCAoX3BhcnNldXRpbC5pc0R1bW15KGlubmVyKSA/IFtdIDogW2lubmVyXSkpO1xuICAgICAgfVxuICAgICAgaWYgKHRoaXMub3B0aW9ucy5wcmVzZXJ2ZVBhcmVucykge1xuICAgICAgICB2YXIgcGFyID0gdGhpcy5zdGFydE5vZGVBdChwYXJlblN0YXJ0KTtcbiAgICAgICAgcGFyLmV4cHJlc3Npb24gPSBpbm5lcjtcbiAgICAgICAgaW5uZXIgPSB0aGlzLmZpbmlzaE5vZGUocGFyLCBcIlBhcmVudGhlc2l6ZWRFeHByZXNzaW9uXCIpO1xuICAgICAgfVxuICAgICAgcmV0dXJuIGlubmVyO1xuXG4gICAgY2FzZSBfLnRva1R5cGVzLmJyYWNrZXRMOlxuICAgICAgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gICAgICBub2RlLmVsZW1lbnRzID0gdGhpcy5wYXJzZUV4cHJMaXN0KF8udG9rVHlwZXMuYnJhY2tldFIsIHRydWUpO1xuICAgICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkFycmF5RXhwcmVzc2lvblwiKTtcblxuICAgIGNhc2UgXy50b2tUeXBlcy5icmFjZUw6XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZU9iaigpO1xuXG4gICAgY2FzZSBfLnRva1R5cGVzLl9jbGFzczpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlQ2xhc3MoKTtcblxuICAgIGNhc2UgXy50b2tUeXBlcy5fZnVuY3Rpb246XG4gICAgICBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgcmV0dXJuIHRoaXMucGFyc2VGdW5jdGlvbihub2RlLCBmYWxzZSk7XG5cbiAgICBjYXNlIF8udG9rVHlwZXMuX25ldzpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlTmV3KCk7XG5cbiAgICBjYXNlIF8udG9rVHlwZXMuX3lpZWxkOlxuICAgICAgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gICAgICB0aGlzLm5leHQoKTtcbiAgICAgIGlmICh0aGlzLnNlbWljb2xvbigpIHx8IHRoaXMuY2FuSW5zZXJ0U2VtaWNvbG9uKCkgfHwgdGhpcy50b2sudHlwZSAhPSBfLnRva1R5cGVzLnN0YXIgJiYgIXRoaXMudG9rLnR5cGUuc3RhcnRzRXhwcikge1xuICAgICAgICBub2RlLmRlbGVnYXRlID0gZmFsc2U7XG4gICAgICAgIG5vZGUuYXJndW1lbnQgPSBudWxsO1xuICAgICAgfSBlbHNlIHtcbiAgICAgICAgbm9kZS5kZWxlZ2F0ZSA9IHRoaXMuZWF0KF8udG9rVHlwZXMuc3Rhcik7XG4gICAgICAgIG5vZGUuYXJndW1lbnQgPSB0aGlzLnBhcnNlTWF5YmVBc3NpZ24oKTtcbiAgICAgIH1cbiAgICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJZaWVsZEV4cHJlc3Npb25cIik7XG5cbiAgICBjYXNlIF8udG9rVHlwZXMuYmFja1F1b3RlOlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VUZW1wbGF0ZSgpO1xuXG4gICAgZGVmYXVsdDpcbiAgICAgIHJldHVybiB0aGlzLmR1bW15SWRlbnQoKTtcbiAgfVxufTtcblxubHAucGFyc2VOZXcgPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGUoKSxcbiAgICAgIHN0YXJ0SW5kZW50ID0gdGhpcy5jdXJJbmRlbnQsXG4gICAgICBsaW5lID0gdGhpcy5jdXJMaW5lU3RhcnQ7XG4gIHZhciBtZXRhID0gdGhpcy5wYXJzZUlkZW50KHRydWUpO1xuICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYgJiYgdGhpcy5lYXQoXy50b2tUeXBlcy5kb3QpKSB7XG4gICAgbm9kZS5tZXRhID0gbWV0YTtcbiAgICBub2RlLnByb3BlcnR5ID0gdGhpcy5wYXJzZUlkZW50KHRydWUpO1xuICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJNZXRhUHJvcGVydHlcIik7XG4gIH1cbiAgdmFyIHN0YXJ0ID0gdGhpcy5zdG9yZUN1cnJlbnRQb3MoKTtcbiAgbm9kZS5jYWxsZWUgPSB0aGlzLnBhcnNlU3Vic2NyaXB0cyh0aGlzLnBhcnNlRXhwckF0b20oKSwgc3RhcnQsIHRydWUsIHN0YXJ0SW5kZW50LCBsaW5lKTtcbiAgaWYgKHRoaXMudG9rLnR5cGUgPT0gXy50b2tUeXBlcy5wYXJlbkwpIHtcbiAgICBub2RlLmFyZ3VtZW50cyA9IHRoaXMucGFyc2VFeHByTGlzdChfLnRva1R5cGVzLnBhcmVuUik7XG4gIH0gZWxzZSB7XG4gICAgbm9kZS5hcmd1bWVudHMgPSBbXTtcbiAgfVxuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiTmV3RXhwcmVzc2lvblwiKTtcbn07XG5cbmxwLnBhcnNlVGVtcGxhdGVFbGVtZW50ID0gZnVuY3Rpb24gKCkge1xuICB2YXIgZWxlbSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gIGVsZW0udmFsdWUgPSB7XG4gICAgcmF3OiB0aGlzLmlucHV0LnNsaWNlKHRoaXMudG9rLnN0YXJ0LCB0aGlzLnRvay5lbmQpLnJlcGxhY2UoL1xcclxcbj8vZywgXCJcXG5cIiksXG4gICAgY29va2VkOiB0aGlzLnRvay52YWx1ZVxuICB9O1xuICB0aGlzLm5leHQoKTtcbiAgZWxlbS50YWlsID0gdGhpcy50b2sudHlwZSA9PT0gXy50b2tUeXBlcy5iYWNrUXVvdGU7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUoZWxlbSwgXCJUZW1wbGF0ZUVsZW1lbnRcIik7XG59O1xuXG5scC5wYXJzZVRlbXBsYXRlID0gZnVuY3Rpb24gKCkge1xuICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gIHRoaXMubmV4dCgpO1xuICBub2RlLmV4cHJlc3Npb25zID0gW107XG4gIHZhciBjdXJFbHQgPSB0aGlzLnBhcnNlVGVtcGxhdGVFbGVtZW50KCk7XG4gIG5vZGUucXVhc2lzID0gW2N1ckVsdF07XG4gIHdoaWxlICghY3VyRWx0LnRhaWwpIHtcbiAgICB0aGlzLm5leHQoKTtcbiAgICBub2RlLmV4cHJlc3Npb25zLnB1c2godGhpcy5wYXJzZUV4cHJlc3Npb24oKSk7XG4gICAgaWYgKHRoaXMuZXhwZWN0KF8udG9rVHlwZXMuYnJhY2VSKSkge1xuICAgICAgY3VyRWx0ID0gdGhpcy5wYXJzZVRlbXBsYXRlRWxlbWVudCgpO1xuICAgIH0gZWxzZSB7XG4gICAgICBjdXJFbHQgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICAgICAgY3VyRWx0LnZhbHVlID0geyBjb29rZWQ6IFwiXCIsIHJhdzogXCJcIiB9O1xuICAgICAgY3VyRWx0LnRhaWwgPSB0cnVlO1xuICAgIH1cbiAgICBub2RlLnF1YXNpcy5wdXNoKGN1ckVsdCk7XG4gIH1cbiAgdGhpcy5leHBlY3QoXy50b2tUeXBlcy5iYWNrUXVvdGUpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiVGVtcGxhdGVMaXRlcmFsXCIpO1xufTtcblxubHAucGFyc2VPYmogPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgbm9kZS5wcm9wZXJ0aWVzID0gW107XG4gIHRoaXMucHVzaEN4KCk7XG4gIHZhciBpbmRlbnQgPSB0aGlzLmN1ckluZGVudCArIDEsXG4gICAgICBsaW5lID0gdGhpcy5jdXJMaW5lU3RhcnQ7XG4gIHRoaXMuZWF0KF8udG9rVHlwZXMuYnJhY2VMKTtcbiAgaWYgKHRoaXMuY3VySW5kZW50ICsgMSA8IGluZGVudCkge1xuICAgIGluZGVudCA9IHRoaXMuY3VySW5kZW50O2xpbmUgPSB0aGlzLmN1ckxpbmVTdGFydDtcbiAgfVxuICB3aGlsZSAoIXRoaXMuY2xvc2VzKF8udG9rVHlwZXMuYnJhY2VSLCBpbmRlbnQsIGxpbmUpKSB7XG4gICAgdmFyIHByb3AgPSB0aGlzLnN0YXJ0Tm9kZSgpLFxuICAgICAgICBpc0dlbmVyYXRvciA9IHVuZGVmaW5lZCxcbiAgICAgICAgc3RhcnQgPSB1bmRlZmluZWQ7XG4gICAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KSB7XG4gICAgICBzdGFydCA9IHRoaXMuc3RvcmVDdXJyZW50UG9zKCk7XG4gICAgICBwcm9wLm1ldGhvZCA9IGZhbHNlO1xuICAgICAgcHJvcC5zaG9ydGhhbmQgPSBmYWxzZTtcbiAgICAgIGlzR2VuZXJhdG9yID0gdGhpcy5lYXQoXy50b2tUeXBlcy5zdGFyKTtcbiAgICB9XG4gICAgdGhpcy5wYXJzZVByb3BlcnR5TmFtZShwcm9wKTtcbiAgICBpZiAoX3BhcnNldXRpbC5pc0R1bW15KHByb3Aua2V5KSkge1xuICAgICAgaWYgKF9wYXJzZXV0aWwuaXNEdW1teSh0aGlzLnBhcnNlTWF5YmVBc3NpZ24oKSkpIHRoaXMubmV4dCgpO3RoaXMuZWF0KF8udG9rVHlwZXMuY29tbWEpO2NvbnRpbnVlO1xuICAgIH1cbiAgICBpZiAodGhpcy5lYXQoXy50b2tUeXBlcy5jb2xvbikpIHtcbiAgICAgIHByb3Aua2luZCA9IFwiaW5pdFwiO1xuICAgICAgcHJvcC52YWx1ZSA9IHRoaXMucGFyc2VNYXliZUFzc2lnbigpO1xuICAgIH0gZWxzZSBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYgJiYgKHRoaXMudG9rLnR5cGUgPT09IF8udG9rVHlwZXMucGFyZW5MIHx8IHRoaXMudG9rLnR5cGUgPT09IF8udG9rVHlwZXMuYnJhY2VMKSkge1xuICAgICAgcHJvcC5raW5kID0gXCJpbml0XCI7XG4gICAgICBwcm9wLm1ldGhvZCA9IHRydWU7XG4gICAgICBwcm9wLnZhbHVlID0gdGhpcy5wYXJzZU1ldGhvZChpc0dlbmVyYXRvcik7XG4gICAgfSBlbHNlIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNSAmJiBwcm9wLmtleS50eXBlID09PSBcIklkZW50aWZpZXJcIiAmJiAhcHJvcC5jb21wdXRlZCAmJiAocHJvcC5rZXkubmFtZSA9PT0gXCJnZXRcIiB8fCBwcm9wLmtleS5uYW1lID09PSBcInNldFwiKSAmJiAodGhpcy50b2sudHlwZSAhPSBfLnRva1R5cGVzLmNvbW1hICYmIHRoaXMudG9rLnR5cGUgIT0gXy50b2tUeXBlcy5icmFjZVIpKSB7XG4gICAgICBwcm9wLmtpbmQgPSBwcm9wLmtleS5uYW1lO1xuICAgICAgdGhpcy5wYXJzZVByb3BlcnR5TmFtZShwcm9wKTtcbiAgICAgIHByb3AudmFsdWUgPSB0aGlzLnBhcnNlTWV0aG9kKGZhbHNlKTtcbiAgICB9IGVsc2Uge1xuICAgICAgcHJvcC5raW5kID0gXCJpbml0XCI7XG4gICAgICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYpIHtcbiAgICAgICAgaWYgKHRoaXMuZWF0KF8udG9rVHlwZXMuZXEpKSB7XG4gICAgICAgICAgdmFyIGFzc2lnbiA9IHRoaXMuc3RhcnROb2RlQXQoc3RhcnQpO1xuICAgICAgICAgIGFzc2lnbi5vcGVyYXRvciA9IFwiPVwiO1xuICAgICAgICAgIGFzc2lnbi5sZWZ0ID0gcHJvcC5rZXk7XG4gICAgICAgICAgYXNzaWduLnJpZ2h0ID0gdGhpcy5wYXJzZU1heWJlQXNzaWduKCk7XG4gICAgICAgICAgcHJvcC52YWx1ZSA9IHRoaXMuZmluaXNoTm9kZShhc3NpZ24sIFwiQXNzaWdubWVudEV4cHJlc3Npb25cIik7XG4gICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgcHJvcC52YWx1ZSA9IHByb3Aua2V5O1xuICAgICAgICB9XG4gICAgICB9IGVsc2Uge1xuICAgICAgICBwcm9wLnZhbHVlID0gdGhpcy5kdW1teUlkZW50KCk7XG4gICAgICB9XG4gICAgICBwcm9wLnNob3J0aGFuZCA9IHRydWU7XG4gICAgfVxuICAgIG5vZGUucHJvcGVydGllcy5wdXNoKHRoaXMuZmluaXNoTm9kZShwcm9wLCBcIlByb3BlcnR5XCIpKTtcbiAgICB0aGlzLmVhdChfLnRva1R5cGVzLmNvbW1hKTtcbiAgfVxuICB0aGlzLnBvcEN4KCk7XG4gIGlmICghdGhpcy5lYXQoXy50b2tUeXBlcy5icmFjZVIpKSB7XG4gICAgLy8gSWYgdGhlcmUgaXMgbm8gY2xvc2luZyBicmFjZSwgbWFrZSB0aGUgbm9kZSBzcGFuIHRvIHRoZSBzdGFydFxuICAgIC8vIG9mIHRoZSBuZXh0IHRva2VuICh0aGlzIGlzIHVzZWZ1bCBmb3IgVGVybilcbiAgICB0aGlzLmxhc3QuZW5kID0gdGhpcy50b2suc3RhcnQ7XG4gICAgaWYgKHRoaXMub3B0aW9ucy5sb2NhdGlvbnMpIHRoaXMubGFzdC5sb2MuZW5kID0gdGhpcy50b2subG9jLnN0YXJ0O1xuICB9XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJPYmplY3RFeHByZXNzaW9uXCIpO1xufTtcblxubHAucGFyc2VQcm9wZXJ0eU5hbWUgPSBmdW5jdGlvbiAocHJvcCkge1xuICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYpIHtcbiAgICBpZiAodGhpcy5lYXQoXy50b2tUeXBlcy5icmFja2V0TCkpIHtcbiAgICAgIHByb3AuY29tcHV0ZWQgPSB0cnVlO1xuICAgICAgcHJvcC5rZXkgPSB0aGlzLnBhcnNlRXhwcmVzc2lvbigpO1xuICAgICAgdGhpcy5leHBlY3QoXy50b2tUeXBlcy5icmFja2V0Uik7XG4gICAgICByZXR1cm47XG4gICAgfSBlbHNlIHtcbiAgICAgIHByb3AuY29tcHV0ZWQgPSBmYWxzZTtcbiAgICB9XG4gIH1cbiAgdmFyIGtleSA9IHRoaXMudG9rLnR5cGUgPT09IF8udG9rVHlwZXMubnVtIHx8IHRoaXMudG9rLnR5cGUgPT09IF8udG9rVHlwZXMuc3RyaW5nID8gdGhpcy5wYXJzZUV4cHJBdG9tKCkgOiB0aGlzLnBhcnNlSWRlbnQoKTtcbiAgcHJvcC5rZXkgPSBrZXkgfHwgdGhpcy5kdW1teUlkZW50KCk7XG59O1xuXG5scC5wYXJzZVByb3BlcnR5QWNjZXNzb3IgPSBmdW5jdGlvbiAoKSB7XG4gIGlmICh0aGlzLnRvay50eXBlID09PSBfLnRva1R5cGVzLm5hbWUgfHwgdGhpcy50b2sudHlwZS5rZXl3b3JkKSByZXR1cm4gdGhpcy5wYXJzZUlkZW50KCk7XG59O1xuXG5scC5wYXJzZUlkZW50ID0gZnVuY3Rpb24gKCkge1xuICB2YXIgbmFtZSA9IHRoaXMudG9rLnR5cGUgPT09IF8udG9rVHlwZXMubmFtZSA/IHRoaXMudG9rLnZhbHVlIDogdGhpcy50b2sudHlwZS5rZXl3b3JkO1xuICBpZiAoIW5hbWUpIHJldHVybiB0aGlzLmR1bW15SWRlbnQoKTtcbiAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICB0aGlzLm5leHQoKTtcbiAgbm9kZS5uYW1lID0gbmFtZTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIklkZW50aWZpZXJcIik7XG59O1xuXG5scC5pbml0RnVuY3Rpb24gPSBmdW5jdGlvbiAobm9kZSkge1xuICBub2RlLmlkID0gbnVsbDtcbiAgbm9kZS5wYXJhbXMgPSBbXTtcbiAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KSB7XG4gICAgbm9kZS5nZW5lcmF0b3IgPSBmYWxzZTtcbiAgICBub2RlLmV4cHJlc3Npb24gPSBmYWxzZTtcbiAgfVxufTtcblxuLy8gQ29udmVydCBleGlzdGluZyBleHByZXNzaW9uIGF0b20gdG8gYXNzaWduYWJsZSBwYXR0ZXJuXG4vLyBpZiBwb3NzaWJsZS5cblxubHAudG9Bc3NpZ25hYmxlID0gZnVuY3Rpb24gKG5vZGUsIGJpbmRpbmcpIHtcbiAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2ICYmIG5vZGUpIHtcbiAgICBzd2l0Y2ggKG5vZGUudHlwZSkge1xuICAgICAgY2FzZSBcIk9iamVjdEV4cHJlc3Npb25cIjpcbiAgICAgICAgbm9kZS50eXBlID0gXCJPYmplY3RQYXR0ZXJuXCI7XG4gICAgICAgIHZhciBwcm9wcyA9IG5vZGUucHJvcGVydGllcztcbiAgICAgICAgZm9yICh2YXIgaSA9IDA7IGkgPCBwcm9wcy5sZW5ndGg7IGkrKykge1xuICAgICAgICAgIHRoaXMudG9Bc3NpZ25hYmxlKHByb3BzW2ldLnZhbHVlLCBiaW5kaW5nKTtcbiAgICAgICAgfWJyZWFrO1xuXG4gICAgICBjYXNlIFwiQXJyYXlFeHByZXNzaW9uXCI6XG4gICAgICAgIG5vZGUudHlwZSA9IFwiQXJyYXlQYXR0ZXJuXCI7XG4gICAgICAgIHRoaXMudG9Bc3NpZ25hYmxlTGlzdChub2RlLmVsZW1lbnRzLCBiaW5kaW5nKTtcbiAgICAgICAgYnJlYWs7XG5cbiAgICAgIGNhc2UgXCJTcHJlYWRFbGVtZW50XCI6XG4gICAgICAgIG5vZGUudHlwZSA9IFwiUmVzdEVsZW1lbnRcIjtcbiAgICAgICAgbm9kZS5hcmd1bWVudCA9IHRoaXMudG9Bc3NpZ25hYmxlKG5vZGUuYXJndW1lbnQsIGJpbmRpbmcpO1xuICAgICAgICBicmVhaztcblxuICAgICAgY2FzZSBcIkFzc2lnbm1lbnRFeHByZXNzaW9uXCI6XG4gICAgICAgIG5vZGUudHlwZSA9IFwiQXNzaWdubWVudFBhdHRlcm5cIjtcbiAgICAgICAgZGVsZXRlIG5vZGUub3BlcmF0b3I7XG4gICAgICAgIGJyZWFrO1xuICAgIH1cbiAgfVxuICByZXR1cm4gdGhpcy5jaGVja0xWYWwobm9kZSwgYmluZGluZyk7XG59O1xuXG5scC50b0Fzc2lnbmFibGVMaXN0ID0gZnVuY3Rpb24gKGV4cHJMaXN0LCBiaW5kaW5nKSB7XG4gIGZvciAodmFyIGkgPSAwOyBpIDwgZXhwckxpc3QubGVuZ3RoOyBpKyspIHtcbiAgICBleHByTGlzdFtpXSA9IHRoaXMudG9Bc3NpZ25hYmxlKGV4cHJMaXN0W2ldLCBiaW5kaW5nKTtcbiAgfXJldHVybiBleHByTGlzdDtcbn07XG5cbmxwLnBhcnNlRnVuY3Rpb25QYXJhbXMgPSBmdW5jdGlvbiAocGFyYW1zKSB7XG4gIHBhcmFtcyA9IHRoaXMucGFyc2VFeHByTGlzdChfLnRva1R5cGVzLnBhcmVuUik7XG4gIHJldHVybiB0aGlzLnRvQXNzaWduYWJsZUxpc3QocGFyYW1zLCB0cnVlKTtcbn07XG5cbmxwLnBhcnNlTWV0aG9kID0gZnVuY3Rpb24gKGlzR2VuZXJhdG9yKSB7XG4gIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgdGhpcy5pbml0RnVuY3Rpb24obm9kZSk7XG4gIG5vZGUucGFyYW1zID0gdGhpcy5wYXJzZUZ1bmN0aW9uUGFyYW1zKCk7XG4gIG5vZGUuZ2VuZXJhdG9yID0gaXNHZW5lcmF0b3IgfHwgZmFsc2U7XG4gIG5vZGUuZXhwcmVzc2lvbiA9IHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2ICYmIHRoaXMudG9rLnR5cGUgIT09IF8udG9rVHlwZXMuYnJhY2VMO1xuICBub2RlLmJvZHkgPSBub2RlLmV4cHJlc3Npb24gPyB0aGlzLnBhcnNlTWF5YmVBc3NpZ24oKSA6IHRoaXMucGFyc2VCbG9jaygpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiRnVuY3Rpb25FeHByZXNzaW9uXCIpO1xufTtcblxubHAucGFyc2VBcnJvd0V4cHJlc3Npb24gPSBmdW5jdGlvbiAobm9kZSwgcGFyYW1zKSB7XG4gIHRoaXMuaW5pdEZ1bmN0aW9uKG5vZGUpO1xuICBub2RlLnBhcmFtcyA9IHRoaXMudG9Bc3NpZ25hYmxlTGlzdChwYXJhbXMsIHRydWUpO1xuICBub2RlLmV4cHJlc3Npb24gPSB0aGlzLnRvay50eXBlICE9PSBfLnRva1R5cGVzLmJyYWNlTDtcbiAgbm9kZS5ib2R5ID0gbm9kZS5leHByZXNzaW9uID8gdGhpcy5wYXJzZU1heWJlQXNzaWduKCkgOiB0aGlzLnBhcnNlQmxvY2soKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkFycm93RnVuY3Rpb25FeHByZXNzaW9uXCIpO1xufTtcblxubHAucGFyc2VFeHByTGlzdCA9IGZ1bmN0aW9uIChjbG9zZSwgYWxsb3dFbXB0eSkge1xuICB0aGlzLnB1c2hDeCgpO1xuICB2YXIgaW5kZW50ID0gdGhpcy5jdXJJbmRlbnQsXG4gICAgICBsaW5lID0gdGhpcy5jdXJMaW5lU3RhcnQsXG4gICAgICBlbHRzID0gW107XG4gIHRoaXMubmV4dCgpOyAvLyBPcGVuaW5nIGJyYWNrZXRcbiAgd2hpbGUgKCF0aGlzLmNsb3NlcyhjbG9zZSwgaW5kZW50ICsgMSwgbGluZSkpIHtcbiAgICBpZiAodGhpcy5lYXQoXy50b2tUeXBlcy5jb21tYSkpIHtcbiAgICAgIGVsdHMucHVzaChhbGxvd0VtcHR5ID8gbnVsbCA6IHRoaXMuZHVtbXlJZGVudCgpKTtcbiAgICAgIGNvbnRpbnVlO1xuICAgIH1cbiAgICB2YXIgZWx0ID0gdGhpcy5wYXJzZU1heWJlQXNzaWduKCk7XG4gICAgaWYgKF9wYXJzZXV0aWwuaXNEdW1teShlbHQpKSB7XG4gICAgICBpZiAodGhpcy5jbG9zZXMoY2xvc2UsIGluZGVudCwgbGluZSkpIGJyZWFrO1xuICAgICAgdGhpcy5uZXh0KCk7XG4gICAgfSBlbHNlIHtcbiAgICAgIGVsdHMucHVzaChlbHQpO1xuICAgIH1cbiAgICB0aGlzLmVhdChfLnRva1R5cGVzLmNvbW1hKTtcbiAgfVxuICB0aGlzLnBvcEN4KCk7XG4gIGlmICghdGhpcy5lYXQoY2xvc2UpKSB7XG4gICAgLy8gSWYgdGhlcmUgaXMgbm8gY2xvc2luZyBicmFjZSwgbWFrZSB0aGUgbm9kZSBzcGFuIHRvIHRoZSBzdGFydFxuICAgIC8vIG9mIHRoZSBuZXh0IHRva2VuICh0aGlzIGlzIHVzZWZ1bCBmb3IgVGVybilcbiAgICB0aGlzLmxhc3QuZW5kID0gdGhpcy50b2suc3RhcnQ7XG4gICAgaWYgKHRoaXMub3B0aW9ucy5sb2NhdGlvbnMpIHRoaXMubGFzdC5sb2MuZW5kID0gdGhpcy50b2subG9jLnN0YXJ0O1xuICB9XG4gIHJldHVybiBlbHRzO1xufTtcblxufSx7XCIuLlwiOjEsXCIuL3BhcnNldXRpbFwiOjQsXCIuL3N0YXRlXCI6NX1dLDM6W2Z1bmN0aW9uKF9kZXJlcV8sbW9kdWxlLGV4cG9ydHMpe1xuLy8gQWNvcm46IExvb3NlIHBhcnNlclxuLy9cbi8vIFRoaXMgbW9kdWxlIHByb3ZpZGVzIGFuIGFsdGVybmF0aXZlIHBhcnNlciAoYHBhcnNlX2RhbW1pdGApIHRoYXRcbi8vIGV4cG9zZXMgdGhhdCBzYW1lIGludGVyZmFjZSBhcyBgcGFyc2VgLCBidXQgd2lsbCB0cnkgdG8gcGFyc2Vcbi8vIGFueXRoaW5nIGFzIEphdmFTY3JpcHQsIHJlcGFpcmluZyBzeW50YXggZXJyb3IgdGhlIGJlc3QgaXQgY2FuLlxuLy8gVGhlcmUgYXJlIGNpcmN1bXN0YW5jZXMgaW4gd2hpY2ggaXQgd2lsbCByYWlzZSBhbiBlcnJvciBhbmQgZ2l2ZVxuLy8gdXAsIGJ1dCB0aGV5IGFyZSB2ZXJ5IHJhcmUuIFRoZSByZXN1bHRpbmcgQVNUIHdpbGwgYmUgYSBtb3N0bHlcbi8vIHZhbGlkIEphdmFTY3JpcHQgQVNUIChhcyBwZXIgdGhlIFtNb3ppbGxhIHBhcnNlciBBUEldW2FwaV0sIGV4Y2VwdFxuLy8gdGhhdDpcbi8vXG4vLyAtIFJldHVybiBvdXRzaWRlIGZ1bmN0aW9ucyBpcyBhbGxvd2VkXG4vL1xuLy8gLSBMYWJlbCBjb25zaXN0ZW5jeSAobm8gY29uZmxpY3RzLCBicmVhayBvbmx5IHRvIGV4aXN0aW5nIGxhYmVscylcbi8vICAgaXMgbm90IGVuZm9yY2VkLlxuLy9cbi8vIC0gQm9ndXMgSWRlbnRpZmllciBub2RlcyB3aXRoIGEgbmFtZSBvZiBgXCLinJZcImAgYXJlIGluc2VydGVkIHdoZW5ldmVyXG4vLyAgIHRoZSBwYXJzZXIgZ290IHRvbyBjb25mdXNlZCB0byByZXR1cm4gYW55dGhpbmcgbWVhbmluZ2Z1bC5cbi8vXG4vLyBbYXBpXTogaHR0cHM6Ly9kZXZlbG9wZXIubW96aWxsYS5vcmcvZW4tVVMvZG9jcy9TcGlkZXJNb25rZXkvUGFyc2VyX0FQSVxuLy9cbi8vIFRoZSBleHBlY3RlZCB1c2UgZm9yIHRoaXMgaXMgdG8gKmZpcnN0KiB0cnkgYGFjb3JuLnBhcnNlYCwgYW5kIG9ubHlcbi8vIGlmIHRoYXQgZmFpbHMgc3dpdGNoIHRvIGBwYXJzZV9kYW1taXRgLiBUaGUgbG9vc2UgcGFyc2VyIG1pZ2h0XG4vLyBwYXJzZSBiYWRseSBpbmRlbnRlZCBjb2RlIGluY29ycmVjdGx5LCBzbyAqKmRvbid0KiogdXNlIGl0IGFzXG4vLyB5b3VyIGRlZmF1bHQgcGFyc2VyLlxuLy9cbi8vIFF1aXRlIGEgbG90IG9mIGFjb3JuLmpzIGlzIGR1cGxpY2F0ZWQgaGVyZS4gVGhlIGFsdGVybmF0aXZlIHdhcyB0b1xuLy8gYWRkIGEgKmxvdCogb2YgZXh0cmEgY3J1ZnQgdG8gdGhhdCBmaWxlLCBtYWtpbmcgaXQgbGVzcyByZWFkYWJsZVxuLy8gYW5kIHNsb3dlci4gQ29weWluZyBhbmQgZWRpdGluZyB0aGUgY29kZSBhbGxvd2VkIG1lIHRvIG1ha2Vcbi8vIGludmFzaXZlIGNoYW5nZXMgYW5kIHNpbXBsaWZpY2F0aW9ucyB3aXRob3V0IGNyZWF0aW5nIGEgY29tcGxpY2F0ZWRcbi8vIHRhbmdsZS5cblxuXCJ1c2Ugc3RyaWN0XCI7XG5cbmV4cG9ydHMuX19lc01vZHVsZSA9IHRydWU7XG5leHBvcnRzLnBhcnNlX2RhbW1pdCA9IHBhcnNlX2RhbW1pdDtcblxuZnVuY3Rpb24gX2ludGVyb3BSZXF1aXJlV2lsZGNhcmQob2JqKSB7IGlmIChvYmogJiYgb2JqLl9fZXNNb2R1bGUpIHsgcmV0dXJuIG9iajsgfSBlbHNlIHsgdmFyIG5ld09iaiA9IHt9OyBpZiAob2JqICE9IG51bGwpIHsgZm9yICh2YXIga2V5IGluIG9iaikgeyBpZiAoT2JqZWN0LnByb3RvdHlwZS5oYXNPd25Qcm9wZXJ0eS5jYWxsKG9iaiwga2V5KSkgbmV3T2JqW2tleV0gPSBvYmpba2V5XTsgfSB9IG5ld09ialtcImRlZmF1bHRcIl0gPSBvYmo7IHJldHVybiBuZXdPYmo7IH0gfVxuXG52YXIgXyA9IF9kZXJlcV8oXCIuLlwiKTtcblxudmFyIGFjb3JuID0gX2ludGVyb3BSZXF1aXJlV2lsZGNhcmQoXyk7XG5cbnZhciBfc3RhdGUgPSBfZGVyZXFfKFwiLi9zdGF0ZVwiKTtcblxuX2RlcmVxXyhcIi4vdG9rZW5pemVcIik7XG5cbl9kZXJlcV8oXCIuL3N0YXRlbWVudFwiKTtcblxuX2RlcmVxXyhcIi4vZXhwcmVzc2lvblwiKTtcblxuZXhwb3J0cy5Mb29zZVBhcnNlciA9IF9zdGF0ZS5Mb29zZVBhcnNlcjtcblxuYWNvcm4uZGVmYXVsdE9wdGlvbnMudGFiU2l6ZSA9IDQ7XG5cbmZ1bmN0aW9uIHBhcnNlX2RhbW1pdChpbnB1dCwgb3B0aW9ucykge1xuICB2YXIgcCA9IG5ldyBfc3RhdGUuTG9vc2VQYXJzZXIoaW5wdXQsIG9wdGlvbnMpO1xuICBwLm5leHQoKTtcbiAgcmV0dXJuIHAucGFyc2VUb3BMZXZlbCgpO1xufVxuXG5hY29ybi5wYXJzZV9kYW1taXQgPSBwYXJzZV9kYW1taXQ7XG5hY29ybi5Mb29zZVBhcnNlciA9IF9zdGF0ZS5Mb29zZVBhcnNlcjtcblxufSx7XCIuLlwiOjEsXCIuL2V4cHJlc3Npb25cIjoyLFwiLi9zdGF0ZVwiOjUsXCIuL3N0YXRlbWVudFwiOjYsXCIuL3Rva2VuaXplXCI6N31dLDQ6W2Z1bmN0aW9uKF9kZXJlcV8sbW9kdWxlLGV4cG9ydHMpe1xuXCJ1c2Ugc3RyaWN0XCI7XG5cbmV4cG9ydHMuX19lc01vZHVsZSA9IHRydWU7XG5leHBvcnRzLmlzRHVtbXkgPSBpc0R1bW15O1xuXG5mdW5jdGlvbiBpc0R1bW15KG5vZGUpIHtcbiAgcmV0dXJuIG5vZGUubmFtZSA9PSBcIuKcllwiO1xufVxuXG59LHt9XSw1OltmdW5jdGlvbihfZGVyZXFfLG1vZHVsZSxleHBvcnRzKXtcblwidXNlIHN0cmljdFwiO1xuXG5leHBvcnRzLl9fZXNNb2R1bGUgPSB0cnVlO1xuXG5mdW5jdGlvbiBfY2xhc3NDYWxsQ2hlY2soaW5zdGFuY2UsIENvbnN0cnVjdG9yKSB7IGlmICghKGluc3RhbmNlIGluc3RhbmNlb2YgQ29uc3RydWN0b3IpKSB7IHRocm93IG5ldyBUeXBlRXJyb3IoXCJDYW5ub3QgY2FsbCBhIGNsYXNzIGFzIGEgZnVuY3Rpb25cIik7IH0gfVxuXG52YXIgXyA9IF9kZXJlcV8oXCIuLlwiKTtcblxudmFyIExvb3NlUGFyc2VyID0gKGZ1bmN0aW9uICgpIHtcbiAgZnVuY3Rpb24gTG9vc2VQYXJzZXIoaW5wdXQsIG9wdGlvbnMpIHtcbiAgICBfY2xhc3NDYWxsQ2hlY2sodGhpcywgTG9vc2VQYXJzZXIpO1xuXG4gICAgdGhpcy50b2tzID0gXy50b2tlbml6ZXIoaW5wdXQsIG9wdGlvbnMpO1xuICAgIHRoaXMub3B0aW9ucyA9IHRoaXMudG9rcy5vcHRpb25zO1xuICAgIHRoaXMuaW5wdXQgPSB0aGlzLnRva3MuaW5wdXQ7XG4gICAgdGhpcy50b2sgPSB0aGlzLmxhc3QgPSB7IHR5cGU6IF8udG9rVHlwZXMuZW9mLCBzdGFydDogMCwgZW5kOiAwIH07XG4gICAgaWYgKHRoaXMub3B0aW9ucy5sb2NhdGlvbnMpIHtcbiAgICAgIHZhciBoZXJlID0gdGhpcy50b2tzLmN1clBvc2l0aW9uKCk7XG4gICAgICB0aGlzLnRvay5sb2MgPSBuZXcgXy5Tb3VyY2VMb2NhdGlvbih0aGlzLnRva3MsIGhlcmUsIGhlcmUpO1xuICAgIH1cbiAgICB0aGlzLmFoZWFkID0gW107IC8vIFRva2VucyBhaGVhZFxuICAgIHRoaXMuY29udGV4dCA9IFtdOyAvLyBJbmRlbnRhdGlvbiBjb250ZXh0ZWRcbiAgICB0aGlzLmN1ckluZGVudCA9IDA7XG4gICAgdGhpcy5jdXJMaW5lU3RhcnQgPSAwO1xuICAgIHRoaXMubmV4dExpbmVTdGFydCA9IHRoaXMubGluZUVuZCh0aGlzLmN1ckxpbmVTdGFydCkgKyAxO1xuICB9XG5cbiAgTG9vc2VQYXJzZXIucHJvdG90eXBlLnN0YXJ0Tm9kZSA9IGZ1bmN0aW9uIHN0YXJ0Tm9kZSgpIHtcbiAgICByZXR1cm4gbmV3IF8uTm9kZSh0aGlzLnRva3MsIHRoaXMudG9rLnN0YXJ0LCB0aGlzLm9wdGlvbnMubG9jYXRpb25zID8gdGhpcy50b2subG9jLnN0YXJ0IDogbnVsbCk7XG4gIH07XG5cbiAgTG9vc2VQYXJzZXIucHJvdG90eXBlLnN0b3JlQ3VycmVudFBvcyA9IGZ1bmN0aW9uIHN0b3JlQ3VycmVudFBvcygpIHtcbiAgICByZXR1cm4gdGhpcy5vcHRpb25zLmxvY2F0aW9ucyA/IFt0aGlzLnRvay5zdGFydCwgdGhpcy50b2subG9jLnN0YXJ0XSA6IHRoaXMudG9rLnN0YXJ0O1xuICB9O1xuXG4gIExvb3NlUGFyc2VyLnByb3RvdHlwZS5zdGFydE5vZGVBdCA9IGZ1bmN0aW9uIHN0YXJ0Tm9kZUF0KHBvcykge1xuICAgIGlmICh0aGlzLm9wdGlvbnMubG9jYXRpb25zKSB7XG4gICAgICByZXR1cm4gbmV3IF8uTm9kZSh0aGlzLnRva3MsIHBvc1swXSwgcG9zWzFdKTtcbiAgICB9IGVsc2Uge1xuICAgICAgcmV0dXJuIG5ldyBfLk5vZGUodGhpcy50b2tzLCBwb3MpO1xuICAgIH1cbiAgfTtcblxuICBMb29zZVBhcnNlci5wcm90b3R5cGUuZmluaXNoTm9kZSA9IGZ1bmN0aW9uIGZpbmlzaE5vZGUobm9kZSwgdHlwZSkge1xuICAgIG5vZGUudHlwZSA9IHR5cGU7XG4gICAgbm9kZS5lbmQgPSB0aGlzLmxhc3QuZW5kO1xuICAgIGlmICh0aGlzLm9wdGlvbnMubG9jYXRpb25zKSBub2RlLmxvYy5lbmQgPSB0aGlzLmxhc3QubG9jLmVuZDtcbiAgICBpZiAodGhpcy5vcHRpb25zLnJhbmdlcykgbm9kZS5yYW5nZVsxXSA9IHRoaXMubGFzdC5lbmQ7XG4gICAgcmV0dXJuIG5vZGU7XG4gIH07XG5cbiAgTG9vc2VQYXJzZXIucHJvdG90eXBlLmR1bW15SWRlbnQgPSBmdW5jdGlvbiBkdW1teUlkZW50KCkge1xuICAgIHZhciBkdW1teSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gICAgZHVtbXkubmFtZSA9IFwi4pyWXCI7XG4gICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShkdW1teSwgXCJJZGVudGlmaWVyXCIpO1xuICB9O1xuXG4gIExvb3NlUGFyc2VyLnByb3RvdHlwZS5kdW1teVN0cmluZyA9IGZ1bmN0aW9uIGR1bW15U3RyaW5nKCkge1xuICAgIHZhciBkdW1teSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gICAgZHVtbXkudmFsdWUgPSBkdW1teS5yYXcgPSBcIuKcllwiO1xuICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUoZHVtbXksIFwiTGl0ZXJhbFwiKTtcbiAgfTtcblxuICBMb29zZVBhcnNlci5wcm90b3R5cGUuZWF0ID0gZnVuY3Rpb24gZWF0KHR5cGUpIHtcbiAgICBpZiAodGhpcy50b2sudHlwZSA9PT0gdHlwZSkge1xuICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICByZXR1cm4gdHJ1ZTtcbiAgICB9IGVsc2Uge1xuICAgICAgcmV0dXJuIGZhbHNlO1xuICAgIH1cbiAgfTtcblxuICBMb29zZVBhcnNlci5wcm90b3R5cGUuaXNDb250ZXh0dWFsID0gZnVuY3Rpb24gaXNDb250ZXh0dWFsKG5hbWUpIHtcbiAgICByZXR1cm4gdGhpcy50b2sudHlwZSA9PT0gXy50b2tUeXBlcy5uYW1lICYmIHRoaXMudG9rLnZhbHVlID09PSBuYW1lO1xuICB9O1xuXG4gIExvb3NlUGFyc2VyLnByb3RvdHlwZS5lYXRDb250ZXh0dWFsID0gZnVuY3Rpb24gZWF0Q29udGV4dHVhbChuYW1lKSB7XG4gICAgcmV0dXJuIHRoaXMudG9rLnZhbHVlID09PSBuYW1lICYmIHRoaXMuZWF0KF8udG9rVHlwZXMubmFtZSk7XG4gIH07XG5cbiAgTG9vc2VQYXJzZXIucHJvdG90eXBlLmNhbkluc2VydFNlbWljb2xvbiA9IGZ1bmN0aW9uIGNhbkluc2VydFNlbWljb2xvbigpIHtcbiAgICByZXR1cm4gdGhpcy50b2sudHlwZSA9PT0gXy50b2tUeXBlcy5lb2YgfHwgdGhpcy50b2sudHlwZSA9PT0gXy50b2tUeXBlcy5icmFjZVIgfHwgXy5saW5lQnJlYWsudGVzdCh0aGlzLmlucHV0LnNsaWNlKHRoaXMubGFzdC5lbmQsIHRoaXMudG9rLnN0YXJ0KSk7XG4gIH07XG5cbiAgTG9vc2VQYXJzZXIucHJvdG90eXBlLnNlbWljb2xvbiA9IGZ1bmN0aW9uIHNlbWljb2xvbigpIHtcbiAgICByZXR1cm4gdGhpcy5lYXQoXy50b2tUeXBlcy5zZW1pKTtcbiAgfTtcblxuICBMb29zZVBhcnNlci5wcm90b3R5cGUuZXhwZWN0ID0gZnVuY3Rpb24gZXhwZWN0KHR5cGUpIHtcbiAgICBpZiAodGhpcy5lYXQodHlwZSkpIHJldHVybiB0cnVlO1xuICAgIGZvciAodmFyIGkgPSAxOyBpIDw9IDI7IGkrKykge1xuICAgICAgaWYgKHRoaXMubG9va0FoZWFkKGkpLnR5cGUgPT0gdHlwZSkge1xuICAgICAgICBmb3IgKHZhciBqID0gMDsgaiA8IGk7IGorKykge1xuICAgICAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgICB9cmV0dXJuIHRydWU7XG4gICAgICB9XG4gICAgfVxuICB9O1xuXG4gIExvb3NlUGFyc2VyLnByb3RvdHlwZS5wdXNoQ3ggPSBmdW5jdGlvbiBwdXNoQ3goKSB7XG4gICAgdGhpcy5jb250ZXh0LnB1c2godGhpcy5jdXJJbmRlbnQpO1xuICB9O1xuXG4gIExvb3NlUGFyc2VyLnByb3RvdHlwZS5wb3BDeCA9IGZ1bmN0aW9uIHBvcEN4KCkge1xuICAgIHRoaXMuY3VySW5kZW50ID0gdGhpcy5jb250ZXh0LnBvcCgpO1xuICB9O1xuXG4gIExvb3NlUGFyc2VyLnByb3RvdHlwZS5saW5lRW5kID0gZnVuY3Rpb24gbGluZUVuZChwb3MpIHtcbiAgICB3aGlsZSAocG9zIDwgdGhpcy5pbnB1dC5sZW5ndGggJiYgIV8uaXNOZXdMaW5lKHRoaXMuaW5wdXQuY2hhckNvZGVBdChwb3MpKSkgKytwb3M7XG4gICAgcmV0dXJuIHBvcztcbiAgfTtcblxuICBMb29zZVBhcnNlci5wcm90b3R5cGUuaW5kZW50YXRpb25BZnRlciA9IGZ1bmN0aW9uIGluZGVudGF0aW9uQWZ0ZXIocG9zKSB7XG4gICAgZm9yICh2YXIgY291bnQgPSAwOzsgKytwb3MpIHtcbiAgICAgIHZhciBjaCA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdChwb3MpO1xuICAgICAgaWYgKGNoID09PSAzMikgKytjb3VudDtlbHNlIGlmIChjaCA9PT0gOSkgY291bnQgKz0gdGhpcy5vcHRpb25zLnRhYlNpemU7ZWxzZSByZXR1cm4gY291bnQ7XG4gICAgfVxuICB9O1xuXG4gIExvb3NlUGFyc2VyLnByb3RvdHlwZS5jbG9zZXMgPSBmdW5jdGlvbiBjbG9zZXMoY2xvc2VUb2ssIGluZGVudCwgbGluZSwgYmxvY2tIZXVyaXN0aWMpIHtcbiAgICBpZiAodGhpcy50b2sudHlwZSA9PT0gY2xvc2VUb2sgfHwgdGhpcy50b2sudHlwZSA9PT0gXy50b2tUeXBlcy5lb2YpIHJldHVybiB0cnVlO1xuICAgIHJldHVybiBsaW5lICE9IHRoaXMuY3VyTGluZVN0YXJ0ICYmIHRoaXMuY3VySW5kZW50IDwgaW5kZW50ICYmIHRoaXMudG9rZW5TdGFydHNMaW5lKCkgJiYgKCFibG9ja0hldXJpc3RpYyB8fCB0aGlzLm5leHRMaW5lU3RhcnQgPj0gdGhpcy5pbnB1dC5sZW5ndGggfHwgdGhpcy5pbmRlbnRhdGlvbkFmdGVyKHRoaXMubmV4dExpbmVTdGFydCkgPCBpbmRlbnQpO1xuICB9O1xuXG4gIExvb3NlUGFyc2VyLnByb3RvdHlwZS50b2tlblN0YXJ0c0xpbmUgPSBmdW5jdGlvbiB0b2tlblN0YXJ0c0xpbmUoKSB7XG4gICAgZm9yICh2YXIgcCA9IHRoaXMudG9rLnN0YXJ0IC0gMTsgcCA+PSB0aGlzLmN1ckxpbmVTdGFydDsgLS1wKSB7XG4gICAgICB2YXIgY2ggPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQocCk7XG4gICAgICBpZiAoY2ggIT09IDkgJiYgY2ggIT09IDMyKSByZXR1cm4gZmFsc2U7XG4gICAgfVxuICAgIHJldHVybiB0cnVlO1xuICB9O1xuXG4gIHJldHVybiBMb29zZVBhcnNlcjtcbn0pKCk7XG5cbmV4cG9ydHMuTG9vc2VQYXJzZXIgPSBMb29zZVBhcnNlcjtcblxufSx7XCIuLlwiOjF9XSw2OltmdW5jdGlvbihfZGVyZXFfLG1vZHVsZSxleHBvcnRzKXtcblwidXNlIHN0cmljdFwiO1xuXG52YXIgX3N0YXRlID0gX2RlcmVxXyhcIi4vc3RhdGVcIik7XG5cbnZhciBfcGFyc2V1dGlsID0gX2RlcmVxXyhcIi4vcGFyc2V1dGlsXCIpO1xuXG52YXIgXyA9IF9kZXJlcV8oXCIuLlwiKTtcblxudmFyIGxwID0gX3N0YXRlLkxvb3NlUGFyc2VyLnByb3RvdHlwZTtcblxubHAucGFyc2VUb3BMZXZlbCA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZUF0KHRoaXMub3B0aW9ucy5sb2NhdGlvbnMgPyBbMCwgXy5nZXRMaW5lSW5mbyh0aGlzLmlucHV0LCAwKV0gOiAwKTtcbiAgbm9kZS5ib2R5ID0gW107XG4gIHdoaWxlICh0aGlzLnRvay50eXBlICE9PSBfLnRva1R5cGVzLmVvZikgbm9kZS5ib2R5LnB1c2godGhpcy5wYXJzZVN0YXRlbWVudCgpKTtcbiAgdGhpcy5sYXN0ID0gdGhpcy50b2s7XG4gIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNikge1xuICAgIG5vZGUuc291cmNlVHlwZSA9IHRoaXMub3B0aW9ucy5zb3VyY2VUeXBlO1xuICB9XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJQcm9ncmFtXCIpO1xufTtcblxubHAucGFyc2VTdGF0ZW1lbnQgPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBzdGFydHR5cGUgPSB0aGlzLnRvay50eXBlLFxuICAgICAgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG5cbiAgc3dpdGNoIChzdGFydHR5cGUpIHtcbiAgICBjYXNlIF8udG9rVHlwZXMuX2JyZWFrOmNhc2UgXy50b2tUeXBlcy5fY29udGludWU6XG4gICAgICB0aGlzLm5leHQoKTtcbiAgICAgIHZhciBpc0JyZWFrID0gc3RhcnR0eXBlID09PSBfLnRva1R5cGVzLl9icmVhaztcbiAgICAgIGlmICh0aGlzLnNlbWljb2xvbigpIHx8IHRoaXMuY2FuSW5zZXJ0U2VtaWNvbG9uKCkpIHtcbiAgICAgICAgbm9kZS5sYWJlbCA9IG51bGw7XG4gICAgICB9IGVsc2Uge1xuICAgICAgICBub2RlLmxhYmVsID0gdGhpcy50b2sudHlwZSA9PT0gXy50b2tUeXBlcy5uYW1lID8gdGhpcy5wYXJzZUlkZW50KCkgOiBudWxsO1xuICAgICAgICB0aGlzLnNlbWljb2xvbigpO1xuICAgICAgfVxuICAgICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBpc0JyZWFrID8gXCJCcmVha1N0YXRlbWVudFwiIDogXCJDb250aW51ZVN0YXRlbWVudFwiKTtcblxuICAgIGNhc2UgXy50b2tUeXBlcy5fZGVidWdnZXI6XG4gICAgICB0aGlzLm5leHQoKTtcbiAgICAgIHRoaXMuc2VtaWNvbG9uKCk7XG4gICAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiRGVidWdnZXJTdGF0ZW1lbnRcIik7XG5cbiAgICBjYXNlIF8udG9rVHlwZXMuX2RvOlxuICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICBub2RlLmJvZHkgPSB0aGlzLnBhcnNlU3RhdGVtZW50KCk7XG4gICAgICBub2RlLnRlc3QgPSB0aGlzLmVhdChfLnRva1R5cGVzLl93aGlsZSkgPyB0aGlzLnBhcnNlUGFyZW5FeHByZXNzaW9uKCkgOiB0aGlzLmR1bW15SWRlbnQoKTtcbiAgICAgIHRoaXMuc2VtaWNvbG9uKCk7XG4gICAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiRG9XaGlsZVN0YXRlbWVudFwiKTtcblxuICAgIGNhc2UgXy50b2tUeXBlcy5fZm9yOlxuICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICB0aGlzLnB1c2hDeCgpO1xuICAgICAgdGhpcy5leHBlY3QoXy50b2tUeXBlcy5wYXJlbkwpO1xuICAgICAgaWYgKHRoaXMudG9rLnR5cGUgPT09IF8udG9rVHlwZXMuc2VtaSkgcmV0dXJuIHRoaXMucGFyc2VGb3Iobm9kZSwgbnVsbCk7XG4gICAgICBpZiAodGhpcy50b2sudHlwZSA9PT0gXy50b2tUeXBlcy5fdmFyIHx8IHRoaXMudG9rLnR5cGUgPT09IF8udG9rVHlwZXMuX2xldCB8fCB0aGlzLnRvay50eXBlID09PSBfLnRva1R5cGVzLl9jb25zdCkge1xuICAgICAgICB2YXIgX2luaXQgPSB0aGlzLnBhcnNlVmFyKHRydWUpO1xuICAgICAgICBpZiAoX2luaXQuZGVjbGFyYXRpb25zLmxlbmd0aCA9PT0gMSAmJiAodGhpcy50b2sudHlwZSA9PT0gXy50b2tUeXBlcy5faW4gfHwgdGhpcy5pc0NvbnRleHR1YWwoXCJvZlwiKSkpIHtcbiAgICAgICAgICByZXR1cm4gdGhpcy5wYXJzZUZvckluKG5vZGUsIF9pbml0KTtcbiAgICAgICAgfVxuICAgICAgICByZXR1cm4gdGhpcy5wYXJzZUZvcihub2RlLCBfaW5pdCk7XG4gICAgICB9XG4gICAgICB2YXIgaW5pdCA9IHRoaXMucGFyc2VFeHByZXNzaW9uKHRydWUpO1xuICAgICAgaWYgKHRoaXMudG9rLnR5cGUgPT09IF8udG9rVHlwZXMuX2luIHx8IHRoaXMuaXNDb250ZXh0dWFsKFwib2ZcIikpIHJldHVybiB0aGlzLnBhcnNlRm9ySW4obm9kZSwgdGhpcy50b0Fzc2lnbmFibGUoaW5pdCkpO1xuICAgICAgcmV0dXJuIHRoaXMucGFyc2VGb3Iobm9kZSwgaW5pdCk7XG5cbiAgICBjYXNlIF8udG9rVHlwZXMuX2Z1bmN0aW9uOlxuICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZUZ1bmN0aW9uKG5vZGUsIHRydWUpO1xuXG4gICAgY2FzZSBfLnRva1R5cGVzLl9pZjpcbiAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgbm9kZS50ZXN0ID0gdGhpcy5wYXJzZVBhcmVuRXhwcmVzc2lvbigpO1xuICAgICAgbm9kZS5jb25zZXF1ZW50ID0gdGhpcy5wYXJzZVN0YXRlbWVudCgpO1xuICAgICAgbm9kZS5hbHRlcm5hdGUgPSB0aGlzLmVhdChfLnRva1R5cGVzLl9lbHNlKSA/IHRoaXMucGFyc2VTdGF0ZW1lbnQoKSA6IG51bGw7XG4gICAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiSWZTdGF0ZW1lbnRcIik7XG5cbiAgICBjYXNlIF8udG9rVHlwZXMuX3JldHVybjpcbiAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgaWYgKHRoaXMuZWF0KF8udG9rVHlwZXMuc2VtaSkgfHwgdGhpcy5jYW5JbnNlcnRTZW1pY29sb24oKSkgbm9kZS5hcmd1bWVudCA9IG51bGw7ZWxzZSB7XG4gICAgICAgIG5vZGUuYXJndW1lbnQgPSB0aGlzLnBhcnNlRXhwcmVzc2lvbigpO3RoaXMuc2VtaWNvbG9uKCk7XG4gICAgICB9XG4gICAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiUmV0dXJuU3RhdGVtZW50XCIpO1xuXG4gICAgY2FzZSBfLnRva1R5cGVzLl9zd2l0Y2g6XG4gICAgICB2YXIgYmxvY2tJbmRlbnQgPSB0aGlzLmN1ckluZGVudCxcbiAgICAgICAgICBsaW5lID0gdGhpcy5jdXJMaW5lU3RhcnQ7XG4gICAgICB0aGlzLm5leHQoKTtcbiAgICAgIG5vZGUuZGlzY3JpbWluYW50ID0gdGhpcy5wYXJzZVBhcmVuRXhwcmVzc2lvbigpO1xuICAgICAgbm9kZS5jYXNlcyA9IFtdO1xuICAgICAgdGhpcy5wdXNoQ3goKTtcbiAgICAgIHRoaXMuZXhwZWN0KF8udG9rVHlwZXMuYnJhY2VMKTtcblxuICAgICAgdmFyIGN1ciA9IHVuZGVmaW5lZDtcbiAgICAgIHdoaWxlICghdGhpcy5jbG9zZXMoXy50b2tUeXBlcy5icmFjZVIsIGJsb2NrSW5kZW50LCBsaW5lLCB0cnVlKSkge1xuICAgICAgICBpZiAodGhpcy50b2sudHlwZSA9PT0gXy50b2tUeXBlcy5fY2FzZSB8fCB0aGlzLnRvay50eXBlID09PSBfLnRva1R5cGVzLl9kZWZhdWx0KSB7XG4gICAgICAgICAgdmFyIGlzQ2FzZSA9IHRoaXMudG9rLnR5cGUgPT09IF8udG9rVHlwZXMuX2Nhc2U7XG4gICAgICAgICAgaWYgKGN1cikgdGhpcy5maW5pc2hOb2RlKGN1ciwgXCJTd2l0Y2hDYXNlXCIpO1xuICAgICAgICAgIG5vZGUuY2FzZXMucHVzaChjdXIgPSB0aGlzLnN0YXJ0Tm9kZSgpKTtcbiAgICAgICAgICBjdXIuY29uc2VxdWVudCA9IFtdO1xuICAgICAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgICAgIGlmIChpc0Nhc2UpIGN1ci50ZXN0ID0gdGhpcy5wYXJzZUV4cHJlc3Npb24oKTtlbHNlIGN1ci50ZXN0ID0gbnVsbDtcbiAgICAgICAgICB0aGlzLmV4cGVjdChfLnRva1R5cGVzLmNvbG9uKTtcbiAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICBpZiAoIWN1cikge1xuICAgICAgICAgICAgbm9kZS5jYXNlcy5wdXNoKGN1ciA9IHRoaXMuc3RhcnROb2RlKCkpO1xuICAgICAgICAgICAgY3VyLmNvbnNlcXVlbnQgPSBbXTtcbiAgICAgICAgICAgIGN1ci50ZXN0ID0gbnVsbDtcbiAgICAgICAgICB9XG4gICAgICAgICAgY3VyLmNvbnNlcXVlbnQucHVzaCh0aGlzLnBhcnNlU3RhdGVtZW50KCkpO1xuICAgICAgICB9XG4gICAgICB9XG4gICAgICBpZiAoY3VyKSB0aGlzLmZpbmlzaE5vZGUoY3VyLCBcIlN3aXRjaENhc2VcIik7XG4gICAgICB0aGlzLnBvcEN4KCk7XG4gICAgICB0aGlzLmVhdChfLnRva1R5cGVzLmJyYWNlUik7XG4gICAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiU3dpdGNoU3RhdGVtZW50XCIpO1xuXG4gICAgY2FzZSBfLnRva1R5cGVzLl90aHJvdzpcbiAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgbm9kZS5hcmd1bWVudCA9IHRoaXMucGFyc2VFeHByZXNzaW9uKCk7XG4gICAgICB0aGlzLnNlbWljb2xvbigpO1xuICAgICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIlRocm93U3RhdGVtZW50XCIpO1xuXG4gICAgY2FzZSBfLnRva1R5cGVzLl90cnk6XG4gICAgICB0aGlzLm5leHQoKTtcbiAgICAgIG5vZGUuYmxvY2sgPSB0aGlzLnBhcnNlQmxvY2soKTtcbiAgICAgIG5vZGUuaGFuZGxlciA9IG51bGw7XG4gICAgICBpZiAodGhpcy50b2sudHlwZSA9PT0gXy50b2tUeXBlcy5fY2F0Y2gpIHtcbiAgICAgICAgdmFyIGNsYXVzZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gICAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgICB0aGlzLmV4cGVjdChfLnRva1R5cGVzLnBhcmVuTCk7XG4gICAgICAgIGNsYXVzZS5wYXJhbSA9IHRoaXMudG9Bc3NpZ25hYmxlKHRoaXMucGFyc2VFeHByQXRvbSgpLCB0cnVlKTtcbiAgICAgICAgdGhpcy5leHBlY3QoXy50b2tUeXBlcy5wYXJlblIpO1xuICAgICAgICBjbGF1c2UuZ3VhcmQgPSBudWxsO1xuICAgICAgICBjbGF1c2UuYm9keSA9IHRoaXMucGFyc2VCbG9jaygpO1xuICAgICAgICBub2RlLmhhbmRsZXIgPSB0aGlzLmZpbmlzaE5vZGUoY2xhdXNlLCBcIkNhdGNoQ2xhdXNlXCIpO1xuICAgICAgfVxuICAgICAgbm9kZS5maW5hbGl6ZXIgPSB0aGlzLmVhdChfLnRva1R5cGVzLl9maW5hbGx5KSA/IHRoaXMucGFyc2VCbG9jaygpIDogbnVsbDtcbiAgICAgIGlmICghbm9kZS5oYW5kbGVyICYmICFub2RlLmZpbmFsaXplcikgcmV0dXJuIG5vZGUuYmxvY2s7XG4gICAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiVHJ5U3RhdGVtZW50XCIpO1xuXG4gICAgY2FzZSBfLnRva1R5cGVzLl92YXI6XG4gICAgY2FzZSBfLnRva1R5cGVzLl9sZXQ6XG4gICAgY2FzZSBfLnRva1R5cGVzLl9jb25zdDpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlVmFyKCk7XG5cbiAgICBjYXNlIF8udG9rVHlwZXMuX3doaWxlOlxuICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICBub2RlLnRlc3QgPSB0aGlzLnBhcnNlUGFyZW5FeHByZXNzaW9uKCk7XG4gICAgICBub2RlLmJvZHkgPSB0aGlzLnBhcnNlU3RhdGVtZW50KCk7XG4gICAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiV2hpbGVTdGF0ZW1lbnRcIik7XG5cbiAgICBjYXNlIF8udG9rVHlwZXMuX3dpdGg6XG4gICAgICB0aGlzLm5leHQoKTtcbiAgICAgIG5vZGUub2JqZWN0ID0gdGhpcy5wYXJzZVBhcmVuRXhwcmVzc2lvbigpO1xuICAgICAgbm9kZS5ib2R5ID0gdGhpcy5wYXJzZVN0YXRlbWVudCgpO1xuICAgICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIldpdGhTdGF0ZW1lbnRcIik7XG5cbiAgICBjYXNlIF8udG9rVHlwZXMuYnJhY2VMOlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VCbG9jaygpO1xuXG4gICAgY2FzZSBfLnRva1R5cGVzLnNlbWk6XG4gICAgICB0aGlzLm5leHQoKTtcbiAgICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJFbXB0eVN0YXRlbWVudFwiKTtcblxuICAgIGNhc2UgXy50b2tUeXBlcy5fY2xhc3M6XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZUNsYXNzKHRydWUpO1xuXG4gICAgY2FzZSBfLnRva1R5cGVzLl9pbXBvcnQ6XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZUltcG9ydCgpO1xuXG4gICAgY2FzZSBfLnRva1R5cGVzLl9leHBvcnQ6XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZUV4cG9ydCgpO1xuXG4gICAgZGVmYXVsdDpcbiAgICAgIHZhciBleHByID0gdGhpcy5wYXJzZUV4cHJlc3Npb24oKTtcbiAgICAgIGlmIChfcGFyc2V1dGlsLmlzRHVtbXkoZXhwcikpIHtcbiAgICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICAgIGlmICh0aGlzLnRvay50eXBlID09PSBfLnRva1R5cGVzLmVvZikgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkVtcHR5U3RhdGVtZW50XCIpO1xuICAgICAgICByZXR1cm4gdGhpcy5wYXJzZVN0YXRlbWVudCgpO1xuICAgICAgfSBlbHNlIGlmIChzdGFydHR5cGUgPT09IF8udG9rVHlwZXMubmFtZSAmJiBleHByLnR5cGUgPT09IFwiSWRlbnRpZmllclwiICYmIHRoaXMuZWF0KF8udG9rVHlwZXMuY29sb24pKSB7XG4gICAgICAgIG5vZGUuYm9keSA9IHRoaXMucGFyc2VTdGF0ZW1lbnQoKTtcbiAgICAgICAgbm9kZS5sYWJlbCA9IGV4cHI7XG4gICAgICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJMYWJlbGVkU3RhdGVtZW50XCIpO1xuICAgICAgfSBlbHNlIHtcbiAgICAgICAgbm9kZS5leHByZXNzaW9uID0gZXhwcjtcbiAgICAgICAgdGhpcy5zZW1pY29sb24oKTtcbiAgICAgICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkV4cHJlc3Npb25TdGF0ZW1lbnRcIik7XG4gICAgICB9XG4gIH1cbn07XG5cbmxwLnBhcnNlQmxvY2sgPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgdGhpcy5wdXNoQ3goKTtcbiAgdGhpcy5leHBlY3QoXy50b2tUeXBlcy5icmFjZUwpO1xuICB2YXIgYmxvY2tJbmRlbnQgPSB0aGlzLmN1ckluZGVudCxcbiAgICAgIGxpbmUgPSB0aGlzLmN1ckxpbmVTdGFydDtcbiAgbm9kZS5ib2R5ID0gW107XG4gIHdoaWxlICghdGhpcy5jbG9zZXMoXy50b2tUeXBlcy5icmFjZVIsIGJsb2NrSW5kZW50LCBsaW5lLCB0cnVlKSkgbm9kZS5ib2R5LnB1c2godGhpcy5wYXJzZVN0YXRlbWVudCgpKTtcbiAgdGhpcy5wb3BDeCgpO1xuICB0aGlzLmVhdChfLnRva1R5cGVzLmJyYWNlUik7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJCbG9ja1N0YXRlbWVudFwiKTtcbn07XG5cbmxwLnBhcnNlRm9yID0gZnVuY3Rpb24gKG5vZGUsIGluaXQpIHtcbiAgbm9kZS5pbml0ID0gaW5pdDtcbiAgbm9kZS50ZXN0ID0gbm9kZS51cGRhdGUgPSBudWxsO1xuICBpZiAodGhpcy5lYXQoXy50b2tUeXBlcy5zZW1pKSAmJiB0aGlzLnRvay50eXBlICE9PSBfLnRva1R5cGVzLnNlbWkpIG5vZGUudGVzdCA9IHRoaXMucGFyc2VFeHByZXNzaW9uKCk7XG4gIGlmICh0aGlzLmVhdChfLnRva1R5cGVzLnNlbWkpICYmIHRoaXMudG9rLnR5cGUgIT09IF8udG9rVHlwZXMucGFyZW5SKSBub2RlLnVwZGF0ZSA9IHRoaXMucGFyc2VFeHByZXNzaW9uKCk7XG4gIHRoaXMucG9wQ3goKTtcbiAgdGhpcy5leHBlY3QoXy50b2tUeXBlcy5wYXJlblIpO1xuICBub2RlLmJvZHkgPSB0aGlzLnBhcnNlU3RhdGVtZW50KCk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJGb3JTdGF0ZW1lbnRcIik7XG59O1xuXG5scC5wYXJzZUZvckluID0gZnVuY3Rpb24gKG5vZGUsIGluaXQpIHtcbiAgdmFyIHR5cGUgPSB0aGlzLnRvay50eXBlID09PSBfLnRva1R5cGVzLl9pbiA/IFwiRm9ySW5TdGF0ZW1lbnRcIiA6IFwiRm9yT2ZTdGF0ZW1lbnRcIjtcbiAgdGhpcy5uZXh0KCk7XG4gIG5vZGUubGVmdCA9IGluaXQ7XG4gIG5vZGUucmlnaHQgPSB0aGlzLnBhcnNlRXhwcmVzc2lvbigpO1xuICB0aGlzLnBvcEN4KCk7XG4gIHRoaXMuZXhwZWN0KF8udG9rVHlwZXMucGFyZW5SKTtcbiAgbm9kZS5ib2R5ID0gdGhpcy5wYXJzZVN0YXRlbWVudCgpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIHR5cGUpO1xufTtcblxubHAucGFyc2VWYXIgPSBmdW5jdGlvbiAobm9Jbikge1xuICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gIG5vZGUua2luZCA9IHRoaXMudG9rLnR5cGUua2V5d29yZDtcbiAgdGhpcy5uZXh0KCk7XG4gIG5vZGUuZGVjbGFyYXRpb25zID0gW107XG4gIGRvIHtcbiAgICB2YXIgZGVjbCA9IHRoaXMuc3RhcnROb2RlKCk7XG4gICAgZGVjbC5pZCA9IHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2ID8gdGhpcy50b0Fzc2lnbmFibGUodGhpcy5wYXJzZUV4cHJBdG9tKCksIHRydWUpIDogdGhpcy5wYXJzZUlkZW50KCk7XG4gICAgZGVjbC5pbml0ID0gdGhpcy5lYXQoXy50b2tUeXBlcy5lcSkgPyB0aGlzLnBhcnNlTWF5YmVBc3NpZ24obm9JbikgOiBudWxsO1xuICAgIG5vZGUuZGVjbGFyYXRpb25zLnB1c2godGhpcy5maW5pc2hOb2RlKGRlY2wsIFwiVmFyaWFibGVEZWNsYXJhdG9yXCIpKTtcbiAgfSB3aGlsZSAodGhpcy5lYXQoXy50b2tUeXBlcy5jb21tYSkpO1xuICBpZiAoIW5vZGUuZGVjbGFyYXRpb25zLmxlbmd0aCkge1xuICAgIHZhciBkZWNsID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgICBkZWNsLmlkID0gdGhpcy5kdW1teUlkZW50KCk7XG4gICAgbm9kZS5kZWNsYXJhdGlvbnMucHVzaCh0aGlzLmZpbmlzaE5vZGUoZGVjbCwgXCJWYXJpYWJsZURlY2xhcmF0b3JcIikpO1xuICB9XG4gIGlmICghbm9JbikgdGhpcy5zZW1pY29sb24oKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIlZhcmlhYmxlRGVjbGFyYXRpb25cIik7XG59O1xuXG5scC5wYXJzZUNsYXNzID0gZnVuY3Rpb24gKGlzU3RhdGVtZW50KSB7XG4gIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgdGhpcy5uZXh0KCk7XG4gIGlmICh0aGlzLnRvay50eXBlID09PSBfLnRva1R5cGVzLm5hbWUpIG5vZGUuaWQgPSB0aGlzLnBhcnNlSWRlbnQoKTtlbHNlIGlmIChpc1N0YXRlbWVudCkgbm9kZS5pZCA9IHRoaXMuZHVtbXlJZGVudCgpO2Vsc2Ugbm9kZS5pZCA9IG51bGw7XG4gIG5vZGUuc3VwZXJDbGFzcyA9IHRoaXMuZWF0KF8udG9rVHlwZXMuX2V4dGVuZHMpID8gdGhpcy5wYXJzZUV4cHJlc3Npb24oKSA6IG51bGw7XG4gIG5vZGUuYm9keSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gIG5vZGUuYm9keS5ib2R5ID0gW107XG4gIHRoaXMucHVzaEN4KCk7XG4gIHZhciBpbmRlbnQgPSB0aGlzLmN1ckluZGVudCArIDEsXG4gICAgICBsaW5lID0gdGhpcy5jdXJMaW5lU3RhcnQ7XG4gIHRoaXMuZWF0KF8udG9rVHlwZXMuYnJhY2VMKTtcbiAgaWYgKHRoaXMuY3VySW5kZW50ICsgMSA8IGluZGVudCkge1xuICAgIGluZGVudCA9IHRoaXMuY3VySW5kZW50O2xpbmUgPSB0aGlzLmN1ckxpbmVTdGFydDtcbiAgfVxuICB3aGlsZSAoIXRoaXMuY2xvc2VzKF8udG9rVHlwZXMuYnJhY2VSLCBpbmRlbnQsIGxpbmUpKSB7XG4gICAgaWYgKHRoaXMuc2VtaWNvbG9uKCkpIGNvbnRpbnVlO1xuICAgIHZhciBtZXRob2QgPSB0aGlzLnN0YXJ0Tm9kZSgpLFxuICAgICAgICBpc0dlbmVyYXRvciA9IHVuZGVmaW5lZDtcbiAgICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYpIHtcbiAgICAgIG1ldGhvZFtcInN0YXRpY1wiXSA9IGZhbHNlO1xuICAgICAgaXNHZW5lcmF0b3IgPSB0aGlzLmVhdChfLnRva1R5cGVzLnN0YXIpO1xuICAgIH1cbiAgICB0aGlzLnBhcnNlUHJvcGVydHlOYW1lKG1ldGhvZCk7XG4gICAgaWYgKF9wYXJzZXV0aWwuaXNEdW1teShtZXRob2Qua2V5KSkge1xuICAgICAgaWYgKF9wYXJzZXV0aWwuaXNEdW1teSh0aGlzLnBhcnNlTWF5YmVBc3NpZ24oKSkpIHRoaXMubmV4dCgpO3RoaXMuZWF0KF8udG9rVHlwZXMuY29tbWEpO2NvbnRpbnVlO1xuICAgIH1cbiAgICBpZiAobWV0aG9kLmtleS50eXBlID09PSBcIklkZW50aWZpZXJcIiAmJiAhbWV0aG9kLmNvbXB1dGVkICYmIG1ldGhvZC5rZXkubmFtZSA9PT0gXCJzdGF0aWNcIiAmJiAodGhpcy50b2sudHlwZSAhPSBfLnRva1R5cGVzLnBhcmVuTCAmJiB0aGlzLnRvay50eXBlICE9IF8udG9rVHlwZXMuYnJhY2VMKSkge1xuICAgICAgbWV0aG9kW1wic3RhdGljXCJdID0gdHJ1ZTtcbiAgICAgIGlzR2VuZXJhdG9yID0gdGhpcy5lYXQoXy50b2tUeXBlcy5zdGFyKTtcbiAgICAgIHRoaXMucGFyc2VQcm9wZXJ0eU5hbWUobWV0aG9kKTtcbiAgICB9IGVsc2Uge1xuICAgICAgbWV0aG9kW1wic3RhdGljXCJdID0gZmFsc2U7XG4gICAgfVxuICAgIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNSAmJiBtZXRob2Qua2V5LnR5cGUgPT09IFwiSWRlbnRpZmllclwiICYmICFtZXRob2QuY29tcHV0ZWQgJiYgKG1ldGhvZC5rZXkubmFtZSA9PT0gXCJnZXRcIiB8fCBtZXRob2Qua2V5Lm5hbWUgPT09IFwic2V0XCIpICYmIHRoaXMudG9rLnR5cGUgIT09IF8udG9rVHlwZXMucGFyZW5MICYmIHRoaXMudG9rLnR5cGUgIT09IF8udG9rVHlwZXMuYnJhY2VMKSB7XG4gICAgICBtZXRob2Qua2luZCA9IG1ldGhvZC5rZXkubmFtZTtcbiAgICAgIHRoaXMucGFyc2VQcm9wZXJ0eU5hbWUobWV0aG9kKTtcbiAgICAgIG1ldGhvZC52YWx1ZSA9IHRoaXMucGFyc2VNZXRob2QoZmFsc2UpO1xuICAgIH0gZWxzZSB7XG4gICAgICBpZiAoIW1ldGhvZC5jb21wdXRlZCAmJiAhbWV0aG9kW1wic3RhdGljXCJdICYmICFpc0dlbmVyYXRvciAmJiAobWV0aG9kLmtleS50eXBlID09PSBcIklkZW50aWZpZXJcIiAmJiBtZXRob2Qua2V5Lm5hbWUgPT09IFwiY29uc3RydWN0b3JcIiB8fCBtZXRob2Qua2V5LnR5cGUgPT09IFwiTGl0ZXJhbFwiICYmIG1ldGhvZC5rZXkudmFsdWUgPT09IFwiY29uc3RydWN0b3JcIikpIHtcbiAgICAgICAgbWV0aG9kLmtpbmQgPSBcImNvbnN0cnVjdG9yXCI7XG4gICAgICB9IGVsc2Uge1xuICAgICAgICBtZXRob2Qua2luZCA9IFwibWV0aG9kXCI7XG4gICAgICB9XG4gICAgICBtZXRob2QudmFsdWUgPSB0aGlzLnBhcnNlTWV0aG9kKGlzR2VuZXJhdG9yKTtcbiAgICB9XG4gICAgbm9kZS5ib2R5LmJvZHkucHVzaCh0aGlzLmZpbmlzaE5vZGUobWV0aG9kLCBcIk1ldGhvZERlZmluaXRpb25cIikpO1xuICB9XG4gIHRoaXMucG9wQ3goKTtcbiAgaWYgKCF0aGlzLmVhdChfLnRva1R5cGVzLmJyYWNlUikpIHtcbiAgICAvLyBJZiB0aGVyZSBpcyBubyBjbG9zaW5nIGJyYWNlLCBtYWtlIHRoZSBub2RlIHNwYW4gdG8gdGhlIHN0YXJ0XG4gICAgLy8gb2YgdGhlIG5leHQgdG9rZW4gKHRoaXMgaXMgdXNlZnVsIGZvciBUZXJuKVxuICAgIHRoaXMubGFzdC5lbmQgPSB0aGlzLnRvay5zdGFydDtcbiAgICBpZiAodGhpcy5vcHRpb25zLmxvY2F0aW9ucykgdGhpcy5sYXN0LmxvYy5lbmQgPSB0aGlzLnRvay5sb2Muc3RhcnQ7XG4gIH1cbiAgdGhpcy5zZW1pY29sb24oKTtcbiAgdGhpcy5maW5pc2hOb2RlKG5vZGUuYm9keSwgXCJDbGFzc0JvZHlcIik7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgaXNTdGF0ZW1lbnQgPyBcIkNsYXNzRGVjbGFyYXRpb25cIiA6IFwiQ2xhc3NFeHByZXNzaW9uXCIpO1xufTtcblxubHAucGFyc2VGdW5jdGlvbiA9IGZ1bmN0aW9uIChub2RlLCBpc1N0YXRlbWVudCkge1xuICB0aGlzLmluaXRGdW5jdGlvbihub2RlKTtcbiAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KSB7XG4gICAgbm9kZS5nZW5lcmF0b3IgPSB0aGlzLmVhdChfLnRva1R5cGVzLnN0YXIpO1xuICB9XG4gIGlmICh0aGlzLnRvay50eXBlID09PSBfLnRva1R5cGVzLm5hbWUpIG5vZGUuaWQgPSB0aGlzLnBhcnNlSWRlbnQoKTtlbHNlIGlmIChpc1N0YXRlbWVudCkgbm9kZS5pZCA9IHRoaXMuZHVtbXlJZGVudCgpO1xuICBub2RlLnBhcmFtcyA9IHRoaXMucGFyc2VGdW5jdGlvblBhcmFtcygpO1xuICBub2RlLmJvZHkgPSB0aGlzLnBhcnNlQmxvY2soKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBpc1N0YXRlbWVudCA/IFwiRnVuY3Rpb25EZWNsYXJhdGlvblwiIDogXCJGdW5jdGlvbkV4cHJlc3Npb25cIik7XG59O1xuXG5scC5wYXJzZUV4cG9ydCA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICB0aGlzLm5leHQoKTtcbiAgaWYgKHRoaXMuZWF0KF8udG9rVHlwZXMuc3RhcikpIHtcbiAgICBub2RlLnNvdXJjZSA9IHRoaXMuZWF0Q29udGV4dHVhbChcImZyb21cIikgPyB0aGlzLnBhcnNlRXhwckF0b20oKSA6IG51bGw7XG4gICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkV4cG9ydEFsbERlY2xhcmF0aW9uXCIpO1xuICB9XG4gIGlmICh0aGlzLmVhdChfLnRva1R5cGVzLl9kZWZhdWx0KSkge1xuICAgIHZhciBleHByID0gdGhpcy5wYXJzZU1heWJlQXNzaWduKCk7XG4gICAgaWYgKGV4cHIuaWQpIHtcbiAgICAgIHN3aXRjaCAoZXhwci50eXBlKSB7XG4gICAgICAgIGNhc2UgXCJGdW5jdGlvbkV4cHJlc3Npb25cIjpcbiAgICAgICAgICBleHByLnR5cGUgPSBcIkZ1bmN0aW9uRGVjbGFyYXRpb25cIjticmVhaztcbiAgICAgICAgY2FzZSBcIkNsYXNzRXhwcmVzc2lvblwiOlxuICAgICAgICAgIGV4cHIudHlwZSA9IFwiQ2xhc3NEZWNsYXJhdGlvblwiO2JyZWFrO1xuICAgICAgfVxuICAgIH1cbiAgICBub2RlLmRlY2xhcmF0aW9uID0gZXhwcjtcbiAgICB0aGlzLnNlbWljb2xvbigpO1xuICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJFeHBvcnREZWZhdWx0RGVjbGFyYXRpb25cIik7XG4gIH1cbiAgaWYgKHRoaXMudG9rLnR5cGUua2V5d29yZCkge1xuICAgIG5vZGUuZGVjbGFyYXRpb24gPSB0aGlzLnBhcnNlU3RhdGVtZW50KCk7XG4gICAgbm9kZS5zcGVjaWZpZXJzID0gW107XG4gICAgbm9kZS5zb3VyY2UgPSBudWxsO1xuICB9IGVsc2Uge1xuICAgIG5vZGUuZGVjbGFyYXRpb24gPSBudWxsO1xuICAgIG5vZGUuc3BlY2lmaWVycyA9IHRoaXMucGFyc2VFeHBvcnRTcGVjaWZpZXJMaXN0KCk7XG4gICAgbm9kZS5zb3VyY2UgPSB0aGlzLmVhdENvbnRleHR1YWwoXCJmcm9tXCIpID8gdGhpcy5wYXJzZUV4cHJBdG9tKCkgOiBudWxsO1xuICAgIHRoaXMuc2VtaWNvbG9uKCk7XG4gIH1cbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkV4cG9ydE5hbWVkRGVjbGFyYXRpb25cIik7XG59O1xuXG5scC5wYXJzZUltcG9ydCA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICB0aGlzLm5leHQoKTtcbiAgaWYgKHRoaXMudG9rLnR5cGUgPT09IF8udG9rVHlwZXMuc3RyaW5nKSB7XG4gICAgbm9kZS5zcGVjaWZpZXJzID0gW107XG4gICAgbm9kZS5zb3VyY2UgPSB0aGlzLnBhcnNlRXhwckF0b20oKTtcbiAgICBub2RlLmtpbmQgPSBcIlwiO1xuICB9IGVsc2Uge1xuICAgIHZhciBlbHQgPSB1bmRlZmluZWQ7XG4gICAgaWYgKHRoaXMudG9rLnR5cGUgPT09IF8udG9rVHlwZXMubmFtZSAmJiB0aGlzLnRvay52YWx1ZSAhPT0gXCJmcm9tXCIpIHtcbiAgICAgIGVsdCA9IHRoaXMuc3RhcnROb2RlKCk7XG4gICAgICBlbHQubG9jYWwgPSB0aGlzLnBhcnNlSWRlbnQoKTtcbiAgICAgIHRoaXMuZmluaXNoTm9kZShlbHQsIFwiSW1wb3J0RGVmYXVsdFNwZWNpZmllclwiKTtcbiAgICAgIHRoaXMuZWF0KF8udG9rVHlwZXMuY29tbWEpO1xuICAgIH1cbiAgICBub2RlLnNwZWNpZmllcnMgPSB0aGlzLnBhcnNlSW1wb3J0U3BlY2lmaWVyTGlzdCgpO1xuICAgIG5vZGUuc291cmNlID0gdGhpcy5lYXRDb250ZXh0dWFsKFwiZnJvbVwiKSA/IHRoaXMucGFyc2VFeHByQXRvbSgpIDogdGhpcy5kdW1teVN0cmluZygpO1xuICAgIGlmIChlbHQpIG5vZGUuc3BlY2lmaWVycy51bnNoaWZ0KGVsdCk7XG4gIH1cbiAgdGhpcy5zZW1pY29sb24oKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkltcG9ydERlY2xhcmF0aW9uXCIpO1xufTtcblxubHAucGFyc2VJbXBvcnRTcGVjaWZpZXJMaXN0ID0gZnVuY3Rpb24gKCkge1xuICB2YXIgZWx0cyA9IFtdO1xuICBpZiAodGhpcy50b2sudHlwZSA9PT0gXy50b2tUeXBlcy5zdGFyKSB7XG4gICAgdmFyIGVsdCA9IHRoaXMuc3RhcnROb2RlKCk7XG4gICAgdGhpcy5uZXh0KCk7XG4gICAgaWYgKHRoaXMuZWF0Q29udGV4dHVhbChcImFzXCIpKSBlbHQubG9jYWwgPSB0aGlzLnBhcnNlSWRlbnQoKTtcbiAgICBlbHRzLnB1c2godGhpcy5maW5pc2hOb2RlKGVsdCwgXCJJbXBvcnROYW1lc3BhY2VTcGVjaWZpZXJcIikpO1xuICB9IGVsc2Uge1xuICAgIHZhciBpbmRlbnQgPSB0aGlzLmN1ckluZGVudCxcbiAgICAgICAgbGluZSA9IHRoaXMuY3VyTGluZVN0YXJ0LFxuICAgICAgICBjb250aW51ZWRMaW5lID0gdGhpcy5uZXh0TGluZVN0YXJ0O1xuICAgIHRoaXMucHVzaEN4KCk7XG4gICAgdGhpcy5lYXQoXy50b2tUeXBlcy5icmFjZUwpO1xuICAgIGlmICh0aGlzLmN1ckxpbmVTdGFydCA+IGNvbnRpbnVlZExpbmUpIGNvbnRpbnVlZExpbmUgPSB0aGlzLmN1ckxpbmVTdGFydDtcbiAgICB3aGlsZSAoIXRoaXMuY2xvc2VzKF8udG9rVHlwZXMuYnJhY2VSLCBpbmRlbnQgKyAodGhpcy5jdXJMaW5lU3RhcnQgPD0gY29udGludWVkTGluZSA/IDEgOiAwKSwgbGluZSkpIHtcbiAgICAgIHZhciBlbHQgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICAgICAgaWYgKHRoaXMuZWF0KF8udG9rVHlwZXMuc3RhcikpIHtcbiAgICAgICAgaWYgKHRoaXMuZWF0Q29udGV4dHVhbChcImFzXCIpKSBlbHQubG9jYWwgPSB0aGlzLnBhcnNlSWRlbnQoKTtcbiAgICAgICAgdGhpcy5maW5pc2hOb2RlKGVsdCwgXCJJbXBvcnROYW1lc3BhY2VTcGVjaWZpZXJcIik7XG4gICAgICB9IGVsc2Uge1xuICAgICAgICBpZiAodGhpcy5pc0NvbnRleHR1YWwoXCJmcm9tXCIpKSBicmVhaztcbiAgICAgICAgZWx0LmltcG9ydGVkID0gdGhpcy5wYXJzZUlkZW50KCk7XG4gICAgICAgIGlmIChfcGFyc2V1dGlsLmlzRHVtbXkoZWx0LmltcG9ydGVkKSkgYnJlYWs7XG4gICAgICAgIGVsdC5sb2NhbCA9IHRoaXMuZWF0Q29udGV4dHVhbChcImFzXCIpID8gdGhpcy5wYXJzZUlkZW50KCkgOiBlbHQuaW1wb3J0ZWQ7XG4gICAgICAgIHRoaXMuZmluaXNoTm9kZShlbHQsIFwiSW1wb3J0U3BlY2lmaWVyXCIpO1xuICAgICAgfVxuICAgICAgZWx0cy5wdXNoKGVsdCk7XG4gICAgICB0aGlzLmVhdChfLnRva1R5cGVzLmNvbW1hKTtcbiAgICB9XG4gICAgdGhpcy5lYXQoXy50b2tUeXBlcy5icmFjZVIpO1xuICAgIHRoaXMucG9wQ3goKTtcbiAgfVxuICByZXR1cm4gZWx0cztcbn07XG5cbmxwLnBhcnNlRXhwb3J0U3BlY2lmaWVyTGlzdCA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIGVsdHMgPSBbXTtcbiAgdmFyIGluZGVudCA9IHRoaXMuY3VySW5kZW50LFxuICAgICAgbGluZSA9IHRoaXMuY3VyTGluZVN0YXJ0LFxuICAgICAgY29udGludWVkTGluZSA9IHRoaXMubmV4dExpbmVTdGFydDtcbiAgdGhpcy5wdXNoQ3goKTtcbiAgdGhpcy5lYXQoXy50b2tUeXBlcy5icmFjZUwpO1xuICBpZiAodGhpcy5jdXJMaW5lU3RhcnQgPiBjb250aW51ZWRMaW5lKSBjb250aW51ZWRMaW5lID0gdGhpcy5jdXJMaW5lU3RhcnQ7XG4gIHdoaWxlICghdGhpcy5jbG9zZXMoXy50b2tUeXBlcy5icmFjZVIsIGluZGVudCArICh0aGlzLmN1ckxpbmVTdGFydCA8PSBjb250aW51ZWRMaW5lID8gMSA6IDApLCBsaW5lKSkge1xuICAgIGlmICh0aGlzLmlzQ29udGV4dHVhbChcImZyb21cIikpIGJyZWFrO1xuICAgIHZhciBlbHQgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICAgIGVsdC5sb2NhbCA9IHRoaXMucGFyc2VJZGVudCgpO1xuICAgIGlmIChfcGFyc2V1dGlsLmlzRHVtbXkoZWx0LmxvY2FsKSkgYnJlYWs7XG4gICAgZWx0LmV4cG9ydGVkID0gdGhpcy5lYXRDb250ZXh0dWFsKFwiYXNcIikgPyB0aGlzLnBhcnNlSWRlbnQoKSA6IGVsdC5sb2NhbDtcbiAgICB0aGlzLmZpbmlzaE5vZGUoZWx0LCBcIkV4cG9ydFNwZWNpZmllclwiKTtcbiAgICBlbHRzLnB1c2goZWx0KTtcbiAgICB0aGlzLmVhdChfLnRva1R5cGVzLmNvbW1hKTtcbiAgfVxuICB0aGlzLmVhdChfLnRva1R5cGVzLmJyYWNlUik7XG4gIHRoaXMucG9wQ3goKTtcbiAgcmV0dXJuIGVsdHM7XG59O1xuXG59LHtcIi4uXCI6MSxcIi4vcGFyc2V1dGlsXCI6NCxcIi4vc3RhdGVcIjo1fV0sNzpbZnVuY3Rpb24oX2RlcmVxXyxtb2R1bGUsZXhwb3J0cyl7XG5cInVzZSBzdHJpY3RcIjtcblxudmFyIF8gPSBfZGVyZXFfKFwiLi5cIik7XG5cbnZhciBfc3RhdGUgPSBfZGVyZXFfKFwiLi9zdGF0ZVwiKTtcblxudmFyIGxwID0gX3N0YXRlLkxvb3NlUGFyc2VyLnByb3RvdHlwZTtcblxuZnVuY3Rpb24gaXNTcGFjZShjaCkge1xuICByZXR1cm4gY2ggPCAxNCAmJiBjaCA+IDggfHwgY2ggPT09IDMyIHx8IGNoID09PSAxNjAgfHwgXy5pc05ld0xpbmUoY2gpO1xufVxuXG5scC5uZXh0ID0gZnVuY3Rpb24gKCkge1xuICB0aGlzLmxhc3QgPSB0aGlzLnRvaztcbiAgaWYgKHRoaXMuYWhlYWQubGVuZ3RoKSB0aGlzLnRvayA9IHRoaXMuYWhlYWQuc2hpZnQoKTtlbHNlIHRoaXMudG9rID0gdGhpcy5yZWFkVG9rZW4oKTtcblxuICBpZiAodGhpcy50b2suc3RhcnQgPj0gdGhpcy5uZXh0TGluZVN0YXJ0KSB7XG4gICAgd2hpbGUgKHRoaXMudG9rLnN0YXJ0ID49IHRoaXMubmV4dExpbmVTdGFydCkge1xuICAgICAgdGhpcy5jdXJMaW5lU3RhcnQgPSB0aGlzLm5leHRMaW5lU3RhcnQ7XG4gICAgICB0aGlzLm5leHRMaW5lU3RhcnQgPSB0aGlzLmxpbmVFbmQodGhpcy5jdXJMaW5lU3RhcnQpICsgMTtcbiAgICB9XG4gICAgdGhpcy5jdXJJbmRlbnQgPSB0aGlzLmluZGVudGF0aW9uQWZ0ZXIodGhpcy5jdXJMaW5lU3RhcnQpO1xuICB9XG59O1xuXG5scC5yZWFkVG9rZW4gPSBmdW5jdGlvbiAoKSB7XG4gIGZvciAoOzspIHtcbiAgICB0cnkge1xuICAgICAgdGhpcy50b2tzLm5leHQoKTtcbiAgICAgIGlmICh0aGlzLnRva3MudHlwZSA9PT0gXy50b2tUeXBlcy5kb3QgJiYgdGhpcy5pbnB1dC5zdWJzdHIodGhpcy50b2tzLmVuZCwgMSkgPT09IFwiLlwiICYmIHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KSB7XG4gICAgICAgIHRoaXMudG9rcy5lbmQrKztcbiAgICAgICAgdGhpcy50b2tzLnR5cGUgPSBfLnRva1R5cGVzLmVsbGlwc2lzO1xuICAgICAgfVxuICAgICAgcmV0dXJuIG5ldyBfLlRva2VuKHRoaXMudG9rcyk7XG4gICAgfSBjYXRjaCAoZSkge1xuICAgICAgaWYgKCEoZSBpbnN0YW5jZW9mIFN5bnRheEVycm9yKSkgdGhyb3cgZTtcblxuICAgICAgLy8gVHJ5IHRvIHNraXAgc29tZSB0ZXh0LCBiYXNlZCBvbiB0aGUgZXJyb3IgbWVzc2FnZSwgYW5kIHRoZW4gY29udGludWVcbiAgICAgIHZhciBtc2cgPSBlLm1lc3NhZ2UsXG4gICAgICAgICAgcG9zID0gZS5yYWlzZWRBdCxcbiAgICAgICAgICByZXBsYWNlID0gdHJ1ZTtcbiAgICAgIGlmICgvdW50ZXJtaW5hdGVkL2kudGVzdChtc2cpKSB7XG4gICAgICAgIHBvcyA9IHRoaXMubGluZUVuZChlLnBvcyArIDEpO1xuICAgICAgICBpZiAoL3N0cmluZy8udGVzdChtc2cpKSB7XG4gICAgICAgICAgcmVwbGFjZSA9IHsgc3RhcnQ6IGUucG9zLCBlbmQ6IHBvcywgdHlwZTogXy50b2tUeXBlcy5zdHJpbmcsIHZhbHVlOiB0aGlzLmlucHV0LnNsaWNlKGUucG9zICsgMSwgcG9zKSB9O1xuICAgICAgICB9IGVsc2UgaWYgKC9yZWd1bGFyIGV4cHIvaS50ZXN0KG1zZykpIHtcbiAgICAgICAgICB2YXIgcmUgPSB0aGlzLmlucHV0LnNsaWNlKGUucG9zLCBwb3MpO1xuICAgICAgICAgIHRyeSB7XG4gICAgICAgICAgICByZSA9IG5ldyBSZWdFeHAocmUpO1xuICAgICAgICAgIH0gY2F0Y2ggKGUpIHt9XG4gICAgICAgICAgcmVwbGFjZSA9IHsgc3RhcnQ6IGUucG9zLCBlbmQ6IHBvcywgdHlwZTogXy50b2tUeXBlcy5yZWdleHAsIHZhbHVlOiByZSB9O1xuICAgICAgICB9IGVsc2UgaWYgKC90ZW1wbGF0ZS8udGVzdChtc2cpKSB7XG4gICAgICAgICAgcmVwbGFjZSA9IHsgc3RhcnQ6IGUucG9zLCBlbmQ6IHBvcyxcbiAgICAgICAgICAgIHR5cGU6IF8udG9rVHlwZXMudGVtcGxhdGUsXG4gICAgICAgICAgICB2YWx1ZTogdGhpcy5pbnB1dC5zbGljZShlLnBvcywgcG9zKSB9O1xuICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgIHJlcGxhY2UgPSBmYWxzZTtcbiAgICAgICAgfVxuICAgICAgfSBlbHNlIGlmICgvaW52YWxpZCAodW5pY29kZXxyZWdleHB8bnVtYmVyKXxleHBlY3RpbmcgdW5pY29kZXxvY3RhbCBsaXRlcmFsfGlzIHJlc2VydmVkfGRpcmVjdGx5IGFmdGVyIG51bWJlcnxleHBlY3RlZCBudW1iZXIgaW4gcmFkaXgvaS50ZXN0KG1zZykpIHtcbiAgICAgICAgd2hpbGUgKHBvcyA8IHRoaXMuaW5wdXQubGVuZ3RoICYmICFpc1NwYWNlKHRoaXMuaW5wdXQuY2hhckNvZGVBdChwb3MpKSkgKytwb3M7XG4gICAgICB9IGVsc2UgaWYgKC9jaGFyYWN0ZXIgZXNjYXBlfGV4cGVjdGVkIGhleGFkZWNpbWFsL2kudGVzdChtc2cpKSB7XG4gICAgICAgIHdoaWxlIChwb3MgPCB0aGlzLmlucHV0Lmxlbmd0aCkge1xuICAgICAgICAgIHZhciBjaCA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdChwb3MrKyk7XG4gICAgICAgICAgaWYgKGNoID09PSAzNCB8fCBjaCA9PT0gMzkgfHwgXy5pc05ld0xpbmUoY2gpKSBicmVhaztcbiAgICAgICAgfVxuICAgICAgfSBlbHNlIGlmICgvdW5leHBlY3RlZCBjaGFyYWN0ZXIvaS50ZXN0KG1zZykpIHtcbiAgICAgICAgcG9zKys7XG4gICAgICAgIHJlcGxhY2UgPSBmYWxzZTtcbiAgICAgIH0gZWxzZSBpZiAoL3JlZ3VsYXIgZXhwcmVzc2lvbi9pLnRlc3QobXNnKSkge1xuICAgICAgICByZXBsYWNlID0gdHJ1ZTtcbiAgICAgIH0gZWxzZSB7XG4gICAgICAgIHRocm93IGU7XG4gICAgICB9XG4gICAgICB0aGlzLnJlc2V0VG8ocG9zKTtcbiAgICAgIGlmIChyZXBsYWNlID09PSB0cnVlKSByZXBsYWNlID0geyBzdGFydDogcG9zLCBlbmQ6IHBvcywgdHlwZTogXy50b2tUeXBlcy5uYW1lLCB2YWx1ZTogXCLinJZcIiB9O1xuICAgICAgaWYgKHJlcGxhY2UpIHtcbiAgICAgICAgaWYgKHRoaXMub3B0aW9ucy5sb2NhdGlvbnMpIHJlcGxhY2UubG9jID0gbmV3IF8uU291cmNlTG9jYXRpb24odGhpcy50b2tzLCBfLmdldExpbmVJbmZvKHRoaXMuaW5wdXQsIHJlcGxhY2Uuc3RhcnQpLCBfLmdldExpbmVJbmZvKHRoaXMuaW5wdXQsIHJlcGxhY2UuZW5kKSk7XG4gICAgICAgIHJldHVybiByZXBsYWNlO1xuICAgICAgfVxuICAgIH1cbiAgfVxufTtcblxubHAucmVzZXRUbyA9IGZ1bmN0aW9uIChwb3MpIHtcbiAgdGhpcy50b2tzLnBvcyA9IHBvcztcbiAgdmFyIGNoID0gdGhpcy5pbnB1dC5jaGFyQXQocG9zIC0gMSk7XG4gIHRoaXMudG9rcy5leHByQWxsb3dlZCA9ICFjaCB8fCAvW1xcW1xce1xcKCw7Oj9cXC8qPStcXC1+IXwmJV48Pl0vLnRlc3QoY2gpIHx8IC9bZW53ZmRdLy50ZXN0KGNoKSAmJiAvXFxiKGtleXdvcmRzfGNhc2V8ZWxzZXxyZXR1cm58dGhyb3d8bmV3fGlufChpbnN0YW5jZXx0eXBlKW9mfGRlbGV0ZXx2b2lkKSQvLnRlc3QodGhpcy5pbnB1dC5zbGljZShwb3MgLSAxMCwgcG9zKSk7XG5cbiAgaWYgKHRoaXMub3B0aW9ucy5sb2NhdGlvbnMpIHtcbiAgICB0aGlzLnRva3MuY3VyTGluZSA9IDE7XG4gICAgdGhpcy50b2tzLmxpbmVTdGFydCA9IF8ubGluZUJyZWFrRy5sYXN0SW5kZXggPSAwO1xuICAgIHZhciBtYXRjaCA9IHVuZGVmaW5lZDtcbiAgICB3aGlsZSAoKG1hdGNoID0gXy5saW5lQnJlYWtHLmV4ZWModGhpcy5pbnB1dCkpICYmIG1hdGNoLmluZGV4IDwgcG9zKSB7XG4gICAgICArK3RoaXMudG9rcy5jdXJMaW5lO1xuICAgICAgdGhpcy50b2tzLmxpbmVTdGFydCA9IG1hdGNoLmluZGV4ICsgbWF0Y2hbMF0ubGVuZ3RoO1xuICAgIH1cbiAgfVxufTtcblxubHAubG9va0FoZWFkID0gZnVuY3Rpb24gKG4pIHtcbiAgd2hpbGUgKG4gPiB0aGlzLmFoZWFkLmxlbmd0aCkgdGhpcy5haGVhZC5wdXNoKHRoaXMucmVhZFRva2VuKCkpO1xuICByZXR1cm4gdGhpcy5haGVhZFtuIC0gMV07XG59O1xuXG59LHtcIi4uXCI6MSxcIi4vc3RhdGVcIjo1fV19LHt9LFszXSkoMylcbn0pOyIsIihmdW5jdGlvbihmKXtpZih0eXBlb2YgZXhwb3J0cz09PVwib2JqZWN0XCImJnR5cGVvZiBtb2R1bGUhPT1cInVuZGVmaW5lZFwiKXttb2R1bGUuZXhwb3J0cz1mKCl9ZWxzZSBpZih0eXBlb2YgZGVmaW5lPT09XCJmdW5jdGlvblwiJiZkZWZpbmUuYW1kKXtkZWZpbmUoW10sZil9ZWxzZXt2YXIgZztpZih0eXBlb2Ygd2luZG93IT09XCJ1bmRlZmluZWRcIil7Zz13aW5kb3d9ZWxzZSBpZih0eXBlb2YgZ2xvYmFsIT09XCJ1bmRlZmluZWRcIil7Zz1nbG9iYWx9ZWxzZSBpZih0eXBlb2Ygc2VsZiE9PVwidW5kZWZpbmVkXCIpe2c9c2VsZn1lbHNle2c9dGhpc30oZy5hY29ybiB8fCAoZy5hY29ybiA9IHt9KSkud2FsayA9IGYoKX19KShmdW5jdGlvbigpe3ZhciBkZWZpbmUsbW9kdWxlLGV4cG9ydHM7cmV0dXJuIChmdW5jdGlvbiBlKHQsbixyKXtmdW5jdGlvbiBzKG8sdSl7aWYoIW5bb10pe2lmKCF0W29dKXt2YXIgYT10eXBlb2YgcmVxdWlyZT09XCJmdW5jdGlvblwiJiZyZXF1aXJlO2lmKCF1JiZhKXJldHVybiBhKG8sITApO2lmKGkpcmV0dXJuIGkobywhMCk7dmFyIGY9bmV3IEVycm9yKFwiQ2Fubm90IGZpbmQgbW9kdWxlICdcIitvK1wiJ1wiKTt0aHJvdyBmLmNvZGU9XCJNT0RVTEVfTk9UX0ZPVU5EXCIsZn12YXIgbD1uW29dPXtleHBvcnRzOnt9fTt0W29dWzBdLmNhbGwobC5leHBvcnRzLGZ1bmN0aW9uKGUpe3ZhciBuPXRbb11bMV1bZV07cmV0dXJuIHMobj9uOmUpfSxsLGwuZXhwb3J0cyxlLHQsbixyKX1yZXR1cm4gbltvXS5leHBvcnRzfXZhciBpPXR5cGVvZiByZXF1aXJlPT1cImZ1bmN0aW9uXCImJnJlcXVpcmU7Zm9yKHZhciBvPTA7bzxyLmxlbmd0aDtvKyspcyhyW29dKTtyZXR1cm4gc30pKHsxOltmdW5jdGlvbihfZGVyZXFfLG1vZHVsZSxleHBvcnRzKXtcbi8vIEFTVCB3YWxrZXIgbW9kdWxlIGZvciBNb3ppbGxhIFBhcnNlciBBUEkgY29tcGF0aWJsZSB0cmVlc1xuXG4vLyBBIHNpbXBsZSB3YWxrIGlzIG9uZSB3aGVyZSB5b3Ugc2ltcGx5IHNwZWNpZnkgY2FsbGJhY2tzIHRvIGJlXG4vLyBjYWxsZWQgb24gc3BlY2lmaWMgbm9kZXMuIFRoZSBsYXN0IHR3byBhcmd1bWVudHMgYXJlIG9wdGlvbmFsLiBBXG4vLyBzaW1wbGUgdXNlIHdvdWxkIGJlXG4vL1xuLy8gICAgIHdhbGsuc2ltcGxlKG15VHJlZSwge1xuLy8gICAgICAgICBFeHByZXNzaW9uOiBmdW5jdGlvbihub2RlKSB7IC4uLiB9XG4vLyAgICAgfSk7XG4vL1xuLy8gdG8gZG8gc29tZXRoaW5nIHdpdGggYWxsIGV4cHJlc3Npb25zLiBBbGwgUGFyc2VyIEFQSSBub2RlIHR5cGVzXG4vLyBjYW4gYmUgdXNlZCB0byBpZGVudGlmeSBub2RlIHR5cGVzLCBhcyB3ZWxsIGFzIEV4cHJlc3Npb24sXG4vLyBTdGF0ZW1lbnQsIGFuZCBTY29wZUJvZHksIHdoaWNoIGRlbm90ZSBjYXRlZ29yaWVzIG9mIG5vZGVzLlxuLy9cbi8vIFRoZSBiYXNlIGFyZ3VtZW50IGNhbiBiZSB1c2VkIHRvIHBhc3MgYSBjdXN0b20gKHJlY3Vyc2l2ZSlcbi8vIHdhbGtlciwgYW5kIHN0YXRlIGNhbiBiZSB1c2VkIHRvIGdpdmUgdGhpcyB3YWxrZWQgYW4gaW5pdGlhbFxuLy8gc3RhdGUuXG5cblwidXNlIHN0cmljdFwiO1xuXG5leHBvcnRzLl9fZXNNb2R1bGUgPSB0cnVlO1xuZXhwb3J0cy5zaW1wbGUgPSBzaW1wbGU7XG5leHBvcnRzLmFuY2VzdG9yID0gYW5jZXN0b3I7XG5leHBvcnRzLnJlY3Vyc2l2ZSA9IHJlY3Vyc2l2ZTtcbmV4cG9ydHMuZmluZE5vZGVBdCA9IGZpbmROb2RlQXQ7XG5leHBvcnRzLmZpbmROb2RlQXJvdW5kID0gZmluZE5vZGVBcm91bmQ7XG5leHBvcnRzLmZpbmROb2RlQWZ0ZXIgPSBmaW5kTm9kZUFmdGVyO1xuZXhwb3J0cy5maW5kTm9kZUJlZm9yZSA9IGZpbmROb2RlQmVmb3JlO1xuZXhwb3J0cy5tYWtlID0gbWFrZTtcblxuZnVuY3Rpb24gX2NsYXNzQ2FsbENoZWNrKGluc3RhbmNlLCBDb25zdHJ1Y3RvcikgeyBpZiAoIShpbnN0YW5jZSBpbnN0YW5jZW9mIENvbnN0cnVjdG9yKSkgeyB0aHJvdyBuZXcgVHlwZUVycm9yKFwiQ2Fubm90IGNhbGwgYSBjbGFzcyBhcyBhIGZ1bmN0aW9uXCIpOyB9IH1cblxuZnVuY3Rpb24gc2ltcGxlKG5vZGUsIHZpc2l0b3JzLCBiYXNlLCBzdGF0ZSwgb3ZlcnJpZGUpIHtcbiAgaWYgKCFiYXNlKSBiYXNlID0gZXhwb3J0cy5iYXNlOyhmdW5jdGlvbiBjKG5vZGUsIHN0LCBvdmVycmlkZSkge1xuICAgIHZhciB0eXBlID0gb3ZlcnJpZGUgfHwgbm9kZS50eXBlLFxuICAgICAgICBmb3VuZCA9IHZpc2l0b3JzW3R5cGVdO1xuICAgIGJhc2VbdHlwZV0obm9kZSwgc3QsIGMpO1xuICAgIGlmIChmb3VuZCkgZm91bmQobm9kZSwgc3QpO1xuICB9KShub2RlLCBzdGF0ZSwgb3ZlcnJpZGUpO1xufVxuXG4vLyBBbiBhbmNlc3RvciB3YWxrIGJ1aWxkcyB1cCBhbiBhcnJheSBvZiBhbmNlc3RvciBub2RlcyAoaW5jbHVkaW5nXG4vLyB0aGUgY3VycmVudCBub2RlKSBhbmQgcGFzc2VzIHRoZW0gdG8gdGhlIGNhbGxiYWNrIGFzIHRoZSBzdGF0ZSBwYXJhbWV0ZXIuXG5cbmZ1bmN0aW9uIGFuY2VzdG9yKG5vZGUsIHZpc2l0b3JzLCBiYXNlLCBzdGF0ZSkge1xuICBpZiAoIWJhc2UpIGJhc2UgPSBleHBvcnRzLmJhc2U7XG4gIGlmICghc3RhdGUpIHN0YXRlID0gW107KGZ1bmN0aW9uIGMobm9kZSwgc3QsIG92ZXJyaWRlKSB7XG4gICAgdmFyIHR5cGUgPSBvdmVycmlkZSB8fCBub2RlLnR5cGUsXG4gICAgICAgIGZvdW5kID0gdmlzaXRvcnNbdHlwZV07XG4gICAgaWYgKG5vZGUgIT0gc3Rbc3QubGVuZ3RoIC0gMV0pIHtcbiAgICAgIHN0ID0gc3Quc2xpY2UoKTtcbiAgICAgIHN0LnB1c2gobm9kZSk7XG4gICAgfVxuICAgIGJhc2VbdHlwZV0obm9kZSwgc3QsIGMpO1xuICAgIGlmIChmb3VuZCkgZm91bmQobm9kZSwgc3QpO1xuICB9KShub2RlLCBzdGF0ZSk7XG59XG5cbi8vIEEgcmVjdXJzaXZlIHdhbGsgaXMgb25lIHdoZXJlIHlvdXIgZnVuY3Rpb25zIG92ZXJyaWRlIHRoZSBkZWZhdWx0XG4vLyB3YWxrZXJzLiBUaGV5IGNhbiBtb2RpZnkgYW5kIHJlcGxhY2UgdGhlIHN0YXRlIHBhcmFtZXRlciB0aGF0J3Ncbi8vIHRocmVhZGVkIHRocm91Z2ggdGhlIHdhbGssIGFuZCBjYW4gb3B0IGhvdyBhbmQgd2hldGhlciB0byB3YWxrXG4vLyB0aGVpciBjaGlsZCBub2RlcyAoYnkgY2FsbGluZyB0aGVpciB0aGlyZCBhcmd1bWVudCBvbiB0aGVzZVxuLy8gbm9kZXMpLlxuXG5mdW5jdGlvbiByZWN1cnNpdmUobm9kZSwgc3RhdGUsIGZ1bmNzLCBiYXNlLCBvdmVycmlkZSkge1xuICB2YXIgdmlzaXRvciA9IGZ1bmNzID8gZXhwb3J0cy5tYWtlKGZ1bmNzLCBiYXNlKSA6IGJhc2U7KGZ1bmN0aW9uIGMobm9kZSwgc3QsIG92ZXJyaWRlKSB7XG4gICAgdmlzaXRvcltvdmVycmlkZSB8fCBub2RlLnR5cGVdKG5vZGUsIHN0LCBjKTtcbiAgfSkobm9kZSwgc3RhdGUsIG92ZXJyaWRlKTtcbn1cblxuZnVuY3Rpb24gbWFrZVRlc3QodGVzdCkge1xuICBpZiAodHlwZW9mIHRlc3QgPT0gXCJzdHJpbmdcIikgcmV0dXJuIGZ1bmN0aW9uICh0eXBlKSB7XG4gICAgcmV0dXJuIHR5cGUgPT0gdGVzdDtcbiAgfTtlbHNlIGlmICghdGVzdCkgcmV0dXJuIGZ1bmN0aW9uICgpIHtcbiAgICByZXR1cm4gdHJ1ZTtcbiAgfTtlbHNlIHJldHVybiB0ZXN0O1xufVxuXG52YXIgRm91bmQgPSBmdW5jdGlvbiBGb3VuZChub2RlLCBzdGF0ZSkge1xuICBfY2xhc3NDYWxsQ2hlY2sodGhpcywgRm91bmQpO1xuXG4gIHRoaXMubm9kZSA9IG5vZGU7dGhpcy5zdGF0ZSA9IHN0YXRlO1xufTtcblxuLy8gRmluZCBhIG5vZGUgd2l0aCBhIGdpdmVuIHN0YXJ0LCBlbmQsIGFuZCB0eXBlIChhbGwgYXJlIG9wdGlvbmFsLFxuLy8gbnVsbCBjYW4gYmUgdXNlZCBhcyB3aWxkY2FyZCkuIFJldHVybnMgYSB7bm9kZSwgc3RhdGV9IG9iamVjdCwgb3Jcbi8vIHVuZGVmaW5lZCB3aGVuIGl0IGRvZXNuJ3QgZmluZCBhIG1hdGNoaW5nIG5vZGUuXG5cbmZ1bmN0aW9uIGZpbmROb2RlQXQobm9kZSwgc3RhcnQsIGVuZCwgdGVzdCwgYmFzZSwgc3RhdGUpIHtcbiAgdGVzdCA9IG1ha2VUZXN0KHRlc3QpO1xuICBpZiAoIWJhc2UpIGJhc2UgPSBleHBvcnRzLmJhc2U7XG4gIHRyeSB7XG4gICAgOyhmdW5jdGlvbiBjKG5vZGUsIHN0LCBvdmVycmlkZSkge1xuICAgICAgdmFyIHR5cGUgPSBvdmVycmlkZSB8fCBub2RlLnR5cGU7XG4gICAgICBpZiAoKHN0YXJ0ID09IG51bGwgfHwgbm9kZS5zdGFydCA8PSBzdGFydCkgJiYgKGVuZCA9PSBudWxsIHx8IG5vZGUuZW5kID49IGVuZCkpIGJhc2VbdHlwZV0obm9kZSwgc3QsIGMpO1xuICAgICAgaWYgKChzdGFydCA9PSBudWxsIHx8IG5vZGUuc3RhcnQgPT0gc3RhcnQpICYmIChlbmQgPT0gbnVsbCB8fCBub2RlLmVuZCA9PSBlbmQpICYmIHRlc3QodHlwZSwgbm9kZSkpIHRocm93IG5ldyBGb3VuZChub2RlLCBzdCk7XG4gICAgfSkobm9kZSwgc3RhdGUpO1xuICB9IGNhdGNoIChlKSB7XG4gICAgaWYgKGUgaW5zdGFuY2VvZiBGb3VuZCkgcmV0dXJuIGU7XG4gICAgdGhyb3cgZTtcbiAgfVxufVxuXG4vLyBGaW5kIHRoZSBpbm5lcm1vc3Qgbm9kZSBvZiBhIGdpdmVuIHR5cGUgdGhhdCBjb250YWlucyB0aGUgZ2l2ZW5cbi8vIHBvc2l0aW9uLiBJbnRlcmZhY2Ugc2ltaWxhciB0byBmaW5kTm9kZUF0LlxuXG5mdW5jdGlvbiBmaW5kTm9kZUFyb3VuZChub2RlLCBwb3MsIHRlc3QsIGJhc2UsIHN0YXRlKSB7XG4gIHRlc3QgPSBtYWtlVGVzdCh0ZXN0KTtcbiAgaWYgKCFiYXNlKSBiYXNlID0gZXhwb3J0cy5iYXNlO1xuICB0cnkge1xuICAgIDsoZnVuY3Rpb24gYyhub2RlLCBzdCwgb3ZlcnJpZGUpIHtcbiAgICAgIHZhciB0eXBlID0gb3ZlcnJpZGUgfHwgbm9kZS50eXBlO1xuICAgICAgaWYgKG5vZGUuc3RhcnQgPiBwb3MgfHwgbm9kZS5lbmQgPCBwb3MpIHJldHVybjtcbiAgICAgIGJhc2VbdHlwZV0obm9kZSwgc3QsIGMpO1xuICAgICAgaWYgKHRlc3QodHlwZSwgbm9kZSkpIHRocm93IG5ldyBGb3VuZChub2RlLCBzdCk7XG4gICAgfSkobm9kZSwgc3RhdGUpO1xuICB9IGNhdGNoIChlKSB7XG4gICAgaWYgKGUgaW5zdGFuY2VvZiBGb3VuZCkgcmV0dXJuIGU7XG4gICAgdGhyb3cgZTtcbiAgfVxufVxuXG4vLyBGaW5kIHRoZSBvdXRlcm1vc3QgbWF0Y2hpbmcgbm9kZSBhZnRlciBhIGdpdmVuIHBvc2l0aW9uLlxuXG5mdW5jdGlvbiBmaW5kTm9kZUFmdGVyKG5vZGUsIHBvcywgdGVzdCwgYmFzZSwgc3RhdGUpIHtcbiAgdGVzdCA9IG1ha2VUZXN0KHRlc3QpO1xuICBpZiAoIWJhc2UpIGJhc2UgPSBleHBvcnRzLmJhc2U7XG4gIHRyeSB7XG4gICAgOyhmdW5jdGlvbiBjKG5vZGUsIHN0LCBvdmVycmlkZSkge1xuICAgICAgaWYgKG5vZGUuZW5kIDwgcG9zKSByZXR1cm47XG4gICAgICB2YXIgdHlwZSA9IG92ZXJyaWRlIHx8IG5vZGUudHlwZTtcbiAgICAgIGlmIChub2RlLnN0YXJ0ID49IHBvcyAmJiB0ZXN0KHR5cGUsIG5vZGUpKSB0aHJvdyBuZXcgRm91bmQobm9kZSwgc3QpO1xuICAgICAgYmFzZVt0eXBlXShub2RlLCBzdCwgYyk7XG4gICAgfSkobm9kZSwgc3RhdGUpO1xuICB9IGNhdGNoIChlKSB7XG4gICAgaWYgKGUgaW5zdGFuY2VvZiBGb3VuZCkgcmV0dXJuIGU7XG4gICAgdGhyb3cgZTtcbiAgfVxufVxuXG4vLyBGaW5kIHRoZSBvdXRlcm1vc3QgbWF0Y2hpbmcgbm9kZSBiZWZvcmUgYSBnaXZlbiBwb3NpdGlvbi5cblxuZnVuY3Rpb24gZmluZE5vZGVCZWZvcmUobm9kZSwgcG9zLCB0ZXN0LCBiYXNlLCBzdGF0ZSkge1xuICB0ZXN0ID0gbWFrZVRlc3QodGVzdCk7XG4gIGlmICghYmFzZSkgYmFzZSA9IGV4cG9ydHMuYmFzZTtcbiAgdmFyIG1heCA9IHVuZGVmaW5lZDsoZnVuY3Rpb24gYyhub2RlLCBzdCwgb3ZlcnJpZGUpIHtcbiAgICBpZiAobm9kZS5zdGFydCA+IHBvcykgcmV0dXJuO1xuICAgIHZhciB0eXBlID0gb3ZlcnJpZGUgfHwgbm9kZS50eXBlO1xuICAgIGlmIChub2RlLmVuZCA8PSBwb3MgJiYgKCFtYXggfHwgbWF4Lm5vZGUuZW5kIDwgbm9kZS5lbmQpICYmIHRlc3QodHlwZSwgbm9kZSkpIG1heCA9IG5ldyBGb3VuZChub2RlLCBzdCk7XG4gICAgYmFzZVt0eXBlXShub2RlLCBzdCwgYyk7XG4gIH0pKG5vZGUsIHN0YXRlKTtcbiAgcmV0dXJuIG1heDtcbn1cblxuLy8gVXNlZCB0byBjcmVhdGUgYSBjdXN0b20gd2Fsa2VyLiBXaWxsIGZpbGwgaW4gYWxsIG1pc3Npbmcgbm9kZVxuLy8gdHlwZSBwcm9wZXJ0aWVzIHdpdGggdGhlIGRlZmF1bHRzLlxuXG5mdW5jdGlvbiBtYWtlKGZ1bmNzLCBiYXNlKSB7XG4gIGlmICghYmFzZSkgYmFzZSA9IGV4cG9ydHMuYmFzZTtcbiAgdmFyIHZpc2l0b3IgPSB7fTtcbiAgZm9yICh2YXIgdHlwZSBpbiBiYXNlKSB2aXNpdG9yW3R5cGVdID0gYmFzZVt0eXBlXTtcbiAgZm9yICh2YXIgdHlwZSBpbiBmdW5jcykgdmlzaXRvclt0eXBlXSA9IGZ1bmNzW3R5cGVdO1xuICByZXR1cm4gdmlzaXRvcjtcbn1cblxuZnVuY3Rpb24gc2tpcFRocm91Z2gobm9kZSwgc3QsIGMpIHtcbiAgYyhub2RlLCBzdCk7XG59XG5mdW5jdGlvbiBpZ25vcmUoX25vZGUsIF9zdCwgX2MpIHt9XG5cbi8vIE5vZGUgd2Fsa2Vycy5cblxudmFyIGJhc2UgPSB7fTtcblxuZXhwb3J0cy5iYXNlID0gYmFzZTtcbmJhc2UuUHJvZ3JhbSA9IGJhc2UuQmxvY2tTdGF0ZW1lbnQgPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgZm9yICh2YXIgaSA9IDA7IGkgPCBub2RlLmJvZHkubGVuZ3RoOyArK2kpIHtcbiAgICBjKG5vZGUuYm9keVtpXSwgc3QsIFwiU3RhdGVtZW50XCIpO1xuICB9XG59O1xuYmFzZS5TdGF0ZW1lbnQgPSBza2lwVGhyb3VnaDtcbmJhc2UuRW1wdHlTdGF0ZW1lbnQgPSBpZ25vcmU7XG5iYXNlLkV4cHJlc3Npb25TdGF0ZW1lbnQgPSBiYXNlLlBhcmVudGhlc2l6ZWRFeHByZXNzaW9uID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIHJldHVybiBjKG5vZGUuZXhwcmVzc2lvbiwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbn07XG5iYXNlLklmU3RhdGVtZW50ID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIGMobm9kZS50ZXN0LCBzdCwgXCJFeHByZXNzaW9uXCIpO1xuICBjKG5vZGUuY29uc2VxdWVudCwgc3QsIFwiU3RhdGVtZW50XCIpO1xuICBpZiAobm9kZS5hbHRlcm5hdGUpIGMobm9kZS5hbHRlcm5hdGUsIHN0LCBcIlN0YXRlbWVudFwiKTtcbn07XG5iYXNlLkxhYmVsZWRTdGF0ZW1lbnQgPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgcmV0dXJuIGMobm9kZS5ib2R5LCBzdCwgXCJTdGF0ZW1lbnRcIik7XG59O1xuYmFzZS5CcmVha1N0YXRlbWVudCA9IGJhc2UuQ29udGludWVTdGF0ZW1lbnQgPSBpZ25vcmU7XG5iYXNlLldpdGhTdGF0ZW1lbnQgPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgYyhub2RlLm9iamVjdCwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbiAgYyhub2RlLmJvZHksIHN0LCBcIlN0YXRlbWVudFwiKTtcbn07XG5iYXNlLlN3aXRjaFN0YXRlbWVudCA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBjKG5vZGUuZGlzY3JpbWluYW50LCBzdCwgXCJFeHByZXNzaW9uXCIpO1xuICBmb3IgKHZhciBpID0gMDsgaSA8IG5vZGUuY2FzZXMubGVuZ3RoOyArK2kpIHtcbiAgICB2YXIgY3MgPSBub2RlLmNhc2VzW2ldO1xuICAgIGlmIChjcy50ZXN0KSBjKGNzLnRlc3QsIHN0LCBcIkV4cHJlc3Npb25cIik7XG4gICAgZm9yICh2YXIgaiA9IDA7IGogPCBjcy5jb25zZXF1ZW50Lmxlbmd0aDsgKytqKSB7XG4gICAgICBjKGNzLmNvbnNlcXVlbnRbal0sIHN0LCBcIlN0YXRlbWVudFwiKTtcbiAgICB9XG4gIH1cbn07XG5iYXNlLlJldHVyblN0YXRlbWVudCA9IGJhc2UuWWllbGRFeHByZXNzaW9uID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIGlmIChub2RlLmFyZ3VtZW50KSBjKG5vZGUuYXJndW1lbnQsIHN0LCBcIkV4cHJlc3Npb25cIik7XG59O1xuYmFzZS5UaHJvd1N0YXRlbWVudCA9IGJhc2UuU3ByZWFkRWxlbWVudCA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICByZXR1cm4gYyhub2RlLmFyZ3VtZW50LCBzdCwgXCJFeHByZXNzaW9uXCIpO1xufTtcbmJhc2UuVHJ5U3RhdGVtZW50ID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIGMobm9kZS5ibG9jaywgc3QsIFwiU3RhdGVtZW50XCIpO1xuICBpZiAobm9kZS5oYW5kbGVyKSB7XG4gICAgYyhub2RlLmhhbmRsZXIucGFyYW0sIHN0LCBcIlBhdHRlcm5cIik7XG4gICAgYyhub2RlLmhhbmRsZXIuYm9keSwgc3QsIFwiU2NvcGVCb2R5XCIpO1xuICB9XG4gIGlmIChub2RlLmZpbmFsaXplcikgYyhub2RlLmZpbmFsaXplciwgc3QsIFwiU3RhdGVtZW50XCIpO1xufTtcbmJhc2UuV2hpbGVTdGF0ZW1lbnQgPSBiYXNlLkRvV2hpbGVTdGF0ZW1lbnQgPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgYyhub2RlLnRlc3QsIHN0LCBcIkV4cHJlc3Npb25cIik7XG4gIGMobm9kZS5ib2R5LCBzdCwgXCJTdGF0ZW1lbnRcIik7XG59O1xuYmFzZS5Gb3JTdGF0ZW1lbnQgPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgaWYgKG5vZGUuaW5pdCkgYyhub2RlLmluaXQsIHN0LCBcIkZvckluaXRcIik7XG4gIGlmIChub2RlLnRlc3QpIGMobm9kZS50ZXN0LCBzdCwgXCJFeHByZXNzaW9uXCIpO1xuICBpZiAobm9kZS51cGRhdGUpIGMobm9kZS51cGRhdGUsIHN0LCBcIkV4cHJlc3Npb25cIik7XG4gIGMobm9kZS5ib2R5LCBzdCwgXCJTdGF0ZW1lbnRcIik7XG59O1xuYmFzZS5Gb3JJblN0YXRlbWVudCA9IGJhc2UuRm9yT2ZTdGF0ZW1lbnQgPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgYyhub2RlLmxlZnQsIHN0LCBcIkZvckluaXRcIik7XG4gIGMobm9kZS5yaWdodCwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbiAgYyhub2RlLmJvZHksIHN0LCBcIlN0YXRlbWVudFwiKTtcbn07XG5iYXNlLkZvckluaXQgPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgaWYgKG5vZGUudHlwZSA9PSBcIlZhcmlhYmxlRGVjbGFyYXRpb25cIikgYyhub2RlLCBzdCk7ZWxzZSBjKG5vZGUsIHN0LCBcIkV4cHJlc3Npb25cIik7XG59O1xuYmFzZS5EZWJ1Z2dlclN0YXRlbWVudCA9IGlnbm9yZTtcblxuYmFzZS5GdW5jdGlvbkRlY2xhcmF0aW9uID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIHJldHVybiBjKG5vZGUsIHN0LCBcIkZ1bmN0aW9uXCIpO1xufTtcbmJhc2UuVmFyaWFibGVEZWNsYXJhdGlvbiA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBmb3IgKHZhciBpID0gMDsgaSA8IG5vZGUuZGVjbGFyYXRpb25zLmxlbmd0aDsgKytpKSB7XG4gICAgYyhub2RlLmRlY2xhcmF0aW9uc1tpXSwgc3QpO1xuICB9XG59O1xuYmFzZS5WYXJpYWJsZURlY2xhcmF0b3IgPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgYyhub2RlLmlkLCBzdCwgXCJQYXR0ZXJuXCIpO1xuICBpZiAobm9kZS5pbml0KSBjKG5vZGUuaW5pdCwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbn07XG5cbmJhc2UuRnVuY3Rpb24gPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgaWYgKG5vZGUuaWQpIGMobm9kZS5pZCwgc3QsIFwiUGF0dGVyblwiKTtcbiAgZm9yICh2YXIgaSA9IDA7IGkgPCBub2RlLnBhcmFtcy5sZW5ndGg7IGkrKykge1xuICAgIGMobm9kZS5wYXJhbXNbaV0sIHN0LCBcIlBhdHRlcm5cIik7XG4gIH1jKG5vZGUuYm9keSwgc3QsIG5vZGUuZXhwcmVzc2lvbiA/IFwiU2NvcGVFeHByZXNzaW9uXCIgOiBcIlNjb3BlQm9keVwiKTtcbn07XG4vLyBGSVhNRSBkcm9wIHRoZXNlIG5vZGUgdHlwZXMgaW4gbmV4dCBtYWpvciB2ZXJzaW9uXG4vLyAoVGhleSBhcmUgYXdrd2FyZCwgYW5kIGluIEVTNiBldmVyeSBibG9jayBjYW4gYmUgYSBzY29wZS4pXG5iYXNlLlNjb3BlQm9keSA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICByZXR1cm4gYyhub2RlLCBzdCwgXCJTdGF0ZW1lbnRcIik7XG59O1xuYmFzZS5TY29wZUV4cHJlc3Npb24gPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgcmV0dXJuIGMobm9kZSwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbn07XG5cbmJhc2UuUGF0dGVybiA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBpZiAobm9kZS50eXBlID09IFwiSWRlbnRpZmllclwiKSBjKG5vZGUsIHN0LCBcIlZhcmlhYmxlUGF0dGVyblwiKTtlbHNlIGlmIChub2RlLnR5cGUgPT0gXCJNZW1iZXJFeHByZXNzaW9uXCIpIGMobm9kZSwgc3QsIFwiTWVtYmVyUGF0dGVyblwiKTtlbHNlIGMobm9kZSwgc3QpO1xufTtcbmJhc2UuVmFyaWFibGVQYXR0ZXJuID0gaWdub3JlO1xuYmFzZS5NZW1iZXJQYXR0ZXJuID0gc2tpcFRocm91Z2g7XG5iYXNlLlJlc3RFbGVtZW50ID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIHJldHVybiBjKG5vZGUuYXJndW1lbnQsIHN0LCBcIlBhdHRlcm5cIik7XG59O1xuYmFzZS5BcnJheVBhdHRlcm4gPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgZm9yICh2YXIgaSA9IDA7IGkgPCBub2RlLmVsZW1lbnRzLmxlbmd0aDsgKytpKSB7XG4gICAgdmFyIGVsdCA9IG5vZGUuZWxlbWVudHNbaV07XG4gICAgaWYgKGVsdCkgYyhlbHQsIHN0LCBcIlBhdHRlcm5cIik7XG4gIH1cbn07XG5iYXNlLk9iamVjdFBhdHRlcm4gPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgZm9yICh2YXIgaSA9IDA7IGkgPCBub2RlLnByb3BlcnRpZXMubGVuZ3RoOyArK2kpIHtcbiAgICBjKG5vZGUucHJvcGVydGllc1tpXS52YWx1ZSwgc3QsIFwiUGF0dGVyblwiKTtcbiAgfVxufTtcblxuYmFzZS5FeHByZXNzaW9uID0gc2tpcFRocm91Z2g7XG5iYXNlLlRoaXNFeHByZXNzaW9uID0gYmFzZS5TdXBlciA9IGJhc2UuTWV0YVByb3BlcnR5ID0gaWdub3JlO1xuYmFzZS5BcnJheUV4cHJlc3Npb24gPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgZm9yICh2YXIgaSA9IDA7IGkgPCBub2RlLmVsZW1lbnRzLmxlbmd0aDsgKytpKSB7XG4gICAgdmFyIGVsdCA9IG5vZGUuZWxlbWVudHNbaV07XG4gICAgaWYgKGVsdCkgYyhlbHQsIHN0LCBcIkV4cHJlc3Npb25cIik7XG4gIH1cbn07XG5iYXNlLk9iamVjdEV4cHJlc3Npb24gPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgZm9yICh2YXIgaSA9IDA7IGkgPCBub2RlLnByb3BlcnRpZXMubGVuZ3RoOyArK2kpIHtcbiAgICBjKG5vZGUucHJvcGVydGllc1tpXSwgc3QpO1xuICB9XG59O1xuYmFzZS5GdW5jdGlvbkV4cHJlc3Npb24gPSBiYXNlLkFycm93RnVuY3Rpb25FeHByZXNzaW9uID0gYmFzZS5GdW5jdGlvbkRlY2xhcmF0aW9uO1xuYmFzZS5TZXF1ZW5jZUV4cHJlc3Npb24gPSBiYXNlLlRlbXBsYXRlTGl0ZXJhbCA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBmb3IgKHZhciBpID0gMDsgaSA8IG5vZGUuZXhwcmVzc2lvbnMubGVuZ3RoOyArK2kpIHtcbiAgICBjKG5vZGUuZXhwcmVzc2lvbnNbaV0sIHN0LCBcIkV4cHJlc3Npb25cIik7XG4gIH1cbn07XG5iYXNlLlVuYXJ5RXhwcmVzc2lvbiA9IGJhc2UuVXBkYXRlRXhwcmVzc2lvbiA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBjKG5vZGUuYXJndW1lbnQsIHN0LCBcIkV4cHJlc3Npb25cIik7XG59O1xuYmFzZS5CaW5hcnlFeHByZXNzaW9uID0gYmFzZS5Mb2dpY2FsRXhwcmVzc2lvbiA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBjKG5vZGUubGVmdCwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbiAgYyhub2RlLnJpZ2h0LCBzdCwgXCJFeHByZXNzaW9uXCIpO1xufTtcbmJhc2UuQXNzaWdubWVudEV4cHJlc3Npb24gPSBiYXNlLkFzc2lnbm1lbnRQYXR0ZXJuID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIGMobm9kZS5sZWZ0LCBzdCwgXCJQYXR0ZXJuXCIpO1xuICBjKG5vZGUucmlnaHQsIHN0LCBcIkV4cHJlc3Npb25cIik7XG59O1xuYmFzZS5Db25kaXRpb25hbEV4cHJlc3Npb24gPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgYyhub2RlLnRlc3QsIHN0LCBcIkV4cHJlc3Npb25cIik7XG4gIGMobm9kZS5jb25zZXF1ZW50LCBzdCwgXCJFeHByZXNzaW9uXCIpO1xuICBjKG5vZGUuYWx0ZXJuYXRlLCBzdCwgXCJFeHByZXNzaW9uXCIpO1xufTtcbmJhc2UuTmV3RXhwcmVzc2lvbiA9IGJhc2UuQ2FsbEV4cHJlc3Npb24gPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgYyhub2RlLmNhbGxlZSwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbiAgaWYgKG5vZGUuYXJndW1lbnRzKSBmb3IgKHZhciBpID0gMDsgaSA8IG5vZGUuYXJndW1lbnRzLmxlbmd0aDsgKytpKSB7XG4gICAgYyhub2RlLmFyZ3VtZW50c1tpXSwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbiAgfVxufTtcbmJhc2UuTWVtYmVyRXhwcmVzc2lvbiA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBjKG5vZGUub2JqZWN0LCBzdCwgXCJFeHByZXNzaW9uXCIpO1xuICBpZiAobm9kZS5jb21wdXRlZCkgYyhub2RlLnByb3BlcnR5LCBzdCwgXCJFeHByZXNzaW9uXCIpO1xufTtcbmJhc2UuRXhwb3J0TmFtZWREZWNsYXJhdGlvbiA9IGJhc2UuRXhwb3J0RGVmYXVsdERlY2xhcmF0aW9uID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIGlmIChub2RlLmRlY2xhcmF0aW9uKSBjKG5vZGUuZGVjbGFyYXRpb24sIHN0KTtcbiAgaWYgKG5vZGUuc291cmNlKSBjKG5vZGUuc291cmNlLCBzdCwgXCJFeHByZXNzaW9uXCIpO1xufTtcbmJhc2UuRXhwb3J0QWxsRGVjbGFyYXRpb24gPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgYyhub2RlLnNvdXJjZSwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbn07XG5iYXNlLkltcG9ydERlY2xhcmF0aW9uID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIGZvciAodmFyIGkgPSAwOyBpIDwgbm9kZS5zcGVjaWZpZXJzLmxlbmd0aDsgaSsrKSB7XG4gICAgYyhub2RlLnNwZWNpZmllcnNbaV0sIHN0KTtcbiAgfWMobm9kZS5zb3VyY2UsIHN0LCBcIkV4cHJlc3Npb25cIik7XG59O1xuYmFzZS5JbXBvcnRTcGVjaWZpZXIgPSBiYXNlLkltcG9ydERlZmF1bHRTcGVjaWZpZXIgPSBiYXNlLkltcG9ydE5hbWVzcGFjZVNwZWNpZmllciA9IGJhc2UuSWRlbnRpZmllciA9IGJhc2UuTGl0ZXJhbCA9IGlnbm9yZTtcblxuYmFzZS5UYWdnZWRUZW1wbGF0ZUV4cHJlc3Npb24gPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgYyhub2RlLnRhZywgc3QsIFwiRXhwcmVzc2lvblwiKTtcbiAgYyhub2RlLnF1YXNpLCBzdCk7XG59O1xuYmFzZS5DbGFzc0RlY2xhcmF0aW9uID0gYmFzZS5DbGFzc0V4cHJlc3Npb24gPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgcmV0dXJuIGMobm9kZSwgc3QsIFwiQ2xhc3NcIik7XG59O1xuYmFzZS5DbGFzcyA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBpZiAobm9kZS5pZCkgYyhub2RlLmlkLCBzdCwgXCJQYXR0ZXJuXCIpO1xuICBpZiAobm9kZS5zdXBlckNsYXNzKSBjKG5vZGUuc3VwZXJDbGFzcywgc3QsIFwiRXhwcmVzc2lvblwiKTtcbiAgZm9yICh2YXIgaSA9IDA7IGkgPCBub2RlLmJvZHkuYm9keS5sZW5ndGg7IGkrKykge1xuICAgIGMobm9kZS5ib2R5LmJvZHlbaV0sIHN0KTtcbiAgfVxufTtcbmJhc2UuTWV0aG9kRGVmaW5pdGlvbiA9IGJhc2UuUHJvcGVydHkgPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgaWYgKG5vZGUuY29tcHV0ZWQpIGMobm9kZS5rZXksIHN0LCBcIkV4cHJlc3Npb25cIik7XG4gIGMobm9kZS52YWx1ZSwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbn07XG5iYXNlLkNvbXByZWhlbnNpb25FeHByZXNzaW9uID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIGZvciAodmFyIGkgPSAwOyBpIDwgbm9kZS5ibG9ja3MubGVuZ3RoOyBpKyspIHtcbiAgICBjKG5vZGUuYmxvY2tzW2ldLnJpZ2h0LCBzdCwgXCJFeHByZXNzaW9uXCIpO1xuICB9Yyhub2RlLmJvZHksIHN0LCBcIkV4cHJlc3Npb25cIik7XG59O1xuXG59LHt9XX0se30sWzFdKSgxKVxufSk7IiwiaWYgKHR5cGVvZiBPYmplY3QuY3JlYXRlID09PSAnZnVuY3Rpb24nKSB7XG4gIC8vIGltcGxlbWVudGF0aW9uIGZyb20gc3RhbmRhcmQgbm9kZS5qcyAndXRpbCcgbW9kdWxlXG4gIG1vZHVsZS5leHBvcnRzID0gZnVuY3Rpb24gaW5oZXJpdHMoY3Rvciwgc3VwZXJDdG9yKSB7XG4gICAgY3Rvci5zdXBlcl8gPSBzdXBlckN0b3JcbiAgICBjdG9yLnByb3RvdHlwZSA9IE9iamVjdC5jcmVhdGUoc3VwZXJDdG9yLnByb3RvdHlwZSwge1xuICAgICAgY29uc3RydWN0b3I6IHtcbiAgICAgICAgdmFsdWU6IGN0b3IsXG4gICAgICAgIGVudW1lcmFibGU6IGZhbHNlLFxuICAgICAgICB3cml0YWJsZTogdHJ1ZSxcbiAgICAgICAgY29uZmlndXJhYmxlOiB0cnVlXG4gICAgICB9XG4gICAgfSk7XG4gIH07XG59IGVsc2Uge1xuICAvLyBvbGQgc2Nob29sIHNoaW0gZm9yIG9sZCBicm93c2Vyc1xuICBtb2R1bGUuZXhwb3J0cyA9IGZ1bmN0aW9uIGluaGVyaXRzKGN0b3IsIHN1cGVyQ3Rvcikge1xuICAgIGN0b3Iuc3VwZXJfID0gc3VwZXJDdG9yXG4gICAgdmFyIFRlbXBDdG9yID0gZnVuY3Rpb24gKCkge31cbiAgICBUZW1wQ3Rvci5wcm90b3R5cGUgPSBzdXBlckN0b3IucHJvdG90eXBlXG4gICAgY3Rvci5wcm90b3R5cGUgPSBuZXcgVGVtcEN0b3IoKVxuICAgIGN0b3IucHJvdG90eXBlLmNvbnN0cnVjdG9yID0gY3RvclxuICB9XG59XG4iLCIvLyBzaGltIGZvciB1c2luZyBwcm9jZXNzIGluIGJyb3dzZXJcblxudmFyIHByb2Nlc3MgPSBtb2R1bGUuZXhwb3J0cyA9IHt9O1xudmFyIHF1ZXVlID0gW107XG52YXIgZHJhaW5pbmcgPSBmYWxzZTtcbnZhciBjdXJyZW50UXVldWU7XG52YXIgcXVldWVJbmRleCA9IC0xO1xuXG5mdW5jdGlvbiBjbGVhblVwTmV4dFRpY2soKSB7XG4gICAgZHJhaW5pbmcgPSBmYWxzZTtcbiAgICBpZiAoY3VycmVudFF1ZXVlLmxlbmd0aCkge1xuICAgICAgICBxdWV1ZSA9IGN1cnJlbnRRdWV1ZS5jb25jYXQocXVldWUpO1xuICAgIH0gZWxzZSB7XG4gICAgICAgIHF1ZXVlSW5kZXggPSAtMTtcbiAgICB9XG4gICAgaWYgKHF1ZXVlLmxlbmd0aCkge1xuICAgICAgICBkcmFpblF1ZXVlKCk7XG4gICAgfVxufVxuXG5mdW5jdGlvbiBkcmFpblF1ZXVlKCkge1xuICAgIGlmIChkcmFpbmluZykge1xuICAgICAgICByZXR1cm47XG4gICAgfVxuICAgIHZhciB0aW1lb3V0ID0gc2V0VGltZW91dChjbGVhblVwTmV4dFRpY2spO1xuICAgIGRyYWluaW5nID0gdHJ1ZTtcblxuICAgIHZhciBsZW4gPSBxdWV1ZS5sZW5ndGg7XG4gICAgd2hpbGUobGVuKSB7XG4gICAgICAgIGN1cnJlbnRRdWV1ZSA9IHF1ZXVlO1xuICAgICAgICBxdWV1ZSA9IFtdO1xuICAgICAgICB3aGlsZSAoKytxdWV1ZUluZGV4IDwgbGVuKSB7XG4gICAgICAgICAgICBjdXJyZW50UXVldWVbcXVldWVJbmRleF0ucnVuKCk7XG4gICAgICAgIH1cbiAgICAgICAgcXVldWVJbmRleCA9IC0xO1xuICAgICAgICBsZW4gPSBxdWV1ZS5sZW5ndGg7XG4gICAgfVxuICAgIGN1cnJlbnRRdWV1ZSA9IG51bGw7XG4gICAgZHJhaW5pbmcgPSBmYWxzZTtcbiAgICBjbGVhclRpbWVvdXQodGltZW91dCk7XG59XG5cbnByb2Nlc3MubmV4dFRpY2sgPSBmdW5jdGlvbiAoZnVuKSB7XG4gICAgdmFyIGFyZ3MgPSBuZXcgQXJyYXkoYXJndW1lbnRzLmxlbmd0aCAtIDEpO1xuICAgIGlmIChhcmd1bWVudHMubGVuZ3RoID4gMSkge1xuICAgICAgICBmb3IgKHZhciBpID0gMTsgaSA8IGFyZ3VtZW50cy5sZW5ndGg7IGkrKykge1xuICAgICAgICAgICAgYXJnc1tpIC0gMV0gPSBhcmd1bWVudHNbaV07XG4gICAgICAgIH1cbiAgICB9XG4gICAgcXVldWUucHVzaChuZXcgSXRlbShmdW4sIGFyZ3MpKTtcbiAgICBpZiAocXVldWUubGVuZ3RoID09PSAxICYmICFkcmFpbmluZykge1xuICAgICAgICBzZXRUaW1lb3V0KGRyYWluUXVldWUsIDApO1xuICAgIH1cbn07XG5cbi8vIHY4IGxpa2VzIHByZWRpY3RpYmxlIG9iamVjdHNcbmZ1bmN0aW9uIEl0ZW0oZnVuLCBhcnJheSkge1xuICAgIHRoaXMuZnVuID0gZnVuO1xuICAgIHRoaXMuYXJyYXkgPSBhcnJheTtcbn1cbkl0ZW0ucHJvdG90eXBlLnJ1biA9IGZ1bmN0aW9uICgpIHtcbiAgICB0aGlzLmZ1bi5hcHBseShudWxsLCB0aGlzLmFycmF5KTtcbn07XG5wcm9jZXNzLnRpdGxlID0gJ2Jyb3dzZXInO1xucHJvY2Vzcy5icm93c2VyID0gdHJ1ZTtcbnByb2Nlc3MuZW52ID0ge307XG5wcm9jZXNzLmFyZ3YgPSBbXTtcbnByb2Nlc3MudmVyc2lvbiA9ICcnOyAvLyBlbXB0eSBzdHJpbmcgdG8gYXZvaWQgcmVnZXhwIGlzc3Vlc1xucHJvY2Vzcy52ZXJzaW9ucyA9IHt9O1xuXG5mdW5jdGlvbiBub29wKCkge31cblxucHJvY2Vzcy5vbiA9IG5vb3A7XG5wcm9jZXNzLmFkZExpc3RlbmVyID0gbm9vcDtcbnByb2Nlc3Mub25jZSA9IG5vb3A7XG5wcm9jZXNzLm9mZiA9IG5vb3A7XG5wcm9jZXNzLnJlbW92ZUxpc3RlbmVyID0gbm9vcDtcbnByb2Nlc3MucmVtb3ZlQWxsTGlzdGVuZXJzID0gbm9vcDtcbnByb2Nlc3MuZW1pdCA9IG5vb3A7XG5cbnByb2Nlc3MuYmluZGluZyA9IGZ1bmN0aW9uIChuYW1lKSB7XG4gICAgdGhyb3cgbmV3IEVycm9yKCdwcm9jZXNzLmJpbmRpbmcgaXMgbm90IHN1cHBvcnRlZCcpO1xufTtcblxuLy8gVE9ETyhzaHR5bG1hbilcbnByb2Nlc3MuY3dkID0gZnVuY3Rpb24gKCkgeyByZXR1cm4gJy8nIH07XG5wcm9jZXNzLmNoZGlyID0gZnVuY3Rpb24gKGRpcikge1xuICAgIHRocm93IG5ldyBFcnJvcigncHJvY2Vzcy5jaGRpciBpcyBub3Qgc3VwcG9ydGVkJyk7XG59O1xucHJvY2Vzcy51bWFzayA9IGZ1bmN0aW9uKCkgeyByZXR1cm4gMDsgfTtcbiIsIm1vZHVsZS5leHBvcnRzID0gZnVuY3Rpb24gaXNCdWZmZXIoYXJnKSB7XG4gIHJldHVybiBhcmcgJiYgdHlwZW9mIGFyZyA9PT0gJ29iamVjdCdcbiAgICAmJiB0eXBlb2YgYXJnLmNvcHkgPT09ICdmdW5jdGlvbidcbiAgICAmJiB0eXBlb2YgYXJnLmZpbGwgPT09ICdmdW5jdGlvbidcbiAgICAmJiB0eXBlb2YgYXJnLnJlYWRVSW50OCA9PT0gJ2Z1bmN0aW9uJztcbn0iLCIvLyBDb3B5cmlnaHQgSm95ZW50LCBJbmMuIGFuZCBvdGhlciBOb2RlIGNvbnRyaWJ1dG9ycy5cbi8vXG4vLyBQZXJtaXNzaW9uIGlzIGhlcmVieSBncmFudGVkLCBmcmVlIG9mIGNoYXJnZSwgdG8gYW55IHBlcnNvbiBvYnRhaW5pbmcgYVxuLy8gY29weSBvZiB0aGlzIHNvZnR3YXJlIGFuZCBhc3NvY2lhdGVkIGRvY3VtZW50YXRpb24gZmlsZXMgKHRoZVxuLy8gXCJTb2Z0d2FyZVwiKSwgdG8gZGVhbCBpbiB0aGUgU29mdHdhcmUgd2l0aG91dCByZXN0cmljdGlvbiwgaW5jbHVkaW5nXG4vLyB3aXRob3V0IGxpbWl0YXRpb24gdGhlIHJpZ2h0cyB0byB1c2UsIGNvcHksIG1vZGlmeSwgbWVyZ2UsIHB1Ymxpc2gsXG4vLyBkaXN0cmlidXRlLCBzdWJsaWNlbnNlLCBhbmQvb3Igc2VsbCBjb3BpZXMgb2YgdGhlIFNvZnR3YXJlLCBhbmQgdG8gcGVybWl0XG4vLyBwZXJzb25zIHRvIHdob20gdGhlIFNvZnR3YXJlIGlzIGZ1cm5pc2hlZCB0byBkbyBzbywgc3ViamVjdCB0byB0aGVcbi8vIGZvbGxvd2luZyBjb25kaXRpb25zOlxuLy9cbi8vIFRoZSBhYm92ZSBjb3B5cmlnaHQgbm90aWNlIGFuZCB0aGlzIHBlcm1pc3Npb24gbm90aWNlIHNoYWxsIGJlIGluY2x1ZGVkXG4vLyBpbiBhbGwgY29waWVzIG9yIHN1YnN0YW50aWFsIHBvcnRpb25zIG9mIHRoZSBTb2Z0d2FyZS5cbi8vXG4vLyBUSEUgU09GVFdBUkUgSVMgUFJPVklERUQgXCJBUyBJU1wiLCBXSVRIT1VUIFdBUlJBTlRZIE9GIEFOWSBLSU5ELCBFWFBSRVNTXG4vLyBPUiBJTVBMSUVELCBJTkNMVURJTkcgQlVUIE5PVCBMSU1JVEVEIFRPIFRIRSBXQVJSQU5USUVTIE9GXG4vLyBNRVJDSEFOVEFCSUxJVFksIEZJVE5FU1MgRk9SIEEgUEFSVElDVUxBUiBQVVJQT1NFIEFORCBOT05JTkZSSU5HRU1FTlQuIElOXG4vLyBOTyBFVkVOVCBTSEFMTCBUSEUgQVVUSE9SUyBPUiBDT1BZUklHSFQgSE9MREVSUyBCRSBMSUFCTEUgRk9SIEFOWSBDTEFJTSxcbi8vIERBTUFHRVMgT1IgT1RIRVIgTElBQklMSVRZLCBXSEVUSEVSIElOIEFOIEFDVElPTiBPRiBDT05UUkFDVCwgVE9SVCBPUlxuLy8gT1RIRVJXSVNFLCBBUklTSU5HIEZST00sIE9VVCBPRiBPUiBJTiBDT05ORUNUSU9OIFdJVEggVEhFIFNPRlRXQVJFIE9SIFRIRVxuLy8gVVNFIE9SIE9USEVSIERFQUxJTkdTIElOIFRIRSBTT0ZUV0FSRS5cblxudmFyIGZvcm1hdFJlZ0V4cCA9IC8lW3NkaiVdL2c7XG5leHBvcnRzLmZvcm1hdCA9IGZ1bmN0aW9uKGYpIHtcbiAgaWYgKCFpc1N0cmluZyhmKSkge1xuICAgIHZhciBvYmplY3RzID0gW107XG4gICAgZm9yICh2YXIgaSA9IDA7IGkgPCBhcmd1bWVudHMubGVuZ3RoOyBpKyspIHtcbiAgICAgIG9iamVjdHMucHVzaChpbnNwZWN0KGFyZ3VtZW50c1tpXSkpO1xuICAgIH1cbiAgICByZXR1cm4gb2JqZWN0cy5qb2luKCcgJyk7XG4gIH1cblxuICB2YXIgaSA9IDE7XG4gIHZhciBhcmdzID0gYXJndW1lbnRzO1xuICB2YXIgbGVuID0gYXJncy5sZW5ndGg7XG4gIHZhciBzdHIgPSBTdHJpbmcoZikucmVwbGFjZShmb3JtYXRSZWdFeHAsIGZ1bmN0aW9uKHgpIHtcbiAgICBpZiAoeCA9PT0gJyUlJykgcmV0dXJuICclJztcbiAgICBpZiAoaSA+PSBsZW4pIHJldHVybiB4O1xuICAgIHN3aXRjaCAoeCkge1xuICAgICAgY2FzZSAnJXMnOiByZXR1cm4gU3RyaW5nKGFyZ3NbaSsrXSk7XG4gICAgICBjYXNlICclZCc6IHJldHVybiBOdW1iZXIoYXJnc1tpKytdKTtcbiAgICAgIGNhc2UgJyVqJzpcbiAgICAgICAgdHJ5IHtcbiAgICAgICAgICByZXR1cm4gSlNPTi5zdHJpbmdpZnkoYXJnc1tpKytdKTtcbiAgICAgICAgfSBjYXRjaCAoXykge1xuICAgICAgICAgIHJldHVybiAnW0NpcmN1bGFyXSc7XG4gICAgICAgIH1cbiAgICAgIGRlZmF1bHQ6XG4gICAgICAgIHJldHVybiB4O1xuICAgIH1cbiAgfSk7XG4gIGZvciAodmFyIHggPSBhcmdzW2ldOyBpIDwgbGVuOyB4ID0gYXJnc1srK2ldKSB7XG4gICAgaWYgKGlzTnVsbCh4KSB8fCAhaXNPYmplY3QoeCkpIHtcbiAgICAgIHN0ciArPSAnICcgKyB4O1xuICAgIH0gZWxzZSB7XG4gICAgICBzdHIgKz0gJyAnICsgaW5zcGVjdCh4KTtcbiAgICB9XG4gIH1cbiAgcmV0dXJuIHN0cjtcbn07XG5cblxuLy8gTWFyayB0aGF0IGEgbWV0aG9kIHNob3VsZCBub3QgYmUgdXNlZC5cbi8vIFJldHVybnMgYSBtb2RpZmllZCBmdW5jdGlvbiB3aGljaCB3YXJucyBvbmNlIGJ5IGRlZmF1bHQuXG4vLyBJZiAtLW5vLWRlcHJlY2F0aW9uIGlzIHNldCwgdGhlbiBpdCBpcyBhIG5vLW9wLlxuZXhwb3J0cy5kZXByZWNhdGUgPSBmdW5jdGlvbihmbiwgbXNnKSB7XG4gIC8vIEFsbG93IGZvciBkZXByZWNhdGluZyB0aGluZ3MgaW4gdGhlIHByb2Nlc3Mgb2Ygc3RhcnRpbmcgdXAuXG4gIGlmIChpc1VuZGVmaW5lZChnbG9iYWwucHJvY2VzcykpIHtcbiAgICByZXR1cm4gZnVuY3Rpb24oKSB7XG4gICAgICByZXR1cm4gZXhwb3J0cy5kZXByZWNhdGUoZm4sIG1zZykuYXBwbHkodGhpcywgYXJndW1lbnRzKTtcbiAgICB9O1xuICB9XG5cbiAgaWYgKHByb2Nlc3Mubm9EZXByZWNhdGlvbiA9PT0gdHJ1ZSkge1xuICAgIHJldHVybiBmbjtcbiAgfVxuXG4gIHZhciB3YXJuZWQgPSBmYWxzZTtcbiAgZnVuY3Rpb24gZGVwcmVjYXRlZCgpIHtcbiAgICBpZiAoIXdhcm5lZCkge1xuICAgICAgaWYgKHByb2Nlc3MudGhyb3dEZXByZWNhdGlvbikge1xuICAgICAgICB0aHJvdyBuZXcgRXJyb3IobXNnKTtcbiAgICAgIH0gZWxzZSBpZiAocHJvY2Vzcy50cmFjZURlcHJlY2F0aW9uKSB7XG4gICAgICAgIGNvbnNvbGUudHJhY2UobXNnKTtcbiAgICAgIH0gZWxzZSB7XG4gICAgICAgIGNvbnNvbGUuZXJyb3IobXNnKTtcbiAgICAgIH1cbiAgICAgIHdhcm5lZCA9IHRydWU7XG4gICAgfVxuICAgIHJldHVybiBmbi5hcHBseSh0aGlzLCBhcmd1bWVudHMpO1xuICB9XG5cbiAgcmV0dXJuIGRlcHJlY2F0ZWQ7XG59O1xuXG5cbnZhciBkZWJ1Z3MgPSB7fTtcbnZhciBkZWJ1Z0Vudmlyb247XG5leHBvcnRzLmRlYnVnbG9nID0gZnVuY3Rpb24oc2V0KSB7XG4gIGlmIChpc1VuZGVmaW5lZChkZWJ1Z0Vudmlyb24pKVxuICAgIGRlYnVnRW52aXJvbiA9IHByb2Nlc3MuZW52Lk5PREVfREVCVUcgfHwgJyc7XG4gIHNldCA9IHNldC50b1VwcGVyQ2FzZSgpO1xuICBpZiAoIWRlYnVnc1tzZXRdKSB7XG4gICAgaWYgKG5ldyBSZWdFeHAoJ1xcXFxiJyArIHNldCArICdcXFxcYicsICdpJykudGVzdChkZWJ1Z0Vudmlyb24pKSB7XG4gICAgICB2YXIgcGlkID0gcHJvY2Vzcy5waWQ7XG4gICAgICBkZWJ1Z3Nbc2V0XSA9IGZ1bmN0aW9uKCkge1xuICAgICAgICB2YXIgbXNnID0gZXhwb3J0cy5mb3JtYXQuYXBwbHkoZXhwb3J0cywgYXJndW1lbnRzKTtcbiAgICAgICAgY29uc29sZS5lcnJvcignJXMgJWQ6ICVzJywgc2V0LCBwaWQsIG1zZyk7XG4gICAgICB9O1xuICAgIH0gZWxzZSB7XG4gICAgICBkZWJ1Z3Nbc2V0XSA9IGZ1bmN0aW9uKCkge307XG4gICAgfVxuICB9XG4gIHJldHVybiBkZWJ1Z3Nbc2V0XTtcbn07XG5cblxuLyoqXG4gKiBFY2hvcyB0aGUgdmFsdWUgb2YgYSB2YWx1ZS4gVHJ5cyB0byBwcmludCB0aGUgdmFsdWUgb3V0XG4gKiBpbiB0aGUgYmVzdCB3YXkgcG9zc2libGUgZ2l2ZW4gdGhlIGRpZmZlcmVudCB0eXBlcy5cbiAqXG4gKiBAcGFyYW0ge09iamVjdH0gb2JqIFRoZSBvYmplY3QgdG8gcHJpbnQgb3V0LlxuICogQHBhcmFtIHtPYmplY3R9IG9wdHMgT3B0aW9uYWwgb3B0aW9ucyBvYmplY3QgdGhhdCBhbHRlcnMgdGhlIG91dHB1dC5cbiAqL1xuLyogbGVnYWN5OiBvYmosIHNob3dIaWRkZW4sIGRlcHRoLCBjb2xvcnMqL1xuZnVuY3Rpb24gaW5zcGVjdChvYmosIG9wdHMpIHtcbiAgLy8gZGVmYXVsdCBvcHRpb25zXG4gIHZhciBjdHggPSB7XG4gICAgc2VlbjogW10sXG4gICAgc3R5bGl6ZTogc3R5bGl6ZU5vQ29sb3JcbiAgfTtcbiAgLy8gbGVnYWN5Li4uXG4gIGlmIChhcmd1bWVudHMubGVuZ3RoID49IDMpIGN0eC5kZXB0aCA9IGFyZ3VtZW50c1syXTtcbiAgaWYgKGFyZ3VtZW50cy5sZW5ndGggPj0gNCkgY3R4LmNvbG9ycyA9IGFyZ3VtZW50c1szXTtcbiAgaWYgKGlzQm9vbGVhbihvcHRzKSkge1xuICAgIC8vIGxlZ2FjeS4uLlxuICAgIGN0eC5zaG93SGlkZGVuID0gb3B0cztcbiAgfSBlbHNlIGlmIChvcHRzKSB7XG4gICAgLy8gZ290IGFuIFwib3B0aW9uc1wiIG9iamVjdFxuICAgIGV4cG9ydHMuX2V4dGVuZChjdHgsIG9wdHMpO1xuICB9XG4gIC8vIHNldCBkZWZhdWx0IG9wdGlvbnNcbiAgaWYgKGlzVW5kZWZpbmVkKGN0eC5zaG93SGlkZGVuKSkgY3R4LnNob3dIaWRkZW4gPSBmYWxzZTtcbiAgaWYgKGlzVW5kZWZpbmVkKGN0eC5kZXB0aCkpIGN0eC5kZXB0aCA9IDI7XG4gIGlmIChpc1VuZGVmaW5lZChjdHguY29sb3JzKSkgY3R4LmNvbG9ycyA9IGZhbHNlO1xuICBpZiAoaXNVbmRlZmluZWQoY3R4LmN1c3RvbUluc3BlY3QpKSBjdHguY3VzdG9tSW5zcGVjdCA9IHRydWU7XG4gIGlmIChjdHguY29sb3JzKSBjdHguc3R5bGl6ZSA9IHN0eWxpemVXaXRoQ29sb3I7XG4gIHJldHVybiBmb3JtYXRWYWx1ZShjdHgsIG9iaiwgY3R4LmRlcHRoKTtcbn1cbmV4cG9ydHMuaW5zcGVjdCA9IGluc3BlY3Q7XG5cblxuLy8gaHR0cDovL2VuLndpa2lwZWRpYS5vcmcvd2lraS9BTlNJX2VzY2FwZV9jb2RlI2dyYXBoaWNzXG5pbnNwZWN0LmNvbG9ycyA9IHtcbiAgJ2JvbGQnIDogWzEsIDIyXSxcbiAgJ2l0YWxpYycgOiBbMywgMjNdLFxuICAndW5kZXJsaW5lJyA6IFs0LCAyNF0sXG4gICdpbnZlcnNlJyA6IFs3LCAyN10sXG4gICd3aGl0ZScgOiBbMzcsIDM5XSxcbiAgJ2dyZXknIDogWzkwLCAzOV0sXG4gICdibGFjaycgOiBbMzAsIDM5XSxcbiAgJ2JsdWUnIDogWzM0LCAzOV0sXG4gICdjeWFuJyA6IFszNiwgMzldLFxuICAnZ3JlZW4nIDogWzMyLCAzOV0sXG4gICdtYWdlbnRhJyA6IFszNSwgMzldLFxuICAncmVkJyA6IFszMSwgMzldLFxuICAneWVsbG93JyA6IFszMywgMzldXG59O1xuXG4vLyBEb24ndCB1c2UgJ2JsdWUnIG5vdCB2aXNpYmxlIG9uIGNtZC5leGVcbmluc3BlY3Quc3R5bGVzID0ge1xuICAnc3BlY2lhbCc6ICdjeWFuJyxcbiAgJ251bWJlcic6ICd5ZWxsb3cnLFxuICAnYm9vbGVhbic6ICd5ZWxsb3cnLFxuICAndW5kZWZpbmVkJzogJ2dyZXknLFxuICAnbnVsbCc6ICdib2xkJyxcbiAgJ3N0cmluZyc6ICdncmVlbicsXG4gICdkYXRlJzogJ21hZ2VudGEnLFxuICAvLyBcIm5hbWVcIjogaW50ZW50aW9uYWxseSBub3Qgc3R5bGluZ1xuICAncmVnZXhwJzogJ3JlZCdcbn07XG5cblxuZnVuY3Rpb24gc3R5bGl6ZVdpdGhDb2xvcihzdHIsIHN0eWxlVHlwZSkge1xuICB2YXIgc3R5bGUgPSBpbnNwZWN0LnN0eWxlc1tzdHlsZVR5cGVdO1xuXG4gIGlmIChzdHlsZSkge1xuICAgIHJldHVybiAnXFx1MDAxYlsnICsgaW5zcGVjdC5jb2xvcnNbc3R5bGVdWzBdICsgJ20nICsgc3RyICtcbiAgICAgICAgICAgJ1xcdTAwMWJbJyArIGluc3BlY3QuY29sb3JzW3N0eWxlXVsxXSArICdtJztcbiAgfSBlbHNlIHtcbiAgICByZXR1cm4gc3RyO1xuICB9XG59XG5cblxuZnVuY3Rpb24gc3R5bGl6ZU5vQ29sb3Ioc3RyLCBzdHlsZVR5cGUpIHtcbiAgcmV0dXJuIHN0cjtcbn1cblxuXG5mdW5jdGlvbiBhcnJheVRvSGFzaChhcnJheSkge1xuICB2YXIgaGFzaCA9IHt9O1xuXG4gIGFycmF5LmZvckVhY2goZnVuY3Rpb24odmFsLCBpZHgpIHtcbiAgICBoYXNoW3ZhbF0gPSB0cnVlO1xuICB9KTtcblxuICByZXR1cm4gaGFzaDtcbn1cblxuXG5mdW5jdGlvbiBmb3JtYXRWYWx1ZShjdHgsIHZhbHVlLCByZWN1cnNlVGltZXMpIHtcbiAgLy8gUHJvdmlkZSBhIGhvb2sgZm9yIHVzZXItc3BlY2lmaWVkIGluc3BlY3QgZnVuY3Rpb25zLlxuICAvLyBDaGVjayB0aGF0IHZhbHVlIGlzIGFuIG9iamVjdCB3aXRoIGFuIGluc3BlY3QgZnVuY3Rpb24gb24gaXRcbiAgaWYgKGN0eC5jdXN0b21JbnNwZWN0ICYmXG4gICAgICB2YWx1ZSAmJlxuICAgICAgaXNGdW5jdGlvbih2YWx1ZS5pbnNwZWN0KSAmJlxuICAgICAgLy8gRmlsdGVyIG91dCB0aGUgdXRpbCBtb2R1bGUsIGl0J3MgaW5zcGVjdCBmdW5jdGlvbiBpcyBzcGVjaWFsXG4gICAgICB2YWx1ZS5pbnNwZWN0ICE9PSBleHBvcnRzLmluc3BlY3QgJiZcbiAgICAgIC8vIEFsc28gZmlsdGVyIG91dCBhbnkgcHJvdG90eXBlIG9iamVjdHMgdXNpbmcgdGhlIGNpcmN1bGFyIGNoZWNrLlxuICAgICAgISh2YWx1ZS5jb25zdHJ1Y3RvciAmJiB2YWx1ZS5jb25zdHJ1Y3Rvci5wcm90b3R5cGUgPT09IHZhbHVlKSkge1xuICAgIHZhciByZXQgPSB2YWx1ZS5pbnNwZWN0KHJlY3Vyc2VUaW1lcywgY3R4KTtcbiAgICBpZiAoIWlzU3RyaW5nKHJldCkpIHtcbiAgICAgIHJldCA9IGZvcm1hdFZhbHVlKGN0eCwgcmV0LCByZWN1cnNlVGltZXMpO1xuICAgIH1cbiAgICByZXR1cm4gcmV0O1xuICB9XG5cbiAgLy8gUHJpbWl0aXZlIHR5cGVzIGNhbm5vdCBoYXZlIHByb3BlcnRpZXNcbiAgdmFyIHByaW1pdGl2ZSA9IGZvcm1hdFByaW1pdGl2ZShjdHgsIHZhbHVlKTtcbiAgaWYgKHByaW1pdGl2ZSkge1xuICAgIHJldHVybiBwcmltaXRpdmU7XG4gIH1cblxuICAvLyBMb29rIHVwIHRoZSBrZXlzIG9mIHRoZSBvYmplY3QuXG4gIHZhciBrZXlzID0gT2JqZWN0LmtleXModmFsdWUpO1xuICB2YXIgdmlzaWJsZUtleXMgPSBhcnJheVRvSGFzaChrZXlzKTtcblxuICBpZiAoY3R4LnNob3dIaWRkZW4pIHtcbiAgICBrZXlzID0gT2JqZWN0LmdldE93blByb3BlcnR5TmFtZXModmFsdWUpO1xuICB9XG5cbiAgLy8gSUUgZG9lc24ndCBtYWtlIGVycm9yIGZpZWxkcyBub24tZW51bWVyYWJsZVxuICAvLyBodHRwOi8vbXNkbi5taWNyb3NvZnQuY29tL2VuLXVzL2xpYnJhcnkvaWUvZHd3NTJzYnQodj12cy45NCkuYXNweFxuICBpZiAoaXNFcnJvcih2YWx1ZSlcbiAgICAgICYmIChrZXlzLmluZGV4T2YoJ21lc3NhZ2UnKSA+PSAwIHx8IGtleXMuaW5kZXhPZignZGVzY3JpcHRpb24nKSA+PSAwKSkge1xuICAgIHJldHVybiBmb3JtYXRFcnJvcih2YWx1ZSk7XG4gIH1cblxuICAvLyBTb21lIHR5cGUgb2Ygb2JqZWN0IHdpdGhvdXQgcHJvcGVydGllcyBjYW4gYmUgc2hvcnRjdXR0ZWQuXG4gIGlmIChrZXlzLmxlbmd0aCA9PT0gMCkge1xuICAgIGlmIChpc0Z1bmN0aW9uKHZhbHVlKSkge1xuICAgICAgdmFyIG5hbWUgPSB2YWx1ZS5uYW1lID8gJzogJyArIHZhbHVlLm5hbWUgOiAnJztcbiAgICAgIHJldHVybiBjdHguc3R5bGl6ZSgnW0Z1bmN0aW9uJyArIG5hbWUgKyAnXScsICdzcGVjaWFsJyk7XG4gICAgfVxuICAgIGlmIChpc1JlZ0V4cCh2YWx1ZSkpIHtcbiAgICAgIHJldHVybiBjdHguc3R5bGl6ZShSZWdFeHAucHJvdG90eXBlLnRvU3RyaW5nLmNhbGwodmFsdWUpLCAncmVnZXhwJyk7XG4gICAgfVxuICAgIGlmIChpc0RhdGUodmFsdWUpKSB7XG4gICAgICByZXR1cm4gY3R4LnN0eWxpemUoRGF0ZS5wcm90b3R5cGUudG9TdHJpbmcuY2FsbCh2YWx1ZSksICdkYXRlJyk7XG4gICAgfVxuICAgIGlmIChpc0Vycm9yKHZhbHVlKSkge1xuICAgICAgcmV0dXJuIGZvcm1hdEVycm9yKHZhbHVlKTtcbiAgICB9XG4gIH1cblxuICB2YXIgYmFzZSA9ICcnLCBhcnJheSA9IGZhbHNlLCBicmFjZXMgPSBbJ3snLCAnfSddO1xuXG4gIC8vIE1ha2UgQXJyYXkgc2F5IHRoYXQgdGhleSBhcmUgQXJyYXlcbiAgaWYgKGlzQXJyYXkodmFsdWUpKSB7XG4gICAgYXJyYXkgPSB0cnVlO1xuICAgIGJyYWNlcyA9IFsnWycsICddJ107XG4gIH1cblxuICAvLyBNYWtlIGZ1bmN0aW9ucyBzYXkgdGhhdCB0aGV5IGFyZSBmdW5jdGlvbnNcbiAgaWYgKGlzRnVuY3Rpb24odmFsdWUpKSB7XG4gICAgdmFyIG4gPSB2YWx1ZS5uYW1lID8gJzogJyArIHZhbHVlLm5hbWUgOiAnJztcbiAgICBiYXNlID0gJyBbRnVuY3Rpb24nICsgbiArICddJztcbiAgfVxuXG4gIC8vIE1ha2UgUmVnRXhwcyBzYXkgdGhhdCB0aGV5IGFyZSBSZWdFeHBzXG4gIGlmIChpc1JlZ0V4cCh2YWx1ZSkpIHtcbiAgICBiYXNlID0gJyAnICsgUmVnRXhwLnByb3RvdHlwZS50b1N0cmluZy5jYWxsKHZhbHVlKTtcbiAgfVxuXG4gIC8vIE1ha2UgZGF0ZXMgd2l0aCBwcm9wZXJ0aWVzIGZpcnN0IHNheSB0aGUgZGF0ZVxuICBpZiAoaXNEYXRlKHZhbHVlKSkge1xuICAgIGJhc2UgPSAnICcgKyBEYXRlLnByb3RvdHlwZS50b1VUQ1N0cmluZy5jYWxsKHZhbHVlKTtcbiAgfVxuXG4gIC8vIE1ha2UgZXJyb3Igd2l0aCBtZXNzYWdlIGZpcnN0IHNheSB0aGUgZXJyb3JcbiAgaWYgKGlzRXJyb3IodmFsdWUpKSB7XG4gICAgYmFzZSA9ICcgJyArIGZvcm1hdEVycm9yKHZhbHVlKTtcbiAgfVxuXG4gIGlmIChrZXlzLmxlbmd0aCA9PT0gMCAmJiAoIWFycmF5IHx8IHZhbHVlLmxlbmd0aCA9PSAwKSkge1xuICAgIHJldHVybiBicmFjZXNbMF0gKyBiYXNlICsgYnJhY2VzWzFdO1xuICB9XG5cbiAgaWYgKHJlY3Vyc2VUaW1lcyA8IDApIHtcbiAgICBpZiAoaXNSZWdFeHAodmFsdWUpKSB7XG4gICAgICByZXR1cm4gY3R4LnN0eWxpemUoUmVnRXhwLnByb3RvdHlwZS50b1N0cmluZy5jYWxsKHZhbHVlKSwgJ3JlZ2V4cCcpO1xuICAgIH0gZWxzZSB7XG4gICAgICByZXR1cm4gY3R4LnN0eWxpemUoJ1tPYmplY3RdJywgJ3NwZWNpYWwnKTtcbiAgICB9XG4gIH1cblxuICBjdHguc2Vlbi5wdXNoKHZhbHVlKTtcblxuICB2YXIgb3V0cHV0O1xuICBpZiAoYXJyYXkpIHtcbiAgICBvdXRwdXQgPSBmb3JtYXRBcnJheShjdHgsIHZhbHVlLCByZWN1cnNlVGltZXMsIHZpc2libGVLZXlzLCBrZXlzKTtcbiAgfSBlbHNlIHtcbiAgICBvdXRwdXQgPSBrZXlzLm1hcChmdW5jdGlvbihrZXkpIHtcbiAgICAgIHJldHVybiBmb3JtYXRQcm9wZXJ0eShjdHgsIHZhbHVlLCByZWN1cnNlVGltZXMsIHZpc2libGVLZXlzLCBrZXksIGFycmF5KTtcbiAgICB9KTtcbiAgfVxuXG4gIGN0eC5zZWVuLnBvcCgpO1xuXG4gIHJldHVybiByZWR1Y2VUb1NpbmdsZVN0cmluZyhvdXRwdXQsIGJhc2UsIGJyYWNlcyk7XG59XG5cblxuZnVuY3Rpb24gZm9ybWF0UHJpbWl0aXZlKGN0eCwgdmFsdWUpIHtcbiAgaWYgKGlzVW5kZWZpbmVkKHZhbHVlKSlcbiAgICByZXR1cm4gY3R4LnN0eWxpemUoJ3VuZGVmaW5lZCcsICd1bmRlZmluZWQnKTtcbiAgaWYgKGlzU3RyaW5nKHZhbHVlKSkge1xuICAgIHZhciBzaW1wbGUgPSAnXFwnJyArIEpTT04uc3RyaW5naWZ5KHZhbHVlKS5yZXBsYWNlKC9eXCJ8XCIkL2csICcnKVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgLnJlcGxhY2UoLycvZywgXCJcXFxcJ1wiKVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgLnJlcGxhY2UoL1xcXFxcIi9nLCAnXCInKSArICdcXCcnO1xuICAgIHJldHVybiBjdHguc3R5bGl6ZShzaW1wbGUsICdzdHJpbmcnKTtcbiAgfVxuICBpZiAoaXNOdW1iZXIodmFsdWUpKVxuICAgIHJldHVybiBjdHguc3R5bGl6ZSgnJyArIHZhbHVlLCAnbnVtYmVyJyk7XG4gIGlmIChpc0Jvb2xlYW4odmFsdWUpKVxuICAgIHJldHVybiBjdHguc3R5bGl6ZSgnJyArIHZhbHVlLCAnYm9vbGVhbicpO1xuICAvLyBGb3Igc29tZSByZWFzb24gdHlwZW9mIG51bGwgaXMgXCJvYmplY3RcIiwgc28gc3BlY2lhbCBjYXNlIGhlcmUuXG4gIGlmIChpc051bGwodmFsdWUpKVxuICAgIHJldHVybiBjdHguc3R5bGl6ZSgnbnVsbCcsICdudWxsJyk7XG59XG5cblxuZnVuY3Rpb24gZm9ybWF0RXJyb3IodmFsdWUpIHtcbiAgcmV0dXJuICdbJyArIEVycm9yLnByb3RvdHlwZS50b1N0cmluZy5jYWxsKHZhbHVlKSArICddJztcbn1cblxuXG5mdW5jdGlvbiBmb3JtYXRBcnJheShjdHgsIHZhbHVlLCByZWN1cnNlVGltZXMsIHZpc2libGVLZXlzLCBrZXlzKSB7XG4gIHZhciBvdXRwdXQgPSBbXTtcbiAgZm9yICh2YXIgaSA9IDAsIGwgPSB2YWx1ZS5sZW5ndGg7IGkgPCBsOyArK2kpIHtcbiAgICBpZiAoaGFzT3duUHJvcGVydHkodmFsdWUsIFN0cmluZyhpKSkpIHtcbiAgICAgIG91dHB1dC5wdXNoKGZvcm1hdFByb3BlcnR5KGN0eCwgdmFsdWUsIHJlY3Vyc2VUaW1lcywgdmlzaWJsZUtleXMsXG4gICAgICAgICAgU3RyaW5nKGkpLCB0cnVlKSk7XG4gICAgfSBlbHNlIHtcbiAgICAgIG91dHB1dC5wdXNoKCcnKTtcbiAgICB9XG4gIH1cbiAga2V5cy5mb3JFYWNoKGZ1bmN0aW9uKGtleSkge1xuICAgIGlmICgha2V5Lm1hdGNoKC9eXFxkKyQvKSkge1xuICAgICAgb3V0cHV0LnB1c2goZm9ybWF0UHJvcGVydHkoY3R4LCB2YWx1ZSwgcmVjdXJzZVRpbWVzLCB2aXNpYmxlS2V5cyxcbiAgICAgICAgICBrZXksIHRydWUpKTtcbiAgICB9XG4gIH0pO1xuICByZXR1cm4gb3V0cHV0O1xufVxuXG5cbmZ1bmN0aW9uIGZvcm1hdFByb3BlcnR5KGN0eCwgdmFsdWUsIHJlY3Vyc2VUaW1lcywgdmlzaWJsZUtleXMsIGtleSwgYXJyYXkpIHtcbiAgdmFyIG5hbWUsIHN0ciwgZGVzYztcbiAgZGVzYyA9IE9iamVjdC5nZXRPd25Qcm9wZXJ0eURlc2NyaXB0b3IodmFsdWUsIGtleSkgfHwgeyB2YWx1ZTogdmFsdWVba2V5XSB9O1xuICBpZiAoZGVzYy5nZXQpIHtcbiAgICBpZiAoZGVzYy5zZXQpIHtcbiAgICAgIHN0ciA9IGN0eC5zdHlsaXplKCdbR2V0dGVyL1NldHRlcl0nLCAnc3BlY2lhbCcpO1xuICAgIH0gZWxzZSB7XG4gICAgICBzdHIgPSBjdHguc3R5bGl6ZSgnW0dldHRlcl0nLCAnc3BlY2lhbCcpO1xuICAgIH1cbiAgfSBlbHNlIHtcbiAgICBpZiAoZGVzYy5zZXQpIHtcbiAgICAgIHN0ciA9IGN0eC5zdHlsaXplKCdbU2V0dGVyXScsICdzcGVjaWFsJyk7XG4gICAgfVxuICB9XG4gIGlmICghaGFzT3duUHJvcGVydHkodmlzaWJsZUtleXMsIGtleSkpIHtcbiAgICBuYW1lID0gJ1snICsga2V5ICsgJ10nO1xuICB9XG4gIGlmICghc3RyKSB7XG4gICAgaWYgKGN0eC5zZWVuLmluZGV4T2YoZGVzYy52YWx1ZSkgPCAwKSB7XG4gICAgICBpZiAoaXNOdWxsKHJlY3Vyc2VUaW1lcykpIHtcbiAgICAgICAgc3RyID0gZm9ybWF0VmFsdWUoY3R4LCBkZXNjLnZhbHVlLCBudWxsKTtcbiAgICAgIH0gZWxzZSB7XG4gICAgICAgIHN0ciA9IGZvcm1hdFZhbHVlKGN0eCwgZGVzYy52YWx1ZSwgcmVjdXJzZVRpbWVzIC0gMSk7XG4gICAgICB9XG4gICAgICBpZiAoc3RyLmluZGV4T2YoJ1xcbicpID4gLTEpIHtcbiAgICAgICAgaWYgKGFycmF5KSB7XG4gICAgICAgICAgc3RyID0gc3RyLnNwbGl0KCdcXG4nKS5tYXAoZnVuY3Rpb24obGluZSkge1xuICAgICAgICAgICAgcmV0dXJuICcgICcgKyBsaW5lO1xuICAgICAgICAgIH0pLmpvaW4oJ1xcbicpLnN1YnN0cigyKTtcbiAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICBzdHIgPSAnXFxuJyArIHN0ci5zcGxpdCgnXFxuJykubWFwKGZ1bmN0aW9uKGxpbmUpIHtcbiAgICAgICAgICAgIHJldHVybiAnICAgJyArIGxpbmU7XG4gICAgICAgICAgfSkuam9pbignXFxuJyk7XG4gICAgICAgIH1cbiAgICAgIH1cbiAgICB9IGVsc2Uge1xuICAgICAgc3RyID0gY3R4LnN0eWxpemUoJ1tDaXJjdWxhcl0nLCAnc3BlY2lhbCcpO1xuICAgIH1cbiAgfVxuICBpZiAoaXNVbmRlZmluZWQobmFtZSkpIHtcbiAgICBpZiAoYXJyYXkgJiYga2V5Lm1hdGNoKC9eXFxkKyQvKSkge1xuICAgICAgcmV0dXJuIHN0cjtcbiAgICB9XG4gICAgbmFtZSA9IEpTT04uc3RyaW5naWZ5KCcnICsga2V5KTtcbiAgICBpZiAobmFtZS5tYXRjaCgvXlwiKFthLXpBLVpfXVthLXpBLVpfMC05XSopXCIkLykpIHtcbiAgICAgIG5hbWUgPSBuYW1lLnN1YnN0cigxLCBuYW1lLmxlbmd0aCAtIDIpO1xuICAgICAgbmFtZSA9IGN0eC5zdHlsaXplKG5hbWUsICduYW1lJyk7XG4gICAgfSBlbHNlIHtcbiAgICAgIG5hbWUgPSBuYW1lLnJlcGxhY2UoLycvZywgXCJcXFxcJ1wiKVxuICAgICAgICAgICAgICAgICAucmVwbGFjZSgvXFxcXFwiL2csICdcIicpXG4gICAgICAgICAgICAgICAgIC5yZXBsYWNlKC8oXlwifFwiJCkvZywgXCInXCIpO1xuICAgICAgbmFtZSA9IGN0eC5zdHlsaXplKG5hbWUsICdzdHJpbmcnKTtcbiAgICB9XG4gIH1cblxuICByZXR1cm4gbmFtZSArICc6ICcgKyBzdHI7XG59XG5cblxuZnVuY3Rpb24gcmVkdWNlVG9TaW5nbGVTdHJpbmcob3V0cHV0LCBiYXNlLCBicmFjZXMpIHtcbiAgdmFyIG51bUxpbmVzRXN0ID0gMDtcbiAgdmFyIGxlbmd0aCA9IG91dHB1dC5yZWR1Y2UoZnVuY3Rpb24ocHJldiwgY3VyKSB7XG4gICAgbnVtTGluZXNFc3QrKztcbiAgICBpZiAoY3VyLmluZGV4T2YoJ1xcbicpID49IDApIG51bUxpbmVzRXN0Kys7XG4gICAgcmV0dXJuIHByZXYgKyBjdXIucmVwbGFjZSgvXFx1MDAxYlxcW1xcZFxcZD9tL2csICcnKS5sZW5ndGggKyAxO1xuICB9LCAwKTtcblxuICBpZiAobGVuZ3RoID4gNjApIHtcbiAgICByZXR1cm4gYnJhY2VzWzBdICtcbiAgICAgICAgICAgKGJhc2UgPT09ICcnID8gJycgOiBiYXNlICsgJ1xcbiAnKSArXG4gICAgICAgICAgICcgJyArXG4gICAgICAgICAgIG91dHB1dC5qb2luKCcsXFxuICAnKSArXG4gICAgICAgICAgICcgJyArXG4gICAgICAgICAgIGJyYWNlc1sxXTtcbiAgfVxuXG4gIHJldHVybiBicmFjZXNbMF0gKyBiYXNlICsgJyAnICsgb3V0cHV0LmpvaW4oJywgJykgKyAnICcgKyBicmFjZXNbMV07XG59XG5cblxuLy8gTk9URTogVGhlc2UgdHlwZSBjaGVja2luZyBmdW5jdGlvbnMgaW50ZW50aW9uYWxseSBkb24ndCB1c2UgYGluc3RhbmNlb2ZgXG4vLyBiZWNhdXNlIGl0IGlzIGZyYWdpbGUgYW5kIGNhbiBiZSBlYXNpbHkgZmFrZWQgd2l0aCBgT2JqZWN0LmNyZWF0ZSgpYC5cbmZ1bmN0aW9uIGlzQXJyYXkoYXIpIHtcbiAgcmV0dXJuIEFycmF5LmlzQXJyYXkoYXIpO1xufVxuZXhwb3J0cy5pc0FycmF5ID0gaXNBcnJheTtcblxuZnVuY3Rpb24gaXNCb29sZWFuKGFyZykge1xuICByZXR1cm4gdHlwZW9mIGFyZyA9PT0gJ2Jvb2xlYW4nO1xufVxuZXhwb3J0cy5pc0Jvb2xlYW4gPSBpc0Jvb2xlYW47XG5cbmZ1bmN0aW9uIGlzTnVsbChhcmcpIHtcbiAgcmV0dXJuIGFyZyA9PT0gbnVsbDtcbn1cbmV4cG9ydHMuaXNOdWxsID0gaXNOdWxsO1xuXG5mdW5jdGlvbiBpc051bGxPclVuZGVmaW5lZChhcmcpIHtcbiAgcmV0dXJuIGFyZyA9PSBudWxsO1xufVxuZXhwb3J0cy5pc051bGxPclVuZGVmaW5lZCA9IGlzTnVsbE9yVW5kZWZpbmVkO1xuXG5mdW5jdGlvbiBpc051bWJlcihhcmcpIHtcbiAgcmV0dXJuIHR5cGVvZiBhcmcgPT09ICdudW1iZXInO1xufVxuZXhwb3J0cy5pc051bWJlciA9IGlzTnVtYmVyO1xuXG5mdW5jdGlvbiBpc1N0cmluZyhhcmcpIHtcbiAgcmV0dXJuIHR5cGVvZiBhcmcgPT09ICdzdHJpbmcnO1xufVxuZXhwb3J0cy5pc1N0cmluZyA9IGlzU3RyaW5nO1xuXG5mdW5jdGlvbiBpc1N5bWJvbChhcmcpIHtcbiAgcmV0dXJuIHR5cGVvZiBhcmcgPT09ICdzeW1ib2wnO1xufVxuZXhwb3J0cy5pc1N5bWJvbCA9IGlzU3ltYm9sO1xuXG5mdW5jdGlvbiBpc1VuZGVmaW5lZChhcmcpIHtcbiAgcmV0dXJuIGFyZyA9PT0gdm9pZCAwO1xufVxuZXhwb3J0cy5pc1VuZGVmaW5lZCA9IGlzVW5kZWZpbmVkO1xuXG5mdW5jdGlvbiBpc1JlZ0V4cChyZSkge1xuICByZXR1cm4gaXNPYmplY3QocmUpICYmIG9iamVjdFRvU3RyaW5nKHJlKSA9PT0gJ1tvYmplY3QgUmVnRXhwXSc7XG59XG5leHBvcnRzLmlzUmVnRXhwID0gaXNSZWdFeHA7XG5cbmZ1bmN0aW9uIGlzT2JqZWN0KGFyZykge1xuICByZXR1cm4gdHlwZW9mIGFyZyA9PT0gJ29iamVjdCcgJiYgYXJnICE9PSBudWxsO1xufVxuZXhwb3J0cy5pc09iamVjdCA9IGlzT2JqZWN0O1xuXG5mdW5jdGlvbiBpc0RhdGUoZCkge1xuICByZXR1cm4gaXNPYmplY3QoZCkgJiYgb2JqZWN0VG9TdHJpbmcoZCkgPT09ICdbb2JqZWN0IERhdGVdJztcbn1cbmV4cG9ydHMuaXNEYXRlID0gaXNEYXRlO1xuXG5mdW5jdGlvbiBpc0Vycm9yKGUpIHtcbiAgcmV0dXJuIGlzT2JqZWN0KGUpICYmXG4gICAgICAob2JqZWN0VG9TdHJpbmcoZSkgPT09ICdbb2JqZWN0IEVycm9yXScgfHwgZSBpbnN0YW5jZW9mIEVycm9yKTtcbn1cbmV4cG9ydHMuaXNFcnJvciA9IGlzRXJyb3I7XG5cbmZ1bmN0aW9uIGlzRnVuY3Rpb24oYXJnKSB7XG4gIHJldHVybiB0eXBlb2YgYXJnID09PSAnZnVuY3Rpb24nO1xufVxuZXhwb3J0cy5pc0Z1bmN0aW9uID0gaXNGdW5jdGlvbjtcblxuZnVuY3Rpb24gaXNQcmltaXRpdmUoYXJnKSB7XG4gIHJldHVybiBhcmcgPT09IG51bGwgfHxcbiAgICAgICAgIHR5cGVvZiBhcmcgPT09ICdib29sZWFuJyB8fFxuICAgICAgICAgdHlwZW9mIGFyZyA9PT0gJ251bWJlcicgfHxcbiAgICAgICAgIHR5cGVvZiBhcmcgPT09ICdzdHJpbmcnIHx8XG4gICAgICAgICB0eXBlb2YgYXJnID09PSAnc3ltYm9sJyB8fCAgLy8gRVM2IHN5bWJvbFxuICAgICAgICAgdHlwZW9mIGFyZyA9PT0gJ3VuZGVmaW5lZCc7XG59XG5leHBvcnRzLmlzUHJpbWl0aXZlID0gaXNQcmltaXRpdmU7XG5cbmV4cG9ydHMuaXNCdWZmZXIgPSByZXF1aXJlKCcuL3N1cHBvcnQvaXNCdWZmZXInKTtcblxuZnVuY3Rpb24gb2JqZWN0VG9TdHJpbmcobykge1xuICByZXR1cm4gT2JqZWN0LnByb3RvdHlwZS50b1N0cmluZy5jYWxsKG8pO1xufVxuXG5cbmZ1bmN0aW9uIHBhZChuKSB7XG4gIHJldHVybiBuIDwgMTAgPyAnMCcgKyBuLnRvU3RyaW5nKDEwKSA6IG4udG9TdHJpbmcoMTApO1xufVxuXG5cbnZhciBtb250aHMgPSBbJ0phbicsICdGZWInLCAnTWFyJywgJ0FwcicsICdNYXknLCAnSnVuJywgJ0p1bCcsICdBdWcnLCAnU2VwJyxcbiAgICAgICAgICAgICAgJ09jdCcsICdOb3YnLCAnRGVjJ107XG5cbi8vIDI2IEZlYiAxNjoxOTozNFxuZnVuY3Rpb24gdGltZXN0YW1wKCkge1xuICB2YXIgZCA9IG5ldyBEYXRlKCk7XG4gIHZhciB0aW1lID0gW3BhZChkLmdldEhvdXJzKCkpLFxuICAgICAgICAgICAgICBwYWQoZC5nZXRNaW51dGVzKCkpLFxuICAgICAgICAgICAgICBwYWQoZC5nZXRTZWNvbmRzKCkpXS5qb2luKCc6Jyk7XG4gIHJldHVybiBbZC5nZXREYXRlKCksIG1vbnRoc1tkLmdldE1vbnRoKCldLCB0aW1lXS5qb2luKCcgJyk7XG59XG5cblxuLy8gbG9nIGlzIGp1c3QgYSB0aGluIHdyYXBwZXIgdG8gY29uc29sZS5sb2cgdGhhdCBwcmVwZW5kcyBhIHRpbWVzdGFtcFxuZXhwb3J0cy5sb2cgPSBmdW5jdGlvbigpIHtcbiAgY29uc29sZS5sb2coJyVzIC0gJXMnLCB0aW1lc3RhbXAoKSwgZXhwb3J0cy5mb3JtYXQuYXBwbHkoZXhwb3J0cywgYXJndW1lbnRzKSk7XG59O1xuXG5cbi8qKlxuICogSW5oZXJpdCB0aGUgcHJvdG90eXBlIG1ldGhvZHMgZnJvbSBvbmUgY29uc3RydWN0b3IgaW50byBhbm90aGVyLlxuICpcbiAqIFRoZSBGdW5jdGlvbi5wcm90b3R5cGUuaW5oZXJpdHMgZnJvbSBsYW5nLmpzIHJld3JpdHRlbiBhcyBhIHN0YW5kYWxvbmVcbiAqIGZ1bmN0aW9uIChub3Qgb24gRnVuY3Rpb24ucHJvdG90eXBlKS4gTk9URTogSWYgdGhpcyBmaWxlIGlzIHRvIGJlIGxvYWRlZFxuICogZHVyaW5nIGJvb3RzdHJhcHBpbmcgdGhpcyBmdW5jdGlvbiBuZWVkcyB0byBiZSByZXdyaXR0ZW4gdXNpbmcgc29tZSBuYXRpdmVcbiAqIGZ1bmN0aW9ucyBhcyBwcm90b3R5cGUgc2V0dXAgdXNpbmcgbm9ybWFsIEphdmFTY3JpcHQgZG9lcyBub3Qgd29yayBhc1xuICogZXhwZWN0ZWQgZHVyaW5nIGJvb3RzdHJhcHBpbmcgKHNlZSBtaXJyb3IuanMgaW4gcjExNDkwMykuXG4gKlxuICogQHBhcmFtIHtmdW5jdGlvbn0gY3RvciBDb25zdHJ1Y3RvciBmdW5jdGlvbiB3aGljaCBuZWVkcyB0byBpbmhlcml0IHRoZVxuICogICAgIHByb3RvdHlwZS5cbiAqIEBwYXJhbSB7ZnVuY3Rpb259IHN1cGVyQ3RvciBDb25zdHJ1Y3RvciBmdW5jdGlvbiB0byBpbmhlcml0IHByb3RvdHlwZSBmcm9tLlxuICovXG5leHBvcnRzLmluaGVyaXRzID0gcmVxdWlyZSgnaW5oZXJpdHMnKTtcblxuZXhwb3J0cy5fZXh0ZW5kID0gZnVuY3Rpb24ob3JpZ2luLCBhZGQpIHtcbiAgLy8gRG9uJ3QgZG8gYW55dGhpbmcgaWYgYWRkIGlzbid0IGFuIG9iamVjdFxuICBpZiAoIWFkZCB8fCAhaXNPYmplY3QoYWRkKSkgcmV0dXJuIG9yaWdpbjtcblxuICB2YXIga2V5cyA9IE9iamVjdC5rZXlzKGFkZCk7XG4gIHZhciBpID0ga2V5cy5sZW5ndGg7XG4gIHdoaWxlIChpLS0pIHtcbiAgICBvcmlnaW5ba2V5c1tpXV0gPSBhZGRba2V5c1tpXV07XG4gIH1cbiAgcmV0dXJuIG9yaWdpbjtcbn07XG5cbmZ1bmN0aW9uIGhhc093blByb3BlcnR5KG9iaiwgcHJvcCkge1xuICByZXR1cm4gT2JqZWN0LnByb3RvdHlwZS5oYXNPd25Qcm9wZXJ0eS5jYWxsKG9iaiwgcHJvcCk7XG59XG4iXX0=
