(function(f){if(typeof exports==="object"&&typeof module!=="undefined"){module.exports=f()}else if(typeof define==="function"&&define.amd){define([],f)}else{var g;if(typeof window!=="undefined"){g=window}else if(typeof global!=="undefined"){g=global}else if(typeof self!=="undefined"){g=self}else{g=this}g.YAtern = f()}})(function(){var define,module,exports;return (function e(t,n,r){function s(o,u){if(!n[o]){if(!t[o]){var a=typeof require=="function"&&require;if(!u&&a)return a(o,!0);if(i)return i(o,!0);var f=new Error("Cannot find module '"+o+"'");throw f.code="MODULE_NOT_FOUND",f}var l=n[o]={exports:{}};t[o][0].call(l.exports,function(e){var n=t[o][1][e];return s(n?n:e)},l,l.exports,e,t,n,r)}return n[o].exports}var i=typeof require=="function"&&require;for(var o=0;o<r.length;o++)s(r[o]);return s})({1:[function(require,module,exports){
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

},{"util":16}],2:[function(require,module,exports){
'use strict';

var types = require('../domains/types');
var walk = require('acorn/dist/walk');
var status = require('../domains/status');
var cstr = require('./constraints');

// arguments are " oldStatus (, name, val)* "
function changedStatus(oldStatus) {
    var newStatus = new status.Status();
    for (var i = 1; i < arguments.length; i = i + 2) {
        newStatus[arguments[i]] = arguments[i + 1];
    }for (var p in oldStatus) {
        if (newStatus[p] === undefined) newStatus[p] = oldStatus[p];
    }
    return newStatus;
}

// returns [access type, prop value]
function propAccess(node) {
    var prop = node.property;
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

function readMember(node, curStatus, c) {
    var ret = new types.AVal();
    var objAVal = c(node.object, curStatus, undefined);
    if (node.property.type !== 'Identifier') {
        // return from property is ignored
        c(node.property, curStatus, undefined);
    }
    var propAcc = propAccess(node);

    constraints.push({ OBJ: objAVal,
        PROP: propAcc[1],
        READ_TO: ret });
    objAVal.propagate(new cstr.ReadProp(propAcc[1], ret));

    // returns AVal for receiver and read member
    return [objAVal, ret];
}
// To prevent recursion,
// we remember the status used in addConstraints
var visitedStatus = [];
var constraints = [];
function clearConstraints() {
    visitedStatus.length = 0;
    constraints.length = 0;
}

var rtCX = undefined;
function addConstraints(ast, initStatus, newRtCX) {

    // set rtCX
    rtCX = newRtCX || rtCX;

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

    // constraint generating walker for expressions
    var constraintGenerator = walk.make({

        Identifier: function Identifier(node, curStatus, c) {
            return curStatus.sc.getAValOf(node.name);
        },

        ThisExpression: function ThisExpression(node, curStatus, c) {
            return curStatus.self;
        },

        Literal: function Literal(node, curStatus, c) {
            var res = new types.AVal();
            if (node.regex) {
                // not implemented yet
                // throw new Error('regex literal is not implemented yet');
                return res;
            }
            switch (typeof node.value) {
                case 'number':
                    constraints.push({ TYPE: types.PrimNumber,
                        INCL_SET: res });
                    res.addType(types.PrimNumber);
                    break;
                case 'string':
                    constraints.push({ TYPE: types.PrimString,
                        INCL_SET: res });
                    res.addType(types.PrimString);
                    break;
                case 'boolean':
                    constraints.push({ TYPE: types.PrimBoolean,
                        INCL_SET: res });
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
            if (node.left.type !== 'MemberExpression') {
                // LHS is a simple variable.
                var varName = node.left.name;
                var lhsAVal = curStatus.sc.getAValOf(varName);

                if (node.operator === '=') {
                    // simple assignment
                    constraints.push({
                        FROM: rhsAVal,
                        TO: lhsAVal
                    });
                    rhsAVal.propagate(lhsAVal);
                    // corresponding AVal is the RHS
                    return rhsAVal;
                }
                var resAVal = new types.AVal();
                if (node.operator === '+=') {
                    // concatenating update
                    constraints.push({
                        ADD_OPRD1: lhsAVal,
                        ADD_OPRD2: rhsAVal,
                        RESULT: resAVal
                    });
                    lhsAVal.propagate(new cstr.IsAdded(rhsAVal, resAVal));
                    rhsAVal.propagate(new cstr.IsAdded(lhsAVal, resAVal));
                } else {
                    // arithmetic update
                    constraints.push({
                        TYPE: types.PrimNumber,
                        INCL_SET: resAVal
                    });
                    resAVal.addType(types.PrimNumber);
                }
                return resAVal;
            } else {
                // member assignment
                var objAVal = c(node.left.object, curStatus, undefined);
                var propAcc = propAccess(node.left);
                if (node.operator === '=') {
                    // assignment to member
                    constraints.push({
                        OBJ: objAVal,
                        PROP: propAcc[1],
                        WRITE_WITH: rhsAVal
                    });
                    objAVal.propagate(new cstr.WriteProp(propAcc[1], rhsAVal));
                    // if property is number literal, also write to 'unknown'
                    if (propAcc[0] === 'numberLiteral') {
                        objAVal.propagate(new cstr.WriteProp(null, rhsAVal));
                    }
                    return rhsAVal;
                }
                var resAVal = new types.AVal();
                var recvAndRet = readMember(node.left, curStatus, c);
                if (node.operator === '+=') {
                    // concatenating update
                    constraints.push({
                        ADD_OPRD1: recvAndRet[1],
                        ADD_OPRD2: rhsAVal,
                        RESULT: resAVal
                    });
                    recvAndRet[1].propagate(new cstr.IsAdded(rhsAVal, resAVal));
                    rhsAVal.propagate(new cstr.IsAdded(recvAndRet[1], resAVal));
                } else {
                    // arithmetic update
                    constraints.push({
                        TYPE: types.PrimNumber,
                        INCL_SET: resAVal
                    });
                    resAVal.addType(types.PrimNumber);
                }
                return resAVal;
            }
        },

        VariableDeclaration: function VariableDeclaration(node, curStatus, c) {
            for (var i = 0; i < node.declarations.length; i++) {
                var decl = node.declarations[i];
                if (decl.init) {
                    var lhsAVal = curStatus.sc.getAValOf(decl.id.name);
                    var rhsAVal = c(decl.init, curStatus, undefined);
                    constraints.push({ FROM: rhsAVal,
                        TO: lhsAVal });
                    rhsAVal.propagate(lhsAVal);
                }
            }
        },

        LogicalExpression: function LogicalExpression(node, curStatus, c) {
            var res = new types.AVal();
            var left = c(node.left, curStatus, undefined);
            var right = c(node.right, curStatus, undefined);
            constraints.push({ FROM: left, TO: res }, { FROM: right, TO: res });
            left.propagate(res);
            right.propagate(res);
            return res;
        },

        ConditionalExpression: function ConditionalExpression(node, curStatus, c) {
            var res = new types.AVal();
            c(node.test, curStatus, undefined);
            var cons = c(node.consequent, curStatus, undefined);
            var alt = c(node.alternate, curStatus, undefined);
            constraints.push({ FROM: cons, TO: res }, { FROM: alt, TO: res });
            cons.propagate(res);
            alt.propagate(res);
            return res;
        },

        NewExpression: function NewExpression(node, curStatus, c) {
            var ret = new types.AVal();
            var callee = c(node.callee, curStatus, undefined);
            var args = [];
            for (var i = 0; i < node.arguments.length; i++) {
                args.push(c(node.arguments[i], curStatus, undefined));
            }
            var newDelta = curStatus.delta.appendOne(node['@label']);
            constraints.push({ CONSTRUCTOR: callee,
                ARGS: args,
                RET: ret,
                EXC: curStatus.exc,
                DELTA: newDelta });
            callee.propagate(new cstr.IsCtor(args, ret, curStatus.exc, newDelta));
            return ret;
        },

        ArrayExpression: function ArrayExpression(node, curStatus, c) {
            var ret = new types.AVal();
            var arrType = new types.ArrType(new types.AVal(rtCX.protos.Array));
            // add length property
            arrType.getProp('length').addType(types.PrimNumber);

            constraints.push({ TYPE: arrType, INCL_SET: ret });
            ret.addType(arrType);

            // add array elements
            for (var i = 0; i < node.elements.length; i++) {
                var eltAVal = c(node.elements[i], curStatus, undefined);

                var prop = i + '';
                constraints.push({ OBJ: ret, PROP: prop, AVAL: eltAVal });
                constraints.push({ OBJ: ret, PROP: null, AVAL: eltAVal });
                ret.propagate(new cstr.WriteProp(prop, eltAVal));
                ret.propagate(new cstr.WriteProp(null, eltAVal));
            }
            return ret;
        },

        ObjectExpression: function ObjectExpression(node, curStatus, c) {
            var ret = new types.AVal();
            var objType = new types.ObjType(new types.AVal(rtCX.protos.Object));
            constraints.push({ TYPE: objType, INCL_SET: ret });
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
                constraints.push({ OBJ: ret, PROP: _name, AVAL: fldAVal });
                ret.propagate(new cstr.WriteProp(_name, fldAVal));
            }
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
                fnInstance = new types.FnType(new types.AVal(rtCX.protos.Function), '[anonymous function]', node.body['@block'].getParamVarNames(), curStatus.sc, node, rtCX.protos.Object);
                node.fnInstances.push(fnInstance);
                var prototypeObject = new types.ObjType(new types.AVal(rtCX.protos.Object), '?.prototype');
                // For .prototype
                var prototypeProp = fnInstance.getProp('prototype');
                constraints.push({ TYPE: prototypeObject,
                    INCL_SET: prototypeProp });
                prototypeProp.addType(prototypeObject);
                // For .prototype.constructor
                var constructorProp = prototypeObject.getProp('constructor');
                constraints.push({ TYPE: fnInstance,
                    INCL_SET: constructorProp });
                constructorProp.addType(fnInstance);
            }
            var ret = new types.AVal();
            constraints.push({ TYPE: fnInstance,
                INCL_SET: ret });
            ret.addType(fnInstance);
            return ret;
        },

        FunctionDeclaration: function FunctionDeclaration(node, curStatus, c) {
            // Drop initial catch scopes
            var sc0 = curStatus.sc.removeInitialCatchBlocks();
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
                fnInstance = new types.FnType(new types.AVal(rtCX.protos.Function), node.id.name, node.body['@block'].getParamVarNames(), sc0, node, rtCX.protos.Object);
                node.fnInstances.push(fnInstance);
                // for each fnInstance, assign one prototype object
                var prototypeObject = new types.ObjType(new types.AVal(rtCX.protos.Object), node.id.name + '.prototype');
                // For .prototype
                var prototypeProp = fnInstance.getProp('prototype');
                constraints.push({ TYPE: prototypeObject,
                    INCL_SET: prototypeProp });
                prototypeProp.addType(prototypeObject);
                // For .prototype.constructor
                var constructorProp = prototypeObject.getProp('constructor');
                constraints.push({ TYPE: fnInstance,
                    INCL_SET: constructorProp });
                constructorProp.addType(fnInstance);
            }
            var lhsAVal = sc0.getAValOf(node.id.name);

            constraints.push({ TYPE: fnInstance,
                INCL_SET: lhsAVal });
            lhsAVal.addType(fnInstance);
            // nothing to return
            return types.AValNull;
        },

        SequenceExpression: function SequenceExpression(node, curStatus, c) {
            var lastIndex = node.expressions.length - 1;
            for (var i = 0; i < lastIndex; i++) {
                c(node.expressions[i], curStatus, undefined);
            }
            return c(node.expressions[lastIndex], curStatus, undefined);
        },

        UnaryExpression: function UnaryExpression(node, curStatus, c) {
            c(node.argument, curStatus, undefined);
            var res = new types.AVal();
            var type = unopResultType(node.operator);
            if (type) {
                constraints.push({ TYPE: type,
                    INCL_SET: res });
                res.addType(type);
            }
            return res;
        },

        UpdateExpression: function UpdateExpression(node, curStatus, c) {
            c(node.argument, curStatus, undefined);
            var res = new types.AVal();
            constraints.push({ TYPE: types.PrimNumber,
                INCL_SET: res });
            res.addType(types.PrimNumber);
            // We ignore the effect of updating to number type
            return res;
        },

        BinaryExpression: function BinaryExpression(node, curStatus, c) {
            var lOprd = c(node.left, curStatus, undefined);
            var rOprd = c(node.right, curStatus, undefined);
            var res = new types.AVal();

            if (node.operator == '+') {
                constraints.push({ ADD_OPRD1: lOprd,
                    ADD_OPRD2: rOprd,
                    RESULT: res });
                lOprd.propagate(new cstr.IsAdded(rOprd, res));
                rOprd.propagate(new cstr.IsAdded(lOprd, res));
            } else {
                if (binopIsBoolean(node.operator)) {
                    constraints.push({ TYPE: types.PrimBoolean,
                        INCL_SET: res });
                    res.addType(types.PrimBoolean);
                } else {
                    constraints.push({ TYPE: types.PrimNumber,
                        INCL_SET: res });
                    res.addType(types.PrimNumber);
                }
            }
            return res;
        },

        TryStatement: function TryStatement(node, curStatus, c) {
            // construct scope chain for catch block
            var catchBlockSC = node.handler.body['@block'].getScopeInstance(curStatus.sc, curStatus.delta);
            // get the AVal for exception parameter
            var excAVal = catchBlockSC.getAValOf(node.handler.param.name);

            // for try block
            var tryStatus = changedStatus(curStatus, 'exc', excAVal);
            c(node.block, tryStatus, undefined);

            // for catch block
            var catchStatus = changedStatus(curStatus, 'sc', catchBlockSC);
            c(node.handler.body, catchStatus, undefined);

            // for finally block
            if (node.finalizer !== null) c(node.finalizer, curStatus, undefined);
        },

        ThrowStatement: function ThrowStatement(node, curStatus, c) {
            var thr = c(node.argument, curStatus, undefined);
            constraints.push({ FROM: thr,
                TO: curStatus.exc });
            thr.propagate(curStatus.exc);
        },

        CallExpression: function CallExpression(node, curStatus, c) {
            var resAVal = new types.AVal();
            var argAVals = [];

            // get AVals for each arguments
            for (var i = 0; i < node.arguments.length; i++) {
                argAVals.push(c(node.arguments[i], curStatus, undefined));
            }
            // append current call site to the context
            var newDelta = curStatus.delta.appendOne(node['@label']);

            if (node.callee.type === 'MemberExpression') {
                // method call
                // var recv = c(node.callee.object, curStatus, undefined);
                // var methodName = immedProp(node.callee);
                // constraints.push({
                //   RECV: recv,
                //   PROPNAME: methodName,
                //   PARAMS: argAVals,
                //   RET: resAVal,
                //   EXC: curStatus.exc,
                //   DELTA: newDelta
                // });
                var recvAndRet = readMember(node.callee, curStatus, c);
                recvAndRet[1].propagate(new cstr.IsCallee(recvAndRet[0], argAVals, resAVal, curStatus.exc, newDelta));
            } else {
                // normal function call
                var calleeAVal = c(node.callee, curStatus, undefined);
                // callee의 return을 call expression으로
                // callee의 exception을 호출 측의 exception에 전달해야
                constraints.push({
                    CALLEE: calleeAVal,
                    SELF: rtCX.globalObject,
                    PARAMS: argAVals,
                    RET: resAVal,
                    EXC: curStatus.exc,
                    DELTA: newDelta
                });
                calleeAVal.propagate(new cstr.IsCallee(new types.AVal(rtCX.globalObject), argAVals, resAVal, curStatus.exc, newDelta));
            }
            return resAVal;
        },

        MemberExpression: function MemberExpression(node, curStatus, c) {
            var recvAndRet = readMember(node, curStatus, c);
            return recvAndRet[1];
        },

        ReturnStatement: function ReturnStatement(node, curStatus, c) {
            if (!node.argument) return;
            var ret = c(node.argument, curStatus, undefined);
            constraints.push({ FROM: ret,
                TO: curStatus.ret });
            ret.propagate(curStatus.ret);
        }
    });

    recursiveWithReturn(ast, initStatus, constraintGenerator);

    // We actually added constraints
    return true;
}

function recursiveWithReturn(node, state, visitor) {
    function c(node, st, override) {
        return visitor[override || node.type](node, st, c);
    }
    return c(node, state);
}

exports.constraints = constraints;
exports.addConstraints = addConstraints;
exports.clearConstraints = clearConstraints;

},{"../domains/status":5,"../domains/types":6,"./constraints":3,"acorn/dist/walk":11}],3:[function(require,module,exports){
'use strict';

var types = require('../domains/types');
var status = require('../domains/status');
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
    var funEnv = f.getFunEnv(this.delta);
    var newSC = f.originNode.body['@block'].getScopeInstance(f.sc, this.delta);
    var funStatus = new status.Status(funEnv[0], funEnv[1], funEnv[2], this.delta, newSC);
    // pass this object
    this.self.propagate(funEnv[0]);

    var minLen = Math.min(this.args.length, f.paramNames.length);
    for (var i = 0; i < minLen; i++) {
        this.args[i].propagate(newSC.getAValOf(f.paramNames[i]));
    }

    // for arguments object
    if (f.originNode.body['@block'].useArgumentsObject) {
        var argObj = f.getArgumentsObject(this.delta);
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
    funEnv[1].propagate(this.ret);
    // get exception
    funEnv[2].propagate(this.exc);
};

function IsCtor(args, ret, exc, delta) {
    this.args = args;
    this.ret = ret;
    this.exc = exc;
    this.delta = delta;
}
IsCtor.prototype = Object.create(CSTR.prototype);
IsCtor.prototype.addType = function (f) {
    if (!(f instanceof types.FnType)) return;
    var funEnv = f.getFunEnv(this.delta);
    var newSC = f.originNode.body['@block'].getScopeInstance(f.sc, this.delta);
    var funStatus = new status.Status(funEnv[0], new IfObjType(funEnv[1]), funEnv[2], this.delta, newSC);
    // pass this object
    var newObj = f.getInstance();
    funEnv[0].addType(newObj);

    var minLen = Math.min(this.args.length, f.paramNames.length);
    for (var i = 0; i < minLen; i++) {
        this.args[i].propagate(newSC.getAValOf(f.paramNames[i]));
    }

    // for arguments object
    if (f.originNode.body['@block'].useArgumentsObject) {
        var argObj = f.getArgumentsObject(this.delta);
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

    // by explicit return, only ObjType are propagated
    funEnv[1].propagate(this.ret);
    // return new object
    this.ret.addType(newObj);
    // get exception
    funEnv[2].propagate(this.exc);
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

},{"../domains/status":5,"../domains/types":6,"./cGen":2}],4:[function(require,module,exports){
// Context for k-CFA analysis
//
// Assume a context is an array of numbers.
// A number in such list denotes a call site, that is @label of a CallExpression.
// We keep the most recent 'k' callsites.
// Equality on contexts should look into the numbers.

"use strict";

var callSiteContextParameter = {
    // maximum length of context
    maxDepthK: 0,
    // function list for sensitive analysis
    sensFuncs: {}
};

function CallSiteContext(csList) {
    if (csList) this.csList = csList;else this.csList = [];
}

CallSiteContext.prototype.equals = function (other) {
    if (this.csList.length != other.csList.length) return false;
    for (var i = 0; i < this.csList.length; i++) {
        if (this.csList[i] !== other.csList[i]) return false;
    }
    return true;
};

CallSiteContext.prototype.appendOne = function (callSite) {
    // use concat to create a new array
    // oldest one comes first
    var appended = this.csList.concat(callSite);
    if (appended.length > callSiteContextParameter.maxDepthK) {
        appended.shift();
    }
    return new CallSiteContext(appended);
};

CallSiteContext.prototype.toString = function () {
    return this.csList.toString();
};

exports.callSiteContextParameter = callSiteContextParameter;
exports.CallSiteContext = CallSiteContext;

},{}],5:[function(require,module,exports){
// Status:
// { self  : AVal,
//   ret   : AVal,
//   exc   : AVal,
//   delta : Context,
//   sc    : ScopeChain }

"use strict";

function Status(self, ret, exc, delta, sc) {
    this.self = self;
    this.ret = ret;
    this.exc = exc;
    this.delta = delta;
    this.sc = sc;
}

Status.prototype.equals = function (other) {
    return this.self === other.self && this.ret === other.ret && this.exc === other.exc && this.delta.equals(other.delta) && this.sc === other.sc;
};

exports.Status = Status;

},{}],6:[function(require,module,exports){
'use strict';

// for DEBUG
var count = 0;
/**
 * the abstract value for a concrete value
 * which is a set of types.
 * @constructor
 * @param {Type} type - give a type to make AVal with a single type
 */
function AVal(type) {
    // type: contained types
    // We assume types are distinguishable by '==='
    if (type) this.types = new Set([type]);else this.types = new Set();
    // forwards: propagation targets
    // We assume targets are distinguishable by 'equals' method
    this.forwards = new Set();
    // for DEBUG
    this._id = count++;
}
/** Check whether it has any type
 * @returns {boolean}
 */
AVal.prototype.isEmpty = function () {
    return this.types.size === 0;
};

/**
 * @returns {[Type]}
 */
AVal.prototype.getTypes = function () {
    return this.types;
};

/**
 * @returns {boolean}
 */
AVal.prototype.hasType = function (type) {
    return this.types.has(type);
};

/**
 * Add a type.
 * @param {Type} type
 */
AVal.prototype.addType = function (type) {
    if (this.types.has(type)) return;
    // given type is new
    this.types.add(type);
    // send to propagation targats
    this.forwards.forEach(function (fwd) {
        fwd.addType(type);
    });
};
/**
 * @param {AVal} target
 */
AVal.prototype.propagate = function (target) {
    if (!this.addForward(target)) return;
    // target is newly added
    // send types to the new target
    this.types.forEach(function (type) {
        target.addType(type);
    });
};

AVal.prototype.addForward = function (fwd) {
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

        if (fwd.equals(oldFwd)) return false;
    }
    this.forwards.add(fwd);
    return true;
};

AVal.prototype.equals = function (other) {
    // simple reference comparison
    return this === other;
};

/**
 * TODO: check whether we really need this method.
 * @param {string} prop
 * @returns {AVal}
 */
AVal.prototype.getProp = function (prop) {
    if (prop === '✖') {
        // ✖ is the bogus property name added for error recovery.
        return AValNull;
    }
    if (this.props.has(prop)) {
        return this.props.get(prop);
    } else {
        return AValNull;
    }
};

/**
 * the super class of all types
 * each type should be distinguishable by '===' operation.
 * @constructor
 */
function Type() {}
Type.prototype = Object.create(null);

/**
 * 1. object types
 * @param {AVal} proto - AVal of constructor's prototype
 * @param {string} name - guessed name
 */
function ObjType(proto, name) {
    this.name = name;
    this.props = new Map();

    // share proto with __proto__
    this.setProp('__proto__', proto);
}
ObjType.prototype = Object.create(Type.prototype);
/**
 * @param {string|null} prop - null for computed props
 * @param {boolean} readOnly - if false, create AVal for prop if necessary
 * @returns {AVal} AVal of the property
 */
ObjType.prototype.getProp = function (prop, readOnly) {
    if (prop === '✖') {
        // ✖ is the bogus property name added during parsing error recovery.
        return AValNull;
    }
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
ObjType.prototype.setProp = function (prop, aval) {
    if (prop === '✖') {
        // ✖ is the bogus property name added during parsing error recovery.
        return;
    }
    this.props.set(prop, aval);
};
/**
 * TODO: Check this function's necessity
 * @param {string} prop
 * @returns {boolean}
 */
ObjType.prototype.hasProp = function (prop) {
    if (prop === '✖') return false;
    return this.props.has(prop);
};
/**
 * TODO: Check this function's necessity
 * @param {Type} type
 * @param {string} prop
 */
ObjType.prototype.addTypeToProp = function (type, prop) {
    if (prop === '✖') return;
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
ObjType.prototype.joinAValToProp = function (aval, prop) {
    var self = this;
    aval.getTypes().forEach(function (type) {
        self.addTypeToProp(type, prop);
    });
};

// make an Obj from the global scope
function mkObjFromGlobalScope(gScope) {
    var gObj = new ObjType(AValNull, '*global scope*');
    gObj.props = gScope.varMap;
    // Override getProp method for global object
    // We ignore 'readOnly' parameter to always return its own prop AVal
    gObj.getProp = function (prop) {
        return ObjType.prototype.getProp.call(this, prop);
    };
    return gObj;
}

/**
 * 2. primitive types
 * @constructor
 * @param {string} name
 */
function PrimType(name) {
    this.name = name;
}
PrimType.prototype = Object.create(Type.prototype);

/**
 * 3. function types
 * the name is used for the type of the instances from the function
 * @constructor
 * @param {AVal} fn_proto - AVal for constructor's .prototype
 * @param {string} name - guessed name
 * @param {[string]} argNames - list of parameter names
 * @param {Scope} sc - functions scope chain, or closure
 * @param {node} originNode - AST node for the function
 * @param {Type} argProto - prototype for arguments object
 */
function FnType(fn_proto, name, argNames, sc, originNode, argProto) {
    ObjType.call(this, fn_proto, name);
    this.paramNames = argNames;
    this.sc = sc;
    this.originNode = originNode;
    this.argProto = argProto;
    // funEnv : CallContext -> [self, ret, exc]
    this.funEnv = new Map();
}
FnType.prototype = Object.create(ObjType.prototype);

/**
 * construct Status for function
 * @param {CallContext} delta - call context
 * @returns {[AVal, AVal, AVal]} - for self, return and exception AVals
 */
FnType.prototype.getFunEnv = function (delta) {
    if (this.funEnv.has(delta)) {
        return this.funEnv.get(delta);
    } else {
        var triple = [new AVal(), new AVal(), new AVal()];
        this.funEnv.set(delta, triple);
        return triple;
    }
};

FnType.prototype.getArgumentsObject = function (delta) {
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
FnType.prototype.getInstance = function () {
    // objInstance is the object made by the functioann
    if (this.objInstance) return this.objInstance;
    // we unify constructor's .prototype and instance's __proto__
    this.objInstance = new ObjType(this.getProp('prototype'));
    return this.objInstance;
};

/** 
 * 4. array types
 * @constructor
 */
function ArrType(arr_proto) {
    ObjType.call(this, arr_proto, 'Array');
}
ArrType.prototype = Object.create(ObjType.prototype);

// Make primitive types
var PrimNumber = new PrimType('number');
var PrimString = new PrimType('string');
var PrimBoolean = new PrimType('boolean');

// AbsNull represents all empty abstract values.
var AValNull = new AVal();
// You should not add any properties to it.
AValNull.props = null;
// Adding types are ignored.
AValNull.addType = function () {};

// export
exports.Type = Type;
exports.ObjType = ObjType;
exports.FnType = FnType;
exports.ArrType = ArrType;
exports.PrimNumber = PrimNumber;
exports.PrimString = PrimString;
exports.PrimBoolean = PrimBoolean;
exports.mkObjFromGlobalScope = mkObjFromGlobalScope;

exports.AVal = AVal;
exports.AValNull = AValNull;

},{}],7:[function(require,module,exports){
// import necessary libraries
'use strict';

var acorn = require('acorn/dist/acorn');
var aux = require('./aux');
var types = require('./domains/types');
var context = require('./domains/context');
var status = require('./domains/status');
var util = require('util');
var varBlock = require('./varBlock');
var cGen = require('./constraint/cGen');
var varRefs = require('./varrefs');

function analyze(input, retAll) {
    // the Scope object for global scope
    // scope.Scope.globalScope = new scope.Scope(null);

    // parsing input program
    var ast = acorn.parse(input);

    var nodeArrayIndexedByList = aux.getNodeList(ast);
    //    console.log(nodeArrayIndexedByList);

    // Show AST before scope resolution
    // aux.showUnfolded(ast);

    /*
        // attatch the global scope to program node
        ast.scope = scope.Scope.globalScope;
    
        // walk recursively to annotate scope objects and
        // add variables to each scopes
        walk.recursive(ast, scope.Scope.globalScope, null,
                       scopeResolver.scopeResolver);
    
        // After Scope Resolution
        console.log('\n\n[[After]]\n');
        aux.showUnfolded(ast);
    
        var constraints = cGen.getConstraints(ast);
    
        console.log('\n\n[[Constraints]]\n');
        aux.showUnfolded(constraints);
    */
    var gBlockAndAnnotatedAST = varBlock.annotateBlockInfo(ast);
    var gBlock = gBlockAndAnnotatedAST.globalBlock;
    var initialContext = new context.CallSiteContext();
    var gScope = gBlock.getScopeInstance(null, initialContext);
    var gObject = types.mkObjFromGlobalScope(gScope);
    var initStatus = new status.Status(gObject, types.AValNull, types.AValNull, initialContext, gScope);
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
        }

    };
    cGen.addConstraints(ast, initStatus, rtCX);
    var constraints = cGen.constraints;
    //aux.showUnfolded(gBlockAndAnnotatedAST.ast);
    // aux.showUnfolded(constraints);
    // aux.showUnfolded(gBlock);
    // console.log(util.inspect(gBlock, {depth: 10}));
    if (retAll) {
        return { gObject: gObject, AST: ast };
    } else {
        return gObject;
    }
}

exports.analyze = analyze;
exports.findIdentifierNodeAt = varRefs.findIdentifierNodeAt;

},{"./aux":1,"./constraint/cGen":2,"./domains/context":4,"./domains/status":5,"./domains/types":6,"./varBlock":8,"./varrefs":9,"acorn/dist/acorn":10,"util":16}],8:[function(require,module,exports){
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

var types = require('./domains/types');
var walk = require('acorn/dist/walk');
var aux = require('./aux');

function VarBlock(paren, originLabel, isCatch) {
    this.paren = paren;
    this.originLabel = originLabel;
    this.isCatch = isCatch;
    this.paramVarNames = [];
    this.localVarNames = [];

    this.usedVariables = [];
    // this.useArgumentsObject
    this.instances = Object.create(null);
    this.scopeInstances = [];
}

VarBlock.prototype = Object.create(null);

VarBlock.prototype.isGlobal = function () {
    return this.paren == null;
};
VarBlock.prototype.isFunction = function () {
    return this.paren != null && this.localVarNames != null;
};
VarBlock.prototype.isCatchBlock = function () {
    return this.isCatch;
};

VarBlock.prototype.getLocalVarNames = function () {
    return this.localVarNames;
};
VarBlock.prototype.getParamVarNames = function () {
    return this.paramVarNames;
};
VarBlock.prototype.hasLocalVar = function (varName) {
    return this.localVarNames && this.localVarNames.indexOf(varName) > -1;
};
VarBlock.prototype.hasParamVar = function (varName) {
    return this.paramVarNames.indexOf(varName) > -1;
};
VarBlock.prototype.hasVar = function (varName) {
    return this.hasParamVar(varName) || this.hasLocalVar(varName);
};

VarBlock.prototype.addDeclaredLocalVar = function (varName, isFunDecl) {
    var currBlock = this;
    // peel off initial catch blocks
    // for function decl, skip any catch blocks,
    // for variable decl, skip catch block with different varName.
    while (currBlock.isCatchBlock() && (isFunDecl || !currBlock.hasParamVar(varName))) {
        currBlock = currBlock.paren;
    }
    // if already added, do not add
    if (!currBlock.hasVar(varName)) {
        currBlock.localVarNames.push(varName);
    }
    // returns the block object that contains the variable
    return currBlock;
};
VarBlock.prototype.addParamVar = function (varName) {
    this.paramVarNames.push(varName);
};
VarBlock.prototype.findVarInChain = function (varName) {
    var currBlock = this;
    while (currBlock && currBlock.paren && !currBlock.hasVar(varName)) {
        currBlock = currBlock.paren;
    }
    // if not found, it will return the global
    return currBlock;
};

VarBlock.prototype.addUsedVar = function (varName) {
    if (this.usedVariables.indexOf(varName) === -1) {
        this.usedVariables.push(varName);
    }
};
VarBlock.prototype.getUsedVarNames = function () {
    return this.usedVariables;
};
VarBlock.prototype.isUsedVar = function (varName) {
    return this.usedVariables.indexOf(varName) > -1;
};

// returns a mapping
VarBlock.prototype.getInstance = function (delta) {
    if (this.instances[delta]) {
        return this.instances[delta];
    }
    // construct VarMap
    var varMap = new Map();
    var varNames = this.getParamVarNames().concat(this.getLocalVarNames());

    for (var i = 0; i < varNames.length; i++) {
        varMap.set(varNames[i], new types.AVal());
    }
    // remember the instance
    this.instances[delta] = varMap;
    return varMap;
};
// returns an array
VarBlock.prototype.getParamAVals = function (delta) {
    var instance = this.getInstance(delta);
    var params = [];
    this.getParamVarNames().forEach(function (name) {
        params.push(instance[aux.internalName(name)]);
    });
    return params;
};
// returns an AVal
VarBlock.prototype.getArgumentsAVal = function (delta) {
    if (!this.useArgumentsObject) {
        throw new Error('Not for this VarBlock');
    }
    return this.getInstance(delta)[aux.internalName('arguments')];
};

// get a Scope instance
VarBlock.prototype.getScopeInstance = function (paren, delta) {
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

var declaredVariableFinder = walk.make({
    Function: function Function(node, currBlock, c) {
        var parenBlock = currBlock;
        if (node.id) {
            var funcName = node.id.name;
            parenBlock = currBlock.addDeclaredLocalVar(funcName, true);
        }
        // create a VarBlock for function
        var funcBlock = new VarBlock(parenBlock, node['@label']);
        node.body['@block'] = funcBlock;
        // add function parameters to the scope
        for (var i = 0; i < node.params.length; i++) {
            var paramName = node.params[i].name;
            funcBlock.addParamVar(paramName);
        }
        c(node.body, funcBlock, undefined);
    },
    VariableDeclaration: function VariableDeclaration(node, currBlock, c) {
        for (var i = 0; i < node.declarations.length; i++) {
            var decl = node.declarations[i];
            var name = decl.id.name;
            currBlock.addDeclaredLocalVar(name);
        }
        if (decl.init) c(decl.init, currBlock, undefined);
    },
    TryStatement: function TryStatement(node, currScope, c) {
        c(node.block, currScope, undefined);
        if (node.handler) {
            c(node.handler, currScope, undefined);
        }
        if (node.finalizer) {
            c(node.finalizer, currScope, undefined);
        }
    },
    CatchClause: function CatchClause(node, currBlock, c) {
        var catchBlock = new VarBlock(currBlock, node['@label'], true);
        catchBlock.addParamVar(node.param.name);
        node.body['@block'] = catchBlock;
        c(node.body, catchBlock, undefined);
    }
});

// For variables in global and arguments in functions
var variableUsageCollector = walk.make({
    Identifier: function Identifier(node, currBlock, c) {
        var containingBlock,
            varName = node.name;
        if (varName !== 'arguments') {
            containingBlock = currBlock.findVarInChain(varName);
            if (containingBlock.isGlobal()) {
                containingBlock.addDeclaredLocalVar(varName);
            }
            containingBlock.addUsedVar(varName);
        } else {
            // varName == 'arguments'
            containingBlock = currBlock;
            while (containingBlock.isCatchBlock() && !containingBlock.hasParamVar(varName)) {
                containingBlock = containingBlock.paren;
            }
            if (containingBlock.hasVar(varName)) {
                // arguments is explicitly declared
                containingBlock.addUsedVar(varName);
            } else {
                // arguments is not explicitly declared
                // add it as local variable
                containingBlock.addDeclaredLocalVar(varName);
                // also it is used
                containingBlock.addUsedVar(varName);
                if (containingBlock.isFunction()) {
                    containingBlock.useArgumentsObject = true;
                }
            }
        }
    },

    ReturnStatement: function ReturnStatement(node, currBlock, c) {
        var functionBlock = currBlock;
        while (functionBlock.isCatchBlock()) {
            functionBlock = functionBlock.paren;
        }
        if (!functionBlock.isGlobal() && node.argument !== null) {
            functionBlock.useReturnWithArgument = true;
        }
        if (node.argument) {
            c(node.argument, currBlock, undefined);
        }
    },

    ScopeBody: function ScopeBody(node, currBlock, c) {
        c(node, node['@block'] || currBlock);
    }
});

function annotateBlockInfo(ast, gBlock) {
    if (!gBlock) {
        // when global block is not given, create
        gBlock = new VarBlock(null, ast['@label']);
    }
    walk.recursive(ast, gBlock, null, declaredVariableFinder);
    walk.recursive(ast, gBlock, null, variableUsageCollector);
    return { globalBlock: gBlock, ast: ast };
}

// define scope object
function Scope(paren, varMap, vb) {
    this.paren = paren;
    this.varMap = varMap;
    this.vb = vb;
}
Scope.prototype = Object.create(null);
// find AVal of a variable in the chain
Scope.prototype.getAValOf = function (varName) {
    var curr = this;
    while (curr != null) {
        if (curr.varMap.has(varName)) {
            return curr.varMap.get(varName);
        }
        curr = curr.paren;
    }
    throw new Error('Should have found the variable');
};
// remove initial catch scopes from the chain
Scope.prototype.removeInitialCatchBlocks = function () {
    var curr = this;
    while (curr.vb.isCatchBlock()) {
        curr = curr.paren;
    }
    return curr;
};

exports.VarBlock = VarBlock;
exports.annotateBlockInfo = annotateBlockInfo;
exports.Scope = Scope;

},{"./aux":1,"./domains/types":6,"acorn/dist/walk":11}],9:[function(require,module,exports){
'use strict';

var walk = require('acorn/dist/walk');
var fs = require('fs');
var infer = require('./infer');

function findIdentifierNodeAt(ast, pos) {
    'use strict';

    // defining walker
    var searchWalker = walk.make({
        Function: function Function(node, st, c) {
            if (node.id) c(node.id, st);
            for (var i = 0; i < node.params.length; i++) c(node.params[i], st);
            c(node.body, st);
        },
        TryStatement: function TryStatement(node, st, c) {
            c(node.block, st);
            if (node.handler) {
                c(node.handler.param, st);
                c(node.handler.body, st);
            }
            if (node.finalizer) {
                c(node.finalizer, st);
            }
        },
        VariableDeclaration: function VariableDeclaration(node, st, c) {
            for (var i = 0; i < node.declarations.length; ++i) {
                var decl = node.declarations[i];
                c(decl.id, st);
                if (decl.init) c(decl.init, st, 'Expression');
            }
        }
    });

    // find the node
    var foundNode = walk.findNodeAround(ast, pos, undefined, searchWalker).node;
    if (foundNode.type === 'Identifier') {
        return foundNode;
    } else {
        return null;
    }
}
/**
 *
 * @param ast - scope annotated AST
 * @param {number} pos - character position
 * @returns {*} - array of AST nodes
 */
function findIdRefsAt(ast, pos) {
    'use strict';
    var idNode = findIdentifierNodeAt(ast, pos);
    if (!idNode) {
        // pos is not at a variable
        return null;
    }
    // find refs for the id node
    var refs = findRefsToVariable(ast, idNode);

    return refs;
}

/**
 *
 * @param ast - scope annotated AST
 * @param idNode - identifier node of interest
 * @returns {Array} - array of AST nodes
 */
function findRefsToVariable(ast, idNode) {
    'use strict';
    var name = idNode.name;

    var refs = [];

    // TODO: find refs for the id
    return refs;
}

// ============================================

function test() {
    'use strict';
    var test_pgm = fs.readFileSync('./tests/a.js');
    var result = infer.analyze(test_pgm, true);

    for (var i = 0; i < test_pgm.length; i++) {
        var foundNode = findIdentifierNodeAt(result.AST, i);
        if (foundNode) {
            console.log(i, ': ', foundNode.name);
        }
    }
}

exports.findIdentifierNodeAt = findIdentifierNodeAt;

},{"./infer":7,"acorn/dist/walk":11,"fs":12}],10:[function(require,module,exports){
(function (global){
(function(f){if(typeof exports==="object"&&typeof module!=="undefined"){module.exports=f()}else if(typeof define==="function"&&define.amd){define([],f)}else{var g;if(typeof window!=="undefined"){g=window}else if(typeof global!=="undefined"){g=global}else if(typeof self!=="undefined"){g=self}else{g=this}g.acorn = f()}})(function(){var define,module,exports;return (function e(t,n,r){function s(o,u){if(!n[o]){if(!t[o]){var a=typeof require=="function"&&require;if(!u&&a)return a(o,!0);if(i)return i(o,!0);var f=new Error("Cannot find module '"+o+"'");throw f.code="MODULE_NOT_FOUND",f}var l=n[o]={exports:{}};t[o][0].call(l.exports,function(e){var n=t[o][1][e];return s(n?n:e)},l,l.exports,e,t,n,r)}return n[o].exports}var i=typeof require=="function"&&require;for(var o=0;o<r.length;o++)s(r[o]);return s})({1:[function(_dereq_,module,exports){


// The main exported interface (under `self.acorn` when in the
// browser) is a `parse` function that takes a code string and
// returns an abstract syntax tree as specified by [Mozilla parser
// API][api].
//
// [api]: https://developer.mozilla.org/en-US/docs/SpiderMonkey/Parser_API

"use strict";

exports.parse = parse;

// This function tries to parse a single expression at a given
// offset in a string. Useful for parsing mixed-language formats
// that embed JavaScript expressions.

exports.parseExpressionAt = parseExpressionAt;

// Acorn is organized as a tokenizer and a recursive-descent parser.
// The `tokenize` export provides an interface to the tokenizer.

exports.tokenizer = tokenizer;
exports.__esModule = true;
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

var _state = _dereq_("./state");

var Parser = _state.Parser;

var _options = _dereq_("./options");

var getOptions = _options.getOptions;

_dereq_("./parseutil");

_dereq_("./statement");

_dereq_("./lval");

_dereq_("./expression");

exports.Parser = _state.Parser;
exports.plugins = _state.plugins;
exports.defaultOptions = _options.defaultOptions;

var _location = _dereq_("./location");

exports.SourceLocation = _location.SourceLocation;
exports.getLineInfo = _location.getLineInfo;
exports.Node = _dereq_("./node").Node;

var _tokentype = _dereq_("./tokentype");

exports.TokenType = _tokentype.TokenType;
exports.tokTypes = _tokentype.types;

var _tokencontext = _dereq_("./tokencontext");

exports.TokContext = _tokencontext.TokContext;
exports.tokContexts = _tokencontext.types;

var _identifier = _dereq_("./identifier");

exports.isIdentifierChar = _identifier.isIdentifierChar;
exports.isIdentifierStart = _identifier.isIdentifierStart;
exports.Token = _dereq_("./tokenize").Token;

var _whitespace = _dereq_("./whitespace");

exports.isNewLine = _whitespace.isNewLine;
exports.lineBreak = _whitespace.lineBreak;
exports.lineBreakG = _whitespace.lineBreakG;
var version = "1.2.2";exports.version = version;

function parse(input, options) {
  var p = parser(options, input);
  var startPos = p.pos,
      startLoc = p.options.locations && p.curPosition();
  p.nextToken();
  return p.parseTopLevel(p.options.program || p.startNodeAt(startPos, startLoc));
}

function parseExpressionAt(input, pos, options) {
  var p = parser(options, input, pos);
  p.nextToken();
  return p.parseExpression();
}

function tokenizer(input, options) {
  return parser(options, input);
}

function parser(options, input) {
  return new Parser(getOptions(options), String(input));
}

},{"./expression":6,"./identifier":7,"./location":8,"./lval":9,"./node":10,"./options":11,"./parseutil":12,"./state":13,"./statement":14,"./tokencontext":15,"./tokenize":16,"./tokentype":17,"./whitespace":19}],2:[function(_dereq_,module,exports){
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

},{}],3:[function(_dereq_,module,exports){
// shim for using process in browser

var process = module.exports = {};
var queue = [];
var draining = false;

function drainQueue() {
    if (draining) {
        return;
    }
    draining = true;
    var currentQueue;
    var len = queue.length;
    while(len) {
        currentQueue = queue;
        queue = [];
        var i = -1;
        while (++i < len) {
            currentQueue[i]();
        }
        len = queue.length;
    }
    draining = false;
}
process.nextTick = function (fun) {
    queue.push(fun);
    if (!draining) {
        setTimeout(drainQueue, 0);
    }
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

},{}],4:[function(_dereq_,module,exports){
module.exports = function isBuffer(arg) {
  return arg && typeof arg === 'object'
    && typeof arg.copy === 'function'
    && typeof arg.fill === 'function'
    && typeof arg.readUInt8 === 'function';
}
},{}],5:[function(_dereq_,module,exports){
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

exports.isBuffer = _dereq_('./support/isBuffer');

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
exports.inherits = _dereq_('inherits');

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

}).call(this,_dereq_('_process'),typeof global !== "undefined" ? global : typeof self !== "undefined" ? self : typeof window !== "undefined" ? window : {})
},{"./support/isBuffer":4,"_process":3,"inherits":2}],6:[function(_dereq_,module,exports){
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

var tt = _dereq_("./tokentype").types;

var Parser = _dereq_("./state").Parser;

var reservedWords = _dereq_("./identifier").reservedWords;

var has = _dereq_("./util").has;

var pp = Parser.prototype;

// Check if property name clashes with already added.
// Object/class getters and setters are not allowed to clash —
// either with each other or with an init property — and in
// strict mode, init properties are also not allowed to be repeated.

pp.checkPropClash = function (prop, propHash) {
  if (this.options.ecmaVersion >= 6) return;
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
  var kind = prop.kind || "init",
      other = undefined;
  if (has(propHash, name)) {
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
  if (this.type === tt.comma) {
    var node = this.startNodeAt(startPos, startLoc);
    node.expressions = [expr];
    while (this.eat(tt.comma)) node.expressions.push(this.parseMaybeAssign(noIn, refShorthandDefaultPos));
    return this.finishNode(node, "SequenceExpression");
  }
  return expr;
};

// Parse an assignment expression. This includes applications of
// operators like `+=`.

pp.parseMaybeAssign = function (noIn, refShorthandDefaultPos, afterLeftParse) {
  if (this.type == tt._yield && this.inGenerator) return this.parseYield();

  var failOnShorthandAssign = undefined;
  if (!refShorthandDefaultPos) {
    refShorthandDefaultPos = { start: 0 };
    failOnShorthandAssign = true;
  } else {
    failOnShorthandAssign = false;
  }
  var startPos = this.start,
      startLoc = this.startLoc;
  if (this.type == tt.parenL || this.type == tt.name) this.potentialArrowAt = this.start;
  var left = this.parseMaybeConditional(noIn, refShorthandDefaultPos);
  if (afterLeftParse) left = afterLeftParse.call(this, left, startPos, startLoc);
  if (this.type.isAssign) {
    var node = this.startNodeAt(startPos, startLoc);
    node.operator = this.value;
    node.left = this.type === tt.eq ? this.toAssignable(left) : left;
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
  if (this.eat(tt.question)) {
    var node = this.startNodeAt(startPos, startLoc);
    node.test = expr;
    node.consequent = this.parseMaybeAssign();
    this.expect(tt.colon);
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
  if (Array.isArray(leftStartPos)) {
    if (this.options.locations && noIn === undefined) {
      // shift arguments to left by one
      noIn = minPrec;
      minPrec = leftStartLoc;
      // flatten leftStartPos
      leftStartLoc = leftStartPos[1];
      leftStartPos = leftStartPos[0];
    }
  }
  if (prec != null && (!noIn || this.type !== tt._in)) {
    if (prec > minPrec) {
      var node = this.startNodeAt(leftStartPos, leftStartLoc);
      node.left = left;
      node.operator = this.value;
      var op = this.type;
      this.next();
      var startPos = this.start,
          startLoc = this.startLoc;
      node.right = this.parseExprOp(this.parseMaybeUnary(), startPos, startLoc, prec, noIn);
      this.finishNode(node, op === tt.logicalOR || op === tt.logicalAND ? "LogicalExpression" : "BinaryExpression");
      return this.parseExprOp(node, leftStartPos, leftStartLoc, minPrec, noIn);
    }
  }
  return left;
};

// Parse unary operators, both prefix and postfix.

pp.parseMaybeUnary = function (refShorthandDefaultPos) {
  if (this.type.prefix) {
    var node = this.startNode(),
        update = this.type === tt.incDec;
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
  if (Array.isArray(startPos)) {
    if (this.options.locations && noCalls === undefined) {
      // shift arguments to left by one
      noCalls = startLoc;
      // flatten startPos
      startLoc = startPos[1];
      startPos = startPos[0];
    }
  }
  for (;;) {
    if (this.eat(tt.dot)) {
      var node = this.startNodeAt(startPos, startLoc);
      node.object = base;
      node.property = this.parseIdent(true);
      node.computed = false;
      base = this.finishNode(node, "MemberExpression");
    } else if (this.eat(tt.bracketL)) {
      var node = this.startNodeAt(startPos, startLoc);
      node.object = base;
      node.property = this.parseExpression();
      node.computed = true;
      this.expect(tt.bracketR);
      base = this.finishNode(node, "MemberExpression");
    } else if (!noCalls && this.eat(tt.parenL)) {
      var node = this.startNodeAt(startPos, startLoc);
      node.callee = base;
      node.arguments = this.parseExprList(tt.parenR, false);
      base = this.finishNode(node, "CallExpression");
    } else if (this.type === tt.backQuote) {
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
    case tt._this:
    case tt._super:
      var type = this.type === tt._this ? "ThisExpression" : "Super";
      node = this.startNode();
      this.next();
      return this.finishNode(node, type);

    case tt._yield:
      if (this.inGenerator) this.unexpected();

    case tt.name:
      var startPos = this.start,
          startLoc = this.startLoc;
      var id = this.parseIdent(this.type !== tt.name);
      if (canBeArrow && !this.canInsertSemicolon() && this.eat(tt.arrow)) return this.parseArrowExpression(this.startNodeAt(startPos, startLoc), [id]);
      return id;

    case tt.regexp:
      var value = this.value;
      node = this.parseLiteral(value.value);
      node.regex = { pattern: value.pattern, flags: value.flags };
      return node;

    case tt.num:case tt.string:
      return this.parseLiteral(this.value);

    case tt._null:case tt._true:case tt._false:
      node = this.startNode();
      node.value = this.type === tt._null ? null : this.type === tt._true;
      node.raw = this.type.keyword;
      this.next();
      return this.finishNode(node, "Literal");

    case tt.parenL:
      return this.parseParenAndDistinguishExpression(canBeArrow);

    case tt.bracketL:
      node = this.startNode();
      this.next();
      // check whether this is array comprehension or regular array
      if (this.options.ecmaVersion >= 7 && this.type === tt._for) {
        return this.parseComprehension(node, false);
      }
      node.elements = this.parseExprList(tt.bracketR, true, true, refShorthandDefaultPos);
      return this.finishNode(node, "ArrayExpression");

    case tt.braceL:
      return this.parseObj(false, refShorthandDefaultPos);

    case tt._function:
      node = this.startNode();
      this.next();
      return this.parseFunction(node, false);

    case tt._class:
      return this.parseClass(this.startNode(), false);

    case tt._new:
      return this.parseNew();

    case tt.backQuote:
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
  this.expect(tt.parenL);
  var val = this.parseExpression();
  this.expect(tt.parenR);
  return val;
};

pp.parseParenAndDistinguishExpression = function (canBeArrow) {
  var startPos = this.start,
      startLoc = this.startLoc,
      val = undefined;
  if (this.options.ecmaVersion >= 6) {
    this.next();

    if (this.options.ecmaVersion >= 7 && this.type === tt._for) {
      return this.parseComprehension(this.startNodeAt(startPos, startLoc), true);
    }

    var innerStartPos = this.start,
        innerStartLoc = this.startLoc;
    var exprList = [],
        first = true;
    var refShorthandDefaultPos = { start: 0 },
        spreadStart = undefined,
        innerParenStart = undefined;
    while (this.type !== tt.parenR) {
      first ? first = false : this.expect(tt.comma);
      if (this.type === tt.ellipsis) {
        spreadStart = this.start;
        exprList.push(this.parseParenItem(this.parseRest()));
        break;
      } else {
        if (this.type === tt.parenL && !innerParenStart) {
          innerParenStart = this.start;
        }
        exprList.push(this.parseMaybeAssign(false, refShorthandDefaultPos, this.parseParenItem));
      }
    }
    var innerEndPos = this.start,
        innerEndLoc = this.startLoc;
    this.expect(tt.parenR);

    if (canBeArrow && !this.canInsertSemicolon() && this.eat(tt.arrow)) {
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
  if (this.options.ecmaVersion >= 6 && this.eat(tt.dot)) {
    node.meta = meta;
    node.property = this.parseIdent(true);
    if (node.property.name !== "target") this.raise(node.property.start, "The only valid meta property for new is new.target");
    return this.finishNode(node, "MetaProperty");
  }
  var startPos = this.start,
      startLoc = this.startLoc;
  node.callee = this.parseSubscripts(this.parseExprAtom(), startPos, startLoc, true);
  if (this.eat(tt.parenL)) node.arguments = this.parseExprList(tt.parenR, false);else node.arguments = empty;
  return this.finishNode(node, "NewExpression");
};

// Parse template expression.

pp.parseTemplateElement = function () {
  var elem = this.startNode();
  elem.value = {
    raw: this.input.slice(this.start, this.end),
    cooked: this.value
  };
  this.next();
  elem.tail = this.type === tt.backQuote;
  return this.finishNode(elem, "TemplateElement");
};

pp.parseTemplate = function () {
  var node = this.startNode();
  this.next();
  node.expressions = [];
  var curElt = this.parseTemplateElement();
  node.quasis = [curElt];
  while (!curElt.tail) {
    this.expect(tt.dollarBraceL);
    node.expressions.push(this.parseExpression());
    this.expect(tt.braceR);
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
  while (!this.eat(tt.braceR)) {
    if (!first) {
      this.expect(tt.comma);
      if (this.afterTrailingComma(tt.braceR)) break;
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
      if (!isPattern) isGenerator = this.eat(tt.star);
    }
    this.parsePropertyName(prop);
    this.parsePropertyValue(prop, isPattern, isGenerator, startPos, startLoc, refShorthandDefaultPos);
    this.checkPropClash(prop, propHash);
    node.properties.push(this.finishNode(prop, "Property"));
  }
  return this.finishNode(node, isPattern ? "ObjectPattern" : "ObjectExpression");
};

pp.parsePropertyValue = function (prop, isPattern, isGenerator, startPos, startLoc, refShorthandDefaultPos) {
  if (this.eat(tt.colon)) {
    prop.value = isPattern ? this.parseMaybeDefault(this.start, this.startLoc) : this.parseMaybeAssign(false, refShorthandDefaultPos);
    prop.kind = "init";
  } else if (this.options.ecmaVersion >= 6 && this.type === tt.parenL) {
    if (isPattern) this.unexpected();
    prop.kind = "init";
    prop.method = true;
    prop.value = this.parseMethod(isGenerator);
  } else if (this.options.ecmaVersion >= 5 && !prop.computed && prop.key.type === "Identifier" && (prop.key.name === "get" || prop.key.name === "set") && (this.type != tt.comma && this.type != tt.braceR)) {
    if (isGenerator || isPattern) this.unexpected();
    prop.kind = prop.key.name;
    this.parsePropertyName(prop);
    prop.value = this.parseMethod(false);
  } else if (this.options.ecmaVersion >= 6 && !prop.computed && prop.key.type === "Identifier") {
    prop.kind = "init";
    if (isPattern) {
      if (this.isKeyword(prop.key.name) || this.strict && (reservedWords.strictBind(prop.key.name) || reservedWords.strict(prop.key.name)) || !this.options.allowReserved && this.isReservedWord(prop.key.name)) this.raise(prop.key.start, "Binding " + prop.key.name);
      prop.value = this.parseMaybeDefault(startPos, startLoc, prop.key);
    } else if (this.type === tt.eq && refShorthandDefaultPos) {
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
    if (this.eat(tt.bracketL)) {
      prop.computed = true;
      prop.key = this.parseMaybeAssign();
      this.expect(tt.bracketR);
      return prop.key;
    } else {
      prop.computed = false;
    }
  }
  return prop.key = this.type === tt.num || this.type === tt.string ? this.parseExprAtom() : this.parseIdent(true);
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
  this.expect(tt.parenL);
  node.params = this.parseBindingList(tt.parenR, false, false);
  var allowExpressionBody = undefined;
  if (this.options.ecmaVersion >= 6) {
    node.generator = isGenerator;
    allowExpressionBody = true;
  } else {
    allowExpressionBody = false;
  }
  this.parseFunctionBody(node, allowExpressionBody);
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
  var isExpression = allowExpression && this.type !== tt.braceL;

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
      this.expect(tt.comma);
      if (allowTrailingComma && this.afterTrailingComma(close)) break;
    } else first = false;

    if (allowEmpty && this.type === tt.comma) {
      elts.push(null);
    } else {
      if (this.type === tt.ellipsis) elts.push(this.parseSpread(refShorthandDefaultPos));else elts.push(this.parseMaybeAssign(false, refShorthandDefaultPos));
    }
  }
  return elts;
};

// Parse the next token as an identifier. If `liberal` is true (used
// when parsing properties), it will also convert keywords into
// identifiers.

pp.parseIdent = function (liberal) {
  var node = this.startNode();
  if (liberal && this.options.allowReserved == "never") liberal = false;
  if (this.type === tt.name) {
    if (!liberal && (!this.options.allowReserved && this.isReservedWord(this.value) || this.strict && reservedWords.strict(this.value) && (this.options.ecmaVersion >= 6 || this.input.slice(this.start, this.end).indexOf("\\") == -1))) this.raise(this.start, "The keyword '" + this.value + "' is reserved");
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
  if (this.type == tt.semi || this.canInsertSemicolon() || this.type != tt.star && !this.type.startsExpr) {
    node.delegate = false;
    node.argument = null;
  } else {
    node.delegate = this.eat(tt.star);
    node.argument = this.parseMaybeAssign();
  }
  return this.finishNode(node, "YieldExpression");
};

// Parses array and generator comprehensions.

pp.parseComprehension = function (node, isGenerator) {
  node.blocks = [];
  while (this.type === tt._for) {
    var block = this.startNode();
    this.next();
    this.expect(tt.parenL);
    block.left = this.parseBindingAtom();
    this.checkLVal(block.left, true);
    this.expectContextual("of");
    block.right = this.parseExpression();
    this.expect(tt.parenR);
    node.blocks.push(this.finishNode(block, "ComprehensionBlock"));
  }
  node.filter = this.eat(tt._if) ? this.parseParenExpression() : null;
  node.body = this.parseExpression();
  this.expect(isGenerator ? tt.parenR : tt.bracketR);
  node.generator = isGenerator;
  return this.finishNode(node, "ComprehensionExpression");
};

},{"./identifier":7,"./state":13,"./tokentype":17,"./util":18}],7:[function(_dereq_,module,exports){


// Test whether a given character code starts an identifier.

"use strict";

exports.isIdentifierStart = isIdentifierStart;

// Test whether a given character is part of an identifier.

exports.isIdentifierChar = isIdentifierChar;
exports.__esModule = true;
// This is a trick taken from Esprima. It turns out that, on
// non-Chrome browsers, to check whether a string is in a set, a
// predicate containing a big ugly `switch` statement is faster than
// a regular expression, and on Chrome the two are about on par.
// This function uses `eval` (non-lexical) to produce such a
// predicate from a space-separated string of words.
//
// It starts by sorting the words by length.

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
    if (arr.length == 1) {
      return f += "return str === " + JSON.stringify(arr[0]) + ";";
    }f += "switch(str){";
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
  var pos = 65536;
  for (var i = 0; i < set.length; i += 2) {
    pos += set[i];
    if (pos > code) {
      return false;
    }pos += set[i + 1];
    if (pos >= code) {
      return true;
    }
  }
}
function isIdentifierStart(code, astral) {
  if (code < 65) {
    return code === 36;
  }if (code < 91) {
    return true;
  }if (code < 97) {
    return code === 95;
  }if (code < 123) {
    return true;
  }if (code <= 65535) {
    return code >= 170 && nonASCIIidentifierStart.test(String.fromCharCode(code));
  }if (astral === false) {
    return false;
  }return isInAstralSet(code, astralIdentifierStartCodes);
}

function isIdentifierChar(code, astral) {
  if (code < 48) {
    return code === 36;
  }if (code < 58) {
    return true;
  }if (code < 65) {
    return false;
  }if (code < 91) {
    return true;
  }if (code < 97) {
    return code === 95;
  }if (code < 123) {
    return true;
  }if (code <= 65535) {
    return code >= 170 && nonASCIIidentifier.test(String.fromCharCode(code));
  }if (astral === false) {
    return false;
  }return isInAstralSet(code, astralIdentifierStartCodes) || isInAstralSet(code, astralIdentifierCodes);
}

},{}],8:[function(_dereq_,module,exports){
"use strict";

var _classCallCheck = function (instance, Constructor) { if (!(instance instanceof Constructor)) { throw new TypeError("Cannot call a class as a function"); } };

// The `getLineInfo` function is mostly useful when the
// `locations` option is off (for performance reasons) and you
// want to find the line/column position for a given character
// offset. `input` should be the code string that the offset refers
// into.

exports.getLineInfo = getLineInfo;
exports.__esModule = true;

var Parser = _dereq_("./state").Parser;

var lineBreakG = _dereq_("./whitespace").lineBreakG;

var deprecate = _dereq_("util").deprecate;

// These are used when `options.locations` is on, for the
// `startLoc` and `endLoc` properties.

var Position = exports.Position = (function () {
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

var SourceLocation = exports.SourceLocation = function SourceLocation(p, start, end) {
  _classCallCheck(this, SourceLocation);

  this.start = start;
  this.end = end;
  if (p.sourceFile !== null) this.source = p.sourceFile;
};

function getLineInfo(input, offset) {
  for (var line = 1, cur = 0;;) {
    lineBreakG.lastIndex = cur;
    var match = lineBreakG.exec(input);
    if (match && match.index < offset) {
      ++line;
      cur = match.index + match[0].length;
    } else {
      return new Position(line, offset - cur);
    }
  }
}

var pp = Parser.prototype;

// This function is used to raise exceptions on parse errors. It
// takes an offset integer (into the current `input`) to indicate
// the location of the error, attaches the position to the end
// of the error message, and then raises a `SyntaxError` with that
// message.

pp.raise = function (pos, message) {
  var loc = getLineInfo(this.input, pos);
  message += " (" + loc.line + ":" + loc.column + ")";
  var err = new SyntaxError(message);
  err.pos = pos;err.loc = loc;err.raisedAt = this.pos;
  throw err;
};

pp.curPosition = function () {
  return new Position(this.curLine, this.pos - this.lineStart);
};

pp.markPosition = function () {
  return this.options.locations ? [this.start, this.startLoc] : this.start;
};

},{"./state":13,"./whitespace":19,"util":5}],9:[function(_dereq_,module,exports){
"use strict";

var tt = _dereq_("./tokentype").types;

var Parser = _dereq_("./state").Parser;

var reservedWords = _dereq_("./identifier").reservedWords;

var has = _dereq_("./util").has;

var pp = Parser.prototype;

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
  node.argument = this.type === tt.name || this.type === tt.bracketL ? this.parseBindingAtom() : this.unexpected();
  return this.finishNode(node, "RestElement");
};

// Parses lvalue (assignable) atom.

pp.parseBindingAtom = function () {
  if (this.options.ecmaVersion < 6) return this.parseIdent();
  switch (this.type) {
    case tt.name:
      return this.parseIdent();

    case tt.bracketL:
      var node = this.startNode();
      this.next();
      node.elements = this.parseBindingList(tt.bracketR, true, true);
      return this.finishNode(node, "ArrayPattern");

    case tt.braceL:
      return this.parseObj(true);

    default:
      this.unexpected();
  }
};

pp.parseBindingList = function (close, allowEmpty, allowTrailingComma) {
  var elts = [],
      first = true;
  while (!this.eat(close)) {
    if (first) first = false;else this.expect(tt.comma);
    if (allowEmpty && this.type === tt.comma) {
      elts.push(null);
    } else if (allowTrailingComma && this.afterTrailingComma(close)) {
      break;
    } else if (this.type === tt.ellipsis) {
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
  if (Array.isArray(startPos)) {
    if (this.options.locations && noCalls === undefined) {
      // shift arguments to left by one
      left = startLoc;
      // flatten startPos
      startLoc = startPos[1];
      startPos = startPos[0];
    }
  }
  left = left || this.parseBindingAtom();
  if (!this.eat(tt.eq)) return left;
  var node = this.startNodeAt(startPos, startLoc);
  node.operator = "=";
  node.left = left;
  node.right = this.parseMaybeAssign();
  return this.finishNode(node, "AssignmentPattern");
};

// Verify that a node is an lval — something that can be assigned
// to.

pp.checkLVal = function (expr, isBinding, checkClashes) {
  switch (expr.type) {
    case "Identifier":
      if (this.strict && (reservedWords.strictBind(expr.name) || reservedWords.strict(expr.name))) this.raise(expr.start, (isBinding ? "Binding " : "Assigning to ") + expr.name + " in strict mode");
      if (checkClashes) {
        if (has(checkClashes, expr.name)) this.raise(expr.start, "Argument name clash in strict mode");
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

},{"./identifier":7,"./state":13,"./tokentype":17,"./util":18}],10:[function(_dereq_,module,exports){
"use strict";

var _classCallCheck = function (instance, Constructor) { if (!(instance instanceof Constructor)) { throw new TypeError("Cannot call a class as a function"); } };

exports.__esModule = true;

var Parser = _dereq_("./state").Parser;

var SourceLocation = _dereq_("./location").SourceLocation;

// Start an AST node, attaching a start offset.

var pp = Parser.prototype;

var Node = exports.Node = function Node() {
  _classCallCheck(this, Node);
};

pp.startNode = function () {
  var node = new Node();
  node.start = this.start;
  if (this.options.locations) node.loc = new SourceLocation(this, this.startLoc);
  if (this.options.directSourceFile) node.sourceFile = this.options.directSourceFile;
  if (this.options.ranges) node.range = [this.start, 0];
  return node;
};

pp.startNodeAt = function (pos, loc) {
  var node = new Node();
  if (Array.isArray(pos)) {
    if (this.options.locations && loc === undefined) {
      // flatten pos
      loc = pos[1];
      pos = pos[0];
    }
  }
  node.start = pos;
  if (this.options.locations) node.loc = new SourceLocation(this, loc);
  if (this.options.directSourceFile) node.sourceFile = this.options.directSourceFile;
  if (this.options.ranges) node.range = [pos, 0];
  return node;
};

// Finish an AST node, adding `type` and `end` properties.

pp.finishNode = function (node, type) {
  node.type = type;
  node.end = this.lastTokEnd;
  if (this.options.locations) node.loc.end = this.lastTokEndLoc;
  if (this.options.ranges) node.range[1] = this.lastTokEnd;
  return node;
};

// Finish node at given position

pp.finishNodeAt = function (node, type, pos, loc) {
  node.type = type;
  if (Array.isArray(pos)) {
    if (this.options.locations && loc === undefined) {
      // flatten pos
      loc = pos[1];
      pos = pos[0];
    }
  }
  node.end = pos;
  if (this.options.locations) node.loc.end = loc;
  if (this.options.ranges) node.range[1] = pos;
  return node;
};

},{"./location":8,"./state":13}],11:[function(_dereq_,module,exports){


// Interpret and default an options object

"use strict";

exports.getOptions = getOptions;
exports.__esModule = true;

var _util = _dereq_("./util");

var has = _util.has;
var isArray = _util.isArray;

var SourceLocation = _dereq_("./location").SourceLocation;

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
};exports.defaultOptions = defaultOptions;

function getOptions(opts) {
  var options = {};
  for (var opt in defaultOptions) {
    options[opt] = opts && has(opts, opt) ? opts[opt] : defaultOptions[opt];
  }if (isArray(options.onToken)) {
    (function () {
      var tokens = options.onToken;
      options.onToken = function (token) {
        return tokens.push(token);
      };
    })();
  }
  if (isArray(options.onComment)) options.onComment = pushComment(options, options.onComment);

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
    if (options.locations) comment.loc = new SourceLocation(this, startLoc, endLoc);
    if (options.ranges) comment.range = [start, end];
    array.push(comment);
  };
}

},{"./location":8,"./util":18}],12:[function(_dereq_,module,exports){
"use strict";

var tt = _dereq_("./tokentype").types;

var Parser = _dereq_("./state").Parser;

var lineBreak = _dereq_("./whitespace").lineBreak;

var pp = Parser.prototype;

// ## Parser utilities

// Test whether a statement node is the string literal `"use strict"`.

pp.isUseStrict = function (stmt) {
  return this.options.ecmaVersion >= 5 && stmt.type === "ExpressionStatement" && stmt.expression.type === "Literal" && stmt.expression.value === "use strict";
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
  return this.type === tt.name && this.value === name;
};

// Consumes contextual keyword if possible.

pp.eatContextual = function (name) {
  return this.value === name && this.eat(tt.name);
};

// Asserts that following token is given contextual keyword.

pp.expectContextual = function (name) {
  if (!this.eatContextual(name)) this.unexpected();
};

// Test whether a semicolon can be inserted at the current position.

pp.canInsertSemicolon = function () {
  return this.type === tt.eof || this.type === tt.braceR || lineBreak.test(this.input.slice(this.lastTokEnd, this.start));
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
  if (!this.eat(tt.semi) && !this.insertSemicolon()) this.unexpected();
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

},{"./state":13,"./tokentype":17,"./whitespace":19}],13:[function(_dereq_,module,exports){
"use strict";

exports.Parser = Parser;
exports.__esModule = true;

var _identifier = _dereq_("./identifier");

var reservedWords = _identifier.reservedWords;
var keywords = _identifier.keywords;

var tt = _dereq_("./tokentype").types;

var lineBreak = _dereq_("./whitespace").lineBreak;

function Parser(options, input, startPos) {
  this.options = options;
  this.sourceFile = this.options.sourceFile || null;
  this.isKeyword = keywords[this.options.ecmaVersion >= 6 ? 6 : 5];
  this.isReservedWord = reservedWords[this.options.ecmaVersion];
  this.input = input;

  // Load plugins
  this.loadPlugins(this.options.plugins);

  // Set up token state

  // The current position of the tokenizer in the input.
  if (startPos) {
    this.pos = startPos;
    this.lineStart = Math.max(0, this.input.lastIndexOf("\n", startPos));
    this.curLine = this.input.slice(0, this.lineStart).split(lineBreak).length;
  } else {
    this.pos = this.lineStart = 0;
    this.curLine = 1;
  }

  // Properties of the current token:
  // Its type
  this.type = tt.eof;
  // For tokens that include more information than their type, the value
  this.value = null;
  // Its start and end offset
  this.start = this.end = this.pos;
  // And, if locations are used, the {line, column} object
  // corresponding to those offsets
  this.startLoc = this.endLoc = null;

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

Parser.prototype.extend = function (name, f) {
  this[name] = f(this[name]);
};

// Registered plugins

var plugins = {};

exports.plugins = plugins;
Parser.prototype.loadPlugins = function (plugins) {
  for (var _name in plugins) {
    var plugin = exports.plugins[_name];
    if (!plugin) throw new Error("Plugin '" + _name + "' not found");
    plugin(this, plugins[_name]);
  }
};

},{"./identifier":7,"./tokentype":17,"./whitespace":19}],14:[function(_dereq_,module,exports){
"use strict";

var tt = _dereq_("./tokentype").types;

var Parser = _dereq_("./state").Parser;

var lineBreak = _dereq_("./whitespace").lineBreak;

var pp = Parser.prototype;

// ### Statement parsing

// Parse a program. Initializes the parser, reads any number of
// statements, and wraps them in a Program node.  Optionally takes a
// `program` argument.  If present, the statements will be appended
// to its body instead of creating a new node.

pp.parseTopLevel = function (node) {
  var first = true;
  if (!node.body) node.body = [];
  while (this.type !== tt.eof) {
    var stmt = this.parseStatement(true, true);
    node.body.push(stmt);
    if (first && this.isUseStrict(stmt)) this.setStrict(true);
    first = false;
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
    case tt._break:case tt._continue:
      return this.parseBreakContinueStatement(node, starttype.keyword);
    case tt._debugger:
      return this.parseDebuggerStatement(node);
    case tt._do:
      return this.parseDoStatement(node);
    case tt._for:
      return this.parseForStatement(node);
    case tt._function:
      if (!declaration && this.options.ecmaVersion >= 6) this.unexpected();
      return this.parseFunctionStatement(node);
    case tt._class:
      if (!declaration) this.unexpected();
      return this.parseClass(node, true);
    case tt._if:
      return this.parseIfStatement(node);
    case tt._return:
      return this.parseReturnStatement(node);
    case tt._switch:
      return this.parseSwitchStatement(node);
    case tt._throw:
      return this.parseThrowStatement(node);
    case tt._try:
      return this.parseTryStatement(node);
    case tt._let:case tt._const:
      if (!declaration) this.unexpected(); // NOTE: falls through to _var
    case tt._var:
      return this.parseVarStatement(node, starttype);
    case tt._while:
      return this.parseWhileStatement(node);
    case tt._with:
      return this.parseWithStatement(node);
    case tt.braceL:
      return this.parseBlock();
    case tt.semi:
      return this.parseEmptyStatement(node);
    case tt._export:
    case tt._import:
      if (!this.options.allowImportExportEverywhere) {
        if (!topLevel) this.raise(this.start, "'import' and 'export' may only appear at the top level");
        if (!this.inModule) this.raise(this.start, "'import' and 'export' may appear only with 'sourceType: module'");
      }
      return starttype === tt._import ? this.parseImport(node) : this.parseExport(node);

    // If the statement does not start with a statement keyword or a
    // brace, it's an ExpressionStatement or LabeledStatement. We
    // simply start parsing an expression, and afterwards, if the
    // next token is a colon and the expression was a simple
    // Identifier node, we switch to interpreting it as a label.
    default:
      var maybeName = this.value,
          expr = this.parseExpression();
      if (starttype === tt.name && expr.type === "Identifier" && this.eat(tt.colon)) return this.parseLabeledStatement(node, maybeName, expr);else return this.parseExpressionStatement(node, expr);
  }
};

pp.parseBreakContinueStatement = function (node, keyword) {
  var isBreak = keyword == "break";
  this.next();
  if (this.eat(tt.semi) || this.insertSemicolon()) node.label = null;else if (this.type !== tt.name) this.unexpected();else {
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
  this.expect(tt._while);
  node.test = this.parseParenExpression();
  if (this.options.ecmaVersion >= 6) this.eat(tt.semi);else this.semicolon();
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
  this.expect(tt.parenL);
  if (this.type === tt.semi) return this.parseFor(node, null);
  if (this.type === tt._var || this.type === tt._let || this.type === tt._const) {
    var _init = this.startNode(),
        varKind = this.type;
    this.next();
    this.parseVar(_init, true, varKind);
    this.finishNode(_init, "VariableDeclaration");
    if ((this.type === tt._in || this.options.ecmaVersion >= 6 && this.isContextual("of")) && _init.declarations.length === 1 && !(varKind !== tt._var && _init.declarations[0].init)) return this.parseForIn(node, _init);
    return this.parseFor(node, _init);
  }
  var refShorthandDefaultPos = { start: 0 };
  var init = this.parseExpression(true, refShorthandDefaultPos);
  if (this.type === tt._in || this.options.ecmaVersion >= 6 && this.isContextual("of")) {
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
  node.alternate = this.eat(tt._else) ? this.parseStatement(false) : null;
  return this.finishNode(node, "IfStatement");
};

pp.parseReturnStatement = function (node) {
  if (!this.inFunction && !this.options.allowReturnOutsideFunction) this.raise(this.start, "'return' outside of function");
  this.next();

  // In `return` (and `break`/`continue`), the keywords with
  // optional arguments, we eagerly look for a semicolon or the
  // possibility to insert one.

  if (this.eat(tt.semi) || this.insertSemicolon()) node.argument = null;else {
    node.argument = this.parseExpression();this.semicolon();
  }
  return this.finishNode(node, "ReturnStatement");
};

pp.parseSwitchStatement = function (node) {
  this.next();
  node.discriminant = this.parseParenExpression();
  node.cases = [];
  this.expect(tt.braceL);
  this.labels.push(switchLabel);

  // Statements under must be grouped (by label) in SwitchCase
  // nodes. `cur` is used to keep the node that we are currently
  // adding statements to.

  for (var cur, sawDefault; this.type != tt.braceR;) {
    if (this.type === tt._case || this.type === tt._default) {
      var isCase = this.type === tt._case;
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
      this.expect(tt.colon);
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
  if (lineBreak.test(this.input.slice(this.lastTokEnd, this.start))) this.raise(this.lastTokEnd, "Illegal newline after throw");
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
  if (this.type === tt._catch) {
    var clause = this.startNode();
    this.next();
    this.expect(tt.parenL);
    clause.param = this.parseBindingAtom();
    this.checkLVal(clause.param, true);
    this.expect(tt.parenR);
    clause.guard = null;
    clause.body = this.parseBlock();
    node.handler = this.finishNode(clause, "CatchClause");
  }
  node.guardedHandlers = empty;
  node.finalizer = this.eat(tt._finally) ? this.parseBlock() : null;
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
  }var kind = this.type.isLoop ? "loop" : this.type === tt._switch ? "switch" : null;
  this.labels.push({ name: maybeName, kind: kind });
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
  this.expect(tt.braceL);
  while (!this.eat(tt.braceR)) {
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
  this.expect(tt.semi);
  node.test = this.type === tt.semi ? null : this.parseExpression();
  this.expect(tt.semi);
  node.update = this.type === tt.parenR ? null : this.parseExpression();
  this.expect(tt.parenR);
  node.body = this.parseStatement(false);
  this.labels.pop();
  return this.finishNode(node, "ForStatement");
};

// Parse a `for`/`in` and `for`/`of` loop, which are almost
// same from parser's perspective.

pp.parseForIn = function (node, init) {
  var type = this.type === tt._in ? "ForInStatement" : "ForOfStatement";
  this.next();
  node.left = init;
  node.right = this.parseExpression();
  this.expect(tt.parenR);
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
    if (this.eat(tt.eq)) {
      decl.init = this.parseMaybeAssign(isFor);
    } else if (kind === tt._const && !(this.type === tt._in || this.options.ecmaVersion >= 6 && this.isContextual("of"))) {
      this.unexpected();
    } else if (decl.id.type != "Identifier" && !(isFor && (this.type === tt._in || this.isContextual("of")))) {
      this.raise(this.lastTokEnd, "Complex binding patterns require an initialization value");
    } else {
      decl.init = null;
    }
    node.declarations.push(this.finishNode(decl, "VariableDeclarator"));
    if (!this.eat(tt.comma)) break;
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
  if (this.options.ecmaVersion >= 6) node.generator = this.eat(tt.star);
  if (isStatement || this.type === tt.name) node.id = this.parseIdent();
  this.parseFunctionParams(node);
  this.parseFunctionBody(node, allowExpressionBody);
  return this.finishNode(node, isStatement ? "FunctionDeclaration" : "FunctionExpression");
};

pp.parseFunctionParams = function (node) {
  this.expect(tt.parenL);
  node.params = this.parseBindingList(tt.parenR, false, false);
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
  this.expect(tt.braceL);
  while (!this.eat(tt.braceR)) {
    if (this.eat(tt.semi)) continue;
    var method = this.startNode();
    var isGenerator = this.eat(tt.star);
    var isMaybeStatic = this.type === tt.name && this.value === "static";
    this.parsePropertyName(method);
    method["static"] = isMaybeStatic && this.type !== tt.parenL;
    if (method["static"]) {
      if (isGenerator) this.unexpected();
      isGenerator = this.eat(tt.star);
      this.parsePropertyName(method);
    }
    method.kind = "method";
    if (!method.computed) {
      var key = method.key;

      var isGetSet = false;
      if (!isGenerator && key.type === "Identifier" && this.type !== tt.parenL && (key.name === "get" || key.name === "set")) {
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
  }
  node.body = this.finishNode(classBody, "ClassBody");
  return this.finishNode(node, isStatement ? "ClassDeclaration" : "ClassExpression");
};

pp.parseClassMethod = function (classBody, method, isGenerator) {
  method.value = this.parseMethod(isGenerator);
  classBody.body.push(this.finishNode(method, "MethodDefinition"));
};

pp.parseClassId = function (node, isStatement) {
  node.id = this.type === tt.name ? this.parseIdent() : isStatement ? this.unexpected() : null;
};

pp.parseClassSuper = function (node) {
  node.superClass = this.eat(tt._extends) ? this.parseExprSubscripts() : null;
};

// Parses module export declaration.

pp.parseExport = function (node) {
  this.next();
  // export * from '...'
  if (this.eat(tt.star)) {
    this.expectContextual("from");
    node.source = this.type === tt.string ? this.parseExprAtom() : this.unexpected();
    this.semicolon();
    return this.finishNode(node, "ExportAllDeclaration");
  }
  if (this.eat(tt._default)) {
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
      node.source = this.type === tt.string ? this.parseExprAtom() : this.unexpected();
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
  this.expect(tt.braceL);
  while (!this.eat(tt.braceR)) {
    if (!first) {
      this.expect(tt.comma);
      if (this.afterTrailingComma(tt.braceR)) break;
    } else first = false;

    var node = this.startNode();
    node.local = this.parseIdent(this.type === tt._default);
    node.exported = this.eatContextual("as") ? this.parseIdent(true) : node.local;
    nodes.push(this.finishNode(node, "ExportSpecifier"));
  }
  return nodes;
};

// Parses import declaration.

pp.parseImport = function (node) {
  this.next();
  // import '...'
  if (this.type === tt.string) {
    node.specifiers = empty;
    node.source = this.parseExprAtom();
    node.kind = "";
  } else {
    node.specifiers = this.parseImportSpecifiers();
    this.expectContextual("from");
    node.source = this.type === tt.string ? this.parseExprAtom() : this.unexpected();
  }
  this.semicolon();
  return this.finishNode(node, "ImportDeclaration");
};

// Parses a comma-separated list of module imports.

pp.parseImportSpecifiers = function () {
  var nodes = [],
      first = true;
  if (this.type === tt.name) {
    // import defaultObj, { x, y as z } from '...'
    var node = this.startNode();
    node.local = this.parseIdent();
    this.checkLVal(node.local, true);
    nodes.push(this.finishNode(node, "ImportDefaultSpecifier"));
    if (!this.eat(tt.comma)) return nodes;
  }
  if (this.type === tt.star) {
    var node = this.startNode();
    this.next();
    this.expectContextual("as");
    node.local = this.parseIdent();
    this.checkLVal(node.local, true);
    nodes.push(this.finishNode(node, "ImportNamespaceSpecifier"));
    return nodes;
  }
  this.expect(tt.braceL);
  while (!this.eat(tt.braceR)) {
    if (!first) {
      this.expect(tt.comma);
      if (this.afterTrailingComma(tt.braceR)) break;
    } else first = false;

    var node = this.startNode();
    node.imported = this.parseIdent(true);
    node.local = this.eatContextual("as") ? this.parseIdent() : node.imported;
    this.checkLVal(node.local, true);
    nodes.push(this.finishNode(node, "ImportSpecifier"));
  }
  return nodes;
};

},{"./state":13,"./tokentype":17,"./whitespace":19}],15:[function(_dereq_,module,exports){
"use strict";

var _classCallCheck = function (instance, Constructor) { if (!(instance instanceof Constructor)) { throw new TypeError("Cannot call a class as a function"); } };

exports.__esModule = true;
// The algorithm used to determine whether a regexp can appear at a
// given point in the program is loosely based on sweet.js' approach.
// See https://github.com/mozilla/sweet.js/wiki/design

var Parser = _dereq_("./state").Parser;

var tt = _dereq_("./tokentype").types;

var lineBreak = _dereq_("./whitespace").lineBreak;

var TokContext = exports.TokContext = function TokContext(token, isExpr, preserveSpace, override) {
  _classCallCheck(this, TokContext);

  this.token = token;
  this.isExpr = isExpr;
  this.preserveSpace = preserveSpace;
  this.override = override;
};

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
var pp = Parser.prototype;

pp.initialContext = function () {
  return [types.b_stat];
};

pp.braceIsBlock = function (prevType) {
  var parent = undefined;
  if (prevType === tt.colon && (parent = this.curContext()).token == "{") return !parent.isExpr;
  if (prevType === tt._return) return lineBreak.test(this.input.slice(this.lastTokEnd, this.start));
  if (prevType === tt._else || prevType === tt.semi || prevType === tt.eof) return true;
  if (prevType == tt.braceL) return this.curContext() === types.b_stat;
  return !this.exprAllowed;
};

pp.updateContext = function (prevType) {
  var update = undefined,
      type = this.type;
  if (type.keyword && prevType == tt.dot) this.exprAllowed = false;else if (update = type.updateContext) update.call(this, prevType);else this.exprAllowed = type.beforeExpr;
};

// Token-specific context update code

tt.parenR.updateContext = tt.braceR.updateContext = function () {
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

tt.braceL.updateContext = function (prevType) {
  this.context.push(this.braceIsBlock(prevType) ? types.b_stat : types.b_expr);
  this.exprAllowed = true;
};

tt.dollarBraceL.updateContext = function () {
  this.context.push(types.b_tmpl);
  this.exprAllowed = true;
};

tt.parenL.updateContext = function (prevType) {
  var statementParens = prevType === tt._if || prevType === tt._for || prevType === tt._with || prevType === tt._while;
  this.context.push(statementParens ? types.p_stat : types.p_expr);
  this.exprAllowed = true;
};

tt.incDec.updateContext = function () {};

tt._function.updateContext = function () {
  if (this.curContext() !== types.b_stat) this.context.push(types.f_expr);
  this.exprAllowed = false;
};

tt.backQuote.updateContext = function () {
  if (this.curContext() === types.q_tmpl) this.context.pop();else this.context.push(types.q_tmpl);
  this.exprAllowed = false;
};

// tokExprAllowed stays unchanged

},{"./state":13,"./tokentype":17,"./whitespace":19}],16:[function(_dereq_,module,exports){
"use strict";

var _classCallCheck = function (instance, Constructor) { if (!(instance instanceof Constructor)) { throw new TypeError("Cannot call a class as a function"); } };

exports.__esModule = true;

var _identifier = _dereq_("./identifier");

var isIdentifierStart = _identifier.isIdentifierStart;
var isIdentifierChar = _identifier.isIdentifierChar;

var _tokentype = _dereq_("./tokentype");

var tt = _tokentype.types;
var keywordTypes = _tokentype.keywords;

var Parser = _dereq_("./state").Parser;

var SourceLocation = _dereq_("./location").SourceLocation;

var _whitespace = _dereq_("./whitespace");

var lineBreak = _whitespace.lineBreak;
var lineBreakG = _whitespace.lineBreakG;
var isNewLine = _whitespace.isNewLine;
var nonASCIIwhitespace = _whitespace.nonASCIIwhitespace;

// Object type used to represent tokens. Note that normally, tokens
// simply exist as properties on the parser object. This is only
// used for the onToken callback and the external tokenizer.

var Token = exports.Token = function Token(p) {
  _classCallCheck(this, Token);

  this.type = p.type;
  this.value = p.value;
  this.start = p.start;
  this.end = p.end;
  if (p.options.locations) this.loc = new SourceLocation(p, p.startLoc, p.endLoc);
  if (p.options.ranges) this.range = [p.start, p.end];
};

// ## Tokenizer

var pp = Parser.prototype;

// Are we running under Rhino?
var isRhino = typeof Packages !== "undefined";

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
        done: token.type === tt.eof,
        value: token
      };
    } };
};

// Toggle strict mode. Re-reads the next number or string to please
// pedantic tests (`"use strict"; 010;` should fail).

pp.setStrict = function (strict) {
  this.strict = strict;
  if (this.type !== tt.num && this.type !== tt.string) return;
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
  if (this.pos >= this.input.length) return this.finishToken(tt.eof);

  if (curContext.override) return curContext.override(this);else this.readToken(this.fullCharCodeAtPos());
};

pp.readToken = function (code) {
  // Identifier or keyword. '\uXXXX' sequences are allowed in
  // identifiers, so '\' also dispatches to that.
  if (isIdentifierStart(code, this.options.ecmaVersion >= 6) || code === 92 /* '\' */) return this.readWord();

  return this.getTokenFromCode(code);
};

pp.fullCharCodeAtPos = function () {
  var code = this.input.charCodeAt(this.pos);
  if (code <= 55295 || code >= 57344) return code;
  var next = this.input.charCodeAt(this.pos + 1);
  return (code << 10) + next - 56613888;
};

pp.skipBlockComment = function () {
  var startLoc = this.options.onComment && this.options.locations && this.curPosition();
  var start = this.pos,
      end = this.input.indexOf("*/", this.pos += 2);
  if (end === -1) this.raise(this.pos - 2, "Unterminated comment");
  this.pos = end + 2;
  if (this.options.locations) {
    lineBreakG.lastIndex = start;
    var match = undefined;
    while ((match = lineBreakG.exec(this.input)) && match.index < this.pos) {
      ++this.curLine;
      this.lineStart = match.index + match[0].length;
    }
  }
  if (this.options.onComment) this.options.onComment(true, this.input.slice(start + 2, end), start, this.pos, startLoc, this.options.locations && this.curPosition());
};

pp.skipLineComment = function (startSkip) {
  var start = this.pos;
  var startLoc = this.options.onComment && this.options.locations && this.curPosition();
  var ch = this.input.charCodeAt(this.pos += startSkip);
  while (this.pos < this.input.length && ch !== 10 && ch !== 13 && ch !== 8232 && ch !== 8233) {
    ++this.pos;
    ch = this.input.charCodeAt(this.pos);
  }
  if (this.options.onComment) this.options.onComment(false, this.input.slice(start + startSkip, this.pos), start, this.pos, startLoc, this.options.locations && this.curPosition());
};

// Called at the start of the parse and after every token. Skips
// whitespace and comments, and.

pp.skipSpace = function () {
  while (this.pos < this.input.length) {
    var ch = this.input.charCodeAt(this.pos);
    if (ch === 32) {
      // ' '
      ++this.pos;
    } else if (ch === 13) {
      ++this.pos;
      var next = this.input.charCodeAt(this.pos);
      if (next === 10) {
        ++this.pos;
      }
      if (this.options.locations) {
        ++this.curLine;
        this.lineStart = this.pos;
      }
    } else if (ch === 10 || ch === 8232 || ch === 8233) {
      ++this.pos;
      if (this.options.locations) {
        ++this.curLine;
        this.lineStart = this.pos;
      }
    } else if (ch > 8 && ch < 14) {
      ++this.pos;
    } else if (ch === 47) {
      // '/'
      var next = this.input.charCodeAt(this.pos + 1);
      if (next === 42) {
        // '*'
        this.skipBlockComment();
      } else if (next === 47) {
        // '/'
        this.skipLineComment(2);
      } else break;
    } else if (ch === 160) {
      // '\xa0'
      ++this.pos;
    } else if (ch >= 5760 && nonASCIIwhitespace.test(String.fromCharCode(ch))) {
      ++this.pos;
    } else {
      break;
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
    return this.finishToken(tt.ellipsis);
  } else {
    ++this.pos;
    return this.finishToken(tt.dot);
  }
};

pp.readToken_slash = function () {
  // '/'
  var next = this.input.charCodeAt(this.pos + 1);
  if (this.exprAllowed) {
    ++this.pos;return this.readRegexp();
  }
  if (next === 61) return this.finishOp(tt.assign, 2);
  return this.finishOp(tt.slash, 1);
};

pp.readToken_mult_modulo = function (code) {
  // '%*'
  var next = this.input.charCodeAt(this.pos + 1);
  if (next === 61) return this.finishOp(tt.assign, 2);
  return this.finishOp(code === 42 ? tt.star : tt.modulo, 1);
};

pp.readToken_pipe_amp = function (code) {
  // '|&'
  var next = this.input.charCodeAt(this.pos + 1);
  if (next === code) return this.finishOp(code === 124 ? tt.logicalOR : tt.logicalAND, 2);
  if (next === 61) return this.finishOp(tt.assign, 2);
  return this.finishOp(code === 124 ? tt.bitwiseOR : tt.bitwiseAND, 1);
};

pp.readToken_caret = function () {
  // '^'
  var next = this.input.charCodeAt(this.pos + 1);
  if (next === 61) return this.finishOp(tt.assign, 2);
  return this.finishOp(tt.bitwiseXOR, 1);
};

pp.readToken_plus_min = function (code) {
  // '+-'
  var next = this.input.charCodeAt(this.pos + 1);
  if (next === code) {
    if (next == 45 && this.input.charCodeAt(this.pos + 2) == 62 && lineBreak.test(this.input.slice(this.lastTokEnd, this.pos))) {
      // A `-->` line comment
      this.skipLineComment(3);
      this.skipSpace();
      return this.nextToken();
    }
    return this.finishOp(tt.incDec, 2);
  }
  if (next === 61) return this.finishOp(tt.assign, 2);
  return this.finishOp(tt.plusMin, 1);
};

pp.readToken_lt_gt = function (code) {
  // '<>'
  var next = this.input.charCodeAt(this.pos + 1);
  var size = 1;
  if (next === code) {
    size = code === 62 && this.input.charCodeAt(this.pos + 2) === 62 ? 3 : 2;
    if (this.input.charCodeAt(this.pos + size) === 61) return this.finishOp(tt.assign, size + 1);
    return this.finishOp(tt.bitShift, size);
  }
  if (next == 33 && code == 60 && this.input.charCodeAt(this.pos + 2) == 45 && this.input.charCodeAt(this.pos + 3) == 45) {
    if (this.inModule) this.unexpected();
    // `<!--`, an XML-style comment that should be interpreted as a line comment
    this.skipLineComment(4);
    this.skipSpace();
    return this.nextToken();
  }
  if (next === 61) size = this.input.charCodeAt(this.pos + 2) === 61 ? 3 : 2;
  return this.finishOp(tt.relational, size);
};

pp.readToken_eq_excl = function (code) {
  // '=!'
  var next = this.input.charCodeAt(this.pos + 1);
  if (next === 61) return this.finishOp(tt.equality, this.input.charCodeAt(this.pos + 2) === 61 ? 3 : 2);
  if (code === 61 && next === 62 && this.options.ecmaVersion >= 6) {
    // '=>'
    this.pos += 2;
    return this.finishToken(tt.arrow);
  }
  return this.finishOp(code === 61 ? tt.eq : tt.prefix, 1);
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
      ++this.pos;return this.finishToken(tt.parenL);
    case 41:
      ++this.pos;return this.finishToken(tt.parenR);
    case 59:
      ++this.pos;return this.finishToken(tt.semi);
    case 44:
      ++this.pos;return this.finishToken(tt.comma);
    case 91:
      ++this.pos;return this.finishToken(tt.bracketL);
    case 93:
      ++this.pos;return this.finishToken(tt.bracketR);
    case 123:
      ++this.pos;return this.finishToken(tt.braceL);
    case 125:
      ++this.pos;return this.finishToken(tt.braceR);
    case 58:
      ++this.pos;return this.finishToken(tt.colon);
    case 63:
      ++this.pos;return this.finishToken(tt.question);

    case 96:
      // '`'
      if (this.options.ecmaVersion < 6) break;
      ++this.pos;
      return this.finishToken(tt.backQuote);

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
      return this.finishOp(tt.prefix, 1);
  }

  this.raise(this.pos, "Unexpected character '" + codePointToString(code) + "'");
};

pp.finishOp = function (type, size) {
  var str = this.input.slice(this.pos, this.pos + size);
  this.pos += size;
  return this.finishToken(type, str);
};

var regexpUnicodeSupport = false;
try {
  new RegExp("￿", "u");regexpUnicodeSupport = true;
} catch (e) {}

// Parse a regular expression. Some context-awareness is necessary,
// since a '/' inside a '[]' set does not end the expression.

pp.readRegexp = function () {
  var escaped = undefined,
      inClass = undefined,
      start = this.pos;
  for (;;) {
    if (this.pos >= this.input.length) this.raise(start, "Unterminated regular expression");
    var ch = this.input.charAt(this.pos);
    if (lineBreak.test(ch)) this.raise(start, "Unterminated regular expression");
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
      tmp = tmp.replace(/\\u([a-fA-F0-9]{4})|\\u\{([0-9a-fA-F]+)\}|[\uD800-\uDBFF][\uDC00-\uDFFF]/g, "x");
    }
  }
  // Detect invalid regular expressions.
  var value = null;
  // Rhino's regular expression parser is flaky and throws uncatchable exceptions,
  // so don't do detection if we are running under Rhino
  if (!isRhino) {
    try {
      new RegExp(tmp);
    } catch (e) {
      if (e instanceof SyntaxError) this.raise(start, "Error parsing regular expression: " + e.message);
      this.raise(e);
    }
    // Get a regular expression object for this pattern-flag pair, or `null` in
    // case the current environment doesn't support the flags it uses.
    try {
      value = new RegExp(content, mods);
    } catch (err) {}
  }
  return this.finishToken(tt.regexp, { pattern: content, flags: mods, value: value });
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
  if (isIdentifierStart(this.fullCharCodeAtPos())) this.raise(this.pos, "Identifier directly after number");
  return this.finishToken(tt.num, val);
};

// Read an integer, octal integer, or floating-point number.

pp.readNumber = function (startsWithDot) {
  var start = this.pos,
      isFloat = false,
      octal = this.input.charCodeAt(this.pos) === 48;
  if (!startsWithDot && this.readInt(10) === null) this.raise(start, "Invalid number");
  if (this.input.charCodeAt(this.pos) === 46) {
    ++this.pos;
    this.readInt(10);
    isFloat = true;
  }
  var next = this.input.charCodeAt(this.pos);
  if (next === 69 || next === 101) {
    // 'eE'
    next = this.input.charCodeAt(++this.pos);
    if (next === 43 || next === 45) ++this.pos; // '+-'
    if (this.readInt(10) === null) this.raise(start, "Invalid number");
    isFloat = true;
  }
  if (isIdentifierStart(this.fullCharCodeAtPos())) this.raise(this.pos, "Identifier directly after number");

  var str = this.input.slice(start, this.pos),
      val = undefined;
  if (isFloat) val = parseFloat(str);else if (!octal || str.length === 1) val = parseInt(str, 10);else if (/[89]/.test(str) || this.strict) this.raise(start, "Invalid number");else val = parseInt(str, 8);
  return this.finishToken(tt.num, val);
};

// Read a string value, interpreting backslash-escapes.

pp.readCodePoint = function () {
  var ch = this.input.charCodeAt(this.pos),
      code = undefined;

  if (ch === 123) {
    if (this.options.ecmaVersion < 6) this.unexpected();
    ++this.pos;
    code = this.readHexChar(this.input.indexOf("}", this.pos) - this.pos);
    ++this.pos;
    if (code > 1114111) this.unexpected();
  } else {
    code = this.readHexChar(4);
  }
  return code;
};

function codePointToString(code) {
  // UTF-16 Decoding
  if (code <= 65535) {
    return String.fromCharCode(code);
  }return String.fromCharCode((code - 65536 >> 10) + 55296, (code - 65536 & 1023) + 56320);
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
      out += this.readEscapedChar();
      chunkStart = this.pos;
    } else {
      if (isNewLine(ch)) this.raise(this.start, "Unterminated string constant");
      ++this.pos;
    }
  }
  out += this.input.slice(chunkStart, this.pos++);
  return this.finishToken(tt.string, out);
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
      if (this.pos === this.start && this.type === tt.template) {
        if (ch === 36) {
          this.pos += 2;
          return this.finishToken(tt.dollarBraceL);
        } else {
          ++this.pos;
          return this.finishToken(tt.backQuote);
        }
      }
      out += this.input.slice(chunkStart, this.pos);
      return this.finishToken(tt.template, out);
    }
    if (ch === 92) {
      // '\'
      out += this.input.slice(chunkStart, this.pos);
      out += this.readEscapedChar();
      chunkStart = this.pos;
    } else if (isNewLine(ch)) {
      out += this.input.slice(chunkStart, this.pos);
      ++this.pos;
      if (ch === 13 && this.input.charCodeAt(this.pos) === 10) {
        ++this.pos;
        out += "\n";
      } else {
        out += String.fromCharCode(ch);
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

pp.readEscapedChar = function () {
  var ch = this.input.charCodeAt(++this.pos);
  var octal = /^[0-7]+/.exec(this.input.slice(this.pos, this.pos + 3));
  if (octal) octal = octal[0];
  while (octal && parseInt(octal, 8) > 255) octal = octal.slice(0, -1);
  if (octal === "0") octal = null;
  ++this.pos;
  if (octal) {
    if (this.strict) this.raise(this.pos - 2, "Octal literal in strict mode");
    this.pos += octal.length - 1;
    return String.fromCharCode(parseInt(octal, 8));
  } else {
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
      case 48:
        return "\u0000"; // 0 -> '\0'
      case 13:
        if (this.input.charCodeAt(this.pos) === 10) ++this.pos; // '\r\n'
      case 10:
        // ' \n'
        if (this.options.locations) {
          this.lineStart = this.pos;++this.curLine;
        }
        return "";
      default:
        return String.fromCharCode(ch);
    }
  }
};

// Used to read character escape sequences ('\x', '\u', '\U').

pp.readHexChar = function (len) {
  var n = this.readInt(16, len);
  if (n === null) this.raise(this.start, "Bad character escape sequence");
  return n;
};

// Used to signal to callers of `readWord1` whether the word
// contained any escape sequences. This is needed because words with
// escape sequences must not be interpreted as keywords.

var containsEsc;

// Read an identifier, and return it as a string. Sets `containsEsc`
// to whether the word contained a '\u' escape.
//
// Incrementally adds only escaped chars, adding other chunks as-is
// as a micro-optimization.

pp.readWord1 = function () {
  containsEsc = false;
  var word = "",
      first = true,
      chunkStart = this.pos;
  var astral = this.options.ecmaVersion >= 6;
  while (this.pos < this.input.length) {
    var ch = this.fullCharCodeAtPos();
    if (isIdentifierChar(ch, astral)) {
      this.pos += ch <= 65535 ? 1 : 2;
    } else if (ch === 92) {
      // "\"
      containsEsc = true;
      word += this.input.slice(chunkStart, this.pos);
      var escStart = this.pos;
      if (this.input.charCodeAt(++this.pos) != 117) // "u"
        this.raise(this.pos, "Expecting Unicode escape sequence \\uXXXX");
      ++this.pos;
      var esc = this.readCodePoint();
      if (!(first ? isIdentifierStart : isIdentifierChar)(esc, astral)) this.raise(escStart, "Invalid Unicode escape");
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
  var type = tt.name;
  if ((this.options.ecmaVersion >= 6 || !containsEsc) && this.isKeyword(word)) type = keywordTypes[word];
  return this.finishToken(type, word);
};

},{"./identifier":7,"./location":8,"./state":13,"./tokentype":17,"./whitespace":19}],17:[function(_dereq_,module,exports){
"use strict";

var _classCallCheck = function (instance, Constructor) { if (!(instance instanceof Constructor)) { throw new TypeError("Cannot call a class as a function"); } };

exports.__esModule = true;
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

var TokenType = exports.TokenType = function TokenType(label) {
  var conf = arguments[1] === undefined ? {} : arguments[1];

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
  var options = arguments[1] === undefined ? {} : arguments[1];

  options.keyword = name;
  keywords[name] = types["_" + name] = new TokenType(name, options);
}

kw("break");
kw("case", beforeExpr);
kw("catch");
kw("continue");
kw("debugger");
kw("default");
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

},{}],18:[function(_dereq_,module,exports){
"use strict";

exports.isArray = isArray;

// Checks if an object has a property.

exports.has = has;
exports.__esModule = true;

function isArray(obj) {
  return Object.prototype.toString.call(obj) === "[object Array]";
}

function has(obj, propName) {
  return Object.prototype.hasOwnProperty.call(obj, propName);
}

},{}],19:[function(_dereq_,module,exports){
"use strict";

exports.isNewLine = isNewLine;
exports.__esModule = true;
// Matches a whole line break (where CRLF is considered a single
// line break). Used to count lines.

var lineBreak = /\r\n?|\n|\u2028|\u2029/;
exports.lineBreak = lineBreak;
var lineBreakG = new RegExp(lineBreak.source, "g");

exports.lineBreakG = lineBreakG;

function isNewLine(code) {
  return code === 10 || code === 13 || code === 8232 || code == 8233;
}

var nonASCIIwhitespace = /[\u1680\u180e\u2000-\u200a\u202f\u205f\u3000\ufeff]/;
exports.nonASCIIwhitespace = nonASCIIwhitespace;

},{}]},{},[1])(1)
});
}).call(this,typeof global !== "undefined" ? global : typeof self !== "undefined" ? self : typeof window !== "undefined" ? window : {})

},{}],11:[function(require,module,exports){
(function (global){
(function(f){if(typeof exports==="object"&&typeof module!=="undefined"){module.exports=f()}else if(typeof define==="function"&&define.amd){define([],f)}else{var g;if(typeof window!=="undefined"){g=window}else if(typeof global!=="undefined"){g=global}else if(typeof self!=="undefined"){g=self}else{g=this}(g.acorn || (g.acorn = {})).walk = f()}})(function(){var define,module,exports;return (function e(t,n,r){function s(o,u){if(!n[o]){if(!t[o]){var a=typeof require=="function"&&require;if(!u&&a)return a(o,!0);if(i)return i(o,!0);var f=new Error("Cannot find module '"+o+"'");throw f.code="MODULE_NOT_FOUND",f}var l=n[o]={exports:{}};t[o][0].call(l.exports,function(e){var n=t[o][1][e];return s(n?n:e)},l,l.exports,e,t,n,r)}return n[o].exports}var i=typeof require=="function"&&require;for(var o=0;o<r.length;o++)s(r[o]);return s})({1:[function(_dereq_,module,exports){
"use strict";

var _classCallCheck = function (instance, Constructor) { if (!(instance instanceof Constructor)) { throw new TypeError("Cannot call a class as a function"); } };

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

exports.simple = simple;

// An ancestor walk builds up an array of ancestor nodes (including
// the current node) and passes them to the callback as the state parameter.
exports.ancestor = ancestor;

// A recursive walk is one where your functions override the default
// walkers. They can modify and replace the state parameter that's
// threaded through the walk, and can opt how and whether to walk
// their child nodes (by calling their third argument on these
// nodes).
exports.recursive = recursive;

// Find a node with a given start, end, and type (all are optional,
// null can be used as wildcard). Returns a {node, state} object, or
// undefined when it doesn't find a matching node.
exports.findNodeAt = findNodeAt;

// Find the innermost node of a given type that contains the given
// position. Interface similar to findNodeAt.
exports.findNodeAround = findNodeAround;

// Find the outermost matching node after a given position.
exports.findNodeAfter = findNodeAfter;

// Find the outermost matching node before a given position.
exports.findNodeBefore = findNodeBefore;

// Used to create a custom walker. Will fill in all missing node
// type properties with the defaults.
exports.make = make;
exports.__esModule = true;

function simple(node, visitors, base, state) {
  if (!base) base = exports.base;(function c(node, st, override) {
    var type = override || node.type,
        found = visitors[type];
    base[type](node, st, c);
    if (found) found(node, st);
  })(node, state);
}

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

function recursive(node, state, funcs, base) {
  var visitor = funcs ? exports.make(funcs, base) : base;(function c(node, st, override) {
    visitor[override || node.type](node, st, c);
  })(node, state);
}

function makeTest(test) {
  if (typeof test == "string") {
    return function (type) {
      return type == test;
    };
  } else if (!test) {
    return function () {
      return true;
    };
  } else {
    return test;
  }
}

var Found = function Found(node, state) {
  _classCallCheck(this, Found);

  this.node = node;this.state = state;
};

function findNodeAt(node, start, end, test, base, state) {
  test = makeTest(test);
  if (!base) base = exports.base;
  try {
    ;(function c(node, st, override) {
      var type = override || node.type;
      if ((start == null || node.start <= start) && (end == null || node.end >= end)) base[type](node, st, c);
      if (test(type, node) && (start == null || node.start == start) && (end == null || node.end == end)) throw new Found(node, st);
    })(node, state);
  } catch (e) {
    if (e instanceof Found) {
      return e;
    }throw e;
  }
}

function findNodeAround(node, pos, test, base, state) {
  test = makeTest(test);
  if (!base) base = exports.base;
  try {
    ;(function c(node, st, override) {
      var type = override || node.type;
      if (node.start > pos || node.end < pos) {
        return;
      }base[type](node, st, c);
      if (test(type, node)) throw new Found(node, st);
    })(node, state);
  } catch (e) {
    if (e instanceof Found) {
      return e;
    }throw e;
  }
}

function findNodeAfter(node, pos, test, base, state) {
  test = makeTest(test);
  if (!base) base = exports.base;
  try {
    ;(function c(node, st, override) {
      if (node.end < pos) {
        return;
      }var type = override || node.type;
      if (node.start >= pos && test(type, node)) throw new Found(node, st);
      base[type](node, st, c);
    })(node, state);
  } catch (e) {
    if (e instanceof Found) {
      return e;
    }throw e;
  }
}

function findNodeBefore(node, pos, test, base, state) {
  test = makeTest(test);
  if (!base) base = exports.base;
  var max = undefined;(function c(node, st, override) {
    if (node.start > pos) {
      return;
    }var type = override || node.type;
    if (node.end <= pos && (!max || max.node.end < node.end) && test(type, node)) max = new Found(node, st);
    base[type](node, st, c);
  })(node, state);
  return max;
}

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
base.ThrowStatement = base.SpreadElement = base.RestElement = function (node, st, c) {
  return c(node.argument, st, "Expression");
};
base.TryStatement = function (node, st, c) {
  c(node.block, st, "Statement");
  if (node.handler) c(node.handler.body, st, "ScopeBody");
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
    var decl = node.declarations[i];
    if (decl.init) c(decl.init, st, "Expression");
  }
};

base.Function = function (node, st, c) {
  return c(node.body, st, "ScopeBody");
};
base.ScopeBody = function (node, st, c) {
  return c(node, st, "Statement");
};

base.Expression = skipThrough;
base.ThisExpression = base.Super = base.MetaProperty = ignore;
base.ArrayExpression = base.ArrayPattern = function (node, st, c) {
  for (var i = 0; i < node.elements.length; ++i) {
    var elt = node.elements[i];
    if (elt) c(elt, st, "Expression");
  }
};
base.ObjectExpression = base.ObjectPattern = function (node, st, c) {
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
base.BinaryExpression = base.AssignmentExpression = base.AssignmentPattern = base.LogicalExpression = function (node, st, c) {
  c(node.left, st, "Expression");
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
  return c(node.declaration, st);
};
base.ImportDeclaration = function (node, st, c) {
  for (var i = 0; i < node.specifiers.length; i++) {
    c(node.specifiers[i], st);
  }
};
base.ImportSpecifier = base.ImportDefaultSpecifier = base.ImportNamespaceSpecifier = base.Identifier = base.Literal = ignore;

base.TaggedTemplateExpression = function (node, st, c) {
  c(node.tag, st, "Expression");
  c(node.quasi, st);
};
base.ClassDeclaration = base.ClassExpression = function (node, st, c) {
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

},{}],12:[function(require,module,exports){

},{}],13:[function(require,module,exports){
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

},{}],14:[function(require,module,exports){
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

},{}],15:[function(require,module,exports){
module.exports = function isBuffer(arg) {
  return arg && typeof arg === 'object'
    && typeof arg.copy === 'function'
    && typeof arg.fill === 'function'
    && typeof arg.readUInt8 === 'function';
}
},{}],16:[function(require,module,exports){
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

},{"./support/isBuffer":15,"_process":14,"inherits":13}]},{},[7])(7)
});
//# sourceMappingURL=data:application/json;charset:utf-8;base64,eyJ2ZXJzaW9uIjozLCJzb3VyY2VzIjpbIm5vZGVfbW9kdWxlcy9icm93c2VyaWZ5L25vZGVfbW9kdWxlcy9icm93c2VyLXBhY2svX3ByZWx1ZGUuanMiLCIvaG9tZS9zd2tpbS9XZWJzdG9ybVByb2plY3RzL3lhdGVybi9saWIvYXV4LmpzIiwiL2hvbWUvc3draW0vV2Vic3Rvcm1Qcm9qZWN0cy95YXRlcm4vbGliL2NvbnN0cmFpbnQvY0dlbi5qcyIsIi9ob21lL3N3a2ltL1dlYnN0b3JtUHJvamVjdHMveWF0ZXJuL2xpYi9jb25zdHJhaW50L2NvbnN0cmFpbnRzLmpzIiwiL2hvbWUvc3draW0vV2Vic3Rvcm1Qcm9qZWN0cy95YXRlcm4vbGliL2RvbWFpbnMvY29udGV4dC5qcyIsIi9ob21lL3N3a2ltL1dlYnN0b3JtUHJvamVjdHMveWF0ZXJuL2xpYi9kb21haW5zL3N0YXR1cy5qcyIsIi9ob21lL3N3a2ltL1dlYnN0b3JtUHJvamVjdHMveWF0ZXJuL2xpYi9kb21haW5zL3R5cGVzLmpzIiwiL2hvbWUvc3draW0vV2Vic3Rvcm1Qcm9qZWN0cy95YXRlcm4vbGliL2luZmVyLmpzIiwiL2hvbWUvc3draW0vV2Vic3Rvcm1Qcm9qZWN0cy95YXRlcm4vbGliL3ZhckJsb2NrLmpzIiwiL2hvbWUvc3draW0vV2Vic3Rvcm1Qcm9qZWN0cy95YXRlcm4vbGliL3ZhcnJlZnMuanMiLCJub2RlX21vZHVsZXMvYWNvcm4vZGlzdC9hY29ybi5qcyIsIm5vZGVfbW9kdWxlcy9hY29ybi9kaXN0L3dhbGsuanMiLCJub2RlX21vZHVsZXMvYnJvd3NlcmlmeS9saWIvX2VtcHR5LmpzIiwibm9kZV9tb2R1bGVzL2Jyb3dzZXJpZnkvbm9kZV9tb2R1bGVzL2luaGVyaXRzL2luaGVyaXRzX2Jyb3dzZXIuanMiLCJub2RlX21vZHVsZXMvYnJvd3NlcmlmeS9ub2RlX21vZHVsZXMvcHJvY2Vzcy9icm93c2VyLmpzIiwibm9kZV9tb2R1bGVzL2Jyb3dzZXJpZnkvbm9kZV9tb2R1bGVzL3V0aWwvc3VwcG9ydC9pc0J1ZmZlckJyb3dzZXIuanMiLCJub2RlX21vZHVsZXMvYnJvd3NlcmlmeS9ub2RlX21vZHVsZXMvdXRpbC91dGlsLmpzIl0sIm5hbWVzIjpbXSwibWFwcGluZ3MiOiJBQUFBOzs7QUNBQSxJQUFJLElBQUksR0FBRyxPQUFPLENBQUMsTUFBTSxDQUFDLENBQUM7O0FBRTNCLFNBQVMsV0FBVyxDQUFDLEdBQUcsRUFBRSxRQUFRLEVBQUU7QUFDaEMsUUFBSSxRQUFRLEdBQUcsRUFBRSxDQUFDOztBQUVsQixRQUFJLEdBQUcsR0FBRyxRQUFRLEtBQUssU0FBUyxHQUFHLENBQUMsR0FBRyxRQUFRLENBQUM7O0FBRWhELGFBQVMsUUFBUSxDQUFDLElBQUksRUFBRTtBQUNwQixZQUFJLENBQUMsUUFBUSxDQUFDLEdBQUcsR0FBRyxDQUFDO0FBQ3JCLGdCQUFRLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQyxDQUFDO0FBQ3BCLFdBQUcsRUFBRSxDQUFDO0tBQ1Q7OztBQUdELGFBQVMsaUJBQWlCLENBQUMsSUFBSSxFQUFFO0FBQzdCLFlBQUksSUFBSSxJQUFJLElBQUksQ0FBQyxjQUFjLENBQUMsTUFBTSxDQUFDLEVBQUU7QUFDckMsb0JBQVEsQ0FBQyxJQUFJLENBQUMsQ0FBQztTQUNsQjtBQUNELFlBQUksSUFBSSxJQUFJLE9BQU8sSUFBSSxLQUFLLFFBQVEsRUFBRTtBQUNsQyxpQkFBSyxJQUFJLENBQUMsSUFBSSxJQUFJLEVBQUU7QUFDaEIsaUNBQWlCLENBQUMsSUFBSSxDQUFDLENBQUMsQ0FBQyxDQUFDLENBQUM7YUFDOUI7U0FDSjtLQUNKOztBQUVELHFCQUFpQixDQUFDLEdBQUcsQ0FBQyxDQUFDOztBQUV2QixXQUFPLFFBQVEsQ0FBQztDQUNuQjs7QUFFRCxTQUFTLFlBQVksQ0FBQyxHQUFHLEVBQUU7QUFDdkIsV0FBTyxDQUFDLEdBQUcsQ0FBQyxJQUFJLENBQUMsT0FBTyxDQUFDLEdBQUcsRUFBRSxFQUFDLEtBQUssRUFBRSxJQUFJLEVBQUMsQ0FBQyxDQUFDLENBQUM7Q0FDakQ7O0FBRUQsT0FBTyxDQUFDLFdB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QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7Ozs7O0FDNzZIQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7Ozs7QUNyVkE7O0FDQUE7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBOztBQ3ZCQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTs7QUMxRkE7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBOzs7QUNMQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBIiwiZmlsZSI6ImdlbmVyYXRlZC5qcyIsInNvdXJjZVJvb3QiOiIiLCJzb3VyY2VzQ29udGVudCI6WyIoZnVuY3Rpb24gZSh0LG4scil7ZnVuY3Rpb24gcyhvLHUpe2lmKCFuW29dKXtpZighdFtvXSl7dmFyIGE9dHlwZW9mIHJlcXVpcmU9PVwiZnVuY3Rpb25cIiYmcmVxdWlyZTtpZighdSYmYSlyZXR1cm4gYShvLCEwKTtpZihpKXJldHVybiBpKG8sITApO3ZhciBmPW5ldyBFcnJvcihcIkNhbm5vdCBmaW5kIG1vZHVsZSAnXCIrbytcIidcIik7dGhyb3cgZi5jb2RlPVwiTU9EVUxFX05PVF9GT1VORFwiLGZ9dmFyIGw9bltvXT17ZXhwb3J0czp7fX07dFtvXVswXS5jYWxsKGwuZXhwb3J0cyxmdW5jdGlvbihlKXt2YXIgbj10W29dWzFdW2VdO3JldHVybiBzKG4/bjplKX0sbCxsLmV4cG9ydHMsZSx0LG4scil9cmV0dXJuIG5bb10uZXhwb3J0c312YXIgaT10eXBlb2YgcmVxdWlyZT09XCJmdW5jdGlvblwiJiZyZXF1aXJlO2Zvcih2YXIgbz0wO288ci5sZW5ndGg7bysrKXMocltvXSk7cmV0dXJuIHN9KSIsInZhciB1dGlsID0gcmVxdWlyZSgndXRpbCcpO1xuXG5mdW5jdGlvbiBnZXROb2RlTGlzdChhc3QsIHN0YXJ0TnVtKSB7XG4gICAgdmFyIG5vZGVMaXN0ID0gW107XG5cbiAgICB2YXIgbnVtID0gc3RhcnROdW0gPT09IHVuZGVmaW5lZCA/IDAgOiBzdGFydE51bTtcblxuICAgIGZ1bmN0aW9uIGFzc2lnbklkKG5vZGUpIHtcbiAgICAgICAgbm9kZVsnQGxhYmVsJ10gPSBudW07XG4gICAgICAgIG5vZGVMaXN0LnB1c2gobm9kZSk7XG4gICAgICAgIG51bSsrO1xuICAgIH1cblxuICAgIC8vIExhYmVsIGV2ZXJ5IEFTVCBub2RlIHdpdGggcHJvcGVydHkgJ3R5cGUnXG4gICAgZnVuY3Rpb24gbGFiZWxOb2RlV2l0aFR5cGUobm9kZSkge1xuICAgICAgICBpZiAobm9kZSAmJiBub2RlLmhhc093blByb3BlcnR5KCd0eXBlJykpIHtcbiAgICAgICAgICAgIGFzc2lnbklkKG5vZGUpO1xuICAgICAgICB9XG4gICAgICAgIGlmIChub2RlICYmIHR5cGVvZiBub2RlID09PSAnb2JqZWN0Jykge1xuICAgICAgICAgICAgZm9yICh2YXIgcCBpbiBub2RlKSB7XG4gICAgICAgICAgICAgICAgbGFiZWxOb2RlV2l0aFR5cGUobm9kZVtwXSk7XG4gICAgICAgICAgICB9XG4gICAgICAgIH1cbiAgICB9XG5cbiAgICBsYWJlbE5vZGVXaXRoVHlwZShhc3QpO1xuXG4gICAgcmV0dXJuIG5vZGVMaXN0O1xufVxuXG5mdW5jdGlvbiBzaG93VW5mb2xkZWQob2JqKSB7XG4gICAgY29uc29sZS5sb2codXRpbC5pbnNwZWN0KG9iaiwge2RlcHRoOiBudWxsfSkpO1xufVxuXG5leHBvcnRzLmdldE5vZGVMaXN0ID0gZ2V0Tm9kZUxpc3Q7XG5leHBvcnRzLnNob3dVbmZvbGRlZCA9IHNob3dVbmZvbGRlZDtcbiIsIid1c2Ugc3RyaWN0JztcblxuY29uc3QgdHlwZXMgPSByZXF1aXJlKCcuLi9kb21haW5zL3R5cGVzJyk7XG5jb25zdCB3YWxrID0gcmVxdWlyZSgnYWNvcm4vZGlzdC93YWxrJyk7XG5jb25zdCBzdGF0dXMgPSByZXF1aXJlKCcuLi9kb21haW5zL3N0YXR1cycpO1xuY29uc3QgY3N0ciA9IHJlcXVpcmUoJy4vY29uc3RyYWludHMnKTtcblxuLy8gYXJndW1lbnRzIGFyZSBcIiBvbGRTdGF0dXMgKCwgbmFtZSwgdmFsKSogXCJcbmZ1bmN0aW9uIGNoYW5nZWRTdGF0dXMob2xkU3RhdHVzKSB7XG4gICAgY29uc3QgbmV3U3RhdHVzID0gbmV3IHN0YXR1cy5TdGF0dXM7XG4gICAgZm9yIChsZXQgaSA9IDE7IGkgPCBhcmd1bWVudHMubGVuZ3RoOyBpID0gaSArIDIpXG4gICAgICAgIG5ld1N0YXR1c1thcmd1bWVudHNbaV1dID0gYXJndW1lbnRzW2krMV07XG5cbiAgICBmb3IgKGxldCBwIGluIG9sZFN0YXR1cykge1xuICAgICAgICBpZiAobmV3U3RhdHVzW3BdID09PSB1bmRlZmluZWQpXG4gICAgICAgICAgICBuZXdTdGF0dXNbcF0gPSBvbGRTdGF0dXNbcF07XG4gICAgfVxuICAgIHJldHVybiBuZXdTdGF0dXM7XG59XG5cbi8vIHJldHVybnMgW2FjY2VzcyB0eXBlLCBwcm9wIHZhbHVlXVxuZnVuY3Rpb24gcHJvcEFjY2Vzcyhub2RlKSB7XG4gICAgY29uc3QgcHJvcCA9IG5vZGUucHJvcGVydHk7XG4gICAgaWYgKCFub2RlLmNvbXB1dGVkKSB7XG4gICAgICAgIHJldHVybiBbJ2RvdEFjY2VzcycsIHByb3AubmFtZV07XG4gICAgfVxuICAgIGlmIChwcm9wLnR5cGUgPT09ICdMaXRlcmFsJykge1xuICAgICAgICBpZiAodHlwZW9mIHByb3AudmFsdWUgPT09ICdzdHJpbmcnKVxuICAgICAgICAgICAgcmV0dXJuIFsnc3RyaW5nTGl0ZXJhbCcsIHByb3AudmFsdWVdO1xuICAgICAgICBpZiAodHlwZW9mIHByb3AudmFsdWUgPT09ICdudW1iZXInKVxuICAgICAgICAgICAgLy8gY29udmVydCBudW1iZXIgdG8gc3RyaW5nXG4gICAgICAgICAgICByZXR1cm4gWydudW1iZXJMaXRlcmFsJywgcHJvcC52YWx1ZSArICcnXTtcbiAgICB9XG4gICAgcmV0dXJuIFtcImNvbXB1dGVkXCIsIG51bGxdO1xufVxuXG5mdW5jdGlvbiB1bm9wUmVzdWx0VHlwZShvcCkge1xuICAgIHN3aXRjaCAob3ApIHtcbiAgICAgICAgY2FzZSAnKyc6IGNhc2UgJy0nOiBjYXNlICd+JzpcbiAgICAgICAgICAgIHJldHVybiB0eXBlcy5QcmltTnVtYmVyO1xuICAgICAgICBjYXNlICchJzpcbiAgICAgICAgICAgIHJldHVybiB0eXBlcy5QcmltQm9vbGVhbjtcbiAgICAgICAgY2FzZSAndHlwZW9mJzpcbiAgICAgICAgICAgIHJldHVybiB0eXBlcy5QcmltU3RyaW5nO1xuICAgICAgICBjYXNlICd2b2lkJzogY2FzZSAnZGVsZXRlJzpcbiAgICAgICAgICAgIHJldHVybiBudWxsO1xuICAgIH1cbn1cblxuZnVuY3Rpb24gYmlub3BJc0Jvb2xlYW4ob3ApIHtcbiAgICBzd2l0Y2ggKG9wKSB7XG4gICAgICAgIGNhc2UgJz09JzogY2FzZSAnIT0nOiBjYXNlICc9PT0nOiBjYXNlICchPT0nOlxuICAgICAgICBjYXNlICc8JzogY2FzZSAnPic6IGNhc2UgJz49JzogY2FzZSAnPD0nOlxuICAgICAgICBjYXNlICdpbic6IGNhc2UgJ2luc3RhbmNlb2YnOlxuICAgICAgICAgICAgcmV0dXJuIHRydWU7XG4gICAgfVxuICAgIHJldHVybiBmYWxzZTtcbn1cblxuZnVuY3Rpb24gcmVhZE1lbWJlcihub2RlLCBjdXJTdGF0dXMsIGMpIHtcbiAgICBjb25zdCByZXQgPSBuZXcgdHlwZXMuQVZhbDtcbiAgICBjb25zdCBvYmpBVmFsID0gYyhub2RlLm9iamVjdCwgY3VyU3RhdHVzLCB1bmRlZmluZWQpO1xuICAgIGlmIChub2RlLnByb3BlcnR5LnR5cGUgIT09ICdJZGVudGlmaWVyJykge1xuICAgICAgICAvLyByZXR1cm4gZnJvbSBwcm9wZXJ0eSBpcyBpZ25vcmVkXG4gICAgICAgIGMobm9kZS5wcm9wZXJ0eSwgY3VyU3RhdHVzLCB1bmRlZmluZWQpO1xuICAgIH1cbiAgICBjb25zdCBwcm9wQWNjID0gcHJvcEFjY2Vzcyhub2RlKTtcblxuICAgIGNvbnN0cmFpbnRzLnB1c2goe09CSjogb2JqQVZhbCxcbiAgICAgICAgICAgICAgICAgICAgICBQUk9QOiBwcm9wQWNjWzFdLFxuICAgICAgICAgICAgICAgICAgICAgIFJFQURfVE86IHJldH0pO1xuICAgIG9iakFWYWwucHJvcGFnYXRlKG5ldyBjc3RyLlJlYWRQcm9wKHByb3BBY2NbMV0sIHJldCkpO1xuXG4gICAgLy8gcmV0dXJucyBBVmFsIGZvciByZWNlaXZlciBhbmQgcmVhZCBtZW1iZXJcbiAgICByZXR1cm4gW29iakFWYWwsIHJldF07XG59XG4vLyBUbyBwcmV2ZW50IHJlY3Vyc2lvbixcbi8vIHdlIHJlbWVtYmVyIHRoZSBzdGF0dXMgdXNlZCBpbiBhZGRDb25zdHJhaW50c1xuY29uc3QgdmlzaXRlZFN0YXR1cyA9IFtdO1xuY29uc3QgY29uc3RyYWludHMgPSBbXTtcbmZ1bmN0aW9uIGNsZWFyQ29uc3RyYWludHMoKSB7XG4gICAgdmlzaXRlZFN0YXR1cy5sZW5ndGggPSAwO1xuICAgIGNvbnN0cmFpbnRzLmxlbmd0aCA9IDA7XG59XG5cbmxldCBydENYO1xuZnVuY3Rpb24gYWRkQ29uc3RyYWludHMoYXN0LCBpbml0U3RhdHVzLCBuZXdSdENYKSB7XG5cbiAgICAvLyBzZXQgcnRDWFxuICAgIHJ0Q1ggPSBuZXdSdENYIHx8IHJ0Q1g7XG5cbiAgICAvLyBDaGVjayB3aGV0aGVyIHdlIGhhdmUgcHJvY2Vzc2VkICdpbml0U3RhdHVzJyBiZWZvcmVcbiAgICBmb3IgKGxldCBpPTA7IGkgPCB2aXNpdGVkU3RhdHVzLmxlbmd0aDsgaSsrKSB7XG4gICAgICAgIGlmIChpbml0U3RhdHVzLmVxdWFscyh2aXNpdGVkU3RhdHVzW2ldKSkge1xuICAgICAgICAgICAgIC8vIElmIHNvLCBkbyBub3RoaW5nXG4gICAgICAgICAgICAgLy8gc2lnbmlmeWluZyB3ZSBkaWRuJ3QgYWRkIGNvbnN0cmFpbnRzXG4gICAgICAgICAgICAgcmV0dXJuIGZhbHNlO1xuICAgICAgICAgfVxuICAgIH1cbiAgICAvLyBJZiB0aGUgaW5pdFN0YXR1cyBpcyBuZXcsIHB1c2ggaXQuXG4gICAgLy8gV2UgZG8gbm90IHJlY29yZCBhc3Qgc2luY2UgYXN0IG5vZGUgZGVwZW5kcyBvbiB0aGUgc3RhdHVzXG4gICAgdmlzaXRlZFN0YXR1cy5wdXNoKGluaXRTdGF0dXMpO1xuXG4gICAgLy8gY29uc3RyYWludCBnZW5lcmF0aW5nIHdhbGtlciBmb3IgZXhwcmVzc2lvbnNcbiAgICBjb25zdCBjb25zdHJhaW50R2VuZXJhdG9yID0gd2Fsay5tYWtlKHtcblxuICAgICAgICBJZGVudGlmaWVyOiBmdW5jdGlvbiAobm9kZSwgY3VyU3RhdHVzLCBjKSB7XG4gICAgICAgICAgICByZXR1cm4gY3VyU3RhdHVzLnNjLmdldEFWYWxPZihub2RlLm5hbWUpO1xuICAgICAgICB9LFxuXG4gICAgICAgIFRoaXNFeHByZXNzaW9uOiBmdW5jdGlvbiAobm9kZSwgY3VyU3RhdHVzLCBjKSB7XG4gICAgICAgICAgICByZXR1cm4gY3VyU3RhdHVzLnNlbGY7XG4gICAgICAgIH0sXG5cbiAgICAgICAgTGl0ZXJhbDogZnVuY3Rpb24gKG5vZGUsIGN1clN0YXR1cywgYykge1xuICAgICAgICAgICAgY29uc3QgcmVzID0gbmV3IHR5cGVzLkFWYWw7XG4gICAgICAgICAgICBpZiAobm9kZS5yZWdleCkge1xuICAgICAgICAgICAgICAgIC8vIG5vdCBpbXBsZW1lbnRlZCB5ZXRcbiAgICAgICAgICAgICAgICAvLyB0aHJvdyBuZXcgRXJyb3IoJ3JlZ2V4IGxpdGVyYWwgaXMgbm90IGltcGxlbWVudGVkIHlldCcpO1xuICAgICAgICAgICAgICAgIHJldHVybiByZXM7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBzd2l0Y2ggKHR5cGVvZiBub2RlLnZhbHVlKSB7XG4gICAgICAgICAgICBjYXNlICdudW1iZXInOlxuICAgICAgICAgICAgICAgIGNvbnN0cmFpbnRzLnB1c2goe1RZUEU6IHR5cGVzLlByaW1OdW1iZXIsXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgSU5DTF9TRVQ6IHJlc30pO1xuICAgICAgICAgICAgICAgIHJlcy5hZGRUeXBlKHR5cGVzLlByaW1OdW1iZXIpO1xuICAgICAgICAgICAgICAgIGJyZWFrO1xuICAgICAgICAgICAgY2FzZSAnc3RyaW5nJzpcbiAgICAgICAgICAgICAgICBjb25zdHJhaW50cy5wdXNoKHtUWVBFOiB0eXBlcy5QcmltU3RyaW5nLFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIElOQ0xfU0VUOiByZXN9KTtcbiAgICAgICAgICAgICAgICByZXMuYWRkVHlwZSh0eXBlcy5QcmltU3RyaW5nKTtcbiAgICAgICAgICAgICAgICBicmVhaztcbiAgICAgICAgICAgIGNhc2UgJ2Jvb2xlYW4nOlxuICAgICAgICAgICAgICAgIGNvbnN0cmFpbnRzLnB1c2goe1RZUEU6IHR5cGVzLlByaW1Cb29sZWFuLFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIElOQ0xfU0VUOiByZXN9KTtcbiAgICAgICAgICAgICAgICByZXMuYWRkVHlwZSh0eXBlcy5QcmltQm9vbGVhbik7XG4gICAgICAgICAgICAgICAgYnJlYWs7XG4gICAgICAgICAgICBjYXNlICdvYmplY3QnOlxuICAgICAgICAgICAgICAgIC8vIEkgZ3Vlc3M6IExpdGVyYWwgJiYgb2JqZWN0ID09PiBub2RlLnZhbHVlID09IG51bGxcbiAgICAgICAgICAgICAgICAvLyBudWxsIGlzIGlnbm9yZWQsIHNvIG5vdGhpbmcgdG8gYWRkXG4gICAgICAgICAgICAgICAgYnJlYWs7XG4gICAgICAgICAgICBjYXNlICdmdW5jdGlvbic6XG4gICAgICAgICAgICAgICAgdGhyb3cgbmV3IEVycm9yKCdJIGd1ZXNzIGZ1bmN0aW9uIGlzIGltcG9zc2libGUgaGVyZS4nKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIHJldHVybiByZXM7XG4gICAgICAgIH0sXG5cbiAgICAgICAgQXNzaWdubWVudEV4cHJlc3Npb246IGZ1bmN0aW9uIChub2RlLCBjdXJTdGF0dXMsIGMpIHtcbiAgICAgICAgICAgIGNvbnN0IHJoc0FWYWwgPSBjKG5vZGUucmlnaHQsIGN1clN0YXR1cywgdW5kZWZpbmVkKTtcbiAgICAgICAgICAgIGlmIChub2RlLmxlZnQudHlwZSAhPT0gJ01lbWJlckV4cHJlc3Npb24nKSB7XG4gICAgICAgICAgICAgICAgLy8gTEhTIGlzIGEgc2ltcGxlIHZhcmlhYmxlLlxuICAgICAgICAgICAgICAgIGNvbnN0IHZhck5hbWUgPSBub2RlLmxlZnQubmFtZTtcbiAgICAgICAgICAgICAgICBjb25zdCBsaHNBVmFsID0gY3VyU3RhdHVzLnNjLmdldEFWYWxPZih2YXJOYW1lKTtcblxuICAgICAgICAgICAgICAgIGlmIChub2RlLm9wZXJhdG9yID09PSAnPScpIHtcbiAgICAgICAgICAgICAgICAgICAgLy8gc2ltcGxlIGFzc2lnbm1lbnRcbiAgICAgICAgICAgICAgICAgICAgY29uc3RyYWludHMucHVzaCh7XG4gICAgICAgICAgICAgICAgICAgICAgICBGUk9NOiByaHNBVmFsLFxuICAgICAgICAgICAgICAgICAgICAgICAgVE86IGxoc0FWYWxcbiAgICAgICAgICAgICAgICAgICAgfSk7XG4gICAgICAgICAgICAgICAgICAgIHJoc0FWYWwucHJvcGFnYXRlKGxoc0FWYWwpO1xuICAgICAgICAgICAgICAgICAgICAvLyBjb3JyZXNwb25kaW5nIEFWYWwgaXMgdGhlIFJIU1xuICAgICAgICAgICAgICAgICAgICByZXR1cm4gcmhzQVZhbDtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgY29uc3QgcmVzQVZhbCA9IG5ldyB0eXBlcy5BVmFsO1xuICAgICAgICAgICAgICAgIGlmIChub2RlLm9wZXJhdG9yID09PSAnKz0nKSB7XG4gICAgICAgICAgICAgICAgICAgIC8vIGNvbmNhdGVuYXRpbmcgdXBkYXRlXG4gICAgICAgICAgICAgICAgICAgIGNvbnN0cmFpbnRzLnB1c2goe1xuICAgICAgICAgICAgICAgICAgICAgICAgQUREX09QUkQxOiBsaHNBVmFsLFxuICAgICAgICAgICAgICAgICAgICAgICAgQUREX09QUkQyOiByaHNBVmFsLFxuICAgICAgICAgICAgICAgICAgICAgICAgUkVTVUxUOiByZXNBVmFsXG4gICAgICAgICAgICAgICAgICAgIH0pO1xuICAgICAgICAgICAgICAgICAgICBsaHNBVmFsLnByb3BhZ2F0ZShuZXcgY3N0ci5Jc0FkZGVkKHJoc0FWYWwsIHJlc0FWYWwpKTtcbiAgICAgICAgICAgICAgICAgICAgcmhzQVZhbC5wcm9wYWdhdGUobmV3IGNzdHIuSXNBZGRlZChsaHNBVmFsLCByZXNBVmFsKSk7XG4gICAgICAgICAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgLy8gYXJpdGhtZXRpYyB1cGRhdGVcbiAgICAgICAgICAgICAgICAgICAgY29uc3RyYWludHMucHVzaCh7XG4gICAgICAgICAgICAgICAgICAgICAgICBUWVBFOnR5cGVzLlByaW1OdW1iZXIsXG4gICAgICAgICAgICAgICAgICAgICAgICBJTkNMX1NFVDogcmVzQVZhbFxuICAgICAgICAgICAgICAgICAgICB9KTtcbiAgICAgICAgICAgICAgICAgICAgcmVzQVZhbC5hZGRUeXBlKHR5cGVzLlByaW1OdW1iZXIpO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICByZXR1cm4gcmVzQVZhbDtcbiAgICAgICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgICAgICAgLy8gbWVtYmVyIGFzc2lnbm1lbnRcbiAgICAgICAgICAgICAgICBjb25zdCBvYmpBVmFsID0gYyhub2RlLmxlZnQub2JqZWN0LCBjdXJTdGF0dXMsIHVuZGVmaW5lZCk7XG4gICAgICAgICAgICAgICAgY29uc3QgcHJvcEFjYyA9IHByb3BBY2Nlc3Mobm9kZS5sZWZ0KTtcbiAgICAgICAgICAgICAgICBpZiAobm9kZS5vcGVyYXRvciA9PT0gJz0nKSB7XG4gICAgICAgICAgICAgICAgICAgIC8vIGFzc2lnbm1lbnQgdG8gbWVtYmVyXG4gICAgICAgICAgICAgICAgICAgIGNvbnN0cmFpbnRzLnB1c2goe1xuICAgICAgICAgICAgICAgICAgICAgICAgT0JKOiBvYmpBVmFsLFxuICAgICAgICAgICAgICAgICAgICAgICAgUFJPUDogcHJvcEFjY1sxXSxcbiAgICAgICAgICAgICAgICAgICAgICAgIFdSSVRFX1dJVEg6IHJoc0FWYWxcbiAgICAgICAgICAgICAgICAgICAgfSk7XG4gICAgICAgICAgICAgICAgICAgIG9iakFWYWwucHJvcGFnYXRlKG5ldyBjc3RyLldyaXRlUHJvcChwcm9wQWNjWzFdLCByaHNBVmFsKSk7XG4gICAgICAgICAgICAgICAgICAgIC8vIGlmIHByb3BlcnR5IGlzIG51bWJlciBsaXRlcmFsLCBhbHNvIHdyaXRlIHRvICd1bmtub3duJ1xuICAgICAgICAgICAgICAgICAgICBpZiAocHJvcEFjY1swXSA9PT0gJ251bWJlckxpdGVyYWwnKSB7XG4gICAgICAgICAgICAgICAgICAgICAgICBvYmpBVmFsLnByb3BhZ2F0ZShuZXcgY3N0ci5Xcml0ZVByb3AobnVsbCwgcmhzQVZhbCkpO1xuICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgIHJldHVybiByaHNBVmFsO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICBjb25zdCByZXNBVmFsID0gbmV3IHR5cGVzLkFWYWw7XG4gICAgICAgICAgICAgICAgY29uc3QgcmVjdkFuZFJldCA9IHJlYWRNZW1iZXIobm9kZS5sZWZ0LCBjdXJTdGF0dXMsIGMpO1xuICAgICAgICAgICAgICAgIGlmIChub2RlLm9wZXJhdG9yID09PSAnKz0nKSB7XG4gICAgICAgICAgICAgICAgICAgIC8vIGNvbmNhdGVuYXRpbmcgdXBkYXRlXG4gICAgICAgICAgICAgICAgICAgIGNvbnN0cmFpbnRzLnB1c2goe1xuICAgICAgICAgICAgICAgICAgICAgICAgQUREX09QUkQxOiByZWN2QW5kUmV0WzFdLFxuICAgICAgICAgICAgICAgICAgICAgICAgQUREX09QUkQyOiByaHNBVmFsLFxuICAgICAgICAgICAgICAgICAgICAgICAgUkVTVUxUOiByZXNBVmFsXG4gICAgICAgICAgICAgICAgICAgIH0pO1xuICAgICAgICAgICAgICAgICAgICByZWN2QW5kUmV0WzFdLnByb3BhZ2F0ZShuZXcgY3N0ci5Jc0FkZGVkKHJoc0FWYWwsIHJlc0FWYWwpKTtcbiAgICAgICAgICAgICAgICAgICAgcmhzQVZhbC5wcm9wYWdhdGUobmV3IGNzdHIuSXNBZGRlZChyZWN2QW5kUmV0WzFdLCByZXNBVmFsKSk7XG4gICAgICAgICAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgLy8gYXJpdGhtZXRpYyB1cGRhdGVcbiAgICAgICAgICAgICAgICAgICAgY29uc3RyYWludHMucHVzaCh7XG4gICAgICAgICAgICAgICAgICAgICAgICBUWVBFOiB0eXBlcy5QcmltTnVtYmVyLFxuICAgICAgICAgICAgICAgICAgICAgICAgSU5DTF9TRVQ6IHJlc0FWYWxcbiAgICAgICAgICAgICAgICAgICAgfSk7XG4gICAgICAgICAgICAgICAgICAgIHJlc0FWYWwuYWRkVHlwZSh0eXBlcy5QcmltTnVtYmVyKTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgcmV0dXJuIHJlc0FWYWw7XG4gICAgICAgICAgICB9XG4gICAgICAgIH0sXG5cbiAgICAgICAgVmFyaWFibGVEZWNsYXJhdGlvbjogZnVuY3Rpb24gKG5vZGUsIGN1clN0YXR1cywgYykge1xuICAgICAgICAgICAgZm9yIChsZXQgaSA9IDA7IGkgPCBub2RlLmRlY2xhcmF0aW9ucy5sZW5ndGg7IGkrKykge1xuICAgICAgICAgICAgICAgIGNvbnN0IGRlY2wgPSBub2RlLmRlY2xhcmF0aW9uc1tpXTtcbiAgICAgICAgICAgICAgICBpZiAoZGVjbC5pbml0KSB7XG4gICAgICAgICAgICAgICAgICAgIGNvbnN0IGxoc0FWYWwgPSBjdXJTdGF0dXMuc2MuZ2V0QVZhbE9mKGRlY2wuaWQubmFtZSk7XG4gICAgICAgICAgICAgICAgICAgIGNvbnN0IHJoc0FWYWwgPSBjKGRlY2wuaW5pdCwgY3VyU3RhdHVzLCB1bmRlZmluZWQpO1xuICAgICAgICAgICAgICAgICAgICBjb25zdHJhaW50cy5wdXNoKHtGUk9NOiByaHNBVmFsLFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBUTzogbGhzQVZhbH0pO1xuICAgICAgICAgICAgICAgICAgICByaHNBVmFsLnByb3BhZ2F0ZShsaHNBVmFsKTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICB9XG4gICAgICAgIH0sXG5cbiAgICAgICAgTG9naWNhbEV4cHJlc3Npb246IGZ1bmN0aW9uIChub2RlLCBjdXJTdGF0dXMsIGMpIHtcbiAgICAgICAgICAgIGNvbnN0IHJlcyA9IG5ldyB0eXBlcy5BVmFsO1xuICAgICAgICAgICAgY29uc3QgbGVmdCA9IGMobm9kZS5sZWZ0LCBjdXJTdGF0dXMsIHVuZGVmaW5lZCk7XG4gICAgICAgICAgICBjb25zdCByaWdodCA9IGMobm9kZS5yaWdodCwgY3VyU3RhdHVzLCB1bmRlZmluZWQpO1xuICAgICAgICAgICAgY29uc3RyYWludHMucHVzaCh7RlJPTTogbGVmdCwgVE86IHJlc30sXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgIHtGUk9NOiByaWdodCwgVE86IHJlc30pO1xuICAgICAgICAgICAgbGVmdC5wcm9wYWdhdGUocmVzKTtcbiAgICAgICAgICAgIHJpZ2h0LnByb3BhZ2F0ZShyZXMpO1xuICAgICAgICAgICAgcmV0dXJuIHJlcztcbiAgICAgICAgfSxcblxuICAgICAgICBDb25kaXRpb25hbEV4cHJlc3Npb246IGZ1bmN0aW9uIChub2RlLCBjdXJTdGF0dXMsIGMpIHtcbiAgICAgICAgICAgIGNvbnN0IHJlcyA9IG5ldyB0eXBlcy5BVmFsO1xuICAgICAgICAgICAgYyhub2RlLnRlc3QsIGN1clN0YXR1cywgdW5kZWZpbmVkKTtcbiAgICAgICAgICAgIGNvbnN0IGNvbnMgPSBjKG5vZGUuY29uc2VxdWVudCwgY3VyU3RhdHVzLCB1bmRlZmluZWQpO1xuICAgICAgICAgICAgY29uc3QgYWx0ID0gYyhub2RlLmFsdGVybmF0ZSwgY3VyU3RhdHVzLCB1bmRlZmluZWQpO1xuICAgICAgICAgICAgY29uc3RyYWludHMucHVzaCh7RlJPTTogY29ucywgVE86IHJlc30sXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgIHtGUk9NOiBhbHQsIFRPOiByZXN9KTtcbiAgICAgICAgICAgIGNvbnMucHJvcGFnYXRlKHJlcyk7XG4gICAgICAgICAgICBhbHQucHJvcGFnYXRlKHJlcyk7XG4gICAgICAgICAgICByZXR1cm4gcmVzO1xuICAgICAgICB9LFxuXG4gICAgICAgIE5ld0V4cHJlc3Npb246IGZ1bmN0aW9uIChub2RlLCBjdXJTdGF0dXMsIGMpIHtcbiAgICAgICAgICAgIGNvbnN0IHJldCA9IG5ldyB0eXBlcy5BVmFsO1xuICAgICAgICAgICAgY29uc3QgY2FsbGVlID0gYyhub2RlLmNhbGxlZSwgY3VyU3RhdHVzLCB1bmRlZmluZWQpO1xuICAgICAgICAgICAgY29uc3QgYXJncyA9IFtdO1xuICAgICAgICAgICAgZm9yIChsZXQgaSA9IDA7IGkgPCBub2RlLmFyZ3VtZW50cy5sZW5ndGg7IGkrKykge1xuICAgICAgICAgICAgICAgIGFyZ3MucHVzaChjKG5vZGUuYXJndW1lbnRzW2ldLCBjdXJTdGF0dXMsIHVuZGVmaW5lZCkpO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgY29uc3QgbmV3RGVsdGEgPSBjdXJTdGF0dXMuZGVsdGEuYXBwZW5kT25lKG5vZGVbJ0BsYWJlbCddKTtcbiAgICAgICAgICAgIGNvbnN0cmFpbnRzLnB1c2goe0NPTlNUUlVDVE9SOiBjYWxsZWUsXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICBBUkdTOiBhcmdzLFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgUkVUOiByZXQsXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICBFWEM6IGN1clN0YXR1cy5leGMsXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICBERUxUQTogbmV3RGVsdGF9KTtcbiAgICAgICAgICAgIGNhbGxlZS5wcm9wYWdhdGUoXG4gICAgICAgICAgICAgICAgbmV3IGNzdHIuSXNDdG9yKFxuICAgICAgICAgICAgICAgICAgICBhcmdzLFxuICAgICAgICAgICAgICAgICAgICByZXQsXG4gICAgICAgICAgICAgICAgICAgIGN1clN0YXR1cy5leGMsXG4gICAgICAgICAgICAgICAgICAgIG5ld0RlbHRhKSk7XG4gICAgICAgICAgICByZXR1cm4gcmV0O1xuICAgICAgICB9LFxuXG4gICAgICAgIEFycmF5RXhwcmVzc2lvbjogZnVuY3Rpb24gKG5vZGUsIGN1clN0YXR1cywgYykge1xuICAgICAgICAgICAgY29uc3QgcmV0ID0gbmV3IHR5cGVzLkFWYWw7XG4gICAgICAgICAgICBjb25zdCBhcnJUeXBlID0gbmV3IHR5cGVzLkFyclR5cGUobmV3IHR5cGVzLkFWYWwocnRDWC5wcm90b3MuQXJyYXkpKTtcbiAgICAgICAgICAgIC8vIGFkZCBsZW5ndGggcHJvcGVydHlcbiAgICAgICAgICAgIGFyclR5cGUuZ2V0UHJvcCgnbGVuZ3RoJykuYWRkVHlwZSh0eXBlcy5QcmltTnVtYmVyKTtcblxuICAgICAgICAgICAgY29uc3RyYWludHMucHVzaCh7VFlQRTogYXJyVHlwZSwgSU5DTF9TRVQ6IHJldH0pO1xuICAgICAgICAgICAgcmV0LmFkZFR5cGUoYXJyVHlwZSk7XG5cbiAgICAgICAgICAgIC8vIGFkZCBhcnJheSBlbGVtZW50c1xuICAgICAgICAgICAgZm9yIChsZXQgaSA9IDA7IGkgPCBub2RlLmVsZW1lbnRzLmxlbmd0aDsgaSsrKSB7XG4gICAgICAgICAgICAgICAgY29uc3QgZWx0QVZhbCA9IGMobm9kZS5lbGVtZW50c1tpXSwgY3VyU3RhdHVzLCB1bmRlZmluZWQpO1xuXG4gICAgICAgICAgICAgICAgY29uc3QgcHJvcCA9IGkgKyAnJztcbiAgICAgICAgICAgICAgICBjb25zdHJhaW50cy5wdXNoKHtPQko6IHJldCwgUFJPUDogcHJvcCwgQVZBTDogZWx0QVZhbH0pO1xuICAgICAgICAgICAgICAgIGNvbnN0cmFpbnRzLnB1c2goe09CSjogcmV0LCBQUk9QOiBudWxsLCBBVkFMOiBlbHRBVmFsfSk7XG4gICAgICAgICAgICAgICAgcmV0LnByb3BhZ2F0ZShuZXcgY3N0ci5Xcml0ZVByb3AocHJvcCwgZWx0QVZhbCkpO1xuICAgICAgICAgICAgICAgIHJldC5wcm9wYWdhdGUobmV3IGNzdHIuV3JpdGVQcm9wKG51bGwsIGVsdEFWYWwpKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIHJldHVybiByZXQ7XG4gICAgICAgIH0sXG5cbiAgICAgICAgT2JqZWN0RXhwcmVzc2lvbjogZnVuY3Rpb24gKG5vZGUsIGN1clN0YXR1cywgYykge1xuICAgICAgICAgICAgY29uc3QgcmV0ID0gbmV3IHR5cGVzLkFWYWw7XG4gICAgICAgICAgICBjb25zdCBvYmpUeXBlID0gbmV3IHR5cGVzLk9ialR5cGUobmV3IHR5cGVzLkFWYWwocnRDWC5wcm90b3MuT2JqZWN0KSk7XG4gICAgICAgICAgICBjb25zdHJhaW50cy5wdXNoKHtUWVBFOiBvYmpUeXBlLCBJTkNMX1NFVDogcmV0fSk7XG4gICAgICAgICAgICByZXQuYWRkVHlwZShvYmpUeXBlKTtcblxuICAgICAgICAgICAgZm9yIChsZXQgaSA9IDA7IGkgPCBub2RlLnByb3BlcnRpZXMubGVuZ3RoOyBpKyspIHtcbiAgICAgICAgICAgICAgICBjb25zdCBwcm9wUGFpciA9IG5vZGUucHJvcGVydGllc1tpXTtcbiAgICAgICAgICAgICAgICBjb25zdCBwcm9wS2V5ID0gcHJvcFBhaXIua2V5O1xuICAgICAgICAgICAgICAgIGxldCBuYW1lO1xuICAgICAgICAgICAgICAgIGNvbnN0IHByb3BFeHByID0gcHJvcFBhaXIudmFsdWU7XG5cbiAgICAgICAgICAgICAgICBjb25zdCBmbGRBVmFsID0gYyhwcm9wRXhwciwgY3VyU3RhdHVzLCB1bmRlZmluZWQpO1xuXG4gICAgICAgICAgICAgICAgaWYgKHByb3BLZXkudHlwZSA9PT0gJ0lkZW50aWZpZXInKSB7XG4gICAgICAgICAgICAgICAgICAgIG5hbWUgPSBwcm9wS2V5Lm5hbWU7XG4gICAgICAgICAgICAgICAgfSBlbHNlIGlmICh0eXBlb2YgcHJvcEtleS52YWx1ZSA9PT0gJ3N0cmluZycpIHtcbiAgICAgICAgICAgICAgICAgICAgbmFtZSA9IHByb3BLZXkudmFsdWU7XG4gICAgICAgICAgICAgICAgfSBlbHNlIGlmICh0eXBlb2YgcHJvcEtleS52YWx1ZSA9PT0gJ251bWJlcicpIHtcbiAgICAgICAgICAgICAgICAgICAgLy8gY29udmVydCBudW1iZXIgdG8gc3RyaW5nXG4gICAgICAgICAgICAgICAgICAgIG5hbWUgPSBwcm9wS2V5LnZhbHVlICsgJyc7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIGNvbnN0cmFpbnRzLnB1c2goe09CSjogcmV0LCBQUk9QOiBuYW1lLCBBVkFMOiBmbGRBVmFsfSk7XG4gICAgICAgICAgICAgICAgcmV0LnByb3BhZ2F0ZShuZXcgY3N0ci5Xcml0ZVByb3AobmFtZSwgZmxkQVZhbCkpO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgcmV0dXJuIHJldDtcbiAgICAgICAgfSxcblxuICAgICAgICBGdW5jdGlvbkV4cHJlc3Npb246IGZ1bmN0aW9uIChub2RlLCBjdXJTdGF0dXMsIGMpIHtcbiAgICAgICAgICAgIGlmICghbm9kZS5mbkluc3RhbmNlcykge1xuICAgICAgICAgICAgICAgIG5vZGUuZm5JbnN0YW5jZXMgPSBbXTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGxldCBmbkluc3RhbmNlID0gbnVsbDtcbiAgICAgICAgICAgIG5vZGUuZm5JbnN0YW5jZXMuZm9yRWFjaChmdW5jdGlvbiAoZm5UeXBlKSB7XG4gICAgICAgICAgICAgICAgaWYgKGZuVHlwZS5zYyA9PT0gY3VyU3RhdHVzLnNjKSB7XG4gICAgICAgICAgICAgICAgICAgIGZuSW5zdGFuY2UgPSBmblR5cGU7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgfSk7XG4gICAgICAgICAgICBpZiAoIWZuSW5zdGFuY2UpIHtcbiAgICAgICAgICAgICAgICBmbkluc3RhbmNlXG4gICAgICAgICAgICAgICAgICAgID0gbmV3IHR5cGVzLkZuVHlwZShuZXcgdHlwZXMuQVZhbChydENYLnByb3Rvcy5GdW5jdGlvbiksXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAnW2Fub255bW91cyBmdW5jdGlvbl0nLFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgbm9kZS5ib2R5WydAYmxvY2snXS5nZXRQYXJhbVZhck5hbWVzKCksXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBjdXJTdGF0dXMuc2MsXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBub2RlLFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgcnRDWC5wcm90b3MuT2JqZWN0KTtcbiAgICAgICAgICAgICAgICBub2RlLmZuSW5zdGFuY2VzLnB1c2goZm5JbnN0YW5jZSk7XG4gICAgICAgICAgICAgICAgY29uc3QgcHJvdG90eXBlT2JqZWN0ID1cbiAgICAgICAgICAgICAgICAgICAgbmV3IHR5cGVzLk9ialR5cGUobmV3IHR5cGVzLkFWYWwocnRDWC5wcm90b3MuT2JqZWN0KSxcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgJz8ucHJvdG90eXBlJyk7XG4gICAgICAgICAgICAgICAgLy8gRm9yIC5wcm90b3R5cGVcbiAgICAgICAgICAgICAgICBjb25zdCBwcm90b3R5cGVQcm9wID0gZm5JbnN0YW5jZS5nZXRQcm9wKCdwcm90b3R5cGUnKTtcbiAgICAgICAgICAgICAgICBjb25zdHJhaW50cy5wdXNoKHtUWVBFOiBwcm90b3R5cGVPYmplY3QsXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgSU5DTF9TRVQ6IHByb3RvdHlwZVByb3B9KTtcbiAgICAgICAgICAgICAgICBwcm90b3R5cGVQcm9wLmFkZFR5cGUocHJvdG90eXBlT2JqZWN0KTtcbiAgICAgICAgICAgICAgICAvLyBGb3IgLnByb3RvdHlwZS5jb25zdHJ1Y3RvclxuICAgICAgICAgICAgICAgIGNvbnN0IGNvbnN0cnVjdG9yUHJvcCA9IHByb3RvdHlwZU9iamVjdC5nZXRQcm9wKCdjb25zdHJ1Y3RvcicpO1xuICAgICAgICAgICAgICAgIGNvbnN0cmFpbnRzLnB1c2goe1RZUEU6IGZuSW5zdGFuY2UsXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgSU5DTF9TRVQ6IGNvbnN0cnVjdG9yUHJvcH0pO1xuICAgICAgICAgICAgICAgIGNvbnN0cnVjdG9yUHJvcC5hZGRUeXBlKGZuSW5zdGFuY2UpO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgY29uc3QgcmV0ID0gbmV3IHR5cGVzLkFWYWw7XG4gICAgICAgICAgICBjb25zdHJhaW50cy5wdXNoKHtUWVBFOiBmbkluc3RhbmNlLFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgSU5DTF9TRVQ6IHJldH0pO1xuICAgICAgICAgICAgcmV0LmFkZFR5cGUoZm5JbnN0YW5jZSk7XG4gICAgICAgICAgICByZXR1cm4gcmV0O1xuICAgICAgICB9LFxuXG4gICAgICAgIEZ1bmN0aW9uRGVjbGFyYXRpb246IGZ1bmN0aW9uIChub2RlLCBjdXJTdGF0dXMsIGMpIHtcbiAgICAgICAgICAgIC8vIERyb3AgaW5pdGlhbCBjYXRjaCBzY29wZXNcbiAgICAgICAgICAgIGNvbnN0IHNjMCA9IGN1clN0YXR1cy5zYy5yZW1vdmVJbml0aWFsQ2F0Y2hCbG9ja3MoKTtcbiAgICAgICAgICAgIGlmICghbm9kZS5mbkluc3RhbmNlcykge1xuICAgICAgICAgICAgICAgIG5vZGUuZm5JbnN0YW5jZXMgPSBbXTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGxldCBmbkluc3RhbmNlID0gbnVsbDtcbiAgICAgICAgICAgIG5vZGUuZm5JbnN0YW5jZXMuZm9yRWFjaChmdW5jdGlvbiAoZm5UeXBlKSB7XG4gICAgICAgICAgICAgICAgaWYgKGZuVHlwZS5zYyA9PT0gc2MwKSB7XG4gICAgICAgICAgICAgICAgICAgIGZuSW5zdGFuY2UgPSBmblR5cGU7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgfSk7XG4gICAgICAgICAgICBpZiAoIWZuSW5zdGFuY2UpIHtcbiAgICAgICAgICAgICAgICBmbkluc3RhbmNlXG4gICAgICAgICAgICAgICAgICAgID0gbmV3IHR5cGVzLkZuVHlwZShuZXcgdHlwZXMuQVZhbChydENYLnByb3Rvcy5GdW5jdGlvbiksXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBub2RlLmlkLm5hbWUsXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBub2RlLmJvZHlbJ0BibG9jayddLmdldFBhcmFtVmFyTmFtZXMoKSxcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIHNjMCxcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIG5vZGUsXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBydENYLnByb3Rvcy5PYmplY3QpO1xuICAgICAgICAgICAgICAgIG5vZGUuZm5JbnN0YW5jZXMucHVzaChmbkluc3RhbmNlKTtcbiAgICAgICAgICAgICAgICAvLyBmb3IgZWFjaCBmbkluc3RhbmNlLCBhc3NpZ24gb25lIHByb3RvdHlwZSBvYmplY3RcbiAgICAgICAgICAgICAgICBjb25zdCBwcm90b3R5cGVPYmplY3QgPVxuICAgICAgICAgICAgICAgICAgICBuZXcgdHlwZXMuT2JqVHlwZShuZXcgdHlwZXMuQVZhbChydENYLnByb3Rvcy5PYmplY3QpLFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBub2RlLmlkLm5hbWUgKyAnLnByb3RvdHlwZScpO1xuICAgICAgICAgICAgICAgIC8vIEZvciAucHJvdG90eXBlXG4gICAgICAgICAgICAgICAgY29uc3QgcHJvdG90eXBlUHJvcCA9IGZuSW5zdGFuY2UuZ2V0UHJvcCgncHJvdG90eXBlJyk7XG4gICAgICAgICAgICAgICAgY29uc3RyYWludHMucHVzaCh7VFlQRTogcHJvdG90eXBlT2JqZWN0LFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIElOQ0xfU0VUOiBwcm90b3R5cGVQcm9wfSk7XG4gICAgICAgICAgICAgICAgcHJvdG90eXBlUHJvcC5hZGRUeXBlKHByb3RvdHlwZU9iamVjdCk7XG4gICAgICAgICAgICAgICAgLy8gRm9yIC5wcm90b3R5cGUuY29uc3RydWN0b3JcbiAgICAgICAgICAgICAgICBjb25zdCBjb25zdHJ1Y3RvclByb3AgPSBwcm90b3R5cGVPYmplY3QuZ2V0UHJvcCgnY29uc3RydWN0b3InKTtcbiAgICAgICAgICAgICAgICBjb25zdHJhaW50cy5wdXNoKHtUWVBFOiBmbkluc3RhbmNlLFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIElOQ0xfU0VUOiBjb25zdHJ1Y3RvclByb3B9KTtcbiAgICAgICAgICAgICAgICBjb25zdHJ1Y3RvclByb3AuYWRkVHlwZShmbkluc3RhbmNlKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGNvbnN0IGxoc0FWYWwgPSBzYzAuZ2V0QVZhbE9mKG5vZGUuaWQubmFtZSk7XG5cbiAgICAgICAgICAgIGNvbnN0cmFpbnRzLnB1c2goe1RZUEU6IGZuSW5zdGFuY2UsXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICBJTkNMX1NFVDogbGhzQVZhbH0pO1xuICAgICAgICAgICAgbGhzQVZhbC5hZGRUeXBlKGZuSW5zdGFuY2UpO1xuICAgICAgICAgICAgLy8gbm90aGluZyB0byByZXR1cm5cbiAgICAgICAgICAgIHJldHVybiB0eXBlcy5BVmFsTnVsbDtcbiAgICAgICAgfSxcblxuICAgICAgICBTZXF1ZW5jZUV4cHJlc3Npb246IGZ1bmN0aW9uIChub2RlLCBjdXJTdGF0dXMsIGMpIHtcbiAgICAgICAgICAgIGNvbnN0IGxhc3RJbmRleCA9IG5vZGUuZXhwcmVzc2lvbnMubGVuZ3RoIC0gMTtcbiAgICAgICAgICAgIGZvciAobGV0IGkgPSAwOyBpIDwgbGFzdEluZGV4OyBpKyspIHtcbiAgICAgICAgICAgICAgICBjKG5vZGUuZXhwcmVzc2lvbnNbaV0sIGN1clN0YXR1cywgdW5kZWZpbmVkKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIHJldHVybiBjKG5vZGUuZXhwcmVzc2lvbnNbbGFzdEluZGV4XSwgY3VyU3RhdHVzLCB1bmRlZmluZWQpO1xuICAgICAgICB9LFxuXG4gICAgICAgIFVuYXJ5RXhwcmVzc2lvbjogZnVuY3Rpb24gKG5vZGUsIGN1clN0YXR1cywgYykge1xuICAgICAgICAgICAgYyhub2RlLmFyZ3VtZW50LCBjdXJTdGF0dXMsIHVuZGVmaW5lZCk7XG4gICAgICAgICAgICBjb25zdCByZXMgPSBuZXcgdHlwZXMuQVZhbDtcbiAgICAgICAgICAgIGNvbnN0IHR5cGUgPSB1bm9wUmVzdWx0VHlwZShub2RlLm9wZXJhdG9yKTtcbiAgICAgICAgICAgIGlmICh0eXBlKSB7XG4gICAgICAgICAgICAgICAgY29uc3RyYWludHMucHVzaCh7VFlQRTogdHlwZSxcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBJTkNMX1NFVDogcmVzfSk7XG4gICAgICAgICAgICAgICAgcmVzLmFkZFR5cGUodHlwZSk7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICByZXR1cm4gcmVzO1xuICAgICAgICB9LFxuXG4gICAgICAgIFVwZGF0ZUV4cHJlc3Npb246IGZ1bmN0aW9uIChub2RlLCBjdXJTdGF0dXMsIGMpIHtcbiAgICAgICAgICAgIGMobm9kZS5hcmd1bWVudCwgY3VyU3RhdHVzLCB1bmRlZmluZWQpO1xuICAgICAgICAgICAgY29uc3QgcmVzID0gbmV3IHR5cGVzLkFWYWw7XG4gICAgICAgICAgICBjb25zdHJhaW50cy5wdXNoKHtUWVBFOiB0eXBlcy5QcmltTnVtYmVyLFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgSU5DTF9TRVQ6IHJlc30pO1xuICAgICAgICAgICAgcmVzLmFkZFR5cGUodHlwZXMuUHJpbU51bWJlcik7XG4gICAgICAgICAgICAvLyBXZSBpZ25vcmUgdGhlIGVmZmVjdCBvZiB1cGRhdGluZyB0byBudW1iZXIgdHlwZVxuICAgICAgICAgICAgcmV0dXJuIHJlcztcbiAgICAgICAgfSxcblxuICAgICAgICBCaW5hcnlFeHByZXNzaW9uOiBmdW5jdGlvbiAobm9kZSwgY3VyU3RhdHVzLCBjKSB7XG4gICAgICAgICAgICBjb25zdCBsT3ByZCA9IGMobm9kZS5sZWZ0LCBjdXJTdGF0dXMsIHVuZGVmaW5lZCk7XG4gICAgICAgICAgICBjb25zdCByT3ByZCA9IGMobm9kZS5yaWdodCwgY3VyU3RhdHVzLCB1bmRlZmluZWQpO1xuICAgICAgICAgICAgY29uc3QgcmVzID0gbmV3IHR5cGVzLkFWYWw7XG5cbiAgICAgICAgICAgIGlmIChub2RlLm9wZXJhdG9yID09ICcrJykge1xuICAgICAgICAgICAgICAgIGNvbnN0cmFpbnRzLnB1c2goe0FERF9PUFJEMTogbE9wcmQsXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgQUREX09QUkQyOiByT3ByZCxcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBSRVNVTFQ6IHJlcyB9KTtcbiAgICAgICAgICAgICAgICBsT3ByZC5wcm9wYWdhdGUobmV3IGNzdHIuSXNBZGRlZChyT3ByZCwgcmVzKSk7XG4gICAgICAgICAgICAgICAgck9wcmQucHJvcGFnYXRlKG5ldyBjc3RyLklzQWRkZWQobE9wcmQsIHJlcykpO1xuICAgICAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICAgICAgICBpZiAoYmlub3BJc0Jvb2xlYW4obm9kZS5vcGVyYXRvcikpIHtcbiAgICAgICAgICAgICAgICAgICAgY29uc3RyYWludHMucHVzaCh7VFlQRTogdHlwZXMuUHJpbUJvb2xlYW4sXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIElOQ0xfU0VUOiByZXN9KTtcbiAgICAgICAgICAgICAgICAgICAgcmVzLmFkZFR5cGUodHlwZXMuUHJpbUJvb2xlYW4pO1xuICAgICAgICAgICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgICAgICAgICAgIGNvbnN0cmFpbnRzLnB1c2goe1RZUEU6IHR5cGVzLlByaW1OdW1iZXIsXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIElOQ0xfU0VUOiByZXN9KTtcbiAgICAgICAgICAgICAgICAgICAgcmVzLmFkZFR5cGUodHlwZXMuUHJpbU51bWJlcik7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgfVxuICAgICAgICAgICAgcmV0dXJuIHJlcztcbiAgICAgICAgfSxcblxuICAgICAgICBUcnlTdGF0ZW1lbnQ6IGZ1bmN0aW9uIChub2RlLCBjdXJTdGF0dXMsIGMpIHtcbiAgICAgICAgICAgIC8vIGNvbnN0cnVjdCBzY29wZSBjaGFpbiBmb3IgY2F0Y2ggYmxvY2tcbiAgICAgICAgICAgIGNvbnN0IGNhdGNoQmxvY2tTQyA9XG4gICAgICAgICAgICAgICAgbm9kZS5oYW5kbGVyLmJvZHlbJ0BibG9jayddXG4gICAgICAgICAgICAgICAgLmdldFNjb3BlSW5zdGFuY2UoY3VyU3RhdHVzLnNjLCBjdXJTdGF0dXMuZGVsdGEpO1xuICAgICAgICAgICAgLy8gZ2V0IHRoZSBBVmFsIGZvciBleGNlcHRpb24gcGFyYW1ldGVyXG4gICAgICAgICAgICBjb25zdCBleGNBVmFsID0gY2F0Y2hCbG9ja1NDLmdldEFWYWxPZihub2RlLmhhbmRsZXIucGFyYW0ubmFtZSk7XG5cbiAgICAgICAgICAgIC8vIGZvciB0cnkgYmxvY2tcbiAgICAgICAgICAgIGNvbnN0IHRyeVN0YXR1cyA9IGNoYW5nZWRTdGF0dXMoY3VyU3RhdHVzLCAnZXhjJywgZXhjQVZhbCk7XG4gICAgICAgICAgICBjKG5vZGUuYmxvY2ssIHRyeVN0YXR1cywgdW5kZWZpbmVkKTtcblxuICAgICAgICAgICAgLy8gZm9yIGNhdGNoIGJsb2NrXG4gICAgICAgICAgICBjb25zdCBjYXRjaFN0YXR1cyA9IGNoYW5nZWRTdGF0dXMoY3VyU3RhdHVzLCAnc2MnLCBjYXRjaEJsb2NrU0MpO1xuICAgICAgICAgICAgYyhub2RlLmhhbmRsZXIuYm9keSwgY2F0Y2hTdGF0dXMsIHVuZGVmaW5lZCk7XG5cbiAgICAgICAgICAgIC8vIGZvciBmaW5hbGx5IGJsb2NrXG4gICAgICAgICAgICBpZiAobm9kZS5maW5hbGl6ZXIgIT09IG51bGwpXG4gICAgICAgICAgICAgICAgYyhub2RlLmZpbmFsaXplciwgY3VyU3RhdHVzLCB1bmRlZmluZWQpO1xuICAgICAgICB9LFxuXG4gICAgICAgIFRocm93U3RhdGVtZW50OiBmdW5jdGlvbiAobm9kZSwgY3VyU3RhdHVzLCBjKSB7XG4gICAgICAgICAgICBjb25zdCB0aHIgPSBjKG5vZGUuYXJndW1lbnQsIGN1clN0YXR1cywgdW5kZWZpbmVkKTtcbiAgICAgICAgICAgIGNvbnN0cmFpbnRzLnB1c2goe0ZST006IHRocixcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIFRPOiBjdXJTdGF0dXMuZXhjfSk7XG4gICAgICAgICAgICB0aHIucHJvcGFnYXRlKGN1clN0YXR1cy5leGMpO1xuICAgICAgICB9LFxuXG4gICAgICAgIENhbGxFeHByZXNzaW9uOiBmdW5jdGlvbiAobm9kZSwgY3VyU3RhdHVzLCBjKSB7XG4gICAgICAgICAgICBjb25zdCByZXNBVmFsID0gbmV3IHR5cGVzLkFWYWw7XG4gICAgICAgICAgICBjb25zdCBhcmdBVmFscyA9IFtdO1xuXG4gICAgICAgICAgICAvLyBnZXQgQVZhbHMgZm9yIGVhY2ggYXJndW1lbnRzXG4gICAgICAgICAgICBmb3IgKGxldCBpID0gMDsgaSA8IG5vZGUuYXJndW1lbnRzLmxlbmd0aDsgaSsrKSB7XG4gICAgICAgICAgICAgICAgYXJnQVZhbHMucHVzaChcbiAgICAgICAgICAgICAgICAgICAgYyhub2RlLmFyZ3VtZW50c1tpXSwgY3VyU3RhdHVzLCB1bmRlZmluZWQpKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIC8vIGFwcGVuZCBjdXJyZW50IGNhbGwgc2l0ZSB0byB0aGUgY29udGV4dFxuICAgICAgICAgICAgY29uc3QgbmV3RGVsdGEgPSBjdXJTdGF0dXMuZGVsdGEuYXBwZW5kT25lKG5vZGVbJ0BsYWJlbCddKTtcblxuICAgICAgICAgICAgaWYgKG5vZGUuY2FsbGVlLnR5cGUgPT09ICdNZW1iZXJFeHByZXNzaW9uJykge1xuICAgICAgICAgICAgICAgIC8vIG1ldGhvZCBjYWxsXG4gICAgICAgICAgICAgICAgLy8gdmFyIHJlY3YgPSBjKG5vZGUuY2FsbGVlLm9iamVjdCwgY3VyU3RhdHVzLCB1bmRlZmluZWQpO1xuICAgICAgICAgICAgICAgIC8vIHZhciBtZXRob2ROYW1lID0gaW1tZWRQcm9wKG5vZGUuY2FsbGVlKTtcbiAgICAgICAgICAgICAgICAvLyBjb25zdHJhaW50cy5wdXNoKHtcbiAgICAgICAgICAgICAgICAvLyAgIFJFQ1Y6IHJlY3YsXG4gICAgICAgICAgICAgICAgLy8gICBQUk9QTkFNRTogbWV0aG9kTmFtZSxcbiAgICAgICAgICAgICAgICAvLyAgIFBBUkFNUzogYXJnQVZhbHMsXG4gICAgICAgICAgICAgICAgLy8gICBSRVQ6IHJlc0FWYWwsXG4gICAgICAgICAgICAgICAgLy8gICBFWEM6IGN1clN0YXR1cy5leGMsXG4gICAgICAgICAgICAgICAgLy8gICBERUxUQTogbmV3RGVsdGFcbiAgICAgICAgICAgICAgICAvLyB9KTtcbiAgICAgICAgICAgICAgICBjb25zdCByZWN2QW5kUmV0ID0gcmVhZE1lbWJlcihub2RlLmNhbGxlZSwgY3VyU3RhdHVzLCBjKTtcbiAgICAgICAgICAgICAgICByZWN2QW5kUmV0WzFdLnByb3BhZ2F0ZShcbiAgICAgICAgICAgICAgICAgICAgbmV3IGNzdHIuSXNDYWxsZWUoXG4gICAgICAgICAgICAgICAgICAgICAgICByZWN2QW5kUmV0WzBdLFxuICAgICAgICAgICAgICAgICAgICAgICAgYXJnQVZhbHMsXG4gICAgICAgICAgICAgICAgICAgICAgICByZXNBVmFsLFxuICAgICAgICAgICAgICAgICAgICAgICAgY3VyU3RhdHVzLmV4YyxcbiAgICAgICAgICAgICAgICAgICAgICAgIG5ld0RlbHRhKSk7XG4gICAgICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgICAgICAgIC8vIG5vcm1hbCBmdW5jdGlvbiBjYWxsXG4gICAgICAgICAgICAgICAgY29uc3QgY2FsbGVlQVZhbCA9IGMobm9kZS5jYWxsZWUsIGN1clN0YXR1cywgdW5kZWZpbmVkKTtcbiAgICAgICAgICAgICAgICAvLyBjYWxsZWXsnZggcmV0dXJu7J2EIGNhbGwgZXhwcmVzc2lvbuycvOuhnFxuICAgICAgICAgICAgICAgIC8vIGNhbGxlZeydmCBleGNlcHRpb27snYQg7Zi47LacIOy4oeydmCBleGNlcHRpb27sl5Ag7KCE64us7ZW07JW8XG4gICAgICAgICAgICAgICAgY29uc3RyYWludHMucHVzaCh7XG4gICAgICAgICAgICAgICAgICAgIENBTExFRTogY2FsbGVlQVZhbCxcbiAgICAgICAgICAgICAgICAgICAgU0VMRjogcnRDWC5nbG9iYWxPYmplY3QsXG4gICAgICAgICAgICAgICAgICAgIFBBUkFNUzogYXJnQVZhbHMsXG4gICAgICAgICAgICAgICAgICAgIFJFVDogcmVzQVZhbCxcbiAgICAgICAgICAgICAgICAgICAgRVhDOiBjdXJTdGF0dXMuZXhjLFxuICAgICAgICAgICAgICAgICAgICBERUxUQTogbmV3RGVsdGFcbiAgICAgICAgICAgICAgICB9KTtcbiAgICAgICAgICAgICAgICBjYWxsZWVBVmFsLnByb3BhZ2F0ZShcbiAgICAgICAgICAgICAgICAgICAgbmV3IGNzdHIuSXNDYWxsZWUoXG4gICAgICAgICAgICAgICAgICAgICAgICBuZXcgdHlwZXMuQVZhbChydENYLmdsb2JhbE9iamVjdCksXG4gICAgICAgICAgICAgICAgICAgICAgICBhcmdBVmFscyxcbiAgICAgICAgICAgICAgICAgICAgICAgIHJlc0FWYWwsXG4gICAgICAgICAgICAgICAgICAgICAgICBjdXJTdGF0dXMuZXhjLFxuICAgICAgICAgICAgICAgICAgICAgICAgbmV3RGVsdGEpKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIHJldHVybiByZXNBVmFsO1xuICAgICAgICB9LFxuXG4gICAgICAgIE1lbWJlckV4cHJlc3Npb246IGZ1bmN0aW9uIChub2RlLCBjdXJTdGF0dXMsIGMpIHtcbiAgICAgICAgICAgIGNvbnN0IHJlY3ZBbmRSZXQgPSByZWFkTWVtYmVyKG5vZGUsIGN1clN0YXR1cywgYyk7XG4gICAgICAgICAgICByZXR1cm4gcmVjdkFuZFJldFsxXTtcbiAgICAgICAgfSxcblxuICAgICAgICBSZXR1cm5TdGF0ZW1lbnQ6IGZ1bmN0aW9uIChub2RlLCBjdXJTdGF0dXMsIGMpIHtcbiAgICAgICAgICAgIGlmICghbm9kZS5hcmd1bWVudCkgcmV0dXJuO1xuICAgICAgICAgICAgY29uc3QgcmV0ID0gYyhub2RlLmFyZ3VtZW50LCBjdXJTdGF0dXMsIHVuZGVmaW5lZCk7XG4gICAgICAgICAgICBjb25zdHJhaW50cy5wdXNoKHtGUk9NOiByZXQsXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICBUTzogY3VyU3RhdHVzLnJldH0pO1xuICAgICAgICAgICAgcmV0LnByb3BhZ2F0ZShjdXJTdGF0dXMucmV0KTtcbiAgICAgICAgfVxuICAgIH0pO1xuXG4gICAgcmVjdXJzaXZlV2l0aFJldHVybihhc3QsIGluaXRTdGF0dXMsIGNvbnN0cmFpbnRHZW5lcmF0b3IpO1xuXG4gICAgLy8gV2UgYWN0dWFsbHkgYWRkZWQgY29uc3RyYWludHNcbiAgICByZXR1cm4gdHJ1ZTtcbn1cblxuZnVuY3Rpb24gcmVjdXJzaXZlV2l0aFJldHVybihub2RlLCBzdGF0ZSwgdmlzaXRvcikge1xuICAgIGZ1bmN0aW9uIGMobm9kZSwgc3QsIG92ZXJyaWRlKSB7XG4gICAgICAgIHJldHVybiB2aXNpdG9yW292ZXJyaWRlIHx8IG5vZGUudHlwZV0obm9kZSwgc3QsIGMpO1xuICAgIH1cbiAgICByZXR1cm4gYyhub2RlLCBzdGF0ZSk7XG59XG5cbmV4cG9ydHMuY29uc3RyYWludHMgPSBjb25zdHJhaW50cztcbmV4cG9ydHMuYWRkQ29uc3RyYWludHMgPSBhZGRDb25zdHJhaW50cztcbmV4cG9ydHMuY2xlYXJDb25zdHJhaW50cyA9IGNsZWFyQ29uc3RyYWludHM7XG4iLCIndXNlIHN0cmljdCc7XG5cbmNvbnN0IHR5cGVzID0gcmVxdWlyZSgnLi4vZG9tYWlucy90eXBlcycpO1xuY29uc3Qgc3RhdHVzID0gcmVxdWlyZSgnLi4vZG9tYWlucy9zdGF0dXMnKTtcbmNvbnN0IGNHZW4gPSByZXF1aXJlKCcuL2NHZW4nKTtcblxuZnVuY3Rpb24gQ1NUUigpIHt9XG5DU1RSLnByb3RvdHlwZSA9IE9iamVjdC5jcmVhdGUobnVsbCk7XG5DU1RSLnByb3RvdHlwZS5lcXVhbHMgPSBmdW5jdGlvbiAob3RoZXIpIHtcbiAgICByZXR1cm4gdGhpcyA9PT0gb3RoZXI7XG59O1xuXG5mdW5jdGlvbiBSZWFkUHJvcChwcm9wLCB0bykge1xuICAgIHRoaXMucHJvcCA9IHByb3A7XG4gICAgdGhpcy50byA9IHRvO1xufVxuUmVhZFByb3AucHJvdG90eXBlID0gT2JqZWN0LmNyZWF0ZShDU1RSLnByb3RvdHlwZSk7XG5SZWFkUHJvcC5wcm90b3R5cGUuYWRkVHlwZSA9IGZ1bmN0aW9uIChvYmopIHtcbiAgICBpZiAoIShvYmogaW5zdGFuY2VvZiAodHlwZXMuT2JqVHlwZSkpKSByZXR1cm47XG4gICAgLy8gd2hlbiBvYmogaXMgT2JqVHlwZSxcbiAgICBjb25zdCBvd25Qcm9wID0gb2JqLmdldFByb3AodGhpcy5wcm9wLCB0cnVlKTtcbiAgICBpZiAob3duUHJvcCkge1xuICAgICAgICAvLyB3aGVuIHRoZSBvYmplY3QgaGFzIHRoZSBwcm9wLFxuICAgICAgICBvd25Qcm9wLnByb3BhZ2F0ZSh0aGlzLnRvKTtcbiAgICB9IGVsc2UgaWYgKG9iai5nZXRQcm9wKCdfX3Byb3RvX18nLCB0cnVlKSkge1xuICAgICAgICAvLyB1c2UgcHJvdG90eXBlIGNoYWluXG4gICAgICAgIG9iai5nZXRQcm9wKCdfX3Byb3RvX18nKVxuICAgICAgICAgIC5wcm9wYWdhdGUobmV3IFJlYWRQcm9wKHRoaXMucHJvcCwgdGhpcy50bykpO1xuICAgIH1cbn07XG5SZWFkUHJvcC5wcm90b3R5cGUuZXF1YWxzID0gZnVuY3Rpb24gKG90aGVyKSB7XG4gICAgaWYgKCEob3RoZXIgaW5zdGFuY2VvZiBSZWFkUHJvcCkpIHJldHVybiBmYWxzZTtcbiAgICByZXR1cm4gdGhpcy5wcm9wID09PSBvdGhlci5wcm9wXG4gICAgICAgICYmIHRoaXMudG8uZXF1YWxzKG90aGVyLnRvKTtcbn07XG5cbmZ1bmN0aW9uIFdyaXRlUHJvcChwcm9wLCBmcm9tKSB7XG4gICAgdGhpcy5wcm9wID0gcHJvcDtcbiAgICB0aGlzLmZyb20gPSBmcm9tO1xufVxuV3JpdGVQcm9wLnByb3RvdHlwZSA9IE9iamVjdC5jcmVhdGUoQ1NUUi5wcm90b3R5cGUpO1xuV3JpdGVQcm9wLnByb3RvdHlwZS5hZGRUeXBlID0gZnVuY3Rpb24gKG9iaikge1xuICAgIGlmICghKG9iaiBpbnN0YW5jZW9mICh0eXBlcy5PYmpUeXBlKSkpIHJldHVybjtcbiAgICBjb25zdCBvd25Qcm9wID0gb2JqLmdldFByb3AodGhpcy5wcm9wKTtcbiAgICB0aGlzLmZyb20ucHJvcGFnYXRlKG93blByb3ApO1xufTtcblxuZnVuY3Rpb24gSXNBZGRlZChvdGhlciwgdGFyZ2V0KSB7XG4gICAgdGhpcy5vdGhlciA9IG90aGVyO1xuICAgIHRoaXMudGFyZ2V0ID0gdGFyZ2V0O1xufVxuSXNBZGRlZC5wcm90b3R5cGUgPSBPYmplY3QuY3JlYXRlKENTVFIucHJvdG90eXBlKTtcbklzQWRkZWQucHJvdG90eXBlLmFkZFR5cGUgPSBmdW5jdGlvbiAodHlwZSkge1xuICAgIGlmICgodHlwZSA9PT0gdHlwZXMuUHJpbU51bWJlciBcbiAgICAgICAgIHx8IHR5cGUgPT09IHR5cGVzLlByaW1Cb29sZWFuKVxuICAgICAmJiAodGhpcy5vdGhlci5oYXNUeXBlKHR5cGVzLlByaW1OdW1iZXIpIFxuICAgICAgICAgfHwgdGhpcy5vdGhlci5oYXNUeXBlKHR5cGVzLlByaW1Cb29sZWFuKSkpIHtcbiAgICAgICAgdGhpcy50YXJnZXQuYWRkVHlwZSh0eXBlcy5QcmltTnVtYmVyKTtcbiAgICB9XG4gICAgaWYgKHR5cGUgPT09IHR5cGVzLlByaW1TdHJpbmdcbiAgICAgJiYgIXRoaXMub3RoZXIuaXNFbXB0eSgpKSB7XG4gICAgICAgICB0aGlzLnRhcmdldC5hZGRUeXBlKHR5cGVzLlByaW1TdHJpbmcpO1xuICAgIH1cbn07XG5cbmZ1bmN0aW9uIElzQ2FsbGVlKHNlbGYsIGFyZ3MsIHJldCwgZXhjLCBkZWx0YSkge1xuICAgIHRoaXMuc2VsZiA9IHNlbGY7XG4gICAgdGhpcy5hcmdzID0gYXJncztcbiAgICB0aGlzLnJldCA9IHJldDtcbiAgICB0aGlzLmV4YyA9IGV4YztcbiAgICB0aGlzLmRlbHRhID0gZGVsdGE7XG59XG5Jc0NhbGxlZS5wcm90b3R5cGUgPSBPYmplY3QuY3JlYXRlKENTVFIucHJvdG90eXBlKTtcbklzQ2FsbGVlLnByb3RvdHlwZS5hZGRUeXBlID0gZnVuY3Rpb24gKGYpIHtcbiAgICBpZiAoIShmIGluc3RhbmNlb2YgKHR5cGVzLkZuVHlwZSkpKSByZXR1cm47XG4gICAgY29uc3QgZnVuRW52ID0gZi5nZXRGdW5FbnYodGhpcy5kZWx0YSk7XG4gICAgY29uc3QgbmV3U0MgPSBmLm9yaWdpbk5vZGUuYm9keVsnQGJsb2NrJ10uZ2V0U2NvcGVJbnN0YW5jZShmLnNjLCB0aGlzLmRlbHRhKTtcbiAgICBjb25zdCBmdW5TdGF0dXNcbiAgICAgICAgPSBuZXcgc3RhdHVzLlN0YXR1cyhmdW5FbnZbMF0sIGZ1bkVudlsxXSwgZnVuRW52WzJdLCBcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICB0aGlzLmRlbHRhLCBuZXdTQyk7XG4gICAgLy8gcGFzcyB0aGlzIG9iamVjdFxuICAgIHRoaXMuc2VsZi5wcm9wYWdhdGUoZnVuRW52WzBdKTtcblxuICAgIGNvbnN0IG1pbkxlbiA9IE1hdGgubWluKHRoaXMuYXJncy5sZW5ndGgsIGYucGFyYW1OYW1lcy5sZW5ndGgpO1xuICAgIGZvciAobGV0IGkgPSAwOyBpIDwgbWluTGVuOyBpKyspIHtcbiAgICAgICAgdGhpcy5hcmdzW2ldLnByb3BhZ2F0ZShuZXdTQy5nZXRBVmFsT2YoZi5wYXJhbU5hbWVzW2ldKSk7XG4gICAgfVxuXG4gICAgLy8gZm9yIGFyZ3VtZW50cyBvYmplY3RcbiAgICBpZiAoZi5vcmlnaW5Ob2RlLmJvZHlbJ0BibG9jayddLnVzZUFyZ3VtZW50c09iamVjdCkge1xuICAgICAgICBjb25zdCBhcmdPYmogPSBmLmdldEFyZ3VtZW50c09iamVjdCh0aGlzLmRlbHRhKTtcbiAgICAgICAgbmV3U0MuZ2V0QVZhbE9mKCdhcmd1bWVudHMnKS5hZGRUeXBlKGFyZ09iaik7XG4gICAgICAgIGZvciAobGV0IGkgPSAwOyBpIDwgdGhpcy5hcmdzLmxlbmd0aDsgaSsrKSB7XG4gICAgICAgICAgICB0aGlzLmFyZ3NbaV0ucHJvcGFnYXRlKGFyZ09iai5nZXRQcm9wKGkgKyAnJykpO1xuICAgICAgICAgICAgdGhpcy5hcmdzW2ldLnByb3BhZ2F0ZShhcmdPYmouZ2V0UHJvcChudWxsKSk7XG4gICAgICAgIH1cbiAgICAgICAgYXJnT2JqLmdldFByb3AoJ2NhbGxlZScpLmFkZFR5cGUoZik7XG4gICAgICAgIGFyZ09iai5nZXRQcm9wKCdsZW5ndGgnKS5hZGRUeXBlKHR5cGVzLlByaW1OdW1iZXIpO1xuICAgIH1cblxuICAgIC8vIGNvbnN0cmFpbnQgZ2VuZXJhdGlvbiBmb3IgdGhlIGZ1bmN0aW9uIGJvZHlcbiAgICBjR2VuLmFkZENvbnN0cmFpbnRzKGYub3JpZ2luTm9kZS5ib2R5LCBmdW5TdGF0dXMpO1xuXG4gICAgLy8gZ2V0IHJldHVybiBcbiAgICBmdW5FbnZbMV0ucHJvcGFnYXRlKHRoaXMucmV0KTtcbiAgICAvLyBnZXQgZXhjZXB0aW9uXG4gICAgZnVuRW52WzJdLnByb3BhZ2F0ZSh0aGlzLmV4Yyk7XG59O1xuXG5mdW5jdGlvbiBJc0N0b3IoYXJncywgcmV0LCBleGMsIGRlbHRhKSB7XG4gICAgdGhpcy5hcmdzID0gYXJncztcbiAgICB0aGlzLnJldCA9IHJldDtcbiAgICB0aGlzLmV4YyA9IGV4YztcbiAgICB0aGlzLmRlbHRhID0gZGVsdGE7XG59XG5Jc0N0b3IucHJvdG90eXBlID0gT2JqZWN0LmNyZWF0ZShDU1RSLnByb3RvdHlwZSk7XG5Jc0N0b3IucHJvdG90eXBlLmFkZFR5cGUgPSBmdW5jdGlvbiAoZikge1xuICAgIGlmICghKGYgaW5zdGFuY2VvZiAodHlwZXMuRm5UeXBlKSkpIHJldHVybjtcbiAgICBjb25zdCBmdW5FbnYgPSBmLmdldEZ1bkVudih0aGlzLmRlbHRhKTtcbiAgICBjb25zdCBuZXdTQyA9IGYub3JpZ2luTm9kZS5ib2R5WydAYmxvY2snXS5nZXRTY29wZUluc3RhbmNlKGYuc2MsIHRoaXMuZGVsdGEpO1xuICAgIGNvbnN0IGZ1blN0YXR1c1xuICAgICAgICA9IG5ldyBzdGF0dXMuU3RhdHVzKGZ1bkVudlswXSwgbmV3IElmT2JqVHlwZShmdW5FbnZbMV0pLCBmdW5FbnZbMl0sXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgdGhpcy5kZWx0YSwgbmV3U0MpO1xuICAgIC8vIHBhc3MgdGhpcyBvYmplY3RcbiAgICBjb25zdCBuZXdPYmogPSBmLmdldEluc3RhbmNlKCk7XG4gICAgZnVuRW52WzBdLmFkZFR5cGUobmV3T2JqKTtcblxuICAgIGNvbnN0IG1pbkxlbiA9IE1hdGgubWluKHRoaXMuYXJncy5sZW5ndGgsIGYucGFyYW1OYW1lcy5sZW5ndGgpO1xuICAgIGZvciAobGV0IGkgPSAwOyBpIDwgbWluTGVuOyBpKyspIHtcbiAgICAgICAgdGhpcy5hcmdzW2ldLnByb3BhZ2F0ZShuZXdTQy5nZXRBVmFsT2YoZi5wYXJhbU5hbWVzW2ldKSk7XG4gICAgfVxuXG4gICAgLy8gZm9yIGFyZ3VtZW50cyBvYmplY3RcbiAgICBpZiAoZi5vcmlnaW5Ob2RlLmJvZHlbJ0BibG9jayddLnVzZUFyZ3VtZW50c09iamVjdCkge1xuICAgICAgICBjb25zdCBhcmdPYmogPSBmLmdldEFyZ3VtZW50c09iamVjdCh0aGlzLmRlbHRhKTtcbiAgICAgICAgbmV3U0MuZ2V0QVZhbE9mKCdhcmd1bWVudHMnKS5hZGRUeXBlKGFyZ09iaik7XG4gICAgICAgIGZvciAobGV0IGkgPSAwOyBpIDwgdGhpcy5hcmdzLmxlbmd0aDsgaSsrKSB7XG4gICAgICAgICAgICB0aGlzLmFyZ3NbaV0ucHJvcGFnYXRlKGFyZ09iai5nZXRQcm9wKGkgKyAnJykpO1xuICAgICAgICAgICAgdGhpcy5hcmdzW2ldLnByb3BhZ2F0ZShhcmdPYmouZ2V0UHJvcChudWxsKSk7XG4gICAgICAgIH1cbiAgICAgICAgYXJnT2JqLmdldFByb3AoJ2NhbGxlZScpLmFkZFR5cGUoZik7XG4gICAgICAgIGFyZ09iai5nZXRQcm9wKCdsZW5ndGgnKS5hZGRUeXBlKHR5cGVzLlByaW1OdW1iZXIpO1xuICAgIH1cblxuICAgIC8vIGNvbnN0cmFpbnQgZ2VuZXJhdGlvbiBmb3IgdGhlIGZ1bmN0aW9uIGJvZHlcbiAgICBjR2VuLmFkZENvbnN0cmFpbnRzKGYub3JpZ2luTm9kZS5ib2R5LCBmdW5TdGF0dXMpO1xuXG4gICAgLy8gYnkgZXhwbGljaXQgcmV0dXJuLCBvbmx5IE9ialR5cGUgYXJlIHByb3BhZ2F0ZWRcbiAgICBmdW5FbnZbMV0ucHJvcGFnYXRlKHRoaXMucmV0KTtcbiAgICAvLyByZXR1cm4gbmV3IG9iamVjdFxuICAgIHRoaXMucmV0LmFkZFR5cGUobmV3T2JqKTtcbiAgICAvLyBnZXQgZXhjZXB0aW9uXG4gICAgZnVuRW52WzJdLnByb3BhZ2F0ZSh0aGlzLmV4Yyk7XG59O1xuXG4vLyBpZ25vcmUgbm9uIG9iamVjdCB0eXBlc1xuZnVuY3Rpb24gSWZPYmpUeXBlKGF2YWwpIHtcbiAgICB0aGlzLmF2YWwgPSBhdmFsO1xufVxuSWZPYmpUeXBlLnByb3RvdHlwZSA9IE9iamVjdC5jcmVhdGUoQ1NUUi5wcm90b3R5cGUpO1xuSWZPYmpUeXBlLnByb3RvdHlwZS5hZGRUeXBlID0gZnVuY3Rpb24gKHR5cGUpIHtcbiAgICBpZiAoISh0eXBlIGluc3RhbmNlb2YgdHlwZXMuT2JqVHlwZSkpIHJldHVybjtcbiAgICB0aGlzLmF2YWwuYWRkVHlwZSh0eXBlKTtcbn07XG5cbmV4cG9ydHMuUmVhZFByb3AgPSBSZWFkUHJvcDtcbmV4cG9ydHMuV3JpdGVQcm9wID0gV3JpdGVQcm9wO1xuZXhwb3J0cy5Jc0FkZGVkID0gSXNBZGRlZDtcbmV4cG9ydHMuSXNDYWxsZWUgPSBJc0NhbGxlZTtcbmV4cG9ydHMuSXNDdG9yID0gSXNDdG9yO1xuIiwiLy8gQ29udGV4dCBmb3Igay1DRkEgYW5hbHlzaXNcbi8vXG4vLyBBc3N1bWUgYSBjb250ZXh0IGlzIGFuIGFycmF5IG9mIG51bWJlcnMuXG4vLyBBIG51bWJlciBpbiBzdWNoIGxpc3QgZGVub3RlcyBhIGNhbGwgc2l0ZSwgdGhhdCBpcyBAbGFiZWwgb2YgYSBDYWxsRXhwcmVzc2lvbi5cbi8vIFdlIGtlZXAgdGhlIG1vc3QgcmVjZW50ICdrJyBjYWxsc2l0ZXMuXG4vLyBFcXVhbGl0eSBvbiBjb250ZXh0cyBzaG91bGQgbG9vayBpbnRvIHRoZSBudW1iZXJzLlxuXG52YXIgY2FsbFNpdGVDb250ZXh0UGFyYW1ldGVyID0ge1xuICAgIC8vIG1heGltdW0gbGVuZ3RoIG9mIGNvbnRleHRcbiAgICBtYXhEZXB0aEs6IDAsXG4gICAgLy8gZnVuY3Rpb24gbGlzdCBmb3Igc2Vuc2l0aXZlIGFuYWx5c2lzXG4gICAgc2Vuc0Z1bmNzOiB7fVxufTtcblxuZnVuY3Rpb24gQ2FsbFNpdGVDb250ZXh0KGNzTGlzdCkge1xuICAgIGlmIChjc0xpc3QpIHRoaXMuY3NMaXN0ID0gY3NMaXN0O1xuICAgIGVsc2UgdGhpcy5jc0xpc3QgPSBbXTtcbn1cblxuQ2FsbFNpdGVDb250ZXh0LnByb3RvdHlwZS5lcXVhbHMgPSBmdW5jdGlvbiAob3RoZXIpIHtcbiAgICBpZiAodGhpcy5jc0xpc3QubGVuZ3RoICE9IG90aGVyLmNzTGlzdC5sZW5ndGgpIHJldHVybiBmYWxzZTtcbiAgICBmb3IgKHZhciBpID0gMDsgaSA8IHRoaXMuY3NMaXN0Lmxlbmd0aDsgaSsrKSB7XG4gICAgICAgIGlmICh0aGlzLmNzTGlzdFtpXSAhPT0gb3RoZXIuY3NMaXN0W2ldKSByZXR1cm4gZmFsc2U7XG4gICAgfVxuICAgIHJldHVybiB0cnVlO1xufTtcblxuQ2FsbFNpdGVDb250ZXh0LnByb3RvdHlwZS5hcHBlbmRPbmUgPSBmdW5jdGlvbiAoY2FsbFNpdGUpIHtcbiAgICAvLyB1c2UgY29uY2F0IHRvIGNyZWF0ZSBhIG5ldyBhcnJheVxuICAgIC8vIG9sZGVzdCBvbmUgY29tZXMgZmlyc3RcbiAgICB2YXIgYXBwZW5kZWQgPSB0aGlzLmNzTGlzdC5jb25jYXQoY2FsbFNpdGUpO1xuICAgIGlmIChhcHBlbmRlZC5sZW5ndGggPiBjYWxsU2l0ZUNvbnRleHRQYXJhbWV0ZXIubWF4RGVwdGhLKSB7XG4gICAgICAgIGFwcGVuZGVkLnNoaWZ0KCk7XG4gICAgfVxuICAgIHJldHVybiBuZXcgQ2FsbFNpdGVDb250ZXh0KGFwcGVuZGVkKTtcbn07XG5cbkNhbGxTaXRlQ29udGV4dC5wcm90b3R5cGUudG9TdHJpbmcgPSBmdW5jdGlvbiAoKSB7XG4gICAgcmV0dXJuIHRoaXMuY3NMaXN0LnRvU3RyaW5nKCk7XG59O1xuXG5leHBvcnRzLmNhbGxTaXRlQ29udGV4dFBhcmFtZXRlciA9IGNhbGxTaXRlQ29udGV4dFBhcmFtZXRlcjtcbmV4cG9ydHMuQ2FsbFNpdGVDb250ZXh0ID0gQ2FsbFNpdGVDb250ZXh0OyIsIi8vIFN0YXR1czpcbi8vIHsgc2VsZiAgOiBBVmFsLFxuLy8gICByZXQgICA6IEFWYWwsXG4vLyAgIGV4YyAgIDogQVZhbCxcbi8vICAgZGVsdGEgOiBDb250ZXh0LFxuLy8gICBzYyAgICA6IFNjb3BlQ2hhaW4gfVxuXG5mdW5jdGlvbiBTdGF0dXMoc2VsZiwgcmV0LCBleGMsIGRlbHRhLCBzYykge1xuICAgIHRoaXMuc2VsZiA9IHNlbGY7XG4gICAgdGhpcy5yZXQgPSByZXQ7XG4gICAgdGhpcy5leGMgPSBleGM7XG4gICAgdGhpcy5kZWx0YSA9IGRlbHRhO1xuICAgIHRoaXMuc2MgPSBzYztcbn1cblxuU3RhdHVzLnByb3RvdHlwZS5lcXVhbHMgPSBmdW5jdGlvbiAob3RoZXIpIHtcbiAgICByZXR1cm4gdGhpcy5zZWxmID09PSBvdGhlci5zZWxmICYmXG4gICAgICAgIHRoaXMucmV0ID09PSBvdGhlci5yZXQgJiZcbiAgICAgICAgdGhpcy5leGMgPT09IG90aGVyLmV4YyAmJlxuICAgICAgICB0aGlzLmRlbHRhLmVxdWFscyhvdGhlci5kZWx0YSkgJiZcbiAgICAgICAgdGhpcy5zYyA9PT0gb3RoZXIuc2M7XG59O1xuXG5leHBvcnRzLlN0YXR1cyA9IFN0YXR1czsiLCIndXNlIHN0cmljdCc7XG5cbi8vIGZvciBERUJVR1xudmFyIGNvdW50ID0gMDtcbi8qKlxuICogdGhlIGFic3RyYWN0IHZhbHVlIGZvciBhIGNvbmNyZXRlIHZhbHVlXG4gKiB3aGljaCBpcyBhIHNldCBvZiB0eXBlcy5cbiAqIEBjb25zdHJ1Y3RvclxuICogQHBhcmFtIHtUeXBlfSB0eXBlIC0gZ2l2ZSBhIHR5cGUgdG8gbWFrZSBBVmFsIHdpdGggYSBzaW5nbGUgdHlwZVxuICovXG5mdW5jdGlvbiBBVmFsKHR5cGUpIHtcbiAgICAvLyB0eXBlOiBjb250YWluZWQgdHlwZXNcbiAgICAvLyBXZSBhc3N1bWUgdHlwZXMgYXJlIGRpc3Rpbmd1aXNoYWJsZSBieSAnPT09J1xuICAgIGlmICh0eXBlKSB0aGlzLnR5cGVzID0gbmV3IFNldChbdHlwZV0pO1xuICAgIGVsc2UgdGhpcy50eXBlcyA9IG5ldyBTZXQoKTtcbiAgICAvLyBmb3J3YXJkczogcHJvcGFnYXRpb24gdGFyZ2V0c1xuICAgIC8vIFdlIGFzc3VtZSB0YXJnZXRzIGFyZSBkaXN0aW5ndWlzaGFibGUgYnkgJ2VxdWFscycgbWV0aG9kXG4gICAgdGhpcy5mb3J3YXJkcyA9IG5ldyBTZXQoKTtcbiAgICAvLyBmb3IgREVCVUdcbiAgICB0aGlzLl9pZCA9IGNvdW50Kys7XG59XG4vKiogQ2hlY2sgd2hldGhlciBpdCBoYXMgYW55IHR5cGVcbiAqIEByZXR1cm5zIHtib29sZWFufVxuICovXG5BVmFsLnByb3RvdHlwZS5pc0VtcHR5ID0gZnVuY3Rpb24gKCkge1xuICAgIHJldHVybiB0aGlzLnR5cGVzLnNpemUgPT09IDA7XG59O1xuXG4vKipcbiAqIEByZXR1cm5zIHtbVHlwZV19XG4gKi9cbkFWYWwucHJvdG90eXBlLmdldFR5cGVzID0gZnVuY3Rpb24gKCkge1xuICAgIHJldHVybiB0aGlzLnR5cGVzO1xufTtcblxuLyoqXG4gKiBAcmV0dXJucyB7Ym9vbGVhbn1cbiAqL1xuQVZhbC5wcm90b3R5cGUuaGFzVHlwZSA9IGZ1bmN0aW9uICh0eXBlKSB7XG4gICAgcmV0dXJuIHRoaXMudHlwZXMuaGFzKHR5cGUpO1xufTtcblxuLyoqXG4gKiBBZGQgYSB0eXBlLlxuICogQHBhcmFtIHtUeXBlfSB0eXBlXG4gKi9cbkFWYWwucHJvdG90eXBlLmFkZFR5cGUgPSBmdW5jdGlvbiAodHlwZSkge1xuICAgIGlmICh0aGlzLnR5cGVzLmhhcyh0eXBlKSkgcmV0dXJuO1xuICAgIC8vIGdpdmVuIHR5cGUgaXMgbmV3XG4gICAgdGhpcy50eXBlcy5hZGQodHlwZSk7XG4gICAgLy8gc2VuZCB0byBwcm9wYWdhdGlvbiB0YXJnYXRzXG4gICAgdGhpcy5mb3J3YXJkcy5mb3JFYWNoKGZ1bmN0aW9uIChmd2QpIHtcbiAgICAgICAgZndkLmFkZFR5cGUodHlwZSk7XG4gICAgfSk7XG59O1xuLyoqXG4gKiBAcGFyYW0ge0FWYWx9IHRhcmdldFxuICovXG5BVmFsLnByb3RvdHlwZS5wcm9wYWdhdGUgPSBmdW5jdGlvbiAodGFyZ2V0KSB7XG4gICAgaWYgKCF0aGlzLmFkZEZvcndhcmQodGFyZ2V0KSkgcmV0dXJuO1xuICAgIC8vIHRhcmdldCBpcyBuZXdseSBhZGRlZFxuICAgIC8vIHNlbmQgdHlwZXMgdG8gdGhlIG5ldyB0YXJnZXRcbiAgICB0aGlzLnR5cGVzLmZvckVhY2goZnVuY3Rpb24gKHR5cGUpIHtcbiAgICAgICAgdGFyZ2V0LmFkZFR5cGUodHlwZSk7XG4gICAgfSk7XG59O1xuXG5BVmFsLnByb3RvdHlwZS5hZGRGb3J3YXJkID0gZnVuY3Rpb24gKGZ3ZCkge1xuICAgIGZvciAobGV0IG9sZEZ3ZCBvZiB0aGlzLmZvcndhcmRzKSB7XG4gICAgICAgIGlmIChmd2QuZXF1YWxzKG9sZEZ3ZCkpIHJldHVybiBmYWxzZTtcbiAgICB9XG4gICAgdGhpcy5mb3J3YXJkcy5hZGQoZndkKTtcbiAgICByZXR1cm4gdHJ1ZTtcbn07XG5cbkFWYWwucHJvdG90eXBlLmVxdWFscyA9IGZ1bmN0aW9uIChvdGhlcikge1xuICAgIC8vIHNpbXBsZSByZWZlcmVuY2UgY29tcGFyaXNvblxuICAgIHJldHVybiB0aGlzID09PSBvdGhlcjtcbn07XG5cbi8qKlxuICogVE9ETzogY2hlY2sgd2hldGhlciB3ZSByZWFsbHkgbmVlZCB0aGlzIG1ldGhvZC5cbiAqIEBwYXJhbSB7c3RyaW5nfSBwcm9wXG4gKiBAcmV0dXJucyB7QVZhbH1cbiAqL1xuQVZhbC5wcm90b3R5cGUuZ2V0UHJvcCA9IGZ1bmN0aW9uIChwcm9wKSB7XG4gICAgaWYgKHByb3AgPT09ICfinJYnKSB7XG4gICAgICAgIC8vIOKcliBpcyB0aGUgYm9ndXMgcHJvcGVydHkgbmFtZSBhZGRlZCBmb3IgZXJyb3IgcmVjb3ZlcnkuXG4gICAgICAgIHJldHVybiBBVmFsTnVsbDtcbiAgICB9XG4gICAgaWYgKHRoaXMucHJvcHMuaGFzKHByb3ApKSB7XG4gICAgICAgIHJldHVybiB0aGlzLnByb3BzLmdldChwcm9wKTtcbiAgICB9IGVsc2Uge1xuICAgICAgICByZXR1cm4gQVZhbE51bGw7XG4gICAgfVxufTtcblxuLyoqXG4gKiB0aGUgc3VwZXIgY2xhc3Mgb2YgYWxsIHR5cGVzXG4gKiBlYWNoIHR5cGUgc2hvdWxkIGJlIGRpc3Rpbmd1aXNoYWJsZSBieSAnPT09JyBvcGVyYXRpb24uXG4gKiBAY29uc3RydWN0b3JcbiAqL1xuZnVuY3Rpb24gVHlwZSgpIHt9XG5UeXBlLnByb3RvdHlwZSA9IE9iamVjdC5jcmVhdGUobnVsbCk7XG5cbi8qKlxuICogMS4gb2JqZWN0IHR5cGVzXG4gKiBAcGFyYW0ge0FWYWx9IHByb3RvIC0gQVZhbCBvZiBjb25zdHJ1Y3RvcidzIHByb3RvdHlwZVxuICogQHBhcmFtIHtzdHJpbmd9IG5hbWUgLSBndWVzc2VkIG5hbWVcbiAqL1xuZnVuY3Rpb24gT2JqVHlwZShwcm90bywgbmFtZSkge1xuICAgIHRoaXMubmFtZSA9IG5hbWU7XG4gICAgdGhpcy5wcm9wcyA9IG5ldyBNYXAoKTtcblxuICAgIC8vIHNoYXJlIHByb3RvIHdpdGggX19wcm90b19fXG4gICAgdGhpcy5zZXRQcm9wKCdfX3Byb3RvX18nLCBwcm90byk7XG59XG5PYmpUeXBlLnByb3RvdHlwZSA9IE9iamVjdC5jcmVhdGUoVHlwZS5wcm90b3R5cGUpO1xuLyoqXG4gKiBAcGFyYW0ge3N0cmluZ3xudWxsfSBwcm9wIC0gbnVsbCBmb3IgY29tcHV0ZWQgcHJvcHNcbiAqIEBwYXJhbSB7Ym9vbGVhbn0gcmVhZE9ubHkgLSBpZiBmYWxzZSwgY3JlYXRlIEFWYWwgZm9yIHByb3AgaWYgbmVjZXNzYXJ5XG4gKiBAcmV0dXJucyB7QVZhbH0gQVZhbCBvZiB0aGUgcHJvcGVydHlcbiAqL1xuT2JqVHlwZS5wcm90b3R5cGUuZ2V0UHJvcCA9IGZ1bmN0aW9uIChwcm9wLCByZWFkT25seSkge1xuICAgIGlmIChwcm9wID09PSAn4pyWJykge1xuICAgICAgICAvLyDinJYgaXMgdGhlIGJvZ3VzIHByb3BlcnR5IG5hbWUgYWRkZWQgZHVyaW5nIHBhcnNpbmcgZXJyb3IgcmVjb3ZlcnkuXG4gICAgICAgIHJldHVybiBBVmFsTnVsbDtcbiAgICB9XG4gICAgaWYgKHRoaXMucHJvcHMuaGFzKHByb3ApKSB7XG4gICAgICAgIHJldHVybiB0aGlzLnByb3BzLmdldChwcm9wKTtcbiAgICB9IGVsc2UgaWYgKHJlYWRPbmx5KSB7XG4gICAgICAgIHJldHVybiBudWxsO1xuICAgIH0gZWxzZSB7XG4gICAgICAgIHZhciBuZXdQcm9wQVZhbCA9IG5ldyBBVmFsO1xuICAgICAgICB0aGlzLnByb3BzLnNldChwcm9wLCBuZXdQcm9wQVZhbCk7XG4gICAgICAgIHJldHVybiBuZXdQcm9wQVZhbDtcbiAgICB9XG59O1xuLyoqXG4gKiBXZSB1c2UgdGhpcyBmdW5jdGlvbiB0byBzaGFyZSAucHJvdG90eXBlIHdpdGggaW5zdGFuY2VzIF9fcHJvdG9fX1xuICogSXQgaXMgcG9zc2libGUgdG8gdXNlIHRoaXMgZnVuY3Rpb24gdG8gbWVyZ2UgQVZhbHMgdG8gb3B0aW1pemUgdGhlIGFuYWx5emVyLlxuICogQHBhcmFtIHtzdHJpbmd8bnVsbH0gcHJvcCAtIG51bGwgZm9yIGNvbXB1dGVkIHByb3BzXG4gKiBAcGFyYW0ge0FWYWx9IGF2YWxcbiAqL1xuT2JqVHlwZS5wcm90b3R5cGUuc2V0UHJvcCA9IGZ1bmN0aW9uIChwcm9wLCBhdmFsKSB7XG4gICAgaWYgKHByb3AgPT09ICfinJYnKSB7XG4gICAgICAgIC8vIOKcliBpcyB0aGUgYm9ndXMgcHJvcGVydHkgbmFtZSBhZGRlZCBkdXJpbmcgcGFyc2luZyBlcnJvciByZWNvdmVyeS5cbiAgICAgICAgcmV0dXJuO1xuICAgIH1cbiAgICB0aGlzLnByb3BzLnNldChwcm9wLCBhdmFsKTtcbn07XG4vKipcbiAqIFRPRE86IENoZWNrIHRoaXMgZnVuY3Rpb24ncyBuZWNlc3NpdHlcbiAqIEBwYXJhbSB7c3RyaW5nfSBwcm9wXG4gKiBAcmV0dXJucyB7Ym9vbGVhbn1cbiAqL1xuT2JqVHlwZS5wcm90b3R5cGUuaGFzUHJvcCA9IGZ1bmN0aW9uIChwcm9wKSB7XG4gICAgaWYgKHByb3AgPT09ICfinJYnKSByZXR1cm4gZmFsc2U7XG4gICAgcmV0dXJuIHRoaXMucHJvcHMuaGFzKHByb3ApO1xufTtcbi8qKlxuICogVE9ETzogQ2hlY2sgdGhpcyBmdW5jdGlvbidzIG5lY2Vzc2l0eVxuICogQHBhcmFtIHtUeXBlfSB0eXBlXG4gKiBAcGFyYW0ge3N0cmluZ30gcHJvcFxuICovXG5PYmpUeXBlLnByb3RvdHlwZS5hZGRUeXBlVG9Qcm9wID0gZnVuY3Rpb24gKHR5cGUsIHByb3ApIHtcbiAgICBpZiAocHJvcCA9PT0gJ+KclicpIHJldHVybjtcbiAgICBpZiAoIXRoaXMucHJvcHMuaGFzKHByb3ApKSB7XG4gICAgICAgIHRoaXMucHJvcHMuc2V0KHByb3AsIG5ldyBBVmFsKTtcbiAgICB9XG4gICAgaWYgKHRoaXMucHJvcHMuZ2V0KHByb3ApLmhhc1R5cGUodHlwZSkpIHJldHVybjtcbiAgICB0aGlzLnByb3BzLmdldChwcm9wKS5hZGRUeXBlKHR5cGUpO1xufTtcbi8qKlxuICogVE9ETzogQ2hlY2sgdGhpcyBmdW5jdGlvbidzIG5lY2Vzc2l0eVxuICogQHBhcmFtIHtBVmFsfSBhdmFsXG4gKiBAcGFyYW0ge3N0cmluZ30gcHJvcFxuICovXG5PYmpUeXBlLnByb3RvdHlwZS5qb2luQVZhbFRvUHJvcCA9IGZ1bmN0aW9uIChhdmFsLCBwcm9wKSB7XG4gICAgdmFyIHNlbGYgPSB0aGlzO1xuICAgIGF2YWwuZ2V0VHlwZXMoKS5mb3JFYWNoKGZ1bmN0aW9uICh0eXBlKSB7XG4gICAgICAgIHNlbGYuYWRkVHlwZVRvUHJvcCh0eXBlLCBwcm9wKTtcbiAgICB9KTtcbn07XG5cbi8vIG1ha2UgYW4gT2JqIGZyb20gdGhlIGdsb2JhbCBzY29wZVxuZnVuY3Rpb24gbWtPYmpGcm9tR2xvYmFsU2NvcGUoZ1Njb3BlKSB7XG4gICAgdmFyIGdPYmogPSBuZXcgT2JqVHlwZShBVmFsTnVsbCwgJypnbG9iYWwgc2NvcGUqJyk7XG4gICAgZ09iai5wcm9wcyA9IGdTY29wZS52YXJNYXA7XG4gICAgLy8gT3ZlcnJpZGUgZ2V0UHJvcCBtZXRob2QgZm9yIGdsb2JhbCBvYmplY3RcbiAgICAvLyBXZSBpZ25vcmUgJ3JlYWRPbmx5JyBwYXJhbWV0ZXIgdG8gYWx3YXlzIHJldHVybiBpdHMgb3duIHByb3AgQVZhbCBcbiAgICBnT2JqLmdldFByb3AgPSBmdW5jdGlvbiAocHJvcCkge1xuICAgICAgICByZXR1cm4gT2JqVHlwZS5wcm90b3R5cGUuZ2V0UHJvcC5jYWxsKHRoaXMsIHByb3ApO1xuICAgIH07XG4gICAgcmV0dXJuIGdPYmo7XG59XG5cbi8qKlxuICogMi4gcHJpbWl0aXZlIHR5cGVzXG4gKiBAY29uc3RydWN0b3JcbiAqIEBwYXJhbSB7c3RyaW5nfSBuYW1lXG4gKi9cbmZ1bmN0aW9uIFByaW1UeXBlKG5hbWUpIHtcbiAgICB0aGlzLm5hbWUgPSBuYW1lO1xufVxuUHJpbVR5cGUucHJvdG90eXBlID0gT2JqZWN0LmNyZWF0ZShUeXBlLnByb3RvdHlwZSk7XG5cbi8qKlxuICogMy4gZnVuY3Rpb24gdHlwZXNcbiAqIHRoZSBuYW1lIGlzIHVzZWQgZm9yIHRoZSB0eXBlIG9mIHRoZSBpbnN0YW5jZXMgZnJvbSB0aGUgZnVuY3Rpb25cbiAqIEBjb25zdHJ1Y3RvclxuICogQHBhcmFtIHtBVmFsfSBmbl9wcm90byAtIEFWYWwgZm9yIGNvbnN0cnVjdG9yJ3MgLnByb3RvdHlwZVxuICogQHBhcmFtIHtzdHJpbmd9IG5hbWUgLSBndWVzc2VkIG5hbWVcbiAqIEBwYXJhbSB7W3N0cmluZ119IGFyZ05hbWVzIC0gbGlzdCBvZiBwYXJhbWV0ZXIgbmFtZXNcbiAqIEBwYXJhbSB7U2NvcGV9IHNjIC0gZnVuY3Rpb25zIHNjb3BlIGNoYWluLCBvciBjbG9zdXJlXG4gKiBAcGFyYW0ge25vZGV9IG9yaWdpbk5vZGUgLSBBU1Qgbm9kZSBmb3IgdGhlIGZ1bmN0aW9uXG4gKiBAcGFyYW0ge1R5cGV9IGFyZ1Byb3RvIC0gcHJvdG90eXBlIGZvciBhcmd1bWVudHMgb2JqZWN0XG4gKi9cbmZ1bmN0aW9uIEZuVHlwZShmbl9wcm90bywgbmFtZSwgYXJnTmFtZXMsIHNjLCBvcmlnaW5Ob2RlLCBhcmdQcm90bykge1xuICAgIE9ialR5cGUuY2FsbCh0aGlzLCBmbl9wcm90bywgbmFtZSk7XG4gICAgdGhpcy5wYXJhbU5hbWVzID0gYXJnTmFtZXM7XG4gICAgdGhpcy5zYyA9IHNjO1xuICAgIHRoaXMub3JpZ2luTm9kZSA9IG9yaWdpbk5vZGU7XG4gICAgdGhpcy5hcmdQcm90byA9IGFyZ1Byb3RvO1xuICAgIC8vIGZ1bkVudiA6IENhbGxDb250ZXh0IC0+IFtzZWxmLCByZXQsIGV4Y11cbiAgICB0aGlzLmZ1bkVudiA9IG5ldyBNYXA7XG59XG5GblR5cGUucHJvdG90eXBlID0gT2JqZWN0LmNyZWF0ZShPYmpUeXBlLnByb3RvdHlwZSk7XG5cbi8qKlxuICogY29uc3RydWN0IFN0YXR1cyBmb3IgZnVuY3Rpb25cbiAqIEBwYXJhbSB7Q2FsbENvbnRleHR9IGRlbHRhIC0gY2FsbCBjb250ZXh0XG4gKiBAcmV0dXJucyB7W0FWYWwsIEFWYWwsIEFWYWxdfSAtIGZvciBzZWxmLCByZXR1cm4gYW5kIGV4Y2VwdGlvbiBBVmFsc1xuICovXG5GblR5cGUucHJvdG90eXBlLmdldEZ1bkVudiA9IGZ1bmN0aW9uIChkZWx0YSkge1xuICAgIGlmICh0aGlzLmZ1bkVudi5oYXMoZGVsdGEpKSB7XG4gICAgICAgIHJldHVybiB0aGlzLmZ1bkVudi5nZXQoZGVsdGEpO1xuICAgIH0gZWxzZSB7XG4gICAgICAgIHZhciB0cmlwbGUgPSBbbmV3IEFWYWwsIG5ldyBBVmFsLCBuZXcgQVZhbF07XG4gICAgICAgIHRoaXMuZnVuRW52LnNldChkZWx0YSwgdHJpcGxlKTtcbiAgICAgICAgcmV0dXJuIHRyaXBsZTtcbiAgICB9XG59O1xuXG5GblR5cGUucHJvdG90eXBlLmdldEFyZ3VtZW50c09iamVjdCA9IGZ1bmN0aW9uIChkZWx0YSkge1xuICAgIHRoaXMuYXJnT2JqTWFwID0gdGhpcy5hcmdPYmpNYXAgfHwgbmV3IE1hcDtcbiAgICBpZiAodGhpcy5hcmdPYmpNYXAuaGFzKGRlbHRhKSkge1xuICAgICAgICByZXR1cm4gdGhpcy5hcmdPYmpNYXAuZ2V0KGRlbHRhKTtcbiAgICB9IGVsc2Uge1xuICAgICAgICB2YXIgYXJnT2JqID0gbmV3IE9ialR5cGUobmV3IEFWYWwodGhpcy5hcmdQcm90byksICcqYXJndW1lbnRzIG9iamVjdConKTtcbiAgICAgICAgdGhpcy5hcmdPYmpNYXAuc2V0KGRlbHRhLCBhcmdPYmopO1xuICAgICAgICByZXR1cm4gYXJnT2JqO1xuICAgIH1cbn07XG5cbi8qKlxuICogZ2V0IE9iamVjdCBtYWRlIGJ5IHRoZSBmdW5jdGlvblxuICogVE9ETzogdXNlIGFkZGl0aW9uYWwgaW5mb3JtYXRpb24gdG8gY3JlYXRlIG11bHRpcGxlIGluc3RhbmNlc1xuICogQHJldHVybnMge09ialR5cGV9XG4gKi9cbkZuVHlwZS5wcm90b3R5cGUuZ2V0SW5zdGFuY2UgPSBmdW5jdGlvbiAoKSB7XG4gICAgLy8gb2JqSW5zdGFuY2UgaXMgdGhlIG9iamVjdCBtYWRlIGJ5IHRoZSBmdW5jdGlvYW5uXG4gICAgaWYgKHRoaXMub2JqSW5zdGFuY2UpIHJldHVybiB0aGlzLm9iakluc3RhbmNlO1xuICAgIC8vIHdlIHVuaWZ5IGNvbnN0cnVjdG9yJ3MgLnByb3RvdHlwZSBhbmQgaW5zdGFuY2UncyBfX3Byb3RvX19cbiAgICB0aGlzLm9iakluc3RhbmNlID0gbmV3IE9ialR5cGUodGhpcy5nZXRQcm9wKCdwcm90b3R5cGUnKSk7XG4gICAgcmV0dXJuIHRoaXMub2JqSW5zdGFuY2U7XG59O1xuXG4vKiogXG4gKiA0LiBhcnJheSB0eXBlc1xuICogQGNvbnN0cnVjdG9yXG4gKi9cbmZ1bmN0aW9uIEFyclR5cGUoYXJyX3Byb3RvKSB7XG4gICAgT2JqVHlwZS5jYWxsKHRoaXMsIGFycl9wcm90bywgJ0FycmF5Jyk7XG59XG5BcnJUeXBlLnByb3RvdHlwZSA9IE9iamVjdC5jcmVhdGUoT2JqVHlwZS5wcm90b3R5cGUpO1xuXG4vLyBNYWtlIHByaW1pdGl2ZSB0eXBlc1xudmFyIFByaW1OdW1iZXIgPSBuZXcgUHJpbVR5cGUoJ251bWJlcicpO1xudmFyIFByaW1TdHJpbmcgPSBuZXcgUHJpbVR5cGUoJ3N0cmluZycpO1xudmFyIFByaW1Cb29sZWFuID0gbmV3IFByaW1UeXBlKCdib29sZWFuJyk7XG5cbi8vIEFic051bGwgcmVwcmVzZW50cyBhbGwgZW1wdHkgYWJzdHJhY3QgdmFsdWVzLlxudmFyIEFWYWxOdWxsID0gbmV3IEFWYWwoKTtcbi8vIFlvdSBzaG91bGQgbm90IGFkZCBhbnkgcHJvcGVydGllcyB0byBpdC5cbkFWYWxOdWxsLnByb3BzID0gbnVsbDtcbi8vIEFkZGluZyB0eXBlcyBhcmUgaWdub3JlZC5cbkFWYWxOdWxsLmFkZFR5cGUgPSBmdW5jdGlvbiAoKSB7fTtcblxuXG4vLyBleHBvcnRcbmV4cG9ydHMuVHlwZSA9IFR5cGU7XG5leHBvcnRzLk9ialR5cGUgPSBPYmpUeXBlO1xuZXhwb3J0cy5GblR5cGUgPSBGblR5cGU7XG5leHBvcnRzLkFyclR5cGUgPSBBcnJUeXBlO1xuZXhwb3J0cy5QcmltTnVtYmVyID0gUHJpbU51bWJlcjtcbmV4cG9ydHMuUHJpbVN0cmluZyA9IFByaW1TdHJpbmc7XG5leHBvcnRzLlByaW1Cb29sZWFuID0gUHJpbUJvb2xlYW47XG5leHBvcnRzLm1rT2JqRnJvbUdsb2JhbFNjb3BlID0gbWtPYmpGcm9tR2xvYmFsU2NvcGU7XG5cbmV4cG9ydHMuQVZhbCA9IEFWYWw7XG5leHBvcnRzLkFWYWxOdWxsID0gQVZhbE51bGw7IiwiLy8gaW1wb3J0IG5lY2Vzc2FyeSBsaWJyYXJpZXNcbnZhciBhY29ybiA9IHJlcXVpcmUoJ2Fjb3JuL2Rpc3QvYWNvcm4nKTtcbnZhciBhdXggPSByZXF1aXJlKCcuL2F1eCcpO1xudmFyIHR5cGVzID0gcmVxdWlyZSgnLi9kb21haW5zL3R5cGVzJyk7XG52YXIgY29udGV4dCA9IHJlcXVpcmUoJy4vZG9tYWlucy9jb250ZXh0Jyk7XG52YXIgc3RhdHVzID0gcmVxdWlyZSgnLi9kb21haW5zL3N0YXR1cycpO1xudmFyIHV0aWwgPSByZXF1aXJlKCd1dGlsJyk7XG52YXIgdmFyQmxvY2sgPSByZXF1aXJlKCcuL3ZhckJsb2NrJyk7XG52YXIgY0dlbiA9IHJlcXVpcmUoJy4vY29uc3RyYWludC9jR2VuJyk7XG52YXIgdmFyUmVmcyA9IHJlcXVpcmUoJy4vdmFycmVmcycpO1xuXG5mdW5jdGlvbiBhbmFseXplKGlucHV0LCByZXRBbGwpIHtcbiAgICAvLyB0aGUgU2NvcGUgb2JqZWN0IGZvciBnbG9iYWwgc2NvcGVcbiAgICAvLyBzY29wZS5TY29wZS5nbG9iYWxTY29wZSA9IG5ldyBzY29wZS5TY29wZShudWxsKTtcblxuICAgIC8vIHBhcnNpbmcgaW5wdXQgcHJvZ3JhbVxuICAgIHZhciBhc3QgPSBhY29ybi5wYXJzZShpbnB1dCk7XG5cbiAgICB2YXIgbm9kZUFycmF5SW5kZXhlZEJ5TGlzdCA9IGF1eC5nZXROb2RlTGlzdChhc3QpO1xuLy8gICAgY29uc29sZS5sb2cobm9kZUFycmF5SW5kZXhlZEJ5TGlzdCk7XG5cbiAgICAvLyBTaG93IEFTVCBiZWZvcmUgc2NvcGUgcmVzb2x1dGlvblxuICAgIC8vIGF1eC5zaG93VW5mb2xkZWQoYXN0KTtcblxuLypcbiAgICAvLyBhdHRhdGNoIHRoZSBnbG9iYWwgc2NvcGUgdG8gcHJvZ3JhbSBub2RlXG4gICAgYXN0LnNjb3BlID0gc2NvcGUuU2NvcGUuZ2xvYmFsU2NvcGU7XG5cbiAgICAvLyB3YWxrIHJlY3Vyc2l2ZWx5IHRvIGFubm90YXRlIHNjb3BlIG9iamVjdHMgYW5kXG4gICAgLy8gYWRkIHZhcmlhYmxlcyB0byBlYWNoIHNjb3Blc1xuICAgIHdhbGsucmVjdXJzaXZlKGFzdCwgc2NvcGUuU2NvcGUuZ2xvYmFsU2NvcGUsIG51bGwsXG4gICAgICAgICAgICAgICAgICAgc2NvcGVSZXNvbHZlci5zY29wZVJlc29sdmVyKTtcblxuICAgIC8vIEFmdGVyIFNjb3BlIFJlc29sdXRpb25cbiAgICBjb25zb2xlLmxvZygnXFxuXFxuW1tBZnRlcl1dXFxuJyk7XG4gICAgYXV4LnNob3dVbmZvbGRlZChhc3QpO1xuXG4gICAgdmFyIGNvbnN0cmFpbnRzID0gY0dlbi5nZXRDb25zdHJhaW50cyhhc3QpO1xuXG4gICAgY29uc29sZS5sb2coJ1xcblxcbltbQ29uc3RyYWludHNdXVxcbicpO1xuICAgIGF1eC5zaG93VW5mb2xkZWQoY29uc3RyYWludHMpO1xuKi9cbiAgICB2YXIgZ0Jsb2NrQW5kQW5ub3RhdGVkQVNUID0gdmFyQmxvY2suYW5ub3RhdGVCbG9ja0luZm8oYXN0KTtcbiAgICB2YXIgZ0Jsb2NrID0gZ0Jsb2NrQW5kQW5ub3RhdGVkQVNULmdsb2JhbEJsb2NrO1xuICAgIHZhciBpbml0aWFsQ29udGV4dCA9IG5ldyBjb250ZXh0LkNhbGxTaXRlQ29udGV4dDtcbiAgICB2YXIgZ1Njb3BlID0gZ0Jsb2NrLmdldFNjb3BlSW5zdGFuY2UobnVsbCwgaW5pdGlhbENvbnRleHQpO1xuICAgIHZhciBnT2JqZWN0ID0gdHlwZXMubWtPYmpGcm9tR2xvYmFsU2NvcGUoZ1Njb3BlKTtcbiAgICB2YXIgaW5pdFN0YXR1cyA9IG5ldyBzdGF0dXMuU3RhdHVzKFxuICAgICAgICBnT2JqZWN0LFxuICAgICAgICB0eXBlcy5BVmFsTnVsbCxcbiAgICAgICAgdHlwZXMuQVZhbE51bGwsXG4gICAgICAgIGluaXRpYWxDb250ZXh0LFxuICAgICAgICBnU2NvcGUpO1xuICAgIC8vIHRoZSBwcm90b3R5cGUgb2JqZWN0IG9mIE9iamVjdFxuICAgIHZhciBPYmpQcm90byA9IG5ldyB0eXBlcy5PYmpUeXBlKG51bGwsICdPYmplY3QucHJvdG90eXBlJyk7XG4gICAgdmFyIHJ0Q1ggPSB7XG4gICAgICAgIGdsb2JhbE9iamVjdDogZ09iamVjdCxcbiAgICAgICAgLy8gdGVtcG9yYWxcbiAgICAgICAgcHJvdG9zOiB7XG4gICAgICAgICAgICBPYmplY3Q6IE9ialByb3RvLFxuICAgICAgICAgICAgRnVuY3Rpb246IG5ldyB0eXBlcy5PYmpUeXBlKG5ldyB0eXBlcy5BVmFsKE9ialByb3RvKSwgJ0Z1bmN0aW9uLnByb3RvdHlwZScpLFxuICAgICAgICAgICAgQXJyYXk6IG5ldyB0eXBlcy5PYmpUeXBlKG5ldyB0eXBlcy5BVmFsKE9ialByb3RvKSwgJ0FycmF5LnByb3RvdHlwZScpLFxuICAgICAgICAgICAgUmVnRXhwOiBuZXcgdHlwZXMuT2JqVHlwZShuZXcgdHlwZXMuQVZhbChPYmpQcm90byksICdSZWdFeHAucHJvdG90eXBlJyksXG4gICAgICAgICAgICBTdHJpbmc6IG5ldyB0eXBlcy5PYmpUeXBlKG5ldyB0eXBlcy5BVmFsKE9ialByb3RvKSwgJ1N0cmluZy5wcm90b3R5cGUnKSxcbiAgICAgICAgICAgIE51bWJlcjogbmV3IHR5cGVzLk9ialR5cGUobmV3IHR5cGVzLkFWYWwoT2JqUHJvdG8pLCAnTnVtYmVyLnByb3RvdHlwZScpLFxuICAgICAgICAgICAgQm9vbGVhbjogbmV3IHR5cGVzLk9ialR5cGUobmV3IHR5cGVzLkFWYWwoT2JqUHJvdG8pLCAnQm9vbGVhbi5wcm90b3R5cGUnKVxuICAgICAgICB9XG5cbiAgICB9O1xuICAgIGNHZW4uYWRkQ29uc3RyYWludHMoYXN0LCBpbml0U3RhdHVzLCBydENYKTtcbiAgICB2YXIgY29uc3RyYWludHMgPSBjR2VuLmNvbnN0cmFpbnRzO1xuICAgIC8vYXV4LnNob3dVbmZvbGRlZChnQmxvY2tBbmRBbm5vdGF0ZWRBU1QuYXN0KTtcbiAgICAvLyBhdXguc2hvd1VuZm9sZGVkKGNvbnN0cmFpbnRzKTtcbiAgICAvLyBhdXguc2hvd1VuZm9sZGVkKGdCbG9jayk7XG4gICAgLy8gY29uc29sZS5sb2codXRpbC5pbnNwZWN0KGdCbG9jaywge2RlcHRoOiAxMH0pKTtcbiAgICBpZiAocmV0QWxsKSB7XG4gICAgICAgIHJldHVybiB7Z09iamVjdDogZ09iamVjdCwgQVNUOiBhc3R9O1xuICAgIH0gZWxzZSB7XG4gICAgICAgIHJldHVybiBnT2JqZWN0O1xuICAgIH1cbn1cblxuZXhwb3J0cy5hbmFseXplID0gYW5hbHl6ZTtcbmV4cG9ydHMuZmluZElkZW50aWZpZXJOb2RlQXQgPSB2YXJSZWZzLmZpbmRJZGVudGlmaWVyTm9kZUF0OyIsIi8qXG4gSmF2YVNjcmlwdOuKlCBnbG9iYWwsIGZ1bmN0aW9uIGJsb2NrLCBjYXRjaCBibG9ja+yXkCDrs4DsiJjqsIAg64us66aw64ukLlxuIEVTNuuKlCDsnbzrsJggYmxvY2vsl5Drj4Qg64us66aw64ukLlxuXG4gVmFyQmxvY2vripQg6rCBIGJsb2Nr7JeQIOuLrOumsCDrs4DsiJjrk6TsnYQg64KY7YOA64K464ukLlxuIC0gcGFyZW4gICAgICA6IEJsb2NrVmFycywg67CU6rmlIGJsb2Nr7J2EIOuCmO2DgOuCtOuKlCDqsJ3ssrRcbiAtIG9yaWdpbkxhYmVsOiBudW1iZXIsIO2VtOuLuSBCbG9ja1ZhcnPqsIAg7ISg7Ja465CcIEFTVCBub2Rl7J2YIEBsYWJlbFxuICAgIG9yaWdpbuydtCDrkKAg7IiYIOyeiOuKlCBub2Rl64qUXG4gICAgRnVuY3Rpb24uYm9keSwgQ2F0Y2hDbGF1c2UuYmxvY2sg65GQ6rCA7KeA64ukLlxuICAgIOuRkOqwgOyngCDrqqjrkZAgQmxvY2tTdGF0ZW1lbnTsnbTri6QuXG4gLSBpc0NhdGNoICAgIDogYm9vbGVhbixcbiAgICogdHJ1ZSAgLT4gY2F0Y2ggYmxvY2tcbiAgICogZmFsc2UgLT4gZnVuY3Rpb24gYmxvY2ssIG9yIGdsb2JhbFxuXG4gLSBwYXJhbVZhck5hbWVzIDog66ek6rCc67OA7IiYIOydtOumhCDrqqnroZ0sIOunpOqwnCDrs4DsiJgg7Iic7ISc64yA66GcXG4gLSBsb2NhbFZhck5hbWVzIDog7KeA7JetIOuzgOyImCDsnbTrpoQg66qp66GdLCDsiJzshJwg66y07J2Y66+4XG4gICAgYXJndW1lbnRz66W8IOyCrOyaqe2VmOuKlCDqsr3smrAgbG9jYWxWYXJOYW1lc+yXkCDrk7HsnqXtlZjqs6AsXG4gICAgYXJndW1lbnRzIG9iamVjdOulvCDsgqzsmqntlZjrqbQgdXNlQXJndW1lbnRzT2JqZWN0ID09IHRydWVcblxuIC0gKG9wdGlvbmFsKSB1c2VBcmd1bWVudHNPYmplY3Q6IGJvb2xlYW5cbiAgICDtlajsiJggYm9keSBibG9ja+yduCDqsr3smrDsl5Drp4wg7IKs7JqpIOqwgOuKpVxuICAgICogdHJ1ZSAgOiBhcmd1bWVudHMgb2JqZWN06rCAIOyCrOyaqeuQmOyXiOuLpC5cbiAgICAgIOymiSDtlajsiJggYm9keeyXkOyEnCDrs4DsiJggYXJndW1lbnRz66W8IOyEoOyWuCDsl4bsnbQg7IKs7Jqp7ZaI64ukLlxuICAgICAg7J20IOqyveyasCwgYXJndW1lbnRz64qUIO2VqOyImOydmCDsp4Dsl60g67OA7IiY66GcIOuTseuhneuQnOuLpC5cbiAgICAqIGZhbHNlIOyduCDqsr3smrDripQg7JeG64ukLiDqt7jrn7TqsbDrqbQg7JWE7JiIIOuzgOyImCDsnpDssrTqsIAg7JeG64ukLlxuXG4gLSB1c2VkVmFyaWFibGVzIDog6rCBIGJsb2Nr7J2YIOunpOqwnOuzgOyImCwg7KeA7Jet67OA7IiYIOykkVxuICAg7IKs7Jqp65CY64qUIOychOy5mOqwgCDsnojripQg6rKD65Ok7J2YIOuqqeuhnVxuXG4gLSBpbnN0YW5jZXMgOiBEZWx0YSAtPiBWYXJCbG9ja+ydmCDrs4DsiJjrk6QgLT4gQVZhbFxuICAgZ2V0SW5zdGFuY2UoZGVsdGEpIOulvCDthrXtlbQg6rCZ7J2AIGRlbHRh64qUIOqwmeydgCBtYXBwaW5nIOyjvOqyjCDrp4zrk6xcblxuIC0gc2NvcGVJbnN0YW5jZXMgOiBbU2NvcGVdXG4gICDtmITsnqwgVmFyQmxvY2vsnYQg66eI7KeA66eJ7Jy866GcIO2VmOuKlCBTY29wZeulvCDrqqjrkZAg66qo7J2A64ukLlxuICAgZ2V0U2NvcGVJbnN0YW5jZShkZWx0YSwgcGFyZW4pIOydhCDthrXtlbQg6rCZ7J2AIHNjb3BlIGNoYWlu7J2AXG4gICDqsJnsnYAg6rCd7LK06rCAIOuQmOuPhOuhnSDrp4zrk6Dri6QuXG4qL1xuJ3VzZSBzdHJpY3QnO1xuXG52YXIgdHlwZXMgPSByZXF1aXJlKCcuL2RvbWFpbnMvdHlwZXMnKTtcbnZhciB3YWxrID0gcmVxdWlyZSgnYWNvcm4vZGlzdC93YWxrJyk7XG52YXIgYXV4ID0gcmVxdWlyZSgnLi9hdXgnKTtcblxuZnVuY3Rpb24gVmFyQmxvY2socGFyZW4sIG9yaWdpbkxhYmVsLCBpc0NhdGNoKSB7XG4gICAgdGhpcy5wYXJlbiA9IHBhcmVuO1xuICAgIHRoaXMub3JpZ2luTGFiZWwgPSBvcmlnaW5MYWJlbDtcbiAgICB0aGlzLmlzQ2F0Y2ggPSBpc0NhdGNoO1xuICAgIHRoaXMucGFyYW1WYXJOYW1lcyA9IFtdO1xuICAgIHRoaXMubG9jYWxWYXJOYW1lcyA9IFtdO1xuXG4gICAgdGhpcy51c2VkVmFyaWFibGVzID0gW107XG4gICAgLy8gdGhpcy51c2VBcmd1bWVudHNPYmplY3RcbiAgICB0aGlzLmluc3RhbmNlcyA9IE9iamVjdC5jcmVhdGUobnVsbCk7XG4gICAgdGhpcy5zY29wZUluc3RhbmNlcyA9IFtdO1xufVxuXG5WYXJCbG9jay5wcm90b3R5cGUgPSBPYmplY3QuY3JlYXRlKG51bGwpO1xuXG5WYXJCbG9jay5wcm90b3R5cGUuaXNHbG9iYWwgPSBmdW5jdGlvbiAoKSB7XG4gICAgcmV0dXJuIHRoaXMucGFyZW4gPT0gbnVsbDtcbn07XG5WYXJCbG9jay5wcm90b3R5cGUuaXNGdW5jdGlvbiA9IGZ1bmN0aW9uICgpIHtcbiAgICByZXR1cm4gdGhpcy5wYXJlbiAhPSBudWxsICYmIHRoaXMubG9jYWxWYXJOYW1lcyAhPSBudWxsO1xufTtcblZhckJsb2NrLnByb3RvdHlwZS5pc0NhdGNoQmxvY2sgPSBmdW5jdGlvbiAoKSB7XG4gICAgcmV0dXJuIHRoaXMuaXNDYXRjaDtcbn07XG5cblZhckJsb2NrLnByb3RvdHlwZS5nZXRMb2NhbFZhck5hbWVzID0gZnVuY3Rpb24gKCkge1xuICAgIHJldHVybiB0aGlzLmxvY2FsVmFyTmFtZXM7XG59O1xuVmFyQmxvY2sucHJvdG90eXBlLmdldFBhcmFtVmFyTmFtZXMgPSBmdW5jdGlvbiAoKSB7XG4gICAgcmV0dXJuIHRoaXMucGFyYW1WYXJOYW1lcztcbn07XG5WYXJCbG9jay5wcm90b3R5cGUuaGFzTG9jYWxWYXIgPSBmdW5jdGlvbiAodmFyTmFtZSkge1xuICAgIHJldHVybiB0aGlzLmxvY2FsVmFyTmFtZXMgJiYgdGhpcy5sb2NhbFZhck5hbWVzLmluZGV4T2YodmFyTmFtZSkgPiAtMTtcbn07XG5WYXJCbG9jay5wcm90b3R5cGUuaGFzUGFyYW1WYXIgPSBmdW5jdGlvbiAodmFyTmFtZSkge1xuICAgIHJldHVybiB0aGlzLnBhcmFtVmFyTmFtZXMuaW5kZXhPZih2YXJOYW1lKSA+IC0xO1xufTtcblZhckJsb2NrLnByb3RvdHlwZS5oYXNWYXIgPSBmdW5jdGlvbiAodmFyTmFtZSkge1xuICAgIHJldHVybiB0aGlzLmhhc1BhcmFtVmFyKHZhck5hbWUpIHx8IHRoaXMuaGFzTG9jYWxWYXIodmFyTmFtZSk7XG59O1xuXG5WYXJCbG9jay5wcm90b3R5cGUuYWRkRGVjbGFyZWRMb2NhbFZhciA9IGZ1bmN0aW9uICh2YXJOYW1lLCBpc0Z1bkRlY2wpIHtcbiAgICB2YXIgY3VyckJsb2NrID0gdGhpcztcbiAgICAvLyBwZWVsIG9mZiBpbml0aWFsIGNhdGNoIGJsb2Nrc1xuICAgIC8vIGZvciBmdW5jdGlvbiBkZWNsLCBza2lwIGFueSBjYXRjaCBibG9ja3MsXG4gICAgLy8gZm9yIHZhcmlhYmxlIGRlY2wsIHNraXAgY2F0Y2ggYmxvY2sgd2l0aCBkaWZmZXJlbnQgdmFyTmFtZS5cbiAgICB3aGlsZSAoY3VyckJsb2NrLmlzQ2F0Y2hCbG9jaygpICYmXG4gICAgICAgICAgIChpc0Z1bkRlY2wgfHwgIWN1cnJCbG9jay5oYXNQYXJhbVZhcih2YXJOYW1lKSkpIHtcbiAgICAgICAgY3VyckJsb2NrID0gY3VyckJsb2NrLnBhcmVuO1xuICAgIH1cbiAgICAvLyBpZiBhbHJlYWR5IGFkZGVkLCBkbyBub3QgYWRkXG4gICAgaWYgKCFjdXJyQmxvY2suaGFzVmFyKHZhck5hbWUpKSB7XG4gICAgICAgIGN1cnJCbG9jay5sb2NhbFZhck5hbWVzLnB1c2godmFyTmFtZSk7XG4gICAgfVxuICAgIC8vIHJldHVybnMgdGhlIGJsb2NrIG9iamVjdCB0aGF0IGNvbnRhaW5zIHRoZSB2YXJpYWJsZVxuICAgIHJldHVybiBjdXJyQmxvY2s7XG59O1xuVmFyQmxvY2sucHJvdG90eXBlLmFkZFBhcmFtVmFyID0gZnVuY3Rpb24gKHZhck5hbWUpIHtcbiAgICB0aGlzLnBhcmFtVmFyTmFtZXMucHVzaCh2YXJOYW1lKTtcbn07XG5WYXJCbG9jay5wcm90b3R5cGUuZmluZFZhckluQ2hhaW4gPSBmdW5jdGlvbiAodmFyTmFtZSkge1xuICAgIHZhciBjdXJyQmxvY2sgPSB0aGlzO1xuICAgIHdoaWxlIChjdXJyQmxvY2sgJiYgY3VyckJsb2NrLnBhcmVuICYmICFjdXJyQmxvY2suaGFzVmFyKHZhck5hbWUpKSB7XG4gICAgICAgIGN1cnJCbG9jayA9IGN1cnJCbG9jay5wYXJlbjtcbiAgICB9XG4gICAgLy8gaWYgbm90IGZvdW5kLCBpdCB3aWxsIHJldHVybiB0aGUgZ2xvYmFsXG4gICAgcmV0dXJuIGN1cnJCbG9jaztcbn07XG5cblZhckJsb2NrLnByb3RvdHlwZS5hZGRVc2VkVmFyID0gZnVuY3Rpb24gKHZhck5hbWUpIHtcbiAgICBpZiAodGhpcy51c2VkVmFyaWFibGVzLmluZGV4T2YodmFyTmFtZSkgPT09IC0xKSB7XG4gICAgICAgIHRoaXMudXNlZFZhcmlhYmxlcy5wdXNoKHZhck5hbWUpO1xuICAgIH1cbn07XG5WYXJCbG9jay5wcm90b3R5cGUuZ2V0VXNlZFZhck5hbWVzID0gZnVuY3Rpb24gKCkge1xuICAgIHJldHVybiB0aGlzLnVzZWRWYXJpYWJsZXM7XG59O1xuVmFyQmxvY2sucHJvdG90eXBlLmlzVXNlZFZhciA9IGZ1bmN0aW9uICh2YXJOYW1lKSB7XG4gICAgcmV0dXJuIHRoaXMudXNlZFZhcmlhYmxlcy5pbmRleE9mKHZhck5hbWUpID4gLTE7XG59O1xuXG4vLyByZXR1cm5zIGEgbWFwcGluZ1xuVmFyQmxvY2sucHJvdG90eXBlLmdldEluc3RhbmNlID0gZnVuY3Rpb24gKGRlbHRhKSB7XG4gICAgaWYgKHRoaXMuaW5zdGFuY2VzW2RlbHRhXSkge1xuICAgICAgICByZXR1cm4gdGhpcy5pbnN0YW5jZXNbZGVsdGFdO1xuICAgIH1cbiAgICAvLyBjb25zdHJ1Y3QgVmFyTWFwXG4gICAgdmFyIHZhck1hcCA9IG5ldyBNYXAoKTtcbiAgICB2YXIgdmFyTmFtZXMgPSB0aGlzLmdldFBhcmFtVmFyTmFtZXMoKS5jb25jYXQodGhpcy5nZXRMb2NhbFZhck5hbWVzKCkpO1xuXG4gICAgZm9yICh2YXIgaSA9IDA7IGkgPCB2YXJOYW1lcy5sZW5ndGg7IGkrKykge1xuICAgICAgICB2YXJNYXAuc2V0KHZhck5hbWVzW2ldLCBuZXcgdHlwZXMuQVZhbCgpKTtcbiAgICB9XG4gICAgLy8gcmVtZW1iZXIgdGhlIGluc3RhbmNlXG4gICAgdGhpcy5pbnN0YW5jZXNbZGVsdGFdID0gdmFyTWFwO1xuICAgIHJldHVybiB2YXJNYXA7XG59O1xuLy8gcmV0dXJucyBhbiBhcnJheVxuVmFyQmxvY2sucHJvdG90eXBlLmdldFBhcmFtQVZhbHMgPSBmdW5jdGlvbiAoZGVsdGEpIHtcbiAgICB2YXIgaW5zdGFuY2UgPSB0aGlzLmdldEluc3RhbmNlKGRlbHRhKTtcbiAgICB2YXIgcGFyYW1zID0gW107XG4gICAgdGhpcy5nZXRQYXJhbVZhck5hbWVzKCkuZm9yRWFjaChmdW5jdGlvbiAobmFtZSkge1xuICAgICAgICBwYXJhbXMucHVzaChpbnN0YW5jZVthdXguaW50ZXJuYWxOYW1lKG5hbWUpXSk7XG4gICAgfSk7XG4gICAgcmV0dXJuIHBhcmFtcztcbn07XG4vLyByZXR1cm5zIGFuIEFWYWxcblZhckJsb2NrLnByb3RvdHlwZS5nZXRBcmd1bWVudHNBVmFsID0gZnVuY3Rpb24gKGRlbHRhKSB7XG4gICAgaWYgKCF0aGlzLnVzZUFyZ3VtZW50c09iamVjdCkge1xuICAgICAgICB0aHJvdyBuZXcgRXJyb3IoJ05vdCBmb3IgdGhpcyBWYXJCbG9jaycpO1xuICAgIH1cbiAgICByZXR1cm4gdGhpcy5nZXRJbnN0YW5jZShkZWx0YSlbYXV4LmludGVybmFsTmFtZSgnYXJndW1lbnRzJyldO1xufTtcblxuLy8gZ2V0IGEgU2NvcGUgaW5zdGFuY2VcblZhckJsb2NrLnByb3RvdHlwZS5nZXRTY29wZUluc3RhbmNlID0gZnVuY3Rpb24gKHBhcmVuLCBkZWx0YSkge1xuICAgIHZhciB2YXJNYXAgPSB0aGlzLmdldEluc3RhbmNlKGRlbHRhKTtcbiAgICB2YXIgZm91bmQgPSBudWxsO1xuXG4gICAgdGhpcy5zY29wZUluc3RhbmNlcy5mb3JFYWNoKGZ1bmN0aW9uIChzYykge1xuICAgICAgICBpZiAoc2MucGFyZW4gPT09IHBhcmVuICYmIHNjLnZhck1hcCA9PT0gdmFyTWFwKSBmb3VuZCA9IHNjO1xuICAgIH0pO1xuXG4gICAgaWYgKGZvdW5kKSB7XG4gICAgICAgIHJldHVybiBmb3VuZDtcbiAgICB9IGVsc2Uge1xuICAgICAgICB2YXIgbmV3U2NvcGVJbnN0YW5jZSA9IG5ldyBTY29wZShwYXJlbiwgdmFyTWFwLCB0aGlzKTtcbiAgICAgICAgdGhpcy5zY29wZUluc3RhbmNlcy5wdXNoKG5ld1Njb3BlSW5zdGFuY2UpO1xuICAgICAgICByZXR1cm4gbmV3U2NvcGVJbnN0YW5jZTtcbiAgICB9XG59O1xuXG52YXIgZGVjbGFyZWRWYXJpYWJsZUZpbmRlciA9IHdhbGsubWFrZSh7XG4gICBGdW5jdGlvbjogZnVuY3Rpb24gKG5vZGUsIGN1cnJCbG9jaywgYykge1xuICAgICAgICB2YXIgcGFyZW5CbG9jayA9IGN1cnJCbG9jaztcbiAgICAgICAgaWYgKG5vZGUuaWQpIHtcbiAgICAgICAgICAgIHZhciBmdW5jTmFtZSA9IG5vZGUuaWQubmFtZTtcbiAgICAgICAgICAgIHBhcmVuQmxvY2sgPSBjdXJyQmxvY2suYWRkRGVjbGFyZWRMb2NhbFZhcihmdW5jTmFtZSwgdHJ1ZSk7XG4gICAgICAgIH1cbiAgICAgICAgLy8gY3JlYXRlIGEgVmFyQmxvY2sgZm9yIGZ1bmN0aW9uXG4gICAgICAgIHZhciBmdW5jQmxvY2sgPSBuZXcgVmFyQmxvY2socGFyZW5CbG9jaywgbm9kZVsnQGxhYmVsJ10pO1xuICAgICAgICBub2RlLmJvZHlbJ0BibG9jayddID0gZnVuY0Jsb2NrO1xuICAgICAgICAvLyBhZGQgZnVuY3Rpb24gcGFyYW1ldGVycyB0byB0aGUgc2NvcGVcbiAgICAgICAgZm9yICh2YXIgaSA9IDA7IGkgPCBub2RlLnBhcmFtcy5sZW5ndGg7IGkrKykge1xuICAgICAgICAgICAgdmFyIHBhcmFtTmFtZSA9IG5vZGUucGFyYW1zW2ldLm5hbWU7XG4gICAgICAgICAgICBmdW5jQmxvY2suYWRkUGFyYW1WYXIocGFyYW1OYW1lKTtcbiAgICAgICAgfVxuICAgICAgICBjKG5vZGUuYm9keSwgZnVuY0Jsb2NrLCB1bmRlZmluZWQpO1xuICAgIH0sXG4gICAgVmFyaWFibGVEZWNsYXJhdGlvbjogZnVuY3Rpb24gKG5vZGUsIGN1cnJCbG9jaywgYykge1xuICAgICAgICBmb3IgKHZhciBpID0gMDsgaSA8IG5vZGUuZGVjbGFyYXRpb25zLmxlbmd0aDsgaSsrKSB7XG4gICAgICAgICAgICB2YXIgZGVjbCA9IG5vZGUuZGVjbGFyYXRpb25zW2ldO1xuICAgICAgICAgICAgdmFyIG5hbWUgPSBkZWNsLmlkLm5hbWU7XG4gICAgICAgICAgICBjdXJyQmxvY2suYWRkRGVjbGFyZWRMb2NhbFZhcihuYW1lKTtcbiAgICAgICAgfVxuICAgICAgICBpZiAoZGVjbC5pbml0KSBjKGRlY2wuaW5pdCwgY3VyckJsb2NrLCB1bmRlZmluZWQpO1xuICAgIH0sXG4gICAgVHJ5U3RhdGVtZW50OiBmdW5jdGlvbiAobm9kZSwgY3VyclNjb3BlLCBjKSB7XG4gICAgICAgIGMobm9kZS5ibG9jaywgY3VyclNjb3BlLCB1bmRlZmluZWQpO1xuICAgICAgICBpZiAobm9kZS5oYW5kbGVyKSB7XG4gICAgICAgICAgICBjKG5vZGUuaGFuZGxlciwgY3VyclNjb3BlLCB1bmRlZmluZWQpO1xuICAgICAgICB9XG4gICAgICAgIGlmIChub2RlLmZpbmFsaXplcikge1xuICAgICAgICAgICAgYyhub2RlLmZpbmFsaXplciwgY3VyclNjb3BlLCB1bmRlZmluZWQpO1xuICAgICAgICB9XG4gICAgfSxcbiAgICBDYXRjaENsYXVzZTogZnVuY3Rpb24gKG5vZGUsIGN1cnJCbG9jaywgYykge1xuICAgICAgICB2YXIgY2F0Y2hCbG9jayA9IG5ldyBWYXJCbG9jayhjdXJyQmxvY2ssIG5vZGVbJ0BsYWJlbCddLCB0cnVlKTtcbiAgICAgICAgY2F0Y2hCbG9jay5hZGRQYXJhbVZhcihub2RlLnBhcmFtLm5hbWUpO1xuICAgICAgICBub2RlLmJvZHlbJ0BibG9jayddID0gY2F0Y2hCbG9jaztcbiAgICAgICAgYyhub2RlLmJvZHksIGNhdGNoQmxvY2ssIHVuZGVmaW5lZCk7XG4gICAgfVxufSk7XG5cbi8vIEZvciB2YXJpYWJsZXMgaW4gZ2xvYmFsIGFuZCBhcmd1bWVudHMgaW4gZnVuY3Rpb25zXG52YXIgdmFyaWFibGVVc2FnZUNvbGxlY3RvciA9IHdhbGsubWFrZSh7XG4gICAgSWRlbnRpZmllcjogZnVuY3Rpb24gKG5vZGUsIGN1cnJCbG9jaywgYykge1xuICAgICAgICB2YXIgY29udGFpbmluZ0Jsb2NrLCB2YXJOYW1lID0gbm9kZS5uYW1lO1xuICAgICAgICBpZiAodmFyTmFtZSAhPT0gJ2FyZ3VtZW50cycpIHtcbiAgICAgICAgICAgIGNvbnRhaW5pbmdCbG9jayA9IGN1cnJCbG9jay5maW5kVmFySW5DaGFpbih2YXJOYW1lKTtcbiAgICAgICAgICAgIGlmIChjb250YWluaW5nQmxvY2suaXNHbG9iYWwoKSkge1xuICAgICAgICAgICAgICAgIGNvbnRhaW5pbmdCbG9jay5hZGREZWNsYXJlZExvY2FsVmFyKHZhck5hbWUpO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgY29udGFpbmluZ0Jsb2NrLmFkZFVzZWRWYXIodmFyTmFtZSk7XG4gICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgICAvLyB2YXJOYW1lID09ICdhcmd1bWVudHMnXG4gICAgICAgICAgICBjb250YWluaW5nQmxvY2sgPSBjdXJyQmxvY2s7XG4gICAgICAgICAgICB3aGlsZSAoY29udGFpbmluZ0Jsb2NrLmlzQ2F0Y2hCbG9jaygpICYmXG4gICAgICAgICAgICAgICAgICAgICFjb250YWluaW5nQmxvY2suaGFzUGFyYW1WYXIodmFyTmFtZSkpIHtcbiAgICAgICAgICAgICAgICBjb250YWluaW5nQmxvY2sgPSBjb250YWluaW5nQmxvY2sucGFyZW47XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBpZiAoY29udGFpbmluZ0Jsb2NrLmhhc1Zhcih2YXJOYW1lKSkge1xuICAgICAgICAgICAgICAgIC8vIGFyZ3VtZW50cyBpcyBleHBsaWNpdGx5IGRlY2xhcmVkXG4gICAgICAgICAgICAgICAgY29udGFpbmluZ0Jsb2NrLmFkZFVzZWRWYXIodmFyTmFtZSk7XG4gICAgICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgICAgICAgIC8vIGFyZ3VtZW50cyBpcyBub3QgZXhwbGljaXRseSBkZWNsYXJlZFxuICAgICAgICAgICAgICAgIC8vIGFkZCBpdCBhcyBsb2NhbCB2YXJpYWJsZVxuICAgICAgICAgICAgICAgIGNvbnRhaW5pbmdCbG9jay5hZGREZWNsYXJlZExvY2FsVmFyKHZhck5hbWUpO1xuICAgICAgICAgICAgICAgIC8vIGFsc28gaXQgaXMgdXNlZFxuICAgICAgICAgICAgICAgIGNvbnRhaW5pbmdCbG9jay5hZGRVc2VkVmFyKHZhck5hbWUpO1xuICAgICAgICAgICAgICAgIGlmIChjb250YWluaW5nQmxvY2suaXNGdW5jdGlvbigpKSB7XG4gICAgICAgICAgICAgICAgICAgIGNvbnRhaW5pbmdCbG9jay51c2VBcmd1bWVudHNPYmplY3QgPSB0cnVlO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgIH1cbiAgICAgICAgfVxuICAgIH0sXG5cbiAgICBSZXR1cm5TdGF0ZW1lbnQ6IGZ1bmN0aW9uIChub2RlLCBjdXJyQmxvY2ssIGMpIHtcbiAgICAgICAgdmFyIGZ1bmN0aW9uQmxvY2sgPSBjdXJyQmxvY2s7XG4gICAgICAgIHdoaWxlIChmdW5jdGlvbkJsb2NrLmlzQ2F0Y2hCbG9jaygpKSB7XG4gICAgICAgICAgICBmdW5jdGlvbkJsb2NrID0gZnVuY3Rpb25CbG9jay5wYXJlbjtcbiAgICAgICAgfVxuICAgICAgICBpZiAoIWZ1bmN0aW9uQmxvY2suaXNHbG9iYWwoKSAmJiBub2RlLmFyZ3VtZW50ICE9PSBudWxsKSB7XG4gICAgICAgICAgICBmdW5jdGlvbkJsb2NrLnVzZVJldHVybldpdGhBcmd1bWVudCA9IHRydWU7XG4gICAgICAgIH1cbiAgICAgICAgaWYgKG5vZGUuYXJndW1lbnQpIHtcbiAgICAgICAgICAgIGMobm9kZS5hcmd1bWVudCwgY3VyckJsb2NrLCB1bmRlZmluZWQpO1xuICAgICAgICB9XG4gICAgfSxcblxuICAgIFNjb3BlQm9keTogZnVuY3Rpb24gKG5vZGUsIGN1cnJCbG9jaywgYykge1xuICAgICAgICBjKG5vZGUsIG5vZGVbJ0BibG9jayddIHx8IGN1cnJCbG9jayk7XG4gICAgfVxufSk7XG5cblxuZnVuY3Rpb24gYW5ub3RhdGVCbG9ja0luZm8oYXN0LCBnQmxvY2spIHtcbiAgICBpZiAoIWdCbG9jaykge1xuICAgICAgICAvLyB3aGVuIGdsb2JhbCBibG9jayBpcyBub3QgZ2l2ZW4sIGNyZWF0ZVxuICAgICAgICBnQmxvY2sgPSBuZXcgVmFyQmxvY2sobnVsbCwgYXN0WydAbGFiZWwnXSk7XG4gICAgfVxuICAgIHdhbGsucmVjdXJzaXZlKGFzdCwgZ0Jsb2NrLCBudWxsLCBkZWNsYXJlZFZhcmlhYmxlRmluZGVyKTtcbiAgICB3YWxrLnJlY3Vyc2l2ZShhc3QsIGdCbG9jaywgbnVsbCwgdmFyaWFibGVVc2FnZUNvbGxlY3Rvcik7XG4gICAgcmV0dXJuIHtnbG9iYWxCbG9jazogZ0Jsb2NrLCBhc3Q6IGFzdH07XG59XG5cbi8vIGRlZmluZSBzY29wZSBvYmplY3RcbmZ1bmN0aW9uIFNjb3BlKHBhcmVuLCB2YXJNYXAsIHZiKSB7XG4gICAgdGhpcy5wYXJlbiA9IHBhcmVuO1xuICAgIHRoaXMudmFyTWFwID0gdmFyTWFwO1xuICAgIHRoaXMudmIgPSB2Yjtcbn1cblNjb3BlLnByb3RvdHlwZSA9IE9iamVjdC5jcmVhdGUobnVsbCk7XG4vLyBmaW5kIEFWYWwgb2YgYSB2YXJpYWJsZSBpbiB0aGUgY2hhaW5cblNjb3BlLnByb3RvdHlwZS5nZXRBVmFsT2YgPSBmdW5jdGlvbiAodmFyTmFtZSkge1xuICAgIHZhciBjdXJyID0gdGhpcztcbiAgICB3aGlsZSAoY3VyciAhPSBudWxsKSB7XG4gICAgICAgIGlmIChjdXJyLnZhck1hcC5oYXModmFyTmFtZSkpIHtcbiAgICAgICAgICAgIHJldHVybiBjdXJyLnZhck1hcC5nZXQodmFyTmFtZSk7XG4gICAgICAgIH1cbiAgICAgICAgY3VyciA9IGN1cnIucGFyZW47XG4gICAgfVxuICAgIHRocm93IG5ldyBFcnJvcignU2hvdWxkIGhhdmUgZm91bmQgdGhlIHZhcmlhYmxlJyk7XG59O1xuLy8gcmVtb3ZlIGluaXRpYWwgY2F0Y2ggc2NvcGVzIGZyb20gdGhlIGNoYWluXG5TY29wZS5wcm90b3R5cGUucmVtb3ZlSW5pdGlhbENhdGNoQmxvY2tzID0gZnVuY3Rpb24gKCkge1xuICAgIHZhciBjdXJyID0gdGhpcztcbiAgICB3aGlsZSAoY3Vyci52Yi5pc0NhdGNoQmxvY2soKSkge1xuICAgICAgICBjdXJyID0gY3Vyci5wYXJlbjtcbiAgICB9XG4gICAgcmV0dXJuIGN1cnI7XG59O1xuXG5cbmV4cG9ydHMuVmFyQmxvY2sgPSBWYXJCbG9jaztcbmV4cG9ydHMuYW5ub3RhdGVCbG9ja0luZm8gPSBhbm5vdGF0ZUJsb2NrSW5mbztcbmV4cG9ydHMuU2NvcGUgPSBTY29wZTtcbiIsInZhciB3YWxrID0gcmVxdWlyZSgnYWNvcm4vZGlzdC93YWxrJyk7XG52YXIgZnMgPSByZXF1aXJlKCdmcycpO1xudmFyIGluZmVyID0gcmVxdWlyZSgnLi9pbmZlcicpO1xuXG5cbmZ1bmN0aW9uIGZpbmRJZGVudGlmaWVyTm9kZUF0KGFzdCwgcG9zKSB7XG4gICAgXCJ1c2Ugc3RyaWN0XCI7XG5cbiAgICAvLyBkZWZpbmluZyB3YWxrZXJcbiAgICB2YXIgc2VhcmNoV2Fsa2VyID0gd2Fsay5tYWtlKHtcbiAgICAgICAgRnVuY3Rpb246IGZ1bmN0aW9uKG5vZGUsIHN0LCBjKSB7XG4gICAgICAgICAgICBpZiAobm9kZS5pZCkgYyhub2RlLmlkLCBzdCk7XG4gICAgICAgICAgICBmb3IgKHZhciBpID0gMDsgaSA8IG5vZGUucGFyYW1zLmxlbmd0aDsgaSsrKVxuICAgICAgICAgICAgICAgIGMobm9kZS5wYXJhbXNbaV0sIHN0KTtcbiAgICAgICAgICAgIGMobm9kZS5ib2R5LCBzdCk7XG4gICAgICAgIH0sXG4gICAgICAgIFRyeVN0YXRlbWVudDogZnVuY3Rpb24obm9kZSwgc3QsIGMpIHtcbiAgICAgICAgICAgIGMobm9kZS5ibG9jaywgc3QpO1xuICAgICAgICAgICAgaWYgKG5vZGUuaGFuZGxlcikge1xuICAgICAgICAgICAgICAgIGMobm9kZS5oYW5kbGVyLnBhcmFtLCBzdCk7XG4gICAgICAgICAgICAgICAgYyhub2RlLmhhbmRsZXIuYm9keSwgc3QpO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgaWYgKG5vZGUuZmluYWxpemVyKSB7XG4gICAgICAgICAgICAgICAgYyhub2RlLmZpbmFsaXplciwgc3QpO1xuICAgICAgICAgICAgfVxuICAgICAgICB9LFxuICAgICAgICBWYXJpYWJsZURlY2xhcmF0aW9uOiBmdW5jdGlvbihub2RlLCBzdCwgYykge1xuICAgICAgICAgICAgZm9yICh2YXIgaSA9IDA7IGkgPCBub2RlLmRlY2xhcmF0aW9ucy5sZW5ndGg7ICsraSkge1xuICAgICAgICAgICAgICAgIHZhciBkZWNsID0gbm9kZS5kZWNsYXJhdGlvbnNbaV07XG4gICAgICAgICAgICAgICAgYyhkZWNsLmlkLCBzdCk7XG4gICAgICAgICAgICAgICAgaWYgKGRlY2wuaW5pdCkgYyhkZWNsLmluaXQsIHN0LCBcIkV4cHJlc3Npb25cIik7XG4gICAgICAgICAgICB9XG4gICAgICAgIH1cbiAgICB9KTtcblxuICAgIC8vIGZpbmQgdGhlIG5vZGVcbiAgICB2YXIgZm91bmROb2RlID0gd2Fsay5maW5kTm9kZUFyb3VuZChhc3QsIHBvcywgdW5kZWZpbmVkLCBzZWFyY2hXYWxrZXIpLm5vZGU7XG4gICAgaWYgKGZvdW5kTm9kZS50eXBlID09PSAnSWRlbnRpZmllcicpIHtcbiAgICAgICAgcmV0dXJuIGZvdW5kTm9kZTtcbiAgICB9IGVsc2Uge1xuICAgICAgICByZXR1cm4gbnVsbDtcbiAgICB9XG59XG4vKipcbiAqXG4gKiBAcGFyYW0gYXN0IC0gc2NvcGUgYW5ub3RhdGVkIEFTVFxuICogQHBhcmFtIHtudW1iZXJ9IHBvcyAtIGNoYXJhY3RlciBwb3NpdGlvblxuICogQHJldHVybnMgeyp9IC0gYXJyYXkgb2YgQVNUIG5vZGVzXG4gKi9cbmZ1bmN0aW9uIGZpbmRJZFJlZnNBdChhc3QsIHBvcykge1xuICAgIFwidXNlIHN0cmljdFwiO1xuICAgIHZhciBpZE5vZGUgPSBmaW5kSWRlbnRpZmllck5vZGVBdChhc3QsIHBvcyk7XG4gICAgaWYgKCFpZE5vZGUpIHtcbiAgICAgICAgLy8gcG9zIGlzIG5vdCBhdCBhIHZhcmlhYmxlXG4gICAgICAgIHJldHVybiBudWxsO1xuICAgIH1cbiAgICAvLyBmaW5kIHJlZnMgZm9yIHRoZSBpZCBub2RlXG4gICAgdmFyIHJlZnMgPSBmaW5kUmVmc1RvVmFyaWFibGUoYXN0LCBpZE5vZGUpO1xuXG4gICAgcmV0dXJuIHJlZnM7XG59XG5cbi8qKlxuICpcbiAqIEBwYXJhbSBhc3QgLSBzY29wZSBhbm5vdGF0ZWQgQVNUXG4gKiBAcGFyYW0gaWROb2RlIC0gaWRlbnRpZmllciBub2RlIG9mIGludGVyZXN0XG4gKiBAcmV0dXJucyB7QXJyYXl9IC0gYXJyYXkgb2YgQVNUIG5vZGVzXG4gKi9cbmZ1bmN0aW9uIGZpbmRSZWZzVG9WYXJpYWJsZShhc3QsIGlkTm9kZSkge1xuICAgIFwidXNlIHN0cmljdFwiO1xuICAgIHZhciBuYW1lID0gaWROb2RlLm5hbWU7XG5cbiAgICB2YXIgcmVmcyA9IFtdO1xuXG4gICAgLy8gVE9ETzogZmluZCByZWZzIGZvciB0aGUgaWRcbiAgICByZXR1cm4gcmVmcztcbn1cblxuXG4vLyA9PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PVxuXG5mdW5jdGlvbiB0ZXN0KCkge1xuICAgIFwidXNlIHN0cmljdFwiO1xuICAgIHZhciB0ZXN0X3BnbSA9IGZzLnJlYWRGaWxlU3luYygnLi90ZXN0cy9hLmpzJyk7XG4gICAgdmFyIHJlc3VsdCA9IGluZmVyLmFuYWx5emUodGVzdF9wZ20sIHRydWUpO1xuXG4gICAgZm9yICh2YXIgaSA9IDA7IGkgPCB0ZXN0X3BnbS5sZW5ndGg7IGkrKykge1xuICAgICAgICB2YXIgZm91bmROb2RlID0gZmluZElkZW50aWZpZXJOb2RlQXQocmVzdWx0LkFTVCwgaSk7XG4gICAgICAgIGlmIChmb3VuZE5vZGUpIHtcbiAgICAgICAgICAgIGNvbnNvbGUubG9nKGksICc6ICcsIGZvdW5kTm9kZS5uYW1lKTtcbiAgICAgICAgfVxuICAgIH1cbn1cblxuZXhwb3J0cy5maW5kSWRlbnRpZmllck5vZGVBdCA9IGZpbmRJZGVudGlmaWVyTm9kZUF0OyIsIihmdW5jdGlvbihmKXtpZih0eXBlb2YgZXhwb3J0cz09PVwib2JqZWN0XCImJnR5cGVvZiBtb2R1bGUhPT1cInVuZGVmaW5lZFwiKXttb2R1bGUuZXhwb3J0cz1mKCl9ZWxzZSBpZih0eXBlb2YgZGVmaW5lPT09XCJmdW5jdGlvblwiJiZkZWZpbmUuYW1kKXtkZWZpbmUoW10sZil9ZWxzZXt2YXIgZztpZih0eXBlb2Ygd2luZG93IT09XCJ1bmRlZmluZWRcIil7Zz13aW5kb3d9ZWxzZSBpZih0eXBlb2YgZ2xvYmFsIT09XCJ1bmRlZmluZWRcIil7Zz1nbG9iYWx9ZWxzZSBpZih0eXBlb2Ygc2VsZiE9PVwidW5kZWZpbmVkXCIpe2c9c2VsZn1lbHNle2c9dGhpc31nLmFjb3JuID0gZigpfX0pKGZ1bmN0aW9uKCl7dmFyIGRlZmluZSxtb2R1bGUsZXhwb3J0cztyZXR1cm4gKGZ1bmN0aW9uIGUodCxuLHIpe2Z1bmN0aW9uIHMobyx1KXtpZighbltvXSl7aWYoIXRbb10pe3ZhciBhPXR5cGVvZiByZXF1aXJlPT1cImZ1bmN0aW9uXCImJnJlcXVpcmU7aWYoIXUmJmEpcmV0dXJuIGEobywhMCk7aWYoaSlyZXR1cm4gaShvLCEwKTt2YXIgZj1uZXcgRXJyb3IoXCJDYW5ub3QgZmluZCBtb2R1bGUgJ1wiK28rXCInXCIpO3Rocm93IGYuY29kZT1cIk1PRFVMRV9OT1RfRk9VTkRcIixmfXZhciBsPW5bb109e2V4cG9ydHM6e319O3Rbb11bMF0uY2FsbChsLmV4cG9ydHMsZnVuY3Rpb24oZSl7dmFyIG49dFtvXVsxXVtlXTtyZXR1cm4gcyhuP246ZSl9LGwsbC5leHBvcnRzLGUsdCxuLHIpfXJldHVybiBuW29dLmV4cG9ydHN9dmFyIGk9dHlwZW9mIHJlcXVpcmU9PVwiZnVuY3Rpb25cIiYmcmVxdWlyZTtmb3IodmFyIG89MDtvPHIubGVuZ3RoO28rKylzKHJbb10pO3JldHVybiBzfSkoezE6W2Z1bmN0aW9uKF9kZXJlcV8sbW9kdWxlLGV4cG9ydHMpe1xuXG5cbi8vIFRoZSBtYWluIGV4cG9ydGVkIGludGVyZmFjZSAodW5kZXIgYHNlbGYuYWNvcm5gIHdoZW4gaW4gdGhlXG4vLyBicm93c2VyKSBpcyBhIGBwYXJzZWAgZnVuY3Rpb24gdGhhdCB0YWtlcyBhIGNvZGUgc3RyaW5nIGFuZFxuLy8gcmV0dXJucyBhbiBhYnN0cmFjdCBzeW50YXggdHJlZSBhcyBzcGVjaWZpZWQgYnkgW01vemlsbGEgcGFyc2VyXG4vLyBBUEldW2FwaV0uXG4vL1xuLy8gW2FwaV06IGh0dHBzOi8vZGV2ZWxvcGVyLm1vemlsbGEub3JnL2VuLVVTL2RvY3MvU3BpZGVyTW9ua2V5L1BhcnNlcl9BUElcblxuXCJ1c2Ugc3RyaWN0XCI7XG5cbmV4cG9ydHMucGFyc2UgPSBwYXJzZTtcblxuLy8gVGhpcyBmdW5jdGlvbiB0cmllcyB0byBwYXJzZSBhIHNpbmdsZSBleHByZXNzaW9uIGF0IGEgZ2l2ZW5cbi8vIG9mZnNldCBpbiBhIHN0cmluZy4gVXNlZnVsIGZvciBwYXJzaW5nIG1peGVkLWxhbmd1YWdlIGZvcm1hdHNcbi8vIHRoYXQgZW1iZWQgSmF2YVNjcmlwdCBleHByZXNzaW9ucy5cblxuZXhwb3J0cy5wYXJzZUV4cHJlc3Npb25BdCA9IHBhcnNlRXhwcmVzc2lvbkF0O1xuXG4vLyBBY29ybiBpcyBvcmdhbml6ZWQgYXMgYSB0b2tlbml6ZXIgYW5kIGEgcmVjdXJzaXZlLWRlc2NlbnQgcGFyc2VyLlxuLy8gVGhlIGB0b2tlbml6ZWAgZXhwb3J0IHByb3ZpZGVzIGFuIGludGVyZmFjZSB0byB0aGUgdG9rZW5pemVyLlxuXG5leHBvcnRzLnRva2VuaXplciA9IHRva2VuaXplcjtcbmV4cG9ydHMuX19lc01vZHVsZSA9IHRydWU7XG4vLyBBY29ybiBpcyBhIHRpbnksIGZhc3QgSmF2YVNjcmlwdCBwYXJzZXIgd3JpdHRlbiBpbiBKYXZhU2NyaXB0LlxuLy9cbi8vIEFjb3JuIHdhcyB3cml0dGVuIGJ5IE1hcmlqbiBIYXZlcmJla2UsIEluZ3ZhciBTdGVwYW55YW4sIGFuZFxuLy8gdmFyaW91cyBjb250cmlidXRvcnMgYW5kIHJlbGVhc2VkIHVuZGVyIGFuIE1JVCBsaWNlbnNlLlxuLy9cbi8vIEdpdCByZXBvc2l0b3JpZXMgZm9yIEFjb3JuIGFyZSBhdmFpbGFibGUgYXRcbi8vXG4vLyAgICAgaHR0cDovL21hcmlqbmhhdmVyYmVrZS5ubC9naXQvYWNvcm5cbi8vICAgICBodHRwczovL2dpdGh1Yi5jb20vbWFyaWpuaC9hY29ybi5naXRcbi8vXG4vLyBQbGVhc2UgdXNlIHRoZSBbZ2l0aHViIGJ1ZyB0cmFja2VyXVtnaGJ0XSB0byByZXBvcnQgaXNzdWVzLlxuLy9cbi8vIFtnaGJ0XTogaHR0cHM6Ly9naXRodWIuY29tL21hcmlqbmgvYWNvcm4vaXNzdWVzXG4vL1xuLy8gVGhpcyBmaWxlIGRlZmluZXMgdGhlIG1haW4gcGFyc2VyIGludGVyZmFjZS4gVGhlIGxpYnJhcnkgYWxzbyBjb21lc1xuLy8gd2l0aCBhIFtlcnJvci10b2xlcmFudCBwYXJzZXJdW2RhbW1pdF0gYW5kIGFuXG4vLyBbYWJzdHJhY3Qgc3ludGF4IHRyZWUgd2Fsa2VyXVt3YWxrXSwgZGVmaW5lZCBpbiBvdGhlciBmaWxlcy5cbi8vXG4vLyBbZGFtbWl0XTogYWNvcm5fbG9vc2UuanNcbi8vIFt3YWxrXTogdXRpbC93YWxrLmpzXG5cbnZhciBfc3RhdGUgPSBfZGVyZXFfKFwiLi9zdGF0ZVwiKTtcblxudmFyIFBhcnNlciA9IF9zdGF0ZS5QYXJzZXI7XG5cbnZhciBfb3B0aW9ucyA9IF9kZXJlcV8oXCIuL29wdGlvbnNcIik7XG5cbnZhciBnZXRPcHRpb25zID0gX29wdGlvbnMuZ2V0T3B0aW9ucztcblxuX2RlcmVxXyhcIi4vcGFyc2V1dGlsXCIpO1xuXG5fZGVyZXFfKFwiLi9zdGF0ZW1lbnRcIik7XG5cbl9kZXJlcV8oXCIuL2x2YWxcIik7XG5cbl9kZXJlcV8oXCIuL2V4cHJlc3Npb25cIik7XG5cbmV4cG9ydHMuUGFyc2VyID0gX3N0YXRlLlBhcnNlcjtcbmV4cG9ydHMucGx1Z2lucyA9IF9zdGF0ZS5wbHVnaW5zO1xuZXhwb3J0cy5kZWZhdWx0T3B0aW9ucyA9IF9vcHRpb25zLmRlZmF1bHRPcHRpb25zO1xuXG52YXIgX2xvY2F0aW9uID0gX2RlcmVxXyhcIi4vbG9jYXRpb25cIik7XG5cbmV4cG9ydHMuU291cmNlTG9jYXRpb24gPSBfbG9jYXRpb24uU291cmNlTG9jYXRpb247XG5leHBvcnRzLmdldExpbmVJbmZvID0gX2xvY2F0aW9uLmdldExpbmVJbmZvO1xuZXhwb3J0cy5Ob2RlID0gX2RlcmVxXyhcIi4vbm9kZVwiKS5Ob2RlO1xuXG52YXIgX3Rva2VudHlwZSA9IF9kZXJlcV8oXCIuL3Rva2VudHlwZVwiKTtcblxuZXhwb3J0cy5Ub2tlblR5cGUgPSBfdG9rZW50eXBlLlRva2VuVHlwZTtcbmV4cG9ydHMudG9rVHlwZXMgPSBfdG9rZW50eXBlLnR5cGVzO1xuXG52YXIgX3Rva2VuY29udGV4dCA9IF9kZXJlcV8oXCIuL3Rva2VuY29udGV4dFwiKTtcblxuZXhwb3J0cy5Ub2tDb250ZXh0ID0gX3Rva2VuY29udGV4dC5Ub2tDb250ZXh0O1xuZXhwb3J0cy50b2tDb250ZXh0cyA9IF90b2tlbmNvbnRleHQudHlwZXM7XG5cbnZhciBfaWRlbnRpZmllciA9IF9kZXJlcV8oXCIuL2lkZW50aWZpZXJcIik7XG5cbmV4cG9ydHMuaXNJZGVudGlmaWVyQ2hhciA9IF9pZGVudGlmaWVyLmlzSWRlbnRpZmllckNoYXI7XG5leHBvcnRzLmlzSWRlbnRpZmllclN0YXJ0ID0gX2lkZW50aWZpZXIuaXNJZGVudGlmaWVyU3RhcnQ7XG5leHBvcnRzLlRva2VuID0gX2RlcmVxXyhcIi4vdG9rZW5pemVcIikuVG9rZW47XG5cbnZhciBfd2hpdGVzcGFjZSA9IF9kZXJlcV8oXCIuL3doaXRlc3BhY2VcIik7XG5cbmV4cG9ydHMuaXNOZXdMaW5lID0gX3doaXRlc3BhY2UuaXNOZXdMaW5lO1xuZXhwb3J0cy5saW5lQnJlYWsgPSBfd2hpdGVzcGFjZS5saW5lQnJlYWs7XG5leHBvcnRzLmxpbmVCcmVha0cgPSBfd2hpdGVzcGFjZS5saW5lQnJlYWtHO1xudmFyIHZlcnNpb24gPSBcIjEuMi4yXCI7ZXhwb3J0cy52ZXJzaW9uID0gdmVyc2lvbjtcblxuZnVuY3Rpb24gcGFyc2UoaW5wdXQsIG9wdGlvbnMpIHtcbiAgdmFyIHAgPSBwYXJzZXIob3B0aW9ucywgaW5wdXQpO1xuICB2YXIgc3RhcnRQb3MgPSBwLnBvcyxcbiAgICAgIHN0YXJ0TG9jID0gcC5vcHRpb25zLmxvY2F0aW9ucyAmJiBwLmN1clBvc2l0aW9uKCk7XG4gIHAubmV4dFRva2VuKCk7XG4gIHJldHVybiBwLnBhcnNlVG9wTGV2ZWwocC5vcHRpb25zLnByb2dyYW0gfHwgcC5zdGFydE5vZGVBdChzdGFydFBvcywgc3RhcnRMb2MpKTtcbn1cblxuZnVuY3Rpb24gcGFyc2VFeHByZXNzaW9uQXQoaW5wdXQsIHBvcywgb3B0aW9ucykge1xuICB2YXIgcCA9IHBhcnNlcihvcHRpb25zLCBpbnB1dCwgcG9zKTtcbiAgcC5uZXh0VG9rZW4oKTtcbiAgcmV0dXJuIHAucGFyc2VFeHByZXNzaW9uKCk7XG59XG5cbmZ1bmN0aW9uIHRva2VuaXplcihpbnB1dCwgb3B0aW9ucykge1xuICByZXR1cm4gcGFyc2VyKG9wdGlvbnMsIGlucHV0KTtcbn1cblxuZnVuY3Rpb24gcGFyc2VyKG9wdGlvbnMsIGlucHV0KSB7XG4gIHJldHVybiBuZXcgUGFyc2VyKGdldE9wdGlvbnMob3B0aW9ucyksIFN0cmluZyhpbnB1dCkpO1xufVxuXG59LHtcIi4vZXhwcmVzc2lvblwiOjYsXCIuL2lkZW50aWZpZXJcIjo3LFwiLi9sb2NhdGlvblwiOjgsXCIuL2x2YWxcIjo5LFwiLi9ub2RlXCI6MTAsXCIuL29wdGlvbnNcIjoxMSxcIi4vcGFyc2V1dGlsXCI6MTIsXCIuL3N0YXRlXCI6MTMsXCIuL3N0YXRlbWVudFwiOjE0LFwiLi90b2tlbmNvbnRleHRcIjoxNSxcIi4vdG9rZW5pemVcIjoxNixcIi4vdG9rZW50eXBlXCI6MTcsXCIuL3doaXRlc3BhY2VcIjoxOX1dLDI6W2Z1bmN0aW9uKF9kZXJlcV8sbW9kdWxlLGV4cG9ydHMpe1xuaWYgKHR5cGVvZiBPYmplY3QuY3JlYXRlID09PSAnZnVuY3Rpb24nKSB7XG4gIC8vIGltcGxlbWVudGF0aW9uIGZyb20gc3RhbmRhcmQgbm9kZS5qcyAndXRpbCcgbW9kdWxlXG4gIG1vZHVsZS5leHBvcnRzID0gZnVuY3Rpb24gaW5oZXJpdHMoY3Rvciwgc3VwZXJDdG9yKSB7XG4gICAgY3Rvci5zdXBlcl8gPSBzdXBlckN0b3JcbiAgICBjdG9yLnByb3RvdHlwZSA9IE9iamVjdC5jcmVhdGUoc3VwZXJDdG9yLnByb3RvdHlwZSwge1xuICAgICAgY29uc3RydWN0b3I6IHtcbiAgICAgICAgdmFsdWU6IGN0b3IsXG4gICAgICAgIGVudW1lcmFibGU6IGZhbHNlLFxuICAgICAgICB3cml0YWJsZTogdHJ1ZSxcbiAgICAgICAgY29uZmlndXJhYmxlOiB0cnVlXG4gICAgICB9XG4gICAgfSk7XG4gIH07XG59IGVsc2Uge1xuICAvLyBvbGQgc2Nob29sIHNoaW0gZm9yIG9sZCBicm93c2Vyc1xuICBtb2R1bGUuZXhwb3J0cyA9IGZ1bmN0aW9uIGluaGVyaXRzKGN0b3IsIHN1cGVyQ3Rvcikge1xuICAgIGN0b3Iuc3VwZXJfID0gc3VwZXJDdG9yXG4gICAgdmFyIFRlbXBDdG9yID0gZnVuY3Rpb24gKCkge31cbiAgICBUZW1wQ3Rvci5wcm90b3R5cGUgPSBzdXBlckN0b3IucHJvdG90eXBlXG4gICAgY3Rvci5wcm90b3R5cGUgPSBuZXcgVGVtcEN0b3IoKVxuICAgIGN0b3IucHJvdG90eXBlLmNvbnN0cnVjdG9yID0gY3RvclxuICB9XG59XG5cbn0se31dLDM6W2Z1bmN0aW9uKF9kZXJlcV8sbW9kdWxlLGV4cG9ydHMpe1xuLy8gc2hpbSBmb3IgdXNpbmcgcHJvY2VzcyBpbiBicm93c2VyXG5cbnZhciBwcm9jZXNzID0gbW9kdWxlLmV4cG9ydHMgPSB7fTtcbnZhciBxdWV1ZSA9IFtdO1xudmFyIGRyYWluaW5nID0gZmFsc2U7XG5cbmZ1bmN0aW9uIGRyYWluUXVldWUoKSB7XG4gICAgaWYgKGRyYWluaW5nKSB7XG4gICAgICAgIHJldHVybjtcbiAgICB9XG4gICAgZHJhaW5pbmcgPSB0cnVlO1xuICAgIHZhciBjdXJyZW50UXVldWU7XG4gICAgdmFyIGxlbiA9IHF1ZXVlLmxlbmd0aDtcbiAgICB3aGlsZShsZW4pIHtcbiAgICAgICAgY3VycmVudFF1ZXVlID0gcXVldWU7XG4gICAgICAgIHF1ZXVlID0gW107XG4gICAgICAgIHZhciBpID0gLTE7XG4gICAgICAgIHdoaWxlICgrK2kgPCBsZW4pIHtcbiAgICAgICAgICAgIGN1cnJlbnRRdWV1ZVtpXSgpO1xuICAgICAgICB9XG4gICAgICAgIGxlbiA9IHF1ZXVlLmxlbmd0aDtcbiAgICB9XG4gICAgZHJhaW5pbmcgPSBmYWxzZTtcbn1cbnByb2Nlc3MubmV4dFRpY2sgPSBmdW5jdGlvbiAoZnVuKSB7XG4gICAgcXVldWUucHVzaChmdW4pO1xuICAgIGlmICghZHJhaW5pbmcpIHtcbiAgICAgICAgc2V0VGltZW91dChkcmFpblF1ZXVlLCAwKTtcbiAgICB9XG59O1xuXG5wcm9jZXNzLnRpdGxlID0gJ2Jyb3dzZXInO1xucHJvY2Vzcy5icm93c2VyID0gdHJ1ZTtcbnByb2Nlc3MuZW52ID0ge307XG5wcm9jZXNzLmFyZ3YgPSBbXTtcbnByb2Nlc3MudmVyc2lvbiA9ICcnOyAvLyBlbXB0eSBzdHJpbmcgdG8gYXZvaWQgcmVnZXhwIGlzc3Vlc1xucHJvY2Vzcy52ZXJzaW9ucyA9IHt9O1xuXG5mdW5jdGlvbiBub29wKCkge31cblxucHJvY2Vzcy5vbiA9IG5vb3A7XG5wcm9jZXNzLmFkZExpc3RlbmVyID0gbm9vcDtcbnByb2Nlc3Mub25jZSA9IG5vb3A7XG5wcm9jZXNzLm9mZiA9IG5vb3A7XG5wcm9jZXNzLnJlbW92ZUxpc3RlbmVyID0gbm9vcDtcbnByb2Nlc3MucmVtb3ZlQWxsTGlzdGVuZXJzID0gbm9vcDtcbnByb2Nlc3MuZW1pdCA9IG5vb3A7XG5cbnByb2Nlc3MuYmluZGluZyA9IGZ1bmN0aW9uIChuYW1lKSB7XG4gICAgdGhyb3cgbmV3IEVycm9yKCdwcm9jZXNzLmJpbmRpbmcgaXMgbm90IHN1cHBvcnRlZCcpO1xufTtcblxuLy8gVE9ETyhzaHR5bG1hbilcbnByb2Nlc3MuY3dkID0gZnVuY3Rpb24gKCkgeyByZXR1cm4gJy8nIH07XG5wcm9jZXNzLmNoZGlyID0gZnVuY3Rpb24gKGRpcikge1xuICAgIHRocm93IG5ldyBFcnJvcigncHJvY2Vzcy5jaGRpciBpcyBub3Qgc3VwcG9ydGVkJyk7XG59O1xucHJvY2Vzcy51bWFzayA9IGZ1bmN0aW9uKCkgeyByZXR1cm4gMDsgfTtcblxufSx7fV0sNDpbZnVuY3Rpb24oX2RlcmVxXyxtb2R1bGUsZXhwb3J0cyl7XG5tb2R1bGUuZXhwb3J0cyA9IGZ1bmN0aW9uIGlzQnVmZmVyKGFyZykge1xuICByZXR1cm4gYXJnICYmIHR5cGVvZiBhcmcgPT09ICdvYmplY3QnXG4gICAgJiYgdHlwZW9mIGFyZy5jb3B5ID09PSAnZnVuY3Rpb24nXG4gICAgJiYgdHlwZW9mIGFyZy5maWxsID09PSAnZnVuY3Rpb24nXG4gICAgJiYgdHlwZW9mIGFyZy5yZWFkVUludDggPT09ICdmdW5jdGlvbic7XG59XG59LHt9XSw1OltmdW5jdGlvbihfZGVyZXFfLG1vZHVsZSxleHBvcnRzKXtcbihmdW5jdGlvbiAocHJvY2VzcyxnbG9iYWwpe1xuLy8gQ29weXJpZ2h0IEpveWVudCwgSW5jLiBhbmQgb3RoZXIgTm9kZSBjb250cmlidXRvcnMuXG4vL1xuLy8gUGVybWlzc2lvbiBpcyBoZXJlYnkgZ3JhbnRlZCwgZnJlZSBvZiBjaGFyZ2UsIHRvIGFueSBwZXJzb24gb2J0YWluaW5nIGFcbi8vIGNvcHkgb2YgdGhpcyBzb2Z0d2FyZSBhbmQgYXNzb2NpYXRlZCBkb2N1bWVudGF0aW9uIGZpbGVzICh0aGVcbi8vIFwiU29mdHdhcmVcIiksIHRvIGRlYWwgaW4gdGhlIFNvZnR3YXJlIHdpdGhvdXQgcmVzdHJpY3Rpb24sIGluY2x1ZGluZ1xuLy8gd2l0aG91dCBsaW1pdGF0aW9uIHRoZSByaWdodHMgdG8gdXNlLCBjb3B5LCBtb2RpZnksIG1lcmdlLCBwdWJsaXNoLFxuLy8gZGlzdHJpYnV0ZSwgc3VibGljZW5zZSwgYW5kL29yIHNlbGwgY29waWVzIG9mIHRoZSBTb2Z0d2FyZSwgYW5kIHRvIHBlcm1pdFxuLy8gcGVyc29ucyB0byB3aG9tIHRoZSBTb2Z0d2FyZSBpcyBmdXJuaXNoZWQgdG8gZG8gc28sIHN1YmplY3QgdG8gdGhlXG4vLyBmb2xsb3dpbmcgY29uZGl0aW9uczpcbi8vXG4vLyBUaGUgYWJvdmUgY29weXJpZ2h0IG5vdGljZSBhbmQgdGhpcyBwZXJtaXNzaW9uIG5vdGljZSBzaGFsbCBiZSBpbmNsdWRlZFxuLy8gaW4gYWxsIGNvcGllcyBvciBzdWJzdGFudGlhbCBwb3J0aW9ucyBvZiB0aGUgU29mdHdhcmUuXG4vL1xuLy8gVEhFIFNPRlRXQVJFIElTIFBST1ZJREVEIFwiQVMgSVNcIiwgV0lUSE9VVCBXQVJSQU5UWSBPRiBBTlkgS0lORCwgRVhQUkVTU1xuLy8gT1IgSU1QTElFRCwgSU5DTFVESU5HIEJVVCBOT1QgTElNSVRFRCBUTyBUSEUgV0FSUkFOVElFUyBPRlxuLy8gTUVSQ0hBTlRBQklMSVRZLCBGSVRORVNTIEZPUiBBIFBBUlRJQ1VMQVIgUFVSUE9TRSBBTkQgTk9OSU5GUklOR0VNRU5ULiBJTlxuLy8gTk8gRVZFTlQgU0hBTEwgVEhFIEFVVEhPUlMgT1IgQ09QWVJJR0hUIEhPTERFUlMgQkUgTElBQkxFIEZPUiBBTlkgQ0xBSU0sXG4vLyBEQU1BR0VTIE9SIE9USEVSIExJQUJJTElUWSwgV0hFVEhFUiBJTiBBTiBBQ1RJT04gT0YgQ09OVFJBQ1QsIFRPUlQgT1Jcbi8vIE9USEVSV0lTRSwgQVJJU0lORyBGUk9NLCBPVVQgT0YgT1IgSU4gQ09OTkVDVElPTiBXSVRIIFRIRSBTT0ZUV0FSRSBPUiBUSEVcbi8vIFVTRSBPUiBPVEhFUiBERUFMSU5HUyBJTiBUSEUgU09GVFdBUkUuXG5cbnZhciBmb3JtYXRSZWdFeHAgPSAvJVtzZGolXS9nO1xuZXhwb3J0cy5mb3JtYXQgPSBmdW5jdGlvbihmKSB7XG4gIGlmICghaXNTdHJpbmcoZikpIHtcbiAgICB2YXIgb2JqZWN0cyA9IFtdO1xuICAgIGZvciAodmFyIGkgPSAwOyBpIDwgYXJndW1lbnRzLmxlbmd0aDsgaSsrKSB7XG4gICAgICBvYmplY3RzLnB1c2goaW5zcGVjdChhcmd1bWVudHNbaV0pKTtcbiAgICB9XG4gICAgcmV0dXJuIG9iamVjdHMuam9pbignICcpO1xuICB9XG5cbiAgdmFyIGkgPSAxO1xuICB2YXIgYXJncyA9IGFyZ3VtZW50cztcbiAgdmFyIGxlbiA9IGFyZ3MubGVuZ3RoO1xuICB2YXIgc3RyID0gU3RyaW5nKGYpLnJlcGxhY2UoZm9ybWF0UmVnRXhwLCBmdW5jdGlvbih4KSB7XG4gICAgaWYgKHggPT09ICclJScpIHJldHVybiAnJSc7XG4gICAgaWYgKGkgPj0gbGVuKSByZXR1cm4geDtcbiAgICBzd2l0Y2ggKHgpIHtcbiAgICAgIGNhc2UgJyVzJzogcmV0dXJuIFN0cmluZyhhcmdzW2krK10pO1xuICAgICAgY2FzZSAnJWQnOiByZXR1cm4gTnVtYmVyKGFyZ3NbaSsrXSk7XG4gICAgICBjYXNlICclaic6XG4gICAgICAgIHRyeSB7XG4gICAgICAgICAgcmV0dXJuIEpTT04uc3RyaW5naWZ5KGFyZ3NbaSsrXSk7XG4gICAgICAgIH0gY2F0Y2ggKF8pIHtcbiAgICAgICAgICByZXR1cm4gJ1tDaXJjdWxhcl0nO1xuICAgICAgICB9XG4gICAgICBkZWZhdWx0OlxuICAgICAgICByZXR1cm4geDtcbiAgICB9XG4gIH0pO1xuICBmb3IgKHZhciB4ID0gYXJnc1tpXTsgaSA8IGxlbjsgeCA9IGFyZ3NbKytpXSkge1xuICAgIGlmIChpc051bGwoeCkgfHwgIWlzT2JqZWN0KHgpKSB7XG4gICAgICBzdHIgKz0gJyAnICsgeDtcbiAgICB9IGVsc2Uge1xuICAgICAgc3RyICs9ICcgJyArIGluc3BlY3QoeCk7XG4gICAgfVxuICB9XG4gIHJldHVybiBzdHI7XG59O1xuXG5cbi8vIE1hcmsgdGhhdCBhIG1ldGhvZCBzaG91bGQgbm90IGJlIHVzZWQuXG4vLyBSZXR1cm5zIGEgbW9kaWZpZWQgZnVuY3Rpb24gd2hpY2ggd2FybnMgb25jZSBieSBkZWZhdWx0LlxuLy8gSWYgLS1uby1kZXByZWNhdGlvbiBpcyBzZXQsIHRoZW4gaXQgaXMgYSBuby1vcC5cbmV4cG9ydHMuZGVwcmVjYXRlID0gZnVuY3Rpb24oZm4sIG1zZykge1xuICAvLyBBbGxvdyBmb3IgZGVwcmVjYXRpbmcgdGhpbmdzIGluIHRoZSBwcm9jZXNzIG9mIHN0YXJ0aW5nIHVwLlxuICBpZiAoaXNVbmRlZmluZWQoZ2xvYmFsLnByb2Nlc3MpKSB7XG4gICAgcmV0dXJuIGZ1bmN0aW9uKCkge1xuICAgICAgcmV0dXJuIGV4cG9ydHMuZGVwcmVjYXRlKGZuLCBtc2cpLmFwcGx5KHRoaXMsIGFyZ3VtZW50cyk7XG4gICAgfTtcbiAgfVxuXG4gIGlmIChwcm9jZXNzLm5vRGVwcmVjYXRpb24gPT09IHRydWUpIHtcbiAgICByZXR1cm4gZm47XG4gIH1cblxuICB2YXIgd2FybmVkID0gZmFsc2U7XG4gIGZ1bmN0aW9uIGRlcHJlY2F0ZWQoKSB7XG4gICAgaWYgKCF3YXJuZWQpIHtcbiAgICAgIGlmIChwcm9jZXNzLnRocm93RGVwcmVjYXRpb24pIHtcbiAgICAgICAgdGhyb3cgbmV3IEVycm9yKG1zZyk7XG4gICAgICB9IGVsc2UgaWYgKHByb2Nlc3MudHJhY2VEZXByZWNhdGlvbikge1xuICAgICAgICBjb25zb2xlLnRyYWNlKG1zZyk7XG4gICAgICB9IGVsc2Uge1xuICAgICAgICBjb25zb2xlLmVycm9yKG1zZyk7XG4gICAgICB9XG4gICAgICB3YXJuZWQgPSB0cnVlO1xuICAgIH1cbiAgICByZXR1cm4gZm4uYXBwbHkodGhpcywgYXJndW1lbnRzKTtcbiAgfVxuXG4gIHJldHVybiBkZXByZWNhdGVkO1xufTtcblxuXG52YXIgZGVidWdzID0ge307XG52YXIgZGVidWdFbnZpcm9uO1xuZXhwb3J0cy5kZWJ1Z2xvZyA9IGZ1bmN0aW9uKHNldCkge1xuICBpZiAoaXNVbmRlZmluZWQoZGVidWdFbnZpcm9uKSlcbiAgICBkZWJ1Z0Vudmlyb24gPSBwcm9jZXNzLmVudi5OT0RFX0RFQlVHIHx8ICcnO1xuICBzZXQgPSBzZXQudG9VcHBlckNhc2UoKTtcbiAgaWYgKCFkZWJ1Z3Nbc2V0XSkge1xuICAgIGlmIChuZXcgUmVnRXhwKCdcXFxcYicgKyBzZXQgKyAnXFxcXGInLCAnaScpLnRlc3QoZGVidWdFbnZpcm9uKSkge1xuICAgICAgdmFyIHBpZCA9IHByb2Nlc3MucGlkO1xuICAgICAgZGVidWdzW3NldF0gPSBmdW5jdGlvbigpIHtcbiAgICAgICAgdmFyIG1zZyA9IGV4cG9ydHMuZm9ybWF0LmFwcGx5KGV4cG9ydHMsIGFyZ3VtZW50cyk7XG4gICAgICAgIGNvbnNvbGUuZXJyb3IoJyVzICVkOiAlcycsIHNldCwgcGlkLCBtc2cpO1xuICAgICAgfTtcbiAgICB9IGVsc2Uge1xuICAgICAgZGVidWdzW3NldF0gPSBmdW5jdGlvbigpIHt9O1xuICAgIH1cbiAgfVxuICByZXR1cm4gZGVidWdzW3NldF07XG59O1xuXG5cbi8qKlxuICogRWNob3MgdGhlIHZhbHVlIG9mIGEgdmFsdWUuIFRyeXMgdG8gcHJpbnQgdGhlIHZhbHVlIG91dFxuICogaW4gdGhlIGJlc3Qgd2F5IHBvc3NpYmxlIGdpdmVuIHRoZSBkaWZmZXJlbnQgdHlwZXMuXG4gKlxuICogQHBhcmFtIHtPYmplY3R9IG9iaiBUaGUgb2JqZWN0IHRvIHByaW50IG91dC5cbiAqIEBwYXJhbSB7T2JqZWN0fSBvcHRzIE9wdGlvbmFsIG9wdGlvbnMgb2JqZWN0IHRoYXQgYWx0ZXJzIHRoZSBvdXRwdXQuXG4gKi9cbi8qIGxlZ2FjeTogb2JqLCBzaG93SGlkZGVuLCBkZXB0aCwgY29sb3JzKi9cbmZ1bmN0aW9uIGluc3BlY3Qob2JqLCBvcHRzKSB7XG4gIC8vIGRlZmF1bHQgb3B0aW9uc1xuICB2YXIgY3R4ID0ge1xuICAgIHNlZW46IFtdLFxuICAgIHN0eWxpemU6IHN0eWxpemVOb0NvbG9yXG4gIH07XG4gIC8vIGxlZ2FjeS4uLlxuICBpZiAoYXJndW1lbnRzLmxlbmd0aCA+PSAzKSBjdHguZGVwdGggPSBhcmd1bWVudHNbMl07XG4gIGlmIChhcmd1bWVudHMubGVuZ3RoID49IDQpIGN0eC5jb2xvcnMgPSBhcmd1bWVudHNbM107XG4gIGlmIChpc0Jvb2xlYW4ob3B0cykpIHtcbiAgICAvLyBsZWdhY3kuLi5cbiAgICBjdHguc2hvd0hpZGRlbiA9IG9wdHM7XG4gIH0gZWxzZSBpZiAob3B0cykge1xuICAgIC8vIGdvdCBhbiBcIm9wdGlvbnNcIiBvYmplY3RcbiAgICBleHBvcnRzLl9leHRlbmQoY3R4LCBvcHRzKTtcbiAgfVxuICAvLyBzZXQgZGVmYXVsdCBvcHRpb25zXG4gIGlmIChpc1VuZGVmaW5lZChjdHguc2hvd0hpZGRlbikpIGN0eC5zaG93SGlkZGVuID0gZmFsc2U7XG4gIGlmIChpc1VuZGVmaW5lZChjdHguZGVwdGgpKSBjdHguZGVwdGggPSAyO1xuICBpZiAoaXNVbmRlZmluZWQoY3R4LmNvbG9ycykpIGN0eC5jb2xvcnMgPSBmYWxzZTtcbiAgaWYgKGlzVW5kZWZpbmVkKGN0eC5jdXN0b21JbnNwZWN0KSkgY3R4LmN1c3RvbUluc3BlY3QgPSB0cnVlO1xuICBpZiAoY3R4LmNvbG9ycykgY3R4LnN0eWxpemUgPSBzdHlsaXplV2l0aENvbG9yO1xuICByZXR1cm4gZm9ybWF0VmFsdWUoY3R4LCBvYmosIGN0eC5kZXB0aCk7XG59XG5leHBvcnRzLmluc3BlY3QgPSBpbnNwZWN0O1xuXG5cbi8vIGh0dHA6Ly9lbi53aWtpcGVkaWEub3JnL3dpa2kvQU5TSV9lc2NhcGVfY29kZSNncmFwaGljc1xuaW5zcGVjdC5jb2xvcnMgPSB7XG4gICdib2xkJyA6IFsxLCAyMl0sXG4gICdpdGFsaWMnIDogWzMsIDIzXSxcbiAgJ3VuZGVybGluZScgOiBbNCwgMjRdLFxuICAnaW52ZXJzZScgOiBbNywgMjddLFxuICAnd2hpdGUnIDogWzM3LCAzOV0sXG4gICdncmV5JyA6IFs5MCwgMzldLFxuICAnYmxhY2snIDogWzMwLCAzOV0sXG4gICdibHVlJyA6IFszNCwgMzldLFxuICAnY3lhbicgOiBbMzYsIDM5XSxcbiAgJ2dyZWVuJyA6IFszMiwgMzldLFxuICAnbWFnZW50YScgOiBbMzUsIDM5XSxcbiAgJ3JlZCcgOiBbMzEsIDM5XSxcbiAgJ3llbGxvdycgOiBbMzMsIDM5XVxufTtcblxuLy8gRG9uJ3QgdXNlICdibHVlJyBub3QgdmlzaWJsZSBvbiBjbWQuZXhlXG5pbnNwZWN0LnN0eWxlcyA9IHtcbiAgJ3NwZWNpYWwnOiAnY3lhbicsXG4gICdudW1iZXInOiAneWVsbG93JyxcbiAgJ2Jvb2xlYW4nOiAneWVsbG93JyxcbiAgJ3VuZGVmaW5lZCc6ICdncmV5JyxcbiAgJ251bGwnOiAnYm9sZCcsXG4gICdzdHJpbmcnOiAnZ3JlZW4nLFxuICAnZGF0ZSc6ICdtYWdlbnRhJyxcbiAgLy8gXCJuYW1lXCI6IGludGVudGlvbmFsbHkgbm90IHN0eWxpbmdcbiAgJ3JlZ2V4cCc6ICdyZWQnXG59O1xuXG5cbmZ1bmN0aW9uIHN0eWxpemVXaXRoQ29sb3Ioc3RyLCBzdHlsZVR5cGUpIHtcbiAgdmFyIHN0eWxlID0gaW5zcGVjdC5zdHlsZXNbc3R5bGVUeXBlXTtcblxuICBpZiAoc3R5bGUpIHtcbiAgICByZXR1cm4gJ1xcdTAwMWJbJyArIGluc3BlY3QuY29sb3JzW3N0eWxlXVswXSArICdtJyArIHN0ciArXG4gICAgICAgICAgICdcXHUwMDFiWycgKyBpbnNwZWN0LmNvbG9yc1tzdHlsZV1bMV0gKyAnbSc7XG4gIH0gZWxzZSB7XG4gICAgcmV0dXJuIHN0cjtcbiAgfVxufVxuXG5cbmZ1bmN0aW9uIHN0eWxpemVOb0NvbG9yKHN0ciwgc3R5bGVUeXBlKSB7XG4gIHJldHVybiBzdHI7XG59XG5cblxuZnVuY3Rpb24gYXJyYXlUb0hhc2goYXJyYXkpIHtcbiAgdmFyIGhhc2ggPSB7fTtcblxuICBhcnJheS5mb3JFYWNoKGZ1bmN0aW9uKHZhbCwgaWR4KSB7XG4gICAgaGFzaFt2YWxdID0gdHJ1ZTtcbiAgfSk7XG5cbiAgcmV0dXJuIGhhc2g7XG59XG5cblxuZnVuY3Rpb24gZm9ybWF0VmFsdWUoY3R4LCB2YWx1ZSwgcmVjdXJzZVRpbWVzKSB7XG4gIC8vIFByb3ZpZGUgYSBob29rIGZvciB1c2VyLXNwZWNpZmllZCBpbnNwZWN0IGZ1bmN0aW9ucy5cbiAgLy8gQ2hlY2sgdGhhdCB2YWx1ZSBpcyBhbiBvYmplY3Qgd2l0aCBhbiBpbnNwZWN0IGZ1bmN0aW9uIG9uIGl0XG4gIGlmIChjdHguY3VzdG9tSW5zcGVjdCAmJlxuICAgICAgdmFsdWUgJiZcbiAgICAgIGlzRnVuY3Rpb24odmFsdWUuaW5zcGVjdCkgJiZcbiAgICAgIC8vIEZpbHRlciBvdXQgdGhlIHV0aWwgbW9kdWxlLCBpdCdzIGluc3BlY3QgZnVuY3Rpb24gaXMgc3BlY2lhbFxuICAgICAgdmFsdWUuaW5zcGVjdCAhPT0gZXhwb3J0cy5pbnNwZWN0ICYmXG4gICAgICAvLyBBbHNvIGZpbHRlciBvdXQgYW55IHByb3RvdHlwZSBvYmplY3RzIHVzaW5nIHRoZSBjaXJjdWxhciBjaGVjay5cbiAgICAgICEodmFsdWUuY29uc3RydWN0b3IgJiYgdmFsdWUuY29uc3RydWN0b3IucHJvdG90eXBlID09PSB2YWx1ZSkpIHtcbiAgICB2YXIgcmV0ID0gdmFsdWUuaW5zcGVjdChyZWN1cnNlVGltZXMsIGN0eCk7XG4gICAgaWYgKCFpc1N0cmluZyhyZXQpKSB7XG4gICAgICByZXQgPSBmb3JtYXRWYWx1ZShjdHgsIHJldCwgcmVjdXJzZVRpbWVzKTtcbiAgICB9XG4gICAgcmV0dXJuIHJldDtcbiAgfVxuXG4gIC8vIFByaW1pdGl2ZSB0eXBlcyBjYW5ub3QgaGF2ZSBwcm9wZXJ0aWVzXG4gIHZhciBwcmltaXRpdmUgPSBmb3JtYXRQcmltaXRpdmUoY3R4LCB2YWx1ZSk7XG4gIGlmIChwcmltaXRpdmUpIHtcbiAgICByZXR1cm4gcHJpbWl0aXZlO1xuICB9XG5cbiAgLy8gTG9vayB1cCB0aGUga2V5cyBvZiB0aGUgb2JqZWN0LlxuICB2YXIga2V5cyA9IE9iamVjdC5rZXlzKHZhbHVlKTtcbiAgdmFyIHZpc2libGVLZXlzID0gYXJyYXlUb0hhc2goa2V5cyk7XG5cbiAgaWYgKGN0eC5zaG93SGlkZGVuKSB7XG4gICAga2V5cyA9IE9iamVjdC5nZXRPd25Qcm9wZXJ0eU5hbWVzKHZhbHVlKTtcbiAgfVxuXG4gIC8vIElFIGRvZXNuJ3QgbWFrZSBlcnJvciBmaWVsZHMgbm9uLWVudW1lcmFibGVcbiAgLy8gaHR0cDovL21zZG4ubWljcm9zb2Z0LmNvbS9lbi11cy9saWJyYXJ5L2llL2R3dzUyc2J0KHY9dnMuOTQpLmFzcHhcbiAgaWYgKGlzRXJyb3IodmFsdWUpXG4gICAgICAmJiAoa2V5cy5pbmRleE9mKCdtZXNzYWdlJykgPj0gMCB8fCBrZXlzLmluZGV4T2YoJ2Rlc2NyaXB0aW9uJykgPj0gMCkpIHtcbiAgICByZXR1cm4gZm9ybWF0RXJyb3IodmFsdWUpO1xuICB9XG5cbiAgLy8gU29tZSB0eXBlIG9mIG9iamVjdCB3aXRob3V0IHByb3BlcnRpZXMgY2FuIGJlIHNob3J0Y3V0dGVkLlxuICBpZiAoa2V5cy5sZW5ndGggPT09IDApIHtcbiAgICBpZiAoaXNGdW5jdGlvbih2YWx1ZSkpIHtcbiAgICAgIHZhciBuYW1lID0gdmFsdWUubmFtZSA/ICc6ICcgKyB2YWx1ZS5uYW1lIDogJyc7XG4gICAgICByZXR1cm4gY3R4LnN0eWxpemUoJ1tGdW5jdGlvbicgKyBuYW1lICsgJ10nLCAnc3BlY2lhbCcpO1xuICAgIH1cbiAgICBpZiAoaXNSZWdFeHAodmFsdWUpKSB7XG4gICAgICByZXR1cm4gY3R4LnN0eWxpemUoUmVnRXhwLnByb3RvdHlwZS50b1N0cmluZy5jYWxsKHZhbHVlKSwgJ3JlZ2V4cCcpO1xuICAgIH1cbiAgICBpZiAoaXNEYXRlKHZhbHVlKSkge1xuICAgICAgcmV0dXJuIGN0eC5zdHlsaXplKERhdGUucHJvdG90eXBlLnRvU3RyaW5nLmNhbGwodmFsdWUpLCAnZGF0ZScpO1xuICAgIH1cbiAgICBpZiAoaXNFcnJvcih2YWx1ZSkpIHtcbiAgICAgIHJldHVybiBmb3JtYXRFcnJvcih2YWx1ZSk7XG4gICAgfVxuICB9XG5cbiAgdmFyIGJhc2UgPSAnJywgYXJyYXkgPSBmYWxzZSwgYnJhY2VzID0gWyd7JywgJ30nXTtcblxuICAvLyBNYWtlIEFycmF5IHNheSB0aGF0IHRoZXkgYXJlIEFycmF5XG4gIGlmIChpc0FycmF5KHZhbHVlKSkge1xuICAgIGFycmF5ID0gdHJ1ZTtcbiAgICBicmFjZXMgPSBbJ1snLCAnXSddO1xuICB9XG5cbiAgLy8gTWFrZSBmdW5jdGlvbnMgc2F5IHRoYXQgdGhleSBhcmUgZnVuY3Rpb25zXG4gIGlmIChpc0Z1bmN0aW9uKHZhbHVlKSkge1xuICAgIHZhciBuID0gdmFsdWUubmFtZSA/ICc6ICcgKyB2YWx1ZS5uYW1lIDogJyc7XG4gICAgYmFzZSA9ICcgW0Z1bmN0aW9uJyArIG4gKyAnXSc7XG4gIH1cblxuICAvLyBNYWtlIFJlZ0V4cHMgc2F5IHRoYXQgdGhleSBhcmUgUmVnRXhwc1xuICBpZiAoaXNSZWdFeHAodmFsdWUpKSB7XG4gICAgYmFzZSA9ICcgJyArIFJlZ0V4cC5wcm90b3R5cGUudG9TdHJpbmcuY2FsbCh2YWx1ZSk7XG4gIH1cblxuICAvLyBNYWtlIGRhdGVzIHdpdGggcHJvcGVydGllcyBmaXJzdCBzYXkgdGhlIGRhdGVcbiAgaWYgKGlzRGF0ZSh2YWx1ZSkpIHtcbiAgICBiYXNlID0gJyAnICsgRGF0ZS5wcm90b3R5cGUudG9VVENTdHJpbmcuY2FsbCh2YWx1ZSk7XG4gIH1cblxuICAvLyBNYWtlIGVycm9yIHdpdGggbWVzc2FnZSBmaXJzdCBzYXkgdGhlIGVycm9yXG4gIGlmIChpc0Vycm9yKHZhbHVlKSkge1xuICAgIGJhc2UgPSAnICcgKyBmb3JtYXRFcnJvcih2YWx1ZSk7XG4gIH1cblxuICBpZiAoa2V5cy5sZW5ndGggPT09IDAgJiYgKCFhcnJheSB8fCB2YWx1ZS5sZW5ndGggPT0gMCkpIHtcbiAgICByZXR1cm4gYnJhY2VzWzBdICsgYmFzZSArIGJyYWNlc1sxXTtcbiAgfVxuXG4gIGlmIChyZWN1cnNlVGltZXMgPCAwKSB7XG4gICAgaWYgKGlzUmVnRXhwKHZhbHVlKSkge1xuICAgICAgcmV0dXJuIGN0eC5zdHlsaXplKFJlZ0V4cC5wcm90b3R5cGUudG9TdHJpbmcuY2FsbCh2YWx1ZSksICdyZWdleHAnKTtcbiAgICB9IGVsc2Uge1xuICAgICAgcmV0dXJuIGN0eC5zdHlsaXplKCdbT2JqZWN0XScsICdzcGVjaWFsJyk7XG4gICAgfVxuICB9XG5cbiAgY3R4LnNlZW4ucHVzaCh2YWx1ZSk7XG5cbiAgdmFyIG91dHB1dDtcbiAgaWYgKGFycmF5KSB7XG4gICAgb3V0cHV0ID0gZm9ybWF0QXJyYXkoY3R4LCB2YWx1ZSwgcmVjdXJzZVRpbWVzLCB2aXNpYmxlS2V5cywga2V5cyk7XG4gIH0gZWxzZSB7XG4gICAgb3V0cHV0ID0ga2V5cy5tYXAoZnVuY3Rpb24oa2V5KSB7XG4gICAgICByZXR1cm4gZm9ybWF0UHJvcGVydHkoY3R4LCB2YWx1ZSwgcmVjdXJzZVRpbWVzLCB2aXNpYmxlS2V5cywga2V5LCBhcnJheSk7XG4gICAgfSk7XG4gIH1cblxuICBjdHguc2Vlbi5wb3AoKTtcblxuICByZXR1cm4gcmVkdWNlVG9TaW5nbGVTdHJpbmcob3V0cHV0LCBiYXNlLCBicmFjZXMpO1xufVxuXG5cbmZ1bmN0aW9uIGZvcm1hdFByaW1pdGl2ZShjdHgsIHZhbHVlKSB7XG4gIGlmIChpc1VuZGVmaW5lZCh2YWx1ZSkpXG4gICAgcmV0dXJuIGN0eC5zdHlsaXplKCd1bmRlZmluZWQnLCAndW5kZWZpbmVkJyk7XG4gIGlmIChpc1N0cmluZyh2YWx1ZSkpIHtcbiAgICB2YXIgc2ltcGxlID0gJ1xcJycgKyBKU09OLnN0cmluZ2lmeSh2YWx1ZSkucmVwbGFjZSgvXlwifFwiJC9nLCAnJylcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIC5yZXBsYWNlKC8nL2csIFwiXFxcXCdcIilcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIC5yZXBsYWNlKC9cXFxcXCIvZywgJ1wiJykgKyAnXFwnJztcbiAgICByZXR1cm4gY3R4LnN0eWxpemUoc2ltcGxlLCAnc3RyaW5nJyk7XG4gIH1cbiAgaWYgKGlzTnVtYmVyKHZhbHVlKSlcbiAgICByZXR1cm4gY3R4LnN0eWxpemUoJycgKyB2YWx1ZSwgJ251bWJlcicpO1xuICBpZiAoaXNCb29sZWFuKHZhbHVlKSlcbiAgICByZXR1cm4gY3R4LnN0eWxpemUoJycgKyB2YWx1ZSwgJ2Jvb2xlYW4nKTtcbiAgLy8gRm9yIHNvbWUgcmVhc29uIHR5cGVvZiBudWxsIGlzIFwib2JqZWN0XCIsIHNvIHNwZWNpYWwgY2FzZSBoZXJlLlxuICBpZiAoaXNOdWxsKHZhbHVlKSlcbiAgICByZXR1cm4gY3R4LnN0eWxpemUoJ251bGwnLCAnbnVsbCcpO1xufVxuXG5cbmZ1bmN0aW9uIGZvcm1hdEVycm9yKHZhbHVlKSB7XG4gIHJldHVybiAnWycgKyBFcnJvci5wcm90b3R5cGUudG9TdHJpbmcuY2FsbCh2YWx1ZSkgKyAnXSc7XG59XG5cblxuZnVuY3Rpb24gZm9ybWF0QXJyYXkoY3R4LCB2YWx1ZSwgcmVjdXJzZVRpbWVzLCB2aXNpYmxlS2V5cywga2V5cykge1xuICB2YXIgb3V0cHV0ID0gW107XG4gIGZvciAodmFyIGkgPSAwLCBsID0gdmFsdWUubGVuZ3RoOyBpIDwgbDsgKytpKSB7XG4gICAgaWYgKGhhc093blByb3BlcnR5KHZhbHVlLCBTdHJpbmcoaSkpKSB7XG4gICAgICBvdXRwdXQucHVzaChmb3JtYXRQcm9wZXJ0eShjdHgsIHZhbHVlLCByZWN1cnNlVGltZXMsIHZpc2libGVLZXlzLFxuICAgICAgICAgIFN0cmluZyhpKSwgdHJ1ZSkpO1xuICAgIH0gZWxzZSB7XG4gICAgICBvdXRwdXQucHVzaCgnJyk7XG4gICAgfVxuICB9XG4gIGtleXMuZm9yRWFjaChmdW5jdGlvbihrZXkpIHtcbiAgICBpZiAoIWtleS5tYXRjaCgvXlxcZCskLykpIHtcbiAgICAgIG91dHB1dC5wdXNoKGZvcm1hdFByb3BlcnR5KGN0eCwgdmFsdWUsIHJlY3Vyc2VUaW1lcywgdmlzaWJsZUtleXMsXG4gICAgICAgICAga2V5LCB0cnVlKSk7XG4gICAgfVxuICB9KTtcbiAgcmV0dXJuIG91dHB1dDtcbn1cblxuXG5mdW5jdGlvbiBmb3JtYXRQcm9wZXJ0eShjdHgsIHZhbHVlLCByZWN1cnNlVGltZXMsIHZpc2libGVLZXlzLCBrZXksIGFycmF5KSB7XG4gIHZhciBuYW1lLCBzdHIsIGRlc2M7XG4gIGRlc2MgPSBPYmplY3QuZ2V0T3duUHJvcGVydHlEZXNjcmlwdG9yKHZhbHVlLCBrZXkpIHx8IHsgdmFsdWU6IHZhbHVlW2tleV0gfTtcbiAgaWYgKGRlc2MuZ2V0KSB7XG4gICAgaWYgKGRlc2Muc2V0KSB7XG4gICAgICBzdHIgPSBjdHguc3R5bGl6ZSgnW0dldHRlci9TZXR0ZXJdJywgJ3NwZWNpYWwnKTtcbiAgICB9IGVsc2Uge1xuICAgICAgc3RyID0gY3R4LnN0eWxpemUoJ1tHZXR0ZXJdJywgJ3NwZWNpYWwnKTtcbiAgICB9XG4gIH0gZWxzZSB7XG4gICAgaWYgKGRlc2Muc2V0KSB7XG4gICAgICBzdHIgPSBjdHguc3R5bGl6ZSgnW1NldHRlcl0nLCAnc3BlY2lhbCcpO1xuICAgIH1cbiAgfVxuICBpZiAoIWhhc093blByb3BlcnR5KHZpc2libGVLZXlzLCBrZXkpKSB7XG4gICAgbmFtZSA9ICdbJyArIGtleSArICddJztcbiAgfVxuICBpZiAoIXN0cikge1xuICAgIGlmIChjdHguc2Vlbi5pbmRleE9mKGRlc2MudmFsdWUpIDwgMCkge1xuICAgICAgaWYgKGlzTnVsbChyZWN1cnNlVGltZXMpKSB7XG4gICAgICAgIHN0ciA9IGZvcm1hdFZhbHVlKGN0eCwgZGVzYy52YWx1ZSwgbnVsbCk7XG4gICAgICB9IGVsc2Uge1xuICAgICAgICBzdHIgPSBmb3JtYXRWYWx1ZShjdHgsIGRlc2MudmFsdWUsIHJlY3Vyc2VUaW1lcyAtIDEpO1xuICAgICAgfVxuICAgICAgaWYgKHN0ci5pbmRleE9mKCdcXG4nKSA+IC0xKSB7XG4gICAgICAgIGlmIChhcnJheSkge1xuICAgICAgICAgIHN0ciA9IHN0ci5zcGxpdCgnXFxuJykubWFwKGZ1bmN0aW9uKGxpbmUpIHtcbiAgICAgICAgICAgIHJldHVybiAnICAnICsgbGluZTtcbiAgICAgICAgICB9KS5qb2luKCdcXG4nKS5zdWJzdHIoMik7XG4gICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgc3RyID0gJ1xcbicgKyBzdHIuc3BsaXQoJ1xcbicpLm1hcChmdW5jdGlvbihsaW5lKSB7XG4gICAgICAgICAgICByZXR1cm4gJyAgICcgKyBsaW5lO1xuICAgICAgICAgIH0pLmpvaW4oJ1xcbicpO1xuICAgICAgICB9XG4gICAgICB9XG4gICAgfSBlbHNlIHtcbiAgICAgIHN0ciA9IGN0eC5zdHlsaXplKCdbQ2lyY3VsYXJdJywgJ3NwZWNpYWwnKTtcbiAgICB9XG4gIH1cbiAgaWYgKGlzVW5kZWZpbmVkKG5hbWUpKSB7XG4gICAgaWYgKGFycmF5ICYmIGtleS5tYXRjaCgvXlxcZCskLykpIHtcbiAgICAgIHJldHVybiBzdHI7XG4gICAgfVxuICAgIG5hbWUgPSBKU09OLnN0cmluZ2lmeSgnJyArIGtleSk7XG4gICAgaWYgKG5hbWUubWF0Y2goL15cIihbYS16QS1aX11bYS16QS1aXzAtOV0qKVwiJC8pKSB7XG4gICAgICBuYW1lID0gbmFtZS5zdWJzdHIoMSwgbmFtZS5sZW5ndGggLSAyKTtcbiAgICAgIG5hbWUgPSBjdHguc3R5bGl6ZShuYW1lLCAnbmFtZScpO1xuICAgIH0gZWxzZSB7XG4gICAgICBuYW1lID0gbmFtZS5yZXBsYWNlKC8nL2csIFwiXFxcXCdcIilcbiAgICAgICAgICAgICAgICAgLnJlcGxhY2UoL1xcXFxcIi9nLCAnXCInKVxuICAgICAgICAgICAgICAgICAucmVwbGFjZSgvKF5cInxcIiQpL2csIFwiJ1wiKTtcbiAgICAgIG5hbWUgPSBjdHguc3R5bGl6ZShuYW1lLCAnc3RyaW5nJyk7XG4gICAgfVxuICB9XG5cbiAgcmV0dXJuIG5hbWUgKyAnOiAnICsgc3RyO1xufVxuXG5cbmZ1bmN0aW9uIHJlZHVjZVRvU2luZ2xlU3RyaW5nKG91dHB1dCwgYmFzZSwgYnJhY2VzKSB7XG4gIHZhciBudW1MaW5lc0VzdCA9IDA7XG4gIHZhciBsZW5ndGggPSBvdXRwdXQucmVkdWNlKGZ1bmN0aW9uKHByZXYsIGN1cikge1xuICAgIG51bUxpbmVzRXN0Kys7XG4gICAgaWYgKGN1ci5pbmRleE9mKCdcXG4nKSA+PSAwKSBudW1MaW5lc0VzdCsrO1xuICAgIHJldHVybiBwcmV2ICsgY3VyLnJlcGxhY2UoL1xcdTAwMWJcXFtcXGRcXGQ/bS9nLCAnJykubGVuZ3RoICsgMTtcbiAgfSwgMCk7XG5cbiAgaWYgKGxlbmd0aCA+IDYwKSB7XG4gICAgcmV0dXJuIGJyYWNlc1swXSArXG4gICAgICAgICAgIChiYXNlID09PSAnJyA/ICcnIDogYmFzZSArICdcXG4gJykgK1xuICAgICAgICAgICAnICcgK1xuICAgICAgICAgICBvdXRwdXQuam9pbignLFxcbiAgJykgK1xuICAgICAgICAgICAnICcgK1xuICAgICAgICAgICBicmFjZXNbMV07XG4gIH1cblxuICByZXR1cm4gYnJhY2VzWzBdICsgYmFzZSArICcgJyArIG91dHB1dC5qb2luKCcsICcpICsgJyAnICsgYnJhY2VzWzFdO1xufVxuXG5cbi8vIE5PVEU6IFRoZXNlIHR5cGUgY2hlY2tpbmcgZnVuY3Rpb25zIGludGVudGlvbmFsbHkgZG9uJ3QgdXNlIGBpbnN0YW5jZW9mYFxuLy8gYmVjYXVzZSBpdCBpcyBmcmFnaWxlIGFuZCBjYW4gYmUgZWFzaWx5IGZha2VkIHdpdGggYE9iamVjdC5jcmVhdGUoKWAuXG5mdW5jdGlvbiBpc0FycmF5KGFyKSB7XG4gIHJldHVybiBBcnJheS5pc0FycmF5KGFyKTtcbn1cbmV4cG9ydHMuaXNBcnJheSA9IGlzQXJyYXk7XG5cbmZ1bmN0aW9uIGlzQm9vbGVhbihhcmcpIHtcbiAgcmV0dXJuIHR5cGVvZiBhcmcgPT09ICdib29sZWFuJztcbn1cbmV4cG9ydHMuaXNCb29sZWFuID0gaXNCb29sZWFuO1xuXG5mdW5jdGlvbiBpc051bGwoYXJnKSB7XG4gIHJldHVybiBhcmcgPT09IG51bGw7XG59XG5leHBvcnRzLmlzTnVsbCA9IGlzTnVsbDtcblxuZnVuY3Rpb24gaXNOdWxsT3JVbmRlZmluZWQoYXJnKSB7XG4gIHJldHVybiBhcmcgPT0gbnVsbDtcbn1cbmV4cG9ydHMuaXNOdWxsT3JVbmRlZmluZWQgPSBpc051bGxPclVuZGVmaW5lZDtcblxuZnVuY3Rpb24gaXNOdW1iZXIoYXJnKSB7XG4gIHJldHVybiB0eXBlb2YgYXJnID09PSAnbnVtYmVyJztcbn1cbmV4cG9ydHMuaXNOdW1iZXIgPSBpc051bWJlcjtcblxuZnVuY3Rpb24gaXNTdHJpbmcoYXJnKSB7XG4gIHJldHVybiB0eXBlb2YgYXJnID09PSAnc3RyaW5nJztcbn1cbmV4cG9ydHMuaXNTdHJpbmcgPSBpc1N0cmluZztcblxuZnVuY3Rpb24gaXNTeW1ib2woYXJnKSB7XG4gIHJldHVybiB0eXBlb2YgYXJnID09PSAnc3ltYm9sJztcbn1cbmV4cG9ydHMuaXNTeW1ib2wgPSBpc1N5bWJvbDtcblxuZnVuY3Rpb24gaXNVbmRlZmluZWQoYXJnKSB7XG4gIHJldHVybiBhcmcgPT09IHZvaWQgMDtcbn1cbmV4cG9ydHMuaXNVbmRlZmluZWQgPSBpc1VuZGVmaW5lZDtcblxuZnVuY3Rpb24gaXNSZWdFeHAocmUpIHtcbiAgcmV0dXJuIGlzT2JqZWN0KHJlKSAmJiBvYmplY3RUb1N0cmluZyhyZSkgPT09ICdbb2JqZWN0IFJlZ0V4cF0nO1xufVxuZXhwb3J0cy5pc1JlZ0V4cCA9IGlzUmVnRXhwO1xuXG5mdW5jdGlvbiBpc09iamVjdChhcmcpIHtcbiAgcmV0dXJuIHR5cGVvZiBhcmcgPT09ICdvYmplY3QnICYmIGFyZyAhPT0gbnVsbDtcbn1cbmV4cG9ydHMuaXNPYmplY3QgPSBpc09iamVjdDtcblxuZnVuY3Rpb24gaXNEYXRlKGQpIHtcbiAgcmV0dXJuIGlzT2JqZWN0KGQpICYmIG9iamVjdFRvU3RyaW5nKGQpID09PSAnW29iamVjdCBEYXRlXSc7XG59XG5leHBvcnRzLmlzRGF0ZSA9IGlzRGF0ZTtcblxuZnVuY3Rpb24gaXNFcnJvcihlKSB7XG4gIHJldHVybiBpc09iamVjdChlKSAmJlxuICAgICAgKG9iamVjdFRvU3RyaW5nKGUpID09PSAnW29iamVjdCBFcnJvcl0nIHx8IGUgaW5zdGFuY2VvZiBFcnJvcik7XG59XG5leHBvcnRzLmlzRXJyb3IgPSBpc0Vycm9yO1xuXG5mdW5jdGlvbiBpc0Z1bmN0aW9uKGFyZykge1xuICByZXR1cm4gdHlwZW9mIGFyZyA9PT0gJ2Z1bmN0aW9uJztcbn1cbmV4cG9ydHMuaXNGdW5jdGlvbiA9IGlzRnVuY3Rpb247XG5cbmZ1bmN0aW9uIGlzUHJpbWl0aXZlKGFyZykge1xuICByZXR1cm4gYXJnID09PSBudWxsIHx8XG4gICAgICAgICB0eXBlb2YgYXJnID09PSAnYm9vbGVhbicgfHxcbiAgICAgICAgIHR5cGVvZiBhcmcgPT09ICdudW1iZXInIHx8XG4gICAgICAgICB0eXBlb2YgYXJnID09PSAnc3RyaW5nJyB8fFxuICAgICAgICAgdHlwZW9mIGFyZyA9PT0gJ3N5bWJvbCcgfHwgIC8vIEVTNiBzeW1ib2xcbiAgICAgICAgIHR5cGVvZiBhcmcgPT09ICd1bmRlZmluZWQnO1xufVxuZXhwb3J0cy5pc1ByaW1pdGl2ZSA9IGlzUHJpbWl0aXZlO1xuXG5leHBvcnRzLmlzQnVmZmVyID0gX2RlcmVxXygnLi9zdXBwb3J0L2lzQnVmZmVyJyk7XG5cbmZ1bmN0aW9uIG9iamVjdFRvU3RyaW5nKG8pIHtcbiAgcmV0dXJuIE9iamVjdC5wcm90b3R5cGUudG9TdHJpbmcuY2FsbChvKTtcbn1cblxuXG5mdW5jdGlvbiBwYWQobikge1xuICByZXR1cm4gbiA8IDEwID8gJzAnICsgbi50b1N0cmluZygxMCkgOiBuLnRvU3RyaW5nKDEwKTtcbn1cblxuXG52YXIgbW9udGhzID0gWydKYW4nLCAnRmViJywgJ01hcicsICdBcHInLCAnTWF5JywgJ0p1bicsICdKdWwnLCAnQXVnJywgJ1NlcCcsXG4gICAgICAgICAgICAgICdPY3QnLCAnTm92JywgJ0RlYyddO1xuXG4vLyAyNiBGZWIgMTY6MTk6MzRcbmZ1bmN0aW9uIHRpbWVzdGFtcCgpIHtcbiAgdmFyIGQgPSBuZXcgRGF0ZSgpO1xuICB2YXIgdGltZSA9IFtwYWQoZC5nZXRIb3VycygpKSxcbiAgICAgICAgICAgICAgcGFkKGQuZ2V0TWludXRlcygpKSxcbiAgICAgICAgICAgICAgcGFkKGQuZ2V0U2Vjb25kcygpKV0uam9pbignOicpO1xuICByZXR1cm4gW2QuZ2V0RGF0ZSgpLCBtb250aHNbZC5nZXRNb250aCgpXSwgdGltZV0uam9pbignICcpO1xufVxuXG5cbi8vIGxvZyBpcyBqdXN0IGEgdGhpbiB3cmFwcGVyIHRvIGNvbnNvbGUubG9nIHRoYXQgcHJlcGVuZHMgYSB0aW1lc3RhbXBcbmV4cG9ydHMubG9nID0gZnVuY3Rpb24oKSB7XG4gIGNvbnNvbGUubG9nKCclcyAtICVzJywgdGltZXN0YW1wKCksIGV4cG9ydHMuZm9ybWF0LmFwcGx5KGV4cG9ydHMsIGFyZ3VtZW50cykpO1xufTtcblxuXG4vKipcbiAqIEluaGVyaXQgdGhlIHByb3RvdHlwZSBtZXRob2RzIGZyb20gb25lIGNvbnN0cnVjdG9yIGludG8gYW5vdGhlci5cbiAqXG4gKiBUaGUgRnVuY3Rpb24ucHJvdG90eXBlLmluaGVyaXRzIGZyb20gbGFuZy5qcyByZXdyaXR0ZW4gYXMgYSBzdGFuZGFsb25lXG4gKiBmdW5jdGlvbiAobm90IG9uIEZ1bmN0aW9uLnByb3RvdHlwZSkuIE5PVEU6IElmIHRoaXMgZmlsZSBpcyB0byBiZSBsb2FkZWRcbiAqIGR1cmluZyBib290c3RyYXBwaW5nIHRoaXMgZnVuY3Rpb24gbmVlZHMgdG8gYmUgcmV3cml0dGVuIHVzaW5nIHNvbWUgbmF0aXZlXG4gKiBmdW5jdGlvbnMgYXMgcHJvdG90eXBlIHNldHVwIHVzaW5nIG5vcm1hbCBKYXZhU2NyaXB0IGRvZXMgbm90IHdvcmsgYXNcbiAqIGV4cGVjdGVkIGR1cmluZyBib290c3RyYXBwaW5nIChzZWUgbWlycm9yLmpzIGluIHIxMTQ5MDMpLlxuICpcbiAqIEBwYXJhbSB7ZnVuY3Rpb259IGN0b3IgQ29uc3RydWN0b3IgZnVuY3Rpb24gd2hpY2ggbmVlZHMgdG8gaW5oZXJpdCB0aGVcbiAqICAgICBwcm90b3R5cGUuXG4gKiBAcGFyYW0ge2Z1bmN0aW9ufSBzdXBlckN0b3IgQ29uc3RydWN0b3IgZnVuY3Rpb24gdG8gaW5oZXJpdCBwcm90b3R5cGUgZnJvbS5cbiAqL1xuZXhwb3J0cy5pbmhlcml0cyA9IF9kZXJlcV8oJ2luaGVyaXRzJyk7XG5cbmV4cG9ydHMuX2V4dGVuZCA9IGZ1bmN0aW9uKG9yaWdpbiwgYWRkKSB7XG4gIC8vIERvbid0IGRvIGFueXRoaW5nIGlmIGFkZCBpc24ndCBhbiBvYmplY3RcbiAgaWYgKCFhZGQgfHwgIWlzT2JqZWN0KGFkZCkpIHJldHVybiBvcmlnaW47XG5cbiAgdmFyIGtleXMgPSBPYmplY3Qua2V5cyhhZGQpO1xuICB2YXIgaSA9IGtleXMubGVuZ3RoO1xuICB3aGlsZSAoaS0tKSB7XG4gICAgb3JpZ2luW2tleXNbaV1dID0gYWRkW2tleXNbaV1dO1xuICB9XG4gIHJldHVybiBvcmlnaW47XG59O1xuXG5mdW5jdGlvbiBoYXNPd25Qcm9wZXJ0eShvYmosIHByb3ApIHtcbiAgcmV0dXJuIE9iamVjdC5wcm90b3R5cGUuaGFzT3duUHJvcGVydHkuY2FsbChvYmosIHByb3ApO1xufVxuXG59KS5jYWxsKHRoaXMsX2RlcmVxXygnX3Byb2Nlc3MnKSx0eXBlb2YgZ2xvYmFsICE9PSBcInVuZGVmaW5lZFwiID8gZ2xvYmFsIDogdHlwZW9mIHNlbGYgIT09IFwidW5kZWZpbmVkXCIgPyBzZWxmIDogdHlwZW9mIHdpbmRvdyAhPT0gXCJ1bmRlZmluZWRcIiA/IHdpbmRvdyA6IHt9KVxufSx7XCIuL3N1cHBvcnQvaXNCdWZmZXJcIjo0LFwiX3Byb2Nlc3NcIjozLFwiaW5oZXJpdHNcIjoyfV0sNjpbZnVuY3Rpb24oX2RlcmVxXyxtb2R1bGUsZXhwb3J0cyl7XG4vLyBBIHJlY3Vyc2l2ZSBkZXNjZW50IHBhcnNlciBvcGVyYXRlcyBieSBkZWZpbmluZyBmdW5jdGlvbnMgZm9yIGFsbFxuLy8gc3ludGFjdGljIGVsZW1lbnRzLCBhbmQgcmVjdXJzaXZlbHkgY2FsbGluZyB0aG9zZSwgZWFjaCBmdW5jdGlvblxuLy8gYWR2YW5jaW5nIHRoZSBpbnB1dCBzdHJlYW0gYW5kIHJldHVybmluZyBhbiBBU1Qgbm9kZS4gUHJlY2VkZW5jZVxuLy8gb2YgY29uc3RydWN0cyAoZm9yIGV4YW1wbGUsIHRoZSBmYWN0IHRoYXQgYCF4WzFdYCBtZWFucyBgISh4WzFdKWBcbi8vIGluc3RlYWQgb2YgYCgheClbMV1gIGlzIGhhbmRsZWQgYnkgdGhlIGZhY3QgdGhhdCB0aGUgcGFyc2VyXG4vLyBmdW5jdGlvbiB0aGF0IHBhcnNlcyB1bmFyeSBwcmVmaXggb3BlcmF0b3JzIGlzIGNhbGxlZCBmaXJzdCwgYW5kXG4vLyBpbiB0dXJuIGNhbGxzIHRoZSBmdW5jdGlvbiB0aGF0IHBhcnNlcyBgW11gIHN1YnNjcmlwdHMg4oCUIHRoYXRcbi8vIHdheSwgaXQnbGwgcmVjZWl2ZSB0aGUgbm9kZSBmb3IgYHhbMV1gIGFscmVhZHkgcGFyc2VkLCBhbmQgd3JhcHNcbi8vICp0aGF0KiBpbiB0aGUgdW5hcnkgb3BlcmF0b3Igbm9kZS5cbi8vXG4vLyBBY29ybiB1c2VzIGFuIFtvcGVyYXRvciBwcmVjZWRlbmNlIHBhcnNlcl1bb3BwXSB0byBoYW5kbGUgYmluYXJ5XG4vLyBvcGVyYXRvciBwcmVjZWRlbmNlLCBiZWNhdXNlIGl0IGlzIG11Y2ggbW9yZSBjb21wYWN0IHRoYW4gdXNpbmdcbi8vIHRoZSB0ZWNobmlxdWUgb3V0bGluZWQgYWJvdmUsIHdoaWNoIHVzZXMgZGlmZmVyZW50LCBuZXN0aW5nXG4vLyBmdW5jdGlvbnMgdG8gc3BlY2lmeSBwcmVjZWRlbmNlLCBmb3IgYWxsIG9mIHRoZSB0ZW4gYmluYXJ5XG4vLyBwcmVjZWRlbmNlIGxldmVscyB0aGF0IEphdmFTY3JpcHQgZGVmaW5lcy5cbi8vXG4vLyBbb3BwXTogaHR0cDovL2VuLndpa2lwZWRpYS5vcmcvd2lraS9PcGVyYXRvci1wcmVjZWRlbmNlX3BhcnNlclxuXG5cInVzZSBzdHJpY3RcIjtcblxudmFyIHR0ID0gX2RlcmVxXyhcIi4vdG9rZW50eXBlXCIpLnR5cGVzO1xuXG52YXIgUGFyc2VyID0gX2RlcmVxXyhcIi4vc3RhdGVcIikuUGFyc2VyO1xuXG52YXIgcmVzZXJ2ZWRXb3JkcyA9IF9kZXJlcV8oXCIuL2lkZW50aWZpZXJcIikucmVzZXJ2ZWRXb3JkcztcblxudmFyIGhhcyA9IF9kZXJlcV8oXCIuL3V0aWxcIikuaGFzO1xuXG52YXIgcHAgPSBQYXJzZXIucHJvdG90eXBlO1xuXG4vLyBDaGVjayBpZiBwcm9wZXJ0eSBuYW1lIGNsYXNoZXMgd2l0aCBhbHJlYWR5IGFkZGVkLlxuLy8gT2JqZWN0L2NsYXNzIGdldHRlcnMgYW5kIHNldHRlcnMgYXJlIG5vdCBhbGxvd2VkIHRvIGNsYXNoIOKAlFxuLy8gZWl0aGVyIHdpdGggZWFjaCBvdGhlciBvciB3aXRoIGFuIGluaXQgcHJvcGVydHkg4oCUIGFuZCBpblxuLy8gc3RyaWN0IG1vZGUsIGluaXQgcHJvcGVydGllcyBhcmUgYWxzbyBub3QgYWxsb3dlZCB0byBiZSByZXBlYXRlZC5cblxucHAuY2hlY2tQcm9wQ2xhc2ggPSBmdW5jdGlvbiAocHJvcCwgcHJvcEhhc2gpIHtcbiAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KSByZXR1cm47XG4gIHZhciBrZXkgPSBwcm9wLmtleSxcbiAgICAgIG5hbWUgPSB1bmRlZmluZWQ7XG4gIHN3aXRjaCAoa2V5LnR5cGUpIHtcbiAgICBjYXNlIFwiSWRlbnRpZmllclwiOlxuICAgICAgbmFtZSA9IGtleS5uYW1lO2JyZWFrO1xuICAgIGNhc2UgXCJMaXRlcmFsXCI6XG4gICAgICBuYW1lID0gU3RyaW5nKGtleS52YWx1ZSk7YnJlYWs7XG4gICAgZGVmYXVsdDpcbiAgICAgIHJldHVybjtcbiAgfVxuICB2YXIga2luZCA9IHByb3Aua2luZCB8fCBcImluaXRcIixcbiAgICAgIG90aGVyID0gdW5kZWZpbmVkO1xuICBpZiAoaGFzKHByb3BIYXNoLCBuYW1lKSkge1xuICAgIG90aGVyID0gcHJvcEhhc2hbbmFtZV07XG4gICAgdmFyIGlzR2V0U2V0ID0ga2luZCAhPT0gXCJpbml0XCI7XG4gICAgaWYgKCh0aGlzLnN0cmljdCB8fCBpc0dldFNldCkgJiYgb3RoZXJba2luZF0gfHwgIShpc0dldFNldCBeIG90aGVyLmluaXQpKSB0aGlzLnJhaXNlKGtleS5zdGFydCwgXCJSZWRlZmluaXRpb24gb2YgcHJvcGVydHlcIik7XG4gIH0gZWxzZSB7XG4gICAgb3RoZXIgPSBwcm9wSGFzaFtuYW1lXSA9IHtcbiAgICAgIGluaXQ6IGZhbHNlLFxuICAgICAgZ2V0OiBmYWxzZSxcbiAgICAgIHNldDogZmFsc2VcbiAgICB9O1xuICB9XG4gIG90aGVyW2tpbmRdID0gdHJ1ZTtcbn07XG5cbi8vICMjIyBFeHByZXNzaW9uIHBhcnNpbmdcblxuLy8gVGhlc2UgbmVzdCwgZnJvbSB0aGUgbW9zdCBnZW5lcmFsIGV4cHJlc3Npb24gdHlwZSBhdCB0aGUgdG9wIHRvXG4vLyAnYXRvbWljJywgbm9uZGl2aXNpYmxlIGV4cHJlc3Npb24gdHlwZXMgYXQgdGhlIGJvdHRvbS4gTW9zdCBvZlxuLy8gdGhlIGZ1bmN0aW9ucyB3aWxsIHNpbXBseSBsZXQgdGhlIGZ1bmN0aW9uKHMpIGJlbG93IHRoZW0gcGFyc2UsXG4vLyBhbmQsICppZiogdGhlIHN5bnRhY3RpYyBjb25zdHJ1Y3QgdGhleSBoYW5kbGUgaXMgcHJlc2VudCwgd3JhcFxuLy8gdGhlIEFTVCBub2RlIHRoYXQgdGhlIGlubmVyIHBhcnNlciBnYXZlIHRoZW0gaW4gYW5vdGhlciBub2RlLlxuXG4vLyBQYXJzZSBhIGZ1bGwgZXhwcmVzc2lvbi4gVGhlIG9wdGlvbmFsIGFyZ3VtZW50cyBhcmUgdXNlZCB0b1xuLy8gZm9yYmlkIHRoZSBgaW5gIG9wZXJhdG9yIChpbiBmb3IgbG9vcHMgaW5pdGFsaXphdGlvbiBleHByZXNzaW9ucylcbi8vIGFuZCBwcm92aWRlIHJlZmVyZW5jZSBmb3Igc3RvcmluZyAnPScgb3BlcmF0b3IgaW5zaWRlIHNob3J0aGFuZFxuLy8gcHJvcGVydHkgYXNzaWdubWVudCBpbiBjb250ZXh0cyB3aGVyZSBib3RoIG9iamVjdCBleHByZXNzaW9uXG4vLyBhbmQgb2JqZWN0IHBhdHRlcm4gbWlnaHQgYXBwZWFyIChzbyBpdCdzIHBvc3NpYmxlIHRvIHJhaXNlXG4vLyBkZWxheWVkIHN5bnRheCBlcnJvciBhdCBjb3JyZWN0IHBvc2l0aW9uKS5cblxucHAucGFyc2VFeHByZXNzaW9uID0gZnVuY3Rpb24gKG5vSW4sIHJlZlNob3J0aGFuZERlZmF1bHRQb3MpIHtcbiAgdmFyIHN0YXJ0UG9zID0gdGhpcy5zdGFydCxcbiAgICAgIHN0YXJ0TG9jID0gdGhpcy5zdGFydExvYztcbiAgdmFyIGV4cHIgPSB0aGlzLnBhcnNlTWF5YmVBc3NpZ24obm9JbiwgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcyk7XG4gIGlmICh0aGlzLnR5cGUgPT09IHR0LmNvbW1hKSB7XG4gICAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0UG9zLCBzdGFydExvYyk7XG4gICAgbm9kZS5leHByZXNzaW9ucyA9IFtleHByXTtcbiAgICB3aGlsZSAodGhpcy5lYXQodHQuY29tbWEpKSBub2RlLmV4cHJlc3Npb25zLnB1c2godGhpcy5wYXJzZU1heWJlQXNzaWduKG5vSW4sIHJlZlNob3J0aGFuZERlZmF1bHRQb3MpKTtcbiAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiU2VxdWVuY2VFeHByZXNzaW9uXCIpO1xuICB9XG4gIHJldHVybiBleHByO1xufTtcblxuLy8gUGFyc2UgYW4gYXNzaWdubWVudCBleHByZXNzaW9uLiBUaGlzIGluY2x1ZGVzIGFwcGxpY2F0aW9ucyBvZlxuLy8gb3BlcmF0b3JzIGxpa2UgYCs9YC5cblxucHAucGFyc2VNYXliZUFzc2lnbiA9IGZ1bmN0aW9uIChub0luLCByZWZTaG9ydGhhbmREZWZhdWx0UG9zLCBhZnRlckxlZnRQYXJzZSkge1xuICBpZiAodGhpcy50eXBlID09IHR0Ll95aWVsZCAmJiB0aGlzLmluR2VuZXJhdG9yKSByZXR1cm4gdGhpcy5wYXJzZVlpZWxkKCk7XG5cbiAgdmFyIGZhaWxPblNob3J0aGFuZEFzc2lnbiA9IHVuZGVmaW5lZDtcbiAgaWYgKCFyZWZTaG9ydGhhbmREZWZhdWx0UG9zKSB7XG4gICAgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcyA9IHsgc3RhcnQ6IDAgfTtcbiAgICBmYWlsT25TaG9ydGhhbmRBc3NpZ24gPSB0cnVlO1xuICB9IGVsc2Uge1xuICAgIGZhaWxPblNob3J0aGFuZEFzc2lnbiA9IGZhbHNlO1xuICB9XG4gIHZhciBzdGFydFBvcyA9IHRoaXMuc3RhcnQsXG4gICAgICBzdGFydExvYyA9IHRoaXMuc3RhcnRMb2M7XG4gIGlmICh0aGlzLnR5cGUgPT0gdHQucGFyZW5MIHx8IHRoaXMudHlwZSA9PSB0dC5uYW1lKSB0aGlzLnBvdGVudGlhbEFycm93QXQgPSB0aGlzLnN0YXJ0O1xuICB2YXIgbGVmdCA9IHRoaXMucGFyc2VNYXliZUNvbmRpdGlvbmFsKG5vSW4sIHJlZlNob3J0aGFuZERlZmF1bHRQb3MpO1xuICBpZiAoYWZ0ZXJMZWZ0UGFyc2UpIGxlZnQgPSBhZnRlckxlZnRQYXJzZS5jYWxsKHRoaXMsIGxlZnQsIHN0YXJ0UG9zLCBzdGFydExvYyk7XG4gIGlmICh0aGlzLnR5cGUuaXNBc3NpZ24pIHtcbiAgICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlQXQoc3RhcnRQb3MsIHN0YXJ0TG9jKTtcbiAgICBub2RlLm9wZXJhdG9yID0gdGhpcy52YWx1ZTtcbiAgICBub2RlLmxlZnQgPSB0aGlzLnR5cGUgPT09IHR0LmVxID8gdGhpcy50b0Fzc2lnbmFibGUobGVmdCkgOiBsZWZ0O1xuICAgIHJlZlNob3J0aGFuZERlZmF1bHRQb3Muc3RhcnQgPSAwOyAvLyByZXNldCBiZWNhdXNlIHNob3J0aGFuZCBkZWZhdWx0IHdhcyB1c2VkIGNvcnJlY3RseVxuICAgIHRoaXMuY2hlY2tMVmFsKGxlZnQpO1xuICAgIHRoaXMubmV4dCgpO1xuICAgIG5vZGUucmlnaHQgPSB0aGlzLnBhcnNlTWF5YmVBc3NpZ24obm9Jbik7XG4gICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkFzc2lnbm1lbnRFeHByZXNzaW9uXCIpO1xuICB9IGVsc2UgaWYgKGZhaWxPblNob3J0aGFuZEFzc2lnbiAmJiByZWZTaG9ydGhhbmREZWZhdWx0UG9zLnN0YXJ0KSB7XG4gICAgdGhpcy51bmV4cGVjdGVkKHJlZlNob3J0aGFuZERlZmF1bHRQb3Muc3RhcnQpO1xuICB9XG4gIHJldHVybiBsZWZ0O1xufTtcblxuLy8gUGFyc2UgYSB0ZXJuYXJ5IGNvbmRpdGlvbmFsIChgPzpgKSBvcGVyYXRvci5cblxucHAucGFyc2VNYXliZUNvbmRpdGlvbmFsID0gZnVuY3Rpb24gKG5vSW4sIHJlZlNob3J0aGFuZERlZmF1bHRQb3MpIHtcbiAgdmFyIHN0YXJ0UG9zID0gdGhpcy5zdGFydCxcbiAgICAgIHN0YXJ0TG9jID0gdGhpcy5zdGFydExvYztcbiAgdmFyIGV4cHIgPSB0aGlzLnBhcnNlRXhwck9wcyhub0luLCByZWZTaG9ydGhhbmREZWZhdWx0UG9zKTtcbiAgaWYgKHJlZlNob3J0aGFuZERlZmF1bHRQb3MgJiYgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcy5zdGFydCkgcmV0dXJuIGV4cHI7XG4gIGlmICh0aGlzLmVhdCh0dC5xdWVzdGlvbikpIHtcbiAgICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlQXQoc3RhcnRQb3MsIHN0YXJ0TG9jKTtcbiAgICBub2RlLnRlc3QgPSBleHByO1xuICAgIG5vZGUuY29uc2VxdWVudCA9IHRoaXMucGFyc2VNYXliZUFzc2lnbigpO1xuICAgIHRoaXMuZXhwZWN0KHR0LmNvbG9uKTtcbiAgICBub2RlLmFsdGVybmF0ZSA9IHRoaXMucGFyc2VNYXliZUFzc2lnbihub0luKTtcbiAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiQ29uZGl0aW9uYWxFeHByZXNzaW9uXCIpO1xuICB9XG4gIHJldHVybiBleHByO1xufTtcblxuLy8gU3RhcnQgdGhlIHByZWNlZGVuY2UgcGFyc2VyLlxuXG5wcC5wYXJzZUV4cHJPcHMgPSBmdW5jdGlvbiAobm9JbiwgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcykge1xuICB2YXIgc3RhcnRQb3MgPSB0aGlzLnN0YXJ0LFxuICAgICAgc3RhcnRMb2MgPSB0aGlzLnN0YXJ0TG9jO1xuICB2YXIgZXhwciA9IHRoaXMucGFyc2VNYXliZVVuYXJ5KHJlZlNob3J0aGFuZERlZmF1bHRQb3MpO1xuICBpZiAocmVmU2hvcnRoYW5kRGVmYXVsdFBvcyAmJiByZWZTaG9ydGhhbmREZWZhdWx0UG9zLnN0YXJ0KSByZXR1cm4gZXhwcjtcbiAgcmV0dXJuIHRoaXMucGFyc2VFeHByT3AoZXhwciwgc3RhcnRQb3MsIHN0YXJ0TG9jLCAtMSwgbm9Jbik7XG59O1xuXG4vLyBQYXJzZSBiaW5hcnkgb3BlcmF0b3JzIHdpdGggdGhlIG9wZXJhdG9yIHByZWNlZGVuY2UgcGFyc2luZ1xuLy8gYWxnb3JpdGhtLiBgbGVmdGAgaXMgdGhlIGxlZnQtaGFuZCBzaWRlIG9mIHRoZSBvcGVyYXRvci5cbi8vIGBtaW5QcmVjYCBwcm92aWRlcyBjb250ZXh0IHRoYXQgYWxsb3dzIHRoZSBmdW5jdGlvbiB0byBzdG9wIGFuZFxuLy8gZGVmZXIgZnVydGhlciBwYXJzZXIgdG8gb25lIG9mIGl0cyBjYWxsZXJzIHdoZW4gaXQgZW5jb3VudGVycyBhblxuLy8gb3BlcmF0b3IgdGhhdCBoYXMgYSBsb3dlciBwcmVjZWRlbmNlIHRoYW4gdGhlIHNldCBpdCBpcyBwYXJzaW5nLlxuXG5wcC5wYXJzZUV4cHJPcCA9IGZ1bmN0aW9uIChsZWZ0LCBsZWZ0U3RhcnRQb3MsIGxlZnRTdGFydExvYywgbWluUHJlYywgbm9Jbikge1xuICB2YXIgcHJlYyA9IHRoaXMudHlwZS5iaW5vcDtcbiAgaWYgKEFycmF5LmlzQXJyYXkobGVmdFN0YXJ0UG9zKSkge1xuICAgIGlmICh0aGlzLm9wdGlvbnMubG9jYXRpb25zICYmIG5vSW4gPT09IHVuZGVmaW5lZCkge1xuICAgICAgLy8gc2hpZnQgYXJndW1lbnRzIHRvIGxlZnQgYnkgb25lXG4gICAgICBub0luID0gbWluUHJlYztcbiAgICAgIG1pblByZWMgPSBsZWZ0U3RhcnRMb2M7XG4gICAgICAvLyBmbGF0dGVuIGxlZnRTdGFydFBvc1xuICAgICAgbGVmdFN0YXJ0TG9jID0gbGVmdFN0YXJ0UG9zWzFdO1xuICAgICAgbGVmdFN0YXJ0UG9zID0gbGVmdFN0YXJ0UG9zWzBdO1xuICAgIH1cbiAgfVxuICBpZiAocHJlYyAhPSBudWxsICYmICghbm9JbiB8fCB0aGlzLnR5cGUgIT09IHR0Ll9pbikpIHtcbiAgICBpZiAocHJlYyA+IG1pblByZWMpIHtcbiAgICAgIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGVBdChsZWZ0U3RhcnRQb3MsIGxlZnRTdGFydExvYyk7XG4gICAgICBub2RlLmxlZnQgPSBsZWZ0O1xuICAgICAgbm9kZS5vcGVyYXRvciA9IHRoaXMudmFsdWU7XG4gICAgICB2YXIgb3AgPSB0aGlzLnR5cGU7XG4gICAgICB0aGlzLm5leHQoKTtcbiAgICAgIHZhciBzdGFydFBvcyA9IHRoaXMuc3RhcnQsXG4gICAgICAgICAgc3RhcnRMb2MgPSB0aGlzLnN0YXJ0TG9jO1xuICAgICAgbm9kZS5yaWdodCA9IHRoaXMucGFyc2VFeHByT3AodGhpcy5wYXJzZU1heWJlVW5hcnkoKSwgc3RhcnRQb3MsIHN0YXJ0TG9jLCBwcmVjLCBub0luKTtcbiAgICAgIHRoaXMuZmluaXNoTm9kZShub2RlLCBvcCA9PT0gdHQubG9naWNhbE9SIHx8IG9wID09PSB0dC5sb2dpY2FsQU5EID8gXCJMb2dpY2FsRXhwcmVzc2lvblwiIDogXCJCaW5hcnlFeHByZXNzaW9uXCIpO1xuICAgICAgcmV0dXJuIHRoaXMucGFyc2VFeHByT3Aobm9kZSwgbGVmdFN0YXJ0UG9zLCBsZWZ0U3RhcnRMb2MsIG1pblByZWMsIG5vSW4pO1xuICAgIH1cbiAgfVxuICByZXR1cm4gbGVmdDtcbn07XG5cbi8vIFBhcnNlIHVuYXJ5IG9wZXJhdG9ycywgYm90aCBwcmVmaXggYW5kIHBvc3RmaXguXG5cbnBwLnBhcnNlTWF5YmVVbmFyeSA9IGZ1bmN0aW9uIChyZWZTaG9ydGhhbmREZWZhdWx0UG9zKSB7XG4gIGlmICh0aGlzLnR5cGUucHJlZml4KSB7XG4gICAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpLFxuICAgICAgICB1cGRhdGUgPSB0aGlzLnR5cGUgPT09IHR0LmluY0RlYztcbiAgICBub2RlLm9wZXJhdG9yID0gdGhpcy52YWx1ZTtcbiAgICBub2RlLnByZWZpeCA9IHRydWU7XG4gICAgdGhpcy5uZXh0KCk7XG4gICAgbm9kZS5hcmd1bWVudCA9IHRoaXMucGFyc2VNYXliZVVuYXJ5KCk7XG4gICAgaWYgKHJlZlNob3J0aGFuZERlZmF1bHRQb3MgJiYgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcy5zdGFydCkgdGhpcy51bmV4cGVjdGVkKHJlZlNob3J0aGFuZERlZmF1bHRQb3Muc3RhcnQpO1xuICAgIGlmICh1cGRhdGUpIHRoaXMuY2hlY2tMVmFsKG5vZGUuYXJndW1lbnQpO2Vsc2UgaWYgKHRoaXMuc3RyaWN0ICYmIG5vZGUub3BlcmF0b3IgPT09IFwiZGVsZXRlXCIgJiYgbm9kZS5hcmd1bWVudC50eXBlID09PSBcIklkZW50aWZpZXJcIikgdGhpcy5yYWlzZShub2RlLnN0YXJ0LCBcIkRlbGV0aW5nIGxvY2FsIHZhcmlhYmxlIGluIHN0cmljdCBtb2RlXCIpO1xuICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgdXBkYXRlID8gXCJVcGRhdGVFeHByZXNzaW9uXCIgOiBcIlVuYXJ5RXhwcmVzc2lvblwiKTtcbiAgfVxuICB2YXIgc3RhcnRQb3MgPSB0aGlzLnN0YXJ0LFxuICAgICAgc3RhcnRMb2MgPSB0aGlzLnN0YXJ0TG9jO1xuICB2YXIgZXhwciA9IHRoaXMucGFyc2VFeHByU3Vic2NyaXB0cyhyZWZTaG9ydGhhbmREZWZhdWx0UG9zKTtcbiAgaWYgKHJlZlNob3J0aGFuZERlZmF1bHRQb3MgJiYgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcy5zdGFydCkgcmV0dXJuIGV4cHI7XG4gIHdoaWxlICh0aGlzLnR5cGUucG9zdGZpeCAmJiAhdGhpcy5jYW5JbnNlcnRTZW1pY29sb24oKSkge1xuICAgIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGVBdChzdGFydFBvcywgc3RhcnRMb2MpO1xuICAgIG5vZGUub3BlcmF0b3IgPSB0aGlzLnZhbHVlO1xuICAgIG5vZGUucHJlZml4ID0gZmFsc2U7XG4gICAgbm9kZS5hcmd1bWVudCA9IGV4cHI7XG4gICAgdGhpcy5jaGVja0xWYWwoZXhwcik7XG4gICAgdGhpcy5uZXh0KCk7XG4gICAgZXhwciA9IHRoaXMuZmluaXNoTm9kZShub2RlLCBcIlVwZGF0ZUV4cHJlc3Npb25cIik7XG4gIH1cbiAgcmV0dXJuIGV4cHI7XG59O1xuXG4vLyBQYXJzZSBjYWxsLCBkb3QsIGFuZCBgW11gLXN1YnNjcmlwdCBleHByZXNzaW9ucy5cblxucHAucGFyc2VFeHByU3Vic2NyaXB0cyA9IGZ1bmN0aW9uIChyZWZTaG9ydGhhbmREZWZhdWx0UG9zKSB7XG4gIHZhciBzdGFydFBvcyA9IHRoaXMuc3RhcnQsXG4gICAgICBzdGFydExvYyA9IHRoaXMuc3RhcnRMb2M7XG4gIHZhciBleHByID0gdGhpcy5wYXJzZUV4cHJBdG9tKHJlZlNob3J0aGFuZERlZmF1bHRQb3MpO1xuICBpZiAocmVmU2hvcnRoYW5kRGVmYXVsdFBvcyAmJiByZWZTaG9ydGhhbmREZWZhdWx0UG9zLnN0YXJ0KSByZXR1cm4gZXhwcjtcbiAgcmV0dXJuIHRoaXMucGFyc2VTdWJzY3JpcHRzKGV4cHIsIHN0YXJ0UG9zLCBzdGFydExvYyk7XG59O1xuXG5wcC5wYXJzZVN1YnNjcmlwdHMgPSBmdW5jdGlvbiAoYmFzZSwgc3RhcnRQb3MsIHN0YXJ0TG9jLCBub0NhbGxzKSB7XG4gIGlmIChBcnJheS5pc0FycmF5KHN0YXJ0UG9zKSkge1xuICAgIGlmICh0aGlzLm9wdGlvbnMubG9jYXRpb25zICYmIG5vQ2FsbHMgPT09IHVuZGVmaW5lZCkge1xuICAgICAgLy8gc2hpZnQgYXJndW1lbnRzIHRvIGxlZnQgYnkgb25lXG4gICAgICBub0NhbGxzID0gc3RhcnRMb2M7XG4gICAgICAvLyBmbGF0dGVuIHN0YXJ0UG9zXG4gICAgICBzdGFydExvYyA9IHN0YXJ0UG9zWzFdO1xuICAgICAgc3RhcnRQb3MgPSBzdGFydFBvc1swXTtcbiAgICB9XG4gIH1cbiAgZm9yICg7Oykge1xuICAgIGlmICh0aGlzLmVhdCh0dC5kb3QpKSB7XG4gICAgICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlQXQoc3RhcnRQb3MsIHN0YXJ0TG9jKTtcbiAgICAgIG5vZGUub2JqZWN0ID0gYmFzZTtcbiAgICAgIG5vZGUucHJvcGVydHkgPSB0aGlzLnBhcnNlSWRlbnQodHJ1ZSk7XG4gICAgICBub2RlLmNvbXB1dGVkID0gZmFsc2U7XG4gICAgICBiYXNlID0gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiTWVtYmVyRXhwcmVzc2lvblwiKTtcbiAgICB9IGVsc2UgaWYgKHRoaXMuZWF0KHR0LmJyYWNrZXRMKSkge1xuICAgICAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0UG9zLCBzdGFydExvYyk7XG4gICAgICBub2RlLm9iamVjdCA9IGJhc2U7XG4gICAgICBub2RlLnByb3BlcnR5ID0gdGhpcy5wYXJzZUV4cHJlc3Npb24oKTtcbiAgICAgIG5vZGUuY29tcHV0ZWQgPSB0cnVlO1xuICAgICAgdGhpcy5leHBlY3QodHQuYnJhY2tldFIpO1xuICAgICAgYmFzZSA9IHRoaXMuZmluaXNoTm9kZShub2RlLCBcIk1lbWJlckV4cHJlc3Npb25cIik7XG4gICAgfSBlbHNlIGlmICghbm9DYWxscyAmJiB0aGlzLmVhdCh0dC5wYXJlbkwpKSB7XG4gICAgICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlQXQoc3RhcnRQb3MsIHN0YXJ0TG9jKTtcbiAgICAgIG5vZGUuY2FsbGVlID0gYmFzZTtcbiAgICAgIG5vZGUuYXJndW1lbnRzID0gdGhpcy5wYXJzZUV4cHJMaXN0KHR0LnBhcmVuUiwgZmFsc2UpO1xuICAgICAgYmFzZSA9IHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkNhbGxFeHByZXNzaW9uXCIpO1xuICAgIH0gZWxzZSBpZiAodGhpcy50eXBlID09PSB0dC5iYWNrUXVvdGUpIHtcbiAgICAgIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGVBdChzdGFydFBvcywgc3RhcnRMb2MpO1xuICAgICAgbm9kZS50YWcgPSBiYXNlO1xuICAgICAgbm9kZS5xdWFzaSA9IHRoaXMucGFyc2VUZW1wbGF0ZSgpO1xuICAgICAgYmFzZSA9IHRoaXMuZmluaXNoTm9kZShub2RlLCBcIlRhZ2dlZFRlbXBsYXRlRXhwcmVzc2lvblwiKTtcbiAgICB9IGVsc2Uge1xuICAgICAgcmV0dXJuIGJhc2U7XG4gICAgfVxuICB9XG59O1xuXG4vLyBQYXJzZSBhbiBhdG9taWMgZXhwcmVzc2lvbiDigJQgZWl0aGVyIGEgc2luZ2xlIHRva2VuIHRoYXQgaXMgYW5cbi8vIGV4cHJlc3Npb24sIGFuIGV4cHJlc3Npb24gc3RhcnRlZCBieSBhIGtleXdvcmQgbGlrZSBgZnVuY3Rpb25gIG9yXG4vLyBgbmV3YCwgb3IgYW4gZXhwcmVzc2lvbiB3cmFwcGVkIGluIHB1bmN0dWF0aW9uIGxpa2UgYCgpYCwgYFtdYCxcbi8vIG9yIGB7fWAuXG5cbnBwLnBhcnNlRXhwckF0b20gPSBmdW5jdGlvbiAocmVmU2hvcnRoYW5kRGVmYXVsdFBvcykge1xuICB2YXIgbm9kZSA9IHVuZGVmaW5lZCxcbiAgICAgIGNhbkJlQXJyb3cgPSB0aGlzLnBvdGVudGlhbEFycm93QXQgPT0gdGhpcy5zdGFydDtcbiAgc3dpdGNoICh0aGlzLnR5cGUpIHtcbiAgICBjYXNlIHR0Ll90aGlzOlxuICAgIGNhc2UgdHQuX3N1cGVyOlxuICAgICAgdmFyIHR5cGUgPSB0aGlzLnR5cGUgPT09IHR0Ll90aGlzID8gXCJUaGlzRXhwcmVzc2lvblwiIDogXCJTdXBlclwiO1xuICAgICAgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gICAgICB0aGlzLm5leHQoKTtcbiAgICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgdHlwZSk7XG5cbiAgICBjYXNlIHR0Ll95aWVsZDpcbiAgICAgIGlmICh0aGlzLmluR2VuZXJhdG9yKSB0aGlzLnVuZXhwZWN0ZWQoKTtcblxuICAgIGNhc2UgdHQubmFtZTpcbiAgICAgIHZhciBzdGFydFBvcyA9IHRoaXMuc3RhcnQsXG4gICAgICAgICAgc3RhcnRMb2MgPSB0aGlzLnN0YXJ0TG9jO1xuICAgICAgdmFyIGlkID0gdGhpcy5wYXJzZUlkZW50KHRoaXMudHlwZSAhPT0gdHQubmFtZSk7XG4gICAgICBpZiAoY2FuQmVBcnJvdyAmJiAhdGhpcy5jYW5JbnNlcnRTZW1pY29sb24oKSAmJiB0aGlzLmVhdCh0dC5hcnJvdykpIHJldHVybiB0aGlzLnBhcnNlQXJyb3dFeHByZXNzaW9uKHRoaXMuc3RhcnROb2RlQXQoc3RhcnRQb3MsIHN0YXJ0TG9jKSwgW2lkXSk7XG4gICAgICByZXR1cm4gaWQ7XG5cbiAgICBjYXNlIHR0LnJlZ2V4cDpcbiAgICAgIHZhciB2YWx1ZSA9IHRoaXMudmFsdWU7XG4gICAgICBub2RlID0gdGhpcy5wYXJzZUxpdGVyYWwodmFsdWUudmFsdWUpO1xuICAgICAgbm9kZS5yZWdleCA9IHsgcGF0dGVybjogdmFsdWUucGF0dGVybiwgZmxhZ3M6IHZhbHVlLmZsYWdzIH07XG4gICAgICByZXR1cm4gbm9kZTtcblxuICAgIGNhc2UgdHQubnVtOmNhc2UgdHQuc3RyaW5nOlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VMaXRlcmFsKHRoaXMudmFsdWUpO1xuXG4gICAgY2FzZSB0dC5fbnVsbDpjYXNlIHR0Ll90cnVlOmNhc2UgdHQuX2ZhbHNlOlxuICAgICAgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gICAgICBub2RlLnZhbHVlID0gdGhpcy50eXBlID09PSB0dC5fbnVsbCA/IG51bGwgOiB0aGlzLnR5cGUgPT09IHR0Ll90cnVlO1xuICAgICAgbm9kZS5yYXcgPSB0aGlzLnR5cGUua2V5d29yZDtcbiAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkxpdGVyYWxcIik7XG5cbiAgICBjYXNlIHR0LnBhcmVuTDpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlUGFyZW5BbmREaXN0aW5ndWlzaEV4cHJlc3Npb24oY2FuQmVBcnJvdyk7XG5cbiAgICBjYXNlIHR0LmJyYWNrZXRMOlxuICAgICAgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gICAgICB0aGlzLm5leHQoKTtcbiAgICAgIC8vIGNoZWNrIHdoZXRoZXIgdGhpcyBpcyBhcnJheSBjb21wcmVoZW5zaW9uIG9yIHJlZ3VsYXIgYXJyYXlcbiAgICAgIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNyAmJiB0aGlzLnR5cGUgPT09IHR0Ll9mb3IpIHtcbiAgICAgICAgcmV0dXJuIHRoaXMucGFyc2VDb21wcmVoZW5zaW9uKG5vZGUsIGZhbHNlKTtcbiAgICAgIH1cbiAgICAgIG5vZGUuZWxlbWVudHMgPSB0aGlzLnBhcnNlRXhwckxpc3QodHQuYnJhY2tldFIsIHRydWUsIHRydWUsIHJlZlNob3J0aGFuZERlZmF1bHRQb3MpO1xuICAgICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkFycmF5RXhwcmVzc2lvblwiKTtcblxuICAgIGNhc2UgdHQuYnJhY2VMOlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VPYmooZmFsc2UsIHJlZlNob3J0aGFuZERlZmF1bHRQb3MpO1xuXG4gICAgY2FzZSB0dC5fZnVuY3Rpb246XG4gICAgICBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgcmV0dXJuIHRoaXMucGFyc2VGdW5jdGlvbihub2RlLCBmYWxzZSk7XG5cbiAgICBjYXNlIHR0Ll9jbGFzczpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlQ2xhc3ModGhpcy5zdGFydE5vZGUoKSwgZmFsc2UpO1xuXG4gICAgY2FzZSB0dC5fbmV3OlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VOZXcoKTtcblxuICAgIGNhc2UgdHQuYmFja1F1b3RlOlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VUZW1wbGF0ZSgpO1xuXG4gICAgZGVmYXVsdDpcbiAgICAgIHRoaXMudW5leHBlY3RlZCgpO1xuICB9XG59O1xuXG5wcC5wYXJzZUxpdGVyYWwgPSBmdW5jdGlvbiAodmFsdWUpIHtcbiAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICBub2RlLnZhbHVlID0gdmFsdWU7XG4gIG5vZGUucmF3ID0gdGhpcy5pbnB1dC5zbGljZSh0aGlzLnN0YXJ0LCB0aGlzLmVuZCk7XG4gIHRoaXMubmV4dCgpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiTGl0ZXJhbFwiKTtcbn07XG5cbnBwLnBhcnNlUGFyZW5FeHByZXNzaW9uID0gZnVuY3Rpb24gKCkge1xuICB0aGlzLmV4cGVjdCh0dC5wYXJlbkwpO1xuICB2YXIgdmFsID0gdGhpcy5wYXJzZUV4cHJlc3Npb24oKTtcbiAgdGhpcy5leHBlY3QodHQucGFyZW5SKTtcbiAgcmV0dXJuIHZhbDtcbn07XG5cbnBwLnBhcnNlUGFyZW5BbmREaXN0aW5ndWlzaEV4cHJlc3Npb24gPSBmdW5jdGlvbiAoY2FuQmVBcnJvdykge1xuICB2YXIgc3RhcnRQb3MgPSB0aGlzLnN0YXJ0LFxuICAgICAgc3RhcnRMb2MgPSB0aGlzLnN0YXJ0TG9jLFxuICAgICAgdmFsID0gdW5kZWZpbmVkO1xuICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYpIHtcbiAgICB0aGlzLm5leHQoKTtcblxuICAgIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNyAmJiB0aGlzLnR5cGUgPT09IHR0Ll9mb3IpIHtcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlQ29tcHJlaGVuc2lvbih0aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0UG9zLCBzdGFydExvYyksIHRydWUpO1xuICAgIH1cblxuICAgIHZhciBpbm5lclN0YXJ0UG9zID0gdGhpcy5zdGFydCxcbiAgICAgICAgaW5uZXJTdGFydExvYyA9IHRoaXMuc3RhcnRMb2M7XG4gICAgdmFyIGV4cHJMaXN0ID0gW10sXG4gICAgICAgIGZpcnN0ID0gdHJ1ZTtcbiAgICB2YXIgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcyA9IHsgc3RhcnQ6IDAgfSxcbiAgICAgICAgc3ByZWFkU3RhcnQgPSB1bmRlZmluZWQsXG4gICAgICAgIGlubmVyUGFyZW5TdGFydCA9IHVuZGVmaW5lZDtcbiAgICB3aGlsZSAodGhpcy50eXBlICE9PSB0dC5wYXJlblIpIHtcbiAgICAgIGZpcnN0ID8gZmlyc3QgPSBmYWxzZSA6IHRoaXMuZXhwZWN0KHR0LmNvbW1hKTtcbiAgICAgIGlmICh0aGlzLnR5cGUgPT09IHR0LmVsbGlwc2lzKSB7XG4gICAgICAgIHNwcmVhZFN0YXJ0ID0gdGhpcy5zdGFydDtcbiAgICAgICAgZXhwckxpc3QucHVzaCh0aGlzLnBhcnNlUGFyZW5JdGVtKHRoaXMucGFyc2VSZXN0KCkpKTtcbiAgICAgICAgYnJlYWs7XG4gICAgICB9IGVsc2Uge1xuICAgICAgICBpZiAodGhpcy50eXBlID09PSB0dC5wYXJlbkwgJiYgIWlubmVyUGFyZW5TdGFydCkge1xuICAgICAgICAgIGlubmVyUGFyZW5TdGFydCA9IHRoaXMuc3RhcnQ7XG4gICAgICAgIH1cbiAgICAgICAgZXhwckxpc3QucHVzaCh0aGlzLnBhcnNlTWF5YmVBc3NpZ24oZmFsc2UsIHJlZlNob3J0aGFuZERlZmF1bHRQb3MsIHRoaXMucGFyc2VQYXJlbkl0ZW0pKTtcbiAgICAgIH1cbiAgICB9XG4gICAgdmFyIGlubmVyRW5kUG9zID0gdGhpcy5zdGFydCxcbiAgICAgICAgaW5uZXJFbmRMb2MgPSB0aGlzLnN0YXJ0TG9jO1xuICAgIHRoaXMuZXhwZWN0KHR0LnBhcmVuUik7XG5cbiAgICBpZiAoY2FuQmVBcnJvdyAmJiAhdGhpcy5jYW5JbnNlcnRTZW1pY29sb24oKSAmJiB0aGlzLmVhdCh0dC5hcnJvdykpIHtcbiAgICAgIGlmIChpbm5lclBhcmVuU3RhcnQpIHRoaXMudW5leHBlY3RlZChpbm5lclBhcmVuU3RhcnQpO1xuICAgICAgcmV0dXJuIHRoaXMucGFyc2VQYXJlbkFycm93TGlzdChzdGFydFBvcywgc3RhcnRMb2MsIGV4cHJMaXN0KTtcbiAgICB9XG5cbiAgICBpZiAoIWV4cHJMaXN0Lmxlbmd0aCkgdGhpcy51bmV4cGVjdGVkKHRoaXMubGFzdFRva1N0YXJ0KTtcbiAgICBpZiAoc3ByZWFkU3RhcnQpIHRoaXMudW5leHBlY3RlZChzcHJlYWRTdGFydCk7XG4gICAgaWYgKHJlZlNob3J0aGFuZERlZmF1bHRQb3Muc3RhcnQpIHRoaXMudW5leHBlY3RlZChyZWZTaG9ydGhhbmREZWZhdWx0UG9zLnN0YXJ0KTtcblxuICAgIGlmIChleHByTGlzdC5sZW5ndGggPiAxKSB7XG4gICAgICB2YWwgPSB0aGlzLnN0YXJ0Tm9kZUF0KGlubmVyU3RhcnRQb3MsIGlubmVyU3RhcnRMb2MpO1xuICAgICAgdmFsLmV4cHJlc3Npb25zID0gZXhwckxpc3Q7XG4gICAgICB0aGlzLmZpbmlzaE5vZGVBdCh2YWwsIFwiU2VxdWVuY2VFeHByZXNzaW9uXCIsIGlubmVyRW5kUG9zLCBpbm5lckVuZExvYyk7XG4gICAgfSBlbHNlIHtcbiAgICAgIHZhbCA9IGV4cHJMaXN0WzBdO1xuICAgIH1cbiAgfSBlbHNlIHtcbiAgICB2YWwgPSB0aGlzLnBhcnNlUGFyZW5FeHByZXNzaW9uKCk7XG4gIH1cblxuICBpZiAodGhpcy5vcHRpb25zLnByZXNlcnZlUGFyZW5zKSB7XG4gICAgdmFyIHBhciA9IHRoaXMuc3RhcnROb2RlQXQoc3RhcnRQb3MsIHN0YXJ0TG9jKTtcbiAgICBwYXIuZXhwcmVzc2lvbiA9IHZhbDtcbiAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKHBhciwgXCJQYXJlbnRoZXNpemVkRXhwcmVzc2lvblwiKTtcbiAgfSBlbHNlIHtcbiAgICByZXR1cm4gdmFsO1xuICB9XG59O1xuXG5wcC5wYXJzZVBhcmVuSXRlbSA9IGZ1bmN0aW9uIChpdGVtKSB7XG4gIHJldHVybiBpdGVtO1xufTtcblxucHAucGFyc2VQYXJlbkFycm93TGlzdCA9IGZ1bmN0aW9uIChzdGFydFBvcywgc3RhcnRMb2MsIGV4cHJMaXN0KSB7XG4gIHJldHVybiB0aGlzLnBhcnNlQXJyb3dFeHByZXNzaW9uKHRoaXMuc3RhcnROb2RlQXQoc3RhcnRQb3MsIHN0YXJ0TG9jKSwgZXhwckxpc3QpO1xufTtcblxuLy8gTmV3J3MgcHJlY2VkZW5jZSBpcyBzbGlnaHRseSB0cmlja3kuIEl0IG11c3QgYWxsb3cgaXRzIGFyZ3VtZW50XG4vLyB0byBiZSBhIGBbXWAgb3IgZG90IHN1YnNjcmlwdCBleHByZXNzaW9uLCBidXQgbm90IGEgY2FsbCDigJQgYXRcbi8vIGxlYXN0LCBub3Qgd2l0aG91dCB3cmFwcGluZyBpdCBpbiBwYXJlbnRoZXNlcy4gVGh1cywgaXQgdXNlcyB0aGVcblxudmFyIGVtcHR5ID0gW107XG5cbnBwLnBhcnNlTmV3ID0gZnVuY3Rpb24gKCkge1xuICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gIHZhciBtZXRhID0gdGhpcy5wYXJzZUlkZW50KHRydWUpO1xuICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYgJiYgdGhpcy5lYXQodHQuZG90KSkge1xuICAgIG5vZGUubWV0YSA9IG1ldGE7XG4gICAgbm9kZS5wcm9wZXJ0eSA9IHRoaXMucGFyc2VJZGVudCh0cnVlKTtcbiAgICBpZiAobm9kZS5wcm9wZXJ0eS5uYW1lICE9PSBcInRhcmdldFwiKSB0aGlzLnJhaXNlKG5vZGUucHJvcGVydHkuc3RhcnQsIFwiVGhlIG9ubHkgdmFsaWQgbWV0YSBwcm9wZXJ0eSBmb3IgbmV3IGlzIG5ldy50YXJnZXRcIik7XG4gICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIk1ldGFQcm9wZXJ0eVwiKTtcbiAgfVxuICB2YXIgc3RhcnRQb3MgPSB0aGlzLnN0YXJ0LFxuICAgICAgc3RhcnRMb2MgPSB0aGlzLnN0YXJ0TG9jO1xuICBub2RlLmNhbGxlZSA9IHRoaXMucGFyc2VTdWJzY3JpcHRzKHRoaXMucGFyc2VFeHByQXRvbSgpLCBzdGFydFBvcywgc3RhcnRMb2MsIHRydWUpO1xuICBpZiAodGhpcy5lYXQodHQucGFyZW5MKSkgbm9kZS5hcmd1bWVudHMgPSB0aGlzLnBhcnNlRXhwckxpc3QodHQucGFyZW5SLCBmYWxzZSk7ZWxzZSBub2RlLmFyZ3VtZW50cyA9IGVtcHR5O1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiTmV3RXhwcmVzc2lvblwiKTtcbn07XG5cbi8vIFBhcnNlIHRlbXBsYXRlIGV4cHJlc3Npb24uXG5cbnBwLnBhcnNlVGVtcGxhdGVFbGVtZW50ID0gZnVuY3Rpb24gKCkge1xuICB2YXIgZWxlbSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gIGVsZW0udmFsdWUgPSB7XG4gICAgcmF3OiB0aGlzLmlucHV0LnNsaWNlKHRoaXMuc3RhcnQsIHRoaXMuZW5kKSxcbiAgICBjb29rZWQ6IHRoaXMudmFsdWVcbiAgfTtcbiAgdGhpcy5uZXh0KCk7XG4gIGVsZW0udGFpbCA9IHRoaXMudHlwZSA9PT0gdHQuYmFja1F1b3RlO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKGVsZW0sIFwiVGVtcGxhdGVFbGVtZW50XCIpO1xufTtcblxucHAucGFyc2VUZW1wbGF0ZSA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICB0aGlzLm5leHQoKTtcbiAgbm9kZS5leHByZXNzaW9ucyA9IFtdO1xuICB2YXIgY3VyRWx0ID0gdGhpcy5wYXJzZVRlbXBsYXRlRWxlbWVudCgpO1xuICBub2RlLnF1YXNpcyA9IFtjdXJFbHRdO1xuICB3aGlsZSAoIWN1ckVsdC50YWlsKSB7XG4gICAgdGhpcy5leHBlY3QodHQuZG9sbGFyQnJhY2VMKTtcbiAgICBub2RlLmV4cHJlc3Npb25zLnB1c2godGhpcy5wYXJzZUV4cHJlc3Npb24oKSk7XG4gICAgdGhpcy5leHBlY3QodHQuYnJhY2VSKTtcbiAgICBub2RlLnF1YXNpcy5wdXNoKGN1ckVsdCA9IHRoaXMucGFyc2VUZW1wbGF0ZUVsZW1lbnQoKSk7XG4gIH1cbiAgdGhpcy5uZXh0KCk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJUZW1wbGF0ZUxpdGVyYWxcIik7XG59O1xuXG4vLyBQYXJzZSBhbiBvYmplY3QgbGl0ZXJhbCBvciBiaW5kaW5nIHBhdHRlcm4uXG5cbnBwLnBhcnNlT2JqID0gZnVuY3Rpb24gKGlzUGF0dGVybiwgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcykge1xuICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCksXG4gICAgICBmaXJzdCA9IHRydWUsXG4gICAgICBwcm9wSGFzaCA9IHt9O1xuICBub2RlLnByb3BlcnRpZXMgPSBbXTtcbiAgdGhpcy5uZXh0KCk7XG4gIHdoaWxlICghdGhpcy5lYXQodHQuYnJhY2VSKSkge1xuICAgIGlmICghZmlyc3QpIHtcbiAgICAgIHRoaXMuZXhwZWN0KHR0LmNvbW1hKTtcbiAgICAgIGlmICh0aGlzLmFmdGVyVHJhaWxpbmdDb21tYSh0dC5icmFjZVIpKSBicmVhaztcbiAgICB9IGVsc2UgZmlyc3QgPSBmYWxzZTtcblxuICAgIHZhciBwcm9wID0gdGhpcy5zdGFydE5vZGUoKSxcbiAgICAgICAgaXNHZW5lcmF0b3IgPSB1bmRlZmluZWQsXG4gICAgICAgIHN0YXJ0UG9zID0gdW5kZWZpbmVkLFxuICAgICAgICBzdGFydExvYyA9IHVuZGVmaW5lZDtcbiAgICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYpIHtcbiAgICAgIHByb3AubWV0aG9kID0gZmFsc2U7XG4gICAgICBwcm9wLnNob3J0aGFuZCA9IGZhbHNlO1xuICAgICAgaWYgKGlzUGF0dGVybiB8fCByZWZTaG9ydGhhbmREZWZhdWx0UG9zKSB7XG4gICAgICAgIHN0YXJ0UG9zID0gdGhpcy5zdGFydDtcbiAgICAgICAgc3RhcnRMb2MgPSB0aGlzLnN0YXJ0TG9jO1xuICAgICAgfVxuICAgICAgaWYgKCFpc1BhdHRlcm4pIGlzR2VuZXJhdG9yID0gdGhpcy5lYXQodHQuc3Rhcik7XG4gICAgfVxuICAgIHRoaXMucGFyc2VQcm9wZXJ0eU5hbWUocHJvcCk7XG4gICAgdGhpcy5wYXJzZVByb3BlcnR5VmFsdWUocHJvcCwgaXNQYXR0ZXJuLCBpc0dlbmVyYXRvciwgc3RhcnRQb3MsIHN0YXJ0TG9jLCByZWZTaG9ydGhhbmREZWZhdWx0UG9zKTtcbiAgICB0aGlzLmNoZWNrUHJvcENsYXNoKHByb3AsIHByb3BIYXNoKTtcbiAgICBub2RlLnByb3BlcnRpZXMucHVzaCh0aGlzLmZpbmlzaE5vZGUocHJvcCwgXCJQcm9wZXJ0eVwiKSk7XG4gIH1cbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBpc1BhdHRlcm4gPyBcIk9iamVjdFBhdHRlcm5cIiA6IFwiT2JqZWN0RXhwcmVzc2lvblwiKTtcbn07XG5cbnBwLnBhcnNlUHJvcGVydHlWYWx1ZSA9IGZ1bmN0aW9uIChwcm9wLCBpc1BhdHRlcm4sIGlzR2VuZXJhdG9yLCBzdGFydFBvcywgc3RhcnRMb2MsIHJlZlNob3J0aGFuZERlZmF1bHRQb3MpIHtcbiAgaWYgKHRoaXMuZWF0KHR0LmNvbG9uKSkge1xuICAgIHByb3AudmFsdWUgPSBpc1BhdHRlcm4gPyB0aGlzLnBhcnNlTWF5YmVEZWZhdWx0KHRoaXMuc3RhcnQsIHRoaXMuc3RhcnRMb2MpIDogdGhpcy5wYXJzZU1heWJlQXNzaWduKGZhbHNlLCByZWZTaG9ydGhhbmREZWZhdWx0UG9zKTtcbiAgICBwcm9wLmtpbmQgPSBcImluaXRcIjtcbiAgfSBlbHNlIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNiAmJiB0aGlzLnR5cGUgPT09IHR0LnBhcmVuTCkge1xuICAgIGlmIChpc1BhdHRlcm4pIHRoaXMudW5leHBlY3RlZCgpO1xuICAgIHByb3Aua2luZCA9IFwiaW5pdFwiO1xuICAgIHByb3AubWV0aG9kID0gdHJ1ZTtcbiAgICBwcm9wLnZhbHVlID0gdGhpcy5wYXJzZU1ldGhvZChpc0dlbmVyYXRvcik7XG4gIH0gZWxzZSBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDUgJiYgIXByb3AuY29tcHV0ZWQgJiYgcHJvcC5rZXkudHlwZSA9PT0gXCJJZGVudGlmaWVyXCIgJiYgKHByb3Aua2V5Lm5hbWUgPT09IFwiZ2V0XCIgfHwgcHJvcC5rZXkubmFtZSA9PT0gXCJzZXRcIikgJiYgKHRoaXMudHlwZSAhPSB0dC5jb21tYSAmJiB0aGlzLnR5cGUgIT0gdHQuYnJhY2VSKSkge1xuICAgIGlmIChpc0dlbmVyYXRvciB8fCBpc1BhdHRlcm4pIHRoaXMudW5leHBlY3RlZCgpO1xuICAgIHByb3Aua2luZCA9IHByb3Aua2V5Lm5hbWU7XG4gICAgdGhpcy5wYXJzZVByb3BlcnR5TmFtZShwcm9wKTtcbiAgICBwcm9wLnZhbHVlID0gdGhpcy5wYXJzZU1ldGhvZChmYWxzZSk7XG4gIH0gZWxzZSBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYgJiYgIXByb3AuY29tcHV0ZWQgJiYgcHJvcC5rZXkudHlwZSA9PT0gXCJJZGVudGlmaWVyXCIpIHtcbiAgICBwcm9wLmtpbmQgPSBcImluaXRcIjtcbiAgICBpZiAoaXNQYXR0ZXJuKSB7XG4gICAgICBpZiAodGhpcy5pc0tleXdvcmQocHJvcC5rZXkubmFtZSkgfHwgdGhpcy5zdHJpY3QgJiYgKHJlc2VydmVkV29yZHMuc3RyaWN0QmluZChwcm9wLmtleS5uYW1lKSB8fCByZXNlcnZlZFdvcmRzLnN0cmljdChwcm9wLmtleS5uYW1lKSkgfHwgIXRoaXMub3B0aW9ucy5hbGxvd1Jlc2VydmVkICYmIHRoaXMuaXNSZXNlcnZlZFdvcmQocHJvcC5rZXkubmFtZSkpIHRoaXMucmFpc2UocHJvcC5rZXkuc3RhcnQsIFwiQmluZGluZyBcIiArIHByb3Aua2V5Lm5hbWUpO1xuICAgICAgcHJvcC52YWx1ZSA9IHRoaXMucGFyc2VNYXliZURlZmF1bHQoc3RhcnRQb3MsIHN0YXJ0TG9jLCBwcm9wLmtleSk7XG4gICAgfSBlbHNlIGlmICh0aGlzLnR5cGUgPT09IHR0LmVxICYmIHJlZlNob3J0aGFuZERlZmF1bHRQb3MpIHtcbiAgICAgIGlmICghcmVmU2hvcnRoYW5kRGVmYXVsdFBvcy5zdGFydCkgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcy5zdGFydCA9IHRoaXMuc3RhcnQ7XG4gICAgICBwcm9wLnZhbHVlID0gdGhpcy5wYXJzZU1heWJlRGVmYXVsdChzdGFydFBvcywgc3RhcnRMb2MsIHByb3Aua2V5KTtcbiAgICB9IGVsc2Uge1xuICAgICAgcHJvcC52YWx1ZSA9IHByb3Aua2V5O1xuICAgIH1cbiAgICBwcm9wLnNob3J0aGFuZCA9IHRydWU7XG4gIH0gZWxzZSB0aGlzLnVuZXhwZWN0ZWQoKTtcbn07XG5cbnBwLnBhcnNlUHJvcGVydHlOYW1lID0gZnVuY3Rpb24gKHByb3ApIHtcbiAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KSB7XG4gICAgaWYgKHRoaXMuZWF0KHR0LmJyYWNrZXRMKSkge1xuICAgICAgcHJvcC5jb21wdXRlZCA9IHRydWU7XG4gICAgICBwcm9wLmtleSA9IHRoaXMucGFyc2VNYXliZUFzc2lnbigpO1xuICAgICAgdGhpcy5leHBlY3QodHQuYnJhY2tldFIpO1xuICAgICAgcmV0dXJuIHByb3Aua2V5O1xuICAgIH0gZWxzZSB7XG4gICAgICBwcm9wLmNvbXB1dGVkID0gZmFsc2U7XG4gICAgfVxuICB9XG4gIHJldHVybiBwcm9wLmtleSA9IHRoaXMudHlwZSA9PT0gdHQubnVtIHx8IHRoaXMudHlwZSA9PT0gdHQuc3RyaW5nID8gdGhpcy5wYXJzZUV4cHJBdG9tKCkgOiB0aGlzLnBhcnNlSWRlbnQodHJ1ZSk7XG59O1xuXG4vLyBJbml0aWFsaXplIGVtcHR5IGZ1bmN0aW9uIG5vZGUuXG5cbnBwLmluaXRGdW5jdGlvbiA9IGZ1bmN0aW9uIChub2RlKSB7XG4gIG5vZGUuaWQgPSBudWxsO1xuICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYpIHtcbiAgICBub2RlLmdlbmVyYXRvciA9IGZhbHNlO1xuICAgIG5vZGUuZXhwcmVzc2lvbiA9IGZhbHNlO1xuICB9XG59O1xuXG4vLyBQYXJzZSBvYmplY3Qgb3IgY2xhc3MgbWV0aG9kLlxuXG5wcC5wYXJzZU1ldGhvZCA9IGZ1bmN0aW9uIChpc0dlbmVyYXRvcikge1xuICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gIHRoaXMuaW5pdEZ1bmN0aW9uKG5vZGUpO1xuICB0aGlzLmV4cGVjdCh0dC5wYXJlbkwpO1xuICBub2RlLnBhcmFtcyA9IHRoaXMucGFyc2VCaW5kaW5nTGlzdCh0dC5wYXJlblIsIGZhbHNlLCBmYWxzZSk7XG4gIHZhciBhbGxvd0V4cHJlc3Npb25Cb2R5ID0gdW5kZWZpbmVkO1xuICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYpIHtcbiAgICBub2RlLmdlbmVyYXRvciA9IGlzR2VuZXJhdG9yO1xuICAgIGFsbG93RXhwcmVzc2lvbkJvZHkgPSB0cnVlO1xuICB9IGVsc2Uge1xuICAgIGFsbG93RXhwcmVzc2lvbkJvZHkgPSBmYWxzZTtcbiAgfVxuICB0aGlzLnBhcnNlRnVuY3Rpb25Cb2R5KG5vZGUsIGFsbG93RXhwcmVzc2lvbkJvZHkpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiRnVuY3Rpb25FeHByZXNzaW9uXCIpO1xufTtcblxuLy8gUGFyc2UgYXJyb3cgZnVuY3Rpb24gZXhwcmVzc2lvbiB3aXRoIGdpdmVuIHBhcmFtZXRlcnMuXG5cbnBwLnBhcnNlQXJyb3dFeHByZXNzaW9uID0gZnVuY3Rpb24gKG5vZGUsIHBhcmFtcykge1xuICB0aGlzLmluaXRGdW5jdGlvbihub2RlKTtcbiAgbm9kZS5wYXJhbXMgPSB0aGlzLnRvQXNzaWduYWJsZUxpc3QocGFyYW1zLCB0cnVlKTtcbiAgdGhpcy5wYXJzZUZ1bmN0aW9uQm9keShub2RlLCB0cnVlKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkFycm93RnVuY3Rpb25FeHByZXNzaW9uXCIpO1xufTtcblxuLy8gUGFyc2UgZnVuY3Rpb24gYm9keSBhbmQgY2hlY2sgcGFyYW1ldGVycy5cblxucHAucGFyc2VGdW5jdGlvbkJvZHkgPSBmdW5jdGlvbiAobm9kZSwgYWxsb3dFeHByZXNzaW9uKSB7XG4gIHZhciBpc0V4cHJlc3Npb24gPSBhbGxvd0V4cHJlc3Npb24gJiYgdGhpcy50eXBlICE9PSB0dC5icmFjZUw7XG5cbiAgaWYgKGlzRXhwcmVzc2lvbikge1xuICAgIG5vZGUuYm9keSA9IHRoaXMucGFyc2VNYXliZUFzc2lnbigpO1xuICAgIG5vZGUuZXhwcmVzc2lvbiA9IHRydWU7XG4gIH0gZWxzZSB7XG4gICAgLy8gU3RhcnQgYSBuZXcgc2NvcGUgd2l0aCByZWdhcmQgdG8gbGFiZWxzIGFuZCB0aGUgYGluRnVuY3Rpb25gXG4gICAgLy8gZmxhZyAocmVzdG9yZSB0aGVtIHRvIHRoZWlyIG9sZCB2YWx1ZSBhZnRlcndhcmRzKS5cbiAgICB2YXIgb2xkSW5GdW5jID0gdGhpcy5pbkZ1bmN0aW9uLFxuICAgICAgICBvbGRJbkdlbiA9IHRoaXMuaW5HZW5lcmF0b3IsXG4gICAgICAgIG9sZExhYmVscyA9IHRoaXMubGFiZWxzO1xuICAgIHRoaXMuaW5GdW5jdGlvbiA9IHRydWU7dGhpcy5pbkdlbmVyYXRvciA9IG5vZGUuZ2VuZXJhdG9yO3RoaXMubGFiZWxzID0gW107XG4gICAgbm9kZS5ib2R5ID0gdGhpcy5wYXJzZUJsb2NrKHRydWUpO1xuICAgIG5vZGUuZXhwcmVzc2lvbiA9IGZhbHNlO1xuICAgIHRoaXMuaW5GdW5jdGlvbiA9IG9sZEluRnVuYzt0aGlzLmluR2VuZXJhdG9yID0gb2xkSW5HZW47dGhpcy5sYWJlbHMgPSBvbGRMYWJlbHM7XG4gIH1cblxuICAvLyBJZiB0aGlzIGlzIGEgc3RyaWN0IG1vZGUgZnVuY3Rpb24sIHZlcmlmeSB0aGF0IGFyZ3VtZW50IG5hbWVzXG4gIC8vIGFyZSBub3QgcmVwZWF0ZWQsIGFuZCBpdCBkb2VzIG5vdCB0cnkgdG8gYmluZCB0aGUgd29yZHMgYGV2YWxgXG4gIC8vIG9yIGBhcmd1bWVudHNgLlxuICBpZiAodGhpcy5zdHJpY3QgfHwgIWlzRXhwcmVzc2lvbiAmJiBub2RlLmJvZHkuYm9keS5sZW5ndGggJiYgdGhpcy5pc1VzZVN0cmljdChub2RlLmJvZHkuYm9keVswXSkpIHtcbiAgICB2YXIgbmFtZUhhc2ggPSB7fSxcbiAgICAgICAgb2xkU3RyaWN0ID0gdGhpcy5zdHJpY3Q7XG4gICAgdGhpcy5zdHJpY3QgPSB0cnVlO1xuICAgIGlmIChub2RlLmlkKSB0aGlzLmNoZWNrTFZhbChub2RlLmlkLCB0cnVlKTtcbiAgICBmb3IgKHZhciBpID0gMDsgaSA8IG5vZGUucGFyYW1zLmxlbmd0aDsgaSsrKSB7XG4gICAgICB0aGlzLmNoZWNrTFZhbChub2RlLnBhcmFtc1tpXSwgdHJ1ZSwgbmFtZUhhc2gpO1xuICAgIH10aGlzLnN0cmljdCA9IG9sZFN0cmljdDtcbiAgfVxufTtcblxuLy8gUGFyc2VzIGEgY29tbWEtc2VwYXJhdGVkIGxpc3Qgb2YgZXhwcmVzc2lvbnMsIGFuZCByZXR1cm5zIHRoZW0gYXNcbi8vIGFuIGFycmF5LiBgY2xvc2VgIGlzIHRoZSB0b2tlbiB0eXBlIHRoYXQgZW5kcyB0aGUgbGlzdCwgYW5kXG4vLyBgYWxsb3dFbXB0eWAgY2FuIGJlIHR1cm5lZCBvbiB0byBhbGxvdyBzdWJzZXF1ZW50IGNvbW1hcyB3aXRoXG4vLyBub3RoaW5nIGluIGJldHdlZW4gdGhlbSB0byBiZSBwYXJzZWQgYXMgYG51bGxgICh3aGljaCBpcyBuZWVkZWRcbi8vIGZvciBhcnJheSBsaXRlcmFscykuXG5cbnBwLnBhcnNlRXhwckxpc3QgPSBmdW5jdGlvbiAoY2xvc2UsIGFsbG93VHJhaWxpbmdDb21tYSwgYWxsb3dFbXB0eSwgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcykge1xuICB2YXIgZWx0cyA9IFtdLFxuICAgICAgZmlyc3QgPSB0cnVlO1xuICB3aGlsZSAoIXRoaXMuZWF0KGNsb3NlKSkge1xuICAgIGlmICghZmlyc3QpIHtcbiAgICAgIHRoaXMuZXhwZWN0KHR0LmNvbW1hKTtcbiAgICAgIGlmIChhbGxvd1RyYWlsaW5nQ29tbWEgJiYgdGhpcy5hZnRlclRyYWlsaW5nQ29tbWEoY2xvc2UpKSBicmVhaztcbiAgICB9IGVsc2UgZmlyc3QgPSBmYWxzZTtcblxuICAgIGlmIChhbGxvd0VtcHR5ICYmIHRoaXMudHlwZSA9PT0gdHQuY29tbWEpIHtcbiAgICAgIGVsdHMucHVzaChudWxsKTtcbiAgICB9IGVsc2Uge1xuICAgICAgaWYgKHRoaXMudHlwZSA9PT0gdHQuZWxsaXBzaXMpIGVsdHMucHVzaCh0aGlzLnBhcnNlU3ByZWFkKHJlZlNob3J0aGFuZERlZmF1bHRQb3MpKTtlbHNlIGVsdHMucHVzaCh0aGlzLnBhcnNlTWF5YmVBc3NpZ24oZmFsc2UsIHJlZlNob3J0aGFuZERlZmF1bHRQb3MpKTtcbiAgICB9XG4gIH1cbiAgcmV0dXJuIGVsdHM7XG59O1xuXG4vLyBQYXJzZSB0aGUgbmV4dCB0b2tlbiBhcyBhbiBpZGVudGlmaWVyLiBJZiBgbGliZXJhbGAgaXMgdHJ1ZSAodXNlZFxuLy8gd2hlbiBwYXJzaW5nIHByb3BlcnRpZXMpLCBpdCB3aWxsIGFsc28gY29udmVydCBrZXl3b3JkcyBpbnRvXG4vLyBpZGVudGlmaWVycy5cblxucHAucGFyc2VJZGVudCA9IGZ1bmN0aW9uIChsaWJlcmFsKSB7XG4gIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgaWYgKGxpYmVyYWwgJiYgdGhpcy5vcHRpb25zLmFsbG93UmVzZXJ2ZWQgPT0gXCJuZXZlclwiKSBsaWJlcmFsID0gZmFsc2U7XG4gIGlmICh0aGlzLnR5cGUgPT09IHR0Lm5hbWUpIHtcbiAgICBpZiAoIWxpYmVyYWwgJiYgKCF0aGlzLm9wdGlvbnMuYWxsb3dSZXNlcnZlZCAmJiB0aGlzLmlzUmVzZXJ2ZWRXb3JkKHRoaXMudmFsdWUpIHx8IHRoaXMuc3RyaWN0ICYmIHJlc2VydmVkV29yZHMuc3RyaWN0KHRoaXMudmFsdWUpICYmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNiB8fCB0aGlzLmlucHV0LnNsaWNlKHRoaXMuc3RhcnQsIHRoaXMuZW5kKS5pbmRleE9mKFwiXFxcXFwiKSA9PSAtMSkpKSB0aGlzLnJhaXNlKHRoaXMuc3RhcnQsIFwiVGhlIGtleXdvcmQgJ1wiICsgdGhpcy52YWx1ZSArIFwiJyBpcyByZXNlcnZlZFwiKTtcbiAgICBub2RlLm5hbWUgPSB0aGlzLnZhbHVlO1xuICB9IGVsc2UgaWYgKGxpYmVyYWwgJiYgdGhpcy50eXBlLmtleXdvcmQpIHtcbiAgICBub2RlLm5hbWUgPSB0aGlzLnR5cGUua2V5d29yZDtcbiAgfSBlbHNlIHtcbiAgICB0aGlzLnVuZXhwZWN0ZWQoKTtcbiAgfVxuICB0aGlzLm5leHQoKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIklkZW50aWZpZXJcIik7XG59O1xuXG4vLyBQYXJzZXMgeWllbGQgZXhwcmVzc2lvbiBpbnNpZGUgZ2VuZXJhdG9yLlxuXG5wcC5wYXJzZVlpZWxkID0gZnVuY3Rpb24gKCkge1xuICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gIHRoaXMubmV4dCgpO1xuICBpZiAodGhpcy50eXBlID09IHR0LnNlbWkgfHwgdGhpcy5jYW5JbnNlcnRTZW1pY29sb24oKSB8fCB0aGlzLnR5cGUgIT0gdHQuc3RhciAmJiAhdGhpcy50eXBlLnN0YXJ0c0V4cHIpIHtcbiAgICBub2RlLmRlbGVnYXRlID0gZmFsc2U7XG4gICAgbm9kZS5hcmd1bWVudCA9IG51bGw7XG4gIH0gZWxzZSB7XG4gICAgbm9kZS5kZWxlZ2F0ZSA9IHRoaXMuZWF0KHR0LnN0YXIpO1xuICAgIG5vZGUuYXJndW1lbnQgPSB0aGlzLnBhcnNlTWF5YmVBc3NpZ24oKTtcbiAgfVxuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiWWllbGRFeHByZXNzaW9uXCIpO1xufTtcblxuLy8gUGFyc2VzIGFycmF5IGFuZCBnZW5lcmF0b3IgY29tcHJlaGVuc2lvbnMuXG5cbnBwLnBhcnNlQ29tcHJlaGVuc2lvbiA9IGZ1bmN0aW9uIChub2RlLCBpc0dlbmVyYXRvcikge1xuICBub2RlLmJsb2NrcyA9IFtdO1xuICB3aGlsZSAodGhpcy50eXBlID09PSB0dC5fZm9yKSB7XG4gICAgdmFyIGJsb2NrID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgICB0aGlzLm5leHQoKTtcbiAgICB0aGlzLmV4cGVjdCh0dC5wYXJlbkwpO1xuICAgIGJsb2NrLmxlZnQgPSB0aGlzLnBhcnNlQmluZGluZ0F0b20oKTtcbiAgICB0aGlzLmNoZWNrTFZhbChibG9jay5sZWZ0LCB0cnVlKTtcbiAgICB0aGlzLmV4cGVjdENvbnRleHR1YWwoXCJvZlwiKTtcbiAgICBibG9jay5yaWdodCA9IHRoaXMucGFyc2VFeHByZXNzaW9uKCk7XG4gICAgdGhpcy5leHBlY3QodHQucGFyZW5SKTtcbiAgICBub2RlLmJsb2Nrcy5wdXNoKHRoaXMuZmluaXNoTm9kZShibG9jaywgXCJDb21wcmVoZW5zaW9uQmxvY2tcIikpO1xuICB9XG4gIG5vZGUuZmlsdGVyID0gdGhpcy5lYXQodHQuX2lmKSA/IHRoaXMucGFyc2VQYXJlbkV4cHJlc3Npb24oKSA6IG51bGw7XG4gIG5vZGUuYm9keSA9IHRoaXMucGFyc2VFeHByZXNzaW9uKCk7XG4gIHRoaXMuZXhwZWN0KGlzR2VuZXJhdG9yID8gdHQucGFyZW5SIDogdHQuYnJhY2tldFIpO1xuICBub2RlLmdlbmVyYXRvciA9IGlzR2VuZXJhdG9yO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiQ29tcHJlaGVuc2lvbkV4cHJlc3Npb25cIik7XG59O1xuXG59LHtcIi4vaWRlbnRpZmllclwiOjcsXCIuL3N0YXRlXCI6MTMsXCIuL3Rva2VudHlwZVwiOjE3LFwiLi91dGlsXCI6MTh9XSw3OltmdW5jdGlvbihfZGVyZXFfLG1vZHVsZSxleHBvcnRzKXtcblxuXG4vLyBUZXN0IHdoZXRoZXIgYSBnaXZlbiBjaGFyYWN0ZXIgY29kZSBzdGFydHMgYW4gaWRlbnRpZmllci5cblxuXCJ1c2Ugc3RyaWN0XCI7XG5cbmV4cG9ydHMuaXNJZGVudGlmaWVyU3RhcnQgPSBpc0lkZW50aWZpZXJTdGFydDtcblxuLy8gVGVzdCB3aGV0aGVyIGEgZ2l2ZW4gY2hhcmFjdGVyIGlzIHBhcnQgb2YgYW4gaWRlbnRpZmllci5cblxuZXhwb3J0cy5pc0lkZW50aWZpZXJDaGFyID0gaXNJZGVudGlmaWVyQ2hhcjtcbmV4cG9ydHMuX19lc01vZHVsZSA9IHRydWU7XG4vLyBUaGlzIGlzIGEgdHJpY2sgdGFrZW4gZnJvbSBFc3ByaW1hLiBJdCB0dXJucyBvdXQgdGhhdCwgb25cbi8vIG5vbi1DaHJvbWUgYnJvd3NlcnMsIHRvIGNoZWNrIHdoZXRoZXIgYSBzdHJpbmcgaXMgaW4gYSBzZXQsIGFcbi8vIHByZWRpY2F0ZSBjb250YWluaW5nIGEgYmlnIHVnbHkgYHN3aXRjaGAgc3RhdGVtZW50IGlzIGZhc3RlciB0aGFuXG4vLyBhIHJlZ3VsYXIgZXhwcmVzc2lvbiwgYW5kIG9uIENocm9tZSB0aGUgdHdvIGFyZSBhYm91dCBvbiBwYXIuXG4vLyBUaGlzIGZ1bmN0aW9uIHVzZXMgYGV2YWxgIChub24tbGV4aWNhbCkgdG8gcHJvZHVjZSBzdWNoIGFcbi8vIHByZWRpY2F0ZSBmcm9tIGEgc3BhY2Utc2VwYXJhdGVkIHN0cmluZyBvZiB3b3Jkcy5cbi8vXG4vLyBJdCBzdGFydHMgYnkgc29ydGluZyB0aGUgd29yZHMgYnkgbGVuZ3RoLlxuXG5mdW5jdGlvbiBtYWtlUHJlZGljYXRlKHdvcmRzKSB7XG4gIHdvcmRzID0gd29yZHMuc3BsaXQoXCIgXCIpO1xuICB2YXIgZiA9IFwiXCIsXG4gICAgICBjYXRzID0gW107XG4gIG91dDogZm9yICh2YXIgaSA9IDA7IGkgPCB3b3Jkcy5sZW5ndGg7ICsraSkge1xuICAgIGZvciAodmFyIGogPSAwOyBqIDwgY2F0cy5sZW5ndGg7ICsraikge1xuICAgICAgaWYgKGNhdHNbal1bMF0ubGVuZ3RoID09IHdvcmRzW2ldLmxlbmd0aCkge1xuICAgICAgICBjYXRzW2pdLnB1c2god29yZHNbaV0pO1xuICAgICAgICBjb250aW51ZSBvdXQ7XG4gICAgICB9XG4gICAgfWNhdHMucHVzaChbd29yZHNbaV1dKTtcbiAgfVxuICBmdW5jdGlvbiBjb21wYXJlVG8oYXJyKSB7XG4gICAgaWYgKGFyci5sZW5ndGggPT0gMSkge1xuICAgICAgcmV0dXJuIGYgKz0gXCJyZXR1cm4gc3RyID09PSBcIiArIEpTT04uc3RyaW5naWZ5KGFyclswXSkgKyBcIjtcIjtcbiAgICB9ZiArPSBcInN3aXRjaChzdHIpe1wiO1xuICAgIGZvciAodmFyIGkgPSAwOyBpIDwgYXJyLmxlbmd0aDsgKytpKSB7XG4gICAgICBmICs9IFwiY2FzZSBcIiArIEpTT04uc3RyaW5naWZ5KGFycltpXSkgKyBcIjpcIjtcbiAgICB9ZiArPSBcInJldHVybiB0cnVlfXJldHVybiBmYWxzZTtcIjtcbiAgfVxuXG4gIC8vIFdoZW4gdGhlcmUgYXJlIG1vcmUgdGhhbiB0aHJlZSBsZW5ndGggY2F0ZWdvcmllcywgYW4gb3V0ZXJcbiAgLy8gc3dpdGNoIGZpcnN0IGRpc3BhdGNoZXMgb24gdGhlIGxlbmd0aHMsIHRvIHNhdmUgb24gY29tcGFyaXNvbnMuXG5cbiAgaWYgKGNhdHMubGVuZ3RoID4gMykge1xuICAgIGNhdHMuc29ydChmdW5jdGlvbiAoYSwgYikge1xuICAgICAgcmV0dXJuIGIubGVuZ3RoIC0gYS5sZW5ndGg7XG4gICAgfSk7XG4gICAgZiArPSBcInN3aXRjaChzdHIubGVuZ3RoKXtcIjtcbiAgICBmb3IgKHZhciBpID0gMDsgaSA8IGNhdHMubGVuZ3RoOyArK2kpIHtcbiAgICAgIHZhciBjYXQgPSBjYXRzW2ldO1xuICAgICAgZiArPSBcImNhc2UgXCIgKyBjYXRbMF0ubGVuZ3RoICsgXCI6XCI7XG4gICAgICBjb21wYXJlVG8oY2F0KTtcbiAgICB9XG4gICAgZiArPSBcIn1cIlxuXG4gICAgLy8gT3RoZXJ3aXNlLCBzaW1wbHkgZ2VuZXJhdGUgYSBmbGF0IGBzd2l0Y2hgIHN0YXRlbWVudC5cblxuICAgIDtcbiAgfSBlbHNlIHtcbiAgICBjb21wYXJlVG8od29yZHMpO1xuICB9XG4gIHJldHVybiBuZXcgRnVuY3Rpb24oXCJzdHJcIiwgZik7XG59XG5cbi8vIFJlc2VydmVkIHdvcmQgbGlzdHMgZm9yIHZhcmlvdXMgZGlhbGVjdHMgb2YgdGhlIGxhbmd1YWdlXG5cbnZhciByZXNlcnZlZFdvcmRzID0ge1xuICAzOiBtYWtlUHJlZGljYXRlKFwiYWJzdHJhY3QgYm9vbGVhbiBieXRlIGNoYXIgY2xhc3MgZG91YmxlIGVudW0gZXhwb3J0IGV4dGVuZHMgZmluYWwgZmxvYXQgZ290byBpbXBsZW1lbnRzIGltcG9ydCBpbnQgaW50ZXJmYWNlIGxvbmcgbmF0aXZlIHBhY2thZ2UgcHJpdmF0ZSBwcm90ZWN0ZWQgcHVibGljIHNob3J0IHN0YXRpYyBzdXBlciBzeW5jaHJvbml6ZWQgdGhyb3dzIHRyYW5zaWVudCB2b2xhdGlsZVwiKSxcbiAgNTogbWFrZVByZWRpY2F0ZShcImNsYXNzIGVudW0gZXh0ZW5kcyBzdXBlciBjb25zdCBleHBvcnQgaW1wb3J0XCIpLFxuICA2OiBtYWtlUHJlZGljYXRlKFwiZW51bSBhd2FpdFwiKSxcbiAgc3RyaWN0OiBtYWtlUHJlZGljYXRlKFwiaW1wbGVtZW50cyBpbnRlcmZhY2UgbGV0IHBhY2thZ2UgcHJpdmF0ZSBwcm90ZWN0ZWQgcHVibGljIHN0YXRpYyB5aWVsZFwiKSxcbiAgc3RyaWN0QmluZDogbWFrZVByZWRpY2F0ZShcImV2YWwgYXJndW1lbnRzXCIpXG59O1xuXG5leHBvcnRzLnJlc2VydmVkV29yZHMgPSByZXNlcnZlZFdvcmRzO1xuLy8gQW5kIHRoZSBrZXl3b3Jkc1xuXG52YXIgZWNtYTVBbmRMZXNzS2V5d29yZHMgPSBcImJyZWFrIGNhc2UgY2F0Y2ggY29udGludWUgZGVidWdnZXIgZGVmYXVsdCBkbyBlbHNlIGZpbmFsbHkgZm9yIGZ1bmN0aW9uIGlmIHJldHVybiBzd2l0Y2ggdGhyb3cgdHJ5IHZhciB3aGlsZSB3aXRoIG51bGwgdHJ1ZSBmYWxzZSBpbnN0YW5jZW9mIHR5cGVvZiB2b2lkIGRlbGV0ZSBuZXcgaW4gdGhpc1wiO1xuXG52YXIga2V5d29yZHMgPSB7XG4gIDU6IG1ha2VQcmVkaWNhdGUoZWNtYTVBbmRMZXNzS2V5d29yZHMpLFxuICA2OiBtYWtlUHJlZGljYXRlKGVjbWE1QW5kTGVzc0tleXdvcmRzICsgXCIgbGV0IGNvbnN0IGNsYXNzIGV4dGVuZHMgZXhwb3J0IGltcG9ydCB5aWVsZCBzdXBlclwiKVxufTtcblxuZXhwb3J0cy5rZXl3b3JkcyA9IGtleXdvcmRzO1xuLy8gIyMgQ2hhcmFjdGVyIGNhdGVnb3JpZXNcblxuLy8gQmlnIHVnbHkgcmVndWxhciBleHByZXNzaW9ucyB0aGF0IG1hdGNoIGNoYXJhY3RlcnMgaW4gdGhlXG4vLyB3aGl0ZXNwYWNlLCBpZGVudGlmaWVyLCBhbmQgaWRlbnRpZmllci1zdGFydCBjYXRlZ29yaWVzLiBUaGVzZVxuLy8gYXJlIG9ubHkgYXBwbGllZCB3aGVuIGEgY2hhcmFjdGVyIGlzIGZvdW5kIHRvIGFjdHVhbGx5IGhhdmUgYVxuLy8gY29kZSBwb2ludCBhYm92ZSAxMjguXG4vLyBHZW5lcmF0ZWQgYnkgYHRvb2xzL2dlbmVyYXRlLWlkZW50aWZpZXItcmVnZXguanNgLlxuXG52YXIgbm9uQVNDSUlpZGVudGlmaWVyU3RhcnRDaGFycyA9IFwiwqrCtcK6w4Atw5bDmC3DtsO4LcuBy4Yty5HLoC3LpMusy67NsC3NtM22zbfNui3Nvc2/zobOiC3Ois6Mzo4tzqHOoy3Ptc+3LdKB0oot1K/UsS3VltWZ1aEt1ofXkC3XqtewLdey2KAt2YrZrtmv2bEt25Pbldul26bbrtuv27ot27zbv9yQ3JIt3K/djS3epd6x34ot36rftN+137rgoIAt4KCV4KCa4KCk4KCo4KGALeChmOCioC3gorLgpIQt4KS54KS94KWQ4KWYLeCloeClsS3gpoDgpoUt4KaM4KaP4KaQ4KaTLeCmqOCmqi3gprDgprLgprYt4Ka54Ka94KeO4Kec4Ked4KefLeCnoeCnsOCnseCohS3gqIrgqI/gqJDgqJMt4Kio4KiqLeCosOCosuCos+CoteCotuCouOCoueCpmS3gqZzgqZ7gqbIt4Km04KqFLeCqjeCqjy3gqpHgqpMt4Kqo4KqqLeCqsOCqsuCqs+CqtS3gqrngqr3gq5Dgq6Dgq6HgrIUt4KyM4KyP4KyQ4KyTLeCsqOCsqi3grLDgrLLgrLPgrLUt4Ky54Ky94K2c4K2d4K2fLeCtoeCtseCug+CuhS3grorgro4t4K6Q4K6SLeCuleCumeCumuCunOCunuCun+Cuo+CupOCuqC3grqrgrq4t4K654K+Q4LCFLeCwjOCwji3gsJDgsJIt4LCo4LCqLeCwueCwveCxmOCxmeCxoOCxoeCyhS3gsozgso4t4LKQ4LKSLeCyqOCyqi3gsrPgsrUt4LK54LK94LOe4LOg4LOh4LOx4LOy4LSFLeC0jOC0ji3gtJDgtJIt4LS64LS94LWO4LWg4LWh4LW6LeC1v+C2hS3gtpbgtpot4Lax4LazLeC2u+C2veC3gC3gt4bguIEt4Liw4Liy4Liz4LmALeC5huC6geC6guC6hOC6h+C6iOC6iuC6jeC6lC3gupfgupkt4Lqf4LqhLeC6o+C6peC6p+C6quC6q+C6rS3gurDgurLgurPgur3gu4At4LuE4LuG4LucLeC7n+C8gOC9gC3gvYfgvYkt4L2s4L6ILeC+jOGAgC3hgKrhgL/hgZAt4YGV4YGaLeGBneGBoeGBpeGBpuGBri3hgbDhgbUt4YKB4YKO4YKgLeGDheGDh+GDjeGDkC3hg7rhg7wt4YmI4YmKLeGJjeGJkC3hiZbhiZjhiZot4Ymd4YmgLeGKiOGKii3hio3hipAt4Yqw4YqyLeGKteGKuC3hir7hi4Dhi4It4YuF4YuILeGLluGLmC3hjJDhjJIt4YyV4YyYLeGNmuGOgC3hjo/hjqAt4Y+04ZCBLeGZrOGZry3hmb/hmoEt4Zqa4ZqgLeGbquGbri3hm7jhnIAt4ZyM4ZyOLeGckeGcoC3hnLHhnYAt4Z2R4Z2gLeGdrOGdri3hnbDhnoAt4Z6z4Z+X4Z+c4aCgLeGht+GigC3hoqjhoqrhorAt4aO14aSALeGknuGlkC3hpa3hpbAt4aW04aaALeGmq+GngS3hp4fhqIAt4aiW4aigLeGplOGqp+GshS3hrLPhrYUt4a2L4a6DLeGuoOGuruGur+Guui3hr6XhsIAt4bCj4bGNLeGxj+Gxmi3hsb3hs6kt4bOs4bOuLeGzseGzteGztuG0gC3htr/huIAt4byV4byYLeG8neG8oC3hvYXhvYgt4b2N4b2QLeG9l+G9meG9m+G9neG9ny3hvb3hvoAt4b604b62LeG+vOG+vuG/gi3hv4Thv4Yt4b+M4b+QLeG/k+G/li3hv5vhv6At4b+s4b+yLeG/tOG/ti3hv7zigbHigb/igpAt4oKc4oSC4oSH4oSKLeKEk+KEleKEmC3ihJ3ihKTihKbihKjihKot4oS54oS8LeKEv+KFhS3ihYnihY7ihaAt4oaI4rCALeKwruKwsC3isZ7isaAt4rOk4rOrLeKzruKzsuKzs+K0gC3itKXitKfitK3itLAt4rWn4rWv4raALeK2luK2oC3itqbitqgt4rau4rawLeK2tuK2uC3itr7it4At4reG4reILeK3juK3kC3it5bit5gt4ree44CFLeOAh+OAoS3jgKnjgLEt44C144C4LeOAvOOBgS3jgpbjgpst44Kf44KhLeODuuODvC3jg7/jhIUt44St44SxLeOGjuOGoC3jhrrjh7At44e/45CALeS2teS4gC3pv4zqgIAt6pKM6pOQLeqTveqUgC3qmIzqmJAt6pif6piq6pir6pmALeqZruqZvy3qmp3qmqAt6puv6pyXLeqcn+qcoi3qnojqnost6p6O6p6QLeqereqesOqeseqfty3qoIHqoIMt6qCF6qCHLeqgiuqgjC3qoKLqoYAt6qGz6qKCLeqis+qjsi3qo7fqo7vqpIot6qSl6qSwLeqlhuqloC3qpbzqpoQt6qay6qeP6qegLeqnpOqnpi3qp6/qp7ot6qe+6qiALeqoqOqpgC3qqYLqqYQt6qmL6qmgLeqptuqpuuqpvi3qqq/qqrHqqrXqqrbqqrkt6qq96quA6quC6qubLeqrneqroC3qq6rqq7It6qu06qyBLeqshuqsiS3qrI7qrJEt6qyW6qygLeqspuqsqC3qrK7qrLAt6q2a6q2cLeqtn+qtpOqtpeqvgC3qr6LqsIAt7Z6j7Z6wLe2fhu2fiy3tn7vvpIAt76mt76mwLe+rme+sgC3vrIbvrJMt76yX76yd76yfLe+sqO+sqi3vrLbvrLgt76y876y+762A762B762D762E762GLe+use+vky3vtL3vtZAt77aP77aSLe+3h++3sC3vt7vvubAt77m077m2Le+7vO+8oS3vvLrvvYEt772a772mLe++vu+/gi3vv4fvv4ot77+P77+SLe+/l++/mi3vv5xcIjtcbnZhciBub25BU0NJSWlkZW50aWZpZXJDaGFycyA9IFwi4oCM4oCNwrfMgC3Nr86H0oMt0ofWkS3Wvda/14HXgteE14XXh9iQLdia2Yst2anZsNuWLduc258t26Tbp9uo26ot263bsC3budyR3LAt3Yrepi3esN+ALd+J36st37PgoJYt4KCZ4KCbLeCgo+CgpS3goKfgoKkt4KCt4KGZLeChm+CjpC3gpIPgpLot4KS84KS+LeClj+ClkS3gpZfgpaLgpaPgpaYt4KWv4KaBLeCmg+CmvOCmvi3gp4Tgp4fgp4jgp4st4KeN4KeX4Kei4Kej4KemLeCnr+CogS3gqIPgqLzgqL4t4KmC4KmH4KmI4KmLLeCpjeCpkeCppi3gqbHgqbXgqoEt4KqD4Kq84Kq+LeCrheCrhy3gq4ngq4st4KuN4Kui4Kuj4KumLeCrr+CsgS3grIPgrLzgrL4t4K2E4K2H4K2I4K2LLeCtjeCtluCtl+CtouCto+Ctpi3gra/groLgrr4t4K+C4K+GLeCviOCvii3gr43gr5fgr6Yt4K+v4LCALeCwg+Cwvi3gsYTgsYYt4LGI4LGKLeCxjeCxleCxluCxouCxo+Cxpi3gsa/gsoEt4LKD4LK84LK+LeCzhOCzhi3gs4jgs4ot4LON4LOV4LOW4LOi4LOj4LOmLeCzr+C0gS3gtIPgtL4t4LWE4LWGLeC1iOC1ii3gtY3gtZfgtaLgtaPgtaYt4LWv4LaC4LaD4LeK4LePLeC3lOC3luC3mC3gt5/gt6Yt4Lev4Ley4Lez4Lix4Li0LeC4uuC5hy3guY7guZAt4LmZ4Lqx4Lq0LeC6ueC6u+C6vOC7iC3gu43gu5At4LuZ4LyY4LyZ4LygLeC8qeC8teC8t+C8ueC8vuC8v+C9sS3gvoTgvobgvofgvo0t4L6X4L6ZLeC+vOC/huGAqy3hgL7hgYAt4YGJ4YGWLeGBmeGBni3hgaDhgaIt4YGk4YGnLeGBreGBsS3hgbThgoIt4YKN4YKPLeGCneGNnS3hjZ/hjakt4Y2x4ZySLeGclOGcsi3hnLThnZLhnZPhnbLhnbPhnrQt4Z+T4Z+d4Z+gLeGfqeGgiy3hoI3hoJAt4aCZ4aKp4aSgLeGkq+GksC3hpLvhpYYt4aWP4aawLeGngOGniOGnieGnkC3hp5rhqJct4aib4amVLeGpnuGpoC3hqbzhqb8t4aqJ4aqQLeGqmeGqsC3hqr3hrIAt4ayE4ay0LeGthOGtkC3hrZnhrast4a2z4a6ALeGuguGuoS3hrq3hrrAt4a654a+mLeGvs+GwpC3hsLfhsYAt4bGJ4bGQLeGxmeGzkC3hs5Lhs5Qt4bOo4bOt4bOyLeGztOGzuOGzueG3gC3ht7Xht7wt4be/4oC/4oGA4oGU4oOQLeKDnOKDoeKDpS3ig7Dis68t4rOx4rW/4regLeK3v+OAqi3jgK/jgpnjgprqmKAt6pip6pmv6pm0LeqZveqan+qbsOqbseqgguqghuqgi+qgoy3qoKfqooDqooHqorQt6qOE6qOQLeqjmeqjoC3qo7HqpIAt6qSJ6qSmLeqkreqlhy3qpZPqpoAt6qaD6qazLeqngOqnkC3qp5nqp6Xqp7At6qe56qipLeqotuqpg+qpjOqpjeqpkC3qqZnqqbst6qm96qqw6qqyLeqqtOqqt+qquOqqvuqqv+qrgeqrqy3qq6/qq7Xqq7bqr6Mt6q+q6q+s6q+t6q+wLeqvue+snu+4gC3vuI/vuKAt77it77iz77i077mNLe+5j++8kC3vvJnvvL9cIjtcblxudmFyIG5vbkFTQ0lJaWRlbnRpZmllclN0YXJ0ID0gbmV3IFJlZ0V4cChcIltcIiArIG5vbkFTQ0lJaWRlbnRpZmllclN0YXJ0Q2hhcnMgKyBcIl1cIik7XG52YXIgbm9uQVNDSUlpZGVudGlmaWVyID0gbmV3IFJlZ0V4cChcIltcIiArIG5vbkFTQ0lJaWRlbnRpZmllclN0YXJ0Q2hhcnMgKyBub25BU0NJSWlkZW50aWZpZXJDaGFycyArIFwiXVwiKTtcblxubm9uQVNDSUlpZGVudGlmaWVyU3RhcnRDaGFycyA9IG5vbkFTQ0lJaWRlbnRpZmllckNoYXJzID0gbnVsbDtcblxuLy8gVGhlc2UgYXJlIGEgcnVuLWxlbmd0aCBhbmQgb2Zmc2V0IGVuY29kZWQgcmVwcmVzZW50YXRpb24gb2YgdGhlXG4vLyA+MHhmZmZmIGNvZGUgcG9pbnRzIHRoYXQgYXJlIGEgdmFsaWQgcGFydCBvZiBpZGVudGlmaWVycy4gVGhlXG4vLyBvZmZzZXQgc3RhcnRzIGF0IDB4MTAwMDAsIGFuZCBlYWNoIHBhaXIgb2YgbnVtYmVycyByZXByZXNlbnRzIGFuXG4vLyBvZmZzZXQgdG8gdGhlIG5leHQgcmFuZ2UsIGFuZCB0aGVuIGEgc2l6ZSBvZiB0aGUgcmFuZ2UuIFRoZXkgd2VyZVxuLy8gZ2VuZXJhdGVkIGJ5IHRvb2xzL2dlbmVyYXRlLWlkZW50aWZpZXItcmVnZXguanNcbnZhciBhc3RyYWxJZGVudGlmaWVyU3RhcnRDb2RlcyA9IFswLCAxMSwgMiwgMjUsIDIsIDE4LCAyLCAxLCAyLCAxNCwgMywgMTMsIDM1LCAxMjIsIDcwLCA1MiwgMjY4LCAyOCwgNCwgNDgsIDQ4LCAzMSwgMTcsIDI2LCA2LCAzNywgMTEsIDI5LCAzLCAzNSwgNSwgNywgMiwgNCwgNDMsIDE1NywgOTksIDM5LCA5LCA1MSwgMTU3LCAzMTAsIDEwLCAyMSwgMTEsIDcsIDE1MywgNSwgMywgMCwgMiwgNDMsIDIsIDEsIDQsIDAsIDMsIDIyLCAxMSwgMjIsIDEwLCAzMCwgOTgsIDIxLCAxMSwgMjUsIDcxLCA1NSwgNywgMSwgNjUsIDAsIDE2LCAzLCAyLCAyLCAyLCAyNiwgNDUsIDI4LCA0LCAyOCwgMzYsIDcsIDIsIDI3LCAyOCwgNTMsIDExLCAyMSwgMTEsIDE4LCAxNCwgMTcsIDExMSwgNzIsIDk1NSwgNTIsIDc2LCA0NCwgMzMsIDI0LCAyNywgMzUsIDQyLCAzNCwgNCwgMCwgMTMsIDQ3LCAxNSwgMywgMjIsIDAsIDM4LCAxNywgMiwgMjQsIDEzMywgNDYsIDM5LCA3LCAzLCAxLCAzLCAyMSwgMiwgNiwgMiwgMSwgMiwgNCwgNCwgMCwgMzIsIDQsIDI4NywgNDcsIDIxLCAxLCAyLCAwLCAxODUsIDQ2LCA4MiwgNDcsIDIxLCAwLCA2MCwgNDIsIDUwMiwgNjMsIDMyLCAwLCA0NDksIDU2LCAxMjg4LCA5MjAsIDEwNCwgMTEwLCAyOTYyLCAxMDcwLCAxMzI2NiwgNTY4LCA4LCAzMCwgMTE0LCAyOSwgMTksIDQ3LCAxNywgMywgMzIsIDIwLCA2LCAxOCwgODgxLCA2OCwgMTIsIDAsIDY3LCAxMiwgMTY0ODEsIDEsIDMwNzEsIDEwNiwgNiwgMTIsIDQsIDgsIDgsIDksIDU5OTEsIDg0LCAyLCA3MCwgMiwgMSwgMywgMCwgMywgMSwgMywgMywgMiwgMTEsIDIsIDAsIDIsIDYsIDIsIDY0LCAyLCAzLCAzLCA3LCAyLCA2LCAyLCAyNywgMiwgMywgMiwgNCwgMiwgMCwgNCwgNiwgMiwgMzM5LCAzLCAyNCwgMiwgMjQsIDIsIDMwLCAyLCAyNCwgMiwgMzAsIDIsIDI0LCAyLCAzMCwgMiwgMjQsIDIsIDMwLCAyLCAyNCwgMiwgNywgNDE0OSwgMTk2LCAxMzQwLCAzLCAyLCAyNiwgMiwgMSwgMiwgMCwgMywgMCwgMiwgOSwgMiwgMywgMiwgMCwgMiwgMCwgNywgMCwgNSwgMCwgMiwgMCwgMiwgMCwgMiwgMiwgMiwgMSwgMiwgMCwgMywgMCwgMiwgMCwgMiwgMCwgMiwgMCwgMiwgMCwgMiwgMSwgMiwgMCwgMywgMywgMiwgNiwgMiwgMywgMiwgMywgMiwgMCwgMiwgOSwgMiwgMTYsIDYsIDIsIDIsIDQsIDIsIDE2LCA0NDIxLCA0MjcxMCwgNDIsIDQxNDgsIDEyLCAyMjEsIDE2MzU1LCA1NDFdO1xudmFyIGFzdHJhbElkZW50aWZpZXJDb2RlcyA9IFs1MDksIDAsIDIyNywgMCwgMTUwLCA0LCAyOTQsIDksIDEzNjgsIDIsIDIsIDEsIDYsIDMsIDQxLCAyLCA1LCAwLCAxNjYsIDEsIDEzMDYsIDIsIDU0LCAxNCwgMzIsIDksIDE2LCAzLCA0NiwgMTAsIDU0LCA5LCA3LCAyLCAzNywgMTMsIDIsIDksIDUyLCAwLCAxMywgMiwgNDksIDEzLCAxNiwgOSwgODMsIDExLCAxNjgsIDExLCA2LCA5LCA4LCAyLCA1NywgMCwgMiwgNiwgMywgMSwgMywgMiwgMTAsIDAsIDExLCAxLCAzLCA2LCA0LCA0LCAzMTYsIDE5LCAxMywgOSwgMjE0LCA2LCAzLCA4LCAxMTIsIDE2LCAxNiwgOSwgODIsIDEyLCA5LCA5LCA1MzUsIDksIDIwODU1LCA5LCAxMzUsIDQsIDYwLCA2LCAyNiwgOSwgMTAxNiwgNDUsIDE3LCAzLCAxOTcyMywgMSwgNTMxOSwgNCwgNCwgNSwgOSwgNywgMywgNiwgMzEsIDMsIDE0OSwgMiwgMTQxOCwgNDksIDQzMDUsIDYsIDc5MjYxOCwgMjM5XTtcblxuLy8gVGhpcyBoYXMgYSBjb21wbGV4aXR5IGxpbmVhciB0byB0aGUgdmFsdWUgb2YgdGhlIGNvZGUuIFRoZVxuLy8gYXNzdW1wdGlvbiBpcyB0aGF0IGxvb2tpbmcgdXAgYXN0cmFsIGlkZW50aWZpZXIgY2hhcmFjdGVycyBpc1xuLy8gcmFyZS5cbmZ1bmN0aW9uIGlzSW5Bc3RyYWxTZXQoY29kZSwgc2V0KSB7XG4gIHZhciBwb3MgPSA2NTUzNjtcbiAgZm9yICh2YXIgaSA9IDA7IGkgPCBzZXQubGVuZ3RoOyBpICs9IDIpIHtcbiAgICBwb3MgKz0gc2V0W2ldO1xuICAgIGlmIChwb3MgPiBjb2RlKSB7XG4gICAgICByZXR1cm4gZmFsc2U7XG4gICAgfXBvcyArPSBzZXRbaSArIDFdO1xuICAgIGlmIChwb3MgPj0gY29kZSkge1xuICAgICAgcmV0dXJuIHRydWU7XG4gICAgfVxuICB9XG59XG5mdW5jdGlvbiBpc0lkZW50aWZpZXJTdGFydChjb2RlLCBhc3RyYWwpIHtcbiAgaWYgKGNvZGUgPCA2NSkge1xuICAgIHJldHVybiBjb2RlID09PSAzNjtcbiAgfWlmIChjb2RlIDwgOTEpIHtcbiAgICByZXR1cm4gdHJ1ZTtcbiAgfWlmIChjb2RlIDwgOTcpIHtcbiAgICByZXR1cm4gY29kZSA9PT0gOTU7XG4gIH1pZiAoY29kZSA8IDEyMykge1xuICAgIHJldHVybiB0cnVlO1xuICB9aWYgKGNvZGUgPD0gNjU1MzUpIHtcbiAgICByZXR1cm4gY29kZSA+PSAxNzAgJiYgbm9uQVNDSUlpZGVudGlmaWVyU3RhcnQudGVzdChTdHJpbmcuZnJvbUNoYXJDb2RlKGNvZGUpKTtcbiAgfWlmIChhc3RyYWwgPT09IGZhbHNlKSB7XG4gICAgcmV0dXJuIGZhbHNlO1xuICB9cmV0dXJuIGlzSW5Bc3RyYWxTZXQoY29kZSwgYXN0cmFsSWRlbnRpZmllclN0YXJ0Q29kZXMpO1xufVxuXG5mdW5jdGlvbiBpc0lkZW50aWZpZXJDaGFyKGNvZGUsIGFzdHJhbCkge1xuICBpZiAoY29kZSA8IDQ4KSB7XG4gICAgcmV0dXJuIGNvZGUgPT09IDM2O1xuICB9aWYgKGNvZGUgPCA1OCkge1xuICAgIHJldHVybiB0cnVlO1xuICB9aWYgKGNvZGUgPCA2NSkge1xuICAgIHJldHVybiBmYWxzZTtcbiAgfWlmIChjb2RlIDwgOTEpIHtcbiAgICByZXR1cm4gdHJ1ZTtcbiAgfWlmIChjb2RlIDwgOTcpIHtcbiAgICByZXR1cm4gY29kZSA9PT0gOTU7XG4gIH1pZiAoY29kZSA8IDEyMykge1xuICAgIHJldHVybiB0cnVlO1xuICB9aWYgKGNvZGUgPD0gNjU1MzUpIHtcbiAgICByZXR1cm4gY29kZSA+PSAxNzAgJiYgbm9uQVNDSUlpZGVudGlmaWVyLnRlc3QoU3RyaW5nLmZyb21DaGFyQ29kZShjb2RlKSk7XG4gIH1pZiAoYXN0cmFsID09PSBmYWxzZSkge1xuICAgIHJldHVybiBmYWxzZTtcbiAgfXJldHVybiBpc0luQXN0cmFsU2V0KGNvZGUsIGFzdHJhbElkZW50aWZpZXJTdGFydENvZGVzKSB8fCBpc0luQXN0cmFsU2V0KGNvZGUsIGFzdHJhbElkZW50aWZpZXJDb2Rlcyk7XG59XG5cbn0se31dLDg6W2Z1bmN0aW9uKF9kZXJlcV8sbW9kdWxlLGV4cG9ydHMpe1xuXCJ1c2Ugc3RyaWN0XCI7XG5cbnZhciBfY2xhc3NDYWxsQ2hlY2sgPSBmdW5jdGlvbiAoaW5zdGFuY2UsIENvbnN0cnVjdG9yKSB7IGlmICghKGluc3RhbmNlIGluc3RhbmNlb2YgQ29uc3RydWN0b3IpKSB7IHRocm93IG5ldyBUeXBlRXJyb3IoXCJDYW5ub3QgY2FsbCBhIGNsYXNzIGFzIGEgZnVuY3Rpb25cIik7IH0gfTtcblxuLy8gVGhlIGBnZXRMaW5lSW5mb2AgZnVuY3Rpb24gaXMgbW9zdGx5IHVzZWZ1bCB3aGVuIHRoZVxuLy8gYGxvY2F0aW9uc2Agb3B0aW9uIGlzIG9mZiAoZm9yIHBlcmZvcm1hbmNlIHJlYXNvbnMpIGFuZCB5b3Vcbi8vIHdhbnQgdG8gZmluZCB0aGUgbGluZS9jb2x1bW4gcG9zaXRpb24gZm9yIGEgZ2l2ZW4gY2hhcmFjdGVyXG4vLyBvZmZzZXQuIGBpbnB1dGAgc2hvdWxkIGJlIHRoZSBjb2RlIHN0cmluZyB0aGF0IHRoZSBvZmZzZXQgcmVmZXJzXG4vLyBpbnRvLlxuXG5leHBvcnRzLmdldExpbmVJbmZvID0gZ2V0TGluZUluZm87XG5leHBvcnRzLl9fZXNNb2R1bGUgPSB0cnVlO1xuXG52YXIgUGFyc2VyID0gX2RlcmVxXyhcIi4vc3RhdGVcIikuUGFyc2VyO1xuXG52YXIgbGluZUJyZWFrRyA9IF9kZXJlcV8oXCIuL3doaXRlc3BhY2VcIikubGluZUJyZWFrRztcblxudmFyIGRlcHJlY2F0ZSA9IF9kZXJlcV8oXCJ1dGlsXCIpLmRlcHJlY2F0ZTtcblxuLy8gVGhlc2UgYXJlIHVzZWQgd2hlbiBgb3B0aW9ucy5sb2NhdGlvbnNgIGlzIG9uLCBmb3IgdGhlXG4vLyBgc3RhcnRMb2NgIGFuZCBgZW5kTG9jYCBwcm9wZXJ0aWVzLlxuXG52YXIgUG9zaXRpb24gPSBleHBvcnRzLlBvc2l0aW9uID0gKGZ1bmN0aW9uICgpIHtcbiAgZnVuY3Rpb24gUG9zaXRpb24obGluZSwgY29sKSB7XG4gICAgX2NsYXNzQ2FsbENoZWNrKHRoaXMsIFBvc2l0aW9uKTtcblxuICAgIHRoaXMubGluZSA9IGxpbmU7XG4gICAgdGhpcy5jb2x1bW4gPSBjb2w7XG4gIH1cblxuICBQb3NpdGlvbi5wcm90b3R5cGUub2Zmc2V0ID0gZnVuY3Rpb24gb2Zmc2V0KG4pIHtcbiAgICByZXR1cm4gbmV3IFBvc2l0aW9uKHRoaXMubGluZSwgdGhpcy5jb2x1bW4gKyBuKTtcbiAgfTtcblxuICByZXR1cm4gUG9zaXRpb247XG59KSgpO1xuXG52YXIgU291cmNlTG9jYXRpb24gPSBleHBvcnRzLlNvdXJjZUxvY2F0aW9uID0gZnVuY3Rpb24gU291cmNlTG9jYXRpb24ocCwgc3RhcnQsIGVuZCkge1xuICBfY2xhc3NDYWxsQ2hlY2sodGhpcywgU291cmNlTG9jYXRpb24pO1xuXG4gIHRoaXMuc3RhcnQgPSBzdGFydDtcbiAgdGhpcy5lbmQgPSBlbmQ7XG4gIGlmIChwLnNvdXJjZUZpbGUgIT09IG51bGwpIHRoaXMuc291cmNlID0gcC5zb3VyY2VGaWxlO1xufTtcblxuZnVuY3Rpb24gZ2V0TGluZUluZm8oaW5wdXQsIG9mZnNldCkge1xuICBmb3IgKHZhciBsaW5lID0gMSwgY3VyID0gMDs7KSB7XG4gICAgbGluZUJyZWFrRy5sYXN0SW5kZXggPSBjdXI7XG4gICAgdmFyIG1hdGNoID0gbGluZUJyZWFrRy5leGVjKGlucHV0KTtcbiAgICBpZiAobWF0Y2ggJiYgbWF0Y2guaW5kZXggPCBvZmZzZXQpIHtcbiAgICAgICsrbGluZTtcbiAgICAgIGN1ciA9IG1hdGNoLmluZGV4ICsgbWF0Y2hbMF0ubGVuZ3RoO1xuICAgIH0gZWxzZSB7XG4gICAgICByZXR1cm4gbmV3IFBvc2l0aW9uKGxpbmUsIG9mZnNldCAtIGN1cik7XG4gICAgfVxuICB9XG59XG5cbnZhciBwcCA9IFBhcnNlci5wcm90b3R5cGU7XG5cbi8vIFRoaXMgZnVuY3Rpb24gaXMgdXNlZCB0byByYWlzZSBleGNlcHRpb25zIG9uIHBhcnNlIGVycm9ycy4gSXRcbi8vIHRha2VzIGFuIG9mZnNldCBpbnRlZ2VyIChpbnRvIHRoZSBjdXJyZW50IGBpbnB1dGApIHRvIGluZGljYXRlXG4vLyB0aGUgbG9jYXRpb24gb2YgdGhlIGVycm9yLCBhdHRhY2hlcyB0aGUgcG9zaXRpb24gdG8gdGhlIGVuZFxuLy8gb2YgdGhlIGVycm9yIG1lc3NhZ2UsIGFuZCB0aGVuIHJhaXNlcyBhIGBTeW50YXhFcnJvcmAgd2l0aCB0aGF0XG4vLyBtZXNzYWdlLlxuXG5wcC5yYWlzZSA9IGZ1bmN0aW9uIChwb3MsIG1lc3NhZ2UpIHtcbiAgdmFyIGxvYyA9IGdldExpbmVJbmZvKHRoaXMuaW5wdXQsIHBvcyk7XG4gIG1lc3NhZ2UgKz0gXCIgKFwiICsgbG9jLmxpbmUgKyBcIjpcIiArIGxvYy5jb2x1bW4gKyBcIilcIjtcbiAgdmFyIGVyciA9IG5ldyBTeW50YXhFcnJvcihtZXNzYWdlKTtcbiAgZXJyLnBvcyA9IHBvcztlcnIubG9jID0gbG9jO2Vyci5yYWlzZWRBdCA9IHRoaXMucG9zO1xuICB0aHJvdyBlcnI7XG59O1xuXG5wcC5jdXJQb3NpdGlvbiA9IGZ1bmN0aW9uICgpIHtcbiAgcmV0dXJuIG5ldyBQb3NpdGlvbih0aGlzLmN1ckxpbmUsIHRoaXMucG9zIC0gdGhpcy5saW5lU3RhcnQpO1xufTtcblxucHAubWFya1Bvc2l0aW9uID0gZnVuY3Rpb24gKCkge1xuICByZXR1cm4gdGhpcy5vcHRpb25zLmxvY2F0aW9ucyA/IFt0aGlzLnN0YXJ0LCB0aGlzLnN0YXJ0TG9jXSA6IHRoaXMuc3RhcnQ7XG59O1xuXG59LHtcIi4vc3RhdGVcIjoxMyxcIi4vd2hpdGVzcGFjZVwiOjE5LFwidXRpbFwiOjV9XSw5OltmdW5jdGlvbihfZGVyZXFfLG1vZHVsZSxleHBvcnRzKXtcblwidXNlIHN0cmljdFwiO1xuXG52YXIgdHQgPSBfZGVyZXFfKFwiLi90b2tlbnR5cGVcIikudHlwZXM7XG5cbnZhciBQYXJzZXIgPSBfZGVyZXFfKFwiLi9zdGF0ZVwiKS5QYXJzZXI7XG5cbnZhciByZXNlcnZlZFdvcmRzID0gX2RlcmVxXyhcIi4vaWRlbnRpZmllclwiKS5yZXNlcnZlZFdvcmRzO1xuXG52YXIgaGFzID0gX2RlcmVxXyhcIi4vdXRpbFwiKS5oYXM7XG5cbnZhciBwcCA9IFBhcnNlci5wcm90b3R5cGU7XG5cbi8vIENvbnZlcnQgZXhpc3RpbmcgZXhwcmVzc2lvbiBhdG9tIHRvIGFzc2lnbmFibGUgcGF0dGVyblxuLy8gaWYgcG9zc2libGUuXG5cbnBwLnRvQXNzaWduYWJsZSA9IGZ1bmN0aW9uIChub2RlLCBpc0JpbmRpbmcpIHtcbiAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2ICYmIG5vZGUpIHtcbiAgICBzd2l0Y2ggKG5vZGUudHlwZSkge1xuICAgICAgY2FzZSBcIklkZW50aWZpZXJcIjpcbiAgICAgIGNhc2UgXCJPYmplY3RQYXR0ZXJuXCI6XG4gICAgICBjYXNlIFwiQXJyYXlQYXR0ZXJuXCI6XG4gICAgICBjYXNlIFwiQXNzaWdubWVudFBhdHRlcm5cIjpcbiAgICAgICAgYnJlYWs7XG5cbiAgICAgIGNhc2UgXCJPYmplY3RFeHByZXNzaW9uXCI6XG4gICAgICAgIG5vZGUudHlwZSA9IFwiT2JqZWN0UGF0dGVyblwiO1xuICAgICAgICBmb3IgKHZhciBpID0gMDsgaSA8IG5vZGUucHJvcGVydGllcy5sZW5ndGg7IGkrKykge1xuICAgICAgICAgIHZhciBwcm9wID0gbm9kZS5wcm9wZXJ0aWVzW2ldO1xuICAgICAgICAgIGlmIChwcm9wLmtpbmQgIT09IFwiaW5pdFwiKSB0aGlzLnJhaXNlKHByb3Aua2V5LnN0YXJ0LCBcIk9iamVjdCBwYXR0ZXJuIGNhbid0IGNvbnRhaW4gZ2V0dGVyIG9yIHNldHRlclwiKTtcbiAgICAgICAgICB0aGlzLnRvQXNzaWduYWJsZShwcm9wLnZhbHVlLCBpc0JpbmRpbmcpO1xuICAgICAgICB9XG4gICAgICAgIGJyZWFrO1xuXG4gICAgICBjYXNlIFwiQXJyYXlFeHByZXNzaW9uXCI6XG4gICAgICAgIG5vZGUudHlwZSA9IFwiQXJyYXlQYXR0ZXJuXCI7XG4gICAgICAgIHRoaXMudG9Bc3NpZ25hYmxlTGlzdChub2RlLmVsZW1lbnRzLCBpc0JpbmRpbmcpO1xuICAgICAgICBicmVhaztcblxuICAgICAgY2FzZSBcIkFzc2lnbm1lbnRFeHByZXNzaW9uXCI6XG4gICAgICAgIGlmIChub2RlLm9wZXJhdG9yID09PSBcIj1cIikge1xuICAgICAgICAgIG5vZGUudHlwZSA9IFwiQXNzaWdubWVudFBhdHRlcm5cIjtcbiAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICB0aGlzLnJhaXNlKG5vZGUubGVmdC5lbmQsIFwiT25seSAnPScgb3BlcmF0b3IgY2FuIGJlIHVzZWQgZm9yIHNwZWNpZnlpbmcgZGVmYXVsdCB2YWx1ZS5cIik7XG4gICAgICAgIH1cbiAgICAgICAgYnJlYWs7XG5cbiAgICAgIGNhc2UgXCJQYXJlbnRoZXNpemVkRXhwcmVzc2lvblwiOlxuICAgICAgICBub2RlLmV4cHJlc3Npb24gPSB0aGlzLnRvQXNzaWduYWJsZShub2RlLmV4cHJlc3Npb24sIGlzQmluZGluZyk7XG4gICAgICAgIGJyZWFrO1xuXG4gICAgICBjYXNlIFwiTWVtYmVyRXhwcmVzc2lvblwiOlxuICAgICAgICBpZiAoIWlzQmluZGluZykgYnJlYWs7XG5cbiAgICAgIGRlZmF1bHQ6XG4gICAgICAgIHRoaXMucmFpc2Uobm9kZS5zdGFydCwgXCJBc3NpZ25pbmcgdG8gcnZhbHVlXCIpO1xuICAgIH1cbiAgfVxuICByZXR1cm4gbm9kZTtcbn07XG5cbi8vIENvbnZlcnQgbGlzdCBvZiBleHByZXNzaW9uIGF0b21zIHRvIGJpbmRpbmcgbGlzdC5cblxucHAudG9Bc3NpZ25hYmxlTGlzdCA9IGZ1bmN0aW9uIChleHByTGlzdCwgaXNCaW5kaW5nKSB7XG4gIHZhciBlbmQgPSBleHByTGlzdC5sZW5ndGg7XG4gIGlmIChlbmQpIHtcbiAgICB2YXIgbGFzdCA9IGV4cHJMaXN0W2VuZCAtIDFdO1xuICAgIGlmIChsYXN0ICYmIGxhc3QudHlwZSA9PSBcIlJlc3RFbGVtZW50XCIpIHtcbiAgICAgIC0tZW5kO1xuICAgIH0gZWxzZSBpZiAobGFzdCAmJiBsYXN0LnR5cGUgPT0gXCJTcHJlYWRFbGVtZW50XCIpIHtcbiAgICAgIGxhc3QudHlwZSA9IFwiUmVzdEVsZW1lbnRcIjtcbiAgICAgIHZhciBhcmcgPSBsYXN0LmFyZ3VtZW50O1xuICAgICAgdGhpcy50b0Fzc2lnbmFibGUoYXJnLCBpc0JpbmRpbmcpO1xuICAgICAgaWYgKGFyZy50eXBlICE9PSBcIklkZW50aWZpZXJcIiAmJiBhcmcudHlwZSAhPT0gXCJNZW1iZXJFeHByZXNzaW9uXCIgJiYgYXJnLnR5cGUgIT09IFwiQXJyYXlQYXR0ZXJuXCIpIHRoaXMudW5leHBlY3RlZChhcmcuc3RhcnQpO1xuICAgICAgLS1lbmQ7XG4gICAgfVxuICB9XG4gIGZvciAodmFyIGkgPSAwOyBpIDwgZW5kOyBpKyspIHtcbiAgICB2YXIgZWx0ID0gZXhwckxpc3RbaV07XG4gICAgaWYgKGVsdCkgdGhpcy50b0Fzc2lnbmFibGUoZWx0LCBpc0JpbmRpbmcpO1xuICB9XG4gIHJldHVybiBleHByTGlzdDtcbn07XG5cbi8vIFBhcnNlcyBzcHJlYWQgZWxlbWVudC5cblxucHAucGFyc2VTcHJlYWQgPSBmdW5jdGlvbiAocmVmU2hvcnRoYW5kRGVmYXVsdFBvcykge1xuICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gIHRoaXMubmV4dCgpO1xuICBub2RlLmFyZ3VtZW50ID0gdGhpcy5wYXJzZU1heWJlQXNzaWduKHJlZlNob3J0aGFuZERlZmF1bHRQb3MpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiU3ByZWFkRWxlbWVudFwiKTtcbn07XG5cbnBwLnBhcnNlUmVzdCA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICB0aGlzLm5leHQoKTtcbiAgbm9kZS5hcmd1bWVudCA9IHRoaXMudHlwZSA9PT0gdHQubmFtZSB8fCB0aGlzLnR5cGUgPT09IHR0LmJyYWNrZXRMID8gdGhpcy5wYXJzZUJpbmRpbmdBdG9tKCkgOiB0aGlzLnVuZXhwZWN0ZWQoKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIlJlc3RFbGVtZW50XCIpO1xufTtcblxuLy8gUGFyc2VzIGx2YWx1ZSAoYXNzaWduYWJsZSkgYXRvbS5cblxucHAucGFyc2VCaW5kaW5nQXRvbSA9IGZ1bmN0aW9uICgpIHtcbiAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA8IDYpIHJldHVybiB0aGlzLnBhcnNlSWRlbnQoKTtcbiAgc3dpdGNoICh0aGlzLnR5cGUpIHtcbiAgICBjYXNlIHR0Lm5hbWU6XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZUlkZW50KCk7XG5cbiAgICBjYXNlIHR0LmJyYWNrZXRMOlxuICAgICAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICBub2RlLmVsZW1lbnRzID0gdGhpcy5wYXJzZUJpbmRpbmdMaXN0KHR0LmJyYWNrZXRSLCB0cnVlLCB0cnVlKTtcbiAgICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJBcnJheVBhdHRlcm5cIik7XG5cbiAgICBjYXNlIHR0LmJyYWNlTDpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlT2JqKHRydWUpO1xuXG4gICAgZGVmYXVsdDpcbiAgICAgIHRoaXMudW5leHBlY3RlZCgpO1xuICB9XG59O1xuXG5wcC5wYXJzZUJpbmRpbmdMaXN0ID0gZnVuY3Rpb24gKGNsb3NlLCBhbGxvd0VtcHR5LCBhbGxvd1RyYWlsaW5nQ29tbWEpIHtcbiAgdmFyIGVsdHMgPSBbXSxcbiAgICAgIGZpcnN0ID0gdHJ1ZTtcbiAgd2hpbGUgKCF0aGlzLmVhdChjbG9zZSkpIHtcbiAgICBpZiAoZmlyc3QpIGZpcnN0ID0gZmFsc2U7ZWxzZSB0aGlzLmV4cGVjdCh0dC5jb21tYSk7XG4gICAgaWYgKGFsbG93RW1wdHkgJiYgdGhpcy50eXBlID09PSB0dC5jb21tYSkge1xuICAgICAgZWx0cy5wdXNoKG51bGwpO1xuICAgIH0gZWxzZSBpZiAoYWxsb3dUcmFpbGluZ0NvbW1hICYmIHRoaXMuYWZ0ZXJUcmFpbGluZ0NvbW1hKGNsb3NlKSkge1xuICAgICAgYnJlYWs7XG4gICAgfSBlbHNlIGlmICh0aGlzLnR5cGUgPT09IHR0LmVsbGlwc2lzKSB7XG4gICAgICB2YXIgcmVzdCA9IHRoaXMucGFyc2VSZXN0KCk7XG4gICAgICB0aGlzLnBhcnNlQmluZGluZ0xpc3RJdGVtKHJlc3QpO1xuICAgICAgZWx0cy5wdXNoKHJlc3QpO1xuICAgICAgdGhpcy5leHBlY3QoY2xvc2UpO1xuICAgICAgYnJlYWs7XG4gICAgfSBlbHNlIHtcbiAgICAgIHZhciBlbGVtID0gdGhpcy5wYXJzZU1heWJlRGVmYXVsdCh0aGlzLnN0YXJ0LCB0aGlzLnN0YXJ0TG9jKTtcbiAgICAgIHRoaXMucGFyc2VCaW5kaW5nTGlzdEl0ZW0oZWxlbSk7XG4gICAgICBlbHRzLnB1c2goZWxlbSk7XG4gICAgfVxuICB9XG4gIHJldHVybiBlbHRzO1xufTtcblxucHAucGFyc2VCaW5kaW5nTGlzdEl0ZW0gPSBmdW5jdGlvbiAocGFyYW0pIHtcbiAgcmV0dXJuIHBhcmFtO1xufTtcblxuLy8gUGFyc2VzIGFzc2lnbm1lbnQgcGF0dGVybiBhcm91bmQgZ2l2ZW4gYXRvbSBpZiBwb3NzaWJsZS5cblxucHAucGFyc2VNYXliZURlZmF1bHQgPSBmdW5jdGlvbiAoc3RhcnRQb3MsIHN0YXJ0TG9jLCBsZWZ0KSB7XG4gIGlmIChBcnJheS5pc0FycmF5KHN0YXJ0UG9zKSkge1xuICAgIGlmICh0aGlzLm9wdGlvbnMubG9jYXRpb25zICYmIG5vQ2FsbHMgPT09IHVuZGVmaW5lZCkge1xuICAgICAgLy8gc2hpZnQgYXJndW1lbnRzIHRvIGxlZnQgYnkgb25lXG4gICAgICBsZWZ0ID0gc3RhcnRMb2M7XG4gICAgICAvLyBmbGF0dGVuIHN0YXJ0UG9zXG4gICAgICBzdGFydExvYyA9IHN0YXJ0UG9zWzFdO1xuICAgICAgc3RhcnRQb3MgPSBzdGFydFBvc1swXTtcbiAgICB9XG4gIH1cbiAgbGVmdCA9IGxlZnQgfHwgdGhpcy5wYXJzZUJpbmRpbmdBdG9tKCk7XG4gIGlmICghdGhpcy5lYXQodHQuZXEpKSByZXR1cm4gbGVmdDtcbiAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0UG9zLCBzdGFydExvYyk7XG4gIG5vZGUub3BlcmF0b3IgPSBcIj1cIjtcbiAgbm9kZS5sZWZ0ID0gbGVmdDtcbiAgbm9kZS5yaWdodCA9IHRoaXMucGFyc2VNYXliZUFzc2lnbigpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiQXNzaWdubWVudFBhdHRlcm5cIik7XG59O1xuXG4vLyBWZXJpZnkgdGhhdCBhIG5vZGUgaXMgYW4gbHZhbCDigJQgc29tZXRoaW5nIHRoYXQgY2FuIGJlIGFzc2lnbmVkXG4vLyB0by5cblxucHAuY2hlY2tMVmFsID0gZnVuY3Rpb24gKGV4cHIsIGlzQmluZGluZywgY2hlY2tDbGFzaGVzKSB7XG4gIHN3aXRjaCAoZXhwci50eXBlKSB7XG4gICAgY2FzZSBcIklkZW50aWZpZXJcIjpcbiAgICAgIGlmICh0aGlzLnN0cmljdCAmJiAocmVzZXJ2ZWRXb3Jkcy5zdHJpY3RCaW5kKGV4cHIubmFtZSkgfHwgcmVzZXJ2ZWRXb3Jkcy5zdHJpY3QoZXhwci5uYW1lKSkpIHRoaXMucmFpc2UoZXhwci5zdGFydCwgKGlzQmluZGluZyA/IFwiQmluZGluZyBcIiA6IFwiQXNzaWduaW5nIHRvIFwiKSArIGV4cHIubmFtZSArIFwiIGluIHN0cmljdCBtb2RlXCIpO1xuICAgICAgaWYgKGNoZWNrQ2xhc2hlcykge1xuICAgICAgICBpZiAoaGFzKGNoZWNrQ2xhc2hlcywgZXhwci5uYW1lKSkgdGhpcy5yYWlzZShleHByLnN0YXJ0LCBcIkFyZ3VtZW50IG5hbWUgY2xhc2ggaW4gc3RyaWN0IG1vZGVcIik7XG4gICAgICAgIGNoZWNrQ2xhc2hlc1tleHByLm5hbWVdID0gdHJ1ZTtcbiAgICAgIH1cbiAgICAgIGJyZWFrO1xuXG4gICAgY2FzZSBcIk1lbWJlckV4cHJlc3Npb25cIjpcbiAgICAgIGlmIChpc0JpbmRpbmcpIHRoaXMucmFpc2UoZXhwci5zdGFydCwgKGlzQmluZGluZyA/IFwiQmluZGluZ1wiIDogXCJBc3NpZ25pbmcgdG9cIikgKyBcIiBtZW1iZXIgZXhwcmVzc2lvblwiKTtcbiAgICAgIGJyZWFrO1xuXG4gICAgY2FzZSBcIk9iamVjdFBhdHRlcm5cIjpcbiAgICAgIGZvciAodmFyIGkgPSAwOyBpIDwgZXhwci5wcm9wZXJ0aWVzLmxlbmd0aDsgaSsrKSB7XG4gICAgICAgIHRoaXMuY2hlY2tMVmFsKGV4cHIucHJvcGVydGllc1tpXS52YWx1ZSwgaXNCaW5kaW5nLCBjaGVja0NsYXNoZXMpO1xuICAgICAgfWJyZWFrO1xuXG4gICAgY2FzZSBcIkFycmF5UGF0dGVyblwiOlxuICAgICAgZm9yICh2YXIgaSA9IDA7IGkgPCBleHByLmVsZW1lbnRzLmxlbmd0aDsgaSsrKSB7XG4gICAgICAgIHZhciBlbGVtID0gZXhwci5lbGVtZW50c1tpXTtcbiAgICAgICAgaWYgKGVsZW0pIHRoaXMuY2hlY2tMVmFsKGVsZW0sIGlzQmluZGluZywgY2hlY2tDbGFzaGVzKTtcbiAgICAgIH1cbiAgICAgIGJyZWFrO1xuXG4gICAgY2FzZSBcIkFzc2lnbm1lbnRQYXR0ZXJuXCI6XG4gICAgICB0aGlzLmNoZWNrTFZhbChleHByLmxlZnQsIGlzQmluZGluZywgY2hlY2tDbGFzaGVzKTtcbiAgICAgIGJyZWFrO1xuXG4gICAgY2FzZSBcIlJlc3RFbGVtZW50XCI6XG4gICAgICB0aGlzLmNoZWNrTFZhbChleHByLmFyZ3VtZW50LCBpc0JpbmRpbmcsIGNoZWNrQ2xhc2hlcyk7XG4gICAgICBicmVhaztcblxuICAgIGNhc2UgXCJQYXJlbnRoZXNpemVkRXhwcmVzc2lvblwiOlxuICAgICAgdGhpcy5jaGVja0xWYWwoZXhwci5leHByZXNzaW9uLCBpc0JpbmRpbmcsIGNoZWNrQ2xhc2hlcyk7XG4gICAgICBicmVhaztcblxuICAgIGRlZmF1bHQ6XG4gICAgICB0aGlzLnJhaXNlKGV4cHIuc3RhcnQsIChpc0JpbmRpbmcgPyBcIkJpbmRpbmdcIiA6IFwiQXNzaWduaW5nIHRvXCIpICsgXCIgcnZhbHVlXCIpO1xuICB9XG59O1xuXG59LHtcIi4vaWRlbnRpZmllclwiOjcsXCIuL3N0YXRlXCI6MTMsXCIuL3Rva2VudHlwZVwiOjE3LFwiLi91dGlsXCI6MTh9XSwxMDpbZnVuY3Rpb24oX2RlcmVxXyxtb2R1bGUsZXhwb3J0cyl7XG5cInVzZSBzdHJpY3RcIjtcblxudmFyIF9jbGFzc0NhbGxDaGVjayA9IGZ1bmN0aW9uIChpbnN0YW5jZSwgQ29uc3RydWN0b3IpIHsgaWYgKCEoaW5zdGFuY2UgaW5zdGFuY2VvZiBDb25zdHJ1Y3RvcikpIHsgdGhyb3cgbmV3IFR5cGVFcnJvcihcIkNhbm5vdCBjYWxsIGEgY2xhc3MgYXMgYSBmdW5jdGlvblwiKTsgfSB9O1xuXG5leHBvcnRzLl9fZXNNb2R1bGUgPSB0cnVlO1xuXG52YXIgUGFyc2VyID0gX2RlcmVxXyhcIi4vc3RhdGVcIikuUGFyc2VyO1xuXG52YXIgU291cmNlTG9jYXRpb24gPSBfZGVyZXFfKFwiLi9sb2NhdGlvblwiKS5Tb3VyY2VMb2NhdGlvbjtcblxuLy8gU3RhcnQgYW4gQVNUIG5vZGUsIGF0dGFjaGluZyBhIHN0YXJ0IG9mZnNldC5cblxudmFyIHBwID0gUGFyc2VyLnByb3RvdHlwZTtcblxudmFyIE5vZGUgPSBleHBvcnRzLk5vZGUgPSBmdW5jdGlvbiBOb2RlKCkge1xuICBfY2xhc3NDYWxsQ2hlY2sodGhpcywgTm9kZSk7XG59O1xuXG5wcC5zdGFydE5vZGUgPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBub2RlID0gbmV3IE5vZGUoKTtcbiAgbm9kZS5zdGFydCA9IHRoaXMuc3RhcnQ7XG4gIGlmICh0aGlzLm9wdGlvbnMubG9jYXRpb25zKSBub2RlLmxvYyA9IG5ldyBTb3VyY2VMb2NhdGlvbih0aGlzLCB0aGlzLnN0YXJ0TG9jKTtcbiAgaWYgKHRoaXMub3B0aW9ucy5kaXJlY3RTb3VyY2VGaWxlKSBub2RlLnNvdXJjZUZpbGUgPSB0aGlzLm9wdGlvbnMuZGlyZWN0U291cmNlRmlsZTtcbiAgaWYgKHRoaXMub3B0aW9ucy5yYW5nZXMpIG5vZGUucmFuZ2UgPSBbdGhpcy5zdGFydCwgMF07XG4gIHJldHVybiBub2RlO1xufTtcblxucHAuc3RhcnROb2RlQXQgPSBmdW5jdGlvbiAocG9zLCBsb2MpIHtcbiAgdmFyIG5vZGUgPSBuZXcgTm9kZSgpO1xuICBpZiAoQXJyYXkuaXNBcnJheShwb3MpKSB7XG4gICAgaWYgKHRoaXMub3B0aW9ucy5sb2NhdGlvbnMgJiYgbG9jID09PSB1bmRlZmluZWQpIHtcbiAgICAgIC8vIGZsYXR0ZW4gcG9zXG4gICAgICBsb2MgPSBwb3NbMV07XG4gICAgICBwb3MgPSBwb3NbMF07XG4gICAgfVxuICB9XG4gIG5vZGUuc3RhcnQgPSBwb3M7XG4gIGlmICh0aGlzLm9wdGlvbnMubG9jYXRpb25zKSBub2RlLmxvYyA9IG5ldyBTb3VyY2VMb2NhdGlvbih0aGlzLCBsb2MpO1xuICBpZiAodGhpcy5vcHRpb25zLmRpcmVjdFNvdXJjZUZpbGUpIG5vZGUuc291cmNlRmlsZSA9IHRoaXMub3B0aW9ucy5kaXJlY3RTb3VyY2VGaWxlO1xuICBpZiAodGhpcy5vcHRpb25zLnJhbmdlcykgbm9kZS5yYW5nZSA9IFtwb3MsIDBdO1xuICByZXR1cm4gbm9kZTtcbn07XG5cbi8vIEZpbmlzaCBhbiBBU1Qgbm9kZSwgYWRkaW5nIGB0eXBlYCBhbmQgYGVuZGAgcHJvcGVydGllcy5cblxucHAuZmluaXNoTm9kZSA9IGZ1bmN0aW9uIChub2RlLCB0eXBlKSB7XG4gIG5vZGUudHlwZSA9IHR5cGU7XG4gIG5vZGUuZW5kID0gdGhpcy5sYXN0VG9rRW5kO1xuICBpZiAodGhpcy5vcHRpb25zLmxvY2F0aW9ucykgbm9kZS5sb2MuZW5kID0gdGhpcy5sYXN0VG9rRW5kTG9jO1xuICBpZiAodGhpcy5vcHRpb25zLnJhbmdlcykgbm9kZS5yYW5nZVsxXSA9IHRoaXMubGFzdFRva0VuZDtcbiAgcmV0dXJuIG5vZGU7XG59O1xuXG4vLyBGaW5pc2ggbm9kZSBhdCBnaXZlbiBwb3NpdGlvblxuXG5wcC5maW5pc2hOb2RlQXQgPSBmdW5jdGlvbiAobm9kZSwgdHlwZSwgcG9zLCBsb2MpIHtcbiAgbm9kZS50eXBlID0gdHlwZTtcbiAgaWYgKEFycmF5LmlzQXJyYXkocG9zKSkge1xuICAgIGlmICh0aGlzLm9wdGlvbnMubG9jYXRpb25zICYmIGxvYyA9PT0gdW5kZWZpbmVkKSB7XG4gICAgICAvLyBmbGF0dGVuIHBvc1xuICAgICAgbG9jID0gcG9zWzFdO1xuICAgICAgcG9zID0gcG9zWzBdO1xuICAgIH1cbiAgfVxuICBub2RlLmVuZCA9IHBvcztcbiAgaWYgKHRoaXMub3B0aW9ucy5sb2NhdGlvbnMpIG5vZGUubG9jLmVuZCA9IGxvYztcbiAgaWYgKHRoaXMub3B0aW9ucy5yYW5nZXMpIG5vZGUucmFuZ2VbMV0gPSBwb3M7XG4gIHJldHVybiBub2RlO1xufTtcblxufSx7XCIuL2xvY2F0aW9uXCI6OCxcIi4vc3RhdGVcIjoxM31dLDExOltmdW5jdGlvbihfZGVyZXFfLG1vZHVsZSxleHBvcnRzKXtcblxuXG4vLyBJbnRlcnByZXQgYW5kIGRlZmF1bHQgYW4gb3B0aW9ucyBvYmplY3RcblxuXCJ1c2Ugc3RyaWN0XCI7XG5cbmV4cG9ydHMuZ2V0T3B0aW9ucyA9IGdldE9wdGlvbnM7XG5leHBvcnRzLl9fZXNNb2R1bGUgPSB0cnVlO1xuXG52YXIgX3V0aWwgPSBfZGVyZXFfKFwiLi91dGlsXCIpO1xuXG52YXIgaGFzID0gX3V0aWwuaGFzO1xudmFyIGlzQXJyYXkgPSBfdXRpbC5pc0FycmF5O1xuXG52YXIgU291cmNlTG9jYXRpb24gPSBfZGVyZXFfKFwiLi9sb2NhdGlvblwiKS5Tb3VyY2VMb2NhdGlvbjtcblxuLy8gQSBzZWNvbmQgb3B0aW9uYWwgYXJndW1lbnQgY2FuIGJlIGdpdmVuIHRvIGZ1cnRoZXIgY29uZmlndXJlXG4vLyB0aGUgcGFyc2VyIHByb2Nlc3MuIFRoZXNlIG9wdGlvbnMgYXJlIHJlY29nbml6ZWQ6XG5cbnZhciBkZWZhdWx0T3B0aW9ucyA9IHtcbiAgLy8gYGVjbWFWZXJzaW9uYCBpbmRpY2F0ZXMgdGhlIEVDTUFTY3JpcHQgdmVyc2lvbiB0byBwYXJzZS4gTXVzdFxuICAvLyBiZSBlaXRoZXIgMywgb3IgNSwgb3IgNi4gVGhpcyBpbmZsdWVuY2VzIHN1cHBvcnQgZm9yIHN0cmljdFxuICAvLyBtb2RlLCB0aGUgc2V0IG9mIHJlc2VydmVkIHdvcmRzLCBzdXBwb3J0IGZvciBnZXR0ZXJzIGFuZFxuICAvLyBzZXR0ZXJzIGFuZCBvdGhlciBmZWF0dXJlcy5cbiAgZWNtYVZlcnNpb246IDUsXG4gIC8vIFNvdXJjZSB0eXBlIChcInNjcmlwdFwiIG9yIFwibW9kdWxlXCIpIGZvciBkaWZmZXJlbnQgc2VtYW50aWNzXG4gIHNvdXJjZVR5cGU6IFwic2NyaXB0XCIsXG4gIC8vIGBvbkluc2VydGVkU2VtaWNvbG9uYCBjYW4gYmUgYSBjYWxsYmFjayB0aGF0IHdpbGwgYmUgY2FsbGVkXG4gIC8vIHdoZW4gYSBzZW1pY29sb24gaXMgYXV0b21hdGljYWxseSBpbnNlcnRlZC4gSXQgd2lsbCBiZSBwYXNzZWRcbiAgLy8gdGggcG9zaXRpb24gb2YgdGhlIGNvbW1hIGFzIGFuIG9mZnNldCwgYW5kIGlmIGBsb2NhdGlvbnNgIGlzXG4gIC8vIGVuYWJsZWQsIGl0IGlzIGdpdmVuIHRoZSBsb2NhdGlvbiBhcyBhIGB7bGluZSwgY29sdW1ufWAgb2JqZWN0XG4gIC8vIGFzIHNlY29uZCBhcmd1bWVudC5cbiAgb25JbnNlcnRlZFNlbWljb2xvbjogbnVsbCxcbiAgLy8gYG9uVHJhaWxpbmdDb21tYWAgaXMgc2ltaWxhciB0byBgb25JbnNlcnRlZFNlbWljb2xvbmAsIGJ1dCBmb3JcbiAgLy8gdHJhaWxpbmcgY29tbWFzLlxuICBvblRyYWlsaW5nQ29tbWE6IG51bGwsXG4gIC8vIEJ5IGRlZmF1bHQsIHJlc2VydmVkIHdvcmRzIGFyZSBub3QgZW5mb3JjZWQuIERpc2FibGVcbiAgLy8gYGFsbG93UmVzZXJ2ZWRgIHRvIGVuZm9yY2UgdGhlbS4gV2hlbiB0aGlzIG9wdGlvbiBoYXMgdGhlXG4gIC8vIHZhbHVlIFwibmV2ZXJcIiwgcmVzZXJ2ZWQgd29yZHMgYW5kIGtleXdvcmRzIGNhbiBhbHNvIG5vdCBiZVxuICAvLyB1c2VkIGFzIHByb3BlcnR5IG5hbWVzLlxuICBhbGxvd1Jlc2VydmVkOiB0cnVlLFxuICAvLyBXaGVuIGVuYWJsZWQsIGEgcmV0dXJuIGF0IHRoZSB0b3AgbGV2ZWwgaXMgbm90IGNvbnNpZGVyZWQgYW5cbiAgLy8gZXJyb3IuXG4gIGFsbG93UmV0dXJuT3V0c2lkZUZ1bmN0aW9uOiBmYWxzZSxcbiAgLy8gV2hlbiBlbmFibGVkLCBpbXBvcnQvZXhwb3J0IHN0YXRlbWVudHMgYXJlIG5vdCBjb25zdHJhaW5lZCB0b1xuICAvLyBhcHBlYXJpbmcgYXQgdGhlIHRvcCBvZiB0aGUgcHJvZ3JhbS5cbiAgYWxsb3dJbXBvcnRFeHBvcnRFdmVyeXdoZXJlOiBmYWxzZSxcbiAgLy8gV2hlbiBlbmFibGVkLCBoYXNoYmFuZyBkaXJlY3RpdmUgaW4gdGhlIGJlZ2lubmluZyBvZiBmaWxlXG4gIC8vIGlzIGFsbG93ZWQgYW5kIHRyZWF0ZWQgYXMgYSBsaW5lIGNvbW1lbnQuXG4gIGFsbG93SGFzaEJhbmc6IGZhbHNlLFxuICAvLyBXaGVuIGBsb2NhdGlvbnNgIGlzIG9uLCBgbG9jYCBwcm9wZXJ0aWVzIGhvbGRpbmcgb2JqZWN0cyB3aXRoXG4gIC8vIGBzdGFydGAgYW5kIGBlbmRgIHByb3BlcnRpZXMgaW4gYHtsaW5lLCBjb2x1bW59YCBmb3JtICh3aXRoXG4gIC8vIGxpbmUgYmVpbmcgMS1iYXNlZCBhbmQgY29sdW1uIDAtYmFzZWQpIHdpbGwgYmUgYXR0YWNoZWQgdG8gdGhlXG4gIC8vIG5vZGVzLlxuICBsb2NhdGlvbnM6IGZhbHNlLFxuICAvLyBBIGZ1bmN0aW9uIGNhbiBiZSBwYXNzZWQgYXMgYG9uVG9rZW5gIG9wdGlvbiwgd2hpY2ggd2lsbFxuICAvLyBjYXVzZSBBY29ybiB0byBjYWxsIHRoYXQgZnVuY3Rpb24gd2l0aCBvYmplY3QgaW4gdGhlIHNhbWVcbiAgLy8gZm9ybWF0IGFzIHRva2VuaXplKCkgcmV0dXJucy4gTm90ZSB0aGF0IHlvdSBhcmUgbm90XG4gIC8vIGFsbG93ZWQgdG8gY2FsbCB0aGUgcGFyc2VyIGZyb20gdGhlIGNhbGxiYWNr4oCUdGhhdCB3aWxsXG4gIC8vIGNvcnJ1cHQgaXRzIGludGVybmFsIHN0YXRlLlxuICBvblRva2VuOiBudWxsLFxuICAvLyBBIGZ1bmN0aW9uIGNhbiBiZSBwYXNzZWQgYXMgYG9uQ29tbWVudGAgb3B0aW9uLCB3aGljaCB3aWxsXG4gIC8vIGNhdXNlIEFjb3JuIHRvIGNhbGwgdGhhdCBmdW5jdGlvbiB3aXRoIGAoYmxvY2ssIHRleHQsIHN0YXJ0LFxuICAvLyBlbmQpYCBwYXJhbWV0ZXJzIHdoZW5ldmVyIGEgY29tbWVudCBpcyBza2lwcGVkLiBgYmxvY2tgIGlzIGFcbiAgLy8gYm9vbGVhbiBpbmRpY2F0aW5nIHdoZXRoZXIgdGhpcyBpcyBhIGJsb2NrIChgLyogKi9gKSBjb21tZW50LFxuICAvLyBgdGV4dGAgaXMgdGhlIGNvbnRlbnQgb2YgdGhlIGNvbW1lbnQsIGFuZCBgc3RhcnRgIGFuZCBgZW5kYCBhcmVcbiAgLy8gY2hhcmFjdGVyIG9mZnNldHMgdGhhdCBkZW5vdGUgdGhlIHN0YXJ0IGFuZCBlbmQgb2YgdGhlIGNvbW1lbnQuXG4gIC8vIFdoZW4gdGhlIGBsb2NhdGlvbnNgIG9wdGlvbiBpcyBvbiwgdHdvIG1vcmUgcGFyYW1ldGVycyBhcmVcbiAgLy8gcGFzc2VkLCB0aGUgZnVsbCBge2xpbmUsIGNvbHVtbn1gIGxvY2F0aW9ucyBvZiB0aGUgc3RhcnQgYW5kXG4gIC8vIGVuZCBvZiB0aGUgY29tbWVudHMuIE5vdGUgdGhhdCB5b3UgYXJlIG5vdCBhbGxvd2VkIHRvIGNhbGwgdGhlXG4gIC8vIHBhcnNlciBmcm9tIHRoZSBjYWxsYmFja+KAlHRoYXQgd2lsbCBjb3JydXB0IGl0cyBpbnRlcm5hbCBzdGF0ZS5cbiAgb25Db21tZW50OiBudWxsLFxuICAvLyBOb2RlcyBoYXZlIHRoZWlyIHN0YXJ0IGFuZCBlbmQgY2hhcmFjdGVycyBvZmZzZXRzIHJlY29yZGVkIGluXG4gIC8vIGBzdGFydGAgYW5kIGBlbmRgIHByb3BlcnRpZXMgKGRpcmVjdGx5IG9uIHRoZSBub2RlLCByYXRoZXIgdGhhblxuICAvLyB0aGUgYGxvY2Agb2JqZWN0LCB3aGljaCBob2xkcyBsaW5lL2NvbHVtbiBkYXRhLiBUbyBhbHNvIGFkZCBhXG4gIC8vIFtzZW1pLXN0YW5kYXJkaXplZF1bcmFuZ2VdIGByYW5nZWAgcHJvcGVydHkgaG9sZGluZyBhIGBbc3RhcnQsXG4gIC8vIGVuZF1gIGFycmF5IHdpdGggdGhlIHNhbWUgbnVtYmVycywgc2V0IHRoZSBgcmFuZ2VzYCBvcHRpb24gdG9cbiAgLy8gYHRydWVgLlxuICAvL1xuICAvLyBbcmFuZ2VdOiBodHRwczovL2J1Z3ppbGxhLm1vemlsbGEub3JnL3Nob3dfYnVnLmNnaT9pZD03NDU2NzhcbiAgcmFuZ2VzOiBmYWxzZSxcbiAgLy8gSXQgaXMgcG9zc2libGUgdG8gcGFyc2UgbXVsdGlwbGUgZmlsZXMgaW50byBhIHNpbmdsZSBBU1QgYnlcbiAgLy8gcGFzc2luZyB0aGUgdHJlZSBwcm9kdWNlZCBieSBwYXJzaW5nIHRoZSBmaXJzdCBmaWxlIGFzXG4gIC8vIGBwcm9ncmFtYCBvcHRpb24gaW4gc3Vic2VxdWVudCBwYXJzZXMuIFRoaXMgd2lsbCBhZGQgdGhlXG4gIC8vIHRvcGxldmVsIGZvcm1zIG9mIHRoZSBwYXJzZWQgZmlsZSB0byB0aGUgYFByb2dyYW1gICh0b3ApIG5vZGVcbiAgLy8gb2YgYW4gZXhpc3RpbmcgcGFyc2UgdHJlZS5cbiAgcHJvZ3JhbTogbnVsbCxcbiAgLy8gV2hlbiBgbG9jYXRpb25zYCBpcyBvbiwgeW91IGNhbiBwYXNzIHRoaXMgdG8gcmVjb3JkIHRoZSBzb3VyY2VcbiAgLy8gZmlsZSBpbiBldmVyeSBub2RlJ3MgYGxvY2Agb2JqZWN0LlxuICBzb3VyY2VGaWxlOiBudWxsLFxuICAvLyBUaGlzIHZhbHVlLCBpZiBnaXZlbiwgaXMgc3RvcmVkIGluIGV2ZXJ5IG5vZGUsIHdoZXRoZXJcbiAgLy8gYGxvY2F0aW9uc2AgaXMgb24gb3Igb2ZmLlxuICBkaXJlY3RTb3VyY2VGaWxlOiBudWxsLFxuICAvLyBXaGVuIGVuYWJsZWQsIHBhcmVudGhlc2l6ZWQgZXhwcmVzc2lvbnMgYXJlIHJlcHJlc2VudGVkIGJ5XG4gIC8vIChub24tc3RhbmRhcmQpIFBhcmVudGhlc2l6ZWRFeHByZXNzaW9uIG5vZGVzXG4gIHByZXNlcnZlUGFyZW5zOiBmYWxzZSxcbiAgcGx1Z2luczoge31cbn07ZXhwb3J0cy5kZWZhdWx0T3B0aW9ucyA9IGRlZmF1bHRPcHRpb25zO1xuXG5mdW5jdGlvbiBnZXRPcHRpb25zKG9wdHMpIHtcbiAgdmFyIG9wdGlvbnMgPSB7fTtcbiAgZm9yICh2YXIgb3B0IGluIGRlZmF1bHRPcHRpb25zKSB7XG4gICAgb3B0aW9uc1tvcHRdID0gb3B0cyAmJiBoYXMob3B0cywgb3B0KSA/IG9wdHNbb3B0XSA6IGRlZmF1bHRPcHRpb25zW29wdF07XG4gIH1pZiAoaXNBcnJheShvcHRpb25zLm9uVG9rZW4pKSB7XG4gICAgKGZ1bmN0aW9uICgpIHtcbiAgICAgIHZhciB0b2tlbnMgPSBvcHRpb25zLm9uVG9rZW47XG4gICAgICBvcHRpb25zLm9uVG9rZW4gPSBmdW5jdGlvbiAodG9rZW4pIHtcbiAgICAgICAgcmV0dXJuIHRva2Vucy5wdXNoKHRva2VuKTtcbiAgICAgIH07XG4gICAgfSkoKTtcbiAgfVxuICBpZiAoaXNBcnJheShvcHRpb25zLm9uQ29tbWVudCkpIG9wdGlvbnMub25Db21tZW50ID0gcHVzaENvbW1lbnQob3B0aW9ucywgb3B0aW9ucy5vbkNvbW1lbnQpO1xuXG4gIHJldHVybiBvcHRpb25zO1xufVxuXG5mdW5jdGlvbiBwdXNoQ29tbWVudChvcHRpb25zLCBhcnJheSkge1xuICByZXR1cm4gZnVuY3Rpb24gKGJsb2NrLCB0ZXh0LCBzdGFydCwgZW5kLCBzdGFydExvYywgZW5kTG9jKSB7XG4gICAgdmFyIGNvbW1lbnQgPSB7XG4gICAgICB0eXBlOiBibG9jayA/IFwiQmxvY2tcIiA6IFwiTGluZVwiLFxuICAgICAgdmFsdWU6IHRleHQsXG4gICAgICBzdGFydDogc3RhcnQsXG4gICAgICBlbmQ6IGVuZFxuICAgIH07XG4gICAgaWYgKG9wdGlvbnMubG9jYXRpb25zKSBjb21tZW50LmxvYyA9IG5ldyBTb3VyY2VMb2NhdGlvbih0aGlzLCBzdGFydExvYywgZW5kTG9jKTtcbiAgICBpZiAob3B0aW9ucy5yYW5nZXMpIGNvbW1lbnQucmFuZ2UgPSBbc3RhcnQsIGVuZF07XG4gICAgYXJyYXkucHVzaChjb21tZW50KTtcbiAgfTtcbn1cblxufSx7XCIuL2xvY2F0aW9uXCI6OCxcIi4vdXRpbFwiOjE4fV0sMTI6W2Z1bmN0aW9uKF9kZXJlcV8sbW9kdWxlLGV4cG9ydHMpe1xuXCJ1c2Ugc3RyaWN0XCI7XG5cbnZhciB0dCA9IF9kZXJlcV8oXCIuL3Rva2VudHlwZVwiKS50eXBlcztcblxudmFyIFBhcnNlciA9IF9kZXJlcV8oXCIuL3N0YXRlXCIpLlBhcnNlcjtcblxudmFyIGxpbmVCcmVhayA9IF9kZXJlcV8oXCIuL3doaXRlc3BhY2VcIikubGluZUJyZWFrO1xuXG52YXIgcHAgPSBQYXJzZXIucHJvdG90eXBlO1xuXG4vLyAjIyBQYXJzZXIgdXRpbGl0aWVzXG5cbi8vIFRlc3Qgd2hldGhlciBhIHN0YXRlbWVudCBub2RlIGlzIHRoZSBzdHJpbmcgbGl0ZXJhbCBgXCJ1c2Ugc3RyaWN0XCJgLlxuXG5wcC5pc1VzZVN0cmljdCA9IGZ1bmN0aW9uIChzdG10KSB7XG4gIHJldHVybiB0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNSAmJiBzdG10LnR5cGUgPT09IFwiRXhwcmVzc2lvblN0YXRlbWVudFwiICYmIHN0bXQuZXhwcmVzc2lvbi50eXBlID09PSBcIkxpdGVyYWxcIiAmJiBzdG10LmV4cHJlc3Npb24udmFsdWUgPT09IFwidXNlIHN0cmljdFwiO1xufTtcblxuLy8gUHJlZGljYXRlIHRoYXQgdGVzdHMgd2hldGhlciB0aGUgbmV4dCB0b2tlbiBpcyBvZiB0aGUgZ2l2ZW5cbi8vIHR5cGUsIGFuZCBpZiB5ZXMsIGNvbnN1bWVzIGl0IGFzIGEgc2lkZSBlZmZlY3QuXG5cbnBwLmVhdCA9IGZ1bmN0aW9uICh0eXBlKSB7XG4gIGlmICh0aGlzLnR5cGUgPT09IHR5cGUpIHtcbiAgICB0aGlzLm5leHQoKTtcbiAgICByZXR1cm4gdHJ1ZTtcbiAgfSBlbHNlIHtcbiAgICByZXR1cm4gZmFsc2U7XG4gIH1cbn07XG5cbi8vIFRlc3RzIHdoZXRoZXIgcGFyc2VkIHRva2VuIGlzIGEgY29udGV4dHVhbCBrZXl3b3JkLlxuXG5wcC5pc0NvbnRleHR1YWwgPSBmdW5jdGlvbiAobmFtZSkge1xuICByZXR1cm4gdGhpcy50eXBlID09PSB0dC5uYW1lICYmIHRoaXMudmFsdWUgPT09IG5hbWU7XG59O1xuXG4vLyBDb25zdW1lcyBjb250ZXh0dWFsIGtleXdvcmQgaWYgcG9zc2libGUuXG5cbnBwLmVhdENvbnRleHR1YWwgPSBmdW5jdGlvbiAobmFtZSkge1xuICByZXR1cm4gdGhpcy52YWx1ZSA9PT0gbmFtZSAmJiB0aGlzLmVhdCh0dC5uYW1lKTtcbn07XG5cbi8vIEFzc2VydHMgdGhhdCBmb2xsb3dpbmcgdG9rZW4gaXMgZ2l2ZW4gY29udGV4dHVhbCBrZXl3b3JkLlxuXG5wcC5leHBlY3RDb250ZXh0dWFsID0gZnVuY3Rpb24gKG5hbWUpIHtcbiAgaWYgKCF0aGlzLmVhdENvbnRleHR1YWwobmFtZSkpIHRoaXMudW5leHBlY3RlZCgpO1xufTtcblxuLy8gVGVzdCB3aGV0aGVyIGEgc2VtaWNvbG9uIGNhbiBiZSBpbnNlcnRlZCBhdCB0aGUgY3VycmVudCBwb3NpdGlvbi5cblxucHAuY2FuSW5zZXJ0U2VtaWNvbG9uID0gZnVuY3Rpb24gKCkge1xuICByZXR1cm4gdGhpcy50eXBlID09PSB0dC5lb2YgfHwgdGhpcy50eXBlID09PSB0dC5icmFjZVIgfHwgbGluZUJyZWFrLnRlc3QodGhpcy5pbnB1dC5zbGljZSh0aGlzLmxhc3RUb2tFbmQsIHRoaXMuc3RhcnQpKTtcbn07XG5cbnBwLmluc2VydFNlbWljb2xvbiA9IGZ1bmN0aW9uICgpIHtcbiAgaWYgKHRoaXMuY2FuSW5zZXJ0U2VtaWNvbG9uKCkpIHtcbiAgICBpZiAodGhpcy5vcHRpb25zLm9uSW5zZXJ0ZWRTZW1pY29sb24pIHRoaXMub3B0aW9ucy5vbkluc2VydGVkU2VtaWNvbG9uKHRoaXMubGFzdFRva0VuZCwgdGhpcy5sYXN0VG9rRW5kTG9jKTtcbiAgICByZXR1cm4gdHJ1ZTtcbiAgfVxufTtcblxuLy8gQ29uc3VtZSBhIHNlbWljb2xvbiwgb3IsIGZhaWxpbmcgdGhhdCwgc2VlIGlmIHdlIGFyZSBhbGxvd2VkIHRvXG4vLyBwcmV0ZW5kIHRoYXQgdGhlcmUgaXMgYSBzZW1pY29sb24gYXQgdGhpcyBwb3NpdGlvbi5cblxucHAuc2VtaWNvbG9uID0gZnVuY3Rpb24gKCkge1xuICBpZiAoIXRoaXMuZWF0KHR0LnNlbWkpICYmICF0aGlzLmluc2VydFNlbWljb2xvbigpKSB0aGlzLnVuZXhwZWN0ZWQoKTtcbn07XG5cbnBwLmFmdGVyVHJhaWxpbmdDb21tYSA9IGZ1bmN0aW9uICh0b2tUeXBlKSB7XG4gIGlmICh0aGlzLnR5cGUgPT0gdG9rVHlwZSkge1xuICAgIGlmICh0aGlzLm9wdGlvbnMub25UcmFpbGluZ0NvbW1hKSB0aGlzLm9wdGlvbnMub25UcmFpbGluZ0NvbW1hKHRoaXMubGFzdFRva1N0YXJ0LCB0aGlzLmxhc3RUb2tTdGFydExvYyk7XG4gICAgdGhpcy5uZXh0KCk7XG4gICAgcmV0dXJuIHRydWU7XG4gIH1cbn07XG5cbi8vIEV4cGVjdCBhIHRva2VuIG9mIGEgZ2l2ZW4gdHlwZS4gSWYgZm91bmQsIGNvbnN1bWUgaXQsIG90aGVyd2lzZSxcbi8vIHJhaXNlIGFuIHVuZXhwZWN0ZWQgdG9rZW4gZXJyb3IuXG5cbnBwLmV4cGVjdCA9IGZ1bmN0aW9uICh0eXBlKSB7XG4gIHRoaXMuZWF0KHR5cGUpIHx8IHRoaXMudW5leHBlY3RlZCgpO1xufTtcblxuLy8gUmFpc2UgYW4gdW5leHBlY3RlZCB0b2tlbiBlcnJvci5cblxucHAudW5leHBlY3RlZCA9IGZ1bmN0aW9uIChwb3MpIHtcbiAgdGhpcy5yYWlzZShwb3MgIT0gbnVsbCA/IHBvcyA6IHRoaXMuc3RhcnQsIFwiVW5leHBlY3RlZCB0b2tlblwiKTtcbn07XG5cbn0se1wiLi9zdGF0ZVwiOjEzLFwiLi90b2tlbnR5cGVcIjoxNyxcIi4vd2hpdGVzcGFjZVwiOjE5fV0sMTM6W2Z1bmN0aW9uKF9kZXJlcV8sbW9kdWxlLGV4cG9ydHMpe1xuXCJ1c2Ugc3RyaWN0XCI7XG5cbmV4cG9ydHMuUGFyc2VyID0gUGFyc2VyO1xuZXhwb3J0cy5fX2VzTW9kdWxlID0gdHJ1ZTtcblxudmFyIF9pZGVudGlmaWVyID0gX2RlcmVxXyhcIi4vaWRlbnRpZmllclwiKTtcblxudmFyIHJlc2VydmVkV29yZHMgPSBfaWRlbnRpZmllci5yZXNlcnZlZFdvcmRzO1xudmFyIGtleXdvcmRzID0gX2lkZW50aWZpZXIua2V5d29yZHM7XG5cbnZhciB0dCA9IF9kZXJlcV8oXCIuL3Rva2VudHlwZVwiKS50eXBlcztcblxudmFyIGxpbmVCcmVhayA9IF9kZXJlcV8oXCIuL3doaXRlc3BhY2VcIikubGluZUJyZWFrO1xuXG5mdW5jdGlvbiBQYXJzZXIob3B0aW9ucywgaW5wdXQsIHN0YXJ0UG9zKSB7XG4gIHRoaXMub3B0aW9ucyA9IG9wdGlvbnM7XG4gIHRoaXMuc291cmNlRmlsZSA9IHRoaXMub3B0aW9ucy5zb3VyY2VGaWxlIHx8IG51bGw7XG4gIHRoaXMuaXNLZXl3b3JkID0ga2V5d29yZHNbdGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYgPyA2IDogNV07XG4gIHRoaXMuaXNSZXNlcnZlZFdvcmQgPSByZXNlcnZlZFdvcmRzW3RoaXMub3B0aW9ucy5lY21hVmVyc2lvbl07XG4gIHRoaXMuaW5wdXQgPSBpbnB1dDtcblxuICAvLyBMb2FkIHBsdWdpbnNcbiAgdGhpcy5sb2FkUGx1Z2lucyh0aGlzLm9wdGlvbnMucGx1Z2lucyk7XG5cbiAgLy8gU2V0IHVwIHRva2VuIHN0YXRlXG5cbiAgLy8gVGhlIGN1cnJlbnQgcG9zaXRpb24gb2YgdGhlIHRva2VuaXplciBpbiB0aGUgaW5wdXQuXG4gIGlmIChzdGFydFBvcykge1xuICAgIHRoaXMucG9zID0gc3RhcnRQb3M7XG4gICAgdGhpcy5saW5lU3RhcnQgPSBNYXRoLm1heCgwLCB0aGlzLmlucHV0Lmxhc3RJbmRleE9mKFwiXFxuXCIsIHN0YXJ0UG9zKSk7XG4gICAgdGhpcy5jdXJMaW5lID0gdGhpcy5pbnB1dC5zbGljZSgwLCB0aGlzLmxpbmVTdGFydCkuc3BsaXQobGluZUJyZWFrKS5sZW5ndGg7XG4gIH0gZWxzZSB7XG4gICAgdGhpcy5wb3MgPSB0aGlzLmxpbmVTdGFydCA9IDA7XG4gICAgdGhpcy5jdXJMaW5lID0gMTtcbiAgfVxuXG4gIC8vIFByb3BlcnRpZXMgb2YgdGhlIGN1cnJlbnQgdG9rZW46XG4gIC8vIEl0cyB0eXBlXG4gIHRoaXMudHlwZSA9IHR0LmVvZjtcbiAgLy8gRm9yIHRva2VucyB0aGF0IGluY2x1ZGUgbW9yZSBpbmZvcm1hdGlvbiB0aGFuIHRoZWlyIHR5cGUsIHRoZSB2YWx1ZVxuICB0aGlzLnZhbHVlID0gbnVsbDtcbiAgLy8gSXRzIHN0YXJ0IGFuZCBlbmQgb2Zmc2V0XG4gIHRoaXMuc3RhcnQgPSB0aGlzLmVuZCA9IHRoaXMucG9zO1xuICAvLyBBbmQsIGlmIGxvY2F0aW9ucyBhcmUgdXNlZCwgdGhlIHtsaW5lLCBjb2x1bW59IG9iamVjdFxuICAvLyBjb3JyZXNwb25kaW5nIHRvIHRob3NlIG9mZnNldHNcbiAgdGhpcy5zdGFydExvYyA9IHRoaXMuZW5kTG9jID0gbnVsbDtcblxuICAvLyBQb3NpdGlvbiBpbmZvcm1hdGlvbiBmb3IgdGhlIHByZXZpb3VzIHRva2VuXG4gIHRoaXMubGFzdFRva0VuZExvYyA9IHRoaXMubGFzdFRva1N0YXJ0TG9jID0gbnVsbDtcbiAgdGhpcy5sYXN0VG9rU3RhcnQgPSB0aGlzLmxhc3RUb2tFbmQgPSB0aGlzLnBvcztcblxuICAvLyBUaGUgY29udGV4dCBzdGFjayBpcyB1c2VkIHRvIHN1cGVyZmljaWFsbHkgdHJhY2sgc3ludGFjdGljXG4gIC8vIGNvbnRleHQgdG8gcHJlZGljdCB3aGV0aGVyIGEgcmVndWxhciBleHByZXNzaW9uIGlzIGFsbG93ZWQgaW4gYVxuICAvLyBnaXZlbiBwb3NpdGlvbi5cbiAgdGhpcy5jb250ZXh0ID0gdGhpcy5pbml0aWFsQ29udGV4dCgpO1xuICB0aGlzLmV4cHJBbGxvd2VkID0gdHJ1ZTtcblxuICAvLyBGaWd1cmUgb3V0IGlmIGl0J3MgYSBtb2R1bGUgY29kZS5cbiAgdGhpcy5zdHJpY3QgPSB0aGlzLmluTW9kdWxlID0gdGhpcy5vcHRpb25zLnNvdXJjZVR5cGUgPT09IFwibW9kdWxlXCI7XG5cbiAgLy8gVXNlZCB0byBzaWduaWZ5IHRoZSBzdGFydCBvZiBhIHBvdGVudGlhbCBhcnJvdyBmdW5jdGlvblxuICB0aGlzLnBvdGVudGlhbEFycm93QXQgPSAtMTtcblxuICAvLyBGbGFncyB0byB0cmFjayB3aGV0aGVyIHdlIGFyZSBpbiBhIGZ1bmN0aW9uLCBhIGdlbmVyYXRvci5cbiAgdGhpcy5pbkZ1bmN0aW9uID0gdGhpcy5pbkdlbmVyYXRvciA9IGZhbHNlO1xuICAvLyBMYWJlbHMgaW4gc2NvcGUuXG4gIHRoaXMubGFiZWxzID0gW107XG5cbiAgLy8gSWYgZW5hYmxlZCwgc2tpcCBsZWFkaW5nIGhhc2hiYW5nIGxpbmUuXG4gIGlmICh0aGlzLnBvcyA9PT0gMCAmJiB0aGlzLm9wdGlvbnMuYWxsb3dIYXNoQmFuZyAmJiB0aGlzLmlucHV0LnNsaWNlKDAsIDIpID09PSBcIiMhXCIpIHRoaXMuc2tpcExpbmVDb21tZW50KDIpO1xufVxuXG5QYXJzZXIucHJvdG90eXBlLmV4dGVuZCA9IGZ1bmN0aW9uIChuYW1lLCBmKSB7XG4gIHRoaXNbbmFtZV0gPSBmKHRoaXNbbmFtZV0pO1xufTtcblxuLy8gUmVnaXN0ZXJlZCBwbHVnaW5zXG5cbnZhciBwbHVnaW5zID0ge307XG5cbmV4cG9ydHMucGx1Z2lucyA9IHBsdWdpbnM7XG5QYXJzZXIucHJvdG90eXBlLmxvYWRQbHVnaW5zID0gZnVuY3Rpb24gKHBsdWdpbnMpIHtcbiAgZm9yICh2YXIgX25hbWUgaW4gcGx1Z2lucykge1xuICAgIHZhciBwbHVnaW4gPSBleHBvcnRzLnBsdWdpbnNbX25hbWVdO1xuICAgIGlmICghcGx1Z2luKSB0aHJvdyBuZXcgRXJyb3IoXCJQbHVnaW4gJ1wiICsgX25hbWUgKyBcIicgbm90IGZvdW5kXCIpO1xuICAgIHBsdWdpbih0aGlzLCBwbHVnaW5zW19uYW1lXSk7XG4gIH1cbn07XG5cbn0se1wiLi9pZGVudGlmaWVyXCI6NyxcIi4vdG9rZW50eXBlXCI6MTcsXCIuL3doaXRlc3BhY2VcIjoxOX1dLDE0OltmdW5jdGlvbihfZGVyZXFfLG1vZHVsZSxleHBvcnRzKXtcblwidXNlIHN0cmljdFwiO1xuXG52YXIgdHQgPSBfZGVyZXFfKFwiLi90b2tlbnR5cGVcIikudHlwZXM7XG5cbnZhciBQYXJzZXIgPSBfZGVyZXFfKFwiLi9zdGF0ZVwiKS5QYXJzZXI7XG5cbnZhciBsaW5lQnJlYWsgPSBfZGVyZXFfKFwiLi93aGl0ZXNwYWNlXCIpLmxpbmVCcmVhaztcblxudmFyIHBwID0gUGFyc2VyLnByb3RvdHlwZTtcblxuLy8gIyMjIFN0YXRlbWVudCBwYXJzaW5nXG5cbi8vIFBhcnNlIGEgcHJvZ3JhbS4gSW5pdGlhbGl6ZXMgdGhlIHBhcnNlciwgcmVhZHMgYW55IG51bWJlciBvZlxuLy8gc3RhdGVtZW50cywgYW5kIHdyYXBzIHRoZW0gaW4gYSBQcm9ncmFtIG5vZGUuICBPcHRpb25hbGx5IHRha2VzIGFcbi8vIGBwcm9ncmFtYCBhcmd1bWVudC4gIElmIHByZXNlbnQsIHRoZSBzdGF0ZW1lbnRzIHdpbGwgYmUgYXBwZW5kZWRcbi8vIHRvIGl0cyBib2R5IGluc3RlYWQgb2YgY3JlYXRpbmcgYSBuZXcgbm9kZS5cblxucHAucGFyc2VUb3BMZXZlbCA9IGZ1bmN0aW9uIChub2RlKSB7XG4gIHZhciBmaXJzdCA9IHRydWU7XG4gIGlmICghbm9kZS5ib2R5KSBub2RlLmJvZHkgPSBbXTtcbiAgd2hpbGUgKHRoaXMudHlwZSAhPT0gdHQuZW9mKSB7XG4gICAgdmFyIHN0bXQgPSB0aGlzLnBhcnNlU3RhdGVtZW50KHRydWUsIHRydWUpO1xuICAgIG5vZGUuYm9keS5wdXNoKHN0bXQpO1xuICAgIGlmIChmaXJzdCAmJiB0aGlzLmlzVXNlU3RyaWN0KHN0bXQpKSB0aGlzLnNldFN0cmljdCh0cnVlKTtcbiAgICBmaXJzdCA9IGZhbHNlO1xuICB9XG4gIHRoaXMubmV4dCgpO1xuICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYpIHtcbiAgICBub2RlLnNvdXJjZVR5cGUgPSB0aGlzLm9wdGlvbnMuc291cmNlVHlwZTtcbiAgfVxuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiUHJvZ3JhbVwiKTtcbn07XG5cbnZhciBsb29wTGFiZWwgPSB7IGtpbmQ6IFwibG9vcFwiIH0sXG4gICAgc3dpdGNoTGFiZWwgPSB7IGtpbmQ6IFwic3dpdGNoXCIgfTtcblxuLy8gUGFyc2UgYSBzaW5nbGUgc3RhdGVtZW50LlxuLy9cbi8vIElmIGV4cGVjdGluZyBhIHN0YXRlbWVudCBhbmQgZmluZGluZyBhIHNsYXNoIG9wZXJhdG9yLCBwYXJzZSBhXG4vLyByZWd1bGFyIGV4cHJlc3Npb24gbGl0ZXJhbC4gVGhpcyBpcyB0byBoYW5kbGUgY2FzZXMgbGlrZVxuLy8gYGlmIChmb28pIC9ibGFoLy5leGVjKGZvbylgLCB3aGVyZSBsb29raW5nIGF0IHRoZSBwcmV2aW91cyB0b2tlblxuLy8gZG9lcyBub3QgaGVscC5cblxucHAucGFyc2VTdGF0ZW1lbnQgPSBmdW5jdGlvbiAoZGVjbGFyYXRpb24sIHRvcExldmVsKSB7XG4gIHZhciBzdGFydHR5cGUgPSB0aGlzLnR5cGUsXG4gICAgICBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcblxuICAvLyBNb3N0IHR5cGVzIG9mIHN0YXRlbWVudHMgYXJlIHJlY29nbml6ZWQgYnkgdGhlIGtleXdvcmQgdGhleVxuICAvLyBzdGFydCB3aXRoLiBNYW55IGFyZSB0cml2aWFsIHRvIHBhcnNlLCBzb21lIHJlcXVpcmUgYSBiaXQgb2ZcbiAgLy8gY29tcGxleGl0eS5cblxuICBzd2l0Y2ggKHN0YXJ0dHlwZSkge1xuICAgIGNhc2UgdHQuX2JyZWFrOmNhc2UgdHQuX2NvbnRpbnVlOlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VCcmVha0NvbnRpbnVlU3RhdGVtZW50KG5vZGUsIHN0YXJ0dHlwZS5rZXl3b3JkKTtcbiAgICBjYXNlIHR0Ll9kZWJ1Z2dlcjpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlRGVidWdnZXJTdGF0ZW1lbnQobm9kZSk7XG4gICAgY2FzZSB0dC5fZG86XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZURvU3RhdGVtZW50KG5vZGUpO1xuICAgIGNhc2UgdHQuX2ZvcjpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlRm9yU3RhdGVtZW50KG5vZGUpO1xuICAgIGNhc2UgdHQuX2Z1bmN0aW9uOlxuICAgICAgaWYgKCFkZWNsYXJhdGlvbiAmJiB0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNikgdGhpcy51bmV4cGVjdGVkKCk7XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZUZ1bmN0aW9uU3RhdGVtZW50KG5vZGUpO1xuICAgIGNhc2UgdHQuX2NsYXNzOlxuICAgICAgaWYgKCFkZWNsYXJhdGlvbikgdGhpcy51bmV4cGVjdGVkKCk7XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZUNsYXNzKG5vZGUsIHRydWUpO1xuICAgIGNhc2UgdHQuX2lmOlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VJZlN0YXRlbWVudChub2RlKTtcbiAgICBjYXNlIHR0Ll9yZXR1cm46XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZVJldHVyblN0YXRlbWVudChub2RlKTtcbiAgICBjYXNlIHR0Ll9zd2l0Y2g6XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZVN3aXRjaFN0YXRlbWVudChub2RlKTtcbiAgICBjYXNlIHR0Ll90aHJvdzpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlVGhyb3dTdGF0ZW1lbnQobm9kZSk7XG4gICAgY2FzZSB0dC5fdHJ5OlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VUcnlTdGF0ZW1lbnQobm9kZSk7XG4gICAgY2FzZSB0dC5fbGV0OmNhc2UgdHQuX2NvbnN0OlxuICAgICAgaWYgKCFkZWNsYXJhdGlvbikgdGhpcy51bmV4cGVjdGVkKCk7IC8vIE5PVEU6IGZhbGxzIHRocm91Z2ggdG8gX3ZhclxuICAgIGNhc2UgdHQuX3ZhcjpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlVmFyU3RhdGVtZW50KG5vZGUsIHN0YXJ0dHlwZSk7XG4gICAgY2FzZSB0dC5fd2hpbGU6XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZVdoaWxlU3RhdGVtZW50KG5vZGUpO1xuICAgIGNhc2UgdHQuX3dpdGg6XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZVdpdGhTdGF0ZW1lbnQobm9kZSk7XG4gICAgY2FzZSB0dC5icmFjZUw6XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZUJsb2NrKCk7XG4gICAgY2FzZSB0dC5zZW1pOlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VFbXB0eVN0YXRlbWVudChub2RlKTtcbiAgICBjYXNlIHR0Ll9leHBvcnQ6XG4gICAgY2FzZSB0dC5faW1wb3J0OlxuICAgICAgaWYgKCF0aGlzLm9wdGlvbnMuYWxsb3dJbXBvcnRFeHBvcnRFdmVyeXdoZXJlKSB7XG4gICAgICAgIGlmICghdG9wTGV2ZWwpIHRoaXMucmFpc2UodGhpcy5zdGFydCwgXCInaW1wb3J0JyBhbmQgJ2V4cG9ydCcgbWF5IG9ubHkgYXBwZWFyIGF0IHRoZSB0b3AgbGV2ZWxcIik7XG4gICAgICAgIGlmICghdGhpcy5pbk1vZHVsZSkgdGhpcy5yYWlzZSh0aGlzLnN0YXJ0LCBcIidpbXBvcnQnIGFuZCAnZXhwb3J0JyBtYXkgYXBwZWFyIG9ubHkgd2l0aCAnc291cmNlVHlwZTogbW9kdWxlJ1wiKTtcbiAgICAgIH1cbiAgICAgIHJldHVybiBzdGFydHR5cGUgPT09IHR0Ll9pbXBvcnQgPyB0aGlzLnBhcnNlSW1wb3J0KG5vZGUpIDogdGhpcy5wYXJzZUV4cG9ydChub2RlKTtcblxuICAgIC8vIElmIHRoZSBzdGF0ZW1lbnQgZG9lcyBub3Qgc3RhcnQgd2l0aCBhIHN0YXRlbWVudCBrZXl3b3JkIG9yIGFcbiAgICAvLyBicmFjZSwgaXQncyBhbiBFeHByZXNzaW9uU3RhdGVtZW50IG9yIExhYmVsZWRTdGF0ZW1lbnQuIFdlXG4gICAgLy8gc2ltcGx5IHN0YXJ0IHBhcnNpbmcgYW4gZXhwcmVzc2lvbiwgYW5kIGFmdGVyd2FyZHMsIGlmIHRoZVxuICAgIC8vIG5leHQgdG9rZW4gaXMgYSBjb2xvbiBhbmQgdGhlIGV4cHJlc3Npb24gd2FzIGEgc2ltcGxlXG4gICAgLy8gSWRlbnRpZmllciBub2RlLCB3ZSBzd2l0Y2ggdG8gaW50ZXJwcmV0aW5nIGl0IGFzIGEgbGFiZWwuXG4gICAgZGVmYXVsdDpcbiAgICAgIHZhciBtYXliZU5hbWUgPSB0aGlzLnZhbHVlLFxuICAgICAgICAgIGV4cHIgPSB0aGlzLnBhcnNlRXhwcmVzc2lvbigpO1xuICAgICAgaWYgKHN0YXJ0dHlwZSA9PT0gdHQubmFtZSAmJiBleHByLnR5cGUgPT09IFwiSWRlbnRpZmllclwiICYmIHRoaXMuZWF0KHR0LmNvbG9uKSkgcmV0dXJuIHRoaXMucGFyc2VMYWJlbGVkU3RhdGVtZW50KG5vZGUsIG1heWJlTmFtZSwgZXhwcik7ZWxzZSByZXR1cm4gdGhpcy5wYXJzZUV4cHJlc3Npb25TdGF0ZW1lbnQobm9kZSwgZXhwcik7XG4gIH1cbn07XG5cbnBwLnBhcnNlQnJlYWtDb250aW51ZVN0YXRlbWVudCA9IGZ1bmN0aW9uIChub2RlLCBrZXl3b3JkKSB7XG4gIHZhciBpc0JyZWFrID0ga2V5d29yZCA9PSBcImJyZWFrXCI7XG4gIHRoaXMubmV4dCgpO1xuICBpZiAodGhpcy5lYXQodHQuc2VtaSkgfHwgdGhpcy5pbnNlcnRTZW1pY29sb24oKSkgbm9kZS5sYWJlbCA9IG51bGw7ZWxzZSBpZiAodGhpcy50eXBlICE9PSB0dC5uYW1lKSB0aGlzLnVuZXhwZWN0ZWQoKTtlbHNlIHtcbiAgICBub2RlLmxhYmVsID0gdGhpcy5wYXJzZUlkZW50KCk7XG4gICAgdGhpcy5zZW1pY29sb24oKTtcbiAgfVxuXG4gIC8vIFZlcmlmeSB0aGF0IHRoZXJlIGlzIGFuIGFjdHVhbCBkZXN0aW5hdGlvbiB0byBicmVhayBvclxuICAvLyBjb250aW51ZSB0by5cbiAgZm9yICh2YXIgaSA9IDA7IGkgPCB0aGlzLmxhYmVscy5sZW5ndGg7ICsraSkge1xuICAgIHZhciBsYWIgPSB0aGlzLmxhYmVsc1tpXTtcbiAgICBpZiAobm9kZS5sYWJlbCA9PSBudWxsIHx8IGxhYi5uYW1lID09PSBub2RlLmxhYmVsLm5hbWUpIHtcbiAgICAgIGlmIChsYWIua2luZCAhPSBudWxsICYmIChpc0JyZWFrIHx8IGxhYi5raW5kID09PSBcImxvb3BcIikpIGJyZWFrO1xuICAgICAgaWYgKG5vZGUubGFiZWwgJiYgaXNCcmVhaykgYnJlYWs7XG4gICAgfVxuICB9XG4gIGlmIChpID09PSB0aGlzLmxhYmVscy5sZW5ndGgpIHRoaXMucmFpc2Uobm9kZS5zdGFydCwgXCJVbnN5bnRhY3RpYyBcIiArIGtleXdvcmQpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIGlzQnJlYWsgPyBcIkJyZWFrU3RhdGVtZW50XCIgOiBcIkNvbnRpbnVlU3RhdGVtZW50XCIpO1xufTtcblxucHAucGFyc2VEZWJ1Z2dlclN0YXRlbWVudCA9IGZ1bmN0aW9uIChub2RlKSB7XG4gIHRoaXMubmV4dCgpO1xuICB0aGlzLnNlbWljb2xvbigpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiRGVidWdnZXJTdGF0ZW1lbnRcIik7XG59O1xuXG5wcC5wYXJzZURvU3RhdGVtZW50ID0gZnVuY3Rpb24gKG5vZGUpIHtcbiAgdGhpcy5uZXh0KCk7XG4gIHRoaXMubGFiZWxzLnB1c2gobG9vcExhYmVsKTtcbiAgbm9kZS5ib2R5ID0gdGhpcy5wYXJzZVN0YXRlbWVudChmYWxzZSk7XG4gIHRoaXMubGFiZWxzLnBvcCgpO1xuICB0aGlzLmV4cGVjdCh0dC5fd2hpbGUpO1xuICBub2RlLnRlc3QgPSB0aGlzLnBhcnNlUGFyZW5FeHByZXNzaW9uKCk7XG4gIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNikgdGhpcy5lYXQodHQuc2VtaSk7ZWxzZSB0aGlzLnNlbWljb2xvbigpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiRG9XaGlsZVN0YXRlbWVudFwiKTtcbn07XG5cbi8vIERpc2FtYmlndWF0aW5nIGJldHdlZW4gYSBgZm9yYCBhbmQgYSBgZm9yYC9gaW5gIG9yIGBmb3JgL2BvZmBcbi8vIGxvb3AgaXMgbm9uLXRyaXZpYWwuIEJhc2ljYWxseSwgd2UgaGF2ZSB0byBwYXJzZSB0aGUgaW5pdCBgdmFyYFxuLy8gc3RhdGVtZW50IG9yIGV4cHJlc3Npb24sIGRpc2FsbG93aW5nIHRoZSBgaW5gIG9wZXJhdG9yIChzZWVcbi8vIHRoZSBzZWNvbmQgcGFyYW1ldGVyIHRvIGBwYXJzZUV4cHJlc3Npb25gKSwgYW5kIHRoZW4gY2hlY2tcbi8vIHdoZXRoZXIgdGhlIG5leHQgdG9rZW4gaXMgYGluYCBvciBgb2ZgLiBXaGVuIHRoZXJlIGlzIG5vIGluaXRcbi8vIHBhcnQgKHNlbWljb2xvbiBpbW1lZGlhdGVseSBhZnRlciB0aGUgb3BlbmluZyBwYXJlbnRoZXNpcyksIGl0XG4vLyBpcyBhIHJlZ3VsYXIgYGZvcmAgbG9vcC5cblxucHAucGFyc2VGb3JTdGF0ZW1lbnQgPSBmdW5jdGlvbiAobm9kZSkge1xuICB0aGlzLm5leHQoKTtcbiAgdGhpcy5sYWJlbHMucHVzaChsb29wTGFiZWwpO1xuICB0aGlzLmV4cGVjdCh0dC5wYXJlbkwpO1xuICBpZiAodGhpcy50eXBlID09PSB0dC5zZW1pKSByZXR1cm4gdGhpcy5wYXJzZUZvcihub2RlLCBudWxsKTtcbiAgaWYgKHRoaXMudHlwZSA9PT0gdHQuX3ZhciB8fCB0aGlzLnR5cGUgPT09IHR0Ll9sZXQgfHwgdGhpcy50eXBlID09PSB0dC5fY29uc3QpIHtcbiAgICB2YXIgX2luaXQgPSB0aGlzLnN0YXJ0Tm9kZSgpLFxuICAgICAgICB2YXJLaW5kID0gdGhpcy50eXBlO1xuICAgIHRoaXMubmV4dCgpO1xuICAgIHRoaXMucGFyc2VWYXIoX2luaXQsIHRydWUsIHZhcktpbmQpO1xuICAgIHRoaXMuZmluaXNoTm9kZShfaW5pdCwgXCJWYXJpYWJsZURlY2xhcmF0aW9uXCIpO1xuICAgIGlmICgodGhpcy50eXBlID09PSB0dC5faW4gfHwgdGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYgJiYgdGhpcy5pc0NvbnRleHR1YWwoXCJvZlwiKSkgJiYgX2luaXQuZGVjbGFyYXRpb25zLmxlbmd0aCA9PT0gMSAmJiAhKHZhcktpbmQgIT09IHR0Ll92YXIgJiYgX2luaXQuZGVjbGFyYXRpb25zWzBdLmluaXQpKSByZXR1cm4gdGhpcy5wYXJzZUZvckluKG5vZGUsIF9pbml0KTtcbiAgICByZXR1cm4gdGhpcy5wYXJzZUZvcihub2RlLCBfaW5pdCk7XG4gIH1cbiAgdmFyIHJlZlNob3J0aGFuZERlZmF1bHRQb3MgPSB7IHN0YXJ0OiAwIH07XG4gIHZhciBpbml0ID0gdGhpcy5wYXJzZUV4cHJlc3Npb24odHJ1ZSwgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcyk7XG4gIGlmICh0aGlzLnR5cGUgPT09IHR0Ll9pbiB8fCB0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNiAmJiB0aGlzLmlzQ29udGV4dHVhbChcIm9mXCIpKSB7XG4gICAgdGhpcy50b0Fzc2lnbmFibGUoaW5pdCk7XG4gICAgdGhpcy5jaGVja0xWYWwoaW5pdCk7XG4gICAgcmV0dXJuIHRoaXMucGFyc2VGb3JJbihub2RlLCBpbml0KTtcbiAgfSBlbHNlIGlmIChyZWZTaG9ydGhhbmREZWZhdWx0UG9zLnN0YXJ0KSB7XG4gICAgdGhpcy51bmV4cGVjdGVkKHJlZlNob3J0aGFuZERlZmF1bHRQb3Muc3RhcnQpO1xuICB9XG4gIHJldHVybiB0aGlzLnBhcnNlRm9yKG5vZGUsIGluaXQpO1xufTtcblxucHAucGFyc2VGdW5jdGlvblN0YXRlbWVudCA9IGZ1bmN0aW9uIChub2RlKSB7XG4gIHRoaXMubmV4dCgpO1xuICByZXR1cm4gdGhpcy5wYXJzZUZ1bmN0aW9uKG5vZGUsIHRydWUpO1xufTtcblxucHAucGFyc2VJZlN0YXRlbWVudCA9IGZ1bmN0aW9uIChub2RlKSB7XG4gIHRoaXMubmV4dCgpO1xuICBub2RlLnRlc3QgPSB0aGlzLnBhcnNlUGFyZW5FeHByZXNzaW9uKCk7XG4gIG5vZGUuY29uc2VxdWVudCA9IHRoaXMucGFyc2VTdGF0ZW1lbnQoZmFsc2UpO1xuICBub2RlLmFsdGVybmF0ZSA9IHRoaXMuZWF0KHR0Ll9lbHNlKSA/IHRoaXMucGFyc2VTdGF0ZW1lbnQoZmFsc2UpIDogbnVsbDtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIklmU3RhdGVtZW50XCIpO1xufTtcblxucHAucGFyc2VSZXR1cm5TdGF0ZW1lbnQgPSBmdW5jdGlvbiAobm9kZSkge1xuICBpZiAoIXRoaXMuaW5GdW5jdGlvbiAmJiAhdGhpcy5vcHRpb25zLmFsbG93UmV0dXJuT3V0c2lkZUZ1bmN0aW9uKSB0aGlzLnJhaXNlKHRoaXMuc3RhcnQsIFwiJ3JldHVybicgb3V0c2lkZSBvZiBmdW5jdGlvblwiKTtcbiAgdGhpcy5uZXh0KCk7XG5cbiAgLy8gSW4gYHJldHVybmAgKGFuZCBgYnJlYWtgL2Bjb250aW51ZWApLCB0aGUga2V5d29yZHMgd2l0aFxuICAvLyBvcHRpb25hbCBhcmd1bWVudHMsIHdlIGVhZ2VybHkgbG9vayBmb3IgYSBzZW1pY29sb24gb3IgdGhlXG4gIC8vIHBvc3NpYmlsaXR5IHRvIGluc2VydCBvbmUuXG5cbiAgaWYgKHRoaXMuZWF0KHR0LnNlbWkpIHx8IHRoaXMuaW5zZXJ0U2VtaWNvbG9uKCkpIG5vZGUuYXJndW1lbnQgPSBudWxsO2Vsc2Uge1xuICAgIG5vZGUuYXJndW1lbnQgPSB0aGlzLnBhcnNlRXhwcmVzc2lvbigpO3RoaXMuc2VtaWNvbG9uKCk7XG4gIH1cbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIlJldHVyblN0YXRlbWVudFwiKTtcbn07XG5cbnBwLnBhcnNlU3dpdGNoU3RhdGVtZW50ID0gZnVuY3Rpb24gKG5vZGUpIHtcbiAgdGhpcy5uZXh0KCk7XG4gIG5vZGUuZGlzY3JpbWluYW50ID0gdGhpcy5wYXJzZVBhcmVuRXhwcmVzc2lvbigpO1xuICBub2RlLmNhc2VzID0gW107XG4gIHRoaXMuZXhwZWN0KHR0LmJyYWNlTCk7XG4gIHRoaXMubGFiZWxzLnB1c2goc3dpdGNoTGFiZWwpO1xuXG4gIC8vIFN0YXRlbWVudHMgdW5kZXIgbXVzdCBiZSBncm91cGVkIChieSBsYWJlbCkgaW4gU3dpdGNoQ2FzZVxuICAvLyBub2Rlcy4gYGN1cmAgaXMgdXNlZCB0byBrZWVwIHRoZSBub2RlIHRoYXQgd2UgYXJlIGN1cnJlbnRseVxuICAvLyBhZGRpbmcgc3RhdGVtZW50cyB0by5cblxuICBmb3IgKHZhciBjdXIsIHNhd0RlZmF1bHQ7IHRoaXMudHlwZSAhPSB0dC5icmFjZVI7KSB7XG4gICAgaWYgKHRoaXMudHlwZSA9PT0gdHQuX2Nhc2UgfHwgdGhpcy50eXBlID09PSB0dC5fZGVmYXVsdCkge1xuICAgICAgdmFyIGlzQ2FzZSA9IHRoaXMudHlwZSA9PT0gdHQuX2Nhc2U7XG4gICAgICBpZiAoY3VyKSB0aGlzLmZpbmlzaE5vZGUoY3VyLCBcIlN3aXRjaENhc2VcIik7XG4gICAgICBub2RlLmNhc2VzLnB1c2goY3VyID0gdGhpcy5zdGFydE5vZGUoKSk7XG4gICAgICBjdXIuY29uc2VxdWVudCA9IFtdO1xuICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICBpZiAoaXNDYXNlKSB7XG4gICAgICAgIGN1ci50ZXN0ID0gdGhpcy5wYXJzZUV4cHJlc3Npb24oKTtcbiAgICAgIH0gZWxzZSB7XG4gICAgICAgIGlmIChzYXdEZWZhdWx0KSB0aGlzLnJhaXNlKHRoaXMubGFzdFRva1N0YXJ0LCBcIk11bHRpcGxlIGRlZmF1bHQgY2xhdXNlc1wiKTtcbiAgICAgICAgc2F3RGVmYXVsdCA9IHRydWU7XG4gICAgICAgIGN1ci50ZXN0ID0gbnVsbDtcbiAgICAgIH1cbiAgICAgIHRoaXMuZXhwZWN0KHR0LmNvbG9uKTtcbiAgICB9IGVsc2Uge1xuICAgICAgaWYgKCFjdXIpIHRoaXMudW5leHBlY3RlZCgpO1xuICAgICAgY3VyLmNvbnNlcXVlbnQucHVzaCh0aGlzLnBhcnNlU3RhdGVtZW50KHRydWUpKTtcbiAgICB9XG4gIH1cbiAgaWYgKGN1cikgdGhpcy5maW5pc2hOb2RlKGN1ciwgXCJTd2l0Y2hDYXNlXCIpO1xuICB0aGlzLm5leHQoKTsgLy8gQ2xvc2luZyBicmFjZVxuICB0aGlzLmxhYmVscy5wb3AoKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIlN3aXRjaFN0YXRlbWVudFwiKTtcbn07XG5cbnBwLnBhcnNlVGhyb3dTdGF0ZW1lbnQgPSBmdW5jdGlvbiAobm9kZSkge1xuICB0aGlzLm5leHQoKTtcbiAgaWYgKGxpbmVCcmVhay50ZXN0KHRoaXMuaW5wdXQuc2xpY2UodGhpcy5sYXN0VG9rRW5kLCB0aGlzLnN0YXJ0KSkpIHRoaXMucmFpc2UodGhpcy5sYXN0VG9rRW5kLCBcIklsbGVnYWwgbmV3bGluZSBhZnRlciB0aHJvd1wiKTtcbiAgbm9kZS5hcmd1bWVudCA9IHRoaXMucGFyc2VFeHByZXNzaW9uKCk7XG4gIHRoaXMuc2VtaWNvbG9uKCk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJUaHJvd1N0YXRlbWVudFwiKTtcbn07XG5cbi8vIFJldXNlZCBlbXB0eSBhcnJheSBhZGRlZCBmb3Igbm9kZSBmaWVsZHMgdGhhdCBhcmUgYWx3YXlzIGVtcHR5LlxuXG52YXIgZW1wdHkgPSBbXTtcblxucHAucGFyc2VUcnlTdGF0ZW1lbnQgPSBmdW5jdGlvbiAobm9kZSkge1xuICB0aGlzLm5leHQoKTtcbiAgbm9kZS5ibG9jayA9IHRoaXMucGFyc2VCbG9jaygpO1xuICBub2RlLmhhbmRsZXIgPSBudWxsO1xuICBpZiAodGhpcy50eXBlID09PSB0dC5fY2F0Y2gpIHtcbiAgICB2YXIgY2xhdXNlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgICB0aGlzLm5leHQoKTtcbiAgICB0aGlzLmV4cGVjdCh0dC5wYXJlbkwpO1xuICAgIGNsYXVzZS5wYXJhbSA9IHRoaXMucGFyc2VCaW5kaW5nQXRvbSgpO1xuICAgIHRoaXMuY2hlY2tMVmFsKGNsYXVzZS5wYXJhbSwgdHJ1ZSk7XG4gICAgdGhpcy5leHBlY3QodHQucGFyZW5SKTtcbiAgICBjbGF1c2UuZ3VhcmQgPSBudWxsO1xuICAgIGNsYXVzZS5ib2R5ID0gdGhpcy5wYXJzZUJsb2NrKCk7XG4gICAgbm9kZS5oYW5kbGVyID0gdGhpcy5maW5pc2hOb2RlKGNsYXVzZSwgXCJDYXRjaENsYXVzZVwiKTtcbiAgfVxuICBub2RlLmd1YXJkZWRIYW5kbGVycyA9IGVtcHR5O1xuICBub2RlLmZpbmFsaXplciA9IHRoaXMuZWF0KHR0Ll9maW5hbGx5KSA/IHRoaXMucGFyc2VCbG9jaygpIDogbnVsbDtcbiAgaWYgKCFub2RlLmhhbmRsZXIgJiYgIW5vZGUuZmluYWxpemVyKSB0aGlzLnJhaXNlKG5vZGUuc3RhcnQsIFwiTWlzc2luZyBjYXRjaCBvciBmaW5hbGx5IGNsYXVzZVwiKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIlRyeVN0YXRlbWVudFwiKTtcbn07XG5cbnBwLnBhcnNlVmFyU3RhdGVtZW50ID0gZnVuY3Rpb24gKG5vZGUsIGtpbmQpIHtcbiAgdGhpcy5uZXh0KCk7XG4gIHRoaXMucGFyc2VWYXIobm9kZSwgZmFsc2UsIGtpbmQpO1xuICB0aGlzLnNlbWljb2xvbigpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiVmFyaWFibGVEZWNsYXJhdGlvblwiKTtcbn07XG5cbnBwLnBhcnNlV2hpbGVTdGF0ZW1lbnQgPSBmdW5jdGlvbiAobm9kZSkge1xuICB0aGlzLm5leHQoKTtcbiAgbm9kZS50ZXN0ID0gdGhpcy5wYXJzZVBhcmVuRXhwcmVzc2lvbigpO1xuICB0aGlzLmxhYmVscy5wdXNoKGxvb3BMYWJlbCk7XG4gIG5vZGUuYm9keSA9IHRoaXMucGFyc2VTdGF0ZW1lbnQoZmFsc2UpO1xuICB0aGlzLmxhYmVscy5wb3AoKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIldoaWxlU3RhdGVtZW50XCIpO1xufTtcblxucHAucGFyc2VXaXRoU3RhdGVtZW50ID0gZnVuY3Rpb24gKG5vZGUpIHtcbiAgaWYgKHRoaXMuc3RyaWN0KSB0aGlzLnJhaXNlKHRoaXMuc3RhcnQsIFwiJ3dpdGgnIGluIHN0cmljdCBtb2RlXCIpO1xuICB0aGlzLm5leHQoKTtcbiAgbm9kZS5vYmplY3QgPSB0aGlzLnBhcnNlUGFyZW5FeHByZXNzaW9uKCk7XG4gIG5vZGUuYm9keSA9IHRoaXMucGFyc2VTdGF0ZW1lbnQoZmFsc2UpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiV2l0aFN0YXRlbWVudFwiKTtcbn07XG5cbnBwLnBhcnNlRW1wdHlTdGF0ZW1lbnQgPSBmdW5jdGlvbiAobm9kZSkge1xuICB0aGlzLm5leHQoKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkVtcHR5U3RhdGVtZW50XCIpO1xufTtcblxucHAucGFyc2VMYWJlbGVkU3RhdGVtZW50ID0gZnVuY3Rpb24gKG5vZGUsIG1heWJlTmFtZSwgZXhwcikge1xuICBmb3IgKHZhciBpID0gMDsgaSA8IHRoaXMubGFiZWxzLmxlbmd0aDsgKytpKSB7XG4gICAgaWYgKHRoaXMubGFiZWxzW2ldLm5hbWUgPT09IG1heWJlTmFtZSkgdGhpcy5yYWlzZShleHByLnN0YXJ0LCBcIkxhYmVsICdcIiArIG1heWJlTmFtZSArIFwiJyBpcyBhbHJlYWR5IGRlY2xhcmVkXCIpO1xuICB9dmFyIGtpbmQgPSB0aGlzLnR5cGUuaXNMb29wID8gXCJsb29wXCIgOiB0aGlzLnR5cGUgPT09IHR0Ll9zd2l0Y2ggPyBcInN3aXRjaFwiIDogbnVsbDtcbiAgdGhpcy5sYWJlbHMucHVzaCh7IG5hbWU6IG1heWJlTmFtZSwga2luZDoga2luZCB9KTtcbiAgbm9kZS5ib2R5ID0gdGhpcy5wYXJzZVN0YXRlbWVudCh0cnVlKTtcbiAgdGhpcy5sYWJlbHMucG9wKCk7XG4gIG5vZGUubGFiZWwgPSBleHByO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiTGFiZWxlZFN0YXRlbWVudFwiKTtcbn07XG5cbnBwLnBhcnNlRXhwcmVzc2lvblN0YXRlbWVudCA9IGZ1bmN0aW9uIChub2RlLCBleHByKSB7XG4gIG5vZGUuZXhwcmVzc2lvbiA9IGV4cHI7XG4gIHRoaXMuc2VtaWNvbG9uKCk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJFeHByZXNzaW9uU3RhdGVtZW50XCIpO1xufTtcblxuLy8gUGFyc2UgYSBzZW1pY29sb24tZW5jbG9zZWQgYmxvY2sgb2Ygc3RhdGVtZW50cywgaGFuZGxpbmcgYFwidXNlXG4vLyBzdHJpY3RcImAgZGVjbGFyYXRpb25zIHdoZW4gYGFsbG93U3RyaWN0YCBpcyB0cnVlICh1c2VkIGZvclxuLy8gZnVuY3Rpb24gYm9kaWVzKS5cblxucHAucGFyc2VCbG9jayA9IGZ1bmN0aW9uIChhbGxvd1N0cmljdCkge1xuICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCksXG4gICAgICBmaXJzdCA9IHRydWUsXG4gICAgICBvbGRTdHJpY3QgPSB1bmRlZmluZWQ7XG4gIG5vZGUuYm9keSA9IFtdO1xuICB0aGlzLmV4cGVjdCh0dC5icmFjZUwpO1xuICB3aGlsZSAoIXRoaXMuZWF0KHR0LmJyYWNlUikpIHtcbiAgICB2YXIgc3RtdCA9IHRoaXMucGFyc2VTdGF0ZW1lbnQodHJ1ZSk7XG4gICAgbm9kZS5ib2R5LnB1c2goc3RtdCk7XG4gICAgaWYgKGZpcnN0ICYmIGFsbG93U3RyaWN0ICYmIHRoaXMuaXNVc2VTdHJpY3Qoc3RtdCkpIHtcbiAgICAgIG9sZFN0cmljdCA9IHRoaXMuc3RyaWN0O1xuICAgICAgdGhpcy5zZXRTdHJpY3QodGhpcy5zdHJpY3QgPSB0cnVlKTtcbiAgICB9XG4gICAgZmlyc3QgPSBmYWxzZTtcbiAgfVxuICBpZiAob2xkU3RyaWN0ID09PSBmYWxzZSkgdGhpcy5zZXRTdHJpY3QoZmFsc2UpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiQmxvY2tTdGF0ZW1lbnRcIik7XG59O1xuXG4vLyBQYXJzZSBhIHJlZ3VsYXIgYGZvcmAgbG9vcC4gVGhlIGRpc2FtYmlndWF0aW9uIGNvZGUgaW5cbi8vIGBwYXJzZVN0YXRlbWVudGAgd2lsbCBhbHJlYWR5IGhhdmUgcGFyc2VkIHRoZSBpbml0IHN0YXRlbWVudCBvclxuLy8gZXhwcmVzc2lvbi5cblxucHAucGFyc2VGb3IgPSBmdW5jdGlvbiAobm9kZSwgaW5pdCkge1xuICBub2RlLmluaXQgPSBpbml0O1xuICB0aGlzLmV4cGVjdCh0dC5zZW1pKTtcbiAgbm9kZS50ZXN0ID0gdGhpcy50eXBlID09PSB0dC5zZW1pID8gbnVsbCA6IHRoaXMucGFyc2VFeHByZXNzaW9uKCk7XG4gIHRoaXMuZXhwZWN0KHR0LnNlbWkpO1xuICBub2RlLnVwZGF0ZSA9IHRoaXMudHlwZSA9PT0gdHQucGFyZW5SID8gbnVsbCA6IHRoaXMucGFyc2VFeHByZXNzaW9uKCk7XG4gIHRoaXMuZXhwZWN0KHR0LnBhcmVuUik7XG4gIG5vZGUuYm9keSA9IHRoaXMucGFyc2VTdGF0ZW1lbnQoZmFsc2UpO1xuICB0aGlzLmxhYmVscy5wb3AoKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkZvclN0YXRlbWVudFwiKTtcbn07XG5cbi8vIFBhcnNlIGEgYGZvcmAvYGluYCBhbmQgYGZvcmAvYG9mYCBsb29wLCB3aGljaCBhcmUgYWxtb3N0XG4vLyBzYW1lIGZyb20gcGFyc2VyJ3MgcGVyc3BlY3RpdmUuXG5cbnBwLnBhcnNlRm9ySW4gPSBmdW5jdGlvbiAobm9kZSwgaW5pdCkge1xuICB2YXIgdHlwZSA9IHRoaXMudHlwZSA9PT0gdHQuX2luID8gXCJGb3JJblN0YXRlbWVudFwiIDogXCJGb3JPZlN0YXRlbWVudFwiO1xuICB0aGlzLm5leHQoKTtcbiAgbm9kZS5sZWZ0ID0gaW5pdDtcbiAgbm9kZS5yaWdodCA9IHRoaXMucGFyc2VFeHByZXNzaW9uKCk7XG4gIHRoaXMuZXhwZWN0KHR0LnBhcmVuUik7XG4gIG5vZGUuYm9keSA9IHRoaXMucGFyc2VTdGF0ZW1lbnQoZmFsc2UpO1xuICB0aGlzLmxhYmVscy5wb3AoKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCB0eXBlKTtcbn07XG5cbi8vIFBhcnNlIGEgbGlzdCBvZiB2YXJpYWJsZSBkZWNsYXJhdGlvbnMuXG5cbnBwLnBhcnNlVmFyID0gZnVuY3Rpb24gKG5vZGUsIGlzRm9yLCBraW5kKSB7XG4gIG5vZGUuZGVjbGFyYXRpb25zID0gW107XG4gIG5vZGUua2luZCA9IGtpbmQua2V5d29yZDtcbiAgZm9yICg7Oykge1xuICAgIHZhciBkZWNsID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgICB0aGlzLnBhcnNlVmFySWQoZGVjbCk7XG4gICAgaWYgKHRoaXMuZWF0KHR0LmVxKSkge1xuICAgICAgZGVjbC5pbml0ID0gdGhpcy5wYXJzZU1heWJlQXNzaWduKGlzRm9yKTtcbiAgICB9IGVsc2UgaWYgKGtpbmQgPT09IHR0Ll9jb25zdCAmJiAhKHRoaXMudHlwZSA9PT0gdHQuX2luIHx8IHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2ICYmIHRoaXMuaXNDb250ZXh0dWFsKFwib2ZcIikpKSB7XG4gICAgICB0aGlzLnVuZXhwZWN0ZWQoKTtcbiAgICB9IGVsc2UgaWYgKGRlY2wuaWQudHlwZSAhPSBcIklkZW50aWZpZXJcIiAmJiAhKGlzRm9yICYmICh0aGlzLnR5cGUgPT09IHR0Ll9pbiB8fCB0aGlzLmlzQ29udGV4dHVhbChcIm9mXCIpKSkpIHtcbiAgICAgIHRoaXMucmFpc2UodGhpcy5sYXN0VG9rRW5kLCBcIkNvbXBsZXggYmluZGluZyBwYXR0ZXJucyByZXF1aXJlIGFuIGluaXRpYWxpemF0aW9uIHZhbHVlXCIpO1xuICAgIH0gZWxzZSB7XG4gICAgICBkZWNsLmluaXQgPSBudWxsO1xuICAgIH1cbiAgICBub2RlLmRlY2xhcmF0aW9ucy5wdXNoKHRoaXMuZmluaXNoTm9kZShkZWNsLCBcIlZhcmlhYmxlRGVjbGFyYXRvclwiKSk7XG4gICAgaWYgKCF0aGlzLmVhdCh0dC5jb21tYSkpIGJyZWFrO1xuICB9XG4gIHJldHVybiBub2RlO1xufTtcblxucHAucGFyc2VWYXJJZCA9IGZ1bmN0aW9uIChkZWNsKSB7XG4gIGRlY2wuaWQgPSB0aGlzLnBhcnNlQmluZGluZ0F0b20oKTtcbiAgdGhpcy5jaGVja0xWYWwoZGVjbC5pZCwgdHJ1ZSk7XG59O1xuXG4vLyBQYXJzZSBhIGZ1bmN0aW9uIGRlY2xhcmF0aW9uIG9yIGxpdGVyYWwgKGRlcGVuZGluZyBvbiB0aGVcbi8vIGBpc1N0YXRlbWVudGAgcGFyYW1ldGVyKS5cblxucHAucGFyc2VGdW5jdGlvbiA9IGZ1bmN0aW9uIChub2RlLCBpc1N0YXRlbWVudCwgYWxsb3dFeHByZXNzaW9uQm9keSkge1xuICB0aGlzLmluaXRGdW5jdGlvbihub2RlKTtcbiAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KSBub2RlLmdlbmVyYXRvciA9IHRoaXMuZWF0KHR0LnN0YXIpO1xuICBpZiAoaXNTdGF0ZW1lbnQgfHwgdGhpcy50eXBlID09PSB0dC5uYW1lKSBub2RlLmlkID0gdGhpcy5wYXJzZUlkZW50KCk7XG4gIHRoaXMucGFyc2VGdW5jdGlvblBhcmFtcyhub2RlKTtcbiAgdGhpcy5wYXJzZUZ1bmN0aW9uQm9keShub2RlLCBhbGxvd0V4cHJlc3Npb25Cb2R5KTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBpc1N0YXRlbWVudCA/IFwiRnVuY3Rpb25EZWNsYXJhdGlvblwiIDogXCJGdW5jdGlvbkV4cHJlc3Npb25cIik7XG59O1xuXG5wcC5wYXJzZUZ1bmN0aW9uUGFyYW1zID0gZnVuY3Rpb24gKG5vZGUpIHtcbiAgdGhpcy5leHBlY3QodHQucGFyZW5MKTtcbiAgbm9kZS5wYXJhbXMgPSB0aGlzLnBhcnNlQmluZGluZ0xpc3QodHQucGFyZW5SLCBmYWxzZSwgZmFsc2UpO1xufTtcblxuLy8gUGFyc2UgYSBjbGFzcyBkZWNsYXJhdGlvbiBvciBsaXRlcmFsIChkZXBlbmRpbmcgb24gdGhlXG4vLyBgaXNTdGF0ZW1lbnRgIHBhcmFtZXRlcikuXG5cbnBwLnBhcnNlQ2xhc3MgPSBmdW5jdGlvbiAobm9kZSwgaXNTdGF0ZW1lbnQpIHtcbiAgdGhpcy5uZXh0KCk7XG4gIHRoaXMucGFyc2VDbGFzc0lkKG5vZGUsIGlzU3RhdGVtZW50KTtcbiAgdGhpcy5wYXJzZUNsYXNzU3VwZXIobm9kZSk7XG4gIHZhciBjbGFzc0JvZHkgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICB2YXIgaGFkQ29uc3RydWN0b3IgPSBmYWxzZTtcbiAgY2xhc3NCb2R5LmJvZHkgPSBbXTtcbiAgdGhpcy5leHBlY3QodHQuYnJhY2VMKTtcbiAgd2hpbGUgKCF0aGlzLmVhdCh0dC5icmFjZVIpKSB7XG4gICAgaWYgKHRoaXMuZWF0KHR0LnNlbWkpKSBjb250aW51ZTtcbiAgICB2YXIgbWV0aG9kID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgICB2YXIgaXNHZW5lcmF0b3IgPSB0aGlzLmVhdCh0dC5zdGFyKTtcbiAgICB2YXIgaXNNYXliZVN0YXRpYyA9IHRoaXMudHlwZSA9PT0gdHQubmFtZSAmJiB0aGlzLnZhbHVlID09PSBcInN0YXRpY1wiO1xuICAgIHRoaXMucGFyc2VQcm9wZXJ0eU5hbWUobWV0aG9kKTtcbiAgICBtZXRob2RbXCJzdGF0aWNcIl0gPSBpc01heWJlU3RhdGljICYmIHRoaXMudHlwZSAhPT0gdHQucGFyZW5MO1xuICAgIGlmIChtZXRob2RbXCJzdGF0aWNcIl0pIHtcbiAgICAgIGlmIChpc0dlbmVyYXRvcikgdGhpcy51bmV4cGVjdGVkKCk7XG4gICAgICBpc0dlbmVyYXRvciA9IHRoaXMuZWF0KHR0LnN0YXIpO1xuICAgICAgdGhpcy5wYXJzZVByb3BlcnR5TmFtZShtZXRob2QpO1xuICAgIH1cbiAgICBtZXRob2Qua2luZCA9IFwibWV0aG9kXCI7XG4gICAgaWYgKCFtZXRob2QuY29tcHV0ZWQpIHtcbiAgICAgIHZhciBrZXkgPSBtZXRob2Qua2V5O1xuXG4gICAgICB2YXIgaXNHZXRTZXQgPSBmYWxzZTtcbiAgICAgIGlmICghaXNHZW5lcmF0b3IgJiYga2V5LnR5cGUgPT09IFwiSWRlbnRpZmllclwiICYmIHRoaXMudHlwZSAhPT0gdHQucGFyZW5MICYmIChrZXkubmFtZSA9PT0gXCJnZXRcIiB8fCBrZXkubmFtZSA9PT0gXCJzZXRcIikpIHtcbiAgICAgICAgaXNHZXRTZXQgPSB0cnVlO1xuICAgICAgICBtZXRob2Qua2luZCA9IGtleS5uYW1lO1xuICAgICAgICBrZXkgPSB0aGlzLnBhcnNlUHJvcGVydHlOYW1lKG1ldGhvZCk7XG4gICAgICB9XG4gICAgICBpZiAoIW1ldGhvZFtcInN0YXRpY1wiXSAmJiAoa2V5LnR5cGUgPT09IFwiSWRlbnRpZmllclwiICYmIGtleS5uYW1lID09PSBcImNvbnN0cnVjdG9yXCIgfHwga2V5LnR5cGUgPT09IFwiTGl0ZXJhbFwiICYmIGtleS52YWx1ZSA9PT0gXCJjb25zdHJ1Y3RvclwiKSkge1xuICAgICAgICBpZiAoaGFkQ29uc3RydWN0b3IpIHRoaXMucmFpc2Uoa2V5LnN0YXJ0LCBcIkR1cGxpY2F0ZSBjb25zdHJ1Y3RvciBpbiB0aGUgc2FtZSBjbGFzc1wiKTtcbiAgICAgICAgaWYgKGlzR2V0U2V0KSB0aGlzLnJhaXNlKGtleS5zdGFydCwgXCJDb25zdHJ1Y3RvciBjYW4ndCBoYXZlIGdldC9zZXQgbW9kaWZpZXJcIik7XG4gICAgICAgIGlmIChpc0dlbmVyYXRvcikgdGhpcy5yYWlzZShrZXkuc3RhcnQsIFwiQ29uc3RydWN0b3IgY2FuJ3QgYmUgYSBnZW5lcmF0b3JcIik7XG4gICAgICAgIG1ldGhvZC5raW5kID0gXCJjb25zdHJ1Y3RvclwiO1xuICAgICAgICBoYWRDb25zdHJ1Y3RvciA9IHRydWU7XG4gICAgICB9XG4gICAgfVxuICAgIHRoaXMucGFyc2VDbGFzc01ldGhvZChjbGFzc0JvZHksIG1ldGhvZCwgaXNHZW5lcmF0b3IpO1xuICB9XG4gIG5vZGUuYm9keSA9IHRoaXMuZmluaXNoTm9kZShjbGFzc0JvZHksIFwiQ2xhc3NCb2R5XCIpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIGlzU3RhdGVtZW50ID8gXCJDbGFzc0RlY2xhcmF0aW9uXCIgOiBcIkNsYXNzRXhwcmVzc2lvblwiKTtcbn07XG5cbnBwLnBhcnNlQ2xhc3NNZXRob2QgPSBmdW5jdGlvbiAoY2xhc3NCb2R5LCBtZXRob2QsIGlzR2VuZXJhdG9yKSB7XG4gIG1ldGhvZC52YWx1ZSA9IHRoaXMucGFyc2VNZXRob2QoaXNHZW5lcmF0b3IpO1xuICBjbGFzc0JvZHkuYm9keS5wdXNoKHRoaXMuZmluaXNoTm9kZShtZXRob2QsIFwiTWV0aG9kRGVmaW5pdGlvblwiKSk7XG59O1xuXG5wcC5wYXJzZUNsYXNzSWQgPSBmdW5jdGlvbiAobm9kZSwgaXNTdGF0ZW1lbnQpIHtcbiAgbm9kZS5pZCA9IHRoaXMudHlwZSA9PT0gdHQubmFtZSA/IHRoaXMucGFyc2VJZGVudCgpIDogaXNTdGF0ZW1lbnQgPyB0aGlzLnVuZXhwZWN0ZWQoKSA6IG51bGw7XG59O1xuXG5wcC5wYXJzZUNsYXNzU3VwZXIgPSBmdW5jdGlvbiAobm9kZSkge1xuICBub2RlLnN1cGVyQ2xhc3MgPSB0aGlzLmVhdCh0dC5fZXh0ZW5kcykgPyB0aGlzLnBhcnNlRXhwclN1YnNjcmlwdHMoKSA6IG51bGw7XG59O1xuXG4vLyBQYXJzZXMgbW9kdWxlIGV4cG9ydCBkZWNsYXJhdGlvbi5cblxucHAucGFyc2VFeHBvcnQgPSBmdW5jdGlvbiAobm9kZSkge1xuICB0aGlzLm5leHQoKTtcbiAgLy8gZXhwb3J0ICogZnJvbSAnLi4uJ1xuICBpZiAodGhpcy5lYXQodHQuc3RhcikpIHtcbiAgICB0aGlzLmV4cGVjdENvbnRleHR1YWwoXCJmcm9tXCIpO1xuICAgIG5vZGUuc291cmNlID0gdGhpcy50eXBlID09PSB0dC5zdHJpbmcgPyB0aGlzLnBhcnNlRXhwckF0b20oKSA6IHRoaXMudW5leHBlY3RlZCgpO1xuICAgIHRoaXMuc2VtaWNvbG9uKCk7XG4gICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkV4cG9ydEFsbERlY2xhcmF0aW9uXCIpO1xuICB9XG4gIGlmICh0aGlzLmVhdCh0dC5fZGVmYXVsdCkpIHtcbiAgICAvLyBleHBvcnQgZGVmYXVsdCAuLi5cbiAgICB2YXIgZXhwciA9IHRoaXMucGFyc2VNYXliZUFzc2lnbigpO1xuICAgIHZhciBuZWVkc1NlbWkgPSB0cnVlO1xuICAgIGlmIChleHByLnR5cGUgPT0gXCJGdW5jdGlvbkV4cHJlc3Npb25cIiB8fCBleHByLnR5cGUgPT0gXCJDbGFzc0V4cHJlc3Npb25cIikge1xuICAgICAgbmVlZHNTZW1pID0gZmFsc2U7XG4gICAgICBpZiAoZXhwci5pZCkge1xuICAgICAgICBleHByLnR5cGUgPSBleHByLnR5cGUgPT0gXCJGdW5jdGlvbkV4cHJlc3Npb25cIiA/IFwiRnVuY3Rpb25EZWNsYXJhdGlvblwiIDogXCJDbGFzc0RlY2xhcmF0aW9uXCI7XG4gICAgICB9XG4gICAgfVxuICAgIG5vZGUuZGVjbGFyYXRpb24gPSBleHByO1xuICAgIGlmIChuZWVkc1NlbWkpIHRoaXMuc2VtaWNvbG9uKCk7XG4gICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkV4cG9ydERlZmF1bHREZWNsYXJhdGlvblwiKTtcbiAgfVxuICAvLyBleHBvcnQgdmFyfGNvbnN0fGxldHxmdW5jdGlvbnxjbGFzcyAuLi5cbiAgaWYgKHRoaXMuc2hvdWxkUGFyc2VFeHBvcnRTdGF0ZW1lbnQoKSkge1xuICAgIG5vZGUuZGVjbGFyYXRpb24gPSB0aGlzLnBhcnNlU3RhdGVtZW50KHRydWUpO1xuICAgIG5vZGUuc3BlY2lmaWVycyA9IFtdO1xuICAgIG5vZGUuc291cmNlID0gbnVsbDtcbiAgfSBlbHNlIHtcbiAgICAvLyBleHBvcnQgeyB4LCB5IGFzIHogfSBbZnJvbSAnLi4uJ11cbiAgICBub2RlLmRlY2xhcmF0aW9uID0gbnVsbDtcbiAgICBub2RlLnNwZWNpZmllcnMgPSB0aGlzLnBhcnNlRXhwb3J0U3BlY2lmaWVycygpO1xuICAgIGlmICh0aGlzLmVhdENvbnRleHR1YWwoXCJmcm9tXCIpKSB7XG4gICAgICBub2RlLnNvdXJjZSA9IHRoaXMudHlwZSA9PT0gdHQuc3RyaW5nID8gdGhpcy5wYXJzZUV4cHJBdG9tKCkgOiB0aGlzLnVuZXhwZWN0ZWQoKTtcbiAgICB9IGVsc2Uge1xuICAgICAgbm9kZS5zb3VyY2UgPSBudWxsO1xuICAgIH1cbiAgICB0aGlzLnNlbWljb2xvbigpO1xuICB9XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJFeHBvcnROYW1lZERlY2xhcmF0aW9uXCIpO1xufTtcblxucHAuc2hvdWxkUGFyc2VFeHBvcnRTdGF0ZW1lbnQgPSBmdW5jdGlvbiAoKSB7XG4gIHJldHVybiB0aGlzLnR5cGUua2V5d29yZDtcbn07XG5cbi8vIFBhcnNlcyBhIGNvbW1hLXNlcGFyYXRlZCBsaXN0IG9mIG1vZHVsZSBleHBvcnRzLlxuXG5wcC5wYXJzZUV4cG9ydFNwZWNpZmllcnMgPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBub2RlcyA9IFtdLFxuICAgICAgZmlyc3QgPSB0cnVlO1xuICAvLyBleHBvcnQgeyB4LCB5IGFzIHogfSBbZnJvbSAnLi4uJ11cbiAgdGhpcy5leHBlY3QodHQuYnJhY2VMKTtcbiAgd2hpbGUgKCF0aGlzLmVhdCh0dC5icmFjZVIpKSB7XG4gICAgaWYgKCFmaXJzdCkge1xuICAgICAgdGhpcy5leHBlY3QodHQuY29tbWEpO1xuICAgICAgaWYgKHRoaXMuYWZ0ZXJUcmFpbGluZ0NvbW1hKHR0LmJyYWNlUikpIGJyZWFrO1xuICAgIH0gZWxzZSBmaXJzdCA9IGZhbHNlO1xuXG4gICAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICAgIG5vZGUubG9jYWwgPSB0aGlzLnBhcnNlSWRlbnQodGhpcy50eXBlID09PSB0dC5fZGVmYXVsdCk7XG4gICAgbm9kZS5leHBvcnRlZCA9IHRoaXMuZWF0Q29udGV4dHVhbChcImFzXCIpID8gdGhpcy5wYXJzZUlkZW50KHRydWUpIDogbm9kZS5sb2NhbDtcbiAgICBub2Rlcy5wdXNoKHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkV4cG9ydFNwZWNpZmllclwiKSk7XG4gIH1cbiAgcmV0dXJuIG5vZGVzO1xufTtcblxuLy8gUGFyc2VzIGltcG9ydCBkZWNsYXJhdGlvbi5cblxucHAucGFyc2VJbXBvcnQgPSBmdW5jdGlvbiAobm9kZSkge1xuICB0aGlzLm5leHQoKTtcbiAgLy8gaW1wb3J0ICcuLi4nXG4gIGlmICh0aGlzLnR5cGUgPT09IHR0LnN0cmluZykge1xuICAgIG5vZGUuc3BlY2lmaWVycyA9IGVtcHR5O1xuICAgIG5vZGUuc291cmNlID0gdGhpcy5wYXJzZUV4cHJBdG9tKCk7XG4gICAgbm9kZS5raW5kID0gXCJcIjtcbiAgfSBlbHNlIHtcbiAgICBub2RlLnNwZWNpZmllcnMgPSB0aGlzLnBhcnNlSW1wb3J0U3BlY2lmaWVycygpO1xuICAgIHRoaXMuZXhwZWN0Q29udGV4dHVhbChcImZyb21cIik7XG4gICAgbm9kZS5zb3VyY2UgPSB0aGlzLnR5cGUgPT09IHR0LnN0cmluZyA/IHRoaXMucGFyc2VFeHByQXRvbSgpIDogdGhpcy51bmV4cGVjdGVkKCk7XG4gIH1cbiAgdGhpcy5zZW1pY29sb24oKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkltcG9ydERlY2xhcmF0aW9uXCIpO1xufTtcblxuLy8gUGFyc2VzIGEgY29tbWEtc2VwYXJhdGVkIGxpc3Qgb2YgbW9kdWxlIGltcG9ydHMuXG5cbnBwLnBhcnNlSW1wb3J0U3BlY2lmaWVycyA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIG5vZGVzID0gW10sXG4gICAgICBmaXJzdCA9IHRydWU7XG4gIGlmICh0aGlzLnR5cGUgPT09IHR0Lm5hbWUpIHtcbiAgICAvLyBpbXBvcnQgZGVmYXVsdE9iaiwgeyB4LCB5IGFzIHogfSBmcm9tICcuLi4nXG4gICAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICAgIG5vZGUubG9jYWwgPSB0aGlzLnBhcnNlSWRlbnQoKTtcbiAgICB0aGlzLmNoZWNrTFZhbChub2RlLmxvY2FsLCB0cnVlKTtcbiAgICBub2Rlcy5wdXNoKHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkltcG9ydERlZmF1bHRTcGVjaWZpZXJcIikpO1xuICAgIGlmICghdGhpcy5lYXQodHQuY29tbWEpKSByZXR1cm4gbm9kZXM7XG4gIH1cbiAgaWYgKHRoaXMudHlwZSA9PT0gdHQuc3Rhcikge1xuICAgIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgICB0aGlzLm5leHQoKTtcbiAgICB0aGlzLmV4cGVjdENvbnRleHR1YWwoXCJhc1wiKTtcbiAgICBub2RlLmxvY2FsID0gdGhpcy5wYXJzZUlkZW50KCk7XG4gICAgdGhpcy5jaGVja0xWYWwobm9kZS5sb2NhbCwgdHJ1ZSk7XG4gICAgbm9kZXMucHVzaCh0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJJbXBvcnROYW1lc3BhY2VTcGVjaWZpZXJcIikpO1xuICAgIHJldHVybiBub2RlcztcbiAgfVxuICB0aGlzLmV4cGVjdCh0dC5icmFjZUwpO1xuICB3aGlsZSAoIXRoaXMuZWF0KHR0LmJyYWNlUikpIHtcbiAgICBpZiAoIWZpcnN0KSB7XG4gICAgICB0aGlzLmV4cGVjdCh0dC5jb21tYSk7XG4gICAgICBpZiAodGhpcy5hZnRlclRyYWlsaW5nQ29tbWEodHQuYnJhY2VSKSkgYnJlYWs7XG4gICAgfSBlbHNlIGZpcnN0ID0gZmFsc2U7XG5cbiAgICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gICAgbm9kZS5pbXBvcnRlZCA9IHRoaXMucGFyc2VJZGVudCh0cnVlKTtcbiAgICBub2RlLmxvY2FsID0gdGhpcy5lYXRDb250ZXh0dWFsKFwiYXNcIikgPyB0aGlzLnBhcnNlSWRlbnQoKSA6IG5vZGUuaW1wb3J0ZWQ7XG4gICAgdGhpcy5jaGVja0xWYWwobm9kZS5sb2NhbCwgdHJ1ZSk7XG4gICAgbm9kZXMucHVzaCh0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJJbXBvcnRTcGVjaWZpZXJcIikpO1xuICB9XG4gIHJldHVybiBub2Rlcztcbn07XG5cbn0se1wiLi9zdGF0ZVwiOjEzLFwiLi90b2tlbnR5cGVcIjoxNyxcIi4vd2hpdGVzcGFjZVwiOjE5fV0sMTU6W2Z1bmN0aW9uKF9kZXJlcV8sbW9kdWxlLGV4cG9ydHMpe1xuXCJ1c2Ugc3RyaWN0XCI7XG5cbnZhciBfY2xhc3NDYWxsQ2hlY2sgPSBmdW5jdGlvbiAoaW5zdGFuY2UsIENvbnN0cnVjdG9yKSB7IGlmICghKGluc3RhbmNlIGluc3RhbmNlb2YgQ29uc3RydWN0b3IpKSB7IHRocm93IG5ldyBUeXBlRXJyb3IoXCJDYW5ub3QgY2FsbCBhIGNsYXNzIGFzIGEgZnVuY3Rpb25cIik7IH0gfTtcblxuZXhwb3J0cy5fX2VzTW9kdWxlID0gdHJ1ZTtcbi8vIFRoZSBhbGdvcml0aG0gdXNlZCB0byBkZXRlcm1pbmUgd2hldGhlciBhIHJlZ2V4cCBjYW4gYXBwZWFyIGF0IGFcbi8vIGdpdmVuIHBvaW50IGluIHRoZSBwcm9ncmFtIGlzIGxvb3NlbHkgYmFzZWQgb24gc3dlZXQuanMnIGFwcHJvYWNoLlxuLy8gU2VlIGh0dHBzOi8vZ2l0aHViLmNvbS9tb3ppbGxhL3N3ZWV0LmpzL3dpa2kvZGVzaWduXG5cbnZhciBQYXJzZXIgPSBfZGVyZXFfKFwiLi9zdGF0ZVwiKS5QYXJzZXI7XG5cbnZhciB0dCA9IF9kZXJlcV8oXCIuL3Rva2VudHlwZVwiKS50eXBlcztcblxudmFyIGxpbmVCcmVhayA9IF9kZXJlcV8oXCIuL3doaXRlc3BhY2VcIikubGluZUJyZWFrO1xuXG52YXIgVG9rQ29udGV4dCA9IGV4cG9ydHMuVG9rQ29udGV4dCA9IGZ1bmN0aW9uIFRva0NvbnRleHQodG9rZW4sIGlzRXhwciwgcHJlc2VydmVTcGFjZSwgb3ZlcnJpZGUpIHtcbiAgX2NsYXNzQ2FsbENoZWNrKHRoaXMsIFRva0NvbnRleHQpO1xuXG4gIHRoaXMudG9rZW4gPSB0b2tlbjtcbiAgdGhpcy5pc0V4cHIgPSBpc0V4cHI7XG4gIHRoaXMucHJlc2VydmVTcGFjZSA9IHByZXNlcnZlU3BhY2U7XG4gIHRoaXMub3ZlcnJpZGUgPSBvdmVycmlkZTtcbn07XG5cbnZhciB0eXBlcyA9IHtcbiAgYl9zdGF0OiBuZXcgVG9rQ29udGV4dChcIntcIiwgZmFsc2UpLFxuICBiX2V4cHI6IG5ldyBUb2tDb250ZXh0KFwie1wiLCB0cnVlKSxcbiAgYl90bXBsOiBuZXcgVG9rQ29udGV4dChcIiR7XCIsIHRydWUpLFxuICBwX3N0YXQ6IG5ldyBUb2tDb250ZXh0KFwiKFwiLCBmYWxzZSksXG4gIHBfZXhwcjogbmV3IFRva0NvbnRleHQoXCIoXCIsIHRydWUpLFxuICBxX3RtcGw6IG5ldyBUb2tDb250ZXh0KFwiYFwiLCB0cnVlLCB0cnVlLCBmdW5jdGlvbiAocCkge1xuICAgIHJldHVybiBwLnJlYWRUbXBsVG9rZW4oKTtcbiAgfSksXG4gIGZfZXhwcjogbmV3IFRva0NvbnRleHQoXCJmdW5jdGlvblwiLCB0cnVlKVxufTtcblxuZXhwb3J0cy50eXBlcyA9IHR5cGVzO1xudmFyIHBwID0gUGFyc2VyLnByb3RvdHlwZTtcblxucHAuaW5pdGlhbENvbnRleHQgPSBmdW5jdGlvbiAoKSB7XG4gIHJldHVybiBbdHlwZXMuYl9zdGF0XTtcbn07XG5cbnBwLmJyYWNlSXNCbG9jayA9IGZ1bmN0aW9uIChwcmV2VHlwZSkge1xuICB2YXIgcGFyZW50ID0gdW5kZWZpbmVkO1xuICBpZiAocHJldlR5cGUgPT09IHR0LmNvbG9uICYmIChwYXJlbnQgPSB0aGlzLmN1ckNvbnRleHQoKSkudG9rZW4gPT0gXCJ7XCIpIHJldHVybiAhcGFyZW50LmlzRXhwcjtcbiAgaWYgKHByZXZUeXBlID09PSB0dC5fcmV0dXJuKSByZXR1cm4gbGluZUJyZWFrLnRlc3QodGhpcy5pbnB1dC5zbGljZSh0aGlzLmxhc3RUb2tFbmQsIHRoaXMuc3RhcnQpKTtcbiAgaWYgKHByZXZUeXBlID09PSB0dC5fZWxzZSB8fCBwcmV2VHlwZSA9PT0gdHQuc2VtaSB8fCBwcmV2VHlwZSA9PT0gdHQuZW9mKSByZXR1cm4gdHJ1ZTtcbiAgaWYgKHByZXZUeXBlID09IHR0LmJyYWNlTCkgcmV0dXJuIHRoaXMuY3VyQ29udGV4dCgpID09PSB0eXBlcy5iX3N0YXQ7XG4gIHJldHVybiAhdGhpcy5leHByQWxsb3dlZDtcbn07XG5cbnBwLnVwZGF0ZUNvbnRleHQgPSBmdW5jdGlvbiAocHJldlR5cGUpIHtcbiAgdmFyIHVwZGF0ZSA9IHVuZGVmaW5lZCxcbiAgICAgIHR5cGUgPSB0aGlzLnR5cGU7XG4gIGlmICh0eXBlLmtleXdvcmQgJiYgcHJldlR5cGUgPT0gdHQuZG90KSB0aGlzLmV4cHJBbGxvd2VkID0gZmFsc2U7ZWxzZSBpZiAodXBkYXRlID0gdHlwZS51cGRhdGVDb250ZXh0KSB1cGRhdGUuY2FsbCh0aGlzLCBwcmV2VHlwZSk7ZWxzZSB0aGlzLmV4cHJBbGxvd2VkID0gdHlwZS5iZWZvcmVFeHByO1xufTtcblxuLy8gVG9rZW4tc3BlY2lmaWMgY29udGV4dCB1cGRhdGUgY29kZVxuXG50dC5wYXJlblIudXBkYXRlQ29udGV4dCA9IHR0LmJyYWNlUi51cGRhdGVDb250ZXh0ID0gZnVuY3Rpb24gKCkge1xuICBpZiAodGhpcy5jb250ZXh0Lmxlbmd0aCA9PSAxKSB7XG4gICAgdGhpcy5leHByQWxsb3dlZCA9IHRydWU7XG4gICAgcmV0dXJuO1xuICB9XG4gIHZhciBvdXQgPSB0aGlzLmNvbnRleHQucG9wKCk7XG4gIGlmIChvdXQgPT09IHR5cGVzLmJfc3RhdCAmJiB0aGlzLmN1ckNvbnRleHQoKSA9PT0gdHlwZXMuZl9leHByKSB7XG4gICAgdGhpcy5jb250ZXh0LnBvcCgpO1xuICAgIHRoaXMuZXhwckFsbG93ZWQgPSBmYWxzZTtcbiAgfSBlbHNlIGlmIChvdXQgPT09IHR5cGVzLmJfdG1wbCkge1xuICAgIHRoaXMuZXhwckFsbG93ZWQgPSB0cnVlO1xuICB9IGVsc2Uge1xuICAgIHRoaXMuZXhwckFsbG93ZWQgPSAhb3V0LmlzRXhwcjtcbiAgfVxufTtcblxudHQuYnJhY2VMLnVwZGF0ZUNvbnRleHQgPSBmdW5jdGlvbiAocHJldlR5cGUpIHtcbiAgdGhpcy5jb250ZXh0LnB1c2godGhpcy5icmFjZUlzQmxvY2socHJldlR5cGUpID8gdHlwZXMuYl9zdGF0IDogdHlwZXMuYl9leHByKTtcbiAgdGhpcy5leHByQWxsb3dlZCA9IHRydWU7XG59O1xuXG50dC5kb2xsYXJCcmFjZUwudXBkYXRlQ29udGV4dCA9IGZ1bmN0aW9uICgpIHtcbiAgdGhpcy5jb250ZXh0LnB1c2godHlwZXMuYl90bXBsKTtcbiAgdGhpcy5leHByQWxsb3dlZCA9IHRydWU7XG59O1xuXG50dC5wYXJlbkwudXBkYXRlQ29udGV4dCA9IGZ1bmN0aW9uIChwcmV2VHlwZSkge1xuICB2YXIgc3RhdGVtZW50UGFyZW5zID0gcHJldlR5cGUgPT09IHR0Ll9pZiB8fCBwcmV2VHlwZSA9PT0gdHQuX2ZvciB8fCBwcmV2VHlwZSA9PT0gdHQuX3dpdGggfHwgcHJldlR5cGUgPT09IHR0Ll93aGlsZTtcbiAgdGhpcy5jb250ZXh0LnB1c2goc3RhdGVtZW50UGFyZW5zID8gdHlwZXMucF9zdGF0IDogdHlwZXMucF9leHByKTtcbiAgdGhpcy5leHByQWxsb3dlZCA9IHRydWU7XG59O1xuXG50dC5pbmNEZWMudXBkYXRlQ29udGV4dCA9IGZ1bmN0aW9uICgpIHt9O1xuXG50dC5fZnVuY3Rpb24udXBkYXRlQ29udGV4dCA9IGZ1bmN0aW9uICgpIHtcbiAgaWYgKHRoaXMuY3VyQ29udGV4dCgpICE9PSB0eXBlcy5iX3N0YXQpIHRoaXMuY29udGV4dC5wdXNoKHR5cGVzLmZfZXhwcik7XG4gIHRoaXMuZXhwckFsbG93ZWQgPSBmYWxzZTtcbn07XG5cbnR0LmJhY2tRdW90ZS51cGRhdGVDb250ZXh0ID0gZnVuY3Rpb24gKCkge1xuICBpZiAodGhpcy5jdXJDb250ZXh0KCkgPT09IHR5cGVzLnFfdG1wbCkgdGhpcy5jb250ZXh0LnBvcCgpO2Vsc2UgdGhpcy5jb250ZXh0LnB1c2godHlwZXMucV90bXBsKTtcbiAgdGhpcy5leHByQWxsb3dlZCA9IGZhbHNlO1xufTtcblxuLy8gdG9rRXhwckFsbG93ZWQgc3RheXMgdW5jaGFuZ2VkXG5cbn0se1wiLi9zdGF0ZVwiOjEzLFwiLi90b2tlbnR5cGVcIjoxNyxcIi4vd2hpdGVzcGFjZVwiOjE5fV0sMTY6W2Z1bmN0aW9uKF9kZXJlcV8sbW9kdWxlLGV4cG9ydHMpe1xuXCJ1c2Ugc3RyaWN0XCI7XG5cbnZhciBfY2xhc3NDYWxsQ2hlY2sgPSBmdW5jdGlvbiAoaW5zdGFuY2UsIENvbnN0cnVjdG9yKSB7IGlmICghKGluc3RhbmNlIGluc3RhbmNlb2YgQ29uc3RydWN0b3IpKSB7IHRocm93IG5ldyBUeXBlRXJyb3IoXCJDYW5ub3QgY2FsbCBhIGNsYXNzIGFzIGEgZnVuY3Rpb25cIik7IH0gfTtcblxuZXhwb3J0cy5fX2VzTW9kdWxlID0gdHJ1ZTtcblxudmFyIF9pZGVudGlmaWVyID0gX2RlcmVxXyhcIi4vaWRlbnRpZmllclwiKTtcblxudmFyIGlzSWRlbnRpZmllclN0YXJ0ID0gX2lkZW50aWZpZXIuaXNJZGVudGlmaWVyU3RhcnQ7XG52YXIgaXNJZGVudGlmaWVyQ2hhciA9IF9pZGVudGlmaWVyLmlzSWRlbnRpZmllckNoYXI7XG5cbnZhciBfdG9rZW50eXBlID0gX2RlcmVxXyhcIi4vdG9rZW50eXBlXCIpO1xuXG52YXIgdHQgPSBfdG9rZW50eXBlLnR5cGVzO1xudmFyIGtleXdvcmRUeXBlcyA9IF90b2tlbnR5cGUua2V5d29yZHM7XG5cbnZhciBQYXJzZXIgPSBfZGVyZXFfKFwiLi9zdGF0ZVwiKS5QYXJzZXI7XG5cbnZhciBTb3VyY2VMb2NhdGlvbiA9IF9kZXJlcV8oXCIuL2xvY2F0aW9uXCIpLlNvdXJjZUxvY2F0aW9uO1xuXG52YXIgX3doaXRlc3BhY2UgPSBfZGVyZXFfKFwiLi93aGl0ZXNwYWNlXCIpO1xuXG52YXIgbGluZUJyZWFrID0gX3doaXRlc3BhY2UubGluZUJyZWFrO1xudmFyIGxpbmVCcmVha0cgPSBfd2hpdGVzcGFjZS5saW5lQnJlYWtHO1xudmFyIGlzTmV3TGluZSA9IF93aGl0ZXNwYWNlLmlzTmV3TGluZTtcbnZhciBub25BU0NJSXdoaXRlc3BhY2UgPSBfd2hpdGVzcGFjZS5ub25BU0NJSXdoaXRlc3BhY2U7XG5cbi8vIE9iamVjdCB0eXBlIHVzZWQgdG8gcmVwcmVzZW50IHRva2Vucy4gTm90ZSB0aGF0IG5vcm1hbGx5LCB0b2tlbnNcbi8vIHNpbXBseSBleGlzdCBhcyBwcm9wZXJ0aWVzIG9uIHRoZSBwYXJzZXIgb2JqZWN0LiBUaGlzIGlzIG9ubHlcbi8vIHVzZWQgZm9yIHRoZSBvblRva2VuIGNhbGxiYWNrIGFuZCB0aGUgZXh0ZXJuYWwgdG9rZW5pemVyLlxuXG52YXIgVG9rZW4gPSBleHBvcnRzLlRva2VuID0gZnVuY3Rpb24gVG9rZW4ocCkge1xuICBfY2xhc3NDYWxsQ2hlY2sodGhpcywgVG9rZW4pO1xuXG4gIHRoaXMudHlwZSA9IHAudHlwZTtcbiAgdGhpcy52YWx1ZSA9IHAudmFsdWU7XG4gIHRoaXMuc3RhcnQgPSBwLnN0YXJ0O1xuICB0aGlzLmVuZCA9IHAuZW5kO1xuICBpZiAocC5vcHRpb25zLmxvY2F0aW9ucykgdGhpcy5sb2MgPSBuZXcgU291cmNlTG9jYXRpb24ocCwgcC5zdGFydExvYywgcC5lbmRMb2MpO1xuICBpZiAocC5vcHRpb25zLnJhbmdlcykgdGhpcy5yYW5nZSA9IFtwLnN0YXJ0LCBwLmVuZF07XG59O1xuXG4vLyAjIyBUb2tlbml6ZXJcblxudmFyIHBwID0gUGFyc2VyLnByb3RvdHlwZTtcblxuLy8gQXJlIHdlIHJ1bm5pbmcgdW5kZXIgUmhpbm8/XG52YXIgaXNSaGlubyA9IHR5cGVvZiBQYWNrYWdlcyAhPT0gXCJ1bmRlZmluZWRcIjtcblxuLy8gTW92ZSB0byB0aGUgbmV4dCB0b2tlblxuXG5wcC5uZXh0ID0gZnVuY3Rpb24gKCkge1xuICBpZiAodGhpcy5vcHRpb25zLm9uVG9rZW4pIHRoaXMub3B0aW9ucy5vblRva2VuKG5ldyBUb2tlbih0aGlzKSk7XG5cbiAgdGhpcy5sYXN0VG9rRW5kID0gdGhpcy5lbmQ7XG4gIHRoaXMubGFzdFRva1N0YXJ0ID0gdGhpcy5zdGFydDtcbiAgdGhpcy5sYXN0VG9rRW5kTG9jID0gdGhpcy5lbmRMb2M7XG4gIHRoaXMubGFzdFRva1N0YXJ0TG9jID0gdGhpcy5zdGFydExvYztcbiAgdGhpcy5uZXh0VG9rZW4oKTtcbn07XG5cbnBwLmdldFRva2VuID0gZnVuY3Rpb24gKCkge1xuICB0aGlzLm5leHQoKTtcbiAgcmV0dXJuIG5ldyBUb2tlbih0aGlzKTtcbn07XG5cbi8vIElmIHdlJ3JlIGluIGFuIEVTNiBlbnZpcm9ubWVudCwgbWFrZSBwYXJzZXJzIGl0ZXJhYmxlXG5pZiAodHlwZW9mIFN5bWJvbCAhPT0gXCJ1bmRlZmluZWRcIikgcHBbU3ltYm9sLml0ZXJhdG9yXSA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIHNlbGYgPSB0aGlzO1xuICByZXR1cm4geyBuZXh0OiBmdW5jdGlvbiBuZXh0KCkge1xuICAgICAgdmFyIHRva2VuID0gc2VsZi5nZXRUb2tlbigpO1xuICAgICAgcmV0dXJuIHtcbiAgICAgICAgZG9uZTogdG9rZW4udHlwZSA9PT0gdHQuZW9mLFxuICAgICAgICB2YWx1ZTogdG9rZW5cbiAgICAgIH07XG4gICAgfSB9O1xufTtcblxuLy8gVG9nZ2xlIHN0cmljdCBtb2RlLiBSZS1yZWFkcyB0aGUgbmV4dCBudW1iZXIgb3Igc3RyaW5nIHRvIHBsZWFzZVxuLy8gcGVkYW50aWMgdGVzdHMgKGBcInVzZSBzdHJpY3RcIjsgMDEwO2Agc2hvdWxkIGZhaWwpLlxuXG5wcC5zZXRTdHJpY3QgPSBmdW5jdGlvbiAoc3RyaWN0KSB7XG4gIHRoaXMuc3RyaWN0ID0gc3RyaWN0O1xuICBpZiAodGhpcy50eXBlICE9PSB0dC5udW0gJiYgdGhpcy50eXBlICE9PSB0dC5zdHJpbmcpIHJldHVybjtcbiAgdGhpcy5wb3MgPSB0aGlzLnN0YXJ0O1xuICBpZiAodGhpcy5vcHRpb25zLmxvY2F0aW9ucykge1xuICAgIHdoaWxlICh0aGlzLnBvcyA8IHRoaXMubGluZVN0YXJ0KSB7XG4gICAgICB0aGlzLmxpbmVTdGFydCA9IHRoaXMuaW5wdXQubGFzdEluZGV4T2YoXCJcXG5cIiwgdGhpcy5saW5lU3RhcnQgLSAyKSArIDE7XG4gICAgICAtLXRoaXMuY3VyTGluZTtcbiAgICB9XG4gIH1cbiAgdGhpcy5uZXh0VG9rZW4oKTtcbn07XG5cbnBwLmN1ckNvbnRleHQgPSBmdW5jdGlvbiAoKSB7XG4gIHJldHVybiB0aGlzLmNvbnRleHRbdGhpcy5jb250ZXh0Lmxlbmd0aCAtIDFdO1xufTtcblxuLy8gUmVhZCBhIHNpbmdsZSB0b2tlbiwgdXBkYXRpbmcgdGhlIHBhcnNlciBvYmplY3QncyB0b2tlbi1yZWxhdGVkXG4vLyBwcm9wZXJ0aWVzLlxuXG5wcC5uZXh0VG9rZW4gPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBjdXJDb250ZXh0ID0gdGhpcy5jdXJDb250ZXh0KCk7XG4gIGlmICghY3VyQ29udGV4dCB8fCAhY3VyQ29udGV4dC5wcmVzZXJ2ZVNwYWNlKSB0aGlzLnNraXBTcGFjZSgpO1xuXG4gIHRoaXMuc3RhcnQgPSB0aGlzLnBvcztcbiAgaWYgKHRoaXMub3B0aW9ucy5sb2NhdGlvbnMpIHRoaXMuc3RhcnRMb2MgPSB0aGlzLmN1clBvc2l0aW9uKCk7XG4gIGlmICh0aGlzLnBvcyA+PSB0aGlzLmlucHV0Lmxlbmd0aCkgcmV0dXJuIHRoaXMuZmluaXNoVG9rZW4odHQuZW9mKTtcblxuICBpZiAoY3VyQ29udGV4dC5vdmVycmlkZSkgcmV0dXJuIGN1ckNvbnRleHQub3ZlcnJpZGUodGhpcyk7ZWxzZSB0aGlzLnJlYWRUb2tlbih0aGlzLmZ1bGxDaGFyQ29kZUF0UG9zKCkpO1xufTtcblxucHAucmVhZFRva2VuID0gZnVuY3Rpb24gKGNvZGUpIHtcbiAgLy8gSWRlbnRpZmllciBvciBrZXl3b3JkLiAnXFx1WFhYWCcgc2VxdWVuY2VzIGFyZSBhbGxvd2VkIGluXG4gIC8vIGlkZW50aWZpZXJzLCBzbyAnXFwnIGFsc28gZGlzcGF0Y2hlcyB0byB0aGF0LlxuICBpZiAoaXNJZGVudGlmaWVyU3RhcnQoY29kZSwgdGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYpIHx8IGNvZGUgPT09IDkyIC8qICdcXCcgKi8pIHJldHVybiB0aGlzLnJlYWRXb3JkKCk7XG5cbiAgcmV0dXJuIHRoaXMuZ2V0VG9rZW5Gcm9tQ29kZShjb2RlKTtcbn07XG5cbnBwLmZ1bGxDaGFyQ29kZUF0UG9zID0gZnVuY3Rpb24gKCkge1xuICB2YXIgY29kZSA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyk7XG4gIGlmIChjb2RlIDw9IDU1Mjk1IHx8IGNvZGUgPj0gNTczNDQpIHJldHVybiBjb2RlO1xuICB2YXIgbmV4dCA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIDEpO1xuICByZXR1cm4gKGNvZGUgPDwgMTApICsgbmV4dCAtIDU2NjEzODg4O1xufTtcblxucHAuc2tpcEJsb2NrQ29tbWVudCA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIHN0YXJ0TG9jID0gdGhpcy5vcHRpb25zLm9uQ29tbWVudCAmJiB0aGlzLm9wdGlvbnMubG9jYXRpb25zICYmIHRoaXMuY3VyUG9zaXRpb24oKTtcbiAgdmFyIHN0YXJ0ID0gdGhpcy5wb3MsXG4gICAgICBlbmQgPSB0aGlzLmlucHV0LmluZGV4T2YoXCIqL1wiLCB0aGlzLnBvcyArPSAyKTtcbiAgaWYgKGVuZCA9PT0gLTEpIHRoaXMucmFpc2UodGhpcy5wb3MgLSAyLCBcIlVudGVybWluYXRlZCBjb21tZW50XCIpO1xuICB0aGlzLnBvcyA9IGVuZCArIDI7XG4gIGlmICh0aGlzLm9wdGlvbnMubG9jYXRpb25zKSB7XG4gICAgbGluZUJyZWFrRy5sYXN0SW5kZXggPSBzdGFydDtcbiAgICB2YXIgbWF0Y2ggPSB1bmRlZmluZWQ7XG4gICAgd2hpbGUgKChtYXRjaCA9IGxpbmVCcmVha0cuZXhlYyh0aGlzLmlucHV0KSkgJiYgbWF0Y2guaW5kZXggPCB0aGlzLnBvcykge1xuICAgICAgKyt0aGlzLmN1ckxpbmU7XG4gICAgICB0aGlzLmxpbmVTdGFydCA9IG1hdGNoLmluZGV4ICsgbWF0Y2hbMF0ubGVuZ3RoO1xuICAgIH1cbiAgfVxuICBpZiAodGhpcy5vcHRpb25zLm9uQ29tbWVudCkgdGhpcy5vcHRpb25zLm9uQ29tbWVudCh0cnVlLCB0aGlzLmlucHV0LnNsaWNlKHN0YXJ0ICsgMiwgZW5kKSwgc3RhcnQsIHRoaXMucG9zLCBzdGFydExvYywgdGhpcy5vcHRpb25zLmxvY2F0aW9ucyAmJiB0aGlzLmN1clBvc2l0aW9uKCkpO1xufTtcblxucHAuc2tpcExpbmVDb21tZW50ID0gZnVuY3Rpb24gKHN0YXJ0U2tpcCkge1xuICB2YXIgc3RhcnQgPSB0aGlzLnBvcztcbiAgdmFyIHN0YXJ0TG9jID0gdGhpcy5vcHRpb25zLm9uQ29tbWVudCAmJiB0aGlzLm9wdGlvbnMubG9jYXRpb25zICYmIHRoaXMuY3VyUG9zaXRpb24oKTtcbiAgdmFyIGNoID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICs9IHN0YXJ0U2tpcCk7XG4gIHdoaWxlICh0aGlzLnBvcyA8IHRoaXMuaW5wdXQubGVuZ3RoICYmIGNoICE9PSAxMCAmJiBjaCAhPT0gMTMgJiYgY2ggIT09IDgyMzIgJiYgY2ggIT09IDgyMzMpIHtcbiAgICArK3RoaXMucG9zO1xuICAgIGNoID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zKTtcbiAgfVxuICBpZiAodGhpcy5vcHRpb25zLm9uQ29tbWVudCkgdGhpcy5vcHRpb25zLm9uQ29tbWVudChmYWxzZSwgdGhpcy5pbnB1dC5zbGljZShzdGFydCArIHN0YXJ0U2tpcCwgdGhpcy5wb3MpLCBzdGFydCwgdGhpcy5wb3MsIHN0YXJ0TG9jLCB0aGlzLm9wdGlvbnMubG9jYXRpb25zICYmIHRoaXMuY3VyUG9zaXRpb24oKSk7XG59O1xuXG4vLyBDYWxsZWQgYXQgdGhlIHN0YXJ0IG9mIHRoZSBwYXJzZSBhbmQgYWZ0ZXIgZXZlcnkgdG9rZW4uIFNraXBzXG4vLyB3aGl0ZXNwYWNlIGFuZCBjb21tZW50cywgYW5kLlxuXG5wcC5za2lwU3BhY2UgPSBmdW5jdGlvbiAoKSB7XG4gIHdoaWxlICh0aGlzLnBvcyA8IHRoaXMuaW5wdXQubGVuZ3RoKSB7XG4gICAgdmFyIGNoID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zKTtcbiAgICBpZiAoY2ggPT09IDMyKSB7XG4gICAgICAvLyAnICdcbiAgICAgICsrdGhpcy5wb3M7XG4gICAgfSBlbHNlIGlmIChjaCA9PT0gMTMpIHtcbiAgICAgICsrdGhpcy5wb3M7XG4gICAgICB2YXIgbmV4dCA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyk7XG4gICAgICBpZiAobmV4dCA9PT0gMTApIHtcbiAgICAgICAgKyt0aGlzLnBvcztcbiAgICAgIH1cbiAgICAgIGlmICh0aGlzLm9wdGlvbnMubG9jYXRpb25zKSB7XG4gICAgICAgICsrdGhpcy5jdXJMaW5lO1xuICAgICAgICB0aGlzLmxpbmVTdGFydCA9IHRoaXMucG9zO1xuICAgICAgfVxuICAgIH0gZWxzZSBpZiAoY2ggPT09IDEwIHx8IGNoID09PSA4MjMyIHx8IGNoID09PSA4MjMzKSB7XG4gICAgICArK3RoaXMucG9zO1xuICAgICAgaWYgKHRoaXMub3B0aW9ucy5sb2NhdGlvbnMpIHtcbiAgICAgICAgKyt0aGlzLmN1ckxpbmU7XG4gICAgICAgIHRoaXMubGluZVN0YXJ0ID0gdGhpcy5wb3M7XG4gICAgICB9XG4gICAgfSBlbHNlIGlmIChjaCA+IDggJiYgY2ggPCAxNCkge1xuICAgICAgKyt0aGlzLnBvcztcbiAgICB9IGVsc2UgaWYgKGNoID09PSA0Nykge1xuICAgICAgLy8gJy8nXG4gICAgICB2YXIgbmV4dCA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIDEpO1xuICAgICAgaWYgKG5leHQgPT09IDQyKSB7XG4gICAgICAgIC8vICcqJ1xuICAgICAgICB0aGlzLnNraXBCbG9ja0NvbW1lbnQoKTtcbiAgICAgIH0gZWxzZSBpZiAobmV4dCA9PT0gNDcpIHtcbiAgICAgICAgLy8gJy8nXG4gICAgICAgIHRoaXMuc2tpcExpbmVDb21tZW50KDIpO1xuICAgICAgfSBlbHNlIGJyZWFrO1xuICAgIH0gZWxzZSBpZiAoY2ggPT09IDE2MCkge1xuICAgICAgLy8gJ1xceGEwJ1xuICAgICAgKyt0aGlzLnBvcztcbiAgICB9IGVsc2UgaWYgKGNoID49IDU3NjAgJiYgbm9uQVNDSUl3aGl0ZXNwYWNlLnRlc3QoU3RyaW5nLmZyb21DaGFyQ29kZShjaCkpKSB7XG4gICAgICArK3RoaXMucG9zO1xuICAgIH0gZWxzZSB7XG4gICAgICBicmVhaztcbiAgICB9XG4gIH1cbn07XG5cbi8vIENhbGxlZCBhdCB0aGUgZW5kIG9mIGV2ZXJ5IHRva2VuLiBTZXRzIGBlbmRgLCBgdmFsYCwgYW5kXG4vLyBtYWludGFpbnMgYGNvbnRleHRgIGFuZCBgZXhwckFsbG93ZWRgLCBhbmQgc2tpcHMgdGhlIHNwYWNlIGFmdGVyXG4vLyB0aGUgdG9rZW4sIHNvIHRoYXQgdGhlIG5leHQgb25lJ3MgYHN0YXJ0YCB3aWxsIHBvaW50IGF0IHRoZVxuLy8gcmlnaHQgcG9zaXRpb24uXG5cbnBwLmZpbmlzaFRva2VuID0gZnVuY3Rpb24gKHR5cGUsIHZhbCkge1xuICB0aGlzLmVuZCA9IHRoaXMucG9zO1xuICBpZiAodGhpcy5vcHRpb25zLmxvY2F0aW9ucykgdGhpcy5lbmRMb2MgPSB0aGlzLmN1clBvc2l0aW9uKCk7XG4gIHZhciBwcmV2VHlwZSA9IHRoaXMudHlwZTtcbiAgdGhpcy50eXBlID0gdHlwZTtcbiAgdGhpcy52YWx1ZSA9IHZhbDtcblxuICB0aGlzLnVwZGF0ZUNvbnRleHQocHJldlR5cGUpO1xufTtcblxuLy8gIyMjIFRva2VuIHJlYWRpbmdcblxuLy8gVGhpcyBpcyB0aGUgZnVuY3Rpb24gdGhhdCBpcyBjYWxsZWQgdG8gZmV0Y2ggdGhlIG5leHQgdG9rZW4uIEl0XG4vLyBpcyBzb21ld2hhdCBvYnNjdXJlLCBiZWNhdXNlIGl0IHdvcmtzIGluIGNoYXJhY3RlciBjb2RlcyByYXRoZXJcbi8vIHRoYW4gY2hhcmFjdGVycywgYW5kIGJlY2F1c2Ugb3BlcmF0b3IgcGFyc2luZyBoYXMgYmVlbiBpbmxpbmVkXG4vLyBpbnRvIGl0LlxuLy9cbi8vIEFsbCBpbiB0aGUgbmFtZSBvZiBzcGVlZC5cbi8vXG5wcC5yZWFkVG9rZW5fZG90ID0gZnVuY3Rpb24gKCkge1xuICB2YXIgbmV4dCA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIDEpO1xuICBpZiAobmV4dCA+PSA0OCAmJiBuZXh0IDw9IDU3KSByZXR1cm4gdGhpcy5yZWFkTnVtYmVyKHRydWUpO1xuICB2YXIgbmV4dDIgPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAyKTtcbiAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2ICYmIG5leHQgPT09IDQ2ICYmIG5leHQyID09PSA0Nikge1xuICAgIC8vIDQ2ID0gZG90ICcuJ1xuICAgIHRoaXMucG9zICs9IDM7XG4gICAgcmV0dXJuIHRoaXMuZmluaXNoVG9rZW4odHQuZWxsaXBzaXMpO1xuICB9IGVsc2Uge1xuICAgICsrdGhpcy5wb3M7XG4gICAgcmV0dXJuIHRoaXMuZmluaXNoVG9rZW4odHQuZG90KTtcbiAgfVxufTtcblxucHAucmVhZFRva2VuX3NsYXNoID0gZnVuY3Rpb24gKCkge1xuICAvLyAnLydcbiAgdmFyIG5leHQgPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAxKTtcbiAgaWYgKHRoaXMuZXhwckFsbG93ZWQpIHtcbiAgICArK3RoaXMucG9zO3JldHVybiB0aGlzLnJlYWRSZWdleHAoKTtcbiAgfVxuICBpZiAobmV4dCA9PT0gNjEpIHJldHVybiB0aGlzLmZpbmlzaE9wKHR0LmFzc2lnbiwgMik7XG4gIHJldHVybiB0aGlzLmZpbmlzaE9wKHR0LnNsYXNoLCAxKTtcbn07XG5cbnBwLnJlYWRUb2tlbl9tdWx0X21vZHVsbyA9IGZ1bmN0aW9uIChjb2RlKSB7XG4gIC8vICclKidcbiAgdmFyIG5leHQgPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAxKTtcbiAgaWYgKG5leHQgPT09IDYxKSByZXR1cm4gdGhpcy5maW5pc2hPcCh0dC5hc3NpZ24sIDIpO1xuICByZXR1cm4gdGhpcy5maW5pc2hPcChjb2RlID09PSA0MiA/IHR0LnN0YXIgOiB0dC5tb2R1bG8sIDEpO1xufTtcblxucHAucmVhZFRva2VuX3BpcGVfYW1wID0gZnVuY3Rpb24gKGNvZGUpIHtcbiAgLy8gJ3wmJ1xuICB2YXIgbmV4dCA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIDEpO1xuICBpZiAobmV4dCA9PT0gY29kZSkgcmV0dXJuIHRoaXMuZmluaXNoT3AoY29kZSA9PT0gMTI0ID8gdHQubG9naWNhbE9SIDogdHQubG9naWNhbEFORCwgMik7XG4gIGlmIChuZXh0ID09PSA2MSkgcmV0dXJuIHRoaXMuZmluaXNoT3AodHQuYXNzaWduLCAyKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoT3AoY29kZSA9PT0gMTI0ID8gdHQuYml0d2lzZU9SIDogdHQuYml0d2lzZUFORCwgMSk7XG59O1xuXG5wcC5yZWFkVG9rZW5fY2FyZXQgPSBmdW5jdGlvbiAoKSB7XG4gIC8vICdeJ1xuICB2YXIgbmV4dCA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIDEpO1xuICBpZiAobmV4dCA9PT0gNjEpIHJldHVybiB0aGlzLmZpbmlzaE9wKHR0LmFzc2lnbiwgMik7XG4gIHJldHVybiB0aGlzLmZpbmlzaE9wKHR0LmJpdHdpc2VYT1IsIDEpO1xufTtcblxucHAucmVhZFRva2VuX3BsdXNfbWluID0gZnVuY3Rpb24gKGNvZGUpIHtcbiAgLy8gJystJ1xuICB2YXIgbmV4dCA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIDEpO1xuICBpZiAobmV4dCA9PT0gY29kZSkge1xuICAgIGlmIChuZXh0ID09IDQ1ICYmIHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIDIpID09IDYyICYmIGxpbmVCcmVhay50ZXN0KHRoaXMuaW5wdXQuc2xpY2UodGhpcy5sYXN0VG9rRW5kLCB0aGlzLnBvcykpKSB7XG4gICAgICAvLyBBIGAtLT5gIGxpbmUgY29tbWVudFxuICAgICAgdGhpcy5za2lwTGluZUNvbW1lbnQoMyk7XG4gICAgICB0aGlzLnNraXBTcGFjZSgpO1xuICAgICAgcmV0dXJuIHRoaXMubmV4dFRva2VuKCk7XG4gICAgfVxuICAgIHJldHVybiB0aGlzLmZpbmlzaE9wKHR0LmluY0RlYywgMik7XG4gIH1cbiAgaWYgKG5leHQgPT09IDYxKSByZXR1cm4gdGhpcy5maW5pc2hPcCh0dC5hc3NpZ24sIDIpO1xuICByZXR1cm4gdGhpcy5maW5pc2hPcCh0dC5wbHVzTWluLCAxKTtcbn07XG5cbnBwLnJlYWRUb2tlbl9sdF9ndCA9IGZ1bmN0aW9uIChjb2RlKSB7XG4gIC8vICc8PidcbiAgdmFyIG5leHQgPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAxKTtcbiAgdmFyIHNpemUgPSAxO1xuICBpZiAobmV4dCA9PT0gY29kZSkge1xuICAgIHNpemUgPSBjb2RlID09PSA2MiAmJiB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAyKSA9PT0gNjIgPyAzIDogMjtcbiAgICBpZiAodGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgc2l6ZSkgPT09IDYxKSByZXR1cm4gdGhpcy5maW5pc2hPcCh0dC5hc3NpZ24sIHNpemUgKyAxKTtcbiAgICByZXR1cm4gdGhpcy5maW5pc2hPcCh0dC5iaXRTaGlmdCwgc2l6ZSk7XG4gIH1cbiAgaWYgKG5leHQgPT0gMzMgJiYgY29kZSA9PSA2MCAmJiB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAyKSA9PSA0NSAmJiB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAzKSA9PSA0NSkge1xuICAgIGlmICh0aGlzLmluTW9kdWxlKSB0aGlzLnVuZXhwZWN0ZWQoKTtcbiAgICAvLyBgPCEtLWAsIGFuIFhNTC1zdHlsZSBjb21tZW50IHRoYXQgc2hvdWxkIGJlIGludGVycHJldGVkIGFzIGEgbGluZSBjb21tZW50XG4gICAgdGhpcy5za2lwTGluZUNvbW1lbnQoNCk7XG4gICAgdGhpcy5za2lwU3BhY2UoKTtcbiAgICByZXR1cm4gdGhpcy5uZXh0VG9rZW4oKTtcbiAgfVxuICBpZiAobmV4dCA9PT0gNjEpIHNpemUgPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAyKSA9PT0gNjEgPyAzIDogMjtcbiAgcmV0dXJuIHRoaXMuZmluaXNoT3AodHQucmVsYXRpb25hbCwgc2l6ZSk7XG59O1xuXG5wcC5yZWFkVG9rZW5fZXFfZXhjbCA9IGZ1bmN0aW9uIChjb2RlKSB7XG4gIC8vICc9ISdcbiAgdmFyIG5leHQgPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAxKTtcbiAgaWYgKG5leHQgPT09IDYxKSByZXR1cm4gdGhpcy5maW5pc2hPcCh0dC5lcXVhbGl0eSwgdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMikgPT09IDYxID8gMyA6IDIpO1xuICBpZiAoY29kZSA9PT0gNjEgJiYgbmV4dCA9PT0gNjIgJiYgdGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYpIHtcbiAgICAvLyAnPT4nXG4gICAgdGhpcy5wb3MgKz0gMjtcbiAgICByZXR1cm4gdGhpcy5maW5pc2hUb2tlbih0dC5hcnJvdyk7XG4gIH1cbiAgcmV0dXJuIHRoaXMuZmluaXNoT3AoY29kZSA9PT0gNjEgPyB0dC5lcSA6IHR0LnByZWZpeCwgMSk7XG59O1xuXG5wcC5nZXRUb2tlbkZyb21Db2RlID0gZnVuY3Rpb24gKGNvZGUpIHtcbiAgc3dpdGNoIChjb2RlKSB7XG4gICAgLy8gVGhlIGludGVycHJldGF0aW9uIG9mIGEgZG90IGRlcGVuZHMgb24gd2hldGhlciBpdCBpcyBmb2xsb3dlZFxuICAgIC8vIGJ5IGEgZGlnaXQgb3IgYW5vdGhlciB0d28gZG90cy5cbiAgICBjYXNlIDQ2OlxuICAgICAgLy8gJy4nXG4gICAgICByZXR1cm4gdGhpcy5yZWFkVG9rZW5fZG90KCk7XG5cbiAgICAvLyBQdW5jdHVhdGlvbiB0b2tlbnMuXG4gICAgY2FzZSA0MDpcbiAgICAgICsrdGhpcy5wb3M7cmV0dXJuIHRoaXMuZmluaXNoVG9rZW4odHQucGFyZW5MKTtcbiAgICBjYXNlIDQxOlxuICAgICAgKyt0aGlzLnBvcztyZXR1cm4gdGhpcy5maW5pc2hUb2tlbih0dC5wYXJlblIpO1xuICAgIGNhc2UgNTk6XG4gICAgICArK3RoaXMucG9zO3JldHVybiB0aGlzLmZpbmlzaFRva2VuKHR0LnNlbWkpO1xuICAgIGNhc2UgNDQ6XG4gICAgICArK3RoaXMucG9zO3JldHVybiB0aGlzLmZpbmlzaFRva2VuKHR0LmNvbW1hKTtcbiAgICBjYXNlIDkxOlxuICAgICAgKyt0aGlzLnBvcztyZXR1cm4gdGhpcy5maW5pc2hUb2tlbih0dC5icmFja2V0TCk7XG4gICAgY2FzZSA5MzpcbiAgICAgICsrdGhpcy5wb3M7cmV0dXJuIHRoaXMuZmluaXNoVG9rZW4odHQuYnJhY2tldFIpO1xuICAgIGNhc2UgMTIzOlxuICAgICAgKyt0aGlzLnBvcztyZXR1cm4gdGhpcy5maW5pc2hUb2tlbih0dC5icmFjZUwpO1xuICAgIGNhc2UgMTI1OlxuICAgICAgKyt0aGlzLnBvcztyZXR1cm4gdGhpcy5maW5pc2hUb2tlbih0dC5icmFjZVIpO1xuICAgIGNhc2UgNTg6XG4gICAgICArK3RoaXMucG9zO3JldHVybiB0aGlzLmZpbmlzaFRva2VuKHR0LmNvbG9uKTtcbiAgICBjYXNlIDYzOlxuICAgICAgKyt0aGlzLnBvcztyZXR1cm4gdGhpcy5maW5pc2hUb2tlbih0dC5xdWVzdGlvbik7XG5cbiAgICBjYXNlIDk2OlxuICAgICAgLy8gJ2AnXG4gICAgICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uIDwgNikgYnJlYWs7XG4gICAgICArK3RoaXMucG9zO1xuICAgICAgcmV0dXJuIHRoaXMuZmluaXNoVG9rZW4odHQuYmFja1F1b3RlKTtcblxuICAgIGNhc2UgNDg6XG4gICAgICAvLyAnMCdcbiAgICAgIHZhciBuZXh0ID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMSk7XG4gICAgICBpZiAobmV4dCA9PT0gMTIwIHx8IG5leHQgPT09IDg4KSByZXR1cm4gdGhpcy5yZWFkUmFkaXhOdW1iZXIoMTYpOyAvLyAnMHgnLCAnMFgnIC0gaGV4IG51bWJlclxuICAgICAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KSB7XG4gICAgICAgIGlmIChuZXh0ID09PSAxMTEgfHwgbmV4dCA9PT0gNzkpIHJldHVybiB0aGlzLnJlYWRSYWRpeE51bWJlcig4KTsgLy8gJzBvJywgJzBPJyAtIG9jdGFsIG51bWJlclxuICAgICAgICBpZiAobmV4dCA9PT0gOTggfHwgbmV4dCA9PT0gNjYpIHJldHVybiB0aGlzLnJlYWRSYWRpeE51bWJlcigyKTsgLy8gJzBiJywgJzBCJyAtIGJpbmFyeSBudW1iZXJcbiAgICAgIH1cbiAgICAvLyBBbnl0aGluZyBlbHNlIGJlZ2lubmluZyB3aXRoIGEgZGlnaXQgaXMgYW4gaW50ZWdlciwgb2N0YWxcbiAgICAvLyBudW1iZXIsIG9yIGZsb2F0LlxuICAgIGNhc2UgNDk6Y2FzZSA1MDpjYXNlIDUxOmNhc2UgNTI6Y2FzZSA1MzpjYXNlIDU0OmNhc2UgNTU6Y2FzZSA1NjpjYXNlIDU3OlxuICAgICAgLy8gMS05XG4gICAgICByZXR1cm4gdGhpcy5yZWFkTnVtYmVyKGZhbHNlKTtcblxuICAgIC8vIFF1b3RlcyBwcm9kdWNlIHN0cmluZ3MuXG4gICAgY2FzZSAzNDpjYXNlIDM5OlxuICAgICAgLy8gJ1wiJywgXCInXCJcbiAgICAgIHJldHVybiB0aGlzLnJlYWRTdHJpbmcoY29kZSk7XG5cbiAgICAvLyBPcGVyYXRvcnMgYXJlIHBhcnNlZCBpbmxpbmUgaW4gdGlueSBzdGF0ZSBtYWNoaW5lcy4gJz0nICg2MSkgaXNcbiAgICAvLyBvZnRlbiByZWZlcnJlZCB0by4gYGZpbmlzaE9wYCBzaW1wbHkgc2tpcHMgdGhlIGFtb3VudCBvZlxuICAgIC8vIGNoYXJhY3RlcnMgaXQgaXMgZ2l2ZW4gYXMgc2Vjb25kIGFyZ3VtZW50LCBhbmQgcmV0dXJucyBhIHRva2VuXG4gICAgLy8gb2YgdGhlIHR5cGUgZ2l2ZW4gYnkgaXRzIGZpcnN0IGFyZ3VtZW50LlxuXG4gICAgY2FzZSA0NzpcbiAgICAgIC8vICcvJ1xuICAgICAgcmV0dXJuIHRoaXMucmVhZFRva2VuX3NsYXNoKCk7XG5cbiAgICBjYXNlIDM3OmNhc2UgNDI6XG4gICAgICAvLyAnJSonXG4gICAgICByZXR1cm4gdGhpcy5yZWFkVG9rZW5fbXVsdF9tb2R1bG8oY29kZSk7XG5cbiAgICBjYXNlIDEyNDpjYXNlIDM4OlxuICAgICAgLy8gJ3wmJ1xuICAgICAgcmV0dXJuIHRoaXMucmVhZFRva2VuX3BpcGVfYW1wKGNvZGUpO1xuXG4gICAgY2FzZSA5NDpcbiAgICAgIC8vICdeJ1xuICAgICAgcmV0dXJuIHRoaXMucmVhZFRva2VuX2NhcmV0KCk7XG5cbiAgICBjYXNlIDQzOmNhc2UgNDU6XG4gICAgICAvLyAnKy0nXG4gICAgICByZXR1cm4gdGhpcy5yZWFkVG9rZW5fcGx1c19taW4oY29kZSk7XG5cbiAgICBjYXNlIDYwOmNhc2UgNjI6XG4gICAgICAvLyAnPD4nXG4gICAgICByZXR1cm4gdGhpcy5yZWFkVG9rZW5fbHRfZ3QoY29kZSk7XG5cbiAgICBjYXNlIDYxOmNhc2UgMzM6XG4gICAgICAvLyAnPSEnXG4gICAgICByZXR1cm4gdGhpcy5yZWFkVG9rZW5fZXFfZXhjbChjb2RlKTtcblxuICAgIGNhc2UgMTI2OlxuICAgICAgLy8gJ34nXG4gICAgICByZXR1cm4gdGhpcy5maW5pc2hPcCh0dC5wcmVmaXgsIDEpO1xuICB9XG5cbiAgdGhpcy5yYWlzZSh0aGlzLnBvcywgXCJVbmV4cGVjdGVkIGNoYXJhY3RlciAnXCIgKyBjb2RlUG9pbnRUb1N0cmluZyhjb2RlKSArIFwiJ1wiKTtcbn07XG5cbnBwLmZpbmlzaE9wID0gZnVuY3Rpb24gKHR5cGUsIHNpemUpIHtcbiAgdmFyIHN0ciA9IHRoaXMuaW5wdXQuc2xpY2UodGhpcy5wb3MsIHRoaXMucG9zICsgc2l6ZSk7XG4gIHRoaXMucG9zICs9IHNpemU7XG4gIHJldHVybiB0aGlzLmZpbmlzaFRva2VuKHR5cGUsIHN0cik7XG59O1xuXG52YXIgcmVnZXhwVW5pY29kZVN1cHBvcnQgPSBmYWxzZTtcbnRyeSB7XG4gIG5ldyBSZWdFeHAoXCLvv79cIiwgXCJ1XCIpO3JlZ2V4cFVuaWNvZGVTdXBwb3J0ID0gdHJ1ZTtcbn0gY2F0Y2ggKGUpIHt9XG5cbi8vIFBhcnNlIGEgcmVndWxhciBleHByZXNzaW9uLiBTb21lIGNvbnRleHQtYXdhcmVuZXNzIGlzIG5lY2Vzc2FyeSxcbi8vIHNpbmNlIGEgJy8nIGluc2lkZSBhICdbXScgc2V0IGRvZXMgbm90IGVuZCB0aGUgZXhwcmVzc2lvbi5cblxucHAucmVhZFJlZ2V4cCA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIGVzY2FwZWQgPSB1bmRlZmluZWQsXG4gICAgICBpbkNsYXNzID0gdW5kZWZpbmVkLFxuICAgICAgc3RhcnQgPSB0aGlzLnBvcztcbiAgZm9yICg7Oykge1xuICAgIGlmICh0aGlzLnBvcyA+PSB0aGlzLmlucHV0Lmxlbmd0aCkgdGhpcy5yYWlzZShzdGFydCwgXCJVbnRlcm1pbmF0ZWQgcmVndWxhciBleHByZXNzaW9uXCIpO1xuICAgIHZhciBjaCA9IHRoaXMuaW5wdXQuY2hhckF0KHRoaXMucG9zKTtcbiAgICBpZiAobGluZUJyZWFrLnRlc3QoY2gpKSB0aGlzLnJhaXNlKHN0YXJ0LCBcIlVudGVybWluYXRlZCByZWd1bGFyIGV4cHJlc3Npb25cIik7XG4gICAgaWYgKCFlc2NhcGVkKSB7XG4gICAgICBpZiAoY2ggPT09IFwiW1wiKSBpbkNsYXNzID0gdHJ1ZTtlbHNlIGlmIChjaCA9PT0gXCJdXCIgJiYgaW5DbGFzcykgaW5DbGFzcyA9IGZhbHNlO2Vsc2UgaWYgKGNoID09PSBcIi9cIiAmJiAhaW5DbGFzcykgYnJlYWs7XG4gICAgICBlc2NhcGVkID0gY2ggPT09IFwiXFxcXFwiO1xuICAgIH0gZWxzZSBlc2NhcGVkID0gZmFsc2U7XG4gICAgKyt0aGlzLnBvcztcbiAgfVxuICB2YXIgY29udGVudCA9IHRoaXMuaW5wdXQuc2xpY2Uoc3RhcnQsIHRoaXMucG9zKTtcbiAgKyt0aGlzLnBvcztcbiAgLy8gTmVlZCB0byB1c2UgYHJlYWRXb3JkMWAgYmVjYXVzZSAnXFx1WFhYWCcgc2VxdWVuY2VzIGFyZSBhbGxvd2VkXG4gIC8vIGhlcmUgKGRvbid0IGFzaykuXG4gIHZhciBtb2RzID0gdGhpcy5yZWFkV29yZDEoKTtcbiAgdmFyIHRtcCA9IGNvbnRlbnQ7XG4gIGlmIChtb2RzKSB7XG4gICAgdmFyIHZhbGlkRmxhZ3MgPSAvXltnbXNpeV0qJC87XG4gICAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KSB2YWxpZEZsYWdzID0gL15bZ21zaXl1XSokLztcbiAgICBpZiAoIXZhbGlkRmxhZ3MudGVzdChtb2RzKSkgdGhpcy5yYWlzZShzdGFydCwgXCJJbnZhbGlkIHJlZ3VsYXIgZXhwcmVzc2lvbiBmbGFnXCIpO1xuICAgIGlmIChtb2RzLmluZGV4T2YoXCJ1XCIpID49IDAgJiYgIXJlZ2V4cFVuaWNvZGVTdXBwb3J0KSB7XG4gICAgICAvLyBSZXBsYWNlIGVhY2ggYXN0cmFsIHN5bWJvbCBhbmQgZXZlcnkgVW5pY29kZSBlc2NhcGUgc2VxdWVuY2UgdGhhdFxuICAgICAgLy8gcG9zc2libHkgcmVwcmVzZW50cyBhbiBhc3RyYWwgc3ltYm9sIG9yIGEgcGFpcmVkIHN1cnJvZ2F0ZSB3aXRoIGFcbiAgICAgIC8vIHNpbmdsZSBBU0NJSSBzeW1ib2wgdG8gYXZvaWQgdGhyb3dpbmcgb24gcmVndWxhciBleHByZXNzaW9ucyB0aGF0XG4gICAgICAvLyBhcmUgb25seSB2YWxpZCBpbiBjb21iaW5hdGlvbiB3aXRoIHRoZSBgL3VgIGZsYWcuXG4gICAgICAvLyBOb3RlOiByZXBsYWNpbmcgd2l0aCB0aGUgQVNDSUkgc3ltYm9sIGB4YCBtaWdodCBjYXVzZSBmYWxzZVxuICAgICAgLy8gbmVnYXRpdmVzIGluIHVubGlrZWx5IHNjZW5hcmlvcy4gRm9yIGV4YW1wbGUsIGBbXFx1ezYxfS1iXWAgaXMgYVxuICAgICAgLy8gcGVyZmVjdGx5IHZhbGlkIHBhdHRlcm4gdGhhdCBpcyBlcXVpdmFsZW50IHRvIGBbYS1iXWAsIGJ1dCBpdCB3b3VsZFxuICAgICAgLy8gYmUgcmVwbGFjZWQgYnkgYFt4LWJdYCB3aGljaCB0aHJvd3MgYW4gZXJyb3IuXG4gICAgICB0bXAgPSB0bXAucmVwbGFjZSgvXFxcXHUoW2EtZkEtRjAtOV17NH0pfFxcXFx1XFx7KFswLTlhLWZBLUZdKylcXH18W1xcdUQ4MDAtXFx1REJGRl1bXFx1REMwMC1cXHVERkZGXS9nLCBcInhcIik7XG4gICAgfVxuICB9XG4gIC8vIERldGVjdCBpbnZhbGlkIHJlZ3VsYXIgZXhwcmVzc2lvbnMuXG4gIHZhciB2YWx1ZSA9IG51bGw7XG4gIC8vIFJoaW5vJ3MgcmVndWxhciBleHByZXNzaW9uIHBhcnNlciBpcyBmbGFreSBhbmQgdGhyb3dzIHVuY2F0Y2hhYmxlIGV4Y2VwdGlvbnMsXG4gIC8vIHNvIGRvbid0IGRvIGRldGVjdGlvbiBpZiB3ZSBhcmUgcnVubmluZyB1bmRlciBSaGlub1xuICBpZiAoIWlzUmhpbm8pIHtcbiAgICB0cnkge1xuICAgICAgbmV3IFJlZ0V4cCh0bXApO1xuICAgIH0gY2F0Y2ggKGUpIHtcbiAgICAgIGlmIChlIGluc3RhbmNlb2YgU3ludGF4RXJyb3IpIHRoaXMucmFpc2Uoc3RhcnQsIFwiRXJyb3IgcGFyc2luZyByZWd1bGFyIGV4cHJlc3Npb246IFwiICsgZS5tZXNzYWdlKTtcbiAgICAgIHRoaXMucmFpc2UoZSk7XG4gICAgfVxuICAgIC8vIEdldCBhIHJlZ3VsYXIgZXhwcmVzc2lvbiBvYmplY3QgZm9yIHRoaXMgcGF0dGVybi1mbGFnIHBhaXIsIG9yIGBudWxsYCBpblxuICAgIC8vIGNhc2UgdGhlIGN1cnJlbnQgZW52aXJvbm1lbnQgZG9lc24ndCBzdXBwb3J0IHRoZSBmbGFncyBpdCB1c2VzLlxuICAgIHRyeSB7XG4gICAgICB2YWx1ZSA9IG5ldyBSZWdFeHAoY29udGVudCwgbW9kcyk7XG4gICAgfSBjYXRjaCAoZXJyKSB7fVxuICB9XG4gIHJldHVybiB0aGlzLmZpbmlzaFRva2VuKHR0LnJlZ2V4cCwgeyBwYXR0ZXJuOiBjb250ZW50LCBmbGFnczogbW9kcywgdmFsdWU6IHZhbHVlIH0pO1xufTtcblxuLy8gUmVhZCBhbiBpbnRlZ2VyIGluIHRoZSBnaXZlbiByYWRpeC4gUmV0dXJuIG51bGwgaWYgemVybyBkaWdpdHNcbi8vIHdlcmUgcmVhZCwgdGhlIGludGVnZXIgdmFsdWUgb3RoZXJ3aXNlLiBXaGVuIGBsZW5gIGlzIGdpdmVuLCB0aGlzXG4vLyB3aWxsIHJldHVybiBgbnVsbGAgdW5sZXNzIHRoZSBpbnRlZ2VyIGhhcyBleGFjdGx5IGBsZW5gIGRpZ2l0cy5cblxucHAucmVhZEludCA9IGZ1bmN0aW9uIChyYWRpeCwgbGVuKSB7XG4gIHZhciBzdGFydCA9IHRoaXMucG9zLFxuICAgICAgdG90YWwgPSAwO1xuICBmb3IgKHZhciBpID0gMCwgZSA9IGxlbiA9PSBudWxsID8gSW5maW5pdHkgOiBsZW47IGkgPCBlOyArK2kpIHtcbiAgICB2YXIgY29kZSA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyksXG4gICAgICAgIHZhbCA9IHVuZGVmaW5lZDtcbiAgICBpZiAoY29kZSA+PSA5NykgdmFsID0gY29kZSAtIDk3ICsgMTA7IC8vIGFcbiAgICBlbHNlIGlmIChjb2RlID49IDY1KSB2YWwgPSBjb2RlIC0gNjUgKyAxMDsgLy8gQVxuICAgIGVsc2UgaWYgKGNvZGUgPj0gNDggJiYgY29kZSA8PSA1NykgdmFsID0gY29kZSAtIDQ4OyAvLyAwLTlcbiAgICBlbHNlIHZhbCA9IEluZmluaXR5O1xuICAgIGlmICh2YWwgPj0gcmFkaXgpIGJyZWFrO1xuICAgICsrdGhpcy5wb3M7XG4gICAgdG90YWwgPSB0b3RhbCAqIHJhZGl4ICsgdmFsO1xuICB9XG4gIGlmICh0aGlzLnBvcyA9PT0gc3RhcnQgfHwgbGVuICE9IG51bGwgJiYgdGhpcy5wb3MgLSBzdGFydCAhPT0gbGVuKSByZXR1cm4gbnVsbDtcblxuICByZXR1cm4gdG90YWw7XG59O1xuXG5wcC5yZWFkUmFkaXhOdW1iZXIgPSBmdW5jdGlvbiAocmFkaXgpIHtcbiAgdGhpcy5wb3MgKz0gMjsgLy8gMHhcbiAgdmFyIHZhbCA9IHRoaXMucmVhZEludChyYWRpeCk7XG4gIGlmICh2YWwgPT0gbnVsbCkgdGhpcy5yYWlzZSh0aGlzLnN0YXJ0ICsgMiwgXCJFeHBlY3RlZCBudW1iZXIgaW4gcmFkaXggXCIgKyByYWRpeCk7XG4gIGlmIChpc0lkZW50aWZpZXJTdGFydCh0aGlzLmZ1bGxDaGFyQ29kZUF0UG9zKCkpKSB0aGlzLnJhaXNlKHRoaXMucG9zLCBcIklkZW50aWZpZXIgZGlyZWN0bHkgYWZ0ZXIgbnVtYmVyXCIpO1xuICByZXR1cm4gdGhpcy5maW5pc2hUb2tlbih0dC5udW0sIHZhbCk7XG59O1xuXG4vLyBSZWFkIGFuIGludGVnZXIsIG9jdGFsIGludGVnZXIsIG9yIGZsb2F0aW5nLXBvaW50IG51bWJlci5cblxucHAucmVhZE51bWJlciA9IGZ1bmN0aW9uIChzdGFydHNXaXRoRG90KSB7XG4gIHZhciBzdGFydCA9IHRoaXMucG9zLFxuICAgICAgaXNGbG9hdCA9IGZhbHNlLFxuICAgICAgb2N0YWwgPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MpID09PSA0ODtcbiAgaWYgKCFzdGFydHNXaXRoRG90ICYmIHRoaXMucmVhZEludCgxMCkgPT09IG51bGwpIHRoaXMucmFpc2Uoc3RhcnQsIFwiSW52YWxpZCBudW1iZXJcIik7XG4gIGlmICh0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MpID09PSA0Nikge1xuICAgICsrdGhpcy5wb3M7XG4gICAgdGhpcy5yZWFkSW50KDEwKTtcbiAgICBpc0Zsb2F0ID0gdHJ1ZTtcbiAgfVxuICB2YXIgbmV4dCA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyk7XG4gIGlmIChuZXh0ID09PSA2OSB8fCBuZXh0ID09PSAxMDEpIHtcbiAgICAvLyAnZUUnXG4gICAgbmV4dCA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCgrK3RoaXMucG9zKTtcbiAgICBpZiAobmV4dCA9PT0gNDMgfHwgbmV4dCA9PT0gNDUpICsrdGhpcy5wb3M7IC8vICcrLSdcbiAgICBpZiAodGhpcy5yZWFkSW50KDEwKSA9PT0gbnVsbCkgdGhpcy5yYWlzZShzdGFydCwgXCJJbnZhbGlkIG51bWJlclwiKTtcbiAgICBpc0Zsb2F0ID0gdHJ1ZTtcbiAgfVxuICBpZiAoaXNJZGVudGlmaWVyU3RhcnQodGhpcy5mdWxsQ2hhckNvZGVBdFBvcygpKSkgdGhpcy5yYWlzZSh0aGlzLnBvcywgXCJJZGVudGlmaWVyIGRpcmVjdGx5IGFmdGVyIG51bWJlclwiKTtcblxuICB2YXIgc3RyID0gdGhpcy5pbnB1dC5zbGljZShzdGFydCwgdGhpcy5wb3MpLFxuICAgICAgdmFsID0gdW5kZWZpbmVkO1xuICBpZiAoaXNGbG9hdCkgdmFsID0gcGFyc2VGbG9hdChzdHIpO2Vsc2UgaWYgKCFvY3RhbCB8fCBzdHIubGVuZ3RoID09PSAxKSB2YWwgPSBwYXJzZUludChzdHIsIDEwKTtlbHNlIGlmICgvWzg5XS8udGVzdChzdHIpIHx8IHRoaXMuc3RyaWN0KSB0aGlzLnJhaXNlKHN0YXJ0LCBcIkludmFsaWQgbnVtYmVyXCIpO2Vsc2UgdmFsID0gcGFyc2VJbnQoc3RyLCA4KTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoVG9rZW4odHQubnVtLCB2YWwpO1xufTtcblxuLy8gUmVhZCBhIHN0cmluZyB2YWx1ZSwgaW50ZXJwcmV0aW5nIGJhY2tzbGFzaC1lc2NhcGVzLlxuXG5wcC5yZWFkQ29kZVBvaW50ID0gZnVuY3Rpb24gKCkge1xuICB2YXIgY2ggPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MpLFxuICAgICAgY29kZSA9IHVuZGVmaW5lZDtcblxuICBpZiAoY2ggPT09IDEyMykge1xuICAgIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPCA2KSB0aGlzLnVuZXhwZWN0ZWQoKTtcbiAgICArK3RoaXMucG9zO1xuICAgIGNvZGUgPSB0aGlzLnJlYWRIZXhDaGFyKHRoaXMuaW5wdXQuaW5kZXhPZihcIn1cIiwgdGhpcy5wb3MpIC0gdGhpcy5wb3MpO1xuICAgICsrdGhpcy5wb3M7XG4gICAgaWYgKGNvZGUgPiAxMTE0MTExKSB0aGlzLnVuZXhwZWN0ZWQoKTtcbiAgfSBlbHNlIHtcbiAgICBjb2RlID0gdGhpcy5yZWFkSGV4Q2hhcig0KTtcbiAgfVxuICByZXR1cm4gY29kZTtcbn07XG5cbmZ1bmN0aW9uIGNvZGVQb2ludFRvU3RyaW5nKGNvZGUpIHtcbiAgLy8gVVRGLTE2IERlY29kaW5nXG4gIGlmIChjb2RlIDw9IDY1NTM1KSB7XG4gICAgcmV0dXJuIFN0cmluZy5mcm9tQ2hhckNvZGUoY29kZSk7XG4gIH1yZXR1cm4gU3RyaW5nLmZyb21DaGFyQ29kZSgoY29kZSAtIDY1NTM2ID4+IDEwKSArIDU1Mjk2LCAoY29kZSAtIDY1NTM2ICYgMTAyMykgKyA1NjMyMCk7XG59XG5cbnBwLnJlYWRTdHJpbmcgPSBmdW5jdGlvbiAocXVvdGUpIHtcbiAgdmFyIG91dCA9IFwiXCIsXG4gICAgICBjaHVua1N0YXJ0ID0gKyt0aGlzLnBvcztcbiAgZm9yICg7Oykge1xuICAgIGlmICh0aGlzLnBvcyA+PSB0aGlzLmlucHV0Lmxlbmd0aCkgdGhpcy5yYWlzZSh0aGlzLnN0YXJ0LCBcIlVudGVybWluYXRlZCBzdHJpbmcgY29uc3RhbnRcIik7XG4gICAgdmFyIGNoID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zKTtcbiAgICBpZiAoY2ggPT09IHF1b3RlKSBicmVhaztcbiAgICBpZiAoY2ggPT09IDkyKSB7XG4gICAgICAvLyAnXFwnXG4gICAgICBvdXQgKz0gdGhpcy5pbnB1dC5zbGljZShjaHVua1N0YXJ0LCB0aGlzLnBvcyk7XG4gICAgICBvdXQgKz0gdGhpcy5yZWFkRXNjYXBlZENoYXIoKTtcbiAgICAgIGNodW5rU3RhcnQgPSB0aGlzLnBvcztcbiAgICB9IGVsc2Uge1xuICAgICAgaWYgKGlzTmV3TGluZShjaCkpIHRoaXMucmFpc2UodGhpcy5zdGFydCwgXCJVbnRlcm1pbmF0ZWQgc3RyaW5nIGNvbnN0YW50XCIpO1xuICAgICAgKyt0aGlzLnBvcztcbiAgICB9XG4gIH1cbiAgb3V0ICs9IHRoaXMuaW5wdXQuc2xpY2UoY2h1bmtTdGFydCwgdGhpcy5wb3MrKyk7XG4gIHJldHVybiB0aGlzLmZpbmlzaFRva2VuKHR0LnN0cmluZywgb3V0KTtcbn07XG5cbi8vIFJlYWRzIHRlbXBsYXRlIHN0cmluZyB0b2tlbnMuXG5cbnBwLnJlYWRUbXBsVG9rZW4gPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBvdXQgPSBcIlwiLFxuICAgICAgY2h1bmtTdGFydCA9IHRoaXMucG9zO1xuICBmb3IgKDs7KSB7XG4gICAgaWYgKHRoaXMucG9zID49IHRoaXMuaW5wdXQubGVuZ3RoKSB0aGlzLnJhaXNlKHRoaXMuc3RhcnQsIFwiVW50ZXJtaW5hdGVkIHRlbXBsYXRlXCIpO1xuICAgIHZhciBjaCA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyk7XG4gICAgaWYgKGNoID09PSA5NiB8fCBjaCA9PT0gMzYgJiYgdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMSkgPT09IDEyMykge1xuICAgICAgLy8gJ2AnLCAnJHsnXG4gICAgICBpZiAodGhpcy5wb3MgPT09IHRoaXMuc3RhcnQgJiYgdGhpcy50eXBlID09PSB0dC50ZW1wbGF0ZSkge1xuICAgICAgICBpZiAoY2ggPT09IDM2KSB7XG4gICAgICAgICAgdGhpcy5wb3MgKz0gMjtcbiAgICAgICAgICByZXR1cm4gdGhpcy5maW5pc2hUb2tlbih0dC5kb2xsYXJCcmFjZUwpO1xuICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgICsrdGhpcy5wb3M7XG4gICAgICAgICAgcmV0dXJuIHRoaXMuZmluaXNoVG9rZW4odHQuYmFja1F1b3RlKTtcbiAgICAgICAgfVxuICAgICAgfVxuICAgICAgb3V0ICs9IHRoaXMuaW5wdXQuc2xpY2UoY2h1bmtTdGFydCwgdGhpcy5wb3MpO1xuICAgICAgcmV0dXJuIHRoaXMuZmluaXNoVG9rZW4odHQudGVtcGxhdGUsIG91dCk7XG4gICAgfVxuICAgIGlmIChjaCA9PT0gOTIpIHtcbiAgICAgIC8vICdcXCdcbiAgICAgIG91dCArPSB0aGlzLmlucHV0LnNsaWNlKGNodW5rU3RhcnQsIHRoaXMucG9zKTtcbiAgICAgIG91dCArPSB0aGlzLnJlYWRFc2NhcGVkQ2hhcigpO1xuICAgICAgY2h1bmtTdGFydCA9IHRoaXMucG9zO1xuICAgIH0gZWxzZSBpZiAoaXNOZXdMaW5lKGNoKSkge1xuICAgICAgb3V0ICs9IHRoaXMuaW5wdXQuc2xpY2UoY2h1bmtTdGFydCwgdGhpcy5wb3MpO1xuICAgICAgKyt0aGlzLnBvcztcbiAgICAgIGlmIChjaCA9PT0gMTMgJiYgdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zKSA9PT0gMTApIHtcbiAgICAgICAgKyt0aGlzLnBvcztcbiAgICAgICAgb3V0ICs9IFwiXFxuXCI7XG4gICAgICB9IGVsc2Uge1xuICAgICAgICBvdXQgKz0gU3RyaW5nLmZyb21DaGFyQ29kZShjaCk7XG4gICAgICB9XG4gICAgICBpZiAodGhpcy5vcHRpb25zLmxvY2F0aW9ucykge1xuICAgICAgICArK3RoaXMuY3VyTGluZTtcbiAgICAgICAgdGhpcy5saW5lU3RhcnQgPSB0aGlzLnBvcztcbiAgICAgIH1cbiAgICAgIGNodW5rU3RhcnQgPSB0aGlzLnBvcztcbiAgICB9IGVsc2Uge1xuICAgICAgKyt0aGlzLnBvcztcbiAgICB9XG4gIH1cbn07XG5cbi8vIFVzZWQgdG8gcmVhZCBlc2NhcGVkIGNoYXJhY3RlcnNcblxucHAucmVhZEVzY2FwZWRDaGFyID0gZnVuY3Rpb24gKCkge1xuICB2YXIgY2ggPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQoKyt0aGlzLnBvcyk7XG4gIHZhciBvY3RhbCA9IC9eWzAtN10rLy5leGVjKHRoaXMuaW5wdXQuc2xpY2UodGhpcy5wb3MsIHRoaXMucG9zICsgMykpO1xuICBpZiAob2N0YWwpIG9jdGFsID0gb2N0YWxbMF07XG4gIHdoaWxlIChvY3RhbCAmJiBwYXJzZUludChvY3RhbCwgOCkgPiAyNTUpIG9jdGFsID0gb2N0YWwuc2xpY2UoMCwgLTEpO1xuICBpZiAob2N0YWwgPT09IFwiMFwiKSBvY3RhbCA9IG51bGw7XG4gICsrdGhpcy5wb3M7XG4gIGlmIChvY3RhbCkge1xuICAgIGlmICh0aGlzLnN0cmljdCkgdGhpcy5yYWlzZSh0aGlzLnBvcyAtIDIsIFwiT2N0YWwgbGl0ZXJhbCBpbiBzdHJpY3QgbW9kZVwiKTtcbiAgICB0aGlzLnBvcyArPSBvY3RhbC5sZW5ndGggLSAxO1xuICAgIHJldHVybiBTdHJpbmcuZnJvbUNoYXJDb2RlKHBhcnNlSW50KG9jdGFsLCA4KSk7XG4gIH0gZWxzZSB7XG4gICAgc3dpdGNoIChjaCkge1xuICAgICAgY2FzZSAxMTA6XG4gICAgICAgIHJldHVybiBcIlxcblwiOyAvLyAnbicgLT4gJ1xcbidcbiAgICAgIGNhc2UgMTE0OlxuICAgICAgICByZXR1cm4gXCJcXHJcIjsgLy8gJ3InIC0+ICdcXHInXG4gICAgICBjYXNlIDEyMDpcbiAgICAgICAgcmV0dXJuIFN0cmluZy5mcm9tQ2hhckNvZGUodGhpcy5yZWFkSGV4Q2hhcigyKSk7IC8vICd4J1xuICAgICAgY2FzZSAxMTc6XG4gICAgICAgIHJldHVybiBjb2RlUG9pbnRUb1N0cmluZyh0aGlzLnJlYWRDb2RlUG9pbnQoKSk7IC8vICd1J1xuICAgICAgY2FzZSAxMTY6XG4gICAgICAgIHJldHVybiBcIlxcdFwiOyAvLyAndCcgLT4gJ1xcdCdcbiAgICAgIGNhc2UgOTg6XG4gICAgICAgIHJldHVybiBcIlxcYlwiOyAvLyAnYicgLT4gJ1xcYidcbiAgICAgIGNhc2UgMTE4OlxuICAgICAgICByZXR1cm4gXCJcXHUwMDBiXCI7IC8vICd2JyAtPiAnXFx1MDAwYidcbiAgICAgIGNhc2UgMTAyOlxuICAgICAgICByZXR1cm4gXCJcXGZcIjsgLy8gJ2YnIC0+ICdcXGYnXG4gICAgICBjYXNlIDQ4OlxuICAgICAgICByZXR1cm4gXCJcXHUwMDAwXCI7IC8vIDAgLT4gJ1xcMCdcbiAgICAgIGNhc2UgMTM6XG4gICAgICAgIGlmICh0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MpID09PSAxMCkgKyt0aGlzLnBvczsgLy8gJ1xcclxcbidcbiAgICAgIGNhc2UgMTA6XG4gICAgICAgIC8vICcgXFxuJ1xuICAgICAgICBpZiAodGhpcy5vcHRpb25zLmxvY2F0aW9ucykge1xuICAgICAgICAgIHRoaXMubGluZVN0YXJ0ID0gdGhpcy5wb3M7Kyt0aGlzLmN1ckxpbmU7XG4gICAgICAgIH1cbiAgICAgICAgcmV0dXJuIFwiXCI7XG4gICAgICBkZWZhdWx0OlxuICAgICAgICByZXR1cm4gU3RyaW5nLmZyb21DaGFyQ29kZShjaCk7XG4gICAgfVxuICB9XG59O1xuXG4vLyBVc2VkIHRvIHJlYWQgY2hhcmFjdGVyIGVzY2FwZSBzZXF1ZW5jZXMgKCdcXHgnLCAnXFx1JywgJ1xcVScpLlxuXG5wcC5yZWFkSGV4Q2hhciA9IGZ1bmN0aW9uIChsZW4pIHtcbiAgdmFyIG4gPSB0aGlzLnJlYWRJbnQoMTYsIGxlbik7XG4gIGlmIChuID09PSBudWxsKSB0aGlzLnJhaXNlKHRoaXMuc3RhcnQsIFwiQmFkIGNoYXJhY3RlciBlc2NhcGUgc2VxdWVuY2VcIik7XG4gIHJldHVybiBuO1xufTtcblxuLy8gVXNlZCB0byBzaWduYWwgdG8gY2FsbGVycyBvZiBgcmVhZFdvcmQxYCB3aGV0aGVyIHRoZSB3b3JkXG4vLyBjb250YWluZWQgYW55IGVzY2FwZSBzZXF1ZW5jZXMuIFRoaXMgaXMgbmVlZGVkIGJlY2F1c2Ugd29yZHMgd2l0aFxuLy8gZXNjYXBlIHNlcXVlbmNlcyBtdXN0IG5vdCBiZSBpbnRlcnByZXRlZCBhcyBrZXl3b3Jkcy5cblxudmFyIGNvbnRhaW5zRXNjO1xuXG4vLyBSZWFkIGFuIGlkZW50aWZpZXIsIGFuZCByZXR1cm4gaXQgYXMgYSBzdHJpbmcuIFNldHMgYGNvbnRhaW5zRXNjYFxuLy8gdG8gd2hldGhlciB0aGUgd29yZCBjb250YWluZWQgYSAnXFx1JyBlc2NhcGUuXG4vL1xuLy8gSW5jcmVtZW50YWxseSBhZGRzIG9ubHkgZXNjYXBlZCBjaGFycywgYWRkaW5nIG90aGVyIGNodW5rcyBhcy1pc1xuLy8gYXMgYSBtaWNyby1vcHRpbWl6YXRpb24uXG5cbnBwLnJlYWRXb3JkMSA9IGZ1bmN0aW9uICgpIHtcbiAgY29udGFpbnNFc2MgPSBmYWxzZTtcbiAgdmFyIHdvcmQgPSBcIlwiLFxuICAgICAgZmlyc3QgPSB0cnVlLFxuICAgICAgY2h1bmtTdGFydCA9IHRoaXMucG9zO1xuICB2YXIgYXN0cmFsID0gdGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDY7XG4gIHdoaWxlICh0aGlzLnBvcyA8IHRoaXMuaW5wdXQubGVuZ3RoKSB7XG4gICAgdmFyIGNoID0gdGhpcy5mdWxsQ2hhckNvZGVBdFBvcygpO1xuICAgIGlmIChpc0lkZW50aWZpZXJDaGFyKGNoLCBhc3RyYWwpKSB7XG4gICAgICB0aGlzLnBvcyArPSBjaCA8PSA2NTUzNSA/IDEgOiAyO1xuICAgIH0gZWxzZSBpZiAoY2ggPT09IDkyKSB7XG4gICAgICAvLyBcIlxcXCJcbiAgICAgIGNvbnRhaW5zRXNjID0gdHJ1ZTtcbiAgICAgIHdvcmQgKz0gdGhpcy5pbnB1dC5zbGljZShjaHVua1N0YXJ0LCB0aGlzLnBvcyk7XG4gICAgICB2YXIgZXNjU3RhcnQgPSB0aGlzLnBvcztcbiAgICAgIGlmICh0aGlzLmlucHV0LmNoYXJDb2RlQXQoKyt0aGlzLnBvcykgIT0gMTE3KSAvLyBcInVcIlxuICAgICAgICB0aGlzLnJhaXNlKHRoaXMucG9zLCBcIkV4cGVjdGluZyBVbmljb2RlIGVzY2FwZSBzZXF1ZW5jZSBcXFxcdVhYWFhcIik7XG4gICAgICArK3RoaXMucG9zO1xuICAgICAgdmFyIGVzYyA9IHRoaXMucmVhZENvZGVQb2ludCgpO1xuICAgICAgaWYgKCEoZmlyc3QgPyBpc0lkZW50aWZpZXJTdGFydCA6IGlzSWRlbnRpZmllckNoYXIpKGVzYywgYXN0cmFsKSkgdGhpcy5yYWlzZShlc2NTdGFydCwgXCJJbnZhbGlkIFVuaWNvZGUgZXNjYXBlXCIpO1xuICAgICAgd29yZCArPSBjb2RlUG9pbnRUb1N0cmluZyhlc2MpO1xuICAgICAgY2h1bmtTdGFydCA9IHRoaXMucG9zO1xuICAgIH0gZWxzZSB7XG4gICAgICBicmVhaztcbiAgICB9XG4gICAgZmlyc3QgPSBmYWxzZTtcbiAgfVxuICByZXR1cm4gd29yZCArIHRoaXMuaW5wdXQuc2xpY2UoY2h1bmtTdGFydCwgdGhpcy5wb3MpO1xufTtcblxuLy8gUmVhZCBhbiBpZGVudGlmaWVyIG9yIGtleXdvcmQgdG9rZW4uIFdpbGwgY2hlY2sgZm9yIHJlc2VydmVkXG4vLyB3b3JkcyB3aGVuIG5lY2Vzc2FyeS5cblxucHAucmVhZFdvcmQgPSBmdW5jdGlvbiAoKSB7XG4gIHZhciB3b3JkID0gdGhpcy5yZWFkV29yZDEoKTtcbiAgdmFyIHR5cGUgPSB0dC5uYW1lO1xuICBpZiAoKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2IHx8ICFjb250YWluc0VzYykgJiYgdGhpcy5pc0tleXdvcmQod29yZCkpIHR5cGUgPSBrZXl3b3JkVHlwZXNbd29yZF07XG4gIHJldHVybiB0aGlzLmZpbmlzaFRva2VuKHR5cGUsIHdvcmQpO1xufTtcblxufSx7XCIuL2lkZW50aWZpZXJcIjo3LFwiLi9sb2NhdGlvblwiOjgsXCIuL3N0YXRlXCI6MTMsXCIuL3Rva2VudHlwZVwiOjE3LFwiLi93aGl0ZXNwYWNlXCI6MTl9XSwxNzpbZnVuY3Rpb24oX2RlcmVxXyxtb2R1bGUsZXhwb3J0cyl7XG5cInVzZSBzdHJpY3RcIjtcblxudmFyIF9jbGFzc0NhbGxDaGVjayA9IGZ1bmN0aW9uIChpbnN0YW5jZSwgQ29uc3RydWN0b3IpIHsgaWYgKCEoaW5zdGFuY2UgaW5zdGFuY2VvZiBDb25zdHJ1Y3RvcikpIHsgdGhyb3cgbmV3IFR5cGVFcnJvcihcIkNhbm5vdCBjYWxsIGEgY2xhc3MgYXMgYSBmdW5jdGlvblwiKTsgfSB9O1xuXG5leHBvcnRzLl9fZXNNb2R1bGUgPSB0cnVlO1xuLy8gIyMgVG9rZW4gdHlwZXNcblxuLy8gVGhlIGFzc2lnbm1lbnQgb2YgZmluZS1ncmFpbmVkLCBpbmZvcm1hdGlvbi1jYXJyeWluZyB0eXBlIG9iamVjdHNcbi8vIGFsbG93cyB0aGUgdG9rZW5pemVyIHRvIHN0b3JlIHRoZSBpbmZvcm1hdGlvbiBpdCBoYXMgYWJvdXQgYVxuLy8gdG9rZW4gaW4gYSB3YXkgdGhhdCBpcyB2ZXJ5IGNoZWFwIGZvciB0aGUgcGFyc2VyIHRvIGxvb2sgdXAuXG5cbi8vIEFsbCB0b2tlbiB0eXBlIHZhcmlhYmxlcyBzdGFydCB3aXRoIGFuIHVuZGVyc2NvcmUsIHRvIG1ha2UgdGhlbVxuLy8gZWFzeSB0byByZWNvZ25pemUuXG5cbi8vIFRoZSBgYmVmb3JlRXhwcmAgcHJvcGVydHkgaXMgdXNlZCB0byBkaXNhbWJpZ3VhdGUgYmV0d2VlbiByZWd1bGFyXG4vLyBleHByZXNzaW9ucyBhbmQgZGl2aXNpb25zLiBJdCBpcyBzZXQgb24gYWxsIHRva2VuIHR5cGVzIHRoYXQgY2FuXG4vLyBiZSBmb2xsb3dlZCBieSBhbiBleHByZXNzaW9uICh0aHVzLCBhIHNsYXNoIGFmdGVyIHRoZW0gd291bGQgYmUgYVxuLy8gcmVndWxhciBleHByZXNzaW9uKS5cbi8vXG4vLyBgaXNMb29wYCBtYXJrcyBhIGtleXdvcmQgYXMgc3RhcnRpbmcgYSBsb29wLCB3aGljaCBpcyBpbXBvcnRhbnRcbi8vIHRvIGtub3cgd2hlbiBwYXJzaW5nIGEgbGFiZWwsIGluIG9yZGVyIHRvIGFsbG93IG9yIGRpc2FsbG93XG4vLyBjb250aW51ZSBqdW1wcyB0byB0aGF0IGxhYmVsLlxuXG52YXIgVG9rZW5UeXBlID0gZXhwb3J0cy5Ub2tlblR5cGUgPSBmdW5jdGlvbiBUb2tlblR5cGUobGFiZWwpIHtcbiAgdmFyIGNvbmYgPSBhcmd1bWVudHNbMV0gPT09IHVuZGVmaW5lZCA/IHt9IDogYXJndW1lbnRzWzFdO1xuXG4gIF9jbGFzc0NhbGxDaGVjayh0aGlzLCBUb2tlblR5cGUpO1xuXG4gIHRoaXMubGFiZWwgPSBsYWJlbDtcbiAgdGhpcy5rZXl3b3JkID0gY29uZi5rZXl3b3JkO1xuICB0aGlzLmJlZm9yZUV4cHIgPSAhIWNvbmYuYmVmb3JlRXhwcjtcbiAgdGhpcy5zdGFydHNFeHByID0gISFjb25mLnN0YXJ0c0V4cHI7XG4gIHRoaXMuaXNMb29wID0gISFjb25mLmlzTG9vcDtcbiAgdGhpcy5pc0Fzc2lnbiA9ICEhY29uZi5pc0Fzc2lnbjtcbiAgdGhpcy5wcmVmaXggPSAhIWNvbmYucHJlZml4O1xuICB0aGlzLnBvc3RmaXggPSAhIWNvbmYucG9zdGZpeDtcbiAgdGhpcy5iaW5vcCA9IGNvbmYuYmlub3AgfHwgbnVsbDtcbiAgdGhpcy51cGRhdGVDb250ZXh0ID0gbnVsbDtcbn07XG5cbmZ1bmN0aW9uIGJpbm9wKG5hbWUsIHByZWMpIHtcbiAgcmV0dXJuIG5ldyBUb2tlblR5cGUobmFtZSwgeyBiZWZvcmVFeHByOiB0cnVlLCBiaW5vcDogcHJlYyB9KTtcbn1cbnZhciBiZWZvcmVFeHByID0geyBiZWZvcmVFeHByOiB0cnVlIH0sXG4gICAgc3RhcnRzRXhwciA9IHsgc3RhcnRzRXhwcjogdHJ1ZSB9O1xuXG52YXIgdHlwZXMgPSB7XG4gIG51bTogbmV3IFRva2VuVHlwZShcIm51bVwiLCBzdGFydHNFeHByKSxcbiAgcmVnZXhwOiBuZXcgVG9rZW5UeXBlKFwicmVnZXhwXCIsIHN0YXJ0c0V4cHIpLFxuICBzdHJpbmc6IG5ldyBUb2tlblR5cGUoXCJzdHJpbmdcIiwgc3RhcnRzRXhwciksXG4gIG5hbWU6IG5ldyBUb2tlblR5cGUoXCJuYW1lXCIsIHN0YXJ0c0V4cHIpLFxuICBlb2Y6IG5ldyBUb2tlblR5cGUoXCJlb2ZcIiksXG5cbiAgLy8gUHVuY3R1YXRpb24gdG9rZW4gdHlwZXMuXG4gIGJyYWNrZXRMOiBuZXcgVG9rZW5UeXBlKFwiW1wiLCB7IGJlZm9yZUV4cHI6IHRydWUsIHN0YXJ0c0V4cHI6IHRydWUgfSksXG4gIGJyYWNrZXRSOiBuZXcgVG9rZW5UeXBlKFwiXVwiKSxcbiAgYnJhY2VMOiBuZXcgVG9rZW5UeXBlKFwie1wiLCB7IGJlZm9yZUV4cHI6IHRydWUsIHN0YXJ0c0V4cHI6IHRydWUgfSksXG4gIGJyYWNlUjogbmV3IFRva2VuVHlwZShcIn1cIiksXG4gIHBhcmVuTDogbmV3IFRva2VuVHlwZShcIihcIiwgeyBiZWZvcmVFeHByOiB0cnVlLCBzdGFydHNFeHByOiB0cnVlIH0pLFxuICBwYXJlblI6IG5ldyBUb2tlblR5cGUoXCIpXCIpLFxuICBjb21tYTogbmV3IFRva2VuVHlwZShcIixcIiwgYmVmb3JlRXhwciksXG4gIHNlbWk6IG5ldyBUb2tlblR5cGUoXCI7XCIsIGJlZm9yZUV4cHIpLFxuICBjb2xvbjogbmV3IFRva2VuVHlwZShcIjpcIiwgYmVmb3JlRXhwciksXG4gIGRvdDogbmV3IFRva2VuVHlwZShcIi5cIiksXG4gIHF1ZXN0aW9uOiBuZXcgVG9rZW5UeXBlKFwiP1wiLCBiZWZvcmVFeHByKSxcbiAgYXJyb3c6IG5ldyBUb2tlblR5cGUoXCI9PlwiLCBiZWZvcmVFeHByKSxcbiAgdGVtcGxhdGU6IG5ldyBUb2tlblR5cGUoXCJ0ZW1wbGF0ZVwiKSxcbiAgZWxsaXBzaXM6IG5ldyBUb2tlblR5cGUoXCIuLi5cIiwgYmVmb3JlRXhwciksXG4gIGJhY2tRdW90ZTogbmV3IFRva2VuVHlwZShcImBcIiwgc3RhcnRzRXhwciksXG4gIGRvbGxhckJyYWNlTDogbmV3IFRva2VuVHlwZShcIiR7XCIsIHsgYmVmb3JlRXhwcjogdHJ1ZSwgc3RhcnRzRXhwcjogdHJ1ZSB9KSxcblxuICAvLyBPcGVyYXRvcnMuIFRoZXNlIGNhcnJ5IHNldmVyYWwga2luZHMgb2YgcHJvcGVydGllcyB0byBoZWxwIHRoZVxuICAvLyBwYXJzZXIgdXNlIHRoZW0gcHJvcGVybHkgKHRoZSBwcmVzZW5jZSBvZiB0aGVzZSBwcm9wZXJ0aWVzIGlzXG4gIC8vIHdoYXQgY2F0ZWdvcml6ZXMgdGhlbSBhcyBvcGVyYXRvcnMpLlxuICAvL1xuICAvLyBgYmlub3BgLCB3aGVuIHByZXNlbnQsIHNwZWNpZmllcyB0aGF0IHRoaXMgb3BlcmF0b3IgaXMgYSBiaW5hcnlcbiAgLy8gb3BlcmF0b3IsIGFuZCB3aWxsIHJlZmVyIHRvIGl0cyBwcmVjZWRlbmNlLlxuICAvL1xuICAvLyBgcHJlZml4YCBhbmQgYHBvc3RmaXhgIG1hcmsgdGhlIG9wZXJhdG9yIGFzIGEgcHJlZml4IG9yIHBvc3RmaXhcbiAgLy8gdW5hcnkgb3BlcmF0b3IuXG4gIC8vXG4gIC8vIGBpc0Fzc2lnbmAgbWFya3MgYWxsIG9mIGA9YCwgYCs9YCwgYC09YCBldGNldGVyYSwgd2hpY2ggYWN0IGFzXG4gIC8vIGJpbmFyeSBvcGVyYXRvcnMgd2l0aCBhIHZlcnkgbG93IHByZWNlZGVuY2UsIHRoYXQgc2hvdWxkIHJlc3VsdFxuICAvLyBpbiBBc3NpZ25tZW50RXhwcmVzc2lvbiBub2Rlcy5cblxuICBlcTogbmV3IFRva2VuVHlwZShcIj1cIiwgeyBiZWZvcmVFeHByOiB0cnVlLCBpc0Fzc2lnbjogdHJ1ZSB9KSxcbiAgYXNzaWduOiBuZXcgVG9rZW5UeXBlKFwiXz1cIiwgeyBiZWZvcmVFeHByOiB0cnVlLCBpc0Fzc2lnbjogdHJ1ZSB9KSxcbiAgaW5jRGVjOiBuZXcgVG9rZW5UeXBlKFwiKysvLS1cIiwgeyBwcmVmaXg6IHRydWUsIHBvc3RmaXg6IHRydWUsIHN0YXJ0c0V4cHI6IHRydWUgfSksXG4gIHByZWZpeDogbmV3IFRva2VuVHlwZShcInByZWZpeFwiLCB7IGJlZm9yZUV4cHI6IHRydWUsIHByZWZpeDogdHJ1ZSwgc3RhcnRzRXhwcjogdHJ1ZSB9KSxcbiAgbG9naWNhbE9SOiBiaW5vcChcInx8XCIsIDEpLFxuICBsb2dpY2FsQU5EOiBiaW5vcChcIiYmXCIsIDIpLFxuICBiaXR3aXNlT1I6IGJpbm9wKFwifFwiLCAzKSxcbiAgYml0d2lzZVhPUjogYmlub3AoXCJeXCIsIDQpLFxuICBiaXR3aXNlQU5EOiBiaW5vcChcIiZcIiwgNSksXG4gIGVxdWFsaXR5OiBiaW5vcChcIj09LyE9XCIsIDYpLFxuICByZWxhdGlvbmFsOiBiaW5vcChcIjwvPlwiLCA3KSxcbiAgYml0U2hpZnQ6IGJpbm9wKFwiPDwvPj5cIiwgOCksXG4gIHBsdXNNaW46IG5ldyBUb2tlblR5cGUoXCIrLy1cIiwgeyBiZWZvcmVFeHByOiB0cnVlLCBiaW5vcDogOSwgcHJlZml4OiB0cnVlLCBzdGFydHNFeHByOiB0cnVlIH0pLFxuICBtb2R1bG86IGJpbm9wKFwiJVwiLCAxMCksXG4gIHN0YXI6IGJpbm9wKFwiKlwiLCAxMCksXG4gIHNsYXNoOiBiaW5vcChcIi9cIiwgMTApXG59O1xuXG5leHBvcnRzLnR5cGVzID0gdHlwZXM7XG4vLyBNYXAga2V5d29yZCBuYW1lcyB0byB0b2tlbiB0eXBlcy5cblxudmFyIGtleXdvcmRzID0ge307XG5cbmV4cG9ydHMua2V5d29yZHMgPSBrZXl3b3Jkcztcbi8vIFN1Y2NpbmN0IGRlZmluaXRpb25zIG9mIGtleXdvcmQgdG9rZW4gdHlwZXNcbmZ1bmN0aW9uIGt3KG5hbWUpIHtcbiAgdmFyIG9wdGlvbnMgPSBhcmd1bWVudHNbMV0gPT09IHVuZGVmaW5lZCA/IHt9IDogYXJndW1lbnRzWzFdO1xuXG4gIG9wdGlvbnMua2V5d29yZCA9IG5hbWU7XG4gIGtleXdvcmRzW25hbWVdID0gdHlwZXNbXCJfXCIgKyBuYW1lXSA9IG5ldyBUb2tlblR5cGUobmFtZSwgb3B0aW9ucyk7XG59XG5cbmt3KFwiYnJlYWtcIik7XG5rdyhcImNhc2VcIiwgYmVmb3JlRXhwcik7XG5rdyhcImNhdGNoXCIpO1xua3coXCJjb250aW51ZVwiKTtcbmt3KFwiZGVidWdnZXJcIik7XG5rdyhcImRlZmF1bHRcIik7XG5rdyhcImRvXCIsIHsgaXNMb29wOiB0cnVlIH0pO1xua3coXCJlbHNlXCIsIGJlZm9yZUV4cHIpO1xua3coXCJmaW5hbGx5XCIpO1xua3coXCJmb3JcIiwgeyBpc0xvb3A6IHRydWUgfSk7XG5rdyhcImZ1bmN0aW9uXCIsIHN0YXJ0c0V4cHIpO1xua3coXCJpZlwiKTtcbmt3KFwicmV0dXJuXCIsIGJlZm9yZUV4cHIpO1xua3coXCJzd2l0Y2hcIik7XG5rdyhcInRocm93XCIsIGJlZm9yZUV4cHIpO1xua3coXCJ0cnlcIik7XG5rdyhcInZhclwiKTtcbmt3KFwibGV0XCIpO1xua3coXCJjb25zdFwiKTtcbmt3KFwid2hpbGVcIiwgeyBpc0xvb3A6IHRydWUgfSk7XG5rdyhcIndpdGhcIik7XG5rdyhcIm5ld1wiLCB7IGJlZm9yZUV4cHI6IHRydWUsIHN0YXJ0c0V4cHI6IHRydWUgfSk7XG5rdyhcInRoaXNcIiwgc3RhcnRzRXhwcik7XG5rdyhcInN1cGVyXCIsIHN0YXJ0c0V4cHIpO1xua3coXCJjbGFzc1wiKTtcbmt3KFwiZXh0ZW5kc1wiLCBiZWZvcmVFeHByKTtcbmt3KFwiZXhwb3J0XCIpO1xua3coXCJpbXBvcnRcIik7XG5rdyhcInlpZWxkXCIsIHsgYmVmb3JlRXhwcjogdHJ1ZSwgc3RhcnRzRXhwcjogdHJ1ZSB9KTtcbmt3KFwibnVsbFwiLCBzdGFydHNFeHByKTtcbmt3KFwidHJ1ZVwiLCBzdGFydHNFeHByKTtcbmt3KFwiZmFsc2VcIiwgc3RhcnRzRXhwcik7XG5rdyhcImluXCIsIHsgYmVmb3JlRXhwcjogdHJ1ZSwgYmlub3A6IDcgfSk7XG5rdyhcImluc3RhbmNlb2ZcIiwgeyBiZWZvcmVFeHByOiB0cnVlLCBiaW5vcDogNyB9KTtcbmt3KFwidHlwZW9mXCIsIHsgYmVmb3JlRXhwcjogdHJ1ZSwgcHJlZml4OiB0cnVlLCBzdGFydHNFeHByOiB0cnVlIH0pO1xua3coXCJ2b2lkXCIsIHsgYmVmb3JlRXhwcjogdHJ1ZSwgcHJlZml4OiB0cnVlLCBzdGFydHNFeHByOiB0cnVlIH0pO1xua3coXCJkZWxldGVcIiwgeyBiZWZvcmVFeHByOiB0cnVlLCBwcmVmaXg6IHRydWUsIHN0YXJ0c0V4cHI6IHRydWUgfSk7XG5cbn0se31dLDE4OltmdW5jdGlvbihfZGVyZXFfLG1vZHVsZSxleHBvcnRzKXtcblwidXNlIHN0cmljdFwiO1xuXG5leHBvcnRzLmlzQXJyYXkgPSBpc0FycmF5O1xuXG4vLyBDaGVja3MgaWYgYW4gb2JqZWN0IGhhcyBhIHByb3BlcnR5LlxuXG5leHBvcnRzLmhhcyA9IGhhcztcbmV4cG9ydHMuX19lc01vZHVsZSA9IHRydWU7XG5cbmZ1bmN0aW9uIGlzQXJyYXkob2JqKSB7XG4gIHJldHVybiBPYmplY3QucHJvdG90eXBlLnRvU3RyaW5nLmNhbGwob2JqKSA9PT0gXCJbb2JqZWN0IEFycmF5XVwiO1xufVxuXG5mdW5jdGlvbiBoYXMob2JqLCBwcm9wTmFtZSkge1xuICByZXR1cm4gT2JqZWN0LnByb3RvdHlwZS5oYXNPd25Qcm9wZXJ0eS5jYWxsKG9iaiwgcHJvcE5hbWUpO1xufVxuXG59LHt9XSwxOTpbZnVuY3Rpb24oX2RlcmVxXyxtb2R1bGUsZXhwb3J0cyl7XG5cInVzZSBzdHJpY3RcIjtcblxuZXhwb3J0cy5pc05ld0xpbmUgPSBpc05ld0xpbmU7XG5leHBvcnRzLl9fZXNNb2R1bGUgPSB0cnVlO1xuLy8gTWF0Y2hlcyBhIHdob2xlIGxpbmUgYnJlYWsgKHdoZXJlIENSTEYgaXMgY29uc2lkZXJlZCBhIHNpbmdsZVxuLy8gbGluZSBicmVhaykuIFVzZWQgdG8gY291bnQgbGluZXMuXG5cbnZhciBsaW5lQnJlYWsgPSAvXFxyXFxuP3xcXG58XFx1MjAyOHxcXHUyMDI5LztcbmV4cG9ydHMubGluZUJyZWFrID0gbGluZUJyZWFrO1xudmFyIGxpbmVCcmVha0cgPSBuZXcgUmVnRXhwKGxpbmVCcmVhay5zb3VyY2UsIFwiZ1wiKTtcblxuZXhwb3J0cy5saW5lQnJlYWtHID0gbGluZUJyZWFrRztcblxuZnVuY3Rpb24gaXNOZXdMaW5lKGNvZGUpIHtcbiAgcmV0dXJuIGNvZGUgPT09IDEwIHx8IGNvZGUgPT09IDEzIHx8IGNvZGUgPT09IDgyMzIgfHwgY29kZSA9PSA4MjMzO1xufVxuXG52YXIgbm9uQVNDSUl3aGl0ZXNwYWNlID0gL1tcXHUxNjgwXFx1MTgwZVxcdTIwMDAtXFx1MjAwYVxcdTIwMmZcXHUyMDVmXFx1MzAwMFxcdWZlZmZdLztcbmV4cG9ydHMubm9uQVNDSUl3aGl0ZXNwYWNlID0gbm9uQVNDSUl3aGl0ZXNwYWNlO1xuXG59LHt9XX0se30sWzFdKSgxKVxufSk7IiwiKGZ1bmN0aW9uKGYpe2lmKHR5cGVvZiBleHBvcnRzPT09XCJvYmplY3RcIiYmdHlwZW9mIG1vZHVsZSE9PVwidW5kZWZpbmVkXCIpe21vZHVsZS5leHBvcnRzPWYoKX1lbHNlIGlmKHR5cGVvZiBkZWZpbmU9PT1cImZ1bmN0aW9uXCImJmRlZmluZS5hbWQpe2RlZmluZShbXSxmKX1lbHNle3ZhciBnO2lmKHR5cGVvZiB3aW5kb3chPT1cInVuZGVmaW5lZFwiKXtnPXdpbmRvd31lbHNlIGlmKHR5cGVvZiBnbG9iYWwhPT1cInVuZGVmaW5lZFwiKXtnPWdsb2JhbH1lbHNlIGlmKHR5cGVvZiBzZWxmIT09XCJ1bmRlZmluZWRcIil7Zz1zZWxmfWVsc2V7Zz10aGlzfShnLmFjb3JuIHx8IChnLmFjb3JuID0ge30pKS53YWxrID0gZigpfX0pKGZ1bmN0aW9uKCl7dmFyIGRlZmluZSxtb2R1bGUsZXhwb3J0cztyZXR1cm4gKGZ1bmN0aW9uIGUodCxuLHIpe2Z1bmN0aW9uIHMobyx1KXtpZighbltvXSl7aWYoIXRbb10pe3ZhciBhPXR5cGVvZiByZXF1aXJlPT1cImZ1bmN0aW9uXCImJnJlcXVpcmU7aWYoIXUmJmEpcmV0dXJuIGEobywhMCk7aWYoaSlyZXR1cm4gaShvLCEwKTt2YXIgZj1uZXcgRXJyb3IoXCJDYW5ub3QgZmluZCBtb2R1bGUgJ1wiK28rXCInXCIpO3Rocm93IGYuY29kZT1cIk1PRFVMRV9OT1RfRk9VTkRcIixmfXZhciBsPW5bb109e2V4cG9ydHM6e319O3Rbb11bMF0uY2FsbChsLmV4cG9ydHMsZnVuY3Rpb24oZSl7dmFyIG49dFtvXVsxXVtlXTtyZXR1cm4gcyhuP246ZSl9LGwsbC5leHBvcnRzLGUsdCxuLHIpfXJldHVybiBuW29dLmV4cG9ydHN9dmFyIGk9dHlwZW9mIHJlcXVpcmU9PVwiZnVuY3Rpb25cIiYmcmVxdWlyZTtmb3IodmFyIG89MDtvPHIubGVuZ3RoO28rKylzKHJbb10pO3JldHVybiBzfSkoezE6W2Z1bmN0aW9uKF9kZXJlcV8sbW9kdWxlLGV4cG9ydHMpe1xuXCJ1c2Ugc3RyaWN0XCI7XG5cbnZhciBfY2xhc3NDYWxsQ2hlY2sgPSBmdW5jdGlvbiAoaW5zdGFuY2UsIENvbnN0cnVjdG9yKSB7IGlmICghKGluc3RhbmNlIGluc3RhbmNlb2YgQ29uc3RydWN0b3IpKSB7IHRocm93IG5ldyBUeXBlRXJyb3IoXCJDYW5ub3QgY2FsbCBhIGNsYXNzIGFzIGEgZnVuY3Rpb25cIik7IH0gfTtcblxuLy8gQVNUIHdhbGtlciBtb2R1bGUgZm9yIE1vemlsbGEgUGFyc2VyIEFQSSBjb21wYXRpYmxlIHRyZWVzXG5cbi8vIEEgc2ltcGxlIHdhbGsgaXMgb25lIHdoZXJlIHlvdSBzaW1wbHkgc3BlY2lmeSBjYWxsYmFja3MgdG8gYmVcbi8vIGNhbGxlZCBvbiBzcGVjaWZpYyBub2Rlcy4gVGhlIGxhc3QgdHdvIGFyZ3VtZW50cyBhcmUgb3B0aW9uYWwuIEFcbi8vIHNpbXBsZSB1c2Ugd291bGQgYmVcbi8vXG4vLyAgICAgd2Fsay5zaW1wbGUobXlUcmVlLCB7XG4vLyAgICAgICAgIEV4cHJlc3Npb246IGZ1bmN0aW9uKG5vZGUpIHsgLi4uIH1cbi8vICAgICB9KTtcbi8vXG4vLyB0byBkbyBzb21ldGhpbmcgd2l0aCBhbGwgZXhwcmVzc2lvbnMuIEFsbCBQYXJzZXIgQVBJIG5vZGUgdHlwZXNcbi8vIGNhbiBiZSB1c2VkIHRvIGlkZW50aWZ5IG5vZGUgdHlwZXMsIGFzIHdlbGwgYXMgRXhwcmVzc2lvbixcbi8vIFN0YXRlbWVudCwgYW5kIFNjb3BlQm9keSwgd2hpY2ggZGVub3RlIGNhdGVnb3JpZXMgb2Ygbm9kZXMuXG4vL1xuLy8gVGhlIGJhc2UgYXJndW1lbnQgY2FuIGJlIHVzZWQgdG8gcGFzcyBhIGN1c3RvbSAocmVjdXJzaXZlKVxuLy8gd2Fsa2VyLCBhbmQgc3RhdGUgY2FuIGJlIHVzZWQgdG8gZ2l2ZSB0aGlzIHdhbGtlZCBhbiBpbml0aWFsXG4vLyBzdGF0ZS5cblxuZXhwb3J0cy5zaW1wbGUgPSBzaW1wbGU7XG5cbi8vIEFuIGFuY2VzdG9yIHdhbGsgYnVpbGRzIHVwIGFuIGFycmF5IG9mIGFuY2VzdG9yIG5vZGVzIChpbmNsdWRpbmdcbi8vIHRoZSBjdXJyZW50IG5vZGUpIGFuZCBwYXNzZXMgdGhlbSB0byB0aGUgY2FsbGJhY2sgYXMgdGhlIHN0YXRlIHBhcmFtZXRlci5cbmV4cG9ydHMuYW5jZXN0b3IgPSBhbmNlc3RvcjtcblxuLy8gQSByZWN1cnNpdmUgd2FsayBpcyBvbmUgd2hlcmUgeW91ciBmdW5jdGlvbnMgb3ZlcnJpZGUgdGhlIGRlZmF1bHRcbi8vIHdhbGtlcnMuIFRoZXkgY2FuIG1vZGlmeSBhbmQgcmVwbGFjZSB0aGUgc3RhdGUgcGFyYW1ldGVyIHRoYXQnc1xuLy8gdGhyZWFkZWQgdGhyb3VnaCB0aGUgd2FsaywgYW5kIGNhbiBvcHQgaG93IGFuZCB3aGV0aGVyIHRvIHdhbGtcbi8vIHRoZWlyIGNoaWxkIG5vZGVzIChieSBjYWxsaW5nIHRoZWlyIHRoaXJkIGFyZ3VtZW50IG9uIHRoZXNlXG4vLyBub2RlcykuXG5leHBvcnRzLnJlY3Vyc2l2ZSA9IHJlY3Vyc2l2ZTtcblxuLy8gRmluZCBhIG5vZGUgd2l0aCBhIGdpdmVuIHN0YXJ0LCBlbmQsIGFuZCB0eXBlIChhbGwgYXJlIG9wdGlvbmFsLFxuLy8gbnVsbCBjYW4gYmUgdXNlZCBhcyB3aWxkY2FyZCkuIFJldHVybnMgYSB7bm9kZSwgc3RhdGV9IG9iamVjdCwgb3Jcbi8vIHVuZGVmaW5lZCB3aGVuIGl0IGRvZXNuJ3QgZmluZCBhIG1hdGNoaW5nIG5vZGUuXG5leHBvcnRzLmZpbmROb2RlQXQgPSBmaW5kTm9kZUF0O1xuXG4vLyBGaW5kIHRoZSBpbm5lcm1vc3Qgbm9kZSBvZiBhIGdpdmVuIHR5cGUgdGhhdCBjb250YWlucyB0aGUgZ2l2ZW5cbi8vIHBvc2l0aW9uLiBJbnRlcmZhY2Ugc2ltaWxhciB0byBmaW5kTm9kZUF0LlxuZXhwb3J0cy5maW5kTm9kZUFyb3VuZCA9IGZpbmROb2RlQXJvdW5kO1xuXG4vLyBGaW5kIHRoZSBvdXRlcm1vc3QgbWF0Y2hpbmcgbm9kZSBhZnRlciBhIGdpdmVuIHBvc2l0aW9uLlxuZXhwb3J0cy5maW5kTm9kZUFmdGVyID0gZmluZE5vZGVBZnRlcjtcblxuLy8gRmluZCB0aGUgb3V0ZXJtb3N0IG1hdGNoaW5nIG5vZGUgYmVmb3JlIGEgZ2l2ZW4gcG9zaXRpb24uXG5leHBvcnRzLmZpbmROb2RlQmVmb3JlID0gZmluZE5vZGVCZWZvcmU7XG5cbi8vIFVzZWQgdG8gY3JlYXRlIGEgY3VzdG9tIHdhbGtlci4gV2lsbCBmaWxsIGluIGFsbCBtaXNzaW5nIG5vZGVcbi8vIHR5cGUgcHJvcGVydGllcyB3aXRoIHRoZSBkZWZhdWx0cy5cbmV4cG9ydHMubWFrZSA9IG1ha2U7XG5leHBvcnRzLl9fZXNNb2R1bGUgPSB0cnVlO1xuXG5mdW5jdGlvbiBzaW1wbGUobm9kZSwgdmlzaXRvcnMsIGJhc2UsIHN0YXRlKSB7XG4gIGlmICghYmFzZSkgYmFzZSA9IGV4cG9ydHMuYmFzZTsoZnVuY3Rpb24gYyhub2RlLCBzdCwgb3ZlcnJpZGUpIHtcbiAgICB2YXIgdHlwZSA9IG92ZXJyaWRlIHx8IG5vZGUudHlwZSxcbiAgICAgICAgZm91bmQgPSB2aXNpdG9yc1t0eXBlXTtcbiAgICBiYXNlW3R5cGVdKG5vZGUsIHN0LCBjKTtcbiAgICBpZiAoZm91bmQpIGZvdW5kKG5vZGUsIHN0KTtcbiAgfSkobm9kZSwgc3RhdGUpO1xufVxuXG5mdW5jdGlvbiBhbmNlc3Rvcihub2RlLCB2aXNpdG9ycywgYmFzZSwgc3RhdGUpIHtcbiAgaWYgKCFiYXNlKSBiYXNlID0gZXhwb3J0cy5iYXNlO1xuICBpZiAoIXN0YXRlKSBzdGF0ZSA9IFtdOyhmdW5jdGlvbiBjKG5vZGUsIHN0LCBvdmVycmlkZSkge1xuICAgIHZhciB0eXBlID0gb3ZlcnJpZGUgfHwgbm9kZS50eXBlLFxuICAgICAgICBmb3VuZCA9IHZpc2l0b3JzW3R5cGVdO1xuICAgIGlmIChub2RlICE9IHN0W3N0Lmxlbmd0aCAtIDFdKSB7XG4gICAgICBzdCA9IHN0LnNsaWNlKCk7XG4gICAgICBzdC5wdXNoKG5vZGUpO1xuICAgIH1cbiAgICBiYXNlW3R5cGVdKG5vZGUsIHN0LCBjKTtcbiAgICBpZiAoZm91bmQpIGZvdW5kKG5vZGUsIHN0KTtcbiAgfSkobm9kZSwgc3RhdGUpO1xufVxuXG5mdW5jdGlvbiByZWN1cnNpdmUobm9kZSwgc3RhdGUsIGZ1bmNzLCBiYXNlKSB7XG4gIHZhciB2aXNpdG9yID0gZnVuY3MgPyBleHBvcnRzLm1ha2UoZnVuY3MsIGJhc2UpIDogYmFzZTsoZnVuY3Rpb24gYyhub2RlLCBzdCwgb3ZlcnJpZGUpIHtcbiAgICB2aXNpdG9yW292ZXJyaWRlIHx8IG5vZGUudHlwZV0obm9kZSwgc3QsIGMpO1xuICB9KShub2RlLCBzdGF0ZSk7XG59XG5cbmZ1bmN0aW9uIG1ha2VUZXN0KHRlc3QpIHtcbiAgaWYgKHR5cGVvZiB0ZXN0ID09IFwic3RyaW5nXCIpIHtcbiAgICByZXR1cm4gZnVuY3Rpb24gKHR5cGUpIHtcbiAgICAgIHJldHVybiB0eXBlID09IHRlc3Q7XG4gICAgfTtcbiAgfSBlbHNlIGlmICghdGVzdCkge1xuICAgIHJldHVybiBmdW5jdGlvbiAoKSB7XG4gICAgICByZXR1cm4gdHJ1ZTtcbiAgICB9O1xuICB9IGVsc2Uge1xuICAgIHJldHVybiB0ZXN0O1xuICB9XG59XG5cbnZhciBGb3VuZCA9IGZ1bmN0aW9uIEZvdW5kKG5vZGUsIHN0YXRlKSB7XG4gIF9jbGFzc0NhbGxDaGVjayh0aGlzLCBGb3VuZCk7XG5cbiAgdGhpcy5ub2RlID0gbm9kZTt0aGlzLnN0YXRlID0gc3RhdGU7XG59O1xuXG5mdW5jdGlvbiBmaW5kTm9kZUF0KG5vZGUsIHN0YXJ0LCBlbmQsIHRlc3QsIGJhc2UsIHN0YXRlKSB7XG4gIHRlc3QgPSBtYWtlVGVzdCh0ZXN0KTtcbiAgaWYgKCFiYXNlKSBiYXNlID0gZXhwb3J0cy5iYXNlO1xuICB0cnkge1xuICAgIDsoZnVuY3Rpb24gYyhub2RlLCBzdCwgb3ZlcnJpZGUpIHtcbiAgICAgIHZhciB0eXBlID0gb3ZlcnJpZGUgfHwgbm9kZS50eXBlO1xuICAgICAgaWYgKChzdGFydCA9PSBudWxsIHx8IG5vZGUuc3RhcnQgPD0gc3RhcnQpICYmIChlbmQgPT0gbnVsbCB8fCBub2RlLmVuZCA+PSBlbmQpKSBiYXNlW3R5cGVdKG5vZGUsIHN0LCBjKTtcbiAgICAgIGlmICh0ZXN0KHR5cGUsIG5vZGUpICYmIChzdGFydCA9PSBudWxsIHx8IG5vZGUuc3RhcnQgPT0gc3RhcnQpICYmIChlbmQgPT0gbnVsbCB8fCBub2RlLmVuZCA9PSBlbmQpKSB0aHJvdyBuZXcgRm91bmQobm9kZSwgc3QpO1xuICAgIH0pKG5vZGUsIHN0YXRlKTtcbiAgfSBjYXRjaCAoZSkge1xuICAgIGlmIChlIGluc3RhbmNlb2YgRm91bmQpIHtcbiAgICAgIHJldHVybiBlO1xuICAgIH10aHJvdyBlO1xuICB9XG59XG5cbmZ1bmN0aW9uIGZpbmROb2RlQXJvdW5kKG5vZGUsIHBvcywgdGVzdCwgYmFzZSwgc3RhdGUpIHtcbiAgdGVzdCA9IG1ha2VUZXN0KHRlc3QpO1xuICBpZiAoIWJhc2UpIGJhc2UgPSBleHBvcnRzLmJhc2U7XG4gIHRyeSB7XG4gICAgOyhmdW5jdGlvbiBjKG5vZGUsIHN0LCBvdmVycmlkZSkge1xuICAgICAgdmFyIHR5cGUgPSBvdmVycmlkZSB8fCBub2RlLnR5cGU7XG4gICAgICBpZiAobm9kZS5zdGFydCA+IHBvcyB8fCBub2RlLmVuZCA8IHBvcykge1xuICAgICAgICByZXR1cm47XG4gICAgICB9YmFzZVt0eXBlXShub2RlLCBzdCwgYyk7XG4gICAgICBpZiAodGVzdCh0eXBlLCBub2RlKSkgdGhyb3cgbmV3IEZvdW5kKG5vZGUsIHN0KTtcbiAgICB9KShub2RlLCBzdGF0ZSk7XG4gIH0gY2F0Y2ggKGUpIHtcbiAgICBpZiAoZSBpbnN0YW5jZW9mIEZvdW5kKSB7XG4gICAgICByZXR1cm4gZTtcbiAgICB9dGhyb3cgZTtcbiAgfVxufVxuXG5mdW5jdGlvbiBmaW5kTm9kZUFmdGVyKG5vZGUsIHBvcywgdGVzdCwgYmFzZSwgc3RhdGUpIHtcbiAgdGVzdCA9IG1ha2VUZXN0KHRlc3QpO1xuICBpZiAoIWJhc2UpIGJhc2UgPSBleHBvcnRzLmJhc2U7XG4gIHRyeSB7XG4gICAgOyhmdW5jdGlvbiBjKG5vZGUsIHN0LCBvdmVycmlkZSkge1xuICAgICAgaWYgKG5vZGUuZW5kIDwgcG9zKSB7XG4gICAgICAgIHJldHVybjtcbiAgICAgIH12YXIgdHlwZSA9IG92ZXJyaWRlIHx8IG5vZGUudHlwZTtcbiAgICAgIGlmIChub2RlLnN0YXJ0ID49IHBvcyAmJiB0ZXN0KHR5cGUsIG5vZGUpKSB0aHJvdyBuZXcgRm91bmQobm9kZSwgc3QpO1xuICAgICAgYmFzZVt0eXBlXShub2RlLCBzdCwgYyk7XG4gICAgfSkobm9kZSwgc3RhdGUpO1xuICB9IGNhdGNoIChlKSB7XG4gICAgaWYgKGUgaW5zdGFuY2VvZiBGb3VuZCkge1xuICAgICAgcmV0dXJuIGU7XG4gICAgfXRocm93IGU7XG4gIH1cbn1cblxuZnVuY3Rpb24gZmluZE5vZGVCZWZvcmUobm9kZSwgcG9zLCB0ZXN0LCBiYXNlLCBzdGF0ZSkge1xuICB0ZXN0ID0gbWFrZVRlc3QodGVzdCk7XG4gIGlmICghYmFzZSkgYmFzZSA9IGV4cG9ydHMuYmFzZTtcbiAgdmFyIG1heCA9IHVuZGVmaW5lZDsoZnVuY3Rpb24gYyhub2RlLCBzdCwgb3ZlcnJpZGUpIHtcbiAgICBpZiAobm9kZS5zdGFydCA+IHBvcykge1xuICAgICAgcmV0dXJuO1xuICAgIH12YXIgdHlwZSA9IG92ZXJyaWRlIHx8IG5vZGUudHlwZTtcbiAgICBpZiAobm9kZS5lbmQgPD0gcG9zICYmICghbWF4IHx8IG1heC5ub2RlLmVuZCA8IG5vZGUuZW5kKSAmJiB0ZXN0KHR5cGUsIG5vZGUpKSBtYXggPSBuZXcgRm91bmQobm9kZSwgc3QpO1xuICAgIGJhc2VbdHlwZV0obm9kZSwgc3QsIGMpO1xuICB9KShub2RlLCBzdGF0ZSk7XG4gIHJldHVybiBtYXg7XG59XG5cbmZ1bmN0aW9uIG1ha2UoZnVuY3MsIGJhc2UpIHtcbiAgaWYgKCFiYXNlKSBiYXNlID0gZXhwb3J0cy5iYXNlO1xuICB2YXIgdmlzaXRvciA9IHt9O1xuICBmb3IgKHZhciB0eXBlIGluIGJhc2UpIHZpc2l0b3JbdHlwZV0gPSBiYXNlW3R5cGVdO1xuICBmb3IgKHZhciB0eXBlIGluIGZ1bmNzKSB2aXNpdG9yW3R5cGVdID0gZnVuY3NbdHlwZV07XG4gIHJldHVybiB2aXNpdG9yO1xufVxuXG5mdW5jdGlvbiBza2lwVGhyb3VnaChub2RlLCBzdCwgYykge1xuICBjKG5vZGUsIHN0KTtcbn1cbmZ1bmN0aW9uIGlnbm9yZShfbm9kZSwgX3N0LCBfYykge31cblxuLy8gTm9kZSB3YWxrZXJzLlxuXG52YXIgYmFzZSA9IHt9O1xuXG5leHBvcnRzLmJhc2UgPSBiYXNlO1xuYmFzZS5Qcm9ncmFtID0gYmFzZS5CbG9ja1N0YXRlbWVudCA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBmb3IgKHZhciBpID0gMDsgaSA8IG5vZGUuYm9keS5sZW5ndGg7ICsraSkge1xuICAgIGMobm9kZS5ib2R5W2ldLCBzdCwgXCJTdGF0ZW1lbnRcIik7XG4gIH1cbn07XG5iYXNlLlN0YXRlbWVudCA9IHNraXBUaHJvdWdoO1xuYmFzZS5FbXB0eVN0YXRlbWVudCA9IGlnbm9yZTtcbmJhc2UuRXhwcmVzc2lvblN0YXRlbWVudCA9IGJhc2UuUGFyZW50aGVzaXplZEV4cHJlc3Npb24gPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgcmV0dXJuIGMobm9kZS5leHByZXNzaW9uLCBzdCwgXCJFeHByZXNzaW9uXCIpO1xufTtcbmJhc2UuSWZTdGF0ZW1lbnQgPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgYyhub2RlLnRlc3QsIHN0LCBcIkV4cHJlc3Npb25cIik7XG4gIGMobm9kZS5jb25zZXF1ZW50LCBzdCwgXCJTdGF0ZW1lbnRcIik7XG4gIGlmIChub2RlLmFsdGVybmF0ZSkgYyhub2RlLmFsdGVybmF0ZSwgc3QsIFwiU3RhdGVtZW50XCIpO1xufTtcbmJhc2UuTGFiZWxlZFN0YXRlbWVudCA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICByZXR1cm4gYyhub2RlLmJvZHksIHN0LCBcIlN0YXRlbWVudFwiKTtcbn07XG5iYXNlLkJyZWFrU3RhdGVtZW50ID0gYmFzZS5Db250aW51ZVN0YXRlbWVudCA9IGlnbm9yZTtcbmJhc2UuV2l0aFN0YXRlbWVudCA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBjKG5vZGUub2JqZWN0LCBzdCwgXCJFeHByZXNzaW9uXCIpO1xuICBjKG5vZGUuYm9keSwgc3QsIFwiU3RhdGVtZW50XCIpO1xufTtcbmJhc2UuU3dpdGNoU3RhdGVtZW50ID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIGMobm9kZS5kaXNjcmltaW5hbnQsIHN0LCBcIkV4cHJlc3Npb25cIik7XG4gIGZvciAodmFyIGkgPSAwOyBpIDwgbm9kZS5jYXNlcy5sZW5ndGg7ICsraSkge1xuICAgIHZhciBjcyA9IG5vZGUuY2FzZXNbaV07XG4gICAgaWYgKGNzLnRlc3QpIGMoY3MudGVzdCwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbiAgICBmb3IgKHZhciBqID0gMDsgaiA8IGNzLmNvbnNlcXVlbnQubGVuZ3RoOyArK2opIHtcbiAgICAgIGMoY3MuY29uc2VxdWVudFtqXSwgc3QsIFwiU3RhdGVtZW50XCIpO1xuICAgIH1cbiAgfVxufTtcbmJhc2UuUmV0dXJuU3RhdGVtZW50ID0gYmFzZS5ZaWVsZEV4cHJlc3Npb24gPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgaWYgKG5vZGUuYXJndW1lbnQpIGMobm9kZS5hcmd1bWVudCwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbn07XG5iYXNlLlRocm93U3RhdGVtZW50ID0gYmFzZS5TcHJlYWRFbGVtZW50ID0gYmFzZS5SZXN0RWxlbWVudCA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICByZXR1cm4gYyhub2RlLmFyZ3VtZW50LCBzdCwgXCJFeHByZXNzaW9uXCIpO1xufTtcbmJhc2UuVHJ5U3RhdGVtZW50ID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIGMobm9kZS5ibG9jaywgc3QsIFwiU3RhdGVtZW50XCIpO1xuICBpZiAobm9kZS5oYW5kbGVyKSBjKG5vZGUuaGFuZGxlci5ib2R5LCBzdCwgXCJTY29wZUJvZHlcIik7XG4gIGlmIChub2RlLmZpbmFsaXplcikgYyhub2RlLmZpbmFsaXplciwgc3QsIFwiU3RhdGVtZW50XCIpO1xufTtcbmJhc2UuV2hpbGVTdGF0ZW1lbnQgPSBiYXNlLkRvV2hpbGVTdGF0ZW1lbnQgPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgYyhub2RlLnRlc3QsIHN0LCBcIkV4cHJlc3Npb25cIik7XG4gIGMobm9kZS5ib2R5LCBzdCwgXCJTdGF0ZW1lbnRcIik7XG59O1xuYmFzZS5Gb3JTdGF0ZW1lbnQgPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgaWYgKG5vZGUuaW5pdCkgYyhub2RlLmluaXQsIHN0LCBcIkZvckluaXRcIik7XG4gIGlmIChub2RlLnRlc3QpIGMobm9kZS50ZXN0LCBzdCwgXCJFeHByZXNzaW9uXCIpO1xuICBpZiAobm9kZS51cGRhdGUpIGMobm9kZS51cGRhdGUsIHN0LCBcIkV4cHJlc3Npb25cIik7XG4gIGMobm9kZS5ib2R5LCBzdCwgXCJTdGF0ZW1lbnRcIik7XG59O1xuYmFzZS5Gb3JJblN0YXRlbWVudCA9IGJhc2UuRm9yT2ZTdGF0ZW1lbnQgPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgYyhub2RlLmxlZnQsIHN0LCBcIkZvckluaXRcIik7XG4gIGMobm9kZS5yaWdodCwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbiAgYyhub2RlLmJvZHksIHN0LCBcIlN0YXRlbWVudFwiKTtcbn07XG5iYXNlLkZvckluaXQgPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgaWYgKG5vZGUudHlwZSA9PSBcIlZhcmlhYmxlRGVjbGFyYXRpb25cIikgYyhub2RlLCBzdCk7ZWxzZSBjKG5vZGUsIHN0LCBcIkV4cHJlc3Npb25cIik7XG59O1xuYmFzZS5EZWJ1Z2dlclN0YXRlbWVudCA9IGlnbm9yZTtcblxuYmFzZS5GdW5jdGlvbkRlY2xhcmF0aW9uID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIHJldHVybiBjKG5vZGUsIHN0LCBcIkZ1bmN0aW9uXCIpO1xufTtcbmJhc2UuVmFyaWFibGVEZWNsYXJhdGlvbiA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBmb3IgKHZhciBpID0gMDsgaSA8IG5vZGUuZGVjbGFyYXRpb25zLmxlbmd0aDsgKytpKSB7XG4gICAgdmFyIGRlY2wgPSBub2RlLmRlY2xhcmF0aW9uc1tpXTtcbiAgICBpZiAoZGVjbC5pbml0KSBjKGRlY2wuaW5pdCwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbiAgfVxufTtcblxuYmFzZS5GdW5jdGlvbiA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICByZXR1cm4gYyhub2RlLmJvZHksIHN0LCBcIlNjb3BlQm9keVwiKTtcbn07XG5iYXNlLlNjb3BlQm9keSA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICByZXR1cm4gYyhub2RlLCBzdCwgXCJTdGF0ZW1lbnRcIik7XG59O1xuXG5iYXNlLkV4cHJlc3Npb24gPSBza2lwVGhyb3VnaDtcbmJhc2UuVGhpc0V4cHJlc3Npb24gPSBiYXNlLlN1cGVyID0gYmFzZS5NZXRhUHJvcGVydHkgPSBpZ25vcmU7XG5iYXNlLkFycmF5RXhwcmVzc2lvbiA9IGJhc2UuQXJyYXlQYXR0ZXJuID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIGZvciAodmFyIGkgPSAwOyBpIDwgbm9kZS5lbGVtZW50cy5sZW5ndGg7ICsraSkge1xuICAgIHZhciBlbHQgPSBub2RlLmVsZW1lbnRzW2ldO1xuICAgIGlmIChlbHQpIGMoZWx0LCBzdCwgXCJFeHByZXNzaW9uXCIpO1xuICB9XG59O1xuYmFzZS5PYmplY3RFeHByZXNzaW9uID0gYmFzZS5PYmplY3RQYXR0ZXJuID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIGZvciAodmFyIGkgPSAwOyBpIDwgbm9kZS5wcm9wZXJ0aWVzLmxlbmd0aDsgKytpKSB7XG4gICAgYyhub2RlLnByb3BlcnRpZXNbaV0sIHN0KTtcbiAgfVxufTtcbmJhc2UuRnVuY3Rpb25FeHByZXNzaW9uID0gYmFzZS5BcnJvd0Z1bmN0aW9uRXhwcmVzc2lvbiA9IGJhc2UuRnVuY3Rpb25EZWNsYXJhdGlvbjtcbmJhc2UuU2VxdWVuY2VFeHByZXNzaW9uID0gYmFzZS5UZW1wbGF0ZUxpdGVyYWwgPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgZm9yICh2YXIgaSA9IDA7IGkgPCBub2RlLmV4cHJlc3Npb25zLmxlbmd0aDsgKytpKSB7XG4gICAgYyhub2RlLmV4cHJlc3Npb25zW2ldLCBzdCwgXCJFeHByZXNzaW9uXCIpO1xuICB9XG59O1xuYmFzZS5VbmFyeUV4cHJlc3Npb24gPSBiYXNlLlVwZGF0ZUV4cHJlc3Npb24gPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgYyhub2RlLmFyZ3VtZW50LCBzdCwgXCJFeHByZXNzaW9uXCIpO1xufTtcbmJhc2UuQmluYXJ5RXhwcmVzc2lvbiA9IGJhc2UuQXNzaWdubWVudEV4cHJlc3Npb24gPSBiYXNlLkFzc2lnbm1lbnRQYXR0ZXJuID0gYmFzZS5Mb2dpY2FsRXhwcmVzc2lvbiA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBjKG5vZGUubGVmdCwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbiAgYyhub2RlLnJpZ2h0LCBzdCwgXCJFeHByZXNzaW9uXCIpO1xufTtcbmJhc2UuQ29uZGl0aW9uYWxFeHByZXNzaW9uID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIGMobm9kZS50ZXN0LCBzdCwgXCJFeHByZXNzaW9uXCIpO1xuICBjKG5vZGUuY29uc2VxdWVudCwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbiAgYyhub2RlLmFsdGVybmF0ZSwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbn07XG5iYXNlLk5ld0V4cHJlc3Npb24gPSBiYXNlLkNhbGxFeHByZXNzaW9uID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIGMobm9kZS5jYWxsZWUsIHN0LCBcIkV4cHJlc3Npb25cIik7XG4gIGlmIChub2RlLmFyZ3VtZW50cykgZm9yICh2YXIgaSA9IDA7IGkgPCBub2RlLmFyZ3VtZW50cy5sZW5ndGg7ICsraSkge1xuICAgIGMobm9kZS5hcmd1bWVudHNbaV0sIHN0LCBcIkV4cHJlc3Npb25cIik7XG4gIH1cbn07XG5iYXNlLk1lbWJlckV4cHJlc3Npb24gPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgYyhub2RlLm9iamVjdCwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbiAgaWYgKG5vZGUuY29tcHV0ZWQpIGMobm9kZS5wcm9wZXJ0eSwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbn07XG5iYXNlLkV4cG9ydE5hbWVkRGVjbGFyYXRpb24gPSBiYXNlLkV4cG9ydERlZmF1bHREZWNsYXJhdGlvbiA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICByZXR1cm4gYyhub2RlLmRlY2xhcmF0aW9uLCBzdCk7XG59O1xuYmFzZS5JbXBvcnREZWNsYXJhdGlvbiA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBmb3IgKHZhciBpID0gMDsgaSA8IG5vZGUuc3BlY2lmaWVycy5sZW5ndGg7IGkrKykge1xuICAgIGMobm9kZS5zcGVjaWZpZXJzW2ldLCBzdCk7XG4gIH1cbn07XG5iYXNlLkltcG9ydFNwZWNpZmllciA9IGJhc2UuSW1wb3J0RGVmYXVsdFNwZWNpZmllciA9IGJhc2UuSW1wb3J0TmFtZXNwYWNlU3BlY2lmaWVyID0gYmFzZS5JZGVudGlmaWVyID0gYmFzZS5MaXRlcmFsID0gaWdub3JlO1xuXG5iYXNlLlRhZ2dlZFRlbXBsYXRlRXhwcmVzc2lvbiA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBjKG5vZGUudGFnLCBzdCwgXCJFeHByZXNzaW9uXCIpO1xuICBjKG5vZGUucXVhc2ksIHN0KTtcbn07XG5iYXNlLkNsYXNzRGVjbGFyYXRpb24gPSBiYXNlLkNsYXNzRXhwcmVzc2lvbiA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBpZiAobm9kZS5zdXBlckNsYXNzKSBjKG5vZGUuc3VwZXJDbGFzcywgc3QsIFwiRXhwcmVzc2lvblwiKTtcbiAgZm9yICh2YXIgaSA9IDA7IGkgPCBub2RlLmJvZHkuYm9keS5sZW5ndGg7IGkrKykge1xuICAgIGMobm9kZS5ib2R5LmJvZHlbaV0sIHN0KTtcbiAgfVxufTtcbmJhc2UuTWV0aG9kRGVmaW5pdGlvbiA9IGJhc2UuUHJvcGVydHkgPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgaWYgKG5vZGUuY29tcHV0ZWQpIGMobm9kZS5rZXksIHN0LCBcIkV4cHJlc3Npb25cIik7XG4gIGMobm9kZS52YWx1ZSwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbn07XG5iYXNlLkNvbXByZWhlbnNpb25FeHByZXNzaW9uID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIGZvciAodmFyIGkgPSAwOyBpIDwgbm9kZS5ibG9ja3MubGVuZ3RoOyBpKyspIHtcbiAgICBjKG5vZGUuYmxvY2tzW2ldLnJpZ2h0LCBzdCwgXCJFeHByZXNzaW9uXCIpO1xuICB9Yyhub2RlLmJvZHksIHN0LCBcIkV4cHJlc3Npb25cIik7XG59O1xuXG59LHt9XX0se30sWzFdKSgxKVxufSk7IixudWxsLCJpZiAodHlwZW9mIE9iamVjdC5jcmVhdGUgPT09ICdmdW5jdGlvbicpIHtcbiAgLy8gaW1wbGVtZW50YXRpb24gZnJvbSBzdGFuZGFyZCBub2RlLmpzICd1dGlsJyBtb2R1bGVcbiAgbW9kdWxlLmV4cG9ydHMgPSBmdW5jdGlvbiBpbmhlcml0cyhjdG9yLCBzdXBlckN0b3IpIHtcbiAgICBjdG9yLnN1cGVyXyA9IHN1cGVyQ3RvclxuICAgIGN0b3IucHJvdG90eXBlID0gT2JqZWN0LmNyZWF0ZShzdXBlckN0b3IucHJvdG90eXBlLCB7XG4gICAgICBjb25zdHJ1Y3Rvcjoge1xuICAgICAgICB2YWx1ZTogY3RvcixcbiAgICAgICAgZW51bWVyYWJsZTogZmFsc2UsXG4gICAgICAgIHdyaXRhYmxlOiB0cnVlLFxuICAgICAgICBjb25maWd1cmFibGU6IHRydWVcbiAgICAgIH1cbiAgICB9KTtcbiAgfTtcbn0gZWxzZSB7XG4gIC8vIG9sZCBzY2hvb2wgc2hpbSBmb3Igb2xkIGJyb3dzZXJzXG4gIG1vZHVsZS5leHBvcnRzID0gZnVuY3Rpb24gaW5oZXJpdHMoY3Rvciwgc3VwZXJDdG9yKSB7XG4gICAgY3Rvci5zdXBlcl8gPSBzdXBlckN0b3JcbiAgICB2YXIgVGVtcEN0b3IgPSBmdW5jdGlvbiAoKSB7fVxuICAgIFRlbXBDdG9yLnByb3RvdHlwZSA9IHN1cGVyQ3Rvci5wcm90b3R5cGVcbiAgICBjdG9yLnByb3RvdHlwZSA9IG5ldyBUZW1wQ3RvcigpXG4gICAgY3Rvci5wcm90b3R5cGUuY29uc3RydWN0b3IgPSBjdG9yXG4gIH1cbn1cbiIsIi8vIHNoaW0gZm9yIHVzaW5nIHByb2Nlc3MgaW4gYnJvd3NlclxuXG52YXIgcHJvY2VzcyA9IG1vZHVsZS5leHBvcnRzID0ge307XG52YXIgcXVldWUgPSBbXTtcbnZhciBkcmFpbmluZyA9IGZhbHNlO1xudmFyIGN1cnJlbnRRdWV1ZTtcbnZhciBxdWV1ZUluZGV4ID0gLTE7XG5cbmZ1bmN0aW9uIGNsZWFuVXBOZXh0VGljaygpIHtcbiAgICBkcmFpbmluZyA9IGZhbHNlO1xuICAgIGlmIChjdXJyZW50UXVldWUubGVuZ3RoKSB7XG4gICAgICAgIHF1ZXVlID0gY3VycmVudFF1ZXVlLmNvbmNhdChxdWV1ZSk7XG4gICAgfSBlbHNlIHtcbiAgICAgICAgcXVldWVJbmRleCA9IC0xO1xuICAgIH1cbiAgICBpZiAocXVldWUubGVuZ3RoKSB7XG4gICAgICAgIGRyYWluUXVldWUoKTtcbiAgICB9XG59XG5cbmZ1bmN0aW9uIGRyYWluUXVldWUoKSB7XG4gICAgaWYgKGRyYWluaW5nKSB7XG4gICAgICAgIHJldHVybjtcbiAgICB9XG4gICAgdmFyIHRpbWVvdXQgPSBzZXRUaW1lb3V0KGNsZWFuVXBOZXh0VGljayk7XG4gICAgZHJhaW5pbmcgPSB0cnVlO1xuXG4gICAgdmFyIGxlbiA9IHF1ZXVlLmxlbmd0aDtcbiAgICB3aGlsZShsZW4pIHtcbiAgICAgICAgY3VycmVudFF1ZXVlID0gcXVldWU7XG4gICAgICAgIHF1ZXVlID0gW107XG4gICAgICAgIHdoaWxlICgrK3F1ZXVlSW5kZXggPCBsZW4pIHtcbiAgICAgICAgICAgIGN1cnJlbnRRdWV1ZVtxdWV1ZUluZGV4XS5ydW4oKTtcbiAgICAgICAgfVxuICAgICAgICBxdWV1ZUluZGV4ID0gLTE7XG4gICAgICAgIGxlbiA9IHF1ZXVlLmxlbmd0aDtcbiAgICB9XG4gICAgY3VycmVudFF1ZXVlID0gbnVsbDtcbiAgICBkcmFpbmluZyA9IGZhbHNlO1xuICAgIGNsZWFyVGltZW91dCh0aW1lb3V0KTtcbn1cblxucHJvY2Vzcy5uZXh0VGljayA9IGZ1bmN0aW9uIChmdW4pIHtcbiAgICB2YXIgYXJncyA9IG5ldyBBcnJheShhcmd1bWVudHMubGVuZ3RoIC0gMSk7XG4gICAgaWYgKGFyZ3VtZW50cy5sZW5ndGggPiAxKSB7XG4gICAgICAgIGZvciAodmFyIGkgPSAxOyBpIDwgYXJndW1lbnRzLmxlbmd0aDsgaSsrKSB7XG4gICAgICAgICAgICBhcmdzW2kgLSAxXSA9IGFyZ3VtZW50c1tpXTtcbiAgICAgICAgfVxuICAgIH1cbiAgICBxdWV1ZS5wdXNoKG5ldyBJdGVtKGZ1biwgYXJncykpO1xuICAgIGlmIChxdWV1ZS5sZW5ndGggPT09IDEgJiYgIWRyYWluaW5nKSB7XG4gICAgICAgIHNldFRpbWVvdXQoZHJhaW5RdWV1ZSwgMCk7XG4gICAgfVxufTtcblxuLy8gdjggbGlrZXMgcHJlZGljdGlibGUgb2JqZWN0c1xuZnVuY3Rpb24gSXRlbShmdW4sIGFycmF5KSB7XG4gICAgdGhpcy5mdW4gPSBmdW47XG4gICAgdGhpcy5hcnJheSA9IGFycmF5O1xufVxuSXRlbS5wcm90b3R5cGUucnVuID0gZnVuY3Rpb24gKCkge1xuICAgIHRoaXMuZnVuLmFwcGx5KG51bGwsIHRoaXMuYXJyYXkpO1xufTtcbnByb2Nlc3MudGl0bGUgPSAnYnJvd3Nlcic7XG5wcm9jZXNzLmJyb3dzZXIgPSB0cnVlO1xucHJvY2Vzcy5lbnYgPSB7fTtcbnByb2Nlc3MuYXJndiA9IFtdO1xucHJvY2Vzcy52ZXJzaW9uID0gJyc7IC8vIGVtcHR5IHN0cmluZyB0byBhdm9pZCByZWdleHAgaXNzdWVzXG5wcm9jZXNzLnZlcnNpb25zID0ge307XG5cbmZ1bmN0aW9uIG5vb3AoKSB7fVxuXG5wcm9jZXNzLm9uID0gbm9vcDtcbnByb2Nlc3MuYWRkTGlzdGVuZXIgPSBub29wO1xucHJvY2Vzcy5vbmNlID0gbm9vcDtcbnByb2Nlc3Mub2ZmID0gbm9vcDtcbnByb2Nlc3MucmVtb3ZlTGlzdGVuZXIgPSBub29wO1xucHJvY2Vzcy5yZW1vdmVBbGxMaXN0ZW5lcnMgPSBub29wO1xucHJvY2Vzcy5lbWl0ID0gbm9vcDtcblxucHJvY2Vzcy5iaW5kaW5nID0gZnVuY3Rpb24gKG5hbWUpIHtcbiAgICB0aHJvdyBuZXcgRXJyb3IoJ3Byb2Nlc3MuYmluZGluZyBpcyBub3Qgc3VwcG9ydGVkJyk7XG59O1xuXG4vLyBUT0RPKHNodHlsbWFuKVxucHJvY2Vzcy5jd2QgPSBmdW5jdGlvbiAoKSB7IHJldHVybiAnLycgfTtcbnByb2Nlc3MuY2hkaXIgPSBmdW5jdGlvbiAoZGlyKSB7XG4gICAgdGhyb3cgbmV3IEVycm9yKCdwcm9jZXNzLmNoZGlyIGlzIG5vdCBzdXBwb3J0ZWQnKTtcbn07XG5wcm9jZXNzLnVtYXNrID0gZnVuY3Rpb24oKSB7IHJldHVybiAwOyB9O1xuIiwibW9kdWxlLmV4cG9ydHMgPSBmdW5jdGlvbiBpc0J1ZmZlcihhcmcpIHtcbiAgcmV0dXJuIGFyZyAmJiB0eXBlb2YgYXJnID09PSAnb2JqZWN0J1xuICAgICYmIHR5cGVvZiBhcmcuY29weSA9PT0gJ2Z1bmN0aW9uJ1xuICAgICYmIHR5cGVvZiBhcmcuZmlsbCA9PT0gJ2Z1bmN0aW9uJ1xuICAgICYmIHR5cGVvZiBhcmcucmVhZFVJbnQ4ID09PSAnZnVuY3Rpb24nO1xufSIsIi8vIENvcHlyaWdodCBKb3llbnQsIEluYy4gYW5kIG90aGVyIE5vZGUgY29udHJpYnV0b3JzLlxuLy9cbi8vIFBlcm1pc3Npb24gaXMgaGVyZWJ5IGdyYW50ZWQsIGZyZWUgb2YgY2hhcmdlLCB0byBhbnkgcGVyc29uIG9idGFpbmluZyBhXG4vLyBjb3B5IG9mIHRoaXMgc29mdHdhcmUgYW5kIGFzc29jaWF0ZWQgZG9jdW1lbnRhdGlvbiBmaWxlcyAodGhlXG4vLyBcIlNvZnR3YXJlXCIpLCB0byBkZWFsIGluIHRoZSBTb2Z0d2FyZSB3aXRob3V0IHJlc3RyaWN0aW9uLCBpbmNsdWRpbmdcbi8vIHdpdGhvdXQgbGltaXRhdGlvbiB0aGUgcmlnaHRzIHRvIHVzZSwgY29weSwgbW9kaWZ5LCBtZXJnZSwgcHVibGlzaCxcbi8vIGRpc3RyaWJ1dGUsIHN1YmxpY2Vuc2UsIGFuZC9vciBzZWxsIGNvcGllcyBvZiB0aGUgU29mdHdhcmUsIGFuZCB0byBwZXJtaXRcbi8vIHBlcnNvbnMgdG8gd2hvbSB0aGUgU29mdHdhcmUgaXMgZnVybmlzaGVkIHRvIGRvIHNvLCBzdWJqZWN0IHRvIHRoZVxuLy8gZm9sbG93aW5nIGNvbmRpdGlvbnM6XG4vL1xuLy8gVGhlIGFib3ZlIGNvcHlyaWdodCBub3RpY2UgYW5kIHRoaXMgcGVybWlzc2lvbiBub3RpY2Ugc2hhbGwgYmUgaW5jbHVkZWRcbi8vIGluIGFsbCBjb3BpZXMgb3Igc3Vic3RhbnRpYWwgcG9ydGlvbnMgb2YgdGhlIFNvZnR3YXJlLlxuLy9cbi8vIFRIRSBTT0ZUV0FSRSBJUyBQUk9WSURFRCBcIkFTIElTXCIsIFdJVEhPVVQgV0FSUkFOVFkgT0YgQU5ZIEtJTkQsIEVYUFJFU1Ncbi8vIE9SIElNUExJRUQsIElOQ0xVRElORyBCVVQgTk9UIExJTUlURUQgVE8gVEhFIFdBUlJBTlRJRVMgT0Zcbi8vIE1FUkNIQU5UQUJJTElUWSwgRklUTkVTUyBGT1IgQSBQQVJUSUNVTEFSIFBVUlBPU0UgQU5EIE5PTklORlJJTkdFTUVOVC4gSU5cbi8vIE5PIEVWRU5UIFNIQUxMIFRIRSBBVVRIT1JTIE9SIENPUFlSSUdIVCBIT0xERVJTIEJFIExJQUJMRSBGT1IgQU5ZIENMQUlNLFxuLy8gREFNQUdFUyBPUiBPVEhFUiBMSUFCSUxJVFksIFdIRVRIRVIgSU4gQU4gQUNUSU9OIE9GIENPTlRSQUNULCBUT1JUIE9SXG4vLyBPVEhFUldJU0UsIEFSSVNJTkcgRlJPTSwgT1VUIE9GIE9SIElOIENPTk5FQ1RJT04gV0lUSCBUSEUgU09GVFdBUkUgT1IgVEhFXG4vLyBVU0UgT1IgT1RIRVIgREVBTElOR1MgSU4gVEhFIFNPRlRXQVJFLlxuXG52YXIgZm9ybWF0UmVnRXhwID0gLyVbc2RqJV0vZztcbmV4cG9ydHMuZm9ybWF0ID0gZnVuY3Rpb24oZikge1xuICBpZiAoIWlzU3RyaW5nKGYpKSB7XG4gICAgdmFyIG9iamVjdHMgPSBbXTtcbiAgICBmb3IgKHZhciBpID0gMDsgaSA8IGFyZ3VtZW50cy5sZW5ndGg7IGkrKykge1xuICAgICAgb2JqZWN0cy5wdXNoKGluc3BlY3QoYXJndW1lbnRzW2ldKSk7XG4gICAgfVxuICAgIHJldHVybiBvYmplY3RzLmpvaW4oJyAnKTtcbiAgfVxuXG4gIHZhciBpID0gMTtcbiAgdmFyIGFyZ3MgPSBhcmd1bWVudHM7XG4gIHZhciBsZW4gPSBhcmdzLmxlbmd0aDtcbiAgdmFyIHN0ciA9IFN0cmluZyhmKS5yZXBsYWNlKGZvcm1hdFJlZ0V4cCwgZnVuY3Rpb24oeCkge1xuICAgIGlmICh4ID09PSAnJSUnKSByZXR1cm4gJyUnO1xuICAgIGlmIChpID49IGxlbikgcmV0dXJuIHg7XG4gICAgc3dpdGNoICh4KSB7XG4gICAgICBjYXNlICclcyc6IHJldHVybiBTdHJpbmcoYXJnc1tpKytdKTtcbiAgICAgIGNhc2UgJyVkJzogcmV0dXJuIE51bWJlcihhcmdzW2krK10pO1xuICAgICAgY2FzZSAnJWonOlxuICAgICAgICB0cnkge1xuICAgICAgICAgIHJldHVybiBKU09OLnN0cmluZ2lmeShhcmdzW2krK10pO1xuICAgICAgICB9IGNhdGNoIChfKSB7XG4gICAgICAgICAgcmV0dXJuICdbQ2lyY3VsYXJdJztcbiAgICAgICAgfVxuICAgICAgZGVmYXVsdDpcbiAgICAgICAgcmV0dXJuIHg7XG4gICAgfVxuICB9KTtcbiAgZm9yICh2YXIgeCA9IGFyZ3NbaV07IGkgPCBsZW47IHggPSBhcmdzWysraV0pIHtcbiAgICBpZiAoaXNOdWxsKHgpIHx8ICFpc09iamVjdCh4KSkge1xuICAgICAgc3RyICs9ICcgJyArIHg7XG4gICAgfSBlbHNlIHtcbiAgICAgIHN0ciArPSAnICcgKyBpbnNwZWN0KHgpO1xuICAgIH1cbiAgfVxuICByZXR1cm4gc3RyO1xufTtcblxuXG4vLyBNYXJrIHRoYXQgYSBtZXRob2Qgc2hvdWxkIG5vdCBiZSB1c2VkLlxuLy8gUmV0dXJucyBhIG1vZGlmaWVkIGZ1bmN0aW9uIHdoaWNoIHdhcm5zIG9uY2UgYnkgZGVmYXVsdC5cbi8vIElmIC0tbm8tZGVwcmVjYXRpb24gaXMgc2V0LCB0aGVuIGl0IGlzIGEgbm8tb3AuXG5leHBvcnRzLmRlcHJlY2F0ZSA9IGZ1bmN0aW9uKGZuLCBtc2cpIHtcbiAgLy8gQWxsb3cgZm9yIGRlcHJlY2F0aW5nIHRoaW5ncyBpbiB0aGUgcHJvY2VzcyBvZiBzdGFydGluZyB1cC5cbiAgaWYgKGlzVW5kZWZpbmVkKGdsb2JhbC5wcm9jZXNzKSkge1xuICAgIHJldHVybiBmdW5jdGlvbigpIHtcbiAgICAgIHJldHVybiBleHBvcnRzLmRlcHJlY2F0ZShmbiwgbXNnKS5hcHBseSh0aGlzLCBhcmd1bWVudHMpO1xuICAgIH07XG4gIH1cblxuICBpZiAocHJvY2Vzcy5ub0RlcHJlY2F0aW9uID09PSB0cnVlKSB7XG4gICAgcmV0dXJuIGZuO1xuICB9XG5cbiAgdmFyIHdhcm5lZCA9IGZhbHNlO1xuICBmdW5jdGlvbiBkZXByZWNhdGVkKCkge1xuICAgIGlmICghd2FybmVkKSB7XG4gICAgICBpZiAocHJvY2Vzcy50aHJvd0RlcHJlY2F0aW9uKSB7XG4gICAgICAgIHRocm93IG5ldyBFcnJvcihtc2cpO1xuICAgICAgfSBlbHNlIGlmIChwcm9jZXNzLnRyYWNlRGVwcmVjYXRpb24pIHtcbiAgICAgICAgY29uc29sZS50cmFjZShtc2cpO1xuICAgICAgfSBlbHNlIHtcbiAgICAgICAgY29uc29sZS5lcnJvcihtc2cpO1xuICAgICAgfVxuICAgICAgd2FybmVkID0gdHJ1ZTtcbiAgICB9XG4gICAgcmV0dXJuIGZuLmFwcGx5KHRoaXMsIGFyZ3VtZW50cyk7XG4gIH1cblxuICByZXR1cm4gZGVwcmVjYXRlZDtcbn07XG5cblxudmFyIGRlYnVncyA9IHt9O1xudmFyIGRlYnVnRW52aXJvbjtcbmV4cG9ydHMuZGVidWdsb2cgPSBmdW5jdGlvbihzZXQpIHtcbiAgaWYgKGlzVW5kZWZpbmVkKGRlYnVnRW52aXJvbikpXG4gICAgZGVidWdFbnZpcm9uID0gcHJvY2Vzcy5lbnYuTk9ERV9ERUJVRyB8fCAnJztcbiAgc2V0ID0gc2V0LnRvVXBwZXJDYXNlKCk7XG4gIGlmICghZGVidWdzW3NldF0pIHtcbiAgICBpZiAobmV3IFJlZ0V4cCgnXFxcXGInICsgc2V0ICsgJ1xcXFxiJywgJ2knKS50ZXN0KGRlYnVnRW52aXJvbikpIHtcbiAgICAgIHZhciBwaWQgPSBwcm9jZXNzLnBpZDtcbiAgICAgIGRlYnVnc1tzZXRdID0gZnVuY3Rpb24oKSB7XG4gICAgICAgIHZhciBtc2cgPSBleHBvcnRzLmZvcm1hdC5hcHBseShleHBvcnRzLCBhcmd1bWVudHMpO1xuICAgICAgICBjb25zb2xlLmVycm9yKCclcyAlZDogJXMnLCBzZXQsIHBpZCwgbXNnKTtcbiAgICAgIH07XG4gICAgfSBlbHNlIHtcbiAgICAgIGRlYnVnc1tzZXRdID0gZnVuY3Rpb24oKSB7fTtcbiAgICB9XG4gIH1cbiAgcmV0dXJuIGRlYnVnc1tzZXRdO1xufTtcblxuXG4vKipcbiAqIEVjaG9zIHRoZSB2YWx1ZSBvZiBhIHZhbHVlLiBUcnlzIHRvIHByaW50IHRoZSB2YWx1ZSBvdXRcbiAqIGluIHRoZSBiZXN0IHdheSBwb3NzaWJsZSBnaXZlbiB0aGUgZGlmZmVyZW50IHR5cGVzLlxuICpcbiAqIEBwYXJhbSB7T2JqZWN0fSBvYmogVGhlIG9iamVjdCB0byBwcmludCBvdXQuXG4gKiBAcGFyYW0ge09iamVjdH0gb3B0cyBPcHRpb25hbCBvcHRpb25zIG9iamVjdCB0aGF0IGFsdGVycyB0aGUgb3V0cHV0LlxuICovXG4vKiBsZWdhY3k6IG9iaiwgc2hvd0hpZGRlbiwgZGVwdGgsIGNvbG9ycyovXG5mdW5jdGlvbiBpbnNwZWN0KG9iaiwgb3B0cykge1xuICAvLyBkZWZhdWx0IG9wdGlvbnNcbiAgdmFyIGN0eCA9IHtcbiAgICBzZWVuOiBbXSxcbiAgICBzdHlsaXplOiBzdHlsaXplTm9Db2xvclxuICB9O1xuICAvLyBsZWdhY3kuLi5cbiAgaWYgKGFyZ3VtZW50cy5sZW5ndGggPj0gMykgY3R4LmRlcHRoID0gYXJndW1lbnRzWzJdO1xuICBpZiAoYXJndW1lbnRzLmxlbmd0aCA+PSA0KSBjdHguY29sb3JzID0gYXJndW1lbnRzWzNdO1xuICBpZiAoaXNCb29sZWFuKG9wdHMpKSB7XG4gICAgLy8gbGVnYWN5Li4uXG4gICAgY3R4LnNob3dIaWRkZW4gPSBvcHRzO1xuICB9IGVsc2UgaWYgKG9wdHMpIHtcbiAgICAvLyBnb3QgYW4gXCJvcHRpb25zXCIgb2JqZWN0XG4gICAgZXhwb3J0cy5fZXh0ZW5kKGN0eCwgb3B0cyk7XG4gIH1cbiAgLy8gc2V0IGRlZmF1bHQgb3B0aW9uc1xuICBpZiAoaXNVbmRlZmluZWQoY3R4LnNob3dIaWRkZW4pKSBjdHguc2hvd0hpZGRlbiA9IGZhbHNlO1xuICBpZiAoaXNVbmRlZmluZWQoY3R4LmRlcHRoKSkgY3R4LmRlcHRoID0gMjtcbiAgaWYgKGlzVW5kZWZpbmVkKGN0eC5jb2xvcnMpKSBjdHguY29sb3JzID0gZmFsc2U7XG4gIGlmIChpc1VuZGVmaW5lZChjdHguY3VzdG9tSW5zcGVjdCkpIGN0eC5jdXN0b21JbnNwZWN0ID0gdHJ1ZTtcbiAgaWYgKGN0eC5jb2xvcnMpIGN0eC5zdHlsaXplID0gc3R5bGl6ZVdpdGhDb2xvcjtcbiAgcmV0dXJuIGZvcm1hdFZhbHVlKGN0eCwgb2JqLCBjdHguZGVwdGgpO1xufVxuZXhwb3J0cy5pbnNwZWN0ID0gaW5zcGVjdDtcblxuXG4vLyBodHRwOi8vZW4ud2lraXBlZGlhLm9yZy93aWtpL0FOU0lfZXNjYXBlX2NvZGUjZ3JhcGhpY3Ncbmluc3BlY3QuY29sb3JzID0ge1xuICAnYm9sZCcgOiBbMSwgMjJdLFxuICAnaXRhbGljJyA6IFszLCAyM10sXG4gICd1bmRlcmxpbmUnIDogWzQsIDI0XSxcbiAgJ2ludmVyc2UnIDogWzcsIDI3XSxcbiAgJ3doaXRlJyA6IFszNywgMzldLFxuICAnZ3JleScgOiBbOTAsIDM5XSxcbiAgJ2JsYWNrJyA6IFszMCwgMzldLFxuICAnYmx1ZScgOiBbMzQsIDM5XSxcbiAgJ2N5YW4nIDogWzM2LCAzOV0sXG4gICdncmVlbicgOiBbMzIsIDM5XSxcbiAgJ21hZ2VudGEnIDogWzM1LCAzOV0sXG4gICdyZWQnIDogWzMxLCAzOV0sXG4gICd5ZWxsb3cnIDogWzMzLCAzOV1cbn07XG5cbi8vIERvbid0IHVzZSAnYmx1ZScgbm90IHZpc2libGUgb24gY21kLmV4ZVxuaW5zcGVjdC5zdHlsZXMgPSB7XG4gICdzcGVjaWFsJzogJ2N5YW4nLFxuICAnbnVtYmVyJzogJ3llbGxvdycsXG4gICdib29sZWFuJzogJ3llbGxvdycsXG4gICd1bmRlZmluZWQnOiAnZ3JleScsXG4gICdudWxsJzogJ2JvbGQnLFxuICAnc3RyaW5nJzogJ2dyZWVuJyxcbiAgJ2RhdGUnOiAnbWFnZW50YScsXG4gIC8vIFwibmFtZVwiOiBpbnRlbnRpb25hbGx5IG5vdCBzdHlsaW5nXG4gICdyZWdleHAnOiAncmVkJ1xufTtcblxuXG5mdW5jdGlvbiBzdHlsaXplV2l0aENvbG9yKHN0ciwgc3R5bGVUeXBlKSB7XG4gIHZhciBzdHlsZSA9IGluc3BlY3Quc3R5bGVzW3N0eWxlVHlwZV07XG5cbiAgaWYgKHN0eWxlKSB7XG4gICAgcmV0dXJuICdcXHUwMDFiWycgKyBpbnNwZWN0LmNvbG9yc1tzdHlsZV1bMF0gKyAnbScgKyBzdHIgK1xuICAgICAgICAgICAnXFx1MDAxYlsnICsgaW5zcGVjdC5jb2xvcnNbc3R5bGVdWzFdICsgJ20nO1xuICB9IGVsc2Uge1xuICAgIHJldHVybiBzdHI7XG4gIH1cbn1cblxuXG5mdW5jdGlvbiBzdHlsaXplTm9Db2xvcihzdHIsIHN0eWxlVHlwZSkge1xuICByZXR1cm4gc3RyO1xufVxuXG5cbmZ1bmN0aW9uIGFycmF5VG9IYXNoKGFycmF5KSB7XG4gIHZhciBoYXNoID0ge307XG5cbiAgYXJyYXkuZm9yRWFjaChmdW5jdGlvbih2YWwsIGlkeCkge1xuICAgIGhhc2hbdmFsXSA9IHRydWU7XG4gIH0pO1xuXG4gIHJldHVybiBoYXNoO1xufVxuXG5cbmZ1bmN0aW9uIGZvcm1hdFZhbHVlKGN0eCwgdmFsdWUsIHJlY3Vyc2VUaW1lcykge1xuICAvLyBQcm92aWRlIGEgaG9vayBmb3IgdXNlci1zcGVjaWZpZWQgaW5zcGVjdCBmdW5jdGlvbnMuXG4gIC8vIENoZWNrIHRoYXQgdmFsdWUgaXMgYW4gb2JqZWN0IHdpdGggYW4gaW5zcGVjdCBmdW5jdGlvbiBvbiBpdFxuICBpZiAoY3R4LmN1c3RvbUluc3BlY3QgJiZcbiAgICAgIHZhbHVlICYmXG4gICAgICBpc0Z1bmN0aW9uKHZhbHVlLmluc3BlY3QpICYmXG4gICAgICAvLyBGaWx0ZXIgb3V0IHRoZSB1dGlsIG1vZHVsZSwgaXQncyBpbnNwZWN0IGZ1bmN0aW9uIGlzIHNwZWNpYWxcbiAgICAgIHZhbHVlLmluc3BlY3QgIT09IGV4cG9ydHMuaW5zcGVjdCAmJlxuICAgICAgLy8gQWxzbyBmaWx0ZXIgb3V0IGFueSBwcm90b3R5cGUgb2JqZWN0cyB1c2luZyB0aGUgY2lyY3VsYXIgY2hlY2suXG4gICAgICAhKHZhbHVlLmNvbnN0cnVjdG9yICYmIHZhbHVlLmNvbnN0cnVjdG9yLnByb3RvdHlwZSA9PT0gdmFsdWUpKSB7XG4gICAgdmFyIHJldCA9IHZhbHVlLmluc3BlY3QocmVjdXJzZVRpbWVzLCBjdHgpO1xuICAgIGlmICghaXNTdHJpbmcocmV0KSkge1xuICAgICAgcmV0ID0gZm9ybWF0VmFsdWUoY3R4LCByZXQsIHJlY3Vyc2VUaW1lcyk7XG4gICAgfVxuICAgIHJldHVybiByZXQ7XG4gIH1cblxuICAvLyBQcmltaXRpdmUgdHlwZXMgY2Fubm90IGhhdmUgcHJvcGVydGllc1xuICB2YXIgcHJpbWl0aXZlID0gZm9ybWF0UHJpbWl0aXZlKGN0eCwgdmFsdWUpO1xuICBpZiAocHJpbWl0aXZlKSB7XG4gICAgcmV0dXJuIHByaW1pdGl2ZTtcbiAgfVxuXG4gIC8vIExvb2sgdXAgdGhlIGtleXMgb2YgdGhlIG9iamVjdC5cbiAgdmFyIGtleXMgPSBPYmplY3Qua2V5cyh2YWx1ZSk7XG4gIHZhciB2aXNpYmxlS2V5cyA9IGFycmF5VG9IYXNoKGtleXMpO1xuXG4gIGlmIChjdHguc2hvd0hpZGRlbikge1xuICAgIGtleXMgPSBPYmplY3QuZ2V0T3duUHJvcGVydHlOYW1lcyh2YWx1ZSk7XG4gIH1cblxuICAvLyBJRSBkb2Vzbid0IG1ha2UgZXJyb3IgZmllbGRzIG5vbi1lbnVtZXJhYmxlXG4gIC8vIGh0dHA6Ly9tc2RuLm1pY3Jvc29mdC5jb20vZW4tdXMvbGlicmFyeS9pZS9kd3c1MnNidCh2PXZzLjk0KS5hc3B4XG4gIGlmIChpc0Vycm9yKHZhbHVlKVxuICAgICAgJiYgKGtleXMuaW5kZXhPZignbWVzc2FnZScpID49IDAgfHwga2V5cy5pbmRleE9mKCdkZXNjcmlwdGlvbicpID49IDApKSB7XG4gICAgcmV0dXJuIGZvcm1hdEVycm9yKHZhbHVlKTtcbiAgfVxuXG4gIC8vIFNvbWUgdHlwZSBvZiBvYmplY3Qgd2l0aG91dCBwcm9wZXJ0aWVzIGNhbiBiZSBzaG9ydGN1dHRlZC5cbiAgaWYgKGtleXMubGVuZ3RoID09PSAwKSB7XG4gICAgaWYgKGlzRnVuY3Rpb24odmFsdWUpKSB7XG4gICAgICB2YXIgbmFtZSA9IHZhbHVlLm5hbWUgPyAnOiAnICsgdmFsdWUubmFtZSA6ICcnO1xuICAgICAgcmV0dXJuIGN0eC5zdHlsaXplKCdbRnVuY3Rpb24nICsgbmFtZSArICddJywgJ3NwZWNpYWwnKTtcbiAgICB9XG4gICAgaWYgKGlzUmVnRXhwKHZhbHVlKSkge1xuICAgICAgcmV0dXJuIGN0eC5zdHlsaXplKFJlZ0V4cC5wcm90b3R5cGUudG9TdHJpbmcuY2FsbCh2YWx1ZSksICdyZWdleHAnKTtcbiAgICB9XG4gICAgaWYgKGlzRGF0ZSh2YWx1ZSkpIHtcbiAgICAgIHJldHVybiBjdHguc3R5bGl6ZShEYXRlLnByb3RvdHlwZS50b1N0cmluZy5jYWxsKHZhbHVlKSwgJ2RhdGUnKTtcbiAgICB9XG4gICAgaWYgKGlzRXJyb3IodmFsdWUpKSB7XG4gICAgICByZXR1cm4gZm9ybWF0RXJyb3IodmFsdWUpO1xuICAgIH1cbiAgfVxuXG4gIHZhciBiYXNlID0gJycsIGFycmF5ID0gZmFsc2UsIGJyYWNlcyA9IFsneycsICd9J107XG5cbiAgLy8gTWFrZSBBcnJheSBzYXkgdGhhdCB0aGV5IGFyZSBBcnJheVxuICBpZiAoaXNBcnJheSh2YWx1ZSkpIHtcbiAgICBhcnJheSA9IHRydWU7XG4gICAgYnJhY2VzID0gWydbJywgJ10nXTtcbiAgfVxuXG4gIC8vIE1ha2UgZnVuY3Rpb25zIHNheSB0aGF0IHRoZXkgYXJlIGZ1bmN0aW9uc1xuICBpZiAoaXNGdW5jdGlvbih2YWx1ZSkpIHtcbiAgICB2YXIgbiA9IHZhbHVlLm5hbWUgPyAnOiAnICsgdmFsdWUubmFtZSA6ICcnO1xuICAgIGJhc2UgPSAnIFtGdW5jdGlvbicgKyBuICsgJ10nO1xuICB9XG5cbiAgLy8gTWFrZSBSZWdFeHBzIHNheSB0aGF0IHRoZXkgYXJlIFJlZ0V4cHNcbiAgaWYgKGlzUmVnRXhwKHZhbHVlKSkge1xuICAgIGJhc2UgPSAnICcgKyBSZWdFeHAucHJvdG90eXBlLnRvU3RyaW5nLmNhbGwodmFsdWUpO1xuICB9XG5cbiAgLy8gTWFrZSBkYXRlcyB3aXRoIHByb3BlcnRpZXMgZmlyc3Qgc2F5IHRoZSBkYXRlXG4gIGlmIChpc0RhdGUodmFsdWUpKSB7XG4gICAgYmFzZSA9ICcgJyArIERhdGUucHJvdG90eXBlLnRvVVRDU3RyaW5nLmNhbGwodmFsdWUpO1xuICB9XG5cbiAgLy8gTWFrZSBlcnJvciB3aXRoIG1lc3NhZ2UgZmlyc3Qgc2F5IHRoZSBlcnJvclxuICBpZiAoaXNFcnJvcih2YWx1ZSkpIHtcbiAgICBiYXNlID0gJyAnICsgZm9ybWF0RXJyb3IodmFsdWUpO1xuICB9XG5cbiAgaWYgKGtleXMubGVuZ3RoID09PSAwICYmICghYXJyYXkgfHwgdmFsdWUubGVuZ3RoID09IDApKSB7XG4gICAgcmV0dXJuIGJyYWNlc1swXSArIGJhc2UgKyBicmFjZXNbMV07XG4gIH1cblxuICBpZiAocmVjdXJzZVRpbWVzIDwgMCkge1xuICAgIGlmIChpc1JlZ0V4cCh2YWx1ZSkpIHtcbiAgICAgIHJldHVybiBjdHguc3R5bGl6ZShSZWdFeHAucHJvdG90eXBlLnRvU3RyaW5nLmNhbGwodmFsdWUpLCAncmVnZXhwJyk7XG4gICAgfSBlbHNlIHtcbiAgICAgIHJldHVybiBjdHguc3R5bGl6ZSgnW09iamVjdF0nLCAnc3BlY2lhbCcpO1xuICAgIH1cbiAgfVxuXG4gIGN0eC5zZWVuLnB1c2godmFsdWUpO1xuXG4gIHZhciBvdXRwdXQ7XG4gIGlmIChhcnJheSkge1xuICAgIG91dHB1dCA9IGZvcm1hdEFycmF5KGN0eCwgdmFsdWUsIHJlY3Vyc2VUaW1lcywgdmlzaWJsZUtleXMsIGtleXMpO1xuICB9IGVsc2Uge1xuICAgIG91dHB1dCA9IGtleXMubWFwKGZ1bmN0aW9uKGtleSkge1xuICAgICAgcmV0dXJuIGZvcm1hdFByb3BlcnR5KGN0eCwgdmFsdWUsIHJlY3Vyc2VUaW1lcywgdmlzaWJsZUtleXMsIGtleSwgYXJyYXkpO1xuICAgIH0pO1xuICB9XG5cbiAgY3R4LnNlZW4ucG9wKCk7XG5cbiAgcmV0dXJuIHJlZHVjZVRvU2luZ2xlU3RyaW5nKG91dHB1dCwgYmFzZSwgYnJhY2VzKTtcbn1cblxuXG5mdW5jdGlvbiBmb3JtYXRQcmltaXRpdmUoY3R4LCB2YWx1ZSkge1xuICBpZiAoaXNVbmRlZmluZWQodmFsdWUpKVxuICAgIHJldHVybiBjdHguc3R5bGl6ZSgndW5kZWZpbmVkJywgJ3VuZGVmaW5lZCcpO1xuICBpZiAoaXNTdHJpbmcodmFsdWUpKSB7XG4gICAgdmFyIHNpbXBsZSA9ICdcXCcnICsgSlNPTi5zdHJpbmdpZnkodmFsdWUpLnJlcGxhY2UoL15cInxcIiQvZywgJycpXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAucmVwbGFjZSgvJy9nLCBcIlxcXFwnXCIpXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAucmVwbGFjZSgvXFxcXFwiL2csICdcIicpICsgJ1xcJyc7XG4gICAgcmV0dXJuIGN0eC5zdHlsaXplKHNpbXBsZSwgJ3N0cmluZycpO1xuICB9XG4gIGlmIChpc051bWJlcih2YWx1ZSkpXG4gICAgcmV0dXJuIGN0eC5zdHlsaXplKCcnICsgdmFsdWUsICdudW1iZXInKTtcbiAgaWYgKGlzQm9vbGVhbih2YWx1ZSkpXG4gICAgcmV0dXJuIGN0eC5zdHlsaXplKCcnICsgdmFsdWUsICdib29sZWFuJyk7XG4gIC8vIEZvciBzb21lIHJlYXNvbiB0eXBlb2YgbnVsbCBpcyBcIm9iamVjdFwiLCBzbyBzcGVjaWFsIGNhc2UgaGVyZS5cbiAgaWYgKGlzTnVsbCh2YWx1ZSkpXG4gICAgcmV0dXJuIGN0eC5zdHlsaXplKCdudWxsJywgJ251bGwnKTtcbn1cblxuXG5mdW5jdGlvbiBmb3JtYXRFcnJvcih2YWx1ZSkge1xuICByZXR1cm4gJ1snICsgRXJyb3IucHJvdG90eXBlLnRvU3RyaW5nLmNhbGwodmFsdWUpICsgJ10nO1xufVxuXG5cbmZ1bmN0aW9uIGZvcm1hdEFycmF5KGN0eCwgdmFsdWUsIHJlY3Vyc2VUaW1lcywgdmlzaWJsZUtleXMsIGtleXMpIHtcbiAgdmFyIG91dHB1dCA9IFtdO1xuICBmb3IgKHZhciBpID0gMCwgbCA9IHZhbHVlLmxlbmd0aDsgaSA8IGw7ICsraSkge1xuICAgIGlmIChoYXNPd25Qcm9wZXJ0eSh2YWx1ZSwgU3RyaW5nKGkpKSkge1xuICAgICAgb3V0cHV0LnB1c2goZm9ybWF0UHJvcGVydHkoY3R4LCB2YWx1ZSwgcmVjdXJzZVRpbWVzLCB2aXNpYmxlS2V5cyxcbiAgICAgICAgICBTdHJpbmcoaSksIHRydWUpKTtcbiAgICB9IGVsc2Uge1xuICAgICAgb3V0cHV0LnB1c2goJycpO1xuICAgIH1cbiAgfVxuICBrZXlzLmZvckVhY2goZnVuY3Rpb24oa2V5KSB7XG4gICAgaWYgKCFrZXkubWF0Y2goL15cXGQrJC8pKSB7XG4gICAgICBvdXRwdXQucHVzaChmb3JtYXRQcm9wZXJ0eShjdHgsIHZhbHVlLCByZWN1cnNlVGltZXMsIHZpc2libGVLZXlzLFxuICAgICAgICAgIGtleSwgdHJ1ZSkpO1xuICAgIH1cbiAgfSk7XG4gIHJldHVybiBvdXRwdXQ7XG59XG5cblxuZnVuY3Rpb24gZm9ybWF0UHJvcGVydHkoY3R4LCB2YWx1ZSwgcmVjdXJzZVRpbWVzLCB2aXNpYmxlS2V5cywga2V5LCBhcnJheSkge1xuICB2YXIgbmFtZSwgc3RyLCBkZXNjO1xuICBkZXNjID0gT2JqZWN0LmdldE93blByb3BlcnR5RGVzY3JpcHRvcih2YWx1ZSwga2V5KSB8fCB7IHZhbHVlOiB2YWx1ZVtrZXldIH07XG4gIGlmIChkZXNjLmdldCkge1xuICAgIGlmIChkZXNjLnNldCkge1xuICAgICAgc3RyID0gY3R4LnN0eWxpemUoJ1tHZXR0ZXIvU2V0dGVyXScsICdzcGVjaWFsJyk7XG4gICAgfSBlbHNlIHtcbiAgICAgIHN0ciA9IGN0eC5zdHlsaXplKCdbR2V0dGVyXScsICdzcGVjaWFsJyk7XG4gICAgfVxuICB9IGVsc2Uge1xuICAgIGlmIChkZXNjLnNldCkge1xuICAgICAgc3RyID0gY3R4LnN0eWxpemUoJ1tTZXR0ZXJdJywgJ3NwZWNpYWwnKTtcbiAgICB9XG4gIH1cbiAgaWYgKCFoYXNPd25Qcm9wZXJ0eSh2aXNpYmxlS2V5cywga2V5KSkge1xuICAgIG5hbWUgPSAnWycgKyBrZXkgKyAnXSc7XG4gIH1cbiAgaWYgKCFzdHIpIHtcbiAgICBpZiAoY3R4LnNlZW4uaW5kZXhPZihkZXNjLnZhbHVlKSA8IDApIHtcbiAgICAgIGlmIChpc051bGwocmVjdXJzZVRpbWVzKSkge1xuICAgICAgICBzdHIgPSBmb3JtYXRWYWx1ZShjdHgsIGRlc2MudmFsdWUsIG51bGwpO1xuICAgICAgfSBlbHNlIHtcbiAgICAgICAgc3RyID0gZm9ybWF0VmFsdWUoY3R4LCBkZXNjLnZhbHVlLCByZWN1cnNlVGltZXMgLSAxKTtcbiAgICAgIH1cbiAgICAgIGlmIChzdHIuaW5kZXhPZignXFxuJykgPiAtMSkge1xuICAgICAgICBpZiAoYXJyYXkpIHtcbiAgICAgICAgICBzdHIgPSBzdHIuc3BsaXQoJ1xcbicpLm1hcChmdW5jdGlvbihsaW5lKSB7XG4gICAgICAgICAgICByZXR1cm4gJyAgJyArIGxpbmU7XG4gICAgICAgICAgfSkuam9pbignXFxuJykuc3Vic3RyKDIpO1xuICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgIHN0ciA9ICdcXG4nICsgc3RyLnNwbGl0KCdcXG4nKS5tYXAoZnVuY3Rpb24obGluZSkge1xuICAgICAgICAgICAgcmV0dXJuICcgICAnICsgbGluZTtcbiAgICAgICAgICB9KS5qb2luKCdcXG4nKTtcbiAgICAgICAgfVxuICAgICAgfVxuICAgIH0gZWxzZSB7XG4gICAgICBzdHIgPSBjdHguc3R5bGl6ZSgnW0NpcmN1bGFyXScsICdzcGVjaWFsJyk7XG4gICAgfVxuICB9XG4gIGlmIChpc1VuZGVmaW5lZChuYW1lKSkge1xuICAgIGlmIChhcnJheSAmJiBrZXkubWF0Y2goL15cXGQrJC8pKSB7XG4gICAgICByZXR1cm4gc3RyO1xuICAgIH1cbiAgICBuYW1lID0gSlNPTi5zdHJpbmdpZnkoJycgKyBrZXkpO1xuICAgIGlmIChuYW1lLm1hdGNoKC9eXCIoW2EtekEtWl9dW2EtekEtWl8wLTldKilcIiQvKSkge1xuICAgICAgbmFtZSA9IG5hbWUuc3Vic3RyKDEsIG5hbWUubGVuZ3RoIC0gMik7XG4gICAgICBuYW1lID0gY3R4LnN0eWxpemUobmFtZSwgJ25hbWUnKTtcbiAgICB9IGVsc2Uge1xuICAgICAgbmFtZSA9IG5hbWUucmVwbGFjZSgvJy9nLCBcIlxcXFwnXCIpXG4gICAgICAgICAgICAgICAgIC5yZXBsYWNlKC9cXFxcXCIvZywgJ1wiJylcbiAgICAgICAgICAgICAgICAgLnJlcGxhY2UoLyheXCJ8XCIkKS9nLCBcIidcIik7XG4gICAgICBuYW1lID0gY3R4LnN0eWxpemUobmFtZSwgJ3N0cmluZycpO1xuICAgIH1cbiAgfVxuXG4gIHJldHVybiBuYW1lICsgJzogJyArIHN0cjtcbn1cblxuXG5mdW5jdGlvbiByZWR1Y2VUb1NpbmdsZVN0cmluZyhvdXRwdXQsIGJhc2UsIGJyYWNlcykge1xuICB2YXIgbnVtTGluZXNFc3QgPSAwO1xuICB2YXIgbGVuZ3RoID0gb3V0cHV0LnJlZHVjZShmdW5jdGlvbihwcmV2LCBjdXIpIHtcbiAgICBudW1MaW5lc0VzdCsrO1xuICAgIGlmIChjdXIuaW5kZXhPZignXFxuJykgPj0gMCkgbnVtTGluZXNFc3QrKztcbiAgICByZXR1cm4gcHJldiArIGN1ci5yZXBsYWNlKC9cXHUwMDFiXFxbXFxkXFxkP20vZywgJycpLmxlbmd0aCArIDE7XG4gIH0sIDApO1xuXG4gIGlmIChsZW5ndGggPiA2MCkge1xuICAgIHJldHVybiBicmFjZXNbMF0gK1xuICAgICAgICAgICAoYmFzZSA9PT0gJycgPyAnJyA6IGJhc2UgKyAnXFxuICcpICtcbiAgICAgICAgICAgJyAnICtcbiAgICAgICAgICAgb3V0cHV0LmpvaW4oJyxcXG4gICcpICtcbiAgICAgICAgICAgJyAnICtcbiAgICAgICAgICAgYnJhY2VzWzFdO1xuICB9XG5cbiAgcmV0dXJuIGJyYWNlc1swXSArIGJhc2UgKyAnICcgKyBvdXRwdXQuam9pbignLCAnKSArICcgJyArIGJyYWNlc1sxXTtcbn1cblxuXG4vLyBOT1RFOiBUaGVzZSB0eXBlIGNoZWNraW5nIGZ1bmN0aW9ucyBpbnRlbnRpb25hbGx5IGRvbid0IHVzZSBgaW5zdGFuY2VvZmBcbi8vIGJlY2F1c2UgaXQgaXMgZnJhZ2lsZSBhbmQgY2FuIGJlIGVhc2lseSBmYWtlZCB3aXRoIGBPYmplY3QuY3JlYXRlKClgLlxuZnVuY3Rpb24gaXNBcnJheShhcikge1xuICByZXR1cm4gQXJyYXkuaXNBcnJheShhcik7XG59XG5leHBvcnRzLmlzQXJyYXkgPSBpc0FycmF5O1xuXG5mdW5jdGlvbiBpc0Jvb2xlYW4oYXJnKSB7XG4gIHJldHVybiB0eXBlb2YgYXJnID09PSAnYm9vbGVhbic7XG59XG5leHBvcnRzLmlzQm9vbGVhbiA9IGlzQm9vbGVhbjtcblxuZnVuY3Rpb24gaXNOdWxsKGFyZykge1xuICByZXR1cm4gYXJnID09PSBudWxsO1xufVxuZXhwb3J0cy5pc051bGwgPSBpc051bGw7XG5cbmZ1bmN0aW9uIGlzTnVsbE9yVW5kZWZpbmVkKGFyZykge1xuICByZXR1cm4gYXJnID09IG51bGw7XG59XG5leHBvcnRzLmlzTnVsbE9yVW5kZWZpbmVkID0gaXNOdWxsT3JVbmRlZmluZWQ7XG5cbmZ1bmN0aW9uIGlzTnVtYmVyKGFyZykge1xuICByZXR1cm4gdHlwZW9mIGFyZyA9PT0gJ251bWJlcic7XG59XG5leHBvcnRzLmlzTnVtYmVyID0gaXNOdW1iZXI7XG5cbmZ1bmN0aW9uIGlzU3RyaW5nKGFyZykge1xuICByZXR1cm4gdHlwZW9mIGFyZyA9PT0gJ3N0cmluZyc7XG59XG5leHBvcnRzLmlzU3RyaW5nID0gaXNTdHJpbmc7XG5cbmZ1bmN0aW9uIGlzU3ltYm9sKGFyZykge1xuICByZXR1cm4gdHlwZW9mIGFyZyA9PT0gJ3N5bWJvbCc7XG59XG5leHBvcnRzLmlzU3ltYm9sID0gaXNTeW1ib2w7XG5cbmZ1bmN0aW9uIGlzVW5kZWZpbmVkKGFyZykge1xuICByZXR1cm4gYXJnID09PSB2b2lkIDA7XG59XG5leHBvcnRzLmlzVW5kZWZpbmVkID0gaXNVbmRlZmluZWQ7XG5cbmZ1bmN0aW9uIGlzUmVnRXhwKHJlKSB7XG4gIHJldHVybiBpc09iamVjdChyZSkgJiYgb2JqZWN0VG9TdHJpbmcocmUpID09PSAnW29iamVjdCBSZWdFeHBdJztcbn1cbmV4cG9ydHMuaXNSZWdFeHAgPSBpc1JlZ0V4cDtcblxuZnVuY3Rpb24gaXNPYmplY3QoYXJnKSB7XG4gIHJldHVybiB0eXBlb2YgYXJnID09PSAnb2JqZWN0JyAmJiBhcmcgIT09IG51bGw7XG59XG5leHBvcnRzLmlzT2JqZWN0ID0gaXNPYmplY3Q7XG5cbmZ1bmN0aW9uIGlzRGF0ZShkKSB7XG4gIHJldHVybiBpc09iamVjdChkKSAmJiBvYmplY3RUb1N0cmluZyhkKSA9PT0gJ1tvYmplY3QgRGF0ZV0nO1xufVxuZXhwb3J0cy5pc0RhdGUgPSBpc0RhdGU7XG5cbmZ1bmN0aW9uIGlzRXJyb3IoZSkge1xuICByZXR1cm4gaXNPYmplY3QoZSkgJiZcbiAgICAgIChvYmplY3RUb1N0cmluZyhlKSA9PT0gJ1tvYmplY3QgRXJyb3JdJyB8fCBlIGluc3RhbmNlb2YgRXJyb3IpO1xufVxuZXhwb3J0cy5pc0Vycm9yID0gaXNFcnJvcjtcblxuZnVuY3Rpb24gaXNGdW5jdGlvbihhcmcpIHtcbiAgcmV0dXJuIHR5cGVvZiBhcmcgPT09ICdmdW5jdGlvbic7XG59XG5leHBvcnRzLmlzRnVuY3Rpb24gPSBpc0Z1bmN0aW9uO1xuXG5mdW5jdGlvbiBpc1ByaW1pdGl2ZShhcmcpIHtcbiAgcmV0dXJuIGFyZyA9PT0gbnVsbCB8fFxuICAgICAgICAgdHlwZW9mIGFyZyA9PT0gJ2Jvb2xlYW4nIHx8XG4gICAgICAgICB0eXBlb2YgYXJnID09PSAnbnVtYmVyJyB8fFxuICAgICAgICAgdHlwZW9mIGFyZyA9PT0gJ3N0cmluZycgfHxcbiAgICAgICAgIHR5cGVvZiBhcmcgPT09ICdzeW1ib2wnIHx8ICAvLyBFUzYgc3ltYm9sXG4gICAgICAgICB0eXBlb2YgYXJnID09PSAndW5kZWZpbmVkJztcbn1cbmV4cG9ydHMuaXNQcmltaXRpdmUgPSBpc1ByaW1pdGl2ZTtcblxuZXhwb3J0cy5pc0J1ZmZlciA9IHJlcXVpcmUoJy4vc3VwcG9ydC9pc0J1ZmZlcicpO1xuXG5mdW5jdGlvbiBvYmplY3RUb1N0cmluZyhvKSB7XG4gIHJldHVybiBPYmplY3QucHJvdG90eXBlLnRvU3RyaW5nLmNhbGwobyk7XG59XG5cblxuZnVuY3Rpb24gcGFkKG4pIHtcbiAgcmV0dXJuIG4gPCAxMCA/ICcwJyArIG4udG9TdHJpbmcoMTApIDogbi50b1N0cmluZygxMCk7XG59XG5cblxudmFyIG1vbnRocyA9IFsnSmFuJywgJ0ZlYicsICdNYXInLCAnQXByJywgJ01heScsICdKdW4nLCAnSnVsJywgJ0F1ZycsICdTZXAnLFxuICAgICAgICAgICAgICAnT2N0JywgJ05vdicsICdEZWMnXTtcblxuLy8gMjYgRmViIDE2OjE5OjM0XG5mdW5jdGlvbiB0aW1lc3RhbXAoKSB7XG4gIHZhciBkID0gbmV3IERhdGUoKTtcbiAgdmFyIHRpbWUgPSBbcGFkKGQuZ2V0SG91cnMoKSksXG4gICAgICAgICAgICAgIHBhZChkLmdldE1pbnV0ZXMoKSksXG4gICAgICAgICAgICAgIHBhZChkLmdldFNlY29uZHMoKSldLmpvaW4oJzonKTtcbiAgcmV0dXJuIFtkLmdldERhdGUoKSwgbW9udGhzW2QuZ2V0TW9udGgoKV0sIHRpbWVdLmpvaW4oJyAnKTtcbn1cblxuXG4vLyBsb2cgaXMganVzdCBhIHRoaW4gd3JhcHBlciB0byBjb25zb2xlLmxvZyB0aGF0IHByZXBlbmRzIGEgdGltZXN0YW1wXG5leHBvcnRzLmxvZyA9IGZ1bmN0aW9uKCkge1xuICBjb25zb2xlLmxvZygnJXMgLSAlcycsIHRpbWVzdGFtcCgpLCBleHBvcnRzLmZvcm1hdC5hcHBseShleHBvcnRzLCBhcmd1bWVudHMpKTtcbn07XG5cblxuLyoqXG4gKiBJbmhlcml0IHRoZSBwcm90b3R5cGUgbWV0aG9kcyBmcm9tIG9uZSBjb25zdHJ1Y3RvciBpbnRvIGFub3RoZXIuXG4gKlxuICogVGhlIEZ1bmN0aW9uLnByb3RvdHlwZS5pbmhlcml0cyBmcm9tIGxhbmcuanMgcmV3cml0dGVuIGFzIGEgc3RhbmRhbG9uZVxuICogZnVuY3Rpb24gKG5vdCBvbiBGdW5jdGlvbi5wcm90b3R5cGUpLiBOT1RFOiBJZiB0aGlzIGZpbGUgaXMgdG8gYmUgbG9hZGVkXG4gKiBkdXJpbmcgYm9vdHN0cmFwcGluZyB0aGlzIGZ1bmN0aW9uIG5lZWRzIHRvIGJlIHJld3JpdHRlbiB1c2luZyBzb21lIG5hdGl2ZVxuICogZnVuY3Rpb25zIGFzIHByb3RvdHlwZSBzZXR1cCB1c2luZyBub3JtYWwgSmF2YVNjcmlwdCBkb2VzIG5vdCB3b3JrIGFzXG4gKiBleHBlY3RlZCBkdXJpbmcgYm9vdHN0cmFwcGluZyAoc2VlIG1pcnJvci5qcyBpbiByMTE0OTAzKS5cbiAqXG4gKiBAcGFyYW0ge2Z1bmN0aW9ufSBjdG9yIENvbnN0cnVjdG9yIGZ1bmN0aW9uIHdoaWNoIG5lZWRzIHRvIGluaGVyaXQgdGhlXG4gKiAgICAgcHJvdG90eXBlLlxuICogQHBhcmFtIHtmdW5jdGlvbn0gc3VwZXJDdG9yIENvbnN0cnVjdG9yIGZ1bmN0aW9uIHRvIGluaGVyaXQgcHJvdG90eXBlIGZyb20uXG4gKi9cbmV4cG9ydHMuaW5oZXJpdHMgPSByZXF1aXJlKCdpbmhlcml0cycpO1xuXG5leHBvcnRzLl9leHRlbmQgPSBmdW5jdGlvbihvcmlnaW4sIGFkZCkge1xuICAvLyBEb24ndCBkbyBhbnl0aGluZyBpZiBhZGQgaXNuJ3QgYW4gb2JqZWN0XG4gIGlmICghYWRkIHx8ICFpc09iamVjdChhZGQpKSByZXR1cm4gb3JpZ2luO1xuXG4gIHZhciBrZXlzID0gT2JqZWN0LmtleXMoYWRkKTtcbiAgdmFyIGkgPSBrZXlzLmxlbmd0aDtcbiAgd2hpbGUgKGktLSkge1xuICAgIG9yaWdpbltrZXlzW2ldXSA9IGFkZFtrZXlzW2ldXTtcbiAgfVxuICByZXR1cm4gb3JpZ2luO1xufTtcblxuZnVuY3Rpb24gaGFzT3duUHJvcGVydHkob2JqLCBwcm9wKSB7XG4gIHJldHVybiBPYmplY3QucHJvdG90eXBlLmhhc093blByb3BlcnR5LmNhbGwob2JqLCBwcm9wKTtcbn1cbiJdfQ==
