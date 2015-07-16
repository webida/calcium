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

    // Show AST before scope resolution
    // aux.showUnfolded(ast);

    varBlock.annotateBlockInfo(ast);
    var gBlock = ast['@block'];
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
        return { gObject: gObject, AST: ast, gBlock: gBlock, gScope: gScope };
    } else {
        return gObject;
    }
}

exports.analyze = analyze;
exports.findIdentifierAt = varRefs.findIdentifierAt;
exports.findVarRefsAt = varRefs.findVarRefsAt;

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

function VarBlock(paren, originNode, isCatch) {
    this.paren = paren;
    this.originNode = originNode;
    this.originLabel = originNode['@label'];
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

VarBlock.prototype.hasAncestor = function (otherBlock) {
    var currBlock = this;
    while (currBlock) {
        if (currBlock === otherBlock) {
            return true;
        }
        currBlock = currBlock.paren;
    }
    return false;
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
        var funcBlock = new VarBlock(parenBlock, node);
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
        var catchBlock = new VarBlock(currBlock, node, true);
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
        gBlock = new VarBlock(null, ast);
    }
    ast['@block'] = gBlock;
    walk.recursive(ast, gBlock, null, declaredVariableFinder);
    walk.recursive(ast, gBlock, null, variableUsageCollector);
    return ast;
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

// a walker that visits each id with varBlock
var varWalker = walk.make({
    Function: function Function(node, vb, c) {
        var innerVb = node.body['@block'];
        if (node.id) c(node.id, innerVb);
        for (var i = 0; i < node.params.length; i++) {
            c(node.params[i], innerVb);
        }c(node.body, innerVb);
    },
    TryStatement: function TryStatement(node, vb, c) {
        c(node.block, vb);
        if (node.handler) {
            var catchVb = node.handler.body['@block'];
            c(node.handler.param, catchVb);
            c(node.handler.body, catchVb);
        }
        if (node.finalizer) {
            c(node.finalizer, vb);
        }
    },
    VariableDeclaration: function VariableDeclaration(node, vb, c) {
        for (var i = 0; i < node.declarations.length; ++i) {
            var decl = node.declarations[i];
            c(decl.id, vb);
            if (decl.init) c(decl.init, vb, 'Expression');
        }
    }
});

/**
 *
 * @param preNode - Apply before visiting the current node.
 * If returns false, do not visit the node.
 * @param postNode - Apply after visiting the current node.
 * If given, return values are overridden.
 * @returns {*}
 */
function wrapWalker(walker, preNode, postNode) {
    var retWalker = {};

    var _loop = function (nodeType) {
        if (!walker.hasOwnProperty(nodeType)) {
            return 'continue';
        }
        retWalker[nodeType] = function (node, vb, c) {
            var ret = undefined;
            if (!preNode || preNode(node, vb, c)) {
                ret = walker[nodeType](node, vb, c);
            } else {
                return;
            }
            if (postNode) {
                ret = postNode(node, vb, c);
            }
            return ret;
        };
    };

    // wrapping each function preNode and postNode
    for (var nodeType in walker) {
        var _ret = _loop(nodeType);

        if (_ret === 'continue') continue;
    }
    return retWalker;
}

function Found(node, state) {
    this.node = node;
    this.state = state;
}

function findIdentifierAt(ast, pos) {
    'use strict';

    // find the node
    //var found = walk.findNodeAround(ast, pos, undefined,
    //    varWalker, ast['@block']);
    var walker = wrapWalker(varWalker, function (node, vb) {
        if (node.start > pos || node.end < pos) {
            return false;
        }
        if (node.type === 'Identifier' && node.name !== '✖') {
            throw new Found(node, vb);
        }
        return true;
    });

    try {
        walk.recursive(ast, ast['@block'], walker);
    } catch (e) {
        if (e instanceof Found) {
            return e;
        } else {
            throw e;
        }
    }
    // not found an identifier
    return null;
    //if (found.node.type === 'Identifier') {
    //    return found;
    //} else {
    //    return null;
    //}
}

/**
 *
 * @param ast - scope annotated AST
 * @param {number} pos - character position
 * @returns {*} - array of AST nodes
 */
function findVarRefsAt(ast, pos) {
    'use strict';
    var found = findIdentifierAt(ast, pos);
    if (!found) {
        // pos is not at a variable
        return null;
    }
    // find refs for the id node
    var refs = findRefsToVariable(ast, found);

    return refs;
}

/**
 *
 * @param ast - scope annotated AST
 * @param found - node and varBlock of the variable
 * @returns {Array} - array of AST nodes
 */
function findRefsToVariable(ast, found) {
    'use strict';
    var varName = found.node.name;
    var vb1 = found.state.findVarInChain(varName);
    var start = vb1.originNode.start;
    var end = vb1.originNode.end;
    var refs = [];

    var walker = walk.make({
        Identifier: function Identifier(node, vb, c) {
            if (node.name !== varName) return;
            var vb2 = vb.findVarInChain(varName);
            if (vb1 === vb2) refs.push(node);
        }
    }, varWalker);
    var count = 0;

    walker = wrapWalker(walker, function (node, vb) {
        // visit only related blocks
        console.info(count++);
        console.info(vb);
        return end >= node.start && node.end >= start;
        //return vb1.hasAncestor(vb) || vb.hasAncestor(vb1);
    });

    walk.recursive(ast, ast['@block'], walker);

    return refs;
}

// ============================================

function test() {
    'use strict';
    var test_pgm = fs.readFileSync('./tests/a.js');
    var result = infer.analyze(test_pgm, true);

    for (var i = 0; i < test_pgm.length; i++) {
        var foundNode = findIdentifierAt(result.AST, i);
        if (foundNode) {
            console.log(i, ': ', foundNode.name);
        }
    }
}

exports.findIdentifierAt = findIdentifierAt;
exports.findVarRefsAt = findVarRefsAt;

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
//# sourceMappingURL=data:application/json;charset:utf-8;base64,eyJ2ZXJzaW9uIjozLCJzb3VyY2VzIjpbIm5vZGVfbW9kdWxlcy9icm93c2VyaWZ5L25vZGVfbW9kdWxlcy9icm93c2VyLXBhY2svX3ByZWx1ZGUuanMiLCIvaG9tZS9zd2tpbS9XZWJzdG9ybVByb2plY3RzL3lhdGVybi9saWIvYXV4LmpzIiwiL2hvbWUvc3draW0vV2Vic3Rvcm1Qcm9qZWN0cy95YXRlcm4vbGliL2NvbnN0cmFpbnQvY0dlbi5qcyIsIi9ob21lL3N3a2ltL1dlYnN0b3JtUHJvamVjdHMveWF0ZXJuL2xpYi9jb25zdHJhaW50L2NvbnN0cmFpbnRzLmpzIiwiL2hvbWUvc3draW0vV2Vic3Rvcm1Qcm9qZWN0cy95YXRlcm4vbGliL2RvbWFpbnMvY29udGV4dC5qcyIsIi9ob21lL3N3a2ltL1dlYnN0b3JtUHJvamVjdHMveWF0ZXJuL2xpYi9kb21haW5zL3N0YXR1cy5qcyIsIi9ob21lL3N3a2ltL1dlYnN0b3JtUHJvamVjdHMveWF0ZXJuL2xpYi9kb21haW5zL3R5cGVzLmpzIiwiL2hvbWUvc3draW0vV2Vic3Rvcm1Qcm9qZWN0cy95YXRlcm4vbGliL2luZmVyLmpzIiwiL2hvbWUvc3draW0vV2Vic3Rvcm1Qcm9qZWN0cy95YXRlcm4vbGliL3ZhckJsb2NrLmpzIiwiL2hvbWUvc3draW0vV2Vic3Rvcm1Qcm9qZWN0cy95YXRlcm4vbGliL3ZhcnJlZnMuanMiLCJub2RlX21vZHVsZXMvYWNvcm4vZGlzdC9hY29ybi5qcyIsIm5vZGVfbW9kdWxlcy9hY29ybi9kaXN0L3dhbGsuanMiLCJub2RlX21vZHVsZXMvYnJvd3NlcmlmeS9saWIvX2VtcHR5LmpzIiwibm9kZV9tb2R1bGVzL2Jyb3dzZXJpZnkvbm9kZV9tb2R1bGVzL2luaGVyaXRzL2luaGVyaXRzX2Jyb3dzZXIuanMiLCJub2RlX21vZHVsZXMvYnJvd3NlcmlmeS9ub2RlX21vZHVsZXMvcHJvY2Vzcy9icm93c2VyLmpzIiwibm9kZV9tb2R1bGVzL2Jyb3dzZXJpZnkvbm9kZV9tb2R1bGVzL3V0aWwvc3VwcG9ydC9pc0J1ZmZlckJyb3dzZXIuanMiLCJub2RlX21vZHVsZXMvYnJvd3NlcmlmeS9ub2RlX21vZHVsZXMvdXRpbC91dGlsLmpzIl0sIm5hbWVzIjpbXSwibWFwcGluZ3MiOiJBQUFBOzs7QUNBQSxJQUFJLElBQUksR0FBRyxPQUFPLENBQUMsTUFBTSxDQUFDLENBQUM7O0FBRTNCLFNBQVMsV0FBVyxDQUFDLEdBQUcsRUFBRSxRQUFRLEVBQUU7QUFDaEMsUUFBSSxRQUFRLEdBQUcsRUFBRSxDQUFDOztBQUVsQixRQUFJLEdBQUcsR0FBRyxRQUFRLEtBQUssU0FBUyxHQUFHLENBQUMsR0FBRyxRQUFRLENBQUM7O0FBRWhELGFBQVMsUUFBUSxDQUFDLElBQUksRUFBRTtBQUNwQixZQUFJLENBQUMsUUFBUSxDQUFDLEdBQUcsR0FBRyxDQUFDO0FBQ3JCLGdCQUFRLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQyxDQUFDO0FBQ3BCLFdBQUcsRUFBRSxDQUFDO0tBQ1Q7OztBQUdELGFBQVMsaUJBQWlCLENBQUMsSUFBSSxFQUFFO0FBQzdCLFlBQUksSUFBSSxJQUFJLElBQUksQ0FBQyxjQUFjLENBQUMsTUFBTSxDQUFDLEVBQUU7QUFDckMsb0JBQVEsQ0FBQyxJQUFJLENBQUMsQ0FBQztTQUNsQjtBQUNELFlBQUksSUFBSSxJQUFJLE9BQU8sSUFBSSxLQUFLLFFBQVEsRUFBRTtBQUNsQyxpQkFBSyxJQUFJLENBQUMsSUFBSSxJQUFJLEVBQUU7QUFDaEIsaUNBQWlCLENBQUMsSUFBSSxDQUFDLENBQUMsQ0FBQyxDQUFDLENBQUM7YUFDOUI7U0FDSjtLQUNKOztBQUVELHFCQUFpQixDQUFDLEdBQUcsQ0FBQyxDQUFDOztBQUV2QixXQUFPLFFBQVEsQ0FBQztDQUNuQjs7QUFFRCxTQUFTLFlBQVksQ0FBQyxHQUFHLEVBQUU7QUFDdkIsV0FBTyxDQUFDLEdBQUcsQ0FBQyxJQUFJLENBQUMsT0FBTyxDQUFDLEdBQUcsRUFBRSxFQUFDLEtBQUssRUFBRSxJQUFJLEVBQUMsQ0FBQyxDQUFDLENBQUM7Q0FDakQ7O0FBRUQsT0FBTyxDQUFDLFdBQVcsR0FBRyxXQUFXLENBQUM7QUFDbEMsT0FBTyxDQUFDLFlBQVksR0FBRyxZQUFZLENBQUM7OztBQ25DcEMsWUFBWSxDQUFDOztBQUViLElBQU0sS0FBSyxHQUFHLE9BQU8sQ0FBQyxrQkFBa0IsQ0FBQyxDQUFDO0FBQzFDLElBQU0sSUFBSSxHQUFHLE9BQU8sQ0FBQyxpQkFBaUIsQ0FBQyxDQUFDO0FBQ3hDLElBQU0sTUFBTSxHQUFHLE9BQU8sQ0FBQyxtQkFBbUIsQ0FBQyxDQUFDO0FBQzVDLElBQU0sSUFBSSxHQUFHLE9BQU8sQ0FBQyxlQUFlLENBQUMsQ0FBQzs7O0FBR3RDLFNBQVMsYUFBYSxDQUFDLFNBQVMsRUFBRTtBQUM5QixRQUFNLFNBQVMsR0FBRyxJQUFJLE1BQU0sQ0FBQyxNQUFNLEVBQUEsQ0FBQztBQUNwQyxTQUFLLElBQUksQ0FBQyxHQUFHLENBQUMsRUFBRSxDQUFDLEdBQUcsU0FBUyxDQUFDLE1BQU0sRUFBRSxDQUFDLEdBQUcsQ0FBQyxHQUFHLENBQUM7QUFDM0MsaUJBQVMsQ0FBQyxTQUFTLENBQUMsQ0FBQyxDQUFDLENBQUMsR0FBRyxTQUFTLENBQUMsQ0FBQyxHQUFDLENBQUMsQ0FBQyxDQUFDO0tBQUEsS0FFeEMsSUFBSSxDQUFDLElBQUksU0FBUyxFQUFFO0FBQ3JCLFlBQUksU0FBUyxDQUFDLENBQUMsQ0FBQyxLQUFLLFNBQVMsRUFDMUIsU0FBUyxDQUFDLENBQUMsQ0FBQyxHQUFHLFNBQVMsQ0FBQyxDQUFDLENBQUMsQ0FBQztLQUNuQztBQUNELFdBQU8sU0FBUyxDQUFDO0NBQ3BCOzs7QUFHRCxTQUFTLFVBQVUsQ0FBQyxJQUFJLEVBQUU7QUFDdEIsUUFBTSxJQUFJLEdBQUcsSUFBSSxDQUFDLFFBQVEsQ0FBQztBQUMzQixRQUFJLENBQUMsSUFBSSxDQUFDLFFBQVEsRUFBRTtBQUNoQixlQUFPLENBQUMsV0FBVyxFQUFFLElBQUksQ0FBQyxJQUFJLENBQUMsQ0FBQztLQUNuQztBQUNELFFBQUksSUFBSSxDQUFDLElBQUksS0FBSyxTQUFTLEVBQUU7QUFDekIsWUFBSSxPQUFPLElBQUksQ0FBQyxLQUFLLEtBQUssUUFBUSxFQUM5QixPQUFPLENBQUMsZUFBZSxFQUFFLElBQUksQ0FBQyxLQUFLLENBQUMsQ0FBQztBQUN6QyxZQUFJLE9BQU8sSUFBSSxDQUFDLEtBQUssS0FBSyxRQUFROztBQUU5QixtQkFBTyxDQUFDLGVBQWUsRUFBRSxJQUFJLENBQUMsS0FBSyxHQUFHLEVBQUUsQ0FBQyxDQUFDO0tBQ2pEO0FBQ0QsV0FBTyxDQUFDLFVBQVUsRUFBRSxJQUFJLENBQUMsQ0FBQztDQUM3Qjs7QUFFRCxTQUFTLGNBQWMsQ0FBQyxFQUFFLEVBQUU7QUFDeEIsWUFBUSxFQUFFO0FBQ04sYUFBSyxHQUFHLENBQUMsS0FBTSxHQUFHLENBQUMsS0FBTSxHQUFHO0FBQ3hCLG1CQUFPLEtBQUssQ0FBQyxVQUFVLENBQUM7QUFBQSxhQUN2QixHQUFHO0FBQ0osbUJBQU8sS0FBSyxDQUFDLFdBQVcsQ0FBQztBQUFBLGFBQ3hCLFFBQVE7QUFDVCxtQkFBTyxLQUFLLENBQUMsVUFBVSxDQUFDO0FBQUEsYUFDdkIsTUFBTSxDQUFDLEtBQU0sUUFBUTtBQUN0QixtQkFBTyxJQUFJLENBQUM7QUFBQSxLQUNuQjtDQUNKOztBQUVELFNBQVMsY0FBYyxDQUFDLEVBQUUsRUFBRTtBQUN4QixZQUFRLEVBQUU7QUFDTixhQUFLLElBQUksQ0FBQyxLQUFNLElBQUksQ0FBQyxLQUFNLEtBQUssQ0FBQyxLQUFNLEtBQUssQ0FBQztBQUM3QyxhQUFLLEdBQUcsQ0FBQyxLQUFNLEdBQUcsQ0FBQyxLQUFNLElBQUksQ0FBQyxLQUFNLElBQUksQ0FBQztBQUN6QyxhQUFLLElBQUksQ0FBQyxLQUFNLFlBQVk7QUFDeEIsbUJBQU8sSUFBSSxDQUFDO0FBQUEsS0FDbkI7QUFDRCxXQUFPLEtBQUssQ0FBQztDQUNoQjs7QUFFRCxTQUFTLFVBQVUsQ0FBQyxJQUFJLEVBQUUsU0FBUyxFQUFFLENBQUMsRUFBRTtBQUNwQyxRQUFNLEdBQUcsR0FBRyxJQUFJLEtBQUssQ0FBQyxJQUFJLEVBQUEsQ0FBQztBQUMzQixRQUFNLE9BQU8sR0FBRyxDQUFDLENBQUMsSUFBSSxDQUFDLE1BQU0sRUFBRSxTQUFTLEVBQUUsU0FBUyxDQUFDLENBQUM7QUFDckQsUUFBSSxJQUFJLENBQUMsUUFBUSxDQUFDLElBQUksS0FBSyxZQUFZLEVBQUU7O0FBRXJDLFNBQUMsQ0FBQyxJQUFJLENBQUMsUUFBUSxFQUFFLFNBQVMsRUFBRSxTQUFTLENBQUMsQ0FBQztLQUMxQztBQUNELFFBQU0sT0FBTyxHQUFHLFVBQVUsQ0FBQyxJQUFJLENBQUMsQ0FBQzs7QUFFakMsZUFBVyxDQUFDLElBQUksQ0FBQyxFQUFDLEdBQUcsRUFBRSxPQUFPO0FBQ1osWUFBSSxFQUFFLE9BQU8sQ0FBQyxDQUFDLENBQUM7QUFDaEIsZUFBTyxFQUFFLEdBQUcsRUFBQyxDQUFDLENBQUM7QUFDakMsV0FBTyxDQUFDLFNBQVMsQ0FBQyxJQUFJLElBQUksQ0FBQyxRQUFRLENBQUMsT0FBTyxDQUFDLENBQUMsQ0FBQyxFQUFFLEdBQUcsQ0FBQyxDQUFDLENBQUM7OztBQUd0RCxXQUFPLENBQUMsT0FBTyxFQUFFLEdBQUcsQ0FBQyxDQUFDO0NBQ3pCOzs7QUFHRCxJQUFNLGFBQWEsR0FBRyxFQUFFLENBQUM7QUFDekIsSUFBTSxXQUFXLEdBQUcsRUFBRSxDQUFDO0FBQ3ZCLFNBQVMsZ0JBQWdCLEdBQUc7QUFDeEIsaUJBQWEsQ0FBQyxNQUFNLEdBQUcsQ0FBQyxDQUFDO0FBQ3pCLGVBQVcsQ0FBQyxNQUFNLEdBQUcsQ0FBQyxDQUFDO0NBQzFCOztBQUVELElBQUksSUFBSSxZQUFBLENBQUM7QUFDVCxTQUFTLGNBQWMsQ0FBQyxHQUFHLEVBQUUsVUFBVSxFQUFFLE9BQU8sRUFBRTs7O0FBRzlDLFFBQUksR0FBRyxPQUFPLElBQUksSUFBSSxDQUFDOzs7QUFHdkIsU0FBSyxJQUFJLENBQUMsR0FBQyxDQUFDLEVBQUUsQ0FBQyxHQUFHLGFBQWEsQ0FBQyxNQUFNLEVBQUUsQ0FBQyxFQUFFLEVBQUU7QUFDekMsWUFBSSxVQUFVLENBQUMsTUFBTSxDQUFDLGFBQWEsQ0FBQyxDQUFDLENBQUMsQ0FBQyxFQUFFOzs7QUFHcEMsbUJBQU8sS0FBSyxDQUFDO1NBQ2hCO0tBQ0w7OztBQUdELGlCQUFhLENBQUMsSUFBSSxDQUFDLFVBQVUsQ0FBQyxDQUFDOzs7QUFHL0IsUUFBTSxtQkFBbUIsR0FBRyxJQUFJLENBQUMsSUFBSSxDQUFDOztBQUVsQyxrQkFBVSxFQUFFLG9CQUFVLElBQUksRUFBRSxTQUFTLEVBQUUsQ0FBQyxFQUFFO0FBQ3RDLG1CQUFPLFNBQVMsQ0FBQyxFQUFFLENBQUMsU0FBUyxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsQ0FBQztTQUM1Qzs7QUFFRCxzQkFBYyxFQUFFLHdCQUFVLElBQUksRUFBRSxTQUFTLEVBQUUsQ0FBQyxFQUFFO0FBQzFDLG1CQUFPLFNBQVMsQ0FBQyxJQUFJLENBQUM7U0FDekI7O0FBRUQsZUFBTyxFQUFFLGlCQUFVLElBQUksRUFBRSxTQUFTLEVBQUUsQ0FBQyxFQUFFO0FBQ25DLGdCQUFNLEdBQUcsR0FBRyxJQUFJLEtBQUssQ0FBQyxJQUFJLEVBQUEsQ0FBQztBQUMzQixnQkFBSSxJQUFJLENBQUMsS0FBSyxFQUFFOzs7QUFHWix1QkFBTyxHQUFHLENBQUM7YUFDZDtBQUNELG9CQUFRLE9BQU8sSUFBSSxDQUFDLEtBQUs7QUFDekIscUJBQUssUUFBUTtBQUNULCtCQUFXLENBQUMsSUFBSSxDQUFDLEVBQUMsSUFBSSxFQUFFLEtBQUssQ0FBQyxVQUFVO0FBQ3RCLGdDQUFRLEVBQUUsR0FBRyxFQUFDLENBQUMsQ0FBQztBQUNsQyx1QkFBRyxDQUFDLE9BQU8sQ0FBQyxLQUFLLENBQUMsVUFBVSxDQUFDLENBQUM7QUFDOUIsMEJBQU07QUFBQSxxQkFDTCxRQUFRO0FBQ1QsK0JBQVcsQ0FBQyxJQUFJLENBQUMsRUFBQyxJQUFJLEVBQUUsS0FBSyxDQUFDLFVBQVU7QUFDdEIsZ0NBQVEsRUFBRSxHQUFHLEVBQUMsQ0FBQyxDQUFDO0FBQ2xDLHVCQUFHLENBQUMsT0FBTyxDQUFDLEtBQUssQ0FBQyxVQUFVLENBQUMsQ0FBQztBQUM5QiwwQkFBTTtBQUFBLHFCQUNMLFNBQVM7QUFDViwrQkFBVyxDQUFDLElBQUksQ0FBQyxFQUFDLElBQUksRUFBRSxLQUFLLENBQUMsV0FBVztBQUN2QixnQ0FBUSxFQUFFLEdBQUcsRUFBQyxDQUFDLENBQUM7QUFDbEMsdUJBQUcsQ0FBQyxPQUFPLENBQUMsS0FBSyxDQUFDLFdBQVcsQ0FBQyxDQUFDO0FBQy9CLDBCQUFNO0FBQUEscUJBQ0wsUUFBUTs7O0FBR1QsMEJBQU07QUFBQSxxQkFDTCxVQUFVO0FBQ1gsMEJBQU0sSUFBSSxLQUFLLENBQUMsc0NBQXNDLENBQUMsQ0FBQztBQUFBLGFBQzNEO0FBQ0QsbUJBQU8sR0FBRyxDQUFDO1NBQ2Q7O0FBRUQsNEJBQW9CLEVBQUUsOEJBQVUsSUFBSSxFQUFFLFNBQVMsRUFBRSxDQUFDLEVBQUU7QUFDaEQsZ0JBQU0sT0FBTyxHQUFHLENBQUMsQ0FBQyxJQUFJLENBQUMsS0FBSyxFQUFFLFNBQVMsRUFBRSxTQUFTLENBQUMsQ0FBQztBQUNwRCxnQkFBSSxJQUFJLENBQUMsSUFBSSxDQUFDLElBQUksS0FBSyxrQkFBa0IsRUFBRTs7QUFFdkMsb0JBQU0sT0FBTyxHQUFHLElBQUksQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDO0FBQy9CLG9CQUFNLE9BQU8sR0FBRyxTQUFTLENBQUMsRUFBRSxDQUFDLFNBQVMsQ0FBQyxPQUFPLENBQUMsQ0FBQzs7QUFFaEQsb0JBQUksSUFBSSxDQUFDLFFBQVEsS0FBSyxHQUFHLEVBQUU7O0FBRXZCLCtCQUFXLENBQUMsSUFBSSxDQUFDO0FBQ2IsNEJBQUksRUFBRSxPQUFPO0FBQ2IsMEJBQUUsRUFBRSxPQUFPO3FCQUNkLENBQUMsQ0FBQztBQUNILDJCQUFPLENBQUMsU0FBUyxDQUFDLE9BQU8sQ0FBQyxDQUFDOztBQUUzQiwyQkFBTyxPQUFPLENBQUM7aUJBQ2xCO0FBQ0Qsb0JBQU0sT0FBTyxHQUFHLElBQUksS0FBSyxDQUFDLElBQUksRUFBQSxDQUFDO0FBQy9CLG9CQUFJLElBQUksQ0FBQyxRQUFRLEtBQUssSUFBSSxFQUFFOztBQUV4QiwrQkFBVyxDQUFDLElBQUksQ0FBQztBQUNiLGlDQUFTLEVBQUUsT0FBTztBQUNsQixpQ0FBUyxFQUFFLE9BQU87QUFDbEIsOEJBQU0sRUFBRSxPQUFPO3FCQUNsQixDQUFDLENBQUM7QUFDSCwyQkFBTyxDQUFDLFNBQVMsQ0FBQyxJQUFJLElBQUksQ0FBQyxPQUFPLENBQUMsT0FBTyxFQUFFLE9BQU8sQ0FBQyxDQUFDLENBQUM7QUFDdEQsMkJBQU8sQ0FBQyxTQUFTLENBQUMsSUFBSSxJQUFJLENBQUMsT0FBTyxDQUFDLE9BQU8sRUFBRSxPQUFPLENBQUMsQ0FBQyxDQUFDO2lCQUN6RCxNQUFNOztBQUVILCtCQUFXLENBQUMsSUFBSSxDQUFDO0FBQ2IsNEJBQUksRUFBQyxLQUFLLENBQUMsVUFBVTtBQUNyQixnQ0FBUSxFQUFFLE9BQU87cUJBQ3BCLENBQUMsQ0FBQztBQUNILDJCQUFPLENBQUMsT0FBTyxDQUFDLEtBQUssQ0FBQyxVQUFVLENBQUMsQ0FBQztpQkFDckM7QUFDRCx1QkFBTyxPQUFPLENBQUM7YUFDbEIsTUFBTTs7QUFFSCxvQkFBTSxPQUFPLEdBQUcsQ0FBQyxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsTUFBTSxFQUFFLFNBQVMsRUFBRSxTQUFTLENBQUMsQ0FBQztBQUMxRCxvQkFBTSxPQUFPLEdBQUcsVUFBVSxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsQ0FBQztBQUN0QyxvQkFBSSxJQUFJLENBQUMsUUFBUSxLQUFLLEdBQUcsRUFBRTs7QUFFdkIsK0JBQVcsQ0FBQyxJQUFJLENBQUM7QUFDYiwyQkFBRyxFQUFFLE9BQU87QUFDWiw0QkFBSSxFQUFFLE9BQU8sQ0FBQyxDQUFDLENBQUM7QUFDaEIsa0NBQVUsRUFBRSxPQUFPO3FCQUN0QixDQUFDLENBQUM7QUFDSCwyQkFBTyxDQUFDLFNBQVMsQ0FBQyxJQUFJLElBQUksQ0FBQyxTQUFTLENBQUMsT0FBTyxDQUFDLENBQUMsQ0FBQyxFQUFFLE9BQU8sQ0FBQyxDQUFDLENBQUM7O0FBRTNELHdCQUFJLE9BQU8sQ0FBQyxDQUFDLENBQUMsS0FBSyxlQUFlLEVBQUU7QUFDaEMsK0JBQU8sQ0FBQyxTQUFTLENBQUMsSUFBSSxJQUFJLENBQUMsU0FBUyxDQUFDLElBQUksRUFBRSxPQUFPLENBQUMsQ0FBQyxDQUFDO3FCQUN4RDtBQUNELDJCQUFPLE9BQU8sQ0FBQztpQkFDbEI7QUFDRCxvQkFBTSxPQUFPLEdBQUcsSUFBSSxLQUFLLENBQUMsSUFBSSxFQUFBLENBQUM7QUFDL0Isb0JBQU0sVUFBVSxHQUFHLFVBQVUsQ0FBQyxJQUFJLENBQUMsSUFBSSxFQUFFLFNBQVMsRUFBRSxDQUFDLENBQUMsQ0FBQztBQUN2RCxvQkFBSSxJQUFJLENBQUMsUUFBUSxLQUFLLElBQUksRUFBRTs7QUFFeEIsK0JBQVcsQ0FBQyxJQUFJLENBQUM7QUFDYixpQ0FBUyxFQUFFLFVBQVUsQ0FBQyxDQUFDLENBQUM7QUFDeEIsaUNBQVMsRUFBRSxPQUFPO0FBQ2xCLDhCQUFNLEVBQUUsT0FBTztxQkFDbEIsQ0FBQyxDQUFDO0FBQ0gsOEJBQVUsQ0FBQyxDQUFDLENBQUMsQ0FBQyxTQUFTLENBQUMsSUFBSSxJQUFJLENBQUMsT0FBTyxDQUFDLE9BQU8sRUFBRSxPQUFPLENBQUMsQ0FBQyxDQUFDO0FBQzVELDJCQUFPLENBQUMsU0FBUyxDQUFDLElBQUksSUFBSSxDQUFDLE9BQU8sQ0FBQyxVQUFVLENBQUMsQ0FBQyxDQUFDLEVBQUUsT0FBTyxDQUFDLENBQUMsQ0FBQztpQkFDL0QsTUFBTTs7QUFFSCwrQkFBVyxDQUFDLElBQUksQ0FBQztBQUNiLDRCQUFJLEVBQUUsS0FBSyxDQUFDLFVBQVU7QUFDdEIsZ0NBQVEsRUFBRSxPQUFPO3FCQUNwQixDQUFDLENBQUM7QUFDSCwyQkFBTyxDQUFDLE9BQU8sQ0FBQyxLQUFLLENBQUMsVUFBVSxDQUFDLENBQUM7aUJBQ3JDO0FBQ0QsdUJBQU8sT0FBTyxDQUFDO2FBQ2xCO1NBQ0o7O0FBRUQsMkJBQW1CLEVBQUUsNkJBQVUsSUFBSSxFQUFFLFNBQVMsRUFBRSxDQUFDLEVBQUU7QUFDL0MsaUJBQUssSUFBSSxDQUFDLEdBQUcsQ0FBQyxFQUFFLENBQUMsR0FBRyxJQUFJLENBQUMsWUFBWSxDQUFDLE1BQU0sRUFBRSxDQUFDLEVBQUUsRUFBRTtBQUMvQyxvQkFBTSxJQUFJLEdBQUcsSUFBSSxDQUFDLFlBQVksQ0FBQyxDQUFDLENBQUMsQ0FBQztBQUNsQyxvQkFBSSxJQUFJLENBQUMsSUFBSSxFQUFFO0FBQ1gsd0JBQU0sT0FBTyxHQUFHLFNBQVMsQ0FBQyxFQUFFLENBQUMsU0FBUyxDQUFDLElBQUksQ0FBQyxFQUFFLENBQUMsSUFBSSxDQUFDLENBQUM7QUFDckQsd0JBQU0sT0FBTyxHQUFHLENBQUMsQ0FBQyxJQUFJLENBQUMsSUFBSSxFQUFFLFNBQVMsRUFBRSxTQUFTLENBQUMsQ0FBQztBQUNuRCwrQkFBVyxDQUFDLElBQUksQ0FBQyxFQUFDLElBQUksRUFBRSxPQUFPO0FBQ2IsMEJBQUUsRUFBRSxPQUFPLEVBQUMsQ0FBQyxDQUFDO0FBQ2hDLDJCQUFPLENBQUMsU0FBUyxDQUFDLE9BQU8sQ0FBQyxDQUFDO2lCQUM5QjthQUNKO1NBQ0o7O0FBRUQseUJBQWlCLEVBQUUsMkJBQVUsSUFBSSxFQUFFLFNBQVMsRUFBRSxDQUFDLEVBQUU7QUFDN0MsZ0JBQU0sR0FBRyxHQUFHLElBQUksS0FBSyxDQUFDLElBQUksRUFBQSxDQUFDO0FBQzNCLGdCQUFNLElBQUksR0FBRyxDQUFDLENBQUMsSUFBSSxDQUFDLElBQUksRUFBRSxTQUFTLEVBQUUsU0FBUyxDQUFDLENBQUM7QUFDaEQsZ0JBQU0sS0FBSyxHQUFHLENBQUMsQ0FBQyxJQUFJLENBQUMsS0FBSyxFQUFFLFNBQVMsRUFBRSxTQUFTLENBQUMsQ0FBQztBQUNsRCx1QkFBVyxDQUFDLElBQUksQ0FBQyxFQUFDLElBQUksRUFBRSxJQUFJLEVBQUUsRUFBRSxFQUFFLEdBQUcsRUFBQyxFQUNyQixFQUFDLElBQUksRUFBRSxLQUFLLEVBQUUsRUFBRSxFQUFFLEdBQUcsRUFBQyxDQUFDLENBQUM7QUFDekMsZ0JBQUksQ0FBQyxTQUFTLENBQUMsR0FBRyxDQUFDLENBQUM7QUFDcEIsaUJBQUssQ0FBQyxTQUFTLENBQUMsR0FBRyxDQUFDLENBQUM7QUFDckIsbUJBQU8sR0FBRyxDQUFDO1NBQ2Q7O0FBRUQsNkJBQXFCLEVBQUUsK0JBQVUsSUFBSSxFQUFFLFNBQVMsRUFBRSxDQUFDLEVBQUU7QUFDakQsZ0JBQU0sR0FBRyxHQUFHLElBQUksS0FBSyxDQUFDLElBQUksRUFBQSxDQUFDO0FBQzNCLGFBQUMsQ0FBQyxJQUFJLENBQUMsSUFBSSxFQUFFLFNBQVMsRUFBRSxTQUFTLENBQUMsQ0FBQztBQUNuQyxnQkFBTSxJQUFJLEdBQUcsQ0FBQyxDQUFDLElBQUksQ0FBQyxVQUFVLEVBQUUsU0FBUyxFQUFFLFNBQVMsQ0FBQyxDQUFDO0FBQ3RELGdCQUFNLEdBQUcsR0FBRyxDQUFDLENBQUMsSUFBSSxDQUFDLFNBQVMsRUFBRSxTQUFTLEVBQUUsU0FBUyxDQUFDLENBQUM7QUFDcEQsdUJBQVcsQ0FBQyxJQUFJLENBQUMsRUFBQyxJQUFJLEVBQUUsSUFBSSxFQUFFLEVBQUUsRUFBRSxHQUFHLEVBQUMsRUFDckIsRUFBQyxJQUFJLEVBQUUsR0FBRyxFQUFFLEVBQUUsRUFBRSxHQUFHLEVBQUMsQ0FBQyxDQUFDO0FBQ3ZDLGdCQUFJLENBQUMsU0FBUyxDQUFDLEdBQUcsQ0FBQyxDQUFDO0FBQ3BCLGVBQUcsQ0FBQyxTQUFTLENBQUMsR0FBRyxDQUFDLENBQUM7QUFDbkIsbUJBQU8sR0FBRyxDQUFDO1NBQ2Q7O0FBRUQscUJBQWEsRUFBRSx1QkFBVSxJQUFJLEVBQUUsU0FBUyxFQUFFLENBQUMsRUFBRTtBQUN6QyxnQkFBTSxHQUFHLEdBQUcsSUFBSSxLQUFLLENBQUMsSUFBSSxFQUFBLENBQUM7QUFDM0IsZ0JBQU0sTUFBTSxHQUFHLENBQUMsQ0FBQyxJQUFJLENBQUMsTUFBTSxFQUFFLFNBQVMsRUFBRSxTQUFTLENBQUMsQ0FBQztBQUNwRCxnQkFBTSxJQUFJLEdBQUcsRUFBRSxDQUFDO0FBQ2hCLGlCQUFLLElBQUksQ0FBQyxHQUFHLENBQUMsRUFBRSxDQUFDLEdBQUcsSUFBSSxDQUFDLFNBQVMsQ0FBQyxNQUFNLEVBQUUsQ0FBQyxFQUFFLEVBQUU7QUFDNUMsb0JBQUksQ0FBQyxJQUFJLENBQUMsQ0FBQyxDQUFDLElBQUksQ0FBQyxTQUFTLENBQUMsQ0FBQyxDQUFDLEVBQUUsU0FBUyxFQUFFLFNBQVMsQ0FBQyxDQUFDLENBQUM7YUFDekQ7QUFDRCxnQkFBTSxRQUFRLEdBQUcsU0FBUyxDQUFDLEtBQUssQ0FBQyxTQUFTLENBQUMsSUFBSSxDQUFDLFFBQVEsQ0FBQyxDQUFDLENBQUM7QUFDM0QsdUJBQVcsQ0FBQyxJQUFJLENBQUMsRUFBQyxXQUFXLEVBQUUsTUFBTTtBQUNuQixvQkFBSSxFQUFFLElBQUk7QUFDVixtQkFBRyxFQUFFLEdBQUc7QUFDUixtQkFBRyxFQUFFLFNBQVMsQ0FBQyxHQUFHO0FBQ2xCLHFCQUFLLEVBQUUsUUFBUSxFQUFDLENBQUMsQ0FBQztBQUNwQyxrQkFBTSxDQUFDLFNBQVMsQ0FDWixJQUFJLElBQUksQ0FBQyxNQUFNLENBQ1gsSUFBSSxFQUNKLEdBQUcsRUFDSCxTQUFTLENBQUMsR0FBRyxFQUNiLFFBQVEsQ0FBQyxDQUFDLENBQUM7QUFDbkIsbUJBQU8sR0FBRyxDQUFDO1NBQ2Q7O0FBRUQsdUJBQWUsRUFBRSx5QkFBVSxJQUFJLEVBQUUsU0FBUyxFQUFFLENBQUMsRUFBRTtBQUMzQyxnQkFBTSxHQUFHLEdBQUcsSUFBSSxLQUFLLENBQUMsSUFBSSxFQUFBLENBQUM7QUFDM0IsZ0JBQU0sT0FBTyxHQUFHLElBQUksS0FBSyxDQUFDLE9BQU8sQ0FBQyxJQUFJLEtBQUssQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDLE1BQU0sQ0FBQyxLQUFLLENBQUMsQ0FBQyxDQUFDOztBQUVyRSxtQkFBTyxDQUFDLE9BQU8sQ0FBQyxRQUFRLENBQUMsQ0FBQyxPQUFPLENBQUMsS0FBSyxDQUFDLFVBQVUsQ0FBQyxDQUFDOztBQUVwRCx1QkFBVyxDQUFDLElBQUksQ0FBQyxFQUFDLElBQUksRUFBRSxPQUFPLEVBQUUsUUFBUSxFQUFFLEdBQUcsRUFBQyxDQUFDLENBQUM7QUFDakQsZUFBRyxDQUFDLE9BQU8sQ0FBQyxPQUFPLENBQUMsQ0FBQzs7O0FBR3JCLGlCQUFLLElBQUksQ0FBQyxHQUFHLENBQUMsRUFBRSxDQUFDLEdBQUcsSUFBSSxDQUFDLFFBQVEsQ0FBQyxNQUFNLEVBQUUsQ0FBQyxFQUFFLEVBQUU7QUFDM0Msb0JBQU0sT0FBTyxHQUFHLENBQUMsQ0FBQyxJQUFJLENBQUMsUUFBUSxDQUFDLENBQUMsQ0FBQyxFQUFFLFNBQVMsRUFBRSxTQUFTLENBQUMsQ0FBQzs7QUFFMUQsb0JBQU0sSUFBSSxHQUFHLENBQUMsR0FBRyxFQUFFLENBQUM7QUFDcEIsMkJBQVcsQ0FBQyxJQUFJLENBQUMsRUFBQyxHQUFHLEVBQUUsR0FBRyxFQUFFLElBQUksRUFBRSxJQUFJLEVBQUUsSUFBSSxFQUFFLE9BQU8sRUFBQyxDQUFDLENBQUM7QUFDeEQsMkJBQVcsQ0FBQyxJQUFJLENBQUMsRUFBQyxHQUFHLEVBQUUsR0FBRyxFQUFFLElBQUksRUFBRSxJQUFJLEVBQUUsSUFBSSxFQUFFLE9BQU8sRUFBQyxDQUFDLENBQUM7QUFDeEQsbUJBQUcsQ0FBQyxTQUFTLENBQUMsSUFBSSxJQUFJLENBQUMsU0FBUyxDQUFDLElBQUksRUFBRSxPQUFPLENBQUMsQ0FBQyxDQUFDO0FBQ2pELG1CQUFHLENBQUMsU0FBUyxDQUFDLElBQUksSUFBSSxDQUFDLFNBQVMsQ0FBQyxJQUFJLEVBQUUsT0FBTyxDQUFDLENBQUMsQ0FBQzthQUNwRDtBQUNELG1CQUFPLEdBQUcsQ0FBQztTQUNkOztBQUVELHdCQUFnQixFQUFFLDBCQUFVLElBQUksRUFBRSxTQUFTLEVBQUUsQ0FBQyxFQUFFO0FBQzVDLGdCQUFNLEdBQUcsR0FBRyxJQUFJLEtBQUssQ0FBQyxJQUFJLEVBQUEsQ0FBQztBQUMzQixnQkFBTSxPQUFPLEdBQUcsSUFBSSxLQUFLLENBQUMsT0FBTyxDQUFDLElBQUksS0FBSyxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsTUFBTSxDQUFDLE1BQU0sQ0FBQyxDQUFDLENBQUM7QUFDdEUsdUJBQVcsQ0FBQyxJQUFJLENBQUMsRUFBQyxJQUFJLEVBQUUsT0FBTyxFQUFFLFFBQVEsRUFBRSxHQUFHLEVBQUMsQ0FBQyxDQUFDO0FBQ2pELGVBQUcsQ0FBQyxPQUFPLENBQUMsT0FBTyxDQUFDLENBQUM7O0FBRXJCLGlCQUFLLElBQUksQ0FBQyxHQUFHLENBQUMsRUFBRSxDQUFDLEdBQUcsSUFBSSxDQUFDLFVBQVUsQ0FBQyxNQUFNLEVBQUUsQ0FBQyxFQUFFLEVBQUU7QUFDN0Msb0JBQU0sUUFBUSxHQUFHLElBQUksQ0FBQyxVQUFVLENBQUMsQ0FBQyxDQUFDLENBQUM7QUFDcEMsb0JBQU0sT0FBTyxHQUFHLFFBQVEsQ0FBQyxHQUFHLENBQUM7QUFDN0Isb0JBQUksS0FBSSxZQUFBLENBQUM7QUFDVCxvQkFBTSxRQUFRLEdBQUcsUUFBUSxDQUFDLEtBQUssQ0FBQzs7QUFFaEMsb0JBQU0sT0FBTyxHQUFHLENBQUMsQ0FBQyxRQUFRLEVBQUUsU0FBUyxFQUFFLFNBQVMsQ0FBQyxDQUFDOztBQUVsRCxvQkFBSSxPQUFPLENBQUMsSUFBSSxLQUFLLFlBQVksRUFBRTtBQUMvQix5QkFBSSxHQUFHLE9BQU8sQ0FBQyxJQUFJLENBQUM7aUJBQ3ZCLE1BQU0sSUFBSSxPQUFPLE9BQU8sQ0FBQyxLQUFLLEtBQUssUUFBUSxFQUFFO0FBQzFDLHlCQUFJLEdBQUcsT0FBTyxDQUFDLEtBQUssQ0FBQztpQkFDeEIsTUFBTSxJQUFJLE9BQU8sT0FBTyxDQUFDLEtBQUssS0FBSyxRQUFRLEVBQUU7O0FBRTFDLHlCQUFJLEdBQUcsT0FBTyxDQUFDLEtBQUssR0FBRyxFQUFFLENBQUM7aUJBQzdCO0FBQ0QsMkJBQVcsQ0FBQyxJQUFJLENBQUMsRUFBQyxHQUFHLEVBQUUsR0FBRyxFQUFFLElBQUksRUFBRSxLQUFJLEVBQUUsSUFBSSxFQUFFLE9BQU8sRUFBQyxDQUFDLENBQUM7QUFDeEQsbUJBQUcsQ0FBQyxTQUFTLENBQUMsSUFBSSxJQUFJLENBQUMsU0FBUyxDQUFDLEtBQUksRUFBRSxPQUFPLENBQUMsQ0FBQyxDQUFDO2FBQ3BEO0FBQ0QsbUJBQU8sR0FBRyxDQUFDO1NBQ2Q7O0FBRUQsMEJBQWtCLEVBQUUsNEJBQVUsSUFBSSxFQUFFLFNBQVMsRUFBRSxDQUFDLEVBQUU7QUFDOUMsZ0JBQUksQ0FBQyxJQUFJLENBQUMsV0FBVyxFQUFFO0FBQ25CLG9CQUFJLENBQUMsV0FBVyxHQUFHLEVBQUUsQ0FBQzthQUN6QjtBQUNELGdCQUFJLFVBQVUsR0FBRyxJQUFJLENBQUM7QUFDdEIsZ0JBQUksQ0FBQyxXQUFXLENBQUMsT0FBTyxDQUFDLFVBQVUsTUFBTSxFQUFFO0FBQ3ZDLG9CQUFJLE1BQU0sQ0FBQyxFQUFFLEtBQUssU0FBUyxDQUFDLEVBQUUsRUFBRTtBQUM1Qiw4QkFBVSxHQUFHLE1BQU0sQ0FBQztpQkFDdkI7YUFDSixDQUFDLENBQUM7QUFDSCxnQkFBSSxDQUFDLFVBQVUsRUFBRTtBQUNiLDBCQUFVLEdBQ0osSUFBSSxLQUFLLENBQUMsTUFBTSxDQUFDLElBQUksS0FBSyxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsTUFBTSxDQUFDLFFBQVEsQ0FBQyxFQUNwQyxzQkFBc0IsRUFDdEIsSUFBSSxDQUFDLElBQUksQ0FBQyxRQUFRLENBQUMsQ0FBQyxnQkFBZ0IsRUFBRSxFQUN0QyxTQUFTLENBQUMsRUFBRSxFQUNaLElBQUksRUFDSixJQUFJLENBQUMsTUFBTSxDQUFDLE1BQU0sQ0FBQyxDQUFDO0FBQzNDLG9CQUFJLENBQUMsV0FBVyxDQUFDLElBQUksQ0FBQyxVQUFVLENBQUMsQ0FBQztBQUNsQyxvQkFBTSxlQUFlLEdBQ2pCLElBQUksS0FBSyxDQUFDLE9BQU8sQ0FBQyxJQUFJLEtBQUssQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDLE1BQU0sQ0FBQyxNQUFNLENBQUMsRUFDbEMsYUFBYSxDQUFDLENBQUM7O0FBRXJDLG9CQUFNLGFBQWEsR0FBRyxVQUFVLENBQUMsT0FBTyxDQUFDLFdBQVcsQ0FBQyxDQUFDO0FBQ3RELDJCQUFXLENBQUMsSUFBSSxDQUFDLEVBQUMsSUFBSSxFQUFFLGVBQWU7QUFDckIsNEJBQVEsRUFBRSxhQUFhLEVBQUMsQ0FBQyxDQUFDO0FBQzVDLDZCQUFhLENBQUMsT0FBTyxDQUFDLGVBQWUsQ0FBQyxDQUFDOztBQUV2QyxvQkFBTSxlQUFlLEdBQUcsZUFBZSxDQUFDLE9BQU8sQ0FBQyxhQUFhLENBQUMsQ0FBQztBQUMvRCwyQkFBVyxDQUFDLElBQUksQ0FBQyxFQUFDLElBQUksRUFBRSxVQUFVO0FBQ2hCLDRCQUFRLEVBQUUsZUFBZSxFQUFDLENBQUMsQ0FBQztBQUM5QywrQkFBZSxDQUFDLE9BQU8sQ0FBQyxVQUFVLENBQUMsQ0FBQzthQUN2QztBQUNELGdCQUFNLEdBQUcsR0FBRyxJQUFJLEtBQUssQ0FBQyxJQUFJLEVBQUEsQ0FBQztBQUMzQix1QkFBVyxDQUFDLElBQUksQ0FBQyxFQUFDLElBQUksRUFBRSxVQUFVO0FBQ2hCLHdCQUFRLEVBQUUsR0FBRyxFQUFDLENBQUMsQ0FBQztBQUNsQyxlQUFHLENBQUMsT0FBTyxDQUFDLFVBQVUsQ0FBQyxDQUFDO0FBQ3hCLG1CQUFPLEdBQUcsQ0FBQztTQUNkOztBQUVELDJCQUFtQixFQUFFLDZCQUFVLElBQUksRUFBRSxTQUFTLEVBQUUsQ0FBQyxFQUFFOztBQUUvQyxnQkFBTSxHQUFHLEdBQUcsU0FBUyxDQUFDLEVBQUUsQ0FBQyx3QkFBd0IsRUFBRSxDQUFDO0FBQ3BELGdCQUFJLENBQUMsSUFBSSxDQUFDLFdBQVcsRUFBRTtBQUNuQixvQkFBSSxDQUFDLFdBQVcsR0FBRyxFQUFFLENBQUM7YUFDekI7QUFDRCxnQkFBSSxVQUFVLEdBQUcsSUFBSSxDQUFDO0FBQ3RCLGdCQUFJLENBQUMsV0FBVyxDQUFDLE9BQU8sQ0FBQyxVQUFVLE1BQU0sRUFBRTtBQUN2QyxvQkFBSSxNQUFNLENBQUMsRUFBRSxLQUFLLEdBQUcsRUFBRTtBQUNuQiw4QkFBVSxHQUFHLE1BQU0sQ0FBQztpQkFDdkI7YUFDSixDQUFDLENBQUM7QUFDSCxnQkFBSSxDQUFDLFVBQVUsRUFBRTtBQUNiLDBCQUFVLEdBQ0osSUFBSSxLQUFLLENBQUMsTUFBTSxDQUFDLElBQUksS0FBSyxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsTUFBTSxDQUFDLFFBQVEsQ0FBQyxFQUNwQyxJQUFJLENBQUMsRUFBRSxDQUFDLElBQUksRUFDWixJQUFJLENBQUMsSUFBSSxDQUFDLFFBQVEsQ0FBQyxDQUFDLGdCQUFnQixFQUFFLEVBQ3RDLEdBQUcsRUFDSCxJQUFJLEVBQ0osSUFBSSxDQUFDLE1BQU0sQ0FBQyxNQUFNLENBQUMsQ0FBQztBQUMzQyxvQkFBSSxDQUFDLFdBQVcsQ0FBQyxJQUFJLENBQUMsVUFBVSxDQUFDLENBQUM7O0FBRWxDLG9CQUFNLGVBQWUsR0FDakIsSUFBSSxLQUFLLENBQUMsT0FBTyxDQUFDLElBQUksS0FBSyxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsTUFBTSxDQUFDLE1BQU0sQ0FBQyxFQUNsQyxJQUFJLENBQUMsRUFBRSxDQUFDLElBQUksR0FBRyxZQUFZLENBQUMsQ0FBQzs7QUFFbkQsb0JBQU0sYUFBYSxHQUFHLFVBQVUsQ0FBQyxPQUFPLENBQUMsV0FBVyxDQUFDLENBQUM7QUFDdEQsMkJBQVcsQ0FBQyxJQUFJLENBQUMsRUFBQyxJQUFJLEVBQUUsZUFBZTtBQUNyQiw0QkFBUSxFQUFFLGFBQWEsRUFBQyxDQUFDLENBQUM7QUFDNUMsNkJBQWEsQ0FBQyxPQUFPLENBQUMsZUFBZSxDQUFDLENBQUM7O0FBRXZDLG9CQUFNLGVBQWUsR0FBRyxlQUFlLENBQUMsT0FBTyxDQUFDLGFBQWEsQ0FBQyxDQUFDO0FBQy9ELDJCQUFXLENBQUMsSUFBSSxDQUFDLEVBQUMsSUFBSSxFQUFFLFVBQVU7QUFDaEIsNEJBQVEsRUFBRSxlQUFlLEVBQUMsQ0FBQyxDQUFDO0FBQzlDLCtCQUFlLENBQUMsT0FBTyxDQUFDLFVBQVUsQ0FBQyxDQUFDO2FBQ3ZDO0FBQ0QsZ0JBQU0sT0FBTyxHQUFHLEdBQUcsQ0FBQyxTQUFTLENBQUMsSUFBSSxDQUFDLEVBQUUsQ0FBQyxJQUFJLENBQUMsQ0FBQzs7QUFFNUMsdUJBQVcsQ0FBQyxJQUFJLENBQUMsRUFBQyxJQUFJLEVBQUUsVUFBVTtBQUNoQix3QkFBUSxFQUFFLE9BQU8sRUFBQyxDQUFDLENBQUM7QUFDdEMsbUJBQU8sQ0FBQyxPQUFPLENBQUMsVUFBVSxDQUFDLENBQUM7O0FBRTVCLG1CQUFPLEtBQUssQ0FBQyxRQUFRLENBQUM7U0FDekI7O0FBRUQsMEJBQWtCLEVBQUUsNEJBQVUsSUFBSSxFQUFFLFNBQVMsRUFBRSxDQUFDLEVBQUU7QUFDOUMsZ0JBQU0sU0FBUyxHQUFHLElBQUksQ0FBQyxXQUFXLENBQUMsTUFBTSxHQUFHLENBQUMsQ0FBQztBQUM5QyxpQkFBSyxJQUFJLENBQUMsR0FBRyxDQUFDLEVBQUUsQ0FBQyxHQUFHLFNBQVMsRUFBRSxDQUFDLEVBQUUsRUFBRTtBQUNoQyxpQkFBQyxDQUFDLElBQUksQ0FBQyxXQUFXLENBQUMsQ0FBQyxDQUFDLEVBQUUsU0FBUyxFQUFFLFNBQVMsQ0FBQyxDQUFDO2FBQ2hEO0FBQ0QsbUJBQU8sQ0FBQyxDQUFDLElBQUksQ0FBQyxXQUFXLENBQUMsU0FBUyxDQUFDLEVBQUUsU0FBUyxFQUFFLFNBQVMsQ0FBQyxDQUFDO1NBQy9EOztBQUVELHVCQUFlLEVBQUUseUJBQVUsSUFBSSxFQUFFLFNBQVMsRUFBRSxDQUFDLEVBQUU7QUFDM0MsYUFBQyxDQUFDLElBQUksQ0FBQyxRQUFRLEVBQUUsU0FBUyxFQUFFLFNBQVMsQ0FBQyxDQUFDO0FBQ3ZDLGdCQUFNLEdBQUcsR0FBRyxJQUFJLEtBQUssQ0FBQyxJQUFJLEVBQUEsQ0FBQztBQUMzQixnQkFBTSxJQUFJLEdBQUcsY0FBYyxDQUFDLElBQUksQ0FBQyxRQUFRLENBQUMsQ0FBQztBQUMzQyxnQkFBSSxJQUFJLEVBQUU7QUFDTiwyQkFBVyxDQUFDLElBQUksQ0FBQyxFQUFDLElBQUksRUFBRSxJQUFJO0FBQ1YsNEJBQVEsRUFBRSxHQUFHLEVBQUMsQ0FBQyxDQUFDO0FBQ2xDLG1CQUFHLENBQUMsT0FBTyxDQUFDLElBQUksQ0FBQyxDQUFDO2FBQ3JCO0FBQ0QsbUJBQU8sR0FBRyxDQUFDO1NBQ2Q7O0FBRUQsd0JBQWdCLEVBQUUsMEJBQVUsSUFBSSxFQUFFLFNBQVMsRUFBRSxDQUFDLEVBQUU7QUFDNUMsYUFBQyxDQUFDLElBQUksQ0FBQyxRQUFRLEVBQUUsU0FBUyxFQUFFLFNBQVMsQ0FBQyxDQUFDO0FBQ3ZDLGdCQUFNLEdBQUcsR0FBRyxJQUFJLEtBQUssQ0FBQyxJQUFJLEVBQUEsQ0FBQztBQUMzQix1QkFBVyxDQUFDLElBQUksQ0FBQyxFQUFDLElBQUksRUFBRSxLQUFLLENBQUMsVUFBVTtBQUN0Qix3QkFBUSxFQUFFLEdBQUcsRUFBQyxDQUFDLENBQUM7QUFDbEMsZUFBRyxDQUFDLE9BQU8sQ0FBQyxLQUFLLENBQUMsVUFBVSxDQUFDLENBQUM7O0FBRTlCLG1CQUFPLEdBQUcsQ0FBQztTQUNkOztBQUVELHdCQUFnQixFQUFFLDBCQUFVLElBQUksRUFBRSxTQUFTLEVBQUUsQ0FBQyxFQUFFO0FBQzVDLGdCQUFNLEtBQUssR0FBRyxDQUFDLENBQUMsSUFBSSxDQUFDLElBQUksRUFBRSxTQUFTLEVBQUUsU0FBUyxDQUFDLENBQUM7QUFDakQsZ0JBQU0sS0FBSyxHQUFHLENBQUMsQ0FBQyxJQUFJLENBQUMsS0FBSyxFQUFFLFNBQVMsRUFBRSxTQUFTLENBQUMsQ0FBQztBQUNsRCxnQkFBTSxHQUFHLEdBQUcsSUFBSSxLQUFLLENBQUMsSUFBSSxFQUFBLENBQUM7O0FBRTNCLGdCQUFJLElBQUksQ0FBQyxRQUFRLElBQUksR0FBRyxFQUFFO0FBQ3RCLDJCQUFXLENBQUMsSUFBSSxDQUFDLEVBQUMsU0FBUyxFQUFFLEtBQUs7QUFDaEIsNkJBQVMsRUFBRSxLQUFLO0FBQ2hCLDBCQUFNLEVBQUUsR0FBRyxFQUFFLENBQUMsQ0FBQztBQUNqQyxxQkFBSyxDQUFDLFNBQVMsQ0FBQyxJQUFJLElBQUksQ0FBQyxPQUFPLENBQUMsS0FBSyxFQUFFLEdBQUcsQ0FBQyxDQUFDLENBQUM7QUFDOUMscUJBQUssQ0FBQyxTQUFTLENBQUMsSUFBSSxJQUFJLENBQUMsT0FBTyxDQUFDLEtBQUssRUFBRSxHQUFHLENBQUMsQ0FBQyxDQUFDO2FBQ2pELE1BQU07QUFDSCxvQkFBSSxjQUFjLENBQUMsSUFBSSxDQUFDLFFBQVEsQ0FBQyxFQUFFO0FBQy9CLCtCQUFXLENBQUMsSUFBSSxDQUFDLEVBQUMsSUFBSSxFQUFFLEtBQUssQ0FBQyxXQUFXO0FBQ3ZCLGdDQUFRLEVBQUUsR0FBRyxFQUFDLENBQUMsQ0FBQztBQUNsQyx1QkFBRyxDQUFDLE9BQU8sQ0FBQyxLQUFLLENBQUMsV0FBVyxDQUFDLENBQUM7aUJBQ2xDLE1BQU07QUFDSCwrQkFBVyxDQUFDLElBQUksQ0FBQyxFQUFDLElBQUksRUFBRSxLQUFLLENBQUMsVUFBVTtBQUN0QixnQ0FBUSxFQUFFLEdBQUcsRUFBQyxDQUFDLENBQUM7QUFDbEMsdUJBQUcsQ0FBQyxPQUFPLENBQUMsS0FBSyxDQUFDLFVBQVUsQ0FBQyxDQUFDO2lCQUNqQzthQUNKO0FBQ0QsbUJBQU8sR0FBRyxDQUFDO1NBQ2Q7O0FBRUQsb0JBQVksRUFBRSxzQkFBVSxJQUFJLEVBQUUsU0FBUyxFQUFFLENBQUMsRUFBRTs7QUFFeEMsZ0JBQU0sWUFBWSxHQUNkLElBQUksQ0FBQyxPQUFPLENBQUMsSUFBSSxDQUFDLFFBQVEsQ0FBQyxDQUMxQixnQkFBZ0IsQ0FBQyxTQUFTLENBQUMsRUFBRSxFQUFFLFNBQVMsQ0FBQyxLQUFLLENBQUMsQ0FBQzs7QUFFckQsZ0JBQU0sT0FBTyxHQUFHLFlBQVksQ0FBQyxTQUFTLENBQUMsSUFBSSxDQUFDLE9BQU8sQ0FBQyxLQUFLLENBQUMsSUFBSSxDQUFDLENBQUM7OztBQUdoRSxnQkFBTSxTQUFTLEdBQUcsYUFBYSxDQUFDLFNBQVMsRUFBRSxLQUFLLEVBQUUsT0FBTyxDQUFDLENBQUM7QUFDM0QsYUFBQyxDQUFDLElBQUksQ0FBQyxLQUFLLEVBQUUsU0FBUyxFQUFFLFNBQVMsQ0FBQyxDQUFDOzs7QUFHcEMsZ0JBQU0sV0FBVyxHQUFHLGFBQWEsQ0FBQyxTQUFTLEVBQUUsSUFBSSxFQUFFLFlBQVksQ0FBQyxDQUFDO0FBQ2pFLGFBQUMsQ0FBQyxJQUFJLENBQUMsT0FBTyxDQUFDLElBQUksRUFBRSxXQUFXLEVBQUUsU0FBUyxDQUFDLENBQUM7OztBQUc3QyxnQkFBSSxJQUFJLENBQUMsU0FBUyxLQUFLLElBQUksRUFDdkIsQ0FBQyxDQUFDLElBQUksQ0FBQyxTQUFTLEVBQUUsU0FBUyxFQUFFLFNBQVMsQ0FBQyxDQUFDO1NBQy9DOztBQUVELHNCQUFjLEVBQUUsd0JBQVUsSUFBSSxFQUFFLFNBQVMsRUFBRSxDQUFDLEVBQUU7QUFDMUMsZ0JBQU0sR0FBRyxHQUFHLENBQUMsQ0FBQyxJQUFJLENBQUMsUUFBUSxFQUFFLFNBQVMsRUFBRSxTQUFTLENBQUMsQ0FBQztBQUNuRCx1QkFBVyxDQUFDLElBQUksQ0FBQyxFQUFDLElBQUksRUFBRSxHQUFHO0FBQ1Qsa0JBQUUsRUFBRSxTQUFTLENBQUMsR0FBRyxFQUFDLENBQUMsQ0FBQztBQUN0QyxlQUFHLENBQUMsU0FBUyxDQUFDLFNBQVMsQ0FBQyxHQUFHLENBQUMsQ0FBQztTQUNoQzs7QUFFRCxzQkFBYyxFQUFFLHdCQUFVLElBQUksRUFBRSxTQUFTLEVBQUUsQ0FBQyxFQUFFO0FBQzFDLGdCQUFNLE9BQU8sR0FBRyxJQUFJLEtBQUssQ0FBQyxJQUFJLEVBQUEsQ0FBQztBQUMvQixnQkFBTSxRQUFRLEdBQUcsRUFBRSxDQUFDOzs7QUFHcEIsaUJBQUssSUFBSSxDQUFDLEdBQUcsQ0FBQyxFQUFFLENBQUMsR0FBRyxJQUFJLENBQUMsU0FBUyxDQUFDLE1BQU0sRUFBRSxDQUFDLEVBQUUsRUFBRTtBQUM1Qyx3QkFBUSxDQUFDLElBQUksQ0FDVCxDQUFDLENBQUMsSUFBSSxDQUFDLFNBQVMsQ0FBQyxDQUFDLENBQUMsRUFBRSxTQUFTLEVBQUUsU0FBUyxDQUFDLENBQUMsQ0FBQzthQUNuRDs7QUFFRCxnQkFBTSxRQUFRLEdBQUcsU0FBUyxDQUFDLEtBQUssQ0FBQyxTQUFTLENBQUMsSUFBSSxDQUFDLFFBQVEsQ0FBQyxDQUFDLENBQUM7O0FBRTNELGdCQUFJLElBQUksQ0FBQyxNQUFNLENBQUMsSUFBSSxLQUFLLGtCQUFrQixFQUFFOzs7Ozs7Ozs7Ozs7QUFZekMsb0JBQU0sVUFBVSxHQUFHLFVBQVUsQ0FBQyxJQUFJLENBQUMsTUFBTSxFQUFFLFNBQVMsRUFBRSxDQUFDLENBQUMsQ0FBQztBQUN6RCwwQkFBVSxDQUFDLENBQUMsQ0FBQyxDQUFDLFNBQVMsQ0FDbkIsSUFBSSxJQUFJLENBQUMsUUFBUSxDQUNiLFVBQVUsQ0FBQyxDQUFDLENBQUMsRUFDYixRQUFRLEVBQ1IsT0FBTyxFQUNQLFNBQVMsQ0FBQyxHQUFHLEVBQ2IsUUFBUSxDQUFDLENBQUMsQ0FBQzthQUN0QixNQUFNOztBQUVILG9CQUFNLFVBQVUsR0FBRyxDQUFDLENBQUMsSUFBSSxDQUFDLE1BQU0sRUFBRSxTQUFTLEVBQUUsU0FBUyxDQUFDLENBQUM7OztBQUd4RCwyQkFBVyxDQUFDLElBQUksQ0FBQztBQUNiLDBCQUFNLEVBQUUsVUFBVTtBQUNsQix3QkFBSSxFQUFFLElBQUksQ0FBQyxZQUFZO0FBQ3ZCLDBCQUFNLEVBQUUsUUFBUTtBQUNoQix1QkFBRyxFQUFFLE9BQU87QUFDWix1QkFBRyxFQUFFLFNBQVMsQ0FBQyxHQUFHO0FBQ2xCLHlCQUFLLEVBQUUsUUFBUTtpQkFDbEIsQ0FBQyxDQUFDO0FBQ0gsMEJBQVUsQ0FBQyxTQUFTLENBQ2hCLElBQUksSUFBSSxDQUFDLFFBQVEsQ0FDYixJQUFJLEtBQUssQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDLFlBQVksQ0FBQyxFQUNqQyxRQUFRLEVBQ1IsT0FBTyxFQUNQLFNBQVMsQ0FBQyxHQUFHLEVBQ2IsUUFBUSxDQUFDLENBQUMsQ0FBQzthQUN0QjtBQUNELG1CQUFPLE9BQU8sQ0FBQztTQUNsQjs7QUFFRCx3QkFBZ0IsRUFBRSwwQkFBVSxJQUFJLEVBQUUsU0FBUyxFQUFFLENBQUMsRUFBRTtBQUM1QyxnQkFBTSxVQUFVLEdBQUcsVUFBVSxDQUFDLElBQUksRUFBRSxTQUFTLEVBQUUsQ0FBQyxDQUFDLENBQUM7QUFDbEQsbUJBQU8sVUFBVSxDQUFDLENBQUMsQ0FBQyxDQUFDO1NBQ3hCOztBQUVELHVCQUFlLEVBQUUseUJBQVUsSUFBSSxFQUFFLFNBQVMsRUFBRSxDQUFDLEVBQUU7QUFDM0MsZ0JBQUksQ0FBQyxJQUFJLENBQUMsUUFBUSxFQUFFLE9BQU87QUFDM0IsZ0JBQU0sR0FBRyxHQUFHLENBQUMsQ0FBQyxJQUFJLENBQUMsUUFBUSxFQUFFLFNBQVMsRUFBRSxTQUFTLENBQUMsQ0FBQztBQUNuRCx1QkFBVyxDQUFDLElBQUksQ0FBQyxFQUFDLElBQUksRUFBRSxHQUFHO0FBQ1Qsa0JBQUUsRUFBRSxTQUFTLENBQUMsR0FBRyxFQUFDLENBQUMsQ0FBQztBQUN0QyxlQUFHLENBQUMsU0FBUyxDQUFDLFNBQVMsQ0FBQyxHQUFHLENBQUMsQ0FBQztTQUNoQztLQUNKLENBQUMsQ0FBQzs7QUFFSCx1QkFBbUIsQ0FBQyxHQUFHLEVBQUUsVUFBVSxFQUFFLG1CQUFtQixDQUFDLENBQUM7OztBQUcxRCxXQUFPLElBQUksQ0FBQztDQUNmOztBQUVELFNBQVMsbUJBQW1CLENBQUMsSUFBSSxFQUFFLEtBQUssRUFBRSxPQUFPLEVBQUU7QUFDL0MsYUFBUyxDQUFDLENBQUMsSUFBSSxFQUFFLEVBQUUsRUFBRSxRQUFRLEVBQUU7QUFDM0IsZUFBTyxPQUFPLENBQUMsUUFBUSxJQUFJLElBQUksQ0FBQyxJQUFJLENBQUMsQ0FBQyxJQUFJLEVBQUUsRUFBRSxFQUFFLENBQUMsQ0FBQyxDQUFDO0tBQ3REO0FBQ0QsV0FBTyxDQUFDLENBQUMsSUFBSSxFQUFFLEtBQUssQ0FBQyxDQUFDO0NBQ3pCOztBQUVELE9BQU8sQ0FBQyxXQUFXLEdBQUcsV0FBVyxDQUFDO0FBQ2xDLE9BQU8sQ0FBQyxjQUFjLEdBQUcsY0FBYyxDQUFDO0FBQ3hDLE9BQU8sQ0FBQyxnQkFBZ0IsR0FBRyxnQkFBZ0IsQ0FBQzs7O0FDemtCNUMsWUFBWSxDQUFDOztBQUViLElBQU0sS0FBSyxHQUFHLE9BQU8sQ0FBQyxrQkFBa0IsQ0FBQyxDQUFDO0FBQzFDLElBQU0sTUFBTSxHQUFHLE9BQU8sQ0FBQyxtQkFBbUIsQ0FBQyxDQUFDO0FBQzVDLElBQU0sSUFBSSxHQUFHLE9BQU8sQ0FBQyxRQUFRLENBQUMsQ0FBQzs7QUFFL0IsU0FBUyxJQUFJLEdBQUcsRUFBRTtBQUNsQixJQUFJLENBQUMsU0FBUyxHQUFHLE1BQU0sQ0FBQyxNQUFNLENBQUMsSUFBSSxDQUFDLENBQUM7QUFDckMsSUFBSSxDQUFDLFNBQVMsQ0FBQyxNQUFNLEdBQUcsVUFBVSxLQUFLLEVBQUU7QUFDckMsV0FBTyxJQUFJLEtBQUssS0FBSyxDQUFDO0NBQ3pCLENBQUM7O0FBRUYsU0FBUyxRQUFRLENBQUMsSUFBSSxFQUFFLEVBQUUsRUFBRTtBQUN4QixRQUFJLENBQUMsSUFBSSxHQUFHLElBQUksQ0FBQztBQUNqQixRQUFJLENBQUMsRUFBRSxHQUFHLEVBQUUsQ0FBQztDQUNoQjtBQUNELFFBQVEsQ0FBQyxTQUFTLEdBQUcsTUFBTSxDQUFDLE1BQU0sQ0FBQyxJQUFJLENBQUMsU0FBUyxDQUFDLENBQUM7QUFDbkQsUUFBUSxDQUFDLFNBQVMsQ0FBQyxPQUFPLEdBQUcsVUFBVSxHQUFHLEVBQUU7QUFDeEMsUUFBSSxFQUFFLEdBQUcsWUFBYSxLQUFLLENBQUMsT0FBTyxDQUFDLEVBQUcsT0FBTzs7QUFFOUMsUUFBTSxPQUFPLEdBQUcsR0FBRyxDQUFDLE9BQU8sQ0FBQyxJQUFJLENBQUMsSUFBSSxFQUFFLElBQUksQ0FBQyxDQUFDO0FBQzdDLFFBQUksT0FBTyxFQUFFOztBQUVULGVBQU8sQ0FBQyxTQUFTLENBQUMsSUFBSSxDQUFDLEVBQUUsQ0FBQyxDQUFDO0tBQzlCLE1BQU0sSUFBSSxHQUFHLENBQUMsT0FBTyxDQUFDLFdBQVcsRUFBRSxJQUFJLENBQUMsRUFBRTs7QUFFdkMsV0FBRyxDQUFDLE9BQU8sQ0FBQyxXQUFXLENBQUMsQ0FDckIsU0FBUyxDQUFDLElBQUksUUFBUSxDQUFDLElBQUksQ0FBQyxJQUFJLEVBQUUsSUFBSSxDQUFDLEVBQUUsQ0FBQyxDQUFDLENBQUM7S0FDbEQ7Q0FDSixDQUFDO0FBQ0YsUUFBUSxDQUFDLFNBQVMsQ0FBQyxNQUFNLEdBQUcsVUFBVSxLQUFLLEVBQUU7QUFDekMsUUFBSSxFQUFFLEtBQUssWUFBWSxRQUFRLENBQUEsRUFBRyxPQUFPLEtBQUssQ0FBQztBQUMvQyxXQUFPLElBQUksQ0FBQyxJQUFJLEtBQUssS0FBSyxDQUFDLElBQUksSUFDeEIsSUFBSSxDQUFDLEVBQUUsQ0FBQyxNQUFNLENBQUMsS0FBSyxDQUFDLEVBQUUsQ0FBQyxDQUFDO0NBQ25DLENBQUM7O0FBRUYsU0FBUyxTQUFTLENBQUMsSUFBSSxFQUFFLElBQUksRUFBRTtBQUMzQixRQUFJLENBQUMsSUFBSSxHQUFHLElBQUksQ0FBQztBQUNqQixRQUFJLENBQUMsSUFBSSxHQUFHLElBQUksQ0FBQztDQUNwQjtBQUNELFNBQVMsQ0FBQyxTQUFTLEdBQUcsTUFBTSxDQUFDLE1BQU0sQ0FBQyxJQUFJLENBQUMsU0FBUyxDQUFDLENBQUM7QUFDcEQsU0FBUyxDQUFDLFNBQVMsQ0FBQyxPQUFPLEdBQUcsVUFBVSxHQUFHLEVBQUU7QUFDekMsUUFBSSxFQUFFLEdBQUcsWUFBYSxLQUFLLENBQUMsT0FBTyxDQUFDLEVBQUcsT0FBTztBQUM5QyxRQUFNLE9BQU8sR0FBRyxHQUFHLENBQUMsT0FBTyxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsQ0FBQztBQUN2QyxRQUFJLENBQUMsSUFBSSxDQUFDLFNBQVMsQ0FBQyxPQUFPLENBQUMsQ0FBQztDQUNoQyxDQUFDOztBQUVGLFNBQVMsT0FBTyxDQUFDLEtBQUssRUFBRSxNQUFNLEVBQUU7QUFDNUIsUUFBSSxDQUFDLEtBQUssR0FBRyxLQUFLLENBQUM7QUFDbkIsUUFBSSxDQUFDLE1BQU0sR0FBRyxNQUFNLENBQUM7Q0FDeEI7QUFDRCxPQUFPLENBQUMsU0FBUyxHQUFHLE1BQU0sQ0FBQyxNQUFNLENBQUMsSUFBSSxDQUFDLFNBQVMsQ0FBQyxDQUFDO0FBQ2xELE9BQU8sQ0FBQyxTQUFTLENBQUMsT0FBTyxHQUFHLFVBQVUsSUFBSSxFQUFFO0FBQ3hDLFFBQUksQ0FBQyxJQUFJLEtBQUssS0FBSyxDQUFDLFVBQVUsSUFDdEIsSUFBSSxLQUFLLEtBQUssQ0FBQyxXQUFXLENBQUEsS0FDN0IsSUFBSSxDQUFDLEtBQUssQ0FBQyxPQUFPLENBQUMsS0FBSyxDQUFDLFVBQVUsQ0FBQyxJQUNqQyxJQUFJLENBQUMsS0FBSyxDQUFDLE9BQU8sQ0FBQyxLQUFLLENBQUMsV0FBVyxDQUFDLENBQUEsRUFBRztBQUM1QyxZQUFJLENBQUMsTUFBTSxDQUFDLE9BQU8sQ0FBQyxLQUFLLENBQUMsVUFBVSxDQUFDLENBQUM7S0FDekM7QUFDRCxRQUFJLElBQUksS0FBSyxLQUFLLENBQUMsVUFBVSxJQUN6QixDQUFDLElBQUksQ0FBQyxLQUFLLENBQUMsT0FBTyxFQUFFLEVBQUU7QUFDdEIsWUFBSSxDQUFDLE1BQU0sQ0FBQyxPQUFPLENBQUMsS0FBSyxDQUFDLFVBQVUsQ0FBQyxDQUFDO0tBQzFDO0NBQ0osQ0FBQzs7QUFFRixTQUFTLFFBQVEsQ0FBQyxJQUFJLEVBQUUsSUFBSSxFQUFFLEdBQUcsRUFBRSxHQUFHLEVBQUUsS0FBSyxFQUFFO0FBQzNDLFFBQUksQ0FBQyxJQUFJLEdBQUcsSUFBSSxDQUFDO0FBQ2pCLFFBQUksQ0FBQyxJQUFJLEdBQUcsSUFBSSxDQUFDO0FBQ2pCLFFBQUksQ0FBQyxHQUFHLEdBQUcsR0FBRyxDQUFDO0FBQ2YsUUFBSSxDQUFDLEdBQUcsR0FBRyxHQUFHLENBQUM7QUFDZixRQUFJLENBQUMsS0FBSyxHQUFHLEtBQUssQ0FBQztDQUN0QjtBQUNELFFBQVEsQ0FBQyxTQUFTLEdBQUcsTUFBTSxDQUFDLE1BQU0sQ0FBQyxJQUFJLENBQUMsU0FBUyxDQUFDLENBQUM7QUFDbkQsUUFBUSxDQUFDLFNBQVMsQ0FBQyxPQUFPLEdBQUcsVUFBVSxDQUFDLEVBQUU7QUFDdEMsUUFBSSxFQUFFLENBQUMsWUFBYSxLQUFLLENBQUMsTUFBTSxDQUFDLEVBQUcsT0FBTztBQUMzQyxRQUFNLE1BQU0sR0FBRyxDQUFDLENBQUMsU0FBUyxDQUFDLElBQUksQ0FBQyxLQUFLLENBQUMsQ0FBQztBQUN2QyxRQUFNLEtBQUssR0FBRyxDQUFDLENBQUMsVUFBVSxDQUFDLElBQUksQ0FBQyxRQUFRLENBQUMsQ0FBQyxnQkFBZ0IsQ0FBQyxDQUFDLENBQUMsRUFBRSxFQUFFLElBQUksQ0FBQyxLQUFLLENBQUMsQ0FBQztBQUM3RSxRQUFNLFNBQVMsR0FDVCxJQUFJLE1BQU0sQ0FBQyxNQUFNLENBQUMsTUFBTSxDQUFDLENBQUMsQ0FBQyxFQUFFLE1BQU0sQ0FBQyxDQUFDLENBQUMsRUFBRSxNQUFNLENBQUMsQ0FBQyxDQUFDLEVBQy9CLElBQUksQ0FBQyxLQUFLLEVBQUUsS0FBSyxDQUFDLENBQUM7O0FBRTNDLFFBQUksQ0FBQyxJQUFJLENBQUMsU0FBUyxDQUFDLE1BQU0sQ0FBQyxDQUFDLENBQUMsQ0FBQyxDQUFDOztBQUUvQixRQUFNLE1BQU0sR0FBRyxJQUFJLENBQUMsR0FBRyxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsTUFBTSxFQUFFLENBQUMsQ0FBQyxVQUFVLENBQUMsTUFBTSxDQUFDLENBQUM7QUFDL0QsU0FBSyxJQUFJLENBQUMsR0FBRyxDQUFDLEVBQUUsQ0FBQyxHQUFHLE1BQU0sRUFBRSxDQUFDLEVBQUUsRUFBRTtBQUM3QixZQUFJLENBQUMsSUFBSSxDQUFDLENBQUMsQ0FBQyxDQUFDLFNBQVMsQ0FBQyxLQUFLLENBQUMsU0FBUyxDQUFDLENBQUMsQ0FBQyxVQUFVLENBQUMsQ0FBQyxDQUFDLENBQUMsQ0FBQyxDQUFDO0tBQzVEOzs7QUFHRCxRQUFJLENBQUMsQ0FBQyxVQUFVLENBQUMsSUFBSSxDQUFDLFFBQVEsQ0FBQyxDQUFDLGtCQUFrQixFQUFFO0FBQ2hELFlBQU0sTUFBTSxHQUFHLENBQUMsQ0FBQyxrQkFBa0IsQ0FBQyxJQUFJLENBQUMsS0FBSyxDQUFDLENBQUM7QUFDaEQsYUFBSyxDQUFDLFNBQVMsQ0FBQyxXQUFXLENBQUMsQ0FBQyxPQUFPLENBQUMsTUFBTSxDQUFDLENBQUM7QUFDN0MsYUFBSyxJQUFJLENBQUMsR0FBRyxDQUFDLEVBQUUsQ0FBQyxHQUFHLElBQUksQ0FBQyxJQUFJLENBQUMsTUFBTSxFQUFFLENBQUMsRUFBRSxFQUFFO0FBQ3ZDLGdCQUFJLENBQUMsSUFBSSxDQUFDLENBQUMsQ0FBQyxDQUFDLFNBQVMsQ0FBQyxNQUFNLENBQUMsT0FBTyxDQUFDLENBQUMsR0FBRyxFQUFFLENBQUMsQ0FBQyxDQUFDO0FBQy9DLGdCQUFJLENBQUMsSUFBSSxDQUFDLENBQUMsQ0FBQyxDQUFDLFNBQVMsQ0FBQyxNQUFNLENBQUMsT0FBTyxDQUFDLElBQUksQ0FBQyxDQUFDLENBQUM7U0FDaEQ7QUFDRCxjQUFNLENBQUMsT0FBTyxDQUFDLFFBQVEsQ0FBQyxDQUFDLE9BQU8sQ0FBQyxDQUFDLENBQUMsQ0FBQztBQUNwQyxjQUFNLENBQUMsT0FBTyxDQUFDLFFBQVEsQ0FBQyxDQUFDLE9BQU8sQ0FBQyxLQUFLLENBQUMsVUFBVSxDQUFDLENBQUM7S0FDdEQ7OztBQUdELFFBQUksQ0FBQyxjQUFjLENBQUMsQ0FBQyxDQUFDLFVBQVUsQ0FBQyxJQUFJLEVBQUUsU0FBUyxDQUFDLENBQUM7OztBQUdsRCxVQUFNLENBQUMsQ0FBQyxDQUFDLENBQUMsU0FBUyxDQUFDLElBQUksQ0FBQyxHQUFHLENBQUMsQ0FBQzs7QUFFOUIsVUFBTSxDQUFDLENBQUMsQ0FBQyxDQUFDLFNBQVMsQ0FBQyxJQUFJLENBQUMsR0FBRyxDQUFDLENBQUM7Q0FDakMsQ0FBQzs7QUFFRixTQUFTLE1BQU0sQ0FBQyxJQUFJLEVBQUUsR0FBRyxFQUFFLEdBQUcsRUFBRSxLQUFLLEVBQUU7QUFDbkMsUUFBSSxDQUFDLElBQUksR0FBRyxJQUFJLENBQUM7QUFDakIsUUFBSSxDQUFDLEdBQUcsR0FBRyxHQUFHLENBQUM7QUFDZixRQUFJLENBQUMsR0FBRyxHQUFHLEdBQUcsQ0FBQztBQUNmLFFBQUksQ0FBQyxLQUFLLEdBQUcsS0FBSyxDQUFDO0NBQ3RCO0FBQ0QsTUFBTSxDQUFDLFNBQVMsR0FBRyxNQUFNLENBQUMsTUFBTSxDQUFDLElBQUksQ0FBQyxTQUFTLENBQUMsQ0FBQztBQUNqRCxNQUFNLENBQUMsU0FBUyxDQUFDLE9BQU8sR0FBRyxVQUFVLENBQUMsRUFBRTtBQUNwQyxRQUFJLEVBQUUsQ0FBQyxZQUFhLEtBQUssQ0FBQyxNQUFNLENBQUMsRUFBRyxPQUFPO0FBQzNDLFFBQU0sTUFBTSxHQUFHLENBQUMsQ0FBQyxTQUFTLENBQUMsSUFBSSxDQUFDLEtBQUssQ0FBQyxDQUFDO0FBQ3ZDLFFBQU0sS0FBSyxHQUFHLENBQUMsQ0FBQyxVQUFVLENBQUMsSUFBSSxDQUFDLFFBQVEsQ0FBQyxDQUFDLGdCQUFnQixDQUFDLENBQUMsQ0FBQyxFQUFFLEVBQUUsSUFBSSxDQUFDLEtBQUssQ0FBQyxDQUFDO0FBQzdFLFFBQU0sU0FBUyxHQUNULElBQUksTUFBTSxDQUFDLE1BQU0sQ0FBQyxNQUFNLENBQUMsQ0FBQyxDQUFDLEVBQUUsSUFBSSxTQUFTLENBQUMsTUFBTSxDQUFDLENBQUMsQ0FBQyxDQUFDLEVBQUUsTUFBTSxDQUFDLENBQUMsQ0FBQyxFQUM5QyxJQUFJLENBQUMsS0FBSyxFQUFFLEtBQUssQ0FBQyxDQUFDOztBQUUzQyxRQUFNLE1BQU0sR0FBRyxDQUFDLENBQUMsV0FBVyxFQUFFLENBQUM7QUFDL0IsVUFBTSxDQUFDLENBQUMsQ0FBQyxDQUFDLE9BQU8sQ0FBQyxNQUFNLENBQUMsQ0FBQzs7QUFFMUIsUUFBTSxNQUFNLEdBQUcsSUFBSSxDQUFDLEdBQUcsQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDLE1BQU0sRUFBRSxDQUFDLENBQUMsVUFBVSxDQUFDLE1BQU0sQ0FBQyxDQUFDO0FBQy9ELFNBQUssSUFBSSxDQUFDLEdBQUcsQ0FBQyxFQUFFLENBQUMsR0FBRyxNQUFNLEVBQUUsQ0FBQyxFQUFFLEVBQUU7QUFDN0IsWUFBSSxDQUFDLElBQUksQ0FBQyxDQUFDLENBQUMsQ0FBQyxTQUFTLENBQUMsS0FBSyxDQUFDLFNBQVMsQ0FBQyxDQUFDLENBQUMsVUFBVSxDQUFDLENBQUMsQ0FBQyxDQUFDLENBQUMsQ0FBQztLQUM1RDs7O0FBR0QsUUFBSSxDQUFDLENBQUMsVUFBVSxDQUFDLElBQUksQ0FBQyxRQUFRLENBQUMsQ0FBQyxrQkFBa0IsRUFBRTtBQUNoRCxZQUFNLE1BQU0sR0FBRyxDQUFDLENBQUMsa0JBQWtCLENBQUMsSUFBSSxDQUFDLEtBQUssQ0FBQyxDQUFDO0FBQ2hELGFBQUssQ0FBQyxTQUFTLENBQUMsV0FBVyxDQUFDLENBQUMsT0FBTyxDQUFDLE1BQU0sQ0FBQyxDQUFDO0FBQzdDLGFBQUssSUFBSSxDQUFDLEdBQUcsQ0FBQyxFQUFFLENBQUMsR0FBRyxJQUFJLENBQUMsSUFBSSxDQUFDLE1BQU0sRUFBRSxDQUFDLEVBQUUsRUFBRTtBQUN2QyxnQkFBSSxDQUFDLElBQUksQ0FBQyxDQUFDLENBQUMsQ0FBQyxTQUFTLENBQUMsTUFBTSxDQUFDLE9BQU8sQ0FBQyxDQUFDLEdBQUcsRUFBRSxDQUFDLENBQUMsQ0FBQztBQUMvQyxnQkFBSSxDQUFDLElBQUksQ0FBQyxDQUFDLENBQUMsQ0FBQyxTQUFTLENBQUMsTUFBTSxDQUFDLE9BQU8sQ0FBQyxJQUFJLENBQUMsQ0FBQyxDQUFDO1NBQ2hEO0FBQ0QsY0FBTSxDQUFDLE9BQU8sQ0FBQyxRQUFRLENBQUMsQ0FBQyxPQUFPLENBQUMsQ0FBQyxDQUFDLENBQUM7QUFDcEMsY0FBTSxDQUFDLE9BQU8sQ0FBQyxRQUFRLENBQUMsQ0FBQyxPQUFPLENBQUMsS0FBSyxDQUFDLFVBQVUsQ0FBQyxDQUFDO0tBQ3REOzs7QUFHRCxRQUFJLENBQUMsY0FBYyxDQUFDLENBQUMsQ0FBQyxVQUFVLENBQUMsSUFBSSxFQUFFLFNBQVMsQ0FBQyxDQUFDOzs7QUFHbEQsVUFBTSxDQUFDLENBQUMsQ0FBQyxDQUFDLFNBQVMsQ0FBQyxJQUFJLENBQUMsR0FBRyxDQUFDLENBQUM7O0FBRTlCLFFBQUksQ0FBQyxHQUFHLENBQUMsT0FBTyxDQUFDLE1BQU0sQ0FBQyxDQUFDOztBQUV6QixVQUFNLENBQUMsQ0FBQyxDQUFDLENBQUMsU0FBUyxDQUFDLElBQUksQ0FBQyxHQUFHLENBQUMsQ0FBQztDQUNqQyxDQUFDOzs7QUFHRixTQUFTLFNBQVMsQ0FBQyxJQUFJLEVBQUU7QUFDckIsUUFBSSxDQUFDLElBQUksR0FBRyxJQUFJLENBQUM7Q0FDcEI7QUFDRCxTQUFTLENBQUMsU0FBUyxHQUFHLE1BQU0sQ0FBQyxNQUFNLENBQUMsSUFBSSxDQUFDLFNBQVMsQ0FBQyxDQUFDO0FBQ3BELFNBQVMsQ0FBQyxTQUFTLENBQUMsT0FBTyxHQUFHLFVBQVUsSUFBSSxFQUFFO0FBQzFDLFFBQUksRUFBRSxJQUFJLFlBQVksS0FBSyxDQUFDLE9BQU8sQ0FBQSxFQUFHLE9BQU87QUFDN0MsUUFBSSxDQUFDLElBQUksQ0FBQyxPQUFPLENBQUMsSUFBSSxDQUFDLENBQUM7Q0FDM0IsQ0FBQzs7QUFFRixPQUFPLENBQUMsUUFBUSxHQUFHLFFBQVEsQ0FBQztBQUM1QixPQUFPLENBQUMsU0FBUyxHQUFHLFNBQVMsQ0FBQztBQUM5QixPQUFPLENBQUMsT0FBTyxHQUFHLE9BQU8sQ0FBQztBQUMxQixPQUFPLENBQUMsUUFBUSxHQUFHLFFBQVEsQ0FBQztBQUM1QixPQUFPLENBQUMsTUFBTSxHQUFHLE1BQU0sQ0FBQzs7Ozs7Ozs7Ozs7O0FDbEt4QixJQUFJLHdCQUF3QixHQUFHOztBQUUzQixhQUFTLEVBQUUsQ0FBQzs7QUFFWixhQUFTLEVBQUUsRUFBRTtDQUNoQixDQUFDOztBQUVGLFNBQVMsZUFBZSxDQUFDLE1BQU0sRUFBRTtBQUM3QixRQUFJLE1BQU0sRUFBRSxJQUFJLENBQUMsTUFBTSxHQUFHLE1BQU0sQ0FBQyxLQUM1QixJQUFJLENBQUMsTUFBTSxHQUFHLEVBQUUsQ0FBQztDQUN6Qjs7QUFFRCxlQUFlLENBQUMsU0FBUyxDQUFDLE1BQU0sR0FBRyxVQUFVLEtBQUssRUFBRTtBQUNoRCxRQUFJLElBQUksQ0FBQyxNQUFNLENBQUMsTUFBTSxJQUFJLEtBQUssQ0FBQyxNQUFNLENBQUMsTUFBTSxFQUFFLE9BQU8sS0FBSyxDQUFDO0FBQzVELFNBQUssSUFBSSxDQUFDLEdBQUcsQ0FBQyxFQUFFLENBQUMsR0FBRyxJQUFJLENBQUMsTUFBTSxDQUFDLE1BQU0sRUFBRSxDQUFDLEVBQUUsRUFBRTtBQUN6QyxZQUFJLElBQUksQ0FBQyxNQUFNLENBQUMsQ0FBQyxDQUFDLEtBQUssS0FBSyxDQUFDLE1BQU0sQ0FBQyxDQUFDLENBQUMsRUFBRSxPQUFPLEtBQUssQ0FBQztLQUN4RDtBQUNELFdBQU8sSUFBSSxDQUFDO0NBQ2YsQ0FBQzs7QUFFRixlQUFlLENBQUMsU0FBUyxDQUFDLFNBQVMsR0FBRyxVQUFVLFFBQVEsRUFBRTs7O0FBR3RELFFBQUksUUFBUSxHQUFHLElBQUksQ0FBQyxNQUFNLENBQUMsTUFBTSxDQUFDLFFBQVEsQ0FBQyxDQUFDO0FBQzVDLFFBQUksUUFBUSxDQUFDLE1BQU0sR0FBRyx3QkFBd0IsQ0FBQyxTQUFTLEVBQUU7QUFDdEQsZ0JBQVEsQ0FBQyxLQUFLLEVBQUUsQ0FBQztLQUNwQjtBQUNELFdBQU8sSUFBSSxlQUFlLENBQUMsUUFBUSxDQUFDLENBQUM7Q0FDeEMsQ0FBQzs7QUFFRixlQUFlLENBQUMsU0FBUyxDQUFDLFFBQVEsR0FBRyxZQUFZO0FBQzdDLFdBQU8sSUFBSSxDQUFDLE1BQU0sQ0FBQyxRQUFRLEVBQUUsQ0FBQztDQUNqQyxDQUFDOztBQUVGLE9BQU8sQ0FBQyx3QkFBd0IsR0FBRyx3QkFBd0IsQ0FBQztBQUM1RCxPQUFPLENBQUMsZUFBZSxHQUFHLGVBQWUsQ0FBQzs7Ozs7Ozs7Ozs7O0FDbkMxQyxTQUFTLE1BQU0sQ0FBQyxJQUFJLEVBQUUsR0FBRyxFQUFFLEdBQUcsRUFBRSxLQUFLLEVBQUUsRUFBRSxFQUFFO0FBQ3ZDLFFBQUksQ0FBQyxJQUFJLEdBQUcsSUFBSSxDQUFDO0FBQ2pCLFFBQUksQ0FBQyxHQUFHLEdBQUcsR0FBRyxDQUFDO0FBQ2YsUUFBSSxDQUFDLEdBQUcsR0FBRyxHQUFHLENBQUM7QUFDZixRQUFJLENBQUMsS0FBSyxHQUFHLEtBQUssQ0FBQztBQUNuQixRQUFJLENBQUMsRUFBRSxHQUFHLEVBQUUsQ0FBQztDQUNoQjs7QUFFRCxNQUFNLENBQUMsU0FBUyxDQUFDLE1BQU0sR0FBRyxVQUFVLEtBQUssRUFBRTtBQUN2QyxXQUFPLElBQUksQ0FBQyxJQUFJLEtBQUssS0FBSyxDQUFDLElBQUksSUFDM0IsSUFBSSxDQUFDLEdBQUcsS0FBSyxLQUFLLENBQUMsR0FBRyxJQUN0QixJQUFJLENBQUMsR0FBRyxLQUFLLEtBQUssQ0FBQyxHQUFHLElBQ3RCLElBQUksQ0FBQyxLQUFLLENBQUMsTUFBTSxDQUFDLEtBQUssQ0FBQyxLQUFLLENBQUMsSUFDOUIsSUFBSSxDQUFDLEVBQUUsS0FBSyxLQUFLLENBQUMsRUFBRSxDQUFDO0NBQzVCLENBQUM7O0FBRUYsT0FBTyxDQUFDLE1BQU0sR0FBRyxNQUFNLENBQUM7OztBQ3ZCeEIsWUFBWSxDQUFDOzs7QUFHYixJQUFJLEtBQUssR0FBRyxDQUFDLENBQUM7Ozs7Ozs7QUFPZCxTQUFTLElBQUksQ0FBQyxJQUFJLEVBQUU7OztBQUdoQixRQUFJLElBQUksRUFBRSxJQUFJLENBQUMsS0FBSyxHQUFHLElBQUksR0FBRyxDQUFDLENBQUMsSUFBSSxDQUFDLENBQUMsQ0FBQyxLQUNsQyxJQUFJLENBQUMsS0FBSyxHQUFHLElBQUksR0FBRyxFQUFFLENBQUM7OztBQUc1QixRQUFJLENBQUMsUUFBUSxHQUFHLElBQUksR0FBRyxFQUFFLENBQUM7O0FBRTFCLFFBQUksQ0FBQyxHQUFHLEdBQUcsS0FBSyxFQUFFLENBQUM7Q0FDdEI7Ozs7QUFJRCxJQUFJLENBQUMsU0FBUyxDQUFDLE9BQU8sR0FBRyxZQUFZO0FBQ2pDLFdBQU8sSUFBSSxDQUFDLEtBQUssQ0FBQyxJQUFJLEtBQUssQ0FBQyxDQUFDO0NBQ2hDLENBQUM7Ozs7O0FBS0YsSUFBSSxDQUFDLFNBQVMsQ0FBQyxRQUFRLEdBQUcsWUFBWTtBQUNsQyxXQUFPLElBQUksQ0FBQyxLQUFLLENBQUM7Q0FDckIsQ0FBQzs7Ozs7QUFLRixJQUFJLENBQUMsU0FBUyxDQUFDLE9BQU8sR0FBRyxVQUFVLElBQUksRUFBRTtBQUNyQyxXQUFPLElBQUksQ0FBQyxLQUFLLENBQUMsR0FBRyxDQUFDLElBQUksQ0FBQyxDQUFDO0NBQy9CLENBQUM7Ozs7OztBQU1GLElBQUksQ0FBQyxTQUFTLENBQUMsT0FBTyxHQUFHLFVBQVUsSUFBSSxFQUFFO0FBQ3JDLFFBQUksSUFBSSxDQUFDLEtBQUssQ0FBQyxHQUFHLENBQUMsSUFBSSxDQUFDLEVBQUUsT0FBTzs7QUFFakMsUUFBSSxDQUFDLEtBQUssQ0FBQyxHQUFHLENBQUMsSUFBSSxDQUFDLENBQUM7O0FBRXJCLFFBQUksQ0FBQyxRQUFRLENBQUMsT0FBTyxDQUFDLFVBQVUsR0FBRyxFQUFFO0FBQ2pDLFdBQUcsQ0FBQyxPQUFPLENBQUMsSUFBSSxDQUFDLENBQUM7S0FDckIsQ0FBQyxDQUFDO0NBQ04sQ0FBQzs7OztBQUlGLElBQUksQ0FBQyxTQUFTLENBQUMsU0FBUyxHQUFHLFVBQVUsTUFBTSxFQUFFO0FBQ3pDLFFBQUksQ0FBQyxJQUFJLENBQUMsVUFBVSxDQUFDLE1BQU0sQ0FBQyxFQUFFLE9BQU87OztBQUdyQyxRQUFJLENBQUMsS0FBSyxDQUFDLE9BQU8sQ0FBQyxVQUFVLElBQUksRUFBRTtBQUMvQixjQUFNLENBQUMsT0FBTyxDQUFDLElBQUksQ0FBQyxDQUFDO0tBQ3hCLENBQUMsQ0FBQztDQUNOLENBQUM7O0FBRUYsSUFBSSxDQUFDLFNBQVMsQ0FBQyxVQUFVLEdBQUcsVUFBVSxHQUFHLEVBQUU7QUFDdkMseUJBQW1CLElBQUksQ0FBQyxRQUFRLGtIQUFFOzs7Ozs7Ozs7Ozs7WUFBekIsTUFBTTs7QUFDWCxZQUFJLEdBQUcsQ0FBQyxNQUFNLENBQUMsTUFBTSxDQUFDLEVBQUUsT0FBTyxLQUFLLENBQUM7S0FDeEM7QUFDRCxRQUFJLENBQUMsUUFBUSxDQUFDLEdBQUcsQ0FBQyxHQUFHLENBQUMsQ0FBQztBQUN2QixXQUFPLElBQUksQ0FBQztDQUNmLENBQUM7O0FBRUYsSUFBSSxDQUFDLFNBQVMsQ0FBQyxNQUFNLEdBQUcsVUFBVSxLQUFLLEVBQUU7O0FBRXJDLFdBQU8sSUFBSSxLQUFLLEtBQUssQ0FBQztDQUN6QixDQUFDOzs7Ozs7O0FBT0YsSUFBSSxDQUFDLFNBQVMsQ0FBQyxPQUFPLEdBQUcsVUFBVSxJQUFJLEVBQUU7QUFDckMsUUFBSSxJQUFJLEtBQUssR0FBRyxFQUFFOztBQUVkLGVBQU8sUUFBUSxDQUFDO0tBQ25CO0FBQ0QsUUFBSSxJQUFJLENBQUMsS0FBSyxDQUFDLEdBQUcsQ0FBQyxJQUFJLENBQUMsRUFBRTtBQUN0QixlQUFPLElBQUksQ0FBQyxLQUFLLENBQUMsR0FBRyxDQUFDLElBQUksQ0FBQyxDQUFDO0tBQy9CLE1BQU07QUFDSCxlQUFPLFFBQVEsQ0FBQztLQUNuQjtDQUNKLENBQUM7Ozs7Ozs7QUFPRixTQUFTLElBQUksR0FBRyxFQUFFO0FBQ2xCLElBQUksQ0FBQyxTQUFTLEdBQUcsTUFBTSxDQUFDLE1BQU0sQ0FBQyxJQUFJLENBQUMsQ0FBQzs7Ozs7OztBQU9yQyxTQUFTLE9BQU8sQ0FBQyxLQUFLLEVBQUUsSUFBSSxFQUFFO0FBQzFCLFFBQUksQ0FBQyxJQUFJLEdBQUcsSUFBSSxDQUFDO0FBQ2pCLFFBQUksQ0FBQyxLQUFLLEdBQUcsSUFBSSxHQUFHLEVBQUUsQ0FBQzs7O0FBR3ZCLFFBQUksQ0FBQyxPQUFPLENBQUMsV0FBVyxFQUFFLEtBQUssQ0FBQyxDQUFDO0NBQ3BDO0FBQ0QsT0FBTyxDQUFDLFNBQVMsR0FBRyxNQUFNLENBQUMsTUFBTSxDQUFDLElBQUksQ0FBQyxTQUFTLENBQUMsQ0FBQzs7Ozs7O0FBTWxELE9BQU8sQ0FBQyxTQUFTLENBQUMsT0FBTyxHQUFHLFVBQVUsSUFBSSxFQUFFLFFBQVEsRUFBRTtBQUNsRCxRQUFJLElBQUksS0FBSyxHQUFHLEVBQUU7O0FBRWQsZUFBTyxRQUFRLENBQUM7S0FDbkI7QUFDRCxRQUFJLElBQUksQ0FBQyxLQUFLLENBQUMsR0FBRyxDQUFDLElBQUksQ0FBQyxFQUFFO0FBQ3RCLGVBQU8sSUFBSSxDQUFDLEtBQUssQ0FBQyxHQUFHLENBQUMsSUFBSSxDQUFDLENBQUM7S0FDL0IsTUFBTSxJQUFJLFFBQVEsRUFBRTtBQUNqQixlQUFPLElBQUksQ0FBQztLQUNmLE1BQU07QUFDSCxZQUFJLFdBQVcsR0FBRyxJQUFJLElBQUksRUFBQSxDQUFDO0FBQzNCLFlBQUksQ0FBQyxLQUFLLENBQUMsR0FBRyxDQUFDLElBQUksRUFBRSxXQUFXLENBQUMsQ0FBQztBQUNsQyxlQUFPLFdBQVcsQ0FBQztLQUN0QjtDQUNKLENBQUM7Ozs7Ozs7QUFPRixPQUFPLENBQUMsU0FBUyxDQUFDLE9BQU8sR0FBRyxVQUFVLElBQUksRUFBRSxJQUFJLEVBQUU7QUFDOUMsUUFBSSxJQUFJLEtBQUssR0FBRyxFQUFFOztBQUVkLGVBQU87S0FDVjtBQUNELFFBQUksQ0FBQyxLQUFLLENBQUMsR0FBRyxDQUFDLElBQUksRUFBRSxJQUFJLENBQUMsQ0FBQztDQUM5QixDQUFDOzs7Ozs7QUFNRixPQUFPLENBQUMsU0FBUyxDQUFDLE9BQU8sR0FBRyxVQUFVLElBQUksRUFBRTtBQUN4QyxRQUFJLElBQUksS0FBSyxHQUFHLEVBQUUsT0FBTyxLQUFLLENBQUM7QUFDL0IsV0FBTyxJQUFJLENBQUMsS0FBSyxDQUFDLEdBQUcsQ0FBQyxJQUFJLENBQUMsQ0FBQztDQUMvQixDQUFDOzs7Ozs7QUFNRixPQUFPLENBQUMsU0FBUyxDQUFDLGFBQWEsR0FBRyxVQUFVLElBQUksRUFBRSxJQUFJLEVBQUU7QUFDcEQsUUFBSSxJQUFJLEtBQUssR0FBRyxFQUFFLE9BQU87QUFDekIsUUFBSSxDQUFDLElBQUksQ0FBQyxLQUFLLENBQUMsR0FBRyxDQUFDLElBQUksQ0FBQyxFQUFFO0FBQ3ZCLFlBQUksQ0FBQyxLQUFLLENBQUMsR0FBRyxDQUFDLElBQUksRUFBRSxJQUFJLElBQUksRUFBQSxDQUFDLENBQUM7S0FDbEM7QUFDRCxRQUFJLElBQUksQ0FBQyxLQUFLLENBQUMsR0FBRyxDQUFDLElBQUksQ0FBQyxDQUFDLE9BQU8sQ0FBQyxJQUFJLENBQUMsRUFBRSxPQUFPO0FBQy9DLFFBQUksQ0FBQyxLQUFLLENBQUMsR0FBRyxDQUFDLElBQUksQ0FBQyxDQUFDLE9BQU8sQ0FBQyxJQUFJLENBQUMsQ0FBQztDQUN0QyxDQUFDOzs7Ozs7QUFNRixPQUFPLENBQUMsU0FBUyxDQUFDLGNBQWMsR0FBRyxVQUFVLElBQUksRUFBRSxJQUFJLEVBQUU7QUFDckQsUUFBSSxJQUFJLEdBQUcsSUFBSSxDQUFDO0FBQ2hCLFFBQUksQ0FBQyxRQUFRLEVBQUUsQ0FBQyxPQUFPLENBQUMsVUFBVSxJQUFJLEVBQUU7QUFDcEMsWUFBSSxDQUFDLGFBQWEsQ0FBQyxJQUFJLEVBQUUsSUFBSSxDQUFDLENBQUM7S0FDbEMsQ0FBQyxDQUFDO0NBQ04sQ0FBQzs7O0FBR0YsU0FBUyxvQkFBb0IsQ0FBQyxNQUFNLEVBQUU7QUFDbEMsUUFBSSxJQUFJLEdBQUcsSUFBSSxPQUFPLENBQUMsUUFBUSxFQUFFLGdCQUFnQixDQUFDLENBQUM7QUFDbkQsUUFBSSxDQUFDLEtBQUssR0FBRyxNQUFNLENBQUMsTUFBTSxDQUFDOzs7QUFHM0IsUUFBSSxDQUFDLE9BQU8sR0FBRyxVQUFVLElBQUksRUFBRTtBQUMzQixlQUFPLE9BQU8sQ0FBQyxTQUFTLENBQUMsT0FBTyxDQUFDLElBQUksQ0FBQyxJQUFJLEVBQUUsSUFBSSxDQUFDLENBQUM7S0FDckQsQ0FBQztBQUNGLFdBQU8sSUFBSSxDQUFDO0NBQ2Y7Ozs7Ozs7QUFPRCxTQUFTLFFBQVEsQ0FBQyxJQUFJLEVBQUU7QUFDcEIsUUFBSSxDQUFDLElBQUksR0FBRyxJQUFJLENBQUM7Q0FDcEI7QUFDRCxRQUFRLENBQUMsU0FBUyxHQUFHLE1BQU0sQ0FBQyxNQUFNLENBQUMsSUFBSSxDQUFDLFNBQVMsQ0FBQyxDQUFDOzs7Ozs7Ozs7Ozs7O0FBYW5ELFNBQVMsTUFBTSxDQUFDLFFBQVEsRUFBRSxJQUFJLEVBQUUsUUFBUSxFQUFFLEVBQUUsRUFBRSxVQUFVLEVBQUUsUUFBUSxFQUFFO0FBQ2hFLFdBQU8sQ0FBQyxJQUFJLENBQUMsSUFBSSxFQUFFLFFBQVEsRUFBRSxJQUFJLENBQUMsQ0FBQztBQUNuQyxRQUFJLENBQUMsVUFBVSxHQUFHLFFBQVEsQ0FBQztBQUMzQixRQUFJLENBQUMsRUFBRSxHQUFHLEVBQUUsQ0FBQztBQUNiLFFBQUksQ0FBQyxVQUFVLEdBQUcsVUFBVSxDQUFDO0FBQzdCLFFBQUksQ0FBQyxRQUFRLEdBQUcsUUFBUSxDQUFDOztBQUV6QixRQUFJLENBQUMsTUFBTSxHQUFHLElBQUksR0FBRyxFQUFBLENBQUM7Q0FDekI7QUFDRCxNQUFNLENBQUMsU0FBUyxHQUFHLE1BQU0sQ0FBQyxNQUFNLENBQUMsT0FBTyxDQUFDLFNBQVMsQ0FBQyxDQUFDOzs7Ozs7O0FBT3BELE1BQU0sQ0FBQyxTQUFTLENBQUMsU0FBUyxHQUFHLFVBQVUsS0FBSyxFQUFFO0FBQzFDLFFBQUksSUFBSSxDQUFDLE1BQU0sQ0FBQyxHQUFHLENBQUMsS0FBSyxDQUFDLEVBQUU7QUFDeEIsZUFBTyxJQUFJLENBQUMsTUFBTSxDQUFDLEdBQUcsQ0FBQyxLQUFLLENBQUMsQ0FBQztLQUNqQyxNQUFNO0FBQ0gsWUFBSSxNQUFNLEdBQUcsQ0FBQyxJQUFJLElBQUksRUFBQSxFQUFFLElBQUksSUFBSSxFQUFBLEVBQUUsSUFBSSxJQUFJLEVBQUEsQ0FBQyxDQUFDO0FBQzVDLFlBQUksQ0FBQyxNQUFNLENBQUMsR0FBRyxDQUFDLEtBQUssRUFBRSxNQUFNLENBQUMsQ0FBQztBQUMvQixlQUFPLE1BQU0sQ0FBQztLQUNqQjtDQUNKLENBQUM7O0FBRUYsTUFBTSxDQUFDLFNBQVMsQ0FBQyxrQkFBa0IsR0FBRyxVQUFVLEtBQUssRUFBRTtBQUNuRCxRQUFJLENBQUMsU0FBUyxHQUFHLElBQUksQ0FBQyxTQUFTLElBQUksSUFBSSxHQUFHLEVBQUEsQ0FBQztBQUMzQyxRQUFJLElBQUksQ0FBQyxTQUFTLENBQUMsR0FBRyxDQUFDLEtBQUssQ0FBQyxFQUFFO0FBQzNCLGVBQU8sSUFBSSxDQUFDLFNBQVMsQ0FBQyxHQUFHLENBQUMsS0FBSyxDQUFDLENBQUM7S0FDcEMsTUFBTTtBQUNILFlBQUksTUFBTSxHQUFHLElBQUksT0FBTyxDQUFDLElBQUksSUFBSSxDQUFDLElBQUksQ0FBQyxRQUFRLENBQUMsRUFBRSxvQkFBb0IsQ0FBQyxDQUFDO0FBQ3hFLFlBQUksQ0FBQyxTQUFTLENBQUMsR0FBRyxDQUFDLEtBQUssRUFBRSxNQUFNLENBQUMsQ0FBQztBQUNsQyxlQUFPLE1BQU0sQ0FBQztLQUNqQjtDQUNKLENBQUM7Ozs7Ozs7QUFPRixNQUFNLENBQUMsU0FBUyxDQUFDLFdBQVcsR0FBRyxZQUFZOztBQUV2QyxRQUFJLElBQUksQ0FBQyxXQUFXLEVBQUUsT0FBTyxJQUFJLENBQUMsV0FBVyxDQUFDOztBQUU5QyxRQUFJLENBQUMsV0FBVyxHQUFHLElBQUksT0FBTyxDQUFDLElBQUksQ0FBQyxPQUFPLENBQUMsV0FBVyxDQUFDLENBQUMsQ0FBQztBQUMxRCxXQUFPLElBQUksQ0FBQyxXQUFXLENBQUM7Q0FDM0IsQ0FBQzs7Ozs7O0FBTUYsU0FBUyxPQUFPLENBQUMsU0FBUyxFQUFFO0FBQ3hCLFdBQU8sQ0FBQyxJQUFJLENBQUMsSUFBSSxFQUFFLFNBQVMsRUFBRSxPQUFPLENBQUMsQ0FBQztDQUMxQztBQUNELE9BQU8sQ0FBQyxTQUFTLEdBQUcsTUFBTSxDQUFDLE1BQU0sQ0FBQyxPQUFPLENBQUMsU0FBUyxDQUFDLENBQUM7OztBQUdyRCxJQUFJLFVBQVUsR0FBRyxJQUFJLFFBQVEsQ0FBQyxRQUFRLENBQUMsQ0FBQztBQUN4QyxJQUFJLFVBQVUsR0FBRyxJQUFJLFFBQVEsQ0FBQyxRQUFRLENBQUMsQ0FBQztBQUN4QyxJQUFJLFdBQVcsR0FBRyxJQUFJLFFBQVEsQ0FBQyxTQUFTLENBQUMsQ0FBQzs7O0FBRzFDLElBQUksUUFBUSxHQUFHLElBQUksSUFBSSxFQUFFLENBQUM7O0FBRTFCLFFBQVEsQ0FBQyxLQUFLLEdBQUcsSUFBSSxDQUFDOztBQUV0QixRQUFRLENBQUMsT0FBTyxHQUFHLFlBQVksRUFBRSxDQUFDOzs7QUFJbEMsT0FBTyxDQUFDLElBQUksR0FBRyxJQUFJLENBQUM7QUFDcEIsT0FBTyxDQUFDLE9BQU8sR0FBRyxPQUFPLENBQUM7QUFDMUIsT0FBTyxDQUFDLE1BQU0sR0FBRyxNQUFNLENBQUM7QUFDeEIsT0FBTyxDQUFDLE9BQU8sR0FBRyxPQUFPLENBQUM7QUFDMUIsT0FBTyxDQUFDLFVBQVUsR0FBRyxVQUFVLENBQUM7QUFDaEMsT0FBTyxDQUFDLFVBQVUsR0FBRyxVQUFVLENBQUM7QUFDaEMsT0FBTyxDQUFDLFdBQVcsR0FBRyxXQUFXLENBQUM7QUFDbEMsT0FBTyxDQUFDLG9CQUFvQixHQUFHLG9CQUFvQixDQUFDOztBQUVwRCxPQUFPLENBQUMsSUFBSSxHQUFHLElBQUksQ0FBQztBQUNwQixPQUFPLENBQUMsUUFBUSxHQUFHLFFBQVEsQ0FBQzs7Ozs7O0FDNVM1QixJQUFJLEtBQUssR0FBRyxPQUFPLENBQUMsa0JBQWtCLENBQUMsQ0FBQztBQUN4QyxJQUFJLEdBQUcsR0FBRyxPQUFPLENBQUMsT0FBTyxDQUFDLENBQUM7QUFDM0IsSUFBSSxLQUFLLEdBQUcsT0FBTyxDQUFDLGlCQUFpQixDQUFDLENBQUM7QUFDdkMsSUFBSSxPQUFPLEdBQUcsT0FBTyxDQUFDLG1CQUFtQixDQUFDLENBQUM7QUFDM0MsSUFBSSxNQUFNLEdBQUcsT0FBTyxDQUFDLGtCQUFrQixDQUFDLENBQUM7QUFDekMsSUFBSSxJQUFJLEdBQUcsT0FBTyxDQUFDLE1BQU0sQ0FBQyxDQUFDO0FBQzNCLElBQUksUUFBUSxHQUFHLE9BQU8sQ0FBQyxZQUFZLENBQUMsQ0FBQztBQUNyQyxJQUFJLElBQUksR0FBRyxPQUFPLENBQUMsbUJBQW1CLENBQUMsQ0FBQztBQUN4QyxJQUFJLE9BQU8sR0FBRyxPQUFPLENBQUMsV0FBVyxDQUFDLENBQUM7O0FBRW5DLFNBQVMsT0FBTyxDQUFDLEtBQUssRUFBRSxNQUFNLEVBQUU7Ozs7O0FBSzVCLFFBQUksR0FBRyxHQUFHLEtBQUssQ0FBQyxLQUFLLENBQUMsS0FBSyxDQUFDLENBQUM7O0FBRTdCLFFBQUksc0JBQXNCLEdBQUcsR0FBRyxDQUFDLFdBQVcsQ0FBQyxHQUFHLENBQUMsQ0FBQzs7Ozs7QUFLbEQsWUFBUSxDQUFDLGlCQUFpQixDQUFDLEdBQUcsQ0FBQyxDQUFDO0FBQ2hDLFFBQUksTUFBTSxHQUFHLEdBQUcsQ0FBQyxRQUFRLENBQUMsQ0FBQztBQUMzQixRQUFJLGNBQWMsR0FBRyxJQUFJLE9BQU8sQ0FBQyxlQUFlLEVBQUEsQ0FBQztBQUNqRCxRQUFJLE1BQU0sR0FBRyxNQUFNLENBQUMsZ0JBQWdCLENBQUMsSUFBSSxFQUFFLGNBQWMsQ0FBQyxDQUFDO0FBQzNELFFBQUksT0FBTyxHQUFHLEtBQUssQ0FBQyxvQkFBb0IsQ0FBQyxNQUFNLENBQUMsQ0FBQztBQUNqRCxRQUFJLFVBQVUsR0FBRyxJQUFJLE1BQU0sQ0FBQyxNQUFNLENBQzlCLE9BQU8sRUFDUCxLQUFLLENBQUMsUUFBUSxFQUNkLEtBQUssQ0FBQyxRQUFRLEVBQ2QsY0FBYyxFQUNkLE1BQU0sQ0FBQyxDQUFDOztBQUVaLFFBQUksUUFBUSxHQUFHLElBQUksS0FBSyxDQUFDLE9BQU8sQ0FBQyxJQUFJLEVBQUUsa0JBQWtCLENBQUMsQ0FBQztBQUMzRCxRQUFJLElBQUksR0FBRztBQUNQLG9CQUFZLEVBQUUsT0FBTzs7QUFFckIsY0FBTSxFQUFFO0FBQ0osa0JBQU0sRUFBRSxRQUFRO0FBQ2hCLG9CQUFRLEVBQUUsSUFBSSxLQUFLLENBQUMsT0FBTyxDQUFDLElBQUksS0FBSyxDQUFDLElBQUksQ0FBQyxRQUFRLENBQUMsRUFBRSxvQkFBb0IsQ0FBQztBQUMzRSxpQkFBSyxFQUFFLElBQUksS0FBSyxDQUFDLE9BQU8sQ0FBQyxJQUFJLEtBQUssQ0FBQyxJQUFJLENBQUMsUUFBUSxDQUFDLEVBQUUsaUJBQWlCLENBQUM7QUFDckUsa0JBQU0sRUFBRSxJQUFJLEtBQUssQ0FBQyxPQUFPLENBQUMsSUFBSSxLQUFLLENBQUMsSUFBSSxDQUFDLFFBQVEsQ0FBQyxFQUFFLGtCQUFrQixDQUFDO0FBQ3ZFLGtCQUFNLEVBQUUsSUFBSSxLQUFLLENBQUMsT0FBTyxDQUFDLElBQUksS0FBSyxDQUFDLElBQUksQ0FBQyxRQUFRLENBQUMsRUFBRSxrQkFBa0IsQ0FBQztBQUN2RSxrQkFBTSxFQUFFLElBQUksS0FBSyxDQUFDLE9BQU8sQ0FBQyxJQUFJLEtBQUssQ0FBQyxJQUFJLENBQUMsUUFBUSxDQUFDLEVBQUUsa0JBQWtCLENBQUM7QUFDdkUsbUJBQU8sRUFBRSxJQUFJLEtBQUssQ0FBQyxPQUFPLENBQUMsSUFBSSxLQUFLLENBQUMsSUFBSSxDQUFDLFFBQVEsQ0FBQyxFQUFFLG1CQUFtQixDQUFDO1NBQzVFOztLQUVKLENBQUM7QUFDRixRQUFJLENBQUMsY0FBYyxDQUFDLEdBQUcsRUFBRSxVQUFVLEVBQUUsSUFBSSxDQUFDLENBQUM7QUFDM0MsUUFBSSxXQUFXLEdBQUcsSUFBSSxDQUFDLFdBQVcsQ0FBQzs7Ozs7QUFLbkMsUUFBSSxNQUFNLEVBQUU7QUFDUixlQUFPLEVBQUMsT0FBTyxFQUFFLE9BQU8sRUFBRSxHQUFHLEVBQUUsR0FBRyxFQUFFLE1BQU0sRUFBRSxNQUFNLEVBQUUsTUFBTSxFQUFFLE1BQU0sRUFBQyxDQUFDO0tBQ3ZFLE1BQU07QUFDSCxlQUFPLE9BQU8sQ0FBQztLQUNsQjtDQUNKOztBQUVELE9BQU8sQ0FBQyxPQUFPLEdBQUcsT0FBTyxDQUFDO0FBQzFCLE9BQU8sQ0FBQyxnQkFBZ0IsR0FBRyxPQUFPLENBQUMsZ0JBQWdCLENBQUM7QUFDcEQsT0FBTyxDQUFDLGFBQWEsR0FBRyxPQUFPLENBQUMsYUFBYSxDQUFDOzs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7O0FDNUI5QyxZQUFZLENBQUM7O0FBRWIsSUFBSSxLQUFLLEdBQUcsT0FBTyxDQUFDLGlCQUFpQixDQUFDLENBQUM7QUFDdkMsSUFBSSxJQUFJLEdBQUcsT0FBTyxDQUFDLGlCQUFpQixDQUFDLENBQUM7QUFDdEMsSUFBSSxHQUFHLEdBQUcsT0FBTyxDQUFDLE9BQU8sQ0FBQyxDQUFDOztBQUUzQixTQUFTLFFBQVEsQ0FBQyxLQUFLLEVBQUUsVUFBVSxFQUFFLE9BQU8sRUFBRTtBQUMxQyxRQUFJLENBQUMsS0FBSyxHQUFHLEtBQUssQ0FBQztBQUNuQixRQUFJLENBQUMsVUFBVSxHQUFHLFVBQVUsQ0FBQztBQUM3QixRQUFJLENBQUMsV0FBVyxHQUFHLFVBQVUsQ0FBQyxRQUFRLENBQUMsQ0FBQztBQUN4QyxRQUFJLENBQUMsT0FBTyxHQUFHLE9BQU8sQ0FBQztBQUN2QixRQUFJLENBQUMsYUFBYSxHQUFHLEVBQUUsQ0FBQztBQUN4QixRQUFJLENBQUMsYUFBYSxHQUFHLEVBQUUsQ0FBQzs7QUFFeEIsUUFBSSxDQUFDLGFBQWEsR0FBRyxFQUFFLENBQUM7O0FBRXhCLFFBQUksQ0FBQyxTQUFTLEdBQUcsTUFBTSxDQUFDLE1BQU0sQ0FBQyxJQUFJLENBQUMsQ0FBQztBQUNyQyxRQUFJLENBQUMsY0FBYyxHQUFHLEVBQUUsQ0FBQztDQUM1Qjs7QUFFRCxRQUFRLENBQUMsU0FBUyxHQUFHLE1BQU0sQ0FBQyxNQUFNLENBQUMsSUFBSSxDQUFDLENBQUM7O0FBRXpDLFFBQVEsQ0FBQyxTQUFTLENBQUMsUUFBUSxHQUFHLFlBQVk7QUFDdEMsV0FBTyxJQUFJLENBQUMsS0FBSyxJQUFJLElBQUksQ0FBQztDQUM3QixDQUFDO0FBQ0YsUUFBUSxDQUFDLFNBQVMsQ0FBQyxVQUFVLEdBQUcsWUFBWTtBQUN4QyxXQUFPLElBQUksQ0FBQyxLQUFLLElBQUksSUFBSSxJQUFJLElBQUksQ0FBQyxhQUFhLElBQUksSUFBSSxDQUFDO0NBQzNELENBQUM7QUFDRixRQUFRLENBQUMsU0FBUyxDQUFDLFlBQVksR0FBRyxZQUFZO0FBQzFDLFdBQU8sSUFBSSxDQUFDLE9BQU8sQ0FBQztDQUN2QixDQUFDOztBQUVGLFFBQVEsQ0FBQyxTQUFTLENBQUMsZ0JBQWdCLEdBQUcsWUFBWTtBQUM5QyxXQUFPLElBQUksQ0FBQyxhQUFhLENBQUM7Q0FDN0IsQ0FBQztBQUNGLFFBQVEsQ0FBQyxTQUFTLENBQUMsZ0JBQWdCLEdBQUcsWUFBWTtBQUM5QyxXQUFPLElBQUksQ0FBQyxhQUFhLENBQUM7Q0FDN0IsQ0FBQztBQUNGLFFBQVEsQ0FBQyxTQUFTLENBQUMsV0FBVyxHQUFHLFVBQVUsT0FBTyxFQUFFO0FBQ2hELFdBQU8sSUFBSSxDQUFDLGFBQWEsSUFBSSxJQUFJLENBQUMsYUFBYSxDQUFDLE9BQU8sQ0FBQyxPQUFPLENBQUMsR0FBRyxDQUFDLENBQUMsQ0FBQztDQUN6RSxDQUFDO0FBQ0YsUUFBUSxDQUFDLFNBQVMsQ0FBQyxXQUFXLEdBQUcsVUFBVSxPQUFPLEVBQUU7QUFDaEQsV0FBTyxJQUFJLENBQUMsYUFBYSxDQUFDLE9BQU8sQ0FBQyxPQUFPLENBQUMsR0FBRyxDQUFDLENBQUMsQ0FBQztDQUNuRCxDQUFDO0FBQ0YsUUFBUSxDQUFDLFNBQVMsQ0FBQyxNQUFNLEdBQUcsVUFBVSxPQUFPLEVBQUU7QUFDM0MsV0FBTyxJQUFJLENBQUMsV0FBVyxDQUFDLE9BQU8sQ0FBQyxJQUFJLElBQUksQ0FBQyxXQUFXLENBQUMsT0FBTyxDQUFDLENBQUM7Q0FDakUsQ0FBQzs7QUFFRixRQUFRLENBQUMsU0FBUyxDQUFDLG1CQUFtQixHQUFHLFVBQVUsT0FBTyxFQUFFLFNBQVMsRUFBRTtBQUNuRSxRQUFJLFNBQVMsR0FBRyxJQUFJLENBQUM7Ozs7QUFJckIsV0FBTyxTQUFTLENBQUMsWUFBWSxFQUFFLEtBQ3ZCLFNBQVMsSUFBSSxDQUFDLFNBQVMsQ0FBQyxXQUFXLENBQUMsT0FBTyxDQUFDLENBQUEsRUFBRztBQUNuRCxpQkFBUyxHQUFHLFNBQVMsQ0FBQyxLQUFLLENBQUM7S0FDL0I7O0FBRUQsUUFBSSxDQUFDLFNBQVMsQ0FBQyxNQUFNLENBQUMsT0FBTyxDQUFDLEVBQUU7QUFDNUIsaUJBQVMsQ0FBQyxhQUFhLENBQUMsSUFBSSxDQUFDLE9BQU8sQ0FBQyxDQUFDO0tBQ3pDOztBQUVELFdBQU8sU0FBUyxDQUFDO0NBQ3BCLENBQUM7QUFDRixRQUFRLENBQUMsU0FBUyxDQUFDLFdBQVcsR0FBRyxVQUFVLE9BQU8sRUFBRTtBQUNoRCxRQUFJLENBQUMsYUFBYSxDQUFDLElBQUksQ0FBQyxPQUFPLENBQUMsQ0FBQztDQUNwQyxDQUFDO0FBQ0YsUUFBUSxDQUFDLFNBQVMsQ0FBQyxjQUFjLEdBQUcsVUFBVSxPQUFPLEVBQUU7QUFDbkQsUUFBSSxTQUFTLEdBQUcsSUFBSSxDQUFDO0FBQ3JCLFdBQU8sU0FBUyxJQUFJLFNBQVMsQ0FBQyxLQUFLLElBQUksQ0FBQyxTQUFTLENBQUMsTUFBTSxDQUFDLE9BQU8sQ0FBQyxFQUFFO0FBQy9ELGlCQUFTLEdBQUcsU0FBUyxDQUFDLEtBQUssQ0FBQztLQUMvQjs7QUFFRCxXQUFPLFNBQVMsQ0FBQztDQUNwQixDQUFDOztBQUVGLFFBQVEsQ0FBQyxTQUFTLENBQUMsV0FBVyxHQUFHLFVBQVUsVUFBVSxFQUFFO0FBQ25ELFFBQUksU0FBUyxHQUFHLElBQUksQ0FBQztBQUNyQixXQUFPLFNBQVMsRUFBRTtBQUNkLFlBQUksU0FBUyxLQUFLLFVBQVUsRUFBRTtBQUMxQixtQkFBTyxJQUFJLENBQUM7U0FDZjtBQUNELGlCQUFTLEdBQUcsU0FBUyxDQUFDLEtBQUssQ0FBQztLQUMvQjtBQUNELFdBQU8sS0FBSyxDQUFDO0NBQ2hCLENBQUM7O0FBRUYsUUFBUSxDQUFDLFNBQVMsQ0FBQyxVQUFVLEdBQUcsVUFBVSxPQUFPLEVBQUU7QUFDL0MsUUFBSSxJQUFJLENBQUMsYUFBYSxDQUFDLE9BQU8sQ0FBQyxPQUFPLENBQUMsS0FBSyxDQUFDLENBQUMsRUFBRTtBQUM1QyxZQUFJLENBQUMsYUFBYSxDQUFDLElBQUksQ0FBQyxPQUFPLENBQUMsQ0FBQztLQUNwQztDQUNKLENBQUM7QUFDRixRQUFRLENBQUMsU0FBUyxDQUFDLGVBQWUsR0FBRyxZQUFZO0FBQzdDLFdBQU8sSUFBSSxDQUFDLGFBQWEsQ0FBQztDQUM3QixDQUFDO0FBQ0YsUUFBUSxDQUFDLFNBQVMsQ0FBQyxTQUFTLEdBQUcsVUFBVSxPQUFPLEVBQUU7QUFDOUMsV0FBTyxJQUFJLENBQUMsYUFBYSxDQUFDLE9BQU8sQ0FBQyxPQUFPLENBQUMsR0FBRyxDQUFDLENBQUMsQ0FBQztDQUNuRCxDQUFDOzs7QUFHRixRQUFRLENBQUMsU0FBUyxDQUFDLFdBQVcsR0FBRyxVQUFVLEtBQUssRUFBRTtBQUM5QyxRQUFJLElBQUksQ0FBQyxTQUFTLENBQUMsS0FBSyxDQUFDLEVBQUU7QUFDdkIsZUFBTyxJQUFJLENBQUMsU0FBUyxDQUFDLEtBQUssQ0FBQyxDQUFDO0tBQ2hDOztBQUVELFFBQUksTUFBTSxHQUFHLElBQUksR0FBRyxFQUFFLENBQUM7QUFDdkIsUUFBSSxRQUFRLEdBQUcsSUFBSSxDQUFDLGdCQUFnQixFQUFFLENBQUMsTUFBTSxDQUFDLElBQUksQ0FBQyxnQkFBZ0IsRUFBRSxDQUFDLENBQUM7O0FBRXZFLFNBQUssSUFBSSxDQUFDLEdBQUcsQ0FBQyxFQUFFLENBQUMsR0FBRyxRQUFRLENBQUMsTUFBTSxFQUFFLENBQUMsRUFBRSxFQUFFO0FBQ3RDLGNBQU0sQ0FBQyxHQUFHLENBQUMsUUFBUSxDQUFDLENBQUMsQ0FBQyxFQUFFLElBQUksS0FBSyxDQUFDLElBQUksRUFBRSxDQUFDLENBQUM7S0FDN0M7O0FBRUQsUUFBSSxDQUFDLFNBQVMsQ0FBQyxLQUFLLENBQUMsR0FBRyxNQUFNLENBQUM7QUFDL0IsV0FBTyxNQUFNLENBQUM7Q0FDakIsQ0FBQzs7QUFFRixRQUFRLENBQUMsU0FBUyxDQUFDLGFBQWEsR0FBRyxVQUFVLEtBQUssRUFBRTtBQUNoRCxRQUFJLFFBQVEsR0FBRyxJQUFJLENBQUMsV0FBVyxDQUFDLEtBQUssQ0FBQyxDQUFDO0FBQ3ZDLFFBQUksTUFBTSxHQUFHLEVBQUUsQ0FBQztBQUNoQixRQUFJLENBQUMsZ0JBQWdCLEVBQUUsQ0FBQyxPQUFPLENBQUMsVUFBVSxJQUFJLEVBQUU7QUFDNUMsY0FBTSxDQUFDLElBQUksQ0FBQyxRQUFRLENBQUMsR0FBRyxDQUFDLFlBQVksQ0FBQyxJQUFJLENBQUMsQ0FBQyxDQUFDLENBQUM7S0FDakQsQ0FBQyxDQUFDO0FBQ0gsV0FBTyxNQUFNLENBQUM7Q0FDakIsQ0FBQzs7QUFFRixRQUFRLENBQUMsU0FBUyxDQUFDLGdCQUFnQixHQUFHLFVBQVUsS0FBSyxFQUFFO0FBQ25ELFFBQUksQ0FBQyxJQUFJLENBQUMsa0JBQWtCLEVBQUU7QUFDMUIsY0FBTSxJQUFJLEtBQUssQ0FBQyx1QkFBdUIsQ0FBQyxDQUFDO0tBQzVDO0FBQ0QsV0FBTyxJQUFJLENBQUMsV0FBVyxDQUFDLEtBQUssQ0FBQyxDQUFDLEdBQUcsQ0FBQyxZQUFZLENBQUMsV0FBVyxDQUFDLENBQUMsQ0FBQztDQUNqRSxDQUFDOzs7QUFHRixRQUFRLENBQUMsU0FBUyxDQUFDLGdCQUFnQixHQUFHLFVBQVUsS0FBSyxFQUFFLEtBQUssRUFBRTtBQUMxRCxRQUFJLE1BQU0sR0FBRyxJQUFJLENBQUMsV0FBVyxDQUFDLEtBQUssQ0FBQyxDQUFDO0FBQ3JDLFFBQUksS0FBSyxHQUFHLElBQUksQ0FBQzs7QUFFakIsUUFBSSxDQUFDLGNBQWMsQ0FBQyxPQUFPLENBQUMsVUFBVSxFQUFFLEVBQUU7QUFDdEMsWUFBSSxFQUFFLENBQUMsS0FBSyxLQUFLLEtBQUssSUFBSSxFQUFFLENBQUMsTUFBTSxLQUFLLE1BQU0sRUFBRSxLQUFLLEdBQUcsRUFBRSxDQUFDO0tBQzlELENBQUMsQ0FBQzs7QUFFSCxRQUFJLEtBQUssRUFBRTtBQUNQLGVBQU8sS0FBSyxDQUFDO0tBQ2hCLE1BQU07QUFDSCxZQUFJLGdCQUFnQixHQUFHLElBQUksS0FBSyxDQUFDLEtBQUssRUFBRSxNQUFNLEVBQUUsSUFBSSxDQUFDLENBQUM7QUFDdEQsWUFBSSxDQUFDLGNBQWMsQ0FBQyxJQUFJLENBQUMsZ0JBQWdCLENBQUMsQ0FBQztBQUMzQyxlQUFPLGdCQUFnQixDQUFDO0tBQzNCO0NBQ0osQ0FBQzs7QUFFRixJQUFJLHNCQUFzQixHQUFHLElBQUksQ0FBQyxJQUFJLENBQUM7QUFDcEMsWUFBUSxFQUFFLGtCQUFVLElBQUksRUFBRSxTQUFTLEVBQUUsQ0FBQyxFQUFFO0FBQ25DLFlBQUksVUFBVSxHQUFHLFNBQVMsQ0FBQztBQUMzQixZQUFJLElBQUksQ0FBQyxFQUFFLEVBQUU7QUFDVCxnQkFBSSxRQUFRLEdBQUcsSUFBSSxDQUFDLEVBQUUsQ0FBQyxJQUFJLENBQUM7QUFDNUIsc0JBQVUsR0FBRyxTQUFTLENBQUMsbUJBQW1CLENBQUMsUUFBUSxFQUFFLElBQUksQ0FBQyxDQUFDO1NBQzlEOztBQUVELFlBQUksU0FBUyxHQUFHLElBQUksUUFBUSxDQUFDLFVBQVUsRUFBRSxJQUFJLENBQUMsQ0FBQztBQUMvQyxZQUFJLENBQUMsSUFBSSxDQUFDLFFBQVEsQ0FBQyxHQUFHLFNBQVMsQ0FBQzs7QUFFaEMsYUFBSyxJQUFJLENBQUMsR0FBRyxDQUFDLEVBQUUsQ0FBQyxHQUFHLElBQUksQ0FBQyxNQUFNLENBQUMsTUFBTSxFQUFFLENBQUMsRUFBRSxFQUFFO0FBQ3pDLGdCQUFJLFNBQVMsR0FBRyxJQUFJLENBQUMsTUFBTSxDQUFDLENBQUMsQ0FBQyxDQUFDLElBQUksQ0FBQztBQUNwQyxxQkFBUyxDQUFDLFdBQVcsQ0FBQyxTQUFTLENBQUMsQ0FBQztTQUNwQztBQUNELFNBQUMsQ0FBQyxJQUFJLENBQUMsSUFBSSxFQUFFLFNBQVMsRUFBRSxTQUFTLENBQUMsQ0FBQztLQUN0QztBQUNELHVCQUFtQixFQUFFLDZCQUFVLElBQUksRUFBRSxTQUFTLEVBQUUsQ0FBQyxFQUFFO0FBQy9DLGFBQUssSUFBSSxDQUFDLEdBQUcsQ0FBQyxFQUFFLENBQUMsR0FBRyxJQUFJLENBQUMsWUFBWSxDQUFDLE1BQU0sRUFBRSxDQUFDLEVBQUUsRUFBRTtBQUMvQyxnQkFBSSxJQUFJLEdBQUcsSUFBSSxDQUFDLFlBQVksQ0FBQyxDQUFDLENBQUMsQ0FBQztBQUNoQyxnQkFBSSxJQUFJLEdBQUcsSUFBSSxDQUFDLEVBQUUsQ0FBQyxJQUFJLENBQUM7QUFDeEIscUJBQVMsQ0FBQyxtQkFBbUIsQ0FBQyxJQUFJLENBQUMsQ0FBQztTQUN2QztBQUNELFlBQUksSUFBSSxDQUFDLElBQUksRUFBRSxDQUFDLENBQUMsSUFBSSxDQUFDLElBQUksRUFBRSxTQUFTLEVBQUUsU0FBUyxDQUFDLENBQUM7S0FDckQ7QUFDRCxnQkFBWSxFQUFFLHNCQUFVLElBQUksRUFBRSxTQUFTLEVBQUUsQ0FBQyxFQUFFO0FBQ3hDLFNBQUMsQ0FBQyxJQUFJLENBQUMsS0FBSyxFQUFFLFNBQVMsRUFBRSxTQUFTLENBQUMsQ0FBQztBQUNwQyxZQUFJLElBQUksQ0FBQyxPQUFPLEVBQUU7QUFDZCxhQUFDLENBQUMsSUFBSSxDQUFDLE9BQU8sRUFBRSxTQUFTLEVBQUUsU0FBUyxDQUFDLENBQUM7U0FDekM7QUFDRCxZQUFJLElBQUksQ0FBQyxTQUFTLEVBQUU7QUFDaEIsYUFBQyxDQUFDLElBQUksQ0FBQyxTQUFTLEVBQUUsU0FBUyxFQUFFLFNBQVMsQ0FBQyxDQUFDO1NBQzNDO0tBQ0o7QUFDRCxlQUFXLEVBQUUscUJBQVUsSUFBSSxFQUFFLFNBQVMsRUFBRSxDQUFDLEVBQUU7QUFDdkMsWUFBSSxVQUFVLEdBQUcsSUFBSSxRQUFRLENBQUMsU0FBUyxFQUFFLElBQUksRUFBRSxJQUFJLENBQUMsQ0FBQztBQUNyRCxrQkFBVSxDQUFDLFdBQVcsQ0FBQyxJQUFJLENBQUMsS0FBSyxDQUFDLElBQUksQ0FBQyxDQUFDO0FBQ3hDLFlBQUksQ0FBQyxJQUFJLENBQUMsUUFBUSxDQUFDLEdBQUcsVUFBVSxDQUFDO0FBQ2pDLFNBQUMsQ0FBQyxJQUFJLENBQUMsSUFBSSxFQUFFLFVBQVUsRUFBRSxTQUFTLENBQUMsQ0FBQztLQUN2QztDQUNKLENBQUMsQ0FBQzs7O0FBR0gsSUFBSSxzQkFBc0IsR0FBRyxJQUFJLENBQUMsSUFBSSxDQUFDO0FBQ25DLGNBQVUsRUFBRSxvQkFBVSxJQUFJLEVBQUUsU0FBUyxFQUFFLENBQUMsRUFBRTtBQUN0QyxZQUFJLGVBQWU7WUFBRSxPQUFPLEdBQUcsSUFBSSxDQUFDLElBQUksQ0FBQztBQUN6QyxZQUFJLE9BQU8sS0FBSyxXQUFXLEVBQUU7QUFDekIsMkJBQWUsR0FBRyxTQUFTLENBQUMsY0FBYyxDQUFDLE9BQU8sQ0FBQyxDQUFDO0FBQ3BELGdCQUFJLGVBQWUsQ0FBQyxRQUFRLEVBQUUsRUFBRTtBQUM1QiwrQkFBZSxDQUFDLG1CQUFtQixDQUFDLE9BQU8sQ0FBQyxDQUFDO2FBQ2hEO0FBQ0QsMkJBQWUsQ0FBQyxVQUFVLENBQUMsT0FBTyxDQUFDLENBQUM7U0FDdkMsTUFBTTs7QUFFSCwyQkFBZSxHQUFHLFNBQVMsQ0FBQztBQUM1QixtQkFBTyxlQUFlLENBQUMsWUFBWSxFQUFFLElBQzdCLENBQUMsZUFBZSxDQUFDLFdBQVcsQ0FBQyxPQUFPLENBQUMsRUFBRTtBQUMzQywrQkFBZSxHQUFHLGVBQWUsQ0FBQyxLQUFLLENBQUM7YUFDM0M7QUFDRCxnQkFBSSxlQUFlLENBQUMsTUFBTSxDQUFDLE9BQU8sQ0FBQyxFQUFFOztBQUVqQywrQkFBZSxDQUFDLFVBQVUsQ0FBQyxPQUFPLENBQUMsQ0FBQzthQUN2QyxNQUFNOzs7QUFHSCwrQkFBZSxDQUFDLG1CQUFtQixDQUFDLE9BQU8sQ0FBQyxDQUFDOztBQUU3QywrQkFBZSxDQUFDLFVBQVUsQ0FBQyxPQUFPLENBQUMsQ0FBQztBQUNwQyxvQkFBSSxlQUFlLENBQUMsVUFBVSxFQUFFLEVBQUU7QUFDOUIsbUNBQWUsQ0FBQyxrQkFBa0IsR0FBRyxJQUFJLENBQUM7aUJBQzdDO2FBQ0o7U0FDSjtLQUNKOztBQUVELG1CQUFlLEVBQUUseUJBQVUsSUFBSSxFQUFFLFNBQVMsRUFBRSxDQUFDLEVBQUU7QUFDM0MsWUFBSSxhQUFhLEdBQUcsU0FBUyxDQUFDO0FBQzlCLGVBQU8sYUFBYSxDQUFDLFlBQVksRUFBRSxFQUFFO0FBQ2pDLHlCQUFhLEdBQUcsYUFBYSxDQUFDLEtBQUssQ0FBQztTQUN2QztBQUNELFlBQUksQ0FBQyxhQUFhLENBQUMsUUFBUSxFQUFFLElBQUksSUFBSSxDQUFDLFFBQVEsS0FBSyxJQUFJLEVBQUU7QUFDckQseUJBQWEsQ0FBQyxxQkFBcUIsR0FBRyxJQUFJLENBQUM7U0FDOUM7QUFDRCxZQUFJLElBQUksQ0FBQyxRQUFRLEVBQUU7QUFDZixhQUFDLENBQUMsSUFBSSxDQUFDLFFBQVEsRUFBRSxTQUFTLEVBQUUsU0FBUyxDQUFDLENBQUM7U0FDMUM7S0FDSjs7QUFFRCxhQUFTLEVBQUUsbUJBQVUsSUFBSSxFQUFFLFNBQVMsRUFBRSxDQUFDLEVBQUU7QUFDckMsU0FBQyxDQUFDLElBQUksRUFBRSxJQUFJLENBQUMsUUFBUSxDQUFDLElBQUksU0FBUyxDQUFDLENBQUM7S0FDeEM7Q0FDSixDQUFDLENBQUM7O0FBR0gsU0FBUyxpQkFBaUIsQ0FBQyxHQUFHLEVBQUUsTUFBTSxFQUFFO0FBQ3BDLFFBQUksQ0FBQyxNQUFNLEVBQUU7O0FBRVQsY0FBTSxHQUFHLElBQUksUUFBUSxDQUFDLElBQUksRUFBRSxHQUFHLENBQUMsQ0FBQztLQUNwQztBQUNELE9BQUcsQ0FBQyxRQUFRLENBQUMsR0FBRyxNQUFNLENBQUM7QUFDdkIsUUFBSSxDQUFDLFNBQVMsQ0FBQyxHQUFHLEVBQUUsTUFBTSxFQUFFLElBQUksRUFBRSxzQkFBc0IsQ0FBQyxDQUFDO0FBQzFELFFBQUksQ0FBQyxTQUFTLENBQUMsR0FBRyxFQUFFLE1BQU0sRUFBRSxJQUFJLEVBQUUsc0JBQXNCLENBQUMsQ0FBQztBQUMxRCxXQUFPLEdBQUcsQ0FBQztDQUNkOzs7QUFHRCxTQUFTLEtBQUssQ0FBQyxLQUFLLEVBQUUsTUFBTSxFQUFFLEVBQUUsRUFBRTtBQUM5QixRQUFJLENBQUMsS0FBSyxHQUFHLEtBQUssQ0FBQztBQUNuQixRQUFJLENBQUMsTUFBTSxHQUFHLE1BQU0sQ0FBQztBQUNyQixRQUFJLENBQUMsRUFBRSxHQUFHLEVBQUUsQ0FBQztDQUNoQjtBQUNELEtBQUssQ0FBQyxTQUFTLEdBQUcsTUFBTSxDQUFDLE1BQU0sQ0FBQyxJQUFJLENBQUMsQ0FBQzs7QUFFdEMsS0FBSyxDQUFDLFNBQVMsQ0FBQyxTQUFTLEdBQUcsVUFBVSxPQUFPLEVBQUU7QUFDM0MsUUFBSSxJQUFJLEdBQUcsSUFBSSxDQUFDO0FBQ2hCLFdBQU8sSUFBSSxJQUFJLElBQUksRUFBRTtBQUNqQixZQUFJLElBQUksQ0FBQyxNQUFNLENBQUMsR0FBRyxDQUFDLE9BQU8sQ0FBQyxFQUFFO0FBQzFCLG1CQUFPLElBQUksQ0FBQyxNQUFNLENBQUMsR0FBRyxDQUFDLE9BQU8sQ0FBQyxDQUFDO1NBQ25DO0FBQ0QsWUFBSSxHQUFHLElBQUksQ0FBQyxLQUFLLENBQUM7S0FDckI7QUFDRCxVQUFNLElBQUksS0FBSyxDQUFDLGdDQUFnQyxDQUFDLENBQUM7Q0FDckQsQ0FBQzs7QUFFRixLQUFLLENBQUMsU0FBUyxDQUFDLHdCQUF3QixHQUFHLFlBQVk7QUFDbkQsUUFBSSxJQUFJLEdBQUcsSUFBSSxDQUFDO0FBQ2hCLFdBQU8sSUFBSSxDQUFDLEVBQUUsQ0FBQyxZQUFZLEVBQUUsRUFBRTtBQUMzQixZQUFJLEdBQUcsSUFBSSxDQUFDLEtBQUssQ0FBQztLQUNyQjtBQUNELFdBQU8sSUFBSSxDQUFDO0NBQ2YsQ0FBQzs7QUFHRixPQUFPLENBQUMsUUFBUSxHQUFHLFFBQVEsQ0FBQztBQUM1QixPQUFPLENBQUMsaUJBQWlCLEdBQUcsaUJBQWlCLENBQUM7QUFDOUMsT0FBTyxDQUFDLEtBQUssR0FBRyxLQUFLLENBQUM7Ozs7O0FDbFV0QixJQUFJLElBQUksR0FBRyxPQUFPLENBQUMsaUJBQWlCLENBQUMsQ0FBQztBQUN0QyxJQUFJLEVBQUUsR0FBRyxPQUFPLENBQUMsSUFBSSxDQUFDLENBQUM7QUFDdkIsSUFBSSxLQUFLLEdBQUcsT0FBTyxDQUFDLFNBQVMsQ0FBQyxDQUFDOzs7QUFJL0IsSUFBSSxTQUFTLEdBQUUsSUFBSSxDQUFDLElBQUksQ0FBQztBQUNyQixZQUFRLEVBQUUsa0JBQVUsSUFBSSxFQUFFLEVBQUUsRUFBRSxDQUFDLEVBQUU7QUFDN0IsWUFBTSxPQUFPLEdBQUcsSUFBSSxDQUFDLElBQUksQ0FBQyxRQUFRLENBQUMsQ0FBQztBQUNwQyxZQUFJLElBQUksQ0FBQyxFQUFFLEVBQUUsQ0FBQyxDQUFDLElBQUksQ0FBQyxFQUFFLEVBQUUsT0FBTyxDQUFDLENBQUM7QUFDakMsYUFBSyxJQUFJLENBQUMsR0FBRyxDQUFDLEVBQUUsQ0FBQyxHQUFHLElBQUksQ0FBQyxNQUFNLENBQUMsTUFBTSxFQUFFLENBQUMsRUFBRTtBQUN2QyxhQUFDLENBQUMsSUFBSSxDQUFDLE1BQU0sQ0FBQyxDQUFDLENBQUMsRUFBRSxPQUFPLENBQUMsQ0FBQztTQUFBLENBQzlCLENBQUMsSUFBSSxDQUFDLElBQUksRUFBRSxPQUFPLENBQUMsQ0FBQztLQUN6QjtBQUNELGdCQUFZLEVBQUUsc0JBQVUsSUFBSSxFQUFFLEVBQUUsRUFBRSxDQUFDLEVBQUU7QUFDakMsU0FBQyxDQUFDLElBQUksQ0FBQyxLQUFLLEVBQUUsRUFBRSxDQUFDLENBQUM7QUFDbEIsWUFBSSxJQUFJLENBQUMsT0FBTyxFQUFFO0FBQ2QsZ0JBQU0sT0FBTyxHQUFHLElBQUksQ0FBQyxPQUFPLENBQUMsSUFBSSxDQUFDLFFBQVEsQ0FBQyxDQUFDO0FBQzVDLGFBQUMsQ0FBQyxJQUFJLENBQUMsT0FBTyxDQUFDLEtBQUssRUFBRSxPQUFPLENBQUMsQ0FBQztBQUMvQixhQUFDLENBQUMsSUFBSSxDQUFDLE9BQU8sQ0FBQyxJQUFJLEVBQUUsT0FBTyxDQUFDLENBQUM7U0FDakM7QUFDRCxZQUFJLElBQUksQ0FBQyxTQUFTLEVBQUU7QUFDaEIsYUFBQyxDQUFDLElBQUksQ0FBQyxTQUFTLEVBQUUsRUFBRSxDQUFDLENBQUM7U0FDekI7S0FDSjtBQUNELHVCQUFtQixFQUFFLDZCQUFVLElBQUksRUFBRSxFQUFFLEVBQUUsQ0FBQyxFQUFFO0FBQ3hDLGFBQUssSUFBSSxDQUFDLEdBQUcsQ0FBQyxFQUFFLENBQUMsR0FBRyxJQUFJLENBQUMsWUFBWSxDQUFDLE1BQU0sRUFBRSxFQUFFLENBQUMsRUFBRTtBQUMvQyxnQkFBSSxJQUFJLEdBQUcsSUFBSSxDQUFDLFlBQVksQ0FBQyxDQUFDLENBQUMsQ0FBQztBQUNoQyxhQUFDLENBQUMsSUFBSSxDQUFDLEVBQUUsRUFBRSxFQUFFLENBQUMsQ0FBQztBQUNmLGdCQUFJLElBQUksQ0FBQyxJQUFJLEVBQUUsQ0FBQyxDQUFDLElBQUksQ0FBQyxJQUFJLEVBQUUsRUFBRSxFQUFFLFlBQVksQ0FBQyxDQUFDO1NBQ2pEO0tBQ0o7Q0FDSixDQUFDLENBQUM7Ozs7Ozs7Ozs7QUFXSCxTQUFTLFVBQVUsQ0FBQyxNQUFNLEVBQUUsT0FBTyxFQUFFLFFBQVEsRUFBRTtBQUMzQyxRQUFNLFNBQVMsR0FBRyxFQUFFLENBQUM7OzBCQUVaLFFBQVE7QUFDYixZQUFJLENBQUMsTUFBTSxDQUFDLGNBQWMsQ0FBQyxRQUFRLENBQUMsRUFBRTtBQUNsQyw4QkFBUztTQUNaO0FBQ0QsaUJBQVMsQ0FBQyxRQUFRLENBQUMsR0FBRyxVQUFDLElBQUksRUFBRSxFQUFFLEVBQUUsQ0FBQyxFQUFLO0FBQ25DLGdCQUFJLEdBQUcsWUFBQSxDQUFDO0FBQ1IsZ0JBQUksQ0FBQyxPQUFPLElBQUksT0FBTyxDQUFDLElBQUksRUFBRSxFQUFFLEVBQUUsQ0FBQyxDQUFDLEVBQUU7QUFDbEMsbUJBQUcsR0FBRyxNQUFNLENBQUMsUUFBUSxDQUFDLENBQUMsSUFBSSxFQUFFLEVBQUUsRUFBRSxDQUFDLENBQUMsQ0FBQzthQUN2QyxNQUFNO0FBQ0gsdUJBQU87YUFDVjtBQUNELGdCQUFJLFFBQVEsRUFBRTtBQUNWLG1CQUFHLEdBQUcsUUFBUSxDQUFDLElBQUksRUFBRSxFQUFFLEVBQUUsQ0FBQyxDQUFDLENBQUM7YUFDL0I7QUFDRCxtQkFBTyxHQUFHLENBQUM7U0FDZCxDQUFBOzs7O0FBZkwsU0FBSyxJQUFJLFFBQVEsSUFBSSxNQUFNLEVBQUU7eUJBQXBCLFFBQVE7O2lDQUVULFNBQVM7S0FjaEI7QUFDRCxXQUFPLFNBQVMsQ0FBQztDQUNwQjs7QUFFRCxTQUFTLEtBQUssQ0FBQyxJQUFJLEVBQUUsS0FBSyxFQUFFO0FBQ3hCLFFBQUksQ0FBQyxJQUFJLEdBQUcsSUFBSSxDQUFDO0FBQ2pCLFFBQUksQ0FBQyxLQUFLLEdBQUcsS0FBSyxDQUFDO0NBQ3RCOztBQUVELFNBQVMsZ0JBQWdCLENBQUMsR0FBRyxFQUFFLEdBQUcsRUFBRTtBQUNoQyxnQkFBWSxDQUFDOzs7OztBQUtiLFFBQU0sTUFBTSxHQUFHLFVBQVUsQ0FBQyxTQUFTLEVBQy9CLFVBQUMsSUFBSSxFQUFFLEVBQUUsRUFBSztBQUNWLFlBQUksSUFBSSxDQUFDLEtBQUssR0FBRyxHQUFHLElBQUksSUFBSSxDQUFDLEdBQUcsR0FBRyxHQUFHLEVBQUU7QUFDcEMsbUJBQU8sS0FBSyxDQUFDO1NBQ2hCO0FBQ0QsWUFBSSxJQUFJLENBQUMsSUFBSSxLQUFLLFlBQVksSUFBSSxJQUFJLENBQUMsSUFBSSxLQUFLLEdBQUcsRUFBRTtBQUNqRCxrQkFBTSxJQUFJLEtBQUssQ0FBQyxJQUFJLEVBQUUsRUFBRSxDQUFDLENBQUM7U0FDN0I7QUFDRCxlQUFPLElBQUksQ0FBQztLQUNmLENBQUMsQ0FBQzs7QUFFUCxRQUFJO0FBQ0EsWUFBSSxDQUFDLFNBQVMsQ0FBQyxHQUFHLEVBQUUsR0FBRyxDQUFDLFFBQVEsQ0FBQyxFQUFFLE1BQU0sQ0FBQyxDQUFDO0tBQzlDLENBQUMsT0FBTyxDQUFDLEVBQUU7QUFDUixZQUFJLENBQUMsWUFBWSxLQUFLLEVBQUU7QUFDcEIsbUJBQU8sQ0FBQyxDQUFDO1NBQ1osTUFBTTtBQUNILGtCQUFNLENBQUMsQ0FBQztTQUNYO0tBQ0o7O0FBRUQsV0FBTyxJQUFJLENBQUM7Ozs7OztDQU1mOzs7Ozs7OztBQVFELFNBQVMsYUFBYSxDQUFDLEdBQUcsRUFBRSxHQUFHLEVBQUU7QUFDN0IsZ0JBQVksQ0FBQztBQUNiLFFBQUksS0FBSyxHQUFHLGdCQUFnQixDQUFDLEdBQUcsRUFBRSxHQUFHLENBQUMsQ0FBQztBQUN2QyxRQUFJLENBQUMsS0FBSyxFQUFFOztBQUVSLGVBQU8sSUFBSSxDQUFDO0tBQ2Y7O0FBRUQsUUFBSSxJQUFJLEdBQUcsa0JBQWtCLENBQUMsR0FBRyxFQUFFLEtBQUssQ0FBQyxDQUFDOztBQUUxQyxXQUFPLElBQUksQ0FBQztDQUNmOzs7Ozs7OztBQVFELFNBQVMsa0JBQWtCLENBQUMsR0FBRyxFQUFFLEtBQUssRUFBRTtBQUNwQyxnQkFBWSxDQUFDO0FBQ2IsUUFBTSxPQUFPLEdBQUcsS0FBSyxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUM7QUFDaEMsUUFBTSxHQUFHLEdBQUcsS0FBSyxDQUFDLEtBQUssQ0FBQyxjQUFjLENBQUMsT0FBTyxDQUFDLENBQUM7QUFDaEQsUUFBTSxLQUFLLEdBQUcsR0FBRyxDQUFDLFVBQVUsQ0FBQyxLQUFLLENBQUM7QUFDbkMsUUFBTSxHQUFHLEdBQUcsR0FBRyxDQUFDLFVBQVUsQ0FBQyxHQUFHLENBQUM7QUFDL0IsUUFBTSxJQUFJLEdBQUcsRUFBRSxDQUFDOztBQUVoQixRQUFJLE1BQU0sR0FBRyxJQUFJLENBQUMsSUFBSSxDQUFDO0FBQ25CLGtCQUFVLEVBQUUsb0JBQUMsSUFBSSxFQUFFLEVBQUUsRUFBRSxDQUFDLEVBQUs7QUFDekIsZ0JBQUksSUFBSSxDQUFDLElBQUksS0FBSyxPQUFPLEVBQUUsT0FBTztBQUNsQyxnQkFBTSxHQUFHLEdBQUcsRUFBRSxDQUFDLGNBQWMsQ0FBQyxPQUFPLENBQUMsQ0FBQztBQUN2QyxnQkFBSSxHQUFHLEtBQUssR0FBRyxFQUFFLElBQUksQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDLENBQUM7U0FDcEM7S0FDSixFQUFFLFNBQVMsQ0FBQyxDQUFDO0FBQ2xCLFFBQUksS0FBSyxHQUFHLENBQUMsQ0FBQzs7QUFFVixVQUFNLEdBQUcsVUFBVSxDQUFDLE1BQU0sRUFBRSxVQUFDLElBQUksRUFBRSxFQUFFLEVBQUs7O0FBRXRDLGVBQU8sQ0FBQyxJQUFJLENBQUMsS0FBSyxFQUFFLENBQUMsQ0FBQztBQUN0QixlQUFPLENBQUMsSUFBSSxDQUFDLEVBQUUsQ0FBQyxDQUFDO0FBQ2pCLGVBQU8sR0FBRyxJQUFJLElBQUksQ0FBQyxLQUFLLElBQUksSUFBSSxDQUFDLEdBQUcsSUFBSSxLQUFLLENBQUM7O0tBRWpELENBQUMsQ0FBQzs7QUFFSCxRQUFJLENBQUMsU0FBUyxDQUFDLEdBQUcsRUFBRSxHQUFHLENBQUMsUUFBUSxDQUFDLEVBQUUsTUFBTSxDQUFDLENBQUM7O0FBRTNDLFdBQU8sSUFBSSxDQUFDO0NBQ2Y7Ozs7QUFJRCxTQUFTLElBQUksR0FBRztBQUNaLGdCQUFZLENBQUM7QUFDYixRQUFJLFFBQVEsR0FBRyxFQUFFLENBQUMsWUFBWSxDQUFDLGNBQWMsQ0FBQyxDQUFDO0FBQy9DLFFBQUksTUFBTSxHQUFHLEtBQUssQ0FBQyxPQUFPLENBQUMsUUFBUSxFQUFFLElBQUksQ0FBQyxDQUFDOztBQUUzQyxTQUFLLElBQUksQ0FBQyxHQUFHLENBQUMsRUFBRSxDQUFDLEdBQUcsUUFBUSxDQUFDLE1BQU0sRUFBRSxDQUFDLEVBQUUsRUFBRTtBQUN0QyxZQUFJLFNBQVMsR0FBRyxnQkFBZ0IsQ0FBQyxNQUFNLENBQUMsR0FBRyxFQUFFLENBQUMsQ0FBQyxDQUFDO0FBQ2hELFlBQUksU0FBUyxFQUFFO0FBQ1gsbUJBQU8sQ0FBQyxHQUFHLENBQUMsQ0FBQyxFQUFFLElBQUksRUFBRSxTQUFTLENBQUMsSUFBSSxDQUFDLENBQUM7U0FDeEM7S0FDSjtDQUNKOztBQUVELE9BQU8sQ0FBQyxnQkFBZ0IsR0FBRyxnQkFBZ0IsQ0FBQztBQUM1QyxPQUFPLENBQUMsYUFBYSxHQUFHLGFBQWEsQ0FBQzs7OztBQ2pMdEM7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBOzs7OztBQzc2SEE7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBOzs7O0FDclZBOztBQ0FBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTs7QUN2QkE7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7O0FDMUZBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTs7O0FDTEE7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSIsImZpbGUiOiJnZW5lcmF0ZWQuanMiLCJzb3VyY2VSb290IjoiIiwic291cmNlc0NvbnRlbnQiOlsiKGZ1bmN0aW9uIGUodCxuLHIpe2Z1bmN0aW9uIHMobyx1KXtpZighbltvXSl7aWYoIXRbb10pe3ZhciBhPXR5cGVvZiByZXF1aXJlPT1cImZ1bmN0aW9uXCImJnJlcXVpcmU7aWYoIXUmJmEpcmV0dXJuIGEobywhMCk7aWYoaSlyZXR1cm4gaShvLCEwKTt2YXIgZj1uZXcgRXJyb3IoXCJDYW5ub3QgZmluZCBtb2R1bGUgJ1wiK28rXCInXCIpO3Rocm93IGYuY29kZT1cIk1PRFVMRV9OT1RfRk9VTkRcIixmfXZhciBsPW5bb109e2V4cG9ydHM6e319O3Rbb11bMF0uY2FsbChsLmV4cG9ydHMsZnVuY3Rpb24oZSl7dmFyIG49dFtvXVsxXVtlXTtyZXR1cm4gcyhuP246ZSl9LGwsbC5leHBvcnRzLGUsdCxuLHIpfXJldHVybiBuW29dLmV4cG9ydHN9dmFyIGk9dHlwZW9mIHJlcXVpcmU9PVwiZnVuY3Rpb25cIiYmcmVxdWlyZTtmb3IodmFyIG89MDtvPHIubGVuZ3RoO28rKylzKHJbb10pO3JldHVybiBzfSkiLCJ2YXIgdXRpbCA9IHJlcXVpcmUoJ3V0aWwnKTtcblxuZnVuY3Rpb24gZ2V0Tm9kZUxpc3QoYXN0LCBzdGFydE51bSkge1xuICAgIHZhciBub2RlTGlzdCA9IFtdO1xuXG4gICAgdmFyIG51bSA9IHN0YXJ0TnVtID09PSB1bmRlZmluZWQgPyAwIDogc3RhcnROdW07XG5cbiAgICBmdW5jdGlvbiBhc3NpZ25JZChub2RlKSB7XG4gICAgICAgIG5vZGVbJ0BsYWJlbCddID0gbnVtO1xuICAgICAgICBub2RlTGlzdC5wdXNoKG5vZGUpO1xuICAgICAgICBudW0rKztcbiAgICB9XG5cbiAgICAvLyBMYWJlbCBldmVyeSBBU1Qgbm9kZSB3aXRoIHByb3BlcnR5ICd0eXBlJ1xuICAgIGZ1bmN0aW9uIGxhYmVsTm9kZVdpdGhUeXBlKG5vZGUpIHtcbiAgICAgICAgaWYgKG5vZGUgJiYgbm9kZS5oYXNPd25Qcm9wZXJ0eSgndHlwZScpKSB7XG4gICAgICAgICAgICBhc3NpZ25JZChub2RlKTtcbiAgICAgICAgfVxuICAgICAgICBpZiAobm9kZSAmJiB0eXBlb2Ygbm9kZSA9PT0gJ29iamVjdCcpIHtcbiAgICAgICAgICAgIGZvciAodmFyIHAgaW4gbm9kZSkge1xuICAgICAgICAgICAgICAgIGxhYmVsTm9kZVdpdGhUeXBlKG5vZGVbcF0pO1xuICAgICAgICAgICAgfVxuICAgICAgICB9XG4gICAgfVxuXG4gICAgbGFiZWxOb2RlV2l0aFR5cGUoYXN0KTtcblxuICAgIHJldHVybiBub2RlTGlzdDtcbn1cblxuZnVuY3Rpb24gc2hvd1VuZm9sZGVkKG9iaikge1xuICAgIGNvbnNvbGUubG9nKHV0aWwuaW5zcGVjdChvYmosIHtkZXB0aDogbnVsbH0pKTtcbn1cblxuZXhwb3J0cy5nZXROb2RlTGlzdCA9IGdldE5vZGVMaXN0O1xuZXhwb3J0cy5zaG93VW5mb2xkZWQgPSBzaG93VW5mb2xkZWQ7XG4iLCIndXNlIHN0cmljdCc7XG5cbmNvbnN0IHR5cGVzID0gcmVxdWlyZSgnLi4vZG9tYWlucy90eXBlcycpO1xuY29uc3Qgd2FsayA9IHJlcXVpcmUoJ2Fjb3JuL2Rpc3Qvd2FsaycpO1xuY29uc3Qgc3RhdHVzID0gcmVxdWlyZSgnLi4vZG9tYWlucy9zdGF0dXMnKTtcbmNvbnN0IGNzdHIgPSByZXF1aXJlKCcuL2NvbnN0cmFpbnRzJyk7XG5cbi8vIGFyZ3VtZW50cyBhcmUgXCIgb2xkU3RhdHVzICgsIG5hbWUsIHZhbCkqIFwiXG5mdW5jdGlvbiBjaGFuZ2VkU3RhdHVzKG9sZFN0YXR1cykge1xuICAgIGNvbnN0IG5ld1N0YXR1cyA9IG5ldyBzdGF0dXMuU3RhdHVzO1xuICAgIGZvciAobGV0IGkgPSAxOyBpIDwgYXJndW1lbnRzLmxlbmd0aDsgaSA9IGkgKyAyKVxuICAgICAgICBuZXdTdGF0dXNbYXJndW1lbnRzW2ldXSA9IGFyZ3VtZW50c1tpKzFdO1xuXG4gICAgZm9yIChsZXQgcCBpbiBvbGRTdGF0dXMpIHtcbiAgICAgICAgaWYgKG5ld1N0YXR1c1twXSA9PT0gdW5kZWZpbmVkKVxuICAgICAgICAgICAgbmV3U3RhdHVzW3BdID0gb2xkU3RhdHVzW3BdO1xuICAgIH1cbiAgICByZXR1cm4gbmV3U3RhdHVzO1xufVxuXG4vLyByZXR1cm5zIFthY2Nlc3MgdHlwZSwgcHJvcCB2YWx1ZV1cbmZ1bmN0aW9uIHByb3BBY2Nlc3Mobm9kZSkge1xuICAgIGNvbnN0IHByb3AgPSBub2RlLnByb3BlcnR5O1xuICAgIGlmICghbm9kZS5jb21wdXRlZCkge1xuICAgICAgICByZXR1cm4gWydkb3RBY2Nlc3MnLCBwcm9wLm5hbWVdO1xuICAgIH1cbiAgICBpZiAocHJvcC50eXBlID09PSAnTGl0ZXJhbCcpIHtcbiAgICAgICAgaWYgKHR5cGVvZiBwcm9wLnZhbHVlID09PSAnc3RyaW5nJylcbiAgICAgICAgICAgIHJldHVybiBbJ3N0cmluZ0xpdGVyYWwnLCBwcm9wLnZhbHVlXTtcbiAgICAgICAgaWYgKHR5cGVvZiBwcm9wLnZhbHVlID09PSAnbnVtYmVyJylcbiAgICAgICAgICAgIC8vIGNvbnZlcnQgbnVtYmVyIHRvIHN0cmluZ1xuICAgICAgICAgICAgcmV0dXJuIFsnbnVtYmVyTGl0ZXJhbCcsIHByb3AudmFsdWUgKyAnJ107XG4gICAgfVxuICAgIHJldHVybiBbXCJjb21wdXRlZFwiLCBudWxsXTtcbn1cblxuZnVuY3Rpb24gdW5vcFJlc3VsdFR5cGUob3ApIHtcbiAgICBzd2l0Y2ggKG9wKSB7XG4gICAgICAgIGNhc2UgJysnOiBjYXNlICctJzogY2FzZSAnfic6XG4gICAgICAgICAgICByZXR1cm4gdHlwZXMuUHJpbU51bWJlcjtcbiAgICAgICAgY2FzZSAnISc6XG4gICAgICAgICAgICByZXR1cm4gdHlwZXMuUHJpbUJvb2xlYW47XG4gICAgICAgIGNhc2UgJ3R5cGVvZic6XG4gICAgICAgICAgICByZXR1cm4gdHlwZXMuUHJpbVN0cmluZztcbiAgICAgICAgY2FzZSAndm9pZCc6IGNhc2UgJ2RlbGV0ZSc6XG4gICAgICAgICAgICByZXR1cm4gbnVsbDtcbiAgICB9XG59XG5cbmZ1bmN0aW9uIGJpbm9wSXNCb29sZWFuKG9wKSB7XG4gICAgc3dpdGNoIChvcCkge1xuICAgICAgICBjYXNlICc9PSc6IGNhc2UgJyE9JzogY2FzZSAnPT09JzogY2FzZSAnIT09JzpcbiAgICAgICAgY2FzZSAnPCc6IGNhc2UgJz4nOiBjYXNlICc+PSc6IGNhc2UgJzw9JzpcbiAgICAgICAgY2FzZSAnaW4nOiBjYXNlICdpbnN0YW5jZW9mJzpcbiAgICAgICAgICAgIHJldHVybiB0cnVlO1xuICAgIH1cbiAgICByZXR1cm4gZmFsc2U7XG59XG5cbmZ1bmN0aW9uIHJlYWRNZW1iZXIobm9kZSwgY3VyU3RhdHVzLCBjKSB7XG4gICAgY29uc3QgcmV0ID0gbmV3IHR5cGVzLkFWYWw7XG4gICAgY29uc3Qgb2JqQVZhbCA9IGMobm9kZS5vYmplY3QsIGN1clN0YXR1cywgdW5kZWZpbmVkKTtcbiAgICBpZiAobm9kZS5wcm9wZXJ0eS50eXBlICE9PSAnSWRlbnRpZmllcicpIHtcbiAgICAgICAgLy8gcmV0dXJuIGZyb20gcHJvcGVydHkgaXMgaWdub3JlZFxuICAgICAgICBjKG5vZGUucHJvcGVydHksIGN1clN0YXR1cywgdW5kZWZpbmVkKTtcbiAgICB9XG4gICAgY29uc3QgcHJvcEFjYyA9IHByb3BBY2Nlc3Mobm9kZSk7XG5cbiAgICBjb25zdHJhaW50cy5wdXNoKHtPQko6IG9iakFWYWwsXG4gICAgICAgICAgICAgICAgICAgICAgUFJPUDogcHJvcEFjY1sxXSxcbiAgICAgICAgICAgICAgICAgICAgICBSRUFEX1RPOiByZXR9KTtcbiAgICBvYmpBVmFsLnByb3BhZ2F0ZShuZXcgY3N0ci5SZWFkUHJvcChwcm9wQWNjWzFdLCByZXQpKTtcblxuICAgIC8vIHJldHVybnMgQVZhbCBmb3IgcmVjZWl2ZXIgYW5kIHJlYWQgbWVtYmVyXG4gICAgcmV0dXJuIFtvYmpBVmFsLCByZXRdO1xufVxuLy8gVG8gcHJldmVudCByZWN1cnNpb24sXG4vLyB3ZSByZW1lbWJlciB0aGUgc3RhdHVzIHVzZWQgaW4gYWRkQ29uc3RyYWludHNcbmNvbnN0IHZpc2l0ZWRTdGF0dXMgPSBbXTtcbmNvbnN0IGNvbnN0cmFpbnRzID0gW107XG5mdW5jdGlvbiBjbGVhckNvbnN0cmFpbnRzKCkge1xuICAgIHZpc2l0ZWRTdGF0dXMubGVuZ3RoID0gMDtcbiAgICBjb25zdHJhaW50cy5sZW5ndGggPSAwO1xufVxuXG5sZXQgcnRDWDtcbmZ1bmN0aW9uIGFkZENvbnN0cmFpbnRzKGFzdCwgaW5pdFN0YXR1cywgbmV3UnRDWCkge1xuXG4gICAgLy8gc2V0IHJ0Q1hcbiAgICBydENYID0gbmV3UnRDWCB8fCBydENYO1xuXG4gICAgLy8gQ2hlY2sgd2hldGhlciB3ZSBoYXZlIHByb2Nlc3NlZCAnaW5pdFN0YXR1cycgYmVmb3JlXG4gICAgZm9yIChsZXQgaT0wOyBpIDwgdmlzaXRlZFN0YXR1cy5sZW5ndGg7IGkrKykge1xuICAgICAgICBpZiAoaW5pdFN0YXR1cy5lcXVhbHModmlzaXRlZFN0YXR1c1tpXSkpIHtcbiAgICAgICAgICAgICAvLyBJZiBzbywgZG8gbm90aGluZ1xuICAgICAgICAgICAgIC8vIHNpZ25pZnlpbmcgd2UgZGlkbid0IGFkZCBjb25zdHJhaW50c1xuICAgICAgICAgICAgIHJldHVybiBmYWxzZTtcbiAgICAgICAgIH1cbiAgICB9XG4gICAgLy8gSWYgdGhlIGluaXRTdGF0dXMgaXMgbmV3LCBwdXNoIGl0LlxuICAgIC8vIFdlIGRvIG5vdCByZWNvcmQgYXN0IHNpbmNlIGFzdCBub2RlIGRlcGVuZHMgb24gdGhlIHN0YXR1c1xuICAgIHZpc2l0ZWRTdGF0dXMucHVzaChpbml0U3RhdHVzKTtcblxuICAgIC8vIGNvbnN0cmFpbnQgZ2VuZXJhdGluZyB3YWxrZXIgZm9yIGV4cHJlc3Npb25zXG4gICAgY29uc3QgY29uc3RyYWludEdlbmVyYXRvciA9IHdhbGsubWFrZSh7XG5cbiAgICAgICAgSWRlbnRpZmllcjogZnVuY3Rpb24gKG5vZGUsIGN1clN0YXR1cywgYykge1xuICAgICAgICAgICAgcmV0dXJuIGN1clN0YXR1cy5zYy5nZXRBVmFsT2Yobm9kZS5uYW1lKTtcbiAgICAgICAgfSxcblxuICAgICAgICBUaGlzRXhwcmVzc2lvbjogZnVuY3Rpb24gKG5vZGUsIGN1clN0YXR1cywgYykge1xuICAgICAgICAgICAgcmV0dXJuIGN1clN0YXR1cy5zZWxmO1xuICAgICAgICB9LFxuXG4gICAgICAgIExpdGVyYWw6IGZ1bmN0aW9uIChub2RlLCBjdXJTdGF0dXMsIGMpIHtcbiAgICAgICAgICAgIGNvbnN0IHJlcyA9IG5ldyB0eXBlcy5BVmFsO1xuICAgICAgICAgICAgaWYgKG5vZGUucmVnZXgpIHtcbiAgICAgICAgICAgICAgICAvLyBub3QgaW1wbGVtZW50ZWQgeWV0XG4gICAgICAgICAgICAgICAgLy8gdGhyb3cgbmV3IEVycm9yKCdyZWdleCBsaXRlcmFsIGlzIG5vdCBpbXBsZW1lbnRlZCB5ZXQnKTtcbiAgICAgICAgICAgICAgICByZXR1cm4gcmVzO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgc3dpdGNoICh0eXBlb2Ygbm9kZS52YWx1ZSkge1xuICAgICAgICAgICAgY2FzZSAnbnVtYmVyJzpcbiAgICAgICAgICAgICAgICBjb25zdHJhaW50cy5wdXNoKHtUWVBFOiB0eXBlcy5QcmltTnVtYmVyLFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIElOQ0xfU0VUOiByZXN9KTtcbiAgICAgICAgICAgICAgICByZXMuYWRkVHlwZSh0eXBlcy5QcmltTnVtYmVyKTtcbiAgICAgICAgICAgICAgICBicmVhaztcbiAgICAgICAgICAgIGNhc2UgJ3N0cmluZyc6XG4gICAgICAgICAgICAgICAgY29uc3RyYWludHMucHVzaCh7VFlQRTogdHlwZXMuUHJpbVN0cmluZyxcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBJTkNMX1NFVDogcmVzfSk7XG4gICAgICAgICAgICAgICAgcmVzLmFkZFR5cGUodHlwZXMuUHJpbVN0cmluZyk7XG4gICAgICAgICAgICAgICAgYnJlYWs7XG4gICAgICAgICAgICBjYXNlICdib29sZWFuJzpcbiAgICAgICAgICAgICAgICBjb25zdHJhaW50cy5wdXNoKHtUWVBFOiB0eXBlcy5QcmltQm9vbGVhbixcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBJTkNMX1NFVDogcmVzfSk7XG4gICAgICAgICAgICAgICAgcmVzLmFkZFR5cGUodHlwZXMuUHJpbUJvb2xlYW4pO1xuICAgICAgICAgICAgICAgIGJyZWFrO1xuICAgICAgICAgICAgY2FzZSAnb2JqZWN0JzpcbiAgICAgICAgICAgICAgICAvLyBJIGd1ZXNzOiBMaXRlcmFsICYmIG9iamVjdCA9PT4gbm9kZS52YWx1ZSA9PSBudWxsXG4gICAgICAgICAgICAgICAgLy8gbnVsbCBpcyBpZ25vcmVkLCBzbyBub3RoaW5nIHRvIGFkZFxuICAgICAgICAgICAgICAgIGJyZWFrO1xuICAgICAgICAgICAgY2FzZSAnZnVuY3Rpb24nOlxuICAgICAgICAgICAgICAgIHRocm93IG5ldyBFcnJvcignSSBndWVzcyBmdW5jdGlvbiBpcyBpbXBvc3NpYmxlIGhlcmUuJyk7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICByZXR1cm4gcmVzO1xuICAgICAgICB9LFxuXG4gICAgICAgIEFzc2lnbm1lbnRFeHByZXNzaW9uOiBmdW5jdGlvbiAobm9kZSwgY3VyU3RhdHVzLCBjKSB7XG4gICAgICAgICAgICBjb25zdCByaHNBVmFsID0gYyhub2RlLnJpZ2h0LCBjdXJTdGF0dXMsIHVuZGVmaW5lZCk7XG4gICAgICAgICAgICBpZiAobm9kZS5sZWZ0LnR5cGUgIT09ICdNZW1iZXJFeHByZXNzaW9uJykge1xuICAgICAgICAgICAgICAgIC8vIExIUyBpcyBhIHNpbXBsZSB2YXJpYWJsZS5cbiAgICAgICAgICAgICAgICBjb25zdCB2YXJOYW1lID0gbm9kZS5sZWZ0Lm5hbWU7XG4gICAgICAgICAgICAgICAgY29uc3QgbGhzQVZhbCA9IGN1clN0YXR1cy5zYy5nZXRBVmFsT2YodmFyTmFtZSk7XG5cbiAgICAgICAgICAgICAgICBpZiAobm9kZS5vcGVyYXRvciA9PT0gJz0nKSB7XG4gICAgICAgICAgICAgICAgICAgIC8vIHNpbXBsZSBhc3NpZ25tZW50XG4gICAgICAgICAgICAgICAgICAgIGNvbnN0cmFpbnRzLnB1c2goe1xuICAgICAgICAgICAgICAgICAgICAgICAgRlJPTTogcmhzQVZhbCxcbiAgICAgICAgICAgICAgICAgICAgICAgIFRPOiBsaHNBVmFsXG4gICAgICAgICAgICAgICAgICAgIH0pO1xuICAgICAgICAgICAgICAgICAgICByaHNBVmFsLnByb3BhZ2F0ZShsaHNBVmFsKTtcbiAgICAgICAgICAgICAgICAgICAgLy8gY29ycmVzcG9uZGluZyBBVmFsIGlzIHRoZSBSSFNcbiAgICAgICAgICAgICAgICAgICAgcmV0dXJuIHJoc0FWYWw7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIGNvbnN0IHJlc0FWYWwgPSBuZXcgdHlwZXMuQVZhbDtcbiAgICAgICAgICAgICAgICBpZiAobm9kZS5vcGVyYXRvciA9PT0gJys9Jykge1xuICAgICAgICAgICAgICAgICAgICAvLyBjb25jYXRlbmF0aW5nIHVwZGF0ZVxuICAgICAgICAgICAgICAgICAgICBjb25zdHJhaW50cy5wdXNoKHtcbiAgICAgICAgICAgICAgICAgICAgICAgIEFERF9PUFJEMTogbGhzQVZhbCxcbiAgICAgICAgICAgICAgICAgICAgICAgIEFERF9PUFJEMjogcmhzQVZhbCxcbiAgICAgICAgICAgICAgICAgICAgICAgIFJFU1VMVDogcmVzQVZhbFxuICAgICAgICAgICAgICAgICAgICB9KTtcbiAgICAgICAgICAgICAgICAgICAgbGhzQVZhbC5wcm9wYWdhdGUobmV3IGNzdHIuSXNBZGRlZChyaHNBVmFsLCByZXNBVmFsKSk7XG4gICAgICAgICAgICAgICAgICAgIHJoc0FWYWwucHJvcGFnYXRlKG5ldyBjc3RyLklzQWRkZWQobGhzQVZhbCwgcmVzQVZhbCkpO1xuICAgICAgICAgICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgICAgICAgICAgIC8vIGFyaXRobWV0aWMgdXBkYXRlXG4gICAgICAgICAgICAgICAgICAgIGNvbnN0cmFpbnRzLnB1c2goe1xuICAgICAgICAgICAgICAgICAgICAgICAgVFlQRTp0eXBlcy5QcmltTnVtYmVyLFxuICAgICAgICAgICAgICAgICAgICAgICAgSU5DTF9TRVQ6IHJlc0FWYWxcbiAgICAgICAgICAgICAgICAgICAgfSk7XG4gICAgICAgICAgICAgICAgICAgIHJlc0FWYWwuYWRkVHlwZSh0eXBlcy5QcmltTnVtYmVyKTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgcmV0dXJuIHJlc0FWYWw7XG4gICAgICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgICAgICAgIC8vIG1lbWJlciBhc3NpZ25tZW50XG4gICAgICAgICAgICAgICAgY29uc3Qgb2JqQVZhbCA9IGMobm9kZS5sZWZ0Lm9iamVjdCwgY3VyU3RhdHVzLCB1bmRlZmluZWQpO1xuICAgICAgICAgICAgICAgIGNvbnN0IHByb3BBY2MgPSBwcm9wQWNjZXNzKG5vZGUubGVmdCk7XG4gICAgICAgICAgICAgICAgaWYgKG5vZGUub3BlcmF0b3IgPT09ICc9Jykge1xuICAgICAgICAgICAgICAgICAgICAvLyBhc3NpZ25tZW50IHRvIG1lbWJlclxuICAgICAgICAgICAgICAgICAgICBjb25zdHJhaW50cy5wdXNoKHtcbiAgICAgICAgICAgICAgICAgICAgICAgIE9CSjogb2JqQVZhbCxcbiAgICAgICAgICAgICAgICAgICAgICAgIFBST1A6IHByb3BBY2NbMV0sXG4gICAgICAgICAgICAgICAgICAgICAgICBXUklURV9XSVRIOiByaHNBVmFsXG4gICAgICAgICAgICAgICAgICAgIH0pO1xuICAgICAgICAgICAgICAgICAgICBvYmpBVmFsLnByb3BhZ2F0ZShuZXcgY3N0ci5Xcml0ZVByb3AocHJvcEFjY1sxXSwgcmhzQVZhbCkpO1xuICAgICAgICAgICAgICAgICAgICAvLyBpZiBwcm9wZXJ0eSBpcyBudW1iZXIgbGl0ZXJhbCwgYWxzbyB3cml0ZSB0byAndW5rbm93bidcbiAgICAgICAgICAgICAgICAgICAgaWYgKHByb3BBY2NbMF0gPT09ICdudW1iZXJMaXRlcmFsJykge1xuICAgICAgICAgICAgICAgICAgICAgICAgb2JqQVZhbC5wcm9wYWdhdGUobmV3IGNzdHIuV3JpdGVQcm9wKG51bGwsIHJoc0FWYWwpKTtcbiAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICByZXR1cm4gcmhzQVZhbDtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgY29uc3QgcmVzQVZhbCA9IG5ldyB0eXBlcy5BVmFsO1xuICAgICAgICAgICAgICAgIGNvbnN0IHJlY3ZBbmRSZXQgPSByZWFkTWVtYmVyKG5vZGUubGVmdCwgY3VyU3RhdHVzLCBjKTtcbiAgICAgICAgICAgICAgICBpZiAobm9kZS5vcGVyYXRvciA9PT0gJys9Jykge1xuICAgICAgICAgICAgICAgICAgICAvLyBjb25jYXRlbmF0aW5nIHVwZGF0ZVxuICAgICAgICAgICAgICAgICAgICBjb25zdHJhaW50cy5wdXNoKHtcbiAgICAgICAgICAgICAgICAgICAgICAgIEFERF9PUFJEMTogcmVjdkFuZFJldFsxXSxcbiAgICAgICAgICAgICAgICAgICAgICAgIEFERF9PUFJEMjogcmhzQVZhbCxcbiAgICAgICAgICAgICAgICAgICAgICAgIFJFU1VMVDogcmVzQVZhbFxuICAgICAgICAgICAgICAgICAgICB9KTtcbiAgICAgICAgICAgICAgICAgICAgcmVjdkFuZFJldFsxXS5wcm9wYWdhdGUobmV3IGNzdHIuSXNBZGRlZChyaHNBVmFsLCByZXNBVmFsKSk7XG4gICAgICAgICAgICAgICAgICAgIHJoc0FWYWwucHJvcGFnYXRlKG5ldyBjc3RyLklzQWRkZWQocmVjdkFuZFJldFsxXSwgcmVzQVZhbCkpO1xuICAgICAgICAgICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgICAgICAgICAgIC8vIGFyaXRobWV0aWMgdXBkYXRlXG4gICAgICAgICAgICAgICAgICAgIGNvbnN0cmFpbnRzLnB1c2goe1xuICAgICAgICAgICAgICAgICAgICAgICAgVFlQRTogdHlwZXMuUHJpbU51bWJlcixcbiAgICAgICAgICAgICAgICAgICAgICAgIElOQ0xfU0VUOiByZXNBVmFsXG4gICAgICAgICAgICAgICAgICAgIH0pO1xuICAgICAgICAgICAgICAgICAgICByZXNBVmFsLmFkZFR5cGUodHlwZXMuUHJpbU51bWJlcik7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIHJldHVybiByZXNBVmFsO1xuICAgICAgICAgICAgfVxuICAgICAgICB9LFxuXG4gICAgICAgIFZhcmlhYmxlRGVjbGFyYXRpb246IGZ1bmN0aW9uIChub2RlLCBjdXJTdGF0dXMsIGMpIHtcbiAgICAgICAgICAgIGZvciAobGV0IGkgPSAwOyBpIDwgbm9kZS5kZWNsYXJhdGlvbnMubGVuZ3RoOyBpKyspIHtcbiAgICAgICAgICAgICAgICBjb25zdCBkZWNsID0gbm9kZS5kZWNsYXJhdGlvbnNbaV07XG4gICAgICAgICAgICAgICAgaWYgKGRlY2wuaW5pdCkge1xuICAgICAgICAgICAgICAgICAgICBjb25zdCBsaHNBVmFsID0gY3VyU3RhdHVzLnNjLmdldEFWYWxPZihkZWNsLmlkLm5hbWUpO1xuICAgICAgICAgICAgICAgICAgICBjb25zdCByaHNBVmFsID0gYyhkZWNsLmluaXQsIGN1clN0YXR1cywgdW5kZWZpbmVkKTtcbiAgICAgICAgICAgICAgICAgICAgY29uc3RyYWludHMucHVzaCh7RlJPTTogcmhzQVZhbCxcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgVE86IGxoc0FWYWx9KTtcbiAgICAgICAgICAgICAgICAgICAgcmhzQVZhbC5wcm9wYWdhdGUobGhzQVZhbCk7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgfVxuICAgICAgICB9LFxuXG4gICAgICAgIExvZ2ljYWxFeHByZXNzaW9uOiBmdW5jdGlvbiAobm9kZSwgY3VyU3RhdHVzLCBjKSB7XG4gICAgICAgICAgICBjb25zdCByZXMgPSBuZXcgdHlwZXMuQVZhbDtcbiAgICAgICAgICAgIGNvbnN0IGxlZnQgPSBjKG5vZGUubGVmdCwgY3VyU3RhdHVzLCB1bmRlZmluZWQpO1xuICAgICAgICAgICAgY29uc3QgcmlnaHQgPSBjKG5vZGUucmlnaHQsIGN1clN0YXR1cywgdW5kZWZpbmVkKTtcbiAgICAgICAgICAgIGNvbnN0cmFpbnRzLnB1c2goe0ZST006IGxlZnQsIFRPOiByZXN9LFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICB7RlJPTTogcmlnaHQsIFRPOiByZXN9KTtcbiAgICAgICAgICAgIGxlZnQucHJvcGFnYXRlKHJlcyk7XG4gICAgICAgICAgICByaWdodC5wcm9wYWdhdGUocmVzKTtcbiAgICAgICAgICAgIHJldHVybiByZXM7XG4gICAgICAgIH0sXG5cbiAgICAgICAgQ29uZGl0aW9uYWxFeHByZXNzaW9uOiBmdW5jdGlvbiAobm9kZSwgY3VyU3RhdHVzLCBjKSB7XG4gICAgICAgICAgICBjb25zdCByZXMgPSBuZXcgdHlwZXMuQVZhbDtcbiAgICAgICAgICAgIGMobm9kZS50ZXN0LCBjdXJTdGF0dXMsIHVuZGVmaW5lZCk7XG4gICAgICAgICAgICBjb25zdCBjb25zID0gYyhub2RlLmNvbnNlcXVlbnQsIGN1clN0YXR1cywgdW5kZWZpbmVkKTtcbiAgICAgICAgICAgIGNvbnN0IGFsdCA9IGMobm9kZS5hbHRlcm5hdGUsIGN1clN0YXR1cywgdW5kZWZpbmVkKTtcbiAgICAgICAgICAgIGNvbnN0cmFpbnRzLnB1c2goe0ZST006IGNvbnMsIFRPOiByZXN9LFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICB7RlJPTTogYWx0LCBUTzogcmVzfSk7XG4gICAgICAgICAgICBjb25zLnByb3BhZ2F0ZShyZXMpO1xuICAgICAgICAgICAgYWx0LnByb3BhZ2F0ZShyZXMpO1xuICAgICAgICAgICAgcmV0dXJuIHJlcztcbiAgICAgICAgfSxcblxuICAgICAgICBOZXdFeHByZXNzaW9uOiBmdW5jdGlvbiAobm9kZSwgY3VyU3RhdHVzLCBjKSB7XG4gICAgICAgICAgICBjb25zdCByZXQgPSBuZXcgdHlwZXMuQVZhbDtcbiAgICAgICAgICAgIGNvbnN0IGNhbGxlZSA9IGMobm9kZS5jYWxsZWUsIGN1clN0YXR1cywgdW5kZWZpbmVkKTtcbiAgICAgICAgICAgIGNvbnN0IGFyZ3MgPSBbXTtcbiAgICAgICAgICAgIGZvciAobGV0IGkgPSAwOyBpIDwgbm9kZS5hcmd1bWVudHMubGVuZ3RoOyBpKyspIHtcbiAgICAgICAgICAgICAgICBhcmdzLnB1c2goYyhub2RlLmFyZ3VtZW50c1tpXSwgY3VyU3RhdHVzLCB1bmRlZmluZWQpKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGNvbnN0IG5ld0RlbHRhID0gY3VyU3RhdHVzLmRlbHRhLmFwcGVuZE9uZShub2RlWydAbGFiZWwnXSk7XG4gICAgICAgICAgICBjb25zdHJhaW50cy5wdXNoKHtDT05TVFJVQ1RPUjogY2FsbGVlLFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgQVJHUzogYXJncyxcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIFJFVDogcmV0LFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgRVhDOiBjdXJTdGF0dXMuZXhjLFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgREVMVEE6IG5ld0RlbHRhfSk7XG4gICAgICAgICAgICBjYWxsZWUucHJvcGFnYXRlKFxuICAgICAgICAgICAgICAgIG5ldyBjc3RyLklzQ3RvcihcbiAgICAgICAgICAgICAgICAgICAgYXJncyxcbiAgICAgICAgICAgICAgICAgICAgcmV0LFxuICAgICAgICAgICAgICAgICAgICBjdXJTdGF0dXMuZXhjLFxuICAgICAgICAgICAgICAgICAgICBuZXdEZWx0YSkpO1xuICAgICAgICAgICAgcmV0dXJuIHJldDtcbiAgICAgICAgfSxcblxuICAgICAgICBBcnJheUV4cHJlc3Npb246IGZ1bmN0aW9uIChub2RlLCBjdXJTdGF0dXMsIGMpIHtcbiAgICAgICAgICAgIGNvbnN0IHJldCA9IG5ldyB0eXBlcy5BVmFsO1xuICAgICAgICAgICAgY29uc3QgYXJyVHlwZSA9IG5ldyB0eXBlcy5BcnJUeXBlKG5ldyB0eXBlcy5BVmFsKHJ0Q1gucHJvdG9zLkFycmF5KSk7XG4gICAgICAgICAgICAvLyBhZGQgbGVuZ3RoIHByb3BlcnR5XG4gICAgICAgICAgICBhcnJUeXBlLmdldFByb3AoJ2xlbmd0aCcpLmFkZFR5cGUodHlwZXMuUHJpbU51bWJlcik7XG5cbiAgICAgICAgICAgIGNvbnN0cmFpbnRzLnB1c2goe1RZUEU6IGFyclR5cGUsIElOQ0xfU0VUOiByZXR9KTtcbiAgICAgICAgICAgIHJldC5hZGRUeXBlKGFyclR5cGUpO1xuXG4gICAgICAgICAgICAvLyBhZGQgYXJyYXkgZWxlbWVudHNcbiAgICAgICAgICAgIGZvciAobGV0IGkgPSAwOyBpIDwgbm9kZS5lbGVtZW50cy5sZW5ndGg7IGkrKykge1xuICAgICAgICAgICAgICAgIGNvbnN0IGVsdEFWYWwgPSBjKG5vZGUuZWxlbWVudHNbaV0sIGN1clN0YXR1cywgdW5kZWZpbmVkKTtcblxuICAgICAgICAgICAgICAgIGNvbnN0IHByb3AgPSBpICsgJyc7XG4gICAgICAgICAgICAgICAgY29uc3RyYWludHMucHVzaCh7T0JKOiByZXQsIFBST1A6IHByb3AsIEFWQUw6IGVsdEFWYWx9KTtcbiAgICAgICAgICAgICAgICBjb25zdHJhaW50cy5wdXNoKHtPQko6IHJldCwgUFJPUDogbnVsbCwgQVZBTDogZWx0QVZhbH0pO1xuICAgICAgICAgICAgICAgIHJldC5wcm9wYWdhdGUobmV3IGNzdHIuV3JpdGVQcm9wKHByb3AsIGVsdEFWYWwpKTtcbiAgICAgICAgICAgICAgICByZXQucHJvcGFnYXRlKG5ldyBjc3RyLldyaXRlUHJvcChudWxsLCBlbHRBVmFsKSk7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICByZXR1cm4gcmV0O1xuICAgICAgICB9LFxuXG4gICAgICAgIE9iamVjdEV4cHJlc3Npb246IGZ1bmN0aW9uIChub2RlLCBjdXJTdGF0dXMsIGMpIHtcbiAgICAgICAgICAgIGNvbnN0IHJldCA9IG5ldyB0eXBlcy5BVmFsO1xuICAgICAgICAgICAgY29uc3Qgb2JqVHlwZSA9IG5ldyB0eXBlcy5PYmpUeXBlKG5ldyB0eXBlcy5BVmFsKHJ0Q1gucHJvdG9zLk9iamVjdCkpO1xuICAgICAgICAgICAgY29uc3RyYWludHMucHVzaCh7VFlQRTogb2JqVHlwZSwgSU5DTF9TRVQ6IHJldH0pO1xuICAgICAgICAgICAgcmV0LmFkZFR5cGUob2JqVHlwZSk7XG5cbiAgICAgICAgICAgIGZvciAobGV0IGkgPSAwOyBpIDwgbm9kZS5wcm9wZXJ0aWVzLmxlbmd0aDsgaSsrKSB7XG4gICAgICAgICAgICAgICAgY29uc3QgcHJvcFBhaXIgPSBub2RlLnByb3BlcnRpZXNbaV07XG4gICAgICAgICAgICAgICAgY29uc3QgcHJvcEtleSA9IHByb3BQYWlyLmtleTtcbiAgICAgICAgICAgICAgICBsZXQgbmFtZTtcbiAgICAgICAgICAgICAgICBjb25zdCBwcm9wRXhwciA9IHByb3BQYWlyLnZhbHVlO1xuXG4gICAgICAgICAgICAgICAgY29uc3QgZmxkQVZhbCA9IGMocHJvcEV4cHIsIGN1clN0YXR1cywgdW5kZWZpbmVkKTtcblxuICAgICAgICAgICAgICAgIGlmIChwcm9wS2V5LnR5cGUgPT09ICdJZGVudGlmaWVyJykge1xuICAgICAgICAgICAgICAgICAgICBuYW1lID0gcHJvcEtleS5uYW1lO1xuICAgICAgICAgICAgICAgIH0gZWxzZSBpZiAodHlwZW9mIHByb3BLZXkudmFsdWUgPT09ICdzdHJpbmcnKSB7XG4gICAgICAgICAgICAgICAgICAgIG5hbWUgPSBwcm9wS2V5LnZhbHVlO1xuICAgICAgICAgICAgICAgIH0gZWxzZSBpZiAodHlwZW9mIHByb3BLZXkudmFsdWUgPT09ICdudW1iZXInKSB7XG4gICAgICAgICAgICAgICAgICAgIC8vIGNvbnZlcnQgbnVtYmVyIHRvIHN0cmluZ1xuICAgICAgICAgICAgICAgICAgICBuYW1lID0gcHJvcEtleS52YWx1ZSArICcnO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICBjb25zdHJhaW50cy5wdXNoKHtPQko6IHJldCwgUFJPUDogbmFtZSwgQVZBTDogZmxkQVZhbH0pO1xuICAgICAgICAgICAgICAgIHJldC5wcm9wYWdhdGUobmV3IGNzdHIuV3JpdGVQcm9wKG5hbWUsIGZsZEFWYWwpKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIHJldHVybiByZXQ7XG4gICAgICAgIH0sXG5cbiAgICAgICAgRnVuY3Rpb25FeHByZXNzaW9uOiBmdW5jdGlvbiAobm9kZSwgY3VyU3RhdHVzLCBjKSB7XG4gICAgICAgICAgICBpZiAoIW5vZGUuZm5JbnN0YW5jZXMpIHtcbiAgICAgICAgICAgICAgICBub2RlLmZuSW5zdGFuY2VzID0gW107XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBsZXQgZm5JbnN0YW5jZSA9IG51bGw7XG4gICAgICAgICAgICBub2RlLmZuSW5zdGFuY2VzLmZvckVhY2goZnVuY3Rpb24gKGZuVHlwZSkge1xuICAgICAgICAgICAgICAgIGlmIChmblR5cGUuc2MgPT09IGN1clN0YXR1cy5zYykge1xuICAgICAgICAgICAgICAgICAgICBmbkluc3RhbmNlID0gZm5UeXBlO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgIH0pO1xuICAgICAgICAgICAgaWYgKCFmbkluc3RhbmNlKSB7XG4gICAgICAgICAgICAgICAgZm5JbnN0YW5jZVxuICAgICAgICAgICAgICAgICAgICA9IG5ldyB0eXBlcy5GblR5cGUobmV3IHR5cGVzLkFWYWwocnRDWC5wcm90b3MuRnVuY3Rpb24pLFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgJ1thbm9ueW1vdXMgZnVuY3Rpb25dJyxcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIG5vZGUuYm9keVsnQGJsb2NrJ10uZ2V0UGFyYW1WYXJOYW1lcygpLFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgY3VyU3RhdHVzLnNjLFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgbm9kZSxcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIHJ0Q1gucHJvdG9zLk9iamVjdCk7XG4gICAgICAgICAgICAgICAgbm9kZS5mbkluc3RhbmNlcy5wdXNoKGZuSW5zdGFuY2UpO1xuICAgICAgICAgICAgICAgIGNvbnN0IHByb3RvdHlwZU9iamVjdCA9XG4gICAgICAgICAgICAgICAgICAgIG5ldyB0eXBlcy5PYmpUeXBlKG5ldyB0eXBlcy5BVmFsKHJ0Q1gucHJvdG9zLk9iamVjdCksXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICc/LnByb3RvdHlwZScpO1xuICAgICAgICAgICAgICAgIC8vIEZvciAucHJvdG90eXBlXG4gICAgICAgICAgICAgICAgY29uc3QgcHJvdG90eXBlUHJvcCA9IGZuSW5zdGFuY2UuZ2V0UHJvcCgncHJvdG90eXBlJyk7XG4gICAgICAgICAgICAgICAgY29uc3RyYWludHMucHVzaCh7VFlQRTogcHJvdG90eXBlT2JqZWN0LFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIElOQ0xfU0VUOiBwcm90b3R5cGVQcm9wfSk7XG4gICAgICAgICAgICAgICAgcHJvdG90eXBlUHJvcC5hZGRUeXBlKHByb3RvdHlwZU9iamVjdCk7XG4gICAgICAgICAgICAgICAgLy8gRm9yIC5wcm90b3R5cGUuY29uc3RydWN0b3JcbiAgICAgICAgICAgICAgICBjb25zdCBjb25zdHJ1Y3RvclByb3AgPSBwcm90b3R5cGVPYmplY3QuZ2V0UHJvcCgnY29uc3RydWN0b3InKTtcbiAgICAgICAgICAgICAgICBjb25zdHJhaW50cy5wdXNoKHtUWVBFOiBmbkluc3RhbmNlLFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIElOQ0xfU0VUOiBjb25zdHJ1Y3RvclByb3B9KTtcbiAgICAgICAgICAgICAgICBjb25zdHJ1Y3RvclByb3AuYWRkVHlwZShmbkluc3RhbmNlKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGNvbnN0IHJldCA9IG5ldyB0eXBlcy5BVmFsO1xuICAgICAgICAgICAgY29uc3RyYWludHMucHVzaCh7VFlQRTogZm5JbnN0YW5jZSxcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIElOQ0xfU0VUOiByZXR9KTtcbiAgICAgICAgICAgIHJldC5hZGRUeXBlKGZuSW5zdGFuY2UpO1xuICAgICAgICAgICAgcmV0dXJuIHJldDtcbiAgICAgICAgfSxcblxuICAgICAgICBGdW5jdGlvbkRlY2xhcmF0aW9uOiBmdW5jdGlvbiAobm9kZSwgY3VyU3RhdHVzLCBjKSB7XG4gICAgICAgICAgICAvLyBEcm9wIGluaXRpYWwgY2F0Y2ggc2NvcGVzXG4gICAgICAgICAgICBjb25zdCBzYzAgPSBjdXJTdGF0dXMuc2MucmVtb3ZlSW5pdGlhbENhdGNoQmxvY2tzKCk7XG4gICAgICAgICAgICBpZiAoIW5vZGUuZm5JbnN0YW5jZXMpIHtcbiAgICAgICAgICAgICAgICBub2RlLmZuSW5zdGFuY2VzID0gW107XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBsZXQgZm5JbnN0YW5jZSA9IG51bGw7XG4gICAgICAgICAgICBub2RlLmZuSW5zdGFuY2VzLmZvckVhY2goZnVuY3Rpb24gKGZuVHlwZSkge1xuICAgICAgICAgICAgICAgIGlmIChmblR5cGUuc2MgPT09IHNjMCkge1xuICAgICAgICAgICAgICAgICAgICBmbkluc3RhbmNlID0gZm5UeXBlO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgIH0pO1xuICAgICAgICAgICAgaWYgKCFmbkluc3RhbmNlKSB7XG4gICAgICAgICAgICAgICAgZm5JbnN0YW5jZVxuICAgICAgICAgICAgICAgICAgICA9IG5ldyB0eXBlcy5GblR5cGUobmV3IHR5cGVzLkFWYWwocnRDWC5wcm90b3MuRnVuY3Rpb24pLFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgbm9kZS5pZC5uYW1lLFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgbm9kZS5ib2R5WydAYmxvY2snXS5nZXRQYXJhbVZhck5hbWVzKCksXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBzYzAsXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBub2RlLFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgcnRDWC5wcm90b3MuT2JqZWN0KTtcbiAgICAgICAgICAgICAgICBub2RlLmZuSW5zdGFuY2VzLnB1c2goZm5JbnN0YW5jZSk7XG4gICAgICAgICAgICAgICAgLy8gZm9yIGVhY2ggZm5JbnN0YW5jZSwgYXNzaWduIG9uZSBwcm90b3R5cGUgb2JqZWN0XG4gICAgICAgICAgICAgICAgY29uc3QgcHJvdG90eXBlT2JqZWN0ID1cbiAgICAgICAgICAgICAgICAgICAgbmV3IHR5cGVzLk9ialR5cGUobmV3IHR5cGVzLkFWYWwocnRDWC5wcm90b3MuT2JqZWN0KSxcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgbm9kZS5pZC5uYW1lICsgJy5wcm90b3R5cGUnKTtcbiAgICAgICAgICAgICAgICAvLyBGb3IgLnByb3RvdHlwZVxuICAgICAgICAgICAgICAgIGNvbnN0IHByb3RvdHlwZVByb3AgPSBmbkluc3RhbmNlLmdldFByb3AoJ3Byb3RvdHlwZScpO1xuICAgICAgICAgICAgICAgIGNvbnN0cmFpbnRzLnB1c2goe1RZUEU6IHByb3RvdHlwZU9iamVjdCxcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBJTkNMX1NFVDogcHJvdG90eXBlUHJvcH0pO1xuICAgICAgICAgICAgICAgIHByb3RvdHlwZVByb3AuYWRkVHlwZShwcm90b3R5cGVPYmplY3QpO1xuICAgICAgICAgICAgICAgIC8vIEZvciAucHJvdG90eXBlLmNvbnN0cnVjdG9yXG4gICAgICAgICAgICAgICAgY29uc3QgY29uc3RydWN0b3JQcm9wID0gcHJvdG90eXBlT2JqZWN0LmdldFByb3AoJ2NvbnN0cnVjdG9yJyk7XG4gICAgICAgICAgICAgICAgY29uc3RyYWludHMucHVzaCh7VFlQRTogZm5JbnN0YW5jZSxcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBJTkNMX1NFVDogY29uc3RydWN0b3JQcm9wfSk7XG4gICAgICAgICAgICAgICAgY29uc3RydWN0b3JQcm9wLmFkZFR5cGUoZm5JbnN0YW5jZSk7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBjb25zdCBsaHNBVmFsID0gc2MwLmdldEFWYWxPZihub2RlLmlkLm5hbWUpO1xuXG4gICAgICAgICAgICBjb25zdHJhaW50cy5wdXNoKHtUWVBFOiBmbkluc3RhbmNlLFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgSU5DTF9TRVQ6IGxoc0FWYWx9KTtcbiAgICAgICAgICAgIGxoc0FWYWwuYWRkVHlwZShmbkluc3RhbmNlKTtcbiAgICAgICAgICAgIC8vIG5vdGhpbmcgdG8gcmV0dXJuXG4gICAgICAgICAgICByZXR1cm4gdHlwZXMuQVZhbE51bGw7XG4gICAgICAgIH0sXG5cbiAgICAgICAgU2VxdWVuY2VFeHByZXNzaW9uOiBmdW5jdGlvbiAobm9kZSwgY3VyU3RhdHVzLCBjKSB7XG4gICAgICAgICAgICBjb25zdCBsYXN0SW5kZXggPSBub2RlLmV4cHJlc3Npb25zLmxlbmd0aCAtIDE7XG4gICAgICAgICAgICBmb3IgKGxldCBpID0gMDsgaSA8IGxhc3RJbmRleDsgaSsrKSB7XG4gICAgICAgICAgICAgICAgYyhub2RlLmV4cHJlc3Npb25zW2ldLCBjdXJTdGF0dXMsIHVuZGVmaW5lZCk7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICByZXR1cm4gYyhub2RlLmV4cHJlc3Npb25zW2xhc3RJbmRleF0sIGN1clN0YXR1cywgdW5kZWZpbmVkKTtcbiAgICAgICAgfSxcblxuICAgICAgICBVbmFyeUV4cHJlc3Npb246IGZ1bmN0aW9uIChub2RlLCBjdXJTdGF0dXMsIGMpIHtcbiAgICAgICAgICAgIGMobm9kZS5hcmd1bWVudCwgY3VyU3RhdHVzLCB1bmRlZmluZWQpO1xuICAgICAgICAgICAgY29uc3QgcmVzID0gbmV3IHR5cGVzLkFWYWw7XG4gICAgICAgICAgICBjb25zdCB0eXBlID0gdW5vcFJlc3VsdFR5cGUobm9kZS5vcGVyYXRvcik7XG4gICAgICAgICAgICBpZiAodHlwZSkge1xuICAgICAgICAgICAgICAgIGNvbnN0cmFpbnRzLnB1c2goe1RZUEU6IHR5cGUsXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgSU5DTF9TRVQ6IHJlc30pO1xuICAgICAgICAgICAgICAgIHJlcy5hZGRUeXBlKHR5cGUpO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgcmV0dXJuIHJlcztcbiAgICAgICAgfSxcblxuICAgICAgICBVcGRhdGVFeHByZXNzaW9uOiBmdW5jdGlvbiAobm9kZSwgY3VyU3RhdHVzLCBjKSB7XG4gICAgICAgICAgICBjKG5vZGUuYXJndW1lbnQsIGN1clN0YXR1cywgdW5kZWZpbmVkKTtcbiAgICAgICAgICAgIGNvbnN0IHJlcyA9IG5ldyB0eXBlcy5BVmFsO1xuICAgICAgICAgICAgY29uc3RyYWludHMucHVzaCh7VFlQRTogdHlwZXMuUHJpbU51bWJlcixcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIElOQ0xfU0VUOiByZXN9KTtcbiAgICAgICAgICAgIHJlcy5hZGRUeXBlKHR5cGVzLlByaW1OdW1iZXIpO1xuICAgICAgICAgICAgLy8gV2UgaWdub3JlIHRoZSBlZmZlY3Qgb2YgdXBkYXRpbmcgdG8gbnVtYmVyIHR5cGVcbiAgICAgICAgICAgIHJldHVybiByZXM7XG4gICAgICAgIH0sXG5cbiAgICAgICAgQmluYXJ5RXhwcmVzc2lvbjogZnVuY3Rpb24gKG5vZGUsIGN1clN0YXR1cywgYykge1xuICAgICAgICAgICAgY29uc3QgbE9wcmQgPSBjKG5vZGUubGVmdCwgY3VyU3RhdHVzLCB1bmRlZmluZWQpO1xuICAgICAgICAgICAgY29uc3Qgck9wcmQgPSBjKG5vZGUucmlnaHQsIGN1clN0YXR1cywgdW5kZWZpbmVkKTtcbiAgICAgICAgICAgIGNvbnN0IHJlcyA9IG5ldyB0eXBlcy5BVmFsO1xuXG4gICAgICAgICAgICBpZiAobm9kZS5vcGVyYXRvciA9PSAnKycpIHtcbiAgICAgICAgICAgICAgICBjb25zdHJhaW50cy5wdXNoKHtBRERfT1BSRDE6IGxPcHJkLFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIEFERF9PUFJEMjogck9wcmQsXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgUkVTVUxUOiByZXMgfSk7XG4gICAgICAgICAgICAgICAgbE9wcmQucHJvcGFnYXRlKG5ldyBjc3RyLklzQWRkZWQock9wcmQsIHJlcykpO1xuICAgICAgICAgICAgICAgIHJPcHJkLnByb3BhZ2F0ZShuZXcgY3N0ci5Jc0FkZGVkKGxPcHJkLCByZXMpKTtcbiAgICAgICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgICAgICAgaWYgKGJpbm9wSXNCb29sZWFuKG5vZGUub3BlcmF0b3IpKSB7XG4gICAgICAgICAgICAgICAgICAgIGNvbnN0cmFpbnRzLnB1c2goe1RZUEU6IHR5cGVzLlByaW1Cb29sZWFuLFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBJTkNMX1NFVDogcmVzfSk7XG4gICAgICAgICAgICAgICAgICAgIHJlcy5hZGRUeXBlKHR5cGVzLlByaW1Cb29sZWFuKTtcbiAgICAgICAgICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgICAgICAgICAgICBjb25zdHJhaW50cy5wdXNoKHtUWVBFOiB0eXBlcy5QcmltTnVtYmVyLFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBJTkNMX1NFVDogcmVzfSk7XG4gICAgICAgICAgICAgICAgICAgIHJlcy5hZGRUeXBlKHR5cGVzLlByaW1OdW1iZXIpO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIHJldHVybiByZXM7XG4gICAgICAgIH0sXG5cbiAgICAgICAgVHJ5U3RhdGVtZW50OiBmdW5jdGlvbiAobm9kZSwgY3VyU3RhdHVzLCBjKSB7XG4gICAgICAgICAgICAvLyBjb25zdHJ1Y3Qgc2NvcGUgY2hhaW4gZm9yIGNhdGNoIGJsb2NrXG4gICAgICAgICAgICBjb25zdCBjYXRjaEJsb2NrU0MgPVxuICAgICAgICAgICAgICAgIG5vZGUuaGFuZGxlci5ib2R5WydAYmxvY2snXVxuICAgICAgICAgICAgICAgIC5nZXRTY29wZUluc3RhbmNlKGN1clN0YXR1cy5zYywgY3VyU3RhdHVzLmRlbHRhKTtcbiAgICAgICAgICAgIC8vIGdldCB0aGUgQVZhbCBmb3IgZXhjZXB0aW9uIHBhcmFtZXRlclxuICAgICAgICAgICAgY29uc3QgZXhjQVZhbCA9IGNhdGNoQmxvY2tTQy5nZXRBVmFsT2Yobm9kZS5oYW5kbGVyLnBhcmFtLm5hbWUpO1xuXG4gICAgICAgICAgICAvLyBmb3IgdHJ5IGJsb2NrXG4gICAgICAgICAgICBjb25zdCB0cnlTdGF0dXMgPSBjaGFuZ2VkU3RhdHVzKGN1clN0YXR1cywgJ2V4YycsIGV4Y0FWYWwpO1xuICAgICAgICAgICAgYyhub2RlLmJsb2NrLCB0cnlTdGF0dXMsIHVuZGVmaW5lZCk7XG5cbiAgICAgICAgICAgIC8vIGZvciBjYXRjaCBibG9ja1xuICAgICAgICAgICAgY29uc3QgY2F0Y2hTdGF0dXMgPSBjaGFuZ2VkU3RhdHVzKGN1clN0YXR1cywgJ3NjJywgY2F0Y2hCbG9ja1NDKTtcbiAgICAgICAgICAgIGMobm9kZS5oYW5kbGVyLmJvZHksIGNhdGNoU3RhdHVzLCB1bmRlZmluZWQpO1xuXG4gICAgICAgICAgICAvLyBmb3IgZmluYWxseSBibG9ja1xuICAgICAgICAgICAgaWYgKG5vZGUuZmluYWxpemVyICE9PSBudWxsKVxuICAgICAgICAgICAgICAgIGMobm9kZS5maW5hbGl6ZXIsIGN1clN0YXR1cywgdW5kZWZpbmVkKTtcbiAgICAgICAgfSxcblxuICAgICAgICBUaHJvd1N0YXRlbWVudDogZnVuY3Rpb24gKG5vZGUsIGN1clN0YXR1cywgYykge1xuICAgICAgICAgICAgY29uc3QgdGhyID0gYyhub2RlLmFyZ3VtZW50LCBjdXJTdGF0dXMsIHVuZGVmaW5lZCk7XG4gICAgICAgICAgICBjb25zdHJhaW50cy5wdXNoKHtGUk9NOiB0aHIsXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICBUTzogY3VyU3RhdHVzLmV4Y30pO1xuICAgICAgICAgICAgdGhyLnByb3BhZ2F0ZShjdXJTdGF0dXMuZXhjKTtcbiAgICAgICAgfSxcblxuICAgICAgICBDYWxsRXhwcmVzc2lvbjogZnVuY3Rpb24gKG5vZGUsIGN1clN0YXR1cywgYykge1xuICAgICAgICAgICAgY29uc3QgcmVzQVZhbCA9IG5ldyB0eXBlcy5BVmFsO1xuICAgICAgICAgICAgY29uc3QgYXJnQVZhbHMgPSBbXTtcblxuICAgICAgICAgICAgLy8gZ2V0IEFWYWxzIGZvciBlYWNoIGFyZ3VtZW50c1xuICAgICAgICAgICAgZm9yIChsZXQgaSA9IDA7IGkgPCBub2RlLmFyZ3VtZW50cy5sZW5ndGg7IGkrKykge1xuICAgICAgICAgICAgICAgIGFyZ0FWYWxzLnB1c2goXG4gICAgICAgICAgICAgICAgICAgIGMobm9kZS5hcmd1bWVudHNbaV0sIGN1clN0YXR1cywgdW5kZWZpbmVkKSk7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICAvLyBhcHBlbmQgY3VycmVudCBjYWxsIHNpdGUgdG8gdGhlIGNvbnRleHRcbiAgICAgICAgICAgIGNvbnN0IG5ld0RlbHRhID0gY3VyU3RhdHVzLmRlbHRhLmFwcGVuZE9uZShub2RlWydAbGFiZWwnXSk7XG5cbiAgICAgICAgICAgIGlmIChub2RlLmNhbGxlZS50eXBlID09PSAnTWVtYmVyRXhwcmVzc2lvbicpIHtcbiAgICAgICAgICAgICAgICAvLyBtZXRob2QgY2FsbFxuICAgICAgICAgICAgICAgIC8vIHZhciByZWN2ID0gYyhub2RlLmNhbGxlZS5vYmplY3QsIGN1clN0YXR1cywgdW5kZWZpbmVkKTtcbiAgICAgICAgICAgICAgICAvLyB2YXIgbWV0aG9kTmFtZSA9IGltbWVkUHJvcChub2RlLmNhbGxlZSk7XG4gICAgICAgICAgICAgICAgLy8gY29uc3RyYWludHMucHVzaCh7XG4gICAgICAgICAgICAgICAgLy8gICBSRUNWOiByZWN2LFxuICAgICAgICAgICAgICAgIC8vICAgUFJPUE5BTUU6IG1ldGhvZE5hbWUsXG4gICAgICAgICAgICAgICAgLy8gICBQQVJBTVM6IGFyZ0FWYWxzLFxuICAgICAgICAgICAgICAgIC8vICAgUkVUOiByZXNBVmFsLFxuICAgICAgICAgICAgICAgIC8vICAgRVhDOiBjdXJTdGF0dXMuZXhjLFxuICAgICAgICAgICAgICAgIC8vICAgREVMVEE6IG5ld0RlbHRhXG4gICAgICAgICAgICAgICAgLy8gfSk7XG4gICAgICAgICAgICAgICAgY29uc3QgcmVjdkFuZFJldCA9IHJlYWRNZW1iZXIobm9kZS5jYWxsZWUsIGN1clN0YXR1cywgYyk7XG4gICAgICAgICAgICAgICAgcmVjdkFuZFJldFsxXS5wcm9wYWdhdGUoXG4gICAgICAgICAgICAgICAgICAgIG5ldyBjc3RyLklzQ2FsbGVlKFxuICAgICAgICAgICAgICAgICAgICAgICAgcmVjdkFuZFJldFswXSxcbiAgICAgICAgICAgICAgICAgICAgICAgIGFyZ0FWYWxzLFxuICAgICAgICAgICAgICAgICAgICAgICAgcmVzQVZhbCxcbiAgICAgICAgICAgICAgICAgICAgICAgIGN1clN0YXR1cy5leGMsXG4gICAgICAgICAgICAgICAgICAgICAgICBuZXdEZWx0YSkpO1xuICAgICAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICAgICAgICAvLyBub3JtYWwgZnVuY3Rpb24gY2FsbFxuICAgICAgICAgICAgICAgIGNvbnN0IGNhbGxlZUFWYWwgPSBjKG5vZGUuY2FsbGVlLCBjdXJTdGF0dXMsIHVuZGVmaW5lZCk7XG4gICAgICAgICAgICAgICAgLy8gY2FsbGVl7J2YIHJldHVybuydhCBjYWxsIGV4cHJlc3Npb27snLzroZxcbiAgICAgICAgICAgICAgICAvLyBjYWxsZWXsnZggZXhjZXB0aW9u7J2EIO2YuOy2nCDsuKHsnZggZXhjZXB0aW9u7JeQIOyghOuLrO2VtOyVvFxuICAgICAgICAgICAgICAgIGNvbnN0cmFpbnRzLnB1c2goe1xuICAgICAgICAgICAgICAgICAgICBDQUxMRUU6IGNhbGxlZUFWYWwsXG4gICAgICAgICAgICAgICAgICAgIFNFTEY6IHJ0Q1guZ2xvYmFsT2JqZWN0LFxuICAgICAgICAgICAgICAgICAgICBQQVJBTVM6IGFyZ0FWYWxzLFxuICAgICAgICAgICAgICAgICAgICBSRVQ6IHJlc0FWYWwsXG4gICAgICAgICAgICAgICAgICAgIEVYQzogY3VyU3RhdHVzLmV4YyxcbiAgICAgICAgICAgICAgICAgICAgREVMVEE6IG5ld0RlbHRhXG4gICAgICAgICAgICAgICAgfSk7XG4gICAgICAgICAgICAgICAgY2FsbGVlQVZhbC5wcm9wYWdhdGUoXG4gICAgICAgICAgICAgICAgICAgIG5ldyBjc3RyLklzQ2FsbGVlKFxuICAgICAgICAgICAgICAgICAgICAgICAgbmV3IHR5cGVzLkFWYWwocnRDWC5nbG9iYWxPYmplY3QpLFxuICAgICAgICAgICAgICAgICAgICAgICAgYXJnQVZhbHMsXG4gICAgICAgICAgICAgICAgICAgICAgICByZXNBVmFsLFxuICAgICAgICAgICAgICAgICAgICAgICAgY3VyU3RhdHVzLmV4YyxcbiAgICAgICAgICAgICAgICAgICAgICAgIG5ld0RlbHRhKSk7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICByZXR1cm4gcmVzQVZhbDtcbiAgICAgICAgfSxcblxuICAgICAgICBNZW1iZXJFeHByZXNzaW9uOiBmdW5jdGlvbiAobm9kZSwgY3VyU3RhdHVzLCBjKSB7XG4gICAgICAgICAgICBjb25zdCByZWN2QW5kUmV0ID0gcmVhZE1lbWJlcihub2RlLCBjdXJTdGF0dXMsIGMpO1xuICAgICAgICAgICAgcmV0dXJuIHJlY3ZBbmRSZXRbMV07XG4gICAgICAgIH0sXG5cbiAgICAgICAgUmV0dXJuU3RhdGVtZW50OiBmdW5jdGlvbiAobm9kZSwgY3VyU3RhdHVzLCBjKSB7XG4gICAgICAgICAgICBpZiAoIW5vZGUuYXJndW1lbnQpIHJldHVybjtcbiAgICAgICAgICAgIGNvbnN0IHJldCA9IGMobm9kZS5hcmd1bWVudCwgY3VyU3RhdHVzLCB1bmRlZmluZWQpO1xuICAgICAgICAgICAgY29uc3RyYWludHMucHVzaCh7RlJPTTogcmV0LFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgVE86IGN1clN0YXR1cy5yZXR9KTtcbiAgICAgICAgICAgIHJldC5wcm9wYWdhdGUoY3VyU3RhdHVzLnJldCk7XG4gICAgICAgIH1cbiAgICB9KTtcblxuICAgIHJlY3Vyc2l2ZVdpdGhSZXR1cm4oYXN0LCBpbml0U3RhdHVzLCBjb25zdHJhaW50R2VuZXJhdG9yKTtcblxuICAgIC8vIFdlIGFjdHVhbGx5IGFkZGVkIGNvbnN0cmFpbnRzXG4gICAgcmV0dXJuIHRydWU7XG59XG5cbmZ1bmN0aW9uIHJlY3Vyc2l2ZVdpdGhSZXR1cm4obm9kZSwgc3RhdGUsIHZpc2l0b3IpIHtcbiAgICBmdW5jdGlvbiBjKG5vZGUsIHN0LCBvdmVycmlkZSkge1xuICAgICAgICByZXR1cm4gdmlzaXRvcltvdmVycmlkZSB8fCBub2RlLnR5cGVdKG5vZGUsIHN0LCBjKTtcbiAgICB9XG4gICAgcmV0dXJuIGMobm9kZSwgc3RhdGUpO1xufVxuXG5leHBvcnRzLmNvbnN0cmFpbnRzID0gY29uc3RyYWludHM7XG5leHBvcnRzLmFkZENvbnN0cmFpbnRzID0gYWRkQ29uc3RyYWludHM7XG5leHBvcnRzLmNsZWFyQ29uc3RyYWludHMgPSBjbGVhckNvbnN0cmFpbnRzO1xuIiwiJ3VzZSBzdHJpY3QnO1xuXG5jb25zdCB0eXBlcyA9IHJlcXVpcmUoJy4uL2RvbWFpbnMvdHlwZXMnKTtcbmNvbnN0IHN0YXR1cyA9IHJlcXVpcmUoJy4uL2RvbWFpbnMvc3RhdHVzJyk7XG5jb25zdCBjR2VuID0gcmVxdWlyZSgnLi9jR2VuJyk7XG5cbmZ1bmN0aW9uIENTVFIoKSB7fVxuQ1NUUi5wcm90b3R5cGUgPSBPYmplY3QuY3JlYXRlKG51bGwpO1xuQ1NUUi5wcm90b3R5cGUuZXF1YWxzID0gZnVuY3Rpb24gKG90aGVyKSB7XG4gICAgcmV0dXJuIHRoaXMgPT09IG90aGVyO1xufTtcblxuZnVuY3Rpb24gUmVhZFByb3AocHJvcCwgdG8pIHtcbiAgICB0aGlzLnByb3AgPSBwcm9wO1xuICAgIHRoaXMudG8gPSB0bztcbn1cblJlYWRQcm9wLnByb3RvdHlwZSA9IE9iamVjdC5jcmVhdGUoQ1NUUi5wcm90b3R5cGUpO1xuUmVhZFByb3AucHJvdG90eXBlLmFkZFR5cGUgPSBmdW5jdGlvbiAob2JqKSB7XG4gICAgaWYgKCEob2JqIGluc3RhbmNlb2YgKHR5cGVzLk9ialR5cGUpKSkgcmV0dXJuO1xuICAgIC8vIHdoZW4gb2JqIGlzIE9ialR5cGUsXG4gICAgY29uc3Qgb3duUHJvcCA9IG9iai5nZXRQcm9wKHRoaXMucHJvcCwgdHJ1ZSk7XG4gICAgaWYgKG93blByb3ApIHtcbiAgICAgICAgLy8gd2hlbiB0aGUgb2JqZWN0IGhhcyB0aGUgcHJvcCxcbiAgICAgICAgb3duUHJvcC5wcm9wYWdhdGUodGhpcy50byk7XG4gICAgfSBlbHNlIGlmIChvYmouZ2V0UHJvcCgnX19wcm90b19fJywgdHJ1ZSkpIHtcbiAgICAgICAgLy8gdXNlIHByb3RvdHlwZSBjaGFpblxuICAgICAgICBvYmouZ2V0UHJvcCgnX19wcm90b19fJylcbiAgICAgICAgICAucHJvcGFnYXRlKG5ldyBSZWFkUHJvcCh0aGlzLnByb3AsIHRoaXMudG8pKTtcbiAgICB9XG59O1xuUmVhZFByb3AucHJvdG90eXBlLmVxdWFscyA9IGZ1bmN0aW9uIChvdGhlcikge1xuICAgIGlmICghKG90aGVyIGluc3RhbmNlb2YgUmVhZFByb3ApKSByZXR1cm4gZmFsc2U7XG4gICAgcmV0dXJuIHRoaXMucHJvcCA9PT0gb3RoZXIucHJvcFxuICAgICAgICAmJiB0aGlzLnRvLmVxdWFscyhvdGhlci50byk7XG59O1xuXG5mdW5jdGlvbiBXcml0ZVByb3AocHJvcCwgZnJvbSkge1xuICAgIHRoaXMucHJvcCA9IHByb3A7XG4gICAgdGhpcy5mcm9tID0gZnJvbTtcbn1cbldyaXRlUHJvcC5wcm90b3R5cGUgPSBPYmplY3QuY3JlYXRlKENTVFIucHJvdG90eXBlKTtcbldyaXRlUHJvcC5wcm90b3R5cGUuYWRkVHlwZSA9IGZ1bmN0aW9uIChvYmopIHtcbiAgICBpZiAoIShvYmogaW5zdGFuY2VvZiAodHlwZXMuT2JqVHlwZSkpKSByZXR1cm47XG4gICAgY29uc3Qgb3duUHJvcCA9IG9iai5nZXRQcm9wKHRoaXMucHJvcCk7XG4gICAgdGhpcy5mcm9tLnByb3BhZ2F0ZShvd25Qcm9wKTtcbn07XG5cbmZ1bmN0aW9uIElzQWRkZWQob3RoZXIsIHRhcmdldCkge1xuICAgIHRoaXMub3RoZXIgPSBvdGhlcjtcbiAgICB0aGlzLnRhcmdldCA9IHRhcmdldDtcbn1cbklzQWRkZWQucHJvdG90eXBlID0gT2JqZWN0LmNyZWF0ZShDU1RSLnByb3RvdHlwZSk7XG5Jc0FkZGVkLnByb3RvdHlwZS5hZGRUeXBlID0gZnVuY3Rpb24gKHR5cGUpIHtcbiAgICBpZiAoKHR5cGUgPT09IHR5cGVzLlByaW1OdW1iZXIgXG4gICAgICAgICB8fCB0eXBlID09PSB0eXBlcy5QcmltQm9vbGVhbilcbiAgICAgJiYgKHRoaXMub3RoZXIuaGFzVHlwZSh0eXBlcy5QcmltTnVtYmVyKSBcbiAgICAgICAgIHx8IHRoaXMub3RoZXIuaGFzVHlwZSh0eXBlcy5QcmltQm9vbGVhbikpKSB7XG4gICAgICAgIHRoaXMudGFyZ2V0LmFkZFR5cGUodHlwZXMuUHJpbU51bWJlcik7XG4gICAgfVxuICAgIGlmICh0eXBlID09PSB0eXBlcy5QcmltU3RyaW5nXG4gICAgICYmICF0aGlzLm90aGVyLmlzRW1wdHkoKSkge1xuICAgICAgICAgdGhpcy50YXJnZXQuYWRkVHlwZSh0eXBlcy5QcmltU3RyaW5nKTtcbiAgICB9XG59O1xuXG5mdW5jdGlvbiBJc0NhbGxlZShzZWxmLCBhcmdzLCByZXQsIGV4YywgZGVsdGEpIHtcbiAgICB0aGlzLnNlbGYgPSBzZWxmO1xuICAgIHRoaXMuYXJncyA9IGFyZ3M7XG4gICAgdGhpcy5yZXQgPSByZXQ7XG4gICAgdGhpcy5leGMgPSBleGM7XG4gICAgdGhpcy5kZWx0YSA9IGRlbHRhO1xufVxuSXNDYWxsZWUucHJvdG90eXBlID0gT2JqZWN0LmNyZWF0ZShDU1RSLnByb3RvdHlwZSk7XG5Jc0NhbGxlZS5wcm90b3R5cGUuYWRkVHlwZSA9IGZ1bmN0aW9uIChmKSB7XG4gICAgaWYgKCEoZiBpbnN0YW5jZW9mICh0eXBlcy5GblR5cGUpKSkgcmV0dXJuO1xuICAgIGNvbnN0IGZ1bkVudiA9IGYuZ2V0RnVuRW52KHRoaXMuZGVsdGEpO1xuICAgIGNvbnN0IG5ld1NDID0gZi5vcmlnaW5Ob2RlLmJvZHlbJ0BibG9jayddLmdldFNjb3BlSW5zdGFuY2UoZi5zYywgdGhpcy5kZWx0YSk7XG4gICAgY29uc3QgZnVuU3RhdHVzXG4gICAgICAgID0gbmV3IHN0YXR1cy5TdGF0dXMoZnVuRW52WzBdLCBmdW5FbnZbMV0sIGZ1bkVudlsyXSwgXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgdGhpcy5kZWx0YSwgbmV3U0MpO1xuICAgIC8vIHBhc3MgdGhpcyBvYmplY3RcbiAgICB0aGlzLnNlbGYucHJvcGFnYXRlKGZ1bkVudlswXSk7XG5cbiAgICBjb25zdCBtaW5MZW4gPSBNYXRoLm1pbih0aGlzLmFyZ3MubGVuZ3RoLCBmLnBhcmFtTmFtZXMubGVuZ3RoKTtcbiAgICBmb3IgKGxldCBpID0gMDsgaSA8IG1pbkxlbjsgaSsrKSB7XG4gICAgICAgIHRoaXMuYXJnc1tpXS5wcm9wYWdhdGUobmV3U0MuZ2V0QVZhbE9mKGYucGFyYW1OYW1lc1tpXSkpO1xuICAgIH1cblxuICAgIC8vIGZvciBhcmd1bWVudHMgb2JqZWN0XG4gICAgaWYgKGYub3JpZ2luTm9kZS5ib2R5WydAYmxvY2snXS51c2VBcmd1bWVudHNPYmplY3QpIHtcbiAgICAgICAgY29uc3QgYXJnT2JqID0gZi5nZXRBcmd1bWVudHNPYmplY3QodGhpcy5kZWx0YSk7XG4gICAgICAgIG5ld1NDLmdldEFWYWxPZignYXJndW1lbnRzJykuYWRkVHlwZShhcmdPYmopO1xuICAgICAgICBmb3IgKGxldCBpID0gMDsgaSA8IHRoaXMuYXJncy5sZW5ndGg7IGkrKykge1xuICAgICAgICAgICAgdGhpcy5hcmdzW2ldLnByb3BhZ2F0ZShhcmdPYmouZ2V0UHJvcChpICsgJycpKTtcbiAgICAgICAgICAgIHRoaXMuYXJnc1tpXS5wcm9wYWdhdGUoYXJnT2JqLmdldFByb3AobnVsbCkpO1xuICAgICAgICB9XG4gICAgICAgIGFyZ09iai5nZXRQcm9wKCdjYWxsZWUnKS5hZGRUeXBlKGYpO1xuICAgICAgICBhcmdPYmouZ2V0UHJvcCgnbGVuZ3RoJykuYWRkVHlwZSh0eXBlcy5QcmltTnVtYmVyKTtcbiAgICB9XG5cbiAgICAvLyBjb25zdHJhaW50IGdlbmVyYXRpb24gZm9yIHRoZSBmdW5jdGlvbiBib2R5XG4gICAgY0dlbi5hZGRDb25zdHJhaW50cyhmLm9yaWdpbk5vZGUuYm9keSwgZnVuU3RhdHVzKTtcblxuICAgIC8vIGdldCByZXR1cm4gXG4gICAgZnVuRW52WzFdLnByb3BhZ2F0ZSh0aGlzLnJldCk7XG4gICAgLy8gZ2V0IGV4Y2VwdGlvblxuICAgIGZ1bkVudlsyXS5wcm9wYWdhdGUodGhpcy5leGMpO1xufTtcblxuZnVuY3Rpb24gSXNDdG9yKGFyZ3MsIHJldCwgZXhjLCBkZWx0YSkge1xuICAgIHRoaXMuYXJncyA9IGFyZ3M7XG4gICAgdGhpcy5yZXQgPSByZXQ7XG4gICAgdGhpcy5leGMgPSBleGM7XG4gICAgdGhpcy5kZWx0YSA9IGRlbHRhO1xufVxuSXNDdG9yLnByb3RvdHlwZSA9IE9iamVjdC5jcmVhdGUoQ1NUUi5wcm90b3R5cGUpO1xuSXNDdG9yLnByb3RvdHlwZS5hZGRUeXBlID0gZnVuY3Rpb24gKGYpIHtcbiAgICBpZiAoIShmIGluc3RhbmNlb2YgKHR5cGVzLkZuVHlwZSkpKSByZXR1cm47XG4gICAgY29uc3QgZnVuRW52ID0gZi5nZXRGdW5FbnYodGhpcy5kZWx0YSk7XG4gICAgY29uc3QgbmV3U0MgPSBmLm9yaWdpbk5vZGUuYm9keVsnQGJsb2NrJ10uZ2V0U2NvcGVJbnN0YW5jZShmLnNjLCB0aGlzLmRlbHRhKTtcbiAgICBjb25zdCBmdW5TdGF0dXNcbiAgICAgICAgPSBuZXcgc3RhdHVzLlN0YXR1cyhmdW5FbnZbMF0sIG5ldyBJZk9ialR5cGUoZnVuRW52WzFdKSwgZnVuRW52WzJdLFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIHRoaXMuZGVsdGEsIG5ld1NDKTtcbiAgICAvLyBwYXNzIHRoaXMgb2JqZWN0XG4gICAgY29uc3QgbmV3T2JqID0gZi5nZXRJbnN0YW5jZSgpO1xuICAgIGZ1bkVudlswXS5hZGRUeXBlKG5ld09iaik7XG5cbiAgICBjb25zdCBtaW5MZW4gPSBNYXRoLm1pbih0aGlzLmFyZ3MubGVuZ3RoLCBmLnBhcmFtTmFtZXMubGVuZ3RoKTtcbiAgICBmb3IgKGxldCBpID0gMDsgaSA8IG1pbkxlbjsgaSsrKSB7XG4gICAgICAgIHRoaXMuYXJnc1tpXS5wcm9wYWdhdGUobmV3U0MuZ2V0QVZhbE9mKGYucGFyYW1OYW1lc1tpXSkpO1xuICAgIH1cblxuICAgIC8vIGZvciBhcmd1bWVudHMgb2JqZWN0XG4gICAgaWYgKGYub3JpZ2luTm9kZS5ib2R5WydAYmxvY2snXS51c2VBcmd1bWVudHNPYmplY3QpIHtcbiAgICAgICAgY29uc3QgYXJnT2JqID0gZi5nZXRBcmd1bWVudHNPYmplY3QodGhpcy5kZWx0YSk7XG4gICAgICAgIG5ld1NDLmdldEFWYWxPZignYXJndW1lbnRzJykuYWRkVHlwZShhcmdPYmopO1xuICAgICAgICBmb3IgKGxldCBpID0gMDsgaSA8IHRoaXMuYXJncy5sZW5ndGg7IGkrKykge1xuICAgICAgICAgICAgdGhpcy5hcmdzW2ldLnByb3BhZ2F0ZShhcmdPYmouZ2V0UHJvcChpICsgJycpKTtcbiAgICAgICAgICAgIHRoaXMuYXJnc1tpXS5wcm9wYWdhdGUoYXJnT2JqLmdldFByb3AobnVsbCkpO1xuICAgICAgICB9XG4gICAgICAgIGFyZ09iai5nZXRQcm9wKCdjYWxsZWUnKS5hZGRUeXBlKGYpO1xuICAgICAgICBhcmdPYmouZ2V0UHJvcCgnbGVuZ3RoJykuYWRkVHlwZSh0eXBlcy5QcmltTnVtYmVyKTtcbiAgICB9XG5cbiAgICAvLyBjb25zdHJhaW50IGdlbmVyYXRpb24gZm9yIHRoZSBmdW5jdGlvbiBib2R5XG4gICAgY0dlbi5hZGRDb25zdHJhaW50cyhmLm9yaWdpbk5vZGUuYm9keSwgZnVuU3RhdHVzKTtcblxuICAgIC8vIGJ5IGV4cGxpY2l0IHJldHVybiwgb25seSBPYmpUeXBlIGFyZSBwcm9wYWdhdGVkXG4gICAgZnVuRW52WzFdLnByb3BhZ2F0ZSh0aGlzLnJldCk7XG4gICAgLy8gcmV0dXJuIG5ldyBvYmplY3RcbiAgICB0aGlzLnJldC5hZGRUeXBlKG5ld09iaik7XG4gICAgLy8gZ2V0IGV4Y2VwdGlvblxuICAgIGZ1bkVudlsyXS5wcm9wYWdhdGUodGhpcy5leGMpO1xufTtcblxuLy8gaWdub3JlIG5vbiBvYmplY3QgdHlwZXNcbmZ1bmN0aW9uIElmT2JqVHlwZShhdmFsKSB7XG4gICAgdGhpcy5hdmFsID0gYXZhbDtcbn1cbklmT2JqVHlwZS5wcm90b3R5cGUgPSBPYmplY3QuY3JlYXRlKENTVFIucHJvdG90eXBlKTtcbklmT2JqVHlwZS5wcm90b3R5cGUuYWRkVHlwZSA9IGZ1bmN0aW9uICh0eXBlKSB7XG4gICAgaWYgKCEodHlwZSBpbnN0YW5jZW9mIHR5cGVzLk9ialR5cGUpKSByZXR1cm47XG4gICAgdGhpcy5hdmFsLmFkZFR5cGUodHlwZSk7XG59O1xuXG5leHBvcnRzLlJlYWRQcm9wID0gUmVhZFByb3A7XG5leHBvcnRzLldyaXRlUHJvcCA9IFdyaXRlUHJvcDtcbmV4cG9ydHMuSXNBZGRlZCA9IElzQWRkZWQ7XG5leHBvcnRzLklzQ2FsbGVlID0gSXNDYWxsZWU7XG5leHBvcnRzLklzQ3RvciA9IElzQ3RvcjtcbiIsIi8vIENvbnRleHQgZm9yIGstQ0ZBIGFuYWx5c2lzXG4vL1xuLy8gQXNzdW1lIGEgY29udGV4dCBpcyBhbiBhcnJheSBvZiBudW1iZXJzLlxuLy8gQSBudW1iZXIgaW4gc3VjaCBsaXN0IGRlbm90ZXMgYSBjYWxsIHNpdGUsIHRoYXQgaXMgQGxhYmVsIG9mIGEgQ2FsbEV4cHJlc3Npb24uXG4vLyBXZSBrZWVwIHRoZSBtb3N0IHJlY2VudCAnaycgY2FsbHNpdGVzLlxuLy8gRXF1YWxpdHkgb24gY29udGV4dHMgc2hvdWxkIGxvb2sgaW50byB0aGUgbnVtYmVycy5cblxudmFyIGNhbGxTaXRlQ29udGV4dFBhcmFtZXRlciA9IHtcbiAgICAvLyBtYXhpbXVtIGxlbmd0aCBvZiBjb250ZXh0XG4gICAgbWF4RGVwdGhLOiAwLFxuICAgIC8vIGZ1bmN0aW9uIGxpc3QgZm9yIHNlbnNpdGl2ZSBhbmFseXNpc1xuICAgIHNlbnNGdW5jczoge31cbn07XG5cbmZ1bmN0aW9uIENhbGxTaXRlQ29udGV4dChjc0xpc3QpIHtcbiAgICBpZiAoY3NMaXN0KSB0aGlzLmNzTGlzdCA9IGNzTGlzdDtcbiAgICBlbHNlIHRoaXMuY3NMaXN0ID0gW107XG59XG5cbkNhbGxTaXRlQ29udGV4dC5wcm90b3R5cGUuZXF1YWxzID0gZnVuY3Rpb24gKG90aGVyKSB7XG4gICAgaWYgKHRoaXMuY3NMaXN0Lmxlbmd0aCAhPSBvdGhlci5jc0xpc3QubGVuZ3RoKSByZXR1cm4gZmFsc2U7XG4gICAgZm9yICh2YXIgaSA9IDA7IGkgPCB0aGlzLmNzTGlzdC5sZW5ndGg7IGkrKykge1xuICAgICAgICBpZiAodGhpcy5jc0xpc3RbaV0gIT09IG90aGVyLmNzTGlzdFtpXSkgcmV0dXJuIGZhbHNlO1xuICAgIH1cbiAgICByZXR1cm4gdHJ1ZTtcbn07XG5cbkNhbGxTaXRlQ29udGV4dC5wcm90b3R5cGUuYXBwZW5kT25lID0gZnVuY3Rpb24gKGNhbGxTaXRlKSB7XG4gICAgLy8gdXNlIGNvbmNhdCB0byBjcmVhdGUgYSBuZXcgYXJyYXlcbiAgICAvLyBvbGRlc3Qgb25lIGNvbWVzIGZpcnN0XG4gICAgdmFyIGFwcGVuZGVkID0gdGhpcy5jc0xpc3QuY29uY2F0KGNhbGxTaXRlKTtcbiAgICBpZiAoYXBwZW5kZWQubGVuZ3RoID4gY2FsbFNpdGVDb250ZXh0UGFyYW1ldGVyLm1heERlcHRoSykge1xuICAgICAgICBhcHBlbmRlZC5zaGlmdCgpO1xuICAgIH1cbiAgICByZXR1cm4gbmV3IENhbGxTaXRlQ29udGV4dChhcHBlbmRlZCk7XG59O1xuXG5DYWxsU2l0ZUNvbnRleHQucHJvdG90eXBlLnRvU3RyaW5nID0gZnVuY3Rpb24gKCkge1xuICAgIHJldHVybiB0aGlzLmNzTGlzdC50b1N0cmluZygpO1xufTtcblxuZXhwb3J0cy5jYWxsU2l0ZUNvbnRleHRQYXJhbWV0ZXIgPSBjYWxsU2l0ZUNvbnRleHRQYXJhbWV0ZXI7XG5leHBvcnRzLkNhbGxTaXRlQ29udGV4dCA9IENhbGxTaXRlQ29udGV4dDsiLCIvLyBTdGF0dXM6XG4vLyB7IHNlbGYgIDogQVZhbCxcbi8vICAgcmV0ICAgOiBBVmFsLFxuLy8gICBleGMgICA6IEFWYWwsXG4vLyAgIGRlbHRhIDogQ29udGV4dCxcbi8vICAgc2MgICAgOiBTY29wZUNoYWluIH1cblxuZnVuY3Rpb24gU3RhdHVzKHNlbGYsIHJldCwgZXhjLCBkZWx0YSwgc2MpIHtcbiAgICB0aGlzLnNlbGYgPSBzZWxmO1xuICAgIHRoaXMucmV0ID0gcmV0O1xuICAgIHRoaXMuZXhjID0gZXhjO1xuICAgIHRoaXMuZGVsdGEgPSBkZWx0YTtcbiAgICB0aGlzLnNjID0gc2M7XG59XG5cblN0YXR1cy5wcm90b3R5cGUuZXF1YWxzID0gZnVuY3Rpb24gKG90aGVyKSB7XG4gICAgcmV0dXJuIHRoaXMuc2VsZiA9PT0gb3RoZXIuc2VsZiAmJlxuICAgICAgICB0aGlzLnJldCA9PT0gb3RoZXIucmV0ICYmXG4gICAgICAgIHRoaXMuZXhjID09PSBvdGhlci5leGMgJiZcbiAgICAgICAgdGhpcy5kZWx0YS5lcXVhbHMob3RoZXIuZGVsdGEpICYmXG4gICAgICAgIHRoaXMuc2MgPT09IG90aGVyLnNjO1xufTtcblxuZXhwb3J0cy5TdGF0dXMgPSBTdGF0dXM7IiwiJ3VzZSBzdHJpY3QnO1xuXG4vLyBmb3IgREVCVUdcbnZhciBjb3VudCA9IDA7XG4vKipcbiAqIHRoZSBhYnN0cmFjdCB2YWx1ZSBmb3IgYSBjb25jcmV0ZSB2YWx1ZVxuICogd2hpY2ggaXMgYSBzZXQgb2YgdHlwZXMuXG4gKiBAY29uc3RydWN0b3JcbiAqIEBwYXJhbSB7VHlwZX0gdHlwZSAtIGdpdmUgYSB0eXBlIHRvIG1ha2UgQVZhbCB3aXRoIGEgc2luZ2xlIHR5cGVcbiAqL1xuZnVuY3Rpb24gQVZhbCh0eXBlKSB7XG4gICAgLy8gdHlwZTogY29udGFpbmVkIHR5cGVzXG4gICAgLy8gV2UgYXNzdW1lIHR5cGVzIGFyZSBkaXN0aW5ndWlzaGFibGUgYnkgJz09PSdcbiAgICBpZiAodHlwZSkgdGhpcy50eXBlcyA9IG5ldyBTZXQoW3R5cGVdKTtcbiAgICBlbHNlIHRoaXMudHlwZXMgPSBuZXcgU2V0KCk7XG4gICAgLy8gZm9yd2FyZHM6IHByb3BhZ2F0aW9uIHRhcmdldHNcbiAgICAvLyBXZSBhc3N1bWUgdGFyZ2V0cyBhcmUgZGlzdGluZ3Vpc2hhYmxlIGJ5ICdlcXVhbHMnIG1ldGhvZFxuICAgIHRoaXMuZm9yd2FyZHMgPSBuZXcgU2V0KCk7XG4gICAgLy8gZm9yIERFQlVHXG4gICAgdGhpcy5faWQgPSBjb3VudCsrO1xufVxuLyoqIENoZWNrIHdoZXRoZXIgaXQgaGFzIGFueSB0eXBlXG4gKiBAcmV0dXJucyB7Ym9vbGVhbn1cbiAqL1xuQVZhbC5wcm90b3R5cGUuaXNFbXB0eSA9IGZ1bmN0aW9uICgpIHtcbiAgICByZXR1cm4gdGhpcy50eXBlcy5zaXplID09PSAwO1xufTtcblxuLyoqXG4gKiBAcmV0dXJucyB7W1R5cGVdfVxuICovXG5BVmFsLnByb3RvdHlwZS5nZXRUeXBlcyA9IGZ1bmN0aW9uICgpIHtcbiAgICByZXR1cm4gdGhpcy50eXBlcztcbn07XG5cbi8qKlxuICogQHJldHVybnMge2Jvb2xlYW59XG4gKi9cbkFWYWwucHJvdG90eXBlLmhhc1R5cGUgPSBmdW5jdGlvbiAodHlwZSkge1xuICAgIHJldHVybiB0aGlzLnR5cGVzLmhhcyh0eXBlKTtcbn07XG5cbi8qKlxuICogQWRkIGEgdHlwZS5cbiAqIEBwYXJhbSB7VHlwZX0gdHlwZVxuICovXG5BVmFsLnByb3RvdHlwZS5hZGRUeXBlID0gZnVuY3Rpb24gKHR5cGUpIHtcbiAgICBpZiAodGhpcy50eXBlcy5oYXModHlwZSkpIHJldHVybjtcbiAgICAvLyBnaXZlbiB0eXBlIGlzIG5ld1xuICAgIHRoaXMudHlwZXMuYWRkKHR5cGUpO1xuICAgIC8vIHNlbmQgdG8gcHJvcGFnYXRpb24gdGFyZ2F0c1xuICAgIHRoaXMuZm9yd2FyZHMuZm9yRWFjaChmdW5jdGlvbiAoZndkKSB7XG4gICAgICAgIGZ3ZC5hZGRUeXBlKHR5cGUpO1xuICAgIH0pO1xufTtcbi8qKlxuICogQHBhcmFtIHtBVmFsfSB0YXJnZXRcbiAqL1xuQVZhbC5wcm90b3R5cGUucHJvcGFnYXRlID0gZnVuY3Rpb24gKHRhcmdldCkge1xuICAgIGlmICghdGhpcy5hZGRGb3J3YXJkKHRhcmdldCkpIHJldHVybjtcbiAgICAvLyB0YXJnZXQgaXMgbmV3bHkgYWRkZWRcbiAgICAvLyBzZW5kIHR5cGVzIHRvIHRoZSBuZXcgdGFyZ2V0XG4gICAgdGhpcy50eXBlcy5mb3JFYWNoKGZ1bmN0aW9uICh0eXBlKSB7XG4gICAgICAgIHRhcmdldC5hZGRUeXBlKHR5cGUpO1xuICAgIH0pO1xufTtcblxuQVZhbC5wcm90b3R5cGUuYWRkRm9yd2FyZCA9IGZ1bmN0aW9uIChmd2QpIHtcbiAgICBmb3IgKGxldCBvbGRGd2Qgb2YgdGhpcy5mb3J3YXJkcykge1xuICAgICAgICBpZiAoZndkLmVxdWFscyhvbGRGd2QpKSByZXR1cm4gZmFsc2U7XG4gICAgfVxuICAgIHRoaXMuZm9yd2FyZHMuYWRkKGZ3ZCk7XG4gICAgcmV0dXJuIHRydWU7XG59O1xuXG5BVmFsLnByb3RvdHlwZS5lcXVhbHMgPSBmdW5jdGlvbiAob3RoZXIpIHtcbiAgICAvLyBzaW1wbGUgcmVmZXJlbmNlIGNvbXBhcmlzb25cbiAgICByZXR1cm4gdGhpcyA9PT0gb3RoZXI7XG59O1xuXG4vKipcbiAqIFRPRE86IGNoZWNrIHdoZXRoZXIgd2UgcmVhbGx5IG5lZWQgdGhpcyBtZXRob2QuXG4gKiBAcGFyYW0ge3N0cmluZ30gcHJvcFxuICogQHJldHVybnMge0FWYWx9XG4gKi9cbkFWYWwucHJvdG90eXBlLmdldFByb3AgPSBmdW5jdGlvbiAocHJvcCkge1xuICAgIGlmIChwcm9wID09PSAn4pyWJykge1xuICAgICAgICAvLyDinJYgaXMgdGhlIGJvZ3VzIHByb3BlcnR5IG5hbWUgYWRkZWQgZm9yIGVycm9yIHJlY292ZXJ5LlxuICAgICAgICByZXR1cm4gQVZhbE51bGw7XG4gICAgfVxuICAgIGlmICh0aGlzLnByb3BzLmhhcyhwcm9wKSkge1xuICAgICAgICByZXR1cm4gdGhpcy5wcm9wcy5nZXQocHJvcCk7XG4gICAgfSBlbHNlIHtcbiAgICAgICAgcmV0dXJuIEFWYWxOdWxsO1xuICAgIH1cbn07XG5cbi8qKlxuICogdGhlIHN1cGVyIGNsYXNzIG9mIGFsbCB0eXBlc1xuICogZWFjaCB0eXBlIHNob3VsZCBiZSBkaXN0aW5ndWlzaGFibGUgYnkgJz09PScgb3BlcmF0aW9uLlxuICogQGNvbnN0cnVjdG9yXG4gKi9cbmZ1bmN0aW9uIFR5cGUoKSB7fVxuVHlwZS5wcm90b3R5cGUgPSBPYmplY3QuY3JlYXRlKG51bGwpO1xuXG4vKipcbiAqIDEuIG9iamVjdCB0eXBlc1xuICogQHBhcmFtIHtBVmFsfSBwcm90byAtIEFWYWwgb2YgY29uc3RydWN0b3IncyBwcm90b3R5cGVcbiAqIEBwYXJhbSB7c3RyaW5nfSBuYW1lIC0gZ3Vlc3NlZCBuYW1lXG4gKi9cbmZ1bmN0aW9uIE9ialR5cGUocHJvdG8sIG5hbWUpIHtcbiAgICB0aGlzLm5hbWUgPSBuYW1lO1xuICAgIHRoaXMucHJvcHMgPSBuZXcgTWFwKCk7XG5cbiAgICAvLyBzaGFyZSBwcm90byB3aXRoIF9fcHJvdG9fX1xuICAgIHRoaXMuc2V0UHJvcCgnX19wcm90b19fJywgcHJvdG8pO1xufVxuT2JqVHlwZS5wcm90b3R5cGUgPSBPYmplY3QuY3JlYXRlKFR5cGUucHJvdG90eXBlKTtcbi8qKlxuICogQHBhcmFtIHtzdHJpbmd8bnVsbH0gcHJvcCAtIG51bGwgZm9yIGNvbXB1dGVkIHByb3BzXG4gKiBAcGFyYW0ge2Jvb2xlYW59IHJlYWRPbmx5IC0gaWYgZmFsc2UsIGNyZWF0ZSBBVmFsIGZvciBwcm9wIGlmIG5lY2Vzc2FyeVxuICogQHJldHVybnMge0FWYWx9IEFWYWwgb2YgdGhlIHByb3BlcnR5XG4gKi9cbk9ialR5cGUucHJvdG90eXBlLmdldFByb3AgPSBmdW5jdGlvbiAocHJvcCwgcmVhZE9ubHkpIHtcbiAgICBpZiAocHJvcCA9PT0gJ+KclicpIHtcbiAgICAgICAgLy8g4pyWIGlzIHRoZSBib2d1cyBwcm9wZXJ0eSBuYW1lIGFkZGVkIGR1cmluZyBwYXJzaW5nIGVycm9yIHJlY292ZXJ5LlxuICAgICAgICByZXR1cm4gQVZhbE51bGw7XG4gICAgfVxuICAgIGlmICh0aGlzLnByb3BzLmhhcyhwcm9wKSkge1xuICAgICAgICByZXR1cm4gdGhpcy5wcm9wcy5nZXQocHJvcCk7XG4gICAgfSBlbHNlIGlmIChyZWFkT25seSkge1xuICAgICAgICByZXR1cm4gbnVsbDtcbiAgICB9IGVsc2Uge1xuICAgICAgICB2YXIgbmV3UHJvcEFWYWwgPSBuZXcgQVZhbDtcbiAgICAgICAgdGhpcy5wcm9wcy5zZXQocHJvcCwgbmV3UHJvcEFWYWwpO1xuICAgICAgICByZXR1cm4gbmV3UHJvcEFWYWw7XG4gICAgfVxufTtcbi8qKlxuICogV2UgdXNlIHRoaXMgZnVuY3Rpb24gdG8gc2hhcmUgLnByb3RvdHlwZSB3aXRoIGluc3RhbmNlcyBfX3Byb3RvX19cbiAqIEl0IGlzIHBvc3NpYmxlIHRvIHVzZSB0aGlzIGZ1bmN0aW9uIHRvIG1lcmdlIEFWYWxzIHRvIG9wdGltaXplIHRoZSBhbmFseXplci5cbiAqIEBwYXJhbSB7c3RyaW5nfG51bGx9IHByb3AgLSBudWxsIGZvciBjb21wdXRlZCBwcm9wc1xuICogQHBhcmFtIHtBVmFsfSBhdmFsXG4gKi9cbk9ialR5cGUucHJvdG90eXBlLnNldFByb3AgPSBmdW5jdGlvbiAocHJvcCwgYXZhbCkge1xuICAgIGlmIChwcm9wID09PSAn4pyWJykge1xuICAgICAgICAvLyDinJYgaXMgdGhlIGJvZ3VzIHByb3BlcnR5IG5hbWUgYWRkZWQgZHVyaW5nIHBhcnNpbmcgZXJyb3IgcmVjb3ZlcnkuXG4gICAgICAgIHJldHVybjtcbiAgICB9XG4gICAgdGhpcy5wcm9wcy5zZXQocHJvcCwgYXZhbCk7XG59O1xuLyoqXG4gKiBUT0RPOiBDaGVjayB0aGlzIGZ1bmN0aW9uJ3MgbmVjZXNzaXR5XG4gKiBAcGFyYW0ge3N0cmluZ30gcHJvcFxuICogQHJldHVybnMge2Jvb2xlYW59XG4gKi9cbk9ialR5cGUucHJvdG90eXBlLmhhc1Byb3AgPSBmdW5jdGlvbiAocHJvcCkge1xuICAgIGlmIChwcm9wID09PSAn4pyWJykgcmV0dXJuIGZhbHNlO1xuICAgIHJldHVybiB0aGlzLnByb3BzLmhhcyhwcm9wKTtcbn07XG4vKipcbiAqIFRPRE86IENoZWNrIHRoaXMgZnVuY3Rpb24ncyBuZWNlc3NpdHlcbiAqIEBwYXJhbSB7VHlwZX0gdHlwZVxuICogQHBhcmFtIHtzdHJpbmd9IHByb3BcbiAqL1xuT2JqVHlwZS5wcm90b3R5cGUuYWRkVHlwZVRvUHJvcCA9IGZ1bmN0aW9uICh0eXBlLCBwcm9wKSB7XG4gICAgaWYgKHByb3AgPT09ICfinJYnKSByZXR1cm47XG4gICAgaWYgKCF0aGlzLnByb3BzLmhhcyhwcm9wKSkge1xuICAgICAgICB0aGlzLnByb3BzLnNldChwcm9wLCBuZXcgQVZhbCk7XG4gICAgfVxuICAgIGlmICh0aGlzLnByb3BzLmdldChwcm9wKS5oYXNUeXBlKHR5cGUpKSByZXR1cm47XG4gICAgdGhpcy5wcm9wcy5nZXQocHJvcCkuYWRkVHlwZSh0eXBlKTtcbn07XG4vKipcbiAqIFRPRE86IENoZWNrIHRoaXMgZnVuY3Rpb24ncyBuZWNlc3NpdHlcbiAqIEBwYXJhbSB7QVZhbH0gYXZhbFxuICogQHBhcmFtIHtzdHJpbmd9IHByb3BcbiAqL1xuT2JqVHlwZS5wcm90b3R5cGUuam9pbkFWYWxUb1Byb3AgPSBmdW5jdGlvbiAoYXZhbCwgcHJvcCkge1xuICAgIHZhciBzZWxmID0gdGhpcztcbiAgICBhdmFsLmdldFR5cGVzKCkuZm9yRWFjaChmdW5jdGlvbiAodHlwZSkge1xuICAgICAgICBzZWxmLmFkZFR5cGVUb1Byb3AodHlwZSwgcHJvcCk7XG4gICAgfSk7XG59O1xuXG4vLyBtYWtlIGFuIE9iaiBmcm9tIHRoZSBnbG9iYWwgc2NvcGVcbmZ1bmN0aW9uIG1rT2JqRnJvbUdsb2JhbFNjb3BlKGdTY29wZSkge1xuICAgIHZhciBnT2JqID0gbmV3IE9ialR5cGUoQVZhbE51bGwsICcqZ2xvYmFsIHNjb3BlKicpO1xuICAgIGdPYmoucHJvcHMgPSBnU2NvcGUudmFyTWFwO1xuICAgIC8vIE92ZXJyaWRlIGdldFByb3AgbWV0aG9kIGZvciBnbG9iYWwgb2JqZWN0XG4gICAgLy8gV2UgaWdub3JlICdyZWFkT25seScgcGFyYW1ldGVyIHRvIGFsd2F5cyByZXR1cm4gaXRzIG93biBwcm9wIEFWYWwgXG4gICAgZ09iai5nZXRQcm9wID0gZnVuY3Rpb24gKHByb3ApIHtcbiAgICAgICAgcmV0dXJuIE9ialR5cGUucHJvdG90eXBlLmdldFByb3AuY2FsbCh0aGlzLCBwcm9wKTtcbiAgICB9O1xuICAgIHJldHVybiBnT2JqO1xufVxuXG4vKipcbiAqIDIuIHByaW1pdGl2ZSB0eXBlc1xuICogQGNvbnN0cnVjdG9yXG4gKiBAcGFyYW0ge3N0cmluZ30gbmFtZVxuICovXG5mdW5jdGlvbiBQcmltVHlwZShuYW1lKSB7XG4gICAgdGhpcy5uYW1lID0gbmFtZTtcbn1cblByaW1UeXBlLnByb3RvdHlwZSA9IE9iamVjdC5jcmVhdGUoVHlwZS5wcm90b3R5cGUpO1xuXG4vKipcbiAqIDMuIGZ1bmN0aW9uIHR5cGVzXG4gKiB0aGUgbmFtZSBpcyB1c2VkIGZvciB0aGUgdHlwZSBvZiB0aGUgaW5zdGFuY2VzIGZyb20gdGhlIGZ1bmN0aW9uXG4gKiBAY29uc3RydWN0b3JcbiAqIEBwYXJhbSB7QVZhbH0gZm5fcHJvdG8gLSBBVmFsIGZvciBjb25zdHJ1Y3RvcidzIC5wcm90b3R5cGVcbiAqIEBwYXJhbSB7c3RyaW5nfSBuYW1lIC0gZ3Vlc3NlZCBuYW1lXG4gKiBAcGFyYW0ge1tzdHJpbmddfSBhcmdOYW1lcyAtIGxpc3Qgb2YgcGFyYW1ldGVyIG5hbWVzXG4gKiBAcGFyYW0ge1Njb3BlfSBzYyAtIGZ1bmN0aW9ucyBzY29wZSBjaGFpbiwgb3IgY2xvc3VyZVxuICogQHBhcmFtIHtub2RlfSBvcmlnaW5Ob2RlIC0gQVNUIG5vZGUgZm9yIHRoZSBmdW5jdGlvblxuICogQHBhcmFtIHtUeXBlfSBhcmdQcm90byAtIHByb3RvdHlwZSBmb3IgYXJndW1lbnRzIG9iamVjdFxuICovXG5mdW5jdGlvbiBGblR5cGUoZm5fcHJvdG8sIG5hbWUsIGFyZ05hbWVzLCBzYywgb3JpZ2luTm9kZSwgYXJnUHJvdG8pIHtcbiAgICBPYmpUeXBlLmNhbGwodGhpcywgZm5fcHJvdG8sIG5hbWUpO1xuICAgIHRoaXMucGFyYW1OYW1lcyA9IGFyZ05hbWVzO1xuICAgIHRoaXMuc2MgPSBzYztcbiAgICB0aGlzLm9yaWdpbk5vZGUgPSBvcmlnaW5Ob2RlO1xuICAgIHRoaXMuYXJnUHJvdG8gPSBhcmdQcm90bztcbiAgICAvLyBmdW5FbnYgOiBDYWxsQ29udGV4dCAtPiBbc2VsZiwgcmV0LCBleGNdXG4gICAgdGhpcy5mdW5FbnYgPSBuZXcgTWFwO1xufVxuRm5UeXBlLnByb3RvdHlwZSA9IE9iamVjdC5jcmVhdGUoT2JqVHlwZS5wcm90b3R5cGUpO1xuXG4vKipcbiAqIGNvbnN0cnVjdCBTdGF0dXMgZm9yIGZ1bmN0aW9uXG4gKiBAcGFyYW0ge0NhbGxDb250ZXh0fSBkZWx0YSAtIGNhbGwgY29udGV4dFxuICogQHJldHVybnMge1tBVmFsLCBBVmFsLCBBVmFsXX0gLSBmb3Igc2VsZiwgcmV0dXJuIGFuZCBleGNlcHRpb24gQVZhbHNcbiAqL1xuRm5UeXBlLnByb3RvdHlwZS5nZXRGdW5FbnYgPSBmdW5jdGlvbiAoZGVsdGEpIHtcbiAgICBpZiAodGhpcy5mdW5FbnYuaGFzKGRlbHRhKSkge1xuICAgICAgICByZXR1cm4gdGhpcy5mdW5FbnYuZ2V0KGRlbHRhKTtcbiAgICB9IGVsc2Uge1xuICAgICAgICB2YXIgdHJpcGxlID0gW25ldyBBVmFsLCBuZXcgQVZhbCwgbmV3IEFWYWxdO1xuICAgICAgICB0aGlzLmZ1bkVudi5zZXQoZGVsdGEsIHRyaXBsZSk7XG4gICAgICAgIHJldHVybiB0cmlwbGU7XG4gICAgfVxufTtcblxuRm5UeXBlLnByb3RvdHlwZS5nZXRBcmd1bWVudHNPYmplY3QgPSBmdW5jdGlvbiAoZGVsdGEpIHtcbiAgICB0aGlzLmFyZ09iak1hcCA9IHRoaXMuYXJnT2JqTWFwIHx8IG5ldyBNYXA7XG4gICAgaWYgKHRoaXMuYXJnT2JqTWFwLmhhcyhkZWx0YSkpIHtcbiAgICAgICAgcmV0dXJuIHRoaXMuYXJnT2JqTWFwLmdldChkZWx0YSk7XG4gICAgfSBlbHNlIHtcbiAgICAgICAgdmFyIGFyZ09iaiA9IG5ldyBPYmpUeXBlKG5ldyBBVmFsKHRoaXMuYXJnUHJvdG8pLCAnKmFyZ3VtZW50cyBvYmplY3QqJyk7XG4gICAgICAgIHRoaXMuYXJnT2JqTWFwLnNldChkZWx0YSwgYXJnT2JqKTtcbiAgICAgICAgcmV0dXJuIGFyZ09iajtcbiAgICB9XG59O1xuXG4vKipcbiAqIGdldCBPYmplY3QgbWFkZSBieSB0aGUgZnVuY3Rpb25cbiAqIFRPRE86IHVzZSBhZGRpdGlvbmFsIGluZm9ybWF0aW9uIHRvIGNyZWF0ZSBtdWx0aXBsZSBpbnN0YW5jZXNcbiAqIEByZXR1cm5zIHtPYmpUeXBlfVxuICovXG5GblR5cGUucHJvdG90eXBlLmdldEluc3RhbmNlID0gZnVuY3Rpb24gKCkge1xuICAgIC8vIG9iakluc3RhbmNlIGlzIHRoZSBvYmplY3QgbWFkZSBieSB0aGUgZnVuY3Rpb2FublxuICAgIGlmICh0aGlzLm9iakluc3RhbmNlKSByZXR1cm4gdGhpcy5vYmpJbnN0YW5jZTtcbiAgICAvLyB3ZSB1bmlmeSBjb25zdHJ1Y3RvcidzIC5wcm90b3R5cGUgYW5kIGluc3RhbmNlJ3MgX19wcm90b19fXG4gICAgdGhpcy5vYmpJbnN0YW5jZSA9IG5ldyBPYmpUeXBlKHRoaXMuZ2V0UHJvcCgncHJvdG90eXBlJykpO1xuICAgIHJldHVybiB0aGlzLm9iakluc3RhbmNlO1xufTtcblxuLyoqIFxuICogNC4gYXJyYXkgdHlwZXNcbiAqIEBjb25zdHJ1Y3RvclxuICovXG5mdW5jdGlvbiBBcnJUeXBlKGFycl9wcm90bykge1xuICAgIE9ialR5cGUuY2FsbCh0aGlzLCBhcnJfcHJvdG8sICdBcnJheScpO1xufVxuQXJyVHlwZS5wcm90b3R5cGUgPSBPYmplY3QuY3JlYXRlKE9ialR5cGUucHJvdG90eXBlKTtcblxuLy8gTWFrZSBwcmltaXRpdmUgdHlwZXNcbnZhciBQcmltTnVtYmVyID0gbmV3IFByaW1UeXBlKCdudW1iZXInKTtcbnZhciBQcmltU3RyaW5nID0gbmV3IFByaW1UeXBlKCdzdHJpbmcnKTtcbnZhciBQcmltQm9vbGVhbiA9IG5ldyBQcmltVHlwZSgnYm9vbGVhbicpO1xuXG4vLyBBYnNOdWxsIHJlcHJlc2VudHMgYWxsIGVtcHR5IGFic3RyYWN0IHZhbHVlcy5cbnZhciBBVmFsTnVsbCA9IG5ldyBBVmFsKCk7XG4vLyBZb3Ugc2hvdWxkIG5vdCBhZGQgYW55IHByb3BlcnRpZXMgdG8gaXQuXG5BVmFsTnVsbC5wcm9wcyA9IG51bGw7XG4vLyBBZGRpbmcgdHlwZXMgYXJlIGlnbm9yZWQuXG5BVmFsTnVsbC5hZGRUeXBlID0gZnVuY3Rpb24gKCkge307XG5cblxuLy8gZXhwb3J0XG5leHBvcnRzLlR5cGUgPSBUeXBlO1xuZXhwb3J0cy5PYmpUeXBlID0gT2JqVHlwZTtcbmV4cG9ydHMuRm5UeXBlID0gRm5UeXBlO1xuZXhwb3J0cy5BcnJUeXBlID0gQXJyVHlwZTtcbmV4cG9ydHMuUHJpbU51bWJlciA9IFByaW1OdW1iZXI7XG5leHBvcnRzLlByaW1TdHJpbmcgPSBQcmltU3RyaW5nO1xuZXhwb3J0cy5QcmltQm9vbGVhbiA9IFByaW1Cb29sZWFuO1xuZXhwb3J0cy5ta09iakZyb21HbG9iYWxTY29wZSA9IG1rT2JqRnJvbUdsb2JhbFNjb3BlO1xuXG5leHBvcnRzLkFWYWwgPSBBVmFsO1xuZXhwb3J0cy5BVmFsTnVsbCA9IEFWYWxOdWxsOyIsIi8vIGltcG9ydCBuZWNlc3NhcnkgbGlicmFyaWVzXG52YXIgYWNvcm4gPSByZXF1aXJlKCdhY29ybi9kaXN0L2Fjb3JuJyk7XG52YXIgYXV4ID0gcmVxdWlyZSgnLi9hdXgnKTtcbnZhciB0eXBlcyA9IHJlcXVpcmUoJy4vZG9tYWlucy90eXBlcycpO1xudmFyIGNvbnRleHQgPSByZXF1aXJlKCcuL2RvbWFpbnMvY29udGV4dCcpO1xudmFyIHN0YXR1cyA9IHJlcXVpcmUoJy4vZG9tYWlucy9zdGF0dXMnKTtcbnZhciB1dGlsID0gcmVxdWlyZSgndXRpbCcpO1xudmFyIHZhckJsb2NrID0gcmVxdWlyZSgnLi92YXJCbG9jaycpO1xudmFyIGNHZW4gPSByZXF1aXJlKCcuL2NvbnN0cmFpbnQvY0dlbicpO1xudmFyIHZhclJlZnMgPSByZXF1aXJlKCcuL3ZhcnJlZnMnKTtcblxuZnVuY3Rpb24gYW5hbHl6ZShpbnB1dCwgcmV0QWxsKSB7XG4gICAgLy8gdGhlIFNjb3BlIG9iamVjdCBmb3IgZ2xvYmFsIHNjb3BlXG4gICAgLy8gc2NvcGUuU2NvcGUuZ2xvYmFsU2NvcGUgPSBuZXcgc2NvcGUuU2NvcGUobnVsbCk7XG5cbiAgICAvLyBwYXJzaW5nIGlucHV0IHByb2dyYW1cbiAgICB2YXIgYXN0ID0gYWNvcm4ucGFyc2UoaW5wdXQpO1xuXG4gICAgdmFyIG5vZGVBcnJheUluZGV4ZWRCeUxpc3QgPSBhdXguZ2V0Tm9kZUxpc3QoYXN0KTtcblxuICAgIC8vIFNob3cgQVNUIGJlZm9yZSBzY29wZSByZXNvbHV0aW9uXG4gICAgLy8gYXV4LnNob3dVbmZvbGRlZChhc3QpO1xuXG4gICAgdmFyQmxvY2suYW5ub3RhdGVCbG9ja0luZm8oYXN0KTtcbiAgICB2YXIgZ0Jsb2NrID0gYXN0WydAYmxvY2snXTtcbiAgICB2YXIgaW5pdGlhbENvbnRleHQgPSBuZXcgY29udGV4dC5DYWxsU2l0ZUNvbnRleHQ7XG4gICAgdmFyIGdTY29wZSA9IGdCbG9jay5nZXRTY29wZUluc3RhbmNlKG51bGwsIGluaXRpYWxDb250ZXh0KTtcbiAgICB2YXIgZ09iamVjdCA9IHR5cGVzLm1rT2JqRnJvbUdsb2JhbFNjb3BlKGdTY29wZSk7XG4gICAgdmFyIGluaXRTdGF0dXMgPSBuZXcgc3RhdHVzLlN0YXR1cyhcbiAgICAgICAgZ09iamVjdCxcbiAgICAgICAgdHlwZXMuQVZhbE51bGwsXG4gICAgICAgIHR5cGVzLkFWYWxOdWxsLFxuICAgICAgICBpbml0aWFsQ29udGV4dCxcbiAgICAgICAgZ1Njb3BlKTtcbiAgICAvLyB0aGUgcHJvdG90eXBlIG9iamVjdCBvZiBPYmplY3RcbiAgICB2YXIgT2JqUHJvdG8gPSBuZXcgdHlwZXMuT2JqVHlwZShudWxsLCAnT2JqZWN0LnByb3RvdHlwZScpO1xuICAgIHZhciBydENYID0ge1xuICAgICAgICBnbG9iYWxPYmplY3Q6IGdPYmplY3QsXG4gICAgICAgIC8vIHRlbXBvcmFsXG4gICAgICAgIHByb3Rvczoge1xuICAgICAgICAgICAgT2JqZWN0OiBPYmpQcm90byxcbiAgICAgICAgICAgIEZ1bmN0aW9uOiBuZXcgdHlwZXMuT2JqVHlwZShuZXcgdHlwZXMuQVZhbChPYmpQcm90byksICdGdW5jdGlvbi5wcm90b3R5cGUnKSxcbiAgICAgICAgICAgIEFycmF5OiBuZXcgdHlwZXMuT2JqVHlwZShuZXcgdHlwZXMuQVZhbChPYmpQcm90byksICdBcnJheS5wcm90b3R5cGUnKSxcbiAgICAgICAgICAgIFJlZ0V4cDogbmV3IHR5cGVzLk9ialR5cGUobmV3IHR5cGVzLkFWYWwoT2JqUHJvdG8pLCAnUmVnRXhwLnByb3RvdHlwZScpLFxuICAgICAgICAgICAgU3RyaW5nOiBuZXcgdHlwZXMuT2JqVHlwZShuZXcgdHlwZXMuQVZhbChPYmpQcm90byksICdTdHJpbmcucHJvdG90eXBlJyksXG4gICAgICAgICAgICBOdW1iZXI6IG5ldyB0eXBlcy5PYmpUeXBlKG5ldyB0eXBlcy5BVmFsKE9ialByb3RvKSwgJ051bWJlci5wcm90b3R5cGUnKSxcbiAgICAgICAgICAgIEJvb2xlYW46IG5ldyB0eXBlcy5PYmpUeXBlKG5ldyB0eXBlcy5BVmFsKE9ialByb3RvKSwgJ0Jvb2xlYW4ucHJvdG90eXBlJylcbiAgICAgICAgfVxuXG4gICAgfTtcbiAgICBjR2VuLmFkZENvbnN0cmFpbnRzKGFzdCwgaW5pdFN0YXR1cywgcnRDWCk7XG4gICAgdmFyIGNvbnN0cmFpbnRzID0gY0dlbi5jb25zdHJhaW50cztcbiAgICAvL2F1eC5zaG93VW5mb2xkZWQoZ0Jsb2NrQW5kQW5ub3RhdGVkQVNULmFzdCk7XG4gICAgLy8gYXV4LnNob3dVbmZvbGRlZChjb25zdHJhaW50cyk7XG4gICAgLy8gYXV4LnNob3dVbmZvbGRlZChnQmxvY2spO1xuICAgIC8vIGNvbnNvbGUubG9nKHV0aWwuaW5zcGVjdChnQmxvY2ssIHtkZXB0aDogMTB9KSk7XG4gICAgaWYgKHJldEFsbCkge1xuICAgICAgICByZXR1cm4ge2dPYmplY3Q6IGdPYmplY3QsIEFTVDogYXN0LCBnQmxvY2s6IGdCbG9jaywgZ1Njb3BlOiBnU2NvcGV9O1xuICAgIH0gZWxzZSB7XG4gICAgICAgIHJldHVybiBnT2JqZWN0O1xuICAgIH1cbn1cblxuZXhwb3J0cy5hbmFseXplID0gYW5hbHl6ZTtcbmV4cG9ydHMuZmluZElkZW50aWZpZXJBdCA9IHZhclJlZnMuZmluZElkZW50aWZpZXJBdDtcbmV4cG9ydHMuZmluZFZhclJlZnNBdCA9IHZhclJlZnMuZmluZFZhclJlZnNBdDtcbiIsIi8qXG4gSmF2YVNjcmlwdOuKlCBnbG9iYWwsIGZ1bmN0aW9uIGJsb2NrLCBjYXRjaCBibG9ja+yXkCDrs4DsiJjqsIAg64us66aw64ukLlxuIEVTNuuKlCDsnbzrsJggYmxvY2vsl5Drj4Qg64us66aw64ukLlxuXG4gVmFyQmxvY2vripQg6rCBIGJsb2Nr7JeQIOuLrOumsCDrs4DsiJjrk6TsnYQg64KY7YOA64K464ukLlxuIC0gcGFyZW4gICAgICA6IEJsb2NrVmFycywg67CU6rmlIGJsb2Nr7J2EIOuCmO2DgOuCtOuKlCDqsJ3ssrRcbiAtIG9yaWdpbkxhYmVsOiBudW1iZXIsIO2VtOuLuSBCbG9ja1ZhcnPqsIAg7ISg7Ja465CcIEFTVCBub2Rl7J2YIEBsYWJlbFxuICAgIG9yaWdpbuydtCDrkKAg7IiYIOyeiOuKlCBub2Rl64qUXG4gICAgRnVuY3Rpb24uYm9keSwgQ2F0Y2hDbGF1c2UuYmxvY2sg65GQ6rCA7KeA64ukLlxuICAgIOuRkOqwgOyngCDrqqjrkZAgQmxvY2tTdGF0ZW1lbnTsnbTri6QuXG4gLSBpc0NhdGNoICAgIDogYm9vbGVhbixcbiAgICogdHJ1ZSAgLT4gY2F0Y2ggYmxvY2tcbiAgICogZmFsc2UgLT4gZnVuY3Rpb24gYmxvY2ssIG9yIGdsb2JhbFxuXG4gLSBwYXJhbVZhck5hbWVzIDog66ek6rCc67OA7IiYIOydtOumhCDrqqnroZ0sIOunpOqwnCDrs4DsiJgg7Iic7ISc64yA66GcXG4gLSBsb2NhbFZhck5hbWVzIDog7KeA7JetIOuzgOyImCDsnbTrpoQg66qp66GdLCDsiJzshJwg66y07J2Y66+4XG4gICAgYXJndW1lbnRz66W8IOyCrOyaqe2VmOuKlCDqsr3smrAgbG9jYWxWYXJOYW1lc+yXkCDrk7HsnqXtlZjqs6AsXG4gICAgYXJndW1lbnRzIG9iamVjdOulvCDsgqzsmqntlZjrqbQgdXNlQXJndW1lbnRzT2JqZWN0ID09IHRydWVcblxuIC0gKG9wdGlvbmFsKSB1c2VBcmd1bWVudHNPYmplY3Q6IGJvb2xlYW5cbiAgICDtlajsiJggYm9keSBibG9ja+yduCDqsr3smrDsl5Drp4wg7IKs7JqpIOqwgOuKpVxuICAgICogdHJ1ZSAgOiBhcmd1bWVudHMgb2JqZWN06rCAIOyCrOyaqeuQmOyXiOuLpC5cbiAgICAgIOymiSDtlajsiJggYm9keeyXkOyEnCDrs4DsiJggYXJndW1lbnRz66W8IOyEoOyWuCDsl4bsnbQg7IKs7Jqp7ZaI64ukLlxuICAgICAg7J20IOqyveyasCwgYXJndW1lbnRz64qUIO2VqOyImOydmCDsp4Dsl60g67OA7IiY66GcIOuTseuhneuQnOuLpC5cbiAgICAqIGZhbHNlIOyduCDqsr3smrDripQg7JeG64ukLiDqt7jrn7TqsbDrqbQg7JWE7JiIIOuzgOyImCDsnpDssrTqsIAg7JeG64ukLlxuXG4gLSB1c2VkVmFyaWFibGVzIDog6rCBIGJsb2Nr7J2YIOunpOqwnOuzgOyImCwg7KeA7Jet67OA7IiYIOykkVxuICAg7IKs7Jqp65CY64qUIOychOy5mOqwgCDsnojripQg6rKD65Ok7J2YIOuqqeuhnVxuXG4gLSBpbnN0YW5jZXMgOiBEZWx0YSAtPiBWYXJCbG9ja+ydmCDrs4DsiJjrk6QgLT4gQVZhbFxuICAgZ2V0SW5zdGFuY2UoZGVsdGEpIOulvCDthrXtlbQg6rCZ7J2AIGRlbHRh64qUIOqwmeydgCBtYXBwaW5nIOyjvOqyjCDrp4zrk6xcblxuIC0gc2NvcGVJbnN0YW5jZXMgOiBbU2NvcGVdXG4gICDtmITsnqwgVmFyQmxvY2vsnYQg66eI7KeA66eJ7Jy866GcIO2VmOuKlCBTY29wZeulvCDrqqjrkZAg66qo7J2A64ukLlxuICAgZ2V0U2NvcGVJbnN0YW5jZShkZWx0YSwgcGFyZW4pIOydhCDthrXtlbQg6rCZ7J2AIHNjb3BlIGNoYWlu7J2AXG4gICDqsJnsnYAg6rCd7LK06rCAIOuQmOuPhOuhnSDrp4zrk6Dri6QuXG4qL1xuJ3VzZSBzdHJpY3QnO1xuXG52YXIgdHlwZXMgPSByZXF1aXJlKCcuL2RvbWFpbnMvdHlwZXMnKTtcbnZhciB3YWxrID0gcmVxdWlyZSgnYWNvcm4vZGlzdC93YWxrJyk7XG52YXIgYXV4ID0gcmVxdWlyZSgnLi9hdXgnKTtcblxuZnVuY3Rpb24gVmFyQmxvY2socGFyZW4sIG9yaWdpbk5vZGUsIGlzQ2F0Y2gpIHtcbiAgICB0aGlzLnBhcmVuID0gcGFyZW47XG4gICAgdGhpcy5vcmlnaW5Ob2RlID0gb3JpZ2luTm9kZTtcbiAgICB0aGlzLm9yaWdpbkxhYmVsID0gb3JpZ2luTm9kZVsnQGxhYmVsJ107XG4gICAgdGhpcy5pc0NhdGNoID0gaXNDYXRjaDtcbiAgICB0aGlzLnBhcmFtVmFyTmFtZXMgPSBbXTtcbiAgICB0aGlzLmxvY2FsVmFyTmFtZXMgPSBbXTtcblxuICAgIHRoaXMudXNlZFZhcmlhYmxlcyA9IFtdO1xuICAgIC8vIHRoaXMudXNlQXJndW1lbnRzT2JqZWN0XG4gICAgdGhpcy5pbnN0YW5jZXMgPSBPYmplY3QuY3JlYXRlKG51bGwpO1xuICAgIHRoaXMuc2NvcGVJbnN0YW5jZXMgPSBbXTtcbn1cblxuVmFyQmxvY2sucHJvdG90eXBlID0gT2JqZWN0LmNyZWF0ZShudWxsKTtcblxuVmFyQmxvY2sucHJvdG90eXBlLmlzR2xvYmFsID0gZnVuY3Rpb24gKCkge1xuICAgIHJldHVybiB0aGlzLnBhcmVuID09IG51bGw7XG59O1xuVmFyQmxvY2sucHJvdG90eXBlLmlzRnVuY3Rpb24gPSBmdW5jdGlvbiAoKSB7XG4gICAgcmV0dXJuIHRoaXMucGFyZW4gIT0gbnVsbCAmJiB0aGlzLmxvY2FsVmFyTmFtZXMgIT0gbnVsbDtcbn07XG5WYXJCbG9jay5wcm90b3R5cGUuaXNDYXRjaEJsb2NrID0gZnVuY3Rpb24gKCkge1xuICAgIHJldHVybiB0aGlzLmlzQ2F0Y2g7XG59O1xuXG5WYXJCbG9jay5wcm90b3R5cGUuZ2V0TG9jYWxWYXJOYW1lcyA9IGZ1bmN0aW9uICgpIHtcbiAgICByZXR1cm4gdGhpcy5sb2NhbFZhck5hbWVzO1xufTtcblZhckJsb2NrLnByb3RvdHlwZS5nZXRQYXJhbVZhck5hbWVzID0gZnVuY3Rpb24gKCkge1xuICAgIHJldHVybiB0aGlzLnBhcmFtVmFyTmFtZXM7XG59O1xuVmFyQmxvY2sucHJvdG90eXBlLmhhc0xvY2FsVmFyID0gZnVuY3Rpb24gKHZhck5hbWUpIHtcbiAgICByZXR1cm4gdGhpcy5sb2NhbFZhck5hbWVzICYmIHRoaXMubG9jYWxWYXJOYW1lcy5pbmRleE9mKHZhck5hbWUpID4gLTE7XG59O1xuVmFyQmxvY2sucHJvdG90eXBlLmhhc1BhcmFtVmFyID0gZnVuY3Rpb24gKHZhck5hbWUpIHtcbiAgICByZXR1cm4gdGhpcy5wYXJhbVZhck5hbWVzLmluZGV4T2YodmFyTmFtZSkgPiAtMTtcbn07XG5WYXJCbG9jay5wcm90b3R5cGUuaGFzVmFyID0gZnVuY3Rpb24gKHZhck5hbWUpIHtcbiAgICByZXR1cm4gdGhpcy5oYXNQYXJhbVZhcih2YXJOYW1lKSB8fCB0aGlzLmhhc0xvY2FsVmFyKHZhck5hbWUpO1xufTtcblxuVmFyQmxvY2sucHJvdG90eXBlLmFkZERlY2xhcmVkTG9jYWxWYXIgPSBmdW5jdGlvbiAodmFyTmFtZSwgaXNGdW5EZWNsKSB7XG4gICAgdmFyIGN1cnJCbG9jayA9IHRoaXM7XG4gICAgLy8gcGVlbCBvZmYgaW5pdGlhbCBjYXRjaCBibG9ja3NcbiAgICAvLyBmb3IgZnVuY3Rpb24gZGVjbCwgc2tpcCBhbnkgY2F0Y2ggYmxvY2tzLFxuICAgIC8vIGZvciB2YXJpYWJsZSBkZWNsLCBza2lwIGNhdGNoIGJsb2NrIHdpdGggZGlmZmVyZW50IHZhck5hbWUuXG4gICAgd2hpbGUgKGN1cnJCbG9jay5pc0NhdGNoQmxvY2soKSAmJlxuICAgICAgICAgICAoaXNGdW5EZWNsIHx8ICFjdXJyQmxvY2suaGFzUGFyYW1WYXIodmFyTmFtZSkpKSB7XG4gICAgICAgIGN1cnJCbG9jayA9IGN1cnJCbG9jay5wYXJlbjtcbiAgICB9XG4gICAgLy8gaWYgYWxyZWFkeSBhZGRlZCwgZG8gbm90IGFkZFxuICAgIGlmICghY3VyckJsb2NrLmhhc1Zhcih2YXJOYW1lKSkge1xuICAgICAgICBjdXJyQmxvY2subG9jYWxWYXJOYW1lcy5wdXNoKHZhck5hbWUpO1xuICAgIH1cbiAgICAvLyByZXR1cm5zIHRoZSBibG9jayBvYmplY3QgdGhhdCBjb250YWlucyB0aGUgdmFyaWFibGVcbiAgICByZXR1cm4gY3VyckJsb2NrO1xufTtcblZhckJsb2NrLnByb3RvdHlwZS5hZGRQYXJhbVZhciA9IGZ1bmN0aW9uICh2YXJOYW1lKSB7XG4gICAgdGhpcy5wYXJhbVZhck5hbWVzLnB1c2godmFyTmFtZSk7XG59O1xuVmFyQmxvY2sucHJvdG90eXBlLmZpbmRWYXJJbkNoYWluID0gZnVuY3Rpb24gKHZhck5hbWUpIHtcbiAgICB2YXIgY3VyckJsb2NrID0gdGhpcztcbiAgICB3aGlsZSAoY3VyckJsb2NrICYmIGN1cnJCbG9jay5wYXJlbiAmJiAhY3VyckJsb2NrLmhhc1Zhcih2YXJOYW1lKSkge1xuICAgICAgICBjdXJyQmxvY2sgPSBjdXJyQmxvY2sucGFyZW47XG4gICAgfVxuICAgIC8vIGlmIG5vdCBmb3VuZCwgaXQgd2lsbCByZXR1cm4gdGhlIGdsb2JhbFxuICAgIHJldHVybiBjdXJyQmxvY2s7XG59O1xuXG5WYXJCbG9jay5wcm90b3R5cGUuaGFzQW5jZXN0b3IgPSBmdW5jdGlvbiAob3RoZXJCbG9jaykge1xuICAgIHZhciBjdXJyQmxvY2sgPSB0aGlzO1xuICAgIHdoaWxlIChjdXJyQmxvY2spIHtcbiAgICAgICAgaWYgKGN1cnJCbG9jayA9PT0gb3RoZXJCbG9jaykge1xuICAgICAgICAgICAgcmV0dXJuIHRydWU7XG4gICAgICAgIH1cbiAgICAgICAgY3VyckJsb2NrID0gY3VyckJsb2NrLnBhcmVuO1xuICAgIH1cbiAgICByZXR1cm4gZmFsc2U7XG59O1xuXG5WYXJCbG9jay5wcm90b3R5cGUuYWRkVXNlZFZhciA9IGZ1bmN0aW9uICh2YXJOYW1lKSB7XG4gICAgaWYgKHRoaXMudXNlZFZhcmlhYmxlcy5pbmRleE9mKHZhck5hbWUpID09PSAtMSkge1xuICAgICAgICB0aGlzLnVzZWRWYXJpYWJsZXMucHVzaCh2YXJOYW1lKTtcbiAgICB9XG59O1xuVmFyQmxvY2sucHJvdG90eXBlLmdldFVzZWRWYXJOYW1lcyA9IGZ1bmN0aW9uICgpIHtcbiAgICByZXR1cm4gdGhpcy51c2VkVmFyaWFibGVzO1xufTtcblZhckJsb2NrLnByb3RvdHlwZS5pc1VzZWRWYXIgPSBmdW5jdGlvbiAodmFyTmFtZSkge1xuICAgIHJldHVybiB0aGlzLnVzZWRWYXJpYWJsZXMuaW5kZXhPZih2YXJOYW1lKSA+IC0xO1xufTtcblxuLy8gcmV0dXJucyBhIG1hcHBpbmdcblZhckJsb2NrLnByb3RvdHlwZS5nZXRJbnN0YW5jZSA9IGZ1bmN0aW9uIChkZWx0YSkge1xuICAgIGlmICh0aGlzLmluc3RhbmNlc1tkZWx0YV0pIHtcbiAgICAgICAgcmV0dXJuIHRoaXMuaW5zdGFuY2VzW2RlbHRhXTtcbiAgICB9XG4gICAgLy8gY29uc3RydWN0IFZhck1hcFxuICAgIHZhciB2YXJNYXAgPSBuZXcgTWFwKCk7XG4gICAgdmFyIHZhck5hbWVzID0gdGhpcy5nZXRQYXJhbVZhck5hbWVzKCkuY29uY2F0KHRoaXMuZ2V0TG9jYWxWYXJOYW1lcygpKTtcblxuICAgIGZvciAodmFyIGkgPSAwOyBpIDwgdmFyTmFtZXMubGVuZ3RoOyBpKyspIHtcbiAgICAgICAgdmFyTWFwLnNldCh2YXJOYW1lc1tpXSwgbmV3IHR5cGVzLkFWYWwoKSk7XG4gICAgfVxuICAgIC8vIHJlbWVtYmVyIHRoZSBpbnN0YW5jZVxuICAgIHRoaXMuaW5zdGFuY2VzW2RlbHRhXSA9IHZhck1hcDtcbiAgICByZXR1cm4gdmFyTWFwO1xufTtcbi8vIHJldHVybnMgYW4gYXJyYXlcblZhckJsb2NrLnByb3RvdHlwZS5nZXRQYXJhbUFWYWxzID0gZnVuY3Rpb24gKGRlbHRhKSB7XG4gICAgdmFyIGluc3RhbmNlID0gdGhpcy5nZXRJbnN0YW5jZShkZWx0YSk7XG4gICAgdmFyIHBhcmFtcyA9IFtdO1xuICAgIHRoaXMuZ2V0UGFyYW1WYXJOYW1lcygpLmZvckVhY2goZnVuY3Rpb24gKG5hbWUpIHtcbiAgICAgICAgcGFyYW1zLnB1c2goaW5zdGFuY2VbYXV4LmludGVybmFsTmFtZShuYW1lKV0pO1xuICAgIH0pO1xuICAgIHJldHVybiBwYXJhbXM7XG59O1xuLy8gcmV0dXJucyBhbiBBVmFsXG5WYXJCbG9jay5wcm90b3R5cGUuZ2V0QXJndW1lbnRzQVZhbCA9IGZ1bmN0aW9uIChkZWx0YSkge1xuICAgIGlmICghdGhpcy51c2VBcmd1bWVudHNPYmplY3QpIHtcbiAgICAgICAgdGhyb3cgbmV3IEVycm9yKCdOb3QgZm9yIHRoaXMgVmFyQmxvY2snKTtcbiAgICB9XG4gICAgcmV0dXJuIHRoaXMuZ2V0SW5zdGFuY2UoZGVsdGEpW2F1eC5pbnRlcm5hbE5hbWUoJ2FyZ3VtZW50cycpXTtcbn07XG5cbi8vIGdldCBhIFNjb3BlIGluc3RhbmNlXG5WYXJCbG9jay5wcm90b3R5cGUuZ2V0U2NvcGVJbnN0YW5jZSA9IGZ1bmN0aW9uIChwYXJlbiwgZGVsdGEpIHtcbiAgICB2YXIgdmFyTWFwID0gdGhpcy5nZXRJbnN0YW5jZShkZWx0YSk7XG4gICAgdmFyIGZvdW5kID0gbnVsbDtcblxuICAgIHRoaXMuc2NvcGVJbnN0YW5jZXMuZm9yRWFjaChmdW5jdGlvbiAoc2MpIHtcbiAgICAgICAgaWYgKHNjLnBhcmVuID09PSBwYXJlbiAmJiBzYy52YXJNYXAgPT09IHZhck1hcCkgZm91bmQgPSBzYztcbiAgICB9KTtcblxuICAgIGlmIChmb3VuZCkge1xuICAgICAgICByZXR1cm4gZm91bmQ7XG4gICAgfSBlbHNlIHtcbiAgICAgICAgdmFyIG5ld1Njb3BlSW5zdGFuY2UgPSBuZXcgU2NvcGUocGFyZW4sIHZhck1hcCwgdGhpcyk7XG4gICAgICAgIHRoaXMuc2NvcGVJbnN0YW5jZXMucHVzaChuZXdTY29wZUluc3RhbmNlKTtcbiAgICAgICAgcmV0dXJuIG5ld1Njb3BlSW5zdGFuY2U7XG4gICAgfVxufTtcblxudmFyIGRlY2xhcmVkVmFyaWFibGVGaW5kZXIgPSB3YWxrLm1ha2Uoe1xuICAgRnVuY3Rpb246IGZ1bmN0aW9uIChub2RlLCBjdXJyQmxvY2ssIGMpIHtcbiAgICAgICAgdmFyIHBhcmVuQmxvY2sgPSBjdXJyQmxvY2s7XG4gICAgICAgIGlmIChub2RlLmlkKSB7XG4gICAgICAgICAgICB2YXIgZnVuY05hbWUgPSBub2RlLmlkLm5hbWU7XG4gICAgICAgICAgICBwYXJlbkJsb2NrID0gY3VyckJsb2NrLmFkZERlY2xhcmVkTG9jYWxWYXIoZnVuY05hbWUsIHRydWUpO1xuICAgICAgICB9XG4gICAgICAgIC8vIGNyZWF0ZSBhIFZhckJsb2NrIGZvciBmdW5jdGlvblxuICAgICAgICB2YXIgZnVuY0Jsb2NrID0gbmV3IFZhckJsb2NrKHBhcmVuQmxvY2ssIG5vZGUpO1xuICAgICAgICBub2RlLmJvZHlbJ0BibG9jayddID0gZnVuY0Jsb2NrO1xuICAgICAgICAvLyBhZGQgZnVuY3Rpb24gcGFyYW1ldGVycyB0byB0aGUgc2NvcGVcbiAgICAgICAgZm9yICh2YXIgaSA9IDA7IGkgPCBub2RlLnBhcmFtcy5sZW5ndGg7IGkrKykge1xuICAgICAgICAgICAgdmFyIHBhcmFtTmFtZSA9IG5vZGUucGFyYW1zW2ldLm5hbWU7XG4gICAgICAgICAgICBmdW5jQmxvY2suYWRkUGFyYW1WYXIocGFyYW1OYW1lKTtcbiAgICAgICAgfVxuICAgICAgICBjKG5vZGUuYm9keSwgZnVuY0Jsb2NrLCB1bmRlZmluZWQpO1xuICAgIH0sXG4gICAgVmFyaWFibGVEZWNsYXJhdGlvbjogZnVuY3Rpb24gKG5vZGUsIGN1cnJCbG9jaywgYykge1xuICAgICAgICBmb3IgKHZhciBpID0gMDsgaSA8IG5vZGUuZGVjbGFyYXRpb25zLmxlbmd0aDsgaSsrKSB7XG4gICAgICAgICAgICB2YXIgZGVjbCA9IG5vZGUuZGVjbGFyYXRpb25zW2ldO1xuICAgICAgICAgICAgdmFyIG5hbWUgPSBkZWNsLmlkLm5hbWU7XG4gICAgICAgICAgICBjdXJyQmxvY2suYWRkRGVjbGFyZWRMb2NhbFZhcihuYW1lKTtcbiAgICAgICAgfVxuICAgICAgICBpZiAoZGVjbC5pbml0KSBjKGRlY2wuaW5pdCwgY3VyckJsb2NrLCB1bmRlZmluZWQpO1xuICAgIH0sXG4gICAgVHJ5U3RhdGVtZW50OiBmdW5jdGlvbiAobm9kZSwgY3VyclNjb3BlLCBjKSB7XG4gICAgICAgIGMobm9kZS5ibG9jaywgY3VyclNjb3BlLCB1bmRlZmluZWQpO1xuICAgICAgICBpZiAobm9kZS5oYW5kbGVyKSB7XG4gICAgICAgICAgICBjKG5vZGUuaGFuZGxlciwgY3VyclNjb3BlLCB1bmRlZmluZWQpO1xuICAgICAgICB9XG4gICAgICAgIGlmIChub2RlLmZpbmFsaXplcikge1xuICAgICAgICAgICAgYyhub2RlLmZpbmFsaXplciwgY3VyclNjb3BlLCB1bmRlZmluZWQpO1xuICAgICAgICB9XG4gICAgfSxcbiAgICBDYXRjaENsYXVzZTogZnVuY3Rpb24gKG5vZGUsIGN1cnJCbG9jaywgYykge1xuICAgICAgICB2YXIgY2F0Y2hCbG9jayA9IG5ldyBWYXJCbG9jayhjdXJyQmxvY2ssIG5vZGUsIHRydWUpO1xuICAgICAgICBjYXRjaEJsb2NrLmFkZFBhcmFtVmFyKG5vZGUucGFyYW0ubmFtZSk7XG4gICAgICAgIG5vZGUuYm9keVsnQGJsb2NrJ10gPSBjYXRjaEJsb2NrO1xuICAgICAgICBjKG5vZGUuYm9keSwgY2F0Y2hCbG9jaywgdW5kZWZpbmVkKTtcbiAgICB9XG59KTtcblxuLy8gRm9yIHZhcmlhYmxlcyBpbiBnbG9iYWwgYW5kIGFyZ3VtZW50cyBpbiBmdW5jdGlvbnNcbnZhciB2YXJpYWJsZVVzYWdlQ29sbGVjdG9yID0gd2Fsay5tYWtlKHtcbiAgICBJZGVudGlmaWVyOiBmdW5jdGlvbiAobm9kZSwgY3VyckJsb2NrLCBjKSB7XG4gICAgICAgIHZhciBjb250YWluaW5nQmxvY2ssIHZhck5hbWUgPSBub2RlLm5hbWU7XG4gICAgICAgIGlmICh2YXJOYW1lICE9PSAnYXJndW1lbnRzJykge1xuICAgICAgICAgICAgY29udGFpbmluZ0Jsb2NrID0gY3VyckJsb2NrLmZpbmRWYXJJbkNoYWluKHZhck5hbWUpO1xuICAgICAgICAgICAgaWYgKGNvbnRhaW5pbmdCbG9jay5pc0dsb2JhbCgpKSB7XG4gICAgICAgICAgICAgICAgY29udGFpbmluZ0Jsb2NrLmFkZERlY2xhcmVkTG9jYWxWYXIodmFyTmFtZSk7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBjb250YWluaW5nQmxvY2suYWRkVXNlZFZhcih2YXJOYW1lKTtcbiAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICAgIC8vIHZhck5hbWUgPT0gJ2FyZ3VtZW50cydcbiAgICAgICAgICAgIGNvbnRhaW5pbmdCbG9jayA9IGN1cnJCbG9jaztcbiAgICAgICAgICAgIHdoaWxlIChjb250YWluaW5nQmxvY2suaXNDYXRjaEJsb2NrKCkgJiZcbiAgICAgICAgICAgICAgICAgICAgIWNvbnRhaW5pbmdCbG9jay5oYXNQYXJhbVZhcih2YXJOYW1lKSkge1xuICAgICAgICAgICAgICAgIGNvbnRhaW5pbmdCbG9jayA9IGNvbnRhaW5pbmdCbG9jay5wYXJlbjtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGlmIChjb250YWluaW5nQmxvY2suaGFzVmFyKHZhck5hbWUpKSB7XG4gICAgICAgICAgICAgICAgLy8gYXJndW1lbnRzIGlzIGV4cGxpY2l0bHkgZGVjbGFyZWRcbiAgICAgICAgICAgICAgICBjb250YWluaW5nQmxvY2suYWRkVXNlZFZhcih2YXJOYW1lKTtcbiAgICAgICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgICAgICAgLy8gYXJndW1lbnRzIGlzIG5vdCBleHBsaWNpdGx5IGRlY2xhcmVkXG4gICAgICAgICAgICAgICAgLy8gYWRkIGl0IGFzIGxvY2FsIHZhcmlhYmxlXG4gICAgICAgICAgICAgICAgY29udGFpbmluZ0Jsb2NrLmFkZERlY2xhcmVkTG9jYWxWYXIodmFyTmFtZSk7XG4gICAgICAgICAgICAgICAgLy8gYWxzbyBpdCBpcyB1c2VkXG4gICAgICAgICAgICAgICAgY29udGFpbmluZ0Jsb2NrLmFkZFVzZWRWYXIodmFyTmFtZSk7XG4gICAgICAgICAgICAgICAgaWYgKGNvbnRhaW5pbmdCbG9jay5pc0Z1bmN0aW9uKCkpIHtcbiAgICAgICAgICAgICAgICAgICAgY29udGFpbmluZ0Jsb2NrLnVzZUFyZ3VtZW50c09iamVjdCA9IHRydWU7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgfVxuICAgICAgICB9XG4gICAgfSxcblxuICAgIFJldHVyblN0YXRlbWVudDogZnVuY3Rpb24gKG5vZGUsIGN1cnJCbG9jaywgYykge1xuICAgICAgICB2YXIgZnVuY3Rpb25CbG9jayA9IGN1cnJCbG9jaztcbiAgICAgICAgd2hpbGUgKGZ1bmN0aW9uQmxvY2suaXNDYXRjaEJsb2NrKCkpIHtcbiAgICAgICAgICAgIGZ1bmN0aW9uQmxvY2sgPSBmdW5jdGlvbkJsb2NrLnBhcmVuO1xuICAgICAgICB9XG4gICAgICAgIGlmICghZnVuY3Rpb25CbG9jay5pc0dsb2JhbCgpICYmIG5vZGUuYXJndW1lbnQgIT09IG51bGwpIHtcbiAgICAgICAgICAgIGZ1bmN0aW9uQmxvY2sudXNlUmV0dXJuV2l0aEFyZ3VtZW50ID0gdHJ1ZTtcbiAgICAgICAgfVxuICAgICAgICBpZiAobm9kZS5hcmd1bWVudCkge1xuICAgICAgICAgICAgYyhub2RlLmFyZ3VtZW50LCBjdXJyQmxvY2ssIHVuZGVmaW5lZCk7XG4gICAgICAgIH1cbiAgICB9LFxuXG4gICAgU2NvcGVCb2R5OiBmdW5jdGlvbiAobm9kZSwgY3VyckJsb2NrLCBjKSB7XG4gICAgICAgIGMobm9kZSwgbm9kZVsnQGJsb2NrJ10gfHwgY3VyckJsb2NrKTtcbiAgICB9XG59KTtcblxuXG5mdW5jdGlvbiBhbm5vdGF0ZUJsb2NrSW5mbyhhc3QsIGdCbG9jaykge1xuICAgIGlmICghZ0Jsb2NrKSB7XG4gICAgICAgIC8vIHdoZW4gZ2xvYmFsIGJsb2NrIGlzIG5vdCBnaXZlbiwgY3JlYXRlXG4gICAgICAgIGdCbG9jayA9IG5ldyBWYXJCbG9jayhudWxsLCBhc3QpO1xuICAgIH1cbiAgICBhc3RbJ0BibG9jayddID0gZ0Jsb2NrO1xuICAgIHdhbGsucmVjdXJzaXZlKGFzdCwgZ0Jsb2NrLCBudWxsLCBkZWNsYXJlZFZhcmlhYmxlRmluZGVyKTtcbiAgICB3YWxrLnJlY3Vyc2l2ZShhc3QsIGdCbG9jaywgbnVsbCwgdmFyaWFibGVVc2FnZUNvbGxlY3Rvcik7XG4gICAgcmV0dXJuIGFzdDtcbn1cblxuLy8gZGVmaW5lIHNjb3BlIG9iamVjdFxuZnVuY3Rpb24gU2NvcGUocGFyZW4sIHZhck1hcCwgdmIpIHtcbiAgICB0aGlzLnBhcmVuID0gcGFyZW47XG4gICAgdGhpcy52YXJNYXAgPSB2YXJNYXA7XG4gICAgdGhpcy52YiA9IHZiO1xufVxuU2NvcGUucHJvdG90eXBlID0gT2JqZWN0LmNyZWF0ZShudWxsKTtcbi8vIGZpbmQgQVZhbCBvZiBhIHZhcmlhYmxlIGluIHRoZSBjaGFpblxuU2NvcGUucHJvdG90eXBlLmdldEFWYWxPZiA9IGZ1bmN0aW9uICh2YXJOYW1lKSB7XG4gICAgdmFyIGN1cnIgPSB0aGlzO1xuICAgIHdoaWxlIChjdXJyICE9IG51bGwpIHtcbiAgICAgICAgaWYgKGN1cnIudmFyTWFwLmhhcyh2YXJOYW1lKSkge1xuICAgICAgICAgICAgcmV0dXJuIGN1cnIudmFyTWFwLmdldCh2YXJOYW1lKTtcbiAgICAgICAgfVxuICAgICAgICBjdXJyID0gY3Vyci5wYXJlbjtcbiAgICB9XG4gICAgdGhyb3cgbmV3IEVycm9yKCdTaG91bGQgaGF2ZSBmb3VuZCB0aGUgdmFyaWFibGUnKTtcbn07XG4vLyByZW1vdmUgaW5pdGlhbCBjYXRjaCBzY29wZXMgZnJvbSB0aGUgY2hhaW5cblNjb3BlLnByb3RvdHlwZS5yZW1vdmVJbml0aWFsQ2F0Y2hCbG9ja3MgPSBmdW5jdGlvbiAoKSB7XG4gICAgdmFyIGN1cnIgPSB0aGlzO1xuICAgIHdoaWxlIChjdXJyLnZiLmlzQ2F0Y2hCbG9jaygpKSB7XG4gICAgICAgIGN1cnIgPSBjdXJyLnBhcmVuO1xuICAgIH1cbiAgICByZXR1cm4gY3Vycjtcbn07XG5cblxuZXhwb3J0cy5WYXJCbG9jayA9IFZhckJsb2NrO1xuZXhwb3J0cy5hbm5vdGF0ZUJsb2NrSW5mbyA9IGFubm90YXRlQmxvY2tJbmZvO1xuZXhwb3J0cy5TY29wZSA9IFNjb3BlO1xuIiwidmFyIHdhbGsgPSByZXF1aXJlKCdhY29ybi9kaXN0L3dhbGsnKTtcbnZhciBmcyA9IHJlcXVpcmUoJ2ZzJyk7XG52YXIgaW5mZXIgPSByZXF1aXJlKCcuL2luZmVyJyk7XG5cblxuLy8gYSB3YWxrZXIgdGhhdCB2aXNpdHMgZWFjaCBpZCB3aXRoIHZhckJsb2NrXG52YXIgdmFyV2Fsa2VyPSB3YWxrLm1ha2Uoe1xuICAgIEZ1bmN0aW9uOiBmdW5jdGlvbiAobm9kZSwgdmIsIGMpIHtcbiAgICAgICAgY29uc3QgaW5uZXJWYiA9IG5vZGUuYm9keVsnQGJsb2NrJ107XG4gICAgICAgIGlmIChub2RlLmlkKSBjKG5vZGUuaWQsIGlubmVyVmIpO1xuICAgICAgICBmb3IgKGxldCBpID0gMDsgaSA8IG5vZGUucGFyYW1zLmxlbmd0aDsgaSsrKVxuICAgICAgICAgICAgYyhub2RlLnBhcmFtc1tpXSwgaW5uZXJWYik7XG4gICAgICAgIGMobm9kZS5ib2R5LCBpbm5lclZiKTtcbiAgICB9LFxuICAgIFRyeVN0YXRlbWVudDogZnVuY3Rpb24gKG5vZGUsIHZiLCBjKSB7XG4gICAgICAgIGMobm9kZS5ibG9jaywgdmIpO1xuICAgICAgICBpZiAobm9kZS5oYW5kbGVyKSB7XG4gICAgICAgICAgICBjb25zdCBjYXRjaFZiID0gbm9kZS5oYW5kbGVyLmJvZHlbJ0BibG9jayddO1xuICAgICAgICAgICAgYyhub2RlLmhhbmRsZXIucGFyYW0sIGNhdGNoVmIpO1xuICAgICAgICAgICAgYyhub2RlLmhhbmRsZXIuYm9keSwgY2F0Y2hWYik7XG4gICAgICAgIH1cbiAgICAgICAgaWYgKG5vZGUuZmluYWxpemVyKSB7XG4gICAgICAgICAgICBjKG5vZGUuZmluYWxpemVyLCB2Yik7XG4gICAgICAgIH1cbiAgICB9LFxuICAgIFZhcmlhYmxlRGVjbGFyYXRpb246IGZ1bmN0aW9uIChub2RlLCB2YiwgYykge1xuICAgICAgICBmb3IgKGxldCBpID0gMDsgaSA8IG5vZGUuZGVjbGFyYXRpb25zLmxlbmd0aDsgKytpKSB7XG4gICAgICAgICAgICB2YXIgZGVjbCA9IG5vZGUuZGVjbGFyYXRpb25zW2ldO1xuICAgICAgICAgICAgYyhkZWNsLmlkLCB2Yik7XG4gICAgICAgICAgICBpZiAoZGVjbC5pbml0KSBjKGRlY2wuaW5pdCwgdmIsIFwiRXhwcmVzc2lvblwiKTtcbiAgICAgICAgfVxuICAgIH1cbn0pO1xuXG5cbi8qKlxuICpcbiAqIEBwYXJhbSBwcmVOb2RlIC0gQXBwbHkgYmVmb3JlIHZpc2l0aW5nIHRoZSBjdXJyZW50IG5vZGUuXG4gKiBJZiByZXR1cm5zIGZhbHNlLCBkbyBub3QgdmlzaXQgdGhlIG5vZGUuXG4gKiBAcGFyYW0gcG9zdE5vZGUgLSBBcHBseSBhZnRlciB2aXNpdGluZyB0aGUgY3VycmVudCBub2RlLlxuICogSWYgZ2l2ZW4sIHJldHVybiB2YWx1ZXMgYXJlIG92ZXJyaWRkZW4uXG4gKiBAcmV0dXJucyB7Kn1cbiAqL1xuZnVuY3Rpb24gd3JhcFdhbGtlcih3YWxrZXIsIHByZU5vZGUsIHBvc3ROb2RlKSB7XG4gICAgY29uc3QgcmV0V2Fsa2VyID0ge307XG4gICAgLy8gd3JhcHBpbmcgZWFjaCBmdW5jdGlvbiBwcmVOb2RlIGFuZCBwb3N0Tm9kZVxuICAgIGZvciAobGV0IG5vZGVUeXBlIGluIHdhbGtlcikge1xuICAgICAgICBpZiAoIXdhbGtlci5oYXNPd25Qcm9wZXJ0eShub2RlVHlwZSkpIHtcbiAgICAgICAgICAgIGNvbnRpbnVlO1xuICAgICAgICB9XG4gICAgICAgIHJldFdhbGtlcltub2RlVHlwZV0gPSAobm9kZSwgdmIsIGMpID0+IHtcbiAgICAgICAgICAgIGxldCByZXQ7XG4gICAgICAgICAgICBpZiAoIXByZU5vZGUgfHwgcHJlTm9kZShub2RlLCB2YiwgYykpIHtcbiAgICAgICAgICAgICAgICByZXQgPSB3YWxrZXJbbm9kZVR5cGVdKG5vZGUsIHZiLCBjKTtcbiAgICAgICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgICAgICAgcmV0dXJuO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgaWYgKHBvc3ROb2RlKSB7XG4gICAgICAgICAgICAgICAgcmV0ID0gcG9zdE5vZGUobm9kZSwgdmIsIGMpO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgcmV0dXJuIHJldDtcbiAgICAgICAgfVxuICAgIH1cbiAgICByZXR1cm4gcmV0V2Fsa2VyO1xufVxuXG5mdW5jdGlvbiBGb3VuZChub2RlLCBzdGF0ZSkge1xuICAgIHRoaXMubm9kZSA9IG5vZGU7XG4gICAgdGhpcy5zdGF0ZSA9IHN0YXRlO1xufVxuXG5mdW5jdGlvbiBmaW5kSWRlbnRpZmllckF0KGFzdCwgcG9zKSB7XG4gICAgXCJ1c2Ugc3RyaWN0XCI7XG5cbiAgICAvLyBmaW5kIHRoZSBub2RlXG4gICAgLy92YXIgZm91bmQgPSB3YWxrLmZpbmROb2RlQXJvdW5kKGFzdCwgcG9zLCB1bmRlZmluZWQsXG4gICAgLy8gICAgdmFyV2Fsa2VyLCBhc3RbJ0BibG9jayddKTtcbiAgICBjb25zdCB3YWxrZXIgPSB3cmFwV2Fsa2VyKHZhcldhbGtlcixcbiAgICAgICAgKG5vZGUsIHZiKSA9PiB7XG4gICAgICAgICAgICBpZiAobm9kZS5zdGFydCA+IHBvcyB8fCBub2RlLmVuZCA8IHBvcykge1xuICAgICAgICAgICAgICAgIHJldHVybiBmYWxzZTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGlmIChub2RlLnR5cGUgPT09ICdJZGVudGlmaWVyJyAmJiBub2RlLm5hbWUgIT09ICfinJYnKSB7XG4gICAgICAgICAgICAgICAgdGhyb3cgbmV3IEZvdW5kKG5vZGUsIHZiKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIHJldHVybiB0cnVlO1xuICAgICAgICB9KTtcblxuICAgIHRyeSB7XG4gICAgICAgIHdhbGsucmVjdXJzaXZlKGFzdCwgYXN0WydAYmxvY2snXSwgd2Fsa2VyKTtcbiAgICB9IGNhdGNoIChlKSB7XG4gICAgICAgIGlmIChlIGluc3RhbmNlb2YgRm91bmQpIHtcbiAgICAgICAgICAgIHJldHVybiBlO1xuICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgICAgdGhyb3cgZTtcbiAgICAgICAgfVxuICAgIH1cbiAgICAvLyBub3QgZm91bmQgYW4gaWRlbnRpZmllclxuICAgIHJldHVybiBudWxsO1xuICAgIC8vaWYgKGZvdW5kLm5vZGUudHlwZSA9PT0gJ0lkZW50aWZpZXInKSB7XG4gICAgLy8gICAgcmV0dXJuIGZvdW5kO1xuICAgIC8vfSBlbHNlIHtcbiAgICAvLyAgICByZXR1cm4gbnVsbDtcbiAgICAvL31cbn1cblxuLyoqXG4gKlxuICogQHBhcmFtIGFzdCAtIHNjb3BlIGFubm90YXRlZCBBU1RcbiAqIEBwYXJhbSB7bnVtYmVyfSBwb3MgLSBjaGFyYWN0ZXIgcG9zaXRpb25cbiAqIEByZXR1cm5zIHsqfSAtIGFycmF5IG9mIEFTVCBub2Rlc1xuICovXG5mdW5jdGlvbiBmaW5kVmFyUmVmc0F0KGFzdCwgcG9zKSB7XG4gICAgXCJ1c2Ugc3RyaWN0XCI7XG4gICAgdmFyIGZvdW5kID0gZmluZElkZW50aWZpZXJBdChhc3QsIHBvcyk7XG4gICAgaWYgKCFmb3VuZCkge1xuICAgICAgICAvLyBwb3MgaXMgbm90IGF0IGEgdmFyaWFibGVcbiAgICAgICAgcmV0dXJuIG51bGw7XG4gICAgfVxuICAgIC8vIGZpbmQgcmVmcyBmb3IgdGhlIGlkIG5vZGVcbiAgICB2YXIgcmVmcyA9IGZpbmRSZWZzVG9WYXJpYWJsZShhc3QsIGZvdW5kKTtcblxuICAgIHJldHVybiByZWZzO1xufVxuXG4vKipcbiAqXG4gKiBAcGFyYW0gYXN0IC0gc2NvcGUgYW5ub3RhdGVkIEFTVFxuICogQHBhcmFtIGZvdW5kIC0gbm9kZSBhbmQgdmFyQmxvY2sgb2YgdGhlIHZhcmlhYmxlXG4gKiBAcmV0dXJucyB7QXJyYXl9IC0gYXJyYXkgb2YgQVNUIG5vZGVzXG4gKi9cbmZ1bmN0aW9uIGZpbmRSZWZzVG9WYXJpYWJsZShhc3QsIGZvdW5kKSB7XG4gICAgXCJ1c2Ugc3RyaWN0XCI7XG4gICAgY29uc3QgdmFyTmFtZSA9IGZvdW5kLm5vZGUubmFtZTtcbiAgICBjb25zdCB2YjEgPSBmb3VuZC5zdGF0ZS5maW5kVmFySW5DaGFpbih2YXJOYW1lKTtcbiAgICBjb25zdCBzdGFydCA9IHZiMS5vcmlnaW5Ob2RlLnN0YXJ0O1xuICAgIGNvbnN0IGVuZCA9IHZiMS5vcmlnaW5Ob2RlLmVuZDtcbiAgICBjb25zdCByZWZzID0gW107XG5cbiAgICB2YXIgd2Fsa2VyID0gd2Fsay5tYWtlKHtcbiAgICAgICAgSWRlbnRpZmllcjogKG5vZGUsIHZiLCBjKSA9PiB7XG4gICAgICAgICAgICBpZiAobm9kZS5uYW1lICE9PSB2YXJOYW1lKSByZXR1cm47XG4gICAgICAgICAgICBjb25zdCB2YjIgPSB2Yi5maW5kVmFySW5DaGFpbih2YXJOYW1lKTtcbiAgICAgICAgICAgIGlmICh2YjEgPT09IHZiMikgcmVmcy5wdXNoKG5vZGUpO1xuICAgICAgICB9XG4gICAgfSwgdmFyV2Fsa2VyKTtcbnZhciBjb3VudCA9IDA7XG5cbiAgICB3YWxrZXIgPSB3cmFwV2Fsa2VyKHdhbGtlciwgKG5vZGUsIHZiKSA9PiB7XG4gICAgICAgIC8vIHZpc2l0IG9ubHkgcmVsYXRlZCBibG9ja3NcbiAgICAgICAgY29uc29sZS5pbmZvKGNvdW50KyspO1xuICAgICAgICBjb25zb2xlLmluZm8odmIpO1xuICAgICAgICByZXR1cm4gZW5kID49IG5vZGUuc3RhcnQgJiYgbm9kZS5lbmQgPj0gc3RhcnQ7XG4gICAgICAgIC8vcmV0dXJuIHZiMS5oYXNBbmNlc3Rvcih2YikgfHwgdmIuaGFzQW5jZXN0b3IodmIxKTtcbiAgICB9KTtcblxuICAgIHdhbGsucmVjdXJzaXZlKGFzdCwgYXN0WydAYmxvY2snXSwgd2Fsa2VyKTtcblxuICAgIHJldHVybiByZWZzO1xufVxuXG4vLyA9PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PVxuXG5mdW5jdGlvbiB0ZXN0KCkge1xuICAgIFwidXNlIHN0cmljdFwiO1xuICAgIHZhciB0ZXN0X3BnbSA9IGZzLnJlYWRGaWxlU3luYygnLi90ZXN0cy9hLmpzJyk7XG4gICAgdmFyIHJlc3VsdCA9IGluZmVyLmFuYWx5emUodGVzdF9wZ20sIHRydWUpO1xuXG4gICAgZm9yICh2YXIgaSA9IDA7IGkgPCB0ZXN0X3BnbS5sZW5ndGg7IGkrKykge1xuICAgICAgICB2YXIgZm91bmROb2RlID0gZmluZElkZW50aWZpZXJBdChyZXN1bHQuQVNULCBpKTtcbiAgICAgICAgaWYgKGZvdW5kTm9kZSkge1xuICAgICAgICAgICAgY29uc29sZS5sb2coaSwgJzogJywgZm91bmROb2RlLm5hbWUpO1xuICAgICAgICB9XG4gICAgfVxufVxuXG5leHBvcnRzLmZpbmRJZGVudGlmaWVyQXQgPSBmaW5kSWRlbnRpZmllckF0O1xuZXhwb3J0cy5maW5kVmFyUmVmc0F0ID0gZmluZFZhclJlZnNBdDsiLCIoZnVuY3Rpb24oZil7aWYodHlwZW9mIGV4cG9ydHM9PT1cIm9iamVjdFwiJiZ0eXBlb2YgbW9kdWxlIT09XCJ1bmRlZmluZWRcIil7bW9kdWxlLmV4cG9ydHM9ZigpfWVsc2UgaWYodHlwZW9mIGRlZmluZT09PVwiZnVuY3Rpb25cIiYmZGVmaW5lLmFtZCl7ZGVmaW5lKFtdLGYpfWVsc2V7dmFyIGc7aWYodHlwZW9mIHdpbmRvdyE9PVwidW5kZWZpbmVkXCIpe2c9d2luZG93fWVsc2UgaWYodHlwZW9mIGdsb2JhbCE9PVwidW5kZWZpbmVkXCIpe2c9Z2xvYmFsfWVsc2UgaWYodHlwZW9mIHNlbGYhPT1cInVuZGVmaW5lZFwiKXtnPXNlbGZ9ZWxzZXtnPXRoaXN9Zy5hY29ybiA9IGYoKX19KShmdW5jdGlvbigpe3ZhciBkZWZpbmUsbW9kdWxlLGV4cG9ydHM7cmV0dXJuIChmdW5jdGlvbiBlKHQsbixyKXtmdW5jdGlvbiBzKG8sdSl7aWYoIW5bb10pe2lmKCF0W29dKXt2YXIgYT10eXBlb2YgcmVxdWlyZT09XCJmdW5jdGlvblwiJiZyZXF1aXJlO2lmKCF1JiZhKXJldHVybiBhKG8sITApO2lmKGkpcmV0dXJuIGkobywhMCk7dmFyIGY9bmV3IEVycm9yKFwiQ2Fubm90IGZpbmQgbW9kdWxlICdcIitvK1wiJ1wiKTt0aHJvdyBmLmNvZGU9XCJNT0RVTEVfTk9UX0ZPVU5EXCIsZn12YXIgbD1uW29dPXtleHBvcnRzOnt9fTt0W29dWzBdLmNhbGwobC5leHBvcnRzLGZ1bmN0aW9uKGUpe3ZhciBuPXRbb11bMV1bZV07cmV0dXJuIHMobj9uOmUpfSxsLGwuZXhwb3J0cyxlLHQsbixyKX1yZXR1cm4gbltvXS5leHBvcnRzfXZhciBpPXR5cGVvZiByZXF1aXJlPT1cImZ1bmN0aW9uXCImJnJlcXVpcmU7Zm9yKHZhciBvPTA7bzxyLmxlbmd0aDtvKyspcyhyW29dKTtyZXR1cm4gc30pKHsxOltmdW5jdGlvbihfZGVyZXFfLG1vZHVsZSxleHBvcnRzKXtcblxuXG4vLyBUaGUgbWFpbiBleHBvcnRlZCBpbnRlcmZhY2UgKHVuZGVyIGBzZWxmLmFjb3JuYCB3aGVuIGluIHRoZVxuLy8gYnJvd3NlcikgaXMgYSBgcGFyc2VgIGZ1bmN0aW9uIHRoYXQgdGFrZXMgYSBjb2RlIHN0cmluZyBhbmRcbi8vIHJldHVybnMgYW4gYWJzdHJhY3Qgc3ludGF4IHRyZWUgYXMgc3BlY2lmaWVkIGJ5IFtNb3ppbGxhIHBhcnNlclxuLy8gQVBJXVthcGldLlxuLy9cbi8vIFthcGldOiBodHRwczovL2RldmVsb3Blci5tb3ppbGxhLm9yZy9lbi1VUy9kb2NzL1NwaWRlck1vbmtleS9QYXJzZXJfQVBJXG5cblwidXNlIHN0cmljdFwiO1xuXG5leHBvcnRzLnBhcnNlID0gcGFyc2U7XG5cbi8vIFRoaXMgZnVuY3Rpb24gdHJpZXMgdG8gcGFyc2UgYSBzaW5nbGUgZXhwcmVzc2lvbiBhdCBhIGdpdmVuXG4vLyBvZmZzZXQgaW4gYSBzdHJpbmcuIFVzZWZ1bCBmb3IgcGFyc2luZyBtaXhlZC1sYW5ndWFnZSBmb3JtYXRzXG4vLyB0aGF0IGVtYmVkIEphdmFTY3JpcHQgZXhwcmVzc2lvbnMuXG5cbmV4cG9ydHMucGFyc2VFeHByZXNzaW9uQXQgPSBwYXJzZUV4cHJlc3Npb25BdDtcblxuLy8gQWNvcm4gaXMgb3JnYW5pemVkIGFzIGEgdG9rZW5pemVyIGFuZCBhIHJlY3Vyc2l2ZS1kZXNjZW50IHBhcnNlci5cbi8vIFRoZSBgdG9rZW5pemVgIGV4cG9ydCBwcm92aWRlcyBhbiBpbnRlcmZhY2UgdG8gdGhlIHRva2VuaXplci5cblxuZXhwb3J0cy50b2tlbml6ZXIgPSB0b2tlbml6ZXI7XG5leHBvcnRzLl9fZXNNb2R1bGUgPSB0cnVlO1xuLy8gQWNvcm4gaXMgYSB0aW55LCBmYXN0IEphdmFTY3JpcHQgcGFyc2VyIHdyaXR0ZW4gaW4gSmF2YVNjcmlwdC5cbi8vXG4vLyBBY29ybiB3YXMgd3JpdHRlbiBieSBNYXJpam4gSGF2ZXJiZWtlLCBJbmd2YXIgU3RlcGFueWFuLCBhbmRcbi8vIHZhcmlvdXMgY29udHJpYnV0b3JzIGFuZCByZWxlYXNlZCB1bmRlciBhbiBNSVQgbGljZW5zZS5cbi8vXG4vLyBHaXQgcmVwb3NpdG9yaWVzIGZvciBBY29ybiBhcmUgYXZhaWxhYmxlIGF0XG4vL1xuLy8gICAgIGh0dHA6Ly9tYXJpam5oYXZlcmJla2UubmwvZ2l0L2Fjb3JuXG4vLyAgICAgaHR0cHM6Ly9naXRodWIuY29tL21hcmlqbmgvYWNvcm4uZ2l0XG4vL1xuLy8gUGxlYXNlIHVzZSB0aGUgW2dpdGh1YiBidWcgdHJhY2tlcl1bZ2hidF0gdG8gcmVwb3J0IGlzc3Vlcy5cbi8vXG4vLyBbZ2hidF06IGh0dHBzOi8vZ2l0aHViLmNvbS9tYXJpam5oL2Fjb3JuL2lzc3Vlc1xuLy9cbi8vIFRoaXMgZmlsZSBkZWZpbmVzIHRoZSBtYWluIHBhcnNlciBpbnRlcmZhY2UuIFRoZSBsaWJyYXJ5IGFsc28gY29tZXNcbi8vIHdpdGggYSBbZXJyb3ItdG9sZXJhbnQgcGFyc2VyXVtkYW1taXRdIGFuZCBhblxuLy8gW2Fic3RyYWN0IHN5bnRheCB0cmVlIHdhbGtlcl1bd2Fsa10sIGRlZmluZWQgaW4gb3RoZXIgZmlsZXMuXG4vL1xuLy8gW2RhbW1pdF06IGFjb3JuX2xvb3NlLmpzXG4vLyBbd2Fsa106IHV0aWwvd2Fsay5qc1xuXG52YXIgX3N0YXRlID0gX2RlcmVxXyhcIi4vc3RhdGVcIik7XG5cbnZhciBQYXJzZXIgPSBfc3RhdGUuUGFyc2VyO1xuXG52YXIgX29wdGlvbnMgPSBfZGVyZXFfKFwiLi9vcHRpb25zXCIpO1xuXG52YXIgZ2V0T3B0aW9ucyA9IF9vcHRpb25zLmdldE9wdGlvbnM7XG5cbl9kZXJlcV8oXCIuL3BhcnNldXRpbFwiKTtcblxuX2RlcmVxXyhcIi4vc3RhdGVtZW50XCIpO1xuXG5fZGVyZXFfKFwiLi9sdmFsXCIpO1xuXG5fZGVyZXFfKFwiLi9leHByZXNzaW9uXCIpO1xuXG5leHBvcnRzLlBhcnNlciA9IF9zdGF0ZS5QYXJzZXI7XG5leHBvcnRzLnBsdWdpbnMgPSBfc3RhdGUucGx1Z2lucztcbmV4cG9ydHMuZGVmYXVsdE9wdGlvbnMgPSBfb3B0aW9ucy5kZWZhdWx0T3B0aW9ucztcblxudmFyIF9sb2NhdGlvbiA9IF9kZXJlcV8oXCIuL2xvY2F0aW9uXCIpO1xuXG5leHBvcnRzLlNvdXJjZUxvY2F0aW9uID0gX2xvY2F0aW9uLlNvdXJjZUxvY2F0aW9uO1xuZXhwb3J0cy5nZXRMaW5lSW5mbyA9IF9sb2NhdGlvbi5nZXRMaW5lSW5mbztcbmV4cG9ydHMuTm9kZSA9IF9kZXJlcV8oXCIuL25vZGVcIikuTm9kZTtcblxudmFyIF90b2tlbnR5cGUgPSBfZGVyZXFfKFwiLi90b2tlbnR5cGVcIik7XG5cbmV4cG9ydHMuVG9rZW5UeXBlID0gX3Rva2VudHlwZS5Ub2tlblR5cGU7XG5leHBvcnRzLnRva1R5cGVzID0gX3Rva2VudHlwZS50eXBlcztcblxudmFyIF90b2tlbmNvbnRleHQgPSBfZGVyZXFfKFwiLi90b2tlbmNvbnRleHRcIik7XG5cbmV4cG9ydHMuVG9rQ29udGV4dCA9IF90b2tlbmNvbnRleHQuVG9rQ29udGV4dDtcbmV4cG9ydHMudG9rQ29udGV4dHMgPSBfdG9rZW5jb250ZXh0LnR5cGVzO1xuXG52YXIgX2lkZW50aWZpZXIgPSBfZGVyZXFfKFwiLi9pZGVudGlmaWVyXCIpO1xuXG5leHBvcnRzLmlzSWRlbnRpZmllckNoYXIgPSBfaWRlbnRpZmllci5pc0lkZW50aWZpZXJDaGFyO1xuZXhwb3J0cy5pc0lkZW50aWZpZXJTdGFydCA9IF9pZGVudGlmaWVyLmlzSWRlbnRpZmllclN0YXJ0O1xuZXhwb3J0cy5Ub2tlbiA9IF9kZXJlcV8oXCIuL3Rva2VuaXplXCIpLlRva2VuO1xuXG52YXIgX3doaXRlc3BhY2UgPSBfZGVyZXFfKFwiLi93aGl0ZXNwYWNlXCIpO1xuXG5leHBvcnRzLmlzTmV3TGluZSA9IF93aGl0ZXNwYWNlLmlzTmV3TGluZTtcbmV4cG9ydHMubGluZUJyZWFrID0gX3doaXRlc3BhY2UubGluZUJyZWFrO1xuZXhwb3J0cy5saW5lQnJlYWtHID0gX3doaXRlc3BhY2UubGluZUJyZWFrRztcbnZhciB2ZXJzaW9uID0gXCIxLjIuMlwiO2V4cG9ydHMudmVyc2lvbiA9IHZlcnNpb247XG5cbmZ1bmN0aW9uIHBhcnNlKGlucHV0LCBvcHRpb25zKSB7XG4gIHZhciBwID0gcGFyc2VyKG9wdGlvbnMsIGlucHV0KTtcbiAgdmFyIHN0YXJ0UG9zID0gcC5wb3MsXG4gICAgICBzdGFydExvYyA9IHAub3B0aW9ucy5sb2NhdGlvbnMgJiYgcC5jdXJQb3NpdGlvbigpO1xuICBwLm5leHRUb2tlbigpO1xuICByZXR1cm4gcC5wYXJzZVRvcExldmVsKHAub3B0aW9ucy5wcm9ncmFtIHx8IHAuc3RhcnROb2RlQXQoc3RhcnRQb3MsIHN0YXJ0TG9jKSk7XG59XG5cbmZ1bmN0aW9uIHBhcnNlRXhwcmVzc2lvbkF0KGlucHV0LCBwb3MsIG9wdGlvbnMpIHtcbiAgdmFyIHAgPSBwYXJzZXIob3B0aW9ucywgaW5wdXQsIHBvcyk7XG4gIHAubmV4dFRva2VuKCk7XG4gIHJldHVybiBwLnBhcnNlRXhwcmVzc2lvbigpO1xufVxuXG5mdW5jdGlvbiB0b2tlbml6ZXIoaW5wdXQsIG9wdGlvbnMpIHtcbiAgcmV0dXJuIHBhcnNlcihvcHRpb25zLCBpbnB1dCk7XG59XG5cbmZ1bmN0aW9uIHBhcnNlcihvcHRpb25zLCBpbnB1dCkge1xuICByZXR1cm4gbmV3IFBhcnNlcihnZXRPcHRpb25zKG9wdGlvbnMpLCBTdHJpbmcoaW5wdXQpKTtcbn1cblxufSx7XCIuL2V4cHJlc3Npb25cIjo2LFwiLi9pZGVudGlmaWVyXCI6NyxcIi4vbG9jYXRpb25cIjo4LFwiLi9sdmFsXCI6OSxcIi4vbm9kZVwiOjEwLFwiLi9vcHRpb25zXCI6MTEsXCIuL3BhcnNldXRpbFwiOjEyLFwiLi9zdGF0ZVwiOjEzLFwiLi9zdGF0ZW1lbnRcIjoxNCxcIi4vdG9rZW5jb250ZXh0XCI6MTUsXCIuL3Rva2VuaXplXCI6MTYsXCIuL3Rva2VudHlwZVwiOjE3LFwiLi93aGl0ZXNwYWNlXCI6MTl9XSwyOltmdW5jdGlvbihfZGVyZXFfLG1vZHVsZSxleHBvcnRzKXtcbmlmICh0eXBlb2YgT2JqZWN0LmNyZWF0ZSA9PT0gJ2Z1bmN0aW9uJykge1xuICAvLyBpbXBsZW1lbnRhdGlvbiBmcm9tIHN0YW5kYXJkIG5vZGUuanMgJ3V0aWwnIG1vZHVsZVxuICBtb2R1bGUuZXhwb3J0cyA9IGZ1bmN0aW9uIGluaGVyaXRzKGN0b3IsIHN1cGVyQ3Rvcikge1xuICAgIGN0b3Iuc3VwZXJfID0gc3VwZXJDdG9yXG4gICAgY3Rvci5wcm90b3R5cGUgPSBPYmplY3QuY3JlYXRlKHN1cGVyQ3Rvci5wcm90b3R5cGUsIHtcbiAgICAgIGNvbnN0cnVjdG9yOiB7XG4gICAgICAgIHZhbHVlOiBjdG9yLFxuICAgICAgICBlbnVtZXJhYmxlOiBmYWxzZSxcbiAgICAgICAgd3JpdGFibGU6IHRydWUsXG4gICAgICAgIGNvbmZpZ3VyYWJsZTogdHJ1ZVxuICAgICAgfVxuICAgIH0pO1xuICB9O1xufSBlbHNlIHtcbiAgLy8gb2xkIHNjaG9vbCBzaGltIGZvciBvbGQgYnJvd3NlcnNcbiAgbW9kdWxlLmV4cG9ydHMgPSBmdW5jdGlvbiBpbmhlcml0cyhjdG9yLCBzdXBlckN0b3IpIHtcbiAgICBjdG9yLnN1cGVyXyA9IHN1cGVyQ3RvclxuICAgIHZhciBUZW1wQ3RvciA9IGZ1bmN0aW9uICgpIHt9XG4gICAgVGVtcEN0b3IucHJvdG90eXBlID0gc3VwZXJDdG9yLnByb3RvdHlwZVxuICAgIGN0b3IucHJvdG90eXBlID0gbmV3IFRlbXBDdG9yKClcbiAgICBjdG9yLnByb3RvdHlwZS5jb25zdHJ1Y3RvciA9IGN0b3JcbiAgfVxufVxuXG59LHt9XSwzOltmdW5jdGlvbihfZGVyZXFfLG1vZHVsZSxleHBvcnRzKXtcbi8vIHNoaW0gZm9yIHVzaW5nIHByb2Nlc3MgaW4gYnJvd3NlclxuXG52YXIgcHJvY2VzcyA9IG1vZHVsZS5leHBvcnRzID0ge307XG52YXIgcXVldWUgPSBbXTtcbnZhciBkcmFpbmluZyA9IGZhbHNlO1xuXG5mdW5jdGlvbiBkcmFpblF1ZXVlKCkge1xuICAgIGlmIChkcmFpbmluZykge1xuICAgICAgICByZXR1cm47XG4gICAgfVxuICAgIGRyYWluaW5nID0gdHJ1ZTtcbiAgICB2YXIgY3VycmVudFF1ZXVlO1xuICAgIHZhciBsZW4gPSBxdWV1ZS5sZW5ndGg7XG4gICAgd2hpbGUobGVuKSB7XG4gICAgICAgIGN1cnJlbnRRdWV1ZSA9IHF1ZXVlO1xuICAgICAgICBxdWV1ZSA9IFtdO1xuICAgICAgICB2YXIgaSA9IC0xO1xuICAgICAgICB3aGlsZSAoKytpIDwgbGVuKSB7XG4gICAgICAgICAgICBjdXJyZW50UXVldWVbaV0oKTtcbiAgICAgICAgfVxuICAgICAgICBsZW4gPSBxdWV1ZS5sZW5ndGg7XG4gICAgfVxuICAgIGRyYWluaW5nID0gZmFsc2U7XG59XG5wcm9jZXNzLm5leHRUaWNrID0gZnVuY3Rpb24gKGZ1bikge1xuICAgIHF1ZXVlLnB1c2goZnVuKTtcbiAgICBpZiAoIWRyYWluaW5nKSB7XG4gICAgICAgIHNldFRpbWVvdXQoZHJhaW5RdWV1ZSwgMCk7XG4gICAgfVxufTtcblxucHJvY2Vzcy50aXRsZSA9ICdicm93c2VyJztcbnByb2Nlc3MuYnJvd3NlciA9IHRydWU7XG5wcm9jZXNzLmVudiA9IHt9O1xucHJvY2Vzcy5hcmd2ID0gW107XG5wcm9jZXNzLnZlcnNpb24gPSAnJzsgLy8gZW1wdHkgc3RyaW5nIHRvIGF2b2lkIHJlZ2V4cCBpc3N1ZXNcbnByb2Nlc3MudmVyc2lvbnMgPSB7fTtcblxuZnVuY3Rpb24gbm9vcCgpIHt9XG5cbnByb2Nlc3Mub24gPSBub29wO1xucHJvY2Vzcy5hZGRMaXN0ZW5lciA9IG5vb3A7XG5wcm9jZXNzLm9uY2UgPSBub29wO1xucHJvY2Vzcy5vZmYgPSBub29wO1xucHJvY2Vzcy5yZW1vdmVMaXN0ZW5lciA9IG5vb3A7XG5wcm9jZXNzLnJlbW92ZUFsbExpc3RlbmVycyA9IG5vb3A7XG5wcm9jZXNzLmVtaXQgPSBub29wO1xuXG5wcm9jZXNzLmJpbmRpbmcgPSBmdW5jdGlvbiAobmFtZSkge1xuICAgIHRocm93IG5ldyBFcnJvcigncHJvY2Vzcy5iaW5kaW5nIGlzIG5vdCBzdXBwb3J0ZWQnKTtcbn07XG5cbi8vIFRPRE8oc2h0eWxtYW4pXG5wcm9jZXNzLmN3ZCA9IGZ1bmN0aW9uICgpIHsgcmV0dXJuICcvJyB9O1xucHJvY2Vzcy5jaGRpciA9IGZ1bmN0aW9uIChkaXIpIHtcbiAgICB0aHJvdyBuZXcgRXJyb3IoJ3Byb2Nlc3MuY2hkaXIgaXMgbm90IHN1cHBvcnRlZCcpO1xufTtcbnByb2Nlc3MudW1hc2sgPSBmdW5jdGlvbigpIHsgcmV0dXJuIDA7IH07XG5cbn0se31dLDQ6W2Z1bmN0aW9uKF9kZXJlcV8sbW9kdWxlLGV4cG9ydHMpe1xubW9kdWxlLmV4cG9ydHMgPSBmdW5jdGlvbiBpc0J1ZmZlcihhcmcpIHtcbiAgcmV0dXJuIGFyZyAmJiB0eXBlb2YgYXJnID09PSAnb2JqZWN0J1xuICAgICYmIHR5cGVvZiBhcmcuY29weSA9PT0gJ2Z1bmN0aW9uJ1xuICAgICYmIHR5cGVvZiBhcmcuZmlsbCA9PT0gJ2Z1bmN0aW9uJ1xuICAgICYmIHR5cGVvZiBhcmcucmVhZFVJbnQ4ID09PSAnZnVuY3Rpb24nO1xufVxufSx7fV0sNTpbZnVuY3Rpb24oX2RlcmVxXyxtb2R1bGUsZXhwb3J0cyl7XG4oZnVuY3Rpb24gKHByb2Nlc3MsZ2xvYmFsKXtcbi8vIENvcHlyaWdodCBKb3llbnQsIEluYy4gYW5kIG90aGVyIE5vZGUgY29udHJpYnV0b3JzLlxuLy9cbi8vIFBlcm1pc3Npb24gaXMgaGVyZWJ5IGdyYW50ZWQsIGZyZWUgb2YgY2hhcmdlLCB0byBhbnkgcGVyc29uIG9idGFpbmluZyBhXG4vLyBjb3B5IG9mIHRoaXMgc29mdHdhcmUgYW5kIGFzc29jaWF0ZWQgZG9jdW1lbnRhdGlvbiBmaWxlcyAodGhlXG4vLyBcIlNvZnR3YXJlXCIpLCB0byBkZWFsIGluIHRoZSBTb2Z0d2FyZSB3aXRob3V0IHJlc3RyaWN0aW9uLCBpbmNsdWRpbmdcbi8vIHdpdGhvdXQgbGltaXRhdGlvbiB0aGUgcmlnaHRzIHRvIHVzZSwgY29weSwgbW9kaWZ5LCBtZXJnZSwgcHVibGlzaCxcbi8vIGRpc3RyaWJ1dGUsIHN1YmxpY2Vuc2UsIGFuZC9vciBzZWxsIGNvcGllcyBvZiB0aGUgU29mdHdhcmUsIGFuZCB0byBwZXJtaXRcbi8vIHBlcnNvbnMgdG8gd2hvbSB0aGUgU29mdHdhcmUgaXMgZnVybmlzaGVkIHRvIGRvIHNvLCBzdWJqZWN0IHRvIHRoZVxuLy8gZm9sbG93aW5nIGNvbmRpdGlvbnM6XG4vL1xuLy8gVGhlIGFib3ZlIGNvcHlyaWdodCBub3RpY2UgYW5kIHRoaXMgcGVybWlzc2lvbiBub3RpY2Ugc2hhbGwgYmUgaW5jbHVkZWRcbi8vIGluIGFsbCBjb3BpZXMgb3Igc3Vic3RhbnRpYWwgcG9ydGlvbnMgb2YgdGhlIFNvZnR3YXJlLlxuLy9cbi8vIFRIRSBTT0ZUV0FSRSBJUyBQUk9WSURFRCBcIkFTIElTXCIsIFdJVEhPVVQgV0FSUkFOVFkgT0YgQU5ZIEtJTkQsIEVYUFJFU1Ncbi8vIE9SIElNUExJRUQsIElOQ0xVRElORyBCVVQgTk9UIExJTUlURUQgVE8gVEhFIFdBUlJBTlRJRVMgT0Zcbi8vIE1FUkNIQU5UQUJJTElUWSwgRklUTkVTUyBGT1IgQSBQQVJUSUNVTEFSIFBVUlBPU0UgQU5EIE5PTklORlJJTkdFTUVOVC4gSU5cbi8vIE5PIEVWRU5UIFNIQUxMIFRIRSBBVVRIT1JTIE9SIENPUFlSSUdIVCBIT0xERVJTIEJFIExJQUJMRSBGT1IgQU5ZIENMQUlNLFxuLy8gREFNQUdFUyBPUiBPVEhFUiBMSUFCSUxJVFksIFdIRVRIRVIgSU4gQU4gQUNUSU9OIE9GIENPTlRSQUNULCBUT1JUIE9SXG4vLyBPVEhFUldJU0UsIEFSSVNJTkcgRlJPTSwgT1VUIE9GIE9SIElOIENPTk5FQ1RJT04gV0lUSCBUSEUgU09GVFdBUkUgT1IgVEhFXG4vLyBVU0UgT1IgT1RIRVIgREVBTElOR1MgSU4gVEhFIFNPRlRXQVJFLlxuXG52YXIgZm9ybWF0UmVnRXhwID0gLyVbc2RqJV0vZztcbmV4cG9ydHMuZm9ybWF0ID0gZnVuY3Rpb24oZikge1xuICBpZiAoIWlzU3RyaW5nKGYpKSB7XG4gICAgdmFyIG9iamVjdHMgPSBbXTtcbiAgICBmb3IgKHZhciBpID0gMDsgaSA8IGFyZ3VtZW50cy5sZW5ndGg7IGkrKykge1xuICAgICAgb2JqZWN0cy5wdXNoKGluc3BlY3QoYXJndW1lbnRzW2ldKSk7XG4gICAgfVxuICAgIHJldHVybiBvYmplY3RzLmpvaW4oJyAnKTtcbiAgfVxuXG4gIHZhciBpID0gMTtcbiAgdmFyIGFyZ3MgPSBhcmd1bWVudHM7XG4gIHZhciBsZW4gPSBhcmdzLmxlbmd0aDtcbiAgdmFyIHN0ciA9IFN0cmluZyhmKS5yZXBsYWNlKGZvcm1hdFJlZ0V4cCwgZnVuY3Rpb24oeCkge1xuICAgIGlmICh4ID09PSAnJSUnKSByZXR1cm4gJyUnO1xuICAgIGlmIChpID49IGxlbikgcmV0dXJuIHg7XG4gICAgc3dpdGNoICh4KSB7XG4gICAgICBjYXNlICclcyc6IHJldHVybiBTdHJpbmcoYXJnc1tpKytdKTtcbiAgICAgIGNhc2UgJyVkJzogcmV0dXJuIE51bWJlcihhcmdzW2krK10pO1xuICAgICAgY2FzZSAnJWonOlxuICAgICAgICB0cnkge1xuICAgICAgICAgIHJldHVybiBKU09OLnN0cmluZ2lmeShhcmdzW2krK10pO1xuICAgICAgICB9IGNhdGNoIChfKSB7XG4gICAgICAgICAgcmV0dXJuICdbQ2lyY3VsYXJdJztcbiAgICAgICAgfVxuICAgICAgZGVmYXVsdDpcbiAgICAgICAgcmV0dXJuIHg7XG4gICAgfVxuICB9KTtcbiAgZm9yICh2YXIgeCA9IGFyZ3NbaV07IGkgPCBsZW47IHggPSBhcmdzWysraV0pIHtcbiAgICBpZiAoaXNOdWxsKHgpIHx8ICFpc09iamVjdCh4KSkge1xuICAgICAgc3RyICs9ICcgJyArIHg7XG4gICAgfSBlbHNlIHtcbiAgICAgIHN0ciArPSAnICcgKyBpbnNwZWN0KHgpO1xuICAgIH1cbiAgfVxuICByZXR1cm4gc3RyO1xufTtcblxuXG4vLyBNYXJrIHRoYXQgYSBtZXRob2Qgc2hvdWxkIG5vdCBiZSB1c2VkLlxuLy8gUmV0dXJucyBhIG1vZGlmaWVkIGZ1bmN0aW9uIHdoaWNoIHdhcm5zIG9uY2UgYnkgZGVmYXVsdC5cbi8vIElmIC0tbm8tZGVwcmVjYXRpb24gaXMgc2V0LCB0aGVuIGl0IGlzIGEgbm8tb3AuXG5leHBvcnRzLmRlcHJlY2F0ZSA9IGZ1bmN0aW9uKGZuLCBtc2cpIHtcbiAgLy8gQWxsb3cgZm9yIGRlcHJlY2F0aW5nIHRoaW5ncyBpbiB0aGUgcHJvY2VzcyBvZiBzdGFydGluZyB1cC5cbiAgaWYgKGlzVW5kZWZpbmVkKGdsb2JhbC5wcm9jZXNzKSkge1xuICAgIHJldHVybiBmdW5jdGlvbigpIHtcbiAgICAgIHJldHVybiBleHBvcnRzLmRlcHJlY2F0ZShmbiwgbXNnKS5hcHBseSh0aGlzLCBhcmd1bWVudHMpO1xuICAgIH07XG4gIH1cblxuICBpZiAocHJvY2Vzcy5ub0RlcHJlY2F0aW9uID09PSB0cnVlKSB7XG4gICAgcmV0dXJuIGZuO1xuICB9XG5cbiAgdmFyIHdhcm5lZCA9IGZhbHNlO1xuICBmdW5jdGlvbiBkZXByZWNhdGVkKCkge1xuICAgIGlmICghd2FybmVkKSB7XG4gICAgICBpZiAocHJvY2Vzcy50aHJvd0RlcHJlY2F0aW9uKSB7XG4gICAgICAgIHRocm93IG5ldyBFcnJvcihtc2cpO1xuICAgICAgfSBlbHNlIGlmIChwcm9jZXNzLnRyYWNlRGVwcmVjYXRpb24pIHtcbiAgICAgICAgY29uc29sZS50cmFjZShtc2cpO1xuICAgICAgfSBlbHNlIHtcbiAgICAgICAgY29uc29sZS5lcnJvcihtc2cpO1xuICAgICAgfVxuICAgICAgd2FybmVkID0gdHJ1ZTtcbiAgICB9XG4gICAgcmV0dXJuIGZuLmFwcGx5KHRoaXMsIGFyZ3VtZW50cyk7XG4gIH1cblxuICByZXR1cm4gZGVwcmVjYXRlZDtcbn07XG5cblxudmFyIGRlYnVncyA9IHt9O1xudmFyIGRlYnVnRW52aXJvbjtcbmV4cG9ydHMuZGVidWdsb2cgPSBmdW5jdGlvbihzZXQpIHtcbiAgaWYgKGlzVW5kZWZpbmVkKGRlYnVnRW52aXJvbikpXG4gICAgZGVidWdFbnZpcm9uID0gcHJvY2Vzcy5lbnYuTk9ERV9ERUJVRyB8fCAnJztcbiAgc2V0ID0gc2V0LnRvVXBwZXJDYXNlKCk7XG4gIGlmICghZGVidWdzW3NldF0pIHtcbiAgICBpZiAobmV3IFJlZ0V4cCgnXFxcXGInICsgc2V0ICsgJ1xcXFxiJywgJ2knKS50ZXN0KGRlYnVnRW52aXJvbikpIHtcbiAgICAgIHZhciBwaWQgPSBwcm9jZXNzLnBpZDtcbiAgICAgIGRlYnVnc1tzZXRdID0gZnVuY3Rpb24oKSB7XG4gICAgICAgIHZhciBtc2cgPSBleHBvcnRzLmZvcm1hdC5hcHBseShleHBvcnRzLCBhcmd1bWVudHMpO1xuICAgICAgICBjb25zb2xlLmVycm9yKCclcyAlZDogJXMnLCBzZXQsIHBpZCwgbXNnKTtcbiAgICAgIH07XG4gICAgfSBlbHNlIHtcbiAgICAgIGRlYnVnc1tzZXRdID0gZnVuY3Rpb24oKSB7fTtcbiAgICB9XG4gIH1cbiAgcmV0dXJuIGRlYnVnc1tzZXRdO1xufTtcblxuXG4vKipcbiAqIEVjaG9zIHRoZSB2YWx1ZSBvZiBhIHZhbHVlLiBUcnlzIHRvIHByaW50IHRoZSB2YWx1ZSBvdXRcbiAqIGluIHRoZSBiZXN0IHdheSBwb3NzaWJsZSBnaXZlbiB0aGUgZGlmZmVyZW50IHR5cGVzLlxuICpcbiAqIEBwYXJhbSB7T2JqZWN0fSBvYmogVGhlIG9iamVjdCB0byBwcmludCBvdXQuXG4gKiBAcGFyYW0ge09iamVjdH0gb3B0cyBPcHRpb25hbCBvcHRpb25zIG9iamVjdCB0aGF0IGFsdGVycyB0aGUgb3V0cHV0LlxuICovXG4vKiBsZWdhY3k6IG9iaiwgc2hvd0hpZGRlbiwgZGVwdGgsIGNvbG9ycyovXG5mdW5jdGlvbiBpbnNwZWN0KG9iaiwgb3B0cykge1xuICAvLyBkZWZhdWx0IG9wdGlvbnNcbiAgdmFyIGN0eCA9IHtcbiAgICBzZWVuOiBbXSxcbiAgICBzdHlsaXplOiBzdHlsaXplTm9Db2xvclxuICB9O1xuICAvLyBsZWdhY3kuLi5cbiAgaWYgKGFyZ3VtZW50cy5sZW5ndGggPj0gMykgY3R4LmRlcHRoID0gYXJndW1lbnRzWzJdO1xuICBpZiAoYXJndW1lbnRzLmxlbmd0aCA+PSA0KSBjdHguY29sb3JzID0gYXJndW1lbnRzWzNdO1xuICBpZiAoaXNCb29sZWFuKG9wdHMpKSB7XG4gICAgLy8gbGVnYWN5Li4uXG4gICAgY3R4LnNob3dIaWRkZW4gPSBvcHRzO1xuICB9IGVsc2UgaWYgKG9wdHMpIHtcbiAgICAvLyBnb3QgYW4gXCJvcHRpb25zXCIgb2JqZWN0XG4gICAgZXhwb3J0cy5fZXh0ZW5kKGN0eCwgb3B0cyk7XG4gIH1cbiAgLy8gc2V0IGRlZmF1bHQgb3B0aW9uc1xuICBpZiAoaXNVbmRlZmluZWQoY3R4LnNob3dIaWRkZW4pKSBjdHguc2hvd0hpZGRlbiA9IGZhbHNlO1xuICBpZiAoaXNVbmRlZmluZWQoY3R4LmRlcHRoKSkgY3R4LmRlcHRoID0gMjtcbiAgaWYgKGlzVW5kZWZpbmVkKGN0eC5jb2xvcnMpKSBjdHguY29sb3JzID0gZmFsc2U7XG4gIGlmIChpc1VuZGVmaW5lZChjdHguY3VzdG9tSW5zcGVjdCkpIGN0eC5jdXN0b21JbnNwZWN0ID0gdHJ1ZTtcbiAgaWYgKGN0eC5jb2xvcnMpIGN0eC5zdHlsaXplID0gc3R5bGl6ZVdpdGhDb2xvcjtcbiAgcmV0dXJuIGZvcm1hdFZhbHVlKGN0eCwgb2JqLCBjdHguZGVwdGgpO1xufVxuZXhwb3J0cy5pbnNwZWN0ID0gaW5zcGVjdDtcblxuXG4vLyBodHRwOi8vZW4ud2lraXBlZGlhLm9yZy93aWtpL0FOU0lfZXNjYXBlX2NvZGUjZ3JhcGhpY3Ncbmluc3BlY3QuY29sb3JzID0ge1xuICAnYm9sZCcgOiBbMSwgMjJdLFxuICAnaXRhbGljJyA6IFszLCAyM10sXG4gICd1bmRlcmxpbmUnIDogWzQsIDI0XSxcbiAgJ2ludmVyc2UnIDogWzcsIDI3XSxcbiAgJ3doaXRlJyA6IFszNywgMzldLFxuICAnZ3JleScgOiBbOTAsIDM5XSxcbiAgJ2JsYWNrJyA6IFszMCwgMzldLFxuICAnYmx1ZScgOiBbMzQsIDM5XSxcbiAgJ2N5YW4nIDogWzM2LCAzOV0sXG4gICdncmVlbicgOiBbMzIsIDM5XSxcbiAgJ21hZ2VudGEnIDogWzM1LCAzOV0sXG4gICdyZWQnIDogWzMxLCAzOV0sXG4gICd5ZWxsb3cnIDogWzMzLCAzOV1cbn07XG5cbi8vIERvbid0IHVzZSAnYmx1ZScgbm90IHZpc2libGUgb24gY21kLmV4ZVxuaW5zcGVjdC5zdHlsZXMgPSB7XG4gICdzcGVjaWFsJzogJ2N5YW4nLFxuICAnbnVtYmVyJzogJ3llbGxvdycsXG4gICdib29sZWFuJzogJ3llbGxvdycsXG4gICd1bmRlZmluZWQnOiAnZ3JleScsXG4gICdudWxsJzogJ2JvbGQnLFxuICAnc3RyaW5nJzogJ2dyZWVuJyxcbiAgJ2RhdGUnOiAnbWFnZW50YScsXG4gIC8vIFwibmFtZVwiOiBpbnRlbnRpb25hbGx5IG5vdCBzdHlsaW5nXG4gICdyZWdleHAnOiAncmVkJ1xufTtcblxuXG5mdW5jdGlvbiBzdHlsaXplV2l0aENvbG9yKHN0ciwgc3R5bGVUeXBlKSB7XG4gIHZhciBzdHlsZSA9IGluc3BlY3Quc3R5bGVzW3N0eWxlVHlwZV07XG5cbiAgaWYgKHN0eWxlKSB7XG4gICAgcmV0dXJuICdcXHUwMDFiWycgKyBpbnNwZWN0LmNvbG9yc1tzdHlsZV1bMF0gKyAnbScgKyBzdHIgK1xuICAgICAgICAgICAnXFx1MDAxYlsnICsgaW5zcGVjdC5jb2xvcnNbc3R5bGVdWzFdICsgJ20nO1xuICB9IGVsc2Uge1xuICAgIHJldHVybiBzdHI7XG4gIH1cbn1cblxuXG5mdW5jdGlvbiBzdHlsaXplTm9Db2xvcihzdHIsIHN0eWxlVHlwZSkge1xuICByZXR1cm4gc3RyO1xufVxuXG5cbmZ1bmN0aW9uIGFycmF5VG9IYXNoKGFycmF5KSB7XG4gIHZhciBoYXNoID0ge307XG5cbiAgYXJyYXkuZm9yRWFjaChmdW5jdGlvbih2YWwsIGlkeCkge1xuICAgIGhhc2hbdmFsXSA9IHRydWU7XG4gIH0pO1xuXG4gIHJldHVybiBoYXNoO1xufVxuXG5cbmZ1bmN0aW9uIGZvcm1hdFZhbHVlKGN0eCwgdmFsdWUsIHJlY3Vyc2VUaW1lcykge1xuICAvLyBQcm92aWRlIGEgaG9vayBmb3IgdXNlci1zcGVjaWZpZWQgaW5zcGVjdCBmdW5jdGlvbnMuXG4gIC8vIENoZWNrIHRoYXQgdmFsdWUgaXMgYW4gb2JqZWN0IHdpdGggYW4gaW5zcGVjdCBmdW5jdGlvbiBvbiBpdFxuICBpZiAoY3R4LmN1c3RvbUluc3BlY3QgJiZcbiAgICAgIHZhbHVlICYmXG4gICAgICBpc0Z1bmN0aW9uKHZhbHVlLmluc3BlY3QpICYmXG4gICAgICAvLyBGaWx0ZXIgb3V0IHRoZSB1dGlsIG1vZHVsZSwgaXQncyBpbnNwZWN0IGZ1bmN0aW9uIGlzIHNwZWNpYWxcbiAgICAgIHZhbHVlLmluc3BlY3QgIT09IGV4cG9ydHMuaW5zcGVjdCAmJlxuICAgICAgLy8gQWxzbyBmaWx0ZXIgb3V0IGFueSBwcm90b3R5cGUgb2JqZWN0cyB1c2luZyB0aGUgY2lyY3VsYXIgY2hlY2suXG4gICAgICAhKHZhbHVlLmNvbnN0cnVjdG9yICYmIHZhbHVlLmNvbnN0cnVjdG9yLnByb3RvdHlwZSA9PT0gdmFsdWUpKSB7XG4gICAgdmFyIHJldCA9IHZhbHVlLmluc3BlY3QocmVjdXJzZVRpbWVzLCBjdHgpO1xuICAgIGlmICghaXNTdHJpbmcocmV0KSkge1xuICAgICAgcmV0ID0gZm9ybWF0VmFsdWUoY3R4LCByZXQsIHJlY3Vyc2VUaW1lcyk7XG4gICAgfVxuICAgIHJldHVybiByZXQ7XG4gIH1cblxuICAvLyBQcmltaXRpdmUgdHlwZXMgY2Fubm90IGhhdmUgcHJvcGVydGllc1xuICB2YXIgcHJpbWl0aXZlID0gZm9ybWF0UHJpbWl0aXZlKGN0eCwgdmFsdWUpO1xuICBpZiAocHJpbWl0aXZlKSB7XG4gICAgcmV0dXJuIHByaW1pdGl2ZTtcbiAgfVxuXG4gIC8vIExvb2sgdXAgdGhlIGtleXMgb2YgdGhlIG9iamVjdC5cbiAgdmFyIGtleXMgPSBPYmplY3Qua2V5cyh2YWx1ZSk7XG4gIHZhciB2aXNpYmxlS2V5cyA9IGFycmF5VG9IYXNoKGtleXMpO1xuXG4gIGlmIChjdHguc2hvd0hpZGRlbikge1xuICAgIGtleXMgPSBPYmplY3QuZ2V0T3duUHJvcGVydHlOYW1lcyh2YWx1ZSk7XG4gIH1cblxuICAvLyBJRSBkb2Vzbid0IG1ha2UgZXJyb3IgZmllbGRzIG5vbi1lbnVtZXJhYmxlXG4gIC8vIGh0dHA6Ly9tc2RuLm1pY3Jvc29mdC5jb20vZW4tdXMvbGlicmFyeS9pZS9kd3c1MnNidCh2PXZzLjk0KS5hc3B4XG4gIGlmIChpc0Vycm9yKHZhbHVlKVxuICAgICAgJiYgKGtleXMuaW5kZXhPZignbWVzc2FnZScpID49IDAgfHwga2V5cy5pbmRleE9mKCdkZXNjcmlwdGlvbicpID49IDApKSB7XG4gICAgcmV0dXJuIGZvcm1hdEVycm9yKHZhbHVlKTtcbiAgfVxuXG4gIC8vIFNvbWUgdHlwZSBvZiBvYmplY3Qgd2l0aG91dCBwcm9wZXJ0aWVzIGNhbiBiZSBzaG9ydGN1dHRlZC5cbiAgaWYgKGtleXMubGVuZ3RoID09PSAwKSB7XG4gICAgaWYgKGlzRnVuY3Rpb24odmFsdWUpKSB7XG4gICAgICB2YXIgbmFtZSA9IHZhbHVlLm5hbWUgPyAnOiAnICsgdmFsdWUubmFtZSA6ICcnO1xuICAgICAgcmV0dXJuIGN0eC5zdHlsaXplKCdbRnVuY3Rpb24nICsgbmFtZSArICddJywgJ3NwZWNpYWwnKTtcbiAgICB9XG4gICAgaWYgKGlzUmVnRXhwKHZhbHVlKSkge1xuICAgICAgcmV0dXJuIGN0eC5zdHlsaXplKFJlZ0V4cC5wcm90b3R5cGUudG9TdHJpbmcuY2FsbCh2YWx1ZSksICdyZWdleHAnKTtcbiAgICB9XG4gICAgaWYgKGlzRGF0ZSh2YWx1ZSkpIHtcbiAgICAgIHJldHVybiBjdHguc3R5bGl6ZShEYXRlLnByb3RvdHlwZS50b1N0cmluZy5jYWxsKHZhbHVlKSwgJ2RhdGUnKTtcbiAgICB9XG4gICAgaWYgKGlzRXJyb3IodmFsdWUpKSB7XG4gICAgICByZXR1cm4gZm9ybWF0RXJyb3IodmFsdWUpO1xuICAgIH1cbiAgfVxuXG4gIHZhciBiYXNlID0gJycsIGFycmF5ID0gZmFsc2UsIGJyYWNlcyA9IFsneycsICd9J107XG5cbiAgLy8gTWFrZSBBcnJheSBzYXkgdGhhdCB0aGV5IGFyZSBBcnJheVxuICBpZiAoaXNBcnJheSh2YWx1ZSkpIHtcbiAgICBhcnJheSA9IHRydWU7XG4gICAgYnJhY2VzID0gWydbJywgJ10nXTtcbiAgfVxuXG4gIC8vIE1ha2UgZnVuY3Rpb25zIHNheSB0aGF0IHRoZXkgYXJlIGZ1bmN0aW9uc1xuICBpZiAoaXNGdW5jdGlvbih2YWx1ZSkpIHtcbiAgICB2YXIgbiA9IHZhbHVlLm5hbWUgPyAnOiAnICsgdmFsdWUubmFtZSA6ICcnO1xuICAgIGJhc2UgPSAnIFtGdW5jdGlvbicgKyBuICsgJ10nO1xuICB9XG5cbiAgLy8gTWFrZSBSZWdFeHBzIHNheSB0aGF0IHRoZXkgYXJlIFJlZ0V4cHNcbiAgaWYgKGlzUmVnRXhwKHZhbHVlKSkge1xuICAgIGJhc2UgPSAnICcgKyBSZWdFeHAucHJvdG90eXBlLnRvU3RyaW5nLmNhbGwodmFsdWUpO1xuICB9XG5cbiAgLy8gTWFrZSBkYXRlcyB3aXRoIHByb3BlcnRpZXMgZmlyc3Qgc2F5IHRoZSBkYXRlXG4gIGlmIChpc0RhdGUodmFsdWUpKSB7XG4gICAgYmFzZSA9ICcgJyArIERhdGUucHJvdG90eXBlLnRvVVRDU3RyaW5nLmNhbGwodmFsdWUpO1xuICB9XG5cbiAgLy8gTWFrZSBlcnJvciB3aXRoIG1lc3NhZ2UgZmlyc3Qgc2F5IHRoZSBlcnJvclxuICBpZiAoaXNFcnJvcih2YWx1ZSkpIHtcbiAgICBiYXNlID0gJyAnICsgZm9ybWF0RXJyb3IodmFsdWUpO1xuICB9XG5cbiAgaWYgKGtleXMubGVuZ3RoID09PSAwICYmICghYXJyYXkgfHwgdmFsdWUubGVuZ3RoID09IDApKSB7XG4gICAgcmV0dXJuIGJyYWNlc1swXSArIGJhc2UgKyBicmFjZXNbMV07XG4gIH1cblxuICBpZiAocmVjdXJzZVRpbWVzIDwgMCkge1xuICAgIGlmIChpc1JlZ0V4cCh2YWx1ZSkpIHtcbiAgICAgIHJldHVybiBjdHguc3R5bGl6ZShSZWdFeHAucHJvdG90eXBlLnRvU3RyaW5nLmNhbGwodmFsdWUpLCAncmVnZXhwJyk7XG4gICAgfSBlbHNlIHtcbiAgICAgIHJldHVybiBjdHguc3R5bGl6ZSgnW09iamVjdF0nLCAnc3BlY2lhbCcpO1xuICAgIH1cbiAgfVxuXG4gIGN0eC5zZWVuLnB1c2godmFsdWUpO1xuXG4gIHZhciBvdXRwdXQ7XG4gIGlmIChhcnJheSkge1xuICAgIG91dHB1dCA9IGZvcm1hdEFycmF5KGN0eCwgdmFsdWUsIHJlY3Vyc2VUaW1lcywgdmlzaWJsZUtleXMsIGtleXMpO1xuICB9IGVsc2Uge1xuICAgIG91dHB1dCA9IGtleXMubWFwKGZ1bmN0aW9uKGtleSkge1xuICAgICAgcmV0dXJuIGZvcm1hdFByb3BlcnR5KGN0eCwgdmFsdWUsIHJlY3Vyc2VUaW1lcywgdmlzaWJsZUtleXMsIGtleSwgYXJyYXkpO1xuICAgIH0pO1xuICB9XG5cbiAgY3R4LnNlZW4ucG9wKCk7XG5cbiAgcmV0dXJuIHJlZHVjZVRvU2luZ2xlU3RyaW5nKG91dHB1dCwgYmFzZSwgYnJhY2VzKTtcbn1cblxuXG5mdW5jdGlvbiBmb3JtYXRQcmltaXRpdmUoY3R4LCB2YWx1ZSkge1xuICBpZiAoaXNVbmRlZmluZWQodmFsdWUpKVxuICAgIHJldHVybiBjdHguc3R5bGl6ZSgndW5kZWZpbmVkJywgJ3VuZGVmaW5lZCcpO1xuICBpZiAoaXNTdHJpbmcodmFsdWUpKSB7XG4gICAgdmFyIHNpbXBsZSA9ICdcXCcnICsgSlNPTi5zdHJpbmdpZnkodmFsdWUpLnJlcGxhY2UoL15cInxcIiQvZywgJycpXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAucmVwbGFjZSgvJy9nLCBcIlxcXFwnXCIpXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAucmVwbGFjZSgvXFxcXFwiL2csICdcIicpICsgJ1xcJyc7XG4gICAgcmV0dXJuIGN0eC5zdHlsaXplKHNpbXBsZSwgJ3N0cmluZycpO1xuICB9XG4gIGlmIChpc051bWJlcih2YWx1ZSkpXG4gICAgcmV0dXJuIGN0eC5zdHlsaXplKCcnICsgdmFsdWUsICdudW1iZXInKTtcbiAgaWYgKGlzQm9vbGVhbih2YWx1ZSkpXG4gICAgcmV0dXJuIGN0eC5zdHlsaXplKCcnICsgdmFsdWUsICdib29sZWFuJyk7XG4gIC8vIEZvciBzb21lIHJlYXNvbiB0eXBlb2YgbnVsbCBpcyBcIm9iamVjdFwiLCBzbyBzcGVjaWFsIGNhc2UgaGVyZS5cbiAgaWYgKGlzTnVsbCh2YWx1ZSkpXG4gICAgcmV0dXJuIGN0eC5zdHlsaXplKCdudWxsJywgJ251bGwnKTtcbn1cblxuXG5mdW5jdGlvbiBmb3JtYXRFcnJvcih2YWx1ZSkge1xuICByZXR1cm4gJ1snICsgRXJyb3IucHJvdG90eXBlLnRvU3RyaW5nLmNhbGwodmFsdWUpICsgJ10nO1xufVxuXG5cbmZ1bmN0aW9uIGZvcm1hdEFycmF5KGN0eCwgdmFsdWUsIHJlY3Vyc2VUaW1lcywgdmlzaWJsZUtleXMsIGtleXMpIHtcbiAgdmFyIG91dHB1dCA9IFtdO1xuICBmb3IgKHZhciBpID0gMCwgbCA9IHZhbHVlLmxlbmd0aDsgaSA8IGw7ICsraSkge1xuICAgIGlmIChoYXNPd25Qcm9wZXJ0eSh2YWx1ZSwgU3RyaW5nKGkpKSkge1xuICAgICAgb3V0cHV0LnB1c2goZm9ybWF0UHJvcGVydHkoY3R4LCB2YWx1ZSwgcmVjdXJzZVRpbWVzLCB2aXNpYmxlS2V5cyxcbiAgICAgICAgICBTdHJpbmcoaSksIHRydWUpKTtcbiAgICB9IGVsc2Uge1xuICAgICAgb3V0cHV0LnB1c2goJycpO1xuICAgIH1cbiAgfVxuICBrZXlzLmZvckVhY2goZnVuY3Rpb24oa2V5KSB7XG4gICAgaWYgKCFrZXkubWF0Y2goL15cXGQrJC8pKSB7XG4gICAgICBvdXRwdXQucHVzaChmb3JtYXRQcm9wZXJ0eShjdHgsIHZhbHVlLCByZWN1cnNlVGltZXMsIHZpc2libGVLZXlzLFxuICAgICAgICAgIGtleSwgdHJ1ZSkpO1xuICAgIH1cbiAgfSk7XG4gIHJldHVybiBvdXRwdXQ7XG59XG5cblxuZnVuY3Rpb24gZm9ybWF0UHJvcGVydHkoY3R4LCB2YWx1ZSwgcmVjdXJzZVRpbWVzLCB2aXNpYmxlS2V5cywga2V5LCBhcnJheSkge1xuICB2YXIgbmFtZSwgc3RyLCBkZXNjO1xuICBkZXNjID0gT2JqZWN0LmdldE93blByb3BlcnR5RGVzY3JpcHRvcih2YWx1ZSwga2V5KSB8fCB7IHZhbHVlOiB2YWx1ZVtrZXldIH07XG4gIGlmIChkZXNjLmdldCkge1xuICAgIGlmIChkZXNjLnNldCkge1xuICAgICAgc3RyID0gY3R4LnN0eWxpemUoJ1tHZXR0ZXIvU2V0dGVyXScsICdzcGVjaWFsJyk7XG4gICAgfSBlbHNlIHtcbiAgICAgIHN0ciA9IGN0eC5zdHlsaXplKCdbR2V0dGVyXScsICdzcGVjaWFsJyk7XG4gICAgfVxuICB9IGVsc2Uge1xuICAgIGlmIChkZXNjLnNldCkge1xuICAgICAgc3RyID0gY3R4LnN0eWxpemUoJ1tTZXR0ZXJdJywgJ3NwZWNpYWwnKTtcbiAgICB9XG4gIH1cbiAgaWYgKCFoYXNPd25Qcm9wZXJ0eSh2aXNpYmxlS2V5cywga2V5KSkge1xuICAgIG5hbWUgPSAnWycgKyBrZXkgKyAnXSc7XG4gIH1cbiAgaWYgKCFzdHIpIHtcbiAgICBpZiAoY3R4LnNlZW4uaW5kZXhPZihkZXNjLnZhbHVlKSA8IDApIHtcbiAgICAgIGlmIChpc051bGwocmVjdXJzZVRpbWVzKSkge1xuICAgICAgICBzdHIgPSBmb3JtYXRWYWx1ZShjdHgsIGRlc2MudmFsdWUsIG51bGwpO1xuICAgICAgfSBlbHNlIHtcbiAgICAgICAgc3RyID0gZm9ybWF0VmFsdWUoY3R4LCBkZXNjLnZhbHVlLCByZWN1cnNlVGltZXMgLSAxKTtcbiAgICAgIH1cbiAgICAgIGlmIChzdHIuaW5kZXhPZignXFxuJykgPiAtMSkge1xuICAgICAgICBpZiAoYXJyYXkpIHtcbiAgICAgICAgICBzdHIgPSBzdHIuc3BsaXQoJ1xcbicpLm1hcChmdW5jdGlvbihsaW5lKSB7XG4gICAgICAgICAgICByZXR1cm4gJyAgJyArIGxpbmU7XG4gICAgICAgICAgfSkuam9pbignXFxuJykuc3Vic3RyKDIpO1xuICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgIHN0ciA9ICdcXG4nICsgc3RyLnNwbGl0KCdcXG4nKS5tYXAoZnVuY3Rpb24obGluZSkge1xuICAgICAgICAgICAgcmV0dXJuICcgICAnICsgbGluZTtcbiAgICAgICAgICB9KS5qb2luKCdcXG4nKTtcbiAgICAgICAgfVxuICAgICAgfVxuICAgIH0gZWxzZSB7XG4gICAgICBzdHIgPSBjdHguc3R5bGl6ZSgnW0NpcmN1bGFyXScsICdzcGVjaWFsJyk7XG4gICAgfVxuICB9XG4gIGlmIChpc1VuZGVmaW5lZChuYW1lKSkge1xuICAgIGlmIChhcnJheSAmJiBrZXkubWF0Y2goL15cXGQrJC8pKSB7XG4gICAgICByZXR1cm4gc3RyO1xuICAgIH1cbiAgICBuYW1lID0gSlNPTi5zdHJpbmdpZnkoJycgKyBrZXkpO1xuICAgIGlmIChuYW1lLm1hdGNoKC9eXCIoW2EtekEtWl9dW2EtekEtWl8wLTldKilcIiQvKSkge1xuICAgICAgbmFtZSA9IG5hbWUuc3Vic3RyKDEsIG5hbWUubGVuZ3RoIC0gMik7XG4gICAgICBuYW1lID0gY3R4LnN0eWxpemUobmFtZSwgJ25hbWUnKTtcbiAgICB9IGVsc2Uge1xuICAgICAgbmFtZSA9IG5hbWUucmVwbGFjZSgvJy9nLCBcIlxcXFwnXCIpXG4gICAgICAgICAgICAgICAgIC5yZXBsYWNlKC9cXFxcXCIvZywgJ1wiJylcbiAgICAgICAgICAgICAgICAgLnJlcGxhY2UoLyheXCJ8XCIkKS9nLCBcIidcIik7XG4gICAgICBuYW1lID0gY3R4LnN0eWxpemUobmFtZSwgJ3N0cmluZycpO1xuICAgIH1cbiAgfVxuXG4gIHJldHVybiBuYW1lICsgJzogJyArIHN0cjtcbn1cblxuXG5mdW5jdGlvbiByZWR1Y2VUb1NpbmdsZVN0cmluZyhvdXRwdXQsIGJhc2UsIGJyYWNlcykge1xuICB2YXIgbnVtTGluZXNFc3QgPSAwO1xuICB2YXIgbGVuZ3RoID0gb3V0cHV0LnJlZHVjZShmdW5jdGlvbihwcmV2LCBjdXIpIHtcbiAgICBudW1MaW5lc0VzdCsrO1xuICAgIGlmIChjdXIuaW5kZXhPZignXFxuJykgPj0gMCkgbnVtTGluZXNFc3QrKztcbiAgICByZXR1cm4gcHJldiArIGN1ci5yZXBsYWNlKC9cXHUwMDFiXFxbXFxkXFxkP20vZywgJycpLmxlbmd0aCArIDE7XG4gIH0sIDApO1xuXG4gIGlmIChsZW5ndGggPiA2MCkge1xuICAgIHJldHVybiBicmFjZXNbMF0gK1xuICAgICAgICAgICAoYmFzZSA9PT0gJycgPyAnJyA6IGJhc2UgKyAnXFxuICcpICtcbiAgICAgICAgICAgJyAnICtcbiAgICAgICAgICAgb3V0cHV0LmpvaW4oJyxcXG4gICcpICtcbiAgICAgICAgICAgJyAnICtcbiAgICAgICAgICAgYnJhY2VzWzFdO1xuICB9XG5cbiAgcmV0dXJuIGJyYWNlc1swXSArIGJhc2UgKyAnICcgKyBvdXRwdXQuam9pbignLCAnKSArICcgJyArIGJyYWNlc1sxXTtcbn1cblxuXG4vLyBOT1RFOiBUaGVzZSB0eXBlIGNoZWNraW5nIGZ1bmN0aW9ucyBpbnRlbnRpb25hbGx5IGRvbid0IHVzZSBgaW5zdGFuY2VvZmBcbi8vIGJlY2F1c2UgaXQgaXMgZnJhZ2lsZSBhbmQgY2FuIGJlIGVhc2lseSBmYWtlZCB3aXRoIGBPYmplY3QuY3JlYXRlKClgLlxuZnVuY3Rpb24gaXNBcnJheShhcikge1xuICByZXR1cm4gQXJyYXkuaXNBcnJheShhcik7XG59XG5leHBvcnRzLmlzQXJyYXkgPSBpc0FycmF5O1xuXG5mdW5jdGlvbiBpc0Jvb2xlYW4oYXJnKSB7XG4gIHJldHVybiB0eXBlb2YgYXJnID09PSAnYm9vbGVhbic7XG59XG5leHBvcnRzLmlzQm9vbGVhbiA9IGlzQm9vbGVhbjtcblxuZnVuY3Rpb24gaXNOdWxsKGFyZykge1xuICByZXR1cm4gYXJnID09PSBudWxsO1xufVxuZXhwb3J0cy5pc051bGwgPSBpc051bGw7XG5cbmZ1bmN0aW9uIGlzTnVsbE9yVW5kZWZpbmVkKGFyZykge1xuICByZXR1cm4gYXJnID09IG51bGw7XG59XG5leHBvcnRzLmlzTnVsbE9yVW5kZWZpbmVkID0gaXNOdWxsT3JVbmRlZmluZWQ7XG5cbmZ1bmN0aW9uIGlzTnVtYmVyKGFyZykge1xuICByZXR1cm4gdHlwZW9mIGFyZyA9PT0gJ251bWJlcic7XG59XG5leHBvcnRzLmlzTnVtYmVyID0gaXNOdW1iZXI7XG5cbmZ1bmN0aW9uIGlzU3RyaW5nKGFyZykge1xuICByZXR1cm4gdHlwZW9mIGFyZyA9PT0gJ3N0cmluZyc7XG59XG5leHBvcnRzLmlzU3RyaW5nID0gaXNTdHJpbmc7XG5cbmZ1bmN0aW9uIGlzU3ltYm9sKGFyZykge1xuICByZXR1cm4gdHlwZW9mIGFyZyA9PT0gJ3N5bWJvbCc7XG59XG5leHBvcnRzLmlzU3ltYm9sID0gaXNTeW1ib2w7XG5cbmZ1bmN0aW9uIGlzVW5kZWZpbmVkKGFyZykge1xuICByZXR1cm4gYXJnID09PSB2b2lkIDA7XG59XG5leHBvcnRzLmlzVW5kZWZpbmVkID0gaXNVbmRlZmluZWQ7XG5cbmZ1bmN0aW9uIGlzUmVnRXhwKHJlKSB7XG4gIHJldHVybiBpc09iamVjdChyZSkgJiYgb2JqZWN0VG9TdHJpbmcocmUpID09PSAnW29iamVjdCBSZWdFeHBdJztcbn1cbmV4cG9ydHMuaXNSZWdFeHAgPSBpc1JlZ0V4cDtcblxuZnVuY3Rpb24gaXNPYmplY3QoYXJnKSB7XG4gIHJldHVybiB0eXBlb2YgYXJnID09PSAnb2JqZWN0JyAmJiBhcmcgIT09IG51bGw7XG59XG5leHBvcnRzLmlzT2JqZWN0ID0gaXNPYmplY3Q7XG5cbmZ1bmN0aW9uIGlzRGF0ZShkKSB7XG4gIHJldHVybiBpc09iamVjdChkKSAmJiBvYmplY3RUb1N0cmluZyhkKSA9PT0gJ1tvYmplY3QgRGF0ZV0nO1xufVxuZXhwb3J0cy5pc0RhdGUgPSBpc0RhdGU7XG5cbmZ1bmN0aW9uIGlzRXJyb3IoZSkge1xuICByZXR1cm4gaXNPYmplY3QoZSkgJiZcbiAgICAgIChvYmplY3RUb1N0cmluZyhlKSA9PT0gJ1tvYmplY3QgRXJyb3JdJyB8fCBlIGluc3RhbmNlb2YgRXJyb3IpO1xufVxuZXhwb3J0cy5pc0Vycm9yID0gaXNFcnJvcjtcblxuZnVuY3Rpb24gaXNGdW5jdGlvbihhcmcpIHtcbiAgcmV0dXJuIHR5cGVvZiBhcmcgPT09ICdmdW5jdGlvbic7XG59XG5leHBvcnRzLmlzRnVuY3Rpb24gPSBpc0Z1bmN0aW9uO1xuXG5mdW5jdGlvbiBpc1ByaW1pdGl2ZShhcmcpIHtcbiAgcmV0dXJuIGFyZyA9PT0gbnVsbCB8fFxuICAgICAgICAgdHlwZW9mIGFyZyA9PT0gJ2Jvb2xlYW4nIHx8XG4gICAgICAgICB0eXBlb2YgYXJnID09PSAnbnVtYmVyJyB8fFxuICAgICAgICAgdHlwZW9mIGFyZyA9PT0gJ3N0cmluZycgfHxcbiAgICAgICAgIHR5cGVvZiBhcmcgPT09ICdzeW1ib2wnIHx8ICAvLyBFUzYgc3ltYm9sXG4gICAgICAgICB0eXBlb2YgYXJnID09PSAndW5kZWZpbmVkJztcbn1cbmV4cG9ydHMuaXNQcmltaXRpdmUgPSBpc1ByaW1pdGl2ZTtcblxuZXhwb3J0cy5pc0J1ZmZlciA9IF9kZXJlcV8oJy4vc3VwcG9ydC9pc0J1ZmZlcicpO1xuXG5mdW5jdGlvbiBvYmplY3RUb1N0cmluZyhvKSB7XG4gIHJldHVybiBPYmplY3QucHJvdG90eXBlLnRvU3RyaW5nLmNhbGwobyk7XG59XG5cblxuZnVuY3Rpb24gcGFkKG4pIHtcbiAgcmV0dXJuIG4gPCAxMCA/ICcwJyArIG4udG9TdHJpbmcoMTApIDogbi50b1N0cmluZygxMCk7XG59XG5cblxudmFyIG1vbnRocyA9IFsnSmFuJywgJ0ZlYicsICdNYXInLCAnQXByJywgJ01heScsICdKdW4nLCAnSnVsJywgJ0F1ZycsICdTZXAnLFxuICAgICAgICAgICAgICAnT2N0JywgJ05vdicsICdEZWMnXTtcblxuLy8gMjYgRmViIDE2OjE5OjM0XG5mdW5jdGlvbiB0aW1lc3RhbXAoKSB7XG4gIHZhciBkID0gbmV3IERhdGUoKTtcbiAgdmFyIHRpbWUgPSBbcGFkKGQuZ2V0SG91cnMoKSksXG4gICAgICAgICAgICAgIHBhZChkLmdldE1pbnV0ZXMoKSksXG4gICAgICAgICAgICAgIHBhZChkLmdldFNlY29uZHMoKSldLmpvaW4oJzonKTtcbiAgcmV0dXJuIFtkLmdldERhdGUoKSwgbW9udGhzW2QuZ2V0TW9udGgoKV0sIHRpbWVdLmpvaW4oJyAnKTtcbn1cblxuXG4vLyBsb2cgaXMganVzdCBhIHRoaW4gd3JhcHBlciB0byBjb25zb2xlLmxvZyB0aGF0IHByZXBlbmRzIGEgdGltZXN0YW1wXG5leHBvcnRzLmxvZyA9IGZ1bmN0aW9uKCkge1xuICBjb25zb2xlLmxvZygnJXMgLSAlcycsIHRpbWVzdGFtcCgpLCBleHBvcnRzLmZvcm1hdC5hcHBseShleHBvcnRzLCBhcmd1bWVudHMpKTtcbn07XG5cblxuLyoqXG4gKiBJbmhlcml0IHRoZSBwcm90b3R5cGUgbWV0aG9kcyBmcm9tIG9uZSBjb25zdHJ1Y3RvciBpbnRvIGFub3RoZXIuXG4gKlxuICogVGhlIEZ1bmN0aW9uLnByb3RvdHlwZS5pbmhlcml0cyBmcm9tIGxhbmcuanMgcmV3cml0dGVuIGFzIGEgc3RhbmRhbG9uZVxuICogZnVuY3Rpb24gKG5vdCBvbiBGdW5jdGlvbi5wcm90b3R5cGUpLiBOT1RFOiBJZiB0aGlzIGZpbGUgaXMgdG8gYmUgbG9hZGVkXG4gKiBkdXJpbmcgYm9vdHN0cmFwcGluZyB0aGlzIGZ1bmN0aW9uIG5lZWRzIHRvIGJlIHJld3JpdHRlbiB1c2luZyBzb21lIG5hdGl2ZVxuICogZnVuY3Rpb25zIGFzIHByb3RvdHlwZSBzZXR1cCB1c2luZyBub3JtYWwgSmF2YVNjcmlwdCBkb2VzIG5vdCB3b3JrIGFzXG4gKiBleHBlY3RlZCBkdXJpbmcgYm9vdHN0cmFwcGluZyAoc2VlIG1pcnJvci5qcyBpbiByMTE0OTAzKS5cbiAqXG4gKiBAcGFyYW0ge2Z1bmN0aW9ufSBjdG9yIENvbnN0cnVjdG9yIGZ1bmN0aW9uIHdoaWNoIG5lZWRzIHRvIGluaGVyaXQgdGhlXG4gKiAgICAgcHJvdG90eXBlLlxuICogQHBhcmFtIHtmdW5jdGlvbn0gc3VwZXJDdG9yIENvbnN0cnVjdG9yIGZ1bmN0aW9uIHRvIGluaGVyaXQgcHJvdG90eXBlIGZyb20uXG4gKi9cbmV4cG9ydHMuaW5oZXJpdHMgPSBfZGVyZXFfKCdpbmhlcml0cycpO1xuXG5leHBvcnRzLl9leHRlbmQgPSBmdW5jdGlvbihvcmlnaW4sIGFkZCkge1xuICAvLyBEb24ndCBkbyBhbnl0aGluZyBpZiBhZGQgaXNuJ3QgYW4gb2JqZWN0XG4gIGlmICghYWRkIHx8ICFpc09iamVjdChhZGQpKSByZXR1cm4gb3JpZ2luO1xuXG4gIHZhciBrZXlzID0gT2JqZWN0LmtleXMoYWRkKTtcbiAgdmFyIGkgPSBrZXlzLmxlbmd0aDtcbiAgd2hpbGUgKGktLSkge1xuICAgIG9yaWdpbltrZXlzW2ldXSA9IGFkZFtrZXlzW2ldXTtcbiAgfVxuICByZXR1cm4gb3JpZ2luO1xufTtcblxuZnVuY3Rpb24gaGFzT3duUHJvcGVydHkob2JqLCBwcm9wKSB7XG4gIHJldHVybiBPYmplY3QucHJvdG90eXBlLmhhc093blByb3BlcnR5LmNhbGwob2JqLCBwcm9wKTtcbn1cblxufSkuY2FsbCh0aGlzLF9kZXJlcV8oJ19wcm9jZXNzJyksdHlwZW9mIGdsb2JhbCAhPT0gXCJ1bmRlZmluZWRcIiA/IGdsb2JhbCA6IHR5cGVvZiBzZWxmICE9PSBcInVuZGVmaW5lZFwiID8gc2VsZiA6IHR5cGVvZiB3aW5kb3cgIT09IFwidW5kZWZpbmVkXCIgPyB3aW5kb3cgOiB7fSlcbn0se1wiLi9zdXBwb3J0L2lzQnVmZmVyXCI6NCxcIl9wcm9jZXNzXCI6MyxcImluaGVyaXRzXCI6Mn1dLDY6W2Z1bmN0aW9uKF9kZXJlcV8sbW9kdWxlLGV4cG9ydHMpe1xuLy8gQSByZWN1cnNpdmUgZGVzY2VudCBwYXJzZXIgb3BlcmF0ZXMgYnkgZGVmaW5pbmcgZnVuY3Rpb25zIGZvciBhbGxcbi8vIHN5bnRhY3RpYyBlbGVtZW50cywgYW5kIHJlY3Vyc2l2ZWx5IGNhbGxpbmcgdGhvc2UsIGVhY2ggZnVuY3Rpb25cbi8vIGFkdmFuY2luZyB0aGUgaW5wdXQgc3RyZWFtIGFuZCByZXR1cm5pbmcgYW4gQVNUIG5vZGUuIFByZWNlZGVuY2Vcbi8vIG9mIGNvbnN0cnVjdHMgKGZvciBleGFtcGxlLCB0aGUgZmFjdCB0aGF0IGAheFsxXWAgbWVhbnMgYCEoeFsxXSlgXG4vLyBpbnN0ZWFkIG9mIGAoIXgpWzFdYCBpcyBoYW5kbGVkIGJ5IHRoZSBmYWN0IHRoYXQgdGhlIHBhcnNlclxuLy8gZnVuY3Rpb24gdGhhdCBwYXJzZXMgdW5hcnkgcHJlZml4IG9wZXJhdG9ycyBpcyBjYWxsZWQgZmlyc3QsIGFuZFxuLy8gaW4gdHVybiBjYWxscyB0aGUgZnVuY3Rpb24gdGhhdCBwYXJzZXMgYFtdYCBzdWJzY3JpcHRzIOKAlCB0aGF0XG4vLyB3YXksIGl0J2xsIHJlY2VpdmUgdGhlIG5vZGUgZm9yIGB4WzFdYCBhbHJlYWR5IHBhcnNlZCwgYW5kIHdyYXBzXG4vLyAqdGhhdCogaW4gdGhlIHVuYXJ5IG9wZXJhdG9yIG5vZGUuXG4vL1xuLy8gQWNvcm4gdXNlcyBhbiBbb3BlcmF0b3IgcHJlY2VkZW5jZSBwYXJzZXJdW29wcF0gdG8gaGFuZGxlIGJpbmFyeVxuLy8gb3BlcmF0b3IgcHJlY2VkZW5jZSwgYmVjYXVzZSBpdCBpcyBtdWNoIG1vcmUgY29tcGFjdCB0aGFuIHVzaW5nXG4vLyB0aGUgdGVjaG5pcXVlIG91dGxpbmVkIGFib3ZlLCB3aGljaCB1c2VzIGRpZmZlcmVudCwgbmVzdGluZ1xuLy8gZnVuY3Rpb25zIHRvIHNwZWNpZnkgcHJlY2VkZW5jZSwgZm9yIGFsbCBvZiB0aGUgdGVuIGJpbmFyeVxuLy8gcHJlY2VkZW5jZSBsZXZlbHMgdGhhdCBKYXZhU2NyaXB0IGRlZmluZXMuXG4vL1xuLy8gW29wcF06IGh0dHA6Ly9lbi53aWtpcGVkaWEub3JnL3dpa2kvT3BlcmF0b3ItcHJlY2VkZW5jZV9wYXJzZXJcblxuXCJ1c2Ugc3RyaWN0XCI7XG5cbnZhciB0dCA9IF9kZXJlcV8oXCIuL3Rva2VudHlwZVwiKS50eXBlcztcblxudmFyIFBhcnNlciA9IF9kZXJlcV8oXCIuL3N0YXRlXCIpLlBhcnNlcjtcblxudmFyIHJlc2VydmVkV29yZHMgPSBfZGVyZXFfKFwiLi9pZGVudGlmaWVyXCIpLnJlc2VydmVkV29yZHM7XG5cbnZhciBoYXMgPSBfZGVyZXFfKFwiLi91dGlsXCIpLmhhcztcblxudmFyIHBwID0gUGFyc2VyLnByb3RvdHlwZTtcblxuLy8gQ2hlY2sgaWYgcHJvcGVydHkgbmFtZSBjbGFzaGVzIHdpdGggYWxyZWFkeSBhZGRlZC5cbi8vIE9iamVjdC9jbGFzcyBnZXR0ZXJzIGFuZCBzZXR0ZXJzIGFyZSBub3QgYWxsb3dlZCB0byBjbGFzaCDigJRcbi8vIGVpdGhlciB3aXRoIGVhY2ggb3RoZXIgb3Igd2l0aCBhbiBpbml0IHByb3BlcnR5IOKAlCBhbmQgaW5cbi8vIHN0cmljdCBtb2RlLCBpbml0IHByb3BlcnRpZXMgYXJlIGFsc28gbm90IGFsbG93ZWQgdG8gYmUgcmVwZWF0ZWQuXG5cbnBwLmNoZWNrUHJvcENsYXNoID0gZnVuY3Rpb24gKHByb3AsIHByb3BIYXNoKSB7XG4gIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNikgcmV0dXJuO1xuICB2YXIga2V5ID0gcHJvcC5rZXksXG4gICAgICBuYW1lID0gdW5kZWZpbmVkO1xuICBzd2l0Y2ggKGtleS50eXBlKSB7XG4gICAgY2FzZSBcIklkZW50aWZpZXJcIjpcbiAgICAgIG5hbWUgPSBrZXkubmFtZTticmVhaztcbiAgICBjYXNlIFwiTGl0ZXJhbFwiOlxuICAgICAgbmFtZSA9IFN0cmluZyhrZXkudmFsdWUpO2JyZWFrO1xuICAgIGRlZmF1bHQ6XG4gICAgICByZXR1cm47XG4gIH1cbiAgdmFyIGtpbmQgPSBwcm9wLmtpbmQgfHwgXCJpbml0XCIsXG4gICAgICBvdGhlciA9IHVuZGVmaW5lZDtcbiAgaWYgKGhhcyhwcm9wSGFzaCwgbmFtZSkpIHtcbiAgICBvdGhlciA9IHByb3BIYXNoW25hbWVdO1xuICAgIHZhciBpc0dldFNldCA9IGtpbmQgIT09IFwiaW5pdFwiO1xuICAgIGlmICgodGhpcy5zdHJpY3QgfHwgaXNHZXRTZXQpICYmIG90aGVyW2tpbmRdIHx8ICEoaXNHZXRTZXQgXiBvdGhlci5pbml0KSkgdGhpcy5yYWlzZShrZXkuc3RhcnQsIFwiUmVkZWZpbml0aW9uIG9mIHByb3BlcnR5XCIpO1xuICB9IGVsc2Uge1xuICAgIG90aGVyID0gcHJvcEhhc2hbbmFtZV0gPSB7XG4gICAgICBpbml0OiBmYWxzZSxcbiAgICAgIGdldDogZmFsc2UsXG4gICAgICBzZXQ6IGZhbHNlXG4gICAgfTtcbiAgfVxuICBvdGhlcltraW5kXSA9IHRydWU7XG59O1xuXG4vLyAjIyMgRXhwcmVzc2lvbiBwYXJzaW5nXG5cbi8vIFRoZXNlIG5lc3QsIGZyb20gdGhlIG1vc3QgZ2VuZXJhbCBleHByZXNzaW9uIHR5cGUgYXQgdGhlIHRvcCB0b1xuLy8gJ2F0b21pYycsIG5vbmRpdmlzaWJsZSBleHByZXNzaW9uIHR5cGVzIGF0IHRoZSBib3R0b20uIE1vc3Qgb2Zcbi8vIHRoZSBmdW5jdGlvbnMgd2lsbCBzaW1wbHkgbGV0IHRoZSBmdW5jdGlvbihzKSBiZWxvdyB0aGVtIHBhcnNlLFxuLy8gYW5kLCAqaWYqIHRoZSBzeW50YWN0aWMgY29uc3RydWN0IHRoZXkgaGFuZGxlIGlzIHByZXNlbnQsIHdyYXBcbi8vIHRoZSBBU1Qgbm9kZSB0aGF0IHRoZSBpbm5lciBwYXJzZXIgZ2F2ZSB0aGVtIGluIGFub3RoZXIgbm9kZS5cblxuLy8gUGFyc2UgYSBmdWxsIGV4cHJlc3Npb24uIFRoZSBvcHRpb25hbCBhcmd1bWVudHMgYXJlIHVzZWQgdG9cbi8vIGZvcmJpZCB0aGUgYGluYCBvcGVyYXRvciAoaW4gZm9yIGxvb3BzIGluaXRhbGl6YXRpb24gZXhwcmVzc2lvbnMpXG4vLyBhbmQgcHJvdmlkZSByZWZlcmVuY2UgZm9yIHN0b3JpbmcgJz0nIG9wZXJhdG9yIGluc2lkZSBzaG9ydGhhbmRcbi8vIHByb3BlcnR5IGFzc2lnbm1lbnQgaW4gY29udGV4dHMgd2hlcmUgYm90aCBvYmplY3QgZXhwcmVzc2lvblxuLy8gYW5kIG9iamVjdCBwYXR0ZXJuIG1pZ2h0IGFwcGVhciAoc28gaXQncyBwb3NzaWJsZSB0byByYWlzZVxuLy8gZGVsYXllZCBzeW50YXggZXJyb3IgYXQgY29ycmVjdCBwb3NpdGlvbikuXG5cbnBwLnBhcnNlRXhwcmVzc2lvbiA9IGZ1bmN0aW9uIChub0luLCByZWZTaG9ydGhhbmREZWZhdWx0UG9zKSB7XG4gIHZhciBzdGFydFBvcyA9IHRoaXMuc3RhcnQsXG4gICAgICBzdGFydExvYyA9IHRoaXMuc3RhcnRMb2M7XG4gIHZhciBleHByID0gdGhpcy5wYXJzZU1heWJlQXNzaWduKG5vSW4sIHJlZlNob3J0aGFuZERlZmF1bHRQb3MpO1xuICBpZiAodGhpcy50eXBlID09PSB0dC5jb21tYSkge1xuICAgIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGVBdChzdGFydFBvcywgc3RhcnRMb2MpO1xuICAgIG5vZGUuZXhwcmVzc2lvbnMgPSBbZXhwcl07XG4gICAgd2hpbGUgKHRoaXMuZWF0KHR0LmNvbW1hKSkgbm9kZS5leHByZXNzaW9ucy5wdXNoKHRoaXMucGFyc2VNYXliZUFzc2lnbihub0luLCByZWZTaG9ydGhhbmREZWZhdWx0UG9zKSk7XG4gICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIlNlcXVlbmNlRXhwcmVzc2lvblwiKTtcbiAgfVxuICByZXR1cm4gZXhwcjtcbn07XG5cbi8vIFBhcnNlIGFuIGFzc2lnbm1lbnQgZXhwcmVzc2lvbi4gVGhpcyBpbmNsdWRlcyBhcHBsaWNhdGlvbnMgb2Zcbi8vIG9wZXJhdG9ycyBsaWtlIGArPWAuXG5cbnBwLnBhcnNlTWF5YmVBc3NpZ24gPSBmdW5jdGlvbiAobm9JbiwgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcywgYWZ0ZXJMZWZ0UGFyc2UpIHtcbiAgaWYgKHRoaXMudHlwZSA9PSB0dC5feWllbGQgJiYgdGhpcy5pbkdlbmVyYXRvcikgcmV0dXJuIHRoaXMucGFyc2VZaWVsZCgpO1xuXG4gIHZhciBmYWlsT25TaG9ydGhhbmRBc3NpZ24gPSB1bmRlZmluZWQ7XG4gIGlmICghcmVmU2hvcnRoYW5kRGVmYXVsdFBvcykge1xuICAgIHJlZlNob3J0aGFuZERlZmF1bHRQb3MgPSB7IHN0YXJ0OiAwIH07XG4gICAgZmFpbE9uU2hvcnRoYW5kQXNzaWduID0gdHJ1ZTtcbiAgfSBlbHNlIHtcbiAgICBmYWlsT25TaG9ydGhhbmRBc3NpZ24gPSBmYWxzZTtcbiAgfVxuICB2YXIgc3RhcnRQb3MgPSB0aGlzLnN0YXJ0LFxuICAgICAgc3RhcnRMb2MgPSB0aGlzLnN0YXJ0TG9jO1xuICBpZiAodGhpcy50eXBlID09IHR0LnBhcmVuTCB8fCB0aGlzLnR5cGUgPT0gdHQubmFtZSkgdGhpcy5wb3RlbnRpYWxBcnJvd0F0ID0gdGhpcy5zdGFydDtcbiAgdmFyIGxlZnQgPSB0aGlzLnBhcnNlTWF5YmVDb25kaXRpb25hbChub0luLCByZWZTaG9ydGhhbmREZWZhdWx0UG9zKTtcbiAgaWYgKGFmdGVyTGVmdFBhcnNlKSBsZWZ0ID0gYWZ0ZXJMZWZ0UGFyc2UuY2FsbCh0aGlzLCBsZWZ0LCBzdGFydFBvcywgc3RhcnRMb2MpO1xuICBpZiAodGhpcy50eXBlLmlzQXNzaWduKSB7XG4gICAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0UG9zLCBzdGFydExvYyk7XG4gICAgbm9kZS5vcGVyYXRvciA9IHRoaXMudmFsdWU7XG4gICAgbm9kZS5sZWZ0ID0gdGhpcy50eXBlID09PSB0dC5lcSA/IHRoaXMudG9Bc3NpZ25hYmxlKGxlZnQpIDogbGVmdDtcbiAgICByZWZTaG9ydGhhbmREZWZhdWx0UG9zLnN0YXJ0ID0gMDsgLy8gcmVzZXQgYmVjYXVzZSBzaG9ydGhhbmQgZGVmYXVsdCB3YXMgdXNlZCBjb3JyZWN0bHlcbiAgICB0aGlzLmNoZWNrTFZhbChsZWZ0KTtcbiAgICB0aGlzLm5leHQoKTtcbiAgICBub2RlLnJpZ2h0ID0gdGhpcy5wYXJzZU1heWJlQXNzaWduKG5vSW4pO1xuICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJBc3NpZ25tZW50RXhwcmVzc2lvblwiKTtcbiAgfSBlbHNlIGlmIChmYWlsT25TaG9ydGhhbmRBc3NpZ24gJiYgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcy5zdGFydCkge1xuICAgIHRoaXMudW5leHBlY3RlZChyZWZTaG9ydGhhbmREZWZhdWx0UG9zLnN0YXJ0KTtcbiAgfVxuICByZXR1cm4gbGVmdDtcbn07XG5cbi8vIFBhcnNlIGEgdGVybmFyeSBjb25kaXRpb25hbCAoYD86YCkgb3BlcmF0b3IuXG5cbnBwLnBhcnNlTWF5YmVDb25kaXRpb25hbCA9IGZ1bmN0aW9uIChub0luLCByZWZTaG9ydGhhbmREZWZhdWx0UG9zKSB7XG4gIHZhciBzdGFydFBvcyA9IHRoaXMuc3RhcnQsXG4gICAgICBzdGFydExvYyA9IHRoaXMuc3RhcnRMb2M7XG4gIHZhciBleHByID0gdGhpcy5wYXJzZUV4cHJPcHMobm9JbiwgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcyk7XG4gIGlmIChyZWZTaG9ydGhhbmREZWZhdWx0UG9zICYmIHJlZlNob3J0aGFuZERlZmF1bHRQb3Muc3RhcnQpIHJldHVybiBleHByO1xuICBpZiAodGhpcy5lYXQodHQucXVlc3Rpb24pKSB7XG4gICAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0UG9zLCBzdGFydExvYyk7XG4gICAgbm9kZS50ZXN0ID0gZXhwcjtcbiAgICBub2RlLmNvbnNlcXVlbnQgPSB0aGlzLnBhcnNlTWF5YmVBc3NpZ24oKTtcbiAgICB0aGlzLmV4cGVjdCh0dC5jb2xvbik7XG4gICAgbm9kZS5hbHRlcm5hdGUgPSB0aGlzLnBhcnNlTWF5YmVBc3NpZ24obm9Jbik7XG4gICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkNvbmRpdGlvbmFsRXhwcmVzc2lvblwiKTtcbiAgfVxuICByZXR1cm4gZXhwcjtcbn07XG5cbi8vIFN0YXJ0IHRoZSBwcmVjZWRlbmNlIHBhcnNlci5cblxucHAucGFyc2VFeHByT3BzID0gZnVuY3Rpb24gKG5vSW4sIHJlZlNob3J0aGFuZERlZmF1bHRQb3MpIHtcbiAgdmFyIHN0YXJ0UG9zID0gdGhpcy5zdGFydCxcbiAgICAgIHN0YXJ0TG9jID0gdGhpcy5zdGFydExvYztcbiAgdmFyIGV4cHIgPSB0aGlzLnBhcnNlTWF5YmVVbmFyeShyZWZTaG9ydGhhbmREZWZhdWx0UG9zKTtcbiAgaWYgKHJlZlNob3J0aGFuZERlZmF1bHRQb3MgJiYgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcy5zdGFydCkgcmV0dXJuIGV4cHI7XG4gIHJldHVybiB0aGlzLnBhcnNlRXhwck9wKGV4cHIsIHN0YXJ0UG9zLCBzdGFydExvYywgLTEsIG5vSW4pO1xufTtcblxuLy8gUGFyc2UgYmluYXJ5IG9wZXJhdG9ycyB3aXRoIHRoZSBvcGVyYXRvciBwcmVjZWRlbmNlIHBhcnNpbmdcbi8vIGFsZ29yaXRobS4gYGxlZnRgIGlzIHRoZSBsZWZ0LWhhbmQgc2lkZSBvZiB0aGUgb3BlcmF0b3IuXG4vLyBgbWluUHJlY2AgcHJvdmlkZXMgY29udGV4dCB0aGF0IGFsbG93cyB0aGUgZnVuY3Rpb24gdG8gc3RvcCBhbmRcbi8vIGRlZmVyIGZ1cnRoZXIgcGFyc2VyIHRvIG9uZSBvZiBpdHMgY2FsbGVycyB3aGVuIGl0IGVuY291bnRlcnMgYW5cbi8vIG9wZXJhdG9yIHRoYXQgaGFzIGEgbG93ZXIgcHJlY2VkZW5jZSB0aGFuIHRoZSBzZXQgaXQgaXMgcGFyc2luZy5cblxucHAucGFyc2VFeHByT3AgPSBmdW5jdGlvbiAobGVmdCwgbGVmdFN0YXJ0UG9zLCBsZWZ0U3RhcnRMb2MsIG1pblByZWMsIG5vSW4pIHtcbiAgdmFyIHByZWMgPSB0aGlzLnR5cGUuYmlub3A7XG4gIGlmIChBcnJheS5pc0FycmF5KGxlZnRTdGFydFBvcykpIHtcbiAgICBpZiAodGhpcy5vcHRpb25zLmxvY2F0aW9ucyAmJiBub0luID09PSB1bmRlZmluZWQpIHtcbiAgICAgIC8vIHNoaWZ0IGFyZ3VtZW50cyB0byBsZWZ0IGJ5IG9uZVxuICAgICAgbm9JbiA9IG1pblByZWM7XG4gICAgICBtaW5QcmVjID0gbGVmdFN0YXJ0TG9jO1xuICAgICAgLy8gZmxhdHRlbiBsZWZ0U3RhcnRQb3NcbiAgICAgIGxlZnRTdGFydExvYyA9IGxlZnRTdGFydFBvc1sxXTtcbiAgICAgIGxlZnRTdGFydFBvcyA9IGxlZnRTdGFydFBvc1swXTtcbiAgICB9XG4gIH1cbiAgaWYgKHByZWMgIT0gbnVsbCAmJiAoIW5vSW4gfHwgdGhpcy50eXBlICE9PSB0dC5faW4pKSB7XG4gICAgaWYgKHByZWMgPiBtaW5QcmVjKSB7XG4gICAgICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlQXQobGVmdFN0YXJ0UG9zLCBsZWZ0U3RhcnRMb2MpO1xuICAgICAgbm9kZS5sZWZ0ID0gbGVmdDtcbiAgICAgIG5vZGUub3BlcmF0b3IgPSB0aGlzLnZhbHVlO1xuICAgICAgdmFyIG9wID0gdGhpcy50eXBlO1xuICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICB2YXIgc3RhcnRQb3MgPSB0aGlzLnN0YXJ0LFxuICAgICAgICAgIHN0YXJ0TG9jID0gdGhpcy5zdGFydExvYztcbiAgICAgIG5vZGUucmlnaHQgPSB0aGlzLnBhcnNlRXhwck9wKHRoaXMucGFyc2VNYXliZVVuYXJ5KCksIHN0YXJ0UG9zLCBzdGFydExvYywgcHJlYywgbm9Jbik7XG4gICAgICB0aGlzLmZpbmlzaE5vZGUobm9kZSwgb3AgPT09IHR0LmxvZ2ljYWxPUiB8fCBvcCA9PT0gdHQubG9naWNhbEFORCA/IFwiTG9naWNhbEV4cHJlc3Npb25cIiA6IFwiQmluYXJ5RXhwcmVzc2lvblwiKTtcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlRXhwck9wKG5vZGUsIGxlZnRTdGFydFBvcywgbGVmdFN0YXJ0TG9jLCBtaW5QcmVjLCBub0luKTtcbiAgICB9XG4gIH1cbiAgcmV0dXJuIGxlZnQ7XG59O1xuXG4vLyBQYXJzZSB1bmFyeSBvcGVyYXRvcnMsIGJvdGggcHJlZml4IGFuZCBwb3N0Zml4LlxuXG5wcC5wYXJzZU1heWJlVW5hcnkgPSBmdW5jdGlvbiAocmVmU2hvcnRoYW5kRGVmYXVsdFBvcykge1xuICBpZiAodGhpcy50eXBlLnByZWZpeCkge1xuICAgIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGUoKSxcbiAgICAgICAgdXBkYXRlID0gdGhpcy50eXBlID09PSB0dC5pbmNEZWM7XG4gICAgbm9kZS5vcGVyYXRvciA9IHRoaXMudmFsdWU7XG4gICAgbm9kZS5wcmVmaXggPSB0cnVlO1xuICAgIHRoaXMubmV4dCgpO1xuICAgIG5vZGUuYXJndW1lbnQgPSB0aGlzLnBhcnNlTWF5YmVVbmFyeSgpO1xuICAgIGlmIChyZWZTaG9ydGhhbmREZWZhdWx0UG9zICYmIHJlZlNob3J0aGFuZERlZmF1bHRQb3Muc3RhcnQpIHRoaXMudW5leHBlY3RlZChyZWZTaG9ydGhhbmREZWZhdWx0UG9zLnN0YXJ0KTtcbiAgICBpZiAodXBkYXRlKSB0aGlzLmNoZWNrTFZhbChub2RlLmFyZ3VtZW50KTtlbHNlIGlmICh0aGlzLnN0cmljdCAmJiBub2RlLm9wZXJhdG9yID09PSBcImRlbGV0ZVwiICYmIG5vZGUuYXJndW1lbnQudHlwZSA9PT0gXCJJZGVudGlmaWVyXCIpIHRoaXMucmFpc2Uobm9kZS5zdGFydCwgXCJEZWxldGluZyBsb2NhbCB2YXJpYWJsZSBpbiBzdHJpY3QgbW9kZVwiKTtcbiAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIHVwZGF0ZSA/IFwiVXBkYXRlRXhwcmVzc2lvblwiIDogXCJVbmFyeUV4cHJlc3Npb25cIik7XG4gIH1cbiAgdmFyIHN0YXJ0UG9zID0gdGhpcy5zdGFydCxcbiAgICAgIHN0YXJ0TG9jID0gdGhpcy5zdGFydExvYztcbiAgdmFyIGV4cHIgPSB0aGlzLnBhcnNlRXhwclN1YnNjcmlwdHMocmVmU2hvcnRoYW5kRGVmYXVsdFBvcyk7XG4gIGlmIChyZWZTaG9ydGhhbmREZWZhdWx0UG9zICYmIHJlZlNob3J0aGFuZERlZmF1bHRQb3Muc3RhcnQpIHJldHVybiBleHByO1xuICB3aGlsZSAodGhpcy50eXBlLnBvc3RmaXggJiYgIXRoaXMuY2FuSW5zZXJ0U2VtaWNvbG9uKCkpIHtcbiAgICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlQXQoc3RhcnRQb3MsIHN0YXJ0TG9jKTtcbiAgICBub2RlLm9wZXJhdG9yID0gdGhpcy52YWx1ZTtcbiAgICBub2RlLnByZWZpeCA9IGZhbHNlO1xuICAgIG5vZGUuYXJndW1lbnQgPSBleHByO1xuICAgIHRoaXMuY2hlY2tMVmFsKGV4cHIpO1xuICAgIHRoaXMubmV4dCgpO1xuICAgIGV4cHIgPSB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJVcGRhdGVFeHByZXNzaW9uXCIpO1xuICB9XG4gIHJldHVybiBleHByO1xufTtcblxuLy8gUGFyc2UgY2FsbCwgZG90LCBhbmQgYFtdYC1zdWJzY3JpcHQgZXhwcmVzc2lvbnMuXG5cbnBwLnBhcnNlRXhwclN1YnNjcmlwdHMgPSBmdW5jdGlvbiAocmVmU2hvcnRoYW5kRGVmYXVsdFBvcykge1xuICB2YXIgc3RhcnRQb3MgPSB0aGlzLnN0YXJ0LFxuICAgICAgc3RhcnRMb2MgPSB0aGlzLnN0YXJ0TG9jO1xuICB2YXIgZXhwciA9IHRoaXMucGFyc2VFeHByQXRvbShyZWZTaG9ydGhhbmREZWZhdWx0UG9zKTtcbiAgaWYgKHJlZlNob3J0aGFuZERlZmF1bHRQb3MgJiYgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcy5zdGFydCkgcmV0dXJuIGV4cHI7XG4gIHJldHVybiB0aGlzLnBhcnNlU3Vic2NyaXB0cyhleHByLCBzdGFydFBvcywgc3RhcnRMb2MpO1xufTtcblxucHAucGFyc2VTdWJzY3JpcHRzID0gZnVuY3Rpb24gKGJhc2UsIHN0YXJ0UG9zLCBzdGFydExvYywgbm9DYWxscykge1xuICBpZiAoQXJyYXkuaXNBcnJheShzdGFydFBvcykpIHtcbiAgICBpZiAodGhpcy5vcHRpb25zLmxvY2F0aW9ucyAmJiBub0NhbGxzID09PSB1bmRlZmluZWQpIHtcbiAgICAgIC8vIHNoaWZ0IGFyZ3VtZW50cyB0byBsZWZ0IGJ5IG9uZVxuICAgICAgbm9DYWxscyA9IHN0YXJ0TG9jO1xuICAgICAgLy8gZmxhdHRlbiBzdGFydFBvc1xuICAgICAgc3RhcnRMb2MgPSBzdGFydFBvc1sxXTtcbiAgICAgIHN0YXJ0UG9zID0gc3RhcnRQb3NbMF07XG4gICAgfVxuICB9XG4gIGZvciAoOzspIHtcbiAgICBpZiAodGhpcy5lYXQodHQuZG90KSkge1xuICAgICAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0UG9zLCBzdGFydExvYyk7XG4gICAgICBub2RlLm9iamVjdCA9IGJhc2U7XG4gICAgICBub2RlLnByb3BlcnR5ID0gdGhpcy5wYXJzZUlkZW50KHRydWUpO1xuICAgICAgbm9kZS5jb21wdXRlZCA9IGZhbHNlO1xuICAgICAgYmFzZSA9IHRoaXMuZmluaXNoTm9kZShub2RlLCBcIk1lbWJlckV4cHJlc3Npb25cIik7XG4gICAgfSBlbHNlIGlmICh0aGlzLmVhdCh0dC5icmFja2V0TCkpIHtcbiAgICAgIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGVBdChzdGFydFBvcywgc3RhcnRMb2MpO1xuICAgICAgbm9kZS5vYmplY3QgPSBiYXNlO1xuICAgICAgbm9kZS5wcm9wZXJ0eSA9IHRoaXMucGFyc2VFeHByZXNzaW9uKCk7XG4gICAgICBub2RlLmNvbXB1dGVkID0gdHJ1ZTtcbiAgICAgIHRoaXMuZXhwZWN0KHR0LmJyYWNrZXRSKTtcbiAgICAgIGJhc2UgPSB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJNZW1iZXJFeHByZXNzaW9uXCIpO1xuICAgIH0gZWxzZSBpZiAoIW5vQ2FsbHMgJiYgdGhpcy5lYXQodHQucGFyZW5MKSkge1xuICAgICAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0UG9zLCBzdGFydExvYyk7XG4gICAgICBub2RlLmNhbGxlZSA9IGJhc2U7XG4gICAgICBub2RlLmFyZ3VtZW50cyA9IHRoaXMucGFyc2VFeHByTGlzdCh0dC5wYXJlblIsIGZhbHNlKTtcbiAgICAgIGJhc2UgPSB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJDYWxsRXhwcmVzc2lvblwiKTtcbiAgICB9IGVsc2UgaWYgKHRoaXMudHlwZSA9PT0gdHQuYmFja1F1b3RlKSB7XG4gICAgICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlQXQoc3RhcnRQb3MsIHN0YXJ0TG9jKTtcbiAgICAgIG5vZGUudGFnID0gYmFzZTtcbiAgICAgIG5vZGUucXVhc2kgPSB0aGlzLnBhcnNlVGVtcGxhdGUoKTtcbiAgICAgIGJhc2UgPSB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJUYWdnZWRUZW1wbGF0ZUV4cHJlc3Npb25cIik7XG4gICAgfSBlbHNlIHtcbiAgICAgIHJldHVybiBiYXNlO1xuICAgIH1cbiAgfVxufTtcblxuLy8gUGFyc2UgYW4gYXRvbWljIGV4cHJlc3Npb24g4oCUIGVpdGhlciBhIHNpbmdsZSB0b2tlbiB0aGF0IGlzIGFuXG4vLyBleHByZXNzaW9uLCBhbiBleHByZXNzaW9uIHN0YXJ0ZWQgYnkgYSBrZXl3b3JkIGxpa2UgYGZ1bmN0aW9uYCBvclxuLy8gYG5ld2AsIG9yIGFuIGV4cHJlc3Npb24gd3JhcHBlZCBpbiBwdW5jdHVhdGlvbiBsaWtlIGAoKWAsIGBbXWAsXG4vLyBvciBge31gLlxuXG5wcC5wYXJzZUV4cHJBdG9tID0gZnVuY3Rpb24gKHJlZlNob3J0aGFuZERlZmF1bHRQb3MpIHtcbiAgdmFyIG5vZGUgPSB1bmRlZmluZWQsXG4gICAgICBjYW5CZUFycm93ID0gdGhpcy5wb3RlbnRpYWxBcnJvd0F0ID09IHRoaXMuc3RhcnQ7XG4gIHN3aXRjaCAodGhpcy50eXBlKSB7XG4gICAgY2FzZSB0dC5fdGhpczpcbiAgICBjYXNlIHR0Ll9zdXBlcjpcbiAgICAgIHZhciB0eXBlID0gdGhpcy50eXBlID09PSB0dC5fdGhpcyA/IFwiVGhpc0V4cHJlc3Npb25cIiA6IFwiU3VwZXJcIjtcbiAgICAgIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIHR5cGUpO1xuXG4gICAgY2FzZSB0dC5feWllbGQ6XG4gICAgICBpZiAodGhpcy5pbkdlbmVyYXRvcikgdGhpcy51bmV4cGVjdGVkKCk7XG5cbiAgICBjYXNlIHR0Lm5hbWU6XG4gICAgICB2YXIgc3RhcnRQb3MgPSB0aGlzLnN0YXJ0LFxuICAgICAgICAgIHN0YXJ0TG9jID0gdGhpcy5zdGFydExvYztcbiAgICAgIHZhciBpZCA9IHRoaXMucGFyc2VJZGVudCh0aGlzLnR5cGUgIT09IHR0Lm5hbWUpO1xuICAgICAgaWYgKGNhbkJlQXJyb3cgJiYgIXRoaXMuY2FuSW5zZXJ0U2VtaWNvbG9uKCkgJiYgdGhpcy5lYXQodHQuYXJyb3cpKSByZXR1cm4gdGhpcy5wYXJzZUFycm93RXhwcmVzc2lvbih0aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0UG9zLCBzdGFydExvYyksIFtpZF0pO1xuICAgICAgcmV0dXJuIGlkO1xuXG4gICAgY2FzZSB0dC5yZWdleHA6XG4gICAgICB2YXIgdmFsdWUgPSB0aGlzLnZhbHVlO1xuICAgICAgbm9kZSA9IHRoaXMucGFyc2VMaXRlcmFsKHZhbHVlLnZhbHVlKTtcbiAgICAgIG5vZGUucmVnZXggPSB7IHBhdHRlcm46IHZhbHVlLnBhdHRlcm4sIGZsYWdzOiB2YWx1ZS5mbGFncyB9O1xuICAgICAgcmV0dXJuIG5vZGU7XG5cbiAgICBjYXNlIHR0Lm51bTpjYXNlIHR0LnN0cmluZzpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlTGl0ZXJhbCh0aGlzLnZhbHVlKTtcblxuICAgIGNhc2UgdHQuX251bGw6Y2FzZSB0dC5fdHJ1ZTpjYXNlIHR0Ll9mYWxzZTpcbiAgICAgIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICAgICAgbm9kZS52YWx1ZSA9IHRoaXMudHlwZSA9PT0gdHQuX251bGwgPyBudWxsIDogdGhpcy50eXBlID09PSB0dC5fdHJ1ZTtcbiAgICAgIG5vZGUucmF3ID0gdGhpcy50eXBlLmtleXdvcmQ7XG4gICAgICB0aGlzLm5leHQoKTtcbiAgICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJMaXRlcmFsXCIpO1xuXG4gICAgY2FzZSB0dC5wYXJlbkw6XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZVBhcmVuQW5kRGlzdGluZ3Vpc2hFeHByZXNzaW9uKGNhbkJlQXJyb3cpO1xuXG4gICAgY2FzZSB0dC5icmFja2V0TDpcbiAgICAgIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICAvLyBjaGVjayB3aGV0aGVyIHRoaXMgaXMgYXJyYXkgY29tcHJlaGVuc2lvbiBvciByZWd1bGFyIGFycmF5XG4gICAgICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDcgJiYgdGhpcy50eXBlID09PSB0dC5fZm9yKSB7XG4gICAgICAgIHJldHVybiB0aGlzLnBhcnNlQ29tcHJlaGVuc2lvbihub2RlLCBmYWxzZSk7XG4gICAgICB9XG4gICAgICBub2RlLmVsZW1lbnRzID0gdGhpcy5wYXJzZUV4cHJMaXN0KHR0LmJyYWNrZXRSLCB0cnVlLCB0cnVlLCByZWZTaG9ydGhhbmREZWZhdWx0UG9zKTtcbiAgICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJBcnJheUV4cHJlc3Npb25cIik7XG5cbiAgICBjYXNlIHR0LmJyYWNlTDpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlT2JqKGZhbHNlLCByZWZTaG9ydGhhbmREZWZhdWx0UG9zKTtcblxuICAgIGNhc2UgdHQuX2Z1bmN0aW9uOlxuICAgICAgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gICAgICB0aGlzLm5leHQoKTtcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlRnVuY3Rpb24obm9kZSwgZmFsc2UpO1xuXG4gICAgY2FzZSB0dC5fY2xhc3M6XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZUNsYXNzKHRoaXMuc3RhcnROb2RlKCksIGZhbHNlKTtcblxuICAgIGNhc2UgdHQuX25ldzpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlTmV3KCk7XG5cbiAgICBjYXNlIHR0LmJhY2tRdW90ZTpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlVGVtcGxhdGUoKTtcblxuICAgIGRlZmF1bHQ6XG4gICAgICB0aGlzLnVuZXhwZWN0ZWQoKTtcbiAgfVxufTtcblxucHAucGFyc2VMaXRlcmFsID0gZnVuY3Rpb24gKHZhbHVlKSB7XG4gIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgbm9kZS52YWx1ZSA9IHZhbHVlO1xuICBub2RlLnJhdyA9IHRoaXMuaW5wdXQuc2xpY2UodGhpcy5zdGFydCwgdGhpcy5lbmQpO1xuICB0aGlzLm5leHQoKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkxpdGVyYWxcIik7XG59O1xuXG5wcC5wYXJzZVBhcmVuRXhwcmVzc2lvbiA9IGZ1bmN0aW9uICgpIHtcbiAgdGhpcy5leHBlY3QodHQucGFyZW5MKTtcbiAgdmFyIHZhbCA9IHRoaXMucGFyc2VFeHByZXNzaW9uKCk7XG4gIHRoaXMuZXhwZWN0KHR0LnBhcmVuUik7XG4gIHJldHVybiB2YWw7XG59O1xuXG5wcC5wYXJzZVBhcmVuQW5kRGlzdGluZ3Vpc2hFeHByZXNzaW9uID0gZnVuY3Rpb24gKGNhbkJlQXJyb3cpIHtcbiAgdmFyIHN0YXJ0UG9zID0gdGhpcy5zdGFydCxcbiAgICAgIHN0YXJ0TG9jID0gdGhpcy5zdGFydExvYyxcbiAgICAgIHZhbCA9IHVuZGVmaW5lZDtcbiAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KSB7XG4gICAgdGhpcy5uZXh0KCk7XG5cbiAgICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDcgJiYgdGhpcy50eXBlID09PSB0dC5fZm9yKSB7XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZUNvbXByZWhlbnNpb24odGhpcy5zdGFydE5vZGVBdChzdGFydFBvcywgc3RhcnRMb2MpLCB0cnVlKTtcbiAgICB9XG5cbiAgICB2YXIgaW5uZXJTdGFydFBvcyA9IHRoaXMuc3RhcnQsXG4gICAgICAgIGlubmVyU3RhcnRMb2MgPSB0aGlzLnN0YXJ0TG9jO1xuICAgIHZhciBleHByTGlzdCA9IFtdLFxuICAgICAgICBmaXJzdCA9IHRydWU7XG4gICAgdmFyIHJlZlNob3J0aGFuZERlZmF1bHRQb3MgPSB7IHN0YXJ0OiAwIH0sXG4gICAgICAgIHNwcmVhZFN0YXJ0ID0gdW5kZWZpbmVkLFxuICAgICAgICBpbm5lclBhcmVuU3RhcnQgPSB1bmRlZmluZWQ7XG4gICAgd2hpbGUgKHRoaXMudHlwZSAhPT0gdHQucGFyZW5SKSB7XG4gICAgICBmaXJzdCA/IGZpcnN0ID0gZmFsc2UgOiB0aGlzLmV4cGVjdCh0dC5jb21tYSk7XG4gICAgICBpZiAodGhpcy50eXBlID09PSB0dC5lbGxpcHNpcykge1xuICAgICAgICBzcHJlYWRTdGFydCA9IHRoaXMuc3RhcnQ7XG4gICAgICAgIGV4cHJMaXN0LnB1c2godGhpcy5wYXJzZVBhcmVuSXRlbSh0aGlzLnBhcnNlUmVzdCgpKSk7XG4gICAgICAgIGJyZWFrO1xuICAgICAgfSBlbHNlIHtcbiAgICAgICAgaWYgKHRoaXMudHlwZSA9PT0gdHQucGFyZW5MICYmICFpbm5lclBhcmVuU3RhcnQpIHtcbiAgICAgICAgICBpbm5lclBhcmVuU3RhcnQgPSB0aGlzLnN0YXJ0O1xuICAgICAgICB9XG4gICAgICAgIGV4cHJMaXN0LnB1c2godGhpcy5wYXJzZU1heWJlQXNzaWduKGZhbHNlLCByZWZTaG9ydGhhbmREZWZhdWx0UG9zLCB0aGlzLnBhcnNlUGFyZW5JdGVtKSk7XG4gICAgICB9XG4gICAgfVxuICAgIHZhciBpbm5lckVuZFBvcyA9IHRoaXMuc3RhcnQsXG4gICAgICAgIGlubmVyRW5kTG9jID0gdGhpcy5zdGFydExvYztcbiAgICB0aGlzLmV4cGVjdCh0dC5wYXJlblIpO1xuXG4gICAgaWYgKGNhbkJlQXJyb3cgJiYgIXRoaXMuY2FuSW5zZXJ0U2VtaWNvbG9uKCkgJiYgdGhpcy5lYXQodHQuYXJyb3cpKSB7XG4gICAgICBpZiAoaW5uZXJQYXJlblN0YXJ0KSB0aGlzLnVuZXhwZWN0ZWQoaW5uZXJQYXJlblN0YXJ0KTtcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlUGFyZW5BcnJvd0xpc3Qoc3RhcnRQb3MsIHN0YXJ0TG9jLCBleHByTGlzdCk7XG4gICAgfVxuXG4gICAgaWYgKCFleHByTGlzdC5sZW5ndGgpIHRoaXMudW5leHBlY3RlZCh0aGlzLmxhc3RUb2tTdGFydCk7XG4gICAgaWYgKHNwcmVhZFN0YXJ0KSB0aGlzLnVuZXhwZWN0ZWQoc3ByZWFkU3RhcnQpO1xuICAgIGlmIChyZWZTaG9ydGhhbmREZWZhdWx0UG9zLnN0YXJ0KSB0aGlzLnVuZXhwZWN0ZWQocmVmU2hvcnRoYW5kRGVmYXVsdFBvcy5zdGFydCk7XG5cbiAgICBpZiAoZXhwckxpc3QubGVuZ3RoID4gMSkge1xuICAgICAgdmFsID0gdGhpcy5zdGFydE5vZGVBdChpbm5lclN0YXJ0UG9zLCBpbm5lclN0YXJ0TG9jKTtcbiAgICAgIHZhbC5leHByZXNzaW9ucyA9IGV4cHJMaXN0O1xuICAgICAgdGhpcy5maW5pc2hOb2RlQXQodmFsLCBcIlNlcXVlbmNlRXhwcmVzc2lvblwiLCBpbm5lckVuZFBvcywgaW5uZXJFbmRMb2MpO1xuICAgIH0gZWxzZSB7XG4gICAgICB2YWwgPSBleHByTGlzdFswXTtcbiAgICB9XG4gIH0gZWxzZSB7XG4gICAgdmFsID0gdGhpcy5wYXJzZVBhcmVuRXhwcmVzc2lvbigpO1xuICB9XG5cbiAgaWYgKHRoaXMub3B0aW9ucy5wcmVzZXJ2ZVBhcmVucykge1xuICAgIHZhciBwYXIgPSB0aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0UG9zLCBzdGFydExvYyk7XG4gICAgcGFyLmV4cHJlc3Npb24gPSB2YWw7XG4gICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShwYXIsIFwiUGFyZW50aGVzaXplZEV4cHJlc3Npb25cIik7XG4gIH0gZWxzZSB7XG4gICAgcmV0dXJuIHZhbDtcbiAgfVxufTtcblxucHAucGFyc2VQYXJlbkl0ZW0gPSBmdW5jdGlvbiAoaXRlbSkge1xuICByZXR1cm4gaXRlbTtcbn07XG5cbnBwLnBhcnNlUGFyZW5BcnJvd0xpc3QgPSBmdW5jdGlvbiAoc3RhcnRQb3MsIHN0YXJ0TG9jLCBleHByTGlzdCkge1xuICByZXR1cm4gdGhpcy5wYXJzZUFycm93RXhwcmVzc2lvbih0aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0UG9zLCBzdGFydExvYyksIGV4cHJMaXN0KTtcbn07XG5cbi8vIE5ldydzIHByZWNlZGVuY2UgaXMgc2xpZ2h0bHkgdHJpY2t5LiBJdCBtdXN0IGFsbG93IGl0cyBhcmd1bWVudFxuLy8gdG8gYmUgYSBgW11gIG9yIGRvdCBzdWJzY3JpcHQgZXhwcmVzc2lvbiwgYnV0IG5vdCBhIGNhbGwg4oCUIGF0XG4vLyBsZWFzdCwgbm90IHdpdGhvdXQgd3JhcHBpbmcgaXQgaW4gcGFyZW50aGVzZXMuIFRodXMsIGl0IHVzZXMgdGhlXG5cbnZhciBlbXB0eSA9IFtdO1xuXG5wcC5wYXJzZU5ldyA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICB2YXIgbWV0YSA9IHRoaXMucGFyc2VJZGVudCh0cnVlKTtcbiAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2ICYmIHRoaXMuZWF0KHR0LmRvdCkpIHtcbiAgICBub2RlLm1ldGEgPSBtZXRhO1xuICAgIG5vZGUucHJvcGVydHkgPSB0aGlzLnBhcnNlSWRlbnQodHJ1ZSk7XG4gICAgaWYgKG5vZGUucHJvcGVydHkubmFtZSAhPT0gXCJ0YXJnZXRcIikgdGhpcy5yYWlzZShub2RlLnByb3BlcnR5LnN0YXJ0LCBcIlRoZSBvbmx5IHZhbGlkIG1ldGEgcHJvcGVydHkgZm9yIG5ldyBpcyBuZXcudGFyZ2V0XCIpO1xuICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJNZXRhUHJvcGVydHlcIik7XG4gIH1cbiAgdmFyIHN0YXJ0UG9zID0gdGhpcy5zdGFydCxcbiAgICAgIHN0YXJ0TG9jID0gdGhpcy5zdGFydExvYztcbiAgbm9kZS5jYWxsZWUgPSB0aGlzLnBhcnNlU3Vic2NyaXB0cyh0aGlzLnBhcnNlRXhwckF0b20oKSwgc3RhcnRQb3MsIHN0YXJ0TG9jLCB0cnVlKTtcbiAgaWYgKHRoaXMuZWF0KHR0LnBhcmVuTCkpIG5vZGUuYXJndW1lbnRzID0gdGhpcy5wYXJzZUV4cHJMaXN0KHR0LnBhcmVuUiwgZmFsc2UpO2Vsc2Ugbm9kZS5hcmd1bWVudHMgPSBlbXB0eTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIk5ld0V4cHJlc3Npb25cIik7XG59O1xuXG4vLyBQYXJzZSB0ZW1wbGF0ZSBleHByZXNzaW9uLlxuXG5wcC5wYXJzZVRlbXBsYXRlRWxlbWVudCA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIGVsZW0gPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICBlbGVtLnZhbHVlID0ge1xuICAgIHJhdzogdGhpcy5pbnB1dC5zbGljZSh0aGlzLnN0YXJ0LCB0aGlzLmVuZCksXG4gICAgY29va2VkOiB0aGlzLnZhbHVlXG4gIH07XG4gIHRoaXMubmV4dCgpO1xuICBlbGVtLnRhaWwgPSB0aGlzLnR5cGUgPT09IHR0LmJhY2tRdW90ZTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShlbGVtLCBcIlRlbXBsYXRlRWxlbWVudFwiKTtcbn07XG5cbnBwLnBhcnNlVGVtcGxhdGUgPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgdGhpcy5uZXh0KCk7XG4gIG5vZGUuZXhwcmVzc2lvbnMgPSBbXTtcbiAgdmFyIGN1ckVsdCA9IHRoaXMucGFyc2VUZW1wbGF0ZUVsZW1lbnQoKTtcbiAgbm9kZS5xdWFzaXMgPSBbY3VyRWx0XTtcbiAgd2hpbGUgKCFjdXJFbHQudGFpbCkge1xuICAgIHRoaXMuZXhwZWN0KHR0LmRvbGxhckJyYWNlTCk7XG4gICAgbm9kZS5leHByZXNzaW9ucy5wdXNoKHRoaXMucGFyc2VFeHByZXNzaW9uKCkpO1xuICAgIHRoaXMuZXhwZWN0KHR0LmJyYWNlUik7XG4gICAgbm9kZS5xdWFzaXMucHVzaChjdXJFbHQgPSB0aGlzLnBhcnNlVGVtcGxhdGVFbGVtZW50KCkpO1xuICB9XG4gIHRoaXMubmV4dCgpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiVGVtcGxhdGVMaXRlcmFsXCIpO1xufTtcblxuLy8gUGFyc2UgYW4gb2JqZWN0IGxpdGVyYWwgb3IgYmluZGluZyBwYXR0ZXJuLlxuXG5wcC5wYXJzZU9iaiA9IGZ1bmN0aW9uIChpc1BhdHRlcm4sIHJlZlNob3J0aGFuZERlZmF1bHRQb3MpIHtcbiAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpLFxuICAgICAgZmlyc3QgPSB0cnVlLFxuICAgICAgcHJvcEhhc2ggPSB7fTtcbiAgbm9kZS5wcm9wZXJ0aWVzID0gW107XG4gIHRoaXMubmV4dCgpO1xuICB3aGlsZSAoIXRoaXMuZWF0KHR0LmJyYWNlUikpIHtcbiAgICBpZiAoIWZpcnN0KSB7XG4gICAgICB0aGlzLmV4cGVjdCh0dC5jb21tYSk7XG4gICAgICBpZiAodGhpcy5hZnRlclRyYWlsaW5nQ29tbWEodHQuYnJhY2VSKSkgYnJlYWs7XG4gICAgfSBlbHNlIGZpcnN0ID0gZmFsc2U7XG5cbiAgICB2YXIgcHJvcCA9IHRoaXMuc3RhcnROb2RlKCksXG4gICAgICAgIGlzR2VuZXJhdG9yID0gdW5kZWZpbmVkLFxuICAgICAgICBzdGFydFBvcyA9IHVuZGVmaW5lZCxcbiAgICAgICAgc3RhcnRMb2MgPSB1bmRlZmluZWQ7XG4gICAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KSB7XG4gICAgICBwcm9wLm1ldGhvZCA9IGZhbHNlO1xuICAgICAgcHJvcC5zaG9ydGhhbmQgPSBmYWxzZTtcbiAgICAgIGlmIChpc1BhdHRlcm4gfHwgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcykge1xuICAgICAgICBzdGFydFBvcyA9IHRoaXMuc3RhcnQ7XG4gICAgICAgIHN0YXJ0TG9jID0gdGhpcy5zdGFydExvYztcbiAgICAgIH1cbiAgICAgIGlmICghaXNQYXR0ZXJuKSBpc0dlbmVyYXRvciA9IHRoaXMuZWF0KHR0LnN0YXIpO1xuICAgIH1cbiAgICB0aGlzLnBhcnNlUHJvcGVydHlOYW1lKHByb3ApO1xuICAgIHRoaXMucGFyc2VQcm9wZXJ0eVZhbHVlKHByb3AsIGlzUGF0dGVybiwgaXNHZW5lcmF0b3IsIHN0YXJ0UG9zLCBzdGFydExvYywgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcyk7XG4gICAgdGhpcy5jaGVja1Byb3BDbGFzaChwcm9wLCBwcm9wSGFzaCk7XG4gICAgbm9kZS5wcm9wZXJ0aWVzLnB1c2godGhpcy5maW5pc2hOb2RlKHByb3AsIFwiUHJvcGVydHlcIikpO1xuICB9XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgaXNQYXR0ZXJuID8gXCJPYmplY3RQYXR0ZXJuXCIgOiBcIk9iamVjdEV4cHJlc3Npb25cIik7XG59O1xuXG5wcC5wYXJzZVByb3BlcnR5VmFsdWUgPSBmdW5jdGlvbiAocHJvcCwgaXNQYXR0ZXJuLCBpc0dlbmVyYXRvciwgc3RhcnRQb3MsIHN0YXJ0TG9jLCByZWZTaG9ydGhhbmREZWZhdWx0UG9zKSB7XG4gIGlmICh0aGlzLmVhdCh0dC5jb2xvbikpIHtcbiAgICBwcm9wLnZhbHVlID0gaXNQYXR0ZXJuID8gdGhpcy5wYXJzZU1heWJlRGVmYXVsdCh0aGlzLnN0YXJ0LCB0aGlzLnN0YXJ0TG9jKSA6IHRoaXMucGFyc2VNYXliZUFzc2lnbihmYWxzZSwgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcyk7XG4gICAgcHJvcC5raW5kID0gXCJpbml0XCI7XG4gIH0gZWxzZSBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYgJiYgdGhpcy50eXBlID09PSB0dC5wYXJlbkwpIHtcbiAgICBpZiAoaXNQYXR0ZXJuKSB0aGlzLnVuZXhwZWN0ZWQoKTtcbiAgICBwcm9wLmtpbmQgPSBcImluaXRcIjtcbiAgICBwcm9wLm1ldGhvZCA9IHRydWU7XG4gICAgcHJvcC52YWx1ZSA9IHRoaXMucGFyc2VNZXRob2QoaXNHZW5lcmF0b3IpO1xuICB9IGVsc2UgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA1ICYmICFwcm9wLmNvbXB1dGVkICYmIHByb3Aua2V5LnR5cGUgPT09IFwiSWRlbnRpZmllclwiICYmIChwcm9wLmtleS5uYW1lID09PSBcImdldFwiIHx8IHByb3Aua2V5Lm5hbWUgPT09IFwic2V0XCIpICYmICh0aGlzLnR5cGUgIT0gdHQuY29tbWEgJiYgdGhpcy50eXBlICE9IHR0LmJyYWNlUikpIHtcbiAgICBpZiAoaXNHZW5lcmF0b3IgfHwgaXNQYXR0ZXJuKSB0aGlzLnVuZXhwZWN0ZWQoKTtcbiAgICBwcm9wLmtpbmQgPSBwcm9wLmtleS5uYW1lO1xuICAgIHRoaXMucGFyc2VQcm9wZXJ0eU5hbWUocHJvcCk7XG4gICAgcHJvcC52YWx1ZSA9IHRoaXMucGFyc2VNZXRob2QoZmFsc2UpO1xuICB9IGVsc2UgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2ICYmICFwcm9wLmNvbXB1dGVkICYmIHByb3Aua2V5LnR5cGUgPT09IFwiSWRlbnRpZmllclwiKSB7XG4gICAgcHJvcC5raW5kID0gXCJpbml0XCI7XG4gICAgaWYgKGlzUGF0dGVybikge1xuICAgICAgaWYgKHRoaXMuaXNLZXl3b3JkKHByb3Aua2V5Lm5hbWUpIHx8IHRoaXMuc3RyaWN0ICYmIChyZXNlcnZlZFdvcmRzLnN0cmljdEJpbmQocHJvcC5rZXkubmFtZSkgfHwgcmVzZXJ2ZWRXb3Jkcy5zdHJpY3QocHJvcC5rZXkubmFtZSkpIHx8ICF0aGlzLm9wdGlvbnMuYWxsb3dSZXNlcnZlZCAmJiB0aGlzLmlzUmVzZXJ2ZWRXb3JkKHByb3Aua2V5Lm5hbWUpKSB0aGlzLnJhaXNlKHByb3Aua2V5LnN0YXJ0LCBcIkJpbmRpbmcgXCIgKyBwcm9wLmtleS5uYW1lKTtcbiAgICAgIHByb3AudmFsdWUgPSB0aGlzLnBhcnNlTWF5YmVEZWZhdWx0KHN0YXJ0UG9zLCBzdGFydExvYywgcHJvcC5rZXkpO1xuICAgIH0gZWxzZSBpZiAodGhpcy50eXBlID09PSB0dC5lcSAmJiByZWZTaG9ydGhhbmREZWZhdWx0UG9zKSB7XG4gICAgICBpZiAoIXJlZlNob3J0aGFuZERlZmF1bHRQb3Muc3RhcnQpIHJlZlNob3J0aGFuZERlZmF1bHRQb3Muc3RhcnQgPSB0aGlzLnN0YXJ0O1xuICAgICAgcHJvcC52YWx1ZSA9IHRoaXMucGFyc2VNYXliZURlZmF1bHQoc3RhcnRQb3MsIHN0YXJ0TG9jLCBwcm9wLmtleSk7XG4gICAgfSBlbHNlIHtcbiAgICAgIHByb3AudmFsdWUgPSBwcm9wLmtleTtcbiAgICB9XG4gICAgcHJvcC5zaG9ydGhhbmQgPSB0cnVlO1xuICB9IGVsc2UgdGhpcy51bmV4cGVjdGVkKCk7XG59O1xuXG5wcC5wYXJzZVByb3BlcnR5TmFtZSA9IGZ1bmN0aW9uIChwcm9wKSB7XG4gIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNikge1xuICAgIGlmICh0aGlzLmVhdCh0dC5icmFja2V0TCkpIHtcbiAgICAgIHByb3AuY29tcHV0ZWQgPSB0cnVlO1xuICAgICAgcHJvcC5rZXkgPSB0aGlzLnBhcnNlTWF5YmVBc3NpZ24oKTtcbiAgICAgIHRoaXMuZXhwZWN0KHR0LmJyYWNrZXRSKTtcbiAgICAgIHJldHVybiBwcm9wLmtleTtcbiAgICB9IGVsc2Uge1xuICAgICAgcHJvcC5jb21wdXRlZCA9IGZhbHNlO1xuICAgIH1cbiAgfVxuICByZXR1cm4gcHJvcC5rZXkgPSB0aGlzLnR5cGUgPT09IHR0Lm51bSB8fCB0aGlzLnR5cGUgPT09IHR0LnN0cmluZyA/IHRoaXMucGFyc2VFeHByQXRvbSgpIDogdGhpcy5wYXJzZUlkZW50KHRydWUpO1xufTtcblxuLy8gSW5pdGlhbGl6ZSBlbXB0eSBmdW5jdGlvbiBub2RlLlxuXG5wcC5pbml0RnVuY3Rpb24gPSBmdW5jdGlvbiAobm9kZSkge1xuICBub2RlLmlkID0gbnVsbDtcbiAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KSB7XG4gICAgbm9kZS5nZW5lcmF0b3IgPSBmYWxzZTtcbiAgICBub2RlLmV4cHJlc3Npb24gPSBmYWxzZTtcbiAgfVxufTtcblxuLy8gUGFyc2Ugb2JqZWN0IG9yIGNsYXNzIG1ldGhvZC5cblxucHAucGFyc2VNZXRob2QgPSBmdW5jdGlvbiAoaXNHZW5lcmF0b3IpIHtcbiAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICB0aGlzLmluaXRGdW5jdGlvbihub2RlKTtcbiAgdGhpcy5leHBlY3QodHQucGFyZW5MKTtcbiAgbm9kZS5wYXJhbXMgPSB0aGlzLnBhcnNlQmluZGluZ0xpc3QodHQucGFyZW5SLCBmYWxzZSwgZmFsc2UpO1xuICB2YXIgYWxsb3dFeHByZXNzaW9uQm9keSA9IHVuZGVmaW5lZDtcbiAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KSB7XG4gICAgbm9kZS5nZW5lcmF0b3IgPSBpc0dlbmVyYXRvcjtcbiAgICBhbGxvd0V4cHJlc3Npb25Cb2R5ID0gdHJ1ZTtcbiAgfSBlbHNlIHtcbiAgICBhbGxvd0V4cHJlc3Npb25Cb2R5ID0gZmFsc2U7XG4gIH1cbiAgdGhpcy5wYXJzZUZ1bmN0aW9uQm9keShub2RlLCBhbGxvd0V4cHJlc3Npb25Cb2R5KTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkZ1bmN0aW9uRXhwcmVzc2lvblwiKTtcbn07XG5cbi8vIFBhcnNlIGFycm93IGZ1bmN0aW9uIGV4cHJlc3Npb24gd2l0aCBnaXZlbiBwYXJhbWV0ZXJzLlxuXG5wcC5wYXJzZUFycm93RXhwcmVzc2lvbiA9IGZ1bmN0aW9uIChub2RlLCBwYXJhbXMpIHtcbiAgdGhpcy5pbml0RnVuY3Rpb24obm9kZSk7XG4gIG5vZGUucGFyYW1zID0gdGhpcy50b0Fzc2lnbmFibGVMaXN0KHBhcmFtcywgdHJ1ZSk7XG4gIHRoaXMucGFyc2VGdW5jdGlvbkJvZHkobm9kZSwgdHJ1ZSk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJBcnJvd0Z1bmN0aW9uRXhwcmVzc2lvblwiKTtcbn07XG5cbi8vIFBhcnNlIGZ1bmN0aW9uIGJvZHkgYW5kIGNoZWNrIHBhcmFtZXRlcnMuXG5cbnBwLnBhcnNlRnVuY3Rpb25Cb2R5ID0gZnVuY3Rpb24gKG5vZGUsIGFsbG93RXhwcmVzc2lvbikge1xuICB2YXIgaXNFeHByZXNzaW9uID0gYWxsb3dFeHByZXNzaW9uICYmIHRoaXMudHlwZSAhPT0gdHQuYnJhY2VMO1xuXG4gIGlmIChpc0V4cHJlc3Npb24pIHtcbiAgICBub2RlLmJvZHkgPSB0aGlzLnBhcnNlTWF5YmVBc3NpZ24oKTtcbiAgICBub2RlLmV4cHJlc3Npb24gPSB0cnVlO1xuICB9IGVsc2Uge1xuICAgIC8vIFN0YXJ0IGEgbmV3IHNjb3BlIHdpdGggcmVnYXJkIHRvIGxhYmVscyBhbmQgdGhlIGBpbkZ1bmN0aW9uYFxuICAgIC8vIGZsYWcgKHJlc3RvcmUgdGhlbSB0byB0aGVpciBvbGQgdmFsdWUgYWZ0ZXJ3YXJkcykuXG4gICAgdmFyIG9sZEluRnVuYyA9IHRoaXMuaW5GdW5jdGlvbixcbiAgICAgICAgb2xkSW5HZW4gPSB0aGlzLmluR2VuZXJhdG9yLFxuICAgICAgICBvbGRMYWJlbHMgPSB0aGlzLmxhYmVscztcbiAgICB0aGlzLmluRnVuY3Rpb24gPSB0cnVlO3RoaXMuaW5HZW5lcmF0b3IgPSBub2RlLmdlbmVyYXRvcjt0aGlzLmxhYmVscyA9IFtdO1xuICAgIG5vZGUuYm9keSA9IHRoaXMucGFyc2VCbG9jayh0cnVlKTtcbiAgICBub2RlLmV4cHJlc3Npb24gPSBmYWxzZTtcbiAgICB0aGlzLmluRnVuY3Rpb24gPSBvbGRJbkZ1bmM7dGhpcy5pbkdlbmVyYXRvciA9IG9sZEluR2VuO3RoaXMubGFiZWxzID0gb2xkTGFiZWxzO1xuICB9XG5cbiAgLy8gSWYgdGhpcyBpcyBhIHN0cmljdCBtb2RlIGZ1bmN0aW9uLCB2ZXJpZnkgdGhhdCBhcmd1bWVudCBuYW1lc1xuICAvLyBhcmUgbm90IHJlcGVhdGVkLCBhbmQgaXQgZG9lcyBub3QgdHJ5IHRvIGJpbmQgdGhlIHdvcmRzIGBldmFsYFxuICAvLyBvciBgYXJndW1lbnRzYC5cbiAgaWYgKHRoaXMuc3RyaWN0IHx8ICFpc0V4cHJlc3Npb24gJiYgbm9kZS5ib2R5LmJvZHkubGVuZ3RoICYmIHRoaXMuaXNVc2VTdHJpY3Qobm9kZS5ib2R5LmJvZHlbMF0pKSB7XG4gICAgdmFyIG5hbWVIYXNoID0ge30sXG4gICAgICAgIG9sZFN0cmljdCA9IHRoaXMuc3RyaWN0O1xuICAgIHRoaXMuc3RyaWN0ID0gdHJ1ZTtcbiAgICBpZiAobm9kZS5pZCkgdGhpcy5jaGVja0xWYWwobm9kZS5pZCwgdHJ1ZSk7XG4gICAgZm9yICh2YXIgaSA9IDA7IGkgPCBub2RlLnBhcmFtcy5sZW5ndGg7IGkrKykge1xuICAgICAgdGhpcy5jaGVja0xWYWwobm9kZS5wYXJhbXNbaV0sIHRydWUsIG5hbWVIYXNoKTtcbiAgICB9dGhpcy5zdHJpY3QgPSBvbGRTdHJpY3Q7XG4gIH1cbn07XG5cbi8vIFBhcnNlcyBhIGNvbW1hLXNlcGFyYXRlZCBsaXN0IG9mIGV4cHJlc3Npb25zLCBhbmQgcmV0dXJucyB0aGVtIGFzXG4vLyBhbiBhcnJheS4gYGNsb3NlYCBpcyB0aGUgdG9rZW4gdHlwZSB0aGF0IGVuZHMgdGhlIGxpc3QsIGFuZFxuLy8gYGFsbG93RW1wdHlgIGNhbiBiZSB0dXJuZWQgb24gdG8gYWxsb3cgc3Vic2VxdWVudCBjb21tYXMgd2l0aFxuLy8gbm90aGluZyBpbiBiZXR3ZWVuIHRoZW0gdG8gYmUgcGFyc2VkIGFzIGBudWxsYCAod2hpY2ggaXMgbmVlZGVkXG4vLyBmb3IgYXJyYXkgbGl0ZXJhbHMpLlxuXG5wcC5wYXJzZUV4cHJMaXN0ID0gZnVuY3Rpb24gKGNsb3NlLCBhbGxvd1RyYWlsaW5nQ29tbWEsIGFsbG93RW1wdHksIHJlZlNob3J0aGFuZERlZmF1bHRQb3MpIHtcbiAgdmFyIGVsdHMgPSBbXSxcbiAgICAgIGZpcnN0ID0gdHJ1ZTtcbiAgd2hpbGUgKCF0aGlzLmVhdChjbG9zZSkpIHtcbiAgICBpZiAoIWZpcnN0KSB7XG4gICAgICB0aGlzLmV4cGVjdCh0dC5jb21tYSk7XG4gICAgICBpZiAoYWxsb3dUcmFpbGluZ0NvbW1hICYmIHRoaXMuYWZ0ZXJUcmFpbGluZ0NvbW1hKGNsb3NlKSkgYnJlYWs7XG4gICAgfSBlbHNlIGZpcnN0ID0gZmFsc2U7XG5cbiAgICBpZiAoYWxsb3dFbXB0eSAmJiB0aGlzLnR5cGUgPT09IHR0LmNvbW1hKSB7XG4gICAgICBlbHRzLnB1c2gobnVsbCk7XG4gICAgfSBlbHNlIHtcbiAgICAgIGlmICh0aGlzLnR5cGUgPT09IHR0LmVsbGlwc2lzKSBlbHRzLnB1c2godGhpcy5wYXJzZVNwcmVhZChyZWZTaG9ydGhhbmREZWZhdWx0UG9zKSk7ZWxzZSBlbHRzLnB1c2godGhpcy5wYXJzZU1heWJlQXNzaWduKGZhbHNlLCByZWZTaG9ydGhhbmREZWZhdWx0UG9zKSk7XG4gICAgfVxuICB9XG4gIHJldHVybiBlbHRzO1xufTtcblxuLy8gUGFyc2UgdGhlIG5leHQgdG9rZW4gYXMgYW4gaWRlbnRpZmllci4gSWYgYGxpYmVyYWxgIGlzIHRydWUgKHVzZWRcbi8vIHdoZW4gcGFyc2luZyBwcm9wZXJ0aWVzKSwgaXQgd2lsbCBhbHNvIGNvbnZlcnQga2V5d29yZHMgaW50b1xuLy8gaWRlbnRpZmllcnMuXG5cbnBwLnBhcnNlSWRlbnQgPSBmdW5jdGlvbiAobGliZXJhbCkge1xuICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gIGlmIChsaWJlcmFsICYmIHRoaXMub3B0aW9ucy5hbGxvd1Jlc2VydmVkID09IFwibmV2ZXJcIikgbGliZXJhbCA9IGZhbHNlO1xuICBpZiAodGhpcy50eXBlID09PSB0dC5uYW1lKSB7XG4gICAgaWYgKCFsaWJlcmFsICYmICghdGhpcy5vcHRpb25zLmFsbG93UmVzZXJ2ZWQgJiYgdGhpcy5pc1Jlc2VydmVkV29yZCh0aGlzLnZhbHVlKSB8fCB0aGlzLnN0cmljdCAmJiByZXNlcnZlZFdvcmRzLnN0cmljdCh0aGlzLnZhbHVlKSAmJiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYgfHwgdGhpcy5pbnB1dC5zbGljZSh0aGlzLnN0YXJ0LCB0aGlzLmVuZCkuaW5kZXhPZihcIlxcXFxcIikgPT0gLTEpKSkgdGhpcy5yYWlzZSh0aGlzLnN0YXJ0LCBcIlRoZSBrZXl3b3JkICdcIiArIHRoaXMudmFsdWUgKyBcIicgaXMgcmVzZXJ2ZWRcIik7XG4gICAgbm9kZS5uYW1lID0gdGhpcy52YWx1ZTtcbiAgfSBlbHNlIGlmIChsaWJlcmFsICYmIHRoaXMudHlwZS5rZXl3b3JkKSB7XG4gICAgbm9kZS5uYW1lID0gdGhpcy50eXBlLmtleXdvcmQ7XG4gIH0gZWxzZSB7XG4gICAgdGhpcy51bmV4cGVjdGVkKCk7XG4gIH1cbiAgdGhpcy5uZXh0KCk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJJZGVudGlmaWVyXCIpO1xufTtcblxuLy8gUGFyc2VzIHlpZWxkIGV4cHJlc3Npb24gaW5zaWRlIGdlbmVyYXRvci5cblxucHAucGFyc2VZaWVsZCA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICB0aGlzLm5leHQoKTtcbiAgaWYgKHRoaXMudHlwZSA9PSB0dC5zZW1pIHx8IHRoaXMuY2FuSW5zZXJ0U2VtaWNvbG9uKCkgfHwgdGhpcy50eXBlICE9IHR0LnN0YXIgJiYgIXRoaXMudHlwZS5zdGFydHNFeHByKSB7XG4gICAgbm9kZS5kZWxlZ2F0ZSA9IGZhbHNlO1xuICAgIG5vZGUuYXJndW1lbnQgPSBudWxsO1xuICB9IGVsc2Uge1xuICAgIG5vZGUuZGVsZWdhdGUgPSB0aGlzLmVhdCh0dC5zdGFyKTtcbiAgICBub2RlLmFyZ3VtZW50ID0gdGhpcy5wYXJzZU1heWJlQXNzaWduKCk7XG4gIH1cbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIllpZWxkRXhwcmVzc2lvblwiKTtcbn07XG5cbi8vIFBhcnNlcyBhcnJheSBhbmQgZ2VuZXJhdG9yIGNvbXByZWhlbnNpb25zLlxuXG5wcC5wYXJzZUNvbXByZWhlbnNpb24gPSBmdW5jdGlvbiAobm9kZSwgaXNHZW5lcmF0b3IpIHtcbiAgbm9kZS5ibG9ja3MgPSBbXTtcbiAgd2hpbGUgKHRoaXMudHlwZSA9PT0gdHQuX2Zvcikge1xuICAgIHZhciBibG9jayA9IHRoaXMuc3RhcnROb2RlKCk7XG4gICAgdGhpcy5uZXh0KCk7XG4gICAgdGhpcy5leHBlY3QodHQucGFyZW5MKTtcbiAgICBibG9jay5sZWZ0ID0gdGhpcy5wYXJzZUJpbmRpbmdBdG9tKCk7XG4gICAgdGhpcy5jaGVja0xWYWwoYmxvY2subGVmdCwgdHJ1ZSk7XG4gICAgdGhpcy5leHBlY3RDb250ZXh0dWFsKFwib2ZcIik7XG4gICAgYmxvY2sucmlnaHQgPSB0aGlzLnBhcnNlRXhwcmVzc2lvbigpO1xuICAgIHRoaXMuZXhwZWN0KHR0LnBhcmVuUik7XG4gICAgbm9kZS5ibG9ja3MucHVzaCh0aGlzLmZpbmlzaE5vZGUoYmxvY2ssIFwiQ29tcHJlaGVuc2lvbkJsb2NrXCIpKTtcbiAgfVxuICBub2RlLmZpbHRlciA9IHRoaXMuZWF0KHR0Ll9pZikgPyB0aGlzLnBhcnNlUGFyZW5FeHByZXNzaW9uKCkgOiBudWxsO1xuICBub2RlLmJvZHkgPSB0aGlzLnBhcnNlRXhwcmVzc2lvbigpO1xuICB0aGlzLmV4cGVjdChpc0dlbmVyYXRvciA/IHR0LnBhcmVuUiA6IHR0LmJyYWNrZXRSKTtcbiAgbm9kZS5nZW5lcmF0b3IgPSBpc0dlbmVyYXRvcjtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkNvbXByZWhlbnNpb25FeHByZXNzaW9uXCIpO1xufTtcblxufSx7XCIuL2lkZW50aWZpZXJcIjo3LFwiLi9zdGF0ZVwiOjEzLFwiLi90b2tlbnR5cGVcIjoxNyxcIi4vdXRpbFwiOjE4fV0sNzpbZnVuY3Rpb24oX2RlcmVxXyxtb2R1bGUsZXhwb3J0cyl7XG5cblxuLy8gVGVzdCB3aGV0aGVyIGEgZ2l2ZW4gY2hhcmFjdGVyIGNvZGUgc3RhcnRzIGFuIGlkZW50aWZpZXIuXG5cblwidXNlIHN0cmljdFwiO1xuXG5leHBvcnRzLmlzSWRlbnRpZmllclN0YXJ0ID0gaXNJZGVudGlmaWVyU3RhcnQ7XG5cbi8vIFRlc3Qgd2hldGhlciBhIGdpdmVuIGNoYXJhY3RlciBpcyBwYXJ0IG9mIGFuIGlkZW50aWZpZXIuXG5cbmV4cG9ydHMuaXNJZGVudGlmaWVyQ2hhciA9IGlzSWRlbnRpZmllckNoYXI7XG5leHBvcnRzLl9fZXNNb2R1bGUgPSB0cnVlO1xuLy8gVGhpcyBpcyBhIHRyaWNrIHRha2VuIGZyb20gRXNwcmltYS4gSXQgdHVybnMgb3V0IHRoYXQsIG9uXG4vLyBub24tQ2hyb21lIGJyb3dzZXJzLCB0byBjaGVjayB3aGV0aGVyIGEgc3RyaW5nIGlzIGluIGEgc2V0LCBhXG4vLyBwcmVkaWNhdGUgY29udGFpbmluZyBhIGJpZyB1Z2x5IGBzd2l0Y2hgIHN0YXRlbWVudCBpcyBmYXN0ZXIgdGhhblxuLy8gYSByZWd1bGFyIGV4cHJlc3Npb24sIGFuZCBvbiBDaHJvbWUgdGhlIHR3byBhcmUgYWJvdXQgb24gcGFyLlxuLy8gVGhpcyBmdW5jdGlvbiB1c2VzIGBldmFsYCAobm9uLWxleGljYWwpIHRvIHByb2R1Y2Ugc3VjaCBhXG4vLyBwcmVkaWNhdGUgZnJvbSBhIHNwYWNlLXNlcGFyYXRlZCBzdHJpbmcgb2Ygd29yZHMuXG4vL1xuLy8gSXQgc3RhcnRzIGJ5IHNvcnRpbmcgdGhlIHdvcmRzIGJ5IGxlbmd0aC5cblxuZnVuY3Rpb24gbWFrZVByZWRpY2F0ZSh3b3Jkcykge1xuICB3b3JkcyA9IHdvcmRzLnNwbGl0KFwiIFwiKTtcbiAgdmFyIGYgPSBcIlwiLFxuICAgICAgY2F0cyA9IFtdO1xuICBvdXQ6IGZvciAodmFyIGkgPSAwOyBpIDwgd29yZHMubGVuZ3RoOyArK2kpIHtcbiAgICBmb3IgKHZhciBqID0gMDsgaiA8IGNhdHMubGVuZ3RoOyArK2opIHtcbiAgICAgIGlmIChjYXRzW2pdWzBdLmxlbmd0aCA9PSB3b3Jkc1tpXS5sZW5ndGgpIHtcbiAgICAgICAgY2F0c1tqXS5wdXNoKHdvcmRzW2ldKTtcbiAgICAgICAgY29udGludWUgb3V0O1xuICAgICAgfVxuICAgIH1jYXRzLnB1c2goW3dvcmRzW2ldXSk7XG4gIH1cbiAgZnVuY3Rpb24gY29tcGFyZVRvKGFycikge1xuICAgIGlmIChhcnIubGVuZ3RoID09IDEpIHtcbiAgICAgIHJldHVybiBmICs9IFwicmV0dXJuIHN0ciA9PT0gXCIgKyBKU09OLnN0cmluZ2lmeShhcnJbMF0pICsgXCI7XCI7XG4gICAgfWYgKz0gXCJzd2l0Y2goc3RyKXtcIjtcbiAgICBmb3IgKHZhciBpID0gMDsgaSA8IGFyci5sZW5ndGg7ICsraSkge1xuICAgICAgZiArPSBcImNhc2UgXCIgKyBKU09OLnN0cmluZ2lmeShhcnJbaV0pICsgXCI6XCI7XG4gICAgfWYgKz0gXCJyZXR1cm4gdHJ1ZX1yZXR1cm4gZmFsc2U7XCI7XG4gIH1cblxuICAvLyBXaGVuIHRoZXJlIGFyZSBtb3JlIHRoYW4gdGhyZWUgbGVuZ3RoIGNhdGVnb3JpZXMsIGFuIG91dGVyXG4gIC8vIHN3aXRjaCBmaXJzdCBkaXNwYXRjaGVzIG9uIHRoZSBsZW5ndGhzLCB0byBzYXZlIG9uIGNvbXBhcmlzb25zLlxuXG4gIGlmIChjYXRzLmxlbmd0aCA+IDMpIHtcbiAgICBjYXRzLnNvcnQoZnVuY3Rpb24gKGEsIGIpIHtcbiAgICAgIHJldHVybiBiLmxlbmd0aCAtIGEubGVuZ3RoO1xuICAgIH0pO1xuICAgIGYgKz0gXCJzd2l0Y2goc3RyLmxlbmd0aCl7XCI7XG4gICAgZm9yICh2YXIgaSA9IDA7IGkgPCBjYXRzLmxlbmd0aDsgKytpKSB7XG4gICAgICB2YXIgY2F0ID0gY2F0c1tpXTtcbiAgICAgIGYgKz0gXCJjYXNlIFwiICsgY2F0WzBdLmxlbmd0aCArIFwiOlwiO1xuICAgICAgY29tcGFyZVRvKGNhdCk7XG4gICAgfVxuICAgIGYgKz0gXCJ9XCJcblxuICAgIC8vIE90aGVyd2lzZSwgc2ltcGx5IGdlbmVyYXRlIGEgZmxhdCBgc3dpdGNoYCBzdGF0ZW1lbnQuXG5cbiAgICA7XG4gIH0gZWxzZSB7XG4gICAgY29tcGFyZVRvKHdvcmRzKTtcbiAgfVxuICByZXR1cm4gbmV3IEZ1bmN0aW9uKFwic3RyXCIsIGYpO1xufVxuXG4vLyBSZXNlcnZlZCB3b3JkIGxpc3RzIGZvciB2YXJpb3VzIGRpYWxlY3RzIG9mIHRoZSBsYW5ndWFnZVxuXG52YXIgcmVzZXJ2ZWRXb3JkcyA9IHtcbiAgMzogbWFrZVByZWRpY2F0ZShcImFic3RyYWN0IGJvb2xlYW4gYnl0ZSBjaGFyIGNsYXNzIGRvdWJsZSBlbnVtIGV4cG9ydCBleHRlbmRzIGZpbmFsIGZsb2F0IGdvdG8gaW1wbGVtZW50cyBpbXBvcnQgaW50IGludGVyZmFjZSBsb25nIG5hdGl2ZSBwYWNrYWdlIHByaXZhdGUgcHJvdGVjdGVkIHB1YmxpYyBzaG9ydCBzdGF0aWMgc3VwZXIgc3luY2hyb25pemVkIHRocm93cyB0cmFuc2llbnQgdm9sYXRpbGVcIiksXG4gIDU6IG1ha2VQcmVkaWNhdGUoXCJjbGFzcyBlbnVtIGV4dGVuZHMgc3VwZXIgY29uc3QgZXhwb3J0IGltcG9ydFwiKSxcbiAgNjogbWFrZVByZWRpY2F0ZShcImVudW0gYXdhaXRcIiksXG4gIHN0cmljdDogbWFrZVByZWRpY2F0ZShcImltcGxlbWVudHMgaW50ZXJmYWNlIGxldCBwYWNrYWdlIHByaXZhdGUgcHJvdGVjdGVkIHB1YmxpYyBzdGF0aWMgeWllbGRcIiksXG4gIHN0cmljdEJpbmQ6IG1ha2VQcmVkaWNhdGUoXCJldmFsIGFyZ3VtZW50c1wiKVxufTtcblxuZXhwb3J0cy5yZXNlcnZlZFdvcmRzID0gcmVzZXJ2ZWRXb3Jkcztcbi8vIEFuZCB0aGUga2V5d29yZHNcblxudmFyIGVjbWE1QW5kTGVzc0tleXdvcmRzID0gXCJicmVhayBjYXNlIGNhdGNoIGNvbnRpbnVlIGRlYnVnZ2VyIGRlZmF1bHQgZG8gZWxzZSBmaW5hbGx5IGZvciBmdW5jdGlvbiBpZiByZXR1cm4gc3dpdGNoIHRocm93IHRyeSB2YXIgd2hpbGUgd2l0aCBudWxsIHRydWUgZmFsc2UgaW5zdGFuY2VvZiB0eXBlb2Ygdm9pZCBkZWxldGUgbmV3IGluIHRoaXNcIjtcblxudmFyIGtleXdvcmRzID0ge1xuICA1OiBtYWtlUHJlZGljYXRlKGVjbWE1QW5kTGVzc0tleXdvcmRzKSxcbiAgNjogbWFrZVByZWRpY2F0ZShlY21hNUFuZExlc3NLZXl3b3JkcyArIFwiIGxldCBjb25zdCBjbGFzcyBleHRlbmRzIGV4cG9ydCBpbXBvcnQgeWllbGQgc3VwZXJcIilcbn07XG5cbmV4cG9ydHMua2V5d29yZHMgPSBrZXl3b3Jkcztcbi8vICMjIENoYXJhY3RlciBjYXRlZ29yaWVzXG5cbi8vIEJpZyB1Z2x5IHJlZ3VsYXIgZXhwcmVzc2lvbnMgdGhhdCBtYXRjaCBjaGFyYWN0ZXJzIGluIHRoZVxuLy8gd2hpdGVzcGFjZSwgaWRlbnRpZmllciwgYW5kIGlkZW50aWZpZXItc3RhcnQgY2F0ZWdvcmllcy4gVGhlc2Vcbi8vIGFyZSBvbmx5IGFwcGxpZWQgd2hlbiBhIGNoYXJhY3RlciBpcyBmb3VuZCB0byBhY3R1YWxseSBoYXZlIGFcbi8vIGNvZGUgcG9pbnQgYWJvdmUgMTI4LlxuLy8gR2VuZXJhdGVkIGJ5IGB0b29scy9nZW5lcmF0ZS1pZGVudGlmaWVyLXJlZ2V4LmpzYC5cblxudmFyIG5vbkFTQ0lJaWRlbnRpZmllclN0YXJ0Q2hhcnMgPSBcIsKqwrXCusOALcOWw5gtw7bDuC3LgcuGLcuRy6Aty6TLrMuuzbAtzbTNts23zbotzb3Nv86GzogtzorOjM6OLc6hzqMtz7XPty3SgdKKLdSv1LEt1ZbVmdWhLdaH15At16rXsC3XstigLdmK2a7Zr9mxLduT25Xbpdum267br9u6Ldu827/ckNySLdyv3Y0t3qXesd+KLd+q37Tftd+64KCALeCgleCgmuCgpOCgqOChgC3goZjgoqAt4KKy4KSELeCkueCkveClkOClmC3gpaHgpbEt4KaA4KaFLeCmjOCmj+CmkOCmky3gpqjgpqot4Kaw4Kay4Ka2LeCmueCmveCnjuCnnOCnneCnny3gp6Hgp7Dgp7HgqIUt4KiK4KiP4KiQ4KiTLeCoqOCoqi3gqLDgqLLgqLPgqLXgqLbgqLjgqLngqZkt4Kmc4Kme4KmyLeCptOCqhS3gqo3gqo8t4KqR4KqTLeCqqOCqqi3gqrDgqrLgqrPgqrUt4Kq54Kq94KuQ4Kug4Kuh4KyFLeCsjOCsj+CskOCsky3grKjgrKot4Kyw4Kyy4Kyz4Ky1LeCsueCsveCtnOCtneCtny3graHgrbHgroPgroUt4K6K4K6OLeCukOCuki3grpXgrpngrprgrpzgrp7grp/grqPgrqTgrqgt4K6q4K6uLeCuueCvkOCwhS3gsIzgsI4t4LCQ4LCSLeCwqOCwqi3gsLngsL3gsZjgsZngsaDgsaHgsoUt4LKM4LKOLeCykOCyki3gsqjgsqot4LKz4LK1LeCyueCyveCznuCzoOCzoeCzseCzsuC0hS3gtIzgtI4t4LSQ4LSSLeC0uuC0veC1juC1oOC1oeC1ui3gtb/gtoUt4LaW4LaaLeC2seC2sy3gtrvgtr3gt4At4LeG4LiBLeC4sOC4suC4s+C5gC3guYbguoHguoLguoTguofguojguorguo3gupQt4LqX4LqZLeC6n+C6oS3guqPguqXguqfguqrguqvguq0t4Lqw4Lqy4Lqz4Lq94LuALeC7hOC7huC7nC3gu5/gvIDgvYAt4L2H4L2JLeC9rOC+iC3gvozhgIAt4YCq4YC/4YGQLeGBleGBmi3hgZ3hgaHhgaXhgabhga4t4YGw4YG1LeGCgeGCjuGCoC3hg4Xhg4fhg43hg5At4YO64YO8LeGJiOGJii3hiY3hiZAt4YmW4YmY4YmaLeGJneGJoC3hiojhioot4YqN4YqQLeGKsOGKsi3hirXhirgt4Yq+4YuA4YuCLeGLheGLiC3hi5bhi5gt4YyQ4YySLeGMleGMmC3hjZrhjoAt4Y6P4Y6gLeGPtOGQgS3hmazhma8t4Zm/4ZqBLeGamuGaoC3hm6rhm64t4Zu44ZyALeGcjOGcji3hnJHhnKAt4Zyx4Z2ALeGdkeGdoC3hnazhna4t4Z2w4Z6ALeGes+Gfl+GfnOGgoC3hobfhooAt4aKo4aKq4aKwLeGjteGkgC3hpJ7hpZAt4aWt4aWwLeGltOGmgC3hpqvhp4Et4aeH4aiALeGoluGooC3hqZThqqfhrIUt4ayz4a2FLeGti+Gugy3hrqDhrq7hrq/hrrot4a+l4bCALeGwo+GxjS3hsY/hsZot4bG94bOpLeGzrOGzri3hs7Hhs7Xhs7bhtIAt4ba/4biALeG8leG8mC3hvJ3hvKAt4b2F4b2ILeG9jeG9kC3hvZfhvZnhvZvhvZ3hvZ8t4b294b6ALeG+tOG+ti3hvrzhvr7hv4It4b+E4b+GLeG/jOG/kC3hv5Phv5Yt4b+b4b+gLeG/rOG/si3hv7Thv7Yt4b+84oGx4oG/4oKQLeKCnOKEguKEh+KEii3ihJPihJXihJgt4oSd4oSk4oSm4oSo4oSqLeKEueKEvC3ihL/ihYUt4oWJ4oWO4oWgLeKGiOKwgC3isK7isLAt4rGe4rGgLeKzpOKzqy3is67is7Lis7PitIAt4rSl4rSn4rSt4rSwLeK1p+K1r+K2gC3itpbitqAt4ram4raoLeK2ruK2sC3itrbitrgt4ra+4reALeK3huK3iC3it47it5At4reW4reYLeK3nuOAhS3jgIfjgKEt44Cp44CxLeOAteOAuC3jgLzjgYEt44KW44KbLeOCn+OCoS3jg7rjg7wt44O/44SFLeOEreOEsS3jho7jhqAt44a644ewLeOHv+OQgC3ktrXkuIAt6b+M6oCALeqSjOqTkC3qk73qlIAt6piM6piQLeqYn+qYquqYq+qZgC3qma7qmb8t6pqd6pqgLeqbr+qcly3qnJ/qnKIt6p6I6p6LLeqejuqekC3qnq3qnrDqnrHqn7ct6qCB6qCDLeqgheqghy3qoIrqoIwt6qCi6qGALeqhs+qigi3qorPqo7It6qO36qO76qSKLeqkpeqksC3qpYbqpaAt6qW86qaELeqmsuqnj+qnoC3qp6Tqp6Yt6qev6qe6LeqnvuqogC3qqKjqqYAt6qmC6qmELeqpi+qpoC3qqbbqqbrqqb4t6qqv6qqx6qq16qq26qq5LeqqveqrgOqrguqrmy3qq53qq6At6quq6quyLeqrtOqsgS3qrIbqrIkt6qyO6qyRLeqsluqsoC3qrKbqrKgt6qyu6qywLeqtmuqtnC3qrZ/qraTqraXqr4At6q+i6rCALe2eo+2esC3tn4btn4st7Z+776SALe+pre+psC3vq5nvrIAt76yG76yTLe+sl++sne+sny3vrKjvrKot76y276y4Le+svO+svu+tgO+tge+tg++thO+thi3vrrHvr5Mt77S977WQLe+2j++2ki3vt4fvt7At77e777mwLe+5tO+5ti3vu7zvvKEt77y6772BLe+9mu+9pi3vvr7vv4It77+H77+KLe+/j++/ki3vv5fvv5ot77+cXCI7XG52YXIgbm9uQVNDSUlpZGVudGlmaWVyQ2hhcnMgPSBcIuKAjOKAjcK3zIAtza/Oh9KDLdKH1pEt1r3Wv9eB14LXhNeF14fYkC3YmtmLLdmp2bDbli3bnNufLduk26fbqNuqLdut27At27nckdywLd2K3qYt3rDfgC3fid+rLd+z4KCWLeCgmeCgmy3goKPgoKUt4KCn4KCpLeCgreChmS3goZvgo6Qt4KSD4KS6LeCkvOCkvi3gpY/gpZEt4KWX4KWi4KWj4KWmLeClr+CmgS3gpoPgprzgpr4t4KeE4KeH4KeI4KeLLeCnjeCnl+CnouCno+Cnpi3gp6/gqIEt4KiD4Ki84Ki+LeCpguCph+CpiOCpiy3gqY3gqZHgqaYt4Kmx4Km14KqBLeCqg+CqvOCqvi3gq4Xgq4ct4KuJ4KuLLeCrjeCrouCro+Crpi3gq6/grIEt4KyD4Ky84Ky+LeCthOCth+CtiOCtiy3grY3grZbgrZfgraLgraPgraYt4K2v4K6C4K6+LeCvguCvhi3gr4jgr4ot4K+N4K+X4K+mLeCvr+CwgC3gsIPgsL4t4LGE4LGGLeCxiOCxii3gsY3gsZXgsZbgsaLgsaPgsaYt4LGv4LKBLeCyg+CyvOCyvi3gs4Tgs4Yt4LOI4LOKLeCzjeCzleCzluCzouCzo+Czpi3gs6/gtIEt4LSD4LS+LeC1hOC1hi3gtYjgtYot4LWN4LWX4LWi4LWj4LWmLeC1r+C2guC2g+C3iuC3jy3gt5Tgt5bgt5gt4Lef4LemLeC3r+C3suC3s+C4seC4tC3guLrguYct4LmO4LmQLeC5meC6seC6tC3gurngurvgurzgu4gt4LuN4LuQLeC7meC8mOC8meC8oC3gvKngvLXgvLfgvLngvL7gvL/gvbEt4L6E4L6G4L6H4L6NLeC+l+C+mS3gvrzgv4bhgKst4YC+4YGALeGBieGBli3hgZnhgZ4t4YGg4YGiLeGBpOGBpy3hga3hgbEt4YG04YKCLeGCjeGCjy3hgp3hjZ0t4Y2f4Y2pLeGNseGcki3hnJThnLIt4Zy04Z2S4Z2T4Z2y4Z2z4Z60LeGfk+GfneGfoC3hn6nhoIst4aCN4aCQLeGgmeGiqeGkoC3hpKvhpLAt4aS74aWGLeGlj+GmsC3hp4Dhp4jhp4nhp5At4aea4aiXLeGom+GplS3hqZ7hqaAt4am84am/LeGqieGqkC3hqpnhqrAt4aq94ayALeGshOGstC3hrYThrZAt4a2Z4a2rLeGts+GugC3hroLhrqEt4a6t4a6wLeGuueGvpi3hr7PhsKQt4bC34bGALeGxieGxkC3hsZnhs5At4bOS4bOULeGzqOGzreGzsi3hs7Ths7jhs7nht4At4be14be8LeG3v+KAv+KBgOKBlOKDkC3ig5zig6Hig6Ut4oOw4rOvLeKzseK1v+K3oC3it7/jgKot44Cv44KZ44Ka6pigLeqYqeqZr+qZtC3qmb3qmp/qm7Dqm7HqoILqoIbqoIvqoKMt6qCn6qKA6qKB6qK0LeqjhOqjkC3qo5nqo6At6qOx6qSALeqkieqkpi3qpK3qpYct6qWT6qaALeqmg+qmsy3qp4Dqp5At6qeZ6qel6qewLeqnueqoqS3qqLbqqYPqqYzqqY3qqZAt6qmZ6qm7LeqpveqqsOqqsi3qqrTqqrfqqrjqqr7qqr/qq4Hqq6st6quv6qu16qu26q+jLeqvquqvrOqvreqvsC3qr7nvrJ7vuIAt77iP77igLe+4re+4s++4tO+5jS3vuY/vvJAt77yZ77y/XCI7XG5cbnZhciBub25BU0NJSWlkZW50aWZpZXJTdGFydCA9IG5ldyBSZWdFeHAoXCJbXCIgKyBub25BU0NJSWlkZW50aWZpZXJTdGFydENoYXJzICsgXCJdXCIpO1xudmFyIG5vbkFTQ0lJaWRlbnRpZmllciA9IG5ldyBSZWdFeHAoXCJbXCIgKyBub25BU0NJSWlkZW50aWZpZXJTdGFydENoYXJzICsgbm9uQVNDSUlpZGVudGlmaWVyQ2hhcnMgKyBcIl1cIik7XG5cbm5vbkFTQ0lJaWRlbnRpZmllclN0YXJ0Q2hhcnMgPSBub25BU0NJSWlkZW50aWZpZXJDaGFycyA9IG51bGw7XG5cbi8vIFRoZXNlIGFyZSBhIHJ1bi1sZW5ndGggYW5kIG9mZnNldCBlbmNvZGVkIHJlcHJlc2VudGF0aW9uIG9mIHRoZVxuLy8gPjB4ZmZmZiBjb2RlIHBvaW50cyB0aGF0IGFyZSBhIHZhbGlkIHBhcnQgb2YgaWRlbnRpZmllcnMuIFRoZVxuLy8gb2Zmc2V0IHN0YXJ0cyBhdCAweDEwMDAwLCBhbmQgZWFjaCBwYWlyIG9mIG51bWJlcnMgcmVwcmVzZW50cyBhblxuLy8gb2Zmc2V0IHRvIHRoZSBuZXh0IHJhbmdlLCBhbmQgdGhlbiBhIHNpemUgb2YgdGhlIHJhbmdlLiBUaGV5IHdlcmVcbi8vIGdlbmVyYXRlZCBieSB0b29scy9nZW5lcmF0ZS1pZGVudGlmaWVyLXJlZ2V4LmpzXG52YXIgYXN0cmFsSWRlbnRpZmllclN0YXJ0Q29kZXMgPSBbMCwgMTEsIDIsIDI1LCAyLCAxOCwgMiwgMSwgMiwgMTQsIDMsIDEzLCAzNSwgMTIyLCA3MCwgNTIsIDI2OCwgMjgsIDQsIDQ4LCA0OCwgMzEsIDE3LCAyNiwgNiwgMzcsIDExLCAyOSwgMywgMzUsIDUsIDcsIDIsIDQsIDQzLCAxNTcsIDk5LCAzOSwgOSwgNTEsIDE1NywgMzEwLCAxMCwgMjEsIDExLCA3LCAxNTMsIDUsIDMsIDAsIDIsIDQzLCAyLCAxLCA0LCAwLCAzLCAyMiwgMTEsIDIyLCAxMCwgMzAsIDk4LCAyMSwgMTEsIDI1LCA3MSwgNTUsIDcsIDEsIDY1LCAwLCAxNiwgMywgMiwgMiwgMiwgMjYsIDQ1LCAyOCwgNCwgMjgsIDM2LCA3LCAyLCAyNywgMjgsIDUzLCAxMSwgMjEsIDExLCAxOCwgMTQsIDE3LCAxMTEsIDcyLCA5NTUsIDUyLCA3NiwgNDQsIDMzLCAyNCwgMjcsIDM1LCA0MiwgMzQsIDQsIDAsIDEzLCA0NywgMTUsIDMsIDIyLCAwLCAzOCwgMTcsIDIsIDI0LCAxMzMsIDQ2LCAzOSwgNywgMywgMSwgMywgMjEsIDIsIDYsIDIsIDEsIDIsIDQsIDQsIDAsIDMyLCA0LCAyODcsIDQ3LCAyMSwgMSwgMiwgMCwgMTg1LCA0NiwgODIsIDQ3LCAyMSwgMCwgNjAsIDQyLCA1MDIsIDYzLCAzMiwgMCwgNDQ5LCA1NiwgMTI4OCwgOTIwLCAxMDQsIDExMCwgMjk2MiwgMTA3MCwgMTMyNjYsIDU2OCwgOCwgMzAsIDExNCwgMjksIDE5LCA0NywgMTcsIDMsIDMyLCAyMCwgNiwgMTgsIDg4MSwgNjgsIDEyLCAwLCA2NywgMTIsIDE2NDgxLCAxLCAzMDcxLCAxMDYsIDYsIDEyLCA0LCA4LCA4LCA5LCA1OTkxLCA4NCwgMiwgNzAsIDIsIDEsIDMsIDAsIDMsIDEsIDMsIDMsIDIsIDExLCAyLCAwLCAyLCA2LCAyLCA2NCwgMiwgMywgMywgNywgMiwgNiwgMiwgMjcsIDIsIDMsIDIsIDQsIDIsIDAsIDQsIDYsIDIsIDMzOSwgMywgMjQsIDIsIDI0LCAyLCAzMCwgMiwgMjQsIDIsIDMwLCAyLCAyNCwgMiwgMzAsIDIsIDI0LCAyLCAzMCwgMiwgMjQsIDIsIDcsIDQxNDksIDE5NiwgMTM0MCwgMywgMiwgMjYsIDIsIDEsIDIsIDAsIDMsIDAsIDIsIDksIDIsIDMsIDIsIDAsIDIsIDAsIDcsIDAsIDUsIDAsIDIsIDAsIDIsIDAsIDIsIDIsIDIsIDEsIDIsIDAsIDMsIDAsIDIsIDAsIDIsIDAsIDIsIDAsIDIsIDAsIDIsIDEsIDIsIDAsIDMsIDMsIDIsIDYsIDIsIDMsIDIsIDMsIDIsIDAsIDIsIDksIDIsIDE2LCA2LCAyLCAyLCA0LCAyLCAxNiwgNDQyMSwgNDI3MTAsIDQyLCA0MTQ4LCAxMiwgMjIxLCAxNjM1NSwgNTQxXTtcbnZhciBhc3RyYWxJZGVudGlmaWVyQ29kZXMgPSBbNTA5LCAwLCAyMjcsIDAsIDE1MCwgNCwgMjk0LCA5LCAxMzY4LCAyLCAyLCAxLCA2LCAzLCA0MSwgMiwgNSwgMCwgMTY2LCAxLCAxMzA2LCAyLCA1NCwgMTQsIDMyLCA5LCAxNiwgMywgNDYsIDEwLCA1NCwgOSwgNywgMiwgMzcsIDEzLCAyLCA5LCA1MiwgMCwgMTMsIDIsIDQ5LCAxMywgMTYsIDksIDgzLCAxMSwgMTY4LCAxMSwgNiwgOSwgOCwgMiwgNTcsIDAsIDIsIDYsIDMsIDEsIDMsIDIsIDEwLCAwLCAxMSwgMSwgMywgNiwgNCwgNCwgMzE2LCAxOSwgMTMsIDksIDIxNCwgNiwgMywgOCwgMTEyLCAxNiwgMTYsIDksIDgyLCAxMiwgOSwgOSwgNTM1LCA5LCAyMDg1NSwgOSwgMTM1LCA0LCA2MCwgNiwgMjYsIDksIDEwMTYsIDQ1LCAxNywgMywgMTk3MjMsIDEsIDUzMTksIDQsIDQsIDUsIDksIDcsIDMsIDYsIDMxLCAzLCAxNDksIDIsIDE0MTgsIDQ5LCA0MzA1LCA2LCA3OTI2MTgsIDIzOV07XG5cbi8vIFRoaXMgaGFzIGEgY29tcGxleGl0eSBsaW5lYXIgdG8gdGhlIHZhbHVlIG9mIHRoZSBjb2RlLiBUaGVcbi8vIGFzc3VtcHRpb24gaXMgdGhhdCBsb29raW5nIHVwIGFzdHJhbCBpZGVudGlmaWVyIGNoYXJhY3RlcnMgaXNcbi8vIHJhcmUuXG5mdW5jdGlvbiBpc0luQXN0cmFsU2V0KGNvZGUsIHNldCkge1xuICB2YXIgcG9zID0gNjU1MzY7XG4gIGZvciAodmFyIGkgPSAwOyBpIDwgc2V0Lmxlbmd0aDsgaSArPSAyKSB7XG4gICAgcG9zICs9IHNldFtpXTtcbiAgICBpZiAocG9zID4gY29kZSkge1xuICAgICAgcmV0dXJuIGZhbHNlO1xuICAgIH1wb3MgKz0gc2V0W2kgKyAxXTtcbiAgICBpZiAocG9zID49IGNvZGUpIHtcbiAgICAgIHJldHVybiB0cnVlO1xuICAgIH1cbiAgfVxufVxuZnVuY3Rpb24gaXNJZGVudGlmaWVyU3RhcnQoY29kZSwgYXN0cmFsKSB7XG4gIGlmIChjb2RlIDwgNjUpIHtcbiAgICByZXR1cm4gY29kZSA9PT0gMzY7XG4gIH1pZiAoY29kZSA8IDkxKSB7XG4gICAgcmV0dXJuIHRydWU7XG4gIH1pZiAoY29kZSA8IDk3KSB7XG4gICAgcmV0dXJuIGNvZGUgPT09IDk1O1xuICB9aWYgKGNvZGUgPCAxMjMpIHtcbiAgICByZXR1cm4gdHJ1ZTtcbiAgfWlmIChjb2RlIDw9IDY1NTM1KSB7XG4gICAgcmV0dXJuIGNvZGUgPj0gMTcwICYmIG5vbkFTQ0lJaWRlbnRpZmllclN0YXJ0LnRlc3QoU3RyaW5nLmZyb21DaGFyQ29kZShjb2RlKSk7XG4gIH1pZiAoYXN0cmFsID09PSBmYWxzZSkge1xuICAgIHJldHVybiBmYWxzZTtcbiAgfXJldHVybiBpc0luQXN0cmFsU2V0KGNvZGUsIGFzdHJhbElkZW50aWZpZXJTdGFydENvZGVzKTtcbn1cblxuZnVuY3Rpb24gaXNJZGVudGlmaWVyQ2hhcihjb2RlLCBhc3RyYWwpIHtcbiAgaWYgKGNvZGUgPCA0OCkge1xuICAgIHJldHVybiBjb2RlID09PSAzNjtcbiAgfWlmIChjb2RlIDwgNTgpIHtcbiAgICByZXR1cm4gdHJ1ZTtcbiAgfWlmIChjb2RlIDwgNjUpIHtcbiAgICByZXR1cm4gZmFsc2U7XG4gIH1pZiAoY29kZSA8IDkxKSB7XG4gICAgcmV0dXJuIHRydWU7XG4gIH1pZiAoY29kZSA8IDk3KSB7XG4gICAgcmV0dXJuIGNvZGUgPT09IDk1O1xuICB9aWYgKGNvZGUgPCAxMjMpIHtcbiAgICByZXR1cm4gdHJ1ZTtcbiAgfWlmIChjb2RlIDw9IDY1NTM1KSB7XG4gICAgcmV0dXJuIGNvZGUgPj0gMTcwICYmIG5vbkFTQ0lJaWRlbnRpZmllci50ZXN0KFN0cmluZy5mcm9tQ2hhckNvZGUoY29kZSkpO1xuICB9aWYgKGFzdHJhbCA9PT0gZmFsc2UpIHtcbiAgICByZXR1cm4gZmFsc2U7XG4gIH1yZXR1cm4gaXNJbkFzdHJhbFNldChjb2RlLCBhc3RyYWxJZGVudGlmaWVyU3RhcnRDb2RlcykgfHwgaXNJbkFzdHJhbFNldChjb2RlLCBhc3RyYWxJZGVudGlmaWVyQ29kZXMpO1xufVxuXG59LHt9XSw4OltmdW5jdGlvbihfZGVyZXFfLG1vZHVsZSxleHBvcnRzKXtcblwidXNlIHN0cmljdFwiO1xuXG52YXIgX2NsYXNzQ2FsbENoZWNrID0gZnVuY3Rpb24gKGluc3RhbmNlLCBDb25zdHJ1Y3RvcikgeyBpZiAoIShpbnN0YW5jZSBpbnN0YW5jZW9mIENvbnN0cnVjdG9yKSkgeyB0aHJvdyBuZXcgVHlwZUVycm9yKFwiQ2Fubm90IGNhbGwgYSBjbGFzcyBhcyBhIGZ1bmN0aW9uXCIpOyB9IH07XG5cbi8vIFRoZSBgZ2V0TGluZUluZm9gIGZ1bmN0aW9uIGlzIG1vc3RseSB1c2VmdWwgd2hlbiB0aGVcbi8vIGBsb2NhdGlvbnNgIG9wdGlvbiBpcyBvZmYgKGZvciBwZXJmb3JtYW5jZSByZWFzb25zKSBhbmQgeW91XG4vLyB3YW50IHRvIGZpbmQgdGhlIGxpbmUvY29sdW1uIHBvc2l0aW9uIGZvciBhIGdpdmVuIGNoYXJhY3RlclxuLy8gb2Zmc2V0LiBgaW5wdXRgIHNob3VsZCBiZSB0aGUgY29kZSBzdHJpbmcgdGhhdCB0aGUgb2Zmc2V0IHJlZmVyc1xuLy8gaW50by5cblxuZXhwb3J0cy5nZXRMaW5lSW5mbyA9IGdldExpbmVJbmZvO1xuZXhwb3J0cy5fX2VzTW9kdWxlID0gdHJ1ZTtcblxudmFyIFBhcnNlciA9IF9kZXJlcV8oXCIuL3N0YXRlXCIpLlBhcnNlcjtcblxudmFyIGxpbmVCcmVha0cgPSBfZGVyZXFfKFwiLi93aGl0ZXNwYWNlXCIpLmxpbmVCcmVha0c7XG5cbnZhciBkZXByZWNhdGUgPSBfZGVyZXFfKFwidXRpbFwiKS5kZXByZWNhdGU7XG5cbi8vIFRoZXNlIGFyZSB1c2VkIHdoZW4gYG9wdGlvbnMubG9jYXRpb25zYCBpcyBvbiwgZm9yIHRoZVxuLy8gYHN0YXJ0TG9jYCBhbmQgYGVuZExvY2AgcHJvcGVydGllcy5cblxudmFyIFBvc2l0aW9uID0gZXhwb3J0cy5Qb3NpdGlvbiA9IChmdW5jdGlvbiAoKSB7XG4gIGZ1bmN0aW9uIFBvc2l0aW9uKGxpbmUsIGNvbCkge1xuICAgIF9jbGFzc0NhbGxDaGVjayh0aGlzLCBQb3NpdGlvbik7XG5cbiAgICB0aGlzLmxpbmUgPSBsaW5lO1xuICAgIHRoaXMuY29sdW1uID0gY29sO1xuICB9XG5cbiAgUG9zaXRpb24ucHJvdG90eXBlLm9mZnNldCA9IGZ1bmN0aW9uIG9mZnNldChuKSB7XG4gICAgcmV0dXJuIG5ldyBQb3NpdGlvbih0aGlzLmxpbmUsIHRoaXMuY29sdW1uICsgbik7XG4gIH07XG5cbiAgcmV0dXJuIFBvc2l0aW9uO1xufSkoKTtcblxudmFyIFNvdXJjZUxvY2F0aW9uID0gZXhwb3J0cy5Tb3VyY2VMb2NhdGlvbiA9IGZ1bmN0aW9uIFNvdXJjZUxvY2F0aW9uKHAsIHN0YXJ0LCBlbmQpIHtcbiAgX2NsYXNzQ2FsbENoZWNrKHRoaXMsIFNvdXJjZUxvY2F0aW9uKTtcblxuICB0aGlzLnN0YXJ0ID0gc3RhcnQ7XG4gIHRoaXMuZW5kID0gZW5kO1xuICBpZiAocC5zb3VyY2VGaWxlICE9PSBudWxsKSB0aGlzLnNvdXJjZSA9IHAuc291cmNlRmlsZTtcbn07XG5cbmZ1bmN0aW9uIGdldExpbmVJbmZvKGlucHV0LCBvZmZzZXQpIHtcbiAgZm9yICh2YXIgbGluZSA9IDEsIGN1ciA9IDA7Oykge1xuICAgIGxpbmVCcmVha0cubGFzdEluZGV4ID0gY3VyO1xuICAgIHZhciBtYXRjaCA9IGxpbmVCcmVha0cuZXhlYyhpbnB1dCk7XG4gICAgaWYgKG1hdGNoICYmIG1hdGNoLmluZGV4IDwgb2Zmc2V0KSB7XG4gICAgICArK2xpbmU7XG4gICAgICBjdXIgPSBtYXRjaC5pbmRleCArIG1hdGNoWzBdLmxlbmd0aDtcbiAgICB9IGVsc2Uge1xuICAgICAgcmV0dXJuIG5ldyBQb3NpdGlvbihsaW5lLCBvZmZzZXQgLSBjdXIpO1xuICAgIH1cbiAgfVxufVxuXG52YXIgcHAgPSBQYXJzZXIucHJvdG90eXBlO1xuXG4vLyBUaGlzIGZ1bmN0aW9uIGlzIHVzZWQgdG8gcmFpc2UgZXhjZXB0aW9ucyBvbiBwYXJzZSBlcnJvcnMuIEl0XG4vLyB0YWtlcyBhbiBvZmZzZXQgaW50ZWdlciAoaW50byB0aGUgY3VycmVudCBgaW5wdXRgKSB0byBpbmRpY2F0ZVxuLy8gdGhlIGxvY2F0aW9uIG9mIHRoZSBlcnJvciwgYXR0YWNoZXMgdGhlIHBvc2l0aW9uIHRvIHRoZSBlbmRcbi8vIG9mIHRoZSBlcnJvciBtZXNzYWdlLCBhbmQgdGhlbiByYWlzZXMgYSBgU3ludGF4RXJyb3JgIHdpdGggdGhhdFxuLy8gbWVzc2FnZS5cblxucHAucmFpc2UgPSBmdW5jdGlvbiAocG9zLCBtZXNzYWdlKSB7XG4gIHZhciBsb2MgPSBnZXRMaW5lSW5mbyh0aGlzLmlucHV0LCBwb3MpO1xuICBtZXNzYWdlICs9IFwiIChcIiArIGxvYy5saW5lICsgXCI6XCIgKyBsb2MuY29sdW1uICsgXCIpXCI7XG4gIHZhciBlcnIgPSBuZXcgU3ludGF4RXJyb3IobWVzc2FnZSk7XG4gIGVyci5wb3MgPSBwb3M7ZXJyLmxvYyA9IGxvYztlcnIucmFpc2VkQXQgPSB0aGlzLnBvcztcbiAgdGhyb3cgZXJyO1xufTtcblxucHAuY3VyUG9zaXRpb24gPSBmdW5jdGlvbiAoKSB7XG4gIHJldHVybiBuZXcgUG9zaXRpb24odGhpcy5jdXJMaW5lLCB0aGlzLnBvcyAtIHRoaXMubGluZVN0YXJ0KTtcbn07XG5cbnBwLm1hcmtQb3NpdGlvbiA9IGZ1bmN0aW9uICgpIHtcbiAgcmV0dXJuIHRoaXMub3B0aW9ucy5sb2NhdGlvbnMgPyBbdGhpcy5zdGFydCwgdGhpcy5zdGFydExvY10gOiB0aGlzLnN0YXJ0O1xufTtcblxufSx7XCIuL3N0YXRlXCI6MTMsXCIuL3doaXRlc3BhY2VcIjoxOSxcInV0aWxcIjo1fV0sOTpbZnVuY3Rpb24oX2RlcmVxXyxtb2R1bGUsZXhwb3J0cyl7XG5cInVzZSBzdHJpY3RcIjtcblxudmFyIHR0ID0gX2RlcmVxXyhcIi4vdG9rZW50eXBlXCIpLnR5cGVzO1xuXG52YXIgUGFyc2VyID0gX2RlcmVxXyhcIi4vc3RhdGVcIikuUGFyc2VyO1xuXG52YXIgcmVzZXJ2ZWRXb3JkcyA9IF9kZXJlcV8oXCIuL2lkZW50aWZpZXJcIikucmVzZXJ2ZWRXb3JkcztcblxudmFyIGhhcyA9IF9kZXJlcV8oXCIuL3V0aWxcIikuaGFzO1xuXG52YXIgcHAgPSBQYXJzZXIucHJvdG90eXBlO1xuXG4vLyBDb252ZXJ0IGV4aXN0aW5nIGV4cHJlc3Npb24gYXRvbSB0byBhc3NpZ25hYmxlIHBhdHRlcm5cbi8vIGlmIHBvc3NpYmxlLlxuXG5wcC50b0Fzc2lnbmFibGUgPSBmdW5jdGlvbiAobm9kZSwgaXNCaW5kaW5nKSB7XG4gIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNiAmJiBub2RlKSB7XG4gICAgc3dpdGNoIChub2RlLnR5cGUpIHtcbiAgICAgIGNhc2UgXCJJZGVudGlmaWVyXCI6XG4gICAgICBjYXNlIFwiT2JqZWN0UGF0dGVyblwiOlxuICAgICAgY2FzZSBcIkFycmF5UGF0dGVyblwiOlxuICAgICAgY2FzZSBcIkFzc2lnbm1lbnRQYXR0ZXJuXCI6XG4gICAgICAgIGJyZWFrO1xuXG4gICAgICBjYXNlIFwiT2JqZWN0RXhwcmVzc2lvblwiOlxuICAgICAgICBub2RlLnR5cGUgPSBcIk9iamVjdFBhdHRlcm5cIjtcbiAgICAgICAgZm9yICh2YXIgaSA9IDA7IGkgPCBub2RlLnByb3BlcnRpZXMubGVuZ3RoOyBpKyspIHtcbiAgICAgICAgICB2YXIgcHJvcCA9IG5vZGUucHJvcGVydGllc1tpXTtcbiAgICAgICAgICBpZiAocHJvcC5raW5kICE9PSBcImluaXRcIikgdGhpcy5yYWlzZShwcm9wLmtleS5zdGFydCwgXCJPYmplY3QgcGF0dGVybiBjYW4ndCBjb250YWluIGdldHRlciBvciBzZXR0ZXJcIik7XG4gICAgICAgICAgdGhpcy50b0Fzc2lnbmFibGUocHJvcC52YWx1ZSwgaXNCaW5kaW5nKTtcbiAgICAgICAgfVxuICAgICAgICBicmVhaztcblxuICAgICAgY2FzZSBcIkFycmF5RXhwcmVzc2lvblwiOlxuICAgICAgICBub2RlLnR5cGUgPSBcIkFycmF5UGF0dGVyblwiO1xuICAgICAgICB0aGlzLnRvQXNzaWduYWJsZUxpc3Qobm9kZS5lbGVtZW50cywgaXNCaW5kaW5nKTtcbiAgICAgICAgYnJlYWs7XG5cbiAgICAgIGNhc2UgXCJBc3NpZ25tZW50RXhwcmVzc2lvblwiOlxuICAgICAgICBpZiAobm9kZS5vcGVyYXRvciA9PT0gXCI9XCIpIHtcbiAgICAgICAgICBub2RlLnR5cGUgPSBcIkFzc2lnbm1lbnRQYXR0ZXJuXCI7XG4gICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgdGhpcy5yYWlzZShub2RlLmxlZnQuZW5kLCBcIk9ubHkgJz0nIG9wZXJhdG9yIGNhbiBiZSB1c2VkIGZvciBzcGVjaWZ5aW5nIGRlZmF1bHQgdmFsdWUuXCIpO1xuICAgICAgICB9XG4gICAgICAgIGJyZWFrO1xuXG4gICAgICBjYXNlIFwiUGFyZW50aGVzaXplZEV4cHJlc3Npb25cIjpcbiAgICAgICAgbm9kZS5leHByZXNzaW9uID0gdGhpcy50b0Fzc2lnbmFibGUobm9kZS5leHByZXNzaW9uLCBpc0JpbmRpbmcpO1xuICAgICAgICBicmVhaztcblxuICAgICAgY2FzZSBcIk1lbWJlckV4cHJlc3Npb25cIjpcbiAgICAgICAgaWYgKCFpc0JpbmRpbmcpIGJyZWFrO1xuXG4gICAgICBkZWZhdWx0OlxuICAgICAgICB0aGlzLnJhaXNlKG5vZGUuc3RhcnQsIFwiQXNzaWduaW5nIHRvIHJ2YWx1ZVwiKTtcbiAgICB9XG4gIH1cbiAgcmV0dXJuIG5vZGU7XG59O1xuXG4vLyBDb252ZXJ0IGxpc3Qgb2YgZXhwcmVzc2lvbiBhdG9tcyB0byBiaW5kaW5nIGxpc3QuXG5cbnBwLnRvQXNzaWduYWJsZUxpc3QgPSBmdW5jdGlvbiAoZXhwckxpc3QsIGlzQmluZGluZykge1xuICB2YXIgZW5kID0gZXhwckxpc3QubGVuZ3RoO1xuICBpZiAoZW5kKSB7XG4gICAgdmFyIGxhc3QgPSBleHByTGlzdFtlbmQgLSAxXTtcbiAgICBpZiAobGFzdCAmJiBsYXN0LnR5cGUgPT0gXCJSZXN0RWxlbWVudFwiKSB7XG4gICAgICAtLWVuZDtcbiAgICB9IGVsc2UgaWYgKGxhc3QgJiYgbGFzdC50eXBlID09IFwiU3ByZWFkRWxlbWVudFwiKSB7XG4gICAgICBsYXN0LnR5cGUgPSBcIlJlc3RFbGVtZW50XCI7XG4gICAgICB2YXIgYXJnID0gbGFzdC5hcmd1bWVudDtcbiAgICAgIHRoaXMudG9Bc3NpZ25hYmxlKGFyZywgaXNCaW5kaW5nKTtcbiAgICAgIGlmIChhcmcudHlwZSAhPT0gXCJJZGVudGlmaWVyXCIgJiYgYXJnLnR5cGUgIT09IFwiTWVtYmVyRXhwcmVzc2lvblwiICYmIGFyZy50eXBlICE9PSBcIkFycmF5UGF0dGVyblwiKSB0aGlzLnVuZXhwZWN0ZWQoYXJnLnN0YXJ0KTtcbiAgICAgIC0tZW5kO1xuICAgIH1cbiAgfVxuICBmb3IgKHZhciBpID0gMDsgaSA8IGVuZDsgaSsrKSB7XG4gICAgdmFyIGVsdCA9IGV4cHJMaXN0W2ldO1xuICAgIGlmIChlbHQpIHRoaXMudG9Bc3NpZ25hYmxlKGVsdCwgaXNCaW5kaW5nKTtcbiAgfVxuICByZXR1cm4gZXhwckxpc3Q7XG59O1xuXG4vLyBQYXJzZXMgc3ByZWFkIGVsZW1lbnQuXG5cbnBwLnBhcnNlU3ByZWFkID0gZnVuY3Rpb24gKHJlZlNob3J0aGFuZERlZmF1bHRQb3MpIHtcbiAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICB0aGlzLm5leHQoKTtcbiAgbm9kZS5hcmd1bWVudCA9IHRoaXMucGFyc2VNYXliZUFzc2lnbihyZWZTaG9ydGhhbmREZWZhdWx0UG9zKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIlNwcmVhZEVsZW1lbnRcIik7XG59O1xuXG5wcC5wYXJzZVJlc3QgPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgdGhpcy5uZXh0KCk7XG4gIG5vZGUuYXJndW1lbnQgPSB0aGlzLnR5cGUgPT09IHR0Lm5hbWUgfHwgdGhpcy50eXBlID09PSB0dC5icmFja2V0TCA/IHRoaXMucGFyc2VCaW5kaW5nQXRvbSgpIDogdGhpcy51bmV4cGVjdGVkKCk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJSZXN0RWxlbWVudFwiKTtcbn07XG5cbi8vIFBhcnNlcyBsdmFsdWUgKGFzc2lnbmFibGUpIGF0b20uXG5cbnBwLnBhcnNlQmluZGluZ0F0b20gPSBmdW5jdGlvbiAoKSB7XG4gIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPCA2KSByZXR1cm4gdGhpcy5wYXJzZUlkZW50KCk7XG4gIHN3aXRjaCAodGhpcy50eXBlKSB7XG4gICAgY2FzZSB0dC5uYW1lOlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VJZGVudCgpO1xuXG4gICAgY2FzZSB0dC5icmFja2V0TDpcbiAgICAgIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgbm9kZS5lbGVtZW50cyA9IHRoaXMucGFyc2VCaW5kaW5nTGlzdCh0dC5icmFja2V0UiwgdHJ1ZSwgdHJ1ZSk7XG4gICAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiQXJyYXlQYXR0ZXJuXCIpO1xuXG4gICAgY2FzZSB0dC5icmFjZUw6XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZU9iaih0cnVlKTtcblxuICAgIGRlZmF1bHQ6XG4gICAgICB0aGlzLnVuZXhwZWN0ZWQoKTtcbiAgfVxufTtcblxucHAucGFyc2VCaW5kaW5nTGlzdCA9IGZ1bmN0aW9uIChjbG9zZSwgYWxsb3dFbXB0eSwgYWxsb3dUcmFpbGluZ0NvbW1hKSB7XG4gIHZhciBlbHRzID0gW10sXG4gICAgICBmaXJzdCA9IHRydWU7XG4gIHdoaWxlICghdGhpcy5lYXQoY2xvc2UpKSB7XG4gICAgaWYgKGZpcnN0KSBmaXJzdCA9IGZhbHNlO2Vsc2UgdGhpcy5leHBlY3QodHQuY29tbWEpO1xuICAgIGlmIChhbGxvd0VtcHR5ICYmIHRoaXMudHlwZSA9PT0gdHQuY29tbWEpIHtcbiAgICAgIGVsdHMucHVzaChudWxsKTtcbiAgICB9IGVsc2UgaWYgKGFsbG93VHJhaWxpbmdDb21tYSAmJiB0aGlzLmFmdGVyVHJhaWxpbmdDb21tYShjbG9zZSkpIHtcbiAgICAgIGJyZWFrO1xuICAgIH0gZWxzZSBpZiAodGhpcy50eXBlID09PSB0dC5lbGxpcHNpcykge1xuICAgICAgdmFyIHJlc3QgPSB0aGlzLnBhcnNlUmVzdCgpO1xuICAgICAgdGhpcy5wYXJzZUJpbmRpbmdMaXN0SXRlbShyZXN0KTtcbiAgICAgIGVsdHMucHVzaChyZXN0KTtcbiAgICAgIHRoaXMuZXhwZWN0KGNsb3NlKTtcbiAgICAgIGJyZWFrO1xuICAgIH0gZWxzZSB7XG4gICAgICB2YXIgZWxlbSA9IHRoaXMucGFyc2VNYXliZURlZmF1bHQodGhpcy5zdGFydCwgdGhpcy5zdGFydExvYyk7XG4gICAgICB0aGlzLnBhcnNlQmluZGluZ0xpc3RJdGVtKGVsZW0pO1xuICAgICAgZWx0cy5wdXNoKGVsZW0pO1xuICAgIH1cbiAgfVxuICByZXR1cm4gZWx0cztcbn07XG5cbnBwLnBhcnNlQmluZGluZ0xpc3RJdGVtID0gZnVuY3Rpb24gKHBhcmFtKSB7XG4gIHJldHVybiBwYXJhbTtcbn07XG5cbi8vIFBhcnNlcyBhc3NpZ25tZW50IHBhdHRlcm4gYXJvdW5kIGdpdmVuIGF0b20gaWYgcG9zc2libGUuXG5cbnBwLnBhcnNlTWF5YmVEZWZhdWx0ID0gZnVuY3Rpb24gKHN0YXJ0UG9zLCBzdGFydExvYywgbGVmdCkge1xuICBpZiAoQXJyYXkuaXNBcnJheShzdGFydFBvcykpIHtcbiAgICBpZiAodGhpcy5vcHRpb25zLmxvY2F0aW9ucyAmJiBub0NhbGxzID09PSB1bmRlZmluZWQpIHtcbiAgICAgIC8vIHNoaWZ0IGFyZ3VtZW50cyB0byBsZWZ0IGJ5IG9uZVxuICAgICAgbGVmdCA9IHN0YXJ0TG9jO1xuICAgICAgLy8gZmxhdHRlbiBzdGFydFBvc1xuICAgICAgc3RhcnRMb2MgPSBzdGFydFBvc1sxXTtcbiAgICAgIHN0YXJ0UG9zID0gc3RhcnRQb3NbMF07XG4gICAgfVxuICB9XG4gIGxlZnQgPSBsZWZ0IHx8IHRoaXMucGFyc2VCaW5kaW5nQXRvbSgpO1xuICBpZiAoIXRoaXMuZWF0KHR0LmVxKSkgcmV0dXJuIGxlZnQ7XG4gIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGVBdChzdGFydFBvcywgc3RhcnRMb2MpO1xuICBub2RlLm9wZXJhdG9yID0gXCI9XCI7XG4gIG5vZGUubGVmdCA9IGxlZnQ7XG4gIG5vZGUucmlnaHQgPSB0aGlzLnBhcnNlTWF5YmVBc3NpZ24oKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkFzc2lnbm1lbnRQYXR0ZXJuXCIpO1xufTtcblxuLy8gVmVyaWZ5IHRoYXQgYSBub2RlIGlzIGFuIGx2YWwg4oCUIHNvbWV0aGluZyB0aGF0IGNhbiBiZSBhc3NpZ25lZFxuLy8gdG8uXG5cbnBwLmNoZWNrTFZhbCA9IGZ1bmN0aW9uIChleHByLCBpc0JpbmRpbmcsIGNoZWNrQ2xhc2hlcykge1xuICBzd2l0Y2ggKGV4cHIudHlwZSkge1xuICAgIGNhc2UgXCJJZGVudGlmaWVyXCI6XG4gICAgICBpZiAodGhpcy5zdHJpY3QgJiYgKHJlc2VydmVkV29yZHMuc3RyaWN0QmluZChleHByLm5hbWUpIHx8IHJlc2VydmVkV29yZHMuc3RyaWN0KGV4cHIubmFtZSkpKSB0aGlzLnJhaXNlKGV4cHIuc3RhcnQsIChpc0JpbmRpbmcgPyBcIkJpbmRpbmcgXCIgOiBcIkFzc2lnbmluZyB0byBcIikgKyBleHByLm5hbWUgKyBcIiBpbiBzdHJpY3QgbW9kZVwiKTtcbiAgICAgIGlmIChjaGVja0NsYXNoZXMpIHtcbiAgICAgICAgaWYgKGhhcyhjaGVja0NsYXNoZXMsIGV4cHIubmFtZSkpIHRoaXMucmFpc2UoZXhwci5zdGFydCwgXCJBcmd1bWVudCBuYW1lIGNsYXNoIGluIHN0cmljdCBtb2RlXCIpO1xuICAgICAgICBjaGVja0NsYXNoZXNbZXhwci5uYW1lXSA9IHRydWU7XG4gICAgICB9XG4gICAgICBicmVhaztcblxuICAgIGNhc2UgXCJNZW1iZXJFeHByZXNzaW9uXCI6XG4gICAgICBpZiAoaXNCaW5kaW5nKSB0aGlzLnJhaXNlKGV4cHIuc3RhcnQsIChpc0JpbmRpbmcgPyBcIkJpbmRpbmdcIiA6IFwiQXNzaWduaW5nIHRvXCIpICsgXCIgbWVtYmVyIGV4cHJlc3Npb25cIik7XG4gICAgICBicmVhaztcblxuICAgIGNhc2UgXCJPYmplY3RQYXR0ZXJuXCI6XG4gICAgICBmb3IgKHZhciBpID0gMDsgaSA8IGV4cHIucHJvcGVydGllcy5sZW5ndGg7IGkrKykge1xuICAgICAgICB0aGlzLmNoZWNrTFZhbChleHByLnByb3BlcnRpZXNbaV0udmFsdWUsIGlzQmluZGluZywgY2hlY2tDbGFzaGVzKTtcbiAgICAgIH1icmVhaztcblxuICAgIGNhc2UgXCJBcnJheVBhdHRlcm5cIjpcbiAgICAgIGZvciAodmFyIGkgPSAwOyBpIDwgZXhwci5lbGVtZW50cy5sZW5ndGg7IGkrKykge1xuICAgICAgICB2YXIgZWxlbSA9IGV4cHIuZWxlbWVudHNbaV07XG4gICAgICAgIGlmIChlbGVtKSB0aGlzLmNoZWNrTFZhbChlbGVtLCBpc0JpbmRpbmcsIGNoZWNrQ2xhc2hlcyk7XG4gICAgICB9XG4gICAgICBicmVhaztcblxuICAgIGNhc2UgXCJBc3NpZ25tZW50UGF0dGVyblwiOlxuICAgICAgdGhpcy5jaGVja0xWYWwoZXhwci5sZWZ0LCBpc0JpbmRpbmcsIGNoZWNrQ2xhc2hlcyk7XG4gICAgICBicmVhaztcblxuICAgIGNhc2UgXCJSZXN0RWxlbWVudFwiOlxuICAgICAgdGhpcy5jaGVja0xWYWwoZXhwci5hcmd1bWVudCwgaXNCaW5kaW5nLCBjaGVja0NsYXNoZXMpO1xuICAgICAgYnJlYWs7XG5cbiAgICBjYXNlIFwiUGFyZW50aGVzaXplZEV4cHJlc3Npb25cIjpcbiAgICAgIHRoaXMuY2hlY2tMVmFsKGV4cHIuZXhwcmVzc2lvbiwgaXNCaW5kaW5nLCBjaGVja0NsYXNoZXMpO1xuICAgICAgYnJlYWs7XG5cbiAgICBkZWZhdWx0OlxuICAgICAgdGhpcy5yYWlzZShleHByLnN0YXJ0LCAoaXNCaW5kaW5nID8gXCJCaW5kaW5nXCIgOiBcIkFzc2lnbmluZyB0b1wiKSArIFwiIHJ2YWx1ZVwiKTtcbiAgfVxufTtcblxufSx7XCIuL2lkZW50aWZpZXJcIjo3LFwiLi9zdGF0ZVwiOjEzLFwiLi90b2tlbnR5cGVcIjoxNyxcIi4vdXRpbFwiOjE4fV0sMTA6W2Z1bmN0aW9uKF9kZXJlcV8sbW9kdWxlLGV4cG9ydHMpe1xuXCJ1c2Ugc3RyaWN0XCI7XG5cbnZhciBfY2xhc3NDYWxsQ2hlY2sgPSBmdW5jdGlvbiAoaW5zdGFuY2UsIENvbnN0cnVjdG9yKSB7IGlmICghKGluc3RhbmNlIGluc3RhbmNlb2YgQ29uc3RydWN0b3IpKSB7IHRocm93IG5ldyBUeXBlRXJyb3IoXCJDYW5ub3QgY2FsbCBhIGNsYXNzIGFzIGEgZnVuY3Rpb25cIik7IH0gfTtcblxuZXhwb3J0cy5fX2VzTW9kdWxlID0gdHJ1ZTtcblxudmFyIFBhcnNlciA9IF9kZXJlcV8oXCIuL3N0YXRlXCIpLlBhcnNlcjtcblxudmFyIFNvdXJjZUxvY2F0aW9uID0gX2RlcmVxXyhcIi4vbG9jYXRpb25cIikuU291cmNlTG9jYXRpb247XG5cbi8vIFN0YXJ0IGFuIEFTVCBub2RlLCBhdHRhY2hpbmcgYSBzdGFydCBvZmZzZXQuXG5cbnZhciBwcCA9IFBhcnNlci5wcm90b3R5cGU7XG5cbnZhciBOb2RlID0gZXhwb3J0cy5Ob2RlID0gZnVuY3Rpb24gTm9kZSgpIHtcbiAgX2NsYXNzQ2FsbENoZWNrKHRoaXMsIE5vZGUpO1xufTtcblxucHAuc3RhcnROb2RlID0gZnVuY3Rpb24gKCkge1xuICB2YXIgbm9kZSA9IG5ldyBOb2RlKCk7XG4gIG5vZGUuc3RhcnQgPSB0aGlzLnN0YXJ0O1xuICBpZiAodGhpcy5vcHRpb25zLmxvY2F0aW9ucykgbm9kZS5sb2MgPSBuZXcgU291cmNlTG9jYXRpb24odGhpcywgdGhpcy5zdGFydExvYyk7XG4gIGlmICh0aGlzLm9wdGlvbnMuZGlyZWN0U291cmNlRmlsZSkgbm9kZS5zb3VyY2VGaWxlID0gdGhpcy5vcHRpb25zLmRpcmVjdFNvdXJjZUZpbGU7XG4gIGlmICh0aGlzLm9wdGlvbnMucmFuZ2VzKSBub2RlLnJhbmdlID0gW3RoaXMuc3RhcnQsIDBdO1xuICByZXR1cm4gbm9kZTtcbn07XG5cbnBwLnN0YXJ0Tm9kZUF0ID0gZnVuY3Rpb24gKHBvcywgbG9jKSB7XG4gIHZhciBub2RlID0gbmV3IE5vZGUoKTtcbiAgaWYgKEFycmF5LmlzQXJyYXkocG9zKSkge1xuICAgIGlmICh0aGlzLm9wdGlvbnMubG9jYXRpb25zICYmIGxvYyA9PT0gdW5kZWZpbmVkKSB7XG4gICAgICAvLyBmbGF0dGVuIHBvc1xuICAgICAgbG9jID0gcG9zWzFdO1xuICAgICAgcG9zID0gcG9zWzBdO1xuICAgIH1cbiAgfVxuICBub2RlLnN0YXJ0ID0gcG9zO1xuICBpZiAodGhpcy5vcHRpb25zLmxvY2F0aW9ucykgbm9kZS5sb2MgPSBuZXcgU291cmNlTG9jYXRpb24odGhpcywgbG9jKTtcbiAgaWYgKHRoaXMub3B0aW9ucy5kaXJlY3RTb3VyY2VGaWxlKSBub2RlLnNvdXJjZUZpbGUgPSB0aGlzLm9wdGlvbnMuZGlyZWN0U291cmNlRmlsZTtcbiAgaWYgKHRoaXMub3B0aW9ucy5yYW5nZXMpIG5vZGUucmFuZ2UgPSBbcG9zLCAwXTtcbiAgcmV0dXJuIG5vZGU7XG59O1xuXG4vLyBGaW5pc2ggYW4gQVNUIG5vZGUsIGFkZGluZyBgdHlwZWAgYW5kIGBlbmRgIHByb3BlcnRpZXMuXG5cbnBwLmZpbmlzaE5vZGUgPSBmdW5jdGlvbiAobm9kZSwgdHlwZSkge1xuICBub2RlLnR5cGUgPSB0eXBlO1xuICBub2RlLmVuZCA9IHRoaXMubGFzdFRva0VuZDtcbiAgaWYgKHRoaXMub3B0aW9ucy5sb2NhdGlvbnMpIG5vZGUubG9jLmVuZCA9IHRoaXMubGFzdFRva0VuZExvYztcbiAgaWYgKHRoaXMub3B0aW9ucy5yYW5nZXMpIG5vZGUucmFuZ2VbMV0gPSB0aGlzLmxhc3RUb2tFbmQ7XG4gIHJldHVybiBub2RlO1xufTtcblxuLy8gRmluaXNoIG5vZGUgYXQgZ2l2ZW4gcG9zaXRpb25cblxucHAuZmluaXNoTm9kZUF0ID0gZnVuY3Rpb24gKG5vZGUsIHR5cGUsIHBvcywgbG9jKSB7XG4gIG5vZGUudHlwZSA9IHR5cGU7XG4gIGlmIChBcnJheS5pc0FycmF5KHBvcykpIHtcbiAgICBpZiAodGhpcy5vcHRpb25zLmxvY2F0aW9ucyAmJiBsb2MgPT09IHVuZGVmaW5lZCkge1xuICAgICAgLy8gZmxhdHRlbiBwb3NcbiAgICAgIGxvYyA9IHBvc1sxXTtcbiAgICAgIHBvcyA9IHBvc1swXTtcbiAgICB9XG4gIH1cbiAgbm9kZS5lbmQgPSBwb3M7XG4gIGlmICh0aGlzLm9wdGlvbnMubG9jYXRpb25zKSBub2RlLmxvYy5lbmQgPSBsb2M7XG4gIGlmICh0aGlzLm9wdGlvbnMucmFuZ2VzKSBub2RlLnJhbmdlWzFdID0gcG9zO1xuICByZXR1cm4gbm9kZTtcbn07XG5cbn0se1wiLi9sb2NhdGlvblwiOjgsXCIuL3N0YXRlXCI6MTN9XSwxMTpbZnVuY3Rpb24oX2RlcmVxXyxtb2R1bGUsZXhwb3J0cyl7XG5cblxuLy8gSW50ZXJwcmV0IGFuZCBkZWZhdWx0IGFuIG9wdGlvbnMgb2JqZWN0XG5cblwidXNlIHN0cmljdFwiO1xuXG5leHBvcnRzLmdldE9wdGlvbnMgPSBnZXRPcHRpb25zO1xuZXhwb3J0cy5fX2VzTW9kdWxlID0gdHJ1ZTtcblxudmFyIF91dGlsID0gX2RlcmVxXyhcIi4vdXRpbFwiKTtcblxudmFyIGhhcyA9IF91dGlsLmhhcztcbnZhciBpc0FycmF5ID0gX3V0aWwuaXNBcnJheTtcblxudmFyIFNvdXJjZUxvY2F0aW9uID0gX2RlcmVxXyhcIi4vbG9jYXRpb25cIikuU291cmNlTG9jYXRpb247XG5cbi8vIEEgc2Vjb25kIG9wdGlvbmFsIGFyZ3VtZW50IGNhbiBiZSBnaXZlbiB0byBmdXJ0aGVyIGNvbmZpZ3VyZVxuLy8gdGhlIHBhcnNlciBwcm9jZXNzLiBUaGVzZSBvcHRpb25zIGFyZSByZWNvZ25pemVkOlxuXG52YXIgZGVmYXVsdE9wdGlvbnMgPSB7XG4gIC8vIGBlY21hVmVyc2lvbmAgaW5kaWNhdGVzIHRoZSBFQ01BU2NyaXB0IHZlcnNpb24gdG8gcGFyc2UuIE11c3RcbiAgLy8gYmUgZWl0aGVyIDMsIG9yIDUsIG9yIDYuIFRoaXMgaW5mbHVlbmNlcyBzdXBwb3J0IGZvciBzdHJpY3RcbiAgLy8gbW9kZSwgdGhlIHNldCBvZiByZXNlcnZlZCB3b3Jkcywgc3VwcG9ydCBmb3IgZ2V0dGVycyBhbmRcbiAgLy8gc2V0dGVycyBhbmQgb3RoZXIgZmVhdHVyZXMuXG4gIGVjbWFWZXJzaW9uOiA1LFxuICAvLyBTb3VyY2UgdHlwZSAoXCJzY3JpcHRcIiBvciBcIm1vZHVsZVwiKSBmb3IgZGlmZmVyZW50IHNlbWFudGljc1xuICBzb3VyY2VUeXBlOiBcInNjcmlwdFwiLFxuICAvLyBgb25JbnNlcnRlZFNlbWljb2xvbmAgY2FuIGJlIGEgY2FsbGJhY2sgdGhhdCB3aWxsIGJlIGNhbGxlZFxuICAvLyB3aGVuIGEgc2VtaWNvbG9uIGlzIGF1dG9tYXRpY2FsbHkgaW5zZXJ0ZWQuIEl0IHdpbGwgYmUgcGFzc2VkXG4gIC8vIHRoIHBvc2l0aW9uIG9mIHRoZSBjb21tYSBhcyBhbiBvZmZzZXQsIGFuZCBpZiBgbG9jYXRpb25zYCBpc1xuICAvLyBlbmFibGVkLCBpdCBpcyBnaXZlbiB0aGUgbG9jYXRpb24gYXMgYSBge2xpbmUsIGNvbHVtbn1gIG9iamVjdFxuICAvLyBhcyBzZWNvbmQgYXJndW1lbnQuXG4gIG9uSW5zZXJ0ZWRTZW1pY29sb246IG51bGwsXG4gIC8vIGBvblRyYWlsaW5nQ29tbWFgIGlzIHNpbWlsYXIgdG8gYG9uSW5zZXJ0ZWRTZW1pY29sb25gLCBidXQgZm9yXG4gIC8vIHRyYWlsaW5nIGNvbW1hcy5cbiAgb25UcmFpbGluZ0NvbW1hOiBudWxsLFxuICAvLyBCeSBkZWZhdWx0LCByZXNlcnZlZCB3b3JkcyBhcmUgbm90IGVuZm9yY2VkLiBEaXNhYmxlXG4gIC8vIGBhbGxvd1Jlc2VydmVkYCB0byBlbmZvcmNlIHRoZW0uIFdoZW4gdGhpcyBvcHRpb24gaGFzIHRoZVxuICAvLyB2YWx1ZSBcIm5ldmVyXCIsIHJlc2VydmVkIHdvcmRzIGFuZCBrZXl3b3JkcyBjYW4gYWxzbyBub3QgYmVcbiAgLy8gdXNlZCBhcyBwcm9wZXJ0eSBuYW1lcy5cbiAgYWxsb3dSZXNlcnZlZDogdHJ1ZSxcbiAgLy8gV2hlbiBlbmFibGVkLCBhIHJldHVybiBhdCB0aGUgdG9wIGxldmVsIGlzIG5vdCBjb25zaWRlcmVkIGFuXG4gIC8vIGVycm9yLlxuICBhbGxvd1JldHVybk91dHNpZGVGdW5jdGlvbjogZmFsc2UsXG4gIC8vIFdoZW4gZW5hYmxlZCwgaW1wb3J0L2V4cG9ydCBzdGF0ZW1lbnRzIGFyZSBub3QgY29uc3RyYWluZWQgdG9cbiAgLy8gYXBwZWFyaW5nIGF0IHRoZSB0b3Agb2YgdGhlIHByb2dyYW0uXG4gIGFsbG93SW1wb3J0RXhwb3J0RXZlcnl3aGVyZTogZmFsc2UsXG4gIC8vIFdoZW4gZW5hYmxlZCwgaGFzaGJhbmcgZGlyZWN0aXZlIGluIHRoZSBiZWdpbm5pbmcgb2YgZmlsZVxuICAvLyBpcyBhbGxvd2VkIGFuZCB0cmVhdGVkIGFzIGEgbGluZSBjb21tZW50LlxuICBhbGxvd0hhc2hCYW5nOiBmYWxzZSxcbiAgLy8gV2hlbiBgbG9jYXRpb25zYCBpcyBvbiwgYGxvY2AgcHJvcGVydGllcyBob2xkaW5nIG9iamVjdHMgd2l0aFxuICAvLyBgc3RhcnRgIGFuZCBgZW5kYCBwcm9wZXJ0aWVzIGluIGB7bGluZSwgY29sdW1ufWAgZm9ybSAod2l0aFxuICAvLyBsaW5lIGJlaW5nIDEtYmFzZWQgYW5kIGNvbHVtbiAwLWJhc2VkKSB3aWxsIGJlIGF0dGFjaGVkIHRvIHRoZVxuICAvLyBub2Rlcy5cbiAgbG9jYXRpb25zOiBmYWxzZSxcbiAgLy8gQSBmdW5jdGlvbiBjYW4gYmUgcGFzc2VkIGFzIGBvblRva2VuYCBvcHRpb24sIHdoaWNoIHdpbGxcbiAgLy8gY2F1c2UgQWNvcm4gdG8gY2FsbCB0aGF0IGZ1bmN0aW9uIHdpdGggb2JqZWN0IGluIHRoZSBzYW1lXG4gIC8vIGZvcm1hdCBhcyB0b2tlbml6ZSgpIHJldHVybnMuIE5vdGUgdGhhdCB5b3UgYXJlIG5vdFxuICAvLyBhbGxvd2VkIHRvIGNhbGwgdGhlIHBhcnNlciBmcm9tIHRoZSBjYWxsYmFja+KAlHRoYXQgd2lsbFxuICAvLyBjb3JydXB0IGl0cyBpbnRlcm5hbCBzdGF0ZS5cbiAgb25Ub2tlbjogbnVsbCxcbiAgLy8gQSBmdW5jdGlvbiBjYW4gYmUgcGFzc2VkIGFzIGBvbkNvbW1lbnRgIG9wdGlvbiwgd2hpY2ggd2lsbFxuICAvLyBjYXVzZSBBY29ybiB0byBjYWxsIHRoYXQgZnVuY3Rpb24gd2l0aCBgKGJsb2NrLCB0ZXh0LCBzdGFydCxcbiAgLy8gZW5kKWAgcGFyYW1ldGVycyB3aGVuZXZlciBhIGNvbW1lbnQgaXMgc2tpcHBlZC4gYGJsb2NrYCBpcyBhXG4gIC8vIGJvb2xlYW4gaW5kaWNhdGluZyB3aGV0aGVyIHRoaXMgaXMgYSBibG9jayAoYC8qICovYCkgY29tbWVudCxcbiAgLy8gYHRleHRgIGlzIHRoZSBjb250ZW50IG9mIHRoZSBjb21tZW50LCBhbmQgYHN0YXJ0YCBhbmQgYGVuZGAgYXJlXG4gIC8vIGNoYXJhY3RlciBvZmZzZXRzIHRoYXQgZGVub3RlIHRoZSBzdGFydCBhbmQgZW5kIG9mIHRoZSBjb21tZW50LlxuICAvLyBXaGVuIHRoZSBgbG9jYXRpb25zYCBvcHRpb24gaXMgb24sIHR3byBtb3JlIHBhcmFtZXRlcnMgYXJlXG4gIC8vIHBhc3NlZCwgdGhlIGZ1bGwgYHtsaW5lLCBjb2x1bW59YCBsb2NhdGlvbnMgb2YgdGhlIHN0YXJ0IGFuZFxuICAvLyBlbmQgb2YgdGhlIGNvbW1lbnRzLiBOb3RlIHRoYXQgeW91IGFyZSBub3QgYWxsb3dlZCB0byBjYWxsIHRoZVxuICAvLyBwYXJzZXIgZnJvbSB0aGUgY2FsbGJhY2vigJR0aGF0IHdpbGwgY29ycnVwdCBpdHMgaW50ZXJuYWwgc3RhdGUuXG4gIG9uQ29tbWVudDogbnVsbCxcbiAgLy8gTm9kZXMgaGF2ZSB0aGVpciBzdGFydCBhbmQgZW5kIGNoYXJhY3RlcnMgb2Zmc2V0cyByZWNvcmRlZCBpblxuICAvLyBgc3RhcnRgIGFuZCBgZW5kYCBwcm9wZXJ0aWVzIChkaXJlY3RseSBvbiB0aGUgbm9kZSwgcmF0aGVyIHRoYW5cbiAgLy8gdGhlIGBsb2NgIG9iamVjdCwgd2hpY2ggaG9sZHMgbGluZS9jb2x1bW4gZGF0YS4gVG8gYWxzbyBhZGQgYVxuICAvLyBbc2VtaS1zdGFuZGFyZGl6ZWRdW3JhbmdlXSBgcmFuZ2VgIHByb3BlcnR5IGhvbGRpbmcgYSBgW3N0YXJ0LFxuICAvLyBlbmRdYCBhcnJheSB3aXRoIHRoZSBzYW1lIG51bWJlcnMsIHNldCB0aGUgYHJhbmdlc2Agb3B0aW9uIHRvXG4gIC8vIGB0cnVlYC5cbiAgLy9cbiAgLy8gW3JhbmdlXTogaHR0cHM6Ly9idWd6aWxsYS5tb3ppbGxhLm9yZy9zaG93X2J1Zy5jZ2k/aWQ9NzQ1Njc4XG4gIHJhbmdlczogZmFsc2UsXG4gIC8vIEl0IGlzIHBvc3NpYmxlIHRvIHBhcnNlIG11bHRpcGxlIGZpbGVzIGludG8gYSBzaW5nbGUgQVNUIGJ5XG4gIC8vIHBhc3NpbmcgdGhlIHRyZWUgcHJvZHVjZWQgYnkgcGFyc2luZyB0aGUgZmlyc3QgZmlsZSBhc1xuICAvLyBgcHJvZ3JhbWAgb3B0aW9uIGluIHN1YnNlcXVlbnQgcGFyc2VzLiBUaGlzIHdpbGwgYWRkIHRoZVxuICAvLyB0b3BsZXZlbCBmb3JtcyBvZiB0aGUgcGFyc2VkIGZpbGUgdG8gdGhlIGBQcm9ncmFtYCAodG9wKSBub2RlXG4gIC8vIG9mIGFuIGV4aXN0aW5nIHBhcnNlIHRyZWUuXG4gIHByb2dyYW06IG51bGwsXG4gIC8vIFdoZW4gYGxvY2F0aW9uc2AgaXMgb24sIHlvdSBjYW4gcGFzcyB0aGlzIHRvIHJlY29yZCB0aGUgc291cmNlXG4gIC8vIGZpbGUgaW4gZXZlcnkgbm9kZSdzIGBsb2NgIG9iamVjdC5cbiAgc291cmNlRmlsZTogbnVsbCxcbiAgLy8gVGhpcyB2YWx1ZSwgaWYgZ2l2ZW4sIGlzIHN0b3JlZCBpbiBldmVyeSBub2RlLCB3aGV0aGVyXG4gIC8vIGBsb2NhdGlvbnNgIGlzIG9uIG9yIG9mZi5cbiAgZGlyZWN0U291cmNlRmlsZTogbnVsbCxcbiAgLy8gV2hlbiBlbmFibGVkLCBwYXJlbnRoZXNpemVkIGV4cHJlc3Npb25zIGFyZSByZXByZXNlbnRlZCBieVxuICAvLyAobm9uLXN0YW5kYXJkKSBQYXJlbnRoZXNpemVkRXhwcmVzc2lvbiBub2Rlc1xuICBwcmVzZXJ2ZVBhcmVuczogZmFsc2UsXG4gIHBsdWdpbnM6IHt9XG59O2V4cG9ydHMuZGVmYXVsdE9wdGlvbnMgPSBkZWZhdWx0T3B0aW9ucztcblxuZnVuY3Rpb24gZ2V0T3B0aW9ucyhvcHRzKSB7XG4gIHZhciBvcHRpb25zID0ge307XG4gIGZvciAodmFyIG9wdCBpbiBkZWZhdWx0T3B0aW9ucykge1xuICAgIG9wdGlvbnNbb3B0XSA9IG9wdHMgJiYgaGFzKG9wdHMsIG9wdCkgPyBvcHRzW29wdF0gOiBkZWZhdWx0T3B0aW9uc1tvcHRdO1xuICB9aWYgKGlzQXJyYXkob3B0aW9ucy5vblRva2VuKSkge1xuICAgIChmdW5jdGlvbiAoKSB7XG4gICAgICB2YXIgdG9rZW5zID0gb3B0aW9ucy5vblRva2VuO1xuICAgICAgb3B0aW9ucy5vblRva2VuID0gZnVuY3Rpb24gKHRva2VuKSB7XG4gICAgICAgIHJldHVybiB0b2tlbnMucHVzaCh0b2tlbik7XG4gICAgICB9O1xuICAgIH0pKCk7XG4gIH1cbiAgaWYgKGlzQXJyYXkob3B0aW9ucy5vbkNvbW1lbnQpKSBvcHRpb25zLm9uQ29tbWVudCA9IHB1c2hDb21tZW50KG9wdGlvbnMsIG9wdGlvbnMub25Db21tZW50KTtcblxuICByZXR1cm4gb3B0aW9ucztcbn1cblxuZnVuY3Rpb24gcHVzaENvbW1lbnQob3B0aW9ucywgYXJyYXkpIHtcbiAgcmV0dXJuIGZ1bmN0aW9uIChibG9jaywgdGV4dCwgc3RhcnQsIGVuZCwgc3RhcnRMb2MsIGVuZExvYykge1xuICAgIHZhciBjb21tZW50ID0ge1xuICAgICAgdHlwZTogYmxvY2sgPyBcIkJsb2NrXCIgOiBcIkxpbmVcIixcbiAgICAgIHZhbHVlOiB0ZXh0LFxuICAgICAgc3RhcnQ6IHN0YXJ0LFxuICAgICAgZW5kOiBlbmRcbiAgICB9O1xuICAgIGlmIChvcHRpb25zLmxvY2F0aW9ucykgY29tbWVudC5sb2MgPSBuZXcgU291cmNlTG9jYXRpb24odGhpcywgc3RhcnRMb2MsIGVuZExvYyk7XG4gICAgaWYgKG9wdGlvbnMucmFuZ2VzKSBjb21tZW50LnJhbmdlID0gW3N0YXJ0LCBlbmRdO1xuICAgIGFycmF5LnB1c2goY29tbWVudCk7XG4gIH07XG59XG5cbn0se1wiLi9sb2NhdGlvblwiOjgsXCIuL3V0aWxcIjoxOH1dLDEyOltmdW5jdGlvbihfZGVyZXFfLG1vZHVsZSxleHBvcnRzKXtcblwidXNlIHN0cmljdFwiO1xuXG52YXIgdHQgPSBfZGVyZXFfKFwiLi90b2tlbnR5cGVcIikudHlwZXM7XG5cbnZhciBQYXJzZXIgPSBfZGVyZXFfKFwiLi9zdGF0ZVwiKS5QYXJzZXI7XG5cbnZhciBsaW5lQnJlYWsgPSBfZGVyZXFfKFwiLi93aGl0ZXNwYWNlXCIpLmxpbmVCcmVhaztcblxudmFyIHBwID0gUGFyc2VyLnByb3RvdHlwZTtcblxuLy8gIyMgUGFyc2VyIHV0aWxpdGllc1xuXG4vLyBUZXN0IHdoZXRoZXIgYSBzdGF0ZW1lbnQgbm9kZSBpcyB0aGUgc3RyaW5nIGxpdGVyYWwgYFwidXNlIHN0cmljdFwiYC5cblxucHAuaXNVc2VTdHJpY3QgPSBmdW5jdGlvbiAoc3RtdCkge1xuICByZXR1cm4gdGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDUgJiYgc3RtdC50eXBlID09PSBcIkV4cHJlc3Npb25TdGF0ZW1lbnRcIiAmJiBzdG10LmV4cHJlc3Npb24udHlwZSA9PT0gXCJMaXRlcmFsXCIgJiYgc3RtdC5leHByZXNzaW9uLnZhbHVlID09PSBcInVzZSBzdHJpY3RcIjtcbn07XG5cbi8vIFByZWRpY2F0ZSB0aGF0IHRlc3RzIHdoZXRoZXIgdGhlIG5leHQgdG9rZW4gaXMgb2YgdGhlIGdpdmVuXG4vLyB0eXBlLCBhbmQgaWYgeWVzLCBjb25zdW1lcyBpdCBhcyBhIHNpZGUgZWZmZWN0LlxuXG5wcC5lYXQgPSBmdW5jdGlvbiAodHlwZSkge1xuICBpZiAodGhpcy50eXBlID09PSB0eXBlKSB7XG4gICAgdGhpcy5uZXh0KCk7XG4gICAgcmV0dXJuIHRydWU7XG4gIH0gZWxzZSB7XG4gICAgcmV0dXJuIGZhbHNlO1xuICB9XG59O1xuXG4vLyBUZXN0cyB3aGV0aGVyIHBhcnNlZCB0b2tlbiBpcyBhIGNvbnRleHR1YWwga2V5d29yZC5cblxucHAuaXNDb250ZXh0dWFsID0gZnVuY3Rpb24gKG5hbWUpIHtcbiAgcmV0dXJuIHRoaXMudHlwZSA9PT0gdHQubmFtZSAmJiB0aGlzLnZhbHVlID09PSBuYW1lO1xufTtcblxuLy8gQ29uc3VtZXMgY29udGV4dHVhbCBrZXl3b3JkIGlmIHBvc3NpYmxlLlxuXG5wcC5lYXRDb250ZXh0dWFsID0gZnVuY3Rpb24gKG5hbWUpIHtcbiAgcmV0dXJuIHRoaXMudmFsdWUgPT09IG5hbWUgJiYgdGhpcy5lYXQodHQubmFtZSk7XG59O1xuXG4vLyBBc3NlcnRzIHRoYXQgZm9sbG93aW5nIHRva2VuIGlzIGdpdmVuIGNvbnRleHR1YWwga2V5d29yZC5cblxucHAuZXhwZWN0Q29udGV4dHVhbCA9IGZ1bmN0aW9uIChuYW1lKSB7XG4gIGlmICghdGhpcy5lYXRDb250ZXh0dWFsKG5hbWUpKSB0aGlzLnVuZXhwZWN0ZWQoKTtcbn07XG5cbi8vIFRlc3Qgd2hldGhlciBhIHNlbWljb2xvbiBjYW4gYmUgaW5zZXJ0ZWQgYXQgdGhlIGN1cnJlbnQgcG9zaXRpb24uXG5cbnBwLmNhbkluc2VydFNlbWljb2xvbiA9IGZ1bmN0aW9uICgpIHtcbiAgcmV0dXJuIHRoaXMudHlwZSA9PT0gdHQuZW9mIHx8IHRoaXMudHlwZSA9PT0gdHQuYnJhY2VSIHx8IGxpbmVCcmVhay50ZXN0KHRoaXMuaW5wdXQuc2xpY2UodGhpcy5sYXN0VG9rRW5kLCB0aGlzLnN0YXJ0KSk7XG59O1xuXG5wcC5pbnNlcnRTZW1pY29sb24gPSBmdW5jdGlvbiAoKSB7XG4gIGlmICh0aGlzLmNhbkluc2VydFNlbWljb2xvbigpKSB7XG4gICAgaWYgKHRoaXMub3B0aW9ucy5vbkluc2VydGVkU2VtaWNvbG9uKSB0aGlzLm9wdGlvbnMub25JbnNlcnRlZFNlbWljb2xvbih0aGlzLmxhc3RUb2tFbmQsIHRoaXMubGFzdFRva0VuZExvYyk7XG4gICAgcmV0dXJuIHRydWU7XG4gIH1cbn07XG5cbi8vIENvbnN1bWUgYSBzZW1pY29sb24sIG9yLCBmYWlsaW5nIHRoYXQsIHNlZSBpZiB3ZSBhcmUgYWxsb3dlZCB0b1xuLy8gcHJldGVuZCB0aGF0IHRoZXJlIGlzIGEgc2VtaWNvbG9uIGF0IHRoaXMgcG9zaXRpb24uXG5cbnBwLnNlbWljb2xvbiA9IGZ1bmN0aW9uICgpIHtcbiAgaWYgKCF0aGlzLmVhdCh0dC5zZW1pKSAmJiAhdGhpcy5pbnNlcnRTZW1pY29sb24oKSkgdGhpcy51bmV4cGVjdGVkKCk7XG59O1xuXG5wcC5hZnRlclRyYWlsaW5nQ29tbWEgPSBmdW5jdGlvbiAodG9rVHlwZSkge1xuICBpZiAodGhpcy50eXBlID09IHRva1R5cGUpIHtcbiAgICBpZiAodGhpcy5vcHRpb25zLm9uVHJhaWxpbmdDb21tYSkgdGhpcy5vcHRpb25zLm9uVHJhaWxpbmdDb21tYSh0aGlzLmxhc3RUb2tTdGFydCwgdGhpcy5sYXN0VG9rU3RhcnRMb2MpO1xuICAgIHRoaXMubmV4dCgpO1xuICAgIHJldHVybiB0cnVlO1xuICB9XG59O1xuXG4vLyBFeHBlY3QgYSB0b2tlbiBvZiBhIGdpdmVuIHR5cGUuIElmIGZvdW5kLCBjb25zdW1lIGl0LCBvdGhlcndpc2UsXG4vLyByYWlzZSBhbiB1bmV4cGVjdGVkIHRva2VuIGVycm9yLlxuXG5wcC5leHBlY3QgPSBmdW5jdGlvbiAodHlwZSkge1xuICB0aGlzLmVhdCh0eXBlKSB8fCB0aGlzLnVuZXhwZWN0ZWQoKTtcbn07XG5cbi8vIFJhaXNlIGFuIHVuZXhwZWN0ZWQgdG9rZW4gZXJyb3IuXG5cbnBwLnVuZXhwZWN0ZWQgPSBmdW5jdGlvbiAocG9zKSB7XG4gIHRoaXMucmFpc2UocG9zICE9IG51bGwgPyBwb3MgOiB0aGlzLnN0YXJ0LCBcIlVuZXhwZWN0ZWQgdG9rZW5cIik7XG59O1xuXG59LHtcIi4vc3RhdGVcIjoxMyxcIi4vdG9rZW50eXBlXCI6MTcsXCIuL3doaXRlc3BhY2VcIjoxOX1dLDEzOltmdW5jdGlvbihfZGVyZXFfLG1vZHVsZSxleHBvcnRzKXtcblwidXNlIHN0cmljdFwiO1xuXG5leHBvcnRzLlBhcnNlciA9IFBhcnNlcjtcbmV4cG9ydHMuX19lc01vZHVsZSA9IHRydWU7XG5cbnZhciBfaWRlbnRpZmllciA9IF9kZXJlcV8oXCIuL2lkZW50aWZpZXJcIik7XG5cbnZhciByZXNlcnZlZFdvcmRzID0gX2lkZW50aWZpZXIucmVzZXJ2ZWRXb3JkcztcbnZhciBrZXl3b3JkcyA9IF9pZGVudGlmaWVyLmtleXdvcmRzO1xuXG52YXIgdHQgPSBfZGVyZXFfKFwiLi90b2tlbnR5cGVcIikudHlwZXM7XG5cbnZhciBsaW5lQnJlYWsgPSBfZGVyZXFfKFwiLi93aGl0ZXNwYWNlXCIpLmxpbmVCcmVhaztcblxuZnVuY3Rpb24gUGFyc2VyKG9wdGlvbnMsIGlucHV0LCBzdGFydFBvcykge1xuICB0aGlzLm9wdGlvbnMgPSBvcHRpb25zO1xuICB0aGlzLnNvdXJjZUZpbGUgPSB0aGlzLm9wdGlvbnMuc291cmNlRmlsZSB8fCBudWxsO1xuICB0aGlzLmlzS2V5d29yZCA9IGtleXdvcmRzW3RoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2ID8gNiA6IDVdO1xuICB0aGlzLmlzUmVzZXJ2ZWRXb3JkID0gcmVzZXJ2ZWRXb3Jkc1t0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb25dO1xuICB0aGlzLmlucHV0ID0gaW5wdXQ7XG5cbiAgLy8gTG9hZCBwbHVnaW5zXG4gIHRoaXMubG9hZFBsdWdpbnModGhpcy5vcHRpb25zLnBsdWdpbnMpO1xuXG4gIC8vIFNldCB1cCB0b2tlbiBzdGF0ZVxuXG4gIC8vIFRoZSBjdXJyZW50IHBvc2l0aW9uIG9mIHRoZSB0b2tlbml6ZXIgaW4gdGhlIGlucHV0LlxuICBpZiAoc3RhcnRQb3MpIHtcbiAgICB0aGlzLnBvcyA9IHN0YXJ0UG9zO1xuICAgIHRoaXMubGluZVN0YXJ0ID0gTWF0aC5tYXgoMCwgdGhpcy5pbnB1dC5sYXN0SW5kZXhPZihcIlxcblwiLCBzdGFydFBvcykpO1xuICAgIHRoaXMuY3VyTGluZSA9IHRoaXMuaW5wdXQuc2xpY2UoMCwgdGhpcy5saW5lU3RhcnQpLnNwbGl0KGxpbmVCcmVhaykubGVuZ3RoO1xuICB9IGVsc2Uge1xuICAgIHRoaXMucG9zID0gdGhpcy5saW5lU3RhcnQgPSAwO1xuICAgIHRoaXMuY3VyTGluZSA9IDE7XG4gIH1cblxuICAvLyBQcm9wZXJ0aWVzIG9mIHRoZSBjdXJyZW50IHRva2VuOlxuICAvLyBJdHMgdHlwZVxuICB0aGlzLnR5cGUgPSB0dC5lb2Y7XG4gIC8vIEZvciB0b2tlbnMgdGhhdCBpbmNsdWRlIG1vcmUgaW5mb3JtYXRpb24gdGhhbiB0aGVpciB0eXBlLCB0aGUgdmFsdWVcbiAgdGhpcy52YWx1ZSA9IG51bGw7XG4gIC8vIEl0cyBzdGFydCBhbmQgZW5kIG9mZnNldFxuICB0aGlzLnN0YXJ0ID0gdGhpcy5lbmQgPSB0aGlzLnBvcztcbiAgLy8gQW5kLCBpZiBsb2NhdGlvbnMgYXJlIHVzZWQsIHRoZSB7bGluZSwgY29sdW1ufSBvYmplY3RcbiAgLy8gY29ycmVzcG9uZGluZyB0byB0aG9zZSBvZmZzZXRzXG4gIHRoaXMuc3RhcnRMb2MgPSB0aGlzLmVuZExvYyA9IG51bGw7XG5cbiAgLy8gUG9zaXRpb24gaW5mb3JtYXRpb24gZm9yIHRoZSBwcmV2aW91cyB0b2tlblxuICB0aGlzLmxhc3RUb2tFbmRMb2MgPSB0aGlzLmxhc3RUb2tTdGFydExvYyA9IG51bGw7XG4gIHRoaXMubGFzdFRva1N0YXJ0ID0gdGhpcy5sYXN0VG9rRW5kID0gdGhpcy5wb3M7XG5cbiAgLy8gVGhlIGNvbnRleHQgc3RhY2sgaXMgdXNlZCB0byBzdXBlcmZpY2lhbGx5IHRyYWNrIHN5bnRhY3RpY1xuICAvLyBjb250ZXh0IHRvIHByZWRpY3Qgd2hldGhlciBhIHJlZ3VsYXIgZXhwcmVzc2lvbiBpcyBhbGxvd2VkIGluIGFcbiAgLy8gZ2l2ZW4gcG9zaXRpb24uXG4gIHRoaXMuY29udGV4dCA9IHRoaXMuaW5pdGlhbENvbnRleHQoKTtcbiAgdGhpcy5leHByQWxsb3dlZCA9IHRydWU7XG5cbiAgLy8gRmlndXJlIG91dCBpZiBpdCdzIGEgbW9kdWxlIGNvZGUuXG4gIHRoaXMuc3RyaWN0ID0gdGhpcy5pbk1vZHVsZSA9IHRoaXMub3B0aW9ucy5zb3VyY2VUeXBlID09PSBcIm1vZHVsZVwiO1xuXG4gIC8vIFVzZWQgdG8gc2lnbmlmeSB0aGUgc3RhcnQgb2YgYSBwb3RlbnRpYWwgYXJyb3cgZnVuY3Rpb25cbiAgdGhpcy5wb3RlbnRpYWxBcnJvd0F0ID0gLTE7XG5cbiAgLy8gRmxhZ3MgdG8gdHJhY2sgd2hldGhlciB3ZSBhcmUgaW4gYSBmdW5jdGlvbiwgYSBnZW5lcmF0b3IuXG4gIHRoaXMuaW5GdW5jdGlvbiA9IHRoaXMuaW5HZW5lcmF0b3IgPSBmYWxzZTtcbiAgLy8gTGFiZWxzIGluIHNjb3BlLlxuICB0aGlzLmxhYmVscyA9IFtdO1xuXG4gIC8vIElmIGVuYWJsZWQsIHNraXAgbGVhZGluZyBoYXNoYmFuZyBsaW5lLlxuICBpZiAodGhpcy5wb3MgPT09IDAgJiYgdGhpcy5vcHRpb25zLmFsbG93SGFzaEJhbmcgJiYgdGhpcy5pbnB1dC5zbGljZSgwLCAyKSA9PT0gXCIjIVwiKSB0aGlzLnNraXBMaW5lQ29tbWVudCgyKTtcbn1cblxuUGFyc2VyLnByb3RvdHlwZS5leHRlbmQgPSBmdW5jdGlvbiAobmFtZSwgZikge1xuICB0aGlzW25hbWVdID0gZih0aGlzW25hbWVdKTtcbn07XG5cbi8vIFJlZ2lzdGVyZWQgcGx1Z2luc1xuXG52YXIgcGx1Z2lucyA9IHt9O1xuXG5leHBvcnRzLnBsdWdpbnMgPSBwbHVnaW5zO1xuUGFyc2VyLnByb3RvdHlwZS5sb2FkUGx1Z2lucyA9IGZ1bmN0aW9uIChwbHVnaW5zKSB7XG4gIGZvciAodmFyIF9uYW1lIGluIHBsdWdpbnMpIHtcbiAgICB2YXIgcGx1Z2luID0gZXhwb3J0cy5wbHVnaW5zW19uYW1lXTtcbiAgICBpZiAoIXBsdWdpbikgdGhyb3cgbmV3IEVycm9yKFwiUGx1Z2luICdcIiArIF9uYW1lICsgXCInIG5vdCBmb3VuZFwiKTtcbiAgICBwbHVnaW4odGhpcywgcGx1Z2luc1tfbmFtZV0pO1xuICB9XG59O1xuXG59LHtcIi4vaWRlbnRpZmllclwiOjcsXCIuL3Rva2VudHlwZVwiOjE3LFwiLi93aGl0ZXNwYWNlXCI6MTl9XSwxNDpbZnVuY3Rpb24oX2RlcmVxXyxtb2R1bGUsZXhwb3J0cyl7XG5cInVzZSBzdHJpY3RcIjtcblxudmFyIHR0ID0gX2RlcmVxXyhcIi4vdG9rZW50eXBlXCIpLnR5cGVzO1xuXG52YXIgUGFyc2VyID0gX2RlcmVxXyhcIi4vc3RhdGVcIikuUGFyc2VyO1xuXG52YXIgbGluZUJyZWFrID0gX2RlcmVxXyhcIi4vd2hpdGVzcGFjZVwiKS5saW5lQnJlYWs7XG5cbnZhciBwcCA9IFBhcnNlci5wcm90b3R5cGU7XG5cbi8vICMjIyBTdGF0ZW1lbnQgcGFyc2luZ1xuXG4vLyBQYXJzZSBhIHByb2dyYW0uIEluaXRpYWxpemVzIHRoZSBwYXJzZXIsIHJlYWRzIGFueSBudW1iZXIgb2Zcbi8vIHN0YXRlbWVudHMsIGFuZCB3cmFwcyB0aGVtIGluIGEgUHJvZ3JhbSBub2RlLiAgT3B0aW9uYWxseSB0YWtlcyBhXG4vLyBgcHJvZ3JhbWAgYXJndW1lbnQuICBJZiBwcmVzZW50LCB0aGUgc3RhdGVtZW50cyB3aWxsIGJlIGFwcGVuZGVkXG4vLyB0byBpdHMgYm9keSBpbnN0ZWFkIG9mIGNyZWF0aW5nIGEgbmV3IG5vZGUuXG5cbnBwLnBhcnNlVG9wTGV2ZWwgPSBmdW5jdGlvbiAobm9kZSkge1xuICB2YXIgZmlyc3QgPSB0cnVlO1xuICBpZiAoIW5vZGUuYm9keSkgbm9kZS5ib2R5ID0gW107XG4gIHdoaWxlICh0aGlzLnR5cGUgIT09IHR0LmVvZikge1xuICAgIHZhciBzdG10ID0gdGhpcy5wYXJzZVN0YXRlbWVudCh0cnVlLCB0cnVlKTtcbiAgICBub2RlLmJvZHkucHVzaChzdG10KTtcbiAgICBpZiAoZmlyc3QgJiYgdGhpcy5pc1VzZVN0cmljdChzdG10KSkgdGhpcy5zZXRTdHJpY3QodHJ1ZSk7XG4gICAgZmlyc3QgPSBmYWxzZTtcbiAgfVxuICB0aGlzLm5leHQoKTtcbiAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KSB7XG4gICAgbm9kZS5zb3VyY2VUeXBlID0gdGhpcy5vcHRpb25zLnNvdXJjZVR5cGU7XG4gIH1cbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIlByb2dyYW1cIik7XG59O1xuXG52YXIgbG9vcExhYmVsID0geyBraW5kOiBcImxvb3BcIiB9LFxuICAgIHN3aXRjaExhYmVsID0geyBraW5kOiBcInN3aXRjaFwiIH07XG5cbi8vIFBhcnNlIGEgc2luZ2xlIHN0YXRlbWVudC5cbi8vXG4vLyBJZiBleHBlY3RpbmcgYSBzdGF0ZW1lbnQgYW5kIGZpbmRpbmcgYSBzbGFzaCBvcGVyYXRvciwgcGFyc2UgYVxuLy8gcmVndWxhciBleHByZXNzaW9uIGxpdGVyYWwuIFRoaXMgaXMgdG8gaGFuZGxlIGNhc2VzIGxpa2Vcbi8vIGBpZiAoZm9vKSAvYmxhaC8uZXhlYyhmb28pYCwgd2hlcmUgbG9va2luZyBhdCB0aGUgcHJldmlvdXMgdG9rZW5cbi8vIGRvZXMgbm90IGhlbHAuXG5cbnBwLnBhcnNlU3RhdGVtZW50ID0gZnVuY3Rpb24gKGRlY2xhcmF0aW9uLCB0b3BMZXZlbCkge1xuICB2YXIgc3RhcnR0eXBlID0gdGhpcy50eXBlLFxuICAgICAgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG5cbiAgLy8gTW9zdCB0eXBlcyBvZiBzdGF0ZW1lbnRzIGFyZSByZWNvZ25pemVkIGJ5IHRoZSBrZXl3b3JkIHRoZXlcbiAgLy8gc3RhcnQgd2l0aC4gTWFueSBhcmUgdHJpdmlhbCB0byBwYXJzZSwgc29tZSByZXF1aXJlIGEgYml0IG9mXG4gIC8vIGNvbXBsZXhpdHkuXG5cbiAgc3dpdGNoIChzdGFydHR5cGUpIHtcbiAgICBjYXNlIHR0Ll9icmVhazpjYXNlIHR0Ll9jb250aW51ZTpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlQnJlYWtDb250aW51ZVN0YXRlbWVudChub2RlLCBzdGFydHR5cGUua2V5d29yZCk7XG4gICAgY2FzZSB0dC5fZGVidWdnZXI6XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZURlYnVnZ2VyU3RhdGVtZW50KG5vZGUpO1xuICAgIGNhc2UgdHQuX2RvOlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VEb1N0YXRlbWVudChub2RlKTtcbiAgICBjYXNlIHR0Ll9mb3I6XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZUZvclN0YXRlbWVudChub2RlKTtcbiAgICBjYXNlIHR0Ll9mdW5jdGlvbjpcbiAgICAgIGlmICghZGVjbGFyYXRpb24gJiYgdGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYpIHRoaXMudW5leHBlY3RlZCgpO1xuICAgICAgcmV0dXJuIHRoaXMucGFyc2VGdW5jdGlvblN0YXRlbWVudChub2RlKTtcbiAgICBjYXNlIHR0Ll9jbGFzczpcbiAgICAgIGlmICghZGVjbGFyYXRpb24pIHRoaXMudW5leHBlY3RlZCgpO1xuICAgICAgcmV0dXJuIHRoaXMucGFyc2VDbGFzcyhub2RlLCB0cnVlKTtcbiAgICBjYXNlIHR0Ll9pZjpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlSWZTdGF0ZW1lbnQobm9kZSk7XG4gICAgY2FzZSB0dC5fcmV0dXJuOlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VSZXR1cm5TdGF0ZW1lbnQobm9kZSk7XG4gICAgY2FzZSB0dC5fc3dpdGNoOlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VTd2l0Y2hTdGF0ZW1lbnQobm9kZSk7XG4gICAgY2FzZSB0dC5fdGhyb3c6XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZVRocm93U3RhdGVtZW50KG5vZGUpO1xuICAgIGNhc2UgdHQuX3RyeTpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlVHJ5U3RhdGVtZW50KG5vZGUpO1xuICAgIGNhc2UgdHQuX2xldDpjYXNlIHR0Ll9jb25zdDpcbiAgICAgIGlmICghZGVjbGFyYXRpb24pIHRoaXMudW5leHBlY3RlZCgpOyAvLyBOT1RFOiBmYWxscyB0aHJvdWdoIHRvIF92YXJcbiAgICBjYXNlIHR0Ll92YXI6XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZVZhclN0YXRlbWVudChub2RlLCBzdGFydHR5cGUpO1xuICAgIGNhc2UgdHQuX3doaWxlOlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VXaGlsZVN0YXRlbWVudChub2RlKTtcbiAgICBjYXNlIHR0Ll93aXRoOlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VXaXRoU3RhdGVtZW50KG5vZGUpO1xuICAgIGNhc2UgdHQuYnJhY2VMOlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VCbG9jaygpO1xuICAgIGNhc2UgdHQuc2VtaTpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlRW1wdHlTdGF0ZW1lbnQobm9kZSk7XG4gICAgY2FzZSB0dC5fZXhwb3J0OlxuICAgIGNhc2UgdHQuX2ltcG9ydDpcbiAgICAgIGlmICghdGhpcy5vcHRpb25zLmFsbG93SW1wb3J0RXhwb3J0RXZlcnl3aGVyZSkge1xuICAgICAgICBpZiAoIXRvcExldmVsKSB0aGlzLnJhaXNlKHRoaXMuc3RhcnQsIFwiJ2ltcG9ydCcgYW5kICdleHBvcnQnIG1heSBvbmx5IGFwcGVhciBhdCB0aGUgdG9wIGxldmVsXCIpO1xuICAgICAgICBpZiAoIXRoaXMuaW5Nb2R1bGUpIHRoaXMucmFpc2UodGhpcy5zdGFydCwgXCInaW1wb3J0JyBhbmQgJ2V4cG9ydCcgbWF5IGFwcGVhciBvbmx5IHdpdGggJ3NvdXJjZVR5cGU6IG1vZHVsZSdcIik7XG4gICAgICB9XG4gICAgICByZXR1cm4gc3RhcnR0eXBlID09PSB0dC5faW1wb3J0ID8gdGhpcy5wYXJzZUltcG9ydChub2RlKSA6IHRoaXMucGFyc2VFeHBvcnQobm9kZSk7XG5cbiAgICAvLyBJZiB0aGUgc3RhdGVtZW50IGRvZXMgbm90IHN0YXJ0IHdpdGggYSBzdGF0ZW1lbnQga2V5d29yZCBvciBhXG4gICAgLy8gYnJhY2UsIGl0J3MgYW4gRXhwcmVzc2lvblN0YXRlbWVudCBvciBMYWJlbGVkU3RhdGVtZW50LiBXZVxuICAgIC8vIHNpbXBseSBzdGFydCBwYXJzaW5nIGFuIGV4cHJlc3Npb24sIGFuZCBhZnRlcndhcmRzLCBpZiB0aGVcbiAgICAvLyBuZXh0IHRva2VuIGlzIGEgY29sb24gYW5kIHRoZSBleHByZXNzaW9uIHdhcyBhIHNpbXBsZVxuICAgIC8vIElkZW50aWZpZXIgbm9kZSwgd2Ugc3dpdGNoIHRvIGludGVycHJldGluZyBpdCBhcyBhIGxhYmVsLlxuICAgIGRlZmF1bHQ6XG4gICAgICB2YXIgbWF5YmVOYW1lID0gdGhpcy52YWx1ZSxcbiAgICAgICAgICBleHByID0gdGhpcy5wYXJzZUV4cHJlc3Npb24oKTtcbiAgICAgIGlmIChzdGFydHR5cGUgPT09IHR0Lm5hbWUgJiYgZXhwci50eXBlID09PSBcIklkZW50aWZpZXJcIiAmJiB0aGlzLmVhdCh0dC5jb2xvbikpIHJldHVybiB0aGlzLnBhcnNlTGFiZWxlZFN0YXRlbWVudChub2RlLCBtYXliZU5hbWUsIGV4cHIpO2Vsc2UgcmV0dXJuIHRoaXMucGFyc2VFeHByZXNzaW9uU3RhdGVtZW50KG5vZGUsIGV4cHIpO1xuICB9XG59O1xuXG5wcC5wYXJzZUJyZWFrQ29udGludWVTdGF0ZW1lbnQgPSBmdW5jdGlvbiAobm9kZSwga2V5d29yZCkge1xuICB2YXIgaXNCcmVhayA9IGtleXdvcmQgPT0gXCJicmVha1wiO1xuICB0aGlzLm5leHQoKTtcbiAgaWYgKHRoaXMuZWF0KHR0LnNlbWkpIHx8IHRoaXMuaW5zZXJ0U2VtaWNvbG9uKCkpIG5vZGUubGFiZWwgPSBudWxsO2Vsc2UgaWYgKHRoaXMudHlwZSAhPT0gdHQubmFtZSkgdGhpcy51bmV4cGVjdGVkKCk7ZWxzZSB7XG4gICAgbm9kZS5sYWJlbCA9IHRoaXMucGFyc2VJZGVudCgpO1xuICAgIHRoaXMuc2VtaWNvbG9uKCk7XG4gIH1cblxuICAvLyBWZXJpZnkgdGhhdCB0aGVyZSBpcyBhbiBhY3R1YWwgZGVzdGluYXRpb24gdG8gYnJlYWsgb3JcbiAgLy8gY29udGludWUgdG8uXG4gIGZvciAodmFyIGkgPSAwOyBpIDwgdGhpcy5sYWJlbHMubGVuZ3RoOyArK2kpIHtcbiAgICB2YXIgbGFiID0gdGhpcy5sYWJlbHNbaV07XG4gICAgaWYgKG5vZGUubGFiZWwgPT0gbnVsbCB8fCBsYWIubmFtZSA9PT0gbm9kZS5sYWJlbC5uYW1lKSB7XG4gICAgICBpZiAobGFiLmtpbmQgIT0gbnVsbCAmJiAoaXNCcmVhayB8fCBsYWIua2luZCA9PT0gXCJsb29wXCIpKSBicmVhaztcbiAgICAgIGlmIChub2RlLmxhYmVsICYmIGlzQnJlYWspIGJyZWFrO1xuICAgIH1cbiAgfVxuICBpZiAoaSA9PT0gdGhpcy5sYWJlbHMubGVuZ3RoKSB0aGlzLnJhaXNlKG5vZGUuc3RhcnQsIFwiVW5zeW50YWN0aWMgXCIgKyBrZXl3b3JkKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBpc0JyZWFrID8gXCJCcmVha1N0YXRlbWVudFwiIDogXCJDb250aW51ZVN0YXRlbWVudFwiKTtcbn07XG5cbnBwLnBhcnNlRGVidWdnZXJTdGF0ZW1lbnQgPSBmdW5jdGlvbiAobm9kZSkge1xuICB0aGlzLm5leHQoKTtcbiAgdGhpcy5zZW1pY29sb24oKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkRlYnVnZ2VyU3RhdGVtZW50XCIpO1xufTtcblxucHAucGFyc2VEb1N0YXRlbWVudCA9IGZ1bmN0aW9uIChub2RlKSB7XG4gIHRoaXMubmV4dCgpO1xuICB0aGlzLmxhYmVscy5wdXNoKGxvb3BMYWJlbCk7XG4gIG5vZGUuYm9keSA9IHRoaXMucGFyc2VTdGF0ZW1lbnQoZmFsc2UpO1xuICB0aGlzLmxhYmVscy5wb3AoKTtcbiAgdGhpcy5leHBlY3QodHQuX3doaWxlKTtcbiAgbm9kZS50ZXN0ID0gdGhpcy5wYXJzZVBhcmVuRXhwcmVzc2lvbigpO1xuICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYpIHRoaXMuZWF0KHR0LnNlbWkpO2Vsc2UgdGhpcy5zZW1pY29sb24oKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkRvV2hpbGVTdGF0ZW1lbnRcIik7XG59O1xuXG4vLyBEaXNhbWJpZ3VhdGluZyBiZXR3ZWVuIGEgYGZvcmAgYW5kIGEgYGZvcmAvYGluYCBvciBgZm9yYC9gb2ZgXG4vLyBsb29wIGlzIG5vbi10cml2aWFsLiBCYXNpY2FsbHksIHdlIGhhdmUgdG8gcGFyc2UgdGhlIGluaXQgYHZhcmBcbi8vIHN0YXRlbWVudCBvciBleHByZXNzaW9uLCBkaXNhbGxvd2luZyB0aGUgYGluYCBvcGVyYXRvciAoc2VlXG4vLyB0aGUgc2Vjb25kIHBhcmFtZXRlciB0byBgcGFyc2VFeHByZXNzaW9uYCksIGFuZCB0aGVuIGNoZWNrXG4vLyB3aGV0aGVyIHRoZSBuZXh0IHRva2VuIGlzIGBpbmAgb3IgYG9mYC4gV2hlbiB0aGVyZSBpcyBubyBpbml0XG4vLyBwYXJ0IChzZW1pY29sb24gaW1tZWRpYXRlbHkgYWZ0ZXIgdGhlIG9wZW5pbmcgcGFyZW50aGVzaXMpLCBpdFxuLy8gaXMgYSByZWd1bGFyIGBmb3JgIGxvb3AuXG5cbnBwLnBhcnNlRm9yU3RhdGVtZW50ID0gZnVuY3Rpb24gKG5vZGUpIHtcbiAgdGhpcy5uZXh0KCk7XG4gIHRoaXMubGFiZWxzLnB1c2gobG9vcExhYmVsKTtcbiAgdGhpcy5leHBlY3QodHQucGFyZW5MKTtcbiAgaWYgKHRoaXMudHlwZSA9PT0gdHQuc2VtaSkgcmV0dXJuIHRoaXMucGFyc2VGb3Iobm9kZSwgbnVsbCk7XG4gIGlmICh0aGlzLnR5cGUgPT09IHR0Ll92YXIgfHwgdGhpcy50eXBlID09PSB0dC5fbGV0IHx8IHRoaXMudHlwZSA9PT0gdHQuX2NvbnN0KSB7XG4gICAgdmFyIF9pbml0ID0gdGhpcy5zdGFydE5vZGUoKSxcbiAgICAgICAgdmFyS2luZCA9IHRoaXMudHlwZTtcbiAgICB0aGlzLm5leHQoKTtcbiAgICB0aGlzLnBhcnNlVmFyKF9pbml0LCB0cnVlLCB2YXJLaW5kKTtcbiAgICB0aGlzLmZpbmlzaE5vZGUoX2luaXQsIFwiVmFyaWFibGVEZWNsYXJhdGlvblwiKTtcbiAgICBpZiAoKHRoaXMudHlwZSA9PT0gdHQuX2luIHx8IHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2ICYmIHRoaXMuaXNDb250ZXh0dWFsKFwib2ZcIikpICYmIF9pbml0LmRlY2xhcmF0aW9ucy5sZW5ndGggPT09IDEgJiYgISh2YXJLaW5kICE9PSB0dC5fdmFyICYmIF9pbml0LmRlY2xhcmF0aW9uc1swXS5pbml0KSkgcmV0dXJuIHRoaXMucGFyc2VGb3JJbihub2RlLCBfaW5pdCk7XG4gICAgcmV0dXJuIHRoaXMucGFyc2VGb3Iobm9kZSwgX2luaXQpO1xuICB9XG4gIHZhciByZWZTaG9ydGhhbmREZWZhdWx0UG9zID0geyBzdGFydDogMCB9O1xuICB2YXIgaW5pdCA9IHRoaXMucGFyc2VFeHByZXNzaW9uKHRydWUsIHJlZlNob3J0aGFuZERlZmF1bHRQb3MpO1xuICBpZiAodGhpcy50eXBlID09PSB0dC5faW4gfHwgdGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYgJiYgdGhpcy5pc0NvbnRleHR1YWwoXCJvZlwiKSkge1xuICAgIHRoaXMudG9Bc3NpZ25hYmxlKGluaXQpO1xuICAgIHRoaXMuY2hlY2tMVmFsKGluaXQpO1xuICAgIHJldHVybiB0aGlzLnBhcnNlRm9ySW4obm9kZSwgaW5pdCk7XG4gIH0gZWxzZSBpZiAocmVmU2hvcnRoYW5kRGVmYXVsdFBvcy5zdGFydCkge1xuICAgIHRoaXMudW5leHBlY3RlZChyZWZTaG9ydGhhbmREZWZhdWx0UG9zLnN0YXJ0KTtcbiAgfVxuICByZXR1cm4gdGhpcy5wYXJzZUZvcihub2RlLCBpbml0KTtcbn07XG5cbnBwLnBhcnNlRnVuY3Rpb25TdGF0ZW1lbnQgPSBmdW5jdGlvbiAobm9kZSkge1xuICB0aGlzLm5leHQoKTtcbiAgcmV0dXJuIHRoaXMucGFyc2VGdW5jdGlvbihub2RlLCB0cnVlKTtcbn07XG5cbnBwLnBhcnNlSWZTdGF0ZW1lbnQgPSBmdW5jdGlvbiAobm9kZSkge1xuICB0aGlzLm5leHQoKTtcbiAgbm9kZS50ZXN0ID0gdGhpcy5wYXJzZVBhcmVuRXhwcmVzc2lvbigpO1xuICBub2RlLmNvbnNlcXVlbnQgPSB0aGlzLnBhcnNlU3RhdGVtZW50KGZhbHNlKTtcbiAgbm9kZS5hbHRlcm5hdGUgPSB0aGlzLmVhdCh0dC5fZWxzZSkgPyB0aGlzLnBhcnNlU3RhdGVtZW50KGZhbHNlKSA6IG51bGw7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJJZlN0YXRlbWVudFwiKTtcbn07XG5cbnBwLnBhcnNlUmV0dXJuU3RhdGVtZW50ID0gZnVuY3Rpb24gKG5vZGUpIHtcbiAgaWYgKCF0aGlzLmluRnVuY3Rpb24gJiYgIXRoaXMub3B0aW9ucy5hbGxvd1JldHVybk91dHNpZGVGdW5jdGlvbikgdGhpcy5yYWlzZSh0aGlzLnN0YXJ0LCBcIidyZXR1cm4nIG91dHNpZGUgb2YgZnVuY3Rpb25cIik7XG4gIHRoaXMubmV4dCgpO1xuXG4gIC8vIEluIGByZXR1cm5gIChhbmQgYGJyZWFrYC9gY29udGludWVgKSwgdGhlIGtleXdvcmRzIHdpdGhcbiAgLy8gb3B0aW9uYWwgYXJndW1lbnRzLCB3ZSBlYWdlcmx5IGxvb2sgZm9yIGEgc2VtaWNvbG9uIG9yIHRoZVxuICAvLyBwb3NzaWJpbGl0eSB0byBpbnNlcnQgb25lLlxuXG4gIGlmICh0aGlzLmVhdCh0dC5zZW1pKSB8fCB0aGlzLmluc2VydFNlbWljb2xvbigpKSBub2RlLmFyZ3VtZW50ID0gbnVsbDtlbHNlIHtcbiAgICBub2RlLmFyZ3VtZW50ID0gdGhpcy5wYXJzZUV4cHJlc3Npb24oKTt0aGlzLnNlbWljb2xvbigpO1xuICB9XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJSZXR1cm5TdGF0ZW1lbnRcIik7XG59O1xuXG5wcC5wYXJzZVN3aXRjaFN0YXRlbWVudCA9IGZ1bmN0aW9uIChub2RlKSB7XG4gIHRoaXMubmV4dCgpO1xuICBub2RlLmRpc2NyaW1pbmFudCA9IHRoaXMucGFyc2VQYXJlbkV4cHJlc3Npb24oKTtcbiAgbm9kZS5jYXNlcyA9IFtdO1xuICB0aGlzLmV4cGVjdCh0dC5icmFjZUwpO1xuICB0aGlzLmxhYmVscy5wdXNoKHN3aXRjaExhYmVsKTtcblxuICAvLyBTdGF0ZW1lbnRzIHVuZGVyIG11c3QgYmUgZ3JvdXBlZCAoYnkgbGFiZWwpIGluIFN3aXRjaENhc2VcbiAgLy8gbm9kZXMuIGBjdXJgIGlzIHVzZWQgdG8ga2VlcCB0aGUgbm9kZSB0aGF0IHdlIGFyZSBjdXJyZW50bHlcbiAgLy8gYWRkaW5nIHN0YXRlbWVudHMgdG8uXG5cbiAgZm9yICh2YXIgY3VyLCBzYXdEZWZhdWx0OyB0aGlzLnR5cGUgIT0gdHQuYnJhY2VSOykge1xuICAgIGlmICh0aGlzLnR5cGUgPT09IHR0Ll9jYXNlIHx8IHRoaXMudHlwZSA9PT0gdHQuX2RlZmF1bHQpIHtcbiAgICAgIHZhciBpc0Nhc2UgPSB0aGlzLnR5cGUgPT09IHR0Ll9jYXNlO1xuICAgICAgaWYgKGN1cikgdGhpcy5maW5pc2hOb2RlKGN1ciwgXCJTd2l0Y2hDYXNlXCIpO1xuICAgICAgbm9kZS5jYXNlcy5wdXNoKGN1ciA9IHRoaXMuc3RhcnROb2RlKCkpO1xuICAgICAgY3VyLmNvbnNlcXVlbnQgPSBbXTtcbiAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgaWYgKGlzQ2FzZSkge1xuICAgICAgICBjdXIudGVzdCA9IHRoaXMucGFyc2VFeHByZXNzaW9uKCk7XG4gICAgICB9IGVsc2Uge1xuICAgICAgICBpZiAoc2F3RGVmYXVsdCkgdGhpcy5yYWlzZSh0aGlzLmxhc3RUb2tTdGFydCwgXCJNdWx0aXBsZSBkZWZhdWx0IGNsYXVzZXNcIik7XG4gICAgICAgIHNhd0RlZmF1bHQgPSB0cnVlO1xuICAgICAgICBjdXIudGVzdCA9IG51bGw7XG4gICAgICB9XG4gICAgICB0aGlzLmV4cGVjdCh0dC5jb2xvbik7XG4gICAgfSBlbHNlIHtcbiAgICAgIGlmICghY3VyKSB0aGlzLnVuZXhwZWN0ZWQoKTtcbiAgICAgIGN1ci5jb25zZXF1ZW50LnB1c2godGhpcy5wYXJzZVN0YXRlbWVudCh0cnVlKSk7XG4gICAgfVxuICB9XG4gIGlmIChjdXIpIHRoaXMuZmluaXNoTm9kZShjdXIsIFwiU3dpdGNoQ2FzZVwiKTtcbiAgdGhpcy5uZXh0KCk7IC8vIENsb3NpbmcgYnJhY2VcbiAgdGhpcy5sYWJlbHMucG9wKCk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJTd2l0Y2hTdGF0ZW1lbnRcIik7XG59O1xuXG5wcC5wYXJzZVRocm93U3RhdGVtZW50ID0gZnVuY3Rpb24gKG5vZGUpIHtcbiAgdGhpcy5uZXh0KCk7XG4gIGlmIChsaW5lQnJlYWsudGVzdCh0aGlzLmlucHV0LnNsaWNlKHRoaXMubGFzdFRva0VuZCwgdGhpcy5zdGFydCkpKSB0aGlzLnJhaXNlKHRoaXMubGFzdFRva0VuZCwgXCJJbGxlZ2FsIG5ld2xpbmUgYWZ0ZXIgdGhyb3dcIik7XG4gIG5vZGUuYXJndW1lbnQgPSB0aGlzLnBhcnNlRXhwcmVzc2lvbigpO1xuICB0aGlzLnNlbWljb2xvbigpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiVGhyb3dTdGF0ZW1lbnRcIik7XG59O1xuXG4vLyBSZXVzZWQgZW1wdHkgYXJyYXkgYWRkZWQgZm9yIG5vZGUgZmllbGRzIHRoYXQgYXJlIGFsd2F5cyBlbXB0eS5cblxudmFyIGVtcHR5ID0gW107XG5cbnBwLnBhcnNlVHJ5U3RhdGVtZW50ID0gZnVuY3Rpb24gKG5vZGUpIHtcbiAgdGhpcy5uZXh0KCk7XG4gIG5vZGUuYmxvY2sgPSB0aGlzLnBhcnNlQmxvY2soKTtcbiAgbm9kZS5oYW5kbGVyID0gbnVsbDtcbiAgaWYgKHRoaXMudHlwZSA9PT0gdHQuX2NhdGNoKSB7XG4gICAgdmFyIGNsYXVzZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gICAgdGhpcy5uZXh0KCk7XG4gICAgdGhpcy5leHBlY3QodHQucGFyZW5MKTtcbiAgICBjbGF1c2UucGFyYW0gPSB0aGlzLnBhcnNlQmluZGluZ0F0b20oKTtcbiAgICB0aGlzLmNoZWNrTFZhbChjbGF1c2UucGFyYW0sIHRydWUpO1xuICAgIHRoaXMuZXhwZWN0KHR0LnBhcmVuUik7XG4gICAgY2xhdXNlLmd1YXJkID0gbnVsbDtcbiAgICBjbGF1c2UuYm9keSA9IHRoaXMucGFyc2VCbG9jaygpO1xuICAgIG5vZGUuaGFuZGxlciA9IHRoaXMuZmluaXNoTm9kZShjbGF1c2UsIFwiQ2F0Y2hDbGF1c2VcIik7XG4gIH1cbiAgbm9kZS5ndWFyZGVkSGFuZGxlcnMgPSBlbXB0eTtcbiAgbm9kZS5maW5hbGl6ZXIgPSB0aGlzLmVhdCh0dC5fZmluYWxseSkgPyB0aGlzLnBhcnNlQmxvY2soKSA6IG51bGw7XG4gIGlmICghbm9kZS5oYW5kbGVyICYmICFub2RlLmZpbmFsaXplcikgdGhpcy5yYWlzZShub2RlLnN0YXJ0LCBcIk1pc3NpbmcgY2F0Y2ggb3IgZmluYWxseSBjbGF1c2VcIik7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJUcnlTdGF0ZW1lbnRcIik7XG59O1xuXG5wcC5wYXJzZVZhclN0YXRlbWVudCA9IGZ1bmN0aW9uIChub2RlLCBraW5kKSB7XG4gIHRoaXMubmV4dCgpO1xuICB0aGlzLnBhcnNlVmFyKG5vZGUsIGZhbHNlLCBraW5kKTtcbiAgdGhpcy5zZW1pY29sb24oKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIlZhcmlhYmxlRGVjbGFyYXRpb25cIik7XG59O1xuXG5wcC5wYXJzZVdoaWxlU3RhdGVtZW50ID0gZnVuY3Rpb24gKG5vZGUpIHtcbiAgdGhpcy5uZXh0KCk7XG4gIG5vZGUudGVzdCA9IHRoaXMucGFyc2VQYXJlbkV4cHJlc3Npb24oKTtcbiAgdGhpcy5sYWJlbHMucHVzaChsb29wTGFiZWwpO1xuICBub2RlLmJvZHkgPSB0aGlzLnBhcnNlU3RhdGVtZW50KGZhbHNlKTtcbiAgdGhpcy5sYWJlbHMucG9wKCk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJXaGlsZVN0YXRlbWVudFwiKTtcbn07XG5cbnBwLnBhcnNlV2l0aFN0YXRlbWVudCA9IGZ1bmN0aW9uIChub2RlKSB7XG4gIGlmICh0aGlzLnN0cmljdCkgdGhpcy5yYWlzZSh0aGlzLnN0YXJ0LCBcIid3aXRoJyBpbiBzdHJpY3QgbW9kZVwiKTtcbiAgdGhpcy5uZXh0KCk7XG4gIG5vZGUub2JqZWN0ID0gdGhpcy5wYXJzZVBhcmVuRXhwcmVzc2lvbigpO1xuICBub2RlLmJvZHkgPSB0aGlzLnBhcnNlU3RhdGVtZW50KGZhbHNlKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIldpdGhTdGF0ZW1lbnRcIik7XG59O1xuXG5wcC5wYXJzZUVtcHR5U3RhdGVtZW50ID0gZnVuY3Rpb24gKG5vZGUpIHtcbiAgdGhpcy5uZXh0KCk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJFbXB0eVN0YXRlbWVudFwiKTtcbn07XG5cbnBwLnBhcnNlTGFiZWxlZFN0YXRlbWVudCA9IGZ1bmN0aW9uIChub2RlLCBtYXliZU5hbWUsIGV4cHIpIHtcbiAgZm9yICh2YXIgaSA9IDA7IGkgPCB0aGlzLmxhYmVscy5sZW5ndGg7ICsraSkge1xuICAgIGlmICh0aGlzLmxhYmVsc1tpXS5uYW1lID09PSBtYXliZU5hbWUpIHRoaXMucmFpc2UoZXhwci5zdGFydCwgXCJMYWJlbCAnXCIgKyBtYXliZU5hbWUgKyBcIicgaXMgYWxyZWFkeSBkZWNsYXJlZFwiKTtcbiAgfXZhciBraW5kID0gdGhpcy50eXBlLmlzTG9vcCA/IFwibG9vcFwiIDogdGhpcy50eXBlID09PSB0dC5fc3dpdGNoID8gXCJzd2l0Y2hcIiA6IG51bGw7XG4gIHRoaXMubGFiZWxzLnB1c2goeyBuYW1lOiBtYXliZU5hbWUsIGtpbmQ6IGtpbmQgfSk7XG4gIG5vZGUuYm9keSA9IHRoaXMucGFyc2VTdGF0ZW1lbnQodHJ1ZSk7XG4gIHRoaXMubGFiZWxzLnBvcCgpO1xuICBub2RlLmxhYmVsID0gZXhwcjtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkxhYmVsZWRTdGF0ZW1lbnRcIik7XG59O1xuXG5wcC5wYXJzZUV4cHJlc3Npb25TdGF0ZW1lbnQgPSBmdW5jdGlvbiAobm9kZSwgZXhwcikge1xuICBub2RlLmV4cHJlc3Npb24gPSBleHByO1xuICB0aGlzLnNlbWljb2xvbigpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiRXhwcmVzc2lvblN0YXRlbWVudFwiKTtcbn07XG5cbi8vIFBhcnNlIGEgc2VtaWNvbG9uLWVuY2xvc2VkIGJsb2NrIG9mIHN0YXRlbWVudHMsIGhhbmRsaW5nIGBcInVzZVxuLy8gc3RyaWN0XCJgIGRlY2xhcmF0aW9ucyB3aGVuIGBhbGxvd1N0cmljdGAgaXMgdHJ1ZSAodXNlZCBmb3Jcbi8vIGZ1bmN0aW9uIGJvZGllcykuXG5cbnBwLnBhcnNlQmxvY2sgPSBmdW5jdGlvbiAoYWxsb3dTdHJpY3QpIHtcbiAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpLFxuICAgICAgZmlyc3QgPSB0cnVlLFxuICAgICAgb2xkU3RyaWN0ID0gdW5kZWZpbmVkO1xuICBub2RlLmJvZHkgPSBbXTtcbiAgdGhpcy5leHBlY3QodHQuYnJhY2VMKTtcbiAgd2hpbGUgKCF0aGlzLmVhdCh0dC5icmFjZVIpKSB7XG4gICAgdmFyIHN0bXQgPSB0aGlzLnBhcnNlU3RhdGVtZW50KHRydWUpO1xuICAgIG5vZGUuYm9keS5wdXNoKHN0bXQpO1xuICAgIGlmIChmaXJzdCAmJiBhbGxvd1N0cmljdCAmJiB0aGlzLmlzVXNlU3RyaWN0KHN0bXQpKSB7XG4gICAgICBvbGRTdHJpY3QgPSB0aGlzLnN0cmljdDtcbiAgICAgIHRoaXMuc2V0U3RyaWN0KHRoaXMuc3RyaWN0ID0gdHJ1ZSk7XG4gICAgfVxuICAgIGZpcnN0ID0gZmFsc2U7XG4gIH1cbiAgaWYgKG9sZFN0cmljdCA9PT0gZmFsc2UpIHRoaXMuc2V0U3RyaWN0KGZhbHNlKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkJsb2NrU3RhdGVtZW50XCIpO1xufTtcblxuLy8gUGFyc2UgYSByZWd1bGFyIGBmb3JgIGxvb3AuIFRoZSBkaXNhbWJpZ3VhdGlvbiBjb2RlIGluXG4vLyBgcGFyc2VTdGF0ZW1lbnRgIHdpbGwgYWxyZWFkeSBoYXZlIHBhcnNlZCB0aGUgaW5pdCBzdGF0ZW1lbnQgb3Jcbi8vIGV4cHJlc3Npb24uXG5cbnBwLnBhcnNlRm9yID0gZnVuY3Rpb24gKG5vZGUsIGluaXQpIHtcbiAgbm9kZS5pbml0ID0gaW5pdDtcbiAgdGhpcy5leHBlY3QodHQuc2VtaSk7XG4gIG5vZGUudGVzdCA9IHRoaXMudHlwZSA9PT0gdHQuc2VtaSA/IG51bGwgOiB0aGlzLnBhcnNlRXhwcmVzc2lvbigpO1xuICB0aGlzLmV4cGVjdCh0dC5zZW1pKTtcbiAgbm9kZS51cGRhdGUgPSB0aGlzLnR5cGUgPT09IHR0LnBhcmVuUiA/IG51bGwgOiB0aGlzLnBhcnNlRXhwcmVzc2lvbigpO1xuICB0aGlzLmV4cGVjdCh0dC5wYXJlblIpO1xuICBub2RlLmJvZHkgPSB0aGlzLnBhcnNlU3RhdGVtZW50KGZhbHNlKTtcbiAgdGhpcy5sYWJlbHMucG9wKCk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJGb3JTdGF0ZW1lbnRcIik7XG59O1xuXG4vLyBQYXJzZSBhIGBmb3JgL2BpbmAgYW5kIGBmb3JgL2BvZmAgbG9vcCwgd2hpY2ggYXJlIGFsbW9zdFxuLy8gc2FtZSBmcm9tIHBhcnNlcidzIHBlcnNwZWN0aXZlLlxuXG5wcC5wYXJzZUZvckluID0gZnVuY3Rpb24gKG5vZGUsIGluaXQpIHtcbiAgdmFyIHR5cGUgPSB0aGlzLnR5cGUgPT09IHR0Ll9pbiA/IFwiRm9ySW5TdGF0ZW1lbnRcIiA6IFwiRm9yT2ZTdGF0ZW1lbnRcIjtcbiAgdGhpcy5uZXh0KCk7XG4gIG5vZGUubGVmdCA9IGluaXQ7XG4gIG5vZGUucmlnaHQgPSB0aGlzLnBhcnNlRXhwcmVzc2lvbigpO1xuICB0aGlzLmV4cGVjdCh0dC5wYXJlblIpO1xuICBub2RlLmJvZHkgPSB0aGlzLnBhcnNlU3RhdGVtZW50KGZhbHNlKTtcbiAgdGhpcy5sYWJlbHMucG9wKCk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgdHlwZSk7XG59O1xuXG4vLyBQYXJzZSBhIGxpc3Qgb2YgdmFyaWFibGUgZGVjbGFyYXRpb25zLlxuXG5wcC5wYXJzZVZhciA9IGZ1bmN0aW9uIChub2RlLCBpc0Zvciwga2luZCkge1xuICBub2RlLmRlY2xhcmF0aW9ucyA9IFtdO1xuICBub2RlLmtpbmQgPSBraW5kLmtleXdvcmQ7XG4gIGZvciAoOzspIHtcbiAgICB2YXIgZGVjbCA9IHRoaXMuc3RhcnROb2RlKCk7XG4gICAgdGhpcy5wYXJzZVZhcklkKGRlY2wpO1xuICAgIGlmICh0aGlzLmVhdCh0dC5lcSkpIHtcbiAgICAgIGRlY2wuaW5pdCA9IHRoaXMucGFyc2VNYXliZUFzc2lnbihpc0Zvcik7XG4gICAgfSBlbHNlIGlmIChraW5kID09PSB0dC5fY29uc3QgJiYgISh0aGlzLnR5cGUgPT09IHR0Ll9pbiB8fCB0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNiAmJiB0aGlzLmlzQ29udGV4dHVhbChcIm9mXCIpKSkge1xuICAgICAgdGhpcy51bmV4cGVjdGVkKCk7XG4gICAgfSBlbHNlIGlmIChkZWNsLmlkLnR5cGUgIT0gXCJJZGVudGlmaWVyXCIgJiYgIShpc0ZvciAmJiAodGhpcy50eXBlID09PSB0dC5faW4gfHwgdGhpcy5pc0NvbnRleHR1YWwoXCJvZlwiKSkpKSB7XG4gICAgICB0aGlzLnJhaXNlKHRoaXMubGFzdFRva0VuZCwgXCJDb21wbGV4IGJpbmRpbmcgcGF0dGVybnMgcmVxdWlyZSBhbiBpbml0aWFsaXphdGlvbiB2YWx1ZVwiKTtcbiAgICB9IGVsc2Uge1xuICAgICAgZGVjbC5pbml0ID0gbnVsbDtcbiAgICB9XG4gICAgbm9kZS5kZWNsYXJhdGlvbnMucHVzaCh0aGlzLmZpbmlzaE5vZGUoZGVjbCwgXCJWYXJpYWJsZURlY2xhcmF0b3JcIikpO1xuICAgIGlmICghdGhpcy5lYXQodHQuY29tbWEpKSBicmVhaztcbiAgfVxuICByZXR1cm4gbm9kZTtcbn07XG5cbnBwLnBhcnNlVmFySWQgPSBmdW5jdGlvbiAoZGVjbCkge1xuICBkZWNsLmlkID0gdGhpcy5wYXJzZUJpbmRpbmdBdG9tKCk7XG4gIHRoaXMuY2hlY2tMVmFsKGRlY2wuaWQsIHRydWUpO1xufTtcblxuLy8gUGFyc2UgYSBmdW5jdGlvbiBkZWNsYXJhdGlvbiBvciBsaXRlcmFsIChkZXBlbmRpbmcgb24gdGhlXG4vLyBgaXNTdGF0ZW1lbnRgIHBhcmFtZXRlcikuXG5cbnBwLnBhcnNlRnVuY3Rpb24gPSBmdW5jdGlvbiAobm9kZSwgaXNTdGF0ZW1lbnQsIGFsbG93RXhwcmVzc2lvbkJvZHkpIHtcbiAgdGhpcy5pbml0RnVuY3Rpb24obm9kZSk7XG4gIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNikgbm9kZS5nZW5lcmF0b3IgPSB0aGlzLmVhdCh0dC5zdGFyKTtcbiAgaWYgKGlzU3RhdGVtZW50IHx8IHRoaXMudHlwZSA9PT0gdHQubmFtZSkgbm9kZS5pZCA9IHRoaXMucGFyc2VJZGVudCgpO1xuICB0aGlzLnBhcnNlRnVuY3Rpb25QYXJhbXMobm9kZSk7XG4gIHRoaXMucGFyc2VGdW5jdGlvbkJvZHkobm9kZSwgYWxsb3dFeHByZXNzaW9uQm9keSk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgaXNTdGF0ZW1lbnQgPyBcIkZ1bmN0aW9uRGVjbGFyYXRpb25cIiA6IFwiRnVuY3Rpb25FeHByZXNzaW9uXCIpO1xufTtcblxucHAucGFyc2VGdW5jdGlvblBhcmFtcyA9IGZ1bmN0aW9uIChub2RlKSB7XG4gIHRoaXMuZXhwZWN0KHR0LnBhcmVuTCk7XG4gIG5vZGUucGFyYW1zID0gdGhpcy5wYXJzZUJpbmRpbmdMaXN0KHR0LnBhcmVuUiwgZmFsc2UsIGZhbHNlKTtcbn07XG5cbi8vIFBhcnNlIGEgY2xhc3MgZGVjbGFyYXRpb24gb3IgbGl0ZXJhbCAoZGVwZW5kaW5nIG9uIHRoZVxuLy8gYGlzU3RhdGVtZW50YCBwYXJhbWV0ZXIpLlxuXG5wcC5wYXJzZUNsYXNzID0gZnVuY3Rpb24gKG5vZGUsIGlzU3RhdGVtZW50KSB7XG4gIHRoaXMubmV4dCgpO1xuICB0aGlzLnBhcnNlQ2xhc3NJZChub2RlLCBpc1N0YXRlbWVudCk7XG4gIHRoaXMucGFyc2VDbGFzc1N1cGVyKG5vZGUpO1xuICB2YXIgY2xhc3NCb2R5ID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgdmFyIGhhZENvbnN0cnVjdG9yID0gZmFsc2U7XG4gIGNsYXNzQm9keS5ib2R5ID0gW107XG4gIHRoaXMuZXhwZWN0KHR0LmJyYWNlTCk7XG4gIHdoaWxlICghdGhpcy5lYXQodHQuYnJhY2VSKSkge1xuICAgIGlmICh0aGlzLmVhdCh0dC5zZW1pKSkgY29udGludWU7XG4gICAgdmFyIG1ldGhvZCA9IHRoaXMuc3RhcnROb2RlKCk7XG4gICAgdmFyIGlzR2VuZXJhdG9yID0gdGhpcy5lYXQodHQuc3Rhcik7XG4gICAgdmFyIGlzTWF5YmVTdGF0aWMgPSB0aGlzLnR5cGUgPT09IHR0Lm5hbWUgJiYgdGhpcy52YWx1ZSA9PT0gXCJzdGF0aWNcIjtcbiAgICB0aGlzLnBhcnNlUHJvcGVydHlOYW1lKG1ldGhvZCk7XG4gICAgbWV0aG9kW1wic3RhdGljXCJdID0gaXNNYXliZVN0YXRpYyAmJiB0aGlzLnR5cGUgIT09IHR0LnBhcmVuTDtcbiAgICBpZiAobWV0aG9kW1wic3RhdGljXCJdKSB7XG4gICAgICBpZiAoaXNHZW5lcmF0b3IpIHRoaXMudW5leHBlY3RlZCgpO1xuICAgICAgaXNHZW5lcmF0b3IgPSB0aGlzLmVhdCh0dC5zdGFyKTtcbiAgICAgIHRoaXMucGFyc2VQcm9wZXJ0eU5hbWUobWV0aG9kKTtcbiAgICB9XG4gICAgbWV0aG9kLmtpbmQgPSBcIm1ldGhvZFwiO1xuICAgIGlmICghbWV0aG9kLmNvbXB1dGVkKSB7XG4gICAgICB2YXIga2V5ID0gbWV0aG9kLmtleTtcblxuICAgICAgdmFyIGlzR2V0U2V0ID0gZmFsc2U7XG4gICAgICBpZiAoIWlzR2VuZXJhdG9yICYmIGtleS50eXBlID09PSBcIklkZW50aWZpZXJcIiAmJiB0aGlzLnR5cGUgIT09IHR0LnBhcmVuTCAmJiAoa2V5Lm5hbWUgPT09IFwiZ2V0XCIgfHwga2V5Lm5hbWUgPT09IFwic2V0XCIpKSB7XG4gICAgICAgIGlzR2V0U2V0ID0gdHJ1ZTtcbiAgICAgICAgbWV0aG9kLmtpbmQgPSBrZXkubmFtZTtcbiAgICAgICAga2V5ID0gdGhpcy5wYXJzZVByb3BlcnR5TmFtZShtZXRob2QpO1xuICAgICAgfVxuICAgICAgaWYgKCFtZXRob2RbXCJzdGF0aWNcIl0gJiYgKGtleS50eXBlID09PSBcIklkZW50aWZpZXJcIiAmJiBrZXkubmFtZSA9PT0gXCJjb25zdHJ1Y3RvclwiIHx8IGtleS50eXBlID09PSBcIkxpdGVyYWxcIiAmJiBrZXkudmFsdWUgPT09IFwiY29uc3RydWN0b3JcIikpIHtcbiAgICAgICAgaWYgKGhhZENvbnN0cnVjdG9yKSB0aGlzLnJhaXNlKGtleS5zdGFydCwgXCJEdXBsaWNhdGUgY29uc3RydWN0b3IgaW4gdGhlIHNhbWUgY2xhc3NcIik7XG4gICAgICAgIGlmIChpc0dldFNldCkgdGhpcy5yYWlzZShrZXkuc3RhcnQsIFwiQ29uc3RydWN0b3IgY2FuJ3QgaGF2ZSBnZXQvc2V0IG1vZGlmaWVyXCIpO1xuICAgICAgICBpZiAoaXNHZW5lcmF0b3IpIHRoaXMucmFpc2Uoa2V5LnN0YXJ0LCBcIkNvbnN0cnVjdG9yIGNhbid0IGJlIGEgZ2VuZXJhdG9yXCIpO1xuICAgICAgICBtZXRob2Qua2luZCA9IFwiY29uc3RydWN0b3JcIjtcbiAgICAgICAgaGFkQ29uc3RydWN0b3IgPSB0cnVlO1xuICAgICAgfVxuICAgIH1cbiAgICB0aGlzLnBhcnNlQ2xhc3NNZXRob2QoY2xhc3NCb2R5LCBtZXRob2QsIGlzR2VuZXJhdG9yKTtcbiAgfVxuICBub2RlLmJvZHkgPSB0aGlzLmZpbmlzaE5vZGUoY2xhc3NCb2R5LCBcIkNsYXNzQm9keVwiKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBpc1N0YXRlbWVudCA/IFwiQ2xhc3NEZWNsYXJhdGlvblwiIDogXCJDbGFzc0V4cHJlc3Npb25cIik7XG59O1xuXG5wcC5wYXJzZUNsYXNzTWV0aG9kID0gZnVuY3Rpb24gKGNsYXNzQm9keSwgbWV0aG9kLCBpc0dlbmVyYXRvcikge1xuICBtZXRob2QudmFsdWUgPSB0aGlzLnBhcnNlTWV0aG9kKGlzR2VuZXJhdG9yKTtcbiAgY2xhc3NCb2R5LmJvZHkucHVzaCh0aGlzLmZpbmlzaE5vZGUobWV0aG9kLCBcIk1ldGhvZERlZmluaXRpb25cIikpO1xufTtcblxucHAucGFyc2VDbGFzc0lkID0gZnVuY3Rpb24gKG5vZGUsIGlzU3RhdGVtZW50KSB7XG4gIG5vZGUuaWQgPSB0aGlzLnR5cGUgPT09IHR0Lm5hbWUgPyB0aGlzLnBhcnNlSWRlbnQoKSA6IGlzU3RhdGVtZW50ID8gdGhpcy51bmV4cGVjdGVkKCkgOiBudWxsO1xufTtcblxucHAucGFyc2VDbGFzc1N1cGVyID0gZnVuY3Rpb24gKG5vZGUpIHtcbiAgbm9kZS5zdXBlckNsYXNzID0gdGhpcy5lYXQodHQuX2V4dGVuZHMpID8gdGhpcy5wYXJzZUV4cHJTdWJzY3JpcHRzKCkgOiBudWxsO1xufTtcblxuLy8gUGFyc2VzIG1vZHVsZSBleHBvcnQgZGVjbGFyYXRpb24uXG5cbnBwLnBhcnNlRXhwb3J0ID0gZnVuY3Rpb24gKG5vZGUpIHtcbiAgdGhpcy5uZXh0KCk7XG4gIC8vIGV4cG9ydCAqIGZyb20gJy4uLidcbiAgaWYgKHRoaXMuZWF0KHR0LnN0YXIpKSB7XG4gICAgdGhpcy5leHBlY3RDb250ZXh0dWFsKFwiZnJvbVwiKTtcbiAgICBub2RlLnNvdXJjZSA9IHRoaXMudHlwZSA9PT0gdHQuc3RyaW5nID8gdGhpcy5wYXJzZUV4cHJBdG9tKCkgOiB0aGlzLnVuZXhwZWN0ZWQoKTtcbiAgICB0aGlzLnNlbWljb2xvbigpO1xuICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJFeHBvcnRBbGxEZWNsYXJhdGlvblwiKTtcbiAgfVxuICBpZiAodGhpcy5lYXQodHQuX2RlZmF1bHQpKSB7XG4gICAgLy8gZXhwb3J0IGRlZmF1bHQgLi4uXG4gICAgdmFyIGV4cHIgPSB0aGlzLnBhcnNlTWF5YmVBc3NpZ24oKTtcbiAgICB2YXIgbmVlZHNTZW1pID0gdHJ1ZTtcbiAgICBpZiAoZXhwci50eXBlID09IFwiRnVuY3Rpb25FeHByZXNzaW9uXCIgfHwgZXhwci50eXBlID09IFwiQ2xhc3NFeHByZXNzaW9uXCIpIHtcbiAgICAgIG5lZWRzU2VtaSA9IGZhbHNlO1xuICAgICAgaWYgKGV4cHIuaWQpIHtcbiAgICAgICAgZXhwci50eXBlID0gZXhwci50eXBlID09IFwiRnVuY3Rpb25FeHByZXNzaW9uXCIgPyBcIkZ1bmN0aW9uRGVjbGFyYXRpb25cIiA6IFwiQ2xhc3NEZWNsYXJhdGlvblwiO1xuICAgICAgfVxuICAgIH1cbiAgICBub2RlLmRlY2xhcmF0aW9uID0gZXhwcjtcbiAgICBpZiAobmVlZHNTZW1pKSB0aGlzLnNlbWljb2xvbigpO1xuICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJFeHBvcnREZWZhdWx0RGVjbGFyYXRpb25cIik7XG4gIH1cbiAgLy8gZXhwb3J0IHZhcnxjb25zdHxsZXR8ZnVuY3Rpb258Y2xhc3MgLi4uXG4gIGlmICh0aGlzLnNob3VsZFBhcnNlRXhwb3J0U3RhdGVtZW50KCkpIHtcbiAgICBub2RlLmRlY2xhcmF0aW9uID0gdGhpcy5wYXJzZVN0YXRlbWVudCh0cnVlKTtcbiAgICBub2RlLnNwZWNpZmllcnMgPSBbXTtcbiAgICBub2RlLnNvdXJjZSA9IG51bGw7XG4gIH0gZWxzZSB7XG4gICAgLy8gZXhwb3J0IHsgeCwgeSBhcyB6IH0gW2Zyb20gJy4uLiddXG4gICAgbm9kZS5kZWNsYXJhdGlvbiA9IG51bGw7XG4gICAgbm9kZS5zcGVjaWZpZXJzID0gdGhpcy5wYXJzZUV4cG9ydFNwZWNpZmllcnMoKTtcbiAgICBpZiAodGhpcy5lYXRDb250ZXh0dWFsKFwiZnJvbVwiKSkge1xuICAgICAgbm9kZS5zb3VyY2UgPSB0aGlzLnR5cGUgPT09IHR0LnN0cmluZyA/IHRoaXMucGFyc2VFeHByQXRvbSgpIDogdGhpcy51bmV4cGVjdGVkKCk7XG4gICAgfSBlbHNlIHtcbiAgICAgIG5vZGUuc291cmNlID0gbnVsbDtcbiAgICB9XG4gICAgdGhpcy5zZW1pY29sb24oKTtcbiAgfVxuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiRXhwb3J0TmFtZWREZWNsYXJhdGlvblwiKTtcbn07XG5cbnBwLnNob3VsZFBhcnNlRXhwb3J0U3RhdGVtZW50ID0gZnVuY3Rpb24gKCkge1xuICByZXR1cm4gdGhpcy50eXBlLmtleXdvcmQ7XG59O1xuXG4vLyBQYXJzZXMgYSBjb21tYS1zZXBhcmF0ZWQgbGlzdCBvZiBtb2R1bGUgZXhwb3J0cy5cblxucHAucGFyc2VFeHBvcnRTcGVjaWZpZXJzID0gZnVuY3Rpb24gKCkge1xuICB2YXIgbm9kZXMgPSBbXSxcbiAgICAgIGZpcnN0ID0gdHJ1ZTtcbiAgLy8gZXhwb3J0IHsgeCwgeSBhcyB6IH0gW2Zyb20gJy4uLiddXG4gIHRoaXMuZXhwZWN0KHR0LmJyYWNlTCk7XG4gIHdoaWxlICghdGhpcy5lYXQodHQuYnJhY2VSKSkge1xuICAgIGlmICghZmlyc3QpIHtcbiAgICAgIHRoaXMuZXhwZWN0KHR0LmNvbW1hKTtcbiAgICAgIGlmICh0aGlzLmFmdGVyVHJhaWxpbmdDb21tYSh0dC5icmFjZVIpKSBicmVhaztcbiAgICB9IGVsc2UgZmlyc3QgPSBmYWxzZTtcblxuICAgIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgICBub2RlLmxvY2FsID0gdGhpcy5wYXJzZUlkZW50KHRoaXMudHlwZSA9PT0gdHQuX2RlZmF1bHQpO1xuICAgIG5vZGUuZXhwb3J0ZWQgPSB0aGlzLmVhdENvbnRleHR1YWwoXCJhc1wiKSA/IHRoaXMucGFyc2VJZGVudCh0cnVlKSA6IG5vZGUubG9jYWw7XG4gICAgbm9kZXMucHVzaCh0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJFeHBvcnRTcGVjaWZpZXJcIikpO1xuICB9XG4gIHJldHVybiBub2Rlcztcbn07XG5cbi8vIFBhcnNlcyBpbXBvcnQgZGVjbGFyYXRpb24uXG5cbnBwLnBhcnNlSW1wb3J0ID0gZnVuY3Rpb24gKG5vZGUpIHtcbiAgdGhpcy5uZXh0KCk7XG4gIC8vIGltcG9ydCAnLi4uJ1xuICBpZiAodGhpcy50eXBlID09PSB0dC5zdHJpbmcpIHtcbiAgICBub2RlLnNwZWNpZmllcnMgPSBlbXB0eTtcbiAgICBub2RlLnNvdXJjZSA9IHRoaXMucGFyc2VFeHByQXRvbSgpO1xuICAgIG5vZGUua2luZCA9IFwiXCI7XG4gIH0gZWxzZSB7XG4gICAgbm9kZS5zcGVjaWZpZXJzID0gdGhpcy5wYXJzZUltcG9ydFNwZWNpZmllcnMoKTtcbiAgICB0aGlzLmV4cGVjdENvbnRleHR1YWwoXCJmcm9tXCIpO1xuICAgIG5vZGUuc291cmNlID0gdGhpcy50eXBlID09PSB0dC5zdHJpbmcgPyB0aGlzLnBhcnNlRXhwckF0b20oKSA6IHRoaXMudW5leHBlY3RlZCgpO1xuICB9XG4gIHRoaXMuc2VtaWNvbG9uKCk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJJbXBvcnREZWNsYXJhdGlvblwiKTtcbn07XG5cbi8vIFBhcnNlcyBhIGNvbW1hLXNlcGFyYXRlZCBsaXN0IG9mIG1vZHVsZSBpbXBvcnRzLlxuXG5wcC5wYXJzZUltcG9ydFNwZWNpZmllcnMgPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBub2RlcyA9IFtdLFxuICAgICAgZmlyc3QgPSB0cnVlO1xuICBpZiAodGhpcy50eXBlID09PSB0dC5uYW1lKSB7XG4gICAgLy8gaW1wb3J0IGRlZmF1bHRPYmosIHsgeCwgeSBhcyB6IH0gZnJvbSAnLi4uJ1xuICAgIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgICBub2RlLmxvY2FsID0gdGhpcy5wYXJzZUlkZW50KCk7XG4gICAgdGhpcy5jaGVja0xWYWwobm9kZS5sb2NhbCwgdHJ1ZSk7XG4gICAgbm9kZXMucHVzaCh0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJJbXBvcnREZWZhdWx0U3BlY2lmaWVyXCIpKTtcbiAgICBpZiAoIXRoaXMuZWF0KHR0LmNvbW1hKSkgcmV0dXJuIG5vZGVzO1xuICB9XG4gIGlmICh0aGlzLnR5cGUgPT09IHR0LnN0YXIpIHtcbiAgICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gICAgdGhpcy5uZXh0KCk7XG4gICAgdGhpcy5leHBlY3RDb250ZXh0dWFsKFwiYXNcIik7XG4gICAgbm9kZS5sb2NhbCA9IHRoaXMucGFyc2VJZGVudCgpO1xuICAgIHRoaXMuY2hlY2tMVmFsKG5vZGUubG9jYWwsIHRydWUpO1xuICAgIG5vZGVzLnB1c2godGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiSW1wb3J0TmFtZXNwYWNlU3BlY2lmaWVyXCIpKTtcbiAgICByZXR1cm4gbm9kZXM7XG4gIH1cbiAgdGhpcy5leHBlY3QodHQuYnJhY2VMKTtcbiAgd2hpbGUgKCF0aGlzLmVhdCh0dC5icmFjZVIpKSB7XG4gICAgaWYgKCFmaXJzdCkge1xuICAgICAgdGhpcy5leHBlY3QodHQuY29tbWEpO1xuICAgICAgaWYgKHRoaXMuYWZ0ZXJUcmFpbGluZ0NvbW1hKHR0LmJyYWNlUikpIGJyZWFrO1xuICAgIH0gZWxzZSBmaXJzdCA9IGZhbHNlO1xuXG4gICAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICAgIG5vZGUuaW1wb3J0ZWQgPSB0aGlzLnBhcnNlSWRlbnQodHJ1ZSk7XG4gICAgbm9kZS5sb2NhbCA9IHRoaXMuZWF0Q29udGV4dHVhbChcImFzXCIpID8gdGhpcy5wYXJzZUlkZW50KCkgOiBub2RlLmltcG9ydGVkO1xuICAgIHRoaXMuY2hlY2tMVmFsKG5vZGUubG9jYWwsIHRydWUpO1xuICAgIG5vZGVzLnB1c2godGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiSW1wb3J0U3BlY2lmaWVyXCIpKTtcbiAgfVxuICByZXR1cm4gbm9kZXM7XG59O1xuXG59LHtcIi4vc3RhdGVcIjoxMyxcIi4vdG9rZW50eXBlXCI6MTcsXCIuL3doaXRlc3BhY2VcIjoxOX1dLDE1OltmdW5jdGlvbihfZGVyZXFfLG1vZHVsZSxleHBvcnRzKXtcblwidXNlIHN0cmljdFwiO1xuXG52YXIgX2NsYXNzQ2FsbENoZWNrID0gZnVuY3Rpb24gKGluc3RhbmNlLCBDb25zdHJ1Y3RvcikgeyBpZiAoIShpbnN0YW5jZSBpbnN0YW5jZW9mIENvbnN0cnVjdG9yKSkgeyB0aHJvdyBuZXcgVHlwZUVycm9yKFwiQ2Fubm90IGNhbGwgYSBjbGFzcyBhcyBhIGZ1bmN0aW9uXCIpOyB9IH07XG5cbmV4cG9ydHMuX19lc01vZHVsZSA9IHRydWU7XG4vLyBUaGUgYWxnb3JpdGhtIHVzZWQgdG8gZGV0ZXJtaW5lIHdoZXRoZXIgYSByZWdleHAgY2FuIGFwcGVhciBhdCBhXG4vLyBnaXZlbiBwb2ludCBpbiB0aGUgcHJvZ3JhbSBpcyBsb29zZWx5IGJhc2VkIG9uIHN3ZWV0LmpzJyBhcHByb2FjaC5cbi8vIFNlZSBodHRwczovL2dpdGh1Yi5jb20vbW96aWxsYS9zd2VldC5qcy93aWtpL2Rlc2lnblxuXG52YXIgUGFyc2VyID0gX2RlcmVxXyhcIi4vc3RhdGVcIikuUGFyc2VyO1xuXG52YXIgdHQgPSBfZGVyZXFfKFwiLi90b2tlbnR5cGVcIikudHlwZXM7XG5cbnZhciBsaW5lQnJlYWsgPSBfZGVyZXFfKFwiLi93aGl0ZXNwYWNlXCIpLmxpbmVCcmVhaztcblxudmFyIFRva0NvbnRleHQgPSBleHBvcnRzLlRva0NvbnRleHQgPSBmdW5jdGlvbiBUb2tDb250ZXh0KHRva2VuLCBpc0V4cHIsIHByZXNlcnZlU3BhY2UsIG92ZXJyaWRlKSB7XG4gIF9jbGFzc0NhbGxDaGVjayh0aGlzLCBUb2tDb250ZXh0KTtcblxuICB0aGlzLnRva2VuID0gdG9rZW47XG4gIHRoaXMuaXNFeHByID0gaXNFeHByO1xuICB0aGlzLnByZXNlcnZlU3BhY2UgPSBwcmVzZXJ2ZVNwYWNlO1xuICB0aGlzLm92ZXJyaWRlID0gb3ZlcnJpZGU7XG59O1xuXG52YXIgdHlwZXMgPSB7XG4gIGJfc3RhdDogbmV3IFRva0NvbnRleHQoXCJ7XCIsIGZhbHNlKSxcbiAgYl9leHByOiBuZXcgVG9rQ29udGV4dChcIntcIiwgdHJ1ZSksXG4gIGJfdG1wbDogbmV3IFRva0NvbnRleHQoXCIke1wiLCB0cnVlKSxcbiAgcF9zdGF0OiBuZXcgVG9rQ29udGV4dChcIihcIiwgZmFsc2UpLFxuICBwX2V4cHI6IG5ldyBUb2tDb250ZXh0KFwiKFwiLCB0cnVlKSxcbiAgcV90bXBsOiBuZXcgVG9rQ29udGV4dChcImBcIiwgdHJ1ZSwgdHJ1ZSwgZnVuY3Rpb24gKHApIHtcbiAgICByZXR1cm4gcC5yZWFkVG1wbFRva2VuKCk7XG4gIH0pLFxuICBmX2V4cHI6IG5ldyBUb2tDb250ZXh0KFwiZnVuY3Rpb25cIiwgdHJ1ZSlcbn07XG5cbmV4cG9ydHMudHlwZXMgPSB0eXBlcztcbnZhciBwcCA9IFBhcnNlci5wcm90b3R5cGU7XG5cbnBwLmluaXRpYWxDb250ZXh0ID0gZnVuY3Rpb24gKCkge1xuICByZXR1cm4gW3R5cGVzLmJfc3RhdF07XG59O1xuXG5wcC5icmFjZUlzQmxvY2sgPSBmdW5jdGlvbiAocHJldlR5cGUpIHtcbiAgdmFyIHBhcmVudCA9IHVuZGVmaW5lZDtcbiAgaWYgKHByZXZUeXBlID09PSB0dC5jb2xvbiAmJiAocGFyZW50ID0gdGhpcy5jdXJDb250ZXh0KCkpLnRva2VuID09IFwie1wiKSByZXR1cm4gIXBhcmVudC5pc0V4cHI7XG4gIGlmIChwcmV2VHlwZSA9PT0gdHQuX3JldHVybikgcmV0dXJuIGxpbmVCcmVhay50ZXN0KHRoaXMuaW5wdXQuc2xpY2UodGhpcy5sYXN0VG9rRW5kLCB0aGlzLnN0YXJ0KSk7XG4gIGlmIChwcmV2VHlwZSA9PT0gdHQuX2Vsc2UgfHwgcHJldlR5cGUgPT09IHR0LnNlbWkgfHwgcHJldlR5cGUgPT09IHR0LmVvZikgcmV0dXJuIHRydWU7XG4gIGlmIChwcmV2VHlwZSA9PSB0dC5icmFjZUwpIHJldHVybiB0aGlzLmN1ckNvbnRleHQoKSA9PT0gdHlwZXMuYl9zdGF0O1xuICByZXR1cm4gIXRoaXMuZXhwckFsbG93ZWQ7XG59O1xuXG5wcC51cGRhdGVDb250ZXh0ID0gZnVuY3Rpb24gKHByZXZUeXBlKSB7XG4gIHZhciB1cGRhdGUgPSB1bmRlZmluZWQsXG4gICAgICB0eXBlID0gdGhpcy50eXBlO1xuICBpZiAodHlwZS5rZXl3b3JkICYmIHByZXZUeXBlID09IHR0LmRvdCkgdGhpcy5leHByQWxsb3dlZCA9IGZhbHNlO2Vsc2UgaWYgKHVwZGF0ZSA9IHR5cGUudXBkYXRlQ29udGV4dCkgdXBkYXRlLmNhbGwodGhpcywgcHJldlR5cGUpO2Vsc2UgdGhpcy5leHByQWxsb3dlZCA9IHR5cGUuYmVmb3JlRXhwcjtcbn07XG5cbi8vIFRva2VuLXNwZWNpZmljIGNvbnRleHQgdXBkYXRlIGNvZGVcblxudHQucGFyZW5SLnVwZGF0ZUNvbnRleHQgPSB0dC5icmFjZVIudXBkYXRlQ29udGV4dCA9IGZ1bmN0aW9uICgpIHtcbiAgaWYgKHRoaXMuY29udGV4dC5sZW5ndGggPT0gMSkge1xuICAgIHRoaXMuZXhwckFsbG93ZWQgPSB0cnVlO1xuICAgIHJldHVybjtcbiAgfVxuICB2YXIgb3V0ID0gdGhpcy5jb250ZXh0LnBvcCgpO1xuICBpZiAob3V0ID09PSB0eXBlcy5iX3N0YXQgJiYgdGhpcy5jdXJDb250ZXh0KCkgPT09IHR5cGVzLmZfZXhwcikge1xuICAgIHRoaXMuY29udGV4dC5wb3AoKTtcbiAgICB0aGlzLmV4cHJBbGxvd2VkID0gZmFsc2U7XG4gIH0gZWxzZSBpZiAob3V0ID09PSB0eXBlcy5iX3RtcGwpIHtcbiAgICB0aGlzLmV4cHJBbGxvd2VkID0gdHJ1ZTtcbiAgfSBlbHNlIHtcbiAgICB0aGlzLmV4cHJBbGxvd2VkID0gIW91dC5pc0V4cHI7XG4gIH1cbn07XG5cbnR0LmJyYWNlTC51cGRhdGVDb250ZXh0ID0gZnVuY3Rpb24gKHByZXZUeXBlKSB7XG4gIHRoaXMuY29udGV4dC5wdXNoKHRoaXMuYnJhY2VJc0Jsb2NrKHByZXZUeXBlKSA/IHR5cGVzLmJfc3RhdCA6IHR5cGVzLmJfZXhwcik7XG4gIHRoaXMuZXhwckFsbG93ZWQgPSB0cnVlO1xufTtcblxudHQuZG9sbGFyQnJhY2VMLnVwZGF0ZUNvbnRleHQgPSBmdW5jdGlvbiAoKSB7XG4gIHRoaXMuY29udGV4dC5wdXNoKHR5cGVzLmJfdG1wbCk7XG4gIHRoaXMuZXhwckFsbG93ZWQgPSB0cnVlO1xufTtcblxudHQucGFyZW5MLnVwZGF0ZUNvbnRleHQgPSBmdW5jdGlvbiAocHJldlR5cGUpIHtcbiAgdmFyIHN0YXRlbWVudFBhcmVucyA9IHByZXZUeXBlID09PSB0dC5faWYgfHwgcHJldlR5cGUgPT09IHR0Ll9mb3IgfHwgcHJldlR5cGUgPT09IHR0Ll93aXRoIHx8IHByZXZUeXBlID09PSB0dC5fd2hpbGU7XG4gIHRoaXMuY29udGV4dC5wdXNoKHN0YXRlbWVudFBhcmVucyA/IHR5cGVzLnBfc3RhdCA6IHR5cGVzLnBfZXhwcik7XG4gIHRoaXMuZXhwckFsbG93ZWQgPSB0cnVlO1xufTtcblxudHQuaW5jRGVjLnVwZGF0ZUNvbnRleHQgPSBmdW5jdGlvbiAoKSB7fTtcblxudHQuX2Z1bmN0aW9uLnVwZGF0ZUNvbnRleHQgPSBmdW5jdGlvbiAoKSB7XG4gIGlmICh0aGlzLmN1ckNvbnRleHQoKSAhPT0gdHlwZXMuYl9zdGF0KSB0aGlzLmNvbnRleHQucHVzaCh0eXBlcy5mX2V4cHIpO1xuICB0aGlzLmV4cHJBbGxvd2VkID0gZmFsc2U7XG59O1xuXG50dC5iYWNrUXVvdGUudXBkYXRlQ29udGV4dCA9IGZ1bmN0aW9uICgpIHtcbiAgaWYgKHRoaXMuY3VyQ29udGV4dCgpID09PSB0eXBlcy5xX3RtcGwpIHRoaXMuY29udGV4dC5wb3AoKTtlbHNlIHRoaXMuY29udGV4dC5wdXNoKHR5cGVzLnFfdG1wbCk7XG4gIHRoaXMuZXhwckFsbG93ZWQgPSBmYWxzZTtcbn07XG5cbi8vIHRva0V4cHJBbGxvd2VkIHN0YXlzIHVuY2hhbmdlZFxuXG59LHtcIi4vc3RhdGVcIjoxMyxcIi4vdG9rZW50eXBlXCI6MTcsXCIuL3doaXRlc3BhY2VcIjoxOX1dLDE2OltmdW5jdGlvbihfZGVyZXFfLG1vZHVsZSxleHBvcnRzKXtcblwidXNlIHN0cmljdFwiO1xuXG52YXIgX2NsYXNzQ2FsbENoZWNrID0gZnVuY3Rpb24gKGluc3RhbmNlLCBDb25zdHJ1Y3RvcikgeyBpZiAoIShpbnN0YW5jZSBpbnN0YW5jZW9mIENvbnN0cnVjdG9yKSkgeyB0aHJvdyBuZXcgVHlwZUVycm9yKFwiQ2Fubm90IGNhbGwgYSBjbGFzcyBhcyBhIGZ1bmN0aW9uXCIpOyB9IH07XG5cbmV4cG9ydHMuX19lc01vZHVsZSA9IHRydWU7XG5cbnZhciBfaWRlbnRpZmllciA9IF9kZXJlcV8oXCIuL2lkZW50aWZpZXJcIik7XG5cbnZhciBpc0lkZW50aWZpZXJTdGFydCA9IF9pZGVudGlmaWVyLmlzSWRlbnRpZmllclN0YXJ0O1xudmFyIGlzSWRlbnRpZmllckNoYXIgPSBfaWRlbnRpZmllci5pc0lkZW50aWZpZXJDaGFyO1xuXG52YXIgX3Rva2VudHlwZSA9IF9kZXJlcV8oXCIuL3Rva2VudHlwZVwiKTtcblxudmFyIHR0ID0gX3Rva2VudHlwZS50eXBlcztcbnZhciBrZXl3b3JkVHlwZXMgPSBfdG9rZW50eXBlLmtleXdvcmRzO1xuXG52YXIgUGFyc2VyID0gX2RlcmVxXyhcIi4vc3RhdGVcIikuUGFyc2VyO1xuXG52YXIgU291cmNlTG9jYXRpb24gPSBfZGVyZXFfKFwiLi9sb2NhdGlvblwiKS5Tb3VyY2VMb2NhdGlvbjtcblxudmFyIF93aGl0ZXNwYWNlID0gX2RlcmVxXyhcIi4vd2hpdGVzcGFjZVwiKTtcblxudmFyIGxpbmVCcmVhayA9IF93aGl0ZXNwYWNlLmxpbmVCcmVhaztcbnZhciBsaW5lQnJlYWtHID0gX3doaXRlc3BhY2UubGluZUJyZWFrRztcbnZhciBpc05ld0xpbmUgPSBfd2hpdGVzcGFjZS5pc05ld0xpbmU7XG52YXIgbm9uQVNDSUl3aGl0ZXNwYWNlID0gX3doaXRlc3BhY2Uubm9uQVNDSUl3aGl0ZXNwYWNlO1xuXG4vLyBPYmplY3QgdHlwZSB1c2VkIHRvIHJlcHJlc2VudCB0b2tlbnMuIE5vdGUgdGhhdCBub3JtYWxseSwgdG9rZW5zXG4vLyBzaW1wbHkgZXhpc3QgYXMgcHJvcGVydGllcyBvbiB0aGUgcGFyc2VyIG9iamVjdC4gVGhpcyBpcyBvbmx5XG4vLyB1c2VkIGZvciB0aGUgb25Ub2tlbiBjYWxsYmFjayBhbmQgdGhlIGV4dGVybmFsIHRva2VuaXplci5cblxudmFyIFRva2VuID0gZXhwb3J0cy5Ub2tlbiA9IGZ1bmN0aW9uIFRva2VuKHApIHtcbiAgX2NsYXNzQ2FsbENoZWNrKHRoaXMsIFRva2VuKTtcblxuICB0aGlzLnR5cGUgPSBwLnR5cGU7XG4gIHRoaXMudmFsdWUgPSBwLnZhbHVlO1xuICB0aGlzLnN0YXJ0ID0gcC5zdGFydDtcbiAgdGhpcy5lbmQgPSBwLmVuZDtcbiAgaWYgKHAub3B0aW9ucy5sb2NhdGlvbnMpIHRoaXMubG9jID0gbmV3IFNvdXJjZUxvY2F0aW9uKHAsIHAuc3RhcnRMb2MsIHAuZW5kTG9jKTtcbiAgaWYgKHAub3B0aW9ucy5yYW5nZXMpIHRoaXMucmFuZ2UgPSBbcC5zdGFydCwgcC5lbmRdO1xufTtcblxuLy8gIyMgVG9rZW5pemVyXG5cbnZhciBwcCA9IFBhcnNlci5wcm90b3R5cGU7XG5cbi8vIEFyZSB3ZSBydW5uaW5nIHVuZGVyIFJoaW5vP1xudmFyIGlzUmhpbm8gPSB0eXBlb2YgUGFja2FnZXMgIT09IFwidW5kZWZpbmVkXCI7XG5cbi8vIE1vdmUgdG8gdGhlIG5leHQgdG9rZW5cblxucHAubmV4dCA9IGZ1bmN0aW9uICgpIHtcbiAgaWYgKHRoaXMub3B0aW9ucy5vblRva2VuKSB0aGlzLm9wdGlvbnMub25Ub2tlbihuZXcgVG9rZW4odGhpcykpO1xuXG4gIHRoaXMubGFzdFRva0VuZCA9IHRoaXMuZW5kO1xuICB0aGlzLmxhc3RUb2tTdGFydCA9IHRoaXMuc3RhcnQ7XG4gIHRoaXMubGFzdFRva0VuZExvYyA9IHRoaXMuZW5kTG9jO1xuICB0aGlzLmxhc3RUb2tTdGFydExvYyA9IHRoaXMuc3RhcnRMb2M7XG4gIHRoaXMubmV4dFRva2VuKCk7XG59O1xuXG5wcC5nZXRUb2tlbiA9IGZ1bmN0aW9uICgpIHtcbiAgdGhpcy5uZXh0KCk7XG4gIHJldHVybiBuZXcgVG9rZW4odGhpcyk7XG59O1xuXG4vLyBJZiB3ZSdyZSBpbiBhbiBFUzYgZW52aXJvbm1lbnQsIG1ha2UgcGFyc2VycyBpdGVyYWJsZVxuaWYgKHR5cGVvZiBTeW1ib2wgIT09IFwidW5kZWZpbmVkXCIpIHBwW1N5bWJvbC5pdGVyYXRvcl0gPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBzZWxmID0gdGhpcztcbiAgcmV0dXJuIHsgbmV4dDogZnVuY3Rpb24gbmV4dCgpIHtcbiAgICAgIHZhciB0b2tlbiA9IHNlbGYuZ2V0VG9rZW4oKTtcbiAgICAgIHJldHVybiB7XG4gICAgICAgIGRvbmU6IHRva2VuLnR5cGUgPT09IHR0LmVvZixcbiAgICAgICAgdmFsdWU6IHRva2VuXG4gICAgICB9O1xuICAgIH0gfTtcbn07XG5cbi8vIFRvZ2dsZSBzdHJpY3QgbW9kZS4gUmUtcmVhZHMgdGhlIG5leHQgbnVtYmVyIG9yIHN0cmluZyB0byBwbGVhc2Vcbi8vIHBlZGFudGljIHRlc3RzIChgXCJ1c2Ugc3RyaWN0XCI7IDAxMDtgIHNob3VsZCBmYWlsKS5cblxucHAuc2V0U3RyaWN0ID0gZnVuY3Rpb24gKHN0cmljdCkge1xuICB0aGlzLnN0cmljdCA9IHN0cmljdDtcbiAgaWYgKHRoaXMudHlwZSAhPT0gdHQubnVtICYmIHRoaXMudHlwZSAhPT0gdHQuc3RyaW5nKSByZXR1cm47XG4gIHRoaXMucG9zID0gdGhpcy5zdGFydDtcbiAgaWYgKHRoaXMub3B0aW9ucy5sb2NhdGlvbnMpIHtcbiAgICB3aGlsZSAodGhpcy5wb3MgPCB0aGlzLmxpbmVTdGFydCkge1xuICAgICAgdGhpcy5saW5lU3RhcnQgPSB0aGlzLmlucHV0Lmxhc3RJbmRleE9mKFwiXFxuXCIsIHRoaXMubGluZVN0YXJ0IC0gMikgKyAxO1xuICAgICAgLS10aGlzLmN1ckxpbmU7XG4gICAgfVxuICB9XG4gIHRoaXMubmV4dFRva2VuKCk7XG59O1xuXG5wcC5jdXJDb250ZXh0ID0gZnVuY3Rpb24gKCkge1xuICByZXR1cm4gdGhpcy5jb250ZXh0W3RoaXMuY29udGV4dC5sZW5ndGggLSAxXTtcbn07XG5cbi8vIFJlYWQgYSBzaW5nbGUgdG9rZW4sIHVwZGF0aW5nIHRoZSBwYXJzZXIgb2JqZWN0J3MgdG9rZW4tcmVsYXRlZFxuLy8gcHJvcGVydGllcy5cblxucHAubmV4dFRva2VuID0gZnVuY3Rpb24gKCkge1xuICB2YXIgY3VyQ29udGV4dCA9IHRoaXMuY3VyQ29udGV4dCgpO1xuICBpZiAoIWN1ckNvbnRleHQgfHwgIWN1ckNvbnRleHQucHJlc2VydmVTcGFjZSkgdGhpcy5za2lwU3BhY2UoKTtcblxuICB0aGlzLnN0YXJ0ID0gdGhpcy5wb3M7XG4gIGlmICh0aGlzLm9wdGlvbnMubG9jYXRpb25zKSB0aGlzLnN0YXJ0TG9jID0gdGhpcy5jdXJQb3NpdGlvbigpO1xuICBpZiAodGhpcy5wb3MgPj0gdGhpcy5pbnB1dC5sZW5ndGgpIHJldHVybiB0aGlzLmZpbmlzaFRva2VuKHR0LmVvZik7XG5cbiAgaWYgKGN1ckNvbnRleHQub3ZlcnJpZGUpIHJldHVybiBjdXJDb250ZXh0Lm92ZXJyaWRlKHRoaXMpO2Vsc2UgdGhpcy5yZWFkVG9rZW4odGhpcy5mdWxsQ2hhckNvZGVBdFBvcygpKTtcbn07XG5cbnBwLnJlYWRUb2tlbiA9IGZ1bmN0aW9uIChjb2RlKSB7XG4gIC8vIElkZW50aWZpZXIgb3Iga2V5d29yZC4gJ1xcdVhYWFgnIHNlcXVlbmNlcyBhcmUgYWxsb3dlZCBpblxuICAvLyBpZGVudGlmaWVycywgc28gJ1xcJyBhbHNvIGRpc3BhdGNoZXMgdG8gdGhhdC5cbiAgaWYgKGlzSWRlbnRpZmllclN0YXJ0KGNvZGUsIHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KSB8fCBjb2RlID09PSA5MiAvKiAnXFwnICovKSByZXR1cm4gdGhpcy5yZWFkV29yZCgpO1xuXG4gIHJldHVybiB0aGlzLmdldFRva2VuRnJvbUNvZGUoY29kZSk7XG59O1xuXG5wcC5mdWxsQ2hhckNvZGVBdFBvcyA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIGNvZGUgPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MpO1xuICBpZiAoY29kZSA8PSA1NTI5NSB8fCBjb2RlID49IDU3MzQ0KSByZXR1cm4gY29kZTtcbiAgdmFyIG5leHQgPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAxKTtcbiAgcmV0dXJuIChjb2RlIDw8IDEwKSArIG5leHQgLSA1NjYxMzg4ODtcbn07XG5cbnBwLnNraXBCbG9ja0NvbW1lbnQgPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBzdGFydExvYyA9IHRoaXMub3B0aW9ucy5vbkNvbW1lbnQgJiYgdGhpcy5vcHRpb25zLmxvY2F0aW9ucyAmJiB0aGlzLmN1clBvc2l0aW9uKCk7XG4gIHZhciBzdGFydCA9IHRoaXMucG9zLFxuICAgICAgZW5kID0gdGhpcy5pbnB1dC5pbmRleE9mKFwiKi9cIiwgdGhpcy5wb3MgKz0gMik7XG4gIGlmIChlbmQgPT09IC0xKSB0aGlzLnJhaXNlKHRoaXMucG9zIC0gMiwgXCJVbnRlcm1pbmF0ZWQgY29tbWVudFwiKTtcbiAgdGhpcy5wb3MgPSBlbmQgKyAyO1xuICBpZiAodGhpcy5vcHRpb25zLmxvY2F0aW9ucykge1xuICAgIGxpbmVCcmVha0cubGFzdEluZGV4ID0gc3RhcnQ7XG4gICAgdmFyIG1hdGNoID0gdW5kZWZpbmVkO1xuICAgIHdoaWxlICgobWF0Y2ggPSBsaW5lQnJlYWtHLmV4ZWModGhpcy5pbnB1dCkpICYmIG1hdGNoLmluZGV4IDwgdGhpcy5wb3MpIHtcbiAgICAgICsrdGhpcy5jdXJMaW5lO1xuICAgICAgdGhpcy5saW5lU3RhcnQgPSBtYXRjaC5pbmRleCArIG1hdGNoWzBdLmxlbmd0aDtcbiAgICB9XG4gIH1cbiAgaWYgKHRoaXMub3B0aW9ucy5vbkNvbW1lbnQpIHRoaXMub3B0aW9ucy5vbkNvbW1lbnQodHJ1ZSwgdGhpcy5pbnB1dC5zbGljZShzdGFydCArIDIsIGVuZCksIHN0YXJ0LCB0aGlzLnBvcywgc3RhcnRMb2MsIHRoaXMub3B0aW9ucy5sb2NhdGlvbnMgJiYgdGhpcy5jdXJQb3NpdGlvbigpKTtcbn07XG5cbnBwLnNraXBMaW5lQ29tbWVudCA9IGZ1bmN0aW9uIChzdGFydFNraXApIHtcbiAgdmFyIHN0YXJ0ID0gdGhpcy5wb3M7XG4gIHZhciBzdGFydExvYyA9IHRoaXMub3B0aW9ucy5vbkNvbW1lbnQgJiYgdGhpcy5vcHRpb25zLmxvY2F0aW9ucyAmJiB0aGlzLmN1clBvc2l0aW9uKCk7XG4gIHZhciBjaCA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArPSBzdGFydFNraXApO1xuICB3aGlsZSAodGhpcy5wb3MgPCB0aGlzLmlucHV0Lmxlbmd0aCAmJiBjaCAhPT0gMTAgJiYgY2ggIT09IDEzICYmIGNoICE9PSA4MjMyICYmIGNoICE9PSA4MjMzKSB7XG4gICAgKyt0aGlzLnBvcztcbiAgICBjaCA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyk7XG4gIH1cbiAgaWYgKHRoaXMub3B0aW9ucy5vbkNvbW1lbnQpIHRoaXMub3B0aW9ucy5vbkNvbW1lbnQoZmFsc2UsIHRoaXMuaW5wdXQuc2xpY2Uoc3RhcnQgKyBzdGFydFNraXAsIHRoaXMucG9zKSwgc3RhcnQsIHRoaXMucG9zLCBzdGFydExvYywgdGhpcy5vcHRpb25zLmxvY2F0aW9ucyAmJiB0aGlzLmN1clBvc2l0aW9uKCkpO1xufTtcblxuLy8gQ2FsbGVkIGF0IHRoZSBzdGFydCBvZiB0aGUgcGFyc2UgYW5kIGFmdGVyIGV2ZXJ5IHRva2VuLiBTa2lwc1xuLy8gd2hpdGVzcGFjZSBhbmQgY29tbWVudHMsIGFuZC5cblxucHAuc2tpcFNwYWNlID0gZnVuY3Rpb24gKCkge1xuICB3aGlsZSAodGhpcy5wb3MgPCB0aGlzLmlucHV0Lmxlbmd0aCkge1xuICAgIHZhciBjaCA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyk7XG4gICAgaWYgKGNoID09PSAzMikge1xuICAgICAgLy8gJyAnXG4gICAgICArK3RoaXMucG9zO1xuICAgIH0gZWxzZSBpZiAoY2ggPT09IDEzKSB7XG4gICAgICArK3RoaXMucG9zO1xuICAgICAgdmFyIG5leHQgPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MpO1xuICAgICAgaWYgKG5leHQgPT09IDEwKSB7XG4gICAgICAgICsrdGhpcy5wb3M7XG4gICAgICB9XG4gICAgICBpZiAodGhpcy5vcHRpb25zLmxvY2F0aW9ucykge1xuICAgICAgICArK3RoaXMuY3VyTGluZTtcbiAgICAgICAgdGhpcy5saW5lU3RhcnQgPSB0aGlzLnBvcztcbiAgICAgIH1cbiAgICB9IGVsc2UgaWYgKGNoID09PSAxMCB8fCBjaCA9PT0gODIzMiB8fCBjaCA9PT0gODIzMykge1xuICAgICAgKyt0aGlzLnBvcztcbiAgICAgIGlmICh0aGlzLm9wdGlvbnMubG9jYXRpb25zKSB7XG4gICAgICAgICsrdGhpcy5jdXJMaW5lO1xuICAgICAgICB0aGlzLmxpbmVTdGFydCA9IHRoaXMucG9zO1xuICAgICAgfVxuICAgIH0gZWxzZSBpZiAoY2ggPiA4ICYmIGNoIDwgMTQpIHtcbiAgICAgICsrdGhpcy5wb3M7XG4gICAgfSBlbHNlIGlmIChjaCA9PT0gNDcpIHtcbiAgICAgIC8vICcvJ1xuICAgICAgdmFyIG5leHQgPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAxKTtcbiAgICAgIGlmIChuZXh0ID09PSA0Mikge1xuICAgICAgICAvLyAnKidcbiAgICAgICAgdGhpcy5za2lwQmxvY2tDb21tZW50KCk7XG4gICAgICB9IGVsc2UgaWYgKG5leHQgPT09IDQ3KSB7XG4gICAgICAgIC8vICcvJ1xuICAgICAgICB0aGlzLnNraXBMaW5lQ29tbWVudCgyKTtcbiAgICAgIH0gZWxzZSBicmVhaztcbiAgICB9IGVsc2UgaWYgKGNoID09PSAxNjApIHtcbiAgICAgIC8vICdcXHhhMCdcbiAgICAgICsrdGhpcy5wb3M7XG4gICAgfSBlbHNlIGlmIChjaCA+PSA1NzYwICYmIG5vbkFTQ0lJd2hpdGVzcGFjZS50ZXN0KFN0cmluZy5mcm9tQ2hhckNvZGUoY2gpKSkge1xuICAgICAgKyt0aGlzLnBvcztcbiAgICB9IGVsc2Uge1xuICAgICAgYnJlYWs7XG4gICAgfVxuICB9XG59O1xuXG4vLyBDYWxsZWQgYXQgdGhlIGVuZCBvZiBldmVyeSB0b2tlbi4gU2V0cyBgZW5kYCwgYHZhbGAsIGFuZFxuLy8gbWFpbnRhaW5zIGBjb250ZXh0YCBhbmQgYGV4cHJBbGxvd2VkYCwgYW5kIHNraXBzIHRoZSBzcGFjZSBhZnRlclxuLy8gdGhlIHRva2VuLCBzbyB0aGF0IHRoZSBuZXh0IG9uZSdzIGBzdGFydGAgd2lsbCBwb2ludCBhdCB0aGVcbi8vIHJpZ2h0IHBvc2l0aW9uLlxuXG5wcC5maW5pc2hUb2tlbiA9IGZ1bmN0aW9uICh0eXBlLCB2YWwpIHtcbiAgdGhpcy5lbmQgPSB0aGlzLnBvcztcbiAgaWYgKHRoaXMub3B0aW9ucy5sb2NhdGlvbnMpIHRoaXMuZW5kTG9jID0gdGhpcy5jdXJQb3NpdGlvbigpO1xuICB2YXIgcHJldlR5cGUgPSB0aGlzLnR5cGU7XG4gIHRoaXMudHlwZSA9IHR5cGU7XG4gIHRoaXMudmFsdWUgPSB2YWw7XG5cbiAgdGhpcy51cGRhdGVDb250ZXh0KHByZXZUeXBlKTtcbn07XG5cbi8vICMjIyBUb2tlbiByZWFkaW5nXG5cbi8vIFRoaXMgaXMgdGhlIGZ1bmN0aW9uIHRoYXQgaXMgY2FsbGVkIHRvIGZldGNoIHRoZSBuZXh0IHRva2VuLiBJdFxuLy8gaXMgc29tZXdoYXQgb2JzY3VyZSwgYmVjYXVzZSBpdCB3b3JrcyBpbiBjaGFyYWN0ZXIgY29kZXMgcmF0aGVyXG4vLyB0aGFuIGNoYXJhY3RlcnMsIGFuZCBiZWNhdXNlIG9wZXJhdG9yIHBhcnNpbmcgaGFzIGJlZW4gaW5saW5lZFxuLy8gaW50byBpdC5cbi8vXG4vLyBBbGwgaW4gdGhlIG5hbWUgb2Ygc3BlZWQuXG4vL1xucHAucmVhZFRva2VuX2RvdCA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIG5leHQgPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAxKTtcbiAgaWYgKG5leHQgPj0gNDggJiYgbmV4dCA8PSA1NykgcmV0dXJuIHRoaXMucmVhZE51bWJlcih0cnVlKTtcbiAgdmFyIG5leHQyID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMik7XG4gIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNiAmJiBuZXh0ID09PSA0NiAmJiBuZXh0MiA9PT0gNDYpIHtcbiAgICAvLyA0NiA9IGRvdCAnLidcbiAgICB0aGlzLnBvcyArPSAzO1xuICAgIHJldHVybiB0aGlzLmZpbmlzaFRva2VuKHR0LmVsbGlwc2lzKTtcbiAgfSBlbHNlIHtcbiAgICArK3RoaXMucG9zO1xuICAgIHJldHVybiB0aGlzLmZpbmlzaFRva2VuKHR0LmRvdCk7XG4gIH1cbn07XG5cbnBwLnJlYWRUb2tlbl9zbGFzaCA9IGZ1bmN0aW9uICgpIHtcbiAgLy8gJy8nXG4gIHZhciBuZXh0ID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMSk7XG4gIGlmICh0aGlzLmV4cHJBbGxvd2VkKSB7XG4gICAgKyt0aGlzLnBvcztyZXR1cm4gdGhpcy5yZWFkUmVnZXhwKCk7XG4gIH1cbiAgaWYgKG5leHQgPT09IDYxKSByZXR1cm4gdGhpcy5maW5pc2hPcCh0dC5hc3NpZ24sIDIpO1xuICByZXR1cm4gdGhpcy5maW5pc2hPcCh0dC5zbGFzaCwgMSk7XG59O1xuXG5wcC5yZWFkVG9rZW5fbXVsdF9tb2R1bG8gPSBmdW5jdGlvbiAoY29kZSkge1xuICAvLyAnJSonXG4gIHZhciBuZXh0ID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMSk7XG4gIGlmIChuZXh0ID09PSA2MSkgcmV0dXJuIHRoaXMuZmluaXNoT3AodHQuYXNzaWduLCAyKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoT3AoY29kZSA9PT0gNDIgPyB0dC5zdGFyIDogdHQubW9kdWxvLCAxKTtcbn07XG5cbnBwLnJlYWRUb2tlbl9waXBlX2FtcCA9IGZ1bmN0aW9uIChjb2RlKSB7XG4gIC8vICd8JidcbiAgdmFyIG5leHQgPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAxKTtcbiAgaWYgKG5leHQgPT09IGNvZGUpIHJldHVybiB0aGlzLmZpbmlzaE9wKGNvZGUgPT09IDEyNCA/IHR0LmxvZ2ljYWxPUiA6IHR0LmxvZ2ljYWxBTkQsIDIpO1xuICBpZiAobmV4dCA9PT0gNjEpIHJldHVybiB0aGlzLmZpbmlzaE9wKHR0LmFzc2lnbiwgMik7XG4gIHJldHVybiB0aGlzLmZpbmlzaE9wKGNvZGUgPT09IDEyNCA/IHR0LmJpdHdpc2VPUiA6IHR0LmJpdHdpc2VBTkQsIDEpO1xufTtcblxucHAucmVhZFRva2VuX2NhcmV0ID0gZnVuY3Rpb24gKCkge1xuICAvLyAnXidcbiAgdmFyIG5leHQgPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAxKTtcbiAgaWYgKG5leHQgPT09IDYxKSByZXR1cm4gdGhpcy5maW5pc2hPcCh0dC5hc3NpZ24sIDIpO1xuICByZXR1cm4gdGhpcy5maW5pc2hPcCh0dC5iaXR3aXNlWE9SLCAxKTtcbn07XG5cbnBwLnJlYWRUb2tlbl9wbHVzX21pbiA9IGZ1bmN0aW9uIChjb2RlKSB7XG4gIC8vICcrLSdcbiAgdmFyIG5leHQgPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAxKTtcbiAgaWYgKG5leHQgPT09IGNvZGUpIHtcbiAgICBpZiAobmV4dCA9PSA0NSAmJiB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAyKSA9PSA2MiAmJiBsaW5lQnJlYWsudGVzdCh0aGlzLmlucHV0LnNsaWNlKHRoaXMubGFzdFRva0VuZCwgdGhpcy5wb3MpKSkge1xuICAgICAgLy8gQSBgLS0+YCBsaW5lIGNvbW1lbnRcbiAgICAgIHRoaXMuc2tpcExpbmVDb21tZW50KDMpO1xuICAgICAgdGhpcy5za2lwU3BhY2UoKTtcbiAgICAgIHJldHVybiB0aGlzLm5leHRUb2tlbigpO1xuICAgIH1cbiAgICByZXR1cm4gdGhpcy5maW5pc2hPcCh0dC5pbmNEZWMsIDIpO1xuICB9XG4gIGlmIChuZXh0ID09PSA2MSkgcmV0dXJuIHRoaXMuZmluaXNoT3AodHQuYXNzaWduLCAyKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoT3AodHQucGx1c01pbiwgMSk7XG59O1xuXG5wcC5yZWFkVG9rZW5fbHRfZ3QgPSBmdW5jdGlvbiAoY29kZSkge1xuICAvLyAnPD4nXG4gIHZhciBuZXh0ID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMSk7XG4gIHZhciBzaXplID0gMTtcbiAgaWYgKG5leHQgPT09IGNvZGUpIHtcbiAgICBzaXplID0gY29kZSA9PT0gNjIgJiYgdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMikgPT09IDYyID8gMyA6IDI7XG4gICAgaWYgKHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIHNpemUpID09PSA2MSkgcmV0dXJuIHRoaXMuZmluaXNoT3AodHQuYXNzaWduLCBzaXplICsgMSk7XG4gICAgcmV0dXJuIHRoaXMuZmluaXNoT3AodHQuYml0U2hpZnQsIHNpemUpO1xuICB9XG4gIGlmIChuZXh0ID09IDMzICYmIGNvZGUgPT0gNjAgJiYgdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMikgPT0gNDUgJiYgdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMykgPT0gNDUpIHtcbiAgICBpZiAodGhpcy5pbk1vZHVsZSkgdGhpcy51bmV4cGVjdGVkKCk7XG4gICAgLy8gYDwhLS1gLCBhbiBYTUwtc3R5bGUgY29tbWVudCB0aGF0IHNob3VsZCBiZSBpbnRlcnByZXRlZCBhcyBhIGxpbmUgY29tbWVudFxuICAgIHRoaXMuc2tpcExpbmVDb21tZW50KDQpO1xuICAgIHRoaXMuc2tpcFNwYWNlKCk7XG4gICAgcmV0dXJuIHRoaXMubmV4dFRva2VuKCk7XG4gIH1cbiAgaWYgKG5leHQgPT09IDYxKSBzaXplID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMikgPT09IDYxID8gMyA6IDI7XG4gIHJldHVybiB0aGlzLmZpbmlzaE9wKHR0LnJlbGF0aW9uYWwsIHNpemUpO1xufTtcblxucHAucmVhZFRva2VuX2VxX2V4Y2wgPSBmdW5jdGlvbiAoY29kZSkge1xuICAvLyAnPSEnXG4gIHZhciBuZXh0ID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMSk7XG4gIGlmIChuZXh0ID09PSA2MSkgcmV0dXJuIHRoaXMuZmluaXNoT3AodHQuZXF1YWxpdHksIHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIDIpID09PSA2MSA/IDMgOiAyKTtcbiAgaWYgKGNvZGUgPT09IDYxICYmIG5leHQgPT09IDYyICYmIHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KSB7XG4gICAgLy8gJz0+J1xuICAgIHRoaXMucG9zICs9IDI7XG4gICAgcmV0dXJuIHRoaXMuZmluaXNoVG9rZW4odHQuYXJyb3cpO1xuICB9XG4gIHJldHVybiB0aGlzLmZpbmlzaE9wKGNvZGUgPT09IDYxID8gdHQuZXEgOiB0dC5wcmVmaXgsIDEpO1xufTtcblxucHAuZ2V0VG9rZW5Gcm9tQ29kZSA9IGZ1bmN0aW9uIChjb2RlKSB7XG4gIHN3aXRjaCAoY29kZSkge1xuICAgIC8vIFRoZSBpbnRlcnByZXRhdGlvbiBvZiBhIGRvdCBkZXBlbmRzIG9uIHdoZXRoZXIgaXQgaXMgZm9sbG93ZWRcbiAgICAvLyBieSBhIGRpZ2l0IG9yIGFub3RoZXIgdHdvIGRvdHMuXG4gICAgY2FzZSA0NjpcbiAgICAgIC8vICcuJ1xuICAgICAgcmV0dXJuIHRoaXMucmVhZFRva2VuX2RvdCgpO1xuXG4gICAgLy8gUHVuY3R1YXRpb24gdG9rZW5zLlxuICAgIGNhc2UgNDA6XG4gICAgICArK3RoaXMucG9zO3JldHVybiB0aGlzLmZpbmlzaFRva2VuKHR0LnBhcmVuTCk7XG4gICAgY2FzZSA0MTpcbiAgICAgICsrdGhpcy5wb3M7cmV0dXJuIHRoaXMuZmluaXNoVG9rZW4odHQucGFyZW5SKTtcbiAgICBjYXNlIDU5OlxuICAgICAgKyt0aGlzLnBvcztyZXR1cm4gdGhpcy5maW5pc2hUb2tlbih0dC5zZW1pKTtcbiAgICBjYXNlIDQ0OlxuICAgICAgKyt0aGlzLnBvcztyZXR1cm4gdGhpcy5maW5pc2hUb2tlbih0dC5jb21tYSk7XG4gICAgY2FzZSA5MTpcbiAgICAgICsrdGhpcy5wb3M7cmV0dXJuIHRoaXMuZmluaXNoVG9rZW4odHQuYnJhY2tldEwpO1xuICAgIGNhc2UgOTM6XG4gICAgICArK3RoaXMucG9zO3JldHVybiB0aGlzLmZpbmlzaFRva2VuKHR0LmJyYWNrZXRSKTtcbiAgICBjYXNlIDEyMzpcbiAgICAgICsrdGhpcy5wb3M7cmV0dXJuIHRoaXMuZmluaXNoVG9rZW4odHQuYnJhY2VMKTtcbiAgICBjYXNlIDEyNTpcbiAgICAgICsrdGhpcy5wb3M7cmV0dXJuIHRoaXMuZmluaXNoVG9rZW4odHQuYnJhY2VSKTtcbiAgICBjYXNlIDU4OlxuICAgICAgKyt0aGlzLnBvcztyZXR1cm4gdGhpcy5maW5pc2hUb2tlbih0dC5jb2xvbik7XG4gICAgY2FzZSA2MzpcbiAgICAgICsrdGhpcy5wb3M7cmV0dXJuIHRoaXMuZmluaXNoVG9rZW4odHQucXVlc3Rpb24pO1xuXG4gICAgY2FzZSA5NjpcbiAgICAgIC8vICdgJ1xuICAgICAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA8IDYpIGJyZWFrO1xuICAgICAgKyt0aGlzLnBvcztcbiAgICAgIHJldHVybiB0aGlzLmZpbmlzaFRva2VuKHR0LmJhY2tRdW90ZSk7XG5cbiAgICBjYXNlIDQ4OlxuICAgICAgLy8gJzAnXG4gICAgICB2YXIgbmV4dCA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIDEpO1xuICAgICAgaWYgKG5leHQgPT09IDEyMCB8fCBuZXh0ID09PSA4OCkgcmV0dXJuIHRoaXMucmVhZFJhZGl4TnVtYmVyKDE2KTsgLy8gJzB4JywgJzBYJyAtIGhleCBudW1iZXJcbiAgICAgIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNikge1xuICAgICAgICBpZiAobmV4dCA9PT0gMTExIHx8IG5leHQgPT09IDc5KSByZXR1cm4gdGhpcy5yZWFkUmFkaXhOdW1iZXIoOCk7IC8vICcwbycsICcwTycgLSBvY3RhbCBudW1iZXJcbiAgICAgICAgaWYgKG5leHQgPT09IDk4IHx8IG5leHQgPT09IDY2KSByZXR1cm4gdGhpcy5yZWFkUmFkaXhOdW1iZXIoMik7IC8vICcwYicsICcwQicgLSBiaW5hcnkgbnVtYmVyXG4gICAgICB9XG4gICAgLy8gQW55dGhpbmcgZWxzZSBiZWdpbm5pbmcgd2l0aCBhIGRpZ2l0IGlzIGFuIGludGVnZXIsIG9jdGFsXG4gICAgLy8gbnVtYmVyLCBvciBmbG9hdC5cbiAgICBjYXNlIDQ5OmNhc2UgNTA6Y2FzZSA1MTpjYXNlIDUyOmNhc2UgNTM6Y2FzZSA1NDpjYXNlIDU1OmNhc2UgNTY6Y2FzZSA1NzpcbiAgICAgIC8vIDEtOVxuICAgICAgcmV0dXJuIHRoaXMucmVhZE51bWJlcihmYWxzZSk7XG5cbiAgICAvLyBRdW90ZXMgcHJvZHVjZSBzdHJpbmdzLlxuICAgIGNhc2UgMzQ6Y2FzZSAzOTpcbiAgICAgIC8vICdcIicsIFwiJ1wiXG4gICAgICByZXR1cm4gdGhpcy5yZWFkU3RyaW5nKGNvZGUpO1xuXG4gICAgLy8gT3BlcmF0b3JzIGFyZSBwYXJzZWQgaW5saW5lIGluIHRpbnkgc3RhdGUgbWFjaGluZXMuICc9JyAoNjEpIGlzXG4gICAgLy8gb2Z0ZW4gcmVmZXJyZWQgdG8uIGBmaW5pc2hPcGAgc2ltcGx5IHNraXBzIHRoZSBhbW91bnQgb2ZcbiAgICAvLyBjaGFyYWN0ZXJzIGl0IGlzIGdpdmVuIGFzIHNlY29uZCBhcmd1bWVudCwgYW5kIHJldHVybnMgYSB0b2tlblxuICAgIC8vIG9mIHRoZSB0eXBlIGdpdmVuIGJ5IGl0cyBmaXJzdCBhcmd1bWVudC5cblxuICAgIGNhc2UgNDc6XG4gICAgICAvLyAnLydcbiAgICAgIHJldHVybiB0aGlzLnJlYWRUb2tlbl9zbGFzaCgpO1xuXG4gICAgY2FzZSAzNzpjYXNlIDQyOlxuICAgICAgLy8gJyUqJ1xuICAgICAgcmV0dXJuIHRoaXMucmVhZFRva2VuX211bHRfbW9kdWxvKGNvZGUpO1xuXG4gICAgY2FzZSAxMjQ6Y2FzZSAzODpcbiAgICAgIC8vICd8JidcbiAgICAgIHJldHVybiB0aGlzLnJlYWRUb2tlbl9waXBlX2FtcChjb2RlKTtcblxuICAgIGNhc2UgOTQ6XG4gICAgICAvLyAnXidcbiAgICAgIHJldHVybiB0aGlzLnJlYWRUb2tlbl9jYXJldCgpO1xuXG4gICAgY2FzZSA0MzpjYXNlIDQ1OlxuICAgICAgLy8gJystJ1xuICAgICAgcmV0dXJuIHRoaXMucmVhZFRva2VuX3BsdXNfbWluKGNvZGUpO1xuXG4gICAgY2FzZSA2MDpjYXNlIDYyOlxuICAgICAgLy8gJzw+J1xuICAgICAgcmV0dXJuIHRoaXMucmVhZFRva2VuX2x0X2d0KGNvZGUpO1xuXG4gICAgY2FzZSA2MTpjYXNlIDMzOlxuICAgICAgLy8gJz0hJ1xuICAgICAgcmV0dXJuIHRoaXMucmVhZFRva2VuX2VxX2V4Y2woY29kZSk7XG5cbiAgICBjYXNlIDEyNjpcbiAgICAgIC8vICd+J1xuICAgICAgcmV0dXJuIHRoaXMuZmluaXNoT3AodHQucHJlZml4LCAxKTtcbiAgfVxuXG4gIHRoaXMucmFpc2UodGhpcy5wb3MsIFwiVW5leHBlY3RlZCBjaGFyYWN0ZXIgJ1wiICsgY29kZVBvaW50VG9TdHJpbmcoY29kZSkgKyBcIidcIik7XG59O1xuXG5wcC5maW5pc2hPcCA9IGZ1bmN0aW9uICh0eXBlLCBzaXplKSB7XG4gIHZhciBzdHIgPSB0aGlzLmlucHV0LnNsaWNlKHRoaXMucG9zLCB0aGlzLnBvcyArIHNpemUpO1xuICB0aGlzLnBvcyArPSBzaXplO1xuICByZXR1cm4gdGhpcy5maW5pc2hUb2tlbih0eXBlLCBzdHIpO1xufTtcblxudmFyIHJlZ2V4cFVuaWNvZGVTdXBwb3J0ID0gZmFsc2U7XG50cnkge1xuICBuZXcgUmVnRXhwKFwi77+/XCIsIFwidVwiKTtyZWdleHBVbmljb2RlU3VwcG9ydCA9IHRydWU7XG59IGNhdGNoIChlKSB7fVxuXG4vLyBQYXJzZSBhIHJlZ3VsYXIgZXhwcmVzc2lvbi4gU29tZSBjb250ZXh0LWF3YXJlbmVzcyBpcyBuZWNlc3NhcnksXG4vLyBzaW5jZSBhICcvJyBpbnNpZGUgYSAnW10nIHNldCBkb2VzIG5vdCBlbmQgdGhlIGV4cHJlc3Npb24uXG5cbnBwLnJlYWRSZWdleHAgPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBlc2NhcGVkID0gdW5kZWZpbmVkLFxuICAgICAgaW5DbGFzcyA9IHVuZGVmaW5lZCxcbiAgICAgIHN0YXJ0ID0gdGhpcy5wb3M7XG4gIGZvciAoOzspIHtcbiAgICBpZiAodGhpcy5wb3MgPj0gdGhpcy5pbnB1dC5sZW5ndGgpIHRoaXMucmFpc2Uoc3RhcnQsIFwiVW50ZXJtaW5hdGVkIHJlZ3VsYXIgZXhwcmVzc2lvblwiKTtcbiAgICB2YXIgY2ggPSB0aGlzLmlucHV0LmNoYXJBdCh0aGlzLnBvcyk7XG4gICAgaWYgKGxpbmVCcmVhay50ZXN0KGNoKSkgdGhpcy5yYWlzZShzdGFydCwgXCJVbnRlcm1pbmF0ZWQgcmVndWxhciBleHByZXNzaW9uXCIpO1xuICAgIGlmICghZXNjYXBlZCkge1xuICAgICAgaWYgKGNoID09PSBcIltcIikgaW5DbGFzcyA9IHRydWU7ZWxzZSBpZiAoY2ggPT09IFwiXVwiICYmIGluQ2xhc3MpIGluQ2xhc3MgPSBmYWxzZTtlbHNlIGlmIChjaCA9PT0gXCIvXCIgJiYgIWluQ2xhc3MpIGJyZWFrO1xuICAgICAgZXNjYXBlZCA9IGNoID09PSBcIlxcXFxcIjtcbiAgICB9IGVsc2UgZXNjYXBlZCA9IGZhbHNlO1xuICAgICsrdGhpcy5wb3M7XG4gIH1cbiAgdmFyIGNvbnRlbnQgPSB0aGlzLmlucHV0LnNsaWNlKHN0YXJ0LCB0aGlzLnBvcyk7XG4gICsrdGhpcy5wb3M7XG4gIC8vIE5lZWQgdG8gdXNlIGByZWFkV29yZDFgIGJlY2F1c2UgJ1xcdVhYWFgnIHNlcXVlbmNlcyBhcmUgYWxsb3dlZFxuICAvLyBoZXJlIChkb24ndCBhc2spLlxuICB2YXIgbW9kcyA9IHRoaXMucmVhZFdvcmQxKCk7XG4gIHZhciB0bXAgPSBjb250ZW50O1xuICBpZiAobW9kcykge1xuICAgIHZhciB2YWxpZEZsYWdzID0gL15bZ21zaXldKiQvO1xuICAgIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNikgdmFsaWRGbGFncyA9IC9eW2dtc2l5dV0qJC87XG4gICAgaWYgKCF2YWxpZEZsYWdzLnRlc3QobW9kcykpIHRoaXMucmFpc2Uoc3RhcnQsIFwiSW52YWxpZCByZWd1bGFyIGV4cHJlc3Npb24gZmxhZ1wiKTtcbiAgICBpZiAobW9kcy5pbmRleE9mKFwidVwiKSA+PSAwICYmICFyZWdleHBVbmljb2RlU3VwcG9ydCkge1xuICAgICAgLy8gUmVwbGFjZSBlYWNoIGFzdHJhbCBzeW1ib2wgYW5kIGV2ZXJ5IFVuaWNvZGUgZXNjYXBlIHNlcXVlbmNlIHRoYXRcbiAgICAgIC8vIHBvc3NpYmx5IHJlcHJlc2VudHMgYW4gYXN0cmFsIHN5bWJvbCBvciBhIHBhaXJlZCBzdXJyb2dhdGUgd2l0aCBhXG4gICAgICAvLyBzaW5nbGUgQVNDSUkgc3ltYm9sIHRvIGF2b2lkIHRocm93aW5nIG9uIHJlZ3VsYXIgZXhwcmVzc2lvbnMgdGhhdFxuICAgICAgLy8gYXJlIG9ubHkgdmFsaWQgaW4gY29tYmluYXRpb24gd2l0aCB0aGUgYC91YCBmbGFnLlxuICAgICAgLy8gTm90ZTogcmVwbGFjaW5nIHdpdGggdGhlIEFTQ0lJIHN5bWJvbCBgeGAgbWlnaHQgY2F1c2UgZmFsc2VcbiAgICAgIC8vIG5lZ2F0aXZlcyBpbiB1bmxpa2VseSBzY2VuYXJpb3MuIEZvciBleGFtcGxlLCBgW1xcdXs2MX0tYl1gIGlzIGFcbiAgICAgIC8vIHBlcmZlY3RseSB2YWxpZCBwYXR0ZXJuIHRoYXQgaXMgZXF1aXZhbGVudCB0byBgW2EtYl1gLCBidXQgaXQgd291bGRcbiAgICAgIC8vIGJlIHJlcGxhY2VkIGJ5IGBbeC1iXWAgd2hpY2ggdGhyb3dzIGFuIGVycm9yLlxuICAgICAgdG1wID0gdG1wLnJlcGxhY2UoL1xcXFx1KFthLWZBLUYwLTldezR9KXxcXFxcdVxceyhbMC05YS1mQS1GXSspXFx9fFtcXHVEODAwLVxcdURCRkZdW1xcdURDMDAtXFx1REZGRl0vZywgXCJ4XCIpO1xuICAgIH1cbiAgfVxuICAvLyBEZXRlY3QgaW52YWxpZCByZWd1bGFyIGV4cHJlc3Npb25zLlxuICB2YXIgdmFsdWUgPSBudWxsO1xuICAvLyBSaGlubydzIHJlZ3VsYXIgZXhwcmVzc2lvbiBwYXJzZXIgaXMgZmxha3kgYW5kIHRocm93cyB1bmNhdGNoYWJsZSBleGNlcHRpb25zLFxuICAvLyBzbyBkb24ndCBkbyBkZXRlY3Rpb24gaWYgd2UgYXJlIHJ1bm5pbmcgdW5kZXIgUmhpbm9cbiAgaWYgKCFpc1JoaW5vKSB7XG4gICAgdHJ5IHtcbiAgICAgIG5ldyBSZWdFeHAodG1wKTtcbiAgICB9IGNhdGNoIChlKSB7XG4gICAgICBpZiAoZSBpbnN0YW5jZW9mIFN5bnRheEVycm9yKSB0aGlzLnJhaXNlKHN0YXJ0LCBcIkVycm9yIHBhcnNpbmcgcmVndWxhciBleHByZXNzaW9uOiBcIiArIGUubWVzc2FnZSk7XG4gICAgICB0aGlzLnJhaXNlKGUpO1xuICAgIH1cbiAgICAvLyBHZXQgYSByZWd1bGFyIGV4cHJlc3Npb24gb2JqZWN0IGZvciB0aGlzIHBhdHRlcm4tZmxhZyBwYWlyLCBvciBgbnVsbGAgaW5cbiAgICAvLyBjYXNlIHRoZSBjdXJyZW50IGVudmlyb25tZW50IGRvZXNuJ3Qgc3VwcG9ydCB0aGUgZmxhZ3MgaXQgdXNlcy5cbiAgICB0cnkge1xuICAgICAgdmFsdWUgPSBuZXcgUmVnRXhwKGNvbnRlbnQsIG1vZHMpO1xuICAgIH0gY2F0Y2ggKGVycikge31cbiAgfVxuICByZXR1cm4gdGhpcy5maW5pc2hUb2tlbih0dC5yZWdleHAsIHsgcGF0dGVybjogY29udGVudCwgZmxhZ3M6IG1vZHMsIHZhbHVlOiB2YWx1ZSB9KTtcbn07XG5cbi8vIFJlYWQgYW4gaW50ZWdlciBpbiB0aGUgZ2l2ZW4gcmFkaXguIFJldHVybiBudWxsIGlmIHplcm8gZGlnaXRzXG4vLyB3ZXJlIHJlYWQsIHRoZSBpbnRlZ2VyIHZhbHVlIG90aGVyd2lzZS4gV2hlbiBgbGVuYCBpcyBnaXZlbiwgdGhpc1xuLy8gd2lsbCByZXR1cm4gYG51bGxgIHVubGVzcyB0aGUgaW50ZWdlciBoYXMgZXhhY3RseSBgbGVuYCBkaWdpdHMuXG5cbnBwLnJlYWRJbnQgPSBmdW5jdGlvbiAocmFkaXgsIGxlbikge1xuICB2YXIgc3RhcnQgPSB0aGlzLnBvcyxcbiAgICAgIHRvdGFsID0gMDtcbiAgZm9yICh2YXIgaSA9IDAsIGUgPSBsZW4gPT0gbnVsbCA/IEluZmluaXR5IDogbGVuOyBpIDwgZTsgKytpKSB7XG4gICAgdmFyIGNvZGUgPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MpLFxuICAgICAgICB2YWwgPSB1bmRlZmluZWQ7XG4gICAgaWYgKGNvZGUgPj0gOTcpIHZhbCA9IGNvZGUgLSA5NyArIDEwOyAvLyBhXG4gICAgZWxzZSBpZiAoY29kZSA+PSA2NSkgdmFsID0gY29kZSAtIDY1ICsgMTA7IC8vIEFcbiAgICBlbHNlIGlmIChjb2RlID49IDQ4ICYmIGNvZGUgPD0gNTcpIHZhbCA9IGNvZGUgLSA0ODsgLy8gMC05XG4gICAgZWxzZSB2YWwgPSBJbmZpbml0eTtcbiAgICBpZiAodmFsID49IHJhZGl4KSBicmVhaztcbiAgICArK3RoaXMucG9zO1xuICAgIHRvdGFsID0gdG90YWwgKiByYWRpeCArIHZhbDtcbiAgfVxuICBpZiAodGhpcy5wb3MgPT09IHN0YXJ0IHx8IGxlbiAhPSBudWxsICYmIHRoaXMucG9zIC0gc3RhcnQgIT09IGxlbikgcmV0dXJuIG51bGw7XG5cbiAgcmV0dXJuIHRvdGFsO1xufTtcblxucHAucmVhZFJhZGl4TnVtYmVyID0gZnVuY3Rpb24gKHJhZGl4KSB7XG4gIHRoaXMucG9zICs9IDI7IC8vIDB4XG4gIHZhciB2YWwgPSB0aGlzLnJlYWRJbnQocmFkaXgpO1xuICBpZiAodmFsID09IG51bGwpIHRoaXMucmFpc2UodGhpcy5zdGFydCArIDIsIFwiRXhwZWN0ZWQgbnVtYmVyIGluIHJhZGl4IFwiICsgcmFkaXgpO1xuICBpZiAoaXNJZGVudGlmaWVyU3RhcnQodGhpcy5mdWxsQ2hhckNvZGVBdFBvcygpKSkgdGhpcy5yYWlzZSh0aGlzLnBvcywgXCJJZGVudGlmaWVyIGRpcmVjdGx5IGFmdGVyIG51bWJlclwiKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoVG9rZW4odHQubnVtLCB2YWwpO1xufTtcblxuLy8gUmVhZCBhbiBpbnRlZ2VyLCBvY3RhbCBpbnRlZ2VyLCBvciBmbG9hdGluZy1wb2ludCBudW1iZXIuXG5cbnBwLnJlYWROdW1iZXIgPSBmdW5jdGlvbiAoc3RhcnRzV2l0aERvdCkge1xuICB2YXIgc3RhcnQgPSB0aGlzLnBvcyxcbiAgICAgIGlzRmxvYXQgPSBmYWxzZSxcbiAgICAgIG9jdGFsID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zKSA9PT0gNDg7XG4gIGlmICghc3RhcnRzV2l0aERvdCAmJiB0aGlzLnJlYWRJbnQoMTApID09PSBudWxsKSB0aGlzLnJhaXNlKHN0YXJ0LCBcIkludmFsaWQgbnVtYmVyXCIpO1xuICBpZiAodGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zKSA9PT0gNDYpIHtcbiAgICArK3RoaXMucG9zO1xuICAgIHRoaXMucmVhZEludCgxMCk7XG4gICAgaXNGbG9hdCA9IHRydWU7XG4gIH1cbiAgdmFyIG5leHQgPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MpO1xuICBpZiAobmV4dCA9PT0gNjkgfHwgbmV4dCA9PT0gMTAxKSB7XG4gICAgLy8gJ2VFJ1xuICAgIG5leHQgPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQoKyt0aGlzLnBvcyk7XG4gICAgaWYgKG5leHQgPT09IDQzIHx8IG5leHQgPT09IDQ1KSArK3RoaXMucG9zOyAvLyAnKy0nXG4gICAgaWYgKHRoaXMucmVhZEludCgxMCkgPT09IG51bGwpIHRoaXMucmFpc2Uoc3RhcnQsIFwiSW52YWxpZCBudW1iZXJcIik7XG4gICAgaXNGbG9hdCA9IHRydWU7XG4gIH1cbiAgaWYgKGlzSWRlbnRpZmllclN0YXJ0KHRoaXMuZnVsbENoYXJDb2RlQXRQb3MoKSkpIHRoaXMucmFpc2UodGhpcy5wb3MsIFwiSWRlbnRpZmllciBkaXJlY3RseSBhZnRlciBudW1iZXJcIik7XG5cbiAgdmFyIHN0ciA9IHRoaXMuaW5wdXQuc2xpY2Uoc3RhcnQsIHRoaXMucG9zKSxcbiAgICAgIHZhbCA9IHVuZGVmaW5lZDtcbiAgaWYgKGlzRmxvYXQpIHZhbCA9IHBhcnNlRmxvYXQoc3RyKTtlbHNlIGlmICghb2N0YWwgfHwgc3RyLmxlbmd0aCA9PT0gMSkgdmFsID0gcGFyc2VJbnQoc3RyLCAxMCk7ZWxzZSBpZiAoL1s4OV0vLnRlc3Qoc3RyKSB8fCB0aGlzLnN0cmljdCkgdGhpcy5yYWlzZShzdGFydCwgXCJJbnZhbGlkIG51bWJlclwiKTtlbHNlIHZhbCA9IHBhcnNlSW50KHN0ciwgOCk7XG4gIHJldHVybiB0aGlzLmZpbmlzaFRva2VuKHR0Lm51bSwgdmFsKTtcbn07XG5cbi8vIFJlYWQgYSBzdHJpbmcgdmFsdWUsIGludGVycHJldGluZyBiYWNrc2xhc2gtZXNjYXBlcy5cblxucHAucmVhZENvZGVQb2ludCA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIGNoID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zKSxcbiAgICAgIGNvZGUgPSB1bmRlZmluZWQ7XG5cbiAgaWYgKGNoID09PSAxMjMpIHtcbiAgICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uIDwgNikgdGhpcy51bmV4cGVjdGVkKCk7XG4gICAgKyt0aGlzLnBvcztcbiAgICBjb2RlID0gdGhpcy5yZWFkSGV4Q2hhcih0aGlzLmlucHV0LmluZGV4T2YoXCJ9XCIsIHRoaXMucG9zKSAtIHRoaXMucG9zKTtcbiAgICArK3RoaXMucG9zO1xuICAgIGlmIChjb2RlID4gMTExNDExMSkgdGhpcy51bmV4cGVjdGVkKCk7XG4gIH0gZWxzZSB7XG4gICAgY29kZSA9IHRoaXMucmVhZEhleENoYXIoNCk7XG4gIH1cbiAgcmV0dXJuIGNvZGU7XG59O1xuXG5mdW5jdGlvbiBjb2RlUG9pbnRUb1N0cmluZyhjb2RlKSB7XG4gIC8vIFVURi0xNiBEZWNvZGluZ1xuICBpZiAoY29kZSA8PSA2NTUzNSkge1xuICAgIHJldHVybiBTdHJpbmcuZnJvbUNoYXJDb2RlKGNvZGUpO1xuICB9cmV0dXJuIFN0cmluZy5mcm9tQ2hhckNvZGUoKGNvZGUgLSA2NTUzNiA+PiAxMCkgKyA1NTI5NiwgKGNvZGUgLSA2NTUzNiAmIDEwMjMpICsgNTYzMjApO1xufVxuXG5wcC5yZWFkU3RyaW5nID0gZnVuY3Rpb24gKHF1b3RlKSB7XG4gIHZhciBvdXQgPSBcIlwiLFxuICAgICAgY2h1bmtTdGFydCA9ICsrdGhpcy5wb3M7XG4gIGZvciAoOzspIHtcbiAgICBpZiAodGhpcy5wb3MgPj0gdGhpcy5pbnB1dC5sZW5ndGgpIHRoaXMucmFpc2UodGhpcy5zdGFydCwgXCJVbnRlcm1pbmF0ZWQgc3RyaW5nIGNvbnN0YW50XCIpO1xuICAgIHZhciBjaCA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyk7XG4gICAgaWYgKGNoID09PSBxdW90ZSkgYnJlYWs7XG4gICAgaWYgKGNoID09PSA5Mikge1xuICAgICAgLy8gJ1xcJ1xuICAgICAgb3V0ICs9IHRoaXMuaW5wdXQuc2xpY2UoY2h1bmtTdGFydCwgdGhpcy5wb3MpO1xuICAgICAgb3V0ICs9IHRoaXMucmVhZEVzY2FwZWRDaGFyKCk7XG4gICAgICBjaHVua1N0YXJ0ID0gdGhpcy5wb3M7XG4gICAgfSBlbHNlIHtcbiAgICAgIGlmIChpc05ld0xpbmUoY2gpKSB0aGlzLnJhaXNlKHRoaXMuc3RhcnQsIFwiVW50ZXJtaW5hdGVkIHN0cmluZyBjb25zdGFudFwiKTtcbiAgICAgICsrdGhpcy5wb3M7XG4gICAgfVxuICB9XG4gIG91dCArPSB0aGlzLmlucHV0LnNsaWNlKGNodW5rU3RhcnQsIHRoaXMucG9zKyspO1xuICByZXR1cm4gdGhpcy5maW5pc2hUb2tlbih0dC5zdHJpbmcsIG91dCk7XG59O1xuXG4vLyBSZWFkcyB0ZW1wbGF0ZSBzdHJpbmcgdG9rZW5zLlxuXG5wcC5yZWFkVG1wbFRva2VuID0gZnVuY3Rpb24gKCkge1xuICB2YXIgb3V0ID0gXCJcIixcbiAgICAgIGNodW5rU3RhcnQgPSB0aGlzLnBvcztcbiAgZm9yICg7Oykge1xuICAgIGlmICh0aGlzLnBvcyA+PSB0aGlzLmlucHV0Lmxlbmd0aCkgdGhpcy5yYWlzZSh0aGlzLnN0YXJ0LCBcIlVudGVybWluYXRlZCB0ZW1wbGF0ZVwiKTtcbiAgICB2YXIgY2ggPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MpO1xuICAgIGlmIChjaCA9PT0gOTYgfHwgY2ggPT09IDM2ICYmIHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIDEpID09PSAxMjMpIHtcbiAgICAgIC8vICdgJywgJyR7J1xuICAgICAgaWYgKHRoaXMucG9zID09PSB0aGlzLnN0YXJ0ICYmIHRoaXMudHlwZSA9PT0gdHQudGVtcGxhdGUpIHtcbiAgICAgICAgaWYgKGNoID09PSAzNikge1xuICAgICAgICAgIHRoaXMucG9zICs9IDI7XG4gICAgICAgICAgcmV0dXJuIHRoaXMuZmluaXNoVG9rZW4odHQuZG9sbGFyQnJhY2VMKTtcbiAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICArK3RoaXMucG9zO1xuICAgICAgICAgIHJldHVybiB0aGlzLmZpbmlzaFRva2VuKHR0LmJhY2tRdW90ZSk7XG4gICAgICAgIH1cbiAgICAgIH1cbiAgICAgIG91dCArPSB0aGlzLmlucHV0LnNsaWNlKGNodW5rU3RhcnQsIHRoaXMucG9zKTtcbiAgICAgIHJldHVybiB0aGlzLmZpbmlzaFRva2VuKHR0LnRlbXBsYXRlLCBvdXQpO1xuICAgIH1cbiAgICBpZiAoY2ggPT09IDkyKSB7XG4gICAgICAvLyAnXFwnXG4gICAgICBvdXQgKz0gdGhpcy5pbnB1dC5zbGljZShjaHVua1N0YXJ0LCB0aGlzLnBvcyk7XG4gICAgICBvdXQgKz0gdGhpcy5yZWFkRXNjYXBlZENoYXIoKTtcbiAgICAgIGNodW5rU3RhcnQgPSB0aGlzLnBvcztcbiAgICB9IGVsc2UgaWYgKGlzTmV3TGluZShjaCkpIHtcbiAgICAgIG91dCArPSB0aGlzLmlucHV0LnNsaWNlKGNodW5rU3RhcnQsIHRoaXMucG9zKTtcbiAgICAgICsrdGhpcy5wb3M7XG4gICAgICBpZiAoY2ggPT09IDEzICYmIHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcykgPT09IDEwKSB7XG4gICAgICAgICsrdGhpcy5wb3M7XG4gICAgICAgIG91dCArPSBcIlxcblwiO1xuICAgICAgfSBlbHNlIHtcbiAgICAgICAgb3V0ICs9IFN0cmluZy5mcm9tQ2hhckNvZGUoY2gpO1xuICAgICAgfVxuICAgICAgaWYgKHRoaXMub3B0aW9ucy5sb2NhdGlvbnMpIHtcbiAgICAgICAgKyt0aGlzLmN1ckxpbmU7XG4gICAgICAgIHRoaXMubGluZVN0YXJ0ID0gdGhpcy5wb3M7XG4gICAgICB9XG4gICAgICBjaHVua1N0YXJ0ID0gdGhpcy5wb3M7XG4gICAgfSBlbHNlIHtcbiAgICAgICsrdGhpcy5wb3M7XG4gICAgfVxuICB9XG59O1xuXG4vLyBVc2VkIHRvIHJlYWQgZXNjYXBlZCBjaGFyYWN0ZXJzXG5cbnBwLnJlYWRFc2NhcGVkQ2hhciA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIGNoID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KCsrdGhpcy5wb3MpO1xuICB2YXIgb2N0YWwgPSAvXlswLTddKy8uZXhlYyh0aGlzLmlucHV0LnNsaWNlKHRoaXMucG9zLCB0aGlzLnBvcyArIDMpKTtcbiAgaWYgKG9jdGFsKSBvY3RhbCA9IG9jdGFsWzBdO1xuICB3aGlsZSAob2N0YWwgJiYgcGFyc2VJbnQob2N0YWwsIDgpID4gMjU1KSBvY3RhbCA9IG9jdGFsLnNsaWNlKDAsIC0xKTtcbiAgaWYgKG9jdGFsID09PSBcIjBcIikgb2N0YWwgPSBudWxsO1xuICArK3RoaXMucG9zO1xuICBpZiAob2N0YWwpIHtcbiAgICBpZiAodGhpcy5zdHJpY3QpIHRoaXMucmFpc2UodGhpcy5wb3MgLSAyLCBcIk9jdGFsIGxpdGVyYWwgaW4gc3RyaWN0IG1vZGVcIik7XG4gICAgdGhpcy5wb3MgKz0gb2N0YWwubGVuZ3RoIC0gMTtcbiAgICByZXR1cm4gU3RyaW5nLmZyb21DaGFyQ29kZShwYXJzZUludChvY3RhbCwgOCkpO1xuICB9IGVsc2Uge1xuICAgIHN3aXRjaCAoY2gpIHtcbiAgICAgIGNhc2UgMTEwOlxuICAgICAgICByZXR1cm4gXCJcXG5cIjsgLy8gJ24nIC0+ICdcXG4nXG4gICAgICBjYXNlIDExNDpcbiAgICAgICAgcmV0dXJuIFwiXFxyXCI7IC8vICdyJyAtPiAnXFxyJ1xuICAgICAgY2FzZSAxMjA6XG4gICAgICAgIHJldHVybiBTdHJpbmcuZnJvbUNoYXJDb2RlKHRoaXMucmVhZEhleENoYXIoMikpOyAvLyAneCdcbiAgICAgIGNhc2UgMTE3OlxuICAgICAgICByZXR1cm4gY29kZVBvaW50VG9TdHJpbmcodGhpcy5yZWFkQ29kZVBvaW50KCkpOyAvLyAndSdcbiAgICAgIGNhc2UgMTE2OlxuICAgICAgICByZXR1cm4gXCJcXHRcIjsgLy8gJ3QnIC0+ICdcXHQnXG4gICAgICBjYXNlIDk4OlxuICAgICAgICByZXR1cm4gXCJcXGJcIjsgLy8gJ2InIC0+ICdcXGInXG4gICAgICBjYXNlIDExODpcbiAgICAgICAgcmV0dXJuIFwiXFx1MDAwYlwiOyAvLyAndicgLT4gJ1xcdTAwMGInXG4gICAgICBjYXNlIDEwMjpcbiAgICAgICAgcmV0dXJuIFwiXFxmXCI7IC8vICdmJyAtPiAnXFxmJ1xuICAgICAgY2FzZSA0ODpcbiAgICAgICAgcmV0dXJuIFwiXFx1MDAwMFwiOyAvLyAwIC0+ICdcXDAnXG4gICAgICBjYXNlIDEzOlxuICAgICAgICBpZiAodGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zKSA9PT0gMTApICsrdGhpcy5wb3M7IC8vICdcXHJcXG4nXG4gICAgICBjYXNlIDEwOlxuICAgICAgICAvLyAnIFxcbidcbiAgICAgICAgaWYgKHRoaXMub3B0aW9ucy5sb2NhdGlvbnMpIHtcbiAgICAgICAgICB0aGlzLmxpbmVTdGFydCA9IHRoaXMucG9zOysrdGhpcy5jdXJMaW5lO1xuICAgICAgICB9XG4gICAgICAgIHJldHVybiBcIlwiO1xuICAgICAgZGVmYXVsdDpcbiAgICAgICAgcmV0dXJuIFN0cmluZy5mcm9tQ2hhckNvZGUoY2gpO1xuICAgIH1cbiAgfVxufTtcblxuLy8gVXNlZCB0byByZWFkIGNoYXJhY3RlciBlc2NhcGUgc2VxdWVuY2VzICgnXFx4JywgJ1xcdScsICdcXFUnKS5cblxucHAucmVhZEhleENoYXIgPSBmdW5jdGlvbiAobGVuKSB7XG4gIHZhciBuID0gdGhpcy5yZWFkSW50KDE2LCBsZW4pO1xuICBpZiAobiA9PT0gbnVsbCkgdGhpcy5yYWlzZSh0aGlzLnN0YXJ0LCBcIkJhZCBjaGFyYWN0ZXIgZXNjYXBlIHNlcXVlbmNlXCIpO1xuICByZXR1cm4gbjtcbn07XG5cbi8vIFVzZWQgdG8gc2lnbmFsIHRvIGNhbGxlcnMgb2YgYHJlYWRXb3JkMWAgd2hldGhlciB0aGUgd29yZFxuLy8gY29udGFpbmVkIGFueSBlc2NhcGUgc2VxdWVuY2VzLiBUaGlzIGlzIG5lZWRlZCBiZWNhdXNlIHdvcmRzIHdpdGhcbi8vIGVzY2FwZSBzZXF1ZW5jZXMgbXVzdCBub3QgYmUgaW50ZXJwcmV0ZWQgYXMga2V5d29yZHMuXG5cbnZhciBjb250YWluc0VzYztcblxuLy8gUmVhZCBhbiBpZGVudGlmaWVyLCBhbmQgcmV0dXJuIGl0IGFzIGEgc3RyaW5nLiBTZXRzIGBjb250YWluc0VzY2Bcbi8vIHRvIHdoZXRoZXIgdGhlIHdvcmQgY29udGFpbmVkIGEgJ1xcdScgZXNjYXBlLlxuLy9cbi8vIEluY3JlbWVudGFsbHkgYWRkcyBvbmx5IGVzY2FwZWQgY2hhcnMsIGFkZGluZyBvdGhlciBjaHVua3MgYXMtaXNcbi8vIGFzIGEgbWljcm8tb3B0aW1pemF0aW9uLlxuXG5wcC5yZWFkV29yZDEgPSBmdW5jdGlvbiAoKSB7XG4gIGNvbnRhaW5zRXNjID0gZmFsc2U7XG4gIHZhciB3b3JkID0gXCJcIixcbiAgICAgIGZpcnN0ID0gdHJ1ZSxcbiAgICAgIGNodW5rU3RhcnQgPSB0aGlzLnBvcztcbiAgdmFyIGFzdHJhbCA9IHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2O1xuICB3aGlsZSAodGhpcy5wb3MgPCB0aGlzLmlucHV0Lmxlbmd0aCkge1xuICAgIHZhciBjaCA9IHRoaXMuZnVsbENoYXJDb2RlQXRQb3MoKTtcbiAgICBpZiAoaXNJZGVudGlmaWVyQ2hhcihjaCwgYXN0cmFsKSkge1xuICAgICAgdGhpcy5wb3MgKz0gY2ggPD0gNjU1MzUgPyAxIDogMjtcbiAgICB9IGVsc2UgaWYgKGNoID09PSA5Mikge1xuICAgICAgLy8gXCJcXFwiXG4gICAgICBjb250YWluc0VzYyA9IHRydWU7XG4gICAgICB3b3JkICs9IHRoaXMuaW5wdXQuc2xpY2UoY2h1bmtTdGFydCwgdGhpcy5wb3MpO1xuICAgICAgdmFyIGVzY1N0YXJ0ID0gdGhpcy5wb3M7XG4gICAgICBpZiAodGhpcy5pbnB1dC5jaGFyQ29kZUF0KCsrdGhpcy5wb3MpICE9IDExNykgLy8gXCJ1XCJcbiAgICAgICAgdGhpcy5yYWlzZSh0aGlzLnBvcywgXCJFeHBlY3RpbmcgVW5pY29kZSBlc2NhcGUgc2VxdWVuY2UgXFxcXHVYWFhYXCIpO1xuICAgICAgKyt0aGlzLnBvcztcbiAgICAgIHZhciBlc2MgPSB0aGlzLnJlYWRDb2RlUG9pbnQoKTtcbiAgICAgIGlmICghKGZpcnN0ID8gaXNJZGVudGlmaWVyU3RhcnQgOiBpc0lkZW50aWZpZXJDaGFyKShlc2MsIGFzdHJhbCkpIHRoaXMucmFpc2UoZXNjU3RhcnQsIFwiSW52YWxpZCBVbmljb2RlIGVzY2FwZVwiKTtcbiAgICAgIHdvcmQgKz0gY29kZVBvaW50VG9TdHJpbmcoZXNjKTtcbiAgICAgIGNodW5rU3RhcnQgPSB0aGlzLnBvcztcbiAgICB9IGVsc2Uge1xuICAgICAgYnJlYWs7XG4gICAgfVxuICAgIGZpcnN0ID0gZmFsc2U7XG4gIH1cbiAgcmV0dXJuIHdvcmQgKyB0aGlzLmlucHV0LnNsaWNlKGNodW5rU3RhcnQsIHRoaXMucG9zKTtcbn07XG5cbi8vIFJlYWQgYW4gaWRlbnRpZmllciBvciBrZXl3b3JkIHRva2VuLiBXaWxsIGNoZWNrIGZvciByZXNlcnZlZFxuLy8gd29yZHMgd2hlbiBuZWNlc3NhcnkuXG5cbnBwLnJlYWRXb3JkID0gZnVuY3Rpb24gKCkge1xuICB2YXIgd29yZCA9IHRoaXMucmVhZFdvcmQxKCk7XG4gIHZhciB0eXBlID0gdHQubmFtZTtcbiAgaWYgKCh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNiB8fCAhY29udGFpbnNFc2MpICYmIHRoaXMuaXNLZXl3b3JkKHdvcmQpKSB0eXBlID0ga2V5d29yZFR5cGVzW3dvcmRdO1xuICByZXR1cm4gdGhpcy5maW5pc2hUb2tlbih0eXBlLCB3b3JkKTtcbn07XG5cbn0se1wiLi9pZGVudGlmaWVyXCI6NyxcIi4vbG9jYXRpb25cIjo4LFwiLi9zdGF0ZVwiOjEzLFwiLi90b2tlbnR5cGVcIjoxNyxcIi4vd2hpdGVzcGFjZVwiOjE5fV0sMTc6W2Z1bmN0aW9uKF9kZXJlcV8sbW9kdWxlLGV4cG9ydHMpe1xuXCJ1c2Ugc3RyaWN0XCI7XG5cbnZhciBfY2xhc3NDYWxsQ2hlY2sgPSBmdW5jdGlvbiAoaW5zdGFuY2UsIENvbnN0cnVjdG9yKSB7IGlmICghKGluc3RhbmNlIGluc3RhbmNlb2YgQ29uc3RydWN0b3IpKSB7IHRocm93IG5ldyBUeXBlRXJyb3IoXCJDYW5ub3QgY2FsbCBhIGNsYXNzIGFzIGEgZnVuY3Rpb25cIik7IH0gfTtcblxuZXhwb3J0cy5fX2VzTW9kdWxlID0gdHJ1ZTtcbi8vICMjIFRva2VuIHR5cGVzXG5cbi8vIFRoZSBhc3NpZ25tZW50IG9mIGZpbmUtZ3JhaW5lZCwgaW5mb3JtYXRpb24tY2FycnlpbmcgdHlwZSBvYmplY3RzXG4vLyBhbGxvd3MgdGhlIHRva2VuaXplciB0byBzdG9yZSB0aGUgaW5mb3JtYXRpb24gaXQgaGFzIGFib3V0IGFcbi8vIHRva2VuIGluIGEgd2F5IHRoYXQgaXMgdmVyeSBjaGVhcCBmb3IgdGhlIHBhcnNlciB0byBsb29rIHVwLlxuXG4vLyBBbGwgdG9rZW4gdHlwZSB2YXJpYWJsZXMgc3RhcnQgd2l0aCBhbiB1bmRlcnNjb3JlLCB0byBtYWtlIHRoZW1cbi8vIGVhc3kgdG8gcmVjb2duaXplLlxuXG4vLyBUaGUgYGJlZm9yZUV4cHJgIHByb3BlcnR5IGlzIHVzZWQgdG8gZGlzYW1iaWd1YXRlIGJldHdlZW4gcmVndWxhclxuLy8gZXhwcmVzc2lvbnMgYW5kIGRpdmlzaW9ucy4gSXQgaXMgc2V0IG9uIGFsbCB0b2tlbiB0eXBlcyB0aGF0IGNhblxuLy8gYmUgZm9sbG93ZWQgYnkgYW4gZXhwcmVzc2lvbiAodGh1cywgYSBzbGFzaCBhZnRlciB0aGVtIHdvdWxkIGJlIGFcbi8vIHJlZ3VsYXIgZXhwcmVzc2lvbikuXG4vL1xuLy8gYGlzTG9vcGAgbWFya3MgYSBrZXl3b3JkIGFzIHN0YXJ0aW5nIGEgbG9vcCwgd2hpY2ggaXMgaW1wb3J0YW50XG4vLyB0byBrbm93IHdoZW4gcGFyc2luZyBhIGxhYmVsLCBpbiBvcmRlciB0byBhbGxvdyBvciBkaXNhbGxvd1xuLy8gY29udGludWUganVtcHMgdG8gdGhhdCBsYWJlbC5cblxudmFyIFRva2VuVHlwZSA9IGV4cG9ydHMuVG9rZW5UeXBlID0gZnVuY3Rpb24gVG9rZW5UeXBlKGxhYmVsKSB7XG4gIHZhciBjb25mID0gYXJndW1lbnRzWzFdID09PSB1bmRlZmluZWQgPyB7fSA6IGFyZ3VtZW50c1sxXTtcblxuICBfY2xhc3NDYWxsQ2hlY2sodGhpcywgVG9rZW5UeXBlKTtcblxuICB0aGlzLmxhYmVsID0gbGFiZWw7XG4gIHRoaXMua2V5d29yZCA9IGNvbmYua2V5d29yZDtcbiAgdGhpcy5iZWZvcmVFeHByID0gISFjb25mLmJlZm9yZUV4cHI7XG4gIHRoaXMuc3RhcnRzRXhwciA9ICEhY29uZi5zdGFydHNFeHByO1xuICB0aGlzLmlzTG9vcCA9ICEhY29uZi5pc0xvb3A7XG4gIHRoaXMuaXNBc3NpZ24gPSAhIWNvbmYuaXNBc3NpZ247XG4gIHRoaXMucHJlZml4ID0gISFjb25mLnByZWZpeDtcbiAgdGhpcy5wb3N0Zml4ID0gISFjb25mLnBvc3RmaXg7XG4gIHRoaXMuYmlub3AgPSBjb25mLmJpbm9wIHx8IG51bGw7XG4gIHRoaXMudXBkYXRlQ29udGV4dCA9IG51bGw7XG59O1xuXG5mdW5jdGlvbiBiaW5vcChuYW1lLCBwcmVjKSB7XG4gIHJldHVybiBuZXcgVG9rZW5UeXBlKG5hbWUsIHsgYmVmb3JlRXhwcjogdHJ1ZSwgYmlub3A6IHByZWMgfSk7XG59XG52YXIgYmVmb3JlRXhwciA9IHsgYmVmb3JlRXhwcjogdHJ1ZSB9LFxuICAgIHN0YXJ0c0V4cHIgPSB7IHN0YXJ0c0V4cHI6IHRydWUgfTtcblxudmFyIHR5cGVzID0ge1xuICBudW06IG5ldyBUb2tlblR5cGUoXCJudW1cIiwgc3RhcnRzRXhwciksXG4gIHJlZ2V4cDogbmV3IFRva2VuVHlwZShcInJlZ2V4cFwiLCBzdGFydHNFeHByKSxcbiAgc3RyaW5nOiBuZXcgVG9rZW5UeXBlKFwic3RyaW5nXCIsIHN0YXJ0c0V4cHIpLFxuICBuYW1lOiBuZXcgVG9rZW5UeXBlKFwibmFtZVwiLCBzdGFydHNFeHByKSxcbiAgZW9mOiBuZXcgVG9rZW5UeXBlKFwiZW9mXCIpLFxuXG4gIC8vIFB1bmN0dWF0aW9uIHRva2VuIHR5cGVzLlxuICBicmFja2V0TDogbmV3IFRva2VuVHlwZShcIltcIiwgeyBiZWZvcmVFeHByOiB0cnVlLCBzdGFydHNFeHByOiB0cnVlIH0pLFxuICBicmFja2V0UjogbmV3IFRva2VuVHlwZShcIl1cIiksXG4gIGJyYWNlTDogbmV3IFRva2VuVHlwZShcIntcIiwgeyBiZWZvcmVFeHByOiB0cnVlLCBzdGFydHNFeHByOiB0cnVlIH0pLFxuICBicmFjZVI6IG5ldyBUb2tlblR5cGUoXCJ9XCIpLFxuICBwYXJlbkw6IG5ldyBUb2tlblR5cGUoXCIoXCIsIHsgYmVmb3JlRXhwcjogdHJ1ZSwgc3RhcnRzRXhwcjogdHJ1ZSB9KSxcbiAgcGFyZW5SOiBuZXcgVG9rZW5UeXBlKFwiKVwiKSxcbiAgY29tbWE6IG5ldyBUb2tlblR5cGUoXCIsXCIsIGJlZm9yZUV4cHIpLFxuICBzZW1pOiBuZXcgVG9rZW5UeXBlKFwiO1wiLCBiZWZvcmVFeHByKSxcbiAgY29sb246IG5ldyBUb2tlblR5cGUoXCI6XCIsIGJlZm9yZUV4cHIpLFxuICBkb3Q6IG5ldyBUb2tlblR5cGUoXCIuXCIpLFxuICBxdWVzdGlvbjogbmV3IFRva2VuVHlwZShcIj9cIiwgYmVmb3JlRXhwciksXG4gIGFycm93OiBuZXcgVG9rZW5UeXBlKFwiPT5cIiwgYmVmb3JlRXhwciksXG4gIHRlbXBsYXRlOiBuZXcgVG9rZW5UeXBlKFwidGVtcGxhdGVcIiksXG4gIGVsbGlwc2lzOiBuZXcgVG9rZW5UeXBlKFwiLi4uXCIsIGJlZm9yZUV4cHIpLFxuICBiYWNrUXVvdGU6IG5ldyBUb2tlblR5cGUoXCJgXCIsIHN0YXJ0c0V4cHIpLFxuICBkb2xsYXJCcmFjZUw6IG5ldyBUb2tlblR5cGUoXCIke1wiLCB7IGJlZm9yZUV4cHI6IHRydWUsIHN0YXJ0c0V4cHI6IHRydWUgfSksXG5cbiAgLy8gT3BlcmF0b3JzLiBUaGVzZSBjYXJyeSBzZXZlcmFsIGtpbmRzIG9mIHByb3BlcnRpZXMgdG8gaGVscCB0aGVcbiAgLy8gcGFyc2VyIHVzZSB0aGVtIHByb3Blcmx5ICh0aGUgcHJlc2VuY2Ugb2YgdGhlc2UgcHJvcGVydGllcyBpc1xuICAvLyB3aGF0IGNhdGVnb3JpemVzIHRoZW0gYXMgb3BlcmF0b3JzKS5cbiAgLy9cbiAgLy8gYGJpbm9wYCwgd2hlbiBwcmVzZW50LCBzcGVjaWZpZXMgdGhhdCB0aGlzIG9wZXJhdG9yIGlzIGEgYmluYXJ5XG4gIC8vIG9wZXJhdG9yLCBhbmQgd2lsbCByZWZlciB0byBpdHMgcHJlY2VkZW5jZS5cbiAgLy9cbiAgLy8gYHByZWZpeGAgYW5kIGBwb3N0Zml4YCBtYXJrIHRoZSBvcGVyYXRvciBhcyBhIHByZWZpeCBvciBwb3N0Zml4XG4gIC8vIHVuYXJ5IG9wZXJhdG9yLlxuICAvL1xuICAvLyBgaXNBc3NpZ25gIG1hcmtzIGFsbCBvZiBgPWAsIGArPWAsIGAtPWAgZXRjZXRlcmEsIHdoaWNoIGFjdCBhc1xuICAvLyBiaW5hcnkgb3BlcmF0b3JzIHdpdGggYSB2ZXJ5IGxvdyBwcmVjZWRlbmNlLCB0aGF0IHNob3VsZCByZXN1bHRcbiAgLy8gaW4gQXNzaWdubWVudEV4cHJlc3Npb24gbm9kZXMuXG5cbiAgZXE6IG5ldyBUb2tlblR5cGUoXCI9XCIsIHsgYmVmb3JlRXhwcjogdHJ1ZSwgaXNBc3NpZ246IHRydWUgfSksXG4gIGFzc2lnbjogbmV3IFRva2VuVHlwZShcIl89XCIsIHsgYmVmb3JlRXhwcjogdHJ1ZSwgaXNBc3NpZ246IHRydWUgfSksXG4gIGluY0RlYzogbmV3IFRva2VuVHlwZShcIisrLy0tXCIsIHsgcHJlZml4OiB0cnVlLCBwb3N0Zml4OiB0cnVlLCBzdGFydHNFeHByOiB0cnVlIH0pLFxuICBwcmVmaXg6IG5ldyBUb2tlblR5cGUoXCJwcmVmaXhcIiwgeyBiZWZvcmVFeHByOiB0cnVlLCBwcmVmaXg6IHRydWUsIHN0YXJ0c0V4cHI6IHRydWUgfSksXG4gIGxvZ2ljYWxPUjogYmlub3AoXCJ8fFwiLCAxKSxcbiAgbG9naWNhbEFORDogYmlub3AoXCImJlwiLCAyKSxcbiAgYml0d2lzZU9SOiBiaW5vcChcInxcIiwgMyksXG4gIGJpdHdpc2VYT1I6IGJpbm9wKFwiXlwiLCA0KSxcbiAgYml0d2lzZUFORDogYmlub3AoXCImXCIsIDUpLFxuICBlcXVhbGl0eTogYmlub3AoXCI9PS8hPVwiLCA2KSxcbiAgcmVsYXRpb25hbDogYmlub3AoXCI8Lz5cIiwgNyksXG4gIGJpdFNoaWZ0OiBiaW5vcChcIjw8Lz4+XCIsIDgpLFxuICBwbHVzTWluOiBuZXcgVG9rZW5UeXBlKFwiKy8tXCIsIHsgYmVmb3JlRXhwcjogdHJ1ZSwgYmlub3A6IDksIHByZWZpeDogdHJ1ZSwgc3RhcnRzRXhwcjogdHJ1ZSB9KSxcbiAgbW9kdWxvOiBiaW5vcChcIiVcIiwgMTApLFxuICBzdGFyOiBiaW5vcChcIipcIiwgMTApLFxuICBzbGFzaDogYmlub3AoXCIvXCIsIDEwKVxufTtcblxuZXhwb3J0cy50eXBlcyA9IHR5cGVzO1xuLy8gTWFwIGtleXdvcmQgbmFtZXMgdG8gdG9rZW4gdHlwZXMuXG5cbnZhciBrZXl3b3JkcyA9IHt9O1xuXG5leHBvcnRzLmtleXdvcmRzID0ga2V5d29yZHM7XG4vLyBTdWNjaW5jdCBkZWZpbml0aW9ucyBvZiBrZXl3b3JkIHRva2VuIHR5cGVzXG5mdW5jdGlvbiBrdyhuYW1lKSB7XG4gIHZhciBvcHRpb25zID0gYXJndW1lbnRzWzFdID09PSB1bmRlZmluZWQgPyB7fSA6IGFyZ3VtZW50c1sxXTtcblxuICBvcHRpb25zLmtleXdvcmQgPSBuYW1lO1xuICBrZXl3b3Jkc1tuYW1lXSA9IHR5cGVzW1wiX1wiICsgbmFtZV0gPSBuZXcgVG9rZW5UeXBlKG5hbWUsIG9wdGlvbnMpO1xufVxuXG5rdyhcImJyZWFrXCIpO1xua3coXCJjYXNlXCIsIGJlZm9yZUV4cHIpO1xua3coXCJjYXRjaFwiKTtcbmt3KFwiY29udGludWVcIik7XG5rdyhcImRlYnVnZ2VyXCIpO1xua3coXCJkZWZhdWx0XCIpO1xua3coXCJkb1wiLCB7IGlzTG9vcDogdHJ1ZSB9KTtcbmt3KFwiZWxzZVwiLCBiZWZvcmVFeHByKTtcbmt3KFwiZmluYWxseVwiKTtcbmt3KFwiZm9yXCIsIHsgaXNMb29wOiB0cnVlIH0pO1xua3coXCJmdW5jdGlvblwiLCBzdGFydHNFeHByKTtcbmt3KFwiaWZcIik7XG5rdyhcInJldHVyblwiLCBiZWZvcmVFeHByKTtcbmt3KFwic3dpdGNoXCIpO1xua3coXCJ0aHJvd1wiLCBiZWZvcmVFeHByKTtcbmt3KFwidHJ5XCIpO1xua3coXCJ2YXJcIik7XG5rdyhcImxldFwiKTtcbmt3KFwiY29uc3RcIik7XG5rdyhcIndoaWxlXCIsIHsgaXNMb29wOiB0cnVlIH0pO1xua3coXCJ3aXRoXCIpO1xua3coXCJuZXdcIiwgeyBiZWZvcmVFeHByOiB0cnVlLCBzdGFydHNFeHByOiB0cnVlIH0pO1xua3coXCJ0aGlzXCIsIHN0YXJ0c0V4cHIpO1xua3coXCJzdXBlclwiLCBzdGFydHNFeHByKTtcbmt3KFwiY2xhc3NcIik7XG5rdyhcImV4dGVuZHNcIiwgYmVmb3JlRXhwcik7XG5rdyhcImV4cG9ydFwiKTtcbmt3KFwiaW1wb3J0XCIpO1xua3coXCJ5aWVsZFwiLCB7IGJlZm9yZUV4cHI6IHRydWUsIHN0YXJ0c0V4cHI6IHRydWUgfSk7XG5rdyhcIm51bGxcIiwgc3RhcnRzRXhwcik7XG5rdyhcInRydWVcIiwgc3RhcnRzRXhwcik7XG5rdyhcImZhbHNlXCIsIHN0YXJ0c0V4cHIpO1xua3coXCJpblwiLCB7IGJlZm9yZUV4cHI6IHRydWUsIGJpbm9wOiA3IH0pO1xua3coXCJpbnN0YW5jZW9mXCIsIHsgYmVmb3JlRXhwcjogdHJ1ZSwgYmlub3A6IDcgfSk7XG5rdyhcInR5cGVvZlwiLCB7IGJlZm9yZUV4cHI6IHRydWUsIHByZWZpeDogdHJ1ZSwgc3RhcnRzRXhwcjogdHJ1ZSB9KTtcbmt3KFwidm9pZFwiLCB7IGJlZm9yZUV4cHI6IHRydWUsIHByZWZpeDogdHJ1ZSwgc3RhcnRzRXhwcjogdHJ1ZSB9KTtcbmt3KFwiZGVsZXRlXCIsIHsgYmVmb3JlRXhwcjogdHJ1ZSwgcHJlZml4OiB0cnVlLCBzdGFydHNFeHByOiB0cnVlIH0pO1xuXG59LHt9XSwxODpbZnVuY3Rpb24oX2RlcmVxXyxtb2R1bGUsZXhwb3J0cyl7XG5cInVzZSBzdHJpY3RcIjtcblxuZXhwb3J0cy5pc0FycmF5ID0gaXNBcnJheTtcblxuLy8gQ2hlY2tzIGlmIGFuIG9iamVjdCBoYXMgYSBwcm9wZXJ0eS5cblxuZXhwb3J0cy5oYXMgPSBoYXM7XG5leHBvcnRzLl9fZXNNb2R1bGUgPSB0cnVlO1xuXG5mdW5jdGlvbiBpc0FycmF5KG9iaikge1xuICByZXR1cm4gT2JqZWN0LnByb3RvdHlwZS50b1N0cmluZy5jYWxsKG9iaikgPT09IFwiW29iamVjdCBBcnJheV1cIjtcbn1cblxuZnVuY3Rpb24gaGFzKG9iaiwgcHJvcE5hbWUpIHtcbiAgcmV0dXJuIE9iamVjdC5wcm90b3R5cGUuaGFzT3duUHJvcGVydHkuY2FsbChvYmosIHByb3BOYW1lKTtcbn1cblxufSx7fV0sMTk6W2Z1bmN0aW9uKF9kZXJlcV8sbW9kdWxlLGV4cG9ydHMpe1xuXCJ1c2Ugc3RyaWN0XCI7XG5cbmV4cG9ydHMuaXNOZXdMaW5lID0gaXNOZXdMaW5lO1xuZXhwb3J0cy5fX2VzTW9kdWxlID0gdHJ1ZTtcbi8vIE1hdGNoZXMgYSB3aG9sZSBsaW5lIGJyZWFrICh3aGVyZSBDUkxGIGlzIGNvbnNpZGVyZWQgYSBzaW5nbGVcbi8vIGxpbmUgYnJlYWspLiBVc2VkIHRvIGNvdW50IGxpbmVzLlxuXG52YXIgbGluZUJyZWFrID0gL1xcclxcbj98XFxufFxcdTIwMjh8XFx1MjAyOS87XG5leHBvcnRzLmxpbmVCcmVhayA9IGxpbmVCcmVhaztcbnZhciBsaW5lQnJlYWtHID0gbmV3IFJlZ0V4cChsaW5lQnJlYWsuc291cmNlLCBcImdcIik7XG5cbmV4cG9ydHMubGluZUJyZWFrRyA9IGxpbmVCcmVha0c7XG5cbmZ1bmN0aW9uIGlzTmV3TGluZShjb2RlKSB7XG4gIHJldHVybiBjb2RlID09PSAxMCB8fCBjb2RlID09PSAxMyB8fCBjb2RlID09PSA4MjMyIHx8IGNvZGUgPT0gODIzMztcbn1cblxudmFyIG5vbkFTQ0lJd2hpdGVzcGFjZSA9IC9bXFx1MTY4MFxcdTE4MGVcXHUyMDAwLVxcdTIwMGFcXHUyMDJmXFx1MjA1ZlxcdTMwMDBcXHVmZWZmXS87XG5leHBvcnRzLm5vbkFTQ0lJd2hpdGVzcGFjZSA9IG5vbkFTQ0lJd2hpdGVzcGFjZTtcblxufSx7fV19LHt9LFsxXSkoMSlcbn0pOyIsIihmdW5jdGlvbihmKXtpZih0eXBlb2YgZXhwb3J0cz09PVwib2JqZWN0XCImJnR5cGVvZiBtb2R1bGUhPT1cInVuZGVmaW5lZFwiKXttb2R1bGUuZXhwb3J0cz1mKCl9ZWxzZSBpZih0eXBlb2YgZGVmaW5lPT09XCJmdW5jdGlvblwiJiZkZWZpbmUuYW1kKXtkZWZpbmUoW10sZil9ZWxzZXt2YXIgZztpZih0eXBlb2Ygd2luZG93IT09XCJ1bmRlZmluZWRcIil7Zz13aW5kb3d9ZWxzZSBpZih0eXBlb2YgZ2xvYmFsIT09XCJ1bmRlZmluZWRcIil7Zz1nbG9iYWx9ZWxzZSBpZih0eXBlb2Ygc2VsZiE9PVwidW5kZWZpbmVkXCIpe2c9c2VsZn1lbHNle2c9dGhpc30oZy5hY29ybiB8fCAoZy5hY29ybiA9IHt9KSkud2FsayA9IGYoKX19KShmdW5jdGlvbigpe3ZhciBkZWZpbmUsbW9kdWxlLGV4cG9ydHM7cmV0dXJuIChmdW5jdGlvbiBlKHQsbixyKXtmdW5jdGlvbiBzKG8sdSl7aWYoIW5bb10pe2lmKCF0W29dKXt2YXIgYT10eXBlb2YgcmVxdWlyZT09XCJmdW5jdGlvblwiJiZyZXF1aXJlO2lmKCF1JiZhKXJldHVybiBhKG8sITApO2lmKGkpcmV0dXJuIGkobywhMCk7dmFyIGY9bmV3IEVycm9yKFwiQ2Fubm90IGZpbmQgbW9kdWxlICdcIitvK1wiJ1wiKTt0aHJvdyBmLmNvZGU9XCJNT0RVTEVfTk9UX0ZPVU5EXCIsZn12YXIgbD1uW29dPXtleHBvcnRzOnt9fTt0W29dWzBdLmNhbGwobC5leHBvcnRzLGZ1bmN0aW9uKGUpe3ZhciBuPXRbb11bMV1bZV07cmV0dXJuIHMobj9uOmUpfSxsLGwuZXhwb3J0cyxlLHQsbixyKX1yZXR1cm4gbltvXS5leHBvcnRzfXZhciBpPXR5cGVvZiByZXF1aXJlPT1cImZ1bmN0aW9uXCImJnJlcXVpcmU7Zm9yKHZhciBvPTA7bzxyLmxlbmd0aDtvKyspcyhyW29dKTtyZXR1cm4gc30pKHsxOltmdW5jdGlvbihfZGVyZXFfLG1vZHVsZSxleHBvcnRzKXtcblwidXNlIHN0cmljdFwiO1xuXG52YXIgX2NsYXNzQ2FsbENoZWNrID0gZnVuY3Rpb24gKGluc3RhbmNlLCBDb25zdHJ1Y3RvcikgeyBpZiAoIShpbnN0YW5jZSBpbnN0YW5jZW9mIENvbnN0cnVjdG9yKSkgeyB0aHJvdyBuZXcgVHlwZUVycm9yKFwiQ2Fubm90IGNhbGwgYSBjbGFzcyBhcyBhIGZ1bmN0aW9uXCIpOyB9IH07XG5cbi8vIEFTVCB3YWxrZXIgbW9kdWxlIGZvciBNb3ppbGxhIFBhcnNlciBBUEkgY29tcGF0aWJsZSB0cmVlc1xuXG4vLyBBIHNpbXBsZSB3YWxrIGlzIG9uZSB3aGVyZSB5b3Ugc2ltcGx5IHNwZWNpZnkgY2FsbGJhY2tzIHRvIGJlXG4vLyBjYWxsZWQgb24gc3BlY2lmaWMgbm9kZXMuIFRoZSBsYXN0IHR3byBhcmd1bWVudHMgYXJlIG9wdGlvbmFsLiBBXG4vLyBzaW1wbGUgdXNlIHdvdWxkIGJlXG4vL1xuLy8gICAgIHdhbGsuc2ltcGxlKG15VHJlZSwge1xuLy8gICAgICAgICBFeHByZXNzaW9uOiBmdW5jdGlvbihub2RlKSB7IC4uLiB9XG4vLyAgICAgfSk7XG4vL1xuLy8gdG8gZG8gc29tZXRoaW5nIHdpdGggYWxsIGV4cHJlc3Npb25zLiBBbGwgUGFyc2VyIEFQSSBub2RlIHR5cGVzXG4vLyBjYW4gYmUgdXNlZCB0byBpZGVudGlmeSBub2RlIHR5cGVzLCBhcyB3ZWxsIGFzIEV4cHJlc3Npb24sXG4vLyBTdGF0ZW1lbnQsIGFuZCBTY29wZUJvZHksIHdoaWNoIGRlbm90ZSBjYXRlZ29yaWVzIG9mIG5vZGVzLlxuLy9cbi8vIFRoZSBiYXNlIGFyZ3VtZW50IGNhbiBiZSB1c2VkIHRvIHBhc3MgYSBjdXN0b20gKHJlY3Vyc2l2ZSlcbi8vIHdhbGtlciwgYW5kIHN0YXRlIGNhbiBiZSB1c2VkIHRvIGdpdmUgdGhpcyB3YWxrZWQgYW4gaW5pdGlhbFxuLy8gc3RhdGUuXG5cbmV4cG9ydHMuc2ltcGxlID0gc2ltcGxlO1xuXG4vLyBBbiBhbmNlc3RvciB3YWxrIGJ1aWxkcyB1cCBhbiBhcnJheSBvZiBhbmNlc3RvciBub2RlcyAoaW5jbHVkaW5nXG4vLyB0aGUgY3VycmVudCBub2RlKSBhbmQgcGFzc2VzIHRoZW0gdG8gdGhlIGNhbGxiYWNrIGFzIHRoZSBzdGF0ZSBwYXJhbWV0ZXIuXG5leHBvcnRzLmFuY2VzdG9yID0gYW5jZXN0b3I7XG5cbi8vIEEgcmVjdXJzaXZlIHdhbGsgaXMgb25lIHdoZXJlIHlvdXIgZnVuY3Rpb25zIG92ZXJyaWRlIHRoZSBkZWZhdWx0XG4vLyB3YWxrZXJzLiBUaGV5IGNhbiBtb2RpZnkgYW5kIHJlcGxhY2UgdGhlIHN0YXRlIHBhcmFtZXRlciB0aGF0J3Ncbi8vIHRocmVhZGVkIHRocm91Z2ggdGhlIHdhbGssIGFuZCBjYW4gb3B0IGhvdyBhbmQgd2hldGhlciB0byB3YWxrXG4vLyB0aGVpciBjaGlsZCBub2RlcyAoYnkgY2FsbGluZyB0aGVpciB0aGlyZCBhcmd1bWVudCBvbiB0aGVzZVxuLy8gbm9kZXMpLlxuZXhwb3J0cy5yZWN1cnNpdmUgPSByZWN1cnNpdmU7XG5cbi8vIEZpbmQgYSBub2RlIHdpdGggYSBnaXZlbiBzdGFydCwgZW5kLCBhbmQgdHlwZSAoYWxsIGFyZSBvcHRpb25hbCxcbi8vIG51bGwgY2FuIGJlIHVzZWQgYXMgd2lsZGNhcmQpLiBSZXR1cm5zIGEge25vZGUsIHN0YXRlfSBvYmplY3QsIG9yXG4vLyB1bmRlZmluZWQgd2hlbiBpdCBkb2Vzbid0IGZpbmQgYSBtYXRjaGluZyBub2RlLlxuZXhwb3J0cy5maW5kTm9kZUF0ID0gZmluZE5vZGVBdDtcblxuLy8gRmluZCB0aGUgaW5uZXJtb3N0IG5vZGUgb2YgYSBnaXZlbiB0eXBlIHRoYXQgY29udGFpbnMgdGhlIGdpdmVuXG4vLyBwb3NpdGlvbi4gSW50ZXJmYWNlIHNpbWlsYXIgdG8gZmluZE5vZGVBdC5cbmV4cG9ydHMuZmluZE5vZGVBcm91bmQgPSBmaW5kTm9kZUFyb3VuZDtcblxuLy8gRmluZCB0aGUgb3V0ZXJtb3N0IG1hdGNoaW5nIG5vZGUgYWZ0ZXIgYSBnaXZlbiBwb3NpdGlvbi5cbmV4cG9ydHMuZmluZE5vZGVBZnRlciA9IGZpbmROb2RlQWZ0ZXI7XG5cbi8vIEZpbmQgdGhlIG91dGVybW9zdCBtYXRjaGluZyBub2RlIGJlZm9yZSBhIGdpdmVuIHBvc2l0aW9uLlxuZXhwb3J0cy5maW5kTm9kZUJlZm9yZSA9IGZpbmROb2RlQmVmb3JlO1xuXG4vLyBVc2VkIHRvIGNyZWF0ZSBhIGN1c3RvbSB3YWxrZXIuIFdpbGwgZmlsbCBpbiBhbGwgbWlzc2luZyBub2RlXG4vLyB0eXBlIHByb3BlcnRpZXMgd2l0aCB0aGUgZGVmYXVsdHMuXG5leHBvcnRzLm1ha2UgPSBtYWtlO1xuZXhwb3J0cy5fX2VzTW9kdWxlID0gdHJ1ZTtcblxuZnVuY3Rpb24gc2ltcGxlKG5vZGUsIHZpc2l0b3JzLCBiYXNlLCBzdGF0ZSkge1xuICBpZiAoIWJhc2UpIGJhc2UgPSBleHBvcnRzLmJhc2U7KGZ1bmN0aW9uIGMobm9kZSwgc3QsIG92ZXJyaWRlKSB7XG4gICAgdmFyIHR5cGUgPSBvdmVycmlkZSB8fCBub2RlLnR5cGUsXG4gICAgICAgIGZvdW5kID0gdmlzaXRvcnNbdHlwZV07XG4gICAgYmFzZVt0eXBlXShub2RlLCBzdCwgYyk7XG4gICAgaWYgKGZvdW5kKSBmb3VuZChub2RlLCBzdCk7XG4gIH0pKG5vZGUsIHN0YXRlKTtcbn1cblxuZnVuY3Rpb24gYW5jZXN0b3Iobm9kZSwgdmlzaXRvcnMsIGJhc2UsIHN0YXRlKSB7XG4gIGlmICghYmFzZSkgYmFzZSA9IGV4cG9ydHMuYmFzZTtcbiAgaWYgKCFzdGF0ZSkgc3RhdGUgPSBbXTsoZnVuY3Rpb24gYyhub2RlLCBzdCwgb3ZlcnJpZGUpIHtcbiAgICB2YXIgdHlwZSA9IG92ZXJyaWRlIHx8IG5vZGUudHlwZSxcbiAgICAgICAgZm91bmQgPSB2aXNpdG9yc1t0eXBlXTtcbiAgICBpZiAobm9kZSAhPSBzdFtzdC5sZW5ndGggLSAxXSkge1xuICAgICAgc3QgPSBzdC5zbGljZSgpO1xuICAgICAgc3QucHVzaChub2RlKTtcbiAgICB9XG4gICAgYmFzZVt0eXBlXShub2RlLCBzdCwgYyk7XG4gICAgaWYgKGZvdW5kKSBmb3VuZChub2RlLCBzdCk7XG4gIH0pKG5vZGUsIHN0YXRlKTtcbn1cblxuZnVuY3Rpb24gcmVjdXJzaXZlKG5vZGUsIHN0YXRlLCBmdW5jcywgYmFzZSkge1xuICB2YXIgdmlzaXRvciA9IGZ1bmNzID8gZXhwb3J0cy5tYWtlKGZ1bmNzLCBiYXNlKSA6IGJhc2U7KGZ1bmN0aW9uIGMobm9kZSwgc3QsIG92ZXJyaWRlKSB7XG4gICAgdmlzaXRvcltvdmVycmlkZSB8fCBub2RlLnR5cGVdKG5vZGUsIHN0LCBjKTtcbiAgfSkobm9kZSwgc3RhdGUpO1xufVxuXG5mdW5jdGlvbiBtYWtlVGVzdCh0ZXN0KSB7XG4gIGlmICh0eXBlb2YgdGVzdCA9PSBcInN0cmluZ1wiKSB7XG4gICAgcmV0dXJuIGZ1bmN0aW9uICh0eXBlKSB7XG4gICAgICByZXR1cm4gdHlwZSA9PSB0ZXN0O1xuICAgIH07XG4gIH0gZWxzZSBpZiAoIXRlc3QpIHtcbiAgICByZXR1cm4gZnVuY3Rpb24gKCkge1xuICAgICAgcmV0dXJuIHRydWU7XG4gICAgfTtcbiAgfSBlbHNlIHtcbiAgICByZXR1cm4gdGVzdDtcbiAgfVxufVxuXG52YXIgRm91bmQgPSBmdW5jdGlvbiBGb3VuZChub2RlLCBzdGF0ZSkge1xuICBfY2xhc3NDYWxsQ2hlY2sodGhpcywgRm91bmQpO1xuXG4gIHRoaXMubm9kZSA9IG5vZGU7dGhpcy5zdGF0ZSA9IHN0YXRlO1xufTtcblxuZnVuY3Rpb24gZmluZE5vZGVBdChub2RlLCBzdGFydCwgZW5kLCB0ZXN0LCBiYXNlLCBzdGF0ZSkge1xuICB0ZXN0ID0gbWFrZVRlc3QodGVzdCk7XG4gIGlmICghYmFzZSkgYmFzZSA9IGV4cG9ydHMuYmFzZTtcbiAgdHJ5IHtcbiAgICA7KGZ1bmN0aW9uIGMobm9kZSwgc3QsIG92ZXJyaWRlKSB7XG4gICAgICB2YXIgdHlwZSA9IG92ZXJyaWRlIHx8IG5vZGUudHlwZTtcbiAgICAgIGlmICgoc3RhcnQgPT0gbnVsbCB8fCBub2RlLnN0YXJ0IDw9IHN0YXJ0KSAmJiAoZW5kID09IG51bGwgfHwgbm9kZS5lbmQgPj0gZW5kKSkgYmFzZVt0eXBlXShub2RlLCBzdCwgYyk7XG4gICAgICBpZiAodGVzdCh0eXBlLCBub2RlKSAmJiAoc3RhcnQgPT0gbnVsbCB8fCBub2RlLnN0YXJ0ID09IHN0YXJ0KSAmJiAoZW5kID09IG51bGwgfHwgbm9kZS5lbmQgPT0gZW5kKSkgdGhyb3cgbmV3IEZvdW5kKG5vZGUsIHN0KTtcbiAgICB9KShub2RlLCBzdGF0ZSk7XG4gIH0gY2F0Y2ggKGUpIHtcbiAgICBpZiAoZSBpbnN0YW5jZW9mIEZvdW5kKSB7XG4gICAgICByZXR1cm4gZTtcbiAgICB9dGhyb3cgZTtcbiAgfVxufVxuXG5mdW5jdGlvbiBmaW5kTm9kZUFyb3VuZChub2RlLCBwb3MsIHRlc3QsIGJhc2UsIHN0YXRlKSB7XG4gIHRlc3QgPSBtYWtlVGVzdCh0ZXN0KTtcbiAgaWYgKCFiYXNlKSBiYXNlID0gZXhwb3J0cy5iYXNlO1xuICB0cnkge1xuICAgIDsoZnVuY3Rpb24gYyhub2RlLCBzdCwgb3ZlcnJpZGUpIHtcbiAgICAgIHZhciB0eXBlID0gb3ZlcnJpZGUgfHwgbm9kZS50eXBlO1xuICAgICAgaWYgKG5vZGUuc3RhcnQgPiBwb3MgfHwgbm9kZS5lbmQgPCBwb3MpIHtcbiAgICAgICAgcmV0dXJuO1xuICAgICAgfWJhc2VbdHlwZV0obm9kZSwgc3QsIGMpO1xuICAgICAgaWYgKHRlc3QodHlwZSwgbm9kZSkpIHRocm93IG5ldyBGb3VuZChub2RlLCBzdCk7XG4gICAgfSkobm9kZSwgc3RhdGUpO1xuICB9IGNhdGNoIChlKSB7XG4gICAgaWYgKGUgaW5zdGFuY2VvZiBGb3VuZCkge1xuICAgICAgcmV0dXJuIGU7XG4gICAgfXRocm93IGU7XG4gIH1cbn1cblxuZnVuY3Rpb24gZmluZE5vZGVBZnRlcihub2RlLCBwb3MsIHRlc3QsIGJhc2UsIHN0YXRlKSB7XG4gIHRlc3QgPSBtYWtlVGVzdCh0ZXN0KTtcbiAgaWYgKCFiYXNlKSBiYXNlID0gZXhwb3J0cy5iYXNlO1xuICB0cnkge1xuICAgIDsoZnVuY3Rpb24gYyhub2RlLCBzdCwgb3ZlcnJpZGUpIHtcbiAgICAgIGlmIChub2RlLmVuZCA8IHBvcykge1xuICAgICAgICByZXR1cm47XG4gICAgICB9dmFyIHR5cGUgPSBvdmVycmlkZSB8fCBub2RlLnR5cGU7XG4gICAgICBpZiAobm9kZS5zdGFydCA+PSBwb3MgJiYgdGVzdCh0eXBlLCBub2RlKSkgdGhyb3cgbmV3IEZvdW5kKG5vZGUsIHN0KTtcbiAgICAgIGJhc2VbdHlwZV0obm9kZSwgc3QsIGMpO1xuICAgIH0pKG5vZGUsIHN0YXRlKTtcbiAgfSBjYXRjaCAoZSkge1xuICAgIGlmIChlIGluc3RhbmNlb2YgRm91bmQpIHtcbiAgICAgIHJldHVybiBlO1xuICAgIH10aHJvdyBlO1xuICB9XG59XG5cbmZ1bmN0aW9uIGZpbmROb2RlQmVmb3JlKG5vZGUsIHBvcywgdGVzdCwgYmFzZSwgc3RhdGUpIHtcbiAgdGVzdCA9IG1ha2VUZXN0KHRlc3QpO1xuICBpZiAoIWJhc2UpIGJhc2UgPSBleHBvcnRzLmJhc2U7XG4gIHZhciBtYXggPSB1bmRlZmluZWQ7KGZ1bmN0aW9uIGMobm9kZSwgc3QsIG92ZXJyaWRlKSB7XG4gICAgaWYgKG5vZGUuc3RhcnQgPiBwb3MpIHtcbiAgICAgIHJldHVybjtcbiAgICB9dmFyIHR5cGUgPSBvdmVycmlkZSB8fCBub2RlLnR5cGU7XG4gICAgaWYgKG5vZGUuZW5kIDw9IHBvcyAmJiAoIW1heCB8fCBtYXgubm9kZS5lbmQgPCBub2RlLmVuZCkgJiYgdGVzdCh0eXBlLCBub2RlKSkgbWF4ID0gbmV3IEZvdW5kKG5vZGUsIHN0KTtcbiAgICBiYXNlW3R5cGVdKG5vZGUsIHN0LCBjKTtcbiAgfSkobm9kZSwgc3RhdGUpO1xuICByZXR1cm4gbWF4O1xufVxuXG5mdW5jdGlvbiBtYWtlKGZ1bmNzLCBiYXNlKSB7XG4gIGlmICghYmFzZSkgYmFzZSA9IGV4cG9ydHMuYmFzZTtcbiAgdmFyIHZpc2l0b3IgPSB7fTtcbiAgZm9yICh2YXIgdHlwZSBpbiBiYXNlKSB2aXNpdG9yW3R5cGVdID0gYmFzZVt0eXBlXTtcbiAgZm9yICh2YXIgdHlwZSBpbiBmdW5jcykgdmlzaXRvclt0eXBlXSA9IGZ1bmNzW3R5cGVdO1xuICByZXR1cm4gdmlzaXRvcjtcbn1cblxuZnVuY3Rpb24gc2tpcFRocm91Z2gobm9kZSwgc3QsIGMpIHtcbiAgYyhub2RlLCBzdCk7XG59XG5mdW5jdGlvbiBpZ25vcmUoX25vZGUsIF9zdCwgX2MpIHt9XG5cbi8vIE5vZGUgd2Fsa2Vycy5cblxudmFyIGJhc2UgPSB7fTtcblxuZXhwb3J0cy5iYXNlID0gYmFzZTtcbmJhc2UuUHJvZ3JhbSA9IGJhc2UuQmxvY2tTdGF0ZW1lbnQgPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgZm9yICh2YXIgaSA9IDA7IGkgPCBub2RlLmJvZHkubGVuZ3RoOyArK2kpIHtcbiAgICBjKG5vZGUuYm9keVtpXSwgc3QsIFwiU3RhdGVtZW50XCIpO1xuICB9XG59O1xuYmFzZS5TdGF0ZW1lbnQgPSBza2lwVGhyb3VnaDtcbmJhc2UuRW1wdHlTdGF0ZW1lbnQgPSBpZ25vcmU7XG5iYXNlLkV4cHJlc3Npb25TdGF0ZW1lbnQgPSBiYXNlLlBhcmVudGhlc2l6ZWRFeHByZXNzaW9uID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIHJldHVybiBjKG5vZGUuZXhwcmVzc2lvbiwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbn07XG5iYXNlLklmU3RhdGVtZW50ID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIGMobm9kZS50ZXN0LCBzdCwgXCJFeHByZXNzaW9uXCIpO1xuICBjKG5vZGUuY29uc2VxdWVudCwgc3QsIFwiU3RhdGVtZW50XCIpO1xuICBpZiAobm9kZS5hbHRlcm5hdGUpIGMobm9kZS5hbHRlcm5hdGUsIHN0LCBcIlN0YXRlbWVudFwiKTtcbn07XG5iYXNlLkxhYmVsZWRTdGF0ZW1lbnQgPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgcmV0dXJuIGMobm9kZS5ib2R5LCBzdCwgXCJTdGF0ZW1lbnRcIik7XG59O1xuYmFzZS5CcmVha1N0YXRlbWVudCA9IGJhc2UuQ29udGludWVTdGF0ZW1lbnQgPSBpZ25vcmU7XG5iYXNlLldpdGhTdGF0ZW1lbnQgPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgYyhub2RlLm9iamVjdCwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbiAgYyhub2RlLmJvZHksIHN0LCBcIlN0YXRlbWVudFwiKTtcbn07XG5iYXNlLlN3aXRjaFN0YXRlbWVudCA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBjKG5vZGUuZGlzY3JpbWluYW50LCBzdCwgXCJFeHByZXNzaW9uXCIpO1xuICBmb3IgKHZhciBpID0gMDsgaSA8IG5vZGUuY2FzZXMubGVuZ3RoOyArK2kpIHtcbiAgICB2YXIgY3MgPSBub2RlLmNhc2VzW2ldO1xuICAgIGlmIChjcy50ZXN0KSBjKGNzLnRlc3QsIHN0LCBcIkV4cHJlc3Npb25cIik7XG4gICAgZm9yICh2YXIgaiA9IDA7IGogPCBjcy5jb25zZXF1ZW50Lmxlbmd0aDsgKytqKSB7XG4gICAgICBjKGNzLmNvbnNlcXVlbnRbal0sIHN0LCBcIlN0YXRlbWVudFwiKTtcbiAgICB9XG4gIH1cbn07XG5iYXNlLlJldHVyblN0YXRlbWVudCA9IGJhc2UuWWllbGRFeHByZXNzaW9uID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIGlmIChub2RlLmFyZ3VtZW50KSBjKG5vZGUuYXJndW1lbnQsIHN0LCBcIkV4cHJlc3Npb25cIik7XG59O1xuYmFzZS5UaHJvd1N0YXRlbWVudCA9IGJhc2UuU3ByZWFkRWxlbWVudCA9IGJhc2UuUmVzdEVsZW1lbnQgPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgcmV0dXJuIGMobm9kZS5hcmd1bWVudCwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbn07XG5iYXNlLlRyeVN0YXRlbWVudCA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBjKG5vZGUuYmxvY2ssIHN0LCBcIlN0YXRlbWVudFwiKTtcbiAgaWYgKG5vZGUuaGFuZGxlcikgYyhub2RlLmhhbmRsZXIuYm9keSwgc3QsIFwiU2NvcGVCb2R5XCIpO1xuICBpZiAobm9kZS5maW5hbGl6ZXIpIGMobm9kZS5maW5hbGl6ZXIsIHN0LCBcIlN0YXRlbWVudFwiKTtcbn07XG5iYXNlLldoaWxlU3RhdGVtZW50ID0gYmFzZS5Eb1doaWxlU3RhdGVtZW50ID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIGMobm9kZS50ZXN0LCBzdCwgXCJFeHByZXNzaW9uXCIpO1xuICBjKG5vZGUuYm9keSwgc3QsIFwiU3RhdGVtZW50XCIpO1xufTtcbmJhc2UuRm9yU3RhdGVtZW50ID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIGlmIChub2RlLmluaXQpIGMobm9kZS5pbml0LCBzdCwgXCJGb3JJbml0XCIpO1xuICBpZiAobm9kZS50ZXN0KSBjKG5vZGUudGVzdCwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbiAgaWYgKG5vZGUudXBkYXRlKSBjKG5vZGUudXBkYXRlLCBzdCwgXCJFeHByZXNzaW9uXCIpO1xuICBjKG5vZGUuYm9keSwgc3QsIFwiU3RhdGVtZW50XCIpO1xufTtcbmJhc2UuRm9ySW5TdGF0ZW1lbnQgPSBiYXNlLkZvck9mU3RhdGVtZW50ID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIGMobm9kZS5sZWZ0LCBzdCwgXCJGb3JJbml0XCIpO1xuICBjKG5vZGUucmlnaHQsIHN0LCBcIkV4cHJlc3Npb25cIik7XG4gIGMobm9kZS5ib2R5LCBzdCwgXCJTdGF0ZW1lbnRcIik7XG59O1xuYmFzZS5Gb3JJbml0ID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIGlmIChub2RlLnR5cGUgPT0gXCJWYXJpYWJsZURlY2xhcmF0aW9uXCIpIGMobm9kZSwgc3QpO2Vsc2UgYyhub2RlLCBzdCwgXCJFeHByZXNzaW9uXCIpO1xufTtcbmJhc2UuRGVidWdnZXJTdGF0ZW1lbnQgPSBpZ25vcmU7XG5cbmJhc2UuRnVuY3Rpb25EZWNsYXJhdGlvbiA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICByZXR1cm4gYyhub2RlLCBzdCwgXCJGdW5jdGlvblwiKTtcbn07XG5iYXNlLlZhcmlhYmxlRGVjbGFyYXRpb24gPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgZm9yICh2YXIgaSA9IDA7IGkgPCBub2RlLmRlY2xhcmF0aW9ucy5sZW5ndGg7ICsraSkge1xuICAgIHZhciBkZWNsID0gbm9kZS5kZWNsYXJhdGlvbnNbaV07XG4gICAgaWYgKGRlY2wuaW5pdCkgYyhkZWNsLmluaXQsIHN0LCBcIkV4cHJlc3Npb25cIik7XG4gIH1cbn07XG5cbmJhc2UuRnVuY3Rpb24gPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgcmV0dXJuIGMobm9kZS5ib2R5LCBzdCwgXCJTY29wZUJvZHlcIik7XG59O1xuYmFzZS5TY29wZUJvZHkgPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgcmV0dXJuIGMobm9kZSwgc3QsIFwiU3RhdGVtZW50XCIpO1xufTtcblxuYmFzZS5FeHByZXNzaW9uID0gc2tpcFRocm91Z2g7XG5iYXNlLlRoaXNFeHByZXNzaW9uID0gYmFzZS5TdXBlciA9IGJhc2UuTWV0YVByb3BlcnR5ID0gaWdub3JlO1xuYmFzZS5BcnJheUV4cHJlc3Npb24gPSBiYXNlLkFycmF5UGF0dGVybiA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBmb3IgKHZhciBpID0gMDsgaSA8IG5vZGUuZWxlbWVudHMubGVuZ3RoOyArK2kpIHtcbiAgICB2YXIgZWx0ID0gbm9kZS5lbGVtZW50c1tpXTtcbiAgICBpZiAoZWx0KSBjKGVsdCwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbiAgfVxufTtcbmJhc2UuT2JqZWN0RXhwcmVzc2lvbiA9IGJhc2UuT2JqZWN0UGF0dGVybiA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBmb3IgKHZhciBpID0gMDsgaSA8IG5vZGUucHJvcGVydGllcy5sZW5ndGg7ICsraSkge1xuICAgIGMobm9kZS5wcm9wZXJ0aWVzW2ldLCBzdCk7XG4gIH1cbn07XG5iYXNlLkZ1bmN0aW9uRXhwcmVzc2lvbiA9IGJhc2UuQXJyb3dGdW5jdGlvbkV4cHJlc3Npb24gPSBiYXNlLkZ1bmN0aW9uRGVjbGFyYXRpb247XG5iYXNlLlNlcXVlbmNlRXhwcmVzc2lvbiA9IGJhc2UuVGVtcGxhdGVMaXRlcmFsID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIGZvciAodmFyIGkgPSAwOyBpIDwgbm9kZS5leHByZXNzaW9ucy5sZW5ndGg7ICsraSkge1xuICAgIGMobm9kZS5leHByZXNzaW9uc1tpXSwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbiAgfVxufTtcbmJhc2UuVW5hcnlFeHByZXNzaW9uID0gYmFzZS5VcGRhdGVFeHByZXNzaW9uID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIGMobm9kZS5hcmd1bWVudCwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbn07XG5iYXNlLkJpbmFyeUV4cHJlc3Npb24gPSBiYXNlLkFzc2lnbm1lbnRFeHByZXNzaW9uID0gYmFzZS5Bc3NpZ25tZW50UGF0dGVybiA9IGJhc2UuTG9naWNhbEV4cHJlc3Npb24gPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgYyhub2RlLmxlZnQsIHN0LCBcIkV4cHJlc3Npb25cIik7XG4gIGMobm9kZS5yaWdodCwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbn07XG5iYXNlLkNvbmRpdGlvbmFsRXhwcmVzc2lvbiA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBjKG5vZGUudGVzdCwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbiAgYyhub2RlLmNvbnNlcXVlbnQsIHN0LCBcIkV4cHJlc3Npb25cIik7XG4gIGMobm9kZS5hbHRlcm5hdGUsIHN0LCBcIkV4cHJlc3Npb25cIik7XG59O1xuYmFzZS5OZXdFeHByZXNzaW9uID0gYmFzZS5DYWxsRXhwcmVzc2lvbiA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBjKG5vZGUuY2FsbGVlLCBzdCwgXCJFeHByZXNzaW9uXCIpO1xuICBpZiAobm9kZS5hcmd1bWVudHMpIGZvciAodmFyIGkgPSAwOyBpIDwgbm9kZS5hcmd1bWVudHMubGVuZ3RoOyArK2kpIHtcbiAgICBjKG5vZGUuYXJndW1lbnRzW2ldLCBzdCwgXCJFeHByZXNzaW9uXCIpO1xuICB9XG59O1xuYmFzZS5NZW1iZXJFeHByZXNzaW9uID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIGMobm9kZS5vYmplY3QsIHN0LCBcIkV4cHJlc3Npb25cIik7XG4gIGlmIChub2RlLmNvbXB1dGVkKSBjKG5vZGUucHJvcGVydHksIHN0LCBcIkV4cHJlc3Npb25cIik7XG59O1xuYmFzZS5FeHBvcnROYW1lZERlY2xhcmF0aW9uID0gYmFzZS5FeHBvcnREZWZhdWx0RGVjbGFyYXRpb24gPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgcmV0dXJuIGMobm9kZS5kZWNsYXJhdGlvbiwgc3QpO1xufTtcbmJhc2UuSW1wb3J0RGVjbGFyYXRpb24gPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgZm9yICh2YXIgaSA9IDA7IGkgPCBub2RlLnNwZWNpZmllcnMubGVuZ3RoOyBpKyspIHtcbiAgICBjKG5vZGUuc3BlY2lmaWVyc1tpXSwgc3QpO1xuICB9XG59O1xuYmFzZS5JbXBvcnRTcGVjaWZpZXIgPSBiYXNlLkltcG9ydERlZmF1bHRTcGVjaWZpZXIgPSBiYXNlLkltcG9ydE5hbWVzcGFjZVNwZWNpZmllciA9IGJhc2UuSWRlbnRpZmllciA9IGJhc2UuTGl0ZXJhbCA9IGlnbm9yZTtcblxuYmFzZS5UYWdnZWRUZW1wbGF0ZUV4cHJlc3Npb24gPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgYyhub2RlLnRhZywgc3QsIFwiRXhwcmVzc2lvblwiKTtcbiAgYyhub2RlLnF1YXNpLCBzdCk7XG59O1xuYmFzZS5DbGFzc0RlY2xhcmF0aW9uID0gYmFzZS5DbGFzc0V4cHJlc3Npb24gPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgaWYgKG5vZGUuc3VwZXJDbGFzcykgYyhub2RlLnN1cGVyQ2xhc3MsIHN0LCBcIkV4cHJlc3Npb25cIik7XG4gIGZvciAodmFyIGkgPSAwOyBpIDwgbm9kZS5ib2R5LmJvZHkubGVuZ3RoOyBpKyspIHtcbiAgICBjKG5vZGUuYm9keS5ib2R5W2ldLCBzdCk7XG4gIH1cbn07XG5iYXNlLk1ldGhvZERlZmluaXRpb24gPSBiYXNlLlByb3BlcnR5ID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIGlmIChub2RlLmNvbXB1dGVkKSBjKG5vZGUua2V5LCBzdCwgXCJFeHByZXNzaW9uXCIpO1xuICBjKG5vZGUudmFsdWUsIHN0LCBcIkV4cHJlc3Npb25cIik7XG59O1xuYmFzZS5Db21wcmVoZW5zaW9uRXhwcmVzc2lvbiA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBmb3IgKHZhciBpID0gMDsgaSA8IG5vZGUuYmxvY2tzLmxlbmd0aDsgaSsrKSB7XG4gICAgYyhub2RlLmJsb2Nrc1tpXS5yaWdodCwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbiAgfWMobm9kZS5ib2R5LCBzdCwgXCJFeHByZXNzaW9uXCIpO1xufTtcblxufSx7fV19LHt9LFsxXSkoMSlcbn0pOyIsbnVsbCwiaWYgKHR5cGVvZiBPYmplY3QuY3JlYXRlID09PSAnZnVuY3Rpb24nKSB7XG4gIC8vIGltcGxlbWVudGF0aW9uIGZyb20gc3RhbmRhcmQgbm9kZS5qcyAndXRpbCcgbW9kdWxlXG4gIG1vZHVsZS5leHBvcnRzID0gZnVuY3Rpb24gaW5oZXJpdHMoY3Rvciwgc3VwZXJDdG9yKSB7XG4gICAgY3Rvci5zdXBlcl8gPSBzdXBlckN0b3JcbiAgICBjdG9yLnByb3RvdHlwZSA9IE9iamVjdC5jcmVhdGUoc3VwZXJDdG9yLnByb3RvdHlwZSwge1xuICAgICAgY29uc3RydWN0b3I6IHtcbiAgICAgICAgdmFsdWU6IGN0b3IsXG4gICAgICAgIGVudW1lcmFibGU6IGZhbHNlLFxuICAgICAgICB3cml0YWJsZTogdHJ1ZSxcbiAgICAgICAgY29uZmlndXJhYmxlOiB0cnVlXG4gICAgICB9XG4gICAgfSk7XG4gIH07XG59IGVsc2Uge1xuICAvLyBvbGQgc2Nob29sIHNoaW0gZm9yIG9sZCBicm93c2Vyc1xuICBtb2R1bGUuZXhwb3J0cyA9IGZ1bmN0aW9uIGluaGVyaXRzKGN0b3IsIHN1cGVyQ3Rvcikge1xuICAgIGN0b3Iuc3VwZXJfID0gc3VwZXJDdG9yXG4gICAgdmFyIFRlbXBDdG9yID0gZnVuY3Rpb24gKCkge31cbiAgICBUZW1wQ3Rvci5wcm90b3R5cGUgPSBzdXBlckN0b3IucHJvdG90eXBlXG4gICAgY3Rvci5wcm90b3R5cGUgPSBuZXcgVGVtcEN0b3IoKVxuICAgIGN0b3IucHJvdG90eXBlLmNvbnN0cnVjdG9yID0gY3RvclxuICB9XG59XG4iLCIvLyBzaGltIGZvciB1c2luZyBwcm9jZXNzIGluIGJyb3dzZXJcblxudmFyIHByb2Nlc3MgPSBtb2R1bGUuZXhwb3J0cyA9IHt9O1xudmFyIHF1ZXVlID0gW107XG52YXIgZHJhaW5pbmcgPSBmYWxzZTtcbnZhciBjdXJyZW50UXVldWU7XG52YXIgcXVldWVJbmRleCA9IC0xO1xuXG5mdW5jdGlvbiBjbGVhblVwTmV4dFRpY2soKSB7XG4gICAgZHJhaW5pbmcgPSBmYWxzZTtcbiAgICBpZiAoY3VycmVudFF1ZXVlLmxlbmd0aCkge1xuICAgICAgICBxdWV1ZSA9IGN1cnJlbnRRdWV1ZS5jb25jYXQocXVldWUpO1xuICAgIH0gZWxzZSB7XG4gICAgICAgIHF1ZXVlSW5kZXggPSAtMTtcbiAgICB9XG4gICAgaWYgKHF1ZXVlLmxlbmd0aCkge1xuICAgICAgICBkcmFpblF1ZXVlKCk7XG4gICAgfVxufVxuXG5mdW5jdGlvbiBkcmFpblF1ZXVlKCkge1xuICAgIGlmIChkcmFpbmluZykge1xuICAgICAgICByZXR1cm47XG4gICAgfVxuICAgIHZhciB0aW1lb3V0ID0gc2V0VGltZW91dChjbGVhblVwTmV4dFRpY2spO1xuICAgIGRyYWluaW5nID0gdHJ1ZTtcblxuICAgIHZhciBsZW4gPSBxdWV1ZS5sZW5ndGg7XG4gICAgd2hpbGUobGVuKSB7XG4gICAgICAgIGN1cnJlbnRRdWV1ZSA9IHF1ZXVlO1xuICAgICAgICBxdWV1ZSA9IFtdO1xuICAgICAgICB3aGlsZSAoKytxdWV1ZUluZGV4IDwgbGVuKSB7XG4gICAgICAgICAgICBjdXJyZW50UXVldWVbcXVldWVJbmRleF0ucnVuKCk7XG4gICAgICAgIH1cbiAgICAgICAgcXVldWVJbmRleCA9IC0xO1xuICAgICAgICBsZW4gPSBxdWV1ZS5sZW5ndGg7XG4gICAgfVxuICAgIGN1cnJlbnRRdWV1ZSA9IG51bGw7XG4gICAgZHJhaW5pbmcgPSBmYWxzZTtcbiAgICBjbGVhclRpbWVvdXQodGltZW91dCk7XG59XG5cbnByb2Nlc3MubmV4dFRpY2sgPSBmdW5jdGlvbiAoZnVuKSB7XG4gICAgdmFyIGFyZ3MgPSBuZXcgQXJyYXkoYXJndW1lbnRzLmxlbmd0aCAtIDEpO1xuICAgIGlmIChhcmd1bWVudHMubGVuZ3RoID4gMSkge1xuICAgICAgICBmb3IgKHZhciBpID0gMTsgaSA8IGFyZ3VtZW50cy5sZW5ndGg7IGkrKykge1xuICAgICAgICAgICAgYXJnc1tpIC0gMV0gPSBhcmd1bWVudHNbaV07XG4gICAgICAgIH1cbiAgICB9XG4gICAgcXVldWUucHVzaChuZXcgSXRlbShmdW4sIGFyZ3MpKTtcbiAgICBpZiAocXVldWUubGVuZ3RoID09PSAxICYmICFkcmFpbmluZykge1xuICAgICAgICBzZXRUaW1lb3V0KGRyYWluUXVldWUsIDApO1xuICAgIH1cbn07XG5cbi8vIHY4IGxpa2VzIHByZWRpY3RpYmxlIG9iamVjdHNcbmZ1bmN0aW9uIEl0ZW0oZnVuLCBhcnJheSkge1xuICAgIHRoaXMuZnVuID0gZnVuO1xuICAgIHRoaXMuYXJyYXkgPSBhcnJheTtcbn1cbkl0ZW0ucHJvdG90eXBlLnJ1biA9IGZ1bmN0aW9uICgpIHtcbiAgICB0aGlzLmZ1bi5hcHBseShudWxsLCB0aGlzLmFycmF5KTtcbn07XG5wcm9jZXNzLnRpdGxlID0gJ2Jyb3dzZXInO1xucHJvY2Vzcy5icm93c2VyID0gdHJ1ZTtcbnByb2Nlc3MuZW52ID0ge307XG5wcm9jZXNzLmFyZ3YgPSBbXTtcbnByb2Nlc3MudmVyc2lvbiA9ICcnOyAvLyBlbXB0eSBzdHJpbmcgdG8gYXZvaWQgcmVnZXhwIGlzc3Vlc1xucHJvY2Vzcy52ZXJzaW9ucyA9IHt9O1xuXG5mdW5jdGlvbiBub29wKCkge31cblxucHJvY2Vzcy5vbiA9IG5vb3A7XG5wcm9jZXNzLmFkZExpc3RlbmVyID0gbm9vcDtcbnByb2Nlc3Mub25jZSA9IG5vb3A7XG5wcm9jZXNzLm9mZiA9IG5vb3A7XG5wcm9jZXNzLnJlbW92ZUxpc3RlbmVyID0gbm9vcDtcbnByb2Nlc3MucmVtb3ZlQWxsTGlzdGVuZXJzID0gbm9vcDtcbnByb2Nlc3MuZW1pdCA9IG5vb3A7XG5cbnByb2Nlc3MuYmluZGluZyA9IGZ1bmN0aW9uIChuYW1lKSB7XG4gICAgdGhyb3cgbmV3IEVycm9yKCdwcm9jZXNzLmJpbmRpbmcgaXMgbm90IHN1cHBvcnRlZCcpO1xufTtcblxuLy8gVE9ETyhzaHR5bG1hbilcbnByb2Nlc3MuY3dkID0gZnVuY3Rpb24gKCkgeyByZXR1cm4gJy8nIH07XG5wcm9jZXNzLmNoZGlyID0gZnVuY3Rpb24gKGRpcikge1xuICAgIHRocm93IG5ldyBFcnJvcigncHJvY2Vzcy5jaGRpciBpcyBub3Qgc3VwcG9ydGVkJyk7XG59O1xucHJvY2Vzcy51bWFzayA9IGZ1bmN0aW9uKCkgeyByZXR1cm4gMDsgfTtcbiIsIm1vZHVsZS5leHBvcnRzID0gZnVuY3Rpb24gaXNCdWZmZXIoYXJnKSB7XG4gIHJldHVybiBhcmcgJiYgdHlwZW9mIGFyZyA9PT0gJ29iamVjdCdcbiAgICAmJiB0eXBlb2YgYXJnLmNvcHkgPT09ICdmdW5jdGlvbidcbiAgICAmJiB0eXBlb2YgYXJnLmZpbGwgPT09ICdmdW5jdGlvbidcbiAgICAmJiB0eXBlb2YgYXJnLnJlYWRVSW50OCA9PT0gJ2Z1bmN0aW9uJztcbn0iLCIvLyBDb3B5cmlnaHQgSm95ZW50LCBJbmMuIGFuZCBvdGhlciBOb2RlIGNvbnRyaWJ1dG9ycy5cbi8vXG4vLyBQZXJtaXNzaW9uIGlzIGhlcmVieSBncmFudGVkLCBmcmVlIG9mIGNoYXJnZSwgdG8gYW55IHBlcnNvbiBvYnRhaW5pbmcgYVxuLy8gY29weSBvZiB0aGlzIHNvZnR3YXJlIGFuZCBhc3NvY2lhdGVkIGRvY3VtZW50YXRpb24gZmlsZXMgKHRoZVxuLy8gXCJTb2Z0d2FyZVwiKSwgdG8gZGVhbCBpbiB0aGUgU29mdHdhcmUgd2l0aG91dCByZXN0cmljdGlvbiwgaW5jbHVkaW5nXG4vLyB3aXRob3V0IGxpbWl0YXRpb24gdGhlIHJpZ2h0cyB0byB1c2UsIGNvcHksIG1vZGlmeSwgbWVyZ2UsIHB1Ymxpc2gsXG4vLyBkaXN0cmlidXRlLCBzdWJsaWNlbnNlLCBhbmQvb3Igc2VsbCBjb3BpZXMgb2YgdGhlIFNvZnR3YXJlLCBhbmQgdG8gcGVybWl0XG4vLyBwZXJzb25zIHRvIHdob20gdGhlIFNvZnR3YXJlIGlzIGZ1cm5pc2hlZCB0byBkbyBzbywgc3ViamVjdCB0byB0aGVcbi8vIGZvbGxvd2luZyBjb25kaXRpb25zOlxuLy9cbi8vIFRoZSBhYm92ZSBjb3B5cmlnaHQgbm90aWNlIGFuZCB0aGlzIHBlcm1pc3Npb24gbm90aWNlIHNoYWxsIGJlIGluY2x1ZGVkXG4vLyBpbiBhbGwgY29waWVzIG9yIHN1YnN0YW50aWFsIHBvcnRpb25zIG9mIHRoZSBTb2Z0d2FyZS5cbi8vXG4vLyBUSEUgU09GVFdBUkUgSVMgUFJPVklERUQgXCJBUyBJU1wiLCBXSVRIT1VUIFdBUlJBTlRZIE9GIEFOWSBLSU5ELCBFWFBSRVNTXG4vLyBPUiBJTVBMSUVELCBJTkNMVURJTkcgQlVUIE5PVCBMSU1JVEVEIFRPIFRIRSBXQVJSQU5USUVTIE9GXG4vLyBNRVJDSEFOVEFCSUxJVFksIEZJVE5FU1MgRk9SIEEgUEFSVElDVUxBUiBQVVJQT1NFIEFORCBOT05JTkZSSU5HRU1FTlQuIElOXG4vLyBOTyBFVkVOVCBTSEFMTCBUSEUgQVVUSE9SUyBPUiBDT1BZUklHSFQgSE9MREVSUyBCRSBMSUFCTEUgRk9SIEFOWSBDTEFJTSxcbi8vIERBTUFHRVMgT1IgT1RIRVIgTElBQklMSVRZLCBXSEVUSEVSIElOIEFOIEFDVElPTiBPRiBDT05UUkFDVCwgVE9SVCBPUlxuLy8gT1RIRVJXSVNFLCBBUklTSU5HIEZST00sIE9VVCBPRiBPUiBJTiBDT05ORUNUSU9OIFdJVEggVEhFIFNPRlRXQVJFIE9SIFRIRVxuLy8gVVNFIE9SIE9USEVSIERFQUxJTkdTIElOIFRIRSBTT0ZUV0FSRS5cblxudmFyIGZvcm1hdFJlZ0V4cCA9IC8lW3NkaiVdL2c7XG5leHBvcnRzLmZvcm1hdCA9IGZ1bmN0aW9uKGYpIHtcbiAgaWYgKCFpc1N0cmluZyhmKSkge1xuICAgIHZhciBvYmplY3RzID0gW107XG4gICAgZm9yICh2YXIgaSA9IDA7IGkgPCBhcmd1bWVudHMubGVuZ3RoOyBpKyspIHtcbiAgICAgIG9iamVjdHMucHVzaChpbnNwZWN0KGFyZ3VtZW50c1tpXSkpO1xuICAgIH1cbiAgICByZXR1cm4gb2JqZWN0cy5qb2luKCcgJyk7XG4gIH1cblxuICB2YXIgaSA9IDE7XG4gIHZhciBhcmdzID0gYXJndW1lbnRzO1xuICB2YXIgbGVuID0gYXJncy5sZW5ndGg7XG4gIHZhciBzdHIgPSBTdHJpbmcoZikucmVwbGFjZShmb3JtYXRSZWdFeHAsIGZ1bmN0aW9uKHgpIHtcbiAgICBpZiAoeCA9PT0gJyUlJykgcmV0dXJuICclJztcbiAgICBpZiAoaSA+PSBsZW4pIHJldHVybiB4O1xuICAgIHN3aXRjaCAoeCkge1xuICAgICAgY2FzZSAnJXMnOiByZXR1cm4gU3RyaW5nKGFyZ3NbaSsrXSk7XG4gICAgICBjYXNlICclZCc6IHJldHVybiBOdW1iZXIoYXJnc1tpKytdKTtcbiAgICAgIGNhc2UgJyVqJzpcbiAgICAgICAgdHJ5IHtcbiAgICAgICAgICByZXR1cm4gSlNPTi5zdHJpbmdpZnkoYXJnc1tpKytdKTtcbiAgICAgICAgfSBjYXRjaCAoXykge1xuICAgICAgICAgIHJldHVybiAnW0NpcmN1bGFyXSc7XG4gICAgICAgIH1cbiAgICAgIGRlZmF1bHQ6XG4gICAgICAgIHJldHVybiB4O1xuICAgIH1cbiAgfSk7XG4gIGZvciAodmFyIHggPSBhcmdzW2ldOyBpIDwgbGVuOyB4ID0gYXJnc1srK2ldKSB7XG4gICAgaWYgKGlzTnVsbCh4KSB8fCAhaXNPYmplY3QoeCkpIHtcbiAgICAgIHN0ciArPSAnICcgKyB4O1xuICAgIH0gZWxzZSB7XG4gICAgICBzdHIgKz0gJyAnICsgaW5zcGVjdCh4KTtcbiAgICB9XG4gIH1cbiAgcmV0dXJuIHN0cjtcbn07XG5cblxuLy8gTWFyayB0aGF0IGEgbWV0aG9kIHNob3VsZCBub3QgYmUgdXNlZC5cbi8vIFJldHVybnMgYSBtb2RpZmllZCBmdW5jdGlvbiB3aGljaCB3YXJucyBvbmNlIGJ5IGRlZmF1bHQuXG4vLyBJZiAtLW5vLWRlcHJlY2F0aW9uIGlzIHNldCwgdGhlbiBpdCBpcyBhIG5vLW9wLlxuZXhwb3J0cy5kZXByZWNhdGUgPSBmdW5jdGlvbihmbiwgbXNnKSB7XG4gIC8vIEFsbG93IGZvciBkZXByZWNhdGluZyB0aGluZ3MgaW4gdGhlIHByb2Nlc3Mgb2Ygc3RhcnRpbmcgdXAuXG4gIGlmIChpc1VuZGVmaW5lZChnbG9iYWwucHJvY2VzcykpIHtcbiAgICByZXR1cm4gZnVuY3Rpb24oKSB7XG4gICAgICByZXR1cm4gZXhwb3J0cy5kZXByZWNhdGUoZm4sIG1zZykuYXBwbHkodGhpcywgYXJndW1lbnRzKTtcbiAgICB9O1xuICB9XG5cbiAgaWYgKHByb2Nlc3Mubm9EZXByZWNhdGlvbiA9PT0gdHJ1ZSkge1xuICAgIHJldHVybiBmbjtcbiAgfVxuXG4gIHZhciB3YXJuZWQgPSBmYWxzZTtcbiAgZnVuY3Rpb24gZGVwcmVjYXRlZCgpIHtcbiAgICBpZiAoIXdhcm5lZCkge1xuICAgICAgaWYgKHByb2Nlc3MudGhyb3dEZXByZWNhdGlvbikge1xuICAgICAgICB0aHJvdyBuZXcgRXJyb3IobXNnKTtcbiAgICAgIH0gZWxzZSBpZiAocHJvY2Vzcy50cmFjZURlcHJlY2F0aW9uKSB7XG4gICAgICAgIGNvbnNvbGUudHJhY2UobXNnKTtcbiAgICAgIH0gZWxzZSB7XG4gICAgICAgIGNvbnNvbGUuZXJyb3IobXNnKTtcbiAgICAgIH1cbiAgICAgIHdhcm5lZCA9IHRydWU7XG4gICAgfVxuICAgIHJldHVybiBmbi5hcHBseSh0aGlzLCBhcmd1bWVudHMpO1xuICB9XG5cbiAgcmV0dXJuIGRlcHJlY2F0ZWQ7XG59O1xuXG5cbnZhciBkZWJ1Z3MgPSB7fTtcbnZhciBkZWJ1Z0Vudmlyb247XG5leHBvcnRzLmRlYnVnbG9nID0gZnVuY3Rpb24oc2V0KSB7XG4gIGlmIChpc1VuZGVmaW5lZChkZWJ1Z0Vudmlyb24pKVxuICAgIGRlYnVnRW52aXJvbiA9IHByb2Nlc3MuZW52Lk5PREVfREVCVUcgfHwgJyc7XG4gIHNldCA9IHNldC50b1VwcGVyQ2FzZSgpO1xuICBpZiAoIWRlYnVnc1tzZXRdKSB7XG4gICAgaWYgKG5ldyBSZWdFeHAoJ1xcXFxiJyArIHNldCArICdcXFxcYicsICdpJykudGVzdChkZWJ1Z0Vudmlyb24pKSB7XG4gICAgICB2YXIgcGlkID0gcHJvY2Vzcy5waWQ7XG4gICAgICBkZWJ1Z3Nbc2V0XSA9IGZ1bmN0aW9uKCkge1xuICAgICAgICB2YXIgbXNnID0gZXhwb3J0cy5mb3JtYXQuYXBwbHkoZXhwb3J0cywgYXJndW1lbnRzKTtcbiAgICAgICAgY29uc29sZS5lcnJvcignJXMgJWQ6ICVzJywgc2V0LCBwaWQsIG1zZyk7XG4gICAgICB9O1xuICAgIH0gZWxzZSB7XG4gICAgICBkZWJ1Z3Nbc2V0XSA9IGZ1bmN0aW9uKCkge307XG4gICAgfVxuICB9XG4gIHJldHVybiBkZWJ1Z3Nbc2V0XTtcbn07XG5cblxuLyoqXG4gKiBFY2hvcyB0aGUgdmFsdWUgb2YgYSB2YWx1ZS4gVHJ5cyB0byBwcmludCB0aGUgdmFsdWUgb3V0XG4gKiBpbiB0aGUgYmVzdCB3YXkgcG9zc2libGUgZ2l2ZW4gdGhlIGRpZmZlcmVudCB0eXBlcy5cbiAqXG4gKiBAcGFyYW0ge09iamVjdH0gb2JqIFRoZSBvYmplY3QgdG8gcHJpbnQgb3V0LlxuICogQHBhcmFtIHtPYmplY3R9IG9wdHMgT3B0aW9uYWwgb3B0aW9ucyBvYmplY3QgdGhhdCBhbHRlcnMgdGhlIG91dHB1dC5cbiAqL1xuLyogbGVnYWN5OiBvYmosIHNob3dIaWRkZW4sIGRlcHRoLCBjb2xvcnMqL1xuZnVuY3Rpb24gaW5zcGVjdChvYmosIG9wdHMpIHtcbiAgLy8gZGVmYXVsdCBvcHRpb25zXG4gIHZhciBjdHggPSB7XG4gICAgc2VlbjogW10sXG4gICAgc3R5bGl6ZTogc3R5bGl6ZU5vQ29sb3JcbiAgfTtcbiAgLy8gbGVnYWN5Li4uXG4gIGlmIChhcmd1bWVudHMubGVuZ3RoID49IDMpIGN0eC5kZXB0aCA9IGFyZ3VtZW50c1syXTtcbiAgaWYgKGFyZ3VtZW50cy5sZW5ndGggPj0gNCkgY3R4LmNvbG9ycyA9IGFyZ3VtZW50c1szXTtcbiAgaWYgKGlzQm9vbGVhbihvcHRzKSkge1xuICAgIC8vIGxlZ2FjeS4uLlxuICAgIGN0eC5zaG93SGlkZGVuID0gb3B0cztcbiAgfSBlbHNlIGlmIChvcHRzKSB7XG4gICAgLy8gZ290IGFuIFwib3B0aW9uc1wiIG9iamVjdFxuICAgIGV4cG9ydHMuX2V4dGVuZChjdHgsIG9wdHMpO1xuICB9XG4gIC8vIHNldCBkZWZhdWx0IG9wdGlvbnNcbiAgaWYgKGlzVW5kZWZpbmVkKGN0eC5zaG93SGlkZGVuKSkgY3R4LnNob3dIaWRkZW4gPSBmYWxzZTtcbiAgaWYgKGlzVW5kZWZpbmVkKGN0eC5kZXB0aCkpIGN0eC5kZXB0aCA9IDI7XG4gIGlmIChpc1VuZGVmaW5lZChjdHguY29sb3JzKSkgY3R4LmNvbG9ycyA9IGZhbHNlO1xuICBpZiAoaXNVbmRlZmluZWQoY3R4LmN1c3RvbUluc3BlY3QpKSBjdHguY3VzdG9tSW5zcGVjdCA9IHRydWU7XG4gIGlmIChjdHguY29sb3JzKSBjdHguc3R5bGl6ZSA9IHN0eWxpemVXaXRoQ29sb3I7XG4gIHJldHVybiBmb3JtYXRWYWx1ZShjdHgsIG9iaiwgY3R4LmRlcHRoKTtcbn1cbmV4cG9ydHMuaW5zcGVjdCA9IGluc3BlY3Q7XG5cblxuLy8gaHR0cDovL2VuLndpa2lwZWRpYS5vcmcvd2lraS9BTlNJX2VzY2FwZV9jb2RlI2dyYXBoaWNzXG5pbnNwZWN0LmNvbG9ycyA9IHtcbiAgJ2JvbGQnIDogWzEsIDIyXSxcbiAgJ2l0YWxpYycgOiBbMywgMjNdLFxuICAndW5kZXJsaW5lJyA6IFs0LCAyNF0sXG4gICdpbnZlcnNlJyA6IFs3LCAyN10sXG4gICd3aGl0ZScgOiBbMzcsIDM5XSxcbiAgJ2dyZXknIDogWzkwLCAzOV0sXG4gICdibGFjaycgOiBbMzAsIDM5XSxcbiAgJ2JsdWUnIDogWzM0LCAzOV0sXG4gICdjeWFuJyA6IFszNiwgMzldLFxuICAnZ3JlZW4nIDogWzMyLCAzOV0sXG4gICdtYWdlbnRhJyA6IFszNSwgMzldLFxuICAncmVkJyA6IFszMSwgMzldLFxuICAneWVsbG93JyA6IFszMywgMzldXG59O1xuXG4vLyBEb24ndCB1c2UgJ2JsdWUnIG5vdCB2aXNpYmxlIG9uIGNtZC5leGVcbmluc3BlY3Quc3R5bGVzID0ge1xuICAnc3BlY2lhbCc6ICdjeWFuJyxcbiAgJ251bWJlcic6ICd5ZWxsb3cnLFxuICAnYm9vbGVhbic6ICd5ZWxsb3cnLFxuICAndW5kZWZpbmVkJzogJ2dyZXknLFxuICAnbnVsbCc6ICdib2xkJyxcbiAgJ3N0cmluZyc6ICdncmVlbicsXG4gICdkYXRlJzogJ21hZ2VudGEnLFxuICAvLyBcIm5hbWVcIjogaW50ZW50aW9uYWxseSBub3Qgc3R5bGluZ1xuICAncmVnZXhwJzogJ3JlZCdcbn07XG5cblxuZnVuY3Rpb24gc3R5bGl6ZVdpdGhDb2xvcihzdHIsIHN0eWxlVHlwZSkge1xuICB2YXIgc3R5bGUgPSBpbnNwZWN0LnN0eWxlc1tzdHlsZVR5cGVdO1xuXG4gIGlmIChzdHlsZSkge1xuICAgIHJldHVybiAnXFx1MDAxYlsnICsgaW5zcGVjdC5jb2xvcnNbc3R5bGVdWzBdICsgJ20nICsgc3RyICtcbiAgICAgICAgICAgJ1xcdTAwMWJbJyArIGluc3BlY3QuY29sb3JzW3N0eWxlXVsxXSArICdtJztcbiAgfSBlbHNlIHtcbiAgICByZXR1cm4gc3RyO1xuICB9XG59XG5cblxuZnVuY3Rpb24gc3R5bGl6ZU5vQ29sb3Ioc3RyLCBzdHlsZVR5cGUpIHtcbiAgcmV0dXJuIHN0cjtcbn1cblxuXG5mdW5jdGlvbiBhcnJheVRvSGFzaChhcnJheSkge1xuICB2YXIgaGFzaCA9IHt9O1xuXG4gIGFycmF5LmZvckVhY2goZnVuY3Rpb24odmFsLCBpZHgpIHtcbiAgICBoYXNoW3ZhbF0gPSB0cnVlO1xuICB9KTtcblxuICByZXR1cm4gaGFzaDtcbn1cblxuXG5mdW5jdGlvbiBmb3JtYXRWYWx1ZShjdHgsIHZhbHVlLCByZWN1cnNlVGltZXMpIHtcbiAgLy8gUHJvdmlkZSBhIGhvb2sgZm9yIHVzZXItc3BlY2lmaWVkIGluc3BlY3QgZnVuY3Rpb25zLlxuICAvLyBDaGVjayB0aGF0IHZhbHVlIGlzIGFuIG9iamVjdCB3aXRoIGFuIGluc3BlY3QgZnVuY3Rpb24gb24gaXRcbiAgaWYgKGN0eC5jdXN0b21JbnNwZWN0ICYmXG4gICAgICB2YWx1ZSAmJlxuICAgICAgaXNGdW5jdGlvbih2YWx1ZS5pbnNwZWN0KSAmJlxuICAgICAgLy8gRmlsdGVyIG91dCB0aGUgdXRpbCBtb2R1bGUsIGl0J3MgaW5zcGVjdCBmdW5jdGlvbiBpcyBzcGVjaWFsXG4gICAgICB2YWx1ZS5pbnNwZWN0ICE9PSBleHBvcnRzLmluc3BlY3QgJiZcbiAgICAgIC8vIEFsc28gZmlsdGVyIG91dCBhbnkgcHJvdG90eXBlIG9iamVjdHMgdXNpbmcgdGhlIGNpcmN1bGFyIGNoZWNrLlxuICAgICAgISh2YWx1ZS5jb25zdHJ1Y3RvciAmJiB2YWx1ZS5jb25zdHJ1Y3Rvci5wcm90b3R5cGUgPT09IHZhbHVlKSkge1xuICAgIHZhciByZXQgPSB2YWx1ZS5pbnNwZWN0KHJlY3Vyc2VUaW1lcywgY3R4KTtcbiAgICBpZiAoIWlzU3RyaW5nKHJldCkpIHtcbiAgICAgIHJldCA9IGZvcm1hdFZhbHVlKGN0eCwgcmV0LCByZWN1cnNlVGltZXMpO1xuICAgIH1cbiAgICByZXR1cm4gcmV0O1xuICB9XG5cbiAgLy8gUHJpbWl0aXZlIHR5cGVzIGNhbm5vdCBoYXZlIHByb3BlcnRpZXNcbiAgdmFyIHByaW1pdGl2ZSA9IGZvcm1hdFByaW1pdGl2ZShjdHgsIHZhbHVlKTtcbiAgaWYgKHByaW1pdGl2ZSkge1xuICAgIHJldHVybiBwcmltaXRpdmU7XG4gIH1cblxuICAvLyBMb29rIHVwIHRoZSBrZXlzIG9mIHRoZSBvYmplY3QuXG4gIHZhciBrZXlzID0gT2JqZWN0LmtleXModmFsdWUpO1xuICB2YXIgdmlzaWJsZUtleXMgPSBhcnJheVRvSGFzaChrZXlzKTtcblxuICBpZiAoY3R4LnNob3dIaWRkZW4pIHtcbiAgICBrZXlzID0gT2JqZWN0LmdldE93blByb3BlcnR5TmFtZXModmFsdWUpO1xuICB9XG5cbiAgLy8gSUUgZG9lc24ndCBtYWtlIGVycm9yIGZpZWxkcyBub24tZW51bWVyYWJsZVxuICAvLyBodHRwOi8vbXNkbi5taWNyb3NvZnQuY29tL2VuLXVzL2xpYnJhcnkvaWUvZHd3NTJzYnQodj12cy45NCkuYXNweFxuICBpZiAoaXNFcnJvcih2YWx1ZSlcbiAgICAgICYmIChrZXlzLmluZGV4T2YoJ21lc3NhZ2UnKSA+PSAwIHx8IGtleXMuaW5kZXhPZignZGVzY3JpcHRpb24nKSA+PSAwKSkge1xuICAgIHJldHVybiBmb3JtYXRFcnJvcih2YWx1ZSk7XG4gIH1cblxuICAvLyBTb21lIHR5cGUgb2Ygb2JqZWN0IHdpdGhvdXQgcHJvcGVydGllcyBjYW4gYmUgc2hvcnRjdXR0ZWQuXG4gIGlmIChrZXlzLmxlbmd0aCA9PT0gMCkge1xuICAgIGlmIChpc0Z1bmN0aW9uKHZhbHVlKSkge1xuICAgICAgdmFyIG5hbWUgPSB2YWx1ZS5uYW1lID8gJzogJyArIHZhbHVlLm5hbWUgOiAnJztcbiAgICAgIHJldHVybiBjdHguc3R5bGl6ZSgnW0Z1bmN0aW9uJyArIG5hbWUgKyAnXScsICdzcGVjaWFsJyk7XG4gICAgfVxuICAgIGlmIChpc1JlZ0V4cCh2YWx1ZSkpIHtcbiAgICAgIHJldHVybiBjdHguc3R5bGl6ZShSZWdFeHAucHJvdG90eXBlLnRvU3RyaW5nLmNhbGwodmFsdWUpLCAncmVnZXhwJyk7XG4gICAgfVxuICAgIGlmIChpc0RhdGUodmFsdWUpKSB7XG4gICAgICByZXR1cm4gY3R4LnN0eWxpemUoRGF0ZS5wcm90b3R5cGUudG9TdHJpbmcuY2FsbCh2YWx1ZSksICdkYXRlJyk7XG4gICAgfVxuICAgIGlmIChpc0Vycm9yKHZhbHVlKSkge1xuICAgICAgcmV0dXJuIGZvcm1hdEVycm9yKHZhbHVlKTtcbiAgICB9XG4gIH1cblxuICB2YXIgYmFzZSA9ICcnLCBhcnJheSA9IGZhbHNlLCBicmFjZXMgPSBbJ3snLCAnfSddO1xuXG4gIC8vIE1ha2UgQXJyYXkgc2F5IHRoYXQgdGhleSBhcmUgQXJyYXlcbiAgaWYgKGlzQXJyYXkodmFsdWUpKSB7XG4gICAgYXJyYXkgPSB0cnVlO1xuICAgIGJyYWNlcyA9IFsnWycsICddJ107XG4gIH1cblxuICAvLyBNYWtlIGZ1bmN0aW9ucyBzYXkgdGhhdCB0aGV5IGFyZSBmdW5jdGlvbnNcbiAgaWYgKGlzRnVuY3Rpb24odmFsdWUpKSB7XG4gICAgdmFyIG4gPSB2YWx1ZS5uYW1lID8gJzogJyArIHZhbHVlLm5hbWUgOiAnJztcbiAgICBiYXNlID0gJyBbRnVuY3Rpb24nICsgbiArICddJztcbiAgfVxuXG4gIC8vIE1ha2UgUmVnRXhwcyBzYXkgdGhhdCB0aGV5IGFyZSBSZWdFeHBzXG4gIGlmIChpc1JlZ0V4cCh2YWx1ZSkpIHtcbiAgICBiYXNlID0gJyAnICsgUmVnRXhwLnByb3RvdHlwZS50b1N0cmluZy5jYWxsKHZhbHVlKTtcbiAgfVxuXG4gIC8vIE1ha2UgZGF0ZXMgd2l0aCBwcm9wZXJ0aWVzIGZpcnN0IHNheSB0aGUgZGF0ZVxuICBpZiAoaXNEYXRlKHZhbHVlKSkge1xuICAgIGJhc2UgPSAnICcgKyBEYXRlLnByb3RvdHlwZS50b1VUQ1N0cmluZy5jYWxsKHZhbHVlKTtcbiAgfVxuXG4gIC8vIE1ha2UgZXJyb3Igd2l0aCBtZXNzYWdlIGZpcnN0IHNheSB0aGUgZXJyb3JcbiAgaWYgKGlzRXJyb3IodmFsdWUpKSB7XG4gICAgYmFzZSA9ICcgJyArIGZvcm1hdEVycm9yKHZhbHVlKTtcbiAgfVxuXG4gIGlmIChrZXlzLmxlbmd0aCA9PT0gMCAmJiAoIWFycmF5IHx8IHZhbHVlLmxlbmd0aCA9PSAwKSkge1xuICAgIHJldHVybiBicmFjZXNbMF0gKyBiYXNlICsgYnJhY2VzWzFdO1xuICB9XG5cbiAgaWYgKHJlY3Vyc2VUaW1lcyA8IDApIHtcbiAgICBpZiAoaXNSZWdFeHAodmFsdWUpKSB7XG4gICAgICByZXR1cm4gY3R4LnN0eWxpemUoUmVnRXhwLnByb3RvdHlwZS50b1N0cmluZy5jYWxsKHZhbHVlKSwgJ3JlZ2V4cCcpO1xuICAgIH0gZWxzZSB7XG4gICAgICByZXR1cm4gY3R4LnN0eWxpemUoJ1tPYmplY3RdJywgJ3NwZWNpYWwnKTtcbiAgICB9XG4gIH1cblxuICBjdHguc2Vlbi5wdXNoKHZhbHVlKTtcblxuICB2YXIgb3V0cHV0O1xuICBpZiAoYXJyYXkpIHtcbiAgICBvdXRwdXQgPSBmb3JtYXRBcnJheShjdHgsIHZhbHVlLCByZWN1cnNlVGltZXMsIHZpc2libGVLZXlzLCBrZXlzKTtcbiAgfSBlbHNlIHtcbiAgICBvdXRwdXQgPSBrZXlzLm1hcChmdW5jdGlvbihrZXkpIHtcbiAgICAgIHJldHVybiBmb3JtYXRQcm9wZXJ0eShjdHgsIHZhbHVlLCByZWN1cnNlVGltZXMsIHZpc2libGVLZXlzLCBrZXksIGFycmF5KTtcbiAgICB9KTtcbiAgfVxuXG4gIGN0eC5zZWVuLnBvcCgpO1xuXG4gIHJldHVybiByZWR1Y2VUb1NpbmdsZVN0cmluZyhvdXRwdXQsIGJhc2UsIGJyYWNlcyk7XG59XG5cblxuZnVuY3Rpb24gZm9ybWF0UHJpbWl0aXZlKGN0eCwgdmFsdWUpIHtcbiAgaWYgKGlzVW5kZWZpbmVkKHZhbHVlKSlcbiAgICByZXR1cm4gY3R4LnN0eWxpemUoJ3VuZGVmaW5lZCcsICd1bmRlZmluZWQnKTtcbiAgaWYgKGlzU3RyaW5nKHZhbHVlKSkge1xuICAgIHZhciBzaW1wbGUgPSAnXFwnJyArIEpTT04uc3RyaW5naWZ5KHZhbHVlKS5yZXBsYWNlKC9eXCJ8XCIkL2csICcnKVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgLnJlcGxhY2UoLycvZywgXCJcXFxcJ1wiKVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgLnJlcGxhY2UoL1xcXFxcIi9nLCAnXCInKSArICdcXCcnO1xuICAgIHJldHVybiBjdHguc3R5bGl6ZShzaW1wbGUsICdzdHJpbmcnKTtcbiAgfVxuICBpZiAoaXNOdW1iZXIodmFsdWUpKVxuICAgIHJldHVybiBjdHguc3R5bGl6ZSgnJyArIHZhbHVlLCAnbnVtYmVyJyk7XG4gIGlmIChpc0Jvb2xlYW4odmFsdWUpKVxuICAgIHJldHVybiBjdHguc3R5bGl6ZSgnJyArIHZhbHVlLCAnYm9vbGVhbicpO1xuICAvLyBGb3Igc29tZSByZWFzb24gdHlwZW9mIG51bGwgaXMgXCJvYmplY3RcIiwgc28gc3BlY2lhbCBjYXNlIGhlcmUuXG4gIGlmIChpc051bGwodmFsdWUpKVxuICAgIHJldHVybiBjdHguc3R5bGl6ZSgnbnVsbCcsICdudWxsJyk7XG59XG5cblxuZnVuY3Rpb24gZm9ybWF0RXJyb3IodmFsdWUpIHtcbiAgcmV0dXJuICdbJyArIEVycm9yLnByb3RvdHlwZS50b1N0cmluZy5jYWxsKHZhbHVlKSArICddJztcbn1cblxuXG5mdW5jdGlvbiBmb3JtYXRBcnJheShjdHgsIHZhbHVlLCByZWN1cnNlVGltZXMsIHZpc2libGVLZXlzLCBrZXlzKSB7XG4gIHZhciBvdXRwdXQgPSBbXTtcbiAgZm9yICh2YXIgaSA9IDAsIGwgPSB2YWx1ZS5sZW5ndGg7IGkgPCBsOyArK2kpIHtcbiAgICBpZiAoaGFzT3duUHJvcGVydHkodmFsdWUsIFN0cmluZyhpKSkpIHtcbiAgICAgIG91dHB1dC5wdXNoKGZvcm1hdFByb3BlcnR5KGN0eCwgdmFsdWUsIHJlY3Vyc2VUaW1lcywgdmlzaWJsZUtleXMsXG4gICAgICAgICAgU3RyaW5nKGkpLCB0cnVlKSk7XG4gICAgfSBlbHNlIHtcbiAgICAgIG91dHB1dC5wdXNoKCcnKTtcbiAgICB9XG4gIH1cbiAga2V5cy5mb3JFYWNoKGZ1bmN0aW9uKGtleSkge1xuICAgIGlmICgha2V5Lm1hdGNoKC9eXFxkKyQvKSkge1xuICAgICAgb3V0cHV0LnB1c2goZm9ybWF0UHJvcGVydHkoY3R4LCB2YWx1ZSwgcmVjdXJzZVRpbWVzLCB2aXNpYmxlS2V5cyxcbiAgICAgICAgICBrZXksIHRydWUpKTtcbiAgICB9XG4gIH0pO1xuICByZXR1cm4gb3V0cHV0O1xufVxuXG5cbmZ1bmN0aW9uIGZvcm1hdFByb3BlcnR5KGN0eCwgdmFsdWUsIHJlY3Vyc2VUaW1lcywgdmlzaWJsZUtleXMsIGtleSwgYXJyYXkpIHtcbiAgdmFyIG5hbWUsIHN0ciwgZGVzYztcbiAgZGVzYyA9IE9iamVjdC5nZXRPd25Qcm9wZXJ0eURlc2NyaXB0b3IodmFsdWUsIGtleSkgfHwgeyB2YWx1ZTogdmFsdWVba2V5XSB9O1xuICBpZiAoZGVzYy5nZXQpIHtcbiAgICBpZiAoZGVzYy5zZXQpIHtcbiAgICAgIHN0ciA9IGN0eC5zdHlsaXplKCdbR2V0dGVyL1NldHRlcl0nLCAnc3BlY2lhbCcpO1xuICAgIH0gZWxzZSB7XG4gICAgICBzdHIgPSBjdHguc3R5bGl6ZSgnW0dldHRlcl0nLCAnc3BlY2lhbCcpO1xuICAgIH1cbiAgfSBlbHNlIHtcbiAgICBpZiAoZGVzYy5zZXQpIHtcbiAgICAgIHN0ciA9IGN0eC5zdHlsaXplKCdbU2V0dGVyXScsICdzcGVjaWFsJyk7XG4gICAgfVxuICB9XG4gIGlmICghaGFzT3duUHJvcGVydHkodmlzaWJsZUtleXMsIGtleSkpIHtcbiAgICBuYW1lID0gJ1snICsga2V5ICsgJ10nO1xuICB9XG4gIGlmICghc3RyKSB7XG4gICAgaWYgKGN0eC5zZWVuLmluZGV4T2YoZGVzYy52YWx1ZSkgPCAwKSB7XG4gICAgICBpZiAoaXNOdWxsKHJlY3Vyc2VUaW1lcykpIHtcbiAgICAgICAgc3RyID0gZm9ybWF0VmFsdWUoY3R4LCBkZXNjLnZhbHVlLCBudWxsKTtcbiAgICAgIH0gZWxzZSB7XG4gICAgICAgIHN0ciA9IGZvcm1hdFZhbHVlKGN0eCwgZGVzYy52YWx1ZSwgcmVjdXJzZVRpbWVzIC0gMSk7XG4gICAgICB9XG4gICAgICBpZiAoc3RyLmluZGV4T2YoJ1xcbicpID4gLTEpIHtcbiAgICAgICAgaWYgKGFycmF5KSB7XG4gICAgICAgICAgc3RyID0gc3RyLnNwbGl0KCdcXG4nKS5tYXAoZnVuY3Rpb24obGluZSkge1xuICAgICAgICAgICAgcmV0dXJuICcgICcgKyBsaW5lO1xuICAgICAgICAgIH0pLmpvaW4oJ1xcbicpLnN1YnN0cigyKTtcbiAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICBzdHIgPSAnXFxuJyArIHN0ci5zcGxpdCgnXFxuJykubWFwKGZ1bmN0aW9uKGxpbmUpIHtcbiAgICAgICAgICAgIHJldHVybiAnICAgJyArIGxpbmU7XG4gICAgICAgICAgfSkuam9pbignXFxuJyk7XG4gICAgICAgIH1cbiAgICAgIH1cbiAgICB9IGVsc2Uge1xuICAgICAgc3RyID0gY3R4LnN0eWxpemUoJ1tDaXJjdWxhcl0nLCAnc3BlY2lhbCcpO1xuICAgIH1cbiAgfVxuICBpZiAoaXNVbmRlZmluZWQobmFtZSkpIHtcbiAgICBpZiAoYXJyYXkgJiYga2V5Lm1hdGNoKC9eXFxkKyQvKSkge1xuICAgICAgcmV0dXJuIHN0cjtcbiAgICB9XG4gICAgbmFtZSA9IEpTT04uc3RyaW5naWZ5KCcnICsga2V5KTtcbiAgICBpZiAobmFtZS5tYXRjaCgvXlwiKFthLXpBLVpfXVthLXpBLVpfMC05XSopXCIkLykpIHtcbiAgICAgIG5hbWUgPSBuYW1lLnN1YnN0cigxLCBuYW1lLmxlbmd0aCAtIDIpO1xuICAgICAgbmFtZSA9IGN0eC5zdHlsaXplKG5hbWUsICduYW1lJyk7XG4gICAgfSBlbHNlIHtcbiAgICAgIG5hbWUgPSBuYW1lLnJlcGxhY2UoLycvZywgXCJcXFxcJ1wiKVxuICAgICAgICAgICAgICAgICAucmVwbGFjZSgvXFxcXFwiL2csICdcIicpXG4gICAgICAgICAgICAgICAgIC5yZXBsYWNlKC8oXlwifFwiJCkvZywgXCInXCIpO1xuICAgICAgbmFtZSA9IGN0eC5zdHlsaXplKG5hbWUsICdzdHJpbmcnKTtcbiAgICB9XG4gIH1cblxuICByZXR1cm4gbmFtZSArICc6ICcgKyBzdHI7XG59XG5cblxuZnVuY3Rpb24gcmVkdWNlVG9TaW5nbGVTdHJpbmcob3V0cHV0LCBiYXNlLCBicmFjZXMpIHtcbiAgdmFyIG51bUxpbmVzRXN0ID0gMDtcbiAgdmFyIGxlbmd0aCA9IG91dHB1dC5yZWR1Y2UoZnVuY3Rpb24ocHJldiwgY3VyKSB7XG4gICAgbnVtTGluZXNFc3QrKztcbiAgICBpZiAoY3VyLmluZGV4T2YoJ1xcbicpID49IDApIG51bUxpbmVzRXN0Kys7XG4gICAgcmV0dXJuIHByZXYgKyBjdXIucmVwbGFjZSgvXFx1MDAxYlxcW1xcZFxcZD9tL2csICcnKS5sZW5ndGggKyAxO1xuICB9LCAwKTtcblxuICBpZiAobGVuZ3RoID4gNjApIHtcbiAgICByZXR1cm4gYnJhY2VzWzBdICtcbiAgICAgICAgICAgKGJhc2UgPT09ICcnID8gJycgOiBiYXNlICsgJ1xcbiAnKSArXG4gICAgICAgICAgICcgJyArXG4gICAgICAgICAgIG91dHB1dC5qb2luKCcsXFxuICAnKSArXG4gICAgICAgICAgICcgJyArXG4gICAgICAgICAgIGJyYWNlc1sxXTtcbiAgfVxuXG4gIHJldHVybiBicmFjZXNbMF0gKyBiYXNlICsgJyAnICsgb3V0cHV0LmpvaW4oJywgJykgKyAnICcgKyBicmFjZXNbMV07XG59XG5cblxuLy8gTk9URTogVGhlc2UgdHlwZSBjaGVja2luZyBmdW5jdGlvbnMgaW50ZW50aW9uYWxseSBkb24ndCB1c2UgYGluc3RhbmNlb2ZgXG4vLyBiZWNhdXNlIGl0IGlzIGZyYWdpbGUgYW5kIGNhbiBiZSBlYXNpbHkgZmFrZWQgd2l0aCBgT2JqZWN0LmNyZWF0ZSgpYC5cbmZ1bmN0aW9uIGlzQXJyYXkoYXIpIHtcbiAgcmV0dXJuIEFycmF5LmlzQXJyYXkoYXIpO1xufVxuZXhwb3J0cy5pc0FycmF5ID0gaXNBcnJheTtcblxuZnVuY3Rpb24gaXNCb29sZWFuKGFyZykge1xuICByZXR1cm4gdHlwZW9mIGFyZyA9PT0gJ2Jvb2xlYW4nO1xufVxuZXhwb3J0cy5pc0Jvb2xlYW4gPSBpc0Jvb2xlYW47XG5cbmZ1bmN0aW9uIGlzTnVsbChhcmcpIHtcbiAgcmV0dXJuIGFyZyA9PT0gbnVsbDtcbn1cbmV4cG9ydHMuaXNOdWxsID0gaXNOdWxsO1xuXG5mdW5jdGlvbiBpc051bGxPclVuZGVmaW5lZChhcmcpIHtcbiAgcmV0dXJuIGFyZyA9PSBudWxsO1xufVxuZXhwb3J0cy5pc051bGxPclVuZGVmaW5lZCA9IGlzTnVsbE9yVW5kZWZpbmVkO1xuXG5mdW5jdGlvbiBpc051bWJlcihhcmcpIHtcbiAgcmV0dXJuIHR5cGVvZiBhcmcgPT09ICdudW1iZXInO1xufVxuZXhwb3J0cy5pc051bWJlciA9IGlzTnVtYmVyO1xuXG5mdW5jdGlvbiBpc1N0cmluZyhhcmcpIHtcbiAgcmV0dXJuIHR5cGVvZiBhcmcgPT09ICdzdHJpbmcnO1xufVxuZXhwb3J0cy5pc1N0cmluZyA9IGlzU3RyaW5nO1xuXG5mdW5jdGlvbiBpc1N5bWJvbChhcmcpIHtcbiAgcmV0dXJuIHR5cGVvZiBhcmcgPT09ICdzeW1ib2wnO1xufVxuZXhwb3J0cy5pc1N5bWJvbCA9IGlzU3ltYm9sO1xuXG5mdW5jdGlvbiBpc1VuZGVmaW5lZChhcmcpIHtcbiAgcmV0dXJuIGFyZyA9PT0gdm9pZCAwO1xufVxuZXhwb3J0cy5pc1VuZGVmaW5lZCA9IGlzVW5kZWZpbmVkO1xuXG5mdW5jdGlvbiBpc1JlZ0V4cChyZSkge1xuICByZXR1cm4gaXNPYmplY3QocmUpICYmIG9iamVjdFRvU3RyaW5nKHJlKSA9PT0gJ1tvYmplY3QgUmVnRXhwXSc7XG59XG5leHBvcnRzLmlzUmVnRXhwID0gaXNSZWdFeHA7XG5cbmZ1bmN0aW9uIGlzT2JqZWN0KGFyZykge1xuICByZXR1cm4gdHlwZW9mIGFyZyA9PT0gJ29iamVjdCcgJiYgYXJnICE9PSBudWxsO1xufVxuZXhwb3J0cy5pc09iamVjdCA9IGlzT2JqZWN0O1xuXG5mdW5jdGlvbiBpc0RhdGUoZCkge1xuICByZXR1cm4gaXNPYmplY3QoZCkgJiYgb2JqZWN0VG9TdHJpbmcoZCkgPT09ICdbb2JqZWN0IERhdGVdJztcbn1cbmV4cG9ydHMuaXNEYXRlID0gaXNEYXRlO1xuXG5mdW5jdGlvbiBpc0Vycm9yKGUpIHtcbiAgcmV0dXJuIGlzT2JqZWN0KGUpICYmXG4gICAgICAob2JqZWN0VG9TdHJpbmcoZSkgPT09ICdbb2JqZWN0IEVycm9yXScgfHwgZSBpbnN0YW5jZW9mIEVycm9yKTtcbn1cbmV4cG9ydHMuaXNFcnJvciA9IGlzRXJyb3I7XG5cbmZ1bmN0aW9uIGlzRnVuY3Rpb24oYXJnKSB7XG4gIHJldHVybiB0eXBlb2YgYXJnID09PSAnZnVuY3Rpb24nO1xufVxuZXhwb3J0cy5pc0Z1bmN0aW9uID0gaXNGdW5jdGlvbjtcblxuZnVuY3Rpb24gaXNQcmltaXRpdmUoYXJnKSB7XG4gIHJldHVybiBhcmcgPT09IG51bGwgfHxcbiAgICAgICAgIHR5cGVvZiBhcmcgPT09ICdib29sZWFuJyB8fFxuICAgICAgICAgdHlwZW9mIGFyZyA9PT0gJ251bWJlcicgfHxcbiAgICAgICAgIHR5cGVvZiBhcmcgPT09ICdzdHJpbmcnIHx8XG4gICAgICAgICB0eXBlb2YgYXJnID09PSAnc3ltYm9sJyB8fCAgLy8gRVM2IHN5bWJvbFxuICAgICAgICAgdHlwZW9mIGFyZyA9PT0gJ3VuZGVmaW5lZCc7XG59XG5leHBvcnRzLmlzUHJpbWl0aXZlID0gaXNQcmltaXRpdmU7XG5cbmV4cG9ydHMuaXNCdWZmZXIgPSByZXF1aXJlKCcuL3N1cHBvcnQvaXNCdWZmZXInKTtcblxuZnVuY3Rpb24gb2JqZWN0VG9TdHJpbmcobykge1xuICByZXR1cm4gT2JqZWN0LnByb3RvdHlwZS50b1N0cmluZy5jYWxsKG8pO1xufVxuXG5cbmZ1bmN0aW9uIHBhZChuKSB7XG4gIHJldHVybiBuIDwgMTAgPyAnMCcgKyBuLnRvU3RyaW5nKDEwKSA6IG4udG9TdHJpbmcoMTApO1xufVxuXG5cbnZhciBtb250aHMgPSBbJ0phbicsICdGZWInLCAnTWFyJywgJ0FwcicsICdNYXknLCAnSnVuJywgJ0p1bCcsICdBdWcnLCAnU2VwJyxcbiAgICAgICAgICAgICAgJ09jdCcsICdOb3YnLCAnRGVjJ107XG5cbi8vIDI2IEZlYiAxNjoxOTozNFxuZnVuY3Rpb24gdGltZXN0YW1wKCkge1xuICB2YXIgZCA9IG5ldyBEYXRlKCk7XG4gIHZhciB0aW1lID0gW3BhZChkLmdldEhvdXJzKCkpLFxuICAgICAgICAgICAgICBwYWQoZC5nZXRNaW51dGVzKCkpLFxuICAgICAgICAgICAgICBwYWQoZC5nZXRTZWNvbmRzKCkpXS5qb2luKCc6Jyk7XG4gIHJldHVybiBbZC5nZXREYXRlKCksIG1vbnRoc1tkLmdldE1vbnRoKCldLCB0aW1lXS5qb2luKCcgJyk7XG59XG5cblxuLy8gbG9nIGlzIGp1c3QgYSB0aGluIHdyYXBwZXIgdG8gY29uc29sZS5sb2cgdGhhdCBwcmVwZW5kcyBhIHRpbWVzdGFtcFxuZXhwb3J0cy5sb2cgPSBmdW5jdGlvbigpIHtcbiAgY29uc29sZS5sb2coJyVzIC0gJXMnLCB0aW1lc3RhbXAoKSwgZXhwb3J0cy5mb3JtYXQuYXBwbHkoZXhwb3J0cywgYXJndW1lbnRzKSk7XG59O1xuXG5cbi8qKlxuICogSW5oZXJpdCB0aGUgcHJvdG90eXBlIG1ldGhvZHMgZnJvbSBvbmUgY29uc3RydWN0b3IgaW50byBhbm90aGVyLlxuICpcbiAqIFRoZSBGdW5jdGlvbi5wcm90b3R5cGUuaW5oZXJpdHMgZnJvbSBsYW5nLmpzIHJld3JpdHRlbiBhcyBhIHN0YW5kYWxvbmVcbiAqIGZ1bmN0aW9uIChub3Qgb24gRnVuY3Rpb24ucHJvdG90eXBlKS4gTk9URTogSWYgdGhpcyBmaWxlIGlzIHRvIGJlIGxvYWRlZFxuICogZHVyaW5nIGJvb3RzdHJhcHBpbmcgdGhpcyBmdW5jdGlvbiBuZWVkcyB0byBiZSByZXdyaXR0ZW4gdXNpbmcgc29tZSBuYXRpdmVcbiAqIGZ1bmN0aW9ucyBhcyBwcm90b3R5cGUgc2V0dXAgdXNpbmcgbm9ybWFsIEphdmFTY3JpcHQgZG9lcyBub3Qgd29yayBhc1xuICogZXhwZWN0ZWQgZHVyaW5nIGJvb3RzdHJhcHBpbmcgKHNlZSBtaXJyb3IuanMgaW4gcjExNDkwMykuXG4gKlxuICogQHBhcmFtIHtmdW5jdGlvbn0gY3RvciBDb25zdHJ1Y3RvciBmdW5jdGlvbiB3aGljaCBuZWVkcyB0byBpbmhlcml0IHRoZVxuICogICAgIHByb3RvdHlwZS5cbiAqIEBwYXJhbSB7ZnVuY3Rpb259IHN1cGVyQ3RvciBDb25zdHJ1Y3RvciBmdW5jdGlvbiB0byBpbmhlcml0IHByb3RvdHlwZSBmcm9tLlxuICovXG5leHBvcnRzLmluaGVyaXRzID0gcmVxdWlyZSgnaW5oZXJpdHMnKTtcblxuZXhwb3J0cy5fZXh0ZW5kID0gZnVuY3Rpb24ob3JpZ2luLCBhZGQpIHtcbiAgLy8gRG9uJ3QgZG8gYW55dGhpbmcgaWYgYWRkIGlzbid0IGFuIG9iamVjdFxuICBpZiAoIWFkZCB8fCAhaXNPYmplY3QoYWRkKSkgcmV0dXJuIG9yaWdpbjtcblxuICB2YXIga2V5cyA9IE9iamVjdC5rZXlzKGFkZCk7XG4gIHZhciBpID0ga2V5cy5sZW5ndGg7XG4gIHdoaWxlIChpLS0pIHtcbiAgICBvcmlnaW5ba2V5c1tpXV0gPSBhZGRba2V5c1tpXV07XG4gIH1cbiAgcmV0dXJuIG9yaWdpbjtcbn07XG5cbmZ1bmN0aW9uIGhhc093blByb3BlcnR5KG9iaiwgcHJvcCkge1xuICByZXR1cm4gT2JqZWN0LnByb3RvdHlwZS5oYXNPd25Qcm9wZXJ0eS5jYWxsKG9iaiwgcHJvcCk7XG59XG4iXX0=
