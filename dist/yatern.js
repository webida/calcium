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

},{"util":18}],2:[function(require,module,exports){
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

},{"../domains/status":5,"../domains/types":6,"./constraints":3,"acorn/dist/walk":14}],3:[function(require,module,exports){
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
var acorn_loose = require('acorn/dist/acorn_loose');
var aux = require('./aux');
var types = require('./domains/types');
var context = require('./domains/context');
var status = require('./domains/status');
var varBlock = require('./varBlock');
var cGen = require('./constraint/cGen');
var varRefs = require('./varrefs');
var retOccur = require('./retOccur');

function analyze(input, retAll) {
    // the Scope object for global scope
    // scope.Scope.globalScope = new scope.Scope(null);

    // parsing input program
    var ast;
    try {
        ast = acorn.parse(input);
    } catch (e) {
        ast = acorn_loose.parse_dammit(input);
    }

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
exports.onFunctionOrReturnKeyword = retOccur.onFunctionOrReturnKeyword;
exports.findReturnStatements = retOccur.findReturnStatements;

},{"./aux":1,"./constraint/cGen":2,"./domains/context":4,"./domains/status":5,"./domains/types":6,"./retOccur":8,"./varBlock":10,"./varrefs":11,"acorn/dist/acorn":12,"acorn/dist/acorn_loose":13}],8:[function(require,module,exports){
'use strict';

var walk = require('acorn/dist/walk');
var myWalker = require('./util/myWalker');

/**
 * Check whether given pos is on a function keyword
 * @param ast - AST of a program
 * @param pos - index position
 * @returns {*} - function node or null
 */
function onFunctionOrReturnKeyword(ast, pos) {
    'use strict';

    // find function node
    // st is the enclosing function
    var walker = myWalker.wrapWalker(walk.base,
    // pre
    function (node, st) {
        if (node.start > pos || node.end < pos) {
            return false;
        }

        // on a function keyword, 8 is the length of 'function'
        // or on return keyword, 6 is the length of 'return'
        if ((node.type === 'FunctionDeclaration' || node.type === 'FunctionExpression') && (node.start <= pos && pos <= node.start + 8) || node.type === 'ReturnStatement' && (node.start <= pos && pos <= node.start + 6)) {
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
 * Given a function node, find its return nodes
 *
 * @param fNode - AST node of a function, possibly with no annotation
 * @returns {*} - array of AST nodes
 */
function getReturnNodes(fNode) {
    'use strict';
    var rets = [];
    if (fNode.type !== 'FunctionExpression' && fNode.type !== 'FunctionDeclaration') {
        throw Error('fNode should be a function node');
    }

    var walker = walk.make({
        ReturnStatement: function ReturnStatement(node) {
            return rets.push(node);
        },
        Function: function Function() {}
    }, walk.base);

    walk.recursive(fNode.body, undefined, walker);

    return rets;
}

/**
 * Find return nodes corresponding to the position
 * if the pos is on a function keyword
 *
 * @param ast - AST node of a program, possibly with no annotation
 * @param pos - cursor position
 * @param includeFunctionKeyword - whether to include function keyword range
 * @returns {Array} - array of AST nodes of return statements
 */
function findReturnStatements(ast, pos, includeFunctionKeyword) {
    'use strict';

    var fNode = onFunctionOrReturnKeyword(ast, pos);
    if (!fNode) {
        // pos is not on function keyword
        return null;
    }

    var rets = getReturnNodes(fNode);
    // when function does not have return statements,
    // indicate it by the closing brace of the function body
    if (rets.length === 0) {
        rets.push({ start: fNode.end - 1, end: fNode.end });
    }
    if (includeFunctionKeyword) {
        rets.push({ start: fNode.start, end: fNode.start + 8 });
    }
    return rets;
}

exports.onFunctionOrReturnKeyword = onFunctionOrReturnKeyword;
exports.findReturnStatements = findReturnStatements;

// not visit inner functions

},{"./util/myWalker":9,"acorn/dist/walk":14}],9:[function(require,module,exports){
/**
 * Wrap a walker with pre- and post- actions
 *
 * @param preNode - Apply before visiting the current node.
 * If returns false, do not visit the node.
 * @param postNode - Apply after visiting the current node.
 * If given, return values are overridden.
 * @returns {*} - a new walker
 */
"use strict";

function wrapWalker(walker, preNode, postNode, stChange) {
    var retWalker = {};

    var _loop = function (nodeType) {
        if (!walker.hasOwnProperty(nodeType)) {
            return "continue";
        }
        retWalker[nodeType] = function (node, st, c) {
            var ret = undefined;
            var newSt = st;
            if (stChange) {
                newSt = stChange(node, st);
            }
            if (!preNode || preNode(node, newSt, c)) {
                ret = walker[nodeType](node, newSt, c);
            } else {
                return;
            }
            if (postNode) {
                ret = postNode(node, newSt, c);
            }
            return ret;
        };
    };

    // wrapping each function preNode and postNode
    for (var nodeType in walker) {
        var _ret = _loop(nodeType);

        if (_ret === "continue") continue;
    }
    return retWalker;
}

exports.wrapWalker = wrapWalker;

},{}],10:[function(require,module,exports){
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

},{"./aux":1,"./domains/types":6,"acorn/dist/walk":14}],11:[function(require,module,exports){
'use strict';

var walk = require('acorn/dist/walk');
var myWalker = require('./util/myWalker');

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
            c(node.handler, vb);
        }
        if (node.finalizer) {
            c(node.finalizer, vb);
        }
    },
    CatchClause: function CatchClause(node, vb, c) {
        var catchVb = node.body['@block'];
        c(node.param, catchVb);
        c(node.body, catchVb);
    },
    VariableDeclaration: function VariableDeclaration(node, vb, c) {
        for (var i = 0; i < node.declarations.length; ++i) {
            var decl = node.declarations[i];
            c(decl.id, vb);
            if (decl.init) c(decl.init, vb);
        }
    }
});

function findIdentifierAt(ast, pos) {
    'use strict';

    function Found(node, state) {
        this.node = node;
        this.state = state;
    }

    // find the node
    var walker = myWalker.wrapWalker(varWalker, function (node, vb) {
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
    // identifier not found
    return null;
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
    var refs = [];

    var walker = walk.make({
        Identifier: function Identifier(node, vb) {
            if (node.name !== varName) return;
            if (vb1 === vb.findVarInChain(varName)) {
                refs.push(node);
            }
        }
    }, varWalker);

    walk.recursive(vb1.originNode, vb1, walker);
    return refs;
}

exports.findIdentifierAt = findIdentifierAt;
exports.findVarRefsAt = findVarRefsAt;

},{"./util/myWalker":9,"acorn/dist/walk":14}],12:[function(require,module,exports){
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

},{}],13:[function(require,module,exports){
(function (global){
(function(f){if(typeof exports==="object"&&typeof module!=="undefined"){module.exports=f()}else if(typeof define==="function"&&define.amd){define([],f)}else{var g;if(typeof window!=="undefined"){g=window}else if(typeof global!=="undefined"){g=global}else if(typeof self!=="undefined"){g=self}else{g=this}(g.acorn || (g.acorn = {})).loose = f()}})(function(){var define,module,exports;return (function e(t,n,r){function s(o,u){if(!n[o]){if(!t[o]){var a=typeof require=="function"&&require;if(!u&&a)return a(o,!0);if(i)return i(o,!0);var f=new Error("Cannot find module '"+o+"'");throw f.code="MODULE_NOT_FOUND",f}var l=n[o]={exports:{}};t[o][0].call(l.exports,function(e){var n=t[o][1][e];return s(n?n:e)},l,l.exports,e,t,n,r)}return n[o].exports}var i=typeof require=="function"&&require;for(var o=0;o<r.length;o++)s(r[o]);return s})({1:[function(_dereq_,module,exports){
"use strict";

var _interopRequireWildcard = function (obj) { return obj && obj.__esModule ? obj : { "default": obj }; };

exports.parse_dammit = parse_dammit;
exports.__esModule = true;
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

var acorn = _interopRequireWildcard(_dereq_(".."));

var _state = _dereq_("./state");

var LooseParser = _state.LooseParser;

_dereq_("./tokenize");

_dereq_("./parseutil");

_dereq_("./statement");

_dereq_("./expression");

exports.LooseParser = _state.LooseParser;

acorn.defaultOptions.tabSize = 4;

function parse_dammit(input, options) {
  var p = new LooseParser(input, options);
  p.next();
  return p.parseTopLevel();
}

acorn.parse_dammit = parse_dammit;
acorn.LooseParser = LooseParser;

},{"..":3,"./expression":4,"./parseutil":5,"./state":6,"./statement":7,"./tokenize":8}],2:[function(_dereq_,module,exports){
(function (global){
"use strict";(function(f){if(typeof exports === "object" && typeof module !== "undefined"){module.exports = f();}else if(typeof define === "function" && define.amd){define([], f);}else {var g;if(typeof window !== "undefined"){g = window;}else if(typeof global !== "undefined"){g = global;}else if(typeof self !== "undefined"){g = self;}else {g = this;}g.acorn = f();}})(function(){var define, module, exports;return (function e(t, n, r){function s(o, u){if(!n[o]){if(!t[o]){var a=typeof _dereq_ == "function" && _dereq_;if(!u && a){return a(o, !0);}if(i){return i(o, !0);}var f=new Error("Cannot find module '" + o + "'");throw (f.code = "MODULE_NOT_FOUND", f);}var l=n[o] = {exports:{}};t[o][0].call(l.exports, function(e){var n=t[o][1][e];return s(n?n:e);}, l, l.exports, e, t, n, r);}return n[o].exports;}var i=typeof _dereq_ == "function" && _dereq_;for(var o=0; o < r.length; o++) s(r[o]);return s;})({1:[function(_dereq_, module, exports){"use strict";exports.parse = parse;exports.parseExpressionAt = parseExpressionAt;exports.tokenizer = tokenizer;exports.__esModule = true;var _state=_dereq_("./state");var Parser=_state.Parser;var _options=_dereq_("./options");var getOptions=_options.getOptions;_dereq_("./parseutil");_dereq_("./statement");_dereq_("./lval");_dereq_("./expression");exports.Parser = _state.Parser;exports.plugins = _state.plugins;exports.defaultOptions = _options.defaultOptions;var _location=_dereq_("./location");exports.SourceLocation = _location.SourceLocation;exports.getLineInfo = _location.getLineInfo;exports.Node = _dereq_("./node").Node;var _tokentype=_dereq_("./tokentype");exports.TokenType = _tokentype.TokenType;exports.tokTypes = _tokentype.types;var _tokencontext=_dereq_("./tokencontext");exports.TokContext = _tokencontext.TokContext;exports.tokContexts = _tokencontext.types;var _identifier=_dereq_("./identifier");exports.isIdentifierChar = _identifier.isIdentifierChar;exports.isIdentifierStart = _identifier.isIdentifierStart;exports.Token = _dereq_("./tokenize").Token;var _whitespace=_dereq_("./whitespace");exports.isNewLine = _whitespace.isNewLine;exports.lineBreak = _whitespace.lineBreak;exports.lineBreakG = _whitespace.lineBreakG;var version="1.2.2";exports.version = version;function parse(input, options){var p=parser(options, input);var startPos=p.pos, startLoc=p.options.locations && p.curPosition();p.nextToken();return p.parseTopLevel(p.options.program || p.startNodeAt(startPos, startLoc));}function parseExpressionAt(input, pos, options){var p=parser(options, input, pos);p.nextToken();return p.parseExpression();}function tokenizer(input, options){return parser(options, input);}function parser(options, input){return new Parser(getOptions(options), String(input));}}, {"./expression":6, "./identifier":7, "./location":8, "./lval":9, "./node":10, "./options":11, "./parseutil":12, "./state":13, "./statement":14, "./tokencontext":15, "./tokenize":16, "./tokentype":17, "./whitespace":19}], 2:[function(_dereq_, module, exports){if(typeof Object.create === "function"){module.exports = function inherits(ctor, superCtor){ctor.super_ = superCtor;ctor.prototype = Object.create(superCtor.prototype, {constructor:{value:ctor, enumerable:false, writable:true, configurable:true}});};}else {module.exports = function inherits(ctor, superCtor){ctor.super_ = superCtor;var TempCtor=function TempCtor(){};TempCtor.prototype = superCtor.prototype;ctor.prototype = new TempCtor();ctor.prototype.constructor = ctor;};}}, {}], 3:[function(_dereq_, module, exports){var process=module.exports = {};var queue=[];var draining=false;function drainQueue(){if(draining){return;}draining = true;var currentQueue;var len=queue.length;while(len) {currentQueue = queue;queue = [];var i=-1;while(++i < len) {currentQueue[i]();}len = queue.length;}draining = false;}process.nextTick = function(fun){queue.push(fun);if(!draining){setTimeout(drainQueue, 0);}};process.title = "browser";process.browser = true;process.env = {};process.argv = [];process.version = "";process.versions = {};function noop(){}process.on = noop;process.addListener = noop;process.once = noop;process.off = noop;process.removeListener = noop;process.removeAllListeners = noop;process.emit = noop;process.binding = function(name){throw new Error("process.binding is not supported");};process.cwd = function(){return "/";};process.chdir = function(dir){throw new Error("process.chdir is not supported");};process.umask = function(){return 0;};}, {}], 4:[function(_dereq_, module, exports){module.exports = function isBuffer(arg){return arg && typeof arg === "object" && typeof arg.copy === "function" && typeof arg.fill === "function" && typeof arg.readUInt8 === "function";};}, {}], 5:[function(_dereq_, module, exports){(function(process, global){var formatRegExp=/%[sdj%]/g;exports.format = function(f){if(!isString(f)){var objects=[];for(var i=0; i < arguments.length; i++) {objects.push(inspect(arguments[i]));}return objects.join(" ");}var i=1;var args=arguments;var len=args.length;var str=String(f).replace(formatRegExp, function(x){if(x === "%%")return "%";if(i >= len)return x;switch(x){case "%s":return String(args[i++]);case "%d":return Number(args[i++]);case "%j":try{return JSON.stringify(args[i++]);}catch(_) {return "[Circular]";}default:return x;}});for(var x=args[i]; i < len; x = args[++i]) {if(isNull(x) || !isObject(x)){str += " " + x;}else {str += " " + inspect(x);}}return str;};exports.deprecate = function(fn, msg){if(isUndefined(global.process)){return function(){return exports.deprecate(fn, msg).apply(this, arguments);};}if(process.noDeprecation === true){return fn;}var warned=false;function deprecated(){if(!warned){if(process.throwDeprecation){throw new Error(msg);}else if(process.traceDeprecation){console.trace(msg);}else {console.error(msg);}warned = true;}return fn.apply(this, arguments);}return deprecated;};var debugs={};var debugEnviron;exports.debuglog = function(set){if(isUndefined(debugEnviron))debugEnviron = process.env.NODE_DEBUG || "";set = set.toUpperCase();if(!debugs[set]){if(new RegExp("\\b" + set + "\\b", "i").test(debugEnviron)){var pid=process.pid;debugs[set] = function(){var msg=exports.format.apply(exports, arguments);console.error("%s %d: %s", set, pid, msg);};}else {debugs[set] = function(){};}}return debugs[set];};function inspect(obj, opts){var ctx={seen:[], stylize:stylizeNoColor};if(arguments.length >= 3)ctx.depth = arguments[2];if(arguments.length >= 4)ctx.colors = arguments[3];if(isBoolean(opts)){ctx.showHidden = opts;}else if(opts){exports._extend(ctx, opts);}if(isUndefined(ctx.showHidden))ctx.showHidden = false;if(isUndefined(ctx.depth))ctx.depth = 2;if(isUndefined(ctx.colors))ctx.colors = false;if(isUndefined(ctx.customInspect))ctx.customInspect = true;if(ctx.colors)ctx.stylize = stylizeWithColor;return formatValue(ctx, obj, ctx.depth);}exports.inspect = inspect;inspect.colors = {bold:[1, 22], italic:[3, 23], underline:[4, 24], inverse:[7, 27], white:[37, 39], grey:[90, 39], black:[30, 39], blue:[34, 39], cyan:[36, 39], green:[32, 39], magenta:[35, 39], red:[31, 39], yellow:[33, 39]};inspect.styles = {special:"cyan", number:"yellow", boolean:"yellow", undefined:"grey", "null":"bold", string:"green", date:"magenta", regexp:"red"};function stylizeWithColor(str, styleType){var style=inspect.styles[styleType];if(style){return "\u001b[" + inspect.colors[style][0] + "m" + str + "\u001b[" + inspect.colors[style][1] + "m";}else {return str;}}function stylizeNoColor(str, styleType){return str;}function arrayToHash(array){var hash={};array.forEach(function(val, idx){hash[val] = true;});return hash;}function formatValue(ctx, value, recurseTimes){if(ctx.customInspect && value && isFunction(value.inspect) && value.inspect !== exports.inspect && !(value.constructor && value.constructor.prototype === value)){var ret=value.inspect(recurseTimes, ctx);if(!isString(ret)){ret = formatValue(ctx, ret, recurseTimes);}return ret;}var primitive=formatPrimitive(ctx, value);if(primitive){return primitive;}var keys=Object.keys(value);var visibleKeys=arrayToHash(keys);if(ctx.showHidden){keys = Object.getOwnPropertyNames(value);}if(isError(value) && (keys.indexOf("message") >= 0 || keys.indexOf("description") >= 0)){return formatError(value);}if(keys.length === 0){if(isFunction(value)){var name=value.name?": " + value.name:"";return ctx.stylize("[Function" + name + "]", "special");}if(isRegExp(value)){return ctx.stylize(RegExp.prototype.toString.call(value), "regexp");}if(isDate(value)){return ctx.stylize(Date.prototype.toString.call(value), "date");}if(isError(value)){return formatError(value);}}var base="", array=false, braces=["{", "}"];if(isArray(value)){array = true;braces = ["[", "]"];}if(isFunction(value)){var n=value.name?": " + value.name:"";base = " [Function" + n + "]";}if(isRegExp(value)){base = " " + RegExp.prototype.toString.call(value);}if(isDate(value)){base = " " + Date.prototype.toUTCString.call(value);}if(isError(value)){base = " " + formatError(value);}if(keys.length === 0 && (!array || value.length == 0)){return braces[0] + base + braces[1];}if(recurseTimes < 0){if(isRegExp(value)){return ctx.stylize(RegExp.prototype.toString.call(value), "regexp");}else {return ctx.stylize("[Object]", "special");}}ctx.seen.push(value);var output;if(array){output = formatArray(ctx, value, recurseTimes, visibleKeys, keys);}else {output = keys.map(function(key){return formatProperty(ctx, value, recurseTimes, visibleKeys, key, array);});}ctx.seen.pop();return reduceToSingleString(output, base, braces);}function formatPrimitive(ctx, value){if(isUndefined(value)){return ctx.stylize("undefined", "undefined");}if(isString(value)){var simple="'" + JSON.stringify(value).replace(/^"|"$/g, "").replace(/'/g, "\\'").replace(/\\"/g, "\"") + "'";return ctx.stylize(simple, "string");}if(isNumber(value)){return ctx.stylize("" + value, "number");}if(isBoolean(value)){return ctx.stylize("" + value, "boolean");}if(isNull(value)){return ctx.stylize("null", "null");}}function formatError(value){return "[" + Error.prototype.toString.call(value) + "]";}function formatArray(ctx, value, recurseTimes, visibleKeys, keys){var output=[];for(var i=0, l=value.length; i < l; ++i) {if(hasOwnProperty(value, String(i))){output.push(formatProperty(ctx, value, recurseTimes, visibleKeys, String(i), true));}else {output.push("");}}keys.forEach(function(key){if(!key.match(/^\d+$/)){output.push(formatProperty(ctx, value, recurseTimes, visibleKeys, key, true));}});return output;}function formatProperty(ctx, value, recurseTimes, visibleKeys, key, array){var name, str, desc;desc = Object.getOwnPropertyDescriptor(value, key) || {value:value[key]};if(desc.get){if(desc.set){str = ctx.stylize("[Getter/Setter]", "special");}else {str = ctx.stylize("[Getter]", "special");}}else {if(desc.set){str = ctx.stylize("[Setter]", "special");}}if(!hasOwnProperty(visibleKeys, key)){name = "[" + key + "]";}if(!str){if(ctx.seen.indexOf(desc.value) < 0){if(isNull(recurseTimes)){str = formatValue(ctx, desc.value, null);}else {str = formatValue(ctx, desc.value, recurseTimes - 1);}if(str.indexOf("\n") > -1){if(array){str = str.split("\n").map(function(line){return "  " + line;}).join("\n").substr(2);}else {str = "\n" + str.split("\n").map(function(line){return "   " + line;}).join("\n");}}}else {str = ctx.stylize("[Circular]", "special");}}if(isUndefined(name)){if(array && key.match(/^\d+$/)){return str;}name = JSON.stringify("" + key);if(name.match(/^"([a-zA-Z_][a-zA-Z_0-9]*)"$/)){name = name.substr(1, name.length - 2);name = ctx.stylize(name, "name");}else {name = name.replace(/'/g, "\\'").replace(/\\"/g, "\"").replace(/(^"|"$)/g, "'");name = ctx.stylize(name, "string");}}return name + ": " + str;}function reduceToSingleString(output, base, braces){var numLinesEst=0;var length=output.reduce(function(prev, cur){numLinesEst++;if(cur.indexOf("\n") >= 0)numLinesEst++;return prev + cur.replace(/\u001b\[\d\d?m/g, "").length + 1;}, 0);if(length > 60){return braces[0] + (base === ""?"":base + "\n ") + " " + output.join(",\n  ") + " " + braces[1];}return braces[0] + base + " " + output.join(", ") + " " + braces[1];}function isArray(ar){return Array.isArray(ar);}exports.isArray = isArray;function isBoolean(arg){return typeof arg === "boolean";}exports.isBoolean = isBoolean;function isNull(arg){return arg === null;}exports.isNull = isNull;function isNullOrUndefined(arg){return arg == null;}exports.isNullOrUndefined = isNullOrUndefined;function isNumber(arg){return typeof arg === "number";}exports.isNumber = isNumber;function isString(arg){return typeof arg === "string";}exports.isString = isString;function isSymbol(arg){return typeof arg === "symbol";}exports.isSymbol = isSymbol;function isUndefined(arg){return arg === void 0;}exports.isUndefined = isUndefined;function isRegExp(re){return isObject(re) && objectToString(re) === "[object RegExp]";}exports.isRegExp = isRegExp;function isObject(arg){return typeof arg === "object" && arg !== null;}exports.isObject = isObject;function isDate(d){return isObject(d) && objectToString(d) === "[object Date]";}exports.isDate = isDate;function isError(e){return isObject(e) && (objectToString(e) === "[object Error]" || e instanceof Error);}exports.isError = isError;function isFunction(arg){return typeof arg === "function";}exports.isFunction = isFunction;function isPrimitive(arg){return arg === null || typeof arg === "boolean" || typeof arg === "number" || typeof arg === "string" || typeof arg === "symbol" || typeof arg === "undefined";}exports.isPrimitive = isPrimitive;exports.isBuffer = _dereq_("./support/isBuffer");function objectToString(o){return Object.prototype.toString.call(o);}function pad(n){return n < 10?"0" + n.toString(10):n.toString(10);}var months=["Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec"];function timestamp(){var d=new Date();var time=[pad(d.getHours()), pad(d.getMinutes()), pad(d.getSeconds())].join(":");return [d.getDate(), months[d.getMonth()], time].join(" ");}exports.log = function(){console.log("%s - %s", timestamp(), exports.format.apply(exports, arguments));};exports.inherits = _dereq_("inherits");exports._extend = function(origin, add){if(!add || !isObject(add))return origin;var keys=Object.keys(add);var i=keys.length;while(i--) {origin[keys[i]] = add[keys[i]];}return origin;};function hasOwnProperty(obj, prop){return Object.prototype.hasOwnProperty.call(obj, prop);}}).call(this, _dereq_("_process"), typeof global !== "undefined"?global:typeof self !== "undefined"?self:typeof window !== "undefined"?window:{});}, {"./support/isBuffer":4, _process:3, inherits:2}], 6:[function(_dereq_, module, exports){"use strict";var tt=_dereq_("./tokentype").types;var Parser=_dereq_("./state").Parser;var reservedWords=_dereq_("./identifier").reservedWords;var has=_dereq_("./util").has;var pp=Parser.prototype;pp.checkPropClash = function(prop, propHash){if(this.options.ecmaVersion >= 6)return;var key=prop.key, name=undefined;switch(key.type){case "Identifier":name = key.name;break;case "Literal":name = String(key.value);break;default:return;}var kind=prop.kind || "init", other=undefined;if(has(propHash, name)){other = propHash[name];var isGetSet=kind !== "init";if((this.strict || isGetSet) && other[kind] || !(isGetSet ^ other.init))this.raise(key.start, "Redefinition of property");}else {other = propHash[name] = {init:false, get:false, set:false};}other[kind] = true;};pp.parseExpression = function(noIn, refShorthandDefaultPos){var startPos=this.start, startLoc=this.startLoc;var expr=this.parseMaybeAssign(noIn, refShorthandDefaultPos);if(this.type === tt.comma){var node=this.startNodeAt(startPos, startLoc);node.expressions = [expr];while(this.eat(tt.comma)) node.expressions.push(this.parseMaybeAssign(noIn, refShorthandDefaultPos));return this.finishNode(node, "SequenceExpression");}return expr;};pp.parseMaybeAssign = function(noIn, refShorthandDefaultPos, afterLeftParse){if(this.type == tt._yield && this.inGenerator)return this.parseYield();var failOnShorthandAssign=undefined;if(!refShorthandDefaultPos){refShorthandDefaultPos = {start:0};failOnShorthandAssign = true;}else {failOnShorthandAssign = false;}var startPos=this.start, startLoc=this.startLoc;if(this.type == tt.parenL || this.type == tt.name)this.potentialArrowAt = this.start;var left=this.parseMaybeConditional(noIn, refShorthandDefaultPos);if(afterLeftParse)left = afterLeftParse.call(this, left, startPos, startLoc);if(this.type.isAssign){var node=this.startNodeAt(startPos, startLoc);node.operator = this.value;node.left = this.type === tt.eq?this.toAssignable(left):left;refShorthandDefaultPos.start = 0;this.checkLVal(left);this.next();node.right = this.parseMaybeAssign(noIn);return this.finishNode(node, "AssignmentExpression");}else if(failOnShorthandAssign && refShorthandDefaultPos.start){this.unexpected(refShorthandDefaultPos.start);}return left;};pp.parseMaybeConditional = function(noIn, refShorthandDefaultPos){var startPos=this.start, startLoc=this.startLoc;var expr=this.parseExprOps(noIn, refShorthandDefaultPos);if(refShorthandDefaultPos && refShorthandDefaultPos.start)return expr;if(this.eat(tt.question)){var node=this.startNodeAt(startPos, startLoc);node.test = expr;node.consequent = this.parseMaybeAssign();this.expect(tt.colon);node.alternate = this.parseMaybeAssign(noIn);return this.finishNode(node, "ConditionalExpression");}return expr;};pp.parseExprOps = function(noIn, refShorthandDefaultPos){var startPos=this.start, startLoc=this.startLoc;var expr=this.parseMaybeUnary(refShorthandDefaultPos);if(refShorthandDefaultPos && refShorthandDefaultPos.start)return expr;return this.parseExprOp(expr, startPos, startLoc, -1, noIn);};pp.parseExprOp = function(left, leftStartPos, leftStartLoc, minPrec, noIn){var prec=this.type.binop;if(Array.isArray(leftStartPos)){if(this.options.locations && noIn === undefined){noIn = minPrec;minPrec = leftStartLoc;leftStartLoc = leftStartPos[1];leftStartPos = leftStartPos[0];}}if(prec != null && (!noIn || this.type !== tt._in)){if(prec > minPrec){var node=this.startNodeAt(leftStartPos, leftStartLoc);node.left = left;node.operator = this.value;var op=this.type;this.next();var startPos=this.start, startLoc=this.startLoc;node.right = this.parseExprOp(this.parseMaybeUnary(), startPos, startLoc, prec, noIn);this.finishNode(node, op === tt.logicalOR || op === tt.logicalAND?"LogicalExpression":"BinaryExpression");return this.parseExprOp(node, leftStartPos, leftStartLoc, minPrec, noIn);}}return left;};pp.parseMaybeUnary = function(refShorthandDefaultPos){if(this.type.prefix){var node=this.startNode(), update=this.type === tt.incDec;node.operator = this.value;node.prefix = true;this.next();node.argument = this.parseMaybeUnary();if(refShorthandDefaultPos && refShorthandDefaultPos.start)this.unexpected(refShorthandDefaultPos.start);if(update)this.checkLVal(node.argument);else if(this.strict && node.operator === "delete" && node.argument.type === "Identifier")this.raise(node.start, "Deleting local variable in strict mode");return this.finishNode(node, update?"UpdateExpression":"UnaryExpression");}var startPos=this.start, startLoc=this.startLoc;var expr=this.parseExprSubscripts(refShorthandDefaultPos);if(refShorthandDefaultPos && refShorthandDefaultPos.start)return expr;while(this.type.postfix && !this.canInsertSemicolon()) {var node=this.startNodeAt(startPos, startLoc);node.operator = this.value;node.prefix = false;node.argument = expr;this.checkLVal(expr);this.next();expr = this.finishNode(node, "UpdateExpression");}return expr;};pp.parseExprSubscripts = function(refShorthandDefaultPos){var startPos=this.start, startLoc=this.startLoc;var expr=this.parseExprAtom(refShorthandDefaultPos);if(refShorthandDefaultPos && refShorthandDefaultPos.start)return expr;return this.parseSubscripts(expr, startPos, startLoc);};pp.parseSubscripts = function(base, startPos, startLoc, noCalls){if(Array.isArray(startPos)){if(this.options.locations && noCalls === undefined){noCalls = startLoc;startLoc = startPos[1];startPos = startPos[0];}}for(;;) {if(this.eat(tt.dot)){var node=this.startNodeAt(startPos, startLoc);node.object = base;node.property = this.parseIdent(true);node.computed = false;base = this.finishNode(node, "MemberExpression");}else if(this.eat(tt.bracketL)){var node=this.startNodeAt(startPos, startLoc);node.object = base;node.property = this.parseExpression();node.computed = true;this.expect(tt.bracketR);base = this.finishNode(node, "MemberExpression");}else if(!noCalls && this.eat(tt.parenL)){var node=this.startNodeAt(startPos, startLoc);node.callee = base;node.arguments = this.parseExprList(tt.parenR, false);base = this.finishNode(node, "CallExpression");}else if(this.type === tt.backQuote){var node=this.startNodeAt(startPos, startLoc);node.tag = base;node.quasi = this.parseTemplate();base = this.finishNode(node, "TaggedTemplateExpression");}else {return base;}}};pp.parseExprAtom = function(refShorthandDefaultPos){var node=undefined, canBeArrow=this.potentialArrowAt == this.start;switch(this.type){case tt._this:case tt._super:var type=this.type === tt._this?"ThisExpression":"Super";node = this.startNode();this.next();return this.finishNode(node, type);case tt._yield:if(this.inGenerator)this.unexpected();case tt.name:var startPos=this.start, startLoc=this.startLoc;var id=this.parseIdent(this.type !== tt.name);if(canBeArrow && !this.canInsertSemicolon() && this.eat(tt.arrow))return this.parseArrowExpression(this.startNodeAt(startPos, startLoc), [id]);return id;case tt.regexp:var value=this.value;node = this.parseLiteral(value.value);node.regex = {pattern:value.pattern, flags:value.flags};return node;case tt.num:case tt.string:return this.parseLiteral(this.value);case tt._null:case tt._true:case tt._false:node = this.startNode();node.value = this.type === tt._null?null:this.type === tt._true;node.raw = this.type.keyword;this.next();return this.finishNode(node, "Literal");case tt.parenL:return this.parseParenAndDistinguishExpression(canBeArrow);case tt.bracketL:node = this.startNode();this.next();if(this.options.ecmaVersion >= 7 && this.type === tt._for){return this.parseComprehension(node, false);}node.elements = this.parseExprList(tt.bracketR, true, true, refShorthandDefaultPos);return this.finishNode(node, "ArrayExpression");case tt.braceL:return this.parseObj(false, refShorthandDefaultPos);case tt._function:node = this.startNode();this.next();return this.parseFunction(node, false);case tt._class:return this.parseClass(this.startNode(), false);case tt._new:return this.parseNew();case tt.backQuote:return this.parseTemplate();default:this.unexpected();}};pp.parseLiteral = function(value){var node=this.startNode();node.value = value;node.raw = this.input.slice(this.start, this.end);this.next();return this.finishNode(node, "Literal");};pp.parseParenExpression = function(){this.expect(tt.parenL);var val=this.parseExpression();this.expect(tt.parenR);return val;};pp.parseParenAndDistinguishExpression = function(canBeArrow){var startPos=this.start, startLoc=this.startLoc, val=undefined;if(this.options.ecmaVersion >= 6){this.next();if(this.options.ecmaVersion >= 7 && this.type === tt._for){return this.parseComprehension(this.startNodeAt(startPos, startLoc), true);}var innerStartPos=this.start, innerStartLoc=this.startLoc;var exprList=[], first=true;var refShorthandDefaultPos={start:0}, spreadStart=undefined, innerParenStart=undefined;while(this.type !== tt.parenR) {first?first = false:this.expect(tt.comma);if(this.type === tt.ellipsis){spreadStart = this.start;exprList.push(this.parseParenItem(this.parseRest()));break;}else {if(this.type === tt.parenL && !innerParenStart){innerParenStart = this.start;}exprList.push(this.parseMaybeAssign(false, refShorthandDefaultPos, this.parseParenItem));}}var innerEndPos=this.start, innerEndLoc=this.startLoc;this.expect(tt.parenR);if(canBeArrow && !this.canInsertSemicolon() && this.eat(tt.arrow)){if(innerParenStart)this.unexpected(innerParenStart);return this.parseParenArrowList(startPos, startLoc, exprList);}if(!exprList.length)this.unexpected(this.lastTokStart);if(spreadStart)this.unexpected(spreadStart);if(refShorthandDefaultPos.start)this.unexpected(refShorthandDefaultPos.start);if(exprList.length > 1){val = this.startNodeAt(innerStartPos, innerStartLoc);val.expressions = exprList;this.finishNodeAt(val, "SequenceExpression", innerEndPos, innerEndLoc);}else {val = exprList[0];}}else {val = this.parseParenExpression();}if(this.options.preserveParens){var par=this.startNodeAt(startPos, startLoc);par.expression = val;return this.finishNode(par, "ParenthesizedExpression");}else {return val;}};pp.parseParenItem = function(item){return item;};pp.parseParenArrowList = function(startPos, startLoc, exprList){return this.parseArrowExpression(this.startNodeAt(startPos, startLoc), exprList);};var empty=[];pp.parseNew = function(){var node=this.startNode();var meta=this.parseIdent(true);if(this.options.ecmaVersion >= 6 && this.eat(tt.dot)){node.meta = meta;node.property = this.parseIdent(true);if(node.property.name !== "target")this.raise(node.property.start, "The only valid meta property for new is new.target");return this.finishNode(node, "MetaProperty");}var startPos=this.start, startLoc=this.startLoc;node.callee = this.parseSubscripts(this.parseExprAtom(), startPos, startLoc, true);if(this.eat(tt.parenL))node.arguments = this.parseExprList(tt.parenR, false);else node.arguments = empty;return this.finishNode(node, "NewExpression");};pp.parseTemplateElement = function(){var elem=this.startNode();elem.value = {raw:this.input.slice(this.start, this.end), cooked:this.value};this.next();elem.tail = this.type === tt.backQuote;return this.finishNode(elem, "TemplateElement");};pp.parseTemplate = function(){var node=this.startNode();this.next();node.expressions = [];var curElt=this.parseTemplateElement();node.quasis = [curElt];while(!curElt.tail) {this.expect(tt.dollarBraceL);node.expressions.push(this.parseExpression());this.expect(tt.braceR);node.quasis.push(curElt = this.parseTemplateElement());}this.next();return this.finishNode(node, "TemplateLiteral");};pp.parseObj = function(isPattern, refShorthandDefaultPos){var node=this.startNode(), first=true, propHash={};node.properties = [];this.next();while(!this.eat(tt.braceR)) {if(!first){this.expect(tt.comma);if(this.afterTrailingComma(tt.braceR))break;}else first = false;var prop=this.startNode(), isGenerator=undefined, startPos=undefined, startLoc=undefined;if(this.options.ecmaVersion >= 6){prop.method = false;prop.shorthand = false;if(isPattern || refShorthandDefaultPos){startPos = this.start;startLoc = this.startLoc;}if(!isPattern)isGenerator = this.eat(tt.star);}this.parsePropertyName(prop);this.parsePropertyValue(prop, isPattern, isGenerator, startPos, startLoc, refShorthandDefaultPos);this.checkPropClash(prop, propHash);node.properties.push(this.finishNode(prop, "Property"));}return this.finishNode(node, isPattern?"ObjectPattern":"ObjectExpression");};pp.parsePropertyValue = function(prop, isPattern, isGenerator, startPos, startLoc, refShorthandDefaultPos){if(this.eat(tt.colon)){prop.value = isPattern?this.parseMaybeDefault(this.start, this.startLoc):this.parseMaybeAssign(false, refShorthandDefaultPos);prop.kind = "init";}else if(this.options.ecmaVersion >= 6 && this.type === tt.parenL){if(isPattern)this.unexpected();prop.kind = "init";prop.method = true;prop.value = this.parseMethod(isGenerator);}else if(this.options.ecmaVersion >= 5 && !prop.computed && prop.key.type === "Identifier" && (prop.key.name === "get" || prop.key.name === "set") && (this.type != tt.comma && this.type != tt.braceR)){if(isGenerator || isPattern)this.unexpected();prop.kind = prop.key.name;this.parsePropertyName(prop);prop.value = this.parseMethod(false);}else if(this.options.ecmaVersion >= 6 && !prop.computed && prop.key.type === "Identifier"){prop.kind = "init";if(isPattern){if(this.isKeyword(prop.key.name) || this.strict && (reservedWords.strictBind(prop.key.name) || reservedWords.strict(prop.key.name)) || !this.options.allowReserved && this.isReservedWord(prop.key.name))this.raise(prop.key.start, "Binding " + prop.key.name);prop.value = this.parseMaybeDefault(startPos, startLoc, prop.key);}else if(this.type === tt.eq && refShorthandDefaultPos){if(!refShorthandDefaultPos.start)refShorthandDefaultPos.start = this.start;prop.value = this.parseMaybeDefault(startPos, startLoc, prop.key);}else {prop.value = prop.key;}prop.shorthand = true;}else this.unexpected();};pp.parsePropertyName = function(prop){if(this.options.ecmaVersion >= 6){if(this.eat(tt.bracketL)){prop.computed = true;prop.key = this.parseMaybeAssign();this.expect(tt.bracketR);return prop.key;}else {prop.computed = false;}}return prop.key = this.type === tt.num || this.type === tt.string?this.parseExprAtom():this.parseIdent(true);};pp.initFunction = function(node){node.id = null;if(this.options.ecmaVersion >= 6){node.generator = false;node.expression = false;}};pp.parseMethod = function(isGenerator){var node=this.startNode();this.initFunction(node);this.expect(tt.parenL);node.params = this.parseBindingList(tt.parenR, false, false);var allowExpressionBody=undefined;if(this.options.ecmaVersion >= 6){node.generator = isGenerator;allowExpressionBody = true;}else {allowExpressionBody = false;}this.parseFunctionBody(node, allowExpressionBody);return this.finishNode(node, "FunctionExpression");};pp.parseArrowExpression = function(node, params){this.initFunction(node);node.params = this.toAssignableList(params, true);this.parseFunctionBody(node, true);return this.finishNode(node, "ArrowFunctionExpression");};pp.parseFunctionBody = function(node, allowExpression){var isExpression=allowExpression && this.type !== tt.braceL;if(isExpression){node.body = this.parseMaybeAssign();node.expression = true;}else {var oldInFunc=this.inFunction, oldInGen=this.inGenerator, oldLabels=this.labels;this.inFunction = true;this.inGenerator = node.generator;this.labels = [];node.body = this.parseBlock(true);node.expression = false;this.inFunction = oldInFunc;this.inGenerator = oldInGen;this.labels = oldLabels;}if(this.strict || !isExpression && node.body.body.length && this.isUseStrict(node.body.body[0])){var nameHash={}, oldStrict=this.strict;this.strict = true;if(node.id)this.checkLVal(node.id, true);for(var i=0; i < node.params.length; i++) {this.checkLVal(node.params[i], true, nameHash);}this.strict = oldStrict;}};pp.parseExprList = function(close, allowTrailingComma, allowEmpty, refShorthandDefaultPos){var elts=[], first=true;while(!this.eat(close)) {if(!first){this.expect(tt.comma);if(allowTrailingComma && this.afterTrailingComma(close))break;}else first = false;if(allowEmpty && this.type === tt.comma){elts.push(null);}else {if(this.type === tt.ellipsis)elts.push(this.parseSpread(refShorthandDefaultPos));else elts.push(this.parseMaybeAssign(false, refShorthandDefaultPos));}}return elts;};pp.parseIdent = function(liberal){var node=this.startNode();if(liberal && this.options.allowReserved == "never")liberal = false;if(this.type === tt.name){if(!liberal && (!this.options.allowReserved && this.isReservedWord(this.value) || this.strict && reservedWords.strict(this.value) && (this.options.ecmaVersion >= 6 || this.input.slice(this.start, this.end).indexOf("\\") == -1)))this.raise(this.start, "The keyword '" + this.value + "' is reserved");node.name = this.value;}else if(liberal && this.type.keyword){node.name = this.type.keyword;}else {this.unexpected();}this.next();return this.finishNode(node, "Identifier");};pp.parseYield = function(){var node=this.startNode();this.next();if(this.type == tt.semi || this.canInsertSemicolon() || this.type != tt.star && !this.type.startsExpr){node.delegate = false;node.argument = null;}else {node.delegate = this.eat(tt.star);node.argument = this.parseMaybeAssign();}return this.finishNode(node, "YieldExpression");};pp.parseComprehension = function(node, isGenerator){node.blocks = [];while(this.type === tt._for) {var block=this.startNode();this.next();this.expect(tt.parenL);block.left = this.parseBindingAtom();this.checkLVal(block.left, true);this.expectContextual("of");block.right = this.parseExpression();this.expect(tt.parenR);node.blocks.push(this.finishNode(block, "ComprehensionBlock"));}node.filter = this.eat(tt._if)?this.parseParenExpression():null;node.body = this.parseExpression();this.expect(isGenerator?tt.parenR:tt.bracketR);node.generator = isGenerator;return this.finishNode(node, "ComprehensionExpression");};}, {"./identifier":7, "./state":13, "./tokentype":17, "./util":18}], 7:[function(_dereq_, module, exports){"use strict";exports.isIdentifierStart = isIdentifierStart;exports.isIdentifierChar = isIdentifierChar;exports.__esModule = true;function makePredicate(words){words = words.split(" ");var f="", cats=[];out: for(var i=0; i < words.length; ++i) {for(var j=0; j < cats.length; ++j) {if(cats[j][0].length == words[i].length){cats[j].push(words[i]);continue out;}}cats.push([words[i]]);}function compareTo(arr){if(arr.length == 1){return f += "return str === " + JSON.stringify(arr[0]) + ";";}f += "switch(str){";for(var i=0; i < arr.length; ++i) {f += "case " + JSON.stringify(arr[i]) + ":";}f += "return true}return false;";}if(cats.length > 3){cats.sort(function(a, b){return b.length - a.length;});f += "switch(str.length){";for(var i=0; i < cats.length; ++i) {var cat=cats[i];f += "case " + cat[0].length + ":";compareTo(cat);}f += "}";}else {compareTo(words);}return new Function("str", f);}var reservedWords={3:makePredicate("abstract boolean byte char class double enum export extends final float goto implements import int interface long native package private protected public short static super synchronized throws transient volatile"), 5:makePredicate("class enum extends super const export import"), 6:makePredicate("enum await"), strict:makePredicate("implements interface let package private protected public static yield"), strictBind:makePredicate("eval arguments")};exports.reservedWords = reservedWords;var ecma5AndLessKeywords="break case catch continue debugger default do else finally for function if return switch throw try var while with null true false instanceof typeof void delete new in this";var keywords={5:makePredicate(ecma5AndLessKeywords), 6:makePredicate(ecma5AndLessKeywords + " let const class extends export import yield super")};exports.keywords = keywords;var nonASCIIidentifierStartChars="ªµºÀ-ÖØ-öø-ˁˆ-ˑˠ-ˤˬˮͰ-ʹͶͷͺ-ͽͿΆΈ-ΊΌΎ-ΡΣ-ϵϷ-ҁҊ-ԯԱ-Ֆՙա-ևא-תװ-ײؠ-يٮٯٱ-ۓەۥۦۮۯۺ-ۼۿܐܒ-ܯݍ-ޥޱߊ-ߪߴߵߺࠀ-ࠕࠚࠤࠨࡀ-ࡘࢠ-ࢲऄ-हऽॐक़-ॡॱ-ঀঅ-ঌএঐও-নপ-রলশ-হঽৎড়ঢ়য়-ৡৰৱਅ-ਊਏਐਓ-ਨਪ-ਰਲਲ਼ਵਸ਼ਸਹਖ਼-ੜਫ਼ੲ-ੴઅ-ઍએ-ઑઓ-નપ-રલળવ-હઽૐૠૡଅ-ଌଏଐଓ-ନପ-ରଲଳଵ-ହଽଡ଼ଢ଼ୟ-ୡୱஃஅ-ஊஎ-ஐஒ-கஙசஜஞடணதந-பம-ஹௐఅ-ఌఎ-ఐఒ-నప-హఽౘౙౠౡಅ-ಌಎ-ಐಒ-ನಪ-ಳವ-ಹಽೞೠೡೱೲഅ-ഌഎ-ഐഒ-ഺഽൎൠൡൺ-ൿඅ-ඖක-නඳ-රලව-ෆก-ะาำเ-ๆກຂຄງຈຊຍດ-ທນ-ຟມ-ຣລວສຫອ-ະາຳຽເ-ໄໆໜ-ໟༀཀ-ཇཉ-ཬྈ-ྌက-ဪဿၐ-ၕၚ-ၝၡၥၦၮ-ၰၵ-ႁႎႠ-ჅჇჍა-ჺჼ-ቈቊ-ቍቐ-ቖቘቚ-ቝበ-ኈኊ-ኍነ-ኰኲ-ኵኸ-ኾዀዂ-ዅወ-ዖዘ-ጐጒ-ጕጘ-ፚᎀ-ᎏᎠ-Ᏼᐁ-ᙬᙯ-ᙿᚁ-ᚚᚠ-ᛪᛮ-ᛸᜀ-ᜌᜎ-ᜑᜠ-ᜱᝀ-ᝑᝠ-ᝬᝮ-ᝰក-ឳៗៜᠠ-ᡷᢀ-ᢨᢪᢰ-ᣵᤀ-ᤞᥐ-ᥭᥰ-ᥴᦀ-ᦫᧁ-ᧇᨀ-ᨖᨠ-ᩔᪧᬅ-ᬳᭅ-ᭋᮃ-ᮠᮮᮯᮺ-ᯥᰀ-ᰣᱍ-ᱏᱚ-ᱽᳩ-ᳬᳮ-ᳱᳵᳶᴀ-ᶿḀ-ἕἘ-Ἕἠ-ὅὈ-Ὅὐ-ὗὙὛὝὟ-ώᾀ-ᾴᾶ-ᾼιῂ-ῄῆ-ῌῐ-ΐῖ-Ίῠ-Ῥῲ-ῴῶ-ῼⁱⁿₐ-ₜℂℇℊ-ℓℕ℘-ℝℤΩℨK-ℹℼ-ℿⅅ-ⅉⅎⅠ-ↈⰀ-Ⱞⰰ-ⱞⱠ-ⳤⳫ-ⳮⳲⳳⴀ-ⴥⴧⴭⴰ-ⵧⵯⶀ-ⶖⶠ-ⶦⶨ-ⶮⶰ-ⶶⶸ-ⶾⷀ-ⷆⷈ-ⷎⷐ-ⷖⷘ-ⷞ々-〇〡-〩〱-〵〸-〼ぁ-ゖ゛-ゟァ-ヺー-ヿㄅ-ㄭㄱ-ㆎㆠ-ㆺㇰ-ㇿ㐀-䶵一-鿌ꀀ-ꒌꓐ-ꓽꔀ-ꘌꘐ-ꘟꘪꘫꙀ-ꙮꙿ-ꚝꚠ-ꛯꜗ-ꜟꜢ-ꞈꞋ-ꞎꞐ-ꞭꞰꞱꟷ-ꠁꠃ-ꠅꠇ-ꠊꠌ-ꠢꡀ-ꡳꢂ-ꢳꣲ-ꣷꣻꤊ-ꤥꤰ-ꥆꥠ-ꥼꦄ-ꦲꧏꧠ-ꧤꧦ-ꧯꧺ-ꧾꨀ-ꨨꩀ-ꩂꩄ-ꩋꩠ-ꩶꩺꩾ-ꪯꪱꪵꪶꪹ-ꪽꫀꫂꫛ-ꫝꫠ-ꫪꫲ-ꫴꬁ-ꬆꬉ-ꬎꬑ-ꬖꬠ-ꬦꬨ-ꬮꬰ-ꭚꭜ-ꭟꭤꭥꯀ-ꯢ가-힣ힰ-ퟆퟋ-ퟻ豈-舘並-龎ﬀ-ﬆﬓ-ﬗיִײַ-ﬨשׁ-זּטּ-לּמּנּסּףּפּצּ-ﮱﯓ-ﴽﵐ-ﶏﶒ-ﷇﷰ-ﷻﹰ-ﹴﹶ-ﻼＡ-Ｚａ-ｚｦ-ﾾￂ-ￇￊ-ￏￒ-ￗￚ-ￜ";var nonASCIIidentifierChars="‌‍·̀-ͯ·҃-֑҇-ׇֽֿׁׂׅׄؐ-ًؚ-٩ٰۖ-ۜ۟-۪ۤۧۨ-ۭ۰-۹ܑܰ-݊ަ-ް߀-߉߫-߳ࠖ-࠙ࠛ-ࠣࠥ-ࠧࠩ-࡙࠭-࡛ࣤ-ःऺ-़ा-ॏ॑-ॗॢॣ०-९ঁ-ঃ়া-ৄেৈো-্ৗৢৣ০-৯ਁ-ਃ਼ਾ-ੂੇੈੋ-੍ੑ੦-ੱੵઁ-ઃ઼ા-ૅે-ૉો-્ૢૣ૦-૯ଁ-ଃ଼ା-ୄେୈୋ-୍ୖୗୢୣ୦-୯ஂா-ூெ-ைொ-்ௗ௦-௯ఀ-ఃా-ౄె-ైొ-్ౕౖౢౣ౦-౯ಁ-ಃ಼ಾ-ೄೆ-ೈೊ-್ೕೖೢೣ೦-೯ഁ-ഃാ-ൄെ-ൈൊ-്ൗൢൣ൦-൯ංඃ්ා-ුූෘ-ෟ෦-෯ෲෳัิ-ฺ็-๎๐-๙ັິ-ູົຼ່-ໍ໐-໙༘༙༠-༩༹༵༷༾༿ཱ-྄྆྇ྍ-ྗྙ-ྼ࿆ါ-ှ၀-၉ၖ-ၙၞ-ၠၢ-ၤၧ-ၭၱ-ၴႂ-ႍႏ-ႝ፝-፟፩-፱ᜒ-᜔ᜲ-᜴ᝒᝓᝲᝳ឴-៓៝០-៩᠋-᠍᠐-᠙ᢩᤠ-ᤫᤰ-᤻᥆-᥏ᦰ-ᧀᧈᧉ᧐-᧚ᨗ-ᨛᩕ-ᩞ᩠-᩿᩼-᪉᪐-᪙᪰-᪽ᬀ-ᬄ᬴-᭄᭐-᭙᭫-᭳ᮀ-ᮂᮡ-ᮭ᮰-᮹᯦-᯳ᰤ-᰷᱀-᱉᱐-᱙᳐-᳔᳒-᳨᳭ᳲ-᳴᳸᳹᷀-᷵᷼-᷿‿⁀⁔⃐-⃥⃜⃡-⃰⳯-⵿⳱ⷠ-〪ⷿ-゙゚〯꘠-꘩꙯ꙴ-꙽ꚟ꛰꛱ꠂ꠆ꠋꠣ-ꠧꢀꢁꢴ-꣄꣐-꣙꣠-꣱꤀-꤉ꤦ-꤭ꥇ-꥓ꦀ-ꦃ꦳-꧀꧐-꧙ꧥ꧰-꧹ꨩ-ꨶꩃꩌꩍ꩐-꩙ꩻ-ꩽꪰꪲ-ꪴꪷꪸꪾ꪿꫁ꫫ-ꫯꫵ꫶ꯣ-ꯪ꯬꯭꯰-꯹ﬞ︀-️︠-︭︳︴﹍-﹏０-９＿";var nonASCIIidentifierStart=new RegExp("[" + nonASCIIidentifierStartChars + "]");var nonASCIIidentifier=new RegExp("[" + nonASCIIidentifierStartChars + nonASCIIidentifierChars + "]");nonASCIIidentifierStartChars = nonASCIIidentifierChars = null;var astralIdentifierStartCodes=[0, 11, 2, 25, 2, 18, 2, 1, 2, 14, 3, 13, 35, 122, 70, 52, 268, 28, 4, 48, 48, 31, 17, 26, 6, 37, 11, 29, 3, 35, 5, 7, 2, 4, 43, 157, 99, 39, 9, 51, 157, 310, 10, 21, 11, 7, 153, 5, 3, 0, 2, 43, 2, 1, 4, 0, 3, 22, 11, 22, 10, 30, 98, 21, 11, 25, 71, 55, 7, 1, 65, 0, 16, 3, 2, 2, 2, 26, 45, 28, 4, 28, 36, 7, 2, 27, 28, 53, 11, 21, 11, 18, 14, 17, 111, 72, 955, 52, 76, 44, 33, 24, 27, 35, 42, 34, 4, 0, 13, 47, 15, 3, 22, 0, 38, 17, 2, 24, 133, 46, 39, 7, 3, 1, 3, 21, 2, 6, 2, 1, 2, 4, 4, 0, 32, 4, 287, 47, 21, 1, 2, 0, 185, 46, 82, 47, 21, 0, 60, 42, 502, 63, 32, 0, 449, 56, 1288, 920, 104, 110, 2962, 1070, 13266, 568, 8, 30, 114, 29, 19, 47, 17, 3, 32, 20, 6, 18, 881, 68, 12, 0, 67, 12, 16481, 1, 3071, 106, 6, 12, 4, 8, 8, 9, 5991, 84, 2, 70, 2, 1, 3, 0, 3, 1, 3, 3, 2, 11, 2, 0, 2, 6, 2, 64, 2, 3, 3, 7, 2, 6, 2, 27, 2, 3, 2, 4, 2, 0, 4, 6, 2, 339, 3, 24, 2, 24, 2, 30, 2, 24, 2, 30, 2, 24, 2, 30, 2, 24, 2, 30, 2, 24, 2, 7, 4149, 196, 1340, 3, 2, 26, 2, 1, 2, 0, 3, 0, 2, 9, 2, 3, 2, 0, 2, 0, 7, 0, 5, 0, 2, 0, 2, 0, 2, 2, 2, 1, 2, 0, 3, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 1, 2, 0, 3, 3, 2, 6, 2, 3, 2, 3, 2, 0, 2, 9, 2, 16, 6, 2, 2, 4, 2, 16, 4421, 42710, 42, 4148, 12, 221, 16355, 541];var astralIdentifierCodes=[509, 0, 227, 0, 150, 4, 294, 9, 1368, 2, 2, 1, 6, 3, 41, 2, 5, 0, 166, 1, 1306, 2, 54, 14, 32, 9, 16, 3, 46, 10, 54, 9, 7, 2, 37, 13, 2, 9, 52, 0, 13, 2, 49, 13, 16, 9, 83, 11, 168, 11, 6, 9, 8, 2, 57, 0, 2, 6, 3, 1, 3, 2, 10, 0, 11, 1, 3, 6, 4, 4, 316, 19, 13, 9, 214, 6, 3, 8, 112, 16, 16, 9, 82, 12, 9, 9, 535, 9, 20855, 9, 135, 4, 60, 6, 26, 9, 1016, 45, 17, 3, 19723, 1, 5319, 4, 4, 5, 9, 7, 3, 6, 31, 3, 149, 2, 1418, 49, 4305, 6, 792618, 239];function isInAstralSet(code, set){var pos=65536;for(var i=0; i < set.length; i += 2) {pos += set[i];if(pos > code){return false;}pos += set[i + 1];if(pos >= code){return true;}}}function isIdentifierStart(code, astral){if(code < 65){return code === 36;}if(code < 91){return true;}if(code < 97){return code === 95;}if(code < 123){return true;}if(code <= 65535){return code >= 170 && nonASCIIidentifierStart.test(String.fromCharCode(code));}if(astral === false){return false;}return isInAstralSet(code, astralIdentifierStartCodes);}function isIdentifierChar(code, astral){if(code < 48){return code === 36;}if(code < 58){return true;}if(code < 65){return false;}if(code < 91){return true;}if(code < 97){return code === 95;}if(code < 123){return true;}if(code <= 65535){return code >= 170 && nonASCIIidentifier.test(String.fromCharCode(code));}if(astral === false){return false;}return isInAstralSet(code, astralIdentifierStartCodes) || isInAstralSet(code, astralIdentifierCodes);}}, {}], 8:[function(_dereq_, module, exports){"use strict";var _classCallCheck=function _classCallCheck(instance, Constructor){if(!(instance instanceof Constructor)){throw new TypeError("Cannot call a class as a function");}};exports.getLineInfo = getLineInfo;exports.__esModule = true;var Parser=_dereq_("./state").Parser;var lineBreakG=_dereq_("./whitespace").lineBreakG;var deprecate=_dereq_("util").deprecate;var Position=exports.Position = (function(){function Position(line, col){_classCallCheck(this, Position);this.line = line;this.column = col;}Position.prototype.offset = function offset(n){return new Position(this.line, this.column + n);};return Position;})();var SourceLocation=exports.SourceLocation = function SourceLocation(p, start, end){_classCallCheck(this, SourceLocation);this.start = start;this.end = end;if(p.sourceFile !== null)this.source = p.sourceFile;};function getLineInfo(input, offset){for(var line=1, cur=0;;) {lineBreakG.lastIndex = cur;var match=lineBreakG.exec(input);if(match && match.index < offset){++line;cur = match.index + match[0].length;}else {return new Position(line, offset - cur);}}}var pp=Parser.prototype;pp.raise = function(pos, message){var loc=getLineInfo(this.input, pos);message += " (" + loc.line + ":" + loc.column + ")";var err=new SyntaxError(message);err.pos = pos;err.loc = loc;err.raisedAt = this.pos;throw err;};pp.curPosition = function(){return new Position(this.curLine, this.pos - this.lineStart);};pp.markPosition = function(){return this.options.locations?[this.start, this.startLoc]:this.start;};}, {"./state":13, "./whitespace":19, util:5}], 9:[function(_dereq_, module, exports){"use strict";var tt=_dereq_("./tokentype").types;var Parser=_dereq_("./state").Parser;var reservedWords=_dereq_("./identifier").reservedWords;var has=_dereq_("./util").has;var pp=Parser.prototype;pp.toAssignable = function(node, isBinding){if(this.options.ecmaVersion >= 6 && node){switch(node.type){case "Identifier":case "ObjectPattern":case "ArrayPattern":case "AssignmentPattern":break;case "ObjectExpression":node.type = "ObjectPattern";for(var i=0; i < node.properties.length; i++) {var prop=node.properties[i];if(prop.kind !== "init")this.raise(prop.key.start, "Object pattern can't contain getter or setter");this.toAssignable(prop.value, isBinding);}break;case "ArrayExpression":node.type = "ArrayPattern";this.toAssignableList(node.elements, isBinding);break;case "AssignmentExpression":if(node.operator === "="){node.type = "AssignmentPattern";}else {this.raise(node.left.end, "Only '=' operator can be used for specifying default value.");}break;case "ParenthesizedExpression":node.expression = this.toAssignable(node.expression, isBinding);break;case "MemberExpression":if(!isBinding)break;default:this.raise(node.start, "Assigning to rvalue");}}return node;};pp.toAssignableList = function(exprList, isBinding){var end=exprList.length;if(end){var last=exprList[end - 1];if(last && last.type == "RestElement"){--end;}else if(last && last.type == "SpreadElement"){last.type = "RestElement";var arg=last.argument;this.toAssignable(arg, isBinding);if(arg.type !== "Identifier" && arg.type !== "MemberExpression" && arg.type !== "ArrayPattern")this.unexpected(arg.start);--end;}}for(var i=0; i < end; i++) {var elt=exprList[i];if(elt)this.toAssignable(elt, isBinding);}return exprList;};pp.parseSpread = function(refShorthandDefaultPos){var node=this.startNode();this.next();node.argument = this.parseMaybeAssign(refShorthandDefaultPos);return this.finishNode(node, "SpreadElement");};pp.parseRest = function(){var node=this.startNode();this.next();node.argument = this.type === tt.name || this.type === tt.bracketL?this.parseBindingAtom():this.unexpected();return this.finishNode(node, "RestElement");};pp.parseBindingAtom = function(){if(this.options.ecmaVersion < 6)return this.parseIdent();switch(this.type){case tt.name:return this.parseIdent();case tt.bracketL:var node=this.startNode();this.next();node.elements = this.parseBindingList(tt.bracketR, true, true);return this.finishNode(node, "ArrayPattern");case tt.braceL:return this.parseObj(true);default:this.unexpected();}};pp.parseBindingList = function(close, allowEmpty, allowTrailingComma){var elts=[], first=true;while(!this.eat(close)) {if(first)first = false;else this.expect(tt.comma);if(allowEmpty && this.type === tt.comma){elts.push(null);}else if(allowTrailingComma && this.afterTrailingComma(close)){break;}else if(this.type === tt.ellipsis){var rest=this.parseRest();this.parseBindingListItem(rest);elts.push(rest);this.expect(close);break;}else {var elem=this.parseMaybeDefault(this.start, this.startLoc);this.parseBindingListItem(elem);elts.push(elem);}}return elts;};pp.parseBindingListItem = function(param){return param;};pp.parseMaybeDefault = function(startPos, startLoc, left){if(Array.isArray(startPos)){if(this.options.locations && noCalls === undefined){left = startLoc;startLoc = startPos[1];startPos = startPos[0];}}left = left || this.parseBindingAtom();if(!this.eat(tt.eq))return left;var node=this.startNodeAt(startPos, startLoc);node.operator = "=";node.left = left;node.right = this.parseMaybeAssign();return this.finishNode(node, "AssignmentPattern");};pp.checkLVal = function(expr, isBinding, checkClashes){switch(expr.type){case "Identifier":if(this.strict && (reservedWords.strictBind(expr.name) || reservedWords.strict(expr.name)))this.raise(expr.start, (isBinding?"Binding ":"Assigning to ") + expr.name + " in strict mode");if(checkClashes){if(has(checkClashes, expr.name))this.raise(expr.start, "Argument name clash in strict mode");checkClashes[expr.name] = true;}break;case "MemberExpression":if(isBinding)this.raise(expr.start, (isBinding?"Binding":"Assigning to") + " member expression");break;case "ObjectPattern":for(var i=0; i < expr.properties.length; i++) {this.checkLVal(expr.properties[i].value, isBinding, checkClashes);}break;case "ArrayPattern":for(var i=0; i < expr.elements.length; i++) {var elem=expr.elements[i];if(elem)this.checkLVal(elem, isBinding, checkClashes);}break;case "AssignmentPattern":this.checkLVal(expr.left, isBinding, checkClashes);break;case "RestElement":this.checkLVal(expr.argument, isBinding, checkClashes);break;case "ParenthesizedExpression":this.checkLVal(expr.expression, isBinding, checkClashes);break;default:this.raise(expr.start, (isBinding?"Binding":"Assigning to") + " rvalue");}};}, {"./identifier":7, "./state":13, "./tokentype":17, "./util":18}], 10:[function(_dereq_, module, exports){"use strict";var _classCallCheck=function _classCallCheck(instance, Constructor){if(!(instance instanceof Constructor)){throw new TypeError("Cannot call a class as a function");}};exports.__esModule = true;var Parser=_dereq_("./state").Parser;var SourceLocation=_dereq_("./location").SourceLocation;var pp=Parser.prototype;var Node=exports.Node = function Node(){_classCallCheck(this, Node);};pp.startNode = function(){var node=new Node();node.start = this.start;if(this.options.locations)node.loc = new SourceLocation(this, this.startLoc);if(this.options.directSourceFile)node.sourceFile = this.options.directSourceFile;if(this.options.ranges)node.range = [this.start, 0];return node;};pp.startNodeAt = function(pos, loc){var node=new Node();if(Array.isArray(pos)){if(this.options.locations && loc === undefined){loc = pos[1];pos = pos[0];}}node.start = pos;if(this.options.locations)node.loc = new SourceLocation(this, loc);if(this.options.directSourceFile)node.sourceFile = this.options.directSourceFile;if(this.options.ranges)node.range = [pos, 0];return node;};pp.finishNode = function(node, type){node.type = type;node.end = this.lastTokEnd;if(this.options.locations)node.loc.end = this.lastTokEndLoc;if(this.options.ranges)node.range[1] = this.lastTokEnd;return node;};pp.finishNodeAt = function(node, type, pos, loc){node.type = type;if(Array.isArray(pos)){if(this.options.locations && loc === undefined){loc = pos[1];pos = pos[0];}}node.end = pos;if(this.options.locations)node.loc.end = loc;if(this.options.ranges)node.range[1] = pos;return node;};}, {"./location":8, "./state":13}], 11:[function(_dereq_, module, exports){"use strict";exports.getOptions = getOptions;exports.__esModule = true;var _util=_dereq_("./util");var has=_util.has;var isArray=_util.isArray;var SourceLocation=_dereq_("./location").SourceLocation;var defaultOptions={ecmaVersion:5, sourceType:"script", onInsertedSemicolon:null, onTrailingComma:null, allowReserved:true, allowReturnOutsideFunction:false, allowImportExportEverywhere:false, allowHashBang:false, locations:false, onToken:null, onComment:null, ranges:false, program:null, sourceFile:null, directSourceFile:null, preserveParens:false, plugins:{}};exports.defaultOptions = defaultOptions;function getOptions(opts){var options={};for(var opt in defaultOptions) {options[opt] = opts && has(opts, opt)?opts[opt]:defaultOptions[opt];}if(isArray(options.onToken)){(function(){var tokens=options.onToken;options.onToken = function(token){return tokens.push(token);};})();}if(isArray(options.onComment))options.onComment = pushComment(options, options.onComment);return options;}function pushComment(options, array){return function(block, text, start, end, startLoc, endLoc){var comment={type:block?"Block":"Line", value:text, start:start, end:end};if(options.locations)comment.loc = new SourceLocation(this, startLoc, endLoc);if(options.ranges)comment.range = [start, end];array.push(comment);};}}, {"./location":8, "./util":18}], 12:[function(_dereq_, module, exports){"use strict";var tt=_dereq_("./tokentype").types;var Parser=_dereq_("./state").Parser;var lineBreak=_dereq_("./whitespace").lineBreak;var pp=Parser.prototype;pp.isUseStrict = function(stmt){return this.options.ecmaVersion >= 5 && stmt.type === "ExpressionStatement" && stmt.expression.type === "Literal" && stmt.expression.value === "use strict";};pp.eat = function(type){if(this.type === type){this.next();return true;}else {return false;}};pp.isContextual = function(name){return this.type === tt.name && this.value === name;};pp.eatContextual = function(name){return this.value === name && this.eat(tt.name);};pp.expectContextual = function(name){if(!this.eatContextual(name))this.unexpected();};pp.canInsertSemicolon = function(){return this.type === tt.eof || this.type === tt.braceR || lineBreak.test(this.input.slice(this.lastTokEnd, this.start));};pp.insertSemicolon = function(){if(this.canInsertSemicolon()){if(this.options.onInsertedSemicolon)this.options.onInsertedSemicolon(this.lastTokEnd, this.lastTokEndLoc);return true;}};pp.semicolon = function(){if(!this.eat(tt.semi) && !this.insertSemicolon())this.unexpected();};pp.afterTrailingComma = function(tokType){if(this.type == tokType){if(this.options.onTrailingComma)this.options.onTrailingComma(this.lastTokStart, this.lastTokStartLoc);this.next();return true;}};pp.expect = function(type){this.eat(type) || this.unexpected();};pp.unexpected = function(pos){this.raise(pos != null?pos:this.start, "Unexpected token");};}, {"./state":13, "./tokentype":17, "./whitespace":19}], 13:[function(_dereq_, module, exports){"use strict";exports.Parser = Parser;exports.__esModule = true;var _identifier=_dereq_("./identifier");var reservedWords=_identifier.reservedWords;var keywords=_identifier.keywords;var tt=_dereq_("./tokentype").types;var lineBreak=_dereq_("./whitespace").lineBreak;function Parser(options, input, startPos){this.options = options;this.sourceFile = this.options.sourceFile || null;this.isKeyword = keywords[this.options.ecmaVersion >= 6?6:5];this.isReservedWord = reservedWords[this.options.ecmaVersion];this.input = input;this.loadPlugins(this.options.plugins);if(startPos){this.pos = startPos;this.lineStart = Math.max(0, this.input.lastIndexOf("\n", startPos));this.curLine = this.input.slice(0, this.lineStart).split(lineBreak).length;}else {this.pos = this.lineStart = 0;this.curLine = 1;}this.type = tt.eof;this.value = null;this.start = this.end = this.pos;this.startLoc = this.endLoc = null;this.lastTokEndLoc = this.lastTokStartLoc = null;this.lastTokStart = this.lastTokEnd = this.pos;this.context = this.initialContext();this.exprAllowed = true;this.strict = this.inModule = this.options.sourceType === "module";this.potentialArrowAt = -1;this.inFunction = this.inGenerator = false;this.labels = [];if(this.pos === 0 && this.options.allowHashBang && this.input.slice(0, 2) === "#!")this.skipLineComment(2);}Parser.prototype.extend = function(name, f){this[name] = f(this[name]);};var plugins={};exports.plugins = plugins;Parser.prototype.loadPlugins = function(plugins){for(var _name in plugins) {var plugin=exports.plugins[_name];if(!plugin)throw new Error("Plugin '" + _name + "' not found");plugin(this, plugins[_name]);}};}, {"./identifier":7, "./tokentype":17, "./whitespace":19}], 14:[function(_dereq_, module, exports){"use strict";var tt=_dereq_("./tokentype").types;var Parser=_dereq_("./state").Parser;var lineBreak=_dereq_("./whitespace").lineBreak;var pp=Parser.prototype;pp.parseTopLevel = function(node){var first=true;if(!node.body)node.body = [];while(this.type !== tt.eof) {var stmt=this.parseStatement(true, true);node.body.push(stmt);if(first && this.isUseStrict(stmt))this.setStrict(true);first = false;}this.next();if(this.options.ecmaVersion >= 6){node.sourceType = this.options.sourceType;}return this.finishNode(node, "Program");};var loopLabel={kind:"loop"}, switchLabel={kind:"switch"};pp.parseStatement = function(declaration, topLevel){var starttype=this.type, node=this.startNode();switch(starttype){case tt._break:case tt._continue:return this.parseBreakContinueStatement(node, starttype.keyword);case tt._debugger:return this.parseDebuggerStatement(node);case tt._do:return this.parseDoStatement(node);case tt._for:return this.parseForStatement(node);case tt._function:if(!declaration && this.options.ecmaVersion >= 6)this.unexpected();return this.parseFunctionStatement(node);case tt._class:if(!declaration)this.unexpected();return this.parseClass(node, true);case tt._if:return this.parseIfStatement(node);case tt._return:return this.parseReturnStatement(node);case tt._switch:return this.parseSwitchStatement(node);case tt._throw:return this.parseThrowStatement(node);case tt._try:return this.parseTryStatement(node);case tt._let:case tt._const:if(!declaration)this.unexpected();case tt._var:return this.parseVarStatement(node, starttype);case tt._while:return this.parseWhileStatement(node);case tt._with:return this.parseWithStatement(node);case tt.braceL:return this.parseBlock();case tt.semi:return this.parseEmptyStatement(node);case tt._export:case tt._import:if(!this.options.allowImportExportEverywhere){if(!topLevel)this.raise(this.start, "'import' and 'export' may only appear at the top level");if(!this.inModule)this.raise(this.start, "'import' and 'export' may appear only with 'sourceType: module'");}return starttype === tt._import?this.parseImport(node):this.parseExport(node);default:var maybeName=this.value, expr=this.parseExpression();if(starttype === tt.name && expr.type === "Identifier" && this.eat(tt.colon))return this.parseLabeledStatement(node, maybeName, expr);else return this.parseExpressionStatement(node, expr);}};pp.parseBreakContinueStatement = function(node, keyword){var isBreak=keyword == "break";this.next();if(this.eat(tt.semi) || this.insertSemicolon())node.label = null;else if(this.type !== tt.name)this.unexpected();else {node.label = this.parseIdent();this.semicolon();}for(var i=0; i < this.labels.length; ++i) {var lab=this.labels[i];if(node.label == null || lab.name === node.label.name){if(lab.kind != null && (isBreak || lab.kind === "loop"))break;if(node.label && isBreak)break;}}if(i === this.labels.length)this.raise(node.start, "Unsyntactic " + keyword);return this.finishNode(node, isBreak?"BreakStatement":"ContinueStatement");};pp.parseDebuggerStatement = function(node){this.next();this.semicolon();return this.finishNode(node, "DebuggerStatement");};pp.parseDoStatement = function(node){this.next();this.labels.push(loopLabel);node.body = this.parseStatement(false);this.labels.pop();this.expect(tt._while);node.test = this.parseParenExpression();if(this.options.ecmaVersion >= 6)this.eat(tt.semi);else this.semicolon();return this.finishNode(node, "DoWhileStatement");};pp.parseForStatement = function(node){this.next();this.labels.push(loopLabel);this.expect(tt.parenL);if(this.type === tt.semi)return this.parseFor(node, null);if(this.type === tt._var || this.type === tt._let || this.type === tt._const){var _init=this.startNode(), varKind=this.type;this.next();this.parseVar(_init, true, varKind);this.finishNode(_init, "VariableDeclaration");if((this.type === tt._in || this.options.ecmaVersion >= 6 && this.isContextual("of")) && _init.declarations.length === 1 && !(varKind !== tt._var && _init.declarations[0].init))return this.parseForIn(node, _init);return this.parseFor(node, _init);}var refShorthandDefaultPos={start:0};var init=this.parseExpression(true, refShorthandDefaultPos);if(this.type === tt._in || this.options.ecmaVersion >= 6 && this.isContextual("of")){this.toAssignable(init);this.checkLVal(init);return this.parseForIn(node, init);}else if(refShorthandDefaultPos.start){this.unexpected(refShorthandDefaultPos.start);}return this.parseFor(node, init);};pp.parseFunctionStatement = function(node){this.next();return this.parseFunction(node, true);};pp.parseIfStatement = function(node){this.next();node.test = this.parseParenExpression();node.consequent = this.parseStatement(false);node.alternate = this.eat(tt._else)?this.parseStatement(false):null;return this.finishNode(node, "IfStatement");};pp.parseReturnStatement = function(node){if(!this.inFunction && !this.options.allowReturnOutsideFunction)this.raise(this.start, "'return' outside of function");this.next();if(this.eat(tt.semi) || this.insertSemicolon())node.argument = null;else {node.argument = this.parseExpression();this.semicolon();}return this.finishNode(node, "ReturnStatement");};pp.parseSwitchStatement = function(node){this.next();node.discriminant = this.parseParenExpression();node.cases = [];this.expect(tt.braceL);this.labels.push(switchLabel);for(var cur, sawDefault; this.type != tt.braceR;) {if(this.type === tt._case || this.type === tt._default){var isCase=this.type === tt._case;if(cur)this.finishNode(cur, "SwitchCase");node.cases.push(cur = this.startNode());cur.consequent = [];this.next();if(isCase){cur.test = this.parseExpression();}else {if(sawDefault)this.raise(this.lastTokStart, "Multiple default clauses");sawDefault = true;cur.test = null;}this.expect(tt.colon);}else {if(!cur)this.unexpected();cur.consequent.push(this.parseStatement(true));}}if(cur)this.finishNode(cur, "SwitchCase");this.next();this.labels.pop();return this.finishNode(node, "SwitchStatement");};pp.parseThrowStatement = function(node){this.next();if(lineBreak.test(this.input.slice(this.lastTokEnd, this.start)))this.raise(this.lastTokEnd, "Illegal newline after throw");node.argument = this.parseExpression();this.semicolon();return this.finishNode(node, "ThrowStatement");};var empty=[];pp.parseTryStatement = function(node){this.next();node.block = this.parseBlock();node.handler = null;if(this.type === tt._catch){var clause=this.startNode();this.next();this.expect(tt.parenL);clause.param = this.parseBindingAtom();this.checkLVal(clause.param, true);this.expect(tt.parenR);clause.guard = null;clause.body = this.parseBlock();node.handler = this.finishNode(clause, "CatchClause");}node.guardedHandlers = empty;node.finalizer = this.eat(tt._finally)?this.parseBlock():null;if(!node.handler && !node.finalizer)this.raise(node.start, "Missing catch or finally clause");return this.finishNode(node, "TryStatement");};pp.parseVarStatement = function(node, kind){this.next();this.parseVar(node, false, kind);this.semicolon();return this.finishNode(node, "VariableDeclaration");};pp.parseWhileStatement = function(node){this.next();node.test = this.parseParenExpression();this.labels.push(loopLabel);node.body = this.parseStatement(false);this.labels.pop();return this.finishNode(node, "WhileStatement");};pp.parseWithStatement = function(node){if(this.strict)this.raise(this.start, "'with' in strict mode");this.next();node.object = this.parseParenExpression();node.body = this.parseStatement(false);return this.finishNode(node, "WithStatement");};pp.parseEmptyStatement = function(node){this.next();return this.finishNode(node, "EmptyStatement");};pp.parseLabeledStatement = function(node, maybeName, expr){for(var i=0; i < this.labels.length; ++i) {if(this.labels[i].name === maybeName)this.raise(expr.start, "Label '" + maybeName + "' is already declared");}var kind=this.type.isLoop?"loop":this.type === tt._switch?"switch":null;this.labels.push({name:maybeName, kind:kind});node.body = this.parseStatement(true);this.labels.pop();node.label = expr;return this.finishNode(node, "LabeledStatement");};pp.parseExpressionStatement = function(node, expr){node.expression = expr;this.semicolon();return this.finishNode(node, "ExpressionStatement");};pp.parseBlock = function(allowStrict){var node=this.startNode(), first=true, oldStrict=undefined;node.body = [];this.expect(tt.braceL);while(!this.eat(tt.braceR)) {var stmt=this.parseStatement(true);node.body.push(stmt);if(first && allowStrict && this.isUseStrict(stmt)){oldStrict = this.strict;this.setStrict(this.strict = true);}first = false;}if(oldStrict === false)this.setStrict(false);return this.finishNode(node, "BlockStatement");};pp.parseFor = function(node, init){node.init = init;this.expect(tt.semi);node.test = this.type === tt.semi?null:this.parseExpression();this.expect(tt.semi);node.update = this.type === tt.parenR?null:this.parseExpression();this.expect(tt.parenR);node.body = this.parseStatement(false);this.labels.pop();return this.finishNode(node, "ForStatement");};pp.parseForIn = function(node, init){var type=this.type === tt._in?"ForInStatement":"ForOfStatement";this.next();node.left = init;node.right = this.parseExpression();this.expect(tt.parenR);node.body = this.parseStatement(false);this.labels.pop();return this.finishNode(node, type);};pp.parseVar = function(node, isFor, kind){node.declarations = [];node.kind = kind.keyword;for(;;) {var decl=this.startNode();this.parseVarId(decl);if(this.eat(tt.eq)){decl.init = this.parseMaybeAssign(isFor);}else if(kind === tt._const && !(this.type === tt._in || this.options.ecmaVersion >= 6 && this.isContextual("of"))){this.unexpected();}else if(decl.id.type != "Identifier" && !(isFor && (this.type === tt._in || this.isContextual("of")))){this.raise(this.lastTokEnd, "Complex binding patterns require an initialization value");}else {decl.init = null;}node.declarations.push(this.finishNode(decl, "VariableDeclarator"));if(!this.eat(tt.comma))break;}return node;};pp.parseVarId = function(decl){decl.id = this.parseBindingAtom();this.checkLVal(decl.id, true);};pp.parseFunction = function(node, isStatement, allowExpressionBody){this.initFunction(node);if(this.options.ecmaVersion >= 6)node.generator = this.eat(tt.star);if(isStatement || this.type === tt.name)node.id = this.parseIdent();this.parseFunctionParams(node);this.parseFunctionBody(node, allowExpressionBody);return this.finishNode(node, isStatement?"FunctionDeclaration":"FunctionExpression");};pp.parseFunctionParams = function(node){this.expect(tt.parenL);node.params = this.parseBindingList(tt.parenR, false, false);};pp.parseClass = function(node, isStatement){this.next();this.parseClassId(node, isStatement);this.parseClassSuper(node);var classBody=this.startNode();var hadConstructor=false;classBody.body = [];this.expect(tt.braceL);while(!this.eat(tt.braceR)) {if(this.eat(tt.semi))continue;var method=this.startNode();var isGenerator=this.eat(tt.star);var isMaybeStatic=this.type === tt.name && this.value === "static";this.parsePropertyName(method);method["static"] = isMaybeStatic && this.type !== tt.parenL;if(method["static"]){if(isGenerator)this.unexpected();isGenerator = this.eat(tt.star);this.parsePropertyName(method);}method.kind = "method";if(!method.computed){var key=method.key;var isGetSet=false;if(!isGenerator && key.type === "Identifier" && this.type !== tt.parenL && (key.name === "get" || key.name === "set")){isGetSet = true;method.kind = key.name;key = this.parsePropertyName(method);}if(!method["static"] && (key.type === "Identifier" && key.name === "constructor" || key.type === "Literal" && key.value === "constructor")){if(hadConstructor)this.raise(key.start, "Duplicate constructor in the same class");if(isGetSet)this.raise(key.start, "Constructor can't have get/set modifier");if(isGenerator)this.raise(key.start, "Constructor can't be a generator");method.kind = "constructor";hadConstructor = true;}}this.parseClassMethod(classBody, method, isGenerator);}node.body = this.finishNode(classBody, "ClassBody");return this.finishNode(node, isStatement?"ClassDeclaration":"ClassExpression");};pp.parseClassMethod = function(classBody, method, isGenerator){method.value = this.parseMethod(isGenerator);classBody.body.push(this.finishNode(method, "MethodDefinition"));};pp.parseClassId = function(node, isStatement){node.id = this.type === tt.name?this.parseIdent():isStatement?this.unexpected():null;};pp.parseClassSuper = function(node){node.superClass = this.eat(tt._extends)?this.parseExprSubscripts():null;};pp.parseExport = function(node){this.next();if(this.eat(tt.star)){this.expectContextual("from");node.source = this.type === tt.string?this.parseExprAtom():this.unexpected();this.semicolon();return this.finishNode(node, "ExportAllDeclaration");}if(this.eat(tt._default)){var expr=this.parseMaybeAssign();var needsSemi=true;if(expr.type == "FunctionExpression" || expr.type == "ClassExpression"){needsSemi = false;if(expr.id){expr.type = expr.type == "FunctionExpression"?"FunctionDeclaration":"ClassDeclaration";}}node.declaration = expr;if(needsSemi)this.semicolon();return this.finishNode(node, "ExportDefaultDeclaration");}if(this.shouldParseExportStatement()){node.declaration = this.parseStatement(true);node.specifiers = [];node.source = null;}else {node.declaration = null;node.specifiers = this.parseExportSpecifiers();if(this.eatContextual("from")){node.source = this.type === tt.string?this.parseExprAtom():this.unexpected();}else {node.source = null;}this.semicolon();}return this.finishNode(node, "ExportNamedDeclaration");};pp.shouldParseExportStatement = function(){return this.type.keyword;};pp.parseExportSpecifiers = function(){var nodes=[], first=true;this.expect(tt.braceL);while(!this.eat(tt.braceR)) {if(!first){this.expect(tt.comma);if(this.afterTrailingComma(tt.braceR))break;}else first = false;var node=this.startNode();node.local = this.parseIdent(this.type === tt._default);node.exported = this.eatContextual("as")?this.parseIdent(true):node.local;nodes.push(this.finishNode(node, "ExportSpecifier"));}return nodes;};pp.parseImport = function(node){this.next();if(this.type === tt.string){node.specifiers = empty;node.source = this.parseExprAtom();node.kind = "";}else {node.specifiers = this.parseImportSpecifiers();this.expectContextual("from");node.source = this.type === tt.string?this.parseExprAtom():this.unexpected();}this.semicolon();return this.finishNode(node, "ImportDeclaration");};pp.parseImportSpecifiers = function(){var nodes=[], first=true;if(this.type === tt.name){var node=this.startNode();node.local = this.parseIdent();this.checkLVal(node.local, true);nodes.push(this.finishNode(node, "ImportDefaultSpecifier"));if(!this.eat(tt.comma))return nodes;}if(this.type === tt.star){var node=this.startNode();this.next();this.expectContextual("as");node.local = this.parseIdent();this.checkLVal(node.local, true);nodes.push(this.finishNode(node, "ImportNamespaceSpecifier"));return nodes;}this.expect(tt.braceL);while(!this.eat(tt.braceR)) {if(!first){this.expect(tt.comma);if(this.afterTrailingComma(tt.braceR))break;}else first = false;var node=this.startNode();node.imported = this.parseIdent(true);node.local = this.eatContextual("as")?this.parseIdent():node.imported;this.checkLVal(node.local, true);nodes.push(this.finishNode(node, "ImportSpecifier"));}return nodes;};}, {"./state":13, "./tokentype":17, "./whitespace":19}], 15:[function(_dereq_, module, exports){"use strict";var _classCallCheck=function _classCallCheck(instance, Constructor){if(!(instance instanceof Constructor)){throw new TypeError("Cannot call a class as a function");}};exports.__esModule = true;var Parser=_dereq_("./state").Parser;var tt=_dereq_("./tokentype").types;var lineBreak=_dereq_("./whitespace").lineBreak;var TokContext=exports.TokContext = function TokContext(token, isExpr, preserveSpace, override){_classCallCheck(this, TokContext);this.token = token;this.isExpr = isExpr;this.preserveSpace = preserveSpace;this.override = override;};var types={b_stat:new TokContext("{", false), b_expr:new TokContext("{", true), b_tmpl:new TokContext("${", true), p_stat:new TokContext("(", false), p_expr:new TokContext("(", true), q_tmpl:new TokContext("`", true, true, function(p){return p.readTmplToken();}), f_expr:new TokContext("function", true)};exports.types = types;var pp=Parser.prototype;pp.initialContext = function(){return [types.b_stat];};pp.braceIsBlock = function(prevType){var parent=undefined;if(prevType === tt.colon && (parent = this.curContext()).token == "{")return !parent.isExpr;if(prevType === tt._return)return lineBreak.test(this.input.slice(this.lastTokEnd, this.start));if(prevType === tt._else || prevType === tt.semi || prevType === tt.eof)return true;if(prevType == tt.braceL)return this.curContext() === types.b_stat;return !this.exprAllowed;};pp.updateContext = function(prevType){var update=undefined, type=this.type;if(type.keyword && prevType == tt.dot)this.exprAllowed = false;else if(update = type.updateContext)update.call(this, prevType);else this.exprAllowed = type.beforeExpr;};tt.parenR.updateContext = tt.braceR.updateContext = function(){if(this.context.length == 1){this.exprAllowed = true;return;}var out=this.context.pop();if(out === types.b_stat && this.curContext() === types.f_expr){this.context.pop();this.exprAllowed = false;}else if(out === types.b_tmpl){this.exprAllowed = true;}else {this.exprAllowed = !out.isExpr;}};tt.braceL.updateContext = function(prevType){this.context.push(this.braceIsBlock(prevType)?types.b_stat:types.b_expr);this.exprAllowed = true;};tt.dollarBraceL.updateContext = function(){this.context.push(types.b_tmpl);this.exprAllowed = true;};tt.parenL.updateContext = function(prevType){var statementParens=prevType === tt._if || prevType === tt._for || prevType === tt._with || prevType === tt._while;this.context.push(statementParens?types.p_stat:types.p_expr);this.exprAllowed = true;};tt.incDec.updateContext = function(){};tt._function.updateContext = function(){if(this.curContext() !== types.b_stat)this.context.push(types.f_expr);this.exprAllowed = false;};tt.backQuote.updateContext = function(){if(this.curContext() === types.q_tmpl)this.context.pop();else this.context.push(types.q_tmpl);this.exprAllowed = false;};}, {"./state":13, "./tokentype":17, "./whitespace":19}], 16:[function(_dereq_, module, exports){"use strict";var _classCallCheck=function _classCallCheck(instance, Constructor){if(!(instance instanceof Constructor)){throw new TypeError("Cannot call a class as a function");}};exports.__esModule = true;var _identifier=_dereq_("./identifier");var isIdentifierStart=_identifier.isIdentifierStart;var isIdentifierChar=_identifier.isIdentifierChar;var _tokentype=_dereq_("./tokentype");var tt=_tokentype.types;var keywordTypes=_tokentype.keywords;var Parser=_dereq_("./state").Parser;var SourceLocation=_dereq_("./location").SourceLocation;var _whitespace=_dereq_("./whitespace");var lineBreak=_whitespace.lineBreak;var lineBreakG=_whitespace.lineBreakG;var isNewLine=_whitespace.isNewLine;var nonASCIIwhitespace=_whitespace.nonASCIIwhitespace;var Token=exports.Token = function Token(p){_classCallCheck(this, Token);this.type = p.type;this.value = p.value;this.start = p.start;this.end = p.end;if(p.options.locations)this.loc = new SourceLocation(p, p.startLoc, p.endLoc);if(p.options.ranges)this.range = [p.start, p.end];};var pp=Parser.prototype;var isRhino=typeof Packages !== "undefined";pp.next = function(){if(this.options.onToken)this.options.onToken(new Token(this));this.lastTokEnd = this.end;this.lastTokStart = this.start;this.lastTokEndLoc = this.endLoc;this.lastTokStartLoc = this.startLoc;this.nextToken();};pp.getToken = function(){this.next();return new Token(this);};if(typeof Symbol !== "undefined")pp[Symbol.iterator] = function(){var self=this;return {next:function next(){var token=self.getToken();return {done:token.type === tt.eof, value:token};}};};pp.setStrict = function(strict){this.strict = strict;if(this.type !== tt.num && this.type !== tt.string)return;this.pos = this.start;if(this.options.locations){while(this.pos < this.lineStart) {this.lineStart = this.input.lastIndexOf("\n", this.lineStart - 2) + 1;--this.curLine;}}this.nextToken();};pp.curContext = function(){return this.context[this.context.length - 1];};pp.nextToken = function(){var curContext=this.curContext();if(!curContext || !curContext.preserveSpace)this.skipSpace();this.start = this.pos;if(this.options.locations)this.startLoc = this.curPosition();if(this.pos >= this.input.length)return this.finishToken(tt.eof);if(curContext.override)return curContext.override(this);else this.readToken(this.fullCharCodeAtPos());};pp.readToken = function(code){if(isIdentifierStart(code, this.options.ecmaVersion >= 6) || code === 92)return this.readWord();return this.getTokenFromCode(code);};pp.fullCharCodeAtPos = function(){var code=this.input.charCodeAt(this.pos);if(code <= 55295 || code >= 57344)return code;var next=this.input.charCodeAt(this.pos + 1);return (code << 10) + next - 56613888;};pp.skipBlockComment = function(){var startLoc=this.options.onComment && this.options.locations && this.curPosition();var start=this.pos, end=this.input.indexOf("*/", this.pos += 2);if(end === -1)this.raise(this.pos - 2, "Unterminated comment");this.pos = end + 2;if(this.options.locations){lineBreakG.lastIndex = start;var match=undefined;while((match = lineBreakG.exec(this.input)) && match.index < this.pos) {++this.curLine;this.lineStart = match.index + match[0].length;}}if(this.options.onComment)this.options.onComment(true, this.input.slice(start + 2, end), start, this.pos, startLoc, this.options.locations && this.curPosition());};pp.skipLineComment = function(startSkip){var start=this.pos;var startLoc=this.options.onComment && this.options.locations && this.curPosition();var ch=this.input.charCodeAt(this.pos += startSkip);while(this.pos < this.input.length && ch !== 10 && ch !== 13 && ch !== 8232 && ch !== 8233) {++this.pos;ch = this.input.charCodeAt(this.pos);}if(this.options.onComment)this.options.onComment(false, this.input.slice(start + startSkip, this.pos), start, this.pos, startLoc, this.options.locations && this.curPosition());};pp.skipSpace = function(){while(this.pos < this.input.length) {var ch=this.input.charCodeAt(this.pos);if(ch === 32){++this.pos;}else if(ch === 13){++this.pos;var next=this.input.charCodeAt(this.pos);if(next === 10){++this.pos;}if(this.options.locations){++this.curLine;this.lineStart = this.pos;}}else if(ch === 10 || ch === 8232 || ch === 8233){++this.pos;if(this.options.locations){++this.curLine;this.lineStart = this.pos;}}else if(ch > 8 && ch < 14){++this.pos;}else if(ch === 47){var next=this.input.charCodeAt(this.pos + 1);if(next === 42){this.skipBlockComment();}else if(next === 47){this.skipLineComment(2);}else break;}else if(ch === 160){++this.pos;}else if(ch >= 5760 && nonASCIIwhitespace.test(String.fromCharCode(ch))){++this.pos;}else {break;}}};pp.finishToken = function(type, val){this.end = this.pos;if(this.options.locations)this.endLoc = this.curPosition();var prevType=this.type;this.type = type;this.value = val;this.updateContext(prevType);};pp.readToken_dot = function(){var next=this.input.charCodeAt(this.pos + 1);if(next >= 48 && next <= 57)return this.readNumber(true);var next2=this.input.charCodeAt(this.pos + 2);if(this.options.ecmaVersion >= 6 && next === 46 && next2 === 46){this.pos += 3;return this.finishToken(tt.ellipsis);}else {++this.pos;return this.finishToken(tt.dot);}};pp.readToken_slash = function(){var next=this.input.charCodeAt(this.pos + 1);if(this.exprAllowed){++this.pos;return this.readRegexp();}if(next === 61)return this.finishOp(tt.assign, 2);return this.finishOp(tt.slash, 1);};pp.readToken_mult_modulo = function(code){var next=this.input.charCodeAt(this.pos + 1);if(next === 61)return this.finishOp(tt.assign, 2);return this.finishOp(code === 42?tt.star:tt.modulo, 1);};pp.readToken_pipe_amp = function(code){var next=this.input.charCodeAt(this.pos + 1);if(next === code)return this.finishOp(code === 124?tt.logicalOR:tt.logicalAND, 2);if(next === 61)return this.finishOp(tt.assign, 2);return this.finishOp(code === 124?tt.bitwiseOR:tt.bitwiseAND, 1);};pp.readToken_caret = function(){var next=this.input.charCodeAt(this.pos + 1);if(next === 61)return this.finishOp(tt.assign, 2);return this.finishOp(tt.bitwiseXOR, 1);};pp.readToken_plus_min = function(code){var next=this.input.charCodeAt(this.pos + 1);if(next === code){if(next == 45 && this.input.charCodeAt(this.pos + 2) == 62 && lineBreak.test(this.input.slice(this.lastTokEnd, this.pos))){this.skipLineComment(3);this.skipSpace();return this.nextToken();}return this.finishOp(tt.incDec, 2);}if(next === 61)return this.finishOp(tt.assign, 2);return this.finishOp(tt.plusMin, 1);};pp.readToken_lt_gt = function(code){var next=this.input.charCodeAt(this.pos + 1);var size=1;if(next === code){size = code === 62 && this.input.charCodeAt(this.pos + 2) === 62?3:2;if(this.input.charCodeAt(this.pos + size) === 61)return this.finishOp(tt.assign, size + 1);return this.finishOp(tt.bitShift, size);}if(next == 33 && code == 60 && this.input.charCodeAt(this.pos + 2) == 45 && this.input.charCodeAt(this.pos + 3) == 45){if(this.inModule)this.unexpected();this.skipLineComment(4);this.skipSpace();return this.nextToken();}if(next === 61)size = this.input.charCodeAt(this.pos + 2) === 61?3:2;return this.finishOp(tt.relational, size);};pp.readToken_eq_excl = function(code){var next=this.input.charCodeAt(this.pos + 1);if(next === 61)return this.finishOp(tt.equality, this.input.charCodeAt(this.pos + 2) === 61?3:2);if(code === 61 && next === 62 && this.options.ecmaVersion >= 6){this.pos += 2;return this.finishToken(tt.arrow);}return this.finishOp(code === 61?tt.eq:tt.prefix, 1);};pp.getTokenFromCode = function(code){switch(code){case 46:return this.readToken_dot();case 40:++this.pos;return this.finishToken(tt.parenL);case 41:++this.pos;return this.finishToken(tt.parenR);case 59:++this.pos;return this.finishToken(tt.semi);case 44:++this.pos;return this.finishToken(tt.comma);case 91:++this.pos;return this.finishToken(tt.bracketL);case 93:++this.pos;return this.finishToken(tt.bracketR);case 123:++this.pos;return this.finishToken(tt.braceL);case 125:++this.pos;return this.finishToken(tt.braceR);case 58:++this.pos;return this.finishToken(tt.colon);case 63:++this.pos;return this.finishToken(tt.question);case 96:if(this.options.ecmaVersion < 6)break;++this.pos;return this.finishToken(tt.backQuote);case 48:var next=this.input.charCodeAt(this.pos + 1);if(next === 120 || next === 88)return this.readRadixNumber(16);if(this.options.ecmaVersion >= 6){if(next === 111 || next === 79)return this.readRadixNumber(8);if(next === 98 || next === 66)return this.readRadixNumber(2);}case 49:case 50:case 51:case 52:case 53:case 54:case 55:case 56:case 57:return this.readNumber(false);case 34:case 39:return this.readString(code);case 47:return this.readToken_slash();case 37:case 42:return this.readToken_mult_modulo(code);case 124:case 38:return this.readToken_pipe_amp(code);case 94:return this.readToken_caret();case 43:case 45:return this.readToken_plus_min(code);case 60:case 62:return this.readToken_lt_gt(code);case 61:case 33:return this.readToken_eq_excl(code);case 126:return this.finishOp(tt.prefix, 1);}this.raise(this.pos, "Unexpected character '" + codePointToString(code) + "'");};pp.finishOp = function(type, size){var str=this.input.slice(this.pos, this.pos + size);this.pos += size;return this.finishToken(type, str);};var regexpUnicodeSupport=false;try{new RegExp("￿", "u");regexpUnicodeSupport = true;}catch(e) {}pp.readRegexp = function(){var escaped=undefined, inClass=undefined, start=this.pos;for(;;) {if(this.pos >= this.input.length)this.raise(start, "Unterminated regular expression");var ch=this.input.charAt(this.pos);if(lineBreak.test(ch))this.raise(start, "Unterminated regular expression");if(!escaped){if(ch === "[")inClass = true;else if(ch === "]" && inClass)inClass = false;else if(ch === "/" && !inClass)break;escaped = ch === "\\";}else escaped = false;++this.pos;}var content=this.input.slice(start, this.pos);++this.pos;var mods=this.readWord1();var tmp=content;if(mods){var validFlags=/^[gmsiy]*$/;if(this.options.ecmaVersion >= 6)validFlags = /^[gmsiyu]*$/;if(!validFlags.test(mods))this.raise(start, "Invalid regular expression flag");if(mods.indexOf("u") >= 0 && !regexpUnicodeSupport){tmp = tmp.replace(/\\u([a-fA-F0-9]{4})|\\u\{([0-9a-fA-F]+)\}|[\uD800-\uDBFF][\uDC00-\uDFFF]/g, "x");}}var value=null;if(!isRhino){try{new RegExp(tmp);}catch(e) {if(e instanceof SyntaxError)this.raise(start, "Error parsing regular expression: " + e.message);this.raise(e);}try{value = new RegExp(content, mods);}catch(err) {}}return this.finishToken(tt.regexp, {pattern:content, flags:mods, value:value});};pp.readInt = function(radix, len){var start=this.pos, total=0;for(var i=0, e=len == null?Infinity:len; i < e; ++i) {var code=this.input.charCodeAt(this.pos), val=undefined;if(code >= 97)val = code - 97 + 10;else if(code >= 65)val = code - 65 + 10;else if(code >= 48 && code <= 57)val = code - 48;else val = Infinity;if(val >= radix)break;++this.pos;total = total * radix + val;}if(this.pos === start || len != null && this.pos - start !== len)return null;return total;};pp.readRadixNumber = function(radix){this.pos += 2;var val=this.readInt(radix);if(val == null)this.raise(this.start + 2, "Expected number in radix " + radix);if(isIdentifierStart(this.fullCharCodeAtPos()))this.raise(this.pos, "Identifier directly after number");return this.finishToken(tt.num, val);};pp.readNumber = function(startsWithDot){var start=this.pos, isFloat=false, octal=this.input.charCodeAt(this.pos) === 48;if(!startsWithDot && this.readInt(10) === null)this.raise(start, "Invalid number");if(this.input.charCodeAt(this.pos) === 46){++this.pos;this.readInt(10);isFloat = true;}var next=this.input.charCodeAt(this.pos);if(next === 69 || next === 101){next = this.input.charCodeAt(++this.pos);if(next === 43 || next === 45)++this.pos;if(this.readInt(10) === null)this.raise(start, "Invalid number");isFloat = true;}if(isIdentifierStart(this.fullCharCodeAtPos()))this.raise(this.pos, "Identifier directly after number");var str=this.input.slice(start, this.pos), val=undefined;if(isFloat)val = parseFloat(str);else if(!octal || str.length === 1)val = parseInt(str, 10);else if(/[89]/.test(str) || this.strict)this.raise(start, "Invalid number");else val = parseInt(str, 8);return this.finishToken(tt.num, val);};pp.readCodePoint = function(){var ch=this.input.charCodeAt(this.pos), code=undefined;if(ch === 123){if(this.options.ecmaVersion < 6)this.unexpected();++this.pos;code = this.readHexChar(this.input.indexOf("}", this.pos) - this.pos);++this.pos;if(code > 1114111)this.unexpected();}else {code = this.readHexChar(4);}return code;};function codePointToString(code){if(code <= 65535){return String.fromCharCode(code);}return String.fromCharCode((code - 65536 >> 10) + 55296, (code - 65536 & 1023) + 56320);}pp.readString = function(quote){var out="", chunkStart=++this.pos;for(;;) {if(this.pos >= this.input.length)this.raise(this.start, "Unterminated string constant");var ch=this.input.charCodeAt(this.pos);if(ch === quote)break;if(ch === 92){out += this.input.slice(chunkStart, this.pos);out += this.readEscapedChar();chunkStart = this.pos;}else {if(isNewLine(ch))this.raise(this.start, "Unterminated string constant");++this.pos;}}out += this.input.slice(chunkStart, this.pos++);return this.finishToken(tt.string, out);};pp.readTmplToken = function(){var out="", chunkStart=this.pos;for(;;) {if(this.pos >= this.input.length)this.raise(this.start, "Unterminated template");var ch=this.input.charCodeAt(this.pos);if(ch === 96 || ch === 36 && this.input.charCodeAt(this.pos + 1) === 123){if(this.pos === this.start && this.type === tt.template){if(ch === 36){this.pos += 2;return this.finishToken(tt.dollarBraceL);}else {++this.pos;return this.finishToken(tt.backQuote);}}out += this.input.slice(chunkStart, this.pos);return this.finishToken(tt.template, out);}if(ch === 92){out += this.input.slice(chunkStart, this.pos);out += this.readEscapedChar();chunkStart = this.pos;}else if(isNewLine(ch)){out += this.input.slice(chunkStart, this.pos);++this.pos;if(ch === 13 && this.input.charCodeAt(this.pos) === 10){++this.pos;out += "\n";}else {out += String.fromCharCode(ch);}if(this.options.locations){++this.curLine;this.lineStart = this.pos;}chunkStart = this.pos;}else {++this.pos;}}};pp.readEscapedChar = function(){var ch=this.input.charCodeAt(++this.pos);var octal=/^[0-7]+/.exec(this.input.slice(this.pos, this.pos + 3));if(octal)octal = octal[0];while(octal && parseInt(octal, 8) > 255) octal = octal.slice(0, -1);if(octal === "0")octal = null;++this.pos;if(octal){if(this.strict)this.raise(this.pos - 2, "Octal literal in strict mode");this.pos += octal.length - 1;return String.fromCharCode(parseInt(octal, 8));}else {switch(ch){case 110:return "\n";case 114:return "\r";case 120:return String.fromCharCode(this.readHexChar(2));case 117:return codePointToString(this.readCodePoint());case 116:return "\t";case 98:return "\b";case 118:return "\u000b";case 102:return "\f";case 48:return "\u0000";case 13:if(this.input.charCodeAt(this.pos) === 10)++this.pos;case 10:if(this.options.locations){this.lineStart = this.pos;++this.curLine;}return "";default:return String.fromCharCode(ch);}}};pp.readHexChar = function(len){var n=this.readInt(16, len);if(n === null)this.raise(this.start, "Bad character escape sequence");return n;};var containsEsc;pp.readWord1 = function(){containsEsc = false;var word="", first=true, chunkStart=this.pos;var astral=this.options.ecmaVersion >= 6;while(this.pos < this.input.length) {var ch=this.fullCharCodeAtPos();if(isIdentifierChar(ch, astral)){this.pos += ch <= 65535?1:2;}else if(ch === 92){containsEsc = true;word += this.input.slice(chunkStart, this.pos);var escStart=this.pos;if(this.input.charCodeAt(++this.pos) != 117)this.raise(this.pos, "Expecting Unicode escape sequence \\uXXXX");++this.pos;var esc=this.readCodePoint();if(!(first?isIdentifierStart:isIdentifierChar)(esc, astral))this.raise(escStart, "Invalid Unicode escape");word += codePointToString(esc);chunkStart = this.pos;}else {break;}first = false;}return word + this.input.slice(chunkStart, this.pos);};pp.readWord = function(){var word=this.readWord1();var type=tt.name;if((this.options.ecmaVersion >= 6 || !containsEsc) && this.isKeyword(word))type = keywordTypes[word];return this.finishToken(type, word);};}, {"./identifier":7, "./location":8, "./state":13, "./tokentype":17, "./whitespace":19}], 17:[function(_dereq_, module, exports){"use strict";var _classCallCheck=function _classCallCheck(instance, Constructor){if(!(instance instanceof Constructor)){throw new TypeError("Cannot call a class as a function");}};exports.__esModule = true;var TokenType=exports.TokenType = function TokenType(label){var conf=arguments[1] === undefined?{}:arguments[1];_classCallCheck(this, TokenType);this.label = label;this.keyword = conf.keyword;this.beforeExpr = !!conf.beforeExpr;this.startsExpr = !!conf.startsExpr;this.isLoop = !!conf.isLoop;this.isAssign = !!conf.isAssign;this.prefix = !!conf.prefix;this.postfix = !!conf.postfix;this.binop = conf.binop || null;this.updateContext = null;};function binop(name, prec){return new TokenType(name, {beforeExpr:true, binop:prec});}var beforeExpr={beforeExpr:true}, startsExpr={startsExpr:true};var types={num:new TokenType("num", startsExpr), regexp:new TokenType("regexp", startsExpr), string:new TokenType("string", startsExpr), name:new TokenType("name", startsExpr), eof:new TokenType("eof"), bracketL:new TokenType("[", {beforeExpr:true, startsExpr:true}), bracketR:new TokenType("]"), braceL:new TokenType("{", {beforeExpr:true, startsExpr:true}), braceR:new TokenType("}"), parenL:new TokenType("(", {beforeExpr:true, startsExpr:true}), parenR:new TokenType(")"), comma:new TokenType(",", beforeExpr), semi:new TokenType(";", beforeExpr), colon:new TokenType(":", beforeExpr), dot:new TokenType("."), question:new TokenType("?", beforeExpr), arrow:new TokenType("=>", beforeExpr), template:new TokenType("template"), ellipsis:new TokenType("...", beforeExpr), backQuote:new TokenType("`", startsExpr), dollarBraceL:new TokenType("${", {beforeExpr:true, startsExpr:true}), eq:new TokenType("=", {beforeExpr:true, isAssign:true}), assign:new TokenType("_=", {beforeExpr:true, isAssign:true}), incDec:new TokenType("++/--", {prefix:true, postfix:true, startsExpr:true}), prefix:new TokenType("prefix", {beforeExpr:true, prefix:true, startsExpr:true}), logicalOR:binop("||", 1), logicalAND:binop("&&", 2), bitwiseOR:binop("|", 3), bitwiseXOR:binop("^", 4), bitwiseAND:binop("&", 5), equality:binop("==/!=", 6), relational:binop("</>", 7), bitShift:binop("<</>>", 8), plusMin:new TokenType("+/-", {beforeExpr:true, binop:9, prefix:true, startsExpr:true}), modulo:binop("%", 10), star:binop("*", 10), slash:binop("/", 10)};exports.types = types;var keywords={};exports.keywords = keywords;function kw(name){var options=arguments[1] === undefined?{}:arguments[1];options.keyword = name;keywords[name] = types["_" + name] = new TokenType(name, options);}kw("break");kw("case", beforeExpr);kw("catch");kw("continue");kw("debugger");kw("default");kw("do", {isLoop:true});kw("else", beforeExpr);kw("finally");kw("for", {isLoop:true});kw("function", startsExpr);kw("if");kw("return", beforeExpr);kw("switch");kw("throw", beforeExpr);kw("try");kw("var");kw("let");kw("const");kw("while", {isLoop:true});kw("with");kw("new", {beforeExpr:true, startsExpr:true});kw("this", startsExpr);kw("super", startsExpr);kw("class");kw("extends", beforeExpr);kw("export");kw("import");kw("yield", {beforeExpr:true, startsExpr:true});kw("null", startsExpr);kw("true", startsExpr);kw("false", startsExpr);kw("in", {beforeExpr:true, binop:7});kw("instanceof", {beforeExpr:true, binop:7});kw("typeof", {beforeExpr:true, prefix:true, startsExpr:true});kw("void", {beforeExpr:true, prefix:true, startsExpr:true});kw("delete", {beforeExpr:true, prefix:true, startsExpr:true});}, {}], 18:[function(_dereq_, module, exports){"use strict";exports.isArray = isArray;exports.has = has;exports.__esModule = true;function isArray(obj){return Object.prototype.toString.call(obj) === "[object Array]";}function has(obj, propName){return Object.prototype.hasOwnProperty.call(obj, propName);}}, {}], 19:[function(_dereq_, module, exports){"use strict";exports.isNewLine = isNewLine;exports.__esModule = true;var lineBreak=/\r\n?|\n|\u2028|\u2029/;exports.lineBreak = lineBreak;var lineBreakG=new RegExp(lineBreak.source, "g");exports.lineBreakG = lineBreakG;function isNewLine(code){return code === 10 || code === 13 || code === 8232 || code == 8233;}var nonASCIIwhitespace=/[\u1680\u180e\u2000-\u200a\u202f\u205f\u3000\ufeff]/;exports.nonASCIIwhitespace = nonASCIIwhitespace;}, {}]}, {}, [1])(1);});

}).call(this,typeof global !== "undefined" ? global : typeof self !== "undefined" ? self : typeof window !== "undefined" ? window : {})
},{}],3:[function(_dereq_,module,exports){
"use strict";

module.exports = typeof acorn != "undefined" ? acorn : _dereq_("acorn");

},{"acorn":2}],4:[function(_dereq_,module,exports){
"use strict";

var LooseParser = _dereq_("./state").LooseParser;

var isDummy = _dereq_("./parseutil").isDummy;

var tt = _dereq_("..").tokTypes;

var lp = LooseParser.prototype;

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
  if (this.tok.type === tt.comma) {
    var node = this.startNodeAt(start);
    node.expressions = [expr];
    while (this.eat(tt.comma)) node.expressions.push(this.parseMaybeAssign(noIn));
    return this.finishNode(node, "SequenceExpression");
  }
  return expr;
};

lp.parseParenExpression = function () {
  this.pushCx();
  this.expect(tt.parenL);
  var val = this.parseExpression();
  this.popCx();
  this.expect(tt.parenR);
  return val;
};

lp.parseMaybeAssign = function (noIn) {
  var start = this.storeCurrentPos();
  var left = this.parseMaybeConditional(noIn);
  if (this.tok.type.isAssign) {
    var node = this.startNodeAt(start);
    node.operator = this.tok.value;
    node.left = this.tok.type === tt.eq ? this.toAssignable(left) : this.checkLVal(left);
    this.next();
    node.right = this.parseMaybeAssign(noIn);
    return this.finishNode(node, "AssignmentExpression");
  }
  return left;
};

lp.parseMaybeConditional = function (noIn) {
  var start = this.storeCurrentPos();
  var expr = this.parseExprOps(noIn);
  if (this.eat(tt.question)) {
    var node = this.startNodeAt(start);
    node.test = expr;
    node.consequent = this.parseMaybeAssign();
    node.alternate = this.expect(tt.colon) ? this.parseMaybeAssign(noIn) : this.dummyIdent();
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
  if (prec != null && (!noIn || this.tok.type !== tt._in)) {
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
        update = this.tok.type === tt.incDec;
    node.operator = this.tok.value;
    node.prefix = true;
    this.next();
    node.argument = this.parseMaybeUnary(noIn);
    if (update) node.argument = this.checkLVal(node.argument);
    return this.finishNode(node, update ? "UpdateExpression" : "UnaryExpression");
  } else if (this.tok.type === tt.ellipsis) {
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
      if (this.tok.type == tt.dot && this.curIndent == startIndent) --startIndent;else return base;
    }

    if (this.eat(tt.dot)) {
      var node = this.startNodeAt(start);
      node.object = base;
      if (this.curLineStart != line && this.curIndent <= startIndent && this.tokenStartsLine()) node.property = this.dummyIdent();else node.property = this.parsePropertyAccessor() || this.dummyIdent();
      node.computed = false;
      base = this.finishNode(node, "MemberExpression");
    } else if (this.tok.type == tt.bracketL) {
      this.pushCx();
      this.next();
      var node = this.startNodeAt(start);
      node.object = base;
      node.property = this.parseExpression();
      node.computed = true;
      this.popCx();
      this.expect(tt.bracketR);
      base = this.finishNode(node, "MemberExpression");
    } else if (!noCalls && this.tok.type == tt.parenL) {
      var node = this.startNodeAt(start);
      node.callee = base;
      node.arguments = this.parseExprList(tt.parenR);
      base = this.finishNode(node, "CallExpression");
    } else if (this.tok.type == tt.backQuote) {
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
    case tt._this:
    case tt._super:
      var type = this.tok.type === tt._this ? "ThisExpression" : "Super";
      node = this.startNode();
      this.next();
      return this.finishNode(node, type);

    case tt.name:
      var start = this.storeCurrentPos();
      var id = this.parseIdent();
      return this.eat(tt.arrow) ? this.parseArrowExpression(this.startNodeAt(start), [id]) : id;

    case tt.regexp:
      node = this.startNode();
      var val = this.tok.value;
      node.regex = { pattern: val.pattern, flags: val.flags };
      node.value = val.value;
      node.raw = this.input.slice(this.tok.start, this.tok.end);
      this.next();
      return this.finishNode(node, "Literal");

    case tt.num:case tt.string:
      node = this.startNode();
      node.value = this.tok.value;
      node.raw = this.input.slice(this.tok.start, this.tok.end);
      this.next();
      return this.finishNode(node, "Literal");

    case tt._null:case tt._true:case tt._false:
      node = this.startNode();
      node.value = this.tok.type === tt._null ? null : this.tok.type === tt._true;
      node.raw = this.tok.type.keyword;
      this.next();
      return this.finishNode(node, "Literal");

    case tt.parenL:
      var parenStart = this.storeCurrentPos();
      this.next();
      var inner = this.parseExpression();
      this.expect(tt.parenR);
      if (this.eat(tt.arrow)) {
        return this.parseArrowExpression(this.startNodeAt(parenStart), inner.expressions || (isDummy(inner) ? [] : [inner]));
      }
      if (this.options.preserveParens) {
        var par = this.startNodeAt(parenStart);
        par.expression = inner;
        inner = this.finishNode(par, "ParenthesizedExpression");
      }
      return inner;

    case tt.bracketL:
      node = this.startNode();
      node.elements = this.parseExprList(tt.bracketR, true);
      return this.finishNode(node, "ArrayExpression");

    case tt.braceL:
      return this.parseObj();

    case tt._class:
      return this.parseClass();

    case tt._function:
      node = this.startNode();
      this.next();
      return this.parseFunction(node, false);

    case tt._new:
      return this.parseNew();

    case tt._yield:
      node = this.startNode();
      this.next();
      if (this.semicolon() || this.canInsertSemicolon() || this.tok.type != tt.star && !this.tok.type.startsExpr) {
        node.delegate = false;
        node.argument = null;
      } else {
        node.delegate = this.eat(tt.star);
        node.argument = this.parseMaybeAssign();
      }
      return this.finishNode(node, "YieldExpression");

    case tt.backQuote:
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
  if (this.options.ecmaVersion >= 6 && this.eat(tt.dot)) {
    node.meta = meta;
    node.property = this.parseIdent(true);
    return this.finishNode(node, "MetaProperty");
  }
  var start = this.storeCurrentPos();
  node.callee = this.parseSubscripts(this.parseExprAtom(), start, true, startIndent, line);
  if (this.tok.type == tt.parenL) {
    node.arguments = this.parseExprList(tt.parenR);
  } else {
    node.arguments = [];
  }
  return this.finishNode(node, "NewExpression");
};

lp.parseTemplateElement = function () {
  var elem = this.startNode();
  elem.value = {
    raw: this.input.slice(this.tok.start, this.tok.end),
    cooked: this.tok.value
  };
  this.next();
  elem.tail = this.tok.type === tt.backQuote;
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
    if (this.expect(tt.braceR)) {
      curElt = this.parseTemplateElement();
    } else {
      curElt = this.startNode();
      curElt.value = { cooked: "", raw: "" };
      curElt.tail = true;
    }
    node.quasis.push(curElt);
  }
  this.expect(tt.backQuote);
  return this.finishNode(node, "TemplateLiteral");
};

lp.parseObj = function () {
  var node = this.startNode();
  node.properties = [];
  this.pushCx();
  var indent = this.curIndent + 1,
      line = this.curLineStart;
  this.eat(tt.braceL);
  if (this.curIndent + 1 < indent) {
    indent = this.curIndent;line = this.curLineStart;
  }
  while (!this.closes(tt.braceR, indent, line)) {
    var prop = this.startNode(),
        isGenerator = undefined,
        start = undefined;
    if (this.options.ecmaVersion >= 6) {
      start = this.storeCurrentPos();
      prop.method = false;
      prop.shorthand = false;
      isGenerator = this.eat(tt.star);
    }
    this.parsePropertyName(prop);
    if (isDummy(prop.key)) {
      if (isDummy(this.parseMaybeAssign())) this.next();this.eat(tt.comma);continue;
    }
    if (this.eat(tt.colon)) {
      prop.kind = "init";
      prop.value = this.parseMaybeAssign();
    } else if (this.options.ecmaVersion >= 6 && (this.tok.type === tt.parenL || this.tok.type === tt.braceL)) {
      prop.kind = "init";
      prop.method = true;
      prop.value = this.parseMethod(isGenerator);
    } else if (this.options.ecmaVersion >= 5 && prop.key.type === "Identifier" && !prop.computed && (prop.key.name === "get" || prop.key.name === "set") && (this.tok.type != tt.comma && this.tok.type != tt.braceR)) {
      prop.kind = prop.key.name;
      this.parsePropertyName(prop);
      prop.value = this.parseMethod(false);
    } else {
      prop.kind = "init";
      if (this.options.ecmaVersion >= 6) {
        if (this.eat(tt.eq)) {
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
    this.eat(tt.comma);
  }
  this.popCx();
  if (!this.eat(tt.braceR)) {
    // If there is no closing brace, make the node span to the start
    // of the next token (this is useful for Tern)
    this.last.end = this.tok.start;
    if (this.options.locations) this.last.loc.end = this.tok.loc.start;
  }
  return this.finishNode(node, "ObjectExpression");
};

lp.parsePropertyName = function (prop) {
  if (this.options.ecmaVersion >= 6) {
    if (this.eat(tt.bracketL)) {
      prop.computed = true;
      prop.key = this.parseExpression();
      this.expect(tt.bracketR);
      return;
    } else {
      prop.computed = false;
    }
  }
  var key = this.tok.type === tt.num || this.tok.type === tt.string ? this.parseExprAtom() : this.parseIdent();
  prop.key = key || this.dummyIdent();
};

lp.parsePropertyAccessor = function () {
  if (this.tok.type === tt.name || this.tok.type.keyword) return this.parseIdent();
};

lp.parseIdent = function () {
  var name = this.tok.type === tt.name ? this.tok.value : this.tok.type.keyword;
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
  params = this.parseExprList(tt.parenR);
  return this.toAssignableList(params, true);
};

lp.parseMethod = function (isGenerator) {
  var node = this.startNode();
  this.initFunction(node);
  node.params = this.parseFunctionParams();
  node.generator = isGenerator || false;
  node.expression = this.options.ecmaVersion >= 6 && this.tok.type !== tt.braceL;
  node.body = node.expression ? this.parseMaybeAssign() : this.parseBlock();
  return this.finishNode(node, "FunctionExpression");
};

lp.parseArrowExpression = function (node, params) {
  this.initFunction(node);
  node.params = this.toAssignableList(params, true);
  node.expression = this.tok.type !== tt.braceL;
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
    if (this.eat(tt.comma)) {
      elts.push(allowEmpty ? null : this.dummyIdent());
      continue;
    }
    var elt = this.parseMaybeAssign();
    if (isDummy(elt)) {
      if (this.closes(close, indent, line)) break;
      this.next();
    } else {
      elts.push(elt);
    }
    this.eat(tt.comma);
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

},{"..":3,"./parseutil":5,"./state":6}],5:[function(_dereq_,module,exports){
"use strict";

exports.isDummy = isDummy;
exports.__esModule = true;

var LooseParser = _dereq_("./state").LooseParser;

var _ = _dereq_("..");

var Node = _.Node;
var SourceLocation = _.SourceLocation;
var lineBreak = _.lineBreak;
var isNewLine = _.isNewLine;
var tt = _.tokTypes;

var lp = LooseParser.prototype;

lp.startNode = function () {
  var node = new Node();
  node.start = this.tok.start;
  if (this.options.locations) node.loc = new SourceLocation(this.toks, this.tok.loc.start);
  if (this.options.directSourceFile) node.sourceFile = this.options.directSourceFile;
  if (this.options.ranges) node.range = [this.tok.start, 0];
  return node;
};

lp.storeCurrentPos = function () {
  return this.options.locations ? [this.tok.start, this.tok.loc.start] : this.tok.start;
};

lp.startNodeAt = function (pos) {
  var node = new Node();
  if (this.options.locations) {
    node.start = pos[0];
    node.loc = new SourceLocation(this.toks, pos[1]);
    pos = pos[0];
  } else {
    node.start = pos;
  }
  if (this.options.directSourceFile) node.sourceFile = this.options.directSourceFile;
  if (this.options.ranges) node.range = [pos, 0];
  return node;
};

lp.finishNode = function (node, type) {
  node.type = type;
  node.end = this.last.end;
  if (this.options.locations) node.loc.end = this.last.loc.end;
  if (this.options.ranges) node.range[1] = this.last.end;
  return node;
};

lp.dummyIdent = function () {
  var dummy = this.startNode();
  dummy.name = "✖";
  return this.finishNode(dummy, "Identifier");
};

function isDummy(node) {
  return node.name == "✖";
}

lp.eat = function (type) {
  if (this.tok.type === type) {
    this.next();
    return true;
  } else {
    return false;
  }
};

lp.isContextual = function (name) {
  return this.tok.type === tt.name && this.tok.value === name;
};

lp.eatContextual = function (name) {
  return this.tok.value === name && this.eat(tt.name);
};

lp.canInsertSemicolon = function () {
  return this.tok.type === tt.eof || this.tok.type === tt.braceR || lineBreak.test(this.input.slice(this.last.end, this.tok.start));
};

lp.semicolon = function () {
  return this.eat(tt.semi);
};

lp.expect = function (type) {
  if (this.eat(type)) return true;
  for (var i = 1; i <= 2; i++) {
    if (this.lookAhead(i).type == type) {
      for (var j = 0; j < i; j++) {
        this.next();
      }return true;
    }
  }
};

lp.pushCx = function () {
  this.context.push(this.curIndent);
};
lp.popCx = function () {
  this.curIndent = this.context.pop();
};

lp.lineEnd = function (pos) {
  while (pos < this.input.length && !isNewLine(this.input.charCodeAt(pos))) ++pos;
  return pos;
};

lp.indentationAfter = function (pos) {
  for (var count = 0;; ++pos) {
    var ch = this.input.charCodeAt(pos);
    if (ch === 32) ++count;else if (ch === 9) count += this.options.tabSize;else return count;
  }
};

lp.closes = function (closeTok, indent, line, blockHeuristic) {
  if (this.tok.type === closeTok || this.tok.type === tt.eof) return true;
  return line != this.curLineStart && this.curIndent < indent && this.tokenStartsLine() && (!blockHeuristic || this.nextLineStart >= this.input.length || this.indentationAfter(this.nextLineStart) < indent);
};

lp.tokenStartsLine = function () {
  for (var p = this.tok.start - 1; p >= this.curLineStart; --p) {
    var ch = this.input.charCodeAt(p);
    if (ch !== 9 && ch !== 32) return false;
  }
  return true;
};

},{"..":3,"./state":6}],6:[function(_dereq_,module,exports){
"use strict";

exports.LooseParser = LooseParser;
exports.__esModule = true;

var _ = _dereq_("..");

var tokenizer = _.tokenizer;
var SourceLocation = _.SourceLocation;
var tt = _.tokTypes;

function LooseParser(input, options) {
  this.toks = tokenizer(input, options);
  this.options = this.toks.options;
  this.input = this.toks.input;
  this.tok = this.last = { type: tt.eof, start: 0, end: 0 };
  if (this.options.locations) {
    var here = this.toks.curPosition();
    this.tok.loc = new SourceLocation(this.toks, here, here);
  }
  this.ahead = []; // Tokens ahead
  this.context = []; // Indentation contexted
  this.curIndent = 0;
  this.curLineStart = 0;
  this.nextLineStart = this.lineEnd(this.curLineStart) + 1;
}

},{"..":3}],7:[function(_dereq_,module,exports){
"use strict";

var LooseParser = _dereq_("./state").LooseParser;

var isDummy = _dereq_("./parseutil").isDummy;

var _ = _dereq_("..");

var getLineInfo = _.getLineInfo;
var tt = _.tokTypes;

var lp = LooseParser.prototype;

lp.parseTopLevel = function () {
  var node = this.startNodeAt(this.options.locations ? [0, getLineInfo(this.input, 0)] : 0);
  node.body = [];
  while (this.tok.type !== tt.eof) node.body.push(this.parseStatement());
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
    case tt._break:case tt._continue:
      this.next();
      var isBreak = starttype === tt._break;
      if (this.semicolon() || this.canInsertSemicolon()) {
        node.label = null;
      } else {
        node.label = this.tok.type === tt.name ? this.parseIdent() : null;
        this.semicolon();
      }
      return this.finishNode(node, isBreak ? "BreakStatement" : "ContinueStatement");

    case tt._debugger:
      this.next();
      this.semicolon();
      return this.finishNode(node, "DebuggerStatement");

    case tt._do:
      this.next();
      node.body = this.parseStatement();
      node.test = this.eat(tt._while) ? this.parseParenExpression() : this.dummyIdent();
      this.semicolon();
      return this.finishNode(node, "DoWhileStatement");

    case tt._for:
      this.next();
      this.pushCx();
      this.expect(tt.parenL);
      if (this.tok.type === tt.semi) return this.parseFor(node, null);
      if (this.tok.type === tt._var || this.tok.type === tt._let || this.tok.type === tt._const) {
        var _init = this.parseVar(true);
        if (_init.declarations.length === 1 && (this.tok.type === tt._in || this.isContextual("of"))) {
          return this.parseForIn(node, _init);
        }
        return this.parseFor(node, _init);
      }
      var init = this.parseExpression(true);
      if (this.tok.type === tt._in || this.isContextual("of")) return this.parseForIn(node, this.toAssignable(init));
      return this.parseFor(node, init);

    case tt._function:
      this.next();
      return this.parseFunction(node, true);

    case tt._if:
      this.next();
      node.test = this.parseParenExpression();
      node.consequent = this.parseStatement();
      node.alternate = this.eat(tt._else) ? this.parseStatement() : null;
      return this.finishNode(node, "IfStatement");

    case tt._return:
      this.next();
      if (this.eat(tt.semi) || this.canInsertSemicolon()) node.argument = null;else {
        node.argument = this.parseExpression();this.semicolon();
      }
      return this.finishNode(node, "ReturnStatement");

    case tt._switch:
      var blockIndent = this.curIndent,
          line = this.curLineStart;
      this.next();
      node.discriminant = this.parseParenExpression();
      node.cases = [];
      this.pushCx();
      this.expect(tt.braceL);

      var cur = undefined;
      while (!this.closes(tt.braceR, blockIndent, line, true)) {
        if (this.tok.type === tt._case || this.tok.type === tt._default) {
          var isCase = this.tok.type === tt._case;
          if (cur) this.finishNode(cur, "SwitchCase");
          node.cases.push(cur = this.startNode());
          cur.consequent = [];
          this.next();
          if (isCase) cur.test = this.parseExpression();else cur.test = null;
          this.expect(tt.colon);
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
      this.eat(tt.braceR);
      return this.finishNode(node, "SwitchStatement");

    case tt._throw:
      this.next();
      node.argument = this.parseExpression();
      this.semicolon();
      return this.finishNode(node, "ThrowStatement");

    case tt._try:
      this.next();
      node.block = this.parseBlock();
      node.handler = null;
      if (this.tok.type === tt._catch) {
        var clause = this.startNode();
        this.next();
        this.expect(tt.parenL);
        clause.param = this.toAssignable(this.parseExprAtom(), true);
        this.expect(tt.parenR);
        clause.guard = null;
        clause.body = this.parseBlock();
        node.handler = this.finishNode(clause, "CatchClause");
      }
      node.finalizer = this.eat(tt._finally) ? this.parseBlock() : null;
      if (!node.handler && !node.finalizer) return node.block;
      return this.finishNode(node, "TryStatement");

    case tt._var:
    case tt._let:
    case tt._const:
      return this.parseVar();

    case tt._while:
      this.next();
      node.test = this.parseParenExpression();
      node.body = this.parseStatement();
      return this.finishNode(node, "WhileStatement");

    case tt._with:
      this.next();
      node.object = this.parseParenExpression();
      node.body = this.parseStatement();
      return this.finishNode(node, "WithStatement");

    case tt.braceL:
      return this.parseBlock();

    case tt.semi:
      this.next();
      return this.finishNode(node, "EmptyStatement");

    case tt._class:
      return this.parseClass(true);

    case tt._import:
      return this.parseImport();

    case tt._export:
      return this.parseExport();

    default:
      var expr = this.parseExpression();
      if (isDummy(expr)) {
        this.next();
        if (this.tok.type === tt.eof) return this.finishNode(node, "EmptyStatement");
        return this.parseStatement();
      } else if (starttype === tt.name && expr.type === "Identifier" && this.eat(tt.colon)) {
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
  this.expect(tt.braceL);
  var blockIndent = this.curIndent,
      line = this.curLineStart;
  node.body = [];
  while (!this.closes(tt.braceR, blockIndent, line, true)) node.body.push(this.parseStatement());
  this.popCx();
  this.eat(tt.braceR);
  return this.finishNode(node, "BlockStatement");
};

lp.parseFor = function (node, init) {
  node.init = init;
  node.test = node.update = null;
  if (this.eat(tt.semi) && this.tok.type !== tt.semi) node.test = this.parseExpression();
  if (this.eat(tt.semi) && this.tok.type !== tt.parenR) node.update = this.parseExpression();
  this.popCx();
  this.expect(tt.parenR);
  node.body = this.parseStatement();
  return this.finishNode(node, "ForStatement");
};

lp.parseForIn = function (node, init) {
  var type = this.tok.type === tt._in ? "ForInStatement" : "ForOfStatement";
  this.next();
  node.left = init;
  node.right = this.parseExpression();
  this.popCx();
  this.expect(tt.parenR);
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
    decl.init = this.eat(tt.eq) ? this.parseMaybeAssign(noIn) : null;
    node.declarations.push(this.finishNode(decl, "VariableDeclarator"));
  } while (this.eat(tt.comma));
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
  if (this.tok.type === tt.name) node.id = this.parseIdent();else if (isStatement) node.id = this.dummyIdent();else node.id = null;
  node.superClass = this.eat(tt._extends) ? this.parseExpression() : null;
  node.body = this.startNode();
  node.body.body = [];
  this.pushCx();
  var indent = this.curIndent + 1,
      line = this.curLineStart;
  this.eat(tt.braceL);
  if (this.curIndent + 1 < indent) {
    indent = this.curIndent;line = this.curLineStart;
  }
  while (!this.closes(tt.braceR, indent, line)) {
    if (this.semicolon()) continue;
    var method = this.startNode(),
        isGenerator = undefined;
    if (this.options.ecmaVersion >= 6) {
      method["static"] = false;
      isGenerator = this.eat(tt.star);
    }
    this.parsePropertyName(method);
    if (isDummy(method.key)) {
      if (isDummy(this.parseMaybeAssign())) this.next();this.eat(tt.comma);continue;
    }
    if (method.key.type === "Identifier" && !method.computed && method.key.name === "static" && (this.tok.type != tt.parenL && this.tok.type != tt.braceL)) {
      method["static"] = true;
      isGenerator = this.eat(tt.star);
      this.parsePropertyName(method);
    } else {
      method["static"] = false;
    }
    if (this.options.ecmaVersion >= 5 && method.key.type === "Identifier" && !method.computed && (method.key.name === "get" || method.key.name === "set") && this.tok.type !== tt.parenL && this.tok.type !== tt.braceL) {
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
  if (!this.eat(tt.braceR)) {
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
    node.generator = this.eat(tt.star);
  }
  if (this.tok.type === tt.name) node.id = this.parseIdent();else if (isStatement) node.id = this.dummyIdent();
  node.params = this.parseFunctionParams();
  node.body = this.parseBlock();
  return this.finishNode(node, isStatement ? "FunctionDeclaration" : "FunctionExpression");
};

lp.parseExport = function () {
  var node = this.startNode();
  this.next();
  if (this.eat(tt.star)) {
    node.source = this.eatContextual("from") ? this.parseExprAtom() : null;
    return this.finishNode(node, "ExportAllDeclaration");
  }
  if (this.eat(tt._default)) {
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
  if (this.tok.type === tt.string) {
    node.specifiers = [];
    node.source = this.parseExprAtom();
    node.kind = "";
  } else {
    var elt = undefined;
    if (this.tok.type === tt.name && this.tok.value !== "from") {
      elt = this.startNode();
      elt.local = this.parseIdent();
      this.finishNode(elt, "ImportDefaultSpecifier");
      this.eat(tt.comma);
    }
    node.specifiers = this.parseImportSpecifierList();
    node.source = this.eatContextual("from") ? this.parseExprAtom() : null;
    if (elt) node.specifiers.unshift(elt);
  }
  this.semicolon();
  return this.finishNode(node, "ImportDeclaration");
};

lp.parseImportSpecifierList = function () {
  var elts = [];
  if (this.tok.type === tt.star) {
    var elt = this.startNode();
    this.next();
    if (this.eatContextual("as")) elt.local = this.parseIdent();
    elts.push(this.finishNode(elt, "ImportNamespaceSpecifier"));
  } else {
    var indent = this.curIndent,
        line = this.curLineStart,
        continuedLine = this.nextLineStart;
    this.pushCx();
    this.eat(tt.braceL);
    if (this.curLineStart > continuedLine) continuedLine = this.curLineStart;
    while (!this.closes(tt.braceR, indent + (this.curLineStart <= continuedLine ? 1 : 0), line)) {
      var elt = this.startNode();
      if (this.eat(tt.star)) {
        if (this.eatContextual("as")) elt.local = this.parseIdent();
        this.finishNode(elt, "ImportNamespaceSpecifier");
      } else {
        if (this.isContextual("from")) break;
        elt.imported = this.parseIdent();
        elt.local = this.eatContextual("as") ? this.parseIdent() : elt.imported;
        this.finishNode(elt, "ImportSpecifier");
      }
      elts.push(elt);
      this.eat(tt.comma);
    }
    this.eat(tt.braceR);
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
  this.eat(tt.braceL);
  if (this.curLineStart > continuedLine) continuedLine = this.curLineStart;
  while (!this.closes(tt.braceR, indent + (this.curLineStart <= continuedLine ? 1 : 0), line)) {
    if (this.isContextual("from")) break;
    var elt = this.startNode();
    elt.local = this.parseIdent();
    elt.exported = this.eatContextual("as") ? this.parseIdent() : elt.local;
    this.finishNode(elt, "ExportSpecifier");
    elts.push(elt);
    this.eat(tt.comma);
  }
  this.eat(tt.braceR);
  this.popCx();
  return elts;
};

},{"..":3,"./parseutil":5,"./state":6}],8:[function(_dereq_,module,exports){
"use strict";

var _ = _dereq_("..");

var tt = _.tokTypes;
var Token = _.Token;
var isNewLine = _.isNewLine;
var SourceLocation = _.SourceLocation;
var getLineInfo = _.getLineInfo;
var lineBreakG = _.lineBreakG;

var LooseParser = _dereq_("./state").LooseParser;

var lp = LooseParser.prototype;

function isSpace(ch) {
  return ch < 14 && ch > 8 || ch === 32 || ch === 160 || isNewLine(ch);
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
      if (this.toks.type === tt.dot && this.input.substr(this.toks.end, 1) === "." && this.options.ecmaVersion >= 6) {
        this.toks.end++;
        this.toks.type = tt.ellipsis;
      }
      return new Token(this.toks);
    } catch (e) {
      if (!(e instanceof SyntaxError)) throw e;

      // Try to skip some text, based on the error message, and then continue
      var msg = e.message,
          pos = e.raisedAt,
          replace = true;
      if (/unterminated/i.test(msg)) {
        pos = this.lineEnd(e.pos + 1);
        if (/string/.test(msg)) {
          replace = { start: e.pos, end: pos, type: tt.string, value: this.input.slice(e.pos + 1, pos) };
        } else if (/regular expr/i.test(msg)) {
          var re = this.input.slice(e.pos, pos);
          try {
            re = new RegExp(re);
          } catch (e) {}
          replace = { start: e.pos, end: pos, type: tt.regexp, value: re };
        } else if (/template/.test(msg)) {
          replace = { start: e.pos, end: pos,
            type: tt.template,
            value: this.input.slice(e.pos, pos) };
        } else {
          replace = false;
        }
      } else if (/invalid (unicode|regexp|number)|expecting unicode|octal literal|is reserved|directly after number|expected number in radix/i.test(msg)) {
        while (pos < this.input.length && !isSpace(this.input.charCodeAt(pos))) ++pos;
      } else if (/character escape|expected hexadecimal/i.test(msg)) {
        while (pos < this.input.length) {
          var ch = this.input.charCodeAt(pos++);
          if (ch === 34 || ch === 39 || isNewLine(ch)) break;
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
      if (replace === true) replace = { start: pos, end: pos, type: tt.name, value: "✖" };
      if (replace) {
        if (this.options.locations) replace.loc = new SourceLocation(this.toks, getLineInfo(this.input, replace.start), getLineInfo(this.input, replace.end));
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
    this.toks.lineStart = lineBreakG.lastIndex = 0;
    var match = undefined;
    while ((match = lineBreakG.exec(this.input)) && match.index < pos) {
      ++this.toks.curLine;
      this.toks.lineStart = match.index + match[0].length;
    }
  }
};

lp.lookAhead = function (n) {
  while (n > this.ahead.length) this.ahead.push(this.readToken());
  return this.ahead[n - 1];
};

},{"..":3,"./state":6}]},{},[1])(1)
});
}).call(this,typeof global !== "undefined" ? global : typeof self !== "undefined" ? self : typeof window !== "undefined" ? window : {})

},{}],14:[function(require,module,exports){
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

},{}],15:[function(require,module,exports){
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

},{}],16:[function(require,module,exports){
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

},{}],17:[function(require,module,exports){
module.exports = function isBuffer(arg) {
  return arg && typeof arg === 'object'
    && typeof arg.copy === 'function'
    && typeof arg.fill === 'function'
    && typeof arg.readUInt8 === 'function';
}
},{}],18:[function(require,module,exports){
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

},{"./support/isBuffer":17,"_process":16,"inherits":15}]},{},[7])(7)
});
//# sourceMappingURL=data:application/json;charset:utf-8;base64,eyJ2ZXJzaW9uIjozLCJzb3VyY2VzIjpbIm5vZGVfbW9kdWxlcy9icm93c2VyaWZ5L25vZGVfbW9kdWxlcy9icm93c2VyLXBhY2svX3ByZWx1ZGUuanMiLCIvaG9tZS9zd2tpbS9XZWJzdG9ybVByb2plY3RzL3lhdGVybi9saWIvYXV4LmpzIiwiL2hvbWUvc3draW0vV2Vic3Rvcm1Qcm9qZWN0cy95YXRlcm4vbGliL2NvbnN0cmFpbnQvY0dlbi5qcyIsIi9ob21lL3N3a2ltL1dlYnN0b3JtUHJvamVjdHMveWF0ZXJuL2xpYi9jb25zdHJhaW50L2NvbnN0cmFpbnRzLmpzIiwiL2hvbWUvc3draW0vV2Vic3Rvcm1Qcm9qZWN0cy95YXRlcm4vbGliL2RvbWFpbnMvY29udGV4dC5qcyIsIi9ob21lL3N3a2ltL1dlYnN0b3JtUHJvamVjdHMveWF0ZXJuL2xpYi9kb21haW5zL3N0YXR1cy5qcyIsIi9ob21lL3N3a2ltL1dlYnN0b3JtUHJvamVjdHMveWF0ZXJuL2xpYi9kb21haW5zL3R5cGVzLmpzIiwiL2hvbWUvc3draW0vV2Vic3Rvcm1Qcm9qZWN0cy95YXRlcm4vbGliL2luZmVyLmpzIiwiL2hvbWUvc3draW0vV2Vic3Rvcm1Qcm9qZWN0cy95YXRlcm4vbGliL3JldE9jY3VyLmpzIiwiL2hvbWUvc3draW0vV2Vic3Rvcm1Qcm9qZWN0cy95YXRlcm4vbGliL3V0aWwvbXlXYWxrZXIuanMiLCIvaG9tZS9zd2tpbS9XZWJzdG9ybVByb2plY3RzL3lhdGVybi9saWIvdmFyQmxvY2suanMiLCIvaG9tZS9zd2tpbS9XZWJzdG9ybVByb2plY3RzL3lhdGVybi9saWIvdmFycmVmcy5qcyIsIm5vZGVfbW9kdWxlcy9hY29ybi9kaXN0L2Fjb3JuLmpzIiwibm9kZV9tb2R1bGVzL2Fjb3JuL2Rpc3QvYWNvcm5fbG9vc2UuanMiLCJub2RlX21vZHVsZXMvYWNvcm4vZGlzdC93YWxrLmpzIiwibm9kZV9tb2R1bGVzL2Jyb3dzZXJpZnkvbm9kZV9tb2R1bGVzL2luaGVyaXRzL2luaGVyaXRzX2Jyb3dzZXIuanMiLCJub2RlX21vZHVsZXMvYnJvd3NlcmlmeS9ub2RlX21vZHVsZXMvcHJvY2Vzcy9icm93c2VyLmpzIiwibm9kZV9tb2R1bGVzL2Jyb3dzZXJpZnkvbm9kZV9tb2R1bGVzL3V0aWwvc3VwcG9ydC9pc0J1ZmZlckJyb3dzZXIuanMiLCJub2RlX21vZHVsZXMvYnJvd3NlcmlmeS9ub2RlX21vZHVsZXMvdXRpbC91dGlsLmpzIl0sIm5hbWVzIjpbXSwibWFwcGluZ3MiOiJBQUFBOzs7QUNBQSxJQUFJLElBQUksR0FBRyxPQUFPLENBQUMsTUFBTSxDQUFDLENBQUM7O0FBRTNCLFNBQVMsV0FBVyxDQUFDLEdBQUcsRUFBRSxRQUFRLEVBQUU7QUFDaEMsUUFBSSxRQUFRLEdBQUcsRUFBRSxDQUFDOztBQUVsQixRQUFJLEdBQUcsR0FBRyxRQUFRLEtBQUssU0FBUyxHQUFHLENBQUMsR0FBRyxRQUFRLENBQUM7O0FBRWhELGFBQVMsUUFBUSxDQUFDLElBQUksRUFBRTtBQUNwQixZQUFJLENBQUMsUUFBUSxDQUFDLEdBQUcsR0FBRyxDQUFDO0FBQ3JCLGdCQUFRLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQyxDQUFDO0FBQ3BCLFdBQUcsRUFBRSxDQUFDO0tBQ1Q7OztBQUdELGFBQVMsaUJBQWlCLENBQUMsSUFBSSxFQUFFO0FBQzdCLFlBQUksSUFBSSxJQUFJLElBQUksQ0FBQyxjQUFjLENBQUMsTUFBTSxDQUFDLEVBQUU7QUFDckMsb0JBQVEsQ0FBQyxJQUFJLENBQUMsQ0FBQztTQUNsQjtBQUNELFlBQUksSUFBSSxJQUFJLE9BQU8sSUFBSSxLQUFLLFFBQVEsRUFBRTtBQUNsQyxpQkFBSyxJQUFJLENBQUMsSUFBSSxJQUFJLEVBQUU7QUFDaEIsaUNBQWlCLENBQUMsSUFBSSxDQUFDLENBQUMsQ0FBQyxDQUFDLENBQUM7YUFDOUI7U0FDSjtLQUNKOztBQUVELHFCQUFpQixDQUFDLEdBQUcsQ0FBQyxDQUFDOztBQUV2QixXQUFPLFFBQVEsQ0FBQztDQUNuQjs7QUFFRCxTQUFTLFlBQVksQ0FBQyxHQUFHLEVBQUU7QUFDdkIs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QUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7Ozs7O0FDNzZIQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTs7Ozs7QUN0eENBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTs7OztBQ3JWQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7O0FDdkJBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBOztBQzFGQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7OztBQ0xBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0EiLCJmaWxlIjoiZ2VuZXJhdGVkLmpzIiwic291cmNlUm9vdCI6IiIsInNvdXJjZXNDb250ZW50IjpbIihmdW5jdGlvbiBlKHQsbixyKXtmdW5jdGlvbiBzKG8sdSl7aWYoIW5bb10pe2lmKCF0W29dKXt2YXIgYT10eXBlb2YgcmVxdWlyZT09XCJmdW5jdGlvblwiJiZyZXF1aXJlO2lmKCF1JiZhKXJldHVybiBhKG8sITApO2lmKGkpcmV0dXJuIGkobywhMCk7dmFyIGY9bmV3IEVycm9yKFwiQ2Fubm90IGZpbmQgbW9kdWxlICdcIitvK1wiJ1wiKTt0aHJvdyBmLmNvZGU9XCJNT0RVTEVfTk9UX0ZPVU5EXCIsZn12YXIgbD1uW29dPXtleHBvcnRzOnt9fTt0W29dWzBdLmNhbGwobC5leHBvcnRzLGZ1bmN0aW9uKGUpe3ZhciBuPXRbb11bMV1bZV07cmV0dXJuIHMobj9uOmUpfSxsLGwuZXhwb3J0cyxlLHQsbixyKX1yZXR1cm4gbltvXS5leHBvcnRzfXZhciBpPXR5cGVvZiByZXF1aXJlPT1cImZ1bmN0aW9uXCImJnJlcXVpcmU7Zm9yKHZhciBvPTA7bzxyLmxlbmd0aDtvKyspcyhyW29dKTtyZXR1cm4gc30pIiwidmFyIHV0aWwgPSByZXF1aXJlKCd1dGlsJyk7XG5cbmZ1bmN0aW9uIGdldE5vZGVMaXN0KGFzdCwgc3RhcnROdW0pIHtcbiAgICB2YXIgbm9kZUxpc3QgPSBbXTtcblxuICAgIHZhciBudW0gPSBzdGFydE51bSA9PT0gdW5kZWZpbmVkID8gMCA6IHN0YXJ0TnVtO1xuXG4gICAgZnVuY3Rpb24gYXNzaWduSWQobm9kZSkge1xuICAgICAgICBub2RlWydAbGFiZWwnXSA9IG51bTtcbiAgICAgICAgbm9kZUxpc3QucHVzaChub2RlKTtcbiAgICAgICAgbnVtKys7XG4gICAgfVxuXG4gICAgLy8gTGFiZWwgZXZlcnkgQVNUIG5vZGUgd2l0aCBwcm9wZXJ0eSAndHlwZSdcbiAgICBmdW5jdGlvbiBsYWJlbE5vZGVXaXRoVHlwZShub2RlKSB7XG4gICAgICAgIGlmIChub2RlICYmIG5vZGUuaGFzT3duUHJvcGVydHkoJ3R5cGUnKSkge1xuICAgICAgICAgICAgYXNzaWduSWQobm9kZSk7XG4gICAgICAgIH1cbiAgICAgICAgaWYgKG5vZGUgJiYgdHlwZW9mIG5vZGUgPT09ICdvYmplY3QnKSB7XG4gICAgICAgICAgICBmb3IgKHZhciBwIGluIG5vZGUpIHtcbiAgICAgICAgICAgICAgICBsYWJlbE5vZGVXaXRoVHlwZShub2RlW3BdKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgfVxuICAgIH1cblxuICAgIGxhYmVsTm9kZVdpdGhUeXBlKGFzdCk7XG5cbiAgICByZXR1cm4gbm9kZUxpc3Q7XG59XG5cbmZ1bmN0aW9uIHNob3dVbmZvbGRlZChvYmopIHtcbiAgICBjb25zb2xlLmxvZyh1dGlsLmluc3BlY3Qob2JqLCB7ZGVwdGg6IG51bGx9KSk7XG59XG5cbmV4cG9ydHMuZ2V0Tm9kZUxpc3QgPSBnZXROb2RlTGlzdDtcbmV4cG9ydHMuc2hvd1VuZm9sZGVkID0gc2hvd1VuZm9sZGVkO1xuIiwiJ3VzZSBzdHJpY3QnO1xuXG5jb25zdCB0eXBlcyA9IHJlcXVpcmUoJy4uL2RvbWFpbnMvdHlwZXMnKTtcbmNvbnN0IHdhbGsgPSByZXF1aXJlKCdhY29ybi9kaXN0L3dhbGsnKTtcbmNvbnN0IHN0YXR1cyA9IHJlcXVpcmUoJy4uL2RvbWFpbnMvc3RhdHVzJyk7XG5jb25zdCBjc3RyID0gcmVxdWlyZSgnLi9jb25zdHJhaW50cycpO1xuXG4vLyBhcmd1bWVudHMgYXJlIFwiIG9sZFN0YXR1cyAoLCBuYW1lLCB2YWwpKiBcIlxuZnVuY3Rpb24gY2hhbmdlZFN0YXR1cyhvbGRTdGF0dXMpIHtcbiAgICBjb25zdCBuZXdTdGF0dXMgPSBuZXcgc3RhdHVzLlN0YXR1cztcbiAgICBmb3IgKGxldCBpID0gMTsgaSA8IGFyZ3VtZW50cy5sZW5ndGg7IGkgPSBpICsgMilcbiAgICAgICAgbmV3U3RhdHVzW2FyZ3VtZW50c1tpXV0gPSBhcmd1bWVudHNbaSsxXTtcblxuICAgIGZvciAobGV0IHAgaW4gb2xkU3RhdHVzKSB7XG4gICAgICAgIGlmIChuZXdTdGF0dXNbcF0gPT09IHVuZGVmaW5lZClcbiAgICAgICAgICAgIG5ld1N0YXR1c1twXSA9IG9sZFN0YXR1c1twXTtcbiAgICB9XG4gICAgcmV0dXJuIG5ld1N0YXR1cztcbn1cblxuLy8gcmV0dXJucyBbYWNjZXNzIHR5cGUsIHByb3AgdmFsdWVdXG5mdW5jdGlvbiBwcm9wQWNjZXNzKG5vZGUpIHtcbiAgICBjb25zdCBwcm9wID0gbm9kZS5wcm9wZXJ0eTtcbiAgICBpZiAoIW5vZGUuY29tcHV0ZWQpIHtcbiAgICAgICAgcmV0dXJuIFsnZG90QWNjZXNzJywgcHJvcC5uYW1lXTtcbiAgICB9XG4gICAgaWYgKHByb3AudHlwZSA9PT0gJ0xpdGVyYWwnKSB7XG4gICAgICAgIGlmICh0eXBlb2YgcHJvcC52YWx1ZSA9PT0gJ3N0cmluZycpXG4gICAgICAgICAgICByZXR1cm4gWydzdHJpbmdMaXRlcmFsJywgcHJvcC52YWx1ZV07XG4gICAgICAgIGlmICh0eXBlb2YgcHJvcC52YWx1ZSA9PT0gJ251bWJlcicpXG4gICAgICAgICAgICAvLyBjb252ZXJ0IG51bWJlciB0byBzdHJpbmdcbiAgICAgICAgICAgIHJldHVybiBbJ251bWJlckxpdGVyYWwnLCBwcm9wLnZhbHVlICsgJyddO1xuICAgIH1cbiAgICByZXR1cm4gW1wiY29tcHV0ZWRcIiwgbnVsbF07XG59XG5cbmZ1bmN0aW9uIHVub3BSZXN1bHRUeXBlKG9wKSB7XG4gICAgc3dpdGNoIChvcCkge1xuICAgICAgICBjYXNlICcrJzogY2FzZSAnLSc6IGNhc2UgJ34nOlxuICAgICAgICAgICAgcmV0dXJuIHR5cGVzLlByaW1OdW1iZXI7XG4gICAgICAgIGNhc2UgJyEnOlxuICAgICAgICAgICAgcmV0dXJuIHR5cGVzLlByaW1Cb29sZWFuO1xuICAgICAgICBjYXNlICd0eXBlb2YnOlxuICAgICAgICAgICAgcmV0dXJuIHR5cGVzLlByaW1TdHJpbmc7XG4gICAgICAgIGNhc2UgJ3ZvaWQnOiBjYXNlICdkZWxldGUnOlxuICAgICAgICAgICAgcmV0dXJuIG51bGw7XG4gICAgfVxufVxuXG5mdW5jdGlvbiBiaW5vcElzQm9vbGVhbihvcCkge1xuICAgIHN3aXRjaCAob3ApIHtcbiAgICAgICAgY2FzZSAnPT0nOiBjYXNlICchPSc6IGNhc2UgJz09PSc6IGNhc2UgJyE9PSc6XG4gICAgICAgIGNhc2UgJzwnOiBjYXNlICc+JzogY2FzZSAnPj0nOiBjYXNlICc8PSc6XG4gICAgICAgIGNhc2UgJ2luJzogY2FzZSAnaW5zdGFuY2VvZic6XG4gICAgICAgICAgICByZXR1cm4gdHJ1ZTtcbiAgICB9XG4gICAgcmV0dXJuIGZhbHNlO1xufVxuXG5mdW5jdGlvbiByZWFkTWVtYmVyKG5vZGUsIGN1clN0YXR1cywgYykge1xuICAgIGNvbnN0IHJldCA9IG5ldyB0eXBlcy5BVmFsO1xuICAgIGNvbnN0IG9iakFWYWwgPSBjKG5vZGUub2JqZWN0LCBjdXJTdGF0dXMsIHVuZGVmaW5lZCk7XG4gICAgaWYgKG5vZGUucHJvcGVydHkudHlwZSAhPT0gJ0lkZW50aWZpZXInKSB7XG4gICAgICAgIC8vIHJldHVybiBmcm9tIHByb3BlcnR5IGlzIGlnbm9yZWRcbiAgICAgICAgYyhub2RlLnByb3BlcnR5LCBjdXJTdGF0dXMsIHVuZGVmaW5lZCk7XG4gICAgfVxuICAgIGNvbnN0IHByb3BBY2MgPSBwcm9wQWNjZXNzKG5vZGUpO1xuXG4gICAgY29uc3RyYWludHMucHVzaCh7T0JKOiBvYmpBVmFsLFxuICAgICAgICAgICAgICAgICAgICAgIFBST1A6IHByb3BBY2NbMV0sXG4gICAgICAgICAgICAgICAgICAgICAgUkVBRF9UTzogcmV0fSk7XG4gICAgb2JqQVZhbC5wcm9wYWdhdGUobmV3IGNzdHIuUmVhZFByb3AocHJvcEFjY1sxXSwgcmV0KSk7XG5cbiAgICAvLyByZXR1cm5zIEFWYWwgZm9yIHJlY2VpdmVyIGFuZCByZWFkIG1lbWJlclxuICAgIHJldHVybiBbb2JqQVZhbCwgcmV0XTtcbn1cbi8vIFRvIHByZXZlbnQgcmVjdXJzaW9uLFxuLy8gd2UgcmVtZW1iZXIgdGhlIHN0YXR1cyB1c2VkIGluIGFkZENvbnN0cmFpbnRzXG5jb25zdCB2aXNpdGVkU3RhdHVzID0gW107XG5jb25zdCBjb25zdHJhaW50cyA9IFtdO1xuZnVuY3Rpb24gY2xlYXJDb25zdHJhaW50cygpIHtcbiAgICB2aXNpdGVkU3RhdHVzLmxlbmd0aCA9IDA7XG4gICAgY29uc3RyYWludHMubGVuZ3RoID0gMDtcbn1cblxubGV0IHJ0Q1g7XG5mdW5jdGlvbiBhZGRDb25zdHJhaW50cyhhc3QsIGluaXRTdGF0dXMsIG5ld1J0Q1gpIHtcblxuICAgIC8vIHNldCBydENYXG4gICAgcnRDWCA9IG5ld1J0Q1ggfHwgcnRDWDtcblxuICAgIC8vIENoZWNrIHdoZXRoZXIgd2UgaGF2ZSBwcm9jZXNzZWQgJ2luaXRTdGF0dXMnIGJlZm9yZVxuICAgIGZvciAobGV0IGk9MDsgaSA8IHZpc2l0ZWRTdGF0dXMubGVuZ3RoOyBpKyspIHtcbiAgICAgICAgaWYgKGluaXRTdGF0dXMuZXF1YWxzKHZpc2l0ZWRTdGF0dXNbaV0pKSB7XG4gICAgICAgICAgICAgLy8gSWYgc28sIGRvIG5vdGhpbmdcbiAgICAgICAgICAgICAvLyBzaWduaWZ5aW5nIHdlIGRpZG4ndCBhZGQgY29uc3RyYWludHNcbiAgICAgICAgICAgICByZXR1cm4gZmFsc2U7XG4gICAgICAgICB9XG4gICAgfVxuICAgIC8vIElmIHRoZSBpbml0U3RhdHVzIGlzIG5ldywgcHVzaCBpdC5cbiAgICAvLyBXZSBkbyBub3QgcmVjb3JkIGFzdCBzaW5jZSBhc3Qgbm9kZSBkZXBlbmRzIG9uIHRoZSBzdGF0dXNcbiAgICB2aXNpdGVkU3RhdHVzLnB1c2goaW5pdFN0YXR1cyk7XG5cbiAgICAvLyBjb25zdHJhaW50IGdlbmVyYXRpbmcgd2Fsa2VyIGZvciBleHByZXNzaW9uc1xuICAgIGNvbnN0IGNvbnN0cmFpbnRHZW5lcmF0b3IgPSB3YWxrLm1ha2Uoe1xuXG4gICAgICAgIElkZW50aWZpZXI6IGZ1bmN0aW9uIChub2RlLCBjdXJTdGF0dXMsIGMpIHtcbiAgICAgICAgICAgIHJldHVybiBjdXJTdGF0dXMuc2MuZ2V0QVZhbE9mKG5vZGUubmFtZSk7XG4gICAgICAgIH0sXG5cbiAgICAgICAgVGhpc0V4cHJlc3Npb246IGZ1bmN0aW9uIChub2RlLCBjdXJTdGF0dXMsIGMpIHtcbiAgICAgICAgICAgIHJldHVybiBjdXJTdGF0dXMuc2VsZjtcbiAgICAgICAgfSxcblxuICAgICAgICBMaXRlcmFsOiBmdW5jdGlvbiAobm9kZSwgY3VyU3RhdHVzLCBjKSB7XG4gICAgICAgICAgICBjb25zdCByZXMgPSBuZXcgdHlwZXMuQVZhbDtcbiAgICAgICAgICAgIGlmIChub2RlLnJlZ2V4KSB7XG4gICAgICAgICAgICAgICAgLy8gbm90IGltcGxlbWVudGVkIHlldFxuICAgICAgICAgICAgICAgIC8vIHRocm93IG5ldyBFcnJvcigncmVnZXggbGl0ZXJhbCBpcyBub3QgaW1wbGVtZW50ZWQgeWV0Jyk7XG4gICAgICAgICAgICAgICAgcmV0dXJuIHJlcztcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIHN3aXRjaCAodHlwZW9mIG5vZGUudmFsdWUpIHtcbiAgICAgICAgICAgIGNhc2UgJ251bWJlcic6XG4gICAgICAgICAgICAgICAgY29uc3RyYWludHMucHVzaCh7VFlQRTogdHlwZXMuUHJpbU51bWJlcixcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBJTkNMX1NFVDogcmVzfSk7XG4gICAgICAgICAgICAgICAgcmVzLmFkZFR5cGUodHlwZXMuUHJpbU51bWJlcik7XG4gICAgICAgICAgICAgICAgYnJlYWs7XG4gICAgICAgICAgICBjYXNlICdzdHJpbmcnOlxuICAgICAgICAgICAgICAgIGNvbnN0cmFpbnRzLnB1c2goe1RZUEU6IHR5cGVzLlByaW1TdHJpbmcsXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgSU5DTF9TRVQ6IHJlc30pO1xuICAgICAgICAgICAgICAgIHJlcy5hZGRUeXBlKHR5cGVzLlByaW1TdHJpbmcpO1xuICAgICAgICAgICAgICAgIGJyZWFrO1xuICAgICAgICAgICAgY2FzZSAnYm9vbGVhbic6XG4gICAgICAgICAgICAgICAgY29uc3RyYWludHMucHVzaCh7VFlQRTogdHlwZXMuUHJpbUJvb2xlYW4sXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgSU5DTF9TRVQ6IHJlc30pO1xuICAgICAgICAgICAgICAgIHJlcy5hZGRUeXBlKHR5cGVzLlByaW1Cb29sZWFuKTtcbiAgICAgICAgICAgICAgICBicmVhaztcbiAgICAgICAgICAgIGNhc2UgJ29iamVjdCc6XG4gICAgICAgICAgICAgICAgLy8gSSBndWVzczogTGl0ZXJhbCAmJiBvYmplY3QgPT0+IG5vZGUudmFsdWUgPT0gbnVsbFxuICAgICAgICAgICAgICAgIC8vIG51bGwgaXMgaWdub3JlZCwgc28gbm90aGluZyB0byBhZGRcbiAgICAgICAgICAgICAgICBicmVhaztcbiAgICAgICAgICAgIGNhc2UgJ2Z1bmN0aW9uJzpcbiAgICAgICAgICAgICAgICB0aHJvdyBuZXcgRXJyb3IoJ0kgZ3Vlc3MgZnVuY3Rpb24gaXMgaW1wb3NzaWJsZSBoZXJlLicpO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgcmV0dXJuIHJlcztcbiAgICAgICAgfSxcblxuICAgICAgICBBc3NpZ25tZW50RXhwcmVzc2lvbjogZnVuY3Rpb24gKG5vZGUsIGN1clN0YXR1cywgYykge1xuICAgICAgICAgICAgY29uc3QgcmhzQVZhbCA9IGMobm9kZS5yaWdodCwgY3VyU3RhdHVzLCB1bmRlZmluZWQpO1xuICAgICAgICAgICAgaWYgKG5vZGUubGVmdC50eXBlICE9PSAnTWVtYmVyRXhwcmVzc2lvbicpIHtcbiAgICAgICAgICAgICAgICAvLyBMSFMgaXMgYSBzaW1wbGUgdmFyaWFibGUuXG4gICAgICAgICAgICAgICAgY29uc3QgdmFyTmFtZSA9IG5vZGUubGVmdC5uYW1lO1xuICAgICAgICAgICAgICAgIGNvbnN0IGxoc0FWYWwgPSBjdXJTdGF0dXMuc2MuZ2V0QVZhbE9mKHZhck5hbWUpO1xuXG4gICAgICAgICAgICAgICAgaWYgKG5vZGUub3BlcmF0b3IgPT09ICc9Jykge1xuICAgICAgICAgICAgICAgICAgICAvLyBzaW1wbGUgYXNzaWdubWVudFxuICAgICAgICAgICAgICAgICAgICBjb25zdHJhaW50cy5wdXNoKHtcbiAgICAgICAgICAgICAgICAgICAgICAgIEZST006IHJoc0FWYWwsXG4gICAgICAgICAgICAgICAgICAgICAgICBUTzogbGhzQVZhbFxuICAgICAgICAgICAgICAgICAgICB9KTtcbiAgICAgICAgICAgICAgICAgICAgcmhzQVZhbC5wcm9wYWdhdGUobGhzQVZhbCk7XG4gICAgICAgICAgICAgICAgICAgIC8vIGNvcnJlc3BvbmRpbmcgQVZhbCBpcyB0aGUgUkhTXG4gICAgICAgICAgICAgICAgICAgIHJldHVybiByaHNBVmFsO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICBjb25zdCByZXNBVmFsID0gbmV3IHR5cGVzLkFWYWw7XG4gICAgICAgICAgICAgICAgaWYgKG5vZGUub3BlcmF0b3IgPT09ICcrPScpIHtcbiAgICAgICAgICAgICAgICAgICAgLy8gY29uY2F0ZW5hdGluZyB1cGRhdGVcbiAgICAgICAgICAgICAgICAgICAgY29uc3RyYWludHMucHVzaCh7XG4gICAgICAgICAgICAgICAgICAgICAgICBBRERfT1BSRDE6IGxoc0FWYWwsXG4gICAgICAgICAgICAgICAgICAgICAgICBBRERfT1BSRDI6IHJoc0FWYWwsXG4gICAgICAgICAgICAgICAgICAgICAgICBSRVNVTFQ6IHJlc0FWYWxcbiAgICAgICAgICAgICAgICAgICAgfSk7XG4gICAgICAgICAgICAgICAgICAgIGxoc0FWYWwucHJvcGFnYXRlKG5ldyBjc3RyLklzQWRkZWQocmhzQVZhbCwgcmVzQVZhbCkpO1xuICAgICAgICAgICAgICAgICAgICByaHNBVmFsLnByb3BhZ2F0ZShuZXcgY3N0ci5Jc0FkZGVkKGxoc0FWYWwsIHJlc0FWYWwpKTtcbiAgICAgICAgICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgICAgICAgICAgICAvLyBhcml0aG1ldGljIHVwZGF0ZVxuICAgICAgICAgICAgICAgICAgICBjb25zdHJhaW50cy5wdXNoKHtcbiAgICAgICAgICAgICAgICAgICAgICAgIFRZUEU6dHlwZXMuUHJpbU51bWJlcixcbiAgICAgICAgICAgICAgICAgICAgICAgIElOQ0xfU0VUOiByZXNBVmFsXG4gICAgICAgICAgICAgICAgICAgIH0pO1xuICAgICAgICAgICAgICAgICAgICByZXNBVmFsLmFkZFR5cGUodHlwZXMuUHJpbU51bWJlcik7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIHJldHVybiByZXNBVmFsO1xuICAgICAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICAgICAgICAvLyBtZW1iZXIgYXNzaWdubWVudFxuICAgICAgICAgICAgICAgIGNvbnN0IG9iakFWYWwgPSBjKG5vZGUubGVmdC5vYmplY3QsIGN1clN0YXR1cywgdW5kZWZpbmVkKTtcbiAgICAgICAgICAgICAgICBjb25zdCBwcm9wQWNjID0gcHJvcEFjY2Vzcyhub2RlLmxlZnQpO1xuICAgICAgICAgICAgICAgIGlmIChub2RlLm9wZXJhdG9yID09PSAnPScpIHtcbiAgICAgICAgICAgICAgICAgICAgLy8gYXNzaWdubWVudCB0byBtZW1iZXJcbiAgICAgICAgICAgICAgICAgICAgY29uc3RyYWludHMucHVzaCh7XG4gICAgICAgICAgICAgICAgICAgICAgICBPQko6IG9iakFWYWwsXG4gICAgICAgICAgICAgICAgICAgICAgICBQUk9QOiBwcm9wQWNjWzFdLFxuICAgICAgICAgICAgICAgICAgICAgICAgV1JJVEVfV0lUSDogcmhzQVZhbFxuICAgICAgICAgICAgICAgICAgICB9KTtcbiAgICAgICAgICAgICAgICAgICAgb2JqQVZhbC5wcm9wYWdhdGUobmV3IGNzdHIuV3JpdGVQcm9wKHByb3BBY2NbMV0sIHJoc0FWYWwpKTtcbiAgICAgICAgICAgICAgICAgICAgLy8gaWYgcHJvcGVydHkgaXMgbnVtYmVyIGxpdGVyYWwsIGFsc28gd3JpdGUgdG8gJ3Vua25vd24nXG4gICAgICAgICAgICAgICAgICAgIGlmIChwcm9wQWNjWzBdID09PSAnbnVtYmVyTGl0ZXJhbCcpIHtcbiAgICAgICAgICAgICAgICAgICAgICAgIG9iakFWYWwucHJvcGFnYXRlKG5ldyBjc3RyLldyaXRlUHJvcChudWxsLCByaHNBVmFsKSk7XG4gICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgcmV0dXJuIHJoc0FWYWw7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIGNvbnN0IHJlc0FWYWwgPSBuZXcgdHlwZXMuQVZhbDtcbiAgICAgICAgICAgICAgICBjb25zdCByZWN2QW5kUmV0ID0gcmVhZE1lbWJlcihub2RlLmxlZnQsIGN1clN0YXR1cywgYyk7XG4gICAgICAgICAgICAgICAgaWYgKG5vZGUub3BlcmF0b3IgPT09ICcrPScpIHtcbiAgICAgICAgICAgICAgICAgICAgLy8gY29uY2F0ZW5hdGluZyB1cGRhdGVcbiAgICAgICAgICAgICAgICAgICAgY29uc3RyYWludHMucHVzaCh7XG4gICAgICAgICAgICAgICAgICAgICAgICBBRERfT1BSRDE6IHJlY3ZBbmRSZXRbMV0sXG4gICAgICAgICAgICAgICAgICAgICAgICBBRERfT1BSRDI6IHJoc0FWYWwsXG4gICAgICAgICAgICAgICAgICAgICAgICBSRVNVTFQ6IHJlc0FWYWxcbiAgICAgICAgICAgICAgICAgICAgfSk7XG4gICAgICAgICAgICAgICAgICAgIHJlY3ZBbmRSZXRbMV0ucHJvcGFnYXRlKG5ldyBjc3RyLklzQWRkZWQocmhzQVZhbCwgcmVzQVZhbCkpO1xuICAgICAgICAgICAgICAgICAgICByaHNBVmFsLnByb3BhZ2F0ZShuZXcgY3N0ci5Jc0FkZGVkKHJlY3ZBbmRSZXRbMV0sIHJlc0FWYWwpKTtcbiAgICAgICAgICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgICAgICAgICAgICAvLyBhcml0aG1ldGljIHVwZGF0ZVxuICAgICAgICAgICAgICAgICAgICBjb25zdHJhaW50cy5wdXNoKHtcbiAgICAgICAgICAgICAgICAgICAgICAgIFRZUEU6IHR5cGVzLlByaW1OdW1iZXIsXG4gICAgICAgICAgICAgICAgICAgICAgICBJTkNMX1NFVDogcmVzQVZhbFxuICAgICAgICAgICAgICAgICAgICB9KTtcbiAgICAgICAgICAgICAgICAgICAgcmVzQVZhbC5hZGRUeXBlKHR5cGVzLlByaW1OdW1iZXIpO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICByZXR1cm4gcmVzQVZhbDtcbiAgICAgICAgICAgIH1cbiAgICAgICAgfSxcblxuICAgICAgICBWYXJpYWJsZURlY2xhcmF0aW9uOiBmdW5jdGlvbiAobm9kZSwgY3VyU3RhdHVzLCBjKSB7XG4gICAgICAgICAgICBmb3IgKGxldCBpID0gMDsgaSA8IG5vZGUuZGVjbGFyYXRpb25zLmxlbmd0aDsgaSsrKSB7XG4gICAgICAgICAgICAgICAgY29uc3QgZGVjbCA9IG5vZGUuZGVjbGFyYXRpb25zW2ldO1xuICAgICAgICAgICAgICAgIGlmIChkZWNsLmluaXQpIHtcbiAgICAgICAgICAgICAgICAgICAgY29uc3QgbGhzQVZhbCA9IGN1clN0YXR1cy5zYy5nZXRBVmFsT2YoZGVjbC5pZC5uYW1lKTtcbiAgICAgICAgICAgICAgICAgICAgY29uc3QgcmhzQVZhbCA9IGMoZGVjbC5pbml0LCBjdXJTdGF0dXMsIHVuZGVmaW5lZCk7XG4gICAgICAgICAgICAgICAgICAgIGNvbnN0cmFpbnRzLnB1c2goe0ZST006IHJoc0FWYWwsXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIFRPOiBsaHNBVmFsfSk7XG4gICAgICAgICAgICAgICAgICAgIHJoc0FWYWwucHJvcGFnYXRlKGxoc0FWYWwpO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgIH1cbiAgICAgICAgfSxcblxuICAgICAgICBMb2dpY2FsRXhwcmVzc2lvbjogZnVuY3Rpb24gKG5vZGUsIGN1clN0YXR1cywgYykge1xuICAgICAgICAgICAgY29uc3QgcmVzID0gbmV3IHR5cGVzLkFWYWw7XG4gICAgICAgICAgICBjb25zdCBsZWZ0ID0gYyhub2RlLmxlZnQsIGN1clN0YXR1cywgdW5kZWZpbmVkKTtcbiAgICAgICAgICAgIGNvbnN0IHJpZ2h0ID0gYyhub2RlLnJpZ2h0LCBjdXJTdGF0dXMsIHVuZGVmaW5lZCk7XG4gICAgICAgICAgICBjb25zdHJhaW50cy5wdXNoKHtGUk9NOiBsZWZ0LCBUTzogcmVzfSxcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAge0ZST006IHJpZ2h0LCBUTzogcmVzfSk7XG4gICAgICAgICAgICBsZWZ0LnByb3BhZ2F0ZShyZXMpO1xuICAgICAgICAgICAgcmlnaHQucHJvcGFnYXRlKHJlcyk7XG4gICAgICAgICAgICByZXR1cm4gcmVzO1xuICAgICAgICB9LFxuXG4gICAgICAgIENvbmRpdGlvbmFsRXhwcmVzc2lvbjogZnVuY3Rpb24gKG5vZGUsIGN1clN0YXR1cywgYykge1xuICAgICAgICAgICAgY29uc3QgcmVzID0gbmV3IHR5cGVzLkFWYWw7XG4gICAgICAgICAgICBjKG5vZGUudGVzdCwgY3VyU3RhdHVzLCB1bmRlZmluZWQpO1xuICAgICAgICAgICAgY29uc3QgY29ucyA9IGMobm9kZS5jb25zZXF1ZW50LCBjdXJTdGF0dXMsIHVuZGVmaW5lZCk7XG4gICAgICAgICAgICBjb25zdCBhbHQgPSBjKG5vZGUuYWx0ZXJuYXRlLCBjdXJTdGF0dXMsIHVuZGVmaW5lZCk7XG4gICAgICAgICAgICBjb25zdHJhaW50cy5wdXNoKHtGUk9NOiBjb25zLCBUTzogcmVzfSxcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAge0ZST006IGFsdCwgVE86IHJlc30pO1xuICAgICAgICAgICAgY29ucy5wcm9wYWdhdGUocmVzKTtcbiAgICAgICAgICAgIGFsdC5wcm9wYWdhdGUocmVzKTtcbiAgICAgICAgICAgIHJldHVybiByZXM7XG4gICAgICAgIH0sXG5cbiAgICAgICAgTmV3RXhwcmVzc2lvbjogZnVuY3Rpb24gKG5vZGUsIGN1clN0YXR1cywgYykge1xuICAgICAgICAgICAgY29uc3QgcmV0ID0gbmV3IHR5cGVzLkFWYWw7XG4gICAgICAgICAgICBjb25zdCBjYWxsZWUgPSBjKG5vZGUuY2FsbGVlLCBjdXJTdGF0dXMsIHVuZGVmaW5lZCk7XG4gICAgICAgICAgICBjb25zdCBhcmdzID0gW107XG4gICAgICAgICAgICBmb3IgKGxldCBpID0gMDsgaSA8IG5vZGUuYXJndW1lbnRzLmxlbmd0aDsgaSsrKSB7XG4gICAgICAgICAgICAgICAgYXJncy5wdXNoKGMobm9kZS5hcmd1bWVudHNbaV0sIGN1clN0YXR1cywgdW5kZWZpbmVkKSk7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBjb25zdCBuZXdEZWx0YSA9IGN1clN0YXR1cy5kZWx0YS5hcHBlbmRPbmUobm9kZVsnQGxhYmVsJ10pO1xuICAgICAgICAgICAgY29uc3RyYWludHMucHVzaCh7Q09OU1RSVUNUT1I6IGNhbGxlZSxcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIEFSR1M6IGFyZ3MsXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICBSRVQ6IHJldCxcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIEVYQzogY3VyU3RhdHVzLmV4YyxcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIERFTFRBOiBuZXdEZWx0YX0pO1xuICAgICAgICAgICAgY2FsbGVlLnByb3BhZ2F0ZShcbiAgICAgICAgICAgICAgICBuZXcgY3N0ci5Jc0N0b3IoXG4gICAgICAgICAgICAgICAgICAgIGFyZ3MsXG4gICAgICAgICAgICAgICAgICAgIHJldCxcbiAgICAgICAgICAgICAgICAgICAgY3VyU3RhdHVzLmV4YyxcbiAgICAgICAgICAgICAgICAgICAgbmV3RGVsdGEpKTtcbiAgICAgICAgICAgIHJldHVybiByZXQ7XG4gICAgICAgIH0sXG5cbiAgICAgICAgQXJyYXlFeHByZXNzaW9uOiBmdW5jdGlvbiAobm9kZSwgY3VyU3RhdHVzLCBjKSB7XG4gICAgICAgICAgICBjb25zdCByZXQgPSBuZXcgdHlwZXMuQVZhbDtcbiAgICAgICAgICAgIGNvbnN0IGFyclR5cGUgPSBuZXcgdHlwZXMuQXJyVHlwZShuZXcgdHlwZXMuQVZhbChydENYLnByb3Rvcy5BcnJheSkpO1xuICAgICAgICAgICAgLy8gYWRkIGxlbmd0aCBwcm9wZXJ0eVxuICAgICAgICAgICAgYXJyVHlwZS5nZXRQcm9wKCdsZW5ndGgnKS5hZGRUeXBlKHR5cGVzLlByaW1OdW1iZXIpO1xuXG4gICAgICAgICAgICBjb25zdHJhaW50cy5wdXNoKHtUWVBFOiBhcnJUeXBlLCBJTkNMX1NFVDogcmV0fSk7XG4gICAgICAgICAgICByZXQuYWRkVHlwZShhcnJUeXBlKTtcblxuICAgICAgICAgICAgLy8gYWRkIGFycmF5IGVsZW1lbnRzXG4gICAgICAgICAgICBmb3IgKGxldCBpID0gMDsgaSA8IG5vZGUuZWxlbWVudHMubGVuZ3RoOyBpKyspIHtcbiAgICAgICAgICAgICAgICBjb25zdCBlbHRBVmFsID0gYyhub2RlLmVsZW1lbnRzW2ldLCBjdXJTdGF0dXMsIHVuZGVmaW5lZCk7XG5cbiAgICAgICAgICAgICAgICBjb25zdCBwcm9wID0gaSArICcnO1xuICAgICAgICAgICAgICAgIGNvbnN0cmFpbnRzLnB1c2goe09CSjogcmV0LCBQUk9QOiBwcm9wLCBBVkFMOiBlbHRBVmFsfSk7XG4gICAgICAgICAgICAgICAgY29uc3RyYWludHMucHVzaCh7T0JKOiByZXQsIFBST1A6IG51bGwsIEFWQUw6IGVsdEFWYWx9KTtcbiAgICAgICAgICAgICAgICByZXQucHJvcGFnYXRlKG5ldyBjc3RyLldyaXRlUHJvcChwcm9wLCBlbHRBVmFsKSk7XG4gICAgICAgICAgICAgICAgcmV0LnByb3BhZ2F0ZShuZXcgY3N0ci5Xcml0ZVByb3AobnVsbCwgZWx0QVZhbCkpO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgcmV0dXJuIHJldDtcbiAgICAgICAgfSxcblxuICAgICAgICBPYmplY3RFeHByZXNzaW9uOiBmdW5jdGlvbiAobm9kZSwgY3VyU3RhdHVzLCBjKSB7XG4gICAgICAgICAgICBjb25zdCByZXQgPSBuZXcgdHlwZXMuQVZhbDtcbiAgICAgICAgICAgIGNvbnN0IG9ialR5cGUgPSBuZXcgdHlwZXMuT2JqVHlwZShuZXcgdHlwZXMuQVZhbChydENYLnByb3Rvcy5PYmplY3QpKTtcbiAgICAgICAgICAgIGNvbnN0cmFpbnRzLnB1c2goe1RZUEU6IG9ialR5cGUsIElOQ0xfU0VUOiByZXR9KTtcbiAgICAgICAgICAgIHJldC5hZGRUeXBlKG9ialR5cGUpO1xuXG4gICAgICAgICAgICBmb3IgKGxldCBpID0gMDsgaSA8IG5vZGUucHJvcGVydGllcy5sZW5ndGg7IGkrKykge1xuICAgICAgICAgICAgICAgIGNvbnN0IHByb3BQYWlyID0gbm9kZS5wcm9wZXJ0aWVzW2ldO1xuICAgICAgICAgICAgICAgIGNvbnN0IHByb3BLZXkgPSBwcm9wUGFpci5rZXk7XG4gICAgICAgICAgICAgICAgbGV0IG5hbWU7XG4gICAgICAgICAgICAgICAgY29uc3QgcHJvcEV4cHIgPSBwcm9wUGFpci52YWx1ZTtcblxuICAgICAgICAgICAgICAgIGNvbnN0IGZsZEFWYWwgPSBjKHByb3BFeHByLCBjdXJTdGF0dXMsIHVuZGVmaW5lZCk7XG5cbiAgICAgICAgICAgICAgICBpZiAocHJvcEtleS50eXBlID09PSAnSWRlbnRpZmllcicpIHtcbiAgICAgICAgICAgICAgICAgICAgbmFtZSA9IHByb3BLZXkubmFtZTtcbiAgICAgICAgICAgICAgICB9IGVsc2UgaWYgKHR5cGVvZiBwcm9wS2V5LnZhbHVlID09PSAnc3RyaW5nJykge1xuICAgICAgICAgICAgICAgICAgICBuYW1lID0gcHJvcEtleS52YWx1ZTtcbiAgICAgICAgICAgICAgICB9IGVsc2UgaWYgKHR5cGVvZiBwcm9wS2V5LnZhbHVlID09PSAnbnVtYmVyJykge1xuICAgICAgICAgICAgICAgICAgICAvLyBjb252ZXJ0IG51bWJlciB0byBzdHJpbmdcbiAgICAgICAgICAgICAgICAgICAgbmFtZSA9IHByb3BLZXkudmFsdWUgKyAnJztcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgY29uc3RyYWludHMucHVzaCh7T0JKOiByZXQsIFBST1A6IG5hbWUsIEFWQUw6IGZsZEFWYWx9KTtcbiAgICAgICAgICAgICAgICByZXQucHJvcGFnYXRlKG5ldyBjc3RyLldyaXRlUHJvcChuYW1lLCBmbGRBVmFsKSk7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICByZXR1cm4gcmV0O1xuICAgICAgICB9LFxuXG4gICAgICAgIEZ1bmN0aW9uRXhwcmVzc2lvbjogZnVuY3Rpb24gKG5vZGUsIGN1clN0YXR1cywgYykge1xuICAgICAgICAgICAgaWYgKCFub2RlLmZuSW5zdGFuY2VzKSB7XG4gICAgICAgICAgICAgICAgbm9kZS5mbkluc3RhbmNlcyA9IFtdO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgbGV0IGZuSW5zdGFuY2UgPSBudWxsO1xuICAgICAgICAgICAgbm9kZS5mbkluc3RhbmNlcy5mb3JFYWNoKGZ1bmN0aW9uIChmblR5cGUpIHtcbiAgICAgICAgICAgICAgICBpZiAoZm5UeXBlLnNjID09PSBjdXJTdGF0dXMuc2MpIHtcbiAgICAgICAgICAgICAgICAgICAgZm5JbnN0YW5jZSA9IGZuVHlwZTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICB9KTtcbiAgICAgICAgICAgIGlmICghZm5JbnN0YW5jZSkge1xuICAgICAgICAgICAgICAgIGZuSW5zdGFuY2VcbiAgICAgICAgICAgICAgICAgICAgPSBuZXcgdHlwZXMuRm5UeXBlKG5ldyB0eXBlcy5BVmFsKHJ0Q1gucHJvdG9zLkZ1bmN0aW9uKSxcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICdbYW5vbnltb3VzIGZ1bmN0aW9uXScsXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBub2RlLmJvZHlbJ0BibG9jayddLmdldFBhcmFtVmFyTmFtZXMoKSxcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGN1clN0YXR1cy5zYyxcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIG5vZGUsXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBydENYLnByb3Rvcy5PYmplY3QpO1xuICAgICAgICAgICAgICAgIG5vZGUuZm5JbnN0YW5jZXMucHVzaChmbkluc3RhbmNlKTtcbiAgICAgICAgICAgICAgICBjb25zdCBwcm90b3R5cGVPYmplY3QgPVxuICAgICAgICAgICAgICAgICAgICBuZXcgdHlwZXMuT2JqVHlwZShuZXcgdHlwZXMuQVZhbChydENYLnByb3Rvcy5PYmplY3QpLFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAnPy5wcm90b3R5cGUnKTtcbiAgICAgICAgICAgICAgICAvLyBGb3IgLnByb3RvdHlwZVxuICAgICAgICAgICAgICAgIGNvbnN0IHByb3RvdHlwZVByb3AgPSBmbkluc3RhbmNlLmdldFByb3AoJ3Byb3RvdHlwZScpO1xuICAgICAgICAgICAgICAgIGNvbnN0cmFpbnRzLnB1c2goe1RZUEU6IHByb3RvdHlwZU9iamVjdCxcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBJTkNMX1NFVDogcHJvdG90eXBlUHJvcH0pO1xuICAgICAgICAgICAgICAgIHByb3RvdHlwZVByb3AuYWRkVHlwZShwcm90b3R5cGVPYmplY3QpO1xuICAgICAgICAgICAgICAgIC8vIEZvciAucHJvdG90eXBlLmNvbnN0cnVjdG9yXG4gICAgICAgICAgICAgICAgY29uc3QgY29uc3RydWN0b3JQcm9wID0gcHJvdG90eXBlT2JqZWN0LmdldFByb3AoJ2NvbnN0cnVjdG9yJyk7XG4gICAgICAgICAgICAgICAgY29uc3RyYWludHMucHVzaCh7VFlQRTogZm5JbnN0YW5jZSxcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBJTkNMX1NFVDogY29uc3RydWN0b3JQcm9wfSk7XG4gICAgICAgICAgICAgICAgY29uc3RydWN0b3JQcm9wLmFkZFR5cGUoZm5JbnN0YW5jZSk7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBjb25zdCByZXQgPSBuZXcgdHlwZXMuQVZhbDtcbiAgICAgICAgICAgIGNvbnN0cmFpbnRzLnB1c2goe1RZUEU6IGZuSW5zdGFuY2UsXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICBJTkNMX1NFVDogcmV0fSk7XG4gICAgICAgICAgICByZXQuYWRkVHlwZShmbkluc3RhbmNlKTtcbiAgICAgICAgICAgIHJldHVybiByZXQ7XG4gICAgICAgIH0sXG5cbiAgICAgICAgRnVuY3Rpb25EZWNsYXJhdGlvbjogZnVuY3Rpb24gKG5vZGUsIGN1clN0YXR1cywgYykge1xuICAgICAgICAgICAgLy8gRHJvcCBpbml0aWFsIGNhdGNoIHNjb3Blc1xuICAgICAgICAgICAgY29uc3Qgc2MwID0gY3VyU3RhdHVzLnNjLnJlbW92ZUluaXRpYWxDYXRjaEJsb2NrcygpO1xuICAgICAgICAgICAgaWYgKCFub2RlLmZuSW5zdGFuY2VzKSB7XG4gICAgICAgICAgICAgICAgbm9kZS5mbkluc3RhbmNlcyA9IFtdO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgbGV0IGZuSW5zdGFuY2UgPSBudWxsO1xuICAgICAgICAgICAgbm9kZS5mbkluc3RhbmNlcy5mb3JFYWNoKGZ1bmN0aW9uIChmblR5cGUpIHtcbiAgICAgICAgICAgICAgICBpZiAoZm5UeXBlLnNjID09PSBzYzApIHtcbiAgICAgICAgICAgICAgICAgICAgZm5JbnN0YW5jZSA9IGZuVHlwZTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICB9KTtcbiAgICAgICAgICAgIGlmICghZm5JbnN0YW5jZSkge1xuICAgICAgICAgICAgICAgIGZuSW5zdGFuY2VcbiAgICAgICAgICAgICAgICAgICAgPSBuZXcgdHlwZXMuRm5UeXBlKG5ldyB0eXBlcy5BVmFsKHJ0Q1gucHJvdG9zLkZ1bmN0aW9uKSxcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIG5vZGUuaWQubmFtZSxcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIG5vZGUuYm9keVsnQGJsb2NrJ10uZ2V0UGFyYW1WYXJOYW1lcygpLFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgc2MwLFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgbm9kZSxcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIHJ0Q1gucHJvdG9zLk9iamVjdCk7XG4gICAgICAgICAgICAgICAgbm9kZS5mbkluc3RhbmNlcy5wdXNoKGZuSW5zdGFuY2UpO1xuICAgICAgICAgICAgICAgIC8vIGZvciBlYWNoIGZuSW5zdGFuY2UsIGFzc2lnbiBvbmUgcHJvdG90eXBlIG9iamVjdFxuICAgICAgICAgICAgICAgIGNvbnN0IHByb3RvdHlwZU9iamVjdCA9XG4gICAgICAgICAgICAgICAgICAgIG5ldyB0eXBlcy5PYmpUeXBlKG5ldyB0eXBlcy5BVmFsKHJ0Q1gucHJvdG9zLk9iamVjdCksXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIG5vZGUuaWQubmFtZSArICcucHJvdG90eXBlJyk7XG4gICAgICAgICAgICAgICAgLy8gRm9yIC5wcm90b3R5cGVcbiAgICAgICAgICAgICAgICBjb25zdCBwcm90b3R5cGVQcm9wID0gZm5JbnN0YW5jZS5nZXRQcm9wKCdwcm90b3R5cGUnKTtcbiAgICAgICAgICAgICAgICBjb25zdHJhaW50cy5wdXNoKHtUWVBFOiBwcm90b3R5cGVPYmplY3QsXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgSU5DTF9TRVQ6IHByb3RvdHlwZVByb3B9KTtcbiAgICAgICAgICAgICAgICBwcm90b3R5cGVQcm9wLmFkZFR5cGUocHJvdG90eXBlT2JqZWN0KTtcbiAgICAgICAgICAgICAgICAvLyBGb3IgLnByb3RvdHlwZS5jb25zdHJ1Y3RvclxuICAgICAgICAgICAgICAgIGNvbnN0IGNvbnN0cnVjdG9yUHJvcCA9IHByb3RvdHlwZU9iamVjdC5nZXRQcm9wKCdjb25zdHJ1Y3RvcicpO1xuICAgICAgICAgICAgICAgIGNvbnN0cmFpbnRzLnB1c2goe1RZUEU6IGZuSW5zdGFuY2UsXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgSU5DTF9TRVQ6IGNvbnN0cnVjdG9yUHJvcH0pO1xuICAgICAgICAgICAgICAgIGNvbnN0cnVjdG9yUHJvcC5hZGRUeXBlKGZuSW5zdGFuY2UpO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgY29uc3QgbGhzQVZhbCA9IHNjMC5nZXRBVmFsT2Yobm9kZS5pZC5uYW1lKTtcblxuICAgICAgICAgICAgY29uc3RyYWludHMucHVzaCh7VFlQRTogZm5JbnN0YW5jZSxcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIElOQ0xfU0VUOiBsaHNBVmFsfSk7XG4gICAgICAgICAgICBsaHNBVmFsLmFkZFR5cGUoZm5JbnN0YW5jZSk7XG4gICAgICAgICAgICAvLyBub3RoaW5nIHRvIHJldHVyblxuICAgICAgICAgICAgcmV0dXJuIHR5cGVzLkFWYWxOdWxsO1xuICAgICAgICB9LFxuXG4gICAgICAgIFNlcXVlbmNlRXhwcmVzc2lvbjogZnVuY3Rpb24gKG5vZGUsIGN1clN0YXR1cywgYykge1xuICAgICAgICAgICAgY29uc3QgbGFzdEluZGV4ID0gbm9kZS5leHByZXNzaW9ucy5sZW5ndGggLSAxO1xuICAgICAgICAgICAgZm9yIChsZXQgaSA9IDA7IGkgPCBsYXN0SW5kZXg7IGkrKykge1xuICAgICAgICAgICAgICAgIGMobm9kZS5leHByZXNzaW9uc1tpXSwgY3VyU3RhdHVzLCB1bmRlZmluZWQpO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgcmV0dXJuIGMobm9kZS5leHByZXNzaW9uc1tsYXN0SW5kZXhdLCBjdXJTdGF0dXMsIHVuZGVmaW5lZCk7XG4gICAgICAgIH0sXG5cbiAgICAgICAgVW5hcnlFeHByZXNzaW9uOiBmdW5jdGlvbiAobm9kZSwgY3VyU3RhdHVzLCBjKSB7XG4gICAgICAgICAgICBjKG5vZGUuYXJndW1lbnQsIGN1clN0YXR1cywgdW5kZWZpbmVkKTtcbiAgICAgICAgICAgIGNvbnN0IHJlcyA9IG5ldyB0eXBlcy5BVmFsO1xuICAgICAgICAgICAgY29uc3QgdHlwZSA9IHVub3BSZXN1bHRUeXBlKG5vZGUub3BlcmF0b3IpO1xuICAgICAgICAgICAgaWYgKHR5cGUpIHtcbiAgICAgICAgICAgICAgICBjb25zdHJhaW50cy5wdXNoKHtUWVBFOiB0eXBlLFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIElOQ0xfU0VUOiByZXN9KTtcbiAgICAgICAgICAgICAgICByZXMuYWRkVHlwZSh0eXBlKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIHJldHVybiByZXM7XG4gICAgICAgIH0sXG5cbiAgICAgICAgVXBkYXRlRXhwcmVzc2lvbjogZnVuY3Rpb24gKG5vZGUsIGN1clN0YXR1cywgYykge1xuICAgICAgICAgICAgYyhub2RlLmFyZ3VtZW50LCBjdXJTdGF0dXMsIHVuZGVmaW5lZCk7XG4gICAgICAgICAgICBjb25zdCByZXMgPSBuZXcgdHlwZXMuQVZhbDtcbiAgICAgICAgICAgIGNvbnN0cmFpbnRzLnB1c2goe1RZUEU6IHR5cGVzLlByaW1OdW1iZXIsXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICBJTkNMX1NFVDogcmVzfSk7XG4gICAgICAgICAgICByZXMuYWRkVHlwZSh0eXBlcy5QcmltTnVtYmVyKTtcbiAgICAgICAgICAgIC8vIFdlIGlnbm9yZSB0aGUgZWZmZWN0IG9mIHVwZGF0aW5nIHRvIG51bWJlciB0eXBlXG4gICAgICAgICAgICByZXR1cm4gcmVzO1xuICAgICAgICB9LFxuXG4gICAgICAgIEJpbmFyeUV4cHJlc3Npb246IGZ1bmN0aW9uIChub2RlLCBjdXJTdGF0dXMsIGMpIHtcbiAgICAgICAgICAgIGNvbnN0IGxPcHJkID0gYyhub2RlLmxlZnQsIGN1clN0YXR1cywgdW5kZWZpbmVkKTtcbiAgICAgICAgICAgIGNvbnN0IHJPcHJkID0gYyhub2RlLnJpZ2h0LCBjdXJTdGF0dXMsIHVuZGVmaW5lZCk7XG4gICAgICAgICAgICBjb25zdCByZXMgPSBuZXcgdHlwZXMuQVZhbDtcblxuICAgICAgICAgICAgaWYgKG5vZGUub3BlcmF0b3IgPT0gJysnKSB7XG4gICAgICAgICAgICAgICAgY29uc3RyYWludHMucHVzaCh7QUREX09QUkQxOiBsT3ByZCxcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBBRERfT1BSRDI6IHJPcHJkLFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIFJFU1VMVDogcmVzIH0pO1xuICAgICAgICAgICAgICAgIGxPcHJkLnByb3BhZ2F0ZShuZXcgY3N0ci5Jc0FkZGVkKHJPcHJkLCByZXMpKTtcbiAgICAgICAgICAgICAgICByT3ByZC5wcm9wYWdhdGUobmV3IGNzdHIuSXNBZGRlZChsT3ByZCwgcmVzKSk7XG4gICAgICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgICAgICAgIGlmIChiaW5vcElzQm9vbGVhbihub2RlLm9wZXJhdG9yKSkge1xuICAgICAgICAgICAgICAgICAgICBjb25zdHJhaW50cy5wdXNoKHtUWVBFOiB0eXBlcy5QcmltQm9vbGVhbixcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgSU5DTF9TRVQ6IHJlc30pO1xuICAgICAgICAgICAgICAgICAgICByZXMuYWRkVHlwZSh0eXBlcy5QcmltQm9vbGVhbik7XG4gICAgICAgICAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgY29uc3RyYWludHMucHVzaCh7VFlQRTogdHlwZXMuUHJpbU51bWJlcixcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgSU5DTF9TRVQ6IHJlc30pO1xuICAgICAgICAgICAgICAgICAgICByZXMuYWRkVHlwZSh0eXBlcy5QcmltTnVtYmVyKTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICByZXR1cm4gcmVzO1xuICAgICAgICB9LFxuXG4gICAgICAgIFRyeVN0YXRlbWVudDogZnVuY3Rpb24gKG5vZGUsIGN1clN0YXR1cywgYykge1xuICAgICAgICAgICAgLy8gY29uc3RydWN0IHNjb3BlIGNoYWluIGZvciBjYXRjaCBibG9ja1xuICAgICAgICAgICAgY29uc3QgY2F0Y2hCbG9ja1NDID1cbiAgICAgICAgICAgICAgICBub2RlLmhhbmRsZXIuYm9keVsnQGJsb2NrJ11cbiAgICAgICAgICAgICAgICAuZ2V0U2NvcGVJbnN0YW5jZShjdXJTdGF0dXMuc2MsIGN1clN0YXR1cy5kZWx0YSk7XG4gICAgICAgICAgICAvLyBnZXQgdGhlIEFWYWwgZm9yIGV4Y2VwdGlvbiBwYXJhbWV0ZXJcbiAgICAgICAgICAgIGNvbnN0IGV4Y0FWYWwgPSBjYXRjaEJsb2NrU0MuZ2V0QVZhbE9mKG5vZGUuaGFuZGxlci5wYXJhbS5uYW1lKTtcblxuICAgICAgICAgICAgLy8gZm9yIHRyeSBibG9ja1xuICAgICAgICAgICAgY29uc3QgdHJ5U3RhdHVzID0gY2hhbmdlZFN0YXR1cyhjdXJTdGF0dXMsICdleGMnLCBleGNBVmFsKTtcbiAgICAgICAgICAgIGMobm9kZS5ibG9jaywgdHJ5U3RhdHVzLCB1bmRlZmluZWQpO1xuXG4gICAgICAgICAgICAvLyBmb3IgY2F0Y2ggYmxvY2tcbiAgICAgICAgICAgIGNvbnN0IGNhdGNoU3RhdHVzID0gY2hhbmdlZFN0YXR1cyhjdXJTdGF0dXMsICdzYycsIGNhdGNoQmxvY2tTQyk7XG4gICAgICAgICAgICBjKG5vZGUuaGFuZGxlci5ib2R5LCBjYXRjaFN0YXR1cywgdW5kZWZpbmVkKTtcblxuICAgICAgICAgICAgLy8gZm9yIGZpbmFsbHkgYmxvY2tcbiAgICAgICAgICAgIGlmIChub2RlLmZpbmFsaXplciAhPT0gbnVsbClcbiAgICAgICAgICAgICAgICBjKG5vZGUuZmluYWxpemVyLCBjdXJTdGF0dXMsIHVuZGVmaW5lZCk7XG4gICAgICAgIH0sXG5cbiAgICAgICAgVGhyb3dTdGF0ZW1lbnQ6IGZ1bmN0aW9uIChub2RlLCBjdXJTdGF0dXMsIGMpIHtcbiAgICAgICAgICAgIGNvbnN0IHRociA9IGMobm9kZS5hcmd1bWVudCwgY3VyU3RhdHVzLCB1bmRlZmluZWQpO1xuICAgICAgICAgICAgY29uc3RyYWludHMucHVzaCh7RlJPTTogdGhyLFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgVE86IGN1clN0YXR1cy5leGN9KTtcbiAgICAgICAgICAgIHRoci5wcm9wYWdhdGUoY3VyU3RhdHVzLmV4Yyk7XG4gICAgICAgIH0sXG5cbiAgICAgICAgQ2FsbEV4cHJlc3Npb246IGZ1bmN0aW9uIChub2RlLCBjdXJTdGF0dXMsIGMpIHtcbiAgICAgICAgICAgIGNvbnN0IHJlc0FWYWwgPSBuZXcgdHlwZXMuQVZhbDtcbiAgICAgICAgICAgIGNvbnN0IGFyZ0FWYWxzID0gW107XG5cbiAgICAgICAgICAgIC8vIGdldCBBVmFscyBmb3IgZWFjaCBhcmd1bWVudHNcbiAgICAgICAgICAgIGZvciAobGV0IGkgPSAwOyBpIDwgbm9kZS5hcmd1bWVudHMubGVuZ3RoOyBpKyspIHtcbiAgICAgICAgICAgICAgICBhcmdBVmFscy5wdXNoKFxuICAgICAgICAgICAgICAgICAgICBjKG5vZGUuYXJndW1lbnRzW2ldLCBjdXJTdGF0dXMsIHVuZGVmaW5lZCkpO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgLy8gYXBwZW5kIGN1cnJlbnQgY2FsbCBzaXRlIHRvIHRoZSBjb250ZXh0XG4gICAgICAgICAgICBjb25zdCBuZXdEZWx0YSA9IGN1clN0YXR1cy5kZWx0YS5hcHBlbmRPbmUobm9kZVsnQGxhYmVsJ10pO1xuXG4gICAgICAgICAgICBpZiAobm9kZS5jYWxsZWUudHlwZSA9PT0gJ01lbWJlckV4cHJlc3Npb24nKSB7XG4gICAgICAgICAgICAgICAgLy8gbWV0aG9kIGNhbGxcbiAgICAgICAgICAgICAgICAvLyB2YXIgcmVjdiA9IGMobm9kZS5jYWxsZWUub2JqZWN0LCBjdXJTdGF0dXMsIHVuZGVmaW5lZCk7XG4gICAgICAgICAgICAgICAgLy8gdmFyIG1ldGhvZE5hbWUgPSBpbW1lZFByb3Aobm9kZS5jYWxsZWUpO1xuICAgICAgICAgICAgICAgIC8vIGNvbnN0cmFpbnRzLnB1c2goe1xuICAgICAgICAgICAgICAgIC8vICAgUkVDVjogcmVjdixcbiAgICAgICAgICAgICAgICAvLyAgIFBST1BOQU1FOiBtZXRob2ROYW1lLFxuICAgICAgICAgICAgICAgIC8vICAgUEFSQU1TOiBhcmdBVmFscyxcbiAgICAgICAgICAgICAgICAvLyAgIFJFVDogcmVzQVZhbCxcbiAgICAgICAgICAgICAgICAvLyAgIEVYQzogY3VyU3RhdHVzLmV4YyxcbiAgICAgICAgICAgICAgICAvLyAgIERFTFRBOiBuZXdEZWx0YVxuICAgICAgICAgICAgICAgIC8vIH0pO1xuICAgICAgICAgICAgICAgIGNvbnN0IHJlY3ZBbmRSZXQgPSByZWFkTWVtYmVyKG5vZGUuY2FsbGVlLCBjdXJTdGF0dXMsIGMpO1xuICAgICAgICAgICAgICAgIHJlY3ZBbmRSZXRbMV0ucHJvcGFnYXRlKFxuICAgICAgICAgICAgICAgICAgICBuZXcgY3N0ci5Jc0NhbGxlZShcbiAgICAgICAgICAgICAgICAgICAgICAgIHJlY3ZBbmRSZXRbMF0sXG4gICAgICAgICAgICAgICAgICAgICAgICBhcmdBVmFscyxcbiAgICAgICAgICAgICAgICAgICAgICAgIHJlc0FWYWwsXG4gICAgICAgICAgICAgICAgICAgICAgICBjdXJTdGF0dXMuZXhjLFxuICAgICAgICAgICAgICAgICAgICAgICAgbmV3RGVsdGEpKTtcbiAgICAgICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgICAgICAgLy8gbm9ybWFsIGZ1bmN0aW9uIGNhbGxcbiAgICAgICAgICAgICAgICBjb25zdCBjYWxsZWVBVmFsID0gYyhub2RlLmNhbGxlZSwgY3VyU3RhdHVzLCB1bmRlZmluZWQpO1xuICAgICAgICAgICAgICAgIC8vIGNhbGxlZeydmCByZXR1cm7snYQgY2FsbCBleHByZXNzaW9u7Jy866GcXG4gICAgICAgICAgICAgICAgLy8gY2FsbGVl7J2YIGV4Y2VwdGlvbuydhCDtmLjstpwg7Lih7J2YIGV4Y2VwdGlvbuyXkCDsoITri6ztlbTslbxcbiAgICAgICAgICAgICAgICBjb25zdHJhaW50cy5wdXNoKHtcbiAgICAgICAgICAgICAgICAgICAgQ0FMTEVFOiBjYWxsZWVBVmFsLFxuICAgICAgICAgICAgICAgICAgICBTRUxGOiBydENYLmdsb2JhbE9iamVjdCxcbiAgICAgICAgICAgICAgICAgICAgUEFSQU1TOiBhcmdBVmFscyxcbiAgICAgICAgICAgICAgICAgICAgUkVUOiByZXNBVmFsLFxuICAgICAgICAgICAgICAgICAgICBFWEM6IGN1clN0YXR1cy5leGMsXG4gICAgICAgICAgICAgICAgICAgIERFTFRBOiBuZXdEZWx0YVxuICAgICAgICAgICAgICAgIH0pO1xuICAgICAgICAgICAgICAgIGNhbGxlZUFWYWwucHJvcGFnYXRlKFxuICAgICAgICAgICAgICAgICAgICBuZXcgY3N0ci5Jc0NhbGxlZShcbiAgICAgICAgICAgICAgICAgICAgICAgIG5ldyB0eXBlcy5BVmFsKHJ0Q1guZ2xvYmFsT2JqZWN0KSxcbiAgICAgICAgICAgICAgICAgICAgICAgIGFyZ0FWYWxzLFxuICAgICAgICAgICAgICAgICAgICAgICAgcmVzQVZhbCxcbiAgICAgICAgICAgICAgICAgICAgICAgIGN1clN0YXR1cy5leGMsXG4gICAgICAgICAgICAgICAgICAgICAgICBuZXdEZWx0YSkpO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgcmV0dXJuIHJlc0FWYWw7XG4gICAgICAgIH0sXG5cbiAgICAgICAgTWVtYmVyRXhwcmVzc2lvbjogZnVuY3Rpb24gKG5vZGUsIGN1clN0YXR1cywgYykge1xuICAgICAgICAgICAgY29uc3QgcmVjdkFuZFJldCA9IHJlYWRNZW1iZXIobm9kZSwgY3VyU3RhdHVzLCBjKTtcbiAgICAgICAgICAgIHJldHVybiByZWN2QW5kUmV0WzFdO1xuICAgICAgICB9LFxuXG4gICAgICAgIFJldHVyblN0YXRlbWVudDogZnVuY3Rpb24gKG5vZGUsIGN1clN0YXR1cywgYykge1xuICAgICAgICAgICAgaWYgKCFub2RlLmFyZ3VtZW50KSByZXR1cm47XG4gICAgICAgICAgICBjb25zdCByZXQgPSBjKG5vZGUuYXJndW1lbnQsIGN1clN0YXR1cywgdW5kZWZpbmVkKTtcbiAgICAgICAgICAgIGNvbnN0cmFpbnRzLnB1c2goe0ZST006IHJldCxcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIFRPOiBjdXJTdGF0dXMucmV0fSk7XG4gICAgICAgICAgICByZXQucHJvcGFnYXRlKGN1clN0YXR1cy5yZXQpO1xuICAgICAgICB9XG4gICAgfSk7XG5cbiAgICByZWN1cnNpdmVXaXRoUmV0dXJuKGFzdCwgaW5pdFN0YXR1cywgY29uc3RyYWludEdlbmVyYXRvcik7XG5cbiAgICAvLyBXZSBhY3R1YWxseSBhZGRlZCBjb25zdHJhaW50c1xuICAgIHJldHVybiB0cnVlO1xufVxuXG5mdW5jdGlvbiByZWN1cnNpdmVXaXRoUmV0dXJuKG5vZGUsIHN0YXRlLCB2aXNpdG9yKSB7XG4gICAgZnVuY3Rpb24gYyhub2RlLCBzdCwgb3ZlcnJpZGUpIHtcbiAgICAgICAgcmV0dXJuIHZpc2l0b3Jbb3ZlcnJpZGUgfHwgbm9kZS50eXBlXShub2RlLCBzdCwgYyk7XG4gICAgfVxuICAgIHJldHVybiBjKG5vZGUsIHN0YXRlKTtcbn1cblxuZXhwb3J0cy5jb25zdHJhaW50cyA9IGNvbnN0cmFpbnRzO1xuZXhwb3J0cy5hZGRDb25zdHJhaW50cyA9IGFkZENvbnN0cmFpbnRzO1xuZXhwb3J0cy5jbGVhckNvbnN0cmFpbnRzID0gY2xlYXJDb25zdHJhaW50cztcbiIsIid1c2Ugc3RyaWN0JztcblxuY29uc3QgdHlwZXMgPSByZXF1aXJlKCcuLi9kb21haW5zL3R5cGVzJyk7XG5jb25zdCBzdGF0dXMgPSByZXF1aXJlKCcuLi9kb21haW5zL3N0YXR1cycpO1xuY29uc3QgY0dlbiA9IHJlcXVpcmUoJy4vY0dlbicpO1xuXG5mdW5jdGlvbiBDU1RSKCkge31cbkNTVFIucHJvdG90eXBlID0gT2JqZWN0LmNyZWF0ZShudWxsKTtcbkNTVFIucHJvdG90eXBlLmVxdWFscyA9IGZ1bmN0aW9uIChvdGhlcikge1xuICAgIHJldHVybiB0aGlzID09PSBvdGhlcjtcbn07XG5cbmZ1bmN0aW9uIFJlYWRQcm9wKHByb3AsIHRvKSB7XG4gICAgdGhpcy5wcm9wID0gcHJvcDtcbiAgICB0aGlzLnRvID0gdG87XG59XG5SZWFkUHJvcC5wcm90b3R5cGUgPSBPYmplY3QuY3JlYXRlKENTVFIucHJvdG90eXBlKTtcblJlYWRQcm9wLnByb3RvdHlwZS5hZGRUeXBlID0gZnVuY3Rpb24gKG9iaikge1xuICAgIGlmICghKG9iaiBpbnN0YW5jZW9mICh0eXBlcy5PYmpUeXBlKSkpIHJldHVybjtcbiAgICAvLyB3aGVuIG9iaiBpcyBPYmpUeXBlLFxuICAgIGNvbnN0IG93blByb3AgPSBvYmouZ2V0UHJvcCh0aGlzLnByb3AsIHRydWUpO1xuICAgIGlmIChvd25Qcm9wKSB7XG4gICAgICAgIC8vIHdoZW4gdGhlIG9iamVjdCBoYXMgdGhlIHByb3AsXG4gICAgICAgIG93blByb3AucHJvcGFnYXRlKHRoaXMudG8pO1xuICAgIH0gZWxzZSBpZiAob2JqLmdldFByb3AoJ19fcHJvdG9fXycsIHRydWUpKSB7XG4gICAgICAgIC8vIHVzZSBwcm90b3R5cGUgY2hhaW5cbiAgICAgICAgb2JqLmdldFByb3AoJ19fcHJvdG9fXycpXG4gICAgICAgICAgLnByb3BhZ2F0ZShuZXcgUmVhZFByb3AodGhpcy5wcm9wLCB0aGlzLnRvKSk7XG4gICAgfVxufTtcblJlYWRQcm9wLnByb3RvdHlwZS5lcXVhbHMgPSBmdW5jdGlvbiAob3RoZXIpIHtcbiAgICBpZiAoIShvdGhlciBpbnN0YW5jZW9mIFJlYWRQcm9wKSkgcmV0dXJuIGZhbHNlO1xuICAgIHJldHVybiB0aGlzLnByb3AgPT09IG90aGVyLnByb3BcbiAgICAgICAgJiYgdGhpcy50by5lcXVhbHMob3RoZXIudG8pO1xufTtcblxuZnVuY3Rpb24gV3JpdGVQcm9wKHByb3AsIGZyb20pIHtcbiAgICB0aGlzLnByb3AgPSBwcm9wO1xuICAgIHRoaXMuZnJvbSA9IGZyb207XG59XG5Xcml0ZVByb3AucHJvdG90eXBlID0gT2JqZWN0LmNyZWF0ZShDU1RSLnByb3RvdHlwZSk7XG5Xcml0ZVByb3AucHJvdG90eXBlLmFkZFR5cGUgPSBmdW5jdGlvbiAob2JqKSB7XG4gICAgaWYgKCEob2JqIGluc3RhbmNlb2YgKHR5cGVzLk9ialR5cGUpKSkgcmV0dXJuO1xuICAgIGNvbnN0IG93blByb3AgPSBvYmouZ2V0UHJvcCh0aGlzLnByb3ApO1xuICAgIHRoaXMuZnJvbS5wcm9wYWdhdGUob3duUHJvcCk7XG59O1xuXG5mdW5jdGlvbiBJc0FkZGVkKG90aGVyLCB0YXJnZXQpIHtcbiAgICB0aGlzLm90aGVyID0gb3RoZXI7XG4gICAgdGhpcy50YXJnZXQgPSB0YXJnZXQ7XG59XG5Jc0FkZGVkLnByb3RvdHlwZSA9IE9iamVjdC5jcmVhdGUoQ1NUUi5wcm90b3R5cGUpO1xuSXNBZGRlZC5wcm90b3R5cGUuYWRkVHlwZSA9IGZ1bmN0aW9uICh0eXBlKSB7XG4gICAgaWYgKCh0eXBlID09PSB0eXBlcy5QcmltTnVtYmVyIFxuICAgICAgICAgfHwgdHlwZSA9PT0gdHlwZXMuUHJpbUJvb2xlYW4pXG4gICAgICYmICh0aGlzLm90aGVyLmhhc1R5cGUodHlwZXMuUHJpbU51bWJlcikgXG4gICAgICAgICB8fCB0aGlzLm90aGVyLmhhc1R5cGUodHlwZXMuUHJpbUJvb2xlYW4pKSkge1xuICAgICAgICB0aGlzLnRhcmdldC5hZGRUeXBlKHR5cGVzLlByaW1OdW1iZXIpO1xuICAgIH1cbiAgICBpZiAodHlwZSA9PT0gdHlwZXMuUHJpbVN0cmluZ1xuICAgICAmJiAhdGhpcy5vdGhlci5pc0VtcHR5KCkpIHtcbiAgICAgICAgIHRoaXMudGFyZ2V0LmFkZFR5cGUodHlwZXMuUHJpbVN0cmluZyk7XG4gICAgfVxufTtcblxuZnVuY3Rpb24gSXNDYWxsZWUoc2VsZiwgYXJncywgcmV0LCBleGMsIGRlbHRhKSB7XG4gICAgdGhpcy5zZWxmID0gc2VsZjtcbiAgICB0aGlzLmFyZ3MgPSBhcmdzO1xuICAgIHRoaXMucmV0ID0gcmV0O1xuICAgIHRoaXMuZXhjID0gZXhjO1xuICAgIHRoaXMuZGVsdGEgPSBkZWx0YTtcbn1cbklzQ2FsbGVlLnByb3RvdHlwZSA9IE9iamVjdC5jcmVhdGUoQ1NUUi5wcm90b3R5cGUpO1xuSXNDYWxsZWUucHJvdG90eXBlLmFkZFR5cGUgPSBmdW5jdGlvbiAoZikge1xuICAgIGlmICghKGYgaW5zdGFuY2VvZiAodHlwZXMuRm5UeXBlKSkpIHJldHVybjtcbiAgICBjb25zdCBmdW5FbnYgPSBmLmdldEZ1bkVudih0aGlzLmRlbHRhKTtcbiAgICBjb25zdCBuZXdTQyA9IGYub3JpZ2luTm9kZS5ib2R5WydAYmxvY2snXS5nZXRTY29wZUluc3RhbmNlKGYuc2MsIHRoaXMuZGVsdGEpO1xuICAgIGNvbnN0IGZ1blN0YXR1c1xuICAgICAgICA9IG5ldyBzdGF0dXMuU3RhdHVzKGZ1bkVudlswXSwgZnVuRW52WzFdLCBmdW5FbnZbMl0sIFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIHRoaXMuZGVsdGEsIG5ld1NDKTtcbiAgICAvLyBwYXNzIHRoaXMgb2JqZWN0XG4gICAgdGhpcy5zZWxmLnByb3BhZ2F0ZShmdW5FbnZbMF0pO1xuXG4gICAgY29uc3QgbWluTGVuID0gTWF0aC5taW4odGhpcy5hcmdzLmxlbmd0aCwgZi5wYXJhbU5hbWVzLmxlbmd0aCk7XG4gICAgZm9yIChsZXQgaSA9IDA7IGkgPCBtaW5MZW47IGkrKykge1xuICAgICAgICB0aGlzLmFyZ3NbaV0ucHJvcGFnYXRlKG5ld1NDLmdldEFWYWxPZihmLnBhcmFtTmFtZXNbaV0pKTtcbiAgICB9XG5cbiAgICAvLyBmb3IgYXJndW1lbnRzIG9iamVjdFxuICAgIGlmIChmLm9yaWdpbk5vZGUuYm9keVsnQGJsb2NrJ10udXNlQXJndW1lbnRzT2JqZWN0KSB7XG4gICAgICAgIGNvbnN0IGFyZ09iaiA9IGYuZ2V0QXJndW1lbnRzT2JqZWN0KHRoaXMuZGVsdGEpO1xuICAgICAgICBuZXdTQy5nZXRBVmFsT2YoJ2FyZ3VtZW50cycpLmFkZFR5cGUoYXJnT2JqKTtcbiAgICAgICAgZm9yIChsZXQgaSA9IDA7IGkgPCB0aGlzLmFyZ3MubGVuZ3RoOyBpKyspIHtcbiAgICAgICAgICAgIHRoaXMuYXJnc1tpXS5wcm9wYWdhdGUoYXJnT2JqLmdldFByb3AoaSArICcnKSk7XG4gICAgICAgICAgICB0aGlzLmFyZ3NbaV0ucHJvcGFnYXRlKGFyZ09iai5nZXRQcm9wKG51bGwpKTtcbiAgICAgICAgfVxuICAgICAgICBhcmdPYmouZ2V0UHJvcCgnY2FsbGVlJykuYWRkVHlwZShmKTtcbiAgICAgICAgYXJnT2JqLmdldFByb3AoJ2xlbmd0aCcpLmFkZFR5cGUodHlwZXMuUHJpbU51bWJlcik7XG4gICAgfVxuXG4gICAgLy8gY29uc3RyYWludCBnZW5lcmF0aW9uIGZvciB0aGUgZnVuY3Rpb24gYm9keVxuICAgIGNHZW4uYWRkQ29uc3RyYWludHMoZi5vcmlnaW5Ob2RlLmJvZHksIGZ1blN0YXR1cyk7XG5cbiAgICAvLyBnZXQgcmV0dXJuIFxuICAgIGZ1bkVudlsxXS5wcm9wYWdhdGUodGhpcy5yZXQpO1xuICAgIC8vIGdldCBleGNlcHRpb25cbiAgICBmdW5FbnZbMl0ucHJvcGFnYXRlKHRoaXMuZXhjKTtcbn07XG5cbmZ1bmN0aW9uIElzQ3RvcihhcmdzLCByZXQsIGV4YywgZGVsdGEpIHtcbiAgICB0aGlzLmFyZ3MgPSBhcmdzO1xuICAgIHRoaXMucmV0ID0gcmV0O1xuICAgIHRoaXMuZXhjID0gZXhjO1xuICAgIHRoaXMuZGVsdGEgPSBkZWx0YTtcbn1cbklzQ3Rvci5wcm90b3R5cGUgPSBPYmplY3QuY3JlYXRlKENTVFIucHJvdG90eXBlKTtcbklzQ3Rvci5wcm90b3R5cGUuYWRkVHlwZSA9IGZ1bmN0aW9uIChmKSB7XG4gICAgaWYgKCEoZiBpbnN0YW5jZW9mICh0eXBlcy5GblR5cGUpKSkgcmV0dXJuO1xuICAgIGNvbnN0IGZ1bkVudiA9IGYuZ2V0RnVuRW52KHRoaXMuZGVsdGEpO1xuICAgIGNvbnN0IG5ld1NDID0gZi5vcmlnaW5Ob2RlLmJvZHlbJ0BibG9jayddLmdldFNjb3BlSW5zdGFuY2UoZi5zYywgdGhpcy5kZWx0YSk7XG4gICAgY29uc3QgZnVuU3RhdHVzXG4gICAgICAgID0gbmV3IHN0YXR1cy5TdGF0dXMoZnVuRW52WzBdLCBuZXcgSWZPYmpUeXBlKGZ1bkVudlsxXSksIGZ1bkVudlsyXSxcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICB0aGlzLmRlbHRhLCBuZXdTQyk7XG4gICAgLy8gcGFzcyB0aGlzIG9iamVjdFxuICAgIGNvbnN0IG5ld09iaiA9IGYuZ2V0SW5zdGFuY2UoKTtcbiAgICBmdW5FbnZbMF0uYWRkVHlwZShuZXdPYmopO1xuXG4gICAgY29uc3QgbWluTGVuID0gTWF0aC5taW4odGhpcy5hcmdzLmxlbmd0aCwgZi5wYXJhbU5hbWVzLmxlbmd0aCk7XG4gICAgZm9yIChsZXQgaSA9IDA7IGkgPCBtaW5MZW47IGkrKykge1xuICAgICAgICB0aGlzLmFyZ3NbaV0ucHJvcGFnYXRlKG5ld1NDLmdldEFWYWxPZihmLnBhcmFtTmFtZXNbaV0pKTtcbiAgICB9XG5cbiAgICAvLyBmb3IgYXJndW1lbnRzIG9iamVjdFxuICAgIGlmIChmLm9yaWdpbk5vZGUuYm9keVsnQGJsb2NrJ10udXNlQXJndW1lbnRzT2JqZWN0KSB7XG4gICAgICAgIGNvbnN0IGFyZ09iaiA9IGYuZ2V0QXJndW1lbnRzT2JqZWN0KHRoaXMuZGVsdGEpO1xuICAgICAgICBuZXdTQy5nZXRBVmFsT2YoJ2FyZ3VtZW50cycpLmFkZFR5cGUoYXJnT2JqKTtcbiAgICAgICAgZm9yIChsZXQgaSA9IDA7IGkgPCB0aGlzLmFyZ3MubGVuZ3RoOyBpKyspIHtcbiAgICAgICAgICAgIHRoaXMuYXJnc1tpXS5wcm9wYWdhdGUoYXJnT2JqLmdldFByb3AoaSArICcnKSk7XG4gICAgICAgICAgICB0aGlzLmFyZ3NbaV0ucHJvcGFnYXRlKGFyZ09iai5nZXRQcm9wKG51bGwpKTtcbiAgICAgICAgfVxuICAgICAgICBhcmdPYmouZ2V0UHJvcCgnY2FsbGVlJykuYWRkVHlwZShmKTtcbiAgICAgICAgYXJnT2JqLmdldFByb3AoJ2xlbmd0aCcpLmFkZFR5cGUodHlwZXMuUHJpbU51bWJlcik7XG4gICAgfVxuXG4gICAgLy8gY29uc3RyYWludCBnZW5lcmF0aW9uIGZvciB0aGUgZnVuY3Rpb24gYm9keVxuICAgIGNHZW4uYWRkQ29uc3RyYWludHMoZi5vcmlnaW5Ob2RlLmJvZHksIGZ1blN0YXR1cyk7XG5cbiAgICAvLyBieSBleHBsaWNpdCByZXR1cm4sIG9ubHkgT2JqVHlwZSBhcmUgcHJvcGFnYXRlZFxuICAgIGZ1bkVudlsxXS5wcm9wYWdhdGUodGhpcy5yZXQpO1xuICAgIC8vIHJldHVybiBuZXcgb2JqZWN0XG4gICAgdGhpcy5yZXQuYWRkVHlwZShuZXdPYmopO1xuICAgIC8vIGdldCBleGNlcHRpb25cbiAgICBmdW5FbnZbMl0ucHJvcGFnYXRlKHRoaXMuZXhjKTtcbn07XG5cbi8vIGlnbm9yZSBub24gb2JqZWN0IHR5cGVzXG5mdW5jdGlvbiBJZk9ialR5cGUoYXZhbCkge1xuICAgIHRoaXMuYXZhbCA9IGF2YWw7XG59XG5JZk9ialR5cGUucHJvdG90eXBlID0gT2JqZWN0LmNyZWF0ZShDU1RSLnByb3RvdHlwZSk7XG5JZk9ialR5cGUucHJvdG90eXBlLmFkZFR5cGUgPSBmdW5jdGlvbiAodHlwZSkge1xuICAgIGlmICghKHR5cGUgaW5zdGFuY2VvZiB0eXBlcy5PYmpUeXBlKSkgcmV0dXJuO1xuICAgIHRoaXMuYXZhbC5hZGRUeXBlKHR5cGUpO1xufTtcblxuZXhwb3J0cy5SZWFkUHJvcCA9IFJlYWRQcm9wO1xuZXhwb3J0cy5Xcml0ZVByb3AgPSBXcml0ZVByb3A7XG5leHBvcnRzLklzQWRkZWQgPSBJc0FkZGVkO1xuZXhwb3J0cy5Jc0NhbGxlZSA9IElzQ2FsbGVlO1xuZXhwb3J0cy5Jc0N0b3IgPSBJc0N0b3I7XG4iLCIvLyBDb250ZXh0IGZvciBrLUNGQSBhbmFseXNpc1xuLy9cbi8vIEFzc3VtZSBhIGNvbnRleHQgaXMgYW4gYXJyYXkgb2YgbnVtYmVycy5cbi8vIEEgbnVtYmVyIGluIHN1Y2ggbGlzdCBkZW5vdGVzIGEgY2FsbCBzaXRlLCB0aGF0IGlzIEBsYWJlbCBvZiBhIENhbGxFeHByZXNzaW9uLlxuLy8gV2Uga2VlcCB0aGUgbW9zdCByZWNlbnQgJ2snIGNhbGxzaXRlcy5cbi8vIEVxdWFsaXR5IG9uIGNvbnRleHRzIHNob3VsZCBsb29rIGludG8gdGhlIG51bWJlcnMuXG5cbnZhciBjYWxsU2l0ZUNvbnRleHRQYXJhbWV0ZXIgPSB7XG4gICAgLy8gbWF4aW11bSBsZW5ndGggb2YgY29udGV4dFxuICAgIG1heERlcHRoSzogMCxcbiAgICAvLyBmdW5jdGlvbiBsaXN0IGZvciBzZW5zaXRpdmUgYW5hbHlzaXNcbiAgICBzZW5zRnVuY3M6IHt9XG59O1xuXG5mdW5jdGlvbiBDYWxsU2l0ZUNvbnRleHQoY3NMaXN0KSB7XG4gICAgaWYgKGNzTGlzdCkgdGhpcy5jc0xpc3QgPSBjc0xpc3Q7XG4gICAgZWxzZSB0aGlzLmNzTGlzdCA9IFtdO1xufVxuXG5DYWxsU2l0ZUNvbnRleHQucHJvdG90eXBlLmVxdWFscyA9IGZ1bmN0aW9uIChvdGhlcikge1xuICAgIGlmICh0aGlzLmNzTGlzdC5sZW5ndGggIT0gb3RoZXIuY3NMaXN0Lmxlbmd0aCkgcmV0dXJuIGZhbHNlO1xuICAgIGZvciAodmFyIGkgPSAwOyBpIDwgdGhpcy5jc0xpc3QubGVuZ3RoOyBpKyspIHtcbiAgICAgICAgaWYgKHRoaXMuY3NMaXN0W2ldICE9PSBvdGhlci5jc0xpc3RbaV0pIHJldHVybiBmYWxzZTtcbiAgICB9XG4gICAgcmV0dXJuIHRydWU7XG59O1xuXG5DYWxsU2l0ZUNvbnRleHQucHJvdG90eXBlLmFwcGVuZE9uZSA9IGZ1bmN0aW9uIChjYWxsU2l0ZSkge1xuICAgIC8vIHVzZSBjb25jYXQgdG8gY3JlYXRlIGEgbmV3IGFycmF5XG4gICAgLy8gb2xkZXN0IG9uZSBjb21lcyBmaXJzdFxuICAgIHZhciBhcHBlbmRlZCA9IHRoaXMuY3NMaXN0LmNvbmNhdChjYWxsU2l0ZSk7XG4gICAgaWYgKGFwcGVuZGVkLmxlbmd0aCA+IGNhbGxTaXRlQ29udGV4dFBhcmFtZXRlci5tYXhEZXB0aEspIHtcbiAgICAgICAgYXBwZW5kZWQuc2hpZnQoKTtcbiAgICB9XG4gICAgcmV0dXJuIG5ldyBDYWxsU2l0ZUNvbnRleHQoYXBwZW5kZWQpO1xufTtcblxuQ2FsbFNpdGVDb250ZXh0LnByb3RvdHlwZS50b1N0cmluZyA9IGZ1bmN0aW9uICgpIHtcbiAgICByZXR1cm4gdGhpcy5jc0xpc3QudG9TdHJpbmcoKTtcbn07XG5cbmV4cG9ydHMuY2FsbFNpdGVDb250ZXh0UGFyYW1ldGVyID0gY2FsbFNpdGVDb250ZXh0UGFyYW1ldGVyO1xuZXhwb3J0cy5DYWxsU2l0ZUNvbnRleHQgPSBDYWxsU2l0ZUNvbnRleHQ7IiwiLy8gU3RhdHVzOlxuLy8geyBzZWxmICA6IEFWYWwsXG4vLyAgIHJldCAgIDogQVZhbCxcbi8vICAgZXhjICAgOiBBVmFsLFxuLy8gICBkZWx0YSA6IENvbnRleHQsXG4vLyAgIHNjICAgIDogU2NvcGVDaGFpbiB9XG5cbmZ1bmN0aW9uIFN0YXR1cyhzZWxmLCByZXQsIGV4YywgZGVsdGEsIHNjKSB7XG4gICAgdGhpcy5zZWxmID0gc2VsZjtcbiAgICB0aGlzLnJldCA9IHJldDtcbiAgICB0aGlzLmV4YyA9IGV4YztcbiAgICB0aGlzLmRlbHRhID0gZGVsdGE7XG4gICAgdGhpcy5zYyA9IHNjO1xufVxuXG5TdGF0dXMucHJvdG90eXBlLmVxdWFscyA9IGZ1bmN0aW9uIChvdGhlcikge1xuICAgIHJldHVybiB0aGlzLnNlbGYgPT09IG90aGVyLnNlbGYgJiZcbiAgICAgICAgdGhpcy5yZXQgPT09IG90aGVyLnJldCAmJlxuICAgICAgICB0aGlzLmV4YyA9PT0gb3RoZXIuZXhjICYmXG4gICAgICAgIHRoaXMuZGVsdGEuZXF1YWxzKG90aGVyLmRlbHRhKSAmJlxuICAgICAgICB0aGlzLnNjID09PSBvdGhlci5zYztcbn07XG5cbmV4cG9ydHMuU3RhdHVzID0gU3RhdHVzOyIsIid1c2Ugc3RyaWN0JztcblxuLy8gZm9yIERFQlVHXG52YXIgY291bnQgPSAwO1xuLyoqXG4gKiB0aGUgYWJzdHJhY3QgdmFsdWUgZm9yIGEgY29uY3JldGUgdmFsdWVcbiAqIHdoaWNoIGlzIGEgc2V0IG9mIHR5cGVzLlxuICogQGNvbnN0cnVjdG9yXG4gKiBAcGFyYW0ge1R5cGV9IHR5cGUgLSBnaXZlIGEgdHlwZSB0byBtYWtlIEFWYWwgd2l0aCBhIHNpbmdsZSB0eXBlXG4gKi9cbmZ1bmN0aW9uIEFWYWwodHlwZSkge1xuICAgIC8vIHR5cGU6IGNvbnRhaW5lZCB0eXBlc1xuICAgIC8vIFdlIGFzc3VtZSB0eXBlcyBhcmUgZGlzdGluZ3Vpc2hhYmxlIGJ5ICc9PT0nXG4gICAgaWYgKHR5cGUpIHRoaXMudHlwZXMgPSBuZXcgU2V0KFt0eXBlXSk7XG4gICAgZWxzZSB0aGlzLnR5cGVzID0gbmV3IFNldCgpO1xuICAgIC8vIGZvcndhcmRzOiBwcm9wYWdhdGlvbiB0YXJnZXRzXG4gICAgLy8gV2UgYXNzdW1lIHRhcmdldHMgYXJlIGRpc3Rpbmd1aXNoYWJsZSBieSAnZXF1YWxzJyBtZXRob2RcbiAgICB0aGlzLmZvcndhcmRzID0gbmV3IFNldCgpO1xuICAgIC8vIGZvciBERUJVR1xuICAgIHRoaXMuX2lkID0gY291bnQrKztcbn1cbi8qKiBDaGVjayB3aGV0aGVyIGl0IGhhcyBhbnkgdHlwZVxuICogQHJldHVybnMge2Jvb2xlYW59XG4gKi9cbkFWYWwucHJvdG90eXBlLmlzRW1wdHkgPSBmdW5jdGlvbiAoKSB7XG4gICAgcmV0dXJuIHRoaXMudHlwZXMuc2l6ZSA9PT0gMDtcbn07XG5cbi8qKlxuICogQHJldHVybnMge1tUeXBlXX1cbiAqL1xuQVZhbC5wcm90b3R5cGUuZ2V0VHlwZXMgPSBmdW5jdGlvbiAoKSB7XG4gICAgcmV0dXJuIHRoaXMudHlwZXM7XG59O1xuXG4vKipcbiAqIEByZXR1cm5zIHtib29sZWFufVxuICovXG5BVmFsLnByb3RvdHlwZS5oYXNUeXBlID0gZnVuY3Rpb24gKHR5cGUpIHtcbiAgICByZXR1cm4gdGhpcy50eXBlcy5oYXModHlwZSk7XG59O1xuXG4vKipcbiAqIEFkZCBhIHR5cGUuXG4gKiBAcGFyYW0ge1R5cGV9IHR5cGVcbiAqL1xuQVZhbC5wcm90b3R5cGUuYWRkVHlwZSA9IGZ1bmN0aW9uICh0eXBlKSB7XG4gICAgaWYgKHRoaXMudHlwZXMuaGFzKHR5cGUpKSByZXR1cm47XG4gICAgLy8gZ2l2ZW4gdHlwZSBpcyBuZXdcbiAgICB0aGlzLnR5cGVzLmFkZCh0eXBlKTtcbiAgICAvLyBzZW5kIHRvIHByb3BhZ2F0aW9uIHRhcmdhdHNcbiAgICB0aGlzLmZvcndhcmRzLmZvckVhY2goZnVuY3Rpb24gKGZ3ZCkge1xuICAgICAgICBmd2QuYWRkVHlwZSh0eXBlKTtcbiAgICB9KTtcbn07XG4vKipcbiAqIEBwYXJhbSB7QVZhbH0gdGFyZ2V0XG4gKi9cbkFWYWwucHJvdG90eXBlLnByb3BhZ2F0ZSA9IGZ1bmN0aW9uICh0YXJnZXQpIHtcbiAgICBpZiAoIXRoaXMuYWRkRm9yd2FyZCh0YXJnZXQpKSByZXR1cm47XG4gICAgLy8gdGFyZ2V0IGlzIG5ld2x5IGFkZGVkXG4gICAgLy8gc2VuZCB0eXBlcyB0byB0aGUgbmV3IHRhcmdldFxuICAgIHRoaXMudHlwZXMuZm9yRWFjaChmdW5jdGlvbiAodHlwZSkge1xuICAgICAgICB0YXJnZXQuYWRkVHlwZSh0eXBlKTtcbiAgICB9KTtcbn07XG5cbkFWYWwucHJvdG90eXBlLmFkZEZvcndhcmQgPSBmdW5jdGlvbiAoZndkKSB7XG4gICAgZm9yIChsZXQgb2xkRndkIG9mIHRoaXMuZm9yd2FyZHMpIHtcbiAgICAgICAgaWYgKGZ3ZC5lcXVhbHMob2xkRndkKSkgcmV0dXJuIGZhbHNlO1xuICAgIH1cbiAgICB0aGlzLmZvcndhcmRzLmFkZChmd2QpO1xuICAgIHJldHVybiB0cnVlO1xufTtcblxuQVZhbC5wcm90b3R5cGUuZXF1YWxzID0gZnVuY3Rpb24gKG90aGVyKSB7XG4gICAgLy8gc2ltcGxlIHJlZmVyZW5jZSBjb21wYXJpc29uXG4gICAgcmV0dXJuIHRoaXMgPT09IG90aGVyO1xufTtcblxuLyoqXG4gKiBUT0RPOiBjaGVjayB3aGV0aGVyIHdlIHJlYWxseSBuZWVkIHRoaXMgbWV0aG9kLlxuICogQHBhcmFtIHtzdHJpbmd9IHByb3BcbiAqIEByZXR1cm5zIHtBVmFsfVxuICovXG5BVmFsLnByb3RvdHlwZS5nZXRQcm9wID0gZnVuY3Rpb24gKHByb3ApIHtcbiAgICBpZiAocHJvcCA9PT0gJ+KclicpIHtcbiAgICAgICAgLy8g4pyWIGlzIHRoZSBib2d1cyBwcm9wZXJ0eSBuYW1lIGFkZGVkIGZvciBlcnJvciByZWNvdmVyeS5cbiAgICAgICAgcmV0dXJuIEFWYWxOdWxsO1xuICAgIH1cbiAgICBpZiAodGhpcy5wcm9wcy5oYXMocHJvcCkpIHtcbiAgICAgICAgcmV0dXJuIHRoaXMucHJvcHMuZ2V0KHByb3ApO1xuICAgIH0gZWxzZSB7XG4gICAgICAgIHJldHVybiBBVmFsTnVsbDtcbiAgICB9XG59O1xuXG4vKipcbiAqIHRoZSBzdXBlciBjbGFzcyBvZiBhbGwgdHlwZXNcbiAqIGVhY2ggdHlwZSBzaG91bGQgYmUgZGlzdGluZ3Vpc2hhYmxlIGJ5ICc9PT0nIG9wZXJhdGlvbi5cbiAqIEBjb25zdHJ1Y3RvclxuICovXG5mdW5jdGlvbiBUeXBlKCkge31cblR5cGUucHJvdG90eXBlID0gT2JqZWN0LmNyZWF0ZShudWxsKTtcblxuLyoqXG4gKiAxLiBvYmplY3QgdHlwZXNcbiAqIEBwYXJhbSB7QVZhbH0gcHJvdG8gLSBBVmFsIG9mIGNvbnN0cnVjdG9yJ3MgcHJvdG90eXBlXG4gKiBAcGFyYW0ge3N0cmluZ30gbmFtZSAtIGd1ZXNzZWQgbmFtZVxuICovXG5mdW5jdGlvbiBPYmpUeXBlKHByb3RvLCBuYW1lKSB7XG4gICAgdGhpcy5uYW1lID0gbmFtZTtcbiAgICB0aGlzLnByb3BzID0gbmV3IE1hcCgpO1xuXG4gICAgLy8gc2hhcmUgcHJvdG8gd2l0aCBfX3Byb3RvX19cbiAgICB0aGlzLnNldFByb3AoJ19fcHJvdG9fXycsIHByb3RvKTtcbn1cbk9ialR5cGUucHJvdG90eXBlID0gT2JqZWN0LmNyZWF0ZShUeXBlLnByb3RvdHlwZSk7XG4vKipcbiAqIEBwYXJhbSB7c3RyaW5nfG51bGx9IHByb3AgLSBudWxsIGZvciBjb21wdXRlZCBwcm9wc1xuICogQHBhcmFtIHtib29sZWFufSByZWFkT25seSAtIGlmIGZhbHNlLCBjcmVhdGUgQVZhbCBmb3IgcHJvcCBpZiBuZWNlc3NhcnlcbiAqIEByZXR1cm5zIHtBVmFsfSBBVmFsIG9mIHRoZSBwcm9wZXJ0eVxuICovXG5PYmpUeXBlLnByb3RvdHlwZS5nZXRQcm9wID0gZnVuY3Rpb24gKHByb3AsIHJlYWRPbmx5KSB7XG4gICAgaWYgKHByb3AgPT09ICfinJYnKSB7XG4gICAgICAgIC8vIOKcliBpcyB0aGUgYm9ndXMgcHJvcGVydHkgbmFtZSBhZGRlZCBkdXJpbmcgcGFyc2luZyBlcnJvciByZWNvdmVyeS5cbiAgICAgICAgcmV0dXJuIEFWYWxOdWxsO1xuICAgIH1cbiAgICBpZiAodGhpcy5wcm9wcy5oYXMocHJvcCkpIHtcbiAgICAgICAgcmV0dXJuIHRoaXMucHJvcHMuZ2V0KHByb3ApO1xuICAgIH0gZWxzZSBpZiAocmVhZE9ubHkpIHtcbiAgICAgICAgcmV0dXJuIG51bGw7XG4gICAgfSBlbHNlIHtcbiAgICAgICAgdmFyIG5ld1Byb3BBVmFsID0gbmV3IEFWYWw7XG4gICAgICAgIHRoaXMucHJvcHMuc2V0KHByb3AsIG5ld1Byb3BBVmFsKTtcbiAgICAgICAgcmV0dXJuIG5ld1Byb3BBVmFsO1xuICAgIH1cbn07XG4vKipcbiAqIFdlIHVzZSB0aGlzIGZ1bmN0aW9uIHRvIHNoYXJlIC5wcm90b3R5cGUgd2l0aCBpbnN0YW5jZXMgX19wcm90b19fXG4gKiBJdCBpcyBwb3NzaWJsZSB0byB1c2UgdGhpcyBmdW5jdGlvbiB0byBtZXJnZSBBVmFscyB0byBvcHRpbWl6ZSB0aGUgYW5hbHl6ZXIuXG4gKiBAcGFyYW0ge3N0cmluZ3xudWxsfSBwcm9wIC0gbnVsbCBmb3IgY29tcHV0ZWQgcHJvcHNcbiAqIEBwYXJhbSB7QVZhbH0gYXZhbFxuICovXG5PYmpUeXBlLnByb3RvdHlwZS5zZXRQcm9wID0gZnVuY3Rpb24gKHByb3AsIGF2YWwpIHtcbiAgICBpZiAocHJvcCA9PT0gJ+KclicpIHtcbiAgICAgICAgLy8g4pyWIGlzIHRoZSBib2d1cyBwcm9wZXJ0eSBuYW1lIGFkZGVkIGR1cmluZyBwYXJzaW5nIGVycm9yIHJlY292ZXJ5LlxuICAgICAgICByZXR1cm47XG4gICAgfVxuICAgIHRoaXMucHJvcHMuc2V0KHByb3AsIGF2YWwpO1xufTtcbi8qKlxuICogVE9ETzogQ2hlY2sgdGhpcyBmdW5jdGlvbidzIG5lY2Vzc2l0eVxuICogQHBhcmFtIHtzdHJpbmd9IHByb3BcbiAqIEByZXR1cm5zIHtib29sZWFufVxuICovXG5PYmpUeXBlLnByb3RvdHlwZS5oYXNQcm9wID0gZnVuY3Rpb24gKHByb3ApIHtcbiAgICBpZiAocHJvcCA9PT0gJ+KclicpIHJldHVybiBmYWxzZTtcbiAgICByZXR1cm4gdGhpcy5wcm9wcy5oYXMocHJvcCk7XG59O1xuLyoqXG4gKiBUT0RPOiBDaGVjayB0aGlzIGZ1bmN0aW9uJ3MgbmVjZXNzaXR5XG4gKiBAcGFyYW0ge1R5cGV9IHR5cGVcbiAqIEBwYXJhbSB7c3RyaW5nfSBwcm9wXG4gKi9cbk9ialR5cGUucHJvdG90eXBlLmFkZFR5cGVUb1Byb3AgPSBmdW5jdGlvbiAodHlwZSwgcHJvcCkge1xuICAgIGlmIChwcm9wID09PSAn4pyWJykgcmV0dXJuO1xuICAgIGlmICghdGhpcy5wcm9wcy5oYXMocHJvcCkpIHtcbiAgICAgICAgdGhpcy5wcm9wcy5zZXQocHJvcCwgbmV3IEFWYWwpO1xuICAgIH1cbiAgICBpZiAodGhpcy5wcm9wcy5nZXQocHJvcCkuaGFzVHlwZSh0eXBlKSkgcmV0dXJuO1xuICAgIHRoaXMucHJvcHMuZ2V0KHByb3ApLmFkZFR5cGUodHlwZSk7XG59O1xuLyoqXG4gKiBUT0RPOiBDaGVjayB0aGlzIGZ1bmN0aW9uJ3MgbmVjZXNzaXR5XG4gKiBAcGFyYW0ge0FWYWx9IGF2YWxcbiAqIEBwYXJhbSB7c3RyaW5nfSBwcm9wXG4gKi9cbk9ialR5cGUucHJvdG90eXBlLmpvaW5BVmFsVG9Qcm9wID0gZnVuY3Rpb24gKGF2YWwsIHByb3ApIHtcbiAgICB2YXIgc2VsZiA9IHRoaXM7XG4gICAgYXZhbC5nZXRUeXBlcygpLmZvckVhY2goZnVuY3Rpb24gKHR5cGUpIHtcbiAgICAgICAgc2VsZi5hZGRUeXBlVG9Qcm9wKHR5cGUsIHByb3ApO1xuICAgIH0pO1xufTtcblxuLy8gbWFrZSBhbiBPYmogZnJvbSB0aGUgZ2xvYmFsIHNjb3BlXG5mdW5jdGlvbiBta09iakZyb21HbG9iYWxTY29wZShnU2NvcGUpIHtcbiAgICB2YXIgZ09iaiA9IG5ldyBPYmpUeXBlKEFWYWxOdWxsLCAnKmdsb2JhbCBzY29wZSonKTtcbiAgICBnT2JqLnByb3BzID0gZ1Njb3BlLnZhck1hcDtcbiAgICAvLyBPdmVycmlkZSBnZXRQcm9wIG1ldGhvZCBmb3IgZ2xvYmFsIG9iamVjdFxuICAgIC8vIFdlIGlnbm9yZSAncmVhZE9ubHknIHBhcmFtZXRlciB0byBhbHdheXMgcmV0dXJuIGl0cyBvd24gcHJvcCBBVmFsIFxuICAgIGdPYmouZ2V0UHJvcCA9IGZ1bmN0aW9uIChwcm9wKSB7XG4gICAgICAgIHJldHVybiBPYmpUeXBlLnByb3RvdHlwZS5nZXRQcm9wLmNhbGwodGhpcywgcHJvcCk7XG4gICAgfTtcbiAgICByZXR1cm4gZ09iajtcbn1cblxuLyoqXG4gKiAyLiBwcmltaXRpdmUgdHlwZXNcbiAqIEBjb25zdHJ1Y3RvclxuICogQHBhcmFtIHtzdHJpbmd9IG5hbWVcbiAqL1xuZnVuY3Rpb24gUHJpbVR5cGUobmFtZSkge1xuICAgIHRoaXMubmFtZSA9IG5hbWU7XG59XG5QcmltVHlwZS5wcm90b3R5cGUgPSBPYmplY3QuY3JlYXRlKFR5cGUucHJvdG90eXBlKTtcblxuLyoqXG4gKiAzLiBmdW5jdGlvbiB0eXBlc1xuICogdGhlIG5hbWUgaXMgdXNlZCBmb3IgdGhlIHR5cGUgb2YgdGhlIGluc3RhbmNlcyBmcm9tIHRoZSBmdW5jdGlvblxuICogQGNvbnN0cnVjdG9yXG4gKiBAcGFyYW0ge0FWYWx9IGZuX3Byb3RvIC0gQVZhbCBmb3IgY29uc3RydWN0b3IncyAucHJvdG90eXBlXG4gKiBAcGFyYW0ge3N0cmluZ30gbmFtZSAtIGd1ZXNzZWQgbmFtZVxuICogQHBhcmFtIHtbc3RyaW5nXX0gYXJnTmFtZXMgLSBsaXN0IG9mIHBhcmFtZXRlciBuYW1lc1xuICogQHBhcmFtIHtTY29wZX0gc2MgLSBmdW5jdGlvbnMgc2NvcGUgY2hhaW4sIG9yIGNsb3N1cmVcbiAqIEBwYXJhbSB7bm9kZX0gb3JpZ2luTm9kZSAtIEFTVCBub2RlIGZvciB0aGUgZnVuY3Rpb25cbiAqIEBwYXJhbSB7VHlwZX0gYXJnUHJvdG8gLSBwcm90b3R5cGUgZm9yIGFyZ3VtZW50cyBvYmplY3RcbiAqL1xuZnVuY3Rpb24gRm5UeXBlKGZuX3Byb3RvLCBuYW1lLCBhcmdOYW1lcywgc2MsIG9yaWdpbk5vZGUsIGFyZ1Byb3RvKSB7XG4gICAgT2JqVHlwZS5jYWxsKHRoaXMsIGZuX3Byb3RvLCBuYW1lKTtcbiAgICB0aGlzLnBhcmFtTmFtZXMgPSBhcmdOYW1lcztcbiAgICB0aGlzLnNjID0gc2M7XG4gICAgdGhpcy5vcmlnaW5Ob2RlID0gb3JpZ2luTm9kZTtcbiAgICB0aGlzLmFyZ1Byb3RvID0gYXJnUHJvdG87XG4gICAgLy8gZnVuRW52IDogQ2FsbENvbnRleHQgLT4gW3NlbGYsIHJldCwgZXhjXVxuICAgIHRoaXMuZnVuRW52ID0gbmV3IE1hcDtcbn1cbkZuVHlwZS5wcm90b3R5cGUgPSBPYmplY3QuY3JlYXRlKE9ialR5cGUucHJvdG90eXBlKTtcblxuLyoqXG4gKiBjb25zdHJ1Y3QgU3RhdHVzIGZvciBmdW5jdGlvblxuICogQHBhcmFtIHtDYWxsQ29udGV4dH0gZGVsdGEgLSBjYWxsIGNvbnRleHRcbiAqIEByZXR1cm5zIHtbQVZhbCwgQVZhbCwgQVZhbF19IC0gZm9yIHNlbGYsIHJldHVybiBhbmQgZXhjZXB0aW9uIEFWYWxzXG4gKi9cbkZuVHlwZS5wcm90b3R5cGUuZ2V0RnVuRW52ID0gZnVuY3Rpb24gKGRlbHRhKSB7XG4gICAgaWYgKHRoaXMuZnVuRW52LmhhcyhkZWx0YSkpIHtcbiAgICAgICAgcmV0dXJuIHRoaXMuZnVuRW52LmdldChkZWx0YSk7XG4gICAgfSBlbHNlIHtcbiAgICAgICAgdmFyIHRyaXBsZSA9IFtuZXcgQVZhbCwgbmV3IEFWYWwsIG5ldyBBVmFsXTtcbiAgICAgICAgdGhpcy5mdW5FbnYuc2V0KGRlbHRhLCB0cmlwbGUpO1xuICAgICAgICByZXR1cm4gdHJpcGxlO1xuICAgIH1cbn07XG5cbkZuVHlwZS5wcm90b3R5cGUuZ2V0QXJndW1lbnRzT2JqZWN0ID0gZnVuY3Rpb24gKGRlbHRhKSB7XG4gICAgdGhpcy5hcmdPYmpNYXAgPSB0aGlzLmFyZ09iak1hcCB8fCBuZXcgTWFwO1xuICAgIGlmICh0aGlzLmFyZ09iak1hcC5oYXMoZGVsdGEpKSB7XG4gICAgICAgIHJldHVybiB0aGlzLmFyZ09iak1hcC5nZXQoZGVsdGEpO1xuICAgIH0gZWxzZSB7XG4gICAgICAgIHZhciBhcmdPYmogPSBuZXcgT2JqVHlwZShuZXcgQVZhbCh0aGlzLmFyZ1Byb3RvKSwgJyphcmd1bWVudHMgb2JqZWN0KicpO1xuICAgICAgICB0aGlzLmFyZ09iak1hcC5zZXQoZGVsdGEsIGFyZ09iaik7XG4gICAgICAgIHJldHVybiBhcmdPYmo7XG4gICAgfVxufTtcblxuLyoqXG4gKiBnZXQgT2JqZWN0IG1hZGUgYnkgdGhlIGZ1bmN0aW9uXG4gKiBUT0RPOiB1c2UgYWRkaXRpb25hbCBpbmZvcm1hdGlvbiB0byBjcmVhdGUgbXVsdGlwbGUgaW5zdGFuY2VzXG4gKiBAcmV0dXJucyB7T2JqVHlwZX1cbiAqL1xuRm5UeXBlLnByb3RvdHlwZS5nZXRJbnN0YW5jZSA9IGZ1bmN0aW9uICgpIHtcbiAgICAvLyBvYmpJbnN0YW5jZSBpcyB0aGUgb2JqZWN0IG1hZGUgYnkgdGhlIGZ1bmN0aW9hbm5cbiAgICBpZiAodGhpcy5vYmpJbnN0YW5jZSkgcmV0dXJuIHRoaXMub2JqSW5zdGFuY2U7XG4gICAgLy8gd2UgdW5pZnkgY29uc3RydWN0b3IncyAucHJvdG90eXBlIGFuZCBpbnN0YW5jZSdzIF9fcHJvdG9fX1xuICAgIHRoaXMub2JqSW5zdGFuY2UgPSBuZXcgT2JqVHlwZSh0aGlzLmdldFByb3AoJ3Byb3RvdHlwZScpKTtcbiAgICByZXR1cm4gdGhpcy5vYmpJbnN0YW5jZTtcbn07XG5cbi8qKiBcbiAqIDQuIGFycmF5IHR5cGVzXG4gKiBAY29uc3RydWN0b3JcbiAqL1xuZnVuY3Rpb24gQXJyVHlwZShhcnJfcHJvdG8pIHtcbiAgICBPYmpUeXBlLmNhbGwodGhpcywgYXJyX3Byb3RvLCAnQXJyYXknKTtcbn1cbkFyclR5cGUucHJvdG90eXBlID0gT2JqZWN0LmNyZWF0ZShPYmpUeXBlLnByb3RvdHlwZSk7XG5cbi8vIE1ha2UgcHJpbWl0aXZlIHR5cGVzXG52YXIgUHJpbU51bWJlciA9IG5ldyBQcmltVHlwZSgnbnVtYmVyJyk7XG52YXIgUHJpbVN0cmluZyA9IG5ldyBQcmltVHlwZSgnc3RyaW5nJyk7XG52YXIgUHJpbUJvb2xlYW4gPSBuZXcgUHJpbVR5cGUoJ2Jvb2xlYW4nKTtcblxuLy8gQWJzTnVsbCByZXByZXNlbnRzIGFsbCBlbXB0eSBhYnN0cmFjdCB2YWx1ZXMuXG52YXIgQVZhbE51bGwgPSBuZXcgQVZhbCgpO1xuLy8gWW91IHNob3VsZCBub3QgYWRkIGFueSBwcm9wZXJ0aWVzIHRvIGl0LlxuQVZhbE51bGwucHJvcHMgPSBudWxsO1xuLy8gQWRkaW5nIHR5cGVzIGFyZSBpZ25vcmVkLlxuQVZhbE51bGwuYWRkVHlwZSA9IGZ1bmN0aW9uICgpIHt9O1xuXG5cbi8vIGV4cG9ydFxuZXhwb3J0cy5UeXBlID0gVHlwZTtcbmV4cG9ydHMuT2JqVHlwZSA9IE9ialR5cGU7XG5leHBvcnRzLkZuVHlwZSA9IEZuVHlwZTtcbmV4cG9ydHMuQXJyVHlwZSA9IEFyclR5cGU7XG5leHBvcnRzLlByaW1OdW1iZXIgPSBQcmltTnVtYmVyO1xuZXhwb3J0cy5QcmltU3RyaW5nID0gUHJpbVN0cmluZztcbmV4cG9ydHMuUHJpbUJvb2xlYW4gPSBQcmltQm9vbGVhbjtcbmV4cG9ydHMubWtPYmpGcm9tR2xvYmFsU2NvcGUgPSBta09iakZyb21HbG9iYWxTY29wZTtcblxuZXhwb3J0cy5BVmFsID0gQVZhbDtcbmV4cG9ydHMuQVZhbE51bGwgPSBBVmFsTnVsbDsiLCIvLyBpbXBvcnQgbmVjZXNzYXJ5IGxpYnJhcmllc1xudmFyIGFjb3JuID0gcmVxdWlyZSgnYWNvcm4vZGlzdC9hY29ybicpO1xudmFyIGFjb3JuX2xvb3NlID0gcmVxdWlyZSgnYWNvcm4vZGlzdC9hY29ybl9sb29zZScpO1xudmFyIGF1eCA9IHJlcXVpcmUoJy4vYXV4Jyk7XG52YXIgdHlwZXMgPSByZXF1aXJlKCcuL2RvbWFpbnMvdHlwZXMnKTtcbnZhciBjb250ZXh0ID0gcmVxdWlyZSgnLi9kb21haW5zL2NvbnRleHQnKTtcbnZhciBzdGF0dXMgPSByZXF1aXJlKCcuL2RvbWFpbnMvc3RhdHVzJyk7XG52YXIgdmFyQmxvY2sgPSByZXF1aXJlKCcuL3ZhckJsb2NrJyk7XG52YXIgY0dlbiA9IHJlcXVpcmUoJy4vY29uc3RyYWludC9jR2VuJyk7XG52YXIgdmFyUmVmcyA9IHJlcXVpcmUoJy4vdmFycmVmcycpO1xudmFyIHJldE9jY3VyID0gcmVxdWlyZSgnLi9yZXRPY2N1cicpO1xuXG5mdW5jdGlvbiBhbmFseXplKGlucHV0LCByZXRBbGwpIHtcbiAgICAvLyB0aGUgU2NvcGUgb2JqZWN0IGZvciBnbG9iYWwgc2NvcGVcbiAgICAvLyBzY29wZS5TY29wZS5nbG9iYWxTY29wZSA9IG5ldyBzY29wZS5TY29wZShudWxsKTtcblxuICAgIC8vIHBhcnNpbmcgaW5wdXQgcHJvZ3JhbVxuICAgIHZhciBhc3Q7XG4gICAgdHJ5IHtcbiAgICAgICAgYXN0ID0gYWNvcm4ucGFyc2UoaW5wdXQpO1xuICAgIH0gY2F0Y2ggKGUpIHtcbiAgICAgICAgYXN0ID0gYWNvcm5fbG9vc2UucGFyc2VfZGFtbWl0KGlucHV0KTtcbiAgICB9XG5cbiAgICB2YXIgbm9kZUFycmF5SW5kZXhlZEJ5TGlzdCA9IGF1eC5nZXROb2RlTGlzdChhc3QpO1xuXG4gICAgLy8gU2hvdyBBU1QgYmVmb3JlIHNjb3BlIHJlc29sdXRpb25cbiAgICAvLyBhdXguc2hvd1VuZm9sZGVkKGFzdCk7XG5cbiAgICB2YXJCbG9jay5hbm5vdGF0ZUJsb2NrSW5mbyhhc3QpO1xuICAgIHZhciBnQmxvY2sgPSBhc3RbJ0BibG9jayddO1xuICAgIHZhciBpbml0aWFsQ29udGV4dCA9IG5ldyBjb250ZXh0LkNhbGxTaXRlQ29udGV4dDtcbiAgICB2YXIgZ1Njb3BlID0gZ0Jsb2NrLmdldFNjb3BlSW5zdGFuY2UobnVsbCwgaW5pdGlhbENvbnRleHQpO1xuICAgIHZhciBnT2JqZWN0ID0gdHlwZXMubWtPYmpGcm9tR2xvYmFsU2NvcGUoZ1Njb3BlKTtcbiAgICB2YXIgaW5pdFN0YXR1cyA9IG5ldyBzdGF0dXMuU3RhdHVzKFxuICAgICAgICBnT2JqZWN0LFxuICAgICAgICB0eXBlcy5BVmFsTnVsbCxcbiAgICAgICAgdHlwZXMuQVZhbE51bGwsXG4gICAgICAgIGluaXRpYWxDb250ZXh0LFxuICAgICAgICBnU2NvcGUpO1xuICAgIC8vIHRoZSBwcm90b3R5cGUgb2JqZWN0IG9mIE9iamVjdFxuICAgIHZhciBPYmpQcm90byA9IG5ldyB0eXBlcy5PYmpUeXBlKG51bGwsICdPYmplY3QucHJvdG90eXBlJyk7XG4gICAgdmFyIHJ0Q1ggPSB7XG4gICAgICAgIGdsb2JhbE9iamVjdDogZ09iamVjdCxcbiAgICAgICAgLy8gdGVtcG9yYWxcbiAgICAgICAgcHJvdG9zOiB7XG4gICAgICAgICAgICBPYmplY3Q6IE9ialByb3RvLFxuICAgICAgICAgICAgRnVuY3Rpb246IG5ldyB0eXBlcy5PYmpUeXBlKG5ldyB0eXBlcy5BVmFsKE9ialByb3RvKSwgJ0Z1bmN0aW9uLnByb3RvdHlwZScpLFxuICAgICAgICAgICAgQXJyYXk6IG5ldyB0eXBlcy5PYmpUeXBlKG5ldyB0eXBlcy5BVmFsKE9ialByb3RvKSwgJ0FycmF5LnByb3RvdHlwZScpLFxuICAgICAgICAgICAgUmVnRXhwOiBuZXcgdHlwZXMuT2JqVHlwZShuZXcgdHlwZXMuQVZhbChPYmpQcm90byksICdSZWdFeHAucHJvdG90eXBlJyksXG4gICAgICAgICAgICBTdHJpbmc6IG5ldyB0eXBlcy5PYmpUeXBlKG5ldyB0eXBlcy5BVmFsKE9ialByb3RvKSwgJ1N0cmluZy5wcm90b3R5cGUnKSxcbiAgICAgICAgICAgIE51bWJlcjogbmV3IHR5cGVzLk9ialR5cGUobmV3IHR5cGVzLkFWYWwoT2JqUHJvdG8pLCAnTnVtYmVyLnByb3RvdHlwZScpLFxuICAgICAgICAgICAgQm9vbGVhbjogbmV3IHR5cGVzLk9ialR5cGUobmV3IHR5cGVzLkFWYWwoT2JqUHJvdG8pLCAnQm9vbGVhbi5wcm90b3R5cGUnKVxuICAgICAgICB9XG5cbiAgICB9O1xuICAgIGNHZW4uYWRkQ29uc3RyYWludHMoYXN0LCBpbml0U3RhdHVzLCBydENYKTtcbiAgICB2YXIgY29uc3RyYWludHMgPSBjR2VuLmNvbnN0cmFpbnRzO1xuICAgIC8vYXV4LnNob3dVbmZvbGRlZChnQmxvY2tBbmRBbm5vdGF0ZWRBU1QuYXN0KTtcbiAgICAvLyBhdXguc2hvd1VuZm9sZGVkKGNvbnN0cmFpbnRzKTtcbiAgICAvLyBhdXguc2hvd1VuZm9sZGVkKGdCbG9jayk7XG4gICAgLy8gY29uc29sZS5sb2codXRpbC5pbnNwZWN0KGdCbG9jaywge2RlcHRoOiAxMH0pKTtcbiAgICBpZiAocmV0QWxsKSB7XG4gICAgICAgIHJldHVybiB7Z09iamVjdDogZ09iamVjdCwgQVNUOiBhc3QsIGdCbG9jazogZ0Jsb2NrLCBnU2NvcGU6IGdTY29wZX07XG4gICAgfSBlbHNlIHtcbiAgICAgICAgcmV0dXJuIGdPYmplY3Q7XG4gICAgfVxufVxuXG5leHBvcnRzLmFuYWx5emUgPSBhbmFseXplO1xuZXhwb3J0cy5maW5kSWRlbnRpZmllckF0ID0gdmFyUmVmcy5maW5kSWRlbnRpZmllckF0O1xuZXhwb3J0cy5maW5kVmFyUmVmc0F0ID0gdmFyUmVmcy5maW5kVmFyUmVmc0F0O1xuZXhwb3J0cy5vbkZ1bmN0aW9uT3JSZXR1cm5LZXl3b3JkID0gcmV0T2NjdXIub25GdW5jdGlvbk9yUmV0dXJuS2V5d29yZDtcbmV4cG9ydHMuZmluZFJldHVyblN0YXRlbWVudHMgPSByZXRPY2N1ci5maW5kUmV0dXJuU3RhdGVtZW50czsiLCJjb25zdCB3YWxrID0gcmVxdWlyZSgnYWNvcm4vZGlzdC93YWxrJyk7XG5jb25zdCBteVdhbGtlciA9IHJlcXVpcmUoJy4vdXRpbC9teVdhbGtlcicpO1xuXG4vKipcbiAqIENoZWNrIHdoZXRoZXIgZ2l2ZW4gcG9zIGlzIG9uIGEgZnVuY3Rpb24ga2V5d29yZFxuICogQHBhcmFtIGFzdCAtIEFTVCBvZiBhIHByb2dyYW1cbiAqIEBwYXJhbSBwb3MgLSBpbmRleCBwb3NpdGlvblxuICogQHJldHVybnMgeyp9IC0gZnVuY3Rpb24gbm9kZSBvciBudWxsXG4gKi9cbmZ1bmN0aW9uIG9uRnVuY3Rpb25PclJldHVybktleXdvcmQoYXN0LCBwb3MpIHtcbiAgICBcInVzZSBzdHJpY3RcIjtcblxuICAgIC8vIGZpbmQgZnVuY3Rpb24gbm9kZVxuICAgIC8vIHN0IGlzIHRoZSBlbmNsb3NpbmcgZnVuY3Rpb25cbiAgICBjb25zdCB3YWxrZXIgPSBteVdhbGtlci53cmFwV2Fsa2VyKHdhbGsuYmFzZSxcbiAgICAgICAgLy8gcHJlXG4gICAgICAgIChub2RlLCBzdCkgPT4ge1xuICAgICAgICAgICAgaWYgKG5vZGUuc3RhcnQgPiBwb3MgfHwgbm9kZS5lbmQgPCBwb3MpIHtcbiAgICAgICAgICAgICAgICByZXR1cm4gZmFsc2U7XG4gICAgICAgICAgICB9XG5cbiAgICAgICAgICAgIC8vIG9uIGEgZnVuY3Rpb24ga2V5d29yZCwgOCBpcyB0aGUgbGVuZ3RoIG9mICdmdW5jdGlvbidcbiAgICAgICAgICAgIC8vIG9yIG9uIHJldHVybiBrZXl3b3JkLCA2IGlzIHRoZSBsZW5ndGggb2YgJ3JldHVybidcbiAgICAgICAgICAgIGlmICgoKG5vZGUudHlwZSA9PT0gJ0Z1bmN0aW9uRGVjbGFyYXRpb24nIHx8IG5vZGUudHlwZSA9PT0gJ0Z1bmN0aW9uRXhwcmVzc2lvbicpXG4gICAgICAgICAgICAgICAgJiYgKG5vZGUuc3RhcnQgPD0gcG9zICYmIHBvcyA8PSBub2RlLnN0YXJ0ICsgOCkpXG4gICAgICAgICAgICAgICAgfHxcbiAgICAgICAgICAgICAgICAobm9kZS50eXBlID09PSAnUmV0dXJuU3RhdGVtZW50J1xuICAgICAgICAgICAgICAgICYmIChub2RlLnN0YXJ0IDw9IHBvcyAmJiBwb3MgPD0gbm9kZS5zdGFydCArIDYpKSkge1xuICAgICAgICAgICAgICAgIHRocm93IHN0O1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgcmV0dXJuIHRydWU7XG4gICAgICAgIH0sXG4gICAgICAgIC8vIHBvc3RcbiAgICAgICAgdW5kZWZpbmVkLFxuICAgICAgICAvLyBzdENoYW5nZVxuICAgICAgICAobm9kZSwgc3QpID0+IHtcbiAgICAgICAgICAgIGlmIChub2RlLnR5cGUgPT09ICdGdW5jdGlvbkRlY2xhcmF0aW9uJ1xuICAgICAgICAgICAgICAgIHx8IG5vZGUudHlwZSA9PT0gJ0Z1bmN0aW9uRXhwcmVzc2lvbicpIHtcbiAgICAgICAgICAgICAgICByZXR1cm4gbm9kZTtcbiAgICAgICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgICAgICAgcmV0dXJuIHN0O1xuICAgICAgICAgICAgfVxuICAgICAgICB9KTtcblxuICAgIHRyeSB7XG4gICAgICAgIHdhbGsucmVjdXJzaXZlKGFzdCwgdW5kZWZpbmVkLCB3YWxrZXIpO1xuICAgIH0gY2F0Y2ggKGUpIHtcbiAgICAgICAgaWYgKGUgJiYgZS50eXBlICYmXG4gICAgICAgICAgICAoZS50eXBlID09PSAnRnVuY3Rpb25FeHByZXNzaW9uJ1xuICAgICAgICAgICAgfHwgZS50eXBlID09PSAnRnVuY3Rpb25EZWNsYXJhdGlvbicpKSB7XG4gICAgICAgICAgICByZXR1cm4gZTtcbiAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICAgIHRocm93IGU7XG4gICAgICAgIH1cbiAgICB9XG4gICAgLy8gaWRlbnRpZmllciBub3QgZm91bmRcbiAgICByZXR1cm4gbnVsbDtcbn1cblxuLyoqXG4gKiBHaXZlbiBhIGZ1bmN0aW9uIG5vZGUsIGZpbmQgaXRzIHJldHVybiBub2Rlc1xuICpcbiAqIEBwYXJhbSBmTm9kZSAtIEFTVCBub2RlIG9mIGEgZnVuY3Rpb24sIHBvc3NpYmx5IHdpdGggbm8gYW5ub3RhdGlvblxuICogQHJldHVybnMgeyp9IC0gYXJyYXkgb2YgQVNUIG5vZGVzXG4gKi9cbmZ1bmN0aW9uIGdldFJldHVybk5vZGVzKGZOb2RlKSB7XG4gICAgXCJ1c2Ugc3RyaWN0XCI7XG4gICAgY29uc3QgcmV0cyA9IFtdO1xuICAgIGlmIChmTm9kZS50eXBlICE9PSAnRnVuY3Rpb25FeHByZXNzaW9uJ1xuICAgICAgICAmJiBmTm9kZS50eXBlICE9PSAnRnVuY3Rpb25EZWNsYXJhdGlvbicpIHtcbiAgICAgICAgdGhyb3cgRXJyb3IoJ2ZOb2RlIHNob3VsZCBiZSBhIGZ1bmN0aW9uIG5vZGUnKTtcbiAgICB9XG5cbiAgICBjb25zdCB3YWxrZXIgPSB3YWxrLm1ha2Uoe1xuICAgICAgICBSZXR1cm5TdGF0ZW1lbnQ6IChub2RlKSA9PiB7XG4gICAgICAgICAgICByZXR1cm4gcmV0cy5wdXNoKG5vZGUpO1xuICAgICAgICB9LFxuICAgICAgICBGdW5jdGlvbjogKCkgPT4ge1xuICAgICAgICAgICAgLy8gbm90IHZpc2l0IGlubmVyIGZ1bmN0aW9uc1xuICAgICAgICB9XG4gICAgfSwgd2Fsay5iYXNlKTtcblxuICAgIHdhbGsucmVjdXJzaXZlKGZOb2RlLmJvZHksIHVuZGVmaW5lZCwgd2Fsa2VyKTtcblxuICAgIHJldHVybiByZXRzO1xufVxuXG4vKipcbiAqIEZpbmQgcmV0dXJuIG5vZGVzIGNvcnJlc3BvbmRpbmcgdG8gdGhlIHBvc2l0aW9uXG4gKiBpZiB0aGUgcG9zIGlzIG9uIGEgZnVuY3Rpb24ga2V5d29yZFxuICpcbiAqIEBwYXJhbSBhc3QgLSBBU1Qgbm9kZSBvZiBhIHByb2dyYW0sIHBvc3NpYmx5IHdpdGggbm8gYW5ub3RhdGlvblxuICogQHBhcmFtIHBvcyAtIGN1cnNvciBwb3NpdGlvblxuICogQHBhcmFtIGluY2x1ZGVGdW5jdGlvbktleXdvcmQgLSB3aGV0aGVyIHRvIGluY2x1ZGUgZnVuY3Rpb24ga2V5d29yZCByYW5nZVxuICogQHJldHVybnMge0FycmF5fSAtIGFycmF5IG9mIEFTVCBub2RlcyBvZiByZXR1cm4gc3RhdGVtZW50c1xuICovXG5mdW5jdGlvbiBmaW5kUmV0dXJuU3RhdGVtZW50cyhhc3QsIHBvcywgaW5jbHVkZUZ1bmN0aW9uS2V5d29yZCkge1xuICAgIFwidXNlIHN0cmljdFwiO1xuXG4gICAgY29uc3QgZk5vZGUgPSBvbkZ1bmN0aW9uT3JSZXR1cm5LZXl3b3JkKGFzdCwgcG9zKTtcbiAgICBpZiAoIWZOb2RlKSB7XG4gICAgICAgIC8vIHBvcyBpcyBub3Qgb24gZnVuY3Rpb24ga2V5d29yZFxuICAgICAgICByZXR1cm4gbnVsbDtcbiAgICB9XG5cbiAgICBjb25zdCByZXRzID0gZ2V0UmV0dXJuTm9kZXMoZk5vZGUpO1xuICAgIC8vIHdoZW4gZnVuY3Rpb24gZG9lcyBub3QgaGF2ZSByZXR1cm4gc3RhdGVtZW50cyxcbiAgICAvLyBpbmRpY2F0ZSBpdCBieSB0aGUgY2xvc2luZyBicmFjZSBvZiB0aGUgZnVuY3Rpb24gYm9keVxuICAgIGlmIChyZXRzLmxlbmd0aCA9PT0gMCkge1xuICAgICAgICByZXRzLnB1c2goe3N0YXJ0OiBmTm9kZS5lbmQgLSAxLCBlbmQ6IGZOb2RlLmVuZH0pO1xuICAgIH1cbiAgICBpZiAoaW5jbHVkZUZ1bmN0aW9uS2V5d29yZCkge1xuICAgICAgICByZXRzLnB1c2goe3N0YXJ0OiBmTm9kZS5zdGFydCwgZW5kOiBmTm9kZS5zdGFydCArIDh9KTtcbiAgICB9XG4gICAgcmV0dXJuIHJldHM7XG59XG5cbmV4cG9ydHMub25GdW5jdGlvbk9yUmV0dXJuS2V5d29yZCA9IG9uRnVuY3Rpb25PclJldHVybktleXdvcmQ7XG5leHBvcnRzLmZpbmRSZXR1cm5TdGF0ZW1lbnRzID0gZmluZFJldHVyblN0YXRlbWVudHM7IiwiLyoqXG4gKiBXcmFwIGEgd2Fsa2VyIHdpdGggcHJlLSBhbmQgcG9zdC0gYWN0aW9uc1xuICpcbiAqIEBwYXJhbSBwcmVOb2RlIC0gQXBwbHkgYmVmb3JlIHZpc2l0aW5nIHRoZSBjdXJyZW50IG5vZGUuXG4gKiBJZiByZXR1cm5zIGZhbHNlLCBkbyBub3QgdmlzaXQgdGhlIG5vZGUuXG4gKiBAcGFyYW0gcG9zdE5vZGUgLSBBcHBseSBhZnRlciB2aXNpdGluZyB0aGUgY3VycmVudCBub2RlLlxuICogSWYgZ2l2ZW4sIHJldHVybiB2YWx1ZXMgYXJlIG92ZXJyaWRkZW4uXG4gKiBAcmV0dXJucyB7Kn0gLSBhIG5ldyB3YWxrZXJcbiAqL1xuZnVuY3Rpb24gd3JhcFdhbGtlcih3YWxrZXIsIHByZU5vZGUsIHBvc3ROb2RlLCBzdENoYW5nZSkge1xuICAgIGNvbnN0IHJldFdhbGtlciA9IHt9O1xuICAgIC8vIHdyYXBwaW5nIGVhY2ggZnVuY3Rpb24gcHJlTm9kZSBhbmQgcG9zdE5vZGVcbiAgICBmb3IgKGxldCBub2RlVHlwZSBpbiB3YWxrZXIpIHtcbiAgICAgICAgaWYgKCF3YWxrZXIuaGFzT3duUHJvcGVydHkobm9kZVR5cGUpKSB7XG4gICAgICAgICAgICBjb250aW51ZTtcbiAgICAgICAgfVxuICAgICAgICByZXRXYWxrZXJbbm9kZVR5cGVdID0gKG5vZGUsIHN0LCBjKSA9PiB7XG4gICAgICAgICAgICBsZXQgcmV0O1xuICAgICAgICAgICAgbGV0IG5ld1N0ID0gc3Q7XG4gICAgICAgICAgICBpZiAoc3RDaGFuZ2UpIHtcbiAgICAgICAgICAgICAgICBuZXdTdCA9IHN0Q2hhbmdlKG5vZGUsIHN0KTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGlmICghcHJlTm9kZSB8fCBwcmVOb2RlKG5vZGUsIG5ld1N0LCBjKSkge1xuICAgICAgICAgICAgICAgIHJldCA9IHdhbGtlcltub2RlVHlwZV0obm9kZSwgbmV3U3QsIGMpO1xuICAgICAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICAgICAgICByZXR1cm47XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBpZiAocG9zdE5vZGUpIHtcbiAgICAgICAgICAgICAgICByZXQgPSBwb3N0Tm9kZShub2RlLCBuZXdTdCwgYyk7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICByZXR1cm4gcmV0O1xuICAgICAgICB9XG4gICAgfVxuICAgIHJldHVybiByZXRXYWxrZXI7XG59XG5cbmV4cG9ydHMud3JhcFdhbGtlciA9IHdyYXBXYWxrZXI7IiwiLypcbiBKYXZhU2NyaXB064qUIGdsb2JhbCwgZnVuY3Rpb24gYmxvY2ssIGNhdGNoIGJsb2Nr7JeQIOuzgOyImOqwgCDri6zrprDri6QuXG4gRVM264qUIOydvOuwmCBibG9ja+yXkOuPhCDri6zrprDri6QuXG5cbiBWYXJCbG9ja+uKlCDqsIEgYmxvY2vsl5Ag64us66awIOuzgOyImOuTpOydhCDrgpjtg4Drgrjri6QuXG4gLSBwYXJlbiAgICAgIDogQmxvY2tWYXJzLCDrsJTquaUgYmxvY2vsnYQg64KY7YOA64K064qUIOqwneyytFxuIC0gb3JpZ2luTGFiZWw6IG51bWJlciwg7ZW064u5IEJsb2NrVmFyc+qwgCDshKDslrjrkJwgQVNUIG5vZGXsnZggQGxhYmVsXG4gICAgb3JpZ2lu7J20IOuQoCDsiJgg7J6I64qUIG5vZGXripRcbiAgICBGdW5jdGlvbi5ib2R5LCBDYXRjaENsYXVzZS5ibG9jayDrkZDqsIDsp4Dri6QuXG4gICAg65GQ6rCA7KeAIOuqqOuRkCBCbG9ja1N0YXRlbWVudOydtOuLpC5cbiAtIGlzQ2F0Y2ggICAgOiBib29sZWFuLFxuICAgKiB0cnVlICAtPiBjYXRjaCBibG9ja1xuICAgKiBmYWxzZSAtPiBmdW5jdGlvbiBibG9jaywgb3IgZ2xvYmFsXG5cbiAtIHBhcmFtVmFyTmFtZXMgOiDrp6TqsJzrs4DsiJgg7J2066aEIOuqqeuhnSwg66ek6rCcIOuzgOyImCDsiJzshJzrjIDroZxcbiAtIGxvY2FsVmFyTmFtZXMgOiDsp4Dsl60g67OA7IiYIOydtOumhCDrqqnroZ0sIOyInOyEnCDrrLTsnZjrr7hcbiAgICBhcmd1bWVudHPrpbwg7IKs7Jqp7ZWY64qUIOqyveyasCBsb2NhbFZhck5hbWVz7JeQIOuTseyepe2VmOqzoCxcbiAgICBhcmd1bWVudHMgb2JqZWN066W8IOyCrOyaqe2VmOuptCB1c2VBcmd1bWVudHNPYmplY3QgPT0gdHJ1ZVxuXG4gLSAob3B0aW9uYWwpIHVzZUFyZ3VtZW50c09iamVjdDogYm9vbGVhblxuICAgIO2VqOyImCBib2R5IGJsb2Nr7J24IOqyveyasOyXkOunjCDsgqzsmqkg6rCA64qlXG4gICAgKiB0cnVlICA6IGFyZ3VtZW50cyBvYmplY3TqsIAg7IKs7Jqp65CY7JeI64ukLlxuICAgICAg7KaJIO2VqOyImCBib2R57JeQ7IScIOuzgOyImCBhcmd1bWVudHPrpbwg7ISg7Ja4IOyXhuydtCDsgqzsmqntlojri6QuXG4gICAgICDsnbQg6rK97JqwLCBhcmd1bWVudHPripQg7ZWo7IiY7J2YIOyngOyXrSDrs4DsiJjroZwg65Ox66Gd65Cc64ukLlxuICAgICogZmFsc2Ug7J24IOqyveyasOuKlCDsl4bri6QuIOq3uOuftOqxsOuptCDslYTsmIgg67OA7IiYIOyekOyytOqwgCDsl4bri6QuXG5cbiAtIHVzZWRWYXJpYWJsZXMgOiDqsIEgYmxvY2vsnZgg66ek6rCc67OA7IiYLCDsp4Dsl63rs4DsiJgg7KSRXG4gICDsgqzsmqnrkJjripQg7JyE7LmY6rCAIOyeiOuKlCDqsoPrk6TsnZgg66qp66GdXG5cbiAtIGluc3RhbmNlcyA6IERlbHRhIC0+IFZhckJsb2Nr7J2YIOuzgOyImOuTpCAtPiBBVmFsXG4gICBnZXRJbnN0YW5jZShkZWx0YSkg66W8IO2Gte2VtCDqsJnsnYAgZGVsdGHripQg6rCZ7J2AIG1hcHBpbmcg7KO86rKMIOunjOuTrFxuXG4gLSBzY29wZUluc3RhbmNlcyA6IFtTY29wZV1cbiAgIO2YhOyerCBWYXJCbG9ja+ydhCDrp4jsp4Drp4nsnLzroZwg7ZWY64qUIFNjb3Bl66W8IOuqqOuRkCDrqqjsnYDri6QuXG4gICBnZXRTY29wZUluc3RhbmNlKGRlbHRhLCBwYXJlbikg7J2EIO2Gte2VtCDqsJnsnYAgc2NvcGUgY2hhaW7snYBcbiAgIOqwmeydgCDqsJ3ssrTqsIAg65CY64+E66GdIOunjOuToOuLpC5cbiovXG4ndXNlIHN0cmljdCc7XG5cbnZhciB0eXBlcyA9IHJlcXVpcmUoJy4vZG9tYWlucy90eXBlcycpO1xudmFyIHdhbGsgPSByZXF1aXJlKCdhY29ybi9kaXN0L3dhbGsnKTtcbnZhciBhdXggPSByZXF1aXJlKCcuL2F1eCcpO1xuXG5mdW5jdGlvbiBWYXJCbG9jayhwYXJlbiwgb3JpZ2luTm9kZSwgaXNDYXRjaCkge1xuICAgIHRoaXMucGFyZW4gPSBwYXJlbjtcbiAgICB0aGlzLm9yaWdpbk5vZGUgPSBvcmlnaW5Ob2RlO1xuICAgIHRoaXMub3JpZ2luTGFiZWwgPSBvcmlnaW5Ob2RlWydAbGFiZWwnXTtcbiAgICB0aGlzLmlzQ2F0Y2ggPSBpc0NhdGNoO1xuICAgIHRoaXMucGFyYW1WYXJOYW1lcyA9IFtdO1xuICAgIHRoaXMubG9jYWxWYXJOYW1lcyA9IFtdO1xuXG4gICAgdGhpcy51c2VkVmFyaWFibGVzID0gW107XG4gICAgLy8gdGhpcy51c2VBcmd1bWVudHNPYmplY3RcbiAgICB0aGlzLmluc3RhbmNlcyA9IE9iamVjdC5jcmVhdGUobnVsbCk7XG4gICAgdGhpcy5zY29wZUluc3RhbmNlcyA9IFtdO1xufVxuXG5WYXJCbG9jay5wcm90b3R5cGUgPSBPYmplY3QuY3JlYXRlKG51bGwpO1xuXG5WYXJCbG9jay5wcm90b3R5cGUuaXNHbG9iYWwgPSBmdW5jdGlvbiAoKSB7XG4gICAgcmV0dXJuIHRoaXMucGFyZW4gPT0gbnVsbDtcbn07XG5WYXJCbG9jay5wcm90b3R5cGUuaXNGdW5jdGlvbiA9IGZ1bmN0aW9uICgpIHtcbiAgICByZXR1cm4gdGhpcy5wYXJlbiAhPSBudWxsICYmIHRoaXMubG9jYWxWYXJOYW1lcyAhPSBudWxsO1xufTtcblZhckJsb2NrLnByb3RvdHlwZS5pc0NhdGNoQmxvY2sgPSBmdW5jdGlvbiAoKSB7XG4gICAgcmV0dXJuIHRoaXMuaXNDYXRjaDtcbn07XG5cblZhckJsb2NrLnByb3RvdHlwZS5nZXRMb2NhbFZhck5hbWVzID0gZnVuY3Rpb24gKCkge1xuICAgIHJldHVybiB0aGlzLmxvY2FsVmFyTmFtZXM7XG59O1xuVmFyQmxvY2sucHJvdG90eXBlLmdldFBhcmFtVmFyTmFtZXMgPSBmdW5jdGlvbiAoKSB7XG4gICAgcmV0dXJuIHRoaXMucGFyYW1WYXJOYW1lcztcbn07XG5WYXJCbG9jay5wcm90b3R5cGUuaGFzTG9jYWxWYXIgPSBmdW5jdGlvbiAodmFyTmFtZSkge1xuICAgIHJldHVybiB0aGlzLmxvY2FsVmFyTmFtZXMgJiYgdGhpcy5sb2NhbFZhck5hbWVzLmluZGV4T2YodmFyTmFtZSkgPiAtMTtcbn07XG5WYXJCbG9jay5wcm90b3R5cGUuaGFzUGFyYW1WYXIgPSBmdW5jdGlvbiAodmFyTmFtZSkge1xuICAgIHJldHVybiB0aGlzLnBhcmFtVmFyTmFtZXMuaW5kZXhPZih2YXJOYW1lKSA+IC0xO1xufTtcblZhckJsb2NrLnByb3RvdHlwZS5oYXNWYXIgPSBmdW5jdGlvbiAodmFyTmFtZSkge1xuICAgIHJldHVybiB0aGlzLmhhc1BhcmFtVmFyKHZhck5hbWUpIHx8IHRoaXMuaGFzTG9jYWxWYXIodmFyTmFtZSk7XG59O1xuXG5WYXJCbG9jay5wcm90b3R5cGUuYWRkRGVjbGFyZWRMb2NhbFZhciA9IGZ1bmN0aW9uICh2YXJOYW1lLCBpc0Z1bkRlY2wpIHtcbiAgICB2YXIgY3VyckJsb2NrID0gdGhpcztcbiAgICAvLyBwZWVsIG9mZiBpbml0aWFsIGNhdGNoIGJsb2Nrc1xuICAgIC8vIGZvciBmdW5jdGlvbiBkZWNsLCBza2lwIGFueSBjYXRjaCBibG9ja3MsXG4gICAgLy8gZm9yIHZhcmlhYmxlIGRlY2wsIHNraXAgY2F0Y2ggYmxvY2sgd2l0aCBkaWZmZXJlbnQgdmFyTmFtZS5cbiAgICB3aGlsZSAoY3VyckJsb2NrLmlzQ2F0Y2hCbG9jaygpICYmXG4gICAgICAgICAgIChpc0Z1bkRlY2wgfHwgIWN1cnJCbG9jay5oYXNQYXJhbVZhcih2YXJOYW1lKSkpIHtcbiAgICAgICAgY3VyckJsb2NrID0gY3VyckJsb2NrLnBhcmVuO1xuICAgIH1cbiAgICAvLyBpZiBhbHJlYWR5IGFkZGVkLCBkbyBub3QgYWRkXG4gICAgaWYgKCFjdXJyQmxvY2suaGFzVmFyKHZhck5hbWUpKSB7XG4gICAgICAgIGN1cnJCbG9jay5sb2NhbFZhck5hbWVzLnB1c2godmFyTmFtZSk7XG4gICAgfVxuICAgIC8vIHJldHVybnMgdGhlIGJsb2NrIG9iamVjdCB0aGF0IGNvbnRhaW5zIHRoZSB2YXJpYWJsZVxuICAgIHJldHVybiBjdXJyQmxvY2s7XG59O1xuVmFyQmxvY2sucHJvdG90eXBlLmFkZFBhcmFtVmFyID0gZnVuY3Rpb24gKHZhck5hbWUpIHtcbiAgICB0aGlzLnBhcmFtVmFyTmFtZXMucHVzaCh2YXJOYW1lKTtcbn07XG5WYXJCbG9jay5wcm90b3R5cGUuZmluZFZhckluQ2hhaW4gPSBmdW5jdGlvbiAodmFyTmFtZSkge1xuICAgIHZhciBjdXJyQmxvY2sgPSB0aGlzO1xuICAgIHdoaWxlIChjdXJyQmxvY2sgJiYgY3VyckJsb2NrLnBhcmVuICYmICFjdXJyQmxvY2suaGFzVmFyKHZhck5hbWUpKSB7XG4gICAgICAgIGN1cnJCbG9jayA9IGN1cnJCbG9jay5wYXJlbjtcbiAgICB9XG4gICAgLy8gaWYgbm90IGZvdW5kLCBpdCB3aWxsIHJldHVybiB0aGUgZ2xvYmFsXG4gICAgcmV0dXJuIGN1cnJCbG9jaztcbn07XG5cblZhckJsb2NrLnByb3RvdHlwZS5hZGRVc2VkVmFyID0gZnVuY3Rpb24gKHZhck5hbWUpIHtcbiAgICBpZiAodGhpcy51c2VkVmFyaWFibGVzLmluZGV4T2YodmFyTmFtZSkgPT09IC0xKSB7XG4gICAgICAgIHRoaXMudXNlZFZhcmlhYmxlcy5wdXNoKHZhck5hbWUpO1xuICAgIH1cbn07XG5WYXJCbG9jay5wcm90b3R5cGUuZ2V0VXNlZFZhck5hbWVzID0gZnVuY3Rpb24gKCkge1xuICAgIHJldHVybiB0aGlzLnVzZWRWYXJpYWJsZXM7XG59O1xuVmFyQmxvY2sucHJvdG90eXBlLmlzVXNlZFZhciA9IGZ1bmN0aW9uICh2YXJOYW1lKSB7XG4gICAgcmV0dXJuIHRoaXMudXNlZFZhcmlhYmxlcy5pbmRleE9mKHZhck5hbWUpID4gLTE7XG59O1xuXG4vLyByZXR1cm5zIGEgbWFwcGluZ1xuVmFyQmxvY2sucHJvdG90eXBlLmdldEluc3RhbmNlID0gZnVuY3Rpb24gKGRlbHRhKSB7XG4gICAgaWYgKHRoaXMuaW5zdGFuY2VzW2RlbHRhXSkge1xuICAgICAgICByZXR1cm4gdGhpcy5pbnN0YW5jZXNbZGVsdGFdO1xuICAgIH1cbiAgICAvLyBjb25zdHJ1Y3QgVmFyTWFwXG4gICAgdmFyIHZhck1hcCA9IG5ldyBNYXAoKTtcbiAgICB2YXIgdmFyTmFtZXMgPSB0aGlzLmdldFBhcmFtVmFyTmFtZXMoKS5jb25jYXQodGhpcy5nZXRMb2NhbFZhck5hbWVzKCkpO1xuXG4gICAgZm9yICh2YXIgaSA9IDA7IGkgPCB2YXJOYW1lcy5sZW5ndGg7IGkrKykge1xuICAgICAgICB2YXJNYXAuc2V0KHZhck5hbWVzW2ldLCBuZXcgdHlwZXMuQVZhbCgpKTtcbiAgICB9XG4gICAgLy8gcmVtZW1iZXIgdGhlIGluc3RhbmNlXG4gICAgdGhpcy5pbnN0YW5jZXNbZGVsdGFdID0gdmFyTWFwO1xuICAgIHJldHVybiB2YXJNYXA7XG59O1xuLy8gcmV0dXJucyBhbiBhcnJheVxuVmFyQmxvY2sucHJvdG90eXBlLmdldFBhcmFtQVZhbHMgPSBmdW5jdGlvbiAoZGVsdGEpIHtcbiAgICB2YXIgaW5zdGFuY2UgPSB0aGlzLmdldEluc3RhbmNlKGRlbHRhKTtcbiAgICB2YXIgcGFyYW1zID0gW107XG4gICAgdGhpcy5nZXRQYXJhbVZhck5hbWVzKCkuZm9yRWFjaChmdW5jdGlvbiAobmFtZSkge1xuICAgICAgICBwYXJhbXMucHVzaChpbnN0YW5jZVthdXguaW50ZXJuYWxOYW1lKG5hbWUpXSk7XG4gICAgfSk7XG4gICAgcmV0dXJuIHBhcmFtcztcbn07XG4vLyByZXR1cm5zIGFuIEFWYWxcblZhckJsb2NrLnByb3RvdHlwZS5nZXRBcmd1bWVudHNBVmFsID0gZnVuY3Rpb24gKGRlbHRhKSB7XG4gICAgaWYgKCF0aGlzLnVzZUFyZ3VtZW50c09iamVjdCkge1xuICAgICAgICB0aHJvdyBuZXcgRXJyb3IoJ05vdCBmb3IgdGhpcyBWYXJCbG9jaycpO1xuICAgIH1cbiAgICByZXR1cm4gdGhpcy5nZXRJbnN0YW5jZShkZWx0YSlbYXV4LmludGVybmFsTmFtZSgnYXJndW1lbnRzJyldO1xufTtcblxuLy8gZ2V0IGEgU2NvcGUgaW5zdGFuY2VcblZhckJsb2NrLnByb3RvdHlwZS5nZXRTY29wZUluc3RhbmNlID0gZnVuY3Rpb24gKHBhcmVuLCBkZWx0YSkge1xuICAgIHZhciB2YXJNYXAgPSB0aGlzLmdldEluc3RhbmNlKGRlbHRhKTtcbiAgICB2YXIgZm91bmQgPSBudWxsO1xuXG4gICAgdGhpcy5zY29wZUluc3RhbmNlcy5mb3JFYWNoKGZ1bmN0aW9uIChzYykge1xuICAgICAgICBpZiAoc2MucGFyZW4gPT09IHBhcmVuICYmIHNjLnZhck1hcCA9PT0gdmFyTWFwKSBmb3VuZCA9IHNjO1xuICAgIH0pO1xuXG4gICAgaWYgKGZvdW5kKSB7XG4gICAgICAgIHJldHVybiBmb3VuZDtcbiAgICB9IGVsc2Uge1xuICAgICAgICB2YXIgbmV3U2NvcGVJbnN0YW5jZSA9IG5ldyBTY29wZShwYXJlbiwgdmFyTWFwLCB0aGlzKTtcbiAgICAgICAgdGhpcy5zY29wZUluc3RhbmNlcy5wdXNoKG5ld1Njb3BlSW5zdGFuY2UpO1xuICAgICAgICByZXR1cm4gbmV3U2NvcGVJbnN0YW5jZTtcbiAgICB9XG59O1xuXG52YXIgZGVjbGFyZWRWYXJpYWJsZUZpbmRlciA9IHdhbGsubWFrZSh7XG4gICBGdW5jdGlvbjogZnVuY3Rpb24gKG5vZGUsIGN1cnJCbG9jaywgYykge1xuICAgICAgICB2YXIgcGFyZW5CbG9jayA9IGN1cnJCbG9jaztcbiAgICAgICAgaWYgKG5vZGUuaWQpIHtcbiAgICAgICAgICAgIHZhciBmdW5jTmFtZSA9IG5vZGUuaWQubmFtZTtcbiAgICAgICAgICAgIHBhcmVuQmxvY2sgPSBjdXJyQmxvY2suYWRkRGVjbGFyZWRMb2NhbFZhcihmdW5jTmFtZSwgdHJ1ZSk7XG4gICAgICAgIH1cbiAgICAgICAgLy8gY3JlYXRlIGEgVmFyQmxvY2sgZm9yIGZ1bmN0aW9uXG4gICAgICAgIHZhciBmdW5jQmxvY2sgPSBuZXcgVmFyQmxvY2socGFyZW5CbG9jaywgbm9kZSk7XG4gICAgICAgIG5vZGUuYm9keVsnQGJsb2NrJ10gPSBmdW5jQmxvY2s7XG4gICAgICAgIC8vIGFkZCBmdW5jdGlvbiBwYXJhbWV0ZXJzIHRvIHRoZSBzY29wZVxuICAgICAgICBmb3IgKHZhciBpID0gMDsgaSA8IG5vZGUucGFyYW1zLmxlbmd0aDsgaSsrKSB7XG4gICAgICAgICAgICB2YXIgcGFyYW1OYW1lID0gbm9kZS5wYXJhbXNbaV0ubmFtZTtcbiAgICAgICAgICAgIGZ1bmNCbG9jay5hZGRQYXJhbVZhcihwYXJhbU5hbWUpO1xuICAgICAgICB9XG4gICAgICAgIGMobm9kZS5ib2R5LCBmdW5jQmxvY2ssIHVuZGVmaW5lZCk7XG4gICAgfSxcbiAgICBWYXJpYWJsZURlY2xhcmF0aW9uOiBmdW5jdGlvbiAobm9kZSwgY3VyckJsb2NrLCBjKSB7XG4gICAgICAgIGZvciAodmFyIGkgPSAwOyBpIDwgbm9kZS5kZWNsYXJhdGlvbnMubGVuZ3RoOyBpKyspIHtcbiAgICAgICAgICAgIHZhciBkZWNsID0gbm9kZS5kZWNsYXJhdGlvbnNbaV07XG4gICAgICAgICAgICB2YXIgbmFtZSA9IGRlY2wuaWQubmFtZTtcbiAgICAgICAgICAgIGN1cnJCbG9jay5hZGREZWNsYXJlZExvY2FsVmFyKG5hbWUpO1xuICAgICAgICB9XG4gICAgICAgIGlmIChkZWNsLmluaXQpIGMoZGVjbC5pbml0LCBjdXJyQmxvY2ssIHVuZGVmaW5lZCk7XG4gICAgfSxcbiAgICBUcnlTdGF0ZW1lbnQ6IGZ1bmN0aW9uIChub2RlLCBjdXJyU2NvcGUsIGMpIHtcbiAgICAgICAgYyhub2RlLmJsb2NrLCBjdXJyU2NvcGUsIHVuZGVmaW5lZCk7XG4gICAgICAgIGlmIChub2RlLmhhbmRsZXIpIHtcbiAgICAgICAgICAgIGMobm9kZS5oYW5kbGVyLCBjdXJyU2NvcGUsIHVuZGVmaW5lZCk7XG4gICAgICAgIH1cbiAgICAgICAgaWYgKG5vZGUuZmluYWxpemVyKSB7XG4gICAgICAgICAgICBjKG5vZGUuZmluYWxpemVyLCBjdXJyU2NvcGUsIHVuZGVmaW5lZCk7XG4gICAgICAgIH1cbiAgICB9LFxuICAgIENhdGNoQ2xhdXNlOiBmdW5jdGlvbiAobm9kZSwgY3VyckJsb2NrLCBjKSB7XG4gICAgICAgIHZhciBjYXRjaEJsb2NrID0gbmV3IFZhckJsb2NrKGN1cnJCbG9jaywgbm9kZSwgdHJ1ZSk7XG4gICAgICAgIGNhdGNoQmxvY2suYWRkUGFyYW1WYXIobm9kZS5wYXJhbS5uYW1lKTtcbiAgICAgICAgbm9kZS5ib2R5WydAYmxvY2snXSA9IGNhdGNoQmxvY2s7XG4gICAgICAgIGMobm9kZS5ib2R5LCBjYXRjaEJsb2NrLCB1bmRlZmluZWQpO1xuICAgIH1cbn0pO1xuXG4vLyBGb3IgdmFyaWFibGVzIGluIGdsb2JhbCBhbmQgYXJndW1lbnRzIGluIGZ1bmN0aW9uc1xudmFyIHZhcmlhYmxlVXNhZ2VDb2xsZWN0b3IgPSB3YWxrLm1ha2Uoe1xuICAgIElkZW50aWZpZXI6IGZ1bmN0aW9uIChub2RlLCBjdXJyQmxvY2ssIGMpIHtcbiAgICAgICAgdmFyIGNvbnRhaW5pbmdCbG9jaywgdmFyTmFtZSA9IG5vZGUubmFtZTtcbiAgICAgICAgaWYgKHZhck5hbWUgIT09ICdhcmd1bWVudHMnKSB7XG4gICAgICAgICAgICBjb250YWluaW5nQmxvY2sgPSBjdXJyQmxvY2suZmluZFZhckluQ2hhaW4odmFyTmFtZSk7XG4gICAgICAgICAgICBpZiAoY29udGFpbmluZ0Jsb2NrLmlzR2xvYmFsKCkpIHtcbiAgICAgICAgICAgICAgICBjb250YWluaW5nQmxvY2suYWRkRGVjbGFyZWRMb2NhbFZhcih2YXJOYW1lKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGNvbnRhaW5pbmdCbG9jay5hZGRVc2VkVmFyKHZhck5hbWUpO1xuICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgICAgLy8gdmFyTmFtZSA9PSAnYXJndW1lbnRzJ1xuICAgICAgICAgICAgY29udGFpbmluZ0Jsb2NrID0gY3VyckJsb2NrO1xuICAgICAgICAgICAgd2hpbGUgKGNvbnRhaW5pbmdCbG9jay5pc0NhdGNoQmxvY2soKSAmJlxuICAgICAgICAgICAgICAgICAgICAhY29udGFpbmluZ0Jsb2NrLmhhc1BhcmFtVmFyKHZhck5hbWUpKSB7XG4gICAgICAgICAgICAgICAgY29udGFpbmluZ0Jsb2NrID0gY29udGFpbmluZ0Jsb2NrLnBhcmVuO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgaWYgKGNvbnRhaW5pbmdCbG9jay5oYXNWYXIodmFyTmFtZSkpIHtcbiAgICAgICAgICAgICAgICAvLyBhcmd1bWVudHMgaXMgZXhwbGljaXRseSBkZWNsYXJlZFxuICAgICAgICAgICAgICAgIGNvbnRhaW5pbmdCbG9jay5hZGRVc2VkVmFyKHZhck5hbWUpO1xuICAgICAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICAgICAgICAvLyBhcmd1bWVudHMgaXMgbm90IGV4cGxpY2l0bHkgZGVjbGFyZWRcbiAgICAgICAgICAgICAgICAvLyBhZGQgaXQgYXMgbG9jYWwgdmFyaWFibGVcbiAgICAgICAgICAgICAgICBjb250YWluaW5nQmxvY2suYWRkRGVjbGFyZWRMb2NhbFZhcih2YXJOYW1lKTtcbiAgICAgICAgICAgICAgICAvLyBhbHNvIGl0IGlzIHVzZWRcbiAgICAgICAgICAgICAgICBjb250YWluaW5nQmxvY2suYWRkVXNlZFZhcih2YXJOYW1lKTtcbiAgICAgICAgICAgICAgICBpZiAoY29udGFpbmluZ0Jsb2NrLmlzRnVuY3Rpb24oKSkge1xuICAgICAgICAgICAgICAgICAgICBjb250YWluaW5nQmxvY2sudXNlQXJndW1lbnRzT2JqZWN0ID0gdHJ1ZTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICB9XG4gICAgICAgIH1cbiAgICB9LFxuXG4gICAgUmV0dXJuU3RhdGVtZW50OiBmdW5jdGlvbiAobm9kZSwgY3VyckJsb2NrLCBjKSB7XG4gICAgICAgIHZhciBmdW5jdGlvbkJsb2NrID0gY3VyckJsb2NrO1xuICAgICAgICB3aGlsZSAoZnVuY3Rpb25CbG9jay5pc0NhdGNoQmxvY2soKSkge1xuICAgICAgICAgICAgZnVuY3Rpb25CbG9jayA9IGZ1bmN0aW9uQmxvY2sucGFyZW47XG4gICAgICAgIH1cbiAgICAgICAgaWYgKCFmdW5jdGlvbkJsb2NrLmlzR2xvYmFsKCkgJiYgbm9kZS5hcmd1bWVudCAhPT0gbnVsbCkge1xuICAgICAgICAgICAgZnVuY3Rpb25CbG9jay51c2VSZXR1cm5XaXRoQXJndW1lbnQgPSB0cnVlO1xuICAgICAgICB9XG4gICAgICAgIGlmIChub2RlLmFyZ3VtZW50KSB7XG4gICAgICAgICAgICBjKG5vZGUuYXJndW1lbnQsIGN1cnJCbG9jaywgdW5kZWZpbmVkKTtcbiAgICAgICAgfVxuICAgIH0sXG5cbiAgICBTY29wZUJvZHk6IGZ1bmN0aW9uIChub2RlLCBjdXJyQmxvY2ssIGMpIHtcbiAgICAgICAgYyhub2RlLCBub2RlWydAYmxvY2snXSB8fCBjdXJyQmxvY2spO1xuICAgIH1cbn0pO1xuXG5cbmZ1bmN0aW9uIGFubm90YXRlQmxvY2tJbmZvKGFzdCwgZ0Jsb2NrKSB7XG4gICAgaWYgKCFnQmxvY2spIHtcbiAgICAgICAgLy8gd2hlbiBnbG9iYWwgYmxvY2sgaXMgbm90IGdpdmVuLCBjcmVhdGVcbiAgICAgICAgZ0Jsb2NrID0gbmV3IFZhckJsb2NrKG51bGwsIGFzdCk7XG4gICAgfVxuICAgIGFzdFsnQGJsb2NrJ10gPSBnQmxvY2s7XG4gICAgd2Fsay5yZWN1cnNpdmUoYXN0LCBnQmxvY2ssIG51bGwsIGRlY2xhcmVkVmFyaWFibGVGaW5kZXIpO1xuICAgIHdhbGsucmVjdXJzaXZlKGFzdCwgZ0Jsb2NrLCBudWxsLCB2YXJpYWJsZVVzYWdlQ29sbGVjdG9yKTtcbiAgICByZXR1cm4gYXN0O1xufVxuXG4vLyBkZWZpbmUgc2NvcGUgb2JqZWN0XG5mdW5jdGlvbiBTY29wZShwYXJlbiwgdmFyTWFwLCB2Yikge1xuICAgIHRoaXMucGFyZW4gPSBwYXJlbjtcbiAgICB0aGlzLnZhck1hcCA9IHZhck1hcDtcbiAgICB0aGlzLnZiID0gdmI7XG59XG5TY29wZS5wcm90b3R5cGUgPSBPYmplY3QuY3JlYXRlKG51bGwpO1xuLy8gZmluZCBBVmFsIG9mIGEgdmFyaWFibGUgaW4gdGhlIGNoYWluXG5TY29wZS5wcm90b3R5cGUuZ2V0QVZhbE9mID0gZnVuY3Rpb24gKHZhck5hbWUpIHtcbiAgICB2YXIgY3VyciA9IHRoaXM7XG4gICAgd2hpbGUgKGN1cnIgIT0gbnVsbCkge1xuICAgICAgICBpZiAoY3Vyci52YXJNYXAuaGFzKHZhck5hbWUpKSB7XG4gICAgICAgICAgICByZXR1cm4gY3Vyci52YXJNYXAuZ2V0KHZhck5hbWUpO1xuICAgICAgICB9XG4gICAgICAgIGN1cnIgPSBjdXJyLnBhcmVuO1xuICAgIH1cbiAgICB0aHJvdyBuZXcgRXJyb3IoJ1Nob3VsZCBoYXZlIGZvdW5kIHRoZSB2YXJpYWJsZScpO1xufTtcbi8vIHJlbW92ZSBpbml0aWFsIGNhdGNoIHNjb3BlcyBmcm9tIHRoZSBjaGFpblxuU2NvcGUucHJvdG90eXBlLnJlbW92ZUluaXRpYWxDYXRjaEJsb2NrcyA9IGZ1bmN0aW9uICgpIHtcbiAgICB2YXIgY3VyciA9IHRoaXM7XG4gICAgd2hpbGUgKGN1cnIudmIuaXNDYXRjaEJsb2NrKCkpIHtcbiAgICAgICAgY3VyciA9IGN1cnIucGFyZW47XG4gICAgfVxuICAgIHJldHVybiBjdXJyO1xufTtcblxuXG5leHBvcnRzLlZhckJsb2NrID0gVmFyQmxvY2s7XG5leHBvcnRzLmFubm90YXRlQmxvY2tJbmZvID0gYW5ub3RhdGVCbG9ja0luZm87XG5leHBvcnRzLlNjb3BlID0gU2NvcGU7XG4iLCJjb25zdCB3YWxrID0gcmVxdWlyZSgnYWNvcm4vZGlzdC93YWxrJyk7XG5jb25zdCBteVdhbGtlciA9IHJlcXVpcmUoJy4vdXRpbC9teVdhbGtlcicpO1xuXG4vLyBhIHdhbGtlciB0aGF0IHZpc2l0cyBlYWNoIGlkIHdpdGggdmFyQmxvY2tcbmNvbnN0IHZhcldhbGtlcj0gd2Fsay5tYWtlKHtcbiAgICBGdW5jdGlvbjogZnVuY3Rpb24gKG5vZGUsIHZiLCBjKSB7XG4gICAgICAgIGNvbnN0IGlubmVyVmIgPSBub2RlLmJvZHlbJ0BibG9jayddO1xuICAgICAgICBpZiAobm9kZS5pZCkgYyhub2RlLmlkLCBpbm5lclZiKTtcbiAgICAgICAgZm9yIChsZXQgaSA9IDA7IGkgPCBub2RlLnBhcmFtcy5sZW5ndGg7IGkrKylcbiAgICAgICAgICAgIGMobm9kZS5wYXJhbXNbaV0sIGlubmVyVmIpO1xuICAgICAgICBjKG5vZGUuYm9keSwgaW5uZXJWYik7XG4gICAgfSxcbiAgICBUcnlTdGF0ZW1lbnQ6IGZ1bmN0aW9uIChub2RlLCB2YiwgYykge1xuICAgICAgICBjKG5vZGUuYmxvY2ssIHZiKTtcbiAgICAgICAgaWYgKG5vZGUuaGFuZGxlcikge1xuICAgICAgICAgICAgYyhub2RlLmhhbmRsZXIsIHZiKTtcbiAgICAgICAgfVxuICAgICAgICBpZiAobm9kZS5maW5hbGl6ZXIpIHtcbiAgICAgICAgICAgIGMobm9kZS5maW5hbGl6ZXIsIHZiKTtcbiAgICAgICAgfVxuICAgIH0sXG4gICAgQ2F0Y2hDbGF1c2U6IGZ1bmN0aW9uIChub2RlLCB2YiwgYykge1xuICAgICAgICBjb25zdCBjYXRjaFZiID0gbm9kZS5ib2R5WydAYmxvY2snXTtcbiAgICAgICAgYyhub2RlLnBhcmFtLCBjYXRjaFZiKTtcbiAgICAgICAgYyhub2RlLmJvZHksIGNhdGNoVmIpO1xuICAgIH0sXG4gICAgVmFyaWFibGVEZWNsYXJhdGlvbjogZnVuY3Rpb24gKG5vZGUsIHZiLCBjKSB7XG4gICAgICAgIGZvciAobGV0IGkgPSAwOyBpIDwgbm9kZS5kZWNsYXJhdGlvbnMubGVuZ3RoOyArK2kpIHtcbiAgICAgICAgICAgIGNvbnN0IGRlY2wgPSBub2RlLmRlY2xhcmF0aW9uc1tpXTtcbiAgICAgICAgICAgIGMoZGVjbC5pZCwgdmIpO1xuICAgICAgICAgICAgaWYgKGRlY2wuaW5pdCkgYyhkZWNsLmluaXQsIHZiKTtcbiAgICAgICAgfVxuICAgIH1cbn0pO1xuXG5mdW5jdGlvbiBmaW5kSWRlbnRpZmllckF0KGFzdCwgcG9zKSB7XG4gICAgXCJ1c2Ugc3RyaWN0XCI7XG5cbiAgICBmdW5jdGlvbiBGb3VuZChub2RlLCBzdGF0ZSkge1xuICAgICAgICB0aGlzLm5vZGUgPSBub2RlO1xuICAgICAgICB0aGlzLnN0YXRlID0gc3RhdGU7XG4gICAgfVxuXG4gICAgLy8gZmluZCB0aGUgbm9kZVxuICAgIGNvbnN0IHdhbGtlciA9IG15V2Fsa2VyLndyYXBXYWxrZXIodmFyV2Fsa2VyLFxuICAgICAgICAobm9kZSwgdmIpID0+IHtcbiAgICAgICAgICAgIGlmIChub2RlLnN0YXJ0ID4gcG9zIHx8IG5vZGUuZW5kIDwgcG9zKSB7XG4gICAgICAgICAgICAgICAgcmV0dXJuIGZhbHNlO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgaWYgKG5vZGUudHlwZSA9PT0gJ0lkZW50aWZpZXInICYmIG5vZGUubmFtZSAhPT0gJ+KclicpIHtcbiAgICAgICAgICAgICAgICB0aHJvdyBuZXcgRm91bmQobm9kZSwgdmIpO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgcmV0dXJuIHRydWU7XG4gICAgICAgIH0pO1xuXG4gICAgdHJ5IHtcbiAgICAgICAgd2Fsay5yZWN1cnNpdmUoYXN0LCBhc3RbJ0BibG9jayddLCB3YWxrZXIpO1xuICAgIH0gY2F0Y2ggKGUpIHtcbiAgICAgICAgaWYgKGUgaW5zdGFuY2VvZiBGb3VuZCkge1xuICAgICAgICAgICAgcmV0dXJuIGU7XG4gICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgICB0aHJvdyBlO1xuICAgICAgICB9XG4gICAgfVxuICAgIC8vIGlkZW50aWZpZXIgbm90IGZvdW5kXG4gICAgcmV0dXJuIG51bGw7XG59XG5cbi8qKlxuICpcbiAqIEBwYXJhbSBhc3QgLSBzY29wZSBhbm5vdGF0ZWQgQVNUXG4gKiBAcGFyYW0ge251bWJlcn0gcG9zIC0gY2hhcmFjdGVyIHBvc2l0aW9uXG4gKiBAcmV0dXJucyB7Kn0gLSBhcnJheSBvZiBBU1Qgbm9kZXNcbiAqL1xuZnVuY3Rpb24gZmluZFZhclJlZnNBdChhc3QsIHBvcykge1xuICAgIFwidXNlIHN0cmljdFwiO1xuICAgIGNvbnN0IGZvdW5kID0gZmluZElkZW50aWZpZXJBdChhc3QsIHBvcyk7XG4gICAgaWYgKCFmb3VuZCkge1xuICAgICAgICAvLyBwb3MgaXMgbm90IGF0IGEgdmFyaWFibGVcbiAgICAgICAgcmV0dXJuIG51bGw7XG4gICAgfVxuICAgIC8vIGZpbmQgcmVmcyBmb3IgdGhlIGlkIG5vZGVcbiAgICBjb25zdCByZWZzID0gZmluZFJlZnNUb1ZhcmlhYmxlKGFzdCwgZm91bmQpO1xuXG4gICAgcmV0dXJuIHJlZnM7XG59XG5cbi8qKlxuICpcbiAqIEBwYXJhbSBhc3QgLSBzY29wZSBhbm5vdGF0ZWQgQVNUXG4gKiBAcGFyYW0gZm91bmQgLSBub2RlIGFuZCB2YXJCbG9jayBvZiB0aGUgdmFyaWFibGVcbiAqIEByZXR1cm5zIHtBcnJheX0gLSBhcnJheSBvZiBBU1Qgbm9kZXNcbiAqL1xuZnVuY3Rpb24gZmluZFJlZnNUb1ZhcmlhYmxlKGFzdCwgZm91bmQpIHtcbiAgICBcInVzZSBzdHJpY3RcIjtcbiAgICBjb25zdCB2YXJOYW1lID0gZm91bmQubm9kZS5uYW1lO1xuICAgIGNvbnN0IHZiMSA9IGZvdW5kLnN0YXRlLmZpbmRWYXJJbkNoYWluKHZhck5hbWUpO1xuICAgIGNvbnN0IHJlZnMgPSBbXTtcblxuICAgIGNvbnN0IHdhbGtlciA9IHdhbGsubWFrZSh7XG4gICAgICAgIElkZW50aWZpZXI6IChub2RlLCB2YikgPT4ge1xuICAgICAgICAgICAgaWYgKG5vZGUubmFtZSAhPT0gdmFyTmFtZSkgcmV0dXJuO1xuICAgICAgICAgICAgaWYgKHZiMSA9PT0gdmIuZmluZFZhckluQ2hhaW4odmFyTmFtZSkpIHtcbiAgICAgICAgICAgICAgICByZWZzLnB1c2gobm9kZSk7XG4gICAgICAgICAgICB9XG4gICAgICAgIH1cbiAgICB9LCB2YXJXYWxrZXIpO1xuXG4gICAgd2Fsay5yZWN1cnNpdmUodmIxLm9yaWdpbk5vZGUsIHZiMSwgd2Fsa2VyKTtcbiAgICByZXR1cm4gcmVmcztcbn1cblxuZXhwb3J0cy5maW5kSWRlbnRpZmllckF0ID0gZmluZElkZW50aWZpZXJBdDtcbmV4cG9ydHMuZmluZFZhclJlZnNBdCA9IGZpbmRWYXJSZWZzQXQ7IiwiKGZ1bmN0aW9uKGYpe2lmKHR5cGVvZiBleHBvcnRzPT09XCJvYmplY3RcIiYmdHlwZW9mIG1vZHVsZSE9PVwidW5kZWZpbmVkXCIpe21vZHVsZS5leHBvcnRzPWYoKX1lbHNlIGlmKHR5cGVvZiBkZWZpbmU9PT1cImZ1bmN0aW9uXCImJmRlZmluZS5hbWQpe2RlZmluZShbXSxmKX1lbHNle3ZhciBnO2lmKHR5cGVvZiB3aW5kb3chPT1cInVuZGVmaW5lZFwiKXtnPXdpbmRvd31lbHNlIGlmKHR5cGVvZiBnbG9iYWwhPT1cInVuZGVmaW5lZFwiKXtnPWdsb2JhbH1lbHNlIGlmKHR5cGVvZiBzZWxmIT09XCJ1bmRlZmluZWRcIil7Zz1zZWxmfWVsc2V7Zz10aGlzfWcuYWNvcm4gPSBmKCl9fSkoZnVuY3Rpb24oKXt2YXIgZGVmaW5lLG1vZHVsZSxleHBvcnRzO3JldHVybiAoZnVuY3Rpb24gZSh0LG4scil7ZnVuY3Rpb24gcyhvLHUpe2lmKCFuW29dKXtpZighdFtvXSl7dmFyIGE9dHlwZW9mIHJlcXVpcmU9PVwiZnVuY3Rpb25cIiYmcmVxdWlyZTtpZighdSYmYSlyZXR1cm4gYShvLCEwKTtpZihpKXJldHVybiBpKG8sITApO3ZhciBmPW5ldyBFcnJvcihcIkNhbm5vdCBmaW5kIG1vZHVsZSAnXCIrbytcIidcIik7dGhyb3cgZi5jb2RlPVwiTU9EVUxFX05PVF9GT1VORFwiLGZ9dmFyIGw9bltvXT17ZXhwb3J0czp7fX07dFtvXVswXS5jYWxsKGwuZXhwb3J0cyxmdW5jdGlvbihlKXt2YXIgbj10W29dWzFdW2VdO3JldHVybiBzKG4/bjplKX0sbCxsLmV4cG9ydHMsZSx0LG4scil9cmV0dXJuIG5bb10uZXhwb3J0c312YXIgaT10eXBlb2YgcmVxdWlyZT09XCJmdW5jdGlvblwiJiZyZXF1aXJlO2Zvcih2YXIgbz0wO288ci5sZW5ndGg7bysrKXMocltvXSk7cmV0dXJuIHN9KSh7MTpbZnVuY3Rpb24oX2RlcmVxXyxtb2R1bGUsZXhwb3J0cyl7XG5cblxuLy8gVGhlIG1haW4gZXhwb3J0ZWQgaW50ZXJmYWNlICh1bmRlciBgc2VsZi5hY29ybmAgd2hlbiBpbiB0aGVcbi8vIGJyb3dzZXIpIGlzIGEgYHBhcnNlYCBmdW5jdGlvbiB0aGF0IHRha2VzIGEgY29kZSBzdHJpbmcgYW5kXG4vLyByZXR1cm5zIGFuIGFic3RyYWN0IHN5bnRheCB0cmVlIGFzIHNwZWNpZmllZCBieSBbTW96aWxsYSBwYXJzZXJcbi8vIEFQSV1bYXBpXS5cbi8vXG4vLyBbYXBpXTogaHR0cHM6Ly9kZXZlbG9wZXIubW96aWxsYS5vcmcvZW4tVVMvZG9jcy9TcGlkZXJNb25rZXkvUGFyc2VyX0FQSVxuXG5cInVzZSBzdHJpY3RcIjtcblxuZXhwb3J0cy5wYXJzZSA9IHBhcnNlO1xuXG4vLyBUaGlzIGZ1bmN0aW9uIHRyaWVzIHRvIHBhcnNlIGEgc2luZ2xlIGV4cHJlc3Npb24gYXQgYSBnaXZlblxuLy8gb2Zmc2V0IGluIGEgc3RyaW5nLiBVc2VmdWwgZm9yIHBhcnNpbmcgbWl4ZWQtbGFuZ3VhZ2UgZm9ybWF0c1xuLy8gdGhhdCBlbWJlZCBKYXZhU2NyaXB0IGV4cHJlc3Npb25zLlxuXG5leHBvcnRzLnBhcnNlRXhwcmVzc2lvbkF0ID0gcGFyc2VFeHByZXNzaW9uQXQ7XG5cbi8vIEFjb3JuIGlzIG9yZ2FuaXplZCBhcyBhIHRva2VuaXplciBhbmQgYSByZWN1cnNpdmUtZGVzY2VudCBwYXJzZXIuXG4vLyBUaGUgYHRva2VuaXplYCBleHBvcnQgcHJvdmlkZXMgYW4gaW50ZXJmYWNlIHRvIHRoZSB0b2tlbml6ZXIuXG5cbmV4cG9ydHMudG9rZW5pemVyID0gdG9rZW5pemVyO1xuZXhwb3J0cy5fX2VzTW9kdWxlID0gdHJ1ZTtcbi8vIEFjb3JuIGlzIGEgdGlueSwgZmFzdCBKYXZhU2NyaXB0IHBhcnNlciB3cml0dGVuIGluIEphdmFTY3JpcHQuXG4vL1xuLy8gQWNvcm4gd2FzIHdyaXR0ZW4gYnkgTWFyaWpuIEhhdmVyYmVrZSwgSW5ndmFyIFN0ZXBhbnlhbiwgYW5kXG4vLyB2YXJpb3VzIGNvbnRyaWJ1dG9ycyBhbmQgcmVsZWFzZWQgdW5kZXIgYW4gTUlUIGxpY2Vuc2UuXG4vL1xuLy8gR2l0IHJlcG9zaXRvcmllcyBmb3IgQWNvcm4gYXJlIGF2YWlsYWJsZSBhdFxuLy9cbi8vICAgICBodHRwOi8vbWFyaWpuaGF2ZXJiZWtlLm5sL2dpdC9hY29yblxuLy8gICAgIGh0dHBzOi8vZ2l0aHViLmNvbS9tYXJpam5oL2Fjb3JuLmdpdFxuLy9cbi8vIFBsZWFzZSB1c2UgdGhlIFtnaXRodWIgYnVnIHRyYWNrZXJdW2doYnRdIHRvIHJlcG9ydCBpc3N1ZXMuXG4vL1xuLy8gW2doYnRdOiBodHRwczovL2dpdGh1Yi5jb20vbWFyaWpuaC9hY29ybi9pc3N1ZXNcbi8vXG4vLyBUaGlzIGZpbGUgZGVmaW5lcyB0aGUgbWFpbiBwYXJzZXIgaW50ZXJmYWNlLiBUaGUgbGlicmFyeSBhbHNvIGNvbWVzXG4vLyB3aXRoIGEgW2Vycm9yLXRvbGVyYW50IHBhcnNlcl1bZGFtbWl0XSBhbmQgYW5cbi8vIFthYnN0cmFjdCBzeW50YXggdHJlZSB3YWxrZXJdW3dhbGtdLCBkZWZpbmVkIGluIG90aGVyIGZpbGVzLlxuLy9cbi8vIFtkYW1taXRdOiBhY29ybl9sb29zZS5qc1xuLy8gW3dhbGtdOiB1dGlsL3dhbGsuanNcblxudmFyIF9zdGF0ZSA9IF9kZXJlcV8oXCIuL3N0YXRlXCIpO1xuXG52YXIgUGFyc2VyID0gX3N0YXRlLlBhcnNlcjtcblxudmFyIF9vcHRpb25zID0gX2RlcmVxXyhcIi4vb3B0aW9uc1wiKTtcblxudmFyIGdldE9wdGlvbnMgPSBfb3B0aW9ucy5nZXRPcHRpb25zO1xuXG5fZGVyZXFfKFwiLi9wYXJzZXV0aWxcIik7XG5cbl9kZXJlcV8oXCIuL3N0YXRlbWVudFwiKTtcblxuX2RlcmVxXyhcIi4vbHZhbFwiKTtcblxuX2RlcmVxXyhcIi4vZXhwcmVzc2lvblwiKTtcblxuZXhwb3J0cy5QYXJzZXIgPSBfc3RhdGUuUGFyc2VyO1xuZXhwb3J0cy5wbHVnaW5zID0gX3N0YXRlLnBsdWdpbnM7XG5leHBvcnRzLmRlZmF1bHRPcHRpb25zID0gX29wdGlvbnMuZGVmYXVsdE9wdGlvbnM7XG5cbnZhciBfbG9jYXRpb24gPSBfZGVyZXFfKFwiLi9sb2NhdGlvblwiKTtcblxuZXhwb3J0cy5Tb3VyY2VMb2NhdGlvbiA9IF9sb2NhdGlvbi5Tb3VyY2VMb2NhdGlvbjtcbmV4cG9ydHMuZ2V0TGluZUluZm8gPSBfbG9jYXRpb24uZ2V0TGluZUluZm87XG5leHBvcnRzLk5vZGUgPSBfZGVyZXFfKFwiLi9ub2RlXCIpLk5vZGU7XG5cbnZhciBfdG9rZW50eXBlID0gX2RlcmVxXyhcIi4vdG9rZW50eXBlXCIpO1xuXG5leHBvcnRzLlRva2VuVHlwZSA9IF90b2tlbnR5cGUuVG9rZW5UeXBlO1xuZXhwb3J0cy50b2tUeXBlcyA9IF90b2tlbnR5cGUudHlwZXM7XG5cbnZhciBfdG9rZW5jb250ZXh0ID0gX2RlcmVxXyhcIi4vdG9rZW5jb250ZXh0XCIpO1xuXG5leHBvcnRzLlRva0NvbnRleHQgPSBfdG9rZW5jb250ZXh0LlRva0NvbnRleHQ7XG5leHBvcnRzLnRva0NvbnRleHRzID0gX3Rva2VuY29udGV4dC50eXBlcztcblxudmFyIF9pZGVudGlmaWVyID0gX2RlcmVxXyhcIi4vaWRlbnRpZmllclwiKTtcblxuZXhwb3J0cy5pc0lkZW50aWZpZXJDaGFyID0gX2lkZW50aWZpZXIuaXNJZGVudGlmaWVyQ2hhcjtcbmV4cG9ydHMuaXNJZGVudGlmaWVyU3RhcnQgPSBfaWRlbnRpZmllci5pc0lkZW50aWZpZXJTdGFydDtcbmV4cG9ydHMuVG9rZW4gPSBfZGVyZXFfKFwiLi90b2tlbml6ZVwiKS5Ub2tlbjtcblxudmFyIF93aGl0ZXNwYWNlID0gX2RlcmVxXyhcIi4vd2hpdGVzcGFjZVwiKTtcblxuZXhwb3J0cy5pc05ld0xpbmUgPSBfd2hpdGVzcGFjZS5pc05ld0xpbmU7XG5leHBvcnRzLmxpbmVCcmVhayA9IF93aGl0ZXNwYWNlLmxpbmVCcmVhaztcbmV4cG9ydHMubGluZUJyZWFrRyA9IF93aGl0ZXNwYWNlLmxpbmVCcmVha0c7XG52YXIgdmVyc2lvbiA9IFwiMS4yLjJcIjtleHBvcnRzLnZlcnNpb24gPSB2ZXJzaW9uO1xuXG5mdW5jdGlvbiBwYXJzZShpbnB1dCwgb3B0aW9ucykge1xuICB2YXIgcCA9IHBhcnNlcihvcHRpb25zLCBpbnB1dCk7XG4gIHZhciBzdGFydFBvcyA9IHAucG9zLFxuICAgICAgc3RhcnRMb2MgPSBwLm9wdGlvbnMubG9jYXRpb25zICYmIHAuY3VyUG9zaXRpb24oKTtcbiAgcC5uZXh0VG9rZW4oKTtcbiAgcmV0dXJuIHAucGFyc2VUb3BMZXZlbChwLm9wdGlvbnMucHJvZ3JhbSB8fCBwLnN0YXJ0Tm9kZUF0KHN0YXJ0UG9zLCBzdGFydExvYykpO1xufVxuXG5mdW5jdGlvbiBwYXJzZUV4cHJlc3Npb25BdChpbnB1dCwgcG9zLCBvcHRpb25zKSB7XG4gIHZhciBwID0gcGFyc2VyKG9wdGlvbnMsIGlucHV0LCBwb3MpO1xuICBwLm5leHRUb2tlbigpO1xuICByZXR1cm4gcC5wYXJzZUV4cHJlc3Npb24oKTtcbn1cblxuZnVuY3Rpb24gdG9rZW5pemVyKGlucHV0LCBvcHRpb25zKSB7XG4gIHJldHVybiBwYXJzZXIob3B0aW9ucywgaW5wdXQpO1xufVxuXG5mdW5jdGlvbiBwYXJzZXIob3B0aW9ucywgaW5wdXQpIHtcbiAgcmV0dXJuIG5ldyBQYXJzZXIoZ2V0T3B0aW9ucyhvcHRpb25zKSwgU3RyaW5nKGlucHV0KSk7XG59XG5cbn0se1wiLi9leHByZXNzaW9uXCI6NixcIi4vaWRlbnRpZmllclwiOjcsXCIuL2xvY2F0aW9uXCI6OCxcIi4vbHZhbFwiOjksXCIuL25vZGVcIjoxMCxcIi4vb3B0aW9uc1wiOjExLFwiLi9wYXJzZXV0aWxcIjoxMixcIi4vc3RhdGVcIjoxMyxcIi4vc3RhdGVtZW50XCI6MTQsXCIuL3Rva2VuY29udGV4dFwiOjE1LFwiLi90b2tlbml6ZVwiOjE2LFwiLi90b2tlbnR5cGVcIjoxNyxcIi4vd2hpdGVzcGFjZVwiOjE5fV0sMjpbZnVuY3Rpb24oX2RlcmVxXyxtb2R1bGUsZXhwb3J0cyl7XG5pZiAodHlwZW9mIE9iamVjdC5jcmVhdGUgPT09ICdmdW5jdGlvbicpIHtcbiAgLy8gaW1wbGVtZW50YXRpb24gZnJvbSBzdGFuZGFyZCBub2RlLmpzICd1dGlsJyBtb2R1bGVcbiAgbW9kdWxlLmV4cG9ydHMgPSBmdW5jdGlvbiBpbmhlcml0cyhjdG9yLCBzdXBlckN0b3IpIHtcbiAgICBjdG9yLnN1cGVyXyA9IHN1cGVyQ3RvclxuICAgIGN0b3IucHJvdG90eXBlID0gT2JqZWN0LmNyZWF0ZShzdXBlckN0b3IucHJvdG90eXBlLCB7XG4gICAgICBjb25zdHJ1Y3Rvcjoge1xuICAgICAgICB2YWx1ZTogY3RvcixcbiAgICAgICAgZW51bWVyYWJsZTogZmFsc2UsXG4gICAgICAgIHdyaXRhYmxlOiB0cnVlLFxuICAgICAgICBjb25maWd1cmFibGU6IHRydWVcbiAgICAgIH1cbiAgICB9KTtcbiAgfTtcbn0gZWxzZSB7XG4gIC8vIG9sZCBzY2hvb2wgc2hpbSBmb3Igb2xkIGJyb3dzZXJzXG4gIG1vZHVsZS5leHBvcnRzID0gZnVuY3Rpb24gaW5oZXJpdHMoY3Rvciwgc3VwZXJDdG9yKSB7XG4gICAgY3Rvci5zdXBlcl8gPSBzdXBlckN0b3JcbiAgICB2YXIgVGVtcEN0b3IgPSBmdW5jdGlvbiAoKSB7fVxuICAgIFRlbXBDdG9yLnByb3RvdHlwZSA9IHN1cGVyQ3Rvci5wcm90b3R5cGVcbiAgICBjdG9yLnByb3RvdHlwZSA9IG5ldyBUZW1wQ3RvcigpXG4gICAgY3Rvci5wcm90b3R5cGUuY29uc3RydWN0b3IgPSBjdG9yXG4gIH1cbn1cblxufSx7fV0sMzpbZnVuY3Rpb24oX2RlcmVxXyxtb2R1bGUsZXhwb3J0cyl7XG4vLyBzaGltIGZvciB1c2luZyBwcm9jZXNzIGluIGJyb3dzZXJcblxudmFyIHByb2Nlc3MgPSBtb2R1bGUuZXhwb3J0cyA9IHt9O1xudmFyIHF1ZXVlID0gW107XG52YXIgZHJhaW5pbmcgPSBmYWxzZTtcblxuZnVuY3Rpb24gZHJhaW5RdWV1ZSgpIHtcbiAgICBpZiAoZHJhaW5pbmcpIHtcbiAgICAgICAgcmV0dXJuO1xuICAgIH1cbiAgICBkcmFpbmluZyA9IHRydWU7XG4gICAgdmFyIGN1cnJlbnRRdWV1ZTtcbiAgICB2YXIgbGVuID0gcXVldWUubGVuZ3RoO1xuICAgIHdoaWxlKGxlbikge1xuICAgICAgICBjdXJyZW50UXVldWUgPSBxdWV1ZTtcbiAgICAgICAgcXVldWUgPSBbXTtcbiAgICAgICAgdmFyIGkgPSAtMTtcbiAgICAgICAgd2hpbGUgKCsraSA8IGxlbikge1xuICAgICAgICAgICAgY3VycmVudFF1ZXVlW2ldKCk7XG4gICAgICAgIH1cbiAgICAgICAgbGVuID0gcXVldWUubGVuZ3RoO1xuICAgIH1cbiAgICBkcmFpbmluZyA9IGZhbHNlO1xufVxucHJvY2Vzcy5uZXh0VGljayA9IGZ1bmN0aW9uIChmdW4pIHtcbiAgICBxdWV1ZS5wdXNoKGZ1bik7XG4gICAgaWYgKCFkcmFpbmluZykge1xuICAgICAgICBzZXRUaW1lb3V0KGRyYWluUXVldWUsIDApO1xuICAgIH1cbn07XG5cbnByb2Nlc3MudGl0bGUgPSAnYnJvd3Nlcic7XG5wcm9jZXNzLmJyb3dzZXIgPSB0cnVlO1xucHJvY2Vzcy5lbnYgPSB7fTtcbnByb2Nlc3MuYXJndiA9IFtdO1xucHJvY2Vzcy52ZXJzaW9uID0gJyc7IC8vIGVtcHR5IHN0cmluZyB0byBhdm9pZCByZWdleHAgaXNzdWVzXG5wcm9jZXNzLnZlcnNpb25zID0ge307XG5cbmZ1bmN0aW9uIG5vb3AoKSB7fVxuXG5wcm9jZXNzLm9uID0gbm9vcDtcbnByb2Nlc3MuYWRkTGlzdGVuZXIgPSBub29wO1xucHJvY2Vzcy5vbmNlID0gbm9vcDtcbnByb2Nlc3Mub2ZmID0gbm9vcDtcbnByb2Nlc3MucmVtb3ZlTGlzdGVuZXIgPSBub29wO1xucHJvY2Vzcy5yZW1vdmVBbGxMaXN0ZW5lcnMgPSBub29wO1xucHJvY2Vzcy5lbWl0ID0gbm9vcDtcblxucHJvY2Vzcy5iaW5kaW5nID0gZnVuY3Rpb24gKG5hbWUpIHtcbiAgICB0aHJvdyBuZXcgRXJyb3IoJ3Byb2Nlc3MuYmluZGluZyBpcyBub3Qgc3VwcG9ydGVkJyk7XG59O1xuXG4vLyBUT0RPKHNodHlsbWFuKVxucHJvY2Vzcy5jd2QgPSBmdW5jdGlvbiAoKSB7IHJldHVybiAnLycgfTtcbnByb2Nlc3MuY2hkaXIgPSBmdW5jdGlvbiAoZGlyKSB7XG4gICAgdGhyb3cgbmV3IEVycm9yKCdwcm9jZXNzLmNoZGlyIGlzIG5vdCBzdXBwb3J0ZWQnKTtcbn07XG5wcm9jZXNzLnVtYXNrID0gZnVuY3Rpb24oKSB7IHJldHVybiAwOyB9O1xuXG59LHt9XSw0OltmdW5jdGlvbihfZGVyZXFfLG1vZHVsZSxleHBvcnRzKXtcbm1vZHVsZS5leHBvcnRzID0gZnVuY3Rpb24gaXNCdWZmZXIoYXJnKSB7XG4gIHJldHVybiBhcmcgJiYgdHlwZW9mIGFyZyA9PT0gJ29iamVjdCdcbiAgICAmJiB0eXBlb2YgYXJnLmNvcHkgPT09ICdmdW5jdGlvbidcbiAgICAmJiB0eXBlb2YgYXJnLmZpbGwgPT09ICdmdW5jdGlvbidcbiAgICAmJiB0eXBlb2YgYXJnLnJlYWRVSW50OCA9PT0gJ2Z1bmN0aW9uJztcbn1cbn0se31dLDU6W2Z1bmN0aW9uKF9kZXJlcV8sbW9kdWxlLGV4cG9ydHMpe1xuKGZ1bmN0aW9uIChwcm9jZXNzLGdsb2JhbCl7XG4vLyBDb3B5cmlnaHQgSm95ZW50LCBJbmMuIGFuZCBvdGhlciBOb2RlIGNvbnRyaWJ1dG9ycy5cbi8vXG4vLyBQZXJtaXNzaW9uIGlzIGhlcmVieSBncmFudGVkLCBmcmVlIG9mIGNoYXJnZSwgdG8gYW55IHBlcnNvbiBvYnRhaW5pbmcgYVxuLy8gY29weSBvZiB0aGlzIHNvZnR3YXJlIGFuZCBhc3NvY2lhdGVkIGRvY3VtZW50YXRpb24gZmlsZXMgKHRoZVxuLy8gXCJTb2Z0d2FyZVwiKSwgdG8gZGVhbCBpbiB0aGUgU29mdHdhcmUgd2l0aG91dCByZXN0cmljdGlvbiwgaW5jbHVkaW5nXG4vLyB3aXRob3V0IGxpbWl0YXRpb24gdGhlIHJpZ2h0cyB0byB1c2UsIGNvcHksIG1vZGlmeSwgbWVyZ2UsIHB1Ymxpc2gsXG4vLyBkaXN0cmlidXRlLCBzdWJsaWNlbnNlLCBhbmQvb3Igc2VsbCBjb3BpZXMgb2YgdGhlIFNvZnR3YXJlLCBhbmQgdG8gcGVybWl0XG4vLyBwZXJzb25zIHRvIHdob20gdGhlIFNvZnR3YXJlIGlzIGZ1cm5pc2hlZCB0byBkbyBzbywgc3ViamVjdCB0byB0aGVcbi8vIGZvbGxvd2luZyBjb25kaXRpb25zOlxuLy9cbi8vIFRoZSBhYm92ZSBjb3B5cmlnaHQgbm90aWNlIGFuZCB0aGlzIHBlcm1pc3Npb24gbm90aWNlIHNoYWxsIGJlIGluY2x1ZGVkXG4vLyBpbiBhbGwgY29waWVzIG9yIHN1YnN0YW50aWFsIHBvcnRpb25zIG9mIHRoZSBTb2Z0d2FyZS5cbi8vXG4vLyBUSEUgU09GVFdBUkUgSVMgUFJPVklERUQgXCJBUyBJU1wiLCBXSVRIT1VUIFdBUlJBTlRZIE9GIEFOWSBLSU5ELCBFWFBSRVNTXG4vLyBPUiBJTVBMSUVELCBJTkNMVURJTkcgQlVUIE5PVCBMSU1JVEVEIFRPIFRIRSBXQVJSQU5USUVTIE9GXG4vLyBNRVJDSEFOVEFCSUxJVFksIEZJVE5FU1MgRk9SIEEgUEFSVElDVUxBUiBQVVJQT1NFIEFORCBOT05JTkZSSU5HRU1FTlQuIElOXG4vLyBOTyBFVkVOVCBTSEFMTCBUSEUgQVVUSE9SUyBPUiBDT1BZUklHSFQgSE9MREVSUyBCRSBMSUFCTEUgRk9SIEFOWSBDTEFJTSxcbi8vIERBTUFHRVMgT1IgT1RIRVIgTElBQklMSVRZLCBXSEVUSEVSIElOIEFOIEFDVElPTiBPRiBDT05UUkFDVCwgVE9SVCBPUlxuLy8gT1RIRVJXSVNFLCBBUklTSU5HIEZST00sIE9VVCBPRiBPUiBJTiBDT05ORUNUSU9OIFdJVEggVEhFIFNPRlRXQVJFIE9SIFRIRVxuLy8gVVNFIE9SIE9USEVSIERFQUxJTkdTIElOIFRIRSBTT0ZUV0FSRS5cblxudmFyIGZvcm1hdFJlZ0V4cCA9IC8lW3NkaiVdL2c7XG5leHBvcnRzLmZvcm1hdCA9IGZ1bmN0aW9uKGYpIHtcbiAgaWYgKCFpc1N0cmluZyhmKSkge1xuICAgIHZhciBvYmplY3RzID0gW107XG4gICAgZm9yICh2YXIgaSA9IDA7IGkgPCBhcmd1bWVudHMubGVuZ3RoOyBpKyspIHtcbiAgICAgIG9iamVjdHMucHVzaChpbnNwZWN0KGFyZ3VtZW50c1tpXSkpO1xuICAgIH1cbiAgICByZXR1cm4gb2JqZWN0cy5qb2luKCcgJyk7XG4gIH1cblxuICB2YXIgaSA9IDE7XG4gIHZhciBhcmdzID0gYXJndW1lbnRzO1xuICB2YXIgbGVuID0gYXJncy5sZW5ndGg7XG4gIHZhciBzdHIgPSBTdHJpbmcoZikucmVwbGFjZShmb3JtYXRSZWdFeHAsIGZ1bmN0aW9uKHgpIHtcbiAgICBpZiAoeCA9PT0gJyUlJykgcmV0dXJuICclJztcbiAgICBpZiAoaSA+PSBsZW4pIHJldHVybiB4O1xuICAgIHN3aXRjaCAoeCkge1xuICAgICAgY2FzZSAnJXMnOiByZXR1cm4gU3RyaW5nKGFyZ3NbaSsrXSk7XG4gICAgICBjYXNlICclZCc6IHJldHVybiBOdW1iZXIoYXJnc1tpKytdKTtcbiAgICAgIGNhc2UgJyVqJzpcbiAgICAgICAgdHJ5IHtcbiAgICAgICAgICByZXR1cm4gSlNPTi5zdHJpbmdpZnkoYXJnc1tpKytdKTtcbiAgICAgICAgfSBjYXRjaCAoXykge1xuICAgICAgICAgIHJldHVybiAnW0NpcmN1bGFyXSc7XG4gICAgICAgIH1cbiAgICAgIGRlZmF1bHQ6XG4gICAgICAgIHJldHVybiB4O1xuICAgIH1cbiAgfSk7XG4gIGZvciAodmFyIHggPSBhcmdzW2ldOyBpIDwgbGVuOyB4ID0gYXJnc1srK2ldKSB7XG4gICAgaWYgKGlzTnVsbCh4KSB8fCAhaXNPYmplY3QoeCkpIHtcbiAgICAgIHN0ciArPSAnICcgKyB4O1xuICAgIH0gZWxzZSB7XG4gICAgICBzdHIgKz0gJyAnICsgaW5zcGVjdCh4KTtcbiAgICB9XG4gIH1cbiAgcmV0dXJuIHN0cjtcbn07XG5cblxuLy8gTWFyayB0aGF0IGEgbWV0aG9kIHNob3VsZCBub3QgYmUgdXNlZC5cbi8vIFJldHVybnMgYSBtb2RpZmllZCBmdW5jdGlvbiB3aGljaCB3YXJucyBvbmNlIGJ5IGRlZmF1bHQuXG4vLyBJZiAtLW5vLWRlcHJlY2F0aW9uIGlzIHNldCwgdGhlbiBpdCBpcyBhIG5vLW9wLlxuZXhwb3J0cy5kZXByZWNhdGUgPSBmdW5jdGlvbihmbiwgbXNnKSB7XG4gIC8vIEFsbG93IGZvciBkZXByZWNhdGluZyB0aGluZ3MgaW4gdGhlIHByb2Nlc3Mgb2Ygc3RhcnRpbmcgdXAuXG4gIGlmIChpc1VuZGVmaW5lZChnbG9iYWwucHJvY2VzcykpIHtcbiAgICByZXR1cm4gZnVuY3Rpb24oKSB7XG4gICAgICByZXR1cm4gZXhwb3J0cy5kZXByZWNhdGUoZm4sIG1zZykuYXBwbHkodGhpcywgYXJndW1lbnRzKTtcbiAgICB9O1xuICB9XG5cbiAgaWYgKHByb2Nlc3Mubm9EZXByZWNhdGlvbiA9PT0gdHJ1ZSkge1xuICAgIHJldHVybiBmbjtcbiAgfVxuXG4gIHZhciB3YXJuZWQgPSBmYWxzZTtcbiAgZnVuY3Rpb24gZGVwcmVjYXRlZCgpIHtcbiAgICBpZiAoIXdhcm5lZCkge1xuICAgICAgaWYgKHByb2Nlc3MudGhyb3dEZXByZWNhdGlvbikge1xuICAgICAgICB0aHJvdyBuZXcgRXJyb3IobXNnKTtcbiAgICAgIH0gZWxzZSBpZiAocHJvY2Vzcy50cmFjZURlcHJlY2F0aW9uKSB7XG4gICAgICAgIGNvbnNvbGUudHJhY2UobXNnKTtcbiAgICAgIH0gZWxzZSB7XG4gICAgICAgIGNvbnNvbGUuZXJyb3IobXNnKTtcbiAgICAgIH1cbiAgICAgIHdhcm5lZCA9IHRydWU7XG4gICAgfVxuICAgIHJldHVybiBmbi5hcHBseSh0aGlzLCBhcmd1bWVudHMpO1xuICB9XG5cbiAgcmV0dXJuIGRlcHJlY2F0ZWQ7XG59O1xuXG5cbnZhciBkZWJ1Z3MgPSB7fTtcbnZhciBkZWJ1Z0Vudmlyb247XG5leHBvcnRzLmRlYnVnbG9nID0gZnVuY3Rpb24oc2V0KSB7XG4gIGlmIChpc1VuZGVmaW5lZChkZWJ1Z0Vudmlyb24pKVxuICAgIGRlYnVnRW52aXJvbiA9IHByb2Nlc3MuZW52Lk5PREVfREVCVUcgfHwgJyc7XG4gIHNldCA9IHNldC50b1VwcGVyQ2FzZSgpO1xuICBpZiAoIWRlYnVnc1tzZXRdKSB7XG4gICAgaWYgKG5ldyBSZWdFeHAoJ1xcXFxiJyArIHNldCArICdcXFxcYicsICdpJykudGVzdChkZWJ1Z0Vudmlyb24pKSB7XG4gICAgICB2YXIgcGlkID0gcHJvY2Vzcy5waWQ7XG4gICAgICBkZWJ1Z3Nbc2V0XSA9IGZ1bmN0aW9uKCkge1xuICAgICAgICB2YXIgbXNnID0gZXhwb3J0cy5mb3JtYXQuYXBwbHkoZXhwb3J0cywgYXJndW1lbnRzKTtcbiAgICAgICAgY29uc29sZS5lcnJvcignJXMgJWQ6ICVzJywgc2V0LCBwaWQsIG1zZyk7XG4gICAgICB9O1xuICAgIH0gZWxzZSB7XG4gICAgICBkZWJ1Z3Nbc2V0XSA9IGZ1bmN0aW9uKCkge307XG4gICAgfVxuICB9XG4gIHJldHVybiBkZWJ1Z3Nbc2V0XTtcbn07XG5cblxuLyoqXG4gKiBFY2hvcyB0aGUgdmFsdWUgb2YgYSB2YWx1ZS4gVHJ5cyB0byBwcmludCB0aGUgdmFsdWUgb3V0XG4gKiBpbiB0aGUgYmVzdCB3YXkgcG9zc2libGUgZ2l2ZW4gdGhlIGRpZmZlcmVudCB0eXBlcy5cbiAqXG4gKiBAcGFyYW0ge09iamVjdH0gb2JqIFRoZSBvYmplY3QgdG8gcHJpbnQgb3V0LlxuICogQHBhcmFtIHtPYmplY3R9IG9wdHMgT3B0aW9uYWwgb3B0aW9ucyBvYmplY3QgdGhhdCBhbHRlcnMgdGhlIG91dHB1dC5cbiAqL1xuLyogbGVnYWN5OiBvYmosIHNob3dIaWRkZW4sIGRlcHRoLCBjb2xvcnMqL1xuZnVuY3Rpb24gaW5zcGVjdChvYmosIG9wdHMpIHtcbiAgLy8gZGVmYXVsdCBvcHRpb25zXG4gIHZhciBjdHggPSB7XG4gICAgc2VlbjogW10sXG4gICAgc3R5bGl6ZTogc3R5bGl6ZU5vQ29sb3JcbiAgfTtcbiAgLy8gbGVnYWN5Li4uXG4gIGlmIChhcmd1bWVudHMubGVuZ3RoID49IDMpIGN0eC5kZXB0aCA9IGFyZ3VtZW50c1syXTtcbiAgaWYgKGFyZ3VtZW50cy5sZW5ndGggPj0gNCkgY3R4LmNvbG9ycyA9IGFyZ3VtZW50c1szXTtcbiAgaWYgKGlzQm9vbGVhbihvcHRzKSkge1xuICAgIC8vIGxlZ2FjeS4uLlxuICAgIGN0eC5zaG93SGlkZGVuID0gb3B0cztcbiAgfSBlbHNlIGlmIChvcHRzKSB7XG4gICAgLy8gZ290IGFuIFwib3B0aW9uc1wiIG9iamVjdFxuICAgIGV4cG9ydHMuX2V4dGVuZChjdHgsIG9wdHMpO1xuICB9XG4gIC8vIHNldCBkZWZhdWx0IG9wdGlvbnNcbiAgaWYgKGlzVW5kZWZpbmVkKGN0eC5zaG93SGlkZGVuKSkgY3R4LnNob3dIaWRkZW4gPSBmYWxzZTtcbiAgaWYgKGlzVW5kZWZpbmVkKGN0eC5kZXB0aCkpIGN0eC5kZXB0aCA9IDI7XG4gIGlmIChpc1VuZGVmaW5lZChjdHguY29sb3JzKSkgY3R4LmNvbG9ycyA9IGZhbHNlO1xuICBpZiAoaXNVbmRlZmluZWQoY3R4LmN1c3RvbUluc3BlY3QpKSBjdHguY3VzdG9tSW5zcGVjdCA9IHRydWU7XG4gIGlmIChjdHguY29sb3JzKSBjdHguc3R5bGl6ZSA9IHN0eWxpemVXaXRoQ29sb3I7XG4gIHJldHVybiBmb3JtYXRWYWx1ZShjdHgsIG9iaiwgY3R4LmRlcHRoKTtcbn1cbmV4cG9ydHMuaW5zcGVjdCA9IGluc3BlY3Q7XG5cblxuLy8gaHR0cDovL2VuLndpa2lwZWRpYS5vcmcvd2lraS9BTlNJX2VzY2FwZV9jb2RlI2dyYXBoaWNzXG5pbnNwZWN0LmNvbG9ycyA9IHtcbiAgJ2JvbGQnIDogWzEsIDIyXSxcbiAgJ2l0YWxpYycgOiBbMywgMjNdLFxuICAndW5kZXJsaW5lJyA6IFs0LCAyNF0sXG4gICdpbnZlcnNlJyA6IFs3LCAyN10sXG4gICd3aGl0ZScgOiBbMzcsIDM5XSxcbiAgJ2dyZXknIDogWzkwLCAzOV0sXG4gICdibGFjaycgOiBbMzAsIDM5XSxcbiAgJ2JsdWUnIDogWzM0LCAzOV0sXG4gICdjeWFuJyA6IFszNiwgMzldLFxuICAnZ3JlZW4nIDogWzMyLCAzOV0sXG4gICdtYWdlbnRhJyA6IFszNSwgMzldLFxuICAncmVkJyA6IFszMSwgMzldLFxuICAneWVsbG93JyA6IFszMywgMzldXG59O1xuXG4vLyBEb24ndCB1c2UgJ2JsdWUnIG5vdCB2aXNpYmxlIG9uIGNtZC5leGVcbmluc3BlY3Quc3R5bGVzID0ge1xuICAnc3BlY2lhbCc6ICdjeWFuJyxcbiAgJ251bWJlcic6ICd5ZWxsb3cnLFxuICAnYm9vbGVhbic6ICd5ZWxsb3cnLFxuICAndW5kZWZpbmVkJzogJ2dyZXknLFxuICAnbnVsbCc6ICdib2xkJyxcbiAgJ3N0cmluZyc6ICdncmVlbicsXG4gICdkYXRlJzogJ21hZ2VudGEnLFxuICAvLyBcIm5hbWVcIjogaW50ZW50aW9uYWxseSBub3Qgc3R5bGluZ1xuICAncmVnZXhwJzogJ3JlZCdcbn07XG5cblxuZnVuY3Rpb24gc3R5bGl6ZVdpdGhDb2xvcihzdHIsIHN0eWxlVHlwZSkge1xuICB2YXIgc3R5bGUgPSBpbnNwZWN0LnN0eWxlc1tzdHlsZVR5cGVdO1xuXG4gIGlmIChzdHlsZSkge1xuICAgIHJldHVybiAnXFx1MDAxYlsnICsgaW5zcGVjdC5jb2xvcnNbc3R5bGVdWzBdICsgJ20nICsgc3RyICtcbiAgICAgICAgICAgJ1xcdTAwMWJbJyArIGluc3BlY3QuY29sb3JzW3N0eWxlXVsxXSArICdtJztcbiAgfSBlbHNlIHtcbiAgICByZXR1cm4gc3RyO1xuICB9XG59XG5cblxuZnVuY3Rpb24gc3R5bGl6ZU5vQ29sb3Ioc3RyLCBzdHlsZVR5cGUpIHtcbiAgcmV0dXJuIHN0cjtcbn1cblxuXG5mdW5jdGlvbiBhcnJheVRvSGFzaChhcnJheSkge1xuICB2YXIgaGFzaCA9IHt9O1xuXG4gIGFycmF5LmZvckVhY2goZnVuY3Rpb24odmFsLCBpZHgpIHtcbiAgICBoYXNoW3ZhbF0gPSB0cnVlO1xuICB9KTtcblxuICByZXR1cm4gaGFzaDtcbn1cblxuXG5mdW5jdGlvbiBmb3JtYXRWYWx1ZShjdHgsIHZhbHVlLCByZWN1cnNlVGltZXMpIHtcbiAgLy8gUHJvdmlkZSBhIGhvb2sgZm9yIHVzZXItc3BlY2lmaWVkIGluc3BlY3QgZnVuY3Rpb25zLlxuICAvLyBDaGVjayB0aGF0IHZhbHVlIGlzIGFuIG9iamVjdCB3aXRoIGFuIGluc3BlY3QgZnVuY3Rpb24gb24gaXRcbiAgaWYgKGN0eC5jdXN0b21JbnNwZWN0ICYmXG4gICAgICB2YWx1ZSAmJlxuICAgICAgaXNGdW5jdGlvbih2YWx1ZS5pbnNwZWN0KSAmJlxuICAgICAgLy8gRmlsdGVyIG91dCB0aGUgdXRpbCBtb2R1bGUsIGl0J3MgaW5zcGVjdCBmdW5jdGlvbiBpcyBzcGVjaWFsXG4gICAgICB2YWx1ZS5pbnNwZWN0ICE9PSBleHBvcnRzLmluc3BlY3QgJiZcbiAgICAgIC8vIEFsc28gZmlsdGVyIG91dCBhbnkgcHJvdG90eXBlIG9iamVjdHMgdXNpbmcgdGhlIGNpcmN1bGFyIGNoZWNrLlxuICAgICAgISh2YWx1ZS5jb25zdHJ1Y3RvciAmJiB2YWx1ZS5jb25zdHJ1Y3Rvci5wcm90b3R5cGUgPT09IHZhbHVlKSkge1xuICAgIHZhciByZXQgPSB2YWx1ZS5pbnNwZWN0KHJlY3Vyc2VUaW1lcywgY3R4KTtcbiAgICBpZiAoIWlzU3RyaW5nKHJldCkpIHtcbiAgICAgIHJldCA9IGZvcm1hdFZhbHVlKGN0eCwgcmV0LCByZWN1cnNlVGltZXMpO1xuICAgIH1cbiAgICByZXR1cm4gcmV0O1xuICB9XG5cbiAgLy8gUHJpbWl0aXZlIHR5cGVzIGNhbm5vdCBoYXZlIHByb3BlcnRpZXNcbiAgdmFyIHByaW1pdGl2ZSA9IGZvcm1hdFByaW1pdGl2ZShjdHgsIHZhbHVlKTtcbiAgaWYgKHByaW1pdGl2ZSkge1xuICAgIHJldHVybiBwcmltaXRpdmU7XG4gIH1cblxuICAvLyBMb29rIHVwIHRoZSBrZXlzIG9mIHRoZSBvYmplY3QuXG4gIHZhciBrZXlzID0gT2JqZWN0LmtleXModmFsdWUpO1xuICB2YXIgdmlzaWJsZUtleXMgPSBhcnJheVRvSGFzaChrZXlzKTtcblxuICBpZiAoY3R4LnNob3dIaWRkZW4pIHtcbiAgICBrZXlzID0gT2JqZWN0LmdldE93blByb3BlcnR5TmFtZXModmFsdWUpO1xuICB9XG5cbiAgLy8gSUUgZG9lc24ndCBtYWtlIGVycm9yIGZpZWxkcyBub24tZW51bWVyYWJsZVxuICAvLyBodHRwOi8vbXNkbi5taWNyb3NvZnQuY29tL2VuLXVzL2xpYnJhcnkvaWUvZHd3NTJzYnQodj12cy45NCkuYXNweFxuICBpZiAoaXNFcnJvcih2YWx1ZSlcbiAgICAgICYmIChrZXlzLmluZGV4T2YoJ21lc3NhZ2UnKSA+PSAwIHx8IGtleXMuaW5kZXhPZignZGVzY3JpcHRpb24nKSA+PSAwKSkge1xuICAgIHJldHVybiBmb3JtYXRFcnJvcih2YWx1ZSk7XG4gIH1cblxuICAvLyBTb21lIHR5cGUgb2Ygb2JqZWN0IHdpdGhvdXQgcHJvcGVydGllcyBjYW4gYmUgc2hvcnRjdXR0ZWQuXG4gIGlmIChrZXlzLmxlbmd0aCA9PT0gMCkge1xuICAgIGlmIChpc0Z1bmN0aW9uKHZhbHVlKSkge1xuICAgICAgdmFyIG5hbWUgPSB2YWx1ZS5uYW1lID8gJzogJyArIHZhbHVlLm5hbWUgOiAnJztcbiAgICAgIHJldHVybiBjdHguc3R5bGl6ZSgnW0Z1bmN0aW9uJyArIG5hbWUgKyAnXScsICdzcGVjaWFsJyk7XG4gICAgfVxuICAgIGlmIChpc1JlZ0V4cCh2YWx1ZSkpIHtcbiAgICAgIHJldHVybiBjdHguc3R5bGl6ZShSZWdFeHAucHJvdG90eXBlLnRvU3RyaW5nLmNhbGwodmFsdWUpLCAncmVnZXhwJyk7XG4gICAgfVxuICAgIGlmIChpc0RhdGUodmFsdWUpKSB7XG4gICAgICByZXR1cm4gY3R4LnN0eWxpemUoRGF0ZS5wcm90b3R5cGUudG9TdHJpbmcuY2FsbCh2YWx1ZSksICdkYXRlJyk7XG4gICAgfVxuICAgIGlmIChpc0Vycm9yKHZhbHVlKSkge1xuICAgICAgcmV0dXJuIGZvcm1hdEVycm9yKHZhbHVlKTtcbiAgICB9XG4gIH1cblxuICB2YXIgYmFzZSA9ICcnLCBhcnJheSA9IGZhbHNlLCBicmFjZXMgPSBbJ3snLCAnfSddO1xuXG4gIC8vIE1ha2UgQXJyYXkgc2F5IHRoYXQgdGhleSBhcmUgQXJyYXlcbiAgaWYgKGlzQXJyYXkodmFsdWUpKSB7XG4gICAgYXJyYXkgPSB0cnVlO1xuICAgIGJyYWNlcyA9IFsnWycsICddJ107XG4gIH1cblxuICAvLyBNYWtlIGZ1bmN0aW9ucyBzYXkgdGhhdCB0aGV5IGFyZSBmdW5jdGlvbnNcbiAgaWYgKGlzRnVuY3Rpb24odmFsdWUpKSB7XG4gICAgdmFyIG4gPSB2YWx1ZS5uYW1lID8gJzogJyArIHZhbHVlLm5hbWUgOiAnJztcbiAgICBiYXNlID0gJyBbRnVuY3Rpb24nICsgbiArICddJztcbiAgfVxuXG4gIC8vIE1ha2UgUmVnRXhwcyBzYXkgdGhhdCB0aGV5IGFyZSBSZWdFeHBzXG4gIGlmIChpc1JlZ0V4cCh2YWx1ZSkpIHtcbiAgICBiYXNlID0gJyAnICsgUmVnRXhwLnByb3RvdHlwZS50b1N0cmluZy5jYWxsKHZhbHVlKTtcbiAgfVxuXG4gIC8vIE1ha2UgZGF0ZXMgd2l0aCBwcm9wZXJ0aWVzIGZpcnN0IHNheSB0aGUgZGF0ZVxuICBpZiAoaXNEYXRlKHZhbHVlKSkge1xuICAgIGJhc2UgPSAnICcgKyBEYXRlLnByb3RvdHlwZS50b1VUQ1N0cmluZy5jYWxsKHZhbHVlKTtcbiAgfVxuXG4gIC8vIE1ha2UgZXJyb3Igd2l0aCBtZXNzYWdlIGZpcnN0IHNheSB0aGUgZXJyb3JcbiAgaWYgKGlzRXJyb3IodmFsdWUpKSB7XG4gICAgYmFzZSA9ICcgJyArIGZvcm1hdEVycm9yKHZhbHVlKTtcbiAgfVxuXG4gIGlmIChrZXlzLmxlbmd0aCA9PT0gMCAmJiAoIWFycmF5IHx8IHZhbHVlLmxlbmd0aCA9PSAwKSkge1xuICAgIHJldHVybiBicmFjZXNbMF0gKyBiYXNlICsgYnJhY2VzWzFdO1xuICB9XG5cbiAgaWYgKHJlY3Vyc2VUaW1lcyA8IDApIHtcbiAgICBpZiAoaXNSZWdFeHAodmFsdWUpKSB7XG4gICAgICByZXR1cm4gY3R4LnN0eWxpemUoUmVnRXhwLnByb3RvdHlwZS50b1N0cmluZy5jYWxsKHZhbHVlKSwgJ3JlZ2V4cCcpO1xuICAgIH0gZWxzZSB7XG4gICAgICByZXR1cm4gY3R4LnN0eWxpemUoJ1tPYmplY3RdJywgJ3NwZWNpYWwnKTtcbiAgICB9XG4gIH1cblxuICBjdHguc2Vlbi5wdXNoKHZhbHVlKTtcblxuICB2YXIgb3V0cHV0O1xuICBpZiAoYXJyYXkpIHtcbiAgICBvdXRwdXQgPSBmb3JtYXRBcnJheShjdHgsIHZhbHVlLCByZWN1cnNlVGltZXMsIHZpc2libGVLZXlzLCBrZXlzKTtcbiAgfSBlbHNlIHtcbiAgICBvdXRwdXQgPSBrZXlzLm1hcChmdW5jdGlvbihrZXkpIHtcbiAgICAgIHJldHVybiBmb3JtYXRQcm9wZXJ0eShjdHgsIHZhbHVlLCByZWN1cnNlVGltZXMsIHZpc2libGVLZXlzLCBrZXksIGFycmF5KTtcbiAgICB9KTtcbiAgfVxuXG4gIGN0eC5zZWVuLnBvcCgpO1xuXG4gIHJldHVybiByZWR1Y2VUb1NpbmdsZVN0cmluZyhvdXRwdXQsIGJhc2UsIGJyYWNlcyk7XG59XG5cblxuZnVuY3Rpb24gZm9ybWF0UHJpbWl0aXZlKGN0eCwgdmFsdWUpIHtcbiAgaWYgKGlzVW5kZWZpbmVkKHZhbHVlKSlcbiAgICByZXR1cm4gY3R4LnN0eWxpemUoJ3VuZGVmaW5lZCcsICd1bmRlZmluZWQnKTtcbiAgaWYgKGlzU3RyaW5nKHZhbHVlKSkge1xuICAgIHZhciBzaW1wbGUgPSAnXFwnJyArIEpTT04uc3RyaW5naWZ5KHZhbHVlKS5yZXBsYWNlKC9eXCJ8XCIkL2csICcnKVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgLnJlcGxhY2UoLycvZywgXCJcXFxcJ1wiKVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgLnJlcGxhY2UoL1xcXFxcIi9nLCAnXCInKSArICdcXCcnO1xuICAgIHJldHVybiBjdHguc3R5bGl6ZShzaW1wbGUsICdzdHJpbmcnKTtcbiAgfVxuICBpZiAoaXNOdW1iZXIodmFsdWUpKVxuICAgIHJldHVybiBjdHguc3R5bGl6ZSgnJyArIHZhbHVlLCAnbnVtYmVyJyk7XG4gIGlmIChpc0Jvb2xlYW4odmFsdWUpKVxuICAgIHJldHVybiBjdHguc3R5bGl6ZSgnJyArIHZhbHVlLCAnYm9vbGVhbicpO1xuICAvLyBGb3Igc29tZSByZWFzb24gdHlwZW9mIG51bGwgaXMgXCJvYmplY3RcIiwgc28gc3BlY2lhbCBjYXNlIGhlcmUuXG4gIGlmIChpc051bGwodmFsdWUpKVxuICAgIHJldHVybiBjdHguc3R5bGl6ZSgnbnVsbCcsICdudWxsJyk7XG59XG5cblxuZnVuY3Rpb24gZm9ybWF0RXJyb3IodmFsdWUpIHtcbiAgcmV0dXJuICdbJyArIEVycm9yLnByb3RvdHlwZS50b1N0cmluZy5jYWxsKHZhbHVlKSArICddJztcbn1cblxuXG5mdW5jdGlvbiBmb3JtYXRBcnJheShjdHgsIHZhbHVlLCByZWN1cnNlVGltZXMsIHZpc2libGVLZXlzLCBrZXlzKSB7XG4gIHZhciBvdXRwdXQgPSBbXTtcbiAgZm9yICh2YXIgaSA9IDAsIGwgPSB2YWx1ZS5sZW5ndGg7IGkgPCBsOyArK2kpIHtcbiAgICBpZiAoaGFzT3duUHJvcGVydHkodmFsdWUsIFN0cmluZyhpKSkpIHtcbiAgICAgIG91dHB1dC5wdXNoKGZvcm1hdFByb3BlcnR5KGN0eCwgdmFsdWUsIHJlY3Vyc2VUaW1lcywgdmlzaWJsZUtleXMsXG4gICAgICAgICAgU3RyaW5nKGkpLCB0cnVlKSk7XG4gICAgfSBlbHNlIHtcbiAgICAgIG91dHB1dC5wdXNoKCcnKTtcbiAgICB9XG4gIH1cbiAga2V5cy5mb3JFYWNoKGZ1bmN0aW9uKGtleSkge1xuICAgIGlmICgha2V5Lm1hdGNoKC9eXFxkKyQvKSkge1xuICAgICAgb3V0cHV0LnB1c2goZm9ybWF0UHJvcGVydHkoY3R4LCB2YWx1ZSwgcmVjdXJzZVRpbWVzLCB2aXNpYmxlS2V5cyxcbiAgICAgICAgICBrZXksIHRydWUpKTtcbiAgICB9XG4gIH0pO1xuICByZXR1cm4gb3V0cHV0O1xufVxuXG5cbmZ1bmN0aW9uIGZvcm1hdFByb3BlcnR5KGN0eCwgdmFsdWUsIHJlY3Vyc2VUaW1lcywgdmlzaWJsZUtleXMsIGtleSwgYXJyYXkpIHtcbiAgdmFyIG5hbWUsIHN0ciwgZGVzYztcbiAgZGVzYyA9IE9iamVjdC5nZXRPd25Qcm9wZXJ0eURlc2NyaXB0b3IodmFsdWUsIGtleSkgfHwgeyB2YWx1ZTogdmFsdWVba2V5XSB9O1xuICBpZiAoZGVzYy5nZXQpIHtcbiAgICBpZiAoZGVzYy5zZXQpIHtcbiAgICAgIHN0ciA9IGN0eC5zdHlsaXplKCdbR2V0dGVyL1NldHRlcl0nLCAnc3BlY2lhbCcpO1xuICAgIH0gZWxzZSB7XG4gICAgICBzdHIgPSBjdHguc3R5bGl6ZSgnW0dldHRlcl0nLCAnc3BlY2lhbCcpO1xuICAgIH1cbiAgfSBlbHNlIHtcbiAgICBpZiAoZGVzYy5zZXQpIHtcbiAgICAgIHN0ciA9IGN0eC5zdHlsaXplKCdbU2V0dGVyXScsICdzcGVjaWFsJyk7XG4gICAgfVxuICB9XG4gIGlmICghaGFzT3duUHJvcGVydHkodmlzaWJsZUtleXMsIGtleSkpIHtcbiAgICBuYW1lID0gJ1snICsga2V5ICsgJ10nO1xuICB9XG4gIGlmICghc3RyKSB7XG4gICAgaWYgKGN0eC5zZWVuLmluZGV4T2YoZGVzYy52YWx1ZSkgPCAwKSB7XG4gICAgICBpZiAoaXNOdWxsKHJlY3Vyc2VUaW1lcykpIHtcbiAgICAgICAgc3RyID0gZm9ybWF0VmFsdWUoY3R4LCBkZXNjLnZhbHVlLCBudWxsKTtcbiAgICAgIH0gZWxzZSB7XG4gICAgICAgIHN0ciA9IGZvcm1hdFZhbHVlKGN0eCwgZGVzYy52YWx1ZSwgcmVjdXJzZVRpbWVzIC0gMSk7XG4gICAgICB9XG4gICAgICBpZiAoc3RyLmluZGV4T2YoJ1xcbicpID4gLTEpIHtcbiAgICAgICAgaWYgKGFycmF5KSB7XG4gICAgICAgICAgc3RyID0gc3RyLnNwbGl0KCdcXG4nKS5tYXAoZnVuY3Rpb24obGluZSkge1xuICAgICAgICAgICAgcmV0dXJuICcgICcgKyBsaW5lO1xuICAgICAgICAgIH0pLmpvaW4oJ1xcbicpLnN1YnN0cigyKTtcbiAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICBzdHIgPSAnXFxuJyArIHN0ci5zcGxpdCgnXFxuJykubWFwKGZ1bmN0aW9uKGxpbmUpIHtcbiAgICAgICAgICAgIHJldHVybiAnICAgJyArIGxpbmU7XG4gICAgICAgICAgfSkuam9pbignXFxuJyk7XG4gICAgICAgIH1cbiAgICAgIH1cbiAgICB9IGVsc2Uge1xuICAgICAgc3RyID0gY3R4LnN0eWxpemUoJ1tDaXJjdWxhcl0nLCAnc3BlY2lhbCcpO1xuICAgIH1cbiAgfVxuICBpZiAoaXNVbmRlZmluZWQobmFtZSkpIHtcbiAgICBpZiAoYXJyYXkgJiYga2V5Lm1hdGNoKC9eXFxkKyQvKSkge1xuICAgICAgcmV0dXJuIHN0cjtcbiAgICB9XG4gICAgbmFtZSA9IEpTT04uc3RyaW5naWZ5KCcnICsga2V5KTtcbiAgICBpZiAobmFtZS5tYXRjaCgvXlwiKFthLXpBLVpfXVthLXpBLVpfMC05XSopXCIkLykpIHtcbiAgICAgIG5hbWUgPSBuYW1lLnN1YnN0cigxLCBuYW1lLmxlbmd0aCAtIDIpO1xuICAgICAgbmFtZSA9IGN0eC5zdHlsaXplKG5hbWUsICduYW1lJyk7XG4gICAgfSBlbHNlIHtcbiAgICAgIG5hbWUgPSBuYW1lLnJlcGxhY2UoLycvZywgXCJcXFxcJ1wiKVxuICAgICAgICAgICAgICAgICAucmVwbGFjZSgvXFxcXFwiL2csICdcIicpXG4gICAgICAgICAgICAgICAgIC5yZXBsYWNlKC8oXlwifFwiJCkvZywgXCInXCIpO1xuICAgICAgbmFtZSA9IGN0eC5zdHlsaXplKG5hbWUsICdzdHJpbmcnKTtcbiAgICB9XG4gIH1cblxuICByZXR1cm4gbmFtZSArICc6ICcgKyBzdHI7XG59XG5cblxuZnVuY3Rpb24gcmVkdWNlVG9TaW5nbGVTdHJpbmcob3V0cHV0LCBiYXNlLCBicmFjZXMpIHtcbiAgdmFyIG51bUxpbmVzRXN0ID0gMDtcbiAgdmFyIGxlbmd0aCA9IG91dHB1dC5yZWR1Y2UoZnVuY3Rpb24ocHJldiwgY3VyKSB7XG4gICAgbnVtTGluZXNFc3QrKztcbiAgICBpZiAoY3VyLmluZGV4T2YoJ1xcbicpID49IDApIG51bUxpbmVzRXN0Kys7XG4gICAgcmV0dXJuIHByZXYgKyBjdXIucmVwbGFjZSgvXFx1MDAxYlxcW1xcZFxcZD9tL2csICcnKS5sZW5ndGggKyAxO1xuICB9LCAwKTtcblxuICBpZiAobGVuZ3RoID4gNjApIHtcbiAgICByZXR1cm4gYnJhY2VzWzBdICtcbiAgICAgICAgICAgKGJhc2UgPT09ICcnID8gJycgOiBiYXNlICsgJ1xcbiAnKSArXG4gICAgICAgICAgICcgJyArXG4gICAgICAgICAgIG91dHB1dC5qb2luKCcsXFxuICAnKSArXG4gICAgICAgICAgICcgJyArXG4gICAgICAgICAgIGJyYWNlc1sxXTtcbiAgfVxuXG4gIHJldHVybiBicmFjZXNbMF0gKyBiYXNlICsgJyAnICsgb3V0cHV0LmpvaW4oJywgJykgKyAnICcgKyBicmFjZXNbMV07XG59XG5cblxuLy8gTk9URTogVGhlc2UgdHlwZSBjaGVja2luZyBmdW5jdGlvbnMgaW50ZW50aW9uYWxseSBkb24ndCB1c2UgYGluc3RhbmNlb2ZgXG4vLyBiZWNhdXNlIGl0IGlzIGZyYWdpbGUgYW5kIGNhbiBiZSBlYXNpbHkgZmFrZWQgd2l0aCBgT2JqZWN0LmNyZWF0ZSgpYC5cbmZ1bmN0aW9uIGlzQXJyYXkoYXIpIHtcbiAgcmV0dXJuIEFycmF5LmlzQXJyYXkoYXIpO1xufVxuZXhwb3J0cy5pc0FycmF5ID0gaXNBcnJheTtcblxuZnVuY3Rpb24gaXNCb29sZWFuKGFyZykge1xuICByZXR1cm4gdHlwZW9mIGFyZyA9PT0gJ2Jvb2xlYW4nO1xufVxuZXhwb3J0cy5pc0Jvb2xlYW4gPSBpc0Jvb2xlYW47XG5cbmZ1bmN0aW9uIGlzTnVsbChhcmcpIHtcbiAgcmV0dXJuIGFyZyA9PT0gbnVsbDtcbn1cbmV4cG9ydHMuaXNOdWxsID0gaXNOdWxsO1xuXG5mdW5jdGlvbiBpc051bGxPclVuZGVmaW5lZChhcmcpIHtcbiAgcmV0dXJuIGFyZyA9PSBudWxsO1xufVxuZXhwb3J0cy5pc051bGxPclVuZGVmaW5lZCA9IGlzTnVsbE9yVW5kZWZpbmVkO1xuXG5mdW5jdGlvbiBpc051bWJlcihhcmcpIHtcbiAgcmV0dXJuIHR5cGVvZiBhcmcgPT09ICdudW1iZXInO1xufVxuZXhwb3J0cy5pc051bWJlciA9IGlzTnVtYmVyO1xuXG5mdW5jdGlvbiBpc1N0cmluZyhhcmcpIHtcbiAgcmV0dXJuIHR5cGVvZiBhcmcgPT09ICdzdHJpbmcnO1xufVxuZXhwb3J0cy5pc1N0cmluZyA9IGlzU3RyaW5nO1xuXG5mdW5jdGlvbiBpc1N5bWJvbChhcmcpIHtcbiAgcmV0dXJuIHR5cGVvZiBhcmcgPT09ICdzeW1ib2wnO1xufVxuZXhwb3J0cy5pc1N5bWJvbCA9IGlzU3ltYm9sO1xuXG5mdW5jdGlvbiBpc1VuZGVmaW5lZChhcmcpIHtcbiAgcmV0dXJuIGFyZyA9PT0gdm9pZCAwO1xufVxuZXhwb3J0cy5pc1VuZGVmaW5lZCA9IGlzVW5kZWZpbmVkO1xuXG5mdW5jdGlvbiBpc1JlZ0V4cChyZSkge1xuICByZXR1cm4gaXNPYmplY3QocmUpICYmIG9iamVjdFRvU3RyaW5nKHJlKSA9PT0gJ1tvYmplY3QgUmVnRXhwXSc7XG59XG5leHBvcnRzLmlzUmVnRXhwID0gaXNSZWdFeHA7XG5cbmZ1bmN0aW9uIGlzT2JqZWN0KGFyZykge1xuICByZXR1cm4gdHlwZW9mIGFyZyA9PT0gJ29iamVjdCcgJiYgYXJnICE9PSBudWxsO1xufVxuZXhwb3J0cy5pc09iamVjdCA9IGlzT2JqZWN0O1xuXG5mdW5jdGlvbiBpc0RhdGUoZCkge1xuICByZXR1cm4gaXNPYmplY3QoZCkgJiYgb2JqZWN0VG9TdHJpbmcoZCkgPT09ICdbb2JqZWN0IERhdGVdJztcbn1cbmV4cG9ydHMuaXNEYXRlID0gaXNEYXRlO1xuXG5mdW5jdGlvbiBpc0Vycm9yKGUpIHtcbiAgcmV0dXJuIGlzT2JqZWN0KGUpICYmXG4gICAgICAob2JqZWN0VG9TdHJpbmcoZSkgPT09ICdbb2JqZWN0IEVycm9yXScgfHwgZSBpbnN0YW5jZW9mIEVycm9yKTtcbn1cbmV4cG9ydHMuaXNFcnJvciA9IGlzRXJyb3I7XG5cbmZ1bmN0aW9uIGlzRnVuY3Rpb24oYXJnKSB7XG4gIHJldHVybiB0eXBlb2YgYXJnID09PSAnZnVuY3Rpb24nO1xufVxuZXhwb3J0cy5pc0Z1bmN0aW9uID0gaXNGdW5jdGlvbjtcblxuZnVuY3Rpb24gaXNQcmltaXRpdmUoYXJnKSB7XG4gIHJldHVybiBhcmcgPT09IG51bGwgfHxcbiAgICAgICAgIHR5cGVvZiBhcmcgPT09ICdib29sZWFuJyB8fFxuICAgICAgICAgdHlwZW9mIGFyZyA9PT0gJ251bWJlcicgfHxcbiAgICAgICAgIHR5cGVvZiBhcmcgPT09ICdzdHJpbmcnIHx8XG4gICAgICAgICB0eXBlb2YgYXJnID09PSAnc3ltYm9sJyB8fCAgLy8gRVM2IHN5bWJvbFxuICAgICAgICAgdHlwZW9mIGFyZyA9PT0gJ3VuZGVmaW5lZCc7XG59XG5leHBvcnRzLmlzUHJpbWl0aXZlID0gaXNQcmltaXRpdmU7XG5cbmV4cG9ydHMuaXNCdWZmZXIgPSBfZGVyZXFfKCcuL3N1cHBvcnQvaXNCdWZmZXInKTtcblxuZnVuY3Rpb24gb2JqZWN0VG9TdHJpbmcobykge1xuICByZXR1cm4gT2JqZWN0LnByb3RvdHlwZS50b1N0cmluZy5jYWxsKG8pO1xufVxuXG5cbmZ1bmN0aW9uIHBhZChuKSB7XG4gIHJldHVybiBuIDwgMTAgPyAnMCcgKyBuLnRvU3RyaW5nKDEwKSA6IG4udG9TdHJpbmcoMTApO1xufVxuXG5cbnZhciBtb250aHMgPSBbJ0phbicsICdGZWInLCAnTWFyJywgJ0FwcicsICdNYXknLCAnSnVuJywgJ0p1bCcsICdBdWcnLCAnU2VwJyxcbiAgICAgICAgICAgICAgJ09jdCcsICdOb3YnLCAnRGVjJ107XG5cbi8vIDI2IEZlYiAxNjoxOTozNFxuZnVuY3Rpb24gdGltZXN0YW1wKCkge1xuICB2YXIgZCA9IG5ldyBEYXRlKCk7XG4gIHZhciB0aW1lID0gW3BhZChkLmdldEhvdXJzKCkpLFxuICAgICAgICAgICAgICBwYWQoZC5nZXRNaW51dGVzKCkpLFxuICAgICAgICAgICAgICBwYWQoZC5nZXRTZWNvbmRzKCkpXS5qb2luKCc6Jyk7XG4gIHJldHVybiBbZC5nZXREYXRlKCksIG1vbnRoc1tkLmdldE1vbnRoKCldLCB0aW1lXS5qb2luKCcgJyk7XG59XG5cblxuLy8gbG9nIGlzIGp1c3QgYSB0aGluIHdyYXBwZXIgdG8gY29uc29sZS5sb2cgdGhhdCBwcmVwZW5kcyBhIHRpbWVzdGFtcFxuZXhwb3J0cy5sb2cgPSBmdW5jdGlvbigpIHtcbiAgY29uc29sZS5sb2coJyVzIC0gJXMnLCB0aW1lc3RhbXAoKSwgZXhwb3J0cy5mb3JtYXQuYXBwbHkoZXhwb3J0cywgYXJndW1lbnRzKSk7XG59O1xuXG5cbi8qKlxuICogSW5oZXJpdCB0aGUgcHJvdG90eXBlIG1ldGhvZHMgZnJvbSBvbmUgY29uc3RydWN0b3IgaW50byBhbm90aGVyLlxuICpcbiAqIFRoZSBGdW5jdGlvbi5wcm90b3R5cGUuaW5oZXJpdHMgZnJvbSBsYW5nLmpzIHJld3JpdHRlbiBhcyBhIHN0YW5kYWxvbmVcbiAqIGZ1bmN0aW9uIChub3Qgb24gRnVuY3Rpb24ucHJvdG90eXBlKS4gTk9URTogSWYgdGhpcyBmaWxlIGlzIHRvIGJlIGxvYWRlZFxuICogZHVyaW5nIGJvb3RzdHJhcHBpbmcgdGhpcyBmdW5jdGlvbiBuZWVkcyB0byBiZSByZXdyaXR0ZW4gdXNpbmcgc29tZSBuYXRpdmVcbiAqIGZ1bmN0aW9ucyBhcyBwcm90b3R5cGUgc2V0dXAgdXNpbmcgbm9ybWFsIEphdmFTY3JpcHQgZG9lcyBub3Qgd29yayBhc1xuICogZXhwZWN0ZWQgZHVyaW5nIGJvb3RzdHJhcHBpbmcgKHNlZSBtaXJyb3IuanMgaW4gcjExNDkwMykuXG4gKlxuICogQHBhcmFtIHtmdW5jdGlvbn0gY3RvciBDb25zdHJ1Y3RvciBmdW5jdGlvbiB3aGljaCBuZWVkcyB0byBpbmhlcml0IHRoZVxuICogICAgIHByb3RvdHlwZS5cbiAqIEBwYXJhbSB7ZnVuY3Rpb259IHN1cGVyQ3RvciBDb25zdHJ1Y3RvciBmdW5jdGlvbiB0byBpbmhlcml0IHByb3RvdHlwZSBmcm9tLlxuICovXG5leHBvcnRzLmluaGVyaXRzID0gX2RlcmVxXygnaW5oZXJpdHMnKTtcblxuZXhwb3J0cy5fZXh0ZW5kID0gZnVuY3Rpb24ob3JpZ2luLCBhZGQpIHtcbiAgLy8gRG9uJ3QgZG8gYW55dGhpbmcgaWYgYWRkIGlzbid0IGFuIG9iamVjdFxuICBpZiAoIWFkZCB8fCAhaXNPYmplY3QoYWRkKSkgcmV0dXJuIG9yaWdpbjtcblxuICB2YXIga2V5cyA9IE9iamVjdC5rZXlzKGFkZCk7XG4gIHZhciBpID0ga2V5cy5sZW5ndGg7XG4gIHdoaWxlIChpLS0pIHtcbiAgICBvcmlnaW5ba2V5c1tpXV0gPSBhZGRba2V5c1tpXV07XG4gIH1cbiAgcmV0dXJuIG9yaWdpbjtcbn07XG5cbmZ1bmN0aW9uIGhhc093blByb3BlcnR5KG9iaiwgcHJvcCkge1xuICByZXR1cm4gT2JqZWN0LnByb3RvdHlwZS5oYXNPd25Qcm9wZXJ0eS5jYWxsKG9iaiwgcHJvcCk7XG59XG5cbn0pLmNhbGwodGhpcyxfZGVyZXFfKCdfcHJvY2VzcycpLHR5cGVvZiBnbG9iYWwgIT09IFwidW5kZWZpbmVkXCIgPyBnbG9iYWwgOiB0eXBlb2Ygc2VsZiAhPT0gXCJ1bmRlZmluZWRcIiA/IHNlbGYgOiB0eXBlb2Ygd2luZG93ICE9PSBcInVuZGVmaW5lZFwiID8gd2luZG93IDoge30pXG59LHtcIi4vc3VwcG9ydC9pc0J1ZmZlclwiOjQsXCJfcHJvY2Vzc1wiOjMsXCJpbmhlcml0c1wiOjJ9XSw2OltmdW5jdGlvbihfZGVyZXFfLG1vZHVsZSxleHBvcnRzKXtcbi8vIEEgcmVjdXJzaXZlIGRlc2NlbnQgcGFyc2VyIG9wZXJhdGVzIGJ5IGRlZmluaW5nIGZ1bmN0aW9ucyBmb3IgYWxsXG4vLyBzeW50YWN0aWMgZWxlbWVudHMsIGFuZCByZWN1cnNpdmVseSBjYWxsaW5nIHRob3NlLCBlYWNoIGZ1bmN0aW9uXG4vLyBhZHZhbmNpbmcgdGhlIGlucHV0IHN0cmVhbSBhbmQgcmV0dXJuaW5nIGFuIEFTVCBub2RlLiBQcmVjZWRlbmNlXG4vLyBvZiBjb25zdHJ1Y3RzIChmb3IgZXhhbXBsZSwgdGhlIGZhY3QgdGhhdCBgIXhbMV1gIG1lYW5zIGAhKHhbMV0pYFxuLy8gaW5zdGVhZCBvZiBgKCF4KVsxXWAgaXMgaGFuZGxlZCBieSB0aGUgZmFjdCB0aGF0IHRoZSBwYXJzZXJcbi8vIGZ1bmN0aW9uIHRoYXQgcGFyc2VzIHVuYXJ5IHByZWZpeCBvcGVyYXRvcnMgaXMgY2FsbGVkIGZpcnN0LCBhbmRcbi8vIGluIHR1cm4gY2FsbHMgdGhlIGZ1bmN0aW9uIHRoYXQgcGFyc2VzIGBbXWAgc3Vic2NyaXB0cyDigJQgdGhhdFxuLy8gd2F5LCBpdCdsbCByZWNlaXZlIHRoZSBub2RlIGZvciBgeFsxXWAgYWxyZWFkeSBwYXJzZWQsIGFuZCB3cmFwc1xuLy8gKnRoYXQqIGluIHRoZSB1bmFyeSBvcGVyYXRvciBub2RlLlxuLy9cbi8vIEFjb3JuIHVzZXMgYW4gW29wZXJhdG9yIHByZWNlZGVuY2UgcGFyc2VyXVtvcHBdIHRvIGhhbmRsZSBiaW5hcnlcbi8vIG9wZXJhdG9yIHByZWNlZGVuY2UsIGJlY2F1c2UgaXQgaXMgbXVjaCBtb3JlIGNvbXBhY3QgdGhhbiB1c2luZ1xuLy8gdGhlIHRlY2huaXF1ZSBvdXRsaW5lZCBhYm92ZSwgd2hpY2ggdXNlcyBkaWZmZXJlbnQsIG5lc3Rpbmdcbi8vIGZ1bmN0aW9ucyB0byBzcGVjaWZ5IHByZWNlZGVuY2UsIGZvciBhbGwgb2YgdGhlIHRlbiBiaW5hcnlcbi8vIHByZWNlZGVuY2UgbGV2ZWxzIHRoYXQgSmF2YVNjcmlwdCBkZWZpbmVzLlxuLy9cbi8vIFtvcHBdOiBodHRwOi8vZW4ud2lraXBlZGlhLm9yZy93aWtpL09wZXJhdG9yLXByZWNlZGVuY2VfcGFyc2VyXG5cblwidXNlIHN0cmljdFwiO1xuXG52YXIgdHQgPSBfZGVyZXFfKFwiLi90b2tlbnR5cGVcIikudHlwZXM7XG5cbnZhciBQYXJzZXIgPSBfZGVyZXFfKFwiLi9zdGF0ZVwiKS5QYXJzZXI7XG5cbnZhciByZXNlcnZlZFdvcmRzID0gX2RlcmVxXyhcIi4vaWRlbnRpZmllclwiKS5yZXNlcnZlZFdvcmRzO1xuXG52YXIgaGFzID0gX2RlcmVxXyhcIi4vdXRpbFwiKS5oYXM7XG5cbnZhciBwcCA9IFBhcnNlci5wcm90b3R5cGU7XG5cbi8vIENoZWNrIGlmIHByb3BlcnR5IG5hbWUgY2xhc2hlcyB3aXRoIGFscmVhZHkgYWRkZWQuXG4vLyBPYmplY3QvY2xhc3MgZ2V0dGVycyBhbmQgc2V0dGVycyBhcmUgbm90IGFsbG93ZWQgdG8gY2xhc2gg4oCUXG4vLyBlaXRoZXIgd2l0aCBlYWNoIG90aGVyIG9yIHdpdGggYW4gaW5pdCBwcm9wZXJ0eSDigJQgYW5kIGluXG4vLyBzdHJpY3QgbW9kZSwgaW5pdCBwcm9wZXJ0aWVzIGFyZSBhbHNvIG5vdCBhbGxvd2VkIHRvIGJlIHJlcGVhdGVkLlxuXG5wcC5jaGVja1Byb3BDbGFzaCA9IGZ1bmN0aW9uIChwcm9wLCBwcm9wSGFzaCkge1xuICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYpIHJldHVybjtcbiAgdmFyIGtleSA9IHByb3Aua2V5LFxuICAgICAgbmFtZSA9IHVuZGVmaW5lZDtcbiAgc3dpdGNoIChrZXkudHlwZSkge1xuICAgIGNhc2UgXCJJZGVudGlmaWVyXCI6XG4gICAgICBuYW1lID0ga2V5Lm5hbWU7YnJlYWs7XG4gICAgY2FzZSBcIkxpdGVyYWxcIjpcbiAgICAgIG5hbWUgPSBTdHJpbmcoa2V5LnZhbHVlKTticmVhaztcbiAgICBkZWZhdWx0OlxuICAgICAgcmV0dXJuO1xuICB9XG4gIHZhciBraW5kID0gcHJvcC5raW5kIHx8IFwiaW5pdFwiLFxuICAgICAgb3RoZXIgPSB1bmRlZmluZWQ7XG4gIGlmIChoYXMocHJvcEhhc2gsIG5hbWUpKSB7XG4gICAgb3RoZXIgPSBwcm9wSGFzaFtuYW1lXTtcbiAgICB2YXIgaXNHZXRTZXQgPSBraW5kICE9PSBcImluaXRcIjtcbiAgICBpZiAoKHRoaXMuc3RyaWN0IHx8IGlzR2V0U2V0KSAmJiBvdGhlcltraW5kXSB8fCAhKGlzR2V0U2V0IF4gb3RoZXIuaW5pdCkpIHRoaXMucmFpc2Uoa2V5LnN0YXJ0LCBcIlJlZGVmaW5pdGlvbiBvZiBwcm9wZXJ0eVwiKTtcbiAgfSBlbHNlIHtcbiAgICBvdGhlciA9IHByb3BIYXNoW25hbWVdID0ge1xuICAgICAgaW5pdDogZmFsc2UsXG4gICAgICBnZXQ6IGZhbHNlLFxuICAgICAgc2V0OiBmYWxzZVxuICAgIH07XG4gIH1cbiAgb3RoZXJba2luZF0gPSB0cnVlO1xufTtcblxuLy8gIyMjIEV4cHJlc3Npb24gcGFyc2luZ1xuXG4vLyBUaGVzZSBuZXN0LCBmcm9tIHRoZSBtb3N0IGdlbmVyYWwgZXhwcmVzc2lvbiB0eXBlIGF0IHRoZSB0b3AgdG9cbi8vICdhdG9taWMnLCBub25kaXZpc2libGUgZXhwcmVzc2lvbiB0eXBlcyBhdCB0aGUgYm90dG9tLiBNb3N0IG9mXG4vLyB0aGUgZnVuY3Rpb25zIHdpbGwgc2ltcGx5IGxldCB0aGUgZnVuY3Rpb24ocykgYmVsb3cgdGhlbSBwYXJzZSxcbi8vIGFuZCwgKmlmKiB0aGUgc3ludGFjdGljIGNvbnN0cnVjdCB0aGV5IGhhbmRsZSBpcyBwcmVzZW50LCB3cmFwXG4vLyB0aGUgQVNUIG5vZGUgdGhhdCB0aGUgaW5uZXIgcGFyc2VyIGdhdmUgdGhlbSBpbiBhbm90aGVyIG5vZGUuXG5cbi8vIFBhcnNlIGEgZnVsbCBleHByZXNzaW9uLiBUaGUgb3B0aW9uYWwgYXJndW1lbnRzIGFyZSB1c2VkIHRvXG4vLyBmb3JiaWQgdGhlIGBpbmAgb3BlcmF0b3IgKGluIGZvciBsb29wcyBpbml0YWxpemF0aW9uIGV4cHJlc3Npb25zKVxuLy8gYW5kIHByb3ZpZGUgcmVmZXJlbmNlIGZvciBzdG9yaW5nICc9JyBvcGVyYXRvciBpbnNpZGUgc2hvcnRoYW5kXG4vLyBwcm9wZXJ0eSBhc3NpZ25tZW50IGluIGNvbnRleHRzIHdoZXJlIGJvdGggb2JqZWN0IGV4cHJlc3Npb25cbi8vIGFuZCBvYmplY3QgcGF0dGVybiBtaWdodCBhcHBlYXIgKHNvIGl0J3MgcG9zc2libGUgdG8gcmFpc2Vcbi8vIGRlbGF5ZWQgc3ludGF4IGVycm9yIGF0IGNvcnJlY3QgcG9zaXRpb24pLlxuXG5wcC5wYXJzZUV4cHJlc3Npb24gPSBmdW5jdGlvbiAobm9JbiwgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcykge1xuICB2YXIgc3RhcnRQb3MgPSB0aGlzLnN0YXJ0LFxuICAgICAgc3RhcnRMb2MgPSB0aGlzLnN0YXJ0TG9jO1xuICB2YXIgZXhwciA9IHRoaXMucGFyc2VNYXliZUFzc2lnbihub0luLCByZWZTaG9ydGhhbmREZWZhdWx0UG9zKTtcbiAgaWYgKHRoaXMudHlwZSA9PT0gdHQuY29tbWEpIHtcbiAgICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlQXQoc3RhcnRQb3MsIHN0YXJ0TG9jKTtcbiAgICBub2RlLmV4cHJlc3Npb25zID0gW2V4cHJdO1xuICAgIHdoaWxlICh0aGlzLmVhdCh0dC5jb21tYSkpIG5vZGUuZXhwcmVzc2lvbnMucHVzaCh0aGlzLnBhcnNlTWF5YmVBc3NpZ24obm9JbiwgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcykpO1xuICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJTZXF1ZW5jZUV4cHJlc3Npb25cIik7XG4gIH1cbiAgcmV0dXJuIGV4cHI7XG59O1xuXG4vLyBQYXJzZSBhbiBhc3NpZ25tZW50IGV4cHJlc3Npb24uIFRoaXMgaW5jbHVkZXMgYXBwbGljYXRpb25zIG9mXG4vLyBvcGVyYXRvcnMgbGlrZSBgKz1gLlxuXG5wcC5wYXJzZU1heWJlQXNzaWduID0gZnVuY3Rpb24gKG5vSW4sIHJlZlNob3J0aGFuZERlZmF1bHRQb3MsIGFmdGVyTGVmdFBhcnNlKSB7XG4gIGlmICh0aGlzLnR5cGUgPT0gdHQuX3lpZWxkICYmIHRoaXMuaW5HZW5lcmF0b3IpIHJldHVybiB0aGlzLnBhcnNlWWllbGQoKTtcblxuICB2YXIgZmFpbE9uU2hvcnRoYW5kQXNzaWduID0gdW5kZWZpbmVkO1xuICBpZiAoIXJlZlNob3J0aGFuZERlZmF1bHRQb3MpIHtcbiAgICByZWZTaG9ydGhhbmREZWZhdWx0UG9zID0geyBzdGFydDogMCB9O1xuICAgIGZhaWxPblNob3J0aGFuZEFzc2lnbiA9IHRydWU7XG4gIH0gZWxzZSB7XG4gICAgZmFpbE9uU2hvcnRoYW5kQXNzaWduID0gZmFsc2U7XG4gIH1cbiAgdmFyIHN0YXJ0UG9zID0gdGhpcy5zdGFydCxcbiAgICAgIHN0YXJ0TG9jID0gdGhpcy5zdGFydExvYztcbiAgaWYgKHRoaXMudHlwZSA9PSB0dC5wYXJlbkwgfHwgdGhpcy50eXBlID09IHR0Lm5hbWUpIHRoaXMucG90ZW50aWFsQXJyb3dBdCA9IHRoaXMuc3RhcnQ7XG4gIHZhciBsZWZ0ID0gdGhpcy5wYXJzZU1heWJlQ29uZGl0aW9uYWwobm9JbiwgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcyk7XG4gIGlmIChhZnRlckxlZnRQYXJzZSkgbGVmdCA9IGFmdGVyTGVmdFBhcnNlLmNhbGwodGhpcywgbGVmdCwgc3RhcnRQb3MsIHN0YXJ0TG9jKTtcbiAgaWYgKHRoaXMudHlwZS5pc0Fzc2lnbikge1xuICAgIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGVBdChzdGFydFBvcywgc3RhcnRMb2MpO1xuICAgIG5vZGUub3BlcmF0b3IgPSB0aGlzLnZhbHVlO1xuICAgIG5vZGUubGVmdCA9IHRoaXMudHlwZSA9PT0gdHQuZXEgPyB0aGlzLnRvQXNzaWduYWJsZShsZWZ0KSA6IGxlZnQ7XG4gICAgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcy5zdGFydCA9IDA7IC8vIHJlc2V0IGJlY2F1c2Ugc2hvcnRoYW5kIGRlZmF1bHQgd2FzIHVzZWQgY29ycmVjdGx5XG4gICAgdGhpcy5jaGVja0xWYWwobGVmdCk7XG4gICAgdGhpcy5uZXh0KCk7XG4gICAgbm9kZS5yaWdodCA9IHRoaXMucGFyc2VNYXliZUFzc2lnbihub0luKTtcbiAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiQXNzaWdubWVudEV4cHJlc3Npb25cIik7XG4gIH0gZWxzZSBpZiAoZmFpbE9uU2hvcnRoYW5kQXNzaWduICYmIHJlZlNob3J0aGFuZERlZmF1bHRQb3Muc3RhcnQpIHtcbiAgICB0aGlzLnVuZXhwZWN0ZWQocmVmU2hvcnRoYW5kRGVmYXVsdFBvcy5zdGFydCk7XG4gIH1cbiAgcmV0dXJuIGxlZnQ7XG59O1xuXG4vLyBQYXJzZSBhIHRlcm5hcnkgY29uZGl0aW9uYWwgKGA/OmApIG9wZXJhdG9yLlxuXG5wcC5wYXJzZU1heWJlQ29uZGl0aW9uYWwgPSBmdW5jdGlvbiAobm9JbiwgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcykge1xuICB2YXIgc3RhcnRQb3MgPSB0aGlzLnN0YXJ0LFxuICAgICAgc3RhcnRMb2MgPSB0aGlzLnN0YXJ0TG9jO1xuICB2YXIgZXhwciA9IHRoaXMucGFyc2VFeHByT3BzKG5vSW4sIHJlZlNob3J0aGFuZERlZmF1bHRQb3MpO1xuICBpZiAocmVmU2hvcnRoYW5kRGVmYXVsdFBvcyAmJiByZWZTaG9ydGhhbmREZWZhdWx0UG9zLnN0YXJ0KSByZXR1cm4gZXhwcjtcbiAgaWYgKHRoaXMuZWF0KHR0LnF1ZXN0aW9uKSkge1xuICAgIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGVBdChzdGFydFBvcywgc3RhcnRMb2MpO1xuICAgIG5vZGUudGVzdCA9IGV4cHI7XG4gICAgbm9kZS5jb25zZXF1ZW50ID0gdGhpcy5wYXJzZU1heWJlQXNzaWduKCk7XG4gICAgdGhpcy5leHBlY3QodHQuY29sb24pO1xuICAgIG5vZGUuYWx0ZXJuYXRlID0gdGhpcy5wYXJzZU1heWJlQXNzaWduKG5vSW4pO1xuICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJDb25kaXRpb25hbEV4cHJlc3Npb25cIik7XG4gIH1cbiAgcmV0dXJuIGV4cHI7XG59O1xuXG4vLyBTdGFydCB0aGUgcHJlY2VkZW5jZSBwYXJzZXIuXG5cbnBwLnBhcnNlRXhwck9wcyA9IGZ1bmN0aW9uIChub0luLCByZWZTaG9ydGhhbmREZWZhdWx0UG9zKSB7XG4gIHZhciBzdGFydFBvcyA9IHRoaXMuc3RhcnQsXG4gICAgICBzdGFydExvYyA9IHRoaXMuc3RhcnRMb2M7XG4gIHZhciBleHByID0gdGhpcy5wYXJzZU1heWJlVW5hcnkocmVmU2hvcnRoYW5kRGVmYXVsdFBvcyk7XG4gIGlmIChyZWZTaG9ydGhhbmREZWZhdWx0UG9zICYmIHJlZlNob3J0aGFuZERlZmF1bHRQb3Muc3RhcnQpIHJldHVybiBleHByO1xuICByZXR1cm4gdGhpcy5wYXJzZUV4cHJPcChleHByLCBzdGFydFBvcywgc3RhcnRMb2MsIC0xLCBub0luKTtcbn07XG5cbi8vIFBhcnNlIGJpbmFyeSBvcGVyYXRvcnMgd2l0aCB0aGUgb3BlcmF0b3IgcHJlY2VkZW5jZSBwYXJzaW5nXG4vLyBhbGdvcml0aG0uIGBsZWZ0YCBpcyB0aGUgbGVmdC1oYW5kIHNpZGUgb2YgdGhlIG9wZXJhdG9yLlxuLy8gYG1pblByZWNgIHByb3ZpZGVzIGNvbnRleHQgdGhhdCBhbGxvd3MgdGhlIGZ1bmN0aW9uIHRvIHN0b3AgYW5kXG4vLyBkZWZlciBmdXJ0aGVyIHBhcnNlciB0byBvbmUgb2YgaXRzIGNhbGxlcnMgd2hlbiBpdCBlbmNvdW50ZXJzIGFuXG4vLyBvcGVyYXRvciB0aGF0IGhhcyBhIGxvd2VyIHByZWNlZGVuY2UgdGhhbiB0aGUgc2V0IGl0IGlzIHBhcnNpbmcuXG5cbnBwLnBhcnNlRXhwck9wID0gZnVuY3Rpb24gKGxlZnQsIGxlZnRTdGFydFBvcywgbGVmdFN0YXJ0TG9jLCBtaW5QcmVjLCBub0luKSB7XG4gIHZhciBwcmVjID0gdGhpcy50eXBlLmJpbm9wO1xuICBpZiAoQXJyYXkuaXNBcnJheShsZWZ0U3RhcnRQb3MpKSB7XG4gICAgaWYgKHRoaXMub3B0aW9ucy5sb2NhdGlvbnMgJiYgbm9JbiA9PT0gdW5kZWZpbmVkKSB7XG4gICAgICAvLyBzaGlmdCBhcmd1bWVudHMgdG8gbGVmdCBieSBvbmVcbiAgICAgIG5vSW4gPSBtaW5QcmVjO1xuICAgICAgbWluUHJlYyA9IGxlZnRTdGFydExvYztcbiAgICAgIC8vIGZsYXR0ZW4gbGVmdFN0YXJ0UG9zXG4gICAgICBsZWZ0U3RhcnRMb2MgPSBsZWZ0U3RhcnRQb3NbMV07XG4gICAgICBsZWZ0U3RhcnRQb3MgPSBsZWZ0U3RhcnRQb3NbMF07XG4gICAgfVxuICB9XG4gIGlmIChwcmVjICE9IG51bGwgJiYgKCFub0luIHx8IHRoaXMudHlwZSAhPT0gdHQuX2luKSkge1xuICAgIGlmIChwcmVjID4gbWluUHJlYykge1xuICAgICAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZUF0KGxlZnRTdGFydFBvcywgbGVmdFN0YXJ0TG9jKTtcbiAgICAgIG5vZGUubGVmdCA9IGxlZnQ7XG4gICAgICBub2RlLm9wZXJhdG9yID0gdGhpcy52YWx1ZTtcbiAgICAgIHZhciBvcCA9IHRoaXMudHlwZTtcbiAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgdmFyIHN0YXJ0UG9zID0gdGhpcy5zdGFydCxcbiAgICAgICAgICBzdGFydExvYyA9IHRoaXMuc3RhcnRMb2M7XG4gICAgICBub2RlLnJpZ2h0ID0gdGhpcy5wYXJzZUV4cHJPcCh0aGlzLnBhcnNlTWF5YmVVbmFyeSgpLCBzdGFydFBvcywgc3RhcnRMb2MsIHByZWMsIG5vSW4pO1xuICAgICAgdGhpcy5maW5pc2hOb2RlKG5vZGUsIG9wID09PSB0dC5sb2dpY2FsT1IgfHwgb3AgPT09IHR0LmxvZ2ljYWxBTkQgPyBcIkxvZ2ljYWxFeHByZXNzaW9uXCIgOiBcIkJpbmFyeUV4cHJlc3Npb25cIik7XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZUV4cHJPcChub2RlLCBsZWZ0U3RhcnRQb3MsIGxlZnRTdGFydExvYywgbWluUHJlYywgbm9Jbik7XG4gICAgfVxuICB9XG4gIHJldHVybiBsZWZ0O1xufTtcblxuLy8gUGFyc2UgdW5hcnkgb3BlcmF0b3JzLCBib3RoIHByZWZpeCBhbmQgcG9zdGZpeC5cblxucHAucGFyc2VNYXliZVVuYXJ5ID0gZnVuY3Rpb24gKHJlZlNob3J0aGFuZERlZmF1bHRQb3MpIHtcbiAgaWYgKHRoaXMudHlwZS5wcmVmaXgpIHtcbiAgICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCksXG4gICAgICAgIHVwZGF0ZSA9IHRoaXMudHlwZSA9PT0gdHQuaW5jRGVjO1xuICAgIG5vZGUub3BlcmF0b3IgPSB0aGlzLnZhbHVlO1xuICAgIG5vZGUucHJlZml4ID0gdHJ1ZTtcbiAgICB0aGlzLm5leHQoKTtcbiAgICBub2RlLmFyZ3VtZW50ID0gdGhpcy5wYXJzZU1heWJlVW5hcnkoKTtcbiAgICBpZiAocmVmU2hvcnRoYW5kRGVmYXVsdFBvcyAmJiByZWZTaG9ydGhhbmREZWZhdWx0UG9zLnN0YXJ0KSB0aGlzLnVuZXhwZWN0ZWQocmVmU2hvcnRoYW5kRGVmYXVsdFBvcy5zdGFydCk7XG4gICAgaWYgKHVwZGF0ZSkgdGhpcy5jaGVja0xWYWwobm9kZS5hcmd1bWVudCk7ZWxzZSBpZiAodGhpcy5zdHJpY3QgJiYgbm9kZS5vcGVyYXRvciA9PT0gXCJkZWxldGVcIiAmJiBub2RlLmFyZ3VtZW50LnR5cGUgPT09IFwiSWRlbnRpZmllclwiKSB0aGlzLnJhaXNlKG5vZGUuc3RhcnQsIFwiRGVsZXRpbmcgbG9jYWwgdmFyaWFibGUgaW4gc3RyaWN0IG1vZGVcIik7XG4gICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCB1cGRhdGUgPyBcIlVwZGF0ZUV4cHJlc3Npb25cIiA6IFwiVW5hcnlFeHByZXNzaW9uXCIpO1xuICB9XG4gIHZhciBzdGFydFBvcyA9IHRoaXMuc3RhcnQsXG4gICAgICBzdGFydExvYyA9IHRoaXMuc3RhcnRMb2M7XG4gIHZhciBleHByID0gdGhpcy5wYXJzZUV4cHJTdWJzY3JpcHRzKHJlZlNob3J0aGFuZERlZmF1bHRQb3MpO1xuICBpZiAocmVmU2hvcnRoYW5kRGVmYXVsdFBvcyAmJiByZWZTaG9ydGhhbmREZWZhdWx0UG9zLnN0YXJ0KSByZXR1cm4gZXhwcjtcbiAgd2hpbGUgKHRoaXMudHlwZS5wb3N0Zml4ICYmICF0aGlzLmNhbkluc2VydFNlbWljb2xvbigpKSB7XG4gICAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0UG9zLCBzdGFydExvYyk7XG4gICAgbm9kZS5vcGVyYXRvciA9IHRoaXMudmFsdWU7XG4gICAgbm9kZS5wcmVmaXggPSBmYWxzZTtcbiAgICBub2RlLmFyZ3VtZW50ID0gZXhwcjtcbiAgICB0aGlzLmNoZWNrTFZhbChleHByKTtcbiAgICB0aGlzLm5leHQoKTtcbiAgICBleHByID0gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiVXBkYXRlRXhwcmVzc2lvblwiKTtcbiAgfVxuICByZXR1cm4gZXhwcjtcbn07XG5cbi8vIFBhcnNlIGNhbGwsIGRvdCwgYW5kIGBbXWAtc3Vic2NyaXB0IGV4cHJlc3Npb25zLlxuXG5wcC5wYXJzZUV4cHJTdWJzY3JpcHRzID0gZnVuY3Rpb24gKHJlZlNob3J0aGFuZERlZmF1bHRQb3MpIHtcbiAgdmFyIHN0YXJ0UG9zID0gdGhpcy5zdGFydCxcbiAgICAgIHN0YXJ0TG9jID0gdGhpcy5zdGFydExvYztcbiAgdmFyIGV4cHIgPSB0aGlzLnBhcnNlRXhwckF0b20ocmVmU2hvcnRoYW5kRGVmYXVsdFBvcyk7XG4gIGlmIChyZWZTaG9ydGhhbmREZWZhdWx0UG9zICYmIHJlZlNob3J0aGFuZERlZmF1bHRQb3Muc3RhcnQpIHJldHVybiBleHByO1xuICByZXR1cm4gdGhpcy5wYXJzZVN1YnNjcmlwdHMoZXhwciwgc3RhcnRQb3MsIHN0YXJ0TG9jKTtcbn07XG5cbnBwLnBhcnNlU3Vic2NyaXB0cyA9IGZ1bmN0aW9uIChiYXNlLCBzdGFydFBvcywgc3RhcnRMb2MsIG5vQ2FsbHMpIHtcbiAgaWYgKEFycmF5LmlzQXJyYXkoc3RhcnRQb3MpKSB7XG4gICAgaWYgKHRoaXMub3B0aW9ucy5sb2NhdGlvbnMgJiYgbm9DYWxscyA9PT0gdW5kZWZpbmVkKSB7XG4gICAgICAvLyBzaGlmdCBhcmd1bWVudHMgdG8gbGVmdCBieSBvbmVcbiAgICAgIG5vQ2FsbHMgPSBzdGFydExvYztcbiAgICAgIC8vIGZsYXR0ZW4gc3RhcnRQb3NcbiAgICAgIHN0YXJ0TG9jID0gc3RhcnRQb3NbMV07XG4gICAgICBzdGFydFBvcyA9IHN0YXJ0UG9zWzBdO1xuICAgIH1cbiAgfVxuICBmb3IgKDs7KSB7XG4gICAgaWYgKHRoaXMuZWF0KHR0LmRvdCkpIHtcbiAgICAgIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGVBdChzdGFydFBvcywgc3RhcnRMb2MpO1xuICAgICAgbm9kZS5vYmplY3QgPSBiYXNlO1xuICAgICAgbm9kZS5wcm9wZXJ0eSA9IHRoaXMucGFyc2VJZGVudCh0cnVlKTtcbiAgICAgIG5vZGUuY29tcHV0ZWQgPSBmYWxzZTtcbiAgICAgIGJhc2UgPSB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJNZW1iZXJFeHByZXNzaW9uXCIpO1xuICAgIH0gZWxzZSBpZiAodGhpcy5lYXQodHQuYnJhY2tldEwpKSB7XG4gICAgICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlQXQoc3RhcnRQb3MsIHN0YXJ0TG9jKTtcbiAgICAgIG5vZGUub2JqZWN0ID0gYmFzZTtcbiAgICAgIG5vZGUucHJvcGVydHkgPSB0aGlzLnBhcnNlRXhwcmVzc2lvbigpO1xuICAgICAgbm9kZS5jb21wdXRlZCA9IHRydWU7XG4gICAgICB0aGlzLmV4cGVjdCh0dC5icmFja2V0Uik7XG4gICAgICBiYXNlID0gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiTWVtYmVyRXhwcmVzc2lvblwiKTtcbiAgICB9IGVsc2UgaWYgKCFub0NhbGxzICYmIHRoaXMuZWF0KHR0LnBhcmVuTCkpIHtcbiAgICAgIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGVBdChzdGFydFBvcywgc3RhcnRMb2MpO1xuICAgICAgbm9kZS5jYWxsZWUgPSBiYXNlO1xuICAgICAgbm9kZS5hcmd1bWVudHMgPSB0aGlzLnBhcnNlRXhwckxpc3QodHQucGFyZW5SLCBmYWxzZSk7XG4gICAgICBiYXNlID0gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiQ2FsbEV4cHJlc3Npb25cIik7XG4gICAgfSBlbHNlIGlmICh0aGlzLnR5cGUgPT09IHR0LmJhY2tRdW90ZSkge1xuICAgICAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0UG9zLCBzdGFydExvYyk7XG4gICAgICBub2RlLnRhZyA9IGJhc2U7XG4gICAgICBub2RlLnF1YXNpID0gdGhpcy5wYXJzZVRlbXBsYXRlKCk7XG4gICAgICBiYXNlID0gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiVGFnZ2VkVGVtcGxhdGVFeHByZXNzaW9uXCIpO1xuICAgIH0gZWxzZSB7XG4gICAgICByZXR1cm4gYmFzZTtcbiAgICB9XG4gIH1cbn07XG5cbi8vIFBhcnNlIGFuIGF0b21pYyBleHByZXNzaW9uIOKAlCBlaXRoZXIgYSBzaW5nbGUgdG9rZW4gdGhhdCBpcyBhblxuLy8gZXhwcmVzc2lvbiwgYW4gZXhwcmVzc2lvbiBzdGFydGVkIGJ5IGEga2V5d29yZCBsaWtlIGBmdW5jdGlvbmAgb3Jcbi8vIGBuZXdgLCBvciBhbiBleHByZXNzaW9uIHdyYXBwZWQgaW4gcHVuY3R1YXRpb24gbGlrZSBgKClgLCBgW11gLFxuLy8gb3IgYHt9YC5cblxucHAucGFyc2VFeHByQXRvbSA9IGZ1bmN0aW9uIChyZWZTaG9ydGhhbmREZWZhdWx0UG9zKSB7XG4gIHZhciBub2RlID0gdW5kZWZpbmVkLFxuICAgICAgY2FuQmVBcnJvdyA9IHRoaXMucG90ZW50aWFsQXJyb3dBdCA9PSB0aGlzLnN0YXJ0O1xuICBzd2l0Y2ggKHRoaXMudHlwZSkge1xuICAgIGNhc2UgdHQuX3RoaXM6XG4gICAgY2FzZSB0dC5fc3VwZXI6XG4gICAgICB2YXIgdHlwZSA9IHRoaXMudHlwZSA9PT0gdHQuX3RoaXMgPyBcIlRoaXNFeHByZXNzaW9uXCIgOiBcIlN1cGVyXCI7XG4gICAgICBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCB0eXBlKTtcblxuICAgIGNhc2UgdHQuX3lpZWxkOlxuICAgICAgaWYgKHRoaXMuaW5HZW5lcmF0b3IpIHRoaXMudW5leHBlY3RlZCgpO1xuXG4gICAgY2FzZSB0dC5uYW1lOlxuICAgICAgdmFyIHN0YXJ0UG9zID0gdGhpcy5zdGFydCxcbiAgICAgICAgICBzdGFydExvYyA9IHRoaXMuc3RhcnRMb2M7XG4gICAgICB2YXIgaWQgPSB0aGlzLnBhcnNlSWRlbnQodGhpcy50eXBlICE9PSB0dC5uYW1lKTtcbiAgICAgIGlmIChjYW5CZUFycm93ICYmICF0aGlzLmNhbkluc2VydFNlbWljb2xvbigpICYmIHRoaXMuZWF0KHR0LmFycm93KSkgcmV0dXJuIHRoaXMucGFyc2VBcnJvd0V4cHJlc3Npb24odGhpcy5zdGFydE5vZGVBdChzdGFydFBvcywgc3RhcnRMb2MpLCBbaWRdKTtcbiAgICAgIHJldHVybiBpZDtcblxuICAgIGNhc2UgdHQucmVnZXhwOlxuICAgICAgdmFyIHZhbHVlID0gdGhpcy52YWx1ZTtcbiAgICAgIG5vZGUgPSB0aGlzLnBhcnNlTGl0ZXJhbCh2YWx1ZS52YWx1ZSk7XG4gICAgICBub2RlLnJlZ2V4ID0geyBwYXR0ZXJuOiB2YWx1ZS5wYXR0ZXJuLCBmbGFnczogdmFsdWUuZmxhZ3MgfTtcbiAgICAgIHJldHVybiBub2RlO1xuXG4gICAgY2FzZSB0dC5udW06Y2FzZSB0dC5zdHJpbmc6XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZUxpdGVyYWwodGhpcy52YWx1ZSk7XG5cbiAgICBjYXNlIHR0Ll9udWxsOmNhc2UgdHQuX3RydWU6Y2FzZSB0dC5fZmFsc2U6XG4gICAgICBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgICAgIG5vZGUudmFsdWUgPSB0aGlzLnR5cGUgPT09IHR0Ll9udWxsID8gbnVsbCA6IHRoaXMudHlwZSA9PT0gdHQuX3RydWU7XG4gICAgICBub2RlLnJhdyA9IHRoaXMudHlwZS5rZXl3b3JkO1xuICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiTGl0ZXJhbFwiKTtcblxuICAgIGNhc2UgdHQucGFyZW5MOlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VQYXJlbkFuZERpc3Rpbmd1aXNoRXhwcmVzc2lvbihjYW5CZUFycm93KTtcblxuICAgIGNhc2UgdHQuYnJhY2tldEw6XG4gICAgICBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgLy8gY2hlY2sgd2hldGhlciB0aGlzIGlzIGFycmF5IGNvbXByZWhlbnNpb24gb3IgcmVndWxhciBhcnJheVxuICAgICAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA3ICYmIHRoaXMudHlwZSA9PT0gdHQuX2Zvcikge1xuICAgICAgICByZXR1cm4gdGhpcy5wYXJzZUNvbXByZWhlbnNpb24obm9kZSwgZmFsc2UpO1xuICAgICAgfVxuICAgICAgbm9kZS5lbGVtZW50cyA9IHRoaXMucGFyc2VFeHByTGlzdCh0dC5icmFja2V0UiwgdHJ1ZSwgdHJ1ZSwgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcyk7XG4gICAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiQXJyYXlFeHByZXNzaW9uXCIpO1xuXG4gICAgY2FzZSB0dC5icmFjZUw6XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZU9iaihmYWxzZSwgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcyk7XG5cbiAgICBjYXNlIHR0Ll9mdW5jdGlvbjpcbiAgICAgIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZUZ1bmN0aW9uKG5vZGUsIGZhbHNlKTtcblxuICAgIGNhc2UgdHQuX2NsYXNzOlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VDbGFzcyh0aGlzLnN0YXJ0Tm9kZSgpLCBmYWxzZSk7XG5cbiAgICBjYXNlIHR0Ll9uZXc6XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZU5ldygpO1xuXG4gICAgY2FzZSB0dC5iYWNrUXVvdGU6XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZVRlbXBsYXRlKCk7XG5cbiAgICBkZWZhdWx0OlxuICAgICAgdGhpcy51bmV4cGVjdGVkKCk7XG4gIH1cbn07XG5cbnBwLnBhcnNlTGl0ZXJhbCA9IGZ1bmN0aW9uICh2YWx1ZSkge1xuICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gIG5vZGUudmFsdWUgPSB2YWx1ZTtcbiAgbm9kZS5yYXcgPSB0aGlzLmlucHV0LnNsaWNlKHRoaXMuc3RhcnQsIHRoaXMuZW5kKTtcbiAgdGhpcy5uZXh0KCk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJMaXRlcmFsXCIpO1xufTtcblxucHAucGFyc2VQYXJlbkV4cHJlc3Npb24gPSBmdW5jdGlvbiAoKSB7XG4gIHRoaXMuZXhwZWN0KHR0LnBhcmVuTCk7XG4gIHZhciB2YWwgPSB0aGlzLnBhcnNlRXhwcmVzc2lvbigpO1xuICB0aGlzLmV4cGVjdCh0dC5wYXJlblIpO1xuICByZXR1cm4gdmFsO1xufTtcblxucHAucGFyc2VQYXJlbkFuZERpc3Rpbmd1aXNoRXhwcmVzc2lvbiA9IGZ1bmN0aW9uIChjYW5CZUFycm93KSB7XG4gIHZhciBzdGFydFBvcyA9IHRoaXMuc3RhcnQsXG4gICAgICBzdGFydExvYyA9IHRoaXMuc3RhcnRMb2MsXG4gICAgICB2YWwgPSB1bmRlZmluZWQ7XG4gIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNikge1xuICAgIHRoaXMubmV4dCgpO1xuXG4gICAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA3ICYmIHRoaXMudHlwZSA9PT0gdHQuX2Zvcikge1xuICAgICAgcmV0dXJuIHRoaXMucGFyc2VDb21wcmVoZW5zaW9uKHRoaXMuc3RhcnROb2RlQXQoc3RhcnRQb3MsIHN0YXJ0TG9jKSwgdHJ1ZSk7XG4gICAgfVxuXG4gICAgdmFyIGlubmVyU3RhcnRQb3MgPSB0aGlzLnN0YXJ0LFxuICAgICAgICBpbm5lclN0YXJ0TG9jID0gdGhpcy5zdGFydExvYztcbiAgICB2YXIgZXhwckxpc3QgPSBbXSxcbiAgICAgICAgZmlyc3QgPSB0cnVlO1xuICAgIHZhciByZWZTaG9ydGhhbmREZWZhdWx0UG9zID0geyBzdGFydDogMCB9LFxuICAgICAgICBzcHJlYWRTdGFydCA9IHVuZGVmaW5lZCxcbiAgICAgICAgaW5uZXJQYXJlblN0YXJ0ID0gdW5kZWZpbmVkO1xuICAgIHdoaWxlICh0aGlzLnR5cGUgIT09IHR0LnBhcmVuUikge1xuICAgICAgZmlyc3QgPyBmaXJzdCA9IGZhbHNlIDogdGhpcy5leHBlY3QodHQuY29tbWEpO1xuICAgICAgaWYgKHRoaXMudHlwZSA9PT0gdHQuZWxsaXBzaXMpIHtcbiAgICAgICAgc3ByZWFkU3RhcnQgPSB0aGlzLnN0YXJ0O1xuICAgICAgICBleHByTGlzdC5wdXNoKHRoaXMucGFyc2VQYXJlbkl0ZW0odGhpcy5wYXJzZVJlc3QoKSkpO1xuICAgICAgICBicmVhaztcbiAgICAgIH0gZWxzZSB7XG4gICAgICAgIGlmICh0aGlzLnR5cGUgPT09IHR0LnBhcmVuTCAmJiAhaW5uZXJQYXJlblN0YXJ0KSB7XG4gICAgICAgICAgaW5uZXJQYXJlblN0YXJ0ID0gdGhpcy5zdGFydDtcbiAgICAgICAgfVxuICAgICAgICBleHByTGlzdC5wdXNoKHRoaXMucGFyc2VNYXliZUFzc2lnbihmYWxzZSwgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcywgdGhpcy5wYXJzZVBhcmVuSXRlbSkpO1xuICAgICAgfVxuICAgIH1cbiAgICB2YXIgaW5uZXJFbmRQb3MgPSB0aGlzLnN0YXJ0LFxuICAgICAgICBpbm5lckVuZExvYyA9IHRoaXMuc3RhcnRMb2M7XG4gICAgdGhpcy5leHBlY3QodHQucGFyZW5SKTtcblxuICAgIGlmIChjYW5CZUFycm93ICYmICF0aGlzLmNhbkluc2VydFNlbWljb2xvbigpICYmIHRoaXMuZWF0KHR0LmFycm93KSkge1xuICAgICAgaWYgKGlubmVyUGFyZW5TdGFydCkgdGhpcy51bmV4cGVjdGVkKGlubmVyUGFyZW5TdGFydCk7XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZVBhcmVuQXJyb3dMaXN0KHN0YXJ0UG9zLCBzdGFydExvYywgZXhwckxpc3QpO1xuICAgIH1cblxuICAgIGlmICghZXhwckxpc3QubGVuZ3RoKSB0aGlzLnVuZXhwZWN0ZWQodGhpcy5sYXN0VG9rU3RhcnQpO1xuICAgIGlmIChzcHJlYWRTdGFydCkgdGhpcy51bmV4cGVjdGVkKHNwcmVhZFN0YXJ0KTtcbiAgICBpZiAocmVmU2hvcnRoYW5kRGVmYXVsdFBvcy5zdGFydCkgdGhpcy51bmV4cGVjdGVkKHJlZlNob3J0aGFuZERlZmF1bHRQb3Muc3RhcnQpO1xuXG4gICAgaWYgKGV4cHJMaXN0Lmxlbmd0aCA+IDEpIHtcbiAgICAgIHZhbCA9IHRoaXMuc3RhcnROb2RlQXQoaW5uZXJTdGFydFBvcywgaW5uZXJTdGFydExvYyk7XG4gICAgICB2YWwuZXhwcmVzc2lvbnMgPSBleHByTGlzdDtcbiAgICAgIHRoaXMuZmluaXNoTm9kZUF0KHZhbCwgXCJTZXF1ZW5jZUV4cHJlc3Npb25cIiwgaW5uZXJFbmRQb3MsIGlubmVyRW5kTG9jKTtcbiAgICB9IGVsc2Uge1xuICAgICAgdmFsID0gZXhwckxpc3RbMF07XG4gICAgfVxuICB9IGVsc2Uge1xuICAgIHZhbCA9IHRoaXMucGFyc2VQYXJlbkV4cHJlc3Npb24oKTtcbiAgfVxuXG4gIGlmICh0aGlzLm9wdGlvbnMucHJlc2VydmVQYXJlbnMpIHtcbiAgICB2YXIgcGFyID0gdGhpcy5zdGFydE5vZGVBdChzdGFydFBvcywgc3RhcnRMb2MpO1xuICAgIHBhci5leHByZXNzaW9uID0gdmFsO1xuICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUocGFyLCBcIlBhcmVudGhlc2l6ZWRFeHByZXNzaW9uXCIpO1xuICB9IGVsc2Uge1xuICAgIHJldHVybiB2YWw7XG4gIH1cbn07XG5cbnBwLnBhcnNlUGFyZW5JdGVtID0gZnVuY3Rpb24gKGl0ZW0pIHtcbiAgcmV0dXJuIGl0ZW07XG59O1xuXG5wcC5wYXJzZVBhcmVuQXJyb3dMaXN0ID0gZnVuY3Rpb24gKHN0YXJ0UG9zLCBzdGFydExvYywgZXhwckxpc3QpIHtcbiAgcmV0dXJuIHRoaXMucGFyc2VBcnJvd0V4cHJlc3Npb24odGhpcy5zdGFydE5vZGVBdChzdGFydFBvcywgc3RhcnRMb2MpLCBleHByTGlzdCk7XG59O1xuXG4vLyBOZXcncyBwcmVjZWRlbmNlIGlzIHNsaWdodGx5IHRyaWNreS4gSXQgbXVzdCBhbGxvdyBpdHMgYXJndW1lbnRcbi8vIHRvIGJlIGEgYFtdYCBvciBkb3Qgc3Vic2NyaXB0IGV4cHJlc3Npb24sIGJ1dCBub3QgYSBjYWxsIOKAlCBhdFxuLy8gbGVhc3QsIG5vdCB3aXRob3V0IHdyYXBwaW5nIGl0IGluIHBhcmVudGhlc2VzLiBUaHVzLCBpdCB1c2VzIHRoZVxuXG52YXIgZW1wdHkgPSBbXTtcblxucHAucGFyc2VOZXcgPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgdmFyIG1ldGEgPSB0aGlzLnBhcnNlSWRlbnQodHJ1ZSk7XG4gIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNiAmJiB0aGlzLmVhdCh0dC5kb3QpKSB7XG4gICAgbm9kZS5tZXRhID0gbWV0YTtcbiAgICBub2RlLnByb3BlcnR5ID0gdGhpcy5wYXJzZUlkZW50KHRydWUpO1xuICAgIGlmIChub2RlLnByb3BlcnR5Lm5hbWUgIT09IFwidGFyZ2V0XCIpIHRoaXMucmFpc2Uobm9kZS5wcm9wZXJ0eS5zdGFydCwgXCJUaGUgb25seSB2YWxpZCBtZXRhIHByb3BlcnR5IGZvciBuZXcgaXMgbmV3LnRhcmdldFwiKTtcbiAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiTWV0YVByb3BlcnR5XCIpO1xuICB9XG4gIHZhciBzdGFydFBvcyA9IHRoaXMuc3RhcnQsXG4gICAgICBzdGFydExvYyA9IHRoaXMuc3RhcnRMb2M7XG4gIG5vZGUuY2FsbGVlID0gdGhpcy5wYXJzZVN1YnNjcmlwdHModGhpcy5wYXJzZUV4cHJBdG9tKCksIHN0YXJ0UG9zLCBzdGFydExvYywgdHJ1ZSk7XG4gIGlmICh0aGlzLmVhdCh0dC5wYXJlbkwpKSBub2RlLmFyZ3VtZW50cyA9IHRoaXMucGFyc2VFeHByTGlzdCh0dC5wYXJlblIsIGZhbHNlKTtlbHNlIG5vZGUuYXJndW1lbnRzID0gZW1wdHk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJOZXdFeHByZXNzaW9uXCIpO1xufTtcblxuLy8gUGFyc2UgdGVtcGxhdGUgZXhwcmVzc2lvbi5cblxucHAucGFyc2VUZW1wbGF0ZUVsZW1lbnQgPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBlbGVtID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgZWxlbS52YWx1ZSA9IHtcbiAgICByYXc6IHRoaXMuaW5wdXQuc2xpY2UodGhpcy5zdGFydCwgdGhpcy5lbmQpLFxuICAgIGNvb2tlZDogdGhpcy52YWx1ZVxuICB9O1xuICB0aGlzLm5leHQoKTtcbiAgZWxlbS50YWlsID0gdGhpcy50eXBlID09PSB0dC5iYWNrUXVvdGU7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUoZWxlbSwgXCJUZW1wbGF0ZUVsZW1lbnRcIik7XG59O1xuXG5wcC5wYXJzZVRlbXBsYXRlID0gZnVuY3Rpb24gKCkge1xuICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gIHRoaXMubmV4dCgpO1xuICBub2RlLmV4cHJlc3Npb25zID0gW107XG4gIHZhciBjdXJFbHQgPSB0aGlzLnBhcnNlVGVtcGxhdGVFbGVtZW50KCk7XG4gIG5vZGUucXVhc2lzID0gW2N1ckVsdF07XG4gIHdoaWxlICghY3VyRWx0LnRhaWwpIHtcbiAgICB0aGlzLmV4cGVjdCh0dC5kb2xsYXJCcmFjZUwpO1xuICAgIG5vZGUuZXhwcmVzc2lvbnMucHVzaCh0aGlzLnBhcnNlRXhwcmVzc2lvbigpKTtcbiAgICB0aGlzLmV4cGVjdCh0dC5icmFjZVIpO1xuICAgIG5vZGUucXVhc2lzLnB1c2goY3VyRWx0ID0gdGhpcy5wYXJzZVRlbXBsYXRlRWxlbWVudCgpKTtcbiAgfVxuICB0aGlzLm5leHQoKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIlRlbXBsYXRlTGl0ZXJhbFwiKTtcbn07XG5cbi8vIFBhcnNlIGFuIG9iamVjdCBsaXRlcmFsIG9yIGJpbmRpbmcgcGF0dGVybi5cblxucHAucGFyc2VPYmogPSBmdW5jdGlvbiAoaXNQYXR0ZXJuLCByZWZTaG9ydGhhbmREZWZhdWx0UG9zKSB7XG4gIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGUoKSxcbiAgICAgIGZpcnN0ID0gdHJ1ZSxcbiAgICAgIHByb3BIYXNoID0ge307XG4gIG5vZGUucHJvcGVydGllcyA9IFtdO1xuICB0aGlzLm5leHQoKTtcbiAgd2hpbGUgKCF0aGlzLmVhdCh0dC5icmFjZVIpKSB7XG4gICAgaWYgKCFmaXJzdCkge1xuICAgICAgdGhpcy5leHBlY3QodHQuY29tbWEpO1xuICAgICAgaWYgKHRoaXMuYWZ0ZXJUcmFpbGluZ0NvbW1hKHR0LmJyYWNlUikpIGJyZWFrO1xuICAgIH0gZWxzZSBmaXJzdCA9IGZhbHNlO1xuXG4gICAgdmFyIHByb3AgPSB0aGlzLnN0YXJ0Tm9kZSgpLFxuICAgICAgICBpc0dlbmVyYXRvciA9IHVuZGVmaW5lZCxcbiAgICAgICAgc3RhcnRQb3MgPSB1bmRlZmluZWQsXG4gICAgICAgIHN0YXJ0TG9jID0gdW5kZWZpbmVkO1xuICAgIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNikge1xuICAgICAgcHJvcC5tZXRob2QgPSBmYWxzZTtcbiAgICAgIHByb3Auc2hvcnRoYW5kID0gZmFsc2U7XG4gICAgICBpZiAoaXNQYXR0ZXJuIHx8IHJlZlNob3J0aGFuZERlZmF1bHRQb3MpIHtcbiAgICAgICAgc3RhcnRQb3MgPSB0aGlzLnN0YXJ0O1xuICAgICAgICBzdGFydExvYyA9IHRoaXMuc3RhcnRMb2M7XG4gICAgICB9XG4gICAgICBpZiAoIWlzUGF0dGVybikgaXNHZW5lcmF0b3IgPSB0aGlzLmVhdCh0dC5zdGFyKTtcbiAgICB9XG4gICAgdGhpcy5wYXJzZVByb3BlcnR5TmFtZShwcm9wKTtcbiAgICB0aGlzLnBhcnNlUHJvcGVydHlWYWx1ZShwcm9wLCBpc1BhdHRlcm4sIGlzR2VuZXJhdG9yLCBzdGFydFBvcywgc3RhcnRMb2MsIHJlZlNob3J0aGFuZERlZmF1bHRQb3MpO1xuICAgIHRoaXMuY2hlY2tQcm9wQ2xhc2gocHJvcCwgcHJvcEhhc2gpO1xuICAgIG5vZGUucHJvcGVydGllcy5wdXNoKHRoaXMuZmluaXNoTm9kZShwcm9wLCBcIlByb3BlcnR5XCIpKTtcbiAgfVxuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIGlzUGF0dGVybiA/IFwiT2JqZWN0UGF0dGVyblwiIDogXCJPYmplY3RFeHByZXNzaW9uXCIpO1xufTtcblxucHAucGFyc2VQcm9wZXJ0eVZhbHVlID0gZnVuY3Rpb24gKHByb3AsIGlzUGF0dGVybiwgaXNHZW5lcmF0b3IsIHN0YXJ0UG9zLCBzdGFydExvYywgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcykge1xuICBpZiAodGhpcy5lYXQodHQuY29sb24pKSB7XG4gICAgcHJvcC52YWx1ZSA9IGlzUGF0dGVybiA/IHRoaXMucGFyc2VNYXliZURlZmF1bHQodGhpcy5zdGFydCwgdGhpcy5zdGFydExvYykgOiB0aGlzLnBhcnNlTWF5YmVBc3NpZ24oZmFsc2UsIHJlZlNob3J0aGFuZERlZmF1bHRQb3MpO1xuICAgIHByb3Aua2luZCA9IFwiaW5pdFwiO1xuICB9IGVsc2UgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2ICYmIHRoaXMudHlwZSA9PT0gdHQucGFyZW5MKSB7XG4gICAgaWYgKGlzUGF0dGVybikgdGhpcy51bmV4cGVjdGVkKCk7XG4gICAgcHJvcC5raW5kID0gXCJpbml0XCI7XG4gICAgcHJvcC5tZXRob2QgPSB0cnVlO1xuICAgIHByb3AudmFsdWUgPSB0aGlzLnBhcnNlTWV0aG9kKGlzR2VuZXJhdG9yKTtcbiAgfSBlbHNlIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNSAmJiAhcHJvcC5jb21wdXRlZCAmJiBwcm9wLmtleS50eXBlID09PSBcIklkZW50aWZpZXJcIiAmJiAocHJvcC5rZXkubmFtZSA9PT0gXCJnZXRcIiB8fCBwcm9wLmtleS5uYW1lID09PSBcInNldFwiKSAmJiAodGhpcy50eXBlICE9IHR0LmNvbW1hICYmIHRoaXMudHlwZSAhPSB0dC5icmFjZVIpKSB7XG4gICAgaWYgKGlzR2VuZXJhdG9yIHx8IGlzUGF0dGVybikgdGhpcy51bmV4cGVjdGVkKCk7XG4gICAgcHJvcC5raW5kID0gcHJvcC5rZXkubmFtZTtcbiAgICB0aGlzLnBhcnNlUHJvcGVydHlOYW1lKHByb3ApO1xuICAgIHByb3AudmFsdWUgPSB0aGlzLnBhcnNlTWV0aG9kKGZhbHNlKTtcbiAgfSBlbHNlIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNiAmJiAhcHJvcC5jb21wdXRlZCAmJiBwcm9wLmtleS50eXBlID09PSBcIklkZW50aWZpZXJcIikge1xuICAgIHByb3Aua2luZCA9IFwiaW5pdFwiO1xuICAgIGlmIChpc1BhdHRlcm4pIHtcbiAgICAgIGlmICh0aGlzLmlzS2V5d29yZChwcm9wLmtleS5uYW1lKSB8fCB0aGlzLnN0cmljdCAmJiAocmVzZXJ2ZWRXb3Jkcy5zdHJpY3RCaW5kKHByb3Aua2V5Lm5hbWUpIHx8IHJlc2VydmVkV29yZHMuc3RyaWN0KHByb3Aua2V5Lm5hbWUpKSB8fCAhdGhpcy5vcHRpb25zLmFsbG93UmVzZXJ2ZWQgJiYgdGhpcy5pc1Jlc2VydmVkV29yZChwcm9wLmtleS5uYW1lKSkgdGhpcy5yYWlzZShwcm9wLmtleS5zdGFydCwgXCJCaW5kaW5nIFwiICsgcHJvcC5rZXkubmFtZSk7XG4gICAgICBwcm9wLnZhbHVlID0gdGhpcy5wYXJzZU1heWJlRGVmYXVsdChzdGFydFBvcywgc3RhcnRMb2MsIHByb3Aua2V5KTtcbiAgICB9IGVsc2UgaWYgKHRoaXMudHlwZSA9PT0gdHQuZXEgJiYgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcykge1xuICAgICAgaWYgKCFyZWZTaG9ydGhhbmREZWZhdWx0UG9zLnN0YXJ0KSByZWZTaG9ydGhhbmREZWZhdWx0UG9zLnN0YXJ0ID0gdGhpcy5zdGFydDtcbiAgICAgIHByb3AudmFsdWUgPSB0aGlzLnBhcnNlTWF5YmVEZWZhdWx0KHN0YXJ0UG9zLCBzdGFydExvYywgcHJvcC5rZXkpO1xuICAgIH0gZWxzZSB7XG4gICAgICBwcm9wLnZhbHVlID0gcHJvcC5rZXk7XG4gICAgfVxuICAgIHByb3Auc2hvcnRoYW5kID0gdHJ1ZTtcbiAgfSBlbHNlIHRoaXMudW5leHBlY3RlZCgpO1xufTtcblxucHAucGFyc2VQcm9wZXJ0eU5hbWUgPSBmdW5jdGlvbiAocHJvcCkge1xuICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYpIHtcbiAgICBpZiAodGhpcy5lYXQodHQuYnJhY2tldEwpKSB7XG4gICAgICBwcm9wLmNvbXB1dGVkID0gdHJ1ZTtcbiAgICAgIHByb3Aua2V5ID0gdGhpcy5wYXJzZU1heWJlQXNzaWduKCk7XG4gICAgICB0aGlzLmV4cGVjdCh0dC5icmFja2V0Uik7XG4gICAgICByZXR1cm4gcHJvcC5rZXk7XG4gICAgfSBlbHNlIHtcbiAgICAgIHByb3AuY29tcHV0ZWQgPSBmYWxzZTtcbiAgICB9XG4gIH1cbiAgcmV0dXJuIHByb3Aua2V5ID0gdGhpcy50eXBlID09PSB0dC5udW0gfHwgdGhpcy50eXBlID09PSB0dC5zdHJpbmcgPyB0aGlzLnBhcnNlRXhwckF0b20oKSA6IHRoaXMucGFyc2VJZGVudCh0cnVlKTtcbn07XG5cbi8vIEluaXRpYWxpemUgZW1wdHkgZnVuY3Rpb24gbm9kZS5cblxucHAuaW5pdEZ1bmN0aW9uID0gZnVuY3Rpb24gKG5vZGUpIHtcbiAgbm9kZS5pZCA9IG51bGw7XG4gIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNikge1xuICAgIG5vZGUuZ2VuZXJhdG9yID0gZmFsc2U7XG4gICAgbm9kZS5leHByZXNzaW9uID0gZmFsc2U7XG4gIH1cbn07XG5cbi8vIFBhcnNlIG9iamVjdCBvciBjbGFzcyBtZXRob2QuXG5cbnBwLnBhcnNlTWV0aG9kID0gZnVuY3Rpb24gKGlzR2VuZXJhdG9yKSB7XG4gIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgdGhpcy5pbml0RnVuY3Rpb24obm9kZSk7XG4gIHRoaXMuZXhwZWN0KHR0LnBhcmVuTCk7XG4gIG5vZGUucGFyYW1zID0gdGhpcy5wYXJzZUJpbmRpbmdMaXN0KHR0LnBhcmVuUiwgZmFsc2UsIGZhbHNlKTtcbiAgdmFyIGFsbG93RXhwcmVzc2lvbkJvZHkgPSB1bmRlZmluZWQ7XG4gIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNikge1xuICAgIG5vZGUuZ2VuZXJhdG9yID0gaXNHZW5lcmF0b3I7XG4gICAgYWxsb3dFeHByZXNzaW9uQm9keSA9IHRydWU7XG4gIH0gZWxzZSB7XG4gICAgYWxsb3dFeHByZXNzaW9uQm9keSA9IGZhbHNlO1xuICB9XG4gIHRoaXMucGFyc2VGdW5jdGlvbkJvZHkobm9kZSwgYWxsb3dFeHByZXNzaW9uQm9keSk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJGdW5jdGlvbkV4cHJlc3Npb25cIik7XG59O1xuXG4vLyBQYXJzZSBhcnJvdyBmdW5jdGlvbiBleHByZXNzaW9uIHdpdGggZ2l2ZW4gcGFyYW1ldGVycy5cblxucHAucGFyc2VBcnJvd0V4cHJlc3Npb24gPSBmdW5jdGlvbiAobm9kZSwgcGFyYW1zKSB7XG4gIHRoaXMuaW5pdEZ1bmN0aW9uKG5vZGUpO1xuICBub2RlLnBhcmFtcyA9IHRoaXMudG9Bc3NpZ25hYmxlTGlzdChwYXJhbXMsIHRydWUpO1xuICB0aGlzLnBhcnNlRnVuY3Rpb25Cb2R5KG5vZGUsIHRydWUpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiQXJyb3dGdW5jdGlvbkV4cHJlc3Npb25cIik7XG59O1xuXG4vLyBQYXJzZSBmdW5jdGlvbiBib2R5IGFuZCBjaGVjayBwYXJhbWV0ZXJzLlxuXG5wcC5wYXJzZUZ1bmN0aW9uQm9keSA9IGZ1bmN0aW9uIChub2RlLCBhbGxvd0V4cHJlc3Npb24pIHtcbiAgdmFyIGlzRXhwcmVzc2lvbiA9IGFsbG93RXhwcmVzc2lvbiAmJiB0aGlzLnR5cGUgIT09IHR0LmJyYWNlTDtcblxuICBpZiAoaXNFeHByZXNzaW9uKSB7XG4gICAgbm9kZS5ib2R5ID0gdGhpcy5wYXJzZU1heWJlQXNzaWduKCk7XG4gICAgbm9kZS5leHByZXNzaW9uID0gdHJ1ZTtcbiAgfSBlbHNlIHtcbiAgICAvLyBTdGFydCBhIG5ldyBzY29wZSB3aXRoIHJlZ2FyZCB0byBsYWJlbHMgYW5kIHRoZSBgaW5GdW5jdGlvbmBcbiAgICAvLyBmbGFnIChyZXN0b3JlIHRoZW0gdG8gdGhlaXIgb2xkIHZhbHVlIGFmdGVyd2FyZHMpLlxuICAgIHZhciBvbGRJbkZ1bmMgPSB0aGlzLmluRnVuY3Rpb24sXG4gICAgICAgIG9sZEluR2VuID0gdGhpcy5pbkdlbmVyYXRvcixcbiAgICAgICAgb2xkTGFiZWxzID0gdGhpcy5sYWJlbHM7XG4gICAgdGhpcy5pbkZ1bmN0aW9uID0gdHJ1ZTt0aGlzLmluR2VuZXJhdG9yID0gbm9kZS5nZW5lcmF0b3I7dGhpcy5sYWJlbHMgPSBbXTtcbiAgICBub2RlLmJvZHkgPSB0aGlzLnBhcnNlQmxvY2sodHJ1ZSk7XG4gICAgbm9kZS5leHByZXNzaW9uID0gZmFsc2U7XG4gICAgdGhpcy5pbkZ1bmN0aW9uID0gb2xkSW5GdW5jO3RoaXMuaW5HZW5lcmF0b3IgPSBvbGRJbkdlbjt0aGlzLmxhYmVscyA9IG9sZExhYmVscztcbiAgfVxuXG4gIC8vIElmIHRoaXMgaXMgYSBzdHJpY3QgbW9kZSBmdW5jdGlvbiwgdmVyaWZ5IHRoYXQgYXJndW1lbnQgbmFtZXNcbiAgLy8gYXJlIG5vdCByZXBlYXRlZCwgYW5kIGl0IGRvZXMgbm90IHRyeSB0byBiaW5kIHRoZSB3b3JkcyBgZXZhbGBcbiAgLy8gb3IgYGFyZ3VtZW50c2AuXG4gIGlmICh0aGlzLnN0cmljdCB8fCAhaXNFeHByZXNzaW9uICYmIG5vZGUuYm9keS5ib2R5Lmxlbmd0aCAmJiB0aGlzLmlzVXNlU3RyaWN0KG5vZGUuYm9keS5ib2R5WzBdKSkge1xuICAgIHZhciBuYW1lSGFzaCA9IHt9LFxuICAgICAgICBvbGRTdHJpY3QgPSB0aGlzLnN0cmljdDtcbiAgICB0aGlzLnN0cmljdCA9IHRydWU7XG4gICAgaWYgKG5vZGUuaWQpIHRoaXMuY2hlY2tMVmFsKG5vZGUuaWQsIHRydWUpO1xuICAgIGZvciAodmFyIGkgPSAwOyBpIDwgbm9kZS5wYXJhbXMubGVuZ3RoOyBpKyspIHtcbiAgICAgIHRoaXMuY2hlY2tMVmFsKG5vZGUucGFyYW1zW2ldLCB0cnVlLCBuYW1lSGFzaCk7XG4gICAgfXRoaXMuc3RyaWN0ID0gb2xkU3RyaWN0O1xuICB9XG59O1xuXG4vLyBQYXJzZXMgYSBjb21tYS1zZXBhcmF0ZWQgbGlzdCBvZiBleHByZXNzaW9ucywgYW5kIHJldHVybnMgdGhlbSBhc1xuLy8gYW4gYXJyYXkuIGBjbG9zZWAgaXMgdGhlIHRva2VuIHR5cGUgdGhhdCBlbmRzIHRoZSBsaXN0LCBhbmRcbi8vIGBhbGxvd0VtcHR5YCBjYW4gYmUgdHVybmVkIG9uIHRvIGFsbG93IHN1YnNlcXVlbnQgY29tbWFzIHdpdGhcbi8vIG5vdGhpbmcgaW4gYmV0d2VlbiB0aGVtIHRvIGJlIHBhcnNlZCBhcyBgbnVsbGAgKHdoaWNoIGlzIG5lZWRlZFxuLy8gZm9yIGFycmF5IGxpdGVyYWxzKS5cblxucHAucGFyc2VFeHByTGlzdCA9IGZ1bmN0aW9uIChjbG9zZSwgYWxsb3dUcmFpbGluZ0NvbW1hLCBhbGxvd0VtcHR5LCByZWZTaG9ydGhhbmREZWZhdWx0UG9zKSB7XG4gIHZhciBlbHRzID0gW10sXG4gICAgICBmaXJzdCA9IHRydWU7XG4gIHdoaWxlICghdGhpcy5lYXQoY2xvc2UpKSB7XG4gICAgaWYgKCFmaXJzdCkge1xuICAgICAgdGhpcy5leHBlY3QodHQuY29tbWEpO1xuICAgICAgaWYgKGFsbG93VHJhaWxpbmdDb21tYSAmJiB0aGlzLmFmdGVyVHJhaWxpbmdDb21tYShjbG9zZSkpIGJyZWFrO1xuICAgIH0gZWxzZSBmaXJzdCA9IGZhbHNlO1xuXG4gICAgaWYgKGFsbG93RW1wdHkgJiYgdGhpcy50eXBlID09PSB0dC5jb21tYSkge1xuICAgICAgZWx0cy5wdXNoKG51bGwpO1xuICAgIH0gZWxzZSB7XG4gICAgICBpZiAodGhpcy50eXBlID09PSB0dC5lbGxpcHNpcykgZWx0cy5wdXNoKHRoaXMucGFyc2VTcHJlYWQocmVmU2hvcnRoYW5kRGVmYXVsdFBvcykpO2Vsc2UgZWx0cy5wdXNoKHRoaXMucGFyc2VNYXliZUFzc2lnbihmYWxzZSwgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcykpO1xuICAgIH1cbiAgfVxuICByZXR1cm4gZWx0cztcbn07XG5cbi8vIFBhcnNlIHRoZSBuZXh0IHRva2VuIGFzIGFuIGlkZW50aWZpZXIuIElmIGBsaWJlcmFsYCBpcyB0cnVlICh1c2VkXG4vLyB3aGVuIHBhcnNpbmcgcHJvcGVydGllcyksIGl0IHdpbGwgYWxzbyBjb252ZXJ0IGtleXdvcmRzIGludG9cbi8vIGlkZW50aWZpZXJzLlxuXG5wcC5wYXJzZUlkZW50ID0gZnVuY3Rpb24gKGxpYmVyYWwpIHtcbiAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICBpZiAobGliZXJhbCAmJiB0aGlzLm9wdGlvbnMuYWxsb3dSZXNlcnZlZCA9PSBcIm5ldmVyXCIpIGxpYmVyYWwgPSBmYWxzZTtcbiAgaWYgKHRoaXMudHlwZSA9PT0gdHQubmFtZSkge1xuICAgIGlmICghbGliZXJhbCAmJiAoIXRoaXMub3B0aW9ucy5hbGxvd1Jlc2VydmVkICYmIHRoaXMuaXNSZXNlcnZlZFdvcmQodGhpcy52YWx1ZSkgfHwgdGhpcy5zdHJpY3QgJiYgcmVzZXJ2ZWRXb3Jkcy5zdHJpY3QodGhpcy52YWx1ZSkgJiYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2IHx8IHRoaXMuaW5wdXQuc2xpY2UodGhpcy5zdGFydCwgdGhpcy5lbmQpLmluZGV4T2YoXCJcXFxcXCIpID09IC0xKSkpIHRoaXMucmFpc2UodGhpcy5zdGFydCwgXCJUaGUga2V5d29yZCAnXCIgKyB0aGlzLnZhbHVlICsgXCInIGlzIHJlc2VydmVkXCIpO1xuICAgIG5vZGUubmFtZSA9IHRoaXMudmFsdWU7XG4gIH0gZWxzZSBpZiAobGliZXJhbCAmJiB0aGlzLnR5cGUua2V5d29yZCkge1xuICAgIG5vZGUubmFtZSA9IHRoaXMudHlwZS5rZXl3b3JkO1xuICB9IGVsc2Uge1xuICAgIHRoaXMudW5leHBlY3RlZCgpO1xuICB9XG4gIHRoaXMubmV4dCgpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiSWRlbnRpZmllclwiKTtcbn07XG5cbi8vIFBhcnNlcyB5aWVsZCBleHByZXNzaW9uIGluc2lkZSBnZW5lcmF0b3IuXG5cbnBwLnBhcnNlWWllbGQgPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgdGhpcy5uZXh0KCk7XG4gIGlmICh0aGlzLnR5cGUgPT0gdHQuc2VtaSB8fCB0aGlzLmNhbkluc2VydFNlbWljb2xvbigpIHx8IHRoaXMudHlwZSAhPSB0dC5zdGFyICYmICF0aGlzLnR5cGUuc3RhcnRzRXhwcikge1xuICAgIG5vZGUuZGVsZWdhdGUgPSBmYWxzZTtcbiAgICBub2RlLmFyZ3VtZW50ID0gbnVsbDtcbiAgfSBlbHNlIHtcbiAgICBub2RlLmRlbGVnYXRlID0gdGhpcy5lYXQodHQuc3Rhcik7XG4gICAgbm9kZS5hcmd1bWVudCA9IHRoaXMucGFyc2VNYXliZUFzc2lnbigpO1xuICB9XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJZaWVsZEV4cHJlc3Npb25cIik7XG59O1xuXG4vLyBQYXJzZXMgYXJyYXkgYW5kIGdlbmVyYXRvciBjb21wcmVoZW5zaW9ucy5cblxucHAucGFyc2VDb21wcmVoZW5zaW9uID0gZnVuY3Rpb24gKG5vZGUsIGlzR2VuZXJhdG9yKSB7XG4gIG5vZGUuYmxvY2tzID0gW107XG4gIHdoaWxlICh0aGlzLnR5cGUgPT09IHR0Ll9mb3IpIHtcbiAgICB2YXIgYmxvY2sgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICAgIHRoaXMubmV4dCgpO1xuICAgIHRoaXMuZXhwZWN0KHR0LnBhcmVuTCk7XG4gICAgYmxvY2subGVmdCA9IHRoaXMucGFyc2VCaW5kaW5nQXRvbSgpO1xuICAgIHRoaXMuY2hlY2tMVmFsKGJsb2NrLmxlZnQsIHRydWUpO1xuICAgIHRoaXMuZXhwZWN0Q29udGV4dHVhbChcIm9mXCIpO1xuICAgIGJsb2NrLnJpZ2h0ID0gdGhpcy5wYXJzZUV4cHJlc3Npb24oKTtcbiAgICB0aGlzLmV4cGVjdCh0dC5wYXJlblIpO1xuICAgIG5vZGUuYmxvY2tzLnB1c2godGhpcy5maW5pc2hOb2RlKGJsb2NrLCBcIkNvbXByZWhlbnNpb25CbG9ja1wiKSk7XG4gIH1cbiAgbm9kZS5maWx0ZXIgPSB0aGlzLmVhdCh0dC5faWYpID8gdGhpcy5wYXJzZVBhcmVuRXhwcmVzc2lvbigpIDogbnVsbDtcbiAgbm9kZS5ib2R5ID0gdGhpcy5wYXJzZUV4cHJlc3Npb24oKTtcbiAgdGhpcy5leHBlY3QoaXNHZW5lcmF0b3IgPyB0dC5wYXJlblIgOiB0dC5icmFja2V0Uik7XG4gIG5vZGUuZ2VuZXJhdG9yID0gaXNHZW5lcmF0b3I7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJDb21wcmVoZW5zaW9uRXhwcmVzc2lvblwiKTtcbn07XG5cbn0se1wiLi9pZGVudGlmaWVyXCI6NyxcIi4vc3RhdGVcIjoxMyxcIi4vdG9rZW50eXBlXCI6MTcsXCIuL3V0aWxcIjoxOH1dLDc6W2Z1bmN0aW9uKF9kZXJlcV8sbW9kdWxlLGV4cG9ydHMpe1xuXG5cbi8vIFRlc3Qgd2hldGhlciBhIGdpdmVuIGNoYXJhY3RlciBjb2RlIHN0YXJ0cyBhbiBpZGVudGlmaWVyLlxuXG5cInVzZSBzdHJpY3RcIjtcblxuZXhwb3J0cy5pc0lkZW50aWZpZXJTdGFydCA9IGlzSWRlbnRpZmllclN0YXJ0O1xuXG4vLyBUZXN0IHdoZXRoZXIgYSBnaXZlbiBjaGFyYWN0ZXIgaXMgcGFydCBvZiBhbiBpZGVudGlmaWVyLlxuXG5leHBvcnRzLmlzSWRlbnRpZmllckNoYXIgPSBpc0lkZW50aWZpZXJDaGFyO1xuZXhwb3J0cy5fX2VzTW9kdWxlID0gdHJ1ZTtcbi8vIFRoaXMgaXMgYSB0cmljayB0YWtlbiBmcm9tIEVzcHJpbWEuIEl0IHR1cm5zIG91dCB0aGF0LCBvblxuLy8gbm9uLUNocm9tZSBicm93c2VycywgdG8gY2hlY2sgd2hldGhlciBhIHN0cmluZyBpcyBpbiBhIHNldCwgYVxuLy8gcHJlZGljYXRlIGNvbnRhaW5pbmcgYSBiaWcgdWdseSBgc3dpdGNoYCBzdGF0ZW1lbnQgaXMgZmFzdGVyIHRoYW5cbi8vIGEgcmVndWxhciBleHByZXNzaW9uLCBhbmQgb24gQ2hyb21lIHRoZSB0d28gYXJlIGFib3V0IG9uIHBhci5cbi8vIFRoaXMgZnVuY3Rpb24gdXNlcyBgZXZhbGAgKG5vbi1sZXhpY2FsKSB0byBwcm9kdWNlIHN1Y2ggYVxuLy8gcHJlZGljYXRlIGZyb20gYSBzcGFjZS1zZXBhcmF0ZWQgc3RyaW5nIG9mIHdvcmRzLlxuLy9cbi8vIEl0IHN0YXJ0cyBieSBzb3J0aW5nIHRoZSB3b3JkcyBieSBsZW5ndGguXG5cbmZ1bmN0aW9uIG1ha2VQcmVkaWNhdGUod29yZHMpIHtcbiAgd29yZHMgPSB3b3Jkcy5zcGxpdChcIiBcIik7XG4gIHZhciBmID0gXCJcIixcbiAgICAgIGNhdHMgPSBbXTtcbiAgb3V0OiBmb3IgKHZhciBpID0gMDsgaSA8IHdvcmRzLmxlbmd0aDsgKytpKSB7XG4gICAgZm9yICh2YXIgaiA9IDA7IGogPCBjYXRzLmxlbmd0aDsgKytqKSB7XG4gICAgICBpZiAoY2F0c1tqXVswXS5sZW5ndGggPT0gd29yZHNbaV0ubGVuZ3RoKSB7XG4gICAgICAgIGNhdHNbal0ucHVzaCh3b3Jkc1tpXSk7XG4gICAgICAgIGNvbnRpbnVlIG91dDtcbiAgICAgIH1cbiAgICB9Y2F0cy5wdXNoKFt3b3Jkc1tpXV0pO1xuICB9XG4gIGZ1bmN0aW9uIGNvbXBhcmVUbyhhcnIpIHtcbiAgICBpZiAoYXJyLmxlbmd0aCA9PSAxKSB7XG4gICAgICByZXR1cm4gZiArPSBcInJldHVybiBzdHIgPT09IFwiICsgSlNPTi5zdHJpbmdpZnkoYXJyWzBdKSArIFwiO1wiO1xuICAgIH1mICs9IFwic3dpdGNoKHN0cil7XCI7XG4gICAgZm9yICh2YXIgaSA9IDA7IGkgPCBhcnIubGVuZ3RoOyArK2kpIHtcbiAgICAgIGYgKz0gXCJjYXNlIFwiICsgSlNPTi5zdHJpbmdpZnkoYXJyW2ldKSArIFwiOlwiO1xuICAgIH1mICs9IFwicmV0dXJuIHRydWV9cmV0dXJuIGZhbHNlO1wiO1xuICB9XG5cbiAgLy8gV2hlbiB0aGVyZSBhcmUgbW9yZSB0aGFuIHRocmVlIGxlbmd0aCBjYXRlZ29yaWVzLCBhbiBvdXRlclxuICAvLyBzd2l0Y2ggZmlyc3QgZGlzcGF0Y2hlcyBvbiB0aGUgbGVuZ3RocywgdG8gc2F2ZSBvbiBjb21wYXJpc29ucy5cblxuICBpZiAoY2F0cy5sZW5ndGggPiAzKSB7XG4gICAgY2F0cy5zb3J0KGZ1bmN0aW9uIChhLCBiKSB7XG4gICAgICByZXR1cm4gYi5sZW5ndGggLSBhLmxlbmd0aDtcbiAgICB9KTtcbiAgICBmICs9IFwic3dpdGNoKHN0ci5sZW5ndGgpe1wiO1xuICAgIGZvciAodmFyIGkgPSAwOyBpIDwgY2F0cy5sZW5ndGg7ICsraSkge1xuICAgICAgdmFyIGNhdCA9IGNhdHNbaV07XG4gICAgICBmICs9IFwiY2FzZSBcIiArIGNhdFswXS5sZW5ndGggKyBcIjpcIjtcbiAgICAgIGNvbXBhcmVUbyhjYXQpO1xuICAgIH1cbiAgICBmICs9IFwifVwiXG5cbiAgICAvLyBPdGhlcndpc2UsIHNpbXBseSBnZW5lcmF0ZSBhIGZsYXQgYHN3aXRjaGAgc3RhdGVtZW50LlxuXG4gICAgO1xuICB9IGVsc2Uge1xuICAgIGNvbXBhcmVUbyh3b3Jkcyk7XG4gIH1cbiAgcmV0dXJuIG5ldyBGdW5jdGlvbihcInN0clwiLCBmKTtcbn1cblxuLy8gUmVzZXJ2ZWQgd29yZCBsaXN0cyBmb3IgdmFyaW91cyBkaWFsZWN0cyBvZiB0aGUgbGFuZ3VhZ2VcblxudmFyIHJlc2VydmVkV29yZHMgPSB7XG4gIDM6IG1ha2VQcmVkaWNhdGUoXCJhYnN0cmFjdCBib29sZWFuIGJ5dGUgY2hhciBjbGFzcyBkb3VibGUgZW51bSBleHBvcnQgZXh0ZW5kcyBmaW5hbCBmbG9hdCBnb3RvIGltcGxlbWVudHMgaW1wb3J0IGludCBpbnRlcmZhY2UgbG9uZyBuYXRpdmUgcGFja2FnZSBwcml2YXRlIHByb3RlY3RlZCBwdWJsaWMgc2hvcnQgc3RhdGljIHN1cGVyIHN5bmNocm9uaXplZCB0aHJvd3MgdHJhbnNpZW50IHZvbGF0aWxlXCIpLFxuICA1OiBtYWtlUHJlZGljYXRlKFwiY2xhc3MgZW51bSBleHRlbmRzIHN1cGVyIGNvbnN0IGV4cG9ydCBpbXBvcnRcIiksXG4gIDY6IG1ha2VQcmVkaWNhdGUoXCJlbnVtIGF3YWl0XCIpLFxuICBzdHJpY3Q6IG1ha2VQcmVkaWNhdGUoXCJpbXBsZW1lbnRzIGludGVyZmFjZSBsZXQgcGFja2FnZSBwcml2YXRlIHByb3RlY3RlZCBwdWJsaWMgc3RhdGljIHlpZWxkXCIpLFxuICBzdHJpY3RCaW5kOiBtYWtlUHJlZGljYXRlKFwiZXZhbCBhcmd1bWVudHNcIilcbn07XG5cbmV4cG9ydHMucmVzZXJ2ZWRXb3JkcyA9IHJlc2VydmVkV29yZHM7XG4vLyBBbmQgdGhlIGtleXdvcmRzXG5cbnZhciBlY21hNUFuZExlc3NLZXl3b3JkcyA9IFwiYnJlYWsgY2FzZSBjYXRjaCBjb250aW51ZSBkZWJ1Z2dlciBkZWZhdWx0IGRvIGVsc2UgZmluYWxseSBmb3IgZnVuY3Rpb24gaWYgcmV0dXJuIHN3aXRjaCB0aHJvdyB0cnkgdmFyIHdoaWxlIHdpdGggbnVsbCB0cnVlIGZhbHNlIGluc3RhbmNlb2YgdHlwZW9mIHZvaWQgZGVsZXRlIG5ldyBpbiB0aGlzXCI7XG5cbnZhciBrZXl3b3JkcyA9IHtcbiAgNTogbWFrZVByZWRpY2F0ZShlY21hNUFuZExlc3NLZXl3b3JkcyksXG4gIDY6IG1ha2VQcmVkaWNhdGUoZWNtYTVBbmRMZXNzS2V5d29yZHMgKyBcIiBsZXQgY29uc3QgY2xhc3MgZXh0ZW5kcyBleHBvcnQgaW1wb3J0IHlpZWxkIHN1cGVyXCIpXG59O1xuXG5leHBvcnRzLmtleXdvcmRzID0ga2V5d29yZHM7XG4vLyAjIyBDaGFyYWN0ZXIgY2F0ZWdvcmllc1xuXG4vLyBCaWcgdWdseSByZWd1bGFyIGV4cHJlc3Npb25zIHRoYXQgbWF0Y2ggY2hhcmFjdGVycyBpbiB0aGVcbi8vIHdoaXRlc3BhY2UsIGlkZW50aWZpZXIsIGFuZCBpZGVudGlmaWVyLXN0YXJ0IGNhdGVnb3JpZXMuIFRoZXNlXG4vLyBhcmUgb25seSBhcHBsaWVkIHdoZW4gYSBjaGFyYWN0ZXIgaXMgZm91bmQgdG8gYWN0dWFsbHkgaGF2ZSBhXG4vLyBjb2RlIHBvaW50IGFib3ZlIDEyOC5cbi8vIEdlbmVyYXRlZCBieSBgdG9vbHMvZ2VuZXJhdGUtaWRlbnRpZmllci1yZWdleC5qc2AuXG5cbnZhciBub25BU0NJSWlkZW50aWZpZXJTdGFydENoYXJzID0gXCLCqsK1wrrDgC3DlsOYLcO2w7gty4HLhi3LkcugLcuky6zLrs2wLc20zbbNt826Lc29zb/Ohs6ILc6KzozOji3Ooc6jLc+1z7ct0oHSii3Ur9SxLdWW1ZnVoS3Wh9eQLdeq17At17LYoC3Zitmu2a/ZsS3bk9uV26Xbptuu26/bui3bvNu/3JDcki3cr92NLd6l3rHfii3fqt+037XfuuCggC3goJXgoJrgoKTgoKjgoYAt4KGY4KKgLeCisuCkhC3gpLngpL3gpZDgpZgt4KWh4KWxLeCmgOCmhS3gpozgpo/gppDgppMt4Kao4KaqLeCmsOCmsuCmti3gprngpr3gp47gp5zgp53gp58t4Keh4Kew4Kex4KiFLeCoiuCoj+CokOCoky3gqKjgqKot4Kiw4Kiy4Kiz4Ki14Ki24Ki44Ki54KmZLeCpnOCpnuCpsi3gqbTgqoUt4KqN4KqPLeCqkeCqky3gqqjgqqot4Kqw4Kqy4Kqz4Kq1LeCqueCqveCrkOCroOCroeCshS3grIzgrI/grJDgrJMt4Kyo4KyqLeCssOCssuCss+CstS3grLngrL3grZzgrZ3grZ8t4K2h4K2x4K6D4K6FLeCuiuCuji3grpDgrpIt4K6V4K6Z4K6a4K6c4K6e4K6f4K6j4K6k4K6oLeCuquCuri3grrngr5DgsIUt4LCM4LCOLeCwkOCwki3gsKjgsKot4LC54LC94LGY4LGZ4LGg4LGh4LKFLeCyjOCyji3gspDgspIt4LKo4LKqLeCys+CytS3gsrngsr3gs57gs6Dgs6Hgs7Hgs7LgtIUt4LSM4LSOLeC0kOC0ki3gtLrgtL3gtY7gtaDgtaHgtbot4LW/4LaFLeC2luC2mi3gtrHgtrMt4La74La94LeALeC3huC4gS3guLDguLLguLPguYAt4LmG4LqB4LqC4LqE4LqH4LqI4LqK4LqN4LqULeC6l+C6mS3gup/guqEt4Lqj4Lql4Lqn4Lqq4Lqr4LqtLeC6sOC6suC6s+C6veC7gC3gu4Tgu4bgu5wt4Luf4LyA4L2ALeC9h+C9iS3gvazgvogt4L6M4YCALeGAquGAv+GBkC3hgZXhgZot4YGd4YGh4YGl4YGm4YGuLeGBsOGBtS3hgoHhgo7hgqAt4YOF4YOH4YON4YOQLeGDuuGDvC3hiYjhiYot4YmN4YmQLeGJluGJmOGJmi3hiZ3hiaAt4YqI4YqKLeGKjeGKkC3hirDhirIt4Yq14Yq4LeGKvuGLgOGLgi3hi4Xhi4gt4YuW4YuYLeGMkOGMki3hjJXhjJgt4Y2a4Y6ALeGOj+GOoC3hj7ThkIEt4Zms4ZmvLeGZv+GagS3hmprhmqAt4Zuq4ZuuLeGbuOGcgC3hnIzhnI4t4ZyR4ZygLeGcseGdgC3hnZHhnaAt4Z2s4Z2uLeGdsOGegC3hnrPhn5fhn5zhoKAt4aG34aKALeGiqOGiquGisC3ho7XhpIAt4aSe4aWQLeGlreGlsC3hpbThpoAt4aar4aeBLeGnh+GogC3hqJbhqKAt4amU4aqn4ayFLeGss+GthS3hrYvhroMt4a6g4a6u4a6v4a66LeGvpeGwgC3hsKPhsY0t4bGP4bGaLeGxveGzqS3hs6zhs64t4bOx4bO14bO24bSALeG2v+G4gC3hvJXhvJgt4byd4bygLeG9heG9iC3hvY3hvZAt4b2X4b2Z4b2b4b2d4b2fLeG9veG+gC3hvrThvrYt4b684b6+4b+CLeG/hOG/hi3hv4zhv5At4b+T4b+WLeG/m+G/oC3hv6zhv7It4b+04b+2LeG/vOKBseKBv+KCkC3igpzihILihIfihIot4oST4oSV4oSYLeKEneKEpOKEpuKEqOKEqi3ihLnihLwt4oS/4oWFLeKFieKFjuKFoC3ihojisIAt4rCu4rCwLeKxnuKxoC3is6Tis6st4rOu4rOy4rOz4rSALeK0peK0p+K0reK0sC3itafita/itoAt4raW4ragLeK2puK2qC3itq7itrAt4ra24ra4LeK2vuK3gC3it4bit4gt4reO4reQLeK3luK3mC3it57jgIUt44CH44ChLeOAqeOAsS3jgLXjgLgt44C844GBLeOCluOCmy3jgp/jgqEt44O644O8LeODv+OEhS3jhK3jhLEt44aO44agLeOGuuOHsC3jh7/jkIAt5La15LiALem/jOqAgC3qkozqk5At6pO96pSALeqYjOqYkC3qmJ/qmKrqmKvqmYAt6pmu6pm/LeqaneqaoC3qm6/qnJct6pyf6pyiLeqeiOqeiy3qno7qnpAt6p6t6p6w6p6x6p+3Leqggeqggy3qoIXqoIct6qCK6qCMLeqgouqhgC3qobPqooIt6qKz6qOyLeqjt+qju+qkii3qpKXqpLAt6qWG6qWgLeqlvOqmhC3qprLqp4/qp6At6qek6qemLeqnr+qnui3qp77qqIAt6qio6qmALeqpguqphC3qqYvqqaAt6qm26qm66qm+Leqqr+qqseqqteqqtuqquS3qqr3qq4Dqq4Lqq5st6qud6qugLeqrquqrsi3qq7TqrIEt6qyG6qyJLeqsjuqskS3qrJbqrKAt6qym6qyoLeqsruqssC3qrZrqrZwt6q2f6q2k6q2l6q+ALeqvouqwgC3tnqPtnrAt7Z+G7Z+LLe2fu++kgC3vqa3vqbAt76uZ76yALe+shu+sky3vrJfvrJ3vrJ8t76yo76yqLe+stu+suC3vrLzvrL7vrYDvrYHvrYPvrYTvrYYt766x76+TLe+0ve+1kC3vto/vtpIt77eH77ewLe+3u++5sC3vubTvubYt77u877yhLe+8uu+9gS3vvZrvvaYt776+77+CLe+/h++/ii3vv4/vv5It77+X77+aLe+/nFwiO1xudmFyIG5vbkFTQ0lJaWRlbnRpZmllckNoYXJzID0gXCLigIzigI3Ct8yALc2vzofSgy3Sh9aRLda91r/XgdeC14TXhdeH2JAt2JrZiy3Zqdmw25Yt25zbny3bpNun26jbqi3brduwLdu53JHcsC3dit6mLd6w34At34nfqy3fs+Cgli3goJngoJst4KCj4KClLeCgp+CgqS3goK3goZkt4KGb4KOkLeCkg+Ckui3gpLzgpL4t4KWP4KWRLeCll+ClouClo+Clpi3gpa/gpoEt4KaD4Ka84Ka+LeCnhOCnh+CniOCniy3gp43gp5fgp6Lgp6Pgp6Yt4Kev4KiBLeCog+CovOCovi3gqYLgqYfgqYjgqYst4KmN4KmR4KmmLeCpseCpteCqgS3gqoPgqrzgqr4t4KuF4KuHLeCrieCriy3gq43gq6Lgq6Pgq6Yt4Kuv4KyBLeCsg+CsvOCsvi3grYTgrYfgrYjgrYst4K2N4K2W4K2X4K2i4K2j4K2mLeCtr+CuguCuvi3gr4Lgr4Yt4K+I4K+KLeCvjeCvl+Cvpi3gr6/gsIAt4LCD4LC+LeCxhOCxhi3gsYjgsYot4LGN4LGV4LGW4LGi4LGj4LGmLeCxr+CygS3gsoPgsrzgsr4t4LOE4LOGLeCziOCzii3gs43gs5Xgs5bgs6Lgs6Pgs6Yt4LOv4LSBLeC0g+C0vi3gtYTgtYYt4LWI4LWKLeC1jeC1l+C1ouC1o+C1pi3gta/gtoLgtoPgt4rgt48t4LeU4LeW4LeYLeC3n+C3pi3gt6/gt7Lgt7PguLHguLQt4Li64LmHLeC5juC5kC3guZngurHgurQt4Lq54Lq74Lq84LuILeC7jeC7kC3gu5ngvJjgvJngvKAt4Lyp4Ly14Ly34Ly54Ly+4Ly/4L2xLeC+hOC+huC+h+C+jS3gvpfgvpkt4L684L+G4YCrLeGAvuGBgC3hgYnhgZYt4YGZ4YGeLeGBoOGBoi3hgaThgact4YGt4YGxLeGBtOGCgi3hgo3hgo8t4YKd4Y2dLeGNn+GNqS3hjbHhnJIt4ZyU4ZyyLeGctOGdkuGdk+GdsuGds+GetC3hn5Phn53hn6At4Z+p4aCLLeGgjeGgkC3hoJnhoqnhpKAt4aSr4aSwLeGku+Glhi3hpY/hprAt4aeA4aeI4aeJ4aeQLeGnmuGoly3hqJvhqZUt4ame4amgLeGpvOGpvy3hqonhqpAt4aqZ4aqwLeGqveGsgC3hrIThrLQt4a2E4a2QLeGtmeGtqy3hrbPhroAt4a6C4a6hLeGureGusC3hrrnhr6Yt4a+z4bCkLeGwt+GxgC3hsYnhsZAt4bGZ4bOQLeGzkuGzlC3hs6jhs63hs7It4bO04bO44bO54beALeG3teG3vC3ht7/igL/igYDigZTig5At4oOc4oOh4oOlLeKDsOKzry3is7Hitb/it6At4re/44CqLeOAr+OCmeOCmuqYoC3qmKnqma/qmbQt6pm96pqf6puw6pux6qCC6qCG6qCL6qCjLeqgp+qigOqigeqitC3qo4Tqo5At6qOZ6qOgLeqjseqkgC3qpInqpKYt6qSt6qWHLeqlk+qmgC3qpoPqprMt6qeA6qeQLeqnmeqnpeqnsC3qp7nqqKkt6qi26qmD6qmM6qmN6qmQLeqpmeqpuy3qqb3qqrDqqrIt6qq06qq36qq46qq+6qq/6quB6qurLeqrr+qrteqrtuqvoy3qr6rqr6zqr63qr7At6q+576ye77iALe+4j++4oC3vuK3vuLPvuLTvuY0t77mP77yQLe+8me+8v1wiO1xuXG52YXIgbm9uQVNDSUlpZGVudGlmaWVyU3RhcnQgPSBuZXcgUmVnRXhwKFwiW1wiICsgbm9uQVNDSUlpZGVudGlmaWVyU3RhcnRDaGFycyArIFwiXVwiKTtcbnZhciBub25BU0NJSWlkZW50aWZpZXIgPSBuZXcgUmVnRXhwKFwiW1wiICsgbm9uQVNDSUlpZGVudGlmaWVyU3RhcnRDaGFycyArIG5vbkFTQ0lJaWRlbnRpZmllckNoYXJzICsgXCJdXCIpO1xuXG5ub25BU0NJSWlkZW50aWZpZXJTdGFydENoYXJzID0gbm9uQVNDSUlpZGVudGlmaWVyQ2hhcnMgPSBudWxsO1xuXG4vLyBUaGVzZSBhcmUgYSBydW4tbGVuZ3RoIGFuZCBvZmZzZXQgZW5jb2RlZCByZXByZXNlbnRhdGlvbiBvZiB0aGVcbi8vID4weGZmZmYgY29kZSBwb2ludHMgdGhhdCBhcmUgYSB2YWxpZCBwYXJ0IG9mIGlkZW50aWZpZXJzLiBUaGVcbi8vIG9mZnNldCBzdGFydHMgYXQgMHgxMDAwMCwgYW5kIGVhY2ggcGFpciBvZiBudW1iZXJzIHJlcHJlc2VudHMgYW5cbi8vIG9mZnNldCB0byB0aGUgbmV4dCByYW5nZSwgYW5kIHRoZW4gYSBzaXplIG9mIHRoZSByYW5nZS4gVGhleSB3ZXJlXG4vLyBnZW5lcmF0ZWQgYnkgdG9vbHMvZ2VuZXJhdGUtaWRlbnRpZmllci1yZWdleC5qc1xudmFyIGFzdHJhbElkZW50aWZpZXJTdGFydENvZGVzID0gWzAsIDExLCAyLCAyNSwgMiwgMTgsIDIsIDEsIDIsIDE0LCAzLCAxMywgMzUsIDEyMiwgNzAsIDUyLCAyNjgsIDI4LCA0LCA0OCwgNDgsIDMxLCAxNywgMjYsIDYsIDM3LCAxMSwgMjksIDMsIDM1LCA1LCA3LCAyLCA0LCA0MywgMTU3LCA5OSwgMzksIDksIDUxLCAxNTcsIDMxMCwgMTAsIDIxLCAxMSwgNywgMTUzLCA1LCAzLCAwLCAyLCA0MywgMiwgMSwgNCwgMCwgMywgMjIsIDExLCAyMiwgMTAsIDMwLCA5OCwgMjEsIDExLCAyNSwgNzEsIDU1LCA3LCAxLCA2NSwgMCwgMTYsIDMsIDIsIDIsIDIsIDI2LCA0NSwgMjgsIDQsIDI4LCAzNiwgNywgMiwgMjcsIDI4LCA1MywgMTEsIDIxLCAxMSwgMTgsIDE0LCAxNywgMTExLCA3MiwgOTU1LCA1MiwgNzYsIDQ0LCAzMywgMjQsIDI3LCAzNSwgNDIsIDM0LCA0LCAwLCAxMywgNDcsIDE1LCAzLCAyMiwgMCwgMzgsIDE3LCAyLCAyNCwgMTMzLCA0NiwgMzksIDcsIDMsIDEsIDMsIDIxLCAyLCA2LCAyLCAxLCAyLCA0LCA0LCAwLCAzMiwgNCwgMjg3LCA0NywgMjEsIDEsIDIsIDAsIDE4NSwgNDYsIDgyLCA0NywgMjEsIDAsIDYwLCA0MiwgNTAyLCA2MywgMzIsIDAsIDQ0OSwgNTYsIDEyODgsIDkyMCwgMTA0LCAxMTAsIDI5NjIsIDEwNzAsIDEzMjY2LCA1NjgsIDgsIDMwLCAxMTQsIDI5LCAxOSwgNDcsIDE3LCAzLCAzMiwgMjAsIDYsIDE4LCA4ODEsIDY4LCAxMiwgMCwgNjcsIDEyLCAxNjQ4MSwgMSwgMzA3MSwgMTA2LCA2LCAxMiwgNCwgOCwgOCwgOSwgNTk5MSwgODQsIDIsIDcwLCAyLCAxLCAzLCAwLCAzLCAxLCAzLCAzLCAyLCAxMSwgMiwgMCwgMiwgNiwgMiwgNjQsIDIsIDMsIDMsIDcsIDIsIDYsIDIsIDI3LCAyLCAzLCAyLCA0LCAyLCAwLCA0LCA2LCAyLCAzMzksIDMsIDI0LCAyLCAyNCwgMiwgMzAsIDIsIDI0LCAyLCAzMCwgMiwgMjQsIDIsIDMwLCAyLCAyNCwgMiwgMzAsIDIsIDI0LCAyLCA3LCA0MTQ5LCAxOTYsIDEzNDAsIDMsIDIsIDI2LCAyLCAxLCAyLCAwLCAzLCAwLCAyLCA5LCAyLCAzLCAyLCAwLCAyLCAwLCA3LCAwLCA1LCAwLCAyLCAwLCAyLCAwLCAyLCAyLCAyLCAxLCAyLCAwLCAzLCAwLCAyLCAwLCAyLCAwLCAyLCAwLCAyLCAwLCAyLCAxLCAyLCAwLCAzLCAzLCAyLCA2LCAyLCAzLCAyLCAzLCAyLCAwLCAyLCA5LCAyLCAxNiwgNiwgMiwgMiwgNCwgMiwgMTYsIDQ0MjEsIDQyNzEwLCA0MiwgNDE0OCwgMTIsIDIyMSwgMTYzNTUsIDU0MV07XG52YXIgYXN0cmFsSWRlbnRpZmllckNvZGVzID0gWzUwOSwgMCwgMjI3LCAwLCAxNTAsIDQsIDI5NCwgOSwgMTM2OCwgMiwgMiwgMSwgNiwgMywgNDEsIDIsIDUsIDAsIDE2NiwgMSwgMTMwNiwgMiwgNTQsIDE0LCAzMiwgOSwgMTYsIDMsIDQ2LCAxMCwgNTQsIDksIDcsIDIsIDM3LCAxMywgMiwgOSwgNTIsIDAsIDEzLCAyLCA0OSwgMTMsIDE2LCA5LCA4MywgMTEsIDE2OCwgMTEsIDYsIDksIDgsIDIsIDU3LCAwLCAyLCA2LCAzLCAxLCAzLCAyLCAxMCwgMCwgMTEsIDEsIDMsIDYsIDQsIDQsIDMxNiwgMTksIDEzLCA5LCAyMTQsIDYsIDMsIDgsIDExMiwgMTYsIDE2LCA5LCA4MiwgMTIsIDksIDksIDUzNSwgOSwgMjA4NTUsIDksIDEzNSwgNCwgNjAsIDYsIDI2LCA5LCAxMDE2LCA0NSwgMTcsIDMsIDE5NzIzLCAxLCA1MzE5LCA0LCA0LCA1LCA5LCA3LCAzLCA2LCAzMSwgMywgMTQ5LCAyLCAxNDE4LCA0OSwgNDMwNSwgNiwgNzkyNjE4LCAyMzldO1xuXG4vLyBUaGlzIGhhcyBhIGNvbXBsZXhpdHkgbGluZWFyIHRvIHRoZSB2YWx1ZSBvZiB0aGUgY29kZS4gVGhlXG4vLyBhc3N1bXB0aW9uIGlzIHRoYXQgbG9va2luZyB1cCBhc3RyYWwgaWRlbnRpZmllciBjaGFyYWN0ZXJzIGlzXG4vLyByYXJlLlxuZnVuY3Rpb24gaXNJbkFzdHJhbFNldChjb2RlLCBzZXQpIHtcbiAgdmFyIHBvcyA9IDY1NTM2O1xuICBmb3IgKHZhciBpID0gMDsgaSA8IHNldC5sZW5ndGg7IGkgKz0gMikge1xuICAgIHBvcyArPSBzZXRbaV07XG4gICAgaWYgKHBvcyA+IGNvZGUpIHtcbiAgICAgIHJldHVybiBmYWxzZTtcbiAgICB9cG9zICs9IHNldFtpICsgMV07XG4gICAgaWYgKHBvcyA+PSBjb2RlKSB7XG4gICAgICByZXR1cm4gdHJ1ZTtcbiAgICB9XG4gIH1cbn1cbmZ1bmN0aW9uIGlzSWRlbnRpZmllclN0YXJ0KGNvZGUsIGFzdHJhbCkge1xuICBpZiAoY29kZSA8IDY1KSB7XG4gICAgcmV0dXJuIGNvZGUgPT09IDM2O1xuICB9aWYgKGNvZGUgPCA5MSkge1xuICAgIHJldHVybiB0cnVlO1xuICB9aWYgKGNvZGUgPCA5Nykge1xuICAgIHJldHVybiBjb2RlID09PSA5NTtcbiAgfWlmIChjb2RlIDwgMTIzKSB7XG4gICAgcmV0dXJuIHRydWU7XG4gIH1pZiAoY29kZSA8PSA2NTUzNSkge1xuICAgIHJldHVybiBjb2RlID49IDE3MCAmJiBub25BU0NJSWlkZW50aWZpZXJTdGFydC50ZXN0KFN0cmluZy5mcm9tQ2hhckNvZGUoY29kZSkpO1xuICB9aWYgKGFzdHJhbCA9PT0gZmFsc2UpIHtcbiAgICByZXR1cm4gZmFsc2U7XG4gIH1yZXR1cm4gaXNJbkFzdHJhbFNldChjb2RlLCBhc3RyYWxJZGVudGlmaWVyU3RhcnRDb2Rlcyk7XG59XG5cbmZ1bmN0aW9uIGlzSWRlbnRpZmllckNoYXIoY29kZSwgYXN0cmFsKSB7XG4gIGlmIChjb2RlIDwgNDgpIHtcbiAgICByZXR1cm4gY29kZSA9PT0gMzY7XG4gIH1pZiAoY29kZSA8IDU4KSB7XG4gICAgcmV0dXJuIHRydWU7XG4gIH1pZiAoY29kZSA8IDY1KSB7XG4gICAgcmV0dXJuIGZhbHNlO1xuICB9aWYgKGNvZGUgPCA5MSkge1xuICAgIHJldHVybiB0cnVlO1xuICB9aWYgKGNvZGUgPCA5Nykge1xuICAgIHJldHVybiBjb2RlID09PSA5NTtcbiAgfWlmIChjb2RlIDwgMTIzKSB7XG4gICAgcmV0dXJuIHRydWU7XG4gIH1pZiAoY29kZSA8PSA2NTUzNSkge1xuICAgIHJldHVybiBjb2RlID49IDE3MCAmJiBub25BU0NJSWlkZW50aWZpZXIudGVzdChTdHJpbmcuZnJvbUNoYXJDb2RlKGNvZGUpKTtcbiAgfWlmIChhc3RyYWwgPT09IGZhbHNlKSB7XG4gICAgcmV0dXJuIGZhbHNlO1xuICB9cmV0dXJuIGlzSW5Bc3RyYWxTZXQoY29kZSwgYXN0cmFsSWRlbnRpZmllclN0YXJ0Q29kZXMpIHx8IGlzSW5Bc3RyYWxTZXQoY29kZSwgYXN0cmFsSWRlbnRpZmllckNvZGVzKTtcbn1cblxufSx7fV0sODpbZnVuY3Rpb24oX2RlcmVxXyxtb2R1bGUsZXhwb3J0cyl7XG5cInVzZSBzdHJpY3RcIjtcblxudmFyIF9jbGFzc0NhbGxDaGVjayA9IGZ1bmN0aW9uIChpbnN0YW5jZSwgQ29uc3RydWN0b3IpIHsgaWYgKCEoaW5zdGFuY2UgaW5zdGFuY2VvZiBDb25zdHJ1Y3RvcikpIHsgdGhyb3cgbmV3IFR5cGVFcnJvcihcIkNhbm5vdCBjYWxsIGEgY2xhc3MgYXMgYSBmdW5jdGlvblwiKTsgfSB9O1xuXG4vLyBUaGUgYGdldExpbmVJbmZvYCBmdW5jdGlvbiBpcyBtb3N0bHkgdXNlZnVsIHdoZW4gdGhlXG4vLyBgbG9jYXRpb25zYCBvcHRpb24gaXMgb2ZmIChmb3IgcGVyZm9ybWFuY2UgcmVhc29ucykgYW5kIHlvdVxuLy8gd2FudCB0byBmaW5kIHRoZSBsaW5lL2NvbHVtbiBwb3NpdGlvbiBmb3IgYSBnaXZlbiBjaGFyYWN0ZXJcbi8vIG9mZnNldC4gYGlucHV0YCBzaG91bGQgYmUgdGhlIGNvZGUgc3RyaW5nIHRoYXQgdGhlIG9mZnNldCByZWZlcnNcbi8vIGludG8uXG5cbmV4cG9ydHMuZ2V0TGluZUluZm8gPSBnZXRMaW5lSW5mbztcbmV4cG9ydHMuX19lc01vZHVsZSA9IHRydWU7XG5cbnZhciBQYXJzZXIgPSBfZGVyZXFfKFwiLi9zdGF0ZVwiKS5QYXJzZXI7XG5cbnZhciBsaW5lQnJlYWtHID0gX2RlcmVxXyhcIi4vd2hpdGVzcGFjZVwiKS5saW5lQnJlYWtHO1xuXG52YXIgZGVwcmVjYXRlID0gX2RlcmVxXyhcInV0aWxcIikuZGVwcmVjYXRlO1xuXG4vLyBUaGVzZSBhcmUgdXNlZCB3aGVuIGBvcHRpb25zLmxvY2F0aW9uc2AgaXMgb24sIGZvciB0aGVcbi8vIGBzdGFydExvY2AgYW5kIGBlbmRMb2NgIHByb3BlcnRpZXMuXG5cbnZhciBQb3NpdGlvbiA9IGV4cG9ydHMuUG9zaXRpb24gPSAoZnVuY3Rpb24gKCkge1xuICBmdW5jdGlvbiBQb3NpdGlvbihsaW5lLCBjb2wpIHtcbiAgICBfY2xhc3NDYWxsQ2hlY2sodGhpcywgUG9zaXRpb24pO1xuXG4gICAgdGhpcy5saW5lID0gbGluZTtcbiAgICB0aGlzLmNvbHVtbiA9IGNvbDtcbiAgfVxuXG4gIFBvc2l0aW9uLnByb3RvdHlwZS5vZmZzZXQgPSBmdW5jdGlvbiBvZmZzZXQobikge1xuICAgIHJldHVybiBuZXcgUG9zaXRpb24odGhpcy5saW5lLCB0aGlzLmNvbHVtbiArIG4pO1xuICB9O1xuXG4gIHJldHVybiBQb3NpdGlvbjtcbn0pKCk7XG5cbnZhciBTb3VyY2VMb2NhdGlvbiA9IGV4cG9ydHMuU291cmNlTG9jYXRpb24gPSBmdW5jdGlvbiBTb3VyY2VMb2NhdGlvbihwLCBzdGFydCwgZW5kKSB7XG4gIF9jbGFzc0NhbGxDaGVjayh0aGlzLCBTb3VyY2VMb2NhdGlvbik7XG5cbiAgdGhpcy5zdGFydCA9IHN0YXJ0O1xuICB0aGlzLmVuZCA9IGVuZDtcbiAgaWYgKHAuc291cmNlRmlsZSAhPT0gbnVsbCkgdGhpcy5zb3VyY2UgPSBwLnNvdXJjZUZpbGU7XG59O1xuXG5mdW5jdGlvbiBnZXRMaW5lSW5mbyhpbnB1dCwgb2Zmc2V0KSB7XG4gIGZvciAodmFyIGxpbmUgPSAxLCBjdXIgPSAwOzspIHtcbiAgICBsaW5lQnJlYWtHLmxhc3RJbmRleCA9IGN1cjtcbiAgICB2YXIgbWF0Y2ggPSBsaW5lQnJlYWtHLmV4ZWMoaW5wdXQpO1xuICAgIGlmIChtYXRjaCAmJiBtYXRjaC5pbmRleCA8IG9mZnNldCkge1xuICAgICAgKytsaW5lO1xuICAgICAgY3VyID0gbWF0Y2guaW5kZXggKyBtYXRjaFswXS5sZW5ndGg7XG4gICAgfSBlbHNlIHtcbiAgICAgIHJldHVybiBuZXcgUG9zaXRpb24obGluZSwgb2Zmc2V0IC0gY3VyKTtcbiAgICB9XG4gIH1cbn1cblxudmFyIHBwID0gUGFyc2VyLnByb3RvdHlwZTtcblxuLy8gVGhpcyBmdW5jdGlvbiBpcyB1c2VkIHRvIHJhaXNlIGV4Y2VwdGlvbnMgb24gcGFyc2UgZXJyb3JzLiBJdFxuLy8gdGFrZXMgYW4gb2Zmc2V0IGludGVnZXIgKGludG8gdGhlIGN1cnJlbnQgYGlucHV0YCkgdG8gaW5kaWNhdGVcbi8vIHRoZSBsb2NhdGlvbiBvZiB0aGUgZXJyb3IsIGF0dGFjaGVzIHRoZSBwb3NpdGlvbiB0byB0aGUgZW5kXG4vLyBvZiB0aGUgZXJyb3IgbWVzc2FnZSwgYW5kIHRoZW4gcmFpc2VzIGEgYFN5bnRheEVycm9yYCB3aXRoIHRoYXRcbi8vIG1lc3NhZ2UuXG5cbnBwLnJhaXNlID0gZnVuY3Rpb24gKHBvcywgbWVzc2FnZSkge1xuICB2YXIgbG9jID0gZ2V0TGluZUluZm8odGhpcy5pbnB1dCwgcG9zKTtcbiAgbWVzc2FnZSArPSBcIiAoXCIgKyBsb2MubGluZSArIFwiOlwiICsgbG9jLmNvbHVtbiArIFwiKVwiO1xuICB2YXIgZXJyID0gbmV3IFN5bnRheEVycm9yKG1lc3NhZ2UpO1xuICBlcnIucG9zID0gcG9zO2Vyci5sb2MgPSBsb2M7ZXJyLnJhaXNlZEF0ID0gdGhpcy5wb3M7XG4gIHRocm93IGVycjtcbn07XG5cbnBwLmN1clBvc2l0aW9uID0gZnVuY3Rpb24gKCkge1xuICByZXR1cm4gbmV3IFBvc2l0aW9uKHRoaXMuY3VyTGluZSwgdGhpcy5wb3MgLSB0aGlzLmxpbmVTdGFydCk7XG59O1xuXG5wcC5tYXJrUG9zaXRpb24gPSBmdW5jdGlvbiAoKSB7XG4gIHJldHVybiB0aGlzLm9wdGlvbnMubG9jYXRpb25zID8gW3RoaXMuc3RhcnQsIHRoaXMuc3RhcnRMb2NdIDogdGhpcy5zdGFydDtcbn07XG5cbn0se1wiLi9zdGF0ZVwiOjEzLFwiLi93aGl0ZXNwYWNlXCI6MTksXCJ1dGlsXCI6NX1dLDk6W2Z1bmN0aW9uKF9kZXJlcV8sbW9kdWxlLGV4cG9ydHMpe1xuXCJ1c2Ugc3RyaWN0XCI7XG5cbnZhciB0dCA9IF9kZXJlcV8oXCIuL3Rva2VudHlwZVwiKS50eXBlcztcblxudmFyIFBhcnNlciA9IF9kZXJlcV8oXCIuL3N0YXRlXCIpLlBhcnNlcjtcblxudmFyIHJlc2VydmVkV29yZHMgPSBfZGVyZXFfKFwiLi9pZGVudGlmaWVyXCIpLnJlc2VydmVkV29yZHM7XG5cbnZhciBoYXMgPSBfZGVyZXFfKFwiLi91dGlsXCIpLmhhcztcblxudmFyIHBwID0gUGFyc2VyLnByb3RvdHlwZTtcblxuLy8gQ29udmVydCBleGlzdGluZyBleHByZXNzaW9uIGF0b20gdG8gYXNzaWduYWJsZSBwYXR0ZXJuXG4vLyBpZiBwb3NzaWJsZS5cblxucHAudG9Bc3NpZ25hYmxlID0gZnVuY3Rpb24gKG5vZGUsIGlzQmluZGluZykge1xuICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYgJiYgbm9kZSkge1xuICAgIHN3aXRjaCAobm9kZS50eXBlKSB7XG4gICAgICBjYXNlIFwiSWRlbnRpZmllclwiOlxuICAgICAgY2FzZSBcIk9iamVjdFBhdHRlcm5cIjpcbiAgICAgIGNhc2UgXCJBcnJheVBhdHRlcm5cIjpcbiAgICAgIGNhc2UgXCJBc3NpZ25tZW50UGF0dGVyblwiOlxuICAgICAgICBicmVhaztcblxuICAgICAgY2FzZSBcIk9iamVjdEV4cHJlc3Npb25cIjpcbiAgICAgICAgbm9kZS50eXBlID0gXCJPYmplY3RQYXR0ZXJuXCI7XG4gICAgICAgIGZvciAodmFyIGkgPSAwOyBpIDwgbm9kZS5wcm9wZXJ0aWVzLmxlbmd0aDsgaSsrKSB7XG4gICAgICAgICAgdmFyIHByb3AgPSBub2RlLnByb3BlcnRpZXNbaV07XG4gICAgICAgICAgaWYgKHByb3Aua2luZCAhPT0gXCJpbml0XCIpIHRoaXMucmFpc2UocHJvcC5rZXkuc3RhcnQsIFwiT2JqZWN0IHBhdHRlcm4gY2FuJ3QgY29udGFpbiBnZXR0ZXIgb3Igc2V0dGVyXCIpO1xuICAgICAgICAgIHRoaXMudG9Bc3NpZ25hYmxlKHByb3AudmFsdWUsIGlzQmluZGluZyk7XG4gICAgICAgIH1cbiAgICAgICAgYnJlYWs7XG5cbiAgICAgIGNhc2UgXCJBcnJheUV4cHJlc3Npb25cIjpcbiAgICAgICAgbm9kZS50eXBlID0gXCJBcnJheVBhdHRlcm5cIjtcbiAgICAgICAgdGhpcy50b0Fzc2lnbmFibGVMaXN0KG5vZGUuZWxlbWVudHMsIGlzQmluZGluZyk7XG4gICAgICAgIGJyZWFrO1xuXG4gICAgICBjYXNlIFwiQXNzaWdubWVudEV4cHJlc3Npb25cIjpcbiAgICAgICAgaWYgKG5vZGUub3BlcmF0b3IgPT09IFwiPVwiKSB7XG4gICAgICAgICAgbm9kZS50eXBlID0gXCJBc3NpZ25tZW50UGF0dGVyblwiO1xuICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgIHRoaXMucmFpc2Uobm9kZS5sZWZ0LmVuZCwgXCJPbmx5ICc9JyBvcGVyYXRvciBjYW4gYmUgdXNlZCBmb3Igc3BlY2lmeWluZyBkZWZhdWx0IHZhbHVlLlwiKTtcbiAgICAgICAgfVxuICAgICAgICBicmVhaztcblxuICAgICAgY2FzZSBcIlBhcmVudGhlc2l6ZWRFeHByZXNzaW9uXCI6XG4gICAgICAgIG5vZGUuZXhwcmVzc2lvbiA9IHRoaXMudG9Bc3NpZ25hYmxlKG5vZGUuZXhwcmVzc2lvbiwgaXNCaW5kaW5nKTtcbiAgICAgICAgYnJlYWs7XG5cbiAgICAgIGNhc2UgXCJNZW1iZXJFeHByZXNzaW9uXCI6XG4gICAgICAgIGlmICghaXNCaW5kaW5nKSBicmVhaztcblxuICAgICAgZGVmYXVsdDpcbiAgICAgICAgdGhpcy5yYWlzZShub2RlLnN0YXJ0LCBcIkFzc2lnbmluZyB0byBydmFsdWVcIik7XG4gICAgfVxuICB9XG4gIHJldHVybiBub2RlO1xufTtcblxuLy8gQ29udmVydCBsaXN0IG9mIGV4cHJlc3Npb24gYXRvbXMgdG8gYmluZGluZyBsaXN0LlxuXG5wcC50b0Fzc2lnbmFibGVMaXN0ID0gZnVuY3Rpb24gKGV4cHJMaXN0LCBpc0JpbmRpbmcpIHtcbiAgdmFyIGVuZCA9IGV4cHJMaXN0Lmxlbmd0aDtcbiAgaWYgKGVuZCkge1xuICAgIHZhciBsYXN0ID0gZXhwckxpc3RbZW5kIC0gMV07XG4gICAgaWYgKGxhc3QgJiYgbGFzdC50eXBlID09IFwiUmVzdEVsZW1lbnRcIikge1xuICAgICAgLS1lbmQ7XG4gICAgfSBlbHNlIGlmIChsYXN0ICYmIGxhc3QudHlwZSA9PSBcIlNwcmVhZEVsZW1lbnRcIikge1xuICAgICAgbGFzdC50eXBlID0gXCJSZXN0RWxlbWVudFwiO1xuICAgICAgdmFyIGFyZyA9IGxhc3QuYXJndW1lbnQ7XG4gICAgICB0aGlzLnRvQXNzaWduYWJsZShhcmcsIGlzQmluZGluZyk7XG4gICAgICBpZiAoYXJnLnR5cGUgIT09IFwiSWRlbnRpZmllclwiICYmIGFyZy50eXBlICE9PSBcIk1lbWJlckV4cHJlc3Npb25cIiAmJiBhcmcudHlwZSAhPT0gXCJBcnJheVBhdHRlcm5cIikgdGhpcy51bmV4cGVjdGVkKGFyZy5zdGFydCk7XG4gICAgICAtLWVuZDtcbiAgICB9XG4gIH1cbiAgZm9yICh2YXIgaSA9IDA7IGkgPCBlbmQ7IGkrKykge1xuICAgIHZhciBlbHQgPSBleHByTGlzdFtpXTtcbiAgICBpZiAoZWx0KSB0aGlzLnRvQXNzaWduYWJsZShlbHQsIGlzQmluZGluZyk7XG4gIH1cbiAgcmV0dXJuIGV4cHJMaXN0O1xufTtcblxuLy8gUGFyc2VzIHNwcmVhZCBlbGVtZW50LlxuXG5wcC5wYXJzZVNwcmVhZCA9IGZ1bmN0aW9uIChyZWZTaG9ydGhhbmREZWZhdWx0UG9zKSB7XG4gIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgdGhpcy5uZXh0KCk7XG4gIG5vZGUuYXJndW1lbnQgPSB0aGlzLnBhcnNlTWF5YmVBc3NpZ24ocmVmU2hvcnRoYW5kRGVmYXVsdFBvcyk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJTcHJlYWRFbGVtZW50XCIpO1xufTtcblxucHAucGFyc2VSZXN0ID0gZnVuY3Rpb24gKCkge1xuICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gIHRoaXMubmV4dCgpO1xuICBub2RlLmFyZ3VtZW50ID0gdGhpcy50eXBlID09PSB0dC5uYW1lIHx8IHRoaXMudHlwZSA9PT0gdHQuYnJhY2tldEwgPyB0aGlzLnBhcnNlQmluZGluZ0F0b20oKSA6IHRoaXMudW5leHBlY3RlZCgpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiUmVzdEVsZW1lbnRcIik7XG59O1xuXG4vLyBQYXJzZXMgbHZhbHVlIChhc3NpZ25hYmxlKSBhdG9tLlxuXG5wcC5wYXJzZUJpbmRpbmdBdG9tID0gZnVuY3Rpb24gKCkge1xuICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uIDwgNikgcmV0dXJuIHRoaXMucGFyc2VJZGVudCgpO1xuICBzd2l0Y2ggKHRoaXMudHlwZSkge1xuICAgIGNhc2UgdHQubmFtZTpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlSWRlbnQoKTtcblxuICAgIGNhc2UgdHQuYnJhY2tldEw6XG4gICAgICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gICAgICB0aGlzLm5leHQoKTtcbiAgICAgIG5vZGUuZWxlbWVudHMgPSB0aGlzLnBhcnNlQmluZGluZ0xpc3QodHQuYnJhY2tldFIsIHRydWUsIHRydWUpO1xuICAgICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkFycmF5UGF0dGVyblwiKTtcblxuICAgIGNhc2UgdHQuYnJhY2VMOlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VPYmoodHJ1ZSk7XG5cbiAgICBkZWZhdWx0OlxuICAgICAgdGhpcy51bmV4cGVjdGVkKCk7XG4gIH1cbn07XG5cbnBwLnBhcnNlQmluZGluZ0xpc3QgPSBmdW5jdGlvbiAoY2xvc2UsIGFsbG93RW1wdHksIGFsbG93VHJhaWxpbmdDb21tYSkge1xuICB2YXIgZWx0cyA9IFtdLFxuICAgICAgZmlyc3QgPSB0cnVlO1xuICB3aGlsZSAoIXRoaXMuZWF0KGNsb3NlKSkge1xuICAgIGlmIChmaXJzdCkgZmlyc3QgPSBmYWxzZTtlbHNlIHRoaXMuZXhwZWN0KHR0LmNvbW1hKTtcbiAgICBpZiAoYWxsb3dFbXB0eSAmJiB0aGlzLnR5cGUgPT09IHR0LmNvbW1hKSB7XG4gICAgICBlbHRzLnB1c2gobnVsbCk7XG4gICAgfSBlbHNlIGlmIChhbGxvd1RyYWlsaW5nQ29tbWEgJiYgdGhpcy5hZnRlclRyYWlsaW5nQ29tbWEoY2xvc2UpKSB7XG4gICAgICBicmVhaztcbiAgICB9IGVsc2UgaWYgKHRoaXMudHlwZSA9PT0gdHQuZWxsaXBzaXMpIHtcbiAgICAgIHZhciByZXN0ID0gdGhpcy5wYXJzZVJlc3QoKTtcbiAgICAgIHRoaXMucGFyc2VCaW5kaW5nTGlzdEl0ZW0ocmVzdCk7XG4gICAgICBlbHRzLnB1c2gocmVzdCk7XG4gICAgICB0aGlzLmV4cGVjdChjbG9zZSk7XG4gICAgICBicmVhaztcbiAgICB9IGVsc2Uge1xuICAgICAgdmFyIGVsZW0gPSB0aGlzLnBhcnNlTWF5YmVEZWZhdWx0KHRoaXMuc3RhcnQsIHRoaXMuc3RhcnRMb2MpO1xuICAgICAgdGhpcy5wYXJzZUJpbmRpbmdMaXN0SXRlbShlbGVtKTtcbiAgICAgIGVsdHMucHVzaChlbGVtKTtcbiAgICB9XG4gIH1cbiAgcmV0dXJuIGVsdHM7XG59O1xuXG5wcC5wYXJzZUJpbmRpbmdMaXN0SXRlbSA9IGZ1bmN0aW9uIChwYXJhbSkge1xuICByZXR1cm4gcGFyYW07XG59O1xuXG4vLyBQYXJzZXMgYXNzaWdubWVudCBwYXR0ZXJuIGFyb3VuZCBnaXZlbiBhdG9tIGlmIHBvc3NpYmxlLlxuXG5wcC5wYXJzZU1heWJlRGVmYXVsdCA9IGZ1bmN0aW9uIChzdGFydFBvcywgc3RhcnRMb2MsIGxlZnQpIHtcbiAgaWYgKEFycmF5LmlzQXJyYXkoc3RhcnRQb3MpKSB7XG4gICAgaWYgKHRoaXMub3B0aW9ucy5sb2NhdGlvbnMgJiYgbm9DYWxscyA9PT0gdW5kZWZpbmVkKSB7XG4gICAgICAvLyBzaGlmdCBhcmd1bWVudHMgdG8gbGVmdCBieSBvbmVcbiAgICAgIGxlZnQgPSBzdGFydExvYztcbiAgICAgIC8vIGZsYXR0ZW4gc3RhcnRQb3NcbiAgICAgIHN0YXJ0TG9jID0gc3RhcnRQb3NbMV07XG4gICAgICBzdGFydFBvcyA9IHN0YXJ0UG9zWzBdO1xuICAgIH1cbiAgfVxuICBsZWZ0ID0gbGVmdCB8fCB0aGlzLnBhcnNlQmluZGluZ0F0b20oKTtcbiAgaWYgKCF0aGlzLmVhdCh0dC5lcSkpIHJldHVybiBsZWZ0O1xuICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlQXQoc3RhcnRQb3MsIHN0YXJ0TG9jKTtcbiAgbm9kZS5vcGVyYXRvciA9IFwiPVwiO1xuICBub2RlLmxlZnQgPSBsZWZ0O1xuICBub2RlLnJpZ2h0ID0gdGhpcy5wYXJzZU1heWJlQXNzaWduKCk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJBc3NpZ25tZW50UGF0dGVyblwiKTtcbn07XG5cbi8vIFZlcmlmeSB0aGF0IGEgbm9kZSBpcyBhbiBsdmFsIOKAlCBzb21ldGhpbmcgdGhhdCBjYW4gYmUgYXNzaWduZWRcbi8vIHRvLlxuXG5wcC5jaGVja0xWYWwgPSBmdW5jdGlvbiAoZXhwciwgaXNCaW5kaW5nLCBjaGVja0NsYXNoZXMpIHtcbiAgc3dpdGNoIChleHByLnR5cGUpIHtcbiAgICBjYXNlIFwiSWRlbnRpZmllclwiOlxuICAgICAgaWYgKHRoaXMuc3RyaWN0ICYmIChyZXNlcnZlZFdvcmRzLnN0cmljdEJpbmQoZXhwci5uYW1lKSB8fCByZXNlcnZlZFdvcmRzLnN0cmljdChleHByLm5hbWUpKSkgdGhpcy5yYWlzZShleHByLnN0YXJ0LCAoaXNCaW5kaW5nID8gXCJCaW5kaW5nIFwiIDogXCJBc3NpZ25pbmcgdG8gXCIpICsgZXhwci5uYW1lICsgXCIgaW4gc3RyaWN0IG1vZGVcIik7XG4gICAgICBpZiAoY2hlY2tDbGFzaGVzKSB7XG4gICAgICAgIGlmIChoYXMoY2hlY2tDbGFzaGVzLCBleHByLm5hbWUpKSB0aGlzLnJhaXNlKGV4cHIuc3RhcnQsIFwiQXJndW1lbnQgbmFtZSBjbGFzaCBpbiBzdHJpY3QgbW9kZVwiKTtcbiAgICAgICAgY2hlY2tDbGFzaGVzW2V4cHIubmFtZV0gPSB0cnVlO1xuICAgICAgfVxuICAgICAgYnJlYWs7XG5cbiAgICBjYXNlIFwiTWVtYmVyRXhwcmVzc2lvblwiOlxuICAgICAgaWYgKGlzQmluZGluZykgdGhpcy5yYWlzZShleHByLnN0YXJ0LCAoaXNCaW5kaW5nID8gXCJCaW5kaW5nXCIgOiBcIkFzc2lnbmluZyB0b1wiKSArIFwiIG1lbWJlciBleHByZXNzaW9uXCIpO1xuICAgICAgYnJlYWs7XG5cbiAgICBjYXNlIFwiT2JqZWN0UGF0dGVyblwiOlxuICAgICAgZm9yICh2YXIgaSA9IDA7IGkgPCBleHByLnByb3BlcnRpZXMubGVuZ3RoOyBpKyspIHtcbiAgICAgICAgdGhpcy5jaGVja0xWYWwoZXhwci5wcm9wZXJ0aWVzW2ldLnZhbHVlLCBpc0JpbmRpbmcsIGNoZWNrQ2xhc2hlcyk7XG4gICAgICB9YnJlYWs7XG5cbiAgICBjYXNlIFwiQXJyYXlQYXR0ZXJuXCI6XG4gICAgICBmb3IgKHZhciBpID0gMDsgaSA8IGV4cHIuZWxlbWVudHMubGVuZ3RoOyBpKyspIHtcbiAgICAgICAgdmFyIGVsZW0gPSBleHByLmVsZW1lbnRzW2ldO1xuICAgICAgICBpZiAoZWxlbSkgdGhpcy5jaGVja0xWYWwoZWxlbSwgaXNCaW5kaW5nLCBjaGVja0NsYXNoZXMpO1xuICAgICAgfVxuICAgICAgYnJlYWs7XG5cbiAgICBjYXNlIFwiQXNzaWdubWVudFBhdHRlcm5cIjpcbiAgICAgIHRoaXMuY2hlY2tMVmFsKGV4cHIubGVmdCwgaXNCaW5kaW5nLCBjaGVja0NsYXNoZXMpO1xuICAgICAgYnJlYWs7XG5cbiAgICBjYXNlIFwiUmVzdEVsZW1lbnRcIjpcbiAgICAgIHRoaXMuY2hlY2tMVmFsKGV4cHIuYXJndW1lbnQsIGlzQmluZGluZywgY2hlY2tDbGFzaGVzKTtcbiAgICAgIGJyZWFrO1xuXG4gICAgY2FzZSBcIlBhcmVudGhlc2l6ZWRFeHByZXNzaW9uXCI6XG4gICAgICB0aGlzLmNoZWNrTFZhbChleHByLmV4cHJlc3Npb24sIGlzQmluZGluZywgY2hlY2tDbGFzaGVzKTtcbiAgICAgIGJyZWFrO1xuXG4gICAgZGVmYXVsdDpcbiAgICAgIHRoaXMucmFpc2UoZXhwci5zdGFydCwgKGlzQmluZGluZyA/IFwiQmluZGluZ1wiIDogXCJBc3NpZ25pbmcgdG9cIikgKyBcIiBydmFsdWVcIik7XG4gIH1cbn07XG5cbn0se1wiLi9pZGVudGlmaWVyXCI6NyxcIi4vc3RhdGVcIjoxMyxcIi4vdG9rZW50eXBlXCI6MTcsXCIuL3V0aWxcIjoxOH1dLDEwOltmdW5jdGlvbihfZGVyZXFfLG1vZHVsZSxleHBvcnRzKXtcblwidXNlIHN0cmljdFwiO1xuXG52YXIgX2NsYXNzQ2FsbENoZWNrID0gZnVuY3Rpb24gKGluc3RhbmNlLCBDb25zdHJ1Y3RvcikgeyBpZiAoIShpbnN0YW5jZSBpbnN0YW5jZW9mIENvbnN0cnVjdG9yKSkgeyB0aHJvdyBuZXcgVHlwZUVycm9yKFwiQ2Fubm90IGNhbGwgYSBjbGFzcyBhcyBhIGZ1bmN0aW9uXCIpOyB9IH07XG5cbmV4cG9ydHMuX19lc01vZHVsZSA9IHRydWU7XG5cbnZhciBQYXJzZXIgPSBfZGVyZXFfKFwiLi9zdGF0ZVwiKS5QYXJzZXI7XG5cbnZhciBTb3VyY2VMb2NhdGlvbiA9IF9kZXJlcV8oXCIuL2xvY2F0aW9uXCIpLlNvdXJjZUxvY2F0aW9uO1xuXG4vLyBTdGFydCBhbiBBU1Qgbm9kZSwgYXR0YWNoaW5nIGEgc3RhcnQgb2Zmc2V0LlxuXG52YXIgcHAgPSBQYXJzZXIucHJvdG90eXBlO1xuXG52YXIgTm9kZSA9IGV4cG9ydHMuTm9kZSA9IGZ1bmN0aW9uIE5vZGUoKSB7XG4gIF9jbGFzc0NhbGxDaGVjayh0aGlzLCBOb2RlKTtcbn07XG5cbnBwLnN0YXJ0Tm9kZSA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIG5vZGUgPSBuZXcgTm9kZSgpO1xuICBub2RlLnN0YXJ0ID0gdGhpcy5zdGFydDtcbiAgaWYgKHRoaXMub3B0aW9ucy5sb2NhdGlvbnMpIG5vZGUubG9jID0gbmV3IFNvdXJjZUxvY2F0aW9uKHRoaXMsIHRoaXMuc3RhcnRMb2MpO1xuICBpZiAodGhpcy5vcHRpb25zLmRpcmVjdFNvdXJjZUZpbGUpIG5vZGUuc291cmNlRmlsZSA9IHRoaXMub3B0aW9ucy5kaXJlY3RTb3VyY2VGaWxlO1xuICBpZiAodGhpcy5vcHRpb25zLnJhbmdlcykgbm9kZS5yYW5nZSA9IFt0aGlzLnN0YXJ0LCAwXTtcbiAgcmV0dXJuIG5vZGU7XG59O1xuXG5wcC5zdGFydE5vZGVBdCA9IGZ1bmN0aW9uIChwb3MsIGxvYykge1xuICB2YXIgbm9kZSA9IG5ldyBOb2RlKCk7XG4gIGlmIChBcnJheS5pc0FycmF5KHBvcykpIHtcbiAgICBpZiAodGhpcy5vcHRpb25zLmxvY2F0aW9ucyAmJiBsb2MgPT09IHVuZGVmaW5lZCkge1xuICAgICAgLy8gZmxhdHRlbiBwb3NcbiAgICAgIGxvYyA9IHBvc1sxXTtcbiAgICAgIHBvcyA9IHBvc1swXTtcbiAgICB9XG4gIH1cbiAgbm9kZS5zdGFydCA9IHBvcztcbiAgaWYgKHRoaXMub3B0aW9ucy5sb2NhdGlvbnMpIG5vZGUubG9jID0gbmV3IFNvdXJjZUxvY2F0aW9uKHRoaXMsIGxvYyk7XG4gIGlmICh0aGlzLm9wdGlvbnMuZGlyZWN0U291cmNlRmlsZSkgbm9kZS5zb3VyY2VGaWxlID0gdGhpcy5vcHRpb25zLmRpcmVjdFNvdXJjZUZpbGU7XG4gIGlmICh0aGlzLm9wdGlvbnMucmFuZ2VzKSBub2RlLnJhbmdlID0gW3BvcywgMF07XG4gIHJldHVybiBub2RlO1xufTtcblxuLy8gRmluaXNoIGFuIEFTVCBub2RlLCBhZGRpbmcgYHR5cGVgIGFuZCBgZW5kYCBwcm9wZXJ0aWVzLlxuXG5wcC5maW5pc2hOb2RlID0gZnVuY3Rpb24gKG5vZGUsIHR5cGUpIHtcbiAgbm9kZS50eXBlID0gdHlwZTtcbiAgbm9kZS5lbmQgPSB0aGlzLmxhc3RUb2tFbmQ7XG4gIGlmICh0aGlzLm9wdGlvbnMubG9jYXRpb25zKSBub2RlLmxvYy5lbmQgPSB0aGlzLmxhc3RUb2tFbmRMb2M7XG4gIGlmICh0aGlzLm9wdGlvbnMucmFuZ2VzKSBub2RlLnJhbmdlWzFdID0gdGhpcy5sYXN0VG9rRW5kO1xuICByZXR1cm4gbm9kZTtcbn07XG5cbi8vIEZpbmlzaCBub2RlIGF0IGdpdmVuIHBvc2l0aW9uXG5cbnBwLmZpbmlzaE5vZGVBdCA9IGZ1bmN0aW9uIChub2RlLCB0eXBlLCBwb3MsIGxvYykge1xuICBub2RlLnR5cGUgPSB0eXBlO1xuICBpZiAoQXJyYXkuaXNBcnJheShwb3MpKSB7XG4gICAgaWYgKHRoaXMub3B0aW9ucy5sb2NhdGlvbnMgJiYgbG9jID09PSB1bmRlZmluZWQpIHtcbiAgICAgIC8vIGZsYXR0ZW4gcG9zXG4gICAgICBsb2MgPSBwb3NbMV07XG4gICAgICBwb3MgPSBwb3NbMF07XG4gICAgfVxuICB9XG4gIG5vZGUuZW5kID0gcG9zO1xuICBpZiAodGhpcy5vcHRpb25zLmxvY2F0aW9ucykgbm9kZS5sb2MuZW5kID0gbG9jO1xuICBpZiAodGhpcy5vcHRpb25zLnJhbmdlcykgbm9kZS5yYW5nZVsxXSA9IHBvcztcbiAgcmV0dXJuIG5vZGU7XG59O1xuXG59LHtcIi4vbG9jYXRpb25cIjo4LFwiLi9zdGF0ZVwiOjEzfV0sMTE6W2Z1bmN0aW9uKF9kZXJlcV8sbW9kdWxlLGV4cG9ydHMpe1xuXG5cbi8vIEludGVycHJldCBhbmQgZGVmYXVsdCBhbiBvcHRpb25zIG9iamVjdFxuXG5cInVzZSBzdHJpY3RcIjtcblxuZXhwb3J0cy5nZXRPcHRpb25zID0gZ2V0T3B0aW9ucztcbmV4cG9ydHMuX19lc01vZHVsZSA9IHRydWU7XG5cbnZhciBfdXRpbCA9IF9kZXJlcV8oXCIuL3V0aWxcIik7XG5cbnZhciBoYXMgPSBfdXRpbC5oYXM7XG52YXIgaXNBcnJheSA9IF91dGlsLmlzQXJyYXk7XG5cbnZhciBTb3VyY2VMb2NhdGlvbiA9IF9kZXJlcV8oXCIuL2xvY2F0aW9uXCIpLlNvdXJjZUxvY2F0aW9uO1xuXG4vLyBBIHNlY29uZCBvcHRpb25hbCBhcmd1bWVudCBjYW4gYmUgZ2l2ZW4gdG8gZnVydGhlciBjb25maWd1cmVcbi8vIHRoZSBwYXJzZXIgcHJvY2Vzcy4gVGhlc2Ugb3B0aW9ucyBhcmUgcmVjb2duaXplZDpcblxudmFyIGRlZmF1bHRPcHRpb25zID0ge1xuICAvLyBgZWNtYVZlcnNpb25gIGluZGljYXRlcyB0aGUgRUNNQVNjcmlwdCB2ZXJzaW9uIHRvIHBhcnNlLiBNdXN0XG4gIC8vIGJlIGVpdGhlciAzLCBvciA1LCBvciA2LiBUaGlzIGluZmx1ZW5jZXMgc3VwcG9ydCBmb3Igc3RyaWN0XG4gIC8vIG1vZGUsIHRoZSBzZXQgb2YgcmVzZXJ2ZWQgd29yZHMsIHN1cHBvcnQgZm9yIGdldHRlcnMgYW5kXG4gIC8vIHNldHRlcnMgYW5kIG90aGVyIGZlYXR1cmVzLlxuICBlY21hVmVyc2lvbjogNSxcbiAgLy8gU291cmNlIHR5cGUgKFwic2NyaXB0XCIgb3IgXCJtb2R1bGVcIikgZm9yIGRpZmZlcmVudCBzZW1hbnRpY3NcbiAgc291cmNlVHlwZTogXCJzY3JpcHRcIixcbiAgLy8gYG9uSW5zZXJ0ZWRTZW1pY29sb25gIGNhbiBiZSBhIGNhbGxiYWNrIHRoYXQgd2lsbCBiZSBjYWxsZWRcbiAgLy8gd2hlbiBhIHNlbWljb2xvbiBpcyBhdXRvbWF0aWNhbGx5IGluc2VydGVkLiBJdCB3aWxsIGJlIHBhc3NlZFxuICAvLyB0aCBwb3NpdGlvbiBvZiB0aGUgY29tbWEgYXMgYW4gb2Zmc2V0LCBhbmQgaWYgYGxvY2F0aW9uc2AgaXNcbiAgLy8gZW5hYmxlZCwgaXQgaXMgZ2l2ZW4gdGhlIGxvY2F0aW9uIGFzIGEgYHtsaW5lLCBjb2x1bW59YCBvYmplY3RcbiAgLy8gYXMgc2Vjb25kIGFyZ3VtZW50LlxuICBvbkluc2VydGVkU2VtaWNvbG9uOiBudWxsLFxuICAvLyBgb25UcmFpbGluZ0NvbW1hYCBpcyBzaW1pbGFyIHRvIGBvbkluc2VydGVkU2VtaWNvbG9uYCwgYnV0IGZvclxuICAvLyB0cmFpbGluZyBjb21tYXMuXG4gIG9uVHJhaWxpbmdDb21tYTogbnVsbCxcbiAgLy8gQnkgZGVmYXVsdCwgcmVzZXJ2ZWQgd29yZHMgYXJlIG5vdCBlbmZvcmNlZC4gRGlzYWJsZVxuICAvLyBgYWxsb3dSZXNlcnZlZGAgdG8gZW5mb3JjZSB0aGVtLiBXaGVuIHRoaXMgb3B0aW9uIGhhcyB0aGVcbiAgLy8gdmFsdWUgXCJuZXZlclwiLCByZXNlcnZlZCB3b3JkcyBhbmQga2V5d29yZHMgY2FuIGFsc28gbm90IGJlXG4gIC8vIHVzZWQgYXMgcHJvcGVydHkgbmFtZXMuXG4gIGFsbG93UmVzZXJ2ZWQ6IHRydWUsXG4gIC8vIFdoZW4gZW5hYmxlZCwgYSByZXR1cm4gYXQgdGhlIHRvcCBsZXZlbCBpcyBub3QgY29uc2lkZXJlZCBhblxuICAvLyBlcnJvci5cbiAgYWxsb3dSZXR1cm5PdXRzaWRlRnVuY3Rpb246IGZhbHNlLFxuICAvLyBXaGVuIGVuYWJsZWQsIGltcG9ydC9leHBvcnQgc3RhdGVtZW50cyBhcmUgbm90IGNvbnN0cmFpbmVkIHRvXG4gIC8vIGFwcGVhcmluZyBhdCB0aGUgdG9wIG9mIHRoZSBwcm9ncmFtLlxuICBhbGxvd0ltcG9ydEV4cG9ydEV2ZXJ5d2hlcmU6IGZhbHNlLFxuICAvLyBXaGVuIGVuYWJsZWQsIGhhc2hiYW5nIGRpcmVjdGl2ZSBpbiB0aGUgYmVnaW5uaW5nIG9mIGZpbGVcbiAgLy8gaXMgYWxsb3dlZCBhbmQgdHJlYXRlZCBhcyBhIGxpbmUgY29tbWVudC5cbiAgYWxsb3dIYXNoQmFuZzogZmFsc2UsXG4gIC8vIFdoZW4gYGxvY2F0aW9uc2AgaXMgb24sIGBsb2NgIHByb3BlcnRpZXMgaG9sZGluZyBvYmplY3RzIHdpdGhcbiAgLy8gYHN0YXJ0YCBhbmQgYGVuZGAgcHJvcGVydGllcyBpbiBge2xpbmUsIGNvbHVtbn1gIGZvcm0gKHdpdGhcbiAgLy8gbGluZSBiZWluZyAxLWJhc2VkIGFuZCBjb2x1bW4gMC1iYXNlZCkgd2lsbCBiZSBhdHRhY2hlZCB0byB0aGVcbiAgLy8gbm9kZXMuXG4gIGxvY2F0aW9uczogZmFsc2UsXG4gIC8vIEEgZnVuY3Rpb24gY2FuIGJlIHBhc3NlZCBhcyBgb25Ub2tlbmAgb3B0aW9uLCB3aGljaCB3aWxsXG4gIC8vIGNhdXNlIEFjb3JuIHRvIGNhbGwgdGhhdCBmdW5jdGlvbiB3aXRoIG9iamVjdCBpbiB0aGUgc2FtZVxuICAvLyBmb3JtYXQgYXMgdG9rZW5pemUoKSByZXR1cm5zLiBOb3RlIHRoYXQgeW91IGFyZSBub3RcbiAgLy8gYWxsb3dlZCB0byBjYWxsIHRoZSBwYXJzZXIgZnJvbSB0aGUgY2FsbGJhY2vigJR0aGF0IHdpbGxcbiAgLy8gY29ycnVwdCBpdHMgaW50ZXJuYWwgc3RhdGUuXG4gIG9uVG9rZW46IG51bGwsXG4gIC8vIEEgZnVuY3Rpb24gY2FuIGJlIHBhc3NlZCBhcyBgb25Db21tZW50YCBvcHRpb24sIHdoaWNoIHdpbGxcbiAgLy8gY2F1c2UgQWNvcm4gdG8gY2FsbCB0aGF0IGZ1bmN0aW9uIHdpdGggYChibG9jaywgdGV4dCwgc3RhcnQsXG4gIC8vIGVuZClgIHBhcmFtZXRlcnMgd2hlbmV2ZXIgYSBjb21tZW50IGlzIHNraXBwZWQuIGBibG9ja2AgaXMgYVxuICAvLyBib29sZWFuIGluZGljYXRpbmcgd2hldGhlciB0aGlzIGlzIGEgYmxvY2sgKGAvKiAqL2ApIGNvbW1lbnQsXG4gIC8vIGB0ZXh0YCBpcyB0aGUgY29udGVudCBvZiB0aGUgY29tbWVudCwgYW5kIGBzdGFydGAgYW5kIGBlbmRgIGFyZVxuICAvLyBjaGFyYWN0ZXIgb2Zmc2V0cyB0aGF0IGRlbm90ZSB0aGUgc3RhcnQgYW5kIGVuZCBvZiB0aGUgY29tbWVudC5cbiAgLy8gV2hlbiB0aGUgYGxvY2F0aW9uc2Agb3B0aW9uIGlzIG9uLCB0d28gbW9yZSBwYXJhbWV0ZXJzIGFyZVxuICAvLyBwYXNzZWQsIHRoZSBmdWxsIGB7bGluZSwgY29sdW1ufWAgbG9jYXRpb25zIG9mIHRoZSBzdGFydCBhbmRcbiAgLy8gZW5kIG9mIHRoZSBjb21tZW50cy4gTm90ZSB0aGF0IHlvdSBhcmUgbm90IGFsbG93ZWQgdG8gY2FsbCB0aGVcbiAgLy8gcGFyc2VyIGZyb20gdGhlIGNhbGxiYWNr4oCUdGhhdCB3aWxsIGNvcnJ1cHQgaXRzIGludGVybmFsIHN0YXRlLlxuICBvbkNvbW1lbnQ6IG51bGwsXG4gIC8vIE5vZGVzIGhhdmUgdGhlaXIgc3RhcnQgYW5kIGVuZCBjaGFyYWN0ZXJzIG9mZnNldHMgcmVjb3JkZWQgaW5cbiAgLy8gYHN0YXJ0YCBhbmQgYGVuZGAgcHJvcGVydGllcyAoZGlyZWN0bHkgb24gdGhlIG5vZGUsIHJhdGhlciB0aGFuXG4gIC8vIHRoZSBgbG9jYCBvYmplY3QsIHdoaWNoIGhvbGRzIGxpbmUvY29sdW1uIGRhdGEuIFRvIGFsc28gYWRkIGFcbiAgLy8gW3NlbWktc3RhbmRhcmRpemVkXVtyYW5nZV0gYHJhbmdlYCBwcm9wZXJ0eSBob2xkaW5nIGEgYFtzdGFydCxcbiAgLy8gZW5kXWAgYXJyYXkgd2l0aCB0aGUgc2FtZSBudW1iZXJzLCBzZXQgdGhlIGByYW5nZXNgIG9wdGlvbiB0b1xuICAvLyBgdHJ1ZWAuXG4gIC8vXG4gIC8vIFtyYW5nZV06IGh0dHBzOi8vYnVnemlsbGEubW96aWxsYS5vcmcvc2hvd19idWcuY2dpP2lkPTc0NTY3OFxuICByYW5nZXM6IGZhbHNlLFxuICAvLyBJdCBpcyBwb3NzaWJsZSB0byBwYXJzZSBtdWx0aXBsZSBmaWxlcyBpbnRvIGEgc2luZ2xlIEFTVCBieVxuICAvLyBwYXNzaW5nIHRoZSB0cmVlIHByb2R1Y2VkIGJ5IHBhcnNpbmcgdGhlIGZpcnN0IGZpbGUgYXNcbiAgLy8gYHByb2dyYW1gIG9wdGlvbiBpbiBzdWJzZXF1ZW50IHBhcnNlcy4gVGhpcyB3aWxsIGFkZCB0aGVcbiAgLy8gdG9wbGV2ZWwgZm9ybXMgb2YgdGhlIHBhcnNlZCBmaWxlIHRvIHRoZSBgUHJvZ3JhbWAgKHRvcCkgbm9kZVxuICAvLyBvZiBhbiBleGlzdGluZyBwYXJzZSB0cmVlLlxuICBwcm9ncmFtOiBudWxsLFxuICAvLyBXaGVuIGBsb2NhdGlvbnNgIGlzIG9uLCB5b3UgY2FuIHBhc3MgdGhpcyB0byByZWNvcmQgdGhlIHNvdXJjZVxuICAvLyBmaWxlIGluIGV2ZXJ5IG5vZGUncyBgbG9jYCBvYmplY3QuXG4gIHNvdXJjZUZpbGU6IG51bGwsXG4gIC8vIFRoaXMgdmFsdWUsIGlmIGdpdmVuLCBpcyBzdG9yZWQgaW4gZXZlcnkgbm9kZSwgd2hldGhlclxuICAvLyBgbG9jYXRpb25zYCBpcyBvbiBvciBvZmYuXG4gIGRpcmVjdFNvdXJjZUZpbGU6IG51bGwsXG4gIC8vIFdoZW4gZW5hYmxlZCwgcGFyZW50aGVzaXplZCBleHByZXNzaW9ucyBhcmUgcmVwcmVzZW50ZWQgYnlcbiAgLy8gKG5vbi1zdGFuZGFyZCkgUGFyZW50aGVzaXplZEV4cHJlc3Npb24gbm9kZXNcbiAgcHJlc2VydmVQYXJlbnM6IGZhbHNlLFxuICBwbHVnaW5zOiB7fVxufTtleHBvcnRzLmRlZmF1bHRPcHRpb25zID0gZGVmYXVsdE9wdGlvbnM7XG5cbmZ1bmN0aW9uIGdldE9wdGlvbnMob3B0cykge1xuICB2YXIgb3B0aW9ucyA9IHt9O1xuICBmb3IgKHZhciBvcHQgaW4gZGVmYXVsdE9wdGlvbnMpIHtcbiAgICBvcHRpb25zW29wdF0gPSBvcHRzICYmIGhhcyhvcHRzLCBvcHQpID8gb3B0c1tvcHRdIDogZGVmYXVsdE9wdGlvbnNbb3B0XTtcbiAgfWlmIChpc0FycmF5KG9wdGlvbnMub25Ub2tlbikpIHtcbiAgICAoZnVuY3Rpb24gKCkge1xuICAgICAgdmFyIHRva2VucyA9IG9wdGlvbnMub25Ub2tlbjtcbiAgICAgIG9wdGlvbnMub25Ub2tlbiA9IGZ1bmN0aW9uICh0b2tlbikge1xuICAgICAgICByZXR1cm4gdG9rZW5zLnB1c2godG9rZW4pO1xuICAgICAgfTtcbiAgICB9KSgpO1xuICB9XG4gIGlmIChpc0FycmF5KG9wdGlvbnMub25Db21tZW50KSkgb3B0aW9ucy5vbkNvbW1lbnQgPSBwdXNoQ29tbWVudChvcHRpb25zLCBvcHRpb25zLm9uQ29tbWVudCk7XG5cbiAgcmV0dXJuIG9wdGlvbnM7XG59XG5cbmZ1bmN0aW9uIHB1c2hDb21tZW50KG9wdGlvbnMsIGFycmF5KSB7XG4gIHJldHVybiBmdW5jdGlvbiAoYmxvY2ssIHRleHQsIHN0YXJ0LCBlbmQsIHN0YXJ0TG9jLCBlbmRMb2MpIHtcbiAgICB2YXIgY29tbWVudCA9IHtcbiAgICAgIHR5cGU6IGJsb2NrID8gXCJCbG9ja1wiIDogXCJMaW5lXCIsXG4gICAgICB2YWx1ZTogdGV4dCxcbiAgICAgIHN0YXJ0OiBzdGFydCxcbiAgICAgIGVuZDogZW5kXG4gICAgfTtcbiAgICBpZiAob3B0aW9ucy5sb2NhdGlvbnMpIGNvbW1lbnQubG9jID0gbmV3IFNvdXJjZUxvY2F0aW9uKHRoaXMsIHN0YXJ0TG9jLCBlbmRMb2MpO1xuICAgIGlmIChvcHRpb25zLnJhbmdlcykgY29tbWVudC5yYW5nZSA9IFtzdGFydCwgZW5kXTtcbiAgICBhcnJheS5wdXNoKGNvbW1lbnQpO1xuICB9O1xufVxuXG59LHtcIi4vbG9jYXRpb25cIjo4LFwiLi91dGlsXCI6MTh9XSwxMjpbZnVuY3Rpb24oX2RlcmVxXyxtb2R1bGUsZXhwb3J0cyl7XG5cInVzZSBzdHJpY3RcIjtcblxudmFyIHR0ID0gX2RlcmVxXyhcIi4vdG9rZW50eXBlXCIpLnR5cGVzO1xuXG52YXIgUGFyc2VyID0gX2RlcmVxXyhcIi4vc3RhdGVcIikuUGFyc2VyO1xuXG52YXIgbGluZUJyZWFrID0gX2RlcmVxXyhcIi4vd2hpdGVzcGFjZVwiKS5saW5lQnJlYWs7XG5cbnZhciBwcCA9IFBhcnNlci5wcm90b3R5cGU7XG5cbi8vICMjIFBhcnNlciB1dGlsaXRpZXNcblxuLy8gVGVzdCB3aGV0aGVyIGEgc3RhdGVtZW50IG5vZGUgaXMgdGhlIHN0cmluZyBsaXRlcmFsIGBcInVzZSBzdHJpY3RcImAuXG5cbnBwLmlzVXNlU3RyaWN0ID0gZnVuY3Rpb24gKHN0bXQpIHtcbiAgcmV0dXJuIHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA1ICYmIHN0bXQudHlwZSA9PT0gXCJFeHByZXNzaW9uU3RhdGVtZW50XCIgJiYgc3RtdC5leHByZXNzaW9uLnR5cGUgPT09IFwiTGl0ZXJhbFwiICYmIHN0bXQuZXhwcmVzc2lvbi52YWx1ZSA9PT0gXCJ1c2Ugc3RyaWN0XCI7XG59O1xuXG4vLyBQcmVkaWNhdGUgdGhhdCB0ZXN0cyB3aGV0aGVyIHRoZSBuZXh0IHRva2VuIGlzIG9mIHRoZSBnaXZlblxuLy8gdHlwZSwgYW5kIGlmIHllcywgY29uc3VtZXMgaXQgYXMgYSBzaWRlIGVmZmVjdC5cblxucHAuZWF0ID0gZnVuY3Rpb24gKHR5cGUpIHtcbiAgaWYgKHRoaXMudHlwZSA9PT0gdHlwZSkge1xuICAgIHRoaXMubmV4dCgpO1xuICAgIHJldHVybiB0cnVlO1xuICB9IGVsc2Uge1xuICAgIHJldHVybiBmYWxzZTtcbiAgfVxufTtcblxuLy8gVGVzdHMgd2hldGhlciBwYXJzZWQgdG9rZW4gaXMgYSBjb250ZXh0dWFsIGtleXdvcmQuXG5cbnBwLmlzQ29udGV4dHVhbCA9IGZ1bmN0aW9uIChuYW1lKSB7XG4gIHJldHVybiB0aGlzLnR5cGUgPT09IHR0Lm5hbWUgJiYgdGhpcy52YWx1ZSA9PT0gbmFtZTtcbn07XG5cbi8vIENvbnN1bWVzIGNvbnRleHR1YWwga2V5d29yZCBpZiBwb3NzaWJsZS5cblxucHAuZWF0Q29udGV4dHVhbCA9IGZ1bmN0aW9uIChuYW1lKSB7XG4gIHJldHVybiB0aGlzLnZhbHVlID09PSBuYW1lICYmIHRoaXMuZWF0KHR0Lm5hbWUpO1xufTtcblxuLy8gQXNzZXJ0cyB0aGF0IGZvbGxvd2luZyB0b2tlbiBpcyBnaXZlbiBjb250ZXh0dWFsIGtleXdvcmQuXG5cbnBwLmV4cGVjdENvbnRleHR1YWwgPSBmdW5jdGlvbiAobmFtZSkge1xuICBpZiAoIXRoaXMuZWF0Q29udGV4dHVhbChuYW1lKSkgdGhpcy51bmV4cGVjdGVkKCk7XG59O1xuXG4vLyBUZXN0IHdoZXRoZXIgYSBzZW1pY29sb24gY2FuIGJlIGluc2VydGVkIGF0IHRoZSBjdXJyZW50IHBvc2l0aW9uLlxuXG5wcC5jYW5JbnNlcnRTZW1pY29sb24gPSBmdW5jdGlvbiAoKSB7XG4gIHJldHVybiB0aGlzLnR5cGUgPT09IHR0LmVvZiB8fCB0aGlzLnR5cGUgPT09IHR0LmJyYWNlUiB8fCBsaW5lQnJlYWsudGVzdCh0aGlzLmlucHV0LnNsaWNlKHRoaXMubGFzdFRva0VuZCwgdGhpcy5zdGFydCkpO1xufTtcblxucHAuaW5zZXJ0U2VtaWNvbG9uID0gZnVuY3Rpb24gKCkge1xuICBpZiAodGhpcy5jYW5JbnNlcnRTZW1pY29sb24oKSkge1xuICAgIGlmICh0aGlzLm9wdGlvbnMub25JbnNlcnRlZFNlbWljb2xvbikgdGhpcy5vcHRpb25zLm9uSW5zZXJ0ZWRTZW1pY29sb24odGhpcy5sYXN0VG9rRW5kLCB0aGlzLmxhc3RUb2tFbmRMb2MpO1xuICAgIHJldHVybiB0cnVlO1xuICB9XG59O1xuXG4vLyBDb25zdW1lIGEgc2VtaWNvbG9uLCBvciwgZmFpbGluZyB0aGF0LCBzZWUgaWYgd2UgYXJlIGFsbG93ZWQgdG9cbi8vIHByZXRlbmQgdGhhdCB0aGVyZSBpcyBhIHNlbWljb2xvbiBhdCB0aGlzIHBvc2l0aW9uLlxuXG5wcC5zZW1pY29sb24gPSBmdW5jdGlvbiAoKSB7XG4gIGlmICghdGhpcy5lYXQodHQuc2VtaSkgJiYgIXRoaXMuaW5zZXJ0U2VtaWNvbG9uKCkpIHRoaXMudW5leHBlY3RlZCgpO1xufTtcblxucHAuYWZ0ZXJUcmFpbGluZ0NvbW1hID0gZnVuY3Rpb24gKHRva1R5cGUpIHtcbiAgaWYgKHRoaXMudHlwZSA9PSB0b2tUeXBlKSB7XG4gICAgaWYgKHRoaXMub3B0aW9ucy5vblRyYWlsaW5nQ29tbWEpIHRoaXMub3B0aW9ucy5vblRyYWlsaW5nQ29tbWEodGhpcy5sYXN0VG9rU3RhcnQsIHRoaXMubGFzdFRva1N0YXJ0TG9jKTtcbiAgICB0aGlzLm5leHQoKTtcbiAgICByZXR1cm4gdHJ1ZTtcbiAgfVxufTtcblxuLy8gRXhwZWN0IGEgdG9rZW4gb2YgYSBnaXZlbiB0eXBlLiBJZiBmb3VuZCwgY29uc3VtZSBpdCwgb3RoZXJ3aXNlLFxuLy8gcmFpc2UgYW4gdW5leHBlY3RlZCB0b2tlbiBlcnJvci5cblxucHAuZXhwZWN0ID0gZnVuY3Rpb24gKHR5cGUpIHtcbiAgdGhpcy5lYXQodHlwZSkgfHwgdGhpcy51bmV4cGVjdGVkKCk7XG59O1xuXG4vLyBSYWlzZSBhbiB1bmV4cGVjdGVkIHRva2VuIGVycm9yLlxuXG5wcC51bmV4cGVjdGVkID0gZnVuY3Rpb24gKHBvcykge1xuICB0aGlzLnJhaXNlKHBvcyAhPSBudWxsID8gcG9zIDogdGhpcy5zdGFydCwgXCJVbmV4cGVjdGVkIHRva2VuXCIpO1xufTtcblxufSx7XCIuL3N0YXRlXCI6MTMsXCIuL3Rva2VudHlwZVwiOjE3LFwiLi93aGl0ZXNwYWNlXCI6MTl9XSwxMzpbZnVuY3Rpb24oX2RlcmVxXyxtb2R1bGUsZXhwb3J0cyl7XG5cInVzZSBzdHJpY3RcIjtcblxuZXhwb3J0cy5QYXJzZXIgPSBQYXJzZXI7XG5leHBvcnRzLl9fZXNNb2R1bGUgPSB0cnVlO1xuXG52YXIgX2lkZW50aWZpZXIgPSBfZGVyZXFfKFwiLi9pZGVudGlmaWVyXCIpO1xuXG52YXIgcmVzZXJ2ZWRXb3JkcyA9IF9pZGVudGlmaWVyLnJlc2VydmVkV29yZHM7XG52YXIga2V5d29yZHMgPSBfaWRlbnRpZmllci5rZXl3b3JkcztcblxudmFyIHR0ID0gX2RlcmVxXyhcIi4vdG9rZW50eXBlXCIpLnR5cGVzO1xuXG52YXIgbGluZUJyZWFrID0gX2RlcmVxXyhcIi4vd2hpdGVzcGFjZVwiKS5saW5lQnJlYWs7XG5cbmZ1bmN0aW9uIFBhcnNlcihvcHRpb25zLCBpbnB1dCwgc3RhcnRQb3MpIHtcbiAgdGhpcy5vcHRpb25zID0gb3B0aW9ucztcbiAgdGhpcy5zb3VyY2VGaWxlID0gdGhpcy5vcHRpb25zLnNvdXJjZUZpbGUgfHwgbnVsbDtcbiAgdGhpcy5pc0tleXdvcmQgPSBrZXl3b3Jkc1t0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNiA/IDYgOiA1XTtcbiAgdGhpcy5pc1Jlc2VydmVkV29yZCA9IHJlc2VydmVkV29yZHNbdGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uXTtcbiAgdGhpcy5pbnB1dCA9IGlucHV0O1xuXG4gIC8vIExvYWQgcGx1Z2luc1xuICB0aGlzLmxvYWRQbHVnaW5zKHRoaXMub3B0aW9ucy5wbHVnaW5zKTtcblxuICAvLyBTZXQgdXAgdG9rZW4gc3RhdGVcblxuICAvLyBUaGUgY3VycmVudCBwb3NpdGlvbiBvZiB0aGUgdG9rZW5pemVyIGluIHRoZSBpbnB1dC5cbiAgaWYgKHN0YXJ0UG9zKSB7XG4gICAgdGhpcy5wb3MgPSBzdGFydFBvcztcbiAgICB0aGlzLmxpbmVTdGFydCA9IE1hdGgubWF4KDAsIHRoaXMuaW5wdXQubGFzdEluZGV4T2YoXCJcXG5cIiwgc3RhcnRQb3MpKTtcbiAgICB0aGlzLmN1ckxpbmUgPSB0aGlzLmlucHV0LnNsaWNlKDAsIHRoaXMubGluZVN0YXJ0KS5zcGxpdChsaW5lQnJlYWspLmxlbmd0aDtcbiAgfSBlbHNlIHtcbiAgICB0aGlzLnBvcyA9IHRoaXMubGluZVN0YXJ0ID0gMDtcbiAgICB0aGlzLmN1ckxpbmUgPSAxO1xuICB9XG5cbiAgLy8gUHJvcGVydGllcyBvZiB0aGUgY3VycmVudCB0b2tlbjpcbiAgLy8gSXRzIHR5cGVcbiAgdGhpcy50eXBlID0gdHQuZW9mO1xuICAvLyBGb3IgdG9rZW5zIHRoYXQgaW5jbHVkZSBtb3JlIGluZm9ybWF0aW9uIHRoYW4gdGhlaXIgdHlwZSwgdGhlIHZhbHVlXG4gIHRoaXMudmFsdWUgPSBudWxsO1xuICAvLyBJdHMgc3RhcnQgYW5kIGVuZCBvZmZzZXRcbiAgdGhpcy5zdGFydCA9IHRoaXMuZW5kID0gdGhpcy5wb3M7XG4gIC8vIEFuZCwgaWYgbG9jYXRpb25zIGFyZSB1c2VkLCB0aGUge2xpbmUsIGNvbHVtbn0gb2JqZWN0XG4gIC8vIGNvcnJlc3BvbmRpbmcgdG8gdGhvc2Ugb2Zmc2V0c1xuICB0aGlzLnN0YXJ0TG9jID0gdGhpcy5lbmRMb2MgPSBudWxsO1xuXG4gIC8vIFBvc2l0aW9uIGluZm9ybWF0aW9uIGZvciB0aGUgcHJldmlvdXMgdG9rZW5cbiAgdGhpcy5sYXN0VG9rRW5kTG9jID0gdGhpcy5sYXN0VG9rU3RhcnRMb2MgPSBudWxsO1xuICB0aGlzLmxhc3RUb2tTdGFydCA9IHRoaXMubGFzdFRva0VuZCA9IHRoaXMucG9zO1xuXG4gIC8vIFRoZSBjb250ZXh0IHN0YWNrIGlzIHVzZWQgdG8gc3VwZXJmaWNpYWxseSB0cmFjayBzeW50YWN0aWNcbiAgLy8gY29udGV4dCB0byBwcmVkaWN0IHdoZXRoZXIgYSByZWd1bGFyIGV4cHJlc3Npb24gaXMgYWxsb3dlZCBpbiBhXG4gIC8vIGdpdmVuIHBvc2l0aW9uLlxuICB0aGlzLmNvbnRleHQgPSB0aGlzLmluaXRpYWxDb250ZXh0KCk7XG4gIHRoaXMuZXhwckFsbG93ZWQgPSB0cnVlO1xuXG4gIC8vIEZpZ3VyZSBvdXQgaWYgaXQncyBhIG1vZHVsZSBjb2RlLlxuICB0aGlzLnN0cmljdCA9IHRoaXMuaW5Nb2R1bGUgPSB0aGlzLm9wdGlvbnMuc291cmNlVHlwZSA9PT0gXCJtb2R1bGVcIjtcblxuICAvLyBVc2VkIHRvIHNpZ25pZnkgdGhlIHN0YXJ0IG9mIGEgcG90ZW50aWFsIGFycm93IGZ1bmN0aW9uXG4gIHRoaXMucG90ZW50aWFsQXJyb3dBdCA9IC0xO1xuXG4gIC8vIEZsYWdzIHRvIHRyYWNrIHdoZXRoZXIgd2UgYXJlIGluIGEgZnVuY3Rpb24sIGEgZ2VuZXJhdG9yLlxuICB0aGlzLmluRnVuY3Rpb24gPSB0aGlzLmluR2VuZXJhdG9yID0gZmFsc2U7XG4gIC8vIExhYmVscyBpbiBzY29wZS5cbiAgdGhpcy5sYWJlbHMgPSBbXTtcblxuICAvLyBJZiBlbmFibGVkLCBza2lwIGxlYWRpbmcgaGFzaGJhbmcgbGluZS5cbiAgaWYgKHRoaXMucG9zID09PSAwICYmIHRoaXMub3B0aW9ucy5hbGxvd0hhc2hCYW5nICYmIHRoaXMuaW5wdXQuc2xpY2UoMCwgMikgPT09IFwiIyFcIikgdGhpcy5za2lwTGluZUNvbW1lbnQoMik7XG59XG5cblBhcnNlci5wcm90b3R5cGUuZXh0ZW5kID0gZnVuY3Rpb24gKG5hbWUsIGYpIHtcbiAgdGhpc1tuYW1lXSA9IGYodGhpc1tuYW1lXSk7XG59O1xuXG4vLyBSZWdpc3RlcmVkIHBsdWdpbnNcblxudmFyIHBsdWdpbnMgPSB7fTtcblxuZXhwb3J0cy5wbHVnaW5zID0gcGx1Z2lucztcblBhcnNlci5wcm90b3R5cGUubG9hZFBsdWdpbnMgPSBmdW5jdGlvbiAocGx1Z2lucykge1xuICBmb3IgKHZhciBfbmFtZSBpbiBwbHVnaW5zKSB7XG4gICAgdmFyIHBsdWdpbiA9IGV4cG9ydHMucGx1Z2luc1tfbmFtZV07XG4gICAgaWYgKCFwbHVnaW4pIHRocm93IG5ldyBFcnJvcihcIlBsdWdpbiAnXCIgKyBfbmFtZSArIFwiJyBub3QgZm91bmRcIik7XG4gICAgcGx1Z2luKHRoaXMsIHBsdWdpbnNbX25hbWVdKTtcbiAgfVxufTtcblxufSx7XCIuL2lkZW50aWZpZXJcIjo3LFwiLi90b2tlbnR5cGVcIjoxNyxcIi4vd2hpdGVzcGFjZVwiOjE5fV0sMTQ6W2Z1bmN0aW9uKF9kZXJlcV8sbW9kdWxlLGV4cG9ydHMpe1xuXCJ1c2Ugc3RyaWN0XCI7XG5cbnZhciB0dCA9IF9kZXJlcV8oXCIuL3Rva2VudHlwZVwiKS50eXBlcztcblxudmFyIFBhcnNlciA9IF9kZXJlcV8oXCIuL3N0YXRlXCIpLlBhcnNlcjtcblxudmFyIGxpbmVCcmVhayA9IF9kZXJlcV8oXCIuL3doaXRlc3BhY2VcIikubGluZUJyZWFrO1xuXG52YXIgcHAgPSBQYXJzZXIucHJvdG90eXBlO1xuXG4vLyAjIyMgU3RhdGVtZW50IHBhcnNpbmdcblxuLy8gUGFyc2UgYSBwcm9ncmFtLiBJbml0aWFsaXplcyB0aGUgcGFyc2VyLCByZWFkcyBhbnkgbnVtYmVyIG9mXG4vLyBzdGF0ZW1lbnRzLCBhbmQgd3JhcHMgdGhlbSBpbiBhIFByb2dyYW0gbm9kZS4gIE9wdGlvbmFsbHkgdGFrZXMgYVxuLy8gYHByb2dyYW1gIGFyZ3VtZW50LiAgSWYgcHJlc2VudCwgdGhlIHN0YXRlbWVudHMgd2lsbCBiZSBhcHBlbmRlZFxuLy8gdG8gaXRzIGJvZHkgaW5zdGVhZCBvZiBjcmVhdGluZyBhIG5ldyBub2RlLlxuXG5wcC5wYXJzZVRvcExldmVsID0gZnVuY3Rpb24gKG5vZGUpIHtcbiAgdmFyIGZpcnN0ID0gdHJ1ZTtcbiAgaWYgKCFub2RlLmJvZHkpIG5vZGUuYm9keSA9IFtdO1xuICB3aGlsZSAodGhpcy50eXBlICE9PSB0dC5lb2YpIHtcbiAgICB2YXIgc3RtdCA9IHRoaXMucGFyc2VTdGF0ZW1lbnQodHJ1ZSwgdHJ1ZSk7XG4gICAgbm9kZS5ib2R5LnB1c2goc3RtdCk7XG4gICAgaWYgKGZpcnN0ICYmIHRoaXMuaXNVc2VTdHJpY3Qoc3RtdCkpIHRoaXMuc2V0U3RyaWN0KHRydWUpO1xuICAgIGZpcnN0ID0gZmFsc2U7XG4gIH1cbiAgdGhpcy5uZXh0KCk7XG4gIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNikge1xuICAgIG5vZGUuc291cmNlVHlwZSA9IHRoaXMub3B0aW9ucy5zb3VyY2VUeXBlO1xuICB9XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJQcm9ncmFtXCIpO1xufTtcblxudmFyIGxvb3BMYWJlbCA9IHsga2luZDogXCJsb29wXCIgfSxcbiAgICBzd2l0Y2hMYWJlbCA9IHsga2luZDogXCJzd2l0Y2hcIiB9O1xuXG4vLyBQYXJzZSBhIHNpbmdsZSBzdGF0ZW1lbnQuXG4vL1xuLy8gSWYgZXhwZWN0aW5nIGEgc3RhdGVtZW50IGFuZCBmaW5kaW5nIGEgc2xhc2ggb3BlcmF0b3IsIHBhcnNlIGFcbi8vIHJlZ3VsYXIgZXhwcmVzc2lvbiBsaXRlcmFsLiBUaGlzIGlzIHRvIGhhbmRsZSBjYXNlcyBsaWtlXG4vLyBgaWYgKGZvbykgL2JsYWgvLmV4ZWMoZm9vKWAsIHdoZXJlIGxvb2tpbmcgYXQgdGhlIHByZXZpb3VzIHRva2VuXG4vLyBkb2VzIG5vdCBoZWxwLlxuXG5wcC5wYXJzZVN0YXRlbWVudCA9IGZ1bmN0aW9uIChkZWNsYXJhdGlvbiwgdG9wTGV2ZWwpIHtcbiAgdmFyIHN0YXJ0dHlwZSA9IHRoaXMudHlwZSxcbiAgICAgIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuXG4gIC8vIE1vc3QgdHlwZXMgb2Ygc3RhdGVtZW50cyBhcmUgcmVjb2duaXplZCBieSB0aGUga2V5d29yZCB0aGV5XG4gIC8vIHN0YXJ0IHdpdGguIE1hbnkgYXJlIHRyaXZpYWwgdG8gcGFyc2UsIHNvbWUgcmVxdWlyZSBhIGJpdCBvZlxuICAvLyBjb21wbGV4aXR5LlxuXG4gIHN3aXRjaCAoc3RhcnR0eXBlKSB7XG4gICAgY2FzZSB0dC5fYnJlYWs6Y2FzZSB0dC5fY29udGludWU6XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZUJyZWFrQ29udGludWVTdGF0ZW1lbnQobm9kZSwgc3RhcnR0eXBlLmtleXdvcmQpO1xuICAgIGNhc2UgdHQuX2RlYnVnZ2VyOlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VEZWJ1Z2dlclN0YXRlbWVudChub2RlKTtcbiAgICBjYXNlIHR0Ll9kbzpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlRG9TdGF0ZW1lbnQobm9kZSk7XG4gICAgY2FzZSB0dC5fZm9yOlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VGb3JTdGF0ZW1lbnQobm9kZSk7XG4gICAgY2FzZSB0dC5fZnVuY3Rpb246XG4gICAgICBpZiAoIWRlY2xhcmF0aW9uICYmIHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KSB0aGlzLnVuZXhwZWN0ZWQoKTtcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlRnVuY3Rpb25TdGF0ZW1lbnQobm9kZSk7XG4gICAgY2FzZSB0dC5fY2xhc3M6XG4gICAgICBpZiAoIWRlY2xhcmF0aW9uKSB0aGlzLnVuZXhwZWN0ZWQoKTtcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlQ2xhc3Mobm9kZSwgdHJ1ZSk7XG4gICAgY2FzZSB0dC5faWY6XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZUlmU3RhdGVtZW50KG5vZGUpO1xuICAgIGNhc2UgdHQuX3JldHVybjpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlUmV0dXJuU3RhdGVtZW50KG5vZGUpO1xuICAgIGNhc2UgdHQuX3N3aXRjaDpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlU3dpdGNoU3RhdGVtZW50KG5vZGUpO1xuICAgIGNhc2UgdHQuX3Rocm93OlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VUaHJvd1N0YXRlbWVudChub2RlKTtcbiAgICBjYXNlIHR0Ll90cnk6XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZVRyeVN0YXRlbWVudChub2RlKTtcbiAgICBjYXNlIHR0Ll9sZXQ6Y2FzZSB0dC5fY29uc3Q6XG4gICAgICBpZiAoIWRlY2xhcmF0aW9uKSB0aGlzLnVuZXhwZWN0ZWQoKTsgLy8gTk9URTogZmFsbHMgdGhyb3VnaCB0byBfdmFyXG4gICAgY2FzZSB0dC5fdmFyOlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VWYXJTdGF0ZW1lbnQobm9kZSwgc3RhcnR0eXBlKTtcbiAgICBjYXNlIHR0Ll93aGlsZTpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlV2hpbGVTdGF0ZW1lbnQobm9kZSk7XG4gICAgY2FzZSB0dC5fd2l0aDpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlV2l0aFN0YXRlbWVudChub2RlKTtcbiAgICBjYXNlIHR0LmJyYWNlTDpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlQmxvY2soKTtcbiAgICBjYXNlIHR0LnNlbWk6XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZUVtcHR5U3RhdGVtZW50KG5vZGUpO1xuICAgIGNhc2UgdHQuX2V4cG9ydDpcbiAgICBjYXNlIHR0Ll9pbXBvcnQ6XG4gICAgICBpZiAoIXRoaXMub3B0aW9ucy5hbGxvd0ltcG9ydEV4cG9ydEV2ZXJ5d2hlcmUpIHtcbiAgICAgICAgaWYgKCF0b3BMZXZlbCkgdGhpcy5yYWlzZSh0aGlzLnN0YXJ0LCBcIidpbXBvcnQnIGFuZCAnZXhwb3J0JyBtYXkgb25seSBhcHBlYXIgYXQgdGhlIHRvcCBsZXZlbFwiKTtcbiAgICAgICAgaWYgKCF0aGlzLmluTW9kdWxlKSB0aGlzLnJhaXNlKHRoaXMuc3RhcnQsIFwiJ2ltcG9ydCcgYW5kICdleHBvcnQnIG1heSBhcHBlYXIgb25seSB3aXRoICdzb3VyY2VUeXBlOiBtb2R1bGUnXCIpO1xuICAgICAgfVxuICAgICAgcmV0dXJuIHN0YXJ0dHlwZSA9PT0gdHQuX2ltcG9ydCA/IHRoaXMucGFyc2VJbXBvcnQobm9kZSkgOiB0aGlzLnBhcnNlRXhwb3J0KG5vZGUpO1xuXG4gICAgLy8gSWYgdGhlIHN0YXRlbWVudCBkb2VzIG5vdCBzdGFydCB3aXRoIGEgc3RhdGVtZW50IGtleXdvcmQgb3IgYVxuICAgIC8vIGJyYWNlLCBpdCdzIGFuIEV4cHJlc3Npb25TdGF0ZW1lbnQgb3IgTGFiZWxlZFN0YXRlbWVudC4gV2VcbiAgICAvLyBzaW1wbHkgc3RhcnQgcGFyc2luZyBhbiBleHByZXNzaW9uLCBhbmQgYWZ0ZXJ3YXJkcywgaWYgdGhlXG4gICAgLy8gbmV4dCB0b2tlbiBpcyBhIGNvbG9uIGFuZCB0aGUgZXhwcmVzc2lvbiB3YXMgYSBzaW1wbGVcbiAgICAvLyBJZGVudGlmaWVyIG5vZGUsIHdlIHN3aXRjaCB0byBpbnRlcnByZXRpbmcgaXQgYXMgYSBsYWJlbC5cbiAgICBkZWZhdWx0OlxuICAgICAgdmFyIG1heWJlTmFtZSA9IHRoaXMudmFsdWUsXG4gICAgICAgICAgZXhwciA9IHRoaXMucGFyc2VFeHByZXNzaW9uKCk7XG4gICAgICBpZiAoc3RhcnR0eXBlID09PSB0dC5uYW1lICYmIGV4cHIudHlwZSA9PT0gXCJJZGVudGlmaWVyXCIgJiYgdGhpcy5lYXQodHQuY29sb24pKSByZXR1cm4gdGhpcy5wYXJzZUxhYmVsZWRTdGF0ZW1lbnQobm9kZSwgbWF5YmVOYW1lLCBleHByKTtlbHNlIHJldHVybiB0aGlzLnBhcnNlRXhwcmVzc2lvblN0YXRlbWVudChub2RlLCBleHByKTtcbiAgfVxufTtcblxucHAucGFyc2VCcmVha0NvbnRpbnVlU3RhdGVtZW50ID0gZnVuY3Rpb24gKG5vZGUsIGtleXdvcmQpIHtcbiAgdmFyIGlzQnJlYWsgPSBrZXl3b3JkID09IFwiYnJlYWtcIjtcbiAgdGhpcy5uZXh0KCk7XG4gIGlmICh0aGlzLmVhdCh0dC5zZW1pKSB8fCB0aGlzLmluc2VydFNlbWljb2xvbigpKSBub2RlLmxhYmVsID0gbnVsbDtlbHNlIGlmICh0aGlzLnR5cGUgIT09IHR0Lm5hbWUpIHRoaXMudW5leHBlY3RlZCgpO2Vsc2Uge1xuICAgIG5vZGUubGFiZWwgPSB0aGlzLnBhcnNlSWRlbnQoKTtcbiAgICB0aGlzLnNlbWljb2xvbigpO1xuICB9XG5cbiAgLy8gVmVyaWZ5IHRoYXQgdGhlcmUgaXMgYW4gYWN0dWFsIGRlc3RpbmF0aW9uIHRvIGJyZWFrIG9yXG4gIC8vIGNvbnRpbnVlIHRvLlxuICBmb3IgKHZhciBpID0gMDsgaSA8IHRoaXMubGFiZWxzLmxlbmd0aDsgKytpKSB7XG4gICAgdmFyIGxhYiA9IHRoaXMubGFiZWxzW2ldO1xuICAgIGlmIChub2RlLmxhYmVsID09IG51bGwgfHwgbGFiLm5hbWUgPT09IG5vZGUubGFiZWwubmFtZSkge1xuICAgICAgaWYgKGxhYi5raW5kICE9IG51bGwgJiYgKGlzQnJlYWsgfHwgbGFiLmtpbmQgPT09IFwibG9vcFwiKSkgYnJlYWs7XG4gICAgICBpZiAobm9kZS5sYWJlbCAmJiBpc0JyZWFrKSBicmVhaztcbiAgICB9XG4gIH1cbiAgaWYgKGkgPT09IHRoaXMubGFiZWxzLmxlbmd0aCkgdGhpcy5yYWlzZShub2RlLnN0YXJ0LCBcIlVuc3ludGFjdGljIFwiICsga2V5d29yZCk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgaXNCcmVhayA/IFwiQnJlYWtTdGF0ZW1lbnRcIiA6IFwiQ29udGludWVTdGF0ZW1lbnRcIik7XG59O1xuXG5wcC5wYXJzZURlYnVnZ2VyU3RhdGVtZW50ID0gZnVuY3Rpb24gKG5vZGUpIHtcbiAgdGhpcy5uZXh0KCk7XG4gIHRoaXMuc2VtaWNvbG9uKCk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJEZWJ1Z2dlclN0YXRlbWVudFwiKTtcbn07XG5cbnBwLnBhcnNlRG9TdGF0ZW1lbnQgPSBmdW5jdGlvbiAobm9kZSkge1xuICB0aGlzLm5leHQoKTtcbiAgdGhpcy5sYWJlbHMucHVzaChsb29wTGFiZWwpO1xuICBub2RlLmJvZHkgPSB0aGlzLnBhcnNlU3RhdGVtZW50KGZhbHNlKTtcbiAgdGhpcy5sYWJlbHMucG9wKCk7XG4gIHRoaXMuZXhwZWN0KHR0Ll93aGlsZSk7XG4gIG5vZGUudGVzdCA9IHRoaXMucGFyc2VQYXJlbkV4cHJlc3Npb24oKTtcbiAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KSB0aGlzLmVhdCh0dC5zZW1pKTtlbHNlIHRoaXMuc2VtaWNvbG9uKCk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJEb1doaWxlU3RhdGVtZW50XCIpO1xufTtcblxuLy8gRGlzYW1iaWd1YXRpbmcgYmV0d2VlbiBhIGBmb3JgIGFuZCBhIGBmb3JgL2BpbmAgb3IgYGZvcmAvYG9mYFxuLy8gbG9vcCBpcyBub24tdHJpdmlhbC4gQmFzaWNhbGx5LCB3ZSBoYXZlIHRvIHBhcnNlIHRoZSBpbml0IGB2YXJgXG4vLyBzdGF0ZW1lbnQgb3IgZXhwcmVzc2lvbiwgZGlzYWxsb3dpbmcgdGhlIGBpbmAgb3BlcmF0b3IgKHNlZVxuLy8gdGhlIHNlY29uZCBwYXJhbWV0ZXIgdG8gYHBhcnNlRXhwcmVzc2lvbmApLCBhbmQgdGhlbiBjaGVja1xuLy8gd2hldGhlciB0aGUgbmV4dCB0b2tlbiBpcyBgaW5gIG9yIGBvZmAuIFdoZW4gdGhlcmUgaXMgbm8gaW5pdFxuLy8gcGFydCAoc2VtaWNvbG9uIGltbWVkaWF0ZWx5IGFmdGVyIHRoZSBvcGVuaW5nIHBhcmVudGhlc2lzKSwgaXRcbi8vIGlzIGEgcmVndWxhciBgZm9yYCBsb29wLlxuXG5wcC5wYXJzZUZvclN0YXRlbWVudCA9IGZ1bmN0aW9uIChub2RlKSB7XG4gIHRoaXMubmV4dCgpO1xuICB0aGlzLmxhYmVscy5wdXNoKGxvb3BMYWJlbCk7XG4gIHRoaXMuZXhwZWN0KHR0LnBhcmVuTCk7XG4gIGlmICh0aGlzLnR5cGUgPT09IHR0LnNlbWkpIHJldHVybiB0aGlzLnBhcnNlRm9yKG5vZGUsIG51bGwpO1xuICBpZiAodGhpcy50eXBlID09PSB0dC5fdmFyIHx8IHRoaXMudHlwZSA9PT0gdHQuX2xldCB8fCB0aGlzLnR5cGUgPT09IHR0Ll9jb25zdCkge1xuICAgIHZhciBfaW5pdCA9IHRoaXMuc3RhcnROb2RlKCksXG4gICAgICAgIHZhcktpbmQgPSB0aGlzLnR5cGU7XG4gICAgdGhpcy5uZXh0KCk7XG4gICAgdGhpcy5wYXJzZVZhcihfaW5pdCwgdHJ1ZSwgdmFyS2luZCk7XG4gICAgdGhpcy5maW5pc2hOb2RlKF9pbml0LCBcIlZhcmlhYmxlRGVjbGFyYXRpb25cIik7XG4gICAgaWYgKCh0aGlzLnR5cGUgPT09IHR0Ll9pbiB8fCB0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNiAmJiB0aGlzLmlzQ29udGV4dHVhbChcIm9mXCIpKSAmJiBfaW5pdC5kZWNsYXJhdGlvbnMubGVuZ3RoID09PSAxICYmICEodmFyS2luZCAhPT0gdHQuX3ZhciAmJiBfaW5pdC5kZWNsYXJhdGlvbnNbMF0uaW5pdCkpIHJldHVybiB0aGlzLnBhcnNlRm9ySW4obm9kZSwgX2luaXQpO1xuICAgIHJldHVybiB0aGlzLnBhcnNlRm9yKG5vZGUsIF9pbml0KTtcbiAgfVxuICB2YXIgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcyA9IHsgc3RhcnQ6IDAgfTtcbiAgdmFyIGluaXQgPSB0aGlzLnBhcnNlRXhwcmVzc2lvbih0cnVlLCByZWZTaG9ydGhhbmREZWZhdWx0UG9zKTtcbiAgaWYgKHRoaXMudHlwZSA9PT0gdHQuX2luIHx8IHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2ICYmIHRoaXMuaXNDb250ZXh0dWFsKFwib2ZcIikpIHtcbiAgICB0aGlzLnRvQXNzaWduYWJsZShpbml0KTtcbiAgICB0aGlzLmNoZWNrTFZhbChpbml0KTtcbiAgICByZXR1cm4gdGhpcy5wYXJzZUZvckluKG5vZGUsIGluaXQpO1xuICB9IGVsc2UgaWYgKHJlZlNob3J0aGFuZERlZmF1bHRQb3Muc3RhcnQpIHtcbiAgICB0aGlzLnVuZXhwZWN0ZWQocmVmU2hvcnRoYW5kRGVmYXVsdFBvcy5zdGFydCk7XG4gIH1cbiAgcmV0dXJuIHRoaXMucGFyc2VGb3Iobm9kZSwgaW5pdCk7XG59O1xuXG5wcC5wYXJzZUZ1bmN0aW9uU3RhdGVtZW50ID0gZnVuY3Rpb24gKG5vZGUpIHtcbiAgdGhpcy5uZXh0KCk7XG4gIHJldHVybiB0aGlzLnBhcnNlRnVuY3Rpb24obm9kZSwgdHJ1ZSk7XG59O1xuXG5wcC5wYXJzZUlmU3RhdGVtZW50ID0gZnVuY3Rpb24gKG5vZGUpIHtcbiAgdGhpcy5uZXh0KCk7XG4gIG5vZGUudGVzdCA9IHRoaXMucGFyc2VQYXJlbkV4cHJlc3Npb24oKTtcbiAgbm9kZS5jb25zZXF1ZW50ID0gdGhpcy5wYXJzZVN0YXRlbWVudChmYWxzZSk7XG4gIG5vZGUuYWx0ZXJuYXRlID0gdGhpcy5lYXQodHQuX2Vsc2UpID8gdGhpcy5wYXJzZVN0YXRlbWVudChmYWxzZSkgOiBudWxsO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiSWZTdGF0ZW1lbnRcIik7XG59O1xuXG5wcC5wYXJzZVJldHVyblN0YXRlbWVudCA9IGZ1bmN0aW9uIChub2RlKSB7XG4gIGlmICghdGhpcy5pbkZ1bmN0aW9uICYmICF0aGlzLm9wdGlvbnMuYWxsb3dSZXR1cm5PdXRzaWRlRnVuY3Rpb24pIHRoaXMucmFpc2UodGhpcy5zdGFydCwgXCIncmV0dXJuJyBvdXRzaWRlIG9mIGZ1bmN0aW9uXCIpO1xuICB0aGlzLm5leHQoKTtcblxuICAvLyBJbiBgcmV0dXJuYCAoYW5kIGBicmVha2AvYGNvbnRpbnVlYCksIHRoZSBrZXl3b3JkcyB3aXRoXG4gIC8vIG9wdGlvbmFsIGFyZ3VtZW50cywgd2UgZWFnZXJseSBsb29rIGZvciBhIHNlbWljb2xvbiBvciB0aGVcbiAgLy8gcG9zc2liaWxpdHkgdG8gaW5zZXJ0IG9uZS5cblxuICBpZiAodGhpcy5lYXQodHQuc2VtaSkgfHwgdGhpcy5pbnNlcnRTZW1pY29sb24oKSkgbm9kZS5hcmd1bWVudCA9IG51bGw7ZWxzZSB7XG4gICAgbm9kZS5hcmd1bWVudCA9IHRoaXMucGFyc2VFeHByZXNzaW9uKCk7dGhpcy5zZW1pY29sb24oKTtcbiAgfVxuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiUmV0dXJuU3RhdGVtZW50XCIpO1xufTtcblxucHAucGFyc2VTd2l0Y2hTdGF0ZW1lbnQgPSBmdW5jdGlvbiAobm9kZSkge1xuICB0aGlzLm5leHQoKTtcbiAgbm9kZS5kaXNjcmltaW5hbnQgPSB0aGlzLnBhcnNlUGFyZW5FeHByZXNzaW9uKCk7XG4gIG5vZGUuY2FzZXMgPSBbXTtcbiAgdGhpcy5leHBlY3QodHQuYnJhY2VMKTtcbiAgdGhpcy5sYWJlbHMucHVzaChzd2l0Y2hMYWJlbCk7XG5cbiAgLy8gU3RhdGVtZW50cyB1bmRlciBtdXN0IGJlIGdyb3VwZWQgKGJ5IGxhYmVsKSBpbiBTd2l0Y2hDYXNlXG4gIC8vIG5vZGVzLiBgY3VyYCBpcyB1c2VkIHRvIGtlZXAgdGhlIG5vZGUgdGhhdCB3ZSBhcmUgY3VycmVudGx5XG4gIC8vIGFkZGluZyBzdGF0ZW1lbnRzIHRvLlxuXG4gIGZvciAodmFyIGN1ciwgc2F3RGVmYXVsdDsgdGhpcy50eXBlICE9IHR0LmJyYWNlUjspIHtcbiAgICBpZiAodGhpcy50eXBlID09PSB0dC5fY2FzZSB8fCB0aGlzLnR5cGUgPT09IHR0Ll9kZWZhdWx0KSB7XG4gICAgICB2YXIgaXNDYXNlID0gdGhpcy50eXBlID09PSB0dC5fY2FzZTtcbiAgICAgIGlmIChjdXIpIHRoaXMuZmluaXNoTm9kZShjdXIsIFwiU3dpdGNoQ2FzZVwiKTtcbiAgICAgIG5vZGUuY2FzZXMucHVzaChjdXIgPSB0aGlzLnN0YXJ0Tm9kZSgpKTtcbiAgICAgIGN1ci5jb25zZXF1ZW50ID0gW107XG4gICAgICB0aGlzLm5leHQoKTtcbiAgICAgIGlmIChpc0Nhc2UpIHtcbiAgICAgICAgY3VyLnRlc3QgPSB0aGlzLnBhcnNlRXhwcmVzc2lvbigpO1xuICAgICAgfSBlbHNlIHtcbiAgICAgICAgaWYgKHNhd0RlZmF1bHQpIHRoaXMucmFpc2UodGhpcy5sYXN0VG9rU3RhcnQsIFwiTXVsdGlwbGUgZGVmYXVsdCBjbGF1c2VzXCIpO1xuICAgICAgICBzYXdEZWZhdWx0ID0gdHJ1ZTtcbiAgICAgICAgY3VyLnRlc3QgPSBudWxsO1xuICAgICAgfVxuICAgICAgdGhpcy5leHBlY3QodHQuY29sb24pO1xuICAgIH0gZWxzZSB7XG4gICAgICBpZiAoIWN1cikgdGhpcy51bmV4cGVjdGVkKCk7XG4gICAgICBjdXIuY29uc2VxdWVudC5wdXNoKHRoaXMucGFyc2VTdGF0ZW1lbnQodHJ1ZSkpO1xuICAgIH1cbiAgfVxuICBpZiAoY3VyKSB0aGlzLmZpbmlzaE5vZGUoY3VyLCBcIlN3aXRjaENhc2VcIik7XG4gIHRoaXMubmV4dCgpOyAvLyBDbG9zaW5nIGJyYWNlXG4gIHRoaXMubGFiZWxzLnBvcCgpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiU3dpdGNoU3RhdGVtZW50XCIpO1xufTtcblxucHAucGFyc2VUaHJvd1N0YXRlbWVudCA9IGZ1bmN0aW9uIChub2RlKSB7XG4gIHRoaXMubmV4dCgpO1xuICBpZiAobGluZUJyZWFrLnRlc3QodGhpcy5pbnB1dC5zbGljZSh0aGlzLmxhc3RUb2tFbmQsIHRoaXMuc3RhcnQpKSkgdGhpcy5yYWlzZSh0aGlzLmxhc3RUb2tFbmQsIFwiSWxsZWdhbCBuZXdsaW5lIGFmdGVyIHRocm93XCIpO1xuICBub2RlLmFyZ3VtZW50ID0gdGhpcy5wYXJzZUV4cHJlc3Npb24oKTtcbiAgdGhpcy5zZW1pY29sb24oKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIlRocm93U3RhdGVtZW50XCIpO1xufTtcblxuLy8gUmV1c2VkIGVtcHR5IGFycmF5IGFkZGVkIGZvciBub2RlIGZpZWxkcyB0aGF0IGFyZSBhbHdheXMgZW1wdHkuXG5cbnZhciBlbXB0eSA9IFtdO1xuXG5wcC5wYXJzZVRyeVN0YXRlbWVudCA9IGZ1bmN0aW9uIChub2RlKSB7XG4gIHRoaXMubmV4dCgpO1xuICBub2RlLmJsb2NrID0gdGhpcy5wYXJzZUJsb2NrKCk7XG4gIG5vZGUuaGFuZGxlciA9IG51bGw7XG4gIGlmICh0aGlzLnR5cGUgPT09IHR0Ll9jYXRjaCkge1xuICAgIHZhciBjbGF1c2UgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICAgIHRoaXMubmV4dCgpO1xuICAgIHRoaXMuZXhwZWN0KHR0LnBhcmVuTCk7XG4gICAgY2xhdXNlLnBhcmFtID0gdGhpcy5wYXJzZUJpbmRpbmdBdG9tKCk7XG4gICAgdGhpcy5jaGVja0xWYWwoY2xhdXNlLnBhcmFtLCB0cnVlKTtcbiAgICB0aGlzLmV4cGVjdCh0dC5wYXJlblIpO1xuICAgIGNsYXVzZS5ndWFyZCA9IG51bGw7XG4gICAgY2xhdXNlLmJvZHkgPSB0aGlzLnBhcnNlQmxvY2soKTtcbiAgICBub2RlLmhhbmRsZXIgPSB0aGlzLmZpbmlzaE5vZGUoY2xhdXNlLCBcIkNhdGNoQ2xhdXNlXCIpO1xuICB9XG4gIG5vZGUuZ3VhcmRlZEhhbmRsZXJzID0gZW1wdHk7XG4gIG5vZGUuZmluYWxpemVyID0gdGhpcy5lYXQodHQuX2ZpbmFsbHkpID8gdGhpcy5wYXJzZUJsb2NrKCkgOiBudWxsO1xuICBpZiAoIW5vZGUuaGFuZGxlciAmJiAhbm9kZS5maW5hbGl6ZXIpIHRoaXMucmFpc2Uobm9kZS5zdGFydCwgXCJNaXNzaW5nIGNhdGNoIG9yIGZpbmFsbHkgY2xhdXNlXCIpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiVHJ5U3RhdGVtZW50XCIpO1xufTtcblxucHAucGFyc2VWYXJTdGF0ZW1lbnQgPSBmdW5jdGlvbiAobm9kZSwga2luZCkge1xuICB0aGlzLm5leHQoKTtcbiAgdGhpcy5wYXJzZVZhcihub2RlLCBmYWxzZSwga2luZCk7XG4gIHRoaXMuc2VtaWNvbG9uKCk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJWYXJpYWJsZURlY2xhcmF0aW9uXCIpO1xufTtcblxucHAucGFyc2VXaGlsZVN0YXRlbWVudCA9IGZ1bmN0aW9uIChub2RlKSB7XG4gIHRoaXMubmV4dCgpO1xuICBub2RlLnRlc3QgPSB0aGlzLnBhcnNlUGFyZW5FeHByZXNzaW9uKCk7XG4gIHRoaXMubGFiZWxzLnB1c2gobG9vcExhYmVsKTtcbiAgbm9kZS5ib2R5ID0gdGhpcy5wYXJzZVN0YXRlbWVudChmYWxzZSk7XG4gIHRoaXMubGFiZWxzLnBvcCgpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiV2hpbGVTdGF0ZW1lbnRcIik7XG59O1xuXG5wcC5wYXJzZVdpdGhTdGF0ZW1lbnQgPSBmdW5jdGlvbiAobm9kZSkge1xuICBpZiAodGhpcy5zdHJpY3QpIHRoaXMucmFpc2UodGhpcy5zdGFydCwgXCInd2l0aCcgaW4gc3RyaWN0IG1vZGVcIik7XG4gIHRoaXMubmV4dCgpO1xuICBub2RlLm9iamVjdCA9IHRoaXMucGFyc2VQYXJlbkV4cHJlc3Npb24oKTtcbiAgbm9kZS5ib2R5ID0gdGhpcy5wYXJzZVN0YXRlbWVudChmYWxzZSk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJXaXRoU3RhdGVtZW50XCIpO1xufTtcblxucHAucGFyc2VFbXB0eVN0YXRlbWVudCA9IGZ1bmN0aW9uIChub2RlKSB7XG4gIHRoaXMubmV4dCgpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiRW1wdHlTdGF0ZW1lbnRcIik7XG59O1xuXG5wcC5wYXJzZUxhYmVsZWRTdGF0ZW1lbnQgPSBmdW5jdGlvbiAobm9kZSwgbWF5YmVOYW1lLCBleHByKSB7XG4gIGZvciAodmFyIGkgPSAwOyBpIDwgdGhpcy5sYWJlbHMubGVuZ3RoOyArK2kpIHtcbiAgICBpZiAodGhpcy5sYWJlbHNbaV0ubmFtZSA9PT0gbWF5YmVOYW1lKSB0aGlzLnJhaXNlKGV4cHIuc3RhcnQsIFwiTGFiZWwgJ1wiICsgbWF5YmVOYW1lICsgXCInIGlzIGFscmVhZHkgZGVjbGFyZWRcIik7XG4gIH12YXIga2luZCA9IHRoaXMudHlwZS5pc0xvb3AgPyBcImxvb3BcIiA6IHRoaXMudHlwZSA9PT0gdHQuX3N3aXRjaCA/IFwic3dpdGNoXCIgOiBudWxsO1xuICB0aGlzLmxhYmVscy5wdXNoKHsgbmFtZTogbWF5YmVOYW1lLCBraW5kOiBraW5kIH0pO1xuICBub2RlLmJvZHkgPSB0aGlzLnBhcnNlU3RhdGVtZW50KHRydWUpO1xuICB0aGlzLmxhYmVscy5wb3AoKTtcbiAgbm9kZS5sYWJlbCA9IGV4cHI7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJMYWJlbGVkU3RhdGVtZW50XCIpO1xufTtcblxucHAucGFyc2VFeHByZXNzaW9uU3RhdGVtZW50ID0gZnVuY3Rpb24gKG5vZGUsIGV4cHIpIHtcbiAgbm9kZS5leHByZXNzaW9uID0gZXhwcjtcbiAgdGhpcy5zZW1pY29sb24oKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkV4cHJlc3Npb25TdGF0ZW1lbnRcIik7XG59O1xuXG4vLyBQYXJzZSBhIHNlbWljb2xvbi1lbmNsb3NlZCBibG9jayBvZiBzdGF0ZW1lbnRzLCBoYW5kbGluZyBgXCJ1c2Vcbi8vIHN0cmljdFwiYCBkZWNsYXJhdGlvbnMgd2hlbiBgYWxsb3dTdHJpY3RgIGlzIHRydWUgKHVzZWQgZm9yXG4vLyBmdW5jdGlvbiBib2RpZXMpLlxuXG5wcC5wYXJzZUJsb2NrID0gZnVuY3Rpb24gKGFsbG93U3RyaWN0KSB7XG4gIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGUoKSxcbiAgICAgIGZpcnN0ID0gdHJ1ZSxcbiAgICAgIG9sZFN0cmljdCA9IHVuZGVmaW5lZDtcbiAgbm9kZS5ib2R5ID0gW107XG4gIHRoaXMuZXhwZWN0KHR0LmJyYWNlTCk7XG4gIHdoaWxlICghdGhpcy5lYXQodHQuYnJhY2VSKSkge1xuICAgIHZhciBzdG10ID0gdGhpcy5wYXJzZVN0YXRlbWVudCh0cnVlKTtcbiAgICBub2RlLmJvZHkucHVzaChzdG10KTtcbiAgICBpZiAoZmlyc3QgJiYgYWxsb3dTdHJpY3QgJiYgdGhpcy5pc1VzZVN0cmljdChzdG10KSkge1xuICAgICAgb2xkU3RyaWN0ID0gdGhpcy5zdHJpY3Q7XG4gICAgICB0aGlzLnNldFN0cmljdCh0aGlzLnN0cmljdCA9IHRydWUpO1xuICAgIH1cbiAgICBmaXJzdCA9IGZhbHNlO1xuICB9XG4gIGlmIChvbGRTdHJpY3QgPT09IGZhbHNlKSB0aGlzLnNldFN0cmljdChmYWxzZSk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJCbG9ja1N0YXRlbWVudFwiKTtcbn07XG5cbi8vIFBhcnNlIGEgcmVndWxhciBgZm9yYCBsb29wLiBUaGUgZGlzYW1iaWd1YXRpb24gY29kZSBpblxuLy8gYHBhcnNlU3RhdGVtZW50YCB3aWxsIGFscmVhZHkgaGF2ZSBwYXJzZWQgdGhlIGluaXQgc3RhdGVtZW50IG9yXG4vLyBleHByZXNzaW9uLlxuXG5wcC5wYXJzZUZvciA9IGZ1bmN0aW9uIChub2RlLCBpbml0KSB7XG4gIG5vZGUuaW5pdCA9IGluaXQ7XG4gIHRoaXMuZXhwZWN0KHR0LnNlbWkpO1xuICBub2RlLnRlc3QgPSB0aGlzLnR5cGUgPT09IHR0LnNlbWkgPyBudWxsIDogdGhpcy5wYXJzZUV4cHJlc3Npb24oKTtcbiAgdGhpcy5leHBlY3QodHQuc2VtaSk7XG4gIG5vZGUudXBkYXRlID0gdGhpcy50eXBlID09PSB0dC5wYXJlblIgPyBudWxsIDogdGhpcy5wYXJzZUV4cHJlc3Npb24oKTtcbiAgdGhpcy5leHBlY3QodHQucGFyZW5SKTtcbiAgbm9kZS5ib2R5ID0gdGhpcy5wYXJzZVN0YXRlbWVudChmYWxzZSk7XG4gIHRoaXMubGFiZWxzLnBvcCgpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiRm9yU3RhdGVtZW50XCIpO1xufTtcblxuLy8gUGFyc2UgYSBgZm9yYC9gaW5gIGFuZCBgZm9yYC9gb2ZgIGxvb3AsIHdoaWNoIGFyZSBhbG1vc3Rcbi8vIHNhbWUgZnJvbSBwYXJzZXIncyBwZXJzcGVjdGl2ZS5cblxucHAucGFyc2VGb3JJbiA9IGZ1bmN0aW9uIChub2RlLCBpbml0KSB7XG4gIHZhciB0eXBlID0gdGhpcy50eXBlID09PSB0dC5faW4gPyBcIkZvckluU3RhdGVtZW50XCIgOiBcIkZvck9mU3RhdGVtZW50XCI7XG4gIHRoaXMubmV4dCgpO1xuICBub2RlLmxlZnQgPSBpbml0O1xuICBub2RlLnJpZ2h0ID0gdGhpcy5wYXJzZUV4cHJlc3Npb24oKTtcbiAgdGhpcy5leHBlY3QodHQucGFyZW5SKTtcbiAgbm9kZS5ib2R5ID0gdGhpcy5wYXJzZVN0YXRlbWVudChmYWxzZSk7XG4gIHRoaXMubGFiZWxzLnBvcCgpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIHR5cGUpO1xufTtcblxuLy8gUGFyc2UgYSBsaXN0IG9mIHZhcmlhYmxlIGRlY2xhcmF0aW9ucy5cblxucHAucGFyc2VWYXIgPSBmdW5jdGlvbiAobm9kZSwgaXNGb3IsIGtpbmQpIHtcbiAgbm9kZS5kZWNsYXJhdGlvbnMgPSBbXTtcbiAgbm9kZS5raW5kID0ga2luZC5rZXl3b3JkO1xuICBmb3IgKDs7KSB7XG4gICAgdmFyIGRlY2wgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICAgIHRoaXMucGFyc2VWYXJJZChkZWNsKTtcbiAgICBpZiAodGhpcy5lYXQodHQuZXEpKSB7XG4gICAgICBkZWNsLmluaXQgPSB0aGlzLnBhcnNlTWF5YmVBc3NpZ24oaXNGb3IpO1xuICAgIH0gZWxzZSBpZiAoa2luZCA9PT0gdHQuX2NvbnN0ICYmICEodGhpcy50eXBlID09PSB0dC5faW4gfHwgdGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYgJiYgdGhpcy5pc0NvbnRleHR1YWwoXCJvZlwiKSkpIHtcbiAgICAgIHRoaXMudW5leHBlY3RlZCgpO1xuICAgIH0gZWxzZSBpZiAoZGVjbC5pZC50eXBlICE9IFwiSWRlbnRpZmllclwiICYmICEoaXNGb3IgJiYgKHRoaXMudHlwZSA9PT0gdHQuX2luIHx8IHRoaXMuaXNDb250ZXh0dWFsKFwib2ZcIikpKSkge1xuICAgICAgdGhpcy5yYWlzZSh0aGlzLmxhc3RUb2tFbmQsIFwiQ29tcGxleCBiaW5kaW5nIHBhdHRlcm5zIHJlcXVpcmUgYW4gaW5pdGlhbGl6YXRpb24gdmFsdWVcIik7XG4gICAgfSBlbHNlIHtcbiAgICAgIGRlY2wuaW5pdCA9IG51bGw7XG4gICAgfVxuICAgIG5vZGUuZGVjbGFyYXRpb25zLnB1c2godGhpcy5maW5pc2hOb2RlKGRlY2wsIFwiVmFyaWFibGVEZWNsYXJhdG9yXCIpKTtcbiAgICBpZiAoIXRoaXMuZWF0KHR0LmNvbW1hKSkgYnJlYWs7XG4gIH1cbiAgcmV0dXJuIG5vZGU7XG59O1xuXG5wcC5wYXJzZVZhcklkID0gZnVuY3Rpb24gKGRlY2wpIHtcbiAgZGVjbC5pZCA9IHRoaXMucGFyc2VCaW5kaW5nQXRvbSgpO1xuICB0aGlzLmNoZWNrTFZhbChkZWNsLmlkLCB0cnVlKTtcbn07XG5cbi8vIFBhcnNlIGEgZnVuY3Rpb24gZGVjbGFyYXRpb24gb3IgbGl0ZXJhbCAoZGVwZW5kaW5nIG9uIHRoZVxuLy8gYGlzU3RhdGVtZW50YCBwYXJhbWV0ZXIpLlxuXG5wcC5wYXJzZUZ1bmN0aW9uID0gZnVuY3Rpb24gKG5vZGUsIGlzU3RhdGVtZW50LCBhbGxvd0V4cHJlc3Npb25Cb2R5KSB7XG4gIHRoaXMuaW5pdEZ1bmN0aW9uKG5vZGUpO1xuICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYpIG5vZGUuZ2VuZXJhdG9yID0gdGhpcy5lYXQodHQuc3Rhcik7XG4gIGlmIChpc1N0YXRlbWVudCB8fCB0aGlzLnR5cGUgPT09IHR0Lm5hbWUpIG5vZGUuaWQgPSB0aGlzLnBhcnNlSWRlbnQoKTtcbiAgdGhpcy5wYXJzZUZ1bmN0aW9uUGFyYW1zKG5vZGUpO1xuICB0aGlzLnBhcnNlRnVuY3Rpb25Cb2R5KG5vZGUsIGFsbG93RXhwcmVzc2lvbkJvZHkpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIGlzU3RhdGVtZW50ID8gXCJGdW5jdGlvbkRlY2xhcmF0aW9uXCIgOiBcIkZ1bmN0aW9uRXhwcmVzc2lvblwiKTtcbn07XG5cbnBwLnBhcnNlRnVuY3Rpb25QYXJhbXMgPSBmdW5jdGlvbiAobm9kZSkge1xuICB0aGlzLmV4cGVjdCh0dC5wYXJlbkwpO1xuICBub2RlLnBhcmFtcyA9IHRoaXMucGFyc2VCaW5kaW5nTGlzdCh0dC5wYXJlblIsIGZhbHNlLCBmYWxzZSk7XG59O1xuXG4vLyBQYXJzZSBhIGNsYXNzIGRlY2xhcmF0aW9uIG9yIGxpdGVyYWwgKGRlcGVuZGluZyBvbiB0aGVcbi8vIGBpc1N0YXRlbWVudGAgcGFyYW1ldGVyKS5cblxucHAucGFyc2VDbGFzcyA9IGZ1bmN0aW9uIChub2RlLCBpc1N0YXRlbWVudCkge1xuICB0aGlzLm5leHQoKTtcbiAgdGhpcy5wYXJzZUNsYXNzSWQobm9kZSwgaXNTdGF0ZW1lbnQpO1xuICB0aGlzLnBhcnNlQ2xhc3NTdXBlcihub2RlKTtcbiAgdmFyIGNsYXNzQm9keSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gIHZhciBoYWRDb25zdHJ1Y3RvciA9IGZhbHNlO1xuICBjbGFzc0JvZHkuYm9keSA9IFtdO1xuICB0aGlzLmV4cGVjdCh0dC5icmFjZUwpO1xuICB3aGlsZSAoIXRoaXMuZWF0KHR0LmJyYWNlUikpIHtcbiAgICBpZiAodGhpcy5lYXQodHQuc2VtaSkpIGNvbnRpbnVlO1xuICAgIHZhciBtZXRob2QgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICAgIHZhciBpc0dlbmVyYXRvciA9IHRoaXMuZWF0KHR0LnN0YXIpO1xuICAgIHZhciBpc01heWJlU3RhdGljID0gdGhpcy50eXBlID09PSB0dC5uYW1lICYmIHRoaXMudmFsdWUgPT09IFwic3RhdGljXCI7XG4gICAgdGhpcy5wYXJzZVByb3BlcnR5TmFtZShtZXRob2QpO1xuICAgIG1ldGhvZFtcInN0YXRpY1wiXSA9IGlzTWF5YmVTdGF0aWMgJiYgdGhpcy50eXBlICE9PSB0dC5wYXJlbkw7XG4gICAgaWYgKG1ldGhvZFtcInN0YXRpY1wiXSkge1xuICAgICAgaWYgKGlzR2VuZXJhdG9yKSB0aGlzLnVuZXhwZWN0ZWQoKTtcbiAgICAgIGlzR2VuZXJhdG9yID0gdGhpcy5lYXQodHQuc3Rhcik7XG4gICAgICB0aGlzLnBhcnNlUHJvcGVydHlOYW1lKG1ldGhvZCk7XG4gICAgfVxuICAgIG1ldGhvZC5raW5kID0gXCJtZXRob2RcIjtcbiAgICBpZiAoIW1ldGhvZC5jb21wdXRlZCkge1xuICAgICAgdmFyIGtleSA9IG1ldGhvZC5rZXk7XG5cbiAgICAgIHZhciBpc0dldFNldCA9IGZhbHNlO1xuICAgICAgaWYgKCFpc0dlbmVyYXRvciAmJiBrZXkudHlwZSA9PT0gXCJJZGVudGlmaWVyXCIgJiYgdGhpcy50eXBlICE9PSB0dC5wYXJlbkwgJiYgKGtleS5uYW1lID09PSBcImdldFwiIHx8IGtleS5uYW1lID09PSBcInNldFwiKSkge1xuICAgICAgICBpc0dldFNldCA9IHRydWU7XG4gICAgICAgIG1ldGhvZC5raW5kID0ga2V5Lm5hbWU7XG4gICAgICAgIGtleSA9IHRoaXMucGFyc2VQcm9wZXJ0eU5hbWUobWV0aG9kKTtcbiAgICAgIH1cbiAgICAgIGlmICghbWV0aG9kW1wic3RhdGljXCJdICYmIChrZXkudHlwZSA9PT0gXCJJZGVudGlmaWVyXCIgJiYga2V5Lm5hbWUgPT09IFwiY29uc3RydWN0b3JcIiB8fCBrZXkudHlwZSA9PT0gXCJMaXRlcmFsXCIgJiYga2V5LnZhbHVlID09PSBcImNvbnN0cnVjdG9yXCIpKSB7XG4gICAgICAgIGlmIChoYWRDb25zdHJ1Y3RvcikgdGhpcy5yYWlzZShrZXkuc3RhcnQsIFwiRHVwbGljYXRlIGNvbnN0cnVjdG9yIGluIHRoZSBzYW1lIGNsYXNzXCIpO1xuICAgICAgICBpZiAoaXNHZXRTZXQpIHRoaXMucmFpc2Uoa2V5LnN0YXJ0LCBcIkNvbnN0cnVjdG9yIGNhbid0IGhhdmUgZ2V0L3NldCBtb2RpZmllclwiKTtcbiAgICAgICAgaWYgKGlzR2VuZXJhdG9yKSB0aGlzLnJhaXNlKGtleS5zdGFydCwgXCJDb25zdHJ1Y3RvciBjYW4ndCBiZSBhIGdlbmVyYXRvclwiKTtcbiAgICAgICAgbWV0aG9kLmtpbmQgPSBcImNvbnN0cnVjdG9yXCI7XG4gICAgICAgIGhhZENvbnN0cnVjdG9yID0gdHJ1ZTtcbiAgICAgIH1cbiAgICB9XG4gICAgdGhpcy5wYXJzZUNsYXNzTWV0aG9kKGNsYXNzQm9keSwgbWV0aG9kLCBpc0dlbmVyYXRvcik7XG4gIH1cbiAgbm9kZS5ib2R5ID0gdGhpcy5maW5pc2hOb2RlKGNsYXNzQm9keSwgXCJDbGFzc0JvZHlcIik7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgaXNTdGF0ZW1lbnQgPyBcIkNsYXNzRGVjbGFyYXRpb25cIiA6IFwiQ2xhc3NFeHByZXNzaW9uXCIpO1xufTtcblxucHAucGFyc2VDbGFzc01ldGhvZCA9IGZ1bmN0aW9uIChjbGFzc0JvZHksIG1ldGhvZCwgaXNHZW5lcmF0b3IpIHtcbiAgbWV0aG9kLnZhbHVlID0gdGhpcy5wYXJzZU1ldGhvZChpc0dlbmVyYXRvcik7XG4gIGNsYXNzQm9keS5ib2R5LnB1c2godGhpcy5maW5pc2hOb2RlKG1ldGhvZCwgXCJNZXRob2REZWZpbml0aW9uXCIpKTtcbn07XG5cbnBwLnBhcnNlQ2xhc3NJZCA9IGZ1bmN0aW9uIChub2RlLCBpc1N0YXRlbWVudCkge1xuICBub2RlLmlkID0gdGhpcy50eXBlID09PSB0dC5uYW1lID8gdGhpcy5wYXJzZUlkZW50KCkgOiBpc1N0YXRlbWVudCA/IHRoaXMudW5leHBlY3RlZCgpIDogbnVsbDtcbn07XG5cbnBwLnBhcnNlQ2xhc3NTdXBlciA9IGZ1bmN0aW9uIChub2RlKSB7XG4gIG5vZGUuc3VwZXJDbGFzcyA9IHRoaXMuZWF0KHR0Ll9leHRlbmRzKSA/IHRoaXMucGFyc2VFeHByU3Vic2NyaXB0cygpIDogbnVsbDtcbn07XG5cbi8vIFBhcnNlcyBtb2R1bGUgZXhwb3J0IGRlY2xhcmF0aW9uLlxuXG5wcC5wYXJzZUV4cG9ydCA9IGZ1bmN0aW9uIChub2RlKSB7XG4gIHRoaXMubmV4dCgpO1xuICAvLyBleHBvcnQgKiBmcm9tICcuLi4nXG4gIGlmICh0aGlzLmVhdCh0dC5zdGFyKSkge1xuICAgIHRoaXMuZXhwZWN0Q29udGV4dHVhbChcImZyb21cIik7XG4gICAgbm9kZS5zb3VyY2UgPSB0aGlzLnR5cGUgPT09IHR0LnN0cmluZyA/IHRoaXMucGFyc2VFeHByQXRvbSgpIDogdGhpcy51bmV4cGVjdGVkKCk7XG4gICAgdGhpcy5zZW1pY29sb24oKTtcbiAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiRXhwb3J0QWxsRGVjbGFyYXRpb25cIik7XG4gIH1cbiAgaWYgKHRoaXMuZWF0KHR0Ll9kZWZhdWx0KSkge1xuICAgIC8vIGV4cG9ydCBkZWZhdWx0IC4uLlxuICAgIHZhciBleHByID0gdGhpcy5wYXJzZU1heWJlQXNzaWduKCk7XG4gICAgdmFyIG5lZWRzU2VtaSA9IHRydWU7XG4gICAgaWYgKGV4cHIudHlwZSA9PSBcIkZ1bmN0aW9uRXhwcmVzc2lvblwiIHx8IGV4cHIudHlwZSA9PSBcIkNsYXNzRXhwcmVzc2lvblwiKSB7XG4gICAgICBuZWVkc1NlbWkgPSBmYWxzZTtcbiAgICAgIGlmIChleHByLmlkKSB7XG4gICAgICAgIGV4cHIudHlwZSA9IGV4cHIudHlwZSA9PSBcIkZ1bmN0aW9uRXhwcmVzc2lvblwiID8gXCJGdW5jdGlvbkRlY2xhcmF0aW9uXCIgOiBcIkNsYXNzRGVjbGFyYXRpb25cIjtcbiAgICAgIH1cbiAgICB9XG4gICAgbm9kZS5kZWNsYXJhdGlvbiA9IGV4cHI7XG4gICAgaWYgKG5lZWRzU2VtaSkgdGhpcy5zZW1pY29sb24oKTtcbiAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiRXhwb3J0RGVmYXVsdERlY2xhcmF0aW9uXCIpO1xuICB9XG4gIC8vIGV4cG9ydCB2YXJ8Y29uc3R8bGV0fGZ1bmN0aW9ufGNsYXNzIC4uLlxuICBpZiAodGhpcy5zaG91bGRQYXJzZUV4cG9ydFN0YXRlbWVudCgpKSB7XG4gICAgbm9kZS5kZWNsYXJhdGlvbiA9IHRoaXMucGFyc2VTdGF0ZW1lbnQodHJ1ZSk7XG4gICAgbm9kZS5zcGVjaWZpZXJzID0gW107XG4gICAgbm9kZS5zb3VyY2UgPSBudWxsO1xuICB9IGVsc2Uge1xuICAgIC8vIGV4cG9ydCB7IHgsIHkgYXMgeiB9IFtmcm9tICcuLi4nXVxuICAgIG5vZGUuZGVjbGFyYXRpb24gPSBudWxsO1xuICAgIG5vZGUuc3BlY2lmaWVycyA9IHRoaXMucGFyc2VFeHBvcnRTcGVjaWZpZXJzKCk7XG4gICAgaWYgKHRoaXMuZWF0Q29udGV4dHVhbChcImZyb21cIikpIHtcbiAgICAgIG5vZGUuc291cmNlID0gdGhpcy50eXBlID09PSB0dC5zdHJpbmcgPyB0aGlzLnBhcnNlRXhwckF0b20oKSA6IHRoaXMudW5leHBlY3RlZCgpO1xuICAgIH0gZWxzZSB7XG4gICAgICBub2RlLnNvdXJjZSA9IG51bGw7XG4gICAgfVxuICAgIHRoaXMuc2VtaWNvbG9uKCk7XG4gIH1cbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkV4cG9ydE5hbWVkRGVjbGFyYXRpb25cIik7XG59O1xuXG5wcC5zaG91bGRQYXJzZUV4cG9ydFN0YXRlbWVudCA9IGZ1bmN0aW9uICgpIHtcbiAgcmV0dXJuIHRoaXMudHlwZS5rZXl3b3JkO1xufTtcblxuLy8gUGFyc2VzIGEgY29tbWEtc2VwYXJhdGVkIGxpc3Qgb2YgbW9kdWxlIGV4cG9ydHMuXG5cbnBwLnBhcnNlRXhwb3J0U3BlY2lmaWVycyA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIG5vZGVzID0gW10sXG4gICAgICBmaXJzdCA9IHRydWU7XG4gIC8vIGV4cG9ydCB7IHgsIHkgYXMgeiB9IFtmcm9tICcuLi4nXVxuICB0aGlzLmV4cGVjdCh0dC5icmFjZUwpO1xuICB3aGlsZSAoIXRoaXMuZWF0KHR0LmJyYWNlUikpIHtcbiAgICBpZiAoIWZpcnN0KSB7XG4gICAgICB0aGlzLmV4cGVjdCh0dC5jb21tYSk7XG4gICAgICBpZiAodGhpcy5hZnRlclRyYWlsaW5nQ29tbWEodHQuYnJhY2VSKSkgYnJlYWs7XG4gICAgfSBlbHNlIGZpcnN0ID0gZmFsc2U7XG5cbiAgICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gICAgbm9kZS5sb2NhbCA9IHRoaXMucGFyc2VJZGVudCh0aGlzLnR5cGUgPT09IHR0Ll9kZWZhdWx0KTtcbiAgICBub2RlLmV4cG9ydGVkID0gdGhpcy5lYXRDb250ZXh0dWFsKFwiYXNcIikgPyB0aGlzLnBhcnNlSWRlbnQodHJ1ZSkgOiBub2RlLmxvY2FsO1xuICAgIG5vZGVzLnB1c2godGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiRXhwb3J0U3BlY2lmaWVyXCIpKTtcbiAgfVxuICByZXR1cm4gbm9kZXM7XG59O1xuXG4vLyBQYXJzZXMgaW1wb3J0IGRlY2xhcmF0aW9uLlxuXG5wcC5wYXJzZUltcG9ydCA9IGZ1bmN0aW9uIChub2RlKSB7XG4gIHRoaXMubmV4dCgpO1xuICAvLyBpbXBvcnQgJy4uLidcbiAgaWYgKHRoaXMudHlwZSA9PT0gdHQuc3RyaW5nKSB7XG4gICAgbm9kZS5zcGVjaWZpZXJzID0gZW1wdHk7XG4gICAgbm9kZS5zb3VyY2UgPSB0aGlzLnBhcnNlRXhwckF0b20oKTtcbiAgICBub2RlLmtpbmQgPSBcIlwiO1xuICB9IGVsc2Uge1xuICAgIG5vZGUuc3BlY2lmaWVycyA9IHRoaXMucGFyc2VJbXBvcnRTcGVjaWZpZXJzKCk7XG4gICAgdGhpcy5leHBlY3RDb250ZXh0dWFsKFwiZnJvbVwiKTtcbiAgICBub2RlLnNvdXJjZSA9IHRoaXMudHlwZSA9PT0gdHQuc3RyaW5nID8gdGhpcy5wYXJzZUV4cHJBdG9tKCkgOiB0aGlzLnVuZXhwZWN0ZWQoKTtcbiAgfVxuICB0aGlzLnNlbWljb2xvbigpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiSW1wb3J0RGVjbGFyYXRpb25cIik7XG59O1xuXG4vLyBQYXJzZXMgYSBjb21tYS1zZXBhcmF0ZWQgbGlzdCBvZiBtb2R1bGUgaW1wb3J0cy5cblxucHAucGFyc2VJbXBvcnRTcGVjaWZpZXJzID0gZnVuY3Rpb24gKCkge1xuICB2YXIgbm9kZXMgPSBbXSxcbiAgICAgIGZpcnN0ID0gdHJ1ZTtcbiAgaWYgKHRoaXMudHlwZSA9PT0gdHQubmFtZSkge1xuICAgIC8vIGltcG9ydCBkZWZhdWx0T2JqLCB7IHgsIHkgYXMgeiB9IGZyb20gJy4uLidcbiAgICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gICAgbm9kZS5sb2NhbCA9IHRoaXMucGFyc2VJZGVudCgpO1xuICAgIHRoaXMuY2hlY2tMVmFsKG5vZGUubG9jYWwsIHRydWUpO1xuICAgIG5vZGVzLnB1c2godGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiSW1wb3J0RGVmYXVsdFNwZWNpZmllclwiKSk7XG4gICAgaWYgKCF0aGlzLmVhdCh0dC5jb21tYSkpIHJldHVybiBub2RlcztcbiAgfVxuICBpZiAodGhpcy50eXBlID09PSB0dC5zdGFyKSB7XG4gICAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICAgIHRoaXMubmV4dCgpO1xuICAgIHRoaXMuZXhwZWN0Q29udGV4dHVhbChcImFzXCIpO1xuICAgIG5vZGUubG9jYWwgPSB0aGlzLnBhcnNlSWRlbnQoKTtcbiAgICB0aGlzLmNoZWNrTFZhbChub2RlLmxvY2FsLCB0cnVlKTtcbiAgICBub2Rlcy5wdXNoKHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkltcG9ydE5hbWVzcGFjZVNwZWNpZmllclwiKSk7XG4gICAgcmV0dXJuIG5vZGVzO1xuICB9XG4gIHRoaXMuZXhwZWN0KHR0LmJyYWNlTCk7XG4gIHdoaWxlICghdGhpcy5lYXQodHQuYnJhY2VSKSkge1xuICAgIGlmICghZmlyc3QpIHtcbiAgICAgIHRoaXMuZXhwZWN0KHR0LmNvbW1hKTtcbiAgICAgIGlmICh0aGlzLmFmdGVyVHJhaWxpbmdDb21tYSh0dC5icmFjZVIpKSBicmVhaztcbiAgICB9IGVsc2UgZmlyc3QgPSBmYWxzZTtcblxuICAgIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgICBub2RlLmltcG9ydGVkID0gdGhpcy5wYXJzZUlkZW50KHRydWUpO1xuICAgIG5vZGUubG9jYWwgPSB0aGlzLmVhdENvbnRleHR1YWwoXCJhc1wiKSA/IHRoaXMucGFyc2VJZGVudCgpIDogbm9kZS5pbXBvcnRlZDtcbiAgICB0aGlzLmNoZWNrTFZhbChub2RlLmxvY2FsLCB0cnVlKTtcbiAgICBub2Rlcy5wdXNoKHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkltcG9ydFNwZWNpZmllclwiKSk7XG4gIH1cbiAgcmV0dXJuIG5vZGVzO1xufTtcblxufSx7XCIuL3N0YXRlXCI6MTMsXCIuL3Rva2VudHlwZVwiOjE3LFwiLi93aGl0ZXNwYWNlXCI6MTl9XSwxNTpbZnVuY3Rpb24oX2RlcmVxXyxtb2R1bGUsZXhwb3J0cyl7XG5cInVzZSBzdHJpY3RcIjtcblxudmFyIF9jbGFzc0NhbGxDaGVjayA9IGZ1bmN0aW9uIChpbnN0YW5jZSwgQ29uc3RydWN0b3IpIHsgaWYgKCEoaW5zdGFuY2UgaW5zdGFuY2VvZiBDb25zdHJ1Y3RvcikpIHsgdGhyb3cgbmV3IFR5cGVFcnJvcihcIkNhbm5vdCBjYWxsIGEgY2xhc3MgYXMgYSBmdW5jdGlvblwiKTsgfSB9O1xuXG5leHBvcnRzLl9fZXNNb2R1bGUgPSB0cnVlO1xuLy8gVGhlIGFsZ29yaXRobSB1c2VkIHRvIGRldGVybWluZSB3aGV0aGVyIGEgcmVnZXhwIGNhbiBhcHBlYXIgYXQgYVxuLy8gZ2l2ZW4gcG9pbnQgaW4gdGhlIHByb2dyYW0gaXMgbG9vc2VseSBiYXNlZCBvbiBzd2VldC5qcycgYXBwcm9hY2guXG4vLyBTZWUgaHR0cHM6Ly9naXRodWIuY29tL21vemlsbGEvc3dlZXQuanMvd2lraS9kZXNpZ25cblxudmFyIFBhcnNlciA9IF9kZXJlcV8oXCIuL3N0YXRlXCIpLlBhcnNlcjtcblxudmFyIHR0ID0gX2RlcmVxXyhcIi4vdG9rZW50eXBlXCIpLnR5cGVzO1xuXG52YXIgbGluZUJyZWFrID0gX2RlcmVxXyhcIi4vd2hpdGVzcGFjZVwiKS5saW5lQnJlYWs7XG5cbnZhciBUb2tDb250ZXh0ID0gZXhwb3J0cy5Ub2tDb250ZXh0ID0gZnVuY3Rpb24gVG9rQ29udGV4dCh0b2tlbiwgaXNFeHByLCBwcmVzZXJ2ZVNwYWNlLCBvdmVycmlkZSkge1xuICBfY2xhc3NDYWxsQ2hlY2sodGhpcywgVG9rQ29udGV4dCk7XG5cbiAgdGhpcy50b2tlbiA9IHRva2VuO1xuICB0aGlzLmlzRXhwciA9IGlzRXhwcjtcbiAgdGhpcy5wcmVzZXJ2ZVNwYWNlID0gcHJlc2VydmVTcGFjZTtcbiAgdGhpcy5vdmVycmlkZSA9IG92ZXJyaWRlO1xufTtcblxudmFyIHR5cGVzID0ge1xuICBiX3N0YXQ6IG5ldyBUb2tDb250ZXh0KFwie1wiLCBmYWxzZSksXG4gIGJfZXhwcjogbmV3IFRva0NvbnRleHQoXCJ7XCIsIHRydWUpLFxuICBiX3RtcGw6IG5ldyBUb2tDb250ZXh0KFwiJHtcIiwgdHJ1ZSksXG4gIHBfc3RhdDogbmV3IFRva0NvbnRleHQoXCIoXCIsIGZhbHNlKSxcbiAgcF9leHByOiBuZXcgVG9rQ29udGV4dChcIihcIiwgdHJ1ZSksXG4gIHFfdG1wbDogbmV3IFRva0NvbnRleHQoXCJgXCIsIHRydWUsIHRydWUsIGZ1bmN0aW9uIChwKSB7XG4gICAgcmV0dXJuIHAucmVhZFRtcGxUb2tlbigpO1xuICB9KSxcbiAgZl9leHByOiBuZXcgVG9rQ29udGV4dChcImZ1bmN0aW9uXCIsIHRydWUpXG59O1xuXG5leHBvcnRzLnR5cGVzID0gdHlwZXM7XG52YXIgcHAgPSBQYXJzZXIucHJvdG90eXBlO1xuXG5wcC5pbml0aWFsQ29udGV4dCA9IGZ1bmN0aW9uICgpIHtcbiAgcmV0dXJuIFt0eXBlcy5iX3N0YXRdO1xufTtcblxucHAuYnJhY2VJc0Jsb2NrID0gZnVuY3Rpb24gKHByZXZUeXBlKSB7XG4gIHZhciBwYXJlbnQgPSB1bmRlZmluZWQ7XG4gIGlmIChwcmV2VHlwZSA9PT0gdHQuY29sb24gJiYgKHBhcmVudCA9IHRoaXMuY3VyQ29udGV4dCgpKS50b2tlbiA9PSBcIntcIikgcmV0dXJuICFwYXJlbnQuaXNFeHByO1xuICBpZiAocHJldlR5cGUgPT09IHR0Ll9yZXR1cm4pIHJldHVybiBsaW5lQnJlYWsudGVzdCh0aGlzLmlucHV0LnNsaWNlKHRoaXMubGFzdFRva0VuZCwgdGhpcy5zdGFydCkpO1xuICBpZiAocHJldlR5cGUgPT09IHR0Ll9lbHNlIHx8IHByZXZUeXBlID09PSB0dC5zZW1pIHx8IHByZXZUeXBlID09PSB0dC5lb2YpIHJldHVybiB0cnVlO1xuICBpZiAocHJldlR5cGUgPT0gdHQuYnJhY2VMKSByZXR1cm4gdGhpcy5jdXJDb250ZXh0KCkgPT09IHR5cGVzLmJfc3RhdDtcbiAgcmV0dXJuICF0aGlzLmV4cHJBbGxvd2VkO1xufTtcblxucHAudXBkYXRlQ29udGV4dCA9IGZ1bmN0aW9uIChwcmV2VHlwZSkge1xuICB2YXIgdXBkYXRlID0gdW5kZWZpbmVkLFxuICAgICAgdHlwZSA9IHRoaXMudHlwZTtcbiAgaWYgKHR5cGUua2V5d29yZCAmJiBwcmV2VHlwZSA9PSB0dC5kb3QpIHRoaXMuZXhwckFsbG93ZWQgPSBmYWxzZTtlbHNlIGlmICh1cGRhdGUgPSB0eXBlLnVwZGF0ZUNvbnRleHQpIHVwZGF0ZS5jYWxsKHRoaXMsIHByZXZUeXBlKTtlbHNlIHRoaXMuZXhwckFsbG93ZWQgPSB0eXBlLmJlZm9yZUV4cHI7XG59O1xuXG4vLyBUb2tlbi1zcGVjaWZpYyBjb250ZXh0IHVwZGF0ZSBjb2RlXG5cbnR0LnBhcmVuUi51cGRhdGVDb250ZXh0ID0gdHQuYnJhY2VSLnVwZGF0ZUNvbnRleHQgPSBmdW5jdGlvbiAoKSB7XG4gIGlmICh0aGlzLmNvbnRleHQubGVuZ3RoID09IDEpIHtcbiAgICB0aGlzLmV4cHJBbGxvd2VkID0gdHJ1ZTtcbiAgICByZXR1cm47XG4gIH1cbiAgdmFyIG91dCA9IHRoaXMuY29udGV4dC5wb3AoKTtcbiAgaWYgKG91dCA9PT0gdHlwZXMuYl9zdGF0ICYmIHRoaXMuY3VyQ29udGV4dCgpID09PSB0eXBlcy5mX2V4cHIpIHtcbiAgICB0aGlzLmNvbnRleHQucG9wKCk7XG4gICAgdGhpcy5leHByQWxsb3dlZCA9IGZhbHNlO1xuICB9IGVsc2UgaWYgKG91dCA9PT0gdHlwZXMuYl90bXBsKSB7XG4gICAgdGhpcy5leHByQWxsb3dlZCA9IHRydWU7XG4gIH0gZWxzZSB7XG4gICAgdGhpcy5leHByQWxsb3dlZCA9ICFvdXQuaXNFeHByO1xuICB9XG59O1xuXG50dC5icmFjZUwudXBkYXRlQ29udGV4dCA9IGZ1bmN0aW9uIChwcmV2VHlwZSkge1xuICB0aGlzLmNvbnRleHQucHVzaCh0aGlzLmJyYWNlSXNCbG9jayhwcmV2VHlwZSkgPyB0eXBlcy5iX3N0YXQgOiB0eXBlcy5iX2V4cHIpO1xuICB0aGlzLmV4cHJBbGxvd2VkID0gdHJ1ZTtcbn07XG5cbnR0LmRvbGxhckJyYWNlTC51cGRhdGVDb250ZXh0ID0gZnVuY3Rpb24gKCkge1xuICB0aGlzLmNvbnRleHQucHVzaCh0eXBlcy5iX3RtcGwpO1xuICB0aGlzLmV4cHJBbGxvd2VkID0gdHJ1ZTtcbn07XG5cbnR0LnBhcmVuTC51cGRhdGVDb250ZXh0ID0gZnVuY3Rpb24gKHByZXZUeXBlKSB7XG4gIHZhciBzdGF0ZW1lbnRQYXJlbnMgPSBwcmV2VHlwZSA9PT0gdHQuX2lmIHx8IHByZXZUeXBlID09PSB0dC5fZm9yIHx8IHByZXZUeXBlID09PSB0dC5fd2l0aCB8fCBwcmV2VHlwZSA9PT0gdHQuX3doaWxlO1xuICB0aGlzLmNvbnRleHQucHVzaChzdGF0ZW1lbnRQYXJlbnMgPyB0eXBlcy5wX3N0YXQgOiB0eXBlcy5wX2V4cHIpO1xuICB0aGlzLmV4cHJBbGxvd2VkID0gdHJ1ZTtcbn07XG5cbnR0LmluY0RlYy51cGRhdGVDb250ZXh0ID0gZnVuY3Rpb24gKCkge307XG5cbnR0Ll9mdW5jdGlvbi51cGRhdGVDb250ZXh0ID0gZnVuY3Rpb24gKCkge1xuICBpZiAodGhpcy5jdXJDb250ZXh0KCkgIT09IHR5cGVzLmJfc3RhdCkgdGhpcy5jb250ZXh0LnB1c2godHlwZXMuZl9leHByKTtcbiAgdGhpcy5leHByQWxsb3dlZCA9IGZhbHNlO1xufTtcblxudHQuYmFja1F1b3RlLnVwZGF0ZUNvbnRleHQgPSBmdW5jdGlvbiAoKSB7XG4gIGlmICh0aGlzLmN1ckNvbnRleHQoKSA9PT0gdHlwZXMucV90bXBsKSB0aGlzLmNvbnRleHQucG9wKCk7ZWxzZSB0aGlzLmNvbnRleHQucHVzaCh0eXBlcy5xX3RtcGwpO1xuICB0aGlzLmV4cHJBbGxvd2VkID0gZmFsc2U7XG59O1xuXG4vLyB0b2tFeHByQWxsb3dlZCBzdGF5cyB1bmNoYW5nZWRcblxufSx7XCIuL3N0YXRlXCI6MTMsXCIuL3Rva2VudHlwZVwiOjE3LFwiLi93aGl0ZXNwYWNlXCI6MTl9XSwxNjpbZnVuY3Rpb24oX2RlcmVxXyxtb2R1bGUsZXhwb3J0cyl7XG5cInVzZSBzdHJpY3RcIjtcblxudmFyIF9jbGFzc0NhbGxDaGVjayA9IGZ1bmN0aW9uIChpbnN0YW5jZSwgQ29uc3RydWN0b3IpIHsgaWYgKCEoaW5zdGFuY2UgaW5zdGFuY2VvZiBDb25zdHJ1Y3RvcikpIHsgdGhyb3cgbmV3IFR5cGVFcnJvcihcIkNhbm5vdCBjYWxsIGEgY2xhc3MgYXMgYSBmdW5jdGlvblwiKTsgfSB9O1xuXG5leHBvcnRzLl9fZXNNb2R1bGUgPSB0cnVlO1xuXG52YXIgX2lkZW50aWZpZXIgPSBfZGVyZXFfKFwiLi9pZGVudGlmaWVyXCIpO1xuXG52YXIgaXNJZGVudGlmaWVyU3RhcnQgPSBfaWRlbnRpZmllci5pc0lkZW50aWZpZXJTdGFydDtcbnZhciBpc0lkZW50aWZpZXJDaGFyID0gX2lkZW50aWZpZXIuaXNJZGVudGlmaWVyQ2hhcjtcblxudmFyIF90b2tlbnR5cGUgPSBfZGVyZXFfKFwiLi90b2tlbnR5cGVcIik7XG5cbnZhciB0dCA9IF90b2tlbnR5cGUudHlwZXM7XG52YXIga2V5d29yZFR5cGVzID0gX3Rva2VudHlwZS5rZXl3b3JkcztcblxudmFyIFBhcnNlciA9IF9kZXJlcV8oXCIuL3N0YXRlXCIpLlBhcnNlcjtcblxudmFyIFNvdXJjZUxvY2F0aW9uID0gX2RlcmVxXyhcIi4vbG9jYXRpb25cIikuU291cmNlTG9jYXRpb247XG5cbnZhciBfd2hpdGVzcGFjZSA9IF9kZXJlcV8oXCIuL3doaXRlc3BhY2VcIik7XG5cbnZhciBsaW5lQnJlYWsgPSBfd2hpdGVzcGFjZS5saW5lQnJlYWs7XG52YXIgbGluZUJyZWFrRyA9IF93aGl0ZXNwYWNlLmxpbmVCcmVha0c7XG52YXIgaXNOZXdMaW5lID0gX3doaXRlc3BhY2UuaXNOZXdMaW5lO1xudmFyIG5vbkFTQ0lJd2hpdGVzcGFjZSA9IF93aGl0ZXNwYWNlLm5vbkFTQ0lJd2hpdGVzcGFjZTtcblxuLy8gT2JqZWN0IHR5cGUgdXNlZCB0byByZXByZXNlbnQgdG9rZW5zLiBOb3RlIHRoYXQgbm9ybWFsbHksIHRva2Vuc1xuLy8gc2ltcGx5IGV4aXN0IGFzIHByb3BlcnRpZXMgb24gdGhlIHBhcnNlciBvYmplY3QuIFRoaXMgaXMgb25seVxuLy8gdXNlZCBmb3IgdGhlIG9uVG9rZW4gY2FsbGJhY2sgYW5kIHRoZSBleHRlcm5hbCB0b2tlbml6ZXIuXG5cbnZhciBUb2tlbiA9IGV4cG9ydHMuVG9rZW4gPSBmdW5jdGlvbiBUb2tlbihwKSB7XG4gIF9jbGFzc0NhbGxDaGVjayh0aGlzLCBUb2tlbik7XG5cbiAgdGhpcy50eXBlID0gcC50eXBlO1xuICB0aGlzLnZhbHVlID0gcC52YWx1ZTtcbiAgdGhpcy5zdGFydCA9IHAuc3RhcnQ7XG4gIHRoaXMuZW5kID0gcC5lbmQ7XG4gIGlmIChwLm9wdGlvbnMubG9jYXRpb25zKSB0aGlzLmxvYyA9IG5ldyBTb3VyY2VMb2NhdGlvbihwLCBwLnN0YXJ0TG9jLCBwLmVuZExvYyk7XG4gIGlmIChwLm9wdGlvbnMucmFuZ2VzKSB0aGlzLnJhbmdlID0gW3Auc3RhcnQsIHAuZW5kXTtcbn07XG5cbi8vICMjIFRva2VuaXplclxuXG52YXIgcHAgPSBQYXJzZXIucHJvdG90eXBlO1xuXG4vLyBBcmUgd2UgcnVubmluZyB1bmRlciBSaGlubz9cbnZhciBpc1JoaW5vID0gdHlwZW9mIFBhY2thZ2VzICE9PSBcInVuZGVmaW5lZFwiO1xuXG4vLyBNb3ZlIHRvIHRoZSBuZXh0IHRva2VuXG5cbnBwLm5leHQgPSBmdW5jdGlvbiAoKSB7XG4gIGlmICh0aGlzLm9wdGlvbnMub25Ub2tlbikgdGhpcy5vcHRpb25zLm9uVG9rZW4obmV3IFRva2VuKHRoaXMpKTtcblxuICB0aGlzLmxhc3RUb2tFbmQgPSB0aGlzLmVuZDtcbiAgdGhpcy5sYXN0VG9rU3RhcnQgPSB0aGlzLnN0YXJ0O1xuICB0aGlzLmxhc3RUb2tFbmRMb2MgPSB0aGlzLmVuZExvYztcbiAgdGhpcy5sYXN0VG9rU3RhcnRMb2MgPSB0aGlzLnN0YXJ0TG9jO1xuICB0aGlzLm5leHRUb2tlbigpO1xufTtcblxucHAuZ2V0VG9rZW4gPSBmdW5jdGlvbiAoKSB7XG4gIHRoaXMubmV4dCgpO1xuICByZXR1cm4gbmV3IFRva2VuKHRoaXMpO1xufTtcblxuLy8gSWYgd2UncmUgaW4gYW4gRVM2IGVudmlyb25tZW50LCBtYWtlIHBhcnNlcnMgaXRlcmFibGVcbmlmICh0eXBlb2YgU3ltYm9sICE9PSBcInVuZGVmaW5lZFwiKSBwcFtTeW1ib2wuaXRlcmF0b3JdID0gZnVuY3Rpb24gKCkge1xuICB2YXIgc2VsZiA9IHRoaXM7XG4gIHJldHVybiB7IG5leHQ6IGZ1bmN0aW9uIG5leHQoKSB7XG4gICAgICB2YXIgdG9rZW4gPSBzZWxmLmdldFRva2VuKCk7XG4gICAgICByZXR1cm4ge1xuICAgICAgICBkb25lOiB0b2tlbi50eXBlID09PSB0dC5lb2YsXG4gICAgICAgIHZhbHVlOiB0b2tlblxuICAgICAgfTtcbiAgICB9IH07XG59O1xuXG4vLyBUb2dnbGUgc3RyaWN0IG1vZGUuIFJlLXJlYWRzIHRoZSBuZXh0IG51bWJlciBvciBzdHJpbmcgdG8gcGxlYXNlXG4vLyBwZWRhbnRpYyB0ZXN0cyAoYFwidXNlIHN0cmljdFwiOyAwMTA7YCBzaG91bGQgZmFpbCkuXG5cbnBwLnNldFN0cmljdCA9IGZ1bmN0aW9uIChzdHJpY3QpIHtcbiAgdGhpcy5zdHJpY3QgPSBzdHJpY3Q7XG4gIGlmICh0aGlzLnR5cGUgIT09IHR0Lm51bSAmJiB0aGlzLnR5cGUgIT09IHR0LnN0cmluZykgcmV0dXJuO1xuICB0aGlzLnBvcyA9IHRoaXMuc3RhcnQ7XG4gIGlmICh0aGlzLm9wdGlvbnMubG9jYXRpb25zKSB7XG4gICAgd2hpbGUgKHRoaXMucG9zIDwgdGhpcy5saW5lU3RhcnQpIHtcbiAgICAgIHRoaXMubGluZVN0YXJ0ID0gdGhpcy5pbnB1dC5sYXN0SW5kZXhPZihcIlxcblwiLCB0aGlzLmxpbmVTdGFydCAtIDIpICsgMTtcbiAgICAgIC0tdGhpcy5jdXJMaW5lO1xuICAgIH1cbiAgfVxuICB0aGlzLm5leHRUb2tlbigpO1xufTtcblxucHAuY3VyQ29udGV4dCA9IGZ1bmN0aW9uICgpIHtcbiAgcmV0dXJuIHRoaXMuY29udGV4dFt0aGlzLmNvbnRleHQubGVuZ3RoIC0gMV07XG59O1xuXG4vLyBSZWFkIGEgc2luZ2xlIHRva2VuLCB1cGRhdGluZyB0aGUgcGFyc2VyIG9iamVjdCdzIHRva2VuLXJlbGF0ZWRcbi8vIHByb3BlcnRpZXMuXG5cbnBwLm5leHRUb2tlbiA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIGN1ckNvbnRleHQgPSB0aGlzLmN1ckNvbnRleHQoKTtcbiAgaWYgKCFjdXJDb250ZXh0IHx8ICFjdXJDb250ZXh0LnByZXNlcnZlU3BhY2UpIHRoaXMuc2tpcFNwYWNlKCk7XG5cbiAgdGhpcy5zdGFydCA9IHRoaXMucG9zO1xuICBpZiAodGhpcy5vcHRpb25zLmxvY2F0aW9ucykgdGhpcy5zdGFydExvYyA9IHRoaXMuY3VyUG9zaXRpb24oKTtcbiAgaWYgKHRoaXMucG9zID49IHRoaXMuaW5wdXQubGVuZ3RoKSByZXR1cm4gdGhpcy5maW5pc2hUb2tlbih0dC5lb2YpO1xuXG4gIGlmIChjdXJDb250ZXh0Lm92ZXJyaWRlKSByZXR1cm4gY3VyQ29udGV4dC5vdmVycmlkZSh0aGlzKTtlbHNlIHRoaXMucmVhZFRva2VuKHRoaXMuZnVsbENoYXJDb2RlQXRQb3MoKSk7XG59O1xuXG5wcC5yZWFkVG9rZW4gPSBmdW5jdGlvbiAoY29kZSkge1xuICAvLyBJZGVudGlmaWVyIG9yIGtleXdvcmQuICdcXHVYWFhYJyBzZXF1ZW5jZXMgYXJlIGFsbG93ZWQgaW5cbiAgLy8gaWRlbnRpZmllcnMsIHNvICdcXCcgYWxzbyBkaXNwYXRjaGVzIHRvIHRoYXQuXG4gIGlmIChpc0lkZW50aWZpZXJTdGFydChjb2RlLCB0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNikgfHwgY29kZSA9PT0gOTIgLyogJ1xcJyAqLykgcmV0dXJuIHRoaXMucmVhZFdvcmQoKTtcblxuICByZXR1cm4gdGhpcy5nZXRUb2tlbkZyb21Db2RlKGNvZGUpO1xufTtcblxucHAuZnVsbENoYXJDb2RlQXRQb3MgPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBjb2RlID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zKTtcbiAgaWYgKGNvZGUgPD0gNTUyOTUgfHwgY29kZSA+PSA1NzM0NCkgcmV0dXJuIGNvZGU7XG4gIHZhciBuZXh0ID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMSk7XG4gIHJldHVybiAoY29kZSA8PCAxMCkgKyBuZXh0IC0gNTY2MTM4ODg7XG59O1xuXG5wcC5za2lwQmxvY2tDb21tZW50ID0gZnVuY3Rpb24gKCkge1xuICB2YXIgc3RhcnRMb2MgPSB0aGlzLm9wdGlvbnMub25Db21tZW50ICYmIHRoaXMub3B0aW9ucy5sb2NhdGlvbnMgJiYgdGhpcy5jdXJQb3NpdGlvbigpO1xuICB2YXIgc3RhcnQgPSB0aGlzLnBvcyxcbiAgICAgIGVuZCA9IHRoaXMuaW5wdXQuaW5kZXhPZihcIiovXCIsIHRoaXMucG9zICs9IDIpO1xuICBpZiAoZW5kID09PSAtMSkgdGhpcy5yYWlzZSh0aGlzLnBvcyAtIDIsIFwiVW50ZXJtaW5hdGVkIGNvbW1lbnRcIik7XG4gIHRoaXMucG9zID0gZW5kICsgMjtcbiAgaWYgKHRoaXMub3B0aW9ucy5sb2NhdGlvbnMpIHtcbiAgICBsaW5lQnJlYWtHLmxhc3RJbmRleCA9IHN0YXJ0O1xuICAgIHZhciBtYXRjaCA9IHVuZGVmaW5lZDtcbiAgICB3aGlsZSAoKG1hdGNoID0gbGluZUJyZWFrRy5leGVjKHRoaXMuaW5wdXQpKSAmJiBtYXRjaC5pbmRleCA8IHRoaXMucG9zKSB7XG4gICAgICArK3RoaXMuY3VyTGluZTtcbiAgICAgIHRoaXMubGluZVN0YXJ0ID0gbWF0Y2guaW5kZXggKyBtYXRjaFswXS5sZW5ndGg7XG4gICAgfVxuICB9XG4gIGlmICh0aGlzLm9wdGlvbnMub25Db21tZW50KSB0aGlzLm9wdGlvbnMub25Db21tZW50KHRydWUsIHRoaXMuaW5wdXQuc2xpY2Uoc3RhcnQgKyAyLCBlbmQpLCBzdGFydCwgdGhpcy5wb3MsIHN0YXJ0TG9jLCB0aGlzLm9wdGlvbnMubG9jYXRpb25zICYmIHRoaXMuY3VyUG9zaXRpb24oKSk7XG59O1xuXG5wcC5za2lwTGluZUNvbW1lbnQgPSBmdW5jdGlvbiAoc3RhcnRTa2lwKSB7XG4gIHZhciBzdGFydCA9IHRoaXMucG9zO1xuICB2YXIgc3RhcnRMb2MgPSB0aGlzLm9wdGlvbnMub25Db21tZW50ICYmIHRoaXMub3B0aW9ucy5sb2NhdGlvbnMgJiYgdGhpcy5jdXJQb3NpdGlvbigpO1xuICB2YXIgY2ggPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKz0gc3RhcnRTa2lwKTtcbiAgd2hpbGUgKHRoaXMucG9zIDwgdGhpcy5pbnB1dC5sZW5ndGggJiYgY2ggIT09IDEwICYmIGNoICE9PSAxMyAmJiBjaCAhPT0gODIzMiAmJiBjaCAhPT0gODIzMykge1xuICAgICsrdGhpcy5wb3M7XG4gICAgY2ggPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MpO1xuICB9XG4gIGlmICh0aGlzLm9wdGlvbnMub25Db21tZW50KSB0aGlzLm9wdGlvbnMub25Db21tZW50KGZhbHNlLCB0aGlzLmlucHV0LnNsaWNlKHN0YXJ0ICsgc3RhcnRTa2lwLCB0aGlzLnBvcyksIHN0YXJ0LCB0aGlzLnBvcywgc3RhcnRMb2MsIHRoaXMub3B0aW9ucy5sb2NhdGlvbnMgJiYgdGhpcy5jdXJQb3NpdGlvbigpKTtcbn07XG5cbi8vIENhbGxlZCBhdCB0aGUgc3RhcnQgb2YgdGhlIHBhcnNlIGFuZCBhZnRlciBldmVyeSB0b2tlbi4gU2tpcHNcbi8vIHdoaXRlc3BhY2UgYW5kIGNvbW1lbnRzLCBhbmQuXG5cbnBwLnNraXBTcGFjZSA9IGZ1bmN0aW9uICgpIHtcbiAgd2hpbGUgKHRoaXMucG9zIDwgdGhpcy5pbnB1dC5sZW5ndGgpIHtcbiAgICB2YXIgY2ggPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MpO1xuICAgIGlmIChjaCA9PT0gMzIpIHtcbiAgICAgIC8vICcgJ1xuICAgICAgKyt0aGlzLnBvcztcbiAgICB9IGVsc2UgaWYgKGNoID09PSAxMykge1xuICAgICAgKyt0aGlzLnBvcztcbiAgICAgIHZhciBuZXh0ID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zKTtcbiAgICAgIGlmIChuZXh0ID09PSAxMCkge1xuICAgICAgICArK3RoaXMucG9zO1xuICAgICAgfVxuICAgICAgaWYgKHRoaXMub3B0aW9ucy5sb2NhdGlvbnMpIHtcbiAgICAgICAgKyt0aGlzLmN1ckxpbmU7XG4gICAgICAgIHRoaXMubGluZVN0YXJ0ID0gdGhpcy5wb3M7XG4gICAgICB9XG4gICAgfSBlbHNlIGlmIChjaCA9PT0gMTAgfHwgY2ggPT09IDgyMzIgfHwgY2ggPT09IDgyMzMpIHtcbiAgICAgICsrdGhpcy5wb3M7XG4gICAgICBpZiAodGhpcy5vcHRpb25zLmxvY2F0aW9ucykge1xuICAgICAgICArK3RoaXMuY3VyTGluZTtcbiAgICAgICAgdGhpcy5saW5lU3RhcnQgPSB0aGlzLnBvcztcbiAgICAgIH1cbiAgICB9IGVsc2UgaWYgKGNoID4gOCAmJiBjaCA8IDE0KSB7XG4gICAgICArK3RoaXMucG9zO1xuICAgIH0gZWxzZSBpZiAoY2ggPT09IDQ3KSB7XG4gICAgICAvLyAnLydcbiAgICAgIHZhciBuZXh0ID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMSk7XG4gICAgICBpZiAobmV4dCA9PT0gNDIpIHtcbiAgICAgICAgLy8gJyonXG4gICAgICAgIHRoaXMuc2tpcEJsb2NrQ29tbWVudCgpO1xuICAgICAgfSBlbHNlIGlmIChuZXh0ID09PSA0Nykge1xuICAgICAgICAvLyAnLydcbiAgICAgICAgdGhpcy5za2lwTGluZUNvbW1lbnQoMik7XG4gICAgICB9IGVsc2UgYnJlYWs7XG4gICAgfSBlbHNlIGlmIChjaCA9PT0gMTYwKSB7XG4gICAgICAvLyAnXFx4YTAnXG4gICAgICArK3RoaXMucG9zO1xuICAgIH0gZWxzZSBpZiAoY2ggPj0gNTc2MCAmJiBub25BU0NJSXdoaXRlc3BhY2UudGVzdChTdHJpbmcuZnJvbUNoYXJDb2RlKGNoKSkpIHtcbiAgICAgICsrdGhpcy5wb3M7XG4gICAgfSBlbHNlIHtcbiAgICAgIGJyZWFrO1xuICAgIH1cbiAgfVxufTtcblxuLy8gQ2FsbGVkIGF0IHRoZSBlbmQgb2YgZXZlcnkgdG9rZW4uIFNldHMgYGVuZGAsIGB2YWxgLCBhbmRcbi8vIG1haW50YWlucyBgY29udGV4dGAgYW5kIGBleHByQWxsb3dlZGAsIGFuZCBza2lwcyB0aGUgc3BhY2UgYWZ0ZXJcbi8vIHRoZSB0b2tlbiwgc28gdGhhdCB0aGUgbmV4dCBvbmUncyBgc3RhcnRgIHdpbGwgcG9pbnQgYXQgdGhlXG4vLyByaWdodCBwb3NpdGlvbi5cblxucHAuZmluaXNoVG9rZW4gPSBmdW5jdGlvbiAodHlwZSwgdmFsKSB7XG4gIHRoaXMuZW5kID0gdGhpcy5wb3M7XG4gIGlmICh0aGlzLm9wdGlvbnMubG9jYXRpb25zKSB0aGlzLmVuZExvYyA9IHRoaXMuY3VyUG9zaXRpb24oKTtcbiAgdmFyIHByZXZUeXBlID0gdGhpcy50eXBlO1xuICB0aGlzLnR5cGUgPSB0eXBlO1xuICB0aGlzLnZhbHVlID0gdmFsO1xuXG4gIHRoaXMudXBkYXRlQ29udGV4dChwcmV2VHlwZSk7XG59O1xuXG4vLyAjIyMgVG9rZW4gcmVhZGluZ1xuXG4vLyBUaGlzIGlzIHRoZSBmdW5jdGlvbiB0aGF0IGlzIGNhbGxlZCB0byBmZXRjaCB0aGUgbmV4dCB0b2tlbi4gSXRcbi8vIGlzIHNvbWV3aGF0IG9ic2N1cmUsIGJlY2F1c2UgaXQgd29ya3MgaW4gY2hhcmFjdGVyIGNvZGVzIHJhdGhlclxuLy8gdGhhbiBjaGFyYWN0ZXJzLCBhbmQgYmVjYXVzZSBvcGVyYXRvciBwYXJzaW5nIGhhcyBiZWVuIGlubGluZWRcbi8vIGludG8gaXQuXG4vL1xuLy8gQWxsIGluIHRoZSBuYW1lIG9mIHNwZWVkLlxuLy9cbnBwLnJlYWRUb2tlbl9kb3QgPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBuZXh0ID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMSk7XG4gIGlmIChuZXh0ID49IDQ4ICYmIG5leHQgPD0gNTcpIHJldHVybiB0aGlzLnJlYWROdW1iZXIodHJ1ZSk7XG4gIHZhciBuZXh0MiA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIDIpO1xuICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYgJiYgbmV4dCA9PT0gNDYgJiYgbmV4dDIgPT09IDQ2KSB7XG4gICAgLy8gNDYgPSBkb3QgJy4nXG4gICAgdGhpcy5wb3MgKz0gMztcbiAgICByZXR1cm4gdGhpcy5maW5pc2hUb2tlbih0dC5lbGxpcHNpcyk7XG4gIH0gZWxzZSB7XG4gICAgKyt0aGlzLnBvcztcbiAgICByZXR1cm4gdGhpcy5maW5pc2hUb2tlbih0dC5kb3QpO1xuICB9XG59O1xuXG5wcC5yZWFkVG9rZW5fc2xhc2ggPSBmdW5jdGlvbiAoKSB7XG4gIC8vICcvJ1xuICB2YXIgbmV4dCA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIDEpO1xuICBpZiAodGhpcy5leHByQWxsb3dlZCkge1xuICAgICsrdGhpcy5wb3M7cmV0dXJuIHRoaXMucmVhZFJlZ2V4cCgpO1xuICB9XG4gIGlmIChuZXh0ID09PSA2MSkgcmV0dXJuIHRoaXMuZmluaXNoT3AodHQuYXNzaWduLCAyKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoT3AodHQuc2xhc2gsIDEpO1xufTtcblxucHAucmVhZFRva2VuX211bHRfbW9kdWxvID0gZnVuY3Rpb24gKGNvZGUpIHtcbiAgLy8gJyUqJ1xuICB2YXIgbmV4dCA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIDEpO1xuICBpZiAobmV4dCA9PT0gNjEpIHJldHVybiB0aGlzLmZpbmlzaE9wKHR0LmFzc2lnbiwgMik7XG4gIHJldHVybiB0aGlzLmZpbmlzaE9wKGNvZGUgPT09IDQyID8gdHQuc3RhciA6IHR0Lm1vZHVsbywgMSk7XG59O1xuXG5wcC5yZWFkVG9rZW5fcGlwZV9hbXAgPSBmdW5jdGlvbiAoY29kZSkge1xuICAvLyAnfCYnXG4gIHZhciBuZXh0ID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMSk7XG4gIGlmIChuZXh0ID09PSBjb2RlKSByZXR1cm4gdGhpcy5maW5pc2hPcChjb2RlID09PSAxMjQgPyB0dC5sb2dpY2FsT1IgOiB0dC5sb2dpY2FsQU5ELCAyKTtcbiAgaWYgKG5leHQgPT09IDYxKSByZXR1cm4gdGhpcy5maW5pc2hPcCh0dC5hc3NpZ24sIDIpO1xuICByZXR1cm4gdGhpcy5maW5pc2hPcChjb2RlID09PSAxMjQgPyB0dC5iaXR3aXNlT1IgOiB0dC5iaXR3aXNlQU5ELCAxKTtcbn07XG5cbnBwLnJlYWRUb2tlbl9jYXJldCA9IGZ1bmN0aW9uICgpIHtcbiAgLy8gJ14nXG4gIHZhciBuZXh0ID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMSk7XG4gIGlmIChuZXh0ID09PSA2MSkgcmV0dXJuIHRoaXMuZmluaXNoT3AodHQuYXNzaWduLCAyKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoT3AodHQuYml0d2lzZVhPUiwgMSk7XG59O1xuXG5wcC5yZWFkVG9rZW5fcGx1c19taW4gPSBmdW5jdGlvbiAoY29kZSkge1xuICAvLyAnKy0nXG4gIHZhciBuZXh0ID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMSk7XG4gIGlmIChuZXh0ID09PSBjb2RlKSB7XG4gICAgaWYgKG5leHQgPT0gNDUgJiYgdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMikgPT0gNjIgJiYgbGluZUJyZWFrLnRlc3QodGhpcy5pbnB1dC5zbGljZSh0aGlzLmxhc3RUb2tFbmQsIHRoaXMucG9zKSkpIHtcbiAgICAgIC8vIEEgYC0tPmAgbGluZSBjb21tZW50XG4gICAgICB0aGlzLnNraXBMaW5lQ29tbWVudCgzKTtcbiAgICAgIHRoaXMuc2tpcFNwYWNlKCk7XG4gICAgICByZXR1cm4gdGhpcy5uZXh0VG9rZW4oKTtcbiAgICB9XG4gICAgcmV0dXJuIHRoaXMuZmluaXNoT3AodHQuaW5jRGVjLCAyKTtcbiAgfVxuICBpZiAobmV4dCA9PT0gNjEpIHJldHVybiB0aGlzLmZpbmlzaE9wKHR0LmFzc2lnbiwgMik7XG4gIHJldHVybiB0aGlzLmZpbmlzaE9wKHR0LnBsdXNNaW4sIDEpO1xufTtcblxucHAucmVhZFRva2VuX2x0X2d0ID0gZnVuY3Rpb24gKGNvZGUpIHtcbiAgLy8gJzw+J1xuICB2YXIgbmV4dCA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIDEpO1xuICB2YXIgc2l6ZSA9IDE7XG4gIGlmIChuZXh0ID09PSBjb2RlKSB7XG4gICAgc2l6ZSA9IGNvZGUgPT09IDYyICYmIHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIDIpID09PSA2MiA/IDMgOiAyO1xuICAgIGlmICh0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyBzaXplKSA9PT0gNjEpIHJldHVybiB0aGlzLmZpbmlzaE9wKHR0LmFzc2lnbiwgc2l6ZSArIDEpO1xuICAgIHJldHVybiB0aGlzLmZpbmlzaE9wKHR0LmJpdFNoaWZ0LCBzaXplKTtcbiAgfVxuICBpZiAobmV4dCA9PSAzMyAmJiBjb2RlID09IDYwICYmIHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIDIpID09IDQ1ICYmIHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIDMpID09IDQ1KSB7XG4gICAgaWYgKHRoaXMuaW5Nb2R1bGUpIHRoaXMudW5leHBlY3RlZCgpO1xuICAgIC8vIGA8IS0tYCwgYW4gWE1MLXN0eWxlIGNvbW1lbnQgdGhhdCBzaG91bGQgYmUgaW50ZXJwcmV0ZWQgYXMgYSBsaW5lIGNvbW1lbnRcbiAgICB0aGlzLnNraXBMaW5lQ29tbWVudCg0KTtcbiAgICB0aGlzLnNraXBTcGFjZSgpO1xuICAgIHJldHVybiB0aGlzLm5leHRUb2tlbigpO1xuICB9XG4gIGlmIChuZXh0ID09PSA2MSkgc2l6ZSA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIDIpID09PSA2MSA/IDMgOiAyO1xuICByZXR1cm4gdGhpcy5maW5pc2hPcCh0dC5yZWxhdGlvbmFsLCBzaXplKTtcbn07XG5cbnBwLnJlYWRUb2tlbl9lcV9leGNsID0gZnVuY3Rpb24gKGNvZGUpIHtcbiAgLy8gJz0hJ1xuICB2YXIgbmV4dCA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIDEpO1xuICBpZiAobmV4dCA9PT0gNjEpIHJldHVybiB0aGlzLmZpbmlzaE9wKHR0LmVxdWFsaXR5LCB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAyKSA9PT0gNjEgPyAzIDogMik7XG4gIGlmIChjb2RlID09PSA2MSAmJiBuZXh0ID09PSA2MiAmJiB0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNikge1xuICAgIC8vICc9PidcbiAgICB0aGlzLnBvcyArPSAyO1xuICAgIHJldHVybiB0aGlzLmZpbmlzaFRva2VuKHR0LmFycm93KTtcbiAgfVxuICByZXR1cm4gdGhpcy5maW5pc2hPcChjb2RlID09PSA2MSA/IHR0LmVxIDogdHQucHJlZml4LCAxKTtcbn07XG5cbnBwLmdldFRva2VuRnJvbUNvZGUgPSBmdW5jdGlvbiAoY29kZSkge1xuICBzd2l0Y2ggKGNvZGUpIHtcbiAgICAvLyBUaGUgaW50ZXJwcmV0YXRpb24gb2YgYSBkb3QgZGVwZW5kcyBvbiB3aGV0aGVyIGl0IGlzIGZvbGxvd2VkXG4gICAgLy8gYnkgYSBkaWdpdCBvciBhbm90aGVyIHR3byBkb3RzLlxuICAgIGNhc2UgNDY6XG4gICAgICAvLyAnLidcbiAgICAgIHJldHVybiB0aGlzLnJlYWRUb2tlbl9kb3QoKTtcblxuICAgIC8vIFB1bmN0dWF0aW9uIHRva2Vucy5cbiAgICBjYXNlIDQwOlxuICAgICAgKyt0aGlzLnBvcztyZXR1cm4gdGhpcy5maW5pc2hUb2tlbih0dC5wYXJlbkwpO1xuICAgIGNhc2UgNDE6XG4gICAgICArK3RoaXMucG9zO3JldHVybiB0aGlzLmZpbmlzaFRva2VuKHR0LnBhcmVuUik7XG4gICAgY2FzZSA1OTpcbiAgICAgICsrdGhpcy5wb3M7cmV0dXJuIHRoaXMuZmluaXNoVG9rZW4odHQuc2VtaSk7XG4gICAgY2FzZSA0NDpcbiAgICAgICsrdGhpcy5wb3M7cmV0dXJuIHRoaXMuZmluaXNoVG9rZW4odHQuY29tbWEpO1xuICAgIGNhc2UgOTE6XG4gICAgICArK3RoaXMucG9zO3JldHVybiB0aGlzLmZpbmlzaFRva2VuKHR0LmJyYWNrZXRMKTtcbiAgICBjYXNlIDkzOlxuICAgICAgKyt0aGlzLnBvcztyZXR1cm4gdGhpcy5maW5pc2hUb2tlbih0dC5icmFja2V0Uik7XG4gICAgY2FzZSAxMjM6XG4gICAgICArK3RoaXMucG9zO3JldHVybiB0aGlzLmZpbmlzaFRva2VuKHR0LmJyYWNlTCk7XG4gICAgY2FzZSAxMjU6XG4gICAgICArK3RoaXMucG9zO3JldHVybiB0aGlzLmZpbmlzaFRva2VuKHR0LmJyYWNlUik7XG4gICAgY2FzZSA1ODpcbiAgICAgICsrdGhpcy5wb3M7cmV0dXJuIHRoaXMuZmluaXNoVG9rZW4odHQuY29sb24pO1xuICAgIGNhc2UgNjM6XG4gICAgICArK3RoaXMucG9zO3JldHVybiB0aGlzLmZpbmlzaFRva2VuKHR0LnF1ZXN0aW9uKTtcblxuICAgIGNhc2UgOTY6XG4gICAgICAvLyAnYCdcbiAgICAgIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPCA2KSBicmVhaztcbiAgICAgICsrdGhpcy5wb3M7XG4gICAgICByZXR1cm4gdGhpcy5maW5pc2hUb2tlbih0dC5iYWNrUXVvdGUpO1xuXG4gICAgY2FzZSA0ODpcbiAgICAgIC8vICcwJ1xuICAgICAgdmFyIG5leHQgPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAxKTtcbiAgICAgIGlmIChuZXh0ID09PSAxMjAgfHwgbmV4dCA9PT0gODgpIHJldHVybiB0aGlzLnJlYWRSYWRpeE51bWJlcigxNik7IC8vICcweCcsICcwWCcgLSBoZXggbnVtYmVyXG4gICAgICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYpIHtcbiAgICAgICAgaWYgKG5leHQgPT09IDExMSB8fCBuZXh0ID09PSA3OSkgcmV0dXJuIHRoaXMucmVhZFJhZGl4TnVtYmVyKDgpOyAvLyAnMG8nLCAnME8nIC0gb2N0YWwgbnVtYmVyXG4gICAgICAgIGlmIChuZXh0ID09PSA5OCB8fCBuZXh0ID09PSA2NikgcmV0dXJuIHRoaXMucmVhZFJhZGl4TnVtYmVyKDIpOyAvLyAnMGInLCAnMEInIC0gYmluYXJ5IG51bWJlclxuICAgICAgfVxuICAgIC8vIEFueXRoaW5nIGVsc2UgYmVnaW5uaW5nIHdpdGggYSBkaWdpdCBpcyBhbiBpbnRlZ2VyLCBvY3RhbFxuICAgIC8vIG51bWJlciwgb3IgZmxvYXQuXG4gICAgY2FzZSA0OTpjYXNlIDUwOmNhc2UgNTE6Y2FzZSA1MjpjYXNlIDUzOmNhc2UgNTQ6Y2FzZSA1NTpjYXNlIDU2OmNhc2UgNTc6XG4gICAgICAvLyAxLTlcbiAgICAgIHJldHVybiB0aGlzLnJlYWROdW1iZXIoZmFsc2UpO1xuXG4gICAgLy8gUXVvdGVzIHByb2R1Y2Ugc3RyaW5ncy5cbiAgICBjYXNlIDM0OmNhc2UgMzk6XG4gICAgICAvLyAnXCInLCBcIidcIlxuICAgICAgcmV0dXJuIHRoaXMucmVhZFN0cmluZyhjb2RlKTtcblxuICAgIC8vIE9wZXJhdG9ycyBhcmUgcGFyc2VkIGlubGluZSBpbiB0aW55IHN0YXRlIG1hY2hpbmVzLiAnPScgKDYxKSBpc1xuICAgIC8vIG9mdGVuIHJlZmVycmVkIHRvLiBgZmluaXNoT3BgIHNpbXBseSBza2lwcyB0aGUgYW1vdW50IG9mXG4gICAgLy8gY2hhcmFjdGVycyBpdCBpcyBnaXZlbiBhcyBzZWNvbmQgYXJndW1lbnQsIGFuZCByZXR1cm5zIGEgdG9rZW5cbiAgICAvLyBvZiB0aGUgdHlwZSBnaXZlbiBieSBpdHMgZmlyc3QgYXJndW1lbnQuXG5cbiAgICBjYXNlIDQ3OlxuICAgICAgLy8gJy8nXG4gICAgICByZXR1cm4gdGhpcy5yZWFkVG9rZW5fc2xhc2goKTtcblxuICAgIGNhc2UgMzc6Y2FzZSA0MjpcbiAgICAgIC8vICclKidcbiAgICAgIHJldHVybiB0aGlzLnJlYWRUb2tlbl9tdWx0X21vZHVsbyhjb2RlKTtcblxuICAgIGNhc2UgMTI0OmNhc2UgMzg6XG4gICAgICAvLyAnfCYnXG4gICAgICByZXR1cm4gdGhpcy5yZWFkVG9rZW5fcGlwZV9hbXAoY29kZSk7XG5cbiAgICBjYXNlIDk0OlxuICAgICAgLy8gJ14nXG4gICAgICByZXR1cm4gdGhpcy5yZWFkVG9rZW5fY2FyZXQoKTtcblxuICAgIGNhc2UgNDM6Y2FzZSA0NTpcbiAgICAgIC8vICcrLSdcbiAgICAgIHJldHVybiB0aGlzLnJlYWRUb2tlbl9wbHVzX21pbihjb2RlKTtcblxuICAgIGNhc2UgNjA6Y2FzZSA2MjpcbiAgICAgIC8vICc8PidcbiAgICAgIHJldHVybiB0aGlzLnJlYWRUb2tlbl9sdF9ndChjb2RlKTtcblxuICAgIGNhc2UgNjE6Y2FzZSAzMzpcbiAgICAgIC8vICc9ISdcbiAgICAgIHJldHVybiB0aGlzLnJlYWRUb2tlbl9lcV9leGNsKGNvZGUpO1xuXG4gICAgY2FzZSAxMjY6XG4gICAgICAvLyAnfidcbiAgICAgIHJldHVybiB0aGlzLmZpbmlzaE9wKHR0LnByZWZpeCwgMSk7XG4gIH1cblxuICB0aGlzLnJhaXNlKHRoaXMucG9zLCBcIlVuZXhwZWN0ZWQgY2hhcmFjdGVyICdcIiArIGNvZGVQb2ludFRvU3RyaW5nKGNvZGUpICsgXCInXCIpO1xufTtcblxucHAuZmluaXNoT3AgPSBmdW5jdGlvbiAodHlwZSwgc2l6ZSkge1xuICB2YXIgc3RyID0gdGhpcy5pbnB1dC5zbGljZSh0aGlzLnBvcywgdGhpcy5wb3MgKyBzaXplKTtcbiAgdGhpcy5wb3MgKz0gc2l6ZTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoVG9rZW4odHlwZSwgc3RyKTtcbn07XG5cbnZhciByZWdleHBVbmljb2RlU3VwcG9ydCA9IGZhbHNlO1xudHJ5IHtcbiAgbmV3IFJlZ0V4cChcIu+/v1wiLCBcInVcIik7cmVnZXhwVW5pY29kZVN1cHBvcnQgPSB0cnVlO1xufSBjYXRjaCAoZSkge31cblxuLy8gUGFyc2UgYSByZWd1bGFyIGV4cHJlc3Npb24uIFNvbWUgY29udGV4dC1hd2FyZW5lc3MgaXMgbmVjZXNzYXJ5LFxuLy8gc2luY2UgYSAnLycgaW5zaWRlIGEgJ1tdJyBzZXQgZG9lcyBub3QgZW5kIHRoZSBleHByZXNzaW9uLlxuXG5wcC5yZWFkUmVnZXhwID0gZnVuY3Rpb24gKCkge1xuICB2YXIgZXNjYXBlZCA9IHVuZGVmaW5lZCxcbiAgICAgIGluQ2xhc3MgPSB1bmRlZmluZWQsXG4gICAgICBzdGFydCA9IHRoaXMucG9zO1xuICBmb3IgKDs7KSB7XG4gICAgaWYgKHRoaXMucG9zID49IHRoaXMuaW5wdXQubGVuZ3RoKSB0aGlzLnJhaXNlKHN0YXJ0LCBcIlVudGVybWluYXRlZCByZWd1bGFyIGV4cHJlc3Npb25cIik7XG4gICAgdmFyIGNoID0gdGhpcy5pbnB1dC5jaGFyQXQodGhpcy5wb3MpO1xuICAgIGlmIChsaW5lQnJlYWsudGVzdChjaCkpIHRoaXMucmFpc2Uoc3RhcnQsIFwiVW50ZXJtaW5hdGVkIHJlZ3VsYXIgZXhwcmVzc2lvblwiKTtcbiAgICBpZiAoIWVzY2FwZWQpIHtcbiAgICAgIGlmIChjaCA9PT0gXCJbXCIpIGluQ2xhc3MgPSB0cnVlO2Vsc2UgaWYgKGNoID09PSBcIl1cIiAmJiBpbkNsYXNzKSBpbkNsYXNzID0gZmFsc2U7ZWxzZSBpZiAoY2ggPT09IFwiL1wiICYmICFpbkNsYXNzKSBicmVhaztcbiAgICAgIGVzY2FwZWQgPSBjaCA9PT0gXCJcXFxcXCI7XG4gICAgfSBlbHNlIGVzY2FwZWQgPSBmYWxzZTtcbiAgICArK3RoaXMucG9zO1xuICB9XG4gIHZhciBjb250ZW50ID0gdGhpcy5pbnB1dC5zbGljZShzdGFydCwgdGhpcy5wb3MpO1xuICArK3RoaXMucG9zO1xuICAvLyBOZWVkIHRvIHVzZSBgcmVhZFdvcmQxYCBiZWNhdXNlICdcXHVYWFhYJyBzZXF1ZW5jZXMgYXJlIGFsbG93ZWRcbiAgLy8gaGVyZSAoZG9uJ3QgYXNrKS5cbiAgdmFyIG1vZHMgPSB0aGlzLnJlYWRXb3JkMSgpO1xuICB2YXIgdG1wID0gY29udGVudDtcbiAgaWYgKG1vZHMpIHtcbiAgICB2YXIgdmFsaWRGbGFncyA9IC9eW2dtc2l5XSokLztcbiAgICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYpIHZhbGlkRmxhZ3MgPSAvXltnbXNpeXVdKiQvO1xuICAgIGlmICghdmFsaWRGbGFncy50ZXN0KG1vZHMpKSB0aGlzLnJhaXNlKHN0YXJ0LCBcIkludmFsaWQgcmVndWxhciBleHByZXNzaW9uIGZsYWdcIik7XG4gICAgaWYgKG1vZHMuaW5kZXhPZihcInVcIikgPj0gMCAmJiAhcmVnZXhwVW5pY29kZVN1cHBvcnQpIHtcbiAgICAgIC8vIFJlcGxhY2UgZWFjaCBhc3RyYWwgc3ltYm9sIGFuZCBldmVyeSBVbmljb2RlIGVzY2FwZSBzZXF1ZW5jZSB0aGF0XG4gICAgICAvLyBwb3NzaWJseSByZXByZXNlbnRzIGFuIGFzdHJhbCBzeW1ib2wgb3IgYSBwYWlyZWQgc3Vycm9nYXRlIHdpdGggYVxuICAgICAgLy8gc2luZ2xlIEFTQ0lJIHN5bWJvbCB0byBhdm9pZCB0aHJvd2luZyBvbiByZWd1bGFyIGV4cHJlc3Npb25zIHRoYXRcbiAgICAgIC8vIGFyZSBvbmx5IHZhbGlkIGluIGNvbWJpbmF0aW9uIHdpdGggdGhlIGAvdWAgZmxhZy5cbiAgICAgIC8vIE5vdGU6IHJlcGxhY2luZyB3aXRoIHRoZSBBU0NJSSBzeW1ib2wgYHhgIG1pZ2h0IGNhdXNlIGZhbHNlXG4gICAgICAvLyBuZWdhdGl2ZXMgaW4gdW5saWtlbHkgc2NlbmFyaW9zLiBGb3IgZXhhbXBsZSwgYFtcXHV7NjF9LWJdYCBpcyBhXG4gICAgICAvLyBwZXJmZWN0bHkgdmFsaWQgcGF0dGVybiB0aGF0IGlzIGVxdWl2YWxlbnQgdG8gYFthLWJdYCwgYnV0IGl0IHdvdWxkXG4gICAgICAvLyBiZSByZXBsYWNlZCBieSBgW3gtYl1gIHdoaWNoIHRocm93cyBhbiBlcnJvci5cbiAgICAgIHRtcCA9IHRtcC5yZXBsYWNlKC9cXFxcdShbYS1mQS1GMC05XXs0fSl8XFxcXHVcXHsoWzAtOWEtZkEtRl0rKVxcfXxbXFx1RDgwMC1cXHVEQkZGXVtcXHVEQzAwLVxcdURGRkZdL2csIFwieFwiKTtcbiAgICB9XG4gIH1cbiAgLy8gRGV0ZWN0IGludmFsaWQgcmVndWxhciBleHByZXNzaW9ucy5cbiAgdmFyIHZhbHVlID0gbnVsbDtcbiAgLy8gUmhpbm8ncyByZWd1bGFyIGV4cHJlc3Npb24gcGFyc2VyIGlzIGZsYWt5IGFuZCB0aHJvd3MgdW5jYXRjaGFibGUgZXhjZXB0aW9ucyxcbiAgLy8gc28gZG9uJ3QgZG8gZGV0ZWN0aW9uIGlmIHdlIGFyZSBydW5uaW5nIHVuZGVyIFJoaW5vXG4gIGlmICghaXNSaGlubykge1xuICAgIHRyeSB7XG4gICAgICBuZXcgUmVnRXhwKHRtcCk7XG4gICAgfSBjYXRjaCAoZSkge1xuICAgICAgaWYgKGUgaW5zdGFuY2VvZiBTeW50YXhFcnJvcikgdGhpcy5yYWlzZShzdGFydCwgXCJFcnJvciBwYXJzaW5nIHJlZ3VsYXIgZXhwcmVzc2lvbjogXCIgKyBlLm1lc3NhZ2UpO1xuICAgICAgdGhpcy5yYWlzZShlKTtcbiAgICB9XG4gICAgLy8gR2V0IGEgcmVndWxhciBleHByZXNzaW9uIG9iamVjdCBmb3IgdGhpcyBwYXR0ZXJuLWZsYWcgcGFpciwgb3IgYG51bGxgIGluXG4gICAgLy8gY2FzZSB0aGUgY3VycmVudCBlbnZpcm9ubWVudCBkb2Vzbid0IHN1cHBvcnQgdGhlIGZsYWdzIGl0IHVzZXMuXG4gICAgdHJ5IHtcbiAgICAgIHZhbHVlID0gbmV3IFJlZ0V4cChjb250ZW50LCBtb2RzKTtcbiAgICB9IGNhdGNoIChlcnIpIHt9XG4gIH1cbiAgcmV0dXJuIHRoaXMuZmluaXNoVG9rZW4odHQucmVnZXhwLCB7IHBhdHRlcm46IGNvbnRlbnQsIGZsYWdzOiBtb2RzLCB2YWx1ZTogdmFsdWUgfSk7XG59O1xuXG4vLyBSZWFkIGFuIGludGVnZXIgaW4gdGhlIGdpdmVuIHJhZGl4LiBSZXR1cm4gbnVsbCBpZiB6ZXJvIGRpZ2l0c1xuLy8gd2VyZSByZWFkLCB0aGUgaW50ZWdlciB2YWx1ZSBvdGhlcndpc2UuIFdoZW4gYGxlbmAgaXMgZ2l2ZW4sIHRoaXNcbi8vIHdpbGwgcmV0dXJuIGBudWxsYCB1bmxlc3MgdGhlIGludGVnZXIgaGFzIGV4YWN0bHkgYGxlbmAgZGlnaXRzLlxuXG5wcC5yZWFkSW50ID0gZnVuY3Rpb24gKHJhZGl4LCBsZW4pIHtcbiAgdmFyIHN0YXJ0ID0gdGhpcy5wb3MsXG4gICAgICB0b3RhbCA9IDA7XG4gIGZvciAodmFyIGkgPSAwLCBlID0gbGVuID09IG51bGwgPyBJbmZpbml0eSA6IGxlbjsgaSA8IGU7ICsraSkge1xuICAgIHZhciBjb2RlID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zKSxcbiAgICAgICAgdmFsID0gdW5kZWZpbmVkO1xuICAgIGlmIChjb2RlID49IDk3KSB2YWwgPSBjb2RlIC0gOTcgKyAxMDsgLy8gYVxuICAgIGVsc2UgaWYgKGNvZGUgPj0gNjUpIHZhbCA9IGNvZGUgLSA2NSArIDEwOyAvLyBBXG4gICAgZWxzZSBpZiAoY29kZSA+PSA0OCAmJiBjb2RlIDw9IDU3KSB2YWwgPSBjb2RlIC0gNDg7IC8vIDAtOVxuICAgIGVsc2UgdmFsID0gSW5maW5pdHk7XG4gICAgaWYgKHZhbCA+PSByYWRpeCkgYnJlYWs7XG4gICAgKyt0aGlzLnBvcztcbiAgICB0b3RhbCA9IHRvdGFsICogcmFkaXggKyB2YWw7XG4gIH1cbiAgaWYgKHRoaXMucG9zID09PSBzdGFydCB8fCBsZW4gIT0gbnVsbCAmJiB0aGlzLnBvcyAtIHN0YXJ0ICE9PSBsZW4pIHJldHVybiBudWxsO1xuXG4gIHJldHVybiB0b3RhbDtcbn07XG5cbnBwLnJlYWRSYWRpeE51bWJlciA9IGZ1bmN0aW9uIChyYWRpeCkge1xuICB0aGlzLnBvcyArPSAyOyAvLyAweFxuICB2YXIgdmFsID0gdGhpcy5yZWFkSW50KHJhZGl4KTtcbiAgaWYgKHZhbCA9PSBudWxsKSB0aGlzLnJhaXNlKHRoaXMuc3RhcnQgKyAyLCBcIkV4cGVjdGVkIG51bWJlciBpbiByYWRpeCBcIiArIHJhZGl4KTtcbiAgaWYgKGlzSWRlbnRpZmllclN0YXJ0KHRoaXMuZnVsbENoYXJDb2RlQXRQb3MoKSkpIHRoaXMucmFpc2UodGhpcy5wb3MsIFwiSWRlbnRpZmllciBkaXJlY3RseSBhZnRlciBudW1iZXJcIik7XG4gIHJldHVybiB0aGlzLmZpbmlzaFRva2VuKHR0Lm51bSwgdmFsKTtcbn07XG5cbi8vIFJlYWQgYW4gaW50ZWdlciwgb2N0YWwgaW50ZWdlciwgb3IgZmxvYXRpbmctcG9pbnQgbnVtYmVyLlxuXG5wcC5yZWFkTnVtYmVyID0gZnVuY3Rpb24gKHN0YXJ0c1dpdGhEb3QpIHtcbiAgdmFyIHN0YXJ0ID0gdGhpcy5wb3MsXG4gICAgICBpc0Zsb2F0ID0gZmFsc2UsXG4gICAgICBvY3RhbCA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcykgPT09IDQ4O1xuICBpZiAoIXN0YXJ0c1dpdGhEb3QgJiYgdGhpcy5yZWFkSW50KDEwKSA9PT0gbnVsbCkgdGhpcy5yYWlzZShzdGFydCwgXCJJbnZhbGlkIG51bWJlclwiKTtcbiAgaWYgKHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcykgPT09IDQ2KSB7XG4gICAgKyt0aGlzLnBvcztcbiAgICB0aGlzLnJlYWRJbnQoMTApO1xuICAgIGlzRmxvYXQgPSB0cnVlO1xuICB9XG4gIHZhciBuZXh0ID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zKTtcbiAgaWYgKG5leHQgPT09IDY5IHx8IG5leHQgPT09IDEwMSkge1xuICAgIC8vICdlRSdcbiAgICBuZXh0ID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KCsrdGhpcy5wb3MpO1xuICAgIGlmIChuZXh0ID09PSA0MyB8fCBuZXh0ID09PSA0NSkgKyt0aGlzLnBvczsgLy8gJystJ1xuICAgIGlmICh0aGlzLnJlYWRJbnQoMTApID09PSBudWxsKSB0aGlzLnJhaXNlKHN0YXJ0LCBcIkludmFsaWQgbnVtYmVyXCIpO1xuICAgIGlzRmxvYXQgPSB0cnVlO1xuICB9XG4gIGlmIChpc0lkZW50aWZpZXJTdGFydCh0aGlzLmZ1bGxDaGFyQ29kZUF0UG9zKCkpKSB0aGlzLnJhaXNlKHRoaXMucG9zLCBcIklkZW50aWZpZXIgZGlyZWN0bHkgYWZ0ZXIgbnVtYmVyXCIpO1xuXG4gIHZhciBzdHIgPSB0aGlzLmlucHV0LnNsaWNlKHN0YXJ0LCB0aGlzLnBvcyksXG4gICAgICB2YWwgPSB1bmRlZmluZWQ7XG4gIGlmIChpc0Zsb2F0KSB2YWwgPSBwYXJzZUZsb2F0KHN0cik7ZWxzZSBpZiAoIW9jdGFsIHx8IHN0ci5sZW5ndGggPT09IDEpIHZhbCA9IHBhcnNlSW50KHN0ciwgMTApO2Vsc2UgaWYgKC9bODldLy50ZXN0KHN0cikgfHwgdGhpcy5zdHJpY3QpIHRoaXMucmFpc2Uoc3RhcnQsIFwiSW52YWxpZCBudW1iZXJcIik7ZWxzZSB2YWwgPSBwYXJzZUludChzdHIsIDgpO1xuICByZXR1cm4gdGhpcy5maW5pc2hUb2tlbih0dC5udW0sIHZhbCk7XG59O1xuXG4vLyBSZWFkIGEgc3RyaW5nIHZhbHVlLCBpbnRlcnByZXRpbmcgYmFja3NsYXNoLWVzY2FwZXMuXG5cbnBwLnJlYWRDb2RlUG9pbnQgPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBjaCA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyksXG4gICAgICBjb2RlID0gdW5kZWZpbmVkO1xuXG4gIGlmIChjaCA9PT0gMTIzKSB7XG4gICAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA8IDYpIHRoaXMudW5leHBlY3RlZCgpO1xuICAgICsrdGhpcy5wb3M7XG4gICAgY29kZSA9IHRoaXMucmVhZEhleENoYXIodGhpcy5pbnB1dC5pbmRleE9mKFwifVwiLCB0aGlzLnBvcykgLSB0aGlzLnBvcyk7XG4gICAgKyt0aGlzLnBvcztcbiAgICBpZiAoY29kZSA+IDExMTQxMTEpIHRoaXMudW5leHBlY3RlZCgpO1xuICB9IGVsc2Uge1xuICAgIGNvZGUgPSB0aGlzLnJlYWRIZXhDaGFyKDQpO1xuICB9XG4gIHJldHVybiBjb2RlO1xufTtcblxuZnVuY3Rpb24gY29kZVBvaW50VG9TdHJpbmcoY29kZSkge1xuICAvLyBVVEYtMTYgRGVjb2RpbmdcbiAgaWYgKGNvZGUgPD0gNjU1MzUpIHtcbiAgICByZXR1cm4gU3RyaW5nLmZyb21DaGFyQ29kZShjb2RlKTtcbiAgfXJldHVybiBTdHJpbmcuZnJvbUNoYXJDb2RlKChjb2RlIC0gNjU1MzYgPj4gMTApICsgNTUyOTYsIChjb2RlIC0gNjU1MzYgJiAxMDIzKSArIDU2MzIwKTtcbn1cblxucHAucmVhZFN0cmluZyA9IGZ1bmN0aW9uIChxdW90ZSkge1xuICB2YXIgb3V0ID0gXCJcIixcbiAgICAgIGNodW5rU3RhcnQgPSArK3RoaXMucG9zO1xuICBmb3IgKDs7KSB7XG4gICAgaWYgKHRoaXMucG9zID49IHRoaXMuaW5wdXQubGVuZ3RoKSB0aGlzLnJhaXNlKHRoaXMuc3RhcnQsIFwiVW50ZXJtaW5hdGVkIHN0cmluZyBjb25zdGFudFwiKTtcbiAgICB2YXIgY2ggPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MpO1xuICAgIGlmIChjaCA9PT0gcXVvdGUpIGJyZWFrO1xuICAgIGlmIChjaCA9PT0gOTIpIHtcbiAgICAgIC8vICdcXCdcbiAgICAgIG91dCArPSB0aGlzLmlucHV0LnNsaWNlKGNodW5rU3RhcnQsIHRoaXMucG9zKTtcbiAgICAgIG91dCArPSB0aGlzLnJlYWRFc2NhcGVkQ2hhcigpO1xuICAgICAgY2h1bmtTdGFydCA9IHRoaXMucG9zO1xuICAgIH0gZWxzZSB7XG4gICAgICBpZiAoaXNOZXdMaW5lKGNoKSkgdGhpcy5yYWlzZSh0aGlzLnN0YXJ0LCBcIlVudGVybWluYXRlZCBzdHJpbmcgY29uc3RhbnRcIik7XG4gICAgICArK3RoaXMucG9zO1xuICAgIH1cbiAgfVxuICBvdXQgKz0gdGhpcy5pbnB1dC5zbGljZShjaHVua1N0YXJ0LCB0aGlzLnBvcysrKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoVG9rZW4odHQuc3RyaW5nLCBvdXQpO1xufTtcblxuLy8gUmVhZHMgdGVtcGxhdGUgc3RyaW5nIHRva2Vucy5cblxucHAucmVhZFRtcGxUb2tlbiA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIG91dCA9IFwiXCIsXG4gICAgICBjaHVua1N0YXJ0ID0gdGhpcy5wb3M7XG4gIGZvciAoOzspIHtcbiAgICBpZiAodGhpcy5wb3MgPj0gdGhpcy5pbnB1dC5sZW5ndGgpIHRoaXMucmFpc2UodGhpcy5zdGFydCwgXCJVbnRlcm1pbmF0ZWQgdGVtcGxhdGVcIik7XG4gICAgdmFyIGNoID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zKTtcbiAgICBpZiAoY2ggPT09IDk2IHx8IGNoID09PSAzNiAmJiB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAxKSA9PT0gMTIzKSB7XG4gICAgICAvLyAnYCcsICckeydcbiAgICAgIGlmICh0aGlzLnBvcyA9PT0gdGhpcy5zdGFydCAmJiB0aGlzLnR5cGUgPT09IHR0LnRlbXBsYXRlKSB7XG4gICAgICAgIGlmIChjaCA9PT0gMzYpIHtcbiAgICAgICAgICB0aGlzLnBvcyArPSAyO1xuICAgICAgICAgIHJldHVybiB0aGlzLmZpbmlzaFRva2VuKHR0LmRvbGxhckJyYWNlTCk7XG4gICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgKyt0aGlzLnBvcztcbiAgICAgICAgICByZXR1cm4gdGhpcy5maW5pc2hUb2tlbih0dC5iYWNrUXVvdGUpO1xuICAgICAgICB9XG4gICAgICB9XG4gICAgICBvdXQgKz0gdGhpcy5pbnB1dC5zbGljZShjaHVua1N0YXJ0LCB0aGlzLnBvcyk7XG4gICAgICByZXR1cm4gdGhpcy5maW5pc2hUb2tlbih0dC50ZW1wbGF0ZSwgb3V0KTtcbiAgICB9XG4gICAgaWYgKGNoID09PSA5Mikge1xuICAgICAgLy8gJ1xcJ1xuICAgICAgb3V0ICs9IHRoaXMuaW5wdXQuc2xpY2UoY2h1bmtTdGFydCwgdGhpcy5wb3MpO1xuICAgICAgb3V0ICs9IHRoaXMucmVhZEVzY2FwZWRDaGFyKCk7XG4gICAgICBjaHVua1N0YXJ0ID0gdGhpcy5wb3M7XG4gICAgfSBlbHNlIGlmIChpc05ld0xpbmUoY2gpKSB7XG4gICAgICBvdXQgKz0gdGhpcy5pbnB1dC5zbGljZShjaHVua1N0YXJ0LCB0aGlzLnBvcyk7XG4gICAgICArK3RoaXMucG9zO1xuICAgICAgaWYgKGNoID09PSAxMyAmJiB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MpID09PSAxMCkge1xuICAgICAgICArK3RoaXMucG9zO1xuICAgICAgICBvdXQgKz0gXCJcXG5cIjtcbiAgICAgIH0gZWxzZSB7XG4gICAgICAgIG91dCArPSBTdHJpbmcuZnJvbUNoYXJDb2RlKGNoKTtcbiAgICAgIH1cbiAgICAgIGlmICh0aGlzLm9wdGlvbnMubG9jYXRpb25zKSB7XG4gICAgICAgICsrdGhpcy5jdXJMaW5lO1xuICAgICAgICB0aGlzLmxpbmVTdGFydCA9IHRoaXMucG9zO1xuICAgICAgfVxuICAgICAgY2h1bmtTdGFydCA9IHRoaXMucG9zO1xuICAgIH0gZWxzZSB7XG4gICAgICArK3RoaXMucG9zO1xuICAgIH1cbiAgfVxufTtcblxuLy8gVXNlZCB0byByZWFkIGVzY2FwZWQgY2hhcmFjdGVyc1xuXG5wcC5yZWFkRXNjYXBlZENoYXIgPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBjaCA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCgrK3RoaXMucG9zKTtcbiAgdmFyIG9jdGFsID0gL15bMC03XSsvLmV4ZWModGhpcy5pbnB1dC5zbGljZSh0aGlzLnBvcywgdGhpcy5wb3MgKyAzKSk7XG4gIGlmIChvY3RhbCkgb2N0YWwgPSBvY3RhbFswXTtcbiAgd2hpbGUgKG9jdGFsICYmIHBhcnNlSW50KG9jdGFsLCA4KSA+IDI1NSkgb2N0YWwgPSBvY3RhbC5zbGljZSgwLCAtMSk7XG4gIGlmIChvY3RhbCA9PT0gXCIwXCIpIG9jdGFsID0gbnVsbDtcbiAgKyt0aGlzLnBvcztcbiAgaWYgKG9jdGFsKSB7XG4gICAgaWYgKHRoaXMuc3RyaWN0KSB0aGlzLnJhaXNlKHRoaXMucG9zIC0gMiwgXCJPY3RhbCBsaXRlcmFsIGluIHN0cmljdCBtb2RlXCIpO1xuICAgIHRoaXMucG9zICs9IG9jdGFsLmxlbmd0aCAtIDE7XG4gICAgcmV0dXJuIFN0cmluZy5mcm9tQ2hhckNvZGUocGFyc2VJbnQob2N0YWwsIDgpKTtcbiAgfSBlbHNlIHtcbiAgICBzd2l0Y2ggKGNoKSB7XG4gICAgICBjYXNlIDExMDpcbiAgICAgICAgcmV0dXJuIFwiXFxuXCI7IC8vICduJyAtPiAnXFxuJ1xuICAgICAgY2FzZSAxMTQ6XG4gICAgICAgIHJldHVybiBcIlxcclwiOyAvLyAncicgLT4gJ1xccidcbiAgICAgIGNhc2UgMTIwOlxuICAgICAgICByZXR1cm4gU3RyaW5nLmZyb21DaGFyQ29kZSh0aGlzLnJlYWRIZXhDaGFyKDIpKTsgLy8gJ3gnXG4gICAgICBjYXNlIDExNzpcbiAgICAgICAgcmV0dXJuIGNvZGVQb2ludFRvU3RyaW5nKHRoaXMucmVhZENvZGVQb2ludCgpKTsgLy8gJ3UnXG4gICAgICBjYXNlIDExNjpcbiAgICAgICAgcmV0dXJuIFwiXFx0XCI7IC8vICd0JyAtPiAnXFx0J1xuICAgICAgY2FzZSA5ODpcbiAgICAgICAgcmV0dXJuIFwiXFxiXCI7IC8vICdiJyAtPiAnXFxiJ1xuICAgICAgY2FzZSAxMTg6XG4gICAgICAgIHJldHVybiBcIlxcdTAwMGJcIjsgLy8gJ3YnIC0+ICdcXHUwMDBiJ1xuICAgICAgY2FzZSAxMDI6XG4gICAgICAgIHJldHVybiBcIlxcZlwiOyAvLyAnZicgLT4gJ1xcZidcbiAgICAgIGNhc2UgNDg6XG4gICAgICAgIHJldHVybiBcIlxcdTAwMDBcIjsgLy8gMCAtPiAnXFwwJ1xuICAgICAgY2FzZSAxMzpcbiAgICAgICAgaWYgKHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcykgPT09IDEwKSArK3RoaXMucG9zOyAvLyAnXFxyXFxuJ1xuICAgICAgY2FzZSAxMDpcbiAgICAgICAgLy8gJyBcXG4nXG4gICAgICAgIGlmICh0aGlzLm9wdGlvbnMubG9jYXRpb25zKSB7XG4gICAgICAgICAgdGhpcy5saW5lU3RhcnQgPSB0aGlzLnBvczsrK3RoaXMuY3VyTGluZTtcbiAgICAgICAgfVxuICAgICAgICByZXR1cm4gXCJcIjtcbiAgICAgIGRlZmF1bHQ6XG4gICAgICAgIHJldHVybiBTdHJpbmcuZnJvbUNoYXJDb2RlKGNoKTtcbiAgICB9XG4gIH1cbn07XG5cbi8vIFVzZWQgdG8gcmVhZCBjaGFyYWN0ZXIgZXNjYXBlIHNlcXVlbmNlcyAoJ1xceCcsICdcXHUnLCAnXFxVJykuXG5cbnBwLnJlYWRIZXhDaGFyID0gZnVuY3Rpb24gKGxlbikge1xuICB2YXIgbiA9IHRoaXMucmVhZEludCgxNiwgbGVuKTtcbiAgaWYgKG4gPT09IG51bGwpIHRoaXMucmFpc2UodGhpcy5zdGFydCwgXCJCYWQgY2hhcmFjdGVyIGVzY2FwZSBzZXF1ZW5jZVwiKTtcbiAgcmV0dXJuIG47XG59O1xuXG4vLyBVc2VkIHRvIHNpZ25hbCB0byBjYWxsZXJzIG9mIGByZWFkV29yZDFgIHdoZXRoZXIgdGhlIHdvcmRcbi8vIGNvbnRhaW5lZCBhbnkgZXNjYXBlIHNlcXVlbmNlcy4gVGhpcyBpcyBuZWVkZWQgYmVjYXVzZSB3b3JkcyB3aXRoXG4vLyBlc2NhcGUgc2VxdWVuY2VzIG11c3Qgbm90IGJlIGludGVycHJldGVkIGFzIGtleXdvcmRzLlxuXG52YXIgY29udGFpbnNFc2M7XG5cbi8vIFJlYWQgYW4gaWRlbnRpZmllciwgYW5kIHJldHVybiBpdCBhcyBhIHN0cmluZy4gU2V0cyBgY29udGFpbnNFc2NgXG4vLyB0byB3aGV0aGVyIHRoZSB3b3JkIGNvbnRhaW5lZCBhICdcXHUnIGVzY2FwZS5cbi8vXG4vLyBJbmNyZW1lbnRhbGx5IGFkZHMgb25seSBlc2NhcGVkIGNoYXJzLCBhZGRpbmcgb3RoZXIgY2h1bmtzIGFzLWlzXG4vLyBhcyBhIG1pY3JvLW9wdGltaXphdGlvbi5cblxucHAucmVhZFdvcmQxID0gZnVuY3Rpb24gKCkge1xuICBjb250YWluc0VzYyA9IGZhbHNlO1xuICB2YXIgd29yZCA9IFwiXCIsXG4gICAgICBmaXJzdCA9IHRydWUsXG4gICAgICBjaHVua1N0YXJ0ID0gdGhpcy5wb3M7XG4gIHZhciBhc3RyYWwgPSB0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNjtcbiAgd2hpbGUgKHRoaXMucG9zIDwgdGhpcy5pbnB1dC5sZW5ndGgpIHtcbiAgICB2YXIgY2ggPSB0aGlzLmZ1bGxDaGFyQ29kZUF0UG9zKCk7XG4gICAgaWYgKGlzSWRlbnRpZmllckNoYXIoY2gsIGFzdHJhbCkpIHtcbiAgICAgIHRoaXMucG9zICs9IGNoIDw9IDY1NTM1ID8gMSA6IDI7XG4gICAgfSBlbHNlIGlmIChjaCA9PT0gOTIpIHtcbiAgICAgIC8vIFwiXFxcIlxuICAgICAgY29udGFpbnNFc2MgPSB0cnVlO1xuICAgICAgd29yZCArPSB0aGlzLmlucHV0LnNsaWNlKGNodW5rU3RhcnQsIHRoaXMucG9zKTtcbiAgICAgIHZhciBlc2NTdGFydCA9IHRoaXMucG9zO1xuICAgICAgaWYgKHRoaXMuaW5wdXQuY2hhckNvZGVBdCgrK3RoaXMucG9zKSAhPSAxMTcpIC8vIFwidVwiXG4gICAgICAgIHRoaXMucmFpc2UodGhpcy5wb3MsIFwiRXhwZWN0aW5nIFVuaWNvZGUgZXNjYXBlIHNlcXVlbmNlIFxcXFx1WFhYWFwiKTtcbiAgICAgICsrdGhpcy5wb3M7XG4gICAgICB2YXIgZXNjID0gdGhpcy5yZWFkQ29kZVBvaW50KCk7XG4gICAgICBpZiAoIShmaXJzdCA/IGlzSWRlbnRpZmllclN0YXJ0IDogaXNJZGVudGlmaWVyQ2hhcikoZXNjLCBhc3RyYWwpKSB0aGlzLnJhaXNlKGVzY1N0YXJ0LCBcIkludmFsaWQgVW5pY29kZSBlc2NhcGVcIik7XG4gICAgICB3b3JkICs9IGNvZGVQb2ludFRvU3RyaW5nKGVzYyk7XG4gICAgICBjaHVua1N0YXJ0ID0gdGhpcy5wb3M7XG4gICAgfSBlbHNlIHtcbiAgICAgIGJyZWFrO1xuICAgIH1cbiAgICBmaXJzdCA9IGZhbHNlO1xuICB9XG4gIHJldHVybiB3b3JkICsgdGhpcy5pbnB1dC5zbGljZShjaHVua1N0YXJ0LCB0aGlzLnBvcyk7XG59O1xuXG4vLyBSZWFkIGFuIGlkZW50aWZpZXIgb3Iga2V5d29yZCB0b2tlbi4gV2lsbCBjaGVjayBmb3IgcmVzZXJ2ZWRcbi8vIHdvcmRzIHdoZW4gbmVjZXNzYXJ5LlxuXG5wcC5yZWFkV29yZCA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIHdvcmQgPSB0aGlzLnJlYWRXb3JkMSgpO1xuICB2YXIgdHlwZSA9IHR0Lm5hbWU7XG4gIGlmICgodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYgfHwgIWNvbnRhaW5zRXNjKSAmJiB0aGlzLmlzS2V5d29yZCh3b3JkKSkgdHlwZSA9IGtleXdvcmRUeXBlc1t3b3JkXTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoVG9rZW4odHlwZSwgd29yZCk7XG59O1xuXG59LHtcIi4vaWRlbnRpZmllclwiOjcsXCIuL2xvY2F0aW9uXCI6OCxcIi4vc3RhdGVcIjoxMyxcIi4vdG9rZW50eXBlXCI6MTcsXCIuL3doaXRlc3BhY2VcIjoxOX1dLDE3OltmdW5jdGlvbihfZGVyZXFfLG1vZHVsZSxleHBvcnRzKXtcblwidXNlIHN0cmljdFwiO1xuXG52YXIgX2NsYXNzQ2FsbENoZWNrID0gZnVuY3Rpb24gKGluc3RhbmNlLCBDb25zdHJ1Y3RvcikgeyBpZiAoIShpbnN0YW5jZSBpbnN0YW5jZW9mIENvbnN0cnVjdG9yKSkgeyB0aHJvdyBuZXcgVHlwZUVycm9yKFwiQ2Fubm90IGNhbGwgYSBjbGFzcyBhcyBhIGZ1bmN0aW9uXCIpOyB9IH07XG5cbmV4cG9ydHMuX19lc01vZHVsZSA9IHRydWU7XG4vLyAjIyBUb2tlbiB0eXBlc1xuXG4vLyBUaGUgYXNzaWdubWVudCBvZiBmaW5lLWdyYWluZWQsIGluZm9ybWF0aW9uLWNhcnJ5aW5nIHR5cGUgb2JqZWN0c1xuLy8gYWxsb3dzIHRoZSB0b2tlbml6ZXIgdG8gc3RvcmUgdGhlIGluZm9ybWF0aW9uIGl0IGhhcyBhYm91dCBhXG4vLyB0b2tlbiBpbiBhIHdheSB0aGF0IGlzIHZlcnkgY2hlYXAgZm9yIHRoZSBwYXJzZXIgdG8gbG9vayB1cC5cblxuLy8gQWxsIHRva2VuIHR5cGUgdmFyaWFibGVzIHN0YXJ0IHdpdGggYW4gdW5kZXJzY29yZSwgdG8gbWFrZSB0aGVtXG4vLyBlYXN5IHRvIHJlY29nbml6ZS5cblxuLy8gVGhlIGBiZWZvcmVFeHByYCBwcm9wZXJ0eSBpcyB1c2VkIHRvIGRpc2FtYmlndWF0ZSBiZXR3ZWVuIHJlZ3VsYXJcbi8vIGV4cHJlc3Npb25zIGFuZCBkaXZpc2lvbnMuIEl0IGlzIHNldCBvbiBhbGwgdG9rZW4gdHlwZXMgdGhhdCBjYW5cbi8vIGJlIGZvbGxvd2VkIGJ5IGFuIGV4cHJlc3Npb24gKHRodXMsIGEgc2xhc2ggYWZ0ZXIgdGhlbSB3b3VsZCBiZSBhXG4vLyByZWd1bGFyIGV4cHJlc3Npb24pLlxuLy9cbi8vIGBpc0xvb3BgIG1hcmtzIGEga2V5d29yZCBhcyBzdGFydGluZyBhIGxvb3AsIHdoaWNoIGlzIGltcG9ydGFudFxuLy8gdG8ga25vdyB3aGVuIHBhcnNpbmcgYSBsYWJlbCwgaW4gb3JkZXIgdG8gYWxsb3cgb3IgZGlzYWxsb3dcbi8vIGNvbnRpbnVlIGp1bXBzIHRvIHRoYXQgbGFiZWwuXG5cbnZhciBUb2tlblR5cGUgPSBleHBvcnRzLlRva2VuVHlwZSA9IGZ1bmN0aW9uIFRva2VuVHlwZShsYWJlbCkge1xuICB2YXIgY29uZiA9IGFyZ3VtZW50c1sxXSA9PT0gdW5kZWZpbmVkID8ge30gOiBhcmd1bWVudHNbMV07XG5cbiAgX2NsYXNzQ2FsbENoZWNrKHRoaXMsIFRva2VuVHlwZSk7XG5cbiAgdGhpcy5sYWJlbCA9IGxhYmVsO1xuICB0aGlzLmtleXdvcmQgPSBjb25mLmtleXdvcmQ7XG4gIHRoaXMuYmVmb3JlRXhwciA9ICEhY29uZi5iZWZvcmVFeHByO1xuICB0aGlzLnN0YXJ0c0V4cHIgPSAhIWNvbmYuc3RhcnRzRXhwcjtcbiAgdGhpcy5pc0xvb3AgPSAhIWNvbmYuaXNMb29wO1xuICB0aGlzLmlzQXNzaWduID0gISFjb25mLmlzQXNzaWduO1xuICB0aGlzLnByZWZpeCA9ICEhY29uZi5wcmVmaXg7XG4gIHRoaXMucG9zdGZpeCA9ICEhY29uZi5wb3N0Zml4O1xuICB0aGlzLmJpbm9wID0gY29uZi5iaW5vcCB8fCBudWxsO1xuICB0aGlzLnVwZGF0ZUNvbnRleHQgPSBudWxsO1xufTtcblxuZnVuY3Rpb24gYmlub3AobmFtZSwgcHJlYykge1xuICByZXR1cm4gbmV3IFRva2VuVHlwZShuYW1lLCB7IGJlZm9yZUV4cHI6IHRydWUsIGJpbm9wOiBwcmVjIH0pO1xufVxudmFyIGJlZm9yZUV4cHIgPSB7IGJlZm9yZUV4cHI6IHRydWUgfSxcbiAgICBzdGFydHNFeHByID0geyBzdGFydHNFeHByOiB0cnVlIH07XG5cbnZhciB0eXBlcyA9IHtcbiAgbnVtOiBuZXcgVG9rZW5UeXBlKFwibnVtXCIsIHN0YXJ0c0V4cHIpLFxuICByZWdleHA6IG5ldyBUb2tlblR5cGUoXCJyZWdleHBcIiwgc3RhcnRzRXhwciksXG4gIHN0cmluZzogbmV3IFRva2VuVHlwZShcInN0cmluZ1wiLCBzdGFydHNFeHByKSxcbiAgbmFtZTogbmV3IFRva2VuVHlwZShcIm5hbWVcIiwgc3RhcnRzRXhwciksXG4gIGVvZjogbmV3IFRva2VuVHlwZShcImVvZlwiKSxcblxuICAvLyBQdW5jdHVhdGlvbiB0b2tlbiB0eXBlcy5cbiAgYnJhY2tldEw6IG5ldyBUb2tlblR5cGUoXCJbXCIsIHsgYmVmb3JlRXhwcjogdHJ1ZSwgc3RhcnRzRXhwcjogdHJ1ZSB9KSxcbiAgYnJhY2tldFI6IG5ldyBUb2tlblR5cGUoXCJdXCIpLFxuICBicmFjZUw6IG5ldyBUb2tlblR5cGUoXCJ7XCIsIHsgYmVmb3JlRXhwcjogdHJ1ZSwgc3RhcnRzRXhwcjogdHJ1ZSB9KSxcbiAgYnJhY2VSOiBuZXcgVG9rZW5UeXBlKFwifVwiKSxcbiAgcGFyZW5MOiBuZXcgVG9rZW5UeXBlKFwiKFwiLCB7IGJlZm9yZUV4cHI6IHRydWUsIHN0YXJ0c0V4cHI6IHRydWUgfSksXG4gIHBhcmVuUjogbmV3IFRva2VuVHlwZShcIilcIiksXG4gIGNvbW1hOiBuZXcgVG9rZW5UeXBlKFwiLFwiLCBiZWZvcmVFeHByKSxcbiAgc2VtaTogbmV3IFRva2VuVHlwZShcIjtcIiwgYmVmb3JlRXhwciksXG4gIGNvbG9uOiBuZXcgVG9rZW5UeXBlKFwiOlwiLCBiZWZvcmVFeHByKSxcbiAgZG90OiBuZXcgVG9rZW5UeXBlKFwiLlwiKSxcbiAgcXVlc3Rpb246IG5ldyBUb2tlblR5cGUoXCI/XCIsIGJlZm9yZUV4cHIpLFxuICBhcnJvdzogbmV3IFRva2VuVHlwZShcIj0+XCIsIGJlZm9yZUV4cHIpLFxuICB0ZW1wbGF0ZTogbmV3IFRva2VuVHlwZShcInRlbXBsYXRlXCIpLFxuICBlbGxpcHNpczogbmV3IFRva2VuVHlwZShcIi4uLlwiLCBiZWZvcmVFeHByKSxcbiAgYmFja1F1b3RlOiBuZXcgVG9rZW5UeXBlKFwiYFwiLCBzdGFydHNFeHByKSxcbiAgZG9sbGFyQnJhY2VMOiBuZXcgVG9rZW5UeXBlKFwiJHtcIiwgeyBiZWZvcmVFeHByOiB0cnVlLCBzdGFydHNFeHByOiB0cnVlIH0pLFxuXG4gIC8vIE9wZXJhdG9ycy4gVGhlc2UgY2Fycnkgc2V2ZXJhbCBraW5kcyBvZiBwcm9wZXJ0aWVzIHRvIGhlbHAgdGhlXG4gIC8vIHBhcnNlciB1c2UgdGhlbSBwcm9wZXJseSAodGhlIHByZXNlbmNlIG9mIHRoZXNlIHByb3BlcnRpZXMgaXNcbiAgLy8gd2hhdCBjYXRlZ29yaXplcyB0aGVtIGFzIG9wZXJhdG9ycykuXG4gIC8vXG4gIC8vIGBiaW5vcGAsIHdoZW4gcHJlc2VudCwgc3BlY2lmaWVzIHRoYXQgdGhpcyBvcGVyYXRvciBpcyBhIGJpbmFyeVxuICAvLyBvcGVyYXRvciwgYW5kIHdpbGwgcmVmZXIgdG8gaXRzIHByZWNlZGVuY2UuXG4gIC8vXG4gIC8vIGBwcmVmaXhgIGFuZCBgcG9zdGZpeGAgbWFyayB0aGUgb3BlcmF0b3IgYXMgYSBwcmVmaXggb3IgcG9zdGZpeFxuICAvLyB1bmFyeSBvcGVyYXRvci5cbiAgLy9cbiAgLy8gYGlzQXNzaWduYCBtYXJrcyBhbGwgb2YgYD1gLCBgKz1gLCBgLT1gIGV0Y2V0ZXJhLCB3aGljaCBhY3QgYXNcbiAgLy8gYmluYXJ5IG9wZXJhdG9ycyB3aXRoIGEgdmVyeSBsb3cgcHJlY2VkZW5jZSwgdGhhdCBzaG91bGQgcmVzdWx0XG4gIC8vIGluIEFzc2lnbm1lbnRFeHByZXNzaW9uIG5vZGVzLlxuXG4gIGVxOiBuZXcgVG9rZW5UeXBlKFwiPVwiLCB7IGJlZm9yZUV4cHI6IHRydWUsIGlzQXNzaWduOiB0cnVlIH0pLFxuICBhc3NpZ246IG5ldyBUb2tlblR5cGUoXCJfPVwiLCB7IGJlZm9yZUV4cHI6IHRydWUsIGlzQXNzaWduOiB0cnVlIH0pLFxuICBpbmNEZWM6IG5ldyBUb2tlblR5cGUoXCIrKy8tLVwiLCB7IHByZWZpeDogdHJ1ZSwgcG9zdGZpeDogdHJ1ZSwgc3RhcnRzRXhwcjogdHJ1ZSB9KSxcbiAgcHJlZml4OiBuZXcgVG9rZW5UeXBlKFwicHJlZml4XCIsIHsgYmVmb3JlRXhwcjogdHJ1ZSwgcHJlZml4OiB0cnVlLCBzdGFydHNFeHByOiB0cnVlIH0pLFxuICBsb2dpY2FsT1I6IGJpbm9wKFwifHxcIiwgMSksXG4gIGxvZ2ljYWxBTkQ6IGJpbm9wKFwiJiZcIiwgMiksXG4gIGJpdHdpc2VPUjogYmlub3AoXCJ8XCIsIDMpLFxuICBiaXR3aXNlWE9SOiBiaW5vcChcIl5cIiwgNCksXG4gIGJpdHdpc2VBTkQ6IGJpbm9wKFwiJlwiLCA1KSxcbiAgZXF1YWxpdHk6IGJpbm9wKFwiPT0vIT1cIiwgNiksXG4gIHJlbGF0aW9uYWw6IGJpbm9wKFwiPC8+XCIsIDcpLFxuICBiaXRTaGlmdDogYmlub3AoXCI8PC8+PlwiLCA4KSxcbiAgcGx1c01pbjogbmV3IFRva2VuVHlwZShcIisvLVwiLCB7IGJlZm9yZUV4cHI6IHRydWUsIGJpbm9wOiA5LCBwcmVmaXg6IHRydWUsIHN0YXJ0c0V4cHI6IHRydWUgfSksXG4gIG1vZHVsbzogYmlub3AoXCIlXCIsIDEwKSxcbiAgc3RhcjogYmlub3AoXCIqXCIsIDEwKSxcbiAgc2xhc2g6IGJpbm9wKFwiL1wiLCAxMClcbn07XG5cbmV4cG9ydHMudHlwZXMgPSB0eXBlcztcbi8vIE1hcCBrZXl3b3JkIG5hbWVzIHRvIHRva2VuIHR5cGVzLlxuXG52YXIga2V5d29yZHMgPSB7fTtcblxuZXhwb3J0cy5rZXl3b3JkcyA9IGtleXdvcmRzO1xuLy8gU3VjY2luY3QgZGVmaW5pdGlvbnMgb2Yga2V5d29yZCB0b2tlbiB0eXBlc1xuZnVuY3Rpb24ga3cobmFtZSkge1xuICB2YXIgb3B0aW9ucyA9IGFyZ3VtZW50c1sxXSA9PT0gdW5kZWZpbmVkID8ge30gOiBhcmd1bWVudHNbMV07XG5cbiAgb3B0aW9ucy5rZXl3b3JkID0gbmFtZTtcbiAga2V5d29yZHNbbmFtZV0gPSB0eXBlc1tcIl9cIiArIG5hbWVdID0gbmV3IFRva2VuVHlwZShuYW1lLCBvcHRpb25zKTtcbn1cblxua3coXCJicmVha1wiKTtcbmt3KFwiY2FzZVwiLCBiZWZvcmVFeHByKTtcbmt3KFwiY2F0Y2hcIik7XG5rdyhcImNvbnRpbnVlXCIpO1xua3coXCJkZWJ1Z2dlclwiKTtcbmt3KFwiZGVmYXVsdFwiKTtcbmt3KFwiZG9cIiwgeyBpc0xvb3A6IHRydWUgfSk7XG5rdyhcImVsc2VcIiwgYmVmb3JlRXhwcik7XG5rdyhcImZpbmFsbHlcIik7XG5rdyhcImZvclwiLCB7IGlzTG9vcDogdHJ1ZSB9KTtcbmt3KFwiZnVuY3Rpb25cIiwgc3RhcnRzRXhwcik7XG5rdyhcImlmXCIpO1xua3coXCJyZXR1cm5cIiwgYmVmb3JlRXhwcik7XG5rdyhcInN3aXRjaFwiKTtcbmt3KFwidGhyb3dcIiwgYmVmb3JlRXhwcik7XG5rdyhcInRyeVwiKTtcbmt3KFwidmFyXCIpO1xua3coXCJsZXRcIik7XG5rdyhcImNvbnN0XCIpO1xua3coXCJ3aGlsZVwiLCB7IGlzTG9vcDogdHJ1ZSB9KTtcbmt3KFwid2l0aFwiKTtcbmt3KFwibmV3XCIsIHsgYmVmb3JlRXhwcjogdHJ1ZSwgc3RhcnRzRXhwcjogdHJ1ZSB9KTtcbmt3KFwidGhpc1wiLCBzdGFydHNFeHByKTtcbmt3KFwic3VwZXJcIiwgc3RhcnRzRXhwcik7XG5rdyhcImNsYXNzXCIpO1xua3coXCJleHRlbmRzXCIsIGJlZm9yZUV4cHIpO1xua3coXCJleHBvcnRcIik7XG5rdyhcImltcG9ydFwiKTtcbmt3KFwieWllbGRcIiwgeyBiZWZvcmVFeHByOiB0cnVlLCBzdGFydHNFeHByOiB0cnVlIH0pO1xua3coXCJudWxsXCIsIHN0YXJ0c0V4cHIpO1xua3coXCJ0cnVlXCIsIHN0YXJ0c0V4cHIpO1xua3coXCJmYWxzZVwiLCBzdGFydHNFeHByKTtcbmt3KFwiaW5cIiwgeyBiZWZvcmVFeHByOiB0cnVlLCBiaW5vcDogNyB9KTtcbmt3KFwiaW5zdGFuY2VvZlwiLCB7IGJlZm9yZUV4cHI6IHRydWUsIGJpbm9wOiA3IH0pO1xua3coXCJ0eXBlb2ZcIiwgeyBiZWZvcmVFeHByOiB0cnVlLCBwcmVmaXg6IHRydWUsIHN0YXJ0c0V4cHI6IHRydWUgfSk7XG5rdyhcInZvaWRcIiwgeyBiZWZvcmVFeHByOiB0cnVlLCBwcmVmaXg6IHRydWUsIHN0YXJ0c0V4cHI6IHRydWUgfSk7XG5rdyhcImRlbGV0ZVwiLCB7IGJlZm9yZUV4cHI6IHRydWUsIHByZWZpeDogdHJ1ZSwgc3RhcnRzRXhwcjogdHJ1ZSB9KTtcblxufSx7fV0sMTg6W2Z1bmN0aW9uKF9kZXJlcV8sbW9kdWxlLGV4cG9ydHMpe1xuXCJ1c2Ugc3RyaWN0XCI7XG5cbmV4cG9ydHMuaXNBcnJheSA9IGlzQXJyYXk7XG5cbi8vIENoZWNrcyBpZiBhbiBvYmplY3QgaGFzIGEgcHJvcGVydHkuXG5cbmV4cG9ydHMuaGFzID0gaGFzO1xuZXhwb3J0cy5fX2VzTW9kdWxlID0gdHJ1ZTtcblxuZnVuY3Rpb24gaXNBcnJheShvYmopIHtcbiAgcmV0dXJuIE9iamVjdC5wcm90b3R5cGUudG9TdHJpbmcuY2FsbChvYmopID09PSBcIltvYmplY3QgQXJyYXldXCI7XG59XG5cbmZ1bmN0aW9uIGhhcyhvYmosIHByb3BOYW1lKSB7XG4gIHJldHVybiBPYmplY3QucHJvdG90eXBlLmhhc093blByb3BlcnR5LmNhbGwob2JqLCBwcm9wTmFtZSk7XG59XG5cbn0se31dLDE5OltmdW5jdGlvbihfZGVyZXFfLG1vZHVsZSxleHBvcnRzKXtcblwidXNlIHN0cmljdFwiO1xuXG5leHBvcnRzLmlzTmV3TGluZSA9IGlzTmV3TGluZTtcbmV4cG9ydHMuX19lc01vZHVsZSA9IHRydWU7XG4vLyBNYXRjaGVzIGEgd2hvbGUgbGluZSBicmVhayAod2hlcmUgQ1JMRiBpcyBjb25zaWRlcmVkIGEgc2luZ2xlXG4vLyBsaW5lIGJyZWFrKS4gVXNlZCB0byBjb3VudCBsaW5lcy5cblxudmFyIGxpbmVCcmVhayA9IC9cXHJcXG4/fFxcbnxcXHUyMDI4fFxcdTIwMjkvO1xuZXhwb3J0cy5saW5lQnJlYWsgPSBsaW5lQnJlYWs7XG52YXIgbGluZUJyZWFrRyA9IG5ldyBSZWdFeHAobGluZUJyZWFrLnNvdXJjZSwgXCJnXCIpO1xuXG5leHBvcnRzLmxpbmVCcmVha0cgPSBsaW5lQnJlYWtHO1xuXG5mdW5jdGlvbiBpc05ld0xpbmUoY29kZSkge1xuICByZXR1cm4gY29kZSA9PT0gMTAgfHwgY29kZSA9PT0gMTMgfHwgY29kZSA9PT0gODIzMiB8fCBjb2RlID09IDgyMzM7XG59XG5cbnZhciBub25BU0NJSXdoaXRlc3BhY2UgPSAvW1xcdTE2ODBcXHUxODBlXFx1MjAwMC1cXHUyMDBhXFx1MjAyZlxcdTIwNWZcXHUzMDAwXFx1ZmVmZl0vO1xuZXhwb3J0cy5ub25BU0NJSXdoaXRlc3BhY2UgPSBub25BU0NJSXdoaXRlc3BhY2U7XG5cbn0se31dfSx7fSxbMV0pKDEpXG59KTsiLCIoZnVuY3Rpb24oZil7aWYodHlwZW9mIGV4cG9ydHM9PT1cIm9iamVjdFwiJiZ0eXBlb2YgbW9kdWxlIT09XCJ1bmRlZmluZWRcIil7bW9kdWxlLmV4cG9ydHM9ZigpfWVsc2UgaWYodHlwZW9mIGRlZmluZT09PVwiZnVuY3Rpb25cIiYmZGVmaW5lLmFtZCl7ZGVmaW5lKFtdLGYpfWVsc2V7dmFyIGc7aWYodHlwZW9mIHdpbmRvdyE9PVwidW5kZWZpbmVkXCIpe2c9d2luZG93fWVsc2UgaWYodHlwZW9mIGdsb2JhbCE9PVwidW5kZWZpbmVkXCIpe2c9Z2xvYmFsfWVsc2UgaWYodHlwZW9mIHNlbGYhPT1cInVuZGVmaW5lZFwiKXtnPXNlbGZ9ZWxzZXtnPXRoaXN9KGcuYWNvcm4gfHwgKGcuYWNvcm4gPSB7fSkpLmxvb3NlID0gZigpfX0pKGZ1bmN0aW9uKCl7dmFyIGRlZmluZSxtb2R1bGUsZXhwb3J0cztyZXR1cm4gKGZ1bmN0aW9uIGUodCxuLHIpe2Z1bmN0aW9uIHMobyx1KXtpZighbltvXSl7aWYoIXRbb10pe3ZhciBhPXR5cGVvZiByZXF1aXJlPT1cImZ1bmN0aW9uXCImJnJlcXVpcmU7aWYoIXUmJmEpcmV0dXJuIGEobywhMCk7aWYoaSlyZXR1cm4gaShvLCEwKTt2YXIgZj1uZXcgRXJyb3IoXCJDYW5ub3QgZmluZCBtb2R1bGUgJ1wiK28rXCInXCIpO3Rocm93IGYuY29kZT1cIk1PRFVMRV9OT1RfRk9VTkRcIixmfXZhciBsPW5bb109e2V4cG9ydHM6e319O3Rbb11bMF0uY2FsbChsLmV4cG9ydHMsZnVuY3Rpb24oZSl7dmFyIG49dFtvXVsxXVtlXTtyZXR1cm4gcyhuP246ZSl9LGwsbC5leHBvcnRzLGUsdCxuLHIpfXJldHVybiBuW29dLmV4cG9ydHN9dmFyIGk9dHlwZW9mIHJlcXVpcmU9PVwiZnVuY3Rpb25cIiYmcmVxdWlyZTtmb3IodmFyIG89MDtvPHIubGVuZ3RoO28rKylzKHJbb10pO3JldHVybiBzfSkoezE6W2Z1bmN0aW9uKF9kZXJlcV8sbW9kdWxlLGV4cG9ydHMpe1xuXCJ1c2Ugc3RyaWN0XCI7XG5cbnZhciBfaW50ZXJvcFJlcXVpcmVXaWxkY2FyZCA9IGZ1bmN0aW9uIChvYmopIHsgcmV0dXJuIG9iaiAmJiBvYmouX19lc01vZHVsZSA/IG9iaiA6IHsgXCJkZWZhdWx0XCI6IG9iaiB9OyB9O1xuXG5leHBvcnRzLnBhcnNlX2RhbW1pdCA9IHBhcnNlX2RhbW1pdDtcbmV4cG9ydHMuX19lc01vZHVsZSA9IHRydWU7XG4vLyBBY29ybjogTG9vc2UgcGFyc2VyXG4vL1xuLy8gVGhpcyBtb2R1bGUgcHJvdmlkZXMgYW4gYWx0ZXJuYXRpdmUgcGFyc2VyIChgcGFyc2VfZGFtbWl0YCkgdGhhdFxuLy8gZXhwb3NlcyB0aGF0IHNhbWUgaW50ZXJmYWNlIGFzIGBwYXJzZWAsIGJ1dCB3aWxsIHRyeSB0byBwYXJzZVxuLy8gYW55dGhpbmcgYXMgSmF2YVNjcmlwdCwgcmVwYWlyaW5nIHN5bnRheCBlcnJvciB0aGUgYmVzdCBpdCBjYW4uXG4vLyBUaGVyZSBhcmUgY2lyY3Vtc3RhbmNlcyBpbiB3aGljaCBpdCB3aWxsIHJhaXNlIGFuIGVycm9yIGFuZCBnaXZlXG4vLyB1cCwgYnV0IHRoZXkgYXJlIHZlcnkgcmFyZS4gVGhlIHJlc3VsdGluZyBBU1Qgd2lsbCBiZSBhIG1vc3RseVxuLy8gdmFsaWQgSmF2YVNjcmlwdCBBU1QgKGFzIHBlciB0aGUgW01vemlsbGEgcGFyc2VyIEFQSV1bYXBpXSwgZXhjZXB0XG4vLyB0aGF0OlxuLy9cbi8vIC0gUmV0dXJuIG91dHNpZGUgZnVuY3Rpb25zIGlzIGFsbG93ZWRcbi8vXG4vLyAtIExhYmVsIGNvbnNpc3RlbmN5IChubyBjb25mbGljdHMsIGJyZWFrIG9ubHkgdG8gZXhpc3RpbmcgbGFiZWxzKVxuLy8gICBpcyBub3QgZW5mb3JjZWQuXG4vL1xuLy8gLSBCb2d1cyBJZGVudGlmaWVyIG5vZGVzIHdpdGggYSBuYW1lIG9mIGBcIuKcllwiYCBhcmUgaW5zZXJ0ZWQgd2hlbmV2ZXJcbi8vICAgdGhlIHBhcnNlciBnb3QgdG9vIGNvbmZ1c2VkIHRvIHJldHVybiBhbnl0aGluZyBtZWFuaW5nZnVsLlxuLy9cbi8vIFthcGldOiBodHRwczovL2RldmVsb3Blci5tb3ppbGxhLm9yZy9lbi1VUy9kb2NzL1NwaWRlck1vbmtleS9QYXJzZXJfQVBJXG4vL1xuLy8gVGhlIGV4cGVjdGVkIHVzZSBmb3IgdGhpcyBpcyB0byAqZmlyc3QqIHRyeSBgYWNvcm4ucGFyc2VgLCBhbmQgb25seVxuLy8gaWYgdGhhdCBmYWlscyBzd2l0Y2ggdG8gYHBhcnNlX2RhbW1pdGAuIFRoZSBsb29zZSBwYXJzZXIgbWlnaHRcbi8vIHBhcnNlIGJhZGx5IGluZGVudGVkIGNvZGUgaW5jb3JyZWN0bHksIHNvICoqZG9uJ3QqKiB1c2UgaXQgYXNcbi8vIHlvdXIgZGVmYXVsdCBwYXJzZXIuXG4vL1xuLy8gUXVpdGUgYSBsb3Qgb2YgYWNvcm4uanMgaXMgZHVwbGljYXRlZCBoZXJlLiBUaGUgYWx0ZXJuYXRpdmUgd2FzIHRvXG4vLyBhZGQgYSAqbG90KiBvZiBleHRyYSBjcnVmdCB0byB0aGF0IGZpbGUsIG1ha2luZyBpdCBsZXNzIHJlYWRhYmxlXG4vLyBhbmQgc2xvd2VyLiBDb3B5aW5nIGFuZCBlZGl0aW5nIHRoZSBjb2RlIGFsbG93ZWQgbWUgdG8gbWFrZVxuLy8gaW52YXNpdmUgY2hhbmdlcyBhbmQgc2ltcGxpZmljYXRpb25zIHdpdGhvdXQgY3JlYXRpbmcgYSBjb21wbGljYXRlZFxuLy8gdGFuZ2xlLlxuXG52YXIgYWNvcm4gPSBfaW50ZXJvcFJlcXVpcmVXaWxkY2FyZChfZGVyZXFfKFwiLi5cIikpO1xuXG52YXIgX3N0YXRlID0gX2RlcmVxXyhcIi4vc3RhdGVcIik7XG5cbnZhciBMb29zZVBhcnNlciA9IF9zdGF0ZS5Mb29zZVBhcnNlcjtcblxuX2RlcmVxXyhcIi4vdG9rZW5pemVcIik7XG5cbl9kZXJlcV8oXCIuL3BhcnNldXRpbFwiKTtcblxuX2RlcmVxXyhcIi4vc3RhdGVtZW50XCIpO1xuXG5fZGVyZXFfKFwiLi9leHByZXNzaW9uXCIpO1xuXG5leHBvcnRzLkxvb3NlUGFyc2VyID0gX3N0YXRlLkxvb3NlUGFyc2VyO1xuXG5hY29ybi5kZWZhdWx0T3B0aW9ucy50YWJTaXplID0gNDtcblxuZnVuY3Rpb24gcGFyc2VfZGFtbWl0KGlucHV0LCBvcHRpb25zKSB7XG4gIHZhciBwID0gbmV3IExvb3NlUGFyc2VyKGlucHV0LCBvcHRpb25zKTtcbiAgcC5uZXh0KCk7XG4gIHJldHVybiBwLnBhcnNlVG9wTGV2ZWwoKTtcbn1cblxuYWNvcm4ucGFyc2VfZGFtbWl0ID0gcGFyc2VfZGFtbWl0O1xuYWNvcm4uTG9vc2VQYXJzZXIgPSBMb29zZVBhcnNlcjtcblxufSx7XCIuLlwiOjMsXCIuL2V4cHJlc3Npb25cIjo0LFwiLi9wYXJzZXV0aWxcIjo1LFwiLi9zdGF0ZVwiOjYsXCIuL3N0YXRlbWVudFwiOjcsXCIuL3Rva2VuaXplXCI6OH1dLDI6W2Z1bmN0aW9uKF9kZXJlcV8sbW9kdWxlLGV4cG9ydHMpe1xuKGZ1bmN0aW9uIChnbG9iYWwpe1xuXCJ1c2Ugc3RyaWN0XCI7KGZ1bmN0aW9uKGYpe2lmKHR5cGVvZiBleHBvcnRzID09PSBcIm9iamVjdFwiICYmIHR5cGVvZiBtb2R1bGUgIT09IFwidW5kZWZpbmVkXCIpe21vZHVsZS5leHBvcnRzID0gZigpO31lbHNlIGlmKHR5cGVvZiBkZWZpbmUgPT09IFwiZnVuY3Rpb25cIiAmJiBkZWZpbmUuYW1kKXtkZWZpbmUoW10sIGYpO31lbHNlIHt2YXIgZztpZih0eXBlb2Ygd2luZG93ICE9PSBcInVuZGVmaW5lZFwiKXtnID0gd2luZG93O31lbHNlIGlmKHR5cGVvZiBnbG9iYWwgIT09IFwidW5kZWZpbmVkXCIpe2cgPSBnbG9iYWw7fWVsc2UgaWYodHlwZW9mIHNlbGYgIT09IFwidW5kZWZpbmVkXCIpe2cgPSBzZWxmO31lbHNlIHtnID0gdGhpczt9Zy5hY29ybiA9IGYoKTt9fSkoZnVuY3Rpb24oKXt2YXIgZGVmaW5lLCBtb2R1bGUsIGV4cG9ydHM7cmV0dXJuIChmdW5jdGlvbiBlKHQsIG4sIHIpe2Z1bmN0aW9uIHMobywgdSl7aWYoIW5bb10pe2lmKCF0W29dKXt2YXIgYT10eXBlb2YgX2RlcmVxXyA9PSBcImZ1bmN0aW9uXCIgJiYgX2RlcmVxXztpZighdSAmJiBhKXtyZXR1cm4gYShvLCAhMCk7fWlmKGkpe3JldHVybiBpKG8sICEwKTt9dmFyIGY9bmV3IEVycm9yKFwiQ2Fubm90IGZpbmQgbW9kdWxlICdcIiArIG8gKyBcIidcIik7dGhyb3cgKGYuY29kZSA9IFwiTU9EVUxFX05PVF9GT1VORFwiLCBmKTt9dmFyIGw9bltvXSA9IHtleHBvcnRzOnt9fTt0W29dWzBdLmNhbGwobC5leHBvcnRzLCBmdW5jdGlvbihlKXt2YXIgbj10W29dWzFdW2VdO3JldHVybiBzKG4/bjplKTt9LCBsLCBsLmV4cG9ydHMsIGUsIHQsIG4sIHIpO31yZXR1cm4gbltvXS5leHBvcnRzO312YXIgaT10eXBlb2YgX2RlcmVxXyA9PSBcImZ1bmN0aW9uXCIgJiYgX2RlcmVxXztmb3IodmFyIG89MDsgbyA8IHIubGVuZ3RoOyBvKyspIHMocltvXSk7cmV0dXJuIHM7fSkoezE6W2Z1bmN0aW9uKF9kZXJlcV8sIG1vZHVsZSwgZXhwb3J0cyl7XCJ1c2Ugc3RyaWN0XCI7ZXhwb3J0cy5wYXJzZSA9IHBhcnNlO2V4cG9ydHMucGFyc2VFeHByZXNzaW9uQXQgPSBwYXJzZUV4cHJlc3Npb25BdDtleHBvcnRzLnRva2VuaXplciA9IHRva2VuaXplcjtleHBvcnRzLl9fZXNNb2R1bGUgPSB0cnVlO3ZhciBfc3RhdGU9X2RlcmVxXyhcIi4vc3RhdGVcIik7dmFyIFBhcnNlcj1fc3RhdGUuUGFyc2VyO3ZhciBfb3B0aW9ucz1fZGVyZXFfKFwiLi9vcHRpb25zXCIpO3ZhciBnZXRPcHRpb25zPV9vcHRpb25zLmdldE9wdGlvbnM7X2RlcmVxXyhcIi4vcGFyc2V1dGlsXCIpO19kZXJlcV8oXCIuL3N0YXRlbWVudFwiKTtfZGVyZXFfKFwiLi9sdmFsXCIpO19kZXJlcV8oXCIuL2V4cHJlc3Npb25cIik7ZXhwb3J0cy5QYXJzZXIgPSBfc3RhdGUuUGFyc2VyO2V4cG9ydHMucGx1Z2lucyA9IF9zdGF0ZS5wbHVnaW5zO2V4cG9ydHMuZGVmYXVsdE9wdGlvbnMgPSBfb3B0aW9ucy5kZWZhdWx0T3B0aW9uczt2YXIgX2xvY2F0aW9uPV9kZXJlcV8oXCIuL2xvY2F0aW9uXCIpO2V4cG9ydHMuU291cmNlTG9jYXRpb24gPSBfbG9jYXRpb24uU291cmNlTG9jYXRpb247ZXhwb3J0cy5nZXRMaW5lSW5mbyA9IF9sb2NhdGlvbi5nZXRMaW5lSW5mbztleHBvcnRzLk5vZGUgPSBfZGVyZXFfKFwiLi9ub2RlXCIpLk5vZGU7dmFyIF90b2tlbnR5cGU9X2RlcmVxXyhcIi4vdG9rZW50eXBlXCIpO2V4cG9ydHMuVG9rZW5UeXBlID0gX3Rva2VudHlwZS5Ub2tlblR5cGU7ZXhwb3J0cy50b2tUeXBlcyA9IF90b2tlbnR5cGUudHlwZXM7dmFyIF90b2tlbmNvbnRleHQ9X2RlcmVxXyhcIi4vdG9rZW5jb250ZXh0XCIpO2V4cG9ydHMuVG9rQ29udGV4dCA9IF90b2tlbmNvbnRleHQuVG9rQ29udGV4dDtleHBvcnRzLnRva0NvbnRleHRzID0gX3Rva2VuY29udGV4dC50eXBlczt2YXIgX2lkZW50aWZpZXI9X2RlcmVxXyhcIi4vaWRlbnRpZmllclwiKTtleHBvcnRzLmlzSWRlbnRpZmllckNoYXIgPSBfaWRlbnRpZmllci5pc0lkZW50aWZpZXJDaGFyO2V4cG9ydHMuaXNJZGVudGlmaWVyU3RhcnQgPSBfaWRlbnRpZmllci5pc0lkZW50aWZpZXJTdGFydDtleHBvcnRzLlRva2VuID0gX2RlcmVxXyhcIi4vdG9rZW5pemVcIikuVG9rZW47dmFyIF93aGl0ZXNwYWNlPV9kZXJlcV8oXCIuL3doaXRlc3BhY2VcIik7ZXhwb3J0cy5pc05ld0xpbmUgPSBfd2hpdGVzcGFjZS5pc05ld0xpbmU7ZXhwb3J0cy5saW5lQnJlYWsgPSBfd2hpdGVzcGFjZS5saW5lQnJlYWs7ZXhwb3J0cy5saW5lQnJlYWtHID0gX3doaXRlc3BhY2UubGluZUJyZWFrRzt2YXIgdmVyc2lvbj1cIjEuMi4yXCI7ZXhwb3J0cy52ZXJzaW9uID0gdmVyc2lvbjtmdW5jdGlvbiBwYXJzZShpbnB1dCwgb3B0aW9ucyl7dmFyIHA9cGFyc2VyKG9wdGlvbnMsIGlucHV0KTt2YXIgc3RhcnRQb3M9cC5wb3MsIHN0YXJ0TG9jPXAub3B0aW9ucy5sb2NhdGlvbnMgJiYgcC5jdXJQb3NpdGlvbigpO3AubmV4dFRva2VuKCk7cmV0dXJuIHAucGFyc2VUb3BMZXZlbChwLm9wdGlvbnMucHJvZ3JhbSB8fCBwLnN0YXJ0Tm9kZUF0KHN0YXJ0UG9zLCBzdGFydExvYykpO31mdW5jdGlvbiBwYXJzZUV4cHJlc3Npb25BdChpbnB1dCwgcG9zLCBvcHRpb25zKXt2YXIgcD1wYXJzZXIob3B0aW9ucywgaW5wdXQsIHBvcyk7cC5uZXh0VG9rZW4oKTtyZXR1cm4gcC5wYXJzZUV4cHJlc3Npb24oKTt9ZnVuY3Rpb24gdG9rZW5pemVyKGlucHV0LCBvcHRpb25zKXtyZXR1cm4gcGFyc2VyKG9wdGlvbnMsIGlucHV0KTt9ZnVuY3Rpb24gcGFyc2VyKG9wdGlvbnMsIGlucHV0KXtyZXR1cm4gbmV3IFBhcnNlcihnZXRPcHRpb25zKG9wdGlvbnMpLCBTdHJpbmcoaW5wdXQpKTt9fSwge1wiLi9leHByZXNzaW9uXCI6NiwgXCIuL2lkZW50aWZpZXJcIjo3LCBcIi4vbG9jYXRpb25cIjo4LCBcIi4vbHZhbFwiOjksIFwiLi9ub2RlXCI6MTAsIFwiLi9vcHRpb25zXCI6MTEsIFwiLi9wYXJzZXV0aWxcIjoxMiwgXCIuL3N0YXRlXCI6MTMsIFwiLi9zdGF0ZW1lbnRcIjoxNCwgXCIuL3Rva2VuY29udGV4dFwiOjE1LCBcIi4vdG9rZW5pemVcIjoxNiwgXCIuL3Rva2VudHlwZVwiOjE3LCBcIi4vd2hpdGVzcGFjZVwiOjE5fV0sIDI6W2Z1bmN0aW9uKF9kZXJlcV8sIG1vZHVsZSwgZXhwb3J0cyl7aWYodHlwZW9mIE9iamVjdC5jcmVhdGUgPT09IFwiZnVuY3Rpb25cIil7bW9kdWxlLmV4cG9ydHMgPSBmdW5jdGlvbiBpbmhlcml0cyhjdG9yLCBzdXBlckN0b3Ipe2N0b3Iuc3VwZXJfID0gc3VwZXJDdG9yO2N0b3IucHJvdG90eXBlID0gT2JqZWN0LmNyZWF0ZShzdXBlckN0b3IucHJvdG90eXBlLCB7Y29uc3RydWN0b3I6e3ZhbHVlOmN0b3IsIGVudW1lcmFibGU6ZmFsc2UsIHdyaXRhYmxlOnRydWUsIGNvbmZpZ3VyYWJsZTp0cnVlfX0pO307fWVsc2Uge21vZHVsZS5leHBvcnRzID0gZnVuY3Rpb24gaW5oZXJpdHMoY3Rvciwgc3VwZXJDdG9yKXtjdG9yLnN1cGVyXyA9IHN1cGVyQ3Rvcjt2YXIgVGVtcEN0b3I9ZnVuY3Rpb24gVGVtcEN0b3IoKXt9O1RlbXBDdG9yLnByb3RvdHlwZSA9IHN1cGVyQ3Rvci5wcm90b3R5cGU7Y3Rvci5wcm90b3R5cGUgPSBuZXcgVGVtcEN0b3IoKTtjdG9yLnByb3RvdHlwZS5jb25zdHJ1Y3RvciA9IGN0b3I7fTt9fSwge31dLCAzOltmdW5jdGlvbihfZGVyZXFfLCBtb2R1bGUsIGV4cG9ydHMpe3ZhciBwcm9jZXNzPW1vZHVsZS5leHBvcnRzID0ge307dmFyIHF1ZXVlPVtdO3ZhciBkcmFpbmluZz1mYWxzZTtmdW5jdGlvbiBkcmFpblF1ZXVlKCl7aWYoZHJhaW5pbmcpe3JldHVybjt9ZHJhaW5pbmcgPSB0cnVlO3ZhciBjdXJyZW50UXVldWU7dmFyIGxlbj1xdWV1ZS5sZW5ndGg7d2hpbGUobGVuKSB7Y3VycmVudFF1ZXVlID0gcXVldWU7cXVldWUgPSBbXTt2YXIgaT0tMTt3aGlsZSgrK2kgPCBsZW4pIHtjdXJyZW50UXVldWVbaV0oKTt9bGVuID0gcXVldWUubGVuZ3RoO31kcmFpbmluZyA9IGZhbHNlO31wcm9jZXNzLm5leHRUaWNrID0gZnVuY3Rpb24oZnVuKXtxdWV1ZS5wdXNoKGZ1bik7aWYoIWRyYWluaW5nKXtzZXRUaW1lb3V0KGRyYWluUXVldWUsIDApO319O3Byb2Nlc3MudGl0bGUgPSBcImJyb3dzZXJcIjtwcm9jZXNzLmJyb3dzZXIgPSB0cnVlO3Byb2Nlc3MuZW52ID0ge307cHJvY2Vzcy5hcmd2ID0gW107cHJvY2Vzcy52ZXJzaW9uID0gXCJcIjtwcm9jZXNzLnZlcnNpb25zID0ge307ZnVuY3Rpb24gbm9vcCgpe31wcm9jZXNzLm9uID0gbm9vcDtwcm9jZXNzLmFkZExpc3RlbmVyID0gbm9vcDtwcm9jZXNzLm9uY2UgPSBub29wO3Byb2Nlc3Mub2ZmID0gbm9vcDtwcm9jZXNzLnJlbW92ZUxpc3RlbmVyID0gbm9vcDtwcm9jZXNzLnJlbW92ZUFsbExpc3RlbmVycyA9IG5vb3A7cHJvY2Vzcy5lbWl0ID0gbm9vcDtwcm9jZXNzLmJpbmRpbmcgPSBmdW5jdGlvbihuYW1lKXt0aHJvdyBuZXcgRXJyb3IoXCJwcm9jZXNzLmJpbmRpbmcgaXMgbm90IHN1cHBvcnRlZFwiKTt9O3Byb2Nlc3MuY3dkID0gZnVuY3Rpb24oKXtyZXR1cm4gXCIvXCI7fTtwcm9jZXNzLmNoZGlyID0gZnVuY3Rpb24oZGlyKXt0aHJvdyBuZXcgRXJyb3IoXCJwcm9jZXNzLmNoZGlyIGlzIG5vdCBzdXBwb3J0ZWRcIik7fTtwcm9jZXNzLnVtYXNrID0gZnVuY3Rpb24oKXtyZXR1cm4gMDt9O30sIHt9XSwgNDpbZnVuY3Rpb24oX2RlcmVxXywgbW9kdWxlLCBleHBvcnRzKXttb2R1bGUuZXhwb3J0cyA9IGZ1bmN0aW9uIGlzQnVmZmVyKGFyZyl7cmV0dXJuIGFyZyAmJiB0eXBlb2YgYXJnID09PSBcIm9iamVjdFwiICYmIHR5cGVvZiBhcmcuY29weSA9PT0gXCJmdW5jdGlvblwiICYmIHR5cGVvZiBhcmcuZmlsbCA9PT0gXCJmdW5jdGlvblwiICYmIHR5cGVvZiBhcmcucmVhZFVJbnQ4ID09PSBcImZ1bmN0aW9uXCI7fTt9LCB7fV0sIDU6W2Z1bmN0aW9uKF9kZXJlcV8sIG1vZHVsZSwgZXhwb3J0cyl7KGZ1bmN0aW9uKHByb2Nlc3MsIGdsb2JhbCl7dmFyIGZvcm1hdFJlZ0V4cD0vJVtzZGolXS9nO2V4cG9ydHMuZm9ybWF0ID0gZnVuY3Rpb24oZil7aWYoIWlzU3RyaW5nKGYpKXt2YXIgb2JqZWN0cz1bXTtmb3IodmFyIGk9MDsgaSA8IGFyZ3VtZW50cy5sZW5ndGg7IGkrKykge29iamVjdHMucHVzaChpbnNwZWN0KGFyZ3VtZW50c1tpXSkpO31yZXR1cm4gb2JqZWN0cy5qb2luKFwiIFwiKTt9dmFyIGk9MTt2YXIgYXJncz1hcmd1bWVudHM7dmFyIGxlbj1hcmdzLmxlbmd0aDt2YXIgc3RyPVN0cmluZyhmKS5yZXBsYWNlKGZvcm1hdFJlZ0V4cCwgZnVuY3Rpb24oeCl7aWYoeCA9PT0gXCIlJVwiKXJldHVybiBcIiVcIjtpZihpID49IGxlbilyZXR1cm4geDtzd2l0Y2goeCl7Y2FzZSBcIiVzXCI6cmV0dXJuIFN0cmluZyhhcmdzW2krK10pO2Nhc2UgXCIlZFwiOnJldHVybiBOdW1iZXIoYXJnc1tpKytdKTtjYXNlIFwiJWpcIjp0cnl7cmV0dXJuIEpTT04uc3RyaW5naWZ5KGFyZ3NbaSsrXSk7fWNhdGNoKF8pIHtyZXR1cm4gXCJbQ2lyY3VsYXJdXCI7fWRlZmF1bHQ6cmV0dXJuIHg7fX0pO2Zvcih2YXIgeD1hcmdzW2ldOyBpIDwgbGVuOyB4ID0gYXJnc1srK2ldKSB7aWYoaXNOdWxsKHgpIHx8ICFpc09iamVjdCh4KSl7c3RyICs9IFwiIFwiICsgeDt9ZWxzZSB7c3RyICs9IFwiIFwiICsgaW5zcGVjdCh4KTt9fXJldHVybiBzdHI7fTtleHBvcnRzLmRlcHJlY2F0ZSA9IGZ1bmN0aW9uKGZuLCBtc2cpe2lmKGlzVW5kZWZpbmVkKGdsb2JhbC5wcm9jZXNzKSl7cmV0dXJuIGZ1bmN0aW9uKCl7cmV0dXJuIGV4cG9ydHMuZGVwcmVjYXRlKGZuLCBtc2cpLmFwcGx5KHRoaXMsIGFyZ3VtZW50cyk7fTt9aWYocHJvY2Vzcy5ub0RlcHJlY2F0aW9uID09PSB0cnVlKXtyZXR1cm4gZm47fXZhciB3YXJuZWQ9ZmFsc2U7ZnVuY3Rpb24gZGVwcmVjYXRlZCgpe2lmKCF3YXJuZWQpe2lmKHByb2Nlc3MudGhyb3dEZXByZWNhdGlvbil7dGhyb3cgbmV3IEVycm9yKG1zZyk7fWVsc2UgaWYocHJvY2Vzcy50cmFjZURlcHJlY2F0aW9uKXtjb25zb2xlLnRyYWNlKG1zZyk7fWVsc2Uge2NvbnNvbGUuZXJyb3IobXNnKTt9d2FybmVkID0gdHJ1ZTt9cmV0dXJuIGZuLmFwcGx5KHRoaXMsIGFyZ3VtZW50cyk7fXJldHVybiBkZXByZWNhdGVkO307dmFyIGRlYnVncz17fTt2YXIgZGVidWdFbnZpcm9uO2V4cG9ydHMuZGVidWdsb2cgPSBmdW5jdGlvbihzZXQpe2lmKGlzVW5kZWZpbmVkKGRlYnVnRW52aXJvbikpZGVidWdFbnZpcm9uID0gcHJvY2Vzcy5lbnYuTk9ERV9ERUJVRyB8fCBcIlwiO3NldCA9IHNldC50b1VwcGVyQ2FzZSgpO2lmKCFkZWJ1Z3Nbc2V0XSl7aWYobmV3IFJlZ0V4cChcIlxcXFxiXCIgKyBzZXQgKyBcIlxcXFxiXCIsIFwiaVwiKS50ZXN0KGRlYnVnRW52aXJvbikpe3ZhciBwaWQ9cHJvY2Vzcy5waWQ7ZGVidWdzW3NldF0gPSBmdW5jdGlvbigpe3ZhciBtc2c9ZXhwb3J0cy5mb3JtYXQuYXBwbHkoZXhwb3J0cywgYXJndW1lbnRzKTtjb25zb2xlLmVycm9yKFwiJXMgJWQ6ICVzXCIsIHNldCwgcGlkLCBtc2cpO307fWVsc2Uge2RlYnVnc1tzZXRdID0gZnVuY3Rpb24oKXt9O319cmV0dXJuIGRlYnVnc1tzZXRdO307ZnVuY3Rpb24gaW5zcGVjdChvYmosIG9wdHMpe3ZhciBjdHg9e3NlZW46W10sIHN0eWxpemU6c3R5bGl6ZU5vQ29sb3J9O2lmKGFyZ3VtZW50cy5sZW5ndGggPj0gMyljdHguZGVwdGggPSBhcmd1bWVudHNbMl07aWYoYXJndW1lbnRzLmxlbmd0aCA+PSA0KWN0eC5jb2xvcnMgPSBhcmd1bWVudHNbM107aWYoaXNCb29sZWFuKG9wdHMpKXtjdHguc2hvd0hpZGRlbiA9IG9wdHM7fWVsc2UgaWYob3B0cyl7ZXhwb3J0cy5fZXh0ZW5kKGN0eCwgb3B0cyk7fWlmKGlzVW5kZWZpbmVkKGN0eC5zaG93SGlkZGVuKSljdHguc2hvd0hpZGRlbiA9IGZhbHNlO2lmKGlzVW5kZWZpbmVkKGN0eC5kZXB0aCkpY3R4LmRlcHRoID0gMjtpZihpc1VuZGVmaW5lZChjdHguY29sb3JzKSljdHguY29sb3JzID0gZmFsc2U7aWYoaXNVbmRlZmluZWQoY3R4LmN1c3RvbUluc3BlY3QpKWN0eC5jdXN0b21JbnNwZWN0ID0gdHJ1ZTtpZihjdHguY29sb3JzKWN0eC5zdHlsaXplID0gc3R5bGl6ZVdpdGhDb2xvcjtyZXR1cm4gZm9ybWF0VmFsdWUoY3R4LCBvYmosIGN0eC5kZXB0aCk7fWV4cG9ydHMuaW5zcGVjdCA9IGluc3BlY3Q7aW5zcGVjdC5jb2xvcnMgPSB7Ym9sZDpbMSwgMjJdLCBpdGFsaWM6WzMsIDIzXSwgdW5kZXJsaW5lOls0LCAyNF0sIGludmVyc2U6WzcsIDI3XSwgd2hpdGU6WzM3LCAzOV0sIGdyZXk6WzkwLCAzOV0sIGJsYWNrOlszMCwgMzldLCBibHVlOlszNCwgMzldLCBjeWFuOlszNiwgMzldLCBncmVlbjpbMzIsIDM5XSwgbWFnZW50YTpbMzUsIDM5XSwgcmVkOlszMSwgMzldLCB5ZWxsb3c6WzMzLCAzOV19O2luc3BlY3Quc3R5bGVzID0ge3NwZWNpYWw6XCJjeWFuXCIsIG51bWJlcjpcInllbGxvd1wiLCBib29sZWFuOlwieWVsbG93XCIsIHVuZGVmaW5lZDpcImdyZXlcIiwgXCJudWxsXCI6XCJib2xkXCIsIHN0cmluZzpcImdyZWVuXCIsIGRhdGU6XCJtYWdlbnRhXCIsIHJlZ2V4cDpcInJlZFwifTtmdW5jdGlvbiBzdHlsaXplV2l0aENvbG9yKHN0ciwgc3R5bGVUeXBlKXt2YXIgc3R5bGU9aW5zcGVjdC5zdHlsZXNbc3R5bGVUeXBlXTtpZihzdHlsZSl7cmV0dXJuIFwiXFx1MDAxYltcIiArIGluc3BlY3QuY29sb3JzW3N0eWxlXVswXSArIFwibVwiICsgc3RyICsgXCJcXHUwMDFiW1wiICsgaW5zcGVjdC5jb2xvcnNbc3R5bGVdWzFdICsgXCJtXCI7fWVsc2Uge3JldHVybiBzdHI7fX1mdW5jdGlvbiBzdHlsaXplTm9Db2xvcihzdHIsIHN0eWxlVHlwZSl7cmV0dXJuIHN0cjt9ZnVuY3Rpb24gYXJyYXlUb0hhc2goYXJyYXkpe3ZhciBoYXNoPXt9O2FycmF5LmZvckVhY2goZnVuY3Rpb24odmFsLCBpZHgpe2hhc2hbdmFsXSA9IHRydWU7fSk7cmV0dXJuIGhhc2g7fWZ1bmN0aW9uIGZvcm1hdFZhbHVlKGN0eCwgdmFsdWUsIHJlY3Vyc2VUaW1lcyl7aWYoY3R4LmN1c3RvbUluc3BlY3QgJiYgdmFsdWUgJiYgaXNGdW5jdGlvbih2YWx1ZS5pbnNwZWN0KSAmJiB2YWx1ZS5pbnNwZWN0ICE9PSBleHBvcnRzLmluc3BlY3QgJiYgISh2YWx1ZS5jb25zdHJ1Y3RvciAmJiB2YWx1ZS5jb25zdHJ1Y3Rvci5wcm90b3R5cGUgPT09IHZhbHVlKSl7dmFyIHJldD12YWx1ZS5pbnNwZWN0KHJlY3Vyc2VUaW1lcywgY3R4KTtpZighaXNTdHJpbmcocmV0KSl7cmV0ID0gZm9ybWF0VmFsdWUoY3R4LCByZXQsIHJlY3Vyc2VUaW1lcyk7fXJldHVybiByZXQ7fXZhciBwcmltaXRpdmU9Zm9ybWF0UHJpbWl0aXZlKGN0eCwgdmFsdWUpO2lmKHByaW1pdGl2ZSl7cmV0dXJuIHByaW1pdGl2ZTt9dmFyIGtleXM9T2JqZWN0LmtleXModmFsdWUpO3ZhciB2aXNpYmxlS2V5cz1hcnJheVRvSGFzaChrZXlzKTtpZihjdHguc2hvd0hpZGRlbil7a2V5cyA9IE9iamVjdC5nZXRPd25Qcm9wZXJ0eU5hbWVzKHZhbHVlKTt9aWYoaXNFcnJvcih2YWx1ZSkgJiYgKGtleXMuaW5kZXhPZihcIm1lc3NhZ2VcIikgPj0gMCB8fCBrZXlzLmluZGV4T2YoXCJkZXNjcmlwdGlvblwiKSA+PSAwKSl7cmV0dXJuIGZvcm1hdEVycm9yKHZhbHVlKTt9aWYoa2V5cy5sZW5ndGggPT09IDApe2lmKGlzRnVuY3Rpb24odmFsdWUpKXt2YXIgbmFtZT12YWx1ZS5uYW1lP1wiOiBcIiArIHZhbHVlLm5hbWU6XCJcIjtyZXR1cm4gY3R4LnN0eWxpemUoXCJbRnVuY3Rpb25cIiArIG5hbWUgKyBcIl1cIiwgXCJzcGVjaWFsXCIpO31pZihpc1JlZ0V4cCh2YWx1ZSkpe3JldHVybiBjdHguc3R5bGl6ZShSZWdFeHAucHJvdG90eXBlLnRvU3RyaW5nLmNhbGwodmFsdWUpLCBcInJlZ2V4cFwiKTt9aWYoaXNEYXRlKHZhbHVlKSl7cmV0dXJuIGN0eC5zdHlsaXplKERhdGUucHJvdG90eXBlLnRvU3RyaW5nLmNhbGwodmFsdWUpLCBcImRhdGVcIik7fWlmKGlzRXJyb3IodmFsdWUpKXtyZXR1cm4gZm9ybWF0RXJyb3IodmFsdWUpO319dmFyIGJhc2U9XCJcIiwgYXJyYXk9ZmFsc2UsIGJyYWNlcz1bXCJ7XCIsIFwifVwiXTtpZihpc0FycmF5KHZhbHVlKSl7YXJyYXkgPSB0cnVlO2JyYWNlcyA9IFtcIltcIiwgXCJdXCJdO31pZihpc0Z1bmN0aW9uKHZhbHVlKSl7dmFyIG49dmFsdWUubmFtZT9cIjogXCIgKyB2YWx1ZS5uYW1lOlwiXCI7YmFzZSA9IFwiIFtGdW5jdGlvblwiICsgbiArIFwiXVwiO31pZihpc1JlZ0V4cCh2YWx1ZSkpe2Jhc2UgPSBcIiBcIiArIFJlZ0V4cC5wcm90b3R5cGUudG9TdHJpbmcuY2FsbCh2YWx1ZSk7fWlmKGlzRGF0ZSh2YWx1ZSkpe2Jhc2UgPSBcIiBcIiArIERhdGUucHJvdG90eXBlLnRvVVRDU3RyaW5nLmNhbGwodmFsdWUpO31pZihpc0Vycm9yKHZhbHVlKSl7YmFzZSA9IFwiIFwiICsgZm9ybWF0RXJyb3IodmFsdWUpO31pZihrZXlzLmxlbmd0aCA9PT0gMCAmJiAoIWFycmF5IHx8IHZhbHVlLmxlbmd0aCA9PSAwKSl7cmV0dXJuIGJyYWNlc1swXSArIGJhc2UgKyBicmFjZXNbMV07fWlmKHJlY3Vyc2VUaW1lcyA8IDApe2lmKGlzUmVnRXhwKHZhbHVlKSl7cmV0dXJuIGN0eC5zdHlsaXplKFJlZ0V4cC5wcm90b3R5cGUudG9TdHJpbmcuY2FsbCh2YWx1ZSksIFwicmVnZXhwXCIpO31lbHNlIHtyZXR1cm4gY3R4LnN0eWxpemUoXCJbT2JqZWN0XVwiLCBcInNwZWNpYWxcIik7fX1jdHguc2Vlbi5wdXNoKHZhbHVlKTt2YXIgb3V0cHV0O2lmKGFycmF5KXtvdXRwdXQgPSBmb3JtYXRBcnJheShjdHgsIHZhbHVlLCByZWN1cnNlVGltZXMsIHZpc2libGVLZXlzLCBrZXlzKTt9ZWxzZSB7b3V0cHV0ID0ga2V5cy5tYXAoZnVuY3Rpb24oa2V5KXtyZXR1cm4gZm9ybWF0UHJvcGVydHkoY3R4LCB2YWx1ZSwgcmVjdXJzZVRpbWVzLCB2aXNpYmxlS2V5cywga2V5LCBhcnJheSk7fSk7fWN0eC5zZWVuLnBvcCgpO3JldHVybiByZWR1Y2VUb1NpbmdsZVN0cmluZyhvdXRwdXQsIGJhc2UsIGJyYWNlcyk7fWZ1bmN0aW9uIGZvcm1hdFByaW1pdGl2ZShjdHgsIHZhbHVlKXtpZihpc1VuZGVmaW5lZCh2YWx1ZSkpe3JldHVybiBjdHguc3R5bGl6ZShcInVuZGVmaW5lZFwiLCBcInVuZGVmaW5lZFwiKTt9aWYoaXNTdHJpbmcodmFsdWUpKXt2YXIgc2ltcGxlPVwiJ1wiICsgSlNPTi5zdHJpbmdpZnkodmFsdWUpLnJlcGxhY2UoL15cInxcIiQvZywgXCJcIikucmVwbGFjZSgvJy9nLCBcIlxcXFwnXCIpLnJlcGxhY2UoL1xcXFxcIi9nLCBcIlxcXCJcIikgKyBcIidcIjtyZXR1cm4gY3R4LnN0eWxpemUoc2ltcGxlLCBcInN0cmluZ1wiKTt9aWYoaXNOdW1iZXIodmFsdWUpKXtyZXR1cm4gY3R4LnN0eWxpemUoXCJcIiArIHZhbHVlLCBcIm51bWJlclwiKTt9aWYoaXNCb29sZWFuKHZhbHVlKSl7cmV0dXJuIGN0eC5zdHlsaXplKFwiXCIgKyB2YWx1ZSwgXCJib29sZWFuXCIpO31pZihpc051bGwodmFsdWUpKXtyZXR1cm4gY3R4LnN0eWxpemUoXCJudWxsXCIsIFwibnVsbFwiKTt9fWZ1bmN0aW9uIGZvcm1hdEVycm9yKHZhbHVlKXtyZXR1cm4gXCJbXCIgKyBFcnJvci5wcm90b3R5cGUudG9TdHJpbmcuY2FsbCh2YWx1ZSkgKyBcIl1cIjt9ZnVuY3Rpb24gZm9ybWF0QXJyYXkoY3R4LCB2YWx1ZSwgcmVjdXJzZVRpbWVzLCB2aXNpYmxlS2V5cywga2V5cyl7dmFyIG91dHB1dD1bXTtmb3IodmFyIGk9MCwgbD12YWx1ZS5sZW5ndGg7IGkgPCBsOyArK2kpIHtpZihoYXNPd25Qcm9wZXJ0eSh2YWx1ZSwgU3RyaW5nKGkpKSl7b3V0cHV0LnB1c2goZm9ybWF0UHJvcGVydHkoY3R4LCB2YWx1ZSwgcmVjdXJzZVRpbWVzLCB2aXNpYmxlS2V5cywgU3RyaW5nKGkpLCB0cnVlKSk7fWVsc2Uge291dHB1dC5wdXNoKFwiXCIpO319a2V5cy5mb3JFYWNoKGZ1bmN0aW9uKGtleSl7aWYoIWtleS5tYXRjaCgvXlxcZCskLykpe291dHB1dC5wdXNoKGZvcm1hdFByb3BlcnR5KGN0eCwgdmFsdWUsIHJlY3Vyc2VUaW1lcywgdmlzaWJsZUtleXMsIGtleSwgdHJ1ZSkpO319KTtyZXR1cm4gb3V0cHV0O31mdW5jdGlvbiBmb3JtYXRQcm9wZXJ0eShjdHgsIHZhbHVlLCByZWN1cnNlVGltZXMsIHZpc2libGVLZXlzLCBrZXksIGFycmF5KXt2YXIgbmFtZSwgc3RyLCBkZXNjO2Rlc2MgPSBPYmplY3QuZ2V0T3duUHJvcGVydHlEZXNjcmlwdG9yKHZhbHVlLCBrZXkpIHx8IHt2YWx1ZTp2YWx1ZVtrZXldfTtpZihkZXNjLmdldCl7aWYoZGVzYy5zZXQpe3N0ciA9IGN0eC5zdHlsaXplKFwiW0dldHRlci9TZXR0ZXJdXCIsIFwic3BlY2lhbFwiKTt9ZWxzZSB7c3RyID0gY3R4LnN0eWxpemUoXCJbR2V0dGVyXVwiLCBcInNwZWNpYWxcIik7fX1lbHNlIHtpZihkZXNjLnNldCl7c3RyID0gY3R4LnN0eWxpemUoXCJbU2V0dGVyXVwiLCBcInNwZWNpYWxcIik7fX1pZighaGFzT3duUHJvcGVydHkodmlzaWJsZUtleXMsIGtleSkpe25hbWUgPSBcIltcIiArIGtleSArIFwiXVwiO31pZighc3RyKXtpZihjdHguc2Vlbi5pbmRleE9mKGRlc2MudmFsdWUpIDwgMCl7aWYoaXNOdWxsKHJlY3Vyc2VUaW1lcykpe3N0ciA9IGZvcm1hdFZhbHVlKGN0eCwgZGVzYy52YWx1ZSwgbnVsbCk7fWVsc2Uge3N0ciA9IGZvcm1hdFZhbHVlKGN0eCwgZGVzYy52YWx1ZSwgcmVjdXJzZVRpbWVzIC0gMSk7fWlmKHN0ci5pbmRleE9mKFwiXFxuXCIpID4gLTEpe2lmKGFycmF5KXtzdHIgPSBzdHIuc3BsaXQoXCJcXG5cIikubWFwKGZ1bmN0aW9uKGxpbmUpe3JldHVybiBcIiAgXCIgKyBsaW5lO30pLmpvaW4oXCJcXG5cIikuc3Vic3RyKDIpO31lbHNlIHtzdHIgPSBcIlxcblwiICsgc3RyLnNwbGl0KFwiXFxuXCIpLm1hcChmdW5jdGlvbihsaW5lKXtyZXR1cm4gXCIgICBcIiArIGxpbmU7fSkuam9pbihcIlxcblwiKTt9fX1lbHNlIHtzdHIgPSBjdHguc3R5bGl6ZShcIltDaXJjdWxhcl1cIiwgXCJzcGVjaWFsXCIpO319aWYoaXNVbmRlZmluZWQobmFtZSkpe2lmKGFycmF5ICYmIGtleS5tYXRjaCgvXlxcZCskLykpe3JldHVybiBzdHI7fW5hbWUgPSBKU09OLnN0cmluZ2lmeShcIlwiICsga2V5KTtpZihuYW1lLm1hdGNoKC9eXCIoW2EtekEtWl9dW2EtekEtWl8wLTldKilcIiQvKSl7bmFtZSA9IG5hbWUuc3Vic3RyKDEsIG5hbWUubGVuZ3RoIC0gMik7bmFtZSA9IGN0eC5zdHlsaXplKG5hbWUsIFwibmFtZVwiKTt9ZWxzZSB7bmFtZSA9IG5hbWUucmVwbGFjZSgvJy9nLCBcIlxcXFwnXCIpLnJlcGxhY2UoL1xcXFxcIi9nLCBcIlxcXCJcIikucmVwbGFjZSgvKF5cInxcIiQpL2csIFwiJ1wiKTtuYW1lID0gY3R4LnN0eWxpemUobmFtZSwgXCJzdHJpbmdcIik7fX1yZXR1cm4gbmFtZSArIFwiOiBcIiArIHN0cjt9ZnVuY3Rpb24gcmVkdWNlVG9TaW5nbGVTdHJpbmcob3V0cHV0LCBiYXNlLCBicmFjZXMpe3ZhciBudW1MaW5lc0VzdD0wO3ZhciBsZW5ndGg9b3V0cHV0LnJlZHVjZShmdW5jdGlvbihwcmV2LCBjdXIpe251bUxpbmVzRXN0Kys7aWYoY3VyLmluZGV4T2YoXCJcXG5cIikgPj0gMCludW1MaW5lc0VzdCsrO3JldHVybiBwcmV2ICsgY3VyLnJlcGxhY2UoL1xcdTAwMWJcXFtcXGRcXGQ/bS9nLCBcIlwiKS5sZW5ndGggKyAxO30sIDApO2lmKGxlbmd0aCA+IDYwKXtyZXR1cm4gYnJhY2VzWzBdICsgKGJhc2UgPT09IFwiXCI/XCJcIjpiYXNlICsgXCJcXG4gXCIpICsgXCIgXCIgKyBvdXRwdXQuam9pbihcIixcXG4gIFwiKSArIFwiIFwiICsgYnJhY2VzWzFdO31yZXR1cm4gYnJhY2VzWzBdICsgYmFzZSArIFwiIFwiICsgb3V0cHV0LmpvaW4oXCIsIFwiKSArIFwiIFwiICsgYnJhY2VzWzFdO31mdW5jdGlvbiBpc0FycmF5KGFyKXtyZXR1cm4gQXJyYXkuaXNBcnJheShhcik7fWV4cG9ydHMuaXNBcnJheSA9IGlzQXJyYXk7ZnVuY3Rpb24gaXNCb29sZWFuKGFyZyl7cmV0dXJuIHR5cGVvZiBhcmcgPT09IFwiYm9vbGVhblwiO31leHBvcnRzLmlzQm9vbGVhbiA9IGlzQm9vbGVhbjtmdW5jdGlvbiBpc051bGwoYXJnKXtyZXR1cm4gYXJnID09PSBudWxsO31leHBvcnRzLmlzTnVsbCA9IGlzTnVsbDtmdW5jdGlvbiBpc051bGxPclVuZGVmaW5lZChhcmcpe3JldHVybiBhcmcgPT0gbnVsbDt9ZXhwb3J0cy5pc051bGxPclVuZGVmaW5lZCA9IGlzTnVsbE9yVW5kZWZpbmVkO2Z1bmN0aW9uIGlzTnVtYmVyKGFyZyl7cmV0dXJuIHR5cGVvZiBhcmcgPT09IFwibnVtYmVyXCI7fWV4cG9ydHMuaXNOdW1iZXIgPSBpc051bWJlcjtmdW5jdGlvbiBpc1N0cmluZyhhcmcpe3JldHVybiB0eXBlb2YgYXJnID09PSBcInN0cmluZ1wiO31leHBvcnRzLmlzU3RyaW5nID0gaXNTdHJpbmc7ZnVuY3Rpb24gaXNTeW1ib2woYXJnKXtyZXR1cm4gdHlwZW9mIGFyZyA9PT0gXCJzeW1ib2xcIjt9ZXhwb3J0cy5pc1N5bWJvbCA9IGlzU3ltYm9sO2Z1bmN0aW9uIGlzVW5kZWZpbmVkKGFyZyl7cmV0dXJuIGFyZyA9PT0gdm9pZCAwO31leHBvcnRzLmlzVW5kZWZpbmVkID0gaXNVbmRlZmluZWQ7ZnVuY3Rpb24gaXNSZWdFeHAocmUpe3JldHVybiBpc09iamVjdChyZSkgJiYgb2JqZWN0VG9TdHJpbmcocmUpID09PSBcIltvYmplY3QgUmVnRXhwXVwiO31leHBvcnRzLmlzUmVnRXhwID0gaXNSZWdFeHA7ZnVuY3Rpb24gaXNPYmplY3QoYXJnKXtyZXR1cm4gdHlwZW9mIGFyZyA9PT0gXCJvYmplY3RcIiAmJiBhcmcgIT09IG51bGw7fWV4cG9ydHMuaXNPYmplY3QgPSBpc09iamVjdDtmdW5jdGlvbiBpc0RhdGUoZCl7cmV0dXJuIGlzT2JqZWN0KGQpICYmIG9iamVjdFRvU3RyaW5nKGQpID09PSBcIltvYmplY3QgRGF0ZV1cIjt9ZXhwb3J0cy5pc0RhdGUgPSBpc0RhdGU7ZnVuY3Rpb24gaXNFcnJvcihlKXtyZXR1cm4gaXNPYmplY3QoZSkgJiYgKG9iamVjdFRvU3RyaW5nKGUpID09PSBcIltvYmplY3QgRXJyb3JdXCIgfHwgZSBpbnN0YW5jZW9mIEVycm9yKTt9ZXhwb3J0cy5pc0Vycm9yID0gaXNFcnJvcjtmdW5jdGlvbiBpc0Z1bmN0aW9uKGFyZyl7cmV0dXJuIHR5cGVvZiBhcmcgPT09IFwiZnVuY3Rpb25cIjt9ZXhwb3J0cy5pc0Z1bmN0aW9uID0gaXNGdW5jdGlvbjtmdW5jdGlvbiBpc1ByaW1pdGl2ZShhcmcpe3JldHVybiBhcmcgPT09IG51bGwgfHwgdHlwZW9mIGFyZyA9PT0gXCJib29sZWFuXCIgfHwgdHlwZW9mIGFyZyA9PT0gXCJudW1iZXJcIiB8fCB0eXBlb2YgYXJnID09PSBcInN0cmluZ1wiIHx8IHR5cGVvZiBhcmcgPT09IFwic3ltYm9sXCIgfHwgdHlwZW9mIGFyZyA9PT0gXCJ1bmRlZmluZWRcIjt9ZXhwb3J0cy5pc1ByaW1pdGl2ZSA9IGlzUHJpbWl0aXZlO2V4cG9ydHMuaXNCdWZmZXIgPSBfZGVyZXFfKFwiLi9zdXBwb3J0L2lzQnVmZmVyXCIpO2Z1bmN0aW9uIG9iamVjdFRvU3RyaW5nKG8pe3JldHVybiBPYmplY3QucHJvdG90eXBlLnRvU3RyaW5nLmNhbGwobyk7fWZ1bmN0aW9uIHBhZChuKXtyZXR1cm4gbiA8IDEwP1wiMFwiICsgbi50b1N0cmluZygxMCk6bi50b1N0cmluZygxMCk7fXZhciBtb250aHM9W1wiSmFuXCIsIFwiRmViXCIsIFwiTWFyXCIsIFwiQXByXCIsIFwiTWF5XCIsIFwiSnVuXCIsIFwiSnVsXCIsIFwiQXVnXCIsIFwiU2VwXCIsIFwiT2N0XCIsIFwiTm92XCIsIFwiRGVjXCJdO2Z1bmN0aW9uIHRpbWVzdGFtcCgpe3ZhciBkPW5ldyBEYXRlKCk7dmFyIHRpbWU9W3BhZChkLmdldEhvdXJzKCkpLCBwYWQoZC5nZXRNaW51dGVzKCkpLCBwYWQoZC5nZXRTZWNvbmRzKCkpXS5qb2luKFwiOlwiKTtyZXR1cm4gW2QuZ2V0RGF0ZSgpLCBtb250aHNbZC5nZXRNb250aCgpXSwgdGltZV0uam9pbihcIiBcIik7fWV4cG9ydHMubG9nID0gZnVuY3Rpb24oKXtjb25zb2xlLmxvZyhcIiVzIC0gJXNcIiwgdGltZXN0YW1wKCksIGV4cG9ydHMuZm9ybWF0LmFwcGx5KGV4cG9ydHMsIGFyZ3VtZW50cykpO307ZXhwb3J0cy5pbmhlcml0cyA9IF9kZXJlcV8oXCJpbmhlcml0c1wiKTtleHBvcnRzLl9leHRlbmQgPSBmdW5jdGlvbihvcmlnaW4sIGFkZCl7aWYoIWFkZCB8fCAhaXNPYmplY3QoYWRkKSlyZXR1cm4gb3JpZ2luO3ZhciBrZXlzPU9iamVjdC5rZXlzKGFkZCk7dmFyIGk9a2V5cy5sZW5ndGg7d2hpbGUoaS0tKSB7b3JpZ2luW2tleXNbaV1dID0gYWRkW2tleXNbaV1dO31yZXR1cm4gb3JpZ2luO307ZnVuY3Rpb24gaGFzT3duUHJvcGVydHkob2JqLCBwcm9wKXtyZXR1cm4gT2JqZWN0LnByb3RvdHlwZS5oYXNPd25Qcm9wZXJ0eS5jYWxsKG9iaiwgcHJvcCk7fX0pLmNhbGwodGhpcywgX2RlcmVxXyhcIl9wcm9jZXNzXCIpLCB0eXBlb2YgZ2xvYmFsICE9PSBcInVuZGVmaW5lZFwiP2dsb2JhbDp0eXBlb2Ygc2VsZiAhPT0gXCJ1bmRlZmluZWRcIj9zZWxmOnR5cGVvZiB3aW5kb3cgIT09IFwidW5kZWZpbmVkXCI/d2luZG93Ont9KTt9LCB7XCIuL3N1cHBvcnQvaXNCdWZmZXJcIjo0LCBfcHJvY2VzczozLCBpbmhlcml0czoyfV0sIDY6W2Z1bmN0aW9uKF9kZXJlcV8sIG1vZHVsZSwgZXhwb3J0cyl7XCJ1c2Ugc3RyaWN0XCI7dmFyIHR0PV9kZXJlcV8oXCIuL3Rva2VudHlwZVwiKS50eXBlczt2YXIgUGFyc2VyPV9kZXJlcV8oXCIuL3N0YXRlXCIpLlBhcnNlcjt2YXIgcmVzZXJ2ZWRXb3Jkcz1fZGVyZXFfKFwiLi9pZGVudGlmaWVyXCIpLnJlc2VydmVkV29yZHM7dmFyIGhhcz1fZGVyZXFfKFwiLi91dGlsXCIpLmhhczt2YXIgcHA9UGFyc2VyLnByb3RvdHlwZTtwcC5jaGVja1Byb3BDbGFzaCA9IGZ1bmN0aW9uKHByb3AsIHByb3BIYXNoKXtpZih0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNilyZXR1cm47dmFyIGtleT1wcm9wLmtleSwgbmFtZT11bmRlZmluZWQ7c3dpdGNoKGtleS50eXBlKXtjYXNlIFwiSWRlbnRpZmllclwiOm5hbWUgPSBrZXkubmFtZTticmVhaztjYXNlIFwiTGl0ZXJhbFwiOm5hbWUgPSBTdHJpbmcoa2V5LnZhbHVlKTticmVhaztkZWZhdWx0OnJldHVybjt9dmFyIGtpbmQ9cHJvcC5raW5kIHx8IFwiaW5pdFwiLCBvdGhlcj11bmRlZmluZWQ7aWYoaGFzKHByb3BIYXNoLCBuYW1lKSl7b3RoZXIgPSBwcm9wSGFzaFtuYW1lXTt2YXIgaXNHZXRTZXQ9a2luZCAhPT0gXCJpbml0XCI7aWYoKHRoaXMuc3RyaWN0IHx8IGlzR2V0U2V0KSAmJiBvdGhlcltraW5kXSB8fCAhKGlzR2V0U2V0IF4gb3RoZXIuaW5pdCkpdGhpcy5yYWlzZShrZXkuc3RhcnQsIFwiUmVkZWZpbml0aW9uIG9mIHByb3BlcnR5XCIpO31lbHNlIHtvdGhlciA9IHByb3BIYXNoW25hbWVdID0ge2luaXQ6ZmFsc2UsIGdldDpmYWxzZSwgc2V0OmZhbHNlfTt9b3RoZXJba2luZF0gPSB0cnVlO307cHAucGFyc2VFeHByZXNzaW9uID0gZnVuY3Rpb24obm9JbiwgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcyl7dmFyIHN0YXJ0UG9zPXRoaXMuc3RhcnQsIHN0YXJ0TG9jPXRoaXMuc3RhcnRMb2M7dmFyIGV4cHI9dGhpcy5wYXJzZU1heWJlQXNzaWduKG5vSW4sIHJlZlNob3J0aGFuZERlZmF1bHRQb3MpO2lmKHRoaXMudHlwZSA9PT0gdHQuY29tbWEpe3ZhciBub2RlPXRoaXMuc3RhcnROb2RlQXQoc3RhcnRQb3MsIHN0YXJ0TG9jKTtub2RlLmV4cHJlc3Npb25zID0gW2V4cHJdO3doaWxlKHRoaXMuZWF0KHR0LmNvbW1hKSkgbm9kZS5leHByZXNzaW9ucy5wdXNoKHRoaXMucGFyc2VNYXliZUFzc2lnbihub0luLCByZWZTaG9ydGhhbmREZWZhdWx0UG9zKSk7cmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIlNlcXVlbmNlRXhwcmVzc2lvblwiKTt9cmV0dXJuIGV4cHI7fTtwcC5wYXJzZU1heWJlQXNzaWduID0gZnVuY3Rpb24obm9JbiwgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcywgYWZ0ZXJMZWZ0UGFyc2Upe2lmKHRoaXMudHlwZSA9PSB0dC5feWllbGQgJiYgdGhpcy5pbkdlbmVyYXRvcilyZXR1cm4gdGhpcy5wYXJzZVlpZWxkKCk7dmFyIGZhaWxPblNob3J0aGFuZEFzc2lnbj11bmRlZmluZWQ7aWYoIXJlZlNob3J0aGFuZERlZmF1bHRQb3Mpe3JlZlNob3J0aGFuZERlZmF1bHRQb3MgPSB7c3RhcnQ6MH07ZmFpbE9uU2hvcnRoYW5kQXNzaWduID0gdHJ1ZTt9ZWxzZSB7ZmFpbE9uU2hvcnRoYW5kQXNzaWduID0gZmFsc2U7fXZhciBzdGFydFBvcz10aGlzLnN0YXJ0LCBzdGFydExvYz10aGlzLnN0YXJ0TG9jO2lmKHRoaXMudHlwZSA9PSB0dC5wYXJlbkwgfHwgdGhpcy50eXBlID09IHR0Lm5hbWUpdGhpcy5wb3RlbnRpYWxBcnJvd0F0ID0gdGhpcy5zdGFydDt2YXIgbGVmdD10aGlzLnBhcnNlTWF5YmVDb25kaXRpb25hbChub0luLCByZWZTaG9ydGhhbmREZWZhdWx0UG9zKTtpZihhZnRlckxlZnRQYXJzZSlsZWZ0ID0gYWZ0ZXJMZWZ0UGFyc2UuY2FsbCh0aGlzLCBsZWZ0LCBzdGFydFBvcywgc3RhcnRMb2MpO2lmKHRoaXMudHlwZS5pc0Fzc2lnbil7dmFyIG5vZGU9dGhpcy5zdGFydE5vZGVBdChzdGFydFBvcywgc3RhcnRMb2MpO25vZGUub3BlcmF0b3IgPSB0aGlzLnZhbHVlO25vZGUubGVmdCA9IHRoaXMudHlwZSA9PT0gdHQuZXE/dGhpcy50b0Fzc2lnbmFibGUobGVmdCk6bGVmdDtyZWZTaG9ydGhhbmREZWZhdWx0UG9zLnN0YXJ0ID0gMDt0aGlzLmNoZWNrTFZhbChsZWZ0KTt0aGlzLm5leHQoKTtub2RlLnJpZ2h0ID0gdGhpcy5wYXJzZU1heWJlQXNzaWduKG5vSW4pO3JldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJBc3NpZ25tZW50RXhwcmVzc2lvblwiKTt9ZWxzZSBpZihmYWlsT25TaG9ydGhhbmRBc3NpZ24gJiYgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcy5zdGFydCl7dGhpcy51bmV4cGVjdGVkKHJlZlNob3J0aGFuZERlZmF1bHRQb3Muc3RhcnQpO31yZXR1cm4gbGVmdDt9O3BwLnBhcnNlTWF5YmVDb25kaXRpb25hbCA9IGZ1bmN0aW9uKG5vSW4sIHJlZlNob3J0aGFuZERlZmF1bHRQb3Mpe3ZhciBzdGFydFBvcz10aGlzLnN0YXJ0LCBzdGFydExvYz10aGlzLnN0YXJ0TG9jO3ZhciBleHByPXRoaXMucGFyc2VFeHByT3BzKG5vSW4sIHJlZlNob3J0aGFuZERlZmF1bHRQb3MpO2lmKHJlZlNob3J0aGFuZERlZmF1bHRQb3MgJiYgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcy5zdGFydClyZXR1cm4gZXhwcjtpZih0aGlzLmVhdCh0dC5xdWVzdGlvbikpe3ZhciBub2RlPXRoaXMuc3RhcnROb2RlQXQoc3RhcnRQb3MsIHN0YXJ0TG9jKTtub2RlLnRlc3QgPSBleHByO25vZGUuY29uc2VxdWVudCA9IHRoaXMucGFyc2VNYXliZUFzc2lnbigpO3RoaXMuZXhwZWN0KHR0LmNvbG9uKTtub2RlLmFsdGVybmF0ZSA9IHRoaXMucGFyc2VNYXliZUFzc2lnbihub0luKTtyZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiQ29uZGl0aW9uYWxFeHByZXNzaW9uXCIpO31yZXR1cm4gZXhwcjt9O3BwLnBhcnNlRXhwck9wcyA9IGZ1bmN0aW9uKG5vSW4sIHJlZlNob3J0aGFuZERlZmF1bHRQb3Mpe3ZhciBzdGFydFBvcz10aGlzLnN0YXJ0LCBzdGFydExvYz10aGlzLnN0YXJ0TG9jO3ZhciBleHByPXRoaXMucGFyc2VNYXliZVVuYXJ5KHJlZlNob3J0aGFuZERlZmF1bHRQb3MpO2lmKHJlZlNob3J0aGFuZERlZmF1bHRQb3MgJiYgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcy5zdGFydClyZXR1cm4gZXhwcjtyZXR1cm4gdGhpcy5wYXJzZUV4cHJPcChleHByLCBzdGFydFBvcywgc3RhcnRMb2MsIC0xLCBub0luKTt9O3BwLnBhcnNlRXhwck9wID0gZnVuY3Rpb24obGVmdCwgbGVmdFN0YXJ0UG9zLCBsZWZ0U3RhcnRMb2MsIG1pblByZWMsIG5vSW4pe3ZhciBwcmVjPXRoaXMudHlwZS5iaW5vcDtpZihBcnJheS5pc0FycmF5KGxlZnRTdGFydFBvcykpe2lmKHRoaXMub3B0aW9ucy5sb2NhdGlvbnMgJiYgbm9JbiA9PT0gdW5kZWZpbmVkKXtub0luID0gbWluUHJlYzttaW5QcmVjID0gbGVmdFN0YXJ0TG9jO2xlZnRTdGFydExvYyA9IGxlZnRTdGFydFBvc1sxXTtsZWZ0U3RhcnRQb3MgPSBsZWZ0U3RhcnRQb3NbMF07fX1pZihwcmVjICE9IG51bGwgJiYgKCFub0luIHx8IHRoaXMudHlwZSAhPT0gdHQuX2luKSl7aWYocHJlYyA+IG1pblByZWMpe3ZhciBub2RlPXRoaXMuc3RhcnROb2RlQXQobGVmdFN0YXJ0UG9zLCBsZWZ0U3RhcnRMb2MpO25vZGUubGVmdCA9IGxlZnQ7bm9kZS5vcGVyYXRvciA9IHRoaXMudmFsdWU7dmFyIG9wPXRoaXMudHlwZTt0aGlzLm5leHQoKTt2YXIgc3RhcnRQb3M9dGhpcy5zdGFydCwgc3RhcnRMb2M9dGhpcy5zdGFydExvYztub2RlLnJpZ2h0ID0gdGhpcy5wYXJzZUV4cHJPcCh0aGlzLnBhcnNlTWF5YmVVbmFyeSgpLCBzdGFydFBvcywgc3RhcnRMb2MsIHByZWMsIG5vSW4pO3RoaXMuZmluaXNoTm9kZShub2RlLCBvcCA9PT0gdHQubG9naWNhbE9SIHx8IG9wID09PSB0dC5sb2dpY2FsQU5EP1wiTG9naWNhbEV4cHJlc3Npb25cIjpcIkJpbmFyeUV4cHJlc3Npb25cIik7cmV0dXJuIHRoaXMucGFyc2VFeHByT3Aobm9kZSwgbGVmdFN0YXJ0UG9zLCBsZWZ0U3RhcnRMb2MsIG1pblByZWMsIG5vSW4pO319cmV0dXJuIGxlZnQ7fTtwcC5wYXJzZU1heWJlVW5hcnkgPSBmdW5jdGlvbihyZWZTaG9ydGhhbmREZWZhdWx0UG9zKXtpZih0aGlzLnR5cGUucHJlZml4KXt2YXIgbm9kZT10aGlzLnN0YXJ0Tm9kZSgpLCB1cGRhdGU9dGhpcy50eXBlID09PSB0dC5pbmNEZWM7bm9kZS5vcGVyYXRvciA9IHRoaXMudmFsdWU7bm9kZS5wcmVmaXggPSB0cnVlO3RoaXMubmV4dCgpO25vZGUuYXJndW1lbnQgPSB0aGlzLnBhcnNlTWF5YmVVbmFyeSgpO2lmKHJlZlNob3J0aGFuZERlZmF1bHRQb3MgJiYgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcy5zdGFydCl0aGlzLnVuZXhwZWN0ZWQocmVmU2hvcnRoYW5kRGVmYXVsdFBvcy5zdGFydCk7aWYodXBkYXRlKXRoaXMuY2hlY2tMVmFsKG5vZGUuYXJndW1lbnQpO2Vsc2UgaWYodGhpcy5zdHJpY3QgJiYgbm9kZS5vcGVyYXRvciA9PT0gXCJkZWxldGVcIiAmJiBub2RlLmFyZ3VtZW50LnR5cGUgPT09IFwiSWRlbnRpZmllclwiKXRoaXMucmFpc2Uobm9kZS5zdGFydCwgXCJEZWxldGluZyBsb2NhbCB2YXJpYWJsZSBpbiBzdHJpY3QgbW9kZVwiKTtyZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIHVwZGF0ZT9cIlVwZGF0ZUV4cHJlc3Npb25cIjpcIlVuYXJ5RXhwcmVzc2lvblwiKTt9dmFyIHN0YXJ0UG9zPXRoaXMuc3RhcnQsIHN0YXJ0TG9jPXRoaXMuc3RhcnRMb2M7dmFyIGV4cHI9dGhpcy5wYXJzZUV4cHJTdWJzY3JpcHRzKHJlZlNob3J0aGFuZERlZmF1bHRQb3MpO2lmKHJlZlNob3J0aGFuZERlZmF1bHRQb3MgJiYgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcy5zdGFydClyZXR1cm4gZXhwcjt3aGlsZSh0aGlzLnR5cGUucG9zdGZpeCAmJiAhdGhpcy5jYW5JbnNlcnRTZW1pY29sb24oKSkge3ZhciBub2RlPXRoaXMuc3RhcnROb2RlQXQoc3RhcnRQb3MsIHN0YXJ0TG9jKTtub2RlLm9wZXJhdG9yID0gdGhpcy52YWx1ZTtub2RlLnByZWZpeCA9IGZhbHNlO25vZGUuYXJndW1lbnQgPSBleHByO3RoaXMuY2hlY2tMVmFsKGV4cHIpO3RoaXMubmV4dCgpO2V4cHIgPSB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJVcGRhdGVFeHByZXNzaW9uXCIpO31yZXR1cm4gZXhwcjt9O3BwLnBhcnNlRXhwclN1YnNjcmlwdHMgPSBmdW5jdGlvbihyZWZTaG9ydGhhbmREZWZhdWx0UG9zKXt2YXIgc3RhcnRQb3M9dGhpcy5zdGFydCwgc3RhcnRMb2M9dGhpcy5zdGFydExvYzt2YXIgZXhwcj10aGlzLnBhcnNlRXhwckF0b20ocmVmU2hvcnRoYW5kRGVmYXVsdFBvcyk7aWYocmVmU2hvcnRoYW5kRGVmYXVsdFBvcyAmJiByZWZTaG9ydGhhbmREZWZhdWx0UG9zLnN0YXJ0KXJldHVybiBleHByO3JldHVybiB0aGlzLnBhcnNlU3Vic2NyaXB0cyhleHByLCBzdGFydFBvcywgc3RhcnRMb2MpO307cHAucGFyc2VTdWJzY3JpcHRzID0gZnVuY3Rpb24oYmFzZSwgc3RhcnRQb3MsIHN0YXJ0TG9jLCBub0NhbGxzKXtpZihBcnJheS5pc0FycmF5KHN0YXJ0UG9zKSl7aWYodGhpcy5vcHRpb25zLmxvY2F0aW9ucyAmJiBub0NhbGxzID09PSB1bmRlZmluZWQpe25vQ2FsbHMgPSBzdGFydExvYztzdGFydExvYyA9IHN0YXJ0UG9zWzFdO3N0YXJ0UG9zID0gc3RhcnRQb3NbMF07fX1mb3IoOzspIHtpZih0aGlzLmVhdCh0dC5kb3QpKXt2YXIgbm9kZT10aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0UG9zLCBzdGFydExvYyk7bm9kZS5vYmplY3QgPSBiYXNlO25vZGUucHJvcGVydHkgPSB0aGlzLnBhcnNlSWRlbnQodHJ1ZSk7bm9kZS5jb21wdXRlZCA9IGZhbHNlO2Jhc2UgPSB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJNZW1iZXJFeHByZXNzaW9uXCIpO31lbHNlIGlmKHRoaXMuZWF0KHR0LmJyYWNrZXRMKSl7dmFyIG5vZGU9dGhpcy5zdGFydE5vZGVBdChzdGFydFBvcywgc3RhcnRMb2MpO25vZGUub2JqZWN0ID0gYmFzZTtub2RlLnByb3BlcnR5ID0gdGhpcy5wYXJzZUV4cHJlc3Npb24oKTtub2RlLmNvbXB1dGVkID0gdHJ1ZTt0aGlzLmV4cGVjdCh0dC5icmFja2V0Uik7YmFzZSA9IHRoaXMuZmluaXNoTm9kZShub2RlLCBcIk1lbWJlckV4cHJlc3Npb25cIik7fWVsc2UgaWYoIW5vQ2FsbHMgJiYgdGhpcy5lYXQodHQucGFyZW5MKSl7dmFyIG5vZGU9dGhpcy5zdGFydE5vZGVBdChzdGFydFBvcywgc3RhcnRMb2MpO25vZGUuY2FsbGVlID0gYmFzZTtub2RlLmFyZ3VtZW50cyA9IHRoaXMucGFyc2VFeHByTGlzdCh0dC5wYXJlblIsIGZhbHNlKTtiYXNlID0gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiQ2FsbEV4cHJlc3Npb25cIik7fWVsc2UgaWYodGhpcy50eXBlID09PSB0dC5iYWNrUXVvdGUpe3ZhciBub2RlPXRoaXMuc3RhcnROb2RlQXQoc3RhcnRQb3MsIHN0YXJ0TG9jKTtub2RlLnRhZyA9IGJhc2U7bm9kZS5xdWFzaSA9IHRoaXMucGFyc2VUZW1wbGF0ZSgpO2Jhc2UgPSB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJUYWdnZWRUZW1wbGF0ZUV4cHJlc3Npb25cIik7fWVsc2Uge3JldHVybiBiYXNlO319fTtwcC5wYXJzZUV4cHJBdG9tID0gZnVuY3Rpb24ocmVmU2hvcnRoYW5kRGVmYXVsdFBvcyl7dmFyIG5vZGU9dW5kZWZpbmVkLCBjYW5CZUFycm93PXRoaXMucG90ZW50aWFsQXJyb3dBdCA9PSB0aGlzLnN0YXJ0O3N3aXRjaCh0aGlzLnR5cGUpe2Nhc2UgdHQuX3RoaXM6Y2FzZSB0dC5fc3VwZXI6dmFyIHR5cGU9dGhpcy50eXBlID09PSB0dC5fdGhpcz9cIlRoaXNFeHByZXNzaW9uXCI6XCJTdXBlclwiO25vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO3RoaXMubmV4dCgpO3JldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgdHlwZSk7Y2FzZSB0dC5feWllbGQ6aWYodGhpcy5pbkdlbmVyYXRvcil0aGlzLnVuZXhwZWN0ZWQoKTtjYXNlIHR0Lm5hbWU6dmFyIHN0YXJ0UG9zPXRoaXMuc3RhcnQsIHN0YXJ0TG9jPXRoaXMuc3RhcnRMb2M7dmFyIGlkPXRoaXMucGFyc2VJZGVudCh0aGlzLnR5cGUgIT09IHR0Lm5hbWUpO2lmKGNhbkJlQXJyb3cgJiYgIXRoaXMuY2FuSW5zZXJ0U2VtaWNvbG9uKCkgJiYgdGhpcy5lYXQodHQuYXJyb3cpKXJldHVybiB0aGlzLnBhcnNlQXJyb3dFeHByZXNzaW9uKHRoaXMuc3RhcnROb2RlQXQoc3RhcnRQb3MsIHN0YXJ0TG9jKSwgW2lkXSk7cmV0dXJuIGlkO2Nhc2UgdHQucmVnZXhwOnZhciB2YWx1ZT10aGlzLnZhbHVlO25vZGUgPSB0aGlzLnBhcnNlTGl0ZXJhbCh2YWx1ZS52YWx1ZSk7bm9kZS5yZWdleCA9IHtwYXR0ZXJuOnZhbHVlLnBhdHRlcm4sIGZsYWdzOnZhbHVlLmZsYWdzfTtyZXR1cm4gbm9kZTtjYXNlIHR0Lm51bTpjYXNlIHR0LnN0cmluZzpyZXR1cm4gdGhpcy5wYXJzZUxpdGVyYWwodGhpcy52YWx1ZSk7Y2FzZSB0dC5fbnVsbDpjYXNlIHR0Ll90cnVlOmNhc2UgdHQuX2ZhbHNlOm5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO25vZGUudmFsdWUgPSB0aGlzLnR5cGUgPT09IHR0Ll9udWxsP251bGw6dGhpcy50eXBlID09PSB0dC5fdHJ1ZTtub2RlLnJhdyA9IHRoaXMudHlwZS5rZXl3b3JkO3RoaXMubmV4dCgpO3JldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJMaXRlcmFsXCIpO2Nhc2UgdHQucGFyZW5MOnJldHVybiB0aGlzLnBhcnNlUGFyZW5BbmREaXN0aW5ndWlzaEV4cHJlc3Npb24oY2FuQmVBcnJvdyk7Y2FzZSB0dC5icmFja2V0TDpub2RlID0gdGhpcy5zdGFydE5vZGUoKTt0aGlzLm5leHQoKTtpZih0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNyAmJiB0aGlzLnR5cGUgPT09IHR0Ll9mb3Ipe3JldHVybiB0aGlzLnBhcnNlQ29tcHJlaGVuc2lvbihub2RlLCBmYWxzZSk7fW5vZGUuZWxlbWVudHMgPSB0aGlzLnBhcnNlRXhwckxpc3QodHQuYnJhY2tldFIsIHRydWUsIHRydWUsIHJlZlNob3J0aGFuZERlZmF1bHRQb3MpO3JldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJBcnJheUV4cHJlc3Npb25cIik7Y2FzZSB0dC5icmFjZUw6cmV0dXJuIHRoaXMucGFyc2VPYmooZmFsc2UsIHJlZlNob3J0aGFuZERlZmF1bHRQb3MpO2Nhc2UgdHQuX2Z1bmN0aW9uOm5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO3RoaXMubmV4dCgpO3JldHVybiB0aGlzLnBhcnNlRnVuY3Rpb24obm9kZSwgZmFsc2UpO2Nhc2UgdHQuX2NsYXNzOnJldHVybiB0aGlzLnBhcnNlQ2xhc3ModGhpcy5zdGFydE5vZGUoKSwgZmFsc2UpO2Nhc2UgdHQuX25ldzpyZXR1cm4gdGhpcy5wYXJzZU5ldygpO2Nhc2UgdHQuYmFja1F1b3RlOnJldHVybiB0aGlzLnBhcnNlVGVtcGxhdGUoKTtkZWZhdWx0OnRoaXMudW5leHBlY3RlZCgpO319O3BwLnBhcnNlTGl0ZXJhbCA9IGZ1bmN0aW9uKHZhbHVlKXt2YXIgbm9kZT10aGlzLnN0YXJ0Tm9kZSgpO25vZGUudmFsdWUgPSB2YWx1ZTtub2RlLnJhdyA9IHRoaXMuaW5wdXQuc2xpY2UodGhpcy5zdGFydCwgdGhpcy5lbmQpO3RoaXMubmV4dCgpO3JldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJMaXRlcmFsXCIpO307cHAucGFyc2VQYXJlbkV4cHJlc3Npb24gPSBmdW5jdGlvbigpe3RoaXMuZXhwZWN0KHR0LnBhcmVuTCk7dmFyIHZhbD10aGlzLnBhcnNlRXhwcmVzc2lvbigpO3RoaXMuZXhwZWN0KHR0LnBhcmVuUik7cmV0dXJuIHZhbDt9O3BwLnBhcnNlUGFyZW5BbmREaXN0aW5ndWlzaEV4cHJlc3Npb24gPSBmdW5jdGlvbihjYW5CZUFycm93KXt2YXIgc3RhcnRQb3M9dGhpcy5zdGFydCwgc3RhcnRMb2M9dGhpcy5zdGFydExvYywgdmFsPXVuZGVmaW5lZDtpZih0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNil7dGhpcy5uZXh0KCk7aWYodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDcgJiYgdGhpcy50eXBlID09PSB0dC5fZm9yKXtyZXR1cm4gdGhpcy5wYXJzZUNvbXByZWhlbnNpb24odGhpcy5zdGFydE5vZGVBdChzdGFydFBvcywgc3RhcnRMb2MpLCB0cnVlKTt9dmFyIGlubmVyU3RhcnRQb3M9dGhpcy5zdGFydCwgaW5uZXJTdGFydExvYz10aGlzLnN0YXJ0TG9jO3ZhciBleHByTGlzdD1bXSwgZmlyc3Q9dHJ1ZTt2YXIgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcz17c3RhcnQ6MH0sIHNwcmVhZFN0YXJ0PXVuZGVmaW5lZCwgaW5uZXJQYXJlblN0YXJ0PXVuZGVmaW5lZDt3aGlsZSh0aGlzLnR5cGUgIT09IHR0LnBhcmVuUikge2ZpcnN0P2ZpcnN0ID0gZmFsc2U6dGhpcy5leHBlY3QodHQuY29tbWEpO2lmKHRoaXMudHlwZSA9PT0gdHQuZWxsaXBzaXMpe3NwcmVhZFN0YXJ0ID0gdGhpcy5zdGFydDtleHByTGlzdC5wdXNoKHRoaXMucGFyc2VQYXJlbkl0ZW0odGhpcy5wYXJzZVJlc3QoKSkpO2JyZWFrO31lbHNlIHtpZih0aGlzLnR5cGUgPT09IHR0LnBhcmVuTCAmJiAhaW5uZXJQYXJlblN0YXJ0KXtpbm5lclBhcmVuU3RhcnQgPSB0aGlzLnN0YXJ0O31leHByTGlzdC5wdXNoKHRoaXMucGFyc2VNYXliZUFzc2lnbihmYWxzZSwgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcywgdGhpcy5wYXJzZVBhcmVuSXRlbSkpO319dmFyIGlubmVyRW5kUG9zPXRoaXMuc3RhcnQsIGlubmVyRW5kTG9jPXRoaXMuc3RhcnRMb2M7dGhpcy5leHBlY3QodHQucGFyZW5SKTtpZihjYW5CZUFycm93ICYmICF0aGlzLmNhbkluc2VydFNlbWljb2xvbigpICYmIHRoaXMuZWF0KHR0LmFycm93KSl7aWYoaW5uZXJQYXJlblN0YXJ0KXRoaXMudW5leHBlY3RlZChpbm5lclBhcmVuU3RhcnQpO3JldHVybiB0aGlzLnBhcnNlUGFyZW5BcnJvd0xpc3Qoc3RhcnRQb3MsIHN0YXJ0TG9jLCBleHByTGlzdCk7fWlmKCFleHByTGlzdC5sZW5ndGgpdGhpcy51bmV4cGVjdGVkKHRoaXMubGFzdFRva1N0YXJ0KTtpZihzcHJlYWRTdGFydCl0aGlzLnVuZXhwZWN0ZWQoc3ByZWFkU3RhcnQpO2lmKHJlZlNob3J0aGFuZERlZmF1bHRQb3Muc3RhcnQpdGhpcy51bmV4cGVjdGVkKHJlZlNob3J0aGFuZERlZmF1bHRQb3Muc3RhcnQpO2lmKGV4cHJMaXN0Lmxlbmd0aCA+IDEpe3ZhbCA9IHRoaXMuc3RhcnROb2RlQXQoaW5uZXJTdGFydFBvcywgaW5uZXJTdGFydExvYyk7dmFsLmV4cHJlc3Npb25zID0gZXhwckxpc3Q7dGhpcy5maW5pc2hOb2RlQXQodmFsLCBcIlNlcXVlbmNlRXhwcmVzc2lvblwiLCBpbm5lckVuZFBvcywgaW5uZXJFbmRMb2MpO31lbHNlIHt2YWwgPSBleHByTGlzdFswXTt9fWVsc2Uge3ZhbCA9IHRoaXMucGFyc2VQYXJlbkV4cHJlc3Npb24oKTt9aWYodGhpcy5vcHRpb25zLnByZXNlcnZlUGFyZW5zKXt2YXIgcGFyPXRoaXMuc3RhcnROb2RlQXQoc3RhcnRQb3MsIHN0YXJ0TG9jKTtwYXIuZXhwcmVzc2lvbiA9IHZhbDtyZXR1cm4gdGhpcy5maW5pc2hOb2RlKHBhciwgXCJQYXJlbnRoZXNpemVkRXhwcmVzc2lvblwiKTt9ZWxzZSB7cmV0dXJuIHZhbDt9fTtwcC5wYXJzZVBhcmVuSXRlbSA9IGZ1bmN0aW9uKGl0ZW0pe3JldHVybiBpdGVtO307cHAucGFyc2VQYXJlbkFycm93TGlzdCA9IGZ1bmN0aW9uKHN0YXJ0UG9zLCBzdGFydExvYywgZXhwckxpc3Qpe3JldHVybiB0aGlzLnBhcnNlQXJyb3dFeHByZXNzaW9uKHRoaXMuc3RhcnROb2RlQXQoc3RhcnRQb3MsIHN0YXJ0TG9jKSwgZXhwckxpc3QpO307dmFyIGVtcHR5PVtdO3BwLnBhcnNlTmV3ID0gZnVuY3Rpb24oKXt2YXIgbm9kZT10aGlzLnN0YXJ0Tm9kZSgpO3ZhciBtZXRhPXRoaXMucGFyc2VJZGVudCh0cnVlKTtpZih0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNiAmJiB0aGlzLmVhdCh0dC5kb3QpKXtub2RlLm1ldGEgPSBtZXRhO25vZGUucHJvcGVydHkgPSB0aGlzLnBhcnNlSWRlbnQodHJ1ZSk7aWYobm9kZS5wcm9wZXJ0eS5uYW1lICE9PSBcInRhcmdldFwiKXRoaXMucmFpc2Uobm9kZS5wcm9wZXJ0eS5zdGFydCwgXCJUaGUgb25seSB2YWxpZCBtZXRhIHByb3BlcnR5IGZvciBuZXcgaXMgbmV3LnRhcmdldFwiKTtyZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiTWV0YVByb3BlcnR5XCIpO312YXIgc3RhcnRQb3M9dGhpcy5zdGFydCwgc3RhcnRMb2M9dGhpcy5zdGFydExvYztub2RlLmNhbGxlZSA9IHRoaXMucGFyc2VTdWJzY3JpcHRzKHRoaXMucGFyc2VFeHByQXRvbSgpLCBzdGFydFBvcywgc3RhcnRMb2MsIHRydWUpO2lmKHRoaXMuZWF0KHR0LnBhcmVuTCkpbm9kZS5hcmd1bWVudHMgPSB0aGlzLnBhcnNlRXhwckxpc3QodHQucGFyZW5SLCBmYWxzZSk7ZWxzZSBub2RlLmFyZ3VtZW50cyA9IGVtcHR5O3JldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJOZXdFeHByZXNzaW9uXCIpO307cHAucGFyc2VUZW1wbGF0ZUVsZW1lbnQgPSBmdW5jdGlvbigpe3ZhciBlbGVtPXRoaXMuc3RhcnROb2RlKCk7ZWxlbS52YWx1ZSA9IHtyYXc6dGhpcy5pbnB1dC5zbGljZSh0aGlzLnN0YXJ0LCB0aGlzLmVuZCksIGNvb2tlZDp0aGlzLnZhbHVlfTt0aGlzLm5leHQoKTtlbGVtLnRhaWwgPSB0aGlzLnR5cGUgPT09IHR0LmJhY2tRdW90ZTtyZXR1cm4gdGhpcy5maW5pc2hOb2RlKGVsZW0sIFwiVGVtcGxhdGVFbGVtZW50XCIpO307cHAucGFyc2VUZW1wbGF0ZSA9IGZ1bmN0aW9uKCl7dmFyIG5vZGU9dGhpcy5zdGFydE5vZGUoKTt0aGlzLm5leHQoKTtub2RlLmV4cHJlc3Npb25zID0gW107dmFyIGN1ckVsdD10aGlzLnBhcnNlVGVtcGxhdGVFbGVtZW50KCk7bm9kZS5xdWFzaXMgPSBbY3VyRWx0XTt3aGlsZSghY3VyRWx0LnRhaWwpIHt0aGlzLmV4cGVjdCh0dC5kb2xsYXJCcmFjZUwpO25vZGUuZXhwcmVzc2lvbnMucHVzaCh0aGlzLnBhcnNlRXhwcmVzc2lvbigpKTt0aGlzLmV4cGVjdCh0dC5icmFjZVIpO25vZGUucXVhc2lzLnB1c2goY3VyRWx0ID0gdGhpcy5wYXJzZVRlbXBsYXRlRWxlbWVudCgpKTt9dGhpcy5uZXh0KCk7cmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIlRlbXBsYXRlTGl0ZXJhbFwiKTt9O3BwLnBhcnNlT2JqID0gZnVuY3Rpb24oaXNQYXR0ZXJuLCByZWZTaG9ydGhhbmREZWZhdWx0UG9zKXt2YXIgbm9kZT10aGlzLnN0YXJ0Tm9kZSgpLCBmaXJzdD10cnVlLCBwcm9wSGFzaD17fTtub2RlLnByb3BlcnRpZXMgPSBbXTt0aGlzLm5leHQoKTt3aGlsZSghdGhpcy5lYXQodHQuYnJhY2VSKSkge2lmKCFmaXJzdCl7dGhpcy5leHBlY3QodHQuY29tbWEpO2lmKHRoaXMuYWZ0ZXJUcmFpbGluZ0NvbW1hKHR0LmJyYWNlUikpYnJlYWs7fWVsc2UgZmlyc3QgPSBmYWxzZTt2YXIgcHJvcD10aGlzLnN0YXJ0Tm9kZSgpLCBpc0dlbmVyYXRvcj11bmRlZmluZWQsIHN0YXJ0UG9zPXVuZGVmaW5lZCwgc3RhcnRMb2M9dW5kZWZpbmVkO2lmKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KXtwcm9wLm1ldGhvZCA9IGZhbHNlO3Byb3Auc2hvcnRoYW5kID0gZmFsc2U7aWYoaXNQYXR0ZXJuIHx8IHJlZlNob3J0aGFuZERlZmF1bHRQb3Mpe3N0YXJ0UG9zID0gdGhpcy5zdGFydDtzdGFydExvYyA9IHRoaXMuc3RhcnRMb2M7fWlmKCFpc1BhdHRlcm4paXNHZW5lcmF0b3IgPSB0aGlzLmVhdCh0dC5zdGFyKTt9dGhpcy5wYXJzZVByb3BlcnR5TmFtZShwcm9wKTt0aGlzLnBhcnNlUHJvcGVydHlWYWx1ZShwcm9wLCBpc1BhdHRlcm4sIGlzR2VuZXJhdG9yLCBzdGFydFBvcywgc3RhcnRMb2MsIHJlZlNob3J0aGFuZERlZmF1bHRQb3MpO3RoaXMuY2hlY2tQcm9wQ2xhc2gocHJvcCwgcHJvcEhhc2gpO25vZGUucHJvcGVydGllcy5wdXNoKHRoaXMuZmluaXNoTm9kZShwcm9wLCBcIlByb3BlcnR5XCIpKTt9cmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBpc1BhdHRlcm4/XCJPYmplY3RQYXR0ZXJuXCI6XCJPYmplY3RFeHByZXNzaW9uXCIpO307cHAucGFyc2VQcm9wZXJ0eVZhbHVlID0gZnVuY3Rpb24ocHJvcCwgaXNQYXR0ZXJuLCBpc0dlbmVyYXRvciwgc3RhcnRQb3MsIHN0YXJ0TG9jLCByZWZTaG9ydGhhbmREZWZhdWx0UG9zKXtpZih0aGlzLmVhdCh0dC5jb2xvbikpe3Byb3AudmFsdWUgPSBpc1BhdHRlcm4/dGhpcy5wYXJzZU1heWJlRGVmYXVsdCh0aGlzLnN0YXJ0LCB0aGlzLnN0YXJ0TG9jKTp0aGlzLnBhcnNlTWF5YmVBc3NpZ24oZmFsc2UsIHJlZlNob3J0aGFuZERlZmF1bHRQb3MpO3Byb3Aua2luZCA9IFwiaW5pdFwiO31lbHNlIGlmKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2ICYmIHRoaXMudHlwZSA9PT0gdHQucGFyZW5MKXtpZihpc1BhdHRlcm4pdGhpcy51bmV4cGVjdGVkKCk7cHJvcC5raW5kID0gXCJpbml0XCI7cHJvcC5tZXRob2QgPSB0cnVlO3Byb3AudmFsdWUgPSB0aGlzLnBhcnNlTWV0aG9kKGlzR2VuZXJhdG9yKTt9ZWxzZSBpZih0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNSAmJiAhcHJvcC5jb21wdXRlZCAmJiBwcm9wLmtleS50eXBlID09PSBcIklkZW50aWZpZXJcIiAmJiAocHJvcC5rZXkubmFtZSA9PT0gXCJnZXRcIiB8fCBwcm9wLmtleS5uYW1lID09PSBcInNldFwiKSAmJiAodGhpcy50eXBlICE9IHR0LmNvbW1hICYmIHRoaXMudHlwZSAhPSB0dC5icmFjZVIpKXtpZihpc0dlbmVyYXRvciB8fCBpc1BhdHRlcm4pdGhpcy51bmV4cGVjdGVkKCk7cHJvcC5raW5kID0gcHJvcC5rZXkubmFtZTt0aGlzLnBhcnNlUHJvcGVydHlOYW1lKHByb3ApO3Byb3AudmFsdWUgPSB0aGlzLnBhcnNlTWV0aG9kKGZhbHNlKTt9ZWxzZSBpZih0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNiAmJiAhcHJvcC5jb21wdXRlZCAmJiBwcm9wLmtleS50eXBlID09PSBcIklkZW50aWZpZXJcIil7cHJvcC5raW5kID0gXCJpbml0XCI7aWYoaXNQYXR0ZXJuKXtpZih0aGlzLmlzS2V5d29yZChwcm9wLmtleS5uYW1lKSB8fCB0aGlzLnN0cmljdCAmJiAocmVzZXJ2ZWRXb3Jkcy5zdHJpY3RCaW5kKHByb3Aua2V5Lm5hbWUpIHx8IHJlc2VydmVkV29yZHMuc3RyaWN0KHByb3Aua2V5Lm5hbWUpKSB8fCAhdGhpcy5vcHRpb25zLmFsbG93UmVzZXJ2ZWQgJiYgdGhpcy5pc1Jlc2VydmVkV29yZChwcm9wLmtleS5uYW1lKSl0aGlzLnJhaXNlKHByb3Aua2V5LnN0YXJ0LCBcIkJpbmRpbmcgXCIgKyBwcm9wLmtleS5uYW1lKTtwcm9wLnZhbHVlID0gdGhpcy5wYXJzZU1heWJlRGVmYXVsdChzdGFydFBvcywgc3RhcnRMb2MsIHByb3Aua2V5KTt9ZWxzZSBpZih0aGlzLnR5cGUgPT09IHR0LmVxICYmIHJlZlNob3J0aGFuZERlZmF1bHRQb3Mpe2lmKCFyZWZTaG9ydGhhbmREZWZhdWx0UG9zLnN0YXJ0KXJlZlNob3J0aGFuZERlZmF1bHRQb3Muc3RhcnQgPSB0aGlzLnN0YXJ0O3Byb3AudmFsdWUgPSB0aGlzLnBhcnNlTWF5YmVEZWZhdWx0KHN0YXJ0UG9zLCBzdGFydExvYywgcHJvcC5rZXkpO31lbHNlIHtwcm9wLnZhbHVlID0gcHJvcC5rZXk7fXByb3Auc2hvcnRoYW5kID0gdHJ1ZTt9ZWxzZSB0aGlzLnVuZXhwZWN0ZWQoKTt9O3BwLnBhcnNlUHJvcGVydHlOYW1lID0gZnVuY3Rpb24ocHJvcCl7aWYodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYpe2lmKHRoaXMuZWF0KHR0LmJyYWNrZXRMKSl7cHJvcC5jb21wdXRlZCA9IHRydWU7cHJvcC5rZXkgPSB0aGlzLnBhcnNlTWF5YmVBc3NpZ24oKTt0aGlzLmV4cGVjdCh0dC5icmFja2V0Uik7cmV0dXJuIHByb3Aua2V5O31lbHNlIHtwcm9wLmNvbXB1dGVkID0gZmFsc2U7fX1yZXR1cm4gcHJvcC5rZXkgPSB0aGlzLnR5cGUgPT09IHR0Lm51bSB8fCB0aGlzLnR5cGUgPT09IHR0LnN0cmluZz90aGlzLnBhcnNlRXhwckF0b20oKTp0aGlzLnBhcnNlSWRlbnQodHJ1ZSk7fTtwcC5pbml0RnVuY3Rpb24gPSBmdW5jdGlvbihub2RlKXtub2RlLmlkID0gbnVsbDtpZih0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNil7bm9kZS5nZW5lcmF0b3IgPSBmYWxzZTtub2RlLmV4cHJlc3Npb24gPSBmYWxzZTt9fTtwcC5wYXJzZU1ldGhvZCA9IGZ1bmN0aW9uKGlzR2VuZXJhdG9yKXt2YXIgbm9kZT10aGlzLnN0YXJ0Tm9kZSgpO3RoaXMuaW5pdEZ1bmN0aW9uKG5vZGUpO3RoaXMuZXhwZWN0KHR0LnBhcmVuTCk7bm9kZS5wYXJhbXMgPSB0aGlzLnBhcnNlQmluZGluZ0xpc3QodHQucGFyZW5SLCBmYWxzZSwgZmFsc2UpO3ZhciBhbGxvd0V4cHJlc3Npb25Cb2R5PXVuZGVmaW5lZDtpZih0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNil7bm9kZS5nZW5lcmF0b3IgPSBpc0dlbmVyYXRvcjthbGxvd0V4cHJlc3Npb25Cb2R5ID0gdHJ1ZTt9ZWxzZSB7YWxsb3dFeHByZXNzaW9uQm9keSA9IGZhbHNlO310aGlzLnBhcnNlRnVuY3Rpb25Cb2R5KG5vZGUsIGFsbG93RXhwcmVzc2lvbkJvZHkpO3JldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJGdW5jdGlvbkV4cHJlc3Npb25cIik7fTtwcC5wYXJzZUFycm93RXhwcmVzc2lvbiA9IGZ1bmN0aW9uKG5vZGUsIHBhcmFtcyl7dGhpcy5pbml0RnVuY3Rpb24obm9kZSk7bm9kZS5wYXJhbXMgPSB0aGlzLnRvQXNzaWduYWJsZUxpc3QocGFyYW1zLCB0cnVlKTt0aGlzLnBhcnNlRnVuY3Rpb25Cb2R5KG5vZGUsIHRydWUpO3JldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJBcnJvd0Z1bmN0aW9uRXhwcmVzc2lvblwiKTt9O3BwLnBhcnNlRnVuY3Rpb25Cb2R5ID0gZnVuY3Rpb24obm9kZSwgYWxsb3dFeHByZXNzaW9uKXt2YXIgaXNFeHByZXNzaW9uPWFsbG93RXhwcmVzc2lvbiAmJiB0aGlzLnR5cGUgIT09IHR0LmJyYWNlTDtpZihpc0V4cHJlc3Npb24pe25vZGUuYm9keSA9IHRoaXMucGFyc2VNYXliZUFzc2lnbigpO25vZGUuZXhwcmVzc2lvbiA9IHRydWU7fWVsc2Uge3ZhciBvbGRJbkZ1bmM9dGhpcy5pbkZ1bmN0aW9uLCBvbGRJbkdlbj10aGlzLmluR2VuZXJhdG9yLCBvbGRMYWJlbHM9dGhpcy5sYWJlbHM7dGhpcy5pbkZ1bmN0aW9uID0gdHJ1ZTt0aGlzLmluR2VuZXJhdG9yID0gbm9kZS5nZW5lcmF0b3I7dGhpcy5sYWJlbHMgPSBbXTtub2RlLmJvZHkgPSB0aGlzLnBhcnNlQmxvY2sodHJ1ZSk7bm9kZS5leHByZXNzaW9uID0gZmFsc2U7dGhpcy5pbkZ1bmN0aW9uID0gb2xkSW5GdW5jO3RoaXMuaW5HZW5lcmF0b3IgPSBvbGRJbkdlbjt0aGlzLmxhYmVscyA9IG9sZExhYmVsczt9aWYodGhpcy5zdHJpY3QgfHwgIWlzRXhwcmVzc2lvbiAmJiBub2RlLmJvZHkuYm9keS5sZW5ndGggJiYgdGhpcy5pc1VzZVN0cmljdChub2RlLmJvZHkuYm9keVswXSkpe3ZhciBuYW1lSGFzaD17fSwgb2xkU3RyaWN0PXRoaXMuc3RyaWN0O3RoaXMuc3RyaWN0ID0gdHJ1ZTtpZihub2RlLmlkKXRoaXMuY2hlY2tMVmFsKG5vZGUuaWQsIHRydWUpO2Zvcih2YXIgaT0wOyBpIDwgbm9kZS5wYXJhbXMubGVuZ3RoOyBpKyspIHt0aGlzLmNoZWNrTFZhbChub2RlLnBhcmFtc1tpXSwgdHJ1ZSwgbmFtZUhhc2gpO310aGlzLnN0cmljdCA9IG9sZFN0cmljdDt9fTtwcC5wYXJzZUV4cHJMaXN0ID0gZnVuY3Rpb24oY2xvc2UsIGFsbG93VHJhaWxpbmdDb21tYSwgYWxsb3dFbXB0eSwgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcyl7dmFyIGVsdHM9W10sIGZpcnN0PXRydWU7d2hpbGUoIXRoaXMuZWF0KGNsb3NlKSkge2lmKCFmaXJzdCl7dGhpcy5leHBlY3QodHQuY29tbWEpO2lmKGFsbG93VHJhaWxpbmdDb21tYSAmJiB0aGlzLmFmdGVyVHJhaWxpbmdDb21tYShjbG9zZSkpYnJlYWs7fWVsc2UgZmlyc3QgPSBmYWxzZTtpZihhbGxvd0VtcHR5ICYmIHRoaXMudHlwZSA9PT0gdHQuY29tbWEpe2VsdHMucHVzaChudWxsKTt9ZWxzZSB7aWYodGhpcy50eXBlID09PSB0dC5lbGxpcHNpcyllbHRzLnB1c2godGhpcy5wYXJzZVNwcmVhZChyZWZTaG9ydGhhbmREZWZhdWx0UG9zKSk7ZWxzZSBlbHRzLnB1c2godGhpcy5wYXJzZU1heWJlQXNzaWduKGZhbHNlLCByZWZTaG9ydGhhbmREZWZhdWx0UG9zKSk7fX1yZXR1cm4gZWx0czt9O3BwLnBhcnNlSWRlbnQgPSBmdW5jdGlvbihsaWJlcmFsKXt2YXIgbm9kZT10aGlzLnN0YXJ0Tm9kZSgpO2lmKGxpYmVyYWwgJiYgdGhpcy5vcHRpb25zLmFsbG93UmVzZXJ2ZWQgPT0gXCJuZXZlclwiKWxpYmVyYWwgPSBmYWxzZTtpZih0aGlzLnR5cGUgPT09IHR0Lm5hbWUpe2lmKCFsaWJlcmFsICYmICghdGhpcy5vcHRpb25zLmFsbG93UmVzZXJ2ZWQgJiYgdGhpcy5pc1Jlc2VydmVkV29yZCh0aGlzLnZhbHVlKSB8fCB0aGlzLnN0cmljdCAmJiByZXNlcnZlZFdvcmRzLnN0cmljdCh0aGlzLnZhbHVlKSAmJiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYgfHwgdGhpcy5pbnB1dC5zbGljZSh0aGlzLnN0YXJ0LCB0aGlzLmVuZCkuaW5kZXhPZihcIlxcXFxcIikgPT0gLTEpKSl0aGlzLnJhaXNlKHRoaXMuc3RhcnQsIFwiVGhlIGtleXdvcmQgJ1wiICsgdGhpcy52YWx1ZSArIFwiJyBpcyByZXNlcnZlZFwiKTtub2RlLm5hbWUgPSB0aGlzLnZhbHVlO31lbHNlIGlmKGxpYmVyYWwgJiYgdGhpcy50eXBlLmtleXdvcmQpe25vZGUubmFtZSA9IHRoaXMudHlwZS5rZXl3b3JkO31lbHNlIHt0aGlzLnVuZXhwZWN0ZWQoKTt9dGhpcy5uZXh0KCk7cmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIklkZW50aWZpZXJcIik7fTtwcC5wYXJzZVlpZWxkID0gZnVuY3Rpb24oKXt2YXIgbm9kZT10aGlzLnN0YXJ0Tm9kZSgpO3RoaXMubmV4dCgpO2lmKHRoaXMudHlwZSA9PSB0dC5zZW1pIHx8IHRoaXMuY2FuSW5zZXJ0U2VtaWNvbG9uKCkgfHwgdGhpcy50eXBlICE9IHR0LnN0YXIgJiYgIXRoaXMudHlwZS5zdGFydHNFeHByKXtub2RlLmRlbGVnYXRlID0gZmFsc2U7bm9kZS5hcmd1bWVudCA9IG51bGw7fWVsc2Uge25vZGUuZGVsZWdhdGUgPSB0aGlzLmVhdCh0dC5zdGFyKTtub2RlLmFyZ3VtZW50ID0gdGhpcy5wYXJzZU1heWJlQXNzaWduKCk7fXJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJZaWVsZEV4cHJlc3Npb25cIik7fTtwcC5wYXJzZUNvbXByZWhlbnNpb24gPSBmdW5jdGlvbihub2RlLCBpc0dlbmVyYXRvcil7bm9kZS5ibG9ja3MgPSBbXTt3aGlsZSh0aGlzLnR5cGUgPT09IHR0Ll9mb3IpIHt2YXIgYmxvY2s9dGhpcy5zdGFydE5vZGUoKTt0aGlzLm5leHQoKTt0aGlzLmV4cGVjdCh0dC5wYXJlbkwpO2Jsb2NrLmxlZnQgPSB0aGlzLnBhcnNlQmluZGluZ0F0b20oKTt0aGlzLmNoZWNrTFZhbChibG9jay5sZWZ0LCB0cnVlKTt0aGlzLmV4cGVjdENvbnRleHR1YWwoXCJvZlwiKTtibG9jay5yaWdodCA9IHRoaXMucGFyc2VFeHByZXNzaW9uKCk7dGhpcy5leHBlY3QodHQucGFyZW5SKTtub2RlLmJsb2Nrcy5wdXNoKHRoaXMuZmluaXNoTm9kZShibG9jaywgXCJDb21wcmVoZW5zaW9uQmxvY2tcIikpO31ub2RlLmZpbHRlciA9IHRoaXMuZWF0KHR0Ll9pZik/dGhpcy5wYXJzZVBhcmVuRXhwcmVzc2lvbigpOm51bGw7bm9kZS5ib2R5ID0gdGhpcy5wYXJzZUV4cHJlc3Npb24oKTt0aGlzLmV4cGVjdChpc0dlbmVyYXRvcj90dC5wYXJlblI6dHQuYnJhY2tldFIpO25vZGUuZ2VuZXJhdG9yID0gaXNHZW5lcmF0b3I7cmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkNvbXByZWhlbnNpb25FeHByZXNzaW9uXCIpO307fSwge1wiLi9pZGVudGlmaWVyXCI6NywgXCIuL3N0YXRlXCI6MTMsIFwiLi90b2tlbnR5cGVcIjoxNywgXCIuL3V0aWxcIjoxOH1dLCA3OltmdW5jdGlvbihfZGVyZXFfLCBtb2R1bGUsIGV4cG9ydHMpe1widXNlIHN0cmljdFwiO2V4cG9ydHMuaXNJZGVudGlmaWVyU3RhcnQgPSBpc0lkZW50aWZpZXJTdGFydDtleHBvcnRzLmlzSWRlbnRpZmllckNoYXIgPSBpc0lkZW50aWZpZXJDaGFyO2V4cG9ydHMuX19lc01vZHVsZSA9IHRydWU7ZnVuY3Rpb24gbWFrZVByZWRpY2F0ZSh3b3Jkcyl7d29yZHMgPSB3b3Jkcy5zcGxpdChcIiBcIik7dmFyIGY9XCJcIiwgY2F0cz1bXTtvdXQ6IGZvcih2YXIgaT0wOyBpIDwgd29yZHMubGVuZ3RoOyArK2kpIHtmb3IodmFyIGo9MDsgaiA8IGNhdHMubGVuZ3RoOyArK2opIHtpZihjYXRzW2pdWzBdLmxlbmd0aCA9PSB3b3Jkc1tpXS5sZW5ndGgpe2NhdHNbal0ucHVzaCh3b3Jkc1tpXSk7Y29udGludWUgb3V0O319Y2F0cy5wdXNoKFt3b3Jkc1tpXV0pO31mdW5jdGlvbiBjb21wYXJlVG8oYXJyKXtpZihhcnIubGVuZ3RoID09IDEpe3JldHVybiBmICs9IFwicmV0dXJuIHN0ciA9PT0gXCIgKyBKU09OLnN0cmluZ2lmeShhcnJbMF0pICsgXCI7XCI7fWYgKz0gXCJzd2l0Y2goc3RyKXtcIjtmb3IodmFyIGk9MDsgaSA8IGFyci5sZW5ndGg7ICsraSkge2YgKz0gXCJjYXNlIFwiICsgSlNPTi5zdHJpbmdpZnkoYXJyW2ldKSArIFwiOlwiO31mICs9IFwicmV0dXJuIHRydWV9cmV0dXJuIGZhbHNlO1wiO31pZihjYXRzLmxlbmd0aCA+IDMpe2NhdHMuc29ydChmdW5jdGlvbihhLCBiKXtyZXR1cm4gYi5sZW5ndGggLSBhLmxlbmd0aDt9KTtmICs9IFwic3dpdGNoKHN0ci5sZW5ndGgpe1wiO2Zvcih2YXIgaT0wOyBpIDwgY2F0cy5sZW5ndGg7ICsraSkge3ZhciBjYXQ9Y2F0c1tpXTtmICs9IFwiY2FzZSBcIiArIGNhdFswXS5sZW5ndGggKyBcIjpcIjtjb21wYXJlVG8oY2F0KTt9ZiArPSBcIn1cIjt9ZWxzZSB7Y29tcGFyZVRvKHdvcmRzKTt9cmV0dXJuIG5ldyBGdW5jdGlvbihcInN0clwiLCBmKTt9dmFyIHJlc2VydmVkV29yZHM9ezM6bWFrZVByZWRpY2F0ZShcImFic3RyYWN0IGJvb2xlYW4gYnl0ZSBjaGFyIGNsYXNzIGRvdWJsZSBlbnVtIGV4cG9ydCBleHRlbmRzIGZpbmFsIGZsb2F0IGdvdG8gaW1wbGVtZW50cyBpbXBvcnQgaW50IGludGVyZmFjZSBsb25nIG5hdGl2ZSBwYWNrYWdlIHByaXZhdGUgcHJvdGVjdGVkIHB1YmxpYyBzaG9ydCBzdGF0aWMgc3VwZXIgc3luY2hyb25pemVkIHRocm93cyB0cmFuc2llbnQgdm9sYXRpbGVcIiksIDU6bWFrZVByZWRpY2F0ZShcImNsYXNzIGVudW0gZXh0ZW5kcyBzdXBlciBjb25zdCBleHBvcnQgaW1wb3J0XCIpLCA2Om1ha2VQcmVkaWNhdGUoXCJlbnVtIGF3YWl0XCIpLCBzdHJpY3Q6bWFrZVByZWRpY2F0ZShcImltcGxlbWVudHMgaW50ZXJmYWNlIGxldCBwYWNrYWdlIHByaXZhdGUgcHJvdGVjdGVkIHB1YmxpYyBzdGF0aWMgeWllbGRcIiksIHN0cmljdEJpbmQ6bWFrZVByZWRpY2F0ZShcImV2YWwgYXJndW1lbnRzXCIpfTtleHBvcnRzLnJlc2VydmVkV29yZHMgPSByZXNlcnZlZFdvcmRzO3ZhciBlY21hNUFuZExlc3NLZXl3b3Jkcz1cImJyZWFrIGNhc2UgY2F0Y2ggY29udGludWUgZGVidWdnZXIgZGVmYXVsdCBkbyBlbHNlIGZpbmFsbHkgZm9yIGZ1bmN0aW9uIGlmIHJldHVybiBzd2l0Y2ggdGhyb3cgdHJ5IHZhciB3aGlsZSB3aXRoIG51bGwgdHJ1ZSBmYWxzZSBpbnN0YW5jZW9mIHR5cGVvZiB2b2lkIGRlbGV0ZSBuZXcgaW4gdGhpc1wiO3ZhciBrZXl3b3Jkcz17NTptYWtlUHJlZGljYXRlKGVjbWE1QW5kTGVzc0tleXdvcmRzKSwgNjptYWtlUHJlZGljYXRlKGVjbWE1QW5kTGVzc0tleXdvcmRzICsgXCIgbGV0IGNvbnN0IGNsYXNzIGV4dGVuZHMgZXhwb3J0IGltcG9ydCB5aWVsZCBzdXBlclwiKX07ZXhwb3J0cy5rZXl3b3JkcyA9IGtleXdvcmRzO3ZhciBub25BU0NJSWlkZW50aWZpZXJTdGFydENoYXJzPVwiwqrCtcK6w4Atw5bDmC3DtsO4LcuBy4Yty5HLoC3LpMusy67NsC3NtM22zbfNui3Nvc2/zobOiC3Ois6Mzo4tzqHOoy3Ptc+3LdKB0oot1K/UsS3VltWZ1aEt1ofXkC3XqtewLdey2KAt2YrZrtmv2bEt25Pbldul26bbrtuv27ot27zbv9yQ3JIt3K/djS3epd6x34ot36rftN+137rgoIAt4KCV4KCa4KCk4KCo4KGALeChmOCioC3gorLgpIQt4KS54KS94KWQ4KWYLeCloeClsS3gpoDgpoUt4KaM4KaP4KaQ4KaTLeCmqOCmqi3gprDgprLgprYt4Ka54Ka94KeO4Kec4Ked4KefLeCnoeCnsOCnseCohS3gqIrgqI/gqJDgqJMt4Kio4KiqLeCosOCosuCos+CoteCotuCouOCoueCpmS3gqZzgqZ7gqbIt4Km04KqFLeCqjeCqjy3gqpHgqpMt4Kqo4KqqLeCqsOCqsuCqs+CqtS3gqrngqr3gq5Dgq6Dgq6HgrIUt4KyM4KyP4KyQ4KyTLeCsqOCsqi3grLDgrLLgrLPgrLUt4Ky54Ky94K2c4K2d4K2fLeCtoeCtseCug+CuhS3grorgro4t4K6Q4K6SLeCuleCumeCumuCunOCunuCun+Cuo+CupOCuqC3grqrgrq4t4K654K+Q4LCFLeCwjOCwji3gsJDgsJIt4LCo4LCqLeCwueCwveCxmOCxmeCxoOCxoeCyhS3gsozgso4t4LKQ4LKSLeCyqOCyqi3gsrPgsrUt4LK54LK94LOe4LOg4LOh4LOx4LOy4LSFLeC0jOC0ji3gtJDgtJIt4LS64LS94LWO4LWg4LWh4LW6LeC1v+C2hS3gtpbgtpot4Lax4LazLeC2u+C2veC3gC3gt4bguIEt4Liw4Liy4Liz4LmALeC5huC6geC6guC6hOC6h+C6iOC6iuC6jeC6lC3gupfgupkt4Lqf4LqhLeC6o+C6peC6p+C6quC6q+C6rS3gurDgurLgurPgur3gu4At4LuE4LuG4LucLeC7n+C8gOC9gC3gvYfgvYkt4L2s4L6ILeC+jOGAgC3hgKrhgL/hgZAt4YGV4YGaLeGBneGBoeGBpeGBpuGBri3hgbDhgbUt4YKB4YKO4YKgLeGDheGDh+GDjeGDkC3hg7rhg7wt4YmI4YmKLeGJjeGJkC3hiZbhiZjhiZot4Ymd4YmgLeGKiOGKii3hio3hipAt4Yqw4YqyLeGKteGKuC3hir7hi4Dhi4It4YuF4YuILeGLluGLmC3hjJDhjJIt4YyV4YyYLeGNmuGOgC3hjo/hjqAt4Y+04ZCBLeGZrOGZry3hmb/hmoEt4Zqa4ZqgLeGbquGbri3hm7jhnIAt4ZyM4ZyOLeGckeGcoC3hnLHhnYAt4Z2R4Z2gLeGdrOGdri3hnbDhnoAt4Z6z4Z+X4Z+c4aCgLeGht+GigC3hoqjhoqrhorAt4aO14aSALeGknuGlkC3hpa3hpbAt4aW04aaALeGmq+GngS3hp4fhqIAt4aiW4aigLeGplOGqp+GshS3hrLPhrYUt4a2L4a6DLeGuoOGuruGur+Guui3hr6XhsIAt4bCj4bGNLeGxj+Gxmi3hsb3hs6kt4bOs4bOuLeGzseGzteGztuG0gC3htr/huIAt4byV4byYLeG8neG8oC3hvYXhvYgt4b2N4b2QLeG9l+G9meG9m+G9neG9ny3hvb3hvoAt4b604b62LeG+vOG+vuG/gi3hv4Thv4Yt4b+M4b+QLeG/k+G/li3hv5vhv6At4b+s4b+yLeG/tOG/ti3hv7zigbHigb/igpAt4oKc4oSC4oSH4oSKLeKEk+KEleKEmC3ihJ3ihKTihKbihKjihKot4oS54oS8LeKEv+KFhS3ihYnihY7ihaAt4oaI4rCALeKwruKwsC3isZ7isaAt4rOk4rOrLeKzruKzsuKzs+K0gC3itKXitKfitK3itLAt4rWn4rWv4raALeK2luK2oC3itqbitqgt4rau4rawLeK2tuK2uC3itr7it4At4reG4reILeK3juK3kC3it5bit5gt4ree44CFLeOAh+OAoS3jgKnjgLEt44C144C4LeOAvOOBgS3jgpbjgpst44Kf44KhLeODuuODvC3jg7/jhIUt44St44SxLeOGjuOGoC3jhrrjh7At44e/45CALeS2teS4gC3pv4zqgIAt6pKM6pOQLeqTveqUgC3qmIzqmJAt6pif6piq6pir6pmALeqZruqZvy3qmp3qmqAt6puv6pyXLeqcn+qcoi3qnojqnost6p6O6p6QLeqereqesOqeseqfty3qoIHqoIMt6qCF6qCHLeqgiuqgjC3qoKLqoYAt6qGz6qKCLeqis+qjsi3qo7fqo7vqpIot6qSl6qSwLeqlhuqloC3qpbzqpoQt6qay6qeP6qegLeqnpOqnpi3qp6/qp7ot6qe+6qiALeqoqOqpgC3qqYLqqYQt6qmL6qmgLeqptuqpuuqpvi3qqq/qqrHqqrXqqrbqqrkt6qq96quA6quC6qubLeqrneqroC3qq6rqq7It6qu06qyBLeqshuqsiS3qrI7qrJEt6qyW6qygLeqspuqsqC3qrK7qrLAt6q2a6q2cLeqtn+qtpOqtpeqvgC3qr6LqsIAt7Z6j7Z6wLe2fhu2fiy3tn7vvpIAt76mt76mwLe+rme+sgC3vrIbvrJMt76yX76yd76yfLe+sqO+sqi3vrLbvrLgt76y876y+762A762B762D762E762GLe+use+vky3vtL3vtZAt77aP77aSLe+3h++3sC3vt7vvubAt77m077m2Le+7vO+8oS3vvLrvvYEt772a772mLe++vu+/gi3vv4fvv4ot77+P77+SLe+/l++/mi3vv5xcIjt2YXIgbm9uQVNDSUlpZGVudGlmaWVyQ2hhcnM9XCLigIzigI3Ct8yALc2vzofSgy3Sh9aRLda91r/XgdeC14TXhdeH2JAt2JrZiy3Zqdmw25Yt25zbny3bpNun26jbqi3brduwLdu53JHcsC3dit6mLd6w34At34nfqy3fs+Cgli3goJngoJst4KCj4KClLeCgp+CgqS3goK3goZkt4KGb4KOkLeCkg+Ckui3gpLzgpL4t4KWP4KWRLeCll+ClouClo+Clpi3gpa/gpoEt4KaD4Ka84Ka+LeCnhOCnh+CniOCniy3gp43gp5fgp6Lgp6Pgp6Yt4Kev4KiBLeCog+CovOCovi3gqYLgqYfgqYjgqYst4KmN4KmR4KmmLeCpseCpteCqgS3gqoPgqrzgqr4t4KuF4KuHLeCrieCriy3gq43gq6Lgq6Pgq6Yt4Kuv4KyBLeCsg+CsvOCsvi3grYTgrYfgrYjgrYst4K2N4K2W4K2X4K2i4K2j4K2mLeCtr+CuguCuvi3gr4Lgr4Yt4K+I4K+KLeCvjeCvl+Cvpi3gr6/gsIAt4LCD4LC+LeCxhOCxhi3gsYjgsYot4LGN4LGV4LGW4LGi4LGj4LGmLeCxr+CygS3gsoPgsrzgsr4t4LOE4LOGLeCziOCzii3gs43gs5Xgs5bgs6Lgs6Pgs6Yt4LOv4LSBLeC0g+C0vi3gtYTgtYYt4LWI4LWKLeC1jeC1l+C1ouC1o+C1pi3gta/gtoLgtoPgt4rgt48t4LeU4LeW4LeYLeC3n+C3pi3gt6/gt7Lgt7PguLHguLQt4Li64LmHLeC5juC5kC3guZngurHgurQt4Lq54Lq74Lq84LuILeC7jeC7kC3gu5ngvJjgvJngvKAt4Lyp4Ly14Ly34Ly54Ly+4Ly/4L2xLeC+hOC+huC+h+C+jS3gvpfgvpkt4L684L+G4YCrLeGAvuGBgC3hgYnhgZYt4YGZ4YGeLeGBoOGBoi3hgaThgact4YGt4YGxLeGBtOGCgi3hgo3hgo8t4YKd4Y2dLeGNn+GNqS3hjbHhnJIt4ZyU4ZyyLeGctOGdkuGdk+GdsuGds+GetC3hn5Phn53hn6At4Z+p4aCLLeGgjeGgkC3hoJnhoqnhpKAt4aSr4aSwLeGku+Glhi3hpY/hprAt4aeA4aeI4aeJ4aeQLeGnmuGoly3hqJvhqZUt4ame4amgLeGpvOGpvy3hqonhqpAt4aqZ4aqwLeGqveGsgC3hrIThrLQt4a2E4a2QLeGtmeGtqy3hrbPhroAt4a6C4a6hLeGureGusC3hrrnhr6Yt4a+z4bCkLeGwt+GxgC3hsYnhsZAt4bGZ4bOQLeGzkuGzlC3hs6jhs63hs7It4bO04bO44bO54beALeG3teG3vC3ht7/igL/igYDigZTig5At4oOc4oOh4oOlLeKDsOKzry3is7Hitb/it6At4re/44CqLeOAr+OCmeOCmuqYoC3qmKnqma/qmbQt6pm96pqf6puw6pux6qCC6qCG6qCL6qCjLeqgp+qigOqigeqitC3qo4Tqo5At6qOZ6qOgLeqjseqkgC3qpInqpKYt6qSt6qWHLeqlk+qmgC3qpoPqprMt6qeA6qeQLeqnmeqnpeqnsC3qp7nqqKkt6qi26qmD6qmM6qmN6qmQLeqpmeqpuy3qqb3qqrDqqrIt6qq06qq36qq46qq+6qq/6quB6qurLeqrr+qrteqrtuqvoy3qr6rqr6zqr63qr7At6q+576ye77iALe+4j++4oC3vuK3vuLPvuLTvuY0t77mP77yQLe+8me+8v1wiO3ZhciBub25BU0NJSWlkZW50aWZpZXJTdGFydD1uZXcgUmVnRXhwKFwiW1wiICsgbm9uQVNDSUlpZGVudGlmaWVyU3RhcnRDaGFycyArIFwiXVwiKTt2YXIgbm9uQVNDSUlpZGVudGlmaWVyPW5ldyBSZWdFeHAoXCJbXCIgKyBub25BU0NJSWlkZW50aWZpZXJTdGFydENoYXJzICsgbm9uQVNDSUlpZGVudGlmaWVyQ2hhcnMgKyBcIl1cIik7bm9uQVNDSUlpZGVudGlmaWVyU3RhcnRDaGFycyA9IG5vbkFTQ0lJaWRlbnRpZmllckNoYXJzID0gbnVsbDt2YXIgYXN0cmFsSWRlbnRpZmllclN0YXJ0Q29kZXM9WzAsIDExLCAyLCAyNSwgMiwgMTgsIDIsIDEsIDIsIDE0LCAzLCAxMywgMzUsIDEyMiwgNzAsIDUyLCAyNjgsIDI4LCA0LCA0OCwgNDgsIDMxLCAxNywgMjYsIDYsIDM3LCAxMSwgMjksIDMsIDM1LCA1LCA3LCAyLCA0LCA0MywgMTU3LCA5OSwgMzksIDksIDUxLCAxNTcsIDMxMCwgMTAsIDIxLCAxMSwgNywgMTUzLCA1LCAzLCAwLCAyLCA0MywgMiwgMSwgNCwgMCwgMywgMjIsIDExLCAyMiwgMTAsIDMwLCA5OCwgMjEsIDExLCAyNSwgNzEsIDU1LCA3LCAxLCA2NSwgMCwgMTYsIDMsIDIsIDIsIDIsIDI2LCA0NSwgMjgsIDQsIDI4LCAzNiwgNywgMiwgMjcsIDI4LCA1MywgMTEsIDIxLCAxMSwgMTgsIDE0LCAxNywgMTExLCA3MiwgOTU1LCA1MiwgNzYsIDQ0LCAzMywgMjQsIDI3LCAzNSwgNDIsIDM0LCA0LCAwLCAxMywgNDcsIDE1LCAzLCAyMiwgMCwgMzgsIDE3LCAyLCAyNCwgMTMzLCA0NiwgMzksIDcsIDMsIDEsIDMsIDIxLCAyLCA2LCAyLCAxLCAyLCA0LCA0LCAwLCAzMiwgNCwgMjg3LCA0NywgMjEsIDEsIDIsIDAsIDE4NSwgNDYsIDgyLCA0NywgMjEsIDAsIDYwLCA0MiwgNTAyLCA2MywgMzIsIDAsIDQ0OSwgNTYsIDEyODgsIDkyMCwgMTA0LCAxMTAsIDI5NjIsIDEwNzAsIDEzMjY2LCA1NjgsIDgsIDMwLCAxMTQsIDI5LCAxOSwgNDcsIDE3LCAzLCAzMiwgMjAsIDYsIDE4LCA4ODEsIDY4LCAxMiwgMCwgNjcsIDEyLCAxNjQ4MSwgMSwgMzA3MSwgMTA2LCA2LCAxMiwgNCwgOCwgOCwgOSwgNTk5MSwgODQsIDIsIDcwLCAyLCAxLCAzLCAwLCAzLCAxLCAzLCAzLCAyLCAxMSwgMiwgMCwgMiwgNiwgMiwgNjQsIDIsIDMsIDMsIDcsIDIsIDYsIDIsIDI3LCAyLCAzLCAyLCA0LCAyLCAwLCA0LCA2LCAyLCAzMzksIDMsIDI0LCAyLCAyNCwgMiwgMzAsIDIsIDI0LCAyLCAzMCwgMiwgMjQsIDIsIDMwLCAyLCAyNCwgMiwgMzAsIDIsIDI0LCAyLCA3LCA0MTQ5LCAxOTYsIDEzNDAsIDMsIDIsIDI2LCAyLCAxLCAyLCAwLCAzLCAwLCAyLCA5LCAyLCAzLCAyLCAwLCAyLCAwLCA3LCAwLCA1LCAwLCAyLCAwLCAyLCAwLCAyLCAyLCAyLCAxLCAyLCAwLCAzLCAwLCAyLCAwLCAyLCAwLCAyLCAwLCAyLCAwLCAyLCAxLCAyLCAwLCAzLCAzLCAyLCA2LCAyLCAzLCAyLCAzLCAyLCAwLCAyLCA5LCAyLCAxNiwgNiwgMiwgMiwgNCwgMiwgMTYsIDQ0MjEsIDQyNzEwLCA0MiwgNDE0OCwgMTIsIDIyMSwgMTYzNTUsIDU0MV07dmFyIGFzdHJhbElkZW50aWZpZXJDb2Rlcz1bNTA5LCAwLCAyMjcsIDAsIDE1MCwgNCwgMjk0LCA5LCAxMzY4LCAyLCAyLCAxLCA2LCAzLCA0MSwgMiwgNSwgMCwgMTY2LCAxLCAxMzA2LCAyLCA1NCwgMTQsIDMyLCA5LCAxNiwgMywgNDYsIDEwLCA1NCwgOSwgNywgMiwgMzcsIDEzLCAyLCA5LCA1MiwgMCwgMTMsIDIsIDQ5LCAxMywgMTYsIDksIDgzLCAxMSwgMTY4LCAxMSwgNiwgOSwgOCwgMiwgNTcsIDAsIDIsIDYsIDMsIDEsIDMsIDIsIDEwLCAwLCAxMSwgMSwgMywgNiwgNCwgNCwgMzE2LCAxOSwgMTMsIDksIDIxNCwgNiwgMywgOCwgMTEyLCAxNiwgMTYsIDksIDgyLCAxMiwgOSwgOSwgNTM1LCA5LCAyMDg1NSwgOSwgMTM1LCA0LCA2MCwgNiwgMjYsIDksIDEwMTYsIDQ1LCAxNywgMywgMTk3MjMsIDEsIDUzMTksIDQsIDQsIDUsIDksIDcsIDMsIDYsIDMxLCAzLCAxNDksIDIsIDE0MTgsIDQ5LCA0MzA1LCA2LCA3OTI2MTgsIDIzOV07ZnVuY3Rpb24gaXNJbkFzdHJhbFNldChjb2RlLCBzZXQpe3ZhciBwb3M9NjU1MzY7Zm9yKHZhciBpPTA7IGkgPCBzZXQubGVuZ3RoOyBpICs9IDIpIHtwb3MgKz0gc2V0W2ldO2lmKHBvcyA+IGNvZGUpe3JldHVybiBmYWxzZTt9cG9zICs9IHNldFtpICsgMV07aWYocG9zID49IGNvZGUpe3JldHVybiB0cnVlO319fWZ1bmN0aW9uIGlzSWRlbnRpZmllclN0YXJ0KGNvZGUsIGFzdHJhbCl7aWYoY29kZSA8IDY1KXtyZXR1cm4gY29kZSA9PT0gMzY7fWlmKGNvZGUgPCA5MSl7cmV0dXJuIHRydWU7fWlmKGNvZGUgPCA5Nyl7cmV0dXJuIGNvZGUgPT09IDk1O31pZihjb2RlIDwgMTIzKXtyZXR1cm4gdHJ1ZTt9aWYoY29kZSA8PSA2NTUzNSl7cmV0dXJuIGNvZGUgPj0gMTcwICYmIG5vbkFTQ0lJaWRlbnRpZmllclN0YXJ0LnRlc3QoU3RyaW5nLmZyb21DaGFyQ29kZShjb2RlKSk7fWlmKGFzdHJhbCA9PT0gZmFsc2Upe3JldHVybiBmYWxzZTt9cmV0dXJuIGlzSW5Bc3RyYWxTZXQoY29kZSwgYXN0cmFsSWRlbnRpZmllclN0YXJ0Q29kZXMpO31mdW5jdGlvbiBpc0lkZW50aWZpZXJDaGFyKGNvZGUsIGFzdHJhbCl7aWYoY29kZSA8IDQ4KXtyZXR1cm4gY29kZSA9PT0gMzY7fWlmKGNvZGUgPCA1OCl7cmV0dXJuIHRydWU7fWlmKGNvZGUgPCA2NSl7cmV0dXJuIGZhbHNlO31pZihjb2RlIDwgOTEpe3JldHVybiB0cnVlO31pZihjb2RlIDwgOTcpe3JldHVybiBjb2RlID09PSA5NTt9aWYoY29kZSA8IDEyMyl7cmV0dXJuIHRydWU7fWlmKGNvZGUgPD0gNjU1MzUpe3JldHVybiBjb2RlID49IDE3MCAmJiBub25BU0NJSWlkZW50aWZpZXIudGVzdChTdHJpbmcuZnJvbUNoYXJDb2RlKGNvZGUpKTt9aWYoYXN0cmFsID09PSBmYWxzZSl7cmV0dXJuIGZhbHNlO31yZXR1cm4gaXNJbkFzdHJhbFNldChjb2RlLCBhc3RyYWxJZGVudGlmaWVyU3RhcnRDb2RlcykgfHwgaXNJbkFzdHJhbFNldChjb2RlLCBhc3RyYWxJZGVudGlmaWVyQ29kZXMpO319LCB7fV0sIDg6W2Z1bmN0aW9uKF9kZXJlcV8sIG1vZHVsZSwgZXhwb3J0cyl7XCJ1c2Ugc3RyaWN0XCI7dmFyIF9jbGFzc0NhbGxDaGVjaz1mdW5jdGlvbiBfY2xhc3NDYWxsQ2hlY2soaW5zdGFuY2UsIENvbnN0cnVjdG9yKXtpZighKGluc3RhbmNlIGluc3RhbmNlb2YgQ29uc3RydWN0b3IpKXt0aHJvdyBuZXcgVHlwZUVycm9yKFwiQ2Fubm90IGNhbGwgYSBjbGFzcyBhcyBhIGZ1bmN0aW9uXCIpO319O2V4cG9ydHMuZ2V0TGluZUluZm8gPSBnZXRMaW5lSW5mbztleHBvcnRzLl9fZXNNb2R1bGUgPSB0cnVlO3ZhciBQYXJzZXI9X2RlcmVxXyhcIi4vc3RhdGVcIikuUGFyc2VyO3ZhciBsaW5lQnJlYWtHPV9kZXJlcV8oXCIuL3doaXRlc3BhY2VcIikubGluZUJyZWFrRzt2YXIgZGVwcmVjYXRlPV9kZXJlcV8oXCJ1dGlsXCIpLmRlcHJlY2F0ZTt2YXIgUG9zaXRpb249ZXhwb3J0cy5Qb3NpdGlvbiA9IChmdW5jdGlvbigpe2Z1bmN0aW9uIFBvc2l0aW9uKGxpbmUsIGNvbCl7X2NsYXNzQ2FsbENoZWNrKHRoaXMsIFBvc2l0aW9uKTt0aGlzLmxpbmUgPSBsaW5lO3RoaXMuY29sdW1uID0gY29sO31Qb3NpdGlvbi5wcm90b3R5cGUub2Zmc2V0ID0gZnVuY3Rpb24gb2Zmc2V0KG4pe3JldHVybiBuZXcgUG9zaXRpb24odGhpcy5saW5lLCB0aGlzLmNvbHVtbiArIG4pO307cmV0dXJuIFBvc2l0aW9uO30pKCk7dmFyIFNvdXJjZUxvY2F0aW9uPWV4cG9ydHMuU291cmNlTG9jYXRpb24gPSBmdW5jdGlvbiBTb3VyY2VMb2NhdGlvbihwLCBzdGFydCwgZW5kKXtfY2xhc3NDYWxsQ2hlY2sodGhpcywgU291cmNlTG9jYXRpb24pO3RoaXMuc3RhcnQgPSBzdGFydDt0aGlzLmVuZCA9IGVuZDtpZihwLnNvdXJjZUZpbGUgIT09IG51bGwpdGhpcy5zb3VyY2UgPSBwLnNvdXJjZUZpbGU7fTtmdW5jdGlvbiBnZXRMaW5lSW5mbyhpbnB1dCwgb2Zmc2V0KXtmb3IodmFyIGxpbmU9MSwgY3VyPTA7Oykge2xpbmVCcmVha0cubGFzdEluZGV4ID0gY3VyO3ZhciBtYXRjaD1saW5lQnJlYWtHLmV4ZWMoaW5wdXQpO2lmKG1hdGNoICYmIG1hdGNoLmluZGV4IDwgb2Zmc2V0KXsrK2xpbmU7Y3VyID0gbWF0Y2guaW5kZXggKyBtYXRjaFswXS5sZW5ndGg7fWVsc2Uge3JldHVybiBuZXcgUG9zaXRpb24obGluZSwgb2Zmc2V0IC0gY3VyKTt9fX12YXIgcHA9UGFyc2VyLnByb3RvdHlwZTtwcC5yYWlzZSA9IGZ1bmN0aW9uKHBvcywgbWVzc2FnZSl7dmFyIGxvYz1nZXRMaW5lSW5mbyh0aGlzLmlucHV0LCBwb3MpO21lc3NhZ2UgKz0gXCIgKFwiICsgbG9jLmxpbmUgKyBcIjpcIiArIGxvYy5jb2x1bW4gKyBcIilcIjt2YXIgZXJyPW5ldyBTeW50YXhFcnJvcihtZXNzYWdlKTtlcnIucG9zID0gcG9zO2Vyci5sb2MgPSBsb2M7ZXJyLnJhaXNlZEF0ID0gdGhpcy5wb3M7dGhyb3cgZXJyO307cHAuY3VyUG9zaXRpb24gPSBmdW5jdGlvbigpe3JldHVybiBuZXcgUG9zaXRpb24odGhpcy5jdXJMaW5lLCB0aGlzLnBvcyAtIHRoaXMubGluZVN0YXJ0KTt9O3BwLm1hcmtQb3NpdGlvbiA9IGZ1bmN0aW9uKCl7cmV0dXJuIHRoaXMub3B0aW9ucy5sb2NhdGlvbnM/W3RoaXMuc3RhcnQsIHRoaXMuc3RhcnRMb2NdOnRoaXMuc3RhcnQ7fTt9LCB7XCIuL3N0YXRlXCI6MTMsIFwiLi93aGl0ZXNwYWNlXCI6MTksIHV0aWw6NX1dLCA5OltmdW5jdGlvbihfZGVyZXFfLCBtb2R1bGUsIGV4cG9ydHMpe1widXNlIHN0cmljdFwiO3ZhciB0dD1fZGVyZXFfKFwiLi90b2tlbnR5cGVcIikudHlwZXM7dmFyIFBhcnNlcj1fZGVyZXFfKFwiLi9zdGF0ZVwiKS5QYXJzZXI7dmFyIHJlc2VydmVkV29yZHM9X2RlcmVxXyhcIi4vaWRlbnRpZmllclwiKS5yZXNlcnZlZFdvcmRzO3ZhciBoYXM9X2RlcmVxXyhcIi4vdXRpbFwiKS5oYXM7dmFyIHBwPVBhcnNlci5wcm90b3R5cGU7cHAudG9Bc3NpZ25hYmxlID0gZnVuY3Rpb24obm9kZSwgaXNCaW5kaW5nKXtpZih0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNiAmJiBub2RlKXtzd2l0Y2gobm9kZS50eXBlKXtjYXNlIFwiSWRlbnRpZmllclwiOmNhc2UgXCJPYmplY3RQYXR0ZXJuXCI6Y2FzZSBcIkFycmF5UGF0dGVyblwiOmNhc2UgXCJBc3NpZ25tZW50UGF0dGVyblwiOmJyZWFrO2Nhc2UgXCJPYmplY3RFeHByZXNzaW9uXCI6bm9kZS50eXBlID0gXCJPYmplY3RQYXR0ZXJuXCI7Zm9yKHZhciBpPTA7IGkgPCBub2RlLnByb3BlcnRpZXMubGVuZ3RoOyBpKyspIHt2YXIgcHJvcD1ub2RlLnByb3BlcnRpZXNbaV07aWYocHJvcC5raW5kICE9PSBcImluaXRcIil0aGlzLnJhaXNlKHByb3Aua2V5LnN0YXJ0LCBcIk9iamVjdCBwYXR0ZXJuIGNhbid0IGNvbnRhaW4gZ2V0dGVyIG9yIHNldHRlclwiKTt0aGlzLnRvQXNzaWduYWJsZShwcm9wLnZhbHVlLCBpc0JpbmRpbmcpO31icmVhaztjYXNlIFwiQXJyYXlFeHByZXNzaW9uXCI6bm9kZS50eXBlID0gXCJBcnJheVBhdHRlcm5cIjt0aGlzLnRvQXNzaWduYWJsZUxpc3Qobm9kZS5lbGVtZW50cywgaXNCaW5kaW5nKTticmVhaztjYXNlIFwiQXNzaWdubWVudEV4cHJlc3Npb25cIjppZihub2RlLm9wZXJhdG9yID09PSBcIj1cIil7bm9kZS50eXBlID0gXCJBc3NpZ25tZW50UGF0dGVyblwiO31lbHNlIHt0aGlzLnJhaXNlKG5vZGUubGVmdC5lbmQsIFwiT25seSAnPScgb3BlcmF0b3IgY2FuIGJlIHVzZWQgZm9yIHNwZWNpZnlpbmcgZGVmYXVsdCB2YWx1ZS5cIik7fWJyZWFrO2Nhc2UgXCJQYXJlbnRoZXNpemVkRXhwcmVzc2lvblwiOm5vZGUuZXhwcmVzc2lvbiA9IHRoaXMudG9Bc3NpZ25hYmxlKG5vZGUuZXhwcmVzc2lvbiwgaXNCaW5kaW5nKTticmVhaztjYXNlIFwiTWVtYmVyRXhwcmVzc2lvblwiOmlmKCFpc0JpbmRpbmcpYnJlYWs7ZGVmYXVsdDp0aGlzLnJhaXNlKG5vZGUuc3RhcnQsIFwiQXNzaWduaW5nIHRvIHJ2YWx1ZVwiKTt9fXJldHVybiBub2RlO307cHAudG9Bc3NpZ25hYmxlTGlzdCA9IGZ1bmN0aW9uKGV4cHJMaXN0LCBpc0JpbmRpbmcpe3ZhciBlbmQ9ZXhwckxpc3QubGVuZ3RoO2lmKGVuZCl7dmFyIGxhc3Q9ZXhwckxpc3RbZW5kIC0gMV07aWYobGFzdCAmJiBsYXN0LnR5cGUgPT0gXCJSZXN0RWxlbWVudFwiKXstLWVuZDt9ZWxzZSBpZihsYXN0ICYmIGxhc3QudHlwZSA9PSBcIlNwcmVhZEVsZW1lbnRcIil7bGFzdC50eXBlID0gXCJSZXN0RWxlbWVudFwiO3ZhciBhcmc9bGFzdC5hcmd1bWVudDt0aGlzLnRvQXNzaWduYWJsZShhcmcsIGlzQmluZGluZyk7aWYoYXJnLnR5cGUgIT09IFwiSWRlbnRpZmllclwiICYmIGFyZy50eXBlICE9PSBcIk1lbWJlckV4cHJlc3Npb25cIiAmJiBhcmcudHlwZSAhPT0gXCJBcnJheVBhdHRlcm5cIil0aGlzLnVuZXhwZWN0ZWQoYXJnLnN0YXJ0KTstLWVuZDt9fWZvcih2YXIgaT0wOyBpIDwgZW5kOyBpKyspIHt2YXIgZWx0PWV4cHJMaXN0W2ldO2lmKGVsdCl0aGlzLnRvQXNzaWduYWJsZShlbHQsIGlzQmluZGluZyk7fXJldHVybiBleHByTGlzdDt9O3BwLnBhcnNlU3ByZWFkID0gZnVuY3Rpb24ocmVmU2hvcnRoYW5kRGVmYXVsdFBvcyl7dmFyIG5vZGU9dGhpcy5zdGFydE5vZGUoKTt0aGlzLm5leHQoKTtub2RlLmFyZ3VtZW50ID0gdGhpcy5wYXJzZU1heWJlQXNzaWduKHJlZlNob3J0aGFuZERlZmF1bHRQb3MpO3JldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJTcHJlYWRFbGVtZW50XCIpO307cHAucGFyc2VSZXN0ID0gZnVuY3Rpb24oKXt2YXIgbm9kZT10aGlzLnN0YXJ0Tm9kZSgpO3RoaXMubmV4dCgpO25vZGUuYXJndW1lbnQgPSB0aGlzLnR5cGUgPT09IHR0Lm5hbWUgfHwgdGhpcy50eXBlID09PSB0dC5icmFja2V0TD90aGlzLnBhcnNlQmluZGluZ0F0b20oKTp0aGlzLnVuZXhwZWN0ZWQoKTtyZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiUmVzdEVsZW1lbnRcIik7fTtwcC5wYXJzZUJpbmRpbmdBdG9tID0gZnVuY3Rpb24oKXtpZih0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPCA2KXJldHVybiB0aGlzLnBhcnNlSWRlbnQoKTtzd2l0Y2godGhpcy50eXBlKXtjYXNlIHR0Lm5hbWU6cmV0dXJuIHRoaXMucGFyc2VJZGVudCgpO2Nhc2UgdHQuYnJhY2tldEw6dmFyIG5vZGU9dGhpcy5zdGFydE5vZGUoKTt0aGlzLm5leHQoKTtub2RlLmVsZW1lbnRzID0gdGhpcy5wYXJzZUJpbmRpbmdMaXN0KHR0LmJyYWNrZXRSLCB0cnVlLCB0cnVlKTtyZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiQXJyYXlQYXR0ZXJuXCIpO2Nhc2UgdHQuYnJhY2VMOnJldHVybiB0aGlzLnBhcnNlT2JqKHRydWUpO2RlZmF1bHQ6dGhpcy51bmV4cGVjdGVkKCk7fX07cHAucGFyc2VCaW5kaW5nTGlzdCA9IGZ1bmN0aW9uKGNsb3NlLCBhbGxvd0VtcHR5LCBhbGxvd1RyYWlsaW5nQ29tbWEpe3ZhciBlbHRzPVtdLCBmaXJzdD10cnVlO3doaWxlKCF0aGlzLmVhdChjbG9zZSkpIHtpZihmaXJzdClmaXJzdCA9IGZhbHNlO2Vsc2UgdGhpcy5leHBlY3QodHQuY29tbWEpO2lmKGFsbG93RW1wdHkgJiYgdGhpcy50eXBlID09PSB0dC5jb21tYSl7ZWx0cy5wdXNoKG51bGwpO31lbHNlIGlmKGFsbG93VHJhaWxpbmdDb21tYSAmJiB0aGlzLmFmdGVyVHJhaWxpbmdDb21tYShjbG9zZSkpe2JyZWFrO31lbHNlIGlmKHRoaXMudHlwZSA9PT0gdHQuZWxsaXBzaXMpe3ZhciByZXN0PXRoaXMucGFyc2VSZXN0KCk7dGhpcy5wYXJzZUJpbmRpbmdMaXN0SXRlbShyZXN0KTtlbHRzLnB1c2gocmVzdCk7dGhpcy5leHBlY3QoY2xvc2UpO2JyZWFrO31lbHNlIHt2YXIgZWxlbT10aGlzLnBhcnNlTWF5YmVEZWZhdWx0KHRoaXMuc3RhcnQsIHRoaXMuc3RhcnRMb2MpO3RoaXMucGFyc2VCaW5kaW5nTGlzdEl0ZW0oZWxlbSk7ZWx0cy5wdXNoKGVsZW0pO319cmV0dXJuIGVsdHM7fTtwcC5wYXJzZUJpbmRpbmdMaXN0SXRlbSA9IGZ1bmN0aW9uKHBhcmFtKXtyZXR1cm4gcGFyYW07fTtwcC5wYXJzZU1heWJlRGVmYXVsdCA9IGZ1bmN0aW9uKHN0YXJ0UG9zLCBzdGFydExvYywgbGVmdCl7aWYoQXJyYXkuaXNBcnJheShzdGFydFBvcykpe2lmKHRoaXMub3B0aW9ucy5sb2NhdGlvbnMgJiYgbm9DYWxscyA9PT0gdW5kZWZpbmVkKXtsZWZ0ID0gc3RhcnRMb2M7c3RhcnRMb2MgPSBzdGFydFBvc1sxXTtzdGFydFBvcyA9IHN0YXJ0UG9zWzBdO319bGVmdCA9IGxlZnQgfHwgdGhpcy5wYXJzZUJpbmRpbmdBdG9tKCk7aWYoIXRoaXMuZWF0KHR0LmVxKSlyZXR1cm4gbGVmdDt2YXIgbm9kZT10aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0UG9zLCBzdGFydExvYyk7bm9kZS5vcGVyYXRvciA9IFwiPVwiO25vZGUubGVmdCA9IGxlZnQ7bm9kZS5yaWdodCA9IHRoaXMucGFyc2VNYXliZUFzc2lnbigpO3JldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJBc3NpZ25tZW50UGF0dGVyblwiKTt9O3BwLmNoZWNrTFZhbCA9IGZ1bmN0aW9uKGV4cHIsIGlzQmluZGluZywgY2hlY2tDbGFzaGVzKXtzd2l0Y2goZXhwci50eXBlKXtjYXNlIFwiSWRlbnRpZmllclwiOmlmKHRoaXMuc3RyaWN0ICYmIChyZXNlcnZlZFdvcmRzLnN0cmljdEJpbmQoZXhwci5uYW1lKSB8fCByZXNlcnZlZFdvcmRzLnN0cmljdChleHByLm5hbWUpKSl0aGlzLnJhaXNlKGV4cHIuc3RhcnQsIChpc0JpbmRpbmc/XCJCaW5kaW5nIFwiOlwiQXNzaWduaW5nIHRvIFwiKSArIGV4cHIubmFtZSArIFwiIGluIHN0cmljdCBtb2RlXCIpO2lmKGNoZWNrQ2xhc2hlcyl7aWYoaGFzKGNoZWNrQ2xhc2hlcywgZXhwci5uYW1lKSl0aGlzLnJhaXNlKGV4cHIuc3RhcnQsIFwiQXJndW1lbnQgbmFtZSBjbGFzaCBpbiBzdHJpY3QgbW9kZVwiKTtjaGVja0NsYXNoZXNbZXhwci5uYW1lXSA9IHRydWU7fWJyZWFrO2Nhc2UgXCJNZW1iZXJFeHByZXNzaW9uXCI6aWYoaXNCaW5kaW5nKXRoaXMucmFpc2UoZXhwci5zdGFydCwgKGlzQmluZGluZz9cIkJpbmRpbmdcIjpcIkFzc2lnbmluZyB0b1wiKSArIFwiIG1lbWJlciBleHByZXNzaW9uXCIpO2JyZWFrO2Nhc2UgXCJPYmplY3RQYXR0ZXJuXCI6Zm9yKHZhciBpPTA7IGkgPCBleHByLnByb3BlcnRpZXMubGVuZ3RoOyBpKyspIHt0aGlzLmNoZWNrTFZhbChleHByLnByb3BlcnRpZXNbaV0udmFsdWUsIGlzQmluZGluZywgY2hlY2tDbGFzaGVzKTt9YnJlYWs7Y2FzZSBcIkFycmF5UGF0dGVyblwiOmZvcih2YXIgaT0wOyBpIDwgZXhwci5lbGVtZW50cy5sZW5ndGg7IGkrKykge3ZhciBlbGVtPWV4cHIuZWxlbWVudHNbaV07aWYoZWxlbSl0aGlzLmNoZWNrTFZhbChlbGVtLCBpc0JpbmRpbmcsIGNoZWNrQ2xhc2hlcyk7fWJyZWFrO2Nhc2UgXCJBc3NpZ25tZW50UGF0dGVyblwiOnRoaXMuY2hlY2tMVmFsKGV4cHIubGVmdCwgaXNCaW5kaW5nLCBjaGVja0NsYXNoZXMpO2JyZWFrO2Nhc2UgXCJSZXN0RWxlbWVudFwiOnRoaXMuY2hlY2tMVmFsKGV4cHIuYXJndW1lbnQsIGlzQmluZGluZywgY2hlY2tDbGFzaGVzKTticmVhaztjYXNlIFwiUGFyZW50aGVzaXplZEV4cHJlc3Npb25cIjp0aGlzLmNoZWNrTFZhbChleHByLmV4cHJlc3Npb24sIGlzQmluZGluZywgY2hlY2tDbGFzaGVzKTticmVhaztkZWZhdWx0OnRoaXMucmFpc2UoZXhwci5zdGFydCwgKGlzQmluZGluZz9cIkJpbmRpbmdcIjpcIkFzc2lnbmluZyB0b1wiKSArIFwiIHJ2YWx1ZVwiKTt9fTt9LCB7XCIuL2lkZW50aWZpZXJcIjo3LCBcIi4vc3RhdGVcIjoxMywgXCIuL3Rva2VudHlwZVwiOjE3LCBcIi4vdXRpbFwiOjE4fV0sIDEwOltmdW5jdGlvbihfZGVyZXFfLCBtb2R1bGUsIGV4cG9ydHMpe1widXNlIHN0cmljdFwiO3ZhciBfY2xhc3NDYWxsQ2hlY2s9ZnVuY3Rpb24gX2NsYXNzQ2FsbENoZWNrKGluc3RhbmNlLCBDb25zdHJ1Y3Rvcil7aWYoIShpbnN0YW5jZSBpbnN0YW5jZW9mIENvbnN0cnVjdG9yKSl7dGhyb3cgbmV3IFR5cGVFcnJvcihcIkNhbm5vdCBjYWxsIGEgY2xhc3MgYXMgYSBmdW5jdGlvblwiKTt9fTtleHBvcnRzLl9fZXNNb2R1bGUgPSB0cnVlO3ZhciBQYXJzZXI9X2RlcmVxXyhcIi4vc3RhdGVcIikuUGFyc2VyO3ZhciBTb3VyY2VMb2NhdGlvbj1fZGVyZXFfKFwiLi9sb2NhdGlvblwiKS5Tb3VyY2VMb2NhdGlvbjt2YXIgcHA9UGFyc2VyLnByb3RvdHlwZTt2YXIgTm9kZT1leHBvcnRzLk5vZGUgPSBmdW5jdGlvbiBOb2RlKCl7X2NsYXNzQ2FsbENoZWNrKHRoaXMsIE5vZGUpO307cHAuc3RhcnROb2RlID0gZnVuY3Rpb24oKXt2YXIgbm9kZT1uZXcgTm9kZSgpO25vZGUuc3RhcnQgPSB0aGlzLnN0YXJ0O2lmKHRoaXMub3B0aW9ucy5sb2NhdGlvbnMpbm9kZS5sb2MgPSBuZXcgU291cmNlTG9jYXRpb24odGhpcywgdGhpcy5zdGFydExvYyk7aWYodGhpcy5vcHRpb25zLmRpcmVjdFNvdXJjZUZpbGUpbm9kZS5zb3VyY2VGaWxlID0gdGhpcy5vcHRpb25zLmRpcmVjdFNvdXJjZUZpbGU7aWYodGhpcy5vcHRpb25zLnJhbmdlcylub2RlLnJhbmdlID0gW3RoaXMuc3RhcnQsIDBdO3JldHVybiBub2RlO307cHAuc3RhcnROb2RlQXQgPSBmdW5jdGlvbihwb3MsIGxvYyl7dmFyIG5vZGU9bmV3IE5vZGUoKTtpZihBcnJheS5pc0FycmF5KHBvcykpe2lmKHRoaXMub3B0aW9ucy5sb2NhdGlvbnMgJiYgbG9jID09PSB1bmRlZmluZWQpe2xvYyA9IHBvc1sxXTtwb3MgPSBwb3NbMF07fX1ub2RlLnN0YXJ0ID0gcG9zO2lmKHRoaXMub3B0aW9ucy5sb2NhdGlvbnMpbm9kZS5sb2MgPSBuZXcgU291cmNlTG9jYXRpb24odGhpcywgbG9jKTtpZih0aGlzLm9wdGlvbnMuZGlyZWN0U291cmNlRmlsZSlub2RlLnNvdXJjZUZpbGUgPSB0aGlzLm9wdGlvbnMuZGlyZWN0U291cmNlRmlsZTtpZih0aGlzLm9wdGlvbnMucmFuZ2VzKW5vZGUucmFuZ2UgPSBbcG9zLCAwXTtyZXR1cm4gbm9kZTt9O3BwLmZpbmlzaE5vZGUgPSBmdW5jdGlvbihub2RlLCB0eXBlKXtub2RlLnR5cGUgPSB0eXBlO25vZGUuZW5kID0gdGhpcy5sYXN0VG9rRW5kO2lmKHRoaXMub3B0aW9ucy5sb2NhdGlvbnMpbm9kZS5sb2MuZW5kID0gdGhpcy5sYXN0VG9rRW5kTG9jO2lmKHRoaXMub3B0aW9ucy5yYW5nZXMpbm9kZS5yYW5nZVsxXSA9IHRoaXMubGFzdFRva0VuZDtyZXR1cm4gbm9kZTt9O3BwLmZpbmlzaE5vZGVBdCA9IGZ1bmN0aW9uKG5vZGUsIHR5cGUsIHBvcywgbG9jKXtub2RlLnR5cGUgPSB0eXBlO2lmKEFycmF5LmlzQXJyYXkocG9zKSl7aWYodGhpcy5vcHRpb25zLmxvY2F0aW9ucyAmJiBsb2MgPT09IHVuZGVmaW5lZCl7bG9jID0gcG9zWzFdO3BvcyA9IHBvc1swXTt9fW5vZGUuZW5kID0gcG9zO2lmKHRoaXMub3B0aW9ucy5sb2NhdGlvbnMpbm9kZS5sb2MuZW5kID0gbG9jO2lmKHRoaXMub3B0aW9ucy5yYW5nZXMpbm9kZS5yYW5nZVsxXSA9IHBvcztyZXR1cm4gbm9kZTt9O30sIHtcIi4vbG9jYXRpb25cIjo4LCBcIi4vc3RhdGVcIjoxM31dLCAxMTpbZnVuY3Rpb24oX2RlcmVxXywgbW9kdWxlLCBleHBvcnRzKXtcInVzZSBzdHJpY3RcIjtleHBvcnRzLmdldE9wdGlvbnMgPSBnZXRPcHRpb25zO2V4cG9ydHMuX19lc01vZHVsZSA9IHRydWU7dmFyIF91dGlsPV9kZXJlcV8oXCIuL3V0aWxcIik7dmFyIGhhcz1fdXRpbC5oYXM7dmFyIGlzQXJyYXk9X3V0aWwuaXNBcnJheTt2YXIgU291cmNlTG9jYXRpb249X2RlcmVxXyhcIi4vbG9jYXRpb25cIikuU291cmNlTG9jYXRpb247dmFyIGRlZmF1bHRPcHRpb25zPXtlY21hVmVyc2lvbjo1LCBzb3VyY2VUeXBlOlwic2NyaXB0XCIsIG9uSW5zZXJ0ZWRTZW1pY29sb246bnVsbCwgb25UcmFpbGluZ0NvbW1hOm51bGwsIGFsbG93UmVzZXJ2ZWQ6dHJ1ZSwgYWxsb3dSZXR1cm5PdXRzaWRlRnVuY3Rpb246ZmFsc2UsIGFsbG93SW1wb3J0RXhwb3J0RXZlcnl3aGVyZTpmYWxzZSwgYWxsb3dIYXNoQmFuZzpmYWxzZSwgbG9jYXRpb25zOmZhbHNlLCBvblRva2VuOm51bGwsIG9uQ29tbWVudDpudWxsLCByYW5nZXM6ZmFsc2UsIHByb2dyYW06bnVsbCwgc291cmNlRmlsZTpudWxsLCBkaXJlY3RTb3VyY2VGaWxlOm51bGwsIHByZXNlcnZlUGFyZW5zOmZhbHNlLCBwbHVnaW5zOnt9fTtleHBvcnRzLmRlZmF1bHRPcHRpb25zID0gZGVmYXVsdE9wdGlvbnM7ZnVuY3Rpb24gZ2V0T3B0aW9ucyhvcHRzKXt2YXIgb3B0aW9ucz17fTtmb3IodmFyIG9wdCBpbiBkZWZhdWx0T3B0aW9ucykge29wdGlvbnNbb3B0XSA9IG9wdHMgJiYgaGFzKG9wdHMsIG9wdCk/b3B0c1tvcHRdOmRlZmF1bHRPcHRpb25zW29wdF07fWlmKGlzQXJyYXkob3B0aW9ucy5vblRva2VuKSl7KGZ1bmN0aW9uKCl7dmFyIHRva2Vucz1vcHRpb25zLm9uVG9rZW47b3B0aW9ucy5vblRva2VuID0gZnVuY3Rpb24odG9rZW4pe3JldHVybiB0b2tlbnMucHVzaCh0b2tlbik7fTt9KSgpO31pZihpc0FycmF5KG9wdGlvbnMub25Db21tZW50KSlvcHRpb25zLm9uQ29tbWVudCA9IHB1c2hDb21tZW50KG9wdGlvbnMsIG9wdGlvbnMub25Db21tZW50KTtyZXR1cm4gb3B0aW9uczt9ZnVuY3Rpb24gcHVzaENvbW1lbnQob3B0aW9ucywgYXJyYXkpe3JldHVybiBmdW5jdGlvbihibG9jaywgdGV4dCwgc3RhcnQsIGVuZCwgc3RhcnRMb2MsIGVuZExvYyl7dmFyIGNvbW1lbnQ9e3R5cGU6YmxvY2s/XCJCbG9ja1wiOlwiTGluZVwiLCB2YWx1ZTp0ZXh0LCBzdGFydDpzdGFydCwgZW5kOmVuZH07aWYob3B0aW9ucy5sb2NhdGlvbnMpY29tbWVudC5sb2MgPSBuZXcgU291cmNlTG9jYXRpb24odGhpcywgc3RhcnRMb2MsIGVuZExvYyk7aWYob3B0aW9ucy5yYW5nZXMpY29tbWVudC5yYW5nZSA9IFtzdGFydCwgZW5kXTthcnJheS5wdXNoKGNvbW1lbnQpO307fX0sIHtcIi4vbG9jYXRpb25cIjo4LCBcIi4vdXRpbFwiOjE4fV0sIDEyOltmdW5jdGlvbihfZGVyZXFfLCBtb2R1bGUsIGV4cG9ydHMpe1widXNlIHN0cmljdFwiO3ZhciB0dD1fZGVyZXFfKFwiLi90b2tlbnR5cGVcIikudHlwZXM7dmFyIFBhcnNlcj1fZGVyZXFfKFwiLi9zdGF0ZVwiKS5QYXJzZXI7dmFyIGxpbmVCcmVhaz1fZGVyZXFfKFwiLi93aGl0ZXNwYWNlXCIpLmxpbmVCcmVhazt2YXIgcHA9UGFyc2VyLnByb3RvdHlwZTtwcC5pc1VzZVN0cmljdCA9IGZ1bmN0aW9uKHN0bXQpe3JldHVybiB0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNSAmJiBzdG10LnR5cGUgPT09IFwiRXhwcmVzc2lvblN0YXRlbWVudFwiICYmIHN0bXQuZXhwcmVzc2lvbi50eXBlID09PSBcIkxpdGVyYWxcIiAmJiBzdG10LmV4cHJlc3Npb24udmFsdWUgPT09IFwidXNlIHN0cmljdFwiO307cHAuZWF0ID0gZnVuY3Rpb24odHlwZSl7aWYodGhpcy50eXBlID09PSB0eXBlKXt0aGlzLm5leHQoKTtyZXR1cm4gdHJ1ZTt9ZWxzZSB7cmV0dXJuIGZhbHNlO319O3BwLmlzQ29udGV4dHVhbCA9IGZ1bmN0aW9uKG5hbWUpe3JldHVybiB0aGlzLnR5cGUgPT09IHR0Lm5hbWUgJiYgdGhpcy52YWx1ZSA9PT0gbmFtZTt9O3BwLmVhdENvbnRleHR1YWwgPSBmdW5jdGlvbihuYW1lKXtyZXR1cm4gdGhpcy52YWx1ZSA9PT0gbmFtZSAmJiB0aGlzLmVhdCh0dC5uYW1lKTt9O3BwLmV4cGVjdENvbnRleHR1YWwgPSBmdW5jdGlvbihuYW1lKXtpZighdGhpcy5lYXRDb250ZXh0dWFsKG5hbWUpKXRoaXMudW5leHBlY3RlZCgpO307cHAuY2FuSW5zZXJ0U2VtaWNvbG9uID0gZnVuY3Rpb24oKXtyZXR1cm4gdGhpcy50eXBlID09PSB0dC5lb2YgfHwgdGhpcy50eXBlID09PSB0dC5icmFjZVIgfHwgbGluZUJyZWFrLnRlc3QodGhpcy5pbnB1dC5zbGljZSh0aGlzLmxhc3RUb2tFbmQsIHRoaXMuc3RhcnQpKTt9O3BwLmluc2VydFNlbWljb2xvbiA9IGZ1bmN0aW9uKCl7aWYodGhpcy5jYW5JbnNlcnRTZW1pY29sb24oKSl7aWYodGhpcy5vcHRpb25zLm9uSW5zZXJ0ZWRTZW1pY29sb24pdGhpcy5vcHRpb25zLm9uSW5zZXJ0ZWRTZW1pY29sb24odGhpcy5sYXN0VG9rRW5kLCB0aGlzLmxhc3RUb2tFbmRMb2MpO3JldHVybiB0cnVlO319O3BwLnNlbWljb2xvbiA9IGZ1bmN0aW9uKCl7aWYoIXRoaXMuZWF0KHR0LnNlbWkpICYmICF0aGlzLmluc2VydFNlbWljb2xvbigpKXRoaXMudW5leHBlY3RlZCgpO307cHAuYWZ0ZXJUcmFpbGluZ0NvbW1hID0gZnVuY3Rpb24odG9rVHlwZSl7aWYodGhpcy50eXBlID09IHRva1R5cGUpe2lmKHRoaXMub3B0aW9ucy5vblRyYWlsaW5nQ29tbWEpdGhpcy5vcHRpb25zLm9uVHJhaWxpbmdDb21tYSh0aGlzLmxhc3RUb2tTdGFydCwgdGhpcy5sYXN0VG9rU3RhcnRMb2MpO3RoaXMubmV4dCgpO3JldHVybiB0cnVlO319O3BwLmV4cGVjdCA9IGZ1bmN0aW9uKHR5cGUpe3RoaXMuZWF0KHR5cGUpIHx8IHRoaXMudW5leHBlY3RlZCgpO307cHAudW5leHBlY3RlZCA9IGZ1bmN0aW9uKHBvcyl7dGhpcy5yYWlzZShwb3MgIT0gbnVsbD9wb3M6dGhpcy5zdGFydCwgXCJVbmV4cGVjdGVkIHRva2VuXCIpO307fSwge1wiLi9zdGF0ZVwiOjEzLCBcIi4vdG9rZW50eXBlXCI6MTcsIFwiLi93aGl0ZXNwYWNlXCI6MTl9XSwgMTM6W2Z1bmN0aW9uKF9kZXJlcV8sIG1vZHVsZSwgZXhwb3J0cyl7XCJ1c2Ugc3RyaWN0XCI7ZXhwb3J0cy5QYXJzZXIgPSBQYXJzZXI7ZXhwb3J0cy5fX2VzTW9kdWxlID0gdHJ1ZTt2YXIgX2lkZW50aWZpZXI9X2RlcmVxXyhcIi4vaWRlbnRpZmllclwiKTt2YXIgcmVzZXJ2ZWRXb3Jkcz1faWRlbnRpZmllci5yZXNlcnZlZFdvcmRzO3ZhciBrZXl3b3Jkcz1faWRlbnRpZmllci5rZXl3b3Jkczt2YXIgdHQ9X2RlcmVxXyhcIi4vdG9rZW50eXBlXCIpLnR5cGVzO3ZhciBsaW5lQnJlYWs9X2RlcmVxXyhcIi4vd2hpdGVzcGFjZVwiKS5saW5lQnJlYWs7ZnVuY3Rpb24gUGFyc2VyKG9wdGlvbnMsIGlucHV0LCBzdGFydFBvcyl7dGhpcy5vcHRpb25zID0gb3B0aW9uczt0aGlzLnNvdXJjZUZpbGUgPSB0aGlzLm9wdGlvbnMuc291cmNlRmlsZSB8fCBudWxsO3RoaXMuaXNLZXl3b3JkID0ga2V5d29yZHNbdGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDY/Njo1XTt0aGlzLmlzUmVzZXJ2ZWRXb3JkID0gcmVzZXJ2ZWRXb3Jkc1t0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb25dO3RoaXMuaW5wdXQgPSBpbnB1dDt0aGlzLmxvYWRQbHVnaW5zKHRoaXMub3B0aW9ucy5wbHVnaW5zKTtpZihzdGFydFBvcyl7dGhpcy5wb3MgPSBzdGFydFBvczt0aGlzLmxpbmVTdGFydCA9IE1hdGgubWF4KDAsIHRoaXMuaW5wdXQubGFzdEluZGV4T2YoXCJcXG5cIiwgc3RhcnRQb3MpKTt0aGlzLmN1ckxpbmUgPSB0aGlzLmlucHV0LnNsaWNlKDAsIHRoaXMubGluZVN0YXJ0KS5zcGxpdChsaW5lQnJlYWspLmxlbmd0aDt9ZWxzZSB7dGhpcy5wb3MgPSB0aGlzLmxpbmVTdGFydCA9IDA7dGhpcy5jdXJMaW5lID0gMTt9dGhpcy50eXBlID0gdHQuZW9mO3RoaXMudmFsdWUgPSBudWxsO3RoaXMuc3RhcnQgPSB0aGlzLmVuZCA9IHRoaXMucG9zO3RoaXMuc3RhcnRMb2MgPSB0aGlzLmVuZExvYyA9IG51bGw7dGhpcy5sYXN0VG9rRW5kTG9jID0gdGhpcy5sYXN0VG9rU3RhcnRMb2MgPSBudWxsO3RoaXMubGFzdFRva1N0YXJ0ID0gdGhpcy5sYXN0VG9rRW5kID0gdGhpcy5wb3M7dGhpcy5jb250ZXh0ID0gdGhpcy5pbml0aWFsQ29udGV4dCgpO3RoaXMuZXhwckFsbG93ZWQgPSB0cnVlO3RoaXMuc3RyaWN0ID0gdGhpcy5pbk1vZHVsZSA9IHRoaXMub3B0aW9ucy5zb3VyY2VUeXBlID09PSBcIm1vZHVsZVwiO3RoaXMucG90ZW50aWFsQXJyb3dBdCA9IC0xO3RoaXMuaW5GdW5jdGlvbiA9IHRoaXMuaW5HZW5lcmF0b3IgPSBmYWxzZTt0aGlzLmxhYmVscyA9IFtdO2lmKHRoaXMucG9zID09PSAwICYmIHRoaXMub3B0aW9ucy5hbGxvd0hhc2hCYW5nICYmIHRoaXMuaW5wdXQuc2xpY2UoMCwgMikgPT09IFwiIyFcIil0aGlzLnNraXBMaW5lQ29tbWVudCgyKTt9UGFyc2VyLnByb3RvdHlwZS5leHRlbmQgPSBmdW5jdGlvbihuYW1lLCBmKXt0aGlzW25hbWVdID0gZih0aGlzW25hbWVdKTt9O3ZhciBwbHVnaW5zPXt9O2V4cG9ydHMucGx1Z2lucyA9IHBsdWdpbnM7UGFyc2VyLnByb3RvdHlwZS5sb2FkUGx1Z2lucyA9IGZ1bmN0aW9uKHBsdWdpbnMpe2Zvcih2YXIgX25hbWUgaW4gcGx1Z2lucykge3ZhciBwbHVnaW49ZXhwb3J0cy5wbHVnaW5zW19uYW1lXTtpZighcGx1Z2luKXRocm93IG5ldyBFcnJvcihcIlBsdWdpbiAnXCIgKyBfbmFtZSArIFwiJyBub3QgZm91bmRcIik7cGx1Z2luKHRoaXMsIHBsdWdpbnNbX25hbWVdKTt9fTt9LCB7XCIuL2lkZW50aWZpZXJcIjo3LCBcIi4vdG9rZW50eXBlXCI6MTcsIFwiLi93aGl0ZXNwYWNlXCI6MTl9XSwgMTQ6W2Z1bmN0aW9uKF9kZXJlcV8sIG1vZHVsZSwgZXhwb3J0cyl7XCJ1c2Ugc3RyaWN0XCI7dmFyIHR0PV9kZXJlcV8oXCIuL3Rva2VudHlwZVwiKS50eXBlczt2YXIgUGFyc2VyPV9kZXJlcV8oXCIuL3N0YXRlXCIpLlBhcnNlcjt2YXIgbGluZUJyZWFrPV9kZXJlcV8oXCIuL3doaXRlc3BhY2VcIikubGluZUJyZWFrO3ZhciBwcD1QYXJzZXIucHJvdG90eXBlO3BwLnBhcnNlVG9wTGV2ZWwgPSBmdW5jdGlvbihub2RlKXt2YXIgZmlyc3Q9dHJ1ZTtpZighbm9kZS5ib2R5KW5vZGUuYm9keSA9IFtdO3doaWxlKHRoaXMudHlwZSAhPT0gdHQuZW9mKSB7dmFyIHN0bXQ9dGhpcy5wYXJzZVN0YXRlbWVudCh0cnVlLCB0cnVlKTtub2RlLmJvZHkucHVzaChzdG10KTtpZihmaXJzdCAmJiB0aGlzLmlzVXNlU3RyaWN0KHN0bXQpKXRoaXMuc2V0U3RyaWN0KHRydWUpO2ZpcnN0ID0gZmFsc2U7fXRoaXMubmV4dCgpO2lmKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KXtub2RlLnNvdXJjZVR5cGUgPSB0aGlzLm9wdGlvbnMuc291cmNlVHlwZTt9cmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIlByb2dyYW1cIik7fTt2YXIgbG9vcExhYmVsPXtraW5kOlwibG9vcFwifSwgc3dpdGNoTGFiZWw9e2tpbmQ6XCJzd2l0Y2hcIn07cHAucGFyc2VTdGF0ZW1lbnQgPSBmdW5jdGlvbihkZWNsYXJhdGlvbiwgdG9wTGV2ZWwpe3ZhciBzdGFydHR5cGU9dGhpcy50eXBlLCBub2RlPXRoaXMuc3RhcnROb2RlKCk7c3dpdGNoKHN0YXJ0dHlwZSl7Y2FzZSB0dC5fYnJlYWs6Y2FzZSB0dC5fY29udGludWU6cmV0dXJuIHRoaXMucGFyc2VCcmVha0NvbnRpbnVlU3RhdGVtZW50KG5vZGUsIHN0YXJ0dHlwZS5rZXl3b3JkKTtjYXNlIHR0Ll9kZWJ1Z2dlcjpyZXR1cm4gdGhpcy5wYXJzZURlYnVnZ2VyU3RhdGVtZW50KG5vZGUpO2Nhc2UgdHQuX2RvOnJldHVybiB0aGlzLnBhcnNlRG9TdGF0ZW1lbnQobm9kZSk7Y2FzZSB0dC5fZm9yOnJldHVybiB0aGlzLnBhcnNlRm9yU3RhdGVtZW50KG5vZGUpO2Nhc2UgdHQuX2Z1bmN0aW9uOmlmKCFkZWNsYXJhdGlvbiAmJiB0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNil0aGlzLnVuZXhwZWN0ZWQoKTtyZXR1cm4gdGhpcy5wYXJzZUZ1bmN0aW9uU3RhdGVtZW50KG5vZGUpO2Nhc2UgdHQuX2NsYXNzOmlmKCFkZWNsYXJhdGlvbil0aGlzLnVuZXhwZWN0ZWQoKTtyZXR1cm4gdGhpcy5wYXJzZUNsYXNzKG5vZGUsIHRydWUpO2Nhc2UgdHQuX2lmOnJldHVybiB0aGlzLnBhcnNlSWZTdGF0ZW1lbnQobm9kZSk7Y2FzZSB0dC5fcmV0dXJuOnJldHVybiB0aGlzLnBhcnNlUmV0dXJuU3RhdGVtZW50KG5vZGUpO2Nhc2UgdHQuX3N3aXRjaDpyZXR1cm4gdGhpcy5wYXJzZVN3aXRjaFN0YXRlbWVudChub2RlKTtjYXNlIHR0Ll90aHJvdzpyZXR1cm4gdGhpcy5wYXJzZVRocm93U3RhdGVtZW50KG5vZGUpO2Nhc2UgdHQuX3RyeTpyZXR1cm4gdGhpcy5wYXJzZVRyeVN0YXRlbWVudChub2RlKTtjYXNlIHR0Ll9sZXQ6Y2FzZSB0dC5fY29uc3Q6aWYoIWRlY2xhcmF0aW9uKXRoaXMudW5leHBlY3RlZCgpO2Nhc2UgdHQuX3ZhcjpyZXR1cm4gdGhpcy5wYXJzZVZhclN0YXRlbWVudChub2RlLCBzdGFydHR5cGUpO2Nhc2UgdHQuX3doaWxlOnJldHVybiB0aGlzLnBhcnNlV2hpbGVTdGF0ZW1lbnQobm9kZSk7Y2FzZSB0dC5fd2l0aDpyZXR1cm4gdGhpcy5wYXJzZVdpdGhTdGF0ZW1lbnQobm9kZSk7Y2FzZSB0dC5icmFjZUw6cmV0dXJuIHRoaXMucGFyc2VCbG9jaygpO2Nhc2UgdHQuc2VtaTpyZXR1cm4gdGhpcy5wYXJzZUVtcHR5U3RhdGVtZW50KG5vZGUpO2Nhc2UgdHQuX2V4cG9ydDpjYXNlIHR0Ll9pbXBvcnQ6aWYoIXRoaXMub3B0aW9ucy5hbGxvd0ltcG9ydEV4cG9ydEV2ZXJ5d2hlcmUpe2lmKCF0b3BMZXZlbCl0aGlzLnJhaXNlKHRoaXMuc3RhcnQsIFwiJ2ltcG9ydCcgYW5kICdleHBvcnQnIG1heSBvbmx5IGFwcGVhciBhdCB0aGUgdG9wIGxldmVsXCIpO2lmKCF0aGlzLmluTW9kdWxlKXRoaXMucmFpc2UodGhpcy5zdGFydCwgXCInaW1wb3J0JyBhbmQgJ2V4cG9ydCcgbWF5IGFwcGVhciBvbmx5IHdpdGggJ3NvdXJjZVR5cGU6IG1vZHVsZSdcIik7fXJldHVybiBzdGFydHR5cGUgPT09IHR0Ll9pbXBvcnQ/dGhpcy5wYXJzZUltcG9ydChub2RlKTp0aGlzLnBhcnNlRXhwb3J0KG5vZGUpO2RlZmF1bHQ6dmFyIG1heWJlTmFtZT10aGlzLnZhbHVlLCBleHByPXRoaXMucGFyc2VFeHByZXNzaW9uKCk7aWYoc3RhcnR0eXBlID09PSB0dC5uYW1lICYmIGV4cHIudHlwZSA9PT0gXCJJZGVudGlmaWVyXCIgJiYgdGhpcy5lYXQodHQuY29sb24pKXJldHVybiB0aGlzLnBhcnNlTGFiZWxlZFN0YXRlbWVudChub2RlLCBtYXliZU5hbWUsIGV4cHIpO2Vsc2UgcmV0dXJuIHRoaXMucGFyc2VFeHByZXNzaW9uU3RhdGVtZW50KG5vZGUsIGV4cHIpO319O3BwLnBhcnNlQnJlYWtDb250aW51ZVN0YXRlbWVudCA9IGZ1bmN0aW9uKG5vZGUsIGtleXdvcmQpe3ZhciBpc0JyZWFrPWtleXdvcmQgPT0gXCJicmVha1wiO3RoaXMubmV4dCgpO2lmKHRoaXMuZWF0KHR0LnNlbWkpIHx8IHRoaXMuaW5zZXJ0U2VtaWNvbG9uKCkpbm9kZS5sYWJlbCA9IG51bGw7ZWxzZSBpZih0aGlzLnR5cGUgIT09IHR0Lm5hbWUpdGhpcy51bmV4cGVjdGVkKCk7ZWxzZSB7bm9kZS5sYWJlbCA9IHRoaXMucGFyc2VJZGVudCgpO3RoaXMuc2VtaWNvbG9uKCk7fWZvcih2YXIgaT0wOyBpIDwgdGhpcy5sYWJlbHMubGVuZ3RoOyArK2kpIHt2YXIgbGFiPXRoaXMubGFiZWxzW2ldO2lmKG5vZGUubGFiZWwgPT0gbnVsbCB8fCBsYWIubmFtZSA9PT0gbm9kZS5sYWJlbC5uYW1lKXtpZihsYWIua2luZCAhPSBudWxsICYmIChpc0JyZWFrIHx8IGxhYi5raW5kID09PSBcImxvb3BcIikpYnJlYWs7aWYobm9kZS5sYWJlbCAmJiBpc0JyZWFrKWJyZWFrO319aWYoaSA9PT0gdGhpcy5sYWJlbHMubGVuZ3RoKXRoaXMucmFpc2Uobm9kZS5zdGFydCwgXCJVbnN5bnRhY3RpYyBcIiArIGtleXdvcmQpO3JldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgaXNCcmVhaz9cIkJyZWFrU3RhdGVtZW50XCI6XCJDb250aW51ZVN0YXRlbWVudFwiKTt9O3BwLnBhcnNlRGVidWdnZXJTdGF0ZW1lbnQgPSBmdW5jdGlvbihub2RlKXt0aGlzLm5leHQoKTt0aGlzLnNlbWljb2xvbigpO3JldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJEZWJ1Z2dlclN0YXRlbWVudFwiKTt9O3BwLnBhcnNlRG9TdGF0ZW1lbnQgPSBmdW5jdGlvbihub2RlKXt0aGlzLm5leHQoKTt0aGlzLmxhYmVscy5wdXNoKGxvb3BMYWJlbCk7bm9kZS5ib2R5ID0gdGhpcy5wYXJzZVN0YXRlbWVudChmYWxzZSk7dGhpcy5sYWJlbHMucG9wKCk7dGhpcy5leHBlY3QodHQuX3doaWxlKTtub2RlLnRlc3QgPSB0aGlzLnBhcnNlUGFyZW5FeHByZXNzaW9uKCk7aWYodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYpdGhpcy5lYXQodHQuc2VtaSk7ZWxzZSB0aGlzLnNlbWljb2xvbigpO3JldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJEb1doaWxlU3RhdGVtZW50XCIpO307cHAucGFyc2VGb3JTdGF0ZW1lbnQgPSBmdW5jdGlvbihub2RlKXt0aGlzLm5leHQoKTt0aGlzLmxhYmVscy5wdXNoKGxvb3BMYWJlbCk7dGhpcy5leHBlY3QodHQucGFyZW5MKTtpZih0aGlzLnR5cGUgPT09IHR0LnNlbWkpcmV0dXJuIHRoaXMucGFyc2VGb3Iobm9kZSwgbnVsbCk7aWYodGhpcy50eXBlID09PSB0dC5fdmFyIHx8IHRoaXMudHlwZSA9PT0gdHQuX2xldCB8fCB0aGlzLnR5cGUgPT09IHR0Ll9jb25zdCl7dmFyIF9pbml0PXRoaXMuc3RhcnROb2RlKCksIHZhcktpbmQ9dGhpcy50eXBlO3RoaXMubmV4dCgpO3RoaXMucGFyc2VWYXIoX2luaXQsIHRydWUsIHZhcktpbmQpO3RoaXMuZmluaXNoTm9kZShfaW5pdCwgXCJWYXJpYWJsZURlY2xhcmF0aW9uXCIpO2lmKCh0aGlzLnR5cGUgPT09IHR0Ll9pbiB8fCB0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNiAmJiB0aGlzLmlzQ29udGV4dHVhbChcIm9mXCIpKSAmJiBfaW5pdC5kZWNsYXJhdGlvbnMubGVuZ3RoID09PSAxICYmICEodmFyS2luZCAhPT0gdHQuX3ZhciAmJiBfaW5pdC5kZWNsYXJhdGlvbnNbMF0uaW5pdCkpcmV0dXJuIHRoaXMucGFyc2VGb3JJbihub2RlLCBfaW5pdCk7cmV0dXJuIHRoaXMucGFyc2VGb3Iobm9kZSwgX2luaXQpO312YXIgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcz17c3RhcnQ6MH07dmFyIGluaXQ9dGhpcy5wYXJzZUV4cHJlc3Npb24odHJ1ZSwgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcyk7aWYodGhpcy50eXBlID09PSB0dC5faW4gfHwgdGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYgJiYgdGhpcy5pc0NvbnRleHR1YWwoXCJvZlwiKSl7dGhpcy50b0Fzc2lnbmFibGUoaW5pdCk7dGhpcy5jaGVja0xWYWwoaW5pdCk7cmV0dXJuIHRoaXMucGFyc2VGb3JJbihub2RlLCBpbml0KTt9ZWxzZSBpZihyZWZTaG9ydGhhbmREZWZhdWx0UG9zLnN0YXJ0KXt0aGlzLnVuZXhwZWN0ZWQocmVmU2hvcnRoYW5kRGVmYXVsdFBvcy5zdGFydCk7fXJldHVybiB0aGlzLnBhcnNlRm9yKG5vZGUsIGluaXQpO307cHAucGFyc2VGdW5jdGlvblN0YXRlbWVudCA9IGZ1bmN0aW9uKG5vZGUpe3RoaXMubmV4dCgpO3JldHVybiB0aGlzLnBhcnNlRnVuY3Rpb24obm9kZSwgdHJ1ZSk7fTtwcC5wYXJzZUlmU3RhdGVtZW50ID0gZnVuY3Rpb24obm9kZSl7dGhpcy5uZXh0KCk7bm9kZS50ZXN0ID0gdGhpcy5wYXJzZVBhcmVuRXhwcmVzc2lvbigpO25vZGUuY29uc2VxdWVudCA9IHRoaXMucGFyc2VTdGF0ZW1lbnQoZmFsc2UpO25vZGUuYWx0ZXJuYXRlID0gdGhpcy5lYXQodHQuX2Vsc2UpP3RoaXMucGFyc2VTdGF0ZW1lbnQoZmFsc2UpOm51bGw7cmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIklmU3RhdGVtZW50XCIpO307cHAucGFyc2VSZXR1cm5TdGF0ZW1lbnQgPSBmdW5jdGlvbihub2RlKXtpZighdGhpcy5pbkZ1bmN0aW9uICYmICF0aGlzLm9wdGlvbnMuYWxsb3dSZXR1cm5PdXRzaWRlRnVuY3Rpb24pdGhpcy5yYWlzZSh0aGlzLnN0YXJ0LCBcIidyZXR1cm4nIG91dHNpZGUgb2YgZnVuY3Rpb25cIik7dGhpcy5uZXh0KCk7aWYodGhpcy5lYXQodHQuc2VtaSkgfHwgdGhpcy5pbnNlcnRTZW1pY29sb24oKSlub2RlLmFyZ3VtZW50ID0gbnVsbDtlbHNlIHtub2RlLmFyZ3VtZW50ID0gdGhpcy5wYXJzZUV4cHJlc3Npb24oKTt0aGlzLnNlbWljb2xvbigpO31yZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiUmV0dXJuU3RhdGVtZW50XCIpO307cHAucGFyc2VTd2l0Y2hTdGF0ZW1lbnQgPSBmdW5jdGlvbihub2RlKXt0aGlzLm5leHQoKTtub2RlLmRpc2NyaW1pbmFudCA9IHRoaXMucGFyc2VQYXJlbkV4cHJlc3Npb24oKTtub2RlLmNhc2VzID0gW107dGhpcy5leHBlY3QodHQuYnJhY2VMKTt0aGlzLmxhYmVscy5wdXNoKHN3aXRjaExhYmVsKTtmb3IodmFyIGN1ciwgc2F3RGVmYXVsdDsgdGhpcy50eXBlICE9IHR0LmJyYWNlUjspIHtpZih0aGlzLnR5cGUgPT09IHR0Ll9jYXNlIHx8IHRoaXMudHlwZSA9PT0gdHQuX2RlZmF1bHQpe3ZhciBpc0Nhc2U9dGhpcy50eXBlID09PSB0dC5fY2FzZTtpZihjdXIpdGhpcy5maW5pc2hOb2RlKGN1ciwgXCJTd2l0Y2hDYXNlXCIpO25vZGUuY2FzZXMucHVzaChjdXIgPSB0aGlzLnN0YXJ0Tm9kZSgpKTtjdXIuY29uc2VxdWVudCA9IFtdO3RoaXMubmV4dCgpO2lmKGlzQ2FzZSl7Y3VyLnRlc3QgPSB0aGlzLnBhcnNlRXhwcmVzc2lvbigpO31lbHNlIHtpZihzYXdEZWZhdWx0KXRoaXMucmFpc2UodGhpcy5sYXN0VG9rU3RhcnQsIFwiTXVsdGlwbGUgZGVmYXVsdCBjbGF1c2VzXCIpO3Nhd0RlZmF1bHQgPSB0cnVlO2N1ci50ZXN0ID0gbnVsbDt9dGhpcy5leHBlY3QodHQuY29sb24pO31lbHNlIHtpZighY3VyKXRoaXMudW5leHBlY3RlZCgpO2N1ci5jb25zZXF1ZW50LnB1c2godGhpcy5wYXJzZVN0YXRlbWVudCh0cnVlKSk7fX1pZihjdXIpdGhpcy5maW5pc2hOb2RlKGN1ciwgXCJTd2l0Y2hDYXNlXCIpO3RoaXMubmV4dCgpO3RoaXMubGFiZWxzLnBvcCgpO3JldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJTd2l0Y2hTdGF0ZW1lbnRcIik7fTtwcC5wYXJzZVRocm93U3RhdGVtZW50ID0gZnVuY3Rpb24obm9kZSl7dGhpcy5uZXh0KCk7aWYobGluZUJyZWFrLnRlc3QodGhpcy5pbnB1dC5zbGljZSh0aGlzLmxhc3RUb2tFbmQsIHRoaXMuc3RhcnQpKSl0aGlzLnJhaXNlKHRoaXMubGFzdFRva0VuZCwgXCJJbGxlZ2FsIG5ld2xpbmUgYWZ0ZXIgdGhyb3dcIik7bm9kZS5hcmd1bWVudCA9IHRoaXMucGFyc2VFeHByZXNzaW9uKCk7dGhpcy5zZW1pY29sb24oKTtyZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiVGhyb3dTdGF0ZW1lbnRcIik7fTt2YXIgZW1wdHk9W107cHAucGFyc2VUcnlTdGF0ZW1lbnQgPSBmdW5jdGlvbihub2RlKXt0aGlzLm5leHQoKTtub2RlLmJsb2NrID0gdGhpcy5wYXJzZUJsb2NrKCk7bm9kZS5oYW5kbGVyID0gbnVsbDtpZih0aGlzLnR5cGUgPT09IHR0Ll9jYXRjaCl7dmFyIGNsYXVzZT10aGlzLnN0YXJ0Tm9kZSgpO3RoaXMubmV4dCgpO3RoaXMuZXhwZWN0KHR0LnBhcmVuTCk7Y2xhdXNlLnBhcmFtID0gdGhpcy5wYXJzZUJpbmRpbmdBdG9tKCk7dGhpcy5jaGVja0xWYWwoY2xhdXNlLnBhcmFtLCB0cnVlKTt0aGlzLmV4cGVjdCh0dC5wYXJlblIpO2NsYXVzZS5ndWFyZCA9IG51bGw7Y2xhdXNlLmJvZHkgPSB0aGlzLnBhcnNlQmxvY2soKTtub2RlLmhhbmRsZXIgPSB0aGlzLmZpbmlzaE5vZGUoY2xhdXNlLCBcIkNhdGNoQ2xhdXNlXCIpO31ub2RlLmd1YXJkZWRIYW5kbGVycyA9IGVtcHR5O25vZGUuZmluYWxpemVyID0gdGhpcy5lYXQodHQuX2ZpbmFsbHkpP3RoaXMucGFyc2VCbG9jaygpOm51bGw7aWYoIW5vZGUuaGFuZGxlciAmJiAhbm9kZS5maW5hbGl6ZXIpdGhpcy5yYWlzZShub2RlLnN0YXJ0LCBcIk1pc3NpbmcgY2F0Y2ggb3IgZmluYWxseSBjbGF1c2VcIik7cmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIlRyeVN0YXRlbWVudFwiKTt9O3BwLnBhcnNlVmFyU3RhdGVtZW50ID0gZnVuY3Rpb24obm9kZSwga2luZCl7dGhpcy5uZXh0KCk7dGhpcy5wYXJzZVZhcihub2RlLCBmYWxzZSwga2luZCk7dGhpcy5zZW1pY29sb24oKTtyZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiVmFyaWFibGVEZWNsYXJhdGlvblwiKTt9O3BwLnBhcnNlV2hpbGVTdGF0ZW1lbnQgPSBmdW5jdGlvbihub2RlKXt0aGlzLm5leHQoKTtub2RlLnRlc3QgPSB0aGlzLnBhcnNlUGFyZW5FeHByZXNzaW9uKCk7dGhpcy5sYWJlbHMucHVzaChsb29wTGFiZWwpO25vZGUuYm9keSA9IHRoaXMucGFyc2VTdGF0ZW1lbnQoZmFsc2UpO3RoaXMubGFiZWxzLnBvcCgpO3JldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJXaGlsZVN0YXRlbWVudFwiKTt9O3BwLnBhcnNlV2l0aFN0YXRlbWVudCA9IGZ1bmN0aW9uKG5vZGUpe2lmKHRoaXMuc3RyaWN0KXRoaXMucmFpc2UodGhpcy5zdGFydCwgXCInd2l0aCcgaW4gc3RyaWN0IG1vZGVcIik7dGhpcy5uZXh0KCk7bm9kZS5vYmplY3QgPSB0aGlzLnBhcnNlUGFyZW5FeHByZXNzaW9uKCk7bm9kZS5ib2R5ID0gdGhpcy5wYXJzZVN0YXRlbWVudChmYWxzZSk7cmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIldpdGhTdGF0ZW1lbnRcIik7fTtwcC5wYXJzZUVtcHR5U3RhdGVtZW50ID0gZnVuY3Rpb24obm9kZSl7dGhpcy5uZXh0KCk7cmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkVtcHR5U3RhdGVtZW50XCIpO307cHAucGFyc2VMYWJlbGVkU3RhdGVtZW50ID0gZnVuY3Rpb24obm9kZSwgbWF5YmVOYW1lLCBleHByKXtmb3IodmFyIGk9MDsgaSA8IHRoaXMubGFiZWxzLmxlbmd0aDsgKytpKSB7aWYodGhpcy5sYWJlbHNbaV0ubmFtZSA9PT0gbWF5YmVOYW1lKXRoaXMucmFpc2UoZXhwci5zdGFydCwgXCJMYWJlbCAnXCIgKyBtYXliZU5hbWUgKyBcIicgaXMgYWxyZWFkeSBkZWNsYXJlZFwiKTt9dmFyIGtpbmQ9dGhpcy50eXBlLmlzTG9vcD9cImxvb3BcIjp0aGlzLnR5cGUgPT09IHR0Ll9zd2l0Y2g/XCJzd2l0Y2hcIjpudWxsO3RoaXMubGFiZWxzLnB1c2goe25hbWU6bWF5YmVOYW1lLCBraW5kOmtpbmR9KTtub2RlLmJvZHkgPSB0aGlzLnBhcnNlU3RhdGVtZW50KHRydWUpO3RoaXMubGFiZWxzLnBvcCgpO25vZGUubGFiZWwgPSBleHByO3JldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJMYWJlbGVkU3RhdGVtZW50XCIpO307cHAucGFyc2VFeHByZXNzaW9uU3RhdGVtZW50ID0gZnVuY3Rpb24obm9kZSwgZXhwcil7bm9kZS5leHByZXNzaW9uID0gZXhwcjt0aGlzLnNlbWljb2xvbigpO3JldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJFeHByZXNzaW9uU3RhdGVtZW50XCIpO307cHAucGFyc2VCbG9jayA9IGZ1bmN0aW9uKGFsbG93U3RyaWN0KXt2YXIgbm9kZT10aGlzLnN0YXJ0Tm9kZSgpLCBmaXJzdD10cnVlLCBvbGRTdHJpY3Q9dW5kZWZpbmVkO25vZGUuYm9keSA9IFtdO3RoaXMuZXhwZWN0KHR0LmJyYWNlTCk7d2hpbGUoIXRoaXMuZWF0KHR0LmJyYWNlUikpIHt2YXIgc3RtdD10aGlzLnBhcnNlU3RhdGVtZW50KHRydWUpO25vZGUuYm9keS5wdXNoKHN0bXQpO2lmKGZpcnN0ICYmIGFsbG93U3RyaWN0ICYmIHRoaXMuaXNVc2VTdHJpY3Qoc3RtdCkpe29sZFN0cmljdCA9IHRoaXMuc3RyaWN0O3RoaXMuc2V0U3RyaWN0KHRoaXMuc3RyaWN0ID0gdHJ1ZSk7fWZpcnN0ID0gZmFsc2U7fWlmKG9sZFN0cmljdCA9PT0gZmFsc2UpdGhpcy5zZXRTdHJpY3QoZmFsc2UpO3JldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJCbG9ja1N0YXRlbWVudFwiKTt9O3BwLnBhcnNlRm9yID0gZnVuY3Rpb24obm9kZSwgaW5pdCl7bm9kZS5pbml0ID0gaW5pdDt0aGlzLmV4cGVjdCh0dC5zZW1pKTtub2RlLnRlc3QgPSB0aGlzLnR5cGUgPT09IHR0LnNlbWk/bnVsbDp0aGlzLnBhcnNlRXhwcmVzc2lvbigpO3RoaXMuZXhwZWN0KHR0LnNlbWkpO25vZGUudXBkYXRlID0gdGhpcy50eXBlID09PSB0dC5wYXJlblI/bnVsbDp0aGlzLnBhcnNlRXhwcmVzc2lvbigpO3RoaXMuZXhwZWN0KHR0LnBhcmVuUik7bm9kZS5ib2R5ID0gdGhpcy5wYXJzZVN0YXRlbWVudChmYWxzZSk7dGhpcy5sYWJlbHMucG9wKCk7cmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkZvclN0YXRlbWVudFwiKTt9O3BwLnBhcnNlRm9ySW4gPSBmdW5jdGlvbihub2RlLCBpbml0KXt2YXIgdHlwZT10aGlzLnR5cGUgPT09IHR0Ll9pbj9cIkZvckluU3RhdGVtZW50XCI6XCJGb3JPZlN0YXRlbWVudFwiO3RoaXMubmV4dCgpO25vZGUubGVmdCA9IGluaXQ7bm9kZS5yaWdodCA9IHRoaXMucGFyc2VFeHByZXNzaW9uKCk7dGhpcy5leHBlY3QodHQucGFyZW5SKTtub2RlLmJvZHkgPSB0aGlzLnBhcnNlU3RhdGVtZW50KGZhbHNlKTt0aGlzLmxhYmVscy5wb3AoKTtyZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIHR5cGUpO307cHAucGFyc2VWYXIgPSBmdW5jdGlvbihub2RlLCBpc0Zvciwga2luZCl7bm9kZS5kZWNsYXJhdGlvbnMgPSBbXTtub2RlLmtpbmQgPSBraW5kLmtleXdvcmQ7Zm9yKDs7KSB7dmFyIGRlY2w9dGhpcy5zdGFydE5vZGUoKTt0aGlzLnBhcnNlVmFySWQoZGVjbCk7aWYodGhpcy5lYXQodHQuZXEpKXtkZWNsLmluaXQgPSB0aGlzLnBhcnNlTWF5YmVBc3NpZ24oaXNGb3IpO31lbHNlIGlmKGtpbmQgPT09IHR0Ll9jb25zdCAmJiAhKHRoaXMudHlwZSA9PT0gdHQuX2luIHx8IHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2ICYmIHRoaXMuaXNDb250ZXh0dWFsKFwib2ZcIikpKXt0aGlzLnVuZXhwZWN0ZWQoKTt9ZWxzZSBpZihkZWNsLmlkLnR5cGUgIT0gXCJJZGVudGlmaWVyXCIgJiYgIShpc0ZvciAmJiAodGhpcy50eXBlID09PSB0dC5faW4gfHwgdGhpcy5pc0NvbnRleHR1YWwoXCJvZlwiKSkpKXt0aGlzLnJhaXNlKHRoaXMubGFzdFRva0VuZCwgXCJDb21wbGV4IGJpbmRpbmcgcGF0dGVybnMgcmVxdWlyZSBhbiBpbml0aWFsaXphdGlvbiB2YWx1ZVwiKTt9ZWxzZSB7ZGVjbC5pbml0ID0gbnVsbDt9bm9kZS5kZWNsYXJhdGlvbnMucHVzaCh0aGlzLmZpbmlzaE5vZGUoZGVjbCwgXCJWYXJpYWJsZURlY2xhcmF0b3JcIikpO2lmKCF0aGlzLmVhdCh0dC5jb21tYSkpYnJlYWs7fXJldHVybiBub2RlO307cHAucGFyc2VWYXJJZCA9IGZ1bmN0aW9uKGRlY2wpe2RlY2wuaWQgPSB0aGlzLnBhcnNlQmluZGluZ0F0b20oKTt0aGlzLmNoZWNrTFZhbChkZWNsLmlkLCB0cnVlKTt9O3BwLnBhcnNlRnVuY3Rpb24gPSBmdW5jdGlvbihub2RlLCBpc1N0YXRlbWVudCwgYWxsb3dFeHByZXNzaW9uQm9keSl7dGhpcy5pbml0RnVuY3Rpb24obm9kZSk7aWYodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYpbm9kZS5nZW5lcmF0b3IgPSB0aGlzLmVhdCh0dC5zdGFyKTtpZihpc1N0YXRlbWVudCB8fCB0aGlzLnR5cGUgPT09IHR0Lm5hbWUpbm9kZS5pZCA9IHRoaXMucGFyc2VJZGVudCgpO3RoaXMucGFyc2VGdW5jdGlvblBhcmFtcyhub2RlKTt0aGlzLnBhcnNlRnVuY3Rpb25Cb2R5KG5vZGUsIGFsbG93RXhwcmVzc2lvbkJvZHkpO3JldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgaXNTdGF0ZW1lbnQ/XCJGdW5jdGlvbkRlY2xhcmF0aW9uXCI6XCJGdW5jdGlvbkV4cHJlc3Npb25cIik7fTtwcC5wYXJzZUZ1bmN0aW9uUGFyYW1zID0gZnVuY3Rpb24obm9kZSl7dGhpcy5leHBlY3QodHQucGFyZW5MKTtub2RlLnBhcmFtcyA9IHRoaXMucGFyc2VCaW5kaW5nTGlzdCh0dC5wYXJlblIsIGZhbHNlLCBmYWxzZSk7fTtwcC5wYXJzZUNsYXNzID0gZnVuY3Rpb24obm9kZSwgaXNTdGF0ZW1lbnQpe3RoaXMubmV4dCgpO3RoaXMucGFyc2VDbGFzc0lkKG5vZGUsIGlzU3RhdGVtZW50KTt0aGlzLnBhcnNlQ2xhc3NTdXBlcihub2RlKTt2YXIgY2xhc3NCb2R5PXRoaXMuc3RhcnROb2RlKCk7dmFyIGhhZENvbnN0cnVjdG9yPWZhbHNlO2NsYXNzQm9keS5ib2R5ID0gW107dGhpcy5leHBlY3QodHQuYnJhY2VMKTt3aGlsZSghdGhpcy5lYXQodHQuYnJhY2VSKSkge2lmKHRoaXMuZWF0KHR0LnNlbWkpKWNvbnRpbnVlO3ZhciBtZXRob2Q9dGhpcy5zdGFydE5vZGUoKTt2YXIgaXNHZW5lcmF0b3I9dGhpcy5lYXQodHQuc3Rhcik7dmFyIGlzTWF5YmVTdGF0aWM9dGhpcy50eXBlID09PSB0dC5uYW1lICYmIHRoaXMudmFsdWUgPT09IFwic3RhdGljXCI7dGhpcy5wYXJzZVByb3BlcnR5TmFtZShtZXRob2QpO21ldGhvZFtcInN0YXRpY1wiXSA9IGlzTWF5YmVTdGF0aWMgJiYgdGhpcy50eXBlICE9PSB0dC5wYXJlbkw7aWYobWV0aG9kW1wic3RhdGljXCJdKXtpZihpc0dlbmVyYXRvcil0aGlzLnVuZXhwZWN0ZWQoKTtpc0dlbmVyYXRvciA9IHRoaXMuZWF0KHR0LnN0YXIpO3RoaXMucGFyc2VQcm9wZXJ0eU5hbWUobWV0aG9kKTt9bWV0aG9kLmtpbmQgPSBcIm1ldGhvZFwiO2lmKCFtZXRob2QuY29tcHV0ZWQpe3ZhciBrZXk9bWV0aG9kLmtleTt2YXIgaXNHZXRTZXQ9ZmFsc2U7aWYoIWlzR2VuZXJhdG9yICYmIGtleS50eXBlID09PSBcIklkZW50aWZpZXJcIiAmJiB0aGlzLnR5cGUgIT09IHR0LnBhcmVuTCAmJiAoa2V5Lm5hbWUgPT09IFwiZ2V0XCIgfHwga2V5Lm5hbWUgPT09IFwic2V0XCIpKXtpc0dldFNldCA9IHRydWU7bWV0aG9kLmtpbmQgPSBrZXkubmFtZTtrZXkgPSB0aGlzLnBhcnNlUHJvcGVydHlOYW1lKG1ldGhvZCk7fWlmKCFtZXRob2RbXCJzdGF0aWNcIl0gJiYgKGtleS50eXBlID09PSBcIklkZW50aWZpZXJcIiAmJiBrZXkubmFtZSA9PT0gXCJjb25zdHJ1Y3RvclwiIHx8IGtleS50eXBlID09PSBcIkxpdGVyYWxcIiAmJiBrZXkudmFsdWUgPT09IFwiY29uc3RydWN0b3JcIikpe2lmKGhhZENvbnN0cnVjdG9yKXRoaXMucmFpc2Uoa2V5LnN0YXJ0LCBcIkR1cGxpY2F0ZSBjb25zdHJ1Y3RvciBpbiB0aGUgc2FtZSBjbGFzc1wiKTtpZihpc0dldFNldCl0aGlzLnJhaXNlKGtleS5zdGFydCwgXCJDb25zdHJ1Y3RvciBjYW4ndCBoYXZlIGdldC9zZXQgbW9kaWZpZXJcIik7aWYoaXNHZW5lcmF0b3IpdGhpcy5yYWlzZShrZXkuc3RhcnQsIFwiQ29uc3RydWN0b3IgY2FuJ3QgYmUgYSBnZW5lcmF0b3JcIik7bWV0aG9kLmtpbmQgPSBcImNvbnN0cnVjdG9yXCI7aGFkQ29uc3RydWN0b3IgPSB0cnVlO319dGhpcy5wYXJzZUNsYXNzTWV0aG9kKGNsYXNzQm9keSwgbWV0aG9kLCBpc0dlbmVyYXRvcik7fW5vZGUuYm9keSA9IHRoaXMuZmluaXNoTm9kZShjbGFzc0JvZHksIFwiQ2xhc3NCb2R5XCIpO3JldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgaXNTdGF0ZW1lbnQ/XCJDbGFzc0RlY2xhcmF0aW9uXCI6XCJDbGFzc0V4cHJlc3Npb25cIik7fTtwcC5wYXJzZUNsYXNzTWV0aG9kID0gZnVuY3Rpb24oY2xhc3NCb2R5LCBtZXRob2QsIGlzR2VuZXJhdG9yKXttZXRob2QudmFsdWUgPSB0aGlzLnBhcnNlTWV0aG9kKGlzR2VuZXJhdG9yKTtjbGFzc0JvZHkuYm9keS5wdXNoKHRoaXMuZmluaXNoTm9kZShtZXRob2QsIFwiTWV0aG9kRGVmaW5pdGlvblwiKSk7fTtwcC5wYXJzZUNsYXNzSWQgPSBmdW5jdGlvbihub2RlLCBpc1N0YXRlbWVudCl7bm9kZS5pZCA9IHRoaXMudHlwZSA9PT0gdHQubmFtZT90aGlzLnBhcnNlSWRlbnQoKTppc1N0YXRlbWVudD90aGlzLnVuZXhwZWN0ZWQoKTpudWxsO307cHAucGFyc2VDbGFzc1N1cGVyID0gZnVuY3Rpb24obm9kZSl7bm9kZS5zdXBlckNsYXNzID0gdGhpcy5lYXQodHQuX2V4dGVuZHMpP3RoaXMucGFyc2VFeHByU3Vic2NyaXB0cygpOm51bGw7fTtwcC5wYXJzZUV4cG9ydCA9IGZ1bmN0aW9uKG5vZGUpe3RoaXMubmV4dCgpO2lmKHRoaXMuZWF0KHR0LnN0YXIpKXt0aGlzLmV4cGVjdENvbnRleHR1YWwoXCJmcm9tXCIpO25vZGUuc291cmNlID0gdGhpcy50eXBlID09PSB0dC5zdHJpbmc/dGhpcy5wYXJzZUV4cHJBdG9tKCk6dGhpcy51bmV4cGVjdGVkKCk7dGhpcy5zZW1pY29sb24oKTtyZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiRXhwb3J0QWxsRGVjbGFyYXRpb25cIik7fWlmKHRoaXMuZWF0KHR0Ll9kZWZhdWx0KSl7dmFyIGV4cHI9dGhpcy5wYXJzZU1heWJlQXNzaWduKCk7dmFyIG5lZWRzU2VtaT10cnVlO2lmKGV4cHIudHlwZSA9PSBcIkZ1bmN0aW9uRXhwcmVzc2lvblwiIHx8IGV4cHIudHlwZSA9PSBcIkNsYXNzRXhwcmVzc2lvblwiKXtuZWVkc1NlbWkgPSBmYWxzZTtpZihleHByLmlkKXtleHByLnR5cGUgPSBleHByLnR5cGUgPT0gXCJGdW5jdGlvbkV4cHJlc3Npb25cIj9cIkZ1bmN0aW9uRGVjbGFyYXRpb25cIjpcIkNsYXNzRGVjbGFyYXRpb25cIjt9fW5vZGUuZGVjbGFyYXRpb24gPSBleHByO2lmKG5lZWRzU2VtaSl0aGlzLnNlbWljb2xvbigpO3JldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJFeHBvcnREZWZhdWx0RGVjbGFyYXRpb25cIik7fWlmKHRoaXMuc2hvdWxkUGFyc2VFeHBvcnRTdGF0ZW1lbnQoKSl7bm9kZS5kZWNsYXJhdGlvbiA9IHRoaXMucGFyc2VTdGF0ZW1lbnQodHJ1ZSk7bm9kZS5zcGVjaWZpZXJzID0gW107bm9kZS5zb3VyY2UgPSBudWxsO31lbHNlIHtub2RlLmRlY2xhcmF0aW9uID0gbnVsbDtub2RlLnNwZWNpZmllcnMgPSB0aGlzLnBhcnNlRXhwb3J0U3BlY2lmaWVycygpO2lmKHRoaXMuZWF0Q29udGV4dHVhbChcImZyb21cIikpe25vZGUuc291cmNlID0gdGhpcy50eXBlID09PSB0dC5zdHJpbmc/dGhpcy5wYXJzZUV4cHJBdG9tKCk6dGhpcy51bmV4cGVjdGVkKCk7fWVsc2Uge25vZGUuc291cmNlID0gbnVsbDt9dGhpcy5zZW1pY29sb24oKTt9cmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkV4cG9ydE5hbWVkRGVjbGFyYXRpb25cIik7fTtwcC5zaG91bGRQYXJzZUV4cG9ydFN0YXRlbWVudCA9IGZ1bmN0aW9uKCl7cmV0dXJuIHRoaXMudHlwZS5rZXl3b3JkO307cHAucGFyc2VFeHBvcnRTcGVjaWZpZXJzID0gZnVuY3Rpb24oKXt2YXIgbm9kZXM9W10sIGZpcnN0PXRydWU7dGhpcy5leHBlY3QodHQuYnJhY2VMKTt3aGlsZSghdGhpcy5lYXQodHQuYnJhY2VSKSkge2lmKCFmaXJzdCl7dGhpcy5leHBlY3QodHQuY29tbWEpO2lmKHRoaXMuYWZ0ZXJUcmFpbGluZ0NvbW1hKHR0LmJyYWNlUikpYnJlYWs7fWVsc2UgZmlyc3QgPSBmYWxzZTt2YXIgbm9kZT10aGlzLnN0YXJ0Tm9kZSgpO25vZGUubG9jYWwgPSB0aGlzLnBhcnNlSWRlbnQodGhpcy50eXBlID09PSB0dC5fZGVmYXVsdCk7bm9kZS5leHBvcnRlZCA9IHRoaXMuZWF0Q29udGV4dHVhbChcImFzXCIpP3RoaXMucGFyc2VJZGVudCh0cnVlKTpub2RlLmxvY2FsO25vZGVzLnB1c2godGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiRXhwb3J0U3BlY2lmaWVyXCIpKTt9cmV0dXJuIG5vZGVzO307cHAucGFyc2VJbXBvcnQgPSBmdW5jdGlvbihub2RlKXt0aGlzLm5leHQoKTtpZih0aGlzLnR5cGUgPT09IHR0LnN0cmluZyl7bm9kZS5zcGVjaWZpZXJzID0gZW1wdHk7bm9kZS5zb3VyY2UgPSB0aGlzLnBhcnNlRXhwckF0b20oKTtub2RlLmtpbmQgPSBcIlwiO31lbHNlIHtub2RlLnNwZWNpZmllcnMgPSB0aGlzLnBhcnNlSW1wb3J0U3BlY2lmaWVycygpO3RoaXMuZXhwZWN0Q29udGV4dHVhbChcImZyb21cIik7bm9kZS5zb3VyY2UgPSB0aGlzLnR5cGUgPT09IHR0LnN0cmluZz90aGlzLnBhcnNlRXhwckF0b20oKTp0aGlzLnVuZXhwZWN0ZWQoKTt9dGhpcy5zZW1pY29sb24oKTtyZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiSW1wb3J0RGVjbGFyYXRpb25cIik7fTtwcC5wYXJzZUltcG9ydFNwZWNpZmllcnMgPSBmdW5jdGlvbigpe3ZhciBub2Rlcz1bXSwgZmlyc3Q9dHJ1ZTtpZih0aGlzLnR5cGUgPT09IHR0Lm5hbWUpe3ZhciBub2RlPXRoaXMuc3RhcnROb2RlKCk7bm9kZS5sb2NhbCA9IHRoaXMucGFyc2VJZGVudCgpO3RoaXMuY2hlY2tMVmFsKG5vZGUubG9jYWwsIHRydWUpO25vZGVzLnB1c2godGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiSW1wb3J0RGVmYXVsdFNwZWNpZmllclwiKSk7aWYoIXRoaXMuZWF0KHR0LmNvbW1hKSlyZXR1cm4gbm9kZXM7fWlmKHRoaXMudHlwZSA9PT0gdHQuc3Rhcil7dmFyIG5vZGU9dGhpcy5zdGFydE5vZGUoKTt0aGlzLm5leHQoKTt0aGlzLmV4cGVjdENvbnRleHR1YWwoXCJhc1wiKTtub2RlLmxvY2FsID0gdGhpcy5wYXJzZUlkZW50KCk7dGhpcy5jaGVja0xWYWwobm9kZS5sb2NhbCwgdHJ1ZSk7bm9kZXMucHVzaCh0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJJbXBvcnROYW1lc3BhY2VTcGVjaWZpZXJcIikpO3JldHVybiBub2Rlczt9dGhpcy5leHBlY3QodHQuYnJhY2VMKTt3aGlsZSghdGhpcy5lYXQodHQuYnJhY2VSKSkge2lmKCFmaXJzdCl7dGhpcy5leHBlY3QodHQuY29tbWEpO2lmKHRoaXMuYWZ0ZXJUcmFpbGluZ0NvbW1hKHR0LmJyYWNlUikpYnJlYWs7fWVsc2UgZmlyc3QgPSBmYWxzZTt2YXIgbm9kZT10aGlzLnN0YXJ0Tm9kZSgpO25vZGUuaW1wb3J0ZWQgPSB0aGlzLnBhcnNlSWRlbnQodHJ1ZSk7bm9kZS5sb2NhbCA9IHRoaXMuZWF0Q29udGV4dHVhbChcImFzXCIpP3RoaXMucGFyc2VJZGVudCgpOm5vZGUuaW1wb3J0ZWQ7dGhpcy5jaGVja0xWYWwobm9kZS5sb2NhbCwgdHJ1ZSk7bm9kZXMucHVzaCh0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJJbXBvcnRTcGVjaWZpZXJcIikpO31yZXR1cm4gbm9kZXM7fTt9LCB7XCIuL3N0YXRlXCI6MTMsIFwiLi90b2tlbnR5cGVcIjoxNywgXCIuL3doaXRlc3BhY2VcIjoxOX1dLCAxNTpbZnVuY3Rpb24oX2RlcmVxXywgbW9kdWxlLCBleHBvcnRzKXtcInVzZSBzdHJpY3RcIjt2YXIgX2NsYXNzQ2FsbENoZWNrPWZ1bmN0aW9uIF9jbGFzc0NhbGxDaGVjayhpbnN0YW5jZSwgQ29uc3RydWN0b3Ipe2lmKCEoaW5zdGFuY2UgaW5zdGFuY2VvZiBDb25zdHJ1Y3Rvcikpe3Rocm93IG5ldyBUeXBlRXJyb3IoXCJDYW5ub3QgY2FsbCBhIGNsYXNzIGFzIGEgZnVuY3Rpb25cIik7fX07ZXhwb3J0cy5fX2VzTW9kdWxlID0gdHJ1ZTt2YXIgUGFyc2VyPV9kZXJlcV8oXCIuL3N0YXRlXCIpLlBhcnNlcjt2YXIgdHQ9X2RlcmVxXyhcIi4vdG9rZW50eXBlXCIpLnR5cGVzO3ZhciBsaW5lQnJlYWs9X2RlcmVxXyhcIi4vd2hpdGVzcGFjZVwiKS5saW5lQnJlYWs7dmFyIFRva0NvbnRleHQ9ZXhwb3J0cy5Ub2tDb250ZXh0ID0gZnVuY3Rpb24gVG9rQ29udGV4dCh0b2tlbiwgaXNFeHByLCBwcmVzZXJ2ZVNwYWNlLCBvdmVycmlkZSl7X2NsYXNzQ2FsbENoZWNrKHRoaXMsIFRva0NvbnRleHQpO3RoaXMudG9rZW4gPSB0b2tlbjt0aGlzLmlzRXhwciA9IGlzRXhwcjt0aGlzLnByZXNlcnZlU3BhY2UgPSBwcmVzZXJ2ZVNwYWNlO3RoaXMub3ZlcnJpZGUgPSBvdmVycmlkZTt9O3ZhciB0eXBlcz17Yl9zdGF0Om5ldyBUb2tDb250ZXh0KFwie1wiLCBmYWxzZSksIGJfZXhwcjpuZXcgVG9rQ29udGV4dChcIntcIiwgdHJ1ZSksIGJfdG1wbDpuZXcgVG9rQ29udGV4dChcIiR7XCIsIHRydWUpLCBwX3N0YXQ6bmV3IFRva0NvbnRleHQoXCIoXCIsIGZhbHNlKSwgcF9leHByOm5ldyBUb2tDb250ZXh0KFwiKFwiLCB0cnVlKSwgcV90bXBsOm5ldyBUb2tDb250ZXh0KFwiYFwiLCB0cnVlLCB0cnVlLCBmdW5jdGlvbihwKXtyZXR1cm4gcC5yZWFkVG1wbFRva2VuKCk7fSksIGZfZXhwcjpuZXcgVG9rQ29udGV4dChcImZ1bmN0aW9uXCIsIHRydWUpfTtleHBvcnRzLnR5cGVzID0gdHlwZXM7dmFyIHBwPVBhcnNlci5wcm90b3R5cGU7cHAuaW5pdGlhbENvbnRleHQgPSBmdW5jdGlvbigpe3JldHVybiBbdHlwZXMuYl9zdGF0XTt9O3BwLmJyYWNlSXNCbG9jayA9IGZ1bmN0aW9uKHByZXZUeXBlKXt2YXIgcGFyZW50PXVuZGVmaW5lZDtpZihwcmV2VHlwZSA9PT0gdHQuY29sb24gJiYgKHBhcmVudCA9IHRoaXMuY3VyQ29udGV4dCgpKS50b2tlbiA9PSBcIntcIilyZXR1cm4gIXBhcmVudC5pc0V4cHI7aWYocHJldlR5cGUgPT09IHR0Ll9yZXR1cm4pcmV0dXJuIGxpbmVCcmVhay50ZXN0KHRoaXMuaW5wdXQuc2xpY2UodGhpcy5sYXN0VG9rRW5kLCB0aGlzLnN0YXJ0KSk7aWYocHJldlR5cGUgPT09IHR0Ll9lbHNlIHx8IHByZXZUeXBlID09PSB0dC5zZW1pIHx8IHByZXZUeXBlID09PSB0dC5lb2YpcmV0dXJuIHRydWU7aWYocHJldlR5cGUgPT0gdHQuYnJhY2VMKXJldHVybiB0aGlzLmN1ckNvbnRleHQoKSA9PT0gdHlwZXMuYl9zdGF0O3JldHVybiAhdGhpcy5leHByQWxsb3dlZDt9O3BwLnVwZGF0ZUNvbnRleHQgPSBmdW5jdGlvbihwcmV2VHlwZSl7dmFyIHVwZGF0ZT11bmRlZmluZWQsIHR5cGU9dGhpcy50eXBlO2lmKHR5cGUua2V5d29yZCAmJiBwcmV2VHlwZSA9PSB0dC5kb3QpdGhpcy5leHByQWxsb3dlZCA9IGZhbHNlO2Vsc2UgaWYodXBkYXRlID0gdHlwZS51cGRhdGVDb250ZXh0KXVwZGF0ZS5jYWxsKHRoaXMsIHByZXZUeXBlKTtlbHNlIHRoaXMuZXhwckFsbG93ZWQgPSB0eXBlLmJlZm9yZUV4cHI7fTt0dC5wYXJlblIudXBkYXRlQ29udGV4dCA9IHR0LmJyYWNlUi51cGRhdGVDb250ZXh0ID0gZnVuY3Rpb24oKXtpZih0aGlzLmNvbnRleHQubGVuZ3RoID09IDEpe3RoaXMuZXhwckFsbG93ZWQgPSB0cnVlO3JldHVybjt9dmFyIG91dD10aGlzLmNvbnRleHQucG9wKCk7aWYob3V0ID09PSB0eXBlcy5iX3N0YXQgJiYgdGhpcy5jdXJDb250ZXh0KCkgPT09IHR5cGVzLmZfZXhwcil7dGhpcy5jb250ZXh0LnBvcCgpO3RoaXMuZXhwckFsbG93ZWQgPSBmYWxzZTt9ZWxzZSBpZihvdXQgPT09IHR5cGVzLmJfdG1wbCl7dGhpcy5leHByQWxsb3dlZCA9IHRydWU7fWVsc2Uge3RoaXMuZXhwckFsbG93ZWQgPSAhb3V0LmlzRXhwcjt9fTt0dC5icmFjZUwudXBkYXRlQ29udGV4dCA9IGZ1bmN0aW9uKHByZXZUeXBlKXt0aGlzLmNvbnRleHQucHVzaCh0aGlzLmJyYWNlSXNCbG9jayhwcmV2VHlwZSk/dHlwZXMuYl9zdGF0OnR5cGVzLmJfZXhwcik7dGhpcy5leHByQWxsb3dlZCA9IHRydWU7fTt0dC5kb2xsYXJCcmFjZUwudXBkYXRlQ29udGV4dCA9IGZ1bmN0aW9uKCl7dGhpcy5jb250ZXh0LnB1c2godHlwZXMuYl90bXBsKTt0aGlzLmV4cHJBbGxvd2VkID0gdHJ1ZTt9O3R0LnBhcmVuTC51cGRhdGVDb250ZXh0ID0gZnVuY3Rpb24ocHJldlR5cGUpe3ZhciBzdGF0ZW1lbnRQYXJlbnM9cHJldlR5cGUgPT09IHR0Ll9pZiB8fCBwcmV2VHlwZSA9PT0gdHQuX2ZvciB8fCBwcmV2VHlwZSA9PT0gdHQuX3dpdGggfHwgcHJldlR5cGUgPT09IHR0Ll93aGlsZTt0aGlzLmNvbnRleHQucHVzaChzdGF0ZW1lbnRQYXJlbnM/dHlwZXMucF9zdGF0OnR5cGVzLnBfZXhwcik7dGhpcy5leHByQWxsb3dlZCA9IHRydWU7fTt0dC5pbmNEZWMudXBkYXRlQ29udGV4dCA9IGZ1bmN0aW9uKCl7fTt0dC5fZnVuY3Rpb24udXBkYXRlQ29udGV4dCA9IGZ1bmN0aW9uKCl7aWYodGhpcy5jdXJDb250ZXh0KCkgIT09IHR5cGVzLmJfc3RhdCl0aGlzLmNvbnRleHQucHVzaCh0eXBlcy5mX2V4cHIpO3RoaXMuZXhwckFsbG93ZWQgPSBmYWxzZTt9O3R0LmJhY2tRdW90ZS51cGRhdGVDb250ZXh0ID0gZnVuY3Rpb24oKXtpZih0aGlzLmN1ckNvbnRleHQoKSA9PT0gdHlwZXMucV90bXBsKXRoaXMuY29udGV4dC5wb3AoKTtlbHNlIHRoaXMuY29udGV4dC5wdXNoKHR5cGVzLnFfdG1wbCk7dGhpcy5leHByQWxsb3dlZCA9IGZhbHNlO307fSwge1wiLi9zdGF0ZVwiOjEzLCBcIi4vdG9rZW50eXBlXCI6MTcsIFwiLi93aGl0ZXNwYWNlXCI6MTl9XSwgMTY6W2Z1bmN0aW9uKF9kZXJlcV8sIG1vZHVsZSwgZXhwb3J0cyl7XCJ1c2Ugc3RyaWN0XCI7dmFyIF9jbGFzc0NhbGxDaGVjaz1mdW5jdGlvbiBfY2xhc3NDYWxsQ2hlY2soaW5zdGFuY2UsIENvbnN0cnVjdG9yKXtpZighKGluc3RhbmNlIGluc3RhbmNlb2YgQ29uc3RydWN0b3IpKXt0aHJvdyBuZXcgVHlwZUVycm9yKFwiQ2Fubm90IGNhbGwgYSBjbGFzcyBhcyBhIGZ1bmN0aW9uXCIpO319O2V4cG9ydHMuX19lc01vZHVsZSA9IHRydWU7dmFyIF9pZGVudGlmaWVyPV9kZXJlcV8oXCIuL2lkZW50aWZpZXJcIik7dmFyIGlzSWRlbnRpZmllclN0YXJ0PV9pZGVudGlmaWVyLmlzSWRlbnRpZmllclN0YXJ0O3ZhciBpc0lkZW50aWZpZXJDaGFyPV9pZGVudGlmaWVyLmlzSWRlbnRpZmllckNoYXI7dmFyIF90b2tlbnR5cGU9X2RlcmVxXyhcIi4vdG9rZW50eXBlXCIpO3ZhciB0dD1fdG9rZW50eXBlLnR5cGVzO3ZhciBrZXl3b3JkVHlwZXM9X3Rva2VudHlwZS5rZXl3b3Jkczt2YXIgUGFyc2VyPV9kZXJlcV8oXCIuL3N0YXRlXCIpLlBhcnNlcjt2YXIgU291cmNlTG9jYXRpb249X2RlcmVxXyhcIi4vbG9jYXRpb25cIikuU291cmNlTG9jYXRpb247dmFyIF93aGl0ZXNwYWNlPV9kZXJlcV8oXCIuL3doaXRlc3BhY2VcIik7dmFyIGxpbmVCcmVhaz1fd2hpdGVzcGFjZS5saW5lQnJlYWs7dmFyIGxpbmVCcmVha0c9X3doaXRlc3BhY2UubGluZUJyZWFrRzt2YXIgaXNOZXdMaW5lPV93aGl0ZXNwYWNlLmlzTmV3TGluZTt2YXIgbm9uQVNDSUl3aGl0ZXNwYWNlPV93aGl0ZXNwYWNlLm5vbkFTQ0lJd2hpdGVzcGFjZTt2YXIgVG9rZW49ZXhwb3J0cy5Ub2tlbiA9IGZ1bmN0aW9uIFRva2VuKHApe19jbGFzc0NhbGxDaGVjayh0aGlzLCBUb2tlbik7dGhpcy50eXBlID0gcC50eXBlO3RoaXMudmFsdWUgPSBwLnZhbHVlO3RoaXMuc3RhcnQgPSBwLnN0YXJ0O3RoaXMuZW5kID0gcC5lbmQ7aWYocC5vcHRpb25zLmxvY2F0aW9ucyl0aGlzLmxvYyA9IG5ldyBTb3VyY2VMb2NhdGlvbihwLCBwLnN0YXJ0TG9jLCBwLmVuZExvYyk7aWYocC5vcHRpb25zLnJhbmdlcyl0aGlzLnJhbmdlID0gW3Auc3RhcnQsIHAuZW5kXTt9O3ZhciBwcD1QYXJzZXIucHJvdG90eXBlO3ZhciBpc1JoaW5vPXR5cGVvZiBQYWNrYWdlcyAhPT0gXCJ1bmRlZmluZWRcIjtwcC5uZXh0ID0gZnVuY3Rpb24oKXtpZih0aGlzLm9wdGlvbnMub25Ub2tlbil0aGlzLm9wdGlvbnMub25Ub2tlbihuZXcgVG9rZW4odGhpcykpO3RoaXMubGFzdFRva0VuZCA9IHRoaXMuZW5kO3RoaXMubGFzdFRva1N0YXJ0ID0gdGhpcy5zdGFydDt0aGlzLmxhc3RUb2tFbmRMb2MgPSB0aGlzLmVuZExvYzt0aGlzLmxhc3RUb2tTdGFydExvYyA9IHRoaXMuc3RhcnRMb2M7dGhpcy5uZXh0VG9rZW4oKTt9O3BwLmdldFRva2VuID0gZnVuY3Rpb24oKXt0aGlzLm5leHQoKTtyZXR1cm4gbmV3IFRva2VuKHRoaXMpO307aWYodHlwZW9mIFN5bWJvbCAhPT0gXCJ1bmRlZmluZWRcIilwcFtTeW1ib2wuaXRlcmF0b3JdID0gZnVuY3Rpb24oKXt2YXIgc2VsZj10aGlzO3JldHVybiB7bmV4dDpmdW5jdGlvbiBuZXh0KCl7dmFyIHRva2VuPXNlbGYuZ2V0VG9rZW4oKTtyZXR1cm4ge2RvbmU6dG9rZW4udHlwZSA9PT0gdHQuZW9mLCB2YWx1ZTp0b2tlbn07fX07fTtwcC5zZXRTdHJpY3QgPSBmdW5jdGlvbihzdHJpY3Qpe3RoaXMuc3RyaWN0ID0gc3RyaWN0O2lmKHRoaXMudHlwZSAhPT0gdHQubnVtICYmIHRoaXMudHlwZSAhPT0gdHQuc3RyaW5nKXJldHVybjt0aGlzLnBvcyA9IHRoaXMuc3RhcnQ7aWYodGhpcy5vcHRpb25zLmxvY2F0aW9ucyl7d2hpbGUodGhpcy5wb3MgPCB0aGlzLmxpbmVTdGFydCkge3RoaXMubGluZVN0YXJ0ID0gdGhpcy5pbnB1dC5sYXN0SW5kZXhPZihcIlxcblwiLCB0aGlzLmxpbmVTdGFydCAtIDIpICsgMTstLXRoaXMuY3VyTGluZTt9fXRoaXMubmV4dFRva2VuKCk7fTtwcC5jdXJDb250ZXh0ID0gZnVuY3Rpb24oKXtyZXR1cm4gdGhpcy5jb250ZXh0W3RoaXMuY29udGV4dC5sZW5ndGggLSAxXTt9O3BwLm5leHRUb2tlbiA9IGZ1bmN0aW9uKCl7dmFyIGN1ckNvbnRleHQ9dGhpcy5jdXJDb250ZXh0KCk7aWYoIWN1ckNvbnRleHQgfHwgIWN1ckNvbnRleHQucHJlc2VydmVTcGFjZSl0aGlzLnNraXBTcGFjZSgpO3RoaXMuc3RhcnQgPSB0aGlzLnBvcztpZih0aGlzLm9wdGlvbnMubG9jYXRpb25zKXRoaXMuc3RhcnRMb2MgPSB0aGlzLmN1clBvc2l0aW9uKCk7aWYodGhpcy5wb3MgPj0gdGhpcy5pbnB1dC5sZW5ndGgpcmV0dXJuIHRoaXMuZmluaXNoVG9rZW4odHQuZW9mKTtpZihjdXJDb250ZXh0Lm92ZXJyaWRlKXJldHVybiBjdXJDb250ZXh0Lm92ZXJyaWRlKHRoaXMpO2Vsc2UgdGhpcy5yZWFkVG9rZW4odGhpcy5mdWxsQ2hhckNvZGVBdFBvcygpKTt9O3BwLnJlYWRUb2tlbiA9IGZ1bmN0aW9uKGNvZGUpe2lmKGlzSWRlbnRpZmllclN0YXJ0KGNvZGUsIHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KSB8fCBjb2RlID09PSA5MilyZXR1cm4gdGhpcy5yZWFkV29yZCgpO3JldHVybiB0aGlzLmdldFRva2VuRnJvbUNvZGUoY29kZSk7fTtwcC5mdWxsQ2hhckNvZGVBdFBvcyA9IGZ1bmN0aW9uKCl7dmFyIGNvZGU9dGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zKTtpZihjb2RlIDw9IDU1Mjk1IHx8IGNvZGUgPj0gNTczNDQpcmV0dXJuIGNvZGU7dmFyIG5leHQ9dGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMSk7cmV0dXJuIChjb2RlIDw8IDEwKSArIG5leHQgLSA1NjYxMzg4ODt9O3BwLnNraXBCbG9ja0NvbW1lbnQgPSBmdW5jdGlvbigpe3ZhciBzdGFydExvYz10aGlzLm9wdGlvbnMub25Db21tZW50ICYmIHRoaXMub3B0aW9ucy5sb2NhdGlvbnMgJiYgdGhpcy5jdXJQb3NpdGlvbigpO3ZhciBzdGFydD10aGlzLnBvcywgZW5kPXRoaXMuaW5wdXQuaW5kZXhPZihcIiovXCIsIHRoaXMucG9zICs9IDIpO2lmKGVuZCA9PT0gLTEpdGhpcy5yYWlzZSh0aGlzLnBvcyAtIDIsIFwiVW50ZXJtaW5hdGVkIGNvbW1lbnRcIik7dGhpcy5wb3MgPSBlbmQgKyAyO2lmKHRoaXMub3B0aW9ucy5sb2NhdGlvbnMpe2xpbmVCcmVha0cubGFzdEluZGV4ID0gc3RhcnQ7dmFyIG1hdGNoPXVuZGVmaW5lZDt3aGlsZSgobWF0Y2ggPSBsaW5lQnJlYWtHLmV4ZWModGhpcy5pbnB1dCkpICYmIG1hdGNoLmluZGV4IDwgdGhpcy5wb3MpIHsrK3RoaXMuY3VyTGluZTt0aGlzLmxpbmVTdGFydCA9IG1hdGNoLmluZGV4ICsgbWF0Y2hbMF0ubGVuZ3RoO319aWYodGhpcy5vcHRpb25zLm9uQ29tbWVudCl0aGlzLm9wdGlvbnMub25Db21tZW50KHRydWUsIHRoaXMuaW5wdXQuc2xpY2Uoc3RhcnQgKyAyLCBlbmQpLCBzdGFydCwgdGhpcy5wb3MsIHN0YXJ0TG9jLCB0aGlzLm9wdGlvbnMubG9jYXRpb25zICYmIHRoaXMuY3VyUG9zaXRpb24oKSk7fTtwcC5za2lwTGluZUNvbW1lbnQgPSBmdW5jdGlvbihzdGFydFNraXApe3ZhciBzdGFydD10aGlzLnBvczt2YXIgc3RhcnRMb2M9dGhpcy5vcHRpb25zLm9uQ29tbWVudCAmJiB0aGlzLm9wdGlvbnMubG9jYXRpb25zICYmIHRoaXMuY3VyUG9zaXRpb24oKTt2YXIgY2g9dGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICs9IHN0YXJ0U2tpcCk7d2hpbGUodGhpcy5wb3MgPCB0aGlzLmlucHV0Lmxlbmd0aCAmJiBjaCAhPT0gMTAgJiYgY2ggIT09IDEzICYmIGNoICE9PSA4MjMyICYmIGNoICE9PSA4MjMzKSB7Kyt0aGlzLnBvcztjaCA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyk7fWlmKHRoaXMub3B0aW9ucy5vbkNvbW1lbnQpdGhpcy5vcHRpb25zLm9uQ29tbWVudChmYWxzZSwgdGhpcy5pbnB1dC5zbGljZShzdGFydCArIHN0YXJ0U2tpcCwgdGhpcy5wb3MpLCBzdGFydCwgdGhpcy5wb3MsIHN0YXJ0TG9jLCB0aGlzLm9wdGlvbnMubG9jYXRpb25zICYmIHRoaXMuY3VyUG9zaXRpb24oKSk7fTtwcC5za2lwU3BhY2UgPSBmdW5jdGlvbigpe3doaWxlKHRoaXMucG9zIDwgdGhpcy5pbnB1dC5sZW5ndGgpIHt2YXIgY2g9dGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zKTtpZihjaCA9PT0gMzIpeysrdGhpcy5wb3M7fWVsc2UgaWYoY2ggPT09IDEzKXsrK3RoaXMucG9zO3ZhciBuZXh0PXRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyk7aWYobmV4dCA9PT0gMTApeysrdGhpcy5wb3M7fWlmKHRoaXMub3B0aW9ucy5sb2NhdGlvbnMpeysrdGhpcy5jdXJMaW5lO3RoaXMubGluZVN0YXJ0ID0gdGhpcy5wb3M7fX1lbHNlIGlmKGNoID09PSAxMCB8fCBjaCA9PT0gODIzMiB8fCBjaCA9PT0gODIzMyl7Kyt0aGlzLnBvcztpZih0aGlzLm9wdGlvbnMubG9jYXRpb25zKXsrK3RoaXMuY3VyTGluZTt0aGlzLmxpbmVTdGFydCA9IHRoaXMucG9zO319ZWxzZSBpZihjaCA+IDggJiYgY2ggPCAxNCl7Kyt0aGlzLnBvczt9ZWxzZSBpZihjaCA9PT0gNDcpe3ZhciBuZXh0PXRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIDEpO2lmKG5leHQgPT09IDQyKXt0aGlzLnNraXBCbG9ja0NvbW1lbnQoKTt9ZWxzZSBpZihuZXh0ID09PSA0Nyl7dGhpcy5za2lwTGluZUNvbW1lbnQoMik7fWVsc2UgYnJlYWs7fWVsc2UgaWYoY2ggPT09IDE2MCl7Kyt0aGlzLnBvczt9ZWxzZSBpZihjaCA+PSA1NzYwICYmIG5vbkFTQ0lJd2hpdGVzcGFjZS50ZXN0KFN0cmluZy5mcm9tQ2hhckNvZGUoY2gpKSl7Kyt0aGlzLnBvczt9ZWxzZSB7YnJlYWs7fX19O3BwLmZpbmlzaFRva2VuID0gZnVuY3Rpb24odHlwZSwgdmFsKXt0aGlzLmVuZCA9IHRoaXMucG9zO2lmKHRoaXMub3B0aW9ucy5sb2NhdGlvbnMpdGhpcy5lbmRMb2MgPSB0aGlzLmN1clBvc2l0aW9uKCk7dmFyIHByZXZUeXBlPXRoaXMudHlwZTt0aGlzLnR5cGUgPSB0eXBlO3RoaXMudmFsdWUgPSB2YWw7dGhpcy51cGRhdGVDb250ZXh0KHByZXZUeXBlKTt9O3BwLnJlYWRUb2tlbl9kb3QgPSBmdW5jdGlvbigpe3ZhciBuZXh0PXRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIDEpO2lmKG5leHQgPj0gNDggJiYgbmV4dCA8PSA1NylyZXR1cm4gdGhpcy5yZWFkTnVtYmVyKHRydWUpO3ZhciBuZXh0Mj10aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAyKTtpZih0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNiAmJiBuZXh0ID09PSA0NiAmJiBuZXh0MiA9PT0gNDYpe3RoaXMucG9zICs9IDM7cmV0dXJuIHRoaXMuZmluaXNoVG9rZW4odHQuZWxsaXBzaXMpO31lbHNlIHsrK3RoaXMucG9zO3JldHVybiB0aGlzLmZpbmlzaFRva2VuKHR0LmRvdCk7fX07cHAucmVhZFRva2VuX3NsYXNoID0gZnVuY3Rpb24oKXt2YXIgbmV4dD10aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAxKTtpZih0aGlzLmV4cHJBbGxvd2VkKXsrK3RoaXMucG9zO3JldHVybiB0aGlzLnJlYWRSZWdleHAoKTt9aWYobmV4dCA9PT0gNjEpcmV0dXJuIHRoaXMuZmluaXNoT3AodHQuYXNzaWduLCAyKTtyZXR1cm4gdGhpcy5maW5pc2hPcCh0dC5zbGFzaCwgMSk7fTtwcC5yZWFkVG9rZW5fbXVsdF9tb2R1bG8gPSBmdW5jdGlvbihjb2RlKXt2YXIgbmV4dD10aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAxKTtpZihuZXh0ID09PSA2MSlyZXR1cm4gdGhpcy5maW5pc2hPcCh0dC5hc3NpZ24sIDIpO3JldHVybiB0aGlzLmZpbmlzaE9wKGNvZGUgPT09IDQyP3R0LnN0YXI6dHQubW9kdWxvLCAxKTt9O3BwLnJlYWRUb2tlbl9waXBlX2FtcCA9IGZ1bmN0aW9uKGNvZGUpe3ZhciBuZXh0PXRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIDEpO2lmKG5leHQgPT09IGNvZGUpcmV0dXJuIHRoaXMuZmluaXNoT3AoY29kZSA9PT0gMTI0P3R0LmxvZ2ljYWxPUjp0dC5sb2dpY2FsQU5ELCAyKTtpZihuZXh0ID09PSA2MSlyZXR1cm4gdGhpcy5maW5pc2hPcCh0dC5hc3NpZ24sIDIpO3JldHVybiB0aGlzLmZpbmlzaE9wKGNvZGUgPT09IDEyND90dC5iaXR3aXNlT1I6dHQuYml0d2lzZUFORCwgMSk7fTtwcC5yZWFkVG9rZW5fY2FyZXQgPSBmdW5jdGlvbigpe3ZhciBuZXh0PXRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIDEpO2lmKG5leHQgPT09IDYxKXJldHVybiB0aGlzLmZpbmlzaE9wKHR0LmFzc2lnbiwgMik7cmV0dXJuIHRoaXMuZmluaXNoT3AodHQuYml0d2lzZVhPUiwgMSk7fTtwcC5yZWFkVG9rZW5fcGx1c19taW4gPSBmdW5jdGlvbihjb2RlKXt2YXIgbmV4dD10aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAxKTtpZihuZXh0ID09PSBjb2RlKXtpZihuZXh0ID09IDQ1ICYmIHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIDIpID09IDYyICYmIGxpbmVCcmVhay50ZXN0KHRoaXMuaW5wdXQuc2xpY2UodGhpcy5sYXN0VG9rRW5kLCB0aGlzLnBvcykpKXt0aGlzLnNraXBMaW5lQ29tbWVudCgzKTt0aGlzLnNraXBTcGFjZSgpO3JldHVybiB0aGlzLm5leHRUb2tlbigpO31yZXR1cm4gdGhpcy5maW5pc2hPcCh0dC5pbmNEZWMsIDIpO31pZihuZXh0ID09PSA2MSlyZXR1cm4gdGhpcy5maW5pc2hPcCh0dC5hc3NpZ24sIDIpO3JldHVybiB0aGlzLmZpbmlzaE9wKHR0LnBsdXNNaW4sIDEpO307cHAucmVhZFRva2VuX2x0X2d0ID0gZnVuY3Rpb24oY29kZSl7dmFyIG5leHQ9dGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMSk7dmFyIHNpemU9MTtpZihuZXh0ID09PSBjb2RlKXtzaXplID0gY29kZSA9PT0gNjIgJiYgdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMikgPT09IDYyPzM6MjtpZih0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyBzaXplKSA9PT0gNjEpcmV0dXJuIHRoaXMuZmluaXNoT3AodHQuYXNzaWduLCBzaXplICsgMSk7cmV0dXJuIHRoaXMuZmluaXNoT3AodHQuYml0U2hpZnQsIHNpemUpO31pZihuZXh0ID09IDMzICYmIGNvZGUgPT0gNjAgJiYgdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMikgPT0gNDUgJiYgdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMykgPT0gNDUpe2lmKHRoaXMuaW5Nb2R1bGUpdGhpcy51bmV4cGVjdGVkKCk7dGhpcy5za2lwTGluZUNvbW1lbnQoNCk7dGhpcy5za2lwU3BhY2UoKTtyZXR1cm4gdGhpcy5uZXh0VG9rZW4oKTt9aWYobmV4dCA9PT0gNjEpc2l6ZSA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIDIpID09PSA2MT8zOjI7cmV0dXJuIHRoaXMuZmluaXNoT3AodHQucmVsYXRpb25hbCwgc2l6ZSk7fTtwcC5yZWFkVG9rZW5fZXFfZXhjbCA9IGZ1bmN0aW9uKGNvZGUpe3ZhciBuZXh0PXRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIDEpO2lmKG5leHQgPT09IDYxKXJldHVybiB0aGlzLmZpbmlzaE9wKHR0LmVxdWFsaXR5LCB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAyKSA9PT0gNjE/MzoyKTtpZihjb2RlID09PSA2MSAmJiBuZXh0ID09PSA2MiAmJiB0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNil7dGhpcy5wb3MgKz0gMjtyZXR1cm4gdGhpcy5maW5pc2hUb2tlbih0dC5hcnJvdyk7fXJldHVybiB0aGlzLmZpbmlzaE9wKGNvZGUgPT09IDYxP3R0LmVxOnR0LnByZWZpeCwgMSk7fTtwcC5nZXRUb2tlbkZyb21Db2RlID0gZnVuY3Rpb24oY29kZSl7c3dpdGNoKGNvZGUpe2Nhc2UgNDY6cmV0dXJuIHRoaXMucmVhZFRva2VuX2RvdCgpO2Nhc2UgNDA6Kyt0aGlzLnBvcztyZXR1cm4gdGhpcy5maW5pc2hUb2tlbih0dC5wYXJlbkwpO2Nhc2UgNDE6Kyt0aGlzLnBvcztyZXR1cm4gdGhpcy5maW5pc2hUb2tlbih0dC5wYXJlblIpO2Nhc2UgNTk6Kyt0aGlzLnBvcztyZXR1cm4gdGhpcy5maW5pc2hUb2tlbih0dC5zZW1pKTtjYXNlIDQ0OisrdGhpcy5wb3M7cmV0dXJuIHRoaXMuZmluaXNoVG9rZW4odHQuY29tbWEpO2Nhc2UgOTE6Kyt0aGlzLnBvcztyZXR1cm4gdGhpcy5maW5pc2hUb2tlbih0dC5icmFja2V0TCk7Y2FzZSA5MzorK3RoaXMucG9zO3JldHVybiB0aGlzLmZpbmlzaFRva2VuKHR0LmJyYWNrZXRSKTtjYXNlIDEyMzorK3RoaXMucG9zO3JldHVybiB0aGlzLmZpbmlzaFRva2VuKHR0LmJyYWNlTCk7Y2FzZSAxMjU6Kyt0aGlzLnBvcztyZXR1cm4gdGhpcy5maW5pc2hUb2tlbih0dC5icmFjZVIpO2Nhc2UgNTg6Kyt0aGlzLnBvcztyZXR1cm4gdGhpcy5maW5pc2hUb2tlbih0dC5jb2xvbik7Y2FzZSA2MzorK3RoaXMucG9zO3JldHVybiB0aGlzLmZpbmlzaFRva2VuKHR0LnF1ZXN0aW9uKTtjYXNlIDk2OmlmKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA8IDYpYnJlYWs7Kyt0aGlzLnBvcztyZXR1cm4gdGhpcy5maW5pc2hUb2tlbih0dC5iYWNrUXVvdGUpO2Nhc2UgNDg6dmFyIG5leHQ9dGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMSk7aWYobmV4dCA9PT0gMTIwIHx8IG5leHQgPT09IDg4KXJldHVybiB0aGlzLnJlYWRSYWRpeE51bWJlcigxNik7aWYodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYpe2lmKG5leHQgPT09IDExMSB8fCBuZXh0ID09PSA3OSlyZXR1cm4gdGhpcy5yZWFkUmFkaXhOdW1iZXIoOCk7aWYobmV4dCA9PT0gOTggfHwgbmV4dCA9PT0gNjYpcmV0dXJuIHRoaXMucmVhZFJhZGl4TnVtYmVyKDIpO31jYXNlIDQ5OmNhc2UgNTA6Y2FzZSA1MTpjYXNlIDUyOmNhc2UgNTM6Y2FzZSA1NDpjYXNlIDU1OmNhc2UgNTY6Y2FzZSA1NzpyZXR1cm4gdGhpcy5yZWFkTnVtYmVyKGZhbHNlKTtjYXNlIDM0OmNhc2UgMzk6cmV0dXJuIHRoaXMucmVhZFN0cmluZyhjb2RlKTtjYXNlIDQ3OnJldHVybiB0aGlzLnJlYWRUb2tlbl9zbGFzaCgpO2Nhc2UgMzc6Y2FzZSA0MjpyZXR1cm4gdGhpcy5yZWFkVG9rZW5fbXVsdF9tb2R1bG8oY29kZSk7Y2FzZSAxMjQ6Y2FzZSAzODpyZXR1cm4gdGhpcy5yZWFkVG9rZW5fcGlwZV9hbXAoY29kZSk7Y2FzZSA5NDpyZXR1cm4gdGhpcy5yZWFkVG9rZW5fY2FyZXQoKTtjYXNlIDQzOmNhc2UgNDU6cmV0dXJuIHRoaXMucmVhZFRva2VuX3BsdXNfbWluKGNvZGUpO2Nhc2UgNjA6Y2FzZSA2MjpyZXR1cm4gdGhpcy5yZWFkVG9rZW5fbHRfZ3QoY29kZSk7Y2FzZSA2MTpjYXNlIDMzOnJldHVybiB0aGlzLnJlYWRUb2tlbl9lcV9leGNsKGNvZGUpO2Nhc2UgMTI2OnJldHVybiB0aGlzLmZpbmlzaE9wKHR0LnByZWZpeCwgMSk7fXRoaXMucmFpc2UodGhpcy5wb3MsIFwiVW5leHBlY3RlZCBjaGFyYWN0ZXIgJ1wiICsgY29kZVBvaW50VG9TdHJpbmcoY29kZSkgKyBcIidcIik7fTtwcC5maW5pc2hPcCA9IGZ1bmN0aW9uKHR5cGUsIHNpemUpe3ZhciBzdHI9dGhpcy5pbnB1dC5zbGljZSh0aGlzLnBvcywgdGhpcy5wb3MgKyBzaXplKTt0aGlzLnBvcyArPSBzaXplO3JldHVybiB0aGlzLmZpbmlzaFRva2VuKHR5cGUsIHN0cik7fTt2YXIgcmVnZXhwVW5pY29kZVN1cHBvcnQ9ZmFsc2U7dHJ5e25ldyBSZWdFeHAoXCLvv79cIiwgXCJ1XCIpO3JlZ2V4cFVuaWNvZGVTdXBwb3J0ID0gdHJ1ZTt9Y2F0Y2goZSkge31wcC5yZWFkUmVnZXhwID0gZnVuY3Rpb24oKXt2YXIgZXNjYXBlZD11bmRlZmluZWQsIGluQ2xhc3M9dW5kZWZpbmVkLCBzdGFydD10aGlzLnBvcztmb3IoOzspIHtpZih0aGlzLnBvcyA+PSB0aGlzLmlucHV0Lmxlbmd0aCl0aGlzLnJhaXNlKHN0YXJ0LCBcIlVudGVybWluYXRlZCByZWd1bGFyIGV4cHJlc3Npb25cIik7dmFyIGNoPXRoaXMuaW5wdXQuY2hhckF0KHRoaXMucG9zKTtpZihsaW5lQnJlYWsudGVzdChjaCkpdGhpcy5yYWlzZShzdGFydCwgXCJVbnRlcm1pbmF0ZWQgcmVndWxhciBleHByZXNzaW9uXCIpO2lmKCFlc2NhcGVkKXtpZihjaCA9PT0gXCJbXCIpaW5DbGFzcyA9IHRydWU7ZWxzZSBpZihjaCA9PT0gXCJdXCIgJiYgaW5DbGFzcylpbkNsYXNzID0gZmFsc2U7ZWxzZSBpZihjaCA9PT0gXCIvXCIgJiYgIWluQ2xhc3MpYnJlYWs7ZXNjYXBlZCA9IGNoID09PSBcIlxcXFxcIjt9ZWxzZSBlc2NhcGVkID0gZmFsc2U7Kyt0aGlzLnBvczt9dmFyIGNvbnRlbnQ9dGhpcy5pbnB1dC5zbGljZShzdGFydCwgdGhpcy5wb3MpOysrdGhpcy5wb3M7dmFyIG1vZHM9dGhpcy5yZWFkV29yZDEoKTt2YXIgdG1wPWNvbnRlbnQ7aWYobW9kcyl7dmFyIHZhbGlkRmxhZ3M9L15bZ21zaXldKiQvO2lmKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KXZhbGlkRmxhZ3MgPSAvXltnbXNpeXVdKiQvO2lmKCF2YWxpZEZsYWdzLnRlc3QobW9kcykpdGhpcy5yYWlzZShzdGFydCwgXCJJbnZhbGlkIHJlZ3VsYXIgZXhwcmVzc2lvbiBmbGFnXCIpO2lmKG1vZHMuaW5kZXhPZihcInVcIikgPj0gMCAmJiAhcmVnZXhwVW5pY29kZVN1cHBvcnQpe3RtcCA9IHRtcC5yZXBsYWNlKC9cXFxcdShbYS1mQS1GMC05XXs0fSl8XFxcXHVcXHsoWzAtOWEtZkEtRl0rKVxcfXxbXFx1RDgwMC1cXHVEQkZGXVtcXHVEQzAwLVxcdURGRkZdL2csIFwieFwiKTt9fXZhciB2YWx1ZT1udWxsO2lmKCFpc1JoaW5vKXt0cnl7bmV3IFJlZ0V4cCh0bXApO31jYXRjaChlKSB7aWYoZSBpbnN0YW5jZW9mIFN5bnRheEVycm9yKXRoaXMucmFpc2Uoc3RhcnQsIFwiRXJyb3IgcGFyc2luZyByZWd1bGFyIGV4cHJlc3Npb246IFwiICsgZS5tZXNzYWdlKTt0aGlzLnJhaXNlKGUpO310cnl7dmFsdWUgPSBuZXcgUmVnRXhwKGNvbnRlbnQsIG1vZHMpO31jYXRjaChlcnIpIHt9fXJldHVybiB0aGlzLmZpbmlzaFRva2VuKHR0LnJlZ2V4cCwge3BhdHRlcm46Y29udGVudCwgZmxhZ3M6bW9kcywgdmFsdWU6dmFsdWV9KTt9O3BwLnJlYWRJbnQgPSBmdW5jdGlvbihyYWRpeCwgbGVuKXt2YXIgc3RhcnQ9dGhpcy5wb3MsIHRvdGFsPTA7Zm9yKHZhciBpPTAsIGU9bGVuID09IG51bGw/SW5maW5pdHk6bGVuOyBpIDwgZTsgKytpKSB7dmFyIGNvZGU9dGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zKSwgdmFsPXVuZGVmaW5lZDtpZihjb2RlID49IDk3KXZhbCA9IGNvZGUgLSA5NyArIDEwO2Vsc2UgaWYoY29kZSA+PSA2NSl2YWwgPSBjb2RlIC0gNjUgKyAxMDtlbHNlIGlmKGNvZGUgPj0gNDggJiYgY29kZSA8PSA1Nyl2YWwgPSBjb2RlIC0gNDg7ZWxzZSB2YWwgPSBJbmZpbml0eTtpZih2YWwgPj0gcmFkaXgpYnJlYWs7Kyt0aGlzLnBvczt0b3RhbCA9IHRvdGFsICogcmFkaXggKyB2YWw7fWlmKHRoaXMucG9zID09PSBzdGFydCB8fCBsZW4gIT0gbnVsbCAmJiB0aGlzLnBvcyAtIHN0YXJ0ICE9PSBsZW4pcmV0dXJuIG51bGw7cmV0dXJuIHRvdGFsO307cHAucmVhZFJhZGl4TnVtYmVyID0gZnVuY3Rpb24ocmFkaXgpe3RoaXMucG9zICs9IDI7dmFyIHZhbD10aGlzLnJlYWRJbnQocmFkaXgpO2lmKHZhbCA9PSBudWxsKXRoaXMucmFpc2UodGhpcy5zdGFydCArIDIsIFwiRXhwZWN0ZWQgbnVtYmVyIGluIHJhZGl4IFwiICsgcmFkaXgpO2lmKGlzSWRlbnRpZmllclN0YXJ0KHRoaXMuZnVsbENoYXJDb2RlQXRQb3MoKSkpdGhpcy5yYWlzZSh0aGlzLnBvcywgXCJJZGVudGlmaWVyIGRpcmVjdGx5IGFmdGVyIG51bWJlclwiKTtyZXR1cm4gdGhpcy5maW5pc2hUb2tlbih0dC5udW0sIHZhbCk7fTtwcC5yZWFkTnVtYmVyID0gZnVuY3Rpb24oc3RhcnRzV2l0aERvdCl7dmFyIHN0YXJ0PXRoaXMucG9zLCBpc0Zsb2F0PWZhbHNlLCBvY3RhbD10aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MpID09PSA0ODtpZighc3RhcnRzV2l0aERvdCAmJiB0aGlzLnJlYWRJbnQoMTApID09PSBudWxsKXRoaXMucmFpc2Uoc3RhcnQsIFwiSW52YWxpZCBudW1iZXJcIik7aWYodGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zKSA9PT0gNDYpeysrdGhpcy5wb3M7dGhpcy5yZWFkSW50KDEwKTtpc0Zsb2F0ID0gdHJ1ZTt9dmFyIG5leHQ9dGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zKTtpZihuZXh0ID09PSA2OSB8fCBuZXh0ID09PSAxMDEpe25leHQgPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQoKyt0aGlzLnBvcyk7aWYobmV4dCA9PT0gNDMgfHwgbmV4dCA9PT0gNDUpKyt0aGlzLnBvcztpZih0aGlzLnJlYWRJbnQoMTApID09PSBudWxsKXRoaXMucmFpc2Uoc3RhcnQsIFwiSW52YWxpZCBudW1iZXJcIik7aXNGbG9hdCA9IHRydWU7fWlmKGlzSWRlbnRpZmllclN0YXJ0KHRoaXMuZnVsbENoYXJDb2RlQXRQb3MoKSkpdGhpcy5yYWlzZSh0aGlzLnBvcywgXCJJZGVudGlmaWVyIGRpcmVjdGx5IGFmdGVyIG51bWJlclwiKTt2YXIgc3RyPXRoaXMuaW5wdXQuc2xpY2Uoc3RhcnQsIHRoaXMucG9zKSwgdmFsPXVuZGVmaW5lZDtpZihpc0Zsb2F0KXZhbCA9IHBhcnNlRmxvYXQoc3RyKTtlbHNlIGlmKCFvY3RhbCB8fCBzdHIubGVuZ3RoID09PSAxKXZhbCA9IHBhcnNlSW50KHN0ciwgMTApO2Vsc2UgaWYoL1s4OV0vLnRlc3Qoc3RyKSB8fCB0aGlzLnN0cmljdCl0aGlzLnJhaXNlKHN0YXJ0LCBcIkludmFsaWQgbnVtYmVyXCIpO2Vsc2UgdmFsID0gcGFyc2VJbnQoc3RyLCA4KTtyZXR1cm4gdGhpcy5maW5pc2hUb2tlbih0dC5udW0sIHZhbCk7fTtwcC5yZWFkQ29kZVBvaW50ID0gZnVuY3Rpb24oKXt2YXIgY2g9dGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zKSwgY29kZT11bmRlZmluZWQ7aWYoY2ggPT09IDEyMyl7aWYodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uIDwgNil0aGlzLnVuZXhwZWN0ZWQoKTsrK3RoaXMucG9zO2NvZGUgPSB0aGlzLnJlYWRIZXhDaGFyKHRoaXMuaW5wdXQuaW5kZXhPZihcIn1cIiwgdGhpcy5wb3MpIC0gdGhpcy5wb3MpOysrdGhpcy5wb3M7aWYoY29kZSA+IDExMTQxMTEpdGhpcy51bmV4cGVjdGVkKCk7fWVsc2Uge2NvZGUgPSB0aGlzLnJlYWRIZXhDaGFyKDQpO31yZXR1cm4gY29kZTt9O2Z1bmN0aW9uIGNvZGVQb2ludFRvU3RyaW5nKGNvZGUpe2lmKGNvZGUgPD0gNjU1MzUpe3JldHVybiBTdHJpbmcuZnJvbUNoYXJDb2RlKGNvZGUpO31yZXR1cm4gU3RyaW5nLmZyb21DaGFyQ29kZSgoY29kZSAtIDY1NTM2ID4+IDEwKSArIDU1Mjk2LCAoY29kZSAtIDY1NTM2ICYgMTAyMykgKyA1NjMyMCk7fXBwLnJlYWRTdHJpbmcgPSBmdW5jdGlvbihxdW90ZSl7dmFyIG91dD1cIlwiLCBjaHVua1N0YXJ0PSsrdGhpcy5wb3M7Zm9yKDs7KSB7aWYodGhpcy5wb3MgPj0gdGhpcy5pbnB1dC5sZW5ndGgpdGhpcy5yYWlzZSh0aGlzLnN0YXJ0LCBcIlVudGVybWluYXRlZCBzdHJpbmcgY29uc3RhbnRcIik7dmFyIGNoPXRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyk7aWYoY2ggPT09IHF1b3RlKWJyZWFrO2lmKGNoID09PSA5Mil7b3V0ICs9IHRoaXMuaW5wdXQuc2xpY2UoY2h1bmtTdGFydCwgdGhpcy5wb3MpO291dCArPSB0aGlzLnJlYWRFc2NhcGVkQ2hhcigpO2NodW5rU3RhcnQgPSB0aGlzLnBvczt9ZWxzZSB7aWYoaXNOZXdMaW5lKGNoKSl0aGlzLnJhaXNlKHRoaXMuc3RhcnQsIFwiVW50ZXJtaW5hdGVkIHN0cmluZyBjb25zdGFudFwiKTsrK3RoaXMucG9zO319b3V0ICs9IHRoaXMuaW5wdXQuc2xpY2UoY2h1bmtTdGFydCwgdGhpcy5wb3MrKyk7cmV0dXJuIHRoaXMuZmluaXNoVG9rZW4odHQuc3RyaW5nLCBvdXQpO307cHAucmVhZFRtcGxUb2tlbiA9IGZ1bmN0aW9uKCl7dmFyIG91dD1cIlwiLCBjaHVua1N0YXJ0PXRoaXMucG9zO2Zvcig7Oykge2lmKHRoaXMucG9zID49IHRoaXMuaW5wdXQubGVuZ3RoKXRoaXMucmFpc2UodGhpcy5zdGFydCwgXCJVbnRlcm1pbmF0ZWQgdGVtcGxhdGVcIik7dmFyIGNoPXRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyk7aWYoY2ggPT09IDk2IHx8IGNoID09PSAzNiAmJiB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAxKSA9PT0gMTIzKXtpZih0aGlzLnBvcyA9PT0gdGhpcy5zdGFydCAmJiB0aGlzLnR5cGUgPT09IHR0LnRlbXBsYXRlKXtpZihjaCA9PT0gMzYpe3RoaXMucG9zICs9IDI7cmV0dXJuIHRoaXMuZmluaXNoVG9rZW4odHQuZG9sbGFyQnJhY2VMKTt9ZWxzZSB7Kyt0aGlzLnBvcztyZXR1cm4gdGhpcy5maW5pc2hUb2tlbih0dC5iYWNrUXVvdGUpO319b3V0ICs9IHRoaXMuaW5wdXQuc2xpY2UoY2h1bmtTdGFydCwgdGhpcy5wb3MpO3JldHVybiB0aGlzLmZpbmlzaFRva2VuKHR0LnRlbXBsYXRlLCBvdXQpO31pZihjaCA9PT0gOTIpe291dCArPSB0aGlzLmlucHV0LnNsaWNlKGNodW5rU3RhcnQsIHRoaXMucG9zKTtvdXQgKz0gdGhpcy5yZWFkRXNjYXBlZENoYXIoKTtjaHVua1N0YXJ0ID0gdGhpcy5wb3M7fWVsc2UgaWYoaXNOZXdMaW5lKGNoKSl7b3V0ICs9IHRoaXMuaW5wdXQuc2xpY2UoY2h1bmtTdGFydCwgdGhpcy5wb3MpOysrdGhpcy5wb3M7aWYoY2ggPT09IDEzICYmIHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcykgPT09IDEwKXsrK3RoaXMucG9zO291dCArPSBcIlxcblwiO31lbHNlIHtvdXQgKz0gU3RyaW5nLmZyb21DaGFyQ29kZShjaCk7fWlmKHRoaXMub3B0aW9ucy5sb2NhdGlvbnMpeysrdGhpcy5jdXJMaW5lO3RoaXMubGluZVN0YXJ0ID0gdGhpcy5wb3M7fWNodW5rU3RhcnQgPSB0aGlzLnBvczt9ZWxzZSB7Kyt0aGlzLnBvczt9fX07cHAucmVhZEVzY2FwZWRDaGFyID0gZnVuY3Rpb24oKXt2YXIgY2g9dGhpcy5pbnB1dC5jaGFyQ29kZUF0KCsrdGhpcy5wb3MpO3ZhciBvY3RhbD0vXlswLTddKy8uZXhlYyh0aGlzLmlucHV0LnNsaWNlKHRoaXMucG9zLCB0aGlzLnBvcyArIDMpKTtpZihvY3RhbClvY3RhbCA9IG9jdGFsWzBdO3doaWxlKG9jdGFsICYmIHBhcnNlSW50KG9jdGFsLCA4KSA+IDI1NSkgb2N0YWwgPSBvY3RhbC5zbGljZSgwLCAtMSk7aWYob2N0YWwgPT09IFwiMFwiKW9jdGFsID0gbnVsbDsrK3RoaXMucG9zO2lmKG9jdGFsKXtpZih0aGlzLnN0cmljdCl0aGlzLnJhaXNlKHRoaXMucG9zIC0gMiwgXCJPY3RhbCBsaXRlcmFsIGluIHN0cmljdCBtb2RlXCIpO3RoaXMucG9zICs9IG9jdGFsLmxlbmd0aCAtIDE7cmV0dXJuIFN0cmluZy5mcm9tQ2hhckNvZGUocGFyc2VJbnQob2N0YWwsIDgpKTt9ZWxzZSB7c3dpdGNoKGNoKXtjYXNlIDExMDpyZXR1cm4gXCJcXG5cIjtjYXNlIDExNDpyZXR1cm4gXCJcXHJcIjtjYXNlIDEyMDpyZXR1cm4gU3RyaW5nLmZyb21DaGFyQ29kZSh0aGlzLnJlYWRIZXhDaGFyKDIpKTtjYXNlIDExNzpyZXR1cm4gY29kZVBvaW50VG9TdHJpbmcodGhpcy5yZWFkQ29kZVBvaW50KCkpO2Nhc2UgMTE2OnJldHVybiBcIlxcdFwiO2Nhc2UgOTg6cmV0dXJuIFwiXFxiXCI7Y2FzZSAxMTg6cmV0dXJuIFwiXFx1MDAwYlwiO2Nhc2UgMTAyOnJldHVybiBcIlxcZlwiO2Nhc2UgNDg6cmV0dXJuIFwiXFx1MDAwMFwiO2Nhc2UgMTM6aWYodGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zKSA9PT0gMTApKyt0aGlzLnBvcztjYXNlIDEwOmlmKHRoaXMub3B0aW9ucy5sb2NhdGlvbnMpe3RoaXMubGluZVN0YXJ0ID0gdGhpcy5wb3M7Kyt0aGlzLmN1ckxpbmU7fXJldHVybiBcIlwiO2RlZmF1bHQ6cmV0dXJuIFN0cmluZy5mcm9tQ2hhckNvZGUoY2gpO319fTtwcC5yZWFkSGV4Q2hhciA9IGZ1bmN0aW9uKGxlbil7dmFyIG49dGhpcy5yZWFkSW50KDE2LCBsZW4pO2lmKG4gPT09IG51bGwpdGhpcy5yYWlzZSh0aGlzLnN0YXJ0LCBcIkJhZCBjaGFyYWN0ZXIgZXNjYXBlIHNlcXVlbmNlXCIpO3JldHVybiBuO307dmFyIGNvbnRhaW5zRXNjO3BwLnJlYWRXb3JkMSA9IGZ1bmN0aW9uKCl7Y29udGFpbnNFc2MgPSBmYWxzZTt2YXIgd29yZD1cIlwiLCBmaXJzdD10cnVlLCBjaHVua1N0YXJ0PXRoaXMucG9zO3ZhciBhc3RyYWw9dGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDY7d2hpbGUodGhpcy5wb3MgPCB0aGlzLmlucHV0Lmxlbmd0aCkge3ZhciBjaD10aGlzLmZ1bGxDaGFyQ29kZUF0UG9zKCk7aWYoaXNJZGVudGlmaWVyQ2hhcihjaCwgYXN0cmFsKSl7dGhpcy5wb3MgKz0gY2ggPD0gNjU1MzU/MToyO31lbHNlIGlmKGNoID09PSA5Mil7Y29udGFpbnNFc2MgPSB0cnVlO3dvcmQgKz0gdGhpcy5pbnB1dC5zbGljZShjaHVua1N0YXJ0LCB0aGlzLnBvcyk7dmFyIGVzY1N0YXJ0PXRoaXMucG9zO2lmKHRoaXMuaW5wdXQuY2hhckNvZGVBdCgrK3RoaXMucG9zKSAhPSAxMTcpdGhpcy5yYWlzZSh0aGlzLnBvcywgXCJFeHBlY3RpbmcgVW5pY29kZSBlc2NhcGUgc2VxdWVuY2UgXFxcXHVYWFhYXCIpOysrdGhpcy5wb3M7dmFyIGVzYz10aGlzLnJlYWRDb2RlUG9pbnQoKTtpZighKGZpcnN0P2lzSWRlbnRpZmllclN0YXJ0OmlzSWRlbnRpZmllckNoYXIpKGVzYywgYXN0cmFsKSl0aGlzLnJhaXNlKGVzY1N0YXJ0LCBcIkludmFsaWQgVW5pY29kZSBlc2NhcGVcIik7d29yZCArPSBjb2RlUG9pbnRUb1N0cmluZyhlc2MpO2NodW5rU3RhcnQgPSB0aGlzLnBvczt9ZWxzZSB7YnJlYWs7fWZpcnN0ID0gZmFsc2U7fXJldHVybiB3b3JkICsgdGhpcy5pbnB1dC5zbGljZShjaHVua1N0YXJ0LCB0aGlzLnBvcyk7fTtwcC5yZWFkV29yZCA9IGZ1bmN0aW9uKCl7dmFyIHdvcmQ9dGhpcy5yZWFkV29yZDEoKTt2YXIgdHlwZT10dC5uYW1lO2lmKCh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNiB8fCAhY29udGFpbnNFc2MpICYmIHRoaXMuaXNLZXl3b3JkKHdvcmQpKXR5cGUgPSBrZXl3b3JkVHlwZXNbd29yZF07cmV0dXJuIHRoaXMuZmluaXNoVG9rZW4odHlwZSwgd29yZCk7fTt9LCB7XCIuL2lkZW50aWZpZXJcIjo3LCBcIi4vbG9jYXRpb25cIjo4LCBcIi4vc3RhdGVcIjoxMywgXCIuL3Rva2VudHlwZVwiOjE3LCBcIi4vd2hpdGVzcGFjZVwiOjE5fV0sIDE3OltmdW5jdGlvbihfZGVyZXFfLCBtb2R1bGUsIGV4cG9ydHMpe1widXNlIHN0cmljdFwiO3ZhciBfY2xhc3NDYWxsQ2hlY2s9ZnVuY3Rpb24gX2NsYXNzQ2FsbENoZWNrKGluc3RhbmNlLCBDb25zdHJ1Y3Rvcil7aWYoIShpbnN0YW5jZSBpbnN0YW5jZW9mIENvbnN0cnVjdG9yKSl7dGhyb3cgbmV3IFR5cGVFcnJvcihcIkNhbm5vdCBjYWxsIGEgY2xhc3MgYXMgYSBmdW5jdGlvblwiKTt9fTtleHBvcnRzLl9fZXNNb2R1bGUgPSB0cnVlO3ZhciBUb2tlblR5cGU9ZXhwb3J0cy5Ub2tlblR5cGUgPSBmdW5jdGlvbiBUb2tlblR5cGUobGFiZWwpe3ZhciBjb25mPWFyZ3VtZW50c1sxXSA9PT0gdW5kZWZpbmVkP3t9OmFyZ3VtZW50c1sxXTtfY2xhc3NDYWxsQ2hlY2sodGhpcywgVG9rZW5UeXBlKTt0aGlzLmxhYmVsID0gbGFiZWw7dGhpcy5rZXl3b3JkID0gY29uZi5rZXl3b3JkO3RoaXMuYmVmb3JlRXhwciA9ICEhY29uZi5iZWZvcmVFeHByO3RoaXMuc3RhcnRzRXhwciA9ICEhY29uZi5zdGFydHNFeHByO3RoaXMuaXNMb29wID0gISFjb25mLmlzTG9vcDt0aGlzLmlzQXNzaWduID0gISFjb25mLmlzQXNzaWduO3RoaXMucHJlZml4ID0gISFjb25mLnByZWZpeDt0aGlzLnBvc3RmaXggPSAhIWNvbmYucG9zdGZpeDt0aGlzLmJpbm9wID0gY29uZi5iaW5vcCB8fCBudWxsO3RoaXMudXBkYXRlQ29udGV4dCA9IG51bGw7fTtmdW5jdGlvbiBiaW5vcChuYW1lLCBwcmVjKXtyZXR1cm4gbmV3IFRva2VuVHlwZShuYW1lLCB7YmVmb3JlRXhwcjp0cnVlLCBiaW5vcDpwcmVjfSk7fXZhciBiZWZvcmVFeHByPXtiZWZvcmVFeHByOnRydWV9LCBzdGFydHNFeHByPXtzdGFydHNFeHByOnRydWV9O3ZhciB0eXBlcz17bnVtOm5ldyBUb2tlblR5cGUoXCJudW1cIiwgc3RhcnRzRXhwciksIHJlZ2V4cDpuZXcgVG9rZW5UeXBlKFwicmVnZXhwXCIsIHN0YXJ0c0V4cHIpLCBzdHJpbmc6bmV3IFRva2VuVHlwZShcInN0cmluZ1wiLCBzdGFydHNFeHByKSwgbmFtZTpuZXcgVG9rZW5UeXBlKFwibmFtZVwiLCBzdGFydHNFeHByKSwgZW9mOm5ldyBUb2tlblR5cGUoXCJlb2ZcIiksIGJyYWNrZXRMOm5ldyBUb2tlblR5cGUoXCJbXCIsIHtiZWZvcmVFeHByOnRydWUsIHN0YXJ0c0V4cHI6dHJ1ZX0pLCBicmFja2V0UjpuZXcgVG9rZW5UeXBlKFwiXVwiKSwgYnJhY2VMOm5ldyBUb2tlblR5cGUoXCJ7XCIsIHtiZWZvcmVFeHByOnRydWUsIHN0YXJ0c0V4cHI6dHJ1ZX0pLCBicmFjZVI6bmV3IFRva2VuVHlwZShcIn1cIiksIHBhcmVuTDpuZXcgVG9rZW5UeXBlKFwiKFwiLCB7YmVmb3JlRXhwcjp0cnVlLCBzdGFydHNFeHByOnRydWV9KSwgcGFyZW5SOm5ldyBUb2tlblR5cGUoXCIpXCIpLCBjb21tYTpuZXcgVG9rZW5UeXBlKFwiLFwiLCBiZWZvcmVFeHByKSwgc2VtaTpuZXcgVG9rZW5UeXBlKFwiO1wiLCBiZWZvcmVFeHByKSwgY29sb246bmV3IFRva2VuVHlwZShcIjpcIiwgYmVmb3JlRXhwciksIGRvdDpuZXcgVG9rZW5UeXBlKFwiLlwiKSwgcXVlc3Rpb246bmV3IFRva2VuVHlwZShcIj9cIiwgYmVmb3JlRXhwciksIGFycm93Om5ldyBUb2tlblR5cGUoXCI9PlwiLCBiZWZvcmVFeHByKSwgdGVtcGxhdGU6bmV3IFRva2VuVHlwZShcInRlbXBsYXRlXCIpLCBlbGxpcHNpczpuZXcgVG9rZW5UeXBlKFwiLi4uXCIsIGJlZm9yZUV4cHIpLCBiYWNrUXVvdGU6bmV3IFRva2VuVHlwZShcImBcIiwgc3RhcnRzRXhwciksIGRvbGxhckJyYWNlTDpuZXcgVG9rZW5UeXBlKFwiJHtcIiwge2JlZm9yZUV4cHI6dHJ1ZSwgc3RhcnRzRXhwcjp0cnVlfSksIGVxOm5ldyBUb2tlblR5cGUoXCI9XCIsIHtiZWZvcmVFeHByOnRydWUsIGlzQXNzaWduOnRydWV9KSwgYXNzaWduOm5ldyBUb2tlblR5cGUoXCJfPVwiLCB7YmVmb3JlRXhwcjp0cnVlLCBpc0Fzc2lnbjp0cnVlfSksIGluY0RlYzpuZXcgVG9rZW5UeXBlKFwiKysvLS1cIiwge3ByZWZpeDp0cnVlLCBwb3N0Zml4OnRydWUsIHN0YXJ0c0V4cHI6dHJ1ZX0pLCBwcmVmaXg6bmV3IFRva2VuVHlwZShcInByZWZpeFwiLCB7YmVmb3JlRXhwcjp0cnVlLCBwcmVmaXg6dHJ1ZSwgc3RhcnRzRXhwcjp0cnVlfSksIGxvZ2ljYWxPUjpiaW5vcChcInx8XCIsIDEpLCBsb2dpY2FsQU5EOmJpbm9wKFwiJiZcIiwgMiksIGJpdHdpc2VPUjpiaW5vcChcInxcIiwgMyksIGJpdHdpc2VYT1I6Ymlub3AoXCJeXCIsIDQpLCBiaXR3aXNlQU5EOmJpbm9wKFwiJlwiLCA1KSwgZXF1YWxpdHk6Ymlub3AoXCI9PS8hPVwiLCA2KSwgcmVsYXRpb25hbDpiaW5vcChcIjwvPlwiLCA3KSwgYml0U2hpZnQ6Ymlub3AoXCI8PC8+PlwiLCA4KSwgcGx1c01pbjpuZXcgVG9rZW5UeXBlKFwiKy8tXCIsIHtiZWZvcmVFeHByOnRydWUsIGJpbm9wOjksIHByZWZpeDp0cnVlLCBzdGFydHNFeHByOnRydWV9KSwgbW9kdWxvOmJpbm9wKFwiJVwiLCAxMCksIHN0YXI6Ymlub3AoXCIqXCIsIDEwKSwgc2xhc2g6Ymlub3AoXCIvXCIsIDEwKX07ZXhwb3J0cy50eXBlcyA9IHR5cGVzO3ZhciBrZXl3b3Jkcz17fTtleHBvcnRzLmtleXdvcmRzID0ga2V5d29yZHM7ZnVuY3Rpb24ga3cobmFtZSl7dmFyIG9wdGlvbnM9YXJndW1lbnRzWzFdID09PSB1bmRlZmluZWQ/e306YXJndW1lbnRzWzFdO29wdGlvbnMua2V5d29yZCA9IG5hbWU7a2V5d29yZHNbbmFtZV0gPSB0eXBlc1tcIl9cIiArIG5hbWVdID0gbmV3IFRva2VuVHlwZShuYW1lLCBvcHRpb25zKTt9a3coXCJicmVha1wiKTtrdyhcImNhc2VcIiwgYmVmb3JlRXhwcik7a3coXCJjYXRjaFwiKTtrdyhcImNvbnRpbnVlXCIpO2t3KFwiZGVidWdnZXJcIik7a3coXCJkZWZhdWx0XCIpO2t3KFwiZG9cIiwge2lzTG9vcDp0cnVlfSk7a3coXCJlbHNlXCIsIGJlZm9yZUV4cHIpO2t3KFwiZmluYWxseVwiKTtrdyhcImZvclwiLCB7aXNMb29wOnRydWV9KTtrdyhcImZ1bmN0aW9uXCIsIHN0YXJ0c0V4cHIpO2t3KFwiaWZcIik7a3coXCJyZXR1cm5cIiwgYmVmb3JlRXhwcik7a3coXCJzd2l0Y2hcIik7a3coXCJ0aHJvd1wiLCBiZWZvcmVFeHByKTtrdyhcInRyeVwiKTtrdyhcInZhclwiKTtrdyhcImxldFwiKTtrdyhcImNvbnN0XCIpO2t3KFwid2hpbGVcIiwge2lzTG9vcDp0cnVlfSk7a3coXCJ3aXRoXCIpO2t3KFwibmV3XCIsIHtiZWZvcmVFeHByOnRydWUsIHN0YXJ0c0V4cHI6dHJ1ZX0pO2t3KFwidGhpc1wiLCBzdGFydHNFeHByKTtrdyhcInN1cGVyXCIsIHN0YXJ0c0V4cHIpO2t3KFwiY2xhc3NcIik7a3coXCJleHRlbmRzXCIsIGJlZm9yZUV4cHIpO2t3KFwiZXhwb3J0XCIpO2t3KFwiaW1wb3J0XCIpO2t3KFwieWllbGRcIiwge2JlZm9yZUV4cHI6dHJ1ZSwgc3RhcnRzRXhwcjp0cnVlfSk7a3coXCJudWxsXCIsIHN0YXJ0c0V4cHIpO2t3KFwidHJ1ZVwiLCBzdGFydHNFeHByKTtrdyhcImZhbHNlXCIsIHN0YXJ0c0V4cHIpO2t3KFwiaW5cIiwge2JlZm9yZUV4cHI6dHJ1ZSwgYmlub3A6N30pO2t3KFwiaW5zdGFuY2VvZlwiLCB7YmVmb3JlRXhwcjp0cnVlLCBiaW5vcDo3fSk7a3coXCJ0eXBlb2ZcIiwge2JlZm9yZUV4cHI6dHJ1ZSwgcHJlZml4OnRydWUsIHN0YXJ0c0V4cHI6dHJ1ZX0pO2t3KFwidm9pZFwiLCB7YmVmb3JlRXhwcjp0cnVlLCBwcmVmaXg6dHJ1ZSwgc3RhcnRzRXhwcjp0cnVlfSk7a3coXCJkZWxldGVcIiwge2JlZm9yZUV4cHI6dHJ1ZSwgcHJlZml4OnRydWUsIHN0YXJ0c0V4cHI6dHJ1ZX0pO30sIHt9XSwgMTg6W2Z1bmN0aW9uKF9kZXJlcV8sIG1vZHVsZSwgZXhwb3J0cyl7XCJ1c2Ugc3RyaWN0XCI7ZXhwb3J0cy5pc0FycmF5ID0gaXNBcnJheTtleHBvcnRzLmhhcyA9IGhhcztleHBvcnRzLl9fZXNNb2R1bGUgPSB0cnVlO2Z1bmN0aW9uIGlzQXJyYXkob2JqKXtyZXR1cm4gT2JqZWN0LnByb3RvdHlwZS50b1N0cmluZy5jYWxsKG9iaikgPT09IFwiW29iamVjdCBBcnJheV1cIjt9ZnVuY3Rpb24gaGFzKG9iaiwgcHJvcE5hbWUpe3JldHVybiBPYmplY3QucHJvdG90eXBlLmhhc093blByb3BlcnR5LmNhbGwob2JqLCBwcm9wTmFtZSk7fX0sIHt9XSwgMTk6W2Z1bmN0aW9uKF9kZXJlcV8sIG1vZHVsZSwgZXhwb3J0cyl7XCJ1c2Ugc3RyaWN0XCI7ZXhwb3J0cy5pc05ld0xpbmUgPSBpc05ld0xpbmU7ZXhwb3J0cy5fX2VzTW9kdWxlID0gdHJ1ZTt2YXIgbGluZUJyZWFrPS9cXHJcXG4/fFxcbnxcXHUyMDI4fFxcdTIwMjkvO2V4cG9ydHMubGluZUJyZWFrID0gbGluZUJyZWFrO3ZhciBsaW5lQnJlYWtHPW5ldyBSZWdFeHAobGluZUJyZWFrLnNvdXJjZSwgXCJnXCIpO2V4cG9ydHMubGluZUJyZWFrRyA9IGxpbmVCcmVha0c7ZnVuY3Rpb24gaXNOZXdMaW5lKGNvZGUpe3JldHVybiBjb2RlID09PSAxMCB8fCBjb2RlID09PSAxMyB8fCBjb2RlID09PSA4MjMyIHx8IGNvZGUgPT0gODIzMzt9dmFyIG5vbkFTQ0lJd2hpdGVzcGFjZT0vW1xcdTE2ODBcXHUxODBlXFx1MjAwMC1cXHUyMDBhXFx1MjAyZlxcdTIwNWZcXHUzMDAwXFx1ZmVmZl0vO2V4cG9ydHMubm9uQVNDSUl3aGl0ZXNwYWNlID0gbm9uQVNDSUl3aGl0ZXNwYWNlO30sIHt9XX0sIHt9LCBbMV0pKDEpO30pO1xuXG59KS5jYWxsKHRoaXMsdHlwZW9mIGdsb2JhbCAhPT0gXCJ1bmRlZmluZWRcIiA/IGdsb2JhbCA6IHR5cGVvZiBzZWxmICE9PSBcInVuZGVmaW5lZFwiID8gc2VsZiA6IHR5cGVvZiB3aW5kb3cgIT09IFwidW5kZWZpbmVkXCIgPyB3aW5kb3cgOiB7fSlcbn0se31dLDM6W2Z1bmN0aW9uKF9kZXJlcV8sbW9kdWxlLGV4cG9ydHMpe1xuXCJ1c2Ugc3RyaWN0XCI7XG5cbm1vZHVsZS5leHBvcnRzID0gdHlwZW9mIGFjb3JuICE9IFwidW5kZWZpbmVkXCIgPyBhY29ybiA6IF9kZXJlcV8oXCJhY29yblwiKTtcblxufSx7XCJhY29yblwiOjJ9XSw0OltmdW5jdGlvbihfZGVyZXFfLG1vZHVsZSxleHBvcnRzKXtcblwidXNlIHN0cmljdFwiO1xuXG52YXIgTG9vc2VQYXJzZXIgPSBfZGVyZXFfKFwiLi9zdGF0ZVwiKS5Mb29zZVBhcnNlcjtcblxudmFyIGlzRHVtbXkgPSBfZGVyZXFfKFwiLi9wYXJzZXV0aWxcIikuaXNEdW1teTtcblxudmFyIHR0ID0gX2RlcmVxXyhcIi4uXCIpLnRva1R5cGVzO1xuXG52YXIgbHAgPSBMb29zZVBhcnNlci5wcm90b3R5cGU7XG5cbmxwLmNoZWNrTFZhbCA9IGZ1bmN0aW9uIChleHByLCBiaW5kaW5nKSB7XG4gIGlmICghZXhwcikgcmV0dXJuIGV4cHI7XG4gIHN3aXRjaCAoZXhwci50eXBlKSB7XG4gICAgY2FzZSBcIklkZW50aWZpZXJcIjpcbiAgICAgIHJldHVybiBleHByO1xuXG4gICAgY2FzZSBcIk1lbWJlckV4cHJlc3Npb25cIjpcbiAgICAgIHJldHVybiBiaW5kaW5nID8gdGhpcy5kdW1teUlkZW50KCkgOiBleHByO1xuXG4gICAgY2FzZSBcIlBhcmVudGhlc2l6ZWRFeHByZXNzaW9uXCI6XG4gICAgICBleHByLmV4cHJlc3Npb24gPSB0aGlzLmNoZWNrTFZhbChleHByLmV4cHJlc3Npb24sIGJpbmRpbmcpO1xuICAgICAgcmV0dXJuIGV4cHI7XG5cbiAgICAvLyBGSVhNRSByZWN1cnNpdmVseSBjaGVjayBjb250ZW50c1xuICAgIGNhc2UgXCJPYmplY3RQYXR0ZXJuXCI6XG4gICAgY2FzZSBcIkFycmF5UGF0dGVyblwiOlxuICAgIGNhc2UgXCJSZXN0RWxlbWVudFwiOlxuICAgIGNhc2UgXCJBc3NpZ25tZW50UGF0dGVyblwiOlxuICAgICAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KSByZXR1cm4gZXhwcjtcblxuICAgIGRlZmF1bHQ6XG4gICAgICByZXR1cm4gdGhpcy5kdW1teUlkZW50KCk7XG4gIH1cbn07XG5cbmxwLnBhcnNlRXhwcmVzc2lvbiA9IGZ1bmN0aW9uIChub0luKSB7XG4gIHZhciBzdGFydCA9IHRoaXMuc3RvcmVDdXJyZW50UG9zKCk7XG4gIHZhciBleHByID0gdGhpcy5wYXJzZU1heWJlQXNzaWduKG5vSW4pO1xuICBpZiAodGhpcy50b2sudHlwZSA9PT0gdHQuY29tbWEpIHtcbiAgICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlQXQoc3RhcnQpO1xuICAgIG5vZGUuZXhwcmVzc2lvbnMgPSBbZXhwcl07XG4gICAgd2hpbGUgKHRoaXMuZWF0KHR0LmNvbW1hKSkgbm9kZS5leHByZXNzaW9ucy5wdXNoKHRoaXMucGFyc2VNYXliZUFzc2lnbihub0luKSk7XG4gICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIlNlcXVlbmNlRXhwcmVzc2lvblwiKTtcbiAgfVxuICByZXR1cm4gZXhwcjtcbn07XG5cbmxwLnBhcnNlUGFyZW5FeHByZXNzaW9uID0gZnVuY3Rpb24gKCkge1xuICB0aGlzLnB1c2hDeCgpO1xuICB0aGlzLmV4cGVjdCh0dC5wYXJlbkwpO1xuICB2YXIgdmFsID0gdGhpcy5wYXJzZUV4cHJlc3Npb24oKTtcbiAgdGhpcy5wb3BDeCgpO1xuICB0aGlzLmV4cGVjdCh0dC5wYXJlblIpO1xuICByZXR1cm4gdmFsO1xufTtcblxubHAucGFyc2VNYXliZUFzc2lnbiA9IGZ1bmN0aW9uIChub0luKSB7XG4gIHZhciBzdGFydCA9IHRoaXMuc3RvcmVDdXJyZW50UG9zKCk7XG4gIHZhciBsZWZ0ID0gdGhpcy5wYXJzZU1heWJlQ29uZGl0aW9uYWwobm9Jbik7XG4gIGlmICh0aGlzLnRvay50eXBlLmlzQXNzaWduKSB7XG4gICAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0KTtcbiAgICBub2RlLm9wZXJhdG9yID0gdGhpcy50b2sudmFsdWU7XG4gICAgbm9kZS5sZWZ0ID0gdGhpcy50b2sudHlwZSA9PT0gdHQuZXEgPyB0aGlzLnRvQXNzaWduYWJsZShsZWZ0KSA6IHRoaXMuY2hlY2tMVmFsKGxlZnQpO1xuICAgIHRoaXMubmV4dCgpO1xuICAgIG5vZGUucmlnaHQgPSB0aGlzLnBhcnNlTWF5YmVBc3NpZ24obm9Jbik7XG4gICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkFzc2lnbm1lbnRFeHByZXNzaW9uXCIpO1xuICB9XG4gIHJldHVybiBsZWZ0O1xufTtcblxubHAucGFyc2VNYXliZUNvbmRpdGlvbmFsID0gZnVuY3Rpb24gKG5vSW4pIHtcbiAgdmFyIHN0YXJ0ID0gdGhpcy5zdG9yZUN1cnJlbnRQb3MoKTtcbiAgdmFyIGV4cHIgPSB0aGlzLnBhcnNlRXhwck9wcyhub0luKTtcbiAgaWYgKHRoaXMuZWF0KHR0LnF1ZXN0aW9uKSkge1xuICAgIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGVBdChzdGFydCk7XG4gICAgbm9kZS50ZXN0ID0gZXhwcjtcbiAgICBub2RlLmNvbnNlcXVlbnQgPSB0aGlzLnBhcnNlTWF5YmVBc3NpZ24oKTtcbiAgICBub2RlLmFsdGVybmF0ZSA9IHRoaXMuZXhwZWN0KHR0LmNvbG9uKSA/IHRoaXMucGFyc2VNYXliZUFzc2lnbihub0luKSA6IHRoaXMuZHVtbXlJZGVudCgpO1xuICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJDb25kaXRpb25hbEV4cHJlc3Npb25cIik7XG4gIH1cbiAgcmV0dXJuIGV4cHI7XG59O1xuXG5scC5wYXJzZUV4cHJPcHMgPSBmdW5jdGlvbiAobm9Jbikge1xuICB2YXIgc3RhcnQgPSB0aGlzLnN0b3JlQ3VycmVudFBvcygpO1xuICB2YXIgaW5kZW50ID0gdGhpcy5jdXJJbmRlbnQsXG4gICAgICBsaW5lID0gdGhpcy5jdXJMaW5lU3RhcnQ7XG4gIHJldHVybiB0aGlzLnBhcnNlRXhwck9wKHRoaXMucGFyc2VNYXliZVVuYXJ5KG5vSW4pLCBzdGFydCwgLTEsIG5vSW4sIGluZGVudCwgbGluZSk7XG59O1xuXG5scC5wYXJzZUV4cHJPcCA9IGZ1bmN0aW9uIChsZWZ0LCBzdGFydCwgbWluUHJlYywgbm9JbiwgaW5kZW50LCBsaW5lKSB7XG4gIGlmICh0aGlzLmN1ckxpbmVTdGFydCAhPSBsaW5lICYmIHRoaXMuY3VySW5kZW50IDwgaW5kZW50ICYmIHRoaXMudG9rZW5TdGFydHNMaW5lKCkpIHJldHVybiBsZWZ0O1xuICB2YXIgcHJlYyA9IHRoaXMudG9rLnR5cGUuYmlub3A7XG4gIGlmIChwcmVjICE9IG51bGwgJiYgKCFub0luIHx8IHRoaXMudG9rLnR5cGUgIT09IHR0Ll9pbikpIHtcbiAgICBpZiAocHJlYyA+IG1pblByZWMpIHtcbiAgICAgIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGVBdChzdGFydCk7XG4gICAgICBub2RlLmxlZnQgPSBsZWZ0O1xuICAgICAgbm9kZS5vcGVyYXRvciA9IHRoaXMudG9rLnZhbHVlO1xuICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICBpZiAodGhpcy5jdXJMaW5lU3RhcnQgIT0gbGluZSAmJiB0aGlzLmN1ckluZGVudCA8IGluZGVudCAmJiB0aGlzLnRva2VuU3RhcnRzTGluZSgpKSB7XG4gICAgICAgIG5vZGUucmlnaHQgPSB0aGlzLmR1bW15SWRlbnQoKTtcbiAgICAgIH0gZWxzZSB7XG4gICAgICAgIHZhciByaWdodFN0YXJ0ID0gdGhpcy5zdG9yZUN1cnJlbnRQb3MoKTtcbiAgICAgICAgbm9kZS5yaWdodCA9IHRoaXMucGFyc2VFeHByT3AodGhpcy5wYXJzZU1heWJlVW5hcnkobm9JbiksIHJpZ2h0U3RhcnQsIHByZWMsIG5vSW4sIGluZGVudCwgbGluZSk7XG4gICAgICB9XG4gICAgICB0aGlzLmZpbmlzaE5vZGUobm9kZSwgLyYmfFxcfFxcfC8udGVzdChub2RlLm9wZXJhdG9yKSA/IFwiTG9naWNhbEV4cHJlc3Npb25cIiA6IFwiQmluYXJ5RXhwcmVzc2lvblwiKTtcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlRXhwck9wKG5vZGUsIHN0YXJ0LCBtaW5QcmVjLCBub0luLCBpbmRlbnQsIGxpbmUpO1xuICAgIH1cbiAgfVxuICByZXR1cm4gbGVmdDtcbn07XG5cbmxwLnBhcnNlTWF5YmVVbmFyeSA9IGZ1bmN0aW9uIChub0luKSB7XG4gIGlmICh0aGlzLnRvay50eXBlLnByZWZpeCkge1xuICAgIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGUoKSxcbiAgICAgICAgdXBkYXRlID0gdGhpcy50b2sudHlwZSA9PT0gdHQuaW5jRGVjO1xuICAgIG5vZGUub3BlcmF0b3IgPSB0aGlzLnRvay52YWx1ZTtcbiAgICBub2RlLnByZWZpeCA9IHRydWU7XG4gICAgdGhpcy5uZXh0KCk7XG4gICAgbm9kZS5hcmd1bWVudCA9IHRoaXMucGFyc2VNYXliZVVuYXJ5KG5vSW4pO1xuICAgIGlmICh1cGRhdGUpIG5vZGUuYXJndW1lbnQgPSB0aGlzLmNoZWNrTFZhbChub2RlLmFyZ3VtZW50KTtcbiAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIHVwZGF0ZSA/IFwiVXBkYXRlRXhwcmVzc2lvblwiIDogXCJVbmFyeUV4cHJlc3Npb25cIik7XG4gIH0gZWxzZSBpZiAodGhpcy50b2sudHlwZSA9PT0gdHQuZWxsaXBzaXMpIHtcbiAgICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gICAgdGhpcy5uZXh0KCk7XG4gICAgbm9kZS5hcmd1bWVudCA9IHRoaXMucGFyc2VNYXliZVVuYXJ5KG5vSW4pO1xuICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJTcHJlYWRFbGVtZW50XCIpO1xuICB9XG4gIHZhciBzdGFydCA9IHRoaXMuc3RvcmVDdXJyZW50UG9zKCk7XG4gIHZhciBleHByID0gdGhpcy5wYXJzZUV4cHJTdWJzY3JpcHRzKCk7XG4gIHdoaWxlICh0aGlzLnRvay50eXBlLnBvc3RmaXggJiYgIXRoaXMuY2FuSW5zZXJ0U2VtaWNvbG9uKCkpIHtcbiAgICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlQXQoc3RhcnQpO1xuICAgIG5vZGUub3BlcmF0b3IgPSB0aGlzLnRvay52YWx1ZTtcbiAgICBub2RlLnByZWZpeCA9IGZhbHNlO1xuICAgIG5vZGUuYXJndW1lbnQgPSB0aGlzLmNoZWNrTFZhbChleHByKTtcbiAgICB0aGlzLm5leHQoKTtcbiAgICBleHByID0gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiVXBkYXRlRXhwcmVzc2lvblwiKTtcbiAgfVxuICByZXR1cm4gZXhwcjtcbn07XG5cbmxwLnBhcnNlRXhwclN1YnNjcmlwdHMgPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBzdGFydCA9IHRoaXMuc3RvcmVDdXJyZW50UG9zKCk7XG4gIHJldHVybiB0aGlzLnBhcnNlU3Vic2NyaXB0cyh0aGlzLnBhcnNlRXhwckF0b20oKSwgc3RhcnQsIGZhbHNlLCB0aGlzLmN1ckluZGVudCwgdGhpcy5jdXJMaW5lU3RhcnQpO1xufTtcblxubHAucGFyc2VTdWJzY3JpcHRzID0gZnVuY3Rpb24gKGJhc2UsIHN0YXJ0LCBub0NhbGxzLCBzdGFydEluZGVudCwgbGluZSkge1xuICBmb3IgKDs7KSB7XG4gICAgaWYgKHRoaXMuY3VyTGluZVN0YXJ0ICE9IGxpbmUgJiYgdGhpcy5jdXJJbmRlbnQgPD0gc3RhcnRJbmRlbnQgJiYgdGhpcy50b2tlblN0YXJ0c0xpbmUoKSkge1xuICAgICAgaWYgKHRoaXMudG9rLnR5cGUgPT0gdHQuZG90ICYmIHRoaXMuY3VySW5kZW50ID09IHN0YXJ0SW5kZW50KSAtLXN0YXJ0SW5kZW50O2Vsc2UgcmV0dXJuIGJhc2U7XG4gICAgfVxuXG4gICAgaWYgKHRoaXMuZWF0KHR0LmRvdCkpIHtcbiAgICAgIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGVBdChzdGFydCk7XG4gICAgICBub2RlLm9iamVjdCA9IGJhc2U7XG4gICAgICBpZiAodGhpcy5jdXJMaW5lU3RhcnQgIT0gbGluZSAmJiB0aGlzLmN1ckluZGVudCA8PSBzdGFydEluZGVudCAmJiB0aGlzLnRva2VuU3RhcnRzTGluZSgpKSBub2RlLnByb3BlcnR5ID0gdGhpcy5kdW1teUlkZW50KCk7ZWxzZSBub2RlLnByb3BlcnR5ID0gdGhpcy5wYXJzZVByb3BlcnR5QWNjZXNzb3IoKSB8fCB0aGlzLmR1bW15SWRlbnQoKTtcbiAgICAgIG5vZGUuY29tcHV0ZWQgPSBmYWxzZTtcbiAgICAgIGJhc2UgPSB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJNZW1iZXJFeHByZXNzaW9uXCIpO1xuICAgIH0gZWxzZSBpZiAodGhpcy50b2sudHlwZSA9PSB0dC5icmFja2V0TCkge1xuICAgICAgdGhpcy5wdXNoQ3goKTtcbiAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0KTtcbiAgICAgIG5vZGUub2JqZWN0ID0gYmFzZTtcbiAgICAgIG5vZGUucHJvcGVydHkgPSB0aGlzLnBhcnNlRXhwcmVzc2lvbigpO1xuICAgICAgbm9kZS5jb21wdXRlZCA9IHRydWU7XG4gICAgICB0aGlzLnBvcEN4KCk7XG4gICAgICB0aGlzLmV4cGVjdCh0dC5icmFja2V0Uik7XG4gICAgICBiYXNlID0gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiTWVtYmVyRXhwcmVzc2lvblwiKTtcbiAgICB9IGVsc2UgaWYgKCFub0NhbGxzICYmIHRoaXMudG9rLnR5cGUgPT0gdHQucGFyZW5MKSB7XG4gICAgICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlQXQoc3RhcnQpO1xuICAgICAgbm9kZS5jYWxsZWUgPSBiYXNlO1xuICAgICAgbm9kZS5hcmd1bWVudHMgPSB0aGlzLnBhcnNlRXhwckxpc3QodHQucGFyZW5SKTtcbiAgICAgIGJhc2UgPSB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJDYWxsRXhwcmVzc2lvblwiKTtcbiAgICB9IGVsc2UgaWYgKHRoaXMudG9rLnR5cGUgPT0gdHQuYmFja1F1b3RlKSB7XG4gICAgICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlQXQoc3RhcnQpO1xuICAgICAgbm9kZS50YWcgPSBiYXNlO1xuICAgICAgbm9kZS5xdWFzaSA9IHRoaXMucGFyc2VUZW1wbGF0ZSgpO1xuICAgICAgYmFzZSA9IHRoaXMuZmluaXNoTm9kZShub2RlLCBcIlRhZ2dlZFRlbXBsYXRlRXhwcmVzc2lvblwiKTtcbiAgICB9IGVsc2Uge1xuICAgICAgcmV0dXJuIGJhc2U7XG4gICAgfVxuICB9XG59O1xuXG5scC5wYXJzZUV4cHJBdG9tID0gZnVuY3Rpb24gKCkge1xuICB2YXIgbm9kZSA9IHVuZGVmaW5lZDtcbiAgc3dpdGNoICh0aGlzLnRvay50eXBlKSB7XG4gICAgY2FzZSB0dC5fdGhpczpcbiAgICBjYXNlIHR0Ll9zdXBlcjpcbiAgICAgIHZhciB0eXBlID0gdGhpcy50b2sudHlwZSA9PT0gdHQuX3RoaXMgPyBcIlRoaXNFeHByZXNzaW9uXCIgOiBcIlN1cGVyXCI7XG4gICAgICBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCB0eXBlKTtcblxuICAgIGNhc2UgdHQubmFtZTpcbiAgICAgIHZhciBzdGFydCA9IHRoaXMuc3RvcmVDdXJyZW50UG9zKCk7XG4gICAgICB2YXIgaWQgPSB0aGlzLnBhcnNlSWRlbnQoKTtcbiAgICAgIHJldHVybiB0aGlzLmVhdCh0dC5hcnJvdykgPyB0aGlzLnBhcnNlQXJyb3dFeHByZXNzaW9uKHRoaXMuc3RhcnROb2RlQXQoc3RhcnQpLCBbaWRdKSA6IGlkO1xuXG4gICAgY2FzZSB0dC5yZWdleHA6XG4gICAgICBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgICAgIHZhciB2YWwgPSB0aGlzLnRvay52YWx1ZTtcbiAgICAgIG5vZGUucmVnZXggPSB7IHBhdHRlcm46IHZhbC5wYXR0ZXJuLCBmbGFnczogdmFsLmZsYWdzIH07XG4gICAgICBub2RlLnZhbHVlID0gdmFsLnZhbHVlO1xuICAgICAgbm9kZS5yYXcgPSB0aGlzLmlucHV0LnNsaWNlKHRoaXMudG9rLnN0YXJ0LCB0aGlzLnRvay5lbmQpO1xuICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiTGl0ZXJhbFwiKTtcblxuICAgIGNhc2UgdHQubnVtOmNhc2UgdHQuc3RyaW5nOlxuICAgICAgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gICAgICBub2RlLnZhbHVlID0gdGhpcy50b2sudmFsdWU7XG4gICAgICBub2RlLnJhdyA9IHRoaXMuaW5wdXQuc2xpY2UodGhpcy50b2suc3RhcnQsIHRoaXMudG9rLmVuZCk7XG4gICAgICB0aGlzLm5leHQoKTtcbiAgICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJMaXRlcmFsXCIpO1xuXG4gICAgY2FzZSB0dC5fbnVsbDpjYXNlIHR0Ll90cnVlOmNhc2UgdHQuX2ZhbHNlOlxuICAgICAgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gICAgICBub2RlLnZhbHVlID0gdGhpcy50b2sudHlwZSA9PT0gdHQuX251bGwgPyBudWxsIDogdGhpcy50b2sudHlwZSA9PT0gdHQuX3RydWU7XG4gICAgICBub2RlLnJhdyA9IHRoaXMudG9rLnR5cGUua2V5d29yZDtcbiAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkxpdGVyYWxcIik7XG5cbiAgICBjYXNlIHR0LnBhcmVuTDpcbiAgICAgIHZhciBwYXJlblN0YXJ0ID0gdGhpcy5zdG9yZUN1cnJlbnRQb3MoKTtcbiAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgdmFyIGlubmVyID0gdGhpcy5wYXJzZUV4cHJlc3Npb24oKTtcbiAgICAgIHRoaXMuZXhwZWN0KHR0LnBhcmVuUik7XG4gICAgICBpZiAodGhpcy5lYXQodHQuYXJyb3cpKSB7XG4gICAgICAgIHJldHVybiB0aGlzLnBhcnNlQXJyb3dFeHByZXNzaW9uKHRoaXMuc3RhcnROb2RlQXQocGFyZW5TdGFydCksIGlubmVyLmV4cHJlc3Npb25zIHx8IChpc0R1bW15KGlubmVyKSA/IFtdIDogW2lubmVyXSkpO1xuICAgICAgfVxuICAgICAgaWYgKHRoaXMub3B0aW9ucy5wcmVzZXJ2ZVBhcmVucykge1xuICAgICAgICB2YXIgcGFyID0gdGhpcy5zdGFydE5vZGVBdChwYXJlblN0YXJ0KTtcbiAgICAgICAgcGFyLmV4cHJlc3Npb24gPSBpbm5lcjtcbiAgICAgICAgaW5uZXIgPSB0aGlzLmZpbmlzaE5vZGUocGFyLCBcIlBhcmVudGhlc2l6ZWRFeHByZXNzaW9uXCIpO1xuICAgICAgfVxuICAgICAgcmV0dXJuIGlubmVyO1xuXG4gICAgY2FzZSB0dC5icmFja2V0TDpcbiAgICAgIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICAgICAgbm9kZS5lbGVtZW50cyA9IHRoaXMucGFyc2VFeHByTGlzdCh0dC5icmFja2V0UiwgdHJ1ZSk7XG4gICAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiQXJyYXlFeHByZXNzaW9uXCIpO1xuXG4gICAgY2FzZSB0dC5icmFjZUw6XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZU9iaigpO1xuXG4gICAgY2FzZSB0dC5fY2xhc3M6XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZUNsYXNzKCk7XG5cbiAgICBjYXNlIHR0Ll9mdW5jdGlvbjpcbiAgICAgIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZUZ1bmN0aW9uKG5vZGUsIGZhbHNlKTtcblxuICAgIGNhc2UgdHQuX25ldzpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlTmV3KCk7XG5cbiAgICBjYXNlIHR0Ll95aWVsZDpcbiAgICAgIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICBpZiAodGhpcy5zZW1pY29sb24oKSB8fCB0aGlzLmNhbkluc2VydFNlbWljb2xvbigpIHx8IHRoaXMudG9rLnR5cGUgIT0gdHQuc3RhciAmJiAhdGhpcy50b2sudHlwZS5zdGFydHNFeHByKSB7XG4gICAgICAgIG5vZGUuZGVsZWdhdGUgPSBmYWxzZTtcbiAgICAgICAgbm9kZS5hcmd1bWVudCA9IG51bGw7XG4gICAgICB9IGVsc2Uge1xuICAgICAgICBub2RlLmRlbGVnYXRlID0gdGhpcy5lYXQodHQuc3Rhcik7XG4gICAgICAgIG5vZGUuYXJndW1lbnQgPSB0aGlzLnBhcnNlTWF5YmVBc3NpZ24oKTtcbiAgICAgIH1cbiAgICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJZaWVsZEV4cHJlc3Npb25cIik7XG5cbiAgICBjYXNlIHR0LmJhY2tRdW90ZTpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlVGVtcGxhdGUoKTtcblxuICAgIGRlZmF1bHQ6XG4gICAgICByZXR1cm4gdGhpcy5kdW1teUlkZW50KCk7XG4gIH1cbn07XG5cbmxwLnBhcnNlTmV3ID0gZnVuY3Rpb24gKCkge1xuICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCksXG4gICAgICBzdGFydEluZGVudCA9IHRoaXMuY3VySW5kZW50LFxuICAgICAgbGluZSA9IHRoaXMuY3VyTGluZVN0YXJ0O1xuICB2YXIgbWV0YSA9IHRoaXMucGFyc2VJZGVudCh0cnVlKTtcbiAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2ICYmIHRoaXMuZWF0KHR0LmRvdCkpIHtcbiAgICBub2RlLm1ldGEgPSBtZXRhO1xuICAgIG5vZGUucHJvcGVydHkgPSB0aGlzLnBhcnNlSWRlbnQodHJ1ZSk7XG4gICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIk1ldGFQcm9wZXJ0eVwiKTtcbiAgfVxuICB2YXIgc3RhcnQgPSB0aGlzLnN0b3JlQ3VycmVudFBvcygpO1xuICBub2RlLmNhbGxlZSA9IHRoaXMucGFyc2VTdWJzY3JpcHRzKHRoaXMucGFyc2VFeHByQXRvbSgpLCBzdGFydCwgdHJ1ZSwgc3RhcnRJbmRlbnQsIGxpbmUpO1xuICBpZiAodGhpcy50b2sudHlwZSA9PSB0dC5wYXJlbkwpIHtcbiAgICBub2RlLmFyZ3VtZW50cyA9IHRoaXMucGFyc2VFeHByTGlzdCh0dC5wYXJlblIpO1xuICB9IGVsc2Uge1xuICAgIG5vZGUuYXJndW1lbnRzID0gW107XG4gIH1cbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIk5ld0V4cHJlc3Npb25cIik7XG59O1xuXG5scC5wYXJzZVRlbXBsYXRlRWxlbWVudCA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIGVsZW0gPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICBlbGVtLnZhbHVlID0ge1xuICAgIHJhdzogdGhpcy5pbnB1dC5zbGljZSh0aGlzLnRvay5zdGFydCwgdGhpcy50b2suZW5kKSxcbiAgICBjb29rZWQ6IHRoaXMudG9rLnZhbHVlXG4gIH07XG4gIHRoaXMubmV4dCgpO1xuICBlbGVtLnRhaWwgPSB0aGlzLnRvay50eXBlID09PSB0dC5iYWNrUXVvdGU7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUoZWxlbSwgXCJUZW1wbGF0ZUVsZW1lbnRcIik7XG59O1xuXG5scC5wYXJzZVRlbXBsYXRlID0gZnVuY3Rpb24gKCkge1xuICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gIHRoaXMubmV4dCgpO1xuICBub2RlLmV4cHJlc3Npb25zID0gW107XG4gIHZhciBjdXJFbHQgPSB0aGlzLnBhcnNlVGVtcGxhdGVFbGVtZW50KCk7XG4gIG5vZGUucXVhc2lzID0gW2N1ckVsdF07XG4gIHdoaWxlICghY3VyRWx0LnRhaWwpIHtcbiAgICB0aGlzLm5leHQoKTtcbiAgICBub2RlLmV4cHJlc3Npb25zLnB1c2godGhpcy5wYXJzZUV4cHJlc3Npb24oKSk7XG4gICAgaWYgKHRoaXMuZXhwZWN0KHR0LmJyYWNlUikpIHtcbiAgICAgIGN1ckVsdCA9IHRoaXMucGFyc2VUZW1wbGF0ZUVsZW1lbnQoKTtcbiAgICB9IGVsc2Uge1xuICAgICAgY3VyRWx0ID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgICAgIGN1ckVsdC52YWx1ZSA9IHsgY29va2VkOiBcIlwiLCByYXc6IFwiXCIgfTtcbiAgICAgIGN1ckVsdC50YWlsID0gdHJ1ZTtcbiAgICB9XG4gICAgbm9kZS5xdWFzaXMucHVzaChjdXJFbHQpO1xuICB9XG4gIHRoaXMuZXhwZWN0KHR0LmJhY2tRdW90ZSk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJUZW1wbGF0ZUxpdGVyYWxcIik7XG59O1xuXG5scC5wYXJzZU9iaiA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICBub2RlLnByb3BlcnRpZXMgPSBbXTtcbiAgdGhpcy5wdXNoQ3goKTtcbiAgdmFyIGluZGVudCA9IHRoaXMuY3VySW5kZW50ICsgMSxcbiAgICAgIGxpbmUgPSB0aGlzLmN1ckxpbmVTdGFydDtcbiAgdGhpcy5lYXQodHQuYnJhY2VMKTtcbiAgaWYgKHRoaXMuY3VySW5kZW50ICsgMSA8IGluZGVudCkge1xuICAgIGluZGVudCA9IHRoaXMuY3VySW5kZW50O2xpbmUgPSB0aGlzLmN1ckxpbmVTdGFydDtcbiAgfVxuICB3aGlsZSAoIXRoaXMuY2xvc2VzKHR0LmJyYWNlUiwgaW5kZW50LCBsaW5lKSkge1xuICAgIHZhciBwcm9wID0gdGhpcy5zdGFydE5vZGUoKSxcbiAgICAgICAgaXNHZW5lcmF0b3IgPSB1bmRlZmluZWQsXG4gICAgICAgIHN0YXJ0ID0gdW5kZWZpbmVkO1xuICAgIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNikge1xuICAgICAgc3RhcnQgPSB0aGlzLnN0b3JlQ3VycmVudFBvcygpO1xuICAgICAgcHJvcC5tZXRob2QgPSBmYWxzZTtcbiAgICAgIHByb3Auc2hvcnRoYW5kID0gZmFsc2U7XG4gICAgICBpc0dlbmVyYXRvciA9IHRoaXMuZWF0KHR0LnN0YXIpO1xuICAgIH1cbiAgICB0aGlzLnBhcnNlUHJvcGVydHlOYW1lKHByb3ApO1xuICAgIGlmIChpc0R1bW15KHByb3Aua2V5KSkge1xuICAgICAgaWYgKGlzRHVtbXkodGhpcy5wYXJzZU1heWJlQXNzaWduKCkpKSB0aGlzLm5leHQoKTt0aGlzLmVhdCh0dC5jb21tYSk7Y29udGludWU7XG4gICAgfVxuICAgIGlmICh0aGlzLmVhdCh0dC5jb2xvbikpIHtcbiAgICAgIHByb3Aua2luZCA9IFwiaW5pdFwiO1xuICAgICAgcHJvcC52YWx1ZSA9IHRoaXMucGFyc2VNYXliZUFzc2lnbigpO1xuICAgIH0gZWxzZSBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYgJiYgKHRoaXMudG9rLnR5cGUgPT09IHR0LnBhcmVuTCB8fCB0aGlzLnRvay50eXBlID09PSB0dC5icmFjZUwpKSB7XG4gICAgICBwcm9wLmtpbmQgPSBcImluaXRcIjtcbiAgICAgIHByb3AubWV0aG9kID0gdHJ1ZTtcbiAgICAgIHByb3AudmFsdWUgPSB0aGlzLnBhcnNlTWV0aG9kKGlzR2VuZXJhdG9yKTtcbiAgICB9IGVsc2UgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA1ICYmIHByb3Aua2V5LnR5cGUgPT09IFwiSWRlbnRpZmllclwiICYmICFwcm9wLmNvbXB1dGVkICYmIChwcm9wLmtleS5uYW1lID09PSBcImdldFwiIHx8IHByb3Aua2V5Lm5hbWUgPT09IFwic2V0XCIpICYmICh0aGlzLnRvay50eXBlICE9IHR0LmNvbW1hICYmIHRoaXMudG9rLnR5cGUgIT0gdHQuYnJhY2VSKSkge1xuICAgICAgcHJvcC5raW5kID0gcHJvcC5rZXkubmFtZTtcbiAgICAgIHRoaXMucGFyc2VQcm9wZXJ0eU5hbWUocHJvcCk7XG4gICAgICBwcm9wLnZhbHVlID0gdGhpcy5wYXJzZU1ldGhvZChmYWxzZSk7XG4gICAgfSBlbHNlIHtcbiAgICAgIHByb3Aua2luZCA9IFwiaW5pdFwiO1xuICAgICAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KSB7XG4gICAgICAgIGlmICh0aGlzLmVhdCh0dC5lcSkpIHtcbiAgICAgICAgICB2YXIgYXNzaWduID0gdGhpcy5zdGFydE5vZGVBdChzdGFydCk7XG4gICAgICAgICAgYXNzaWduLm9wZXJhdG9yID0gXCI9XCI7XG4gICAgICAgICAgYXNzaWduLmxlZnQgPSBwcm9wLmtleTtcbiAgICAgICAgICBhc3NpZ24ucmlnaHQgPSB0aGlzLnBhcnNlTWF5YmVBc3NpZ24oKTtcbiAgICAgICAgICBwcm9wLnZhbHVlID0gdGhpcy5maW5pc2hOb2RlKGFzc2lnbiwgXCJBc3NpZ25tZW50RXhwcmVzc2lvblwiKTtcbiAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICBwcm9wLnZhbHVlID0gcHJvcC5rZXk7XG4gICAgICAgIH1cbiAgICAgIH0gZWxzZSB7XG4gICAgICAgIHByb3AudmFsdWUgPSB0aGlzLmR1bW15SWRlbnQoKTtcbiAgICAgIH1cbiAgICAgIHByb3Auc2hvcnRoYW5kID0gdHJ1ZTtcbiAgICB9XG4gICAgbm9kZS5wcm9wZXJ0aWVzLnB1c2godGhpcy5maW5pc2hOb2RlKHByb3AsIFwiUHJvcGVydHlcIikpO1xuICAgIHRoaXMuZWF0KHR0LmNvbW1hKTtcbiAgfVxuICB0aGlzLnBvcEN4KCk7XG4gIGlmICghdGhpcy5lYXQodHQuYnJhY2VSKSkge1xuICAgIC8vIElmIHRoZXJlIGlzIG5vIGNsb3NpbmcgYnJhY2UsIG1ha2UgdGhlIG5vZGUgc3BhbiB0byB0aGUgc3RhcnRcbiAgICAvLyBvZiB0aGUgbmV4dCB0b2tlbiAodGhpcyBpcyB1c2VmdWwgZm9yIFRlcm4pXG4gICAgdGhpcy5sYXN0LmVuZCA9IHRoaXMudG9rLnN0YXJ0O1xuICAgIGlmICh0aGlzLm9wdGlvbnMubG9jYXRpb25zKSB0aGlzLmxhc3QubG9jLmVuZCA9IHRoaXMudG9rLmxvYy5zdGFydDtcbiAgfVxuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiT2JqZWN0RXhwcmVzc2lvblwiKTtcbn07XG5cbmxwLnBhcnNlUHJvcGVydHlOYW1lID0gZnVuY3Rpb24gKHByb3ApIHtcbiAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KSB7XG4gICAgaWYgKHRoaXMuZWF0KHR0LmJyYWNrZXRMKSkge1xuICAgICAgcHJvcC5jb21wdXRlZCA9IHRydWU7XG4gICAgICBwcm9wLmtleSA9IHRoaXMucGFyc2VFeHByZXNzaW9uKCk7XG4gICAgICB0aGlzLmV4cGVjdCh0dC5icmFja2V0Uik7XG4gICAgICByZXR1cm47XG4gICAgfSBlbHNlIHtcbiAgICAgIHByb3AuY29tcHV0ZWQgPSBmYWxzZTtcbiAgICB9XG4gIH1cbiAgdmFyIGtleSA9IHRoaXMudG9rLnR5cGUgPT09IHR0Lm51bSB8fCB0aGlzLnRvay50eXBlID09PSB0dC5zdHJpbmcgPyB0aGlzLnBhcnNlRXhwckF0b20oKSA6IHRoaXMucGFyc2VJZGVudCgpO1xuICBwcm9wLmtleSA9IGtleSB8fCB0aGlzLmR1bW15SWRlbnQoKTtcbn07XG5cbmxwLnBhcnNlUHJvcGVydHlBY2Nlc3NvciA9IGZ1bmN0aW9uICgpIHtcbiAgaWYgKHRoaXMudG9rLnR5cGUgPT09IHR0Lm5hbWUgfHwgdGhpcy50b2sudHlwZS5rZXl3b3JkKSByZXR1cm4gdGhpcy5wYXJzZUlkZW50KCk7XG59O1xuXG5scC5wYXJzZUlkZW50ID0gZnVuY3Rpb24gKCkge1xuICB2YXIgbmFtZSA9IHRoaXMudG9rLnR5cGUgPT09IHR0Lm5hbWUgPyB0aGlzLnRvay52YWx1ZSA6IHRoaXMudG9rLnR5cGUua2V5d29yZDtcbiAgaWYgKCFuYW1lKSByZXR1cm4gdGhpcy5kdW1teUlkZW50KCk7XG4gIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgdGhpcy5uZXh0KCk7XG4gIG5vZGUubmFtZSA9IG5hbWU7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJJZGVudGlmaWVyXCIpO1xufTtcblxubHAuaW5pdEZ1bmN0aW9uID0gZnVuY3Rpb24gKG5vZGUpIHtcbiAgbm9kZS5pZCA9IG51bGw7XG4gIG5vZGUucGFyYW1zID0gW107XG4gIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNikge1xuICAgIG5vZGUuZ2VuZXJhdG9yID0gZmFsc2U7XG4gICAgbm9kZS5leHByZXNzaW9uID0gZmFsc2U7XG4gIH1cbn07XG5cbi8vIENvbnZlcnQgZXhpc3RpbmcgZXhwcmVzc2lvbiBhdG9tIHRvIGFzc2lnbmFibGUgcGF0dGVyblxuLy8gaWYgcG9zc2libGUuXG5cbmxwLnRvQXNzaWduYWJsZSA9IGZ1bmN0aW9uIChub2RlLCBiaW5kaW5nKSB7XG4gIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNiAmJiBub2RlKSB7XG4gICAgc3dpdGNoIChub2RlLnR5cGUpIHtcbiAgICAgIGNhc2UgXCJPYmplY3RFeHByZXNzaW9uXCI6XG4gICAgICAgIG5vZGUudHlwZSA9IFwiT2JqZWN0UGF0dGVyblwiO1xuICAgICAgICB2YXIgcHJvcHMgPSBub2RlLnByb3BlcnRpZXM7XG4gICAgICAgIGZvciAodmFyIGkgPSAwOyBpIDwgcHJvcHMubGVuZ3RoOyBpKyspIHtcbiAgICAgICAgICB0aGlzLnRvQXNzaWduYWJsZShwcm9wc1tpXS52YWx1ZSwgYmluZGluZyk7XG4gICAgICAgIH1icmVhaztcblxuICAgICAgY2FzZSBcIkFycmF5RXhwcmVzc2lvblwiOlxuICAgICAgICBub2RlLnR5cGUgPSBcIkFycmF5UGF0dGVyblwiO1xuICAgICAgICB0aGlzLnRvQXNzaWduYWJsZUxpc3Qobm9kZS5lbGVtZW50cywgYmluZGluZyk7XG4gICAgICAgIGJyZWFrO1xuXG4gICAgICBjYXNlIFwiU3ByZWFkRWxlbWVudFwiOlxuICAgICAgICBub2RlLnR5cGUgPSBcIlJlc3RFbGVtZW50XCI7XG4gICAgICAgIG5vZGUuYXJndW1lbnQgPSB0aGlzLnRvQXNzaWduYWJsZShub2RlLmFyZ3VtZW50LCBiaW5kaW5nKTtcbiAgICAgICAgYnJlYWs7XG5cbiAgICAgIGNhc2UgXCJBc3NpZ25tZW50RXhwcmVzc2lvblwiOlxuICAgICAgICBub2RlLnR5cGUgPSBcIkFzc2lnbm1lbnRQYXR0ZXJuXCI7XG4gICAgICAgIGJyZWFrO1xuICAgIH1cbiAgfVxuICByZXR1cm4gdGhpcy5jaGVja0xWYWwobm9kZSwgYmluZGluZyk7XG59O1xuXG5scC50b0Fzc2lnbmFibGVMaXN0ID0gZnVuY3Rpb24gKGV4cHJMaXN0LCBiaW5kaW5nKSB7XG4gIGZvciAodmFyIGkgPSAwOyBpIDwgZXhwckxpc3QubGVuZ3RoOyBpKyspIHtcbiAgICBleHByTGlzdFtpXSA9IHRoaXMudG9Bc3NpZ25hYmxlKGV4cHJMaXN0W2ldLCBiaW5kaW5nKTtcbiAgfXJldHVybiBleHByTGlzdDtcbn07XG5cbmxwLnBhcnNlRnVuY3Rpb25QYXJhbXMgPSBmdW5jdGlvbiAocGFyYW1zKSB7XG4gIHBhcmFtcyA9IHRoaXMucGFyc2VFeHByTGlzdCh0dC5wYXJlblIpO1xuICByZXR1cm4gdGhpcy50b0Fzc2lnbmFibGVMaXN0KHBhcmFtcywgdHJ1ZSk7XG59O1xuXG5scC5wYXJzZU1ldGhvZCA9IGZ1bmN0aW9uIChpc0dlbmVyYXRvcikge1xuICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gIHRoaXMuaW5pdEZ1bmN0aW9uKG5vZGUpO1xuICBub2RlLnBhcmFtcyA9IHRoaXMucGFyc2VGdW5jdGlvblBhcmFtcygpO1xuICBub2RlLmdlbmVyYXRvciA9IGlzR2VuZXJhdG9yIHx8IGZhbHNlO1xuICBub2RlLmV4cHJlc3Npb24gPSB0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNiAmJiB0aGlzLnRvay50eXBlICE9PSB0dC5icmFjZUw7XG4gIG5vZGUuYm9keSA9IG5vZGUuZXhwcmVzc2lvbiA/IHRoaXMucGFyc2VNYXliZUFzc2lnbigpIDogdGhpcy5wYXJzZUJsb2NrKCk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJGdW5jdGlvbkV4cHJlc3Npb25cIik7XG59O1xuXG5scC5wYXJzZUFycm93RXhwcmVzc2lvbiA9IGZ1bmN0aW9uIChub2RlLCBwYXJhbXMpIHtcbiAgdGhpcy5pbml0RnVuY3Rpb24obm9kZSk7XG4gIG5vZGUucGFyYW1zID0gdGhpcy50b0Fzc2lnbmFibGVMaXN0KHBhcmFtcywgdHJ1ZSk7XG4gIG5vZGUuZXhwcmVzc2lvbiA9IHRoaXMudG9rLnR5cGUgIT09IHR0LmJyYWNlTDtcbiAgbm9kZS5ib2R5ID0gbm9kZS5leHByZXNzaW9uID8gdGhpcy5wYXJzZU1heWJlQXNzaWduKCkgOiB0aGlzLnBhcnNlQmxvY2soKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkFycm93RnVuY3Rpb25FeHByZXNzaW9uXCIpO1xufTtcblxubHAucGFyc2VFeHByTGlzdCA9IGZ1bmN0aW9uIChjbG9zZSwgYWxsb3dFbXB0eSkge1xuICB0aGlzLnB1c2hDeCgpO1xuICB2YXIgaW5kZW50ID0gdGhpcy5jdXJJbmRlbnQsXG4gICAgICBsaW5lID0gdGhpcy5jdXJMaW5lU3RhcnQsXG4gICAgICBlbHRzID0gW107XG4gIHRoaXMubmV4dCgpOyAvLyBPcGVuaW5nIGJyYWNrZXRcbiAgd2hpbGUgKCF0aGlzLmNsb3NlcyhjbG9zZSwgaW5kZW50ICsgMSwgbGluZSkpIHtcbiAgICBpZiAodGhpcy5lYXQodHQuY29tbWEpKSB7XG4gICAgICBlbHRzLnB1c2goYWxsb3dFbXB0eSA/IG51bGwgOiB0aGlzLmR1bW15SWRlbnQoKSk7XG4gICAgICBjb250aW51ZTtcbiAgICB9XG4gICAgdmFyIGVsdCA9IHRoaXMucGFyc2VNYXliZUFzc2lnbigpO1xuICAgIGlmIChpc0R1bW15KGVsdCkpIHtcbiAgICAgIGlmICh0aGlzLmNsb3NlcyhjbG9zZSwgaW5kZW50LCBsaW5lKSkgYnJlYWs7XG4gICAgICB0aGlzLm5leHQoKTtcbiAgICB9IGVsc2Uge1xuICAgICAgZWx0cy5wdXNoKGVsdCk7XG4gICAgfVxuICAgIHRoaXMuZWF0KHR0LmNvbW1hKTtcbiAgfVxuICB0aGlzLnBvcEN4KCk7XG4gIGlmICghdGhpcy5lYXQoY2xvc2UpKSB7XG4gICAgLy8gSWYgdGhlcmUgaXMgbm8gY2xvc2luZyBicmFjZSwgbWFrZSB0aGUgbm9kZSBzcGFuIHRvIHRoZSBzdGFydFxuICAgIC8vIG9mIHRoZSBuZXh0IHRva2VuICh0aGlzIGlzIHVzZWZ1bCBmb3IgVGVybilcbiAgICB0aGlzLmxhc3QuZW5kID0gdGhpcy50b2suc3RhcnQ7XG4gICAgaWYgKHRoaXMub3B0aW9ucy5sb2NhdGlvbnMpIHRoaXMubGFzdC5sb2MuZW5kID0gdGhpcy50b2subG9jLnN0YXJ0O1xuICB9XG4gIHJldHVybiBlbHRzO1xufTtcblxufSx7XCIuLlwiOjMsXCIuL3BhcnNldXRpbFwiOjUsXCIuL3N0YXRlXCI6Nn1dLDU6W2Z1bmN0aW9uKF9kZXJlcV8sbW9kdWxlLGV4cG9ydHMpe1xuXCJ1c2Ugc3RyaWN0XCI7XG5cbmV4cG9ydHMuaXNEdW1teSA9IGlzRHVtbXk7XG5leHBvcnRzLl9fZXNNb2R1bGUgPSB0cnVlO1xuXG52YXIgTG9vc2VQYXJzZXIgPSBfZGVyZXFfKFwiLi9zdGF0ZVwiKS5Mb29zZVBhcnNlcjtcblxudmFyIF8gPSBfZGVyZXFfKFwiLi5cIik7XG5cbnZhciBOb2RlID0gXy5Ob2RlO1xudmFyIFNvdXJjZUxvY2F0aW9uID0gXy5Tb3VyY2VMb2NhdGlvbjtcbnZhciBsaW5lQnJlYWsgPSBfLmxpbmVCcmVhaztcbnZhciBpc05ld0xpbmUgPSBfLmlzTmV3TGluZTtcbnZhciB0dCA9IF8udG9rVHlwZXM7XG5cbnZhciBscCA9IExvb3NlUGFyc2VyLnByb3RvdHlwZTtcblxubHAuc3RhcnROb2RlID0gZnVuY3Rpb24gKCkge1xuICB2YXIgbm9kZSA9IG5ldyBOb2RlKCk7XG4gIG5vZGUuc3RhcnQgPSB0aGlzLnRvay5zdGFydDtcbiAgaWYgKHRoaXMub3B0aW9ucy5sb2NhdGlvbnMpIG5vZGUubG9jID0gbmV3IFNvdXJjZUxvY2F0aW9uKHRoaXMudG9rcywgdGhpcy50b2subG9jLnN0YXJ0KTtcbiAgaWYgKHRoaXMub3B0aW9ucy5kaXJlY3RTb3VyY2VGaWxlKSBub2RlLnNvdXJjZUZpbGUgPSB0aGlzLm9wdGlvbnMuZGlyZWN0U291cmNlRmlsZTtcbiAgaWYgKHRoaXMub3B0aW9ucy5yYW5nZXMpIG5vZGUucmFuZ2UgPSBbdGhpcy50b2suc3RhcnQsIDBdO1xuICByZXR1cm4gbm9kZTtcbn07XG5cbmxwLnN0b3JlQ3VycmVudFBvcyA9IGZ1bmN0aW9uICgpIHtcbiAgcmV0dXJuIHRoaXMub3B0aW9ucy5sb2NhdGlvbnMgPyBbdGhpcy50b2suc3RhcnQsIHRoaXMudG9rLmxvYy5zdGFydF0gOiB0aGlzLnRvay5zdGFydDtcbn07XG5cbmxwLnN0YXJ0Tm9kZUF0ID0gZnVuY3Rpb24gKHBvcykge1xuICB2YXIgbm9kZSA9IG5ldyBOb2RlKCk7XG4gIGlmICh0aGlzLm9wdGlvbnMubG9jYXRpb25zKSB7XG4gICAgbm9kZS5zdGFydCA9IHBvc1swXTtcbiAgICBub2RlLmxvYyA9IG5ldyBTb3VyY2VMb2NhdGlvbih0aGlzLnRva3MsIHBvc1sxXSk7XG4gICAgcG9zID0gcG9zWzBdO1xuICB9IGVsc2Uge1xuICAgIG5vZGUuc3RhcnQgPSBwb3M7XG4gIH1cbiAgaWYgKHRoaXMub3B0aW9ucy5kaXJlY3RTb3VyY2VGaWxlKSBub2RlLnNvdXJjZUZpbGUgPSB0aGlzLm9wdGlvbnMuZGlyZWN0U291cmNlRmlsZTtcbiAgaWYgKHRoaXMub3B0aW9ucy5yYW5nZXMpIG5vZGUucmFuZ2UgPSBbcG9zLCAwXTtcbiAgcmV0dXJuIG5vZGU7XG59O1xuXG5scC5maW5pc2hOb2RlID0gZnVuY3Rpb24gKG5vZGUsIHR5cGUpIHtcbiAgbm9kZS50eXBlID0gdHlwZTtcbiAgbm9kZS5lbmQgPSB0aGlzLmxhc3QuZW5kO1xuICBpZiAodGhpcy5vcHRpb25zLmxvY2F0aW9ucykgbm9kZS5sb2MuZW5kID0gdGhpcy5sYXN0LmxvYy5lbmQ7XG4gIGlmICh0aGlzLm9wdGlvbnMucmFuZ2VzKSBub2RlLnJhbmdlWzFdID0gdGhpcy5sYXN0LmVuZDtcbiAgcmV0dXJuIG5vZGU7XG59O1xuXG5scC5kdW1teUlkZW50ID0gZnVuY3Rpb24gKCkge1xuICB2YXIgZHVtbXkgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICBkdW1teS5uYW1lID0gXCLinJZcIjtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShkdW1teSwgXCJJZGVudGlmaWVyXCIpO1xufTtcblxuZnVuY3Rpb24gaXNEdW1teShub2RlKSB7XG4gIHJldHVybiBub2RlLm5hbWUgPT0gXCLinJZcIjtcbn1cblxubHAuZWF0ID0gZnVuY3Rpb24gKHR5cGUpIHtcbiAgaWYgKHRoaXMudG9rLnR5cGUgPT09IHR5cGUpIHtcbiAgICB0aGlzLm5leHQoKTtcbiAgICByZXR1cm4gdHJ1ZTtcbiAgfSBlbHNlIHtcbiAgICByZXR1cm4gZmFsc2U7XG4gIH1cbn07XG5cbmxwLmlzQ29udGV4dHVhbCA9IGZ1bmN0aW9uIChuYW1lKSB7XG4gIHJldHVybiB0aGlzLnRvay50eXBlID09PSB0dC5uYW1lICYmIHRoaXMudG9rLnZhbHVlID09PSBuYW1lO1xufTtcblxubHAuZWF0Q29udGV4dHVhbCA9IGZ1bmN0aW9uIChuYW1lKSB7XG4gIHJldHVybiB0aGlzLnRvay52YWx1ZSA9PT0gbmFtZSAmJiB0aGlzLmVhdCh0dC5uYW1lKTtcbn07XG5cbmxwLmNhbkluc2VydFNlbWljb2xvbiA9IGZ1bmN0aW9uICgpIHtcbiAgcmV0dXJuIHRoaXMudG9rLnR5cGUgPT09IHR0LmVvZiB8fCB0aGlzLnRvay50eXBlID09PSB0dC5icmFjZVIgfHwgbGluZUJyZWFrLnRlc3QodGhpcy5pbnB1dC5zbGljZSh0aGlzLmxhc3QuZW5kLCB0aGlzLnRvay5zdGFydCkpO1xufTtcblxubHAuc2VtaWNvbG9uID0gZnVuY3Rpb24gKCkge1xuICByZXR1cm4gdGhpcy5lYXQodHQuc2VtaSk7XG59O1xuXG5scC5leHBlY3QgPSBmdW5jdGlvbiAodHlwZSkge1xuICBpZiAodGhpcy5lYXQodHlwZSkpIHJldHVybiB0cnVlO1xuICBmb3IgKHZhciBpID0gMTsgaSA8PSAyOyBpKyspIHtcbiAgICBpZiAodGhpcy5sb29rQWhlYWQoaSkudHlwZSA9PSB0eXBlKSB7XG4gICAgICBmb3IgKHZhciBqID0gMDsgaiA8IGk7IGorKykge1xuICAgICAgICB0aGlzLm5leHQoKTtcbiAgICAgIH1yZXR1cm4gdHJ1ZTtcbiAgICB9XG4gIH1cbn07XG5cbmxwLnB1c2hDeCA9IGZ1bmN0aW9uICgpIHtcbiAgdGhpcy5jb250ZXh0LnB1c2godGhpcy5jdXJJbmRlbnQpO1xufTtcbmxwLnBvcEN4ID0gZnVuY3Rpb24gKCkge1xuICB0aGlzLmN1ckluZGVudCA9IHRoaXMuY29udGV4dC5wb3AoKTtcbn07XG5cbmxwLmxpbmVFbmQgPSBmdW5jdGlvbiAocG9zKSB7XG4gIHdoaWxlIChwb3MgPCB0aGlzLmlucHV0Lmxlbmd0aCAmJiAhaXNOZXdMaW5lKHRoaXMuaW5wdXQuY2hhckNvZGVBdChwb3MpKSkgKytwb3M7XG4gIHJldHVybiBwb3M7XG59O1xuXG5scC5pbmRlbnRhdGlvbkFmdGVyID0gZnVuY3Rpb24gKHBvcykge1xuICBmb3IgKHZhciBjb3VudCA9IDA7OyArK3Bvcykge1xuICAgIHZhciBjaCA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdChwb3MpO1xuICAgIGlmIChjaCA9PT0gMzIpICsrY291bnQ7ZWxzZSBpZiAoY2ggPT09IDkpIGNvdW50ICs9IHRoaXMub3B0aW9ucy50YWJTaXplO2Vsc2UgcmV0dXJuIGNvdW50O1xuICB9XG59O1xuXG5scC5jbG9zZXMgPSBmdW5jdGlvbiAoY2xvc2VUb2ssIGluZGVudCwgbGluZSwgYmxvY2tIZXVyaXN0aWMpIHtcbiAgaWYgKHRoaXMudG9rLnR5cGUgPT09IGNsb3NlVG9rIHx8IHRoaXMudG9rLnR5cGUgPT09IHR0LmVvZikgcmV0dXJuIHRydWU7XG4gIHJldHVybiBsaW5lICE9IHRoaXMuY3VyTGluZVN0YXJ0ICYmIHRoaXMuY3VySW5kZW50IDwgaW5kZW50ICYmIHRoaXMudG9rZW5TdGFydHNMaW5lKCkgJiYgKCFibG9ja0hldXJpc3RpYyB8fCB0aGlzLm5leHRMaW5lU3RhcnQgPj0gdGhpcy5pbnB1dC5sZW5ndGggfHwgdGhpcy5pbmRlbnRhdGlvbkFmdGVyKHRoaXMubmV4dExpbmVTdGFydCkgPCBpbmRlbnQpO1xufTtcblxubHAudG9rZW5TdGFydHNMaW5lID0gZnVuY3Rpb24gKCkge1xuICBmb3IgKHZhciBwID0gdGhpcy50b2suc3RhcnQgLSAxOyBwID49IHRoaXMuY3VyTGluZVN0YXJ0OyAtLXApIHtcbiAgICB2YXIgY2ggPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQocCk7XG4gICAgaWYgKGNoICE9PSA5ICYmIGNoICE9PSAzMikgcmV0dXJuIGZhbHNlO1xuICB9XG4gIHJldHVybiB0cnVlO1xufTtcblxufSx7XCIuLlwiOjMsXCIuL3N0YXRlXCI6Nn1dLDY6W2Z1bmN0aW9uKF9kZXJlcV8sbW9kdWxlLGV4cG9ydHMpe1xuXCJ1c2Ugc3RyaWN0XCI7XG5cbmV4cG9ydHMuTG9vc2VQYXJzZXIgPSBMb29zZVBhcnNlcjtcbmV4cG9ydHMuX19lc01vZHVsZSA9IHRydWU7XG5cbnZhciBfID0gX2RlcmVxXyhcIi4uXCIpO1xuXG52YXIgdG9rZW5pemVyID0gXy50b2tlbml6ZXI7XG52YXIgU291cmNlTG9jYXRpb24gPSBfLlNvdXJjZUxvY2F0aW9uO1xudmFyIHR0ID0gXy50b2tUeXBlcztcblxuZnVuY3Rpb24gTG9vc2VQYXJzZXIoaW5wdXQsIG9wdGlvbnMpIHtcbiAgdGhpcy50b2tzID0gdG9rZW5pemVyKGlucHV0LCBvcHRpb25zKTtcbiAgdGhpcy5vcHRpb25zID0gdGhpcy50b2tzLm9wdGlvbnM7XG4gIHRoaXMuaW5wdXQgPSB0aGlzLnRva3MuaW5wdXQ7XG4gIHRoaXMudG9rID0gdGhpcy5sYXN0ID0geyB0eXBlOiB0dC5lb2YsIHN0YXJ0OiAwLCBlbmQ6IDAgfTtcbiAgaWYgKHRoaXMub3B0aW9ucy5sb2NhdGlvbnMpIHtcbiAgICB2YXIgaGVyZSA9IHRoaXMudG9rcy5jdXJQb3NpdGlvbigpO1xuICAgIHRoaXMudG9rLmxvYyA9IG5ldyBTb3VyY2VMb2NhdGlvbih0aGlzLnRva3MsIGhlcmUsIGhlcmUpO1xuICB9XG4gIHRoaXMuYWhlYWQgPSBbXTsgLy8gVG9rZW5zIGFoZWFkXG4gIHRoaXMuY29udGV4dCA9IFtdOyAvLyBJbmRlbnRhdGlvbiBjb250ZXh0ZWRcbiAgdGhpcy5jdXJJbmRlbnQgPSAwO1xuICB0aGlzLmN1ckxpbmVTdGFydCA9IDA7XG4gIHRoaXMubmV4dExpbmVTdGFydCA9IHRoaXMubGluZUVuZCh0aGlzLmN1ckxpbmVTdGFydCkgKyAxO1xufVxuXG59LHtcIi4uXCI6M31dLDc6W2Z1bmN0aW9uKF9kZXJlcV8sbW9kdWxlLGV4cG9ydHMpe1xuXCJ1c2Ugc3RyaWN0XCI7XG5cbnZhciBMb29zZVBhcnNlciA9IF9kZXJlcV8oXCIuL3N0YXRlXCIpLkxvb3NlUGFyc2VyO1xuXG52YXIgaXNEdW1teSA9IF9kZXJlcV8oXCIuL3BhcnNldXRpbFwiKS5pc0R1bW15O1xuXG52YXIgXyA9IF9kZXJlcV8oXCIuLlwiKTtcblxudmFyIGdldExpbmVJbmZvID0gXy5nZXRMaW5lSW5mbztcbnZhciB0dCA9IF8udG9rVHlwZXM7XG5cbnZhciBscCA9IExvb3NlUGFyc2VyLnByb3RvdHlwZTtcblxubHAucGFyc2VUb3BMZXZlbCA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZUF0KHRoaXMub3B0aW9ucy5sb2NhdGlvbnMgPyBbMCwgZ2V0TGluZUluZm8odGhpcy5pbnB1dCwgMCldIDogMCk7XG4gIG5vZGUuYm9keSA9IFtdO1xuICB3aGlsZSAodGhpcy50b2sudHlwZSAhPT0gdHQuZW9mKSBub2RlLmJvZHkucHVzaCh0aGlzLnBhcnNlU3RhdGVtZW50KCkpO1xuICB0aGlzLmxhc3QgPSB0aGlzLnRvaztcbiAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KSB7XG4gICAgbm9kZS5zb3VyY2VUeXBlID0gdGhpcy5vcHRpb25zLnNvdXJjZVR5cGU7XG4gIH1cbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIlByb2dyYW1cIik7XG59O1xuXG5scC5wYXJzZVN0YXRlbWVudCA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIHN0YXJ0dHlwZSA9IHRoaXMudG9rLnR5cGUsXG4gICAgICBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcblxuICBzd2l0Y2ggKHN0YXJ0dHlwZSkge1xuICAgIGNhc2UgdHQuX2JyZWFrOmNhc2UgdHQuX2NvbnRpbnVlOlxuICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICB2YXIgaXNCcmVhayA9IHN0YXJ0dHlwZSA9PT0gdHQuX2JyZWFrO1xuICAgICAgaWYgKHRoaXMuc2VtaWNvbG9uKCkgfHwgdGhpcy5jYW5JbnNlcnRTZW1pY29sb24oKSkge1xuICAgICAgICBub2RlLmxhYmVsID0gbnVsbDtcbiAgICAgIH0gZWxzZSB7XG4gICAgICAgIG5vZGUubGFiZWwgPSB0aGlzLnRvay50eXBlID09PSB0dC5uYW1lID8gdGhpcy5wYXJzZUlkZW50KCkgOiBudWxsO1xuICAgICAgICB0aGlzLnNlbWljb2xvbigpO1xuICAgICAgfVxuICAgICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBpc0JyZWFrID8gXCJCcmVha1N0YXRlbWVudFwiIDogXCJDb250aW51ZVN0YXRlbWVudFwiKTtcblxuICAgIGNhc2UgdHQuX2RlYnVnZ2VyOlxuICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICB0aGlzLnNlbWljb2xvbigpO1xuICAgICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkRlYnVnZ2VyU3RhdGVtZW50XCIpO1xuXG4gICAgY2FzZSB0dC5fZG86XG4gICAgICB0aGlzLm5leHQoKTtcbiAgICAgIG5vZGUuYm9keSA9IHRoaXMucGFyc2VTdGF0ZW1lbnQoKTtcbiAgICAgIG5vZGUudGVzdCA9IHRoaXMuZWF0KHR0Ll93aGlsZSkgPyB0aGlzLnBhcnNlUGFyZW5FeHByZXNzaW9uKCkgOiB0aGlzLmR1bW15SWRlbnQoKTtcbiAgICAgIHRoaXMuc2VtaWNvbG9uKCk7XG4gICAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiRG9XaGlsZVN0YXRlbWVudFwiKTtcblxuICAgIGNhc2UgdHQuX2ZvcjpcbiAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgdGhpcy5wdXNoQ3goKTtcbiAgICAgIHRoaXMuZXhwZWN0KHR0LnBhcmVuTCk7XG4gICAgICBpZiAodGhpcy50b2sudHlwZSA9PT0gdHQuc2VtaSkgcmV0dXJuIHRoaXMucGFyc2VGb3Iobm9kZSwgbnVsbCk7XG4gICAgICBpZiAodGhpcy50b2sudHlwZSA9PT0gdHQuX3ZhciB8fCB0aGlzLnRvay50eXBlID09PSB0dC5fbGV0IHx8IHRoaXMudG9rLnR5cGUgPT09IHR0Ll9jb25zdCkge1xuICAgICAgICB2YXIgX2luaXQgPSB0aGlzLnBhcnNlVmFyKHRydWUpO1xuICAgICAgICBpZiAoX2luaXQuZGVjbGFyYXRpb25zLmxlbmd0aCA9PT0gMSAmJiAodGhpcy50b2sudHlwZSA9PT0gdHQuX2luIHx8IHRoaXMuaXNDb250ZXh0dWFsKFwib2ZcIikpKSB7XG4gICAgICAgICAgcmV0dXJuIHRoaXMucGFyc2VGb3JJbihub2RlLCBfaW5pdCk7XG4gICAgICAgIH1cbiAgICAgICAgcmV0dXJuIHRoaXMucGFyc2VGb3Iobm9kZSwgX2luaXQpO1xuICAgICAgfVxuICAgICAgdmFyIGluaXQgPSB0aGlzLnBhcnNlRXhwcmVzc2lvbih0cnVlKTtcbiAgICAgIGlmICh0aGlzLnRvay50eXBlID09PSB0dC5faW4gfHwgdGhpcy5pc0NvbnRleHR1YWwoXCJvZlwiKSkgcmV0dXJuIHRoaXMucGFyc2VGb3JJbihub2RlLCB0aGlzLnRvQXNzaWduYWJsZShpbml0KSk7XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZUZvcihub2RlLCBpbml0KTtcblxuICAgIGNhc2UgdHQuX2Z1bmN0aW9uOlxuICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZUZ1bmN0aW9uKG5vZGUsIHRydWUpO1xuXG4gICAgY2FzZSB0dC5faWY6XG4gICAgICB0aGlzLm5leHQoKTtcbiAgICAgIG5vZGUudGVzdCA9IHRoaXMucGFyc2VQYXJlbkV4cHJlc3Npb24oKTtcbiAgICAgIG5vZGUuY29uc2VxdWVudCA9IHRoaXMucGFyc2VTdGF0ZW1lbnQoKTtcbiAgICAgIG5vZGUuYWx0ZXJuYXRlID0gdGhpcy5lYXQodHQuX2Vsc2UpID8gdGhpcy5wYXJzZVN0YXRlbWVudCgpIDogbnVsbDtcbiAgICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJJZlN0YXRlbWVudFwiKTtcblxuICAgIGNhc2UgdHQuX3JldHVybjpcbiAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgaWYgKHRoaXMuZWF0KHR0LnNlbWkpIHx8IHRoaXMuY2FuSW5zZXJ0U2VtaWNvbG9uKCkpIG5vZGUuYXJndW1lbnQgPSBudWxsO2Vsc2Uge1xuICAgICAgICBub2RlLmFyZ3VtZW50ID0gdGhpcy5wYXJzZUV4cHJlc3Npb24oKTt0aGlzLnNlbWljb2xvbigpO1xuICAgICAgfVxuICAgICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIlJldHVyblN0YXRlbWVudFwiKTtcblxuICAgIGNhc2UgdHQuX3N3aXRjaDpcbiAgICAgIHZhciBibG9ja0luZGVudCA9IHRoaXMuY3VySW5kZW50LFxuICAgICAgICAgIGxpbmUgPSB0aGlzLmN1ckxpbmVTdGFydDtcbiAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgbm9kZS5kaXNjcmltaW5hbnQgPSB0aGlzLnBhcnNlUGFyZW5FeHByZXNzaW9uKCk7XG4gICAgICBub2RlLmNhc2VzID0gW107XG4gICAgICB0aGlzLnB1c2hDeCgpO1xuICAgICAgdGhpcy5leHBlY3QodHQuYnJhY2VMKTtcblxuICAgICAgdmFyIGN1ciA9IHVuZGVmaW5lZDtcbiAgICAgIHdoaWxlICghdGhpcy5jbG9zZXModHQuYnJhY2VSLCBibG9ja0luZGVudCwgbGluZSwgdHJ1ZSkpIHtcbiAgICAgICAgaWYgKHRoaXMudG9rLnR5cGUgPT09IHR0Ll9jYXNlIHx8IHRoaXMudG9rLnR5cGUgPT09IHR0Ll9kZWZhdWx0KSB7XG4gICAgICAgICAgdmFyIGlzQ2FzZSA9IHRoaXMudG9rLnR5cGUgPT09IHR0Ll9jYXNlO1xuICAgICAgICAgIGlmIChjdXIpIHRoaXMuZmluaXNoTm9kZShjdXIsIFwiU3dpdGNoQ2FzZVwiKTtcbiAgICAgICAgICBub2RlLmNhc2VzLnB1c2goY3VyID0gdGhpcy5zdGFydE5vZGUoKSk7XG4gICAgICAgICAgY3VyLmNvbnNlcXVlbnQgPSBbXTtcbiAgICAgICAgICB0aGlzLm5leHQoKTtcbiAgICAgICAgICBpZiAoaXNDYXNlKSBjdXIudGVzdCA9IHRoaXMucGFyc2VFeHByZXNzaW9uKCk7ZWxzZSBjdXIudGVzdCA9IG51bGw7XG4gICAgICAgICAgdGhpcy5leHBlY3QodHQuY29sb24pO1xuICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgIGlmICghY3VyKSB7XG4gICAgICAgICAgICBub2RlLmNhc2VzLnB1c2goY3VyID0gdGhpcy5zdGFydE5vZGUoKSk7XG4gICAgICAgICAgICBjdXIuY29uc2VxdWVudCA9IFtdO1xuICAgICAgICAgICAgY3VyLnRlc3QgPSBudWxsO1xuICAgICAgICAgIH1cbiAgICAgICAgICBjdXIuY29uc2VxdWVudC5wdXNoKHRoaXMucGFyc2VTdGF0ZW1lbnQoKSk7XG4gICAgICAgIH1cbiAgICAgIH1cbiAgICAgIGlmIChjdXIpIHRoaXMuZmluaXNoTm9kZShjdXIsIFwiU3dpdGNoQ2FzZVwiKTtcbiAgICAgIHRoaXMucG9wQ3goKTtcbiAgICAgIHRoaXMuZWF0KHR0LmJyYWNlUik7XG4gICAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiU3dpdGNoU3RhdGVtZW50XCIpO1xuXG4gICAgY2FzZSB0dC5fdGhyb3c6XG4gICAgICB0aGlzLm5leHQoKTtcbiAgICAgIG5vZGUuYXJndW1lbnQgPSB0aGlzLnBhcnNlRXhwcmVzc2lvbigpO1xuICAgICAgdGhpcy5zZW1pY29sb24oKTtcbiAgICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJUaHJvd1N0YXRlbWVudFwiKTtcblxuICAgIGNhc2UgdHQuX3RyeTpcbiAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgbm9kZS5ibG9jayA9IHRoaXMucGFyc2VCbG9jaygpO1xuICAgICAgbm9kZS5oYW5kbGVyID0gbnVsbDtcbiAgICAgIGlmICh0aGlzLnRvay50eXBlID09PSB0dC5fY2F0Y2gpIHtcbiAgICAgICAgdmFyIGNsYXVzZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gICAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgICB0aGlzLmV4cGVjdCh0dC5wYXJlbkwpO1xuICAgICAgICBjbGF1c2UucGFyYW0gPSB0aGlzLnRvQXNzaWduYWJsZSh0aGlzLnBhcnNlRXhwckF0b20oKSwgdHJ1ZSk7XG4gICAgICAgIHRoaXMuZXhwZWN0KHR0LnBhcmVuUik7XG4gICAgICAgIGNsYXVzZS5ndWFyZCA9IG51bGw7XG4gICAgICAgIGNsYXVzZS5ib2R5ID0gdGhpcy5wYXJzZUJsb2NrKCk7XG4gICAgICAgIG5vZGUuaGFuZGxlciA9IHRoaXMuZmluaXNoTm9kZShjbGF1c2UsIFwiQ2F0Y2hDbGF1c2VcIik7XG4gICAgICB9XG4gICAgICBub2RlLmZpbmFsaXplciA9IHRoaXMuZWF0KHR0Ll9maW5hbGx5KSA/IHRoaXMucGFyc2VCbG9jaygpIDogbnVsbDtcbiAgICAgIGlmICghbm9kZS5oYW5kbGVyICYmICFub2RlLmZpbmFsaXplcikgcmV0dXJuIG5vZGUuYmxvY2s7XG4gICAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiVHJ5U3RhdGVtZW50XCIpO1xuXG4gICAgY2FzZSB0dC5fdmFyOlxuICAgIGNhc2UgdHQuX2xldDpcbiAgICBjYXNlIHR0Ll9jb25zdDpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlVmFyKCk7XG5cbiAgICBjYXNlIHR0Ll93aGlsZTpcbiAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgbm9kZS50ZXN0ID0gdGhpcy5wYXJzZVBhcmVuRXhwcmVzc2lvbigpO1xuICAgICAgbm9kZS5ib2R5ID0gdGhpcy5wYXJzZVN0YXRlbWVudCgpO1xuICAgICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIldoaWxlU3RhdGVtZW50XCIpO1xuXG4gICAgY2FzZSB0dC5fd2l0aDpcbiAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgbm9kZS5vYmplY3QgPSB0aGlzLnBhcnNlUGFyZW5FeHByZXNzaW9uKCk7XG4gICAgICBub2RlLmJvZHkgPSB0aGlzLnBhcnNlU3RhdGVtZW50KCk7XG4gICAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiV2l0aFN0YXRlbWVudFwiKTtcblxuICAgIGNhc2UgdHQuYnJhY2VMOlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VCbG9jaygpO1xuXG4gICAgY2FzZSB0dC5zZW1pOlxuICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiRW1wdHlTdGF0ZW1lbnRcIik7XG5cbiAgICBjYXNlIHR0Ll9jbGFzczpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlQ2xhc3ModHJ1ZSk7XG5cbiAgICBjYXNlIHR0Ll9pbXBvcnQ6XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZUltcG9ydCgpO1xuXG4gICAgY2FzZSB0dC5fZXhwb3J0OlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VFeHBvcnQoKTtcblxuICAgIGRlZmF1bHQ6XG4gICAgICB2YXIgZXhwciA9IHRoaXMucGFyc2VFeHByZXNzaW9uKCk7XG4gICAgICBpZiAoaXNEdW1teShleHByKSkge1xuICAgICAgICB0aGlzLm5leHQoKTtcbiAgICAgICAgaWYgKHRoaXMudG9rLnR5cGUgPT09IHR0LmVvZikgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkVtcHR5U3RhdGVtZW50XCIpO1xuICAgICAgICByZXR1cm4gdGhpcy5wYXJzZVN0YXRlbWVudCgpO1xuICAgICAgfSBlbHNlIGlmIChzdGFydHR5cGUgPT09IHR0Lm5hbWUgJiYgZXhwci50eXBlID09PSBcIklkZW50aWZpZXJcIiAmJiB0aGlzLmVhdCh0dC5jb2xvbikpIHtcbiAgICAgICAgbm9kZS5ib2R5ID0gdGhpcy5wYXJzZVN0YXRlbWVudCgpO1xuICAgICAgICBub2RlLmxhYmVsID0gZXhwcjtcbiAgICAgICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkxhYmVsZWRTdGF0ZW1lbnRcIik7XG4gICAgICB9IGVsc2Uge1xuICAgICAgICBub2RlLmV4cHJlc3Npb24gPSBleHByO1xuICAgICAgICB0aGlzLnNlbWljb2xvbigpO1xuICAgICAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiRXhwcmVzc2lvblN0YXRlbWVudFwiKTtcbiAgICAgIH1cbiAgfVxufTtcblxubHAucGFyc2VCbG9jayA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICB0aGlzLnB1c2hDeCgpO1xuICB0aGlzLmV4cGVjdCh0dC5icmFjZUwpO1xuICB2YXIgYmxvY2tJbmRlbnQgPSB0aGlzLmN1ckluZGVudCxcbiAgICAgIGxpbmUgPSB0aGlzLmN1ckxpbmVTdGFydDtcbiAgbm9kZS5ib2R5ID0gW107XG4gIHdoaWxlICghdGhpcy5jbG9zZXModHQuYnJhY2VSLCBibG9ja0luZGVudCwgbGluZSwgdHJ1ZSkpIG5vZGUuYm9keS5wdXNoKHRoaXMucGFyc2VTdGF0ZW1lbnQoKSk7XG4gIHRoaXMucG9wQ3goKTtcbiAgdGhpcy5lYXQodHQuYnJhY2VSKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkJsb2NrU3RhdGVtZW50XCIpO1xufTtcblxubHAucGFyc2VGb3IgPSBmdW5jdGlvbiAobm9kZSwgaW5pdCkge1xuICBub2RlLmluaXQgPSBpbml0O1xuICBub2RlLnRlc3QgPSBub2RlLnVwZGF0ZSA9IG51bGw7XG4gIGlmICh0aGlzLmVhdCh0dC5zZW1pKSAmJiB0aGlzLnRvay50eXBlICE9PSB0dC5zZW1pKSBub2RlLnRlc3QgPSB0aGlzLnBhcnNlRXhwcmVzc2lvbigpO1xuICBpZiAodGhpcy5lYXQodHQuc2VtaSkgJiYgdGhpcy50b2sudHlwZSAhPT0gdHQucGFyZW5SKSBub2RlLnVwZGF0ZSA9IHRoaXMucGFyc2VFeHByZXNzaW9uKCk7XG4gIHRoaXMucG9wQ3goKTtcbiAgdGhpcy5leHBlY3QodHQucGFyZW5SKTtcbiAgbm9kZS5ib2R5ID0gdGhpcy5wYXJzZVN0YXRlbWVudCgpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiRm9yU3RhdGVtZW50XCIpO1xufTtcblxubHAucGFyc2VGb3JJbiA9IGZ1bmN0aW9uIChub2RlLCBpbml0KSB7XG4gIHZhciB0eXBlID0gdGhpcy50b2sudHlwZSA9PT0gdHQuX2luID8gXCJGb3JJblN0YXRlbWVudFwiIDogXCJGb3JPZlN0YXRlbWVudFwiO1xuICB0aGlzLm5leHQoKTtcbiAgbm9kZS5sZWZ0ID0gaW5pdDtcbiAgbm9kZS5yaWdodCA9IHRoaXMucGFyc2VFeHByZXNzaW9uKCk7XG4gIHRoaXMucG9wQ3goKTtcbiAgdGhpcy5leHBlY3QodHQucGFyZW5SKTtcbiAgbm9kZS5ib2R5ID0gdGhpcy5wYXJzZVN0YXRlbWVudCgpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIHR5cGUpO1xufTtcblxubHAucGFyc2VWYXIgPSBmdW5jdGlvbiAobm9Jbikge1xuICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gIG5vZGUua2luZCA9IHRoaXMudG9rLnR5cGUua2V5d29yZDtcbiAgdGhpcy5uZXh0KCk7XG4gIG5vZGUuZGVjbGFyYXRpb25zID0gW107XG4gIGRvIHtcbiAgICB2YXIgZGVjbCA9IHRoaXMuc3RhcnROb2RlKCk7XG4gICAgZGVjbC5pZCA9IHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2ID8gdGhpcy50b0Fzc2lnbmFibGUodGhpcy5wYXJzZUV4cHJBdG9tKCksIHRydWUpIDogdGhpcy5wYXJzZUlkZW50KCk7XG4gICAgZGVjbC5pbml0ID0gdGhpcy5lYXQodHQuZXEpID8gdGhpcy5wYXJzZU1heWJlQXNzaWduKG5vSW4pIDogbnVsbDtcbiAgICBub2RlLmRlY2xhcmF0aW9ucy5wdXNoKHRoaXMuZmluaXNoTm9kZShkZWNsLCBcIlZhcmlhYmxlRGVjbGFyYXRvclwiKSk7XG4gIH0gd2hpbGUgKHRoaXMuZWF0KHR0LmNvbW1hKSk7XG4gIGlmICghbm9kZS5kZWNsYXJhdGlvbnMubGVuZ3RoKSB7XG4gICAgdmFyIGRlY2wgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICAgIGRlY2wuaWQgPSB0aGlzLmR1bW15SWRlbnQoKTtcbiAgICBub2RlLmRlY2xhcmF0aW9ucy5wdXNoKHRoaXMuZmluaXNoTm9kZShkZWNsLCBcIlZhcmlhYmxlRGVjbGFyYXRvclwiKSk7XG4gIH1cbiAgaWYgKCFub0luKSB0aGlzLnNlbWljb2xvbigpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiVmFyaWFibGVEZWNsYXJhdGlvblwiKTtcbn07XG5cbmxwLnBhcnNlQ2xhc3MgPSBmdW5jdGlvbiAoaXNTdGF0ZW1lbnQpIHtcbiAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICB0aGlzLm5leHQoKTtcbiAgaWYgKHRoaXMudG9rLnR5cGUgPT09IHR0Lm5hbWUpIG5vZGUuaWQgPSB0aGlzLnBhcnNlSWRlbnQoKTtlbHNlIGlmIChpc1N0YXRlbWVudCkgbm9kZS5pZCA9IHRoaXMuZHVtbXlJZGVudCgpO2Vsc2Ugbm9kZS5pZCA9IG51bGw7XG4gIG5vZGUuc3VwZXJDbGFzcyA9IHRoaXMuZWF0KHR0Ll9leHRlbmRzKSA/IHRoaXMucGFyc2VFeHByZXNzaW9uKCkgOiBudWxsO1xuICBub2RlLmJvZHkgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICBub2RlLmJvZHkuYm9keSA9IFtdO1xuICB0aGlzLnB1c2hDeCgpO1xuICB2YXIgaW5kZW50ID0gdGhpcy5jdXJJbmRlbnQgKyAxLFxuICAgICAgbGluZSA9IHRoaXMuY3VyTGluZVN0YXJ0O1xuICB0aGlzLmVhdCh0dC5icmFjZUwpO1xuICBpZiAodGhpcy5jdXJJbmRlbnQgKyAxIDwgaW5kZW50KSB7XG4gICAgaW5kZW50ID0gdGhpcy5jdXJJbmRlbnQ7bGluZSA9IHRoaXMuY3VyTGluZVN0YXJ0O1xuICB9XG4gIHdoaWxlICghdGhpcy5jbG9zZXModHQuYnJhY2VSLCBpbmRlbnQsIGxpbmUpKSB7XG4gICAgaWYgKHRoaXMuc2VtaWNvbG9uKCkpIGNvbnRpbnVlO1xuICAgIHZhciBtZXRob2QgPSB0aGlzLnN0YXJ0Tm9kZSgpLFxuICAgICAgICBpc0dlbmVyYXRvciA9IHVuZGVmaW5lZDtcbiAgICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYpIHtcbiAgICAgIG1ldGhvZFtcInN0YXRpY1wiXSA9IGZhbHNlO1xuICAgICAgaXNHZW5lcmF0b3IgPSB0aGlzLmVhdCh0dC5zdGFyKTtcbiAgICB9XG4gICAgdGhpcy5wYXJzZVByb3BlcnR5TmFtZShtZXRob2QpO1xuICAgIGlmIChpc0R1bW15KG1ldGhvZC5rZXkpKSB7XG4gICAgICBpZiAoaXNEdW1teSh0aGlzLnBhcnNlTWF5YmVBc3NpZ24oKSkpIHRoaXMubmV4dCgpO3RoaXMuZWF0KHR0LmNvbW1hKTtjb250aW51ZTtcbiAgICB9XG4gICAgaWYgKG1ldGhvZC5rZXkudHlwZSA9PT0gXCJJZGVudGlmaWVyXCIgJiYgIW1ldGhvZC5jb21wdXRlZCAmJiBtZXRob2Qua2V5Lm5hbWUgPT09IFwic3RhdGljXCIgJiYgKHRoaXMudG9rLnR5cGUgIT0gdHQucGFyZW5MICYmIHRoaXMudG9rLnR5cGUgIT0gdHQuYnJhY2VMKSkge1xuICAgICAgbWV0aG9kW1wic3RhdGljXCJdID0gdHJ1ZTtcbiAgICAgIGlzR2VuZXJhdG9yID0gdGhpcy5lYXQodHQuc3Rhcik7XG4gICAgICB0aGlzLnBhcnNlUHJvcGVydHlOYW1lKG1ldGhvZCk7XG4gICAgfSBlbHNlIHtcbiAgICAgIG1ldGhvZFtcInN0YXRpY1wiXSA9IGZhbHNlO1xuICAgIH1cbiAgICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDUgJiYgbWV0aG9kLmtleS50eXBlID09PSBcIklkZW50aWZpZXJcIiAmJiAhbWV0aG9kLmNvbXB1dGVkICYmIChtZXRob2Qua2V5Lm5hbWUgPT09IFwiZ2V0XCIgfHwgbWV0aG9kLmtleS5uYW1lID09PSBcInNldFwiKSAmJiB0aGlzLnRvay50eXBlICE9PSB0dC5wYXJlbkwgJiYgdGhpcy50b2sudHlwZSAhPT0gdHQuYnJhY2VMKSB7XG4gICAgICBtZXRob2Qua2luZCA9IG1ldGhvZC5rZXkubmFtZTtcbiAgICAgIHRoaXMucGFyc2VQcm9wZXJ0eU5hbWUobWV0aG9kKTtcbiAgICAgIG1ldGhvZC52YWx1ZSA9IHRoaXMucGFyc2VNZXRob2QoZmFsc2UpO1xuICAgIH0gZWxzZSB7XG4gICAgICBpZiAoIW1ldGhvZC5jb21wdXRlZCAmJiAhbWV0aG9kW1wic3RhdGljXCJdICYmICFpc0dlbmVyYXRvciAmJiAobWV0aG9kLmtleS50eXBlID09PSBcIklkZW50aWZpZXJcIiAmJiBtZXRob2Qua2V5Lm5hbWUgPT09IFwiY29uc3RydWN0b3JcIiB8fCBtZXRob2Qua2V5LnR5cGUgPT09IFwiTGl0ZXJhbFwiICYmIG1ldGhvZC5rZXkudmFsdWUgPT09IFwiY29uc3RydWN0b3JcIikpIHtcbiAgICAgICAgbWV0aG9kLmtpbmQgPSBcImNvbnN0cnVjdG9yXCI7XG4gICAgICB9IGVsc2Uge1xuICAgICAgICBtZXRob2Qua2luZCA9IFwibWV0aG9kXCI7XG4gICAgICB9XG4gICAgICBtZXRob2QudmFsdWUgPSB0aGlzLnBhcnNlTWV0aG9kKGlzR2VuZXJhdG9yKTtcbiAgICB9XG4gICAgbm9kZS5ib2R5LmJvZHkucHVzaCh0aGlzLmZpbmlzaE5vZGUobWV0aG9kLCBcIk1ldGhvZERlZmluaXRpb25cIikpO1xuICB9XG4gIHRoaXMucG9wQ3goKTtcbiAgaWYgKCF0aGlzLmVhdCh0dC5icmFjZVIpKSB7XG4gICAgLy8gSWYgdGhlcmUgaXMgbm8gY2xvc2luZyBicmFjZSwgbWFrZSB0aGUgbm9kZSBzcGFuIHRvIHRoZSBzdGFydFxuICAgIC8vIG9mIHRoZSBuZXh0IHRva2VuICh0aGlzIGlzIHVzZWZ1bCBmb3IgVGVybilcbiAgICB0aGlzLmxhc3QuZW5kID0gdGhpcy50b2suc3RhcnQ7XG4gICAgaWYgKHRoaXMub3B0aW9ucy5sb2NhdGlvbnMpIHRoaXMubGFzdC5sb2MuZW5kID0gdGhpcy50b2subG9jLnN0YXJ0O1xuICB9XG4gIHRoaXMuc2VtaWNvbG9uKCk7XG4gIHRoaXMuZmluaXNoTm9kZShub2RlLmJvZHksIFwiQ2xhc3NCb2R5XCIpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIGlzU3RhdGVtZW50ID8gXCJDbGFzc0RlY2xhcmF0aW9uXCIgOiBcIkNsYXNzRXhwcmVzc2lvblwiKTtcbn07XG5cbmxwLnBhcnNlRnVuY3Rpb24gPSBmdW5jdGlvbiAobm9kZSwgaXNTdGF0ZW1lbnQpIHtcbiAgdGhpcy5pbml0RnVuY3Rpb24obm9kZSk7XG4gIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNikge1xuICAgIG5vZGUuZ2VuZXJhdG9yID0gdGhpcy5lYXQodHQuc3Rhcik7XG4gIH1cbiAgaWYgKHRoaXMudG9rLnR5cGUgPT09IHR0Lm5hbWUpIG5vZGUuaWQgPSB0aGlzLnBhcnNlSWRlbnQoKTtlbHNlIGlmIChpc1N0YXRlbWVudCkgbm9kZS5pZCA9IHRoaXMuZHVtbXlJZGVudCgpO1xuICBub2RlLnBhcmFtcyA9IHRoaXMucGFyc2VGdW5jdGlvblBhcmFtcygpO1xuICBub2RlLmJvZHkgPSB0aGlzLnBhcnNlQmxvY2soKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBpc1N0YXRlbWVudCA/IFwiRnVuY3Rpb25EZWNsYXJhdGlvblwiIDogXCJGdW5jdGlvbkV4cHJlc3Npb25cIik7XG59O1xuXG5scC5wYXJzZUV4cG9ydCA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICB0aGlzLm5leHQoKTtcbiAgaWYgKHRoaXMuZWF0KHR0LnN0YXIpKSB7XG4gICAgbm9kZS5zb3VyY2UgPSB0aGlzLmVhdENvbnRleHR1YWwoXCJmcm9tXCIpID8gdGhpcy5wYXJzZUV4cHJBdG9tKCkgOiBudWxsO1xuICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJFeHBvcnRBbGxEZWNsYXJhdGlvblwiKTtcbiAgfVxuICBpZiAodGhpcy5lYXQodHQuX2RlZmF1bHQpKSB7XG4gICAgdmFyIGV4cHIgPSB0aGlzLnBhcnNlTWF5YmVBc3NpZ24oKTtcbiAgICBpZiAoZXhwci5pZCkge1xuICAgICAgc3dpdGNoIChleHByLnR5cGUpIHtcbiAgICAgICAgY2FzZSBcIkZ1bmN0aW9uRXhwcmVzc2lvblwiOlxuICAgICAgICAgIGV4cHIudHlwZSA9IFwiRnVuY3Rpb25EZWNsYXJhdGlvblwiO2JyZWFrO1xuICAgICAgICBjYXNlIFwiQ2xhc3NFeHByZXNzaW9uXCI6XG4gICAgICAgICAgZXhwci50eXBlID0gXCJDbGFzc0RlY2xhcmF0aW9uXCI7YnJlYWs7XG4gICAgICB9XG4gICAgfVxuICAgIG5vZGUuZGVjbGFyYXRpb24gPSBleHByO1xuICAgIHRoaXMuc2VtaWNvbG9uKCk7XG4gICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkV4cG9ydERlZmF1bHREZWNsYXJhdGlvblwiKTtcbiAgfVxuICBpZiAodGhpcy50b2sudHlwZS5rZXl3b3JkKSB7XG4gICAgbm9kZS5kZWNsYXJhdGlvbiA9IHRoaXMucGFyc2VTdGF0ZW1lbnQoKTtcbiAgICBub2RlLnNwZWNpZmllcnMgPSBbXTtcbiAgICBub2RlLnNvdXJjZSA9IG51bGw7XG4gIH0gZWxzZSB7XG4gICAgbm9kZS5kZWNsYXJhdGlvbiA9IG51bGw7XG4gICAgbm9kZS5zcGVjaWZpZXJzID0gdGhpcy5wYXJzZUV4cG9ydFNwZWNpZmllckxpc3QoKTtcbiAgICBub2RlLnNvdXJjZSA9IHRoaXMuZWF0Q29udGV4dHVhbChcImZyb21cIikgPyB0aGlzLnBhcnNlRXhwckF0b20oKSA6IG51bGw7XG4gICAgdGhpcy5zZW1pY29sb24oKTtcbiAgfVxuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiRXhwb3J0TmFtZWREZWNsYXJhdGlvblwiKTtcbn07XG5cbmxwLnBhcnNlSW1wb3J0ID0gZnVuY3Rpb24gKCkge1xuICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gIHRoaXMubmV4dCgpO1xuICBpZiAodGhpcy50b2sudHlwZSA9PT0gdHQuc3RyaW5nKSB7XG4gICAgbm9kZS5zcGVjaWZpZXJzID0gW107XG4gICAgbm9kZS5zb3VyY2UgPSB0aGlzLnBhcnNlRXhwckF0b20oKTtcbiAgICBub2RlLmtpbmQgPSBcIlwiO1xuICB9IGVsc2Uge1xuICAgIHZhciBlbHQgPSB1bmRlZmluZWQ7XG4gICAgaWYgKHRoaXMudG9rLnR5cGUgPT09IHR0Lm5hbWUgJiYgdGhpcy50b2sudmFsdWUgIT09IFwiZnJvbVwiKSB7XG4gICAgICBlbHQgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICAgICAgZWx0LmxvY2FsID0gdGhpcy5wYXJzZUlkZW50KCk7XG4gICAgICB0aGlzLmZpbmlzaE5vZGUoZWx0LCBcIkltcG9ydERlZmF1bHRTcGVjaWZpZXJcIik7XG4gICAgICB0aGlzLmVhdCh0dC5jb21tYSk7XG4gICAgfVxuICAgIG5vZGUuc3BlY2lmaWVycyA9IHRoaXMucGFyc2VJbXBvcnRTcGVjaWZpZXJMaXN0KCk7XG4gICAgbm9kZS5zb3VyY2UgPSB0aGlzLmVhdENvbnRleHR1YWwoXCJmcm9tXCIpID8gdGhpcy5wYXJzZUV4cHJBdG9tKCkgOiBudWxsO1xuICAgIGlmIChlbHQpIG5vZGUuc3BlY2lmaWVycy51bnNoaWZ0KGVsdCk7XG4gIH1cbiAgdGhpcy5zZW1pY29sb24oKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkltcG9ydERlY2xhcmF0aW9uXCIpO1xufTtcblxubHAucGFyc2VJbXBvcnRTcGVjaWZpZXJMaXN0ID0gZnVuY3Rpb24gKCkge1xuICB2YXIgZWx0cyA9IFtdO1xuICBpZiAodGhpcy50b2sudHlwZSA9PT0gdHQuc3Rhcikge1xuICAgIHZhciBlbHQgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICAgIHRoaXMubmV4dCgpO1xuICAgIGlmICh0aGlzLmVhdENvbnRleHR1YWwoXCJhc1wiKSkgZWx0LmxvY2FsID0gdGhpcy5wYXJzZUlkZW50KCk7XG4gICAgZWx0cy5wdXNoKHRoaXMuZmluaXNoTm9kZShlbHQsIFwiSW1wb3J0TmFtZXNwYWNlU3BlY2lmaWVyXCIpKTtcbiAgfSBlbHNlIHtcbiAgICB2YXIgaW5kZW50ID0gdGhpcy5jdXJJbmRlbnQsXG4gICAgICAgIGxpbmUgPSB0aGlzLmN1ckxpbmVTdGFydCxcbiAgICAgICAgY29udGludWVkTGluZSA9IHRoaXMubmV4dExpbmVTdGFydDtcbiAgICB0aGlzLnB1c2hDeCgpO1xuICAgIHRoaXMuZWF0KHR0LmJyYWNlTCk7XG4gICAgaWYgKHRoaXMuY3VyTGluZVN0YXJ0ID4gY29udGludWVkTGluZSkgY29udGludWVkTGluZSA9IHRoaXMuY3VyTGluZVN0YXJ0O1xuICAgIHdoaWxlICghdGhpcy5jbG9zZXModHQuYnJhY2VSLCBpbmRlbnQgKyAodGhpcy5jdXJMaW5lU3RhcnQgPD0gY29udGludWVkTGluZSA/IDEgOiAwKSwgbGluZSkpIHtcbiAgICAgIHZhciBlbHQgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICAgICAgaWYgKHRoaXMuZWF0KHR0LnN0YXIpKSB7XG4gICAgICAgIGlmICh0aGlzLmVhdENvbnRleHR1YWwoXCJhc1wiKSkgZWx0LmxvY2FsID0gdGhpcy5wYXJzZUlkZW50KCk7XG4gICAgICAgIHRoaXMuZmluaXNoTm9kZShlbHQsIFwiSW1wb3J0TmFtZXNwYWNlU3BlY2lmaWVyXCIpO1xuICAgICAgfSBlbHNlIHtcbiAgICAgICAgaWYgKHRoaXMuaXNDb250ZXh0dWFsKFwiZnJvbVwiKSkgYnJlYWs7XG4gICAgICAgIGVsdC5pbXBvcnRlZCA9IHRoaXMucGFyc2VJZGVudCgpO1xuICAgICAgICBlbHQubG9jYWwgPSB0aGlzLmVhdENvbnRleHR1YWwoXCJhc1wiKSA/IHRoaXMucGFyc2VJZGVudCgpIDogZWx0LmltcG9ydGVkO1xuICAgICAgICB0aGlzLmZpbmlzaE5vZGUoZWx0LCBcIkltcG9ydFNwZWNpZmllclwiKTtcbiAgICAgIH1cbiAgICAgIGVsdHMucHVzaChlbHQpO1xuICAgICAgdGhpcy5lYXQodHQuY29tbWEpO1xuICAgIH1cbiAgICB0aGlzLmVhdCh0dC5icmFjZVIpO1xuICAgIHRoaXMucG9wQ3goKTtcbiAgfVxuICByZXR1cm4gZWx0cztcbn07XG5cbmxwLnBhcnNlRXhwb3J0U3BlY2lmaWVyTGlzdCA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIGVsdHMgPSBbXTtcbiAgdmFyIGluZGVudCA9IHRoaXMuY3VySW5kZW50LFxuICAgICAgbGluZSA9IHRoaXMuY3VyTGluZVN0YXJ0LFxuICAgICAgY29udGludWVkTGluZSA9IHRoaXMubmV4dExpbmVTdGFydDtcbiAgdGhpcy5wdXNoQ3goKTtcbiAgdGhpcy5lYXQodHQuYnJhY2VMKTtcbiAgaWYgKHRoaXMuY3VyTGluZVN0YXJ0ID4gY29udGludWVkTGluZSkgY29udGludWVkTGluZSA9IHRoaXMuY3VyTGluZVN0YXJ0O1xuICB3aGlsZSAoIXRoaXMuY2xvc2VzKHR0LmJyYWNlUiwgaW5kZW50ICsgKHRoaXMuY3VyTGluZVN0YXJ0IDw9IGNvbnRpbnVlZExpbmUgPyAxIDogMCksIGxpbmUpKSB7XG4gICAgaWYgKHRoaXMuaXNDb250ZXh0dWFsKFwiZnJvbVwiKSkgYnJlYWs7XG4gICAgdmFyIGVsdCA9IHRoaXMuc3RhcnROb2RlKCk7XG4gICAgZWx0LmxvY2FsID0gdGhpcy5wYXJzZUlkZW50KCk7XG4gICAgZWx0LmV4cG9ydGVkID0gdGhpcy5lYXRDb250ZXh0dWFsKFwiYXNcIikgPyB0aGlzLnBhcnNlSWRlbnQoKSA6IGVsdC5sb2NhbDtcbiAgICB0aGlzLmZpbmlzaE5vZGUoZWx0LCBcIkV4cG9ydFNwZWNpZmllclwiKTtcbiAgICBlbHRzLnB1c2goZWx0KTtcbiAgICB0aGlzLmVhdCh0dC5jb21tYSk7XG4gIH1cbiAgdGhpcy5lYXQodHQuYnJhY2VSKTtcbiAgdGhpcy5wb3BDeCgpO1xuICByZXR1cm4gZWx0cztcbn07XG5cbn0se1wiLi5cIjozLFwiLi9wYXJzZXV0aWxcIjo1LFwiLi9zdGF0ZVwiOjZ9XSw4OltmdW5jdGlvbihfZGVyZXFfLG1vZHVsZSxleHBvcnRzKXtcblwidXNlIHN0cmljdFwiO1xuXG52YXIgXyA9IF9kZXJlcV8oXCIuLlwiKTtcblxudmFyIHR0ID0gXy50b2tUeXBlcztcbnZhciBUb2tlbiA9IF8uVG9rZW47XG52YXIgaXNOZXdMaW5lID0gXy5pc05ld0xpbmU7XG52YXIgU291cmNlTG9jYXRpb24gPSBfLlNvdXJjZUxvY2F0aW9uO1xudmFyIGdldExpbmVJbmZvID0gXy5nZXRMaW5lSW5mbztcbnZhciBsaW5lQnJlYWtHID0gXy5saW5lQnJlYWtHO1xuXG52YXIgTG9vc2VQYXJzZXIgPSBfZGVyZXFfKFwiLi9zdGF0ZVwiKS5Mb29zZVBhcnNlcjtcblxudmFyIGxwID0gTG9vc2VQYXJzZXIucHJvdG90eXBlO1xuXG5mdW5jdGlvbiBpc1NwYWNlKGNoKSB7XG4gIHJldHVybiBjaCA8IDE0ICYmIGNoID4gOCB8fCBjaCA9PT0gMzIgfHwgY2ggPT09IDE2MCB8fCBpc05ld0xpbmUoY2gpO1xufVxuXG5scC5uZXh0ID0gZnVuY3Rpb24gKCkge1xuICB0aGlzLmxhc3QgPSB0aGlzLnRvaztcbiAgaWYgKHRoaXMuYWhlYWQubGVuZ3RoKSB0aGlzLnRvayA9IHRoaXMuYWhlYWQuc2hpZnQoKTtlbHNlIHRoaXMudG9rID0gdGhpcy5yZWFkVG9rZW4oKTtcblxuICBpZiAodGhpcy50b2suc3RhcnQgPj0gdGhpcy5uZXh0TGluZVN0YXJ0KSB7XG4gICAgd2hpbGUgKHRoaXMudG9rLnN0YXJ0ID49IHRoaXMubmV4dExpbmVTdGFydCkge1xuICAgICAgdGhpcy5jdXJMaW5lU3RhcnQgPSB0aGlzLm5leHRMaW5lU3RhcnQ7XG4gICAgICB0aGlzLm5leHRMaW5lU3RhcnQgPSB0aGlzLmxpbmVFbmQodGhpcy5jdXJMaW5lU3RhcnQpICsgMTtcbiAgICB9XG4gICAgdGhpcy5jdXJJbmRlbnQgPSB0aGlzLmluZGVudGF0aW9uQWZ0ZXIodGhpcy5jdXJMaW5lU3RhcnQpO1xuICB9XG59O1xuXG5scC5yZWFkVG9rZW4gPSBmdW5jdGlvbiAoKSB7XG4gIGZvciAoOzspIHtcbiAgICB0cnkge1xuICAgICAgdGhpcy50b2tzLm5leHQoKTtcbiAgICAgIGlmICh0aGlzLnRva3MudHlwZSA9PT0gdHQuZG90ICYmIHRoaXMuaW5wdXQuc3Vic3RyKHRoaXMudG9rcy5lbmQsIDEpID09PSBcIi5cIiAmJiB0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNikge1xuICAgICAgICB0aGlzLnRva3MuZW5kKys7XG4gICAgICAgIHRoaXMudG9rcy50eXBlID0gdHQuZWxsaXBzaXM7XG4gICAgICB9XG4gICAgICByZXR1cm4gbmV3IFRva2VuKHRoaXMudG9rcyk7XG4gICAgfSBjYXRjaCAoZSkge1xuICAgICAgaWYgKCEoZSBpbnN0YW5jZW9mIFN5bnRheEVycm9yKSkgdGhyb3cgZTtcblxuICAgICAgLy8gVHJ5IHRvIHNraXAgc29tZSB0ZXh0LCBiYXNlZCBvbiB0aGUgZXJyb3IgbWVzc2FnZSwgYW5kIHRoZW4gY29udGludWVcbiAgICAgIHZhciBtc2cgPSBlLm1lc3NhZ2UsXG4gICAgICAgICAgcG9zID0gZS5yYWlzZWRBdCxcbiAgICAgICAgICByZXBsYWNlID0gdHJ1ZTtcbiAgICAgIGlmICgvdW50ZXJtaW5hdGVkL2kudGVzdChtc2cpKSB7XG4gICAgICAgIHBvcyA9IHRoaXMubGluZUVuZChlLnBvcyArIDEpO1xuICAgICAgICBpZiAoL3N0cmluZy8udGVzdChtc2cpKSB7XG4gICAgICAgICAgcmVwbGFjZSA9IHsgc3RhcnQ6IGUucG9zLCBlbmQ6IHBvcywgdHlwZTogdHQuc3RyaW5nLCB2YWx1ZTogdGhpcy5pbnB1dC5zbGljZShlLnBvcyArIDEsIHBvcykgfTtcbiAgICAgICAgfSBlbHNlIGlmICgvcmVndWxhciBleHByL2kudGVzdChtc2cpKSB7XG4gICAgICAgICAgdmFyIHJlID0gdGhpcy5pbnB1dC5zbGljZShlLnBvcywgcG9zKTtcbiAgICAgICAgICB0cnkge1xuICAgICAgICAgICAgcmUgPSBuZXcgUmVnRXhwKHJlKTtcbiAgICAgICAgICB9IGNhdGNoIChlKSB7fVxuICAgICAgICAgIHJlcGxhY2UgPSB7IHN0YXJ0OiBlLnBvcywgZW5kOiBwb3MsIHR5cGU6IHR0LnJlZ2V4cCwgdmFsdWU6IHJlIH07XG4gICAgICAgIH0gZWxzZSBpZiAoL3RlbXBsYXRlLy50ZXN0KG1zZykpIHtcbiAgICAgICAgICByZXBsYWNlID0geyBzdGFydDogZS5wb3MsIGVuZDogcG9zLFxuICAgICAgICAgICAgdHlwZTogdHQudGVtcGxhdGUsXG4gICAgICAgICAgICB2YWx1ZTogdGhpcy5pbnB1dC5zbGljZShlLnBvcywgcG9zKSB9O1xuICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgIHJlcGxhY2UgPSBmYWxzZTtcbiAgICAgICAgfVxuICAgICAgfSBlbHNlIGlmICgvaW52YWxpZCAodW5pY29kZXxyZWdleHB8bnVtYmVyKXxleHBlY3RpbmcgdW5pY29kZXxvY3RhbCBsaXRlcmFsfGlzIHJlc2VydmVkfGRpcmVjdGx5IGFmdGVyIG51bWJlcnxleHBlY3RlZCBudW1iZXIgaW4gcmFkaXgvaS50ZXN0KG1zZykpIHtcbiAgICAgICAgd2hpbGUgKHBvcyA8IHRoaXMuaW5wdXQubGVuZ3RoICYmICFpc1NwYWNlKHRoaXMuaW5wdXQuY2hhckNvZGVBdChwb3MpKSkgKytwb3M7XG4gICAgICB9IGVsc2UgaWYgKC9jaGFyYWN0ZXIgZXNjYXBlfGV4cGVjdGVkIGhleGFkZWNpbWFsL2kudGVzdChtc2cpKSB7XG4gICAgICAgIHdoaWxlIChwb3MgPCB0aGlzLmlucHV0Lmxlbmd0aCkge1xuICAgICAgICAgIHZhciBjaCA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdChwb3MrKyk7XG4gICAgICAgICAgaWYgKGNoID09PSAzNCB8fCBjaCA9PT0gMzkgfHwgaXNOZXdMaW5lKGNoKSkgYnJlYWs7XG4gICAgICAgIH1cbiAgICAgIH0gZWxzZSBpZiAoL3VuZXhwZWN0ZWQgY2hhcmFjdGVyL2kudGVzdChtc2cpKSB7XG4gICAgICAgIHBvcysrO1xuICAgICAgICByZXBsYWNlID0gZmFsc2U7XG4gICAgICB9IGVsc2UgaWYgKC9yZWd1bGFyIGV4cHJlc3Npb24vaS50ZXN0KG1zZykpIHtcbiAgICAgICAgcmVwbGFjZSA9IHRydWU7XG4gICAgICB9IGVsc2Uge1xuICAgICAgICB0aHJvdyBlO1xuICAgICAgfVxuICAgICAgdGhpcy5yZXNldFRvKHBvcyk7XG4gICAgICBpZiAocmVwbGFjZSA9PT0gdHJ1ZSkgcmVwbGFjZSA9IHsgc3RhcnQ6IHBvcywgZW5kOiBwb3MsIHR5cGU6IHR0Lm5hbWUsIHZhbHVlOiBcIuKcllwiIH07XG4gICAgICBpZiAocmVwbGFjZSkge1xuICAgICAgICBpZiAodGhpcy5vcHRpb25zLmxvY2F0aW9ucykgcmVwbGFjZS5sb2MgPSBuZXcgU291cmNlTG9jYXRpb24odGhpcy50b2tzLCBnZXRMaW5lSW5mbyh0aGlzLmlucHV0LCByZXBsYWNlLnN0YXJ0KSwgZ2V0TGluZUluZm8odGhpcy5pbnB1dCwgcmVwbGFjZS5lbmQpKTtcbiAgICAgICAgcmV0dXJuIHJlcGxhY2U7XG4gICAgICB9XG4gICAgfVxuICB9XG59O1xuXG5scC5yZXNldFRvID0gZnVuY3Rpb24gKHBvcykge1xuICB0aGlzLnRva3MucG9zID0gcG9zO1xuICB2YXIgY2ggPSB0aGlzLmlucHV0LmNoYXJBdChwb3MgLSAxKTtcbiAgdGhpcy50b2tzLmV4cHJBbGxvd2VkID0gIWNoIHx8IC9bXFxbXFx7XFwoLDs6P1xcLyo9K1xcLX4hfCYlXjw+XS8udGVzdChjaCkgfHwgL1tlbndmZF0vLnRlc3QoY2gpICYmIC9cXGIoa2V5d29yZHN8Y2FzZXxlbHNlfHJldHVybnx0aHJvd3xuZXd8aW58KGluc3RhbmNlfHR5cGUpb2Z8ZGVsZXRlfHZvaWQpJC8udGVzdCh0aGlzLmlucHV0LnNsaWNlKHBvcyAtIDEwLCBwb3MpKTtcblxuICBpZiAodGhpcy5vcHRpb25zLmxvY2F0aW9ucykge1xuICAgIHRoaXMudG9rcy5jdXJMaW5lID0gMTtcbiAgICB0aGlzLnRva3MubGluZVN0YXJ0ID0gbGluZUJyZWFrRy5sYXN0SW5kZXggPSAwO1xuICAgIHZhciBtYXRjaCA9IHVuZGVmaW5lZDtcbiAgICB3aGlsZSAoKG1hdGNoID0gbGluZUJyZWFrRy5leGVjKHRoaXMuaW5wdXQpKSAmJiBtYXRjaC5pbmRleCA8IHBvcykge1xuICAgICAgKyt0aGlzLnRva3MuY3VyTGluZTtcbiAgICAgIHRoaXMudG9rcy5saW5lU3RhcnQgPSBtYXRjaC5pbmRleCArIG1hdGNoWzBdLmxlbmd0aDtcbiAgICB9XG4gIH1cbn07XG5cbmxwLmxvb2tBaGVhZCA9IGZ1bmN0aW9uIChuKSB7XG4gIHdoaWxlIChuID4gdGhpcy5haGVhZC5sZW5ndGgpIHRoaXMuYWhlYWQucHVzaCh0aGlzLnJlYWRUb2tlbigpKTtcbiAgcmV0dXJuIHRoaXMuYWhlYWRbbiAtIDFdO1xufTtcblxufSx7XCIuLlwiOjMsXCIuL3N0YXRlXCI6Nn1dfSx7fSxbMV0pKDEpXG59KTsiLCIoZnVuY3Rpb24oZil7aWYodHlwZW9mIGV4cG9ydHM9PT1cIm9iamVjdFwiJiZ0eXBlb2YgbW9kdWxlIT09XCJ1bmRlZmluZWRcIil7bW9kdWxlLmV4cG9ydHM9ZigpfWVsc2UgaWYodHlwZW9mIGRlZmluZT09PVwiZnVuY3Rpb25cIiYmZGVmaW5lLmFtZCl7ZGVmaW5lKFtdLGYpfWVsc2V7dmFyIGc7aWYodHlwZW9mIHdpbmRvdyE9PVwidW5kZWZpbmVkXCIpe2c9d2luZG93fWVsc2UgaWYodHlwZW9mIGdsb2JhbCE9PVwidW5kZWZpbmVkXCIpe2c9Z2xvYmFsfWVsc2UgaWYodHlwZW9mIHNlbGYhPT1cInVuZGVmaW5lZFwiKXtnPXNlbGZ9ZWxzZXtnPXRoaXN9KGcuYWNvcm4gfHwgKGcuYWNvcm4gPSB7fSkpLndhbGsgPSBmKCl9fSkoZnVuY3Rpb24oKXt2YXIgZGVmaW5lLG1vZHVsZSxleHBvcnRzO3JldHVybiAoZnVuY3Rpb24gZSh0LG4scil7ZnVuY3Rpb24gcyhvLHUpe2lmKCFuW29dKXtpZighdFtvXSl7dmFyIGE9dHlwZW9mIHJlcXVpcmU9PVwiZnVuY3Rpb25cIiYmcmVxdWlyZTtpZighdSYmYSlyZXR1cm4gYShvLCEwKTtpZihpKXJldHVybiBpKG8sITApO3ZhciBmPW5ldyBFcnJvcihcIkNhbm5vdCBmaW5kIG1vZHVsZSAnXCIrbytcIidcIik7dGhyb3cgZi5jb2RlPVwiTU9EVUxFX05PVF9GT1VORFwiLGZ9dmFyIGw9bltvXT17ZXhwb3J0czp7fX07dFtvXVswXS5jYWxsKGwuZXhwb3J0cyxmdW5jdGlvbihlKXt2YXIgbj10W29dWzFdW2VdO3JldHVybiBzKG4/bjplKX0sbCxsLmV4cG9ydHMsZSx0LG4scil9cmV0dXJuIG5bb10uZXhwb3J0c312YXIgaT10eXBlb2YgcmVxdWlyZT09XCJmdW5jdGlvblwiJiZyZXF1aXJlO2Zvcih2YXIgbz0wO288ci5sZW5ndGg7bysrKXMocltvXSk7cmV0dXJuIHN9KSh7MTpbZnVuY3Rpb24oX2RlcmVxXyxtb2R1bGUsZXhwb3J0cyl7XG5cInVzZSBzdHJpY3RcIjtcblxudmFyIF9jbGFzc0NhbGxDaGVjayA9IGZ1bmN0aW9uIChpbnN0YW5jZSwgQ29uc3RydWN0b3IpIHsgaWYgKCEoaW5zdGFuY2UgaW5zdGFuY2VvZiBDb25zdHJ1Y3RvcikpIHsgdGhyb3cgbmV3IFR5cGVFcnJvcihcIkNhbm5vdCBjYWxsIGEgY2xhc3MgYXMgYSBmdW5jdGlvblwiKTsgfSB9O1xuXG4vLyBBU1Qgd2Fsa2VyIG1vZHVsZSBmb3IgTW96aWxsYSBQYXJzZXIgQVBJIGNvbXBhdGlibGUgdHJlZXNcblxuLy8gQSBzaW1wbGUgd2FsayBpcyBvbmUgd2hlcmUgeW91IHNpbXBseSBzcGVjaWZ5IGNhbGxiYWNrcyB0byBiZVxuLy8gY2FsbGVkIG9uIHNwZWNpZmljIG5vZGVzLiBUaGUgbGFzdCB0d28gYXJndW1lbnRzIGFyZSBvcHRpb25hbC4gQVxuLy8gc2ltcGxlIHVzZSB3b3VsZCBiZVxuLy9cbi8vICAgICB3YWxrLnNpbXBsZShteVRyZWUsIHtcbi8vICAgICAgICAgRXhwcmVzc2lvbjogZnVuY3Rpb24obm9kZSkgeyAuLi4gfVxuLy8gICAgIH0pO1xuLy9cbi8vIHRvIGRvIHNvbWV0aGluZyB3aXRoIGFsbCBleHByZXNzaW9ucy4gQWxsIFBhcnNlciBBUEkgbm9kZSB0eXBlc1xuLy8gY2FuIGJlIHVzZWQgdG8gaWRlbnRpZnkgbm9kZSB0eXBlcywgYXMgd2VsbCBhcyBFeHByZXNzaW9uLFxuLy8gU3RhdGVtZW50LCBhbmQgU2NvcGVCb2R5LCB3aGljaCBkZW5vdGUgY2F0ZWdvcmllcyBvZiBub2Rlcy5cbi8vXG4vLyBUaGUgYmFzZSBhcmd1bWVudCBjYW4gYmUgdXNlZCB0byBwYXNzIGEgY3VzdG9tIChyZWN1cnNpdmUpXG4vLyB3YWxrZXIsIGFuZCBzdGF0ZSBjYW4gYmUgdXNlZCB0byBnaXZlIHRoaXMgd2Fsa2VkIGFuIGluaXRpYWxcbi8vIHN0YXRlLlxuXG5leHBvcnRzLnNpbXBsZSA9IHNpbXBsZTtcblxuLy8gQW4gYW5jZXN0b3Igd2FsayBidWlsZHMgdXAgYW4gYXJyYXkgb2YgYW5jZXN0b3Igbm9kZXMgKGluY2x1ZGluZ1xuLy8gdGhlIGN1cnJlbnQgbm9kZSkgYW5kIHBhc3NlcyB0aGVtIHRvIHRoZSBjYWxsYmFjayBhcyB0aGUgc3RhdGUgcGFyYW1ldGVyLlxuZXhwb3J0cy5hbmNlc3RvciA9IGFuY2VzdG9yO1xuXG4vLyBBIHJlY3Vyc2l2ZSB3YWxrIGlzIG9uZSB3aGVyZSB5b3VyIGZ1bmN0aW9ucyBvdmVycmlkZSB0aGUgZGVmYXVsdFxuLy8gd2Fsa2Vycy4gVGhleSBjYW4gbW9kaWZ5IGFuZCByZXBsYWNlIHRoZSBzdGF0ZSBwYXJhbWV0ZXIgdGhhdCdzXG4vLyB0aHJlYWRlZCB0aHJvdWdoIHRoZSB3YWxrLCBhbmQgY2FuIG9wdCBob3cgYW5kIHdoZXRoZXIgdG8gd2Fsa1xuLy8gdGhlaXIgY2hpbGQgbm9kZXMgKGJ5IGNhbGxpbmcgdGhlaXIgdGhpcmQgYXJndW1lbnQgb24gdGhlc2Vcbi8vIG5vZGVzKS5cbmV4cG9ydHMucmVjdXJzaXZlID0gcmVjdXJzaXZlO1xuXG4vLyBGaW5kIGEgbm9kZSB3aXRoIGEgZ2l2ZW4gc3RhcnQsIGVuZCwgYW5kIHR5cGUgKGFsbCBhcmUgb3B0aW9uYWwsXG4vLyBudWxsIGNhbiBiZSB1c2VkIGFzIHdpbGRjYXJkKS4gUmV0dXJucyBhIHtub2RlLCBzdGF0ZX0gb2JqZWN0LCBvclxuLy8gdW5kZWZpbmVkIHdoZW4gaXQgZG9lc24ndCBmaW5kIGEgbWF0Y2hpbmcgbm9kZS5cbmV4cG9ydHMuZmluZE5vZGVBdCA9IGZpbmROb2RlQXQ7XG5cbi8vIEZpbmQgdGhlIGlubmVybW9zdCBub2RlIG9mIGEgZ2l2ZW4gdHlwZSB0aGF0IGNvbnRhaW5zIHRoZSBnaXZlblxuLy8gcG9zaXRpb24uIEludGVyZmFjZSBzaW1pbGFyIHRvIGZpbmROb2RlQXQuXG5leHBvcnRzLmZpbmROb2RlQXJvdW5kID0gZmluZE5vZGVBcm91bmQ7XG5cbi8vIEZpbmQgdGhlIG91dGVybW9zdCBtYXRjaGluZyBub2RlIGFmdGVyIGEgZ2l2ZW4gcG9zaXRpb24uXG5leHBvcnRzLmZpbmROb2RlQWZ0ZXIgPSBmaW5kTm9kZUFmdGVyO1xuXG4vLyBGaW5kIHRoZSBvdXRlcm1vc3QgbWF0Y2hpbmcgbm9kZSBiZWZvcmUgYSBnaXZlbiBwb3NpdGlvbi5cbmV4cG9ydHMuZmluZE5vZGVCZWZvcmUgPSBmaW5kTm9kZUJlZm9yZTtcblxuLy8gVXNlZCB0byBjcmVhdGUgYSBjdXN0b20gd2Fsa2VyLiBXaWxsIGZpbGwgaW4gYWxsIG1pc3Npbmcgbm9kZVxuLy8gdHlwZSBwcm9wZXJ0aWVzIHdpdGggdGhlIGRlZmF1bHRzLlxuZXhwb3J0cy5tYWtlID0gbWFrZTtcbmV4cG9ydHMuX19lc01vZHVsZSA9IHRydWU7XG5cbmZ1bmN0aW9uIHNpbXBsZShub2RlLCB2aXNpdG9ycywgYmFzZSwgc3RhdGUpIHtcbiAgaWYgKCFiYXNlKSBiYXNlID0gZXhwb3J0cy5iYXNlOyhmdW5jdGlvbiBjKG5vZGUsIHN0LCBvdmVycmlkZSkge1xuICAgIHZhciB0eXBlID0gb3ZlcnJpZGUgfHwgbm9kZS50eXBlLFxuICAgICAgICBmb3VuZCA9IHZpc2l0b3JzW3R5cGVdO1xuICAgIGJhc2VbdHlwZV0obm9kZSwgc3QsIGMpO1xuICAgIGlmIChmb3VuZCkgZm91bmQobm9kZSwgc3QpO1xuICB9KShub2RlLCBzdGF0ZSk7XG59XG5cbmZ1bmN0aW9uIGFuY2VzdG9yKG5vZGUsIHZpc2l0b3JzLCBiYXNlLCBzdGF0ZSkge1xuICBpZiAoIWJhc2UpIGJhc2UgPSBleHBvcnRzLmJhc2U7XG4gIGlmICghc3RhdGUpIHN0YXRlID0gW107KGZ1bmN0aW9uIGMobm9kZSwgc3QsIG92ZXJyaWRlKSB7XG4gICAgdmFyIHR5cGUgPSBvdmVycmlkZSB8fCBub2RlLnR5cGUsXG4gICAgICAgIGZvdW5kID0gdmlzaXRvcnNbdHlwZV07XG4gICAgaWYgKG5vZGUgIT0gc3Rbc3QubGVuZ3RoIC0gMV0pIHtcbiAgICAgIHN0ID0gc3Quc2xpY2UoKTtcbiAgICAgIHN0LnB1c2gobm9kZSk7XG4gICAgfVxuICAgIGJhc2VbdHlwZV0obm9kZSwgc3QsIGMpO1xuICAgIGlmIChmb3VuZCkgZm91bmQobm9kZSwgc3QpO1xuICB9KShub2RlLCBzdGF0ZSk7XG59XG5cbmZ1bmN0aW9uIHJlY3Vyc2l2ZShub2RlLCBzdGF0ZSwgZnVuY3MsIGJhc2UpIHtcbiAgdmFyIHZpc2l0b3IgPSBmdW5jcyA/IGV4cG9ydHMubWFrZShmdW5jcywgYmFzZSkgOiBiYXNlOyhmdW5jdGlvbiBjKG5vZGUsIHN0LCBvdmVycmlkZSkge1xuICAgIHZpc2l0b3Jbb3ZlcnJpZGUgfHwgbm9kZS50eXBlXShub2RlLCBzdCwgYyk7XG4gIH0pKG5vZGUsIHN0YXRlKTtcbn1cblxuZnVuY3Rpb24gbWFrZVRlc3QodGVzdCkge1xuICBpZiAodHlwZW9mIHRlc3QgPT0gXCJzdHJpbmdcIikge1xuICAgIHJldHVybiBmdW5jdGlvbiAodHlwZSkge1xuICAgICAgcmV0dXJuIHR5cGUgPT0gdGVzdDtcbiAgICB9O1xuICB9IGVsc2UgaWYgKCF0ZXN0KSB7XG4gICAgcmV0dXJuIGZ1bmN0aW9uICgpIHtcbiAgICAgIHJldHVybiB0cnVlO1xuICAgIH07XG4gIH0gZWxzZSB7XG4gICAgcmV0dXJuIHRlc3Q7XG4gIH1cbn1cblxudmFyIEZvdW5kID0gZnVuY3Rpb24gRm91bmQobm9kZSwgc3RhdGUpIHtcbiAgX2NsYXNzQ2FsbENoZWNrKHRoaXMsIEZvdW5kKTtcblxuICB0aGlzLm5vZGUgPSBub2RlO3RoaXMuc3RhdGUgPSBzdGF0ZTtcbn07XG5cbmZ1bmN0aW9uIGZpbmROb2RlQXQobm9kZSwgc3RhcnQsIGVuZCwgdGVzdCwgYmFzZSwgc3RhdGUpIHtcbiAgdGVzdCA9IG1ha2VUZXN0KHRlc3QpO1xuICBpZiAoIWJhc2UpIGJhc2UgPSBleHBvcnRzLmJhc2U7XG4gIHRyeSB7XG4gICAgOyhmdW5jdGlvbiBjKG5vZGUsIHN0LCBvdmVycmlkZSkge1xuICAgICAgdmFyIHR5cGUgPSBvdmVycmlkZSB8fCBub2RlLnR5cGU7XG4gICAgICBpZiAoKHN0YXJ0ID09IG51bGwgfHwgbm9kZS5zdGFydCA8PSBzdGFydCkgJiYgKGVuZCA9PSBudWxsIHx8IG5vZGUuZW5kID49IGVuZCkpIGJhc2VbdHlwZV0obm9kZSwgc3QsIGMpO1xuICAgICAgaWYgKHRlc3QodHlwZSwgbm9kZSkgJiYgKHN0YXJ0ID09IG51bGwgfHwgbm9kZS5zdGFydCA9PSBzdGFydCkgJiYgKGVuZCA9PSBudWxsIHx8IG5vZGUuZW5kID09IGVuZCkpIHRocm93IG5ldyBGb3VuZChub2RlLCBzdCk7XG4gICAgfSkobm9kZSwgc3RhdGUpO1xuICB9IGNhdGNoIChlKSB7XG4gICAgaWYgKGUgaW5zdGFuY2VvZiBGb3VuZCkge1xuICAgICAgcmV0dXJuIGU7XG4gICAgfXRocm93IGU7XG4gIH1cbn1cblxuZnVuY3Rpb24gZmluZE5vZGVBcm91bmQobm9kZSwgcG9zLCB0ZXN0LCBiYXNlLCBzdGF0ZSkge1xuICB0ZXN0ID0gbWFrZVRlc3QodGVzdCk7XG4gIGlmICghYmFzZSkgYmFzZSA9IGV4cG9ydHMuYmFzZTtcbiAgdHJ5IHtcbiAgICA7KGZ1bmN0aW9uIGMobm9kZSwgc3QsIG92ZXJyaWRlKSB7XG4gICAgICB2YXIgdHlwZSA9IG92ZXJyaWRlIHx8IG5vZGUudHlwZTtcbiAgICAgIGlmIChub2RlLnN0YXJ0ID4gcG9zIHx8IG5vZGUuZW5kIDwgcG9zKSB7XG4gICAgICAgIHJldHVybjtcbiAgICAgIH1iYXNlW3R5cGVdKG5vZGUsIHN0LCBjKTtcbiAgICAgIGlmICh0ZXN0KHR5cGUsIG5vZGUpKSB0aHJvdyBuZXcgRm91bmQobm9kZSwgc3QpO1xuICAgIH0pKG5vZGUsIHN0YXRlKTtcbiAgfSBjYXRjaCAoZSkge1xuICAgIGlmIChlIGluc3RhbmNlb2YgRm91bmQpIHtcbiAgICAgIHJldHVybiBlO1xuICAgIH10aHJvdyBlO1xuICB9XG59XG5cbmZ1bmN0aW9uIGZpbmROb2RlQWZ0ZXIobm9kZSwgcG9zLCB0ZXN0LCBiYXNlLCBzdGF0ZSkge1xuICB0ZXN0ID0gbWFrZVRlc3QodGVzdCk7XG4gIGlmICghYmFzZSkgYmFzZSA9IGV4cG9ydHMuYmFzZTtcbiAgdHJ5IHtcbiAgICA7KGZ1bmN0aW9uIGMobm9kZSwgc3QsIG92ZXJyaWRlKSB7XG4gICAgICBpZiAobm9kZS5lbmQgPCBwb3MpIHtcbiAgICAgICAgcmV0dXJuO1xuICAgICAgfXZhciB0eXBlID0gb3ZlcnJpZGUgfHwgbm9kZS50eXBlO1xuICAgICAgaWYgKG5vZGUuc3RhcnQgPj0gcG9zICYmIHRlc3QodHlwZSwgbm9kZSkpIHRocm93IG5ldyBGb3VuZChub2RlLCBzdCk7XG4gICAgICBiYXNlW3R5cGVdKG5vZGUsIHN0LCBjKTtcbiAgICB9KShub2RlLCBzdGF0ZSk7XG4gIH0gY2F0Y2ggKGUpIHtcbiAgICBpZiAoZSBpbnN0YW5jZW9mIEZvdW5kKSB7XG4gICAgICByZXR1cm4gZTtcbiAgICB9dGhyb3cgZTtcbiAgfVxufVxuXG5mdW5jdGlvbiBmaW5kTm9kZUJlZm9yZShub2RlLCBwb3MsIHRlc3QsIGJhc2UsIHN0YXRlKSB7XG4gIHRlc3QgPSBtYWtlVGVzdCh0ZXN0KTtcbiAgaWYgKCFiYXNlKSBiYXNlID0gZXhwb3J0cy5iYXNlO1xuICB2YXIgbWF4ID0gdW5kZWZpbmVkOyhmdW5jdGlvbiBjKG5vZGUsIHN0LCBvdmVycmlkZSkge1xuICAgIGlmIChub2RlLnN0YXJ0ID4gcG9zKSB7XG4gICAgICByZXR1cm47XG4gICAgfXZhciB0eXBlID0gb3ZlcnJpZGUgfHwgbm9kZS50eXBlO1xuICAgIGlmIChub2RlLmVuZCA8PSBwb3MgJiYgKCFtYXggfHwgbWF4Lm5vZGUuZW5kIDwgbm9kZS5lbmQpICYmIHRlc3QodHlwZSwgbm9kZSkpIG1heCA9IG5ldyBGb3VuZChub2RlLCBzdCk7XG4gICAgYmFzZVt0eXBlXShub2RlLCBzdCwgYyk7XG4gIH0pKG5vZGUsIHN0YXRlKTtcbiAgcmV0dXJuIG1heDtcbn1cblxuZnVuY3Rpb24gbWFrZShmdW5jcywgYmFzZSkge1xuICBpZiAoIWJhc2UpIGJhc2UgPSBleHBvcnRzLmJhc2U7XG4gIHZhciB2aXNpdG9yID0ge307XG4gIGZvciAodmFyIHR5cGUgaW4gYmFzZSkgdmlzaXRvclt0eXBlXSA9IGJhc2VbdHlwZV07XG4gIGZvciAodmFyIHR5cGUgaW4gZnVuY3MpIHZpc2l0b3JbdHlwZV0gPSBmdW5jc1t0eXBlXTtcbiAgcmV0dXJuIHZpc2l0b3I7XG59XG5cbmZ1bmN0aW9uIHNraXBUaHJvdWdoKG5vZGUsIHN0LCBjKSB7XG4gIGMobm9kZSwgc3QpO1xufVxuZnVuY3Rpb24gaWdub3JlKF9ub2RlLCBfc3QsIF9jKSB7fVxuXG4vLyBOb2RlIHdhbGtlcnMuXG5cbnZhciBiYXNlID0ge307XG5cbmV4cG9ydHMuYmFzZSA9IGJhc2U7XG5iYXNlLlByb2dyYW0gPSBiYXNlLkJsb2NrU3RhdGVtZW50ID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIGZvciAodmFyIGkgPSAwOyBpIDwgbm9kZS5ib2R5Lmxlbmd0aDsgKytpKSB7XG4gICAgYyhub2RlLmJvZHlbaV0sIHN0LCBcIlN0YXRlbWVudFwiKTtcbiAgfVxufTtcbmJhc2UuU3RhdGVtZW50ID0gc2tpcFRocm91Z2g7XG5iYXNlLkVtcHR5U3RhdGVtZW50ID0gaWdub3JlO1xuYmFzZS5FeHByZXNzaW9uU3RhdGVtZW50ID0gYmFzZS5QYXJlbnRoZXNpemVkRXhwcmVzc2lvbiA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICByZXR1cm4gYyhub2RlLmV4cHJlc3Npb24sIHN0LCBcIkV4cHJlc3Npb25cIik7XG59O1xuYmFzZS5JZlN0YXRlbWVudCA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBjKG5vZGUudGVzdCwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbiAgYyhub2RlLmNvbnNlcXVlbnQsIHN0LCBcIlN0YXRlbWVudFwiKTtcbiAgaWYgKG5vZGUuYWx0ZXJuYXRlKSBjKG5vZGUuYWx0ZXJuYXRlLCBzdCwgXCJTdGF0ZW1lbnRcIik7XG59O1xuYmFzZS5MYWJlbGVkU3RhdGVtZW50ID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIHJldHVybiBjKG5vZGUuYm9keSwgc3QsIFwiU3RhdGVtZW50XCIpO1xufTtcbmJhc2UuQnJlYWtTdGF0ZW1lbnQgPSBiYXNlLkNvbnRpbnVlU3RhdGVtZW50ID0gaWdub3JlO1xuYmFzZS5XaXRoU3RhdGVtZW50ID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIGMobm9kZS5vYmplY3QsIHN0LCBcIkV4cHJlc3Npb25cIik7XG4gIGMobm9kZS5ib2R5LCBzdCwgXCJTdGF0ZW1lbnRcIik7XG59O1xuYmFzZS5Td2l0Y2hTdGF0ZW1lbnQgPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgYyhub2RlLmRpc2NyaW1pbmFudCwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbiAgZm9yICh2YXIgaSA9IDA7IGkgPCBub2RlLmNhc2VzLmxlbmd0aDsgKytpKSB7XG4gICAgdmFyIGNzID0gbm9kZS5jYXNlc1tpXTtcbiAgICBpZiAoY3MudGVzdCkgYyhjcy50ZXN0LCBzdCwgXCJFeHByZXNzaW9uXCIpO1xuICAgIGZvciAodmFyIGogPSAwOyBqIDwgY3MuY29uc2VxdWVudC5sZW5ndGg7ICsraikge1xuICAgICAgYyhjcy5jb25zZXF1ZW50W2pdLCBzdCwgXCJTdGF0ZW1lbnRcIik7XG4gICAgfVxuICB9XG59O1xuYmFzZS5SZXR1cm5TdGF0ZW1lbnQgPSBiYXNlLllpZWxkRXhwcmVzc2lvbiA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBpZiAobm9kZS5hcmd1bWVudCkgYyhub2RlLmFyZ3VtZW50LCBzdCwgXCJFeHByZXNzaW9uXCIpO1xufTtcbmJhc2UuVGhyb3dTdGF0ZW1lbnQgPSBiYXNlLlNwcmVhZEVsZW1lbnQgPSBiYXNlLlJlc3RFbGVtZW50ID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIHJldHVybiBjKG5vZGUuYXJndW1lbnQsIHN0LCBcIkV4cHJlc3Npb25cIik7XG59O1xuYmFzZS5UcnlTdGF0ZW1lbnQgPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgYyhub2RlLmJsb2NrLCBzdCwgXCJTdGF0ZW1lbnRcIik7XG4gIGlmIChub2RlLmhhbmRsZXIpIGMobm9kZS5oYW5kbGVyLmJvZHksIHN0LCBcIlNjb3BlQm9keVwiKTtcbiAgaWYgKG5vZGUuZmluYWxpemVyKSBjKG5vZGUuZmluYWxpemVyLCBzdCwgXCJTdGF0ZW1lbnRcIik7XG59O1xuYmFzZS5XaGlsZVN0YXRlbWVudCA9IGJhc2UuRG9XaGlsZVN0YXRlbWVudCA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBjKG5vZGUudGVzdCwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbiAgYyhub2RlLmJvZHksIHN0LCBcIlN0YXRlbWVudFwiKTtcbn07XG5iYXNlLkZvclN0YXRlbWVudCA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBpZiAobm9kZS5pbml0KSBjKG5vZGUuaW5pdCwgc3QsIFwiRm9ySW5pdFwiKTtcbiAgaWYgKG5vZGUudGVzdCkgYyhub2RlLnRlc3QsIHN0LCBcIkV4cHJlc3Npb25cIik7XG4gIGlmIChub2RlLnVwZGF0ZSkgYyhub2RlLnVwZGF0ZSwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbiAgYyhub2RlLmJvZHksIHN0LCBcIlN0YXRlbWVudFwiKTtcbn07XG5iYXNlLkZvckluU3RhdGVtZW50ID0gYmFzZS5Gb3JPZlN0YXRlbWVudCA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBjKG5vZGUubGVmdCwgc3QsIFwiRm9ySW5pdFwiKTtcbiAgYyhub2RlLnJpZ2h0LCBzdCwgXCJFeHByZXNzaW9uXCIpO1xuICBjKG5vZGUuYm9keSwgc3QsIFwiU3RhdGVtZW50XCIpO1xufTtcbmJhc2UuRm9ySW5pdCA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBpZiAobm9kZS50eXBlID09IFwiVmFyaWFibGVEZWNsYXJhdGlvblwiKSBjKG5vZGUsIHN0KTtlbHNlIGMobm9kZSwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbn07XG5iYXNlLkRlYnVnZ2VyU3RhdGVtZW50ID0gaWdub3JlO1xuXG5iYXNlLkZ1bmN0aW9uRGVjbGFyYXRpb24gPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgcmV0dXJuIGMobm9kZSwgc3QsIFwiRnVuY3Rpb25cIik7XG59O1xuYmFzZS5WYXJpYWJsZURlY2xhcmF0aW9uID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIGZvciAodmFyIGkgPSAwOyBpIDwgbm9kZS5kZWNsYXJhdGlvbnMubGVuZ3RoOyArK2kpIHtcbiAgICB2YXIgZGVjbCA9IG5vZGUuZGVjbGFyYXRpb25zW2ldO1xuICAgIGlmIChkZWNsLmluaXQpIGMoZGVjbC5pbml0LCBzdCwgXCJFeHByZXNzaW9uXCIpO1xuICB9XG59O1xuXG5iYXNlLkZ1bmN0aW9uID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIHJldHVybiBjKG5vZGUuYm9keSwgc3QsIFwiU2NvcGVCb2R5XCIpO1xufTtcbmJhc2UuU2NvcGVCb2R5ID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIHJldHVybiBjKG5vZGUsIHN0LCBcIlN0YXRlbWVudFwiKTtcbn07XG5cbmJhc2UuRXhwcmVzc2lvbiA9IHNraXBUaHJvdWdoO1xuYmFzZS5UaGlzRXhwcmVzc2lvbiA9IGJhc2UuU3VwZXIgPSBiYXNlLk1ldGFQcm9wZXJ0eSA9IGlnbm9yZTtcbmJhc2UuQXJyYXlFeHByZXNzaW9uID0gYmFzZS5BcnJheVBhdHRlcm4gPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgZm9yICh2YXIgaSA9IDA7IGkgPCBub2RlLmVsZW1lbnRzLmxlbmd0aDsgKytpKSB7XG4gICAgdmFyIGVsdCA9IG5vZGUuZWxlbWVudHNbaV07XG4gICAgaWYgKGVsdCkgYyhlbHQsIHN0LCBcIkV4cHJlc3Npb25cIik7XG4gIH1cbn07XG5iYXNlLk9iamVjdEV4cHJlc3Npb24gPSBiYXNlLk9iamVjdFBhdHRlcm4gPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgZm9yICh2YXIgaSA9IDA7IGkgPCBub2RlLnByb3BlcnRpZXMubGVuZ3RoOyArK2kpIHtcbiAgICBjKG5vZGUucHJvcGVydGllc1tpXSwgc3QpO1xuICB9XG59O1xuYmFzZS5GdW5jdGlvbkV4cHJlc3Npb24gPSBiYXNlLkFycm93RnVuY3Rpb25FeHByZXNzaW9uID0gYmFzZS5GdW5jdGlvbkRlY2xhcmF0aW9uO1xuYmFzZS5TZXF1ZW5jZUV4cHJlc3Npb24gPSBiYXNlLlRlbXBsYXRlTGl0ZXJhbCA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBmb3IgKHZhciBpID0gMDsgaSA8IG5vZGUuZXhwcmVzc2lvbnMubGVuZ3RoOyArK2kpIHtcbiAgICBjKG5vZGUuZXhwcmVzc2lvbnNbaV0sIHN0LCBcIkV4cHJlc3Npb25cIik7XG4gIH1cbn07XG5iYXNlLlVuYXJ5RXhwcmVzc2lvbiA9IGJhc2UuVXBkYXRlRXhwcmVzc2lvbiA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBjKG5vZGUuYXJndW1lbnQsIHN0LCBcIkV4cHJlc3Npb25cIik7XG59O1xuYmFzZS5CaW5hcnlFeHByZXNzaW9uID0gYmFzZS5Bc3NpZ25tZW50RXhwcmVzc2lvbiA9IGJhc2UuQXNzaWdubWVudFBhdHRlcm4gPSBiYXNlLkxvZ2ljYWxFeHByZXNzaW9uID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIGMobm9kZS5sZWZ0LCBzdCwgXCJFeHByZXNzaW9uXCIpO1xuICBjKG5vZGUucmlnaHQsIHN0LCBcIkV4cHJlc3Npb25cIik7XG59O1xuYmFzZS5Db25kaXRpb25hbEV4cHJlc3Npb24gPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgYyhub2RlLnRlc3QsIHN0LCBcIkV4cHJlc3Npb25cIik7XG4gIGMobm9kZS5jb25zZXF1ZW50LCBzdCwgXCJFeHByZXNzaW9uXCIpO1xuICBjKG5vZGUuYWx0ZXJuYXRlLCBzdCwgXCJFeHByZXNzaW9uXCIpO1xufTtcbmJhc2UuTmV3RXhwcmVzc2lvbiA9IGJhc2UuQ2FsbEV4cHJlc3Npb24gPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgYyhub2RlLmNhbGxlZSwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbiAgaWYgKG5vZGUuYXJndW1lbnRzKSBmb3IgKHZhciBpID0gMDsgaSA8IG5vZGUuYXJndW1lbnRzLmxlbmd0aDsgKytpKSB7XG4gICAgYyhub2RlLmFyZ3VtZW50c1tpXSwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbiAgfVxufTtcbmJhc2UuTWVtYmVyRXhwcmVzc2lvbiA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBjKG5vZGUub2JqZWN0LCBzdCwgXCJFeHByZXNzaW9uXCIpO1xuICBpZiAobm9kZS5jb21wdXRlZCkgYyhub2RlLnByb3BlcnR5LCBzdCwgXCJFeHByZXNzaW9uXCIpO1xufTtcbmJhc2UuRXhwb3J0TmFtZWREZWNsYXJhdGlvbiA9IGJhc2UuRXhwb3J0RGVmYXVsdERlY2xhcmF0aW9uID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIHJldHVybiBjKG5vZGUuZGVjbGFyYXRpb24sIHN0KTtcbn07XG5iYXNlLkltcG9ydERlY2xhcmF0aW9uID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIGZvciAodmFyIGkgPSAwOyBpIDwgbm9kZS5zcGVjaWZpZXJzLmxlbmd0aDsgaSsrKSB7XG4gICAgYyhub2RlLnNwZWNpZmllcnNbaV0sIHN0KTtcbiAgfVxufTtcbmJhc2UuSW1wb3J0U3BlY2lmaWVyID0gYmFzZS5JbXBvcnREZWZhdWx0U3BlY2lmaWVyID0gYmFzZS5JbXBvcnROYW1lc3BhY2VTcGVjaWZpZXIgPSBiYXNlLklkZW50aWZpZXIgPSBiYXNlLkxpdGVyYWwgPSBpZ25vcmU7XG5cbmJhc2UuVGFnZ2VkVGVtcGxhdGVFeHByZXNzaW9uID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIGMobm9kZS50YWcsIHN0LCBcIkV4cHJlc3Npb25cIik7XG4gIGMobm9kZS5xdWFzaSwgc3QpO1xufTtcbmJhc2UuQ2xhc3NEZWNsYXJhdGlvbiA9IGJhc2UuQ2xhc3NFeHByZXNzaW9uID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIGlmIChub2RlLnN1cGVyQ2xhc3MpIGMobm9kZS5zdXBlckNsYXNzLCBzdCwgXCJFeHByZXNzaW9uXCIpO1xuICBmb3IgKHZhciBpID0gMDsgaSA8IG5vZGUuYm9keS5ib2R5Lmxlbmd0aDsgaSsrKSB7XG4gICAgYyhub2RlLmJvZHkuYm9keVtpXSwgc3QpO1xuICB9XG59O1xuYmFzZS5NZXRob2REZWZpbml0aW9uID0gYmFzZS5Qcm9wZXJ0eSA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBpZiAobm9kZS5jb21wdXRlZCkgYyhub2RlLmtleSwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbiAgYyhub2RlLnZhbHVlLCBzdCwgXCJFeHByZXNzaW9uXCIpO1xufTtcbmJhc2UuQ29tcHJlaGVuc2lvbkV4cHJlc3Npb24gPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgZm9yICh2YXIgaSA9IDA7IGkgPCBub2RlLmJsb2Nrcy5sZW5ndGg7IGkrKykge1xuICAgIGMobm9kZS5ibG9ja3NbaV0ucmlnaHQsIHN0LCBcIkV4cHJlc3Npb25cIik7XG4gIH1jKG5vZGUuYm9keSwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbn07XG5cbn0se31dfSx7fSxbMV0pKDEpXG59KTsiLCJpZiAodHlwZW9mIE9iamVjdC5jcmVhdGUgPT09ICdmdW5jdGlvbicpIHtcbiAgLy8gaW1wbGVtZW50YXRpb24gZnJvbSBzdGFuZGFyZCBub2RlLmpzICd1dGlsJyBtb2R1bGVcbiAgbW9kdWxlLmV4cG9ydHMgPSBmdW5jdGlvbiBpbmhlcml0cyhjdG9yLCBzdXBlckN0b3IpIHtcbiAgICBjdG9yLnN1cGVyXyA9IHN1cGVyQ3RvclxuICAgIGN0b3IucHJvdG90eXBlID0gT2JqZWN0LmNyZWF0ZShzdXBlckN0b3IucHJvdG90eXBlLCB7XG4gICAgICBjb25zdHJ1Y3Rvcjoge1xuICAgICAgICB2YWx1ZTogY3RvcixcbiAgICAgICAgZW51bWVyYWJsZTogZmFsc2UsXG4gICAgICAgIHdyaXRhYmxlOiB0cnVlLFxuICAgICAgICBjb25maWd1cmFibGU6IHRydWVcbiAgICAgIH1cbiAgICB9KTtcbiAgfTtcbn0gZWxzZSB7XG4gIC8vIG9sZCBzY2hvb2wgc2hpbSBmb3Igb2xkIGJyb3dzZXJzXG4gIG1vZHVsZS5leHBvcnRzID0gZnVuY3Rpb24gaW5oZXJpdHMoY3Rvciwgc3VwZXJDdG9yKSB7XG4gICAgY3Rvci5zdXBlcl8gPSBzdXBlckN0b3JcbiAgICB2YXIgVGVtcEN0b3IgPSBmdW5jdGlvbiAoKSB7fVxuICAgIFRlbXBDdG9yLnByb3RvdHlwZSA9IHN1cGVyQ3Rvci5wcm90b3R5cGVcbiAgICBjdG9yLnByb3RvdHlwZSA9IG5ldyBUZW1wQ3RvcigpXG4gICAgY3Rvci5wcm90b3R5cGUuY29uc3RydWN0b3IgPSBjdG9yXG4gIH1cbn1cbiIsIi8vIHNoaW0gZm9yIHVzaW5nIHByb2Nlc3MgaW4gYnJvd3NlclxuXG52YXIgcHJvY2VzcyA9IG1vZHVsZS5leHBvcnRzID0ge307XG52YXIgcXVldWUgPSBbXTtcbnZhciBkcmFpbmluZyA9IGZhbHNlO1xudmFyIGN1cnJlbnRRdWV1ZTtcbnZhciBxdWV1ZUluZGV4ID0gLTE7XG5cbmZ1bmN0aW9uIGNsZWFuVXBOZXh0VGljaygpIHtcbiAgICBkcmFpbmluZyA9IGZhbHNlO1xuICAgIGlmIChjdXJyZW50UXVldWUubGVuZ3RoKSB7XG4gICAgICAgIHF1ZXVlID0gY3VycmVudFF1ZXVlLmNvbmNhdChxdWV1ZSk7XG4gICAgfSBlbHNlIHtcbiAgICAgICAgcXVldWVJbmRleCA9IC0xO1xuICAgIH1cbiAgICBpZiAocXVldWUubGVuZ3RoKSB7XG4gICAgICAgIGRyYWluUXVldWUoKTtcbiAgICB9XG59XG5cbmZ1bmN0aW9uIGRyYWluUXVldWUoKSB7XG4gICAgaWYgKGRyYWluaW5nKSB7XG4gICAgICAgIHJldHVybjtcbiAgICB9XG4gICAgdmFyIHRpbWVvdXQgPSBzZXRUaW1lb3V0KGNsZWFuVXBOZXh0VGljayk7XG4gICAgZHJhaW5pbmcgPSB0cnVlO1xuXG4gICAgdmFyIGxlbiA9IHF1ZXVlLmxlbmd0aDtcbiAgICB3aGlsZShsZW4pIHtcbiAgICAgICAgY3VycmVudFF1ZXVlID0gcXVldWU7XG4gICAgICAgIHF1ZXVlID0gW107XG4gICAgICAgIHdoaWxlICgrK3F1ZXVlSW5kZXggPCBsZW4pIHtcbiAgICAgICAgICAgIGN1cnJlbnRRdWV1ZVtxdWV1ZUluZGV4XS5ydW4oKTtcbiAgICAgICAgfVxuICAgICAgICBxdWV1ZUluZGV4ID0gLTE7XG4gICAgICAgIGxlbiA9IHF1ZXVlLmxlbmd0aDtcbiAgICB9XG4gICAgY3VycmVudFF1ZXVlID0gbnVsbDtcbiAgICBkcmFpbmluZyA9IGZhbHNlO1xuICAgIGNsZWFyVGltZW91dCh0aW1lb3V0KTtcbn1cblxucHJvY2Vzcy5uZXh0VGljayA9IGZ1bmN0aW9uIChmdW4pIHtcbiAgICB2YXIgYXJncyA9IG5ldyBBcnJheShhcmd1bWVudHMubGVuZ3RoIC0gMSk7XG4gICAgaWYgKGFyZ3VtZW50cy5sZW5ndGggPiAxKSB7XG4gICAgICAgIGZvciAodmFyIGkgPSAxOyBpIDwgYXJndW1lbnRzLmxlbmd0aDsgaSsrKSB7XG4gICAgICAgICAgICBhcmdzW2kgLSAxXSA9IGFyZ3VtZW50c1tpXTtcbiAgICAgICAgfVxuICAgIH1cbiAgICBxdWV1ZS5wdXNoKG5ldyBJdGVtKGZ1biwgYXJncykpO1xuICAgIGlmIChxdWV1ZS5sZW5ndGggPT09IDEgJiYgIWRyYWluaW5nKSB7XG4gICAgICAgIHNldFRpbWVvdXQoZHJhaW5RdWV1ZSwgMCk7XG4gICAgfVxufTtcblxuLy8gdjggbGlrZXMgcHJlZGljdGlibGUgb2JqZWN0c1xuZnVuY3Rpb24gSXRlbShmdW4sIGFycmF5KSB7XG4gICAgdGhpcy5mdW4gPSBmdW47XG4gICAgdGhpcy5hcnJheSA9IGFycmF5O1xufVxuSXRlbS5wcm90b3R5cGUucnVuID0gZnVuY3Rpb24gKCkge1xuICAgIHRoaXMuZnVuLmFwcGx5KG51bGwsIHRoaXMuYXJyYXkpO1xufTtcbnByb2Nlc3MudGl0bGUgPSAnYnJvd3Nlcic7XG5wcm9jZXNzLmJyb3dzZXIgPSB0cnVlO1xucHJvY2Vzcy5lbnYgPSB7fTtcbnByb2Nlc3MuYXJndiA9IFtdO1xucHJvY2Vzcy52ZXJzaW9uID0gJyc7IC8vIGVtcHR5IHN0cmluZyB0byBhdm9pZCByZWdleHAgaXNzdWVzXG5wcm9jZXNzLnZlcnNpb25zID0ge307XG5cbmZ1bmN0aW9uIG5vb3AoKSB7fVxuXG5wcm9jZXNzLm9uID0gbm9vcDtcbnByb2Nlc3MuYWRkTGlzdGVuZXIgPSBub29wO1xucHJvY2Vzcy5vbmNlID0gbm9vcDtcbnByb2Nlc3Mub2ZmID0gbm9vcDtcbnByb2Nlc3MucmVtb3ZlTGlzdGVuZXIgPSBub29wO1xucHJvY2Vzcy5yZW1vdmVBbGxMaXN0ZW5lcnMgPSBub29wO1xucHJvY2Vzcy5lbWl0ID0gbm9vcDtcblxucHJvY2Vzcy5iaW5kaW5nID0gZnVuY3Rpb24gKG5hbWUpIHtcbiAgICB0aHJvdyBuZXcgRXJyb3IoJ3Byb2Nlc3MuYmluZGluZyBpcyBub3Qgc3VwcG9ydGVkJyk7XG59O1xuXG4vLyBUT0RPKHNodHlsbWFuKVxucHJvY2Vzcy5jd2QgPSBmdW5jdGlvbiAoKSB7IHJldHVybiAnLycgfTtcbnByb2Nlc3MuY2hkaXIgPSBmdW5jdGlvbiAoZGlyKSB7XG4gICAgdGhyb3cgbmV3IEVycm9yKCdwcm9jZXNzLmNoZGlyIGlzIG5vdCBzdXBwb3J0ZWQnKTtcbn07XG5wcm9jZXNzLnVtYXNrID0gZnVuY3Rpb24oKSB7IHJldHVybiAwOyB9O1xuIiwibW9kdWxlLmV4cG9ydHMgPSBmdW5jdGlvbiBpc0J1ZmZlcihhcmcpIHtcbiAgcmV0dXJuIGFyZyAmJiB0eXBlb2YgYXJnID09PSAnb2JqZWN0J1xuICAgICYmIHR5cGVvZiBhcmcuY29weSA9PT0gJ2Z1bmN0aW9uJ1xuICAgICYmIHR5cGVvZiBhcmcuZmlsbCA9PT0gJ2Z1bmN0aW9uJ1xuICAgICYmIHR5cGVvZiBhcmcucmVhZFVJbnQ4ID09PSAnZnVuY3Rpb24nO1xufSIsIi8vIENvcHlyaWdodCBKb3llbnQsIEluYy4gYW5kIG90aGVyIE5vZGUgY29udHJpYnV0b3JzLlxuLy9cbi8vIFBlcm1pc3Npb24gaXMgaGVyZWJ5IGdyYW50ZWQsIGZyZWUgb2YgY2hhcmdlLCB0byBhbnkgcGVyc29uIG9idGFpbmluZyBhXG4vLyBjb3B5IG9mIHRoaXMgc29mdHdhcmUgYW5kIGFzc29jaWF0ZWQgZG9jdW1lbnRhdGlvbiBmaWxlcyAodGhlXG4vLyBcIlNvZnR3YXJlXCIpLCB0byBkZWFsIGluIHRoZSBTb2Z0d2FyZSB3aXRob3V0IHJlc3RyaWN0aW9uLCBpbmNsdWRpbmdcbi8vIHdpdGhvdXQgbGltaXRhdGlvbiB0aGUgcmlnaHRzIHRvIHVzZSwgY29weSwgbW9kaWZ5LCBtZXJnZSwgcHVibGlzaCxcbi8vIGRpc3RyaWJ1dGUsIHN1YmxpY2Vuc2UsIGFuZC9vciBzZWxsIGNvcGllcyBvZiB0aGUgU29mdHdhcmUsIGFuZCB0byBwZXJtaXRcbi8vIHBlcnNvbnMgdG8gd2hvbSB0aGUgU29mdHdhcmUgaXMgZnVybmlzaGVkIHRvIGRvIHNvLCBzdWJqZWN0IHRvIHRoZVxuLy8gZm9sbG93aW5nIGNvbmRpdGlvbnM6XG4vL1xuLy8gVGhlIGFib3ZlIGNvcHlyaWdodCBub3RpY2UgYW5kIHRoaXMgcGVybWlzc2lvbiBub3RpY2Ugc2hhbGwgYmUgaW5jbHVkZWRcbi8vIGluIGFsbCBjb3BpZXMgb3Igc3Vic3RhbnRpYWwgcG9ydGlvbnMgb2YgdGhlIFNvZnR3YXJlLlxuLy9cbi8vIFRIRSBTT0ZUV0FSRSBJUyBQUk9WSURFRCBcIkFTIElTXCIsIFdJVEhPVVQgV0FSUkFOVFkgT0YgQU5ZIEtJTkQsIEVYUFJFU1Ncbi8vIE9SIElNUExJRUQsIElOQ0xVRElORyBCVVQgTk9UIExJTUlURUQgVE8gVEhFIFdBUlJBTlRJRVMgT0Zcbi8vIE1FUkNIQU5UQUJJTElUWSwgRklUTkVTUyBGT1IgQSBQQVJUSUNVTEFSIFBVUlBPU0UgQU5EIE5PTklORlJJTkdFTUVOVC4gSU5cbi8vIE5PIEVWRU5UIFNIQUxMIFRIRSBBVVRIT1JTIE9SIENPUFlSSUdIVCBIT0xERVJTIEJFIExJQUJMRSBGT1IgQU5ZIENMQUlNLFxuLy8gREFNQUdFUyBPUiBPVEhFUiBMSUFCSUxJVFksIFdIRVRIRVIgSU4gQU4gQUNUSU9OIE9GIENPTlRSQUNULCBUT1JUIE9SXG4vLyBPVEhFUldJU0UsIEFSSVNJTkcgRlJPTSwgT1VUIE9GIE9SIElOIENPTk5FQ1RJT04gV0lUSCBUSEUgU09GVFdBUkUgT1IgVEhFXG4vLyBVU0UgT1IgT1RIRVIgREVBTElOR1MgSU4gVEhFIFNPRlRXQVJFLlxuXG52YXIgZm9ybWF0UmVnRXhwID0gLyVbc2RqJV0vZztcbmV4cG9ydHMuZm9ybWF0ID0gZnVuY3Rpb24oZikge1xuICBpZiAoIWlzU3RyaW5nKGYpKSB7XG4gICAgdmFyIG9iamVjdHMgPSBbXTtcbiAgICBmb3IgKHZhciBpID0gMDsgaSA8IGFyZ3VtZW50cy5sZW5ndGg7IGkrKykge1xuICAgICAgb2JqZWN0cy5wdXNoKGluc3BlY3QoYXJndW1lbnRzW2ldKSk7XG4gICAgfVxuICAgIHJldHVybiBvYmplY3RzLmpvaW4oJyAnKTtcbiAgfVxuXG4gIHZhciBpID0gMTtcbiAgdmFyIGFyZ3MgPSBhcmd1bWVudHM7XG4gIHZhciBsZW4gPSBhcmdzLmxlbmd0aDtcbiAgdmFyIHN0ciA9IFN0cmluZyhmKS5yZXBsYWNlKGZvcm1hdFJlZ0V4cCwgZnVuY3Rpb24oeCkge1xuICAgIGlmICh4ID09PSAnJSUnKSByZXR1cm4gJyUnO1xuICAgIGlmIChpID49IGxlbikgcmV0dXJuIHg7XG4gICAgc3dpdGNoICh4KSB7XG4gICAgICBjYXNlICclcyc6IHJldHVybiBTdHJpbmcoYXJnc1tpKytdKTtcbiAgICAgIGNhc2UgJyVkJzogcmV0dXJuIE51bWJlcihhcmdzW2krK10pO1xuICAgICAgY2FzZSAnJWonOlxuICAgICAgICB0cnkge1xuICAgICAgICAgIHJldHVybiBKU09OLnN0cmluZ2lmeShhcmdzW2krK10pO1xuICAgICAgICB9IGNhdGNoIChfKSB7XG4gICAgICAgICAgcmV0dXJuICdbQ2lyY3VsYXJdJztcbiAgICAgICAgfVxuICAgICAgZGVmYXVsdDpcbiAgICAgICAgcmV0dXJuIHg7XG4gICAgfVxuICB9KTtcbiAgZm9yICh2YXIgeCA9IGFyZ3NbaV07IGkgPCBsZW47IHggPSBhcmdzWysraV0pIHtcbiAgICBpZiAoaXNOdWxsKHgpIHx8ICFpc09iamVjdCh4KSkge1xuICAgICAgc3RyICs9ICcgJyArIHg7XG4gICAgfSBlbHNlIHtcbiAgICAgIHN0ciArPSAnICcgKyBpbnNwZWN0KHgpO1xuICAgIH1cbiAgfVxuICByZXR1cm4gc3RyO1xufTtcblxuXG4vLyBNYXJrIHRoYXQgYSBtZXRob2Qgc2hvdWxkIG5vdCBiZSB1c2VkLlxuLy8gUmV0dXJucyBhIG1vZGlmaWVkIGZ1bmN0aW9uIHdoaWNoIHdhcm5zIG9uY2UgYnkgZGVmYXVsdC5cbi8vIElmIC0tbm8tZGVwcmVjYXRpb24gaXMgc2V0LCB0aGVuIGl0IGlzIGEgbm8tb3AuXG5leHBvcnRzLmRlcHJlY2F0ZSA9IGZ1bmN0aW9uKGZuLCBtc2cpIHtcbiAgLy8gQWxsb3cgZm9yIGRlcHJlY2F0aW5nIHRoaW5ncyBpbiB0aGUgcHJvY2VzcyBvZiBzdGFydGluZyB1cC5cbiAgaWYgKGlzVW5kZWZpbmVkKGdsb2JhbC5wcm9jZXNzKSkge1xuICAgIHJldHVybiBmdW5jdGlvbigpIHtcbiAgICAgIHJldHVybiBleHBvcnRzLmRlcHJlY2F0ZShmbiwgbXNnKS5hcHBseSh0aGlzLCBhcmd1bWVudHMpO1xuICAgIH07XG4gIH1cblxuICBpZiAocHJvY2Vzcy5ub0RlcHJlY2F0aW9uID09PSB0cnVlKSB7XG4gICAgcmV0dXJuIGZuO1xuICB9XG5cbiAgdmFyIHdhcm5lZCA9IGZhbHNlO1xuICBmdW5jdGlvbiBkZXByZWNhdGVkKCkge1xuICAgIGlmICghd2FybmVkKSB7XG4gICAgICBpZiAocHJvY2Vzcy50aHJvd0RlcHJlY2F0aW9uKSB7XG4gICAgICAgIHRocm93IG5ldyBFcnJvcihtc2cpO1xuICAgICAgfSBlbHNlIGlmIChwcm9jZXNzLnRyYWNlRGVwcmVjYXRpb24pIHtcbiAgICAgICAgY29uc29sZS50cmFjZShtc2cpO1xuICAgICAgfSBlbHNlIHtcbiAgICAgICAgY29uc29sZS5lcnJvcihtc2cpO1xuICAgICAgfVxuICAgICAgd2FybmVkID0gdHJ1ZTtcbiAgICB9XG4gICAgcmV0dXJuIGZuLmFwcGx5KHRoaXMsIGFyZ3VtZW50cyk7XG4gIH1cblxuICByZXR1cm4gZGVwcmVjYXRlZDtcbn07XG5cblxudmFyIGRlYnVncyA9IHt9O1xudmFyIGRlYnVnRW52aXJvbjtcbmV4cG9ydHMuZGVidWdsb2cgPSBmdW5jdGlvbihzZXQpIHtcbiAgaWYgKGlzVW5kZWZpbmVkKGRlYnVnRW52aXJvbikpXG4gICAgZGVidWdFbnZpcm9uID0gcHJvY2Vzcy5lbnYuTk9ERV9ERUJVRyB8fCAnJztcbiAgc2V0ID0gc2V0LnRvVXBwZXJDYXNlKCk7XG4gIGlmICghZGVidWdzW3NldF0pIHtcbiAgICBpZiAobmV3IFJlZ0V4cCgnXFxcXGInICsgc2V0ICsgJ1xcXFxiJywgJ2knKS50ZXN0KGRlYnVnRW52aXJvbikpIHtcbiAgICAgIHZhciBwaWQgPSBwcm9jZXNzLnBpZDtcbiAgICAgIGRlYnVnc1tzZXRdID0gZnVuY3Rpb24oKSB7XG4gICAgICAgIHZhciBtc2cgPSBleHBvcnRzLmZvcm1hdC5hcHBseShleHBvcnRzLCBhcmd1bWVudHMpO1xuICAgICAgICBjb25zb2xlLmVycm9yKCclcyAlZDogJXMnLCBzZXQsIHBpZCwgbXNnKTtcbiAgICAgIH07XG4gICAgfSBlbHNlIHtcbiAgICAgIGRlYnVnc1tzZXRdID0gZnVuY3Rpb24oKSB7fTtcbiAgICB9XG4gIH1cbiAgcmV0dXJuIGRlYnVnc1tzZXRdO1xufTtcblxuXG4vKipcbiAqIEVjaG9zIHRoZSB2YWx1ZSBvZiBhIHZhbHVlLiBUcnlzIHRvIHByaW50IHRoZSB2YWx1ZSBvdXRcbiAqIGluIHRoZSBiZXN0IHdheSBwb3NzaWJsZSBnaXZlbiB0aGUgZGlmZmVyZW50IHR5cGVzLlxuICpcbiAqIEBwYXJhbSB7T2JqZWN0fSBvYmogVGhlIG9iamVjdCB0byBwcmludCBvdXQuXG4gKiBAcGFyYW0ge09iamVjdH0gb3B0cyBPcHRpb25hbCBvcHRpb25zIG9iamVjdCB0aGF0IGFsdGVycyB0aGUgb3V0cHV0LlxuICovXG4vKiBsZWdhY3k6IG9iaiwgc2hvd0hpZGRlbiwgZGVwdGgsIGNvbG9ycyovXG5mdW5jdGlvbiBpbnNwZWN0KG9iaiwgb3B0cykge1xuICAvLyBkZWZhdWx0IG9wdGlvbnNcbiAgdmFyIGN0eCA9IHtcbiAgICBzZWVuOiBbXSxcbiAgICBzdHlsaXplOiBzdHlsaXplTm9Db2xvclxuICB9O1xuICAvLyBsZWdhY3kuLi5cbiAgaWYgKGFyZ3VtZW50cy5sZW5ndGggPj0gMykgY3R4LmRlcHRoID0gYXJndW1lbnRzWzJdO1xuICBpZiAoYXJndW1lbnRzLmxlbmd0aCA+PSA0KSBjdHguY29sb3JzID0gYXJndW1lbnRzWzNdO1xuICBpZiAoaXNCb29sZWFuKG9wdHMpKSB7XG4gICAgLy8gbGVnYWN5Li4uXG4gICAgY3R4LnNob3dIaWRkZW4gPSBvcHRzO1xuICB9IGVsc2UgaWYgKG9wdHMpIHtcbiAgICAvLyBnb3QgYW4gXCJvcHRpb25zXCIgb2JqZWN0XG4gICAgZXhwb3J0cy5fZXh0ZW5kKGN0eCwgb3B0cyk7XG4gIH1cbiAgLy8gc2V0IGRlZmF1bHQgb3B0aW9uc1xuICBpZiAoaXNVbmRlZmluZWQoY3R4LnNob3dIaWRkZW4pKSBjdHguc2hvd0hpZGRlbiA9IGZhbHNlO1xuICBpZiAoaXNVbmRlZmluZWQoY3R4LmRlcHRoKSkgY3R4LmRlcHRoID0gMjtcbiAgaWYgKGlzVW5kZWZpbmVkKGN0eC5jb2xvcnMpKSBjdHguY29sb3JzID0gZmFsc2U7XG4gIGlmIChpc1VuZGVmaW5lZChjdHguY3VzdG9tSW5zcGVjdCkpIGN0eC5jdXN0b21JbnNwZWN0ID0gdHJ1ZTtcbiAgaWYgKGN0eC5jb2xvcnMpIGN0eC5zdHlsaXplID0gc3R5bGl6ZVdpdGhDb2xvcjtcbiAgcmV0dXJuIGZvcm1hdFZhbHVlKGN0eCwgb2JqLCBjdHguZGVwdGgpO1xufVxuZXhwb3J0cy5pbnNwZWN0ID0gaW5zcGVjdDtcblxuXG4vLyBodHRwOi8vZW4ud2lraXBlZGlhLm9yZy93aWtpL0FOU0lfZXNjYXBlX2NvZGUjZ3JhcGhpY3Ncbmluc3BlY3QuY29sb3JzID0ge1xuICAnYm9sZCcgOiBbMSwgMjJdLFxuICAnaXRhbGljJyA6IFszLCAyM10sXG4gICd1bmRlcmxpbmUnIDogWzQsIDI0XSxcbiAgJ2ludmVyc2UnIDogWzcsIDI3XSxcbiAgJ3doaXRlJyA6IFszNywgMzldLFxuICAnZ3JleScgOiBbOTAsIDM5XSxcbiAgJ2JsYWNrJyA6IFszMCwgMzldLFxuICAnYmx1ZScgOiBbMzQsIDM5XSxcbiAgJ2N5YW4nIDogWzM2LCAzOV0sXG4gICdncmVlbicgOiBbMzIsIDM5XSxcbiAgJ21hZ2VudGEnIDogWzM1LCAzOV0sXG4gICdyZWQnIDogWzMxLCAzOV0sXG4gICd5ZWxsb3cnIDogWzMzLCAzOV1cbn07XG5cbi8vIERvbid0IHVzZSAnYmx1ZScgbm90IHZpc2libGUgb24gY21kLmV4ZVxuaW5zcGVjdC5zdHlsZXMgPSB7XG4gICdzcGVjaWFsJzogJ2N5YW4nLFxuICAnbnVtYmVyJzogJ3llbGxvdycsXG4gICdib29sZWFuJzogJ3llbGxvdycsXG4gICd1bmRlZmluZWQnOiAnZ3JleScsXG4gICdudWxsJzogJ2JvbGQnLFxuICAnc3RyaW5nJzogJ2dyZWVuJyxcbiAgJ2RhdGUnOiAnbWFnZW50YScsXG4gIC8vIFwibmFtZVwiOiBpbnRlbnRpb25hbGx5IG5vdCBzdHlsaW5nXG4gICdyZWdleHAnOiAncmVkJ1xufTtcblxuXG5mdW5jdGlvbiBzdHlsaXplV2l0aENvbG9yKHN0ciwgc3R5bGVUeXBlKSB7XG4gIHZhciBzdHlsZSA9IGluc3BlY3Quc3R5bGVzW3N0eWxlVHlwZV07XG5cbiAgaWYgKHN0eWxlKSB7XG4gICAgcmV0dXJuICdcXHUwMDFiWycgKyBpbnNwZWN0LmNvbG9yc1tzdHlsZV1bMF0gKyAnbScgKyBzdHIgK1xuICAgICAgICAgICAnXFx1MDAxYlsnICsgaW5zcGVjdC5jb2xvcnNbc3R5bGVdWzFdICsgJ20nO1xuICB9IGVsc2Uge1xuICAgIHJldHVybiBzdHI7XG4gIH1cbn1cblxuXG5mdW5jdGlvbiBzdHlsaXplTm9Db2xvcihzdHIsIHN0eWxlVHlwZSkge1xuICByZXR1cm4gc3RyO1xufVxuXG5cbmZ1bmN0aW9uIGFycmF5VG9IYXNoKGFycmF5KSB7XG4gIHZhciBoYXNoID0ge307XG5cbiAgYXJyYXkuZm9yRWFjaChmdW5jdGlvbih2YWwsIGlkeCkge1xuICAgIGhhc2hbdmFsXSA9IHRydWU7XG4gIH0pO1xuXG4gIHJldHVybiBoYXNoO1xufVxuXG5cbmZ1bmN0aW9uIGZvcm1hdFZhbHVlKGN0eCwgdmFsdWUsIHJlY3Vyc2VUaW1lcykge1xuICAvLyBQcm92aWRlIGEgaG9vayBmb3IgdXNlci1zcGVjaWZpZWQgaW5zcGVjdCBmdW5jdGlvbnMuXG4gIC8vIENoZWNrIHRoYXQgdmFsdWUgaXMgYW4gb2JqZWN0IHdpdGggYW4gaW5zcGVjdCBmdW5jdGlvbiBvbiBpdFxuICBpZiAoY3R4LmN1c3RvbUluc3BlY3QgJiZcbiAgICAgIHZhbHVlICYmXG4gICAgICBpc0Z1bmN0aW9uKHZhbHVlLmluc3BlY3QpICYmXG4gICAgICAvLyBGaWx0ZXIgb3V0IHRoZSB1dGlsIG1vZHVsZSwgaXQncyBpbnNwZWN0IGZ1bmN0aW9uIGlzIHNwZWNpYWxcbiAgICAgIHZhbHVlLmluc3BlY3QgIT09IGV4cG9ydHMuaW5zcGVjdCAmJlxuICAgICAgLy8gQWxzbyBmaWx0ZXIgb3V0IGFueSBwcm90b3R5cGUgb2JqZWN0cyB1c2luZyB0aGUgY2lyY3VsYXIgY2hlY2suXG4gICAgICAhKHZhbHVlLmNvbnN0cnVjdG9yICYmIHZhbHVlLmNvbnN0cnVjdG9yLnByb3RvdHlwZSA9PT0gdmFsdWUpKSB7XG4gICAgdmFyIHJldCA9IHZhbHVlLmluc3BlY3QocmVjdXJzZVRpbWVzLCBjdHgpO1xuICAgIGlmICghaXNTdHJpbmcocmV0KSkge1xuICAgICAgcmV0ID0gZm9ybWF0VmFsdWUoY3R4LCByZXQsIHJlY3Vyc2VUaW1lcyk7XG4gICAgfVxuICAgIHJldHVybiByZXQ7XG4gIH1cblxuICAvLyBQcmltaXRpdmUgdHlwZXMgY2Fubm90IGhhdmUgcHJvcGVydGllc1xuICB2YXIgcHJpbWl0aXZlID0gZm9ybWF0UHJpbWl0aXZlKGN0eCwgdmFsdWUpO1xuICBpZiAocHJpbWl0aXZlKSB7XG4gICAgcmV0dXJuIHByaW1pdGl2ZTtcbiAgfVxuXG4gIC8vIExvb2sgdXAgdGhlIGtleXMgb2YgdGhlIG9iamVjdC5cbiAgdmFyIGtleXMgPSBPYmplY3Qua2V5cyh2YWx1ZSk7XG4gIHZhciB2aXNpYmxlS2V5cyA9IGFycmF5VG9IYXNoKGtleXMpO1xuXG4gIGlmIChjdHguc2hvd0hpZGRlbikge1xuICAgIGtleXMgPSBPYmplY3QuZ2V0T3duUHJvcGVydHlOYW1lcyh2YWx1ZSk7XG4gIH1cblxuICAvLyBJRSBkb2Vzbid0IG1ha2UgZXJyb3IgZmllbGRzIG5vbi1lbnVtZXJhYmxlXG4gIC8vIGh0dHA6Ly9tc2RuLm1pY3Jvc29mdC5jb20vZW4tdXMvbGlicmFyeS9pZS9kd3c1MnNidCh2PXZzLjk0KS5hc3B4XG4gIGlmIChpc0Vycm9yKHZhbHVlKVxuICAgICAgJiYgKGtleXMuaW5kZXhPZignbWVzc2FnZScpID49IDAgfHwga2V5cy5pbmRleE9mKCdkZXNjcmlwdGlvbicpID49IDApKSB7XG4gICAgcmV0dXJuIGZvcm1hdEVycm9yKHZhbHVlKTtcbiAgfVxuXG4gIC8vIFNvbWUgdHlwZSBvZiBvYmplY3Qgd2l0aG91dCBwcm9wZXJ0aWVzIGNhbiBiZSBzaG9ydGN1dHRlZC5cbiAgaWYgKGtleXMubGVuZ3RoID09PSAwKSB7XG4gICAgaWYgKGlzRnVuY3Rpb24odmFsdWUpKSB7XG4gICAgICB2YXIgbmFtZSA9IHZhbHVlLm5hbWUgPyAnOiAnICsgdmFsdWUubmFtZSA6ICcnO1xuICAgICAgcmV0dXJuIGN0eC5zdHlsaXplKCdbRnVuY3Rpb24nICsgbmFtZSArICddJywgJ3NwZWNpYWwnKTtcbiAgICB9XG4gICAgaWYgKGlzUmVnRXhwKHZhbHVlKSkge1xuICAgICAgcmV0dXJuIGN0eC5zdHlsaXplKFJlZ0V4cC5wcm90b3R5cGUudG9TdHJpbmcuY2FsbCh2YWx1ZSksICdyZWdleHAnKTtcbiAgICB9XG4gICAgaWYgKGlzRGF0ZSh2YWx1ZSkpIHtcbiAgICAgIHJldHVybiBjdHguc3R5bGl6ZShEYXRlLnByb3RvdHlwZS50b1N0cmluZy5jYWxsKHZhbHVlKSwgJ2RhdGUnKTtcbiAgICB9XG4gICAgaWYgKGlzRXJyb3IodmFsdWUpKSB7XG4gICAgICByZXR1cm4gZm9ybWF0RXJyb3IodmFsdWUpO1xuICAgIH1cbiAgfVxuXG4gIHZhciBiYXNlID0gJycsIGFycmF5ID0gZmFsc2UsIGJyYWNlcyA9IFsneycsICd9J107XG5cbiAgLy8gTWFrZSBBcnJheSBzYXkgdGhhdCB0aGV5IGFyZSBBcnJheVxuICBpZiAoaXNBcnJheSh2YWx1ZSkpIHtcbiAgICBhcnJheSA9IHRydWU7XG4gICAgYnJhY2VzID0gWydbJywgJ10nXTtcbiAgfVxuXG4gIC8vIE1ha2UgZnVuY3Rpb25zIHNheSB0aGF0IHRoZXkgYXJlIGZ1bmN0aW9uc1xuICBpZiAoaXNGdW5jdGlvbih2YWx1ZSkpIHtcbiAgICB2YXIgbiA9IHZhbHVlLm5hbWUgPyAnOiAnICsgdmFsdWUubmFtZSA6ICcnO1xuICAgIGJhc2UgPSAnIFtGdW5jdGlvbicgKyBuICsgJ10nO1xuICB9XG5cbiAgLy8gTWFrZSBSZWdFeHBzIHNheSB0aGF0IHRoZXkgYXJlIFJlZ0V4cHNcbiAgaWYgKGlzUmVnRXhwKHZhbHVlKSkge1xuICAgIGJhc2UgPSAnICcgKyBSZWdFeHAucHJvdG90eXBlLnRvU3RyaW5nLmNhbGwodmFsdWUpO1xuICB9XG5cbiAgLy8gTWFrZSBkYXRlcyB3aXRoIHByb3BlcnRpZXMgZmlyc3Qgc2F5IHRoZSBkYXRlXG4gIGlmIChpc0RhdGUodmFsdWUpKSB7XG4gICAgYmFzZSA9ICcgJyArIERhdGUucHJvdG90eXBlLnRvVVRDU3RyaW5nLmNhbGwodmFsdWUpO1xuICB9XG5cbiAgLy8gTWFrZSBlcnJvciB3aXRoIG1lc3NhZ2UgZmlyc3Qgc2F5IHRoZSBlcnJvclxuICBpZiAoaXNFcnJvcih2YWx1ZSkpIHtcbiAgICBiYXNlID0gJyAnICsgZm9ybWF0RXJyb3IodmFsdWUpO1xuICB9XG5cbiAgaWYgKGtleXMubGVuZ3RoID09PSAwICYmICghYXJyYXkgfHwgdmFsdWUubGVuZ3RoID09IDApKSB7XG4gICAgcmV0dXJuIGJyYWNlc1swXSArIGJhc2UgKyBicmFjZXNbMV07XG4gIH1cblxuICBpZiAocmVjdXJzZVRpbWVzIDwgMCkge1xuICAgIGlmIChpc1JlZ0V4cCh2YWx1ZSkpIHtcbiAgICAgIHJldHVybiBjdHguc3R5bGl6ZShSZWdFeHAucHJvdG90eXBlLnRvU3RyaW5nLmNhbGwodmFsdWUpLCAncmVnZXhwJyk7XG4gICAgfSBlbHNlIHtcbiAgICAgIHJldHVybiBjdHguc3R5bGl6ZSgnW09iamVjdF0nLCAnc3BlY2lhbCcpO1xuICAgIH1cbiAgfVxuXG4gIGN0eC5zZWVuLnB1c2godmFsdWUpO1xuXG4gIHZhciBvdXRwdXQ7XG4gIGlmIChhcnJheSkge1xuICAgIG91dHB1dCA9IGZvcm1hdEFycmF5KGN0eCwgdmFsdWUsIHJlY3Vyc2VUaW1lcywgdmlzaWJsZUtleXMsIGtleXMpO1xuICB9IGVsc2Uge1xuICAgIG91dHB1dCA9IGtleXMubWFwKGZ1bmN0aW9uKGtleSkge1xuICAgICAgcmV0dXJuIGZvcm1hdFByb3BlcnR5KGN0eCwgdmFsdWUsIHJlY3Vyc2VUaW1lcywgdmlzaWJsZUtleXMsIGtleSwgYXJyYXkpO1xuICAgIH0pO1xuICB9XG5cbiAgY3R4LnNlZW4ucG9wKCk7XG5cbiAgcmV0dXJuIHJlZHVjZVRvU2luZ2xlU3RyaW5nKG91dHB1dCwgYmFzZSwgYnJhY2VzKTtcbn1cblxuXG5mdW5jdGlvbiBmb3JtYXRQcmltaXRpdmUoY3R4LCB2YWx1ZSkge1xuICBpZiAoaXNVbmRlZmluZWQodmFsdWUpKVxuICAgIHJldHVybiBjdHguc3R5bGl6ZSgndW5kZWZpbmVkJywgJ3VuZGVmaW5lZCcpO1xuICBpZiAoaXNTdHJpbmcodmFsdWUpKSB7XG4gICAgdmFyIHNpbXBsZSA9ICdcXCcnICsgSlNPTi5zdHJpbmdpZnkodmFsdWUpLnJlcGxhY2UoL15cInxcIiQvZywgJycpXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAucmVwbGFjZSgvJy9nLCBcIlxcXFwnXCIpXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAucmVwbGFjZSgvXFxcXFwiL2csICdcIicpICsgJ1xcJyc7XG4gICAgcmV0dXJuIGN0eC5zdHlsaXplKHNpbXBsZSwgJ3N0cmluZycpO1xuICB9XG4gIGlmIChpc051bWJlcih2YWx1ZSkpXG4gICAgcmV0dXJuIGN0eC5zdHlsaXplKCcnICsgdmFsdWUsICdudW1iZXInKTtcbiAgaWYgKGlzQm9vbGVhbih2YWx1ZSkpXG4gICAgcmV0dXJuIGN0eC5zdHlsaXplKCcnICsgdmFsdWUsICdib29sZWFuJyk7XG4gIC8vIEZvciBzb21lIHJlYXNvbiB0eXBlb2YgbnVsbCBpcyBcIm9iamVjdFwiLCBzbyBzcGVjaWFsIGNhc2UgaGVyZS5cbiAgaWYgKGlzTnVsbCh2YWx1ZSkpXG4gICAgcmV0dXJuIGN0eC5zdHlsaXplKCdudWxsJywgJ251bGwnKTtcbn1cblxuXG5mdW5jdGlvbiBmb3JtYXRFcnJvcih2YWx1ZSkge1xuICByZXR1cm4gJ1snICsgRXJyb3IucHJvdG90eXBlLnRvU3RyaW5nLmNhbGwodmFsdWUpICsgJ10nO1xufVxuXG5cbmZ1bmN0aW9uIGZvcm1hdEFycmF5KGN0eCwgdmFsdWUsIHJlY3Vyc2VUaW1lcywgdmlzaWJsZUtleXMsIGtleXMpIHtcbiAgdmFyIG91dHB1dCA9IFtdO1xuICBmb3IgKHZhciBpID0gMCwgbCA9IHZhbHVlLmxlbmd0aDsgaSA8IGw7ICsraSkge1xuICAgIGlmIChoYXNPd25Qcm9wZXJ0eSh2YWx1ZSwgU3RyaW5nKGkpKSkge1xuICAgICAgb3V0cHV0LnB1c2goZm9ybWF0UHJvcGVydHkoY3R4LCB2YWx1ZSwgcmVjdXJzZVRpbWVzLCB2aXNpYmxlS2V5cyxcbiAgICAgICAgICBTdHJpbmcoaSksIHRydWUpKTtcbiAgICB9IGVsc2Uge1xuICAgICAgb3V0cHV0LnB1c2goJycpO1xuICAgIH1cbiAgfVxuICBrZXlzLmZvckVhY2goZnVuY3Rpb24oa2V5KSB7XG4gICAgaWYgKCFrZXkubWF0Y2goL15cXGQrJC8pKSB7XG4gICAgICBvdXRwdXQucHVzaChmb3JtYXRQcm9wZXJ0eShjdHgsIHZhbHVlLCByZWN1cnNlVGltZXMsIHZpc2libGVLZXlzLFxuICAgICAgICAgIGtleSwgdHJ1ZSkpO1xuICAgIH1cbiAgfSk7XG4gIHJldHVybiBvdXRwdXQ7XG59XG5cblxuZnVuY3Rpb24gZm9ybWF0UHJvcGVydHkoY3R4LCB2YWx1ZSwgcmVjdXJzZVRpbWVzLCB2aXNpYmxlS2V5cywga2V5LCBhcnJheSkge1xuICB2YXIgbmFtZSwgc3RyLCBkZXNjO1xuICBkZXNjID0gT2JqZWN0LmdldE93blByb3BlcnR5RGVzY3JpcHRvcih2YWx1ZSwga2V5KSB8fCB7IHZhbHVlOiB2YWx1ZVtrZXldIH07XG4gIGlmIChkZXNjLmdldCkge1xuICAgIGlmIChkZXNjLnNldCkge1xuICAgICAgc3RyID0gY3R4LnN0eWxpemUoJ1tHZXR0ZXIvU2V0dGVyXScsICdzcGVjaWFsJyk7XG4gICAgfSBlbHNlIHtcbiAgICAgIHN0ciA9IGN0eC5zdHlsaXplKCdbR2V0dGVyXScsICdzcGVjaWFsJyk7XG4gICAgfVxuICB9IGVsc2Uge1xuICAgIGlmIChkZXNjLnNldCkge1xuICAgICAgc3RyID0gY3R4LnN0eWxpemUoJ1tTZXR0ZXJdJywgJ3NwZWNpYWwnKTtcbiAgICB9XG4gIH1cbiAgaWYgKCFoYXNPd25Qcm9wZXJ0eSh2aXNpYmxlS2V5cywga2V5KSkge1xuICAgIG5hbWUgPSAnWycgKyBrZXkgKyAnXSc7XG4gIH1cbiAgaWYgKCFzdHIpIHtcbiAgICBpZiAoY3R4LnNlZW4uaW5kZXhPZihkZXNjLnZhbHVlKSA8IDApIHtcbiAgICAgIGlmIChpc051bGwocmVjdXJzZVRpbWVzKSkge1xuICAgICAgICBzdHIgPSBmb3JtYXRWYWx1ZShjdHgsIGRlc2MudmFsdWUsIG51bGwpO1xuICAgICAgfSBlbHNlIHtcbiAgICAgICAgc3RyID0gZm9ybWF0VmFsdWUoY3R4LCBkZXNjLnZhbHVlLCByZWN1cnNlVGltZXMgLSAxKTtcbiAgICAgIH1cbiAgICAgIGlmIChzdHIuaW5kZXhPZignXFxuJykgPiAtMSkge1xuICAgICAgICBpZiAoYXJyYXkpIHtcbiAgICAgICAgICBzdHIgPSBzdHIuc3BsaXQoJ1xcbicpLm1hcChmdW5jdGlvbihsaW5lKSB7XG4gICAgICAgICAgICByZXR1cm4gJyAgJyArIGxpbmU7XG4gICAgICAgICAgfSkuam9pbignXFxuJykuc3Vic3RyKDIpO1xuICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgIHN0ciA9ICdcXG4nICsgc3RyLnNwbGl0KCdcXG4nKS5tYXAoZnVuY3Rpb24obGluZSkge1xuICAgICAgICAgICAgcmV0dXJuICcgICAnICsgbGluZTtcbiAgICAgICAgICB9KS5qb2luKCdcXG4nKTtcbiAgICAgICAgfVxuICAgICAgfVxuICAgIH0gZWxzZSB7XG4gICAgICBzdHIgPSBjdHguc3R5bGl6ZSgnW0NpcmN1bGFyXScsICdzcGVjaWFsJyk7XG4gICAgfVxuICB9XG4gIGlmIChpc1VuZGVmaW5lZChuYW1lKSkge1xuICAgIGlmIChhcnJheSAmJiBrZXkubWF0Y2goL15cXGQrJC8pKSB7XG4gICAgICByZXR1cm4gc3RyO1xuICAgIH1cbiAgICBuYW1lID0gSlNPTi5zdHJpbmdpZnkoJycgKyBrZXkpO1xuICAgIGlmIChuYW1lLm1hdGNoKC9eXCIoW2EtekEtWl9dW2EtekEtWl8wLTldKilcIiQvKSkge1xuICAgICAgbmFtZSA9IG5hbWUuc3Vic3RyKDEsIG5hbWUubGVuZ3RoIC0gMik7XG4gICAgICBuYW1lID0gY3R4LnN0eWxpemUobmFtZSwgJ25hbWUnKTtcbiAgICB9IGVsc2Uge1xuICAgICAgbmFtZSA9IG5hbWUucmVwbGFjZSgvJy9nLCBcIlxcXFwnXCIpXG4gICAgICAgICAgICAgICAgIC5yZXBsYWNlKC9cXFxcXCIvZywgJ1wiJylcbiAgICAgICAgICAgICAgICAgLnJlcGxhY2UoLyheXCJ8XCIkKS9nLCBcIidcIik7XG4gICAgICBuYW1lID0gY3R4LnN0eWxpemUobmFtZSwgJ3N0cmluZycpO1xuICAgIH1cbiAgfVxuXG4gIHJldHVybiBuYW1lICsgJzogJyArIHN0cjtcbn1cblxuXG5mdW5jdGlvbiByZWR1Y2VUb1NpbmdsZVN0cmluZyhvdXRwdXQsIGJhc2UsIGJyYWNlcykge1xuICB2YXIgbnVtTGluZXNFc3QgPSAwO1xuICB2YXIgbGVuZ3RoID0gb3V0cHV0LnJlZHVjZShmdW5jdGlvbihwcmV2LCBjdXIpIHtcbiAgICBudW1MaW5lc0VzdCsrO1xuICAgIGlmIChjdXIuaW5kZXhPZignXFxuJykgPj0gMCkgbnVtTGluZXNFc3QrKztcbiAgICByZXR1cm4gcHJldiArIGN1ci5yZXBsYWNlKC9cXHUwMDFiXFxbXFxkXFxkP20vZywgJycpLmxlbmd0aCArIDE7XG4gIH0sIDApO1xuXG4gIGlmIChsZW5ndGggPiA2MCkge1xuICAgIHJldHVybiBicmFjZXNbMF0gK1xuICAgICAgICAgICAoYmFzZSA9PT0gJycgPyAnJyA6IGJhc2UgKyAnXFxuICcpICtcbiAgICAgICAgICAgJyAnICtcbiAgICAgICAgICAgb3V0cHV0LmpvaW4oJyxcXG4gICcpICtcbiAgICAgICAgICAgJyAnICtcbiAgICAgICAgICAgYnJhY2VzWzFdO1xuICB9XG5cbiAgcmV0dXJuIGJyYWNlc1swXSArIGJhc2UgKyAnICcgKyBvdXRwdXQuam9pbignLCAnKSArICcgJyArIGJyYWNlc1sxXTtcbn1cblxuXG4vLyBOT1RFOiBUaGVzZSB0eXBlIGNoZWNraW5nIGZ1bmN0aW9ucyBpbnRlbnRpb25hbGx5IGRvbid0IHVzZSBgaW5zdGFuY2VvZmBcbi8vIGJlY2F1c2UgaXQgaXMgZnJhZ2lsZSBhbmQgY2FuIGJlIGVhc2lseSBmYWtlZCB3aXRoIGBPYmplY3QuY3JlYXRlKClgLlxuZnVuY3Rpb24gaXNBcnJheShhcikge1xuICByZXR1cm4gQXJyYXkuaXNBcnJheShhcik7XG59XG5leHBvcnRzLmlzQXJyYXkgPSBpc0FycmF5O1xuXG5mdW5jdGlvbiBpc0Jvb2xlYW4oYXJnKSB7XG4gIHJldHVybiB0eXBlb2YgYXJnID09PSAnYm9vbGVhbic7XG59XG5leHBvcnRzLmlzQm9vbGVhbiA9IGlzQm9vbGVhbjtcblxuZnVuY3Rpb24gaXNOdWxsKGFyZykge1xuICByZXR1cm4gYXJnID09PSBudWxsO1xufVxuZXhwb3J0cy5pc051bGwgPSBpc051bGw7XG5cbmZ1bmN0aW9uIGlzTnVsbE9yVW5kZWZpbmVkKGFyZykge1xuICByZXR1cm4gYXJnID09IG51bGw7XG59XG5leHBvcnRzLmlzTnVsbE9yVW5kZWZpbmVkID0gaXNOdWxsT3JVbmRlZmluZWQ7XG5cbmZ1bmN0aW9uIGlzTnVtYmVyKGFyZykge1xuICByZXR1cm4gdHlwZW9mIGFyZyA9PT0gJ251bWJlcic7XG59XG5leHBvcnRzLmlzTnVtYmVyID0gaXNOdW1iZXI7XG5cbmZ1bmN0aW9uIGlzU3RyaW5nKGFyZykge1xuICByZXR1cm4gdHlwZW9mIGFyZyA9PT0gJ3N0cmluZyc7XG59XG5leHBvcnRzLmlzU3RyaW5nID0gaXNTdHJpbmc7XG5cbmZ1bmN0aW9uIGlzU3ltYm9sKGFyZykge1xuICByZXR1cm4gdHlwZW9mIGFyZyA9PT0gJ3N5bWJvbCc7XG59XG5leHBvcnRzLmlzU3ltYm9sID0gaXNTeW1ib2w7XG5cbmZ1bmN0aW9uIGlzVW5kZWZpbmVkKGFyZykge1xuICByZXR1cm4gYXJnID09PSB2b2lkIDA7XG59XG5leHBvcnRzLmlzVW5kZWZpbmVkID0gaXNVbmRlZmluZWQ7XG5cbmZ1bmN0aW9uIGlzUmVnRXhwKHJlKSB7XG4gIHJldHVybiBpc09iamVjdChyZSkgJiYgb2JqZWN0VG9TdHJpbmcocmUpID09PSAnW29iamVjdCBSZWdFeHBdJztcbn1cbmV4cG9ydHMuaXNSZWdFeHAgPSBpc1JlZ0V4cDtcblxuZnVuY3Rpb24gaXNPYmplY3QoYXJnKSB7XG4gIHJldHVybiB0eXBlb2YgYXJnID09PSAnb2JqZWN0JyAmJiBhcmcgIT09IG51bGw7XG59XG5leHBvcnRzLmlzT2JqZWN0ID0gaXNPYmplY3Q7XG5cbmZ1bmN0aW9uIGlzRGF0ZShkKSB7XG4gIHJldHVybiBpc09iamVjdChkKSAmJiBvYmplY3RUb1N0cmluZyhkKSA9PT0gJ1tvYmplY3QgRGF0ZV0nO1xufVxuZXhwb3J0cy5pc0RhdGUgPSBpc0RhdGU7XG5cbmZ1bmN0aW9uIGlzRXJyb3IoZSkge1xuICByZXR1cm4gaXNPYmplY3QoZSkgJiZcbiAgICAgIChvYmplY3RUb1N0cmluZyhlKSA9PT0gJ1tvYmplY3QgRXJyb3JdJyB8fCBlIGluc3RhbmNlb2YgRXJyb3IpO1xufVxuZXhwb3J0cy5pc0Vycm9yID0gaXNFcnJvcjtcblxuZnVuY3Rpb24gaXNGdW5jdGlvbihhcmcpIHtcbiAgcmV0dXJuIHR5cGVvZiBhcmcgPT09ICdmdW5jdGlvbic7XG59XG5leHBvcnRzLmlzRnVuY3Rpb24gPSBpc0Z1bmN0aW9uO1xuXG5mdW5jdGlvbiBpc1ByaW1pdGl2ZShhcmcpIHtcbiAgcmV0dXJuIGFyZyA9PT0gbnVsbCB8fFxuICAgICAgICAgdHlwZW9mIGFyZyA9PT0gJ2Jvb2xlYW4nIHx8XG4gICAgICAgICB0eXBlb2YgYXJnID09PSAnbnVtYmVyJyB8fFxuICAgICAgICAgdHlwZW9mIGFyZyA9PT0gJ3N0cmluZycgfHxcbiAgICAgICAgIHR5cGVvZiBhcmcgPT09ICdzeW1ib2wnIHx8ICAvLyBFUzYgc3ltYm9sXG4gICAgICAgICB0eXBlb2YgYXJnID09PSAndW5kZWZpbmVkJztcbn1cbmV4cG9ydHMuaXNQcmltaXRpdmUgPSBpc1ByaW1pdGl2ZTtcblxuZXhwb3J0cy5pc0J1ZmZlciA9IHJlcXVpcmUoJy4vc3VwcG9ydC9pc0J1ZmZlcicpO1xuXG5mdW5jdGlvbiBvYmplY3RUb1N0cmluZyhvKSB7XG4gIHJldHVybiBPYmplY3QucHJvdG90eXBlLnRvU3RyaW5nLmNhbGwobyk7XG59XG5cblxuZnVuY3Rpb24gcGFkKG4pIHtcbiAgcmV0dXJuIG4gPCAxMCA/ICcwJyArIG4udG9TdHJpbmcoMTApIDogbi50b1N0cmluZygxMCk7XG59XG5cblxudmFyIG1vbnRocyA9IFsnSmFuJywgJ0ZlYicsICdNYXInLCAnQXByJywgJ01heScsICdKdW4nLCAnSnVsJywgJ0F1ZycsICdTZXAnLFxuICAgICAgICAgICAgICAnT2N0JywgJ05vdicsICdEZWMnXTtcblxuLy8gMjYgRmViIDE2OjE5OjM0XG5mdW5jdGlvbiB0aW1lc3RhbXAoKSB7XG4gIHZhciBkID0gbmV3IERhdGUoKTtcbiAgdmFyIHRpbWUgPSBbcGFkKGQuZ2V0SG91cnMoKSksXG4gICAgICAgICAgICAgIHBhZChkLmdldE1pbnV0ZXMoKSksXG4gICAgICAgICAgICAgIHBhZChkLmdldFNlY29uZHMoKSldLmpvaW4oJzonKTtcbiAgcmV0dXJuIFtkLmdldERhdGUoKSwgbW9udGhzW2QuZ2V0TW9udGgoKV0sIHRpbWVdLmpvaW4oJyAnKTtcbn1cblxuXG4vLyBsb2cgaXMganVzdCBhIHRoaW4gd3JhcHBlciB0byBjb25zb2xlLmxvZyB0aGF0IHByZXBlbmRzIGEgdGltZXN0YW1wXG5leHBvcnRzLmxvZyA9IGZ1bmN0aW9uKCkge1xuICBjb25zb2xlLmxvZygnJXMgLSAlcycsIHRpbWVzdGFtcCgpLCBleHBvcnRzLmZvcm1hdC5hcHBseShleHBvcnRzLCBhcmd1bWVudHMpKTtcbn07XG5cblxuLyoqXG4gKiBJbmhlcml0IHRoZSBwcm90b3R5cGUgbWV0aG9kcyBmcm9tIG9uZSBjb25zdHJ1Y3RvciBpbnRvIGFub3RoZXIuXG4gKlxuICogVGhlIEZ1bmN0aW9uLnByb3RvdHlwZS5pbmhlcml0cyBmcm9tIGxhbmcuanMgcmV3cml0dGVuIGFzIGEgc3RhbmRhbG9uZVxuICogZnVuY3Rpb24gKG5vdCBvbiBGdW5jdGlvbi5wcm90b3R5cGUpLiBOT1RFOiBJZiB0aGlzIGZpbGUgaXMgdG8gYmUgbG9hZGVkXG4gKiBkdXJpbmcgYm9vdHN0cmFwcGluZyB0aGlzIGZ1bmN0aW9uIG5lZWRzIHRvIGJlIHJld3JpdHRlbiB1c2luZyBzb21lIG5hdGl2ZVxuICogZnVuY3Rpb25zIGFzIHByb3RvdHlwZSBzZXR1cCB1c2luZyBub3JtYWwgSmF2YVNjcmlwdCBkb2VzIG5vdCB3b3JrIGFzXG4gKiBleHBlY3RlZCBkdXJpbmcgYm9vdHN0cmFwcGluZyAoc2VlIG1pcnJvci5qcyBpbiByMTE0OTAzKS5cbiAqXG4gKiBAcGFyYW0ge2Z1bmN0aW9ufSBjdG9yIENvbnN0cnVjdG9yIGZ1bmN0aW9uIHdoaWNoIG5lZWRzIHRvIGluaGVyaXQgdGhlXG4gKiAgICAgcHJvdG90eXBlLlxuICogQHBhcmFtIHtmdW5jdGlvbn0gc3VwZXJDdG9yIENvbnN0cnVjdG9yIGZ1bmN0aW9uIHRvIGluaGVyaXQgcHJvdG90eXBlIGZyb20uXG4gKi9cbmV4cG9ydHMuaW5oZXJpdHMgPSByZXF1aXJlKCdpbmhlcml0cycpO1xuXG5leHBvcnRzLl9leHRlbmQgPSBmdW5jdGlvbihvcmlnaW4sIGFkZCkge1xuICAvLyBEb24ndCBkbyBhbnl0aGluZyBpZiBhZGQgaXNuJ3QgYW4gb2JqZWN0XG4gIGlmICghYWRkIHx8ICFpc09iamVjdChhZGQpKSByZXR1cm4gb3JpZ2luO1xuXG4gIHZhciBrZXlzID0gT2JqZWN0LmtleXMoYWRkKTtcbiAgdmFyIGkgPSBrZXlzLmxlbmd0aDtcbiAgd2hpbGUgKGktLSkge1xuICAgIG9yaWdpbltrZXlzW2ldXSA9IGFkZFtrZXlzW2ldXTtcbiAgfVxuICByZXR1cm4gb3JpZ2luO1xufTtcblxuZnVuY3Rpb24gaGFzT3duUHJvcGVydHkob2JqLCBwcm9wKSB7XG4gIHJldHVybiBPYmplY3QucHJvdG90eXBlLmhhc093blByb3BlcnR5LmNhbGwob2JqLCBwcm9wKTtcbn1cbiJdfQ==
