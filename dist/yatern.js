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
var util = require('util');
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
exports.onFunctionKeyword = retOccur.onFunctionKeyword;
exports.findReturnStatements = retOccur.findReturnStatements;

},{"./aux":1,"./constraint/cGen":2,"./domains/context":4,"./domains/status":5,"./domains/types":6,"./retOccur":8,"./varBlock":10,"./varrefs":11,"acorn/dist/acorn":12,"acorn/dist/acorn_loose":13,"util":18}],8:[function(require,module,exports){
/**
 * Created by swkim on 15. 7. 29.
 */

'use strict';

var walk = require('acorn/dist/walk');
var myWalker = require('./util/myWalker');

/**
 * Check whether given pos is on a function keyword
 * @param ast - AST of a program
 * @param pos - index position
 * @returns {*} - function node or null
 */
function onFunctionKeyword(ast, pos) {
    'use strict';

    // find function node
    var walker = myWalker.wrapWalker(walk.base, function (node, vb) {
        if (node.start > pos || node.end < pos) {
            return false;
        }
        // 8 is the length of 'function' keyword
        if ((node.type === 'FunctionDeclaration' || node.type === 'FunctionExpression') && (node.start <= pos && pos <= node.start + 8)) {
            throw node;
        }
        return true;
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

    var fNode = onFunctionKeyword(ast, pos);
    if (!fNode) {
        // pos is not on function keyword
        return null;
    }

    var refs = getReturnNodes(fNode);
    if (includeFunctionKeyword) {
        refs.push({ start: fNode.start, end: fNode.start + 8 });
    }
    return refs;
}

exports.onFunctionKeyword = onFunctionKeyword;
exports.findReturnStatements = findReturnStatements;

// not visit inner functions

},{"./util/myWalker":9,"acorn/dist/walk":14}],9:[function(require,module,exports){
/**
 *
 * @param preNode - Apply before visiting the current node.
 * If returns false, do not visit the node.
 * @param postNode - Apply after visiting the current node.
 * If given, return values are overridden.
 * @returns {*} - a new walker
 */
"use strict";

function wrapWalker(walker, preNode, postNode) {
    var retWalker = {};

    var _loop = function (nodeType) {
        if (!walker.hasOwnProperty(nodeType)) {
            return "continue";
        }
        retWalker[nodeType] = function (node, st, c) {
            var ret = undefined;
            if (!preNode || preNode(node, st, c)) {
                ret = walker[nodeType](node, st, c);
            } else {
                return;
            }
            if (postNode) {
                ret = postNode(node, st, c);
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
//# sourceMappingURL=data:application/json;charset:utf-8;base64,eyJ2ZXJzaW9uIjozLCJzb3VyY2VzIjpbIm5vZGVfbW9kdWxlcy9icm93c2VyaWZ5L25vZGVfbW9kdWxlcy9icm93c2VyLXBhY2svX3ByZWx1ZGUuanMiLCIvaG9tZS9zd2tpbS9XZWJzdG9ybVByb2plY3RzL3lhdGVybi9saWIvYXV4LmpzIiwiL2hvbWUvc3draW0vV2Vic3Rvcm1Qcm9qZWN0cy95YXRlcm4vbGliL2NvbnN0cmFpbnQvY0dlbi5qcyIsIi9ob21lL3N3a2ltL1dlYnN0b3JtUHJvamVjdHMveWF0ZXJuL2xpYi9jb25zdHJhaW50L2NvbnN0cmFpbnRzLmpzIiwiL2hvbWUvc3draW0vV2Vic3Rvcm1Qcm9qZWN0cy95YXRlcm4vbGliL2RvbWFpbnMvY29udGV4dC5qcyIsIi9ob21lL3N3a2ltL1dlYnN0b3JtUHJvamVjdHMveWF0ZXJuL2xpYi9kb21haW5zL3N0YXR1cy5qcyIsIi9ob21lL3N3a2ltL1dlYnN0b3JtUHJvamVjdHMveWF0ZXJuL2xpYi9kb21haW5zL3R5cGVzLmpzIiwiL2hvbWUvc3draW0vV2Vic3Rvcm1Qcm9qZWN0cy95YXRlcm4vbGliL2luZmVyLmpzIiwiL2hvbWUvc3draW0vV2Vic3Rvcm1Qcm9qZWN0cy95YXRlcm4vbGliL3JldE9jY3VyLmpzIiwiL2hvbWUvc3draW0vV2Vic3Rvcm1Qcm9qZWN0cy95YXRlcm4vbGliL3V0aWwvbXlXYWxrZXIuanMiLCIvaG9tZS9zd2tpbS9XZWJzdG9ybVByb2plY3RzL3lhdGVybi9saWIvdmFyQmxvY2suanMiLCIvaG9tZS9zd2tpbS9XZWJzdG9ybVByb2plY3RzL3lhdGVybi9saWIvdmFycmVmcy5qcyIsIm5vZGVfbW9kdWxlcy9hY29ybi9kaXN0L2Fjb3JuLmpzIiwibm9kZV9tb2R1bGVzL2Fjb3JuL2Rpc3QvYWNvcm5fbG9vc2UuanMiLCJub2RlX21vZHVsZXMvYWNvcm4vZGlzdC93YWxrLmpzIiwibm9kZV9tb2R1bGVzL2Jyb3dzZXJpZnkvbm9kZV9tb2R1bGVzL2luaGVyaXRzL2luaGVyaXRzX2Jyb3dzZXIuanMiLCJub2RlX21vZHVsZXMvYnJvd3NlcmlmeS9ub2RlX21vZHVsZXMvcHJvY2Vzcy9icm93c2VyLmpzIiwibm9kZV9tb2R1bGVzL2Jyb3dzZXJpZnkvbm9kZV9tb2R1bGVzL3V0aWwvc3VwcG9ydC9pc0J1ZmZlckJyb3dzZXIuanMiLCJub2RlX21vZHVsZXMvYnJvd3NlcmlmeS9ub2RlX21vZHVsZXMvdXRpbC91dGlsLmpzIl0sIm5hbWVzIjpbXSwibWFwcGluZ3MiOiJBQUFBOzs7QUNBQSxJQUFJLElBQUksR0FBRyxPQUFPLENBQUMsTUFBTSxDQUFDLENBQUM7O0FBRTNCLFNBQVMsV0FBVyxDQUFDLEdBQUcsRUFBRSxRQUFRLEVBQUU7QUFDaEMsUUFBSSxRQUFRLEdBQUcsRUFBRSxDQUFDOztBQUVsQixRQUFJLEdBQUcsR0FBRyxRQUFRLEtBQUssU0FBUyxHQUFHLENBQUMsR0FBRyxRQUFRLENBQUM7O0FBRWhELGFBQVMsUUFBUSxDQUFDLElBQUksRUFBRTtBQUNwQixZQUFJLENBQUMsUUFBUSxDQUFDLEdBQUcsR0FBRyxDQUFDO0FBQ3JCLGdCQUFRLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQyxDQUFDO0FBQ3BCLFdBQUcsRUFBRSxDQUFDO0tBQ1Q7OztBQUdELGFBQVMsaUJBQWlCLENBQUMsSUFBSSxFQUFFO0FBQzdCLFlBQUksSUFBSSxJQUFJLElBQUksQ0FBQyxjQUFjLENBQUMsTUFBTSxDQUFDLEVBQUU7QUFDckMsb0JBQVEsQ0FBQyxJQUFJLENBQUMsQ0FBQztTQUNsQjtBQUNELFlBQUksSUFBSSxJQUFJLE9BQU8sSUFBSSxLQUFLLFFBQVEsRUFBRTtBQUNsQyxpQkFBSyxJQUFJLENBQUMsSUFBSSxJQUFJLEVBQUU7QUFDaEIsaUNBQWlCLENBQUMsSUFBSSxDQUFDLENBQUMsQ0FBQyxDQUFDLENBQUM7YUFDOUI7U0FDSjtLQUNKOztBQUVELHFCQUFpQixDQUFDLEdBQUcsQ0FBQyxDQUFDOztBQUV2QixXQUFPLFFBQVEsQ0FBQztDQUNuQjs7QUFFRCxTQUFTLFlBQVksQ0FBQyxHQUFHLEVBQUU7QUFDdkIs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O0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTs7Ozs7QUM3NkhBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBOzs7OztBQ3R4Q0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBOzs7O0FDclZBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTs7QUN2QkE7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7O0FDMUZBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTs7O0FDTEE7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSIsImZpbGUiOiJnZW5lcmF0ZWQuanMiLCJzb3VyY2VSb290IjoiIiwic291cmNlc0NvbnRlbnQiOlsiKGZ1bmN0aW9uIGUodCxuLHIpe2Z1bmN0aW9uIHMobyx1KXtpZighbltvXSl7aWYoIXRbb10pe3ZhciBhPXR5cGVvZiByZXF1aXJlPT1cImZ1bmN0aW9uXCImJnJlcXVpcmU7aWYoIXUmJmEpcmV0dXJuIGEobywhMCk7aWYoaSlyZXR1cm4gaShvLCEwKTt2YXIgZj1uZXcgRXJyb3IoXCJDYW5ub3QgZmluZCBtb2R1bGUgJ1wiK28rXCInXCIpO3Rocm93IGYuY29kZT1cIk1PRFVMRV9OT1RfRk9VTkRcIixmfXZhciBsPW5bb109e2V4cG9ydHM6e319O3Rbb11bMF0uY2FsbChsLmV4cG9ydHMsZnVuY3Rpb24oZSl7dmFyIG49dFtvXVsxXVtlXTtyZXR1cm4gcyhuP246ZSl9LGwsbC5leHBvcnRzLGUsdCxuLHIpfXJldHVybiBuW29dLmV4cG9ydHN9dmFyIGk9dHlwZW9mIHJlcXVpcmU9PVwiZnVuY3Rpb25cIiYmcmVxdWlyZTtmb3IodmFyIG89MDtvPHIubGVuZ3RoO28rKylzKHJbb10pO3JldHVybiBzfSkiLCJ2YXIgdXRpbCA9IHJlcXVpcmUoJ3V0aWwnKTtcblxuZnVuY3Rpb24gZ2V0Tm9kZUxpc3QoYXN0LCBzdGFydE51bSkge1xuICAgIHZhciBub2RlTGlzdCA9IFtdO1xuXG4gICAgdmFyIG51bSA9IHN0YXJ0TnVtID09PSB1bmRlZmluZWQgPyAwIDogc3RhcnROdW07XG5cbiAgICBmdW5jdGlvbiBhc3NpZ25JZChub2RlKSB7XG4gICAgICAgIG5vZGVbJ0BsYWJlbCddID0gbnVtO1xuICAgICAgICBub2RlTGlzdC5wdXNoKG5vZGUpO1xuICAgICAgICBudW0rKztcbiAgICB9XG5cbiAgICAvLyBMYWJlbCBldmVyeSBBU1Qgbm9kZSB3aXRoIHByb3BlcnR5ICd0eXBlJ1xuICAgIGZ1bmN0aW9uIGxhYmVsTm9kZVdpdGhUeXBlKG5vZGUpIHtcbiAgICAgICAgaWYgKG5vZGUgJiYgbm9kZS5oYXNPd25Qcm9wZXJ0eSgndHlwZScpKSB7XG4gICAgICAgICAgICBhc3NpZ25JZChub2RlKTtcbiAgICAgICAgfVxuICAgICAgICBpZiAobm9kZSAmJiB0eXBlb2Ygbm9kZSA9PT0gJ29iamVjdCcpIHtcbiAgICAgICAgICAgIGZvciAodmFyIHAgaW4gbm9kZSkge1xuICAgICAgICAgICAgICAgIGxhYmVsTm9kZVdpdGhUeXBlKG5vZGVbcF0pO1xuICAgICAgICAgICAgfVxuICAgICAgICB9XG4gICAgfVxuXG4gICAgbGFiZWxOb2RlV2l0aFR5cGUoYXN0KTtcblxuICAgIHJldHVybiBub2RlTGlzdDtcbn1cblxuZnVuY3Rpb24gc2hvd1VuZm9sZGVkKG9iaikge1xuICAgIGNvbnNvbGUubG9nKHV0aWwuaW5zcGVjdChvYmosIHtkZXB0aDogbnVsbH0pKTtcbn1cblxuZXhwb3J0cy5nZXROb2RlTGlzdCA9IGdldE5vZGVMaXN0O1xuZXhwb3J0cy5zaG93VW5mb2xkZWQgPSBzaG93VW5mb2xkZWQ7XG4iLCIndXNlIHN0cmljdCc7XG5cbmNvbnN0IHR5cGVzID0gcmVxdWlyZSgnLi4vZG9tYWlucy90eXBlcycpO1xuY29uc3Qgd2FsayA9IHJlcXVpcmUoJ2Fjb3JuL2Rpc3Qvd2FsaycpO1xuY29uc3Qgc3RhdHVzID0gcmVxdWlyZSgnLi4vZG9tYWlucy9zdGF0dXMnKTtcbmNvbnN0IGNzdHIgPSByZXF1aXJlKCcuL2NvbnN0cmFpbnRzJyk7XG5cbi8vIGFyZ3VtZW50cyBhcmUgXCIgb2xkU3RhdHVzICgsIG5hbWUsIHZhbCkqIFwiXG5mdW5jdGlvbiBjaGFuZ2VkU3RhdHVzKG9sZFN0YXR1cykge1xuICAgIGNvbnN0IG5ld1N0YXR1cyA9IG5ldyBzdGF0dXMuU3RhdHVzO1xuICAgIGZvciAobGV0IGkgPSAxOyBpIDwgYXJndW1lbnRzLmxlbmd0aDsgaSA9IGkgKyAyKVxuICAgICAgICBuZXdTdGF0dXNbYXJndW1lbnRzW2ldXSA9IGFyZ3VtZW50c1tpKzFdO1xuXG4gICAgZm9yIChsZXQgcCBpbiBvbGRTdGF0dXMpIHtcbiAgICAgICAgaWYgKG5ld1N0YXR1c1twXSA9PT0gdW5kZWZpbmVkKVxuICAgICAgICAgICAgbmV3U3RhdHVzW3BdID0gb2xkU3RhdHVzW3BdO1xuICAgIH1cbiAgICByZXR1cm4gbmV3U3RhdHVzO1xufVxuXG4vLyByZXR1cm5zIFthY2Nlc3MgdHlwZSwgcHJvcCB2YWx1ZV1cbmZ1bmN0aW9uIHByb3BBY2Nlc3Mobm9kZSkge1xuICAgIGNvbnN0IHByb3AgPSBub2RlLnByb3BlcnR5O1xuICAgIGlmICghbm9kZS5jb21wdXRlZCkge1xuICAgICAgICByZXR1cm4gWydkb3RBY2Nlc3MnLCBwcm9wLm5hbWVdO1xuICAgIH1cbiAgICBpZiAocHJvcC50eXBlID09PSAnTGl0ZXJhbCcpIHtcbiAgICAgICAgaWYgKHR5cGVvZiBwcm9wLnZhbHVlID09PSAnc3RyaW5nJylcbiAgICAgICAgICAgIHJldHVybiBbJ3N0cmluZ0xpdGVyYWwnLCBwcm9wLnZhbHVlXTtcbiAgICAgICAgaWYgKHR5cGVvZiBwcm9wLnZhbHVlID09PSAnbnVtYmVyJylcbiAgICAgICAgICAgIC8vIGNvbnZlcnQgbnVtYmVyIHRvIHN0cmluZ1xuICAgICAgICAgICAgcmV0dXJuIFsnbnVtYmVyTGl0ZXJhbCcsIHByb3AudmFsdWUgKyAnJ107XG4gICAgfVxuICAgIHJldHVybiBbXCJjb21wdXRlZFwiLCBudWxsXTtcbn1cblxuZnVuY3Rpb24gdW5vcFJlc3VsdFR5cGUob3ApIHtcbiAgICBzd2l0Y2ggKG9wKSB7XG4gICAgICAgIGNhc2UgJysnOiBjYXNlICctJzogY2FzZSAnfic6XG4gICAgICAgICAgICByZXR1cm4gdHlwZXMuUHJpbU51bWJlcjtcbiAgICAgICAgY2FzZSAnISc6XG4gICAgICAgICAgICByZXR1cm4gdHlwZXMuUHJpbUJvb2xlYW47XG4gICAgICAgIGNhc2UgJ3R5cGVvZic6XG4gICAgICAgICAgICByZXR1cm4gdHlwZXMuUHJpbVN0cmluZztcbiAgICAgICAgY2FzZSAndm9pZCc6IGNhc2UgJ2RlbGV0ZSc6XG4gICAgICAgICAgICByZXR1cm4gbnVsbDtcbiAgICB9XG59XG5cbmZ1bmN0aW9uIGJpbm9wSXNCb29sZWFuKG9wKSB7XG4gICAgc3dpdGNoIChvcCkge1xuICAgICAgICBjYXNlICc9PSc6IGNhc2UgJyE9JzogY2FzZSAnPT09JzogY2FzZSAnIT09JzpcbiAgICAgICAgY2FzZSAnPCc6IGNhc2UgJz4nOiBjYXNlICc+PSc6IGNhc2UgJzw9JzpcbiAgICAgICAgY2FzZSAnaW4nOiBjYXNlICdpbnN0YW5jZW9mJzpcbiAgICAgICAgICAgIHJldHVybiB0cnVlO1xuICAgIH1cbiAgICByZXR1cm4gZmFsc2U7XG59XG5cbmZ1bmN0aW9uIHJlYWRNZW1iZXIobm9kZSwgY3VyU3RhdHVzLCBjKSB7XG4gICAgY29uc3QgcmV0ID0gbmV3IHR5cGVzLkFWYWw7XG4gICAgY29uc3Qgb2JqQVZhbCA9IGMobm9kZS5vYmplY3QsIGN1clN0YXR1cywgdW5kZWZpbmVkKTtcbiAgICBpZiAobm9kZS5wcm9wZXJ0eS50eXBlICE9PSAnSWRlbnRpZmllcicpIHtcbiAgICAgICAgLy8gcmV0dXJuIGZyb20gcHJvcGVydHkgaXMgaWdub3JlZFxuICAgICAgICBjKG5vZGUucHJvcGVydHksIGN1clN0YXR1cywgdW5kZWZpbmVkKTtcbiAgICB9XG4gICAgY29uc3QgcHJvcEFjYyA9IHByb3BBY2Nlc3Mobm9kZSk7XG5cbiAgICBjb25zdHJhaW50cy5wdXNoKHtPQko6IG9iakFWYWwsXG4gICAgICAgICAgICAgICAgICAgICAgUFJPUDogcHJvcEFjY1sxXSxcbiAgICAgICAgICAgICAgICAgICAgICBSRUFEX1RPOiByZXR9KTtcbiAgICBvYmpBVmFsLnByb3BhZ2F0ZShuZXcgY3N0ci5SZWFkUHJvcChwcm9wQWNjWzFdLCByZXQpKTtcblxuICAgIC8vIHJldHVybnMgQVZhbCBmb3IgcmVjZWl2ZXIgYW5kIHJlYWQgbWVtYmVyXG4gICAgcmV0dXJuIFtvYmpBVmFsLCByZXRdO1xufVxuLy8gVG8gcHJldmVudCByZWN1cnNpb24sXG4vLyB3ZSByZW1lbWJlciB0aGUgc3RhdHVzIHVzZWQgaW4gYWRkQ29uc3RyYWludHNcbmNvbnN0IHZpc2l0ZWRTdGF0dXMgPSBbXTtcbmNvbnN0IGNvbnN0cmFpbnRzID0gW107XG5mdW5jdGlvbiBjbGVhckNvbnN0cmFpbnRzKCkge1xuICAgIHZpc2l0ZWRTdGF0dXMubGVuZ3RoID0gMDtcbiAgICBjb25zdHJhaW50cy5sZW5ndGggPSAwO1xufVxuXG5sZXQgcnRDWDtcbmZ1bmN0aW9uIGFkZENvbnN0cmFpbnRzKGFzdCwgaW5pdFN0YXR1cywgbmV3UnRDWCkge1xuXG4gICAgLy8gc2V0IHJ0Q1hcbiAgICBydENYID0gbmV3UnRDWCB8fCBydENYO1xuXG4gICAgLy8gQ2hlY2sgd2hldGhlciB3ZSBoYXZlIHByb2Nlc3NlZCAnaW5pdFN0YXR1cycgYmVmb3JlXG4gICAgZm9yIChsZXQgaT0wOyBpIDwgdmlzaXRlZFN0YXR1cy5sZW5ndGg7IGkrKykge1xuICAgICAgICBpZiAoaW5pdFN0YXR1cy5lcXVhbHModmlzaXRlZFN0YXR1c1tpXSkpIHtcbiAgICAgICAgICAgICAvLyBJZiBzbywgZG8gbm90aGluZ1xuICAgICAgICAgICAgIC8vIHNpZ25pZnlpbmcgd2UgZGlkbid0IGFkZCBjb25zdHJhaW50c1xuICAgICAgICAgICAgIHJldHVybiBmYWxzZTtcbiAgICAgICAgIH1cbiAgICB9XG4gICAgLy8gSWYgdGhlIGluaXRTdGF0dXMgaXMgbmV3LCBwdXNoIGl0LlxuICAgIC8vIFdlIGRvIG5vdCByZWNvcmQgYXN0IHNpbmNlIGFzdCBub2RlIGRlcGVuZHMgb24gdGhlIHN0YXR1c1xuICAgIHZpc2l0ZWRTdGF0dXMucHVzaChpbml0U3RhdHVzKTtcblxuICAgIC8vIGNvbnN0cmFpbnQgZ2VuZXJhdGluZyB3YWxrZXIgZm9yIGV4cHJlc3Npb25zXG4gICAgY29uc3QgY29uc3RyYWludEdlbmVyYXRvciA9IHdhbGsubWFrZSh7XG5cbiAgICAgICAgSWRlbnRpZmllcjogZnVuY3Rpb24gKG5vZGUsIGN1clN0YXR1cywgYykge1xuICAgICAgICAgICAgcmV0dXJuIGN1clN0YXR1cy5zYy5nZXRBVmFsT2Yobm9kZS5uYW1lKTtcbiAgICAgICAgfSxcblxuICAgICAgICBUaGlzRXhwcmVzc2lvbjogZnVuY3Rpb24gKG5vZGUsIGN1clN0YXR1cywgYykge1xuICAgICAgICAgICAgcmV0dXJuIGN1clN0YXR1cy5zZWxmO1xuICAgICAgICB9LFxuXG4gICAgICAgIExpdGVyYWw6IGZ1bmN0aW9uIChub2RlLCBjdXJTdGF0dXMsIGMpIHtcbiAgICAgICAgICAgIGNvbnN0IHJlcyA9IG5ldyB0eXBlcy5BVmFsO1xuICAgICAgICAgICAgaWYgKG5vZGUucmVnZXgpIHtcbiAgICAgICAgICAgICAgICAvLyBub3QgaW1wbGVtZW50ZWQgeWV0XG4gICAgICAgICAgICAgICAgLy8gdGhyb3cgbmV3IEVycm9yKCdyZWdleCBsaXRlcmFsIGlzIG5vdCBpbXBsZW1lbnRlZCB5ZXQnKTtcbiAgICAgICAgICAgICAgICByZXR1cm4gcmVzO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgc3dpdGNoICh0eXBlb2Ygbm9kZS52YWx1ZSkge1xuICAgICAgICAgICAgY2FzZSAnbnVtYmVyJzpcbiAgICAgICAgICAgICAgICBjb25zdHJhaW50cy5wdXNoKHtUWVBFOiB0eXBlcy5QcmltTnVtYmVyLFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIElOQ0xfU0VUOiByZXN9KTtcbiAgICAgICAgICAgICAgICByZXMuYWRkVHlwZSh0eXBlcy5QcmltTnVtYmVyKTtcbiAgICAgICAgICAgICAgICBicmVhaztcbiAgICAgICAgICAgIGNhc2UgJ3N0cmluZyc6XG4gICAgICAgICAgICAgICAgY29uc3RyYWludHMucHVzaCh7VFlQRTogdHlwZXMuUHJpbVN0cmluZyxcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBJTkNMX1NFVDogcmVzfSk7XG4gICAgICAgICAgICAgICAgcmVzLmFkZFR5cGUodHlwZXMuUHJpbVN0cmluZyk7XG4gICAgICAgICAgICAgICAgYnJlYWs7XG4gICAgICAgICAgICBjYXNlICdib29sZWFuJzpcbiAgICAgICAgICAgICAgICBjb25zdHJhaW50cy5wdXNoKHtUWVBFOiB0eXBlcy5QcmltQm9vbGVhbixcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBJTkNMX1NFVDogcmVzfSk7XG4gICAgICAgICAgICAgICAgcmVzLmFkZFR5cGUodHlwZXMuUHJpbUJvb2xlYW4pO1xuICAgICAgICAgICAgICAgIGJyZWFrO1xuICAgICAgICAgICAgY2FzZSAnb2JqZWN0JzpcbiAgICAgICAgICAgICAgICAvLyBJIGd1ZXNzOiBMaXRlcmFsICYmIG9iamVjdCA9PT4gbm9kZS52YWx1ZSA9PSBudWxsXG4gICAgICAgICAgICAgICAgLy8gbnVsbCBpcyBpZ25vcmVkLCBzbyBub3RoaW5nIHRvIGFkZFxuICAgICAgICAgICAgICAgIGJyZWFrO1xuICAgICAgICAgICAgY2FzZSAnZnVuY3Rpb24nOlxuICAgICAgICAgICAgICAgIHRocm93IG5ldyBFcnJvcignSSBndWVzcyBmdW5jdGlvbiBpcyBpbXBvc3NpYmxlIGhlcmUuJyk7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICByZXR1cm4gcmVzO1xuICAgICAgICB9LFxuXG4gICAgICAgIEFzc2lnbm1lbnRFeHByZXNzaW9uOiBmdW5jdGlvbiAobm9kZSwgY3VyU3RhdHVzLCBjKSB7XG4gICAgICAgICAgICBjb25zdCByaHNBVmFsID0gYyhub2RlLnJpZ2h0LCBjdXJTdGF0dXMsIHVuZGVmaW5lZCk7XG4gICAgICAgICAgICBpZiAobm9kZS5sZWZ0LnR5cGUgIT09ICdNZW1iZXJFeHByZXNzaW9uJykge1xuICAgICAgICAgICAgICAgIC8vIExIUyBpcyBhIHNpbXBsZSB2YXJpYWJsZS5cbiAgICAgICAgICAgICAgICBjb25zdCB2YXJOYW1lID0gbm9kZS5sZWZ0Lm5hbWU7XG4gICAgICAgICAgICAgICAgY29uc3QgbGhzQVZhbCA9IGN1clN0YXR1cy5zYy5nZXRBVmFsT2YodmFyTmFtZSk7XG5cbiAgICAgICAgICAgICAgICBpZiAobm9kZS5vcGVyYXRvciA9PT0gJz0nKSB7XG4gICAgICAgICAgICAgICAgICAgIC8vIHNpbXBsZSBhc3NpZ25tZW50XG4gICAgICAgICAgICAgICAgICAgIGNvbnN0cmFpbnRzLnB1c2goe1xuICAgICAgICAgICAgICAgICAgICAgICAgRlJPTTogcmhzQVZhbCxcbiAgICAgICAgICAgICAgICAgICAgICAgIFRPOiBsaHNBVmFsXG4gICAgICAgICAgICAgICAgICAgIH0pO1xuICAgICAgICAgICAgICAgICAgICByaHNBVmFsLnByb3BhZ2F0ZShsaHNBVmFsKTtcbiAgICAgICAgICAgICAgICAgICAgLy8gY29ycmVzcG9uZGluZyBBVmFsIGlzIHRoZSBSSFNcbiAgICAgICAgICAgICAgICAgICAgcmV0dXJuIHJoc0FWYWw7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIGNvbnN0IHJlc0FWYWwgPSBuZXcgdHlwZXMuQVZhbDtcbiAgICAgICAgICAgICAgICBpZiAobm9kZS5vcGVyYXRvciA9PT0gJys9Jykge1xuICAgICAgICAgICAgICAgICAgICAvLyBjb25jYXRlbmF0aW5nIHVwZGF0ZVxuICAgICAgICAgICAgICAgICAgICBjb25zdHJhaW50cy5wdXNoKHtcbiAgICAgICAgICAgICAgICAgICAgICAgIEFERF9PUFJEMTogbGhzQVZhbCxcbiAgICAgICAgICAgICAgICAgICAgICAgIEFERF9PUFJEMjogcmhzQVZhbCxcbiAgICAgICAgICAgICAgICAgICAgICAgIFJFU1VMVDogcmVzQVZhbFxuICAgICAgICAgICAgICAgICAgICB9KTtcbiAgICAgICAgICAgICAgICAgICAgbGhzQVZhbC5wcm9wYWdhdGUobmV3IGNzdHIuSXNBZGRlZChyaHNBVmFsLCByZXNBVmFsKSk7XG4gICAgICAgICAgICAgICAgICAgIHJoc0FWYWwucHJvcGFnYXRlKG5ldyBjc3RyLklzQWRkZWQobGhzQVZhbCwgcmVzQVZhbCkpO1xuICAgICAgICAgICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgICAgICAgICAgIC8vIGFyaXRobWV0aWMgdXBkYXRlXG4gICAgICAgICAgICAgICAgICAgIGNvbnN0cmFpbnRzLnB1c2goe1xuICAgICAgICAgICAgICAgICAgICAgICAgVFlQRTp0eXBlcy5QcmltTnVtYmVyLFxuICAgICAgICAgICAgICAgICAgICAgICAgSU5DTF9TRVQ6IHJlc0FWYWxcbiAgICAgICAgICAgICAgICAgICAgfSk7XG4gICAgICAgICAgICAgICAgICAgIHJlc0FWYWwuYWRkVHlwZSh0eXBlcy5QcmltTnVtYmVyKTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgcmV0dXJuIHJlc0FWYWw7XG4gICAgICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgICAgICAgIC8vIG1lbWJlciBhc3NpZ25tZW50XG4gICAgICAgICAgICAgICAgY29uc3Qgb2JqQVZhbCA9IGMobm9kZS5sZWZ0Lm9iamVjdCwgY3VyU3RhdHVzLCB1bmRlZmluZWQpO1xuICAgICAgICAgICAgICAgIGNvbnN0IHByb3BBY2MgPSBwcm9wQWNjZXNzKG5vZGUubGVmdCk7XG4gICAgICAgICAgICAgICAgaWYgKG5vZGUub3BlcmF0b3IgPT09ICc9Jykge1xuICAgICAgICAgICAgICAgICAgICAvLyBhc3NpZ25tZW50IHRvIG1lbWJlclxuICAgICAgICAgICAgICAgICAgICBjb25zdHJhaW50cy5wdXNoKHtcbiAgICAgICAgICAgICAgICAgICAgICAgIE9CSjogb2JqQVZhbCxcbiAgICAgICAgICAgICAgICAgICAgICAgIFBST1A6IHByb3BBY2NbMV0sXG4gICAgICAgICAgICAgICAgICAgICAgICBXUklURV9XSVRIOiByaHNBVmFsXG4gICAgICAgICAgICAgICAgICAgIH0pO1xuICAgICAgICAgICAgICAgICAgICBvYmpBVmFsLnByb3BhZ2F0ZShuZXcgY3N0ci5Xcml0ZVByb3AocHJvcEFjY1sxXSwgcmhzQVZhbCkpO1xuICAgICAgICAgICAgICAgICAgICAvLyBpZiBwcm9wZXJ0eSBpcyBudW1iZXIgbGl0ZXJhbCwgYWxzbyB3cml0ZSB0byAndW5rbm93bidcbiAgICAgICAgICAgICAgICAgICAgaWYgKHByb3BBY2NbMF0gPT09ICdudW1iZXJMaXRlcmFsJykge1xuICAgICAgICAgICAgICAgICAgICAgICAgb2JqQVZhbC5wcm9wYWdhdGUobmV3IGNzdHIuV3JpdGVQcm9wKG51bGwsIHJoc0FWYWwpKTtcbiAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICByZXR1cm4gcmhzQVZhbDtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgY29uc3QgcmVzQVZhbCA9IG5ldyB0eXBlcy5BVmFsO1xuICAgICAgICAgICAgICAgIGNvbnN0IHJlY3ZBbmRSZXQgPSByZWFkTWVtYmVyKG5vZGUubGVmdCwgY3VyU3RhdHVzLCBjKTtcbiAgICAgICAgICAgICAgICBpZiAobm9kZS5vcGVyYXRvciA9PT0gJys9Jykge1xuICAgICAgICAgICAgICAgICAgICAvLyBjb25jYXRlbmF0aW5nIHVwZGF0ZVxuICAgICAgICAgICAgICAgICAgICBjb25zdHJhaW50cy5wdXNoKHtcbiAgICAgICAgICAgICAgICAgICAgICAgIEFERF9PUFJEMTogcmVjdkFuZFJldFsxXSxcbiAgICAgICAgICAgICAgICAgICAgICAgIEFERF9PUFJEMjogcmhzQVZhbCxcbiAgICAgICAgICAgICAgICAgICAgICAgIFJFU1VMVDogcmVzQVZhbFxuICAgICAgICAgICAgICAgICAgICB9KTtcbiAgICAgICAgICAgICAgICAgICAgcmVjdkFuZFJldFsxXS5wcm9wYWdhdGUobmV3IGNzdHIuSXNBZGRlZChyaHNBVmFsLCByZXNBVmFsKSk7XG4gICAgICAgICAgICAgICAgICAgIHJoc0FWYWwucHJvcGFnYXRlKG5ldyBjc3RyLklzQWRkZWQocmVjdkFuZFJldFsxXSwgcmVzQVZhbCkpO1xuICAgICAgICAgICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgICAgICAgICAgIC8vIGFyaXRobWV0aWMgdXBkYXRlXG4gICAgICAgICAgICAgICAgICAgIGNvbnN0cmFpbnRzLnB1c2goe1xuICAgICAgICAgICAgICAgICAgICAgICAgVFlQRTogdHlwZXMuUHJpbU51bWJlcixcbiAgICAgICAgICAgICAgICAgICAgICAgIElOQ0xfU0VUOiByZXNBVmFsXG4gICAgICAgICAgICAgICAgICAgIH0pO1xuICAgICAgICAgICAgICAgICAgICByZXNBVmFsLmFkZFR5cGUodHlwZXMuUHJpbU51bWJlcik7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIHJldHVybiByZXNBVmFsO1xuICAgICAgICAgICAgfVxuICAgICAgICB9LFxuXG4gICAgICAgIFZhcmlhYmxlRGVjbGFyYXRpb246IGZ1bmN0aW9uIChub2RlLCBjdXJTdGF0dXMsIGMpIHtcbiAgICAgICAgICAgIGZvciAobGV0IGkgPSAwOyBpIDwgbm9kZS5kZWNsYXJhdGlvbnMubGVuZ3RoOyBpKyspIHtcbiAgICAgICAgICAgICAgICBjb25zdCBkZWNsID0gbm9kZS5kZWNsYXJhdGlvbnNbaV07XG4gICAgICAgICAgICAgICAgaWYgKGRlY2wuaW5pdCkge1xuICAgICAgICAgICAgICAgICAgICBjb25zdCBsaHNBVmFsID0gY3VyU3RhdHVzLnNjLmdldEFWYWxPZihkZWNsLmlkLm5hbWUpO1xuICAgICAgICAgICAgICAgICAgICBjb25zdCByaHNBVmFsID0gYyhkZWNsLmluaXQsIGN1clN0YXR1cywgdW5kZWZpbmVkKTtcbiAgICAgICAgICAgICAgICAgICAgY29uc3RyYWludHMucHVzaCh7RlJPTTogcmhzQVZhbCxcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgVE86IGxoc0FWYWx9KTtcbiAgICAgICAgICAgICAgICAgICAgcmhzQVZhbC5wcm9wYWdhdGUobGhzQVZhbCk7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgfVxuICAgICAgICB9LFxuXG4gICAgICAgIExvZ2ljYWxFeHByZXNzaW9uOiBmdW5jdGlvbiAobm9kZSwgY3VyU3RhdHVzLCBjKSB7XG4gICAgICAgICAgICBjb25zdCByZXMgPSBuZXcgdHlwZXMuQVZhbDtcbiAgICAgICAgICAgIGNvbnN0IGxlZnQgPSBjKG5vZGUubGVmdCwgY3VyU3RhdHVzLCB1bmRlZmluZWQpO1xuICAgICAgICAgICAgY29uc3QgcmlnaHQgPSBjKG5vZGUucmlnaHQsIGN1clN0YXR1cywgdW5kZWZpbmVkKTtcbiAgICAgICAgICAgIGNvbnN0cmFpbnRzLnB1c2goe0ZST006IGxlZnQsIFRPOiByZXN9LFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICB7RlJPTTogcmlnaHQsIFRPOiByZXN9KTtcbiAgICAgICAgICAgIGxlZnQucHJvcGFnYXRlKHJlcyk7XG4gICAgICAgICAgICByaWdodC5wcm9wYWdhdGUocmVzKTtcbiAgICAgICAgICAgIHJldHVybiByZXM7XG4gICAgICAgIH0sXG5cbiAgICAgICAgQ29uZGl0aW9uYWxFeHByZXNzaW9uOiBmdW5jdGlvbiAobm9kZSwgY3VyU3RhdHVzLCBjKSB7XG4gICAgICAgICAgICBjb25zdCByZXMgPSBuZXcgdHlwZXMuQVZhbDtcbiAgICAgICAgICAgIGMobm9kZS50ZXN0LCBjdXJTdGF0dXMsIHVuZGVmaW5lZCk7XG4gICAgICAgICAgICBjb25zdCBjb25zID0gYyhub2RlLmNvbnNlcXVlbnQsIGN1clN0YXR1cywgdW5kZWZpbmVkKTtcbiAgICAgICAgICAgIGNvbnN0IGFsdCA9IGMobm9kZS5hbHRlcm5hdGUsIGN1clN0YXR1cywgdW5kZWZpbmVkKTtcbiAgICAgICAgICAgIGNvbnN0cmFpbnRzLnB1c2goe0ZST006IGNvbnMsIFRPOiByZXN9LFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICB7RlJPTTogYWx0LCBUTzogcmVzfSk7XG4gICAgICAgICAgICBjb25zLnByb3BhZ2F0ZShyZXMpO1xuICAgICAgICAgICAgYWx0LnByb3BhZ2F0ZShyZXMpO1xuICAgICAgICAgICAgcmV0dXJuIHJlcztcbiAgICAgICAgfSxcblxuICAgICAgICBOZXdFeHByZXNzaW9uOiBmdW5jdGlvbiAobm9kZSwgY3VyU3RhdHVzLCBjKSB7XG4gICAgICAgICAgICBjb25zdCByZXQgPSBuZXcgdHlwZXMuQVZhbDtcbiAgICAgICAgICAgIGNvbnN0IGNhbGxlZSA9IGMobm9kZS5jYWxsZWUsIGN1clN0YXR1cywgdW5kZWZpbmVkKTtcbiAgICAgICAgICAgIGNvbnN0IGFyZ3MgPSBbXTtcbiAgICAgICAgICAgIGZvciAobGV0IGkgPSAwOyBpIDwgbm9kZS5hcmd1bWVudHMubGVuZ3RoOyBpKyspIHtcbiAgICAgICAgICAgICAgICBhcmdzLnB1c2goYyhub2RlLmFyZ3VtZW50c1tpXSwgY3VyU3RhdHVzLCB1bmRlZmluZWQpKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGNvbnN0IG5ld0RlbHRhID0gY3VyU3RhdHVzLmRlbHRhLmFwcGVuZE9uZShub2RlWydAbGFiZWwnXSk7XG4gICAgICAgICAgICBjb25zdHJhaW50cy5wdXNoKHtDT05TVFJVQ1RPUjogY2FsbGVlLFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgQVJHUzogYXJncyxcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIFJFVDogcmV0LFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgRVhDOiBjdXJTdGF0dXMuZXhjLFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgREVMVEE6IG5ld0RlbHRhfSk7XG4gICAgICAgICAgICBjYWxsZWUucHJvcGFnYXRlKFxuICAgICAgICAgICAgICAgIG5ldyBjc3RyLklzQ3RvcihcbiAgICAgICAgICAgICAgICAgICAgYXJncyxcbiAgICAgICAgICAgICAgICAgICAgcmV0LFxuICAgICAgICAgICAgICAgICAgICBjdXJTdGF0dXMuZXhjLFxuICAgICAgICAgICAgICAgICAgICBuZXdEZWx0YSkpO1xuICAgICAgICAgICAgcmV0dXJuIHJldDtcbiAgICAgICAgfSxcblxuICAgICAgICBBcnJheUV4cHJlc3Npb246IGZ1bmN0aW9uIChub2RlLCBjdXJTdGF0dXMsIGMpIHtcbiAgICAgICAgICAgIGNvbnN0IHJldCA9IG5ldyB0eXBlcy5BVmFsO1xuICAgICAgICAgICAgY29uc3QgYXJyVHlwZSA9IG5ldyB0eXBlcy5BcnJUeXBlKG5ldyB0eXBlcy5BVmFsKHJ0Q1gucHJvdG9zLkFycmF5KSk7XG4gICAgICAgICAgICAvLyBhZGQgbGVuZ3RoIHByb3BlcnR5XG4gICAgICAgICAgICBhcnJUeXBlLmdldFByb3AoJ2xlbmd0aCcpLmFkZFR5cGUodHlwZXMuUHJpbU51bWJlcik7XG5cbiAgICAgICAgICAgIGNvbnN0cmFpbnRzLnB1c2goe1RZUEU6IGFyclR5cGUsIElOQ0xfU0VUOiByZXR9KTtcbiAgICAgICAgICAgIHJldC5hZGRUeXBlKGFyclR5cGUpO1xuXG4gICAgICAgICAgICAvLyBhZGQgYXJyYXkgZWxlbWVudHNcbiAgICAgICAgICAgIGZvciAobGV0IGkgPSAwOyBpIDwgbm9kZS5lbGVtZW50cy5sZW5ndGg7IGkrKykge1xuICAgICAgICAgICAgICAgIGNvbnN0IGVsdEFWYWwgPSBjKG5vZGUuZWxlbWVudHNbaV0sIGN1clN0YXR1cywgdW5kZWZpbmVkKTtcblxuICAgICAgICAgICAgICAgIGNvbnN0IHByb3AgPSBpICsgJyc7XG4gICAgICAgICAgICAgICAgY29uc3RyYWludHMucHVzaCh7T0JKOiByZXQsIFBST1A6IHByb3AsIEFWQUw6IGVsdEFWYWx9KTtcbiAgICAgICAgICAgICAgICBjb25zdHJhaW50cy5wdXNoKHtPQko6IHJldCwgUFJPUDogbnVsbCwgQVZBTDogZWx0QVZhbH0pO1xuICAgICAgICAgICAgICAgIHJldC5wcm9wYWdhdGUobmV3IGNzdHIuV3JpdGVQcm9wKHByb3AsIGVsdEFWYWwpKTtcbiAgICAgICAgICAgICAgICByZXQucHJvcGFnYXRlKG5ldyBjc3RyLldyaXRlUHJvcChudWxsLCBlbHRBVmFsKSk7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICByZXR1cm4gcmV0O1xuICAgICAgICB9LFxuXG4gICAgICAgIE9iamVjdEV4cHJlc3Npb246IGZ1bmN0aW9uIChub2RlLCBjdXJTdGF0dXMsIGMpIHtcbiAgICAgICAgICAgIGNvbnN0IHJldCA9IG5ldyB0eXBlcy5BVmFsO1xuICAgICAgICAgICAgY29uc3Qgb2JqVHlwZSA9IG5ldyB0eXBlcy5PYmpUeXBlKG5ldyB0eXBlcy5BVmFsKHJ0Q1gucHJvdG9zLk9iamVjdCkpO1xuICAgICAgICAgICAgY29uc3RyYWludHMucHVzaCh7VFlQRTogb2JqVHlwZSwgSU5DTF9TRVQ6IHJldH0pO1xuICAgICAgICAgICAgcmV0LmFkZFR5cGUob2JqVHlwZSk7XG5cbiAgICAgICAgICAgIGZvciAobGV0IGkgPSAwOyBpIDwgbm9kZS5wcm9wZXJ0aWVzLmxlbmd0aDsgaSsrKSB7XG4gICAgICAgICAgICAgICAgY29uc3QgcHJvcFBhaXIgPSBub2RlLnByb3BlcnRpZXNbaV07XG4gICAgICAgICAgICAgICAgY29uc3QgcHJvcEtleSA9IHByb3BQYWlyLmtleTtcbiAgICAgICAgICAgICAgICBsZXQgbmFtZTtcbiAgICAgICAgICAgICAgICBjb25zdCBwcm9wRXhwciA9IHByb3BQYWlyLnZhbHVlO1xuXG4gICAgICAgICAgICAgICAgY29uc3QgZmxkQVZhbCA9IGMocHJvcEV4cHIsIGN1clN0YXR1cywgdW5kZWZpbmVkKTtcblxuICAgICAgICAgICAgICAgIGlmIChwcm9wS2V5LnR5cGUgPT09ICdJZGVudGlmaWVyJykge1xuICAgICAgICAgICAgICAgICAgICBuYW1lID0gcHJvcEtleS5uYW1lO1xuICAgICAgICAgICAgICAgIH0gZWxzZSBpZiAodHlwZW9mIHByb3BLZXkudmFsdWUgPT09ICdzdHJpbmcnKSB7XG4gICAgICAgICAgICAgICAgICAgIG5hbWUgPSBwcm9wS2V5LnZhbHVlO1xuICAgICAgICAgICAgICAgIH0gZWxzZSBpZiAodHlwZW9mIHByb3BLZXkudmFsdWUgPT09ICdudW1iZXInKSB7XG4gICAgICAgICAgICAgICAgICAgIC8vIGNvbnZlcnQgbnVtYmVyIHRvIHN0cmluZ1xuICAgICAgICAgICAgICAgICAgICBuYW1lID0gcHJvcEtleS52YWx1ZSArICcnO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICBjb25zdHJhaW50cy5wdXNoKHtPQko6IHJldCwgUFJPUDogbmFtZSwgQVZBTDogZmxkQVZhbH0pO1xuICAgICAgICAgICAgICAgIHJldC5wcm9wYWdhdGUobmV3IGNzdHIuV3JpdGVQcm9wKG5hbWUsIGZsZEFWYWwpKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIHJldHVybiByZXQ7XG4gICAgICAgIH0sXG5cbiAgICAgICAgRnVuY3Rpb25FeHByZXNzaW9uOiBmdW5jdGlvbiAobm9kZSwgY3VyU3RhdHVzLCBjKSB7XG4gICAgICAgICAgICBpZiAoIW5vZGUuZm5JbnN0YW5jZXMpIHtcbiAgICAgICAgICAgICAgICBub2RlLmZuSW5zdGFuY2VzID0gW107XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBsZXQgZm5JbnN0YW5jZSA9IG51bGw7XG4gICAgICAgICAgICBub2RlLmZuSW5zdGFuY2VzLmZvckVhY2goZnVuY3Rpb24gKGZuVHlwZSkge1xuICAgICAgICAgICAgICAgIGlmIChmblR5cGUuc2MgPT09IGN1clN0YXR1cy5zYykge1xuICAgICAgICAgICAgICAgICAgICBmbkluc3RhbmNlID0gZm5UeXBlO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgIH0pO1xuICAgICAgICAgICAgaWYgKCFmbkluc3RhbmNlKSB7XG4gICAgICAgICAgICAgICAgZm5JbnN0YW5jZVxuICAgICAgICAgICAgICAgICAgICA9IG5ldyB0eXBlcy5GblR5cGUobmV3IHR5cGVzLkFWYWwocnRDWC5wcm90b3MuRnVuY3Rpb24pLFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgJ1thbm9ueW1vdXMgZnVuY3Rpb25dJyxcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIG5vZGUuYm9keVsnQGJsb2NrJ10uZ2V0UGFyYW1WYXJOYW1lcygpLFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgY3VyU3RhdHVzLnNjLFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgbm9kZSxcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIHJ0Q1gucHJvdG9zLk9iamVjdCk7XG4gICAgICAgICAgICAgICAgbm9kZS5mbkluc3RhbmNlcy5wdXNoKGZuSW5zdGFuY2UpO1xuICAgICAgICAgICAgICAgIGNvbnN0IHByb3RvdHlwZU9iamVjdCA9XG4gICAgICAgICAgICAgICAgICAgIG5ldyB0eXBlcy5PYmpUeXBlKG5ldyB0eXBlcy5BVmFsKHJ0Q1gucHJvdG9zLk9iamVjdCksXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICc/LnByb3RvdHlwZScpO1xuICAgICAgICAgICAgICAgIC8vIEZvciAucHJvdG90eXBlXG4gICAgICAgICAgICAgICAgY29uc3QgcHJvdG90eXBlUHJvcCA9IGZuSW5zdGFuY2UuZ2V0UHJvcCgncHJvdG90eXBlJyk7XG4gICAgICAgICAgICAgICAgY29uc3RyYWludHMucHVzaCh7VFlQRTogcHJvdG90eXBlT2JqZWN0LFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIElOQ0xfU0VUOiBwcm90b3R5cGVQcm9wfSk7XG4gICAgICAgICAgICAgICAgcHJvdG90eXBlUHJvcC5hZGRUeXBlKHByb3RvdHlwZU9iamVjdCk7XG4gICAgICAgICAgICAgICAgLy8gRm9yIC5wcm90b3R5cGUuY29uc3RydWN0b3JcbiAgICAgICAgICAgICAgICBjb25zdCBjb25zdHJ1Y3RvclByb3AgPSBwcm90b3R5cGVPYmplY3QuZ2V0UHJvcCgnY29uc3RydWN0b3InKTtcbiAgICAgICAgICAgICAgICBjb25zdHJhaW50cy5wdXNoKHtUWVBFOiBmbkluc3RhbmNlLFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIElOQ0xfU0VUOiBjb25zdHJ1Y3RvclByb3B9KTtcbiAgICAgICAgICAgICAgICBjb25zdHJ1Y3RvclByb3AuYWRkVHlwZShmbkluc3RhbmNlKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGNvbnN0IHJldCA9IG5ldyB0eXBlcy5BVmFsO1xuICAgICAgICAgICAgY29uc3RyYWludHMucHVzaCh7VFlQRTogZm5JbnN0YW5jZSxcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIElOQ0xfU0VUOiByZXR9KTtcbiAgICAgICAgICAgIHJldC5hZGRUeXBlKGZuSW5zdGFuY2UpO1xuICAgICAgICAgICAgcmV0dXJuIHJldDtcbiAgICAgICAgfSxcblxuICAgICAgICBGdW5jdGlvbkRlY2xhcmF0aW9uOiBmdW5jdGlvbiAobm9kZSwgY3VyU3RhdHVzLCBjKSB7XG4gICAgICAgICAgICAvLyBEcm9wIGluaXRpYWwgY2F0Y2ggc2NvcGVzXG4gICAgICAgICAgICBjb25zdCBzYzAgPSBjdXJTdGF0dXMuc2MucmVtb3ZlSW5pdGlhbENhdGNoQmxvY2tzKCk7XG4gICAgICAgICAgICBpZiAoIW5vZGUuZm5JbnN0YW5jZXMpIHtcbiAgICAgICAgICAgICAgICBub2RlLmZuSW5zdGFuY2VzID0gW107XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBsZXQgZm5JbnN0YW5jZSA9IG51bGw7XG4gICAgICAgICAgICBub2RlLmZuSW5zdGFuY2VzLmZvckVhY2goZnVuY3Rpb24gKGZuVHlwZSkge1xuICAgICAgICAgICAgICAgIGlmIChmblR5cGUuc2MgPT09IHNjMCkge1xuICAgICAgICAgICAgICAgICAgICBmbkluc3RhbmNlID0gZm5UeXBlO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgIH0pO1xuICAgICAgICAgICAgaWYgKCFmbkluc3RhbmNlKSB7XG4gICAgICAgICAgICAgICAgZm5JbnN0YW5jZVxuICAgICAgICAgICAgICAgICAgICA9IG5ldyB0eXBlcy5GblR5cGUobmV3IHR5cGVzLkFWYWwocnRDWC5wcm90b3MuRnVuY3Rpb24pLFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgbm9kZS5pZC5uYW1lLFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgbm9kZS5ib2R5WydAYmxvY2snXS5nZXRQYXJhbVZhck5hbWVzKCksXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBzYzAsXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBub2RlLFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgcnRDWC5wcm90b3MuT2JqZWN0KTtcbiAgICAgICAgICAgICAgICBub2RlLmZuSW5zdGFuY2VzLnB1c2goZm5JbnN0YW5jZSk7XG4gICAgICAgICAgICAgICAgLy8gZm9yIGVhY2ggZm5JbnN0YW5jZSwgYXNzaWduIG9uZSBwcm90b3R5cGUgb2JqZWN0XG4gICAgICAgICAgICAgICAgY29uc3QgcHJvdG90eXBlT2JqZWN0ID1cbiAgICAgICAgICAgICAgICAgICAgbmV3IHR5cGVzLk9ialR5cGUobmV3IHR5cGVzLkFWYWwocnRDWC5wcm90b3MuT2JqZWN0KSxcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgbm9kZS5pZC5uYW1lICsgJy5wcm90b3R5cGUnKTtcbiAgICAgICAgICAgICAgICAvLyBGb3IgLnByb3RvdHlwZVxuICAgICAgICAgICAgICAgIGNvbnN0IHByb3RvdHlwZVByb3AgPSBmbkluc3RhbmNlLmdldFByb3AoJ3Byb3RvdHlwZScpO1xuICAgICAgICAgICAgICAgIGNvbnN0cmFpbnRzLnB1c2goe1RZUEU6IHByb3RvdHlwZU9iamVjdCxcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBJTkNMX1NFVDogcHJvdG90eXBlUHJvcH0pO1xuICAgICAgICAgICAgICAgIHByb3RvdHlwZVByb3AuYWRkVHlwZShwcm90b3R5cGVPYmplY3QpO1xuICAgICAgICAgICAgICAgIC8vIEZvciAucHJvdG90eXBlLmNvbnN0cnVjdG9yXG4gICAgICAgICAgICAgICAgY29uc3QgY29uc3RydWN0b3JQcm9wID0gcHJvdG90eXBlT2JqZWN0LmdldFByb3AoJ2NvbnN0cnVjdG9yJyk7XG4gICAgICAgICAgICAgICAgY29uc3RyYWludHMucHVzaCh7VFlQRTogZm5JbnN0YW5jZSxcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBJTkNMX1NFVDogY29uc3RydWN0b3JQcm9wfSk7XG4gICAgICAgICAgICAgICAgY29uc3RydWN0b3JQcm9wLmFkZFR5cGUoZm5JbnN0YW5jZSk7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBjb25zdCBsaHNBVmFsID0gc2MwLmdldEFWYWxPZihub2RlLmlkLm5hbWUpO1xuXG4gICAgICAgICAgICBjb25zdHJhaW50cy5wdXNoKHtUWVBFOiBmbkluc3RhbmNlLFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgSU5DTF9TRVQ6IGxoc0FWYWx9KTtcbiAgICAgICAgICAgIGxoc0FWYWwuYWRkVHlwZShmbkluc3RhbmNlKTtcbiAgICAgICAgICAgIC8vIG5vdGhpbmcgdG8gcmV0dXJuXG4gICAgICAgICAgICByZXR1cm4gdHlwZXMuQVZhbE51bGw7XG4gICAgICAgIH0sXG5cbiAgICAgICAgU2VxdWVuY2VFeHByZXNzaW9uOiBmdW5jdGlvbiAobm9kZSwgY3VyU3RhdHVzLCBjKSB7XG4gICAgICAgICAgICBjb25zdCBsYXN0SW5kZXggPSBub2RlLmV4cHJlc3Npb25zLmxlbmd0aCAtIDE7XG4gICAgICAgICAgICBmb3IgKGxldCBpID0gMDsgaSA8IGxhc3RJbmRleDsgaSsrKSB7XG4gICAgICAgICAgICAgICAgYyhub2RlLmV4cHJlc3Npb25zW2ldLCBjdXJTdGF0dXMsIHVuZGVmaW5lZCk7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICByZXR1cm4gYyhub2RlLmV4cHJlc3Npb25zW2xhc3RJbmRleF0sIGN1clN0YXR1cywgdW5kZWZpbmVkKTtcbiAgICAgICAgfSxcblxuICAgICAgICBVbmFyeUV4cHJlc3Npb246IGZ1bmN0aW9uIChub2RlLCBjdXJTdGF0dXMsIGMpIHtcbiAgICAgICAgICAgIGMobm9kZS5hcmd1bWVudCwgY3VyU3RhdHVzLCB1bmRlZmluZWQpO1xuICAgICAgICAgICAgY29uc3QgcmVzID0gbmV3IHR5cGVzLkFWYWw7XG4gICAgICAgICAgICBjb25zdCB0eXBlID0gdW5vcFJlc3VsdFR5cGUobm9kZS5vcGVyYXRvcik7XG4gICAgICAgICAgICBpZiAodHlwZSkge1xuICAgICAgICAgICAgICAgIGNvbnN0cmFpbnRzLnB1c2goe1RZUEU6IHR5cGUsXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgSU5DTF9TRVQ6IHJlc30pO1xuICAgICAgICAgICAgICAgIHJlcy5hZGRUeXBlKHR5cGUpO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgcmV0dXJuIHJlcztcbiAgICAgICAgfSxcblxuICAgICAgICBVcGRhdGVFeHByZXNzaW9uOiBmdW5jdGlvbiAobm9kZSwgY3VyU3RhdHVzLCBjKSB7XG4gICAgICAgICAgICBjKG5vZGUuYXJndW1lbnQsIGN1clN0YXR1cywgdW5kZWZpbmVkKTtcbiAgICAgICAgICAgIGNvbnN0IHJlcyA9IG5ldyB0eXBlcy5BVmFsO1xuICAgICAgICAgICAgY29uc3RyYWludHMucHVzaCh7VFlQRTogdHlwZXMuUHJpbU51bWJlcixcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIElOQ0xfU0VUOiByZXN9KTtcbiAgICAgICAgICAgIHJlcy5hZGRUeXBlKHR5cGVzLlByaW1OdW1iZXIpO1xuICAgICAgICAgICAgLy8gV2UgaWdub3JlIHRoZSBlZmZlY3Qgb2YgdXBkYXRpbmcgdG8gbnVtYmVyIHR5cGVcbiAgICAgICAgICAgIHJldHVybiByZXM7XG4gICAgICAgIH0sXG5cbiAgICAgICAgQmluYXJ5RXhwcmVzc2lvbjogZnVuY3Rpb24gKG5vZGUsIGN1clN0YXR1cywgYykge1xuICAgICAgICAgICAgY29uc3QgbE9wcmQgPSBjKG5vZGUubGVmdCwgY3VyU3RhdHVzLCB1bmRlZmluZWQpO1xuICAgICAgICAgICAgY29uc3Qgck9wcmQgPSBjKG5vZGUucmlnaHQsIGN1clN0YXR1cywgdW5kZWZpbmVkKTtcbiAgICAgICAgICAgIGNvbnN0IHJlcyA9IG5ldyB0eXBlcy5BVmFsO1xuXG4gICAgICAgICAgICBpZiAobm9kZS5vcGVyYXRvciA9PSAnKycpIHtcbiAgICAgICAgICAgICAgICBjb25zdHJhaW50cy5wdXNoKHtBRERfT1BSRDE6IGxPcHJkLFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIEFERF9PUFJEMjogck9wcmQsXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgUkVTVUxUOiByZXMgfSk7XG4gICAgICAgICAgICAgICAgbE9wcmQucHJvcGFnYXRlKG5ldyBjc3RyLklzQWRkZWQock9wcmQsIHJlcykpO1xuICAgICAgICAgICAgICAgIHJPcHJkLnByb3BhZ2F0ZShuZXcgY3N0ci5Jc0FkZGVkKGxPcHJkLCByZXMpKTtcbiAgICAgICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgICAgICAgaWYgKGJpbm9wSXNCb29sZWFuKG5vZGUub3BlcmF0b3IpKSB7XG4gICAgICAgICAgICAgICAgICAgIGNvbnN0cmFpbnRzLnB1c2goe1RZUEU6IHR5cGVzLlByaW1Cb29sZWFuLFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBJTkNMX1NFVDogcmVzfSk7XG4gICAgICAgICAgICAgICAgICAgIHJlcy5hZGRUeXBlKHR5cGVzLlByaW1Cb29sZWFuKTtcbiAgICAgICAgICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgICAgICAgICAgICBjb25zdHJhaW50cy5wdXNoKHtUWVBFOiB0eXBlcy5QcmltTnVtYmVyLFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBJTkNMX1NFVDogcmVzfSk7XG4gICAgICAgICAgICAgICAgICAgIHJlcy5hZGRUeXBlKHR5cGVzLlByaW1OdW1iZXIpO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIHJldHVybiByZXM7XG4gICAgICAgIH0sXG5cbiAgICAgICAgVHJ5U3RhdGVtZW50OiBmdW5jdGlvbiAobm9kZSwgY3VyU3RhdHVzLCBjKSB7XG4gICAgICAgICAgICAvLyBjb25zdHJ1Y3Qgc2NvcGUgY2hhaW4gZm9yIGNhdGNoIGJsb2NrXG4gICAgICAgICAgICBjb25zdCBjYXRjaEJsb2NrU0MgPVxuICAgICAgICAgICAgICAgIG5vZGUuaGFuZGxlci5ib2R5WydAYmxvY2snXVxuICAgICAgICAgICAgICAgIC5nZXRTY29wZUluc3RhbmNlKGN1clN0YXR1cy5zYywgY3VyU3RhdHVzLmRlbHRhKTtcbiAgICAgICAgICAgIC8vIGdldCB0aGUgQVZhbCBmb3IgZXhjZXB0aW9uIHBhcmFtZXRlclxuICAgICAgICAgICAgY29uc3QgZXhjQVZhbCA9IGNhdGNoQmxvY2tTQy5nZXRBVmFsT2Yobm9kZS5oYW5kbGVyLnBhcmFtLm5hbWUpO1xuXG4gICAgICAgICAgICAvLyBmb3IgdHJ5IGJsb2NrXG4gICAgICAgICAgICBjb25zdCB0cnlTdGF0dXMgPSBjaGFuZ2VkU3RhdHVzKGN1clN0YXR1cywgJ2V4YycsIGV4Y0FWYWwpO1xuICAgICAgICAgICAgYyhub2RlLmJsb2NrLCB0cnlTdGF0dXMsIHVuZGVmaW5lZCk7XG5cbiAgICAgICAgICAgIC8vIGZvciBjYXRjaCBibG9ja1xuICAgICAgICAgICAgY29uc3QgY2F0Y2hTdGF0dXMgPSBjaGFuZ2VkU3RhdHVzKGN1clN0YXR1cywgJ3NjJywgY2F0Y2hCbG9ja1NDKTtcbiAgICAgICAgICAgIGMobm9kZS5oYW5kbGVyLmJvZHksIGNhdGNoU3RhdHVzLCB1bmRlZmluZWQpO1xuXG4gICAgICAgICAgICAvLyBmb3IgZmluYWxseSBibG9ja1xuICAgICAgICAgICAgaWYgKG5vZGUuZmluYWxpemVyICE9PSBudWxsKVxuICAgICAgICAgICAgICAgIGMobm9kZS5maW5hbGl6ZXIsIGN1clN0YXR1cywgdW5kZWZpbmVkKTtcbiAgICAgICAgfSxcblxuICAgICAgICBUaHJvd1N0YXRlbWVudDogZnVuY3Rpb24gKG5vZGUsIGN1clN0YXR1cywgYykge1xuICAgICAgICAgICAgY29uc3QgdGhyID0gYyhub2RlLmFyZ3VtZW50LCBjdXJTdGF0dXMsIHVuZGVmaW5lZCk7XG4gICAgICAgICAgICBjb25zdHJhaW50cy5wdXNoKHtGUk9NOiB0aHIsXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICBUTzogY3VyU3RhdHVzLmV4Y30pO1xuICAgICAgICAgICAgdGhyLnByb3BhZ2F0ZShjdXJTdGF0dXMuZXhjKTtcbiAgICAgICAgfSxcblxuICAgICAgICBDYWxsRXhwcmVzc2lvbjogZnVuY3Rpb24gKG5vZGUsIGN1clN0YXR1cywgYykge1xuICAgICAgICAgICAgY29uc3QgcmVzQVZhbCA9IG5ldyB0eXBlcy5BVmFsO1xuICAgICAgICAgICAgY29uc3QgYXJnQVZhbHMgPSBbXTtcblxuICAgICAgICAgICAgLy8gZ2V0IEFWYWxzIGZvciBlYWNoIGFyZ3VtZW50c1xuICAgICAgICAgICAgZm9yIChsZXQgaSA9IDA7IGkgPCBub2RlLmFyZ3VtZW50cy5sZW5ndGg7IGkrKykge1xuICAgICAgICAgICAgICAgIGFyZ0FWYWxzLnB1c2goXG4gICAgICAgICAgICAgICAgICAgIGMobm9kZS5hcmd1bWVudHNbaV0sIGN1clN0YXR1cywgdW5kZWZpbmVkKSk7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICAvLyBhcHBlbmQgY3VycmVudCBjYWxsIHNpdGUgdG8gdGhlIGNvbnRleHRcbiAgICAgICAgICAgIGNvbnN0IG5ld0RlbHRhID0gY3VyU3RhdHVzLmRlbHRhLmFwcGVuZE9uZShub2RlWydAbGFiZWwnXSk7XG5cbiAgICAgICAgICAgIGlmIChub2RlLmNhbGxlZS50eXBlID09PSAnTWVtYmVyRXhwcmVzc2lvbicpIHtcbiAgICAgICAgICAgICAgICAvLyBtZXRob2QgY2FsbFxuICAgICAgICAgICAgICAgIC8vIHZhciByZWN2ID0gYyhub2RlLmNhbGxlZS5vYmplY3QsIGN1clN0YXR1cywgdW5kZWZpbmVkKTtcbiAgICAgICAgICAgICAgICAvLyB2YXIgbWV0aG9kTmFtZSA9IGltbWVkUHJvcChub2RlLmNhbGxlZSk7XG4gICAgICAgICAgICAgICAgLy8gY29uc3RyYWludHMucHVzaCh7XG4gICAgICAgICAgICAgICAgLy8gICBSRUNWOiByZWN2LFxuICAgICAgICAgICAgICAgIC8vICAgUFJPUE5BTUU6IG1ldGhvZE5hbWUsXG4gICAgICAgICAgICAgICAgLy8gICBQQVJBTVM6IGFyZ0FWYWxzLFxuICAgICAgICAgICAgICAgIC8vICAgUkVUOiByZXNBVmFsLFxuICAgICAgICAgICAgICAgIC8vICAgRVhDOiBjdXJTdGF0dXMuZXhjLFxuICAgICAgICAgICAgICAgIC8vICAgREVMVEE6IG5ld0RlbHRhXG4gICAgICAgICAgICAgICAgLy8gfSk7XG4gICAgICAgICAgICAgICAgY29uc3QgcmVjdkFuZFJldCA9IHJlYWRNZW1iZXIobm9kZS5jYWxsZWUsIGN1clN0YXR1cywgYyk7XG4gICAgICAgICAgICAgICAgcmVjdkFuZFJldFsxXS5wcm9wYWdhdGUoXG4gICAgICAgICAgICAgICAgICAgIG5ldyBjc3RyLklzQ2FsbGVlKFxuICAgICAgICAgICAgICAgICAgICAgICAgcmVjdkFuZFJldFswXSxcbiAgICAgICAgICAgICAgICAgICAgICAgIGFyZ0FWYWxzLFxuICAgICAgICAgICAgICAgICAgICAgICAgcmVzQVZhbCxcbiAgICAgICAgICAgICAgICAgICAgICAgIGN1clN0YXR1cy5leGMsXG4gICAgICAgICAgICAgICAgICAgICAgICBuZXdEZWx0YSkpO1xuICAgICAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICAgICAgICAvLyBub3JtYWwgZnVuY3Rpb24gY2FsbFxuICAgICAgICAgICAgICAgIGNvbnN0IGNhbGxlZUFWYWwgPSBjKG5vZGUuY2FsbGVlLCBjdXJTdGF0dXMsIHVuZGVmaW5lZCk7XG4gICAgICAgICAgICAgICAgLy8gY2FsbGVl7J2YIHJldHVybuydhCBjYWxsIGV4cHJlc3Npb27snLzroZxcbiAgICAgICAgICAgICAgICAvLyBjYWxsZWXsnZggZXhjZXB0aW9u7J2EIO2YuOy2nCDsuKHsnZggZXhjZXB0aW9u7JeQIOyghOuLrO2VtOyVvFxuICAgICAgICAgICAgICAgIGNvbnN0cmFpbnRzLnB1c2goe1xuICAgICAgICAgICAgICAgICAgICBDQUxMRUU6IGNhbGxlZUFWYWwsXG4gICAgICAgICAgICAgICAgICAgIFNFTEY6IHJ0Q1guZ2xvYmFsT2JqZWN0LFxuICAgICAgICAgICAgICAgICAgICBQQVJBTVM6IGFyZ0FWYWxzLFxuICAgICAgICAgICAgICAgICAgICBSRVQ6IHJlc0FWYWwsXG4gICAgICAgICAgICAgICAgICAgIEVYQzogY3VyU3RhdHVzLmV4YyxcbiAgICAgICAgICAgICAgICAgICAgREVMVEE6IG5ld0RlbHRhXG4gICAgICAgICAgICAgICAgfSk7XG4gICAgICAgICAgICAgICAgY2FsbGVlQVZhbC5wcm9wYWdhdGUoXG4gICAgICAgICAgICAgICAgICAgIG5ldyBjc3RyLklzQ2FsbGVlKFxuICAgICAgICAgICAgICAgICAgICAgICAgbmV3IHR5cGVzLkFWYWwocnRDWC5nbG9iYWxPYmplY3QpLFxuICAgICAgICAgICAgICAgICAgICAgICAgYXJnQVZhbHMsXG4gICAgICAgICAgICAgICAgICAgICAgICByZXNBVmFsLFxuICAgICAgICAgICAgICAgICAgICAgICAgY3VyU3RhdHVzLmV4YyxcbiAgICAgICAgICAgICAgICAgICAgICAgIG5ld0RlbHRhKSk7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICByZXR1cm4gcmVzQVZhbDtcbiAgICAgICAgfSxcblxuICAgICAgICBNZW1iZXJFeHByZXNzaW9uOiBmdW5jdGlvbiAobm9kZSwgY3VyU3RhdHVzLCBjKSB7XG4gICAgICAgICAgICBjb25zdCByZWN2QW5kUmV0ID0gcmVhZE1lbWJlcihub2RlLCBjdXJTdGF0dXMsIGMpO1xuICAgICAgICAgICAgcmV0dXJuIHJlY3ZBbmRSZXRbMV07XG4gICAgICAgIH0sXG5cbiAgICAgICAgUmV0dXJuU3RhdGVtZW50OiBmdW5jdGlvbiAobm9kZSwgY3VyU3RhdHVzLCBjKSB7XG4gICAgICAgICAgICBpZiAoIW5vZGUuYXJndW1lbnQpIHJldHVybjtcbiAgICAgICAgICAgIGNvbnN0IHJldCA9IGMobm9kZS5hcmd1bWVudCwgY3VyU3RhdHVzLCB1bmRlZmluZWQpO1xuICAgICAgICAgICAgY29uc3RyYWludHMucHVzaCh7RlJPTTogcmV0LFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgVE86IGN1clN0YXR1cy5yZXR9KTtcbiAgICAgICAgICAgIHJldC5wcm9wYWdhdGUoY3VyU3RhdHVzLnJldCk7XG4gICAgICAgIH1cbiAgICB9KTtcblxuICAgIHJlY3Vyc2l2ZVdpdGhSZXR1cm4oYXN0LCBpbml0U3RhdHVzLCBjb25zdHJhaW50R2VuZXJhdG9yKTtcblxuICAgIC8vIFdlIGFjdHVhbGx5IGFkZGVkIGNvbnN0cmFpbnRzXG4gICAgcmV0dXJuIHRydWU7XG59XG5cbmZ1bmN0aW9uIHJlY3Vyc2l2ZVdpdGhSZXR1cm4obm9kZSwgc3RhdGUsIHZpc2l0b3IpIHtcbiAgICBmdW5jdGlvbiBjKG5vZGUsIHN0LCBvdmVycmlkZSkge1xuICAgICAgICByZXR1cm4gdmlzaXRvcltvdmVycmlkZSB8fCBub2RlLnR5cGVdKG5vZGUsIHN0LCBjKTtcbiAgICB9XG4gICAgcmV0dXJuIGMobm9kZSwgc3RhdGUpO1xufVxuXG5leHBvcnRzLmNvbnN0cmFpbnRzID0gY29uc3RyYWludHM7XG5leHBvcnRzLmFkZENvbnN0cmFpbnRzID0gYWRkQ29uc3RyYWludHM7XG5leHBvcnRzLmNsZWFyQ29uc3RyYWludHMgPSBjbGVhckNvbnN0cmFpbnRzO1xuIiwiJ3VzZSBzdHJpY3QnO1xuXG5jb25zdCB0eXBlcyA9IHJlcXVpcmUoJy4uL2RvbWFpbnMvdHlwZXMnKTtcbmNvbnN0IHN0YXR1cyA9IHJlcXVpcmUoJy4uL2RvbWFpbnMvc3RhdHVzJyk7XG5jb25zdCBjR2VuID0gcmVxdWlyZSgnLi9jR2VuJyk7XG5cbmZ1bmN0aW9uIENTVFIoKSB7fVxuQ1NUUi5wcm90b3R5cGUgPSBPYmplY3QuY3JlYXRlKG51bGwpO1xuQ1NUUi5wcm90b3R5cGUuZXF1YWxzID0gZnVuY3Rpb24gKG90aGVyKSB7XG4gICAgcmV0dXJuIHRoaXMgPT09IG90aGVyO1xufTtcblxuZnVuY3Rpb24gUmVhZFByb3AocHJvcCwgdG8pIHtcbiAgICB0aGlzLnByb3AgPSBwcm9wO1xuICAgIHRoaXMudG8gPSB0bztcbn1cblJlYWRQcm9wLnByb3RvdHlwZSA9IE9iamVjdC5jcmVhdGUoQ1NUUi5wcm90b3R5cGUpO1xuUmVhZFByb3AucHJvdG90eXBlLmFkZFR5cGUgPSBmdW5jdGlvbiAob2JqKSB7XG4gICAgaWYgKCEob2JqIGluc3RhbmNlb2YgKHR5cGVzLk9ialR5cGUpKSkgcmV0dXJuO1xuICAgIC8vIHdoZW4gb2JqIGlzIE9ialR5cGUsXG4gICAgY29uc3Qgb3duUHJvcCA9IG9iai5nZXRQcm9wKHRoaXMucHJvcCwgdHJ1ZSk7XG4gICAgaWYgKG93blByb3ApIHtcbiAgICAgICAgLy8gd2hlbiB0aGUgb2JqZWN0IGhhcyB0aGUgcHJvcCxcbiAgICAgICAgb3duUHJvcC5wcm9wYWdhdGUodGhpcy50byk7XG4gICAgfSBlbHNlIGlmIChvYmouZ2V0UHJvcCgnX19wcm90b19fJywgdHJ1ZSkpIHtcbiAgICAgICAgLy8gdXNlIHByb3RvdHlwZSBjaGFpblxuICAgICAgICBvYmouZ2V0UHJvcCgnX19wcm90b19fJylcbiAgICAgICAgICAucHJvcGFnYXRlKG5ldyBSZWFkUHJvcCh0aGlzLnByb3AsIHRoaXMudG8pKTtcbiAgICB9XG59O1xuUmVhZFByb3AucHJvdG90eXBlLmVxdWFscyA9IGZ1bmN0aW9uIChvdGhlcikge1xuICAgIGlmICghKG90aGVyIGluc3RhbmNlb2YgUmVhZFByb3ApKSByZXR1cm4gZmFsc2U7XG4gICAgcmV0dXJuIHRoaXMucHJvcCA9PT0gb3RoZXIucHJvcFxuICAgICAgICAmJiB0aGlzLnRvLmVxdWFscyhvdGhlci50byk7XG59O1xuXG5mdW5jdGlvbiBXcml0ZVByb3AocHJvcCwgZnJvbSkge1xuICAgIHRoaXMucHJvcCA9IHByb3A7XG4gICAgdGhpcy5mcm9tID0gZnJvbTtcbn1cbldyaXRlUHJvcC5wcm90b3R5cGUgPSBPYmplY3QuY3JlYXRlKENTVFIucHJvdG90eXBlKTtcbldyaXRlUHJvcC5wcm90b3R5cGUuYWRkVHlwZSA9IGZ1bmN0aW9uIChvYmopIHtcbiAgICBpZiAoIShvYmogaW5zdGFuY2VvZiAodHlwZXMuT2JqVHlwZSkpKSByZXR1cm47XG4gICAgY29uc3Qgb3duUHJvcCA9IG9iai5nZXRQcm9wKHRoaXMucHJvcCk7XG4gICAgdGhpcy5mcm9tLnByb3BhZ2F0ZShvd25Qcm9wKTtcbn07XG5cbmZ1bmN0aW9uIElzQWRkZWQob3RoZXIsIHRhcmdldCkge1xuICAgIHRoaXMub3RoZXIgPSBvdGhlcjtcbiAgICB0aGlzLnRhcmdldCA9IHRhcmdldDtcbn1cbklzQWRkZWQucHJvdG90eXBlID0gT2JqZWN0LmNyZWF0ZShDU1RSLnByb3RvdHlwZSk7XG5Jc0FkZGVkLnByb3RvdHlwZS5hZGRUeXBlID0gZnVuY3Rpb24gKHR5cGUpIHtcbiAgICBpZiAoKHR5cGUgPT09IHR5cGVzLlByaW1OdW1iZXIgXG4gICAgICAgICB8fCB0eXBlID09PSB0eXBlcy5QcmltQm9vbGVhbilcbiAgICAgJiYgKHRoaXMub3RoZXIuaGFzVHlwZSh0eXBlcy5QcmltTnVtYmVyKSBcbiAgICAgICAgIHx8IHRoaXMub3RoZXIuaGFzVHlwZSh0eXBlcy5QcmltQm9vbGVhbikpKSB7XG4gICAgICAgIHRoaXMudGFyZ2V0LmFkZFR5cGUodHlwZXMuUHJpbU51bWJlcik7XG4gICAgfVxuICAgIGlmICh0eXBlID09PSB0eXBlcy5QcmltU3RyaW5nXG4gICAgICYmICF0aGlzLm90aGVyLmlzRW1wdHkoKSkge1xuICAgICAgICAgdGhpcy50YXJnZXQuYWRkVHlwZSh0eXBlcy5QcmltU3RyaW5nKTtcbiAgICB9XG59O1xuXG5mdW5jdGlvbiBJc0NhbGxlZShzZWxmLCBhcmdzLCByZXQsIGV4YywgZGVsdGEpIHtcbiAgICB0aGlzLnNlbGYgPSBzZWxmO1xuICAgIHRoaXMuYXJncyA9IGFyZ3M7XG4gICAgdGhpcy5yZXQgPSByZXQ7XG4gICAgdGhpcy5leGMgPSBleGM7XG4gICAgdGhpcy5kZWx0YSA9IGRlbHRhO1xufVxuSXNDYWxsZWUucHJvdG90eXBlID0gT2JqZWN0LmNyZWF0ZShDU1RSLnByb3RvdHlwZSk7XG5Jc0NhbGxlZS5wcm90b3R5cGUuYWRkVHlwZSA9IGZ1bmN0aW9uIChmKSB7XG4gICAgaWYgKCEoZiBpbnN0YW5jZW9mICh0eXBlcy5GblR5cGUpKSkgcmV0dXJuO1xuICAgIGNvbnN0IGZ1bkVudiA9IGYuZ2V0RnVuRW52KHRoaXMuZGVsdGEpO1xuICAgIGNvbnN0IG5ld1NDID0gZi5vcmlnaW5Ob2RlLmJvZHlbJ0BibG9jayddLmdldFNjb3BlSW5zdGFuY2UoZi5zYywgdGhpcy5kZWx0YSk7XG4gICAgY29uc3QgZnVuU3RhdHVzXG4gICAgICAgID0gbmV3IHN0YXR1cy5TdGF0dXMoZnVuRW52WzBdLCBmdW5FbnZbMV0sIGZ1bkVudlsyXSwgXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgdGhpcy5kZWx0YSwgbmV3U0MpO1xuICAgIC8vIHBhc3MgdGhpcyBvYmplY3RcbiAgICB0aGlzLnNlbGYucHJvcGFnYXRlKGZ1bkVudlswXSk7XG5cbiAgICBjb25zdCBtaW5MZW4gPSBNYXRoLm1pbih0aGlzLmFyZ3MubGVuZ3RoLCBmLnBhcmFtTmFtZXMubGVuZ3RoKTtcbiAgICBmb3IgKGxldCBpID0gMDsgaSA8IG1pbkxlbjsgaSsrKSB7XG4gICAgICAgIHRoaXMuYXJnc1tpXS5wcm9wYWdhdGUobmV3U0MuZ2V0QVZhbE9mKGYucGFyYW1OYW1lc1tpXSkpO1xuICAgIH1cblxuICAgIC8vIGZvciBhcmd1bWVudHMgb2JqZWN0XG4gICAgaWYgKGYub3JpZ2luTm9kZS5ib2R5WydAYmxvY2snXS51c2VBcmd1bWVudHNPYmplY3QpIHtcbiAgICAgICAgY29uc3QgYXJnT2JqID0gZi5nZXRBcmd1bWVudHNPYmplY3QodGhpcy5kZWx0YSk7XG4gICAgICAgIG5ld1NDLmdldEFWYWxPZignYXJndW1lbnRzJykuYWRkVHlwZShhcmdPYmopO1xuICAgICAgICBmb3IgKGxldCBpID0gMDsgaSA8IHRoaXMuYXJncy5sZW5ndGg7IGkrKykge1xuICAgICAgICAgICAgdGhpcy5hcmdzW2ldLnByb3BhZ2F0ZShhcmdPYmouZ2V0UHJvcChpICsgJycpKTtcbiAgICAgICAgICAgIHRoaXMuYXJnc1tpXS5wcm9wYWdhdGUoYXJnT2JqLmdldFByb3AobnVsbCkpO1xuICAgICAgICB9XG4gICAgICAgIGFyZ09iai5nZXRQcm9wKCdjYWxsZWUnKS5hZGRUeXBlKGYpO1xuICAgICAgICBhcmdPYmouZ2V0UHJvcCgnbGVuZ3RoJykuYWRkVHlwZSh0eXBlcy5QcmltTnVtYmVyKTtcbiAgICB9XG5cbiAgICAvLyBjb25zdHJhaW50IGdlbmVyYXRpb24gZm9yIHRoZSBmdW5jdGlvbiBib2R5XG4gICAgY0dlbi5hZGRDb25zdHJhaW50cyhmLm9yaWdpbk5vZGUuYm9keSwgZnVuU3RhdHVzKTtcblxuICAgIC8vIGdldCByZXR1cm4gXG4gICAgZnVuRW52WzFdLnByb3BhZ2F0ZSh0aGlzLnJldCk7XG4gICAgLy8gZ2V0IGV4Y2VwdGlvblxuICAgIGZ1bkVudlsyXS5wcm9wYWdhdGUodGhpcy5leGMpO1xufTtcblxuZnVuY3Rpb24gSXNDdG9yKGFyZ3MsIHJldCwgZXhjLCBkZWx0YSkge1xuICAgIHRoaXMuYXJncyA9IGFyZ3M7XG4gICAgdGhpcy5yZXQgPSByZXQ7XG4gICAgdGhpcy5leGMgPSBleGM7XG4gICAgdGhpcy5kZWx0YSA9IGRlbHRhO1xufVxuSXNDdG9yLnByb3RvdHlwZSA9IE9iamVjdC5jcmVhdGUoQ1NUUi5wcm90b3R5cGUpO1xuSXNDdG9yLnByb3RvdHlwZS5hZGRUeXBlID0gZnVuY3Rpb24gKGYpIHtcbiAgICBpZiAoIShmIGluc3RhbmNlb2YgKHR5cGVzLkZuVHlwZSkpKSByZXR1cm47XG4gICAgY29uc3QgZnVuRW52ID0gZi5nZXRGdW5FbnYodGhpcy5kZWx0YSk7XG4gICAgY29uc3QgbmV3U0MgPSBmLm9yaWdpbk5vZGUuYm9keVsnQGJsb2NrJ10uZ2V0U2NvcGVJbnN0YW5jZShmLnNjLCB0aGlzLmRlbHRhKTtcbiAgICBjb25zdCBmdW5TdGF0dXNcbiAgICAgICAgPSBuZXcgc3RhdHVzLlN0YXR1cyhmdW5FbnZbMF0sIG5ldyBJZk9ialR5cGUoZnVuRW52WzFdKSwgZnVuRW52WzJdLFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIHRoaXMuZGVsdGEsIG5ld1NDKTtcbiAgICAvLyBwYXNzIHRoaXMgb2JqZWN0XG4gICAgY29uc3QgbmV3T2JqID0gZi5nZXRJbnN0YW5jZSgpO1xuICAgIGZ1bkVudlswXS5hZGRUeXBlKG5ld09iaik7XG5cbiAgICBjb25zdCBtaW5MZW4gPSBNYXRoLm1pbih0aGlzLmFyZ3MubGVuZ3RoLCBmLnBhcmFtTmFtZXMubGVuZ3RoKTtcbiAgICBmb3IgKGxldCBpID0gMDsgaSA8IG1pbkxlbjsgaSsrKSB7XG4gICAgICAgIHRoaXMuYXJnc1tpXS5wcm9wYWdhdGUobmV3U0MuZ2V0QVZhbE9mKGYucGFyYW1OYW1lc1tpXSkpO1xuICAgIH1cblxuICAgIC8vIGZvciBhcmd1bWVudHMgb2JqZWN0XG4gICAgaWYgKGYub3JpZ2luTm9kZS5ib2R5WydAYmxvY2snXS51c2VBcmd1bWVudHNPYmplY3QpIHtcbiAgICAgICAgY29uc3QgYXJnT2JqID0gZi5nZXRBcmd1bWVudHNPYmplY3QodGhpcy5kZWx0YSk7XG4gICAgICAgIG5ld1NDLmdldEFWYWxPZignYXJndW1lbnRzJykuYWRkVHlwZShhcmdPYmopO1xuICAgICAgICBmb3IgKGxldCBpID0gMDsgaSA8IHRoaXMuYXJncy5sZW5ndGg7IGkrKykge1xuICAgICAgICAgICAgdGhpcy5hcmdzW2ldLnByb3BhZ2F0ZShhcmdPYmouZ2V0UHJvcChpICsgJycpKTtcbiAgICAgICAgICAgIHRoaXMuYXJnc1tpXS5wcm9wYWdhdGUoYXJnT2JqLmdldFByb3AobnVsbCkpO1xuICAgICAgICB9XG4gICAgICAgIGFyZ09iai5nZXRQcm9wKCdjYWxsZWUnKS5hZGRUeXBlKGYpO1xuICAgICAgICBhcmdPYmouZ2V0UHJvcCgnbGVuZ3RoJykuYWRkVHlwZSh0eXBlcy5QcmltTnVtYmVyKTtcbiAgICB9XG5cbiAgICAvLyBjb25zdHJhaW50IGdlbmVyYXRpb24gZm9yIHRoZSBmdW5jdGlvbiBib2R5XG4gICAgY0dlbi5hZGRDb25zdHJhaW50cyhmLm9yaWdpbk5vZGUuYm9keSwgZnVuU3RhdHVzKTtcblxuICAgIC8vIGJ5IGV4cGxpY2l0IHJldHVybiwgb25seSBPYmpUeXBlIGFyZSBwcm9wYWdhdGVkXG4gICAgZnVuRW52WzFdLnByb3BhZ2F0ZSh0aGlzLnJldCk7XG4gICAgLy8gcmV0dXJuIG5ldyBvYmplY3RcbiAgICB0aGlzLnJldC5hZGRUeXBlKG5ld09iaik7XG4gICAgLy8gZ2V0IGV4Y2VwdGlvblxuICAgIGZ1bkVudlsyXS5wcm9wYWdhdGUodGhpcy5leGMpO1xufTtcblxuLy8gaWdub3JlIG5vbiBvYmplY3QgdHlwZXNcbmZ1bmN0aW9uIElmT2JqVHlwZShhdmFsKSB7XG4gICAgdGhpcy5hdmFsID0gYXZhbDtcbn1cbklmT2JqVHlwZS5wcm90b3R5cGUgPSBPYmplY3QuY3JlYXRlKENTVFIucHJvdG90eXBlKTtcbklmT2JqVHlwZS5wcm90b3R5cGUuYWRkVHlwZSA9IGZ1bmN0aW9uICh0eXBlKSB7XG4gICAgaWYgKCEodHlwZSBpbnN0YW5jZW9mIHR5cGVzLk9ialR5cGUpKSByZXR1cm47XG4gICAgdGhpcy5hdmFsLmFkZFR5cGUodHlwZSk7XG59O1xuXG5leHBvcnRzLlJlYWRQcm9wID0gUmVhZFByb3A7XG5leHBvcnRzLldyaXRlUHJvcCA9IFdyaXRlUHJvcDtcbmV4cG9ydHMuSXNBZGRlZCA9IElzQWRkZWQ7XG5leHBvcnRzLklzQ2FsbGVlID0gSXNDYWxsZWU7XG5leHBvcnRzLklzQ3RvciA9IElzQ3RvcjtcbiIsIi8vIENvbnRleHQgZm9yIGstQ0ZBIGFuYWx5c2lzXG4vL1xuLy8gQXNzdW1lIGEgY29udGV4dCBpcyBhbiBhcnJheSBvZiBudW1iZXJzLlxuLy8gQSBudW1iZXIgaW4gc3VjaCBsaXN0IGRlbm90ZXMgYSBjYWxsIHNpdGUsIHRoYXQgaXMgQGxhYmVsIG9mIGEgQ2FsbEV4cHJlc3Npb24uXG4vLyBXZSBrZWVwIHRoZSBtb3N0IHJlY2VudCAnaycgY2FsbHNpdGVzLlxuLy8gRXF1YWxpdHkgb24gY29udGV4dHMgc2hvdWxkIGxvb2sgaW50byB0aGUgbnVtYmVycy5cblxudmFyIGNhbGxTaXRlQ29udGV4dFBhcmFtZXRlciA9IHtcbiAgICAvLyBtYXhpbXVtIGxlbmd0aCBvZiBjb250ZXh0XG4gICAgbWF4RGVwdGhLOiAwLFxuICAgIC8vIGZ1bmN0aW9uIGxpc3QgZm9yIHNlbnNpdGl2ZSBhbmFseXNpc1xuICAgIHNlbnNGdW5jczoge31cbn07XG5cbmZ1bmN0aW9uIENhbGxTaXRlQ29udGV4dChjc0xpc3QpIHtcbiAgICBpZiAoY3NMaXN0KSB0aGlzLmNzTGlzdCA9IGNzTGlzdDtcbiAgICBlbHNlIHRoaXMuY3NMaXN0ID0gW107XG59XG5cbkNhbGxTaXRlQ29udGV4dC5wcm90b3R5cGUuZXF1YWxzID0gZnVuY3Rpb24gKG90aGVyKSB7XG4gICAgaWYgKHRoaXMuY3NMaXN0Lmxlbmd0aCAhPSBvdGhlci5jc0xpc3QubGVuZ3RoKSByZXR1cm4gZmFsc2U7XG4gICAgZm9yICh2YXIgaSA9IDA7IGkgPCB0aGlzLmNzTGlzdC5sZW5ndGg7IGkrKykge1xuICAgICAgICBpZiAodGhpcy5jc0xpc3RbaV0gIT09IG90aGVyLmNzTGlzdFtpXSkgcmV0dXJuIGZhbHNlO1xuICAgIH1cbiAgICByZXR1cm4gdHJ1ZTtcbn07XG5cbkNhbGxTaXRlQ29udGV4dC5wcm90b3R5cGUuYXBwZW5kT25lID0gZnVuY3Rpb24gKGNhbGxTaXRlKSB7XG4gICAgLy8gdXNlIGNvbmNhdCB0byBjcmVhdGUgYSBuZXcgYXJyYXlcbiAgICAvLyBvbGRlc3Qgb25lIGNvbWVzIGZpcnN0XG4gICAgdmFyIGFwcGVuZGVkID0gdGhpcy5jc0xpc3QuY29uY2F0KGNhbGxTaXRlKTtcbiAgICBpZiAoYXBwZW5kZWQubGVuZ3RoID4gY2FsbFNpdGVDb250ZXh0UGFyYW1ldGVyLm1heERlcHRoSykge1xuICAgICAgICBhcHBlbmRlZC5zaGlmdCgpO1xuICAgIH1cbiAgICByZXR1cm4gbmV3IENhbGxTaXRlQ29udGV4dChhcHBlbmRlZCk7XG59O1xuXG5DYWxsU2l0ZUNvbnRleHQucHJvdG90eXBlLnRvU3RyaW5nID0gZnVuY3Rpb24gKCkge1xuICAgIHJldHVybiB0aGlzLmNzTGlzdC50b1N0cmluZygpO1xufTtcblxuZXhwb3J0cy5jYWxsU2l0ZUNvbnRleHRQYXJhbWV0ZXIgPSBjYWxsU2l0ZUNvbnRleHRQYXJhbWV0ZXI7XG5leHBvcnRzLkNhbGxTaXRlQ29udGV4dCA9IENhbGxTaXRlQ29udGV4dDsiLCIvLyBTdGF0dXM6XG4vLyB7IHNlbGYgIDogQVZhbCxcbi8vICAgcmV0ICAgOiBBVmFsLFxuLy8gICBleGMgICA6IEFWYWwsXG4vLyAgIGRlbHRhIDogQ29udGV4dCxcbi8vICAgc2MgICAgOiBTY29wZUNoYWluIH1cblxuZnVuY3Rpb24gU3RhdHVzKHNlbGYsIHJldCwgZXhjLCBkZWx0YSwgc2MpIHtcbiAgICB0aGlzLnNlbGYgPSBzZWxmO1xuICAgIHRoaXMucmV0ID0gcmV0O1xuICAgIHRoaXMuZXhjID0gZXhjO1xuICAgIHRoaXMuZGVsdGEgPSBkZWx0YTtcbiAgICB0aGlzLnNjID0gc2M7XG59XG5cblN0YXR1cy5wcm90b3R5cGUuZXF1YWxzID0gZnVuY3Rpb24gKG90aGVyKSB7XG4gICAgcmV0dXJuIHRoaXMuc2VsZiA9PT0gb3RoZXIuc2VsZiAmJlxuICAgICAgICB0aGlzLnJldCA9PT0gb3RoZXIucmV0ICYmXG4gICAgICAgIHRoaXMuZXhjID09PSBvdGhlci5leGMgJiZcbiAgICAgICAgdGhpcy5kZWx0YS5lcXVhbHMob3RoZXIuZGVsdGEpICYmXG4gICAgICAgIHRoaXMuc2MgPT09IG90aGVyLnNjO1xufTtcblxuZXhwb3J0cy5TdGF0dXMgPSBTdGF0dXM7IiwiJ3VzZSBzdHJpY3QnO1xuXG4vLyBmb3IgREVCVUdcbnZhciBjb3VudCA9IDA7XG4vKipcbiAqIHRoZSBhYnN0cmFjdCB2YWx1ZSBmb3IgYSBjb25jcmV0ZSB2YWx1ZVxuICogd2hpY2ggaXMgYSBzZXQgb2YgdHlwZXMuXG4gKiBAY29uc3RydWN0b3JcbiAqIEBwYXJhbSB7VHlwZX0gdHlwZSAtIGdpdmUgYSB0eXBlIHRvIG1ha2UgQVZhbCB3aXRoIGEgc2luZ2xlIHR5cGVcbiAqL1xuZnVuY3Rpb24gQVZhbCh0eXBlKSB7XG4gICAgLy8gdHlwZTogY29udGFpbmVkIHR5cGVzXG4gICAgLy8gV2UgYXNzdW1lIHR5cGVzIGFyZSBkaXN0aW5ndWlzaGFibGUgYnkgJz09PSdcbiAgICBpZiAodHlwZSkgdGhpcy50eXBlcyA9IG5ldyBTZXQoW3R5cGVdKTtcbiAgICBlbHNlIHRoaXMudHlwZXMgPSBuZXcgU2V0KCk7XG4gICAgLy8gZm9yd2FyZHM6IHByb3BhZ2F0aW9uIHRhcmdldHNcbiAgICAvLyBXZSBhc3N1bWUgdGFyZ2V0cyBhcmUgZGlzdGluZ3Vpc2hhYmxlIGJ5ICdlcXVhbHMnIG1ldGhvZFxuICAgIHRoaXMuZm9yd2FyZHMgPSBuZXcgU2V0KCk7XG4gICAgLy8gZm9yIERFQlVHXG4gICAgdGhpcy5faWQgPSBjb3VudCsrO1xufVxuLyoqIENoZWNrIHdoZXRoZXIgaXQgaGFzIGFueSB0eXBlXG4gKiBAcmV0dXJucyB7Ym9vbGVhbn1cbiAqL1xuQVZhbC5wcm90b3R5cGUuaXNFbXB0eSA9IGZ1bmN0aW9uICgpIHtcbiAgICByZXR1cm4gdGhpcy50eXBlcy5zaXplID09PSAwO1xufTtcblxuLyoqXG4gKiBAcmV0dXJucyB7W1R5cGVdfVxuICovXG5BVmFsLnByb3RvdHlwZS5nZXRUeXBlcyA9IGZ1bmN0aW9uICgpIHtcbiAgICByZXR1cm4gdGhpcy50eXBlcztcbn07XG5cbi8qKlxuICogQHJldHVybnMge2Jvb2xlYW59XG4gKi9cbkFWYWwucHJvdG90eXBlLmhhc1R5cGUgPSBmdW5jdGlvbiAodHlwZSkge1xuICAgIHJldHVybiB0aGlzLnR5cGVzLmhhcyh0eXBlKTtcbn07XG5cbi8qKlxuICogQWRkIGEgdHlwZS5cbiAqIEBwYXJhbSB7VHlwZX0gdHlwZVxuICovXG5BVmFsLnByb3RvdHlwZS5hZGRUeXBlID0gZnVuY3Rpb24gKHR5cGUpIHtcbiAgICBpZiAodGhpcy50eXBlcy5oYXModHlwZSkpIHJldHVybjtcbiAgICAvLyBnaXZlbiB0eXBlIGlzIG5ld1xuICAgIHRoaXMudHlwZXMuYWRkKHR5cGUpO1xuICAgIC8vIHNlbmQgdG8gcHJvcGFnYXRpb24gdGFyZ2F0c1xuICAgIHRoaXMuZm9yd2FyZHMuZm9yRWFjaChmdW5jdGlvbiAoZndkKSB7XG4gICAgICAgIGZ3ZC5hZGRUeXBlKHR5cGUpO1xuICAgIH0pO1xufTtcbi8qKlxuICogQHBhcmFtIHtBVmFsfSB0YXJnZXRcbiAqL1xuQVZhbC5wcm90b3R5cGUucHJvcGFnYXRlID0gZnVuY3Rpb24gKHRhcmdldCkge1xuICAgIGlmICghdGhpcy5hZGRGb3J3YXJkKHRhcmdldCkpIHJldHVybjtcbiAgICAvLyB0YXJnZXQgaXMgbmV3bHkgYWRkZWRcbiAgICAvLyBzZW5kIHR5cGVzIHRvIHRoZSBuZXcgdGFyZ2V0XG4gICAgdGhpcy50eXBlcy5mb3JFYWNoKGZ1bmN0aW9uICh0eXBlKSB7XG4gICAgICAgIHRhcmdldC5hZGRUeXBlKHR5cGUpO1xuICAgIH0pO1xufTtcblxuQVZhbC5wcm90b3R5cGUuYWRkRm9yd2FyZCA9IGZ1bmN0aW9uIChmd2QpIHtcbiAgICBmb3IgKGxldCBvbGRGd2Qgb2YgdGhpcy5mb3J3YXJkcykge1xuICAgICAgICBpZiAoZndkLmVxdWFscyhvbGRGd2QpKSByZXR1cm4gZmFsc2U7XG4gICAgfVxuICAgIHRoaXMuZm9yd2FyZHMuYWRkKGZ3ZCk7XG4gICAgcmV0dXJuIHRydWU7XG59O1xuXG5BVmFsLnByb3RvdHlwZS5lcXVhbHMgPSBmdW5jdGlvbiAob3RoZXIpIHtcbiAgICAvLyBzaW1wbGUgcmVmZXJlbmNlIGNvbXBhcmlzb25cbiAgICByZXR1cm4gdGhpcyA9PT0gb3RoZXI7XG59O1xuXG4vKipcbiAqIFRPRE86IGNoZWNrIHdoZXRoZXIgd2UgcmVhbGx5IG5lZWQgdGhpcyBtZXRob2QuXG4gKiBAcGFyYW0ge3N0cmluZ30gcHJvcFxuICogQHJldHVybnMge0FWYWx9XG4gKi9cbkFWYWwucHJvdG90eXBlLmdldFByb3AgPSBmdW5jdGlvbiAocHJvcCkge1xuICAgIGlmIChwcm9wID09PSAn4pyWJykge1xuICAgICAgICAvLyDinJYgaXMgdGhlIGJvZ3VzIHByb3BlcnR5IG5hbWUgYWRkZWQgZm9yIGVycm9yIHJlY292ZXJ5LlxuICAgICAgICByZXR1cm4gQVZhbE51bGw7XG4gICAgfVxuICAgIGlmICh0aGlzLnByb3BzLmhhcyhwcm9wKSkge1xuICAgICAgICByZXR1cm4gdGhpcy5wcm9wcy5nZXQocHJvcCk7XG4gICAgfSBlbHNlIHtcbiAgICAgICAgcmV0dXJuIEFWYWxOdWxsO1xuICAgIH1cbn07XG5cbi8qKlxuICogdGhlIHN1cGVyIGNsYXNzIG9mIGFsbCB0eXBlc1xuICogZWFjaCB0eXBlIHNob3VsZCBiZSBkaXN0aW5ndWlzaGFibGUgYnkgJz09PScgb3BlcmF0aW9uLlxuICogQGNvbnN0cnVjdG9yXG4gKi9cbmZ1bmN0aW9uIFR5cGUoKSB7fVxuVHlwZS5wcm90b3R5cGUgPSBPYmplY3QuY3JlYXRlKG51bGwpO1xuXG4vKipcbiAqIDEuIG9iamVjdCB0eXBlc1xuICogQHBhcmFtIHtBVmFsfSBwcm90byAtIEFWYWwgb2YgY29uc3RydWN0b3IncyBwcm90b3R5cGVcbiAqIEBwYXJhbSB7c3RyaW5nfSBuYW1lIC0gZ3Vlc3NlZCBuYW1lXG4gKi9cbmZ1bmN0aW9uIE9ialR5cGUocHJvdG8sIG5hbWUpIHtcbiAgICB0aGlzLm5hbWUgPSBuYW1lO1xuICAgIHRoaXMucHJvcHMgPSBuZXcgTWFwKCk7XG5cbiAgICAvLyBzaGFyZSBwcm90byB3aXRoIF9fcHJvdG9fX1xuICAgIHRoaXMuc2V0UHJvcCgnX19wcm90b19fJywgcHJvdG8pO1xufVxuT2JqVHlwZS5wcm90b3R5cGUgPSBPYmplY3QuY3JlYXRlKFR5cGUucHJvdG90eXBlKTtcbi8qKlxuICogQHBhcmFtIHtzdHJpbmd8bnVsbH0gcHJvcCAtIG51bGwgZm9yIGNvbXB1dGVkIHByb3BzXG4gKiBAcGFyYW0ge2Jvb2xlYW59IHJlYWRPbmx5IC0gaWYgZmFsc2UsIGNyZWF0ZSBBVmFsIGZvciBwcm9wIGlmIG5lY2Vzc2FyeVxuICogQHJldHVybnMge0FWYWx9IEFWYWwgb2YgdGhlIHByb3BlcnR5XG4gKi9cbk9ialR5cGUucHJvdG90eXBlLmdldFByb3AgPSBmdW5jdGlvbiAocHJvcCwgcmVhZE9ubHkpIHtcbiAgICBpZiAocHJvcCA9PT0gJ+KclicpIHtcbiAgICAgICAgLy8g4pyWIGlzIHRoZSBib2d1cyBwcm9wZXJ0eSBuYW1lIGFkZGVkIGR1cmluZyBwYXJzaW5nIGVycm9yIHJlY292ZXJ5LlxuICAgICAgICByZXR1cm4gQVZhbE51bGw7XG4gICAgfVxuICAgIGlmICh0aGlzLnByb3BzLmhhcyhwcm9wKSkge1xuICAgICAgICByZXR1cm4gdGhpcy5wcm9wcy5nZXQocHJvcCk7XG4gICAgfSBlbHNlIGlmIChyZWFkT25seSkge1xuICAgICAgICByZXR1cm4gbnVsbDtcbiAgICB9IGVsc2Uge1xuICAgICAgICB2YXIgbmV3UHJvcEFWYWwgPSBuZXcgQVZhbDtcbiAgICAgICAgdGhpcy5wcm9wcy5zZXQocHJvcCwgbmV3UHJvcEFWYWwpO1xuICAgICAgICByZXR1cm4gbmV3UHJvcEFWYWw7XG4gICAgfVxufTtcbi8qKlxuICogV2UgdXNlIHRoaXMgZnVuY3Rpb24gdG8gc2hhcmUgLnByb3RvdHlwZSB3aXRoIGluc3RhbmNlcyBfX3Byb3RvX19cbiAqIEl0IGlzIHBvc3NpYmxlIHRvIHVzZSB0aGlzIGZ1bmN0aW9uIHRvIG1lcmdlIEFWYWxzIHRvIG9wdGltaXplIHRoZSBhbmFseXplci5cbiAqIEBwYXJhbSB7c3RyaW5nfG51bGx9IHByb3AgLSBudWxsIGZvciBjb21wdXRlZCBwcm9wc1xuICogQHBhcmFtIHtBVmFsfSBhdmFsXG4gKi9cbk9ialR5cGUucHJvdG90eXBlLnNldFByb3AgPSBmdW5jdGlvbiAocHJvcCwgYXZhbCkge1xuICAgIGlmIChwcm9wID09PSAn4pyWJykge1xuICAgICAgICAvLyDinJYgaXMgdGhlIGJvZ3VzIHByb3BlcnR5IG5hbWUgYWRkZWQgZHVyaW5nIHBhcnNpbmcgZXJyb3IgcmVjb3ZlcnkuXG4gICAgICAgIHJldHVybjtcbiAgICB9XG4gICAgdGhpcy5wcm9wcy5zZXQocHJvcCwgYXZhbCk7XG59O1xuLyoqXG4gKiBUT0RPOiBDaGVjayB0aGlzIGZ1bmN0aW9uJ3MgbmVjZXNzaXR5XG4gKiBAcGFyYW0ge3N0cmluZ30gcHJvcFxuICogQHJldHVybnMge2Jvb2xlYW59XG4gKi9cbk9ialR5cGUucHJvdG90eXBlLmhhc1Byb3AgPSBmdW5jdGlvbiAocHJvcCkge1xuICAgIGlmIChwcm9wID09PSAn4pyWJykgcmV0dXJuIGZhbHNlO1xuICAgIHJldHVybiB0aGlzLnByb3BzLmhhcyhwcm9wKTtcbn07XG4vKipcbiAqIFRPRE86IENoZWNrIHRoaXMgZnVuY3Rpb24ncyBuZWNlc3NpdHlcbiAqIEBwYXJhbSB7VHlwZX0gdHlwZVxuICogQHBhcmFtIHtzdHJpbmd9IHByb3BcbiAqL1xuT2JqVHlwZS5wcm90b3R5cGUuYWRkVHlwZVRvUHJvcCA9IGZ1bmN0aW9uICh0eXBlLCBwcm9wKSB7XG4gICAgaWYgKHByb3AgPT09ICfinJYnKSByZXR1cm47XG4gICAgaWYgKCF0aGlzLnByb3BzLmhhcyhwcm9wKSkge1xuICAgICAgICB0aGlzLnByb3BzLnNldChwcm9wLCBuZXcgQVZhbCk7XG4gICAgfVxuICAgIGlmICh0aGlzLnByb3BzLmdldChwcm9wKS5oYXNUeXBlKHR5cGUpKSByZXR1cm47XG4gICAgdGhpcy5wcm9wcy5nZXQocHJvcCkuYWRkVHlwZSh0eXBlKTtcbn07XG4vKipcbiAqIFRPRE86IENoZWNrIHRoaXMgZnVuY3Rpb24ncyBuZWNlc3NpdHlcbiAqIEBwYXJhbSB7QVZhbH0gYXZhbFxuICogQHBhcmFtIHtzdHJpbmd9IHByb3BcbiAqL1xuT2JqVHlwZS5wcm90b3R5cGUuam9pbkFWYWxUb1Byb3AgPSBmdW5jdGlvbiAoYXZhbCwgcHJvcCkge1xuICAgIHZhciBzZWxmID0gdGhpcztcbiAgICBhdmFsLmdldFR5cGVzKCkuZm9yRWFjaChmdW5jdGlvbiAodHlwZSkge1xuICAgICAgICBzZWxmLmFkZFR5cGVUb1Byb3AodHlwZSwgcHJvcCk7XG4gICAgfSk7XG59O1xuXG4vLyBtYWtlIGFuIE9iaiBmcm9tIHRoZSBnbG9iYWwgc2NvcGVcbmZ1bmN0aW9uIG1rT2JqRnJvbUdsb2JhbFNjb3BlKGdTY29wZSkge1xuICAgIHZhciBnT2JqID0gbmV3IE9ialR5cGUoQVZhbE51bGwsICcqZ2xvYmFsIHNjb3BlKicpO1xuICAgIGdPYmoucHJvcHMgPSBnU2NvcGUudmFyTWFwO1xuICAgIC8vIE92ZXJyaWRlIGdldFByb3AgbWV0aG9kIGZvciBnbG9iYWwgb2JqZWN0XG4gICAgLy8gV2UgaWdub3JlICdyZWFkT25seScgcGFyYW1ldGVyIHRvIGFsd2F5cyByZXR1cm4gaXRzIG93biBwcm9wIEFWYWwgXG4gICAgZ09iai5nZXRQcm9wID0gZnVuY3Rpb24gKHByb3ApIHtcbiAgICAgICAgcmV0dXJuIE9ialR5cGUucHJvdG90eXBlLmdldFByb3AuY2FsbCh0aGlzLCBwcm9wKTtcbiAgICB9O1xuICAgIHJldHVybiBnT2JqO1xufVxuXG4vKipcbiAqIDIuIHByaW1pdGl2ZSB0eXBlc1xuICogQGNvbnN0cnVjdG9yXG4gKiBAcGFyYW0ge3N0cmluZ30gbmFtZVxuICovXG5mdW5jdGlvbiBQcmltVHlwZShuYW1lKSB7XG4gICAgdGhpcy5uYW1lID0gbmFtZTtcbn1cblByaW1UeXBlLnByb3RvdHlwZSA9IE9iamVjdC5jcmVhdGUoVHlwZS5wcm90b3R5cGUpO1xuXG4vKipcbiAqIDMuIGZ1bmN0aW9uIHR5cGVzXG4gKiB0aGUgbmFtZSBpcyB1c2VkIGZvciB0aGUgdHlwZSBvZiB0aGUgaW5zdGFuY2VzIGZyb20gdGhlIGZ1bmN0aW9uXG4gKiBAY29uc3RydWN0b3JcbiAqIEBwYXJhbSB7QVZhbH0gZm5fcHJvdG8gLSBBVmFsIGZvciBjb25zdHJ1Y3RvcidzIC5wcm90b3R5cGVcbiAqIEBwYXJhbSB7c3RyaW5nfSBuYW1lIC0gZ3Vlc3NlZCBuYW1lXG4gKiBAcGFyYW0ge1tzdHJpbmddfSBhcmdOYW1lcyAtIGxpc3Qgb2YgcGFyYW1ldGVyIG5hbWVzXG4gKiBAcGFyYW0ge1Njb3BlfSBzYyAtIGZ1bmN0aW9ucyBzY29wZSBjaGFpbiwgb3IgY2xvc3VyZVxuICogQHBhcmFtIHtub2RlfSBvcmlnaW5Ob2RlIC0gQVNUIG5vZGUgZm9yIHRoZSBmdW5jdGlvblxuICogQHBhcmFtIHtUeXBlfSBhcmdQcm90byAtIHByb3RvdHlwZSBmb3IgYXJndW1lbnRzIG9iamVjdFxuICovXG5mdW5jdGlvbiBGblR5cGUoZm5fcHJvdG8sIG5hbWUsIGFyZ05hbWVzLCBzYywgb3JpZ2luTm9kZSwgYXJnUHJvdG8pIHtcbiAgICBPYmpUeXBlLmNhbGwodGhpcywgZm5fcHJvdG8sIG5hbWUpO1xuICAgIHRoaXMucGFyYW1OYW1lcyA9IGFyZ05hbWVzO1xuICAgIHRoaXMuc2MgPSBzYztcbiAgICB0aGlzLm9yaWdpbk5vZGUgPSBvcmlnaW5Ob2RlO1xuICAgIHRoaXMuYXJnUHJvdG8gPSBhcmdQcm90bztcbiAgICAvLyBmdW5FbnYgOiBDYWxsQ29udGV4dCAtPiBbc2VsZiwgcmV0LCBleGNdXG4gICAgdGhpcy5mdW5FbnYgPSBuZXcgTWFwO1xufVxuRm5UeXBlLnByb3RvdHlwZSA9IE9iamVjdC5jcmVhdGUoT2JqVHlwZS5wcm90b3R5cGUpO1xuXG4vKipcbiAqIGNvbnN0cnVjdCBTdGF0dXMgZm9yIGZ1bmN0aW9uXG4gKiBAcGFyYW0ge0NhbGxDb250ZXh0fSBkZWx0YSAtIGNhbGwgY29udGV4dFxuICogQHJldHVybnMge1tBVmFsLCBBVmFsLCBBVmFsXX0gLSBmb3Igc2VsZiwgcmV0dXJuIGFuZCBleGNlcHRpb24gQVZhbHNcbiAqL1xuRm5UeXBlLnByb3RvdHlwZS5nZXRGdW5FbnYgPSBmdW5jdGlvbiAoZGVsdGEpIHtcbiAgICBpZiAodGhpcy5mdW5FbnYuaGFzKGRlbHRhKSkge1xuICAgICAgICByZXR1cm4gdGhpcy5mdW5FbnYuZ2V0KGRlbHRhKTtcbiAgICB9IGVsc2Uge1xuICAgICAgICB2YXIgdHJpcGxlID0gW25ldyBBVmFsLCBuZXcgQVZhbCwgbmV3IEFWYWxdO1xuICAgICAgICB0aGlzLmZ1bkVudi5zZXQoZGVsdGEsIHRyaXBsZSk7XG4gICAgICAgIHJldHVybiB0cmlwbGU7XG4gICAgfVxufTtcblxuRm5UeXBlLnByb3RvdHlwZS5nZXRBcmd1bWVudHNPYmplY3QgPSBmdW5jdGlvbiAoZGVsdGEpIHtcbiAgICB0aGlzLmFyZ09iak1hcCA9IHRoaXMuYXJnT2JqTWFwIHx8IG5ldyBNYXA7XG4gICAgaWYgKHRoaXMuYXJnT2JqTWFwLmhhcyhkZWx0YSkpIHtcbiAgICAgICAgcmV0dXJuIHRoaXMuYXJnT2JqTWFwLmdldChkZWx0YSk7XG4gICAgfSBlbHNlIHtcbiAgICAgICAgdmFyIGFyZ09iaiA9IG5ldyBPYmpUeXBlKG5ldyBBVmFsKHRoaXMuYXJnUHJvdG8pLCAnKmFyZ3VtZW50cyBvYmplY3QqJyk7XG4gICAgICAgIHRoaXMuYXJnT2JqTWFwLnNldChkZWx0YSwgYXJnT2JqKTtcbiAgICAgICAgcmV0dXJuIGFyZ09iajtcbiAgICB9XG59O1xuXG4vKipcbiAqIGdldCBPYmplY3QgbWFkZSBieSB0aGUgZnVuY3Rpb25cbiAqIFRPRE86IHVzZSBhZGRpdGlvbmFsIGluZm9ybWF0aW9uIHRvIGNyZWF0ZSBtdWx0aXBsZSBpbnN0YW5jZXNcbiAqIEByZXR1cm5zIHtPYmpUeXBlfVxuICovXG5GblR5cGUucHJvdG90eXBlLmdldEluc3RhbmNlID0gZnVuY3Rpb24gKCkge1xuICAgIC8vIG9iakluc3RhbmNlIGlzIHRoZSBvYmplY3QgbWFkZSBieSB0aGUgZnVuY3Rpb2FublxuICAgIGlmICh0aGlzLm9iakluc3RhbmNlKSByZXR1cm4gdGhpcy5vYmpJbnN0YW5jZTtcbiAgICAvLyB3ZSB1bmlmeSBjb25zdHJ1Y3RvcidzIC5wcm90b3R5cGUgYW5kIGluc3RhbmNlJ3MgX19wcm90b19fXG4gICAgdGhpcy5vYmpJbnN0YW5jZSA9IG5ldyBPYmpUeXBlKHRoaXMuZ2V0UHJvcCgncHJvdG90eXBlJykpO1xuICAgIHJldHVybiB0aGlzLm9iakluc3RhbmNlO1xufTtcblxuLyoqIFxuICogNC4gYXJyYXkgdHlwZXNcbiAqIEBjb25zdHJ1Y3RvclxuICovXG5mdW5jdGlvbiBBcnJUeXBlKGFycl9wcm90bykge1xuICAgIE9ialR5cGUuY2FsbCh0aGlzLCBhcnJfcHJvdG8sICdBcnJheScpO1xufVxuQXJyVHlwZS5wcm90b3R5cGUgPSBPYmplY3QuY3JlYXRlKE9ialR5cGUucHJvdG90eXBlKTtcblxuLy8gTWFrZSBwcmltaXRpdmUgdHlwZXNcbnZhciBQcmltTnVtYmVyID0gbmV3IFByaW1UeXBlKCdudW1iZXInKTtcbnZhciBQcmltU3RyaW5nID0gbmV3IFByaW1UeXBlKCdzdHJpbmcnKTtcbnZhciBQcmltQm9vbGVhbiA9IG5ldyBQcmltVHlwZSgnYm9vbGVhbicpO1xuXG4vLyBBYnNOdWxsIHJlcHJlc2VudHMgYWxsIGVtcHR5IGFic3RyYWN0IHZhbHVlcy5cbnZhciBBVmFsTnVsbCA9IG5ldyBBVmFsKCk7XG4vLyBZb3Ugc2hvdWxkIG5vdCBhZGQgYW55IHByb3BlcnRpZXMgdG8gaXQuXG5BVmFsTnVsbC5wcm9wcyA9IG51bGw7XG4vLyBBZGRpbmcgdHlwZXMgYXJlIGlnbm9yZWQuXG5BVmFsTnVsbC5hZGRUeXBlID0gZnVuY3Rpb24gKCkge307XG5cblxuLy8gZXhwb3J0XG5leHBvcnRzLlR5cGUgPSBUeXBlO1xuZXhwb3J0cy5PYmpUeXBlID0gT2JqVHlwZTtcbmV4cG9ydHMuRm5UeXBlID0gRm5UeXBlO1xuZXhwb3J0cy5BcnJUeXBlID0gQXJyVHlwZTtcbmV4cG9ydHMuUHJpbU51bWJlciA9IFByaW1OdW1iZXI7XG5leHBvcnRzLlByaW1TdHJpbmcgPSBQcmltU3RyaW5nO1xuZXhwb3J0cy5QcmltQm9vbGVhbiA9IFByaW1Cb29sZWFuO1xuZXhwb3J0cy5ta09iakZyb21HbG9iYWxTY29wZSA9IG1rT2JqRnJvbUdsb2JhbFNjb3BlO1xuXG5leHBvcnRzLkFWYWwgPSBBVmFsO1xuZXhwb3J0cy5BVmFsTnVsbCA9IEFWYWxOdWxsOyIsIi8vIGltcG9ydCBuZWNlc3NhcnkgbGlicmFyaWVzXG52YXIgYWNvcm4gPSByZXF1aXJlKCdhY29ybi9kaXN0L2Fjb3JuJyk7XG52YXIgYWNvcm5fbG9vc2UgPSByZXF1aXJlKCdhY29ybi9kaXN0L2Fjb3JuX2xvb3NlJyk7XG52YXIgYXV4ID0gcmVxdWlyZSgnLi9hdXgnKTtcbnZhciB0eXBlcyA9IHJlcXVpcmUoJy4vZG9tYWlucy90eXBlcycpO1xudmFyIGNvbnRleHQgPSByZXF1aXJlKCcuL2RvbWFpbnMvY29udGV4dCcpO1xudmFyIHN0YXR1cyA9IHJlcXVpcmUoJy4vZG9tYWlucy9zdGF0dXMnKTtcbnZhciB1dGlsID0gcmVxdWlyZSgndXRpbCcpO1xudmFyIHZhckJsb2NrID0gcmVxdWlyZSgnLi92YXJCbG9jaycpO1xudmFyIGNHZW4gPSByZXF1aXJlKCcuL2NvbnN0cmFpbnQvY0dlbicpO1xudmFyIHZhclJlZnMgPSByZXF1aXJlKCcuL3ZhcnJlZnMnKTtcbnZhciByZXRPY2N1ciA9IHJlcXVpcmUoJy4vcmV0T2NjdXInKTtcblxuZnVuY3Rpb24gYW5hbHl6ZShpbnB1dCwgcmV0QWxsKSB7XG4gICAgLy8gdGhlIFNjb3BlIG9iamVjdCBmb3IgZ2xvYmFsIHNjb3BlXG4gICAgLy8gc2NvcGUuU2NvcGUuZ2xvYmFsU2NvcGUgPSBuZXcgc2NvcGUuU2NvcGUobnVsbCk7XG5cbiAgICAvLyBwYXJzaW5nIGlucHV0IHByb2dyYW1cbiAgICB2YXIgYXN0O1xuICAgIHRyeSB7XG4gICAgICAgIGFzdCA9IGFjb3JuLnBhcnNlKGlucHV0KTtcbiAgICB9IGNhdGNoIChlKSB7XG4gICAgICAgIGFzdCA9IGFjb3JuX2xvb3NlLnBhcnNlX2RhbW1pdChpbnB1dCk7XG4gICAgfVxuXG4gICAgdmFyIG5vZGVBcnJheUluZGV4ZWRCeUxpc3QgPSBhdXguZ2V0Tm9kZUxpc3QoYXN0KTtcblxuICAgIC8vIFNob3cgQVNUIGJlZm9yZSBzY29wZSByZXNvbHV0aW9uXG4gICAgLy8gYXV4LnNob3dVbmZvbGRlZChhc3QpO1xuXG4gICAgdmFyQmxvY2suYW5ub3RhdGVCbG9ja0luZm8oYXN0KTtcbiAgICB2YXIgZ0Jsb2NrID0gYXN0WydAYmxvY2snXTtcbiAgICB2YXIgaW5pdGlhbENvbnRleHQgPSBuZXcgY29udGV4dC5DYWxsU2l0ZUNvbnRleHQ7XG4gICAgdmFyIGdTY29wZSA9IGdCbG9jay5nZXRTY29wZUluc3RhbmNlKG51bGwsIGluaXRpYWxDb250ZXh0KTtcbiAgICB2YXIgZ09iamVjdCA9IHR5cGVzLm1rT2JqRnJvbUdsb2JhbFNjb3BlKGdTY29wZSk7XG4gICAgdmFyIGluaXRTdGF0dXMgPSBuZXcgc3RhdHVzLlN0YXR1cyhcbiAgICAgICAgZ09iamVjdCxcbiAgICAgICAgdHlwZXMuQVZhbE51bGwsXG4gICAgICAgIHR5cGVzLkFWYWxOdWxsLFxuICAgICAgICBpbml0aWFsQ29udGV4dCxcbiAgICAgICAgZ1Njb3BlKTtcbiAgICAvLyB0aGUgcHJvdG90eXBlIG9iamVjdCBvZiBPYmplY3RcbiAgICB2YXIgT2JqUHJvdG8gPSBuZXcgdHlwZXMuT2JqVHlwZShudWxsLCAnT2JqZWN0LnByb3RvdHlwZScpO1xuICAgIHZhciBydENYID0ge1xuICAgICAgICBnbG9iYWxPYmplY3Q6IGdPYmplY3QsXG4gICAgICAgIC8vIHRlbXBvcmFsXG4gICAgICAgIHByb3Rvczoge1xuICAgICAgICAgICAgT2JqZWN0OiBPYmpQcm90byxcbiAgICAgICAgICAgIEZ1bmN0aW9uOiBuZXcgdHlwZXMuT2JqVHlwZShuZXcgdHlwZXMuQVZhbChPYmpQcm90byksICdGdW5jdGlvbi5wcm90b3R5cGUnKSxcbiAgICAgICAgICAgIEFycmF5OiBuZXcgdHlwZXMuT2JqVHlwZShuZXcgdHlwZXMuQVZhbChPYmpQcm90byksICdBcnJheS5wcm90b3R5cGUnKSxcbiAgICAgICAgICAgIFJlZ0V4cDogbmV3IHR5cGVzLk9ialR5cGUobmV3IHR5cGVzLkFWYWwoT2JqUHJvdG8pLCAnUmVnRXhwLnByb3RvdHlwZScpLFxuICAgICAgICAgICAgU3RyaW5nOiBuZXcgdHlwZXMuT2JqVHlwZShuZXcgdHlwZXMuQVZhbChPYmpQcm90byksICdTdHJpbmcucHJvdG90eXBlJyksXG4gICAgICAgICAgICBOdW1iZXI6IG5ldyB0eXBlcy5PYmpUeXBlKG5ldyB0eXBlcy5BVmFsKE9ialByb3RvKSwgJ051bWJlci5wcm90b3R5cGUnKSxcbiAgICAgICAgICAgIEJvb2xlYW46IG5ldyB0eXBlcy5PYmpUeXBlKG5ldyB0eXBlcy5BVmFsKE9ialByb3RvKSwgJ0Jvb2xlYW4ucHJvdG90eXBlJylcbiAgICAgICAgfVxuXG4gICAgfTtcbiAgICBjR2VuLmFkZENvbnN0cmFpbnRzKGFzdCwgaW5pdFN0YXR1cywgcnRDWCk7XG4gICAgdmFyIGNvbnN0cmFpbnRzID0gY0dlbi5jb25zdHJhaW50cztcbiAgICAvL2F1eC5zaG93VW5mb2xkZWQoZ0Jsb2NrQW5kQW5ub3RhdGVkQVNULmFzdCk7XG4gICAgLy8gYXV4LnNob3dVbmZvbGRlZChjb25zdHJhaW50cyk7XG4gICAgLy8gYXV4LnNob3dVbmZvbGRlZChnQmxvY2spO1xuICAgIC8vIGNvbnNvbGUubG9nKHV0aWwuaW5zcGVjdChnQmxvY2ssIHtkZXB0aDogMTB9KSk7XG4gICAgaWYgKHJldEFsbCkge1xuICAgICAgICByZXR1cm4ge2dPYmplY3Q6IGdPYmplY3QsIEFTVDogYXN0LCBnQmxvY2s6IGdCbG9jaywgZ1Njb3BlOiBnU2NvcGV9O1xuICAgIH0gZWxzZSB7XG4gICAgICAgIHJldHVybiBnT2JqZWN0O1xuICAgIH1cbn1cblxuZXhwb3J0cy5hbmFseXplID0gYW5hbHl6ZTtcbmV4cG9ydHMuZmluZElkZW50aWZpZXJBdCA9IHZhclJlZnMuZmluZElkZW50aWZpZXJBdDtcbmV4cG9ydHMuZmluZFZhclJlZnNBdCA9IHZhclJlZnMuZmluZFZhclJlZnNBdDtcbmV4cG9ydHMub25GdW5jdGlvbktleXdvcmQgPSByZXRPY2N1ci5vbkZ1bmN0aW9uS2V5d29yZDtcbmV4cG9ydHMuZmluZFJldHVyblN0YXRlbWVudHMgPSByZXRPY2N1ci5maW5kUmV0dXJuU3RhdGVtZW50czsiLCIvKipcbiAqIENyZWF0ZWQgYnkgc3draW0gb24gMTUuIDcuIDI5LlxuICovXG5cbmNvbnN0IHdhbGsgPSByZXF1aXJlKCdhY29ybi9kaXN0L3dhbGsnKTtcbmNvbnN0IG15V2Fsa2VyID0gcmVxdWlyZSgnLi91dGlsL215V2Fsa2VyJyk7XG5cbi8qKlxuICogQ2hlY2sgd2hldGhlciBnaXZlbiBwb3MgaXMgb24gYSBmdW5jdGlvbiBrZXl3b3JkXG4gKiBAcGFyYW0gYXN0IC0gQVNUIG9mIGEgcHJvZ3JhbVxuICogQHBhcmFtIHBvcyAtIGluZGV4IHBvc2l0aW9uXG4gKiBAcmV0dXJucyB7Kn0gLSBmdW5jdGlvbiBub2RlIG9yIG51bGxcbiAqL1xuZnVuY3Rpb24gb25GdW5jdGlvbktleXdvcmQoYXN0LCBwb3MpIHtcbiAgICBcInVzZSBzdHJpY3RcIjtcblxuICAgIC8vIGZpbmQgZnVuY3Rpb24gbm9kZVxuICAgIGNvbnN0IHdhbGtlciA9IG15V2Fsa2VyLndyYXBXYWxrZXIod2Fsay5iYXNlLFxuICAgICAgICAobm9kZSwgdmIpID0+IHtcbiAgICAgICAgICAgIGlmIChub2RlLnN0YXJ0ID4gcG9zIHx8IG5vZGUuZW5kIDwgcG9zKSB7XG4gICAgICAgICAgICAgICAgcmV0dXJuIGZhbHNlO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgLy8gOCBpcyB0aGUgbGVuZ3RoIG9mICdmdW5jdGlvbicga2V5d29yZFxuICAgICAgICAgICAgaWYgKChub2RlLnR5cGUgPT09ICdGdW5jdGlvbkRlY2xhcmF0aW9uJ1xuICAgICAgICAgICAgICAgIHx8IG5vZGUudHlwZSA9PT0gJ0Z1bmN0aW9uRXhwcmVzc2lvbicpXG4gICAgICAgICAgICAgICAgJiYgKG5vZGUuc3RhcnQgPD0gcG9zICYmIHBvcyA8PSBub2RlLnN0YXJ0ICsgOCkpIHtcbiAgICAgICAgICAgICAgICB0aHJvdyBub2RlO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgcmV0dXJuIHRydWU7XG4gICAgICAgIH0pO1xuXG4gICAgdHJ5IHtcbiAgICAgICAgd2Fsay5yZWN1cnNpdmUoYXN0LCB1bmRlZmluZWQsIHdhbGtlcik7XG4gICAgfSBjYXRjaCAoZSkge1xuICAgICAgICBpZiAoZSAmJiBlLnR5cGUgJiZcbiAgICAgICAgICAgIChlLnR5cGUgPT09ICdGdW5jdGlvbkV4cHJlc3Npb24nXG4gICAgICAgICAgICB8fCBlLnR5cGUgPT09ICdGdW5jdGlvbkRlY2xhcmF0aW9uJykpIHtcbiAgICAgICAgICAgIHJldHVybiBlO1xuICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgICAgdGhyb3cgZTtcbiAgICAgICAgfVxuICAgIH1cbiAgICAvLyBpZGVudGlmaWVyIG5vdCBmb3VuZFxuICAgIHJldHVybiBudWxsO1xufVxuXG4vKipcbiAqIEdpdmVuIGEgZnVuY3Rpb24gbm9kZSwgZmluZCBpdHMgcmV0dXJuIG5vZGVzXG4gKlxuICogQHBhcmFtIGZOb2RlIC0gQVNUIG5vZGUgb2YgYSBmdW5jdGlvbiwgcG9zc2libHkgd2l0aCBubyBhbm5vdGF0aW9uXG4gKiBAcmV0dXJucyB7Kn0gLSBhcnJheSBvZiBBU1Qgbm9kZXNcbiAqL1xuZnVuY3Rpb24gZ2V0UmV0dXJuTm9kZXMoZk5vZGUpIHtcbiAgICBcInVzZSBzdHJpY3RcIjtcbiAgICBjb25zdCByZXRzID0gW107XG4gICAgaWYgKGZOb2RlLnR5cGUgIT09ICdGdW5jdGlvbkV4cHJlc3Npb24nXG4gICAgICAgICYmIGZOb2RlLnR5cGUgIT09ICdGdW5jdGlvbkRlY2xhcmF0aW9uJykge1xuICAgICAgICB0aHJvdyBFcnJvcignZk5vZGUgc2hvdWxkIGJlIGEgZnVuY3Rpb24gbm9kZScpO1xuICAgIH1cblxuICAgIGNvbnN0IHdhbGtlciA9IHdhbGsubWFrZSh7XG4gICAgICAgIFJldHVyblN0YXRlbWVudDogKG5vZGUpID0+IHtcbiAgICAgICAgICAgIHJldHVybiByZXRzLnB1c2gobm9kZSk7XG4gICAgICAgIH0sXG4gICAgICAgIEZ1bmN0aW9uOiAoKSA9PiB7XG4gICAgICAgICAgICAvLyBub3QgdmlzaXQgaW5uZXIgZnVuY3Rpb25zXG4gICAgICAgIH1cbiAgICB9LCB3YWxrLmJhc2UpO1xuXG4gICAgd2Fsay5yZWN1cnNpdmUoZk5vZGUuYm9keSwgdW5kZWZpbmVkLCB3YWxrZXIpO1xuXG4gICAgcmV0dXJuIHJldHM7XG59XG5cbi8qKlxuICogRmluZCByZXR1cm4gbm9kZXMgY29ycmVzcG9uZGluZyB0byB0aGUgcG9zaXRpb25cbiAqIGlmIHRoZSBwb3MgaXMgb24gYSBmdW5jdGlvbiBrZXl3b3JkXG4gKlxuICogQHBhcmFtIGFzdCAtIEFTVCBub2RlIG9mIGEgcHJvZ3JhbSwgcG9zc2libHkgd2l0aCBubyBhbm5vdGF0aW9uXG4gKiBAcGFyYW0gcG9zIC0gY3Vyc29yIHBvc2l0aW9uXG4gKiBAcGFyYW0gaW5jbHVkZUZ1bmN0aW9uS2V5d29yZCAtIHdoZXRoZXIgdG8gaW5jbHVkZSBmdW5jdGlvbiBrZXl3b3JkIHJhbmdlXG4gKiBAcmV0dXJucyB7QXJyYXl9IC0gYXJyYXkgb2YgQVNUIG5vZGVzIG9mIHJldHVybiBzdGF0ZW1lbnRzXG4gKi9cbmZ1bmN0aW9uIGZpbmRSZXR1cm5TdGF0ZW1lbnRzKGFzdCwgcG9zLCBpbmNsdWRlRnVuY3Rpb25LZXl3b3JkKSB7XG4gICAgXCJ1c2Ugc3RyaWN0XCI7XG5cbiAgICBjb25zdCBmTm9kZSA9IG9uRnVuY3Rpb25LZXl3b3JkKGFzdCwgcG9zKTtcbiAgICBpZiAoIWZOb2RlKSB7XG4gICAgICAgIC8vIHBvcyBpcyBub3Qgb24gZnVuY3Rpb24ga2V5d29yZFxuICAgICAgICByZXR1cm4gbnVsbDtcbiAgICB9XG5cbiAgICBjb25zdCByZWZzID0gZ2V0UmV0dXJuTm9kZXMoZk5vZGUpO1xuICAgIGlmIChpbmNsdWRlRnVuY3Rpb25LZXl3b3JkKSB7XG4gICAgICAgIHJlZnMucHVzaCh7c3RhcnQ6IGZOb2RlLnN0YXJ0LCBlbmQ6IGZOb2RlLnN0YXJ0ICsgOH0pO1xuICAgIH1cbiAgICByZXR1cm4gcmVmcztcbn1cblxuZXhwb3J0cy5vbkZ1bmN0aW9uS2V5d29yZCA9IG9uRnVuY3Rpb25LZXl3b3JkO1xuZXhwb3J0cy5maW5kUmV0dXJuU3RhdGVtZW50cyA9IGZpbmRSZXR1cm5TdGF0ZW1lbnRzOyIsIi8qKlxuICpcbiAqIEBwYXJhbSBwcmVOb2RlIC0gQXBwbHkgYmVmb3JlIHZpc2l0aW5nIHRoZSBjdXJyZW50IG5vZGUuXG4gKiBJZiByZXR1cm5zIGZhbHNlLCBkbyBub3QgdmlzaXQgdGhlIG5vZGUuXG4gKiBAcGFyYW0gcG9zdE5vZGUgLSBBcHBseSBhZnRlciB2aXNpdGluZyB0aGUgY3VycmVudCBub2RlLlxuICogSWYgZ2l2ZW4sIHJldHVybiB2YWx1ZXMgYXJlIG92ZXJyaWRkZW4uXG4gKiBAcmV0dXJucyB7Kn0gLSBhIG5ldyB3YWxrZXJcbiAqL1xuZnVuY3Rpb24gd3JhcFdhbGtlcih3YWxrZXIsIHByZU5vZGUsIHBvc3ROb2RlKSB7XG4gICAgY29uc3QgcmV0V2Fsa2VyID0ge307XG4gICAgLy8gd3JhcHBpbmcgZWFjaCBmdW5jdGlvbiBwcmVOb2RlIGFuZCBwb3N0Tm9kZVxuICAgIGZvciAobGV0IG5vZGVUeXBlIGluIHdhbGtlcikge1xuICAgICAgICBpZiAoIXdhbGtlci5oYXNPd25Qcm9wZXJ0eShub2RlVHlwZSkpIHtcbiAgICAgICAgICAgIGNvbnRpbnVlO1xuICAgICAgICB9XG4gICAgICAgIHJldFdhbGtlcltub2RlVHlwZV0gPSAobm9kZSwgc3QsIGMpID0+IHtcbiAgICAgICAgICAgIGxldCByZXQ7XG4gICAgICAgICAgICBpZiAoIXByZU5vZGUgfHwgcHJlTm9kZShub2RlLCBzdCwgYykpIHtcbiAgICAgICAgICAgICAgICByZXQgPSB3YWxrZXJbbm9kZVR5cGVdKG5vZGUsIHN0LCBjKTtcbiAgICAgICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgICAgICAgcmV0dXJuO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgaWYgKHBvc3ROb2RlKSB7XG4gICAgICAgICAgICAgICAgcmV0ID0gcG9zdE5vZGUobm9kZSwgc3QsIGMpO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgcmV0dXJuIHJldDtcbiAgICAgICAgfVxuICAgIH1cbiAgICByZXR1cm4gcmV0V2Fsa2VyO1xufVxuXG5leHBvcnRzLndyYXBXYWxrZXIgPSB3cmFwV2Fsa2VyOyIsIi8qXG4gSmF2YVNjcmlwdOuKlCBnbG9iYWwsIGZ1bmN0aW9uIGJsb2NrLCBjYXRjaCBibG9ja+yXkCDrs4DsiJjqsIAg64us66aw64ukLlxuIEVTNuuKlCDsnbzrsJggYmxvY2vsl5Drj4Qg64us66aw64ukLlxuXG4gVmFyQmxvY2vripQg6rCBIGJsb2Nr7JeQIOuLrOumsCDrs4DsiJjrk6TsnYQg64KY7YOA64K464ukLlxuIC0gcGFyZW4gICAgICA6IEJsb2NrVmFycywg67CU6rmlIGJsb2Nr7J2EIOuCmO2DgOuCtOuKlCDqsJ3ssrRcbiAtIG9yaWdpbkxhYmVsOiBudW1iZXIsIO2VtOuLuSBCbG9ja1ZhcnPqsIAg7ISg7Ja465CcIEFTVCBub2Rl7J2YIEBsYWJlbFxuICAgIG9yaWdpbuydtCDrkKAg7IiYIOyeiOuKlCBub2Rl64qUXG4gICAgRnVuY3Rpb24uYm9keSwgQ2F0Y2hDbGF1c2UuYmxvY2sg65GQ6rCA7KeA64ukLlxuICAgIOuRkOqwgOyngCDrqqjrkZAgQmxvY2tTdGF0ZW1lbnTsnbTri6QuXG4gLSBpc0NhdGNoICAgIDogYm9vbGVhbixcbiAgICogdHJ1ZSAgLT4gY2F0Y2ggYmxvY2tcbiAgICogZmFsc2UgLT4gZnVuY3Rpb24gYmxvY2ssIG9yIGdsb2JhbFxuXG4gLSBwYXJhbVZhck5hbWVzIDog66ek6rCc67OA7IiYIOydtOumhCDrqqnroZ0sIOunpOqwnCDrs4DsiJgg7Iic7ISc64yA66GcXG4gLSBsb2NhbFZhck5hbWVzIDog7KeA7JetIOuzgOyImCDsnbTrpoQg66qp66GdLCDsiJzshJwg66y07J2Y66+4XG4gICAgYXJndW1lbnRz66W8IOyCrOyaqe2VmOuKlCDqsr3smrAgbG9jYWxWYXJOYW1lc+yXkCDrk7HsnqXtlZjqs6AsXG4gICAgYXJndW1lbnRzIG9iamVjdOulvCDsgqzsmqntlZjrqbQgdXNlQXJndW1lbnRzT2JqZWN0ID09IHRydWVcblxuIC0gKG9wdGlvbmFsKSB1c2VBcmd1bWVudHNPYmplY3Q6IGJvb2xlYW5cbiAgICDtlajsiJggYm9keSBibG9ja+yduCDqsr3smrDsl5Drp4wg7IKs7JqpIOqwgOuKpVxuICAgICogdHJ1ZSAgOiBhcmd1bWVudHMgb2JqZWN06rCAIOyCrOyaqeuQmOyXiOuLpC5cbiAgICAgIOymiSDtlajsiJggYm9keeyXkOyEnCDrs4DsiJggYXJndW1lbnRz66W8IOyEoOyWuCDsl4bsnbQg7IKs7Jqp7ZaI64ukLlxuICAgICAg7J20IOqyveyasCwgYXJndW1lbnRz64qUIO2VqOyImOydmCDsp4Dsl60g67OA7IiY66GcIOuTseuhneuQnOuLpC5cbiAgICAqIGZhbHNlIOyduCDqsr3smrDripQg7JeG64ukLiDqt7jrn7TqsbDrqbQg7JWE7JiIIOuzgOyImCDsnpDssrTqsIAg7JeG64ukLlxuXG4gLSB1c2VkVmFyaWFibGVzIDog6rCBIGJsb2Nr7J2YIOunpOqwnOuzgOyImCwg7KeA7Jet67OA7IiYIOykkVxuICAg7IKs7Jqp65CY64qUIOychOy5mOqwgCDsnojripQg6rKD65Ok7J2YIOuqqeuhnVxuXG4gLSBpbnN0YW5jZXMgOiBEZWx0YSAtPiBWYXJCbG9ja+ydmCDrs4DsiJjrk6QgLT4gQVZhbFxuICAgZ2V0SW5zdGFuY2UoZGVsdGEpIOulvCDthrXtlbQg6rCZ7J2AIGRlbHRh64qUIOqwmeydgCBtYXBwaW5nIOyjvOqyjCDrp4zrk6xcblxuIC0gc2NvcGVJbnN0YW5jZXMgOiBbU2NvcGVdXG4gICDtmITsnqwgVmFyQmxvY2vsnYQg66eI7KeA66eJ7Jy866GcIO2VmOuKlCBTY29wZeulvCDrqqjrkZAg66qo7J2A64ukLlxuICAgZ2V0U2NvcGVJbnN0YW5jZShkZWx0YSwgcGFyZW4pIOydhCDthrXtlbQg6rCZ7J2AIHNjb3BlIGNoYWlu7J2AXG4gICDqsJnsnYAg6rCd7LK06rCAIOuQmOuPhOuhnSDrp4zrk6Dri6QuXG4qL1xuJ3VzZSBzdHJpY3QnO1xuXG52YXIgdHlwZXMgPSByZXF1aXJlKCcuL2RvbWFpbnMvdHlwZXMnKTtcbnZhciB3YWxrID0gcmVxdWlyZSgnYWNvcm4vZGlzdC93YWxrJyk7XG52YXIgYXV4ID0gcmVxdWlyZSgnLi9hdXgnKTtcblxuZnVuY3Rpb24gVmFyQmxvY2socGFyZW4sIG9yaWdpbk5vZGUsIGlzQ2F0Y2gpIHtcbiAgICB0aGlzLnBhcmVuID0gcGFyZW47XG4gICAgdGhpcy5vcmlnaW5Ob2RlID0gb3JpZ2luTm9kZTtcbiAgICB0aGlzLm9yaWdpbkxhYmVsID0gb3JpZ2luTm9kZVsnQGxhYmVsJ107XG4gICAgdGhpcy5pc0NhdGNoID0gaXNDYXRjaDtcbiAgICB0aGlzLnBhcmFtVmFyTmFtZXMgPSBbXTtcbiAgICB0aGlzLmxvY2FsVmFyTmFtZXMgPSBbXTtcblxuICAgIHRoaXMudXNlZFZhcmlhYmxlcyA9IFtdO1xuICAgIC8vIHRoaXMudXNlQXJndW1lbnRzT2JqZWN0XG4gICAgdGhpcy5pbnN0YW5jZXMgPSBPYmplY3QuY3JlYXRlKG51bGwpO1xuICAgIHRoaXMuc2NvcGVJbnN0YW5jZXMgPSBbXTtcbn1cblxuVmFyQmxvY2sucHJvdG90eXBlID0gT2JqZWN0LmNyZWF0ZShudWxsKTtcblxuVmFyQmxvY2sucHJvdG90eXBlLmlzR2xvYmFsID0gZnVuY3Rpb24gKCkge1xuICAgIHJldHVybiB0aGlzLnBhcmVuID09IG51bGw7XG59O1xuVmFyQmxvY2sucHJvdG90eXBlLmlzRnVuY3Rpb24gPSBmdW5jdGlvbiAoKSB7XG4gICAgcmV0dXJuIHRoaXMucGFyZW4gIT0gbnVsbCAmJiB0aGlzLmxvY2FsVmFyTmFtZXMgIT0gbnVsbDtcbn07XG5WYXJCbG9jay5wcm90b3R5cGUuaXNDYXRjaEJsb2NrID0gZnVuY3Rpb24gKCkge1xuICAgIHJldHVybiB0aGlzLmlzQ2F0Y2g7XG59O1xuXG5WYXJCbG9jay5wcm90b3R5cGUuZ2V0TG9jYWxWYXJOYW1lcyA9IGZ1bmN0aW9uICgpIHtcbiAgICByZXR1cm4gdGhpcy5sb2NhbFZhck5hbWVzO1xufTtcblZhckJsb2NrLnByb3RvdHlwZS5nZXRQYXJhbVZhck5hbWVzID0gZnVuY3Rpb24gKCkge1xuICAgIHJldHVybiB0aGlzLnBhcmFtVmFyTmFtZXM7XG59O1xuVmFyQmxvY2sucHJvdG90eXBlLmhhc0xvY2FsVmFyID0gZnVuY3Rpb24gKHZhck5hbWUpIHtcbiAgICByZXR1cm4gdGhpcy5sb2NhbFZhck5hbWVzICYmIHRoaXMubG9jYWxWYXJOYW1lcy5pbmRleE9mKHZhck5hbWUpID4gLTE7XG59O1xuVmFyQmxvY2sucHJvdG90eXBlLmhhc1BhcmFtVmFyID0gZnVuY3Rpb24gKHZhck5hbWUpIHtcbiAgICByZXR1cm4gdGhpcy5wYXJhbVZhck5hbWVzLmluZGV4T2YodmFyTmFtZSkgPiAtMTtcbn07XG5WYXJCbG9jay5wcm90b3R5cGUuaGFzVmFyID0gZnVuY3Rpb24gKHZhck5hbWUpIHtcbiAgICByZXR1cm4gdGhpcy5oYXNQYXJhbVZhcih2YXJOYW1lKSB8fCB0aGlzLmhhc0xvY2FsVmFyKHZhck5hbWUpO1xufTtcblxuVmFyQmxvY2sucHJvdG90eXBlLmFkZERlY2xhcmVkTG9jYWxWYXIgPSBmdW5jdGlvbiAodmFyTmFtZSwgaXNGdW5EZWNsKSB7XG4gICAgdmFyIGN1cnJCbG9jayA9IHRoaXM7XG4gICAgLy8gcGVlbCBvZmYgaW5pdGlhbCBjYXRjaCBibG9ja3NcbiAgICAvLyBmb3IgZnVuY3Rpb24gZGVjbCwgc2tpcCBhbnkgY2F0Y2ggYmxvY2tzLFxuICAgIC8vIGZvciB2YXJpYWJsZSBkZWNsLCBza2lwIGNhdGNoIGJsb2NrIHdpdGggZGlmZmVyZW50IHZhck5hbWUuXG4gICAgd2hpbGUgKGN1cnJCbG9jay5pc0NhdGNoQmxvY2soKSAmJlxuICAgICAgICAgICAoaXNGdW5EZWNsIHx8ICFjdXJyQmxvY2suaGFzUGFyYW1WYXIodmFyTmFtZSkpKSB7XG4gICAgICAgIGN1cnJCbG9jayA9IGN1cnJCbG9jay5wYXJlbjtcbiAgICB9XG4gICAgLy8gaWYgYWxyZWFkeSBhZGRlZCwgZG8gbm90IGFkZFxuICAgIGlmICghY3VyckJsb2NrLmhhc1Zhcih2YXJOYW1lKSkge1xuICAgICAgICBjdXJyQmxvY2subG9jYWxWYXJOYW1lcy5wdXNoKHZhck5hbWUpO1xuICAgIH1cbiAgICAvLyByZXR1cm5zIHRoZSBibG9jayBvYmplY3QgdGhhdCBjb250YWlucyB0aGUgdmFyaWFibGVcbiAgICByZXR1cm4gY3VyckJsb2NrO1xufTtcblZhckJsb2NrLnByb3RvdHlwZS5hZGRQYXJhbVZhciA9IGZ1bmN0aW9uICh2YXJOYW1lKSB7XG4gICAgdGhpcy5wYXJhbVZhck5hbWVzLnB1c2godmFyTmFtZSk7XG59O1xuVmFyQmxvY2sucHJvdG90eXBlLmZpbmRWYXJJbkNoYWluID0gZnVuY3Rpb24gKHZhck5hbWUpIHtcbiAgICB2YXIgY3VyckJsb2NrID0gdGhpcztcbiAgICB3aGlsZSAoY3VyckJsb2NrICYmIGN1cnJCbG9jay5wYXJlbiAmJiAhY3VyckJsb2NrLmhhc1Zhcih2YXJOYW1lKSkge1xuICAgICAgICBjdXJyQmxvY2sgPSBjdXJyQmxvY2sucGFyZW47XG4gICAgfVxuICAgIC8vIGlmIG5vdCBmb3VuZCwgaXQgd2lsbCByZXR1cm4gdGhlIGdsb2JhbFxuICAgIHJldHVybiBjdXJyQmxvY2s7XG59O1xuXG5WYXJCbG9jay5wcm90b3R5cGUuYWRkVXNlZFZhciA9IGZ1bmN0aW9uICh2YXJOYW1lKSB7XG4gICAgaWYgKHRoaXMudXNlZFZhcmlhYmxlcy5pbmRleE9mKHZhck5hbWUpID09PSAtMSkge1xuICAgICAgICB0aGlzLnVzZWRWYXJpYWJsZXMucHVzaCh2YXJOYW1lKTtcbiAgICB9XG59O1xuVmFyQmxvY2sucHJvdG90eXBlLmdldFVzZWRWYXJOYW1lcyA9IGZ1bmN0aW9uICgpIHtcbiAgICByZXR1cm4gdGhpcy51c2VkVmFyaWFibGVzO1xufTtcblZhckJsb2NrLnByb3RvdHlwZS5pc1VzZWRWYXIgPSBmdW5jdGlvbiAodmFyTmFtZSkge1xuICAgIHJldHVybiB0aGlzLnVzZWRWYXJpYWJsZXMuaW5kZXhPZih2YXJOYW1lKSA+IC0xO1xufTtcblxuLy8gcmV0dXJucyBhIG1hcHBpbmdcblZhckJsb2NrLnByb3RvdHlwZS5nZXRJbnN0YW5jZSA9IGZ1bmN0aW9uIChkZWx0YSkge1xuICAgIGlmICh0aGlzLmluc3RhbmNlc1tkZWx0YV0pIHtcbiAgICAgICAgcmV0dXJuIHRoaXMuaW5zdGFuY2VzW2RlbHRhXTtcbiAgICB9XG4gICAgLy8gY29uc3RydWN0IFZhck1hcFxuICAgIHZhciB2YXJNYXAgPSBuZXcgTWFwKCk7XG4gICAgdmFyIHZhck5hbWVzID0gdGhpcy5nZXRQYXJhbVZhck5hbWVzKCkuY29uY2F0KHRoaXMuZ2V0TG9jYWxWYXJOYW1lcygpKTtcblxuICAgIGZvciAodmFyIGkgPSAwOyBpIDwgdmFyTmFtZXMubGVuZ3RoOyBpKyspIHtcbiAgICAgICAgdmFyTWFwLnNldCh2YXJOYW1lc1tpXSwgbmV3IHR5cGVzLkFWYWwoKSk7XG4gICAgfVxuICAgIC8vIHJlbWVtYmVyIHRoZSBpbnN0YW5jZVxuICAgIHRoaXMuaW5zdGFuY2VzW2RlbHRhXSA9IHZhck1hcDtcbiAgICByZXR1cm4gdmFyTWFwO1xufTtcbi8vIHJldHVybnMgYW4gYXJyYXlcblZhckJsb2NrLnByb3RvdHlwZS5nZXRQYXJhbUFWYWxzID0gZnVuY3Rpb24gKGRlbHRhKSB7XG4gICAgdmFyIGluc3RhbmNlID0gdGhpcy5nZXRJbnN0YW5jZShkZWx0YSk7XG4gICAgdmFyIHBhcmFtcyA9IFtdO1xuICAgIHRoaXMuZ2V0UGFyYW1WYXJOYW1lcygpLmZvckVhY2goZnVuY3Rpb24gKG5hbWUpIHtcbiAgICAgICAgcGFyYW1zLnB1c2goaW5zdGFuY2VbYXV4LmludGVybmFsTmFtZShuYW1lKV0pO1xuICAgIH0pO1xuICAgIHJldHVybiBwYXJhbXM7XG59O1xuLy8gcmV0dXJucyBhbiBBVmFsXG5WYXJCbG9jay5wcm90b3R5cGUuZ2V0QXJndW1lbnRzQVZhbCA9IGZ1bmN0aW9uIChkZWx0YSkge1xuICAgIGlmICghdGhpcy51c2VBcmd1bWVudHNPYmplY3QpIHtcbiAgICAgICAgdGhyb3cgbmV3IEVycm9yKCdOb3QgZm9yIHRoaXMgVmFyQmxvY2snKTtcbiAgICB9XG4gICAgcmV0dXJuIHRoaXMuZ2V0SW5zdGFuY2UoZGVsdGEpW2F1eC5pbnRlcm5hbE5hbWUoJ2FyZ3VtZW50cycpXTtcbn07XG5cbi8vIGdldCBhIFNjb3BlIGluc3RhbmNlXG5WYXJCbG9jay5wcm90b3R5cGUuZ2V0U2NvcGVJbnN0YW5jZSA9IGZ1bmN0aW9uIChwYXJlbiwgZGVsdGEpIHtcbiAgICB2YXIgdmFyTWFwID0gdGhpcy5nZXRJbnN0YW5jZShkZWx0YSk7XG4gICAgdmFyIGZvdW5kID0gbnVsbDtcblxuICAgIHRoaXMuc2NvcGVJbnN0YW5jZXMuZm9yRWFjaChmdW5jdGlvbiAoc2MpIHtcbiAgICAgICAgaWYgKHNjLnBhcmVuID09PSBwYXJlbiAmJiBzYy52YXJNYXAgPT09IHZhck1hcCkgZm91bmQgPSBzYztcbiAgICB9KTtcblxuICAgIGlmIChmb3VuZCkge1xuICAgICAgICByZXR1cm4gZm91bmQ7XG4gICAgfSBlbHNlIHtcbiAgICAgICAgdmFyIG5ld1Njb3BlSW5zdGFuY2UgPSBuZXcgU2NvcGUocGFyZW4sIHZhck1hcCwgdGhpcyk7XG4gICAgICAgIHRoaXMuc2NvcGVJbnN0YW5jZXMucHVzaChuZXdTY29wZUluc3RhbmNlKTtcbiAgICAgICAgcmV0dXJuIG5ld1Njb3BlSW5zdGFuY2U7XG4gICAgfVxufTtcblxudmFyIGRlY2xhcmVkVmFyaWFibGVGaW5kZXIgPSB3YWxrLm1ha2Uoe1xuICAgRnVuY3Rpb246IGZ1bmN0aW9uIChub2RlLCBjdXJyQmxvY2ssIGMpIHtcbiAgICAgICAgdmFyIHBhcmVuQmxvY2sgPSBjdXJyQmxvY2s7XG4gICAgICAgIGlmIChub2RlLmlkKSB7XG4gICAgICAgICAgICB2YXIgZnVuY05hbWUgPSBub2RlLmlkLm5hbWU7XG4gICAgICAgICAgICBwYXJlbkJsb2NrID0gY3VyckJsb2NrLmFkZERlY2xhcmVkTG9jYWxWYXIoZnVuY05hbWUsIHRydWUpO1xuICAgICAgICB9XG4gICAgICAgIC8vIGNyZWF0ZSBhIFZhckJsb2NrIGZvciBmdW5jdGlvblxuICAgICAgICB2YXIgZnVuY0Jsb2NrID0gbmV3IFZhckJsb2NrKHBhcmVuQmxvY2ssIG5vZGUpO1xuICAgICAgICBub2RlLmJvZHlbJ0BibG9jayddID0gZnVuY0Jsb2NrO1xuICAgICAgICAvLyBhZGQgZnVuY3Rpb24gcGFyYW1ldGVycyB0byB0aGUgc2NvcGVcbiAgICAgICAgZm9yICh2YXIgaSA9IDA7IGkgPCBub2RlLnBhcmFtcy5sZW5ndGg7IGkrKykge1xuICAgICAgICAgICAgdmFyIHBhcmFtTmFtZSA9IG5vZGUucGFyYW1zW2ldLm5hbWU7XG4gICAgICAgICAgICBmdW5jQmxvY2suYWRkUGFyYW1WYXIocGFyYW1OYW1lKTtcbiAgICAgICAgfVxuICAgICAgICBjKG5vZGUuYm9keSwgZnVuY0Jsb2NrLCB1bmRlZmluZWQpO1xuICAgIH0sXG4gICAgVmFyaWFibGVEZWNsYXJhdGlvbjogZnVuY3Rpb24gKG5vZGUsIGN1cnJCbG9jaywgYykge1xuICAgICAgICBmb3IgKHZhciBpID0gMDsgaSA8IG5vZGUuZGVjbGFyYXRpb25zLmxlbmd0aDsgaSsrKSB7XG4gICAgICAgICAgICB2YXIgZGVjbCA9IG5vZGUuZGVjbGFyYXRpb25zW2ldO1xuICAgICAgICAgICAgdmFyIG5hbWUgPSBkZWNsLmlkLm5hbWU7XG4gICAgICAgICAgICBjdXJyQmxvY2suYWRkRGVjbGFyZWRMb2NhbFZhcihuYW1lKTtcbiAgICAgICAgfVxuICAgICAgICBpZiAoZGVjbC5pbml0KSBjKGRlY2wuaW5pdCwgY3VyckJsb2NrLCB1bmRlZmluZWQpO1xuICAgIH0sXG4gICAgVHJ5U3RhdGVtZW50OiBmdW5jdGlvbiAobm9kZSwgY3VyclNjb3BlLCBjKSB7XG4gICAgICAgIGMobm9kZS5ibG9jaywgY3VyclNjb3BlLCB1bmRlZmluZWQpO1xuICAgICAgICBpZiAobm9kZS5oYW5kbGVyKSB7XG4gICAgICAgICAgICBjKG5vZGUuaGFuZGxlciwgY3VyclNjb3BlLCB1bmRlZmluZWQpO1xuICAgICAgICB9XG4gICAgICAgIGlmIChub2RlLmZpbmFsaXplcikge1xuICAgICAgICAgICAgYyhub2RlLmZpbmFsaXplciwgY3VyclNjb3BlLCB1bmRlZmluZWQpO1xuICAgICAgICB9XG4gICAgfSxcbiAgICBDYXRjaENsYXVzZTogZnVuY3Rpb24gKG5vZGUsIGN1cnJCbG9jaywgYykge1xuICAgICAgICB2YXIgY2F0Y2hCbG9jayA9IG5ldyBWYXJCbG9jayhjdXJyQmxvY2ssIG5vZGUsIHRydWUpO1xuICAgICAgICBjYXRjaEJsb2NrLmFkZFBhcmFtVmFyKG5vZGUucGFyYW0ubmFtZSk7XG4gICAgICAgIG5vZGUuYm9keVsnQGJsb2NrJ10gPSBjYXRjaEJsb2NrO1xuICAgICAgICBjKG5vZGUuYm9keSwgY2F0Y2hCbG9jaywgdW5kZWZpbmVkKTtcbiAgICB9XG59KTtcblxuLy8gRm9yIHZhcmlhYmxlcyBpbiBnbG9iYWwgYW5kIGFyZ3VtZW50cyBpbiBmdW5jdGlvbnNcbnZhciB2YXJpYWJsZVVzYWdlQ29sbGVjdG9yID0gd2Fsay5tYWtlKHtcbiAgICBJZGVudGlmaWVyOiBmdW5jdGlvbiAobm9kZSwgY3VyckJsb2NrLCBjKSB7XG4gICAgICAgIHZhciBjb250YWluaW5nQmxvY2ssIHZhck5hbWUgPSBub2RlLm5hbWU7XG4gICAgICAgIGlmICh2YXJOYW1lICE9PSAnYXJndW1lbnRzJykge1xuICAgICAgICAgICAgY29udGFpbmluZ0Jsb2NrID0gY3VyckJsb2NrLmZpbmRWYXJJbkNoYWluKHZhck5hbWUpO1xuICAgICAgICAgICAgaWYgKGNvbnRhaW5pbmdCbG9jay5pc0dsb2JhbCgpKSB7XG4gICAgICAgICAgICAgICAgY29udGFpbmluZ0Jsb2NrLmFkZERlY2xhcmVkTG9jYWxWYXIodmFyTmFtZSk7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBjb250YWluaW5nQmxvY2suYWRkVXNlZFZhcih2YXJOYW1lKTtcbiAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICAgIC8vIHZhck5hbWUgPT0gJ2FyZ3VtZW50cydcbiAgICAgICAgICAgIGNvbnRhaW5pbmdCbG9jayA9IGN1cnJCbG9jaztcbiAgICAgICAgICAgIHdoaWxlIChjb250YWluaW5nQmxvY2suaXNDYXRjaEJsb2NrKCkgJiZcbiAgICAgICAgICAgICAgICAgICAgIWNvbnRhaW5pbmdCbG9jay5oYXNQYXJhbVZhcih2YXJOYW1lKSkge1xuICAgICAgICAgICAgICAgIGNvbnRhaW5pbmdCbG9jayA9IGNvbnRhaW5pbmdCbG9jay5wYXJlbjtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGlmIChjb250YWluaW5nQmxvY2suaGFzVmFyKHZhck5hbWUpKSB7XG4gICAgICAgICAgICAgICAgLy8gYXJndW1lbnRzIGlzIGV4cGxpY2l0bHkgZGVjbGFyZWRcbiAgICAgICAgICAgICAgICBjb250YWluaW5nQmxvY2suYWRkVXNlZFZhcih2YXJOYW1lKTtcbiAgICAgICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgICAgICAgLy8gYXJndW1lbnRzIGlzIG5vdCBleHBsaWNpdGx5IGRlY2xhcmVkXG4gICAgICAgICAgICAgICAgLy8gYWRkIGl0IGFzIGxvY2FsIHZhcmlhYmxlXG4gICAgICAgICAgICAgICAgY29udGFpbmluZ0Jsb2NrLmFkZERlY2xhcmVkTG9jYWxWYXIodmFyTmFtZSk7XG4gICAgICAgICAgICAgICAgLy8gYWxzbyBpdCBpcyB1c2VkXG4gICAgICAgICAgICAgICAgY29udGFpbmluZ0Jsb2NrLmFkZFVzZWRWYXIodmFyTmFtZSk7XG4gICAgICAgICAgICAgICAgaWYgKGNvbnRhaW5pbmdCbG9jay5pc0Z1bmN0aW9uKCkpIHtcbiAgICAgICAgICAgICAgICAgICAgY29udGFpbmluZ0Jsb2NrLnVzZUFyZ3VtZW50c09iamVjdCA9IHRydWU7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgfVxuICAgICAgICB9XG4gICAgfSxcblxuICAgIFJldHVyblN0YXRlbWVudDogZnVuY3Rpb24gKG5vZGUsIGN1cnJCbG9jaywgYykge1xuICAgICAgICB2YXIgZnVuY3Rpb25CbG9jayA9IGN1cnJCbG9jaztcbiAgICAgICAgd2hpbGUgKGZ1bmN0aW9uQmxvY2suaXNDYXRjaEJsb2NrKCkpIHtcbiAgICAgICAgICAgIGZ1bmN0aW9uQmxvY2sgPSBmdW5jdGlvbkJsb2NrLnBhcmVuO1xuICAgICAgICB9XG4gICAgICAgIGlmICghZnVuY3Rpb25CbG9jay5pc0dsb2JhbCgpICYmIG5vZGUuYXJndW1lbnQgIT09IG51bGwpIHtcbiAgICAgICAgICAgIGZ1bmN0aW9uQmxvY2sudXNlUmV0dXJuV2l0aEFyZ3VtZW50ID0gdHJ1ZTtcbiAgICAgICAgfVxuICAgICAgICBpZiAobm9kZS5hcmd1bWVudCkge1xuICAgICAgICAgICAgYyhub2RlLmFyZ3VtZW50LCBjdXJyQmxvY2ssIHVuZGVmaW5lZCk7XG4gICAgICAgIH1cbiAgICB9LFxuXG4gICAgU2NvcGVCb2R5OiBmdW5jdGlvbiAobm9kZSwgY3VyckJsb2NrLCBjKSB7XG4gICAgICAgIGMobm9kZSwgbm9kZVsnQGJsb2NrJ10gfHwgY3VyckJsb2NrKTtcbiAgICB9XG59KTtcblxuXG5mdW5jdGlvbiBhbm5vdGF0ZUJsb2NrSW5mbyhhc3QsIGdCbG9jaykge1xuICAgIGlmICghZ0Jsb2NrKSB7XG4gICAgICAgIC8vIHdoZW4gZ2xvYmFsIGJsb2NrIGlzIG5vdCBnaXZlbiwgY3JlYXRlXG4gICAgICAgIGdCbG9jayA9IG5ldyBWYXJCbG9jayhudWxsLCBhc3QpO1xuICAgIH1cbiAgICBhc3RbJ0BibG9jayddID0gZ0Jsb2NrO1xuICAgIHdhbGsucmVjdXJzaXZlKGFzdCwgZ0Jsb2NrLCBudWxsLCBkZWNsYXJlZFZhcmlhYmxlRmluZGVyKTtcbiAgICB3YWxrLnJlY3Vyc2l2ZShhc3QsIGdCbG9jaywgbnVsbCwgdmFyaWFibGVVc2FnZUNvbGxlY3Rvcik7XG4gICAgcmV0dXJuIGFzdDtcbn1cblxuLy8gZGVmaW5lIHNjb3BlIG9iamVjdFxuZnVuY3Rpb24gU2NvcGUocGFyZW4sIHZhck1hcCwgdmIpIHtcbiAgICB0aGlzLnBhcmVuID0gcGFyZW47XG4gICAgdGhpcy52YXJNYXAgPSB2YXJNYXA7XG4gICAgdGhpcy52YiA9IHZiO1xufVxuU2NvcGUucHJvdG90eXBlID0gT2JqZWN0LmNyZWF0ZShudWxsKTtcbi8vIGZpbmQgQVZhbCBvZiBhIHZhcmlhYmxlIGluIHRoZSBjaGFpblxuU2NvcGUucHJvdG90eXBlLmdldEFWYWxPZiA9IGZ1bmN0aW9uICh2YXJOYW1lKSB7XG4gICAgdmFyIGN1cnIgPSB0aGlzO1xuICAgIHdoaWxlIChjdXJyICE9IG51bGwpIHtcbiAgICAgICAgaWYgKGN1cnIudmFyTWFwLmhhcyh2YXJOYW1lKSkge1xuICAgICAgICAgICAgcmV0dXJuIGN1cnIudmFyTWFwLmdldCh2YXJOYW1lKTtcbiAgICAgICAgfVxuICAgICAgICBjdXJyID0gY3Vyci5wYXJlbjtcbiAgICB9XG4gICAgdGhyb3cgbmV3IEVycm9yKCdTaG91bGQgaGF2ZSBmb3VuZCB0aGUgdmFyaWFibGUnKTtcbn07XG4vLyByZW1vdmUgaW5pdGlhbCBjYXRjaCBzY29wZXMgZnJvbSB0aGUgY2hhaW5cblNjb3BlLnByb3RvdHlwZS5yZW1vdmVJbml0aWFsQ2F0Y2hCbG9ja3MgPSBmdW5jdGlvbiAoKSB7XG4gICAgdmFyIGN1cnIgPSB0aGlzO1xuICAgIHdoaWxlIChjdXJyLnZiLmlzQ2F0Y2hCbG9jaygpKSB7XG4gICAgICAgIGN1cnIgPSBjdXJyLnBhcmVuO1xuICAgIH1cbiAgICByZXR1cm4gY3Vycjtcbn07XG5cblxuZXhwb3J0cy5WYXJCbG9jayA9IFZhckJsb2NrO1xuZXhwb3J0cy5hbm5vdGF0ZUJsb2NrSW5mbyA9IGFubm90YXRlQmxvY2tJbmZvO1xuZXhwb3J0cy5TY29wZSA9IFNjb3BlO1xuIiwiY29uc3Qgd2FsayA9IHJlcXVpcmUoJ2Fjb3JuL2Rpc3Qvd2FsaycpO1xuY29uc3QgbXlXYWxrZXIgPSByZXF1aXJlKCcuL3V0aWwvbXlXYWxrZXInKTtcblxuLy8gYSB3YWxrZXIgdGhhdCB2aXNpdHMgZWFjaCBpZCB3aXRoIHZhckJsb2NrXG5jb25zdCB2YXJXYWxrZXI9IHdhbGsubWFrZSh7XG4gICAgRnVuY3Rpb246IGZ1bmN0aW9uIChub2RlLCB2YiwgYykge1xuICAgICAgICBjb25zdCBpbm5lclZiID0gbm9kZS5ib2R5WydAYmxvY2snXTtcbiAgICAgICAgaWYgKG5vZGUuaWQpIGMobm9kZS5pZCwgaW5uZXJWYik7XG4gICAgICAgIGZvciAobGV0IGkgPSAwOyBpIDwgbm9kZS5wYXJhbXMubGVuZ3RoOyBpKyspXG4gICAgICAgICAgICBjKG5vZGUucGFyYW1zW2ldLCBpbm5lclZiKTtcbiAgICAgICAgYyhub2RlLmJvZHksIGlubmVyVmIpO1xuICAgIH0sXG4gICAgVHJ5U3RhdGVtZW50OiBmdW5jdGlvbiAobm9kZSwgdmIsIGMpIHtcbiAgICAgICAgYyhub2RlLmJsb2NrLCB2Yik7XG4gICAgICAgIGlmIChub2RlLmhhbmRsZXIpIHtcbiAgICAgICAgICAgIGMobm9kZS5oYW5kbGVyLCB2Yik7XG4gICAgICAgIH1cbiAgICAgICAgaWYgKG5vZGUuZmluYWxpemVyKSB7XG4gICAgICAgICAgICBjKG5vZGUuZmluYWxpemVyLCB2Yik7XG4gICAgICAgIH1cbiAgICB9LFxuICAgIENhdGNoQ2xhdXNlOiBmdW5jdGlvbiAobm9kZSwgdmIsIGMpIHtcbiAgICAgICAgY29uc3QgY2F0Y2hWYiA9IG5vZGUuYm9keVsnQGJsb2NrJ107XG4gICAgICAgIGMobm9kZS5wYXJhbSwgY2F0Y2hWYik7XG4gICAgICAgIGMobm9kZS5ib2R5LCBjYXRjaFZiKTtcbiAgICB9LFxuICAgIFZhcmlhYmxlRGVjbGFyYXRpb246IGZ1bmN0aW9uIChub2RlLCB2YiwgYykge1xuICAgICAgICBmb3IgKGxldCBpID0gMDsgaSA8IG5vZGUuZGVjbGFyYXRpb25zLmxlbmd0aDsgKytpKSB7XG4gICAgICAgICAgICBjb25zdCBkZWNsID0gbm9kZS5kZWNsYXJhdGlvbnNbaV07XG4gICAgICAgICAgICBjKGRlY2wuaWQsIHZiKTtcbiAgICAgICAgICAgIGlmIChkZWNsLmluaXQpIGMoZGVjbC5pbml0LCB2Yik7XG4gICAgICAgIH1cbiAgICB9XG59KTtcblxuZnVuY3Rpb24gZmluZElkZW50aWZpZXJBdChhc3QsIHBvcykge1xuICAgIFwidXNlIHN0cmljdFwiO1xuXG4gICAgZnVuY3Rpb24gRm91bmQobm9kZSwgc3RhdGUpIHtcbiAgICAgICAgdGhpcy5ub2RlID0gbm9kZTtcbiAgICAgICAgdGhpcy5zdGF0ZSA9IHN0YXRlO1xuICAgIH1cblxuICAgIC8vIGZpbmQgdGhlIG5vZGVcbiAgICBjb25zdCB3YWxrZXIgPSBteVdhbGtlci53cmFwV2Fsa2VyKHZhcldhbGtlcixcbiAgICAgICAgKG5vZGUsIHZiKSA9PiB7XG4gICAgICAgICAgICBpZiAobm9kZS5zdGFydCA+IHBvcyB8fCBub2RlLmVuZCA8IHBvcykge1xuICAgICAgICAgICAgICAgIHJldHVybiBmYWxzZTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGlmIChub2RlLnR5cGUgPT09ICdJZGVudGlmaWVyJyAmJiBub2RlLm5hbWUgIT09ICfinJYnKSB7XG4gICAgICAgICAgICAgICAgdGhyb3cgbmV3IEZvdW5kKG5vZGUsIHZiKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIHJldHVybiB0cnVlO1xuICAgICAgICB9KTtcblxuICAgIHRyeSB7XG4gICAgICAgIHdhbGsucmVjdXJzaXZlKGFzdCwgYXN0WydAYmxvY2snXSwgd2Fsa2VyKTtcbiAgICB9IGNhdGNoIChlKSB7XG4gICAgICAgIGlmIChlIGluc3RhbmNlb2YgRm91bmQpIHtcbiAgICAgICAgICAgIHJldHVybiBlO1xuICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgICAgdGhyb3cgZTtcbiAgICAgICAgfVxuICAgIH1cbiAgICAvLyBpZGVudGlmaWVyIG5vdCBmb3VuZFxuICAgIHJldHVybiBudWxsO1xufVxuXG4vKipcbiAqXG4gKiBAcGFyYW0gYXN0IC0gc2NvcGUgYW5ub3RhdGVkIEFTVFxuICogQHBhcmFtIHtudW1iZXJ9IHBvcyAtIGNoYXJhY3RlciBwb3NpdGlvblxuICogQHJldHVybnMgeyp9IC0gYXJyYXkgb2YgQVNUIG5vZGVzXG4gKi9cbmZ1bmN0aW9uIGZpbmRWYXJSZWZzQXQoYXN0LCBwb3MpIHtcbiAgICBcInVzZSBzdHJpY3RcIjtcbiAgICBjb25zdCBmb3VuZCA9IGZpbmRJZGVudGlmaWVyQXQoYXN0LCBwb3MpO1xuICAgIGlmICghZm91bmQpIHtcbiAgICAgICAgLy8gcG9zIGlzIG5vdCBhdCBhIHZhcmlhYmxlXG4gICAgICAgIHJldHVybiBudWxsO1xuICAgIH1cbiAgICAvLyBmaW5kIHJlZnMgZm9yIHRoZSBpZCBub2RlXG4gICAgY29uc3QgcmVmcyA9IGZpbmRSZWZzVG9WYXJpYWJsZShhc3QsIGZvdW5kKTtcblxuICAgIHJldHVybiByZWZzO1xufVxuXG4vKipcbiAqXG4gKiBAcGFyYW0gYXN0IC0gc2NvcGUgYW5ub3RhdGVkIEFTVFxuICogQHBhcmFtIGZvdW5kIC0gbm9kZSBhbmQgdmFyQmxvY2sgb2YgdGhlIHZhcmlhYmxlXG4gKiBAcmV0dXJucyB7QXJyYXl9IC0gYXJyYXkgb2YgQVNUIG5vZGVzXG4gKi9cbmZ1bmN0aW9uIGZpbmRSZWZzVG9WYXJpYWJsZShhc3QsIGZvdW5kKSB7XG4gICAgXCJ1c2Ugc3RyaWN0XCI7XG4gICAgY29uc3QgdmFyTmFtZSA9IGZvdW5kLm5vZGUubmFtZTtcbiAgICBjb25zdCB2YjEgPSBmb3VuZC5zdGF0ZS5maW5kVmFySW5DaGFpbih2YXJOYW1lKTtcbiAgICBjb25zdCByZWZzID0gW107XG5cbiAgICBjb25zdCB3YWxrZXIgPSB3YWxrLm1ha2Uoe1xuICAgICAgICBJZGVudGlmaWVyOiAobm9kZSwgdmIpID0+IHtcbiAgICAgICAgICAgIGlmIChub2RlLm5hbWUgIT09IHZhck5hbWUpIHJldHVybjtcbiAgICAgICAgICAgIGlmICh2YjEgPT09IHZiLmZpbmRWYXJJbkNoYWluKHZhck5hbWUpKSB7XG4gICAgICAgICAgICAgICAgcmVmcy5wdXNoKG5vZGUpO1xuICAgICAgICAgICAgfVxuICAgICAgICB9XG4gICAgfSwgdmFyV2Fsa2VyKTtcblxuICAgIHdhbGsucmVjdXJzaXZlKHZiMS5vcmlnaW5Ob2RlLCB2YjEsIHdhbGtlcik7XG4gICAgcmV0dXJuIHJlZnM7XG59XG5cbmV4cG9ydHMuZmluZElkZW50aWZpZXJBdCA9IGZpbmRJZGVudGlmaWVyQXQ7XG5leHBvcnRzLmZpbmRWYXJSZWZzQXQgPSBmaW5kVmFyUmVmc0F0OyIsIihmdW5jdGlvbihmKXtpZih0eXBlb2YgZXhwb3J0cz09PVwib2JqZWN0XCImJnR5cGVvZiBtb2R1bGUhPT1cInVuZGVmaW5lZFwiKXttb2R1bGUuZXhwb3J0cz1mKCl9ZWxzZSBpZih0eXBlb2YgZGVmaW5lPT09XCJmdW5jdGlvblwiJiZkZWZpbmUuYW1kKXtkZWZpbmUoW10sZil9ZWxzZXt2YXIgZztpZih0eXBlb2Ygd2luZG93IT09XCJ1bmRlZmluZWRcIil7Zz13aW5kb3d9ZWxzZSBpZih0eXBlb2YgZ2xvYmFsIT09XCJ1bmRlZmluZWRcIil7Zz1nbG9iYWx9ZWxzZSBpZih0eXBlb2Ygc2VsZiE9PVwidW5kZWZpbmVkXCIpe2c9c2VsZn1lbHNle2c9dGhpc31nLmFjb3JuID0gZigpfX0pKGZ1bmN0aW9uKCl7dmFyIGRlZmluZSxtb2R1bGUsZXhwb3J0cztyZXR1cm4gKGZ1bmN0aW9uIGUodCxuLHIpe2Z1bmN0aW9uIHMobyx1KXtpZighbltvXSl7aWYoIXRbb10pe3ZhciBhPXR5cGVvZiByZXF1aXJlPT1cImZ1bmN0aW9uXCImJnJlcXVpcmU7aWYoIXUmJmEpcmV0dXJuIGEobywhMCk7aWYoaSlyZXR1cm4gaShvLCEwKTt2YXIgZj1uZXcgRXJyb3IoXCJDYW5ub3QgZmluZCBtb2R1bGUgJ1wiK28rXCInXCIpO3Rocm93IGYuY29kZT1cIk1PRFVMRV9OT1RfRk9VTkRcIixmfXZhciBsPW5bb109e2V4cG9ydHM6e319O3Rbb11bMF0uY2FsbChsLmV4cG9ydHMsZnVuY3Rpb24oZSl7dmFyIG49dFtvXVsxXVtlXTtyZXR1cm4gcyhuP246ZSl9LGwsbC5leHBvcnRzLGUsdCxuLHIpfXJldHVybiBuW29dLmV4cG9ydHN9dmFyIGk9dHlwZW9mIHJlcXVpcmU9PVwiZnVuY3Rpb25cIiYmcmVxdWlyZTtmb3IodmFyIG89MDtvPHIubGVuZ3RoO28rKylzKHJbb10pO3JldHVybiBzfSkoezE6W2Z1bmN0aW9uKF9kZXJlcV8sbW9kdWxlLGV4cG9ydHMpe1xuXG5cbi8vIFRoZSBtYWluIGV4cG9ydGVkIGludGVyZmFjZSAodW5kZXIgYHNlbGYuYWNvcm5gIHdoZW4gaW4gdGhlXG4vLyBicm93c2VyKSBpcyBhIGBwYXJzZWAgZnVuY3Rpb24gdGhhdCB0YWtlcyBhIGNvZGUgc3RyaW5nIGFuZFxuLy8gcmV0dXJucyBhbiBhYnN0cmFjdCBzeW50YXggdHJlZSBhcyBzcGVjaWZpZWQgYnkgW01vemlsbGEgcGFyc2VyXG4vLyBBUEldW2FwaV0uXG4vL1xuLy8gW2FwaV06IGh0dHBzOi8vZGV2ZWxvcGVyLm1vemlsbGEub3JnL2VuLVVTL2RvY3MvU3BpZGVyTW9ua2V5L1BhcnNlcl9BUElcblxuXCJ1c2Ugc3RyaWN0XCI7XG5cbmV4cG9ydHMucGFyc2UgPSBwYXJzZTtcblxuLy8gVGhpcyBmdW5jdGlvbiB0cmllcyB0byBwYXJzZSBhIHNpbmdsZSBleHByZXNzaW9uIGF0IGEgZ2l2ZW5cbi8vIG9mZnNldCBpbiBhIHN0cmluZy4gVXNlZnVsIGZvciBwYXJzaW5nIG1peGVkLWxhbmd1YWdlIGZvcm1hdHNcbi8vIHRoYXQgZW1iZWQgSmF2YVNjcmlwdCBleHByZXNzaW9ucy5cblxuZXhwb3J0cy5wYXJzZUV4cHJlc3Npb25BdCA9IHBhcnNlRXhwcmVzc2lvbkF0O1xuXG4vLyBBY29ybiBpcyBvcmdhbml6ZWQgYXMgYSB0b2tlbml6ZXIgYW5kIGEgcmVjdXJzaXZlLWRlc2NlbnQgcGFyc2VyLlxuLy8gVGhlIGB0b2tlbml6ZWAgZXhwb3J0IHByb3ZpZGVzIGFuIGludGVyZmFjZSB0byB0aGUgdG9rZW5pemVyLlxuXG5leHBvcnRzLnRva2VuaXplciA9IHRva2VuaXplcjtcbmV4cG9ydHMuX19lc01vZHVsZSA9IHRydWU7XG4vLyBBY29ybiBpcyBhIHRpbnksIGZhc3QgSmF2YVNjcmlwdCBwYXJzZXIgd3JpdHRlbiBpbiBKYXZhU2NyaXB0LlxuLy9cbi8vIEFjb3JuIHdhcyB3cml0dGVuIGJ5IE1hcmlqbiBIYXZlcmJla2UsIEluZ3ZhciBTdGVwYW55YW4sIGFuZFxuLy8gdmFyaW91cyBjb250cmlidXRvcnMgYW5kIHJlbGVhc2VkIHVuZGVyIGFuIE1JVCBsaWNlbnNlLlxuLy9cbi8vIEdpdCByZXBvc2l0b3JpZXMgZm9yIEFjb3JuIGFyZSBhdmFpbGFibGUgYXRcbi8vXG4vLyAgICAgaHR0cDovL21hcmlqbmhhdmVyYmVrZS5ubC9naXQvYWNvcm5cbi8vICAgICBodHRwczovL2dpdGh1Yi5jb20vbWFyaWpuaC9hY29ybi5naXRcbi8vXG4vLyBQbGVhc2UgdXNlIHRoZSBbZ2l0aHViIGJ1ZyB0cmFja2VyXVtnaGJ0XSB0byByZXBvcnQgaXNzdWVzLlxuLy9cbi8vIFtnaGJ0XTogaHR0cHM6Ly9naXRodWIuY29tL21hcmlqbmgvYWNvcm4vaXNzdWVzXG4vL1xuLy8gVGhpcyBmaWxlIGRlZmluZXMgdGhlIG1haW4gcGFyc2VyIGludGVyZmFjZS4gVGhlIGxpYnJhcnkgYWxzbyBjb21lc1xuLy8gd2l0aCBhIFtlcnJvci10b2xlcmFudCBwYXJzZXJdW2RhbW1pdF0gYW5kIGFuXG4vLyBbYWJzdHJhY3Qgc3ludGF4IHRyZWUgd2Fsa2VyXVt3YWxrXSwgZGVmaW5lZCBpbiBvdGhlciBmaWxlcy5cbi8vXG4vLyBbZGFtbWl0XTogYWNvcm5fbG9vc2UuanNcbi8vIFt3YWxrXTogdXRpbC93YWxrLmpzXG5cbnZhciBfc3RhdGUgPSBfZGVyZXFfKFwiLi9zdGF0ZVwiKTtcblxudmFyIFBhcnNlciA9IF9zdGF0ZS5QYXJzZXI7XG5cbnZhciBfb3B0aW9ucyA9IF9kZXJlcV8oXCIuL29wdGlvbnNcIik7XG5cbnZhciBnZXRPcHRpb25zID0gX29wdGlvbnMuZ2V0T3B0aW9ucztcblxuX2RlcmVxXyhcIi4vcGFyc2V1dGlsXCIpO1xuXG5fZGVyZXFfKFwiLi9zdGF0ZW1lbnRcIik7XG5cbl9kZXJlcV8oXCIuL2x2YWxcIik7XG5cbl9kZXJlcV8oXCIuL2V4cHJlc3Npb25cIik7XG5cbmV4cG9ydHMuUGFyc2VyID0gX3N0YXRlLlBhcnNlcjtcbmV4cG9ydHMucGx1Z2lucyA9IF9zdGF0ZS5wbHVnaW5zO1xuZXhwb3J0cy5kZWZhdWx0T3B0aW9ucyA9IF9vcHRpb25zLmRlZmF1bHRPcHRpb25zO1xuXG52YXIgX2xvY2F0aW9uID0gX2RlcmVxXyhcIi4vbG9jYXRpb25cIik7XG5cbmV4cG9ydHMuU291cmNlTG9jYXRpb24gPSBfbG9jYXRpb24uU291cmNlTG9jYXRpb247XG5leHBvcnRzLmdldExpbmVJbmZvID0gX2xvY2F0aW9uLmdldExpbmVJbmZvO1xuZXhwb3J0cy5Ob2RlID0gX2RlcmVxXyhcIi4vbm9kZVwiKS5Ob2RlO1xuXG52YXIgX3Rva2VudHlwZSA9IF9kZXJlcV8oXCIuL3Rva2VudHlwZVwiKTtcblxuZXhwb3J0cy5Ub2tlblR5cGUgPSBfdG9rZW50eXBlLlRva2VuVHlwZTtcbmV4cG9ydHMudG9rVHlwZXMgPSBfdG9rZW50eXBlLnR5cGVzO1xuXG52YXIgX3Rva2VuY29udGV4dCA9IF9kZXJlcV8oXCIuL3Rva2VuY29udGV4dFwiKTtcblxuZXhwb3J0cy5Ub2tDb250ZXh0ID0gX3Rva2VuY29udGV4dC5Ub2tDb250ZXh0O1xuZXhwb3J0cy50b2tDb250ZXh0cyA9IF90b2tlbmNvbnRleHQudHlwZXM7XG5cbnZhciBfaWRlbnRpZmllciA9IF9kZXJlcV8oXCIuL2lkZW50aWZpZXJcIik7XG5cbmV4cG9ydHMuaXNJZGVudGlmaWVyQ2hhciA9IF9pZGVudGlmaWVyLmlzSWRlbnRpZmllckNoYXI7XG5leHBvcnRzLmlzSWRlbnRpZmllclN0YXJ0ID0gX2lkZW50aWZpZXIuaXNJZGVudGlmaWVyU3RhcnQ7XG5leHBvcnRzLlRva2VuID0gX2RlcmVxXyhcIi4vdG9rZW5pemVcIikuVG9rZW47XG5cbnZhciBfd2hpdGVzcGFjZSA9IF9kZXJlcV8oXCIuL3doaXRlc3BhY2VcIik7XG5cbmV4cG9ydHMuaXNOZXdMaW5lID0gX3doaXRlc3BhY2UuaXNOZXdMaW5lO1xuZXhwb3J0cy5saW5lQnJlYWsgPSBfd2hpdGVzcGFjZS5saW5lQnJlYWs7XG5leHBvcnRzLmxpbmVCcmVha0cgPSBfd2hpdGVzcGFjZS5saW5lQnJlYWtHO1xudmFyIHZlcnNpb24gPSBcIjEuMi4yXCI7ZXhwb3J0cy52ZXJzaW9uID0gdmVyc2lvbjtcblxuZnVuY3Rpb24gcGFyc2UoaW5wdXQsIG9wdGlvbnMpIHtcbiAgdmFyIHAgPSBwYXJzZXIob3B0aW9ucywgaW5wdXQpO1xuICB2YXIgc3RhcnRQb3MgPSBwLnBvcyxcbiAgICAgIHN0YXJ0TG9jID0gcC5vcHRpb25zLmxvY2F0aW9ucyAmJiBwLmN1clBvc2l0aW9uKCk7XG4gIHAubmV4dFRva2VuKCk7XG4gIHJldHVybiBwLnBhcnNlVG9wTGV2ZWwocC5vcHRpb25zLnByb2dyYW0gfHwgcC5zdGFydE5vZGVBdChzdGFydFBvcywgc3RhcnRMb2MpKTtcbn1cblxuZnVuY3Rpb24gcGFyc2VFeHByZXNzaW9uQXQoaW5wdXQsIHBvcywgb3B0aW9ucykge1xuICB2YXIgcCA9IHBhcnNlcihvcHRpb25zLCBpbnB1dCwgcG9zKTtcbiAgcC5uZXh0VG9rZW4oKTtcbiAgcmV0dXJuIHAucGFyc2VFeHByZXNzaW9uKCk7XG59XG5cbmZ1bmN0aW9uIHRva2VuaXplcihpbnB1dCwgb3B0aW9ucykge1xuICByZXR1cm4gcGFyc2VyKG9wdGlvbnMsIGlucHV0KTtcbn1cblxuZnVuY3Rpb24gcGFyc2VyKG9wdGlvbnMsIGlucHV0KSB7XG4gIHJldHVybiBuZXcgUGFyc2VyKGdldE9wdGlvbnMob3B0aW9ucyksIFN0cmluZyhpbnB1dCkpO1xufVxuXG59LHtcIi4vZXhwcmVzc2lvblwiOjYsXCIuL2lkZW50aWZpZXJcIjo3LFwiLi9sb2NhdGlvblwiOjgsXCIuL2x2YWxcIjo5LFwiLi9ub2RlXCI6MTAsXCIuL29wdGlvbnNcIjoxMSxcIi4vcGFyc2V1dGlsXCI6MTIsXCIuL3N0YXRlXCI6MTMsXCIuL3N0YXRlbWVudFwiOjE0LFwiLi90b2tlbmNvbnRleHRcIjoxNSxcIi4vdG9rZW5pemVcIjoxNixcIi4vdG9rZW50eXBlXCI6MTcsXCIuL3doaXRlc3BhY2VcIjoxOX1dLDI6W2Z1bmN0aW9uKF9kZXJlcV8sbW9kdWxlLGV4cG9ydHMpe1xuaWYgKHR5cGVvZiBPYmplY3QuY3JlYXRlID09PSAnZnVuY3Rpb24nKSB7XG4gIC8vIGltcGxlbWVudGF0aW9uIGZyb20gc3RhbmRhcmQgbm9kZS5qcyAndXRpbCcgbW9kdWxlXG4gIG1vZHVsZS5leHBvcnRzID0gZnVuY3Rpb24gaW5oZXJpdHMoY3Rvciwgc3VwZXJDdG9yKSB7XG4gICAgY3Rvci5zdXBlcl8gPSBzdXBlckN0b3JcbiAgICBjdG9yLnByb3RvdHlwZSA9IE9iamVjdC5jcmVhdGUoc3VwZXJDdG9yLnByb3RvdHlwZSwge1xuICAgICAgY29uc3RydWN0b3I6IHtcbiAgICAgICAgdmFsdWU6IGN0b3IsXG4gICAgICAgIGVudW1lcmFibGU6IGZhbHNlLFxuICAgICAgICB3cml0YWJsZTogdHJ1ZSxcbiAgICAgICAgY29uZmlndXJhYmxlOiB0cnVlXG4gICAgICB9XG4gICAgfSk7XG4gIH07XG59IGVsc2Uge1xuICAvLyBvbGQgc2Nob29sIHNoaW0gZm9yIG9sZCBicm93c2Vyc1xuICBtb2R1bGUuZXhwb3J0cyA9IGZ1bmN0aW9uIGluaGVyaXRzKGN0b3IsIHN1cGVyQ3Rvcikge1xuICAgIGN0b3Iuc3VwZXJfID0gc3VwZXJDdG9yXG4gICAgdmFyIFRlbXBDdG9yID0gZnVuY3Rpb24gKCkge31cbiAgICBUZW1wQ3Rvci5wcm90b3R5cGUgPSBzdXBlckN0b3IucHJvdG90eXBlXG4gICAgY3Rvci5wcm90b3R5cGUgPSBuZXcgVGVtcEN0b3IoKVxuICAgIGN0b3IucHJvdG90eXBlLmNvbnN0cnVjdG9yID0gY3RvclxuICB9XG59XG5cbn0se31dLDM6W2Z1bmN0aW9uKF9kZXJlcV8sbW9kdWxlLGV4cG9ydHMpe1xuLy8gc2hpbSBmb3IgdXNpbmcgcHJvY2VzcyBpbiBicm93c2VyXG5cbnZhciBwcm9jZXNzID0gbW9kdWxlLmV4cG9ydHMgPSB7fTtcbnZhciBxdWV1ZSA9IFtdO1xudmFyIGRyYWluaW5nID0gZmFsc2U7XG5cbmZ1bmN0aW9uIGRyYWluUXVldWUoKSB7XG4gICAgaWYgKGRyYWluaW5nKSB7XG4gICAgICAgIHJldHVybjtcbiAgICB9XG4gICAgZHJhaW5pbmcgPSB0cnVlO1xuICAgIHZhciBjdXJyZW50UXVldWU7XG4gICAgdmFyIGxlbiA9IHF1ZXVlLmxlbmd0aDtcbiAgICB3aGlsZShsZW4pIHtcbiAgICAgICAgY3VycmVudFF1ZXVlID0gcXVldWU7XG4gICAgICAgIHF1ZXVlID0gW107XG4gICAgICAgIHZhciBpID0gLTE7XG4gICAgICAgIHdoaWxlICgrK2kgPCBsZW4pIHtcbiAgICAgICAgICAgIGN1cnJlbnRRdWV1ZVtpXSgpO1xuICAgICAgICB9XG4gICAgICAgIGxlbiA9IHF1ZXVlLmxlbmd0aDtcbiAgICB9XG4gICAgZHJhaW5pbmcgPSBmYWxzZTtcbn1cbnByb2Nlc3MubmV4dFRpY2sgPSBmdW5jdGlvbiAoZnVuKSB7XG4gICAgcXVldWUucHVzaChmdW4pO1xuICAgIGlmICghZHJhaW5pbmcpIHtcbiAgICAgICAgc2V0VGltZW91dChkcmFpblF1ZXVlLCAwKTtcbiAgICB9XG59O1xuXG5wcm9jZXNzLnRpdGxlID0gJ2Jyb3dzZXInO1xucHJvY2Vzcy5icm93c2VyID0gdHJ1ZTtcbnByb2Nlc3MuZW52ID0ge307XG5wcm9jZXNzLmFyZ3YgPSBbXTtcbnByb2Nlc3MudmVyc2lvbiA9ICcnOyAvLyBlbXB0eSBzdHJpbmcgdG8gYXZvaWQgcmVnZXhwIGlzc3Vlc1xucHJvY2Vzcy52ZXJzaW9ucyA9IHt9O1xuXG5mdW5jdGlvbiBub29wKCkge31cblxucHJvY2Vzcy5vbiA9IG5vb3A7XG5wcm9jZXNzLmFkZExpc3RlbmVyID0gbm9vcDtcbnByb2Nlc3Mub25jZSA9IG5vb3A7XG5wcm9jZXNzLm9mZiA9IG5vb3A7XG5wcm9jZXNzLnJlbW92ZUxpc3RlbmVyID0gbm9vcDtcbnByb2Nlc3MucmVtb3ZlQWxsTGlzdGVuZXJzID0gbm9vcDtcbnByb2Nlc3MuZW1pdCA9IG5vb3A7XG5cbnByb2Nlc3MuYmluZGluZyA9IGZ1bmN0aW9uIChuYW1lKSB7XG4gICAgdGhyb3cgbmV3IEVycm9yKCdwcm9jZXNzLmJpbmRpbmcgaXMgbm90IHN1cHBvcnRlZCcpO1xufTtcblxuLy8gVE9ETyhzaHR5bG1hbilcbnByb2Nlc3MuY3dkID0gZnVuY3Rpb24gKCkgeyByZXR1cm4gJy8nIH07XG5wcm9jZXNzLmNoZGlyID0gZnVuY3Rpb24gKGRpcikge1xuICAgIHRocm93IG5ldyBFcnJvcigncHJvY2Vzcy5jaGRpciBpcyBub3Qgc3VwcG9ydGVkJyk7XG59O1xucHJvY2Vzcy51bWFzayA9IGZ1bmN0aW9uKCkgeyByZXR1cm4gMDsgfTtcblxufSx7fV0sNDpbZnVuY3Rpb24oX2RlcmVxXyxtb2R1bGUsZXhwb3J0cyl7XG5tb2R1bGUuZXhwb3J0cyA9IGZ1bmN0aW9uIGlzQnVmZmVyKGFyZykge1xuICByZXR1cm4gYXJnICYmIHR5cGVvZiBhcmcgPT09ICdvYmplY3QnXG4gICAgJiYgdHlwZW9mIGFyZy5jb3B5ID09PSAnZnVuY3Rpb24nXG4gICAgJiYgdHlwZW9mIGFyZy5maWxsID09PSAnZnVuY3Rpb24nXG4gICAgJiYgdHlwZW9mIGFyZy5yZWFkVUludDggPT09ICdmdW5jdGlvbic7XG59XG59LHt9XSw1OltmdW5jdGlvbihfZGVyZXFfLG1vZHVsZSxleHBvcnRzKXtcbihmdW5jdGlvbiAocHJvY2VzcyxnbG9iYWwpe1xuLy8gQ29weXJpZ2h0IEpveWVudCwgSW5jLiBhbmQgb3RoZXIgTm9kZSBjb250cmlidXRvcnMuXG4vL1xuLy8gUGVybWlzc2lvbiBpcyBoZXJlYnkgZ3JhbnRlZCwgZnJlZSBvZiBjaGFyZ2UsIHRvIGFueSBwZXJzb24gb2J0YWluaW5nIGFcbi8vIGNvcHkgb2YgdGhpcyBzb2Z0d2FyZSBhbmQgYXNzb2NpYXRlZCBkb2N1bWVudGF0aW9uIGZpbGVzICh0aGVcbi8vIFwiU29mdHdhcmVcIiksIHRvIGRlYWwgaW4gdGhlIFNvZnR3YXJlIHdpdGhvdXQgcmVzdHJpY3Rpb24sIGluY2x1ZGluZ1xuLy8gd2l0aG91dCBsaW1pdGF0aW9uIHRoZSByaWdodHMgdG8gdXNlLCBjb3B5LCBtb2RpZnksIG1lcmdlLCBwdWJsaXNoLFxuLy8gZGlzdHJpYnV0ZSwgc3VibGljZW5zZSwgYW5kL29yIHNlbGwgY29waWVzIG9mIHRoZSBTb2Z0d2FyZSwgYW5kIHRvIHBlcm1pdFxuLy8gcGVyc29ucyB0byB3aG9tIHRoZSBTb2Z0d2FyZSBpcyBmdXJuaXNoZWQgdG8gZG8gc28sIHN1YmplY3QgdG8gdGhlXG4vLyBmb2xsb3dpbmcgY29uZGl0aW9uczpcbi8vXG4vLyBUaGUgYWJvdmUgY29weXJpZ2h0IG5vdGljZSBhbmQgdGhpcyBwZXJtaXNzaW9uIG5vdGljZSBzaGFsbCBiZSBpbmNsdWRlZFxuLy8gaW4gYWxsIGNvcGllcyBvciBzdWJzdGFudGlhbCBwb3J0aW9ucyBvZiB0aGUgU29mdHdhcmUuXG4vL1xuLy8gVEhFIFNPRlRXQVJFIElTIFBST1ZJREVEIFwiQVMgSVNcIiwgV0lUSE9VVCBXQVJSQU5UWSBPRiBBTlkgS0lORCwgRVhQUkVTU1xuLy8gT1IgSU1QTElFRCwgSU5DTFVESU5HIEJVVCBOT1QgTElNSVRFRCBUTyBUSEUgV0FSUkFOVElFUyBPRlxuLy8gTUVSQ0hBTlRBQklMSVRZLCBGSVRORVNTIEZPUiBBIFBBUlRJQ1VMQVIgUFVSUE9TRSBBTkQgTk9OSU5GUklOR0VNRU5ULiBJTlxuLy8gTk8gRVZFTlQgU0hBTEwgVEhFIEFVVEhPUlMgT1IgQ09QWVJJR0hUIEhPTERFUlMgQkUgTElBQkxFIEZPUiBBTlkgQ0xBSU0sXG4vLyBEQU1BR0VTIE9SIE9USEVSIExJQUJJTElUWSwgV0hFVEhFUiBJTiBBTiBBQ1RJT04gT0YgQ09OVFJBQ1QsIFRPUlQgT1Jcbi8vIE9USEVSV0lTRSwgQVJJU0lORyBGUk9NLCBPVVQgT0YgT1IgSU4gQ09OTkVDVElPTiBXSVRIIFRIRSBTT0ZUV0FSRSBPUiBUSEVcbi8vIFVTRSBPUiBPVEhFUiBERUFMSU5HUyBJTiBUSEUgU09GVFdBUkUuXG5cbnZhciBmb3JtYXRSZWdFeHAgPSAvJVtzZGolXS9nO1xuZXhwb3J0cy5mb3JtYXQgPSBmdW5jdGlvbihmKSB7XG4gIGlmICghaXNTdHJpbmcoZikpIHtcbiAgICB2YXIgb2JqZWN0cyA9IFtdO1xuICAgIGZvciAodmFyIGkgPSAwOyBpIDwgYXJndW1lbnRzLmxlbmd0aDsgaSsrKSB7XG4gICAgICBvYmplY3RzLnB1c2goaW5zcGVjdChhcmd1bWVudHNbaV0pKTtcbiAgICB9XG4gICAgcmV0dXJuIG9iamVjdHMuam9pbignICcpO1xuICB9XG5cbiAgdmFyIGkgPSAxO1xuICB2YXIgYXJncyA9IGFyZ3VtZW50cztcbiAgdmFyIGxlbiA9IGFyZ3MubGVuZ3RoO1xuICB2YXIgc3RyID0gU3RyaW5nKGYpLnJlcGxhY2UoZm9ybWF0UmVnRXhwLCBmdW5jdGlvbih4KSB7XG4gICAgaWYgKHggPT09ICclJScpIHJldHVybiAnJSc7XG4gICAgaWYgKGkgPj0gbGVuKSByZXR1cm4geDtcbiAgICBzd2l0Y2ggKHgpIHtcbiAgICAgIGNhc2UgJyVzJzogcmV0dXJuIFN0cmluZyhhcmdzW2krK10pO1xuICAgICAgY2FzZSAnJWQnOiByZXR1cm4gTnVtYmVyKGFyZ3NbaSsrXSk7XG4gICAgICBjYXNlICclaic6XG4gICAgICAgIHRyeSB7XG4gICAgICAgICAgcmV0dXJuIEpTT04uc3RyaW5naWZ5KGFyZ3NbaSsrXSk7XG4gICAgICAgIH0gY2F0Y2ggKF8pIHtcbiAgICAgICAgICByZXR1cm4gJ1tDaXJjdWxhcl0nO1xuICAgICAgICB9XG4gICAgICBkZWZhdWx0OlxuICAgICAgICByZXR1cm4geDtcbiAgICB9XG4gIH0pO1xuICBmb3IgKHZhciB4ID0gYXJnc1tpXTsgaSA8IGxlbjsgeCA9IGFyZ3NbKytpXSkge1xuICAgIGlmIChpc051bGwoeCkgfHwgIWlzT2JqZWN0KHgpKSB7XG4gICAgICBzdHIgKz0gJyAnICsgeDtcbiAgICB9IGVsc2Uge1xuICAgICAgc3RyICs9ICcgJyArIGluc3BlY3QoeCk7XG4gICAgfVxuICB9XG4gIHJldHVybiBzdHI7XG59O1xuXG5cbi8vIE1hcmsgdGhhdCBhIG1ldGhvZCBzaG91bGQgbm90IGJlIHVzZWQuXG4vLyBSZXR1cm5zIGEgbW9kaWZpZWQgZnVuY3Rpb24gd2hpY2ggd2FybnMgb25jZSBieSBkZWZhdWx0LlxuLy8gSWYgLS1uby1kZXByZWNhdGlvbiBpcyBzZXQsIHRoZW4gaXQgaXMgYSBuby1vcC5cbmV4cG9ydHMuZGVwcmVjYXRlID0gZnVuY3Rpb24oZm4sIG1zZykge1xuICAvLyBBbGxvdyBmb3IgZGVwcmVjYXRpbmcgdGhpbmdzIGluIHRoZSBwcm9jZXNzIG9mIHN0YXJ0aW5nIHVwLlxuICBpZiAoaXNVbmRlZmluZWQoZ2xvYmFsLnByb2Nlc3MpKSB7XG4gICAgcmV0dXJuIGZ1bmN0aW9uKCkge1xuICAgICAgcmV0dXJuIGV4cG9ydHMuZGVwcmVjYXRlKGZuLCBtc2cpLmFwcGx5KHRoaXMsIGFyZ3VtZW50cyk7XG4gICAgfTtcbiAgfVxuXG4gIGlmIChwcm9jZXNzLm5vRGVwcmVjYXRpb24gPT09IHRydWUpIHtcbiAgICByZXR1cm4gZm47XG4gIH1cblxuICB2YXIgd2FybmVkID0gZmFsc2U7XG4gIGZ1bmN0aW9uIGRlcHJlY2F0ZWQoKSB7XG4gICAgaWYgKCF3YXJuZWQpIHtcbiAgICAgIGlmIChwcm9jZXNzLnRocm93RGVwcmVjYXRpb24pIHtcbiAgICAgICAgdGhyb3cgbmV3IEVycm9yKG1zZyk7XG4gICAgICB9IGVsc2UgaWYgKHByb2Nlc3MudHJhY2VEZXByZWNhdGlvbikge1xuICAgICAgICBjb25zb2xlLnRyYWNlKG1zZyk7XG4gICAgICB9IGVsc2Uge1xuICAgICAgICBjb25zb2xlLmVycm9yKG1zZyk7XG4gICAgICB9XG4gICAgICB3YXJuZWQgPSB0cnVlO1xuICAgIH1cbiAgICByZXR1cm4gZm4uYXBwbHkodGhpcywgYXJndW1lbnRzKTtcbiAgfVxuXG4gIHJldHVybiBkZXByZWNhdGVkO1xufTtcblxuXG52YXIgZGVidWdzID0ge307XG52YXIgZGVidWdFbnZpcm9uO1xuZXhwb3J0cy5kZWJ1Z2xvZyA9IGZ1bmN0aW9uKHNldCkge1xuICBpZiAoaXNVbmRlZmluZWQoZGVidWdFbnZpcm9uKSlcbiAgICBkZWJ1Z0Vudmlyb24gPSBwcm9jZXNzLmVudi5OT0RFX0RFQlVHIHx8ICcnO1xuICBzZXQgPSBzZXQudG9VcHBlckNhc2UoKTtcbiAgaWYgKCFkZWJ1Z3Nbc2V0XSkge1xuICAgIGlmIChuZXcgUmVnRXhwKCdcXFxcYicgKyBzZXQgKyAnXFxcXGInLCAnaScpLnRlc3QoZGVidWdFbnZpcm9uKSkge1xuICAgICAgdmFyIHBpZCA9IHByb2Nlc3MucGlkO1xuICAgICAgZGVidWdzW3NldF0gPSBmdW5jdGlvbigpIHtcbiAgICAgICAgdmFyIG1zZyA9IGV4cG9ydHMuZm9ybWF0LmFwcGx5KGV4cG9ydHMsIGFyZ3VtZW50cyk7XG4gICAgICAgIGNvbnNvbGUuZXJyb3IoJyVzICVkOiAlcycsIHNldCwgcGlkLCBtc2cpO1xuICAgICAgfTtcbiAgICB9IGVsc2Uge1xuICAgICAgZGVidWdzW3NldF0gPSBmdW5jdGlvbigpIHt9O1xuICAgIH1cbiAgfVxuICByZXR1cm4gZGVidWdzW3NldF07XG59O1xuXG5cbi8qKlxuICogRWNob3MgdGhlIHZhbHVlIG9mIGEgdmFsdWUuIFRyeXMgdG8gcHJpbnQgdGhlIHZhbHVlIG91dFxuICogaW4gdGhlIGJlc3Qgd2F5IHBvc3NpYmxlIGdpdmVuIHRoZSBkaWZmZXJlbnQgdHlwZXMuXG4gKlxuICogQHBhcmFtIHtPYmplY3R9IG9iaiBUaGUgb2JqZWN0IHRvIHByaW50IG91dC5cbiAqIEBwYXJhbSB7T2JqZWN0fSBvcHRzIE9wdGlvbmFsIG9wdGlvbnMgb2JqZWN0IHRoYXQgYWx0ZXJzIHRoZSBvdXRwdXQuXG4gKi9cbi8qIGxlZ2FjeTogb2JqLCBzaG93SGlkZGVuLCBkZXB0aCwgY29sb3JzKi9cbmZ1bmN0aW9uIGluc3BlY3Qob2JqLCBvcHRzKSB7XG4gIC8vIGRlZmF1bHQgb3B0aW9uc1xuICB2YXIgY3R4ID0ge1xuICAgIHNlZW46IFtdLFxuICAgIHN0eWxpemU6IHN0eWxpemVOb0NvbG9yXG4gIH07XG4gIC8vIGxlZ2FjeS4uLlxuICBpZiAoYXJndW1lbnRzLmxlbmd0aCA+PSAzKSBjdHguZGVwdGggPSBhcmd1bWVudHNbMl07XG4gIGlmIChhcmd1bWVudHMubGVuZ3RoID49IDQpIGN0eC5jb2xvcnMgPSBhcmd1bWVudHNbM107XG4gIGlmIChpc0Jvb2xlYW4ob3B0cykpIHtcbiAgICAvLyBsZWdhY3kuLi5cbiAgICBjdHguc2hvd0hpZGRlbiA9IG9wdHM7XG4gIH0gZWxzZSBpZiAob3B0cykge1xuICAgIC8vIGdvdCBhbiBcIm9wdGlvbnNcIiBvYmplY3RcbiAgICBleHBvcnRzLl9leHRlbmQoY3R4LCBvcHRzKTtcbiAgfVxuICAvLyBzZXQgZGVmYXVsdCBvcHRpb25zXG4gIGlmIChpc1VuZGVmaW5lZChjdHguc2hvd0hpZGRlbikpIGN0eC5zaG93SGlkZGVuID0gZmFsc2U7XG4gIGlmIChpc1VuZGVmaW5lZChjdHguZGVwdGgpKSBjdHguZGVwdGggPSAyO1xuICBpZiAoaXNVbmRlZmluZWQoY3R4LmNvbG9ycykpIGN0eC5jb2xvcnMgPSBmYWxzZTtcbiAgaWYgKGlzVW5kZWZpbmVkKGN0eC5jdXN0b21JbnNwZWN0KSkgY3R4LmN1c3RvbUluc3BlY3QgPSB0cnVlO1xuICBpZiAoY3R4LmNvbG9ycykgY3R4LnN0eWxpemUgPSBzdHlsaXplV2l0aENvbG9yO1xuICByZXR1cm4gZm9ybWF0VmFsdWUoY3R4LCBvYmosIGN0eC5kZXB0aCk7XG59XG5leHBvcnRzLmluc3BlY3QgPSBpbnNwZWN0O1xuXG5cbi8vIGh0dHA6Ly9lbi53aWtpcGVkaWEub3JnL3dpa2kvQU5TSV9lc2NhcGVfY29kZSNncmFwaGljc1xuaW5zcGVjdC5jb2xvcnMgPSB7XG4gICdib2xkJyA6IFsxLCAyMl0sXG4gICdpdGFsaWMnIDogWzMsIDIzXSxcbiAgJ3VuZGVybGluZScgOiBbNCwgMjRdLFxuICAnaW52ZXJzZScgOiBbNywgMjddLFxuICAnd2hpdGUnIDogWzM3LCAzOV0sXG4gICdncmV5JyA6IFs5MCwgMzldLFxuICAnYmxhY2snIDogWzMwLCAzOV0sXG4gICdibHVlJyA6IFszNCwgMzldLFxuICAnY3lhbicgOiBbMzYsIDM5XSxcbiAgJ2dyZWVuJyA6IFszMiwgMzldLFxuICAnbWFnZW50YScgOiBbMzUsIDM5XSxcbiAgJ3JlZCcgOiBbMzEsIDM5XSxcbiAgJ3llbGxvdycgOiBbMzMsIDM5XVxufTtcblxuLy8gRG9uJ3QgdXNlICdibHVlJyBub3QgdmlzaWJsZSBvbiBjbWQuZXhlXG5pbnNwZWN0LnN0eWxlcyA9IHtcbiAgJ3NwZWNpYWwnOiAnY3lhbicsXG4gICdudW1iZXInOiAneWVsbG93JyxcbiAgJ2Jvb2xlYW4nOiAneWVsbG93JyxcbiAgJ3VuZGVmaW5lZCc6ICdncmV5JyxcbiAgJ251bGwnOiAnYm9sZCcsXG4gICdzdHJpbmcnOiAnZ3JlZW4nLFxuICAnZGF0ZSc6ICdtYWdlbnRhJyxcbiAgLy8gXCJuYW1lXCI6IGludGVudGlvbmFsbHkgbm90IHN0eWxpbmdcbiAgJ3JlZ2V4cCc6ICdyZWQnXG59O1xuXG5cbmZ1bmN0aW9uIHN0eWxpemVXaXRoQ29sb3Ioc3RyLCBzdHlsZVR5cGUpIHtcbiAgdmFyIHN0eWxlID0gaW5zcGVjdC5zdHlsZXNbc3R5bGVUeXBlXTtcblxuICBpZiAoc3R5bGUpIHtcbiAgICByZXR1cm4gJ1xcdTAwMWJbJyArIGluc3BlY3QuY29sb3JzW3N0eWxlXVswXSArICdtJyArIHN0ciArXG4gICAgICAgICAgICdcXHUwMDFiWycgKyBpbnNwZWN0LmNvbG9yc1tzdHlsZV1bMV0gKyAnbSc7XG4gIH0gZWxzZSB7XG4gICAgcmV0dXJuIHN0cjtcbiAgfVxufVxuXG5cbmZ1bmN0aW9uIHN0eWxpemVOb0NvbG9yKHN0ciwgc3R5bGVUeXBlKSB7XG4gIHJldHVybiBzdHI7XG59XG5cblxuZnVuY3Rpb24gYXJyYXlUb0hhc2goYXJyYXkpIHtcbiAgdmFyIGhhc2ggPSB7fTtcblxuICBhcnJheS5mb3JFYWNoKGZ1bmN0aW9uKHZhbCwgaWR4KSB7XG4gICAgaGFzaFt2YWxdID0gdHJ1ZTtcbiAgfSk7XG5cbiAgcmV0dXJuIGhhc2g7XG59XG5cblxuZnVuY3Rpb24gZm9ybWF0VmFsdWUoY3R4LCB2YWx1ZSwgcmVjdXJzZVRpbWVzKSB7XG4gIC8vIFByb3ZpZGUgYSBob29rIGZvciB1c2VyLXNwZWNpZmllZCBpbnNwZWN0IGZ1bmN0aW9ucy5cbiAgLy8gQ2hlY2sgdGhhdCB2YWx1ZSBpcyBhbiBvYmplY3Qgd2l0aCBhbiBpbnNwZWN0IGZ1bmN0aW9uIG9uIGl0XG4gIGlmIChjdHguY3VzdG9tSW5zcGVjdCAmJlxuICAgICAgdmFsdWUgJiZcbiAgICAgIGlzRnVuY3Rpb24odmFsdWUuaW5zcGVjdCkgJiZcbiAgICAgIC8vIEZpbHRlciBvdXQgdGhlIHV0aWwgbW9kdWxlLCBpdCdzIGluc3BlY3QgZnVuY3Rpb24gaXMgc3BlY2lhbFxuICAgICAgdmFsdWUuaW5zcGVjdCAhPT0gZXhwb3J0cy5pbnNwZWN0ICYmXG4gICAgICAvLyBBbHNvIGZpbHRlciBvdXQgYW55IHByb3RvdHlwZSBvYmplY3RzIHVzaW5nIHRoZSBjaXJjdWxhciBjaGVjay5cbiAgICAgICEodmFsdWUuY29uc3RydWN0b3IgJiYgdmFsdWUuY29uc3RydWN0b3IucHJvdG90eXBlID09PSB2YWx1ZSkpIHtcbiAgICB2YXIgcmV0ID0gdmFsdWUuaW5zcGVjdChyZWN1cnNlVGltZXMsIGN0eCk7XG4gICAgaWYgKCFpc1N0cmluZyhyZXQpKSB7XG4gICAgICByZXQgPSBmb3JtYXRWYWx1ZShjdHgsIHJldCwgcmVjdXJzZVRpbWVzKTtcbiAgICB9XG4gICAgcmV0dXJuIHJldDtcbiAgfVxuXG4gIC8vIFByaW1pdGl2ZSB0eXBlcyBjYW5ub3QgaGF2ZSBwcm9wZXJ0aWVzXG4gIHZhciBwcmltaXRpdmUgPSBmb3JtYXRQcmltaXRpdmUoY3R4LCB2YWx1ZSk7XG4gIGlmIChwcmltaXRpdmUpIHtcbiAgICByZXR1cm4gcHJpbWl0aXZlO1xuICB9XG5cbiAgLy8gTG9vayB1cCB0aGUga2V5cyBvZiB0aGUgb2JqZWN0LlxuICB2YXIga2V5cyA9IE9iamVjdC5rZXlzKHZhbHVlKTtcbiAgdmFyIHZpc2libGVLZXlzID0gYXJyYXlUb0hhc2goa2V5cyk7XG5cbiAgaWYgKGN0eC5zaG93SGlkZGVuKSB7XG4gICAga2V5cyA9IE9iamVjdC5nZXRPd25Qcm9wZXJ0eU5hbWVzKHZhbHVlKTtcbiAgfVxuXG4gIC8vIElFIGRvZXNuJ3QgbWFrZSBlcnJvciBmaWVsZHMgbm9uLWVudW1lcmFibGVcbiAgLy8gaHR0cDovL21zZG4ubWljcm9zb2Z0LmNvbS9lbi11cy9saWJyYXJ5L2llL2R3dzUyc2J0KHY9dnMuOTQpLmFzcHhcbiAgaWYgKGlzRXJyb3IodmFsdWUpXG4gICAgICAmJiAoa2V5cy5pbmRleE9mKCdtZXNzYWdlJykgPj0gMCB8fCBrZXlzLmluZGV4T2YoJ2Rlc2NyaXB0aW9uJykgPj0gMCkpIHtcbiAgICByZXR1cm4gZm9ybWF0RXJyb3IodmFsdWUpO1xuICB9XG5cbiAgLy8gU29tZSB0eXBlIG9mIG9iamVjdCB3aXRob3V0IHByb3BlcnRpZXMgY2FuIGJlIHNob3J0Y3V0dGVkLlxuICBpZiAoa2V5cy5sZW5ndGggPT09IDApIHtcbiAgICBpZiAoaXNGdW5jdGlvbih2YWx1ZSkpIHtcbiAgICAgIHZhciBuYW1lID0gdmFsdWUubmFtZSA/ICc6ICcgKyB2YWx1ZS5uYW1lIDogJyc7XG4gICAgICByZXR1cm4gY3R4LnN0eWxpemUoJ1tGdW5jdGlvbicgKyBuYW1lICsgJ10nLCAnc3BlY2lhbCcpO1xuICAgIH1cbiAgICBpZiAoaXNSZWdFeHAodmFsdWUpKSB7XG4gICAgICByZXR1cm4gY3R4LnN0eWxpemUoUmVnRXhwLnByb3RvdHlwZS50b1N0cmluZy5jYWxsKHZhbHVlKSwgJ3JlZ2V4cCcpO1xuICAgIH1cbiAgICBpZiAoaXNEYXRlKHZhbHVlKSkge1xuICAgICAgcmV0dXJuIGN0eC5zdHlsaXplKERhdGUucHJvdG90eXBlLnRvU3RyaW5nLmNhbGwodmFsdWUpLCAnZGF0ZScpO1xuICAgIH1cbiAgICBpZiAoaXNFcnJvcih2YWx1ZSkpIHtcbiAgICAgIHJldHVybiBmb3JtYXRFcnJvcih2YWx1ZSk7XG4gICAgfVxuICB9XG5cbiAgdmFyIGJhc2UgPSAnJywgYXJyYXkgPSBmYWxzZSwgYnJhY2VzID0gWyd7JywgJ30nXTtcblxuICAvLyBNYWtlIEFycmF5IHNheSB0aGF0IHRoZXkgYXJlIEFycmF5XG4gIGlmIChpc0FycmF5KHZhbHVlKSkge1xuICAgIGFycmF5ID0gdHJ1ZTtcbiAgICBicmFjZXMgPSBbJ1snLCAnXSddO1xuICB9XG5cbiAgLy8gTWFrZSBmdW5jdGlvbnMgc2F5IHRoYXQgdGhleSBhcmUgZnVuY3Rpb25zXG4gIGlmIChpc0Z1bmN0aW9uKHZhbHVlKSkge1xuICAgIHZhciBuID0gdmFsdWUubmFtZSA/ICc6ICcgKyB2YWx1ZS5uYW1lIDogJyc7XG4gICAgYmFzZSA9ICcgW0Z1bmN0aW9uJyArIG4gKyAnXSc7XG4gIH1cblxuICAvLyBNYWtlIFJlZ0V4cHMgc2F5IHRoYXQgdGhleSBhcmUgUmVnRXhwc1xuICBpZiAoaXNSZWdFeHAodmFsdWUpKSB7XG4gICAgYmFzZSA9ICcgJyArIFJlZ0V4cC5wcm90b3R5cGUudG9TdHJpbmcuY2FsbCh2YWx1ZSk7XG4gIH1cblxuICAvLyBNYWtlIGRhdGVzIHdpdGggcHJvcGVydGllcyBmaXJzdCBzYXkgdGhlIGRhdGVcbiAgaWYgKGlzRGF0ZSh2YWx1ZSkpIHtcbiAgICBiYXNlID0gJyAnICsgRGF0ZS5wcm90b3R5cGUudG9VVENTdHJpbmcuY2FsbCh2YWx1ZSk7XG4gIH1cblxuICAvLyBNYWtlIGVycm9yIHdpdGggbWVzc2FnZSBmaXJzdCBzYXkgdGhlIGVycm9yXG4gIGlmIChpc0Vycm9yKHZhbHVlKSkge1xuICAgIGJhc2UgPSAnICcgKyBmb3JtYXRFcnJvcih2YWx1ZSk7XG4gIH1cblxuICBpZiAoa2V5cy5sZW5ndGggPT09IDAgJiYgKCFhcnJheSB8fCB2YWx1ZS5sZW5ndGggPT0gMCkpIHtcbiAgICByZXR1cm4gYnJhY2VzWzBdICsgYmFzZSArIGJyYWNlc1sxXTtcbiAgfVxuXG4gIGlmIChyZWN1cnNlVGltZXMgPCAwKSB7XG4gICAgaWYgKGlzUmVnRXhwKHZhbHVlKSkge1xuICAgICAgcmV0dXJuIGN0eC5zdHlsaXplKFJlZ0V4cC5wcm90b3R5cGUudG9TdHJpbmcuY2FsbCh2YWx1ZSksICdyZWdleHAnKTtcbiAgICB9IGVsc2Uge1xuICAgICAgcmV0dXJuIGN0eC5zdHlsaXplKCdbT2JqZWN0XScsICdzcGVjaWFsJyk7XG4gICAgfVxuICB9XG5cbiAgY3R4LnNlZW4ucHVzaCh2YWx1ZSk7XG5cbiAgdmFyIG91dHB1dDtcbiAgaWYgKGFycmF5KSB7XG4gICAgb3V0cHV0ID0gZm9ybWF0QXJyYXkoY3R4LCB2YWx1ZSwgcmVjdXJzZVRpbWVzLCB2aXNpYmxlS2V5cywga2V5cyk7XG4gIH0gZWxzZSB7XG4gICAgb3V0cHV0ID0ga2V5cy5tYXAoZnVuY3Rpb24oa2V5KSB7XG4gICAgICByZXR1cm4gZm9ybWF0UHJvcGVydHkoY3R4LCB2YWx1ZSwgcmVjdXJzZVRpbWVzLCB2aXNpYmxlS2V5cywga2V5LCBhcnJheSk7XG4gICAgfSk7XG4gIH1cblxuICBjdHguc2Vlbi5wb3AoKTtcblxuICByZXR1cm4gcmVkdWNlVG9TaW5nbGVTdHJpbmcob3V0cHV0LCBiYXNlLCBicmFjZXMpO1xufVxuXG5cbmZ1bmN0aW9uIGZvcm1hdFByaW1pdGl2ZShjdHgsIHZhbHVlKSB7XG4gIGlmIChpc1VuZGVmaW5lZCh2YWx1ZSkpXG4gICAgcmV0dXJuIGN0eC5zdHlsaXplKCd1bmRlZmluZWQnLCAndW5kZWZpbmVkJyk7XG4gIGlmIChpc1N0cmluZyh2YWx1ZSkpIHtcbiAgICB2YXIgc2ltcGxlID0gJ1xcJycgKyBKU09OLnN0cmluZ2lmeSh2YWx1ZSkucmVwbGFjZSgvXlwifFwiJC9nLCAnJylcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIC5yZXBsYWNlKC8nL2csIFwiXFxcXCdcIilcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIC5yZXBsYWNlKC9cXFxcXCIvZywgJ1wiJykgKyAnXFwnJztcbiAgICByZXR1cm4gY3R4LnN0eWxpemUoc2ltcGxlLCAnc3RyaW5nJyk7XG4gIH1cbiAgaWYgKGlzTnVtYmVyKHZhbHVlKSlcbiAgICByZXR1cm4gY3R4LnN0eWxpemUoJycgKyB2YWx1ZSwgJ251bWJlcicpO1xuICBpZiAoaXNCb29sZWFuKHZhbHVlKSlcbiAgICByZXR1cm4gY3R4LnN0eWxpemUoJycgKyB2YWx1ZSwgJ2Jvb2xlYW4nKTtcbiAgLy8gRm9yIHNvbWUgcmVhc29uIHR5cGVvZiBudWxsIGlzIFwib2JqZWN0XCIsIHNvIHNwZWNpYWwgY2FzZSBoZXJlLlxuICBpZiAoaXNOdWxsKHZhbHVlKSlcbiAgICByZXR1cm4gY3R4LnN0eWxpemUoJ251bGwnLCAnbnVsbCcpO1xufVxuXG5cbmZ1bmN0aW9uIGZvcm1hdEVycm9yKHZhbHVlKSB7XG4gIHJldHVybiAnWycgKyBFcnJvci5wcm90b3R5cGUudG9TdHJpbmcuY2FsbCh2YWx1ZSkgKyAnXSc7XG59XG5cblxuZnVuY3Rpb24gZm9ybWF0QXJyYXkoY3R4LCB2YWx1ZSwgcmVjdXJzZVRpbWVzLCB2aXNpYmxlS2V5cywga2V5cykge1xuICB2YXIgb3V0cHV0ID0gW107XG4gIGZvciAodmFyIGkgPSAwLCBsID0gdmFsdWUubGVuZ3RoOyBpIDwgbDsgKytpKSB7XG4gICAgaWYgKGhhc093blByb3BlcnR5KHZhbHVlLCBTdHJpbmcoaSkpKSB7XG4gICAgICBvdXRwdXQucHVzaChmb3JtYXRQcm9wZXJ0eShjdHgsIHZhbHVlLCByZWN1cnNlVGltZXMsIHZpc2libGVLZXlzLFxuICAgICAgICAgIFN0cmluZyhpKSwgdHJ1ZSkpO1xuICAgIH0gZWxzZSB7XG4gICAgICBvdXRwdXQucHVzaCgnJyk7XG4gICAgfVxuICB9XG4gIGtleXMuZm9yRWFjaChmdW5jdGlvbihrZXkpIHtcbiAgICBpZiAoIWtleS5tYXRjaCgvXlxcZCskLykpIHtcbiAgICAgIG91dHB1dC5wdXNoKGZvcm1hdFByb3BlcnR5KGN0eCwgdmFsdWUsIHJlY3Vyc2VUaW1lcywgdmlzaWJsZUtleXMsXG4gICAgICAgICAga2V5LCB0cnVlKSk7XG4gICAgfVxuICB9KTtcbiAgcmV0dXJuIG91dHB1dDtcbn1cblxuXG5mdW5jdGlvbiBmb3JtYXRQcm9wZXJ0eShjdHgsIHZhbHVlLCByZWN1cnNlVGltZXMsIHZpc2libGVLZXlzLCBrZXksIGFycmF5KSB7XG4gIHZhciBuYW1lLCBzdHIsIGRlc2M7XG4gIGRlc2MgPSBPYmplY3QuZ2V0T3duUHJvcGVydHlEZXNjcmlwdG9yKHZhbHVlLCBrZXkpIHx8IHsgdmFsdWU6IHZhbHVlW2tleV0gfTtcbiAgaWYgKGRlc2MuZ2V0KSB7XG4gICAgaWYgKGRlc2Muc2V0KSB7XG4gICAgICBzdHIgPSBjdHguc3R5bGl6ZSgnW0dldHRlci9TZXR0ZXJdJywgJ3NwZWNpYWwnKTtcbiAgICB9IGVsc2Uge1xuICAgICAgc3RyID0gY3R4LnN0eWxpemUoJ1tHZXR0ZXJdJywgJ3NwZWNpYWwnKTtcbiAgICB9XG4gIH0gZWxzZSB7XG4gICAgaWYgKGRlc2Muc2V0KSB7XG4gICAgICBzdHIgPSBjdHguc3R5bGl6ZSgnW1NldHRlcl0nLCAnc3BlY2lhbCcpO1xuICAgIH1cbiAgfVxuICBpZiAoIWhhc093blByb3BlcnR5KHZpc2libGVLZXlzLCBrZXkpKSB7XG4gICAgbmFtZSA9ICdbJyArIGtleSArICddJztcbiAgfVxuICBpZiAoIXN0cikge1xuICAgIGlmIChjdHguc2Vlbi5pbmRleE9mKGRlc2MudmFsdWUpIDwgMCkge1xuICAgICAgaWYgKGlzTnVsbChyZWN1cnNlVGltZXMpKSB7XG4gICAgICAgIHN0ciA9IGZvcm1hdFZhbHVlKGN0eCwgZGVzYy52YWx1ZSwgbnVsbCk7XG4gICAgICB9IGVsc2Uge1xuICAgICAgICBzdHIgPSBmb3JtYXRWYWx1ZShjdHgsIGRlc2MudmFsdWUsIHJlY3Vyc2VUaW1lcyAtIDEpO1xuICAgICAgfVxuICAgICAgaWYgKHN0ci5pbmRleE9mKCdcXG4nKSA+IC0xKSB7XG4gICAgICAgIGlmIChhcnJheSkge1xuICAgICAgICAgIHN0ciA9IHN0ci5zcGxpdCgnXFxuJykubWFwKGZ1bmN0aW9uKGxpbmUpIHtcbiAgICAgICAgICAgIHJldHVybiAnICAnICsgbGluZTtcbiAgICAgICAgICB9KS5qb2luKCdcXG4nKS5zdWJzdHIoMik7XG4gICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgc3RyID0gJ1xcbicgKyBzdHIuc3BsaXQoJ1xcbicpLm1hcChmdW5jdGlvbihsaW5lKSB7XG4gICAgICAgICAgICByZXR1cm4gJyAgICcgKyBsaW5lO1xuICAgICAgICAgIH0pLmpvaW4oJ1xcbicpO1xuICAgICAgICB9XG4gICAgICB9XG4gICAgfSBlbHNlIHtcbiAgICAgIHN0ciA9IGN0eC5zdHlsaXplKCdbQ2lyY3VsYXJdJywgJ3NwZWNpYWwnKTtcbiAgICB9XG4gIH1cbiAgaWYgKGlzVW5kZWZpbmVkKG5hbWUpKSB7XG4gICAgaWYgKGFycmF5ICYmIGtleS5tYXRjaCgvXlxcZCskLykpIHtcbiAgICAgIHJldHVybiBzdHI7XG4gICAgfVxuICAgIG5hbWUgPSBKU09OLnN0cmluZ2lmeSgnJyArIGtleSk7XG4gICAgaWYgKG5hbWUubWF0Y2goL15cIihbYS16QS1aX11bYS16QS1aXzAtOV0qKVwiJC8pKSB7XG4gICAgICBuYW1lID0gbmFtZS5zdWJzdHIoMSwgbmFtZS5sZW5ndGggLSAyKTtcbiAgICAgIG5hbWUgPSBjdHguc3R5bGl6ZShuYW1lLCAnbmFtZScpO1xuICAgIH0gZWxzZSB7XG4gICAgICBuYW1lID0gbmFtZS5yZXBsYWNlKC8nL2csIFwiXFxcXCdcIilcbiAgICAgICAgICAgICAgICAgLnJlcGxhY2UoL1xcXFxcIi9nLCAnXCInKVxuICAgICAgICAgICAgICAgICAucmVwbGFjZSgvKF5cInxcIiQpL2csIFwiJ1wiKTtcbiAgICAgIG5hbWUgPSBjdHguc3R5bGl6ZShuYW1lLCAnc3RyaW5nJyk7XG4gICAgfVxuICB9XG5cbiAgcmV0dXJuIG5hbWUgKyAnOiAnICsgc3RyO1xufVxuXG5cbmZ1bmN0aW9uIHJlZHVjZVRvU2luZ2xlU3RyaW5nKG91dHB1dCwgYmFzZSwgYnJhY2VzKSB7XG4gIHZhciBudW1MaW5lc0VzdCA9IDA7XG4gIHZhciBsZW5ndGggPSBvdXRwdXQucmVkdWNlKGZ1bmN0aW9uKHByZXYsIGN1cikge1xuICAgIG51bUxpbmVzRXN0Kys7XG4gICAgaWYgKGN1ci5pbmRleE9mKCdcXG4nKSA+PSAwKSBudW1MaW5lc0VzdCsrO1xuICAgIHJldHVybiBwcmV2ICsgY3VyLnJlcGxhY2UoL1xcdTAwMWJcXFtcXGRcXGQ/bS9nLCAnJykubGVuZ3RoICsgMTtcbiAgfSwgMCk7XG5cbiAgaWYgKGxlbmd0aCA+IDYwKSB7XG4gICAgcmV0dXJuIGJyYWNlc1swXSArXG4gICAgICAgICAgIChiYXNlID09PSAnJyA/ICcnIDogYmFzZSArICdcXG4gJykgK1xuICAgICAgICAgICAnICcgK1xuICAgICAgICAgICBvdXRwdXQuam9pbignLFxcbiAgJykgK1xuICAgICAgICAgICAnICcgK1xuICAgICAgICAgICBicmFjZXNbMV07XG4gIH1cblxuICByZXR1cm4gYnJhY2VzWzBdICsgYmFzZSArICcgJyArIG91dHB1dC5qb2luKCcsICcpICsgJyAnICsgYnJhY2VzWzFdO1xufVxuXG5cbi8vIE5PVEU6IFRoZXNlIHR5cGUgY2hlY2tpbmcgZnVuY3Rpb25zIGludGVudGlvbmFsbHkgZG9uJ3QgdXNlIGBpbnN0YW5jZW9mYFxuLy8gYmVjYXVzZSBpdCBpcyBmcmFnaWxlIGFuZCBjYW4gYmUgZWFzaWx5IGZha2VkIHdpdGggYE9iamVjdC5jcmVhdGUoKWAuXG5mdW5jdGlvbiBpc0FycmF5KGFyKSB7XG4gIHJldHVybiBBcnJheS5pc0FycmF5KGFyKTtcbn1cbmV4cG9ydHMuaXNBcnJheSA9IGlzQXJyYXk7XG5cbmZ1bmN0aW9uIGlzQm9vbGVhbihhcmcpIHtcbiAgcmV0dXJuIHR5cGVvZiBhcmcgPT09ICdib29sZWFuJztcbn1cbmV4cG9ydHMuaXNCb29sZWFuID0gaXNCb29sZWFuO1xuXG5mdW5jdGlvbiBpc051bGwoYXJnKSB7XG4gIHJldHVybiBhcmcgPT09IG51bGw7XG59XG5leHBvcnRzLmlzTnVsbCA9IGlzTnVsbDtcblxuZnVuY3Rpb24gaXNOdWxsT3JVbmRlZmluZWQoYXJnKSB7XG4gIHJldHVybiBhcmcgPT0gbnVsbDtcbn1cbmV4cG9ydHMuaXNOdWxsT3JVbmRlZmluZWQgPSBpc051bGxPclVuZGVmaW5lZDtcblxuZnVuY3Rpb24gaXNOdW1iZXIoYXJnKSB7XG4gIHJldHVybiB0eXBlb2YgYXJnID09PSAnbnVtYmVyJztcbn1cbmV4cG9ydHMuaXNOdW1iZXIgPSBpc051bWJlcjtcblxuZnVuY3Rpb24gaXNTdHJpbmcoYXJnKSB7XG4gIHJldHVybiB0eXBlb2YgYXJnID09PSAnc3RyaW5nJztcbn1cbmV4cG9ydHMuaXNTdHJpbmcgPSBpc1N0cmluZztcblxuZnVuY3Rpb24gaXNTeW1ib2woYXJnKSB7XG4gIHJldHVybiB0eXBlb2YgYXJnID09PSAnc3ltYm9sJztcbn1cbmV4cG9ydHMuaXNTeW1ib2wgPSBpc1N5bWJvbDtcblxuZnVuY3Rpb24gaXNVbmRlZmluZWQoYXJnKSB7XG4gIHJldHVybiBhcmcgPT09IHZvaWQgMDtcbn1cbmV4cG9ydHMuaXNVbmRlZmluZWQgPSBpc1VuZGVmaW5lZDtcblxuZnVuY3Rpb24gaXNSZWdFeHAocmUpIHtcbiAgcmV0dXJuIGlzT2JqZWN0KHJlKSAmJiBvYmplY3RUb1N0cmluZyhyZSkgPT09ICdbb2JqZWN0IFJlZ0V4cF0nO1xufVxuZXhwb3J0cy5pc1JlZ0V4cCA9IGlzUmVnRXhwO1xuXG5mdW5jdGlvbiBpc09iamVjdChhcmcpIHtcbiAgcmV0dXJuIHR5cGVvZiBhcmcgPT09ICdvYmplY3QnICYmIGFyZyAhPT0gbnVsbDtcbn1cbmV4cG9ydHMuaXNPYmplY3QgPSBpc09iamVjdDtcblxuZnVuY3Rpb24gaXNEYXRlKGQpIHtcbiAgcmV0dXJuIGlzT2JqZWN0KGQpICYmIG9iamVjdFRvU3RyaW5nKGQpID09PSAnW29iamVjdCBEYXRlXSc7XG59XG5leHBvcnRzLmlzRGF0ZSA9IGlzRGF0ZTtcblxuZnVuY3Rpb24gaXNFcnJvcihlKSB7XG4gIHJldHVybiBpc09iamVjdChlKSAmJlxuICAgICAgKG9iamVjdFRvU3RyaW5nKGUpID09PSAnW29iamVjdCBFcnJvcl0nIHx8IGUgaW5zdGFuY2VvZiBFcnJvcik7XG59XG5leHBvcnRzLmlzRXJyb3IgPSBpc0Vycm9yO1xuXG5mdW5jdGlvbiBpc0Z1bmN0aW9uKGFyZykge1xuICByZXR1cm4gdHlwZW9mIGFyZyA9PT0gJ2Z1bmN0aW9uJztcbn1cbmV4cG9ydHMuaXNGdW5jdGlvbiA9IGlzRnVuY3Rpb247XG5cbmZ1bmN0aW9uIGlzUHJpbWl0aXZlKGFyZykge1xuICByZXR1cm4gYXJnID09PSBudWxsIHx8XG4gICAgICAgICB0eXBlb2YgYXJnID09PSAnYm9vbGVhbicgfHxcbiAgICAgICAgIHR5cGVvZiBhcmcgPT09ICdudW1iZXInIHx8XG4gICAgICAgICB0eXBlb2YgYXJnID09PSAnc3RyaW5nJyB8fFxuICAgICAgICAgdHlwZW9mIGFyZyA9PT0gJ3N5bWJvbCcgfHwgIC8vIEVTNiBzeW1ib2xcbiAgICAgICAgIHR5cGVvZiBhcmcgPT09ICd1bmRlZmluZWQnO1xufVxuZXhwb3J0cy5pc1ByaW1pdGl2ZSA9IGlzUHJpbWl0aXZlO1xuXG5leHBvcnRzLmlzQnVmZmVyID0gX2RlcmVxXygnLi9zdXBwb3J0L2lzQnVmZmVyJyk7XG5cbmZ1bmN0aW9uIG9iamVjdFRvU3RyaW5nKG8pIHtcbiAgcmV0dXJuIE9iamVjdC5wcm90b3R5cGUudG9TdHJpbmcuY2FsbChvKTtcbn1cblxuXG5mdW5jdGlvbiBwYWQobikge1xuICByZXR1cm4gbiA8IDEwID8gJzAnICsgbi50b1N0cmluZygxMCkgOiBuLnRvU3RyaW5nKDEwKTtcbn1cblxuXG52YXIgbW9udGhzID0gWydKYW4nLCAnRmViJywgJ01hcicsICdBcHInLCAnTWF5JywgJ0p1bicsICdKdWwnLCAnQXVnJywgJ1NlcCcsXG4gICAgICAgICAgICAgICdPY3QnLCAnTm92JywgJ0RlYyddO1xuXG4vLyAyNiBGZWIgMTY6MTk6MzRcbmZ1bmN0aW9uIHRpbWVzdGFtcCgpIHtcbiAgdmFyIGQgPSBuZXcgRGF0ZSgpO1xuICB2YXIgdGltZSA9IFtwYWQoZC5nZXRIb3VycygpKSxcbiAgICAgICAgICAgICAgcGFkKGQuZ2V0TWludXRlcygpKSxcbiAgICAgICAgICAgICAgcGFkKGQuZ2V0U2Vjb25kcygpKV0uam9pbignOicpO1xuICByZXR1cm4gW2QuZ2V0RGF0ZSgpLCBtb250aHNbZC5nZXRNb250aCgpXSwgdGltZV0uam9pbignICcpO1xufVxuXG5cbi8vIGxvZyBpcyBqdXN0IGEgdGhpbiB3cmFwcGVyIHRvIGNvbnNvbGUubG9nIHRoYXQgcHJlcGVuZHMgYSB0aW1lc3RhbXBcbmV4cG9ydHMubG9nID0gZnVuY3Rpb24oKSB7XG4gIGNvbnNvbGUubG9nKCclcyAtICVzJywgdGltZXN0YW1wKCksIGV4cG9ydHMuZm9ybWF0LmFwcGx5KGV4cG9ydHMsIGFyZ3VtZW50cykpO1xufTtcblxuXG4vKipcbiAqIEluaGVyaXQgdGhlIHByb3RvdHlwZSBtZXRob2RzIGZyb20gb25lIGNvbnN0cnVjdG9yIGludG8gYW5vdGhlci5cbiAqXG4gKiBUaGUgRnVuY3Rpb24ucHJvdG90eXBlLmluaGVyaXRzIGZyb20gbGFuZy5qcyByZXdyaXR0ZW4gYXMgYSBzdGFuZGFsb25lXG4gKiBmdW5jdGlvbiAobm90IG9uIEZ1bmN0aW9uLnByb3RvdHlwZSkuIE5PVEU6IElmIHRoaXMgZmlsZSBpcyB0byBiZSBsb2FkZWRcbiAqIGR1cmluZyBib290c3RyYXBwaW5nIHRoaXMgZnVuY3Rpb24gbmVlZHMgdG8gYmUgcmV3cml0dGVuIHVzaW5nIHNvbWUgbmF0aXZlXG4gKiBmdW5jdGlvbnMgYXMgcHJvdG90eXBlIHNldHVwIHVzaW5nIG5vcm1hbCBKYXZhU2NyaXB0IGRvZXMgbm90IHdvcmsgYXNcbiAqIGV4cGVjdGVkIGR1cmluZyBib290c3RyYXBwaW5nIChzZWUgbWlycm9yLmpzIGluIHIxMTQ5MDMpLlxuICpcbiAqIEBwYXJhbSB7ZnVuY3Rpb259IGN0b3IgQ29uc3RydWN0b3IgZnVuY3Rpb24gd2hpY2ggbmVlZHMgdG8gaW5oZXJpdCB0aGVcbiAqICAgICBwcm90b3R5cGUuXG4gKiBAcGFyYW0ge2Z1bmN0aW9ufSBzdXBlckN0b3IgQ29uc3RydWN0b3IgZnVuY3Rpb24gdG8gaW5oZXJpdCBwcm90b3R5cGUgZnJvbS5cbiAqL1xuZXhwb3J0cy5pbmhlcml0cyA9IF9kZXJlcV8oJ2luaGVyaXRzJyk7XG5cbmV4cG9ydHMuX2V4dGVuZCA9IGZ1bmN0aW9uKG9yaWdpbiwgYWRkKSB7XG4gIC8vIERvbid0IGRvIGFueXRoaW5nIGlmIGFkZCBpc24ndCBhbiBvYmplY3RcbiAgaWYgKCFhZGQgfHwgIWlzT2JqZWN0KGFkZCkpIHJldHVybiBvcmlnaW47XG5cbiAgdmFyIGtleXMgPSBPYmplY3Qua2V5cyhhZGQpO1xuICB2YXIgaSA9IGtleXMubGVuZ3RoO1xuICB3aGlsZSAoaS0tKSB7XG4gICAgb3JpZ2luW2tleXNbaV1dID0gYWRkW2tleXNbaV1dO1xuICB9XG4gIHJldHVybiBvcmlnaW47XG59O1xuXG5mdW5jdGlvbiBoYXNPd25Qcm9wZXJ0eShvYmosIHByb3ApIHtcbiAgcmV0dXJuIE9iamVjdC5wcm90b3R5cGUuaGFzT3duUHJvcGVydHkuY2FsbChvYmosIHByb3ApO1xufVxuXG59KS5jYWxsKHRoaXMsX2RlcmVxXygnX3Byb2Nlc3MnKSx0eXBlb2YgZ2xvYmFsICE9PSBcInVuZGVmaW5lZFwiID8gZ2xvYmFsIDogdHlwZW9mIHNlbGYgIT09IFwidW5kZWZpbmVkXCIgPyBzZWxmIDogdHlwZW9mIHdpbmRvdyAhPT0gXCJ1bmRlZmluZWRcIiA/IHdpbmRvdyA6IHt9KVxufSx7XCIuL3N1cHBvcnQvaXNCdWZmZXJcIjo0LFwiX3Byb2Nlc3NcIjozLFwiaW5oZXJpdHNcIjoyfV0sNjpbZnVuY3Rpb24oX2RlcmVxXyxtb2R1bGUsZXhwb3J0cyl7XG4vLyBBIHJlY3Vyc2l2ZSBkZXNjZW50IHBhcnNlciBvcGVyYXRlcyBieSBkZWZpbmluZyBmdW5jdGlvbnMgZm9yIGFsbFxuLy8gc3ludGFjdGljIGVsZW1lbnRzLCBhbmQgcmVjdXJzaXZlbHkgY2FsbGluZyB0aG9zZSwgZWFjaCBmdW5jdGlvblxuLy8gYWR2YW5jaW5nIHRoZSBpbnB1dCBzdHJlYW0gYW5kIHJldHVybmluZyBhbiBBU1Qgbm9kZS4gUHJlY2VkZW5jZVxuLy8gb2YgY29uc3RydWN0cyAoZm9yIGV4YW1wbGUsIHRoZSBmYWN0IHRoYXQgYCF4WzFdYCBtZWFucyBgISh4WzFdKWBcbi8vIGluc3RlYWQgb2YgYCgheClbMV1gIGlzIGhhbmRsZWQgYnkgdGhlIGZhY3QgdGhhdCB0aGUgcGFyc2VyXG4vLyBmdW5jdGlvbiB0aGF0IHBhcnNlcyB1bmFyeSBwcmVmaXggb3BlcmF0b3JzIGlzIGNhbGxlZCBmaXJzdCwgYW5kXG4vLyBpbiB0dXJuIGNhbGxzIHRoZSBmdW5jdGlvbiB0aGF0IHBhcnNlcyBgW11gIHN1YnNjcmlwdHMg4oCUIHRoYXRcbi8vIHdheSwgaXQnbGwgcmVjZWl2ZSB0aGUgbm9kZSBmb3IgYHhbMV1gIGFscmVhZHkgcGFyc2VkLCBhbmQgd3JhcHNcbi8vICp0aGF0KiBpbiB0aGUgdW5hcnkgb3BlcmF0b3Igbm9kZS5cbi8vXG4vLyBBY29ybiB1c2VzIGFuIFtvcGVyYXRvciBwcmVjZWRlbmNlIHBhcnNlcl1bb3BwXSB0byBoYW5kbGUgYmluYXJ5XG4vLyBvcGVyYXRvciBwcmVjZWRlbmNlLCBiZWNhdXNlIGl0IGlzIG11Y2ggbW9yZSBjb21wYWN0IHRoYW4gdXNpbmdcbi8vIHRoZSB0ZWNobmlxdWUgb3V0bGluZWQgYWJvdmUsIHdoaWNoIHVzZXMgZGlmZmVyZW50LCBuZXN0aW5nXG4vLyBmdW5jdGlvbnMgdG8gc3BlY2lmeSBwcmVjZWRlbmNlLCBmb3IgYWxsIG9mIHRoZSB0ZW4gYmluYXJ5XG4vLyBwcmVjZWRlbmNlIGxldmVscyB0aGF0IEphdmFTY3JpcHQgZGVmaW5lcy5cbi8vXG4vLyBbb3BwXTogaHR0cDovL2VuLndpa2lwZWRpYS5vcmcvd2lraS9PcGVyYXRvci1wcmVjZWRlbmNlX3BhcnNlclxuXG5cInVzZSBzdHJpY3RcIjtcblxudmFyIHR0ID0gX2RlcmVxXyhcIi4vdG9rZW50eXBlXCIpLnR5cGVzO1xuXG52YXIgUGFyc2VyID0gX2RlcmVxXyhcIi4vc3RhdGVcIikuUGFyc2VyO1xuXG52YXIgcmVzZXJ2ZWRXb3JkcyA9IF9kZXJlcV8oXCIuL2lkZW50aWZpZXJcIikucmVzZXJ2ZWRXb3JkcztcblxudmFyIGhhcyA9IF9kZXJlcV8oXCIuL3V0aWxcIikuaGFzO1xuXG52YXIgcHAgPSBQYXJzZXIucHJvdG90eXBlO1xuXG4vLyBDaGVjayBpZiBwcm9wZXJ0eSBuYW1lIGNsYXNoZXMgd2l0aCBhbHJlYWR5IGFkZGVkLlxuLy8gT2JqZWN0L2NsYXNzIGdldHRlcnMgYW5kIHNldHRlcnMgYXJlIG5vdCBhbGxvd2VkIHRvIGNsYXNoIOKAlFxuLy8gZWl0aGVyIHdpdGggZWFjaCBvdGhlciBvciB3aXRoIGFuIGluaXQgcHJvcGVydHkg4oCUIGFuZCBpblxuLy8gc3RyaWN0IG1vZGUsIGluaXQgcHJvcGVydGllcyBhcmUgYWxzbyBub3QgYWxsb3dlZCB0byBiZSByZXBlYXRlZC5cblxucHAuY2hlY2tQcm9wQ2xhc2ggPSBmdW5jdGlvbiAocHJvcCwgcHJvcEhhc2gpIHtcbiAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KSByZXR1cm47XG4gIHZhciBrZXkgPSBwcm9wLmtleSxcbiAgICAgIG5hbWUgPSB1bmRlZmluZWQ7XG4gIHN3aXRjaCAoa2V5LnR5cGUpIHtcbiAgICBjYXNlIFwiSWRlbnRpZmllclwiOlxuICAgICAgbmFtZSA9IGtleS5uYW1lO2JyZWFrO1xuICAgIGNhc2UgXCJMaXRlcmFsXCI6XG4gICAgICBuYW1lID0gU3RyaW5nKGtleS52YWx1ZSk7YnJlYWs7XG4gICAgZGVmYXVsdDpcbiAgICAgIHJldHVybjtcbiAgfVxuICB2YXIga2luZCA9IHByb3Aua2luZCB8fCBcImluaXRcIixcbiAgICAgIG90aGVyID0gdW5kZWZpbmVkO1xuICBpZiAoaGFzKHByb3BIYXNoLCBuYW1lKSkge1xuICAgIG90aGVyID0gcHJvcEhhc2hbbmFtZV07XG4gICAgdmFyIGlzR2V0U2V0ID0ga2luZCAhPT0gXCJpbml0XCI7XG4gICAgaWYgKCh0aGlzLnN0cmljdCB8fCBpc0dldFNldCkgJiYgb3RoZXJba2luZF0gfHwgIShpc0dldFNldCBeIG90aGVyLmluaXQpKSB0aGlzLnJhaXNlKGtleS5zdGFydCwgXCJSZWRlZmluaXRpb24gb2YgcHJvcGVydHlcIik7XG4gIH0gZWxzZSB7XG4gICAgb3RoZXIgPSBwcm9wSGFzaFtuYW1lXSA9IHtcbiAgICAgIGluaXQ6IGZhbHNlLFxuICAgICAgZ2V0OiBmYWxzZSxcbiAgICAgIHNldDogZmFsc2VcbiAgICB9O1xuICB9XG4gIG90aGVyW2tpbmRdID0gdHJ1ZTtcbn07XG5cbi8vICMjIyBFeHByZXNzaW9uIHBhcnNpbmdcblxuLy8gVGhlc2UgbmVzdCwgZnJvbSB0aGUgbW9zdCBnZW5lcmFsIGV4cHJlc3Npb24gdHlwZSBhdCB0aGUgdG9wIHRvXG4vLyAnYXRvbWljJywgbm9uZGl2aXNpYmxlIGV4cHJlc3Npb24gdHlwZXMgYXQgdGhlIGJvdHRvbS4gTW9zdCBvZlxuLy8gdGhlIGZ1bmN0aW9ucyB3aWxsIHNpbXBseSBsZXQgdGhlIGZ1bmN0aW9uKHMpIGJlbG93IHRoZW0gcGFyc2UsXG4vLyBhbmQsICppZiogdGhlIHN5bnRhY3RpYyBjb25zdHJ1Y3QgdGhleSBoYW5kbGUgaXMgcHJlc2VudCwgd3JhcFxuLy8gdGhlIEFTVCBub2RlIHRoYXQgdGhlIGlubmVyIHBhcnNlciBnYXZlIHRoZW0gaW4gYW5vdGhlciBub2RlLlxuXG4vLyBQYXJzZSBhIGZ1bGwgZXhwcmVzc2lvbi4gVGhlIG9wdGlvbmFsIGFyZ3VtZW50cyBhcmUgdXNlZCB0b1xuLy8gZm9yYmlkIHRoZSBgaW5gIG9wZXJhdG9yIChpbiBmb3IgbG9vcHMgaW5pdGFsaXphdGlvbiBleHByZXNzaW9ucylcbi8vIGFuZCBwcm92aWRlIHJlZmVyZW5jZSBmb3Igc3RvcmluZyAnPScgb3BlcmF0b3IgaW5zaWRlIHNob3J0aGFuZFxuLy8gcHJvcGVydHkgYXNzaWdubWVudCBpbiBjb250ZXh0cyB3aGVyZSBib3RoIG9iamVjdCBleHByZXNzaW9uXG4vLyBhbmQgb2JqZWN0IHBhdHRlcm4gbWlnaHQgYXBwZWFyIChzbyBpdCdzIHBvc3NpYmxlIHRvIHJhaXNlXG4vLyBkZWxheWVkIHN5bnRheCBlcnJvciBhdCBjb3JyZWN0IHBvc2l0aW9uKS5cblxucHAucGFyc2VFeHByZXNzaW9uID0gZnVuY3Rpb24gKG5vSW4sIHJlZlNob3J0aGFuZERlZmF1bHRQb3MpIHtcbiAgdmFyIHN0YXJ0UG9zID0gdGhpcy5zdGFydCxcbiAgICAgIHN0YXJ0TG9jID0gdGhpcy5zdGFydExvYztcbiAgdmFyIGV4cHIgPSB0aGlzLnBhcnNlTWF5YmVBc3NpZ24obm9JbiwgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcyk7XG4gIGlmICh0aGlzLnR5cGUgPT09IHR0LmNvbW1hKSB7XG4gICAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0UG9zLCBzdGFydExvYyk7XG4gICAgbm9kZS5leHByZXNzaW9ucyA9IFtleHByXTtcbiAgICB3aGlsZSAodGhpcy5lYXQodHQuY29tbWEpKSBub2RlLmV4cHJlc3Npb25zLnB1c2godGhpcy5wYXJzZU1heWJlQXNzaWduKG5vSW4sIHJlZlNob3J0aGFuZERlZmF1bHRQb3MpKTtcbiAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiU2VxdWVuY2VFeHByZXNzaW9uXCIpO1xuICB9XG4gIHJldHVybiBleHByO1xufTtcblxuLy8gUGFyc2UgYW4gYXNzaWdubWVudCBleHByZXNzaW9uLiBUaGlzIGluY2x1ZGVzIGFwcGxpY2F0aW9ucyBvZlxuLy8gb3BlcmF0b3JzIGxpa2UgYCs9YC5cblxucHAucGFyc2VNYXliZUFzc2lnbiA9IGZ1bmN0aW9uIChub0luLCByZWZTaG9ydGhhbmREZWZhdWx0UG9zLCBhZnRlckxlZnRQYXJzZSkge1xuICBpZiAodGhpcy50eXBlID09IHR0Ll95aWVsZCAmJiB0aGlzLmluR2VuZXJhdG9yKSByZXR1cm4gdGhpcy5wYXJzZVlpZWxkKCk7XG5cbiAgdmFyIGZhaWxPblNob3J0aGFuZEFzc2lnbiA9IHVuZGVmaW5lZDtcbiAgaWYgKCFyZWZTaG9ydGhhbmREZWZhdWx0UG9zKSB7XG4gICAgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcyA9IHsgc3RhcnQ6IDAgfTtcbiAgICBmYWlsT25TaG9ydGhhbmRBc3NpZ24gPSB0cnVlO1xuICB9IGVsc2Uge1xuICAgIGZhaWxPblNob3J0aGFuZEFzc2lnbiA9IGZhbHNlO1xuICB9XG4gIHZhciBzdGFydFBvcyA9IHRoaXMuc3RhcnQsXG4gICAgICBzdGFydExvYyA9IHRoaXMuc3RhcnRMb2M7XG4gIGlmICh0aGlzLnR5cGUgPT0gdHQucGFyZW5MIHx8IHRoaXMudHlwZSA9PSB0dC5uYW1lKSB0aGlzLnBvdGVudGlhbEFycm93QXQgPSB0aGlzLnN0YXJ0O1xuICB2YXIgbGVmdCA9IHRoaXMucGFyc2VNYXliZUNvbmRpdGlvbmFsKG5vSW4sIHJlZlNob3J0aGFuZERlZmF1bHRQb3MpO1xuICBpZiAoYWZ0ZXJMZWZ0UGFyc2UpIGxlZnQgPSBhZnRlckxlZnRQYXJzZS5jYWxsKHRoaXMsIGxlZnQsIHN0YXJ0UG9zLCBzdGFydExvYyk7XG4gIGlmICh0aGlzLnR5cGUuaXNBc3NpZ24pIHtcbiAgICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlQXQoc3RhcnRQb3MsIHN0YXJ0TG9jKTtcbiAgICBub2RlLm9wZXJhdG9yID0gdGhpcy52YWx1ZTtcbiAgICBub2RlLmxlZnQgPSB0aGlzLnR5cGUgPT09IHR0LmVxID8gdGhpcy50b0Fzc2lnbmFibGUobGVmdCkgOiBsZWZ0O1xuICAgIHJlZlNob3J0aGFuZERlZmF1bHRQb3Muc3RhcnQgPSAwOyAvLyByZXNldCBiZWNhdXNlIHNob3J0aGFuZCBkZWZhdWx0IHdhcyB1c2VkIGNvcnJlY3RseVxuICAgIHRoaXMuY2hlY2tMVmFsKGxlZnQpO1xuICAgIHRoaXMubmV4dCgpO1xuICAgIG5vZGUucmlnaHQgPSB0aGlzLnBhcnNlTWF5YmVBc3NpZ24obm9Jbik7XG4gICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkFzc2lnbm1lbnRFeHByZXNzaW9uXCIpO1xuICB9IGVsc2UgaWYgKGZhaWxPblNob3J0aGFuZEFzc2lnbiAmJiByZWZTaG9ydGhhbmREZWZhdWx0UG9zLnN0YXJ0KSB7XG4gICAgdGhpcy51bmV4cGVjdGVkKHJlZlNob3J0aGFuZERlZmF1bHRQb3Muc3RhcnQpO1xuICB9XG4gIHJldHVybiBsZWZ0O1xufTtcblxuLy8gUGFyc2UgYSB0ZXJuYXJ5IGNvbmRpdGlvbmFsIChgPzpgKSBvcGVyYXRvci5cblxucHAucGFyc2VNYXliZUNvbmRpdGlvbmFsID0gZnVuY3Rpb24gKG5vSW4sIHJlZlNob3J0aGFuZERlZmF1bHRQb3MpIHtcbiAgdmFyIHN0YXJ0UG9zID0gdGhpcy5zdGFydCxcbiAgICAgIHN0YXJ0TG9jID0gdGhpcy5zdGFydExvYztcbiAgdmFyIGV4cHIgPSB0aGlzLnBhcnNlRXhwck9wcyhub0luLCByZWZTaG9ydGhhbmREZWZhdWx0UG9zKTtcbiAgaWYgKHJlZlNob3J0aGFuZERlZmF1bHRQb3MgJiYgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcy5zdGFydCkgcmV0dXJuIGV4cHI7XG4gIGlmICh0aGlzLmVhdCh0dC5xdWVzdGlvbikpIHtcbiAgICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlQXQoc3RhcnRQb3MsIHN0YXJ0TG9jKTtcbiAgICBub2RlLnRlc3QgPSBleHByO1xuICAgIG5vZGUuY29uc2VxdWVudCA9IHRoaXMucGFyc2VNYXliZUFzc2lnbigpO1xuICAgIHRoaXMuZXhwZWN0KHR0LmNvbG9uKTtcbiAgICBub2RlLmFsdGVybmF0ZSA9IHRoaXMucGFyc2VNYXliZUFzc2lnbihub0luKTtcbiAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiQ29uZGl0aW9uYWxFeHByZXNzaW9uXCIpO1xuICB9XG4gIHJldHVybiBleHByO1xufTtcblxuLy8gU3RhcnQgdGhlIHByZWNlZGVuY2UgcGFyc2VyLlxuXG5wcC5wYXJzZUV4cHJPcHMgPSBmdW5jdGlvbiAobm9JbiwgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcykge1xuICB2YXIgc3RhcnRQb3MgPSB0aGlzLnN0YXJ0LFxuICAgICAgc3RhcnRMb2MgPSB0aGlzLnN0YXJ0TG9jO1xuICB2YXIgZXhwciA9IHRoaXMucGFyc2VNYXliZVVuYXJ5KHJlZlNob3J0aGFuZERlZmF1bHRQb3MpO1xuICBpZiAocmVmU2hvcnRoYW5kRGVmYXVsdFBvcyAmJiByZWZTaG9ydGhhbmREZWZhdWx0UG9zLnN0YXJ0KSByZXR1cm4gZXhwcjtcbiAgcmV0dXJuIHRoaXMucGFyc2VFeHByT3AoZXhwciwgc3RhcnRQb3MsIHN0YXJ0TG9jLCAtMSwgbm9Jbik7XG59O1xuXG4vLyBQYXJzZSBiaW5hcnkgb3BlcmF0b3JzIHdpdGggdGhlIG9wZXJhdG9yIHByZWNlZGVuY2UgcGFyc2luZ1xuLy8gYWxnb3JpdGhtLiBgbGVmdGAgaXMgdGhlIGxlZnQtaGFuZCBzaWRlIG9mIHRoZSBvcGVyYXRvci5cbi8vIGBtaW5QcmVjYCBwcm92aWRlcyBjb250ZXh0IHRoYXQgYWxsb3dzIHRoZSBmdW5jdGlvbiB0byBzdG9wIGFuZFxuLy8gZGVmZXIgZnVydGhlciBwYXJzZXIgdG8gb25lIG9mIGl0cyBjYWxsZXJzIHdoZW4gaXQgZW5jb3VudGVycyBhblxuLy8gb3BlcmF0b3IgdGhhdCBoYXMgYSBsb3dlciBwcmVjZWRlbmNlIHRoYW4gdGhlIHNldCBpdCBpcyBwYXJzaW5nLlxuXG5wcC5wYXJzZUV4cHJPcCA9IGZ1bmN0aW9uIChsZWZ0LCBsZWZ0U3RhcnRQb3MsIGxlZnRTdGFydExvYywgbWluUHJlYywgbm9Jbikge1xuICB2YXIgcHJlYyA9IHRoaXMudHlwZS5iaW5vcDtcbiAgaWYgKEFycmF5LmlzQXJyYXkobGVmdFN0YXJ0UG9zKSkge1xuICAgIGlmICh0aGlzLm9wdGlvbnMubG9jYXRpb25zICYmIG5vSW4gPT09IHVuZGVmaW5lZCkge1xuICAgICAgLy8gc2hpZnQgYXJndW1lbnRzIHRvIGxlZnQgYnkgb25lXG4gICAgICBub0luID0gbWluUHJlYztcbiAgICAgIG1pblByZWMgPSBsZWZ0U3RhcnRMb2M7XG4gICAgICAvLyBmbGF0dGVuIGxlZnRTdGFydFBvc1xuICAgICAgbGVmdFN0YXJ0TG9jID0gbGVmdFN0YXJ0UG9zWzFdO1xuICAgICAgbGVmdFN0YXJ0UG9zID0gbGVmdFN0YXJ0UG9zWzBdO1xuICAgIH1cbiAgfVxuICBpZiAocHJlYyAhPSBudWxsICYmICghbm9JbiB8fCB0aGlzLnR5cGUgIT09IHR0Ll9pbikpIHtcbiAgICBpZiAocHJlYyA+IG1pblByZWMpIHtcbiAgICAgIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGVBdChsZWZ0U3RhcnRQb3MsIGxlZnRTdGFydExvYyk7XG4gICAgICBub2RlLmxlZnQgPSBsZWZ0O1xuICAgICAgbm9kZS5vcGVyYXRvciA9IHRoaXMudmFsdWU7XG4gICAgICB2YXIgb3AgPSB0aGlzLnR5cGU7XG4gICAgICB0aGlzLm5leHQoKTtcbiAgICAgIHZhciBzdGFydFBvcyA9IHRoaXMuc3RhcnQsXG4gICAgICAgICAgc3RhcnRMb2MgPSB0aGlzLnN0YXJ0TG9jO1xuICAgICAgbm9kZS5yaWdodCA9IHRoaXMucGFyc2VFeHByT3AodGhpcy5wYXJzZU1heWJlVW5hcnkoKSwgc3RhcnRQb3MsIHN0YXJ0TG9jLCBwcmVjLCBub0luKTtcbiAgICAgIHRoaXMuZmluaXNoTm9kZShub2RlLCBvcCA9PT0gdHQubG9naWNhbE9SIHx8IG9wID09PSB0dC5sb2dpY2FsQU5EID8gXCJMb2dpY2FsRXhwcmVzc2lvblwiIDogXCJCaW5hcnlFeHByZXNzaW9uXCIpO1xuICAgICAgcmV0dXJuIHRoaXMucGFyc2VFeHByT3Aobm9kZSwgbGVmdFN0YXJ0UG9zLCBsZWZ0U3RhcnRMb2MsIG1pblByZWMsIG5vSW4pO1xuICAgIH1cbiAgfVxuICByZXR1cm4gbGVmdDtcbn07XG5cbi8vIFBhcnNlIHVuYXJ5IG9wZXJhdG9ycywgYm90aCBwcmVmaXggYW5kIHBvc3RmaXguXG5cbnBwLnBhcnNlTWF5YmVVbmFyeSA9IGZ1bmN0aW9uIChyZWZTaG9ydGhhbmREZWZhdWx0UG9zKSB7XG4gIGlmICh0aGlzLnR5cGUucHJlZml4KSB7XG4gICAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpLFxuICAgICAgICB1cGRhdGUgPSB0aGlzLnR5cGUgPT09IHR0LmluY0RlYztcbiAgICBub2RlLm9wZXJhdG9yID0gdGhpcy52YWx1ZTtcbiAgICBub2RlLnByZWZpeCA9IHRydWU7XG4gICAgdGhpcy5uZXh0KCk7XG4gICAgbm9kZS5hcmd1bWVudCA9IHRoaXMucGFyc2VNYXliZVVuYXJ5KCk7XG4gICAgaWYgKHJlZlNob3J0aGFuZERlZmF1bHRQb3MgJiYgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcy5zdGFydCkgdGhpcy51bmV4cGVjdGVkKHJlZlNob3J0aGFuZERlZmF1bHRQb3Muc3RhcnQpO1xuICAgIGlmICh1cGRhdGUpIHRoaXMuY2hlY2tMVmFsKG5vZGUuYXJndW1lbnQpO2Vsc2UgaWYgKHRoaXMuc3RyaWN0ICYmIG5vZGUub3BlcmF0b3IgPT09IFwiZGVsZXRlXCIgJiYgbm9kZS5hcmd1bWVudC50eXBlID09PSBcIklkZW50aWZpZXJcIikgdGhpcy5yYWlzZShub2RlLnN0YXJ0LCBcIkRlbGV0aW5nIGxvY2FsIHZhcmlhYmxlIGluIHN0cmljdCBtb2RlXCIpO1xuICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgdXBkYXRlID8gXCJVcGRhdGVFeHByZXNzaW9uXCIgOiBcIlVuYXJ5RXhwcmVzc2lvblwiKTtcbiAgfVxuICB2YXIgc3RhcnRQb3MgPSB0aGlzLnN0YXJ0LFxuICAgICAgc3RhcnRMb2MgPSB0aGlzLnN0YXJ0TG9jO1xuICB2YXIgZXhwciA9IHRoaXMucGFyc2VFeHByU3Vic2NyaXB0cyhyZWZTaG9ydGhhbmREZWZhdWx0UG9zKTtcbiAgaWYgKHJlZlNob3J0aGFuZERlZmF1bHRQb3MgJiYgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcy5zdGFydCkgcmV0dXJuIGV4cHI7XG4gIHdoaWxlICh0aGlzLnR5cGUucG9zdGZpeCAmJiAhdGhpcy5jYW5JbnNlcnRTZW1pY29sb24oKSkge1xuICAgIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGVBdChzdGFydFBvcywgc3RhcnRMb2MpO1xuICAgIG5vZGUub3BlcmF0b3IgPSB0aGlzLnZhbHVlO1xuICAgIG5vZGUucHJlZml4ID0gZmFsc2U7XG4gICAgbm9kZS5hcmd1bWVudCA9IGV4cHI7XG4gICAgdGhpcy5jaGVja0xWYWwoZXhwcik7XG4gICAgdGhpcy5uZXh0KCk7XG4gICAgZXhwciA9IHRoaXMuZmluaXNoTm9kZShub2RlLCBcIlVwZGF0ZUV4cHJlc3Npb25cIik7XG4gIH1cbiAgcmV0dXJuIGV4cHI7XG59O1xuXG4vLyBQYXJzZSBjYWxsLCBkb3QsIGFuZCBgW11gLXN1YnNjcmlwdCBleHByZXNzaW9ucy5cblxucHAucGFyc2VFeHByU3Vic2NyaXB0cyA9IGZ1bmN0aW9uIChyZWZTaG9ydGhhbmREZWZhdWx0UG9zKSB7XG4gIHZhciBzdGFydFBvcyA9IHRoaXMuc3RhcnQsXG4gICAgICBzdGFydExvYyA9IHRoaXMuc3RhcnRMb2M7XG4gIHZhciBleHByID0gdGhpcy5wYXJzZUV4cHJBdG9tKHJlZlNob3J0aGFuZERlZmF1bHRQb3MpO1xuICBpZiAocmVmU2hvcnRoYW5kRGVmYXVsdFBvcyAmJiByZWZTaG9ydGhhbmREZWZhdWx0UG9zLnN0YXJ0KSByZXR1cm4gZXhwcjtcbiAgcmV0dXJuIHRoaXMucGFyc2VTdWJzY3JpcHRzKGV4cHIsIHN0YXJ0UG9zLCBzdGFydExvYyk7XG59O1xuXG5wcC5wYXJzZVN1YnNjcmlwdHMgPSBmdW5jdGlvbiAoYmFzZSwgc3RhcnRQb3MsIHN0YXJ0TG9jLCBub0NhbGxzKSB7XG4gIGlmIChBcnJheS5pc0FycmF5KHN0YXJ0UG9zKSkge1xuICAgIGlmICh0aGlzLm9wdGlvbnMubG9jYXRpb25zICYmIG5vQ2FsbHMgPT09IHVuZGVmaW5lZCkge1xuICAgICAgLy8gc2hpZnQgYXJndW1lbnRzIHRvIGxlZnQgYnkgb25lXG4gICAgICBub0NhbGxzID0gc3RhcnRMb2M7XG4gICAgICAvLyBmbGF0dGVuIHN0YXJ0UG9zXG4gICAgICBzdGFydExvYyA9IHN0YXJ0UG9zWzFdO1xuICAgICAgc3RhcnRQb3MgPSBzdGFydFBvc1swXTtcbiAgICB9XG4gIH1cbiAgZm9yICg7Oykge1xuICAgIGlmICh0aGlzLmVhdCh0dC5kb3QpKSB7XG4gICAgICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlQXQoc3RhcnRQb3MsIHN0YXJ0TG9jKTtcbiAgICAgIG5vZGUub2JqZWN0ID0gYmFzZTtcbiAgICAgIG5vZGUucHJvcGVydHkgPSB0aGlzLnBhcnNlSWRlbnQodHJ1ZSk7XG4gICAgICBub2RlLmNvbXB1dGVkID0gZmFsc2U7XG4gICAgICBiYXNlID0gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiTWVtYmVyRXhwcmVzc2lvblwiKTtcbiAgICB9IGVsc2UgaWYgKHRoaXMuZWF0KHR0LmJyYWNrZXRMKSkge1xuICAgICAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0UG9zLCBzdGFydExvYyk7XG4gICAgICBub2RlLm9iamVjdCA9IGJhc2U7XG4gICAgICBub2RlLnByb3BlcnR5ID0gdGhpcy5wYXJzZUV4cHJlc3Npb24oKTtcbiAgICAgIG5vZGUuY29tcHV0ZWQgPSB0cnVlO1xuICAgICAgdGhpcy5leHBlY3QodHQuYnJhY2tldFIpO1xuICAgICAgYmFzZSA9IHRoaXMuZmluaXNoTm9kZShub2RlLCBcIk1lbWJlckV4cHJlc3Npb25cIik7XG4gICAgfSBlbHNlIGlmICghbm9DYWxscyAmJiB0aGlzLmVhdCh0dC5wYXJlbkwpKSB7XG4gICAgICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlQXQoc3RhcnRQb3MsIHN0YXJ0TG9jKTtcbiAgICAgIG5vZGUuY2FsbGVlID0gYmFzZTtcbiAgICAgIG5vZGUuYXJndW1lbnRzID0gdGhpcy5wYXJzZUV4cHJMaXN0KHR0LnBhcmVuUiwgZmFsc2UpO1xuICAgICAgYmFzZSA9IHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkNhbGxFeHByZXNzaW9uXCIpO1xuICAgIH0gZWxzZSBpZiAodGhpcy50eXBlID09PSB0dC5iYWNrUXVvdGUpIHtcbiAgICAgIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGVBdChzdGFydFBvcywgc3RhcnRMb2MpO1xuICAgICAgbm9kZS50YWcgPSBiYXNlO1xuICAgICAgbm9kZS5xdWFzaSA9IHRoaXMucGFyc2VUZW1wbGF0ZSgpO1xuICAgICAgYmFzZSA9IHRoaXMuZmluaXNoTm9kZShub2RlLCBcIlRhZ2dlZFRlbXBsYXRlRXhwcmVzc2lvblwiKTtcbiAgICB9IGVsc2Uge1xuICAgICAgcmV0dXJuIGJhc2U7XG4gICAgfVxuICB9XG59O1xuXG4vLyBQYXJzZSBhbiBhdG9taWMgZXhwcmVzc2lvbiDigJQgZWl0aGVyIGEgc2luZ2xlIHRva2VuIHRoYXQgaXMgYW5cbi8vIGV4cHJlc3Npb24sIGFuIGV4cHJlc3Npb24gc3RhcnRlZCBieSBhIGtleXdvcmQgbGlrZSBgZnVuY3Rpb25gIG9yXG4vLyBgbmV3YCwgb3IgYW4gZXhwcmVzc2lvbiB3cmFwcGVkIGluIHB1bmN0dWF0aW9uIGxpa2UgYCgpYCwgYFtdYCxcbi8vIG9yIGB7fWAuXG5cbnBwLnBhcnNlRXhwckF0b20gPSBmdW5jdGlvbiAocmVmU2hvcnRoYW5kRGVmYXVsdFBvcykge1xuICB2YXIgbm9kZSA9IHVuZGVmaW5lZCxcbiAgICAgIGNhbkJlQXJyb3cgPSB0aGlzLnBvdGVudGlhbEFycm93QXQgPT0gdGhpcy5zdGFydDtcbiAgc3dpdGNoICh0aGlzLnR5cGUpIHtcbiAgICBjYXNlIHR0Ll90aGlzOlxuICAgIGNhc2UgdHQuX3N1cGVyOlxuICAgICAgdmFyIHR5cGUgPSB0aGlzLnR5cGUgPT09IHR0Ll90aGlzID8gXCJUaGlzRXhwcmVzc2lvblwiIDogXCJTdXBlclwiO1xuICAgICAgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gICAgICB0aGlzLm5leHQoKTtcbiAgICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgdHlwZSk7XG5cbiAgICBjYXNlIHR0Ll95aWVsZDpcbiAgICAgIGlmICh0aGlzLmluR2VuZXJhdG9yKSB0aGlzLnVuZXhwZWN0ZWQoKTtcblxuICAgIGNhc2UgdHQubmFtZTpcbiAgICAgIHZhciBzdGFydFBvcyA9IHRoaXMuc3RhcnQsXG4gICAgICAgICAgc3RhcnRMb2MgPSB0aGlzLnN0YXJ0TG9jO1xuICAgICAgdmFyIGlkID0gdGhpcy5wYXJzZUlkZW50KHRoaXMudHlwZSAhPT0gdHQubmFtZSk7XG4gICAgICBpZiAoY2FuQmVBcnJvdyAmJiAhdGhpcy5jYW5JbnNlcnRTZW1pY29sb24oKSAmJiB0aGlzLmVhdCh0dC5hcnJvdykpIHJldHVybiB0aGlzLnBhcnNlQXJyb3dFeHByZXNzaW9uKHRoaXMuc3RhcnROb2RlQXQoc3RhcnRQb3MsIHN0YXJ0TG9jKSwgW2lkXSk7XG4gICAgICByZXR1cm4gaWQ7XG5cbiAgICBjYXNlIHR0LnJlZ2V4cDpcbiAgICAgIHZhciB2YWx1ZSA9IHRoaXMudmFsdWU7XG4gICAgICBub2RlID0gdGhpcy5wYXJzZUxpdGVyYWwodmFsdWUudmFsdWUpO1xuICAgICAgbm9kZS5yZWdleCA9IHsgcGF0dGVybjogdmFsdWUucGF0dGVybiwgZmxhZ3M6IHZhbHVlLmZsYWdzIH07XG4gICAgICByZXR1cm4gbm9kZTtcblxuICAgIGNhc2UgdHQubnVtOmNhc2UgdHQuc3RyaW5nOlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VMaXRlcmFsKHRoaXMudmFsdWUpO1xuXG4gICAgY2FzZSB0dC5fbnVsbDpjYXNlIHR0Ll90cnVlOmNhc2UgdHQuX2ZhbHNlOlxuICAgICAgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gICAgICBub2RlLnZhbHVlID0gdGhpcy50eXBlID09PSB0dC5fbnVsbCA/IG51bGwgOiB0aGlzLnR5cGUgPT09IHR0Ll90cnVlO1xuICAgICAgbm9kZS5yYXcgPSB0aGlzLnR5cGUua2V5d29yZDtcbiAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkxpdGVyYWxcIik7XG5cbiAgICBjYXNlIHR0LnBhcmVuTDpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlUGFyZW5BbmREaXN0aW5ndWlzaEV4cHJlc3Npb24oY2FuQmVBcnJvdyk7XG5cbiAgICBjYXNlIHR0LmJyYWNrZXRMOlxuICAgICAgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gICAgICB0aGlzLm5leHQoKTtcbiAgICAgIC8vIGNoZWNrIHdoZXRoZXIgdGhpcyBpcyBhcnJheSBjb21wcmVoZW5zaW9uIG9yIHJlZ3VsYXIgYXJyYXlcbiAgICAgIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNyAmJiB0aGlzLnR5cGUgPT09IHR0Ll9mb3IpIHtcbiAgICAgICAgcmV0dXJuIHRoaXMucGFyc2VDb21wcmVoZW5zaW9uKG5vZGUsIGZhbHNlKTtcbiAgICAgIH1cbiAgICAgIG5vZGUuZWxlbWVudHMgPSB0aGlzLnBhcnNlRXhwckxpc3QodHQuYnJhY2tldFIsIHRydWUsIHRydWUsIHJlZlNob3J0aGFuZERlZmF1bHRQb3MpO1xuICAgICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkFycmF5RXhwcmVzc2lvblwiKTtcblxuICAgIGNhc2UgdHQuYnJhY2VMOlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VPYmooZmFsc2UsIHJlZlNob3J0aGFuZERlZmF1bHRQb3MpO1xuXG4gICAgY2FzZSB0dC5fZnVuY3Rpb246XG4gICAgICBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgcmV0dXJuIHRoaXMucGFyc2VGdW5jdGlvbihub2RlLCBmYWxzZSk7XG5cbiAgICBjYXNlIHR0Ll9jbGFzczpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlQ2xhc3ModGhpcy5zdGFydE5vZGUoKSwgZmFsc2UpO1xuXG4gICAgY2FzZSB0dC5fbmV3OlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VOZXcoKTtcblxuICAgIGNhc2UgdHQuYmFja1F1b3RlOlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VUZW1wbGF0ZSgpO1xuXG4gICAgZGVmYXVsdDpcbiAgICAgIHRoaXMudW5leHBlY3RlZCgpO1xuICB9XG59O1xuXG5wcC5wYXJzZUxpdGVyYWwgPSBmdW5jdGlvbiAodmFsdWUpIHtcbiAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICBub2RlLnZhbHVlID0gdmFsdWU7XG4gIG5vZGUucmF3ID0gdGhpcy5pbnB1dC5zbGljZSh0aGlzLnN0YXJ0LCB0aGlzLmVuZCk7XG4gIHRoaXMubmV4dCgpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiTGl0ZXJhbFwiKTtcbn07XG5cbnBwLnBhcnNlUGFyZW5FeHByZXNzaW9uID0gZnVuY3Rpb24gKCkge1xuICB0aGlzLmV4cGVjdCh0dC5wYXJlbkwpO1xuICB2YXIgdmFsID0gdGhpcy5wYXJzZUV4cHJlc3Npb24oKTtcbiAgdGhpcy5leHBlY3QodHQucGFyZW5SKTtcbiAgcmV0dXJuIHZhbDtcbn07XG5cbnBwLnBhcnNlUGFyZW5BbmREaXN0aW5ndWlzaEV4cHJlc3Npb24gPSBmdW5jdGlvbiAoY2FuQmVBcnJvdykge1xuICB2YXIgc3RhcnRQb3MgPSB0aGlzLnN0YXJ0LFxuICAgICAgc3RhcnRMb2MgPSB0aGlzLnN0YXJ0TG9jLFxuICAgICAgdmFsID0gdW5kZWZpbmVkO1xuICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYpIHtcbiAgICB0aGlzLm5leHQoKTtcblxuICAgIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNyAmJiB0aGlzLnR5cGUgPT09IHR0Ll9mb3IpIHtcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlQ29tcHJlaGVuc2lvbih0aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0UG9zLCBzdGFydExvYyksIHRydWUpO1xuICAgIH1cblxuICAgIHZhciBpbm5lclN0YXJ0UG9zID0gdGhpcy5zdGFydCxcbiAgICAgICAgaW5uZXJTdGFydExvYyA9IHRoaXMuc3RhcnRMb2M7XG4gICAgdmFyIGV4cHJMaXN0ID0gW10sXG4gICAgICAgIGZpcnN0ID0gdHJ1ZTtcbiAgICB2YXIgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcyA9IHsgc3RhcnQ6IDAgfSxcbiAgICAgICAgc3ByZWFkU3RhcnQgPSB1bmRlZmluZWQsXG4gICAgICAgIGlubmVyUGFyZW5TdGFydCA9IHVuZGVmaW5lZDtcbiAgICB3aGlsZSAodGhpcy50eXBlICE9PSB0dC5wYXJlblIpIHtcbiAgICAgIGZpcnN0ID8gZmlyc3QgPSBmYWxzZSA6IHRoaXMuZXhwZWN0KHR0LmNvbW1hKTtcbiAgICAgIGlmICh0aGlzLnR5cGUgPT09IHR0LmVsbGlwc2lzKSB7XG4gICAgICAgIHNwcmVhZFN0YXJ0ID0gdGhpcy5zdGFydDtcbiAgICAgICAgZXhwckxpc3QucHVzaCh0aGlzLnBhcnNlUGFyZW5JdGVtKHRoaXMucGFyc2VSZXN0KCkpKTtcbiAgICAgICAgYnJlYWs7XG4gICAgICB9IGVsc2Uge1xuICAgICAgICBpZiAodGhpcy50eXBlID09PSB0dC5wYXJlbkwgJiYgIWlubmVyUGFyZW5TdGFydCkge1xuICAgICAgICAgIGlubmVyUGFyZW5TdGFydCA9IHRoaXMuc3RhcnQ7XG4gICAgICAgIH1cbiAgICAgICAgZXhwckxpc3QucHVzaCh0aGlzLnBhcnNlTWF5YmVBc3NpZ24oZmFsc2UsIHJlZlNob3J0aGFuZERlZmF1bHRQb3MsIHRoaXMucGFyc2VQYXJlbkl0ZW0pKTtcbiAgICAgIH1cbiAgICB9XG4gICAgdmFyIGlubmVyRW5kUG9zID0gdGhpcy5zdGFydCxcbiAgICAgICAgaW5uZXJFbmRMb2MgPSB0aGlzLnN0YXJ0TG9jO1xuICAgIHRoaXMuZXhwZWN0KHR0LnBhcmVuUik7XG5cbiAgICBpZiAoY2FuQmVBcnJvdyAmJiAhdGhpcy5jYW5JbnNlcnRTZW1pY29sb24oKSAmJiB0aGlzLmVhdCh0dC5hcnJvdykpIHtcbiAgICAgIGlmIChpbm5lclBhcmVuU3RhcnQpIHRoaXMudW5leHBlY3RlZChpbm5lclBhcmVuU3RhcnQpO1xuICAgICAgcmV0dXJuIHRoaXMucGFyc2VQYXJlbkFycm93TGlzdChzdGFydFBvcywgc3RhcnRMb2MsIGV4cHJMaXN0KTtcbiAgICB9XG5cbiAgICBpZiAoIWV4cHJMaXN0Lmxlbmd0aCkgdGhpcy51bmV4cGVjdGVkKHRoaXMubGFzdFRva1N0YXJ0KTtcbiAgICBpZiAoc3ByZWFkU3RhcnQpIHRoaXMudW5leHBlY3RlZChzcHJlYWRTdGFydCk7XG4gICAgaWYgKHJlZlNob3J0aGFuZERlZmF1bHRQb3Muc3RhcnQpIHRoaXMudW5leHBlY3RlZChyZWZTaG9ydGhhbmREZWZhdWx0UG9zLnN0YXJ0KTtcblxuICAgIGlmIChleHByTGlzdC5sZW5ndGggPiAxKSB7XG4gICAgICB2YWwgPSB0aGlzLnN0YXJ0Tm9kZUF0KGlubmVyU3RhcnRQb3MsIGlubmVyU3RhcnRMb2MpO1xuICAgICAgdmFsLmV4cHJlc3Npb25zID0gZXhwckxpc3Q7XG4gICAgICB0aGlzLmZpbmlzaE5vZGVBdCh2YWwsIFwiU2VxdWVuY2VFeHByZXNzaW9uXCIsIGlubmVyRW5kUG9zLCBpbm5lckVuZExvYyk7XG4gICAgfSBlbHNlIHtcbiAgICAgIHZhbCA9IGV4cHJMaXN0WzBdO1xuICAgIH1cbiAgfSBlbHNlIHtcbiAgICB2YWwgPSB0aGlzLnBhcnNlUGFyZW5FeHByZXNzaW9uKCk7XG4gIH1cblxuICBpZiAodGhpcy5vcHRpb25zLnByZXNlcnZlUGFyZW5zKSB7XG4gICAgdmFyIHBhciA9IHRoaXMuc3RhcnROb2RlQXQoc3RhcnRQb3MsIHN0YXJ0TG9jKTtcbiAgICBwYXIuZXhwcmVzc2lvbiA9IHZhbDtcbiAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKHBhciwgXCJQYXJlbnRoZXNpemVkRXhwcmVzc2lvblwiKTtcbiAgfSBlbHNlIHtcbiAgICByZXR1cm4gdmFsO1xuICB9XG59O1xuXG5wcC5wYXJzZVBhcmVuSXRlbSA9IGZ1bmN0aW9uIChpdGVtKSB7XG4gIHJldHVybiBpdGVtO1xufTtcblxucHAucGFyc2VQYXJlbkFycm93TGlzdCA9IGZ1bmN0aW9uIChzdGFydFBvcywgc3RhcnRMb2MsIGV4cHJMaXN0KSB7XG4gIHJldHVybiB0aGlzLnBhcnNlQXJyb3dFeHByZXNzaW9uKHRoaXMuc3RhcnROb2RlQXQoc3RhcnRQb3MsIHN0YXJ0TG9jKSwgZXhwckxpc3QpO1xufTtcblxuLy8gTmV3J3MgcHJlY2VkZW5jZSBpcyBzbGlnaHRseSB0cmlja3kuIEl0IG11c3QgYWxsb3cgaXRzIGFyZ3VtZW50XG4vLyB0byBiZSBhIGBbXWAgb3IgZG90IHN1YnNjcmlwdCBleHByZXNzaW9uLCBidXQgbm90IGEgY2FsbCDigJQgYXRcbi8vIGxlYXN0LCBub3Qgd2l0aG91dCB3cmFwcGluZyBpdCBpbiBwYXJlbnRoZXNlcy4gVGh1cywgaXQgdXNlcyB0aGVcblxudmFyIGVtcHR5ID0gW107XG5cbnBwLnBhcnNlTmV3ID0gZnVuY3Rpb24gKCkge1xuICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gIHZhciBtZXRhID0gdGhpcy5wYXJzZUlkZW50KHRydWUpO1xuICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYgJiYgdGhpcy5lYXQodHQuZG90KSkge1xuICAgIG5vZGUubWV0YSA9IG1ldGE7XG4gICAgbm9kZS5wcm9wZXJ0eSA9IHRoaXMucGFyc2VJZGVudCh0cnVlKTtcbiAgICBpZiAobm9kZS5wcm9wZXJ0eS5uYW1lICE9PSBcInRhcmdldFwiKSB0aGlzLnJhaXNlKG5vZGUucHJvcGVydHkuc3RhcnQsIFwiVGhlIG9ubHkgdmFsaWQgbWV0YSBwcm9wZXJ0eSBmb3IgbmV3IGlzIG5ldy50YXJnZXRcIik7XG4gICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIk1ldGFQcm9wZXJ0eVwiKTtcbiAgfVxuICB2YXIgc3RhcnRQb3MgPSB0aGlzLnN0YXJ0LFxuICAgICAgc3RhcnRMb2MgPSB0aGlzLnN0YXJ0TG9jO1xuICBub2RlLmNhbGxlZSA9IHRoaXMucGFyc2VTdWJzY3JpcHRzKHRoaXMucGFyc2VFeHByQXRvbSgpLCBzdGFydFBvcywgc3RhcnRMb2MsIHRydWUpO1xuICBpZiAodGhpcy5lYXQodHQucGFyZW5MKSkgbm9kZS5hcmd1bWVudHMgPSB0aGlzLnBhcnNlRXhwckxpc3QodHQucGFyZW5SLCBmYWxzZSk7ZWxzZSBub2RlLmFyZ3VtZW50cyA9IGVtcHR5O1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiTmV3RXhwcmVzc2lvblwiKTtcbn07XG5cbi8vIFBhcnNlIHRlbXBsYXRlIGV4cHJlc3Npb24uXG5cbnBwLnBhcnNlVGVtcGxhdGVFbGVtZW50ID0gZnVuY3Rpb24gKCkge1xuICB2YXIgZWxlbSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gIGVsZW0udmFsdWUgPSB7XG4gICAgcmF3OiB0aGlzLmlucHV0LnNsaWNlKHRoaXMuc3RhcnQsIHRoaXMuZW5kKSxcbiAgICBjb29rZWQ6IHRoaXMudmFsdWVcbiAgfTtcbiAgdGhpcy5uZXh0KCk7XG4gIGVsZW0udGFpbCA9IHRoaXMudHlwZSA9PT0gdHQuYmFja1F1b3RlO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKGVsZW0sIFwiVGVtcGxhdGVFbGVtZW50XCIpO1xufTtcblxucHAucGFyc2VUZW1wbGF0ZSA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICB0aGlzLm5leHQoKTtcbiAgbm9kZS5leHByZXNzaW9ucyA9IFtdO1xuICB2YXIgY3VyRWx0ID0gdGhpcy5wYXJzZVRlbXBsYXRlRWxlbWVudCgpO1xuICBub2RlLnF1YXNpcyA9IFtjdXJFbHRdO1xuICB3aGlsZSAoIWN1ckVsdC50YWlsKSB7XG4gICAgdGhpcy5leHBlY3QodHQuZG9sbGFyQnJhY2VMKTtcbiAgICBub2RlLmV4cHJlc3Npb25zLnB1c2godGhpcy5wYXJzZUV4cHJlc3Npb24oKSk7XG4gICAgdGhpcy5leHBlY3QodHQuYnJhY2VSKTtcbiAgICBub2RlLnF1YXNpcy5wdXNoKGN1ckVsdCA9IHRoaXMucGFyc2VUZW1wbGF0ZUVsZW1lbnQoKSk7XG4gIH1cbiAgdGhpcy5uZXh0KCk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJUZW1wbGF0ZUxpdGVyYWxcIik7XG59O1xuXG4vLyBQYXJzZSBhbiBvYmplY3QgbGl0ZXJhbCBvciBiaW5kaW5nIHBhdHRlcm4uXG5cbnBwLnBhcnNlT2JqID0gZnVuY3Rpb24gKGlzUGF0dGVybiwgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcykge1xuICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCksXG4gICAgICBmaXJzdCA9IHRydWUsXG4gICAgICBwcm9wSGFzaCA9IHt9O1xuICBub2RlLnByb3BlcnRpZXMgPSBbXTtcbiAgdGhpcy5uZXh0KCk7XG4gIHdoaWxlICghdGhpcy5lYXQodHQuYnJhY2VSKSkge1xuICAgIGlmICghZmlyc3QpIHtcbiAgICAgIHRoaXMuZXhwZWN0KHR0LmNvbW1hKTtcbiAgICAgIGlmICh0aGlzLmFmdGVyVHJhaWxpbmdDb21tYSh0dC5icmFjZVIpKSBicmVhaztcbiAgICB9IGVsc2UgZmlyc3QgPSBmYWxzZTtcblxuICAgIHZhciBwcm9wID0gdGhpcy5zdGFydE5vZGUoKSxcbiAgICAgICAgaXNHZW5lcmF0b3IgPSB1bmRlZmluZWQsXG4gICAgICAgIHN0YXJ0UG9zID0gdW5kZWZpbmVkLFxuICAgICAgICBzdGFydExvYyA9IHVuZGVmaW5lZDtcbiAgICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYpIHtcbiAgICAgIHByb3AubWV0aG9kID0gZmFsc2U7XG4gICAgICBwcm9wLnNob3J0aGFuZCA9IGZhbHNlO1xuICAgICAgaWYgKGlzUGF0dGVybiB8fCByZWZTaG9ydGhhbmREZWZhdWx0UG9zKSB7XG4gICAgICAgIHN0YXJ0UG9zID0gdGhpcy5zdGFydDtcbiAgICAgICAgc3RhcnRMb2MgPSB0aGlzLnN0YXJ0TG9jO1xuICAgICAgfVxuICAgICAgaWYgKCFpc1BhdHRlcm4pIGlzR2VuZXJhdG9yID0gdGhpcy5lYXQodHQuc3Rhcik7XG4gICAgfVxuICAgIHRoaXMucGFyc2VQcm9wZXJ0eU5hbWUocHJvcCk7XG4gICAgdGhpcy5wYXJzZVByb3BlcnR5VmFsdWUocHJvcCwgaXNQYXR0ZXJuLCBpc0dlbmVyYXRvciwgc3RhcnRQb3MsIHN0YXJ0TG9jLCByZWZTaG9ydGhhbmREZWZhdWx0UG9zKTtcbiAgICB0aGlzLmNoZWNrUHJvcENsYXNoKHByb3AsIHByb3BIYXNoKTtcbiAgICBub2RlLnByb3BlcnRpZXMucHVzaCh0aGlzLmZpbmlzaE5vZGUocHJvcCwgXCJQcm9wZXJ0eVwiKSk7XG4gIH1cbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBpc1BhdHRlcm4gPyBcIk9iamVjdFBhdHRlcm5cIiA6IFwiT2JqZWN0RXhwcmVzc2lvblwiKTtcbn07XG5cbnBwLnBhcnNlUHJvcGVydHlWYWx1ZSA9IGZ1bmN0aW9uIChwcm9wLCBpc1BhdHRlcm4sIGlzR2VuZXJhdG9yLCBzdGFydFBvcywgc3RhcnRMb2MsIHJlZlNob3J0aGFuZERlZmF1bHRQb3MpIHtcbiAgaWYgKHRoaXMuZWF0KHR0LmNvbG9uKSkge1xuICAgIHByb3AudmFsdWUgPSBpc1BhdHRlcm4gPyB0aGlzLnBhcnNlTWF5YmVEZWZhdWx0KHRoaXMuc3RhcnQsIHRoaXMuc3RhcnRMb2MpIDogdGhpcy5wYXJzZU1heWJlQXNzaWduKGZhbHNlLCByZWZTaG9ydGhhbmREZWZhdWx0UG9zKTtcbiAgICBwcm9wLmtpbmQgPSBcImluaXRcIjtcbiAgfSBlbHNlIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNiAmJiB0aGlzLnR5cGUgPT09IHR0LnBhcmVuTCkge1xuICAgIGlmIChpc1BhdHRlcm4pIHRoaXMudW5leHBlY3RlZCgpO1xuICAgIHByb3Aua2luZCA9IFwiaW5pdFwiO1xuICAgIHByb3AubWV0aG9kID0gdHJ1ZTtcbiAgICBwcm9wLnZhbHVlID0gdGhpcy5wYXJzZU1ldGhvZChpc0dlbmVyYXRvcik7XG4gIH0gZWxzZSBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDUgJiYgIXByb3AuY29tcHV0ZWQgJiYgcHJvcC5rZXkudHlwZSA9PT0gXCJJZGVudGlmaWVyXCIgJiYgKHByb3Aua2V5Lm5hbWUgPT09IFwiZ2V0XCIgfHwgcHJvcC5rZXkubmFtZSA9PT0gXCJzZXRcIikgJiYgKHRoaXMudHlwZSAhPSB0dC5jb21tYSAmJiB0aGlzLnR5cGUgIT0gdHQuYnJhY2VSKSkge1xuICAgIGlmIChpc0dlbmVyYXRvciB8fCBpc1BhdHRlcm4pIHRoaXMudW5leHBlY3RlZCgpO1xuICAgIHByb3Aua2luZCA9IHByb3Aua2V5Lm5hbWU7XG4gICAgdGhpcy5wYXJzZVByb3BlcnR5TmFtZShwcm9wKTtcbiAgICBwcm9wLnZhbHVlID0gdGhpcy5wYXJzZU1ldGhvZChmYWxzZSk7XG4gIH0gZWxzZSBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYgJiYgIXByb3AuY29tcHV0ZWQgJiYgcHJvcC5rZXkudHlwZSA9PT0gXCJJZGVudGlmaWVyXCIpIHtcbiAgICBwcm9wLmtpbmQgPSBcImluaXRcIjtcbiAgICBpZiAoaXNQYXR0ZXJuKSB7XG4gICAgICBpZiAodGhpcy5pc0tleXdvcmQocHJvcC5rZXkubmFtZSkgfHwgdGhpcy5zdHJpY3QgJiYgKHJlc2VydmVkV29yZHMuc3RyaWN0QmluZChwcm9wLmtleS5uYW1lKSB8fCByZXNlcnZlZFdvcmRzLnN0cmljdChwcm9wLmtleS5uYW1lKSkgfHwgIXRoaXMub3B0aW9ucy5hbGxvd1Jlc2VydmVkICYmIHRoaXMuaXNSZXNlcnZlZFdvcmQocHJvcC5rZXkubmFtZSkpIHRoaXMucmFpc2UocHJvcC5rZXkuc3RhcnQsIFwiQmluZGluZyBcIiArIHByb3Aua2V5Lm5hbWUpO1xuICAgICAgcHJvcC52YWx1ZSA9IHRoaXMucGFyc2VNYXliZURlZmF1bHQoc3RhcnRQb3MsIHN0YXJ0TG9jLCBwcm9wLmtleSk7XG4gICAgfSBlbHNlIGlmICh0aGlzLnR5cGUgPT09IHR0LmVxICYmIHJlZlNob3J0aGFuZERlZmF1bHRQb3MpIHtcbiAgICAgIGlmICghcmVmU2hvcnRoYW5kRGVmYXVsdFBvcy5zdGFydCkgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcy5zdGFydCA9IHRoaXMuc3RhcnQ7XG4gICAgICBwcm9wLnZhbHVlID0gdGhpcy5wYXJzZU1heWJlRGVmYXVsdChzdGFydFBvcywgc3RhcnRMb2MsIHByb3Aua2V5KTtcbiAgICB9IGVsc2Uge1xuICAgICAgcHJvcC52YWx1ZSA9IHByb3Aua2V5O1xuICAgIH1cbiAgICBwcm9wLnNob3J0aGFuZCA9IHRydWU7XG4gIH0gZWxzZSB0aGlzLnVuZXhwZWN0ZWQoKTtcbn07XG5cbnBwLnBhcnNlUHJvcGVydHlOYW1lID0gZnVuY3Rpb24gKHByb3ApIHtcbiAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KSB7XG4gICAgaWYgKHRoaXMuZWF0KHR0LmJyYWNrZXRMKSkge1xuICAgICAgcHJvcC5jb21wdXRlZCA9IHRydWU7XG4gICAgICBwcm9wLmtleSA9IHRoaXMucGFyc2VNYXliZUFzc2lnbigpO1xuICAgICAgdGhpcy5leHBlY3QodHQuYnJhY2tldFIpO1xuICAgICAgcmV0dXJuIHByb3Aua2V5O1xuICAgIH0gZWxzZSB7XG4gICAgICBwcm9wLmNvbXB1dGVkID0gZmFsc2U7XG4gICAgfVxuICB9XG4gIHJldHVybiBwcm9wLmtleSA9IHRoaXMudHlwZSA9PT0gdHQubnVtIHx8IHRoaXMudHlwZSA9PT0gdHQuc3RyaW5nID8gdGhpcy5wYXJzZUV4cHJBdG9tKCkgOiB0aGlzLnBhcnNlSWRlbnQodHJ1ZSk7XG59O1xuXG4vLyBJbml0aWFsaXplIGVtcHR5IGZ1bmN0aW9uIG5vZGUuXG5cbnBwLmluaXRGdW5jdGlvbiA9IGZ1bmN0aW9uIChub2RlKSB7XG4gIG5vZGUuaWQgPSBudWxsO1xuICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYpIHtcbiAgICBub2RlLmdlbmVyYXRvciA9IGZhbHNlO1xuICAgIG5vZGUuZXhwcmVzc2lvbiA9IGZhbHNlO1xuICB9XG59O1xuXG4vLyBQYXJzZSBvYmplY3Qgb3IgY2xhc3MgbWV0aG9kLlxuXG5wcC5wYXJzZU1ldGhvZCA9IGZ1bmN0aW9uIChpc0dlbmVyYXRvcikge1xuICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gIHRoaXMuaW5pdEZ1bmN0aW9uKG5vZGUpO1xuICB0aGlzLmV4cGVjdCh0dC5wYXJlbkwpO1xuICBub2RlLnBhcmFtcyA9IHRoaXMucGFyc2VCaW5kaW5nTGlzdCh0dC5wYXJlblIsIGZhbHNlLCBmYWxzZSk7XG4gIHZhciBhbGxvd0V4cHJlc3Npb25Cb2R5ID0gdW5kZWZpbmVkO1xuICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYpIHtcbiAgICBub2RlLmdlbmVyYXRvciA9IGlzR2VuZXJhdG9yO1xuICAgIGFsbG93RXhwcmVzc2lvbkJvZHkgPSB0cnVlO1xuICB9IGVsc2Uge1xuICAgIGFsbG93RXhwcmVzc2lvbkJvZHkgPSBmYWxzZTtcbiAgfVxuICB0aGlzLnBhcnNlRnVuY3Rpb25Cb2R5KG5vZGUsIGFsbG93RXhwcmVzc2lvbkJvZHkpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiRnVuY3Rpb25FeHByZXNzaW9uXCIpO1xufTtcblxuLy8gUGFyc2UgYXJyb3cgZnVuY3Rpb24gZXhwcmVzc2lvbiB3aXRoIGdpdmVuIHBhcmFtZXRlcnMuXG5cbnBwLnBhcnNlQXJyb3dFeHByZXNzaW9uID0gZnVuY3Rpb24gKG5vZGUsIHBhcmFtcykge1xuICB0aGlzLmluaXRGdW5jdGlvbihub2RlKTtcbiAgbm9kZS5wYXJhbXMgPSB0aGlzLnRvQXNzaWduYWJsZUxpc3QocGFyYW1zLCB0cnVlKTtcbiAgdGhpcy5wYXJzZUZ1bmN0aW9uQm9keShub2RlLCB0cnVlKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkFycm93RnVuY3Rpb25FeHByZXNzaW9uXCIpO1xufTtcblxuLy8gUGFyc2UgZnVuY3Rpb24gYm9keSBhbmQgY2hlY2sgcGFyYW1ldGVycy5cblxucHAucGFyc2VGdW5jdGlvbkJvZHkgPSBmdW5jdGlvbiAobm9kZSwgYWxsb3dFeHByZXNzaW9uKSB7XG4gIHZhciBpc0V4cHJlc3Npb24gPSBhbGxvd0V4cHJlc3Npb24gJiYgdGhpcy50eXBlICE9PSB0dC5icmFjZUw7XG5cbiAgaWYgKGlzRXhwcmVzc2lvbikge1xuICAgIG5vZGUuYm9keSA9IHRoaXMucGFyc2VNYXliZUFzc2lnbigpO1xuICAgIG5vZGUuZXhwcmVzc2lvbiA9IHRydWU7XG4gIH0gZWxzZSB7XG4gICAgLy8gU3RhcnQgYSBuZXcgc2NvcGUgd2l0aCByZWdhcmQgdG8gbGFiZWxzIGFuZCB0aGUgYGluRnVuY3Rpb25gXG4gICAgLy8gZmxhZyAocmVzdG9yZSB0aGVtIHRvIHRoZWlyIG9sZCB2YWx1ZSBhZnRlcndhcmRzKS5cbiAgICB2YXIgb2xkSW5GdW5jID0gdGhpcy5pbkZ1bmN0aW9uLFxuICAgICAgICBvbGRJbkdlbiA9IHRoaXMuaW5HZW5lcmF0b3IsXG4gICAgICAgIG9sZExhYmVscyA9IHRoaXMubGFiZWxzO1xuICAgIHRoaXMuaW5GdW5jdGlvbiA9IHRydWU7dGhpcy5pbkdlbmVyYXRvciA9IG5vZGUuZ2VuZXJhdG9yO3RoaXMubGFiZWxzID0gW107XG4gICAgbm9kZS5ib2R5ID0gdGhpcy5wYXJzZUJsb2NrKHRydWUpO1xuICAgIG5vZGUuZXhwcmVzc2lvbiA9IGZhbHNlO1xuICAgIHRoaXMuaW5GdW5jdGlvbiA9IG9sZEluRnVuYzt0aGlzLmluR2VuZXJhdG9yID0gb2xkSW5HZW47dGhpcy5sYWJlbHMgPSBvbGRMYWJlbHM7XG4gIH1cblxuICAvLyBJZiB0aGlzIGlzIGEgc3RyaWN0IG1vZGUgZnVuY3Rpb24sIHZlcmlmeSB0aGF0IGFyZ3VtZW50IG5hbWVzXG4gIC8vIGFyZSBub3QgcmVwZWF0ZWQsIGFuZCBpdCBkb2VzIG5vdCB0cnkgdG8gYmluZCB0aGUgd29yZHMgYGV2YWxgXG4gIC8vIG9yIGBhcmd1bWVudHNgLlxuICBpZiAodGhpcy5zdHJpY3QgfHwgIWlzRXhwcmVzc2lvbiAmJiBub2RlLmJvZHkuYm9keS5sZW5ndGggJiYgdGhpcy5pc1VzZVN0cmljdChub2RlLmJvZHkuYm9keVswXSkpIHtcbiAgICB2YXIgbmFtZUhhc2ggPSB7fSxcbiAgICAgICAgb2xkU3RyaWN0ID0gdGhpcy5zdHJpY3Q7XG4gICAgdGhpcy5zdHJpY3QgPSB0cnVlO1xuICAgIGlmIChub2RlLmlkKSB0aGlzLmNoZWNrTFZhbChub2RlLmlkLCB0cnVlKTtcbiAgICBmb3IgKHZhciBpID0gMDsgaSA8IG5vZGUucGFyYW1zLmxlbmd0aDsgaSsrKSB7XG4gICAgICB0aGlzLmNoZWNrTFZhbChub2RlLnBhcmFtc1tpXSwgdHJ1ZSwgbmFtZUhhc2gpO1xuICAgIH10aGlzLnN0cmljdCA9IG9sZFN0cmljdDtcbiAgfVxufTtcblxuLy8gUGFyc2VzIGEgY29tbWEtc2VwYXJhdGVkIGxpc3Qgb2YgZXhwcmVzc2lvbnMsIGFuZCByZXR1cm5zIHRoZW0gYXNcbi8vIGFuIGFycmF5LiBgY2xvc2VgIGlzIHRoZSB0b2tlbiB0eXBlIHRoYXQgZW5kcyB0aGUgbGlzdCwgYW5kXG4vLyBgYWxsb3dFbXB0eWAgY2FuIGJlIHR1cm5lZCBvbiB0byBhbGxvdyBzdWJzZXF1ZW50IGNvbW1hcyB3aXRoXG4vLyBub3RoaW5nIGluIGJldHdlZW4gdGhlbSB0byBiZSBwYXJzZWQgYXMgYG51bGxgICh3aGljaCBpcyBuZWVkZWRcbi8vIGZvciBhcnJheSBsaXRlcmFscykuXG5cbnBwLnBhcnNlRXhwckxpc3QgPSBmdW5jdGlvbiAoY2xvc2UsIGFsbG93VHJhaWxpbmdDb21tYSwgYWxsb3dFbXB0eSwgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcykge1xuICB2YXIgZWx0cyA9IFtdLFxuICAgICAgZmlyc3QgPSB0cnVlO1xuICB3aGlsZSAoIXRoaXMuZWF0KGNsb3NlKSkge1xuICAgIGlmICghZmlyc3QpIHtcbiAgICAgIHRoaXMuZXhwZWN0KHR0LmNvbW1hKTtcbiAgICAgIGlmIChhbGxvd1RyYWlsaW5nQ29tbWEgJiYgdGhpcy5hZnRlclRyYWlsaW5nQ29tbWEoY2xvc2UpKSBicmVhaztcbiAgICB9IGVsc2UgZmlyc3QgPSBmYWxzZTtcblxuICAgIGlmIChhbGxvd0VtcHR5ICYmIHRoaXMudHlwZSA9PT0gdHQuY29tbWEpIHtcbiAgICAgIGVsdHMucHVzaChudWxsKTtcbiAgICB9IGVsc2Uge1xuICAgICAgaWYgKHRoaXMudHlwZSA9PT0gdHQuZWxsaXBzaXMpIGVsdHMucHVzaCh0aGlzLnBhcnNlU3ByZWFkKHJlZlNob3J0aGFuZERlZmF1bHRQb3MpKTtlbHNlIGVsdHMucHVzaCh0aGlzLnBhcnNlTWF5YmVBc3NpZ24oZmFsc2UsIHJlZlNob3J0aGFuZERlZmF1bHRQb3MpKTtcbiAgICB9XG4gIH1cbiAgcmV0dXJuIGVsdHM7XG59O1xuXG4vLyBQYXJzZSB0aGUgbmV4dCB0b2tlbiBhcyBhbiBpZGVudGlmaWVyLiBJZiBgbGliZXJhbGAgaXMgdHJ1ZSAodXNlZFxuLy8gd2hlbiBwYXJzaW5nIHByb3BlcnRpZXMpLCBpdCB3aWxsIGFsc28gY29udmVydCBrZXl3b3JkcyBpbnRvXG4vLyBpZGVudGlmaWVycy5cblxucHAucGFyc2VJZGVudCA9IGZ1bmN0aW9uIChsaWJlcmFsKSB7XG4gIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgaWYgKGxpYmVyYWwgJiYgdGhpcy5vcHRpb25zLmFsbG93UmVzZXJ2ZWQgPT0gXCJuZXZlclwiKSBsaWJlcmFsID0gZmFsc2U7XG4gIGlmICh0aGlzLnR5cGUgPT09IHR0Lm5hbWUpIHtcbiAgICBpZiAoIWxpYmVyYWwgJiYgKCF0aGlzLm9wdGlvbnMuYWxsb3dSZXNlcnZlZCAmJiB0aGlzLmlzUmVzZXJ2ZWRXb3JkKHRoaXMudmFsdWUpIHx8IHRoaXMuc3RyaWN0ICYmIHJlc2VydmVkV29yZHMuc3RyaWN0KHRoaXMudmFsdWUpICYmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNiB8fCB0aGlzLmlucHV0LnNsaWNlKHRoaXMuc3RhcnQsIHRoaXMuZW5kKS5pbmRleE9mKFwiXFxcXFwiKSA9PSAtMSkpKSB0aGlzLnJhaXNlKHRoaXMuc3RhcnQsIFwiVGhlIGtleXdvcmQgJ1wiICsgdGhpcy52YWx1ZSArIFwiJyBpcyByZXNlcnZlZFwiKTtcbiAgICBub2RlLm5hbWUgPSB0aGlzLnZhbHVlO1xuICB9IGVsc2UgaWYgKGxpYmVyYWwgJiYgdGhpcy50eXBlLmtleXdvcmQpIHtcbiAgICBub2RlLm5hbWUgPSB0aGlzLnR5cGUua2V5d29yZDtcbiAgfSBlbHNlIHtcbiAgICB0aGlzLnVuZXhwZWN0ZWQoKTtcbiAgfVxuICB0aGlzLm5leHQoKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIklkZW50aWZpZXJcIik7XG59O1xuXG4vLyBQYXJzZXMgeWllbGQgZXhwcmVzc2lvbiBpbnNpZGUgZ2VuZXJhdG9yLlxuXG5wcC5wYXJzZVlpZWxkID0gZnVuY3Rpb24gKCkge1xuICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gIHRoaXMubmV4dCgpO1xuICBpZiAodGhpcy50eXBlID09IHR0LnNlbWkgfHwgdGhpcy5jYW5JbnNlcnRTZW1pY29sb24oKSB8fCB0aGlzLnR5cGUgIT0gdHQuc3RhciAmJiAhdGhpcy50eXBlLnN0YXJ0c0V4cHIpIHtcbiAgICBub2RlLmRlbGVnYXRlID0gZmFsc2U7XG4gICAgbm9kZS5hcmd1bWVudCA9IG51bGw7XG4gIH0gZWxzZSB7XG4gICAgbm9kZS5kZWxlZ2F0ZSA9IHRoaXMuZWF0KHR0LnN0YXIpO1xuICAgIG5vZGUuYXJndW1lbnQgPSB0aGlzLnBhcnNlTWF5YmVBc3NpZ24oKTtcbiAgfVxuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiWWllbGRFeHByZXNzaW9uXCIpO1xufTtcblxuLy8gUGFyc2VzIGFycmF5IGFuZCBnZW5lcmF0b3IgY29tcHJlaGVuc2lvbnMuXG5cbnBwLnBhcnNlQ29tcHJlaGVuc2lvbiA9IGZ1bmN0aW9uIChub2RlLCBpc0dlbmVyYXRvcikge1xuICBub2RlLmJsb2NrcyA9IFtdO1xuICB3aGlsZSAodGhpcy50eXBlID09PSB0dC5fZm9yKSB7XG4gICAgdmFyIGJsb2NrID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgICB0aGlzLm5leHQoKTtcbiAgICB0aGlzLmV4cGVjdCh0dC5wYXJlbkwpO1xuICAgIGJsb2NrLmxlZnQgPSB0aGlzLnBhcnNlQmluZGluZ0F0b20oKTtcbiAgICB0aGlzLmNoZWNrTFZhbChibG9jay5sZWZ0LCB0cnVlKTtcbiAgICB0aGlzLmV4cGVjdENvbnRleHR1YWwoXCJvZlwiKTtcbiAgICBibG9jay5yaWdodCA9IHRoaXMucGFyc2VFeHByZXNzaW9uKCk7XG4gICAgdGhpcy5leHBlY3QodHQucGFyZW5SKTtcbiAgICBub2RlLmJsb2Nrcy5wdXNoKHRoaXMuZmluaXNoTm9kZShibG9jaywgXCJDb21wcmVoZW5zaW9uQmxvY2tcIikpO1xuICB9XG4gIG5vZGUuZmlsdGVyID0gdGhpcy5lYXQodHQuX2lmKSA/IHRoaXMucGFyc2VQYXJlbkV4cHJlc3Npb24oKSA6IG51bGw7XG4gIG5vZGUuYm9keSA9IHRoaXMucGFyc2VFeHByZXNzaW9uKCk7XG4gIHRoaXMuZXhwZWN0KGlzR2VuZXJhdG9yID8gdHQucGFyZW5SIDogdHQuYnJhY2tldFIpO1xuICBub2RlLmdlbmVyYXRvciA9IGlzR2VuZXJhdG9yO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiQ29tcHJlaGVuc2lvbkV4cHJlc3Npb25cIik7XG59O1xuXG59LHtcIi4vaWRlbnRpZmllclwiOjcsXCIuL3N0YXRlXCI6MTMsXCIuL3Rva2VudHlwZVwiOjE3LFwiLi91dGlsXCI6MTh9XSw3OltmdW5jdGlvbihfZGVyZXFfLG1vZHVsZSxleHBvcnRzKXtcblxuXG4vLyBUZXN0IHdoZXRoZXIgYSBnaXZlbiBjaGFyYWN0ZXIgY29kZSBzdGFydHMgYW4gaWRlbnRpZmllci5cblxuXCJ1c2Ugc3RyaWN0XCI7XG5cbmV4cG9ydHMuaXNJZGVudGlmaWVyU3RhcnQgPSBpc0lkZW50aWZpZXJTdGFydDtcblxuLy8gVGVzdCB3aGV0aGVyIGEgZ2l2ZW4gY2hhcmFjdGVyIGlzIHBhcnQgb2YgYW4gaWRlbnRpZmllci5cblxuZXhwb3J0cy5pc0lkZW50aWZpZXJDaGFyID0gaXNJZGVudGlmaWVyQ2hhcjtcbmV4cG9ydHMuX19lc01vZHVsZSA9IHRydWU7XG4vLyBUaGlzIGlzIGEgdHJpY2sgdGFrZW4gZnJvbSBFc3ByaW1hLiBJdCB0dXJucyBvdXQgdGhhdCwgb25cbi8vIG5vbi1DaHJvbWUgYnJvd3NlcnMsIHRvIGNoZWNrIHdoZXRoZXIgYSBzdHJpbmcgaXMgaW4gYSBzZXQsIGFcbi8vIHByZWRpY2F0ZSBjb250YWluaW5nIGEgYmlnIHVnbHkgYHN3aXRjaGAgc3RhdGVtZW50IGlzIGZhc3RlciB0aGFuXG4vLyBhIHJlZ3VsYXIgZXhwcmVzc2lvbiwgYW5kIG9uIENocm9tZSB0aGUgdHdvIGFyZSBhYm91dCBvbiBwYXIuXG4vLyBUaGlzIGZ1bmN0aW9uIHVzZXMgYGV2YWxgIChub24tbGV4aWNhbCkgdG8gcHJvZHVjZSBzdWNoIGFcbi8vIHByZWRpY2F0ZSBmcm9tIGEgc3BhY2Utc2VwYXJhdGVkIHN0cmluZyBvZiB3b3Jkcy5cbi8vXG4vLyBJdCBzdGFydHMgYnkgc29ydGluZyB0aGUgd29yZHMgYnkgbGVuZ3RoLlxuXG5mdW5jdGlvbiBtYWtlUHJlZGljYXRlKHdvcmRzKSB7XG4gIHdvcmRzID0gd29yZHMuc3BsaXQoXCIgXCIpO1xuICB2YXIgZiA9IFwiXCIsXG4gICAgICBjYXRzID0gW107XG4gIG91dDogZm9yICh2YXIgaSA9IDA7IGkgPCB3b3Jkcy5sZW5ndGg7ICsraSkge1xuICAgIGZvciAodmFyIGogPSAwOyBqIDwgY2F0cy5sZW5ndGg7ICsraikge1xuICAgICAgaWYgKGNhdHNbal1bMF0ubGVuZ3RoID09IHdvcmRzW2ldLmxlbmd0aCkge1xuICAgICAgICBjYXRzW2pdLnB1c2god29yZHNbaV0pO1xuICAgICAgICBjb250aW51ZSBvdXQ7XG4gICAgICB9XG4gICAgfWNhdHMucHVzaChbd29yZHNbaV1dKTtcbiAgfVxuICBmdW5jdGlvbiBjb21wYXJlVG8oYXJyKSB7XG4gICAgaWYgKGFyci5sZW5ndGggPT0gMSkge1xuICAgICAgcmV0dXJuIGYgKz0gXCJyZXR1cm4gc3RyID09PSBcIiArIEpTT04uc3RyaW5naWZ5KGFyclswXSkgKyBcIjtcIjtcbiAgICB9ZiArPSBcInN3aXRjaChzdHIpe1wiO1xuICAgIGZvciAodmFyIGkgPSAwOyBpIDwgYXJyLmxlbmd0aDsgKytpKSB7XG4gICAgICBmICs9IFwiY2FzZSBcIiArIEpTT04uc3RyaW5naWZ5KGFycltpXSkgKyBcIjpcIjtcbiAgICB9ZiArPSBcInJldHVybiB0cnVlfXJldHVybiBmYWxzZTtcIjtcbiAgfVxuXG4gIC8vIFdoZW4gdGhlcmUgYXJlIG1vcmUgdGhhbiB0aHJlZSBsZW5ndGggY2F0ZWdvcmllcywgYW4gb3V0ZXJcbiAgLy8gc3dpdGNoIGZpcnN0IGRpc3BhdGNoZXMgb24gdGhlIGxlbmd0aHMsIHRvIHNhdmUgb24gY29tcGFyaXNvbnMuXG5cbiAgaWYgKGNhdHMubGVuZ3RoID4gMykge1xuICAgIGNhdHMuc29ydChmdW5jdGlvbiAoYSwgYikge1xuICAgICAgcmV0dXJuIGIubGVuZ3RoIC0gYS5sZW5ndGg7XG4gICAgfSk7XG4gICAgZiArPSBcInN3aXRjaChzdHIubGVuZ3RoKXtcIjtcbiAgICBmb3IgKHZhciBpID0gMDsgaSA8IGNhdHMubGVuZ3RoOyArK2kpIHtcbiAgICAgIHZhciBjYXQgPSBjYXRzW2ldO1xuICAgICAgZiArPSBcImNhc2UgXCIgKyBjYXRbMF0ubGVuZ3RoICsgXCI6XCI7XG4gICAgICBjb21wYXJlVG8oY2F0KTtcbiAgICB9XG4gICAgZiArPSBcIn1cIlxuXG4gICAgLy8gT3RoZXJ3aXNlLCBzaW1wbHkgZ2VuZXJhdGUgYSBmbGF0IGBzd2l0Y2hgIHN0YXRlbWVudC5cblxuICAgIDtcbiAgfSBlbHNlIHtcbiAgICBjb21wYXJlVG8od29yZHMpO1xuICB9XG4gIHJldHVybiBuZXcgRnVuY3Rpb24oXCJzdHJcIiwgZik7XG59XG5cbi8vIFJlc2VydmVkIHdvcmQgbGlzdHMgZm9yIHZhcmlvdXMgZGlhbGVjdHMgb2YgdGhlIGxhbmd1YWdlXG5cbnZhciByZXNlcnZlZFdvcmRzID0ge1xuICAzOiBtYWtlUHJlZGljYXRlKFwiYWJzdHJhY3QgYm9vbGVhbiBieXRlIGNoYXIgY2xhc3MgZG91YmxlIGVudW0gZXhwb3J0IGV4dGVuZHMgZmluYWwgZmxvYXQgZ290byBpbXBsZW1lbnRzIGltcG9ydCBpbnQgaW50ZXJmYWNlIGxvbmcgbmF0aXZlIHBhY2thZ2UgcHJpdmF0ZSBwcm90ZWN0ZWQgcHVibGljIHNob3J0IHN0YXRpYyBzdXBlciBzeW5jaHJvbml6ZWQgdGhyb3dzIHRyYW5zaWVudCB2b2xhdGlsZVwiKSxcbiAgNTogbWFrZVByZWRpY2F0ZShcImNsYXNzIGVudW0gZXh0ZW5kcyBzdXBlciBjb25zdCBleHBvcnQgaW1wb3J0XCIpLFxuICA2OiBtYWtlUHJlZGljYXRlKFwiZW51bSBhd2FpdFwiKSxcbiAgc3RyaWN0OiBtYWtlUHJlZGljYXRlKFwiaW1wbGVtZW50cyBpbnRlcmZhY2UgbGV0IHBhY2thZ2UgcHJpdmF0ZSBwcm90ZWN0ZWQgcHVibGljIHN0YXRpYyB5aWVsZFwiKSxcbiAgc3RyaWN0QmluZDogbWFrZVByZWRpY2F0ZShcImV2YWwgYXJndW1lbnRzXCIpXG59O1xuXG5leHBvcnRzLnJlc2VydmVkV29yZHMgPSByZXNlcnZlZFdvcmRzO1xuLy8gQW5kIHRoZSBrZXl3b3Jkc1xuXG52YXIgZWNtYTVBbmRMZXNzS2V5d29yZHMgPSBcImJyZWFrIGNhc2UgY2F0Y2ggY29udGludWUgZGVidWdnZXIgZGVmYXVsdCBkbyBlbHNlIGZpbmFsbHkgZm9yIGZ1bmN0aW9uIGlmIHJldHVybiBzd2l0Y2ggdGhyb3cgdHJ5IHZhciB3aGlsZSB3aXRoIG51bGwgdHJ1ZSBmYWxzZSBpbnN0YW5jZW9mIHR5cGVvZiB2b2lkIGRlbGV0ZSBuZXcgaW4gdGhpc1wiO1xuXG52YXIga2V5d29yZHMgPSB7XG4gIDU6IG1ha2VQcmVkaWNhdGUoZWNtYTVBbmRMZXNzS2V5d29yZHMpLFxuICA2OiBtYWtlUHJlZGljYXRlKGVjbWE1QW5kTGVzc0tleXdvcmRzICsgXCIgbGV0IGNvbnN0IGNsYXNzIGV4dGVuZHMgZXhwb3J0IGltcG9ydCB5aWVsZCBzdXBlclwiKVxufTtcblxuZXhwb3J0cy5rZXl3b3JkcyA9IGtleXdvcmRzO1xuLy8gIyMgQ2hhcmFjdGVyIGNhdGVnb3JpZXNcblxuLy8gQmlnIHVnbHkgcmVndWxhciBleHByZXNzaW9ucyB0aGF0IG1hdGNoIGNoYXJhY3RlcnMgaW4gdGhlXG4vLyB3aGl0ZXNwYWNlLCBpZGVudGlmaWVyLCBhbmQgaWRlbnRpZmllci1zdGFydCBjYXRlZ29yaWVzLiBUaGVzZVxuLy8gYXJlIG9ubHkgYXBwbGllZCB3aGVuIGEgY2hhcmFjdGVyIGlzIGZvdW5kIHRvIGFjdHVhbGx5IGhhdmUgYVxuLy8gY29kZSBwb2ludCBhYm92ZSAxMjguXG4vLyBHZW5lcmF0ZWQgYnkgYHRvb2xzL2dlbmVyYXRlLWlkZW50aWZpZXItcmVnZXguanNgLlxuXG52YXIgbm9uQVNDSUlpZGVudGlmaWVyU3RhcnRDaGFycyA9IFwiwqrCtcK6w4Atw5bDmC3DtsO4LcuBy4Yty5HLoC3LpMusy67NsC3NtM22zbfNui3Nvc2/zobOiC3Ois6Mzo4tzqHOoy3Ptc+3LdKB0oot1K/UsS3VltWZ1aEt1ofXkC3XqtewLdey2KAt2YrZrtmv2bEt25Pbldul26bbrtuv27ot27zbv9yQ3JIt3K/djS3epd6x34ot36rftN+137rgoIAt4KCV4KCa4KCk4KCo4KGALeChmOCioC3gorLgpIQt4KS54KS94KWQ4KWYLeCloeClsS3gpoDgpoUt4KaM4KaP4KaQ4KaTLeCmqOCmqi3gprDgprLgprYt4Ka54Ka94KeO4Kec4Ked4KefLeCnoeCnsOCnseCohS3gqIrgqI/gqJDgqJMt4Kio4KiqLeCosOCosuCos+CoteCotuCouOCoueCpmS3gqZzgqZ7gqbIt4Km04KqFLeCqjeCqjy3gqpHgqpMt4Kqo4KqqLeCqsOCqsuCqs+CqtS3gqrngqr3gq5Dgq6Dgq6HgrIUt4KyM4KyP4KyQ4KyTLeCsqOCsqi3grLDgrLLgrLPgrLUt4Ky54Ky94K2c4K2d4K2fLeCtoeCtseCug+CuhS3grorgro4t4K6Q4K6SLeCuleCumeCumuCunOCunuCun+Cuo+CupOCuqC3grqrgrq4t4K654K+Q4LCFLeCwjOCwji3gsJDgsJIt4LCo4LCqLeCwueCwveCxmOCxmeCxoOCxoeCyhS3gsozgso4t4LKQ4LKSLeCyqOCyqi3gsrPgsrUt4LK54LK94LOe4LOg4LOh4LOx4LOy4LSFLeC0jOC0ji3gtJDgtJIt4LS64LS94LWO4LWg4LWh4LW6LeC1v+C2hS3gtpbgtpot4Lax4LazLeC2u+C2veC3gC3gt4bguIEt4Liw4Liy4Liz4LmALeC5huC6geC6guC6hOC6h+C6iOC6iuC6jeC6lC3gupfgupkt4Lqf4LqhLeC6o+C6peC6p+C6quC6q+C6rS3gurDgurLgurPgur3gu4At4LuE4LuG4LucLeC7n+C8gOC9gC3gvYfgvYkt4L2s4L6ILeC+jOGAgC3hgKrhgL/hgZAt4YGV4YGaLeGBneGBoeGBpeGBpuGBri3hgbDhgbUt4YKB4YKO4YKgLeGDheGDh+GDjeGDkC3hg7rhg7wt4YmI4YmKLeGJjeGJkC3hiZbhiZjhiZot4Ymd4YmgLeGKiOGKii3hio3hipAt4Yqw4YqyLeGKteGKuC3hir7hi4Dhi4It4YuF4YuILeGLluGLmC3hjJDhjJIt4YyV4YyYLeGNmuGOgC3hjo/hjqAt4Y+04ZCBLeGZrOGZry3hmb/hmoEt4Zqa4ZqgLeGbquGbri3hm7jhnIAt4ZyM4ZyOLeGckeGcoC3hnLHhnYAt4Z2R4Z2gLeGdrOGdri3hnbDhnoAt4Z6z4Z+X4Z+c4aCgLeGht+GigC3hoqjhoqrhorAt4aO14aSALeGknuGlkC3hpa3hpbAt4aW04aaALeGmq+GngS3hp4fhqIAt4aiW4aigLeGplOGqp+GshS3hrLPhrYUt4a2L4a6DLeGuoOGuruGur+Guui3hr6XhsIAt4bCj4bGNLeGxj+Gxmi3hsb3hs6kt4bOs4bOuLeGzseGzteGztuG0gC3htr/huIAt4byV4byYLeG8neG8oC3hvYXhvYgt4b2N4b2QLeG9l+G9meG9m+G9neG9ny3hvb3hvoAt4b604b62LeG+vOG+vuG/gi3hv4Thv4Yt4b+M4b+QLeG/k+G/li3hv5vhv6At4b+s4b+yLeG/tOG/ti3hv7zigbHigb/igpAt4oKc4oSC4oSH4oSKLeKEk+KEleKEmC3ihJ3ihKTihKbihKjihKot4oS54oS8LeKEv+KFhS3ihYnihY7ihaAt4oaI4rCALeKwruKwsC3isZ7isaAt4rOk4rOrLeKzruKzsuKzs+K0gC3itKXitKfitK3itLAt4rWn4rWv4raALeK2luK2oC3itqbitqgt4rau4rawLeK2tuK2uC3itr7it4At4reG4reILeK3juK3kC3it5bit5gt4ree44CFLeOAh+OAoS3jgKnjgLEt44C144C4LeOAvOOBgS3jgpbjgpst44Kf44KhLeODuuODvC3jg7/jhIUt44St44SxLeOGjuOGoC3jhrrjh7At44e/45CALeS2teS4gC3pv4zqgIAt6pKM6pOQLeqTveqUgC3qmIzqmJAt6pif6piq6pir6pmALeqZruqZvy3qmp3qmqAt6puv6pyXLeqcn+qcoi3qnojqnost6p6O6p6QLeqereqesOqeseqfty3qoIHqoIMt6qCF6qCHLeqgiuqgjC3qoKLqoYAt6qGz6qKCLeqis+qjsi3qo7fqo7vqpIot6qSl6qSwLeqlhuqloC3qpbzqpoQt6qay6qeP6qegLeqnpOqnpi3qp6/qp7ot6qe+6qiALeqoqOqpgC3qqYLqqYQt6qmL6qmgLeqptuqpuuqpvi3qqq/qqrHqqrXqqrbqqrkt6qq96quA6quC6qubLeqrneqroC3qq6rqq7It6qu06qyBLeqshuqsiS3qrI7qrJEt6qyW6qygLeqspuqsqC3qrK7qrLAt6q2a6q2cLeqtn+qtpOqtpeqvgC3qr6LqsIAt7Z6j7Z6wLe2fhu2fiy3tn7vvpIAt76mt76mwLe+rme+sgC3vrIbvrJMt76yX76yd76yfLe+sqO+sqi3vrLbvrLgt76y876y+762A762B762D762E762GLe+use+vky3vtL3vtZAt77aP77aSLe+3h++3sC3vt7vvubAt77m077m2Le+7vO+8oS3vvLrvvYEt772a772mLe++vu+/gi3vv4fvv4ot77+P77+SLe+/l++/mi3vv5xcIjtcbnZhciBub25BU0NJSWlkZW50aWZpZXJDaGFycyA9IFwi4oCM4oCNwrfMgC3Nr86H0oMt0ofWkS3Wvda/14HXgteE14XXh9iQLdia2Yst2anZsNuWLduc258t26Tbp9uo26ot263bsC3budyR3LAt3Yrepi3esN+ALd+J36st37PgoJYt4KCZ4KCbLeCgo+CgpS3goKfgoKkt4KCt4KGZLeChm+CjpC3gpIPgpLot4KS84KS+LeClj+ClkS3gpZfgpaLgpaPgpaYt4KWv4KaBLeCmg+CmvOCmvi3gp4Tgp4fgp4jgp4st4KeN4KeX4Kei4Kej4KemLeCnr+CogS3gqIPgqLzgqL4t4KmC4KmH4KmI4KmLLeCpjeCpkeCppi3gqbHgqbXgqoEt4KqD4Kq84Kq+LeCrheCrhy3gq4ngq4st4KuN4Kui4Kuj4KumLeCrr+CsgS3grIPgrLzgrL4t4K2E4K2H4K2I4K2LLeCtjeCtluCtl+CtouCto+Ctpi3gra/groLgrr4t4K+C4K+GLeCviOCvii3gr43gr5fgr6Yt4K+v4LCALeCwg+Cwvi3gsYTgsYYt4LGI4LGKLeCxjeCxleCxluCxouCxo+Cxpi3gsa/gsoEt4LKD4LK84LK+LeCzhOCzhi3gs4jgs4ot4LON4LOV4LOW4LOi4LOj4LOmLeCzr+C0gS3gtIPgtL4t4LWE4LWGLeC1iOC1ii3gtY3gtZfgtaLgtaPgtaYt4LWv4LaC4LaD4LeK4LePLeC3lOC3luC3mC3gt5/gt6Yt4Lev4Ley4Lez4Lix4Li0LeC4uuC5hy3guY7guZAt4LmZ4Lqx4Lq0LeC6ueC6u+C6vOC7iC3gu43gu5At4LuZ4LyY4LyZ4LygLeC8qeC8teC8t+C8ueC8vuC8v+C9sS3gvoTgvobgvofgvo0t4L6X4L6ZLeC+vOC/huGAqy3hgL7hgYAt4YGJ4YGWLeGBmeGBni3hgaDhgaIt4YGk4YGnLeGBreGBsS3hgbThgoIt4YKN4YKPLeGCneGNnS3hjZ/hjakt4Y2x4ZySLeGclOGcsi3hnLThnZLhnZPhnbLhnbPhnrQt4Z+T4Z+d4Z+gLeGfqeGgiy3hoI3hoJAt4aCZ4aKp4aSgLeGkq+GksC3hpLvhpYYt4aWP4aawLeGngOGniOGnieGnkC3hp5rhqJct4aib4amVLeGpnuGpoC3hqbzhqb8t4aqJ4aqQLeGqmeGqsC3hqr3hrIAt4ayE4ay0LeGthOGtkC3hrZnhrast4a2z4a6ALeGuguGuoS3hrq3hrrAt4a654a+mLeGvs+GwpC3hsLfhsYAt4bGJ4bGQLeGxmeGzkC3hs5Lhs5Qt4bOo4bOt4bOyLeGztOGzuOGzueG3gC3ht7Xht7wt4be/4oC/4oGA4oGU4oOQLeKDnOKDoeKDpS3ig7Dis68t4rOx4rW/4regLeK3v+OAqi3jgK/jgpnjgprqmKAt6pip6pmv6pm0LeqZveqan+qbsOqbseqgguqghuqgi+qgoy3qoKfqooDqooHqorQt6qOE6qOQLeqjmeqjoC3qo7HqpIAt6qSJ6qSmLeqkreqlhy3qpZPqpoAt6qaD6qazLeqngOqnkC3qp5nqp6Xqp7At6qe56qipLeqotuqpg+qpjOqpjeqpkC3qqZnqqbst6qm96qqw6qqyLeqqtOqqt+qquOqqvuqqv+qrgeqrqy3qq6/qq7Xqq7bqr6Mt6q+q6q+s6q+t6q+wLeqvue+snu+4gC3vuI/vuKAt77it77iz77i077mNLe+5j++8kC3vvJnvvL9cIjtcblxudmFyIG5vbkFTQ0lJaWRlbnRpZmllclN0YXJ0ID0gbmV3IFJlZ0V4cChcIltcIiArIG5vbkFTQ0lJaWRlbnRpZmllclN0YXJ0Q2hhcnMgKyBcIl1cIik7XG52YXIgbm9uQVNDSUlpZGVudGlmaWVyID0gbmV3IFJlZ0V4cChcIltcIiArIG5vbkFTQ0lJaWRlbnRpZmllclN0YXJ0Q2hhcnMgKyBub25BU0NJSWlkZW50aWZpZXJDaGFycyArIFwiXVwiKTtcblxubm9uQVNDSUlpZGVudGlmaWVyU3RhcnRDaGFycyA9IG5vbkFTQ0lJaWRlbnRpZmllckNoYXJzID0gbnVsbDtcblxuLy8gVGhlc2UgYXJlIGEgcnVuLWxlbmd0aCBhbmQgb2Zmc2V0IGVuY29kZWQgcmVwcmVzZW50YXRpb24gb2YgdGhlXG4vLyA+MHhmZmZmIGNvZGUgcG9pbnRzIHRoYXQgYXJlIGEgdmFsaWQgcGFydCBvZiBpZGVudGlmaWVycy4gVGhlXG4vLyBvZmZzZXQgc3RhcnRzIGF0IDB4MTAwMDAsIGFuZCBlYWNoIHBhaXIgb2YgbnVtYmVycyByZXByZXNlbnRzIGFuXG4vLyBvZmZzZXQgdG8gdGhlIG5leHQgcmFuZ2UsIGFuZCB0aGVuIGEgc2l6ZSBvZiB0aGUgcmFuZ2UuIFRoZXkgd2VyZVxuLy8gZ2VuZXJhdGVkIGJ5IHRvb2xzL2dlbmVyYXRlLWlkZW50aWZpZXItcmVnZXguanNcbnZhciBhc3RyYWxJZGVudGlmaWVyU3RhcnRDb2RlcyA9IFswLCAxMSwgMiwgMjUsIDIsIDE4LCAyLCAxLCAyLCAxNCwgMywgMTMsIDM1LCAxMjIsIDcwLCA1MiwgMjY4LCAyOCwgNCwgNDgsIDQ4LCAzMSwgMTcsIDI2LCA2LCAzNywgMTEsIDI5LCAzLCAzNSwgNSwgNywgMiwgNCwgNDMsIDE1NywgOTksIDM5LCA5LCA1MSwgMTU3LCAzMTAsIDEwLCAyMSwgMTEsIDcsIDE1MywgNSwgMywgMCwgMiwgNDMsIDIsIDEsIDQsIDAsIDMsIDIyLCAxMSwgMjIsIDEwLCAzMCwgOTgsIDIxLCAxMSwgMjUsIDcxLCA1NSwgNywgMSwgNjUsIDAsIDE2LCAzLCAyLCAyLCAyLCAyNiwgNDUsIDI4LCA0LCAyOCwgMzYsIDcsIDIsIDI3LCAyOCwgNTMsIDExLCAyMSwgMTEsIDE4LCAxNCwgMTcsIDExMSwgNzIsIDk1NSwgNTIsIDc2LCA0NCwgMzMsIDI0LCAyNywgMzUsIDQyLCAzNCwgNCwgMCwgMTMsIDQ3LCAxNSwgMywgMjIsIDAsIDM4LCAxNywgMiwgMjQsIDEzMywgNDYsIDM5LCA3LCAzLCAxLCAzLCAyMSwgMiwgNiwgMiwgMSwgMiwgNCwgNCwgMCwgMzIsIDQsIDI4NywgNDcsIDIxLCAxLCAyLCAwLCAxODUsIDQ2LCA4MiwgNDcsIDIxLCAwLCA2MCwgNDIsIDUwMiwgNjMsIDMyLCAwLCA0NDksIDU2LCAxMjg4LCA5MjAsIDEwNCwgMTEwLCAyOTYyLCAxMDcwLCAxMzI2NiwgNTY4LCA4LCAzMCwgMTE0LCAyOSwgMTksIDQ3LCAxNywgMywgMzIsIDIwLCA2LCAxOCwgODgxLCA2OCwgMTIsIDAsIDY3LCAxMiwgMTY0ODEsIDEsIDMwNzEsIDEwNiwgNiwgMTIsIDQsIDgsIDgsIDksIDU5OTEsIDg0LCAyLCA3MCwgMiwgMSwgMywgMCwgMywgMSwgMywgMywgMiwgMTEsIDIsIDAsIDIsIDYsIDIsIDY0LCAyLCAzLCAzLCA3LCAyLCA2LCAyLCAyNywgMiwgMywgMiwgNCwgMiwgMCwgNCwgNiwgMiwgMzM5LCAzLCAyNCwgMiwgMjQsIDIsIDMwLCAyLCAyNCwgMiwgMzAsIDIsIDI0LCAyLCAzMCwgMiwgMjQsIDIsIDMwLCAyLCAyNCwgMiwgNywgNDE0OSwgMTk2LCAxMzQwLCAzLCAyLCAyNiwgMiwgMSwgMiwgMCwgMywgMCwgMiwgOSwgMiwgMywgMiwgMCwgMiwgMCwgNywgMCwgNSwgMCwgMiwgMCwgMiwgMCwgMiwgMiwgMiwgMSwgMiwgMCwgMywgMCwgMiwgMCwgMiwgMCwgMiwgMCwgMiwgMCwgMiwgMSwgMiwgMCwgMywgMywgMiwgNiwgMiwgMywgMiwgMywgMiwgMCwgMiwgOSwgMiwgMTYsIDYsIDIsIDIsIDQsIDIsIDE2LCA0NDIxLCA0MjcxMCwgNDIsIDQxNDgsIDEyLCAyMjEsIDE2MzU1LCA1NDFdO1xudmFyIGFzdHJhbElkZW50aWZpZXJDb2RlcyA9IFs1MDksIDAsIDIyNywgMCwgMTUwLCA0LCAyOTQsIDksIDEzNjgsIDIsIDIsIDEsIDYsIDMsIDQxLCAyLCA1LCAwLCAxNjYsIDEsIDEzMDYsIDIsIDU0LCAxNCwgMzIsIDksIDE2LCAzLCA0NiwgMTAsIDU0LCA5LCA3LCAyLCAzNywgMTMsIDIsIDksIDUyLCAwLCAxMywgMiwgNDksIDEzLCAxNiwgOSwgODMsIDExLCAxNjgsIDExLCA2LCA5LCA4LCAyLCA1NywgMCwgMiwgNiwgMywgMSwgMywgMiwgMTAsIDAsIDExLCAxLCAzLCA2LCA0LCA0LCAzMTYsIDE5LCAxMywgOSwgMjE0LCA2LCAzLCA4LCAxMTIsIDE2LCAxNiwgOSwgODIsIDEyLCA5LCA5LCA1MzUsIDksIDIwODU1LCA5LCAxMzUsIDQsIDYwLCA2LCAyNiwgOSwgMTAxNiwgNDUsIDE3LCAzLCAxOTcyMywgMSwgNTMxOSwgNCwgNCwgNSwgOSwgNywgMywgNiwgMzEsIDMsIDE0OSwgMiwgMTQxOCwgNDksIDQzMDUsIDYsIDc5MjYxOCwgMjM5XTtcblxuLy8gVGhpcyBoYXMgYSBjb21wbGV4aXR5IGxpbmVhciB0byB0aGUgdmFsdWUgb2YgdGhlIGNvZGUuIFRoZVxuLy8gYXNzdW1wdGlvbiBpcyB0aGF0IGxvb2tpbmcgdXAgYXN0cmFsIGlkZW50aWZpZXIgY2hhcmFjdGVycyBpc1xuLy8gcmFyZS5cbmZ1bmN0aW9uIGlzSW5Bc3RyYWxTZXQoY29kZSwgc2V0KSB7XG4gIHZhciBwb3MgPSA2NTUzNjtcbiAgZm9yICh2YXIgaSA9IDA7IGkgPCBzZXQubGVuZ3RoOyBpICs9IDIpIHtcbiAgICBwb3MgKz0gc2V0W2ldO1xuICAgIGlmIChwb3MgPiBjb2RlKSB7XG4gICAgICByZXR1cm4gZmFsc2U7XG4gICAgfXBvcyArPSBzZXRbaSArIDFdO1xuICAgIGlmIChwb3MgPj0gY29kZSkge1xuICAgICAgcmV0dXJuIHRydWU7XG4gICAgfVxuICB9XG59XG5mdW5jdGlvbiBpc0lkZW50aWZpZXJTdGFydChjb2RlLCBhc3RyYWwpIHtcbiAgaWYgKGNvZGUgPCA2NSkge1xuICAgIHJldHVybiBjb2RlID09PSAzNjtcbiAgfWlmIChjb2RlIDwgOTEpIHtcbiAgICByZXR1cm4gdHJ1ZTtcbiAgfWlmIChjb2RlIDwgOTcpIHtcbiAgICByZXR1cm4gY29kZSA9PT0gOTU7XG4gIH1pZiAoY29kZSA8IDEyMykge1xuICAgIHJldHVybiB0cnVlO1xuICB9aWYgKGNvZGUgPD0gNjU1MzUpIHtcbiAgICByZXR1cm4gY29kZSA+PSAxNzAgJiYgbm9uQVNDSUlpZGVudGlmaWVyU3RhcnQudGVzdChTdHJpbmcuZnJvbUNoYXJDb2RlKGNvZGUpKTtcbiAgfWlmIChhc3RyYWwgPT09IGZhbHNlKSB7XG4gICAgcmV0dXJuIGZhbHNlO1xuICB9cmV0dXJuIGlzSW5Bc3RyYWxTZXQoY29kZSwgYXN0cmFsSWRlbnRpZmllclN0YXJ0Q29kZXMpO1xufVxuXG5mdW5jdGlvbiBpc0lkZW50aWZpZXJDaGFyKGNvZGUsIGFzdHJhbCkge1xuICBpZiAoY29kZSA8IDQ4KSB7XG4gICAgcmV0dXJuIGNvZGUgPT09IDM2O1xuICB9aWYgKGNvZGUgPCA1OCkge1xuICAgIHJldHVybiB0cnVlO1xuICB9aWYgKGNvZGUgPCA2NSkge1xuICAgIHJldHVybiBmYWxzZTtcbiAgfWlmIChjb2RlIDwgOTEpIHtcbiAgICByZXR1cm4gdHJ1ZTtcbiAgfWlmIChjb2RlIDwgOTcpIHtcbiAgICByZXR1cm4gY29kZSA9PT0gOTU7XG4gIH1pZiAoY29kZSA8IDEyMykge1xuICAgIHJldHVybiB0cnVlO1xuICB9aWYgKGNvZGUgPD0gNjU1MzUpIHtcbiAgICByZXR1cm4gY29kZSA+PSAxNzAgJiYgbm9uQVNDSUlpZGVudGlmaWVyLnRlc3QoU3RyaW5nLmZyb21DaGFyQ29kZShjb2RlKSk7XG4gIH1pZiAoYXN0cmFsID09PSBmYWxzZSkge1xuICAgIHJldHVybiBmYWxzZTtcbiAgfXJldHVybiBpc0luQXN0cmFsU2V0KGNvZGUsIGFzdHJhbElkZW50aWZpZXJTdGFydENvZGVzKSB8fCBpc0luQXN0cmFsU2V0KGNvZGUsIGFzdHJhbElkZW50aWZpZXJDb2Rlcyk7XG59XG5cbn0se31dLDg6W2Z1bmN0aW9uKF9kZXJlcV8sbW9kdWxlLGV4cG9ydHMpe1xuXCJ1c2Ugc3RyaWN0XCI7XG5cbnZhciBfY2xhc3NDYWxsQ2hlY2sgPSBmdW5jdGlvbiAoaW5zdGFuY2UsIENvbnN0cnVjdG9yKSB7IGlmICghKGluc3RhbmNlIGluc3RhbmNlb2YgQ29uc3RydWN0b3IpKSB7IHRocm93IG5ldyBUeXBlRXJyb3IoXCJDYW5ub3QgY2FsbCBhIGNsYXNzIGFzIGEgZnVuY3Rpb25cIik7IH0gfTtcblxuLy8gVGhlIGBnZXRMaW5lSW5mb2AgZnVuY3Rpb24gaXMgbW9zdGx5IHVzZWZ1bCB3aGVuIHRoZVxuLy8gYGxvY2F0aW9uc2Agb3B0aW9uIGlzIG9mZiAoZm9yIHBlcmZvcm1hbmNlIHJlYXNvbnMpIGFuZCB5b3Vcbi8vIHdhbnQgdG8gZmluZCB0aGUgbGluZS9jb2x1bW4gcG9zaXRpb24gZm9yIGEgZ2l2ZW4gY2hhcmFjdGVyXG4vLyBvZmZzZXQuIGBpbnB1dGAgc2hvdWxkIGJlIHRoZSBjb2RlIHN0cmluZyB0aGF0IHRoZSBvZmZzZXQgcmVmZXJzXG4vLyBpbnRvLlxuXG5leHBvcnRzLmdldExpbmVJbmZvID0gZ2V0TGluZUluZm87XG5leHBvcnRzLl9fZXNNb2R1bGUgPSB0cnVlO1xuXG52YXIgUGFyc2VyID0gX2RlcmVxXyhcIi4vc3RhdGVcIikuUGFyc2VyO1xuXG52YXIgbGluZUJyZWFrRyA9IF9kZXJlcV8oXCIuL3doaXRlc3BhY2VcIikubGluZUJyZWFrRztcblxudmFyIGRlcHJlY2F0ZSA9IF9kZXJlcV8oXCJ1dGlsXCIpLmRlcHJlY2F0ZTtcblxuLy8gVGhlc2UgYXJlIHVzZWQgd2hlbiBgb3B0aW9ucy5sb2NhdGlvbnNgIGlzIG9uLCBmb3IgdGhlXG4vLyBgc3RhcnRMb2NgIGFuZCBgZW5kTG9jYCBwcm9wZXJ0aWVzLlxuXG52YXIgUG9zaXRpb24gPSBleHBvcnRzLlBvc2l0aW9uID0gKGZ1bmN0aW9uICgpIHtcbiAgZnVuY3Rpb24gUG9zaXRpb24obGluZSwgY29sKSB7XG4gICAgX2NsYXNzQ2FsbENoZWNrKHRoaXMsIFBvc2l0aW9uKTtcblxuICAgIHRoaXMubGluZSA9IGxpbmU7XG4gICAgdGhpcy5jb2x1bW4gPSBjb2w7XG4gIH1cblxuICBQb3NpdGlvbi5wcm90b3R5cGUub2Zmc2V0ID0gZnVuY3Rpb24gb2Zmc2V0KG4pIHtcbiAgICByZXR1cm4gbmV3IFBvc2l0aW9uKHRoaXMubGluZSwgdGhpcy5jb2x1bW4gKyBuKTtcbiAgfTtcblxuICByZXR1cm4gUG9zaXRpb247XG59KSgpO1xuXG52YXIgU291cmNlTG9jYXRpb24gPSBleHBvcnRzLlNvdXJjZUxvY2F0aW9uID0gZnVuY3Rpb24gU291cmNlTG9jYXRpb24ocCwgc3RhcnQsIGVuZCkge1xuICBfY2xhc3NDYWxsQ2hlY2sodGhpcywgU291cmNlTG9jYXRpb24pO1xuXG4gIHRoaXMuc3RhcnQgPSBzdGFydDtcbiAgdGhpcy5lbmQgPSBlbmQ7XG4gIGlmIChwLnNvdXJjZUZpbGUgIT09IG51bGwpIHRoaXMuc291cmNlID0gcC5zb3VyY2VGaWxlO1xufTtcblxuZnVuY3Rpb24gZ2V0TGluZUluZm8oaW5wdXQsIG9mZnNldCkge1xuICBmb3IgKHZhciBsaW5lID0gMSwgY3VyID0gMDs7KSB7XG4gICAgbGluZUJyZWFrRy5sYXN0SW5kZXggPSBjdXI7XG4gICAgdmFyIG1hdGNoID0gbGluZUJyZWFrRy5leGVjKGlucHV0KTtcbiAgICBpZiAobWF0Y2ggJiYgbWF0Y2guaW5kZXggPCBvZmZzZXQpIHtcbiAgICAgICsrbGluZTtcbiAgICAgIGN1ciA9IG1hdGNoLmluZGV4ICsgbWF0Y2hbMF0ubGVuZ3RoO1xuICAgIH0gZWxzZSB7XG4gICAgICByZXR1cm4gbmV3IFBvc2l0aW9uKGxpbmUsIG9mZnNldCAtIGN1cik7XG4gICAgfVxuICB9XG59XG5cbnZhciBwcCA9IFBhcnNlci5wcm90b3R5cGU7XG5cbi8vIFRoaXMgZnVuY3Rpb24gaXMgdXNlZCB0byByYWlzZSBleGNlcHRpb25zIG9uIHBhcnNlIGVycm9ycy4gSXRcbi8vIHRha2VzIGFuIG9mZnNldCBpbnRlZ2VyIChpbnRvIHRoZSBjdXJyZW50IGBpbnB1dGApIHRvIGluZGljYXRlXG4vLyB0aGUgbG9jYXRpb24gb2YgdGhlIGVycm9yLCBhdHRhY2hlcyB0aGUgcG9zaXRpb24gdG8gdGhlIGVuZFxuLy8gb2YgdGhlIGVycm9yIG1lc3NhZ2UsIGFuZCB0aGVuIHJhaXNlcyBhIGBTeW50YXhFcnJvcmAgd2l0aCB0aGF0XG4vLyBtZXNzYWdlLlxuXG5wcC5yYWlzZSA9IGZ1bmN0aW9uIChwb3MsIG1lc3NhZ2UpIHtcbiAgdmFyIGxvYyA9IGdldExpbmVJbmZvKHRoaXMuaW5wdXQsIHBvcyk7XG4gIG1lc3NhZ2UgKz0gXCIgKFwiICsgbG9jLmxpbmUgKyBcIjpcIiArIGxvYy5jb2x1bW4gKyBcIilcIjtcbiAgdmFyIGVyciA9IG5ldyBTeW50YXhFcnJvcihtZXNzYWdlKTtcbiAgZXJyLnBvcyA9IHBvcztlcnIubG9jID0gbG9jO2Vyci5yYWlzZWRBdCA9IHRoaXMucG9zO1xuICB0aHJvdyBlcnI7XG59O1xuXG5wcC5jdXJQb3NpdGlvbiA9IGZ1bmN0aW9uICgpIHtcbiAgcmV0dXJuIG5ldyBQb3NpdGlvbih0aGlzLmN1ckxpbmUsIHRoaXMucG9zIC0gdGhpcy5saW5lU3RhcnQpO1xufTtcblxucHAubWFya1Bvc2l0aW9uID0gZnVuY3Rpb24gKCkge1xuICByZXR1cm4gdGhpcy5vcHRpb25zLmxvY2F0aW9ucyA/IFt0aGlzLnN0YXJ0LCB0aGlzLnN0YXJ0TG9jXSA6IHRoaXMuc3RhcnQ7XG59O1xuXG59LHtcIi4vc3RhdGVcIjoxMyxcIi4vd2hpdGVzcGFjZVwiOjE5LFwidXRpbFwiOjV9XSw5OltmdW5jdGlvbihfZGVyZXFfLG1vZHVsZSxleHBvcnRzKXtcblwidXNlIHN0cmljdFwiO1xuXG52YXIgdHQgPSBfZGVyZXFfKFwiLi90b2tlbnR5cGVcIikudHlwZXM7XG5cbnZhciBQYXJzZXIgPSBfZGVyZXFfKFwiLi9zdGF0ZVwiKS5QYXJzZXI7XG5cbnZhciByZXNlcnZlZFdvcmRzID0gX2RlcmVxXyhcIi4vaWRlbnRpZmllclwiKS5yZXNlcnZlZFdvcmRzO1xuXG52YXIgaGFzID0gX2RlcmVxXyhcIi4vdXRpbFwiKS5oYXM7XG5cbnZhciBwcCA9IFBhcnNlci5wcm90b3R5cGU7XG5cbi8vIENvbnZlcnQgZXhpc3RpbmcgZXhwcmVzc2lvbiBhdG9tIHRvIGFzc2lnbmFibGUgcGF0dGVyblxuLy8gaWYgcG9zc2libGUuXG5cbnBwLnRvQXNzaWduYWJsZSA9IGZ1bmN0aW9uIChub2RlLCBpc0JpbmRpbmcpIHtcbiAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2ICYmIG5vZGUpIHtcbiAgICBzd2l0Y2ggKG5vZGUudHlwZSkge1xuICAgICAgY2FzZSBcIklkZW50aWZpZXJcIjpcbiAgICAgIGNhc2UgXCJPYmplY3RQYXR0ZXJuXCI6XG4gICAgICBjYXNlIFwiQXJyYXlQYXR0ZXJuXCI6XG4gICAgICBjYXNlIFwiQXNzaWdubWVudFBhdHRlcm5cIjpcbiAgICAgICAgYnJlYWs7XG5cbiAgICAgIGNhc2UgXCJPYmplY3RFeHByZXNzaW9uXCI6XG4gICAgICAgIG5vZGUudHlwZSA9IFwiT2JqZWN0UGF0dGVyblwiO1xuICAgICAgICBmb3IgKHZhciBpID0gMDsgaSA8IG5vZGUucHJvcGVydGllcy5sZW5ndGg7IGkrKykge1xuICAgICAgICAgIHZhciBwcm9wID0gbm9kZS5wcm9wZXJ0aWVzW2ldO1xuICAgICAgICAgIGlmIChwcm9wLmtpbmQgIT09IFwiaW5pdFwiKSB0aGlzLnJhaXNlKHByb3Aua2V5LnN0YXJ0LCBcIk9iamVjdCBwYXR0ZXJuIGNhbid0IGNvbnRhaW4gZ2V0dGVyIG9yIHNldHRlclwiKTtcbiAgICAgICAgICB0aGlzLnRvQXNzaWduYWJsZShwcm9wLnZhbHVlLCBpc0JpbmRpbmcpO1xuICAgICAgICB9XG4gICAgICAgIGJyZWFrO1xuXG4gICAgICBjYXNlIFwiQXJyYXlFeHByZXNzaW9uXCI6XG4gICAgICAgIG5vZGUudHlwZSA9IFwiQXJyYXlQYXR0ZXJuXCI7XG4gICAgICAgIHRoaXMudG9Bc3NpZ25hYmxlTGlzdChub2RlLmVsZW1lbnRzLCBpc0JpbmRpbmcpO1xuICAgICAgICBicmVhaztcblxuICAgICAgY2FzZSBcIkFzc2lnbm1lbnRFeHByZXNzaW9uXCI6XG4gICAgICAgIGlmIChub2RlLm9wZXJhdG9yID09PSBcIj1cIikge1xuICAgICAgICAgIG5vZGUudHlwZSA9IFwiQXNzaWdubWVudFBhdHRlcm5cIjtcbiAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICB0aGlzLnJhaXNlKG5vZGUubGVmdC5lbmQsIFwiT25seSAnPScgb3BlcmF0b3IgY2FuIGJlIHVzZWQgZm9yIHNwZWNpZnlpbmcgZGVmYXVsdCB2YWx1ZS5cIik7XG4gICAgICAgIH1cbiAgICAgICAgYnJlYWs7XG5cbiAgICAgIGNhc2UgXCJQYXJlbnRoZXNpemVkRXhwcmVzc2lvblwiOlxuICAgICAgICBub2RlLmV4cHJlc3Npb24gPSB0aGlzLnRvQXNzaWduYWJsZShub2RlLmV4cHJlc3Npb24sIGlzQmluZGluZyk7XG4gICAgICAgIGJyZWFrO1xuXG4gICAgICBjYXNlIFwiTWVtYmVyRXhwcmVzc2lvblwiOlxuICAgICAgICBpZiAoIWlzQmluZGluZykgYnJlYWs7XG5cbiAgICAgIGRlZmF1bHQ6XG4gICAgICAgIHRoaXMucmFpc2Uobm9kZS5zdGFydCwgXCJBc3NpZ25pbmcgdG8gcnZhbHVlXCIpO1xuICAgIH1cbiAgfVxuICByZXR1cm4gbm9kZTtcbn07XG5cbi8vIENvbnZlcnQgbGlzdCBvZiBleHByZXNzaW9uIGF0b21zIHRvIGJpbmRpbmcgbGlzdC5cblxucHAudG9Bc3NpZ25hYmxlTGlzdCA9IGZ1bmN0aW9uIChleHByTGlzdCwgaXNCaW5kaW5nKSB7XG4gIHZhciBlbmQgPSBleHByTGlzdC5sZW5ndGg7XG4gIGlmIChlbmQpIHtcbiAgICB2YXIgbGFzdCA9IGV4cHJMaXN0W2VuZCAtIDFdO1xuICAgIGlmIChsYXN0ICYmIGxhc3QudHlwZSA9PSBcIlJlc3RFbGVtZW50XCIpIHtcbiAgICAgIC0tZW5kO1xuICAgIH0gZWxzZSBpZiAobGFzdCAmJiBsYXN0LnR5cGUgPT0gXCJTcHJlYWRFbGVtZW50XCIpIHtcbiAgICAgIGxhc3QudHlwZSA9IFwiUmVzdEVsZW1lbnRcIjtcbiAgICAgIHZhciBhcmcgPSBsYXN0LmFyZ3VtZW50O1xuICAgICAgdGhpcy50b0Fzc2lnbmFibGUoYXJnLCBpc0JpbmRpbmcpO1xuICAgICAgaWYgKGFyZy50eXBlICE9PSBcIklkZW50aWZpZXJcIiAmJiBhcmcudHlwZSAhPT0gXCJNZW1iZXJFeHByZXNzaW9uXCIgJiYgYXJnLnR5cGUgIT09IFwiQXJyYXlQYXR0ZXJuXCIpIHRoaXMudW5leHBlY3RlZChhcmcuc3RhcnQpO1xuICAgICAgLS1lbmQ7XG4gICAgfVxuICB9XG4gIGZvciAodmFyIGkgPSAwOyBpIDwgZW5kOyBpKyspIHtcbiAgICB2YXIgZWx0ID0gZXhwckxpc3RbaV07XG4gICAgaWYgKGVsdCkgdGhpcy50b0Fzc2lnbmFibGUoZWx0LCBpc0JpbmRpbmcpO1xuICB9XG4gIHJldHVybiBleHByTGlzdDtcbn07XG5cbi8vIFBhcnNlcyBzcHJlYWQgZWxlbWVudC5cblxucHAucGFyc2VTcHJlYWQgPSBmdW5jdGlvbiAocmVmU2hvcnRoYW5kRGVmYXVsdFBvcykge1xuICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gIHRoaXMubmV4dCgpO1xuICBub2RlLmFyZ3VtZW50ID0gdGhpcy5wYXJzZU1heWJlQXNzaWduKHJlZlNob3J0aGFuZERlZmF1bHRQb3MpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiU3ByZWFkRWxlbWVudFwiKTtcbn07XG5cbnBwLnBhcnNlUmVzdCA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICB0aGlzLm5leHQoKTtcbiAgbm9kZS5hcmd1bWVudCA9IHRoaXMudHlwZSA9PT0gdHQubmFtZSB8fCB0aGlzLnR5cGUgPT09IHR0LmJyYWNrZXRMID8gdGhpcy5wYXJzZUJpbmRpbmdBdG9tKCkgOiB0aGlzLnVuZXhwZWN0ZWQoKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIlJlc3RFbGVtZW50XCIpO1xufTtcblxuLy8gUGFyc2VzIGx2YWx1ZSAoYXNzaWduYWJsZSkgYXRvbS5cblxucHAucGFyc2VCaW5kaW5nQXRvbSA9IGZ1bmN0aW9uICgpIHtcbiAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA8IDYpIHJldHVybiB0aGlzLnBhcnNlSWRlbnQoKTtcbiAgc3dpdGNoICh0aGlzLnR5cGUpIHtcbiAgICBjYXNlIHR0Lm5hbWU6XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZUlkZW50KCk7XG5cbiAgICBjYXNlIHR0LmJyYWNrZXRMOlxuICAgICAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICBub2RlLmVsZW1lbnRzID0gdGhpcy5wYXJzZUJpbmRpbmdMaXN0KHR0LmJyYWNrZXRSLCB0cnVlLCB0cnVlKTtcbiAgICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJBcnJheVBhdHRlcm5cIik7XG5cbiAgICBjYXNlIHR0LmJyYWNlTDpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlT2JqKHRydWUpO1xuXG4gICAgZGVmYXVsdDpcbiAgICAgIHRoaXMudW5leHBlY3RlZCgpO1xuICB9XG59O1xuXG5wcC5wYXJzZUJpbmRpbmdMaXN0ID0gZnVuY3Rpb24gKGNsb3NlLCBhbGxvd0VtcHR5LCBhbGxvd1RyYWlsaW5nQ29tbWEpIHtcbiAgdmFyIGVsdHMgPSBbXSxcbiAgICAgIGZpcnN0ID0gdHJ1ZTtcbiAgd2hpbGUgKCF0aGlzLmVhdChjbG9zZSkpIHtcbiAgICBpZiAoZmlyc3QpIGZpcnN0ID0gZmFsc2U7ZWxzZSB0aGlzLmV4cGVjdCh0dC5jb21tYSk7XG4gICAgaWYgKGFsbG93RW1wdHkgJiYgdGhpcy50eXBlID09PSB0dC5jb21tYSkge1xuICAgICAgZWx0cy5wdXNoKG51bGwpO1xuICAgIH0gZWxzZSBpZiAoYWxsb3dUcmFpbGluZ0NvbW1hICYmIHRoaXMuYWZ0ZXJUcmFpbGluZ0NvbW1hKGNsb3NlKSkge1xuICAgICAgYnJlYWs7XG4gICAgfSBlbHNlIGlmICh0aGlzLnR5cGUgPT09IHR0LmVsbGlwc2lzKSB7XG4gICAgICB2YXIgcmVzdCA9IHRoaXMucGFyc2VSZXN0KCk7XG4gICAgICB0aGlzLnBhcnNlQmluZGluZ0xpc3RJdGVtKHJlc3QpO1xuICAgICAgZWx0cy5wdXNoKHJlc3QpO1xuICAgICAgdGhpcy5leHBlY3QoY2xvc2UpO1xuICAgICAgYnJlYWs7XG4gICAgfSBlbHNlIHtcbiAgICAgIHZhciBlbGVtID0gdGhpcy5wYXJzZU1heWJlRGVmYXVsdCh0aGlzLnN0YXJ0LCB0aGlzLnN0YXJ0TG9jKTtcbiAgICAgIHRoaXMucGFyc2VCaW5kaW5nTGlzdEl0ZW0oZWxlbSk7XG4gICAgICBlbHRzLnB1c2goZWxlbSk7XG4gICAgfVxuICB9XG4gIHJldHVybiBlbHRzO1xufTtcblxucHAucGFyc2VCaW5kaW5nTGlzdEl0ZW0gPSBmdW5jdGlvbiAocGFyYW0pIHtcbiAgcmV0dXJuIHBhcmFtO1xufTtcblxuLy8gUGFyc2VzIGFzc2lnbm1lbnQgcGF0dGVybiBhcm91bmQgZ2l2ZW4gYXRvbSBpZiBwb3NzaWJsZS5cblxucHAucGFyc2VNYXliZURlZmF1bHQgPSBmdW5jdGlvbiAoc3RhcnRQb3MsIHN0YXJ0TG9jLCBsZWZ0KSB7XG4gIGlmIChBcnJheS5pc0FycmF5KHN0YXJ0UG9zKSkge1xuICAgIGlmICh0aGlzLm9wdGlvbnMubG9jYXRpb25zICYmIG5vQ2FsbHMgPT09IHVuZGVmaW5lZCkge1xuICAgICAgLy8gc2hpZnQgYXJndW1lbnRzIHRvIGxlZnQgYnkgb25lXG4gICAgICBsZWZ0ID0gc3RhcnRMb2M7XG4gICAgICAvLyBmbGF0dGVuIHN0YXJ0UG9zXG4gICAgICBzdGFydExvYyA9IHN0YXJ0UG9zWzFdO1xuICAgICAgc3RhcnRQb3MgPSBzdGFydFBvc1swXTtcbiAgICB9XG4gIH1cbiAgbGVmdCA9IGxlZnQgfHwgdGhpcy5wYXJzZUJpbmRpbmdBdG9tKCk7XG4gIGlmICghdGhpcy5lYXQodHQuZXEpKSByZXR1cm4gbGVmdDtcbiAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0UG9zLCBzdGFydExvYyk7XG4gIG5vZGUub3BlcmF0b3IgPSBcIj1cIjtcbiAgbm9kZS5sZWZ0ID0gbGVmdDtcbiAgbm9kZS5yaWdodCA9IHRoaXMucGFyc2VNYXliZUFzc2lnbigpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiQXNzaWdubWVudFBhdHRlcm5cIik7XG59O1xuXG4vLyBWZXJpZnkgdGhhdCBhIG5vZGUgaXMgYW4gbHZhbCDigJQgc29tZXRoaW5nIHRoYXQgY2FuIGJlIGFzc2lnbmVkXG4vLyB0by5cblxucHAuY2hlY2tMVmFsID0gZnVuY3Rpb24gKGV4cHIsIGlzQmluZGluZywgY2hlY2tDbGFzaGVzKSB7XG4gIHN3aXRjaCAoZXhwci50eXBlKSB7XG4gICAgY2FzZSBcIklkZW50aWZpZXJcIjpcbiAgICAgIGlmICh0aGlzLnN0cmljdCAmJiAocmVzZXJ2ZWRXb3Jkcy5zdHJpY3RCaW5kKGV4cHIubmFtZSkgfHwgcmVzZXJ2ZWRXb3Jkcy5zdHJpY3QoZXhwci5uYW1lKSkpIHRoaXMucmFpc2UoZXhwci5zdGFydCwgKGlzQmluZGluZyA/IFwiQmluZGluZyBcIiA6IFwiQXNzaWduaW5nIHRvIFwiKSArIGV4cHIubmFtZSArIFwiIGluIHN0cmljdCBtb2RlXCIpO1xuICAgICAgaWYgKGNoZWNrQ2xhc2hlcykge1xuICAgICAgICBpZiAoaGFzKGNoZWNrQ2xhc2hlcywgZXhwci5uYW1lKSkgdGhpcy5yYWlzZShleHByLnN0YXJ0LCBcIkFyZ3VtZW50IG5hbWUgY2xhc2ggaW4gc3RyaWN0IG1vZGVcIik7XG4gICAgICAgIGNoZWNrQ2xhc2hlc1tleHByLm5hbWVdID0gdHJ1ZTtcbiAgICAgIH1cbiAgICAgIGJyZWFrO1xuXG4gICAgY2FzZSBcIk1lbWJlckV4cHJlc3Npb25cIjpcbiAgICAgIGlmIChpc0JpbmRpbmcpIHRoaXMucmFpc2UoZXhwci5zdGFydCwgKGlzQmluZGluZyA/IFwiQmluZGluZ1wiIDogXCJBc3NpZ25pbmcgdG9cIikgKyBcIiBtZW1iZXIgZXhwcmVzc2lvblwiKTtcbiAgICAgIGJyZWFrO1xuXG4gICAgY2FzZSBcIk9iamVjdFBhdHRlcm5cIjpcbiAgICAgIGZvciAodmFyIGkgPSAwOyBpIDwgZXhwci5wcm9wZXJ0aWVzLmxlbmd0aDsgaSsrKSB7XG4gICAgICAgIHRoaXMuY2hlY2tMVmFsKGV4cHIucHJvcGVydGllc1tpXS52YWx1ZSwgaXNCaW5kaW5nLCBjaGVja0NsYXNoZXMpO1xuICAgICAgfWJyZWFrO1xuXG4gICAgY2FzZSBcIkFycmF5UGF0dGVyblwiOlxuICAgICAgZm9yICh2YXIgaSA9IDA7IGkgPCBleHByLmVsZW1lbnRzLmxlbmd0aDsgaSsrKSB7XG4gICAgICAgIHZhciBlbGVtID0gZXhwci5lbGVtZW50c1tpXTtcbiAgICAgICAgaWYgKGVsZW0pIHRoaXMuY2hlY2tMVmFsKGVsZW0sIGlzQmluZGluZywgY2hlY2tDbGFzaGVzKTtcbiAgICAgIH1cbiAgICAgIGJyZWFrO1xuXG4gICAgY2FzZSBcIkFzc2lnbm1lbnRQYXR0ZXJuXCI6XG4gICAgICB0aGlzLmNoZWNrTFZhbChleHByLmxlZnQsIGlzQmluZGluZywgY2hlY2tDbGFzaGVzKTtcbiAgICAgIGJyZWFrO1xuXG4gICAgY2FzZSBcIlJlc3RFbGVtZW50XCI6XG4gICAgICB0aGlzLmNoZWNrTFZhbChleHByLmFyZ3VtZW50LCBpc0JpbmRpbmcsIGNoZWNrQ2xhc2hlcyk7XG4gICAgICBicmVhaztcblxuICAgIGNhc2UgXCJQYXJlbnRoZXNpemVkRXhwcmVzc2lvblwiOlxuICAgICAgdGhpcy5jaGVja0xWYWwoZXhwci5leHByZXNzaW9uLCBpc0JpbmRpbmcsIGNoZWNrQ2xhc2hlcyk7XG4gICAgICBicmVhaztcblxuICAgIGRlZmF1bHQ6XG4gICAgICB0aGlzLnJhaXNlKGV4cHIuc3RhcnQsIChpc0JpbmRpbmcgPyBcIkJpbmRpbmdcIiA6IFwiQXNzaWduaW5nIHRvXCIpICsgXCIgcnZhbHVlXCIpO1xuICB9XG59O1xuXG59LHtcIi4vaWRlbnRpZmllclwiOjcsXCIuL3N0YXRlXCI6MTMsXCIuL3Rva2VudHlwZVwiOjE3LFwiLi91dGlsXCI6MTh9XSwxMDpbZnVuY3Rpb24oX2RlcmVxXyxtb2R1bGUsZXhwb3J0cyl7XG5cInVzZSBzdHJpY3RcIjtcblxudmFyIF9jbGFzc0NhbGxDaGVjayA9IGZ1bmN0aW9uIChpbnN0YW5jZSwgQ29uc3RydWN0b3IpIHsgaWYgKCEoaW5zdGFuY2UgaW5zdGFuY2VvZiBDb25zdHJ1Y3RvcikpIHsgdGhyb3cgbmV3IFR5cGVFcnJvcihcIkNhbm5vdCBjYWxsIGEgY2xhc3MgYXMgYSBmdW5jdGlvblwiKTsgfSB9O1xuXG5leHBvcnRzLl9fZXNNb2R1bGUgPSB0cnVlO1xuXG52YXIgUGFyc2VyID0gX2RlcmVxXyhcIi4vc3RhdGVcIikuUGFyc2VyO1xuXG52YXIgU291cmNlTG9jYXRpb24gPSBfZGVyZXFfKFwiLi9sb2NhdGlvblwiKS5Tb3VyY2VMb2NhdGlvbjtcblxuLy8gU3RhcnQgYW4gQVNUIG5vZGUsIGF0dGFjaGluZyBhIHN0YXJ0IG9mZnNldC5cblxudmFyIHBwID0gUGFyc2VyLnByb3RvdHlwZTtcblxudmFyIE5vZGUgPSBleHBvcnRzLk5vZGUgPSBmdW5jdGlvbiBOb2RlKCkge1xuICBfY2xhc3NDYWxsQ2hlY2sodGhpcywgTm9kZSk7XG59O1xuXG5wcC5zdGFydE5vZGUgPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBub2RlID0gbmV3IE5vZGUoKTtcbiAgbm9kZS5zdGFydCA9IHRoaXMuc3RhcnQ7XG4gIGlmICh0aGlzLm9wdGlvbnMubG9jYXRpb25zKSBub2RlLmxvYyA9IG5ldyBTb3VyY2VMb2NhdGlvbih0aGlzLCB0aGlzLnN0YXJ0TG9jKTtcbiAgaWYgKHRoaXMub3B0aW9ucy5kaXJlY3RTb3VyY2VGaWxlKSBub2RlLnNvdXJjZUZpbGUgPSB0aGlzLm9wdGlvbnMuZGlyZWN0U291cmNlRmlsZTtcbiAgaWYgKHRoaXMub3B0aW9ucy5yYW5nZXMpIG5vZGUucmFuZ2UgPSBbdGhpcy5zdGFydCwgMF07XG4gIHJldHVybiBub2RlO1xufTtcblxucHAuc3RhcnROb2RlQXQgPSBmdW5jdGlvbiAocG9zLCBsb2MpIHtcbiAgdmFyIG5vZGUgPSBuZXcgTm9kZSgpO1xuICBpZiAoQXJyYXkuaXNBcnJheShwb3MpKSB7XG4gICAgaWYgKHRoaXMub3B0aW9ucy5sb2NhdGlvbnMgJiYgbG9jID09PSB1bmRlZmluZWQpIHtcbiAgICAgIC8vIGZsYXR0ZW4gcG9zXG4gICAgICBsb2MgPSBwb3NbMV07XG4gICAgICBwb3MgPSBwb3NbMF07XG4gICAgfVxuICB9XG4gIG5vZGUuc3RhcnQgPSBwb3M7XG4gIGlmICh0aGlzLm9wdGlvbnMubG9jYXRpb25zKSBub2RlLmxvYyA9IG5ldyBTb3VyY2VMb2NhdGlvbih0aGlzLCBsb2MpO1xuICBpZiAodGhpcy5vcHRpb25zLmRpcmVjdFNvdXJjZUZpbGUpIG5vZGUuc291cmNlRmlsZSA9IHRoaXMub3B0aW9ucy5kaXJlY3RTb3VyY2VGaWxlO1xuICBpZiAodGhpcy5vcHRpb25zLnJhbmdlcykgbm9kZS5yYW5nZSA9IFtwb3MsIDBdO1xuICByZXR1cm4gbm9kZTtcbn07XG5cbi8vIEZpbmlzaCBhbiBBU1Qgbm9kZSwgYWRkaW5nIGB0eXBlYCBhbmQgYGVuZGAgcHJvcGVydGllcy5cblxucHAuZmluaXNoTm9kZSA9IGZ1bmN0aW9uIChub2RlLCB0eXBlKSB7XG4gIG5vZGUudHlwZSA9IHR5cGU7XG4gIG5vZGUuZW5kID0gdGhpcy5sYXN0VG9rRW5kO1xuICBpZiAodGhpcy5vcHRpb25zLmxvY2F0aW9ucykgbm9kZS5sb2MuZW5kID0gdGhpcy5sYXN0VG9rRW5kTG9jO1xuICBpZiAodGhpcy5vcHRpb25zLnJhbmdlcykgbm9kZS5yYW5nZVsxXSA9IHRoaXMubGFzdFRva0VuZDtcbiAgcmV0dXJuIG5vZGU7XG59O1xuXG4vLyBGaW5pc2ggbm9kZSBhdCBnaXZlbiBwb3NpdGlvblxuXG5wcC5maW5pc2hOb2RlQXQgPSBmdW5jdGlvbiAobm9kZSwgdHlwZSwgcG9zLCBsb2MpIHtcbiAgbm9kZS50eXBlID0gdHlwZTtcbiAgaWYgKEFycmF5LmlzQXJyYXkocG9zKSkge1xuICAgIGlmICh0aGlzLm9wdGlvbnMubG9jYXRpb25zICYmIGxvYyA9PT0gdW5kZWZpbmVkKSB7XG4gICAgICAvLyBmbGF0dGVuIHBvc1xuICAgICAgbG9jID0gcG9zWzFdO1xuICAgICAgcG9zID0gcG9zWzBdO1xuICAgIH1cbiAgfVxuICBub2RlLmVuZCA9IHBvcztcbiAgaWYgKHRoaXMub3B0aW9ucy5sb2NhdGlvbnMpIG5vZGUubG9jLmVuZCA9IGxvYztcbiAgaWYgKHRoaXMub3B0aW9ucy5yYW5nZXMpIG5vZGUucmFuZ2VbMV0gPSBwb3M7XG4gIHJldHVybiBub2RlO1xufTtcblxufSx7XCIuL2xvY2F0aW9uXCI6OCxcIi4vc3RhdGVcIjoxM31dLDExOltmdW5jdGlvbihfZGVyZXFfLG1vZHVsZSxleHBvcnRzKXtcblxuXG4vLyBJbnRlcnByZXQgYW5kIGRlZmF1bHQgYW4gb3B0aW9ucyBvYmplY3RcblxuXCJ1c2Ugc3RyaWN0XCI7XG5cbmV4cG9ydHMuZ2V0T3B0aW9ucyA9IGdldE9wdGlvbnM7XG5leHBvcnRzLl9fZXNNb2R1bGUgPSB0cnVlO1xuXG52YXIgX3V0aWwgPSBfZGVyZXFfKFwiLi91dGlsXCIpO1xuXG52YXIgaGFzID0gX3V0aWwuaGFzO1xudmFyIGlzQXJyYXkgPSBfdXRpbC5pc0FycmF5O1xuXG52YXIgU291cmNlTG9jYXRpb24gPSBfZGVyZXFfKFwiLi9sb2NhdGlvblwiKS5Tb3VyY2VMb2NhdGlvbjtcblxuLy8gQSBzZWNvbmQgb3B0aW9uYWwgYXJndW1lbnQgY2FuIGJlIGdpdmVuIHRvIGZ1cnRoZXIgY29uZmlndXJlXG4vLyB0aGUgcGFyc2VyIHByb2Nlc3MuIFRoZXNlIG9wdGlvbnMgYXJlIHJlY29nbml6ZWQ6XG5cbnZhciBkZWZhdWx0T3B0aW9ucyA9IHtcbiAgLy8gYGVjbWFWZXJzaW9uYCBpbmRpY2F0ZXMgdGhlIEVDTUFTY3JpcHQgdmVyc2lvbiB0byBwYXJzZS4gTXVzdFxuICAvLyBiZSBlaXRoZXIgMywgb3IgNSwgb3IgNi4gVGhpcyBpbmZsdWVuY2VzIHN1cHBvcnQgZm9yIHN0cmljdFxuICAvLyBtb2RlLCB0aGUgc2V0IG9mIHJlc2VydmVkIHdvcmRzLCBzdXBwb3J0IGZvciBnZXR0ZXJzIGFuZFxuICAvLyBzZXR0ZXJzIGFuZCBvdGhlciBmZWF0dXJlcy5cbiAgZWNtYVZlcnNpb246IDUsXG4gIC8vIFNvdXJjZSB0eXBlIChcInNjcmlwdFwiIG9yIFwibW9kdWxlXCIpIGZvciBkaWZmZXJlbnQgc2VtYW50aWNzXG4gIHNvdXJjZVR5cGU6IFwic2NyaXB0XCIsXG4gIC8vIGBvbkluc2VydGVkU2VtaWNvbG9uYCBjYW4gYmUgYSBjYWxsYmFjayB0aGF0IHdpbGwgYmUgY2FsbGVkXG4gIC8vIHdoZW4gYSBzZW1pY29sb24gaXMgYXV0b21hdGljYWxseSBpbnNlcnRlZC4gSXQgd2lsbCBiZSBwYXNzZWRcbiAgLy8gdGggcG9zaXRpb24gb2YgdGhlIGNvbW1hIGFzIGFuIG9mZnNldCwgYW5kIGlmIGBsb2NhdGlvbnNgIGlzXG4gIC8vIGVuYWJsZWQsIGl0IGlzIGdpdmVuIHRoZSBsb2NhdGlvbiBhcyBhIGB7bGluZSwgY29sdW1ufWAgb2JqZWN0XG4gIC8vIGFzIHNlY29uZCBhcmd1bWVudC5cbiAgb25JbnNlcnRlZFNlbWljb2xvbjogbnVsbCxcbiAgLy8gYG9uVHJhaWxpbmdDb21tYWAgaXMgc2ltaWxhciB0byBgb25JbnNlcnRlZFNlbWljb2xvbmAsIGJ1dCBmb3JcbiAgLy8gdHJhaWxpbmcgY29tbWFzLlxuICBvblRyYWlsaW5nQ29tbWE6IG51bGwsXG4gIC8vIEJ5IGRlZmF1bHQsIHJlc2VydmVkIHdvcmRzIGFyZSBub3QgZW5mb3JjZWQuIERpc2FibGVcbiAgLy8gYGFsbG93UmVzZXJ2ZWRgIHRvIGVuZm9yY2UgdGhlbS4gV2hlbiB0aGlzIG9wdGlvbiBoYXMgdGhlXG4gIC8vIHZhbHVlIFwibmV2ZXJcIiwgcmVzZXJ2ZWQgd29yZHMgYW5kIGtleXdvcmRzIGNhbiBhbHNvIG5vdCBiZVxuICAvLyB1c2VkIGFzIHByb3BlcnR5IG5hbWVzLlxuICBhbGxvd1Jlc2VydmVkOiB0cnVlLFxuICAvLyBXaGVuIGVuYWJsZWQsIGEgcmV0dXJuIGF0IHRoZSB0b3AgbGV2ZWwgaXMgbm90IGNvbnNpZGVyZWQgYW5cbiAgLy8gZXJyb3IuXG4gIGFsbG93UmV0dXJuT3V0c2lkZUZ1bmN0aW9uOiBmYWxzZSxcbiAgLy8gV2hlbiBlbmFibGVkLCBpbXBvcnQvZXhwb3J0IHN0YXRlbWVudHMgYXJlIG5vdCBjb25zdHJhaW5lZCB0b1xuICAvLyBhcHBlYXJpbmcgYXQgdGhlIHRvcCBvZiB0aGUgcHJvZ3JhbS5cbiAgYWxsb3dJbXBvcnRFeHBvcnRFdmVyeXdoZXJlOiBmYWxzZSxcbiAgLy8gV2hlbiBlbmFibGVkLCBoYXNoYmFuZyBkaXJlY3RpdmUgaW4gdGhlIGJlZ2lubmluZyBvZiBmaWxlXG4gIC8vIGlzIGFsbG93ZWQgYW5kIHRyZWF0ZWQgYXMgYSBsaW5lIGNvbW1lbnQuXG4gIGFsbG93SGFzaEJhbmc6IGZhbHNlLFxuICAvLyBXaGVuIGBsb2NhdGlvbnNgIGlzIG9uLCBgbG9jYCBwcm9wZXJ0aWVzIGhvbGRpbmcgb2JqZWN0cyB3aXRoXG4gIC8vIGBzdGFydGAgYW5kIGBlbmRgIHByb3BlcnRpZXMgaW4gYHtsaW5lLCBjb2x1bW59YCBmb3JtICh3aXRoXG4gIC8vIGxpbmUgYmVpbmcgMS1iYXNlZCBhbmQgY29sdW1uIDAtYmFzZWQpIHdpbGwgYmUgYXR0YWNoZWQgdG8gdGhlXG4gIC8vIG5vZGVzLlxuICBsb2NhdGlvbnM6IGZhbHNlLFxuICAvLyBBIGZ1bmN0aW9uIGNhbiBiZSBwYXNzZWQgYXMgYG9uVG9rZW5gIG9wdGlvbiwgd2hpY2ggd2lsbFxuICAvLyBjYXVzZSBBY29ybiB0byBjYWxsIHRoYXQgZnVuY3Rpb24gd2l0aCBvYmplY3QgaW4gdGhlIHNhbWVcbiAgLy8gZm9ybWF0IGFzIHRva2VuaXplKCkgcmV0dXJucy4gTm90ZSB0aGF0IHlvdSBhcmUgbm90XG4gIC8vIGFsbG93ZWQgdG8gY2FsbCB0aGUgcGFyc2VyIGZyb20gdGhlIGNhbGxiYWNr4oCUdGhhdCB3aWxsXG4gIC8vIGNvcnJ1cHQgaXRzIGludGVybmFsIHN0YXRlLlxuICBvblRva2VuOiBudWxsLFxuICAvLyBBIGZ1bmN0aW9uIGNhbiBiZSBwYXNzZWQgYXMgYG9uQ29tbWVudGAgb3B0aW9uLCB3aGljaCB3aWxsXG4gIC8vIGNhdXNlIEFjb3JuIHRvIGNhbGwgdGhhdCBmdW5jdGlvbiB3aXRoIGAoYmxvY2ssIHRleHQsIHN0YXJ0LFxuICAvLyBlbmQpYCBwYXJhbWV0ZXJzIHdoZW5ldmVyIGEgY29tbWVudCBpcyBza2lwcGVkLiBgYmxvY2tgIGlzIGFcbiAgLy8gYm9vbGVhbiBpbmRpY2F0aW5nIHdoZXRoZXIgdGhpcyBpcyBhIGJsb2NrIChgLyogKi9gKSBjb21tZW50LFxuICAvLyBgdGV4dGAgaXMgdGhlIGNvbnRlbnQgb2YgdGhlIGNvbW1lbnQsIGFuZCBgc3RhcnRgIGFuZCBgZW5kYCBhcmVcbiAgLy8gY2hhcmFjdGVyIG9mZnNldHMgdGhhdCBkZW5vdGUgdGhlIHN0YXJ0IGFuZCBlbmQgb2YgdGhlIGNvbW1lbnQuXG4gIC8vIFdoZW4gdGhlIGBsb2NhdGlvbnNgIG9wdGlvbiBpcyBvbiwgdHdvIG1vcmUgcGFyYW1ldGVycyBhcmVcbiAgLy8gcGFzc2VkLCB0aGUgZnVsbCBge2xpbmUsIGNvbHVtbn1gIGxvY2F0aW9ucyBvZiB0aGUgc3RhcnQgYW5kXG4gIC8vIGVuZCBvZiB0aGUgY29tbWVudHMuIE5vdGUgdGhhdCB5b3UgYXJlIG5vdCBhbGxvd2VkIHRvIGNhbGwgdGhlXG4gIC8vIHBhcnNlciBmcm9tIHRoZSBjYWxsYmFja+KAlHRoYXQgd2lsbCBjb3JydXB0IGl0cyBpbnRlcm5hbCBzdGF0ZS5cbiAgb25Db21tZW50OiBudWxsLFxuICAvLyBOb2RlcyBoYXZlIHRoZWlyIHN0YXJ0IGFuZCBlbmQgY2hhcmFjdGVycyBvZmZzZXRzIHJlY29yZGVkIGluXG4gIC8vIGBzdGFydGAgYW5kIGBlbmRgIHByb3BlcnRpZXMgKGRpcmVjdGx5IG9uIHRoZSBub2RlLCByYXRoZXIgdGhhblxuICAvLyB0aGUgYGxvY2Agb2JqZWN0LCB3aGljaCBob2xkcyBsaW5lL2NvbHVtbiBkYXRhLiBUbyBhbHNvIGFkZCBhXG4gIC8vIFtzZW1pLXN0YW5kYXJkaXplZF1bcmFuZ2VdIGByYW5nZWAgcHJvcGVydHkgaG9sZGluZyBhIGBbc3RhcnQsXG4gIC8vIGVuZF1gIGFycmF5IHdpdGggdGhlIHNhbWUgbnVtYmVycywgc2V0IHRoZSBgcmFuZ2VzYCBvcHRpb24gdG9cbiAgLy8gYHRydWVgLlxuICAvL1xuICAvLyBbcmFuZ2VdOiBodHRwczovL2J1Z3ppbGxhLm1vemlsbGEub3JnL3Nob3dfYnVnLmNnaT9pZD03NDU2NzhcbiAgcmFuZ2VzOiBmYWxzZSxcbiAgLy8gSXQgaXMgcG9zc2libGUgdG8gcGFyc2UgbXVsdGlwbGUgZmlsZXMgaW50byBhIHNpbmdsZSBBU1QgYnlcbiAgLy8gcGFzc2luZyB0aGUgdHJlZSBwcm9kdWNlZCBieSBwYXJzaW5nIHRoZSBmaXJzdCBmaWxlIGFzXG4gIC8vIGBwcm9ncmFtYCBvcHRpb24gaW4gc3Vic2VxdWVudCBwYXJzZXMuIFRoaXMgd2lsbCBhZGQgdGhlXG4gIC8vIHRvcGxldmVsIGZvcm1zIG9mIHRoZSBwYXJzZWQgZmlsZSB0byB0aGUgYFByb2dyYW1gICh0b3ApIG5vZGVcbiAgLy8gb2YgYW4gZXhpc3RpbmcgcGFyc2UgdHJlZS5cbiAgcHJvZ3JhbTogbnVsbCxcbiAgLy8gV2hlbiBgbG9jYXRpb25zYCBpcyBvbiwgeW91IGNhbiBwYXNzIHRoaXMgdG8gcmVjb3JkIHRoZSBzb3VyY2VcbiAgLy8gZmlsZSBpbiBldmVyeSBub2RlJ3MgYGxvY2Agb2JqZWN0LlxuICBzb3VyY2VGaWxlOiBudWxsLFxuICAvLyBUaGlzIHZhbHVlLCBpZiBnaXZlbiwgaXMgc3RvcmVkIGluIGV2ZXJ5IG5vZGUsIHdoZXRoZXJcbiAgLy8gYGxvY2F0aW9uc2AgaXMgb24gb3Igb2ZmLlxuICBkaXJlY3RTb3VyY2VGaWxlOiBudWxsLFxuICAvLyBXaGVuIGVuYWJsZWQsIHBhcmVudGhlc2l6ZWQgZXhwcmVzc2lvbnMgYXJlIHJlcHJlc2VudGVkIGJ5XG4gIC8vIChub24tc3RhbmRhcmQpIFBhcmVudGhlc2l6ZWRFeHByZXNzaW9uIG5vZGVzXG4gIHByZXNlcnZlUGFyZW5zOiBmYWxzZSxcbiAgcGx1Z2luczoge31cbn07ZXhwb3J0cy5kZWZhdWx0T3B0aW9ucyA9IGRlZmF1bHRPcHRpb25zO1xuXG5mdW5jdGlvbiBnZXRPcHRpb25zKG9wdHMpIHtcbiAgdmFyIG9wdGlvbnMgPSB7fTtcbiAgZm9yICh2YXIgb3B0IGluIGRlZmF1bHRPcHRpb25zKSB7XG4gICAgb3B0aW9uc1tvcHRdID0gb3B0cyAmJiBoYXMob3B0cywgb3B0KSA/IG9wdHNbb3B0XSA6IGRlZmF1bHRPcHRpb25zW29wdF07XG4gIH1pZiAoaXNBcnJheShvcHRpb25zLm9uVG9rZW4pKSB7XG4gICAgKGZ1bmN0aW9uICgpIHtcbiAgICAgIHZhciB0b2tlbnMgPSBvcHRpb25zLm9uVG9rZW47XG4gICAgICBvcHRpb25zLm9uVG9rZW4gPSBmdW5jdGlvbiAodG9rZW4pIHtcbiAgICAgICAgcmV0dXJuIHRva2Vucy5wdXNoKHRva2VuKTtcbiAgICAgIH07XG4gICAgfSkoKTtcbiAgfVxuICBpZiAoaXNBcnJheShvcHRpb25zLm9uQ29tbWVudCkpIG9wdGlvbnMub25Db21tZW50ID0gcHVzaENvbW1lbnQob3B0aW9ucywgb3B0aW9ucy5vbkNvbW1lbnQpO1xuXG4gIHJldHVybiBvcHRpb25zO1xufVxuXG5mdW5jdGlvbiBwdXNoQ29tbWVudChvcHRpb25zLCBhcnJheSkge1xuICByZXR1cm4gZnVuY3Rpb24gKGJsb2NrLCB0ZXh0LCBzdGFydCwgZW5kLCBzdGFydExvYywgZW5kTG9jKSB7XG4gICAgdmFyIGNvbW1lbnQgPSB7XG4gICAgICB0eXBlOiBibG9jayA/IFwiQmxvY2tcIiA6IFwiTGluZVwiLFxuICAgICAgdmFsdWU6IHRleHQsXG4gICAgICBzdGFydDogc3RhcnQsXG4gICAgICBlbmQ6IGVuZFxuICAgIH07XG4gICAgaWYgKG9wdGlvbnMubG9jYXRpb25zKSBjb21tZW50LmxvYyA9IG5ldyBTb3VyY2VMb2NhdGlvbih0aGlzLCBzdGFydExvYywgZW5kTG9jKTtcbiAgICBpZiAob3B0aW9ucy5yYW5nZXMpIGNvbW1lbnQucmFuZ2UgPSBbc3RhcnQsIGVuZF07XG4gICAgYXJyYXkucHVzaChjb21tZW50KTtcbiAgfTtcbn1cblxufSx7XCIuL2xvY2F0aW9uXCI6OCxcIi4vdXRpbFwiOjE4fV0sMTI6W2Z1bmN0aW9uKF9kZXJlcV8sbW9kdWxlLGV4cG9ydHMpe1xuXCJ1c2Ugc3RyaWN0XCI7XG5cbnZhciB0dCA9IF9kZXJlcV8oXCIuL3Rva2VudHlwZVwiKS50eXBlcztcblxudmFyIFBhcnNlciA9IF9kZXJlcV8oXCIuL3N0YXRlXCIpLlBhcnNlcjtcblxudmFyIGxpbmVCcmVhayA9IF9kZXJlcV8oXCIuL3doaXRlc3BhY2VcIikubGluZUJyZWFrO1xuXG52YXIgcHAgPSBQYXJzZXIucHJvdG90eXBlO1xuXG4vLyAjIyBQYXJzZXIgdXRpbGl0aWVzXG5cbi8vIFRlc3Qgd2hldGhlciBhIHN0YXRlbWVudCBub2RlIGlzIHRoZSBzdHJpbmcgbGl0ZXJhbCBgXCJ1c2Ugc3RyaWN0XCJgLlxuXG5wcC5pc1VzZVN0cmljdCA9IGZ1bmN0aW9uIChzdG10KSB7XG4gIHJldHVybiB0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNSAmJiBzdG10LnR5cGUgPT09IFwiRXhwcmVzc2lvblN0YXRlbWVudFwiICYmIHN0bXQuZXhwcmVzc2lvbi50eXBlID09PSBcIkxpdGVyYWxcIiAmJiBzdG10LmV4cHJlc3Npb24udmFsdWUgPT09IFwidXNlIHN0cmljdFwiO1xufTtcblxuLy8gUHJlZGljYXRlIHRoYXQgdGVzdHMgd2hldGhlciB0aGUgbmV4dCB0b2tlbiBpcyBvZiB0aGUgZ2l2ZW5cbi8vIHR5cGUsIGFuZCBpZiB5ZXMsIGNvbnN1bWVzIGl0IGFzIGEgc2lkZSBlZmZlY3QuXG5cbnBwLmVhdCA9IGZ1bmN0aW9uICh0eXBlKSB7XG4gIGlmICh0aGlzLnR5cGUgPT09IHR5cGUpIHtcbiAgICB0aGlzLm5leHQoKTtcbiAgICByZXR1cm4gdHJ1ZTtcbiAgfSBlbHNlIHtcbiAgICByZXR1cm4gZmFsc2U7XG4gIH1cbn07XG5cbi8vIFRlc3RzIHdoZXRoZXIgcGFyc2VkIHRva2VuIGlzIGEgY29udGV4dHVhbCBrZXl3b3JkLlxuXG5wcC5pc0NvbnRleHR1YWwgPSBmdW5jdGlvbiAobmFtZSkge1xuICByZXR1cm4gdGhpcy50eXBlID09PSB0dC5uYW1lICYmIHRoaXMudmFsdWUgPT09IG5hbWU7XG59O1xuXG4vLyBDb25zdW1lcyBjb250ZXh0dWFsIGtleXdvcmQgaWYgcG9zc2libGUuXG5cbnBwLmVhdENvbnRleHR1YWwgPSBmdW5jdGlvbiAobmFtZSkge1xuICByZXR1cm4gdGhpcy52YWx1ZSA9PT0gbmFtZSAmJiB0aGlzLmVhdCh0dC5uYW1lKTtcbn07XG5cbi8vIEFzc2VydHMgdGhhdCBmb2xsb3dpbmcgdG9rZW4gaXMgZ2l2ZW4gY29udGV4dHVhbCBrZXl3b3JkLlxuXG5wcC5leHBlY3RDb250ZXh0dWFsID0gZnVuY3Rpb24gKG5hbWUpIHtcbiAgaWYgKCF0aGlzLmVhdENvbnRleHR1YWwobmFtZSkpIHRoaXMudW5leHBlY3RlZCgpO1xufTtcblxuLy8gVGVzdCB3aGV0aGVyIGEgc2VtaWNvbG9uIGNhbiBiZSBpbnNlcnRlZCBhdCB0aGUgY3VycmVudCBwb3NpdGlvbi5cblxucHAuY2FuSW5zZXJ0U2VtaWNvbG9uID0gZnVuY3Rpb24gKCkge1xuICByZXR1cm4gdGhpcy50eXBlID09PSB0dC5lb2YgfHwgdGhpcy50eXBlID09PSB0dC5icmFjZVIgfHwgbGluZUJyZWFrLnRlc3QodGhpcy5pbnB1dC5zbGljZSh0aGlzLmxhc3RUb2tFbmQsIHRoaXMuc3RhcnQpKTtcbn07XG5cbnBwLmluc2VydFNlbWljb2xvbiA9IGZ1bmN0aW9uICgpIHtcbiAgaWYgKHRoaXMuY2FuSW5zZXJ0U2VtaWNvbG9uKCkpIHtcbiAgICBpZiAodGhpcy5vcHRpb25zLm9uSW5zZXJ0ZWRTZW1pY29sb24pIHRoaXMub3B0aW9ucy5vbkluc2VydGVkU2VtaWNvbG9uKHRoaXMubGFzdFRva0VuZCwgdGhpcy5sYXN0VG9rRW5kTG9jKTtcbiAgICByZXR1cm4gdHJ1ZTtcbiAgfVxufTtcblxuLy8gQ29uc3VtZSBhIHNlbWljb2xvbiwgb3IsIGZhaWxpbmcgdGhhdCwgc2VlIGlmIHdlIGFyZSBhbGxvd2VkIHRvXG4vLyBwcmV0ZW5kIHRoYXQgdGhlcmUgaXMgYSBzZW1pY29sb24gYXQgdGhpcyBwb3NpdGlvbi5cblxucHAuc2VtaWNvbG9uID0gZnVuY3Rpb24gKCkge1xuICBpZiAoIXRoaXMuZWF0KHR0LnNlbWkpICYmICF0aGlzLmluc2VydFNlbWljb2xvbigpKSB0aGlzLnVuZXhwZWN0ZWQoKTtcbn07XG5cbnBwLmFmdGVyVHJhaWxpbmdDb21tYSA9IGZ1bmN0aW9uICh0b2tUeXBlKSB7XG4gIGlmICh0aGlzLnR5cGUgPT0gdG9rVHlwZSkge1xuICAgIGlmICh0aGlzLm9wdGlvbnMub25UcmFpbGluZ0NvbW1hKSB0aGlzLm9wdGlvbnMub25UcmFpbGluZ0NvbW1hKHRoaXMubGFzdFRva1N0YXJ0LCB0aGlzLmxhc3RUb2tTdGFydExvYyk7XG4gICAgdGhpcy5uZXh0KCk7XG4gICAgcmV0dXJuIHRydWU7XG4gIH1cbn07XG5cbi8vIEV4cGVjdCBhIHRva2VuIG9mIGEgZ2l2ZW4gdHlwZS4gSWYgZm91bmQsIGNvbnN1bWUgaXQsIG90aGVyd2lzZSxcbi8vIHJhaXNlIGFuIHVuZXhwZWN0ZWQgdG9rZW4gZXJyb3IuXG5cbnBwLmV4cGVjdCA9IGZ1bmN0aW9uICh0eXBlKSB7XG4gIHRoaXMuZWF0KHR5cGUpIHx8IHRoaXMudW5leHBlY3RlZCgpO1xufTtcblxuLy8gUmFpc2UgYW4gdW5leHBlY3RlZCB0b2tlbiBlcnJvci5cblxucHAudW5leHBlY3RlZCA9IGZ1bmN0aW9uIChwb3MpIHtcbiAgdGhpcy5yYWlzZShwb3MgIT0gbnVsbCA/IHBvcyA6IHRoaXMuc3RhcnQsIFwiVW5leHBlY3RlZCB0b2tlblwiKTtcbn07XG5cbn0se1wiLi9zdGF0ZVwiOjEzLFwiLi90b2tlbnR5cGVcIjoxNyxcIi4vd2hpdGVzcGFjZVwiOjE5fV0sMTM6W2Z1bmN0aW9uKF9kZXJlcV8sbW9kdWxlLGV4cG9ydHMpe1xuXCJ1c2Ugc3RyaWN0XCI7XG5cbmV4cG9ydHMuUGFyc2VyID0gUGFyc2VyO1xuZXhwb3J0cy5fX2VzTW9kdWxlID0gdHJ1ZTtcblxudmFyIF9pZGVudGlmaWVyID0gX2RlcmVxXyhcIi4vaWRlbnRpZmllclwiKTtcblxudmFyIHJlc2VydmVkV29yZHMgPSBfaWRlbnRpZmllci5yZXNlcnZlZFdvcmRzO1xudmFyIGtleXdvcmRzID0gX2lkZW50aWZpZXIua2V5d29yZHM7XG5cbnZhciB0dCA9IF9kZXJlcV8oXCIuL3Rva2VudHlwZVwiKS50eXBlcztcblxudmFyIGxpbmVCcmVhayA9IF9kZXJlcV8oXCIuL3doaXRlc3BhY2VcIikubGluZUJyZWFrO1xuXG5mdW5jdGlvbiBQYXJzZXIob3B0aW9ucywgaW5wdXQsIHN0YXJ0UG9zKSB7XG4gIHRoaXMub3B0aW9ucyA9IG9wdGlvbnM7XG4gIHRoaXMuc291cmNlRmlsZSA9IHRoaXMub3B0aW9ucy5zb3VyY2VGaWxlIHx8IG51bGw7XG4gIHRoaXMuaXNLZXl3b3JkID0ga2V5d29yZHNbdGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYgPyA2IDogNV07XG4gIHRoaXMuaXNSZXNlcnZlZFdvcmQgPSByZXNlcnZlZFdvcmRzW3RoaXMub3B0aW9ucy5lY21hVmVyc2lvbl07XG4gIHRoaXMuaW5wdXQgPSBpbnB1dDtcblxuICAvLyBMb2FkIHBsdWdpbnNcbiAgdGhpcy5sb2FkUGx1Z2lucyh0aGlzLm9wdGlvbnMucGx1Z2lucyk7XG5cbiAgLy8gU2V0IHVwIHRva2VuIHN0YXRlXG5cbiAgLy8gVGhlIGN1cnJlbnQgcG9zaXRpb24gb2YgdGhlIHRva2VuaXplciBpbiB0aGUgaW5wdXQuXG4gIGlmIChzdGFydFBvcykge1xuICAgIHRoaXMucG9zID0gc3RhcnRQb3M7XG4gICAgdGhpcy5saW5lU3RhcnQgPSBNYXRoLm1heCgwLCB0aGlzLmlucHV0Lmxhc3RJbmRleE9mKFwiXFxuXCIsIHN0YXJ0UG9zKSk7XG4gICAgdGhpcy5jdXJMaW5lID0gdGhpcy5pbnB1dC5zbGljZSgwLCB0aGlzLmxpbmVTdGFydCkuc3BsaXQobGluZUJyZWFrKS5sZW5ndGg7XG4gIH0gZWxzZSB7XG4gICAgdGhpcy5wb3MgPSB0aGlzLmxpbmVTdGFydCA9IDA7XG4gICAgdGhpcy5jdXJMaW5lID0gMTtcbiAgfVxuXG4gIC8vIFByb3BlcnRpZXMgb2YgdGhlIGN1cnJlbnQgdG9rZW46XG4gIC8vIEl0cyB0eXBlXG4gIHRoaXMudHlwZSA9IHR0LmVvZjtcbiAgLy8gRm9yIHRva2VucyB0aGF0IGluY2x1ZGUgbW9yZSBpbmZvcm1hdGlvbiB0aGFuIHRoZWlyIHR5cGUsIHRoZSB2YWx1ZVxuICB0aGlzLnZhbHVlID0gbnVsbDtcbiAgLy8gSXRzIHN0YXJ0IGFuZCBlbmQgb2Zmc2V0XG4gIHRoaXMuc3RhcnQgPSB0aGlzLmVuZCA9IHRoaXMucG9zO1xuICAvLyBBbmQsIGlmIGxvY2F0aW9ucyBhcmUgdXNlZCwgdGhlIHtsaW5lLCBjb2x1bW59IG9iamVjdFxuICAvLyBjb3JyZXNwb25kaW5nIHRvIHRob3NlIG9mZnNldHNcbiAgdGhpcy5zdGFydExvYyA9IHRoaXMuZW5kTG9jID0gbnVsbDtcblxuICAvLyBQb3NpdGlvbiBpbmZvcm1hdGlvbiBmb3IgdGhlIHByZXZpb3VzIHRva2VuXG4gIHRoaXMubGFzdFRva0VuZExvYyA9IHRoaXMubGFzdFRva1N0YXJ0TG9jID0gbnVsbDtcbiAgdGhpcy5sYXN0VG9rU3RhcnQgPSB0aGlzLmxhc3RUb2tFbmQgPSB0aGlzLnBvcztcblxuICAvLyBUaGUgY29udGV4dCBzdGFjayBpcyB1c2VkIHRvIHN1cGVyZmljaWFsbHkgdHJhY2sgc3ludGFjdGljXG4gIC8vIGNvbnRleHQgdG8gcHJlZGljdCB3aGV0aGVyIGEgcmVndWxhciBleHByZXNzaW9uIGlzIGFsbG93ZWQgaW4gYVxuICAvLyBnaXZlbiBwb3NpdGlvbi5cbiAgdGhpcy5jb250ZXh0ID0gdGhpcy5pbml0aWFsQ29udGV4dCgpO1xuICB0aGlzLmV4cHJBbGxvd2VkID0gdHJ1ZTtcblxuICAvLyBGaWd1cmUgb3V0IGlmIGl0J3MgYSBtb2R1bGUgY29kZS5cbiAgdGhpcy5zdHJpY3QgPSB0aGlzLmluTW9kdWxlID0gdGhpcy5vcHRpb25zLnNvdXJjZVR5cGUgPT09IFwibW9kdWxlXCI7XG5cbiAgLy8gVXNlZCB0byBzaWduaWZ5IHRoZSBzdGFydCBvZiBhIHBvdGVudGlhbCBhcnJvdyBmdW5jdGlvblxuICB0aGlzLnBvdGVudGlhbEFycm93QXQgPSAtMTtcblxuICAvLyBGbGFncyB0byB0cmFjayB3aGV0aGVyIHdlIGFyZSBpbiBhIGZ1bmN0aW9uLCBhIGdlbmVyYXRvci5cbiAgdGhpcy5pbkZ1bmN0aW9uID0gdGhpcy5pbkdlbmVyYXRvciA9IGZhbHNlO1xuICAvLyBMYWJlbHMgaW4gc2NvcGUuXG4gIHRoaXMubGFiZWxzID0gW107XG5cbiAgLy8gSWYgZW5hYmxlZCwgc2tpcCBsZWFkaW5nIGhhc2hiYW5nIGxpbmUuXG4gIGlmICh0aGlzLnBvcyA9PT0gMCAmJiB0aGlzLm9wdGlvbnMuYWxsb3dIYXNoQmFuZyAmJiB0aGlzLmlucHV0LnNsaWNlKDAsIDIpID09PSBcIiMhXCIpIHRoaXMuc2tpcExpbmVDb21tZW50KDIpO1xufVxuXG5QYXJzZXIucHJvdG90eXBlLmV4dGVuZCA9IGZ1bmN0aW9uIChuYW1lLCBmKSB7XG4gIHRoaXNbbmFtZV0gPSBmKHRoaXNbbmFtZV0pO1xufTtcblxuLy8gUmVnaXN0ZXJlZCBwbHVnaW5zXG5cbnZhciBwbHVnaW5zID0ge307XG5cbmV4cG9ydHMucGx1Z2lucyA9IHBsdWdpbnM7XG5QYXJzZXIucHJvdG90eXBlLmxvYWRQbHVnaW5zID0gZnVuY3Rpb24gKHBsdWdpbnMpIHtcbiAgZm9yICh2YXIgX25hbWUgaW4gcGx1Z2lucykge1xuICAgIHZhciBwbHVnaW4gPSBleHBvcnRzLnBsdWdpbnNbX25hbWVdO1xuICAgIGlmICghcGx1Z2luKSB0aHJvdyBuZXcgRXJyb3IoXCJQbHVnaW4gJ1wiICsgX25hbWUgKyBcIicgbm90IGZvdW5kXCIpO1xuICAgIHBsdWdpbih0aGlzLCBwbHVnaW5zW19uYW1lXSk7XG4gIH1cbn07XG5cbn0se1wiLi9pZGVudGlmaWVyXCI6NyxcIi4vdG9rZW50eXBlXCI6MTcsXCIuL3doaXRlc3BhY2VcIjoxOX1dLDE0OltmdW5jdGlvbihfZGVyZXFfLG1vZHVsZSxleHBvcnRzKXtcblwidXNlIHN0cmljdFwiO1xuXG52YXIgdHQgPSBfZGVyZXFfKFwiLi90b2tlbnR5cGVcIikudHlwZXM7XG5cbnZhciBQYXJzZXIgPSBfZGVyZXFfKFwiLi9zdGF0ZVwiKS5QYXJzZXI7XG5cbnZhciBsaW5lQnJlYWsgPSBfZGVyZXFfKFwiLi93aGl0ZXNwYWNlXCIpLmxpbmVCcmVhaztcblxudmFyIHBwID0gUGFyc2VyLnByb3RvdHlwZTtcblxuLy8gIyMjIFN0YXRlbWVudCBwYXJzaW5nXG5cbi8vIFBhcnNlIGEgcHJvZ3JhbS4gSW5pdGlhbGl6ZXMgdGhlIHBhcnNlciwgcmVhZHMgYW55IG51bWJlciBvZlxuLy8gc3RhdGVtZW50cywgYW5kIHdyYXBzIHRoZW0gaW4gYSBQcm9ncmFtIG5vZGUuICBPcHRpb25hbGx5IHRha2VzIGFcbi8vIGBwcm9ncmFtYCBhcmd1bWVudC4gIElmIHByZXNlbnQsIHRoZSBzdGF0ZW1lbnRzIHdpbGwgYmUgYXBwZW5kZWRcbi8vIHRvIGl0cyBib2R5IGluc3RlYWQgb2YgY3JlYXRpbmcgYSBuZXcgbm9kZS5cblxucHAucGFyc2VUb3BMZXZlbCA9IGZ1bmN0aW9uIChub2RlKSB7XG4gIHZhciBmaXJzdCA9IHRydWU7XG4gIGlmICghbm9kZS5ib2R5KSBub2RlLmJvZHkgPSBbXTtcbiAgd2hpbGUgKHRoaXMudHlwZSAhPT0gdHQuZW9mKSB7XG4gICAgdmFyIHN0bXQgPSB0aGlzLnBhcnNlU3RhdGVtZW50KHRydWUsIHRydWUpO1xuICAgIG5vZGUuYm9keS5wdXNoKHN0bXQpO1xuICAgIGlmIChmaXJzdCAmJiB0aGlzLmlzVXNlU3RyaWN0KHN0bXQpKSB0aGlzLnNldFN0cmljdCh0cnVlKTtcbiAgICBmaXJzdCA9IGZhbHNlO1xuICB9XG4gIHRoaXMubmV4dCgpO1xuICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYpIHtcbiAgICBub2RlLnNvdXJjZVR5cGUgPSB0aGlzLm9wdGlvbnMuc291cmNlVHlwZTtcbiAgfVxuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiUHJvZ3JhbVwiKTtcbn07XG5cbnZhciBsb29wTGFiZWwgPSB7IGtpbmQ6IFwibG9vcFwiIH0sXG4gICAgc3dpdGNoTGFiZWwgPSB7IGtpbmQ6IFwic3dpdGNoXCIgfTtcblxuLy8gUGFyc2UgYSBzaW5nbGUgc3RhdGVtZW50LlxuLy9cbi8vIElmIGV4cGVjdGluZyBhIHN0YXRlbWVudCBhbmQgZmluZGluZyBhIHNsYXNoIG9wZXJhdG9yLCBwYXJzZSBhXG4vLyByZWd1bGFyIGV4cHJlc3Npb24gbGl0ZXJhbC4gVGhpcyBpcyB0byBoYW5kbGUgY2FzZXMgbGlrZVxuLy8gYGlmIChmb28pIC9ibGFoLy5leGVjKGZvbylgLCB3aGVyZSBsb29raW5nIGF0IHRoZSBwcmV2aW91cyB0b2tlblxuLy8gZG9lcyBub3QgaGVscC5cblxucHAucGFyc2VTdGF0ZW1lbnQgPSBmdW5jdGlvbiAoZGVjbGFyYXRpb24sIHRvcExldmVsKSB7XG4gIHZhciBzdGFydHR5cGUgPSB0aGlzLnR5cGUsXG4gICAgICBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcblxuICAvLyBNb3N0IHR5cGVzIG9mIHN0YXRlbWVudHMgYXJlIHJlY29nbml6ZWQgYnkgdGhlIGtleXdvcmQgdGhleVxuICAvLyBzdGFydCB3aXRoLiBNYW55IGFyZSB0cml2aWFsIHRvIHBhcnNlLCBzb21lIHJlcXVpcmUgYSBiaXQgb2ZcbiAgLy8gY29tcGxleGl0eS5cblxuICBzd2l0Y2ggKHN0YXJ0dHlwZSkge1xuICAgIGNhc2UgdHQuX2JyZWFrOmNhc2UgdHQuX2NvbnRpbnVlOlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VCcmVha0NvbnRpbnVlU3RhdGVtZW50KG5vZGUsIHN0YXJ0dHlwZS5rZXl3b3JkKTtcbiAgICBjYXNlIHR0Ll9kZWJ1Z2dlcjpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlRGVidWdnZXJTdGF0ZW1lbnQobm9kZSk7XG4gICAgY2FzZSB0dC5fZG86XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZURvU3RhdGVtZW50KG5vZGUpO1xuICAgIGNhc2UgdHQuX2ZvcjpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlRm9yU3RhdGVtZW50KG5vZGUpO1xuICAgIGNhc2UgdHQuX2Z1bmN0aW9uOlxuICAgICAgaWYgKCFkZWNsYXJhdGlvbiAmJiB0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNikgdGhpcy51bmV4cGVjdGVkKCk7XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZUZ1bmN0aW9uU3RhdGVtZW50KG5vZGUpO1xuICAgIGNhc2UgdHQuX2NsYXNzOlxuICAgICAgaWYgKCFkZWNsYXJhdGlvbikgdGhpcy51bmV4cGVjdGVkKCk7XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZUNsYXNzKG5vZGUsIHRydWUpO1xuICAgIGNhc2UgdHQuX2lmOlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VJZlN0YXRlbWVudChub2RlKTtcbiAgICBjYXNlIHR0Ll9yZXR1cm46XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZVJldHVyblN0YXRlbWVudChub2RlKTtcbiAgICBjYXNlIHR0Ll9zd2l0Y2g6XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZVN3aXRjaFN0YXRlbWVudChub2RlKTtcbiAgICBjYXNlIHR0Ll90aHJvdzpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlVGhyb3dTdGF0ZW1lbnQobm9kZSk7XG4gICAgY2FzZSB0dC5fdHJ5OlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VUcnlTdGF0ZW1lbnQobm9kZSk7XG4gICAgY2FzZSB0dC5fbGV0OmNhc2UgdHQuX2NvbnN0OlxuICAgICAgaWYgKCFkZWNsYXJhdGlvbikgdGhpcy51bmV4cGVjdGVkKCk7IC8vIE5PVEU6IGZhbGxzIHRocm91Z2ggdG8gX3ZhclxuICAgIGNhc2UgdHQuX3ZhcjpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlVmFyU3RhdGVtZW50KG5vZGUsIHN0YXJ0dHlwZSk7XG4gICAgY2FzZSB0dC5fd2hpbGU6XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZVdoaWxlU3RhdGVtZW50KG5vZGUpO1xuICAgIGNhc2UgdHQuX3dpdGg6XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZVdpdGhTdGF0ZW1lbnQobm9kZSk7XG4gICAgY2FzZSB0dC5icmFjZUw6XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZUJsb2NrKCk7XG4gICAgY2FzZSB0dC5zZW1pOlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VFbXB0eVN0YXRlbWVudChub2RlKTtcbiAgICBjYXNlIHR0Ll9leHBvcnQ6XG4gICAgY2FzZSB0dC5faW1wb3J0OlxuICAgICAgaWYgKCF0aGlzLm9wdGlvbnMuYWxsb3dJbXBvcnRFeHBvcnRFdmVyeXdoZXJlKSB7XG4gICAgICAgIGlmICghdG9wTGV2ZWwpIHRoaXMucmFpc2UodGhpcy5zdGFydCwgXCInaW1wb3J0JyBhbmQgJ2V4cG9ydCcgbWF5IG9ubHkgYXBwZWFyIGF0IHRoZSB0b3AgbGV2ZWxcIik7XG4gICAgICAgIGlmICghdGhpcy5pbk1vZHVsZSkgdGhpcy5yYWlzZSh0aGlzLnN0YXJ0LCBcIidpbXBvcnQnIGFuZCAnZXhwb3J0JyBtYXkgYXBwZWFyIG9ubHkgd2l0aCAnc291cmNlVHlwZTogbW9kdWxlJ1wiKTtcbiAgICAgIH1cbiAgICAgIHJldHVybiBzdGFydHR5cGUgPT09IHR0Ll9pbXBvcnQgPyB0aGlzLnBhcnNlSW1wb3J0KG5vZGUpIDogdGhpcy5wYXJzZUV4cG9ydChub2RlKTtcblxuICAgIC8vIElmIHRoZSBzdGF0ZW1lbnQgZG9lcyBub3Qgc3RhcnQgd2l0aCBhIHN0YXRlbWVudCBrZXl3b3JkIG9yIGFcbiAgICAvLyBicmFjZSwgaXQncyBhbiBFeHByZXNzaW9uU3RhdGVtZW50IG9yIExhYmVsZWRTdGF0ZW1lbnQuIFdlXG4gICAgLy8gc2ltcGx5IHN0YXJ0IHBhcnNpbmcgYW4gZXhwcmVzc2lvbiwgYW5kIGFmdGVyd2FyZHMsIGlmIHRoZVxuICAgIC8vIG5leHQgdG9rZW4gaXMgYSBjb2xvbiBhbmQgdGhlIGV4cHJlc3Npb24gd2FzIGEgc2ltcGxlXG4gICAgLy8gSWRlbnRpZmllciBub2RlLCB3ZSBzd2l0Y2ggdG8gaW50ZXJwcmV0aW5nIGl0IGFzIGEgbGFiZWwuXG4gICAgZGVmYXVsdDpcbiAgICAgIHZhciBtYXliZU5hbWUgPSB0aGlzLnZhbHVlLFxuICAgICAgICAgIGV4cHIgPSB0aGlzLnBhcnNlRXhwcmVzc2lvbigpO1xuICAgICAgaWYgKHN0YXJ0dHlwZSA9PT0gdHQubmFtZSAmJiBleHByLnR5cGUgPT09IFwiSWRlbnRpZmllclwiICYmIHRoaXMuZWF0KHR0LmNvbG9uKSkgcmV0dXJuIHRoaXMucGFyc2VMYWJlbGVkU3RhdGVtZW50KG5vZGUsIG1heWJlTmFtZSwgZXhwcik7ZWxzZSByZXR1cm4gdGhpcy5wYXJzZUV4cHJlc3Npb25TdGF0ZW1lbnQobm9kZSwgZXhwcik7XG4gIH1cbn07XG5cbnBwLnBhcnNlQnJlYWtDb250aW51ZVN0YXRlbWVudCA9IGZ1bmN0aW9uIChub2RlLCBrZXl3b3JkKSB7XG4gIHZhciBpc0JyZWFrID0ga2V5d29yZCA9PSBcImJyZWFrXCI7XG4gIHRoaXMubmV4dCgpO1xuICBpZiAodGhpcy5lYXQodHQuc2VtaSkgfHwgdGhpcy5pbnNlcnRTZW1pY29sb24oKSkgbm9kZS5sYWJlbCA9IG51bGw7ZWxzZSBpZiAodGhpcy50eXBlICE9PSB0dC5uYW1lKSB0aGlzLnVuZXhwZWN0ZWQoKTtlbHNlIHtcbiAgICBub2RlLmxhYmVsID0gdGhpcy5wYXJzZUlkZW50KCk7XG4gICAgdGhpcy5zZW1pY29sb24oKTtcbiAgfVxuXG4gIC8vIFZlcmlmeSB0aGF0IHRoZXJlIGlzIGFuIGFjdHVhbCBkZXN0aW5hdGlvbiB0byBicmVhayBvclxuICAvLyBjb250aW51ZSB0by5cbiAgZm9yICh2YXIgaSA9IDA7IGkgPCB0aGlzLmxhYmVscy5sZW5ndGg7ICsraSkge1xuICAgIHZhciBsYWIgPSB0aGlzLmxhYmVsc1tpXTtcbiAgICBpZiAobm9kZS5sYWJlbCA9PSBudWxsIHx8IGxhYi5uYW1lID09PSBub2RlLmxhYmVsLm5hbWUpIHtcbiAgICAgIGlmIChsYWIua2luZCAhPSBudWxsICYmIChpc0JyZWFrIHx8IGxhYi5raW5kID09PSBcImxvb3BcIikpIGJyZWFrO1xuICAgICAgaWYgKG5vZGUubGFiZWwgJiYgaXNCcmVhaykgYnJlYWs7XG4gICAgfVxuICB9XG4gIGlmIChpID09PSB0aGlzLmxhYmVscy5sZW5ndGgpIHRoaXMucmFpc2Uobm9kZS5zdGFydCwgXCJVbnN5bnRhY3RpYyBcIiArIGtleXdvcmQpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIGlzQnJlYWsgPyBcIkJyZWFrU3RhdGVtZW50XCIgOiBcIkNvbnRpbnVlU3RhdGVtZW50XCIpO1xufTtcblxucHAucGFyc2VEZWJ1Z2dlclN0YXRlbWVudCA9IGZ1bmN0aW9uIChub2RlKSB7XG4gIHRoaXMubmV4dCgpO1xuICB0aGlzLnNlbWljb2xvbigpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiRGVidWdnZXJTdGF0ZW1lbnRcIik7XG59O1xuXG5wcC5wYXJzZURvU3RhdGVtZW50ID0gZnVuY3Rpb24gKG5vZGUpIHtcbiAgdGhpcy5uZXh0KCk7XG4gIHRoaXMubGFiZWxzLnB1c2gobG9vcExhYmVsKTtcbiAgbm9kZS5ib2R5ID0gdGhpcy5wYXJzZVN0YXRlbWVudChmYWxzZSk7XG4gIHRoaXMubGFiZWxzLnBvcCgpO1xuICB0aGlzLmV4cGVjdCh0dC5fd2hpbGUpO1xuICBub2RlLnRlc3QgPSB0aGlzLnBhcnNlUGFyZW5FeHByZXNzaW9uKCk7XG4gIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNikgdGhpcy5lYXQodHQuc2VtaSk7ZWxzZSB0aGlzLnNlbWljb2xvbigpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiRG9XaGlsZVN0YXRlbWVudFwiKTtcbn07XG5cbi8vIERpc2FtYmlndWF0aW5nIGJldHdlZW4gYSBgZm9yYCBhbmQgYSBgZm9yYC9gaW5gIG9yIGBmb3JgL2BvZmBcbi8vIGxvb3AgaXMgbm9uLXRyaXZpYWwuIEJhc2ljYWxseSwgd2UgaGF2ZSB0byBwYXJzZSB0aGUgaW5pdCBgdmFyYFxuLy8gc3RhdGVtZW50IG9yIGV4cHJlc3Npb24sIGRpc2FsbG93aW5nIHRoZSBgaW5gIG9wZXJhdG9yIChzZWVcbi8vIHRoZSBzZWNvbmQgcGFyYW1ldGVyIHRvIGBwYXJzZUV4cHJlc3Npb25gKSwgYW5kIHRoZW4gY2hlY2tcbi8vIHdoZXRoZXIgdGhlIG5leHQgdG9rZW4gaXMgYGluYCBvciBgb2ZgLiBXaGVuIHRoZXJlIGlzIG5vIGluaXRcbi8vIHBhcnQgKHNlbWljb2xvbiBpbW1lZGlhdGVseSBhZnRlciB0aGUgb3BlbmluZyBwYXJlbnRoZXNpcyksIGl0XG4vLyBpcyBhIHJlZ3VsYXIgYGZvcmAgbG9vcC5cblxucHAucGFyc2VGb3JTdGF0ZW1lbnQgPSBmdW5jdGlvbiAobm9kZSkge1xuICB0aGlzLm5leHQoKTtcbiAgdGhpcy5sYWJlbHMucHVzaChsb29wTGFiZWwpO1xuICB0aGlzLmV4cGVjdCh0dC5wYXJlbkwpO1xuICBpZiAodGhpcy50eXBlID09PSB0dC5zZW1pKSByZXR1cm4gdGhpcy5wYXJzZUZvcihub2RlLCBudWxsKTtcbiAgaWYgKHRoaXMudHlwZSA9PT0gdHQuX3ZhciB8fCB0aGlzLnR5cGUgPT09IHR0Ll9sZXQgfHwgdGhpcy50eXBlID09PSB0dC5fY29uc3QpIHtcbiAgICB2YXIgX2luaXQgPSB0aGlzLnN0YXJ0Tm9kZSgpLFxuICAgICAgICB2YXJLaW5kID0gdGhpcy50eXBlO1xuICAgIHRoaXMubmV4dCgpO1xuICAgIHRoaXMucGFyc2VWYXIoX2luaXQsIHRydWUsIHZhcktpbmQpO1xuICAgIHRoaXMuZmluaXNoTm9kZShfaW5pdCwgXCJWYXJpYWJsZURlY2xhcmF0aW9uXCIpO1xuICAgIGlmICgodGhpcy50eXBlID09PSB0dC5faW4gfHwgdGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYgJiYgdGhpcy5pc0NvbnRleHR1YWwoXCJvZlwiKSkgJiYgX2luaXQuZGVjbGFyYXRpb25zLmxlbmd0aCA9PT0gMSAmJiAhKHZhcktpbmQgIT09IHR0Ll92YXIgJiYgX2luaXQuZGVjbGFyYXRpb25zWzBdLmluaXQpKSByZXR1cm4gdGhpcy5wYXJzZUZvckluKG5vZGUsIF9pbml0KTtcbiAgICByZXR1cm4gdGhpcy5wYXJzZUZvcihub2RlLCBfaW5pdCk7XG4gIH1cbiAgdmFyIHJlZlNob3J0aGFuZERlZmF1bHRQb3MgPSB7IHN0YXJ0OiAwIH07XG4gIHZhciBpbml0ID0gdGhpcy5wYXJzZUV4cHJlc3Npb24odHJ1ZSwgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcyk7XG4gIGlmICh0aGlzLnR5cGUgPT09IHR0Ll9pbiB8fCB0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNiAmJiB0aGlzLmlzQ29udGV4dHVhbChcIm9mXCIpKSB7XG4gICAgdGhpcy50b0Fzc2lnbmFibGUoaW5pdCk7XG4gICAgdGhpcy5jaGVja0xWYWwoaW5pdCk7XG4gICAgcmV0dXJuIHRoaXMucGFyc2VGb3JJbihub2RlLCBpbml0KTtcbiAgfSBlbHNlIGlmIChyZWZTaG9ydGhhbmREZWZhdWx0UG9zLnN0YXJ0KSB7XG4gICAgdGhpcy51bmV4cGVjdGVkKHJlZlNob3J0aGFuZERlZmF1bHRQb3Muc3RhcnQpO1xuICB9XG4gIHJldHVybiB0aGlzLnBhcnNlRm9yKG5vZGUsIGluaXQpO1xufTtcblxucHAucGFyc2VGdW5jdGlvblN0YXRlbWVudCA9IGZ1bmN0aW9uIChub2RlKSB7XG4gIHRoaXMubmV4dCgpO1xuICByZXR1cm4gdGhpcy5wYXJzZUZ1bmN0aW9uKG5vZGUsIHRydWUpO1xufTtcblxucHAucGFyc2VJZlN0YXRlbWVudCA9IGZ1bmN0aW9uIChub2RlKSB7XG4gIHRoaXMubmV4dCgpO1xuICBub2RlLnRlc3QgPSB0aGlzLnBhcnNlUGFyZW5FeHByZXNzaW9uKCk7XG4gIG5vZGUuY29uc2VxdWVudCA9IHRoaXMucGFyc2VTdGF0ZW1lbnQoZmFsc2UpO1xuICBub2RlLmFsdGVybmF0ZSA9IHRoaXMuZWF0KHR0Ll9lbHNlKSA/IHRoaXMucGFyc2VTdGF0ZW1lbnQoZmFsc2UpIDogbnVsbDtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIklmU3RhdGVtZW50XCIpO1xufTtcblxucHAucGFyc2VSZXR1cm5TdGF0ZW1lbnQgPSBmdW5jdGlvbiAobm9kZSkge1xuICBpZiAoIXRoaXMuaW5GdW5jdGlvbiAmJiAhdGhpcy5vcHRpb25zLmFsbG93UmV0dXJuT3V0c2lkZUZ1bmN0aW9uKSB0aGlzLnJhaXNlKHRoaXMuc3RhcnQsIFwiJ3JldHVybicgb3V0c2lkZSBvZiBmdW5jdGlvblwiKTtcbiAgdGhpcy5uZXh0KCk7XG5cbiAgLy8gSW4gYHJldHVybmAgKGFuZCBgYnJlYWtgL2Bjb250aW51ZWApLCB0aGUga2V5d29yZHMgd2l0aFxuICAvLyBvcHRpb25hbCBhcmd1bWVudHMsIHdlIGVhZ2VybHkgbG9vayBmb3IgYSBzZW1pY29sb24gb3IgdGhlXG4gIC8vIHBvc3NpYmlsaXR5IHRvIGluc2VydCBvbmUuXG5cbiAgaWYgKHRoaXMuZWF0KHR0LnNlbWkpIHx8IHRoaXMuaW5zZXJ0U2VtaWNvbG9uKCkpIG5vZGUuYXJndW1lbnQgPSBudWxsO2Vsc2Uge1xuICAgIG5vZGUuYXJndW1lbnQgPSB0aGlzLnBhcnNlRXhwcmVzc2lvbigpO3RoaXMuc2VtaWNvbG9uKCk7XG4gIH1cbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIlJldHVyblN0YXRlbWVudFwiKTtcbn07XG5cbnBwLnBhcnNlU3dpdGNoU3RhdGVtZW50ID0gZnVuY3Rpb24gKG5vZGUpIHtcbiAgdGhpcy5uZXh0KCk7XG4gIG5vZGUuZGlzY3JpbWluYW50ID0gdGhpcy5wYXJzZVBhcmVuRXhwcmVzc2lvbigpO1xuICBub2RlLmNhc2VzID0gW107XG4gIHRoaXMuZXhwZWN0KHR0LmJyYWNlTCk7XG4gIHRoaXMubGFiZWxzLnB1c2goc3dpdGNoTGFiZWwpO1xuXG4gIC8vIFN0YXRlbWVudHMgdW5kZXIgbXVzdCBiZSBncm91cGVkIChieSBsYWJlbCkgaW4gU3dpdGNoQ2FzZVxuICAvLyBub2Rlcy4gYGN1cmAgaXMgdXNlZCB0byBrZWVwIHRoZSBub2RlIHRoYXQgd2UgYXJlIGN1cnJlbnRseVxuICAvLyBhZGRpbmcgc3RhdGVtZW50cyB0by5cblxuICBmb3IgKHZhciBjdXIsIHNhd0RlZmF1bHQ7IHRoaXMudHlwZSAhPSB0dC5icmFjZVI7KSB7XG4gICAgaWYgKHRoaXMudHlwZSA9PT0gdHQuX2Nhc2UgfHwgdGhpcy50eXBlID09PSB0dC5fZGVmYXVsdCkge1xuICAgICAgdmFyIGlzQ2FzZSA9IHRoaXMudHlwZSA9PT0gdHQuX2Nhc2U7XG4gICAgICBpZiAoY3VyKSB0aGlzLmZpbmlzaE5vZGUoY3VyLCBcIlN3aXRjaENhc2VcIik7XG4gICAgICBub2RlLmNhc2VzLnB1c2goY3VyID0gdGhpcy5zdGFydE5vZGUoKSk7XG4gICAgICBjdXIuY29uc2VxdWVudCA9IFtdO1xuICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICBpZiAoaXNDYXNlKSB7XG4gICAgICAgIGN1ci50ZXN0ID0gdGhpcy5wYXJzZUV4cHJlc3Npb24oKTtcbiAgICAgIH0gZWxzZSB7XG4gICAgICAgIGlmIChzYXdEZWZhdWx0KSB0aGlzLnJhaXNlKHRoaXMubGFzdFRva1N0YXJ0LCBcIk11bHRpcGxlIGRlZmF1bHQgY2xhdXNlc1wiKTtcbiAgICAgICAgc2F3RGVmYXVsdCA9IHRydWU7XG4gICAgICAgIGN1ci50ZXN0ID0gbnVsbDtcbiAgICAgIH1cbiAgICAgIHRoaXMuZXhwZWN0KHR0LmNvbG9uKTtcbiAgICB9IGVsc2Uge1xuICAgICAgaWYgKCFjdXIpIHRoaXMudW5leHBlY3RlZCgpO1xuICAgICAgY3VyLmNvbnNlcXVlbnQucHVzaCh0aGlzLnBhcnNlU3RhdGVtZW50KHRydWUpKTtcbiAgICB9XG4gIH1cbiAgaWYgKGN1cikgdGhpcy5maW5pc2hOb2RlKGN1ciwgXCJTd2l0Y2hDYXNlXCIpO1xuICB0aGlzLm5leHQoKTsgLy8gQ2xvc2luZyBicmFjZVxuICB0aGlzLmxhYmVscy5wb3AoKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIlN3aXRjaFN0YXRlbWVudFwiKTtcbn07XG5cbnBwLnBhcnNlVGhyb3dTdGF0ZW1lbnQgPSBmdW5jdGlvbiAobm9kZSkge1xuICB0aGlzLm5leHQoKTtcbiAgaWYgKGxpbmVCcmVhay50ZXN0KHRoaXMuaW5wdXQuc2xpY2UodGhpcy5sYXN0VG9rRW5kLCB0aGlzLnN0YXJ0KSkpIHRoaXMucmFpc2UodGhpcy5sYXN0VG9rRW5kLCBcIklsbGVnYWwgbmV3bGluZSBhZnRlciB0aHJvd1wiKTtcbiAgbm9kZS5hcmd1bWVudCA9IHRoaXMucGFyc2VFeHByZXNzaW9uKCk7XG4gIHRoaXMuc2VtaWNvbG9uKCk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJUaHJvd1N0YXRlbWVudFwiKTtcbn07XG5cbi8vIFJldXNlZCBlbXB0eSBhcnJheSBhZGRlZCBmb3Igbm9kZSBmaWVsZHMgdGhhdCBhcmUgYWx3YXlzIGVtcHR5LlxuXG52YXIgZW1wdHkgPSBbXTtcblxucHAucGFyc2VUcnlTdGF0ZW1lbnQgPSBmdW5jdGlvbiAobm9kZSkge1xuICB0aGlzLm5leHQoKTtcbiAgbm9kZS5ibG9jayA9IHRoaXMucGFyc2VCbG9jaygpO1xuICBub2RlLmhhbmRsZXIgPSBudWxsO1xuICBpZiAodGhpcy50eXBlID09PSB0dC5fY2F0Y2gpIHtcbiAgICB2YXIgY2xhdXNlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgICB0aGlzLm5leHQoKTtcbiAgICB0aGlzLmV4cGVjdCh0dC5wYXJlbkwpO1xuICAgIGNsYXVzZS5wYXJhbSA9IHRoaXMucGFyc2VCaW5kaW5nQXRvbSgpO1xuICAgIHRoaXMuY2hlY2tMVmFsKGNsYXVzZS5wYXJhbSwgdHJ1ZSk7XG4gICAgdGhpcy5leHBlY3QodHQucGFyZW5SKTtcbiAgICBjbGF1c2UuZ3VhcmQgPSBudWxsO1xuICAgIGNsYXVzZS5ib2R5ID0gdGhpcy5wYXJzZUJsb2NrKCk7XG4gICAgbm9kZS5oYW5kbGVyID0gdGhpcy5maW5pc2hOb2RlKGNsYXVzZSwgXCJDYXRjaENsYXVzZVwiKTtcbiAgfVxuICBub2RlLmd1YXJkZWRIYW5kbGVycyA9IGVtcHR5O1xuICBub2RlLmZpbmFsaXplciA9IHRoaXMuZWF0KHR0Ll9maW5hbGx5KSA/IHRoaXMucGFyc2VCbG9jaygpIDogbnVsbDtcbiAgaWYgKCFub2RlLmhhbmRsZXIgJiYgIW5vZGUuZmluYWxpemVyKSB0aGlzLnJhaXNlKG5vZGUuc3RhcnQsIFwiTWlzc2luZyBjYXRjaCBvciBmaW5hbGx5IGNsYXVzZVwiKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIlRyeVN0YXRlbWVudFwiKTtcbn07XG5cbnBwLnBhcnNlVmFyU3RhdGVtZW50ID0gZnVuY3Rpb24gKG5vZGUsIGtpbmQpIHtcbiAgdGhpcy5uZXh0KCk7XG4gIHRoaXMucGFyc2VWYXIobm9kZSwgZmFsc2UsIGtpbmQpO1xuICB0aGlzLnNlbWljb2xvbigpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiVmFyaWFibGVEZWNsYXJhdGlvblwiKTtcbn07XG5cbnBwLnBhcnNlV2hpbGVTdGF0ZW1lbnQgPSBmdW5jdGlvbiAobm9kZSkge1xuICB0aGlzLm5leHQoKTtcbiAgbm9kZS50ZXN0ID0gdGhpcy5wYXJzZVBhcmVuRXhwcmVzc2lvbigpO1xuICB0aGlzLmxhYmVscy5wdXNoKGxvb3BMYWJlbCk7XG4gIG5vZGUuYm9keSA9IHRoaXMucGFyc2VTdGF0ZW1lbnQoZmFsc2UpO1xuICB0aGlzLmxhYmVscy5wb3AoKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIldoaWxlU3RhdGVtZW50XCIpO1xufTtcblxucHAucGFyc2VXaXRoU3RhdGVtZW50ID0gZnVuY3Rpb24gKG5vZGUpIHtcbiAgaWYgKHRoaXMuc3RyaWN0KSB0aGlzLnJhaXNlKHRoaXMuc3RhcnQsIFwiJ3dpdGgnIGluIHN0cmljdCBtb2RlXCIpO1xuICB0aGlzLm5leHQoKTtcbiAgbm9kZS5vYmplY3QgPSB0aGlzLnBhcnNlUGFyZW5FeHByZXNzaW9uKCk7XG4gIG5vZGUuYm9keSA9IHRoaXMucGFyc2VTdGF0ZW1lbnQoZmFsc2UpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiV2l0aFN0YXRlbWVudFwiKTtcbn07XG5cbnBwLnBhcnNlRW1wdHlTdGF0ZW1lbnQgPSBmdW5jdGlvbiAobm9kZSkge1xuICB0aGlzLm5leHQoKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkVtcHR5U3RhdGVtZW50XCIpO1xufTtcblxucHAucGFyc2VMYWJlbGVkU3RhdGVtZW50ID0gZnVuY3Rpb24gKG5vZGUsIG1heWJlTmFtZSwgZXhwcikge1xuICBmb3IgKHZhciBpID0gMDsgaSA8IHRoaXMubGFiZWxzLmxlbmd0aDsgKytpKSB7XG4gICAgaWYgKHRoaXMubGFiZWxzW2ldLm5hbWUgPT09IG1heWJlTmFtZSkgdGhpcy5yYWlzZShleHByLnN0YXJ0LCBcIkxhYmVsICdcIiArIG1heWJlTmFtZSArIFwiJyBpcyBhbHJlYWR5IGRlY2xhcmVkXCIpO1xuICB9dmFyIGtpbmQgPSB0aGlzLnR5cGUuaXNMb29wID8gXCJsb29wXCIgOiB0aGlzLnR5cGUgPT09IHR0Ll9zd2l0Y2ggPyBcInN3aXRjaFwiIDogbnVsbDtcbiAgdGhpcy5sYWJlbHMucHVzaCh7IG5hbWU6IG1heWJlTmFtZSwga2luZDoga2luZCB9KTtcbiAgbm9kZS5ib2R5ID0gdGhpcy5wYXJzZVN0YXRlbWVudCh0cnVlKTtcbiAgdGhpcy5sYWJlbHMucG9wKCk7XG4gIG5vZGUubGFiZWwgPSBleHByO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiTGFiZWxlZFN0YXRlbWVudFwiKTtcbn07XG5cbnBwLnBhcnNlRXhwcmVzc2lvblN0YXRlbWVudCA9IGZ1bmN0aW9uIChub2RlLCBleHByKSB7XG4gIG5vZGUuZXhwcmVzc2lvbiA9IGV4cHI7XG4gIHRoaXMuc2VtaWNvbG9uKCk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJFeHByZXNzaW9uU3RhdGVtZW50XCIpO1xufTtcblxuLy8gUGFyc2UgYSBzZW1pY29sb24tZW5jbG9zZWQgYmxvY2sgb2Ygc3RhdGVtZW50cywgaGFuZGxpbmcgYFwidXNlXG4vLyBzdHJpY3RcImAgZGVjbGFyYXRpb25zIHdoZW4gYGFsbG93U3RyaWN0YCBpcyB0cnVlICh1c2VkIGZvclxuLy8gZnVuY3Rpb24gYm9kaWVzKS5cblxucHAucGFyc2VCbG9jayA9IGZ1bmN0aW9uIChhbGxvd1N0cmljdCkge1xuICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCksXG4gICAgICBmaXJzdCA9IHRydWUsXG4gICAgICBvbGRTdHJpY3QgPSB1bmRlZmluZWQ7XG4gIG5vZGUuYm9keSA9IFtdO1xuICB0aGlzLmV4cGVjdCh0dC5icmFjZUwpO1xuICB3aGlsZSAoIXRoaXMuZWF0KHR0LmJyYWNlUikpIHtcbiAgICB2YXIgc3RtdCA9IHRoaXMucGFyc2VTdGF0ZW1lbnQodHJ1ZSk7XG4gICAgbm9kZS5ib2R5LnB1c2goc3RtdCk7XG4gICAgaWYgKGZpcnN0ICYmIGFsbG93U3RyaWN0ICYmIHRoaXMuaXNVc2VTdHJpY3Qoc3RtdCkpIHtcbiAgICAgIG9sZFN0cmljdCA9IHRoaXMuc3RyaWN0O1xuICAgICAgdGhpcy5zZXRTdHJpY3QodGhpcy5zdHJpY3QgPSB0cnVlKTtcbiAgICB9XG4gICAgZmlyc3QgPSBmYWxzZTtcbiAgfVxuICBpZiAob2xkU3RyaWN0ID09PSBmYWxzZSkgdGhpcy5zZXRTdHJpY3QoZmFsc2UpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiQmxvY2tTdGF0ZW1lbnRcIik7XG59O1xuXG4vLyBQYXJzZSBhIHJlZ3VsYXIgYGZvcmAgbG9vcC4gVGhlIGRpc2FtYmlndWF0aW9uIGNvZGUgaW5cbi8vIGBwYXJzZVN0YXRlbWVudGAgd2lsbCBhbHJlYWR5IGhhdmUgcGFyc2VkIHRoZSBpbml0IHN0YXRlbWVudCBvclxuLy8gZXhwcmVzc2lvbi5cblxucHAucGFyc2VGb3IgPSBmdW5jdGlvbiAobm9kZSwgaW5pdCkge1xuICBub2RlLmluaXQgPSBpbml0O1xuICB0aGlzLmV4cGVjdCh0dC5zZW1pKTtcbiAgbm9kZS50ZXN0ID0gdGhpcy50eXBlID09PSB0dC5zZW1pID8gbnVsbCA6IHRoaXMucGFyc2VFeHByZXNzaW9uKCk7XG4gIHRoaXMuZXhwZWN0KHR0LnNlbWkpO1xuICBub2RlLnVwZGF0ZSA9IHRoaXMudHlwZSA9PT0gdHQucGFyZW5SID8gbnVsbCA6IHRoaXMucGFyc2VFeHByZXNzaW9uKCk7XG4gIHRoaXMuZXhwZWN0KHR0LnBhcmVuUik7XG4gIG5vZGUuYm9keSA9IHRoaXMucGFyc2VTdGF0ZW1lbnQoZmFsc2UpO1xuICB0aGlzLmxhYmVscy5wb3AoKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkZvclN0YXRlbWVudFwiKTtcbn07XG5cbi8vIFBhcnNlIGEgYGZvcmAvYGluYCBhbmQgYGZvcmAvYG9mYCBsb29wLCB3aGljaCBhcmUgYWxtb3N0XG4vLyBzYW1lIGZyb20gcGFyc2VyJ3MgcGVyc3BlY3RpdmUuXG5cbnBwLnBhcnNlRm9ySW4gPSBmdW5jdGlvbiAobm9kZSwgaW5pdCkge1xuICB2YXIgdHlwZSA9IHRoaXMudHlwZSA9PT0gdHQuX2luID8gXCJGb3JJblN0YXRlbWVudFwiIDogXCJGb3JPZlN0YXRlbWVudFwiO1xuICB0aGlzLm5leHQoKTtcbiAgbm9kZS5sZWZ0ID0gaW5pdDtcbiAgbm9kZS5yaWdodCA9IHRoaXMucGFyc2VFeHByZXNzaW9uKCk7XG4gIHRoaXMuZXhwZWN0KHR0LnBhcmVuUik7XG4gIG5vZGUuYm9keSA9IHRoaXMucGFyc2VTdGF0ZW1lbnQoZmFsc2UpO1xuICB0aGlzLmxhYmVscy5wb3AoKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCB0eXBlKTtcbn07XG5cbi8vIFBhcnNlIGEgbGlzdCBvZiB2YXJpYWJsZSBkZWNsYXJhdGlvbnMuXG5cbnBwLnBhcnNlVmFyID0gZnVuY3Rpb24gKG5vZGUsIGlzRm9yLCBraW5kKSB7XG4gIG5vZGUuZGVjbGFyYXRpb25zID0gW107XG4gIG5vZGUua2luZCA9IGtpbmQua2V5d29yZDtcbiAgZm9yICg7Oykge1xuICAgIHZhciBkZWNsID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgICB0aGlzLnBhcnNlVmFySWQoZGVjbCk7XG4gICAgaWYgKHRoaXMuZWF0KHR0LmVxKSkge1xuICAgICAgZGVjbC5pbml0ID0gdGhpcy5wYXJzZU1heWJlQXNzaWduKGlzRm9yKTtcbiAgICB9IGVsc2UgaWYgKGtpbmQgPT09IHR0Ll9jb25zdCAmJiAhKHRoaXMudHlwZSA9PT0gdHQuX2luIHx8IHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2ICYmIHRoaXMuaXNDb250ZXh0dWFsKFwib2ZcIikpKSB7XG4gICAgICB0aGlzLnVuZXhwZWN0ZWQoKTtcbiAgICB9IGVsc2UgaWYgKGRlY2wuaWQudHlwZSAhPSBcIklkZW50aWZpZXJcIiAmJiAhKGlzRm9yICYmICh0aGlzLnR5cGUgPT09IHR0Ll9pbiB8fCB0aGlzLmlzQ29udGV4dHVhbChcIm9mXCIpKSkpIHtcbiAgICAgIHRoaXMucmFpc2UodGhpcy5sYXN0VG9rRW5kLCBcIkNvbXBsZXggYmluZGluZyBwYXR0ZXJucyByZXF1aXJlIGFuIGluaXRpYWxpemF0aW9uIHZhbHVlXCIpO1xuICAgIH0gZWxzZSB7XG4gICAgICBkZWNsLmluaXQgPSBudWxsO1xuICAgIH1cbiAgICBub2RlLmRlY2xhcmF0aW9ucy5wdXNoKHRoaXMuZmluaXNoTm9kZShkZWNsLCBcIlZhcmlhYmxlRGVjbGFyYXRvclwiKSk7XG4gICAgaWYgKCF0aGlzLmVhdCh0dC5jb21tYSkpIGJyZWFrO1xuICB9XG4gIHJldHVybiBub2RlO1xufTtcblxucHAucGFyc2VWYXJJZCA9IGZ1bmN0aW9uIChkZWNsKSB7XG4gIGRlY2wuaWQgPSB0aGlzLnBhcnNlQmluZGluZ0F0b20oKTtcbiAgdGhpcy5jaGVja0xWYWwoZGVjbC5pZCwgdHJ1ZSk7XG59O1xuXG4vLyBQYXJzZSBhIGZ1bmN0aW9uIGRlY2xhcmF0aW9uIG9yIGxpdGVyYWwgKGRlcGVuZGluZyBvbiB0aGVcbi8vIGBpc1N0YXRlbWVudGAgcGFyYW1ldGVyKS5cblxucHAucGFyc2VGdW5jdGlvbiA9IGZ1bmN0aW9uIChub2RlLCBpc1N0YXRlbWVudCwgYWxsb3dFeHByZXNzaW9uQm9keSkge1xuICB0aGlzLmluaXRGdW5jdGlvbihub2RlKTtcbiAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KSBub2RlLmdlbmVyYXRvciA9IHRoaXMuZWF0KHR0LnN0YXIpO1xuICBpZiAoaXNTdGF0ZW1lbnQgfHwgdGhpcy50eXBlID09PSB0dC5uYW1lKSBub2RlLmlkID0gdGhpcy5wYXJzZUlkZW50KCk7XG4gIHRoaXMucGFyc2VGdW5jdGlvblBhcmFtcyhub2RlKTtcbiAgdGhpcy5wYXJzZUZ1bmN0aW9uQm9keShub2RlLCBhbGxvd0V4cHJlc3Npb25Cb2R5KTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBpc1N0YXRlbWVudCA/IFwiRnVuY3Rpb25EZWNsYXJhdGlvblwiIDogXCJGdW5jdGlvbkV4cHJlc3Npb25cIik7XG59O1xuXG5wcC5wYXJzZUZ1bmN0aW9uUGFyYW1zID0gZnVuY3Rpb24gKG5vZGUpIHtcbiAgdGhpcy5leHBlY3QodHQucGFyZW5MKTtcbiAgbm9kZS5wYXJhbXMgPSB0aGlzLnBhcnNlQmluZGluZ0xpc3QodHQucGFyZW5SLCBmYWxzZSwgZmFsc2UpO1xufTtcblxuLy8gUGFyc2UgYSBjbGFzcyBkZWNsYXJhdGlvbiBvciBsaXRlcmFsIChkZXBlbmRpbmcgb24gdGhlXG4vLyBgaXNTdGF0ZW1lbnRgIHBhcmFtZXRlcikuXG5cbnBwLnBhcnNlQ2xhc3MgPSBmdW5jdGlvbiAobm9kZSwgaXNTdGF0ZW1lbnQpIHtcbiAgdGhpcy5uZXh0KCk7XG4gIHRoaXMucGFyc2VDbGFzc0lkKG5vZGUsIGlzU3RhdGVtZW50KTtcbiAgdGhpcy5wYXJzZUNsYXNzU3VwZXIobm9kZSk7XG4gIHZhciBjbGFzc0JvZHkgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICB2YXIgaGFkQ29uc3RydWN0b3IgPSBmYWxzZTtcbiAgY2xhc3NCb2R5LmJvZHkgPSBbXTtcbiAgdGhpcy5leHBlY3QodHQuYnJhY2VMKTtcbiAgd2hpbGUgKCF0aGlzLmVhdCh0dC5icmFjZVIpKSB7XG4gICAgaWYgKHRoaXMuZWF0KHR0LnNlbWkpKSBjb250aW51ZTtcbiAgICB2YXIgbWV0aG9kID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgICB2YXIgaXNHZW5lcmF0b3IgPSB0aGlzLmVhdCh0dC5zdGFyKTtcbiAgICB2YXIgaXNNYXliZVN0YXRpYyA9IHRoaXMudHlwZSA9PT0gdHQubmFtZSAmJiB0aGlzLnZhbHVlID09PSBcInN0YXRpY1wiO1xuICAgIHRoaXMucGFyc2VQcm9wZXJ0eU5hbWUobWV0aG9kKTtcbiAgICBtZXRob2RbXCJzdGF0aWNcIl0gPSBpc01heWJlU3RhdGljICYmIHRoaXMudHlwZSAhPT0gdHQucGFyZW5MO1xuICAgIGlmIChtZXRob2RbXCJzdGF0aWNcIl0pIHtcbiAgICAgIGlmIChpc0dlbmVyYXRvcikgdGhpcy51bmV4cGVjdGVkKCk7XG4gICAgICBpc0dlbmVyYXRvciA9IHRoaXMuZWF0KHR0LnN0YXIpO1xuICAgICAgdGhpcy5wYXJzZVByb3BlcnR5TmFtZShtZXRob2QpO1xuICAgIH1cbiAgICBtZXRob2Qua2luZCA9IFwibWV0aG9kXCI7XG4gICAgaWYgKCFtZXRob2QuY29tcHV0ZWQpIHtcbiAgICAgIHZhciBrZXkgPSBtZXRob2Qua2V5O1xuXG4gICAgICB2YXIgaXNHZXRTZXQgPSBmYWxzZTtcbiAgICAgIGlmICghaXNHZW5lcmF0b3IgJiYga2V5LnR5cGUgPT09IFwiSWRlbnRpZmllclwiICYmIHRoaXMudHlwZSAhPT0gdHQucGFyZW5MICYmIChrZXkubmFtZSA9PT0gXCJnZXRcIiB8fCBrZXkubmFtZSA9PT0gXCJzZXRcIikpIHtcbiAgICAgICAgaXNHZXRTZXQgPSB0cnVlO1xuICAgICAgICBtZXRob2Qua2luZCA9IGtleS5uYW1lO1xuICAgICAgICBrZXkgPSB0aGlzLnBhcnNlUHJvcGVydHlOYW1lKG1ldGhvZCk7XG4gICAgICB9XG4gICAgICBpZiAoIW1ldGhvZFtcInN0YXRpY1wiXSAmJiAoa2V5LnR5cGUgPT09IFwiSWRlbnRpZmllclwiICYmIGtleS5uYW1lID09PSBcImNvbnN0cnVjdG9yXCIgfHwga2V5LnR5cGUgPT09IFwiTGl0ZXJhbFwiICYmIGtleS52YWx1ZSA9PT0gXCJjb25zdHJ1Y3RvclwiKSkge1xuICAgICAgICBpZiAoaGFkQ29uc3RydWN0b3IpIHRoaXMucmFpc2Uoa2V5LnN0YXJ0LCBcIkR1cGxpY2F0ZSBjb25zdHJ1Y3RvciBpbiB0aGUgc2FtZSBjbGFzc1wiKTtcbiAgICAgICAgaWYgKGlzR2V0U2V0KSB0aGlzLnJhaXNlKGtleS5zdGFydCwgXCJDb25zdHJ1Y3RvciBjYW4ndCBoYXZlIGdldC9zZXQgbW9kaWZpZXJcIik7XG4gICAgICAgIGlmIChpc0dlbmVyYXRvcikgdGhpcy5yYWlzZShrZXkuc3RhcnQsIFwiQ29uc3RydWN0b3IgY2FuJ3QgYmUgYSBnZW5lcmF0b3JcIik7XG4gICAgICAgIG1ldGhvZC5raW5kID0gXCJjb25zdHJ1Y3RvclwiO1xuICAgICAgICBoYWRDb25zdHJ1Y3RvciA9IHRydWU7XG4gICAgICB9XG4gICAgfVxuICAgIHRoaXMucGFyc2VDbGFzc01ldGhvZChjbGFzc0JvZHksIG1ldGhvZCwgaXNHZW5lcmF0b3IpO1xuICB9XG4gIG5vZGUuYm9keSA9IHRoaXMuZmluaXNoTm9kZShjbGFzc0JvZHksIFwiQ2xhc3NCb2R5XCIpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIGlzU3RhdGVtZW50ID8gXCJDbGFzc0RlY2xhcmF0aW9uXCIgOiBcIkNsYXNzRXhwcmVzc2lvblwiKTtcbn07XG5cbnBwLnBhcnNlQ2xhc3NNZXRob2QgPSBmdW5jdGlvbiAoY2xhc3NCb2R5LCBtZXRob2QsIGlzR2VuZXJhdG9yKSB7XG4gIG1ldGhvZC52YWx1ZSA9IHRoaXMucGFyc2VNZXRob2QoaXNHZW5lcmF0b3IpO1xuICBjbGFzc0JvZHkuYm9keS5wdXNoKHRoaXMuZmluaXNoTm9kZShtZXRob2QsIFwiTWV0aG9kRGVmaW5pdGlvblwiKSk7XG59O1xuXG5wcC5wYXJzZUNsYXNzSWQgPSBmdW5jdGlvbiAobm9kZSwgaXNTdGF0ZW1lbnQpIHtcbiAgbm9kZS5pZCA9IHRoaXMudHlwZSA9PT0gdHQubmFtZSA/IHRoaXMucGFyc2VJZGVudCgpIDogaXNTdGF0ZW1lbnQgPyB0aGlzLnVuZXhwZWN0ZWQoKSA6IG51bGw7XG59O1xuXG5wcC5wYXJzZUNsYXNzU3VwZXIgPSBmdW5jdGlvbiAobm9kZSkge1xuICBub2RlLnN1cGVyQ2xhc3MgPSB0aGlzLmVhdCh0dC5fZXh0ZW5kcykgPyB0aGlzLnBhcnNlRXhwclN1YnNjcmlwdHMoKSA6IG51bGw7XG59O1xuXG4vLyBQYXJzZXMgbW9kdWxlIGV4cG9ydCBkZWNsYXJhdGlvbi5cblxucHAucGFyc2VFeHBvcnQgPSBmdW5jdGlvbiAobm9kZSkge1xuICB0aGlzLm5leHQoKTtcbiAgLy8gZXhwb3J0ICogZnJvbSAnLi4uJ1xuICBpZiAodGhpcy5lYXQodHQuc3RhcikpIHtcbiAgICB0aGlzLmV4cGVjdENvbnRleHR1YWwoXCJmcm9tXCIpO1xuICAgIG5vZGUuc291cmNlID0gdGhpcy50eXBlID09PSB0dC5zdHJpbmcgPyB0aGlzLnBhcnNlRXhwckF0b20oKSA6IHRoaXMudW5leHBlY3RlZCgpO1xuICAgIHRoaXMuc2VtaWNvbG9uKCk7XG4gICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkV4cG9ydEFsbERlY2xhcmF0aW9uXCIpO1xuICB9XG4gIGlmICh0aGlzLmVhdCh0dC5fZGVmYXVsdCkpIHtcbiAgICAvLyBleHBvcnQgZGVmYXVsdCAuLi5cbiAgICB2YXIgZXhwciA9IHRoaXMucGFyc2VNYXliZUFzc2lnbigpO1xuICAgIHZhciBuZWVkc1NlbWkgPSB0cnVlO1xuICAgIGlmIChleHByLnR5cGUgPT0gXCJGdW5jdGlvbkV4cHJlc3Npb25cIiB8fCBleHByLnR5cGUgPT0gXCJDbGFzc0V4cHJlc3Npb25cIikge1xuICAgICAgbmVlZHNTZW1pID0gZmFsc2U7XG4gICAgICBpZiAoZXhwci5pZCkge1xuICAgICAgICBleHByLnR5cGUgPSBleHByLnR5cGUgPT0gXCJGdW5jdGlvbkV4cHJlc3Npb25cIiA/IFwiRnVuY3Rpb25EZWNsYXJhdGlvblwiIDogXCJDbGFzc0RlY2xhcmF0aW9uXCI7XG4gICAgICB9XG4gICAgfVxuICAgIG5vZGUuZGVjbGFyYXRpb24gPSBleHByO1xuICAgIGlmIChuZWVkc1NlbWkpIHRoaXMuc2VtaWNvbG9uKCk7XG4gICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkV4cG9ydERlZmF1bHREZWNsYXJhdGlvblwiKTtcbiAgfVxuICAvLyBleHBvcnQgdmFyfGNvbnN0fGxldHxmdW5jdGlvbnxjbGFzcyAuLi5cbiAgaWYgKHRoaXMuc2hvdWxkUGFyc2VFeHBvcnRTdGF0ZW1lbnQoKSkge1xuICAgIG5vZGUuZGVjbGFyYXRpb24gPSB0aGlzLnBhcnNlU3RhdGVtZW50KHRydWUpO1xuICAgIG5vZGUuc3BlY2lmaWVycyA9IFtdO1xuICAgIG5vZGUuc291cmNlID0gbnVsbDtcbiAgfSBlbHNlIHtcbiAgICAvLyBleHBvcnQgeyB4LCB5IGFzIHogfSBbZnJvbSAnLi4uJ11cbiAgICBub2RlLmRlY2xhcmF0aW9uID0gbnVsbDtcbiAgICBub2RlLnNwZWNpZmllcnMgPSB0aGlzLnBhcnNlRXhwb3J0U3BlY2lmaWVycygpO1xuICAgIGlmICh0aGlzLmVhdENvbnRleHR1YWwoXCJmcm9tXCIpKSB7XG4gICAgICBub2RlLnNvdXJjZSA9IHRoaXMudHlwZSA9PT0gdHQuc3RyaW5nID8gdGhpcy5wYXJzZUV4cHJBdG9tKCkgOiB0aGlzLnVuZXhwZWN0ZWQoKTtcbiAgICB9IGVsc2Uge1xuICAgICAgbm9kZS5zb3VyY2UgPSBudWxsO1xuICAgIH1cbiAgICB0aGlzLnNlbWljb2xvbigpO1xuICB9XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJFeHBvcnROYW1lZERlY2xhcmF0aW9uXCIpO1xufTtcblxucHAuc2hvdWxkUGFyc2VFeHBvcnRTdGF0ZW1lbnQgPSBmdW5jdGlvbiAoKSB7XG4gIHJldHVybiB0aGlzLnR5cGUua2V5d29yZDtcbn07XG5cbi8vIFBhcnNlcyBhIGNvbW1hLXNlcGFyYXRlZCBsaXN0IG9mIG1vZHVsZSBleHBvcnRzLlxuXG5wcC5wYXJzZUV4cG9ydFNwZWNpZmllcnMgPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBub2RlcyA9IFtdLFxuICAgICAgZmlyc3QgPSB0cnVlO1xuICAvLyBleHBvcnQgeyB4LCB5IGFzIHogfSBbZnJvbSAnLi4uJ11cbiAgdGhpcy5leHBlY3QodHQuYnJhY2VMKTtcbiAgd2hpbGUgKCF0aGlzLmVhdCh0dC5icmFjZVIpKSB7XG4gICAgaWYgKCFmaXJzdCkge1xuICAgICAgdGhpcy5leHBlY3QodHQuY29tbWEpO1xuICAgICAgaWYgKHRoaXMuYWZ0ZXJUcmFpbGluZ0NvbW1hKHR0LmJyYWNlUikpIGJyZWFrO1xuICAgIH0gZWxzZSBmaXJzdCA9IGZhbHNlO1xuXG4gICAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICAgIG5vZGUubG9jYWwgPSB0aGlzLnBhcnNlSWRlbnQodGhpcy50eXBlID09PSB0dC5fZGVmYXVsdCk7XG4gICAgbm9kZS5leHBvcnRlZCA9IHRoaXMuZWF0Q29udGV4dHVhbChcImFzXCIpID8gdGhpcy5wYXJzZUlkZW50KHRydWUpIDogbm9kZS5sb2NhbDtcbiAgICBub2Rlcy5wdXNoKHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkV4cG9ydFNwZWNpZmllclwiKSk7XG4gIH1cbiAgcmV0dXJuIG5vZGVzO1xufTtcblxuLy8gUGFyc2VzIGltcG9ydCBkZWNsYXJhdGlvbi5cblxucHAucGFyc2VJbXBvcnQgPSBmdW5jdGlvbiAobm9kZSkge1xuICB0aGlzLm5leHQoKTtcbiAgLy8gaW1wb3J0ICcuLi4nXG4gIGlmICh0aGlzLnR5cGUgPT09IHR0LnN0cmluZykge1xuICAgIG5vZGUuc3BlY2lmaWVycyA9IGVtcHR5O1xuICAgIG5vZGUuc291cmNlID0gdGhpcy5wYXJzZUV4cHJBdG9tKCk7XG4gICAgbm9kZS5raW5kID0gXCJcIjtcbiAgfSBlbHNlIHtcbiAgICBub2RlLnNwZWNpZmllcnMgPSB0aGlzLnBhcnNlSW1wb3J0U3BlY2lmaWVycygpO1xuICAgIHRoaXMuZXhwZWN0Q29udGV4dHVhbChcImZyb21cIik7XG4gICAgbm9kZS5zb3VyY2UgPSB0aGlzLnR5cGUgPT09IHR0LnN0cmluZyA/IHRoaXMucGFyc2VFeHByQXRvbSgpIDogdGhpcy51bmV4cGVjdGVkKCk7XG4gIH1cbiAgdGhpcy5zZW1pY29sb24oKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkltcG9ydERlY2xhcmF0aW9uXCIpO1xufTtcblxuLy8gUGFyc2VzIGEgY29tbWEtc2VwYXJhdGVkIGxpc3Qgb2YgbW9kdWxlIGltcG9ydHMuXG5cbnBwLnBhcnNlSW1wb3J0U3BlY2lmaWVycyA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIG5vZGVzID0gW10sXG4gICAgICBmaXJzdCA9IHRydWU7XG4gIGlmICh0aGlzLnR5cGUgPT09IHR0Lm5hbWUpIHtcbiAgICAvLyBpbXBvcnQgZGVmYXVsdE9iaiwgeyB4LCB5IGFzIHogfSBmcm9tICcuLi4nXG4gICAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICAgIG5vZGUubG9jYWwgPSB0aGlzLnBhcnNlSWRlbnQoKTtcbiAgICB0aGlzLmNoZWNrTFZhbChub2RlLmxvY2FsLCB0cnVlKTtcbiAgICBub2Rlcy5wdXNoKHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkltcG9ydERlZmF1bHRTcGVjaWZpZXJcIikpO1xuICAgIGlmICghdGhpcy5lYXQodHQuY29tbWEpKSByZXR1cm4gbm9kZXM7XG4gIH1cbiAgaWYgKHRoaXMudHlwZSA9PT0gdHQuc3Rhcikge1xuICAgIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgICB0aGlzLm5leHQoKTtcbiAgICB0aGlzLmV4cGVjdENvbnRleHR1YWwoXCJhc1wiKTtcbiAgICBub2RlLmxvY2FsID0gdGhpcy5wYXJzZUlkZW50KCk7XG4gICAgdGhpcy5jaGVja0xWYWwobm9kZS5sb2NhbCwgdHJ1ZSk7XG4gICAgbm9kZXMucHVzaCh0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJJbXBvcnROYW1lc3BhY2VTcGVjaWZpZXJcIikpO1xuICAgIHJldHVybiBub2RlcztcbiAgfVxuICB0aGlzLmV4cGVjdCh0dC5icmFjZUwpO1xuICB3aGlsZSAoIXRoaXMuZWF0KHR0LmJyYWNlUikpIHtcbiAgICBpZiAoIWZpcnN0KSB7XG4gICAgICB0aGlzLmV4cGVjdCh0dC5jb21tYSk7XG4gICAgICBpZiAodGhpcy5hZnRlclRyYWlsaW5nQ29tbWEodHQuYnJhY2VSKSkgYnJlYWs7XG4gICAgfSBlbHNlIGZpcnN0ID0gZmFsc2U7XG5cbiAgICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gICAgbm9kZS5pbXBvcnRlZCA9IHRoaXMucGFyc2VJZGVudCh0cnVlKTtcbiAgICBub2RlLmxvY2FsID0gdGhpcy5lYXRDb250ZXh0dWFsKFwiYXNcIikgPyB0aGlzLnBhcnNlSWRlbnQoKSA6IG5vZGUuaW1wb3J0ZWQ7XG4gICAgdGhpcy5jaGVja0xWYWwobm9kZS5sb2NhbCwgdHJ1ZSk7XG4gICAgbm9kZXMucHVzaCh0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJJbXBvcnRTcGVjaWZpZXJcIikpO1xuICB9XG4gIHJldHVybiBub2Rlcztcbn07XG5cbn0se1wiLi9zdGF0ZVwiOjEzLFwiLi90b2tlbnR5cGVcIjoxNyxcIi4vd2hpdGVzcGFjZVwiOjE5fV0sMTU6W2Z1bmN0aW9uKF9kZXJlcV8sbW9kdWxlLGV4cG9ydHMpe1xuXCJ1c2Ugc3RyaWN0XCI7XG5cbnZhciBfY2xhc3NDYWxsQ2hlY2sgPSBmdW5jdGlvbiAoaW5zdGFuY2UsIENvbnN0cnVjdG9yKSB7IGlmICghKGluc3RhbmNlIGluc3RhbmNlb2YgQ29uc3RydWN0b3IpKSB7IHRocm93IG5ldyBUeXBlRXJyb3IoXCJDYW5ub3QgY2FsbCBhIGNsYXNzIGFzIGEgZnVuY3Rpb25cIik7IH0gfTtcblxuZXhwb3J0cy5fX2VzTW9kdWxlID0gdHJ1ZTtcbi8vIFRoZSBhbGdvcml0aG0gdXNlZCB0byBkZXRlcm1pbmUgd2hldGhlciBhIHJlZ2V4cCBjYW4gYXBwZWFyIGF0IGFcbi8vIGdpdmVuIHBvaW50IGluIHRoZSBwcm9ncmFtIGlzIGxvb3NlbHkgYmFzZWQgb24gc3dlZXQuanMnIGFwcHJvYWNoLlxuLy8gU2VlIGh0dHBzOi8vZ2l0aHViLmNvbS9tb3ppbGxhL3N3ZWV0LmpzL3dpa2kvZGVzaWduXG5cbnZhciBQYXJzZXIgPSBfZGVyZXFfKFwiLi9zdGF0ZVwiKS5QYXJzZXI7XG5cbnZhciB0dCA9IF9kZXJlcV8oXCIuL3Rva2VudHlwZVwiKS50eXBlcztcblxudmFyIGxpbmVCcmVhayA9IF9kZXJlcV8oXCIuL3doaXRlc3BhY2VcIikubGluZUJyZWFrO1xuXG52YXIgVG9rQ29udGV4dCA9IGV4cG9ydHMuVG9rQ29udGV4dCA9IGZ1bmN0aW9uIFRva0NvbnRleHQodG9rZW4sIGlzRXhwciwgcHJlc2VydmVTcGFjZSwgb3ZlcnJpZGUpIHtcbiAgX2NsYXNzQ2FsbENoZWNrKHRoaXMsIFRva0NvbnRleHQpO1xuXG4gIHRoaXMudG9rZW4gPSB0b2tlbjtcbiAgdGhpcy5pc0V4cHIgPSBpc0V4cHI7XG4gIHRoaXMucHJlc2VydmVTcGFjZSA9IHByZXNlcnZlU3BhY2U7XG4gIHRoaXMub3ZlcnJpZGUgPSBvdmVycmlkZTtcbn07XG5cbnZhciB0eXBlcyA9IHtcbiAgYl9zdGF0OiBuZXcgVG9rQ29udGV4dChcIntcIiwgZmFsc2UpLFxuICBiX2V4cHI6IG5ldyBUb2tDb250ZXh0KFwie1wiLCB0cnVlKSxcbiAgYl90bXBsOiBuZXcgVG9rQ29udGV4dChcIiR7XCIsIHRydWUpLFxuICBwX3N0YXQ6IG5ldyBUb2tDb250ZXh0KFwiKFwiLCBmYWxzZSksXG4gIHBfZXhwcjogbmV3IFRva0NvbnRleHQoXCIoXCIsIHRydWUpLFxuICBxX3RtcGw6IG5ldyBUb2tDb250ZXh0KFwiYFwiLCB0cnVlLCB0cnVlLCBmdW5jdGlvbiAocCkge1xuICAgIHJldHVybiBwLnJlYWRUbXBsVG9rZW4oKTtcbiAgfSksXG4gIGZfZXhwcjogbmV3IFRva0NvbnRleHQoXCJmdW5jdGlvblwiLCB0cnVlKVxufTtcblxuZXhwb3J0cy50eXBlcyA9IHR5cGVzO1xudmFyIHBwID0gUGFyc2VyLnByb3RvdHlwZTtcblxucHAuaW5pdGlhbENvbnRleHQgPSBmdW5jdGlvbiAoKSB7XG4gIHJldHVybiBbdHlwZXMuYl9zdGF0XTtcbn07XG5cbnBwLmJyYWNlSXNCbG9jayA9IGZ1bmN0aW9uIChwcmV2VHlwZSkge1xuICB2YXIgcGFyZW50ID0gdW5kZWZpbmVkO1xuICBpZiAocHJldlR5cGUgPT09IHR0LmNvbG9uICYmIChwYXJlbnQgPSB0aGlzLmN1ckNvbnRleHQoKSkudG9rZW4gPT0gXCJ7XCIpIHJldHVybiAhcGFyZW50LmlzRXhwcjtcbiAgaWYgKHByZXZUeXBlID09PSB0dC5fcmV0dXJuKSByZXR1cm4gbGluZUJyZWFrLnRlc3QodGhpcy5pbnB1dC5zbGljZSh0aGlzLmxhc3RUb2tFbmQsIHRoaXMuc3RhcnQpKTtcbiAgaWYgKHByZXZUeXBlID09PSB0dC5fZWxzZSB8fCBwcmV2VHlwZSA9PT0gdHQuc2VtaSB8fCBwcmV2VHlwZSA9PT0gdHQuZW9mKSByZXR1cm4gdHJ1ZTtcbiAgaWYgKHByZXZUeXBlID09IHR0LmJyYWNlTCkgcmV0dXJuIHRoaXMuY3VyQ29udGV4dCgpID09PSB0eXBlcy5iX3N0YXQ7XG4gIHJldHVybiAhdGhpcy5leHByQWxsb3dlZDtcbn07XG5cbnBwLnVwZGF0ZUNvbnRleHQgPSBmdW5jdGlvbiAocHJldlR5cGUpIHtcbiAgdmFyIHVwZGF0ZSA9IHVuZGVmaW5lZCxcbiAgICAgIHR5cGUgPSB0aGlzLnR5cGU7XG4gIGlmICh0eXBlLmtleXdvcmQgJiYgcHJldlR5cGUgPT0gdHQuZG90KSB0aGlzLmV4cHJBbGxvd2VkID0gZmFsc2U7ZWxzZSBpZiAodXBkYXRlID0gdHlwZS51cGRhdGVDb250ZXh0KSB1cGRhdGUuY2FsbCh0aGlzLCBwcmV2VHlwZSk7ZWxzZSB0aGlzLmV4cHJBbGxvd2VkID0gdHlwZS5iZWZvcmVFeHByO1xufTtcblxuLy8gVG9rZW4tc3BlY2lmaWMgY29udGV4dCB1cGRhdGUgY29kZVxuXG50dC5wYXJlblIudXBkYXRlQ29udGV4dCA9IHR0LmJyYWNlUi51cGRhdGVDb250ZXh0ID0gZnVuY3Rpb24gKCkge1xuICBpZiAodGhpcy5jb250ZXh0Lmxlbmd0aCA9PSAxKSB7XG4gICAgdGhpcy5leHByQWxsb3dlZCA9IHRydWU7XG4gICAgcmV0dXJuO1xuICB9XG4gIHZhciBvdXQgPSB0aGlzLmNvbnRleHQucG9wKCk7XG4gIGlmIChvdXQgPT09IHR5cGVzLmJfc3RhdCAmJiB0aGlzLmN1ckNvbnRleHQoKSA9PT0gdHlwZXMuZl9leHByKSB7XG4gICAgdGhpcy5jb250ZXh0LnBvcCgpO1xuICAgIHRoaXMuZXhwckFsbG93ZWQgPSBmYWxzZTtcbiAgfSBlbHNlIGlmIChvdXQgPT09IHR5cGVzLmJfdG1wbCkge1xuICAgIHRoaXMuZXhwckFsbG93ZWQgPSB0cnVlO1xuICB9IGVsc2Uge1xuICAgIHRoaXMuZXhwckFsbG93ZWQgPSAhb3V0LmlzRXhwcjtcbiAgfVxufTtcblxudHQuYnJhY2VMLnVwZGF0ZUNvbnRleHQgPSBmdW5jdGlvbiAocHJldlR5cGUpIHtcbiAgdGhpcy5jb250ZXh0LnB1c2godGhpcy5icmFjZUlzQmxvY2socHJldlR5cGUpID8gdHlwZXMuYl9zdGF0IDogdHlwZXMuYl9leHByKTtcbiAgdGhpcy5leHByQWxsb3dlZCA9IHRydWU7XG59O1xuXG50dC5kb2xsYXJCcmFjZUwudXBkYXRlQ29udGV4dCA9IGZ1bmN0aW9uICgpIHtcbiAgdGhpcy5jb250ZXh0LnB1c2godHlwZXMuYl90bXBsKTtcbiAgdGhpcy5leHByQWxsb3dlZCA9IHRydWU7XG59O1xuXG50dC5wYXJlbkwudXBkYXRlQ29udGV4dCA9IGZ1bmN0aW9uIChwcmV2VHlwZSkge1xuICB2YXIgc3RhdGVtZW50UGFyZW5zID0gcHJldlR5cGUgPT09IHR0Ll9pZiB8fCBwcmV2VHlwZSA9PT0gdHQuX2ZvciB8fCBwcmV2VHlwZSA9PT0gdHQuX3dpdGggfHwgcHJldlR5cGUgPT09IHR0Ll93aGlsZTtcbiAgdGhpcy5jb250ZXh0LnB1c2goc3RhdGVtZW50UGFyZW5zID8gdHlwZXMucF9zdGF0IDogdHlwZXMucF9leHByKTtcbiAgdGhpcy5leHByQWxsb3dlZCA9IHRydWU7XG59O1xuXG50dC5pbmNEZWMudXBkYXRlQ29udGV4dCA9IGZ1bmN0aW9uICgpIHt9O1xuXG50dC5fZnVuY3Rpb24udXBkYXRlQ29udGV4dCA9IGZ1bmN0aW9uICgpIHtcbiAgaWYgKHRoaXMuY3VyQ29udGV4dCgpICE9PSB0eXBlcy5iX3N0YXQpIHRoaXMuY29udGV4dC5wdXNoKHR5cGVzLmZfZXhwcik7XG4gIHRoaXMuZXhwckFsbG93ZWQgPSBmYWxzZTtcbn07XG5cbnR0LmJhY2tRdW90ZS51cGRhdGVDb250ZXh0ID0gZnVuY3Rpb24gKCkge1xuICBpZiAodGhpcy5jdXJDb250ZXh0KCkgPT09IHR5cGVzLnFfdG1wbCkgdGhpcy5jb250ZXh0LnBvcCgpO2Vsc2UgdGhpcy5jb250ZXh0LnB1c2godHlwZXMucV90bXBsKTtcbiAgdGhpcy5leHByQWxsb3dlZCA9IGZhbHNlO1xufTtcblxuLy8gdG9rRXhwckFsbG93ZWQgc3RheXMgdW5jaGFuZ2VkXG5cbn0se1wiLi9zdGF0ZVwiOjEzLFwiLi90b2tlbnR5cGVcIjoxNyxcIi4vd2hpdGVzcGFjZVwiOjE5fV0sMTY6W2Z1bmN0aW9uKF9kZXJlcV8sbW9kdWxlLGV4cG9ydHMpe1xuXCJ1c2Ugc3RyaWN0XCI7XG5cbnZhciBfY2xhc3NDYWxsQ2hlY2sgPSBmdW5jdGlvbiAoaW5zdGFuY2UsIENvbnN0cnVjdG9yKSB7IGlmICghKGluc3RhbmNlIGluc3RhbmNlb2YgQ29uc3RydWN0b3IpKSB7IHRocm93IG5ldyBUeXBlRXJyb3IoXCJDYW5ub3QgY2FsbCBhIGNsYXNzIGFzIGEgZnVuY3Rpb25cIik7IH0gfTtcblxuZXhwb3J0cy5fX2VzTW9kdWxlID0gdHJ1ZTtcblxudmFyIF9pZGVudGlmaWVyID0gX2RlcmVxXyhcIi4vaWRlbnRpZmllclwiKTtcblxudmFyIGlzSWRlbnRpZmllclN0YXJ0ID0gX2lkZW50aWZpZXIuaXNJZGVudGlmaWVyU3RhcnQ7XG52YXIgaXNJZGVudGlmaWVyQ2hhciA9IF9pZGVudGlmaWVyLmlzSWRlbnRpZmllckNoYXI7XG5cbnZhciBfdG9rZW50eXBlID0gX2RlcmVxXyhcIi4vdG9rZW50eXBlXCIpO1xuXG52YXIgdHQgPSBfdG9rZW50eXBlLnR5cGVzO1xudmFyIGtleXdvcmRUeXBlcyA9IF90b2tlbnR5cGUua2V5d29yZHM7XG5cbnZhciBQYXJzZXIgPSBfZGVyZXFfKFwiLi9zdGF0ZVwiKS5QYXJzZXI7XG5cbnZhciBTb3VyY2VMb2NhdGlvbiA9IF9kZXJlcV8oXCIuL2xvY2F0aW9uXCIpLlNvdXJjZUxvY2F0aW9uO1xuXG52YXIgX3doaXRlc3BhY2UgPSBfZGVyZXFfKFwiLi93aGl0ZXNwYWNlXCIpO1xuXG52YXIgbGluZUJyZWFrID0gX3doaXRlc3BhY2UubGluZUJyZWFrO1xudmFyIGxpbmVCcmVha0cgPSBfd2hpdGVzcGFjZS5saW5lQnJlYWtHO1xudmFyIGlzTmV3TGluZSA9IF93aGl0ZXNwYWNlLmlzTmV3TGluZTtcbnZhciBub25BU0NJSXdoaXRlc3BhY2UgPSBfd2hpdGVzcGFjZS5ub25BU0NJSXdoaXRlc3BhY2U7XG5cbi8vIE9iamVjdCB0eXBlIHVzZWQgdG8gcmVwcmVzZW50IHRva2Vucy4gTm90ZSB0aGF0IG5vcm1hbGx5LCB0b2tlbnNcbi8vIHNpbXBseSBleGlzdCBhcyBwcm9wZXJ0aWVzIG9uIHRoZSBwYXJzZXIgb2JqZWN0LiBUaGlzIGlzIG9ubHlcbi8vIHVzZWQgZm9yIHRoZSBvblRva2VuIGNhbGxiYWNrIGFuZCB0aGUgZXh0ZXJuYWwgdG9rZW5pemVyLlxuXG52YXIgVG9rZW4gPSBleHBvcnRzLlRva2VuID0gZnVuY3Rpb24gVG9rZW4ocCkge1xuICBfY2xhc3NDYWxsQ2hlY2sodGhpcywgVG9rZW4pO1xuXG4gIHRoaXMudHlwZSA9IHAudHlwZTtcbiAgdGhpcy52YWx1ZSA9IHAudmFsdWU7XG4gIHRoaXMuc3RhcnQgPSBwLnN0YXJ0O1xuICB0aGlzLmVuZCA9IHAuZW5kO1xuICBpZiAocC5vcHRpb25zLmxvY2F0aW9ucykgdGhpcy5sb2MgPSBuZXcgU291cmNlTG9jYXRpb24ocCwgcC5zdGFydExvYywgcC5lbmRMb2MpO1xuICBpZiAocC5vcHRpb25zLnJhbmdlcykgdGhpcy5yYW5nZSA9IFtwLnN0YXJ0LCBwLmVuZF07XG59O1xuXG4vLyAjIyBUb2tlbml6ZXJcblxudmFyIHBwID0gUGFyc2VyLnByb3RvdHlwZTtcblxuLy8gQXJlIHdlIHJ1bm5pbmcgdW5kZXIgUmhpbm8/XG52YXIgaXNSaGlubyA9IHR5cGVvZiBQYWNrYWdlcyAhPT0gXCJ1bmRlZmluZWRcIjtcblxuLy8gTW92ZSB0byB0aGUgbmV4dCB0b2tlblxuXG5wcC5uZXh0ID0gZnVuY3Rpb24gKCkge1xuICBpZiAodGhpcy5vcHRpb25zLm9uVG9rZW4pIHRoaXMub3B0aW9ucy5vblRva2VuKG5ldyBUb2tlbih0aGlzKSk7XG5cbiAgdGhpcy5sYXN0VG9rRW5kID0gdGhpcy5lbmQ7XG4gIHRoaXMubGFzdFRva1N0YXJ0ID0gdGhpcy5zdGFydDtcbiAgdGhpcy5sYXN0VG9rRW5kTG9jID0gdGhpcy5lbmRMb2M7XG4gIHRoaXMubGFzdFRva1N0YXJ0TG9jID0gdGhpcy5zdGFydExvYztcbiAgdGhpcy5uZXh0VG9rZW4oKTtcbn07XG5cbnBwLmdldFRva2VuID0gZnVuY3Rpb24gKCkge1xuICB0aGlzLm5leHQoKTtcbiAgcmV0dXJuIG5ldyBUb2tlbih0aGlzKTtcbn07XG5cbi8vIElmIHdlJ3JlIGluIGFuIEVTNiBlbnZpcm9ubWVudCwgbWFrZSBwYXJzZXJzIGl0ZXJhYmxlXG5pZiAodHlwZW9mIFN5bWJvbCAhPT0gXCJ1bmRlZmluZWRcIikgcHBbU3ltYm9sLml0ZXJhdG9yXSA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIHNlbGYgPSB0aGlzO1xuICByZXR1cm4geyBuZXh0OiBmdW5jdGlvbiBuZXh0KCkge1xuICAgICAgdmFyIHRva2VuID0gc2VsZi5nZXRUb2tlbigpO1xuICAgICAgcmV0dXJuIHtcbiAgICAgICAgZG9uZTogdG9rZW4udHlwZSA9PT0gdHQuZW9mLFxuICAgICAgICB2YWx1ZTogdG9rZW5cbiAgICAgIH07XG4gICAgfSB9O1xufTtcblxuLy8gVG9nZ2xlIHN0cmljdCBtb2RlLiBSZS1yZWFkcyB0aGUgbmV4dCBudW1iZXIgb3Igc3RyaW5nIHRvIHBsZWFzZVxuLy8gcGVkYW50aWMgdGVzdHMgKGBcInVzZSBzdHJpY3RcIjsgMDEwO2Agc2hvdWxkIGZhaWwpLlxuXG5wcC5zZXRTdHJpY3QgPSBmdW5jdGlvbiAoc3RyaWN0KSB7XG4gIHRoaXMuc3RyaWN0ID0gc3RyaWN0O1xuICBpZiAodGhpcy50eXBlICE9PSB0dC5udW0gJiYgdGhpcy50eXBlICE9PSB0dC5zdHJpbmcpIHJldHVybjtcbiAgdGhpcy5wb3MgPSB0aGlzLnN0YXJ0O1xuICBpZiAodGhpcy5vcHRpb25zLmxvY2F0aW9ucykge1xuICAgIHdoaWxlICh0aGlzLnBvcyA8IHRoaXMubGluZVN0YXJ0KSB7XG4gICAgICB0aGlzLmxpbmVTdGFydCA9IHRoaXMuaW5wdXQubGFzdEluZGV4T2YoXCJcXG5cIiwgdGhpcy5saW5lU3RhcnQgLSAyKSArIDE7XG4gICAgICAtLXRoaXMuY3VyTGluZTtcbiAgICB9XG4gIH1cbiAgdGhpcy5uZXh0VG9rZW4oKTtcbn07XG5cbnBwLmN1ckNvbnRleHQgPSBmdW5jdGlvbiAoKSB7XG4gIHJldHVybiB0aGlzLmNvbnRleHRbdGhpcy5jb250ZXh0Lmxlbmd0aCAtIDFdO1xufTtcblxuLy8gUmVhZCBhIHNpbmdsZSB0b2tlbiwgdXBkYXRpbmcgdGhlIHBhcnNlciBvYmplY3QncyB0b2tlbi1yZWxhdGVkXG4vLyBwcm9wZXJ0aWVzLlxuXG5wcC5uZXh0VG9rZW4gPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBjdXJDb250ZXh0ID0gdGhpcy5jdXJDb250ZXh0KCk7XG4gIGlmICghY3VyQ29udGV4dCB8fCAhY3VyQ29udGV4dC5wcmVzZXJ2ZVNwYWNlKSB0aGlzLnNraXBTcGFjZSgpO1xuXG4gIHRoaXMuc3RhcnQgPSB0aGlzLnBvcztcbiAgaWYgKHRoaXMub3B0aW9ucy5sb2NhdGlvbnMpIHRoaXMuc3RhcnRMb2MgPSB0aGlzLmN1clBvc2l0aW9uKCk7XG4gIGlmICh0aGlzLnBvcyA+PSB0aGlzLmlucHV0Lmxlbmd0aCkgcmV0dXJuIHRoaXMuZmluaXNoVG9rZW4odHQuZW9mKTtcblxuICBpZiAoY3VyQ29udGV4dC5vdmVycmlkZSkgcmV0dXJuIGN1ckNvbnRleHQub3ZlcnJpZGUodGhpcyk7ZWxzZSB0aGlzLnJlYWRUb2tlbih0aGlzLmZ1bGxDaGFyQ29kZUF0UG9zKCkpO1xufTtcblxucHAucmVhZFRva2VuID0gZnVuY3Rpb24gKGNvZGUpIHtcbiAgLy8gSWRlbnRpZmllciBvciBrZXl3b3JkLiAnXFx1WFhYWCcgc2VxdWVuY2VzIGFyZSBhbGxvd2VkIGluXG4gIC8vIGlkZW50aWZpZXJzLCBzbyAnXFwnIGFsc28gZGlzcGF0Y2hlcyB0byB0aGF0LlxuICBpZiAoaXNJZGVudGlmaWVyU3RhcnQoY29kZSwgdGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYpIHx8IGNvZGUgPT09IDkyIC8qICdcXCcgKi8pIHJldHVybiB0aGlzLnJlYWRXb3JkKCk7XG5cbiAgcmV0dXJuIHRoaXMuZ2V0VG9rZW5Gcm9tQ29kZShjb2RlKTtcbn07XG5cbnBwLmZ1bGxDaGFyQ29kZUF0UG9zID0gZnVuY3Rpb24gKCkge1xuICB2YXIgY29kZSA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyk7XG4gIGlmIChjb2RlIDw9IDU1Mjk1IHx8IGNvZGUgPj0gNTczNDQpIHJldHVybiBjb2RlO1xuICB2YXIgbmV4dCA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIDEpO1xuICByZXR1cm4gKGNvZGUgPDwgMTApICsgbmV4dCAtIDU2NjEzODg4O1xufTtcblxucHAuc2tpcEJsb2NrQ29tbWVudCA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIHN0YXJ0TG9jID0gdGhpcy5vcHRpb25zLm9uQ29tbWVudCAmJiB0aGlzLm9wdGlvbnMubG9jYXRpb25zICYmIHRoaXMuY3VyUG9zaXRpb24oKTtcbiAgdmFyIHN0YXJ0ID0gdGhpcy5wb3MsXG4gICAgICBlbmQgPSB0aGlzLmlucHV0LmluZGV4T2YoXCIqL1wiLCB0aGlzLnBvcyArPSAyKTtcbiAgaWYgKGVuZCA9PT0gLTEpIHRoaXMucmFpc2UodGhpcy5wb3MgLSAyLCBcIlVudGVybWluYXRlZCBjb21tZW50XCIpO1xuICB0aGlzLnBvcyA9IGVuZCArIDI7XG4gIGlmICh0aGlzLm9wdGlvbnMubG9jYXRpb25zKSB7XG4gICAgbGluZUJyZWFrRy5sYXN0SW5kZXggPSBzdGFydDtcbiAgICB2YXIgbWF0Y2ggPSB1bmRlZmluZWQ7XG4gICAgd2hpbGUgKChtYXRjaCA9IGxpbmVCcmVha0cuZXhlYyh0aGlzLmlucHV0KSkgJiYgbWF0Y2guaW5kZXggPCB0aGlzLnBvcykge1xuICAgICAgKyt0aGlzLmN1ckxpbmU7XG4gICAgICB0aGlzLmxpbmVTdGFydCA9IG1hdGNoLmluZGV4ICsgbWF0Y2hbMF0ubGVuZ3RoO1xuICAgIH1cbiAgfVxuICBpZiAodGhpcy5vcHRpb25zLm9uQ29tbWVudCkgdGhpcy5vcHRpb25zLm9uQ29tbWVudCh0cnVlLCB0aGlzLmlucHV0LnNsaWNlKHN0YXJ0ICsgMiwgZW5kKSwgc3RhcnQsIHRoaXMucG9zLCBzdGFydExvYywgdGhpcy5vcHRpb25zLmxvY2F0aW9ucyAmJiB0aGlzLmN1clBvc2l0aW9uKCkpO1xufTtcblxucHAuc2tpcExpbmVDb21tZW50ID0gZnVuY3Rpb24gKHN0YXJ0U2tpcCkge1xuICB2YXIgc3RhcnQgPSB0aGlzLnBvcztcbiAgdmFyIHN0YXJ0TG9jID0gdGhpcy5vcHRpb25zLm9uQ29tbWVudCAmJiB0aGlzLm9wdGlvbnMubG9jYXRpb25zICYmIHRoaXMuY3VyUG9zaXRpb24oKTtcbiAgdmFyIGNoID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICs9IHN0YXJ0U2tpcCk7XG4gIHdoaWxlICh0aGlzLnBvcyA8IHRoaXMuaW5wdXQubGVuZ3RoICYmIGNoICE9PSAxMCAmJiBjaCAhPT0gMTMgJiYgY2ggIT09IDgyMzIgJiYgY2ggIT09IDgyMzMpIHtcbiAgICArK3RoaXMucG9zO1xuICAgIGNoID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zKTtcbiAgfVxuICBpZiAodGhpcy5vcHRpb25zLm9uQ29tbWVudCkgdGhpcy5vcHRpb25zLm9uQ29tbWVudChmYWxzZSwgdGhpcy5pbnB1dC5zbGljZShzdGFydCArIHN0YXJ0U2tpcCwgdGhpcy5wb3MpLCBzdGFydCwgdGhpcy5wb3MsIHN0YXJ0TG9jLCB0aGlzLm9wdGlvbnMubG9jYXRpb25zICYmIHRoaXMuY3VyUG9zaXRpb24oKSk7XG59O1xuXG4vLyBDYWxsZWQgYXQgdGhlIHN0YXJ0IG9mIHRoZSBwYXJzZSBhbmQgYWZ0ZXIgZXZlcnkgdG9rZW4uIFNraXBzXG4vLyB3aGl0ZXNwYWNlIGFuZCBjb21tZW50cywgYW5kLlxuXG5wcC5za2lwU3BhY2UgPSBmdW5jdGlvbiAoKSB7XG4gIHdoaWxlICh0aGlzLnBvcyA8IHRoaXMuaW5wdXQubGVuZ3RoKSB7XG4gICAgdmFyIGNoID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zKTtcbiAgICBpZiAoY2ggPT09IDMyKSB7XG4gICAgICAvLyAnICdcbiAgICAgICsrdGhpcy5wb3M7XG4gICAgfSBlbHNlIGlmIChjaCA9PT0gMTMpIHtcbiAgICAgICsrdGhpcy5wb3M7XG4gICAgICB2YXIgbmV4dCA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyk7XG4gICAgICBpZiAobmV4dCA9PT0gMTApIHtcbiAgICAgICAgKyt0aGlzLnBvcztcbiAgICAgIH1cbiAgICAgIGlmICh0aGlzLm9wdGlvbnMubG9jYXRpb25zKSB7XG4gICAgICAgICsrdGhpcy5jdXJMaW5lO1xuICAgICAgICB0aGlzLmxpbmVTdGFydCA9IHRoaXMucG9zO1xuICAgICAgfVxuICAgIH0gZWxzZSBpZiAoY2ggPT09IDEwIHx8IGNoID09PSA4MjMyIHx8IGNoID09PSA4MjMzKSB7XG4gICAgICArK3RoaXMucG9zO1xuICAgICAgaWYgKHRoaXMub3B0aW9ucy5sb2NhdGlvbnMpIHtcbiAgICAgICAgKyt0aGlzLmN1ckxpbmU7XG4gICAgICAgIHRoaXMubGluZVN0YXJ0ID0gdGhpcy5wb3M7XG4gICAgICB9XG4gICAgfSBlbHNlIGlmIChjaCA+IDggJiYgY2ggPCAxNCkge1xuICAgICAgKyt0aGlzLnBvcztcbiAgICB9IGVsc2UgaWYgKGNoID09PSA0Nykge1xuICAgICAgLy8gJy8nXG4gICAgICB2YXIgbmV4dCA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIDEpO1xuICAgICAgaWYgKG5leHQgPT09IDQyKSB7XG4gICAgICAgIC8vICcqJ1xuICAgICAgICB0aGlzLnNraXBCbG9ja0NvbW1lbnQoKTtcbiAgICAgIH0gZWxzZSBpZiAobmV4dCA9PT0gNDcpIHtcbiAgICAgICAgLy8gJy8nXG4gICAgICAgIHRoaXMuc2tpcExpbmVDb21tZW50KDIpO1xuICAgICAgfSBlbHNlIGJyZWFrO1xuICAgIH0gZWxzZSBpZiAoY2ggPT09IDE2MCkge1xuICAgICAgLy8gJ1xceGEwJ1xuICAgICAgKyt0aGlzLnBvcztcbiAgICB9IGVsc2UgaWYgKGNoID49IDU3NjAgJiYgbm9uQVNDSUl3aGl0ZXNwYWNlLnRlc3QoU3RyaW5nLmZyb21DaGFyQ29kZShjaCkpKSB7XG4gICAgICArK3RoaXMucG9zO1xuICAgIH0gZWxzZSB7XG4gICAgICBicmVhaztcbiAgICB9XG4gIH1cbn07XG5cbi8vIENhbGxlZCBhdCB0aGUgZW5kIG9mIGV2ZXJ5IHRva2VuLiBTZXRzIGBlbmRgLCBgdmFsYCwgYW5kXG4vLyBtYWludGFpbnMgYGNvbnRleHRgIGFuZCBgZXhwckFsbG93ZWRgLCBhbmQgc2tpcHMgdGhlIHNwYWNlIGFmdGVyXG4vLyB0aGUgdG9rZW4sIHNvIHRoYXQgdGhlIG5leHQgb25lJ3MgYHN0YXJ0YCB3aWxsIHBvaW50IGF0IHRoZVxuLy8gcmlnaHQgcG9zaXRpb24uXG5cbnBwLmZpbmlzaFRva2VuID0gZnVuY3Rpb24gKHR5cGUsIHZhbCkge1xuICB0aGlzLmVuZCA9IHRoaXMucG9zO1xuICBpZiAodGhpcy5vcHRpb25zLmxvY2F0aW9ucykgdGhpcy5lbmRMb2MgPSB0aGlzLmN1clBvc2l0aW9uKCk7XG4gIHZhciBwcmV2VHlwZSA9IHRoaXMudHlwZTtcbiAgdGhpcy50eXBlID0gdHlwZTtcbiAgdGhpcy52YWx1ZSA9IHZhbDtcblxuICB0aGlzLnVwZGF0ZUNvbnRleHQocHJldlR5cGUpO1xufTtcblxuLy8gIyMjIFRva2VuIHJlYWRpbmdcblxuLy8gVGhpcyBpcyB0aGUgZnVuY3Rpb24gdGhhdCBpcyBjYWxsZWQgdG8gZmV0Y2ggdGhlIG5leHQgdG9rZW4uIEl0XG4vLyBpcyBzb21ld2hhdCBvYnNjdXJlLCBiZWNhdXNlIGl0IHdvcmtzIGluIGNoYXJhY3RlciBjb2RlcyByYXRoZXJcbi8vIHRoYW4gY2hhcmFjdGVycywgYW5kIGJlY2F1c2Ugb3BlcmF0b3IgcGFyc2luZyBoYXMgYmVlbiBpbmxpbmVkXG4vLyBpbnRvIGl0LlxuLy9cbi8vIEFsbCBpbiB0aGUgbmFtZSBvZiBzcGVlZC5cbi8vXG5wcC5yZWFkVG9rZW5fZG90ID0gZnVuY3Rpb24gKCkge1xuICB2YXIgbmV4dCA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIDEpO1xuICBpZiAobmV4dCA+PSA0OCAmJiBuZXh0IDw9IDU3KSByZXR1cm4gdGhpcy5yZWFkTnVtYmVyKHRydWUpO1xuICB2YXIgbmV4dDIgPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAyKTtcbiAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2ICYmIG5leHQgPT09IDQ2ICYmIG5leHQyID09PSA0Nikge1xuICAgIC8vIDQ2ID0gZG90ICcuJ1xuICAgIHRoaXMucG9zICs9IDM7XG4gICAgcmV0dXJuIHRoaXMuZmluaXNoVG9rZW4odHQuZWxsaXBzaXMpO1xuICB9IGVsc2Uge1xuICAgICsrdGhpcy5wb3M7XG4gICAgcmV0dXJuIHRoaXMuZmluaXNoVG9rZW4odHQuZG90KTtcbiAgfVxufTtcblxucHAucmVhZFRva2VuX3NsYXNoID0gZnVuY3Rpb24gKCkge1xuICAvLyAnLydcbiAgdmFyIG5leHQgPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAxKTtcbiAgaWYgKHRoaXMuZXhwckFsbG93ZWQpIHtcbiAgICArK3RoaXMucG9zO3JldHVybiB0aGlzLnJlYWRSZWdleHAoKTtcbiAgfVxuICBpZiAobmV4dCA9PT0gNjEpIHJldHVybiB0aGlzLmZpbmlzaE9wKHR0LmFzc2lnbiwgMik7XG4gIHJldHVybiB0aGlzLmZpbmlzaE9wKHR0LnNsYXNoLCAxKTtcbn07XG5cbnBwLnJlYWRUb2tlbl9tdWx0X21vZHVsbyA9IGZ1bmN0aW9uIChjb2RlKSB7XG4gIC8vICclKidcbiAgdmFyIG5leHQgPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAxKTtcbiAgaWYgKG5leHQgPT09IDYxKSByZXR1cm4gdGhpcy5maW5pc2hPcCh0dC5hc3NpZ24sIDIpO1xuICByZXR1cm4gdGhpcy5maW5pc2hPcChjb2RlID09PSA0MiA/IHR0LnN0YXIgOiB0dC5tb2R1bG8sIDEpO1xufTtcblxucHAucmVhZFRva2VuX3BpcGVfYW1wID0gZnVuY3Rpb24gKGNvZGUpIHtcbiAgLy8gJ3wmJ1xuICB2YXIgbmV4dCA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIDEpO1xuICBpZiAobmV4dCA9PT0gY29kZSkgcmV0dXJuIHRoaXMuZmluaXNoT3AoY29kZSA9PT0gMTI0ID8gdHQubG9naWNhbE9SIDogdHQubG9naWNhbEFORCwgMik7XG4gIGlmIChuZXh0ID09PSA2MSkgcmV0dXJuIHRoaXMuZmluaXNoT3AodHQuYXNzaWduLCAyKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoT3AoY29kZSA9PT0gMTI0ID8gdHQuYml0d2lzZU9SIDogdHQuYml0d2lzZUFORCwgMSk7XG59O1xuXG5wcC5yZWFkVG9rZW5fY2FyZXQgPSBmdW5jdGlvbiAoKSB7XG4gIC8vICdeJ1xuICB2YXIgbmV4dCA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIDEpO1xuICBpZiAobmV4dCA9PT0gNjEpIHJldHVybiB0aGlzLmZpbmlzaE9wKHR0LmFzc2lnbiwgMik7XG4gIHJldHVybiB0aGlzLmZpbmlzaE9wKHR0LmJpdHdpc2VYT1IsIDEpO1xufTtcblxucHAucmVhZFRva2VuX3BsdXNfbWluID0gZnVuY3Rpb24gKGNvZGUpIHtcbiAgLy8gJystJ1xuICB2YXIgbmV4dCA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIDEpO1xuICBpZiAobmV4dCA9PT0gY29kZSkge1xuICAgIGlmIChuZXh0ID09IDQ1ICYmIHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIDIpID09IDYyICYmIGxpbmVCcmVhay50ZXN0KHRoaXMuaW5wdXQuc2xpY2UodGhpcy5sYXN0VG9rRW5kLCB0aGlzLnBvcykpKSB7XG4gICAgICAvLyBBIGAtLT5gIGxpbmUgY29tbWVudFxuICAgICAgdGhpcy5za2lwTGluZUNvbW1lbnQoMyk7XG4gICAgICB0aGlzLnNraXBTcGFjZSgpO1xuICAgICAgcmV0dXJuIHRoaXMubmV4dFRva2VuKCk7XG4gICAgfVxuICAgIHJldHVybiB0aGlzLmZpbmlzaE9wKHR0LmluY0RlYywgMik7XG4gIH1cbiAgaWYgKG5leHQgPT09IDYxKSByZXR1cm4gdGhpcy5maW5pc2hPcCh0dC5hc3NpZ24sIDIpO1xuICByZXR1cm4gdGhpcy5maW5pc2hPcCh0dC5wbHVzTWluLCAxKTtcbn07XG5cbnBwLnJlYWRUb2tlbl9sdF9ndCA9IGZ1bmN0aW9uIChjb2RlKSB7XG4gIC8vICc8PidcbiAgdmFyIG5leHQgPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAxKTtcbiAgdmFyIHNpemUgPSAxO1xuICBpZiAobmV4dCA9PT0gY29kZSkge1xuICAgIHNpemUgPSBjb2RlID09PSA2MiAmJiB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAyKSA9PT0gNjIgPyAzIDogMjtcbiAgICBpZiAodGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgc2l6ZSkgPT09IDYxKSByZXR1cm4gdGhpcy5maW5pc2hPcCh0dC5hc3NpZ24sIHNpemUgKyAxKTtcbiAgICByZXR1cm4gdGhpcy5maW5pc2hPcCh0dC5iaXRTaGlmdCwgc2l6ZSk7XG4gIH1cbiAgaWYgKG5leHQgPT0gMzMgJiYgY29kZSA9PSA2MCAmJiB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAyKSA9PSA0NSAmJiB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAzKSA9PSA0NSkge1xuICAgIGlmICh0aGlzLmluTW9kdWxlKSB0aGlzLnVuZXhwZWN0ZWQoKTtcbiAgICAvLyBgPCEtLWAsIGFuIFhNTC1zdHlsZSBjb21tZW50IHRoYXQgc2hvdWxkIGJlIGludGVycHJldGVkIGFzIGEgbGluZSBjb21tZW50XG4gICAgdGhpcy5za2lwTGluZUNvbW1lbnQoNCk7XG4gICAgdGhpcy5za2lwU3BhY2UoKTtcbiAgICByZXR1cm4gdGhpcy5uZXh0VG9rZW4oKTtcbiAgfVxuICBpZiAobmV4dCA9PT0gNjEpIHNpemUgPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAyKSA9PT0gNjEgPyAzIDogMjtcbiAgcmV0dXJuIHRoaXMuZmluaXNoT3AodHQucmVsYXRpb25hbCwgc2l6ZSk7XG59O1xuXG5wcC5yZWFkVG9rZW5fZXFfZXhjbCA9IGZ1bmN0aW9uIChjb2RlKSB7XG4gIC8vICc9ISdcbiAgdmFyIG5leHQgPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAxKTtcbiAgaWYgKG5leHQgPT09IDYxKSByZXR1cm4gdGhpcy5maW5pc2hPcCh0dC5lcXVhbGl0eSwgdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMikgPT09IDYxID8gMyA6IDIpO1xuICBpZiAoY29kZSA9PT0gNjEgJiYgbmV4dCA9PT0gNjIgJiYgdGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYpIHtcbiAgICAvLyAnPT4nXG4gICAgdGhpcy5wb3MgKz0gMjtcbiAgICByZXR1cm4gdGhpcy5maW5pc2hUb2tlbih0dC5hcnJvdyk7XG4gIH1cbiAgcmV0dXJuIHRoaXMuZmluaXNoT3AoY29kZSA9PT0gNjEgPyB0dC5lcSA6IHR0LnByZWZpeCwgMSk7XG59O1xuXG5wcC5nZXRUb2tlbkZyb21Db2RlID0gZnVuY3Rpb24gKGNvZGUpIHtcbiAgc3dpdGNoIChjb2RlKSB7XG4gICAgLy8gVGhlIGludGVycHJldGF0aW9uIG9mIGEgZG90IGRlcGVuZHMgb24gd2hldGhlciBpdCBpcyBmb2xsb3dlZFxuICAgIC8vIGJ5IGEgZGlnaXQgb3IgYW5vdGhlciB0d28gZG90cy5cbiAgICBjYXNlIDQ2OlxuICAgICAgLy8gJy4nXG4gICAgICByZXR1cm4gdGhpcy5yZWFkVG9rZW5fZG90KCk7XG5cbiAgICAvLyBQdW5jdHVhdGlvbiB0b2tlbnMuXG4gICAgY2FzZSA0MDpcbiAgICAgICsrdGhpcy5wb3M7cmV0dXJuIHRoaXMuZmluaXNoVG9rZW4odHQucGFyZW5MKTtcbiAgICBjYXNlIDQxOlxuICAgICAgKyt0aGlzLnBvcztyZXR1cm4gdGhpcy5maW5pc2hUb2tlbih0dC5wYXJlblIpO1xuICAgIGNhc2UgNTk6XG4gICAgICArK3RoaXMucG9zO3JldHVybiB0aGlzLmZpbmlzaFRva2VuKHR0LnNlbWkpO1xuICAgIGNhc2UgNDQ6XG4gICAgICArK3RoaXMucG9zO3JldHVybiB0aGlzLmZpbmlzaFRva2VuKHR0LmNvbW1hKTtcbiAgICBjYXNlIDkxOlxuICAgICAgKyt0aGlzLnBvcztyZXR1cm4gdGhpcy5maW5pc2hUb2tlbih0dC5icmFja2V0TCk7XG4gICAgY2FzZSA5MzpcbiAgICAgICsrdGhpcy5wb3M7cmV0dXJuIHRoaXMuZmluaXNoVG9rZW4odHQuYnJhY2tldFIpO1xuICAgIGNhc2UgMTIzOlxuICAgICAgKyt0aGlzLnBvcztyZXR1cm4gdGhpcy5maW5pc2hUb2tlbih0dC5icmFjZUwpO1xuICAgIGNhc2UgMTI1OlxuICAgICAgKyt0aGlzLnBvcztyZXR1cm4gdGhpcy5maW5pc2hUb2tlbih0dC5icmFjZVIpO1xuICAgIGNhc2UgNTg6XG4gICAgICArK3RoaXMucG9zO3JldHVybiB0aGlzLmZpbmlzaFRva2VuKHR0LmNvbG9uKTtcbiAgICBjYXNlIDYzOlxuICAgICAgKyt0aGlzLnBvcztyZXR1cm4gdGhpcy5maW5pc2hUb2tlbih0dC5xdWVzdGlvbik7XG5cbiAgICBjYXNlIDk2OlxuICAgICAgLy8gJ2AnXG4gICAgICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uIDwgNikgYnJlYWs7XG4gICAgICArK3RoaXMucG9zO1xuICAgICAgcmV0dXJuIHRoaXMuZmluaXNoVG9rZW4odHQuYmFja1F1b3RlKTtcblxuICAgIGNhc2UgNDg6XG4gICAgICAvLyAnMCdcbiAgICAgIHZhciBuZXh0ID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMSk7XG4gICAgICBpZiAobmV4dCA9PT0gMTIwIHx8IG5leHQgPT09IDg4KSByZXR1cm4gdGhpcy5yZWFkUmFkaXhOdW1iZXIoMTYpOyAvLyAnMHgnLCAnMFgnIC0gaGV4IG51bWJlclxuICAgICAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KSB7XG4gICAgICAgIGlmIChuZXh0ID09PSAxMTEgfHwgbmV4dCA9PT0gNzkpIHJldHVybiB0aGlzLnJlYWRSYWRpeE51bWJlcig4KTsgLy8gJzBvJywgJzBPJyAtIG9jdGFsIG51bWJlclxuICAgICAgICBpZiAobmV4dCA9PT0gOTggfHwgbmV4dCA9PT0gNjYpIHJldHVybiB0aGlzLnJlYWRSYWRpeE51bWJlcigyKTsgLy8gJzBiJywgJzBCJyAtIGJpbmFyeSBudW1iZXJcbiAgICAgIH1cbiAgICAvLyBBbnl0aGluZyBlbHNlIGJlZ2lubmluZyB3aXRoIGEgZGlnaXQgaXMgYW4gaW50ZWdlciwgb2N0YWxcbiAgICAvLyBudW1iZXIsIG9yIGZsb2F0LlxuICAgIGNhc2UgNDk6Y2FzZSA1MDpjYXNlIDUxOmNhc2UgNTI6Y2FzZSA1MzpjYXNlIDU0OmNhc2UgNTU6Y2FzZSA1NjpjYXNlIDU3OlxuICAgICAgLy8gMS05XG4gICAgICByZXR1cm4gdGhpcy5yZWFkTnVtYmVyKGZhbHNlKTtcblxuICAgIC8vIFF1b3RlcyBwcm9kdWNlIHN0cmluZ3MuXG4gICAgY2FzZSAzNDpjYXNlIDM5OlxuICAgICAgLy8gJ1wiJywgXCInXCJcbiAgICAgIHJldHVybiB0aGlzLnJlYWRTdHJpbmcoY29kZSk7XG5cbiAgICAvLyBPcGVyYXRvcnMgYXJlIHBhcnNlZCBpbmxpbmUgaW4gdGlueSBzdGF0ZSBtYWNoaW5lcy4gJz0nICg2MSkgaXNcbiAgICAvLyBvZnRlbiByZWZlcnJlZCB0by4gYGZpbmlzaE9wYCBzaW1wbHkgc2tpcHMgdGhlIGFtb3VudCBvZlxuICAgIC8vIGNoYXJhY3RlcnMgaXQgaXMgZ2l2ZW4gYXMgc2Vjb25kIGFyZ3VtZW50LCBhbmQgcmV0dXJucyBhIHRva2VuXG4gICAgLy8gb2YgdGhlIHR5cGUgZ2l2ZW4gYnkgaXRzIGZpcnN0IGFyZ3VtZW50LlxuXG4gICAgY2FzZSA0NzpcbiAgICAgIC8vICcvJ1xuICAgICAgcmV0dXJuIHRoaXMucmVhZFRva2VuX3NsYXNoKCk7XG5cbiAgICBjYXNlIDM3OmNhc2UgNDI6XG4gICAgICAvLyAnJSonXG4gICAgICByZXR1cm4gdGhpcy5yZWFkVG9rZW5fbXVsdF9tb2R1bG8oY29kZSk7XG5cbiAgICBjYXNlIDEyNDpjYXNlIDM4OlxuICAgICAgLy8gJ3wmJ1xuICAgICAgcmV0dXJuIHRoaXMucmVhZFRva2VuX3BpcGVfYW1wKGNvZGUpO1xuXG4gICAgY2FzZSA5NDpcbiAgICAgIC8vICdeJ1xuICAgICAgcmV0dXJuIHRoaXMucmVhZFRva2VuX2NhcmV0KCk7XG5cbiAgICBjYXNlIDQzOmNhc2UgNDU6XG4gICAgICAvLyAnKy0nXG4gICAgICByZXR1cm4gdGhpcy5yZWFkVG9rZW5fcGx1c19taW4oY29kZSk7XG5cbiAgICBjYXNlIDYwOmNhc2UgNjI6XG4gICAgICAvLyAnPD4nXG4gICAgICByZXR1cm4gdGhpcy5yZWFkVG9rZW5fbHRfZ3QoY29kZSk7XG5cbiAgICBjYXNlIDYxOmNhc2UgMzM6XG4gICAgICAvLyAnPSEnXG4gICAgICByZXR1cm4gdGhpcy5yZWFkVG9rZW5fZXFfZXhjbChjb2RlKTtcblxuICAgIGNhc2UgMTI2OlxuICAgICAgLy8gJ34nXG4gICAgICByZXR1cm4gdGhpcy5maW5pc2hPcCh0dC5wcmVmaXgsIDEpO1xuICB9XG5cbiAgdGhpcy5yYWlzZSh0aGlzLnBvcywgXCJVbmV4cGVjdGVkIGNoYXJhY3RlciAnXCIgKyBjb2RlUG9pbnRUb1N0cmluZyhjb2RlKSArIFwiJ1wiKTtcbn07XG5cbnBwLmZpbmlzaE9wID0gZnVuY3Rpb24gKHR5cGUsIHNpemUpIHtcbiAgdmFyIHN0ciA9IHRoaXMuaW5wdXQuc2xpY2UodGhpcy5wb3MsIHRoaXMucG9zICsgc2l6ZSk7XG4gIHRoaXMucG9zICs9IHNpemU7XG4gIHJldHVybiB0aGlzLmZpbmlzaFRva2VuKHR5cGUsIHN0cik7XG59O1xuXG52YXIgcmVnZXhwVW5pY29kZVN1cHBvcnQgPSBmYWxzZTtcbnRyeSB7XG4gIG5ldyBSZWdFeHAoXCLvv79cIiwgXCJ1XCIpO3JlZ2V4cFVuaWNvZGVTdXBwb3J0ID0gdHJ1ZTtcbn0gY2F0Y2ggKGUpIHt9XG5cbi8vIFBhcnNlIGEgcmVndWxhciBleHByZXNzaW9uLiBTb21lIGNvbnRleHQtYXdhcmVuZXNzIGlzIG5lY2Vzc2FyeSxcbi8vIHNpbmNlIGEgJy8nIGluc2lkZSBhICdbXScgc2V0IGRvZXMgbm90IGVuZCB0aGUgZXhwcmVzc2lvbi5cblxucHAucmVhZFJlZ2V4cCA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIGVzY2FwZWQgPSB1bmRlZmluZWQsXG4gICAgICBpbkNsYXNzID0gdW5kZWZpbmVkLFxuICAgICAgc3RhcnQgPSB0aGlzLnBvcztcbiAgZm9yICg7Oykge1xuICAgIGlmICh0aGlzLnBvcyA+PSB0aGlzLmlucHV0Lmxlbmd0aCkgdGhpcy5yYWlzZShzdGFydCwgXCJVbnRlcm1pbmF0ZWQgcmVndWxhciBleHByZXNzaW9uXCIpO1xuICAgIHZhciBjaCA9IHRoaXMuaW5wdXQuY2hhckF0KHRoaXMucG9zKTtcbiAgICBpZiAobGluZUJyZWFrLnRlc3QoY2gpKSB0aGlzLnJhaXNlKHN0YXJ0LCBcIlVudGVybWluYXRlZCByZWd1bGFyIGV4cHJlc3Npb25cIik7XG4gICAgaWYgKCFlc2NhcGVkKSB7XG4gICAgICBpZiAoY2ggPT09IFwiW1wiKSBpbkNsYXNzID0gdHJ1ZTtlbHNlIGlmIChjaCA9PT0gXCJdXCIgJiYgaW5DbGFzcykgaW5DbGFzcyA9IGZhbHNlO2Vsc2UgaWYgKGNoID09PSBcIi9cIiAmJiAhaW5DbGFzcykgYnJlYWs7XG4gICAgICBlc2NhcGVkID0gY2ggPT09IFwiXFxcXFwiO1xuICAgIH0gZWxzZSBlc2NhcGVkID0gZmFsc2U7XG4gICAgKyt0aGlzLnBvcztcbiAgfVxuICB2YXIgY29udGVudCA9IHRoaXMuaW5wdXQuc2xpY2Uoc3RhcnQsIHRoaXMucG9zKTtcbiAgKyt0aGlzLnBvcztcbiAgLy8gTmVlZCB0byB1c2UgYHJlYWRXb3JkMWAgYmVjYXVzZSAnXFx1WFhYWCcgc2VxdWVuY2VzIGFyZSBhbGxvd2VkXG4gIC8vIGhlcmUgKGRvbid0IGFzaykuXG4gIHZhciBtb2RzID0gdGhpcy5yZWFkV29yZDEoKTtcbiAgdmFyIHRtcCA9IGNvbnRlbnQ7XG4gIGlmIChtb2RzKSB7XG4gICAgdmFyIHZhbGlkRmxhZ3MgPSAvXltnbXNpeV0qJC87XG4gICAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KSB2YWxpZEZsYWdzID0gL15bZ21zaXl1XSokLztcbiAgICBpZiAoIXZhbGlkRmxhZ3MudGVzdChtb2RzKSkgdGhpcy5yYWlzZShzdGFydCwgXCJJbnZhbGlkIHJlZ3VsYXIgZXhwcmVzc2lvbiBmbGFnXCIpO1xuICAgIGlmIChtb2RzLmluZGV4T2YoXCJ1XCIpID49IDAgJiYgIXJlZ2V4cFVuaWNvZGVTdXBwb3J0KSB7XG4gICAgICAvLyBSZXBsYWNlIGVhY2ggYXN0cmFsIHN5bWJvbCBhbmQgZXZlcnkgVW5pY29kZSBlc2NhcGUgc2VxdWVuY2UgdGhhdFxuICAgICAgLy8gcG9zc2libHkgcmVwcmVzZW50cyBhbiBhc3RyYWwgc3ltYm9sIG9yIGEgcGFpcmVkIHN1cnJvZ2F0ZSB3aXRoIGFcbiAgICAgIC8vIHNpbmdsZSBBU0NJSSBzeW1ib2wgdG8gYXZvaWQgdGhyb3dpbmcgb24gcmVndWxhciBleHByZXNzaW9ucyB0aGF0XG4gICAgICAvLyBhcmUgb25seSB2YWxpZCBpbiBjb21iaW5hdGlvbiB3aXRoIHRoZSBgL3VgIGZsYWcuXG4gICAgICAvLyBOb3RlOiByZXBsYWNpbmcgd2l0aCB0aGUgQVNDSUkgc3ltYm9sIGB4YCBtaWdodCBjYXVzZSBmYWxzZVxuICAgICAgLy8gbmVnYXRpdmVzIGluIHVubGlrZWx5IHNjZW5hcmlvcy4gRm9yIGV4YW1wbGUsIGBbXFx1ezYxfS1iXWAgaXMgYVxuICAgICAgLy8gcGVyZmVjdGx5IHZhbGlkIHBhdHRlcm4gdGhhdCBpcyBlcXVpdmFsZW50IHRvIGBbYS1iXWAsIGJ1dCBpdCB3b3VsZFxuICAgICAgLy8gYmUgcmVwbGFjZWQgYnkgYFt4LWJdYCB3aGljaCB0aHJvd3MgYW4gZXJyb3IuXG4gICAgICB0bXAgPSB0bXAucmVwbGFjZSgvXFxcXHUoW2EtZkEtRjAtOV17NH0pfFxcXFx1XFx7KFswLTlhLWZBLUZdKylcXH18W1xcdUQ4MDAtXFx1REJGRl1bXFx1REMwMC1cXHVERkZGXS9nLCBcInhcIik7XG4gICAgfVxuICB9XG4gIC8vIERldGVjdCBpbnZhbGlkIHJlZ3VsYXIgZXhwcmVzc2lvbnMuXG4gIHZhciB2YWx1ZSA9IG51bGw7XG4gIC8vIFJoaW5vJ3MgcmVndWxhciBleHByZXNzaW9uIHBhcnNlciBpcyBmbGFreSBhbmQgdGhyb3dzIHVuY2F0Y2hhYmxlIGV4Y2VwdGlvbnMsXG4gIC8vIHNvIGRvbid0IGRvIGRldGVjdGlvbiBpZiB3ZSBhcmUgcnVubmluZyB1bmRlciBSaGlub1xuICBpZiAoIWlzUmhpbm8pIHtcbiAgICB0cnkge1xuICAgICAgbmV3IFJlZ0V4cCh0bXApO1xuICAgIH0gY2F0Y2ggKGUpIHtcbiAgICAgIGlmIChlIGluc3RhbmNlb2YgU3ludGF4RXJyb3IpIHRoaXMucmFpc2Uoc3RhcnQsIFwiRXJyb3IgcGFyc2luZyByZWd1bGFyIGV4cHJlc3Npb246IFwiICsgZS5tZXNzYWdlKTtcbiAgICAgIHRoaXMucmFpc2UoZSk7XG4gICAgfVxuICAgIC8vIEdldCBhIHJlZ3VsYXIgZXhwcmVzc2lvbiBvYmplY3QgZm9yIHRoaXMgcGF0dGVybi1mbGFnIHBhaXIsIG9yIGBudWxsYCBpblxuICAgIC8vIGNhc2UgdGhlIGN1cnJlbnQgZW52aXJvbm1lbnQgZG9lc24ndCBzdXBwb3J0IHRoZSBmbGFncyBpdCB1c2VzLlxuICAgIHRyeSB7XG4gICAgICB2YWx1ZSA9IG5ldyBSZWdFeHAoY29udGVudCwgbW9kcyk7XG4gICAgfSBjYXRjaCAoZXJyKSB7fVxuICB9XG4gIHJldHVybiB0aGlzLmZpbmlzaFRva2VuKHR0LnJlZ2V4cCwgeyBwYXR0ZXJuOiBjb250ZW50LCBmbGFnczogbW9kcywgdmFsdWU6IHZhbHVlIH0pO1xufTtcblxuLy8gUmVhZCBhbiBpbnRlZ2VyIGluIHRoZSBnaXZlbiByYWRpeC4gUmV0dXJuIG51bGwgaWYgemVybyBkaWdpdHNcbi8vIHdlcmUgcmVhZCwgdGhlIGludGVnZXIgdmFsdWUgb3RoZXJ3aXNlLiBXaGVuIGBsZW5gIGlzIGdpdmVuLCB0aGlzXG4vLyB3aWxsIHJldHVybiBgbnVsbGAgdW5sZXNzIHRoZSBpbnRlZ2VyIGhhcyBleGFjdGx5IGBsZW5gIGRpZ2l0cy5cblxucHAucmVhZEludCA9IGZ1bmN0aW9uIChyYWRpeCwgbGVuKSB7XG4gIHZhciBzdGFydCA9IHRoaXMucG9zLFxuICAgICAgdG90YWwgPSAwO1xuICBmb3IgKHZhciBpID0gMCwgZSA9IGxlbiA9PSBudWxsID8gSW5maW5pdHkgOiBsZW47IGkgPCBlOyArK2kpIHtcbiAgICB2YXIgY29kZSA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyksXG4gICAgICAgIHZhbCA9IHVuZGVmaW5lZDtcbiAgICBpZiAoY29kZSA+PSA5NykgdmFsID0gY29kZSAtIDk3ICsgMTA7IC8vIGFcbiAgICBlbHNlIGlmIChjb2RlID49IDY1KSB2YWwgPSBjb2RlIC0gNjUgKyAxMDsgLy8gQVxuICAgIGVsc2UgaWYgKGNvZGUgPj0gNDggJiYgY29kZSA8PSA1NykgdmFsID0gY29kZSAtIDQ4OyAvLyAwLTlcbiAgICBlbHNlIHZhbCA9IEluZmluaXR5O1xuICAgIGlmICh2YWwgPj0gcmFkaXgpIGJyZWFrO1xuICAgICsrdGhpcy5wb3M7XG4gICAgdG90YWwgPSB0b3RhbCAqIHJhZGl4ICsgdmFsO1xuICB9XG4gIGlmICh0aGlzLnBvcyA9PT0gc3RhcnQgfHwgbGVuICE9IG51bGwgJiYgdGhpcy5wb3MgLSBzdGFydCAhPT0gbGVuKSByZXR1cm4gbnVsbDtcblxuICByZXR1cm4gdG90YWw7XG59O1xuXG5wcC5yZWFkUmFkaXhOdW1iZXIgPSBmdW5jdGlvbiAocmFkaXgpIHtcbiAgdGhpcy5wb3MgKz0gMjsgLy8gMHhcbiAgdmFyIHZhbCA9IHRoaXMucmVhZEludChyYWRpeCk7XG4gIGlmICh2YWwgPT0gbnVsbCkgdGhpcy5yYWlzZSh0aGlzLnN0YXJ0ICsgMiwgXCJFeHBlY3RlZCBudW1iZXIgaW4gcmFkaXggXCIgKyByYWRpeCk7XG4gIGlmIChpc0lkZW50aWZpZXJTdGFydCh0aGlzLmZ1bGxDaGFyQ29kZUF0UG9zKCkpKSB0aGlzLnJhaXNlKHRoaXMucG9zLCBcIklkZW50aWZpZXIgZGlyZWN0bHkgYWZ0ZXIgbnVtYmVyXCIpO1xuICByZXR1cm4gdGhpcy5maW5pc2hUb2tlbih0dC5udW0sIHZhbCk7XG59O1xuXG4vLyBSZWFkIGFuIGludGVnZXIsIG9jdGFsIGludGVnZXIsIG9yIGZsb2F0aW5nLXBvaW50IG51bWJlci5cblxucHAucmVhZE51bWJlciA9IGZ1bmN0aW9uIChzdGFydHNXaXRoRG90KSB7XG4gIHZhciBzdGFydCA9IHRoaXMucG9zLFxuICAgICAgaXNGbG9hdCA9IGZhbHNlLFxuICAgICAgb2N0YWwgPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MpID09PSA0ODtcbiAgaWYgKCFzdGFydHNXaXRoRG90ICYmIHRoaXMucmVhZEludCgxMCkgPT09IG51bGwpIHRoaXMucmFpc2Uoc3RhcnQsIFwiSW52YWxpZCBudW1iZXJcIik7XG4gIGlmICh0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MpID09PSA0Nikge1xuICAgICsrdGhpcy5wb3M7XG4gICAgdGhpcy5yZWFkSW50KDEwKTtcbiAgICBpc0Zsb2F0ID0gdHJ1ZTtcbiAgfVxuICB2YXIgbmV4dCA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyk7XG4gIGlmIChuZXh0ID09PSA2OSB8fCBuZXh0ID09PSAxMDEpIHtcbiAgICAvLyAnZUUnXG4gICAgbmV4dCA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCgrK3RoaXMucG9zKTtcbiAgICBpZiAobmV4dCA9PT0gNDMgfHwgbmV4dCA9PT0gNDUpICsrdGhpcy5wb3M7IC8vICcrLSdcbiAgICBpZiAodGhpcy5yZWFkSW50KDEwKSA9PT0gbnVsbCkgdGhpcy5yYWlzZShzdGFydCwgXCJJbnZhbGlkIG51bWJlclwiKTtcbiAgICBpc0Zsb2F0ID0gdHJ1ZTtcbiAgfVxuICBpZiAoaXNJZGVudGlmaWVyU3RhcnQodGhpcy5mdWxsQ2hhckNvZGVBdFBvcygpKSkgdGhpcy5yYWlzZSh0aGlzLnBvcywgXCJJZGVudGlmaWVyIGRpcmVjdGx5IGFmdGVyIG51bWJlclwiKTtcblxuICB2YXIgc3RyID0gdGhpcy5pbnB1dC5zbGljZShzdGFydCwgdGhpcy5wb3MpLFxuICAgICAgdmFsID0gdW5kZWZpbmVkO1xuICBpZiAoaXNGbG9hdCkgdmFsID0gcGFyc2VGbG9hdChzdHIpO2Vsc2UgaWYgKCFvY3RhbCB8fCBzdHIubGVuZ3RoID09PSAxKSB2YWwgPSBwYXJzZUludChzdHIsIDEwKTtlbHNlIGlmICgvWzg5XS8udGVzdChzdHIpIHx8IHRoaXMuc3RyaWN0KSB0aGlzLnJhaXNlKHN0YXJ0LCBcIkludmFsaWQgbnVtYmVyXCIpO2Vsc2UgdmFsID0gcGFyc2VJbnQoc3RyLCA4KTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoVG9rZW4odHQubnVtLCB2YWwpO1xufTtcblxuLy8gUmVhZCBhIHN0cmluZyB2YWx1ZSwgaW50ZXJwcmV0aW5nIGJhY2tzbGFzaC1lc2NhcGVzLlxuXG5wcC5yZWFkQ29kZVBvaW50ID0gZnVuY3Rpb24gKCkge1xuICB2YXIgY2ggPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MpLFxuICAgICAgY29kZSA9IHVuZGVmaW5lZDtcblxuICBpZiAoY2ggPT09IDEyMykge1xuICAgIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPCA2KSB0aGlzLnVuZXhwZWN0ZWQoKTtcbiAgICArK3RoaXMucG9zO1xuICAgIGNvZGUgPSB0aGlzLnJlYWRIZXhDaGFyKHRoaXMuaW5wdXQuaW5kZXhPZihcIn1cIiwgdGhpcy5wb3MpIC0gdGhpcy5wb3MpO1xuICAgICsrdGhpcy5wb3M7XG4gICAgaWYgKGNvZGUgPiAxMTE0MTExKSB0aGlzLnVuZXhwZWN0ZWQoKTtcbiAgfSBlbHNlIHtcbiAgICBjb2RlID0gdGhpcy5yZWFkSGV4Q2hhcig0KTtcbiAgfVxuICByZXR1cm4gY29kZTtcbn07XG5cbmZ1bmN0aW9uIGNvZGVQb2ludFRvU3RyaW5nKGNvZGUpIHtcbiAgLy8gVVRGLTE2IERlY29kaW5nXG4gIGlmIChjb2RlIDw9IDY1NTM1KSB7XG4gICAgcmV0dXJuIFN0cmluZy5mcm9tQ2hhckNvZGUoY29kZSk7XG4gIH1yZXR1cm4gU3RyaW5nLmZyb21DaGFyQ29kZSgoY29kZSAtIDY1NTM2ID4+IDEwKSArIDU1Mjk2LCAoY29kZSAtIDY1NTM2ICYgMTAyMykgKyA1NjMyMCk7XG59XG5cbnBwLnJlYWRTdHJpbmcgPSBmdW5jdGlvbiAocXVvdGUpIHtcbiAgdmFyIG91dCA9IFwiXCIsXG4gICAgICBjaHVua1N0YXJ0ID0gKyt0aGlzLnBvcztcbiAgZm9yICg7Oykge1xuICAgIGlmICh0aGlzLnBvcyA+PSB0aGlzLmlucHV0Lmxlbmd0aCkgdGhpcy5yYWlzZSh0aGlzLnN0YXJ0LCBcIlVudGVybWluYXRlZCBzdHJpbmcgY29uc3RhbnRcIik7XG4gICAgdmFyIGNoID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zKTtcbiAgICBpZiAoY2ggPT09IHF1b3RlKSBicmVhaztcbiAgICBpZiAoY2ggPT09IDkyKSB7XG4gICAgICAvLyAnXFwnXG4gICAgICBvdXQgKz0gdGhpcy5pbnB1dC5zbGljZShjaHVua1N0YXJ0LCB0aGlzLnBvcyk7XG4gICAgICBvdXQgKz0gdGhpcy5yZWFkRXNjYXBlZENoYXIoKTtcbiAgICAgIGNodW5rU3RhcnQgPSB0aGlzLnBvcztcbiAgICB9IGVsc2Uge1xuICAgICAgaWYgKGlzTmV3TGluZShjaCkpIHRoaXMucmFpc2UodGhpcy5zdGFydCwgXCJVbnRlcm1pbmF0ZWQgc3RyaW5nIGNvbnN0YW50XCIpO1xuICAgICAgKyt0aGlzLnBvcztcbiAgICB9XG4gIH1cbiAgb3V0ICs9IHRoaXMuaW5wdXQuc2xpY2UoY2h1bmtTdGFydCwgdGhpcy5wb3MrKyk7XG4gIHJldHVybiB0aGlzLmZpbmlzaFRva2VuKHR0LnN0cmluZywgb3V0KTtcbn07XG5cbi8vIFJlYWRzIHRlbXBsYXRlIHN0cmluZyB0b2tlbnMuXG5cbnBwLnJlYWRUbXBsVG9rZW4gPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBvdXQgPSBcIlwiLFxuICAgICAgY2h1bmtTdGFydCA9IHRoaXMucG9zO1xuICBmb3IgKDs7KSB7XG4gICAgaWYgKHRoaXMucG9zID49IHRoaXMuaW5wdXQubGVuZ3RoKSB0aGlzLnJhaXNlKHRoaXMuc3RhcnQsIFwiVW50ZXJtaW5hdGVkIHRlbXBsYXRlXCIpO1xuICAgIHZhciBjaCA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyk7XG4gICAgaWYgKGNoID09PSA5NiB8fCBjaCA9PT0gMzYgJiYgdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMSkgPT09IDEyMykge1xuICAgICAgLy8gJ2AnLCAnJHsnXG4gICAgICBpZiAodGhpcy5wb3MgPT09IHRoaXMuc3RhcnQgJiYgdGhpcy50eXBlID09PSB0dC50ZW1wbGF0ZSkge1xuICAgICAgICBpZiAoY2ggPT09IDM2KSB7XG4gICAgICAgICAgdGhpcy5wb3MgKz0gMjtcbiAgICAgICAgICByZXR1cm4gdGhpcy5maW5pc2hUb2tlbih0dC5kb2xsYXJCcmFjZUwpO1xuICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgICsrdGhpcy5wb3M7XG4gICAgICAgICAgcmV0dXJuIHRoaXMuZmluaXNoVG9rZW4odHQuYmFja1F1b3RlKTtcbiAgICAgICAgfVxuICAgICAgfVxuICAgICAgb3V0ICs9IHRoaXMuaW5wdXQuc2xpY2UoY2h1bmtTdGFydCwgdGhpcy5wb3MpO1xuICAgICAgcmV0dXJuIHRoaXMuZmluaXNoVG9rZW4odHQudGVtcGxhdGUsIG91dCk7XG4gICAgfVxuICAgIGlmIChjaCA9PT0gOTIpIHtcbiAgICAgIC8vICdcXCdcbiAgICAgIG91dCArPSB0aGlzLmlucHV0LnNsaWNlKGNodW5rU3RhcnQsIHRoaXMucG9zKTtcbiAgICAgIG91dCArPSB0aGlzLnJlYWRFc2NhcGVkQ2hhcigpO1xuICAgICAgY2h1bmtTdGFydCA9IHRoaXMucG9zO1xuICAgIH0gZWxzZSBpZiAoaXNOZXdMaW5lKGNoKSkge1xuICAgICAgb3V0ICs9IHRoaXMuaW5wdXQuc2xpY2UoY2h1bmtTdGFydCwgdGhpcy5wb3MpO1xuICAgICAgKyt0aGlzLnBvcztcbiAgICAgIGlmIChjaCA9PT0gMTMgJiYgdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zKSA9PT0gMTApIHtcbiAgICAgICAgKyt0aGlzLnBvcztcbiAgICAgICAgb3V0ICs9IFwiXFxuXCI7XG4gICAgICB9IGVsc2Uge1xuICAgICAgICBvdXQgKz0gU3RyaW5nLmZyb21DaGFyQ29kZShjaCk7XG4gICAgICB9XG4gICAgICBpZiAodGhpcy5vcHRpb25zLmxvY2F0aW9ucykge1xuICAgICAgICArK3RoaXMuY3VyTGluZTtcbiAgICAgICAgdGhpcy5saW5lU3RhcnQgPSB0aGlzLnBvcztcbiAgICAgIH1cbiAgICAgIGNodW5rU3RhcnQgPSB0aGlzLnBvcztcbiAgICB9IGVsc2Uge1xuICAgICAgKyt0aGlzLnBvcztcbiAgICB9XG4gIH1cbn07XG5cbi8vIFVzZWQgdG8gcmVhZCBlc2NhcGVkIGNoYXJhY3RlcnNcblxucHAucmVhZEVzY2FwZWRDaGFyID0gZnVuY3Rpb24gKCkge1xuICB2YXIgY2ggPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQoKyt0aGlzLnBvcyk7XG4gIHZhciBvY3RhbCA9IC9eWzAtN10rLy5leGVjKHRoaXMuaW5wdXQuc2xpY2UodGhpcy5wb3MsIHRoaXMucG9zICsgMykpO1xuICBpZiAob2N0YWwpIG9jdGFsID0gb2N0YWxbMF07XG4gIHdoaWxlIChvY3RhbCAmJiBwYXJzZUludChvY3RhbCwgOCkgPiAyNTUpIG9jdGFsID0gb2N0YWwuc2xpY2UoMCwgLTEpO1xuICBpZiAob2N0YWwgPT09IFwiMFwiKSBvY3RhbCA9IG51bGw7XG4gICsrdGhpcy5wb3M7XG4gIGlmIChvY3RhbCkge1xuICAgIGlmICh0aGlzLnN0cmljdCkgdGhpcy5yYWlzZSh0aGlzLnBvcyAtIDIsIFwiT2N0YWwgbGl0ZXJhbCBpbiBzdHJpY3QgbW9kZVwiKTtcbiAgICB0aGlzLnBvcyArPSBvY3RhbC5sZW5ndGggLSAxO1xuICAgIHJldHVybiBTdHJpbmcuZnJvbUNoYXJDb2RlKHBhcnNlSW50KG9jdGFsLCA4KSk7XG4gIH0gZWxzZSB7XG4gICAgc3dpdGNoIChjaCkge1xuICAgICAgY2FzZSAxMTA6XG4gICAgICAgIHJldHVybiBcIlxcblwiOyAvLyAnbicgLT4gJ1xcbidcbiAgICAgIGNhc2UgMTE0OlxuICAgICAgICByZXR1cm4gXCJcXHJcIjsgLy8gJ3InIC0+ICdcXHInXG4gICAgICBjYXNlIDEyMDpcbiAgICAgICAgcmV0dXJuIFN0cmluZy5mcm9tQ2hhckNvZGUodGhpcy5yZWFkSGV4Q2hhcigyKSk7IC8vICd4J1xuICAgICAgY2FzZSAxMTc6XG4gICAgICAgIHJldHVybiBjb2RlUG9pbnRUb1N0cmluZyh0aGlzLnJlYWRDb2RlUG9pbnQoKSk7IC8vICd1J1xuICAgICAgY2FzZSAxMTY6XG4gICAgICAgIHJldHVybiBcIlxcdFwiOyAvLyAndCcgLT4gJ1xcdCdcbiAgICAgIGNhc2UgOTg6XG4gICAgICAgIHJldHVybiBcIlxcYlwiOyAvLyAnYicgLT4gJ1xcYidcbiAgICAgIGNhc2UgMTE4OlxuICAgICAgICByZXR1cm4gXCJcXHUwMDBiXCI7IC8vICd2JyAtPiAnXFx1MDAwYidcbiAgICAgIGNhc2UgMTAyOlxuICAgICAgICByZXR1cm4gXCJcXGZcIjsgLy8gJ2YnIC0+ICdcXGYnXG4gICAgICBjYXNlIDQ4OlxuICAgICAgICByZXR1cm4gXCJcXHUwMDAwXCI7IC8vIDAgLT4gJ1xcMCdcbiAgICAgIGNhc2UgMTM6XG4gICAgICAgIGlmICh0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MpID09PSAxMCkgKyt0aGlzLnBvczsgLy8gJ1xcclxcbidcbiAgICAgIGNhc2UgMTA6XG4gICAgICAgIC8vICcgXFxuJ1xuICAgICAgICBpZiAodGhpcy5vcHRpb25zLmxvY2F0aW9ucykge1xuICAgICAgICAgIHRoaXMubGluZVN0YXJ0ID0gdGhpcy5wb3M7Kyt0aGlzLmN1ckxpbmU7XG4gICAgICAgIH1cbiAgICAgICAgcmV0dXJuIFwiXCI7XG4gICAgICBkZWZhdWx0OlxuICAgICAgICByZXR1cm4gU3RyaW5nLmZyb21DaGFyQ29kZShjaCk7XG4gICAgfVxuICB9XG59O1xuXG4vLyBVc2VkIHRvIHJlYWQgY2hhcmFjdGVyIGVzY2FwZSBzZXF1ZW5jZXMgKCdcXHgnLCAnXFx1JywgJ1xcVScpLlxuXG5wcC5yZWFkSGV4Q2hhciA9IGZ1bmN0aW9uIChsZW4pIHtcbiAgdmFyIG4gPSB0aGlzLnJlYWRJbnQoMTYsIGxlbik7XG4gIGlmIChuID09PSBudWxsKSB0aGlzLnJhaXNlKHRoaXMuc3RhcnQsIFwiQmFkIGNoYXJhY3RlciBlc2NhcGUgc2VxdWVuY2VcIik7XG4gIHJldHVybiBuO1xufTtcblxuLy8gVXNlZCB0byBzaWduYWwgdG8gY2FsbGVycyBvZiBgcmVhZFdvcmQxYCB3aGV0aGVyIHRoZSB3b3JkXG4vLyBjb250YWluZWQgYW55IGVzY2FwZSBzZXF1ZW5jZXMuIFRoaXMgaXMgbmVlZGVkIGJlY2F1c2Ugd29yZHMgd2l0aFxuLy8gZXNjYXBlIHNlcXVlbmNlcyBtdXN0IG5vdCBiZSBpbnRlcnByZXRlZCBhcyBrZXl3b3Jkcy5cblxudmFyIGNvbnRhaW5zRXNjO1xuXG4vLyBSZWFkIGFuIGlkZW50aWZpZXIsIGFuZCByZXR1cm4gaXQgYXMgYSBzdHJpbmcuIFNldHMgYGNvbnRhaW5zRXNjYFxuLy8gdG8gd2hldGhlciB0aGUgd29yZCBjb250YWluZWQgYSAnXFx1JyBlc2NhcGUuXG4vL1xuLy8gSW5jcmVtZW50YWxseSBhZGRzIG9ubHkgZXNjYXBlZCBjaGFycywgYWRkaW5nIG90aGVyIGNodW5rcyBhcy1pc1xuLy8gYXMgYSBtaWNyby1vcHRpbWl6YXRpb24uXG5cbnBwLnJlYWRXb3JkMSA9IGZ1bmN0aW9uICgpIHtcbiAgY29udGFpbnNFc2MgPSBmYWxzZTtcbiAgdmFyIHdvcmQgPSBcIlwiLFxuICAgICAgZmlyc3QgPSB0cnVlLFxuICAgICAgY2h1bmtTdGFydCA9IHRoaXMucG9zO1xuICB2YXIgYXN0cmFsID0gdGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDY7XG4gIHdoaWxlICh0aGlzLnBvcyA8IHRoaXMuaW5wdXQubGVuZ3RoKSB7XG4gICAgdmFyIGNoID0gdGhpcy5mdWxsQ2hhckNvZGVBdFBvcygpO1xuICAgIGlmIChpc0lkZW50aWZpZXJDaGFyKGNoLCBhc3RyYWwpKSB7XG4gICAgICB0aGlzLnBvcyArPSBjaCA8PSA2NTUzNSA/IDEgOiAyO1xuICAgIH0gZWxzZSBpZiAoY2ggPT09IDkyKSB7XG4gICAgICAvLyBcIlxcXCJcbiAgICAgIGNvbnRhaW5zRXNjID0gdHJ1ZTtcbiAgICAgIHdvcmQgKz0gdGhpcy5pbnB1dC5zbGljZShjaHVua1N0YXJ0LCB0aGlzLnBvcyk7XG4gICAgICB2YXIgZXNjU3RhcnQgPSB0aGlzLnBvcztcbiAgICAgIGlmICh0aGlzLmlucHV0LmNoYXJDb2RlQXQoKyt0aGlzLnBvcykgIT0gMTE3KSAvLyBcInVcIlxuICAgICAgICB0aGlzLnJhaXNlKHRoaXMucG9zLCBcIkV4cGVjdGluZyBVbmljb2RlIGVzY2FwZSBzZXF1ZW5jZSBcXFxcdVhYWFhcIik7XG4gICAgICArK3RoaXMucG9zO1xuICAgICAgdmFyIGVzYyA9IHRoaXMucmVhZENvZGVQb2ludCgpO1xuICAgICAgaWYgKCEoZmlyc3QgPyBpc0lkZW50aWZpZXJTdGFydCA6IGlzSWRlbnRpZmllckNoYXIpKGVzYywgYXN0cmFsKSkgdGhpcy5yYWlzZShlc2NTdGFydCwgXCJJbnZhbGlkIFVuaWNvZGUgZXNjYXBlXCIpO1xuICAgICAgd29yZCArPSBjb2RlUG9pbnRUb1N0cmluZyhlc2MpO1xuICAgICAgY2h1bmtTdGFydCA9IHRoaXMucG9zO1xuICAgIH0gZWxzZSB7XG4gICAgICBicmVhaztcbiAgICB9XG4gICAgZmlyc3QgPSBmYWxzZTtcbiAgfVxuICByZXR1cm4gd29yZCArIHRoaXMuaW5wdXQuc2xpY2UoY2h1bmtTdGFydCwgdGhpcy5wb3MpO1xufTtcblxuLy8gUmVhZCBhbiBpZGVudGlmaWVyIG9yIGtleXdvcmQgdG9rZW4uIFdpbGwgY2hlY2sgZm9yIHJlc2VydmVkXG4vLyB3b3JkcyB3aGVuIG5lY2Vzc2FyeS5cblxucHAucmVhZFdvcmQgPSBmdW5jdGlvbiAoKSB7XG4gIHZhciB3b3JkID0gdGhpcy5yZWFkV29yZDEoKTtcbiAgdmFyIHR5cGUgPSB0dC5uYW1lO1xuICBpZiAoKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2IHx8ICFjb250YWluc0VzYykgJiYgdGhpcy5pc0tleXdvcmQod29yZCkpIHR5cGUgPSBrZXl3b3JkVHlwZXNbd29yZF07XG4gIHJldHVybiB0aGlzLmZpbmlzaFRva2VuKHR5cGUsIHdvcmQpO1xufTtcblxufSx7XCIuL2lkZW50aWZpZXJcIjo3LFwiLi9sb2NhdGlvblwiOjgsXCIuL3N0YXRlXCI6MTMsXCIuL3Rva2VudHlwZVwiOjE3LFwiLi93aGl0ZXNwYWNlXCI6MTl9XSwxNzpbZnVuY3Rpb24oX2RlcmVxXyxtb2R1bGUsZXhwb3J0cyl7XG5cInVzZSBzdHJpY3RcIjtcblxudmFyIF9jbGFzc0NhbGxDaGVjayA9IGZ1bmN0aW9uIChpbnN0YW5jZSwgQ29uc3RydWN0b3IpIHsgaWYgKCEoaW5zdGFuY2UgaW5zdGFuY2VvZiBDb25zdHJ1Y3RvcikpIHsgdGhyb3cgbmV3IFR5cGVFcnJvcihcIkNhbm5vdCBjYWxsIGEgY2xhc3MgYXMgYSBmdW5jdGlvblwiKTsgfSB9O1xuXG5leHBvcnRzLl9fZXNNb2R1bGUgPSB0cnVlO1xuLy8gIyMgVG9rZW4gdHlwZXNcblxuLy8gVGhlIGFzc2lnbm1lbnQgb2YgZmluZS1ncmFpbmVkLCBpbmZvcm1hdGlvbi1jYXJyeWluZyB0eXBlIG9iamVjdHNcbi8vIGFsbG93cyB0aGUgdG9rZW5pemVyIHRvIHN0b3JlIHRoZSBpbmZvcm1hdGlvbiBpdCBoYXMgYWJvdXQgYVxuLy8gdG9rZW4gaW4gYSB3YXkgdGhhdCBpcyB2ZXJ5IGNoZWFwIGZvciB0aGUgcGFyc2VyIHRvIGxvb2sgdXAuXG5cbi8vIEFsbCB0b2tlbiB0eXBlIHZhcmlhYmxlcyBzdGFydCB3aXRoIGFuIHVuZGVyc2NvcmUsIHRvIG1ha2UgdGhlbVxuLy8gZWFzeSB0byByZWNvZ25pemUuXG5cbi8vIFRoZSBgYmVmb3JlRXhwcmAgcHJvcGVydHkgaXMgdXNlZCB0byBkaXNhbWJpZ3VhdGUgYmV0d2VlbiByZWd1bGFyXG4vLyBleHByZXNzaW9ucyBhbmQgZGl2aXNpb25zLiBJdCBpcyBzZXQgb24gYWxsIHRva2VuIHR5cGVzIHRoYXQgY2FuXG4vLyBiZSBmb2xsb3dlZCBieSBhbiBleHByZXNzaW9uICh0aHVzLCBhIHNsYXNoIGFmdGVyIHRoZW0gd291bGQgYmUgYVxuLy8gcmVndWxhciBleHByZXNzaW9uKS5cbi8vXG4vLyBgaXNMb29wYCBtYXJrcyBhIGtleXdvcmQgYXMgc3RhcnRpbmcgYSBsb29wLCB3aGljaCBpcyBpbXBvcnRhbnRcbi8vIHRvIGtub3cgd2hlbiBwYXJzaW5nIGEgbGFiZWwsIGluIG9yZGVyIHRvIGFsbG93IG9yIGRpc2FsbG93XG4vLyBjb250aW51ZSBqdW1wcyB0byB0aGF0IGxhYmVsLlxuXG52YXIgVG9rZW5UeXBlID0gZXhwb3J0cy5Ub2tlblR5cGUgPSBmdW5jdGlvbiBUb2tlblR5cGUobGFiZWwpIHtcbiAgdmFyIGNvbmYgPSBhcmd1bWVudHNbMV0gPT09IHVuZGVmaW5lZCA/IHt9IDogYXJndW1lbnRzWzFdO1xuXG4gIF9jbGFzc0NhbGxDaGVjayh0aGlzLCBUb2tlblR5cGUpO1xuXG4gIHRoaXMubGFiZWwgPSBsYWJlbDtcbiAgdGhpcy5rZXl3b3JkID0gY29uZi5rZXl3b3JkO1xuICB0aGlzLmJlZm9yZUV4cHIgPSAhIWNvbmYuYmVmb3JlRXhwcjtcbiAgdGhpcy5zdGFydHNFeHByID0gISFjb25mLnN0YXJ0c0V4cHI7XG4gIHRoaXMuaXNMb29wID0gISFjb25mLmlzTG9vcDtcbiAgdGhpcy5pc0Fzc2lnbiA9ICEhY29uZi5pc0Fzc2lnbjtcbiAgdGhpcy5wcmVmaXggPSAhIWNvbmYucHJlZml4O1xuICB0aGlzLnBvc3RmaXggPSAhIWNvbmYucG9zdGZpeDtcbiAgdGhpcy5iaW5vcCA9IGNvbmYuYmlub3AgfHwgbnVsbDtcbiAgdGhpcy51cGRhdGVDb250ZXh0ID0gbnVsbDtcbn07XG5cbmZ1bmN0aW9uIGJpbm9wKG5hbWUsIHByZWMpIHtcbiAgcmV0dXJuIG5ldyBUb2tlblR5cGUobmFtZSwgeyBiZWZvcmVFeHByOiB0cnVlLCBiaW5vcDogcHJlYyB9KTtcbn1cbnZhciBiZWZvcmVFeHByID0geyBiZWZvcmVFeHByOiB0cnVlIH0sXG4gICAgc3RhcnRzRXhwciA9IHsgc3RhcnRzRXhwcjogdHJ1ZSB9O1xuXG52YXIgdHlwZXMgPSB7XG4gIG51bTogbmV3IFRva2VuVHlwZShcIm51bVwiLCBzdGFydHNFeHByKSxcbiAgcmVnZXhwOiBuZXcgVG9rZW5UeXBlKFwicmVnZXhwXCIsIHN0YXJ0c0V4cHIpLFxuICBzdHJpbmc6IG5ldyBUb2tlblR5cGUoXCJzdHJpbmdcIiwgc3RhcnRzRXhwciksXG4gIG5hbWU6IG5ldyBUb2tlblR5cGUoXCJuYW1lXCIsIHN0YXJ0c0V4cHIpLFxuICBlb2Y6IG5ldyBUb2tlblR5cGUoXCJlb2ZcIiksXG5cbiAgLy8gUHVuY3R1YXRpb24gdG9rZW4gdHlwZXMuXG4gIGJyYWNrZXRMOiBuZXcgVG9rZW5UeXBlKFwiW1wiLCB7IGJlZm9yZUV4cHI6IHRydWUsIHN0YXJ0c0V4cHI6IHRydWUgfSksXG4gIGJyYWNrZXRSOiBuZXcgVG9rZW5UeXBlKFwiXVwiKSxcbiAgYnJhY2VMOiBuZXcgVG9rZW5UeXBlKFwie1wiLCB7IGJlZm9yZUV4cHI6IHRydWUsIHN0YXJ0c0V4cHI6IHRydWUgfSksXG4gIGJyYWNlUjogbmV3IFRva2VuVHlwZShcIn1cIiksXG4gIHBhcmVuTDogbmV3IFRva2VuVHlwZShcIihcIiwgeyBiZWZvcmVFeHByOiB0cnVlLCBzdGFydHNFeHByOiB0cnVlIH0pLFxuICBwYXJlblI6IG5ldyBUb2tlblR5cGUoXCIpXCIpLFxuICBjb21tYTogbmV3IFRva2VuVHlwZShcIixcIiwgYmVmb3JlRXhwciksXG4gIHNlbWk6IG5ldyBUb2tlblR5cGUoXCI7XCIsIGJlZm9yZUV4cHIpLFxuICBjb2xvbjogbmV3IFRva2VuVHlwZShcIjpcIiwgYmVmb3JlRXhwciksXG4gIGRvdDogbmV3IFRva2VuVHlwZShcIi5cIiksXG4gIHF1ZXN0aW9uOiBuZXcgVG9rZW5UeXBlKFwiP1wiLCBiZWZvcmVFeHByKSxcbiAgYXJyb3c6IG5ldyBUb2tlblR5cGUoXCI9PlwiLCBiZWZvcmVFeHByKSxcbiAgdGVtcGxhdGU6IG5ldyBUb2tlblR5cGUoXCJ0ZW1wbGF0ZVwiKSxcbiAgZWxsaXBzaXM6IG5ldyBUb2tlblR5cGUoXCIuLi5cIiwgYmVmb3JlRXhwciksXG4gIGJhY2tRdW90ZTogbmV3IFRva2VuVHlwZShcImBcIiwgc3RhcnRzRXhwciksXG4gIGRvbGxhckJyYWNlTDogbmV3IFRva2VuVHlwZShcIiR7XCIsIHsgYmVmb3JlRXhwcjogdHJ1ZSwgc3RhcnRzRXhwcjogdHJ1ZSB9KSxcblxuICAvLyBPcGVyYXRvcnMuIFRoZXNlIGNhcnJ5IHNldmVyYWwga2luZHMgb2YgcHJvcGVydGllcyB0byBoZWxwIHRoZVxuICAvLyBwYXJzZXIgdXNlIHRoZW0gcHJvcGVybHkgKHRoZSBwcmVzZW5jZSBvZiB0aGVzZSBwcm9wZXJ0aWVzIGlzXG4gIC8vIHdoYXQgY2F0ZWdvcml6ZXMgdGhlbSBhcyBvcGVyYXRvcnMpLlxuICAvL1xuICAvLyBgYmlub3BgLCB3aGVuIHByZXNlbnQsIHNwZWNpZmllcyB0aGF0IHRoaXMgb3BlcmF0b3IgaXMgYSBiaW5hcnlcbiAgLy8gb3BlcmF0b3IsIGFuZCB3aWxsIHJlZmVyIHRvIGl0cyBwcmVjZWRlbmNlLlxuICAvL1xuICAvLyBgcHJlZml4YCBhbmQgYHBvc3RmaXhgIG1hcmsgdGhlIG9wZXJhdG9yIGFzIGEgcHJlZml4IG9yIHBvc3RmaXhcbiAgLy8gdW5hcnkgb3BlcmF0b3IuXG4gIC8vXG4gIC8vIGBpc0Fzc2lnbmAgbWFya3MgYWxsIG9mIGA9YCwgYCs9YCwgYC09YCBldGNldGVyYSwgd2hpY2ggYWN0IGFzXG4gIC8vIGJpbmFyeSBvcGVyYXRvcnMgd2l0aCBhIHZlcnkgbG93IHByZWNlZGVuY2UsIHRoYXQgc2hvdWxkIHJlc3VsdFxuICAvLyBpbiBBc3NpZ25tZW50RXhwcmVzc2lvbiBub2Rlcy5cblxuICBlcTogbmV3IFRva2VuVHlwZShcIj1cIiwgeyBiZWZvcmVFeHByOiB0cnVlLCBpc0Fzc2lnbjogdHJ1ZSB9KSxcbiAgYXNzaWduOiBuZXcgVG9rZW5UeXBlKFwiXz1cIiwgeyBiZWZvcmVFeHByOiB0cnVlLCBpc0Fzc2lnbjogdHJ1ZSB9KSxcbiAgaW5jRGVjOiBuZXcgVG9rZW5UeXBlKFwiKysvLS1cIiwgeyBwcmVmaXg6IHRydWUsIHBvc3RmaXg6IHRydWUsIHN0YXJ0c0V4cHI6IHRydWUgfSksXG4gIHByZWZpeDogbmV3IFRva2VuVHlwZShcInByZWZpeFwiLCB7IGJlZm9yZUV4cHI6IHRydWUsIHByZWZpeDogdHJ1ZSwgc3RhcnRzRXhwcjogdHJ1ZSB9KSxcbiAgbG9naWNhbE9SOiBiaW5vcChcInx8XCIsIDEpLFxuICBsb2dpY2FsQU5EOiBiaW5vcChcIiYmXCIsIDIpLFxuICBiaXR3aXNlT1I6IGJpbm9wKFwifFwiLCAzKSxcbiAgYml0d2lzZVhPUjogYmlub3AoXCJeXCIsIDQpLFxuICBiaXR3aXNlQU5EOiBiaW5vcChcIiZcIiwgNSksXG4gIGVxdWFsaXR5OiBiaW5vcChcIj09LyE9XCIsIDYpLFxuICByZWxhdGlvbmFsOiBiaW5vcChcIjwvPlwiLCA3KSxcbiAgYml0U2hpZnQ6IGJpbm9wKFwiPDwvPj5cIiwgOCksXG4gIHBsdXNNaW46IG5ldyBUb2tlblR5cGUoXCIrLy1cIiwgeyBiZWZvcmVFeHByOiB0cnVlLCBiaW5vcDogOSwgcHJlZml4OiB0cnVlLCBzdGFydHNFeHByOiB0cnVlIH0pLFxuICBtb2R1bG86IGJpbm9wKFwiJVwiLCAxMCksXG4gIHN0YXI6IGJpbm9wKFwiKlwiLCAxMCksXG4gIHNsYXNoOiBiaW5vcChcIi9cIiwgMTApXG59O1xuXG5leHBvcnRzLnR5cGVzID0gdHlwZXM7XG4vLyBNYXAga2V5d29yZCBuYW1lcyB0byB0b2tlbiB0eXBlcy5cblxudmFyIGtleXdvcmRzID0ge307XG5cbmV4cG9ydHMua2V5d29yZHMgPSBrZXl3b3Jkcztcbi8vIFN1Y2NpbmN0IGRlZmluaXRpb25zIG9mIGtleXdvcmQgdG9rZW4gdHlwZXNcbmZ1bmN0aW9uIGt3KG5hbWUpIHtcbiAgdmFyIG9wdGlvbnMgPSBhcmd1bWVudHNbMV0gPT09IHVuZGVmaW5lZCA/IHt9IDogYXJndW1lbnRzWzFdO1xuXG4gIG9wdGlvbnMua2V5d29yZCA9IG5hbWU7XG4gIGtleXdvcmRzW25hbWVdID0gdHlwZXNbXCJfXCIgKyBuYW1lXSA9IG5ldyBUb2tlblR5cGUobmFtZSwgb3B0aW9ucyk7XG59XG5cbmt3KFwiYnJlYWtcIik7XG5rdyhcImNhc2VcIiwgYmVmb3JlRXhwcik7XG5rdyhcImNhdGNoXCIpO1xua3coXCJjb250aW51ZVwiKTtcbmt3KFwiZGVidWdnZXJcIik7XG5rdyhcImRlZmF1bHRcIik7XG5rdyhcImRvXCIsIHsgaXNMb29wOiB0cnVlIH0pO1xua3coXCJlbHNlXCIsIGJlZm9yZUV4cHIpO1xua3coXCJmaW5hbGx5XCIpO1xua3coXCJmb3JcIiwgeyBpc0xvb3A6IHRydWUgfSk7XG5rdyhcImZ1bmN0aW9uXCIsIHN0YXJ0c0V4cHIpO1xua3coXCJpZlwiKTtcbmt3KFwicmV0dXJuXCIsIGJlZm9yZUV4cHIpO1xua3coXCJzd2l0Y2hcIik7XG5rdyhcInRocm93XCIsIGJlZm9yZUV4cHIpO1xua3coXCJ0cnlcIik7XG5rdyhcInZhclwiKTtcbmt3KFwibGV0XCIpO1xua3coXCJjb25zdFwiKTtcbmt3KFwid2hpbGVcIiwgeyBpc0xvb3A6IHRydWUgfSk7XG5rdyhcIndpdGhcIik7XG5rdyhcIm5ld1wiLCB7IGJlZm9yZUV4cHI6IHRydWUsIHN0YXJ0c0V4cHI6IHRydWUgfSk7XG5rdyhcInRoaXNcIiwgc3RhcnRzRXhwcik7XG5rdyhcInN1cGVyXCIsIHN0YXJ0c0V4cHIpO1xua3coXCJjbGFzc1wiKTtcbmt3KFwiZXh0ZW5kc1wiLCBiZWZvcmVFeHByKTtcbmt3KFwiZXhwb3J0XCIpO1xua3coXCJpbXBvcnRcIik7XG5rdyhcInlpZWxkXCIsIHsgYmVmb3JlRXhwcjogdHJ1ZSwgc3RhcnRzRXhwcjogdHJ1ZSB9KTtcbmt3KFwibnVsbFwiLCBzdGFydHNFeHByKTtcbmt3KFwidHJ1ZVwiLCBzdGFydHNFeHByKTtcbmt3KFwiZmFsc2VcIiwgc3RhcnRzRXhwcik7XG5rdyhcImluXCIsIHsgYmVmb3JlRXhwcjogdHJ1ZSwgYmlub3A6IDcgfSk7XG5rdyhcImluc3RhbmNlb2ZcIiwgeyBiZWZvcmVFeHByOiB0cnVlLCBiaW5vcDogNyB9KTtcbmt3KFwidHlwZW9mXCIsIHsgYmVmb3JlRXhwcjogdHJ1ZSwgcHJlZml4OiB0cnVlLCBzdGFydHNFeHByOiB0cnVlIH0pO1xua3coXCJ2b2lkXCIsIHsgYmVmb3JlRXhwcjogdHJ1ZSwgcHJlZml4OiB0cnVlLCBzdGFydHNFeHByOiB0cnVlIH0pO1xua3coXCJkZWxldGVcIiwgeyBiZWZvcmVFeHByOiB0cnVlLCBwcmVmaXg6IHRydWUsIHN0YXJ0c0V4cHI6IHRydWUgfSk7XG5cbn0se31dLDE4OltmdW5jdGlvbihfZGVyZXFfLG1vZHVsZSxleHBvcnRzKXtcblwidXNlIHN0cmljdFwiO1xuXG5leHBvcnRzLmlzQXJyYXkgPSBpc0FycmF5O1xuXG4vLyBDaGVja3MgaWYgYW4gb2JqZWN0IGhhcyBhIHByb3BlcnR5LlxuXG5leHBvcnRzLmhhcyA9IGhhcztcbmV4cG9ydHMuX19lc01vZHVsZSA9IHRydWU7XG5cbmZ1bmN0aW9uIGlzQXJyYXkob2JqKSB7XG4gIHJldHVybiBPYmplY3QucHJvdG90eXBlLnRvU3RyaW5nLmNhbGwob2JqKSA9PT0gXCJbb2JqZWN0IEFycmF5XVwiO1xufVxuXG5mdW5jdGlvbiBoYXMob2JqLCBwcm9wTmFtZSkge1xuICByZXR1cm4gT2JqZWN0LnByb3RvdHlwZS5oYXNPd25Qcm9wZXJ0eS5jYWxsKG9iaiwgcHJvcE5hbWUpO1xufVxuXG59LHt9XSwxOTpbZnVuY3Rpb24oX2RlcmVxXyxtb2R1bGUsZXhwb3J0cyl7XG5cInVzZSBzdHJpY3RcIjtcblxuZXhwb3J0cy5pc05ld0xpbmUgPSBpc05ld0xpbmU7XG5leHBvcnRzLl9fZXNNb2R1bGUgPSB0cnVlO1xuLy8gTWF0Y2hlcyBhIHdob2xlIGxpbmUgYnJlYWsgKHdoZXJlIENSTEYgaXMgY29uc2lkZXJlZCBhIHNpbmdsZVxuLy8gbGluZSBicmVhaykuIFVzZWQgdG8gY291bnQgbGluZXMuXG5cbnZhciBsaW5lQnJlYWsgPSAvXFxyXFxuP3xcXG58XFx1MjAyOHxcXHUyMDI5LztcbmV4cG9ydHMubGluZUJyZWFrID0gbGluZUJyZWFrO1xudmFyIGxpbmVCcmVha0cgPSBuZXcgUmVnRXhwKGxpbmVCcmVhay5zb3VyY2UsIFwiZ1wiKTtcblxuZXhwb3J0cy5saW5lQnJlYWtHID0gbGluZUJyZWFrRztcblxuZnVuY3Rpb24gaXNOZXdMaW5lKGNvZGUpIHtcbiAgcmV0dXJuIGNvZGUgPT09IDEwIHx8IGNvZGUgPT09IDEzIHx8IGNvZGUgPT09IDgyMzIgfHwgY29kZSA9PSA4MjMzO1xufVxuXG52YXIgbm9uQVNDSUl3aGl0ZXNwYWNlID0gL1tcXHUxNjgwXFx1MTgwZVxcdTIwMDAtXFx1MjAwYVxcdTIwMmZcXHUyMDVmXFx1MzAwMFxcdWZlZmZdLztcbmV4cG9ydHMubm9uQVNDSUl3aGl0ZXNwYWNlID0gbm9uQVNDSUl3aGl0ZXNwYWNlO1xuXG59LHt9XX0se30sWzFdKSgxKVxufSk7IiwiKGZ1bmN0aW9uKGYpe2lmKHR5cGVvZiBleHBvcnRzPT09XCJvYmplY3RcIiYmdHlwZW9mIG1vZHVsZSE9PVwidW5kZWZpbmVkXCIpe21vZHVsZS5leHBvcnRzPWYoKX1lbHNlIGlmKHR5cGVvZiBkZWZpbmU9PT1cImZ1bmN0aW9uXCImJmRlZmluZS5hbWQpe2RlZmluZShbXSxmKX1lbHNle3ZhciBnO2lmKHR5cGVvZiB3aW5kb3chPT1cInVuZGVmaW5lZFwiKXtnPXdpbmRvd31lbHNlIGlmKHR5cGVvZiBnbG9iYWwhPT1cInVuZGVmaW5lZFwiKXtnPWdsb2JhbH1lbHNlIGlmKHR5cGVvZiBzZWxmIT09XCJ1bmRlZmluZWRcIil7Zz1zZWxmfWVsc2V7Zz10aGlzfShnLmFjb3JuIHx8IChnLmFjb3JuID0ge30pKS5sb29zZSA9IGYoKX19KShmdW5jdGlvbigpe3ZhciBkZWZpbmUsbW9kdWxlLGV4cG9ydHM7cmV0dXJuIChmdW5jdGlvbiBlKHQsbixyKXtmdW5jdGlvbiBzKG8sdSl7aWYoIW5bb10pe2lmKCF0W29dKXt2YXIgYT10eXBlb2YgcmVxdWlyZT09XCJmdW5jdGlvblwiJiZyZXF1aXJlO2lmKCF1JiZhKXJldHVybiBhKG8sITApO2lmKGkpcmV0dXJuIGkobywhMCk7dmFyIGY9bmV3IEVycm9yKFwiQ2Fubm90IGZpbmQgbW9kdWxlICdcIitvK1wiJ1wiKTt0aHJvdyBmLmNvZGU9XCJNT0RVTEVfTk9UX0ZPVU5EXCIsZn12YXIgbD1uW29dPXtleHBvcnRzOnt9fTt0W29dWzBdLmNhbGwobC5leHBvcnRzLGZ1bmN0aW9uKGUpe3ZhciBuPXRbb11bMV1bZV07cmV0dXJuIHMobj9uOmUpfSxsLGwuZXhwb3J0cyxlLHQsbixyKX1yZXR1cm4gbltvXS5leHBvcnRzfXZhciBpPXR5cGVvZiByZXF1aXJlPT1cImZ1bmN0aW9uXCImJnJlcXVpcmU7Zm9yKHZhciBvPTA7bzxyLmxlbmd0aDtvKyspcyhyW29dKTtyZXR1cm4gc30pKHsxOltmdW5jdGlvbihfZGVyZXFfLG1vZHVsZSxleHBvcnRzKXtcblwidXNlIHN0cmljdFwiO1xuXG52YXIgX2ludGVyb3BSZXF1aXJlV2lsZGNhcmQgPSBmdW5jdGlvbiAob2JqKSB7IHJldHVybiBvYmogJiYgb2JqLl9fZXNNb2R1bGUgPyBvYmogOiB7IFwiZGVmYXVsdFwiOiBvYmogfTsgfTtcblxuZXhwb3J0cy5wYXJzZV9kYW1taXQgPSBwYXJzZV9kYW1taXQ7XG5leHBvcnRzLl9fZXNNb2R1bGUgPSB0cnVlO1xuLy8gQWNvcm46IExvb3NlIHBhcnNlclxuLy9cbi8vIFRoaXMgbW9kdWxlIHByb3ZpZGVzIGFuIGFsdGVybmF0aXZlIHBhcnNlciAoYHBhcnNlX2RhbW1pdGApIHRoYXRcbi8vIGV4cG9zZXMgdGhhdCBzYW1lIGludGVyZmFjZSBhcyBgcGFyc2VgLCBidXQgd2lsbCB0cnkgdG8gcGFyc2Vcbi8vIGFueXRoaW5nIGFzIEphdmFTY3JpcHQsIHJlcGFpcmluZyBzeW50YXggZXJyb3IgdGhlIGJlc3QgaXQgY2FuLlxuLy8gVGhlcmUgYXJlIGNpcmN1bXN0YW5jZXMgaW4gd2hpY2ggaXQgd2lsbCByYWlzZSBhbiBlcnJvciBhbmQgZ2l2ZVxuLy8gdXAsIGJ1dCB0aGV5IGFyZSB2ZXJ5IHJhcmUuIFRoZSByZXN1bHRpbmcgQVNUIHdpbGwgYmUgYSBtb3N0bHlcbi8vIHZhbGlkIEphdmFTY3JpcHQgQVNUIChhcyBwZXIgdGhlIFtNb3ppbGxhIHBhcnNlciBBUEldW2FwaV0sIGV4Y2VwdFxuLy8gdGhhdDpcbi8vXG4vLyAtIFJldHVybiBvdXRzaWRlIGZ1bmN0aW9ucyBpcyBhbGxvd2VkXG4vL1xuLy8gLSBMYWJlbCBjb25zaXN0ZW5jeSAobm8gY29uZmxpY3RzLCBicmVhayBvbmx5IHRvIGV4aXN0aW5nIGxhYmVscylcbi8vICAgaXMgbm90IGVuZm9yY2VkLlxuLy9cbi8vIC0gQm9ndXMgSWRlbnRpZmllciBub2RlcyB3aXRoIGEgbmFtZSBvZiBgXCLinJZcImAgYXJlIGluc2VydGVkIHdoZW5ldmVyXG4vLyAgIHRoZSBwYXJzZXIgZ290IHRvbyBjb25mdXNlZCB0byByZXR1cm4gYW55dGhpbmcgbWVhbmluZ2Z1bC5cbi8vXG4vLyBbYXBpXTogaHR0cHM6Ly9kZXZlbG9wZXIubW96aWxsYS5vcmcvZW4tVVMvZG9jcy9TcGlkZXJNb25rZXkvUGFyc2VyX0FQSVxuLy9cbi8vIFRoZSBleHBlY3RlZCB1c2UgZm9yIHRoaXMgaXMgdG8gKmZpcnN0KiB0cnkgYGFjb3JuLnBhcnNlYCwgYW5kIG9ubHlcbi8vIGlmIHRoYXQgZmFpbHMgc3dpdGNoIHRvIGBwYXJzZV9kYW1taXRgLiBUaGUgbG9vc2UgcGFyc2VyIG1pZ2h0XG4vLyBwYXJzZSBiYWRseSBpbmRlbnRlZCBjb2RlIGluY29ycmVjdGx5LCBzbyAqKmRvbid0KiogdXNlIGl0IGFzXG4vLyB5b3VyIGRlZmF1bHQgcGFyc2VyLlxuLy9cbi8vIFF1aXRlIGEgbG90IG9mIGFjb3JuLmpzIGlzIGR1cGxpY2F0ZWQgaGVyZS4gVGhlIGFsdGVybmF0aXZlIHdhcyB0b1xuLy8gYWRkIGEgKmxvdCogb2YgZXh0cmEgY3J1ZnQgdG8gdGhhdCBmaWxlLCBtYWtpbmcgaXQgbGVzcyByZWFkYWJsZVxuLy8gYW5kIHNsb3dlci4gQ29weWluZyBhbmQgZWRpdGluZyB0aGUgY29kZSBhbGxvd2VkIG1lIHRvIG1ha2Vcbi8vIGludmFzaXZlIGNoYW5nZXMgYW5kIHNpbXBsaWZpY2F0aW9ucyB3aXRob3V0IGNyZWF0aW5nIGEgY29tcGxpY2F0ZWRcbi8vIHRhbmdsZS5cblxudmFyIGFjb3JuID0gX2ludGVyb3BSZXF1aXJlV2lsZGNhcmQoX2RlcmVxXyhcIi4uXCIpKTtcblxudmFyIF9zdGF0ZSA9IF9kZXJlcV8oXCIuL3N0YXRlXCIpO1xuXG52YXIgTG9vc2VQYXJzZXIgPSBfc3RhdGUuTG9vc2VQYXJzZXI7XG5cbl9kZXJlcV8oXCIuL3Rva2VuaXplXCIpO1xuXG5fZGVyZXFfKFwiLi9wYXJzZXV0aWxcIik7XG5cbl9kZXJlcV8oXCIuL3N0YXRlbWVudFwiKTtcblxuX2RlcmVxXyhcIi4vZXhwcmVzc2lvblwiKTtcblxuZXhwb3J0cy5Mb29zZVBhcnNlciA9IF9zdGF0ZS5Mb29zZVBhcnNlcjtcblxuYWNvcm4uZGVmYXVsdE9wdGlvbnMudGFiU2l6ZSA9IDQ7XG5cbmZ1bmN0aW9uIHBhcnNlX2RhbW1pdChpbnB1dCwgb3B0aW9ucykge1xuICB2YXIgcCA9IG5ldyBMb29zZVBhcnNlcihpbnB1dCwgb3B0aW9ucyk7XG4gIHAubmV4dCgpO1xuICByZXR1cm4gcC5wYXJzZVRvcExldmVsKCk7XG59XG5cbmFjb3JuLnBhcnNlX2RhbW1pdCA9IHBhcnNlX2RhbW1pdDtcbmFjb3JuLkxvb3NlUGFyc2VyID0gTG9vc2VQYXJzZXI7XG5cbn0se1wiLi5cIjozLFwiLi9leHByZXNzaW9uXCI6NCxcIi4vcGFyc2V1dGlsXCI6NSxcIi4vc3RhdGVcIjo2LFwiLi9zdGF0ZW1lbnRcIjo3LFwiLi90b2tlbml6ZVwiOjh9XSwyOltmdW5jdGlvbihfZGVyZXFfLG1vZHVsZSxleHBvcnRzKXtcbihmdW5jdGlvbiAoZ2xvYmFsKXtcblwidXNlIHN0cmljdFwiOyhmdW5jdGlvbihmKXtpZih0eXBlb2YgZXhwb3J0cyA9PT0gXCJvYmplY3RcIiAmJiB0eXBlb2YgbW9kdWxlICE9PSBcInVuZGVmaW5lZFwiKXttb2R1bGUuZXhwb3J0cyA9IGYoKTt9ZWxzZSBpZih0eXBlb2YgZGVmaW5lID09PSBcImZ1bmN0aW9uXCIgJiYgZGVmaW5lLmFtZCl7ZGVmaW5lKFtdLCBmKTt9ZWxzZSB7dmFyIGc7aWYodHlwZW9mIHdpbmRvdyAhPT0gXCJ1bmRlZmluZWRcIil7ZyA9IHdpbmRvdzt9ZWxzZSBpZih0eXBlb2YgZ2xvYmFsICE9PSBcInVuZGVmaW5lZFwiKXtnID0gZ2xvYmFsO31lbHNlIGlmKHR5cGVvZiBzZWxmICE9PSBcInVuZGVmaW5lZFwiKXtnID0gc2VsZjt9ZWxzZSB7ZyA9IHRoaXM7fWcuYWNvcm4gPSBmKCk7fX0pKGZ1bmN0aW9uKCl7dmFyIGRlZmluZSwgbW9kdWxlLCBleHBvcnRzO3JldHVybiAoZnVuY3Rpb24gZSh0LCBuLCByKXtmdW5jdGlvbiBzKG8sIHUpe2lmKCFuW29dKXtpZighdFtvXSl7dmFyIGE9dHlwZW9mIF9kZXJlcV8gPT0gXCJmdW5jdGlvblwiICYmIF9kZXJlcV87aWYoIXUgJiYgYSl7cmV0dXJuIGEobywgITApO31pZihpKXtyZXR1cm4gaShvLCAhMCk7fXZhciBmPW5ldyBFcnJvcihcIkNhbm5vdCBmaW5kIG1vZHVsZSAnXCIgKyBvICsgXCInXCIpO3Rocm93IChmLmNvZGUgPSBcIk1PRFVMRV9OT1RfRk9VTkRcIiwgZik7fXZhciBsPW5bb10gPSB7ZXhwb3J0czp7fX07dFtvXVswXS5jYWxsKGwuZXhwb3J0cywgZnVuY3Rpb24oZSl7dmFyIG49dFtvXVsxXVtlXTtyZXR1cm4gcyhuP246ZSk7fSwgbCwgbC5leHBvcnRzLCBlLCB0LCBuLCByKTt9cmV0dXJuIG5bb10uZXhwb3J0czt9dmFyIGk9dHlwZW9mIF9kZXJlcV8gPT0gXCJmdW5jdGlvblwiICYmIF9kZXJlcV87Zm9yKHZhciBvPTA7IG8gPCByLmxlbmd0aDsgbysrKSBzKHJbb10pO3JldHVybiBzO30pKHsxOltmdW5jdGlvbihfZGVyZXFfLCBtb2R1bGUsIGV4cG9ydHMpe1widXNlIHN0cmljdFwiO2V4cG9ydHMucGFyc2UgPSBwYXJzZTtleHBvcnRzLnBhcnNlRXhwcmVzc2lvbkF0ID0gcGFyc2VFeHByZXNzaW9uQXQ7ZXhwb3J0cy50b2tlbml6ZXIgPSB0b2tlbml6ZXI7ZXhwb3J0cy5fX2VzTW9kdWxlID0gdHJ1ZTt2YXIgX3N0YXRlPV9kZXJlcV8oXCIuL3N0YXRlXCIpO3ZhciBQYXJzZXI9X3N0YXRlLlBhcnNlcjt2YXIgX29wdGlvbnM9X2RlcmVxXyhcIi4vb3B0aW9uc1wiKTt2YXIgZ2V0T3B0aW9ucz1fb3B0aW9ucy5nZXRPcHRpb25zO19kZXJlcV8oXCIuL3BhcnNldXRpbFwiKTtfZGVyZXFfKFwiLi9zdGF0ZW1lbnRcIik7X2RlcmVxXyhcIi4vbHZhbFwiKTtfZGVyZXFfKFwiLi9leHByZXNzaW9uXCIpO2V4cG9ydHMuUGFyc2VyID0gX3N0YXRlLlBhcnNlcjtleHBvcnRzLnBsdWdpbnMgPSBfc3RhdGUucGx1Z2lucztleHBvcnRzLmRlZmF1bHRPcHRpb25zID0gX29wdGlvbnMuZGVmYXVsdE9wdGlvbnM7dmFyIF9sb2NhdGlvbj1fZGVyZXFfKFwiLi9sb2NhdGlvblwiKTtleHBvcnRzLlNvdXJjZUxvY2F0aW9uID0gX2xvY2F0aW9uLlNvdXJjZUxvY2F0aW9uO2V4cG9ydHMuZ2V0TGluZUluZm8gPSBfbG9jYXRpb24uZ2V0TGluZUluZm87ZXhwb3J0cy5Ob2RlID0gX2RlcmVxXyhcIi4vbm9kZVwiKS5Ob2RlO3ZhciBfdG9rZW50eXBlPV9kZXJlcV8oXCIuL3Rva2VudHlwZVwiKTtleHBvcnRzLlRva2VuVHlwZSA9IF90b2tlbnR5cGUuVG9rZW5UeXBlO2V4cG9ydHMudG9rVHlwZXMgPSBfdG9rZW50eXBlLnR5cGVzO3ZhciBfdG9rZW5jb250ZXh0PV9kZXJlcV8oXCIuL3Rva2VuY29udGV4dFwiKTtleHBvcnRzLlRva0NvbnRleHQgPSBfdG9rZW5jb250ZXh0LlRva0NvbnRleHQ7ZXhwb3J0cy50b2tDb250ZXh0cyA9IF90b2tlbmNvbnRleHQudHlwZXM7dmFyIF9pZGVudGlmaWVyPV9kZXJlcV8oXCIuL2lkZW50aWZpZXJcIik7ZXhwb3J0cy5pc0lkZW50aWZpZXJDaGFyID0gX2lkZW50aWZpZXIuaXNJZGVudGlmaWVyQ2hhcjtleHBvcnRzLmlzSWRlbnRpZmllclN0YXJ0ID0gX2lkZW50aWZpZXIuaXNJZGVudGlmaWVyU3RhcnQ7ZXhwb3J0cy5Ub2tlbiA9IF9kZXJlcV8oXCIuL3Rva2VuaXplXCIpLlRva2VuO3ZhciBfd2hpdGVzcGFjZT1fZGVyZXFfKFwiLi93aGl0ZXNwYWNlXCIpO2V4cG9ydHMuaXNOZXdMaW5lID0gX3doaXRlc3BhY2UuaXNOZXdMaW5lO2V4cG9ydHMubGluZUJyZWFrID0gX3doaXRlc3BhY2UubGluZUJyZWFrO2V4cG9ydHMubGluZUJyZWFrRyA9IF93aGl0ZXNwYWNlLmxpbmVCcmVha0c7dmFyIHZlcnNpb249XCIxLjIuMlwiO2V4cG9ydHMudmVyc2lvbiA9IHZlcnNpb247ZnVuY3Rpb24gcGFyc2UoaW5wdXQsIG9wdGlvbnMpe3ZhciBwPXBhcnNlcihvcHRpb25zLCBpbnB1dCk7dmFyIHN0YXJ0UG9zPXAucG9zLCBzdGFydExvYz1wLm9wdGlvbnMubG9jYXRpb25zICYmIHAuY3VyUG9zaXRpb24oKTtwLm5leHRUb2tlbigpO3JldHVybiBwLnBhcnNlVG9wTGV2ZWwocC5vcHRpb25zLnByb2dyYW0gfHwgcC5zdGFydE5vZGVBdChzdGFydFBvcywgc3RhcnRMb2MpKTt9ZnVuY3Rpb24gcGFyc2VFeHByZXNzaW9uQXQoaW5wdXQsIHBvcywgb3B0aW9ucyl7dmFyIHA9cGFyc2VyKG9wdGlvbnMsIGlucHV0LCBwb3MpO3AubmV4dFRva2VuKCk7cmV0dXJuIHAucGFyc2VFeHByZXNzaW9uKCk7fWZ1bmN0aW9uIHRva2VuaXplcihpbnB1dCwgb3B0aW9ucyl7cmV0dXJuIHBhcnNlcihvcHRpb25zLCBpbnB1dCk7fWZ1bmN0aW9uIHBhcnNlcihvcHRpb25zLCBpbnB1dCl7cmV0dXJuIG5ldyBQYXJzZXIoZ2V0T3B0aW9ucyhvcHRpb25zKSwgU3RyaW5nKGlucHV0KSk7fX0sIHtcIi4vZXhwcmVzc2lvblwiOjYsIFwiLi9pZGVudGlmaWVyXCI6NywgXCIuL2xvY2F0aW9uXCI6OCwgXCIuL2x2YWxcIjo5LCBcIi4vbm9kZVwiOjEwLCBcIi4vb3B0aW9uc1wiOjExLCBcIi4vcGFyc2V1dGlsXCI6MTIsIFwiLi9zdGF0ZVwiOjEzLCBcIi4vc3RhdGVtZW50XCI6MTQsIFwiLi90b2tlbmNvbnRleHRcIjoxNSwgXCIuL3Rva2VuaXplXCI6MTYsIFwiLi90b2tlbnR5cGVcIjoxNywgXCIuL3doaXRlc3BhY2VcIjoxOX1dLCAyOltmdW5jdGlvbihfZGVyZXFfLCBtb2R1bGUsIGV4cG9ydHMpe2lmKHR5cGVvZiBPYmplY3QuY3JlYXRlID09PSBcImZ1bmN0aW9uXCIpe21vZHVsZS5leHBvcnRzID0gZnVuY3Rpb24gaW5oZXJpdHMoY3Rvciwgc3VwZXJDdG9yKXtjdG9yLnN1cGVyXyA9IHN1cGVyQ3RvcjtjdG9yLnByb3RvdHlwZSA9IE9iamVjdC5jcmVhdGUoc3VwZXJDdG9yLnByb3RvdHlwZSwge2NvbnN0cnVjdG9yOnt2YWx1ZTpjdG9yLCBlbnVtZXJhYmxlOmZhbHNlLCB3cml0YWJsZTp0cnVlLCBjb25maWd1cmFibGU6dHJ1ZX19KTt9O31lbHNlIHttb2R1bGUuZXhwb3J0cyA9IGZ1bmN0aW9uIGluaGVyaXRzKGN0b3IsIHN1cGVyQ3Rvcil7Y3Rvci5zdXBlcl8gPSBzdXBlckN0b3I7dmFyIFRlbXBDdG9yPWZ1bmN0aW9uIFRlbXBDdG9yKCl7fTtUZW1wQ3Rvci5wcm90b3R5cGUgPSBzdXBlckN0b3IucHJvdG90eXBlO2N0b3IucHJvdG90eXBlID0gbmV3IFRlbXBDdG9yKCk7Y3Rvci5wcm90b3R5cGUuY29uc3RydWN0b3IgPSBjdG9yO307fX0sIHt9XSwgMzpbZnVuY3Rpb24oX2RlcmVxXywgbW9kdWxlLCBleHBvcnRzKXt2YXIgcHJvY2Vzcz1tb2R1bGUuZXhwb3J0cyA9IHt9O3ZhciBxdWV1ZT1bXTt2YXIgZHJhaW5pbmc9ZmFsc2U7ZnVuY3Rpb24gZHJhaW5RdWV1ZSgpe2lmKGRyYWluaW5nKXtyZXR1cm47fWRyYWluaW5nID0gdHJ1ZTt2YXIgY3VycmVudFF1ZXVlO3ZhciBsZW49cXVldWUubGVuZ3RoO3doaWxlKGxlbikge2N1cnJlbnRRdWV1ZSA9IHF1ZXVlO3F1ZXVlID0gW107dmFyIGk9LTE7d2hpbGUoKytpIDwgbGVuKSB7Y3VycmVudFF1ZXVlW2ldKCk7fWxlbiA9IHF1ZXVlLmxlbmd0aDt9ZHJhaW5pbmcgPSBmYWxzZTt9cHJvY2Vzcy5uZXh0VGljayA9IGZ1bmN0aW9uKGZ1bil7cXVldWUucHVzaChmdW4pO2lmKCFkcmFpbmluZyl7c2V0VGltZW91dChkcmFpblF1ZXVlLCAwKTt9fTtwcm9jZXNzLnRpdGxlID0gXCJicm93c2VyXCI7cHJvY2Vzcy5icm93c2VyID0gdHJ1ZTtwcm9jZXNzLmVudiA9IHt9O3Byb2Nlc3MuYXJndiA9IFtdO3Byb2Nlc3MudmVyc2lvbiA9IFwiXCI7cHJvY2Vzcy52ZXJzaW9ucyA9IHt9O2Z1bmN0aW9uIG5vb3AoKXt9cHJvY2Vzcy5vbiA9IG5vb3A7cHJvY2Vzcy5hZGRMaXN0ZW5lciA9IG5vb3A7cHJvY2Vzcy5vbmNlID0gbm9vcDtwcm9jZXNzLm9mZiA9IG5vb3A7cHJvY2Vzcy5yZW1vdmVMaXN0ZW5lciA9IG5vb3A7cHJvY2Vzcy5yZW1vdmVBbGxMaXN0ZW5lcnMgPSBub29wO3Byb2Nlc3MuZW1pdCA9IG5vb3A7cHJvY2Vzcy5iaW5kaW5nID0gZnVuY3Rpb24obmFtZSl7dGhyb3cgbmV3IEVycm9yKFwicHJvY2Vzcy5iaW5kaW5nIGlzIG5vdCBzdXBwb3J0ZWRcIik7fTtwcm9jZXNzLmN3ZCA9IGZ1bmN0aW9uKCl7cmV0dXJuIFwiL1wiO307cHJvY2Vzcy5jaGRpciA9IGZ1bmN0aW9uKGRpcil7dGhyb3cgbmV3IEVycm9yKFwicHJvY2Vzcy5jaGRpciBpcyBub3Qgc3VwcG9ydGVkXCIpO307cHJvY2Vzcy51bWFzayA9IGZ1bmN0aW9uKCl7cmV0dXJuIDA7fTt9LCB7fV0sIDQ6W2Z1bmN0aW9uKF9kZXJlcV8sIG1vZHVsZSwgZXhwb3J0cyl7bW9kdWxlLmV4cG9ydHMgPSBmdW5jdGlvbiBpc0J1ZmZlcihhcmcpe3JldHVybiBhcmcgJiYgdHlwZW9mIGFyZyA9PT0gXCJvYmplY3RcIiAmJiB0eXBlb2YgYXJnLmNvcHkgPT09IFwiZnVuY3Rpb25cIiAmJiB0eXBlb2YgYXJnLmZpbGwgPT09IFwiZnVuY3Rpb25cIiAmJiB0eXBlb2YgYXJnLnJlYWRVSW50OCA9PT0gXCJmdW5jdGlvblwiO307fSwge31dLCA1OltmdW5jdGlvbihfZGVyZXFfLCBtb2R1bGUsIGV4cG9ydHMpeyhmdW5jdGlvbihwcm9jZXNzLCBnbG9iYWwpe3ZhciBmb3JtYXRSZWdFeHA9LyVbc2RqJV0vZztleHBvcnRzLmZvcm1hdCA9IGZ1bmN0aW9uKGYpe2lmKCFpc1N0cmluZyhmKSl7dmFyIG9iamVjdHM9W107Zm9yKHZhciBpPTA7IGkgPCBhcmd1bWVudHMubGVuZ3RoOyBpKyspIHtvYmplY3RzLnB1c2goaW5zcGVjdChhcmd1bWVudHNbaV0pKTt9cmV0dXJuIG9iamVjdHMuam9pbihcIiBcIik7fXZhciBpPTE7dmFyIGFyZ3M9YXJndW1lbnRzO3ZhciBsZW49YXJncy5sZW5ndGg7dmFyIHN0cj1TdHJpbmcoZikucmVwbGFjZShmb3JtYXRSZWdFeHAsIGZ1bmN0aW9uKHgpe2lmKHggPT09IFwiJSVcIilyZXR1cm4gXCIlXCI7aWYoaSA+PSBsZW4pcmV0dXJuIHg7c3dpdGNoKHgpe2Nhc2UgXCIlc1wiOnJldHVybiBTdHJpbmcoYXJnc1tpKytdKTtjYXNlIFwiJWRcIjpyZXR1cm4gTnVtYmVyKGFyZ3NbaSsrXSk7Y2FzZSBcIiVqXCI6dHJ5e3JldHVybiBKU09OLnN0cmluZ2lmeShhcmdzW2krK10pO31jYXRjaChfKSB7cmV0dXJuIFwiW0NpcmN1bGFyXVwiO31kZWZhdWx0OnJldHVybiB4O319KTtmb3IodmFyIHg9YXJnc1tpXTsgaSA8IGxlbjsgeCA9IGFyZ3NbKytpXSkge2lmKGlzTnVsbCh4KSB8fCAhaXNPYmplY3QoeCkpe3N0ciArPSBcIiBcIiArIHg7fWVsc2Uge3N0ciArPSBcIiBcIiArIGluc3BlY3QoeCk7fX1yZXR1cm4gc3RyO307ZXhwb3J0cy5kZXByZWNhdGUgPSBmdW5jdGlvbihmbiwgbXNnKXtpZihpc1VuZGVmaW5lZChnbG9iYWwucHJvY2Vzcykpe3JldHVybiBmdW5jdGlvbigpe3JldHVybiBleHBvcnRzLmRlcHJlY2F0ZShmbiwgbXNnKS5hcHBseSh0aGlzLCBhcmd1bWVudHMpO307fWlmKHByb2Nlc3Mubm9EZXByZWNhdGlvbiA9PT0gdHJ1ZSl7cmV0dXJuIGZuO312YXIgd2FybmVkPWZhbHNlO2Z1bmN0aW9uIGRlcHJlY2F0ZWQoKXtpZighd2FybmVkKXtpZihwcm9jZXNzLnRocm93RGVwcmVjYXRpb24pe3Rocm93IG5ldyBFcnJvcihtc2cpO31lbHNlIGlmKHByb2Nlc3MudHJhY2VEZXByZWNhdGlvbil7Y29uc29sZS50cmFjZShtc2cpO31lbHNlIHtjb25zb2xlLmVycm9yKG1zZyk7fXdhcm5lZCA9IHRydWU7fXJldHVybiBmbi5hcHBseSh0aGlzLCBhcmd1bWVudHMpO31yZXR1cm4gZGVwcmVjYXRlZDt9O3ZhciBkZWJ1Z3M9e307dmFyIGRlYnVnRW52aXJvbjtleHBvcnRzLmRlYnVnbG9nID0gZnVuY3Rpb24oc2V0KXtpZihpc1VuZGVmaW5lZChkZWJ1Z0Vudmlyb24pKWRlYnVnRW52aXJvbiA9IHByb2Nlc3MuZW52Lk5PREVfREVCVUcgfHwgXCJcIjtzZXQgPSBzZXQudG9VcHBlckNhc2UoKTtpZighZGVidWdzW3NldF0pe2lmKG5ldyBSZWdFeHAoXCJcXFxcYlwiICsgc2V0ICsgXCJcXFxcYlwiLCBcImlcIikudGVzdChkZWJ1Z0Vudmlyb24pKXt2YXIgcGlkPXByb2Nlc3MucGlkO2RlYnVnc1tzZXRdID0gZnVuY3Rpb24oKXt2YXIgbXNnPWV4cG9ydHMuZm9ybWF0LmFwcGx5KGV4cG9ydHMsIGFyZ3VtZW50cyk7Y29uc29sZS5lcnJvcihcIiVzICVkOiAlc1wiLCBzZXQsIHBpZCwgbXNnKTt9O31lbHNlIHtkZWJ1Z3Nbc2V0XSA9IGZ1bmN0aW9uKCl7fTt9fXJldHVybiBkZWJ1Z3Nbc2V0XTt9O2Z1bmN0aW9uIGluc3BlY3Qob2JqLCBvcHRzKXt2YXIgY3R4PXtzZWVuOltdLCBzdHlsaXplOnN0eWxpemVOb0NvbG9yfTtpZihhcmd1bWVudHMubGVuZ3RoID49IDMpY3R4LmRlcHRoID0gYXJndW1lbnRzWzJdO2lmKGFyZ3VtZW50cy5sZW5ndGggPj0gNCljdHguY29sb3JzID0gYXJndW1lbnRzWzNdO2lmKGlzQm9vbGVhbihvcHRzKSl7Y3R4LnNob3dIaWRkZW4gPSBvcHRzO31lbHNlIGlmKG9wdHMpe2V4cG9ydHMuX2V4dGVuZChjdHgsIG9wdHMpO31pZihpc1VuZGVmaW5lZChjdHguc2hvd0hpZGRlbikpY3R4LnNob3dIaWRkZW4gPSBmYWxzZTtpZihpc1VuZGVmaW5lZChjdHguZGVwdGgpKWN0eC5kZXB0aCA9IDI7aWYoaXNVbmRlZmluZWQoY3R4LmNvbG9ycykpY3R4LmNvbG9ycyA9IGZhbHNlO2lmKGlzVW5kZWZpbmVkKGN0eC5jdXN0b21JbnNwZWN0KSljdHguY3VzdG9tSW5zcGVjdCA9IHRydWU7aWYoY3R4LmNvbG9ycyljdHguc3R5bGl6ZSA9IHN0eWxpemVXaXRoQ29sb3I7cmV0dXJuIGZvcm1hdFZhbHVlKGN0eCwgb2JqLCBjdHguZGVwdGgpO31leHBvcnRzLmluc3BlY3QgPSBpbnNwZWN0O2luc3BlY3QuY29sb3JzID0ge2JvbGQ6WzEsIDIyXSwgaXRhbGljOlszLCAyM10sIHVuZGVybGluZTpbNCwgMjRdLCBpbnZlcnNlOls3LCAyN10sIHdoaXRlOlszNywgMzldLCBncmV5Ols5MCwgMzldLCBibGFjazpbMzAsIDM5XSwgYmx1ZTpbMzQsIDM5XSwgY3lhbjpbMzYsIDM5XSwgZ3JlZW46WzMyLCAzOV0sIG1hZ2VudGE6WzM1LCAzOV0sIHJlZDpbMzEsIDM5XSwgeWVsbG93OlszMywgMzldfTtpbnNwZWN0LnN0eWxlcyA9IHtzcGVjaWFsOlwiY3lhblwiLCBudW1iZXI6XCJ5ZWxsb3dcIiwgYm9vbGVhbjpcInllbGxvd1wiLCB1bmRlZmluZWQ6XCJncmV5XCIsIFwibnVsbFwiOlwiYm9sZFwiLCBzdHJpbmc6XCJncmVlblwiLCBkYXRlOlwibWFnZW50YVwiLCByZWdleHA6XCJyZWRcIn07ZnVuY3Rpb24gc3R5bGl6ZVdpdGhDb2xvcihzdHIsIHN0eWxlVHlwZSl7dmFyIHN0eWxlPWluc3BlY3Quc3R5bGVzW3N0eWxlVHlwZV07aWYoc3R5bGUpe3JldHVybiBcIlxcdTAwMWJbXCIgKyBpbnNwZWN0LmNvbG9yc1tzdHlsZV1bMF0gKyBcIm1cIiArIHN0ciArIFwiXFx1MDAxYltcIiArIGluc3BlY3QuY29sb3JzW3N0eWxlXVsxXSArIFwibVwiO31lbHNlIHtyZXR1cm4gc3RyO319ZnVuY3Rpb24gc3R5bGl6ZU5vQ29sb3Ioc3RyLCBzdHlsZVR5cGUpe3JldHVybiBzdHI7fWZ1bmN0aW9uIGFycmF5VG9IYXNoKGFycmF5KXt2YXIgaGFzaD17fTthcnJheS5mb3JFYWNoKGZ1bmN0aW9uKHZhbCwgaWR4KXtoYXNoW3ZhbF0gPSB0cnVlO30pO3JldHVybiBoYXNoO31mdW5jdGlvbiBmb3JtYXRWYWx1ZShjdHgsIHZhbHVlLCByZWN1cnNlVGltZXMpe2lmKGN0eC5jdXN0b21JbnNwZWN0ICYmIHZhbHVlICYmIGlzRnVuY3Rpb24odmFsdWUuaW5zcGVjdCkgJiYgdmFsdWUuaW5zcGVjdCAhPT0gZXhwb3J0cy5pbnNwZWN0ICYmICEodmFsdWUuY29uc3RydWN0b3IgJiYgdmFsdWUuY29uc3RydWN0b3IucHJvdG90eXBlID09PSB2YWx1ZSkpe3ZhciByZXQ9dmFsdWUuaW5zcGVjdChyZWN1cnNlVGltZXMsIGN0eCk7aWYoIWlzU3RyaW5nKHJldCkpe3JldCA9IGZvcm1hdFZhbHVlKGN0eCwgcmV0LCByZWN1cnNlVGltZXMpO31yZXR1cm4gcmV0O312YXIgcHJpbWl0aXZlPWZvcm1hdFByaW1pdGl2ZShjdHgsIHZhbHVlKTtpZihwcmltaXRpdmUpe3JldHVybiBwcmltaXRpdmU7fXZhciBrZXlzPU9iamVjdC5rZXlzKHZhbHVlKTt2YXIgdmlzaWJsZUtleXM9YXJyYXlUb0hhc2goa2V5cyk7aWYoY3R4LnNob3dIaWRkZW4pe2tleXMgPSBPYmplY3QuZ2V0T3duUHJvcGVydHlOYW1lcyh2YWx1ZSk7fWlmKGlzRXJyb3IodmFsdWUpICYmIChrZXlzLmluZGV4T2YoXCJtZXNzYWdlXCIpID49IDAgfHwga2V5cy5pbmRleE9mKFwiZGVzY3JpcHRpb25cIikgPj0gMCkpe3JldHVybiBmb3JtYXRFcnJvcih2YWx1ZSk7fWlmKGtleXMubGVuZ3RoID09PSAwKXtpZihpc0Z1bmN0aW9uKHZhbHVlKSl7dmFyIG5hbWU9dmFsdWUubmFtZT9cIjogXCIgKyB2YWx1ZS5uYW1lOlwiXCI7cmV0dXJuIGN0eC5zdHlsaXplKFwiW0Z1bmN0aW9uXCIgKyBuYW1lICsgXCJdXCIsIFwic3BlY2lhbFwiKTt9aWYoaXNSZWdFeHAodmFsdWUpKXtyZXR1cm4gY3R4LnN0eWxpemUoUmVnRXhwLnByb3RvdHlwZS50b1N0cmluZy5jYWxsKHZhbHVlKSwgXCJyZWdleHBcIik7fWlmKGlzRGF0ZSh2YWx1ZSkpe3JldHVybiBjdHguc3R5bGl6ZShEYXRlLnByb3RvdHlwZS50b1N0cmluZy5jYWxsKHZhbHVlKSwgXCJkYXRlXCIpO31pZihpc0Vycm9yKHZhbHVlKSl7cmV0dXJuIGZvcm1hdEVycm9yKHZhbHVlKTt9fXZhciBiYXNlPVwiXCIsIGFycmF5PWZhbHNlLCBicmFjZXM9W1wie1wiLCBcIn1cIl07aWYoaXNBcnJheSh2YWx1ZSkpe2FycmF5ID0gdHJ1ZTticmFjZXMgPSBbXCJbXCIsIFwiXVwiXTt9aWYoaXNGdW5jdGlvbih2YWx1ZSkpe3ZhciBuPXZhbHVlLm5hbWU/XCI6IFwiICsgdmFsdWUubmFtZTpcIlwiO2Jhc2UgPSBcIiBbRnVuY3Rpb25cIiArIG4gKyBcIl1cIjt9aWYoaXNSZWdFeHAodmFsdWUpKXtiYXNlID0gXCIgXCIgKyBSZWdFeHAucHJvdG90eXBlLnRvU3RyaW5nLmNhbGwodmFsdWUpO31pZihpc0RhdGUodmFsdWUpKXtiYXNlID0gXCIgXCIgKyBEYXRlLnByb3RvdHlwZS50b1VUQ1N0cmluZy5jYWxsKHZhbHVlKTt9aWYoaXNFcnJvcih2YWx1ZSkpe2Jhc2UgPSBcIiBcIiArIGZvcm1hdEVycm9yKHZhbHVlKTt9aWYoa2V5cy5sZW5ndGggPT09IDAgJiYgKCFhcnJheSB8fCB2YWx1ZS5sZW5ndGggPT0gMCkpe3JldHVybiBicmFjZXNbMF0gKyBiYXNlICsgYnJhY2VzWzFdO31pZihyZWN1cnNlVGltZXMgPCAwKXtpZihpc1JlZ0V4cCh2YWx1ZSkpe3JldHVybiBjdHguc3R5bGl6ZShSZWdFeHAucHJvdG90eXBlLnRvU3RyaW5nLmNhbGwodmFsdWUpLCBcInJlZ2V4cFwiKTt9ZWxzZSB7cmV0dXJuIGN0eC5zdHlsaXplKFwiW09iamVjdF1cIiwgXCJzcGVjaWFsXCIpO319Y3R4LnNlZW4ucHVzaCh2YWx1ZSk7dmFyIG91dHB1dDtpZihhcnJheSl7b3V0cHV0ID0gZm9ybWF0QXJyYXkoY3R4LCB2YWx1ZSwgcmVjdXJzZVRpbWVzLCB2aXNpYmxlS2V5cywga2V5cyk7fWVsc2Uge291dHB1dCA9IGtleXMubWFwKGZ1bmN0aW9uKGtleSl7cmV0dXJuIGZvcm1hdFByb3BlcnR5KGN0eCwgdmFsdWUsIHJlY3Vyc2VUaW1lcywgdmlzaWJsZUtleXMsIGtleSwgYXJyYXkpO30pO31jdHguc2Vlbi5wb3AoKTtyZXR1cm4gcmVkdWNlVG9TaW5nbGVTdHJpbmcob3V0cHV0LCBiYXNlLCBicmFjZXMpO31mdW5jdGlvbiBmb3JtYXRQcmltaXRpdmUoY3R4LCB2YWx1ZSl7aWYoaXNVbmRlZmluZWQodmFsdWUpKXtyZXR1cm4gY3R4LnN0eWxpemUoXCJ1bmRlZmluZWRcIiwgXCJ1bmRlZmluZWRcIik7fWlmKGlzU3RyaW5nKHZhbHVlKSl7dmFyIHNpbXBsZT1cIidcIiArIEpTT04uc3RyaW5naWZ5KHZhbHVlKS5yZXBsYWNlKC9eXCJ8XCIkL2csIFwiXCIpLnJlcGxhY2UoLycvZywgXCJcXFxcJ1wiKS5yZXBsYWNlKC9cXFxcXCIvZywgXCJcXFwiXCIpICsgXCInXCI7cmV0dXJuIGN0eC5zdHlsaXplKHNpbXBsZSwgXCJzdHJpbmdcIik7fWlmKGlzTnVtYmVyKHZhbHVlKSl7cmV0dXJuIGN0eC5zdHlsaXplKFwiXCIgKyB2YWx1ZSwgXCJudW1iZXJcIik7fWlmKGlzQm9vbGVhbih2YWx1ZSkpe3JldHVybiBjdHguc3R5bGl6ZShcIlwiICsgdmFsdWUsIFwiYm9vbGVhblwiKTt9aWYoaXNOdWxsKHZhbHVlKSl7cmV0dXJuIGN0eC5zdHlsaXplKFwibnVsbFwiLCBcIm51bGxcIik7fX1mdW5jdGlvbiBmb3JtYXRFcnJvcih2YWx1ZSl7cmV0dXJuIFwiW1wiICsgRXJyb3IucHJvdG90eXBlLnRvU3RyaW5nLmNhbGwodmFsdWUpICsgXCJdXCI7fWZ1bmN0aW9uIGZvcm1hdEFycmF5KGN0eCwgdmFsdWUsIHJlY3Vyc2VUaW1lcywgdmlzaWJsZUtleXMsIGtleXMpe3ZhciBvdXRwdXQ9W107Zm9yKHZhciBpPTAsIGw9dmFsdWUubGVuZ3RoOyBpIDwgbDsgKytpKSB7aWYoaGFzT3duUHJvcGVydHkodmFsdWUsIFN0cmluZyhpKSkpe291dHB1dC5wdXNoKGZvcm1hdFByb3BlcnR5KGN0eCwgdmFsdWUsIHJlY3Vyc2VUaW1lcywgdmlzaWJsZUtleXMsIFN0cmluZyhpKSwgdHJ1ZSkpO31lbHNlIHtvdXRwdXQucHVzaChcIlwiKTt9fWtleXMuZm9yRWFjaChmdW5jdGlvbihrZXkpe2lmKCFrZXkubWF0Y2goL15cXGQrJC8pKXtvdXRwdXQucHVzaChmb3JtYXRQcm9wZXJ0eShjdHgsIHZhbHVlLCByZWN1cnNlVGltZXMsIHZpc2libGVLZXlzLCBrZXksIHRydWUpKTt9fSk7cmV0dXJuIG91dHB1dDt9ZnVuY3Rpb24gZm9ybWF0UHJvcGVydHkoY3R4LCB2YWx1ZSwgcmVjdXJzZVRpbWVzLCB2aXNpYmxlS2V5cywga2V5LCBhcnJheSl7dmFyIG5hbWUsIHN0ciwgZGVzYztkZXNjID0gT2JqZWN0LmdldE93blByb3BlcnR5RGVzY3JpcHRvcih2YWx1ZSwga2V5KSB8fCB7dmFsdWU6dmFsdWVba2V5XX07aWYoZGVzYy5nZXQpe2lmKGRlc2Muc2V0KXtzdHIgPSBjdHguc3R5bGl6ZShcIltHZXR0ZXIvU2V0dGVyXVwiLCBcInNwZWNpYWxcIik7fWVsc2Uge3N0ciA9IGN0eC5zdHlsaXplKFwiW0dldHRlcl1cIiwgXCJzcGVjaWFsXCIpO319ZWxzZSB7aWYoZGVzYy5zZXQpe3N0ciA9IGN0eC5zdHlsaXplKFwiW1NldHRlcl1cIiwgXCJzcGVjaWFsXCIpO319aWYoIWhhc093blByb3BlcnR5KHZpc2libGVLZXlzLCBrZXkpKXtuYW1lID0gXCJbXCIgKyBrZXkgKyBcIl1cIjt9aWYoIXN0cil7aWYoY3R4LnNlZW4uaW5kZXhPZihkZXNjLnZhbHVlKSA8IDApe2lmKGlzTnVsbChyZWN1cnNlVGltZXMpKXtzdHIgPSBmb3JtYXRWYWx1ZShjdHgsIGRlc2MudmFsdWUsIG51bGwpO31lbHNlIHtzdHIgPSBmb3JtYXRWYWx1ZShjdHgsIGRlc2MudmFsdWUsIHJlY3Vyc2VUaW1lcyAtIDEpO31pZihzdHIuaW5kZXhPZihcIlxcblwiKSA+IC0xKXtpZihhcnJheSl7c3RyID0gc3RyLnNwbGl0KFwiXFxuXCIpLm1hcChmdW5jdGlvbihsaW5lKXtyZXR1cm4gXCIgIFwiICsgbGluZTt9KS5qb2luKFwiXFxuXCIpLnN1YnN0cigyKTt9ZWxzZSB7c3RyID0gXCJcXG5cIiArIHN0ci5zcGxpdChcIlxcblwiKS5tYXAoZnVuY3Rpb24obGluZSl7cmV0dXJuIFwiICAgXCIgKyBsaW5lO30pLmpvaW4oXCJcXG5cIik7fX19ZWxzZSB7c3RyID0gY3R4LnN0eWxpemUoXCJbQ2lyY3VsYXJdXCIsIFwic3BlY2lhbFwiKTt9fWlmKGlzVW5kZWZpbmVkKG5hbWUpKXtpZihhcnJheSAmJiBrZXkubWF0Y2goL15cXGQrJC8pKXtyZXR1cm4gc3RyO31uYW1lID0gSlNPTi5zdHJpbmdpZnkoXCJcIiArIGtleSk7aWYobmFtZS5tYXRjaCgvXlwiKFthLXpBLVpfXVthLXpBLVpfMC05XSopXCIkLykpe25hbWUgPSBuYW1lLnN1YnN0cigxLCBuYW1lLmxlbmd0aCAtIDIpO25hbWUgPSBjdHguc3R5bGl6ZShuYW1lLCBcIm5hbWVcIik7fWVsc2Uge25hbWUgPSBuYW1lLnJlcGxhY2UoLycvZywgXCJcXFxcJ1wiKS5yZXBsYWNlKC9cXFxcXCIvZywgXCJcXFwiXCIpLnJlcGxhY2UoLyheXCJ8XCIkKS9nLCBcIidcIik7bmFtZSA9IGN0eC5zdHlsaXplKG5hbWUsIFwic3RyaW5nXCIpO319cmV0dXJuIG5hbWUgKyBcIjogXCIgKyBzdHI7fWZ1bmN0aW9uIHJlZHVjZVRvU2luZ2xlU3RyaW5nKG91dHB1dCwgYmFzZSwgYnJhY2VzKXt2YXIgbnVtTGluZXNFc3Q9MDt2YXIgbGVuZ3RoPW91dHB1dC5yZWR1Y2UoZnVuY3Rpb24ocHJldiwgY3VyKXtudW1MaW5lc0VzdCsrO2lmKGN1ci5pbmRleE9mKFwiXFxuXCIpID49IDApbnVtTGluZXNFc3QrKztyZXR1cm4gcHJldiArIGN1ci5yZXBsYWNlKC9cXHUwMDFiXFxbXFxkXFxkP20vZywgXCJcIikubGVuZ3RoICsgMTt9LCAwKTtpZihsZW5ndGggPiA2MCl7cmV0dXJuIGJyYWNlc1swXSArIChiYXNlID09PSBcIlwiP1wiXCI6YmFzZSArIFwiXFxuIFwiKSArIFwiIFwiICsgb3V0cHV0LmpvaW4oXCIsXFxuICBcIikgKyBcIiBcIiArIGJyYWNlc1sxXTt9cmV0dXJuIGJyYWNlc1swXSArIGJhc2UgKyBcIiBcIiArIG91dHB1dC5qb2luKFwiLCBcIikgKyBcIiBcIiArIGJyYWNlc1sxXTt9ZnVuY3Rpb24gaXNBcnJheShhcil7cmV0dXJuIEFycmF5LmlzQXJyYXkoYXIpO31leHBvcnRzLmlzQXJyYXkgPSBpc0FycmF5O2Z1bmN0aW9uIGlzQm9vbGVhbihhcmcpe3JldHVybiB0eXBlb2YgYXJnID09PSBcImJvb2xlYW5cIjt9ZXhwb3J0cy5pc0Jvb2xlYW4gPSBpc0Jvb2xlYW47ZnVuY3Rpb24gaXNOdWxsKGFyZyl7cmV0dXJuIGFyZyA9PT0gbnVsbDt9ZXhwb3J0cy5pc051bGwgPSBpc051bGw7ZnVuY3Rpb24gaXNOdWxsT3JVbmRlZmluZWQoYXJnKXtyZXR1cm4gYXJnID09IG51bGw7fWV4cG9ydHMuaXNOdWxsT3JVbmRlZmluZWQgPSBpc051bGxPclVuZGVmaW5lZDtmdW5jdGlvbiBpc051bWJlcihhcmcpe3JldHVybiB0eXBlb2YgYXJnID09PSBcIm51bWJlclwiO31leHBvcnRzLmlzTnVtYmVyID0gaXNOdW1iZXI7ZnVuY3Rpb24gaXNTdHJpbmcoYXJnKXtyZXR1cm4gdHlwZW9mIGFyZyA9PT0gXCJzdHJpbmdcIjt9ZXhwb3J0cy5pc1N0cmluZyA9IGlzU3RyaW5nO2Z1bmN0aW9uIGlzU3ltYm9sKGFyZyl7cmV0dXJuIHR5cGVvZiBhcmcgPT09IFwic3ltYm9sXCI7fWV4cG9ydHMuaXNTeW1ib2wgPSBpc1N5bWJvbDtmdW5jdGlvbiBpc1VuZGVmaW5lZChhcmcpe3JldHVybiBhcmcgPT09IHZvaWQgMDt9ZXhwb3J0cy5pc1VuZGVmaW5lZCA9IGlzVW5kZWZpbmVkO2Z1bmN0aW9uIGlzUmVnRXhwKHJlKXtyZXR1cm4gaXNPYmplY3QocmUpICYmIG9iamVjdFRvU3RyaW5nKHJlKSA9PT0gXCJbb2JqZWN0IFJlZ0V4cF1cIjt9ZXhwb3J0cy5pc1JlZ0V4cCA9IGlzUmVnRXhwO2Z1bmN0aW9uIGlzT2JqZWN0KGFyZyl7cmV0dXJuIHR5cGVvZiBhcmcgPT09IFwib2JqZWN0XCIgJiYgYXJnICE9PSBudWxsO31leHBvcnRzLmlzT2JqZWN0ID0gaXNPYmplY3Q7ZnVuY3Rpb24gaXNEYXRlKGQpe3JldHVybiBpc09iamVjdChkKSAmJiBvYmplY3RUb1N0cmluZyhkKSA9PT0gXCJbb2JqZWN0IERhdGVdXCI7fWV4cG9ydHMuaXNEYXRlID0gaXNEYXRlO2Z1bmN0aW9uIGlzRXJyb3IoZSl7cmV0dXJuIGlzT2JqZWN0KGUpICYmIChvYmplY3RUb1N0cmluZyhlKSA9PT0gXCJbb2JqZWN0IEVycm9yXVwiIHx8IGUgaW5zdGFuY2VvZiBFcnJvcik7fWV4cG9ydHMuaXNFcnJvciA9IGlzRXJyb3I7ZnVuY3Rpb24gaXNGdW5jdGlvbihhcmcpe3JldHVybiB0eXBlb2YgYXJnID09PSBcImZ1bmN0aW9uXCI7fWV4cG9ydHMuaXNGdW5jdGlvbiA9IGlzRnVuY3Rpb247ZnVuY3Rpb24gaXNQcmltaXRpdmUoYXJnKXtyZXR1cm4gYXJnID09PSBudWxsIHx8IHR5cGVvZiBhcmcgPT09IFwiYm9vbGVhblwiIHx8IHR5cGVvZiBhcmcgPT09IFwibnVtYmVyXCIgfHwgdHlwZW9mIGFyZyA9PT0gXCJzdHJpbmdcIiB8fCB0eXBlb2YgYXJnID09PSBcInN5bWJvbFwiIHx8IHR5cGVvZiBhcmcgPT09IFwidW5kZWZpbmVkXCI7fWV4cG9ydHMuaXNQcmltaXRpdmUgPSBpc1ByaW1pdGl2ZTtleHBvcnRzLmlzQnVmZmVyID0gX2RlcmVxXyhcIi4vc3VwcG9ydC9pc0J1ZmZlclwiKTtmdW5jdGlvbiBvYmplY3RUb1N0cmluZyhvKXtyZXR1cm4gT2JqZWN0LnByb3RvdHlwZS50b1N0cmluZy5jYWxsKG8pO31mdW5jdGlvbiBwYWQobil7cmV0dXJuIG4gPCAxMD9cIjBcIiArIG4udG9TdHJpbmcoMTApOm4udG9TdHJpbmcoMTApO312YXIgbW9udGhzPVtcIkphblwiLCBcIkZlYlwiLCBcIk1hclwiLCBcIkFwclwiLCBcIk1heVwiLCBcIkp1blwiLCBcIkp1bFwiLCBcIkF1Z1wiLCBcIlNlcFwiLCBcIk9jdFwiLCBcIk5vdlwiLCBcIkRlY1wiXTtmdW5jdGlvbiB0aW1lc3RhbXAoKXt2YXIgZD1uZXcgRGF0ZSgpO3ZhciB0aW1lPVtwYWQoZC5nZXRIb3VycygpKSwgcGFkKGQuZ2V0TWludXRlcygpKSwgcGFkKGQuZ2V0U2Vjb25kcygpKV0uam9pbihcIjpcIik7cmV0dXJuIFtkLmdldERhdGUoKSwgbW9udGhzW2QuZ2V0TW9udGgoKV0sIHRpbWVdLmpvaW4oXCIgXCIpO31leHBvcnRzLmxvZyA9IGZ1bmN0aW9uKCl7Y29uc29sZS5sb2coXCIlcyAtICVzXCIsIHRpbWVzdGFtcCgpLCBleHBvcnRzLmZvcm1hdC5hcHBseShleHBvcnRzLCBhcmd1bWVudHMpKTt9O2V4cG9ydHMuaW5oZXJpdHMgPSBfZGVyZXFfKFwiaW5oZXJpdHNcIik7ZXhwb3J0cy5fZXh0ZW5kID0gZnVuY3Rpb24ob3JpZ2luLCBhZGQpe2lmKCFhZGQgfHwgIWlzT2JqZWN0KGFkZCkpcmV0dXJuIG9yaWdpbjt2YXIga2V5cz1PYmplY3Qua2V5cyhhZGQpO3ZhciBpPWtleXMubGVuZ3RoO3doaWxlKGktLSkge29yaWdpbltrZXlzW2ldXSA9IGFkZFtrZXlzW2ldXTt9cmV0dXJuIG9yaWdpbjt9O2Z1bmN0aW9uIGhhc093blByb3BlcnR5KG9iaiwgcHJvcCl7cmV0dXJuIE9iamVjdC5wcm90b3R5cGUuaGFzT3duUHJvcGVydHkuY2FsbChvYmosIHByb3ApO319KS5jYWxsKHRoaXMsIF9kZXJlcV8oXCJfcHJvY2Vzc1wiKSwgdHlwZW9mIGdsb2JhbCAhPT0gXCJ1bmRlZmluZWRcIj9nbG9iYWw6dHlwZW9mIHNlbGYgIT09IFwidW5kZWZpbmVkXCI/c2VsZjp0eXBlb2Ygd2luZG93ICE9PSBcInVuZGVmaW5lZFwiP3dpbmRvdzp7fSk7fSwge1wiLi9zdXBwb3J0L2lzQnVmZmVyXCI6NCwgX3Byb2Nlc3M6MywgaW5oZXJpdHM6Mn1dLCA2OltmdW5jdGlvbihfZGVyZXFfLCBtb2R1bGUsIGV4cG9ydHMpe1widXNlIHN0cmljdFwiO3ZhciB0dD1fZGVyZXFfKFwiLi90b2tlbnR5cGVcIikudHlwZXM7dmFyIFBhcnNlcj1fZGVyZXFfKFwiLi9zdGF0ZVwiKS5QYXJzZXI7dmFyIHJlc2VydmVkV29yZHM9X2RlcmVxXyhcIi4vaWRlbnRpZmllclwiKS5yZXNlcnZlZFdvcmRzO3ZhciBoYXM9X2RlcmVxXyhcIi4vdXRpbFwiKS5oYXM7dmFyIHBwPVBhcnNlci5wcm90b3R5cGU7cHAuY2hlY2tQcm9wQ2xhc2ggPSBmdW5jdGlvbihwcm9wLCBwcm9wSGFzaCl7aWYodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYpcmV0dXJuO3ZhciBrZXk9cHJvcC5rZXksIG5hbWU9dW5kZWZpbmVkO3N3aXRjaChrZXkudHlwZSl7Y2FzZSBcIklkZW50aWZpZXJcIjpuYW1lID0ga2V5Lm5hbWU7YnJlYWs7Y2FzZSBcIkxpdGVyYWxcIjpuYW1lID0gU3RyaW5nKGtleS52YWx1ZSk7YnJlYWs7ZGVmYXVsdDpyZXR1cm47fXZhciBraW5kPXByb3Aua2luZCB8fCBcImluaXRcIiwgb3RoZXI9dW5kZWZpbmVkO2lmKGhhcyhwcm9wSGFzaCwgbmFtZSkpe290aGVyID0gcHJvcEhhc2hbbmFtZV07dmFyIGlzR2V0U2V0PWtpbmQgIT09IFwiaW5pdFwiO2lmKCh0aGlzLnN0cmljdCB8fCBpc0dldFNldCkgJiYgb3RoZXJba2luZF0gfHwgIShpc0dldFNldCBeIG90aGVyLmluaXQpKXRoaXMucmFpc2Uoa2V5LnN0YXJ0LCBcIlJlZGVmaW5pdGlvbiBvZiBwcm9wZXJ0eVwiKTt9ZWxzZSB7b3RoZXIgPSBwcm9wSGFzaFtuYW1lXSA9IHtpbml0OmZhbHNlLCBnZXQ6ZmFsc2UsIHNldDpmYWxzZX07fW90aGVyW2tpbmRdID0gdHJ1ZTt9O3BwLnBhcnNlRXhwcmVzc2lvbiA9IGZ1bmN0aW9uKG5vSW4sIHJlZlNob3J0aGFuZERlZmF1bHRQb3Mpe3ZhciBzdGFydFBvcz10aGlzLnN0YXJ0LCBzdGFydExvYz10aGlzLnN0YXJ0TG9jO3ZhciBleHByPXRoaXMucGFyc2VNYXliZUFzc2lnbihub0luLCByZWZTaG9ydGhhbmREZWZhdWx0UG9zKTtpZih0aGlzLnR5cGUgPT09IHR0LmNvbW1hKXt2YXIgbm9kZT10aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0UG9zLCBzdGFydExvYyk7bm9kZS5leHByZXNzaW9ucyA9IFtleHByXTt3aGlsZSh0aGlzLmVhdCh0dC5jb21tYSkpIG5vZGUuZXhwcmVzc2lvbnMucHVzaCh0aGlzLnBhcnNlTWF5YmVBc3NpZ24obm9JbiwgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcykpO3JldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJTZXF1ZW5jZUV4cHJlc3Npb25cIik7fXJldHVybiBleHByO307cHAucGFyc2VNYXliZUFzc2lnbiA9IGZ1bmN0aW9uKG5vSW4sIHJlZlNob3J0aGFuZERlZmF1bHRQb3MsIGFmdGVyTGVmdFBhcnNlKXtpZih0aGlzLnR5cGUgPT0gdHQuX3lpZWxkICYmIHRoaXMuaW5HZW5lcmF0b3IpcmV0dXJuIHRoaXMucGFyc2VZaWVsZCgpO3ZhciBmYWlsT25TaG9ydGhhbmRBc3NpZ249dW5kZWZpbmVkO2lmKCFyZWZTaG9ydGhhbmREZWZhdWx0UG9zKXtyZWZTaG9ydGhhbmREZWZhdWx0UG9zID0ge3N0YXJ0OjB9O2ZhaWxPblNob3J0aGFuZEFzc2lnbiA9IHRydWU7fWVsc2Uge2ZhaWxPblNob3J0aGFuZEFzc2lnbiA9IGZhbHNlO312YXIgc3RhcnRQb3M9dGhpcy5zdGFydCwgc3RhcnRMb2M9dGhpcy5zdGFydExvYztpZih0aGlzLnR5cGUgPT0gdHQucGFyZW5MIHx8IHRoaXMudHlwZSA9PSB0dC5uYW1lKXRoaXMucG90ZW50aWFsQXJyb3dBdCA9IHRoaXMuc3RhcnQ7dmFyIGxlZnQ9dGhpcy5wYXJzZU1heWJlQ29uZGl0aW9uYWwobm9JbiwgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcyk7aWYoYWZ0ZXJMZWZ0UGFyc2UpbGVmdCA9IGFmdGVyTGVmdFBhcnNlLmNhbGwodGhpcywgbGVmdCwgc3RhcnRQb3MsIHN0YXJ0TG9jKTtpZih0aGlzLnR5cGUuaXNBc3NpZ24pe3ZhciBub2RlPXRoaXMuc3RhcnROb2RlQXQoc3RhcnRQb3MsIHN0YXJ0TG9jKTtub2RlLm9wZXJhdG9yID0gdGhpcy52YWx1ZTtub2RlLmxlZnQgPSB0aGlzLnR5cGUgPT09IHR0LmVxP3RoaXMudG9Bc3NpZ25hYmxlKGxlZnQpOmxlZnQ7cmVmU2hvcnRoYW5kRGVmYXVsdFBvcy5zdGFydCA9IDA7dGhpcy5jaGVja0xWYWwobGVmdCk7dGhpcy5uZXh0KCk7bm9kZS5yaWdodCA9IHRoaXMucGFyc2VNYXliZUFzc2lnbihub0luKTtyZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiQXNzaWdubWVudEV4cHJlc3Npb25cIik7fWVsc2UgaWYoZmFpbE9uU2hvcnRoYW5kQXNzaWduICYmIHJlZlNob3J0aGFuZERlZmF1bHRQb3Muc3RhcnQpe3RoaXMudW5leHBlY3RlZChyZWZTaG9ydGhhbmREZWZhdWx0UG9zLnN0YXJ0KTt9cmV0dXJuIGxlZnQ7fTtwcC5wYXJzZU1heWJlQ29uZGl0aW9uYWwgPSBmdW5jdGlvbihub0luLCByZWZTaG9ydGhhbmREZWZhdWx0UG9zKXt2YXIgc3RhcnRQb3M9dGhpcy5zdGFydCwgc3RhcnRMb2M9dGhpcy5zdGFydExvYzt2YXIgZXhwcj10aGlzLnBhcnNlRXhwck9wcyhub0luLCByZWZTaG9ydGhhbmREZWZhdWx0UG9zKTtpZihyZWZTaG9ydGhhbmREZWZhdWx0UG9zICYmIHJlZlNob3J0aGFuZERlZmF1bHRQb3Muc3RhcnQpcmV0dXJuIGV4cHI7aWYodGhpcy5lYXQodHQucXVlc3Rpb24pKXt2YXIgbm9kZT10aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0UG9zLCBzdGFydExvYyk7bm9kZS50ZXN0ID0gZXhwcjtub2RlLmNvbnNlcXVlbnQgPSB0aGlzLnBhcnNlTWF5YmVBc3NpZ24oKTt0aGlzLmV4cGVjdCh0dC5jb2xvbik7bm9kZS5hbHRlcm5hdGUgPSB0aGlzLnBhcnNlTWF5YmVBc3NpZ24obm9Jbik7cmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkNvbmRpdGlvbmFsRXhwcmVzc2lvblwiKTt9cmV0dXJuIGV4cHI7fTtwcC5wYXJzZUV4cHJPcHMgPSBmdW5jdGlvbihub0luLCByZWZTaG9ydGhhbmREZWZhdWx0UG9zKXt2YXIgc3RhcnRQb3M9dGhpcy5zdGFydCwgc3RhcnRMb2M9dGhpcy5zdGFydExvYzt2YXIgZXhwcj10aGlzLnBhcnNlTWF5YmVVbmFyeShyZWZTaG9ydGhhbmREZWZhdWx0UG9zKTtpZihyZWZTaG9ydGhhbmREZWZhdWx0UG9zICYmIHJlZlNob3J0aGFuZERlZmF1bHRQb3Muc3RhcnQpcmV0dXJuIGV4cHI7cmV0dXJuIHRoaXMucGFyc2VFeHByT3AoZXhwciwgc3RhcnRQb3MsIHN0YXJ0TG9jLCAtMSwgbm9Jbik7fTtwcC5wYXJzZUV4cHJPcCA9IGZ1bmN0aW9uKGxlZnQsIGxlZnRTdGFydFBvcywgbGVmdFN0YXJ0TG9jLCBtaW5QcmVjLCBub0luKXt2YXIgcHJlYz10aGlzLnR5cGUuYmlub3A7aWYoQXJyYXkuaXNBcnJheShsZWZ0U3RhcnRQb3MpKXtpZih0aGlzLm9wdGlvbnMubG9jYXRpb25zICYmIG5vSW4gPT09IHVuZGVmaW5lZCl7bm9JbiA9IG1pblByZWM7bWluUHJlYyA9IGxlZnRTdGFydExvYztsZWZ0U3RhcnRMb2MgPSBsZWZ0U3RhcnRQb3NbMV07bGVmdFN0YXJ0UG9zID0gbGVmdFN0YXJ0UG9zWzBdO319aWYocHJlYyAhPSBudWxsICYmICghbm9JbiB8fCB0aGlzLnR5cGUgIT09IHR0Ll9pbikpe2lmKHByZWMgPiBtaW5QcmVjKXt2YXIgbm9kZT10aGlzLnN0YXJ0Tm9kZUF0KGxlZnRTdGFydFBvcywgbGVmdFN0YXJ0TG9jKTtub2RlLmxlZnQgPSBsZWZ0O25vZGUub3BlcmF0b3IgPSB0aGlzLnZhbHVlO3ZhciBvcD10aGlzLnR5cGU7dGhpcy5uZXh0KCk7dmFyIHN0YXJ0UG9zPXRoaXMuc3RhcnQsIHN0YXJ0TG9jPXRoaXMuc3RhcnRMb2M7bm9kZS5yaWdodCA9IHRoaXMucGFyc2VFeHByT3AodGhpcy5wYXJzZU1heWJlVW5hcnkoKSwgc3RhcnRQb3MsIHN0YXJ0TG9jLCBwcmVjLCBub0luKTt0aGlzLmZpbmlzaE5vZGUobm9kZSwgb3AgPT09IHR0LmxvZ2ljYWxPUiB8fCBvcCA9PT0gdHQubG9naWNhbEFORD9cIkxvZ2ljYWxFeHByZXNzaW9uXCI6XCJCaW5hcnlFeHByZXNzaW9uXCIpO3JldHVybiB0aGlzLnBhcnNlRXhwck9wKG5vZGUsIGxlZnRTdGFydFBvcywgbGVmdFN0YXJ0TG9jLCBtaW5QcmVjLCBub0luKTt9fXJldHVybiBsZWZ0O307cHAucGFyc2VNYXliZVVuYXJ5ID0gZnVuY3Rpb24ocmVmU2hvcnRoYW5kRGVmYXVsdFBvcyl7aWYodGhpcy50eXBlLnByZWZpeCl7dmFyIG5vZGU9dGhpcy5zdGFydE5vZGUoKSwgdXBkYXRlPXRoaXMudHlwZSA9PT0gdHQuaW5jRGVjO25vZGUub3BlcmF0b3IgPSB0aGlzLnZhbHVlO25vZGUucHJlZml4ID0gdHJ1ZTt0aGlzLm5leHQoKTtub2RlLmFyZ3VtZW50ID0gdGhpcy5wYXJzZU1heWJlVW5hcnkoKTtpZihyZWZTaG9ydGhhbmREZWZhdWx0UG9zICYmIHJlZlNob3J0aGFuZERlZmF1bHRQb3Muc3RhcnQpdGhpcy51bmV4cGVjdGVkKHJlZlNob3J0aGFuZERlZmF1bHRQb3Muc3RhcnQpO2lmKHVwZGF0ZSl0aGlzLmNoZWNrTFZhbChub2RlLmFyZ3VtZW50KTtlbHNlIGlmKHRoaXMuc3RyaWN0ICYmIG5vZGUub3BlcmF0b3IgPT09IFwiZGVsZXRlXCIgJiYgbm9kZS5hcmd1bWVudC50eXBlID09PSBcIklkZW50aWZpZXJcIil0aGlzLnJhaXNlKG5vZGUuc3RhcnQsIFwiRGVsZXRpbmcgbG9jYWwgdmFyaWFibGUgaW4gc3RyaWN0IG1vZGVcIik7cmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCB1cGRhdGU/XCJVcGRhdGVFeHByZXNzaW9uXCI6XCJVbmFyeUV4cHJlc3Npb25cIik7fXZhciBzdGFydFBvcz10aGlzLnN0YXJ0LCBzdGFydExvYz10aGlzLnN0YXJ0TG9jO3ZhciBleHByPXRoaXMucGFyc2VFeHByU3Vic2NyaXB0cyhyZWZTaG9ydGhhbmREZWZhdWx0UG9zKTtpZihyZWZTaG9ydGhhbmREZWZhdWx0UG9zICYmIHJlZlNob3J0aGFuZERlZmF1bHRQb3Muc3RhcnQpcmV0dXJuIGV4cHI7d2hpbGUodGhpcy50eXBlLnBvc3RmaXggJiYgIXRoaXMuY2FuSW5zZXJ0U2VtaWNvbG9uKCkpIHt2YXIgbm9kZT10aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0UG9zLCBzdGFydExvYyk7bm9kZS5vcGVyYXRvciA9IHRoaXMudmFsdWU7bm9kZS5wcmVmaXggPSBmYWxzZTtub2RlLmFyZ3VtZW50ID0gZXhwcjt0aGlzLmNoZWNrTFZhbChleHByKTt0aGlzLm5leHQoKTtleHByID0gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiVXBkYXRlRXhwcmVzc2lvblwiKTt9cmV0dXJuIGV4cHI7fTtwcC5wYXJzZUV4cHJTdWJzY3JpcHRzID0gZnVuY3Rpb24ocmVmU2hvcnRoYW5kRGVmYXVsdFBvcyl7dmFyIHN0YXJ0UG9zPXRoaXMuc3RhcnQsIHN0YXJ0TG9jPXRoaXMuc3RhcnRMb2M7dmFyIGV4cHI9dGhpcy5wYXJzZUV4cHJBdG9tKHJlZlNob3J0aGFuZERlZmF1bHRQb3MpO2lmKHJlZlNob3J0aGFuZERlZmF1bHRQb3MgJiYgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcy5zdGFydClyZXR1cm4gZXhwcjtyZXR1cm4gdGhpcy5wYXJzZVN1YnNjcmlwdHMoZXhwciwgc3RhcnRQb3MsIHN0YXJ0TG9jKTt9O3BwLnBhcnNlU3Vic2NyaXB0cyA9IGZ1bmN0aW9uKGJhc2UsIHN0YXJ0UG9zLCBzdGFydExvYywgbm9DYWxscyl7aWYoQXJyYXkuaXNBcnJheShzdGFydFBvcykpe2lmKHRoaXMub3B0aW9ucy5sb2NhdGlvbnMgJiYgbm9DYWxscyA9PT0gdW5kZWZpbmVkKXtub0NhbGxzID0gc3RhcnRMb2M7c3RhcnRMb2MgPSBzdGFydFBvc1sxXTtzdGFydFBvcyA9IHN0YXJ0UG9zWzBdO319Zm9yKDs7KSB7aWYodGhpcy5lYXQodHQuZG90KSl7dmFyIG5vZGU9dGhpcy5zdGFydE5vZGVBdChzdGFydFBvcywgc3RhcnRMb2MpO25vZGUub2JqZWN0ID0gYmFzZTtub2RlLnByb3BlcnR5ID0gdGhpcy5wYXJzZUlkZW50KHRydWUpO25vZGUuY29tcHV0ZWQgPSBmYWxzZTtiYXNlID0gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiTWVtYmVyRXhwcmVzc2lvblwiKTt9ZWxzZSBpZih0aGlzLmVhdCh0dC5icmFja2V0TCkpe3ZhciBub2RlPXRoaXMuc3RhcnROb2RlQXQoc3RhcnRQb3MsIHN0YXJ0TG9jKTtub2RlLm9iamVjdCA9IGJhc2U7bm9kZS5wcm9wZXJ0eSA9IHRoaXMucGFyc2VFeHByZXNzaW9uKCk7bm9kZS5jb21wdXRlZCA9IHRydWU7dGhpcy5leHBlY3QodHQuYnJhY2tldFIpO2Jhc2UgPSB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJNZW1iZXJFeHByZXNzaW9uXCIpO31lbHNlIGlmKCFub0NhbGxzICYmIHRoaXMuZWF0KHR0LnBhcmVuTCkpe3ZhciBub2RlPXRoaXMuc3RhcnROb2RlQXQoc3RhcnRQb3MsIHN0YXJ0TG9jKTtub2RlLmNhbGxlZSA9IGJhc2U7bm9kZS5hcmd1bWVudHMgPSB0aGlzLnBhcnNlRXhwckxpc3QodHQucGFyZW5SLCBmYWxzZSk7YmFzZSA9IHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkNhbGxFeHByZXNzaW9uXCIpO31lbHNlIGlmKHRoaXMudHlwZSA9PT0gdHQuYmFja1F1b3RlKXt2YXIgbm9kZT10aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0UG9zLCBzdGFydExvYyk7bm9kZS50YWcgPSBiYXNlO25vZGUucXVhc2kgPSB0aGlzLnBhcnNlVGVtcGxhdGUoKTtiYXNlID0gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiVGFnZ2VkVGVtcGxhdGVFeHByZXNzaW9uXCIpO31lbHNlIHtyZXR1cm4gYmFzZTt9fX07cHAucGFyc2VFeHByQXRvbSA9IGZ1bmN0aW9uKHJlZlNob3J0aGFuZERlZmF1bHRQb3Mpe3ZhciBub2RlPXVuZGVmaW5lZCwgY2FuQmVBcnJvdz10aGlzLnBvdGVudGlhbEFycm93QXQgPT0gdGhpcy5zdGFydDtzd2l0Y2godGhpcy50eXBlKXtjYXNlIHR0Ll90aGlzOmNhc2UgdHQuX3N1cGVyOnZhciB0eXBlPXRoaXMudHlwZSA9PT0gdHQuX3RoaXM/XCJUaGlzRXhwcmVzc2lvblwiOlwiU3VwZXJcIjtub2RlID0gdGhpcy5zdGFydE5vZGUoKTt0aGlzLm5leHQoKTtyZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIHR5cGUpO2Nhc2UgdHQuX3lpZWxkOmlmKHRoaXMuaW5HZW5lcmF0b3IpdGhpcy51bmV4cGVjdGVkKCk7Y2FzZSB0dC5uYW1lOnZhciBzdGFydFBvcz10aGlzLnN0YXJ0LCBzdGFydExvYz10aGlzLnN0YXJ0TG9jO3ZhciBpZD10aGlzLnBhcnNlSWRlbnQodGhpcy50eXBlICE9PSB0dC5uYW1lKTtpZihjYW5CZUFycm93ICYmICF0aGlzLmNhbkluc2VydFNlbWljb2xvbigpICYmIHRoaXMuZWF0KHR0LmFycm93KSlyZXR1cm4gdGhpcy5wYXJzZUFycm93RXhwcmVzc2lvbih0aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0UG9zLCBzdGFydExvYyksIFtpZF0pO3JldHVybiBpZDtjYXNlIHR0LnJlZ2V4cDp2YXIgdmFsdWU9dGhpcy52YWx1ZTtub2RlID0gdGhpcy5wYXJzZUxpdGVyYWwodmFsdWUudmFsdWUpO25vZGUucmVnZXggPSB7cGF0dGVybjp2YWx1ZS5wYXR0ZXJuLCBmbGFnczp2YWx1ZS5mbGFnc307cmV0dXJuIG5vZGU7Y2FzZSB0dC5udW06Y2FzZSB0dC5zdHJpbmc6cmV0dXJuIHRoaXMucGFyc2VMaXRlcmFsKHRoaXMudmFsdWUpO2Nhc2UgdHQuX251bGw6Y2FzZSB0dC5fdHJ1ZTpjYXNlIHR0Ll9mYWxzZTpub2RlID0gdGhpcy5zdGFydE5vZGUoKTtub2RlLnZhbHVlID0gdGhpcy50eXBlID09PSB0dC5fbnVsbD9udWxsOnRoaXMudHlwZSA9PT0gdHQuX3RydWU7bm9kZS5yYXcgPSB0aGlzLnR5cGUua2V5d29yZDt0aGlzLm5leHQoKTtyZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiTGl0ZXJhbFwiKTtjYXNlIHR0LnBhcmVuTDpyZXR1cm4gdGhpcy5wYXJzZVBhcmVuQW5kRGlzdGluZ3Vpc2hFeHByZXNzaW9uKGNhbkJlQXJyb3cpO2Nhc2UgdHQuYnJhY2tldEw6bm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7dGhpcy5uZXh0KCk7aWYodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDcgJiYgdGhpcy50eXBlID09PSB0dC5fZm9yKXtyZXR1cm4gdGhpcy5wYXJzZUNvbXByZWhlbnNpb24obm9kZSwgZmFsc2UpO31ub2RlLmVsZW1lbnRzID0gdGhpcy5wYXJzZUV4cHJMaXN0KHR0LmJyYWNrZXRSLCB0cnVlLCB0cnVlLCByZWZTaG9ydGhhbmREZWZhdWx0UG9zKTtyZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiQXJyYXlFeHByZXNzaW9uXCIpO2Nhc2UgdHQuYnJhY2VMOnJldHVybiB0aGlzLnBhcnNlT2JqKGZhbHNlLCByZWZTaG9ydGhhbmREZWZhdWx0UG9zKTtjYXNlIHR0Ll9mdW5jdGlvbjpub2RlID0gdGhpcy5zdGFydE5vZGUoKTt0aGlzLm5leHQoKTtyZXR1cm4gdGhpcy5wYXJzZUZ1bmN0aW9uKG5vZGUsIGZhbHNlKTtjYXNlIHR0Ll9jbGFzczpyZXR1cm4gdGhpcy5wYXJzZUNsYXNzKHRoaXMuc3RhcnROb2RlKCksIGZhbHNlKTtjYXNlIHR0Ll9uZXc6cmV0dXJuIHRoaXMucGFyc2VOZXcoKTtjYXNlIHR0LmJhY2tRdW90ZTpyZXR1cm4gdGhpcy5wYXJzZVRlbXBsYXRlKCk7ZGVmYXVsdDp0aGlzLnVuZXhwZWN0ZWQoKTt9fTtwcC5wYXJzZUxpdGVyYWwgPSBmdW5jdGlvbih2YWx1ZSl7dmFyIG5vZGU9dGhpcy5zdGFydE5vZGUoKTtub2RlLnZhbHVlID0gdmFsdWU7bm9kZS5yYXcgPSB0aGlzLmlucHV0LnNsaWNlKHRoaXMuc3RhcnQsIHRoaXMuZW5kKTt0aGlzLm5leHQoKTtyZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiTGl0ZXJhbFwiKTt9O3BwLnBhcnNlUGFyZW5FeHByZXNzaW9uID0gZnVuY3Rpb24oKXt0aGlzLmV4cGVjdCh0dC5wYXJlbkwpO3ZhciB2YWw9dGhpcy5wYXJzZUV4cHJlc3Npb24oKTt0aGlzLmV4cGVjdCh0dC5wYXJlblIpO3JldHVybiB2YWw7fTtwcC5wYXJzZVBhcmVuQW5kRGlzdGluZ3Vpc2hFeHByZXNzaW9uID0gZnVuY3Rpb24oY2FuQmVBcnJvdyl7dmFyIHN0YXJ0UG9zPXRoaXMuc3RhcnQsIHN0YXJ0TG9jPXRoaXMuc3RhcnRMb2MsIHZhbD11bmRlZmluZWQ7aWYodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYpe3RoaXMubmV4dCgpO2lmKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA3ICYmIHRoaXMudHlwZSA9PT0gdHQuX2Zvcil7cmV0dXJuIHRoaXMucGFyc2VDb21wcmVoZW5zaW9uKHRoaXMuc3RhcnROb2RlQXQoc3RhcnRQb3MsIHN0YXJ0TG9jKSwgdHJ1ZSk7fXZhciBpbm5lclN0YXJ0UG9zPXRoaXMuc3RhcnQsIGlubmVyU3RhcnRMb2M9dGhpcy5zdGFydExvYzt2YXIgZXhwckxpc3Q9W10sIGZpcnN0PXRydWU7dmFyIHJlZlNob3J0aGFuZERlZmF1bHRQb3M9e3N0YXJ0OjB9LCBzcHJlYWRTdGFydD11bmRlZmluZWQsIGlubmVyUGFyZW5TdGFydD11bmRlZmluZWQ7d2hpbGUodGhpcy50eXBlICE9PSB0dC5wYXJlblIpIHtmaXJzdD9maXJzdCA9IGZhbHNlOnRoaXMuZXhwZWN0KHR0LmNvbW1hKTtpZih0aGlzLnR5cGUgPT09IHR0LmVsbGlwc2lzKXtzcHJlYWRTdGFydCA9IHRoaXMuc3RhcnQ7ZXhwckxpc3QucHVzaCh0aGlzLnBhcnNlUGFyZW5JdGVtKHRoaXMucGFyc2VSZXN0KCkpKTticmVhazt9ZWxzZSB7aWYodGhpcy50eXBlID09PSB0dC5wYXJlbkwgJiYgIWlubmVyUGFyZW5TdGFydCl7aW5uZXJQYXJlblN0YXJ0ID0gdGhpcy5zdGFydDt9ZXhwckxpc3QucHVzaCh0aGlzLnBhcnNlTWF5YmVBc3NpZ24oZmFsc2UsIHJlZlNob3J0aGFuZERlZmF1bHRQb3MsIHRoaXMucGFyc2VQYXJlbkl0ZW0pKTt9fXZhciBpbm5lckVuZFBvcz10aGlzLnN0YXJ0LCBpbm5lckVuZExvYz10aGlzLnN0YXJ0TG9jO3RoaXMuZXhwZWN0KHR0LnBhcmVuUik7aWYoY2FuQmVBcnJvdyAmJiAhdGhpcy5jYW5JbnNlcnRTZW1pY29sb24oKSAmJiB0aGlzLmVhdCh0dC5hcnJvdykpe2lmKGlubmVyUGFyZW5TdGFydCl0aGlzLnVuZXhwZWN0ZWQoaW5uZXJQYXJlblN0YXJ0KTtyZXR1cm4gdGhpcy5wYXJzZVBhcmVuQXJyb3dMaXN0KHN0YXJ0UG9zLCBzdGFydExvYywgZXhwckxpc3QpO31pZighZXhwckxpc3QubGVuZ3RoKXRoaXMudW5leHBlY3RlZCh0aGlzLmxhc3RUb2tTdGFydCk7aWYoc3ByZWFkU3RhcnQpdGhpcy51bmV4cGVjdGVkKHNwcmVhZFN0YXJ0KTtpZihyZWZTaG9ydGhhbmREZWZhdWx0UG9zLnN0YXJ0KXRoaXMudW5leHBlY3RlZChyZWZTaG9ydGhhbmREZWZhdWx0UG9zLnN0YXJ0KTtpZihleHByTGlzdC5sZW5ndGggPiAxKXt2YWwgPSB0aGlzLnN0YXJ0Tm9kZUF0KGlubmVyU3RhcnRQb3MsIGlubmVyU3RhcnRMb2MpO3ZhbC5leHByZXNzaW9ucyA9IGV4cHJMaXN0O3RoaXMuZmluaXNoTm9kZUF0KHZhbCwgXCJTZXF1ZW5jZUV4cHJlc3Npb25cIiwgaW5uZXJFbmRQb3MsIGlubmVyRW5kTG9jKTt9ZWxzZSB7dmFsID0gZXhwckxpc3RbMF07fX1lbHNlIHt2YWwgPSB0aGlzLnBhcnNlUGFyZW5FeHByZXNzaW9uKCk7fWlmKHRoaXMub3B0aW9ucy5wcmVzZXJ2ZVBhcmVucyl7dmFyIHBhcj10aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0UG9zLCBzdGFydExvYyk7cGFyLmV4cHJlc3Npb24gPSB2YWw7cmV0dXJuIHRoaXMuZmluaXNoTm9kZShwYXIsIFwiUGFyZW50aGVzaXplZEV4cHJlc3Npb25cIik7fWVsc2Uge3JldHVybiB2YWw7fX07cHAucGFyc2VQYXJlbkl0ZW0gPSBmdW5jdGlvbihpdGVtKXtyZXR1cm4gaXRlbTt9O3BwLnBhcnNlUGFyZW5BcnJvd0xpc3QgPSBmdW5jdGlvbihzdGFydFBvcywgc3RhcnRMb2MsIGV4cHJMaXN0KXtyZXR1cm4gdGhpcy5wYXJzZUFycm93RXhwcmVzc2lvbih0aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0UG9zLCBzdGFydExvYyksIGV4cHJMaXN0KTt9O3ZhciBlbXB0eT1bXTtwcC5wYXJzZU5ldyA9IGZ1bmN0aW9uKCl7dmFyIG5vZGU9dGhpcy5zdGFydE5vZGUoKTt2YXIgbWV0YT10aGlzLnBhcnNlSWRlbnQodHJ1ZSk7aWYodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYgJiYgdGhpcy5lYXQodHQuZG90KSl7bm9kZS5tZXRhID0gbWV0YTtub2RlLnByb3BlcnR5ID0gdGhpcy5wYXJzZUlkZW50KHRydWUpO2lmKG5vZGUucHJvcGVydHkubmFtZSAhPT0gXCJ0YXJnZXRcIil0aGlzLnJhaXNlKG5vZGUucHJvcGVydHkuc3RhcnQsIFwiVGhlIG9ubHkgdmFsaWQgbWV0YSBwcm9wZXJ0eSBmb3IgbmV3IGlzIG5ldy50YXJnZXRcIik7cmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIk1ldGFQcm9wZXJ0eVwiKTt9dmFyIHN0YXJ0UG9zPXRoaXMuc3RhcnQsIHN0YXJ0TG9jPXRoaXMuc3RhcnRMb2M7bm9kZS5jYWxsZWUgPSB0aGlzLnBhcnNlU3Vic2NyaXB0cyh0aGlzLnBhcnNlRXhwckF0b20oKSwgc3RhcnRQb3MsIHN0YXJ0TG9jLCB0cnVlKTtpZih0aGlzLmVhdCh0dC5wYXJlbkwpKW5vZGUuYXJndW1lbnRzID0gdGhpcy5wYXJzZUV4cHJMaXN0KHR0LnBhcmVuUiwgZmFsc2UpO2Vsc2Ugbm9kZS5hcmd1bWVudHMgPSBlbXB0eTtyZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiTmV3RXhwcmVzc2lvblwiKTt9O3BwLnBhcnNlVGVtcGxhdGVFbGVtZW50ID0gZnVuY3Rpb24oKXt2YXIgZWxlbT10aGlzLnN0YXJ0Tm9kZSgpO2VsZW0udmFsdWUgPSB7cmF3OnRoaXMuaW5wdXQuc2xpY2UodGhpcy5zdGFydCwgdGhpcy5lbmQpLCBjb29rZWQ6dGhpcy52YWx1ZX07dGhpcy5uZXh0KCk7ZWxlbS50YWlsID0gdGhpcy50eXBlID09PSB0dC5iYWNrUXVvdGU7cmV0dXJuIHRoaXMuZmluaXNoTm9kZShlbGVtLCBcIlRlbXBsYXRlRWxlbWVudFwiKTt9O3BwLnBhcnNlVGVtcGxhdGUgPSBmdW5jdGlvbigpe3ZhciBub2RlPXRoaXMuc3RhcnROb2RlKCk7dGhpcy5uZXh0KCk7bm9kZS5leHByZXNzaW9ucyA9IFtdO3ZhciBjdXJFbHQ9dGhpcy5wYXJzZVRlbXBsYXRlRWxlbWVudCgpO25vZGUucXVhc2lzID0gW2N1ckVsdF07d2hpbGUoIWN1ckVsdC50YWlsKSB7dGhpcy5leHBlY3QodHQuZG9sbGFyQnJhY2VMKTtub2RlLmV4cHJlc3Npb25zLnB1c2godGhpcy5wYXJzZUV4cHJlc3Npb24oKSk7dGhpcy5leHBlY3QodHQuYnJhY2VSKTtub2RlLnF1YXNpcy5wdXNoKGN1ckVsdCA9IHRoaXMucGFyc2VUZW1wbGF0ZUVsZW1lbnQoKSk7fXRoaXMubmV4dCgpO3JldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJUZW1wbGF0ZUxpdGVyYWxcIik7fTtwcC5wYXJzZU9iaiA9IGZ1bmN0aW9uKGlzUGF0dGVybiwgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcyl7dmFyIG5vZGU9dGhpcy5zdGFydE5vZGUoKSwgZmlyc3Q9dHJ1ZSwgcHJvcEhhc2g9e307bm9kZS5wcm9wZXJ0aWVzID0gW107dGhpcy5uZXh0KCk7d2hpbGUoIXRoaXMuZWF0KHR0LmJyYWNlUikpIHtpZighZmlyc3Qpe3RoaXMuZXhwZWN0KHR0LmNvbW1hKTtpZih0aGlzLmFmdGVyVHJhaWxpbmdDb21tYSh0dC5icmFjZVIpKWJyZWFrO31lbHNlIGZpcnN0ID0gZmFsc2U7dmFyIHByb3A9dGhpcy5zdGFydE5vZGUoKSwgaXNHZW5lcmF0b3I9dW5kZWZpbmVkLCBzdGFydFBvcz11bmRlZmluZWQsIHN0YXJ0TG9jPXVuZGVmaW5lZDtpZih0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNil7cHJvcC5tZXRob2QgPSBmYWxzZTtwcm9wLnNob3J0aGFuZCA9IGZhbHNlO2lmKGlzUGF0dGVybiB8fCByZWZTaG9ydGhhbmREZWZhdWx0UG9zKXtzdGFydFBvcyA9IHRoaXMuc3RhcnQ7c3RhcnRMb2MgPSB0aGlzLnN0YXJ0TG9jO31pZighaXNQYXR0ZXJuKWlzR2VuZXJhdG9yID0gdGhpcy5lYXQodHQuc3Rhcik7fXRoaXMucGFyc2VQcm9wZXJ0eU5hbWUocHJvcCk7dGhpcy5wYXJzZVByb3BlcnR5VmFsdWUocHJvcCwgaXNQYXR0ZXJuLCBpc0dlbmVyYXRvciwgc3RhcnRQb3MsIHN0YXJ0TG9jLCByZWZTaG9ydGhhbmREZWZhdWx0UG9zKTt0aGlzLmNoZWNrUHJvcENsYXNoKHByb3AsIHByb3BIYXNoKTtub2RlLnByb3BlcnRpZXMucHVzaCh0aGlzLmZpbmlzaE5vZGUocHJvcCwgXCJQcm9wZXJ0eVwiKSk7fXJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgaXNQYXR0ZXJuP1wiT2JqZWN0UGF0dGVyblwiOlwiT2JqZWN0RXhwcmVzc2lvblwiKTt9O3BwLnBhcnNlUHJvcGVydHlWYWx1ZSA9IGZ1bmN0aW9uKHByb3AsIGlzUGF0dGVybiwgaXNHZW5lcmF0b3IsIHN0YXJ0UG9zLCBzdGFydExvYywgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcyl7aWYodGhpcy5lYXQodHQuY29sb24pKXtwcm9wLnZhbHVlID0gaXNQYXR0ZXJuP3RoaXMucGFyc2VNYXliZURlZmF1bHQodGhpcy5zdGFydCwgdGhpcy5zdGFydExvYyk6dGhpcy5wYXJzZU1heWJlQXNzaWduKGZhbHNlLCByZWZTaG9ydGhhbmREZWZhdWx0UG9zKTtwcm9wLmtpbmQgPSBcImluaXRcIjt9ZWxzZSBpZih0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNiAmJiB0aGlzLnR5cGUgPT09IHR0LnBhcmVuTCl7aWYoaXNQYXR0ZXJuKXRoaXMudW5leHBlY3RlZCgpO3Byb3Aua2luZCA9IFwiaW5pdFwiO3Byb3AubWV0aG9kID0gdHJ1ZTtwcm9wLnZhbHVlID0gdGhpcy5wYXJzZU1ldGhvZChpc0dlbmVyYXRvcik7fWVsc2UgaWYodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDUgJiYgIXByb3AuY29tcHV0ZWQgJiYgcHJvcC5rZXkudHlwZSA9PT0gXCJJZGVudGlmaWVyXCIgJiYgKHByb3Aua2V5Lm5hbWUgPT09IFwiZ2V0XCIgfHwgcHJvcC5rZXkubmFtZSA9PT0gXCJzZXRcIikgJiYgKHRoaXMudHlwZSAhPSB0dC5jb21tYSAmJiB0aGlzLnR5cGUgIT0gdHQuYnJhY2VSKSl7aWYoaXNHZW5lcmF0b3IgfHwgaXNQYXR0ZXJuKXRoaXMudW5leHBlY3RlZCgpO3Byb3Aua2luZCA9IHByb3Aua2V5Lm5hbWU7dGhpcy5wYXJzZVByb3BlcnR5TmFtZShwcm9wKTtwcm9wLnZhbHVlID0gdGhpcy5wYXJzZU1ldGhvZChmYWxzZSk7fWVsc2UgaWYodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYgJiYgIXByb3AuY29tcHV0ZWQgJiYgcHJvcC5rZXkudHlwZSA9PT0gXCJJZGVudGlmaWVyXCIpe3Byb3Aua2luZCA9IFwiaW5pdFwiO2lmKGlzUGF0dGVybil7aWYodGhpcy5pc0tleXdvcmQocHJvcC5rZXkubmFtZSkgfHwgdGhpcy5zdHJpY3QgJiYgKHJlc2VydmVkV29yZHMuc3RyaWN0QmluZChwcm9wLmtleS5uYW1lKSB8fCByZXNlcnZlZFdvcmRzLnN0cmljdChwcm9wLmtleS5uYW1lKSkgfHwgIXRoaXMub3B0aW9ucy5hbGxvd1Jlc2VydmVkICYmIHRoaXMuaXNSZXNlcnZlZFdvcmQocHJvcC5rZXkubmFtZSkpdGhpcy5yYWlzZShwcm9wLmtleS5zdGFydCwgXCJCaW5kaW5nIFwiICsgcHJvcC5rZXkubmFtZSk7cHJvcC52YWx1ZSA9IHRoaXMucGFyc2VNYXliZURlZmF1bHQoc3RhcnRQb3MsIHN0YXJ0TG9jLCBwcm9wLmtleSk7fWVsc2UgaWYodGhpcy50eXBlID09PSB0dC5lcSAmJiByZWZTaG9ydGhhbmREZWZhdWx0UG9zKXtpZighcmVmU2hvcnRoYW5kRGVmYXVsdFBvcy5zdGFydClyZWZTaG9ydGhhbmREZWZhdWx0UG9zLnN0YXJ0ID0gdGhpcy5zdGFydDtwcm9wLnZhbHVlID0gdGhpcy5wYXJzZU1heWJlRGVmYXVsdChzdGFydFBvcywgc3RhcnRMb2MsIHByb3Aua2V5KTt9ZWxzZSB7cHJvcC52YWx1ZSA9IHByb3Aua2V5O31wcm9wLnNob3J0aGFuZCA9IHRydWU7fWVsc2UgdGhpcy51bmV4cGVjdGVkKCk7fTtwcC5wYXJzZVByb3BlcnR5TmFtZSA9IGZ1bmN0aW9uKHByb3Ape2lmKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KXtpZih0aGlzLmVhdCh0dC5icmFja2V0TCkpe3Byb3AuY29tcHV0ZWQgPSB0cnVlO3Byb3Aua2V5ID0gdGhpcy5wYXJzZU1heWJlQXNzaWduKCk7dGhpcy5leHBlY3QodHQuYnJhY2tldFIpO3JldHVybiBwcm9wLmtleTt9ZWxzZSB7cHJvcC5jb21wdXRlZCA9IGZhbHNlO319cmV0dXJuIHByb3Aua2V5ID0gdGhpcy50eXBlID09PSB0dC5udW0gfHwgdGhpcy50eXBlID09PSB0dC5zdHJpbmc/dGhpcy5wYXJzZUV4cHJBdG9tKCk6dGhpcy5wYXJzZUlkZW50KHRydWUpO307cHAuaW5pdEZ1bmN0aW9uID0gZnVuY3Rpb24obm9kZSl7bm9kZS5pZCA9IG51bGw7aWYodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYpe25vZGUuZ2VuZXJhdG9yID0gZmFsc2U7bm9kZS5leHByZXNzaW9uID0gZmFsc2U7fX07cHAucGFyc2VNZXRob2QgPSBmdW5jdGlvbihpc0dlbmVyYXRvcil7dmFyIG5vZGU9dGhpcy5zdGFydE5vZGUoKTt0aGlzLmluaXRGdW5jdGlvbihub2RlKTt0aGlzLmV4cGVjdCh0dC5wYXJlbkwpO25vZGUucGFyYW1zID0gdGhpcy5wYXJzZUJpbmRpbmdMaXN0KHR0LnBhcmVuUiwgZmFsc2UsIGZhbHNlKTt2YXIgYWxsb3dFeHByZXNzaW9uQm9keT11bmRlZmluZWQ7aWYodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYpe25vZGUuZ2VuZXJhdG9yID0gaXNHZW5lcmF0b3I7YWxsb3dFeHByZXNzaW9uQm9keSA9IHRydWU7fWVsc2Uge2FsbG93RXhwcmVzc2lvbkJvZHkgPSBmYWxzZTt9dGhpcy5wYXJzZUZ1bmN0aW9uQm9keShub2RlLCBhbGxvd0V4cHJlc3Npb25Cb2R5KTtyZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiRnVuY3Rpb25FeHByZXNzaW9uXCIpO307cHAucGFyc2VBcnJvd0V4cHJlc3Npb24gPSBmdW5jdGlvbihub2RlLCBwYXJhbXMpe3RoaXMuaW5pdEZ1bmN0aW9uKG5vZGUpO25vZGUucGFyYW1zID0gdGhpcy50b0Fzc2lnbmFibGVMaXN0KHBhcmFtcywgdHJ1ZSk7dGhpcy5wYXJzZUZ1bmN0aW9uQm9keShub2RlLCB0cnVlKTtyZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiQXJyb3dGdW5jdGlvbkV4cHJlc3Npb25cIik7fTtwcC5wYXJzZUZ1bmN0aW9uQm9keSA9IGZ1bmN0aW9uKG5vZGUsIGFsbG93RXhwcmVzc2lvbil7dmFyIGlzRXhwcmVzc2lvbj1hbGxvd0V4cHJlc3Npb24gJiYgdGhpcy50eXBlICE9PSB0dC5icmFjZUw7aWYoaXNFeHByZXNzaW9uKXtub2RlLmJvZHkgPSB0aGlzLnBhcnNlTWF5YmVBc3NpZ24oKTtub2RlLmV4cHJlc3Npb24gPSB0cnVlO31lbHNlIHt2YXIgb2xkSW5GdW5jPXRoaXMuaW5GdW5jdGlvbiwgb2xkSW5HZW49dGhpcy5pbkdlbmVyYXRvciwgb2xkTGFiZWxzPXRoaXMubGFiZWxzO3RoaXMuaW5GdW5jdGlvbiA9IHRydWU7dGhpcy5pbkdlbmVyYXRvciA9IG5vZGUuZ2VuZXJhdG9yO3RoaXMubGFiZWxzID0gW107bm9kZS5ib2R5ID0gdGhpcy5wYXJzZUJsb2NrKHRydWUpO25vZGUuZXhwcmVzc2lvbiA9IGZhbHNlO3RoaXMuaW5GdW5jdGlvbiA9IG9sZEluRnVuYzt0aGlzLmluR2VuZXJhdG9yID0gb2xkSW5HZW47dGhpcy5sYWJlbHMgPSBvbGRMYWJlbHM7fWlmKHRoaXMuc3RyaWN0IHx8ICFpc0V4cHJlc3Npb24gJiYgbm9kZS5ib2R5LmJvZHkubGVuZ3RoICYmIHRoaXMuaXNVc2VTdHJpY3Qobm9kZS5ib2R5LmJvZHlbMF0pKXt2YXIgbmFtZUhhc2g9e30sIG9sZFN0cmljdD10aGlzLnN0cmljdDt0aGlzLnN0cmljdCA9IHRydWU7aWYobm9kZS5pZCl0aGlzLmNoZWNrTFZhbChub2RlLmlkLCB0cnVlKTtmb3IodmFyIGk9MDsgaSA8IG5vZGUucGFyYW1zLmxlbmd0aDsgaSsrKSB7dGhpcy5jaGVja0xWYWwobm9kZS5wYXJhbXNbaV0sIHRydWUsIG5hbWVIYXNoKTt9dGhpcy5zdHJpY3QgPSBvbGRTdHJpY3Q7fX07cHAucGFyc2VFeHByTGlzdCA9IGZ1bmN0aW9uKGNsb3NlLCBhbGxvd1RyYWlsaW5nQ29tbWEsIGFsbG93RW1wdHksIHJlZlNob3J0aGFuZERlZmF1bHRQb3Mpe3ZhciBlbHRzPVtdLCBmaXJzdD10cnVlO3doaWxlKCF0aGlzLmVhdChjbG9zZSkpIHtpZighZmlyc3Qpe3RoaXMuZXhwZWN0KHR0LmNvbW1hKTtpZihhbGxvd1RyYWlsaW5nQ29tbWEgJiYgdGhpcy5hZnRlclRyYWlsaW5nQ29tbWEoY2xvc2UpKWJyZWFrO31lbHNlIGZpcnN0ID0gZmFsc2U7aWYoYWxsb3dFbXB0eSAmJiB0aGlzLnR5cGUgPT09IHR0LmNvbW1hKXtlbHRzLnB1c2gobnVsbCk7fWVsc2Uge2lmKHRoaXMudHlwZSA9PT0gdHQuZWxsaXBzaXMpZWx0cy5wdXNoKHRoaXMucGFyc2VTcHJlYWQocmVmU2hvcnRoYW5kRGVmYXVsdFBvcykpO2Vsc2UgZWx0cy5wdXNoKHRoaXMucGFyc2VNYXliZUFzc2lnbihmYWxzZSwgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcykpO319cmV0dXJuIGVsdHM7fTtwcC5wYXJzZUlkZW50ID0gZnVuY3Rpb24obGliZXJhbCl7dmFyIG5vZGU9dGhpcy5zdGFydE5vZGUoKTtpZihsaWJlcmFsICYmIHRoaXMub3B0aW9ucy5hbGxvd1Jlc2VydmVkID09IFwibmV2ZXJcIilsaWJlcmFsID0gZmFsc2U7aWYodGhpcy50eXBlID09PSB0dC5uYW1lKXtpZighbGliZXJhbCAmJiAoIXRoaXMub3B0aW9ucy5hbGxvd1Jlc2VydmVkICYmIHRoaXMuaXNSZXNlcnZlZFdvcmQodGhpcy52YWx1ZSkgfHwgdGhpcy5zdHJpY3QgJiYgcmVzZXJ2ZWRXb3Jkcy5zdHJpY3QodGhpcy52YWx1ZSkgJiYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2IHx8IHRoaXMuaW5wdXQuc2xpY2UodGhpcy5zdGFydCwgdGhpcy5lbmQpLmluZGV4T2YoXCJcXFxcXCIpID09IC0xKSkpdGhpcy5yYWlzZSh0aGlzLnN0YXJ0LCBcIlRoZSBrZXl3b3JkICdcIiArIHRoaXMudmFsdWUgKyBcIicgaXMgcmVzZXJ2ZWRcIik7bm9kZS5uYW1lID0gdGhpcy52YWx1ZTt9ZWxzZSBpZihsaWJlcmFsICYmIHRoaXMudHlwZS5rZXl3b3JkKXtub2RlLm5hbWUgPSB0aGlzLnR5cGUua2V5d29yZDt9ZWxzZSB7dGhpcy51bmV4cGVjdGVkKCk7fXRoaXMubmV4dCgpO3JldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJJZGVudGlmaWVyXCIpO307cHAucGFyc2VZaWVsZCA9IGZ1bmN0aW9uKCl7dmFyIG5vZGU9dGhpcy5zdGFydE5vZGUoKTt0aGlzLm5leHQoKTtpZih0aGlzLnR5cGUgPT0gdHQuc2VtaSB8fCB0aGlzLmNhbkluc2VydFNlbWljb2xvbigpIHx8IHRoaXMudHlwZSAhPSB0dC5zdGFyICYmICF0aGlzLnR5cGUuc3RhcnRzRXhwcil7bm9kZS5kZWxlZ2F0ZSA9IGZhbHNlO25vZGUuYXJndW1lbnQgPSBudWxsO31lbHNlIHtub2RlLmRlbGVnYXRlID0gdGhpcy5lYXQodHQuc3Rhcik7bm9kZS5hcmd1bWVudCA9IHRoaXMucGFyc2VNYXliZUFzc2lnbigpO31yZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiWWllbGRFeHByZXNzaW9uXCIpO307cHAucGFyc2VDb21wcmVoZW5zaW9uID0gZnVuY3Rpb24obm9kZSwgaXNHZW5lcmF0b3Ipe25vZGUuYmxvY2tzID0gW107d2hpbGUodGhpcy50eXBlID09PSB0dC5fZm9yKSB7dmFyIGJsb2NrPXRoaXMuc3RhcnROb2RlKCk7dGhpcy5uZXh0KCk7dGhpcy5leHBlY3QodHQucGFyZW5MKTtibG9jay5sZWZ0ID0gdGhpcy5wYXJzZUJpbmRpbmdBdG9tKCk7dGhpcy5jaGVja0xWYWwoYmxvY2subGVmdCwgdHJ1ZSk7dGhpcy5leHBlY3RDb250ZXh0dWFsKFwib2ZcIik7YmxvY2sucmlnaHQgPSB0aGlzLnBhcnNlRXhwcmVzc2lvbigpO3RoaXMuZXhwZWN0KHR0LnBhcmVuUik7bm9kZS5ibG9ja3MucHVzaCh0aGlzLmZpbmlzaE5vZGUoYmxvY2ssIFwiQ29tcHJlaGVuc2lvbkJsb2NrXCIpKTt9bm9kZS5maWx0ZXIgPSB0aGlzLmVhdCh0dC5faWYpP3RoaXMucGFyc2VQYXJlbkV4cHJlc3Npb24oKTpudWxsO25vZGUuYm9keSA9IHRoaXMucGFyc2VFeHByZXNzaW9uKCk7dGhpcy5leHBlY3QoaXNHZW5lcmF0b3I/dHQucGFyZW5SOnR0LmJyYWNrZXRSKTtub2RlLmdlbmVyYXRvciA9IGlzR2VuZXJhdG9yO3JldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJDb21wcmVoZW5zaW9uRXhwcmVzc2lvblwiKTt9O30sIHtcIi4vaWRlbnRpZmllclwiOjcsIFwiLi9zdGF0ZVwiOjEzLCBcIi4vdG9rZW50eXBlXCI6MTcsIFwiLi91dGlsXCI6MTh9XSwgNzpbZnVuY3Rpb24oX2RlcmVxXywgbW9kdWxlLCBleHBvcnRzKXtcInVzZSBzdHJpY3RcIjtleHBvcnRzLmlzSWRlbnRpZmllclN0YXJ0ID0gaXNJZGVudGlmaWVyU3RhcnQ7ZXhwb3J0cy5pc0lkZW50aWZpZXJDaGFyID0gaXNJZGVudGlmaWVyQ2hhcjtleHBvcnRzLl9fZXNNb2R1bGUgPSB0cnVlO2Z1bmN0aW9uIG1ha2VQcmVkaWNhdGUod29yZHMpe3dvcmRzID0gd29yZHMuc3BsaXQoXCIgXCIpO3ZhciBmPVwiXCIsIGNhdHM9W107b3V0OiBmb3IodmFyIGk9MDsgaSA8IHdvcmRzLmxlbmd0aDsgKytpKSB7Zm9yKHZhciBqPTA7IGogPCBjYXRzLmxlbmd0aDsgKytqKSB7aWYoY2F0c1tqXVswXS5sZW5ndGggPT0gd29yZHNbaV0ubGVuZ3RoKXtjYXRzW2pdLnB1c2god29yZHNbaV0pO2NvbnRpbnVlIG91dDt9fWNhdHMucHVzaChbd29yZHNbaV1dKTt9ZnVuY3Rpb24gY29tcGFyZVRvKGFycil7aWYoYXJyLmxlbmd0aCA9PSAxKXtyZXR1cm4gZiArPSBcInJldHVybiBzdHIgPT09IFwiICsgSlNPTi5zdHJpbmdpZnkoYXJyWzBdKSArIFwiO1wiO31mICs9IFwic3dpdGNoKHN0cil7XCI7Zm9yKHZhciBpPTA7IGkgPCBhcnIubGVuZ3RoOyArK2kpIHtmICs9IFwiY2FzZSBcIiArIEpTT04uc3RyaW5naWZ5KGFycltpXSkgKyBcIjpcIjt9ZiArPSBcInJldHVybiB0cnVlfXJldHVybiBmYWxzZTtcIjt9aWYoY2F0cy5sZW5ndGggPiAzKXtjYXRzLnNvcnQoZnVuY3Rpb24oYSwgYil7cmV0dXJuIGIubGVuZ3RoIC0gYS5sZW5ndGg7fSk7ZiArPSBcInN3aXRjaChzdHIubGVuZ3RoKXtcIjtmb3IodmFyIGk9MDsgaSA8IGNhdHMubGVuZ3RoOyArK2kpIHt2YXIgY2F0PWNhdHNbaV07ZiArPSBcImNhc2UgXCIgKyBjYXRbMF0ubGVuZ3RoICsgXCI6XCI7Y29tcGFyZVRvKGNhdCk7fWYgKz0gXCJ9XCI7fWVsc2Uge2NvbXBhcmVUbyh3b3Jkcyk7fXJldHVybiBuZXcgRnVuY3Rpb24oXCJzdHJcIiwgZik7fXZhciByZXNlcnZlZFdvcmRzPXszOm1ha2VQcmVkaWNhdGUoXCJhYnN0cmFjdCBib29sZWFuIGJ5dGUgY2hhciBjbGFzcyBkb3VibGUgZW51bSBleHBvcnQgZXh0ZW5kcyBmaW5hbCBmbG9hdCBnb3RvIGltcGxlbWVudHMgaW1wb3J0IGludCBpbnRlcmZhY2UgbG9uZyBuYXRpdmUgcGFja2FnZSBwcml2YXRlIHByb3RlY3RlZCBwdWJsaWMgc2hvcnQgc3RhdGljIHN1cGVyIHN5bmNocm9uaXplZCB0aHJvd3MgdHJhbnNpZW50IHZvbGF0aWxlXCIpLCA1Om1ha2VQcmVkaWNhdGUoXCJjbGFzcyBlbnVtIGV4dGVuZHMgc3VwZXIgY29uc3QgZXhwb3J0IGltcG9ydFwiKSwgNjptYWtlUHJlZGljYXRlKFwiZW51bSBhd2FpdFwiKSwgc3RyaWN0Om1ha2VQcmVkaWNhdGUoXCJpbXBsZW1lbnRzIGludGVyZmFjZSBsZXQgcGFja2FnZSBwcml2YXRlIHByb3RlY3RlZCBwdWJsaWMgc3RhdGljIHlpZWxkXCIpLCBzdHJpY3RCaW5kOm1ha2VQcmVkaWNhdGUoXCJldmFsIGFyZ3VtZW50c1wiKX07ZXhwb3J0cy5yZXNlcnZlZFdvcmRzID0gcmVzZXJ2ZWRXb3Jkczt2YXIgZWNtYTVBbmRMZXNzS2V5d29yZHM9XCJicmVhayBjYXNlIGNhdGNoIGNvbnRpbnVlIGRlYnVnZ2VyIGRlZmF1bHQgZG8gZWxzZSBmaW5hbGx5IGZvciBmdW5jdGlvbiBpZiByZXR1cm4gc3dpdGNoIHRocm93IHRyeSB2YXIgd2hpbGUgd2l0aCBudWxsIHRydWUgZmFsc2UgaW5zdGFuY2VvZiB0eXBlb2Ygdm9pZCBkZWxldGUgbmV3IGluIHRoaXNcIjt2YXIga2V5d29yZHM9ezU6bWFrZVByZWRpY2F0ZShlY21hNUFuZExlc3NLZXl3b3JkcyksIDY6bWFrZVByZWRpY2F0ZShlY21hNUFuZExlc3NLZXl3b3JkcyArIFwiIGxldCBjb25zdCBjbGFzcyBleHRlbmRzIGV4cG9ydCBpbXBvcnQgeWllbGQgc3VwZXJcIil9O2V4cG9ydHMua2V5d29yZHMgPSBrZXl3b3Jkczt2YXIgbm9uQVNDSUlpZGVudGlmaWVyU3RhcnRDaGFycz1cIsKqwrXCusOALcOWw5gtw7bDuC3LgcuGLcuRy6Aty6TLrMuuzbAtzbTNts23zbotzb3Nv86GzogtzorOjM6OLc6hzqMtz7XPty3SgdKKLdSv1LEt1ZbVmdWhLdaH15At16rXsC3XstigLdmK2a7Zr9mxLduT25Xbpdum267br9u6Ldu827/ckNySLdyv3Y0t3qXesd+KLd+q37Tftd+64KCALeCgleCgmuCgpOCgqOChgC3goZjgoqAt4KKy4KSELeCkueCkveClkOClmC3gpaHgpbEt4KaA4KaFLeCmjOCmj+CmkOCmky3gpqjgpqot4Kaw4Kay4Ka2LeCmueCmveCnjuCnnOCnneCnny3gp6Hgp7Dgp7HgqIUt4KiK4KiP4KiQ4KiTLeCoqOCoqi3gqLDgqLLgqLPgqLXgqLbgqLjgqLngqZkt4Kmc4Kme4KmyLeCptOCqhS3gqo3gqo8t4KqR4KqTLeCqqOCqqi3gqrDgqrLgqrPgqrUt4Kq54Kq94KuQ4Kug4Kuh4KyFLeCsjOCsj+CskOCsky3grKjgrKot4Kyw4Kyy4Kyz4Ky1LeCsueCsveCtnOCtneCtny3graHgrbHgroPgroUt4K6K4K6OLeCukOCuki3grpXgrpngrprgrpzgrp7grp/grqPgrqTgrqgt4K6q4K6uLeCuueCvkOCwhS3gsIzgsI4t4LCQ4LCSLeCwqOCwqi3gsLngsL3gsZjgsZngsaDgsaHgsoUt4LKM4LKOLeCykOCyki3gsqjgsqot4LKz4LK1LeCyueCyveCznuCzoOCzoeCzseCzsuC0hS3gtIzgtI4t4LSQ4LSSLeC0uuC0veC1juC1oOC1oeC1ui3gtb/gtoUt4LaW4LaaLeC2seC2sy3gtrvgtr3gt4At4LeG4LiBLeC4sOC4suC4s+C5gC3guYbguoHguoLguoTguofguojguorguo3gupQt4LqX4LqZLeC6n+C6oS3guqPguqXguqfguqrguqvguq0t4Lqw4Lqy4Lqz4Lq94LuALeC7hOC7huC7nC3gu5/gvIDgvYAt4L2H4L2JLeC9rOC+iC3gvozhgIAt4YCq4YC/4YGQLeGBleGBmi3hgZ3hgaHhgaXhgabhga4t4YGw4YG1LeGCgeGCjuGCoC3hg4Xhg4fhg43hg5At4YO64YO8LeGJiOGJii3hiY3hiZAt4YmW4YmY4YmaLeGJneGJoC3hiojhioot4YqN4YqQLeGKsOGKsi3hirXhirgt4Yq+4YuA4YuCLeGLheGLiC3hi5bhi5gt4YyQ4YySLeGMleGMmC3hjZrhjoAt4Y6P4Y6gLeGPtOGQgS3hmazhma8t4Zm/4ZqBLeGamuGaoC3hm6rhm64t4Zu44ZyALeGcjOGcji3hnJHhnKAt4Zyx4Z2ALeGdkeGdoC3hnazhna4t4Z2w4Z6ALeGes+Gfl+GfnOGgoC3hobfhooAt4aKo4aKq4aKwLeGjteGkgC3hpJ7hpZAt4aWt4aWwLeGltOGmgC3hpqvhp4Et4aeH4aiALeGoluGooC3hqZThqqfhrIUt4ayz4a2FLeGti+Gugy3hrqDhrq7hrq/hrrot4a+l4bCALeGwo+GxjS3hsY/hsZot4bG94bOpLeGzrOGzri3hs7Hhs7Xhs7bhtIAt4ba/4biALeG8leG8mC3hvJ3hvKAt4b2F4b2ILeG9jeG9kC3hvZfhvZnhvZvhvZ3hvZ8t4b294b6ALeG+tOG+ti3hvrzhvr7hv4It4b+E4b+GLeG/jOG/kC3hv5Phv5Yt4b+b4b+gLeG/rOG/si3hv7Thv7Yt4b+84oGx4oG/4oKQLeKCnOKEguKEh+KEii3ihJPihJXihJgt4oSd4oSk4oSm4oSo4oSqLeKEueKEvC3ihL/ihYUt4oWJ4oWO4oWgLeKGiOKwgC3isK7isLAt4rGe4rGgLeKzpOKzqy3is67is7Lis7PitIAt4rSl4rSn4rSt4rSwLeK1p+K1r+K2gC3itpbitqAt4ram4raoLeK2ruK2sC3itrbitrgt4ra+4reALeK3huK3iC3it47it5At4reW4reYLeK3nuOAhS3jgIfjgKEt44Cp44CxLeOAteOAuC3jgLzjgYEt44KW44KbLeOCn+OCoS3jg7rjg7wt44O/44SFLeOEreOEsS3jho7jhqAt44a644ewLeOHv+OQgC3ktrXkuIAt6b+M6oCALeqSjOqTkC3qk73qlIAt6piM6piQLeqYn+qYquqYq+qZgC3qma7qmb8t6pqd6pqgLeqbr+qcly3qnJ/qnKIt6p6I6p6LLeqejuqekC3qnq3qnrDqnrHqn7ct6qCB6qCDLeqgheqghy3qoIrqoIwt6qCi6qGALeqhs+qigi3qorPqo7It6qO36qO76qSKLeqkpeqksC3qpYbqpaAt6qW86qaELeqmsuqnj+qnoC3qp6Tqp6Yt6qev6qe6LeqnvuqogC3qqKjqqYAt6qmC6qmELeqpi+qpoC3qqbbqqbrqqb4t6qqv6qqx6qq16qq26qq5LeqqveqrgOqrguqrmy3qq53qq6At6quq6quyLeqrtOqsgS3qrIbqrIkt6qyO6qyRLeqsluqsoC3qrKbqrKgt6qyu6qywLeqtmuqtnC3qrZ/qraTqraXqr4At6q+i6rCALe2eo+2esC3tn4btn4st7Z+776SALe+pre+psC3vq5nvrIAt76yG76yTLe+sl++sne+sny3vrKjvrKot76y276y4Le+svO+svu+tgO+tge+tg++thO+thi3vrrHvr5Mt77S977WQLe+2j++2ki3vt4fvt7At77e777mwLe+5tO+5ti3vu7zvvKEt77y6772BLe+9mu+9pi3vvr7vv4It77+H77+KLe+/j++/ki3vv5fvv5ot77+cXCI7dmFyIG5vbkFTQ0lJaWRlbnRpZmllckNoYXJzPVwi4oCM4oCNwrfMgC3Nr86H0oMt0ofWkS3Wvda/14HXgteE14XXh9iQLdia2Yst2anZsNuWLduc258t26Tbp9uo26ot263bsC3budyR3LAt3Yrepi3esN+ALd+J36st37PgoJYt4KCZ4KCbLeCgo+CgpS3goKfgoKkt4KCt4KGZLeChm+CjpC3gpIPgpLot4KS84KS+LeClj+ClkS3gpZfgpaLgpaPgpaYt4KWv4KaBLeCmg+CmvOCmvi3gp4Tgp4fgp4jgp4st4KeN4KeX4Kei4Kej4KemLeCnr+CogS3gqIPgqLzgqL4t4KmC4KmH4KmI4KmLLeCpjeCpkeCppi3gqbHgqbXgqoEt4KqD4Kq84Kq+LeCrheCrhy3gq4ngq4st4KuN4Kui4Kuj4KumLeCrr+CsgS3grIPgrLzgrL4t4K2E4K2H4K2I4K2LLeCtjeCtluCtl+CtouCto+Ctpi3gra/groLgrr4t4K+C4K+GLeCviOCvii3gr43gr5fgr6Yt4K+v4LCALeCwg+Cwvi3gsYTgsYYt4LGI4LGKLeCxjeCxleCxluCxouCxo+Cxpi3gsa/gsoEt4LKD4LK84LK+LeCzhOCzhi3gs4jgs4ot4LON4LOV4LOW4LOi4LOj4LOmLeCzr+C0gS3gtIPgtL4t4LWE4LWGLeC1iOC1ii3gtY3gtZfgtaLgtaPgtaYt4LWv4LaC4LaD4LeK4LePLeC3lOC3luC3mC3gt5/gt6Yt4Lev4Ley4Lez4Lix4Li0LeC4uuC5hy3guY7guZAt4LmZ4Lqx4Lq0LeC6ueC6u+C6vOC7iC3gu43gu5At4LuZ4LyY4LyZ4LygLeC8qeC8teC8t+C8ueC8vuC8v+C9sS3gvoTgvobgvofgvo0t4L6X4L6ZLeC+vOC/huGAqy3hgL7hgYAt4YGJ4YGWLeGBmeGBni3hgaDhgaIt4YGk4YGnLeGBreGBsS3hgbThgoIt4YKN4YKPLeGCneGNnS3hjZ/hjakt4Y2x4ZySLeGclOGcsi3hnLThnZLhnZPhnbLhnbPhnrQt4Z+T4Z+d4Z+gLeGfqeGgiy3hoI3hoJAt4aCZ4aKp4aSgLeGkq+GksC3hpLvhpYYt4aWP4aawLeGngOGniOGnieGnkC3hp5rhqJct4aib4amVLeGpnuGpoC3hqbzhqb8t4aqJ4aqQLeGqmeGqsC3hqr3hrIAt4ayE4ay0LeGthOGtkC3hrZnhrast4a2z4a6ALeGuguGuoS3hrq3hrrAt4a654a+mLeGvs+GwpC3hsLfhsYAt4bGJ4bGQLeGxmeGzkC3hs5Lhs5Qt4bOo4bOt4bOyLeGztOGzuOGzueG3gC3ht7Xht7wt4be/4oC/4oGA4oGU4oOQLeKDnOKDoeKDpS3ig7Dis68t4rOx4rW/4regLeK3v+OAqi3jgK/jgpnjgprqmKAt6pip6pmv6pm0LeqZveqan+qbsOqbseqgguqghuqgi+qgoy3qoKfqooDqooHqorQt6qOE6qOQLeqjmeqjoC3qo7HqpIAt6qSJ6qSmLeqkreqlhy3qpZPqpoAt6qaD6qazLeqngOqnkC3qp5nqp6Xqp7At6qe56qipLeqotuqpg+qpjOqpjeqpkC3qqZnqqbst6qm96qqw6qqyLeqqtOqqt+qquOqqvuqqv+qrgeqrqy3qq6/qq7Xqq7bqr6Mt6q+q6q+s6q+t6q+wLeqvue+snu+4gC3vuI/vuKAt77it77iz77i077mNLe+5j++8kC3vvJnvvL9cIjt2YXIgbm9uQVNDSUlpZGVudGlmaWVyU3RhcnQ9bmV3IFJlZ0V4cChcIltcIiArIG5vbkFTQ0lJaWRlbnRpZmllclN0YXJ0Q2hhcnMgKyBcIl1cIik7dmFyIG5vbkFTQ0lJaWRlbnRpZmllcj1uZXcgUmVnRXhwKFwiW1wiICsgbm9uQVNDSUlpZGVudGlmaWVyU3RhcnRDaGFycyArIG5vbkFTQ0lJaWRlbnRpZmllckNoYXJzICsgXCJdXCIpO25vbkFTQ0lJaWRlbnRpZmllclN0YXJ0Q2hhcnMgPSBub25BU0NJSWlkZW50aWZpZXJDaGFycyA9IG51bGw7dmFyIGFzdHJhbElkZW50aWZpZXJTdGFydENvZGVzPVswLCAxMSwgMiwgMjUsIDIsIDE4LCAyLCAxLCAyLCAxNCwgMywgMTMsIDM1LCAxMjIsIDcwLCA1MiwgMjY4LCAyOCwgNCwgNDgsIDQ4LCAzMSwgMTcsIDI2LCA2LCAzNywgMTEsIDI5LCAzLCAzNSwgNSwgNywgMiwgNCwgNDMsIDE1NywgOTksIDM5LCA5LCA1MSwgMTU3LCAzMTAsIDEwLCAyMSwgMTEsIDcsIDE1MywgNSwgMywgMCwgMiwgNDMsIDIsIDEsIDQsIDAsIDMsIDIyLCAxMSwgMjIsIDEwLCAzMCwgOTgsIDIxLCAxMSwgMjUsIDcxLCA1NSwgNywgMSwgNjUsIDAsIDE2LCAzLCAyLCAyLCAyLCAyNiwgNDUsIDI4LCA0LCAyOCwgMzYsIDcsIDIsIDI3LCAyOCwgNTMsIDExLCAyMSwgMTEsIDE4LCAxNCwgMTcsIDExMSwgNzIsIDk1NSwgNTIsIDc2LCA0NCwgMzMsIDI0LCAyNywgMzUsIDQyLCAzNCwgNCwgMCwgMTMsIDQ3LCAxNSwgMywgMjIsIDAsIDM4LCAxNywgMiwgMjQsIDEzMywgNDYsIDM5LCA3LCAzLCAxLCAzLCAyMSwgMiwgNiwgMiwgMSwgMiwgNCwgNCwgMCwgMzIsIDQsIDI4NywgNDcsIDIxLCAxLCAyLCAwLCAxODUsIDQ2LCA4MiwgNDcsIDIxLCAwLCA2MCwgNDIsIDUwMiwgNjMsIDMyLCAwLCA0NDksIDU2LCAxMjg4LCA5MjAsIDEwNCwgMTEwLCAyOTYyLCAxMDcwLCAxMzI2NiwgNTY4LCA4LCAzMCwgMTE0LCAyOSwgMTksIDQ3LCAxNywgMywgMzIsIDIwLCA2LCAxOCwgODgxLCA2OCwgMTIsIDAsIDY3LCAxMiwgMTY0ODEsIDEsIDMwNzEsIDEwNiwgNiwgMTIsIDQsIDgsIDgsIDksIDU5OTEsIDg0LCAyLCA3MCwgMiwgMSwgMywgMCwgMywgMSwgMywgMywgMiwgMTEsIDIsIDAsIDIsIDYsIDIsIDY0LCAyLCAzLCAzLCA3LCAyLCA2LCAyLCAyNywgMiwgMywgMiwgNCwgMiwgMCwgNCwgNiwgMiwgMzM5LCAzLCAyNCwgMiwgMjQsIDIsIDMwLCAyLCAyNCwgMiwgMzAsIDIsIDI0LCAyLCAzMCwgMiwgMjQsIDIsIDMwLCAyLCAyNCwgMiwgNywgNDE0OSwgMTk2LCAxMzQwLCAzLCAyLCAyNiwgMiwgMSwgMiwgMCwgMywgMCwgMiwgOSwgMiwgMywgMiwgMCwgMiwgMCwgNywgMCwgNSwgMCwgMiwgMCwgMiwgMCwgMiwgMiwgMiwgMSwgMiwgMCwgMywgMCwgMiwgMCwgMiwgMCwgMiwgMCwgMiwgMCwgMiwgMSwgMiwgMCwgMywgMywgMiwgNiwgMiwgMywgMiwgMywgMiwgMCwgMiwgOSwgMiwgMTYsIDYsIDIsIDIsIDQsIDIsIDE2LCA0NDIxLCA0MjcxMCwgNDIsIDQxNDgsIDEyLCAyMjEsIDE2MzU1LCA1NDFdO3ZhciBhc3RyYWxJZGVudGlmaWVyQ29kZXM9WzUwOSwgMCwgMjI3LCAwLCAxNTAsIDQsIDI5NCwgOSwgMTM2OCwgMiwgMiwgMSwgNiwgMywgNDEsIDIsIDUsIDAsIDE2NiwgMSwgMTMwNiwgMiwgNTQsIDE0LCAzMiwgOSwgMTYsIDMsIDQ2LCAxMCwgNTQsIDksIDcsIDIsIDM3LCAxMywgMiwgOSwgNTIsIDAsIDEzLCAyLCA0OSwgMTMsIDE2LCA5LCA4MywgMTEsIDE2OCwgMTEsIDYsIDksIDgsIDIsIDU3LCAwLCAyLCA2LCAzLCAxLCAzLCAyLCAxMCwgMCwgMTEsIDEsIDMsIDYsIDQsIDQsIDMxNiwgMTksIDEzLCA5LCAyMTQsIDYsIDMsIDgsIDExMiwgMTYsIDE2LCA5LCA4MiwgMTIsIDksIDksIDUzNSwgOSwgMjA4NTUsIDksIDEzNSwgNCwgNjAsIDYsIDI2LCA5LCAxMDE2LCA0NSwgMTcsIDMsIDE5NzIzLCAxLCA1MzE5LCA0LCA0LCA1LCA5LCA3LCAzLCA2LCAzMSwgMywgMTQ5LCAyLCAxNDE4LCA0OSwgNDMwNSwgNiwgNzkyNjE4LCAyMzldO2Z1bmN0aW9uIGlzSW5Bc3RyYWxTZXQoY29kZSwgc2V0KXt2YXIgcG9zPTY1NTM2O2Zvcih2YXIgaT0wOyBpIDwgc2V0Lmxlbmd0aDsgaSArPSAyKSB7cG9zICs9IHNldFtpXTtpZihwb3MgPiBjb2RlKXtyZXR1cm4gZmFsc2U7fXBvcyArPSBzZXRbaSArIDFdO2lmKHBvcyA+PSBjb2RlKXtyZXR1cm4gdHJ1ZTt9fX1mdW5jdGlvbiBpc0lkZW50aWZpZXJTdGFydChjb2RlLCBhc3RyYWwpe2lmKGNvZGUgPCA2NSl7cmV0dXJuIGNvZGUgPT09IDM2O31pZihjb2RlIDwgOTEpe3JldHVybiB0cnVlO31pZihjb2RlIDwgOTcpe3JldHVybiBjb2RlID09PSA5NTt9aWYoY29kZSA8IDEyMyl7cmV0dXJuIHRydWU7fWlmKGNvZGUgPD0gNjU1MzUpe3JldHVybiBjb2RlID49IDE3MCAmJiBub25BU0NJSWlkZW50aWZpZXJTdGFydC50ZXN0KFN0cmluZy5mcm9tQ2hhckNvZGUoY29kZSkpO31pZihhc3RyYWwgPT09IGZhbHNlKXtyZXR1cm4gZmFsc2U7fXJldHVybiBpc0luQXN0cmFsU2V0KGNvZGUsIGFzdHJhbElkZW50aWZpZXJTdGFydENvZGVzKTt9ZnVuY3Rpb24gaXNJZGVudGlmaWVyQ2hhcihjb2RlLCBhc3RyYWwpe2lmKGNvZGUgPCA0OCl7cmV0dXJuIGNvZGUgPT09IDM2O31pZihjb2RlIDwgNTgpe3JldHVybiB0cnVlO31pZihjb2RlIDwgNjUpe3JldHVybiBmYWxzZTt9aWYoY29kZSA8IDkxKXtyZXR1cm4gdHJ1ZTt9aWYoY29kZSA8IDk3KXtyZXR1cm4gY29kZSA9PT0gOTU7fWlmKGNvZGUgPCAxMjMpe3JldHVybiB0cnVlO31pZihjb2RlIDw9IDY1NTM1KXtyZXR1cm4gY29kZSA+PSAxNzAgJiYgbm9uQVNDSUlpZGVudGlmaWVyLnRlc3QoU3RyaW5nLmZyb21DaGFyQ29kZShjb2RlKSk7fWlmKGFzdHJhbCA9PT0gZmFsc2Upe3JldHVybiBmYWxzZTt9cmV0dXJuIGlzSW5Bc3RyYWxTZXQoY29kZSwgYXN0cmFsSWRlbnRpZmllclN0YXJ0Q29kZXMpIHx8IGlzSW5Bc3RyYWxTZXQoY29kZSwgYXN0cmFsSWRlbnRpZmllckNvZGVzKTt9fSwge31dLCA4OltmdW5jdGlvbihfZGVyZXFfLCBtb2R1bGUsIGV4cG9ydHMpe1widXNlIHN0cmljdFwiO3ZhciBfY2xhc3NDYWxsQ2hlY2s9ZnVuY3Rpb24gX2NsYXNzQ2FsbENoZWNrKGluc3RhbmNlLCBDb25zdHJ1Y3Rvcil7aWYoIShpbnN0YW5jZSBpbnN0YW5jZW9mIENvbnN0cnVjdG9yKSl7dGhyb3cgbmV3IFR5cGVFcnJvcihcIkNhbm5vdCBjYWxsIGEgY2xhc3MgYXMgYSBmdW5jdGlvblwiKTt9fTtleHBvcnRzLmdldExpbmVJbmZvID0gZ2V0TGluZUluZm87ZXhwb3J0cy5fX2VzTW9kdWxlID0gdHJ1ZTt2YXIgUGFyc2VyPV9kZXJlcV8oXCIuL3N0YXRlXCIpLlBhcnNlcjt2YXIgbGluZUJyZWFrRz1fZGVyZXFfKFwiLi93aGl0ZXNwYWNlXCIpLmxpbmVCcmVha0c7dmFyIGRlcHJlY2F0ZT1fZGVyZXFfKFwidXRpbFwiKS5kZXByZWNhdGU7dmFyIFBvc2l0aW9uPWV4cG9ydHMuUG9zaXRpb24gPSAoZnVuY3Rpb24oKXtmdW5jdGlvbiBQb3NpdGlvbihsaW5lLCBjb2wpe19jbGFzc0NhbGxDaGVjayh0aGlzLCBQb3NpdGlvbik7dGhpcy5saW5lID0gbGluZTt0aGlzLmNvbHVtbiA9IGNvbDt9UG9zaXRpb24ucHJvdG90eXBlLm9mZnNldCA9IGZ1bmN0aW9uIG9mZnNldChuKXtyZXR1cm4gbmV3IFBvc2l0aW9uKHRoaXMubGluZSwgdGhpcy5jb2x1bW4gKyBuKTt9O3JldHVybiBQb3NpdGlvbjt9KSgpO3ZhciBTb3VyY2VMb2NhdGlvbj1leHBvcnRzLlNvdXJjZUxvY2F0aW9uID0gZnVuY3Rpb24gU291cmNlTG9jYXRpb24ocCwgc3RhcnQsIGVuZCl7X2NsYXNzQ2FsbENoZWNrKHRoaXMsIFNvdXJjZUxvY2F0aW9uKTt0aGlzLnN0YXJ0ID0gc3RhcnQ7dGhpcy5lbmQgPSBlbmQ7aWYocC5zb3VyY2VGaWxlICE9PSBudWxsKXRoaXMuc291cmNlID0gcC5zb3VyY2VGaWxlO307ZnVuY3Rpb24gZ2V0TGluZUluZm8oaW5wdXQsIG9mZnNldCl7Zm9yKHZhciBsaW5lPTEsIGN1cj0wOzspIHtsaW5lQnJlYWtHLmxhc3RJbmRleCA9IGN1cjt2YXIgbWF0Y2g9bGluZUJyZWFrRy5leGVjKGlucHV0KTtpZihtYXRjaCAmJiBtYXRjaC5pbmRleCA8IG9mZnNldCl7KytsaW5lO2N1ciA9IG1hdGNoLmluZGV4ICsgbWF0Y2hbMF0ubGVuZ3RoO31lbHNlIHtyZXR1cm4gbmV3IFBvc2l0aW9uKGxpbmUsIG9mZnNldCAtIGN1cik7fX19dmFyIHBwPVBhcnNlci5wcm90b3R5cGU7cHAucmFpc2UgPSBmdW5jdGlvbihwb3MsIG1lc3NhZ2Upe3ZhciBsb2M9Z2V0TGluZUluZm8odGhpcy5pbnB1dCwgcG9zKTttZXNzYWdlICs9IFwiIChcIiArIGxvYy5saW5lICsgXCI6XCIgKyBsb2MuY29sdW1uICsgXCIpXCI7dmFyIGVycj1uZXcgU3ludGF4RXJyb3IobWVzc2FnZSk7ZXJyLnBvcyA9IHBvcztlcnIubG9jID0gbG9jO2Vyci5yYWlzZWRBdCA9IHRoaXMucG9zO3Rocm93IGVycjt9O3BwLmN1clBvc2l0aW9uID0gZnVuY3Rpb24oKXtyZXR1cm4gbmV3IFBvc2l0aW9uKHRoaXMuY3VyTGluZSwgdGhpcy5wb3MgLSB0aGlzLmxpbmVTdGFydCk7fTtwcC5tYXJrUG9zaXRpb24gPSBmdW5jdGlvbigpe3JldHVybiB0aGlzLm9wdGlvbnMubG9jYXRpb25zP1t0aGlzLnN0YXJ0LCB0aGlzLnN0YXJ0TG9jXTp0aGlzLnN0YXJ0O307fSwge1wiLi9zdGF0ZVwiOjEzLCBcIi4vd2hpdGVzcGFjZVwiOjE5LCB1dGlsOjV9XSwgOTpbZnVuY3Rpb24oX2RlcmVxXywgbW9kdWxlLCBleHBvcnRzKXtcInVzZSBzdHJpY3RcIjt2YXIgdHQ9X2RlcmVxXyhcIi4vdG9rZW50eXBlXCIpLnR5cGVzO3ZhciBQYXJzZXI9X2RlcmVxXyhcIi4vc3RhdGVcIikuUGFyc2VyO3ZhciByZXNlcnZlZFdvcmRzPV9kZXJlcV8oXCIuL2lkZW50aWZpZXJcIikucmVzZXJ2ZWRXb3Jkczt2YXIgaGFzPV9kZXJlcV8oXCIuL3V0aWxcIikuaGFzO3ZhciBwcD1QYXJzZXIucHJvdG90eXBlO3BwLnRvQXNzaWduYWJsZSA9IGZ1bmN0aW9uKG5vZGUsIGlzQmluZGluZyl7aWYodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYgJiYgbm9kZSl7c3dpdGNoKG5vZGUudHlwZSl7Y2FzZSBcIklkZW50aWZpZXJcIjpjYXNlIFwiT2JqZWN0UGF0dGVyblwiOmNhc2UgXCJBcnJheVBhdHRlcm5cIjpjYXNlIFwiQXNzaWdubWVudFBhdHRlcm5cIjpicmVhaztjYXNlIFwiT2JqZWN0RXhwcmVzc2lvblwiOm5vZGUudHlwZSA9IFwiT2JqZWN0UGF0dGVyblwiO2Zvcih2YXIgaT0wOyBpIDwgbm9kZS5wcm9wZXJ0aWVzLmxlbmd0aDsgaSsrKSB7dmFyIHByb3A9bm9kZS5wcm9wZXJ0aWVzW2ldO2lmKHByb3Aua2luZCAhPT0gXCJpbml0XCIpdGhpcy5yYWlzZShwcm9wLmtleS5zdGFydCwgXCJPYmplY3QgcGF0dGVybiBjYW4ndCBjb250YWluIGdldHRlciBvciBzZXR0ZXJcIik7dGhpcy50b0Fzc2lnbmFibGUocHJvcC52YWx1ZSwgaXNCaW5kaW5nKTt9YnJlYWs7Y2FzZSBcIkFycmF5RXhwcmVzc2lvblwiOm5vZGUudHlwZSA9IFwiQXJyYXlQYXR0ZXJuXCI7dGhpcy50b0Fzc2lnbmFibGVMaXN0KG5vZGUuZWxlbWVudHMsIGlzQmluZGluZyk7YnJlYWs7Y2FzZSBcIkFzc2lnbm1lbnRFeHByZXNzaW9uXCI6aWYobm9kZS5vcGVyYXRvciA9PT0gXCI9XCIpe25vZGUudHlwZSA9IFwiQXNzaWdubWVudFBhdHRlcm5cIjt9ZWxzZSB7dGhpcy5yYWlzZShub2RlLmxlZnQuZW5kLCBcIk9ubHkgJz0nIG9wZXJhdG9yIGNhbiBiZSB1c2VkIGZvciBzcGVjaWZ5aW5nIGRlZmF1bHQgdmFsdWUuXCIpO31icmVhaztjYXNlIFwiUGFyZW50aGVzaXplZEV4cHJlc3Npb25cIjpub2RlLmV4cHJlc3Npb24gPSB0aGlzLnRvQXNzaWduYWJsZShub2RlLmV4cHJlc3Npb24sIGlzQmluZGluZyk7YnJlYWs7Y2FzZSBcIk1lbWJlckV4cHJlc3Npb25cIjppZighaXNCaW5kaW5nKWJyZWFrO2RlZmF1bHQ6dGhpcy5yYWlzZShub2RlLnN0YXJ0LCBcIkFzc2lnbmluZyB0byBydmFsdWVcIik7fX1yZXR1cm4gbm9kZTt9O3BwLnRvQXNzaWduYWJsZUxpc3QgPSBmdW5jdGlvbihleHByTGlzdCwgaXNCaW5kaW5nKXt2YXIgZW5kPWV4cHJMaXN0Lmxlbmd0aDtpZihlbmQpe3ZhciBsYXN0PWV4cHJMaXN0W2VuZCAtIDFdO2lmKGxhc3QgJiYgbGFzdC50eXBlID09IFwiUmVzdEVsZW1lbnRcIil7LS1lbmQ7fWVsc2UgaWYobGFzdCAmJiBsYXN0LnR5cGUgPT0gXCJTcHJlYWRFbGVtZW50XCIpe2xhc3QudHlwZSA9IFwiUmVzdEVsZW1lbnRcIjt2YXIgYXJnPWxhc3QuYXJndW1lbnQ7dGhpcy50b0Fzc2lnbmFibGUoYXJnLCBpc0JpbmRpbmcpO2lmKGFyZy50eXBlICE9PSBcIklkZW50aWZpZXJcIiAmJiBhcmcudHlwZSAhPT0gXCJNZW1iZXJFeHByZXNzaW9uXCIgJiYgYXJnLnR5cGUgIT09IFwiQXJyYXlQYXR0ZXJuXCIpdGhpcy51bmV4cGVjdGVkKGFyZy5zdGFydCk7LS1lbmQ7fX1mb3IodmFyIGk9MDsgaSA8IGVuZDsgaSsrKSB7dmFyIGVsdD1leHByTGlzdFtpXTtpZihlbHQpdGhpcy50b0Fzc2lnbmFibGUoZWx0LCBpc0JpbmRpbmcpO31yZXR1cm4gZXhwckxpc3Q7fTtwcC5wYXJzZVNwcmVhZCA9IGZ1bmN0aW9uKHJlZlNob3J0aGFuZERlZmF1bHRQb3Mpe3ZhciBub2RlPXRoaXMuc3RhcnROb2RlKCk7dGhpcy5uZXh0KCk7bm9kZS5hcmd1bWVudCA9IHRoaXMucGFyc2VNYXliZUFzc2lnbihyZWZTaG9ydGhhbmREZWZhdWx0UG9zKTtyZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiU3ByZWFkRWxlbWVudFwiKTt9O3BwLnBhcnNlUmVzdCA9IGZ1bmN0aW9uKCl7dmFyIG5vZGU9dGhpcy5zdGFydE5vZGUoKTt0aGlzLm5leHQoKTtub2RlLmFyZ3VtZW50ID0gdGhpcy50eXBlID09PSB0dC5uYW1lIHx8IHRoaXMudHlwZSA9PT0gdHQuYnJhY2tldEw/dGhpcy5wYXJzZUJpbmRpbmdBdG9tKCk6dGhpcy51bmV4cGVjdGVkKCk7cmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIlJlc3RFbGVtZW50XCIpO307cHAucGFyc2VCaW5kaW5nQXRvbSA9IGZ1bmN0aW9uKCl7aWYodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uIDwgNilyZXR1cm4gdGhpcy5wYXJzZUlkZW50KCk7c3dpdGNoKHRoaXMudHlwZSl7Y2FzZSB0dC5uYW1lOnJldHVybiB0aGlzLnBhcnNlSWRlbnQoKTtjYXNlIHR0LmJyYWNrZXRMOnZhciBub2RlPXRoaXMuc3RhcnROb2RlKCk7dGhpcy5uZXh0KCk7bm9kZS5lbGVtZW50cyA9IHRoaXMucGFyc2VCaW5kaW5nTGlzdCh0dC5icmFja2V0UiwgdHJ1ZSwgdHJ1ZSk7cmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkFycmF5UGF0dGVyblwiKTtjYXNlIHR0LmJyYWNlTDpyZXR1cm4gdGhpcy5wYXJzZU9iaih0cnVlKTtkZWZhdWx0OnRoaXMudW5leHBlY3RlZCgpO319O3BwLnBhcnNlQmluZGluZ0xpc3QgPSBmdW5jdGlvbihjbG9zZSwgYWxsb3dFbXB0eSwgYWxsb3dUcmFpbGluZ0NvbW1hKXt2YXIgZWx0cz1bXSwgZmlyc3Q9dHJ1ZTt3aGlsZSghdGhpcy5lYXQoY2xvc2UpKSB7aWYoZmlyc3QpZmlyc3QgPSBmYWxzZTtlbHNlIHRoaXMuZXhwZWN0KHR0LmNvbW1hKTtpZihhbGxvd0VtcHR5ICYmIHRoaXMudHlwZSA9PT0gdHQuY29tbWEpe2VsdHMucHVzaChudWxsKTt9ZWxzZSBpZihhbGxvd1RyYWlsaW5nQ29tbWEgJiYgdGhpcy5hZnRlclRyYWlsaW5nQ29tbWEoY2xvc2UpKXticmVhazt9ZWxzZSBpZih0aGlzLnR5cGUgPT09IHR0LmVsbGlwc2lzKXt2YXIgcmVzdD10aGlzLnBhcnNlUmVzdCgpO3RoaXMucGFyc2VCaW5kaW5nTGlzdEl0ZW0ocmVzdCk7ZWx0cy5wdXNoKHJlc3QpO3RoaXMuZXhwZWN0KGNsb3NlKTticmVhazt9ZWxzZSB7dmFyIGVsZW09dGhpcy5wYXJzZU1heWJlRGVmYXVsdCh0aGlzLnN0YXJ0LCB0aGlzLnN0YXJ0TG9jKTt0aGlzLnBhcnNlQmluZGluZ0xpc3RJdGVtKGVsZW0pO2VsdHMucHVzaChlbGVtKTt9fXJldHVybiBlbHRzO307cHAucGFyc2VCaW5kaW5nTGlzdEl0ZW0gPSBmdW5jdGlvbihwYXJhbSl7cmV0dXJuIHBhcmFtO307cHAucGFyc2VNYXliZURlZmF1bHQgPSBmdW5jdGlvbihzdGFydFBvcywgc3RhcnRMb2MsIGxlZnQpe2lmKEFycmF5LmlzQXJyYXkoc3RhcnRQb3MpKXtpZih0aGlzLm9wdGlvbnMubG9jYXRpb25zICYmIG5vQ2FsbHMgPT09IHVuZGVmaW5lZCl7bGVmdCA9IHN0YXJ0TG9jO3N0YXJ0TG9jID0gc3RhcnRQb3NbMV07c3RhcnRQb3MgPSBzdGFydFBvc1swXTt9fWxlZnQgPSBsZWZ0IHx8IHRoaXMucGFyc2VCaW5kaW5nQXRvbSgpO2lmKCF0aGlzLmVhdCh0dC5lcSkpcmV0dXJuIGxlZnQ7dmFyIG5vZGU9dGhpcy5zdGFydE5vZGVBdChzdGFydFBvcywgc3RhcnRMb2MpO25vZGUub3BlcmF0b3IgPSBcIj1cIjtub2RlLmxlZnQgPSBsZWZ0O25vZGUucmlnaHQgPSB0aGlzLnBhcnNlTWF5YmVBc3NpZ24oKTtyZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiQXNzaWdubWVudFBhdHRlcm5cIik7fTtwcC5jaGVja0xWYWwgPSBmdW5jdGlvbihleHByLCBpc0JpbmRpbmcsIGNoZWNrQ2xhc2hlcyl7c3dpdGNoKGV4cHIudHlwZSl7Y2FzZSBcIklkZW50aWZpZXJcIjppZih0aGlzLnN0cmljdCAmJiAocmVzZXJ2ZWRXb3Jkcy5zdHJpY3RCaW5kKGV4cHIubmFtZSkgfHwgcmVzZXJ2ZWRXb3Jkcy5zdHJpY3QoZXhwci5uYW1lKSkpdGhpcy5yYWlzZShleHByLnN0YXJ0LCAoaXNCaW5kaW5nP1wiQmluZGluZyBcIjpcIkFzc2lnbmluZyB0byBcIikgKyBleHByLm5hbWUgKyBcIiBpbiBzdHJpY3QgbW9kZVwiKTtpZihjaGVja0NsYXNoZXMpe2lmKGhhcyhjaGVja0NsYXNoZXMsIGV4cHIubmFtZSkpdGhpcy5yYWlzZShleHByLnN0YXJ0LCBcIkFyZ3VtZW50IG5hbWUgY2xhc2ggaW4gc3RyaWN0IG1vZGVcIik7Y2hlY2tDbGFzaGVzW2V4cHIubmFtZV0gPSB0cnVlO31icmVhaztjYXNlIFwiTWVtYmVyRXhwcmVzc2lvblwiOmlmKGlzQmluZGluZyl0aGlzLnJhaXNlKGV4cHIuc3RhcnQsIChpc0JpbmRpbmc/XCJCaW5kaW5nXCI6XCJBc3NpZ25pbmcgdG9cIikgKyBcIiBtZW1iZXIgZXhwcmVzc2lvblwiKTticmVhaztjYXNlIFwiT2JqZWN0UGF0dGVyblwiOmZvcih2YXIgaT0wOyBpIDwgZXhwci5wcm9wZXJ0aWVzLmxlbmd0aDsgaSsrKSB7dGhpcy5jaGVja0xWYWwoZXhwci5wcm9wZXJ0aWVzW2ldLnZhbHVlLCBpc0JpbmRpbmcsIGNoZWNrQ2xhc2hlcyk7fWJyZWFrO2Nhc2UgXCJBcnJheVBhdHRlcm5cIjpmb3IodmFyIGk9MDsgaSA8IGV4cHIuZWxlbWVudHMubGVuZ3RoOyBpKyspIHt2YXIgZWxlbT1leHByLmVsZW1lbnRzW2ldO2lmKGVsZW0pdGhpcy5jaGVja0xWYWwoZWxlbSwgaXNCaW5kaW5nLCBjaGVja0NsYXNoZXMpO31icmVhaztjYXNlIFwiQXNzaWdubWVudFBhdHRlcm5cIjp0aGlzLmNoZWNrTFZhbChleHByLmxlZnQsIGlzQmluZGluZywgY2hlY2tDbGFzaGVzKTticmVhaztjYXNlIFwiUmVzdEVsZW1lbnRcIjp0aGlzLmNoZWNrTFZhbChleHByLmFyZ3VtZW50LCBpc0JpbmRpbmcsIGNoZWNrQ2xhc2hlcyk7YnJlYWs7Y2FzZSBcIlBhcmVudGhlc2l6ZWRFeHByZXNzaW9uXCI6dGhpcy5jaGVja0xWYWwoZXhwci5leHByZXNzaW9uLCBpc0JpbmRpbmcsIGNoZWNrQ2xhc2hlcyk7YnJlYWs7ZGVmYXVsdDp0aGlzLnJhaXNlKGV4cHIuc3RhcnQsIChpc0JpbmRpbmc/XCJCaW5kaW5nXCI6XCJBc3NpZ25pbmcgdG9cIikgKyBcIiBydmFsdWVcIik7fX07fSwge1wiLi9pZGVudGlmaWVyXCI6NywgXCIuL3N0YXRlXCI6MTMsIFwiLi90b2tlbnR5cGVcIjoxNywgXCIuL3V0aWxcIjoxOH1dLCAxMDpbZnVuY3Rpb24oX2RlcmVxXywgbW9kdWxlLCBleHBvcnRzKXtcInVzZSBzdHJpY3RcIjt2YXIgX2NsYXNzQ2FsbENoZWNrPWZ1bmN0aW9uIF9jbGFzc0NhbGxDaGVjayhpbnN0YW5jZSwgQ29uc3RydWN0b3Ipe2lmKCEoaW5zdGFuY2UgaW5zdGFuY2VvZiBDb25zdHJ1Y3Rvcikpe3Rocm93IG5ldyBUeXBlRXJyb3IoXCJDYW5ub3QgY2FsbCBhIGNsYXNzIGFzIGEgZnVuY3Rpb25cIik7fX07ZXhwb3J0cy5fX2VzTW9kdWxlID0gdHJ1ZTt2YXIgUGFyc2VyPV9kZXJlcV8oXCIuL3N0YXRlXCIpLlBhcnNlcjt2YXIgU291cmNlTG9jYXRpb249X2RlcmVxXyhcIi4vbG9jYXRpb25cIikuU291cmNlTG9jYXRpb247dmFyIHBwPVBhcnNlci5wcm90b3R5cGU7dmFyIE5vZGU9ZXhwb3J0cy5Ob2RlID0gZnVuY3Rpb24gTm9kZSgpe19jbGFzc0NhbGxDaGVjayh0aGlzLCBOb2RlKTt9O3BwLnN0YXJ0Tm9kZSA9IGZ1bmN0aW9uKCl7dmFyIG5vZGU9bmV3IE5vZGUoKTtub2RlLnN0YXJ0ID0gdGhpcy5zdGFydDtpZih0aGlzLm9wdGlvbnMubG9jYXRpb25zKW5vZGUubG9jID0gbmV3IFNvdXJjZUxvY2F0aW9uKHRoaXMsIHRoaXMuc3RhcnRMb2MpO2lmKHRoaXMub3B0aW9ucy5kaXJlY3RTb3VyY2VGaWxlKW5vZGUuc291cmNlRmlsZSA9IHRoaXMub3B0aW9ucy5kaXJlY3RTb3VyY2VGaWxlO2lmKHRoaXMub3B0aW9ucy5yYW5nZXMpbm9kZS5yYW5nZSA9IFt0aGlzLnN0YXJ0LCAwXTtyZXR1cm4gbm9kZTt9O3BwLnN0YXJ0Tm9kZUF0ID0gZnVuY3Rpb24ocG9zLCBsb2Mpe3ZhciBub2RlPW5ldyBOb2RlKCk7aWYoQXJyYXkuaXNBcnJheShwb3MpKXtpZih0aGlzLm9wdGlvbnMubG9jYXRpb25zICYmIGxvYyA9PT0gdW5kZWZpbmVkKXtsb2MgPSBwb3NbMV07cG9zID0gcG9zWzBdO319bm9kZS5zdGFydCA9IHBvcztpZih0aGlzLm9wdGlvbnMubG9jYXRpb25zKW5vZGUubG9jID0gbmV3IFNvdXJjZUxvY2F0aW9uKHRoaXMsIGxvYyk7aWYodGhpcy5vcHRpb25zLmRpcmVjdFNvdXJjZUZpbGUpbm9kZS5zb3VyY2VGaWxlID0gdGhpcy5vcHRpb25zLmRpcmVjdFNvdXJjZUZpbGU7aWYodGhpcy5vcHRpb25zLnJhbmdlcylub2RlLnJhbmdlID0gW3BvcywgMF07cmV0dXJuIG5vZGU7fTtwcC5maW5pc2hOb2RlID0gZnVuY3Rpb24obm9kZSwgdHlwZSl7bm9kZS50eXBlID0gdHlwZTtub2RlLmVuZCA9IHRoaXMubGFzdFRva0VuZDtpZih0aGlzLm9wdGlvbnMubG9jYXRpb25zKW5vZGUubG9jLmVuZCA9IHRoaXMubGFzdFRva0VuZExvYztpZih0aGlzLm9wdGlvbnMucmFuZ2VzKW5vZGUucmFuZ2VbMV0gPSB0aGlzLmxhc3RUb2tFbmQ7cmV0dXJuIG5vZGU7fTtwcC5maW5pc2hOb2RlQXQgPSBmdW5jdGlvbihub2RlLCB0eXBlLCBwb3MsIGxvYyl7bm9kZS50eXBlID0gdHlwZTtpZihBcnJheS5pc0FycmF5KHBvcykpe2lmKHRoaXMub3B0aW9ucy5sb2NhdGlvbnMgJiYgbG9jID09PSB1bmRlZmluZWQpe2xvYyA9IHBvc1sxXTtwb3MgPSBwb3NbMF07fX1ub2RlLmVuZCA9IHBvcztpZih0aGlzLm9wdGlvbnMubG9jYXRpb25zKW5vZGUubG9jLmVuZCA9IGxvYztpZih0aGlzLm9wdGlvbnMucmFuZ2VzKW5vZGUucmFuZ2VbMV0gPSBwb3M7cmV0dXJuIG5vZGU7fTt9LCB7XCIuL2xvY2F0aW9uXCI6OCwgXCIuL3N0YXRlXCI6MTN9XSwgMTE6W2Z1bmN0aW9uKF9kZXJlcV8sIG1vZHVsZSwgZXhwb3J0cyl7XCJ1c2Ugc3RyaWN0XCI7ZXhwb3J0cy5nZXRPcHRpb25zID0gZ2V0T3B0aW9ucztleHBvcnRzLl9fZXNNb2R1bGUgPSB0cnVlO3ZhciBfdXRpbD1fZGVyZXFfKFwiLi91dGlsXCIpO3ZhciBoYXM9X3V0aWwuaGFzO3ZhciBpc0FycmF5PV91dGlsLmlzQXJyYXk7dmFyIFNvdXJjZUxvY2F0aW9uPV9kZXJlcV8oXCIuL2xvY2F0aW9uXCIpLlNvdXJjZUxvY2F0aW9uO3ZhciBkZWZhdWx0T3B0aW9ucz17ZWNtYVZlcnNpb246NSwgc291cmNlVHlwZTpcInNjcmlwdFwiLCBvbkluc2VydGVkU2VtaWNvbG9uOm51bGwsIG9uVHJhaWxpbmdDb21tYTpudWxsLCBhbGxvd1Jlc2VydmVkOnRydWUsIGFsbG93UmV0dXJuT3V0c2lkZUZ1bmN0aW9uOmZhbHNlLCBhbGxvd0ltcG9ydEV4cG9ydEV2ZXJ5d2hlcmU6ZmFsc2UsIGFsbG93SGFzaEJhbmc6ZmFsc2UsIGxvY2F0aW9uczpmYWxzZSwgb25Ub2tlbjpudWxsLCBvbkNvbW1lbnQ6bnVsbCwgcmFuZ2VzOmZhbHNlLCBwcm9ncmFtOm51bGwsIHNvdXJjZUZpbGU6bnVsbCwgZGlyZWN0U291cmNlRmlsZTpudWxsLCBwcmVzZXJ2ZVBhcmVuczpmYWxzZSwgcGx1Z2luczp7fX07ZXhwb3J0cy5kZWZhdWx0T3B0aW9ucyA9IGRlZmF1bHRPcHRpb25zO2Z1bmN0aW9uIGdldE9wdGlvbnMob3B0cyl7dmFyIG9wdGlvbnM9e307Zm9yKHZhciBvcHQgaW4gZGVmYXVsdE9wdGlvbnMpIHtvcHRpb25zW29wdF0gPSBvcHRzICYmIGhhcyhvcHRzLCBvcHQpP29wdHNbb3B0XTpkZWZhdWx0T3B0aW9uc1tvcHRdO31pZihpc0FycmF5KG9wdGlvbnMub25Ub2tlbikpeyhmdW5jdGlvbigpe3ZhciB0b2tlbnM9b3B0aW9ucy5vblRva2VuO29wdGlvbnMub25Ub2tlbiA9IGZ1bmN0aW9uKHRva2VuKXtyZXR1cm4gdG9rZW5zLnB1c2godG9rZW4pO307fSkoKTt9aWYoaXNBcnJheShvcHRpb25zLm9uQ29tbWVudCkpb3B0aW9ucy5vbkNvbW1lbnQgPSBwdXNoQ29tbWVudChvcHRpb25zLCBvcHRpb25zLm9uQ29tbWVudCk7cmV0dXJuIG9wdGlvbnM7fWZ1bmN0aW9uIHB1c2hDb21tZW50KG9wdGlvbnMsIGFycmF5KXtyZXR1cm4gZnVuY3Rpb24oYmxvY2ssIHRleHQsIHN0YXJ0LCBlbmQsIHN0YXJ0TG9jLCBlbmRMb2Mpe3ZhciBjb21tZW50PXt0eXBlOmJsb2NrP1wiQmxvY2tcIjpcIkxpbmVcIiwgdmFsdWU6dGV4dCwgc3RhcnQ6c3RhcnQsIGVuZDplbmR9O2lmKG9wdGlvbnMubG9jYXRpb25zKWNvbW1lbnQubG9jID0gbmV3IFNvdXJjZUxvY2F0aW9uKHRoaXMsIHN0YXJ0TG9jLCBlbmRMb2MpO2lmKG9wdGlvbnMucmFuZ2VzKWNvbW1lbnQucmFuZ2UgPSBbc3RhcnQsIGVuZF07YXJyYXkucHVzaChjb21tZW50KTt9O319LCB7XCIuL2xvY2F0aW9uXCI6OCwgXCIuL3V0aWxcIjoxOH1dLCAxMjpbZnVuY3Rpb24oX2RlcmVxXywgbW9kdWxlLCBleHBvcnRzKXtcInVzZSBzdHJpY3RcIjt2YXIgdHQ9X2RlcmVxXyhcIi4vdG9rZW50eXBlXCIpLnR5cGVzO3ZhciBQYXJzZXI9X2RlcmVxXyhcIi4vc3RhdGVcIikuUGFyc2VyO3ZhciBsaW5lQnJlYWs9X2RlcmVxXyhcIi4vd2hpdGVzcGFjZVwiKS5saW5lQnJlYWs7dmFyIHBwPVBhcnNlci5wcm90b3R5cGU7cHAuaXNVc2VTdHJpY3QgPSBmdW5jdGlvbihzdG10KXtyZXR1cm4gdGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDUgJiYgc3RtdC50eXBlID09PSBcIkV4cHJlc3Npb25TdGF0ZW1lbnRcIiAmJiBzdG10LmV4cHJlc3Npb24udHlwZSA9PT0gXCJMaXRlcmFsXCIgJiYgc3RtdC5leHByZXNzaW9uLnZhbHVlID09PSBcInVzZSBzdHJpY3RcIjt9O3BwLmVhdCA9IGZ1bmN0aW9uKHR5cGUpe2lmKHRoaXMudHlwZSA9PT0gdHlwZSl7dGhpcy5uZXh0KCk7cmV0dXJuIHRydWU7fWVsc2Uge3JldHVybiBmYWxzZTt9fTtwcC5pc0NvbnRleHR1YWwgPSBmdW5jdGlvbihuYW1lKXtyZXR1cm4gdGhpcy50eXBlID09PSB0dC5uYW1lICYmIHRoaXMudmFsdWUgPT09IG5hbWU7fTtwcC5lYXRDb250ZXh0dWFsID0gZnVuY3Rpb24obmFtZSl7cmV0dXJuIHRoaXMudmFsdWUgPT09IG5hbWUgJiYgdGhpcy5lYXQodHQubmFtZSk7fTtwcC5leHBlY3RDb250ZXh0dWFsID0gZnVuY3Rpb24obmFtZSl7aWYoIXRoaXMuZWF0Q29udGV4dHVhbChuYW1lKSl0aGlzLnVuZXhwZWN0ZWQoKTt9O3BwLmNhbkluc2VydFNlbWljb2xvbiA9IGZ1bmN0aW9uKCl7cmV0dXJuIHRoaXMudHlwZSA9PT0gdHQuZW9mIHx8IHRoaXMudHlwZSA9PT0gdHQuYnJhY2VSIHx8IGxpbmVCcmVhay50ZXN0KHRoaXMuaW5wdXQuc2xpY2UodGhpcy5sYXN0VG9rRW5kLCB0aGlzLnN0YXJ0KSk7fTtwcC5pbnNlcnRTZW1pY29sb24gPSBmdW5jdGlvbigpe2lmKHRoaXMuY2FuSW5zZXJ0U2VtaWNvbG9uKCkpe2lmKHRoaXMub3B0aW9ucy5vbkluc2VydGVkU2VtaWNvbG9uKXRoaXMub3B0aW9ucy5vbkluc2VydGVkU2VtaWNvbG9uKHRoaXMubGFzdFRva0VuZCwgdGhpcy5sYXN0VG9rRW5kTG9jKTtyZXR1cm4gdHJ1ZTt9fTtwcC5zZW1pY29sb24gPSBmdW5jdGlvbigpe2lmKCF0aGlzLmVhdCh0dC5zZW1pKSAmJiAhdGhpcy5pbnNlcnRTZW1pY29sb24oKSl0aGlzLnVuZXhwZWN0ZWQoKTt9O3BwLmFmdGVyVHJhaWxpbmdDb21tYSA9IGZ1bmN0aW9uKHRva1R5cGUpe2lmKHRoaXMudHlwZSA9PSB0b2tUeXBlKXtpZih0aGlzLm9wdGlvbnMub25UcmFpbGluZ0NvbW1hKXRoaXMub3B0aW9ucy5vblRyYWlsaW5nQ29tbWEodGhpcy5sYXN0VG9rU3RhcnQsIHRoaXMubGFzdFRva1N0YXJ0TG9jKTt0aGlzLm5leHQoKTtyZXR1cm4gdHJ1ZTt9fTtwcC5leHBlY3QgPSBmdW5jdGlvbih0eXBlKXt0aGlzLmVhdCh0eXBlKSB8fCB0aGlzLnVuZXhwZWN0ZWQoKTt9O3BwLnVuZXhwZWN0ZWQgPSBmdW5jdGlvbihwb3Mpe3RoaXMucmFpc2UocG9zICE9IG51bGw/cG9zOnRoaXMuc3RhcnQsIFwiVW5leHBlY3RlZCB0b2tlblwiKTt9O30sIHtcIi4vc3RhdGVcIjoxMywgXCIuL3Rva2VudHlwZVwiOjE3LCBcIi4vd2hpdGVzcGFjZVwiOjE5fV0sIDEzOltmdW5jdGlvbihfZGVyZXFfLCBtb2R1bGUsIGV4cG9ydHMpe1widXNlIHN0cmljdFwiO2V4cG9ydHMuUGFyc2VyID0gUGFyc2VyO2V4cG9ydHMuX19lc01vZHVsZSA9IHRydWU7dmFyIF9pZGVudGlmaWVyPV9kZXJlcV8oXCIuL2lkZW50aWZpZXJcIik7dmFyIHJlc2VydmVkV29yZHM9X2lkZW50aWZpZXIucmVzZXJ2ZWRXb3Jkczt2YXIga2V5d29yZHM9X2lkZW50aWZpZXIua2V5d29yZHM7dmFyIHR0PV9kZXJlcV8oXCIuL3Rva2VudHlwZVwiKS50eXBlczt2YXIgbGluZUJyZWFrPV9kZXJlcV8oXCIuL3doaXRlc3BhY2VcIikubGluZUJyZWFrO2Z1bmN0aW9uIFBhcnNlcihvcHRpb25zLCBpbnB1dCwgc3RhcnRQb3Mpe3RoaXMub3B0aW9ucyA9IG9wdGlvbnM7dGhpcy5zb3VyY2VGaWxlID0gdGhpcy5vcHRpb25zLnNvdXJjZUZpbGUgfHwgbnVsbDt0aGlzLmlzS2V5d29yZCA9IGtleXdvcmRzW3RoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2PzY6NV07dGhpcy5pc1Jlc2VydmVkV29yZCA9IHJlc2VydmVkV29yZHNbdGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uXTt0aGlzLmlucHV0ID0gaW5wdXQ7dGhpcy5sb2FkUGx1Z2lucyh0aGlzLm9wdGlvbnMucGx1Z2lucyk7aWYoc3RhcnRQb3Mpe3RoaXMucG9zID0gc3RhcnRQb3M7dGhpcy5saW5lU3RhcnQgPSBNYXRoLm1heCgwLCB0aGlzLmlucHV0Lmxhc3RJbmRleE9mKFwiXFxuXCIsIHN0YXJ0UG9zKSk7dGhpcy5jdXJMaW5lID0gdGhpcy5pbnB1dC5zbGljZSgwLCB0aGlzLmxpbmVTdGFydCkuc3BsaXQobGluZUJyZWFrKS5sZW5ndGg7fWVsc2Uge3RoaXMucG9zID0gdGhpcy5saW5lU3RhcnQgPSAwO3RoaXMuY3VyTGluZSA9IDE7fXRoaXMudHlwZSA9IHR0LmVvZjt0aGlzLnZhbHVlID0gbnVsbDt0aGlzLnN0YXJ0ID0gdGhpcy5lbmQgPSB0aGlzLnBvczt0aGlzLnN0YXJ0TG9jID0gdGhpcy5lbmRMb2MgPSBudWxsO3RoaXMubGFzdFRva0VuZExvYyA9IHRoaXMubGFzdFRva1N0YXJ0TG9jID0gbnVsbDt0aGlzLmxhc3RUb2tTdGFydCA9IHRoaXMubGFzdFRva0VuZCA9IHRoaXMucG9zO3RoaXMuY29udGV4dCA9IHRoaXMuaW5pdGlhbENvbnRleHQoKTt0aGlzLmV4cHJBbGxvd2VkID0gdHJ1ZTt0aGlzLnN0cmljdCA9IHRoaXMuaW5Nb2R1bGUgPSB0aGlzLm9wdGlvbnMuc291cmNlVHlwZSA9PT0gXCJtb2R1bGVcIjt0aGlzLnBvdGVudGlhbEFycm93QXQgPSAtMTt0aGlzLmluRnVuY3Rpb24gPSB0aGlzLmluR2VuZXJhdG9yID0gZmFsc2U7dGhpcy5sYWJlbHMgPSBbXTtpZih0aGlzLnBvcyA9PT0gMCAmJiB0aGlzLm9wdGlvbnMuYWxsb3dIYXNoQmFuZyAmJiB0aGlzLmlucHV0LnNsaWNlKDAsIDIpID09PSBcIiMhXCIpdGhpcy5za2lwTGluZUNvbW1lbnQoMik7fVBhcnNlci5wcm90b3R5cGUuZXh0ZW5kID0gZnVuY3Rpb24obmFtZSwgZil7dGhpc1tuYW1lXSA9IGYodGhpc1tuYW1lXSk7fTt2YXIgcGx1Z2lucz17fTtleHBvcnRzLnBsdWdpbnMgPSBwbHVnaW5zO1BhcnNlci5wcm90b3R5cGUubG9hZFBsdWdpbnMgPSBmdW5jdGlvbihwbHVnaW5zKXtmb3IodmFyIF9uYW1lIGluIHBsdWdpbnMpIHt2YXIgcGx1Z2luPWV4cG9ydHMucGx1Z2luc1tfbmFtZV07aWYoIXBsdWdpbil0aHJvdyBuZXcgRXJyb3IoXCJQbHVnaW4gJ1wiICsgX25hbWUgKyBcIicgbm90IGZvdW5kXCIpO3BsdWdpbih0aGlzLCBwbHVnaW5zW19uYW1lXSk7fX07fSwge1wiLi9pZGVudGlmaWVyXCI6NywgXCIuL3Rva2VudHlwZVwiOjE3LCBcIi4vd2hpdGVzcGFjZVwiOjE5fV0sIDE0OltmdW5jdGlvbihfZGVyZXFfLCBtb2R1bGUsIGV4cG9ydHMpe1widXNlIHN0cmljdFwiO3ZhciB0dD1fZGVyZXFfKFwiLi90b2tlbnR5cGVcIikudHlwZXM7dmFyIFBhcnNlcj1fZGVyZXFfKFwiLi9zdGF0ZVwiKS5QYXJzZXI7dmFyIGxpbmVCcmVhaz1fZGVyZXFfKFwiLi93aGl0ZXNwYWNlXCIpLmxpbmVCcmVhazt2YXIgcHA9UGFyc2VyLnByb3RvdHlwZTtwcC5wYXJzZVRvcExldmVsID0gZnVuY3Rpb24obm9kZSl7dmFyIGZpcnN0PXRydWU7aWYoIW5vZGUuYm9keSlub2RlLmJvZHkgPSBbXTt3aGlsZSh0aGlzLnR5cGUgIT09IHR0LmVvZikge3ZhciBzdG10PXRoaXMucGFyc2VTdGF0ZW1lbnQodHJ1ZSwgdHJ1ZSk7bm9kZS5ib2R5LnB1c2goc3RtdCk7aWYoZmlyc3QgJiYgdGhpcy5pc1VzZVN0cmljdChzdG10KSl0aGlzLnNldFN0cmljdCh0cnVlKTtmaXJzdCA9IGZhbHNlO310aGlzLm5leHQoKTtpZih0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNil7bm9kZS5zb3VyY2VUeXBlID0gdGhpcy5vcHRpb25zLnNvdXJjZVR5cGU7fXJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJQcm9ncmFtXCIpO307dmFyIGxvb3BMYWJlbD17a2luZDpcImxvb3BcIn0sIHN3aXRjaExhYmVsPXtraW5kOlwic3dpdGNoXCJ9O3BwLnBhcnNlU3RhdGVtZW50ID0gZnVuY3Rpb24oZGVjbGFyYXRpb24sIHRvcExldmVsKXt2YXIgc3RhcnR0eXBlPXRoaXMudHlwZSwgbm9kZT10aGlzLnN0YXJ0Tm9kZSgpO3N3aXRjaChzdGFydHR5cGUpe2Nhc2UgdHQuX2JyZWFrOmNhc2UgdHQuX2NvbnRpbnVlOnJldHVybiB0aGlzLnBhcnNlQnJlYWtDb250aW51ZVN0YXRlbWVudChub2RlLCBzdGFydHR5cGUua2V5d29yZCk7Y2FzZSB0dC5fZGVidWdnZXI6cmV0dXJuIHRoaXMucGFyc2VEZWJ1Z2dlclN0YXRlbWVudChub2RlKTtjYXNlIHR0Ll9kbzpyZXR1cm4gdGhpcy5wYXJzZURvU3RhdGVtZW50KG5vZGUpO2Nhc2UgdHQuX2ZvcjpyZXR1cm4gdGhpcy5wYXJzZUZvclN0YXRlbWVudChub2RlKTtjYXNlIHR0Ll9mdW5jdGlvbjppZighZGVjbGFyYXRpb24gJiYgdGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYpdGhpcy51bmV4cGVjdGVkKCk7cmV0dXJuIHRoaXMucGFyc2VGdW5jdGlvblN0YXRlbWVudChub2RlKTtjYXNlIHR0Ll9jbGFzczppZighZGVjbGFyYXRpb24pdGhpcy51bmV4cGVjdGVkKCk7cmV0dXJuIHRoaXMucGFyc2VDbGFzcyhub2RlLCB0cnVlKTtjYXNlIHR0Ll9pZjpyZXR1cm4gdGhpcy5wYXJzZUlmU3RhdGVtZW50KG5vZGUpO2Nhc2UgdHQuX3JldHVybjpyZXR1cm4gdGhpcy5wYXJzZVJldHVyblN0YXRlbWVudChub2RlKTtjYXNlIHR0Ll9zd2l0Y2g6cmV0dXJuIHRoaXMucGFyc2VTd2l0Y2hTdGF0ZW1lbnQobm9kZSk7Y2FzZSB0dC5fdGhyb3c6cmV0dXJuIHRoaXMucGFyc2VUaHJvd1N0YXRlbWVudChub2RlKTtjYXNlIHR0Ll90cnk6cmV0dXJuIHRoaXMucGFyc2VUcnlTdGF0ZW1lbnQobm9kZSk7Y2FzZSB0dC5fbGV0OmNhc2UgdHQuX2NvbnN0OmlmKCFkZWNsYXJhdGlvbil0aGlzLnVuZXhwZWN0ZWQoKTtjYXNlIHR0Ll92YXI6cmV0dXJuIHRoaXMucGFyc2VWYXJTdGF0ZW1lbnQobm9kZSwgc3RhcnR0eXBlKTtjYXNlIHR0Ll93aGlsZTpyZXR1cm4gdGhpcy5wYXJzZVdoaWxlU3RhdGVtZW50KG5vZGUpO2Nhc2UgdHQuX3dpdGg6cmV0dXJuIHRoaXMucGFyc2VXaXRoU3RhdGVtZW50KG5vZGUpO2Nhc2UgdHQuYnJhY2VMOnJldHVybiB0aGlzLnBhcnNlQmxvY2soKTtjYXNlIHR0LnNlbWk6cmV0dXJuIHRoaXMucGFyc2VFbXB0eVN0YXRlbWVudChub2RlKTtjYXNlIHR0Ll9leHBvcnQ6Y2FzZSB0dC5faW1wb3J0OmlmKCF0aGlzLm9wdGlvbnMuYWxsb3dJbXBvcnRFeHBvcnRFdmVyeXdoZXJlKXtpZighdG9wTGV2ZWwpdGhpcy5yYWlzZSh0aGlzLnN0YXJ0LCBcIidpbXBvcnQnIGFuZCAnZXhwb3J0JyBtYXkgb25seSBhcHBlYXIgYXQgdGhlIHRvcCBsZXZlbFwiKTtpZighdGhpcy5pbk1vZHVsZSl0aGlzLnJhaXNlKHRoaXMuc3RhcnQsIFwiJ2ltcG9ydCcgYW5kICdleHBvcnQnIG1heSBhcHBlYXIgb25seSB3aXRoICdzb3VyY2VUeXBlOiBtb2R1bGUnXCIpO31yZXR1cm4gc3RhcnR0eXBlID09PSB0dC5faW1wb3J0P3RoaXMucGFyc2VJbXBvcnQobm9kZSk6dGhpcy5wYXJzZUV4cG9ydChub2RlKTtkZWZhdWx0OnZhciBtYXliZU5hbWU9dGhpcy52YWx1ZSwgZXhwcj10aGlzLnBhcnNlRXhwcmVzc2lvbigpO2lmKHN0YXJ0dHlwZSA9PT0gdHQubmFtZSAmJiBleHByLnR5cGUgPT09IFwiSWRlbnRpZmllclwiICYmIHRoaXMuZWF0KHR0LmNvbG9uKSlyZXR1cm4gdGhpcy5wYXJzZUxhYmVsZWRTdGF0ZW1lbnQobm9kZSwgbWF5YmVOYW1lLCBleHByKTtlbHNlIHJldHVybiB0aGlzLnBhcnNlRXhwcmVzc2lvblN0YXRlbWVudChub2RlLCBleHByKTt9fTtwcC5wYXJzZUJyZWFrQ29udGludWVTdGF0ZW1lbnQgPSBmdW5jdGlvbihub2RlLCBrZXl3b3JkKXt2YXIgaXNCcmVhaz1rZXl3b3JkID09IFwiYnJlYWtcIjt0aGlzLm5leHQoKTtpZih0aGlzLmVhdCh0dC5zZW1pKSB8fCB0aGlzLmluc2VydFNlbWljb2xvbigpKW5vZGUubGFiZWwgPSBudWxsO2Vsc2UgaWYodGhpcy50eXBlICE9PSB0dC5uYW1lKXRoaXMudW5leHBlY3RlZCgpO2Vsc2Uge25vZGUubGFiZWwgPSB0aGlzLnBhcnNlSWRlbnQoKTt0aGlzLnNlbWljb2xvbigpO31mb3IodmFyIGk9MDsgaSA8IHRoaXMubGFiZWxzLmxlbmd0aDsgKytpKSB7dmFyIGxhYj10aGlzLmxhYmVsc1tpXTtpZihub2RlLmxhYmVsID09IG51bGwgfHwgbGFiLm5hbWUgPT09IG5vZGUubGFiZWwubmFtZSl7aWYobGFiLmtpbmQgIT0gbnVsbCAmJiAoaXNCcmVhayB8fCBsYWIua2luZCA9PT0gXCJsb29wXCIpKWJyZWFrO2lmKG5vZGUubGFiZWwgJiYgaXNCcmVhaylicmVhazt9fWlmKGkgPT09IHRoaXMubGFiZWxzLmxlbmd0aCl0aGlzLnJhaXNlKG5vZGUuc3RhcnQsIFwiVW5zeW50YWN0aWMgXCIgKyBrZXl3b3JkKTtyZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIGlzQnJlYWs/XCJCcmVha1N0YXRlbWVudFwiOlwiQ29udGludWVTdGF0ZW1lbnRcIik7fTtwcC5wYXJzZURlYnVnZ2VyU3RhdGVtZW50ID0gZnVuY3Rpb24obm9kZSl7dGhpcy5uZXh0KCk7dGhpcy5zZW1pY29sb24oKTtyZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiRGVidWdnZXJTdGF0ZW1lbnRcIik7fTtwcC5wYXJzZURvU3RhdGVtZW50ID0gZnVuY3Rpb24obm9kZSl7dGhpcy5uZXh0KCk7dGhpcy5sYWJlbHMucHVzaChsb29wTGFiZWwpO25vZGUuYm9keSA9IHRoaXMucGFyc2VTdGF0ZW1lbnQoZmFsc2UpO3RoaXMubGFiZWxzLnBvcCgpO3RoaXMuZXhwZWN0KHR0Ll93aGlsZSk7bm9kZS50ZXN0ID0gdGhpcy5wYXJzZVBhcmVuRXhwcmVzc2lvbigpO2lmKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KXRoaXMuZWF0KHR0LnNlbWkpO2Vsc2UgdGhpcy5zZW1pY29sb24oKTtyZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiRG9XaGlsZVN0YXRlbWVudFwiKTt9O3BwLnBhcnNlRm9yU3RhdGVtZW50ID0gZnVuY3Rpb24obm9kZSl7dGhpcy5uZXh0KCk7dGhpcy5sYWJlbHMucHVzaChsb29wTGFiZWwpO3RoaXMuZXhwZWN0KHR0LnBhcmVuTCk7aWYodGhpcy50eXBlID09PSB0dC5zZW1pKXJldHVybiB0aGlzLnBhcnNlRm9yKG5vZGUsIG51bGwpO2lmKHRoaXMudHlwZSA9PT0gdHQuX3ZhciB8fCB0aGlzLnR5cGUgPT09IHR0Ll9sZXQgfHwgdGhpcy50eXBlID09PSB0dC5fY29uc3Qpe3ZhciBfaW5pdD10aGlzLnN0YXJ0Tm9kZSgpLCB2YXJLaW5kPXRoaXMudHlwZTt0aGlzLm5leHQoKTt0aGlzLnBhcnNlVmFyKF9pbml0LCB0cnVlLCB2YXJLaW5kKTt0aGlzLmZpbmlzaE5vZGUoX2luaXQsIFwiVmFyaWFibGVEZWNsYXJhdGlvblwiKTtpZigodGhpcy50eXBlID09PSB0dC5faW4gfHwgdGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYgJiYgdGhpcy5pc0NvbnRleHR1YWwoXCJvZlwiKSkgJiYgX2luaXQuZGVjbGFyYXRpb25zLmxlbmd0aCA9PT0gMSAmJiAhKHZhcktpbmQgIT09IHR0Ll92YXIgJiYgX2luaXQuZGVjbGFyYXRpb25zWzBdLmluaXQpKXJldHVybiB0aGlzLnBhcnNlRm9ySW4obm9kZSwgX2luaXQpO3JldHVybiB0aGlzLnBhcnNlRm9yKG5vZGUsIF9pbml0KTt9dmFyIHJlZlNob3J0aGFuZERlZmF1bHRQb3M9e3N0YXJ0OjB9O3ZhciBpbml0PXRoaXMucGFyc2VFeHByZXNzaW9uKHRydWUsIHJlZlNob3J0aGFuZERlZmF1bHRQb3MpO2lmKHRoaXMudHlwZSA9PT0gdHQuX2luIHx8IHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2ICYmIHRoaXMuaXNDb250ZXh0dWFsKFwib2ZcIikpe3RoaXMudG9Bc3NpZ25hYmxlKGluaXQpO3RoaXMuY2hlY2tMVmFsKGluaXQpO3JldHVybiB0aGlzLnBhcnNlRm9ySW4obm9kZSwgaW5pdCk7fWVsc2UgaWYocmVmU2hvcnRoYW5kRGVmYXVsdFBvcy5zdGFydCl7dGhpcy51bmV4cGVjdGVkKHJlZlNob3J0aGFuZERlZmF1bHRQb3Muc3RhcnQpO31yZXR1cm4gdGhpcy5wYXJzZUZvcihub2RlLCBpbml0KTt9O3BwLnBhcnNlRnVuY3Rpb25TdGF0ZW1lbnQgPSBmdW5jdGlvbihub2RlKXt0aGlzLm5leHQoKTtyZXR1cm4gdGhpcy5wYXJzZUZ1bmN0aW9uKG5vZGUsIHRydWUpO307cHAucGFyc2VJZlN0YXRlbWVudCA9IGZ1bmN0aW9uKG5vZGUpe3RoaXMubmV4dCgpO25vZGUudGVzdCA9IHRoaXMucGFyc2VQYXJlbkV4cHJlc3Npb24oKTtub2RlLmNvbnNlcXVlbnQgPSB0aGlzLnBhcnNlU3RhdGVtZW50KGZhbHNlKTtub2RlLmFsdGVybmF0ZSA9IHRoaXMuZWF0KHR0Ll9lbHNlKT90aGlzLnBhcnNlU3RhdGVtZW50KGZhbHNlKTpudWxsO3JldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJJZlN0YXRlbWVudFwiKTt9O3BwLnBhcnNlUmV0dXJuU3RhdGVtZW50ID0gZnVuY3Rpb24obm9kZSl7aWYoIXRoaXMuaW5GdW5jdGlvbiAmJiAhdGhpcy5vcHRpb25zLmFsbG93UmV0dXJuT3V0c2lkZUZ1bmN0aW9uKXRoaXMucmFpc2UodGhpcy5zdGFydCwgXCIncmV0dXJuJyBvdXRzaWRlIG9mIGZ1bmN0aW9uXCIpO3RoaXMubmV4dCgpO2lmKHRoaXMuZWF0KHR0LnNlbWkpIHx8IHRoaXMuaW5zZXJ0U2VtaWNvbG9uKCkpbm9kZS5hcmd1bWVudCA9IG51bGw7ZWxzZSB7bm9kZS5hcmd1bWVudCA9IHRoaXMucGFyc2VFeHByZXNzaW9uKCk7dGhpcy5zZW1pY29sb24oKTt9cmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIlJldHVyblN0YXRlbWVudFwiKTt9O3BwLnBhcnNlU3dpdGNoU3RhdGVtZW50ID0gZnVuY3Rpb24obm9kZSl7dGhpcy5uZXh0KCk7bm9kZS5kaXNjcmltaW5hbnQgPSB0aGlzLnBhcnNlUGFyZW5FeHByZXNzaW9uKCk7bm9kZS5jYXNlcyA9IFtdO3RoaXMuZXhwZWN0KHR0LmJyYWNlTCk7dGhpcy5sYWJlbHMucHVzaChzd2l0Y2hMYWJlbCk7Zm9yKHZhciBjdXIsIHNhd0RlZmF1bHQ7IHRoaXMudHlwZSAhPSB0dC5icmFjZVI7KSB7aWYodGhpcy50eXBlID09PSB0dC5fY2FzZSB8fCB0aGlzLnR5cGUgPT09IHR0Ll9kZWZhdWx0KXt2YXIgaXNDYXNlPXRoaXMudHlwZSA9PT0gdHQuX2Nhc2U7aWYoY3VyKXRoaXMuZmluaXNoTm9kZShjdXIsIFwiU3dpdGNoQ2FzZVwiKTtub2RlLmNhc2VzLnB1c2goY3VyID0gdGhpcy5zdGFydE5vZGUoKSk7Y3VyLmNvbnNlcXVlbnQgPSBbXTt0aGlzLm5leHQoKTtpZihpc0Nhc2Upe2N1ci50ZXN0ID0gdGhpcy5wYXJzZUV4cHJlc3Npb24oKTt9ZWxzZSB7aWYoc2F3RGVmYXVsdCl0aGlzLnJhaXNlKHRoaXMubGFzdFRva1N0YXJ0LCBcIk11bHRpcGxlIGRlZmF1bHQgY2xhdXNlc1wiKTtzYXdEZWZhdWx0ID0gdHJ1ZTtjdXIudGVzdCA9IG51bGw7fXRoaXMuZXhwZWN0KHR0LmNvbG9uKTt9ZWxzZSB7aWYoIWN1cil0aGlzLnVuZXhwZWN0ZWQoKTtjdXIuY29uc2VxdWVudC5wdXNoKHRoaXMucGFyc2VTdGF0ZW1lbnQodHJ1ZSkpO319aWYoY3VyKXRoaXMuZmluaXNoTm9kZShjdXIsIFwiU3dpdGNoQ2FzZVwiKTt0aGlzLm5leHQoKTt0aGlzLmxhYmVscy5wb3AoKTtyZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiU3dpdGNoU3RhdGVtZW50XCIpO307cHAucGFyc2VUaHJvd1N0YXRlbWVudCA9IGZ1bmN0aW9uKG5vZGUpe3RoaXMubmV4dCgpO2lmKGxpbmVCcmVhay50ZXN0KHRoaXMuaW5wdXQuc2xpY2UodGhpcy5sYXN0VG9rRW5kLCB0aGlzLnN0YXJ0KSkpdGhpcy5yYWlzZSh0aGlzLmxhc3RUb2tFbmQsIFwiSWxsZWdhbCBuZXdsaW5lIGFmdGVyIHRocm93XCIpO25vZGUuYXJndW1lbnQgPSB0aGlzLnBhcnNlRXhwcmVzc2lvbigpO3RoaXMuc2VtaWNvbG9uKCk7cmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIlRocm93U3RhdGVtZW50XCIpO307dmFyIGVtcHR5PVtdO3BwLnBhcnNlVHJ5U3RhdGVtZW50ID0gZnVuY3Rpb24obm9kZSl7dGhpcy5uZXh0KCk7bm9kZS5ibG9jayA9IHRoaXMucGFyc2VCbG9jaygpO25vZGUuaGFuZGxlciA9IG51bGw7aWYodGhpcy50eXBlID09PSB0dC5fY2F0Y2gpe3ZhciBjbGF1c2U9dGhpcy5zdGFydE5vZGUoKTt0aGlzLm5leHQoKTt0aGlzLmV4cGVjdCh0dC5wYXJlbkwpO2NsYXVzZS5wYXJhbSA9IHRoaXMucGFyc2VCaW5kaW5nQXRvbSgpO3RoaXMuY2hlY2tMVmFsKGNsYXVzZS5wYXJhbSwgdHJ1ZSk7dGhpcy5leHBlY3QodHQucGFyZW5SKTtjbGF1c2UuZ3VhcmQgPSBudWxsO2NsYXVzZS5ib2R5ID0gdGhpcy5wYXJzZUJsb2NrKCk7bm9kZS5oYW5kbGVyID0gdGhpcy5maW5pc2hOb2RlKGNsYXVzZSwgXCJDYXRjaENsYXVzZVwiKTt9bm9kZS5ndWFyZGVkSGFuZGxlcnMgPSBlbXB0eTtub2RlLmZpbmFsaXplciA9IHRoaXMuZWF0KHR0Ll9maW5hbGx5KT90aGlzLnBhcnNlQmxvY2soKTpudWxsO2lmKCFub2RlLmhhbmRsZXIgJiYgIW5vZGUuZmluYWxpemVyKXRoaXMucmFpc2Uobm9kZS5zdGFydCwgXCJNaXNzaW5nIGNhdGNoIG9yIGZpbmFsbHkgY2xhdXNlXCIpO3JldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJUcnlTdGF0ZW1lbnRcIik7fTtwcC5wYXJzZVZhclN0YXRlbWVudCA9IGZ1bmN0aW9uKG5vZGUsIGtpbmQpe3RoaXMubmV4dCgpO3RoaXMucGFyc2VWYXIobm9kZSwgZmFsc2UsIGtpbmQpO3RoaXMuc2VtaWNvbG9uKCk7cmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIlZhcmlhYmxlRGVjbGFyYXRpb25cIik7fTtwcC5wYXJzZVdoaWxlU3RhdGVtZW50ID0gZnVuY3Rpb24obm9kZSl7dGhpcy5uZXh0KCk7bm9kZS50ZXN0ID0gdGhpcy5wYXJzZVBhcmVuRXhwcmVzc2lvbigpO3RoaXMubGFiZWxzLnB1c2gobG9vcExhYmVsKTtub2RlLmJvZHkgPSB0aGlzLnBhcnNlU3RhdGVtZW50KGZhbHNlKTt0aGlzLmxhYmVscy5wb3AoKTtyZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiV2hpbGVTdGF0ZW1lbnRcIik7fTtwcC5wYXJzZVdpdGhTdGF0ZW1lbnQgPSBmdW5jdGlvbihub2RlKXtpZih0aGlzLnN0cmljdCl0aGlzLnJhaXNlKHRoaXMuc3RhcnQsIFwiJ3dpdGgnIGluIHN0cmljdCBtb2RlXCIpO3RoaXMubmV4dCgpO25vZGUub2JqZWN0ID0gdGhpcy5wYXJzZVBhcmVuRXhwcmVzc2lvbigpO25vZGUuYm9keSA9IHRoaXMucGFyc2VTdGF0ZW1lbnQoZmFsc2UpO3JldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJXaXRoU3RhdGVtZW50XCIpO307cHAucGFyc2VFbXB0eVN0YXRlbWVudCA9IGZ1bmN0aW9uKG5vZGUpe3RoaXMubmV4dCgpO3JldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJFbXB0eVN0YXRlbWVudFwiKTt9O3BwLnBhcnNlTGFiZWxlZFN0YXRlbWVudCA9IGZ1bmN0aW9uKG5vZGUsIG1heWJlTmFtZSwgZXhwcil7Zm9yKHZhciBpPTA7IGkgPCB0aGlzLmxhYmVscy5sZW5ndGg7ICsraSkge2lmKHRoaXMubGFiZWxzW2ldLm5hbWUgPT09IG1heWJlTmFtZSl0aGlzLnJhaXNlKGV4cHIuc3RhcnQsIFwiTGFiZWwgJ1wiICsgbWF5YmVOYW1lICsgXCInIGlzIGFscmVhZHkgZGVjbGFyZWRcIik7fXZhciBraW5kPXRoaXMudHlwZS5pc0xvb3A/XCJsb29wXCI6dGhpcy50eXBlID09PSB0dC5fc3dpdGNoP1wic3dpdGNoXCI6bnVsbDt0aGlzLmxhYmVscy5wdXNoKHtuYW1lOm1heWJlTmFtZSwga2luZDpraW5kfSk7bm9kZS5ib2R5ID0gdGhpcy5wYXJzZVN0YXRlbWVudCh0cnVlKTt0aGlzLmxhYmVscy5wb3AoKTtub2RlLmxhYmVsID0gZXhwcjtyZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiTGFiZWxlZFN0YXRlbWVudFwiKTt9O3BwLnBhcnNlRXhwcmVzc2lvblN0YXRlbWVudCA9IGZ1bmN0aW9uKG5vZGUsIGV4cHIpe25vZGUuZXhwcmVzc2lvbiA9IGV4cHI7dGhpcy5zZW1pY29sb24oKTtyZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiRXhwcmVzc2lvblN0YXRlbWVudFwiKTt9O3BwLnBhcnNlQmxvY2sgPSBmdW5jdGlvbihhbGxvd1N0cmljdCl7dmFyIG5vZGU9dGhpcy5zdGFydE5vZGUoKSwgZmlyc3Q9dHJ1ZSwgb2xkU3RyaWN0PXVuZGVmaW5lZDtub2RlLmJvZHkgPSBbXTt0aGlzLmV4cGVjdCh0dC5icmFjZUwpO3doaWxlKCF0aGlzLmVhdCh0dC5icmFjZVIpKSB7dmFyIHN0bXQ9dGhpcy5wYXJzZVN0YXRlbWVudCh0cnVlKTtub2RlLmJvZHkucHVzaChzdG10KTtpZihmaXJzdCAmJiBhbGxvd1N0cmljdCAmJiB0aGlzLmlzVXNlU3RyaWN0KHN0bXQpKXtvbGRTdHJpY3QgPSB0aGlzLnN0cmljdDt0aGlzLnNldFN0cmljdCh0aGlzLnN0cmljdCA9IHRydWUpO31maXJzdCA9IGZhbHNlO31pZihvbGRTdHJpY3QgPT09IGZhbHNlKXRoaXMuc2V0U3RyaWN0KGZhbHNlKTtyZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiQmxvY2tTdGF0ZW1lbnRcIik7fTtwcC5wYXJzZUZvciA9IGZ1bmN0aW9uKG5vZGUsIGluaXQpe25vZGUuaW5pdCA9IGluaXQ7dGhpcy5leHBlY3QodHQuc2VtaSk7bm9kZS50ZXN0ID0gdGhpcy50eXBlID09PSB0dC5zZW1pP251bGw6dGhpcy5wYXJzZUV4cHJlc3Npb24oKTt0aGlzLmV4cGVjdCh0dC5zZW1pKTtub2RlLnVwZGF0ZSA9IHRoaXMudHlwZSA9PT0gdHQucGFyZW5SP251bGw6dGhpcy5wYXJzZUV4cHJlc3Npb24oKTt0aGlzLmV4cGVjdCh0dC5wYXJlblIpO25vZGUuYm9keSA9IHRoaXMucGFyc2VTdGF0ZW1lbnQoZmFsc2UpO3RoaXMubGFiZWxzLnBvcCgpO3JldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJGb3JTdGF0ZW1lbnRcIik7fTtwcC5wYXJzZUZvckluID0gZnVuY3Rpb24obm9kZSwgaW5pdCl7dmFyIHR5cGU9dGhpcy50eXBlID09PSB0dC5faW4/XCJGb3JJblN0YXRlbWVudFwiOlwiRm9yT2ZTdGF0ZW1lbnRcIjt0aGlzLm5leHQoKTtub2RlLmxlZnQgPSBpbml0O25vZGUucmlnaHQgPSB0aGlzLnBhcnNlRXhwcmVzc2lvbigpO3RoaXMuZXhwZWN0KHR0LnBhcmVuUik7bm9kZS5ib2R5ID0gdGhpcy5wYXJzZVN0YXRlbWVudChmYWxzZSk7dGhpcy5sYWJlbHMucG9wKCk7cmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCB0eXBlKTt9O3BwLnBhcnNlVmFyID0gZnVuY3Rpb24obm9kZSwgaXNGb3IsIGtpbmQpe25vZGUuZGVjbGFyYXRpb25zID0gW107bm9kZS5raW5kID0ga2luZC5rZXl3b3JkO2Zvcig7Oykge3ZhciBkZWNsPXRoaXMuc3RhcnROb2RlKCk7dGhpcy5wYXJzZVZhcklkKGRlY2wpO2lmKHRoaXMuZWF0KHR0LmVxKSl7ZGVjbC5pbml0ID0gdGhpcy5wYXJzZU1heWJlQXNzaWduKGlzRm9yKTt9ZWxzZSBpZihraW5kID09PSB0dC5fY29uc3QgJiYgISh0aGlzLnR5cGUgPT09IHR0Ll9pbiB8fCB0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNiAmJiB0aGlzLmlzQ29udGV4dHVhbChcIm9mXCIpKSl7dGhpcy51bmV4cGVjdGVkKCk7fWVsc2UgaWYoZGVjbC5pZC50eXBlICE9IFwiSWRlbnRpZmllclwiICYmICEoaXNGb3IgJiYgKHRoaXMudHlwZSA9PT0gdHQuX2luIHx8IHRoaXMuaXNDb250ZXh0dWFsKFwib2ZcIikpKSl7dGhpcy5yYWlzZSh0aGlzLmxhc3RUb2tFbmQsIFwiQ29tcGxleCBiaW5kaW5nIHBhdHRlcm5zIHJlcXVpcmUgYW4gaW5pdGlhbGl6YXRpb24gdmFsdWVcIik7fWVsc2Uge2RlY2wuaW5pdCA9IG51bGw7fW5vZGUuZGVjbGFyYXRpb25zLnB1c2godGhpcy5maW5pc2hOb2RlKGRlY2wsIFwiVmFyaWFibGVEZWNsYXJhdG9yXCIpKTtpZighdGhpcy5lYXQodHQuY29tbWEpKWJyZWFrO31yZXR1cm4gbm9kZTt9O3BwLnBhcnNlVmFySWQgPSBmdW5jdGlvbihkZWNsKXtkZWNsLmlkID0gdGhpcy5wYXJzZUJpbmRpbmdBdG9tKCk7dGhpcy5jaGVja0xWYWwoZGVjbC5pZCwgdHJ1ZSk7fTtwcC5wYXJzZUZ1bmN0aW9uID0gZnVuY3Rpb24obm9kZSwgaXNTdGF0ZW1lbnQsIGFsbG93RXhwcmVzc2lvbkJvZHkpe3RoaXMuaW5pdEZ1bmN0aW9uKG5vZGUpO2lmKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KW5vZGUuZ2VuZXJhdG9yID0gdGhpcy5lYXQodHQuc3Rhcik7aWYoaXNTdGF0ZW1lbnQgfHwgdGhpcy50eXBlID09PSB0dC5uYW1lKW5vZGUuaWQgPSB0aGlzLnBhcnNlSWRlbnQoKTt0aGlzLnBhcnNlRnVuY3Rpb25QYXJhbXMobm9kZSk7dGhpcy5wYXJzZUZ1bmN0aW9uQm9keShub2RlLCBhbGxvd0V4cHJlc3Npb25Cb2R5KTtyZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIGlzU3RhdGVtZW50P1wiRnVuY3Rpb25EZWNsYXJhdGlvblwiOlwiRnVuY3Rpb25FeHByZXNzaW9uXCIpO307cHAucGFyc2VGdW5jdGlvblBhcmFtcyA9IGZ1bmN0aW9uKG5vZGUpe3RoaXMuZXhwZWN0KHR0LnBhcmVuTCk7bm9kZS5wYXJhbXMgPSB0aGlzLnBhcnNlQmluZGluZ0xpc3QodHQucGFyZW5SLCBmYWxzZSwgZmFsc2UpO307cHAucGFyc2VDbGFzcyA9IGZ1bmN0aW9uKG5vZGUsIGlzU3RhdGVtZW50KXt0aGlzLm5leHQoKTt0aGlzLnBhcnNlQ2xhc3NJZChub2RlLCBpc1N0YXRlbWVudCk7dGhpcy5wYXJzZUNsYXNzU3VwZXIobm9kZSk7dmFyIGNsYXNzQm9keT10aGlzLnN0YXJ0Tm9kZSgpO3ZhciBoYWRDb25zdHJ1Y3Rvcj1mYWxzZTtjbGFzc0JvZHkuYm9keSA9IFtdO3RoaXMuZXhwZWN0KHR0LmJyYWNlTCk7d2hpbGUoIXRoaXMuZWF0KHR0LmJyYWNlUikpIHtpZih0aGlzLmVhdCh0dC5zZW1pKSljb250aW51ZTt2YXIgbWV0aG9kPXRoaXMuc3RhcnROb2RlKCk7dmFyIGlzR2VuZXJhdG9yPXRoaXMuZWF0KHR0LnN0YXIpO3ZhciBpc01heWJlU3RhdGljPXRoaXMudHlwZSA9PT0gdHQubmFtZSAmJiB0aGlzLnZhbHVlID09PSBcInN0YXRpY1wiO3RoaXMucGFyc2VQcm9wZXJ0eU5hbWUobWV0aG9kKTttZXRob2RbXCJzdGF0aWNcIl0gPSBpc01heWJlU3RhdGljICYmIHRoaXMudHlwZSAhPT0gdHQucGFyZW5MO2lmKG1ldGhvZFtcInN0YXRpY1wiXSl7aWYoaXNHZW5lcmF0b3IpdGhpcy51bmV4cGVjdGVkKCk7aXNHZW5lcmF0b3IgPSB0aGlzLmVhdCh0dC5zdGFyKTt0aGlzLnBhcnNlUHJvcGVydHlOYW1lKG1ldGhvZCk7fW1ldGhvZC5raW5kID0gXCJtZXRob2RcIjtpZighbWV0aG9kLmNvbXB1dGVkKXt2YXIga2V5PW1ldGhvZC5rZXk7dmFyIGlzR2V0U2V0PWZhbHNlO2lmKCFpc0dlbmVyYXRvciAmJiBrZXkudHlwZSA9PT0gXCJJZGVudGlmaWVyXCIgJiYgdGhpcy50eXBlICE9PSB0dC5wYXJlbkwgJiYgKGtleS5uYW1lID09PSBcImdldFwiIHx8IGtleS5uYW1lID09PSBcInNldFwiKSl7aXNHZXRTZXQgPSB0cnVlO21ldGhvZC5raW5kID0ga2V5Lm5hbWU7a2V5ID0gdGhpcy5wYXJzZVByb3BlcnR5TmFtZShtZXRob2QpO31pZighbWV0aG9kW1wic3RhdGljXCJdICYmIChrZXkudHlwZSA9PT0gXCJJZGVudGlmaWVyXCIgJiYga2V5Lm5hbWUgPT09IFwiY29uc3RydWN0b3JcIiB8fCBrZXkudHlwZSA9PT0gXCJMaXRlcmFsXCIgJiYga2V5LnZhbHVlID09PSBcImNvbnN0cnVjdG9yXCIpKXtpZihoYWRDb25zdHJ1Y3Rvcil0aGlzLnJhaXNlKGtleS5zdGFydCwgXCJEdXBsaWNhdGUgY29uc3RydWN0b3IgaW4gdGhlIHNhbWUgY2xhc3NcIik7aWYoaXNHZXRTZXQpdGhpcy5yYWlzZShrZXkuc3RhcnQsIFwiQ29uc3RydWN0b3IgY2FuJ3QgaGF2ZSBnZXQvc2V0IG1vZGlmaWVyXCIpO2lmKGlzR2VuZXJhdG9yKXRoaXMucmFpc2Uoa2V5LnN0YXJ0LCBcIkNvbnN0cnVjdG9yIGNhbid0IGJlIGEgZ2VuZXJhdG9yXCIpO21ldGhvZC5raW5kID0gXCJjb25zdHJ1Y3RvclwiO2hhZENvbnN0cnVjdG9yID0gdHJ1ZTt9fXRoaXMucGFyc2VDbGFzc01ldGhvZChjbGFzc0JvZHksIG1ldGhvZCwgaXNHZW5lcmF0b3IpO31ub2RlLmJvZHkgPSB0aGlzLmZpbmlzaE5vZGUoY2xhc3NCb2R5LCBcIkNsYXNzQm9keVwiKTtyZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIGlzU3RhdGVtZW50P1wiQ2xhc3NEZWNsYXJhdGlvblwiOlwiQ2xhc3NFeHByZXNzaW9uXCIpO307cHAucGFyc2VDbGFzc01ldGhvZCA9IGZ1bmN0aW9uKGNsYXNzQm9keSwgbWV0aG9kLCBpc0dlbmVyYXRvcil7bWV0aG9kLnZhbHVlID0gdGhpcy5wYXJzZU1ldGhvZChpc0dlbmVyYXRvcik7Y2xhc3NCb2R5LmJvZHkucHVzaCh0aGlzLmZpbmlzaE5vZGUobWV0aG9kLCBcIk1ldGhvZERlZmluaXRpb25cIikpO307cHAucGFyc2VDbGFzc0lkID0gZnVuY3Rpb24obm9kZSwgaXNTdGF0ZW1lbnQpe25vZGUuaWQgPSB0aGlzLnR5cGUgPT09IHR0Lm5hbWU/dGhpcy5wYXJzZUlkZW50KCk6aXNTdGF0ZW1lbnQ/dGhpcy51bmV4cGVjdGVkKCk6bnVsbDt9O3BwLnBhcnNlQ2xhc3NTdXBlciA9IGZ1bmN0aW9uKG5vZGUpe25vZGUuc3VwZXJDbGFzcyA9IHRoaXMuZWF0KHR0Ll9leHRlbmRzKT90aGlzLnBhcnNlRXhwclN1YnNjcmlwdHMoKTpudWxsO307cHAucGFyc2VFeHBvcnQgPSBmdW5jdGlvbihub2RlKXt0aGlzLm5leHQoKTtpZih0aGlzLmVhdCh0dC5zdGFyKSl7dGhpcy5leHBlY3RDb250ZXh0dWFsKFwiZnJvbVwiKTtub2RlLnNvdXJjZSA9IHRoaXMudHlwZSA9PT0gdHQuc3RyaW5nP3RoaXMucGFyc2VFeHByQXRvbSgpOnRoaXMudW5leHBlY3RlZCgpO3RoaXMuc2VtaWNvbG9uKCk7cmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkV4cG9ydEFsbERlY2xhcmF0aW9uXCIpO31pZih0aGlzLmVhdCh0dC5fZGVmYXVsdCkpe3ZhciBleHByPXRoaXMucGFyc2VNYXliZUFzc2lnbigpO3ZhciBuZWVkc1NlbWk9dHJ1ZTtpZihleHByLnR5cGUgPT0gXCJGdW5jdGlvbkV4cHJlc3Npb25cIiB8fCBleHByLnR5cGUgPT0gXCJDbGFzc0V4cHJlc3Npb25cIil7bmVlZHNTZW1pID0gZmFsc2U7aWYoZXhwci5pZCl7ZXhwci50eXBlID0gZXhwci50eXBlID09IFwiRnVuY3Rpb25FeHByZXNzaW9uXCI/XCJGdW5jdGlvbkRlY2xhcmF0aW9uXCI6XCJDbGFzc0RlY2xhcmF0aW9uXCI7fX1ub2RlLmRlY2xhcmF0aW9uID0gZXhwcjtpZihuZWVkc1NlbWkpdGhpcy5zZW1pY29sb24oKTtyZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiRXhwb3J0RGVmYXVsdERlY2xhcmF0aW9uXCIpO31pZih0aGlzLnNob3VsZFBhcnNlRXhwb3J0U3RhdGVtZW50KCkpe25vZGUuZGVjbGFyYXRpb24gPSB0aGlzLnBhcnNlU3RhdGVtZW50KHRydWUpO25vZGUuc3BlY2lmaWVycyA9IFtdO25vZGUuc291cmNlID0gbnVsbDt9ZWxzZSB7bm9kZS5kZWNsYXJhdGlvbiA9IG51bGw7bm9kZS5zcGVjaWZpZXJzID0gdGhpcy5wYXJzZUV4cG9ydFNwZWNpZmllcnMoKTtpZih0aGlzLmVhdENvbnRleHR1YWwoXCJmcm9tXCIpKXtub2RlLnNvdXJjZSA9IHRoaXMudHlwZSA9PT0gdHQuc3RyaW5nP3RoaXMucGFyc2VFeHByQXRvbSgpOnRoaXMudW5leHBlY3RlZCgpO31lbHNlIHtub2RlLnNvdXJjZSA9IG51bGw7fXRoaXMuc2VtaWNvbG9uKCk7fXJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJFeHBvcnROYW1lZERlY2xhcmF0aW9uXCIpO307cHAuc2hvdWxkUGFyc2VFeHBvcnRTdGF0ZW1lbnQgPSBmdW5jdGlvbigpe3JldHVybiB0aGlzLnR5cGUua2V5d29yZDt9O3BwLnBhcnNlRXhwb3J0U3BlY2lmaWVycyA9IGZ1bmN0aW9uKCl7dmFyIG5vZGVzPVtdLCBmaXJzdD10cnVlO3RoaXMuZXhwZWN0KHR0LmJyYWNlTCk7d2hpbGUoIXRoaXMuZWF0KHR0LmJyYWNlUikpIHtpZighZmlyc3Qpe3RoaXMuZXhwZWN0KHR0LmNvbW1hKTtpZih0aGlzLmFmdGVyVHJhaWxpbmdDb21tYSh0dC5icmFjZVIpKWJyZWFrO31lbHNlIGZpcnN0ID0gZmFsc2U7dmFyIG5vZGU9dGhpcy5zdGFydE5vZGUoKTtub2RlLmxvY2FsID0gdGhpcy5wYXJzZUlkZW50KHRoaXMudHlwZSA9PT0gdHQuX2RlZmF1bHQpO25vZGUuZXhwb3J0ZWQgPSB0aGlzLmVhdENvbnRleHR1YWwoXCJhc1wiKT90aGlzLnBhcnNlSWRlbnQodHJ1ZSk6bm9kZS5sb2NhbDtub2Rlcy5wdXNoKHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkV4cG9ydFNwZWNpZmllclwiKSk7fXJldHVybiBub2Rlczt9O3BwLnBhcnNlSW1wb3J0ID0gZnVuY3Rpb24obm9kZSl7dGhpcy5uZXh0KCk7aWYodGhpcy50eXBlID09PSB0dC5zdHJpbmcpe25vZGUuc3BlY2lmaWVycyA9IGVtcHR5O25vZGUuc291cmNlID0gdGhpcy5wYXJzZUV4cHJBdG9tKCk7bm9kZS5raW5kID0gXCJcIjt9ZWxzZSB7bm9kZS5zcGVjaWZpZXJzID0gdGhpcy5wYXJzZUltcG9ydFNwZWNpZmllcnMoKTt0aGlzLmV4cGVjdENvbnRleHR1YWwoXCJmcm9tXCIpO25vZGUuc291cmNlID0gdGhpcy50eXBlID09PSB0dC5zdHJpbmc/dGhpcy5wYXJzZUV4cHJBdG9tKCk6dGhpcy51bmV4cGVjdGVkKCk7fXRoaXMuc2VtaWNvbG9uKCk7cmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkltcG9ydERlY2xhcmF0aW9uXCIpO307cHAucGFyc2VJbXBvcnRTcGVjaWZpZXJzID0gZnVuY3Rpb24oKXt2YXIgbm9kZXM9W10sIGZpcnN0PXRydWU7aWYodGhpcy50eXBlID09PSB0dC5uYW1lKXt2YXIgbm9kZT10aGlzLnN0YXJ0Tm9kZSgpO25vZGUubG9jYWwgPSB0aGlzLnBhcnNlSWRlbnQoKTt0aGlzLmNoZWNrTFZhbChub2RlLmxvY2FsLCB0cnVlKTtub2Rlcy5wdXNoKHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkltcG9ydERlZmF1bHRTcGVjaWZpZXJcIikpO2lmKCF0aGlzLmVhdCh0dC5jb21tYSkpcmV0dXJuIG5vZGVzO31pZih0aGlzLnR5cGUgPT09IHR0LnN0YXIpe3ZhciBub2RlPXRoaXMuc3RhcnROb2RlKCk7dGhpcy5uZXh0KCk7dGhpcy5leHBlY3RDb250ZXh0dWFsKFwiYXNcIik7bm9kZS5sb2NhbCA9IHRoaXMucGFyc2VJZGVudCgpO3RoaXMuY2hlY2tMVmFsKG5vZGUubG9jYWwsIHRydWUpO25vZGVzLnB1c2godGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiSW1wb3J0TmFtZXNwYWNlU3BlY2lmaWVyXCIpKTtyZXR1cm4gbm9kZXM7fXRoaXMuZXhwZWN0KHR0LmJyYWNlTCk7d2hpbGUoIXRoaXMuZWF0KHR0LmJyYWNlUikpIHtpZighZmlyc3Qpe3RoaXMuZXhwZWN0KHR0LmNvbW1hKTtpZih0aGlzLmFmdGVyVHJhaWxpbmdDb21tYSh0dC5icmFjZVIpKWJyZWFrO31lbHNlIGZpcnN0ID0gZmFsc2U7dmFyIG5vZGU9dGhpcy5zdGFydE5vZGUoKTtub2RlLmltcG9ydGVkID0gdGhpcy5wYXJzZUlkZW50KHRydWUpO25vZGUubG9jYWwgPSB0aGlzLmVhdENvbnRleHR1YWwoXCJhc1wiKT90aGlzLnBhcnNlSWRlbnQoKTpub2RlLmltcG9ydGVkO3RoaXMuY2hlY2tMVmFsKG5vZGUubG9jYWwsIHRydWUpO25vZGVzLnB1c2godGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiSW1wb3J0U3BlY2lmaWVyXCIpKTt9cmV0dXJuIG5vZGVzO307fSwge1wiLi9zdGF0ZVwiOjEzLCBcIi4vdG9rZW50eXBlXCI6MTcsIFwiLi93aGl0ZXNwYWNlXCI6MTl9XSwgMTU6W2Z1bmN0aW9uKF9kZXJlcV8sIG1vZHVsZSwgZXhwb3J0cyl7XCJ1c2Ugc3RyaWN0XCI7dmFyIF9jbGFzc0NhbGxDaGVjaz1mdW5jdGlvbiBfY2xhc3NDYWxsQ2hlY2soaW5zdGFuY2UsIENvbnN0cnVjdG9yKXtpZighKGluc3RhbmNlIGluc3RhbmNlb2YgQ29uc3RydWN0b3IpKXt0aHJvdyBuZXcgVHlwZUVycm9yKFwiQ2Fubm90IGNhbGwgYSBjbGFzcyBhcyBhIGZ1bmN0aW9uXCIpO319O2V4cG9ydHMuX19lc01vZHVsZSA9IHRydWU7dmFyIFBhcnNlcj1fZGVyZXFfKFwiLi9zdGF0ZVwiKS5QYXJzZXI7dmFyIHR0PV9kZXJlcV8oXCIuL3Rva2VudHlwZVwiKS50eXBlczt2YXIgbGluZUJyZWFrPV9kZXJlcV8oXCIuL3doaXRlc3BhY2VcIikubGluZUJyZWFrO3ZhciBUb2tDb250ZXh0PWV4cG9ydHMuVG9rQ29udGV4dCA9IGZ1bmN0aW9uIFRva0NvbnRleHQodG9rZW4sIGlzRXhwciwgcHJlc2VydmVTcGFjZSwgb3ZlcnJpZGUpe19jbGFzc0NhbGxDaGVjayh0aGlzLCBUb2tDb250ZXh0KTt0aGlzLnRva2VuID0gdG9rZW47dGhpcy5pc0V4cHIgPSBpc0V4cHI7dGhpcy5wcmVzZXJ2ZVNwYWNlID0gcHJlc2VydmVTcGFjZTt0aGlzLm92ZXJyaWRlID0gb3ZlcnJpZGU7fTt2YXIgdHlwZXM9e2Jfc3RhdDpuZXcgVG9rQ29udGV4dChcIntcIiwgZmFsc2UpLCBiX2V4cHI6bmV3IFRva0NvbnRleHQoXCJ7XCIsIHRydWUpLCBiX3RtcGw6bmV3IFRva0NvbnRleHQoXCIke1wiLCB0cnVlKSwgcF9zdGF0Om5ldyBUb2tDb250ZXh0KFwiKFwiLCBmYWxzZSksIHBfZXhwcjpuZXcgVG9rQ29udGV4dChcIihcIiwgdHJ1ZSksIHFfdG1wbDpuZXcgVG9rQ29udGV4dChcImBcIiwgdHJ1ZSwgdHJ1ZSwgZnVuY3Rpb24ocCl7cmV0dXJuIHAucmVhZFRtcGxUb2tlbigpO30pLCBmX2V4cHI6bmV3IFRva0NvbnRleHQoXCJmdW5jdGlvblwiLCB0cnVlKX07ZXhwb3J0cy50eXBlcyA9IHR5cGVzO3ZhciBwcD1QYXJzZXIucHJvdG90eXBlO3BwLmluaXRpYWxDb250ZXh0ID0gZnVuY3Rpb24oKXtyZXR1cm4gW3R5cGVzLmJfc3RhdF07fTtwcC5icmFjZUlzQmxvY2sgPSBmdW5jdGlvbihwcmV2VHlwZSl7dmFyIHBhcmVudD11bmRlZmluZWQ7aWYocHJldlR5cGUgPT09IHR0LmNvbG9uICYmIChwYXJlbnQgPSB0aGlzLmN1ckNvbnRleHQoKSkudG9rZW4gPT0gXCJ7XCIpcmV0dXJuICFwYXJlbnQuaXNFeHByO2lmKHByZXZUeXBlID09PSB0dC5fcmV0dXJuKXJldHVybiBsaW5lQnJlYWsudGVzdCh0aGlzLmlucHV0LnNsaWNlKHRoaXMubGFzdFRva0VuZCwgdGhpcy5zdGFydCkpO2lmKHByZXZUeXBlID09PSB0dC5fZWxzZSB8fCBwcmV2VHlwZSA9PT0gdHQuc2VtaSB8fCBwcmV2VHlwZSA9PT0gdHQuZW9mKXJldHVybiB0cnVlO2lmKHByZXZUeXBlID09IHR0LmJyYWNlTClyZXR1cm4gdGhpcy5jdXJDb250ZXh0KCkgPT09IHR5cGVzLmJfc3RhdDtyZXR1cm4gIXRoaXMuZXhwckFsbG93ZWQ7fTtwcC51cGRhdGVDb250ZXh0ID0gZnVuY3Rpb24ocHJldlR5cGUpe3ZhciB1cGRhdGU9dW5kZWZpbmVkLCB0eXBlPXRoaXMudHlwZTtpZih0eXBlLmtleXdvcmQgJiYgcHJldlR5cGUgPT0gdHQuZG90KXRoaXMuZXhwckFsbG93ZWQgPSBmYWxzZTtlbHNlIGlmKHVwZGF0ZSA9IHR5cGUudXBkYXRlQ29udGV4dCl1cGRhdGUuY2FsbCh0aGlzLCBwcmV2VHlwZSk7ZWxzZSB0aGlzLmV4cHJBbGxvd2VkID0gdHlwZS5iZWZvcmVFeHByO307dHQucGFyZW5SLnVwZGF0ZUNvbnRleHQgPSB0dC5icmFjZVIudXBkYXRlQ29udGV4dCA9IGZ1bmN0aW9uKCl7aWYodGhpcy5jb250ZXh0Lmxlbmd0aCA9PSAxKXt0aGlzLmV4cHJBbGxvd2VkID0gdHJ1ZTtyZXR1cm47fXZhciBvdXQ9dGhpcy5jb250ZXh0LnBvcCgpO2lmKG91dCA9PT0gdHlwZXMuYl9zdGF0ICYmIHRoaXMuY3VyQ29udGV4dCgpID09PSB0eXBlcy5mX2V4cHIpe3RoaXMuY29udGV4dC5wb3AoKTt0aGlzLmV4cHJBbGxvd2VkID0gZmFsc2U7fWVsc2UgaWYob3V0ID09PSB0eXBlcy5iX3RtcGwpe3RoaXMuZXhwckFsbG93ZWQgPSB0cnVlO31lbHNlIHt0aGlzLmV4cHJBbGxvd2VkID0gIW91dC5pc0V4cHI7fX07dHQuYnJhY2VMLnVwZGF0ZUNvbnRleHQgPSBmdW5jdGlvbihwcmV2VHlwZSl7dGhpcy5jb250ZXh0LnB1c2godGhpcy5icmFjZUlzQmxvY2socHJldlR5cGUpP3R5cGVzLmJfc3RhdDp0eXBlcy5iX2V4cHIpO3RoaXMuZXhwckFsbG93ZWQgPSB0cnVlO307dHQuZG9sbGFyQnJhY2VMLnVwZGF0ZUNvbnRleHQgPSBmdW5jdGlvbigpe3RoaXMuY29udGV4dC5wdXNoKHR5cGVzLmJfdG1wbCk7dGhpcy5leHByQWxsb3dlZCA9IHRydWU7fTt0dC5wYXJlbkwudXBkYXRlQ29udGV4dCA9IGZ1bmN0aW9uKHByZXZUeXBlKXt2YXIgc3RhdGVtZW50UGFyZW5zPXByZXZUeXBlID09PSB0dC5faWYgfHwgcHJldlR5cGUgPT09IHR0Ll9mb3IgfHwgcHJldlR5cGUgPT09IHR0Ll93aXRoIHx8IHByZXZUeXBlID09PSB0dC5fd2hpbGU7dGhpcy5jb250ZXh0LnB1c2goc3RhdGVtZW50UGFyZW5zP3R5cGVzLnBfc3RhdDp0eXBlcy5wX2V4cHIpO3RoaXMuZXhwckFsbG93ZWQgPSB0cnVlO307dHQuaW5jRGVjLnVwZGF0ZUNvbnRleHQgPSBmdW5jdGlvbigpe307dHQuX2Z1bmN0aW9uLnVwZGF0ZUNvbnRleHQgPSBmdW5jdGlvbigpe2lmKHRoaXMuY3VyQ29udGV4dCgpICE9PSB0eXBlcy5iX3N0YXQpdGhpcy5jb250ZXh0LnB1c2godHlwZXMuZl9leHByKTt0aGlzLmV4cHJBbGxvd2VkID0gZmFsc2U7fTt0dC5iYWNrUXVvdGUudXBkYXRlQ29udGV4dCA9IGZ1bmN0aW9uKCl7aWYodGhpcy5jdXJDb250ZXh0KCkgPT09IHR5cGVzLnFfdG1wbCl0aGlzLmNvbnRleHQucG9wKCk7ZWxzZSB0aGlzLmNvbnRleHQucHVzaCh0eXBlcy5xX3RtcGwpO3RoaXMuZXhwckFsbG93ZWQgPSBmYWxzZTt9O30sIHtcIi4vc3RhdGVcIjoxMywgXCIuL3Rva2VudHlwZVwiOjE3LCBcIi4vd2hpdGVzcGFjZVwiOjE5fV0sIDE2OltmdW5jdGlvbihfZGVyZXFfLCBtb2R1bGUsIGV4cG9ydHMpe1widXNlIHN0cmljdFwiO3ZhciBfY2xhc3NDYWxsQ2hlY2s9ZnVuY3Rpb24gX2NsYXNzQ2FsbENoZWNrKGluc3RhbmNlLCBDb25zdHJ1Y3Rvcil7aWYoIShpbnN0YW5jZSBpbnN0YW5jZW9mIENvbnN0cnVjdG9yKSl7dGhyb3cgbmV3IFR5cGVFcnJvcihcIkNhbm5vdCBjYWxsIGEgY2xhc3MgYXMgYSBmdW5jdGlvblwiKTt9fTtleHBvcnRzLl9fZXNNb2R1bGUgPSB0cnVlO3ZhciBfaWRlbnRpZmllcj1fZGVyZXFfKFwiLi9pZGVudGlmaWVyXCIpO3ZhciBpc0lkZW50aWZpZXJTdGFydD1faWRlbnRpZmllci5pc0lkZW50aWZpZXJTdGFydDt2YXIgaXNJZGVudGlmaWVyQ2hhcj1faWRlbnRpZmllci5pc0lkZW50aWZpZXJDaGFyO3ZhciBfdG9rZW50eXBlPV9kZXJlcV8oXCIuL3Rva2VudHlwZVwiKTt2YXIgdHQ9X3Rva2VudHlwZS50eXBlczt2YXIga2V5d29yZFR5cGVzPV90b2tlbnR5cGUua2V5d29yZHM7dmFyIFBhcnNlcj1fZGVyZXFfKFwiLi9zdGF0ZVwiKS5QYXJzZXI7dmFyIFNvdXJjZUxvY2F0aW9uPV9kZXJlcV8oXCIuL2xvY2F0aW9uXCIpLlNvdXJjZUxvY2F0aW9uO3ZhciBfd2hpdGVzcGFjZT1fZGVyZXFfKFwiLi93aGl0ZXNwYWNlXCIpO3ZhciBsaW5lQnJlYWs9X3doaXRlc3BhY2UubGluZUJyZWFrO3ZhciBsaW5lQnJlYWtHPV93aGl0ZXNwYWNlLmxpbmVCcmVha0c7dmFyIGlzTmV3TGluZT1fd2hpdGVzcGFjZS5pc05ld0xpbmU7dmFyIG5vbkFTQ0lJd2hpdGVzcGFjZT1fd2hpdGVzcGFjZS5ub25BU0NJSXdoaXRlc3BhY2U7dmFyIFRva2VuPWV4cG9ydHMuVG9rZW4gPSBmdW5jdGlvbiBUb2tlbihwKXtfY2xhc3NDYWxsQ2hlY2sodGhpcywgVG9rZW4pO3RoaXMudHlwZSA9IHAudHlwZTt0aGlzLnZhbHVlID0gcC52YWx1ZTt0aGlzLnN0YXJ0ID0gcC5zdGFydDt0aGlzLmVuZCA9IHAuZW5kO2lmKHAub3B0aW9ucy5sb2NhdGlvbnMpdGhpcy5sb2MgPSBuZXcgU291cmNlTG9jYXRpb24ocCwgcC5zdGFydExvYywgcC5lbmRMb2MpO2lmKHAub3B0aW9ucy5yYW5nZXMpdGhpcy5yYW5nZSA9IFtwLnN0YXJ0LCBwLmVuZF07fTt2YXIgcHA9UGFyc2VyLnByb3RvdHlwZTt2YXIgaXNSaGlubz10eXBlb2YgUGFja2FnZXMgIT09IFwidW5kZWZpbmVkXCI7cHAubmV4dCA9IGZ1bmN0aW9uKCl7aWYodGhpcy5vcHRpb25zLm9uVG9rZW4pdGhpcy5vcHRpb25zLm9uVG9rZW4obmV3IFRva2VuKHRoaXMpKTt0aGlzLmxhc3RUb2tFbmQgPSB0aGlzLmVuZDt0aGlzLmxhc3RUb2tTdGFydCA9IHRoaXMuc3RhcnQ7dGhpcy5sYXN0VG9rRW5kTG9jID0gdGhpcy5lbmRMb2M7dGhpcy5sYXN0VG9rU3RhcnRMb2MgPSB0aGlzLnN0YXJ0TG9jO3RoaXMubmV4dFRva2VuKCk7fTtwcC5nZXRUb2tlbiA9IGZ1bmN0aW9uKCl7dGhpcy5uZXh0KCk7cmV0dXJuIG5ldyBUb2tlbih0aGlzKTt9O2lmKHR5cGVvZiBTeW1ib2wgIT09IFwidW5kZWZpbmVkXCIpcHBbU3ltYm9sLml0ZXJhdG9yXSA9IGZ1bmN0aW9uKCl7dmFyIHNlbGY9dGhpcztyZXR1cm4ge25leHQ6ZnVuY3Rpb24gbmV4dCgpe3ZhciB0b2tlbj1zZWxmLmdldFRva2VuKCk7cmV0dXJuIHtkb25lOnRva2VuLnR5cGUgPT09IHR0LmVvZiwgdmFsdWU6dG9rZW59O319O307cHAuc2V0U3RyaWN0ID0gZnVuY3Rpb24oc3RyaWN0KXt0aGlzLnN0cmljdCA9IHN0cmljdDtpZih0aGlzLnR5cGUgIT09IHR0Lm51bSAmJiB0aGlzLnR5cGUgIT09IHR0LnN0cmluZylyZXR1cm47dGhpcy5wb3MgPSB0aGlzLnN0YXJ0O2lmKHRoaXMub3B0aW9ucy5sb2NhdGlvbnMpe3doaWxlKHRoaXMucG9zIDwgdGhpcy5saW5lU3RhcnQpIHt0aGlzLmxpbmVTdGFydCA9IHRoaXMuaW5wdXQubGFzdEluZGV4T2YoXCJcXG5cIiwgdGhpcy5saW5lU3RhcnQgLSAyKSArIDE7LS10aGlzLmN1ckxpbmU7fX10aGlzLm5leHRUb2tlbigpO307cHAuY3VyQ29udGV4dCA9IGZ1bmN0aW9uKCl7cmV0dXJuIHRoaXMuY29udGV4dFt0aGlzLmNvbnRleHQubGVuZ3RoIC0gMV07fTtwcC5uZXh0VG9rZW4gPSBmdW5jdGlvbigpe3ZhciBjdXJDb250ZXh0PXRoaXMuY3VyQ29udGV4dCgpO2lmKCFjdXJDb250ZXh0IHx8ICFjdXJDb250ZXh0LnByZXNlcnZlU3BhY2UpdGhpcy5za2lwU3BhY2UoKTt0aGlzLnN0YXJ0ID0gdGhpcy5wb3M7aWYodGhpcy5vcHRpb25zLmxvY2F0aW9ucyl0aGlzLnN0YXJ0TG9jID0gdGhpcy5jdXJQb3NpdGlvbigpO2lmKHRoaXMucG9zID49IHRoaXMuaW5wdXQubGVuZ3RoKXJldHVybiB0aGlzLmZpbmlzaFRva2VuKHR0LmVvZik7aWYoY3VyQ29udGV4dC5vdmVycmlkZSlyZXR1cm4gY3VyQ29udGV4dC5vdmVycmlkZSh0aGlzKTtlbHNlIHRoaXMucmVhZFRva2VuKHRoaXMuZnVsbENoYXJDb2RlQXRQb3MoKSk7fTtwcC5yZWFkVG9rZW4gPSBmdW5jdGlvbihjb2RlKXtpZihpc0lkZW50aWZpZXJTdGFydChjb2RlLCB0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNikgfHwgY29kZSA9PT0gOTIpcmV0dXJuIHRoaXMucmVhZFdvcmQoKTtyZXR1cm4gdGhpcy5nZXRUb2tlbkZyb21Db2RlKGNvZGUpO307cHAuZnVsbENoYXJDb2RlQXRQb3MgPSBmdW5jdGlvbigpe3ZhciBjb2RlPXRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyk7aWYoY29kZSA8PSA1NTI5NSB8fCBjb2RlID49IDU3MzQ0KXJldHVybiBjb2RlO3ZhciBuZXh0PXRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIDEpO3JldHVybiAoY29kZSA8PCAxMCkgKyBuZXh0IC0gNTY2MTM4ODg7fTtwcC5za2lwQmxvY2tDb21tZW50ID0gZnVuY3Rpb24oKXt2YXIgc3RhcnRMb2M9dGhpcy5vcHRpb25zLm9uQ29tbWVudCAmJiB0aGlzLm9wdGlvbnMubG9jYXRpb25zICYmIHRoaXMuY3VyUG9zaXRpb24oKTt2YXIgc3RhcnQ9dGhpcy5wb3MsIGVuZD10aGlzLmlucHV0LmluZGV4T2YoXCIqL1wiLCB0aGlzLnBvcyArPSAyKTtpZihlbmQgPT09IC0xKXRoaXMucmFpc2UodGhpcy5wb3MgLSAyLCBcIlVudGVybWluYXRlZCBjb21tZW50XCIpO3RoaXMucG9zID0gZW5kICsgMjtpZih0aGlzLm9wdGlvbnMubG9jYXRpb25zKXtsaW5lQnJlYWtHLmxhc3RJbmRleCA9IHN0YXJ0O3ZhciBtYXRjaD11bmRlZmluZWQ7d2hpbGUoKG1hdGNoID0gbGluZUJyZWFrRy5leGVjKHRoaXMuaW5wdXQpKSAmJiBtYXRjaC5pbmRleCA8IHRoaXMucG9zKSB7Kyt0aGlzLmN1ckxpbmU7dGhpcy5saW5lU3RhcnQgPSBtYXRjaC5pbmRleCArIG1hdGNoWzBdLmxlbmd0aDt9fWlmKHRoaXMub3B0aW9ucy5vbkNvbW1lbnQpdGhpcy5vcHRpb25zLm9uQ29tbWVudCh0cnVlLCB0aGlzLmlucHV0LnNsaWNlKHN0YXJ0ICsgMiwgZW5kKSwgc3RhcnQsIHRoaXMucG9zLCBzdGFydExvYywgdGhpcy5vcHRpb25zLmxvY2F0aW9ucyAmJiB0aGlzLmN1clBvc2l0aW9uKCkpO307cHAuc2tpcExpbmVDb21tZW50ID0gZnVuY3Rpb24oc3RhcnRTa2lwKXt2YXIgc3RhcnQ9dGhpcy5wb3M7dmFyIHN0YXJ0TG9jPXRoaXMub3B0aW9ucy5vbkNvbW1lbnQgJiYgdGhpcy5vcHRpb25zLmxvY2F0aW9ucyAmJiB0aGlzLmN1clBvc2l0aW9uKCk7dmFyIGNoPXRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArPSBzdGFydFNraXApO3doaWxlKHRoaXMucG9zIDwgdGhpcy5pbnB1dC5sZW5ndGggJiYgY2ggIT09IDEwICYmIGNoICE9PSAxMyAmJiBjaCAhPT0gODIzMiAmJiBjaCAhPT0gODIzMykgeysrdGhpcy5wb3M7Y2ggPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MpO31pZih0aGlzLm9wdGlvbnMub25Db21tZW50KXRoaXMub3B0aW9ucy5vbkNvbW1lbnQoZmFsc2UsIHRoaXMuaW5wdXQuc2xpY2Uoc3RhcnQgKyBzdGFydFNraXAsIHRoaXMucG9zKSwgc3RhcnQsIHRoaXMucG9zLCBzdGFydExvYywgdGhpcy5vcHRpb25zLmxvY2F0aW9ucyAmJiB0aGlzLmN1clBvc2l0aW9uKCkpO307cHAuc2tpcFNwYWNlID0gZnVuY3Rpb24oKXt3aGlsZSh0aGlzLnBvcyA8IHRoaXMuaW5wdXQubGVuZ3RoKSB7dmFyIGNoPXRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyk7aWYoY2ggPT09IDMyKXsrK3RoaXMucG9zO31lbHNlIGlmKGNoID09PSAxMyl7Kyt0aGlzLnBvczt2YXIgbmV4dD10aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MpO2lmKG5leHQgPT09IDEwKXsrK3RoaXMucG9zO31pZih0aGlzLm9wdGlvbnMubG9jYXRpb25zKXsrK3RoaXMuY3VyTGluZTt0aGlzLmxpbmVTdGFydCA9IHRoaXMucG9zO319ZWxzZSBpZihjaCA9PT0gMTAgfHwgY2ggPT09IDgyMzIgfHwgY2ggPT09IDgyMzMpeysrdGhpcy5wb3M7aWYodGhpcy5vcHRpb25zLmxvY2F0aW9ucyl7Kyt0aGlzLmN1ckxpbmU7dGhpcy5saW5lU3RhcnQgPSB0aGlzLnBvczt9fWVsc2UgaWYoY2ggPiA4ICYmIGNoIDwgMTQpeysrdGhpcy5wb3M7fWVsc2UgaWYoY2ggPT09IDQ3KXt2YXIgbmV4dD10aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAxKTtpZihuZXh0ID09PSA0Mil7dGhpcy5za2lwQmxvY2tDb21tZW50KCk7fWVsc2UgaWYobmV4dCA9PT0gNDcpe3RoaXMuc2tpcExpbmVDb21tZW50KDIpO31lbHNlIGJyZWFrO31lbHNlIGlmKGNoID09PSAxNjApeysrdGhpcy5wb3M7fWVsc2UgaWYoY2ggPj0gNTc2MCAmJiBub25BU0NJSXdoaXRlc3BhY2UudGVzdChTdHJpbmcuZnJvbUNoYXJDb2RlKGNoKSkpeysrdGhpcy5wb3M7fWVsc2Uge2JyZWFrO319fTtwcC5maW5pc2hUb2tlbiA9IGZ1bmN0aW9uKHR5cGUsIHZhbCl7dGhpcy5lbmQgPSB0aGlzLnBvcztpZih0aGlzLm9wdGlvbnMubG9jYXRpb25zKXRoaXMuZW5kTG9jID0gdGhpcy5jdXJQb3NpdGlvbigpO3ZhciBwcmV2VHlwZT10aGlzLnR5cGU7dGhpcy50eXBlID0gdHlwZTt0aGlzLnZhbHVlID0gdmFsO3RoaXMudXBkYXRlQ29udGV4dChwcmV2VHlwZSk7fTtwcC5yZWFkVG9rZW5fZG90ID0gZnVuY3Rpb24oKXt2YXIgbmV4dD10aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAxKTtpZihuZXh0ID49IDQ4ICYmIG5leHQgPD0gNTcpcmV0dXJuIHRoaXMucmVhZE51bWJlcih0cnVlKTt2YXIgbmV4dDI9dGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMik7aWYodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYgJiYgbmV4dCA9PT0gNDYgJiYgbmV4dDIgPT09IDQ2KXt0aGlzLnBvcyArPSAzO3JldHVybiB0aGlzLmZpbmlzaFRva2VuKHR0LmVsbGlwc2lzKTt9ZWxzZSB7Kyt0aGlzLnBvcztyZXR1cm4gdGhpcy5maW5pc2hUb2tlbih0dC5kb3QpO319O3BwLnJlYWRUb2tlbl9zbGFzaCA9IGZ1bmN0aW9uKCl7dmFyIG5leHQ9dGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMSk7aWYodGhpcy5leHByQWxsb3dlZCl7Kyt0aGlzLnBvcztyZXR1cm4gdGhpcy5yZWFkUmVnZXhwKCk7fWlmKG5leHQgPT09IDYxKXJldHVybiB0aGlzLmZpbmlzaE9wKHR0LmFzc2lnbiwgMik7cmV0dXJuIHRoaXMuZmluaXNoT3AodHQuc2xhc2gsIDEpO307cHAucmVhZFRva2VuX211bHRfbW9kdWxvID0gZnVuY3Rpb24oY29kZSl7dmFyIG5leHQ9dGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMSk7aWYobmV4dCA9PT0gNjEpcmV0dXJuIHRoaXMuZmluaXNoT3AodHQuYXNzaWduLCAyKTtyZXR1cm4gdGhpcy5maW5pc2hPcChjb2RlID09PSA0Mj90dC5zdGFyOnR0Lm1vZHVsbywgMSk7fTtwcC5yZWFkVG9rZW5fcGlwZV9hbXAgPSBmdW5jdGlvbihjb2RlKXt2YXIgbmV4dD10aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAxKTtpZihuZXh0ID09PSBjb2RlKXJldHVybiB0aGlzLmZpbmlzaE9wKGNvZGUgPT09IDEyND90dC5sb2dpY2FsT1I6dHQubG9naWNhbEFORCwgMik7aWYobmV4dCA9PT0gNjEpcmV0dXJuIHRoaXMuZmluaXNoT3AodHQuYXNzaWduLCAyKTtyZXR1cm4gdGhpcy5maW5pc2hPcChjb2RlID09PSAxMjQ/dHQuYml0d2lzZU9SOnR0LmJpdHdpc2VBTkQsIDEpO307cHAucmVhZFRva2VuX2NhcmV0ID0gZnVuY3Rpb24oKXt2YXIgbmV4dD10aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAxKTtpZihuZXh0ID09PSA2MSlyZXR1cm4gdGhpcy5maW5pc2hPcCh0dC5hc3NpZ24sIDIpO3JldHVybiB0aGlzLmZpbmlzaE9wKHR0LmJpdHdpc2VYT1IsIDEpO307cHAucmVhZFRva2VuX3BsdXNfbWluID0gZnVuY3Rpb24oY29kZSl7dmFyIG5leHQ9dGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMSk7aWYobmV4dCA9PT0gY29kZSl7aWYobmV4dCA9PSA0NSAmJiB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAyKSA9PSA2MiAmJiBsaW5lQnJlYWsudGVzdCh0aGlzLmlucHV0LnNsaWNlKHRoaXMubGFzdFRva0VuZCwgdGhpcy5wb3MpKSl7dGhpcy5za2lwTGluZUNvbW1lbnQoMyk7dGhpcy5za2lwU3BhY2UoKTtyZXR1cm4gdGhpcy5uZXh0VG9rZW4oKTt9cmV0dXJuIHRoaXMuZmluaXNoT3AodHQuaW5jRGVjLCAyKTt9aWYobmV4dCA9PT0gNjEpcmV0dXJuIHRoaXMuZmluaXNoT3AodHQuYXNzaWduLCAyKTtyZXR1cm4gdGhpcy5maW5pc2hPcCh0dC5wbHVzTWluLCAxKTt9O3BwLnJlYWRUb2tlbl9sdF9ndCA9IGZ1bmN0aW9uKGNvZGUpe3ZhciBuZXh0PXRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIDEpO3ZhciBzaXplPTE7aWYobmV4dCA9PT0gY29kZSl7c2l6ZSA9IGNvZGUgPT09IDYyICYmIHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIDIpID09PSA2Mj8zOjI7aWYodGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgc2l6ZSkgPT09IDYxKXJldHVybiB0aGlzLmZpbmlzaE9wKHR0LmFzc2lnbiwgc2l6ZSArIDEpO3JldHVybiB0aGlzLmZpbmlzaE9wKHR0LmJpdFNoaWZ0LCBzaXplKTt9aWYobmV4dCA9PSAzMyAmJiBjb2RlID09IDYwICYmIHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIDIpID09IDQ1ICYmIHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIDMpID09IDQ1KXtpZih0aGlzLmluTW9kdWxlKXRoaXMudW5leHBlY3RlZCgpO3RoaXMuc2tpcExpbmVDb21tZW50KDQpO3RoaXMuc2tpcFNwYWNlKCk7cmV0dXJuIHRoaXMubmV4dFRva2VuKCk7fWlmKG5leHQgPT09IDYxKXNpemUgPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAyKSA9PT0gNjE/MzoyO3JldHVybiB0aGlzLmZpbmlzaE9wKHR0LnJlbGF0aW9uYWwsIHNpemUpO307cHAucmVhZFRva2VuX2VxX2V4Y2wgPSBmdW5jdGlvbihjb2RlKXt2YXIgbmV4dD10aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAxKTtpZihuZXh0ID09PSA2MSlyZXR1cm4gdGhpcy5maW5pc2hPcCh0dC5lcXVhbGl0eSwgdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMikgPT09IDYxPzM6Mik7aWYoY29kZSA9PT0gNjEgJiYgbmV4dCA9PT0gNjIgJiYgdGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYpe3RoaXMucG9zICs9IDI7cmV0dXJuIHRoaXMuZmluaXNoVG9rZW4odHQuYXJyb3cpO31yZXR1cm4gdGhpcy5maW5pc2hPcChjb2RlID09PSA2MT90dC5lcTp0dC5wcmVmaXgsIDEpO307cHAuZ2V0VG9rZW5Gcm9tQ29kZSA9IGZ1bmN0aW9uKGNvZGUpe3N3aXRjaChjb2RlKXtjYXNlIDQ2OnJldHVybiB0aGlzLnJlYWRUb2tlbl9kb3QoKTtjYXNlIDQwOisrdGhpcy5wb3M7cmV0dXJuIHRoaXMuZmluaXNoVG9rZW4odHQucGFyZW5MKTtjYXNlIDQxOisrdGhpcy5wb3M7cmV0dXJuIHRoaXMuZmluaXNoVG9rZW4odHQucGFyZW5SKTtjYXNlIDU5OisrdGhpcy5wb3M7cmV0dXJuIHRoaXMuZmluaXNoVG9rZW4odHQuc2VtaSk7Y2FzZSA0NDorK3RoaXMucG9zO3JldHVybiB0aGlzLmZpbmlzaFRva2VuKHR0LmNvbW1hKTtjYXNlIDkxOisrdGhpcy5wb3M7cmV0dXJuIHRoaXMuZmluaXNoVG9rZW4odHQuYnJhY2tldEwpO2Nhc2UgOTM6Kyt0aGlzLnBvcztyZXR1cm4gdGhpcy5maW5pc2hUb2tlbih0dC5icmFja2V0Uik7Y2FzZSAxMjM6Kyt0aGlzLnBvcztyZXR1cm4gdGhpcy5maW5pc2hUb2tlbih0dC5icmFjZUwpO2Nhc2UgMTI1OisrdGhpcy5wb3M7cmV0dXJuIHRoaXMuZmluaXNoVG9rZW4odHQuYnJhY2VSKTtjYXNlIDU4OisrdGhpcy5wb3M7cmV0dXJuIHRoaXMuZmluaXNoVG9rZW4odHQuY29sb24pO2Nhc2UgNjM6Kyt0aGlzLnBvcztyZXR1cm4gdGhpcy5maW5pc2hUb2tlbih0dC5xdWVzdGlvbik7Y2FzZSA5NjppZih0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPCA2KWJyZWFrOysrdGhpcy5wb3M7cmV0dXJuIHRoaXMuZmluaXNoVG9rZW4odHQuYmFja1F1b3RlKTtjYXNlIDQ4OnZhciBuZXh0PXRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIDEpO2lmKG5leHQgPT09IDEyMCB8fCBuZXh0ID09PSA4OClyZXR1cm4gdGhpcy5yZWFkUmFkaXhOdW1iZXIoMTYpO2lmKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KXtpZihuZXh0ID09PSAxMTEgfHwgbmV4dCA9PT0gNzkpcmV0dXJuIHRoaXMucmVhZFJhZGl4TnVtYmVyKDgpO2lmKG5leHQgPT09IDk4IHx8IG5leHQgPT09IDY2KXJldHVybiB0aGlzLnJlYWRSYWRpeE51bWJlcigyKTt9Y2FzZSA0OTpjYXNlIDUwOmNhc2UgNTE6Y2FzZSA1MjpjYXNlIDUzOmNhc2UgNTQ6Y2FzZSA1NTpjYXNlIDU2OmNhc2UgNTc6cmV0dXJuIHRoaXMucmVhZE51bWJlcihmYWxzZSk7Y2FzZSAzNDpjYXNlIDM5OnJldHVybiB0aGlzLnJlYWRTdHJpbmcoY29kZSk7Y2FzZSA0NzpyZXR1cm4gdGhpcy5yZWFkVG9rZW5fc2xhc2goKTtjYXNlIDM3OmNhc2UgNDI6cmV0dXJuIHRoaXMucmVhZFRva2VuX211bHRfbW9kdWxvKGNvZGUpO2Nhc2UgMTI0OmNhc2UgMzg6cmV0dXJuIHRoaXMucmVhZFRva2VuX3BpcGVfYW1wKGNvZGUpO2Nhc2UgOTQ6cmV0dXJuIHRoaXMucmVhZFRva2VuX2NhcmV0KCk7Y2FzZSA0MzpjYXNlIDQ1OnJldHVybiB0aGlzLnJlYWRUb2tlbl9wbHVzX21pbihjb2RlKTtjYXNlIDYwOmNhc2UgNjI6cmV0dXJuIHRoaXMucmVhZFRva2VuX2x0X2d0KGNvZGUpO2Nhc2UgNjE6Y2FzZSAzMzpyZXR1cm4gdGhpcy5yZWFkVG9rZW5fZXFfZXhjbChjb2RlKTtjYXNlIDEyNjpyZXR1cm4gdGhpcy5maW5pc2hPcCh0dC5wcmVmaXgsIDEpO310aGlzLnJhaXNlKHRoaXMucG9zLCBcIlVuZXhwZWN0ZWQgY2hhcmFjdGVyICdcIiArIGNvZGVQb2ludFRvU3RyaW5nKGNvZGUpICsgXCInXCIpO307cHAuZmluaXNoT3AgPSBmdW5jdGlvbih0eXBlLCBzaXplKXt2YXIgc3RyPXRoaXMuaW5wdXQuc2xpY2UodGhpcy5wb3MsIHRoaXMucG9zICsgc2l6ZSk7dGhpcy5wb3MgKz0gc2l6ZTtyZXR1cm4gdGhpcy5maW5pc2hUb2tlbih0eXBlLCBzdHIpO307dmFyIHJlZ2V4cFVuaWNvZGVTdXBwb3J0PWZhbHNlO3RyeXtuZXcgUmVnRXhwKFwi77+/XCIsIFwidVwiKTtyZWdleHBVbmljb2RlU3VwcG9ydCA9IHRydWU7fWNhdGNoKGUpIHt9cHAucmVhZFJlZ2V4cCA9IGZ1bmN0aW9uKCl7dmFyIGVzY2FwZWQ9dW5kZWZpbmVkLCBpbkNsYXNzPXVuZGVmaW5lZCwgc3RhcnQ9dGhpcy5wb3M7Zm9yKDs7KSB7aWYodGhpcy5wb3MgPj0gdGhpcy5pbnB1dC5sZW5ndGgpdGhpcy5yYWlzZShzdGFydCwgXCJVbnRlcm1pbmF0ZWQgcmVndWxhciBleHByZXNzaW9uXCIpO3ZhciBjaD10aGlzLmlucHV0LmNoYXJBdCh0aGlzLnBvcyk7aWYobGluZUJyZWFrLnRlc3QoY2gpKXRoaXMucmFpc2Uoc3RhcnQsIFwiVW50ZXJtaW5hdGVkIHJlZ3VsYXIgZXhwcmVzc2lvblwiKTtpZighZXNjYXBlZCl7aWYoY2ggPT09IFwiW1wiKWluQ2xhc3MgPSB0cnVlO2Vsc2UgaWYoY2ggPT09IFwiXVwiICYmIGluQ2xhc3MpaW5DbGFzcyA9IGZhbHNlO2Vsc2UgaWYoY2ggPT09IFwiL1wiICYmICFpbkNsYXNzKWJyZWFrO2VzY2FwZWQgPSBjaCA9PT0gXCJcXFxcXCI7fWVsc2UgZXNjYXBlZCA9IGZhbHNlOysrdGhpcy5wb3M7fXZhciBjb250ZW50PXRoaXMuaW5wdXQuc2xpY2Uoc3RhcnQsIHRoaXMucG9zKTsrK3RoaXMucG9zO3ZhciBtb2RzPXRoaXMucmVhZFdvcmQxKCk7dmFyIHRtcD1jb250ZW50O2lmKG1vZHMpe3ZhciB2YWxpZEZsYWdzPS9eW2dtc2l5XSokLztpZih0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNil2YWxpZEZsYWdzID0gL15bZ21zaXl1XSokLztpZighdmFsaWRGbGFncy50ZXN0KG1vZHMpKXRoaXMucmFpc2Uoc3RhcnQsIFwiSW52YWxpZCByZWd1bGFyIGV4cHJlc3Npb24gZmxhZ1wiKTtpZihtb2RzLmluZGV4T2YoXCJ1XCIpID49IDAgJiYgIXJlZ2V4cFVuaWNvZGVTdXBwb3J0KXt0bXAgPSB0bXAucmVwbGFjZSgvXFxcXHUoW2EtZkEtRjAtOV17NH0pfFxcXFx1XFx7KFswLTlhLWZBLUZdKylcXH18W1xcdUQ4MDAtXFx1REJGRl1bXFx1REMwMC1cXHVERkZGXS9nLCBcInhcIik7fX12YXIgdmFsdWU9bnVsbDtpZighaXNSaGlubyl7dHJ5e25ldyBSZWdFeHAodG1wKTt9Y2F0Y2goZSkge2lmKGUgaW5zdGFuY2VvZiBTeW50YXhFcnJvcil0aGlzLnJhaXNlKHN0YXJ0LCBcIkVycm9yIHBhcnNpbmcgcmVndWxhciBleHByZXNzaW9uOiBcIiArIGUubWVzc2FnZSk7dGhpcy5yYWlzZShlKTt9dHJ5e3ZhbHVlID0gbmV3IFJlZ0V4cChjb250ZW50LCBtb2RzKTt9Y2F0Y2goZXJyKSB7fX1yZXR1cm4gdGhpcy5maW5pc2hUb2tlbih0dC5yZWdleHAsIHtwYXR0ZXJuOmNvbnRlbnQsIGZsYWdzOm1vZHMsIHZhbHVlOnZhbHVlfSk7fTtwcC5yZWFkSW50ID0gZnVuY3Rpb24ocmFkaXgsIGxlbil7dmFyIHN0YXJ0PXRoaXMucG9zLCB0b3RhbD0wO2Zvcih2YXIgaT0wLCBlPWxlbiA9PSBudWxsP0luZmluaXR5OmxlbjsgaSA8IGU7ICsraSkge3ZhciBjb2RlPXRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyksIHZhbD11bmRlZmluZWQ7aWYoY29kZSA+PSA5Nyl2YWwgPSBjb2RlIC0gOTcgKyAxMDtlbHNlIGlmKGNvZGUgPj0gNjUpdmFsID0gY29kZSAtIDY1ICsgMTA7ZWxzZSBpZihjb2RlID49IDQ4ICYmIGNvZGUgPD0gNTcpdmFsID0gY29kZSAtIDQ4O2Vsc2UgdmFsID0gSW5maW5pdHk7aWYodmFsID49IHJhZGl4KWJyZWFrOysrdGhpcy5wb3M7dG90YWwgPSB0b3RhbCAqIHJhZGl4ICsgdmFsO31pZih0aGlzLnBvcyA9PT0gc3RhcnQgfHwgbGVuICE9IG51bGwgJiYgdGhpcy5wb3MgLSBzdGFydCAhPT0gbGVuKXJldHVybiBudWxsO3JldHVybiB0b3RhbDt9O3BwLnJlYWRSYWRpeE51bWJlciA9IGZ1bmN0aW9uKHJhZGl4KXt0aGlzLnBvcyArPSAyO3ZhciB2YWw9dGhpcy5yZWFkSW50KHJhZGl4KTtpZih2YWwgPT0gbnVsbCl0aGlzLnJhaXNlKHRoaXMuc3RhcnQgKyAyLCBcIkV4cGVjdGVkIG51bWJlciBpbiByYWRpeCBcIiArIHJhZGl4KTtpZihpc0lkZW50aWZpZXJTdGFydCh0aGlzLmZ1bGxDaGFyQ29kZUF0UG9zKCkpKXRoaXMucmFpc2UodGhpcy5wb3MsIFwiSWRlbnRpZmllciBkaXJlY3RseSBhZnRlciBudW1iZXJcIik7cmV0dXJuIHRoaXMuZmluaXNoVG9rZW4odHQubnVtLCB2YWwpO307cHAucmVhZE51bWJlciA9IGZ1bmN0aW9uKHN0YXJ0c1dpdGhEb3Qpe3ZhciBzdGFydD10aGlzLnBvcywgaXNGbG9hdD1mYWxzZSwgb2N0YWw9dGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zKSA9PT0gNDg7aWYoIXN0YXJ0c1dpdGhEb3QgJiYgdGhpcy5yZWFkSW50KDEwKSA9PT0gbnVsbCl0aGlzLnJhaXNlKHN0YXJ0LCBcIkludmFsaWQgbnVtYmVyXCIpO2lmKHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcykgPT09IDQ2KXsrK3RoaXMucG9zO3RoaXMucmVhZEludCgxMCk7aXNGbG9hdCA9IHRydWU7fXZhciBuZXh0PXRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyk7aWYobmV4dCA9PT0gNjkgfHwgbmV4dCA9PT0gMTAxKXtuZXh0ID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KCsrdGhpcy5wb3MpO2lmKG5leHQgPT09IDQzIHx8IG5leHQgPT09IDQ1KSsrdGhpcy5wb3M7aWYodGhpcy5yZWFkSW50KDEwKSA9PT0gbnVsbCl0aGlzLnJhaXNlKHN0YXJ0LCBcIkludmFsaWQgbnVtYmVyXCIpO2lzRmxvYXQgPSB0cnVlO31pZihpc0lkZW50aWZpZXJTdGFydCh0aGlzLmZ1bGxDaGFyQ29kZUF0UG9zKCkpKXRoaXMucmFpc2UodGhpcy5wb3MsIFwiSWRlbnRpZmllciBkaXJlY3RseSBhZnRlciBudW1iZXJcIik7dmFyIHN0cj10aGlzLmlucHV0LnNsaWNlKHN0YXJ0LCB0aGlzLnBvcyksIHZhbD11bmRlZmluZWQ7aWYoaXNGbG9hdCl2YWwgPSBwYXJzZUZsb2F0KHN0cik7ZWxzZSBpZighb2N0YWwgfHwgc3RyLmxlbmd0aCA9PT0gMSl2YWwgPSBwYXJzZUludChzdHIsIDEwKTtlbHNlIGlmKC9bODldLy50ZXN0KHN0cikgfHwgdGhpcy5zdHJpY3QpdGhpcy5yYWlzZShzdGFydCwgXCJJbnZhbGlkIG51bWJlclwiKTtlbHNlIHZhbCA9IHBhcnNlSW50KHN0ciwgOCk7cmV0dXJuIHRoaXMuZmluaXNoVG9rZW4odHQubnVtLCB2YWwpO307cHAucmVhZENvZGVQb2ludCA9IGZ1bmN0aW9uKCl7dmFyIGNoPXRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyksIGNvZGU9dW5kZWZpbmVkO2lmKGNoID09PSAxMjMpe2lmKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA8IDYpdGhpcy51bmV4cGVjdGVkKCk7Kyt0aGlzLnBvcztjb2RlID0gdGhpcy5yZWFkSGV4Q2hhcih0aGlzLmlucHV0LmluZGV4T2YoXCJ9XCIsIHRoaXMucG9zKSAtIHRoaXMucG9zKTsrK3RoaXMucG9zO2lmKGNvZGUgPiAxMTE0MTExKXRoaXMudW5leHBlY3RlZCgpO31lbHNlIHtjb2RlID0gdGhpcy5yZWFkSGV4Q2hhcig0KTt9cmV0dXJuIGNvZGU7fTtmdW5jdGlvbiBjb2RlUG9pbnRUb1N0cmluZyhjb2RlKXtpZihjb2RlIDw9IDY1NTM1KXtyZXR1cm4gU3RyaW5nLmZyb21DaGFyQ29kZShjb2RlKTt9cmV0dXJuIFN0cmluZy5mcm9tQ2hhckNvZGUoKGNvZGUgLSA2NTUzNiA+PiAxMCkgKyA1NTI5NiwgKGNvZGUgLSA2NTUzNiAmIDEwMjMpICsgNTYzMjApO31wcC5yZWFkU3RyaW5nID0gZnVuY3Rpb24ocXVvdGUpe3ZhciBvdXQ9XCJcIiwgY2h1bmtTdGFydD0rK3RoaXMucG9zO2Zvcig7Oykge2lmKHRoaXMucG9zID49IHRoaXMuaW5wdXQubGVuZ3RoKXRoaXMucmFpc2UodGhpcy5zdGFydCwgXCJVbnRlcm1pbmF0ZWQgc3RyaW5nIGNvbnN0YW50XCIpO3ZhciBjaD10aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MpO2lmKGNoID09PSBxdW90ZSlicmVhaztpZihjaCA9PT0gOTIpe291dCArPSB0aGlzLmlucHV0LnNsaWNlKGNodW5rU3RhcnQsIHRoaXMucG9zKTtvdXQgKz0gdGhpcy5yZWFkRXNjYXBlZENoYXIoKTtjaHVua1N0YXJ0ID0gdGhpcy5wb3M7fWVsc2Uge2lmKGlzTmV3TGluZShjaCkpdGhpcy5yYWlzZSh0aGlzLnN0YXJ0LCBcIlVudGVybWluYXRlZCBzdHJpbmcgY29uc3RhbnRcIik7Kyt0aGlzLnBvczt9fW91dCArPSB0aGlzLmlucHV0LnNsaWNlKGNodW5rU3RhcnQsIHRoaXMucG9zKyspO3JldHVybiB0aGlzLmZpbmlzaFRva2VuKHR0LnN0cmluZywgb3V0KTt9O3BwLnJlYWRUbXBsVG9rZW4gPSBmdW5jdGlvbigpe3ZhciBvdXQ9XCJcIiwgY2h1bmtTdGFydD10aGlzLnBvcztmb3IoOzspIHtpZih0aGlzLnBvcyA+PSB0aGlzLmlucHV0Lmxlbmd0aCl0aGlzLnJhaXNlKHRoaXMuc3RhcnQsIFwiVW50ZXJtaW5hdGVkIHRlbXBsYXRlXCIpO3ZhciBjaD10aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MpO2lmKGNoID09PSA5NiB8fCBjaCA9PT0gMzYgJiYgdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMSkgPT09IDEyMyl7aWYodGhpcy5wb3MgPT09IHRoaXMuc3RhcnQgJiYgdGhpcy50eXBlID09PSB0dC50ZW1wbGF0ZSl7aWYoY2ggPT09IDM2KXt0aGlzLnBvcyArPSAyO3JldHVybiB0aGlzLmZpbmlzaFRva2VuKHR0LmRvbGxhckJyYWNlTCk7fWVsc2UgeysrdGhpcy5wb3M7cmV0dXJuIHRoaXMuZmluaXNoVG9rZW4odHQuYmFja1F1b3RlKTt9fW91dCArPSB0aGlzLmlucHV0LnNsaWNlKGNodW5rU3RhcnQsIHRoaXMucG9zKTtyZXR1cm4gdGhpcy5maW5pc2hUb2tlbih0dC50ZW1wbGF0ZSwgb3V0KTt9aWYoY2ggPT09IDkyKXtvdXQgKz0gdGhpcy5pbnB1dC5zbGljZShjaHVua1N0YXJ0LCB0aGlzLnBvcyk7b3V0ICs9IHRoaXMucmVhZEVzY2FwZWRDaGFyKCk7Y2h1bmtTdGFydCA9IHRoaXMucG9zO31lbHNlIGlmKGlzTmV3TGluZShjaCkpe291dCArPSB0aGlzLmlucHV0LnNsaWNlKGNodW5rU3RhcnQsIHRoaXMucG9zKTsrK3RoaXMucG9zO2lmKGNoID09PSAxMyAmJiB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MpID09PSAxMCl7Kyt0aGlzLnBvcztvdXQgKz0gXCJcXG5cIjt9ZWxzZSB7b3V0ICs9IFN0cmluZy5mcm9tQ2hhckNvZGUoY2gpO31pZih0aGlzLm9wdGlvbnMubG9jYXRpb25zKXsrK3RoaXMuY3VyTGluZTt0aGlzLmxpbmVTdGFydCA9IHRoaXMucG9zO31jaHVua1N0YXJ0ID0gdGhpcy5wb3M7fWVsc2UgeysrdGhpcy5wb3M7fX19O3BwLnJlYWRFc2NhcGVkQ2hhciA9IGZ1bmN0aW9uKCl7dmFyIGNoPXRoaXMuaW5wdXQuY2hhckNvZGVBdCgrK3RoaXMucG9zKTt2YXIgb2N0YWw9L15bMC03XSsvLmV4ZWModGhpcy5pbnB1dC5zbGljZSh0aGlzLnBvcywgdGhpcy5wb3MgKyAzKSk7aWYob2N0YWwpb2N0YWwgPSBvY3RhbFswXTt3aGlsZShvY3RhbCAmJiBwYXJzZUludChvY3RhbCwgOCkgPiAyNTUpIG9jdGFsID0gb2N0YWwuc2xpY2UoMCwgLTEpO2lmKG9jdGFsID09PSBcIjBcIilvY3RhbCA9IG51bGw7Kyt0aGlzLnBvcztpZihvY3RhbCl7aWYodGhpcy5zdHJpY3QpdGhpcy5yYWlzZSh0aGlzLnBvcyAtIDIsIFwiT2N0YWwgbGl0ZXJhbCBpbiBzdHJpY3QgbW9kZVwiKTt0aGlzLnBvcyArPSBvY3RhbC5sZW5ndGggLSAxO3JldHVybiBTdHJpbmcuZnJvbUNoYXJDb2RlKHBhcnNlSW50KG9jdGFsLCA4KSk7fWVsc2Uge3N3aXRjaChjaCl7Y2FzZSAxMTA6cmV0dXJuIFwiXFxuXCI7Y2FzZSAxMTQ6cmV0dXJuIFwiXFxyXCI7Y2FzZSAxMjA6cmV0dXJuIFN0cmluZy5mcm9tQ2hhckNvZGUodGhpcy5yZWFkSGV4Q2hhcigyKSk7Y2FzZSAxMTc6cmV0dXJuIGNvZGVQb2ludFRvU3RyaW5nKHRoaXMucmVhZENvZGVQb2ludCgpKTtjYXNlIDExNjpyZXR1cm4gXCJcXHRcIjtjYXNlIDk4OnJldHVybiBcIlxcYlwiO2Nhc2UgMTE4OnJldHVybiBcIlxcdTAwMGJcIjtjYXNlIDEwMjpyZXR1cm4gXCJcXGZcIjtjYXNlIDQ4OnJldHVybiBcIlxcdTAwMDBcIjtjYXNlIDEzOmlmKHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcykgPT09IDEwKSsrdGhpcy5wb3M7Y2FzZSAxMDppZih0aGlzLm9wdGlvbnMubG9jYXRpb25zKXt0aGlzLmxpbmVTdGFydCA9IHRoaXMucG9zOysrdGhpcy5jdXJMaW5lO31yZXR1cm4gXCJcIjtkZWZhdWx0OnJldHVybiBTdHJpbmcuZnJvbUNoYXJDb2RlKGNoKTt9fX07cHAucmVhZEhleENoYXIgPSBmdW5jdGlvbihsZW4pe3ZhciBuPXRoaXMucmVhZEludCgxNiwgbGVuKTtpZihuID09PSBudWxsKXRoaXMucmFpc2UodGhpcy5zdGFydCwgXCJCYWQgY2hhcmFjdGVyIGVzY2FwZSBzZXF1ZW5jZVwiKTtyZXR1cm4gbjt9O3ZhciBjb250YWluc0VzYztwcC5yZWFkV29yZDEgPSBmdW5jdGlvbigpe2NvbnRhaW5zRXNjID0gZmFsc2U7dmFyIHdvcmQ9XCJcIiwgZmlyc3Q9dHJ1ZSwgY2h1bmtTdGFydD10aGlzLnBvczt2YXIgYXN0cmFsPXRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2O3doaWxlKHRoaXMucG9zIDwgdGhpcy5pbnB1dC5sZW5ndGgpIHt2YXIgY2g9dGhpcy5mdWxsQ2hhckNvZGVBdFBvcygpO2lmKGlzSWRlbnRpZmllckNoYXIoY2gsIGFzdHJhbCkpe3RoaXMucG9zICs9IGNoIDw9IDY1NTM1PzE6Mjt9ZWxzZSBpZihjaCA9PT0gOTIpe2NvbnRhaW5zRXNjID0gdHJ1ZTt3b3JkICs9IHRoaXMuaW5wdXQuc2xpY2UoY2h1bmtTdGFydCwgdGhpcy5wb3MpO3ZhciBlc2NTdGFydD10aGlzLnBvcztpZih0aGlzLmlucHV0LmNoYXJDb2RlQXQoKyt0aGlzLnBvcykgIT0gMTE3KXRoaXMucmFpc2UodGhpcy5wb3MsIFwiRXhwZWN0aW5nIFVuaWNvZGUgZXNjYXBlIHNlcXVlbmNlIFxcXFx1WFhYWFwiKTsrK3RoaXMucG9zO3ZhciBlc2M9dGhpcy5yZWFkQ29kZVBvaW50KCk7aWYoIShmaXJzdD9pc0lkZW50aWZpZXJTdGFydDppc0lkZW50aWZpZXJDaGFyKShlc2MsIGFzdHJhbCkpdGhpcy5yYWlzZShlc2NTdGFydCwgXCJJbnZhbGlkIFVuaWNvZGUgZXNjYXBlXCIpO3dvcmQgKz0gY29kZVBvaW50VG9TdHJpbmcoZXNjKTtjaHVua1N0YXJ0ID0gdGhpcy5wb3M7fWVsc2Uge2JyZWFrO31maXJzdCA9IGZhbHNlO31yZXR1cm4gd29yZCArIHRoaXMuaW5wdXQuc2xpY2UoY2h1bmtTdGFydCwgdGhpcy5wb3MpO307cHAucmVhZFdvcmQgPSBmdW5jdGlvbigpe3ZhciB3b3JkPXRoaXMucmVhZFdvcmQxKCk7dmFyIHR5cGU9dHQubmFtZTtpZigodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYgfHwgIWNvbnRhaW5zRXNjKSAmJiB0aGlzLmlzS2V5d29yZCh3b3JkKSl0eXBlID0ga2V5d29yZFR5cGVzW3dvcmRdO3JldHVybiB0aGlzLmZpbmlzaFRva2VuKHR5cGUsIHdvcmQpO307fSwge1wiLi9pZGVudGlmaWVyXCI6NywgXCIuL2xvY2F0aW9uXCI6OCwgXCIuL3N0YXRlXCI6MTMsIFwiLi90b2tlbnR5cGVcIjoxNywgXCIuL3doaXRlc3BhY2VcIjoxOX1dLCAxNzpbZnVuY3Rpb24oX2RlcmVxXywgbW9kdWxlLCBleHBvcnRzKXtcInVzZSBzdHJpY3RcIjt2YXIgX2NsYXNzQ2FsbENoZWNrPWZ1bmN0aW9uIF9jbGFzc0NhbGxDaGVjayhpbnN0YW5jZSwgQ29uc3RydWN0b3Ipe2lmKCEoaW5zdGFuY2UgaW5zdGFuY2VvZiBDb25zdHJ1Y3Rvcikpe3Rocm93IG5ldyBUeXBlRXJyb3IoXCJDYW5ub3QgY2FsbCBhIGNsYXNzIGFzIGEgZnVuY3Rpb25cIik7fX07ZXhwb3J0cy5fX2VzTW9kdWxlID0gdHJ1ZTt2YXIgVG9rZW5UeXBlPWV4cG9ydHMuVG9rZW5UeXBlID0gZnVuY3Rpb24gVG9rZW5UeXBlKGxhYmVsKXt2YXIgY29uZj1hcmd1bWVudHNbMV0gPT09IHVuZGVmaW5lZD97fTphcmd1bWVudHNbMV07X2NsYXNzQ2FsbENoZWNrKHRoaXMsIFRva2VuVHlwZSk7dGhpcy5sYWJlbCA9IGxhYmVsO3RoaXMua2V5d29yZCA9IGNvbmYua2V5d29yZDt0aGlzLmJlZm9yZUV4cHIgPSAhIWNvbmYuYmVmb3JlRXhwcjt0aGlzLnN0YXJ0c0V4cHIgPSAhIWNvbmYuc3RhcnRzRXhwcjt0aGlzLmlzTG9vcCA9ICEhY29uZi5pc0xvb3A7dGhpcy5pc0Fzc2lnbiA9ICEhY29uZi5pc0Fzc2lnbjt0aGlzLnByZWZpeCA9ICEhY29uZi5wcmVmaXg7dGhpcy5wb3N0Zml4ID0gISFjb25mLnBvc3RmaXg7dGhpcy5iaW5vcCA9IGNvbmYuYmlub3AgfHwgbnVsbDt0aGlzLnVwZGF0ZUNvbnRleHQgPSBudWxsO307ZnVuY3Rpb24gYmlub3AobmFtZSwgcHJlYyl7cmV0dXJuIG5ldyBUb2tlblR5cGUobmFtZSwge2JlZm9yZUV4cHI6dHJ1ZSwgYmlub3A6cHJlY30pO312YXIgYmVmb3JlRXhwcj17YmVmb3JlRXhwcjp0cnVlfSwgc3RhcnRzRXhwcj17c3RhcnRzRXhwcjp0cnVlfTt2YXIgdHlwZXM9e251bTpuZXcgVG9rZW5UeXBlKFwibnVtXCIsIHN0YXJ0c0V4cHIpLCByZWdleHA6bmV3IFRva2VuVHlwZShcInJlZ2V4cFwiLCBzdGFydHNFeHByKSwgc3RyaW5nOm5ldyBUb2tlblR5cGUoXCJzdHJpbmdcIiwgc3RhcnRzRXhwciksIG5hbWU6bmV3IFRva2VuVHlwZShcIm5hbWVcIiwgc3RhcnRzRXhwciksIGVvZjpuZXcgVG9rZW5UeXBlKFwiZW9mXCIpLCBicmFja2V0TDpuZXcgVG9rZW5UeXBlKFwiW1wiLCB7YmVmb3JlRXhwcjp0cnVlLCBzdGFydHNFeHByOnRydWV9KSwgYnJhY2tldFI6bmV3IFRva2VuVHlwZShcIl1cIiksIGJyYWNlTDpuZXcgVG9rZW5UeXBlKFwie1wiLCB7YmVmb3JlRXhwcjp0cnVlLCBzdGFydHNFeHByOnRydWV9KSwgYnJhY2VSOm5ldyBUb2tlblR5cGUoXCJ9XCIpLCBwYXJlbkw6bmV3IFRva2VuVHlwZShcIihcIiwge2JlZm9yZUV4cHI6dHJ1ZSwgc3RhcnRzRXhwcjp0cnVlfSksIHBhcmVuUjpuZXcgVG9rZW5UeXBlKFwiKVwiKSwgY29tbWE6bmV3IFRva2VuVHlwZShcIixcIiwgYmVmb3JlRXhwciksIHNlbWk6bmV3IFRva2VuVHlwZShcIjtcIiwgYmVmb3JlRXhwciksIGNvbG9uOm5ldyBUb2tlblR5cGUoXCI6XCIsIGJlZm9yZUV4cHIpLCBkb3Q6bmV3IFRva2VuVHlwZShcIi5cIiksIHF1ZXN0aW9uOm5ldyBUb2tlblR5cGUoXCI/XCIsIGJlZm9yZUV4cHIpLCBhcnJvdzpuZXcgVG9rZW5UeXBlKFwiPT5cIiwgYmVmb3JlRXhwciksIHRlbXBsYXRlOm5ldyBUb2tlblR5cGUoXCJ0ZW1wbGF0ZVwiKSwgZWxsaXBzaXM6bmV3IFRva2VuVHlwZShcIi4uLlwiLCBiZWZvcmVFeHByKSwgYmFja1F1b3RlOm5ldyBUb2tlblR5cGUoXCJgXCIsIHN0YXJ0c0V4cHIpLCBkb2xsYXJCcmFjZUw6bmV3IFRva2VuVHlwZShcIiR7XCIsIHtiZWZvcmVFeHByOnRydWUsIHN0YXJ0c0V4cHI6dHJ1ZX0pLCBlcTpuZXcgVG9rZW5UeXBlKFwiPVwiLCB7YmVmb3JlRXhwcjp0cnVlLCBpc0Fzc2lnbjp0cnVlfSksIGFzc2lnbjpuZXcgVG9rZW5UeXBlKFwiXz1cIiwge2JlZm9yZUV4cHI6dHJ1ZSwgaXNBc3NpZ246dHJ1ZX0pLCBpbmNEZWM6bmV3IFRva2VuVHlwZShcIisrLy0tXCIsIHtwcmVmaXg6dHJ1ZSwgcG9zdGZpeDp0cnVlLCBzdGFydHNFeHByOnRydWV9KSwgcHJlZml4Om5ldyBUb2tlblR5cGUoXCJwcmVmaXhcIiwge2JlZm9yZUV4cHI6dHJ1ZSwgcHJlZml4OnRydWUsIHN0YXJ0c0V4cHI6dHJ1ZX0pLCBsb2dpY2FsT1I6Ymlub3AoXCJ8fFwiLCAxKSwgbG9naWNhbEFORDpiaW5vcChcIiYmXCIsIDIpLCBiaXR3aXNlT1I6Ymlub3AoXCJ8XCIsIDMpLCBiaXR3aXNlWE9SOmJpbm9wKFwiXlwiLCA0KSwgYml0d2lzZUFORDpiaW5vcChcIiZcIiwgNSksIGVxdWFsaXR5OmJpbm9wKFwiPT0vIT1cIiwgNiksIHJlbGF0aW9uYWw6Ymlub3AoXCI8Lz5cIiwgNyksIGJpdFNoaWZ0OmJpbm9wKFwiPDwvPj5cIiwgOCksIHBsdXNNaW46bmV3IFRva2VuVHlwZShcIisvLVwiLCB7YmVmb3JlRXhwcjp0cnVlLCBiaW5vcDo5LCBwcmVmaXg6dHJ1ZSwgc3RhcnRzRXhwcjp0cnVlfSksIG1vZHVsbzpiaW5vcChcIiVcIiwgMTApLCBzdGFyOmJpbm9wKFwiKlwiLCAxMCksIHNsYXNoOmJpbm9wKFwiL1wiLCAxMCl9O2V4cG9ydHMudHlwZXMgPSB0eXBlczt2YXIga2V5d29yZHM9e307ZXhwb3J0cy5rZXl3b3JkcyA9IGtleXdvcmRzO2Z1bmN0aW9uIGt3KG5hbWUpe3ZhciBvcHRpb25zPWFyZ3VtZW50c1sxXSA9PT0gdW5kZWZpbmVkP3t9OmFyZ3VtZW50c1sxXTtvcHRpb25zLmtleXdvcmQgPSBuYW1lO2tleXdvcmRzW25hbWVdID0gdHlwZXNbXCJfXCIgKyBuYW1lXSA9IG5ldyBUb2tlblR5cGUobmFtZSwgb3B0aW9ucyk7fWt3KFwiYnJlYWtcIik7a3coXCJjYXNlXCIsIGJlZm9yZUV4cHIpO2t3KFwiY2F0Y2hcIik7a3coXCJjb250aW51ZVwiKTtrdyhcImRlYnVnZ2VyXCIpO2t3KFwiZGVmYXVsdFwiKTtrdyhcImRvXCIsIHtpc0xvb3A6dHJ1ZX0pO2t3KFwiZWxzZVwiLCBiZWZvcmVFeHByKTtrdyhcImZpbmFsbHlcIik7a3coXCJmb3JcIiwge2lzTG9vcDp0cnVlfSk7a3coXCJmdW5jdGlvblwiLCBzdGFydHNFeHByKTtrdyhcImlmXCIpO2t3KFwicmV0dXJuXCIsIGJlZm9yZUV4cHIpO2t3KFwic3dpdGNoXCIpO2t3KFwidGhyb3dcIiwgYmVmb3JlRXhwcik7a3coXCJ0cnlcIik7a3coXCJ2YXJcIik7a3coXCJsZXRcIik7a3coXCJjb25zdFwiKTtrdyhcIndoaWxlXCIsIHtpc0xvb3A6dHJ1ZX0pO2t3KFwid2l0aFwiKTtrdyhcIm5ld1wiLCB7YmVmb3JlRXhwcjp0cnVlLCBzdGFydHNFeHByOnRydWV9KTtrdyhcInRoaXNcIiwgc3RhcnRzRXhwcik7a3coXCJzdXBlclwiLCBzdGFydHNFeHByKTtrdyhcImNsYXNzXCIpO2t3KFwiZXh0ZW5kc1wiLCBiZWZvcmVFeHByKTtrdyhcImV4cG9ydFwiKTtrdyhcImltcG9ydFwiKTtrdyhcInlpZWxkXCIsIHtiZWZvcmVFeHByOnRydWUsIHN0YXJ0c0V4cHI6dHJ1ZX0pO2t3KFwibnVsbFwiLCBzdGFydHNFeHByKTtrdyhcInRydWVcIiwgc3RhcnRzRXhwcik7a3coXCJmYWxzZVwiLCBzdGFydHNFeHByKTtrdyhcImluXCIsIHtiZWZvcmVFeHByOnRydWUsIGJpbm9wOjd9KTtrdyhcImluc3RhbmNlb2ZcIiwge2JlZm9yZUV4cHI6dHJ1ZSwgYmlub3A6N30pO2t3KFwidHlwZW9mXCIsIHtiZWZvcmVFeHByOnRydWUsIHByZWZpeDp0cnVlLCBzdGFydHNFeHByOnRydWV9KTtrdyhcInZvaWRcIiwge2JlZm9yZUV4cHI6dHJ1ZSwgcHJlZml4OnRydWUsIHN0YXJ0c0V4cHI6dHJ1ZX0pO2t3KFwiZGVsZXRlXCIsIHtiZWZvcmVFeHByOnRydWUsIHByZWZpeDp0cnVlLCBzdGFydHNFeHByOnRydWV9KTt9LCB7fV0sIDE4OltmdW5jdGlvbihfZGVyZXFfLCBtb2R1bGUsIGV4cG9ydHMpe1widXNlIHN0cmljdFwiO2V4cG9ydHMuaXNBcnJheSA9IGlzQXJyYXk7ZXhwb3J0cy5oYXMgPSBoYXM7ZXhwb3J0cy5fX2VzTW9kdWxlID0gdHJ1ZTtmdW5jdGlvbiBpc0FycmF5KG9iail7cmV0dXJuIE9iamVjdC5wcm90b3R5cGUudG9TdHJpbmcuY2FsbChvYmopID09PSBcIltvYmplY3QgQXJyYXldXCI7fWZ1bmN0aW9uIGhhcyhvYmosIHByb3BOYW1lKXtyZXR1cm4gT2JqZWN0LnByb3RvdHlwZS5oYXNPd25Qcm9wZXJ0eS5jYWxsKG9iaiwgcHJvcE5hbWUpO319LCB7fV0sIDE5OltmdW5jdGlvbihfZGVyZXFfLCBtb2R1bGUsIGV4cG9ydHMpe1widXNlIHN0cmljdFwiO2V4cG9ydHMuaXNOZXdMaW5lID0gaXNOZXdMaW5lO2V4cG9ydHMuX19lc01vZHVsZSA9IHRydWU7dmFyIGxpbmVCcmVhaz0vXFxyXFxuP3xcXG58XFx1MjAyOHxcXHUyMDI5LztleHBvcnRzLmxpbmVCcmVhayA9IGxpbmVCcmVhazt2YXIgbGluZUJyZWFrRz1uZXcgUmVnRXhwKGxpbmVCcmVhay5zb3VyY2UsIFwiZ1wiKTtleHBvcnRzLmxpbmVCcmVha0cgPSBsaW5lQnJlYWtHO2Z1bmN0aW9uIGlzTmV3TGluZShjb2RlKXtyZXR1cm4gY29kZSA9PT0gMTAgfHwgY29kZSA9PT0gMTMgfHwgY29kZSA9PT0gODIzMiB8fCBjb2RlID09IDgyMzM7fXZhciBub25BU0NJSXdoaXRlc3BhY2U9L1tcXHUxNjgwXFx1MTgwZVxcdTIwMDAtXFx1MjAwYVxcdTIwMmZcXHUyMDVmXFx1MzAwMFxcdWZlZmZdLztleHBvcnRzLm5vbkFTQ0lJd2hpdGVzcGFjZSA9IG5vbkFTQ0lJd2hpdGVzcGFjZTt9LCB7fV19LCB7fSwgWzFdKSgxKTt9KTtcblxufSkuY2FsbCh0aGlzLHR5cGVvZiBnbG9iYWwgIT09IFwidW5kZWZpbmVkXCIgPyBnbG9iYWwgOiB0eXBlb2Ygc2VsZiAhPT0gXCJ1bmRlZmluZWRcIiA/IHNlbGYgOiB0eXBlb2Ygd2luZG93ICE9PSBcInVuZGVmaW5lZFwiID8gd2luZG93IDoge30pXG59LHt9XSwzOltmdW5jdGlvbihfZGVyZXFfLG1vZHVsZSxleHBvcnRzKXtcblwidXNlIHN0cmljdFwiO1xuXG5tb2R1bGUuZXhwb3J0cyA9IHR5cGVvZiBhY29ybiAhPSBcInVuZGVmaW5lZFwiID8gYWNvcm4gOiBfZGVyZXFfKFwiYWNvcm5cIik7XG5cbn0se1wiYWNvcm5cIjoyfV0sNDpbZnVuY3Rpb24oX2RlcmVxXyxtb2R1bGUsZXhwb3J0cyl7XG5cInVzZSBzdHJpY3RcIjtcblxudmFyIExvb3NlUGFyc2VyID0gX2RlcmVxXyhcIi4vc3RhdGVcIikuTG9vc2VQYXJzZXI7XG5cbnZhciBpc0R1bW15ID0gX2RlcmVxXyhcIi4vcGFyc2V1dGlsXCIpLmlzRHVtbXk7XG5cbnZhciB0dCA9IF9kZXJlcV8oXCIuLlwiKS50b2tUeXBlcztcblxudmFyIGxwID0gTG9vc2VQYXJzZXIucHJvdG90eXBlO1xuXG5scC5jaGVja0xWYWwgPSBmdW5jdGlvbiAoZXhwciwgYmluZGluZykge1xuICBpZiAoIWV4cHIpIHJldHVybiBleHByO1xuICBzd2l0Y2ggKGV4cHIudHlwZSkge1xuICAgIGNhc2UgXCJJZGVudGlmaWVyXCI6XG4gICAgICByZXR1cm4gZXhwcjtcblxuICAgIGNhc2UgXCJNZW1iZXJFeHByZXNzaW9uXCI6XG4gICAgICByZXR1cm4gYmluZGluZyA/IHRoaXMuZHVtbXlJZGVudCgpIDogZXhwcjtcblxuICAgIGNhc2UgXCJQYXJlbnRoZXNpemVkRXhwcmVzc2lvblwiOlxuICAgICAgZXhwci5leHByZXNzaW9uID0gdGhpcy5jaGVja0xWYWwoZXhwci5leHByZXNzaW9uLCBiaW5kaW5nKTtcbiAgICAgIHJldHVybiBleHByO1xuXG4gICAgLy8gRklYTUUgcmVjdXJzaXZlbHkgY2hlY2sgY29udGVudHNcbiAgICBjYXNlIFwiT2JqZWN0UGF0dGVyblwiOlxuICAgIGNhc2UgXCJBcnJheVBhdHRlcm5cIjpcbiAgICBjYXNlIFwiUmVzdEVsZW1lbnRcIjpcbiAgICBjYXNlIFwiQXNzaWdubWVudFBhdHRlcm5cIjpcbiAgICAgIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNikgcmV0dXJuIGV4cHI7XG5cbiAgICBkZWZhdWx0OlxuICAgICAgcmV0dXJuIHRoaXMuZHVtbXlJZGVudCgpO1xuICB9XG59O1xuXG5scC5wYXJzZUV4cHJlc3Npb24gPSBmdW5jdGlvbiAobm9Jbikge1xuICB2YXIgc3RhcnQgPSB0aGlzLnN0b3JlQ3VycmVudFBvcygpO1xuICB2YXIgZXhwciA9IHRoaXMucGFyc2VNYXliZUFzc2lnbihub0luKTtcbiAgaWYgKHRoaXMudG9rLnR5cGUgPT09IHR0LmNvbW1hKSB7XG4gICAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0KTtcbiAgICBub2RlLmV4cHJlc3Npb25zID0gW2V4cHJdO1xuICAgIHdoaWxlICh0aGlzLmVhdCh0dC5jb21tYSkpIG5vZGUuZXhwcmVzc2lvbnMucHVzaCh0aGlzLnBhcnNlTWF5YmVBc3NpZ24obm9JbikpO1xuICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJTZXF1ZW5jZUV4cHJlc3Npb25cIik7XG4gIH1cbiAgcmV0dXJuIGV4cHI7XG59O1xuXG5scC5wYXJzZVBhcmVuRXhwcmVzc2lvbiA9IGZ1bmN0aW9uICgpIHtcbiAgdGhpcy5wdXNoQ3goKTtcbiAgdGhpcy5leHBlY3QodHQucGFyZW5MKTtcbiAgdmFyIHZhbCA9IHRoaXMucGFyc2VFeHByZXNzaW9uKCk7XG4gIHRoaXMucG9wQ3goKTtcbiAgdGhpcy5leHBlY3QodHQucGFyZW5SKTtcbiAgcmV0dXJuIHZhbDtcbn07XG5cbmxwLnBhcnNlTWF5YmVBc3NpZ24gPSBmdW5jdGlvbiAobm9Jbikge1xuICB2YXIgc3RhcnQgPSB0aGlzLnN0b3JlQ3VycmVudFBvcygpO1xuICB2YXIgbGVmdCA9IHRoaXMucGFyc2VNYXliZUNvbmRpdGlvbmFsKG5vSW4pO1xuICBpZiAodGhpcy50b2sudHlwZS5pc0Fzc2lnbikge1xuICAgIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGVBdChzdGFydCk7XG4gICAgbm9kZS5vcGVyYXRvciA9IHRoaXMudG9rLnZhbHVlO1xuICAgIG5vZGUubGVmdCA9IHRoaXMudG9rLnR5cGUgPT09IHR0LmVxID8gdGhpcy50b0Fzc2lnbmFibGUobGVmdCkgOiB0aGlzLmNoZWNrTFZhbChsZWZ0KTtcbiAgICB0aGlzLm5leHQoKTtcbiAgICBub2RlLnJpZ2h0ID0gdGhpcy5wYXJzZU1heWJlQXNzaWduKG5vSW4pO1xuICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJBc3NpZ25tZW50RXhwcmVzc2lvblwiKTtcbiAgfVxuICByZXR1cm4gbGVmdDtcbn07XG5cbmxwLnBhcnNlTWF5YmVDb25kaXRpb25hbCA9IGZ1bmN0aW9uIChub0luKSB7XG4gIHZhciBzdGFydCA9IHRoaXMuc3RvcmVDdXJyZW50UG9zKCk7XG4gIHZhciBleHByID0gdGhpcy5wYXJzZUV4cHJPcHMobm9Jbik7XG4gIGlmICh0aGlzLmVhdCh0dC5xdWVzdGlvbikpIHtcbiAgICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlQXQoc3RhcnQpO1xuICAgIG5vZGUudGVzdCA9IGV4cHI7XG4gICAgbm9kZS5jb25zZXF1ZW50ID0gdGhpcy5wYXJzZU1heWJlQXNzaWduKCk7XG4gICAgbm9kZS5hbHRlcm5hdGUgPSB0aGlzLmV4cGVjdCh0dC5jb2xvbikgPyB0aGlzLnBhcnNlTWF5YmVBc3NpZ24obm9JbikgOiB0aGlzLmR1bW15SWRlbnQoKTtcbiAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiQ29uZGl0aW9uYWxFeHByZXNzaW9uXCIpO1xuICB9XG4gIHJldHVybiBleHByO1xufTtcblxubHAucGFyc2VFeHByT3BzID0gZnVuY3Rpb24gKG5vSW4pIHtcbiAgdmFyIHN0YXJ0ID0gdGhpcy5zdG9yZUN1cnJlbnRQb3MoKTtcbiAgdmFyIGluZGVudCA9IHRoaXMuY3VySW5kZW50LFxuICAgICAgbGluZSA9IHRoaXMuY3VyTGluZVN0YXJ0O1xuICByZXR1cm4gdGhpcy5wYXJzZUV4cHJPcCh0aGlzLnBhcnNlTWF5YmVVbmFyeShub0luKSwgc3RhcnQsIC0xLCBub0luLCBpbmRlbnQsIGxpbmUpO1xufTtcblxubHAucGFyc2VFeHByT3AgPSBmdW5jdGlvbiAobGVmdCwgc3RhcnQsIG1pblByZWMsIG5vSW4sIGluZGVudCwgbGluZSkge1xuICBpZiAodGhpcy5jdXJMaW5lU3RhcnQgIT0gbGluZSAmJiB0aGlzLmN1ckluZGVudCA8IGluZGVudCAmJiB0aGlzLnRva2VuU3RhcnRzTGluZSgpKSByZXR1cm4gbGVmdDtcbiAgdmFyIHByZWMgPSB0aGlzLnRvay50eXBlLmJpbm9wO1xuICBpZiAocHJlYyAhPSBudWxsICYmICghbm9JbiB8fCB0aGlzLnRvay50eXBlICE9PSB0dC5faW4pKSB7XG4gICAgaWYgKHByZWMgPiBtaW5QcmVjKSB7XG4gICAgICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlQXQoc3RhcnQpO1xuICAgICAgbm9kZS5sZWZ0ID0gbGVmdDtcbiAgICAgIG5vZGUub3BlcmF0b3IgPSB0aGlzLnRvay52YWx1ZTtcbiAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgaWYgKHRoaXMuY3VyTGluZVN0YXJ0ICE9IGxpbmUgJiYgdGhpcy5jdXJJbmRlbnQgPCBpbmRlbnQgJiYgdGhpcy50b2tlblN0YXJ0c0xpbmUoKSkge1xuICAgICAgICBub2RlLnJpZ2h0ID0gdGhpcy5kdW1teUlkZW50KCk7XG4gICAgICB9IGVsc2Uge1xuICAgICAgICB2YXIgcmlnaHRTdGFydCA9IHRoaXMuc3RvcmVDdXJyZW50UG9zKCk7XG4gICAgICAgIG5vZGUucmlnaHQgPSB0aGlzLnBhcnNlRXhwck9wKHRoaXMucGFyc2VNYXliZVVuYXJ5KG5vSW4pLCByaWdodFN0YXJ0LCBwcmVjLCBub0luLCBpbmRlbnQsIGxpbmUpO1xuICAgICAgfVxuICAgICAgdGhpcy5maW5pc2hOb2RlKG5vZGUsIC8mJnxcXHxcXHwvLnRlc3Qobm9kZS5vcGVyYXRvcikgPyBcIkxvZ2ljYWxFeHByZXNzaW9uXCIgOiBcIkJpbmFyeUV4cHJlc3Npb25cIik7XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZUV4cHJPcChub2RlLCBzdGFydCwgbWluUHJlYywgbm9JbiwgaW5kZW50LCBsaW5lKTtcbiAgICB9XG4gIH1cbiAgcmV0dXJuIGxlZnQ7XG59O1xuXG5scC5wYXJzZU1heWJlVW5hcnkgPSBmdW5jdGlvbiAobm9Jbikge1xuICBpZiAodGhpcy50b2sudHlwZS5wcmVmaXgpIHtcbiAgICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCksXG4gICAgICAgIHVwZGF0ZSA9IHRoaXMudG9rLnR5cGUgPT09IHR0LmluY0RlYztcbiAgICBub2RlLm9wZXJhdG9yID0gdGhpcy50b2sudmFsdWU7XG4gICAgbm9kZS5wcmVmaXggPSB0cnVlO1xuICAgIHRoaXMubmV4dCgpO1xuICAgIG5vZGUuYXJndW1lbnQgPSB0aGlzLnBhcnNlTWF5YmVVbmFyeShub0luKTtcbiAgICBpZiAodXBkYXRlKSBub2RlLmFyZ3VtZW50ID0gdGhpcy5jaGVja0xWYWwobm9kZS5hcmd1bWVudCk7XG4gICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCB1cGRhdGUgPyBcIlVwZGF0ZUV4cHJlc3Npb25cIiA6IFwiVW5hcnlFeHByZXNzaW9uXCIpO1xuICB9IGVsc2UgaWYgKHRoaXMudG9rLnR5cGUgPT09IHR0LmVsbGlwc2lzKSB7XG4gICAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICAgIHRoaXMubmV4dCgpO1xuICAgIG5vZGUuYXJndW1lbnQgPSB0aGlzLnBhcnNlTWF5YmVVbmFyeShub0luKTtcbiAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiU3ByZWFkRWxlbWVudFwiKTtcbiAgfVxuICB2YXIgc3RhcnQgPSB0aGlzLnN0b3JlQ3VycmVudFBvcygpO1xuICB2YXIgZXhwciA9IHRoaXMucGFyc2VFeHByU3Vic2NyaXB0cygpO1xuICB3aGlsZSAodGhpcy50b2sudHlwZS5wb3N0Zml4ICYmICF0aGlzLmNhbkluc2VydFNlbWljb2xvbigpKSB7XG4gICAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0KTtcbiAgICBub2RlLm9wZXJhdG9yID0gdGhpcy50b2sudmFsdWU7XG4gICAgbm9kZS5wcmVmaXggPSBmYWxzZTtcbiAgICBub2RlLmFyZ3VtZW50ID0gdGhpcy5jaGVja0xWYWwoZXhwcik7XG4gICAgdGhpcy5uZXh0KCk7XG4gICAgZXhwciA9IHRoaXMuZmluaXNoTm9kZShub2RlLCBcIlVwZGF0ZUV4cHJlc3Npb25cIik7XG4gIH1cbiAgcmV0dXJuIGV4cHI7XG59O1xuXG5scC5wYXJzZUV4cHJTdWJzY3JpcHRzID0gZnVuY3Rpb24gKCkge1xuICB2YXIgc3RhcnQgPSB0aGlzLnN0b3JlQ3VycmVudFBvcygpO1xuICByZXR1cm4gdGhpcy5wYXJzZVN1YnNjcmlwdHModGhpcy5wYXJzZUV4cHJBdG9tKCksIHN0YXJ0LCBmYWxzZSwgdGhpcy5jdXJJbmRlbnQsIHRoaXMuY3VyTGluZVN0YXJ0KTtcbn07XG5cbmxwLnBhcnNlU3Vic2NyaXB0cyA9IGZ1bmN0aW9uIChiYXNlLCBzdGFydCwgbm9DYWxscywgc3RhcnRJbmRlbnQsIGxpbmUpIHtcbiAgZm9yICg7Oykge1xuICAgIGlmICh0aGlzLmN1ckxpbmVTdGFydCAhPSBsaW5lICYmIHRoaXMuY3VySW5kZW50IDw9IHN0YXJ0SW5kZW50ICYmIHRoaXMudG9rZW5TdGFydHNMaW5lKCkpIHtcbiAgICAgIGlmICh0aGlzLnRvay50eXBlID09IHR0LmRvdCAmJiB0aGlzLmN1ckluZGVudCA9PSBzdGFydEluZGVudCkgLS1zdGFydEluZGVudDtlbHNlIHJldHVybiBiYXNlO1xuICAgIH1cblxuICAgIGlmICh0aGlzLmVhdCh0dC5kb3QpKSB7XG4gICAgICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlQXQoc3RhcnQpO1xuICAgICAgbm9kZS5vYmplY3QgPSBiYXNlO1xuICAgICAgaWYgKHRoaXMuY3VyTGluZVN0YXJ0ICE9IGxpbmUgJiYgdGhpcy5jdXJJbmRlbnQgPD0gc3RhcnRJbmRlbnQgJiYgdGhpcy50b2tlblN0YXJ0c0xpbmUoKSkgbm9kZS5wcm9wZXJ0eSA9IHRoaXMuZHVtbXlJZGVudCgpO2Vsc2Ugbm9kZS5wcm9wZXJ0eSA9IHRoaXMucGFyc2VQcm9wZXJ0eUFjY2Vzc29yKCkgfHwgdGhpcy5kdW1teUlkZW50KCk7XG4gICAgICBub2RlLmNvbXB1dGVkID0gZmFsc2U7XG4gICAgICBiYXNlID0gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiTWVtYmVyRXhwcmVzc2lvblwiKTtcbiAgICB9IGVsc2UgaWYgKHRoaXMudG9rLnR5cGUgPT0gdHQuYnJhY2tldEwpIHtcbiAgICAgIHRoaXMucHVzaEN4KCk7XG4gICAgICB0aGlzLm5leHQoKTtcbiAgICAgIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGVBdChzdGFydCk7XG4gICAgICBub2RlLm9iamVjdCA9IGJhc2U7XG4gICAgICBub2RlLnByb3BlcnR5ID0gdGhpcy5wYXJzZUV4cHJlc3Npb24oKTtcbiAgICAgIG5vZGUuY29tcHV0ZWQgPSB0cnVlO1xuICAgICAgdGhpcy5wb3BDeCgpO1xuICAgICAgdGhpcy5leHBlY3QodHQuYnJhY2tldFIpO1xuICAgICAgYmFzZSA9IHRoaXMuZmluaXNoTm9kZShub2RlLCBcIk1lbWJlckV4cHJlc3Npb25cIik7XG4gICAgfSBlbHNlIGlmICghbm9DYWxscyAmJiB0aGlzLnRvay50eXBlID09IHR0LnBhcmVuTCkge1xuICAgICAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0KTtcbiAgICAgIG5vZGUuY2FsbGVlID0gYmFzZTtcbiAgICAgIG5vZGUuYXJndW1lbnRzID0gdGhpcy5wYXJzZUV4cHJMaXN0KHR0LnBhcmVuUik7XG4gICAgICBiYXNlID0gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiQ2FsbEV4cHJlc3Npb25cIik7XG4gICAgfSBlbHNlIGlmICh0aGlzLnRvay50eXBlID09IHR0LmJhY2tRdW90ZSkge1xuICAgICAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0KTtcbiAgICAgIG5vZGUudGFnID0gYmFzZTtcbiAgICAgIG5vZGUucXVhc2kgPSB0aGlzLnBhcnNlVGVtcGxhdGUoKTtcbiAgICAgIGJhc2UgPSB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJUYWdnZWRUZW1wbGF0ZUV4cHJlc3Npb25cIik7XG4gICAgfSBlbHNlIHtcbiAgICAgIHJldHVybiBiYXNlO1xuICAgIH1cbiAgfVxufTtcblxubHAucGFyc2VFeHByQXRvbSA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIG5vZGUgPSB1bmRlZmluZWQ7XG4gIHN3aXRjaCAodGhpcy50b2sudHlwZSkge1xuICAgIGNhc2UgdHQuX3RoaXM6XG4gICAgY2FzZSB0dC5fc3VwZXI6XG4gICAgICB2YXIgdHlwZSA9IHRoaXMudG9rLnR5cGUgPT09IHR0Ll90aGlzID8gXCJUaGlzRXhwcmVzc2lvblwiIDogXCJTdXBlclwiO1xuICAgICAgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gICAgICB0aGlzLm5leHQoKTtcbiAgICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgdHlwZSk7XG5cbiAgICBjYXNlIHR0Lm5hbWU6XG4gICAgICB2YXIgc3RhcnQgPSB0aGlzLnN0b3JlQ3VycmVudFBvcygpO1xuICAgICAgdmFyIGlkID0gdGhpcy5wYXJzZUlkZW50KCk7XG4gICAgICByZXR1cm4gdGhpcy5lYXQodHQuYXJyb3cpID8gdGhpcy5wYXJzZUFycm93RXhwcmVzc2lvbih0aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0KSwgW2lkXSkgOiBpZDtcblxuICAgIGNhc2UgdHQucmVnZXhwOlxuICAgICAgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gICAgICB2YXIgdmFsID0gdGhpcy50b2sudmFsdWU7XG4gICAgICBub2RlLnJlZ2V4ID0geyBwYXR0ZXJuOiB2YWwucGF0dGVybiwgZmxhZ3M6IHZhbC5mbGFncyB9O1xuICAgICAgbm9kZS52YWx1ZSA9IHZhbC52YWx1ZTtcbiAgICAgIG5vZGUucmF3ID0gdGhpcy5pbnB1dC5zbGljZSh0aGlzLnRvay5zdGFydCwgdGhpcy50b2suZW5kKTtcbiAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkxpdGVyYWxcIik7XG5cbiAgICBjYXNlIHR0Lm51bTpjYXNlIHR0LnN0cmluZzpcbiAgICAgIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICAgICAgbm9kZS52YWx1ZSA9IHRoaXMudG9rLnZhbHVlO1xuICAgICAgbm9kZS5yYXcgPSB0aGlzLmlucHV0LnNsaWNlKHRoaXMudG9rLnN0YXJ0LCB0aGlzLnRvay5lbmQpO1xuICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiTGl0ZXJhbFwiKTtcblxuICAgIGNhc2UgdHQuX251bGw6Y2FzZSB0dC5fdHJ1ZTpjYXNlIHR0Ll9mYWxzZTpcbiAgICAgIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICAgICAgbm9kZS52YWx1ZSA9IHRoaXMudG9rLnR5cGUgPT09IHR0Ll9udWxsID8gbnVsbCA6IHRoaXMudG9rLnR5cGUgPT09IHR0Ll90cnVlO1xuICAgICAgbm9kZS5yYXcgPSB0aGlzLnRvay50eXBlLmtleXdvcmQ7XG4gICAgICB0aGlzLm5leHQoKTtcbiAgICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJMaXRlcmFsXCIpO1xuXG4gICAgY2FzZSB0dC5wYXJlbkw6XG4gICAgICB2YXIgcGFyZW5TdGFydCA9IHRoaXMuc3RvcmVDdXJyZW50UG9zKCk7XG4gICAgICB0aGlzLm5leHQoKTtcbiAgICAgIHZhciBpbm5lciA9IHRoaXMucGFyc2VFeHByZXNzaW9uKCk7XG4gICAgICB0aGlzLmV4cGVjdCh0dC5wYXJlblIpO1xuICAgICAgaWYgKHRoaXMuZWF0KHR0LmFycm93KSkge1xuICAgICAgICByZXR1cm4gdGhpcy5wYXJzZUFycm93RXhwcmVzc2lvbih0aGlzLnN0YXJ0Tm9kZUF0KHBhcmVuU3RhcnQpLCBpbm5lci5leHByZXNzaW9ucyB8fCAoaXNEdW1teShpbm5lcikgPyBbXSA6IFtpbm5lcl0pKTtcbiAgICAgIH1cbiAgICAgIGlmICh0aGlzLm9wdGlvbnMucHJlc2VydmVQYXJlbnMpIHtcbiAgICAgICAgdmFyIHBhciA9IHRoaXMuc3RhcnROb2RlQXQocGFyZW5TdGFydCk7XG4gICAgICAgIHBhci5leHByZXNzaW9uID0gaW5uZXI7XG4gICAgICAgIGlubmVyID0gdGhpcy5maW5pc2hOb2RlKHBhciwgXCJQYXJlbnRoZXNpemVkRXhwcmVzc2lvblwiKTtcbiAgICAgIH1cbiAgICAgIHJldHVybiBpbm5lcjtcblxuICAgIGNhc2UgdHQuYnJhY2tldEw6XG4gICAgICBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgICAgIG5vZGUuZWxlbWVudHMgPSB0aGlzLnBhcnNlRXhwckxpc3QodHQuYnJhY2tldFIsIHRydWUpO1xuICAgICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkFycmF5RXhwcmVzc2lvblwiKTtcblxuICAgIGNhc2UgdHQuYnJhY2VMOlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VPYmooKTtcblxuICAgIGNhc2UgdHQuX2NsYXNzOlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VDbGFzcygpO1xuXG4gICAgY2FzZSB0dC5fZnVuY3Rpb246XG4gICAgICBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgcmV0dXJuIHRoaXMucGFyc2VGdW5jdGlvbihub2RlLCBmYWxzZSk7XG5cbiAgICBjYXNlIHR0Ll9uZXc6XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZU5ldygpO1xuXG4gICAgY2FzZSB0dC5feWllbGQ6XG4gICAgICBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgaWYgKHRoaXMuc2VtaWNvbG9uKCkgfHwgdGhpcy5jYW5JbnNlcnRTZW1pY29sb24oKSB8fCB0aGlzLnRvay50eXBlICE9IHR0LnN0YXIgJiYgIXRoaXMudG9rLnR5cGUuc3RhcnRzRXhwcikge1xuICAgICAgICBub2RlLmRlbGVnYXRlID0gZmFsc2U7XG4gICAgICAgIG5vZGUuYXJndW1lbnQgPSBudWxsO1xuICAgICAgfSBlbHNlIHtcbiAgICAgICAgbm9kZS5kZWxlZ2F0ZSA9IHRoaXMuZWF0KHR0LnN0YXIpO1xuICAgICAgICBub2RlLmFyZ3VtZW50ID0gdGhpcy5wYXJzZU1heWJlQXNzaWduKCk7XG4gICAgICB9XG4gICAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiWWllbGRFeHByZXNzaW9uXCIpO1xuXG4gICAgY2FzZSB0dC5iYWNrUXVvdGU6XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZVRlbXBsYXRlKCk7XG5cbiAgICBkZWZhdWx0OlxuICAgICAgcmV0dXJuIHRoaXMuZHVtbXlJZGVudCgpO1xuICB9XG59O1xuXG5scC5wYXJzZU5ldyA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpLFxuICAgICAgc3RhcnRJbmRlbnQgPSB0aGlzLmN1ckluZGVudCxcbiAgICAgIGxpbmUgPSB0aGlzLmN1ckxpbmVTdGFydDtcbiAgdmFyIG1ldGEgPSB0aGlzLnBhcnNlSWRlbnQodHJ1ZSk7XG4gIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNiAmJiB0aGlzLmVhdCh0dC5kb3QpKSB7XG4gICAgbm9kZS5tZXRhID0gbWV0YTtcbiAgICBub2RlLnByb3BlcnR5ID0gdGhpcy5wYXJzZUlkZW50KHRydWUpO1xuICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJNZXRhUHJvcGVydHlcIik7XG4gIH1cbiAgdmFyIHN0YXJ0ID0gdGhpcy5zdG9yZUN1cnJlbnRQb3MoKTtcbiAgbm9kZS5jYWxsZWUgPSB0aGlzLnBhcnNlU3Vic2NyaXB0cyh0aGlzLnBhcnNlRXhwckF0b20oKSwgc3RhcnQsIHRydWUsIHN0YXJ0SW5kZW50LCBsaW5lKTtcbiAgaWYgKHRoaXMudG9rLnR5cGUgPT0gdHQucGFyZW5MKSB7XG4gICAgbm9kZS5hcmd1bWVudHMgPSB0aGlzLnBhcnNlRXhwckxpc3QodHQucGFyZW5SKTtcbiAgfSBlbHNlIHtcbiAgICBub2RlLmFyZ3VtZW50cyA9IFtdO1xuICB9XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJOZXdFeHByZXNzaW9uXCIpO1xufTtcblxubHAucGFyc2VUZW1wbGF0ZUVsZW1lbnQgPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBlbGVtID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgZWxlbS52YWx1ZSA9IHtcbiAgICByYXc6IHRoaXMuaW5wdXQuc2xpY2UodGhpcy50b2suc3RhcnQsIHRoaXMudG9rLmVuZCksXG4gICAgY29va2VkOiB0aGlzLnRvay52YWx1ZVxuICB9O1xuICB0aGlzLm5leHQoKTtcbiAgZWxlbS50YWlsID0gdGhpcy50b2sudHlwZSA9PT0gdHQuYmFja1F1b3RlO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKGVsZW0sIFwiVGVtcGxhdGVFbGVtZW50XCIpO1xufTtcblxubHAucGFyc2VUZW1wbGF0ZSA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICB0aGlzLm5leHQoKTtcbiAgbm9kZS5leHByZXNzaW9ucyA9IFtdO1xuICB2YXIgY3VyRWx0ID0gdGhpcy5wYXJzZVRlbXBsYXRlRWxlbWVudCgpO1xuICBub2RlLnF1YXNpcyA9IFtjdXJFbHRdO1xuICB3aGlsZSAoIWN1ckVsdC50YWlsKSB7XG4gICAgdGhpcy5uZXh0KCk7XG4gICAgbm9kZS5leHByZXNzaW9ucy5wdXNoKHRoaXMucGFyc2VFeHByZXNzaW9uKCkpO1xuICAgIGlmICh0aGlzLmV4cGVjdCh0dC5icmFjZVIpKSB7XG4gICAgICBjdXJFbHQgPSB0aGlzLnBhcnNlVGVtcGxhdGVFbGVtZW50KCk7XG4gICAgfSBlbHNlIHtcbiAgICAgIGN1ckVsdCA9IHRoaXMuc3RhcnROb2RlKCk7XG4gICAgICBjdXJFbHQudmFsdWUgPSB7IGNvb2tlZDogXCJcIiwgcmF3OiBcIlwiIH07XG4gICAgICBjdXJFbHQudGFpbCA9IHRydWU7XG4gICAgfVxuICAgIG5vZGUucXVhc2lzLnB1c2goY3VyRWx0KTtcbiAgfVxuICB0aGlzLmV4cGVjdCh0dC5iYWNrUXVvdGUpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiVGVtcGxhdGVMaXRlcmFsXCIpO1xufTtcblxubHAucGFyc2VPYmogPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgbm9kZS5wcm9wZXJ0aWVzID0gW107XG4gIHRoaXMucHVzaEN4KCk7XG4gIHZhciBpbmRlbnQgPSB0aGlzLmN1ckluZGVudCArIDEsXG4gICAgICBsaW5lID0gdGhpcy5jdXJMaW5lU3RhcnQ7XG4gIHRoaXMuZWF0KHR0LmJyYWNlTCk7XG4gIGlmICh0aGlzLmN1ckluZGVudCArIDEgPCBpbmRlbnQpIHtcbiAgICBpbmRlbnQgPSB0aGlzLmN1ckluZGVudDtsaW5lID0gdGhpcy5jdXJMaW5lU3RhcnQ7XG4gIH1cbiAgd2hpbGUgKCF0aGlzLmNsb3Nlcyh0dC5icmFjZVIsIGluZGVudCwgbGluZSkpIHtcbiAgICB2YXIgcHJvcCA9IHRoaXMuc3RhcnROb2RlKCksXG4gICAgICAgIGlzR2VuZXJhdG9yID0gdW5kZWZpbmVkLFxuICAgICAgICBzdGFydCA9IHVuZGVmaW5lZDtcbiAgICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYpIHtcbiAgICAgIHN0YXJ0ID0gdGhpcy5zdG9yZUN1cnJlbnRQb3MoKTtcbiAgICAgIHByb3AubWV0aG9kID0gZmFsc2U7XG4gICAgICBwcm9wLnNob3J0aGFuZCA9IGZhbHNlO1xuICAgICAgaXNHZW5lcmF0b3IgPSB0aGlzLmVhdCh0dC5zdGFyKTtcbiAgICB9XG4gICAgdGhpcy5wYXJzZVByb3BlcnR5TmFtZShwcm9wKTtcbiAgICBpZiAoaXNEdW1teShwcm9wLmtleSkpIHtcbiAgICAgIGlmIChpc0R1bW15KHRoaXMucGFyc2VNYXliZUFzc2lnbigpKSkgdGhpcy5uZXh0KCk7dGhpcy5lYXQodHQuY29tbWEpO2NvbnRpbnVlO1xuICAgIH1cbiAgICBpZiAodGhpcy5lYXQodHQuY29sb24pKSB7XG4gICAgICBwcm9wLmtpbmQgPSBcImluaXRcIjtcbiAgICAgIHByb3AudmFsdWUgPSB0aGlzLnBhcnNlTWF5YmVBc3NpZ24oKTtcbiAgICB9IGVsc2UgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2ICYmICh0aGlzLnRvay50eXBlID09PSB0dC5wYXJlbkwgfHwgdGhpcy50b2sudHlwZSA9PT0gdHQuYnJhY2VMKSkge1xuICAgICAgcHJvcC5raW5kID0gXCJpbml0XCI7XG4gICAgICBwcm9wLm1ldGhvZCA9IHRydWU7XG4gICAgICBwcm9wLnZhbHVlID0gdGhpcy5wYXJzZU1ldGhvZChpc0dlbmVyYXRvcik7XG4gICAgfSBlbHNlIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNSAmJiBwcm9wLmtleS50eXBlID09PSBcIklkZW50aWZpZXJcIiAmJiAhcHJvcC5jb21wdXRlZCAmJiAocHJvcC5rZXkubmFtZSA9PT0gXCJnZXRcIiB8fCBwcm9wLmtleS5uYW1lID09PSBcInNldFwiKSAmJiAodGhpcy50b2sudHlwZSAhPSB0dC5jb21tYSAmJiB0aGlzLnRvay50eXBlICE9IHR0LmJyYWNlUikpIHtcbiAgICAgIHByb3Aua2luZCA9IHByb3Aua2V5Lm5hbWU7XG4gICAgICB0aGlzLnBhcnNlUHJvcGVydHlOYW1lKHByb3ApO1xuICAgICAgcHJvcC52YWx1ZSA9IHRoaXMucGFyc2VNZXRob2QoZmFsc2UpO1xuICAgIH0gZWxzZSB7XG4gICAgICBwcm9wLmtpbmQgPSBcImluaXRcIjtcbiAgICAgIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNikge1xuICAgICAgICBpZiAodGhpcy5lYXQodHQuZXEpKSB7XG4gICAgICAgICAgdmFyIGFzc2lnbiA9IHRoaXMuc3RhcnROb2RlQXQoc3RhcnQpO1xuICAgICAgICAgIGFzc2lnbi5vcGVyYXRvciA9IFwiPVwiO1xuICAgICAgICAgIGFzc2lnbi5sZWZ0ID0gcHJvcC5rZXk7XG4gICAgICAgICAgYXNzaWduLnJpZ2h0ID0gdGhpcy5wYXJzZU1heWJlQXNzaWduKCk7XG4gICAgICAgICAgcHJvcC52YWx1ZSA9IHRoaXMuZmluaXNoTm9kZShhc3NpZ24sIFwiQXNzaWdubWVudEV4cHJlc3Npb25cIik7XG4gICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgcHJvcC52YWx1ZSA9IHByb3Aua2V5O1xuICAgICAgICB9XG4gICAgICB9IGVsc2Uge1xuICAgICAgICBwcm9wLnZhbHVlID0gdGhpcy5kdW1teUlkZW50KCk7XG4gICAgICB9XG4gICAgICBwcm9wLnNob3J0aGFuZCA9IHRydWU7XG4gICAgfVxuICAgIG5vZGUucHJvcGVydGllcy5wdXNoKHRoaXMuZmluaXNoTm9kZShwcm9wLCBcIlByb3BlcnR5XCIpKTtcbiAgICB0aGlzLmVhdCh0dC5jb21tYSk7XG4gIH1cbiAgdGhpcy5wb3BDeCgpO1xuICBpZiAoIXRoaXMuZWF0KHR0LmJyYWNlUikpIHtcbiAgICAvLyBJZiB0aGVyZSBpcyBubyBjbG9zaW5nIGJyYWNlLCBtYWtlIHRoZSBub2RlIHNwYW4gdG8gdGhlIHN0YXJ0XG4gICAgLy8gb2YgdGhlIG5leHQgdG9rZW4gKHRoaXMgaXMgdXNlZnVsIGZvciBUZXJuKVxuICAgIHRoaXMubGFzdC5lbmQgPSB0aGlzLnRvay5zdGFydDtcbiAgICBpZiAodGhpcy5vcHRpb25zLmxvY2F0aW9ucykgdGhpcy5sYXN0LmxvYy5lbmQgPSB0aGlzLnRvay5sb2Muc3RhcnQ7XG4gIH1cbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIk9iamVjdEV4cHJlc3Npb25cIik7XG59O1xuXG5scC5wYXJzZVByb3BlcnR5TmFtZSA9IGZ1bmN0aW9uIChwcm9wKSB7XG4gIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNikge1xuICAgIGlmICh0aGlzLmVhdCh0dC5icmFja2V0TCkpIHtcbiAgICAgIHByb3AuY29tcHV0ZWQgPSB0cnVlO1xuICAgICAgcHJvcC5rZXkgPSB0aGlzLnBhcnNlRXhwcmVzc2lvbigpO1xuICAgICAgdGhpcy5leHBlY3QodHQuYnJhY2tldFIpO1xuICAgICAgcmV0dXJuO1xuICAgIH0gZWxzZSB7XG4gICAgICBwcm9wLmNvbXB1dGVkID0gZmFsc2U7XG4gICAgfVxuICB9XG4gIHZhciBrZXkgPSB0aGlzLnRvay50eXBlID09PSB0dC5udW0gfHwgdGhpcy50b2sudHlwZSA9PT0gdHQuc3RyaW5nID8gdGhpcy5wYXJzZUV4cHJBdG9tKCkgOiB0aGlzLnBhcnNlSWRlbnQoKTtcbiAgcHJvcC5rZXkgPSBrZXkgfHwgdGhpcy5kdW1teUlkZW50KCk7XG59O1xuXG5scC5wYXJzZVByb3BlcnR5QWNjZXNzb3IgPSBmdW5jdGlvbiAoKSB7XG4gIGlmICh0aGlzLnRvay50eXBlID09PSB0dC5uYW1lIHx8IHRoaXMudG9rLnR5cGUua2V5d29yZCkgcmV0dXJuIHRoaXMucGFyc2VJZGVudCgpO1xufTtcblxubHAucGFyc2VJZGVudCA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIG5hbWUgPSB0aGlzLnRvay50eXBlID09PSB0dC5uYW1lID8gdGhpcy50b2sudmFsdWUgOiB0aGlzLnRvay50eXBlLmtleXdvcmQ7XG4gIGlmICghbmFtZSkgcmV0dXJuIHRoaXMuZHVtbXlJZGVudCgpO1xuICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gIHRoaXMubmV4dCgpO1xuICBub2RlLm5hbWUgPSBuYW1lO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiSWRlbnRpZmllclwiKTtcbn07XG5cbmxwLmluaXRGdW5jdGlvbiA9IGZ1bmN0aW9uIChub2RlKSB7XG4gIG5vZGUuaWQgPSBudWxsO1xuICBub2RlLnBhcmFtcyA9IFtdO1xuICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYpIHtcbiAgICBub2RlLmdlbmVyYXRvciA9IGZhbHNlO1xuICAgIG5vZGUuZXhwcmVzc2lvbiA9IGZhbHNlO1xuICB9XG59O1xuXG4vLyBDb252ZXJ0IGV4aXN0aW5nIGV4cHJlc3Npb24gYXRvbSB0byBhc3NpZ25hYmxlIHBhdHRlcm5cbi8vIGlmIHBvc3NpYmxlLlxuXG5scC50b0Fzc2lnbmFibGUgPSBmdW5jdGlvbiAobm9kZSwgYmluZGluZykge1xuICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYgJiYgbm9kZSkge1xuICAgIHN3aXRjaCAobm9kZS50eXBlKSB7XG4gICAgICBjYXNlIFwiT2JqZWN0RXhwcmVzc2lvblwiOlxuICAgICAgICBub2RlLnR5cGUgPSBcIk9iamVjdFBhdHRlcm5cIjtcbiAgICAgICAgdmFyIHByb3BzID0gbm9kZS5wcm9wZXJ0aWVzO1xuICAgICAgICBmb3IgKHZhciBpID0gMDsgaSA8IHByb3BzLmxlbmd0aDsgaSsrKSB7XG4gICAgICAgICAgdGhpcy50b0Fzc2lnbmFibGUocHJvcHNbaV0udmFsdWUsIGJpbmRpbmcpO1xuICAgICAgICB9YnJlYWs7XG5cbiAgICAgIGNhc2UgXCJBcnJheUV4cHJlc3Npb25cIjpcbiAgICAgICAgbm9kZS50eXBlID0gXCJBcnJheVBhdHRlcm5cIjtcbiAgICAgICAgdGhpcy50b0Fzc2lnbmFibGVMaXN0KG5vZGUuZWxlbWVudHMsIGJpbmRpbmcpO1xuICAgICAgICBicmVhaztcblxuICAgICAgY2FzZSBcIlNwcmVhZEVsZW1lbnRcIjpcbiAgICAgICAgbm9kZS50eXBlID0gXCJSZXN0RWxlbWVudFwiO1xuICAgICAgICBub2RlLmFyZ3VtZW50ID0gdGhpcy50b0Fzc2lnbmFibGUobm9kZS5hcmd1bWVudCwgYmluZGluZyk7XG4gICAgICAgIGJyZWFrO1xuXG4gICAgICBjYXNlIFwiQXNzaWdubWVudEV4cHJlc3Npb25cIjpcbiAgICAgICAgbm9kZS50eXBlID0gXCJBc3NpZ25tZW50UGF0dGVyblwiO1xuICAgICAgICBicmVhaztcbiAgICB9XG4gIH1cbiAgcmV0dXJuIHRoaXMuY2hlY2tMVmFsKG5vZGUsIGJpbmRpbmcpO1xufTtcblxubHAudG9Bc3NpZ25hYmxlTGlzdCA9IGZ1bmN0aW9uIChleHByTGlzdCwgYmluZGluZykge1xuICBmb3IgKHZhciBpID0gMDsgaSA8IGV4cHJMaXN0Lmxlbmd0aDsgaSsrKSB7XG4gICAgZXhwckxpc3RbaV0gPSB0aGlzLnRvQXNzaWduYWJsZShleHByTGlzdFtpXSwgYmluZGluZyk7XG4gIH1yZXR1cm4gZXhwckxpc3Q7XG59O1xuXG5scC5wYXJzZUZ1bmN0aW9uUGFyYW1zID0gZnVuY3Rpb24gKHBhcmFtcykge1xuICBwYXJhbXMgPSB0aGlzLnBhcnNlRXhwckxpc3QodHQucGFyZW5SKTtcbiAgcmV0dXJuIHRoaXMudG9Bc3NpZ25hYmxlTGlzdChwYXJhbXMsIHRydWUpO1xufTtcblxubHAucGFyc2VNZXRob2QgPSBmdW5jdGlvbiAoaXNHZW5lcmF0b3IpIHtcbiAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICB0aGlzLmluaXRGdW5jdGlvbihub2RlKTtcbiAgbm9kZS5wYXJhbXMgPSB0aGlzLnBhcnNlRnVuY3Rpb25QYXJhbXMoKTtcbiAgbm9kZS5nZW5lcmF0b3IgPSBpc0dlbmVyYXRvciB8fCBmYWxzZTtcbiAgbm9kZS5leHByZXNzaW9uID0gdGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYgJiYgdGhpcy50b2sudHlwZSAhPT0gdHQuYnJhY2VMO1xuICBub2RlLmJvZHkgPSBub2RlLmV4cHJlc3Npb24gPyB0aGlzLnBhcnNlTWF5YmVBc3NpZ24oKSA6IHRoaXMucGFyc2VCbG9jaygpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiRnVuY3Rpb25FeHByZXNzaW9uXCIpO1xufTtcblxubHAucGFyc2VBcnJvd0V4cHJlc3Npb24gPSBmdW5jdGlvbiAobm9kZSwgcGFyYW1zKSB7XG4gIHRoaXMuaW5pdEZ1bmN0aW9uKG5vZGUpO1xuICBub2RlLnBhcmFtcyA9IHRoaXMudG9Bc3NpZ25hYmxlTGlzdChwYXJhbXMsIHRydWUpO1xuICBub2RlLmV4cHJlc3Npb24gPSB0aGlzLnRvay50eXBlICE9PSB0dC5icmFjZUw7XG4gIG5vZGUuYm9keSA9IG5vZGUuZXhwcmVzc2lvbiA/IHRoaXMucGFyc2VNYXliZUFzc2lnbigpIDogdGhpcy5wYXJzZUJsb2NrKCk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJBcnJvd0Z1bmN0aW9uRXhwcmVzc2lvblwiKTtcbn07XG5cbmxwLnBhcnNlRXhwckxpc3QgPSBmdW5jdGlvbiAoY2xvc2UsIGFsbG93RW1wdHkpIHtcbiAgdGhpcy5wdXNoQ3goKTtcbiAgdmFyIGluZGVudCA9IHRoaXMuY3VySW5kZW50LFxuICAgICAgbGluZSA9IHRoaXMuY3VyTGluZVN0YXJ0LFxuICAgICAgZWx0cyA9IFtdO1xuICB0aGlzLm5leHQoKTsgLy8gT3BlbmluZyBicmFja2V0XG4gIHdoaWxlICghdGhpcy5jbG9zZXMoY2xvc2UsIGluZGVudCArIDEsIGxpbmUpKSB7XG4gICAgaWYgKHRoaXMuZWF0KHR0LmNvbW1hKSkge1xuICAgICAgZWx0cy5wdXNoKGFsbG93RW1wdHkgPyBudWxsIDogdGhpcy5kdW1teUlkZW50KCkpO1xuICAgICAgY29udGludWU7XG4gICAgfVxuICAgIHZhciBlbHQgPSB0aGlzLnBhcnNlTWF5YmVBc3NpZ24oKTtcbiAgICBpZiAoaXNEdW1teShlbHQpKSB7XG4gICAgICBpZiAodGhpcy5jbG9zZXMoY2xvc2UsIGluZGVudCwgbGluZSkpIGJyZWFrO1xuICAgICAgdGhpcy5uZXh0KCk7XG4gICAgfSBlbHNlIHtcbiAgICAgIGVsdHMucHVzaChlbHQpO1xuICAgIH1cbiAgICB0aGlzLmVhdCh0dC5jb21tYSk7XG4gIH1cbiAgdGhpcy5wb3BDeCgpO1xuICBpZiAoIXRoaXMuZWF0KGNsb3NlKSkge1xuICAgIC8vIElmIHRoZXJlIGlzIG5vIGNsb3NpbmcgYnJhY2UsIG1ha2UgdGhlIG5vZGUgc3BhbiB0byB0aGUgc3RhcnRcbiAgICAvLyBvZiB0aGUgbmV4dCB0b2tlbiAodGhpcyBpcyB1c2VmdWwgZm9yIFRlcm4pXG4gICAgdGhpcy5sYXN0LmVuZCA9IHRoaXMudG9rLnN0YXJ0O1xuICAgIGlmICh0aGlzLm9wdGlvbnMubG9jYXRpb25zKSB0aGlzLmxhc3QubG9jLmVuZCA9IHRoaXMudG9rLmxvYy5zdGFydDtcbiAgfVxuICByZXR1cm4gZWx0cztcbn07XG5cbn0se1wiLi5cIjozLFwiLi9wYXJzZXV0aWxcIjo1LFwiLi9zdGF0ZVwiOjZ9XSw1OltmdW5jdGlvbihfZGVyZXFfLG1vZHVsZSxleHBvcnRzKXtcblwidXNlIHN0cmljdFwiO1xuXG5leHBvcnRzLmlzRHVtbXkgPSBpc0R1bW15O1xuZXhwb3J0cy5fX2VzTW9kdWxlID0gdHJ1ZTtcblxudmFyIExvb3NlUGFyc2VyID0gX2RlcmVxXyhcIi4vc3RhdGVcIikuTG9vc2VQYXJzZXI7XG5cbnZhciBfID0gX2RlcmVxXyhcIi4uXCIpO1xuXG52YXIgTm9kZSA9IF8uTm9kZTtcbnZhciBTb3VyY2VMb2NhdGlvbiA9IF8uU291cmNlTG9jYXRpb247XG52YXIgbGluZUJyZWFrID0gXy5saW5lQnJlYWs7XG52YXIgaXNOZXdMaW5lID0gXy5pc05ld0xpbmU7XG52YXIgdHQgPSBfLnRva1R5cGVzO1xuXG52YXIgbHAgPSBMb29zZVBhcnNlci5wcm90b3R5cGU7XG5cbmxwLnN0YXJ0Tm9kZSA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIG5vZGUgPSBuZXcgTm9kZSgpO1xuICBub2RlLnN0YXJ0ID0gdGhpcy50b2suc3RhcnQ7XG4gIGlmICh0aGlzLm9wdGlvbnMubG9jYXRpb25zKSBub2RlLmxvYyA9IG5ldyBTb3VyY2VMb2NhdGlvbih0aGlzLnRva3MsIHRoaXMudG9rLmxvYy5zdGFydCk7XG4gIGlmICh0aGlzLm9wdGlvbnMuZGlyZWN0U291cmNlRmlsZSkgbm9kZS5zb3VyY2VGaWxlID0gdGhpcy5vcHRpb25zLmRpcmVjdFNvdXJjZUZpbGU7XG4gIGlmICh0aGlzLm9wdGlvbnMucmFuZ2VzKSBub2RlLnJhbmdlID0gW3RoaXMudG9rLnN0YXJ0LCAwXTtcbiAgcmV0dXJuIG5vZGU7XG59O1xuXG5scC5zdG9yZUN1cnJlbnRQb3MgPSBmdW5jdGlvbiAoKSB7XG4gIHJldHVybiB0aGlzLm9wdGlvbnMubG9jYXRpb25zID8gW3RoaXMudG9rLnN0YXJ0LCB0aGlzLnRvay5sb2Muc3RhcnRdIDogdGhpcy50b2suc3RhcnQ7XG59O1xuXG5scC5zdGFydE5vZGVBdCA9IGZ1bmN0aW9uIChwb3MpIHtcbiAgdmFyIG5vZGUgPSBuZXcgTm9kZSgpO1xuICBpZiAodGhpcy5vcHRpb25zLmxvY2F0aW9ucykge1xuICAgIG5vZGUuc3RhcnQgPSBwb3NbMF07XG4gICAgbm9kZS5sb2MgPSBuZXcgU291cmNlTG9jYXRpb24odGhpcy50b2tzLCBwb3NbMV0pO1xuICAgIHBvcyA9IHBvc1swXTtcbiAgfSBlbHNlIHtcbiAgICBub2RlLnN0YXJ0ID0gcG9zO1xuICB9XG4gIGlmICh0aGlzLm9wdGlvbnMuZGlyZWN0U291cmNlRmlsZSkgbm9kZS5zb3VyY2VGaWxlID0gdGhpcy5vcHRpb25zLmRpcmVjdFNvdXJjZUZpbGU7XG4gIGlmICh0aGlzLm9wdGlvbnMucmFuZ2VzKSBub2RlLnJhbmdlID0gW3BvcywgMF07XG4gIHJldHVybiBub2RlO1xufTtcblxubHAuZmluaXNoTm9kZSA9IGZ1bmN0aW9uIChub2RlLCB0eXBlKSB7XG4gIG5vZGUudHlwZSA9IHR5cGU7XG4gIG5vZGUuZW5kID0gdGhpcy5sYXN0LmVuZDtcbiAgaWYgKHRoaXMub3B0aW9ucy5sb2NhdGlvbnMpIG5vZGUubG9jLmVuZCA9IHRoaXMubGFzdC5sb2MuZW5kO1xuICBpZiAodGhpcy5vcHRpb25zLnJhbmdlcykgbm9kZS5yYW5nZVsxXSA9IHRoaXMubGFzdC5lbmQ7XG4gIHJldHVybiBub2RlO1xufTtcblxubHAuZHVtbXlJZGVudCA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIGR1bW15ID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgZHVtbXkubmFtZSA9IFwi4pyWXCI7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUoZHVtbXksIFwiSWRlbnRpZmllclwiKTtcbn07XG5cbmZ1bmN0aW9uIGlzRHVtbXkobm9kZSkge1xuICByZXR1cm4gbm9kZS5uYW1lID09IFwi4pyWXCI7XG59XG5cbmxwLmVhdCA9IGZ1bmN0aW9uICh0eXBlKSB7XG4gIGlmICh0aGlzLnRvay50eXBlID09PSB0eXBlKSB7XG4gICAgdGhpcy5uZXh0KCk7XG4gICAgcmV0dXJuIHRydWU7XG4gIH0gZWxzZSB7XG4gICAgcmV0dXJuIGZhbHNlO1xuICB9XG59O1xuXG5scC5pc0NvbnRleHR1YWwgPSBmdW5jdGlvbiAobmFtZSkge1xuICByZXR1cm4gdGhpcy50b2sudHlwZSA9PT0gdHQubmFtZSAmJiB0aGlzLnRvay52YWx1ZSA9PT0gbmFtZTtcbn07XG5cbmxwLmVhdENvbnRleHR1YWwgPSBmdW5jdGlvbiAobmFtZSkge1xuICByZXR1cm4gdGhpcy50b2sudmFsdWUgPT09IG5hbWUgJiYgdGhpcy5lYXQodHQubmFtZSk7XG59O1xuXG5scC5jYW5JbnNlcnRTZW1pY29sb24gPSBmdW5jdGlvbiAoKSB7XG4gIHJldHVybiB0aGlzLnRvay50eXBlID09PSB0dC5lb2YgfHwgdGhpcy50b2sudHlwZSA9PT0gdHQuYnJhY2VSIHx8IGxpbmVCcmVhay50ZXN0KHRoaXMuaW5wdXQuc2xpY2UodGhpcy5sYXN0LmVuZCwgdGhpcy50b2suc3RhcnQpKTtcbn07XG5cbmxwLnNlbWljb2xvbiA9IGZ1bmN0aW9uICgpIHtcbiAgcmV0dXJuIHRoaXMuZWF0KHR0LnNlbWkpO1xufTtcblxubHAuZXhwZWN0ID0gZnVuY3Rpb24gKHR5cGUpIHtcbiAgaWYgKHRoaXMuZWF0KHR5cGUpKSByZXR1cm4gdHJ1ZTtcbiAgZm9yICh2YXIgaSA9IDE7IGkgPD0gMjsgaSsrKSB7XG4gICAgaWYgKHRoaXMubG9va0FoZWFkKGkpLnR5cGUgPT0gdHlwZSkge1xuICAgICAgZm9yICh2YXIgaiA9IDA7IGogPCBpOyBqKyspIHtcbiAgICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICB9cmV0dXJuIHRydWU7XG4gICAgfVxuICB9XG59O1xuXG5scC5wdXNoQ3ggPSBmdW5jdGlvbiAoKSB7XG4gIHRoaXMuY29udGV4dC5wdXNoKHRoaXMuY3VySW5kZW50KTtcbn07XG5scC5wb3BDeCA9IGZ1bmN0aW9uICgpIHtcbiAgdGhpcy5jdXJJbmRlbnQgPSB0aGlzLmNvbnRleHQucG9wKCk7XG59O1xuXG5scC5saW5lRW5kID0gZnVuY3Rpb24gKHBvcykge1xuICB3aGlsZSAocG9zIDwgdGhpcy5pbnB1dC5sZW5ndGggJiYgIWlzTmV3TGluZSh0aGlzLmlucHV0LmNoYXJDb2RlQXQocG9zKSkpICsrcG9zO1xuICByZXR1cm4gcG9zO1xufTtcblxubHAuaW5kZW50YXRpb25BZnRlciA9IGZ1bmN0aW9uIChwb3MpIHtcbiAgZm9yICh2YXIgY291bnQgPSAwOzsgKytwb3MpIHtcbiAgICB2YXIgY2ggPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQocG9zKTtcbiAgICBpZiAoY2ggPT09IDMyKSArK2NvdW50O2Vsc2UgaWYgKGNoID09PSA5KSBjb3VudCArPSB0aGlzLm9wdGlvbnMudGFiU2l6ZTtlbHNlIHJldHVybiBjb3VudDtcbiAgfVxufTtcblxubHAuY2xvc2VzID0gZnVuY3Rpb24gKGNsb3NlVG9rLCBpbmRlbnQsIGxpbmUsIGJsb2NrSGV1cmlzdGljKSB7XG4gIGlmICh0aGlzLnRvay50eXBlID09PSBjbG9zZVRvayB8fCB0aGlzLnRvay50eXBlID09PSB0dC5lb2YpIHJldHVybiB0cnVlO1xuICByZXR1cm4gbGluZSAhPSB0aGlzLmN1ckxpbmVTdGFydCAmJiB0aGlzLmN1ckluZGVudCA8IGluZGVudCAmJiB0aGlzLnRva2VuU3RhcnRzTGluZSgpICYmICghYmxvY2tIZXVyaXN0aWMgfHwgdGhpcy5uZXh0TGluZVN0YXJ0ID49IHRoaXMuaW5wdXQubGVuZ3RoIHx8IHRoaXMuaW5kZW50YXRpb25BZnRlcih0aGlzLm5leHRMaW5lU3RhcnQpIDwgaW5kZW50KTtcbn07XG5cbmxwLnRva2VuU3RhcnRzTGluZSA9IGZ1bmN0aW9uICgpIHtcbiAgZm9yICh2YXIgcCA9IHRoaXMudG9rLnN0YXJ0IC0gMTsgcCA+PSB0aGlzLmN1ckxpbmVTdGFydDsgLS1wKSB7XG4gICAgdmFyIGNoID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHApO1xuICAgIGlmIChjaCAhPT0gOSAmJiBjaCAhPT0gMzIpIHJldHVybiBmYWxzZTtcbiAgfVxuICByZXR1cm4gdHJ1ZTtcbn07XG5cbn0se1wiLi5cIjozLFwiLi9zdGF0ZVwiOjZ9XSw2OltmdW5jdGlvbihfZGVyZXFfLG1vZHVsZSxleHBvcnRzKXtcblwidXNlIHN0cmljdFwiO1xuXG5leHBvcnRzLkxvb3NlUGFyc2VyID0gTG9vc2VQYXJzZXI7XG5leHBvcnRzLl9fZXNNb2R1bGUgPSB0cnVlO1xuXG52YXIgXyA9IF9kZXJlcV8oXCIuLlwiKTtcblxudmFyIHRva2VuaXplciA9IF8udG9rZW5pemVyO1xudmFyIFNvdXJjZUxvY2F0aW9uID0gXy5Tb3VyY2VMb2NhdGlvbjtcbnZhciB0dCA9IF8udG9rVHlwZXM7XG5cbmZ1bmN0aW9uIExvb3NlUGFyc2VyKGlucHV0LCBvcHRpb25zKSB7XG4gIHRoaXMudG9rcyA9IHRva2VuaXplcihpbnB1dCwgb3B0aW9ucyk7XG4gIHRoaXMub3B0aW9ucyA9IHRoaXMudG9rcy5vcHRpb25zO1xuICB0aGlzLmlucHV0ID0gdGhpcy50b2tzLmlucHV0O1xuICB0aGlzLnRvayA9IHRoaXMubGFzdCA9IHsgdHlwZTogdHQuZW9mLCBzdGFydDogMCwgZW5kOiAwIH07XG4gIGlmICh0aGlzLm9wdGlvbnMubG9jYXRpb25zKSB7XG4gICAgdmFyIGhlcmUgPSB0aGlzLnRva3MuY3VyUG9zaXRpb24oKTtcbiAgICB0aGlzLnRvay5sb2MgPSBuZXcgU291cmNlTG9jYXRpb24odGhpcy50b2tzLCBoZXJlLCBoZXJlKTtcbiAgfVxuICB0aGlzLmFoZWFkID0gW107IC8vIFRva2VucyBhaGVhZFxuICB0aGlzLmNvbnRleHQgPSBbXTsgLy8gSW5kZW50YXRpb24gY29udGV4dGVkXG4gIHRoaXMuY3VySW5kZW50ID0gMDtcbiAgdGhpcy5jdXJMaW5lU3RhcnQgPSAwO1xuICB0aGlzLm5leHRMaW5lU3RhcnQgPSB0aGlzLmxpbmVFbmQodGhpcy5jdXJMaW5lU3RhcnQpICsgMTtcbn1cblxufSx7XCIuLlwiOjN9XSw3OltmdW5jdGlvbihfZGVyZXFfLG1vZHVsZSxleHBvcnRzKXtcblwidXNlIHN0cmljdFwiO1xuXG52YXIgTG9vc2VQYXJzZXIgPSBfZGVyZXFfKFwiLi9zdGF0ZVwiKS5Mb29zZVBhcnNlcjtcblxudmFyIGlzRHVtbXkgPSBfZGVyZXFfKFwiLi9wYXJzZXV0aWxcIikuaXNEdW1teTtcblxudmFyIF8gPSBfZGVyZXFfKFwiLi5cIik7XG5cbnZhciBnZXRMaW5lSW5mbyA9IF8uZ2V0TGluZUluZm87XG52YXIgdHQgPSBfLnRva1R5cGVzO1xuXG52YXIgbHAgPSBMb29zZVBhcnNlci5wcm90b3R5cGU7XG5cbmxwLnBhcnNlVG9wTGV2ZWwgPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGVBdCh0aGlzLm9wdGlvbnMubG9jYXRpb25zID8gWzAsIGdldExpbmVJbmZvKHRoaXMuaW5wdXQsIDApXSA6IDApO1xuICBub2RlLmJvZHkgPSBbXTtcbiAgd2hpbGUgKHRoaXMudG9rLnR5cGUgIT09IHR0LmVvZikgbm9kZS5ib2R5LnB1c2godGhpcy5wYXJzZVN0YXRlbWVudCgpKTtcbiAgdGhpcy5sYXN0ID0gdGhpcy50b2s7XG4gIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNikge1xuICAgIG5vZGUuc291cmNlVHlwZSA9IHRoaXMub3B0aW9ucy5zb3VyY2VUeXBlO1xuICB9XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJQcm9ncmFtXCIpO1xufTtcblxubHAucGFyc2VTdGF0ZW1lbnQgPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBzdGFydHR5cGUgPSB0aGlzLnRvay50eXBlLFxuICAgICAgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG5cbiAgc3dpdGNoIChzdGFydHR5cGUpIHtcbiAgICBjYXNlIHR0Ll9icmVhazpjYXNlIHR0Ll9jb250aW51ZTpcbiAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgdmFyIGlzQnJlYWsgPSBzdGFydHR5cGUgPT09IHR0Ll9icmVhaztcbiAgICAgIGlmICh0aGlzLnNlbWljb2xvbigpIHx8IHRoaXMuY2FuSW5zZXJ0U2VtaWNvbG9uKCkpIHtcbiAgICAgICAgbm9kZS5sYWJlbCA9IG51bGw7XG4gICAgICB9IGVsc2Uge1xuICAgICAgICBub2RlLmxhYmVsID0gdGhpcy50b2sudHlwZSA9PT0gdHQubmFtZSA/IHRoaXMucGFyc2VJZGVudCgpIDogbnVsbDtcbiAgICAgICAgdGhpcy5zZW1pY29sb24oKTtcbiAgICAgIH1cbiAgICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgaXNCcmVhayA/IFwiQnJlYWtTdGF0ZW1lbnRcIiA6IFwiQ29udGludWVTdGF0ZW1lbnRcIik7XG5cbiAgICBjYXNlIHR0Ll9kZWJ1Z2dlcjpcbiAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgdGhpcy5zZW1pY29sb24oKTtcbiAgICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJEZWJ1Z2dlclN0YXRlbWVudFwiKTtcblxuICAgIGNhc2UgdHQuX2RvOlxuICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICBub2RlLmJvZHkgPSB0aGlzLnBhcnNlU3RhdGVtZW50KCk7XG4gICAgICBub2RlLnRlc3QgPSB0aGlzLmVhdCh0dC5fd2hpbGUpID8gdGhpcy5wYXJzZVBhcmVuRXhwcmVzc2lvbigpIDogdGhpcy5kdW1teUlkZW50KCk7XG4gICAgICB0aGlzLnNlbWljb2xvbigpO1xuICAgICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkRvV2hpbGVTdGF0ZW1lbnRcIik7XG5cbiAgICBjYXNlIHR0Ll9mb3I6XG4gICAgICB0aGlzLm5leHQoKTtcbiAgICAgIHRoaXMucHVzaEN4KCk7XG4gICAgICB0aGlzLmV4cGVjdCh0dC5wYXJlbkwpO1xuICAgICAgaWYgKHRoaXMudG9rLnR5cGUgPT09IHR0LnNlbWkpIHJldHVybiB0aGlzLnBhcnNlRm9yKG5vZGUsIG51bGwpO1xuICAgICAgaWYgKHRoaXMudG9rLnR5cGUgPT09IHR0Ll92YXIgfHwgdGhpcy50b2sudHlwZSA9PT0gdHQuX2xldCB8fCB0aGlzLnRvay50eXBlID09PSB0dC5fY29uc3QpIHtcbiAgICAgICAgdmFyIF9pbml0ID0gdGhpcy5wYXJzZVZhcih0cnVlKTtcbiAgICAgICAgaWYgKF9pbml0LmRlY2xhcmF0aW9ucy5sZW5ndGggPT09IDEgJiYgKHRoaXMudG9rLnR5cGUgPT09IHR0Ll9pbiB8fCB0aGlzLmlzQ29udGV4dHVhbChcIm9mXCIpKSkge1xuICAgICAgICAgIHJldHVybiB0aGlzLnBhcnNlRm9ySW4obm9kZSwgX2luaXQpO1xuICAgICAgICB9XG4gICAgICAgIHJldHVybiB0aGlzLnBhcnNlRm9yKG5vZGUsIF9pbml0KTtcbiAgICAgIH1cbiAgICAgIHZhciBpbml0ID0gdGhpcy5wYXJzZUV4cHJlc3Npb24odHJ1ZSk7XG4gICAgICBpZiAodGhpcy50b2sudHlwZSA9PT0gdHQuX2luIHx8IHRoaXMuaXNDb250ZXh0dWFsKFwib2ZcIikpIHJldHVybiB0aGlzLnBhcnNlRm9ySW4obm9kZSwgdGhpcy50b0Fzc2lnbmFibGUoaW5pdCkpO1xuICAgICAgcmV0dXJuIHRoaXMucGFyc2VGb3Iobm9kZSwgaW5pdCk7XG5cbiAgICBjYXNlIHR0Ll9mdW5jdGlvbjpcbiAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgcmV0dXJuIHRoaXMucGFyc2VGdW5jdGlvbihub2RlLCB0cnVlKTtcblxuICAgIGNhc2UgdHQuX2lmOlxuICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICBub2RlLnRlc3QgPSB0aGlzLnBhcnNlUGFyZW5FeHByZXNzaW9uKCk7XG4gICAgICBub2RlLmNvbnNlcXVlbnQgPSB0aGlzLnBhcnNlU3RhdGVtZW50KCk7XG4gICAgICBub2RlLmFsdGVybmF0ZSA9IHRoaXMuZWF0KHR0Ll9lbHNlKSA/IHRoaXMucGFyc2VTdGF0ZW1lbnQoKSA6IG51bGw7XG4gICAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiSWZTdGF0ZW1lbnRcIik7XG5cbiAgICBjYXNlIHR0Ll9yZXR1cm46XG4gICAgICB0aGlzLm5leHQoKTtcbiAgICAgIGlmICh0aGlzLmVhdCh0dC5zZW1pKSB8fCB0aGlzLmNhbkluc2VydFNlbWljb2xvbigpKSBub2RlLmFyZ3VtZW50ID0gbnVsbDtlbHNlIHtcbiAgICAgICAgbm9kZS5hcmd1bWVudCA9IHRoaXMucGFyc2VFeHByZXNzaW9uKCk7dGhpcy5zZW1pY29sb24oKTtcbiAgICAgIH1cbiAgICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJSZXR1cm5TdGF0ZW1lbnRcIik7XG5cbiAgICBjYXNlIHR0Ll9zd2l0Y2g6XG4gICAgICB2YXIgYmxvY2tJbmRlbnQgPSB0aGlzLmN1ckluZGVudCxcbiAgICAgICAgICBsaW5lID0gdGhpcy5jdXJMaW5lU3RhcnQ7XG4gICAgICB0aGlzLm5leHQoKTtcbiAgICAgIG5vZGUuZGlzY3JpbWluYW50ID0gdGhpcy5wYXJzZVBhcmVuRXhwcmVzc2lvbigpO1xuICAgICAgbm9kZS5jYXNlcyA9IFtdO1xuICAgICAgdGhpcy5wdXNoQ3goKTtcbiAgICAgIHRoaXMuZXhwZWN0KHR0LmJyYWNlTCk7XG5cbiAgICAgIHZhciBjdXIgPSB1bmRlZmluZWQ7XG4gICAgICB3aGlsZSAoIXRoaXMuY2xvc2VzKHR0LmJyYWNlUiwgYmxvY2tJbmRlbnQsIGxpbmUsIHRydWUpKSB7XG4gICAgICAgIGlmICh0aGlzLnRvay50eXBlID09PSB0dC5fY2FzZSB8fCB0aGlzLnRvay50eXBlID09PSB0dC5fZGVmYXVsdCkge1xuICAgICAgICAgIHZhciBpc0Nhc2UgPSB0aGlzLnRvay50eXBlID09PSB0dC5fY2FzZTtcbiAgICAgICAgICBpZiAoY3VyKSB0aGlzLmZpbmlzaE5vZGUoY3VyLCBcIlN3aXRjaENhc2VcIik7XG4gICAgICAgICAgbm9kZS5jYXNlcy5wdXNoKGN1ciA9IHRoaXMuc3RhcnROb2RlKCkpO1xuICAgICAgICAgIGN1ci5jb25zZXF1ZW50ID0gW107XG4gICAgICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICAgICAgaWYgKGlzQ2FzZSkgY3VyLnRlc3QgPSB0aGlzLnBhcnNlRXhwcmVzc2lvbigpO2Vsc2UgY3VyLnRlc3QgPSBudWxsO1xuICAgICAgICAgIHRoaXMuZXhwZWN0KHR0LmNvbG9uKTtcbiAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICBpZiAoIWN1cikge1xuICAgICAgICAgICAgbm9kZS5jYXNlcy5wdXNoKGN1ciA9IHRoaXMuc3RhcnROb2RlKCkpO1xuICAgICAgICAgICAgY3VyLmNvbnNlcXVlbnQgPSBbXTtcbiAgICAgICAgICAgIGN1ci50ZXN0ID0gbnVsbDtcbiAgICAgICAgICB9XG4gICAgICAgICAgY3VyLmNvbnNlcXVlbnQucHVzaCh0aGlzLnBhcnNlU3RhdGVtZW50KCkpO1xuICAgICAgICB9XG4gICAgICB9XG4gICAgICBpZiAoY3VyKSB0aGlzLmZpbmlzaE5vZGUoY3VyLCBcIlN3aXRjaENhc2VcIik7XG4gICAgICB0aGlzLnBvcEN4KCk7XG4gICAgICB0aGlzLmVhdCh0dC5icmFjZVIpO1xuICAgICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIlN3aXRjaFN0YXRlbWVudFwiKTtcblxuICAgIGNhc2UgdHQuX3Rocm93OlxuICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICBub2RlLmFyZ3VtZW50ID0gdGhpcy5wYXJzZUV4cHJlc3Npb24oKTtcbiAgICAgIHRoaXMuc2VtaWNvbG9uKCk7XG4gICAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiVGhyb3dTdGF0ZW1lbnRcIik7XG5cbiAgICBjYXNlIHR0Ll90cnk6XG4gICAgICB0aGlzLm5leHQoKTtcbiAgICAgIG5vZGUuYmxvY2sgPSB0aGlzLnBhcnNlQmxvY2soKTtcbiAgICAgIG5vZGUuaGFuZGxlciA9IG51bGw7XG4gICAgICBpZiAodGhpcy50b2sudHlwZSA9PT0gdHQuX2NhdGNoKSB7XG4gICAgICAgIHZhciBjbGF1c2UgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICAgICAgICB0aGlzLm5leHQoKTtcbiAgICAgICAgdGhpcy5leHBlY3QodHQucGFyZW5MKTtcbiAgICAgICAgY2xhdXNlLnBhcmFtID0gdGhpcy50b0Fzc2lnbmFibGUodGhpcy5wYXJzZUV4cHJBdG9tKCksIHRydWUpO1xuICAgICAgICB0aGlzLmV4cGVjdCh0dC5wYXJlblIpO1xuICAgICAgICBjbGF1c2UuZ3VhcmQgPSBudWxsO1xuICAgICAgICBjbGF1c2UuYm9keSA9IHRoaXMucGFyc2VCbG9jaygpO1xuICAgICAgICBub2RlLmhhbmRsZXIgPSB0aGlzLmZpbmlzaE5vZGUoY2xhdXNlLCBcIkNhdGNoQ2xhdXNlXCIpO1xuICAgICAgfVxuICAgICAgbm9kZS5maW5hbGl6ZXIgPSB0aGlzLmVhdCh0dC5fZmluYWxseSkgPyB0aGlzLnBhcnNlQmxvY2soKSA6IG51bGw7XG4gICAgICBpZiAoIW5vZGUuaGFuZGxlciAmJiAhbm9kZS5maW5hbGl6ZXIpIHJldHVybiBub2RlLmJsb2NrO1xuICAgICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIlRyeVN0YXRlbWVudFwiKTtcblxuICAgIGNhc2UgdHQuX3ZhcjpcbiAgICBjYXNlIHR0Ll9sZXQ6XG4gICAgY2FzZSB0dC5fY29uc3Q6XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZVZhcigpO1xuXG4gICAgY2FzZSB0dC5fd2hpbGU6XG4gICAgICB0aGlzLm5leHQoKTtcbiAgICAgIG5vZGUudGVzdCA9IHRoaXMucGFyc2VQYXJlbkV4cHJlc3Npb24oKTtcbiAgICAgIG5vZGUuYm9keSA9IHRoaXMucGFyc2VTdGF0ZW1lbnQoKTtcbiAgICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJXaGlsZVN0YXRlbWVudFwiKTtcblxuICAgIGNhc2UgdHQuX3dpdGg6XG4gICAgICB0aGlzLm5leHQoKTtcbiAgICAgIG5vZGUub2JqZWN0ID0gdGhpcy5wYXJzZVBhcmVuRXhwcmVzc2lvbigpO1xuICAgICAgbm9kZS5ib2R5ID0gdGhpcy5wYXJzZVN0YXRlbWVudCgpO1xuICAgICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIldpdGhTdGF0ZW1lbnRcIik7XG5cbiAgICBjYXNlIHR0LmJyYWNlTDpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlQmxvY2soKTtcblxuICAgIGNhc2UgdHQuc2VtaTpcbiAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkVtcHR5U3RhdGVtZW50XCIpO1xuXG4gICAgY2FzZSB0dC5fY2xhc3M6XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZUNsYXNzKHRydWUpO1xuXG4gICAgY2FzZSB0dC5faW1wb3J0OlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VJbXBvcnQoKTtcblxuICAgIGNhc2UgdHQuX2V4cG9ydDpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlRXhwb3J0KCk7XG5cbiAgICBkZWZhdWx0OlxuICAgICAgdmFyIGV4cHIgPSB0aGlzLnBhcnNlRXhwcmVzc2lvbigpO1xuICAgICAgaWYgKGlzRHVtbXkoZXhwcikpIHtcbiAgICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICAgIGlmICh0aGlzLnRvay50eXBlID09PSB0dC5lb2YpIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJFbXB0eVN0YXRlbWVudFwiKTtcbiAgICAgICAgcmV0dXJuIHRoaXMucGFyc2VTdGF0ZW1lbnQoKTtcbiAgICAgIH0gZWxzZSBpZiAoc3RhcnR0eXBlID09PSB0dC5uYW1lICYmIGV4cHIudHlwZSA9PT0gXCJJZGVudGlmaWVyXCIgJiYgdGhpcy5lYXQodHQuY29sb24pKSB7XG4gICAgICAgIG5vZGUuYm9keSA9IHRoaXMucGFyc2VTdGF0ZW1lbnQoKTtcbiAgICAgICAgbm9kZS5sYWJlbCA9IGV4cHI7XG4gICAgICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJMYWJlbGVkU3RhdGVtZW50XCIpO1xuICAgICAgfSBlbHNlIHtcbiAgICAgICAgbm9kZS5leHByZXNzaW9uID0gZXhwcjtcbiAgICAgICAgdGhpcy5zZW1pY29sb24oKTtcbiAgICAgICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkV4cHJlc3Npb25TdGF0ZW1lbnRcIik7XG4gICAgICB9XG4gIH1cbn07XG5cbmxwLnBhcnNlQmxvY2sgPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgdGhpcy5wdXNoQ3goKTtcbiAgdGhpcy5leHBlY3QodHQuYnJhY2VMKTtcbiAgdmFyIGJsb2NrSW5kZW50ID0gdGhpcy5jdXJJbmRlbnQsXG4gICAgICBsaW5lID0gdGhpcy5jdXJMaW5lU3RhcnQ7XG4gIG5vZGUuYm9keSA9IFtdO1xuICB3aGlsZSAoIXRoaXMuY2xvc2VzKHR0LmJyYWNlUiwgYmxvY2tJbmRlbnQsIGxpbmUsIHRydWUpKSBub2RlLmJvZHkucHVzaCh0aGlzLnBhcnNlU3RhdGVtZW50KCkpO1xuICB0aGlzLnBvcEN4KCk7XG4gIHRoaXMuZWF0KHR0LmJyYWNlUik7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJCbG9ja1N0YXRlbWVudFwiKTtcbn07XG5cbmxwLnBhcnNlRm9yID0gZnVuY3Rpb24gKG5vZGUsIGluaXQpIHtcbiAgbm9kZS5pbml0ID0gaW5pdDtcbiAgbm9kZS50ZXN0ID0gbm9kZS51cGRhdGUgPSBudWxsO1xuICBpZiAodGhpcy5lYXQodHQuc2VtaSkgJiYgdGhpcy50b2sudHlwZSAhPT0gdHQuc2VtaSkgbm9kZS50ZXN0ID0gdGhpcy5wYXJzZUV4cHJlc3Npb24oKTtcbiAgaWYgKHRoaXMuZWF0KHR0LnNlbWkpICYmIHRoaXMudG9rLnR5cGUgIT09IHR0LnBhcmVuUikgbm9kZS51cGRhdGUgPSB0aGlzLnBhcnNlRXhwcmVzc2lvbigpO1xuICB0aGlzLnBvcEN4KCk7XG4gIHRoaXMuZXhwZWN0KHR0LnBhcmVuUik7XG4gIG5vZGUuYm9keSA9IHRoaXMucGFyc2VTdGF0ZW1lbnQoKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkZvclN0YXRlbWVudFwiKTtcbn07XG5cbmxwLnBhcnNlRm9ySW4gPSBmdW5jdGlvbiAobm9kZSwgaW5pdCkge1xuICB2YXIgdHlwZSA9IHRoaXMudG9rLnR5cGUgPT09IHR0Ll9pbiA/IFwiRm9ySW5TdGF0ZW1lbnRcIiA6IFwiRm9yT2ZTdGF0ZW1lbnRcIjtcbiAgdGhpcy5uZXh0KCk7XG4gIG5vZGUubGVmdCA9IGluaXQ7XG4gIG5vZGUucmlnaHQgPSB0aGlzLnBhcnNlRXhwcmVzc2lvbigpO1xuICB0aGlzLnBvcEN4KCk7XG4gIHRoaXMuZXhwZWN0KHR0LnBhcmVuUik7XG4gIG5vZGUuYm9keSA9IHRoaXMucGFyc2VTdGF0ZW1lbnQoKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCB0eXBlKTtcbn07XG5cbmxwLnBhcnNlVmFyID0gZnVuY3Rpb24gKG5vSW4pIHtcbiAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICBub2RlLmtpbmQgPSB0aGlzLnRvay50eXBlLmtleXdvcmQ7XG4gIHRoaXMubmV4dCgpO1xuICBub2RlLmRlY2xhcmF0aW9ucyA9IFtdO1xuICBkbyB7XG4gICAgdmFyIGRlY2wgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICAgIGRlY2wuaWQgPSB0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNiA/IHRoaXMudG9Bc3NpZ25hYmxlKHRoaXMucGFyc2VFeHByQXRvbSgpLCB0cnVlKSA6IHRoaXMucGFyc2VJZGVudCgpO1xuICAgIGRlY2wuaW5pdCA9IHRoaXMuZWF0KHR0LmVxKSA/IHRoaXMucGFyc2VNYXliZUFzc2lnbihub0luKSA6IG51bGw7XG4gICAgbm9kZS5kZWNsYXJhdGlvbnMucHVzaCh0aGlzLmZpbmlzaE5vZGUoZGVjbCwgXCJWYXJpYWJsZURlY2xhcmF0b3JcIikpO1xuICB9IHdoaWxlICh0aGlzLmVhdCh0dC5jb21tYSkpO1xuICBpZiAoIW5vZGUuZGVjbGFyYXRpb25zLmxlbmd0aCkge1xuICAgIHZhciBkZWNsID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgICBkZWNsLmlkID0gdGhpcy5kdW1teUlkZW50KCk7XG4gICAgbm9kZS5kZWNsYXJhdGlvbnMucHVzaCh0aGlzLmZpbmlzaE5vZGUoZGVjbCwgXCJWYXJpYWJsZURlY2xhcmF0b3JcIikpO1xuICB9XG4gIGlmICghbm9JbikgdGhpcy5zZW1pY29sb24oKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIlZhcmlhYmxlRGVjbGFyYXRpb25cIik7XG59O1xuXG5scC5wYXJzZUNsYXNzID0gZnVuY3Rpb24gKGlzU3RhdGVtZW50KSB7XG4gIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgdGhpcy5uZXh0KCk7XG4gIGlmICh0aGlzLnRvay50eXBlID09PSB0dC5uYW1lKSBub2RlLmlkID0gdGhpcy5wYXJzZUlkZW50KCk7ZWxzZSBpZiAoaXNTdGF0ZW1lbnQpIG5vZGUuaWQgPSB0aGlzLmR1bW15SWRlbnQoKTtlbHNlIG5vZGUuaWQgPSBudWxsO1xuICBub2RlLnN1cGVyQ2xhc3MgPSB0aGlzLmVhdCh0dC5fZXh0ZW5kcykgPyB0aGlzLnBhcnNlRXhwcmVzc2lvbigpIDogbnVsbDtcbiAgbm9kZS5ib2R5ID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgbm9kZS5ib2R5LmJvZHkgPSBbXTtcbiAgdGhpcy5wdXNoQ3goKTtcbiAgdmFyIGluZGVudCA9IHRoaXMuY3VySW5kZW50ICsgMSxcbiAgICAgIGxpbmUgPSB0aGlzLmN1ckxpbmVTdGFydDtcbiAgdGhpcy5lYXQodHQuYnJhY2VMKTtcbiAgaWYgKHRoaXMuY3VySW5kZW50ICsgMSA8IGluZGVudCkge1xuICAgIGluZGVudCA9IHRoaXMuY3VySW5kZW50O2xpbmUgPSB0aGlzLmN1ckxpbmVTdGFydDtcbiAgfVxuICB3aGlsZSAoIXRoaXMuY2xvc2VzKHR0LmJyYWNlUiwgaW5kZW50LCBsaW5lKSkge1xuICAgIGlmICh0aGlzLnNlbWljb2xvbigpKSBjb250aW51ZTtcbiAgICB2YXIgbWV0aG9kID0gdGhpcy5zdGFydE5vZGUoKSxcbiAgICAgICAgaXNHZW5lcmF0b3IgPSB1bmRlZmluZWQ7XG4gICAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KSB7XG4gICAgICBtZXRob2RbXCJzdGF0aWNcIl0gPSBmYWxzZTtcbiAgICAgIGlzR2VuZXJhdG9yID0gdGhpcy5lYXQodHQuc3Rhcik7XG4gICAgfVxuICAgIHRoaXMucGFyc2VQcm9wZXJ0eU5hbWUobWV0aG9kKTtcbiAgICBpZiAoaXNEdW1teShtZXRob2Qua2V5KSkge1xuICAgICAgaWYgKGlzRHVtbXkodGhpcy5wYXJzZU1heWJlQXNzaWduKCkpKSB0aGlzLm5leHQoKTt0aGlzLmVhdCh0dC5jb21tYSk7Y29udGludWU7XG4gICAgfVxuICAgIGlmIChtZXRob2Qua2V5LnR5cGUgPT09IFwiSWRlbnRpZmllclwiICYmICFtZXRob2QuY29tcHV0ZWQgJiYgbWV0aG9kLmtleS5uYW1lID09PSBcInN0YXRpY1wiICYmICh0aGlzLnRvay50eXBlICE9IHR0LnBhcmVuTCAmJiB0aGlzLnRvay50eXBlICE9IHR0LmJyYWNlTCkpIHtcbiAgICAgIG1ldGhvZFtcInN0YXRpY1wiXSA9IHRydWU7XG4gICAgICBpc0dlbmVyYXRvciA9IHRoaXMuZWF0KHR0LnN0YXIpO1xuICAgICAgdGhpcy5wYXJzZVByb3BlcnR5TmFtZShtZXRob2QpO1xuICAgIH0gZWxzZSB7XG4gICAgICBtZXRob2RbXCJzdGF0aWNcIl0gPSBmYWxzZTtcbiAgICB9XG4gICAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA1ICYmIG1ldGhvZC5rZXkudHlwZSA9PT0gXCJJZGVudGlmaWVyXCIgJiYgIW1ldGhvZC5jb21wdXRlZCAmJiAobWV0aG9kLmtleS5uYW1lID09PSBcImdldFwiIHx8IG1ldGhvZC5rZXkubmFtZSA9PT0gXCJzZXRcIikgJiYgdGhpcy50b2sudHlwZSAhPT0gdHQucGFyZW5MICYmIHRoaXMudG9rLnR5cGUgIT09IHR0LmJyYWNlTCkge1xuICAgICAgbWV0aG9kLmtpbmQgPSBtZXRob2Qua2V5Lm5hbWU7XG4gICAgICB0aGlzLnBhcnNlUHJvcGVydHlOYW1lKG1ldGhvZCk7XG4gICAgICBtZXRob2QudmFsdWUgPSB0aGlzLnBhcnNlTWV0aG9kKGZhbHNlKTtcbiAgICB9IGVsc2Uge1xuICAgICAgaWYgKCFtZXRob2QuY29tcHV0ZWQgJiYgIW1ldGhvZFtcInN0YXRpY1wiXSAmJiAhaXNHZW5lcmF0b3IgJiYgKG1ldGhvZC5rZXkudHlwZSA9PT0gXCJJZGVudGlmaWVyXCIgJiYgbWV0aG9kLmtleS5uYW1lID09PSBcImNvbnN0cnVjdG9yXCIgfHwgbWV0aG9kLmtleS50eXBlID09PSBcIkxpdGVyYWxcIiAmJiBtZXRob2Qua2V5LnZhbHVlID09PSBcImNvbnN0cnVjdG9yXCIpKSB7XG4gICAgICAgIG1ldGhvZC5raW5kID0gXCJjb25zdHJ1Y3RvclwiO1xuICAgICAgfSBlbHNlIHtcbiAgICAgICAgbWV0aG9kLmtpbmQgPSBcIm1ldGhvZFwiO1xuICAgICAgfVxuICAgICAgbWV0aG9kLnZhbHVlID0gdGhpcy5wYXJzZU1ldGhvZChpc0dlbmVyYXRvcik7XG4gICAgfVxuICAgIG5vZGUuYm9keS5ib2R5LnB1c2godGhpcy5maW5pc2hOb2RlKG1ldGhvZCwgXCJNZXRob2REZWZpbml0aW9uXCIpKTtcbiAgfVxuICB0aGlzLnBvcEN4KCk7XG4gIGlmICghdGhpcy5lYXQodHQuYnJhY2VSKSkge1xuICAgIC8vIElmIHRoZXJlIGlzIG5vIGNsb3NpbmcgYnJhY2UsIG1ha2UgdGhlIG5vZGUgc3BhbiB0byB0aGUgc3RhcnRcbiAgICAvLyBvZiB0aGUgbmV4dCB0b2tlbiAodGhpcyBpcyB1c2VmdWwgZm9yIFRlcm4pXG4gICAgdGhpcy5sYXN0LmVuZCA9IHRoaXMudG9rLnN0YXJ0O1xuICAgIGlmICh0aGlzLm9wdGlvbnMubG9jYXRpb25zKSB0aGlzLmxhc3QubG9jLmVuZCA9IHRoaXMudG9rLmxvYy5zdGFydDtcbiAgfVxuICB0aGlzLnNlbWljb2xvbigpO1xuICB0aGlzLmZpbmlzaE5vZGUobm9kZS5ib2R5LCBcIkNsYXNzQm9keVwiKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBpc1N0YXRlbWVudCA/IFwiQ2xhc3NEZWNsYXJhdGlvblwiIDogXCJDbGFzc0V4cHJlc3Npb25cIik7XG59O1xuXG5scC5wYXJzZUZ1bmN0aW9uID0gZnVuY3Rpb24gKG5vZGUsIGlzU3RhdGVtZW50KSB7XG4gIHRoaXMuaW5pdEZ1bmN0aW9uKG5vZGUpO1xuICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYpIHtcbiAgICBub2RlLmdlbmVyYXRvciA9IHRoaXMuZWF0KHR0LnN0YXIpO1xuICB9XG4gIGlmICh0aGlzLnRvay50eXBlID09PSB0dC5uYW1lKSBub2RlLmlkID0gdGhpcy5wYXJzZUlkZW50KCk7ZWxzZSBpZiAoaXNTdGF0ZW1lbnQpIG5vZGUuaWQgPSB0aGlzLmR1bW15SWRlbnQoKTtcbiAgbm9kZS5wYXJhbXMgPSB0aGlzLnBhcnNlRnVuY3Rpb25QYXJhbXMoKTtcbiAgbm9kZS5ib2R5ID0gdGhpcy5wYXJzZUJsb2NrKCk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgaXNTdGF0ZW1lbnQgPyBcIkZ1bmN0aW9uRGVjbGFyYXRpb25cIiA6IFwiRnVuY3Rpb25FeHByZXNzaW9uXCIpO1xufTtcblxubHAucGFyc2VFeHBvcnQgPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgdGhpcy5uZXh0KCk7XG4gIGlmICh0aGlzLmVhdCh0dC5zdGFyKSkge1xuICAgIG5vZGUuc291cmNlID0gdGhpcy5lYXRDb250ZXh0dWFsKFwiZnJvbVwiKSA/IHRoaXMucGFyc2VFeHByQXRvbSgpIDogbnVsbDtcbiAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiRXhwb3J0QWxsRGVjbGFyYXRpb25cIik7XG4gIH1cbiAgaWYgKHRoaXMuZWF0KHR0Ll9kZWZhdWx0KSkge1xuICAgIHZhciBleHByID0gdGhpcy5wYXJzZU1heWJlQXNzaWduKCk7XG4gICAgaWYgKGV4cHIuaWQpIHtcbiAgICAgIHN3aXRjaCAoZXhwci50eXBlKSB7XG4gICAgICAgIGNhc2UgXCJGdW5jdGlvbkV4cHJlc3Npb25cIjpcbiAgICAgICAgICBleHByLnR5cGUgPSBcIkZ1bmN0aW9uRGVjbGFyYXRpb25cIjticmVhaztcbiAgICAgICAgY2FzZSBcIkNsYXNzRXhwcmVzc2lvblwiOlxuICAgICAgICAgIGV4cHIudHlwZSA9IFwiQ2xhc3NEZWNsYXJhdGlvblwiO2JyZWFrO1xuICAgICAgfVxuICAgIH1cbiAgICBub2RlLmRlY2xhcmF0aW9uID0gZXhwcjtcbiAgICB0aGlzLnNlbWljb2xvbigpO1xuICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJFeHBvcnREZWZhdWx0RGVjbGFyYXRpb25cIik7XG4gIH1cbiAgaWYgKHRoaXMudG9rLnR5cGUua2V5d29yZCkge1xuICAgIG5vZGUuZGVjbGFyYXRpb24gPSB0aGlzLnBhcnNlU3RhdGVtZW50KCk7XG4gICAgbm9kZS5zcGVjaWZpZXJzID0gW107XG4gICAgbm9kZS5zb3VyY2UgPSBudWxsO1xuICB9IGVsc2Uge1xuICAgIG5vZGUuZGVjbGFyYXRpb24gPSBudWxsO1xuICAgIG5vZGUuc3BlY2lmaWVycyA9IHRoaXMucGFyc2VFeHBvcnRTcGVjaWZpZXJMaXN0KCk7XG4gICAgbm9kZS5zb3VyY2UgPSB0aGlzLmVhdENvbnRleHR1YWwoXCJmcm9tXCIpID8gdGhpcy5wYXJzZUV4cHJBdG9tKCkgOiBudWxsO1xuICAgIHRoaXMuc2VtaWNvbG9uKCk7XG4gIH1cbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkV4cG9ydE5hbWVkRGVjbGFyYXRpb25cIik7XG59O1xuXG5scC5wYXJzZUltcG9ydCA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICB0aGlzLm5leHQoKTtcbiAgaWYgKHRoaXMudG9rLnR5cGUgPT09IHR0LnN0cmluZykge1xuICAgIG5vZGUuc3BlY2lmaWVycyA9IFtdO1xuICAgIG5vZGUuc291cmNlID0gdGhpcy5wYXJzZUV4cHJBdG9tKCk7XG4gICAgbm9kZS5raW5kID0gXCJcIjtcbiAgfSBlbHNlIHtcbiAgICB2YXIgZWx0ID0gdW5kZWZpbmVkO1xuICAgIGlmICh0aGlzLnRvay50eXBlID09PSB0dC5uYW1lICYmIHRoaXMudG9rLnZhbHVlICE9PSBcImZyb21cIikge1xuICAgICAgZWx0ID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgICAgIGVsdC5sb2NhbCA9IHRoaXMucGFyc2VJZGVudCgpO1xuICAgICAgdGhpcy5maW5pc2hOb2RlKGVsdCwgXCJJbXBvcnREZWZhdWx0U3BlY2lmaWVyXCIpO1xuICAgICAgdGhpcy5lYXQodHQuY29tbWEpO1xuICAgIH1cbiAgICBub2RlLnNwZWNpZmllcnMgPSB0aGlzLnBhcnNlSW1wb3J0U3BlY2lmaWVyTGlzdCgpO1xuICAgIG5vZGUuc291cmNlID0gdGhpcy5lYXRDb250ZXh0dWFsKFwiZnJvbVwiKSA/IHRoaXMucGFyc2VFeHByQXRvbSgpIDogbnVsbDtcbiAgICBpZiAoZWx0KSBub2RlLnNwZWNpZmllcnMudW5zaGlmdChlbHQpO1xuICB9XG4gIHRoaXMuc2VtaWNvbG9uKCk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJJbXBvcnREZWNsYXJhdGlvblwiKTtcbn07XG5cbmxwLnBhcnNlSW1wb3J0U3BlY2lmaWVyTGlzdCA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIGVsdHMgPSBbXTtcbiAgaWYgKHRoaXMudG9rLnR5cGUgPT09IHR0LnN0YXIpIHtcbiAgICB2YXIgZWx0ID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgICB0aGlzLm5leHQoKTtcbiAgICBpZiAodGhpcy5lYXRDb250ZXh0dWFsKFwiYXNcIikpIGVsdC5sb2NhbCA9IHRoaXMucGFyc2VJZGVudCgpO1xuICAgIGVsdHMucHVzaCh0aGlzLmZpbmlzaE5vZGUoZWx0LCBcIkltcG9ydE5hbWVzcGFjZVNwZWNpZmllclwiKSk7XG4gIH0gZWxzZSB7XG4gICAgdmFyIGluZGVudCA9IHRoaXMuY3VySW5kZW50LFxuICAgICAgICBsaW5lID0gdGhpcy5jdXJMaW5lU3RhcnQsXG4gICAgICAgIGNvbnRpbnVlZExpbmUgPSB0aGlzLm5leHRMaW5lU3RhcnQ7XG4gICAgdGhpcy5wdXNoQ3goKTtcbiAgICB0aGlzLmVhdCh0dC5icmFjZUwpO1xuICAgIGlmICh0aGlzLmN1ckxpbmVTdGFydCA+IGNvbnRpbnVlZExpbmUpIGNvbnRpbnVlZExpbmUgPSB0aGlzLmN1ckxpbmVTdGFydDtcbiAgICB3aGlsZSAoIXRoaXMuY2xvc2VzKHR0LmJyYWNlUiwgaW5kZW50ICsgKHRoaXMuY3VyTGluZVN0YXJ0IDw9IGNvbnRpbnVlZExpbmUgPyAxIDogMCksIGxpbmUpKSB7XG4gICAgICB2YXIgZWx0ID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgICAgIGlmICh0aGlzLmVhdCh0dC5zdGFyKSkge1xuICAgICAgICBpZiAodGhpcy5lYXRDb250ZXh0dWFsKFwiYXNcIikpIGVsdC5sb2NhbCA9IHRoaXMucGFyc2VJZGVudCgpO1xuICAgICAgICB0aGlzLmZpbmlzaE5vZGUoZWx0LCBcIkltcG9ydE5hbWVzcGFjZVNwZWNpZmllclwiKTtcbiAgICAgIH0gZWxzZSB7XG4gICAgICAgIGlmICh0aGlzLmlzQ29udGV4dHVhbChcImZyb21cIikpIGJyZWFrO1xuICAgICAgICBlbHQuaW1wb3J0ZWQgPSB0aGlzLnBhcnNlSWRlbnQoKTtcbiAgICAgICAgZWx0LmxvY2FsID0gdGhpcy5lYXRDb250ZXh0dWFsKFwiYXNcIikgPyB0aGlzLnBhcnNlSWRlbnQoKSA6IGVsdC5pbXBvcnRlZDtcbiAgICAgICAgdGhpcy5maW5pc2hOb2RlKGVsdCwgXCJJbXBvcnRTcGVjaWZpZXJcIik7XG4gICAgICB9XG4gICAgICBlbHRzLnB1c2goZWx0KTtcbiAgICAgIHRoaXMuZWF0KHR0LmNvbW1hKTtcbiAgICB9XG4gICAgdGhpcy5lYXQodHQuYnJhY2VSKTtcbiAgICB0aGlzLnBvcEN4KCk7XG4gIH1cbiAgcmV0dXJuIGVsdHM7XG59O1xuXG5scC5wYXJzZUV4cG9ydFNwZWNpZmllckxpc3QgPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBlbHRzID0gW107XG4gIHZhciBpbmRlbnQgPSB0aGlzLmN1ckluZGVudCxcbiAgICAgIGxpbmUgPSB0aGlzLmN1ckxpbmVTdGFydCxcbiAgICAgIGNvbnRpbnVlZExpbmUgPSB0aGlzLm5leHRMaW5lU3RhcnQ7XG4gIHRoaXMucHVzaEN4KCk7XG4gIHRoaXMuZWF0KHR0LmJyYWNlTCk7XG4gIGlmICh0aGlzLmN1ckxpbmVTdGFydCA+IGNvbnRpbnVlZExpbmUpIGNvbnRpbnVlZExpbmUgPSB0aGlzLmN1ckxpbmVTdGFydDtcbiAgd2hpbGUgKCF0aGlzLmNsb3Nlcyh0dC5icmFjZVIsIGluZGVudCArICh0aGlzLmN1ckxpbmVTdGFydCA8PSBjb250aW51ZWRMaW5lID8gMSA6IDApLCBsaW5lKSkge1xuICAgIGlmICh0aGlzLmlzQ29udGV4dHVhbChcImZyb21cIikpIGJyZWFrO1xuICAgIHZhciBlbHQgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICAgIGVsdC5sb2NhbCA9IHRoaXMucGFyc2VJZGVudCgpO1xuICAgIGVsdC5leHBvcnRlZCA9IHRoaXMuZWF0Q29udGV4dHVhbChcImFzXCIpID8gdGhpcy5wYXJzZUlkZW50KCkgOiBlbHQubG9jYWw7XG4gICAgdGhpcy5maW5pc2hOb2RlKGVsdCwgXCJFeHBvcnRTcGVjaWZpZXJcIik7XG4gICAgZWx0cy5wdXNoKGVsdCk7XG4gICAgdGhpcy5lYXQodHQuY29tbWEpO1xuICB9XG4gIHRoaXMuZWF0KHR0LmJyYWNlUik7XG4gIHRoaXMucG9wQ3goKTtcbiAgcmV0dXJuIGVsdHM7XG59O1xuXG59LHtcIi4uXCI6MyxcIi4vcGFyc2V1dGlsXCI6NSxcIi4vc3RhdGVcIjo2fV0sODpbZnVuY3Rpb24oX2RlcmVxXyxtb2R1bGUsZXhwb3J0cyl7XG5cInVzZSBzdHJpY3RcIjtcblxudmFyIF8gPSBfZGVyZXFfKFwiLi5cIik7XG5cbnZhciB0dCA9IF8udG9rVHlwZXM7XG52YXIgVG9rZW4gPSBfLlRva2VuO1xudmFyIGlzTmV3TGluZSA9IF8uaXNOZXdMaW5lO1xudmFyIFNvdXJjZUxvY2F0aW9uID0gXy5Tb3VyY2VMb2NhdGlvbjtcbnZhciBnZXRMaW5lSW5mbyA9IF8uZ2V0TGluZUluZm87XG52YXIgbGluZUJyZWFrRyA9IF8ubGluZUJyZWFrRztcblxudmFyIExvb3NlUGFyc2VyID0gX2RlcmVxXyhcIi4vc3RhdGVcIikuTG9vc2VQYXJzZXI7XG5cbnZhciBscCA9IExvb3NlUGFyc2VyLnByb3RvdHlwZTtcblxuZnVuY3Rpb24gaXNTcGFjZShjaCkge1xuICByZXR1cm4gY2ggPCAxNCAmJiBjaCA+IDggfHwgY2ggPT09IDMyIHx8IGNoID09PSAxNjAgfHwgaXNOZXdMaW5lKGNoKTtcbn1cblxubHAubmV4dCA9IGZ1bmN0aW9uICgpIHtcbiAgdGhpcy5sYXN0ID0gdGhpcy50b2s7XG4gIGlmICh0aGlzLmFoZWFkLmxlbmd0aCkgdGhpcy50b2sgPSB0aGlzLmFoZWFkLnNoaWZ0KCk7ZWxzZSB0aGlzLnRvayA9IHRoaXMucmVhZFRva2VuKCk7XG5cbiAgaWYgKHRoaXMudG9rLnN0YXJ0ID49IHRoaXMubmV4dExpbmVTdGFydCkge1xuICAgIHdoaWxlICh0aGlzLnRvay5zdGFydCA+PSB0aGlzLm5leHRMaW5lU3RhcnQpIHtcbiAgICAgIHRoaXMuY3VyTGluZVN0YXJ0ID0gdGhpcy5uZXh0TGluZVN0YXJ0O1xuICAgICAgdGhpcy5uZXh0TGluZVN0YXJ0ID0gdGhpcy5saW5lRW5kKHRoaXMuY3VyTGluZVN0YXJ0KSArIDE7XG4gICAgfVxuICAgIHRoaXMuY3VySW5kZW50ID0gdGhpcy5pbmRlbnRhdGlvbkFmdGVyKHRoaXMuY3VyTGluZVN0YXJ0KTtcbiAgfVxufTtcblxubHAucmVhZFRva2VuID0gZnVuY3Rpb24gKCkge1xuICBmb3IgKDs7KSB7XG4gICAgdHJ5IHtcbiAgICAgIHRoaXMudG9rcy5uZXh0KCk7XG4gICAgICBpZiAodGhpcy50b2tzLnR5cGUgPT09IHR0LmRvdCAmJiB0aGlzLmlucHV0LnN1YnN0cih0aGlzLnRva3MuZW5kLCAxKSA9PT0gXCIuXCIgJiYgdGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYpIHtcbiAgICAgICAgdGhpcy50b2tzLmVuZCsrO1xuICAgICAgICB0aGlzLnRva3MudHlwZSA9IHR0LmVsbGlwc2lzO1xuICAgICAgfVxuICAgICAgcmV0dXJuIG5ldyBUb2tlbih0aGlzLnRva3MpO1xuICAgIH0gY2F0Y2ggKGUpIHtcbiAgICAgIGlmICghKGUgaW5zdGFuY2VvZiBTeW50YXhFcnJvcikpIHRocm93IGU7XG5cbiAgICAgIC8vIFRyeSB0byBza2lwIHNvbWUgdGV4dCwgYmFzZWQgb24gdGhlIGVycm9yIG1lc3NhZ2UsIGFuZCB0aGVuIGNvbnRpbnVlXG4gICAgICB2YXIgbXNnID0gZS5tZXNzYWdlLFxuICAgICAgICAgIHBvcyA9IGUucmFpc2VkQXQsXG4gICAgICAgICAgcmVwbGFjZSA9IHRydWU7XG4gICAgICBpZiAoL3VudGVybWluYXRlZC9pLnRlc3QobXNnKSkge1xuICAgICAgICBwb3MgPSB0aGlzLmxpbmVFbmQoZS5wb3MgKyAxKTtcbiAgICAgICAgaWYgKC9zdHJpbmcvLnRlc3QobXNnKSkge1xuICAgICAgICAgIHJlcGxhY2UgPSB7IHN0YXJ0OiBlLnBvcywgZW5kOiBwb3MsIHR5cGU6IHR0LnN0cmluZywgdmFsdWU6IHRoaXMuaW5wdXQuc2xpY2UoZS5wb3MgKyAxLCBwb3MpIH07XG4gICAgICAgIH0gZWxzZSBpZiAoL3JlZ3VsYXIgZXhwci9pLnRlc3QobXNnKSkge1xuICAgICAgICAgIHZhciByZSA9IHRoaXMuaW5wdXQuc2xpY2UoZS5wb3MsIHBvcyk7XG4gICAgICAgICAgdHJ5IHtcbiAgICAgICAgICAgIHJlID0gbmV3IFJlZ0V4cChyZSk7XG4gICAgICAgICAgfSBjYXRjaCAoZSkge31cbiAgICAgICAgICByZXBsYWNlID0geyBzdGFydDogZS5wb3MsIGVuZDogcG9zLCB0eXBlOiB0dC5yZWdleHAsIHZhbHVlOiByZSB9O1xuICAgICAgICB9IGVsc2UgaWYgKC90ZW1wbGF0ZS8udGVzdChtc2cpKSB7XG4gICAgICAgICAgcmVwbGFjZSA9IHsgc3RhcnQ6IGUucG9zLCBlbmQ6IHBvcyxcbiAgICAgICAgICAgIHR5cGU6IHR0LnRlbXBsYXRlLFxuICAgICAgICAgICAgdmFsdWU6IHRoaXMuaW5wdXQuc2xpY2UoZS5wb3MsIHBvcykgfTtcbiAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICByZXBsYWNlID0gZmFsc2U7XG4gICAgICAgIH1cbiAgICAgIH0gZWxzZSBpZiAoL2ludmFsaWQgKHVuaWNvZGV8cmVnZXhwfG51bWJlcil8ZXhwZWN0aW5nIHVuaWNvZGV8b2N0YWwgbGl0ZXJhbHxpcyByZXNlcnZlZHxkaXJlY3RseSBhZnRlciBudW1iZXJ8ZXhwZWN0ZWQgbnVtYmVyIGluIHJhZGl4L2kudGVzdChtc2cpKSB7XG4gICAgICAgIHdoaWxlIChwb3MgPCB0aGlzLmlucHV0Lmxlbmd0aCAmJiAhaXNTcGFjZSh0aGlzLmlucHV0LmNoYXJDb2RlQXQocG9zKSkpICsrcG9zO1xuICAgICAgfSBlbHNlIGlmICgvY2hhcmFjdGVyIGVzY2FwZXxleHBlY3RlZCBoZXhhZGVjaW1hbC9pLnRlc3QobXNnKSkge1xuICAgICAgICB3aGlsZSAocG9zIDwgdGhpcy5pbnB1dC5sZW5ndGgpIHtcbiAgICAgICAgICB2YXIgY2ggPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQocG9zKyspO1xuICAgICAgICAgIGlmIChjaCA9PT0gMzQgfHwgY2ggPT09IDM5IHx8IGlzTmV3TGluZShjaCkpIGJyZWFrO1xuICAgICAgICB9XG4gICAgICB9IGVsc2UgaWYgKC91bmV4cGVjdGVkIGNoYXJhY3Rlci9pLnRlc3QobXNnKSkge1xuICAgICAgICBwb3MrKztcbiAgICAgICAgcmVwbGFjZSA9IGZhbHNlO1xuICAgICAgfSBlbHNlIGlmICgvcmVndWxhciBleHByZXNzaW9uL2kudGVzdChtc2cpKSB7XG4gICAgICAgIHJlcGxhY2UgPSB0cnVlO1xuICAgICAgfSBlbHNlIHtcbiAgICAgICAgdGhyb3cgZTtcbiAgICAgIH1cbiAgICAgIHRoaXMucmVzZXRUbyhwb3MpO1xuICAgICAgaWYgKHJlcGxhY2UgPT09IHRydWUpIHJlcGxhY2UgPSB7IHN0YXJ0OiBwb3MsIGVuZDogcG9zLCB0eXBlOiB0dC5uYW1lLCB2YWx1ZTogXCLinJZcIiB9O1xuICAgICAgaWYgKHJlcGxhY2UpIHtcbiAgICAgICAgaWYgKHRoaXMub3B0aW9ucy5sb2NhdGlvbnMpIHJlcGxhY2UubG9jID0gbmV3IFNvdXJjZUxvY2F0aW9uKHRoaXMudG9rcywgZ2V0TGluZUluZm8odGhpcy5pbnB1dCwgcmVwbGFjZS5zdGFydCksIGdldExpbmVJbmZvKHRoaXMuaW5wdXQsIHJlcGxhY2UuZW5kKSk7XG4gICAgICAgIHJldHVybiByZXBsYWNlO1xuICAgICAgfVxuICAgIH1cbiAgfVxufTtcblxubHAucmVzZXRUbyA9IGZ1bmN0aW9uIChwb3MpIHtcbiAgdGhpcy50b2tzLnBvcyA9IHBvcztcbiAgdmFyIGNoID0gdGhpcy5pbnB1dC5jaGFyQXQocG9zIC0gMSk7XG4gIHRoaXMudG9rcy5leHByQWxsb3dlZCA9ICFjaCB8fCAvW1xcW1xce1xcKCw7Oj9cXC8qPStcXC1+IXwmJV48Pl0vLnRlc3QoY2gpIHx8IC9bZW53ZmRdLy50ZXN0KGNoKSAmJiAvXFxiKGtleXdvcmRzfGNhc2V8ZWxzZXxyZXR1cm58dGhyb3d8bmV3fGlufChpbnN0YW5jZXx0eXBlKW9mfGRlbGV0ZXx2b2lkKSQvLnRlc3QodGhpcy5pbnB1dC5zbGljZShwb3MgLSAxMCwgcG9zKSk7XG5cbiAgaWYgKHRoaXMub3B0aW9ucy5sb2NhdGlvbnMpIHtcbiAgICB0aGlzLnRva3MuY3VyTGluZSA9IDE7XG4gICAgdGhpcy50b2tzLmxpbmVTdGFydCA9IGxpbmVCcmVha0cubGFzdEluZGV4ID0gMDtcbiAgICB2YXIgbWF0Y2ggPSB1bmRlZmluZWQ7XG4gICAgd2hpbGUgKChtYXRjaCA9IGxpbmVCcmVha0cuZXhlYyh0aGlzLmlucHV0KSkgJiYgbWF0Y2guaW5kZXggPCBwb3MpIHtcbiAgICAgICsrdGhpcy50b2tzLmN1ckxpbmU7XG4gICAgICB0aGlzLnRva3MubGluZVN0YXJ0ID0gbWF0Y2guaW5kZXggKyBtYXRjaFswXS5sZW5ndGg7XG4gICAgfVxuICB9XG59O1xuXG5scC5sb29rQWhlYWQgPSBmdW5jdGlvbiAobikge1xuICB3aGlsZSAobiA+IHRoaXMuYWhlYWQubGVuZ3RoKSB0aGlzLmFoZWFkLnB1c2godGhpcy5yZWFkVG9rZW4oKSk7XG4gIHJldHVybiB0aGlzLmFoZWFkW24gLSAxXTtcbn07XG5cbn0se1wiLi5cIjozLFwiLi9zdGF0ZVwiOjZ9XX0se30sWzFdKSgxKVxufSk7IiwiKGZ1bmN0aW9uKGYpe2lmKHR5cGVvZiBleHBvcnRzPT09XCJvYmplY3RcIiYmdHlwZW9mIG1vZHVsZSE9PVwidW5kZWZpbmVkXCIpe21vZHVsZS5leHBvcnRzPWYoKX1lbHNlIGlmKHR5cGVvZiBkZWZpbmU9PT1cImZ1bmN0aW9uXCImJmRlZmluZS5hbWQpe2RlZmluZShbXSxmKX1lbHNle3ZhciBnO2lmKHR5cGVvZiB3aW5kb3chPT1cInVuZGVmaW5lZFwiKXtnPXdpbmRvd31lbHNlIGlmKHR5cGVvZiBnbG9iYWwhPT1cInVuZGVmaW5lZFwiKXtnPWdsb2JhbH1lbHNlIGlmKHR5cGVvZiBzZWxmIT09XCJ1bmRlZmluZWRcIil7Zz1zZWxmfWVsc2V7Zz10aGlzfShnLmFjb3JuIHx8IChnLmFjb3JuID0ge30pKS53YWxrID0gZigpfX0pKGZ1bmN0aW9uKCl7dmFyIGRlZmluZSxtb2R1bGUsZXhwb3J0cztyZXR1cm4gKGZ1bmN0aW9uIGUodCxuLHIpe2Z1bmN0aW9uIHMobyx1KXtpZighbltvXSl7aWYoIXRbb10pe3ZhciBhPXR5cGVvZiByZXF1aXJlPT1cImZ1bmN0aW9uXCImJnJlcXVpcmU7aWYoIXUmJmEpcmV0dXJuIGEobywhMCk7aWYoaSlyZXR1cm4gaShvLCEwKTt2YXIgZj1uZXcgRXJyb3IoXCJDYW5ub3QgZmluZCBtb2R1bGUgJ1wiK28rXCInXCIpO3Rocm93IGYuY29kZT1cIk1PRFVMRV9OT1RfRk9VTkRcIixmfXZhciBsPW5bb109e2V4cG9ydHM6e319O3Rbb11bMF0uY2FsbChsLmV4cG9ydHMsZnVuY3Rpb24oZSl7dmFyIG49dFtvXVsxXVtlXTtyZXR1cm4gcyhuP246ZSl9LGwsbC5leHBvcnRzLGUsdCxuLHIpfXJldHVybiBuW29dLmV4cG9ydHN9dmFyIGk9dHlwZW9mIHJlcXVpcmU9PVwiZnVuY3Rpb25cIiYmcmVxdWlyZTtmb3IodmFyIG89MDtvPHIubGVuZ3RoO28rKylzKHJbb10pO3JldHVybiBzfSkoezE6W2Z1bmN0aW9uKF9kZXJlcV8sbW9kdWxlLGV4cG9ydHMpe1xuXCJ1c2Ugc3RyaWN0XCI7XG5cbnZhciBfY2xhc3NDYWxsQ2hlY2sgPSBmdW5jdGlvbiAoaW5zdGFuY2UsIENvbnN0cnVjdG9yKSB7IGlmICghKGluc3RhbmNlIGluc3RhbmNlb2YgQ29uc3RydWN0b3IpKSB7IHRocm93IG5ldyBUeXBlRXJyb3IoXCJDYW5ub3QgY2FsbCBhIGNsYXNzIGFzIGEgZnVuY3Rpb25cIik7IH0gfTtcblxuLy8gQVNUIHdhbGtlciBtb2R1bGUgZm9yIE1vemlsbGEgUGFyc2VyIEFQSSBjb21wYXRpYmxlIHRyZWVzXG5cbi8vIEEgc2ltcGxlIHdhbGsgaXMgb25lIHdoZXJlIHlvdSBzaW1wbHkgc3BlY2lmeSBjYWxsYmFja3MgdG8gYmVcbi8vIGNhbGxlZCBvbiBzcGVjaWZpYyBub2Rlcy4gVGhlIGxhc3QgdHdvIGFyZ3VtZW50cyBhcmUgb3B0aW9uYWwuIEFcbi8vIHNpbXBsZSB1c2Ugd291bGQgYmVcbi8vXG4vLyAgICAgd2Fsay5zaW1wbGUobXlUcmVlLCB7XG4vLyAgICAgICAgIEV4cHJlc3Npb246IGZ1bmN0aW9uKG5vZGUpIHsgLi4uIH1cbi8vICAgICB9KTtcbi8vXG4vLyB0byBkbyBzb21ldGhpbmcgd2l0aCBhbGwgZXhwcmVzc2lvbnMuIEFsbCBQYXJzZXIgQVBJIG5vZGUgdHlwZXNcbi8vIGNhbiBiZSB1c2VkIHRvIGlkZW50aWZ5IG5vZGUgdHlwZXMsIGFzIHdlbGwgYXMgRXhwcmVzc2lvbixcbi8vIFN0YXRlbWVudCwgYW5kIFNjb3BlQm9keSwgd2hpY2ggZGVub3RlIGNhdGVnb3JpZXMgb2Ygbm9kZXMuXG4vL1xuLy8gVGhlIGJhc2UgYXJndW1lbnQgY2FuIGJlIHVzZWQgdG8gcGFzcyBhIGN1c3RvbSAocmVjdXJzaXZlKVxuLy8gd2Fsa2VyLCBhbmQgc3RhdGUgY2FuIGJlIHVzZWQgdG8gZ2l2ZSB0aGlzIHdhbGtlZCBhbiBpbml0aWFsXG4vLyBzdGF0ZS5cblxuZXhwb3J0cy5zaW1wbGUgPSBzaW1wbGU7XG5cbi8vIEFuIGFuY2VzdG9yIHdhbGsgYnVpbGRzIHVwIGFuIGFycmF5IG9mIGFuY2VzdG9yIG5vZGVzIChpbmNsdWRpbmdcbi8vIHRoZSBjdXJyZW50IG5vZGUpIGFuZCBwYXNzZXMgdGhlbSB0byB0aGUgY2FsbGJhY2sgYXMgdGhlIHN0YXRlIHBhcmFtZXRlci5cbmV4cG9ydHMuYW5jZXN0b3IgPSBhbmNlc3RvcjtcblxuLy8gQSByZWN1cnNpdmUgd2FsayBpcyBvbmUgd2hlcmUgeW91ciBmdW5jdGlvbnMgb3ZlcnJpZGUgdGhlIGRlZmF1bHRcbi8vIHdhbGtlcnMuIFRoZXkgY2FuIG1vZGlmeSBhbmQgcmVwbGFjZSB0aGUgc3RhdGUgcGFyYW1ldGVyIHRoYXQnc1xuLy8gdGhyZWFkZWQgdGhyb3VnaCB0aGUgd2FsaywgYW5kIGNhbiBvcHQgaG93IGFuZCB3aGV0aGVyIHRvIHdhbGtcbi8vIHRoZWlyIGNoaWxkIG5vZGVzIChieSBjYWxsaW5nIHRoZWlyIHRoaXJkIGFyZ3VtZW50IG9uIHRoZXNlXG4vLyBub2RlcykuXG5leHBvcnRzLnJlY3Vyc2l2ZSA9IHJlY3Vyc2l2ZTtcblxuLy8gRmluZCBhIG5vZGUgd2l0aCBhIGdpdmVuIHN0YXJ0LCBlbmQsIGFuZCB0eXBlIChhbGwgYXJlIG9wdGlvbmFsLFxuLy8gbnVsbCBjYW4gYmUgdXNlZCBhcyB3aWxkY2FyZCkuIFJldHVybnMgYSB7bm9kZSwgc3RhdGV9IG9iamVjdCwgb3Jcbi8vIHVuZGVmaW5lZCB3aGVuIGl0IGRvZXNuJ3QgZmluZCBhIG1hdGNoaW5nIG5vZGUuXG5leHBvcnRzLmZpbmROb2RlQXQgPSBmaW5kTm9kZUF0O1xuXG4vLyBGaW5kIHRoZSBpbm5lcm1vc3Qgbm9kZSBvZiBhIGdpdmVuIHR5cGUgdGhhdCBjb250YWlucyB0aGUgZ2l2ZW5cbi8vIHBvc2l0aW9uLiBJbnRlcmZhY2Ugc2ltaWxhciB0byBmaW5kTm9kZUF0LlxuZXhwb3J0cy5maW5kTm9kZUFyb3VuZCA9IGZpbmROb2RlQXJvdW5kO1xuXG4vLyBGaW5kIHRoZSBvdXRlcm1vc3QgbWF0Y2hpbmcgbm9kZSBhZnRlciBhIGdpdmVuIHBvc2l0aW9uLlxuZXhwb3J0cy5maW5kTm9kZUFmdGVyID0gZmluZE5vZGVBZnRlcjtcblxuLy8gRmluZCB0aGUgb3V0ZXJtb3N0IG1hdGNoaW5nIG5vZGUgYmVmb3JlIGEgZ2l2ZW4gcG9zaXRpb24uXG5leHBvcnRzLmZpbmROb2RlQmVmb3JlID0gZmluZE5vZGVCZWZvcmU7XG5cbi8vIFVzZWQgdG8gY3JlYXRlIGEgY3VzdG9tIHdhbGtlci4gV2lsbCBmaWxsIGluIGFsbCBtaXNzaW5nIG5vZGVcbi8vIHR5cGUgcHJvcGVydGllcyB3aXRoIHRoZSBkZWZhdWx0cy5cbmV4cG9ydHMubWFrZSA9IG1ha2U7XG5leHBvcnRzLl9fZXNNb2R1bGUgPSB0cnVlO1xuXG5mdW5jdGlvbiBzaW1wbGUobm9kZSwgdmlzaXRvcnMsIGJhc2UsIHN0YXRlKSB7XG4gIGlmICghYmFzZSkgYmFzZSA9IGV4cG9ydHMuYmFzZTsoZnVuY3Rpb24gYyhub2RlLCBzdCwgb3ZlcnJpZGUpIHtcbiAgICB2YXIgdHlwZSA9IG92ZXJyaWRlIHx8IG5vZGUudHlwZSxcbiAgICAgICAgZm91bmQgPSB2aXNpdG9yc1t0eXBlXTtcbiAgICBiYXNlW3R5cGVdKG5vZGUsIHN0LCBjKTtcbiAgICBpZiAoZm91bmQpIGZvdW5kKG5vZGUsIHN0KTtcbiAgfSkobm9kZSwgc3RhdGUpO1xufVxuXG5mdW5jdGlvbiBhbmNlc3Rvcihub2RlLCB2aXNpdG9ycywgYmFzZSwgc3RhdGUpIHtcbiAgaWYgKCFiYXNlKSBiYXNlID0gZXhwb3J0cy5iYXNlO1xuICBpZiAoIXN0YXRlKSBzdGF0ZSA9IFtdOyhmdW5jdGlvbiBjKG5vZGUsIHN0LCBvdmVycmlkZSkge1xuICAgIHZhciB0eXBlID0gb3ZlcnJpZGUgfHwgbm9kZS50eXBlLFxuICAgICAgICBmb3VuZCA9IHZpc2l0b3JzW3R5cGVdO1xuICAgIGlmIChub2RlICE9IHN0W3N0Lmxlbmd0aCAtIDFdKSB7XG4gICAgICBzdCA9IHN0LnNsaWNlKCk7XG4gICAgICBzdC5wdXNoKG5vZGUpO1xuICAgIH1cbiAgICBiYXNlW3R5cGVdKG5vZGUsIHN0LCBjKTtcbiAgICBpZiAoZm91bmQpIGZvdW5kKG5vZGUsIHN0KTtcbiAgfSkobm9kZSwgc3RhdGUpO1xufVxuXG5mdW5jdGlvbiByZWN1cnNpdmUobm9kZSwgc3RhdGUsIGZ1bmNzLCBiYXNlKSB7XG4gIHZhciB2aXNpdG9yID0gZnVuY3MgPyBleHBvcnRzLm1ha2UoZnVuY3MsIGJhc2UpIDogYmFzZTsoZnVuY3Rpb24gYyhub2RlLCBzdCwgb3ZlcnJpZGUpIHtcbiAgICB2aXNpdG9yW292ZXJyaWRlIHx8IG5vZGUudHlwZV0obm9kZSwgc3QsIGMpO1xuICB9KShub2RlLCBzdGF0ZSk7XG59XG5cbmZ1bmN0aW9uIG1ha2VUZXN0KHRlc3QpIHtcbiAgaWYgKHR5cGVvZiB0ZXN0ID09IFwic3RyaW5nXCIpIHtcbiAgICByZXR1cm4gZnVuY3Rpb24gKHR5cGUpIHtcbiAgICAgIHJldHVybiB0eXBlID09IHRlc3Q7XG4gICAgfTtcbiAgfSBlbHNlIGlmICghdGVzdCkge1xuICAgIHJldHVybiBmdW5jdGlvbiAoKSB7XG4gICAgICByZXR1cm4gdHJ1ZTtcbiAgICB9O1xuICB9IGVsc2Uge1xuICAgIHJldHVybiB0ZXN0O1xuICB9XG59XG5cbnZhciBGb3VuZCA9IGZ1bmN0aW9uIEZvdW5kKG5vZGUsIHN0YXRlKSB7XG4gIF9jbGFzc0NhbGxDaGVjayh0aGlzLCBGb3VuZCk7XG5cbiAgdGhpcy5ub2RlID0gbm9kZTt0aGlzLnN0YXRlID0gc3RhdGU7XG59O1xuXG5mdW5jdGlvbiBmaW5kTm9kZUF0KG5vZGUsIHN0YXJ0LCBlbmQsIHRlc3QsIGJhc2UsIHN0YXRlKSB7XG4gIHRlc3QgPSBtYWtlVGVzdCh0ZXN0KTtcbiAgaWYgKCFiYXNlKSBiYXNlID0gZXhwb3J0cy5iYXNlO1xuICB0cnkge1xuICAgIDsoZnVuY3Rpb24gYyhub2RlLCBzdCwgb3ZlcnJpZGUpIHtcbiAgICAgIHZhciB0eXBlID0gb3ZlcnJpZGUgfHwgbm9kZS50eXBlO1xuICAgICAgaWYgKChzdGFydCA9PSBudWxsIHx8IG5vZGUuc3RhcnQgPD0gc3RhcnQpICYmIChlbmQgPT0gbnVsbCB8fCBub2RlLmVuZCA+PSBlbmQpKSBiYXNlW3R5cGVdKG5vZGUsIHN0LCBjKTtcbiAgICAgIGlmICh0ZXN0KHR5cGUsIG5vZGUpICYmIChzdGFydCA9PSBudWxsIHx8IG5vZGUuc3RhcnQgPT0gc3RhcnQpICYmIChlbmQgPT0gbnVsbCB8fCBub2RlLmVuZCA9PSBlbmQpKSB0aHJvdyBuZXcgRm91bmQobm9kZSwgc3QpO1xuICAgIH0pKG5vZGUsIHN0YXRlKTtcbiAgfSBjYXRjaCAoZSkge1xuICAgIGlmIChlIGluc3RhbmNlb2YgRm91bmQpIHtcbiAgICAgIHJldHVybiBlO1xuICAgIH10aHJvdyBlO1xuICB9XG59XG5cbmZ1bmN0aW9uIGZpbmROb2RlQXJvdW5kKG5vZGUsIHBvcywgdGVzdCwgYmFzZSwgc3RhdGUpIHtcbiAgdGVzdCA9IG1ha2VUZXN0KHRlc3QpO1xuICBpZiAoIWJhc2UpIGJhc2UgPSBleHBvcnRzLmJhc2U7XG4gIHRyeSB7XG4gICAgOyhmdW5jdGlvbiBjKG5vZGUsIHN0LCBvdmVycmlkZSkge1xuICAgICAgdmFyIHR5cGUgPSBvdmVycmlkZSB8fCBub2RlLnR5cGU7XG4gICAgICBpZiAobm9kZS5zdGFydCA+IHBvcyB8fCBub2RlLmVuZCA8IHBvcykge1xuICAgICAgICByZXR1cm47XG4gICAgICB9YmFzZVt0eXBlXShub2RlLCBzdCwgYyk7XG4gICAgICBpZiAodGVzdCh0eXBlLCBub2RlKSkgdGhyb3cgbmV3IEZvdW5kKG5vZGUsIHN0KTtcbiAgICB9KShub2RlLCBzdGF0ZSk7XG4gIH0gY2F0Y2ggKGUpIHtcbiAgICBpZiAoZSBpbnN0YW5jZW9mIEZvdW5kKSB7XG4gICAgICByZXR1cm4gZTtcbiAgICB9dGhyb3cgZTtcbiAgfVxufVxuXG5mdW5jdGlvbiBmaW5kTm9kZUFmdGVyKG5vZGUsIHBvcywgdGVzdCwgYmFzZSwgc3RhdGUpIHtcbiAgdGVzdCA9IG1ha2VUZXN0KHRlc3QpO1xuICBpZiAoIWJhc2UpIGJhc2UgPSBleHBvcnRzLmJhc2U7XG4gIHRyeSB7XG4gICAgOyhmdW5jdGlvbiBjKG5vZGUsIHN0LCBvdmVycmlkZSkge1xuICAgICAgaWYgKG5vZGUuZW5kIDwgcG9zKSB7XG4gICAgICAgIHJldHVybjtcbiAgICAgIH12YXIgdHlwZSA9IG92ZXJyaWRlIHx8IG5vZGUudHlwZTtcbiAgICAgIGlmIChub2RlLnN0YXJ0ID49IHBvcyAmJiB0ZXN0KHR5cGUsIG5vZGUpKSB0aHJvdyBuZXcgRm91bmQobm9kZSwgc3QpO1xuICAgICAgYmFzZVt0eXBlXShub2RlLCBzdCwgYyk7XG4gICAgfSkobm9kZSwgc3RhdGUpO1xuICB9IGNhdGNoIChlKSB7XG4gICAgaWYgKGUgaW5zdGFuY2VvZiBGb3VuZCkge1xuICAgICAgcmV0dXJuIGU7XG4gICAgfXRocm93IGU7XG4gIH1cbn1cblxuZnVuY3Rpb24gZmluZE5vZGVCZWZvcmUobm9kZSwgcG9zLCB0ZXN0LCBiYXNlLCBzdGF0ZSkge1xuICB0ZXN0ID0gbWFrZVRlc3QodGVzdCk7XG4gIGlmICghYmFzZSkgYmFzZSA9IGV4cG9ydHMuYmFzZTtcbiAgdmFyIG1heCA9IHVuZGVmaW5lZDsoZnVuY3Rpb24gYyhub2RlLCBzdCwgb3ZlcnJpZGUpIHtcbiAgICBpZiAobm9kZS5zdGFydCA+IHBvcykge1xuICAgICAgcmV0dXJuO1xuICAgIH12YXIgdHlwZSA9IG92ZXJyaWRlIHx8IG5vZGUudHlwZTtcbiAgICBpZiAobm9kZS5lbmQgPD0gcG9zICYmICghbWF4IHx8IG1heC5ub2RlLmVuZCA8IG5vZGUuZW5kKSAmJiB0ZXN0KHR5cGUsIG5vZGUpKSBtYXggPSBuZXcgRm91bmQobm9kZSwgc3QpO1xuICAgIGJhc2VbdHlwZV0obm9kZSwgc3QsIGMpO1xuICB9KShub2RlLCBzdGF0ZSk7XG4gIHJldHVybiBtYXg7XG59XG5cbmZ1bmN0aW9uIG1ha2UoZnVuY3MsIGJhc2UpIHtcbiAgaWYgKCFiYXNlKSBiYXNlID0gZXhwb3J0cy5iYXNlO1xuICB2YXIgdmlzaXRvciA9IHt9O1xuICBmb3IgKHZhciB0eXBlIGluIGJhc2UpIHZpc2l0b3JbdHlwZV0gPSBiYXNlW3R5cGVdO1xuICBmb3IgKHZhciB0eXBlIGluIGZ1bmNzKSB2aXNpdG9yW3R5cGVdID0gZnVuY3NbdHlwZV07XG4gIHJldHVybiB2aXNpdG9yO1xufVxuXG5mdW5jdGlvbiBza2lwVGhyb3VnaChub2RlLCBzdCwgYykge1xuICBjKG5vZGUsIHN0KTtcbn1cbmZ1bmN0aW9uIGlnbm9yZShfbm9kZSwgX3N0LCBfYykge31cblxuLy8gTm9kZSB3YWxrZXJzLlxuXG52YXIgYmFzZSA9IHt9O1xuXG5leHBvcnRzLmJhc2UgPSBiYXNlO1xuYmFzZS5Qcm9ncmFtID0gYmFzZS5CbG9ja1N0YXRlbWVudCA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBmb3IgKHZhciBpID0gMDsgaSA8IG5vZGUuYm9keS5sZW5ndGg7ICsraSkge1xuICAgIGMobm9kZS5ib2R5W2ldLCBzdCwgXCJTdGF0ZW1lbnRcIik7XG4gIH1cbn07XG5iYXNlLlN0YXRlbWVudCA9IHNraXBUaHJvdWdoO1xuYmFzZS5FbXB0eVN0YXRlbWVudCA9IGlnbm9yZTtcbmJhc2UuRXhwcmVzc2lvblN0YXRlbWVudCA9IGJhc2UuUGFyZW50aGVzaXplZEV4cHJlc3Npb24gPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgcmV0dXJuIGMobm9kZS5leHByZXNzaW9uLCBzdCwgXCJFeHByZXNzaW9uXCIpO1xufTtcbmJhc2UuSWZTdGF0ZW1lbnQgPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgYyhub2RlLnRlc3QsIHN0LCBcIkV4cHJlc3Npb25cIik7XG4gIGMobm9kZS5jb25zZXF1ZW50LCBzdCwgXCJTdGF0ZW1lbnRcIik7XG4gIGlmIChub2RlLmFsdGVybmF0ZSkgYyhub2RlLmFsdGVybmF0ZSwgc3QsIFwiU3RhdGVtZW50XCIpO1xufTtcbmJhc2UuTGFiZWxlZFN0YXRlbWVudCA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICByZXR1cm4gYyhub2RlLmJvZHksIHN0LCBcIlN0YXRlbWVudFwiKTtcbn07XG5iYXNlLkJyZWFrU3RhdGVtZW50ID0gYmFzZS5Db250aW51ZVN0YXRlbWVudCA9IGlnbm9yZTtcbmJhc2UuV2l0aFN0YXRlbWVudCA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBjKG5vZGUub2JqZWN0LCBzdCwgXCJFeHByZXNzaW9uXCIpO1xuICBjKG5vZGUuYm9keSwgc3QsIFwiU3RhdGVtZW50XCIpO1xufTtcbmJhc2UuU3dpdGNoU3RhdGVtZW50ID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIGMobm9kZS5kaXNjcmltaW5hbnQsIHN0LCBcIkV4cHJlc3Npb25cIik7XG4gIGZvciAodmFyIGkgPSAwOyBpIDwgbm9kZS5jYXNlcy5sZW5ndGg7ICsraSkge1xuICAgIHZhciBjcyA9IG5vZGUuY2FzZXNbaV07XG4gICAgaWYgKGNzLnRlc3QpIGMoY3MudGVzdCwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbiAgICBmb3IgKHZhciBqID0gMDsgaiA8IGNzLmNvbnNlcXVlbnQubGVuZ3RoOyArK2opIHtcbiAgICAgIGMoY3MuY29uc2VxdWVudFtqXSwgc3QsIFwiU3RhdGVtZW50XCIpO1xuICAgIH1cbiAgfVxufTtcbmJhc2UuUmV0dXJuU3RhdGVtZW50ID0gYmFzZS5ZaWVsZEV4cHJlc3Npb24gPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgaWYgKG5vZGUuYXJndW1lbnQpIGMobm9kZS5hcmd1bWVudCwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbn07XG5iYXNlLlRocm93U3RhdGVtZW50ID0gYmFzZS5TcHJlYWRFbGVtZW50ID0gYmFzZS5SZXN0RWxlbWVudCA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICByZXR1cm4gYyhub2RlLmFyZ3VtZW50LCBzdCwgXCJFeHByZXNzaW9uXCIpO1xufTtcbmJhc2UuVHJ5U3RhdGVtZW50ID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIGMobm9kZS5ibG9jaywgc3QsIFwiU3RhdGVtZW50XCIpO1xuICBpZiAobm9kZS5oYW5kbGVyKSBjKG5vZGUuaGFuZGxlci5ib2R5LCBzdCwgXCJTY29wZUJvZHlcIik7XG4gIGlmIChub2RlLmZpbmFsaXplcikgYyhub2RlLmZpbmFsaXplciwgc3QsIFwiU3RhdGVtZW50XCIpO1xufTtcbmJhc2UuV2hpbGVTdGF0ZW1lbnQgPSBiYXNlLkRvV2hpbGVTdGF0ZW1lbnQgPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgYyhub2RlLnRlc3QsIHN0LCBcIkV4cHJlc3Npb25cIik7XG4gIGMobm9kZS5ib2R5LCBzdCwgXCJTdGF0ZW1lbnRcIik7XG59O1xuYmFzZS5Gb3JTdGF0ZW1lbnQgPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgaWYgKG5vZGUuaW5pdCkgYyhub2RlLmluaXQsIHN0LCBcIkZvckluaXRcIik7XG4gIGlmIChub2RlLnRlc3QpIGMobm9kZS50ZXN0LCBzdCwgXCJFeHByZXNzaW9uXCIpO1xuICBpZiAobm9kZS51cGRhdGUpIGMobm9kZS51cGRhdGUsIHN0LCBcIkV4cHJlc3Npb25cIik7XG4gIGMobm9kZS5ib2R5LCBzdCwgXCJTdGF0ZW1lbnRcIik7XG59O1xuYmFzZS5Gb3JJblN0YXRlbWVudCA9IGJhc2UuRm9yT2ZTdGF0ZW1lbnQgPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgYyhub2RlLmxlZnQsIHN0LCBcIkZvckluaXRcIik7XG4gIGMobm9kZS5yaWdodCwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbiAgYyhub2RlLmJvZHksIHN0LCBcIlN0YXRlbWVudFwiKTtcbn07XG5iYXNlLkZvckluaXQgPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgaWYgKG5vZGUudHlwZSA9PSBcIlZhcmlhYmxlRGVjbGFyYXRpb25cIikgYyhub2RlLCBzdCk7ZWxzZSBjKG5vZGUsIHN0LCBcIkV4cHJlc3Npb25cIik7XG59O1xuYmFzZS5EZWJ1Z2dlclN0YXRlbWVudCA9IGlnbm9yZTtcblxuYmFzZS5GdW5jdGlvbkRlY2xhcmF0aW9uID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIHJldHVybiBjKG5vZGUsIHN0LCBcIkZ1bmN0aW9uXCIpO1xufTtcbmJhc2UuVmFyaWFibGVEZWNsYXJhdGlvbiA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBmb3IgKHZhciBpID0gMDsgaSA8IG5vZGUuZGVjbGFyYXRpb25zLmxlbmd0aDsgKytpKSB7XG4gICAgdmFyIGRlY2wgPSBub2RlLmRlY2xhcmF0aW9uc1tpXTtcbiAgICBpZiAoZGVjbC5pbml0KSBjKGRlY2wuaW5pdCwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbiAgfVxufTtcblxuYmFzZS5GdW5jdGlvbiA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICByZXR1cm4gYyhub2RlLmJvZHksIHN0LCBcIlNjb3BlQm9keVwiKTtcbn07XG5iYXNlLlNjb3BlQm9keSA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICByZXR1cm4gYyhub2RlLCBzdCwgXCJTdGF0ZW1lbnRcIik7XG59O1xuXG5iYXNlLkV4cHJlc3Npb24gPSBza2lwVGhyb3VnaDtcbmJhc2UuVGhpc0V4cHJlc3Npb24gPSBiYXNlLlN1cGVyID0gYmFzZS5NZXRhUHJvcGVydHkgPSBpZ25vcmU7XG5iYXNlLkFycmF5RXhwcmVzc2lvbiA9IGJhc2UuQXJyYXlQYXR0ZXJuID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIGZvciAodmFyIGkgPSAwOyBpIDwgbm9kZS5lbGVtZW50cy5sZW5ndGg7ICsraSkge1xuICAgIHZhciBlbHQgPSBub2RlLmVsZW1lbnRzW2ldO1xuICAgIGlmIChlbHQpIGMoZWx0LCBzdCwgXCJFeHByZXNzaW9uXCIpO1xuICB9XG59O1xuYmFzZS5PYmplY3RFeHByZXNzaW9uID0gYmFzZS5PYmplY3RQYXR0ZXJuID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIGZvciAodmFyIGkgPSAwOyBpIDwgbm9kZS5wcm9wZXJ0aWVzLmxlbmd0aDsgKytpKSB7XG4gICAgYyhub2RlLnByb3BlcnRpZXNbaV0sIHN0KTtcbiAgfVxufTtcbmJhc2UuRnVuY3Rpb25FeHByZXNzaW9uID0gYmFzZS5BcnJvd0Z1bmN0aW9uRXhwcmVzc2lvbiA9IGJhc2UuRnVuY3Rpb25EZWNsYXJhdGlvbjtcbmJhc2UuU2VxdWVuY2VFeHByZXNzaW9uID0gYmFzZS5UZW1wbGF0ZUxpdGVyYWwgPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgZm9yICh2YXIgaSA9IDA7IGkgPCBub2RlLmV4cHJlc3Npb25zLmxlbmd0aDsgKytpKSB7XG4gICAgYyhub2RlLmV4cHJlc3Npb25zW2ldLCBzdCwgXCJFeHByZXNzaW9uXCIpO1xuICB9XG59O1xuYmFzZS5VbmFyeUV4cHJlc3Npb24gPSBiYXNlLlVwZGF0ZUV4cHJlc3Npb24gPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgYyhub2RlLmFyZ3VtZW50LCBzdCwgXCJFeHByZXNzaW9uXCIpO1xufTtcbmJhc2UuQmluYXJ5RXhwcmVzc2lvbiA9IGJhc2UuQXNzaWdubWVudEV4cHJlc3Npb24gPSBiYXNlLkFzc2lnbm1lbnRQYXR0ZXJuID0gYmFzZS5Mb2dpY2FsRXhwcmVzc2lvbiA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBjKG5vZGUubGVmdCwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbiAgYyhub2RlLnJpZ2h0LCBzdCwgXCJFeHByZXNzaW9uXCIpO1xufTtcbmJhc2UuQ29uZGl0aW9uYWxFeHByZXNzaW9uID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIGMobm9kZS50ZXN0LCBzdCwgXCJFeHByZXNzaW9uXCIpO1xuICBjKG5vZGUuY29uc2VxdWVudCwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbiAgYyhub2RlLmFsdGVybmF0ZSwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbn07XG5iYXNlLk5ld0V4cHJlc3Npb24gPSBiYXNlLkNhbGxFeHByZXNzaW9uID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIGMobm9kZS5jYWxsZWUsIHN0LCBcIkV4cHJlc3Npb25cIik7XG4gIGlmIChub2RlLmFyZ3VtZW50cykgZm9yICh2YXIgaSA9IDA7IGkgPCBub2RlLmFyZ3VtZW50cy5sZW5ndGg7ICsraSkge1xuICAgIGMobm9kZS5hcmd1bWVudHNbaV0sIHN0LCBcIkV4cHJlc3Npb25cIik7XG4gIH1cbn07XG5iYXNlLk1lbWJlckV4cHJlc3Npb24gPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgYyhub2RlLm9iamVjdCwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbiAgaWYgKG5vZGUuY29tcHV0ZWQpIGMobm9kZS5wcm9wZXJ0eSwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbn07XG5iYXNlLkV4cG9ydE5hbWVkRGVjbGFyYXRpb24gPSBiYXNlLkV4cG9ydERlZmF1bHREZWNsYXJhdGlvbiA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICByZXR1cm4gYyhub2RlLmRlY2xhcmF0aW9uLCBzdCk7XG59O1xuYmFzZS5JbXBvcnREZWNsYXJhdGlvbiA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBmb3IgKHZhciBpID0gMDsgaSA8IG5vZGUuc3BlY2lmaWVycy5sZW5ndGg7IGkrKykge1xuICAgIGMobm9kZS5zcGVjaWZpZXJzW2ldLCBzdCk7XG4gIH1cbn07XG5iYXNlLkltcG9ydFNwZWNpZmllciA9IGJhc2UuSW1wb3J0RGVmYXVsdFNwZWNpZmllciA9IGJhc2UuSW1wb3J0TmFtZXNwYWNlU3BlY2lmaWVyID0gYmFzZS5JZGVudGlmaWVyID0gYmFzZS5MaXRlcmFsID0gaWdub3JlO1xuXG5iYXNlLlRhZ2dlZFRlbXBsYXRlRXhwcmVzc2lvbiA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBjKG5vZGUudGFnLCBzdCwgXCJFeHByZXNzaW9uXCIpO1xuICBjKG5vZGUucXVhc2ksIHN0KTtcbn07XG5iYXNlLkNsYXNzRGVjbGFyYXRpb24gPSBiYXNlLkNsYXNzRXhwcmVzc2lvbiA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBpZiAobm9kZS5zdXBlckNsYXNzKSBjKG5vZGUuc3VwZXJDbGFzcywgc3QsIFwiRXhwcmVzc2lvblwiKTtcbiAgZm9yICh2YXIgaSA9IDA7IGkgPCBub2RlLmJvZHkuYm9keS5sZW5ndGg7IGkrKykge1xuICAgIGMobm9kZS5ib2R5LmJvZHlbaV0sIHN0KTtcbiAgfVxufTtcbmJhc2UuTWV0aG9kRGVmaW5pdGlvbiA9IGJhc2UuUHJvcGVydHkgPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgaWYgKG5vZGUuY29tcHV0ZWQpIGMobm9kZS5rZXksIHN0LCBcIkV4cHJlc3Npb25cIik7XG4gIGMobm9kZS52YWx1ZSwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbn07XG5iYXNlLkNvbXByZWhlbnNpb25FeHByZXNzaW9uID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIGZvciAodmFyIGkgPSAwOyBpIDwgbm9kZS5ibG9ja3MubGVuZ3RoOyBpKyspIHtcbiAgICBjKG5vZGUuYmxvY2tzW2ldLnJpZ2h0LCBzdCwgXCJFeHByZXNzaW9uXCIpO1xuICB9Yyhub2RlLmJvZHksIHN0LCBcIkV4cHJlc3Npb25cIik7XG59O1xuXG59LHt9XX0se30sWzFdKSgxKVxufSk7IiwiaWYgKHR5cGVvZiBPYmplY3QuY3JlYXRlID09PSAnZnVuY3Rpb24nKSB7XG4gIC8vIGltcGxlbWVudGF0aW9uIGZyb20gc3RhbmRhcmQgbm9kZS5qcyAndXRpbCcgbW9kdWxlXG4gIG1vZHVsZS5leHBvcnRzID0gZnVuY3Rpb24gaW5oZXJpdHMoY3Rvciwgc3VwZXJDdG9yKSB7XG4gICAgY3Rvci5zdXBlcl8gPSBzdXBlckN0b3JcbiAgICBjdG9yLnByb3RvdHlwZSA9IE9iamVjdC5jcmVhdGUoc3VwZXJDdG9yLnByb3RvdHlwZSwge1xuICAgICAgY29uc3RydWN0b3I6IHtcbiAgICAgICAgdmFsdWU6IGN0b3IsXG4gICAgICAgIGVudW1lcmFibGU6IGZhbHNlLFxuICAgICAgICB3cml0YWJsZTogdHJ1ZSxcbiAgICAgICAgY29uZmlndXJhYmxlOiB0cnVlXG4gICAgICB9XG4gICAgfSk7XG4gIH07XG59IGVsc2Uge1xuICAvLyBvbGQgc2Nob29sIHNoaW0gZm9yIG9sZCBicm93c2Vyc1xuICBtb2R1bGUuZXhwb3J0cyA9IGZ1bmN0aW9uIGluaGVyaXRzKGN0b3IsIHN1cGVyQ3Rvcikge1xuICAgIGN0b3Iuc3VwZXJfID0gc3VwZXJDdG9yXG4gICAgdmFyIFRlbXBDdG9yID0gZnVuY3Rpb24gKCkge31cbiAgICBUZW1wQ3Rvci5wcm90b3R5cGUgPSBzdXBlckN0b3IucHJvdG90eXBlXG4gICAgY3Rvci5wcm90b3R5cGUgPSBuZXcgVGVtcEN0b3IoKVxuICAgIGN0b3IucHJvdG90eXBlLmNvbnN0cnVjdG9yID0gY3RvclxuICB9XG59XG4iLCIvLyBzaGltIGZvciB1c2luZyBwcm9jZXNzIGluIGJyb3dzZXJcblxudmFyIHByb2Nlc3MgPSBtb2R1bGUuZXhwb3J0cyA9IHt9O1xudmFyIHF1ZXVlID0gW107XG52YXIgZHJhaW5pbmcgPSBmYWxzZTtcbnZhciBjdXJyZW50UXVldWU7XG52YXIgcXVldWVJbmRleCA9IC0xO1xuXG5mdW5jdGlvbiBjbGVhblVwTmV4dFRpY2soKSB7XG4gICAgZHJhaW5pbmcgPSBmYWxzZTtcbiAgICBpZiAoY3VycmVudFF1ZXVlLmxlbmd0aCkge1xuICAgICAgICBxdWV1ZSA9IGN1cnJlbnRRdWV1ZS5jb25jYXQocXVldWUpO1xuICAgIH0gZWxzZSB7XG4gICAgICAgIHF1ZXVlSW5kZXggPSAtMTtcbiAgICB9XG4gICAgaWYgKHF1ZXVlLmxlbmd0aCkge1xuICAgICAgICBkcmFpblF1ZXVlKCk7XG4gICAgfVxufVxuXG5mdW5jdGlvbiBkcmFpblF1ZXVlKCkge1xuICAgIGlmIChkcmFpbmluZykge1xuICAgICAgICByZXR1cm47XG4gICAgfVxuICAgIHZhciB0aW1lb3V0ID0gc2V0VGltZW91dChjbGVhblVwTmV4dFRpY2spO1xuICAgIGRyYWluaW5nID0gdHJ1ZTtcblxuICAgIHZhciBsZW4gPSBxdWV1ZS5sZW5ndGg7XG4gICAgd2hpbGUobGVuKSB7XG4gICAgICAgIGN1cnJlbnRRdWV1ZSA9IHF1ZXVlO1xuICAgICAgICBxdWV1ZSA9IFtdO1xuICAgICAgICB3aGlsZSAoKytxdWV1ZUluZGV4IDwgbGVuKSB7XG4gICAgICAgICAgICBjdXJyZW50UXVldWVbcXVldWVJbmRleF0ucnVuKCk7XG4gICAgICAgIH1cbiAgICAgICAgcXVldWVJbmRleCA9IC0xO1xuICAgICAgICBsZW4gPSBxdWV1ZS5sZW5ndGg7XG4gICAgfVxuICAgIGN1cnJlbnRRdWV1ZSA9IG51bGw7XG4gICAgZHJhaW5pbmcgPSBmYWxzZTtcbiAgICBjbGVhclRpbWVvdXQodGltZW91dCk7XG59XG5cbnByb2Nlc3MubmV4dFRpY2sgPSBmdW5jdGlvbiAoZnVuKSB7XG4gICAgdmFyIGFyZ3MgPSBuZXcgQXJyYXkoYXJndW1lbnRzLmxlbmd0aCAtIDEpO1xuICAgIGlmIChhcmd1bWVudHMubGVuZ3RoID4gMSkge1xuICAgICAgICBmb3IgKHZhciBpID0gMTsgaSA8IGFyZ3VtZW50cy5sZW5ndGg7IGkrKykge1xuICAgICAgICAgICAgYXJnc1tpIC0gMV0gPSBhcmd1bWVudHNbaV07XG4gICAgICAgIH1cbiAgICB9XG4gICAgcXVldWUucHVzaChuZXcgSXRlbShmdW4sIGFyZ3MpKTtcbiAgICBpZiAocXVldWUubGVuZ3RoID09PSAxICYmICFkcmFpbmluZykge1xuICAgICAgICBzZXRUaW1lb3V0KGRyYWluUXVldWUsIDApO1xuICAgIH1cbn07XG5cbi8vIHY4IGxpa2VzIHByZWRpY3RpYmxlIG9iamVjdHNcbmZ1bmN0aW9uIEl0ZW0oZnVuLCBhcnJheSkge1xuICAgIHRoaXMuZnVuID0gZnVuO1xuICAgIHRoaXMuYXJyYXkgPSBhcnJheTtcbn1cbkl0ZW0ucHJvdG90eXBlLnJ1biA9IGZ1bmN0aW9uICgpIHtcbiAgICB0aGlzLmZ1bi5hcHBseShudWxsLCB0aGlzLmFycmF5KTtcbn07XG5wcm9jZXNzLnRpdGxlID0gJ2Jyb3dzZXInO1xucHJvY2Vzcy5icm93c2VyID0gdHJ1ZTtcbnByb2Nlc3MuZW52ID0ge307XG5wcm9jZXNzLmFyZ3YgPSBbXTtcbnByb2Nlc3MudmVyc2lvbiA9ICcnOyAvLyBlbXB0eSBzdHJpbmcgdG8gYXZvaWQgcmVnZXhwIGlzc3Vlc1xucHJvY2Vzcy52ZXJzaW9ucyA9IHt9O1xuXG5mdW5jdGlvbiBub29wKCkge31cblxucHJvY2Vzcy5vbiA9IG5vb3A7XG5wcm9jZXNzLmFkZExpc3RlbmVyID0gbm9vcDtcbnByb2Nlc3Mub25jZSA9IG5vb3A7XG5wcm9jZXNzLm9mZiA9IG5vb3A7XG5wcm9jZXNzLnJlbW92ZUxpc3RlbmVyID0gbm9vcDtcbnByb2Nlc3MucmVtb3ZlQWxsTGlzdGVuZXJzID0gbm9vcDtcbnByb2Nlc3MuZW1pdCA9IG5vb3A7XG5cbnByb2Nlc3MuYmluZGluZyA9IGZ1bmN0aW9uIChuYW1lKSB7XG4gICAgdGhyb3cgbmV3IEVycm9yKCdwcm9jZXNzLmJpbmRpbmcgaXMgbm90IHN1cHBvcnRlZCcpO1xufTtcblxuLy8gVE9ETyhzaHR5bG1hbilcbnByb2Nlc3MuY3dkID0gZnVuY3Rpb24gKCkgeyByZXR1cm4gJy8nIH07XG5wcm9jZXNzLmNoZGlyID0gZnVuY3Rpb24gKGRpcikge1xuICAgIHRocm93IG5ldyBFcnJvcigncHJvY2Vzcy5jaGRpciBpcyBub3Qgc3VwcG9ydGVkJyk7XG59O1xucHJvY2Vzcy51bWFzayA9IGZ1bmN0aW9uKCkgeyByZXR1cm4gMDsgfTtcbiIsIm1vZHVsZS5leHBvcnRzID0gZnVuY3Rpb24gaXNCdWZmZXIoYXJnKSB7XG4gIHJldHVybiBhcmcgJiYgdHlwZW9mIGFyZyA9PT0gJ29iamVjdCdcbiAgICAmJiB0eXBlb2YgYXJnLmNvcHkgPT09ICdmdW5jdGlvbidcbiAgICAmJiB0eXBlb2YgYXJnLmZpbGwgPT09ICdmdW5jdGlvbidcbiAgICAmJiB0eXBlb2YgYXJnLnJlYWRVSW50OCA9PT0gJ2Z1bmN0aW9uJztcbn0iLCIvLyBDb3B5cmlnaHQgSm95ZW50LCBJbmMuIGFuZCBvdGhlciBOb2RlIGNvbnRyaWJ1dG9ycy5cbi8vXG4vLyBQZXJtaXNzaW9uIGlzIGhlcmVieSBncmFudGVkLCBmcmVlIG9mIGNoYXJnZSwgdG8gYW55IHBlcnNvbiBvYnRhaW5pbmcgYVxuLy8gY29weSBvZiB0aGlzIHNvZnR3YXJlIGFuZCBhc3NvY2lhdGVkIGRvY3VtZW50YXRpb24gZmlsZXMgKHRoZVxuLy8gXCJTb2Z0d2FyZVwiKSwgdG8gZGVhbCBpbiB0aGUgU29mdHdhcmUgd2l0aG91dCByZXN0cmljdGlvbiwgaW5jbHVkaW5nXG4vLyB3aXRob3V0IGxpbWl0YXRpb24gdGhlIHJpZ2h0cyB0byB1c2UsIGNvcHksIG1vZGlmeSwgbWVyZ2UsIHB1Ymxpc2gsXG4vLyBkaXN0cmlidXRlLCBzdWJsaWNlbnNlLCBhbmQvb3Igc2VsbCBjb3BpZXMgb2YgdGhlIFNvZnR3YXJlLCBhbmQgdG8gcGVybWl0XG4vLyBwZXJzb25zIHRvIHdob20gdGhlIFNvZnR3YXJlIGlzIGZ1cm5pc2hlZCB0byBkbyBzbywgc3ViamVjdCB0byB0aGVcbi8vIGZvbGxvd2luZyBjb25kaXRpb25zOlxuLy9cbi8vIFRoZSBhYm92ZSBjb3B5cmlnaHQgbm90aWNlIGFuZCB0aGlzIHBlcm1pc3Npb24gbm90aWNlIHNoYWxsIGJlIGluY2x1ZGVkXG4vLyBpbiBhbGwgY29waWVzIG9yIHN1YnN0YW50aWFsIHBvcnRpb25zIG9mIHRoZSBTb2Z0d2FyZS5cbi8vXG4vLyBUSEUgU09GVFdBUkUgSVMgUFJPVklERUQgXCJBUyBJU1wiLCBXSVRIT1VUIFdBUlJBTlRZIE9GIEFOWSBLSU5ELCBFWFBSRVNTXG4vLyBPUiBJTVBMSUVELCBJTkNMVURJTkcgQlVUIE5PVCBMSU1JVEVEIFRPIFRIRSBXQVJSQU5USUVTIE9GXG4vLyBNRVJDSEFOVEFCSUxJVFksIEZJVE5FU1MgRk9SIEEgUEFSVElDVUxBUiBQVVJQT1NFIEFORCBOT05JTkZSSU5HRU1FTlQuIElOXG4vLyBOTyBFVkVOVCBTSEFMTCBUSEUgQVVUSE9SUyBPUiBDT1BZUklHSFQgSE9MREVSUyBCRSBMSUFCTEUgRk9SIEFOWSBDTEFJTSxcbi8vIERBTUFHRVMgT1IgT1RIRVIgTElBQklMSVRZLCBXSEVUSEVSIElOIEFOIEFDVElPTiBPRiBDT05UUkFDVCwgVE9SVCBPUlxuLy8gT1RIRVJXSVNFLCBBUklTSU5HIEZST00sIE9VVCBPRiBPUiBJTiBDT05ORUNUSU9OIFdJVEggVEhFIFNPRlRXQVJFIE9SIFRIRVxuLy8gVVNFIE9SIE9USEVSIERFQUxJTkdTIElOIFRIRSBTT0ZUV0FSRS5cblxudmFyIGZvcm1hdFJlZ0V4cCA9IC8lW3NkaiVdL2c7XG5leHBvcnRzLmZvcm1hdCA9IGZ1bmN0aW9uKGYpIHtcbiAgaWYgKCFpc1N0cmluZyhmKSkge1xuICAgIHZhciBvYmplY3RzID0gW107XG4gICAgZm9yICh2YXIgaSA9IDA7IGkgPCBhcmd1bWVudHMubGVuZ3RoOyBpKyspIHtcbiAgICAgIG9iamVjdHMucHVzaChpbnNwZWN0KGFyZ3VtZW50c1tpXSkpO1xuICAgIH1cbiAgICByZXR1cm4gb2JqZWN0cy5qb2luKCcgJyk7XG4gIH1cblxuICB2YXIgaSA9IDE7XG4gIHZhciBhcmdzID0gYXJndW1lbnRzO1xuICB2YXIgbGVuID0gYXJncy5sZW5ndGg7XG4gIHZhciBzdHIgPSBTdHJpbmcoZikucmVwbGFjZShmb3JtYXRSZWdFeHAsIGZ1bmN0aW9uKHgpIHtcbiAgICBpZiAoeCA9PT0gJyUlJykgcmV0dXJuICclJztcbiAgICBpZiAoaSA+PSBsZW4pIHJldHVybiB4O1xuICAgIHN3aXRjaCAoeCkge1xuICAgICAgY2FzZSAnJXMnOiByZXR1cm4gU3RyaW5nKGFyZ3NbaSsrXSk7XG4gICAgICBjYXNlICclZCc6IHJldHVybiBOdW1iZXIoYXJnc1tpKytdKTtcbiAgICAgIGNhc2UgJyVqJzpcbiAgICAgICAgdHJ5IHtcbiAgICAgICAgICByZXR1cm4gSlNPTi5zdHJpbmdpZnkoYXJnc1tpKytdKTtcbiAgICAgICAgfSBjYXRjaCAoXykge1xuICAgICAgICAgIHJldHVybiAnW0NpcmN1bGFyXSc7XG4gICAgICAgIH1cbiAgICAgIGRlZmF1bHQ6XG4gICAgICAgIHJldHVybiB4O1xuICAgIH1cbiAgfSk7XG4gIGZvciAodmFyIHggPSBhcmdzW2ldOyBpIDwgbGVuOyB4ID0gYXJnc1srK2ldKSB7XG4gICAgaWYgKGlzTnVsbCh4KSB8fCAhaXNPYmplY3QoeCkpIHtcbiAgICAgIHN0ciArPSAnICcgKyB4O1xuICAgIH0gZWxzZSB7XG4gICAgICBzdHIgKz0gJyAnICsgaW5zcGVjdCh4KTtcbiAgICB9XG4gIH1cbiAgcmV0dXJuIHN0cjtcbn07XG5cblxuLy8gTWFyayB0aGF0IGEgbWV0aG9kIHNob3VsZCBub3QgYmUgdXNlZC5cbi8vIFJldHVybnMgYSBtb2RpZmllZCBmdW5jdGlvbiB3aGljaCB3YXJucyBvbmNlIGJ5IGRlZmF1bHQuXG4vLyBJZiAtLW5vLWRlcHJlY2F0aW9uIGlzIHNldCwgdGhlbiBpdCBpcyBhIG5vLW9wLlxuZXhwb3J0cy5kZXByZWNhdGUgPSBmdW5jdGlvbihmbiwgbXNnKSB7XG4gIC8vIEFsbG93IGZvciBkZXByZWNhdGluZyB0aGluZ3MgaW4gdGhlIHByb2Nlc3Mgb2Ygc3RhcnRpbmcgdXAuXG4gIGlmIChpc1VuZGVmaW5lZChnbG9iYWwucHJvY2VzcykpIHtcbiAgICByZXR1cm4gZnVuY3Rpb24oKSB7XG4gICAgICByZXR1cm4gZXhwb3J0cy5kZXByZWNhdGUoZm4sIG1zZykuYXBwbHkodGhpcywgYXJndW1lbnRzKTtcbiAgICB9O1xuICB9XG5cbiAgaWYgKHByb2Nlc3Mubm9EZXByZWNhdGlvbiA9PT0gdHJ1ZSkge1xuICAgIHJldHVybiBmbjtcbiAgfVxuXG4gIHZhciB3YXJuZWQgPSBmYWxzZTtcbiAgZnVuY3Rpb24gZGVwcmVjYXRlZCgpIHtcbiAgICBpZiAoIXdhcm5lZCkge1xuICAgICAgaWYgKHByb2Nlc3MudGhyb3dEZXByZWNhdGlvbikge1xuICAgICAgICB0aHJvdyBuZXcgRXJyb3IobXNnKTtcbiAgICAgIH0gZWxzZSBpZiAocHJvY2Vzcy50cmFjZURlcHJlY2F0aW9uKSB7XG4gICAgICAgIGNvbnNvbGUudHJhY2UobXNnKTtcbiAgICAgIH0gZWxzZSB7XG4gICAgICAgIGNvbnNvbGUuZXJyb3IobXNnKTtcbiAgICAgIH1cbiAgICAgIHdhcm5lZCA9IHRydWU7XG4gICAgfVxuICAgIHJldHVybiBmbi5hcHBseSh0aGlzLCBhcmd1bWVudHMpO1xuICB9XG5cbiAgcmV0dXJuIGRlcHJlY2F0ZWQ7XG59O1xuXG5cbnZhciBkZWJ1Z3MgPSB7fTtcbnZhciBkZWJ1Z0Vudmlyb247XG5leHBvcnRzLmRlYnVnbG9nID0gZnVuY3Rpb24oc2V0KSB7XG4gIGlmIChpc1VuZGVmaW5lZChkZWJ1Z0Vudmlyb24pKVxuICAgIGRlYnVnRW52aXJvbiA9IHByb2Nlc3MuZW52Lk5PREVfREVCVUcgfHwgJyc7XG4gIHNldCA9IHNldC50b1VwcGVyQ2FzZSgpO1xuICBpZiAoIWRlYnVnc1tzZXRdKSB7XG4gICAgaWYgKG5ldyBSZWdFeHAoJ1xcXFxiJyArIHNldCArICdcXFxcYicsICdpJykudGVzdChkZWJ1Z0Vudmlyb24pKSB7XG4gICAgICB2YXIgcGlkID0gcHJvY2Vzcy5waWQ7XG4gICAgICBkZWJ1Z3Nbc2V0XSA9IGZ1bmN0aW9uKCkge1xuICAgICAgICB2YXIgbXNnID0gZXhwb3J0cy5mb3JtYXQuYXBwbHkoZXhwb3J0cywgYXJndW1lbnRzKTtcbiAgICAgICAgY29uc29sZS5lcnJvcignJXMgJWQ6ICVzJywgc2V0LCBwaWQsIG1zZyk7XG4gICAgICB9O1xuICAgIH0gZWxzZSB7XG4gICAgICBkZWJ1Z3Nbc2V0XSA9IGZ1bmN0aW9uKCkge307XG4gICAgfVxuICB9XG4gIHJldHVybiBkZWJ1Z3Nbc2V0XTtcbn07XG5cblxuLyoqXG4gKiBFY2hvcyB0aGUgdmFsdWUgb2YgYSB2YWx1ZS4gVHJ5cyB0byBwcmludCB0aGUgdmFsdWUgb3V0XG4gKiBpbiB0aGUgYmVzdCB3YXkgcG9zc2libGUgZ2l2ZW4gdGhlIGRpZmZlcmVudCB0eXBlcy5cbiAqXG4gKiBAcGFyYW0ge09iamVjdH0gb2JqIFRoZSBvYmplY3QgdG8gcHJpbnQgb3V0LlxuICogQHBhcmFtIHtPYmplY3R9IG9wdHMgT3B0aW9uYWwgb3B0aW9ucyBvYmplY3QgdGhhdCBhbHRlcnMgdGhlIG91dHB1dC5cbiAqL1xuLyogbGVnYWN5OiBvYmosIHNob3dIaWRkZW4sIGRlcHRoLCBjb2xvcnMqL1xuZnVuY3Rpb24gaW5zcGVjdChvYmosIG9wdHMpIHtcbiAgLy8gZGVmYXVsdCBvcHRpb25zXG4gIHZhciBjdHggPSB7XG4gICAgc2VlbjogW10sXG4gICAgc3R5bGl6ZTogc3R5bGl6ZU5vQ29sb3JcbiAgfTtcbiAgLy8gbGVnYWN5Li4uXG4gIGlmIChhcmd1bWVudHMubGVuZ3RoID49IDMpIGN0eC5kZXB0aCA9IGFyZ3VtZW50c1syXTtcbiAgaWYgKGFyZ3VtZW50cy5sZW5ndGggPj0gNCkgY3R4LmNvbG9ycyA9IGFyZ3VtZW50c1szXTtcbiAgaWYgKGlzQm9vbGVhbihvcHRzKSkge1xuICAgIC8vIGxlZ2FjeS4uLlxuICAgIGN0eC5zaG93SGlkZGVuID0gb3B0cztcbiAgfSBlbHNlIGlmIChvcHRzKSB7XG4gICAgLy8gZ290IGFuIFwib3B0aW9uc1wiIG9iamVjdFxuICAgIGV4cG9ydHMuX2V4dGVuZChjdHgsIG9wdHMpO1xuICB9XG4gIC8vIHNldCBkZWZhdWx0IG9wdGlvbnNcbiAgaWYgKGlzVW5kZWZpbmVkKGN0eC5zaG93SGlkZGVuKSkgY3R4LnNob3dIaWRkZW4gPSBmYWxzZTtcbiAgaWYgKGlzVW5kZWZpbmVkKGN0eC5kZXB0aCkpIGN0eC5kZXB0aCA9IDI7XG4gIGlmIChpc1VuZGVmaW5lZChjdHguY29sb3JzKSkgY3R4LmNvbG9ycyA9IGZhbHNlO1xuICBpZiAoaXNVbmRlZmluZWQoY3R4LmN1c3RvbUluc3BlY3QpKSBjdHguY3VzdG9tSW5zcGVjdCA9IHRydWU7XG4gIGlmIChjdHguY29sb3JzKSBjdHguc3R5bGl6ZSA9IHN0eWxpemVXaXRoQ29sb3I7XG4gIHJldHVybiBmb3JtYXRWYWx1ZShjdHgsIG9iaiwgY3R4LmRlcHRoKTtcbn1cbmV4cG9ydHMuaW5zcGVjdCA9IGluc3BlY3Q7XG5cblxuLy8gaHR0cDovL2VuLndpa2lwZWRpYS5vcmcvd2lraS9BTlNJX2VzY2FwZV9jb2RlI2dyYXBoaWNzXG5pbnNwZWN0LmNvbG9ycyA9IHtcbiAgJ2JvbGQnIDogWzEsIDIyXSxcbiAgJ2l0YWxpYycgOiBbMywgMjNdLFxuICAndW5kZXJsaW5lJyA6IFs0LCAyNF0sXG4gICdpbnZlcnNlJyA6IFs3LCAyN10sXG4gICd3aGl0ZScgOiBbMzcsIDM5XSxcbiAgJ2dyZXknIDogWzkwLCAzOV0sXG4gICdibGFjaycgOiBbMzAsIDM5XSxcbiAgJ2JsdWUnIDogWzM0LCAzOV0sXG4gICdjeWFuJyA6IFszNiwgMzldLFxuICAnZ3JlZW4nIDogWzMyLCAzOV0sXG4gICdtYWdlbnRhJyA6IFszNSwgMzldLFxuICAncmVkJyA6IFszMSwgMzldLFxuICAneWVsbG93JyA6IFszMywgMzldXG59O1xuXG4vLyBEb24ndCB1c2UgJ2JsdWUnIG5vdCB2aXNpYmxlIG9uIGNtZC5leGVcbmluc3BlY3Quc3R5bGVzID0ge1xuICAnc3BlY2lhbCc6ICdjeWFuJyxcbiAgJ251bWJlcic6ICd5ZWxsb3cnLFxuICAnYm9vbGVhbic6ICd5ZWxsb3cnLFxuICAndW5kZWZpbmVkJzogJ2dyZXknLFxuICAnbnVsbCc6ICdib2xkJyxcbiAgJ3N0cmluZyc6ICdncmVlbicsXG4gICdkYXRlJzogJ21hZ2VudGEnLFxuICAvLyBcIm5hbWVcIjogaW50ZW50aW9uYWxseSBub3Qgc3R5bGluZ1xuICAncmVnZXhwJzogJ3JlZCdcbn07XG5cblxuZnVuY3Rpb24gc3R5bGl6ZVdpdGhDb2xvcihzdHIsIHN0eWxlVHlwZSkge1xuICB2YXIgc3R5bGUgPSBpbnNwZWN0LnN0eWxlc1tzdHlsZVR5cGVdO1xuXG4gIGlmIChzdHlsZSkge1xuICAgIHJldHVybiAnXFx1MDAxYlsnICsgaW5zcGVjdC5jb2xvcnNbc3R5bGVdWzBdICsgJ20nICsgc3RyICtcbiAgICAgICAgICAgJ1xcdTAwMWJbJyArIGluc3BlY3QuY29sb3JzW3N0eWxlXVsxXSArICdtJztcbiAgfSBlbHNlIHtcbiAgICByZXR1cm4gc3RyO1xuICB9XG59XG5cblxuZnVuY3Rpb24gc3R5bGl6ZU5vQ29sb3Ioc3RyLCBzdHlsZVR5cGUpIHtcbiAgcmV0dXJuIHN0cjtcbn1cblxuXG5mdW5jdGlvbiBhcnJheVRvSGFzaChhcnJheSkge1xuICB2YXIgaGFzaCA9IHt9O1xuXG4gIGFycmF5LmZvckVhY2goZnVuY3Rpb24odmFsLCBpZHgpIHtcbiAgICBoYXNoW3ZhbF0gPSB0cnVlO1xuICB9KTtcblxuICByZXR1cm4gaGFzaDtcbn1cblxuXG5mdW5jdGlvbiBmb3JtYXRWYWx1ZShjdHgsIHZhbHVlLCByZWN1cnNlVGltZXMpIHtcbiAgLy8gUHJvdmlkZSBhIGhvb2sgZm9yIHVzZXItc3BlY2lmaWVkIGluc3BlY3QgZnVuY3Rpb25zLlxuICAvLyBDaGVjayB0aGF0IHZhbHVlIGlzIGFuIG9iamVjdCB3aXRoIGFuIGluc3BlY3QgZnVuY3Rpb24gb24gaXRcbiAgaWYgKGN0eC5jdXN0b21JbnNwZWN0ICYmXG4gICAgICB2YWx1ZSAmJlxuICAgICAgaXNGdW5jdGlvbih2YWx1ZS5pbnNwZWN0KSAmJlxuICAgICAgLy8gRmlsdGVyIG91dCB0aGUgdXRpbCBtb2R1bGUsIGl0J3MgaW5zcGVjdCBmdW5jdGlvbiBpcyBzcGVjaWFsXG4gICAgICB2YWx1ZS5pbnNwZWN0ICE9PSBleHBvcnRzLmluc3BlY3QgJiZcbiAgICAgIC8vIEFsc28gZmlsdGVyIG91dCBhbnkgcHJvdG90eXBlIG9iamVjdHMgdXNpbmcgdGhlIGNpcmN1bGFyIGNoZWNrLlxuICAgICAgISh2YWx1ZS5jb25zdHJ1Y3RvciAmJiB2YWx1ZS5jb25zdHJ1Y3Rvci5wcm90b3R5cGUgPT09IHZhbHVlKSkge1xuICAgIHZhciByZXQgPSB2YWx1ZS5pbnNwZWN0KHJlY3Vyc2VUaW1lcywgY3R4KTtcbiAgICBpZiAoIWlzU3RyaW5nKHJldCkpIHtcbiAgICAgIHJldCA9IGZvcm1hdFZhbHVlKGN0eCwgcmV0LCByZWN1cnNlVGltZXMpO1xuICAgIH1cbiAgICByZXR1cm4gcmV0O1xuICB9XG5cbiAgLy8gUHJpbWl0aXZlIHR5cGVzIGNhbm5vdCBoYXZlIHByb3BlcnRpZXNcbiAgdmFyIHByaW1pdGl2ZSA9IGZvcm1hdFByaW1pdGl2ZShjdHgsIHZhbHVlKTtcbiAgaWYgKHByaW1pdGl2ZSkge1xuICAgIHJldHVybiBwcmltaXRpdmU7XG4gIH1cblxuICAvLyBMb29rIHVwIHRoZSBrZXlzIG9mIHRoZSBvYmplY3QuXG4gIHZhciBrZXlzID0gT2JqZWN0LmtleXModmFsdWUpO1xuICB2YXIgdmlzaWJsZUtleXMgPSBhcnJheVRvSGFzaChrZXlzKTtcblxuICBpZiAoY3R4LnNob3dIaWRkZW4pIHtcbiAgICBrZXlzID0gT2JqZWN0LmdldE93blByb3BlcnR5TmFtZXModmFsdWUpO1xuICB9XG5cbiAgLy8gSUUgZG9lc24ndCBtYWtlIGVycm9yIGZpZWxkcyBub24tZW51bWVyYWJsZVxuICAvLyBodHRwOi8vbXNkbi5taWNyb3NvZnQuY29tL2VuLXVzL2xpYnJhcnkvaWUvZHd3NTJzYnQodj12cy45NCkuYXNweFxuICBpZiAoaXNFcnJvcih2YWx1ZSlcbiAgICAgICYmIChrZXlzLmluZGV4T2YoJ21lc3NhZ2UnKSA+PSAwIHx8IGtleXMuaW5kZXhPZignZGVzY3JpcHRpb24nKSA+PSAwKSkge1xuICAgIHJldHVybiBmb3JtYXRFcnJvcih2YWx1ZSk7XG4gIH1cblxuICAvLyBTb21lIHR5cGUgb2Ygb2JqZWN0IHdpdGhvdXQgcHJvcGVydGllcyBjYW4gYmUgc2hvcnRjdXR0ZWQuXG4gIGlmIChrZXlzLmxlbmd0aCA9PT0gMCkge1xuICAgIGlmIChpc0Z1bmN0aW9uKHZhbHVlKSkge1xuICAgICAgdmFyIG5hbWUgPSB2YWx1ZS5uYW1lID8gJzogJyArIHZhbHVlLm5hbWUgOiAnJztcbiAgICAgIHJldHVybiBjdHguc3R5bGl6ZSgnW0Z1bmN0aW9uJyArIG5hbWUgKyAnXScsICdzcGVjaWFsJyk7XG4gICAgfVxuICAgIGlmIChpc1JlZ0V4cCh2YWx1ZSkpIHtcbiAgICAgIHJldHVybiBjdHguc3R5bGl6ZShSZWdFeHAucHJvdG90eXBlLnRvU3RyaW5nLmNhbGwodmFsdWUpLCAncmVnZXhwJyk7XG4gICAgfVxuICAgIGlmIChpc0RhdGUodmFsdWUpKSB7XG4gICAgICByZXR1cm4gY3R4LnN0eWxpemUoRGF0ZS5wcm90b3R5cGUudG9TdHJpbmcuY2FsbCh2YWx1ZSksICdkYXRlJyk7XG4gICAgfVxuICAgIGlmIChpc0Vycm9yKHZhbHVlKSkge1xuICAgICAgcmV0dXJuIGZvcm1hdEVycm9yKHZhbHVlKTtcbiAgICB9XG4gIH1cblxuICB2YXIgYmFzZSA9ICcnLCBhcnJheSA9IGZhbHNlLCBicmFjZXMgPSBbJ3snLCAnfSddO1xuXG4gIC8vIE1ha2UgQXJyYXkgc2F5IHRoYXQgdGhleSBhcmUgQXJyYXlcbiAgaWYgKGlzQXJyYXkodmFsdWUpKSB7XG4gICAgYXJyYXkgPSB0cnVlO1xuICAgIGJyYWNlcyA9IFsnWycsICddJ107XG4gIH1cblxuICAvLyBNYWtlIGZ1bmN0aW9ucyBzYXkgdGhhdCB0aGV5IGFyZSBmdW5jdGlvbnNcbiAgaWYgKGlzRnVuY3Rpb24odmFsdWUpKSB7XG4gICAgdmFyIG4gPSB2YWx1ZS5uYW1lID8gJzogJyArIHZhbHVlLm5hbWUgOiAnJztcbiAgICBiYXNlID0gJyBbRnVuY3Rpb24nICsgbiArICddJztcbiAgfVxuXG4gIC8vIE1ha2UgUmVnRXhwcyBzYXkgdGhhdCB0aGV5IGFyZSBSZWdFeHBzXG4gIGlmIChpc1JlZ0V4cCh2YWx1ZSkpIHtcbiAgICBiYXNlID0gJyAnICsgUmVnRXhwLnByb3RvdHlwZS50b1N0cmluZy5jYWxsKHZhbHVlKTtcbiAgfVxuXG4gIC8vIE1ha2UgZGF0ZXMgd2l0aCBwcm9wZXJ0aWVzIGZpcnN0IHNheSB0aGUgZGF0ZVxuICBpZiAoaXNEYXRlKHZhbHVlKSkge1xuICAgIGJhc2UgPSAnICcgKyBEYXRlLnByb3RvdHlwZS50b1VUQ1N0cmluZy5jYWxsKHZhbHVlKTtcbiAgfVxuXG4gIC8vIE1ha2UgZXJyb3Igd2l0aCBtZXNzYWdlIGZpcnN0IHNheSB0aGUgZXJyb3JcbiAgaWYgKGlzRXJyb3IodmFsdWUpKSB7XG4gICAgYmFzZSA9ICcgJyArIGZvcm1hdEVycm9yKHZhbHVlKTtcbiAgfVxuXG4gIGlmIChrZXlzLmxlbmd0aCA9PT0gMCAmJiAoIWFycmF5IHx8IHZhbHVlLmxlbmd0aCA9PSAwKSkge1xuICAgIHJldHVybiBicmFjZXNbMF0gKyBiYXNlICsgYnJhY2VzWzFdO1xuICB9XG5cbiAgaWYgKHJlY3Vyc2VUaW1lcyA8IDApIHtcbiAgICBpZiAoaXNSZWdFeHAodmFsdWUpKSB7XG4gICAgICByZXR1cm4gY3R4LnN0eWxpemUoUmVnRXhwLnByb3RvdHlwZS50b1N0cmluZy5jYWxsKHZhbHVlKSwgJ3JlZ2V4cCcpO1xuICAgIH0gZWxzZSB7XG4gICAgICByZXR1cm4gY3R4LnN0eWxpemUoJ1tPYmplY3RdJywgJ3NwZWNpYWwnKTtcbiAgICB9XG4gIH1cblxuICBjdHguc2Vlbi5wdXNoKHZhbHVlKTtcblxuICB2YXIgb3V0cHV0O1xuICBpZiAoYXJyYXkpIHtcbiAgICBvdXRwdXQgPSBmb3JtYXRBcnJheShjdHgsIHZhbHVlLCByZWN1cnNlVGltZXMsIHZpc2libGVLZXlzLCBrZXlzKTtcbiAgfSBlbHNlIHtcbiAgICBvdXRwdXQgPSBrZXlzLm1hcChmdW5jdGlvbihrZXkpIHtcbiAgICAgIHJldHVybiBmb3JtYXRQcm9wZXJ0eShjdHgsIHZhbHVlLCByZWN1cnNlVGltZXMsIHZpc2libGVLZXlzLCBrZXksIGFycmF5KTtcbiAgICB9KTtcbiAgfVxuXG4gIGN0eC5zZWVuLnBvcCgpO1xuXG4gIHJldHVybiByZWR1Y2VUb1NpbmdsZVN0cmluZyhvdXRwdXQsIGJhc2UsIGJyYWNlcyk7XG59XG5cblxuZnVuY3Rpb24gZm9ybWF0UHJpbWl0aXZlKGN0eCwgdmFsdWUpIHtcbiAgaWYgKGlzVW5kZWZpbmVkKHZhbHVlKSlcbiAgICByZXR1cm4gY3R4LnN0eWxpemUoJ3VuZGVmaW5lZCcsICd1bmRlZmluZWQnKTtcbiAgaWYgKGlzU3RyaW5nKHZhbHVlKSkge1xuICAgIHZhciBzaW1wbGUgPSAnXFwnJyArIEpTT04uc3RyaW5naWZ5KHZhbHVlKS5yZXBsYWNlKC9eXCJ8XCIkL2csICcnKVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgLnJlcGxhY2UoLycvZywgXCJcXFxcJ1wiKVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgLnJlcGxhY2UoL1xcXFxcIi9nLCAnXCInKSArICdcXCcnO1xuICAgIHJldHVybiBjdHguc3R5bGl6ZShzaW1wbGUsICdzdHJpbmcnKTtcbiAgfVxuICBpZiAoaXNOdW1iZXIodmFsdWUpKVxuICAgIHJldHVybiBjdHguc3R5bGl6ZSgnJyArIHZhbHVlLCAnbnVtYmVyJyk7XG4gIGlmIChpc0Jvb2xlYW4odmFsdWUpKVxuICAgIHJldHVybiBjdHguc3R5bGl6ZSgnJyArIHZhbHVlLCAnYm9vbGVhbicpO1xuICAvLyBGb3Igc29tZSByZWFzb24gdHlwZW9mIG51bGwgaXMgXCJvYmplY3RcIiwgc28gc3BlY2lhbCBjYXNlIGhlcmUuXG4gIGlmIChpc051bGwodmFsdWUpKVxuICAgIHJldHVybiBjdHguc3R5bGl6ZSgnbnVsbCcsICdudWxsJyk7XG59XG5cblxuZnVuY3Rpb24gZm9ybWF0RXJyb3IodmFsdWUpIHtcbiAgcmV0dXJuICdbJyArIEVycm9yLnByb3RvdHlwZS50b1N0cmluZy5jYWxsKHZhbHVlKSArICddJztcbn1cblxuXG5mdW5jdGlvbiBmb3JtYXRBcnJheShjdHgsIHZhbHVlLCByZWN1cnNlVGltZXMsIHZpc2libGVLZXlzLCBrZXlzKSB7XG4gIHZhciBvdXRwdXQgPSBbXTtcbiAgZm9yICh2YXIgaSA9IDAsIGwgPSB2YWx1ZS5sZW5ndGg7IGkgPCBsOyArK2kpIHtcbiAgICBpZiAoaGFzT3duUHJvcGVydHkodmFsdWUsIFN0cmluZyhpKSkpIHtcbiAgICAgIG91dHB1dC5wdXNoKGZvcm1hdFByb3BlcnR5KGN0eCwgdmFsdWUsIHJlY3Vyc2VUaW1lcywgdmlzaWJsZUtleXMsXG4gICAgICAgICAgU3RyaW5nKGkpLCB0cnVlKSk7XG4gICAgfSBlbHNlIHtcbiAgICAgIG91dHB1dC5wdXNoKCcnKTtcbiAgICB9XG4gIH1cbiAga2V5cy5mb3JFYWNoKGZ1bmN0aW9uKGtleSkge1xuICAgIGlmICgha2V5Lm1hdGNoKC9eXFxkKyQvKSkge1xuICAgICAgb3V0cHV0LnB1c2goZm9ybWF0UHJvcGVydHkoY3R4LCB2YWx1ZSwgcmVjdXJzZVRpbWVzLCB2aXNpYmxlS2V5cyxcbiAgICAgICAgICBrZXksIHRydWUpKTtcbiAgICB9XG4gIH0pO1xuICByZXR1cm4gb3V0cHV0O1xufVxuXG5cbmZ1bmN0aW9uIGZvcm1hdFByb3BlcnR5KGN0eCwgdmFsdWUsIHJlY3Vyc2VUaW1lcywgdmlzaWJsZUtleXMsIGtleSwgYXJyYXkpIHtcbiAgdmFyIG5hbWUsIHN0ciwgZGVzYztcbiAgZGVzYyA9IE9iamVjdC5nZXRPd25Qcm9wZXJ0eURlc2NyaXB0b3IodmFsdWUsIGtleSkgfHwgeyB2YWx1ZTogdmFsdWVba2V5XSB9O1xuICBpZiAoZGVzYy5nZXQpIHtcbiAgICBpZiAoZGVzYy5zZXQpIHtcbiAgICAgIHN0ciA9IGN0eC5zdHlsaXplKCdbR2V0dGVyL1NldHRlcl0nLCAnc3BlY2lhbCcpO1xuICAgIH0gZWxzZSB7XG4gICAgICBzdHIgPSBjdHguc3R5bGl6ZSgnW0dldHRlcl0nLCAnc3BlY2lhbCcpO1xuICAgIH1cbiAgfSBlbHNlIHtcbiAgICBpZiAoZGVzYy5zZXQpIHtcbiAgICAgIHN0ciA9IGN0eC5zdHlsaXplKCdbU2V0dGVyXScsICdzcGVjaWFsJyk7XG4gICAgfVxuICB9XG4gIGlmICghaGFzT3duUHJvcGVydHkodmlzaWJsZUtleXMsIGtleSkpIHtcbiAgICBuYW1lID0gJ1snICsga2V5ICsgJ10nO1xuICB9XG4gIGlmICghc3RyKSB7XG4gICAgaWYgKGN0eC5zZWVuLmluZGV4T2YoZGVzYy52YWx1ZSkgPCAwKSB7XG4gICAgICBpZiAoaXNOdWxsKHJlY3Vyc2VUaW1lcykpIHtcbiAgICAgICAgc3RyID0gZm9ybWF0VmFsdWUoY3R4LCBkZXNjLnZhbHVlLCBudWxsKTtcbiAgICAgIH0gZWxzZSB7XG4gICAgICAgIHN0ciA9IGZvcm1hdFZhbHVlKGN0eCwgZGVzYy52YWx1ZSwgcmVjdXJzZVRpbWVzIC0gMSk7XG4gICAgICB9XG4gICAgICBpZiAoc3RyLmluZGV4T2YoJ1xcbicpID4gLTEpIHtcbiAgICAgICAgaWYgKGFycmF5KSB7XG4gICAgICAgICAgc3RyID0gc3RyLnNwbGl0KCdcXG4nKS5tYXAoZnVuY3Rpb24obGluZSkge1xuICAgICAgICAgICAgcmV0dXJuICcgICcgKyBsaW5lO1xuICAgICAgICAgIH0pLmpvaW4oJ1xcbicpLnN1YnN0cigyKTtcbiAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICBzdHIgPSAnXFxuJyArIHN0ci5zcGxpdCgnXFxuJykubWFwKGZ1bmN0aW9uKGxpbmUpIHtcbiAgICAgICAgICAgIHJldHVybiAnICAgJyArIGxpbmU7XG4gICAgICAgICAgfSkuam9pbignXFxuJyk7XG4gICAgICAgIH1cbiAgICAgIH1cbiAgICB9IGVsc2Uge1xuICAgICAgc3RyID0gY3R4LnN0eWxpemUoJ1tDaXJjdWxhcl0nLCAnc3BlY2lhbCcpO1xuICAgIH1cbiAgfVxuICBpZiAoaXNVbmRlZmluZWQobmFtZSkpIHtcbiAgICBpZiAoYXJyYXkgJiYga2V5Lm1hdGNoKC9eXFxkKyQvKSkge1xuICAgICAgcmV0dXJuIHN0cjtcbiAgICB9XG4gICAgbmFtZSA9IEpTT04uc3RyaW5naWZ5KCcnICsga2V5KTtcbiAgICBpZiAobmFtZS5tYXRjaCgvXlwiKFthLXpBLVpfXVthLXpBLVpfMC05XSopXCIkLykpIHtcbiAgICAgIG5hbWUgPSBuYW1lLnN1YnN0cigxLCBuYW1lLmxlbmd0aCAtIDIpO1xuICAgICAgbmFtZSA9IGN0eC5zdHlsaXplKG5hbWUsICduYW1lJyk7XG4gICAgfSBlbHNlIHtcbiAgICAgIG5hbWUgPSBuYW1lLnJlcGxhY2UoLycvZywgXCJcXFxcJ1wiKVxuICAgICAgICAgICAgICAgICAucmVwbGFjZSgvXFxcXFwiL2csICdcIicpXG4gICAgICAgICAgICAgICAgIC5yZXBsYWNlKC8oXlwifFwiJCkvZywgXCInXCIpO1xuICAgICAgbmFtZSA9IGN0eC5zdHlsaXplKG5hbWUsICdzdHJpbmcnKTtcbiAgICB9XG4gIH1cblxuICByZXR1cm4gbmFtZSArICc6ICcgKyBzdHI7XG59XG5cblxuZnVuY3Rpb24gcmVkdWNlVG9TaW5nbGVTdHJpbmcob3V0cHV0LCBiYXNlLCBicmFjZXMpIHtcbiAgdmFyIG51bUxpbmVzRXN0ID0gMDtcbiAgdmFyIGxlbmd0aCA9IG91dHB1dC5yZWR1Y2UoZnVuY3Rpb24ocHJldiwgY3VyKSB7XG4gICAgbnVtTGluZXNFc3QrKztcbiAgICBpZiAoY3VyLmluZGV4T2YoJ1xcbicpID49IDApIG51bUxpbmVzRXN0Kys7XG4gICAgcmV0dXJuIHByZXYgKyBjdXIucmVwbGFjZSgvXFx1MDAxYlxcW1xcZFxcZD9tL2csICcnKS5sZW5ndGggKyAxO1xuICB9LCAwKTtcblxuICBpZiAobGVuZ3RoID4gNjApIHtcbiAgICByZXR1cm4gYnJhY2VzWzBdICtcbiAgICAgICAgICAgKGJhc2UgPT09ICcnID8gJycgOiBiYXNlICsgJ1xcbiAnKSArXG4gICAgICAgICAgICcgJyArXG4gICAgICAgICAgIG91dHB1dC5qb2luKCcsXFxuICAnKSArXG4gICAgICAgICAgICcgJyArXG4gICAgICAgICAgIGJyYWNlc1sxXTtcbiAgfVxuXG4gIHJldHVybiBicmFjZXNbMF0gKyBiYXNlICsgJyAnICsgb3V0cHV0LmpvaW4oJywgJykgKyAnICcgKyBicmFjZXNbMV07XG59XG5cblxuLy8gTk9URTogVGhlc2UgdHlwZSBjaGVja2luZyBmdW5jdGlvbnMgaW50ZW50aW9uYWxseSBkb24ndCB1c2UgYGluc3RhbmNlb2ZgXG4vLyBiZWNhdXNlIGl0IGlzIGZyYWdpbGUgYW5kIGNhbiBiZSBlYXNpbHkgZmFrZWQgd2l0aCBgT2JqZWN0LmNyZWF0ZSgpYC5cbmZ1bmN0aW9uIGlzQXJyYXkoYXIpIHtcbiAgcmV0dXJuIEFycmF5LmlzQXJyYXkoYXIpO1xufVxuZXhwb3J0cy5pc0FycmF5ID0gaXNBcnJheTtcblxuZnVuY3Rpb24gaXNCb29sZWFuKGFyZykge1xuICByZXR1cm4gdHlwZW9mIGFyZyA9PT0gJ2Jvb2xlYW4nO1xufVxuZXhwb3J0cy5pc0Jvb2xlYW4gPSBpc0Jvb2xlYW47XG5cbmZ1bmN0aW9uIGlzTnVsbChhcmcpIHtcbiAgcmV0dXJuIGFyZyA9PT0gbnVsbDtcbn1cbmV4cG9ydHMuaXNOdWxsID0gaXNOdWxsO1xuXG5mdW5jdGlvbiBpc051bGxPclVuZGVmaW5lZChhcmcpIHtcbiAgcmV0dXJuIGFyZyA9PSBudWxsO1xufVxuZXhwb3J0cy5pc051bGxPclVuZGVmaW5lZCA9IGlzTnVsbE9yVW5kZWZpbmVkO1xuXG5mdW5jdGlvbiBpc051bWJlcihhcmcpIHtcbiAgcmV0dXJuIHR5cGVvZiBhcmcgPT09ICdudW1iZXInO1xufVxuZXhwb3J0cy5pc051bWJlciA9IGlzTnVtYmVyO1xuXG5mdW5jdGlvbiBpc1N0cmluZyhhcmcpIHtcbiAgcmV0dXJuIHR5cGVvZiBhcmcgPT09ICdzdHJpbmcnO1xufVxuZXhwb3J0cy5pc1N0cmluZyA9IGlzU3RyaW5nO1xuXG5mdW5jdGlvbiBpc1N5bWJvbChhcmcpIHtcbiAgcmV0dXJuIHR5cGVvZiBhcmcgPT09ICdzeW1ib2wnO1xufVxuZXhwb3J0cy5pc1N5bWJvbCA9IGlzU3ltYm9sO1xuXG5mdW5jdGlvbiBpc1VuZGVmaW5lZChhcmcpIHtcbiAgcmV0dXJuIGFyZyA9PT0gdm9pZCAwO1xufVxuZXhwb3J0cy5pc1VuZGVmaW5lZCA9IGlzVW5kZWZpbmVkO1xuXG5mdW5jdGlvbiBpc1JlZ0V4cChyZSkge1xuICByZXR1cm4gaXNPYmplY3QocmUpICYmIG9iamVjdFRvU3RyaW5nKHJlKSA9PT0gJ1tvYmplY3QgUmVnRXhwXSc7XG59XG5leHBvcnRzLmlzUmVnRXhwID0gaXNSZWdFeHA7XG5cbmZ1bmN0aW9uIGlzT2JqZWN0KGFyZykge1xuICByZXR1cm4gdHlwZW9mIGFyZyA9PT0gJ29iamVjdCcgJiYgYXJnICE9PSBudWxsO1xufVxuZXhwb3J0cy5pc09iamVjdCA9IGlzT2JqZWN0O1xuXG5mdW5jdGlvbiBpc0RhdGUoZCkge1xuICByZXR1cm4gaXNPYmplY3QoZCkgJiYgb2JqZWN0VG9TdHJpbmcoZCkgPT09ICdbb2JqZWN0IERhdGVdJztcbn1cbmV4cG9ydHMuaXNEYXRlID0gaXNEYXRlO1xuXG5mdW5jdGlvbiBpc0Vycm9yKGUpIHtcbiAgcmV0dXJuIGlzT2JqZWN0KGUpICYmXG4gICAgICAob2JqZWN0VG9TdHJpbmcoZSkgPT09ICdbb2JqZWN0IEVycm9yXScgfHwgZSBpbnN0YW5jZW9mIEVycm9yKTtcbn1cbmV4cG9ydHMuaXNFcnJvciA9IGlzRXJyb3I7XG5cbmZ1bmN0aW9uIGlzRnVuY3Rpb24oYXJnKSB7XG4gIHJldHVybiB0eXBlb2YgYXJnID09PSAnZnVuY3Rpb24nO1xufVxuZXhwb3J0cy5pc0Z1bmN0aW9uID0gaXNGdW5jdGlvbjtcblxuZnVuY3Rpb24gaXNQcmltaXRpdmUoYXJnKSB7XG4gIHJldHVybiBhcmcgPT09IG51bGwgfHxcbiAgICAgICAgIHR5cGVvZiBhcmcgPT09ICdib29sZWFuJyB8fFxuICAgICAgICAgdHlwZW9mIGFyZyA9PT0gJ251bWJlcicgfHxcbiAgICAgICAgIHR5cGVvZiBhcmcgPT09ICdzdHJpbmcnIHx8XG4gICAgICAgICB0eXBlb2YgYXJnID09PSAnc3ltYm9sJyB8fCAgLy8gRVM2IHN5bWJvbFxuICAgICAgICAgdHlwZW9mIGFyZyA9PT0gJ3VuZGVmaW5lZCc7XG59XG5leHBvcnRzLmlzUHJpbWl0aXZlID0gaXNQcmltaXRpdmU7XG5cbmV4cG9ydHMuaXNCdWZmZXIgPSByZXF1aXJlKCcuL3N1cHBvcnQvaXNCdWZmZXInKTtcblxuZnVuY3Rpb24gb2JqZWN0VG9TdHJpbmcobykge1xuICByZXR1cm4gT2JqZWN0LnByb3RvdHlwZS50b1N0cmluZy5jYWxsKG8pO1xufVxuXG5cbmZ1bmN0aW9uIHBhZChuKSB7XG4gIHJldHVybiBuIDwgMTAgPyAnMCcgKyBuLnRvU3RyaW5nKDEwKSA6IG4udG9TdHJpbmcoMTApO1xufVxuXG5cbnZhciBtb250aHMgPSBbJ0phbicsICdGZWInLCAnTWFyJywgJ0FwcicsICdNYXknLCAnSnVuJywgJ0p1bCcsICdBdWcnLCAnU2VwJyxcbiAgICAgICAgICAgICAgJ09jdCcsICdOb3YnLCAnRGVjJ107XG5cbi8vIDI2IEZlYiAxNjoxOTozNFxuZnVuY3Rpb24gdGltZXN0YW1wKCkge1xuICB2YXIgZCA9IG5ldyBEYXRlKCk7XG4gIHZhciB0aW1lID0gW3BhZChkLmdldEhvdXJzKCkpLFxuICAgICAgICAgICAgICBwYWQoZC5nZXRNaW51dGVzKCkpLFxuICAgICAgICAgICAgICBwYWQoZC5nZXRTZWNvbmRzKCkpXS5qb2luKCc6Jyk7XG4gIHJldHVybiBbZC5nZXREYXRlKCksIG1vbnRoc1tkLmdldE1vbnRoKCldLCB0aW1lXS5qb2luKCcgJyk7XG59XG5cblxuLy8gbG9nIGlzIGp1c3QgYSB0aGluIHdyYXBwZXIgdG8gY29uc29sZS5sb2cgdGhhdCBwcmVwZW5kcyBhIHRpbWVzdGFtcFxuZXhwb3J0cy5sb2cgPSBmdW5jdGlvbigpIHtcbiAgY29uc29sZS5sb2coJyVzIC0gJXMnLCB0aW1lc3RhbXAoKSwgZXhwb3J0cy5mb3JtYXQuYXBwbHkoZXhwb3J0cywgYXJndW1lbnRzKSk7XG59O1xuXG5cbi8qKlxuICogSW5oZXJpdCB0aGUgcHJvdG90eXBlIG1ldGhvZHMgZnJvbSBvbmUgY29uc3RydWN0b3IgaW50byBhbm90aGVyLlxuICpcbiAqIFRoZSBGdW5jdGlvbi5wcm90b3R5cGUuaW5oZXJpdHMgZnJvbSBsYW5nLmpzIHJld3JpdHRlbiBhcyBhIHN0YW5kYWxvbmVcbiAqIGZ1bmN0aW9uIChub3Qgb24gRnVuY3Rpb24ucHJvdG90eXBlKS4gTk9URTogSWYgdGhpcyBmaWxlIGlzIHRvIGJlIGxvYWRlZFxuICogZHVyaW5nIGJvb3RzdHJhcHBpbmcgdGhpcyBmdW5jdGlvbiBuZWVkcyB0byBiZSByZXdyaXR0ZW4gdXNpbmcgc29tZSBuYXRpdmVcbiAqIGZ1bmN0aW9ucyBhcyBwcm90b3R5cGUgc2V0dXAgdXNpbmcgbm9ybWFsIEphdmFTY3JpcHQgZG9lcyBub3Qgd29yayBhc1xuICogZXhwZWN0ZWQgZHVyaW5nIGJvb3RzdHJhcHBpbmcgKHNlZSBtaXJyb3IuanMgaW4gcjExNDkwMykuXG4gKlxuICogQHBhcmFtIHtmdW5jdGlvbn0gY3RvciBDb25zdHJ1Y3RvciBmdW5jdGlvbiB3aGljaCBuZWVkcyB0byBpbmhlcml0IHRoZVxuICogICAgIHByb3RvdHlwZS5cbiAqIEBwYXJhbSB7ZnVuY3Rpb259IHN1cGVyQ3RvciBDb25zdHJ1Y3RvciBmdW5jdGlvbiB0byBpbmhlcml0IHByb3RvdHlwZSBmcm9tLlxuICovXG5leHBvcnRzLmluaGVyaXRzID0gcmVxdWlyZSgnaW5oZXJpdHMnKTtcblxuZXhwb3J0cy5fZXh0ZW5kID0gZnVuY3Rpb24ob3JpZ2luLCBhZGQpIHtcbiAgLy8gRG9uJ3QgZG8gYW55dGhpbmcgaWYgYWRkIGlzbid0IGFuIG9iamVjdFxuICBpZiAoIWFkZCB8fCAhaXNPYmplY3QoYWRkKSkgcmV0dXJuIG9yaWdpbjtcblxuICB2YXIga2V5cyA9IE9iamVjdC5rZXlzKGFkZCk7XG4gIHZhciBpID0ga2V5cy5sZW5ndGg7XG4gIHdoaWxlIChpLS0pIHtcbiAgICBvcmlnaW5ba2V5c1tpXV0gPSBhZGRba2V5c1tpXV07XG4gIH1cbiAgcmV0dXJuIG9yaWdpbjtcbn07XG5cbmZ1bmN0aW9uIGhhc093blByb3BlcnR5KG9iaiwgcHJvcCkge1xuICByZXR1cm4gT2JqZWN0LnByb3RvdHlwZS5oYXNPd25Qcm9wZXJ0eS5jYWxsKG9iaiwgcHJvcCk7XG59XG4iXX0=
