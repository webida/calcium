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

},{"util":17}],2:[function(require,module,exports){
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

},{"../domains/status":5,"../domains/types":6,"./constraints":3,"acorn/dist/walk":12}],3:[function(require,module,exports){
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

},{"./aux":1,"./constraint/cGen":2,"./domains/context":4,"./domains/status":5,"./domains/types":6,"./varBlock":8,"./varrefs":9,"acorn/dist/acorn":10,"acorn/dist/acorn_loose":11,"util":17}],8:[function(require,module,exports){
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

},{"./aux":1,"./domains/types":6,"acorn/dist/walk":12}],9:[function(require,module,exports){
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

function findIdentifierAt(ast, pos) {
    'use strict';

    function Found(node, state) {
        this.node = node;
        this.state = state;
    }

    // find the node
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

},{"./infer":7,"acorn/dist/walk":12,"fs":13}],10:[function(require,module,exports){
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

},{}],12:[function(require,module,exports){
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

},{}],13:[function(require,module,exports){

},{}],14:[function(require,module,exports){
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

},{}],15:[function(require,module,exports){
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

},{}],16:[function(require,module,exports){
module.exports = function isBuffer(arg) {
  return arg && typeof arg === 'object'
    && typeof arg.copy === 'function'
    && typeof arg.fill === 'function'
    && typeof arg.readUInt8 === 'function';
}
},{}],17:[function(require,module,exports){
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

},{"./support/isBuffer":16,"_process":15,"inherits":14}]},{},[7])(7)
});
//# sourceMappingURL=data:application/json;charset:utf-8;base64,eyJ2ZXJzaW9uIjozLCJzb3VyY2VzIjpbIm5vZGVfbW9kdWxlcy9icm93c2VyaWZ5L25vZGVfbW9kdWxlcy9icm93c2VyLXBhY2svX3ByZWx1ZGUuanMiLCIvaG9tZS9zd2tpbS9XZWJzdG9ybVByb2plY3RzL3lhdGVybi9saWIvYXV4LmpzIiwiL2hvbWUvc3draW0vV2Vic3Rvcm1Qcm9qZWN0cy95YXRlcm4vbGliL2NvbnN0cmFpbnQvY0dlbi5qcyIsIi9ob21lL3N3a2ltL1dlYnN0b3JtUHJvamVjdHMveWF0ZXJuL2xpYi9jb25zdHJhaW50L2NvbnN0cmFpbnRzLmpzIiwiL2hvbWUvc3draW0vV2Vic3Rvcm1Qcm9qZWN0cy95YXRlcm4vbGliL2RvbWFpbnMvY29udGV4dC5qcyIsIi9ob21lL3N3a2ltL1dlYnN0b3JtUHJvamVjdHMveWF0ZXJuL2xpYi9kb21haW5zL3N0YXR1cy5qcyIsIi9ob21lL3N3a2ltL1dlYnN0b3JtUHJvamVjdHMveWF0ZXJuL2xpYi9kb21haW5zL3R5cGVzLmpzIiwiL2hvbWUvc3draW0vV2Vic3Rvcm1Qcm9qZWN0cy95YXRlcm4vbGliL2luZmVyLmpzIiwiL2hvbWUvc3draW0vV2Vic3Rvcm1Qcm9qZWN0cy95YXRlcm4vbGliL3ZhckJsb2NrLmpzIiwiL2hvbWUvc3draW0vV2Vic3Rvcm1Qcm9qZWN0cy95YXRlcm4vbGliL3ZhcnJlZnMuanMiLCJub2RlX21vZHVsZXMvYWNvcm4vZGlzdC9hY29ybi5qcyIsIm5vZGVfbW9kdWxlcy9hY29ybi9kaXN0L2Fjb3JuX2xvb3NlLmpzIiwibm9kZV9tb2R1bGVzL2Fjb3JuL2Rpc3Qvd2Fsay5qcyIsIm5vZGVfbW9kdWxlcy9icm93c2VyaWZ5L2xpYi9fZW1wdHkuanMiLCJub2RlX21vZHVsZXMvYnJvd3NlcmlmeS9ub2RlX21vZHVsZXMvaW5oZXJpdHMvaW5oZXJpdHNfYnJvd3Nlci5qcyIsIm5vZGVfbW9kdWxlcy9icm93c2VyaWZ5L25vZGVfbW9kdWxlcy9wcm9jZXNzL2Jyb3dzZXIuanMiLCJub2RlX21vZHVsZXMvYnJvd3NlcmlmeS9ub2RlX21vZHVsZXMvdXRpbC9zdXBwb3J0L2lzQnVmZmVyQnJvd3Nlci5qcyIsIm5vZGVfbW9kdWxlcy9icm93c2VyaWZ5L25vZGVfbW9kdWxlcy91dGlsL3V0aWwuanMiXSwibmFtZXMiOltdLCJtYXBwaW5ncyI6IkFBQUE7OztBQ0FBLElBQUksSUFBSSxHQUFHLE9BQU8sQ0FBQyxNQUFNLENBQUMsQ0FBQzs7QUFFM0IsU0FBUyxXQUFXLENBQUMsR0FBRyxFQUFFLFFBQVEsRUFBRTtBQUNoQyxRQUFJLFFBQVEsR0FBRyxFQUFFLENBQUM7O0FBRWxCLFFBQUksR0FBRyxHQUFHLFFBQVEsS0FBSyxTQUFTLEdBQUcsQ0FBQyxHQUFHLFFBQVEsQ0FBQzs7QUFFaEQsYUFBUyxRQUFRLENBQUMsSUFBSSxFQUFFO0FBQ3BCLFlBQUksQ0FBQyxRQUFRLENBQUMsR0FBRyxHQUFHLENBQUM7QUFDckIsZ0JBQVEsQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDLENBQUM7QUFDcEIsV0FBRyxFQUFFLENBQUM7S0FDVDs7O0FBR0QsYUFBUyxpQkFBaUIsQ0FBQyxJQUFJLEVBQUU7QUFDN0IsWUFBSSxJQUFJLElBQUksSUFBSSxDQUFDLGNBQWMsQ0FBQyxNQUFNLENBQUMsRUFBRTtBQUNyQyxvQkFBUSxDQUFDLElBQUksQ0FBQyxDQUFDO1NBQ2xCO0FBQ0QsWUFBSSxJQUFJLElBQUksT0FBTyxJQUFJLEtBQUssUUFBUSxFQUFFO0FBQ2xDLGlCQUFLLElBQUksQ0FBQyxJQUFJLElBQUksRUFBRTtBQUNoQixpQ0FBaUIsQ0FBQyxJQUFJLENBQUMsQ0FBQyxDQUFDLENBQUMsQ0FBQzthQUM5QjtTQUNKO0tBQ0o7O0FBRUQscUJBQWlCLENBQUMsR0FBRyxDQUFDLENBQUM7O0FBRXZCLFdBQU8sUUFBUSxDQUFDO0NBQ25COztBQUVELFNBQVMsWUFBWSxDQUFDLEdBQUcsRUFBRTtBQUN2QixXQUFPLENBQUMsR0FBRyxDQUFDLElBQUksQ0FBQyxPQUFPLENBQUMsR0FBRyxFQUFFLEVBQUMsS0FBSyxFQUFFLElBQUksRUFB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QUFTLENBQUMsT0FBTyxHQUFHLFVBQVUsQ0FBQyxFQUFFO0FBQ3BDLFFBQUksRUFBRSxDQUFDLFlBQWEsS0FBSyxDQUFDLE1BQU0sQ0FBQyxFQUFHLE9BQU87QUFDM0MsUUFBTSxNQUFNLEdBQUcsQ0FBQyxDQUFDLFNBQVMsQ0FBQyxJQUFJLENBQUMsS0FBSyxDQUFDLENBQUM7QUFDdkMsUUFBTSxLQUFLLEdBQUcsQ0FBQyxDQUFDLFVBQVUsQ0FBQyxJQUFJLENBQUMsUUFBUSxDQUFDLENBQUMsZ0JBQWdCLENBQUMsQ0FBQyxDQUFDLEVBQUUsRUFBRSxJQUFJLENBQUMsS0FBSyxDQUFDLENBQUM7QUFDN0UsUUFBTSxTQUFTLEdBQ1QsSUFBSSxNQUFNLENBQUMsTUFBTSxDQUFDLE1BQU0sQ0FBQyxDQUFDLENBQUMsRUFBRSxJQUFJLFNBQVMsQ0FBQyxNQUFNLENBQUMsQ0FBQyxDQUFDLENBQUMsRUFBRSxNQUFNLENBQUMsQ0FBQyxDQUFDLEVBQzlDLElBQUksQ0FBQyxLQUFLLEVBQUUsS0FBSyxDQUFDLENBQUM7O0FBRTNDLFFBQU0sTUFBTSxHQUFHLENBQUMsQ0FBQyxXQUFXLEVBQUUsQ0FBQztBQUMvQixVQUFNLENBQUMsQ0FBQyxDQUFDLENBQUMsT0FBTyxDQUFDLE1BQU0sQ0FBQyxDQUFDOztBQUUxQixRQUFNLE1BQU0sR0FBRyxJQUFJLENBQUMsR0FBRyxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsTUFBTSxFQUFFLENBQUMsQ0FBQyxVQUFVLENBQUMsTUFBTSxDQUFDLENBQUM7QUFDL0QsU0FBSyxJQUFJLENBQUMsR0FBRyxDQUFDLEVBQUUsQ0FBQyxHQUFHLE1BQU0sRUFBRSxDQUFDLEVBQUUsRUFBRTtBQUM3QixZQUFJLENBQUMsSUFBSSxDQUFDLENBQUMsQ0FBQyxDQUFDLFNBQVMsQ0FBQyxLQUFLLENBQUMsU0FBUyxDQUFDLENBQUMsQ0FBQyxVQUFVLENBQUMsQ0FBQyxDQUFDLENBQUMsQ0FBQyxDQUFDO0tBQzVEOzs7QUFHRCxRQUFJLENBQUMsQ0FBQyxVQUFVLENBQUMsSUFBSSxDQUFD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Q0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7Ozs7O0FDNzZIQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTs7Ozs7QUN0eENBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTs7OztBQ3JWQTs7QUNBQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7O0FDdkJBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBOztBQzFGQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7OztBQ0xBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0EiLCJmaWxlIjoiZ2VuZXJhdGVkLmpzIiwic291cmNlUm9vdCI6IiIsInNvdXJjZXNDb250ZW50IjpbIihmdW5jdGlvbiBlKHQsbixyKXtmdW5jdGlvbiBzKG8sdSl7aWYoIW5bb10pe2lmKCF0W29dKXt2YXIgYT10eXBlb2YgcmVxdWlyZT09XCJmdW5jdGlvblwiJiZyZXF1aXJlO2lmKCF1JiZhKXJldHVybiBhKG8sITApO2lmKGkpcmV0dXJuIGkobywhMCk7dmFyIGY9bmV3IEVycm9yKFwiQ2Fubm90IGZpbmQgbW9kdWxlICdcIitvK1wiJ1wiKTt0aHJvdyBmLmNvZGU9XCJNT0RVTEVfTk9UX0ZPVU5EXCIsZn12YXIgbD1uW29dPXtleHBvcnRzOnt9fTt0W29dWzBdLmNhbGwobC5leHBvcnRzLGZ1bmN0aW9uKGUpe3ZhciBuPXRbb11bMV1bZV07cmV0dXJuIHMobj9uOmUpfSxsLGwuZXhwb3J0cyxlLHQsbixyKX1yZXR1cm4gbltvXS5leHBvcnRzfXZhciBpPXR5cGVvZiByZXF1aXJlPT1cImZ1bmN0aW9uXCImJnJlcXVpcmU7Zm9yKHZhciBvPTA7bzxyLmxlbmd0aDtvKyspcyhyW29dKTtyZXR1cm4gc30pIiwidmFyIHV0aWwgPSByZXF1aXJlKCd1dGlsJyk7XG5cbmZ1bmN0aW9uIGdldE5vZGVMaXN0KGFzdCwgc3RhcnROdW0pIHtcbiAgICB2YXIgbm9kZUxpc3QgPSBbXTtcblxuICAgIHZhciBudW0gPSBzdGFydE51bSA9PT0gdW5kZWZpbmVkID8gMCA6IHN0YXJ0TnVtO1xuXG4gICAgZnVuY3Rpb24gYXNzaWduSWQobm9kZSkge1xuICAgICAgICBub2RlWydAbGFiZWwnXSA9IG51bTtcbiAgICAgICAgbm9kZUxpc3QucHVzaChub2RlKTtcbiAgICAgICAgbnVtKys7XG4gICAgfVxuXG4gICAgLy8gTGFiZWwgZXZlcnkgQVNUIG5vZGUgd2l0aCBwcm9wZXJ0eSAndHlwZSdcbiAgICBmdW5jdGlvbiBsYWJlbE5vZGVXaXRoVHlwZShub2RlKSB7XG4gICAgICAgIGlmIChub2RlICYmIG5vZGUuaGFzT3duUHJvcGVydHkoJ3R5cGUnKSkge1xuICAgICAgICAgICAgYXNzaWduSWQobm9kZSk7XG4gICAgICAgIH1cbiAgICAgICAgaWYgKG5vZGUgJiYgdHlwZW9mIG5vZGUgPT09ICdvYmplY3QnKSB7XG4gICAgICAgICAgICBmb3IgKHZhciBwIGluIG5vZGUpIHtcbiAgICAgICAgICAgICAgICBsYWJlbE5vZGVXaXRoVHlwZShub2RlW3BdKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgfVxuICAgIH1cblxuICAgIGxhYmVsTm9kZVdpdGhUeXBlKGFzdCk7XG5cbiAgICByZXR1cm4gbm9kZUxpc3Q7XG59XG5cbmZ1bmN0aW9uIHNob3dVbmZvbGRlZChvYmopIHtcbiAgICBjb25zb2xlLmxvZyh1dGlsLmluc3BlY3Qob2JqLCB7ZGVwdGg6IG51bGx9KSk7XG59XG5cbmV4cG9ydHMuZ2V0Tm9kZUxpc3QgPSBnZXROb2RlTGlzdDtcbmV4cG9ydHMuc2hvd1VuZm9sZGVkID0gc2hvd1VuZm9sZGVkO1xuIiwiJ3VzZSBzdHJpY3QnO1xuXG5jb25zdCB0eXBlcyA9IHJlcXVpcmUoJy4uL2RvbWFpbnMvdHlwZXMnKTtcbmNvbnN0IHdhbGsgPSByZXF1aXJlKCdhY29ybi9kaXN0L3dhbGsnKTtcbmNvbnN0IHN0YXR1cyA9IHJlcXVpcmUoJy4uL2RvbWFpbnMvc3RhdHVzJyk7XG5jb25zdCBjc3RyID0gcmVxdWlyZSgnLi9jb25zdHJhaW50cycpO1xuXG4vLyBhcmd1bWVudHMgYXJlIFwiIG9sZFN0YXR1cyAoLCBuYW1lLCB2YWwpKiBcIlxuZnVuY3Rpb24gY2hhbmdlZFN0YXR1cyhvbGRTdGF0dXMpIHtcbiAgICBjb25zdCBuZXdTdGF0dXMgPSBuZXcgc3RhdHVzLlN0YXR1cztcbiAgICBmb3IgKGxldCBpID0gMTsgaSA8IGFyZ3VtZW50cy5sZW5ndGg7IGkgPSBpICsgMilcbiAgICAgICAgbmV3U3RhdHVzW2FyZ3VtZW50c1tpXV0gPSBhcmd1bWVudHNbaSsxXTtcblxuICAgIGZvciAobGV0IHAgaW4gb2xkU3RhdHVzKSB7XG4gICAgICAgIGlmIChuZXdTdGF0dXNbcF0gPT09IHVuZGVmaW5lZClcbiAgICAgICAgICAgIG5ld1N0YXR1c1twXSA9IG9sZFN0YXR1c1twXTtcbiAgICB9XG4gICAgcmV0dXJuIG5ld1N0YXR1cztcbn1cblxuLy8gcmV0dXJucyBbYWNjZXNzIHR5cGUsIHByb3AgdmFsdWVdXG5mdW5jdGlvbiBwcm9wQWNjZXNzKG5vZGUpIHtcbiAgICBjb25zdCBwcm9wID0gbm9kZS5wcm9wZXJ0eTtcbiAgICBpZiAoIW5vZGUuY29tcHV0ZWQpIHtcbiAgICAgICAgcmV0dXJuIFsnZG90QWNjZXNzJywgcHJvcC5uYW1lXTtcbiAgICB9XG4gICAgaWYgKHByb3AudHlwZSA9PT0gJ0xpdGVyYWwnKSB7XG4gICAgICAgIGlmICh0eXBlb2YgcHJvcC52YWx1ZSA9PT0gJ3N0cmluZycpXG4gICAgICAgICAgICByZXR1cm4gWydzdHJpbmdMaXRlcmFsJywgcHJvcC52YWx1ZV07XG4gICAgICAgIGlmICh0eXBlb2YgcHJvcC52YWx1ZSA9PT0gJ251bWJlcicpXG4gICAgICAgICAgICAvLyBjb252ZXJ0IG51bWJlciB0byBzdHJpbmdcbiAgICAgICAgICAgIHJldHVybiBbJ251bWJlckxpdGVyYWwnLCBwcm9wLnZhbHVlICsgJyddO1xuICAgIH1cbiAgICByZXR1cm4gW1wiY29tcHV0ZWRcIiwgbnVsbF07XG59XG5cbmZ1bmN0aW9uIHVub3BSZXN1bHRUeXBlKG9wKSB7XG4gICAgc3dpdGNoIChvcCkge1xuICAgICAgICBjYXNlICcrJzogY2FzZSAnLSc6IGNhc2UgJ34nOlxuICAgICAgICAgICAgcmV0dXJuIHR5cGVzLlByaW1OdW1iZXI7XG4gICAgICAgIGNhc2UgJyEnOlxuICAgICAgICAgICAgcmV0dXJuIHR5cGVzLlByaW1Cb29sZWFuO1xuICAgICAgICBjYXNlICd0eXBlb2YnOlxuICAgICAgICAgICAgcmV0dXJuIHR5cGVzLlByaW1TdHJpbmc7XG4gICAgICAgIGNhc2UgJ3ZvaWQnOiBjYXNlICdkZWxldGUnOlxuICAgICAgICAgICAgcmV0dXJuIG51bGw7XG4gICAgfVxufVxuXG5mdW5jdGlvbiBiaW5vcElzQm9vbGVhbihvcCkge1xuICAgIHN3aXRjaCAob3ApIHtcbiAgICAgICAgY2FzZSAnPT0nOiBjYXNlICchPSc6IGNhc2UgJz09PSc6IGNhc2UgJyE9PSc6XG4gICAgICAgIGNhc2UgJzwnOiBjYXNlICc+JzogY2FzZSAnPj0nOiBjYXNlICc8PSc6XG4gICAgICAgIGNhc2UgJ2luJzogY2FzZSAnaW5zdGFuY2VvZic6XG4gICAgICAgICAgICByZXR1cm4gdHJ1ZTtcbiAgICB9XG4gICAgcmV0dXJuIGZhbHNlO1xufVxuXG5mdW5jdGlvbiByZWFkTWVtYmVyKG5vZGUsIGN1clN0YXR1cywgYykge1xuICAgIGNvbnN0IHJldCA9IG5ldyB0eXBlcy5BVmFsO1xuICAgIGNvbnN0IG9iakFWYWwgPSBjKG5vZGUub2JqZWN0LCBjdXJTdGF0dXMsIHVuZGVmaW5lZCk7XG4gICAgaWYgKG5vZGUucHJvcGVydHkudHlwZSAhPT0gJ0lkZW50aWZpZXInKSB7XG4gICAgICAgIC8vIHJldHVybiBmcm9tIHByb3BlcnR5IGlzIGlnbm9yZWRcbiAgICAgICAgYyhub2RlLnByb3BlcnR5LCBjdXJTdGF0dXMsIHVuZGVmaW5lZCk7XG4gICAgfVxuICAgIGNvbnN0IHByb3BBY2MgPSBwcm9wQWNjZXNzKG5vZGUpO1xuXG4gICAgY29uc3RyYWludHMucHVzaCh7T0JKOiBvYmpBVmFsLFxuICAgICAgICAgICAgICAgICAgICAgIFBST1A6IHByb3BBY2NbMV0sXG4gICAgICAgICAgICAgICAgICAgICAgUkVBRF9UTzogcmV0fSk7XG4gICAgb2JqQVZhbC5wcm9wYWdhdGUobmV3IGNzdHIuUmVhZFByb3AocHJvcEFjY1sxXSwgcmV0KSk7XG5cbiAgICAvLyByZXR1cm5zIEFWYWwgZm9yIHJlY2VpdmVyIGFuZCByZWFkIG1lbWJlclxuICAgIHJldHVybiBbb2JqQVZhbCwgcmV0XTtcbn1cbi8vIFRvIHByZXZlbnQgcmVjdXJzaW9uLFxuLy8gd2UgcmVtZW1iZXIgdGhlIHN0YXR1cyB1c2VkIGluIGFkZENvbnN0cmFpbnRzXG5jb25zdCB2aXNpdGVkU3RhdHVzID0gW107XG5jb25zdCBjb25zdHJhaW50cyA9IFtdO1xuZnVuY3Rpb24gY2xlYXJDb25zdHJhaW50cygpIHtcbiAgICB2aXNpdGVkU3RhdHVzLmxlbmd0aCA9IDA7XG4gICAgY29uc3RyYWludHMubGVuZ3RoID0gMDtcbn1cblxubGV0IHJ0Q1g7XG5mdW5jdGlvbiBhZGRDb25zdHJhaW50cyhhc3QsIGluaXRTdGF0dXMsIG5ld1J0Q1gpIHtcblxuICAgIC8vIHNldCBydENYXG4gICAgcnRDWCA9IG5ld1J0Q1ggfHwgcnRDWDtcblxuICAgIC8vIENoZWNrIHdoZXRoZXIgd2UgaGF2ZSBwcm9jZXNzZWQgJ2luaXRTdGF0dXMnIGJlZm9yZVxuICAgIGZvciAobGV0IGk9MDsgaSA8IHZpc2l0ZWRTdGF0dXMubGVuZ3RoOyBpKyspIHtcbiAgICAgICAgaWYgKGluaXRTdGF0dXMuZXF1YWxzKHZpc2l0ZWRTdGF0dXNbaV0pKSB7XG4gICAgICAgICAgICAgLy8gSWYgc28sIGRvIG5vdGhpbmdcbiAgICAgICAgICAgICAvLyBzaWduaWZ5aW5nIHdlIGRpZG4ndCBhZGQgY29uc3RyYWludHNcbiAgICAgICAgICAgICByZXR1cm4gZmFsc2U7XG4gICAgICAgICB9XG4gICAgfVxuICAgIC8vIElmIHRoZSBpbml0U3RhdHVzIGlzIG5ldywgcHVzaCBpdC5cbiAgICAvLyBXZSBkbyBub3QgcmVjb3JkIGFzdCBzaW5jZSBhc3Qgbm9kZSBkZXBlbmRzIG9uIHRoZSBzdGF0dXNcbiAgICB2aXNpdGVkU3RhdHVzLnB1c2goaW5pdFN0YXR1cyk7XG5cbiAgICAvLyBjb25zdHJhaW50IGdlbmVyYXRpbmcgd2Fsa2VyIGZvciBleHByZXNzaW9uc1xuICAgIGNvbnN0IGNvbnN0cmFpbnRHZW5lcmF0b3IgPSB3YWxrLm1ha2Uoe1xuXG4gICAgICAgIElkZW50aWZpZXI6IGZ1bmN0aW9uIChub2RlLCBjdXJTdGF0dXMsIGMpIHtcbiAgICAgICAgICAgIHJldHVybiBjdXJTdGF0dXMuc2MuZ2V0QVZhbE9mKG5vZGUubmFtZSk7XG4gICAgICAgIH0sXG5cbiAgICAgICAgVGhpc0V4cHJlc3Npb246IGZ1bmN0aW9uIChub2RlLCBjdXJTdGF0dXMsIGMpIHtcbiAgICAgICAgICAgIHJldHVybiBjdXJTdGF0dXMuc2VsZjtcbiAgICAgICAgfSxcblxuICAgICAgICBMaXRlcmFsOiBmdW5jdGlvbiAobm9kZSwgY3VyU3RhdHVzLCBjKSB7XG4gICAgICAgICAgICBjb25zdCByZXMgPSBuZXcgdHlwZXMuQVZhbDtcbiAgICAgICAgICAgIGlmIChub2RlLnJlZ2V4KSB7XG4gICAgICAgICAgICAgICAgLy8gbm90IGltcGxlbWVudGVkIHlldFxuICAgICAgICAgICAgICAgIC8vIHRocm93IG5ldyBFcnJvcigncmVnZXggbGl0ZXJhbCBpcyBub3QgaW1wbGVtZW50ZWQgeWV0Jyk7XG4gICAgICAgICAgICAgICAgcmV0dXJuIHJlcztcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIHN3aXRjaCAodHlwZW9mIG5vZGUudmFsdWUpIHtcbiAgICAgICAgICAgIGNhc2UgJ251bWJlcic6XG4gICAgICAgICAgICAgICAgY29uc3RyYWludHMucHVzaCh7VFlQRTogdHlwZXMuUHJpbU51bWJlcixcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBJTkNMX1NFVDogcmVzfSk7XG4gICAgICAgICAgICAgICAgcmVzLmFkZFR5cGUodHlwZXMuUHJpbU51bWJlcik7XG4gICAgICAgICAgICAgICAgYnJlYWs7XG4gICAgICAgICAgICBjYXNlICdzdHJpbmcnOlxuICAgICAgICAgICAgICAgIGNvbnN0cmFpbnRzLnB1c2goe1RZUEU6IHR5cGVzLlByaW1TdHJpbmcsXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgSU5DTF9TRVQ6IHJlc30pO1xuICAgICAgICAgICAgICAgIHJlcy5hZGRUeXBlKHR5cGVzLlByaW1TdHJpbmcpO1xuICAgICAgICAgICAgICAgIGJyZWFrO1xuICAgICAgICAgICAgY2FzZSAnYm9vbGVhbic6XG4gICAgICAgICAgICAgICAgY29uc3RyYWludHMucHVzaCh7VFlQRTogdHlwZXMuUHJpbUJvb2xlYW4sXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgSU5DTF9TRVQ6IHJlc30pO1xuICAgICAgICAgICAgICAgIHJlcy5hZGRUeXBlKHR5cGVzLlByaW1Cb29sZWFuKTtcbiAgICAgICAgICAgICAgICBicmVhaztcbiAgICAgICAgICAgIGNhc2UgJ29iamVjdCc6XG4gICAgICAgICAgICAgICAgLy8gSSBndWVzczogTGl0ZXJhbCAmJiBvYmplY3QgPT0+IG5vZGUudmFsdWUgPT0gbnVsbFxuICAgICAgICAgICAgICAgIC8vIG51bGwgaXMgaWdub3JlZCwgc28gbm90aGluZyB0byBhZGRcbiAgICAgICAgICAgICAgICBicmVhaztcbiAgICAgICAgICAgIGNhc2UgJ2Z1bmN0aW9uJzpcbiAgICAgICAgICAgICAgICB0aHJvdyBuZXcgRXJyb3IoJ0kgZ3Vlc3MgZnVuY3Rpb24gaXMgaW1wb3NzaWJsZSBoZXJlLicpO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgcmV0dXJuIHJlcztcbiAgICAgICAgfSxcblxuICAgICAgICBBc3NpZ25tZW50RXhwcmVzc2lvbjogZnVuY3Rpb24gKG5vZGUsIGN1clN0YXR1cywgYykge1xuICAgICAgICAgICAgY29uc3QgcmhzQVZhbCA9IGMobm9kZS5yaWdodCwgY3VyU3RhdHVzLCB1bmRlZmluZWQpO1xuICAgICAgICAgICAgaWYgKG5vZGUubGVmdC50eXBlICE9PSAnTWVtYmVyRXhwcmVzc2lvbicpIHtcbiAgICAgICAgICAgICAgICAvLyBMSFMgaXMgYSBzaW1wbGUgdmFyaWFibGUuXG4gICAgICAgICAgICAgICAgY29uc3QgdmFyTmFtZSA9IG5vZGUubGVmdC5uYW1lO1xuICAgICAgICAgICAgICAgIGNvbnN0IGxoc0FWYWwgPSBjdXJTdGF0dXMuc2MuZ2V0QVZhbE9mKHZhck5hbWUpO1xuXG4gICAgICAgICAgICAgICAgaWYgKG5vZGUub3BlcmF0b3IgPT09ICc9Jykge1xuICAgICAgICAgICAgICAgICAgICAvLyBzaW1wbGUgYXNzaWdubWVudFxuICAgICAgICAgICAgICAgICAgICBjb25zdHJhaW50cy5wdXNoKHtcbiAgICAgICAgICAgICAgICAgICAgICAgIEZST006IHJoc0FWYWwsXG4gICAgICAgICAgICAgICAgICAgICAgICBUTzogbGhzQVZhbFxuICAgICAgICAgICAgICAgICAgICB9KTtcbiAgICAgICAgICAgICAgICAgICAgcmhzQVZhbC5wcm9wYWdhdGUobGhzQVZhbCk7XG4gICAgICAgICAgICAgICAgICAgIC8vIGNvcnJlc3BvbmRpbmcgQVZhbCBpcyB0aGUgUkhTXG4gICAgICAgICAgICAgICAgICAgIHJldHVybiByaHNBVmFsO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICBjb25zdCByZXNBVmFsID0gbmV3IHR5cGVzLkFWYWw7XG4gICAgICAgICAgICAgICAgaWYgKG5vZGUub3BlcmF0b3IgPT09ICcrPScpIHtcbiAgICAgICAgICAgICAgICAgICAgLy8gY29uY2F0ZW5hdGluZyB1cGRhdGVcbiAgICAgICAgICAgICAgICAgICAgY29uc3RyYWludHMucHVzaCh7XG4gICAgICAgICAgICAgICAgICAgICAgICBBRERfT1BSRDE6IGxoc0FWYWwsXG4gICAgICAgICAgICAgICAgICAgICAgICBBRERfT1BSRDI6IHJoc0FWYWwsXG4gICAgICAgICAgICAgICAgICAgICAgICBSRVNVTFQ6IHJlc0FWYWxcbiAgICAgICAgICAgICAgICAgICAgfSk7XG4gICAgICAgICAgICAgICAgICAgIGxoc0FWYWwucHJvcGFnYXRlKG5ldyBjc3RyLklzQWRkZWQocmhzQVZhbCwgcmVzQVZhbCkpO1xuICAgICAgICAgICAgICAgICAgICByaHNBVmFsLnByb3BhZ2F0ZShuZXcgY3N0ci5Jc0FkZGVkKGxoc0FWYWwsIHJlc0FWYWwpKTtcbiAgICAgICAgICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgICAgICAgICAgICAvLyBhcml0aG1ldGljIHVwZGF0ZVxuICAgICAgICAgICAgICAgICAgICBjb25zdHJhaW50cy5wdXNoKHtcbiAgICAgICAgICAgICAgICAgICAgICAgIFRZUEU6dHlwZXMuUHJpbU51bWJlcixcbiAgICAgICAgICAgICAgICAgICAgICAgIElOQ0xfU0VUOiByZXNBVmFsXG4gICAgICAgICAgICAgICAgICAgIH0pO1xuICAgICAgICAgICAgICAgICAgICByZXNBVmFsLmFkZFR5cGUodHlwZXMuUHJpbU51bWJlcik7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIHJldHVybiByZXNBVmFsO1xuICAgICAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICAgICAgICAvLyBtZW1iZXIgYXNzaWdubWVudFxuICAgICAgICAgICAgICAgIGNvbnN0IG9iakFWYWwgPSBjKG5vZGUubGVmdC5vYmplY3QsIGN1clN0YXR1cywgdW5kZWZpbmVkKTtcbiAgICAgICAgICAgICAgICBjb25zdCBwcm9wQWNjID0gcHJvcEFjY2Vzcyhub2RlLmxlZnQpO1xuICAgICAgICAgICAgICAgIGlmIChub2RlLm9wZXJhdG9yID09PSAnPScpIHtcbiAgICAgICAgICAgICAgICAgICAgLy8gYXNzaWdubWVudCB0byBtZW1iZXJcbiAgICAgICAgICAgICAgICAgICAgY29uc3RyYWludHMucHVzaCh7XG4gICAgICAgICAgICAgICAgICAgICAgICBPQko6IG9iakFWYWwsXG4gICAgICAgICAgICAgICAgICAgICAgICBQUk9QOiBwcm9wQWNjWzFdLFxuICAgICAgICAgICAgICAgICAgICAgICAgV1JJVEVfV0lUSDogcmhzQVZhbFxuICAgICAgICAgICAgICAgICAgICB9KTtcbiAgICAgICAgICAgICAgICAgICAgb2JqQVZhbC5wcm9wYWdhdGUobmV3IGNzdHIuV3JpdGVQcm9wKHByb3BBY2NbMV0sIHJoc0FWYWwpKTtcbiAgICAgICAgICAgICAgICAgICAgLy8gaWYgcHJvcGVydHkgaXMgbnVtYmVyIGxpdGVyYWwsIGFsc28gd3JpdGUgdG8gJ3Vua25vd24nXG4gICAgICAgICAgICAgICAgICAgIGlmIChwcm9wQWNjWzBdID09PSAnbnVtYmVyTGl0ZXJhbCcpIHtcbiAgICAgICAgICAgICAgICAgICAgICAgIG9iakFWYWwucHJvcGFnYXRlKG5ldyBjc3RyLldyaXRlUHJvcChudWxsLCByaHNBVmFsKSk7XG4gICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgcmV0dXJuIHJoc0FWYWw7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIGNvbnN0IHJlc0FWYWwgPSBuZXcgdHlwZXMuQVZhbDtcbiAgICAgICAgICAgICAgICBjb25zdCByZWN2QW5kUmV0ID0gcmVhZE1lbWJlcihub2RlLmxlZnQsIGN1clN0YXR1cywgYyk7XG4gICAgICAgICAgICAgICAgaWYgKG5vZGUub3BlcmF0b3IgPT09ICcrPScpIHtcbiAgICAgICAgICAgICAgICAgICAgLy8gY29uY2F0ZW5hdGluZyB1cGRhdGVcbiAgICAgICAgICAgICAgICAgICAgY29uc3RyYWludHMucHVzaCh7XG4gICAgICAgICAgICAgICAgICAgICAgICBBRERfT1BSRDE6IHJlY3ZBbmRSZXRbMV0sXG4gICAgICAgICAgICAgICAgICAgICAgICBBRERfT1BSRDI6IHJoc0FWYWwsXG4gICAgICAgICAgICAgICAgICAgICAgICBSRVNVTFQ6IHJlc0FWYWxcbiAgICAgICAgICAgICAgICAgICAgfSk7XG4gICAgICAgICAgICAgICAgICAgIHJlY3ZBbmRSZXRbMV0ucHJvcGFnYXRlKG5ldyBjc3RyLklzQWRkZWQocmhzQVZhbCwgcmVzQVZhbCkpO1xuICAgICAgICAgICAgICAgICAgICByaHNBVmFsLnByb3BhZ2F0ZShuZXcgY3N0ci5Jc0FkZGVkKHJlY3ZBbmRSZXRbMV0sIHJlc0FWYWwpKTtcbiAgICAgICAgICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgICAgICAgICAgICAvLyBhcml0aG1ldGljIHVwZGF0ZVxuICAgICAgICAgICAgICAgICAgICBjb25zdHJhaW50cy5wdXNoKHtcbiAgICAgICAgICAgICAgICAgICAgICAgIFRZUEU6IHR5cGVzLlByaW1OdW1iZXIsXG4gICAgICAgICAgICAgICAgICAgICAgICBJTkNMX1NFVDogcmVzQVZhbFxuICAgICAgICAgICAgICAgICAgICB9KTtcbiAgICAgICAgICAgICAgICAgICAgcmVzQVZhbC5hZGRUeXBlKHR5cGVzLlByaW1OdW1iZXIpO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICByZXR1cm4gcmVzQVZhbDtcbiAgICAgICAgICAgIH1cbiAgICAgICAgfSxcblxuICAgICAgICBWYXJpYWJsZURlY2xhcmF0aW9uOiBmdW5jdGlvbiAobm9kZSwgY3VyU3RhdHVzLCBjKSB7XG4gICAgICAgICAgICBmb3IgKGxldCBpID0gMDsgaSA8IG5vZGUuZGVjbGFyYXRpb25zLmxlbmd0aDsgaSsrKSB7XG4gICAgICAgICAgICAgICAgY29uc3QgZGVjbCA9IG5vZGUuZGVjbGFyYXRpb25zW2ldO1xuICAgICAgICAgICAgICAgIGlmIChkZWNsLmluaXQpIHtcbiAgICAgICAgICAgICAgICAgICAgY29uc3QgbGhzQVZhbCA9IGN1clN0YXR1cy5zYy5nZXRBVmFsT2YoZGVjbC5pZC5uYW1lKTtcbiAgICAgICAgICAgICAgICAgICAgY29uc3QgcmhzQVZhbCA9IGMoZGVjbC5pbml0LCBjdXJTdGF0dXMsIHVuZGVmaW5lZCk7XG4gICAgICAgICAgICAgICAgICAgIGNvbnN0cmFpbnRzLnB1c2goe0ZST006IHJoc0FWYWwsXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIFRPOiBsaHNBVmFsfSk7XG4gICAgICAgICAgICAgICAgICAgIHJoc0FWYWwucHJvcGFnYXRlKGxoc0FWYWwpO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgIH1cbiAgICAgICAgfSxcblxuICAgICAgICBMb2dpY2FsRXhwcmVzc2lvbjogZnVuY3Rpb24gKG5vZGUsIGN1clN0YXR1cywgYykge1xuICAgICAgICAgICAgY29uc3QgcmVzID0gbmV3IHR5cGVzLkFWYWw7XG4gICAgICAgICAgICBjb25zdCBsZWZ0ID0gYyhub2RlLmxlZnQsIGN1clN0YXR1cywgdW5kZWZpbmVkKTtcbiAgICAgICAgICAgIGNvbnN0IHJpZ2h0ID0gYyhub2RlLnJpZ2h0LCBjdXJTdGF0dXMsIHVuZGVmaW5lZCk7XG4gICAgICAgICAgICBjb25zdHJhaW50cy5wdXNoKHtGUk9NOiBsZWZ0LCBUTzogcmVzfSxcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAge0ZST006IHJpZ2h0LCBUTzogcmVzfSk7XG4gICAgICAgICAgICBsZWZ0LnByb3BhZ2F0ZShyZXMpO1xuICAgICAgICAgICAgcmlnaHQucHJvcGFnYXRlKHJlcyk7XG4gICAgICAgICAgICByZXR1cm4gcmVzO1xuICAgICAgICB9LFxuXG4gICAgICAgIENvbmRpdGlvbmFsRXhwcmVzc2lvbjogZnVuY3Rpb24gKG5vZGUsIGN1clN0YXR1cywgYykge1xuICAgICAgICAgICAgY29uc3QgcmVzID0gbmV3IHR5cGVzLkFWYWw7XG4gICAgICAgICAgICBjKG5vZGUudGVzdCwgY3VyU3RhdHVzLCB1bmRlZmluZWQpO1xuICAgICAgICAgICAgY29uc3QgY29ucyA9IGMobm9kZS5jb25zZXF1ZW50LCBjdXJTdGF0dXMsIHVuZGVmaW5lZCk7XG4gICAgICAgICAgICBjb25zdCBhbHQgPSBjKG5vZGUuYWx0ZXJuYXRlLCBjdXJTdGF0dXMsIHVuZGVmaW5lZCk7XG4gICAgICAgICAgICBjb25zdHJhaW50cy5wdXNoKHtGUk9NOiBjb25zLCBUTzogcmVzfSxcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAge0ZST006IGFsdCwgVE86IHJlc30pO1xuICAgICAgICAgICAgY29ucy5wcm9wYWdhdGUocmVzKTtcbiAgICAgICAgICAgIGFsdC5wcm9wYWdhdGUocmVzKTtcbiAgICAgICAgICAgIHJldHVybiByZXM7XG4gICAgICAgIH0sXG5cbiAgICAgICAgTmV3RXhwcmVzc2lvbjogZnVuY3Rpb24gKG5vZGUsIGN1clN0YXR1cywgYykge1xuICAgICAgICAgICAgY29uc3QgcmV0ID0gbmV3IHR5cGVzLkFWYWw7XG4gICAgICAgICAgICBjb25zdCBjYWxsZWUgPSBjKG5vZGUuY2FsbGVlLCBjdXJTdGF0dXMsIHVuZGVmaW5lZCk7XG4gICAgICAgICAgICBjb25zdCBhcmdzID0gW107XG4gICAgICAgICAgICBmb3IgKGxldCBpID0gMDsgaSA8IG5vZGUuYXJndW1lbnRzLmxlbmd0aDsgaSsrKSB7XG4gICAgICAgICAgICAgICAgYXJncy5wdXNoKGMobm9kZS5hcmd1bWVudHNbaV0sIGN1clN0YXR1cywgdW5kZWZpbmVkKSk7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBjb25zdCBuZXdEZWx0YSA9IGN1clN0YXR1cy5kZWx0YS5hcHBlbmRPbmUobm9kZVsnQGxhYmVsJ10pO1xuICAgICAgICAgICAgY29uc3RyYWludHMucHVzaCh7Q09OU1RSVUNUT1I6IGNhbGxlZSxcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIEFSR1M6IGFyZ3MsXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICBSRVQ6IHJldCxcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIEVYQzogY3VyU3RhdHVzLmV4YyxcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIERFTFRBOiBuZXdEZWx0YX0pO1xuICAgICAgICAgICAgY2FsbGVlLnByb3BhZ2F0ZShcbiAgICAgICAgICAgICAgICBuZXcgY3N0ci5Jc0N0b3IoXG4gICAgICAgICAgICAgICAgICAgIGFyZ3MsXG4gICAgICAgICAgICAgICAgICAgIHJldCxcbiAgICAgICAgICAgICAgICAgICAgY3VyU3RhdHVzLmV4YyxcbiAgICAgICAgICAgICAgICAgICAgbmV3RGVsdGEpKTtcbiAgICAgICAgICAgIHJldHVybiByZXQ7XG4gICAgICAgIH0sXG5cbiAgICAgICAgQXJyYXlFeHByZXNzaW9uOiBmdW5jdGlvbiAobm9kZSwgY3VyU3RhdHVzLCBjKSB7XG4gICAgICAgICAgICBjb25zdCByZXQgPSBuZXcgdHlwZXMuQVZhbDtcbiAgICAgICAgICAgIGNvbnN0IGFyclR5cGUgPSBuZXcgdHlwZXMuQXJyVHlwZShuZXcgdHlwZXMuQVZhbChydENYLnByb3Rvcy5BcnJheSkpO1xuICAgICAgICAgICAgLy8gYWRkIGxlbmd0aCBwcm9wZXJ0eVxuICAgICAgICAgICAgYXJyVHlwZS5nZXRQcm9wKCdsZW5ndGgnKS5hZGRUeXBlKHR5cGVzLlByaW1OdW1iZXIpO1xuXG4gICAgICAgICAgICBjb25zdHJhaW50cy5wdXNoKHtUWVBFOiBhcnJUeXBlLCBJTkNMX1NFVDogcmV0fSk7XG4gICAgICAgICAgICByZXQuYWRkVHlwZShhcnJUeXBlKTtcblxuICAgICAgICAgICAgLy8gYWRkIGFycmF5IGVsZW1lbnRzXG4gICAgICAgICAgICBmb3IgKGxldCBpID0gMDsgaSA8IG5vZGUuZWxlbWVudHMubGVuZ3RoOyBpKyspIHtcbiAgICAgICAgICAgICAgICBjb25zdCBlbHRBVmFsID0gYyhub2RlLmVsZW1lbnRzW2ldLCBjdXJTdGF0dXMsIHVuZGVmaW5lZCk7XG5cbiAgICAgICAgICAgICAgICBjb25zdCBwcm9wID0gaSArICcnO1xuICAgICAgICAgICAgICAgIGNvbnN0cmFpbnRzLnB1c2goe09CSjogcmV0LCBQUk9QOiBwcm9wLCBBVkFMOiBlbHRBVmFsfSk7XG4gICAgICAgICAgICAgICAgY29uc3RyYWludHMucHVzaCh7T0JKOiByZXQsIFBST1A6IG51bGwsIEFWQUw6IGVsdEFWYWx9KTtcbiAgICAgICAgICAgICAgICByZXQucHJvcGFnYXRlKG5ldyBjc3RyLldyaXRlUHJvcChwcm9wLCBlbHRBVmFsKSk7XG4gICAgICAgICAgICAgICAgcmV0LnByb3BhZ2F0ZShuZXcgY3N0ci5Xcml0ZVByb3AobnVsbCwgZWx0QVZhbCkpO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgcmV0dXJuIHJldDtcbiAgICAgICAgfSxcblxuICAgICAgICBPYmplY3RFeHByZXNzaW9uOiBmdW5jdGlvbiAobm9kZSwgY3VyU3RhdHVzLCBjKSB7XG4gICAgICAgICAgICBjb25zdCByZXQgPSBuZXcgdHlwZXMuQVZhbDtcbiAgICAgICAgICAgIGNvbnN0IG9ialR5cGUgPSBuZXcgdHlwZXMuT2JqVHlwZShuZXcgdHlwZXMuQVZhbChydENYLnByb3Rvcy5PYmplY3QpKTtcbiAgICAgICAgICAgIGNvbnN0cmFpbnRzLnB1c2goe1RZUEU6IG9ialR5cGUsIElOQ0xfU0VUOiByZXR9KTtcbiAgICAgICAgICAgIHJldC5hZGRUeXBlKG9ialR5cGUpO1xuXG4gICAgICAgICAgICBmb3IgKGxldCBpID0gMDsgaSA8IG5vZGUucHJvcGVydGllcy5sZW5ndGg7IGkrKykge1xuICAgICAgICAgICAgICAgIGNvbnN0IHByb3BQYWlyID0gbm9kZS5wcm9wZXJ0aWVzW2ldO1xuICAgICAgICAgICAgICAgIGNvbnN0IHByb3BLZXkgPSBwcm9wUGFpci5rZXk7XG4gICAgICAgICAgICAgICAgbGV0IG5hbWU7XG4gICAgICAgICAgICAgICAgY29uc3QgcHJvcEV4cHIgPSBwcm9wUGFpci52YWx1ZTtcblxuICAgICAgICAgICAgICAgIGNvbnN0IGZsZEFWYWwgPSBjKHByb3BFeHByLCBjdXJTdGF0dXMsIHVuZGVmaW5lZCk7XG5cbiAgICAgICAgICAgICAgICBpZiAocHJvcEtleS50eXBlID09PSAnSWRlbnRpZmllcicpIHtcbiAgICAgICAgICAgICAgICAgICAgbmFtZSA9IHByb3BLZXkubmFtZTtcbiAgICAgICAgICAgICAgICB9IGVsc2UgaWYgKHR5cGVvZiBwcm9wS2V5LnZhbHVlID09PSAnc3RyaW5nJykge1xuICAgICAgICAgICAgICAgICAgICBuYW1lID0gcHJvcEtleS52YWx1ZTtcbiAgICAgICAgICAgICAgICB9IGVsc2UgaWYgKHR5cGVvZiBwcm9wS2V5LnZhbHVlID09PSAnbnVtYmVyJykge1xuICAgICAgICAgICAgICAgICAgICAvLyBjb252ZXJ0IG51bWJlciB0byBzdHJpbmdcbiAgICAgICAgICAgICAgICAgICAgbmFtZSA9IHByb3BLZXkudmFsdWUgKyAnJztcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgY29uc3RyYWludHMucHVzaCh7T0JKOiByZXQsIFBST1A6IG5hbWUsIEFWQUw6IGZsZEFWYWx9KTtcbiAgICAgICAgICAgICAgICByZXQucHJvcGFnYXRlKG5ldyBjc3RyLldyaXRlUHJvcChuYW1lLCBmbGRBVmFsKSk7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICByZXR1cm4gcmV0O1xuICAgICAgICB9LFxuXG4gICAgICAgIEZ1bmN0aW9uRXhwcmVzc2lvbjogZnVuY3Rpb24gKG5vZGUsIGN1clN0YXR1cywgYykge1xuICAgICAgICAgICAgaWYgKCFub2RlLmZuSW5zdGFuY2VzKSB7XG4gICAgICAgICAgICAgICAgbm9kZS5mbkluc3RhbmNlcyA9IFtdO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgbGV0IGZuSW5zdGFuY2UgPSBudWxsO1xuICAgICAgICAgICAgbm9kZS5mbkluc3RhbmNlcy5mb3JFYWNoKGZ1bmN0aW9uIChmblR5cGUpIHtcbiAgICAgICAgICAgICAgICBpZiAoZm5UeXBlLnNjID09PSBjdXJTdGF0dXMuc2MpIHtcbiAgICAgICAgICAgICAgICAgICAgZm5JbnN0YW5jZSA9IGZuVHlwZTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICB9KTtcbiAgICAgICAgICAgIGlmICghZm5JbnN0YW5jZSkge1xuICAgICAgICAgICAgICAgIGZuSW5zdGFuY2VcbiAgICAgICAgICAgICAgICAgICAgPSBuZXcgdHlwZXMuRm5UeXBlKG5ldyB0eXBlcy5BVmFsKHJ0Q1gucHJvdG9zLkZ1bmN0aW9uKSxcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICdbYW5vbnltb3VzIGZ1bmN0aW9uXScsXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBub2RlLmJvZHlbJ0BibG9jayddLmdldFBhcmFtVmFyTmFtZXMoKSxcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGN1clN0YXR1cy5zYyxcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIG5vZGUsXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBydENYLnByb3Rvcy5PYmplY3QpO1xuICAgICAgICAgICAgICAgIG5vZGUuZm5JbnN0YW5jZXMucHVzaChmbkluc3RhbmNlKTtcbiAgICAgICAgICAgICAgICBjb25zdCBwcm90b3R5cGVPYmplY3QgPVxuICAgICAgICAgICAgICAgICAgICBuZXcgdHlwZXMuT2JqVHlwZShuZXcgdHlwZXMuQVZhbChydENYLnByb3Rvcy5PYmplY3QpLFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAnPy5wcm90b3R5cGUnKTtcbiAgICAgICAgICAgICAgICAvLyBGb3IgLnByb3RvdHlwZVxuICAgICAgICAgICAgICAgIGNvbnN0IHByb3RvdHlwZVByb3AgPSBmbkluc3RhbmNlLmdldFByb3AoJ3Byb3RvdHlwZScpO1xuICAgICAgICAgICAgICAgIGNvbnN0cmFpbnRzLnB1c2goe1RZUEU6IHByb3RvdHlwZU9iamVjdCxcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBJTkNMX1NFVDogcHJvdG90eXBlUHJvcH0pO1xuICAgICAgICAgICAgICAgIHByb3RvdHlwZVByb3AuYWRkVHlwZShwcm90b3R5cGVPYmplY3QpO1xuICAgICAgICAgICAgICAgIC8vIEZvciAucHJvdG90eXBlLmNvbnN0cnVjdG9yXG4gICAgICAgICAgICAgICAgY29uc3QgY29uc3RydWN0b3JQcm9wID0gcHJvdG90eXBlT2JqZWN0LmdldFByb3AoJ2NvbnN0cnVjdG9yJyk7XG4gICAgICAgICAgICAgICAgY29uc3RyYWludHMucHVzaCh7VFlQRTogZm5JbnN0YW5jZSxcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBJTkNMX1NFVDogY29uc3RydWN0b3JQcm9wfSk7XG4gICAgICAgICAgICAgICAgY29uc3RydWN0b3JQcm9wLmFkZFR5cGUoZm5JbnN0YW5jZSk7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBjb25zdCByZXQgPSBuZXcgdHlwZXMuQVZhbDtcbiAgICAgICAgICAgIGNvbnN0cmFpbnRzLnB1c2goe1RZUEU6IGZuSW5zdGFuY2UsXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICBJTkNMX1NFVDogcmV0fSk7XG4gICAgICAgICAgICByZXQuYWRkVHlwZShmbkluc3RhbmNlKTtcbiAgICAgICAgICAgIHJldHVybiByZXQ7XG4gICAgICAgIH0sXG5cbiAgICAgICAgRnVuY3Rpb25EZWNsYXJhdGlvbjogZnVuY3Rpb24gKG5vZGUsIGN1clN0YXR1cywgYykge1xuICAgICAgICAgICAgLy8gRHJvcCBpbml0aWFsIGNhdGNoIHNjb3Blc1xuICAgICAgICAgICAgY29uc3Qgc2MwID0gY3VyU3RhdHVzLnNjLnJlbW92ZUluaXRpYWxDYXRjaEJsb2NrcygpO1xuICAgICAgICAgICAgaWYgKCFub2RlLmZuSW5zdGFuY2VzKSB7XG4gICAgICAgICAgICAgICAgbm9kZS5mbkluc3RhbmNlcyA9IFtdO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgbGV0IGZuSW5zdGFuY2UgPSBudWxsO1xuICAgICAgICAgICAgbm9kZS5mbkluc3RhbmNlcy5mb3JFYWNoKGZ1bmN0aW9uIChmblR5cGUpIHtcbiAgICAgICAgICAgICAgICBpZiAoZm5UeXBlLnNjID09PSBzYzApIHtcbiAgICAgICAgICAgICAgICAgICAgZm5JbnN0YW5jZSA9IGZuVHlwZTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICB9KTtcbiAgICAgICAgICAgIGlmICghZm5JbnN0YW5jZSkge1xuICAgICAgICAgICAgICAgIGZuSW5zdGFuY2VcbiAgICAgICAgICAgICAgICAgICAgPSBuZXcgdHlwZXMuRm5UeXBlKG5ldyB0eXBlcy5BVmFsKHJ0Q1gucHJvdG9zLkZ1bmN0aW9uKSxcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIG5vZGUuaWQubmFtZSxcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIG5vZGUuYm9keVsnQGJsb2NrJ10uZ2V0UGFyYW1WYXJOYW1lcygpLFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgc2MwLFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgbm9kZSxcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIHJ0Q1gucHJvdG9zLk9iamVjdCk7XG4gICAgICAgICAgICAgICAgbm9kZS5mbkluc3RhbmNlcy5wdXNoKGZuSW5zdGFuY2UpO1xuICAgICAgICAgICAgICAgIC8vIGZvciBlYWNoIGZuSW5zdGFuY2UsIGFzc2lnbiBvbmUgcHJvdG90eXBlIG9iamVjdFxuICAgICAgICAgICAgICAgIGNvbnN0IHByb3RvdHlwZU9iamVjdCA9XG4gICAgICAgICAgICAgICAgICAgIG5ldyB0eXBlcy5PYmpUeXBlKG5ldyB0eXBlcy5BVmFsKHJ0Q1gucHJvdG9zLk9iamVjdCksXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIG5vZGUuaWQubmFtZSArICcucHJvdG90eXBlJyk7XG4gICAgICAgICAgICAgICAgLy8gRm9yIC5wcm90b3R5cGVcbiAgICAgICAgICAgICAgICBjb25zdCBwcm90b3R5cGVQcm9wID0gZm5JbnN0YW5jZS5nZXRQcm9wKCdwcm90b3R5cGUnKTtcbiAgICAgICAgICAgICAgICBjb25zdHJhaW50cy5wdXNoKHtUWVBFOiBwcm90b3R5cGVPYmplY3QsXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgSU5DTF9TRVQ6IHByb3RvdHlwZVByb3B9KTtcbiAgICAgICAgICAgICAgICBwcm90b3R5cGVQcm9wLmFkZFR5cGUocHJvdG90eXBlT2JqZWN0KTtcbiAgICAgICAgICAgICAgICAvLyBGb3IgLnByb3RvdHlwZS5jb25zdHJ1Y3RvclxuICAgICAgICAgICAgICAgIGNvbnN0IGNvbnN0cnVjdG9yUHJvcCA9IHByb3RvdHlwZU9iamVjdC5nZXRQcm9wKCdjb25zdHJ1Y3RvcicpO1xuICAgICAgICAgICAgICAgIGNvbnN0cmFpbnRzLnB1c2goe1RZUEU6IGZuSW5zdGFuY2UsXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgSU5DTF9TRVQ6IGNvbnN0cnVjdG9yUHJvcH0pO1xuICAgICAgICAgICAgICAgIGNvbnN0cnVjdG9yUHJvcC5hZGRUeXBlKGZuSW5zdGFuY2UpO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgY29uc3QgbGhzQVZhbCA9IHNjMC5nZXRBVmFsT2Yobm9kZS5pZC5uYW1lKTtcblxuICAgICAgICAgICAgY29uc3RyYWludHMucHVzaCh7VFlQRTogZm5JbnN0YW5jZSxcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIElOQ0xfU0VUOiBsaHNBVmFsfSk7XG4gICAgICAgICAgICBsaHNBVmFsLmFkZFR5cGUoZm5JbnN0YW5jZSk7XG4gICAgICAgICAgICAvLyBub3RoaW5nIHRvIHJldHVyblxuICAgICAgICAgICAgcmV0dXJuIHR5cGVzLkFWYWxOdWxsO1xuICAgICAgICB9LFxuXG4gICAgICAgIFNlcXVlbmNlRXhwcmVzc2lvbjogZnVuY3Rpb24gKG5vZGUsIGN1clN0YXR1cywgYykge1xuICAgICAgICAgICAgY29uc3QgbGFzdEluZGV4ID0gbm9kZS5leHByZXNzaW9ucy5sZW5ndGggLSAxO1xuICAgICAgICAgICAgZm9yIChsZXQgaSA9IDA7IGkgPCBsYXN0SW5kZXg7IGkrKykge1xuICAgICAgICAgICAgICAgIGMobm9kZS5leHByZXNzaW9uc1tpXSwgY3VyU3RhdHVzLCB1bmRlZmluZWQpO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgcmV0dXJuIGMobm9kZS5leHByZXNzaW9uc1tsYXN0SW5kZXhdLCBjdXJTdGF0dXMsIHVuZGVmaW5lZCk7XG4gICAgICAgIH0sXG5cbiAgICAgICAgVW5hcnlFeHByZXNzaW9uOiBmdW5jdGlvbiAobm9kZSwgY3VyU3RhdHVzLCBjKSB7XG4gICAgICAgICAgICBjKG5vZGUuYXJndW1lbnQsIGN1clN0YXR1cywgdW5kZWZpbmVkKTtcbiAgICAgICAgICAgIGNvbnN0IHJlcyA9IG5ldyB0eXBlcy5BVmFsO1xuICAgICAgICAgICAgY29uc3QgdHlwZSA9IHVub3BSZXN1bHRUeXBlKG5vZGUub3BlcmF0b3IpO1xuICAgICAgICAgICAgaWYgKHR5cGUpIHtcbiAgICAgICAgICAgICAgICBjb25zdHJhaW50cy5wdXNoKHtUWVBFOiB0eXBlLFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIElOQ0xfU0VUOiByZXN9KTtcbiAgICAgICAgICAgICAgICByZXMuYWRkVHlwZSh0eXBlKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIHJldHVybiByZXM7XG4gICAgICAgIH0sXG5cbiAgICAgICAgVXBkYXRlRXhwcmVzc2lvbjogZnVuY3Rpb24gKG5vZGUsIGN1clN0YXR1cywgYykge1xuICAgICAgICAgICAgYyhub2RlLmFyZ3VtZW50LCBjdXJTdGF0dXMsIHVuZGVmaW5lZCk7XG4gICAgICAgICAgICBjb25zdCByZXMgPSBuZXcgdHlwZXMuQVZhbDtcbiAgICAgICAgICAgIGNvbnN0cmFpbnRzLnB1c2goe1RZUEU6IHR5cGVzLlByaW1OdW1iZXIsXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICBJTkNMX1NFVDogcmVzfSk7XG4gICAgICAgICAgICByZXMuYWRkVHlwZSh0eXBlcy5QcmltTnVtYmVyKTtcbiAgICAgICAgICAgIC8vIFdlIGlnbm9yZSB0aGUgZWZmZWN0IG9mIHVwZGF0aW5nIHRvIG51bWJlciB0eXBlXG4gICAgICAgICAgICByZXR1cm4gcmVzO1xuICAgICAgICB9LFxuXG4gICAgICAgIEJpbmFyeUV4cHJlc3Npb246IGZ1bmN0aW9uIChub2RlLCBjdXJTdGF0dXMsIGMpIHtcbiAgICAgICAgICAgIGNvbnN0IGxPcHJkID0gYyhub2RlLmxlZnQsIGN1clN0YXR1cywgdW5kZWZpbmVkKTtcbiAgICAgICAgICAgIGNvbnN0IHJPcHJkID0gYyhub2RlLnJpZ2h0LCBjdXJTdGF0dXMsIHVuZGVmaW5lZCk7XG4gICAgICAgICAgICBjb25zdCByZXMgPSBuZXcgdHlwZXMuQVZhbDtcblxuICAgICAgICAgICAgaWYgKG5vZGUub3BlcmF0b3IgPT0gJysnKSB7XG4gICAgICAgICAgICAgICAgY29uc3RyYWludHMucHVzaCh7QUREX09QUkQxOiBsT3ByZCxcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBBRERfT1BSRDI6IHJPcHJkLFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIFJFU1VMVDogcmVzIH0pO1xuICAgICAgICAgICAgICAgIGxPcHJkLnByb3BhZ2F0ZShuZXcgY3N0ci5Jc0FkZGVkKHJPcHJkLCByZXMpKTtcbiAgICAgICAgICAgICAgICByT3ByZC5wcm9wYWdhdGUobmV3IGNzdHIuSXNBZGRlZChsT3ByZCwgcmVzKSk7XG4gICAgICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgICAgICAgIGlmIChiaW5vcElzQm9vbGVhbihub2RlLm9wZXJhdG9yKSkge1xuICAgICAgICAgICAgICAgICAgICBjb25zdHJhaW50cy5wdXNoKHtUWVBFOiB0eXBlcy5QcmltQm9vbGVhbixcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgSU5DTF9TRVQ6IHJlc30pO1xuICAgICAgICAgICAgICAgICAgICByZXMuYWRkVHlwZSh0eXBlcy5QcmltQm9vbGVhbik7XG4gICAgICAgICAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgY29uc3RyYWludHMucHVzaCh7VFlQRTogdHlwZXMuUHJpbU51bWJlcixcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgSU5DTF9TRVQ6IHJlc30pO1xuICAgICAgICAgICAgICAgICAgICByZXMuYWRkVHlwZSh0eXBlcy5QcmltTnVtYmVyKTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICByZXR1cm4gcmVzO1xuICAgICAgICB9LFxuXG4gICAgICAgIFRyeVN0YXRlbWVudDogZnVuY3Rpb24gKG5vZGUsIGN1clN0YXR1cywgYykge1xuICAgICAgICAgICAgLy8gY29uc3RydWN0IHNjb3BlIGNoYWluIGZvciBjYXRjaCBibG9ja1xuICAgICAgICAgICAgY29uc3QgY2F0Y2hCbG9ja1NDID1cbiAgICAgICAgICAgICAgICBub2RlLmhhbmRsZXIuYm9keVsnQGJsb2NrJ11cbiAgICAgICAgICAgICAgICAuZ2V0U2NvcGVJbnN0YW5jZShjdXJTdGF0dXMuc2MsIGN1clN0YXR1cy5kZWx0YSk7XG4gICAgICAgICAgICAvLyBnZXQgdGhlIEFWYWwgZm9yIGV4Y2VwdGlvbiBwYXJhbWV0ZXJcbiAgICAgICAgICAgIGNvbnN0IGV4Y0FWYWwgPSBjYXRjaEJsb2NrU0MuZ2V0QVZhbE9mKG5vZGUuaGFuZGxlci5wYXJhbS5uYW1lKTtcblxuICAgICAgICAgICAgLy8gZm9yIHRyeSBibG9ja1xuICAgICAgICAgICAgY29uc3QgdHJ5U3RhdHVzID0gY2hhbmdlZFN0YXR1cyhjdXJTdGF0dXMsICdleGMnLCBleGNBVmFsKTtcbiAgICAgICAgICAgIGMobm9kZS5ibG9jaywgdHJ5U3RhdHVzLCB1bmRlZmluZWQpO1xuXG4gICAgICAgICAgICAvLyBmb3IgY2F0Y2ggYmxvY2tcbiAgICAgICAgICAgIGNvbnN0IGNhdGNoU3RhdHVzID0gY2hhbmdlZFN0YXR1cyhjdXJTdGF0dXMsICdzYycsIGNhdGNoQmxvY2tTQyk7XG4gICAgICAgICAgICBjKG5vZGUuaGFuZGxlci5ib2R5LCBjYXRjaFN0YXR1cywgdW5kZWZpbmVkKTtcblxuICAgICAgICAgICAgLy8gZm9yIGZpbmFsbHkgYmxvY2tcbiAgICAgICAgICAgIGlmIChub2RlLmZpbmFsaXplciAhPT0gbnVsbClcbiAgICAgICAgICAgICAgICBjKG5vZGUuZmluYWxpemVyLCBjdXJTdGF0dXMsIHVuZGVmaW5lZCk7XG4gICAgICAgIH0sXG5cbiAgICAgICAgVGhyb3dTdGF0ZW1lbnQ6IGZ1bmN0aW9uIChub2RlLCBjdXJTdGF0dXMsIGMpIHtcbiAgICAgICAgICAgIGNvbnN0IHRociA9IGMobm9kZS5hcmd1bWVudCwgY3VyU3RhdHVzLCB1bmRlZmluZWQpO1xuICAgICAgICAgICAgY29uc3RyYWludHMucHVzaCh7RlJPTTogdGhyLFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgVE86IGN1clN0YXR1cy5leGN9KTtcbiAgICAgICAgICAgIHRoci5wcm9wYWdhdGUoY3VyU3RhdHVzLmV4Yyk7XG4gICAgICAgIH0sXG5cbiAgICAgICAgQ2FsbEV4cHJlc3Npb246IGZ1bmN0aW9uIChub2RlLCBjdXJTdGF0dXMsIGMpIHtcbiAgICAgICAgICAgIGNvbnN0IHJlc0FWYWwgPSBuZXcgdHlwZXMuQVZhbDtcbiAgICAgICAgICAgIGNvbnN0IGFyZ0FWYWxzID0gW107XG5cbiAgICAgICAgICAgIC8vIGdldCBBVmFscyBmb3IgZWFjaCBhcmd1bWVudHNcbiAgICAgICAgICAgIGZvciAobGV0IGkgPSAwOyBpIDwgbm9kZS5hcmd1bWVudHMubGVuZ3RoOyBpKyspIHtcbiAgICAgICAgICAgICAgICBhcmdBVmFscy5wdXNoKFxuICAgICAgICAgICAgICAgICAgICBjKG5vZGUuYXJndW1lbnRzW2ldLCBjdXJTdGF0dXMsIHVuZGVmaW5lZCkpO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgLy8gYXBwZW5kIGN1cnJlbnQgY2FsbCBzaXRlIHRvIHRoZSBjb250ZXh0XG4gICAgICAgICAgICBjb25zdCBuZXdEZWx0YSA9IGN1clN0YXR1cy5kZWx0YS5hcHBlbmRPbmUobm9kZVsnQGxhYmVsJ10pO1xuXG4gICAgICAgICAgICBpZiAobm9kZS5jYWxsZWUudHlwZSA9PT0gJ01lbWJlckV4cHJlc3Npb24nKSB7XG4gICAgICAgICAgICAgICAgLy8gbWV0aG9kIGNhbGxcbiAgICAgICAgICAgICAgICAvLyB2YXIgcmVjdiA9IGMobm9kZS5jYWxsZWUub2JqZWN0LCBjdXJTdGF0dXMsIHVuZGVmaW5lZCk7XG4gICAgICAgICAgICAgICAgLy8gdmFyIG1ldGhvZE5hbWUgPSBpbW1lZFByb3Aobm9kZS5jYWxsZWUpO1xuICAgICAgICAgICAgICAgIC8vIGNvbnN0cmFpbnRzLnB1c2goe1xuICAgICAgICAgICAgICAgIC8vICAgUkVDVjogcmVjdixcbiAgICAgICAgICAgICAgICAvLyAgIFBST1BOQU1FOiBtZXRob2ROYW1lLFxuICAgICAgICAgICAgICAgIC8vICAgUEFSQU1TOiBhcmdBVmFscyxcbiAgICAgICAgICAgICAgICAvLyAgIFJFVDogcmVzQVZhbCxcbiAgICAgICAgICAgICAgICAvLyAgIEVYQzogY3VyU3RhdHVzLmV4YyxcbiAgICAgICAgICAgICAgICAvLyAgIERFTFRBOiBuZXdEZWx0YVxuICAgICAgICAgICAgICAgIC8vIH0pO1xuICAgICAgICAgICAgICAgIGNvbnN0IHJlY3ZBbmRSZXQgPSByZWFkTWVtYmVyKG5vZGUuY2FsbGVlLCBjdXJTdGF0dXMsIGMpO1xuICAgICAgICAgICAgICAgIHJlY3ZBbmRSZXRbMV0ucHJvcGFnYXRlKFxuICAgICAgICAgICAgICAgICAgICBuZXcgY3N0ci5Jc0NhbGxlZShcbiAgICAgICAgICAgICAgICAgICAgICAgIHJlY3ZBbmRSZXRbMF0sXG4gICAgICAgICAgICAgICAgICAgICAgICBhcmdBVmFscyxcbiAgICAgICAgICAgICAgICAgICAgICAgIHJlc0FWYWwsXG4gICAgICAgICAgICAgICAgICAgICAgICBjdXJTdGF0dXMuZXhjLFxuICAgICAgICAgICAgICAgICAgICAgICAgbmV3RGVsdGEpKTtcbiAgICAgICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgICAgICAgLy8gbm9ybWFsIGZ1bmN0aW9uIGNhbGxcbiAgICAgICAgICAgICAgICBjb25zdCBjYWxsZWVBVmFsID0gYyhub2RlLmNhbGxlZSwgY3VyU3RhdHVzLCB1bmRlZmluZWQpO1xuICAgICAgICAgICAgICAgIC8vIGNhbGxlZeydmCByZXR1cm7snYQgY2FsbCBleHByZXNzaW9u7Jy866GcXG4gICAgICAgICAgICAgICAgLy8gY2FsbGVl7J2YIGV4Y2VwdGlvbuydhCDtmLjstpwg7Lih7J2YIGV4Y2VwdGlvbuyXkCDsoITri6ztlbTslbxcbiAgICAgICAgICAgICAgICBjb25zdHJhaW50cy5wdXNoKHtcbiAgICAgICAgICAgICAgICAgICAgQ0FMTEVFOiBjYWxsZWVBVmFsLFxuICAgICAgICAgICAgICAgICAgICBTRUxGOiBydENYLmdsb2JhbE9iamVjdCxcbiAgICAgICAgICAgICAgICAgICAgUEFSQU1TOiBhcmdBVmFscyxcbiAgICAgICAgICAgICAgICAgICAgUkVUOiByZXNBVmFsLFxuICAgICAgICAgICAgICAgICAgICBFWEM6IGN1clN0YXR1cy5leGMsXG4gICAgICAgICAgICAgICAgICAgIERFTFRBOiBuZXdEZWx0YVxuICAgICAgICAgICAgICAgIH0pO1xuICAgICAgICAgICAgICAgIGNhbGxlZUFWYWwucHJvcGFnYXRlKFxuICAgICAgICAgICAgICAgICAgICBuZXcgY3N0ci5Jc0NhbGxlZShcbiAgICAgICAgICAgICAgICAgICAgICAgIG5ldyB0eXBlcy5BVmFsKHJ0Q1guZ2xvYmFsT2JqZWN0KSxcbiAgICAgICAgICAgICAgICAgICAgICAgIGFyZ0FWYWxzLFxuICAgICAgICAgICAgICAgICAgICAgICAgcmVzQVZhbCxcbiAgICAgICAgICAgICAgICAgICAgICAgIGN1clN0YXR1cy5leGMsXG4gICAgICAgICAgICAgICAgICAgICAgICBuZXdEZWx0YSkpO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgcmV0dXJuIHJlc0FWYWw7XG4gICAgICAgIH0sXG5cbiAgICAgICAgTWVtYmVyRXhwcmVzc2lvbjogZnVuY3Rpb24gKG5vZGUsIGN1clN0YXR1cywgYykge1xuICAgICAgICAgICAgY29uc3QgcmVjdkFuZFJldCA9IHJlYWRNZW1iZXIobm9kZSwgY3VyU3RhdHVzLCBjKTtcbiAgICAgICAgICAgIHJldHVybiByZWN2QW5kUmV0WzFdO1xuICAgICAgICB9LFxuXG4gICAgICAgIFJldHVyblN0YXRlbWVudDogZnVuY3Rpb24gKG5vZGUsIGN1clN0YXR1cywgYykge1xuICAgICAgICAgICAgaWYgKCFub2RlLmFyZ3VtZW50KSByZXR1cm47XG4gICAgICAgICAgICBjb25zdCByZXQgPSBjKG5vZGUuYXJndW1lbnQsIGN1clN0YXR1cywgdW5kZWZpbmVkKTtcbiAgICAgICAgICAgIGNvbnN0cmFpbnRzLnB1c2goe0ZST006IHJldCxcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIFRPOiBjdXJTdGF0dXMucmV0fSk7XG4gICAgICAgICAgICByZXQucHJvcGFnYXRlKGN1clN0YXR1cy5yZXQpO1xuICAgICAgICB9XG4gICAgfSk7XG5cbiAgICByZWN1cnNpdmVXaXRoUmV0dXJuKGFzdCwgaW5pdFN0YXR1cywgY29uc3RyYWludEdlbmVyYXRvcik7XG5cbiAgICAvLyBXZSBhY3R1YWxseSBhZGRlZCBjb25zdHJhaW50c1xuICAgIHJldHVybiB0cnVlO1xufVxuXG5mdW5jdGlvbiByZWN1cnNpdmVXaXRoUmV0dXJuKG5vZGUsIHN0YXRlLCB2aXNpdG9yKSB7XG4gICAgZnVuY3Rpb24gYyhub2RlLCBzdCwgb3ZlcnJpZGUpIHtcbiAgICAgICAgcmV0dXJuIHZpc2l0b3Jbb3ZlcnJpZGUgfHwgbm9kZS50eXBlXShub2RlLCBzdCwgYyk7XG4gICAgfVxuICAgIHJldHVybiBjKG5vZGUsIHN0YXRlKTtcbn1cblxuZXhwb3J0cy5jb25zdHJhaW50cyA9IGNvbnN0cmFpbnRzO1xuZXhwb3J0cy5hZGRDb25zdHJhaW50cyA9IGFkZENvbnN0cmFpbnRzO1xuZXhwb3J0cy5jbGVhckNvbnN0cmFpbnRzID0gY2xlYXJDb25zdHJhaW50cztcbiIsIid1c2Ugc3RyaWN0JztcblxuY29uc3QgdHlwZXMgPSByZXF1aXJlKCcuLi9kb21haW5zL3R5cGVzJyk7XG5jb25zdCBzdGF0dXMgPSByZXF1aXJlKCcuLi9kb21haW5zL3N0YXR1cycpO1xuY29uc3QgY0dlbiA9IHJlcXVpcmUoJy4vY0dlbicpO1xuXG5mdW5jdGlvbiBDU1RSKCkge31cbkNTVFIucHJvdG90eXBlID0gT2JqZWN0LmNyZWF0ZShudWxsKTtcbkNTVFIucHJvdG90eXBlLmVxdWFscyA9IGZ1bmN0aW9uIChvdGhlcikge1xuICAgIHJldHVybiB0aGlzID09PSBvdGhlcjtcbn07XG5cbmZ1bmN0aW9uIFJlYWRQcm9wKHByb3AsIHRvKSB7XG4gICAgdGhpcy5wcm9wID0gcHJvcDtcbiAgICB0aGlzLnRvID0gdG87XG59XG5SZWFkUHJvcC5wcm90b3R5cGUgPSBPYmplY3QuY3JlYXRlKENTVFIucHJvdG90eXBlKTtcblJlYWRQcm9wLnByb3RvdHlwZS5hZGRUeXBlID0gZnVuY3Rpb24gKG9iaikge1xuICAgIGlmICghKG9iaiBpbnN0YW5jZW9mICh0eXBlcy5PYmpUeXBlKSkpIHJldHVybjtcbiAgICAvLyB3aGVuIG9iaiBpcyBPYmpUeXBlLFxuICAgIGNvbnN0IG93blByb3AgPSBvYmouZ2V0UHJvcCh0aGlzLnByb3AsIHRydWUpO1xuICAgIGlmIChvd25Qcm9wKSB7XG4gICAgICAgIC8vIHdoZW4gdGhlIG9iamVjdCBoYXMgdGhlIHByb3AsXG4gICAgICAgIG93blByb3AucHJvcGFnYXRlKHRoaXMudG8pO1xuICAgIH0gZWxzZSBpZiAob2JqLmdldFByb3AoJ19fcHJvdG9fXycsIHRydWUpKSB7XG4gICAgICAgIC8vIHVzZSBwcm90b3R5cGUgY2hhaW5cbiAgICAgICAgb2JqLmdldFByb3AoJ19fcHJvdG9fXycpXG4gICAgICAgICAgLnByb3BhZ2F0ZShuZXcgUmVhZFByb3AodGhpcy5wcm9wLCB0aGlzLnRvKSk7XG4gICAgfVxufTtcblJlYWRQcm9wLnByb3RvdHlwZS5lcXVhbHMgPSBmdW5jdGlvbiAob3RoZXIpIHtcbiAgICBpZiAoIShvdGhlciBpbnN0YW5jZW9mIFJlYWRQcm9wKSkgcmV0dXJuIGZhbHNlO1xuICAgIHJldHVybiB0aGlzLnByb3AgPT09IG90aGVyLnByb3BcbiAgICAgICAgJiYgdGhpcy50by5lcXVhbHMob3RoZXIudG8pO1xufTtcblxuZnVuY3Rpb24gV3JpdGVQcm9wKHByb3AsIGZyb20pIHtcbiAgICB0aGlzLnByb3AgPSBwcm9wO1xuICAgIHRoaXMuZnJvbSA9IGZyb207XG59XG5Xcml0ZVByb3AucHJvdG90eXBlID0gT2JqZWN0LmNyZWF0ZShDU1RSLnByb3RvdHlwZSk7XG5Xcml0ZVByb3AucHJvdG90eXBlLmFkZFR5cGUgPSBmdW5jdGlvbiAob2JqKSB7XG4gICAgaWYgKCEob2JqIGluc3RhbmNlb2YgKHR5cGVzLk9ialR5cGUpKSkgcmV0dXJuO1xuICAgIGNvbnN0IG93blByb3AgPSBvYmouZ2V0UHJvcCh0aGlzLnByb3ApO1xuICAgIHRoaXMuZnJvbS5wcm9wYWdhdGUob3duUHJvcCk7XG59O1xuXG5mdW5jdGlvbiBJc0FkZGVkKG90aGVyLCB0YXJnZXQpIHtcbiAgICB0aGlzLm90aGVyID0gb3RoZXI7XG4gICAgdGhpcy50YXJnZXQgPSB0YXJnZXQ7XG59XG5Jc0FkZGVkLnByb3RvdHlwZSA9IE9iamVjdC5jcmVhdGUoQ1NUUi5wcm90b3R5cGUpO1xuSXNBZGRlZC5wcm90b3R5cGUuYWRkVHlwZSA9IGZ1bmN0aW9uICh0eXBlKSB7XG4gICAgaWYgKCh0eXBlID09PSB0eXBlcy5QcmltTnVtYmVyIFxuICAgICAgICAgfHwgdHlwZSA9PT0gdHlwZXMuUHJpbUJvb2xlYW4pXG4gICAgICYmICh0aGlzLm90aGVyLmhhc1R5cGUodHlwZXMuUHJpbU51bWJlcikgXG4gICAgICAgICB8fCB0aGlzLm90aGVyLmhhc1R5cGUodHlwZXMuUHJpbUJvb2xlYW4pKSkge1xuICAgICAgICB0aGlzLnRhcmdldC5hZGRUeXBlKHR5cGVzLlByaW1OdW1iZXIpO1xuICAgIH1cbiAgICBpZiAodHlwZSA9PT0gdHlwZXMuUHJpbVN0cmluZ1xuICAgICAmJiAhdGhpcy5vdGhlci5pc0VtcHR5KCkpIHtcbiAgICAgICAgIHRoaXMudGFyZ2V0LmFkZFR5cGUodHlwZXMuUHJpbVN0cmluZyk7XG4gICAgfVxufTtcblxuZnVuY3Rpb24gSXNDYWxsZWUoc2VsZiwgYXJncywgcmV0LCBleGMsIGRlbHRhKSB7XG4gICAgdGhpcy5zZWxmID0gc2VsZjtcbiAgICB0aGlzLmFyZ3MgPSBhcmdzO1xuICAgIHRoaXMucmV0ID0gcmV0O1xuICAgIHRoaXMuZXhjID0gZXhjO1xuICAgIHRoaXMuZGVsdGEgPSBkZWx0YTtcbn1cbklzQ2FsbGVlLnByb3RvdHlwZSA9IE9iamVjdC5jcmVhdGUoQ1NUUi5wcm90b3R5cGUpO1xuSXNDYWxsZWUucHJvdG90eXBlLmFkZFR5cGUgPSBmdW5jdGlvbiAoZikge1xuICAgIGlmICghKGYgaW5zdGFuY2VvZiAodHlwZXMuRm5UeXBlKSkpIHJldHVybjtcbiAgICBjb25zdCBmdW5FbnYgPSBmLmdldEZ1bkVudih0aGlzLmRlbHRhKTtcbiAgICBjb25zdCBuZXdTQyA9IGYub3JpZ2luTm9kZS5ib2R5WydAYmxvY2snXS5nZXRTY29wZUluc3RhbmNlKGYuc2MsIHRoaXMuZGVsdGEpO1xuICAgIGNvbnN0IGZ1blN0YXR1c1xuICAgICAgICA9IG5ldyBzdGF0dXMuU3RhdHVzKGZ1bkVudlswXSwgZnVuRW52WzFdLCBmdW5FbnZbMl0sIFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIHRoaXMuZGVsdGEsIG5ld1NDKTtcbiAgICAvLyBwYXNzIHRoaXMgb2JqZWN0XG4gICAgdGhpcy5zZWxmLnByb3BhZ2F0ZShmdW5FbnZbMF0pO1xuXG4gICAgY29uc3QgbWluTGVuID0gTWF0aC5taW4odGhpcy5hcmdzLmxlbmd0aCwgZi5wYXJhbU5hbWVzLmxlbmd0aCk7XG4gICAgZm9yIChsZXQgaSA9IDA7IGkgPCBtaW5MZW47IGkrKykge1xuICAgICAgICB0aGlzLmFyZ3NbaV0ucHJvcGFnYXRlKG5ld1NDLmdldEFWYWxPZihmLnBhcmFtTmFtZXNbaV0pKTtcbiAgICB9XG5cbiAgICAvLyBmb3IgYXJndW1lbnRzIG9iamVjdFxuICAgIGlmIChmLm9yaWdpbk5vZGUuYm9keVsnQGJsb2NrJ10udXNlQXJndW1lbnRzT2JqZWN0KSB7XG4gICAgICAgIGNvbnN0IGFyZ09iaiA9IGYuZ2V0QXJndW1lbnRzT2JqZWN0KHRoaXMuZGVsdGEpO1xuICAgICAgICBuZXdTQy5nZXRBVmFsT2YoJ2FyZ3VtZW50cycpLmFkZFR5cGUoYXJnT2JqKTtcbiAgICAgICAgZm9yIChsZXQgaSA9IDA7IGkgPCB0aGlzLmFyZ3MubGVuZ3RoOyBpKyspIHtcbiAgICAgICAgICAgIHRoaXMuYXJnc1tpXS5wcm9wYWdhdGUoYXJnT2JqLmdldFByb3AoaSArICcnKSk7XG4gICAgICAgICAgICB0aGlzLmFyZ3NbaV0ucHJvcGFnYXRlKGFyZ09iai5nZXRQcm9wKG51bGwpKTtcbiAgICAgICAgfVxuICAgICAgICBhcmdPYmouZ2V0UHJvcCgnY2FsbGVlJykuYWRkVHlwZShmKTtcbiAgICAgICAgYXJnT2JqLmdldFByb3AoJ2xlbmd0aCcpLmFkZFR5cGUodHlwZXMuUHJpbU51bWJlcik7XG4gICAgfVxuXG4gICAgLy8gY29uc3RyYWludCBnZW5lcmF0aW9uIGZvciB0aGUgZnVuY3Rpb24gYm9keVxuICAgIGNHZW4uYWRkQ29uc3RyYWludHMoZi5vcmlnaW5Ob2RlLmJvZHksIGZ1blN0YXR1cyk7XG5cbiAgICAvLyBnZXQgcmV0dXJuIFxuICAgIGZ1bkVudlsxXS5wcm9wYWdhdGUodGhpcy5yZXQpO1xuICAgIC8vIGdldCBleGNlcHRpb25cbiAgICBmdW5FbnZbMl0ucHJvcGFnYXRlKHRoaXMuZXhjKTtcbn07XG5cbmZ1bmN0aW9uIElzQ3RvcihhcmdzLCByZXQsIGV4YywgZGVsdGEpIHtcbiAgICB0aGlzLmFyZ3MgPSBhcmdzO1xuICAgIHRoaXMucmV0ID0gcmV0O1xuICAgIHRoaXMuZXhjID0gZXhjO1xuICAgIHRoaXMuZGVsdGEgPSBkZWx0YTtcbn1cbklzQ3Rvci5wcm90b3R5cGUgPSBPYmplY3QuY3JlYXRlKENTVFIucHJvdG90eXBlKTtcbklzQ3Rvci5wcm90b3R5cGUuYWRkVHlwZSA9IGZ1bmN0aW9uIChmKSB7XG4gICAgaWYgKCEoZiBpbnN0YW5jZW9mICh0eXBlcy5GblR5cGUpKSkgcmV0dXJuO1xuICAgIGNvbnN0IGZ1bkVudiA9IGYuZ2V0RnVuRW52KHRoaXMuZGVsdGEpO1xuICAgIGNvbnN0IG5ld1NDID0gZi5vcmlnaW5Ob2RlLmJvZHlbJ0BibG9jayddLmdldFNjb3BlSW5zdGFuY2UoZi5zYywgdGhpcy5kZWx0YSk7XG4gICAgY29uc3QgZnVuU3RhdHVzXG4gICAgICAgID0gbmV3IHN0YXR1cy5TdGF0dXMoZnVuRW52WzBdLCBuZXcgSWZPYmpUeXBlKGZ1bkVudlsxXSksIGZ1bkVudlsyXSxcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICB0aGlzLmRlbHRhLCBuZXdTQyk7XG4gICAgLy8gcGFzcyB0aGlzIG9iamVjdFxuICAgIGNvbnN0IG5ld09iaiA9IGYuZ2V0SW5zdGFuY2UoKTtcbiAgICBmdW5FbnZbMF0uYWRkVHlwZShuZXdPYmopO1xuXG4gICAgY29uc3QgbWluTGVuID0gTWF0aC5taW4odGhpcy5hcmdzLmxlbmd0aCwgZi5wYXJhbU5hbWVzLmxlbmd0aCk7XG4gICAgZm9yIChsZXQgaSA9IDA7IGkgPCBtaW5MZW47IGkrKykge1xuICAgICAgICB0aGlzLmFyZ3NbaV0ucHJvcGFnYXRlKG5ld1NDLmdldEFWYWxPZihmLnBhcmFtTmFtZXNbaV0pKTtcbiAgICB9XG5cbiAgICAvLyBmb3IgYXJndW1lbnRzIG9iamVjdFxuICAgIGlmIChmLm9yaWdpbk5vZGUuYm9keVsnQGJsb2NrJ10udXNlQXJndW1lbnRzT2JqZWN0KSB7XG4gICAgICAgIGNvbnN0IGFyZ09iaiA9IGYuZ2V0QXJndW1lbnRzT2JqZWN0KHRoaXMuZGVsdGEpO1xuICAgICAgICBuZXdTQy5nZXRBVmFsT2YoJ2FyZ3VtZW50cycpLmFkZFR5cGUoYXJnT2JqKTtcbiAgICAgICAgZm9yIChsZXQgaSA9IDA7IGkgPCB0aGlzLmFyZ3MubGVuZ3RoOyBpKyspIHtcbiAgICAgICAgICAgIHRoaXMuYXJnc1tpXS5wcm9wYWdhdGUoYXJnT2JqLmdldFByb3AoaSArICcnKSk7XG4gICAgICAgICAgICB0aGlzLmFyZ3NbaV0ucHJvcGFnYXRlKGFyZ09iai5nZXRQcm9wKG51bGwpKTtcbiAgICAgICAgfVxuICAgICAgICBhcmdPYmouZ2V0UHJvcCgnY2FsbGVlJykuYWRkVHlwZShmKTtcbiAgICAgICAgYXJnT2JqLmdldFByb3AoJ2xlbmd0aCcpLmFkZFR5cGUodHlwZXMuUHJpbU51bWJlcik7XG4gICAgfVxuXG4gICAgLy8gY29uc3RyYWludCBnZW5lcmF0aW9uIGZvciB0aGUgZnVuY3Rpb24gYm9keVxuICAgIGNHZW4uYWRkQ29uc3RyYWludHMoZi5vcmlnaW5Ob2RlLmJvZHksIGZ1blN0YXR1cyk7XG5cbiAgICAvLyBieSBleHBsaWNpdCByZXR1cm4sIG9ubHkgT2JqVHlwZSBhcmUgcHJvcGFnYXRlZFxuICAgIGZ1bkVudlsxXS5wcm9wYWdhdGUodGhpcy5yZXQpO1xuICAgIC8vIHJldHVybiBuZXcgb2JqZWN0XG4gICAgdGhpcy5yZXQuYWRkVHlwZShuZXdPYmopO1xuICAgIC8vIGdldCBleGNlcHRpb25cbiAgICBmdW5FbnZbMl0ucHJvcGFnYXRlKHRoaXMuZXhjKTtcbn07XG5cbi8vIGlnbm9yZSBub24gb2JqZWN0IHR5cGVzXG5mdW5jdGlvbiBJZk9ialR5cGUoYXZhbCkge1xuICAgIHRoaXMuYXZhbCA9IGF2YWw7XG59XG5JZk9ialR5cGUucHJvdG90eXBlID0gT2JqZWN0LmNyZWF0ZShDU1RSLnByb3RvdHlwZSk7XG5JZk9ialR5cGUucHJvdG90eXBlLmFkZFR5cGUgPSBmdW5jdGlvbiAodHlwZSkge1xuICAgIGlmICghKHR5cGUgaW5zdGFuY2VvZiB0eXBlcy5PYmpUeXBlKSkgcmV0dXJuO1xuICAgIHRoaXMuYXZhbC5hZGRUeXBlKHR5cGUpO1xufTtcblxuZXhwb3J0cy5SZWFkUHJvcCA9IFJlYWRQcm9wO1xuZXhwb3J0cy5Xcml0ZVByb3AgPSBXcml0ZVByb3A7XG5leHBvcnRzLklzQWRkZWQgPSBJc0FkZGVkO1xuZXhwb3J0cy5Jc0NhbGxlZSA9IElzQ2FsbGVlO1xuZXhwb3J0cy5Jc0N0b3IgPSBJc0N0b3I7XG4iLCIvLyBDb250ZXh0IGZvciBrLUNGQSBhbmFseXNpc1xuLy9cbi8vIEFzc3VtZSBhIGNvbnRleHQgaXMgYW4gYXJyYXkgb2YgbnVtYmVycy5cbi8vIEEgbnVtYmVyIGluIHN1Y2ggbGlzdCBkZW5vdGVzIGEgY2FsbCBzaXRlLCB0aGF0IGlzIEBsYWJlbCBvZiBhIENhbGxFeHByZXNzaW9uLlxuLy8gV2Uga2VlcCB0aGUgbW9zdCByZWNlbnQgJ2snIGNhbGxzaXRlcy5cbi8vIEVxdWFsaXR5IG9uIGNvbnRleHRzIHNob3VsZCBsb29rIGludG8gdGhlIG51bWJlcnMuXG5cbnZhciBjYWxsU2l0ZUNvbnRleHRQYXJhbWV0ZXIgPSB7XG4gICAgLy8gbWF4aW11bSBsZW5ndGggb2YgY29udGV4dFxuICAgIG1heERlcHRoSzogMCxcbiAgICAvLyBmdW5jdGlvbiBsaXN0IGZvciBzZW5zaXRpdmUgYW5hbHlzaXNcbiAgICBzZW5zRnVuY3M6IHt9XG59O1xuXG5mdW5jdGlvbiBDYWxsU2l0ZUNvbnRleHQoY3NMaXN0KSB7XG4gICAgaWYgKGNzTGlzdCkgdGhpcy5jc0xpc3QgPSBjc0xpc3Q7XG4gICAgZWxzZSB0aGlzLmNzTGlzdCA9IFtdO1xufVxuXG5DYWxsU2l0ZUNvbnRleHQucHJvdG90eXBlLmVxdWFscyA9IGZ1bmN0aW9uIChvdGhlcikge1xuICAgIGlmICh0aGlzLmNzTGlzdC5sZW5ndGggIT0gb3RoZXIuY3NMaXN0Lmxlbmd0aCkgcmV0dXJuIGZhbHNlO1xuICAgIGZvciAodmFyIGkgPSAwOyBpIDwgdGhpcy5jc0xpc3QubGVuZ3RoOyBpKyspIHtcbiAgICAgICAgaWYgKHRoaXMuY3NMaXN0W2ldICE9PSBvdGhlci5jc0xpc3RbaV0pIHJldHVybiBmYWxzZTtcbiAgICB9XG4gICAgcmV0dXJuIHRydWU7XG59O1xuXG5DYWxsU2l0ZUNvbnRleHQucHJvdG90eXBlLmFwcGVuZE9uZSA9IGZ1bmN0aW9uIChjYWxsU2l0ZSkge1xuICAgIC8vIHVzZSBjb25jYXQgdG8gY3JlYXRlIGEgbmV3IGFycmF5XG4gICAgLy8gb2xkZXN0IG9uZSBjb21lcyBmaXJzdFxuICAgIHZhciBhcHBlbmRlZCA9IHRoaXMuY3NMaXN0LmNvbmNhdChjYWxsU2l0ZSk7XG4gICAgaWYgKGFwcGVuZGVkLmxlbmd0aCA+IGNhbGxTaXRlQ29udGV4dFBhcmFtZXRlci5tYXhEZXB0aEspIHtcbiAgICAgICAgYXBwZW5kZWQuc2hpZnQoKTtcbiAgICB9XG4gICAgcmV0dXJuIG5ldyBDYWxsU2l0ZUNvbnRleHQoYXBwZW5kZWQpO1xufTtcblxuQ2FsbFNpdGVDb250ZXh0LnByb3RvdHlwZS50b1N0cmluZyA9IGZ1bmN0aW9uICgpIHtcbiAgICByZXR1cm4gdGhpcy5jc0xpc3QudG9TdHJpbmcoKTtcbn07XG5cbmV4cG9ydHMuY2FsbFNpdGVDb250ZXh0UGFyYW1ldGVyID0gY2FsbFNpdGVDb250ZXh0UGFyYW1ldGVyO1xuZXhwb3J0cy5DYWxsU2l0ZUNvbnRleHQgPSBDYWxsU2l0ZUNvbnRleHQ7IiwiLy8gU3RhdHVzOlxuLy8geyBzZWxmICA6IEFWYWwsXG4vLyAgIHJldCAgIDogQVZhbCxcbi8vICAgZXhjICAgOiBBVmFsLFxuLy8gICBkZWx0YSA6IENvbnRleHQsXG4vLyAgIHNjICAgIDogU2NvcGVDaGFpbiB9XG5cbmZ1bmN0aW9uIFN0YXR1cyhzZWxmLCByZXQsIGV4YywgZGVsdGEsIHNjKSB7XG4gICAgdGhpcy5zZWxmID0gc2VsZjtcbiAgICB0aGlzLnJldCA9IHJldDtcbiAgICB0aGlzLmV4YyA9IGV4YztcbiAgICB0aGlzLmRlbHRhID0gZGVsdGE7XG4gICAgdGhpcy5zYyA9IHNjO1xufVxuXG5TdGF0dXMucHJvdG90eXBlLmVxdWFscyA9IGZ1bmN0aW9uIChvdGhlcikge1xuICAgIHJldHVybiB0aGlzLnNlbGYgPT09IG90aGVyLnNlbGYgJiZcbiAgICAgICAgdGhpcy5yZXQgPT09IG90aGVyLnJldCAmJlxuICAgICAgICB0aGlzLmV4YyA9PT0gb3RoZXIuZXhjICYmXG4gICAgICAgIHRoaXMuZGVsdGEuZXF1YWxzKG90aGVyLmRlbHRhKSAmJlxuICAgICAgICB0aGlzLnNjID09PSBvdGhlci5zYztcbn07XG5cbmV4cG9ydHMuU3RhdHVzID0gU3RhdHVzOyIsIid1c2Ugc3RyaWN0JztcblxuLy8gZm9yIERFQlVHXG52YXIgY291bnQgPSAwO1xuLyoqXG4gKiB0aGUgYWJzdHJhY3QgdmFsdWUgZm9yIGEgY29uY3JldGUgdmFsdWVcbiAqIHdoaWNoIGlzIGEgc2V0IG9mIHR5cGVzLlxuICogQGNvbnN0cnVjdG9yXG4gKiBAcGFyYW0ge1R5cGV9IHR5cGUgLSBnaXZlIGEgdHlwZSB0byBtYWtlIEFWYWwgd2l0aCBhIHNpbmdsZSB0eXBlXG4gKi9cbmZ1bmN0aW9uIEFWYWwodHlwZSkge1xuICAgIC8vIHR5cGU6IGNvbnRhaW5lZCB0eXBlc1xuICAgIC8vIFdlIGFzc3VtZSB0eXBlcyBhcmUgZGlzdGluZ3Vpc2hhYmxlIGJ5ICc9PT0nXG4gICAgaWYgKHR5cGUpIHRoaXMudHlwZXMgPSBuZXcgU2V0KFt0eXBlXSk7XG4gICAgZWxzZSB0aGlzLnR5cGVzID0gbmV3IFNldCgpO1xuICAgIC8vIGZvcndhcmRzOiBwcm9wYWdhdGlvbiB0YXJnZXRzXG4gICAgLy8gV2UgYXNzdW1lIHRhcmdldHMgYXJlIGRpc3Rpbmd1aXNoYWJsZSBieSAnZXF1YWxzJyBtZXRob2RcbiAgICB0aGlzLmZvcndhcmRzID0gbmV3IFNldCgpO1xuICAgIC8vIGZvciBERUJVR1xuICAgIHRoaXMuX2lkID0gY291bnQrKztcbn1cbi8qKiBDaGVjayB3aGV0aGVyIGl0IGhhcyBhbnkgdHlwZVxuICogQHJldHVybnMge2Jvb2xlYW59XG4gKi9cbkFWYWwucHJvdG90eXBlLmlzRW1wdHkgPSBmdW5jdGlvbiAoKSB7XG4gICAgcmV0dXJuIHRoaXMudHlwZXMuc2l6ZSA9PT0gMDtcbn07XG5cbi8qKlxuICogQHJldHVybnMge1tUeXBlXX1cbiAqL1xuQVZhbC5wcm90b3R5cGUuZ2V0VHlwZXMgPSBmdW5jdGlvbiAoKSB7XG4gICAgcmV0dXJuIHRoaXMudHlwZXM7XG59O1xuXG4vKipcbiAqIEByZXR1cm5zIHtib29sZWFufVxuICovXG5BVmFsLnByb3RvdHlwZS5oYXNUeXBlID0gZnVuY3Rpb24gKHR5cGUpIHtcbiAgICByZXR1cm4gdGhpcy50eXBlcy5oYXModHlwZSk7XG59O1xuXG4vKipcbiAqIEFkZCBhIHR5cGUuXG4gKiBAcGFyYW0ge1R5cGV9IHR5cGVcbiAqL1xuQVZhbC5wcm90b3R5cGUuYWRkVHlwZSA9IGZ1bmN0aW9uICh0eXBlKSB7XG4gICAgaWYgKHRoaXMudHlwZXMuaGFzKHR5cGUpKSByZXR1cm47XG4gICAgLy8gZ2l2ZW4gdHlwZSBpcyBuZXdcbiAgICB0aGlzLnR5cGVzLmFkZCh0eXBlKTtcbiAgICAvLyBzZW5kIHRvIHByb3BhZ2F0aW9uIHRhcmdhdHNcbiAgICB0aGlzLmZvcndhcmRzLmZvckVhY2goZnVuY3Rpb24gKGZ3ZCkge1xuICAgICAgICBmd2QuYWRkVHlwZSh0eXBlKTtcbiAgICB9KTtcbn07XG4vKipcbiAqIEBwYXJhbSB7QVZhbH0gdGFyZ2V0XG4gKi9cbkFWYWwucHJvdG90eXBlLnByb3BhZ2F0ZSA9IGZ1bmN0aW9uICh0YXJnZXQpIHtcbiAgICBpZiAoIXRoaXMuYWRkRm9yd2FyZCh0YXJnZXQpKSByZXR1cm47XG4gICAgLy8gdGFyZ2V0IGlzIG5ld2x5IGFkZGVkXG4gICAgLy8gc2VuZCB0eXBlcyB0byB0aGUgbmV3IHRhcmdldFxuICAgIHRoaXMudHlwZXMuZm9yRWFjaChmdW5jdGlvbiAodHlwZSkge1xuICAgICAgICB0YXJnZXQuYWRkVHlwZSh0eXBlKTtcbiAgICB9KTtcbn07XG5cbkFWYWwucHJvdG90eXBlLmFkZEZvcndhcmQgPSBmdW5jdGlvbiAoZndkKSB7XG4gICAgZm9yIChsZXQgb2xkRndkIG9mIHRoaXMuZm9yd2FyZHMpIHtcbiAgICAgICAgaWYgKGZ3ZC5lcXVhbHMob2xkRndkKSkgcmV0dXJuIGZhbHNlO1xuICAgIH1cbiAgICB0aGlzLmZvcndhcmRzLmFkZChmd2QpO1xuICAgIHJldHVybiB0cnVlO1xufTtcblxuQVZhbC5wcm90b3R5cGUuZXF1YWxzID0gZnVuY3Rpb24gKG90aGVyKSB7XG4gICAgLy8gc2ltcGxlIHJlZmVyZW5jZSBjb21wYXJpc29uXG4gICAgcmV0dXJuIHRoaXMgPT09IG90aGVyO1xufTtcblxuLyoqXG4gKiBUT0RPOiBjaGVjayB3aGV0aGVyIHdlIHJlYWxseSBuZWVkIHRoaXMgbWV0aG9kLlxuICogQHBhcmFtIHtzdHJpbmd9IHByb3BcbiAqIEByZXR1cm5zIHtBVmFsfVxuICovXG5BVmFsLnByb3RvdHlwZS5nZXRQcm9wID0gZnVuY3Rpb24gKHByb3ApIHtcbiAgICBpZiAocHJvcCA9PT0gJ+KclicpIHtcbiAgICAgICAgLy8g4pyWIGlzIHRoZSBib2d1cyBwcm9wZXJ0eSBuYW1lIGFkZGVkIGZvciBlcnJvciByZWNvdmVyeS5cbiAgICAgICAgcmV0dXJuIEFWYWxOdWxsO1xuICAgIH1cbiAgICBpZiAodGhpcy5wcm9wcy5oYXMocHJvcCkpIHtcbiAgICAgICAgcmV0dXJuIHRoaXMucHJvcHMuZ2V0KHByb3ApO1xuICAgIH0gZWxzZSB7XG4gICAgICAgIHJldHVybiBBVmFsTnVsbDtcbiAgICB9XG59O1xuXG4vKipcbiAqIHRoZSBzdXBlciBjbGFzcyBvZiBhbGwgdHlwZXNcbiAqIGVhY2ggdHlwZSBzaG91bGQgYmUgZGlzdGluZ3Vpc2hhYmxlIGJ5ICc9PT0nIG9wZXJhdGlvbi5cbiAqIEBjb25zdHJ1Y3RvclxuICovXG5mdW5jdGlvbiBUeXBlKCkge31cblR5cGUucHJvdG90eXBlID0gT2JqZWN0LmNyZWF0ZShudWxsKTtcblxuLyoqXG4gKiAxLiBvYmplY3QgdHlwZXNcbiAqIEBwYXJhbSB7QVZhbH0gcHJvdG8gLSBBVmFsIG9mIGNvbnN0cnVjdG9yJ3MgcHJvdG90eXBlXG4gKiBAcGFyYW0ge3N0cmluZ30gbmFtZSAtIGd1ZXNzZWQgbmFtZVxuICovXG5mdW5jdGlvbiBPYmpUeXBlKHByb3RvLCBuYW1lKSB7XG4gICAgdGhpcy5uYW1lID0gbmFtZTtcbiAgICB0aGlzLnByb3BzID0gbmV3IE1hcCgpO1xuXG4gICAgLy8gc2hhcmUgcHJvdG8gd2l0aCBfX3Byb3RvX19cbiAgICB0aGlzLnNldFByb3AoJ19fcHJvdG9fXycsIHByb3RvKTtcbn1cbk9ialR5cGUucHJvdG90eXBlID0gT2JqZWN0LmNyZWF0ZShUeXBlLnByb3RvdHlwZSk7XG4vKipcbiAqIEBwYXJhbSB7c3RyaW5nfG51bGx9IHByb3AgLSBudWxsIGZvciBjb21wdXRlZCBwcm9wc1xuICogQHBhcmFtIHtib29sZWFufSByZWFkT25seSAtIGlmIGZhbHNlLCBjcmVhdGUgQVZhbCBmb3IgcHJvcCBpZiBuZWNlc3NhcnlcbiAqIEByZXR1cm5zIHtBVmFsfSBBVmFsIG9mIHRoZSBwcm9wZXJ0eVxuICovXG5PYmpUeXBlLnByb3RvdHlwZS5nZXRQcm9wID0gZnVuY3Rpb24gKHByb3AsIHJlYWRPbmx5KSB7XG4gICAgaWYgKHByb3AgPT09ICfinJYnKSB7XG4gICAgICAgIC8vIOKcliBpcyB0aGUgYm9ndXMgcHJvcGVydHkgbmFtZSBhZGRlZCBkdXJpbmcgcGFyc2luZyBlcnJvciByZWNvdmVyeS5cbiAgICAgICAgcmV0dXJuIEFWYWxOdWxsO1xuICAgIH1cbiAgICBpZiAodGhpcy5wcm9wcy5oYXMocHJvcCkpIHtcbiAgICAgICAgcmV0dXJuIHRoaXMucHJvcHMuZ2V0KHByb3ApO1xuICAgIH0gZWxzZSBpZiAocmVhZE9ubHkpIHtcbiAgICAgICAgcmV0dXJuIG51bGw7XG4gICAgfSBlbHNlIHtcbiAgICAgICAgdmFyIG5ld1Byb3BBVmFsID0gbmV3IEFWYWw7XG4gICAgICAgIHRoaXMucHJvcHMuc2V0KHByb3AsIG5ld1Byb3BBVmFsKTtcbiAgICAgICAgcmV0dXJuIG5ld1Byb3BBVmFsO1xuICAgIH1cbn07XG4vKipcbiAqIFdlIHVzZSB0aGlzIGZ1bmN0aW9uIHRvIHNoYXJlIC5wcm90b3R5cGUgd2l0aCBpbnN0YW5jZXMgX19wcm90b19fXG4gKiBJdCBpcyBwb3NzaWJsZSB0byB1c2UgdGhpcyBmdW5jdGlvbiB0byBtZXJnZSBBVmFscyB0byBvcHRpbWl6ZSB0aGUgYW5hbHl6ZXIuXG4gKiBAcGFyYW0ge3N0cmluZ3xudWxsfSBwcm9wIC0gbnVsbCBmb3IgY29tcHV0ZWQgcHJvcHNcbiAqIEBwYXJhbSB7QVZhbH0gYXZhbFxuICovXG5PYmpUeXBlLnByb3RvdHlwZS5zZXRQcm9wID0gZnVuY3Rpb24gKHByb3AsIGF2YWwpIHtcbiAgICBpZiAocHJvcCA9PT0gJ+KclicpIHtcbiAgICAgICAgLy8g4pyWIGlzIHRoZSBib2d1cyBwcm9wZXJ0eSBuYW1lIGFkZGVkIGR1cmluZyBwYXJzaW5nIGVycm9yIHJlY292ZXJ5LlxuICAgICAgICByZXR1cm47XG4gICAgfVxuICAgIHRoaXMucHJvcHMuc2V0KHByb3AsIGF2YWwpO1xufTtcbi8qKlxuICogVE9ETzogQ2hlY2sgdGhpcyBmdW5jdGlvbidzIG5lY2Vzc2l0eVxuICogQHBhcmFtIHtzdHJpbmd9IHByb3BcbiAqIEByZXR1cm5zIHtib29sZWFufVxuICovXG5PYmpUeXBlLnByb3RvdHlwZS5oYXNQcm9wID0gZnVuY3Rpb24gKHByb3ApIHtcbiAgICBpZiAocHJvcCA9PT0gJ+KclicpIHJldHVybiBmYWxzZTtcbiAgICByZXR1cm4gdGhpcy5wcm9wcy5oYXMocHJvcCk7XG59O1xuLyoqXG4gKiBUT0RPOiBDaGVjayB0aGlzIGZ1bmN0aW9uJ3MgbmVjZXNzaXR5XG4gKiBAcGFyYW0ge1R5cGV9IHR5cGVcbiAqIEBwYXJhbSB7c3RyaW5nfSBwcm9wXG4gKi9cbk9ialR5cGUucHJvdG90eXBlLmFkZFR5cGVUb1Byb3AgPSBmdW5jdGlvbiAodHlwZSwgcHJvcCkge1xuICAgIGlmIChwcm9wID09PSAn4pyWJykgcmV0dXJuO1xuICAgIGlmICghdGhpcy5wcm9wcy5oYXMocHJvcCkpIHtcbiAgICAgICAgdGhpcy5wcm9wcy5zZXQocHJvcCwgbmV3IEFWYWwpO1xuICAgIH1cbiAgICBpZiAodGhpcy5wcm9wcy5nZXQocHJvcCkuaGFzVHlwZSh0eXBlKSkgcmV0dXJuO1xuICAgIHRoaXMucHJvcHMuZ2V0KHByb3ApLmFkZFR5cGUodHlwZSk7XG59O1xuLyoqXG4gKiBUT0RPOiBDaGVjayB0aGlzIGZ1bmN0aW9uJ3MgbmVjZXNzaXR5XG4gKiBAcGFyYW0ge0FWYWx9IGF2YWxcbiAqIEBwYXJhbSB7c3RyaW5nfSBwcm9wXG4gKi9cbk9ialR5cGUucHJvdG90eXBlLmpvaW5BVmFsVG9Qcm9wID0gZnVuY3Rpb24gKGF2YWwsIHByb3ApIHtcbiAgICB2YXIgc2VsZiA9IHRoaXM7XG4gICAgYXZhbC5nZXRUeXBlcygpLmZvckVhY2goZnVuY3Rpb24gKHR5cGUpIHtcbiAgICAgICAgc2VsZi5hZGRUeXBlVG9Qcm9wKHR5cGUsIHByb3ApO1xuICAgIH0pO1xufTtcblxuLy8gbWFrZSBhbiBPYmogZnJvbSB0aGUgZ2xvYmFsIHNjb3BlXG5mdW5jdGlvbiBta09iakZyb21HbG9iYWxTY29wZShnU2NvcGUpIHtcbiAgICB2YXIgZ09iaiA9IG5ldyBPYmpUeXBlKEFWYWxOdWxsLCAnKmdsb2JhbCBzY29wZSonKTtcbiAgICBnT2JqLnByb3BzID0gZ1Njb3BlLnZhck1hcDtcbiAgICAvLyBPdmVycmlkZSBnZXRQcm9wIG1ldGhvZCBmb3IgZ2xvYmFsIG9iamVjdFxuICAgIC8vIFdlIGlnbm9yZSAncmVhZE9ubHknIHBhcmFtZXRlciB0byBhbHdheXMgcmV0dXJuIGl0cyBvd24gcHJvcCBBVmFsIFxuICAgIGdPYmouZ2V0UHJvcCA9IGZ1bmN0aW9uIChwcm9wKSB7XG4gICAgICAgIHJldHVybiBPYmpUeXBlLnByb3RvdHlwZS5nZXRQcm9wLmNhbGwodGhpcywgcHJvcCk7XG4gICAgfTtcbiAgICByZXR1cm4gZ09iajtcbn1cblxuLyoqXG4gKiAyLiBwcmltaXRpdmUgdHlwZXNcbiAqIEBjb25zdHJ1Y3RvclxuICogQHBhcmFtIHtzdHJpbmd9IG5hbWVcbiAqL1xuZnVuY3Rpb24gUHJpbVR5cGUobmFtZSkge1xuICAgIHRoaXMubmFtZSA9IG5hbWU7XG59XG5QcmltVHlwZS5wcm90b3R5cGUgPSBPYmplY3QuY3JlYXRlKFR5cGUucHJvdG90eXBlKTtcblxuLyoqXG4gKiAzLiBmdW5jdGlvbiB0eXBlc1xuICogdGhlIG5hbWUgaXMgdXNlZCBmb3IgdGhlIHR5cGUgb2YgdGhlIGluc3RhbmNlcyBmcm9tIHRoZSBmdW5jdGlvblxuICogQGNvbnN0cnVjdG9yXG4gKiBAcGFyYW0ge0FWYWx9IGZuX3Byb3RvIC0gQVZhbCBmb3IgY29uc3RydWN0b3IncyAucHJvdG90eXBlXG4gKiBAcGFyYW0ge3N0cmluZ30gbmFtZSAtIGd1ZXNzZWQgbmFtZVxuICogQHBhcmFtIHtbc3RyaW5nXX0gYXJnTmFtZXMgLSBsaXN0IG9mIHBhcmFtZXRlciBuYW1lc1xuICogQHBhcmFtIHtTY29wZX0gc2MgLSBmdW5jdGlvbnMgc2NvcGUgY2hhaW4sIG9yIGNsb3N1cmVcbiAqIEBwYXJhbSB7bm9kZX0gb3JpZ2luTm9kZSAtIEFTVCBub2RlIGZvciB0aGUgZnVuY3Rpb25cbiAqIEBwYXJhbSB7VHlwZX0gYXJnUHJvdG8gLSBwcm90b3R5cGUgZm9yIGFyZ3VtZW50cyBvYmplY3RcbiAqL1xuZnVuY3Rpb24gRm5UeXBlKGZuX3Byb3RvLCBuYW1lLCBhcmdOYW1lcywgc2MsIG9yaWdpbk5vZGUsIGFyZ1Byb3RvKSB7XG4gICAgT2JqVHlwZS5jYWxsKHRoaXMsIGZuX3Byb3RvLCBuYW1lKTtcbiAgICB0aGlzLnBhcmFtTmFtZXMgPSBhcmdOYW1lcztcbiAgICB0aGlzLnNjID0gc2M7XG4gICAgdGhpcy5vcmlnaW5Ob2RlID0gb3JpZ2luTm9kZTtcbiAgICB0aGlzLmFyZ1Byb3RvID0gYXJnUHJvdG87XG4gICAgLy8gZnVuRW52IDogQ2FsbENvbnRleHQgLT4gW3NlbGYsIHJldCwgZXhjXVxuICAgIHRoaXMuZnVuRW52ID0gbmV3IE1hcDtcbn1cbkZuVHlwZS5wcm90b3R5cGUgPSBPYmplY3QuY3JlYXRlKE9ialR5cGUucHJvdG90eXBlKTtcblxuLyoqXG4gKiBjb25zdHJ1Y3QgU3RhdHVzIGZvciBmdW5jdGlvblxuICogQHBhcmFtIHtDYWxsQ29udGV4dH0gZGVsdGEgLSBjYWxsIGNvbnRleHRcbiAqIEByZXR1cm5zIHtbQVZhbCwgQVZhbCwgQVZhbF19IC0gZm9yIHNlbGYsIHJldHVybiBhbmQgZXhjZXB0aW9uIEFWYWxzXG4gKi9cbkZuVHlwZS5wcm90b3R5cGUuZ2V0RnVuRW52ID0gZnVuY3Rpb24gKGRlbHRhKSB7XG4gICAgaWYgKHRoaXMuZnVuRW52LmhhcyhkZWx0YSkpIHtcbiAgICAgICAgcmV0dXJuIHRoaXMuZnVuRW52LmdldChkZWx0YSk7XG4gICAgfSBlbHNlIHtcbiAgICAgICAgdmFyIHRyaXBsZSA9IFtuZXcgQVZhbCwgbmV3IEFWYWwsIG5ldyBBVmFsXTtcbiAgICAgICAgdGhpcy5mdW5FbnYuc2V0KGRlbHRhLCB0cmlwbGUpO1xuICAgICAgICByZXR1cm4gdHJpcGxlO1xuICAgIH1cbn07XG5cbkZuVHlwZS5wcm90b3R5cGUuZ2V0QXJndW1lbnRzT2JqZWN0ID0gZnVuY3Rpb24gKGRlbHRhKSB7XG4gICAgdGhpcy5hcmdPYmpNYXAgPSB0aGlzLmFyZ09iak1hcCB8fCBuZXcgTWFwO1xuICAgIGlmICh0aGlzLmFyZ09iak1hcC5oYXMoZGVsdGEpKSB7XG4gICAgICAgIHJldHVybiB0aGlzLmFyZ09iak1hcC5nZXQoZGVsdGEpO1xuICAgIH0gZWxzZSB7XG4gICAgICAgIHZhciBhcmdPYmogPSBuZXcgT2JqVHlwZShuZXcgQVZhbCh0aGlzLmFyZ1Byb3RvKSwgJyphcmd1bWVudHMgb2JqZWN0KicpO1xuICAgICAgICB0aGlzLmFyZ09iak1hcC5zZXQoZGVsdGEsIGFyZ09iaik7XG4gICAgICAgIHJldHVybiBhcmdPYmo7XG4gICAgfVxufTtcblxuLyoqXG4gKiBnZXQgT2JqZWN0IG1hZGUgYnkgdGhlIGZ1bmN0aW9uXG4gKiBUT0RPOiB1c2UgYWRkaXRpb25hbCBpbmZvcm1hdGlvbiB0byBjcmVhdGUgbXVsdGlwbGUgaW5zdGFuY2VzXG4gKiBAcmV0dXJucyB7T2JqVHlwZX1cbiAqL1xuRm5UeXBlLnByb3RvdHlwZS5nZXRJbnN0YW5jZSA9IGZ1bmN0aW9uICgpIHtcbiAgICAvLyBvYmpJbnN0YW5jZSBpcyB0aGUgb2JqZWN0IG1hZGUgYnkgdGhlIGZ1bmN0aW9hbm5cbiAgICBpZiAodGhpcy5vYmpJbnN0YW5jZSkgcmV0dXJuIHRoaXMub2JqSW5zdGFuY2U7XG4gICAgLy8gd2UgdW5pZnkgY29uc3RydWN0b3IncyAucHJvdG90eXBlIGFuZCBpbnN0YW5jZSdzIF9fcHJvdG9fX1xuICAgIHRoaXMub2JqSW5zdGFuY2UgPSBuZXcgT2JqVHlwZSh0aGlzLmdldFByb3AoJ3Byb3RvdHlwZScpKTtcbiAgICByZXR1cm4gdGhpcy5vYmpJbnN0YW5jZTtcbn07XG5cbi8qKiBcbiAqIDQuIGFycmF5IHR5cGVzXG4gKiBAY29uc3RydWN0b3JcbiAqL1xuZnVuY3Rpb24gQXJyVHlwZShhcnJfcHJvdG8pIHtcbiAgICBPYmpUeXBlLmNhbGwodGhpcywgYXJyX3Byb3RvLCAnQXJyYXknKTtcbn1cbkFyclR5cGUucHJvdG90eXBlID0gT2JqZWN0LmNyZWF0ZShPYmpUeXBlLnByb3RvdHlwZSk7XG5cbi8vIE1ha2UgcHJpbWl0aXZlIHR5cGVzXG52YXIgUHJpbU51bWJlciA9IG5ldyBQcmltVHlwZSgnbnVtYmVyJyk7XG52YXIgUHJpbVN0cmluZyA9IG5ldyBQcmltVHlwZSgnc3RyaW5nJyk7XG52YXIgUHJpbUJvb2xlYW4gPSBuZXcgUHJpbVR5cGUoJ2Jvb2xlYW4nKTtcblxuLy8gQWJzTnVsbCByZXByZXNlbnRzIGFsbCBlbXB0eSBhYnN0cmFjdCB2YWx1ZXMuXG52YXIgQVZhbE51bGwgPSBuZXcgQVZhbCgpO1xuLy8gWW91IHNob3VsZCBub3QgYWRkIGFueSBwcm9wZXJ0aWVzIHRvIGl0LlxuQVZhbE51bGwucHJvcHMgPSBudWxsO1xuLy8gQWRkaW5nIHR5cGVzIGFyZSBpZ25vcmVkLlxuQVZhbE51bGwuYWRkVHlwZSA9IGZ1bmN0aW9uICgpIHt9O1xuXG5cbi8vIGV4cG9ydFxuZXhwb3J0cy5UeXBlID0gVHlwZTtcbmV4cG9ydHMuT2JqVHlwZSA9IE9ialR5cGU7XG5leHBvcnRzLkZuVHlwZSA9IEZuVHlwZTtcbmV4cG9ydHMuQXJyVHlwZSA9IEFyclR5cGU7XG5leHBvcnRzLlByaW1OdW1iZXIgPSBQcmltTnVtYmVyO1xuZXhwb3J0cy5QcmltU3RyaW5nID0gUHJpbVN0cmluZztcbmV4cG9ydHMuUHJpbUJvb2xlYW4gPSBQcmltQm9vbGVhbjtcbmV4cG9ydHMubWtPYmpGcm9tR2xvYmFsU2NvcGUgPSBta09iakZyb21HbG9iYWxTY29wZTtcblxuZXhwb3J0cy5BVmFsID0gQVZhbDtcbmV4cG9ydHMuQVZhbE51bGwgPSBBVmFsTnVsbDsiLCIvLyBpbXBvcnQgbmVjZXNzYXJ5IGxpYnJhcmllc1xudmFyIGFjb3JuID0gcmVxdWlyZSgnYWNvcm4vZGlzdC9hY29ybicpO1xudmFyIGFjb3JuX2xvb3NlID0gcmVxdWlyZSgnYWNvcm4vZGlzdC9hY29ybl9sb29zZScpO1xudmFyIGF1eCA9IHJlcXVpcmUoJy4vYXV4Jyk7XG52YXIgdHlwZXMgPSByZXF1aXJlKCcuL2RvbWFpbnMvdHlwZXMnKTtcbnZhciBjb250ZXh0ID0gcmVxdWlyZSgnLi9kb21haW5zL2NvbnRleHQnKTtcbnZhciBzdGF0dXMgPSByZXF1aXJlKCcuL2RvbWFpbnMvc3RhdHVzJyk7XG52YXIgdXRpbCA9IHJlcXVpcmUoJ3V0aWwnKTtcbnZhciB2YXJCbG9jayA9IHJlcXVpcmUoJy4vdmFyQmxvY2snKTtcbnZhciBjR2VuID0gcmVxdWlyZSgnLi9jb25zdHJhaW50L2NHZW4nKTtcbnZhciB2YXJSZWZzID0gcmVxdWlyZSgnLi92YXJyZWZzJyk7XG5cbmZ1bmN0aW9uIGFuYWx5emUoaW5wdXQsIHJldEFsbCkge1xuICAgIC8vIHRoZSBTY29wZSBvYmplY3QgZm9yIGdsb2JhbCBzY29wZVxuICAgIC8vIHNjb3BlLlNjb3BlLmdsb2JhbFNjb3BlID0gbmV3IHNjb3BlLlNjb3BlKG51bGwpO1xuXG4gICAgLy8gcGFyc2luZyBpbnB1dCBwcm9ncmFtXG4gICAgdmFyIGFzdDtcbiAgICB0cnkge1xuICAgICAgICBhc3QgPSBhY29ybi5wYXJzZShpbnB1dCk7XG4gICAgfSBjYXRjaCAoZSkge1xuICAgICAgICBhc3QgPSBhY29ybl9sb29zZS5wYXJzZV9kYW1taXQoaW5wdXQpO1xuICAgIH1cblxuICAgIHZhciBub2RlQXJyYXlJbmRleGVkQnlMaXN0ID0gYXV4LmdldE5vZGVMaXN0KGFzdCk7XG5cbiAgICAvLyBTaG93IEFTVCBiZWZvcmUgc2NvcGUgcmVzb2x1dGlvblxuICAgIC8vIGF1eC5zaG93VW5mb2xkZWQoYXN0KTtcblxuICAgIHZhckJsb2NrLmFubm90YXRlQmxvY2tJbmZvKGFzdCk7XG4gICAgdmFyIGdCbG9jayA9IGFzdFsnQGJsb2NrJ107XG4gICAgdmFyIGluaXRpYWxDb250ZXh0ID0gbmV3IGNvbnRleHQuQ2FsbFNpdGVDb250ZXh0O1xuICAgIHZhciBnU2NvcGUgPSBnQmxvY2suZ2V0U2NvcGVJbnN0YW5jZShudWxsLCBpbml0aWFsQ29udGV4dCk7XG4gICAgdmFyIGdPYmplY3QgPSB0eXBlcy5ta09iakZyb21HbG9iYWxTY29wZShnU2NvcGUpO1xuICAgIHZhciBpbml0U3RhdHVzID0gbmV3IHN0YXR1cy5TdGF0dXMoXG4gICAgICAgIGdPYmplY3QsXG4gICAgICAgIHR5cGVzLkFWYWxOdWxsLFxuICAgICAgICB0eXBlcy5BVmFsTnVsbCxcbiAgICAgICAgaW5pdGlhbENvbnRleHQsXG4gICAgICAgIGdTY29wZSk7XG4gICAgLy8gdGhlIHByb3RvdHlwZSBvYmplY3Qgb2YgT2JqZWN0XG4gICAgdmFyIE9ialByb3RvID0gbmV3IHR5cGVzLk9ialR5cGUobnVsbCwgJ09iamVjdC5wcm90b3R5cGUnKTtcbiAgICB2YXIgcnRDWCA9IHtcbiAgICAgICAgZ2xvYmFsT2JqZWN0OiBnT2JqZWN0LFxuICAgICAgICAvLyB0ZW1wb3JhbFxuICAgICAgICBwcm90b3M6IHtcbiAgICAgICAgICAgIE9iamVjdDogT2JqUHJvdG8sXG4gICAgICAgICAgICBGdW5jdGlvbjogbmV3IHR5cGVzLk9ialR5cGUobmV3IHR5cGVzLkFWYWwoT2JqUHJvdG8pLCAnRnVuY3Rpb24ucHJvdG90eXBlJyksXG4gICAgICAgICAgICBBcnJheTogbmV3IHR5cGVzLk9ialR5cGUobmV3IHR5cGVzLkFWYWwoT2JqUHJvdG8pLCAnQXJyYXkucHJvdG90eXBlJyksXG4gICAgICAgICAgICBSZWdFeHA6IG5ldyB0eXBlcy5PYmpUeXBlKG5ldyB0eXBlcy5BVmFsKE9ialByb3RvKSwgJ1JlZ0V4cC5wcm90b3R5cGUnKSxcbiAgICAgICAgICAgIFN0cmluZzogbmV3IHR5cGVzLk9ialR5cGUobmV3IHR5cGVzLkFWYWwoT2JqUHJvdG8pLCAnU3RyaW5nLnByb3RvdHlwZScpLFxuICAgICAgICAgICAgTnVtYmVyOiBuZXcgdHlwZXMuT2JqVHlwZShuZXcgdHlwZXMuQVZhbChPYmpQcm90byksICdOdW1iZXIucHJvdG90eXBlJyksXG4gICAgICAgICAgICBCb29sZWFuOiBuZXcgdHlwZXMuT2JqVHlwZShuZXcgdHlwZXMuQVZhbChPYmpQcm90byksICdCb29sZWFuLnByb3RvdHlwZScpXG4gICAgICAgIH1cblxuICAgIH07XG4gICAgY0dlbi5hZGRDb25zdHJhaW50cyhhc3QsIGluaXRTdGF0dXMsIHJ0Q1gpO1xuICAgIHZhciBjb25zdHJhaW50cyA9IGNHZW4uY29uc3RyYWludHM7XG4gICAgLy9hdXguc2hvd1VuZm9sZGVkKGdCbG9ja0FuZEFubm90YXRlZEFTVC5hc3QpO1xuICAgIC8vIGF1eC5zaG93VW5mb2xkZWQoY29uc3RyYWludHMpO1xuICAgIC8vIGF1eC5zaG93VW5mb2xkZWQoZ0Jsb2NrKTtcbiAgICAvLyBjb25zb2xlLmxvZyh1dGlsLmluc3BlY3QoZ0Jsb2NrLCB7ZGVwdGg6IDEwfSkpO1xuICAgIGlmIChyZXRBbGwpIHtcbiAgICAgICAgcmV0dXJuIHtnT2JqZWN0OiBnT2JqZWN0LCBBU1Q6IGFzdCwgZ0Jsb2NrOiBnQmxvY2ssIGdTY29wZTogZ1Njb3BlfTtcbiAgICB9IGVsc2Uge1xuICAgICAgICByZXR1cm4gZ09iamVjdDtcbiAgICB9XG59XG5cbmV4cG9ydHMuYW5hbHl6ZSA9IGFuYWx5emU7XG5leHBvcnRzLmZpbmRJZGVudGlmaWVyQXQgPSB2YXJSZWZzLmZpbmRJZGVudGlmaWVyQXQ7XG5leHBvcnRzLmZpbmRWYXJSZWZzQXQgPSB2YXJSZWZzLmZpbmRWYXJSZWZzQXQ7XG4iLCIvKlxuIEphdmFTY3JpcHTripQgZ2xvYmFsLCBmdW5jdGlvbiBibG9jaywgY2F0Y2ggYmxvY2vsl5Ag67OA7IiY6rCAIOuLrOumsOuLpC5cbiBFUzbripQg7J2867CYIGJsb2Nr7JeQ64+EIOuLrOumsOuLpC5cblxuIFZhckJsb2Nr64qUIOqwgSBibG9ja+yXkCDri6zrprAg67OA7IiY65Ok7J2EIOuCmO2DgOuCuOuLpC5cbiAtIHBhcmVuICAgICAgOiBCbG9ja1ZhcnMsIOuwlOq5pSBibG9ja+ydhCDrgpjtg4DrgrTripQg6rCd7LK0XG4gLSBvcmlnaW5MYWJlbDogbnVtYmVyLCDtlbTri7kgQmxvY2tWYXJz6rCAIOyEoOyWuOuQnCBBU1Qgbm9kZeydmCBAbGFiZWxcbiAgICBvcmlnaW7snbQg65CgIOyImCDsnojripQgbm9kZeuKlFxuICAgIEZ1bmN0aW9uLmJvZHksIENhdGNoQ2xhdXNlLmJsb2NrIOuRkOqwgOyngOuLpC5cbiAgICDrkZDqsIDsp4Ag66qo65GQIEJsb2NrU3RhdGVtZW507J2064ukLlxuIC0gaXNDYXRjaCAgICA6IGJvb2xlYW4sXG4gICAqIHRydWUgIC0+IGNhdGNoIGJsb2NrXG4gICAqIGZhbHNlIC0+IGZ1bmN0aW9uIGJsb2NrLCBvciBnbG9iYWxcblxuIC0gcGFyYW1WYXJOYW1lcyA6IOunpOqwnOuzgOyImCDsnbTrpoQg66qp66GdLCDrp6TqsJwg67OA7IiYIOyInOyEnOuMgOuhnFxuIC0gbG9jYWxWYXJOYW1lcyA6IOyngOyXrSDrs4DsiJgg7J2066aEIOuqqeuhnSwg7Iic7IScIOustOydmOuvuFxuICAgIGFyZ3VtZW50c+ulvCDsgqzsmqntlZjripQg6rK97JqwIGxvY2FsVmFyTmFtZXPsl5Ag65Ox7J6l7ZWY6rOgLFxuICAgIGFyZ3VtZW50cyBvYmplY3Trpbwg7IKs7Jqp7ZWY66m0IHVzZUFyZ3VtZW50c09iamVjdCA9PSB0cnVlXG5cbiAtIChvcHRpb25hbCkgdXNlQXJndW1lbnRzT2JqZWN0OiBib29sZWFuXG4gICAg7ZWo7IiYIGJvZHkgYmxvY2vsnbgg6rK97Jqw7JeQ66eMIOyCrOyaqSDqsIDriqVcbiAgICAqIHRydWUgIDogYXJndW1lbnRzIG9iamVjdOqwgCDsgqzsmqnrkJjsl4jri6QuXG4gICAgICDspokg7ZWo7IiYIGJvZHnsl5DshJwg67OA7IiYIGFyZ3VtZW50c+ulvCDshKDslrgg7JeG7J20IOyCrOyaqe2WiOuLpC5cbiAgICAgIOydtCDqsr3smrAsIGFyZ3VtZW50c+uKlCDtlajsiJjsnZgg7KeA7JetIOuzgOyImOuhnCDrk7HroZ3rkJzri6QuXG4gICAgKiBmYWxzZSDsnbgg6rK97Jqw64qUIOyXhuuLpC4g6re465+06rGw66m0IOyVhOyYiCDrs4DsiJgg7J6Q7LK06rCAIOyXhuuLpC5cblxuIC0gdXNlZFZhcmlhYmxlcyA6IOqwgSBibG9ja+ydmCDrp6TqsJzrs4DsiJgsIOyngOyXreuzgOyImCDspJFcbiAgIOyCrOyaqeuQmOuKlCDsnITsuZjqsIAg7J6I64qUIOqyg+uTpOydmCDrqqnroZ1cblxuIC0gaW5zdGFuY2VzIDogRGVsdGEgLT4gVmFyQmxvY2vsnZgg67OA7IiY65OkIC0+IEFWYWxcbiAgIGdldEluc3RhbmNlKGRlbHRhKSDrpbwg7Ya17ZW0IOqwmeydgCBkZWx0YeuKlCDqsJnsnYAgbWFwcGluZyDso7zqsowg66eM65OsXG5cbiAtIHNjb3BlSW5zdGFuY2VzIDogW1Njb3BlXVxuICAg7ZiE7J6sIFZhckJsb2Nr7J2EIOuniOyngOunieycvOuhnCDtlZjripQgU2NvcGXrpbwg66qo65GQIOuqqOydgOuLpC5cbiAgIGdldFNjb3BlSW5zdGFuY2UoZGVsdGEsIHBhcmVuKSDsnYQg7Ya17ZW0IOqwmeydgCBzY29wZSBjaGFpbuydgFxuICAg6rCZ7J2AIOqwneyytOqwgCDrkJjrj4TroZ0g66eM65Og64ukLlxuKi9cbid1c2Ugc3RyaWN0JztcblxudmFyIHR5cGVzID0gcmVxdWlyZSgnLi9kb21haW5zL3R5cGVzJyk7XG52YXIgd2FsayA9IHJlcXVpcmUoJ2Fjb3JuL2Rpc3Qvd2FsaycpO1xudmFyIGF1eCA9IHJlcXVpcmUoJy4vYXV4Jyk7XG5cbmZ1bmN0aW9uIFZhckJsb2NrKHBhcmVuLCBvcmlnaW5Ob2RlLCBpc0NhdGNoKSB7XG4gICAgdGhpcy5wYXJlbiA9IHBhcmVuO1xuICAgIHRoaXMub3JpZ2luTm9kZSA9IG9yaWdpbk5vZGU7XG4gICAgdGhpcy5vcmlnaW5MYWJlbCA9IG9yaWdpbk5vZGVbJ0BsYWJlbCddO1xuICAgIHRoaXMuaXNDYXRjaCA9IGlzQ2F0Y2g7XG4gICAgdGhpcy5wYXJhbVZhck5hbWVzID0gW107XG4gICAgdGhpcy5sb2NhbFZhck5hbWVzID0gW107XG5cbiAgICB0aGlzLnVzZWRWYXJpYWJsZXMgPSBbXTtcbiAgICAvLyB0aGlzLnVzZUFyZ3VtZW50c09iamVjdFxuICAgIHRoaXMuaW5zdGFuY2VzID0gT2JqZWN0LmNyZWF0ZShudWxsKTtcbiAgICB0aGlzLnNjb3BlSW5zdGFuY2VzID0gW107XG59XG5cblZhckJsb2NrLnByb3RvdHlwZSA9IE9iamVjdC5jcmVhdGUobnVsbCk7XG5cblZhckJsb2NrLnByb3RvdHlwZS5pc0dsb2JhbCA9IGZ1bmN0aW9uICgpIHtcbiAgICByZXR1cm4gdGhpcy5wYXJlbiA9PSBudWxsO1xufTtcblZhckJsb2NrLnByb3RvdHlwZS5pc0Z1bmN0aW9uID0gZnVuY3Rpb24gKCkge1xuICAgIHJldHVybiB0aGlzLnBhcmVuICE9IG51bGwgJiYgdGhpcy5sb2NhbFZhck5hbWVzICE9IG51bGw7XG59O1xuVmFyQmxvY2sucHJvdG90eXBlLmlzQ2F0Y2hCbG9jayA9IGZ1bmN0aW9uICgpIHtcbiAgICByZXR1cm4gdGhpcy5pc0NhdGNoO1xufTtcblxuVmFyQmxvY2sucHJvdG90eXBlLmdldExvY2FsVmFyTmFtZXMgPSBmdW5jdGlvbiAoKSB7XG4gICAgcmV0dXJuIHRoaXMubG9jYWxWYXJOYW1lcztcbn07XG5WYXJCbG9jay5wcm90b3R5cGUuZ2V0UGFyYW1WYXJOYW1lcyA9IGZ1bmN0aW9uICgpIHtcbiAgICByZXR1cm4gdGhpcy5wYXJhbVZhck5hbWVzO1xufTtcblZhckJsb2NrLnByb3RvdHlwZS5oYXNMb2NhbFZhciA9IGZ1bmN0aW9uICh2YXJOYW1lKSB7XG4gICAgcmV0dXJuIHRoaXMubG9jYWxWYXJOYW1lcyAmJiB0aGlzLmxvY2FsVmFyTmFtZXMuaW5kZXhPZih2YXJOYW1lKSA+IC0xO1xufTtcblZhckJsb2NrLnByb3RvdHlwZS5oYXNQYXJhbVZhciA9IGZ1bmN0aW9uICh2YXJOYW1lKSB7XG4gICAgcmV0dXJuIHRoaXMucGFyYW1WYXJOYW1lcy5pbmRleE9mKHZhck5hbWUpID4gLTE7XG59O1xuVmFyQmxvY2sucHJvdG90eXBlLmhhc1ZhciA9IGZ1bmN0aW9uICh2YXJOYW1lKSB7XG4gICAgcmV0dXJuIHRoaXMuaGFzUGFyYW1WYXIodmFyTmFtZSkgfHwgdGhpcy5oYXNMb2NhbFZhcih2YXJOYW1lKTtcbn07XG5cblZhckJsb2NrLnByb3RvdHlwZS5hZGREZWNsYXJlZExvY2FsVmFyID0gZnVuY3Rpb24gKHZhck5hbWUsIGlzRnVuRGVjbCkge1xuICAgIHZhciBjdXJyQmxvY2sgPSB0aGlzO1xuICAgIC8vIHBlZWwgb2ZmIGluaXRpYWwgY2F0Y2ggYmxvY2tzXG4gICAgLy8gZm9yIGZ1bmN0aW9uIGRlY2wsIHNraXAgYW55IGNhdGNoIGJsb2NrcyxcbiAgICAvLyBmb3IgdmFyaWFibGUgZGVjbCwgc2tpcCBjYXRjaCBibG9jayB3aXRoIGRpZmZlcmVudCB2YXJOYW1lLlxuICAgIHdoaWxlIChjdXJyQmxvY2suaXNDYXRjaEJsb2NrKCkgJiZcbiAgICAgICAgICAgKGlzRnVuRGVjbCB8fCAhY3VyckJsb2NrLmhhc1BhcmFtVmFyKHZhck5hbWUpKSkge1xuICAgICAgICBjdXJyQmxvY2sgPSBjdXJyQmxvY2sucGFyZW47XG4gICAgfVxuICAgIC8vIGlmIGFscmVhZHkgYWRkZWQsIGRvIG5vdCBhZGRcbiAgICBpZiAoIWN1cnJCbG9jay5oYXNWYXIodmFyTmFtZSkpIHtcbiAgICAgICAgY3VyckJsb2NrLmxvY2FsVmFyTmFtZXMucHVzaCh2YXJOYW1lKTtcbiAgICB9XG4gICAgLy8gcmV0dXJucyB0aGUgYmxvY2sgb2JqZWN0IHRoYXQgY29udGFpbnMgdGhlIHZhcmlhYmxlXG4gICAgcmV0dXJuIGN1cnJCbG9jaztcbn07XG5WYXJCbG9jay5wcm90b3R5cGUuYWRkUGFyYW1WYXIgPSBmdW5jdGlvbiAodmFyTmFtZSkge1xuICAgIHRoaXMucGFyYW1WYXJOYW1lcy5wdXNoKHZhck5hbWUpO1xufTtcblZhckJsb2NrLnByb3RvdHlwZS5maW5kVmFySW5DaGFpbiA9IGZ1bmN0aW9uICh2YXJOYW1lKSB7XG4gICAgdmFyIGN1cnJCbG9jayA9IHRoaXM7XG4gICAgd2hpbGUgKGN1cnJCbG9jayAmJiBjdXJyQmxvY2sucGFyZW4gJiYgIWN1cnJCbG9jay5oYXNWYXIodmFyTmFtZSkpIHtcbiAgICAgICAgY3VyckJsb2NrID0gY3VyckJsb2NrLnBhcmVuO1xuICAgIH1cbiAgICAvLyBpZiBub3QgZm91bmQsIGl0IHdpbGwgcmV0dXJuIHRoZSBnbG9iYWxcbiAgICByZXR1cm4gY3VyckJsb2NrO1xufTtcblxuVmFyQmxvY2sucHJvdG90eXBlLmFkZFVzZWRWYXIgPSBmdW5jdGlvbiAodmFyTmFtZSkge1xuICAgIGlmICh0aGlzLnVzZWRWYXJpYWJsZXMuaW5kZXhPZih2YXJOYW1lKSA9PT0gLTEpIHtcbiAgICAgICAgdGhpcy51c2VkVmFyaWFibGVzLnB1c2godmFyTmFtZSk7XG4gICAgfVxufTtcblZhckJsb2NrLnByb3RvdHlwZS5nZXRVc2VkVmFyTmFtZXMgPSBmdW5jdGlvbiAoKSB7XG4gICAgcmV0dXJuIHRoaXMudXNlZFZhcmlhYmxlcztcbn07XG5WYXJCbG9jay5wcm90b3R5cGUuaXNVc2VkVmFyID0gZnVuY3Rpb24gKHZhck5hbWUpIHtcbiAgICByZXR1cm4gdGhpcy51c2VkVmFyaWFibGVzLmluZGV4T2YodmFyTmFtZSkgPiAtMTtcbn07XG5cbi8vIHJldHVybnMgYSBtYXBwaW5nXG5WYXJCbG9jay5wcm90b3R5cGUuZ2V0SW5zdGFuY2UgPSBmdW5jdGlvbiAoZGVsdGEpIHtcbiAgICBpZiAodGhpcy5pbnN0YW5jZXNbZGVsdGFdKSB7XG4gICAgICAgIHJldHVybiB0aGlzLmluc3RhbmNlc1tkZWx0YV07XG4gICAgfVxuICAgIC8vIGNvbnN0cnVjdCBWYXJNYXBcbiAgICB2YXIgdmFyTWFwID0gbmV3IE1hcCgpO1xuICAgIHZhciB2YXJOYW1lcyA9IHRoaXMuZ2V0UGFyYW1WYXJOYW1lcygpLmNvbmNhdCh0aGlzLmdldExvY2FsVmFyTmFtZXMoKSk7XG5cbiAgICBmb3IgKHZhciBpID0gMDsgaSA8IHZhck5hbWVzLmxlbmd0aDsgaSsrKSB7XG4gICAgICAgIHZhck1hcC5zZXQodmFyTmFtZXNbaV0sIG5ldyB0eXBlcy5BVmFsKCkpO1xuICAgIH1cbiAgICAvLyByZW1lbWJlciB0aGUgaW5zdGFuY2VcbiAgICB0aGlzLmluc3RhbmNlc1tkZWx0YV0gPSB2YXJNYXA7XG4gICAgcmV0dXJuIHZhck1hcDtcbn07XG4vLyByZXR1cm5zIGFuIGFycmF5XG5WYXJCbG9jay5wcm90b3R5cGUuZ2V0UGFyYW1BVmFscyA9IGZ1bmN0aW9uIChkZWx0YSkge1xuICAgIHZhciBpbnN0YW5jZSA9IHRoaXMuZ2V0SW5zdGFuY2UoZGVsdGEpO1xuICAgIHZhciBwYXJhbXMgPSBbXTtcbiAgICB0aGlzLmdldFBhcmFtVmFyTmFtZXMoKS5mb3JFYWNoKGZ1bmN0aW9uIChuYW1lKSB7XG4gICAgICAgIHBhcmFtcy5wdXNoKGluc3RhbmNlW2F1eC5pbnRlcm5hbE5hbWUobmFtZSldKTtcbiAgICB9KTtcbiAgICByZXR1cm4gcGFyYW1zO1xufTtcbi8vIHJldHVybnMgYW4gQVZhbFxuVmFyQmxvY2sucHJvdG90eXBlLmdldEFyZ3VtZW50c0FWYWwgPSBmdW5jdGlvbiAoZGVsdGEpIHtcbiAgICBpZiAoIXRoaXMudXNlQXJndW1lbnRzT2JqZWN0KSB7XG4gICAgICAgIHRocm93IG5ldyBFcnJvcignTm90IGZvciB0aGlzIFZhckJsb2NrJyk7XG4gICAgfVxuICAgIHJldHVybiB0aGlzLmdldEluc3RhbmNlKGRlbHRhKVthdXguaW50ZXJuYWxOYW1lKCdhcmd1bWVudHMnKV07XG59O1xuXG4vLyBnZXQgYSBTY29wZSBpbnN0YW5jZVxuVmFyQmxvY2sucHJvdG90eXBlLmdldFNjb3BlSW5zdGFuY2UgPSBmdW5jdGlvbiAocGFyZW4sIGRlbHRhKSB7XG4gICAgdmFyIHZhck1hcCA9IHRoaXMuZ2V0SW5zdGFuY2UoZGVsdGEpO1xuICAgIHZhciBmb3VuZCA9IG51bGw7XG5cbiAgICB0aGlzLnNjb3BlSW5zdGFuY2VzLmZvckVhY2goZnVuY3Rpb24gKHNjKSB7XG4gICAgICAgIGlmIChzYy5wYXJlbiA9PT0gcGFyZW4gJiYgc2MudmFyTWFwID09PSB2YXJNYXApIGZvdW5kID0gc2M7XG4gICAgfSk7XG5cbiAgICBpZiAoZm91bmQpIHtcbiAgICAgICAgcmV0dXJuIGZvdW5kO1xuICAgIH0gZWxzZSB7XG4gICAgICAgIHZhciBuZXdTY29wZUluc3RhbmNlID0gbmV3IFNjb3BlKHBhcmVuLCB2YXJNYXAsIHRoaXMpO1xuICAgICAgICB0aGlzLnNjb3BlSW5zdGFuY2VzLnB1c2gobmV3U2NvcGVJbnN0YW5jZSk7XG4gICAgICAgIHJldHVybiBuZXdTY29wZUluc3RhbmNlO1xuICAgIH1cbn07XG5cbnZhciBkZWNsYXJlZFZhcmlhYmxlRmluZGVyID0gd2Fsay5tYWtlKHtcbiAgIEZ1bmN0aW9uOiBmdW5jdGlvbiAobm9kZSwgY3VyckJsb2NrLCBjKSB7XG4gICAgICAgIHZhciBwYXJlbkJsb2NrID0gY3VyckJsb2NrO1xuICAgICAgICBpZiAobm9kZS5pZCkge1xuICAgICAgICAgICAgdmFyIGZ1bmNOYW1lID0gbm9kZS5pZC5uYW1lO1xuICAgICAgICAgICAgcGFyZW5CbG9jayA9IGN1cnJCbG9jay5hZGREZWNsYXJlZExvY2FsVmFyKGZ1bmNOYW1lLCB0cnVlKTtcbiAgICAgICAgfVxuICAgICAgICAvLyBjcmVhdGUgYSBWYXJCbG9jayBmb3IgZnVuY3Rpb25cbiAgICAgICAgdmFyIGZ1bmNCbG9jayA9IG5ldyBWYXJCbG9jayhwYXJlbkJsb2NrLCBub2RlKTtcbiAgICAgICAgbm9kZS5ib2R5WydAYmxvY2snXSA9IGZ1bmNCbG9jaztcbiAgICAgICAgLy8gYWRkIGZ1bmN0aW9uIHBhcmFtZXRlcnMgdG8gdGhlIHNjb3BlXG4gICAgICAgIGZvciAodmFyIGkgPSAwOyBpIDwgbm9kZS5wYXJhbXMubGVuZ3RoOyBpKyspIHtcbiAgICAgICAgICAgIHZhciBwYXJhbU5hbWUgPSBub2RlLnBhcmFtc1tpXS5uYW1lO1xuICAgICAgICAgICAgZnVuY0Jsb2NrLmFkZFBhcmFtVmFyKHBhcmFtTmFtZSk7XG4gICAgICAgIH1cbiAgICAgICAgYyhub2RlLmJvZHksIGZ1bmNCbG9jaywgdW5kZWZpbmVkKTtcbiAgICB9LFxuICAgIFZhcmlhYmxlRGVjbGFyYXRpb246IGZ1bmN0aW9uIChub2RlLCBjdXJyQmxvY2ssIGMpIHtcbiAgICAgICAgZm9yICh2YXIgaSA9IDA7IGkgPCBub2RlLmRlY2xhcmF0aW9ucy5sZW5ndGg7IGkrKykge1xuICAgICAgICAgICAgdmFyIGRlY2wgPSBub2RlLmRlY2xhcmF0aW9uc1tpXTtcbiAgICAgICAgICAgIHZhciBuYW1lID0gZGVjbC5pZC5uYW1lO1xuICAgICAgICAgICAgY3VyckJsb2NrLmFkZERlY2xhcmVkTG9jYWxWYXIobmFtZSk7XG4gICAgICAgIH1cbiAgICAgICAgaWYgKGRlY2wuaW5pdCkgYyhkZWNsLmluaXQsIGN1cnJCbG9jaywgdW5kZWZpbmVkKTtcbiAgICB9LFxuICAgIFRyeVN0YXRlbWVudDogZnVuY3Rpb24gKG5vZGUsIGN1cnJTY29wZSwgYykge1xuICAgICAgICBjKG5vZGUuYmxvY2ssIGN1cnJTY29wZSwgdW5kZWZpbmVkKTtcbiAgICAgICAgaWYgKG5vZGUuaGFuZGxlcikge1xuICAgICAgICAgICAgYyhub2RlLmhhbmRsZXIsIGN1cnJTY29wZSwgdW5kZWZpbmVkKTtcbiAgICAgICAgfVxuICAgICAgICBpZiAobm9kZS5maW5hbGl6ZXIpIHtcbiAgICAgICAgICAgIGMobm9kZS5maW5hbGl6ZXIsIGN1cnJTY29wZSwgdW5kZWZpbmVkKTtcbiAgICAgICAgfVxuICAgIH0sXG4gICAgQ2F0Y2hDbGF1c2U6IGZ1bmN0aW9uIChub2RlLCBjdXJyQmxvY2ssIGMpIHtcbiAgICAgICAgdmFyIGNhdGNoQmxvY2sgPSBuZXcgVmFyQmxvY2soY3VyckJsb2NrLCBub2RlLCB0cnVlKTtcbiAgICAgICAgY2F0Y2hCbG9jay5hZGRQYXJhbVZhcihub2RlLnBhcmFtLm5hbWUpO1xuICAgICAgICBub2RlLmJvZHlbJ0BibG9jayddID0gY2F0Y2hCbG9jaztcbiAgICAgICAgYyhub2RlLmJvZHksIGNhdGNoQmxvY2ssIHVuZGVmaW5lZCk7XG4gICAgfVxufSk7XG5cbi8vIEZvciB2YXJpYWJsZXMgaW4gZ2xvYmFsIGFuZCBhcmd1bWVudHMgaW4gZnVuY3Rpb25zXG52YXIgdmFyaWFibGVVc2FnZUNvbGxlY3RvciA9IHdhbGsubWFrZSh7XG4gICAgSWRlbnRpZmllcjogZnVuY3Rpb24gKG5vZGUsIGN1cnJCbG9jaywgYykge1xuICAgICAgICB2YXIgY29udGFpbmluZ0Jsb2NrLCB2YXJOYW1lID0gbm9kZS5uYW1lO1xuICAgICAgICBpZiAodmFyTmFtZSAhPT0gJ2FyZ3VtZW50cycpIHtcbiAgICAgICAgICAgIGNvbnRhaW5pbmdCbG9jayA9IGN1cnJCbG9jay5maW5kVmFySW5DaGFpbih2YXJOYW1lKTtcbiAgICAgICAgICAgIGlmIChjb250YWluaW5nQmxvY2suaXNHbG9iYWwoKSkge1xuICAgICAgICAgICAgICAgIGNvbnRhaW5pbmdCbG9jay5hZGREZWNsYXJlZExvY2FsVmFyKHZhck5hbWUpO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgY29udGFpbmluZ0Jsb2NrLmFkZFVzZWRWYXIodmFyTmFtZSk7XG4gICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgICAvLyB2YXJOYW1lID09ICdhcmd1bWVudHMnXG4gICAgICAgICAgICBjb250YWluaW5nQmxvY2sgPSBjdXJyQmxvY2s7XG4gICAgICAgICAgICB3aGlsZSAoY29udGFpbmluZ0Jsb2NrLmlzQ2F0Y2hCbG9jaygpICYmXG4gICAgICAgICAgICAgICAgICAgICFjb250YWluaW5nQmxvY2suaGFzUGFyYW1WYXIodmFyTmFtZSkpIHtcbiAgICAgICAgICAgICAgICBjb250YWluaW5nQmxvY2sgPSBjb250YWluaW5nQmxvY2sucGFyZW47XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBpZiAoY29udGFpbmluZ0Jsb2NrLmhhc1Zhcih2YXJOYW1lKSkge1xuICAgICAgICAgICAgICAgIC8vIGFyZ3VtZW50cyBpcyBleHBsaWNpdGx5IGRlY2xhcmVkXG4gICAgICAgICAgICAgICAgY29udGFpbmluZ0Jsb2NrLmFkZFVzZWRWYXIodmFyTmFtZSk7XG4gICAgICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgICAgICAgIC8vIGFyZ3VtZW50cyBpcyBub3QgZXhwbGljaXRseSBkZWNsYXJlZFxuICAgICAgICAgICAgICAgIC8vIGFkZCBpdCBhcyBsb2NhbCB2YXJpYWJsZVxuICAgICAgICAgICAgICAgIGNvbnRhaW5pbmdCbG9jay5hZGREZWNsYXJlZExvY2FsVmFyKHZhck5hbWUpO1xuICAgICAgICAgICAgICAgIC8vIGFsc28gaXQgaXMgdXNlZFxuICAgICAgICAgICAgICAgIGNvbnRhaW5pbmdCbG9jay5hZGRVc2VkVmFyKHZhck5hbWUpO1xuICAgICAgICAgICAgICAgIGlmIChjb250YWluaW5nQmxvY2suaXNGdW5jdGlvbigpKSB7XG4gICAgICAgICAgICAgICAgICAgIGNvbnRhaW5pbmdCbG9jay51c2VBcmd1bWVudHNPYmplY3QgPSB0cnVlO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgIH1cbiAgICAgICAgfVxuICAgIH0sXG5cbiAgICBSZXR1cm5TdGF0ZW1lbnQ6IGZ1bmN0aW9uIChub2RlLCBjdXJyQmxvY2ssIGMpIHtcbiAgICAgICAgdmFyIGZ1bmN0aW9uQmxvY2sgPSBjdXJyQmxvY2s7XG4gICAgICAgIHdoaWxlIChmdW5jdGlvbkJsb2NrLmlzQ2F0Y2hCbG9jaygpKSB7XG4gICAgICAgICAgICBmdW5jdGlvbkJsb2NrID0gZnVuY3Rpb25CbG9jay5wYXJlbjtcbiAgICAgICAgfVxuICAgICAgICBpZiAoIWZ1bmN0aW9uQmxvY2suaXNHbG9iYWwoKSAmJiBub2RlLmFyZ3VtZW50ICE9PSBudWxsKSB7XG4gICAgICAgICAgICBmdW5jdGlvbkJsb2NrLnVzZVJldHVybldpdGhBcmd1bWVudCA9IHRydWU7XG4gICAgICAgIH1cbiAgICAgICAgaWYgKG5vZGUuYXJndW1lbnQpIHtcbiAgICAgICAgICAgIGMobm9kZS5hcmd1bWVudCwgY3VyckJsb2NrLCB1bmRlZmluZWQpO1xuICAgICAgICB9XG4gICAgfSxcblxuICAgIFNjb3BlQm9keTogZnVuY3Rpb24gKG5vZGUsIGN1cnJCbG9jaywgYykge1xuICAgICAgICBjKG5vZGUsIG5vZGVbJ0BibG9jayddIHx8IGN1cnJCbG9jayk7XG4gICAgfVxufSk7XG5cblxuZnVuY3Rpb24gYW5ub3RhdGVCbG9ja0luZm8oYXN0LCBnQmxvY2spIHtcbiAgICBpZiAoIWdCbG9jaykge1xuICAgICAgICAvLyB3aGVuIGdsb2JhbCBibG9jayBpcyBub3QgZ2l2ZW4sIGNyZWF0ZVxuICAgICAgICBnQmxvY2sgPSBuZXcgVmFyQmxvY2sobnVsbCwgYXN0KTtcbiAgICB9XG4gICAgYXN0WydAYmxvY2snXSA9IGdCbG9jaztcbiAgICB3YWxrLnJlY3Vyc2l2ZShhc3QsIGdCbG9jaywgbnVsbCwgZGVjbGFyZWRWYXJpYWJsZUZpbmRlcik7XG4gICAgd2Fsay5yZWN1cnNpdmUoYXN0LCBnQmxvY2ssIG51bGwsIHZhcmlhYmxlVXNhZ2VDb2xsZWN0b3IpO1xuICAgIHJldHVybiBhc3Q7XG59XG5cbi8vIGRlZmluZSBzY29wZSBvYmplY3RcbmZ1bmN0aW9uIFNjb3BlKHBhcmVuLCB2YXJNYXAsIHZiKSB7XG4gICAgdGhpcy5wYXJlbiA9IHBhcmVuO1xuICAgIHRoaXMudmFyTWFwID0gdmFyTWFwO1xuICAgIHRoaXMudmIgPSB2Yjtcbn1cblNjb3BlLnByb3RvdHlwZSA9IE9iamVjdC5jcmVhdGUobnVsbCk7XG4vLyBmaW5kIEFWYWwgb2YgYSB2YXJpYWJsZSBpbiB0aGUgY2hhaW5cblNjb3BlLnByb3RvdHlwZS5nZXRBVmFsT2YgPSBmdW5jdGlvbiAodmFyTmFtZSkge1xuICAgIHZhciBjdXJyID0gdGhpcztcbiAgICB3aGlsZSAoY3VyciAhPSBudWxsKSB7XG4gICAgICAgIGlmIChjdXJyLnZhck1hcC5oYXModmFyTmFtZSkpIHtcbiAgICAgICAgICAgIHJldHVybiBjdXJyLnZhck1hcC5nZXQodmFyTmFtZSk7XG4gICAgICAgIH1cbiAgICAgICAgY3VyciA9IGN1cnIucGFyZW47XG4gICAgfVxuICAgIHRocm93IG5ldyBFcnJvcignU2hvdWxkIGhhdmUgZm91bmQgdGhlIHZhcmlhYmxlJyk7XG59O1xuLy8gcmVtb3ZlIGluaXRpYWwgY2F0Y2ggc2NvcGVzIGZyb20gdGhlIGNoYWluXG5TY29wZS5wcm90b3R5cGUucmVtb3ZlSW5pdGlhbENhdGNoQmxvY2tzID0gZnVuY3Rpb24gKCkge1xuICAgIHZhciBjdXJyID0gdGhpcztcbiAgICB3aGlsZSAoY3Vyci52Yi5pc0NhdGNoQmxvY2soKSkge1xuICAgICAgICBjdXJyID0gY3Vyci5wYXJlbjtcbiAgICB9XG4gICAgcmV0dXJuIGN1cnI7XG59O1xuXG5cbmV4cG9ydHMuVmFyQmxvY2sgPSBWYXJCbG9jaztcbmV4cG9ydHMuYW5ub3RhdGVCbG9ja0luZm8gPSBhbm5vdGF0ZUJsb2NrSW5mbztcbmV4cG9ydHMuU2NvcGUgPSBTY29wZTtcbiIsInZhciB3YWxrID0gcmVxdWlyZSgnYWNvcm4vZGlzdC93YWxrJyk7XG52YXIgZnMgPSByZXF1aXJlKCdmcycpO1xudmFyIGluZmVyID0gcmVxdWlyZSgnLi9pbmZlcicpO1xuXG4vLyBhIHdhbGtlciB0aGF0IHZpc2l0cyBlYWNoIGlkIHdpdGggdmFyQmxvY2tcbnZhciB2YXJXYWxrZXI9IHdhbGsubWFrZSh7XG4gICAgRnVuY3Rpb246IGZ1bmN0aW9uIChub2RlLCB2YiwgYykge1xuICAgICAgICBjb25zdCBpbm5lclZiID0gbm9kZS5ib2R5WydAYmxvY2snXTtcbiAgICAgICAgaWYgKG5vZGUuaWQpIGMobm9kZS5pZCwgaW5uZXJWYik7XG4gICAgICAgIGZvciAobGV0IGkgPSAwOyBpIDwgbm9kZS5wYXJhbXMubGVuZ3RoOyBpKyspXG4gICAgICAgICAgICBjKG5vZGUucGFyYW1zW2ldLCBpbm5lclZiKTtcbiAgICAgICAgYyhub2RlLmJvZHksIGlubmVyVmIpO1xuICAgIH0sXG4gICAgVHJ5U3RhdGVtZW50OiBmdW5jdGlvbiAobm9kZSwgdmIsIGMpIHtcbiAgICAgICAgYyhub2RlLmJsb2NrLCB2Yik7XG4gICAgICAgIGlmIChub2RlLmhhbmRsZXIpIHtcbiAgICAgICAgICAgIGMobm9kZS5oYW5kbGVyLCB2Yik7XG4gICAgICAgIH1cbiAgICAgICAgaWYgKG5vZGUuZmluYWxpemVyKSB7XG4gICAgICAgICAgICBjKG5vZGUuZmluYWxpemVyLCB2Yik7XG4gICAgICAgIH1cbiAgICB9LFxuICAgIENhdGNoQ2xhdXNlOiBmdW5jdGlvbiAobm9kZSwgdmIsIGMpIHtcbiAgICAgICAgY29uc3QgY2F0Y2hWYiA9IG5vZGUuYm9keVsnQGJsb2NrJ107XG4gICAgICAgIGMobm9kZS5wYXJhbSwgY2F0Y2hWYik7XG4gICAgICAgIGMobm9kZS5ib2R5LCBjYXRjaFZiKTtcbiAgICB9LFxuICAgIFZhcmlhYmxlRGVjbGFyYXRpb246IGZ1bmN0aW9uIChub2RlLCB2YiwgYykge1xuICAgICAgICBmb3IgKGxldCBpID0gMDsgaSA8IG5vZGUuZGVjbGFyYXRpb25zLmxlbmd0aDsgKytpKSB7XG4gICAgICAgICAgICB2YXIgZGVjbCA9IG5vZGUuZGVjbGFyYXRpb25zW2ldO1xuICAgICAgICAgICAgYyhkZWNsLmlkLCB2Yik7XG4gICAgICAgICAgICBpZiAoZGVjbC5pbml0KSBjKGRlY2wuaW5pdCwgdmIpO1xuICAgICAgICB9XG4gICAgfVxufSk7XG5cbi8qKlxuICpcbiAqIEBwYXJhbSBwcmVOb2RlIC0gQXBwbHkgYmVmb3JlIHZpc2l0aW5nIHRoZSBjdXJyZW50IG5vZGUuXG4gKiBJZiByZXR1cm5zIGZhbHNlLCBkbyBub3QgdmlzaXQgdGhlIG5vZGUuXG4gKiBAcGFyYW0gcG9zdE5vZGUgLSBBcHBseSBhZnRlciB2aXNpdGluZyB0aGUgY3VycmVudCBub2RlLlxuICogSWYgZ2l2ZW4sIHJldHVybiB2YWx1ZXMgYXJlIG92ZXJyaWRkZW4uXG4gKiBAcmV0dXJucyB7Kn1cbiAqL1xuZnVuY3Rpb24gd3JhcFdhbGtlcih3YWxrZXIsIHByZU5vZGUsIHBvc3ROb2RlKSB7XG4gICAgY29uc3QgcmV0V2Fsa2VyID0ge307XG4gICAgLy8gd3JhcHBpbmcgZWFjaCBmdW5jdGlvbiBwcmVOb2RlIGFuZCBwb3N0Tm9kZVxuICAgIGZvciAobGV0IG5vZGVUeXBlIGluIHdhbGtlcikge1xuICAgICAgICBpZiAoIXdhbGtlci5oYXNPd25Qcm9wZXJ0eShub2RlVHlwZSkpIHtcbiAgICAgICAgICAgIGNvbnRpbnVlO1xuICAgICAgICB9XG4gICAgICAgIHJldFdhbGtlcltub2RlVHlwZV0gPSAobm9kZSwgdmIsIGMpID0+IHtcbiAgICAgICAgICAgIGxldCByZXQ7XG4gICAgICAgICAgICBpZiAoIXByZU5vZGUgfHwgcHJlTm9kZShub2RlLCB2YiwgYykpIHtcbiAgICAgICAgICAgICAgICByZXQgPSB3YWxrZXJbbm9kZVR5cGVdKG5vZGUsIHZiLCBjKTtcbiAgICAgICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgICAgICAgcmV0dXJuO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgaWYgKHBvc3ROb2RlKSB7XG4gICAgICAgICAgICAgICAgcmV0ID0gcG9zdE5vZGUobm9kZSwgdmIsIGMpO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgcmV0dXJuIHJldDtcbiAgICAgICAgfVxuICAgIH1cbiAgICByZXR1cm4gcmV0V2Fsa2VyO1xufVxuXG5mdW5jdGlvbiBmaW5kSWRlbnRpZmllckF0KGFzdCwgcG9zKSB7XG4gICAgXCJ1c2Ugc3RyaWN0XCI7XG5cbiAgICBmdW5jdGlvbiBGb3VuZChub2RlLCBzdGF0ZSkge1xuICAgICAgICB0aGlzLm5vZGUgPSBub2RlO1xuICAgICAgICB0aGlzLnN0YXRlID0gc3RhdGU7XG4gICAgfVxuXG4gICAgLy8gZmluZCB0aGUgbm9kZVxuICAgIGNvbnN0IHdhbGtlciA9IHdyYXBXYWxrZXIodmFyV2Fsa2VyLFxuICAgICAgICAobm9kZSwgdmIpID0+IHtcbiAgICAgICAgICAgIGlmIChub2RlLnN0YXJ0ID4gcG9zIHx8IG5vZGUuZW5kIDwgcG9zKSB7XG4gICAgICAgICAgICAgICAgcmV0dXJuIGZhbHNlO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgaWYgKG5vZGUudHlwZSA9PT0gJ0lkZW50aWZpZXInICYmIG5vZGUubmFtZSAhPT0gJ+KclicpIHtcbiAgICAgICAgICAgICAgICB0aHJvdyBuZXcgRm91bmQobm9kZSwgdmIpO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgcmV0dXJuIHRydWU7XG4gICAgICAgIH0pO1xuXG4gICAgdHJ5IHtcbiAgICAgICAgd2Fsay5yZWN1cnNpdmUoYXN0LCBhc3RbJ0BibG9jayddLCB3YWxrZXIpO1xuICAgIH0gY2F0Y2ggKGUpIHtcbiAgICAgICAgaWYgKGUgaW5zdGFuY2VvZiBGb3VuZCkge1xuICAgICAgICAgICAgcmV0dXJuIGU7XG4gICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgICB0aHJvdyBlO1xuICAgICAgICB9XG4gICAgfVxuICAgIC8vIGlkZW50aWZpZXIgbm90IGZvdW5kXG4gICAgcmV0dXJuIG51bGw7XG59XG5cbi8qKlxuICpcbiAqIEBwYXJhbSBhc3QgLSBzY29wZSBhbm5vdGF0ZWQgQVNUXG4gKiBAcGFyYW0ge251bWJlcn0gcG9zIC0gY2hhcmFjdGVyIHBvc2l0aW9uXG4gKiBAcmV0dXJucyB7Kn0gLSBhcnJheSBvZiBBU1Qgbm9kZXNcbiAqL1xuZnVuY3Rpb24gZmluZFZhclJlZnNBdChhc3QsIHBvcykge1xuICAgIFwidXNlIHN0cmljdFwiO1xuICAgIHZhciBmb3VuZCA9IGZpbmRJZGVudGlmaWVyQXQoYXN0LCBwb3MpO1xuICAgIGlmICghZm91bmQpIHtcbiAgICAgICAgLy8gcG9zIGlzIG5vdCBhdCBhIHZhcmlhYmxlXG4gICAgICAgIHJldHVybiBudWxsO1xuICAgIH1cbiAgICAvLyBmaW5kIHJlZnMgZm9yIHRoZSBpZCBub2RlXG4gICAgdmFyIHJlZnMgPSBmaW5kUmVmc1RvVmFyaWFibGUoYXN0LCBmb3VuZCk7XG5cbiAgICByZXR1cm4gcmVmcztcbn1cblxuLyoqXG4gKlxuICogQHBhcmFtIGFzdCAtIHNjb3BlIGFubm90YXRlZCBBU1RcbiAqIEBwYXJhbSBmb3VuZCAtIG5vZGUgYW5kIHZhckJsb2NrIG9mIHRoZSB2YXJpYWJsZVxuICogQHJldHVybnMge0FycmF5fSAtIGFycmF5IG9mIEFTVCBub2Rlc1xuICovXG5mdW5jdGlvbiBmaW5kUmVmc1RvVmFyaWFibGUoYXN0LCBmb3VuZCkge1xuICAgIFwidXNlIHN0cmljdFwiO1xuICAgIGNvbnN0IHZhck5hbWUgPSBmb3VuZC5ub2RlLm5hbWU7XG4gICAgY29uc3QgdmIxID0gZm91bmQuc3RhdGUuZmluZFZhckluQ2hhaW4odmFyTmFtZSk7XG4gICAgY29uc3QgcmVmcyA9IFtdO1xuXG4gICAgY29uc3Qgd2Fsa2VyID0gd2Fsay5tYWtlKHtcbiAgICAgICAgSWRlbnRpZmllcjogKG5vZGUsIHZiKSA9PiB7XG4gICAgICAgICAgICBpZiAobm9kZS5uYW1lICE9PSB2YXJOYW1lKSByZXR1cm47XG4gICAgICAgICAgICBpZiAodmIxID09PSB2Yi5maW5kVmFySW5DaGFpbih2YXJOYW1lKSkge1xuICAgICAgICAgICAgICAgIHJlZnMucHVzaChub2RlKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgfVxuICAgIH0sIHZhcldhbGtlcik7XG5cbiAgICB3YWxrLnJlY3Vyc2l2ZSh2YjEub3JpZ2luTm9kZSwgdmIxLCB3YWxrZXIpO1xuICAgIHJldHVybiByZWZzO1xufVxuXG5leHBvcnRzLmZpbmRJZGVudGlmaWVyQXQgPSBmaW5kSWRlbnRpZmllckF0O1xuZXhwb3J0cy5maW5kVmFyUmVmc0F0ID0gZmluZFZhclJlZnNBdDsiLCIoZnVuY3Rpb24oZil7aWYodHlwZW9mIGV4cG9ydHM9PT1cIm9iamVjdFwiJiZ0eXBlb2YgbW9kdWxlIT09XCJ1bmRlZmluZWRcIil7bW9kdWxlLmV4cG9ydHM9ZigpfWVsc2UgaWYodHlwZW9mIGRlZmluZT09PVwiZnVuY3Rpb25cIiYmZGVmaW5lLmFtZCl7ZGVmaW5lKFtdLGYpfWVsc2V7dmFyIGc7aWYodHlwZW9mIHdpbmRvdyE9PVwidW5kZWZpbmVkXCIpe2c9d2luZG93fWVsc2UgaWYodHlwZW9mIGdsb2JhbCE9PVwidW5kZWZpbmVkXCIpe2c9Z2xvYmFsfWVsc2UgaWYodHlwZW9mIHNlbGYhPT1cInVuZGVmaW5lZFwiKXtnPXNlbGZ9ZWxzZXtnPXRoaXN9Zy5hY29ybiA9IGYoKX19KShmdW5jdGlvbigpe3ZhciBkZWZpbmUsbW9kdWxlLGV4cG9ydHM7cmV0dXJuIChmdW5jdGlvbiBlKHQsbixyKXtmdW5jdGlvbiBzKG8sdSl7aWYoIW5bb10pe2lmKCF0W29dKXt2YXIgYT10eXBlb2YgcmVxdWlyZT09XCJmdW5jdGlvblwiJiZyZXF1aXJlO2lmKCF1JiZhKXJldHVybiBhKG8sITApO2lmKGkpcmV0dXJuIGkobywhMCk7dmFyIGY9bmV3IEVycm9yKFwiQ2Fubm90IGZpbmQgbW9kdWxlICdcIitvK1wiJ1wiKTt0aHJvdyBmLmNvZGU9XCJNT0RVTEVfTk9UX0ZPVU5EXCIsZn12YXIgbD1uW29dPXtleHBvcnRzOnt9fTt0W29dWzBdLmNhbGwobC5leHBvcnRzLGZ1bmN0aW9uKGUpe3ZhciBuPXRbb11bMV1bZV07cmV0dXJuIHMobj9uOmUpfSxsLGwuZXhwb3J0cyxlLHQsbixyKX1yZXR1cm4gbltvXS5leHBvcnRzfXZhciBpPXR5cGVvZiByZXF1aXJlPT1cImZ1bmN0aW9uXCImJnJlcXVpcmU7Zm9yKHZhciBvPTA7bzxyLmxlbmd0aDtvKyspcyhyW29dKTtyZXR1cm4gc30pKHsxOltmdW5jdGlvbihfZGVyZXFfLG1vZHVsZSxleHBvcnRzKXtcblxuXG4vLyBUaGUgbWFpbiBleHBvcnRlZCBpbnRlcmZhY2UgKHVuZGVyIGBzZWxmLmFjb3JuYCB3aGVuIGluIHRoZVxuLy8gYnJvd3NlcikgaXMgYSBgcGFyc2VgIGZ1bmN0aW9uIHRoYXQgdGFrZXMgYSBjb2RlIHN0cmluZyBhbmRcbi8vIHJldHVybnMgYW4gYWJzdHJhY3Qgc3ludGF4IHRyZWUgYXMgc3BlY2lmaWVkIGJ5IFtNb3ppbGxhIHBhcnNlclxuLy8gQVBJXVthcGldLlxuLy9cbi8vIFthcGldOiBodHRwczovL2RldmVsb3Blci5tb3ppbGxhLm9yZy9lbi1VUy9kb2NzL1NwaWRlck1vbmtleS9QYXJzZXJfQVBJXG5cblwidXNlIHN0cmljdFwiO1xuXG5leHBvcnRzLnBhcnNlID0gcGFyc2U7XG5cbi8vIFRoaXMgZnVuY3Rpb24gdHJpZXMgdG8gcGFyc2UgYSBzaW5nbGUgZXhwcmVzc2lvbiBhdCBhIGdpdmVuXG4vLyBvZmZzZXQgaW4gYSBzdHJpbmcuIFVzZWZ1bCBmb3IgcGFyc2luZyBtaXhlZC1sYW5ndWFnZSBmb3JtYXRzXG4vLyB0aGF0IGVtYmVkIEphdmFTY3JpcHQgZXhwcmVzc2lvbnMuXG5cbmV4cG9ydHMucGFyc2VFeHByZXNzaW9uQXQgPSBwYXJzZUV4cHJlc3Npb25BdDtcblxuLy8gQWNvcm4gaXMgb3JnYW5pemVkIGFzIGEgdG9rZW5pemVyIGFuZCBhIHJlY3Vyc2l2ZS1kZXNjZW50IHBhcnNlci5cbi8vIFRoZSBgdG9rZW5pemVgIGV4cG9ydCBwcm92aWRlcyBhbiBpbnRlcmZhY2UgdG8gdGhlIHRva2VuaXplci5cblxuZXhwb3J0cy50b2tlbml6ZXIgPSB0b2tlbml6ZXI7XG5leHBvcnRzLl9fZXNNb2R1bGUgPSB0cnVlO1xuLy8gQWNvcm4gaXMgYSB0aW55LCBmYXN0IEphdmFTY3JpcHQgcGFyc2VyIHdyaXR0ZW4gaW4gSmF2YVNjcmlwdC5cbi8vXG4vLyBBY29ybiB3YXMgd3JpdHRlbiBieSBNYXJpam4gSGF2ZXJiZWtlLCBJbmd2YXIgU3RlcGFueWFuLCBhbmRcbi8vIHZhcmlvdXMgY29udHJpYnV0b3JzIGFuZCByZWxlYXNlZCB1bmRlciBhbiBNSVQgbGljZW5zZS5cbi8vXG4vLyBHaXQgcmVwb3NpdG9yaWVzIGZvciBBY29ybiBhcmUgYXZhaWxhYmxlIGF0XG4vL1xuLy8gICAgIGh0dHA6Ly9tYXJpam5oYXZlcmJla2UubmwvZ2l0L2Fjb3JuXG4vLyAgICAgaHR0cHM6Ly9naXRodWIuY29tL21hcmlqbmgvYWNvcm4uZ2l0XG4vL1xuLy8gUGxlYXNlIHVzZSB0aGUgW2dpdGh1YiBidWcgdHJhY2tlcl1bZ2hidF0gdG8gcmVwb3J0IGlzc3Vlcy5cbi8vXG4vLyBbZ2hidF06IGh0dHBzOi8vZ2l0aHViLmNvbS9tYXJpam5oL2Fjb3JuL2lzc3Vlc1xuLy9cbi8vIFRoaXMgZmlsZSBkZWZpbmVzIHRoZSBtYWluIHBhcnNlciBpbnRlcmZhY2UuIFRoZSBsaWJyYXJ5IGFsc28gY29tZXNcbi8vIHdpdGggYSBbZXJyb3ItdG9sZXJhbnQgcGFyc2VyXVtkYW1taXRdIGFuZCBhblxuLy8gW2Fic3RyYWN0IHN5bnRheCB0cmVlIHdhbGtlcl1bd2Fsa10sIGRlZmluZWQgaW4gb3RoZXIgZmlsZXMuXG4vL1xuLy8gW2RhbW1pdF06IGFjb3JuX2xvb3NlLmpzXG4vLyBbd2Fsa106IHV0aWwvd2Fsay5qc1xuXG52YXIgX3N0YXRlID0gX2RlcmVxXyhcIi4vc3RhdGVcIik7XG5cbnZhciBQYXJzZXIgPSBfc3RhdGUuUGFyc2VyO1xuXG52YXIgX29wdGlvbnMgPSBfZGVyZXFfKFwiLi9vcHRpb25zXCIpO1xuXG52YXIgZ2V0T3B0aW9ucyA9IF9vcHRpb25zLmdldE9wdGlvbnM7XG5cbl9kZXJlcV8oXCIuL3BhcnNldXRpbFwiKTtcblxuX2RlcmVxXyhcIi4vc3RhdGVtZW50XCIpO1xuXG5fZGVyZXFfKFwiLi9sdmFsXCIpO1xuXG5fZGVyZXFfKFwiLi9leHByZXNzaW9uXCIpO1xuXG5leHBvcnRzLlBhcnNlciA9IF9zdGF0ZS5QYXJzZXI7XG5leHBvcnRzLnBsdWdpbnMgPSBfc3RhdGUucGx1Z2lucztcbmV4cG9ydHMuZGVmYXVsdE9wdGlvbnMgPSBfb3B0aW9ucy5kZWZhdWx0T3B0aW9ucztcblxudmFyIF9sb2NhdGlvbiA9IF9kZXJlcV8oXCIuL2xvY2F0aW9uXCIpO1xuXG5leHBvcnRzLlNvdXJjZUxvY2F0aW9uID0gX2xvY2F0aW9uLlNvdXJjZUxvY2F0aW9uO1xuZXhwb3J0cy5nZXRMaW5lSW5mbyA9IF9sb2NhdGlvbi5nZXRMaW5lSW5mbztcbmV4cG9ydHMuTm9kZSA9IF9kZXJlcV8oXCIuL25vZGVcIikuTm9kZTtcblxudmFyIF90b2tlbnR5cGUgPSBfZGVyZXFfKFwiLi90b2tlbnR5cGVcIik7XG5cbmV4cG9ydHMuVG9rZW5UeXBlID0gX3Rva2VudHlwZS5Ub2tlblR5cGU7XG5leHBvcnRzLnRva1R5cGVzID0gX3Rva2VudHlwZS50eXBlcztcblxudmFyIF90b2tlbmNvbnRleHQgPSBfZGVyZXFfKFwiLi90b2tlbmNvbnRleHRcIik7XG5cbmV4cG9ydHMuVG9rQ29udGV4dCA9IF90b2tlbmNvbnRleHQuVG9rQ29udGV4dDtcbmV4cG9ydHMudG9rQ29udGV4dHMgPSBfdG9rZW5jb250ZXh0LnR5cGVzO1xuXG52YXIgX2lkZW50aWZpZXIgPSBfZGVyZXFfKFwiLi9pZGVudGlmaWVyXCIpO1xuXG5leHBvcnRzLmlzSWRlbnRpZmllckNoYXIgPSBfaWRlbnRpZmllci5pc0lkZW50aWZpZXJDaGFyO1xuZXhwb3J0cy5pc0lkZW50aWZpZXJTdGFydCA9IF9pZGVudGlmaWVyLmlzSWRlbnRpZmllclN0YXJ0O1xuZXhwb3J0cy5Ub2tlbiA9IF9kZXJlcV8oXCIuL3Rva2VuaXplXCIpLlRva2VuO1xuXG52YXIgX3doaXRlc3BhY2UgPSBfZGVyZXFfKFwiLi93aGl0ZXNwYWNlXCIpO1xuXG5leHBvcnRzLmlzTmV3TGluZSA9IF93aGl0ZXNwYWNlLmlzTmV3TGluZTtcbmV4cG9ydHMubGluZUJyZWFrID0gX3doaXRlc3BhY2UubGluZUJyZWFrO1xuZXhwb3J0cy5saW5lQnJlYWtHID0gX3doaXRlc3BhY2UubGluZUJyZWFrRztcbnZhciB2ZXJzaW9uID0gXCIxLjIuMlwiO2V4cG9ydHMudmVyc2lvbiA9IHZlcnNpb247XG5cbmZ1bmN0aW9uIHBhcnNlKGlucHV0LCBvcHRpb25zKSB7XG4gIHZhciBwID0gcGFyc2VyKG9wdGlvbnMsIGlucHV0KTtcbiAgdmFyIHN0YXJ0UG9zID0gcC5wb3MsXG4gICAgICBzdGFydExvYyA9IHAub3B0aW9ucy5sb2NhdGlvbnMgJiYgcC5jdXJQb3NpdGlvbigpO1xuICBwLm5leHRUb2tlbigpO1xuICByZXR1cm4gcC5wYXJzZVRvcExldmVsKHAub3B0aW9ucy5wcm9ncmFtIHx8IHAuc3RhcnROb2RlQXQoc3RhcnRQb3MsIHN0YXJ0TG9jKSk7XG59XG5cbmZ1bmN0aW9uIHBhcnNlRXhwcmVzc2lvbkF0KGlucHV0LCBwb3MsIG9wdGlvbnMpIHtcbiAgdmFyIHAgPSBwYXJzZXIob3B0aW9ucywgaW5wdXQsIHBvcyk7XG4gIHAubmV4dFRva2VuKCk7XG4gIHJldHVybiBwLnBhcnNlRXhwcmVzc2lvbigpO1xufVxuXG5mdW5jdGlvbiB0b2tlbml6ZXIoaW5wdXQsIG9wdGlvbnMpIHtcbiAgcmV0dXJuIHBhcnNlcihvcHRpb25zLCBpbnB1dCk7XG59XG5cbmZ1bmN0aW9uIHBhcnNlcihvcHRpb25zLCBpbnB1dCkge1xuICByZXR1cm4gbmV3IFBhcnNlcihnZXRPcHRpb25zKG9wdGlvbnMpLCBTdHJpbmcoaW5wdXQpKTtcbn1cblxufSx7XCIuL2V4cHJlc3Npb25cIjo2LFwiLi9pZGVudGlmaWVyXCI6NyxcIi4vbG9jYXRpb25cIjo4LFwiLi9sdmFsXCI6OSxcIi4vbm9kZVwiOjEwLFwiLi9vcHRpb25zXCI6MTEsXCIuL3BhcnNldXRpbFwiOjEyLFwiLi9zdGF0ZVwiOjEzLFwiLi9zdGF0ZW1lbnRcIjoxNCxcIi4vdG9rZW5jb250ZXh0XCI6MTUsXCIuL3Rva2VuaXplXCI6MTYsXCIuL3Rva2VudHlwZVwiOjE3LFwiLi93aGl0ZXNwYWNlXCI6MTl9XSwyOltmdW5jdGlvbihfZGVyZXFfLG1vZHVsZSxleHBvcnRzKXtcbmlmICh0eXBlb2YgT2JqZWN0LmNyZWF0ZSA9PT0gJ2Z1bmN0aW9uJykge1xuICAvLyBpbXBsZW1lbnRhdGlvbiBmcm9tIHN0YW5kYXJkIG5vZGUuanMgJ3V0aWwnIG1vZHVsZVxuICBtb2R1bGUuZXhwb3J0cyA9IGZ1bmN0aW9uIGluaGVyaXRzKGN0b3IsIHN1cGVyQ3Rvcikge1xuICAgIGN0b3Iuc3VwZXJfID0gc3VwZXJDdG9yXG4gICAgY3Rvci5wcm90b3R5cGUgPSBPYmplY3QuY3JlYXRlKHN1cGVyQ3Rvci5wcm90b3R5cGUsIHtcbiAgICAgIGNvbnN0cnVjdG9yOiB7XG4gICAgICAgIHZhbHVlOiBjdG9yLFxuICAgICAgICBlbnVtZXJhYmxlOiBmYWxzZSxcbiAgICAgICAgd3JpdGFibGU6IHRydWUsXG4gICAgICAgIGNvbmZpZ3VyYWJsZTogdHJ1ZVxuICAgICAgfVxuICAgIH0pO1xuICB9O1xufSBlbHNlIHtcbiAgLy8gb2xkIHNjaG9vbCBzaGltIGZvciBvbGQgYnJvd3NlcnNcbiAgbW9kdWxlLmV4cG9ydHMgPSBmdW5jdGlvbiBpbmhlcml0cyhjdG9yLCBzdXBlckN0b3IpIHtcbiAgICBjdG9yLnN1cGVyXyA9IHN1cGVyQ3RvclxuICAgIHZhciBUZW1wQ3RvciA9IGZ1bmN0aW9uICgpIHt9XG4gICAgVGVtcEN0b3IucHJvdG90eXBlID0gc3VwZXJDdG9yLnByb3RvdHlwZVxuICAgIGN0b3IucHJvdG90eXBlID0gbmV3IFRlbXBDdG9yKClcbiAgICBjdG9yLnByb3RvdHlwZS5jb25zdHJ1Y3RvciA9IGN0b3JcbiAgfVxufVxuXG59LHt9XSwzOltmdW5jdGlvbihfZGVyZXFfLG1vZHVsZSxleHBvcnRzKXtcbi8vIHNoaW0gZm9yIHVzaW5nIHByb2Nlc3MgaW4gYnJvd3NlclxuXG52YXIgcHJvY2VzcyA9IG1vZHVsZS5leHBvcnRzID0ge307XG52YXIgcXVldWUgPSBbXTtcbnZhciBkcmFpbmluZyA9IGZhbHNlO1xuXG5mdW5jdGlvbiBkcmFpblF1ZXVlKCkge1xuICAgIGlmIChkcmFpbmluZykge1xuICAgICAgICByZXR1cm47XG4gICAgfVxuICAgIGRyYWluaW5nID0gdHJ1ZTtcbiAgICB2YXIgY3VycmVudFF1ZXVlO1xuICAgIHZhciBsZW4gPSBxdWV1ZS5sZW5ndGg7XG4gICAgd2hpbGUobGVuKSB7XG4gICAgICAgIGN1cnJlbnRRdWV1ZSA9IHF1ZXVlO1xuICAgICAgICBxdWV1ZSA9IFtdO1xuICAgICAgICB2YXIgaSA9IC0xO1xuICAgICAgICB3aGlsZSAoKytpIDwgbGVuKSB7XG4gICAgICAgICAgICBjdXJyZW50UXVldWVbaV0oKTtcbiAgICAgICAgfVxuICAgICAgICBsZW4gPSBxdWV1ZS5sZW5ndGg7XG4gICAgfVxuICAgIGRyYWluaW5nID0gZmFsc2U7XG59XG5wcm9jZXNzLm5leHRUaWNrID0gZnVuY3Rpb24gKGZ1bikge1xuICAgIHF1ZXVlLnB1c2goZnVuKTtcbiAgICBpZiAoIWRyYWluaW5nKSB7XG4gICAgICAgIHNldFRpbWVvdXQoZHJhaW5RdWV1ZSwgMCk7XG4gICAgfVxufTtcblxucHJvY2Vzcy50aXRsZSA9ICdicm93c2VyJztcbnByb2Nlc3MuYnJvd3NlciA9IHRydWU7XG5wcm9jZXNzLmVudiA9IHt9O1xucHJvY2Vzcy5hcmd2ID0gW107XG5wcm9jZXNzLnZlcnNpb24gPSAnJzsgLy8gZW1wdHkgc3RyaW5nIHRvIGF2b2lkIHJlZ2V4cCBpc3N1ZXNcbnByb2Nlc3MudmVyc2lvbnMgPSB7fTtcblxuZnVuY3Rpb24gbm9vcCgpIHt9XG5cbnByb2Nlc3Mub24gPSBub29wO1xucHJvY2Vzcy5hZGRMaXN0ZW5lciA9IG5vb3A7XG5wcm9jZXNzLm9uY2UgPSBub29wO1xucHJvY2Vzcy5vZmYgPSBub29wO1xucHJvY2Vzcy5yZW1vdmVMaXN0ZW5lciA9IG5vb3A7XG5wcm9jZXNzLnJlbW92ZUFsbExpc3RlbmVycyA9IG5vb3A7XG5wcm9jZXNzLmVtaXQgPSBub29wO1xuXG5wcm9jZXNzLmJpbmRpbmcgPSBmdW5jdGlvbiAobmFtZSkge1xuICAgIHRocm93IG5ldyBFcnJvcigncHJvY2Vzcy5iaW5kaW5nIGlzIG5vdCBzdXBwb3J0ZWQnKTtcbn07XG5cbi8vIFRPRE8oc2h0eWxtYW4pXG5wcm9jZXNzLmN3ZCA9IGZ1bmN0aW9uICgpIHsgcmV0dXJuICcvJyB9O1xucHJvY2Vzcy5jaGRpciA9IGZ1bmN0aW9uIChkaXIpIHtcbiAgICB0aHJvdyBuZXcgRXJyb3IoJ3Byb2Nlc3MuY2hkaXIgaXMgbm90IHN1cHBvcnRlZCcpO1xufTtcbnByb2Nlc3MudW1hc2sgPSBmdW5jdGlvbigpIHsgcmV0dXJuIDA7IH07XG5cbn0se31dLDQ6W2Z1bmN0aW9uKF9kZXJlcV8sbW9kdWxlLGV4cG9ydHMpe1xubW9kdWxlLmV4cG9ydHMgPSBmdW5jdGlvbiBpc0J1ZmZlcihhcmcpIHtcbiAgcmV0dXJuIGFyZyAmJiB0eXBlb2YgYXJnID09PSAnb2JqZWN0J1xuICAgICYmIHR5cGVvZiBhcmcuY29weSA9PT0gJ2Z1bmN0aW9uJ1xuICAgICYmIHR5cGVvZiBhcmcuZmlsbCA9PT0gJ2Z1bmN0aW9uJ1xuICAgICYmIHR5cGVvZiBhcmcucmVhZFVJbnQ4ID09PSAnZnVuY3Rpb24nO1xufVxufSx7fV0sNTpbZnVuY3Rpb24oX2RlcmVxXyxtb2R1bGUsZXhwb3J0cyl7XG4oZnVuY3Rpb24gKHByb2Nlc3MsZ2xvYmFsKXtcbi8vIENvcHlyaWdodCBKb3llbnQsIEluYy4gYW5kIG90aGVyIE5vZGUgY29udHJpYnV0b3JzLlxuLy9cbi8vIFBlcm1pc3Npb24gaXMgaGVyZWJ5IGdyYW50ZWQsIGZyZWUgb2YgY2hhcmdlLCB0byBhbnkgcGVyc29uIG9idGFpbmluZyBhXG4vLyBjb3B5IG9mIHRoaXMgc29mdHdhcmUgYW5kIGFzc29jaWF0ZWQgZG9jdW1lbnRhdGlvbiBmaWxlcyAodGhlXG4vLyBcIlNvZnR3YXJlXCIpLCB0byBkZWFsIGluIHRoZSBTb2Z0d2FyZSB3aXRob3V0IHJlc3RyaWN0aW9uLCBpbmNsdWRpbmdcbi8vIHdpdGhvdXQgbGltaXRhdGlvbiB0aGUgcmlnaHRzIHRvIHVzZSwgY29weSwgbW9kaWZ5LCBtZXJnZSwgcHVibGlzaCxcbi8vIGRpc3RyaWJ1dGUsIHN1YmxpY2Vuc2UsIGFuZC9vciBzZWxsIGNvcGllcyBvZiB0aGUgU29mdHdhcmUsIGFuZCB0byBwZXJtaXRcbi8vIHBlcnNvbnMgdG8gd2hvbSB0aGUgU29mdHdhcmUgaXMgZnVybmlzaGVkIHRvIGRvIHNvLCBzdWJqZWN0IHRvIHRoZVxuLy8gZm9sbG93aW5nIGNvbmRpdGlvbnM6XG4vL1xuLy8gVGhlIGFib3ZlIGNvcHlyaWdodCBub3RpY2UgYW5kIHRoaXMgcGVybWlzc2lvbiBub3RpY2Ugc2hhbGwgYmUgaW5jbHVkZWRcbi8vIGluIGFsbCBjb3BpZXMgb3Igc3Vic3RhbnRpYWwgcG9ydGlvbnMgb2YgdGhlIFNvZnR3YXJlLlxuLy9cbi8vIFRIRSBTT0ZUV0FSRSBJUyBQUk9WSURFRCBcIkFTIElTXCIsIFdJVEhPVVQgV0FSUkFOVFkgT0YgQU5ZIEtJTkQsIEVYUFJFU1Ncbi8vIE9SIElNUExJRUQsIElOQ0xVRElORyBCVVQgTk9UIExJTUlURUQgVE8gVEhFIFdBUlJBTlRJRVMgT0Zcbi8vIE1FUkNIQU5UQUJJTElUWSwgRklUTkVTUyBGT1IgQSBQQVJUSUNVTEFSIFBVUlBPU0UgQU5EIE5PTklORlJJTkdFTUVOVC4gSU5cbi8vIE5PIEVWRU5UIFNIQUxMIFRIRSBBVVRIT1JTIE9SIENPUFlSSUdIVCBIT0xERVJTIEJFIExJQUJMRSBGT1IgQU5ZIENMQUlNLFxuLy8gREFNQUdFUyBPUiBPVEhFUiBMSUFCSUxJVFksIFdIRVRIRVIgSU4gQU4gQUNUSU9OIE9GIENPTlRSQUNULCBUT1JUIE9SXG4vLyBPVEhFUldJU0UsIEFSSVNJTkcgRlJPTSwgT1VUIE9GIE9SIElOIENPTk5FQ1RJT04gV0lUSCBUSEUgU09GVFdBUkUgT1IgVEhFXG4vLyBVU0UgT1IgT1RIRVIgREVBTElOR1MgSU4gVEhFIFNPRlRXQVJFLlxuXG52YXIgZm9ybWF0UmVnRXhwID0gLyVbc2RqJV0vZztcbmV4cG9ydHMuZm9ybWF0ID0gZnVuY3Rpb24oZikge1xuICBpZiAoIWlzU3RyaW5nKGYpKSB7XG4gICAgdmFyIG9iamVjdHMgPSBbXTtcbiAgICBmb3IgKHZhciBpID0gMDsgaSA8IGFyZ3VtZW50cy5sZW5ndGg7IGkrKykge1xuICAgICAgb2JqZWN0cy5wdXNoKGluc3BlY3QoYXJndW1lbnRzW2ldKSk7XG4gICAgfVxuICAgIHJldHVybiBvYmplY3RzLmpvaW4oJyAnKTtcbiAgfVxuXG4gIHZhciBpID0gMTtcbiAgdmFyIGFyZ3MgPSBhcmd1bWVudHM7XG4gIHZhciBsZW4gPSBhcmdzLmxlbmd0aDtcbiAgdmFyIHN0ciA9IFN0cmluZyhmKS5yZXBsYWNlKGZvcm1hdFJlZ0V4cCwgZnVuY3Rpb24oeCkge1xuICAgIGlmICh4ID09PSAnJSUnKSByZXR1cm4gJyUnO1xuICAgIGlmIChpID49IGxlbikgcmV0dXJuIHg7XG4gICAgc3dpdGNoICh4KSB7XG4gICAgICBjYXNlICclcyc6IHJldHVybiBTdHJpbmcoYXJnc1tpKytdKTtcbiAgICAgIGNhc2UgJyVkJzogcmV0dXJuIE51bWJlcihhcmdzW2krK10pO1xuICAgICAgY2FzZSAnJWonOlxuICAgICAgICB0cnkge1xuICAgICAgICAgIHJldHVybiBKU09OLnN0cmluZ2lmeShhcmdzW2krK10pO1xuICAgICAgICB9IGNhdGNoIChfKSB7XG4gICAgICAgICAgcmV0dXJuICdbQ2lyY3VsYXJdJztcbiAgICAgICAgfVxuICAgICAgZGVmYXVsdDpcbiAgICAgICAgcmV0dXJuIHg7XG4gICAgfVxuICB9KTtcbiAgZm9yICh2YXIgeCA9IGFyZ3NbaV07IGkgPCBsZW47IHggPSBhcmdzWysraV0pIHtcbiAgICBpZiAoaXNOdWxsKHgpIHx8ICFpc09iamVjdCh4KSkge1xuICAgICAgc3RyICs9ICcgJyArIHg7XG4gICAgfSBlbHNlIHtcbiAgICAgIHN0ciArPSAnICcgKyBpbnNwZWN0KHgpO1xuICAgIH1cbiAgfVxuICByZXR1cm4gc3RyO1xufTtcblxuXG4vLyBNYXJrIHRoYXQgYSBtZXRob2Qgc2hvdWxkIG5vdCBiZSB1c2VkLlxuLy8gUmV0dXJucyBhIG1vZGlmaWVkIGZ1bmN0aW9uIHdoaWNoIHdhcm5zIG9uY2UgYnkgZGVmYXVsdC5cbi8vIElmIC0tbm8tZGVwcmVjYXRpb24gaXMgc2V0LCB0aGVuIGl0IGlzIGEgbm8tb3AuXG5leHBvcnRzLmRlcHJlY2F0ZSA9IGZ1bmN0aW9uKGZuLCBtc2cpIHtcbiAgLy8gQWxsb3cgZm9yIGRlcHJlY2F0aW5nIHRoaW5ncyBpbiB0aGUgcHJvY2VzcyBvZiBzdGFydGluZyB1cC5cbiAgaWYgKGlzVW5kZWZpbmVkKGdsb2JhbC5wcm9jZXNzKSkge1xuICAgIHJldHVybiBmdW5jdGlvbigpIHtcbiAgICAgIHJldHVybiBleHBvcnRzLmRlcHJlY2F0ZShmbiwgbXNnKS5hcHBseSh0aGlzLCBhcmd1bWVudHMpO1xuICAgIH07XG4gIH1cblxuICBpZiAocHJvY2Vzcy5ub0RlcHJlY2F0aW9uID09PSB0cnVlKSB7XG4gICAgcmV0dXJuIGZuO1xuICB9XG5cbiAgdmFyIHdhcm5lZCA9IGZhbHNlO1xuICBmdW5jdGlvbiBkZXByZWNhdGVkKCkge1xuICAgIGlmICghd2FybmVkKSB7XG4gICAgICBpZiAocHJvY2Vzcy50aHJvd0RlcHJlY2F0aW9uKSB7XG4gICAgICAgIHRocm93IG5ldyBFcnJvcihtc2cpO1xuICAgICAgfSBlbHNlIGlmIChwcm9jZXNzLnRyYWNlRGVwcmVjYXRpb24pIHtcbiAgICAgICAgY29uc29sZS50cmFjZShtc2cpO1xuICAgICAgfSBlbHNlIHtcbiAgICAgICAgY29uc29sZS5lcnJvcihtc2cpO1xuICAgICAgfVxuICAgICAgd2FybmVkID0gdHJ1ZTtcbiAgICB9XG4gICAgcmV0dXJuIGZuLmFwcGx5KHRoaXMsIGFyZ3VtZW50cyk7XG4gIH1cblxuICByZXR1cm4gZGVwcmVjYXRlZDtcbn07XG5cblxudmFyIGRlYnVncyA9IHt9O1xudmFyIGRlYnVnRW52aXJvbjtcbmV4cG9ydHMuZGVidWdsb2cgPSBmdW5jdGlvbihzZXQpIHtcbiAgaWYgKGlzVW5kZWZpbmVkKGRlYnVnRW52aXJvbikpXG4gICAgZGVidWdFbnZpcm9uID0gcHJvY2Vzcy5lbnYuTk9ERV9ERUJVRyB8fCAnJztcbiAgc2V0ID0gc2V0LnRvVXBwZXJDYXNlKCk7XG4gIGlmICghZGVidWdzW3NldF0pIHtcbiAgICBpZiAobmV3IFJlZ0V4cCgnXFxcXGInICsgc2V0ICsgJ1xcXFxiJywgJ2knKS50ZXN0KGRlYnVnRW52aXJvbikpIHtcbiAgICAgIHZhciBwaWQgPSBwcm9jZXNzLnBpZDtcbiAgICAgIGRlYnVnc1tzZXRdID0gZnVuY3Rpb24oKSB7XG4gICAgICAgIHZhciBtc2cgPSBleHBvcnRzLmZvcm1hdC5hcHBseShleHBvcnRzLCBhcmd1bWVudHMpO1xuICAgICAgICBjb25zb2xlLmVycm9yKCclcyAlZDogJXMnLCBzZXQsIHBpZCwgbXNnKTtcbiAgICAgIH07XG4gICAgfSBlbHNlIHtcbiAgICAgIGRlYnVnc1tzZXRdID0gZnVuY3Rpb24oKSB7fTtcbiAgICB9XG4gIH1cbiAgcmV0dXJuIGRlYnVnc1tzZXRdO1xufTtcblxuXG4vKipcbiAqIEVjaG9zIHRoZSB2YWx1ZSBvZiBhIHZhbHVlLiBUcnlzIHRvIHByaW50IHRoZSB2YWx1ZSBvdXRcbiAqIGluIHRoZSBiZXN0IHdheSBwb3NzaWJsZSBnaXZlbiB0aGUgZGlmZmVyZW50IHR5cGVzLlxuICpcbiAqIEBwYXJhbSB7T2JqZWN0fSBvYmogVGhlIG9iamVjdCB0byBwcmludCBvdXQuXG4gKiBAcGFyYW0ge09iamVjdH0gb3B0cyBPcHRpb25hbCBvcHRpb25zIG9iamVjdCB0aGF0IGFsdGVycyB0aGUgb3V0cHV0LlxuICovXG4vKiBsZWdhY3k6IG9iaiwgc2hvd0hpZGRlbiwgZGVwdGgsIGNvbG9ycyovXG5mdW5jdGlvbiBpbnNwZWN0KG9iaiwgb3B0cykge1xuICAvLyBkZWZhdWx0IG9wdGlvbnNcbiAgdmFyIGN0eCA9IHtcbiAgICBzZWVuOiBbXSxcbiAgICBzdHlsaXplOiBzdHlsaXplTm9Db2xvclxuICB9O1xuICAvLyBsZWdhY3kuLi5cbiAgaWYgKGFyZ3VtZW50cy5sZW5ndGggPj0gMykgY3R4LmRlcHRoID0gYXJndW1lbnRzWzJdO1xuICBpZiAoYXJndW1lbnRzLmxlbmd0aCA+PSA0KSBjdHguY29sb3JzID0gYXJndW1lbnRzWzNdO1xuICBpZiAoaXNCb29sZWFuKG9wdHMpKSB7XG4gICAgLy8gbGVnYWN5Li4uXG4gICAgY3R4LnNob3dIaWRkZW4gPSBvcHRzO1xuICB9IGVsc2UgaWYgKG9wdHMpIHtcbiAgICAvLyBnb3QgYW4gXCJvcHRpb25zXCIgb2JqZWN0XG4gICAgZXhwb3J0cy5fZXh0ZW5kKGN0eCwgb3B0cyk7XG4gIH1cbiAgLy8gc2V0IGRlZmF1bHQgb3B0aW9uc1xuICBpZiAoaXNVbmRlZmluZWQoY3R4LnNob3dIaWRkZW4pKSBjdHguc2hvd0hpZGRlbiA9IGZhbHNlO1xuICBpZiAoaXNVbmRlZmluZWQoY3R4LmRlcHRoKSkgY3R4LmRlcHRoID0gMjtcbiAgaWYgKGlzVW5kZWZpbmVkKGN0eC5jb2xvcnMpKSBjdHguY29sb3JzID0gZmFsc2U7XG4gIGlmIChpc1VuZGVmaW5lZChjdHguY3VzdG9tSW5zcGVjdCkpIGN0eC5jdXN0b21JbnNwZWN0ID0gdHJ1ZTtcbiAgaWYgKGN0eC5jb2xvcnMpIGN0eC5zdHlsaXplID0gc3R5bGl6ZVdpdGhDb2xvcjtcbiAgcmV0dXJuIGZvcm1hdFZhbHVlKGN0eCwgb2JqLCBjdHguZGVwdGgpO1xufVxuZXhwb3J0cy5pbnNwZWN0ID0gaW5zcGVjdDtcblxuXG4vLyBodHRwOi8vZW4ud2lraXBlZGlhLm9yZy93aWtpL0FOU0lfZXNjYXBlX2NvZGUjZ3JhcGhpY3Ncbmluc3BlY3QuY29sb3JzID0ge1xuICAnYm9sZCcgOiBbMSwgMjJdLFxuICAnaXRhbGljJyA6IFszLCAyM10sXG4gICd1bmRlcmxpbmUnIDogWzQsIDI0XSxcbiAgJ2ludmVyc2UnIDogWzcsIDI3XSxcbiAgJ3doaXRlJyA6IFszNywgMzldLFxuICAnZ3JleScgOiBbOTAsIDM5XSxcbiAgJ2JsYWNrJyA6IFszMCwgMzldLFxuICAnYmx1ZScgOiBbMzQsIDM5XSxcbiAgJ2N5YW4nIDogWzM2LCAzOV0sXG4gICdncmVlbicgOiBbMzIsIDM5XSxcbiAgJ21hZ2VudGEnIDogWzM1LCAzOV0sXG4gICdyZWQnIDogWzMxLCAzOV0sXG4gICd5ZWxsb3cnIDogWzMzLCAzOV1cbn07XG5cbi8vIERvbid0IHVzZSAnYmx1ZScgbm90IHZpc2libGUgb24gY21kLmV4ZVxuaW5zcGVjdC5zdHlsZXMgPSB7XG4gICdzcGVjaWFsJzogJ2N5YW4nLFxuICAnbnVtYmVyJzogJ3llbGxvdycsXG4gICdib29sZWFuJzogJ3llbGxvdycsXG4gICd1bmRlZmluZWQnOiAnZ3JleScsXG4gICdudWxsJzogJ2JvbGQnLFxuICAnc3RyaW5nJzogJ2dyZWVuJyxcbiAgJ2RhdGUnOiAnbWFnZW50YScsXG4gIC8vIFwibmFtZVwiOiBpbnRlbnRpb25hbGx5IG5vdCBzdHlsaW5nXG4gICdyZWdleHAnOiAncmVkJ1xufTtcblxuXG5mdW5jdGlvbiBzdHlsaXplV2l0aENvbG9yKHN0ciwgc3R5bGVUeXBlKSB7XG4gIHZhciBzdHlsZSA9IGluc3BlY3Quc3R5bGVzW3N0eWxlVHlwZV07XG5cbiAgaWYgKHN0eWxlKSB7XG4gICAgcmV0dXJuICdcXHUwMDFiWycgKyBpbnNwZWN0LmNvbG9yc1tzdHlsZV1bMF0gKyAnbScgKyBzdHIgK1xuICAgICAgICAgICAnXFx1MDAxYlsnICsgaW5zcGVjdC5jb2xvcnNbc3R5bGVdWzFdICsgJ20nO1xuICB9IGVsc2Uge1xuICAgIHJldHVybiBzdHI7XG4gIH1cbn1cblxuXG5mdW5jdGlvbiBzdHlsaXplTm9Db2xvcihzdHIsIHN0eWxlVHlwZSkge1xuICByZXR1cm4gc3RyO1xufVxuXG5cbmZ1bmN0aW9uIGFycmF5VG9IYXNoKGFycmF5KSB7XG4gIHZhciBoYXNoID0ge307XG5cbiAgYXJyYXkuZm9yRWFjaChmdW5jdGlvbih2YWwsIGlkeCkge1xuICAgIGhhc2hbdmFsXSA9IHRydWU7XG4gIH0pO1xuXG4gIHJldHVybiBoYXNoO1xufVxuXG5cbmZ1bmN0aW9uIGZvcm1hdFZhbHVlKGN0eCwgdmFsdWUsIHJlY3Vyc2VUaW1lcykge1xuICAvLyBQcm92aWRlIGEgaG9vayBmb3IgdXNlci1zcGVjaWZpZWQgaW5zcGVjdCBmdW5jdGlvbnMuXG4gIC8vIENoZWNrIHRoYXQgdmFsdWUgaXMgYW4gb2JqZWN0IHdpdGggYW4gaW5zcGVjdCBmdW5jdGlvbiBvbiBpdFxuICBpZiAoY3R4LmN1c3RvbUluc3BlY3QgJiZcbiAgICAgIHZhbHVlICYmXG4gICAgICBpc0Z1bmN0aW9uKHZhbHVlLmluc3BlY3QpICYmXG4gICAgICAvLyBGaWx0ZXIgb3V0IHRoZSB1dGlsIG1vZHVsZSwgaXQncyBpbnNwZWN0IGZ1bmN0aW9uIGlzIHNwZWNpYWxcbiAgICAgIHZhbHVlLmluc3BlY3QgIT09IGV4cG9ydHMuaW5zcGVjdCAmJlxuICAgICAgLy8gQWxzbyBmaWx0ZXIgb3V0IGFueSBwcm90b3R5cGUgb2JqZWN0cyB1c2luZyB0aGUgY2lyY3VsYXIgY2hlY2suXG4gICAgICAhKHZhbHVlLmNvbnN0cnVjdG9yICYmIHZhbHVlLmNvbnN0cnVjdG9yLnByb3RvdHlwZSA9PT0gdmFsdWUpKSB7XG4gICAgdmFyIHJldCA9IHZhbHVlLmluc3BlY3QocmVjdXJzZVRpbWVzLCBjdHgpO1xuICAgIGlmICghaXNTdHJpbmcocmV0KSkge1xuICAgICAgcmV0ID0gZm9ybWF0VmFsdWUoY3R4LCByZXQsIHJlY3Vyc2VUaW1lcyk7XG4gICAgfVxuICAgIHJldHVybiByZXQ7XG4gIH1cblxuICAvLyBQcmltaXRpdmUgdHlwZXMgY2Fubm90IGhhdmUgcHJvcGVydGllc1xuICB2YXIgcHJpbWl0aXZlID0gZm9ybWF0UHJpbWl0aXZlKGN0eCwgdmFsdWUpO1xuICBpZiAocHJpbWl0aXZlKSB7XG4gICAgcmV0dXJuIHByaW1pdGl2ZTtcbiAgfVxuXG4gIC8vIExvb2sgdXAgdGhlIGtleXMgb2YgdGhlIG9iamVjdC5cbiAgdmFyIGtleXMgPSBPYmplY3Qua2V5cyh2YWx1ZSk7XG4gIHZhciB2aXNpYmxlS2V5cyA9IGFycmF5VG9IYXNoKGtleXMpO1xuXG4gIGlmIChjdHguc2hvd0hpZGRlbikge1xuICAgIGtleXMgPSBPYmplY3QuZ2V0T3duUHJvcGVydHlOYW1lcyh2YWx1ZSk7XG4gIH1cblxuICAvLyBJRSBkb2Vzbid0IG1ha2UgZXJyb3IgZmllbGRzIG5vbi1lbnVtZXJhYmxlXG4gIC8vIGh0dHA6Ly9tc2RuLm1pY3Jvc29mdC5jb20vZW4tdXMvbGlicmFyeS9pZS9kd3c1MnNidCh2PXZzLjk0KS5hc3B4XG4gIGlmIChpc0Vycm9yKHZhbHVlKVxuICAgICAgJiYgKGtleXMuaW5kZXhPZignbWVzc2FnZScpID49IDAgfHwga2V5cy5pbmRleE9mKCdkZXNjcmlwdGlvbicpID49IDApKSB7XG4gICAgcmV0dXJuIGZvcm1hdEVycm9yKHZhbHVlKTtcbiAgfVxuXG4gIC8vIFNvbWUgdHlwZSBvZiBvYmplY3Qgd2l0aG91dCBwcm9wZXJ0aWVzIGNhbiBiZSBzaG9ydGN1dHRlZC5cbiAgaWYgKGtleXMubGVuZ3RoID09PSAwKSB7XG4gICAgaWYgKGlzRnVuY3Rpb24odmFsdWUpKSB7XG4gICAgICB2YXIgbmFtZSA9IHZhbHVlLm5hbWUgPyAnOiAnICsgdmFsdWUubmFtZSA6ICcnO1xuICAgICAgcmV0dXJuIGN0eC5zdHlsaXplKCdbRnVuY3Rpb24nICsgbmFtZSArICddJywgJ3NwZWNpYWwnKTtcbiAgICB9XG4gICAgaWYgKGlzUmVnRXhwKHZhbHVlKSkge1xuICAgICAgcmV0dXJuIGN0eC5zdHlsaXplKFJlZ0V4cC5wcm90b3R5cGUudG9TdHJpbmcuY2FsbCh2YWx1ZSksICdyZWdleHAnKTtcbiAgICB9XG4gICAgaWYgKGlzRGF0ZSh2YWx1ZSkpIHtcbiAgICAgIHJldHVybiBjdHguc3R5bGl6ZShEYXRlLnByb3RvdHlwZS50b1N0cmluZy5jYWxsKHZhbHVlKSwgJ2RhdGUnKTtcbiAgICB9XG4gICAgaWYgKGlzRXJyb3IodmFsdWUpKSB7XG4gICAgICByZXR1cm4gZm9ybWF0RXJyb3IodmFsdWUpO1xuICAgIH1cbiAgfVxuXG4gIHZhciBiYXNlID0gJycsIGFycmF5ID0gZmFsc2UsIGJyYWNlcyA9IFsneycsICd9J107XG5cbiAgLy8gTWFrZSBBcnJheSBzYXkgdGhhdCB0aGV5IGFyZSBBcnJheVxuICBpZiAoaXNBcnJheSh2YWx1ZSkpIHtcbiAgICBhcnJheSA9IHRydWU7XG4gICAgYnJhY2VzID0gWydbJywgJ10nXTtcbiAgfVxuXG4gIC8vIE1ha2UgZnVuY3Rpb25zIHNheSB0aGF0IHRoZXkgYXJlIGZ1bmN0aW9uc1xuICBpZiAoaXNGdW5jdGlvbih2YWx1ZSkpIHtcbiAgICB2YXIgbiA9IHZhbHVlLm5hbWUgPyAnOiAnICsgdmFsdWUubmFtZSA6ICcnO1xuICAgIGJhc2UgPSAnIFtGdW5jdGlvbicgKyBuICsgJ10nO1xuICB9XG5cbiAgLy8gTWFrZSBSZWdFeHBzIHNheSB0aGF0IHRoZXkgYXJlIFJlZ0V4cHNcbiAgaWYgKGlzUmVnRXhwKHZhbHVlKSkge1xuICAgIGJhc2UgPSAnICcgKyBSZWdFeHAucHJvdG90eXBlLnRvU3RyaW5nLmNhbGwodmFsdWUpO1xuICB9XG5cbiAgLy8gTWFrZSBkYXRlcyB3aXRoIHByb3BlcnRpZXMgZmlyc3Qgc2F5IHRoZSBkYXRlXG4gIGlmIChpc0RhdGUodmFsdWUpKSB7XG4gICAgYmFzZSA9ICcgJyArIERhdGUucHJvdG90eXBlLnRvVVRDU3RyaW5nLmNhbGwodmFsdWUpO1xuICB9XG5cbiAgLy8gTWFrZSBlcnJvciB3aXRoIG1lc3NhZ2UgZmlyc3Qgc2F5IHRoZSBlcnJvclxuICBpZiAoaXNFcnJvcih2YWx1ZSkpIHtcbiAgICBiYXNlID0gJyAnICsgZm9ybWF0RXJyb3IodmFsdWUpO1xuICB9XG5cbiAgaWYgKGtleXMubGVuZ3RoID09PSAwICYmICghYXJyYXkgfHwgdmFsdWUubGVuZ3RoID09IDApKSB7XG4gICAgcmV0dXJuIGJyYWNlc1swXSArIGJhc2UgKyBicmFjZXNbMV07XG4gIH1cblxuICBpZiAocmVjdXJzZVRpbWVzIDwgMCkge1xuICAgIGlmIChpc1JlZ0V4cCh2YWx1ZSkpIHtcbiAgICAgIHJldHVybiBjdHguc3R5bGl6ZShSZWdFeHAucHJvdG90eXBlLnRvU3RyaW5nLmNhbGwodmFsdWUpLCAncmVnZXhwJyk7XG4gICAgfSBlbHNlIHtcbiAgICAgIHJldHVybiBjdHguc3R5bGl6ZSgnW09iamVjdF0nLCAnc3BlY2lhbCcpO1xuICAgIH1cbiAgfVxuXG4gIGN0eC5zZWVuLnB1c2godmFsdWUpO1xuXG4gIHZhciBvdXRwdXQ7XG4gIGlmIChhcnJheSkge1xuICAgIG91dHB1dCA9IGZvcm1hdEFycmF5KGN0eCwgdmFsdWUsIHJlY3Vyc2VUaW1lcywgdmlzaWJsZUtleXMsIGtleXMpO1xuICB9IGVsc2Uge1xuICAgIG91dHB1dCA9IGtleXMubWFwKGZ1bmN0aW9uKGtleSkge1xuICAgICAgcmV0dXJuIGZvcm1hdFByb3BlcnR5KGN0eCwgdmFsdWUsIHJlY3Vyc2VUaW1lcywgdmlzaWJsZUtleXMsIGtleSwgYXJyYXkpO1xuICAgIH0pO1xuICB9XG5cbiAgY3R4LnNlZW4ucG9wKCk7XG5cbiAgcmV0dXJuIHJlZHVjZVRvU2luZ2xlU3RyaW5nKG91dHB1dCwgYmFzZSwgYnJhY2VzKTtcbn1cblxuXG5mdW5jdGlvbiBmb3JtYXRQcmltaXRpdmUoY3R4LCB2YWx1ZSkge1xuICBpZiAoaXNVbmRlZmluZWQodmFsdWUpKVxuICAgIHJldHVybiBjdHguc3R5bGl6ZSgndW5kZWZpbmVkJywgJ3VuZGVmaW5lZCcpO1xuICBpZiAoaXNTdHJpbmcodmFsdWUpKSB7XG4gICAgdmFyIHNpbXBsZSA9ICdcXCcnICsgSlNPTi5zdHJpbmdpZnkodmFsdWUpLnJlcGxhY2UoL15cInxcIiQvZywgJycpXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAucmVwbGFjZSgvJy9nLCBcIlxcXFwnXCIpXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAucmVwbGFjZSgvXFxcXFwiL2csICdcIicpICsgJ1xcJyc7XG4gICAgcmV0dXJuIGN0eC5zdHlsaXplKHNpbXBsZSwgJ3N0cmluZycpO1xuICB9XG4gIGlmIChpc051bWJlcih2YWx1ZSkpXG4gICAgcmV0dXJuIGN0eC5zdHlsaXplKCcnICsgdmFsdWUsICdudW1iZXInKTtcbiAgaWYgKGlzQm9vbGVhbih2YWx1ZSkpXG4gICAgcmV0dXJuIGN0eC5zdHlsaXplKCcnICsgdmFsdWUsICdib29sZWFuJyk7XG4gIC8vIEZvciBzb21lIHJlYXNvbiB0eXBlb2YgbnVsbCBpcyBcIm9iamVjdFwiLCBzbyBzcGVjaWFsIGNhc2UgaGVyZS5cbiAgaWYgKGlzTnVsbCh2YWx1ZSkpXG4gICAgcmV0dXJuIGN0eC5zdHlsaXplKCdudWxsJywgJ251bGwnKTtcbn1cblxuXG5mdW5jdGlvbiBmb3JtYXRFcnJvcih2YWx1ZSkge1xuICByZXR1cm4gJ1snICsgRXJyb3IucHJvdG90eXBlLnRvU3RyaW5nLmNhbGwodmFsdWUpICsgJ10nO1xufVxuXG5cbmZ1bmN0aW9uIGZvcm1hdEFycmF5KGN0eCwgdmFsdWUsIHJlY3Vyc2VUaW1lcywgdmlzaWJsZUtleXMsIGtleXMpIHtcbiAgdmFyIG91dHB1dCA9IFtdO1xuICBmb3IgKHZhciBpID0gMCwgbCA9IHZhbHVlLmxlbmd0aDsgaSA8IGw7ICsraSkge1xuICAgIGlmIChoYXNPd25Qcm9wZXJ0eSh2YWx1ZSwgU3RyaW5nKGkpKSkge1xuICAgICAgb3V0cHV0LnB1c2goZm9ybWF0UHJvcGVydHkoY3R4LCB2YWx1ZSwgcmVjdXJzZVRpbWVzLCB2aXNpYmxlS2V5cyxcbiAgICAgICAgICBTdHJpbmcoaSksIHRydWUpKTtcbiAgICB9IGVsc2Uge1xuICAgICAgb3V0cHV0LnB1c2goJycpO1xuICAgIH1cbiAgfVxuICBrZXlzLmZvckVhY2goZnVuY3Rpb24oa2V5KSB7XG4gICAgaWYgKCFrZXkubWF0Y2goL15cXGQrJC8pKSB7XG4gICAgICBvdXRwdXQucHVzaChmb3JtYXRQcm9wZXJ0eShjdHgsIHZhbHVlLCByZWN1cnNlVGltZXMsIHZpc2libGVLZXlzLFxuICAgICAgICAgIGtleSwgdHJ1ZSkpO1xuICAgIH1cbiAgfSk7XG4gIHJldHVybiBvdXRwdXQ7XG59XG5cblxuZnVuY3Rpb24gZm9ybWF0UHJvcGVydHkoY3R4LCB2YWx1ZSwgcmVjdXJzZVRpbWVzLCB2aXNpYmxlS2V5cywga2V5LCBhcnJheSkge1xuICB2YXIgbmFtZSwgc3RyLCBkZXNjO1xuICBkZXNjID0gT2JqZWN0LmdldE93blByb3BlcnR5RGVzY3JpcHRvcih2YWx1ZSwga2V5KSB8fCB7IHZhbHVlOiB2YWx1ZVtrZXldIH07XG4gIGlmIChkZXNjLmdldCkge1xuICAgIGlmIChkZXNjLnNldCkge1xuICAgICAgc3RyID0gY3R4LnN0eWxpemUoJ1tHZXR0ZXIvU2V0dGVyXScsICdzcGVjaWFsJyk7XG4gICAgfSBlbHNlIHtcbiAgICAgIHN0ciA9IGN0eC5zdHlsaXplKCdbR2V0dGVyXScsICdzcGVjaWFsJyk7XG4gICAgfVxuICB9IGVsc2Uge1xuICAgIGlmIChkZXNjLnNldCkge1xuICAgICAgc3RyID0gY3R4LnN0eWxpemUoJ1tTZXR0ZXJdJywgJ3NwZWNpYWwnKTtcbiAgICB9XG4gIH1cbiAgaWYgKCFoYXNPd25Qcm9wZXJ0eSh2aXNpYmxlS2V5cywga2V5KSkge1xuICAgIG5hbWUgPSAnWycgKyBrZXkgKyAnXSc7XG4gIH1cbiAgaWYgKCFzdHIpIHtcbiAgICBpZiAoY3R4LnNlZW4uaW5kZXhPZihkZXNjLnZhbHVlKSA8IDApIHtcbiAgICAgIGlmIChpc051bGwocmVjdXJzZVRpbWVzKSkge1xuICAgICAgICBzdHIgPSBmb3JtYXRWYWx1ZShjdHgsIGRlc2MudmFsdWUsIG51bGwpO1xuICAgICAgfSBlbHNlIHtcbiAgICAgICAgc3RyID0gZm9ybWF0VmFsdWUoY3R4LCBkZXNjLnZhbHVlLCByZWN1cnNlVGltZXMgLSAxKTtcbiAgICAgIH1cbiAgICAgIGlmIChzdHIuaW5kZXhPZignXFxuJykgPiAtMSkge1xuICAgICAgICBpZiAoYXJyYXkpIHtcbiAgICAgICAgICBzdHIgPSBzdHIuc3BsaXQoJ1xcbicpLm1hcChmdW5jdGlvbihsaW5lKSB7XG4gICAgICAgICAgICByZXR1cm4gJyAgJyArIGxpbmU7XG4gICAgICAgICAgfSkuam9pbignXFxuJykuc3Vic3RyKDIpO1xuICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgIHN0ciA9ICdcXG4nICsgc3RyLnNwbGl0KCdcXG4nKS5tYXAoZnVuY3Rpb24obGluZSkge1xuICAgICAgICAgICAgcmV0dXJuICcgICAnICsgbGluZTtcbiAgICAgICAgICB9KS5qb2luKCdcXG4nKTtcbiAgICAgICAgfVxuICAgICAgfVxuICAgIH0gZWxzZSB7XG4gICAgICBzdHIgPSBjdHguc3R5bGl6ZSgnW0NpcmN1bGFyXScsICdzcGVjaWFsJyk7XG4gICAgfVxuICB9XG4gIGlmIChpc1VuZGVmaW5lZChuYW1lKSkge1xuICAgIGlmIChhcnJheSAmJiBrZXkubWF0Y2goL15cXGQrJC8pKSB7XG4gICAgICByZXR1cm4gc3RyO1xuICAgIH1cbiAgICBuYW1lID0gSlNPTi5zdHJpbmdpZnkoJycgKyBrZXkpO1xuICAgIGlmIChuYW1lLm1hdGNoKC9eXCIoW2EtekEtWl9dW2EtekEtWl8wLTldKilcIiQvKSkge1xuICAgICAgbmFtZSA9IG5hbWUuc3Vic3RyKDEsIG5hbWUubGVuZ3RoIC0gMik7XG4gICAgICBuYW1lID0gY3R4LnN0eWxpemUobmFtZSwgJ25hbWUnKTtcbiAgICB9IGVsc2Uge1xuICAgICAgbmFtZSA9IG5hbWUucmVwbGFjZSgvJy9nLCBcIlxcXFwnXCIpXG4gICAgICAgICAgICAgICAgIC5yZXBsYWNlKC9cXFxcXCIvZywgJ1wiJylcbiAgICAgICAgICAgICAgICAgLnJlcGxhY2UoLyheXCJ8XCIkKS9nLCBcIidcIik7XG4gICAgICBuYW1lID0gY3R4LnN0eWxpemUobmFtZSwgJ3N0cmluZycpO1xuICAgIH1cbiAgfVxuXG4gIHJldHVybiBuYW1lICsgJzogJyArIHN0cjtcbn1cblxuXG5mdW5jdGlvbiByZWR1Y2VUb1NpbmdsZVN0cmluZyhvdXRwdXQsIGJhc2UsIGJyYWNlcykge1xuICB2YXIgbnVtTGluZXNFc3QgPSAwO1xuICB2YXIgbGVuZ3RoID0gb3V0cHV0LnJlZHVjZShmdW5jdGlvbihwcmV2LCBjdXIpIHtcbiAgICBudW1MaW5lc0VzdCsrO1xuICAgIGlmIChjdXIuaW5kZXhPZignXFxuJykgPj0gMCkgbnVtTGluZXNFc3QrKztcbiAgICByZXR1cm4gcHJldiArIGN1ci5yZXBsYWNlKC9cXHUwMDFiXFxbXFxkXFxkP20vZywgJycpLmxlbmd0aCArIDE7XG4gIH0sIDApO1xuXG4gIGlmIChsZW5ndGggPiA2MCkge1xuICAgIHJldHVybiBicmFjZXNbMF0gK1xuICAgICAgICAgICAoYmFzZSA9PT0gJycgPyAnJyA6IGJhc2UgKyAnXFxuICcpICtcbiAgICAgICAgICAgJyAnICtcbiAgICAgICAgICAgb3V0cHV0LmpvaW4oJyxcXG4gICcpICtcbiAgICAgICAgICAgJyAnICtcbiAgICAgICAgICAgYnJhY2VzWzFdO1xuICB9XG5cbiAgcmV0dXJuIGJyYWNlc1swXSArIGJhc2UgKyAnICcgKyBvdXRwdXQuam9pbignLCAnKSArICcgJyArIGJyYWNlc1sxXTtcbn1cblxuXG4vLyBOT1RFOiBUaGVzZSB0eXBlIGNoZWNraW5nIGZ1bmN0aW9ucyBpbnRlbnRpb25hbGx5IGRvbid0IHVzZSBgaW5zdGFuY2VvZmBcbi8vIGJlY2F1c2UgaXQgaXMgZnJhZ2lsZSBhbmQgY2FuIGJlIGVhc2lseSBmYWtlZCB3aXRoIGBPYmplY3QuY3JlYXRlKClgLlxuZnVuY3Rpb24gaXNBcnJheShhcikge1xuICByZXR1cm4gQXJyYXkuaXNBcnJheShhcik7XG59XG5leHBvcnRzLmlzQXJyYXkgPSBpc0FycmF5O1xuXG5mdW5jdGlvbiBpc0Jvb2xlYW4oYXJnKSB7XG4gIHJldHVybiB0eXBlb2YgYXJnID09PSAnYm9vbGVhbic7XG59XG5leHBvcnRzLmlzQm9vbGVhbiA9IGlzQm9vbGVhbjtcblxuZnVuY3Rpb24gaXNOdWxsKGFyZykge1xuICByZXR1cm4gYXJnID09PSBudWxsO1xufVxuZXhwb3J0cy5pc051bGwgPSBpc051bGw7XG5cbmZ1bmN0aW9uIGlzTnVsbE9yVW5kZWZpbmVkKGFyZykge1xuICByZXR1cm4gYXJnID09IG51bGw7XG59XG5leHBvcnRzLmlzTnVsbE9yVW5kZWZpbmVkID0gaXNOdWxsT3JVbmRlZmluZWQ7XG5cbmZ1bmN0aW9uIGlzTnVtYmVyKGFyZykge1xuICByZXR1cm4gdHlwZW9mIGFyZyA9PT0gJ251bWJlcic7XG59XG5leHBvcnRzLmlzTnVtYmVyID0gaXNOdW1iZXI7XG5cbmZ1bmN0aW9uIGlzU3RyaW5nKGFyZykge1xuICByZXR1cm4gdHlwZW9mIGFyZyA9PT0gJ3N0cmluZyc7XG59XG5leHBvcnRzLmlzU3RyaW5nID0gaXNTdHJpbmc7XG5cbmZ1bmN0aW9uIGlzU3ltYm9sKGFyZykge1xuICByZXR1cm4gdHlwZW9mIGFyZyA9PT0gJ3N5bWJvbCc7XG59XG5leHBvcnRzLmlzU3ltYm9sID0gaXNTeW1ib2w7XG5cbmZ1bmN0aW9uIGlzVW5kZWZpbmVkKGFyZykge1xuICByZXR1cm4gYXJnID09PSB2b2lkIDA7XG59XG5leHBvcnRzLmlzVW5kZWZpbmVkID0gaXNVbmRlZmluZWQ7XG5cbmZ1bmN0aW9uIGlzUmVnRXhwKHJlKSB7XG4gIHJldHVybiBpc09iamVjdChyZSkgJiYgb2JqZWN0VG9TdHJpbmcocmUpID09PSAnW29iamVjdCBSZWdFeHBdJztcbn1cbmV4cG9ydHMuaXNSZWdFeHAgPSBpc1JlZ0V4cDtcblxuZnVuY3Rpb24gaXNPYmplY3QoYXJnKSB7XG4gIHJldHVybiB0eXBlb2YgYXJnID09PSAnb2JqZWN0JyAmJiBhcmcgIT09IG51bGw7XG59XG5leHBvcnRzLmlzT2JqZWN0ID0gaXNPYmplY3Q7XG5cbmZ1bmN0aW9uIGlzRGF0ZShkKSB7XG4gIHJldHVybiBpc09iamVjdChkKSAmJiBvYmplY3RUb1N0cmluZyhkKSA9PT0gJ1tvYmplY3QgRGF0ZV0nO1xufVxuZXhwb3J0cy5pc0RhdGUgPSBpc0RhdGU7XG5cbmZ1bmN0aW9uIGlzRXJyb3IoZSkge1xuICByZXR1cm4gaXNPYmplY3QoZSkgJiZcbiAgICAgIChvYmplY3RUb1N0cmluZyhlKSA9PT0gJ1tvYmplY3QgRXJyb3JdJyB8fCBlIGluc3RhbmNlb2YgRXJyb3IpO1xufVxuZXhwb3J0cy5pc0Vycm9yID0gaXNFcnJvcjtcblxuZnVuY3Rpb24gaXNGdW5jdGlvbihhcmcpIHtcbiAgcmV0dXJuIHR5cGVvZiBhcmcgPT09ICdmdW5jdGlvbic7XG59XG5leHBvcnRzLmlzRnVuY3Rpb24gPSBpc0Z1bmN0aW9uO1xuXG5mdW5jdGlvbiBpc1ByaW1pdGl2ZShhcmcpIHtcbiAgcmV0dXJuIGFyZyA9PT0gbnVsbCB8fFxuICAgICAgICAgdHlwZW9mIGFyZyA9PT0gJ2Jvb2xlYW4nIHx8XG4gICAgICAgICB0eXBlb2YgYXJnID09PSAnbnVtYmVyJyB8fFxuICAgICAgICAgdHlwZW9mIGFyZyA9PT0gJ3N0cmluZycgfHxcbiAgICAgICAgIHR5cGVvZiBhcmcgPT09ICdzeW1ib2wnIHx8ICAvLyBFUzYgc3ltYm9sXG4gICAgICAgICB0eXBlb2YgYXJnID09PSAndW5kZWZpbmVkJztcbn1cbmV4cG9ydHMuaXNQcmltaXRpdmUgPSBpc1ByaW1pdGl2ZTtcblxuZXhwb3J0cy5pc0J1ZmZlciA9IF9kZXJlcV8oJy4vc3VwcG9ydC9pc0J1ZmZlcicpO1xuXG5mdW5jdGlvbiBvYmplY3RUb1N0cmluZyhvKSB7XG4gIHJldHVybiBPYmplY3QucHJvdG90eXBlLnRvU3RyaW5nLmNhbGwobyk7XG59XG5cblxuZnVuY3Rpb24gcGFkKG4pIHtcbiAgcmV0dXJuIG4gPCAxMCA/ICcwJyArIG4udG9TdHJpbmcoMTApIDogbi50b1N0cmluZygxMCk7XG59XG5cblxudmFyIG1vbnRocyA9IFsnSmFuJywgJ0ZlYicsICdNYXInLCAnQXByJywgJ01heScsICdKdW4nLCAnSnVsJywgJ0F1ZycsICdTZXAnLFxuICAgICAgICAgICAgICAnT2N0JywgJ05vdicsICdEZWMnXTtcblxuLy8gMjYgRmViIDE2OjE5OjM0XG5mdW5jdGlvbiB0aW1lc3RhbXAoKSB7XG4gIHZhciBkID0gbmV3IERhdGUoKTtcbiAgdmFyIHRpbWUgPSBbcGFkKGQuZ2V0SG91cnMoKSksXG4gICAgICAgICAgICAgIHBhZChkLmdldE1pbnV0ZXMoKSksXG4gICAgICAgICAgICAgIHBhZChkLmdldFNlY29uZHMoKSldLmpvaW4oJzonKTtcbiAgcmV0dXJuIFtkLmdldERhdGUoKSwgbW9udGhzW2QuZ2V0TW9udGgoKV0sIHRpbWVdLmpvaW4oJyAnKTtcbn1cblxuXG4vLyBsb2cgaXMganVzdCBhIHRoaW4gd3JhcHBlciB0byBjb25zb2xlLmxvZyB0aGF0IHByZXBlbmRzIGEgdGltZXN0YW1wXG5leHBvcnRzLmxvZyA9IGZ1bmN0aW9uKCkge1xuICBjb25zb2xlLmxvZygnJXMgLSAlcycsIHRpbWVzdGFtcCgpLCBleHBvcnRzLmZvcm1hdC5hcHBseShleHBvcnRzLCBhcmd1bWVudHMpKTtcbn07XG5cblxuLyoqXG4gKiBJbmhlcml0IHRoZSBwcm90b3R5cGUgbWV0aG9kcyBmcm9tIG9uZSBjb25zdHJ1Y3RvciBpbnRvIGFub3RoZXIuXG4gKlxuICogVGhlIEZ1bmN0aW9uLnByb3RvdHlwZS5pbmhlcml0cyBmcm9tIGxhbmcuanMgcmV3cml0dGVuIGFzIGEgc3RhbmRhbG9uZVxuICogZnVuY3Rpb24gKG5vdCBvbiBGdW5jdGlvbi5wcm90b3R5cGUpLiBOT1RFOiBJZiB0aGlzIGZpbGUgaXMgdG8gYmUgbG9hZGVkXG4gKiBkdXJpbmcgYm9vdHN0cmFwcGluZyB0aGlzIGZ1bmN0aW9uIG5lZWRzIHRvIGJlIHJld3JpdHRlbiB1c2luZyBzb21lIG5hdGl2ZVxuICogZnVuY3Rpb25zIGFzIHByb3RvdHlwZSBzZXR1cCB1c2luZyBub3JtYWwgSmF2YVNjcmlwdCBkb2VzIG5vdCB3b3JrIGFzXG4gKiBleHBlY3RlZCBkdXJpbmcgYm9vdHN0cmFwcGluZyAoc2VlIG1pcnJvci5qcyBpbiByMTE0OTAzKS5cbiAqXG4gKiBAcGFyYW0ge2Z1bmN0aW9ufSBjdG9yIENvbnN0cnVjdG9yIGZ1bmN0aW9uIHdoaWNoIG5lZWRzIHRvIGluaGVyaXQgdGhlXG4gKiAgICAgcHJvdG90eXBlLlxuICogQHBhcmFtIHtmdW5jdGlvbn0gc3VwZXJDdG9yIENvbnN0cnVjdG9yIGZ1bmN0aW9uIHRvIGluaGVyaXQgcHJvdG90eXBlIGZyb20uXG4gKi9cbmV4cG9ydHMuaW5oZXJpdHMgPSBfZGVyZXFfKCdpbmhlcml0cycpO1xuXG5leHBvcnRzLl9leHRlbmQgPSBmdW5jdGlvbihvcmlnaW4sIGFkZCkge1xuICAvLyBEb24ndCBkbyBhbnl0aGluZyBpZiBhZGQgaXNuJ3QgYW4gb2JqZWN0XG4gIGlmICghYWRkIHx8ICFpc09iamVjdChhZGQpKSByZXR1cm4gb3JpZ2luO1xuXG4gIHZhciBrZXlzID0gT2JqZWN0LmtleXMoYWRkKTtcbiAgdmFyIGkgPSBrZXlzLmxlbmd0aDtcbiAgd2hpbGUgKGktLSkge1xuICAgIG9yaWdpbltrZXlzW2ldXSA9IGFkZFtrZXlzW2ldXTtcbiAgfVxuICByZXR1cm4gb3JpZ2luO1xufTtcblxuZnVuY3Rpb24gaGFzT3duUHJvcGVydHkob2JqLCBwcm9wKSB7XG4gIHJldHVybiBPYmplY3QucHJvdG90eXBlLmhhc093blByb3BlcnR5LmNhbGwob2JqLCBwcm9wKTtcbn1cblxufSkuY2FsbCh0aGlzLF9kZXJlcV8oJ19wcm9jZXNzJyksdHlwZW9mIGdsb2JhbCAhPT0gXCJ1bmRlZmluZWRcIiA/IGdsb2JhbCA6IHR5cGVvZiBzZWxmICE9PSBcInVuZGVmaW5lZFwiID8gc2VsZiA6IHR5cGVvZiB3aW5kb3cgIT09IFwidW5kZWZpbmVkXCIgPyB3aW5kb3cgOiB7fSlcbn0se1wiLi9zdXBwb3J0L2lzQnVmZmVyXCI6NCxcIl9wcm9jZXNzXCI6MyxcImluaGVyaXRzXCI6Mn1dLDY6W2Z1bmN0aW9uKF9kZXJlcV8sbW9kdWxlLGV4cG9ydHMpe1xuLy8gQSByZWN1cnNpdmUgZGVzY2VudCBwYXJzZXIgb3BlcmF0ZXMgYnkgZGVmaW5pbmcgZnVuY3Rpb25zIGZvciBhbGxcbi8vIHN5bnRhY3RpYyBlbGVtZW50cywgYW5kIHJlY3Vyc2l2ZWx5IGNhbGxpbmcgdGhvc2UsIGVhY2ggZnVuY3Rpb25cbi8vIGFkdmFuY2luZyB0aGUgaW5wdXQgc3RyZWFtIGFuZCByZXR1cm5pbmcgYW4gQVNUIG5vZGUuIFByZWNlZGVuY2Vcbi8vIG9mIGNvbnN0cnVjdHMgKGZvciBleGFtcGxlLCB0aGUgZmFjdCB0aGF0IGAheFsxXWAgbWVhbnMgYCEoeFsxXSlgXG4vLyBpbnN0ZWFkIG9mIGAoIXgpWzFdYCBpcyBoYW5kbGVkIGJ5IHRoZSBmYWN0IHRoYXQgdGhlIHBhcnNlclxuLy8gZnVuY3Rpb24gdGhhdCBwYXJzZXMgdW5hcnkgcHJlZml4IG9wZXJhdG9ycyBpcyBjYWxsZWQgZmlyc3QsIGFuZFxuLy8gaW4gdHVybiBjYWxscyB0aGUgZnVuY3Rpb24gdGhhdCBwYXJzZXMgYFtdYCBzdWJzY3JpcHRzIOKAlCB0aGF0XG4vLyB3YXksIGl0J2xsIHJlY2VpdmUgdGhlIG5vZGUgZm9yIGB4WzFdYCBhbHJlYWR5IHBhcnNlZCwgYW5kIHdyYXBzXG4vLyAqdGhhdCogaW4gdGhlIHVuYXJ5IG9wZXJhdG9yIG5vZGUuXG4vL1xuLy8gQWNvcm4gdXNlcyBhbiBbb3BlcmF0b3IgcHJlY2VkZW5jZSBwYXJzZXJdW29wcF0gdG8gaGFuZGxlIGJpbmFyeVxuLy8gb3BlcmF0b3IgcHJlY2VkZW5jZSwgYmVjYXVzZSBpdCBpcyBtdWNoIG1vcmUgY29tcGFjdCB0aGFuIHVzaW5nXG4vLyB0aGUgdGVjaG5pcXVlIG91dGxpbmVkIGFib3ZlLCB3aGljaCB1c2VzIGRpZmZlcmVudCwgbmVzdGluZ1xuLy8gZnVuY3Rpb25zIHRvIHNwZWNpZnkgcHJlY2VkZW5jZSwgZm9yIGFsbCBvZiB0aGUgdGVuIGJpbmFyeVxuLy8gcHJlY2VkZW5jZSBsZXZlbHMgdGhhdCBKYXZhU2NyaXB0IGRlZmluZXMuXG4vL1xuLy8gW29wcF06IGh0dHA6Ly9lbi53aWtpcGVkaWEub3JnL3dpa2kvT3BlcmF0b3ItcHJlY2VkZW5jZV9wYXJzZXJcblxuXCJ1c2Ugc3RyaWN0XCI7XG5cbnZhciB0dCA9IF9kZXJlcV8oXCIuL3Rva2VudHlwZVwiKS50eXBlcztcblxudmFyIFBhcnNlciA9IF9kZXJlcV8oXCIuL3N0YXRlXCIpLlBhcnNlcjtcblxudmFyIHJlc2VydmVkV29yZHMgPSBfZGVyZXFfKFwiLi9pZGVudGlmaWVyXCIpLnJlc2VydmVkV29yZHM7XG5cbnZhciBoYXMgPSBfZGVyZXFfKFwiLi91dGlsXCIpLmhhcztcblxudmFyIHBwID0gUGFyc2VyLnByb3RvdHlwZTtcblxuLy8gQ2hlY2sgaWYgcHJvcGVydHkgbmFtZSBjbGFzaGVzIHdpdGggYWxyZWFkeSBhZGRlZC5cbi8vIE9iamVjdC9jbGFzcyBnZXR0ZXJzIGFuZCBzZXR0ZXJzIGFyZSBub3QgYWxsb3dlZCB0byBjbGFzaCDigJRcbi8vIGVpdGhlciB3aXRoIGVhY2ggb3RoZXIgb3Igd2l0aCBhbiBpbml0IHByb3BlcnR5IOKAlCBhbmQgaW5cbi8vIHN0cmljdCBtb2RlLCBpbml0IHByb3BlcnRpZXMgYXJlIGFsc28gbm90IGFsbG93ZWQgdG8gYmUgcmVwZWF0ZWQuXG5cbnBwLmNoZWNrUHJvcENsYXNoID0gZnVuY3Rpb24gKHByb3AsIHByb3BIYXNoKSB7XG4gIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNikgcmV0dXJuO1xuICB2YXIga2V5ID0gcHJvcC5rZXksXG4gICAgICBuYW1lID0gdW5kZWZpbmVkO1xuICBzd2l0Y2ggKGtleS50eXBlKSB7XG4gICAgY2FzZSBcIklkZW50aWZpZXJcIjpcbiAgICAgIG5hbWUgPSBrZXkubmFtZTticmVhaztcbiAgICBjYXNlIFwiTGl0ZXJhbFwiOlxuICAgICAgbmFtZSA9IFN0cmluZyhrZXkudmFsdWUpO2JyZWFrO1xuICAgIGRlZmF1bHQ6XG4gICAgICByZXR1cm47XG4gIH1cbiAgdmFyIGtpbmQgPSBwcm9wLmtpbmQgfHwgXCJpbml0XCIsXG4gICAgICBvdGhlciA9IHVuZGVmaW5lZDtcbiAgaWYgKGhhcyhwcm9wSGFzaCwgbmFtZSkpIHtcbiAgICBvdGhlciA9IHByb3BIYXNoW25hbWVdO1xuICAgIHZhciBpc0dldFNldCA9IGtpbmQgIT09IFwiaW5pdFwiO1xuICAgIGlmICgodGhpcy5zdHJpY3QgfHwgaXNHZXRTZXQpICYmIG90aGVyW2tpbmRdIHx8ICEoaXNHZXRTZXQgXiBvdGhlci5pbml0KSkgdGhpcy5yYWlzZShrZXkuc3RhcnQsIFwiUmVkZWZpbml0aW9uIG9mIHByb3BlcnR5XCIpO1xuICB9IGVsc2Uge1xuICAgIG90aGVyID0gcHJvcEhhc2hbbmFtZV0gPSB7XG4gICAgICBpbml0OiBmYWxzZSxcbiAgICAgIGdldDogZmFsc2UsXG4gICAgICBzZXQ6IGZhbHNlXG4gICAgfTtcbiAgfVxuICBvdGhlcltraW5kXSA9IHRydWU7XG59O1xuXG4vLyAjIyMgRXhwcmVzc2lvbiBwYXJzaW5nXG5cbi8vIFRoZXNlIG5lc3QsIGZyb20gdGhlIG1vc3QgZ2VuZXJhbCBleHByZXNzaW9uIHR5cGUgYXQgdGhlIHRvcCB0b1xuLy8gJ2F0b21pYycsIG5vbmRpdmlzaWJsZSBleHByZXNzaW9uIHR5cGVzIGF0IHRoZSBib3R0b20uIE1vc3Qgb2Zcbi8vIHRoZSBmdW5jdGlvbnMgd2lsbCBzaW1wbHkgbGV0IHRoZSBmdW5jdGlvbihzKSBiZWxvdyB0aGVtIHBhcnNlLFxuLy8gYW5kLCAqaWYqIHRoZSBzeW50YWN0aWMgY29uc3RydWN0IHRoZXkgaGFuZGxlIGlzIHByZXNlbnQsIHdyYXBcbi8vIHRoZSBBU1Qgbm9kZSB0aGF0IHRoZSBpbm5lciBwYXJzZXIgZ2F2ZSB0aGVtIGluIGFub3RoZXIgbm9kZS5cblxuLy8gUGFyc2UgYSBmdWxsIGV4cHJlc3Npb24uIFRoZSBvcHRpb25hbCBhcmd1bWVudHMgYXJlIHVzZWQgdG9cbi8vIGZvcmJpZCB0aGUgYGluYCBvcGVyYXRvciAoaW4gZm9yIGxvb3BzIGluaXRhbGl6YXRpb24gZXhwcmVzc2lvbnMpXG4vLyBhbmQgcHJvdmlkZSByZWZlcmVuY2UgZm9yIHN0b3JpbmcgJz0nIG9wZXJhdG9yIGluc2lkZSBzaG9ydGhhbmRcbi8vIHByb3BlcnR5IGFzc2lnbm1lbnQgaW4gY29udGV4dHMgd2hlcmUgYm90aCBvYmplY3QgZXhwcmVzc2lvblxuLy8gYW5kIG9iamVjdCBwYXR0ZXJuIG1pZ2h0IGFwcGVhciAoc28gaXQncyBwb3NzaWJsZSB0byByYWlzZVxuLy8gZGVsYXllZCBzeW50YXggZXJyb3IgYXQgY29ycmVjdCBwb3NpdGlvbikuXG5cbnBwLnBhcnNlRXhwcmVzc2lvbiA9IGZ1bmN0aW9uIChub0luLCByZWZTaG9ydGhhbmREZWZhdWx0UG9zKSB7XG4gIHZhciBzdGFydFBvcyA9IHRoaXMuc3RhcnQsXG4gICAgICBzdGFydExvYyA9IHRoaXMuc3RhcnRMb2M7XG4gIHZhciBleHByID0gdGhpcy5wYXJzZU1heWJlQXNzaWduKG5vSW4sIHJlZlNob3J0aGFuZERlZmF1bHRQb3MpO1xuICBpZiAodGhpcy50eXBlID09PSB0dC5jb21tYSkge1xuICAgIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGVBdChzdGFydFBvcywgc3RhcnRMb2MpO1xuICAgIG5vZGUuZXhwcmVzc2lvbnMgPSBbZXhwcl07XG4gICAgd2hpbGUgKHRoaXMuZWF0KHR0LmNvbW1hKSkgbm9kZS5leHByZXNzaW9ucy5wdXNoKHRoaXMucGFyc2VNYXliZUFzc2lnbihub0luLCByZWZTaG9ydGhhbmREZWZhdWx0UG9zKSk7XG4gICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIlNlcXVlbmNlRXhwcmVzc2lvblwiKTtcbiAgfVxuICByZXR1cm4gZXhwcjtcbn07XG5cbi8vIFBhcnNlIGFuIGFzc2lnbm1lbnQgZXhwcmVzc2lvbi4gVGhpcyBpbmNsdWRlcyBhcHBsaWNhdGlvbnMgb2Zcbi8vIG9wZXJhdG9ycyBsaWtlIGArPWAuXG5cbnBwLnBhcnNlTWF5YmVBc3NpZ24gPSBmdW5jdGlvbiAobm9JbiwgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcywgYWZ0ZXJMZWZ0UGFyc2UpIHtcbiAgaWYgKHRoaXMudHlwZSA9PSB0dC5feWllbGQgJiYgdGhpcy5pbkdlbmVyYXRvcikgcmV0dXJuIHRoaXMucGFyc2VZaWVsZCgpO1xuXG4gIHZhciBmYWlsT25TaG9ydGhhbmRBc3NpZ24gPSB1bmRlZmluZWQ7XG4gIGlmICghcmVmU2hvcnRoYW5kRGVmYXVsdFBvcykge1xuICAgIHJlZlNob3J0aGFuZERlZmF1bHRQb3MgPSB7IHN0YXJ0OiAwIH07XG4gICAgZmFpbE9uU2hvcnRoYW5kQXNzaWduID0gdHJ1ZTtcbiAgfSBlbHNlIHtcbiAgICBmYWlsT25TaG9ydGhhbmRBc3NpZ24gPSBmYWxzZTtcbiAgfVxuICB2YXIgc3RhcnRQb3MgPSB0aGlzLnN0YXJ0LFxuICAgICAgc3RhcnRMb2MgPSB0aGlzLnN0YXJ0TG9jO1xuICBpZiAodGhpcy50eXBlID09IHR0LnBhcmVuTCB8fCB0aGlzLnR5cGUgPT0gdHQubmFtZSkgdGhpcy5wb3RlbnRpYWxBcnJvd0F0ID0gdGhpcy5zdGFydDtcbiAgdmFyIGxlZnQgPSB0aGlzLnBhcnNlTWF5YmVDb25kaXRpb25hbChub0luLCByZWZTaG9ydGhhbmREZWZhdWx0UG9zKTtcbiAgaWYgKGFmdGVyTGVmdFBhcnNlKSBsZWZ0ID0gYWZ0ZXJMZWZ0UGFyc2UuY2FsbCh0aGlzLCBsZWZ0LCBzdGFydFBvcywgc3RhcnRMb2MpO1xuICBpZiAodGhpcy50eXBlLmlzQXNzaWduKSB7XG4gICAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0UG9zLCBzdGFydExvYyk7XG4gICAgbm9kZS5vcGVyYXRvciA9IHRoaXMudmFsdWU7XG4gICAgbm9kZS5sZWZ0ID0gdGhpcy50eXBlID09PSB0dC5lcSA/IHRoaXMudG9Bc3NpZ25hYmxlKGxlZnQpIDogbGVmdDtcbiAgICByZWZTaG9ydGhhbmREZWZhdWx0UG9zLnN0YXJ0ID0gMDsgLy8gcmVzZXQgYmVjYXVzZSBzaG9ydGhhbmQgZGVmYXVsdCB3YXMgdXNlZCBjb3JyZWN0bHlcbiAgICB0aGlzLmNoZWNrTFZhbChsZWZ0KTtcbiAgICB0aGlzLm5leHQoKTtcbiAgICBub2RlLnJpZ2h0ID0gdGhpcy5wYXJzZU1heWJlQXNzaWduKG5vSW4pO1xuICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJBc3NpZ25tZW50RXhwcmVzc2lvblwiKTtcbiAgfSBlbHNlIGlmIChmYWlsT25TaG9ydGhhbmRBc3NpZ24gJiYgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcy5zdGFydCkge1xuICAgIHRoaXMudW5leHBlY3RlZChyZWZTaG9ydGhhbmREZWZhdWx0UG9zLnN0YXJ0KTtcbiAgfVxuICByZXR1cm4gbGVmdDtcbn07XG5cbi8vIFBhcnNlIGEgdGVybmFyeSBjb25kaXRpb25hbCAoYD86YCkgb3BlcmF0b3IuXG5cbnBwLnBhcnNlTWF5YmVDb25kaXRpb25hbCA9IGZ1bmN0aW9uIChub0luLCByZWZTaG9ydGhhbmREZWZhdWx0UG9zKSB7XG4gIHZhciBzdGFydFBvcyA9IHRoaXMuc3RhcnQsXG4gICAgICBzdGFydExvYyA9IHRoaXMuc3RhcnRMb2M7XG4gIHZhciBleHByID0gdGhpcy5wYXJzZUV4cHJPcHMobm9JbiwgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcyk7XG4gIGlmIChyZWZTaG9ydGhhbmREZWZhdWx0UG9zICYmIHJlZlNob3J0aGFuZERlZmF1bHRQb3Muc3RhcnQpIHJldHVybiBleHByO1xuICBpZiAodGhpcy5lYXQodHQucXVlc3Rpb24pKSB7XG4gICAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0UG9zLCBzdGFydExvYyk7XG4gICAgbm9kZS50ZXN0ID0gZXhwcjtcbiAgICBub2RlLmNvbnNlcXVlbnQgPSB0aGlzLnBhcnNlTWF5YmVBc3NpZ24oKTtcbiAgICB0aGlzLmV4cGVjdCh0dC5jb2xvbik7XG4gICAgbm9kZS5hbHRlcm5hdGUgPSB0aGlzLnBhcnNlTWF5YmVBc3NpZ24obm9Jbik7XG4gICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkNvbmRpdGlvbmFsRXhwcmVzc2lvblwiKTtcbiAgfVxuICByZXR1cm4gZXhwcjtcbn07XG5cbi8vIFN0YXJ0IHRoZSBwcmVjZWRlbmNlIHBhcnNlci5cblxucHAucGFyc2VFeHByT3BzID0gZnVuY3Rpb24gKG5vSW4sIHJlZlNob3J0aGFuZERlZmF1bHRQb3MpIHtcbiAgdmFyIHN0YXJ0UG9zID0gdGhpcy5zdGFydCxcbiAgICAgIHN0YXJ0TG9jID0gdGhpcy5zdGFydExvYztcbiAgdmFyIGV4cHIgPSB0aGlzLnBhcnNlTWF5YmVVbmFyeShyZWZTaG9ydGhhbmREZWZhdWx0UG9zKTtcbiAgaWYgKHJlZlNob3J0aGFuZERlZmF1bHRQb3MgJiYgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcy5zdGFydCkgcmV0dXJuIGV4cHI7XG4gIHJldHVybiB0aGlzLnBhcnNlRXhwck9wKGV4cHIsIHN0YXJ0UG9zLCBzdGFydExvYywgLTEsIG5vSW4pO1xufTtcblxuLy8gUGFyc2UgYmluYXJ5IG9wZXJhdG9ycyB3aXRoIHRoZSBvcGVyYXRvciBwcmVjZWRlbmNlIHBhcnNpbmdcbi8vIGFsZ29yaXRobS4gYGxlZnRgIGlzIHRoZSBsZWZ0LWhhbmQgc2lkZSBvZiB0aGUgb3BlcmF0b3IuXG4vLyBgbWluUHJlY2AgcHJvdmlkZXMgY29udGV4dCB0aGF0IGFsbG93cyB0aGUgZnVuY3Rpb24gdG8gc3RvcCBhbmRcbi8vIGRlZmVyIGZ1cnRoZXIgcGFyc2VyIHRvIG9uZSBvZiBpdHMgY2FsbGVycyB3aGVuIGl0IGVuY291bnRlcnMgYW5cbi8vIG9wZXJhdG9yIHRoYXQgaGFzIGEgbG93ZXIgcHJlY2VkZW5jZSB0aGFuIHRoZSBzZXQgaXQgaXMgcGFyc2luZy5cblxucHAucGFyc2VFeHByT3AgPSBmdW5jdGlvbiAobGVmdCwgbGVmdFN0YXJ0UG9zLCBsZWZ0U3RhcnRMb2MsIG1pblByZWMsIG5vSW4pIHtcbiAgdmFyIHByZWMgPSB0aGlzLnR5cGUuYmlub3A7XG4gIGlmIChBcnJheS5pc0FycmF5KGxlZnRTdGFydFBvcykpIHtcbiAgICBpZiAodGhpcy5vcHRpb25zLmxvY2F0aW9ucyAmJiBub0luID09PSB1bmRlZmluZWQpIHtcbiAgICAgIC8vIHNoaWZ0IGFyZ3VtZW50cyB0byBsZWZ0IGJ5IG9uZVxuICAgICAgbm9JbiA9IG1pblByZWM7XG4gICAgICBtaW5QcmVjID0gbGVmdFN0YXJ0TG9jO1xuICAgICAgLy8gZmxhdHRlbiBsZWZ0U3RhcnRQb3NcbiAgICAgIGxlZnRTdGFydExvYyA9IGxlZnRTdGFydFBvc1sxXTtcbiAgICAgIGxlZnRTdGFydFBvcyA9IGxlZnRTdGFydFBvc1swXTtcbiAgICB9XG4gIH1cbiAgaWYgKHByZWMgIT0gbnVsbCAmJiAoIW5vSW4gfHwgdGhpcy50eXBlICE9PSB0dC5faW4pKSB7XG4gICAgaWYgKHByZWMgPiBtaW5QcmVjKSB7XG4gICAgICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlQXQobGVmdFN0YXJ0UG9zLCBsZWZ0U3RhcnRMb2MpO1xuICAgICAgbm9kZS5sZWZ0ID0gbGVmdDtcbiAgICAgIG5vZGUub3BlcmF0b3IgPSB0aGlzLnZhbHVlO1xuICAgICAgdmFyIG9wID0gdGhpcy50eXBlO1xuICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICB2YXIgc3RhcnRQb3MgPSB0aGlzLnN0YXJ0LFxuICAgICAgICAgIHN0YXJ0TG9jID0gdGhpcy5zdGFydExvYztcbiAgICAgIG5vZGUucmlnaHQgPSB0aGlzLnBhcnNlRXhwck9wKHRoaXMucGFyc2VNYXliZVVuYXJ5KCksIHN0YXJ0UG9zLCBzdGFydExvYywgcHJlYywgbm9Jbik7XG4gICAgICB0aGlzLmZpbmlzaE5vZGUobm9kZSwgb3AgPT09IHR0LmxvZ2ljYWxPUiB8fCBvcCA9PT0gdHQubG9naWNhbEFORCA/IFwiTG9naWNhbEV4cHJlc3Npb25cIiA6IFwiQmluYXJ5RXhwcmVzc2lvblwiKTtcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlRXhwck9wKG5vZGUsIGxlZnRTdGFydFBvcywgbGVmdFN0YXJ0TG9jLCBtaW5QcmVjLCBub0luKTtcbiAgICB9XG4gIH1cbiAgcmV0dXJuIGxlZnQ7XG59O1xuXG4vLyBQYXJzZSB1bmFyeSBvcGVyYXRvcnMsIGJvdGggcHJlZml4IGFuZCBwb3N0Zml4LlxuXG5wcC5wYXJzZU1heWJlVW5hcnkgPSBmdW5jdGlvbiAocmVmU2hvcnRoYW5kRGVmYXVsdFBvcykge1xuICBpZiAodGhpcy50eXBlLnByZWZpeCkge1xuICAgIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGUoKSxcbiAgICAgICAgdXBkYXRlID0gdGhpcy50eXBlID09PSB0dC5pbmNEZWM7XG4gICAgbm9kZS5vcGVyYXRvciA9IHRoaXMudmFsdWU7XG4gICAgbm9kZS5wcmVmaXggPSB0cnVlO1xuICAgIHRoaXMubmV4dCgpO1xuICAgIG5vZGUuYXJndW1lbnQgPSB0aGlzLnBhcnNlTWF5YmVVbmFyeSgpO1xuICAgIGlmIChyZWZTaG9ydGhhbmREZWZhdWx0UG9zICYmIHJlZlNob3J0aGFuZERlZmF1bHRQb3Muc3RhcnQpIHRoaXMudW5leHBlY3RlZChyZWZTaG9ydGhhbmREZWZhdWx0UG9zLnN0YXJ0KTtcbiAgICBpZiAodXBkYXRlKSB0aGlzLmNoZWNrTFZhbChub2RlLmFyZ3VtZW50KTtlbHNlIGlmICh0aGlzLnN0cmljdCAmJiBub2RlLm9wZXJhdG9yID09PSBcImRlbGV0ZVwiICYmIG5vZGUuYXJndW1lbnQudHlwZSA9PT0gXCJJZGVudGlmaWVyXCIpIHRoaXMucmFpc2Uobm9kZS5zdGFydCwgXCJEZWxldGluZyBsb2NhbCB2YXJpYWJsZSBpbiBzdHJpY3QgbW9kZVwiKTtcbiAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIHVwZGF0ZSA/IFwiVXBkYXRlRXhwcmVzc2lvblwiIDogXCJVbmFyeUV4cHJlc3Npb25cIik7XG4gIH1cbiAgdmFyIHN0YXJ0UG9zID0gdGhpcy5zdGFydCxcbiAgICAgIHN0YXJ0TG9jID0gdGhpcy5zdGFydExvYztcbiAgdmFyIGV4cHIgPSB0aGlzLnBhcnNlRXhwclN1YnNjcmlwdHMocmVmU2hvcnRoYW5kRGVmYXVsdFBvcyk7XG4gIGlmIChyZWZTaG9ydGhhbmREZWZhdWx0UG9zICYmIHJlZlNob3J0aGFuZERlZmF1bHRQb3Muc3RhcnQpIHJldHVybiBleHByO1xuICB3aGlsZSAodGhpcy50eXBlLnBvc3RmaXggJiYgIXRoaXMuY2FuSW5zZXJ0U2VtaWNvbG9uKCkpIHtcbiAgICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlQXQoc3RhcnRQb3MsIHN0YXJ0TG9jKTtcbiAgICBub2RlLm9wZXJhdG9yID0gdGhpcy52YWx1ZTtcbiAgICBub2RlLnByZWZpeCA9IGZhbHNlO1xuICAgIG5vZGUuYXJndW1lbnQgPSBleHByO1xuICAgIHRoaXMuY2hlY2tMVmFsKGV4cHIpO1xuICAgIHRoaXMubmV4dCgpO1xuICAgIGV4cHIgPSB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJVcGRhdGVFeHByZXNzaW9uXCIpO1xuICB9XG4gIHJldHVybiBleHByO1xufTtcblxuLy8gUGFyc2UgY2FsbCwgZG90LCBhbmQgYFtdYC1zdWJzY3JpcHQgZXhwcmVzc2lvbnMuXG5cbnBwLnBhcnNlRXhwclN1YnNjcmlwdHMgPSBmdW5jdGlvbiAocmVmU2hvcnRoYW5kRGVmYXVsdFBvcykge1xuICB2YXIgc3RhcnRQb3MgPSB0aGlzLnN0YXJ0LFxuICAgICAgc3RhcnRMb2MgPSB0aGlzLnN0YXJ0TG9jO1xuICB2YXIgZXhwciA9IHRoaXMucGFyc2VFeHByQXRvbShyZWZTaG9ydGhhbmREZWZhdWx0UG9zKTtcbiAgaWYgKHJlZlNob3J0aGFuZERlZmF1bHRQb3MgJiYgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcy5zdGFydCkgcmV0dXJuIGV4cHI7XG4gIHJldHVybiB0aGlzLnBhcnNlU3Vic2NyaXB0cyhleHByLCBzdGFydFBvcywgc3RhcnRMb2MpO1xufTtcblxucHAucGFyc2VTdWJzY3JpcHRzID0gZnVuY3Rpb24gKGJhc2UsIHN0YXJ0UG9zLCBzdGFydExvYywgbm9DYWxscykge1xuICBpZiAoQXJyYXkuaXNBcnJheShzdGFydFBvcykpIHtcbiAgICBpZiAodGhpcy5vcHRpb25zLmxvY2F0aW9ucyAmJiBub0NhbGxzID09PSB1bmRlZmluZWQpIHtcbiAgICAgIC8vIHNoaWZ0IGFyZ3VtZW50cyB0byBsZWZ0IGJ5IG9uZVxuICAgICAgbm9DYWxscyA9IHN0YXJ0TG9jO1xuICAgICAgLy8gZmxhdHRlbiBzdGFydFBvc1xuICAgICAgc3RhcnRMb2MgPSBzdGFydFBvc1sxXTtcbiAgICAgIHN0YXJ0UG9zID0gc3RhcnRQb3NbMF07XG4gICAgfVxuICB9XG4gIGZvciAoOzspIHtcbiAgICBpZiAodGhpcy5lYXQodHQuZG90KSkge1xuICAgICAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0UG9zLCBzdGFydExvYyk7XG4gICAgICBub2RlLm9iamVjdCA9IGJhc2U7XG4gICAgICBub2RlLnByb3BlcnR5ID0gdGhpcy5wYXJzZUlkZW50KHRydWUpO1xuICAgICAgbm9kZS5jb21wdXRlZCA9IGZhbHNlO1xuICAgICAgYmFzZSA9IHRoaXMuZmluaXNoTm9kZShub2RlLCBcIk1lbWJlckV4cHJlc3Npb25cIik7XG4gICAgfSBlbHNlIGlmICh0aGlzLmVhdCh0dC5icmFja2V0TCkpIHtcbiAgICAgIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGVBdChzdGFydFBvcywgc3RhcnRMb2MpO1xuICAgICAgbm9kZS5vYmplY3QgPSBiYXNlO1xuICAgICAgbm9kZS5wcm9wZXJ0eSA9IHRoaXMucGFyc2VFeHByZXNzaW9uKCk7XG4gICAgICBub2RlLmNvbXB1dGVkID0gdHJ1ZTtcbiAgICAgIHRoaXMuZXhwZWN0KHR0LmJyYWNrZXRSKTtcbiAgICAgIGJhc2UgPSB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJNZW1iZXJFeHByZXNzaW9uXCIpO1xuICAgIH0gZWxzZSBpZiAoIW5vQ2FsbHMgJiYgdGhpcy5lYXQodHQucGFyZW5MKSkge1xuICAgICAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0UG9zLCBzdGFydExvYyk7XG4gICAgICBub2RlLmNhbGxlZSA9IGJhc2U7XG4gICAgICBub2RlLmFyZ3VtZW50cyA9IHRoaXMucGFyc2VFeHByTGlzdCh0dC5wYXJlblIsIGZhbHNlKTtcbiAgICAgIGJhc2UgPSB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJDYWxsRXhwcmVzc2lvblwiKTtcbiAgICB9IGVsc2UgaWYgKHRoaXMudHlwZSA9PT0gdHQuYmFja1F1b3RlKSB7XG4gICAgICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlQXQoc3RhcnRQb3MsIHN0YXJ0TG9jKTtcbiAgICAgIG5vZGUudGFnID0gYmFzZTtcbiAgICAgIG5vZGUucXVhc2kgPSB0aGlzLnBhcnNlVGVtcGxhdGUoKTtcbiAgICAgIGJhc2UgPSB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJUYWdnZWRUZW1wbGF0ZUV4cHJlc3Npb25cIik7XG4gICAgfSBlbHNlIHtcbiAgICAgIHJldHVybiBiYXNlO1xuICAgIH1cbiAgfVxufTtcblxuLy8gUGFyc2UgYW4gYXRvbWljIGV4cHJlc3Npb24g4oCUIGVpdGhlciBhIHNpbmdsZSB0b2tlbiB0aGF0IGlzIGFuXG4vLyBleHByZXNzaW9uLCBhbiBleHByZXNzaW9uIHN0YXJ0ZWQgYnkgYSBrZXl3b3JkIGxpa2UgYGZ1bmN0aW9uYCBvclxuLy8gYG5ld2AsIG9yIGFuIGV4cHJlc3Npb24gd3JhcHBlZCBpbiBwdW5jdHVhdGlvbiBsaWtlIGAoKWAsIGBbXWAsXG4vLyBvciBge31gLlxuXG5wcC5wYXJzZUV4cHJBdG9tID0gZnVuY3Rpb24gKHJlZlNob3J0aGFuZERlZmF1bHRQb3MpIHtcbiAgdmFyIG5vZGUgPSB1bmRlZmluZWQsXG4gICAgICBjYW5CZUFycm93ID0gdGhpcy5wb3RlbnRpYWxBcnJvd0F0ID09IHRoaXMuc3RhcnQ7XG4gIHN3aXRjaCAodGhpcy50eXBlKSB7XG4gICAgY2FzZSB0dC5fdGhpczpcbiAgICBjYXNlIHR0Ll9zdXBlcjpcbiAgICAgIHZhciB0eXBlID0gdGhpcy50eXBlID09PSB0dC5fdGhpcyA/IFwiVGhpc0V4cHJlc3Npb25cIiA6IFwiU3VwZXJcIjtcbiAgICAgIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIHR5cGUpO1xuXG4gICAgY2FzZSB0dC5feWllbGQ6XG4gICAgICBpZiAodGhpcy5pbkdlbmVyYXRvcikgdGhpcy51bmV4cGVjdGVkKCk7XG5cbiAgICBjYXNlIHR0Lm5hbWU6XG4gICAgICB2YXIgc3RhcnRQb3MgPSB0aGlzLnN0YXJ0LFxuICAgICAgICAgIHN0YXJ0TG9jID0gdGhpcy5zdGFydExvYztcbiAgICAgIHZhciBpZCA9IHRoaXMucGFyc2VJZGVudCh0aGlzLnR5cGUgIT09IHR0Lm5hbWUpO1xuICAgICAgaWYgKGNhbkJlQXJyb3cgJiYgIXRoaXMuY2FuSW5zZXJ0U2VtaWNvbG9uKCkgJiYgdGhpcy5lYXQodHQuYXJyb3cpKSByZXR1cm4gdGhpcy5wYXJzZUFycm93RXhwcmVzc2lvbih0aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0UG9zLCBzdGFydExvYyksIFtpZF0pO1xuICAgICAgcmV0dXJuIGlkO1xuXG4gICAgY2FzZSB0dC5yZWdleHA6XG4gICAgICB2YXIgdmFsdWUgPSB0aGlzLnZhbHVlO1xuICAgICAgbm9kZSA9IHRoaXMucGFyc2VMaXRlcmFsKHZhbHVlLnZhbHVlKTtcbiAgICAgIG5vZGUucmVnZXggPSB7IHBhdHRlcm46IHZhbHVlLnBhdHRlcm4sIGZsYWdzOiB2YWx1ZS5mbGFncyB9O1xuICAgICAgcmV0dXJuIG5vZGU7XG5cbiAgICBjYXNlIHR0Lm51bTpjYXNlIHR0LnN0cmluZzpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlTGl0ZXJhbCh0aGlzLnZhbHVlKTtcblxuICAgIGNhc2UgdHQuX251bGw6Y2FzZSB0dC5fdHJ1ZTpjYXNlIHR0Ll9mYWxzZTpcbiAgICAgIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICAgICAgbm9kZS52YWx1ZSA9IHRoaXMudHlwZSA9PT0gdHQuX251bGwgPyBudWxsIDogdGhpcy50eXBlID09PSB0dC5fdHJ1ZTtcbiAgICAgIG5vZGUucmF3ID0gdGhpcy50eXBlLmtleXdvcmQ7XG4gICAgICB0aGlzLm5leHQoKTtcbiAgICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJMaXRlcmFsXCIpO1xuXG4gICAgY2FzZSB0dC5wYXJlbkw6XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZVBhcmVuQW5kRGlzdGluZ3Vpc2hFeHByZXNzaW9uKGNhbkJlQXJyb3cpO1xuXG4gICAgY2FzZSB0dC5icmFja2V0TDpcbiAgICAgIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICAvLyBjaGVjayB3aGV0aGVyIHRoaXMgaXMgYXJyYXkgY29tcHJlaGVuc2lvbiBvciByZWd1bGFyIGFycmF5XG4gICAgICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDcgJiYgdGhpcy50eXBlID09PSB0dC5fZm9yKSB7XG4gICAgICAgIHJldHVybiB0aGlzLnBhcnNlQ29tcHJlaGVuc2lvbihub2RlLCBmYWxzZSk7XG4gICAgICB9XG4gICAgICBub2RlLmVsZW1lbnRzID0gdGhpcy5wYXJzZUV4cHJMaXN0KHR0LmJyYWNrZXRSLCB0cnVlLCB0cnVlLCByZWZTaG9ydGhhbmREZWZhdWx0UG9zKTtcbiAgICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJBcnJheUV4cHJlc3Npb25cIik7XG5cbiAgICBjYXNlIHR0LmJyYWNlTDpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlT2JqKGZhbHNlLCByZWZTaG9ydGhhbmREZWZhdWx0UG9zKTtcblxuICAgIGNhc2UgdHQuX2Z1bmN0aW9uOlxuICAgICAgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gICAgICB0aGlzLm5leHQoKTtcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlRnVuY3Rpb24obm9kZSwgZmFsc2UpO1xuXG4gICAgY2FzZSB0dC5fY2xhc3M6XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZUNsYXNzKHRoaXMuc3RhcnROb2RlKCksIGZhbHNlKTtcblxuICAgIGNhc2UgdHQuX25ldzpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlTmV3KCk7XG5cbiAgICBjYXNlIHR0LmJhY2tRdW90ZTpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlVGVtcGxhdGUoKTtcblxuICAgIGRlZmF1bHQ6XG4gICAgICB0aGlzLnVuZXhwZWN0ZWQoKTtcbiAgfVxufTtcblxucHAucGFyc2VMaXRlcmFsID0gZnVuY3Rpb24gKHZhbHVlKSB7XG4gIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgbm9kZS52YWx1ZSA9IHZhbHVlO1xuICBub2RlLnJhdyA9IHRoaXMuaW5wdXQuc2xpY2UodGhpcy5zdGFydCwgdGhpcy5lbmQpO1xuICB0aGlzLm5leHQoKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkxpdGVyYWxcIik7XG59O1xuXG5wcC5wYXJzZVBhcmVuRXhwcmVzc2lvbiA9IGZ1bmN0aW9uICgpIHtcbiAgdGhpcy5leHBlY3QodHQucGFyZW5MKTtcbiAgdmFyIHZhbCA9IHRoaXMucGFyc2VFeHByZXNzaW9uKCk7XG4gIHRoaXMuZXhwZWN0KHR0LnBhcmVuUik7XG4gIHJldHVybiB2YWw7XG59O1xuXG5wcC5wYXJzZVBhcmVuQW5kRGlzdGluZ3Vpc2hFeHByZXNzaW9uID0gZnVuY3Rpb24gKGNhbkJlQXJyb3cpIHtcbiAgdmFyIHN0YXJ0UG9zID0gdGhpcy5zdGFydCxcbiAgICAgIHN0YXJ0TG9jID0gdGhpcy5zdGFydExvYyxcbiAgICAgIHZhbCA9IHVuZGVmaW5lZDtcbiAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KSB7XG4gICAgdGhpcy5uZXh0KCk7XG5cbiAgICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDcgJiYgdGhpcy50eXBlID09PSB0dC5fZm9yKSB7XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZUNvbXByZWhlbnNpb24odGhpcy5zdGFydE5vZGVBdChzdGFydFBvcywgc3RhcnRMb2MpLCB0cnVlKTtcbiAgICB9XG5cbiAgICB2YXIgaW5uZXJTdGFydFBvcyA9IHRoaXMuc3RhcnQsXG4gICAgICAgIGlubmVyU3RhcnRMb2MgPSB0aGlzLnN0YXJ0TG9jO1xuICAgIHZhciBleHByTGlzdCA9IFtdLFxuICAgICAgICBmaXJzdCA9IHRydWU7XG4gICAgdmFyIHJlZlNob3J0aGFuZERlZmF1bHRQb3MgPSB7IHN0YXJ0OiAwIH0sXG4gICAgICAgIHNwcmVhZFN0YXJ0ID0gdW5kZWZpbmVkLFxuICAgICAgICBpbm5lclBhcmVuU3RhcnQgPSB1bmRlZmluZWQ7XG4gICAgd2hpbGUgKHRoaXMudHlwZSAhPT0gdHQucGFyZW5SKSB7XG4gICAgICBmaXJzdCA/IGZpcnN0ID0gZmFsc2UgOiB0aGlzLmV4cGVjdCh0dC5jb21tYSk7XG4gICAgICBpZiAodGhpcy50eXBlID09PSB0dC5lbGxpcHNpcykge1xuICAgICAgICBzcHJlYWRTdGFydCA9IHRoaXMuc3RhcnQ7XG4gICAgICAgIGV4cHJMaXN0LnB1c2godGhpcy5wYXJzZVBhcmVuSXRlbSh0aGlzLnBhcnNlUmVzdCgpKSk7XG4gICAgICAgIGJyZWFrO1xuICAgICAgfSBlbHNlIHtcbiAgICAgICAgaWYgKHRoaXMudHlwZSA9PT0gdHQucGFyZW5MICYmICFpbm5lclBhcmVuU3RhcnQpIHtcbiAgICAgICAgICBpbm5lclBhcmVuU3RhcnQgPSB0aGlzLnN0YXJ0O1xuICAgICAgICB9XG4gICAgICAgIGV4cHJMaXN0LnB1c2godGhpcy5wYXJzZU1heWJlQXNzaWduKGZhbHNlLCByZWZTaG9ydGhhbmREZWZhdWx0UG9zLCB0aGlzLnBhcnNlUGFyZW5JdGVtKSk7XG4gICAgICB9XG4gICAgfVxuICAgIHZhciBpbm5lckVuZFBvcyA9IHRoaXMuc3RhcnQsXG4gICAgICAgIGlubmVyRW5kTG9jID0gdGhpcy5zdGFydExvYztcbiAgICB0aGlzLmV4cGVjdCh0dC5wYXJlblIpO1xuXG4gICAgaWYgKGNhbkJlQXJyb3cgJiYgIXRoaXMuY2FuSW5zZXJ0U2VtaWNvbG9uKCkgJiYgdGhpcy5lYXQodHQuYXJyb3cpKSB7XG4gICAgICBpZiAoaW5uZXJQYXJlblN0YXJ0KSB0aGlzLnVuZXhwZWN0ZWQoaW5uZXJQYXJlblN0YXJ0KTtcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlUGFyZW5BcnJvd0xpc3Qoc3RhcnRQb3MsIHN0YXJ0TG9jLCBleHByTGlzdCk7XG4gICAgfVxuXG4gICAgaWYgKCFleHByTGlzdC5sZW5ndGgpIHRoaXMudW5leHBlY3RlZCh0aGlzLmxhc3RUb2tTdGFydCk7XG4gICAgaWYgKHNwcmVhZFN0YXJ0KSB0aGlzLnVuZXhwZWN0ZWQoc3ByZWFkU3RhcnQpO1xuICAgIGlmIChyZWZTaG9ydGhhbmREZWZhdWx0UG9zLnN0YXJ0KSB0aGlzLnVuZXhwZWN0ZWQocmVmU2hvcnRoYW5kRGVmYXVsdFBvcy5zdGFydCk7XG5cbiAgICBpZiAoZXhwckxpc3QubGVuZ3RoID4gMSkge1xuICAgICAgdmFsID0gdGhpcy5zdGFydE5vZGVBdChpbm5lclN0YXJ0UG9zLCBpbm5lclN0YXJ0TG9jKTtcbiAgICAgIHZhbC5leHByZXNzaW9ucyA9IGV4cHJMaXN0O1xuICAgICAgdGhpcy5maW5pc2hOb2RlQXQodmFsLCBcIlNlcXVlbmNlRXhwcmVzc2lvblwiLCBpbm5lckVuZFBvcywgaW5uZXJFbmRMb2MpO1xuICAgIH0gZWxzZSB7XG4gICAgICB2YWwgPSBleHByTGlzdFswXTtcbiAgICB9XG4gIH0gZWxzZSB7XG4gICAgdmFsID0gdGhpcy5wYXJzZVBhcmVuRXhwcmVzc2lvbigpO1xuICB9XG5cbiAgaWYgKHRoaXMub3B0aW9ucy5wcmVzZXJ2ZVBhcmVucykge1xuICAgIHZhciBwYXIgPSB0aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0UG9zLCBzdGFydExvYyk7XG4gICAgcGFyLmV4cHJlc3Npb24gPSB2YWw7XG4gICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShwYXIsIFwiUGFyZW50aGVzaXplZEV4cHJlc3Npb25cIik7XG4gIH0gZWxzZSB7XG4gICAgcmV0dXJuIHZhbDtcbiAgfVxufTtcblxucHAucGFyc2VQYXJlbkl0ZW0gPSBmdW5jdGlvbiAoaXRlbSkge1xuICByZXR1cm4gaXRlbTtcbn07XG5cbnBwLnBhcnNlUGFyZW5BcnJvd0xpc3QgPSBmdW5jdGlvbiAoc3RhcnRQb3MsIHN0YXJ0TG9jLCBleHByTGlzdCkge1xuICByZXR1cm4gdGhpcy5wYXJzZUFycm93RXhwcmVzc2lvbih0aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0UG9zLCBzdGFydExvYyksIGV4cHJMaXN0KTtcbn07XG5cbi8vIE5ldydzIHByZWNlZGVuY2UgaXMgc2xpZ2h0bHkgdHJpY2t5LiBJdCBtdXN0IGFsbG93IGl0cyBhcmd1bWVudFxuLy8gdG8gYmUgYSBgW11gIG9yIGRvdCBzdWJzY3JpcHQgZXhwcmVzc2lvbiwgYnV0IG5vdCBhIGNhbGwg4oCUIGF0XG4vLyBsZWFzdCwgbm90IHdpdGhvdXQgd3JhcHBpbmcgaXQgaW4gcGFyZW50aGVzZXMuIFRodXMsIGl0IHVzZXMgdGhlXG5cbnZhciBlbXB0eSA9IFtdO1xuXG5wcC5wYXJzZU5ldyA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICB2YXIgbWV0YSA9IHRoaXMucGFyc2VJZGVudCh0cnVlKTtcbiAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2ICYmIHRoaXMuZWF0KHR0LmRvdCkpIHtcbiAgICBub2RlLm1ldGEgPSBtZXRhO1xuICAgIG5vZGUucHJvcGVydHkgPSB0aGlzLnBhcnNlSWRlbnQodHJ1ZSk7XG4gICAgaWYgKG5vZGUucHJvcGVydHkubmFtZSAhPT0gXCJ0YXJnZXRcIikgdGhpcy5yYWlzZShub2RlLnByb3BlcnR5LnN0YXJ0LCBcIlRoZSBvbmx5IHZhbGlkIG1ldGEgcHJvcGVydHkgZm9yIG5ldyBpcyBuZXcudGFyZ2V0XCIpO1xuICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJNZXRhUHJvcGVydHlcIik7XG4gIH1cbiAgdmFyIHN0YXJ0UG9zID0gdGhpcy5zdGFydCxcbiAgICAgIHN0YXJ0TG9jID0gdGhpcy5zdGFydExvYztcbiAgbm9kZS5jYWxsZWUgPSB0aGlzLnBhcnNlU3Vic2NyaXB0cyh0aGlzLnBhcnNlRXhwckF0b20oKSwgc3RhcnRQb3MsIHN0YXJ0TG9jLCB0cnVlKTtcbiAgaWYgKHRoaXMuZWF0KHR0LnBhcmVuTCkpIG5vZGUuYXJndW1lbnRzID0gdGhpcy5wYXJzZUV4cHJMaXN0KHR0LnBhcmVuUiwgZmFsc2UpO2Vsc2Ugbm9kZS5hcmd1bWVudHMgPSBlbXB0eTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIk5ld0V4cHJlc3Npb25cIik7XG59O1xuXG4vLyBQYXJzZSB0ZW1wbGF0ZSBleHByZXNzaW9uLlxuXG5wcC5wYXJzZVRlbXBsYXRlRWxlbWVudCA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIGVsZW0gPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICBlbGVtLnZhbHVlID0ge1xuICAgIHJhdzogdGhpcy5pbnB1dC5zbGljZSh0aGlzLnN0YXJ0LCB0aGlzLmVuZCksXG4gICAgY29va2VkOiB0aGlzLnZhbHVlXG4gIH07XG4gIHRoaXMubmV4dCgpO1xuICBlbGVtLnRhaWwgPSB0aGlzLnR5cGUgPT09IHR0LmJhY2tRdW90ZTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShlbGVtLCBcIlRlbXBsYXRlRWxlbWVudFwiKTtcbn07XG5cbnBwLnBhcnNlVGVtcGxhdGUgPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgdGhpcy5uZXh0KCk7XG4gIG5vZGUuZXhwcmVzc2lvbnMgPSBbXTtcbiAgdmFyIGN1ckVsdCA9IHRoaXMucGFyc2VUZW1wbGF0ZUVsZW1lbnQoKTtcbiAgbm9kZS5xdWFzaXMgPSBbY3VyRWx0XTtcbiAgd2hpbGUgKCFjdXJFbHQudGFpbCkge1xuICAgIHRoaXMuZXhwZWN0KHR0LmRvbGxhckJyYWNlTCk7XG4gICAgbm9kZS5leHByZXNzaW9ucy5wdXNoKHRoaXMucGFyc2VFeHByZXNzaW9uKCkpO1xuICAgIHRoaXMuZXhwZWN0KHR0LmJyYWNlUik7XG4gICAgbm9kZS5xdWFzaXMucHVzaChjdXJFbHQgPSB0aGlzLnBhcnNlVGVtcGxhdGVFbGVtZW50KCkpO1xuICB9XG4gIHRoaXMubmV4dCgpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiVGVtcGxhdGVMaXRlcmFsXCIpO1xufTtcblxuLy8gUGFyc2UgYW4gb2JqZWN0IGxpdGVyYWwgb3IgYmluZGluZyBwYXR0ZXJuLlxuXG5wcC5wYXJzZU9iaiA9IGZ1bmN0aW9uIChpc1BhdHRlcm4sIHJlZlNob3J0aGFuZERlZmF1bHRQb3MpIHtcbiAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpLFxuICAgICAgZmlyc3QgPSB0cnVlLFxuICAgICAgcHJvcEhhc2ggPSB7fTtcbiAgbm9kZS5wcm9wZXJ0aWVzID0gW107XG4gIHRoaXMubmV4dCgpO1xuICB3aGlsZSAoIXRoaXMuZWF0KHR0LmJyYWNlUikpIHtcbiAgICBpZiAoIWZpcnN0KSB7XG4gICAgICB0aGlzLmV4cGVjdCh0dC5jb21tYSk7XG4gICAgICBpZiAodGhpcy5hZnRlclRyYWlsaW5nQ29tbWEodHQuYnJhY2VSKSkgYnJlYWs7XG4gICAgfSBlbHNlIGZpcnN0ID0gZmFsc2U7XG5cbiAgICB2YXIgcHJvcCA9IHRoaXMuc3RhcnROb2RlKCksXG4gICAgICAgIGlzR2VuZXJhdG9yID0gdW5kZWZpbmVkLFxuICAgICAgICBzdGFydFBvcyA9IHVuZGVmaW5lZCxcbiAgICAgICAgc3RhcnRMb2MgPSB1bmRlZmluZWQ7XG4gICAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KSB7XG4gICAgICBwcm9wLm1ldGhvZCA9IGZhbHNlO1xuICAgICAgcHJvcC5zaG9ydGhhbmQgPSBmYWxzZTtcbiAgICAgIGlmIChpc1BhdHRlcm4gfHwgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcykge1xuICAgICAgICBzdGFydFBvcyA9IHRoaXMuc3RhcnQ7XG4gICAgICAgIHN0YXJ0TG9jID0gdGhpcy5zdGFydExvYztcbiAgICAgIH1cbiAgICAgIGlmICghaXNQYXR0ZXJuKSBpc0dlbmVyYXRvciA9IHRoaXMuZWF0KHR0LnN0YXIpO1xuICAgIH1cbiAgICB0aGlzLnBhcnNlUHJvcGVydHlOYW1lKHByb3ApO1xuICAgIHRoaXMucGFyc2VQcm9wZXJ0eVZhbHVlKHByb3AsIGlzUGF0dGVybiwgaXNHZW5lcmF0b3IsIHN0YXJ0UG9zLCBzdGFydExvYywgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcyk7XG4gICAgdGhpcy5jaGVja1Byb3BDbGFzaChwcm9wLCBwcm9wSGFzaCk7XG4gICAgbm9kZS5wcm9wZXJ0aWVzLnB1c2godGhpcy5maW5pc2hOb2RlKHByb3AsIFwiUHJvcGVydHlcIikpO1xuICB9XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgaXNQYXR0ZXJuID8gXCJPYmplY3RQYXR0ZXJuXCIgOiBcIk9iamVjdEV4cHJlc3Npb25cIik7XG59O1xuXG5wcC5wYXJzZVByb3BlcnR5VmFsdWUgPSBmdW5jdGlvbiAocHJvcCwgaXNQYXR0ZXJuLCBpc0dlbmVyYXRvciwgc3RhcnRQb3MsIHN0YXJ0TG9jLCByZWZTaG9ydGhhbmREZWZhdWx0UG9zKSB7XG4gIGlmICh0aGlzLmVhdCh0dC5jb2xvbikpIHtcbiAgICBwcm9wLnZhbHVlID0gaXNQYXR0ZXJuID8gdGhpcy5wYXJzZU1heWJlRGVmYXVsdCh0aGlzLnN0YXJ0LCB0aGlzLnN0YXJ0TG9jKSA6IHRoaXMucGFyc2VNYXliZUFzc2lnbihmYWxzZSwgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcyk7XG4gICAgcHJvcC5raW5kID0gXCJpbml0XCI7XG4gIH0gZWxzZSBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYgJiYgdGhpcy50eXBlID09PSB0dC5wYXJlbkwpIHtcbiAgICBpZiAoaXNQYXR0ZXJuKSB0aGlzLnVuZXhwZWN0ZWQoKTtcbiAgICBwcm9wLmtpbmQgPSBcImluaXRcIjtcbiAgICBwcm9wLm1ldGhvZCA9IHRydWU7XG4gICAgcHJvcC52YWx1ZSA9IHRoaXMucGFyc2VNZXRob2QoaXNHZW5lcmF0b3IpO1xuICB9IGVsc2UgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA1ICYmICFwcm9wLmNvbXB1dGVkICYmIHByb3Aua2V5LnR5cGUgPT09IFwiSWRlbnRpZmllclwiICYmIChwcm9wLmtleS5uYW1lID09PSBcImdldFwiIHx8IHByb3Aua2V5Lm5hbWUgPT09IFwic2V0XCIpICYmICh0aGlzLnR5cGUgIT0gdHQuY29tbWEgJiYgdGhpcy50eXBlICE9IHR0LmJyYWNlUikpIHtcbiAgICBpZiAoaXNHZW5lcmF0b3IgfHwgaXNQYXR0ZXJuKSB0aGlzLnVuZXhwZWN0ZWQoKTtcbiAgICBwcm9wLmtpbmQgPSBwcm9wLmtleS5uYW1lO1xuICAgIHRoaXMucGFyc2VQcm9wZXJ0eU5hbWUocHJvcCk7XG4gICAgcHJvcC52YWx1ZSA9IHRoaXMucGFyc2VNZXRob2QoZmFsc2UpO1xuICB9IGVsc2UgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2ICYmICFwcm9wLmNvbXB1dGVkICYmIHByb3Aua2V5LnR5cGUgPT09IFwiSWRlbnRpZmllclwiKSB7XG4gICAgcHJvcC5raW5kID0gXCJpbml0XCI7XG4gICAgaWYgKGlzUGF0dGVybikge1xuICAgICAgaWYgKHRoaXMuaXNLZXl3b3JkKHByb3Aua2V5Lm5hbWUpIHx8IHRoaXMuc3RyaWN0ICYmIChyZXNlcnZlZFdvcmRzLnN0cmljdEJpbmQocHJvcC5rZXkubmFtZSkgfHwgcmVzZXJ2ZWRXb3Jkcy5zdHJpY3QocHJvcC5rZXkubmFtZSkpIHx8ICF0aGlzLm9wdGlvbnMuYWxsb3dSZXNlcnZlZCAmJiB0aGlzLmlzUmVzZXJ2ZWRXb3JkKHByb3Aua2V5Lm5hbWUpKSB0aGlzLnJhaXNlKHByb3Aua2V5LnN0YXJ0LCBcIkJpbmRpbmcgXCIgKyBwcm9wLmtleS5uYW1lKTtcbiAgICAgIHByb3AudmFsdWUgPSB0aGlzLnBhcnNlTWF5YmVEZWZhdWx0KHN0YXJ0UG9zLCBzdGFydExvYywgcHJvcC5rZXkpO1xuICAgIH0gZWxzZSBpZiAodGhpcy50eXBlID09PSB0dC5lcSAmJiByZWZTaG9ydGhhbmREZWZhdWx0UG9zKSB7XG4gICAgICBpZiAoIXJlZlNob3J0aGFuZERlZmF1bHRQb3Muc3RhcnQpIHJlZlNob3J0aGFuZERlZmF1bHRQb3Muc3RhcnQgPSB0aGlzLnN0YXJ0O1xuICAgICAgcHJvcC52YWx1ZSA9IHRoaXMucGFyc2VNYXliZURlZmF1bHQoc3RhcnRQb3MsIHN0YXJ0TG9jLCBwcm9wLmtleSk7XG4gICAgfSBlbHNlIHtcbiAgICAgIHByb3AudmFsdWUgPSBwcm9wLmtleTtcbiAgICB9XG4gICAgcHJvcC5zaG9ydGhhbmQgPSB0cnVlO1xuICB9IGVsc2UgdGhpcy51bmV4cGVjdGVkKCk7XG59O1xuXG5wcC5wYXJzZVByb3BlcnR5TmFtZSA9IGZ1bmN0aW9uIChwcm9wKSB7XG4gIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNikge1xuICAgIGlmICh0aGlzLmVhdCh0dC5icmFja2V0TCkpIHtcbiAgICAgIHByb3AuY29tcHV0ZWQgPSB0cnVlO1xuICAgICAgcHJvcC5rZXkgPSB0aGlzLnBhcnNlTWF5YmVBc3NpZ24oKTtcbiAgICAgIHRoaXMuZXhwZWN0KHR0LmJyYWNrZXRSKTtcbiAgICAgIHJldHVybiBwcm9wLmtleTtcbiAgICB9IGVsc2Uge1xuICAgICAgcHJvcC5jb21wdXRlZCA9IGZhbHNlO1xuICAgIH1cbiAgfVxuICByZXR1cm4gcHJvcC5rZXkgPSB0aGlzLnR5cGUgPT09IHR0Lm51bSB8fCB0aGlzLnR5cGUgPT09IHR0LnN0cmluZyA/IHRoaXMucGFyc2VFeHByQXRvbSgpIDogdGhpcy5wYXJzZUlkZW50KHRydWUpO1xufTtcblxuLy8gSW5pdGlhbGl6ZSBlbXB0eSBmdW5jdGlvbiBub2RlLlxuXG5wcC5pbml0RnVuY3Rpb24gPSBmdW5jdGlvbiAobm9kZSkge1xuICBub2RlLmlkID0gbnVsbDtcbiAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KSB7XG4gICAgbm9kZS5nZW5lcmF0b3IgPSBmYWxzZTtcbiAgICBub2RlLmV4cHJlc3Npb24gPSBmYWxzZTtcbiAgfVxufTtcblxuLy8gUGFyc2Ugb2JqZWN0IG9yIGNsYXNzIG1ldGhvZC5cblxucHAucGFyc2VNZXRob2QgPSBmdW5jdGlvbiAoaXNHZW5lcmF0b3IpIHtcbiAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICB0aGlzLmluaXRGdW5jdGlvbihub2RlKTtcbiAgdGhpcy5leHBlY3QodHQucGFyZW5MKTtcbiAgbm9kZS5wYXJhbXMgPSB0aGlzLnBhcnNlQmluZGluZ0xpc3QodHQucGFyZW5SLCBmYWxzZSwgZmFsc2UpO1xuICB2YXIgYWxsb3dFeHByZXNzaW9uQm9keSA9IHVuZGVmaW5lZDtcbiAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KSB7XG4gICAgbm9kZS5nZW5lcmF0b3IgPSBpc0dlbmVyYXRvcjtcbiAgICBhbGxvd0V4cHJlc3Npb25Cb2R5ID0gdHJ1ZTtcbiAgfSBlbHNlIHtcbiAgICBhbGxvd0V4cHJlc3Npb25Cb2R5ID0gZmFsc2U7XG4gIH1cbiAgdGhpcy5wYXJzZUZ1bmN0aW9uQm9keShub2RlLCBhbGxvd0V4cHJlc3Npb25Cb2R5KTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkZ1bmN0aW9uRXhwcmVzc2lvblwiKTtcbn07XG5cbi8vIFBhcnNlIGFycm93IGZ1bmN0aW9uIGV4cHJlc3Npb24gd2l0aCBnaXZlbiBwYXJhbWV0ZXJzLlxuXG5wcC5wYXJzZUFycm93RXhwcmVzc2lvbiA9IGZ1bmN0aW9uIChub2RlLCBwYXJhbXMpIHtcbiAgdGhpcy5pbml0RnVuY3Rpb24obm9kZSk7XG4gIG5vZGUucGFyYW1zID0gdGhpcy50b0Fzc2lnbmFibGVMaXN0KHBhcmFtcywgdHJ1ZSk7XG4gIHRoaXMucGFyc2VGdW5jdGlvbkJvZHkobm9kZSwgdHJ1ZSk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJBcnJvd0Z1bmN0aW9uRXhwcmVzc2lvblwiKTtcbn07XG5cbi8vIFBhcnNlIGZ1bmN0aW9uIGJvZHkgYW5kIGNoZWNrIHBhcmFtZXRlcnMuXG5cbnBwLnBhcnNlRnVuY3Rpb25Cb2R5ID0gZnVuY3Rpb24gKG5vZGUsIGFsbG93RXhwcmVzc2lvbikge1xuICB2YXIgaXNFeHByZXNzaW9uID0gYWxsb3dFeHByZXNzaW9uICYmIHRoaXMudHlwZSAhPT0gdHQuYnJhY2VMO1xuXG4gIGlmIChpc0V4cHJlc3Npb24pIHtcbiAgICBub2RlLmJvZHkgPSB0aGlzLnBhcnNlTWF5YmVBc3NpZ24oKTtcbiAgICBub2RlLmV4cHJlc3Npb24gPSB0cnVlO1xuICB9IGVsc2Uge1xuICAgIC8vIFN0YXJ0IGEgbmV3IHNjb3BlIHdpdGggcmVnYXJkIHRvIGxhYmVscyBhbmQgdGhlIGBpbkZ1bmN0aW9uYFxuICAgIC8vIGZsYWcgKHJlc3RvcmUgdGhlbSB0byB0aGVpciBvbGQgdmFsdWUgYWZ0ZXJ3YXJkcykuXG4gICAgdmFyIG9sZEluRnVuYyA9IHRoaXMuaW5GdW5jdGlvbixcbiAgICAgICAgb2xkSW5HZW4gPSB0aGlzLmluR2VuZXJhdG9yLFxuICAgICAgICBvbGRMYWJlbHMgPSB0aGlzLmxhYmVscztcbiAgICB0aGlzLmluRnVuY3Rpb24gPSB0cnVlO3RoaXMuaW5HZW5lcmF0b3IgPSBub2RlLmdlbmVyYXRvcjt0aGlzLmxhYmVscyA9IFtdO1xuICAgIG5vZGUuYm9keSA9IHRoaXMucGFyc2VCbG9jayh0cnVlKTtcbiAgICBub2RlLmV4cHJlc3Npb24gPSBmYWxzZTtcbiAgICB0aGlzLmluRnVuY3Rpb24gPSBvbGRJbkZ1bmM7dGhpcy5pbkdlbmVyYXRvciA9IG9sZEluR2VuO3RoaXMubGFiZWxzID0gb2xkTGFiZWxzO1xuICB9XG5cbiAgLy8gSWYgdGhpcyBpcyBhIHN0cmljdCBtb2RlIGZ1bmN0aW9uLCB2ZXJpZnkgdGhhdCBhcmd1bWVudCBuYW1lc1xuICAvLyBhcmUgbm90IHJlcGVhdGVkLCBhbmQgaXQgZG9lcyBub3QgdHJ5IHRvIGJpbmQgdGhlIHdvcmRzIGBldmFsYFxuICAvLyBvciBgYXJndW1lbnRzYC5cbiAgaWYgKHRoaXMuc3RyaWN0IHx8ICFpc0V4cHJlc3Npb24gJiYgbm9kZS5ib2R5LmJvZHkubGVuZ3RoICYmIHRoaXMuaXNVc2VTdHJpY3Qobm9kZS5ib2R5LmJvZHlbMF0pKSB7XG4gICAgdmFyIG5hbWVIYXNoID0ge30sXG4gICAgICAgIG9sZFN0cmljdCA9IHRoaXMuc3RyaWN0O1xuICAgIHRoaXMuc3RyaWN0ID0gdHJ1ZTtcbiAgICBpZiAobm9kZS5pZCkgdGhpcy5jaGVja0xWYWwobm9kZS5pZCwgdHJ1ZSk7XG4gICAgZm9yICh2YXIgaSA9IDA7IGkgPCBub2RlLnBhcmFtcy5sZW5ndGg7IGkrKykge1xuICAgICAgdGhpcy5jaGVja0xWYWwobm9kZS5wYXJhbXNbaV0sIHRydWUsIG5hbWVIYXNoKTtcbiAgICB9dGhpcy5zdHJpY3QgPSBvbGRTdHJpY3Q7XG4gIH1cbn07XG5cbi8vIFBhcnNlcyBhIGNvbW1hLXNlcGFyYXRlZCBsaXN0IG9mIGV4cHJlc3Npb25zLCBhbmQgcmV0dXJucyB0aGVtIGFzXG4vLyBhbiBhcnJheS4gYGNsb3NlYCBpcyB0aGUgdG9rZW4gdHlwZSB0aGF0IGVuZHMgdGhlIGxpc3QsIGFuZFxuLy8gYGFsbG93RW1wdHlgIGNhbiBiZSB0dXJuZWQgb24gdG8gYWxsb3cgc3Vic2VxdWVudCBjb21tYXMgd2l0aFxuLy8gbm90aGluZyBpbiBiZXR3ZWVuIHRoZW0gdG8gYmUgcGFyc2VkIGFzIGBudWxsYCAod2hpY2ggaXMgbmVlZGVkXG4vLyBmb3IgYXJyYXkgbGl0ZXJhbHMpLlxuXG5wcC5wYXJzZUV4cHJMaXN0ID0gZnVuY3Rpb24gKGNsb3NlLCBhbGxvd1RyYWlsaW5nQ29tbWEsIGFsbG93RW1wdHksIHJlZlNob3J0aGFuZERlZmF1bHRQb3MpIHtcbiAgdmFyIGVsdHMgPSBbXSxcbiAgICAgIGZpcnN0ID0gdHJ1ZTtcbiAgd2hpbGUgKCF0aGlzLmVhdChjbG9zZSkpIHtcbiAgICBpZiAoIWZpcnN0KSB7XG4gICAgICB0aGlzLmV4cGVjdCh0dC5jb21tYSk7XG4gICAgICBpZiAoYWxsb3dUcmFpbGluZ0NvbW1hICYmIHRoaXMuYWZ0ZXJUcmFpbGluZ0NvbW1hKGNsb3NlKSkgYnJlYWs7XG4gICAgfSBlbHNlIGZpcnN0ID0gZmFsc2U7XG5cbiAgICBpZiAoYWxsb3dFbXB0eSAmJiB0aGlzLnR5cGUgPT09IHR0LmNvbW1hKSB7XG4gICAgICBlbHRzLnB1c2gobnVsbCk7XG4gICAgfSBlbHNlIHtcbiAgICAgIGlmICh0aGlzLnR5cGUgPT09IHR0LmVsbGlwc2lzKSBlbHRzLnB1c2godGhpcy5wYXJzZVNwcmVhZChyZWZTaG9ydGhhbmREZWZhdWx0UG9zKSk7ZWxzZSBlbHRzLnB1c2godGhpcy5wYXJzZU1heWJlQXNzaWduKGZhbHNlLCByZWZTaG9ydGhhbmREZWZhdWx0UG9zKSk7XG4gICAgfVxuICB9XG4gIHJldHVybiBlbHRzO1xufTtcblxuLy8gUGFyc2UgdGhlIG5leHQgdG9rZW4gYXMgYW4gaWRlbnRpZmllci4gSWYgYGxpYmVyYWxgIGlzIHRydWUgKHVzZWRcbi8vIHdoZW4gcGFyc2luZyBwcm9wZXJ0aWVzKSwgaXQgd2lsbCBhbHNvIGNvbnZlcnQga2V5d29yZHMgaW50b1xuLy8gaWRlbnRpZmllcnMuXG5cbnBwLnBhcnNlSWRlbnQgPSBmdW5jdGlvbiAobGliZXJhbCkge1xuICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gIGlmIChsaWJlcmFsICYmIHRoaXMub3B0aW9ucy5hbGxvd1Jlc2VydmVkID09IFwibmV2ZXJcIikgbGliZXJhbCA9IGZhbHNlO1xuICBpZiAodGhpcy50eXBlID09PSB0dC5uYW1lKSB7XG4gICAgaWYgKCFsaWJlcmFsICYmICghdGhpcy5vcHRpb25zLmFsbG93UmVzZXJ2ZWQgJiYgdGhpcy5pc1Jlc2VydmVkV29yZCh0aGlzLnZhbHVlKSB8fCB0aGlzLnN0cmljdCAmJiByZXNlcnZlZFdvcmRzLnN0cmljdCh0aGlzLnZhbHVlKSAmJiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYgfHwgdGhpcy5pbnB1dC5zbGljZSh0aGlzLnN0YXJ0LCB0aGlzLmVuZCkuaW5kZXhPZihcIlxcXFxcIikgPT0gLTEpKSkgdGhpcy5yYWlzZSh0aGlzLnN0YXJ0LCBcIlRoZSBrZXl3b3JkICdcIiArIHRoaXMudmFsdWUgKyBcIicgaXMgcmVzZXJ2ZWRcIik7XG4gICAgbm9kZS5uYW1lID0gdGhpcy52YWx1ZTtcbiAgfSBlbHNlIGlmIChsaWJlcmFsICYmIHRoaXMudHlwZS5rZXl3b3JkKSB7XG4gICAgbm9kZS5uYW1lID0gdGhpcy50eXBlLmtleXdvcmQ7XG4gIH0gZWxzZSB7XG4gICAgdGhpcy51bmV4cGVjdGVkKCk7XG4gIH1cbiAgdGhpcy5uZXh0KCk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJJZGVudGlmaWVyXCIpO1xufTtcblxuLy8gUGFyc2VzIHlpZWxkIGV4cHJlc3Npb24gaW5zaWRlIGdlbmVyYXRvci5cblxucHAucGFyc2VZaWVsZCA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICB0aGlzLm5leHQoKTtcbiAgaWYgKHRoaXMudHlwZSA9PSB0dC5zZW1pIHx8IHRoaXMuY2FuSW5zZXJ0U2VtaWNvbG9uKCkgfHwgdGhpcy50eXBlICE9IHR0LnN0YXIgJiYgIXRoaXMudHlwZS5zdGFydHNFeHByKSB7XG4gICAgbm9kZS5kZWxlZ2F0ZSA9IGZhbHNlO1xuICAgIG5vZGUuYXJndW1lbnQgPSBudWxsO1xuICB9IGVsc2Uge1xuICAgIG5vZGUuZGVsZWdhdGUgPSB0aGlzLmVhdCh0dC5zdGFyKTtcbiAgICBub2RlLmFyZ3VtZW50ID0gdGhpcy5wYXJzZU1heWJlQXNzaWduKCk7XG4gIH1cbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIllpZWxkRXhwcmVzc2lvblwiKTtcbn07XG5cbi8vIFBhcnNlcyBhcnJheSBhbmQgZ2VuZXJhdG9yIGNvbXByZWhlbnNpb25zLlxuXG5wcC5wYXJzZUNvbXByZWhlbnNpb24gPSBmdW5jdGlvbiAobm9kZSwgaXNHZW5lcmF0b3IpIHtcbiAgbm9kZS5ibG9ja3MgPSBbXTtcbiAgd2hpbGUgKHRoaXMudHlwZSA9PT0gdHQuX2Zvcikge1xuICAgIHZhciBibG9jayA9IHRoaXMuc3RhcnROb2RlKCk7XG4gICAgdGhpcy5uZXh0KCk7XG4gICAgdGhpcy5leHBlY3QodHQucGFyZW5MKTtcbiAgICBibG9jay5sZWZ0ID0gdGhpcy5wYXJzZUJpbmRpbmdBdG9tKCk7XG4gICAgdGhpcy5jaGVja0xWYWwoYmxvY2subGVmdCwgdHJ1ZSk7XG4gICAgdGhpcy5leHBlY3RDb250ZXh0dWFsKFwib2ZcIik7XG4gICAgYmxvY2sucmlnaHQgPSB0aGlzLnBhcnNlRXhwcmVzc2lvbigpO1xuICAgIHRoaXMuZXhwZWN0KHR0LnBhcmVuUik7XG4gICAgbm9kZS5ibG9ja3MucHVzaCh0aGlzLmZpbmlzaE5vZGUoYmxvY2ssIFwiQ29tcHJlaGVuc2lvbkJsb2NrXCIpKTtcbiAgfVxuICBub2RlLmZpbHRlciA9IHRoaXMuZWF0KHR0Ll9pZikgPyB0aGlzLnBhcnNlUGFyZW5FeHByZXNzaW9uKCkgOiBudWxsO1xuICBub2RlLmJvZHkgPSB0aGlzLnBhcnNlRXhwcmVzc2lvbigpO1xuICB0aGlzLmV4cGVjdChpc0dlbmVyYXRvciA/IHR0LnBhcmVuUiA6IHR0LmJyYWNrZXRSKTtcbiAgbm9kZS5nZW5lcmF0b3IgPSBpc0dlbmVyYXRvcjtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkNvbXByZWhlbnNpb25FeHByZXNzaW9uXCIpO1xufTtcblxufSx7XCIuL2lkZW50aWZpZXJcIjo3LFwiLi9zdGF0ZVwiOjEzLFwiLi90b2tlbnR5cGVcIjoxNyxcIi4vdXRpbFwiOjE4fV0sNzpbZnVuY3Rpb24oX2RlcmVxXyxtb2R1bGUsZXhwb3J0cyl7XG5cblxuLy8gVGVzdCB3aGV0aGVyIGEgZ2l2ZW4gY2hhcmFjdGVyIGNvZGUgc3RhcnRzIGFuIGlkZW50aWZpZXIuXG5cblwidXNlIHN0cmljdFwiO1xuXG5leHBvcnRzLmlzSWRlbnRpZmllclN0YXJ0ID0gaXNJZGVudGlmaWVyU3RhcnQ7XG5cbi8vIFRlc3Qgd2hldGhlciBhIGdpdmVuIGNoYXJhY3RlciBpcyBwYXJ0IG9mIGFuIGlkZW50aWZpZXIuXG5cbmV4cG9ydHMuaXNJZGVudGlmaWVyQ2hhciA9IGlzSWRlbnRpZmllckNoYXI7XG5leHBvcnRzLl9fZXNNb2R1bGUgPSB0cnVlO1xuLy8gVGhpcyBpcyBhIHRyaWNrIHRha2VuIGZyb20gRXNwcmltYS4gSXQgdHVybnMgb3V0IHRoYXQsIG9uXG4vLyBub24tQ2hyb21lIGJyb3dzZXJzLCB0byBjaGVjayB3aGV0aGVyIGEgc3RyaW5nIGlzIGluIGEgc2V0LCBhXG4vLyBwcmVkaWNhdGUgY29udGFpbmluZyBhIGJpZyB1Z2x5IGBzd2l0Y2hgIHN0YXRlbWVudCBpcyBmYXN0ZXIgdGhhblxuLy8gYSByZWd1bGFyIGV4cHJlc3Npb24sIGFuZCBvbiBDaHJvbWUgdGhlIHR3byBhcmUgYWJvdXQgb24gcGFyLlxuLy8gVGhpcyBmdW5jdGlvbiB1c2VzIGBldmFsYCAobm9uLWxleGljYWwpIHRvIHByb2R1Y2Ugc3VjaCBhXG4vLyBwcmVkaWNhdGUgZnJvbSBhIHNwYWNlLXNlcGFyYXRlZCBzdHJpbmcgb2Ygd29yZHMuXG4vL1xuLy8gSXQgc3RhcnRzIGJ5IHNvcnRpbmcgdGhlIHdvcmRzIGJ5IGxlbmd0aC5cblxuZnVuY3Rpb24gbWFrZVByZWRpY2F0ZSh3b3Jkcykge1xuICB3b3JkcyA9IHdvcmRzLnNwbGl0KFwiIFwiKTtcbiAgdmFyIGYgPSBcIlwiLFxuICAgICAgY2F0cyA9IFtdO1xuICBvdXQ6IGZvciAodmFyIGkgPSAwOyBpIDwgd29yZHMubGVuZ3RoOyArK2kpIHtcbiAgICBmb3IgKHZhciBqID0gMDsgaiA8IGNhdHMubGVuZ3RoOyArK2opIHtcbiAgICAgIGlmIChjYXRzW2pdWzBdLmxlbmd0aCA9PSB3b3Jkc1tpXS5sZW5ndGgpIHtcbiAgICAgICAgY2F0c1tqXS5wdXNoKHdvcmRzW2ldKTtcbiAgICAgICAgY29udGludWUgb3V0O1xuICAgICAgfVxuICAgIH1jYXRzLnB1c2goW3dvcmRzW2ldXSk7XG4gIH1cbiAgZnVuY3Rpb24gY29tcGFyZVRvKGFycikge1xuICAgIGlmIChhcnIubGVuZ3RoID09IDEpIHtcbiAgICAgIHJldHVybiBmICs9IFwicmV0dXJuIHN0ciA9PT0gXCIgKyBKU09OLnN0cmluZ2lmeShhcnJbMF0pICsgXCI7XCI7XG4gICAgfWYgKz0gXCJzd2l0Y2goc3RyKXtcIjtcbiAgICBmb3IgKHZhciBpID0gMDsgaSA8IGFyci5sZW5ndGg7ICsraSkge1xuICAgICAgZiArPSBcImNhc2UgXCIgKyBKU09OLnN0cmluZ2lmeShhcnJbaV0pICsgXCI6XCI7XG4gICAgfWYgKz0gXCJyZXR1cm4gdHJ1ZX1yZXR1cm4gZmFsc2U7XCI7XG4gIH1cblxuICAvLyBXaGVuIHRoZXJlIGFyZSBtb3JlIHRoYW4gdGhyZWUgbGVuZ3RoIGNhdGVnb3JpZXMsIGFuIG91dGVyXG4gIC8vIHN3aXRjaCBmaXJzdCBkaXNwYXRjaGVzIG9uIHRoZSBsZW5ndGhzLCB0byBzYXZlIG9uIGNvbXBhcmlzb25zLlxuXG4gIGlmIChjYXRzLmxlbmd0aCA+IDMpIHtcbiAgICBjYXRzLnNvcnQoZnVuY3Rpb24gKGEsIGIpIHtcbiAgICAgIHJldHVybiBiLmxlbmd0aCAtIGEubGVuZ3RoO1xuICAgIH0pO1xuICAgIGYgKz0gXCJzd2l0Y2goc3RyLmxlbmd0aCl7XCI7XG4gICAgZm9yICh2YXIgaSA9IDA7IGkgPCBjYXRzLmxlbmd0aDsgKytpKSB7XG4gICAgICB2YXIgY2F0ID0gY2F0c1tpXTtcbiAgICAgIGYgKz0gXCJjYXNlIFwiICsgY2F0WzBdLmxlbmd0aCArIFwiOlwiO1xuICAgICAgY29tcGFyZVRvKGNhdCk7XG4gICAgfVxuICAgIGYgKz0gXCJ9XCJcblxuICAgIC8vIE90aGVyd2lzZSwgc2ltcGx5IGdlbmVyYXRlIGEgZmxhdCBgc3dpdGNoYCBzdGF0ZW1lbnQuXG5cbiAgICA7XG4gIH0gZWxzZSB7XG4gICAgY29tcGFyZVRvKHdvcmRzKTtcbiAgfVxuICByZXR1cm4gbmV3IEZ1bmN0aW9uKFwic3RyXCIsIGYpO1xufVxuXG4vLyBSZXNlcnZlZCB3b3JkIGxpc3RzIGZvciB2YXJpb3VzIGRpYWxlY3RzIG9mIHRoZSBsYW5ndWFnZVxuXG52YXIgcmVzZXJ2ZWRXb3JkcyA9IHtcbiAgMzogbWFrZVByZWRpY2F0ZShcImFic3RyYWN0IGJvb2xlYW4gYnl0ZSBjaGFyIGNsYXNzIGRvdWJsZSBlbnVtIGV4cG9ydCBleHRlbmRzIGZpbmFsIGZsb2F0IGdvdG8gaW1wbGVtZW50cyBpbXBvcnQgaW50IGludGVyZmFjZSBsb25nIG5hdGl2ZSBwYWNrYWdlIHByaXZhdGUgcHJvdGVjdGVkIHB1YmxpYyBzaG9ydCBzdGF0aWMgc3VwZXIgc3luY2hyb25pemVkIHRocm93cyB0cmFuc2llbnQgdm9sYXRpbGVcIiksXG4gIDU6IG1ha2VQcmVkaWNhdGUoXCJjbGFzcyBlbnVtIGV4dGVuZHMgc3VwZXIgY29uc3QgZXhwb3J0IGltcG9ydFwiKSxcbiAgNjogbWFrZVByZWRpY2F0ZShcImVudW0gYXdhaXRcIiksXG4gIHN0cmljdDogbWFrZVByZWRpY2F0ZShcImltcGxlbWVudHMgaW50ZXJmYWNlIGxldCBwYWNrYWdlIHByaXZhdGUgcHJvdGVjdGVkIHB1YmxpYyBzdGF0aWMgeWllbGRcIiksXG4gIHN0cmljdEJpbmQ6IG1ha2VQcmVkaWNhdGUoXCJldmFsIGFyZ3VtZW50c1wiKVxufTtcblxuZXhwb3J0cy5yZXNlcnZlZFdvcmRzID0gcmVzZXJ2ZWRXb3Jkcztcbi8vIEFuZCB0aGUga2V5d29yZHNcblxudmFyIGVjbWE1QW5kTGVzc0tleXdvcmRzID0gXCJicmVhayBjYXNlIGNhdGNoIGNvbnRpbnVlIGRlYnVnZ2VyIGRlZmF1bHQgZG8gZWxzZSBmaW5hbGx5IGZvciBmdW5jdGlvbiBpZiByZXR1cm4gc3dpdGNoIHRocm93IHRyeSB2YXIgd2hpbGUgd2l0aCBudWxsIHRydWUgZmFsc2UgaW5zdGFuY2VvZiB0eXBlb2Ygdm9pZCBkZWxldGUgbmV3IGluIHRoaXNcIjtcblxudmFyIGtleXdvcmRzID0ge1xuICA1OiBtYWtlUHJlZGljYXRlKGVjbWE1QW5kTGVzc0tleXdvcmRzKSxcbiAgNjogbWFrZVByZWRpY2F0ZShlY21hNUFuZExlc3NLZXl3b3JkcyArIFwiIGxldCBjb25zdCBjbGFzcyBleHRlbmRzIGV4cG9ydCBpbXBvcnQgeWllbGQgc3VwZXJcIilcbn07XG5cbmV4cG9ydHMua2V5d29yZHMgPSBrZXl3b3Jkcztcbi8vICMjIENoYXJhY3RlciBjYXRlZ29yaWVzXG5cbi8vIEJpZyB1Z2x5IHJlZ3VsYXIgZXhwcmVzc2lvbnMgdGhhdCBtYXRjaCBjaGFyYWN0ZXJzIGluIHRoZVxuLy8gd2hpdGVzcGFjZSwgaWRlbnRpZmllciwgYW5kIGlkZW50aWZpZXItc3RhcnQgY2F0ZWdvcmllcy4gVGhlc2Vcbi8vIGFyZSBvbmx5IGFwcGxpZWQgd2hlbiBhIGNoYXJhY3RlciBpcyBmb3VuZCB0byBhY3R1YWxseSBoYXZlIGFcbi8vIGNvZGUgcG9pbnQgYWJvdmUgMTI4LlxuLy8gR2VuZXJhdGVkIGJ5IGB0b29scy9nZW5lcmF0ZS1pZGVudGlmaWVyLXJlZ2V4LmpzYC5cblxudmFyIG5vbkFTQ0lJaWRlbnRpZmllclN0YXJ0Q2hhcnMgPSBcIsKqwrXCusOALcOWw5gtw7bDuC3LgcuGLcuRy6Aty6TLrMuuzbAtzbTNts23zbotzb3Nv86GzogtzorOjM6OLc6hzqMtz7XPty3SgdKKLdSv1LEt1ZbVmdWhLdaH15At16rXsC3XstigLdmK2a7Zr9mxLduT25Xbpdum267br9u6Ldu827/ckNySLdyv3Y0t3qXesd+KLd+q37Tftd+64KCALeCgleCgmuCgpOCgqOChgC3goZjgoqAt4KKy4KSELeCkueCkveClkOClmC3gpaHgpbEt4KaA4KaFLeCmjOCmj+CmkOCmky3gpqjgpqot4Kaw4Kay4Ka2LeCmueCmveCnjuCnnOCnneCnny3gp6Hgp7Dgp7HgqIUt4KiK4KiP4KiQ4KiTLeCoqOCoqi3gqLDgqLLgqLPgqLXgqLbgqLjgqLngqZkt4Kmc4Kme4KmyLeCptOCqhS3gqo3gqo8t4KqR4KqTLeCqqOCqqi3gqrDgqrLgqrPgqrUt4Kq54Kq94KuQ4Kug4Kuh4KyFLeCsjOCsj+CskOCsky3grKjgrKot4Kyw4Kyy4Kyz4Ky1LeCsueCsveCtnOCtneCtny3graHgrbHgroPgroUt4K6K4K6OLeCukOCuki3grpXgrpngrprgrpzgrp7grp/grqPgrqTgrqgt4K6q4K6uLeCuueCvkOCwhS3gsIzgsI4t4LCQ4LCSLeCwqOCwqi3gsLngsL3gsZjgsZngsaDgsaHgsoUt4LKM4LKOLeCykOCyki3gsqjgsqot4LKz4LK1LeCyueCyveCznuCzoOCzoeCzseCzsuC0hS3gtIzgtI4t4LSQ4LSSLeC0uuC0veC1juC1oOC1oeC1ui3gtb/gtoUt4LaW4LaaLeC2seC2sy3gtrvgtr3gt4At4LeG4LiBLeC4sOC4suC4s+C5gC3guYbguoHguoLguoTguofguojguorguo3gupQt4LqX4LqZLeC6n+C6oS3guqPguqXguqfguqrguqvguq0t4Lqw4Lqy4Lqz4Lq94LuALeC7hOC7huC7nC3gu5/gvIDgvYAt4L2H4L2JLeC9rOC+iC3gvozhgIAt4YCq4YC/4YGQLeGBleGBmi3hgZ3hgaHhgaXhgabhga4t4YGw4YG1LeGCgeGCjuGCoC3hg4Xhg4fhg43hg5At4YO64YO8LeGJiOGJii3hiY3hiZAt4YmW4YmY4YmaLeGJneGJoC3hiojhioot4YqN4YqQLeGKsOGKsi3hirXhirgt4Yq+4YuA4YuCLeGLheGLiC3hi5bhi5gt4YyQ4YySLeGMleGMmC3hjZrhjoAt4Y6P4Y6gLeGPtOGQgS3hmazhma8t4Zm/4ZqBLeGamuGaoC3hm6rhm64t4Zu44ZyALeGcjOGcji3hnJHhnKAt4Zyx4Z2ALeGdkeGdoC3hnazhna4t4Z2w4Z6ALeGes+Gfl+GfnOGgoC3hobfhooAt4aKo4aKq4aKwLeGjteGkgC3hpJ7hpZAt4aWt4aWwLeGltOGmgC3hpqvhp4Et4aeH4aiALeGoluGooC3hqZThqqfhrIUt4ayz4a2FLeGti+Gugy3hrqDhrq7hrq/hrrot4a+l4bCALeGwo+GxjS3hsY/hsZot4bG94bOpLeGzrOGzri3hs7Hhs7Xhs7bhtIAt4ba/4biALeG8leG8mC3hvJ3hvKAt4b2F4b2ILeG9jeG9kC3hvZfhvZnhvZvhvZ3hvZ8t4b294b6ALeG+tOG+ti3hvrzhvr7hv4It4b+E4b+GLeG/jOG/kC3hv5Phv5Yt4b+b4b+gLeG/rOG/si3hv7Thv7Yt4b+84oGx4oG/4oKQLeKCnOKEguKEh+KEii3ihJPihJXihJgt4oSd4oSk4oSm4oSo4oSqLeKEueKEvC3ihL/ihYUt4oWJ4oWO4oWgLeKGiOKwgC3isK7isLAt4rGe4rGgLeKzpOKzqy3is67is7Lis7PitIAt4rSl4rSn4rSt4rSwLeK1p+K1r+K2gC3itpbitqAt4ram4raoLeK2ruK2sC3itrbitrgt4ra+4reALeK3huK3iC3it47it5At4reW4reYLeK3nuOAhS3jgIfjgKEt44Cp44CxLeOAteOAuC3jgLzjgYEt44KW44KbLeOCn+OCoS3jg7rjg7wt44O/44SFLeOEreOEsS3jho7jhqAt44a644ewLeOHv+OQgC3ktrXkuIAt6b+M6oCALeqSjOqTkC3qk73qlIAt6piM6piQLeqYn+qYquqYq+qZgC3qma7qmb8t6pqd6pqgLeqbr+qcly3qnJ/qnKIt6p6I6p6LLeqejuqekC3qnq3qnrDqnrHqn7ct6qCB6qCDLeqgheqghy3qoIrqoIwt6qCi6qGALeqhs+qigi3qorPqo7It6qO36qO76qSKLeqkpeqksC3qpYbqpaAt6qW86qaELeqmsuqnj+qnoC3qp6Tqp6Yt6qev6qe6LeqnvuqogC3qqKjqqYAt6qmC6qmELeqpi+qpoC3qqbbqqbrqqb4t6qqv6qqx6qq16qq26qq5LeqqveqrgOqrguqrmy3qq53qq6At6quq6quyLeqrtOqsgS3qrIbqrIkt6qyO6qyRLeqsluqsoC3qrKbqrKgt6qyu6qywLeqtmuqtnC3qrZ/qraTqraXqr4At6q+i6rCALe2eo+2esC3tn4btn4st7Z+776SALe+pre+psC3vq5nvrIAt76yG76yTLe+sl++sne+sny3vrKjvrKot76y276y4Le+svO+svu+tgO+tge+tg++thO+thi3vrrHvr5Mt77S977WQLe+2j++2ki3vt4fvt7At77e777mwLe+5tO+5ti3vu7zvvKEt77y6772BLe+9mu+9pi3vvr7vv4It77+H77+KLe+/j++/ki3vv5fvv5ot77+cXCI7XG52YXIgbm9uQVNDSUlpZGVudGlmaWVyQ2hhcnMgPSBcIuKAjOKAjcK3zIAtza/Oh9KDLdKH1pEt1r3Wv9eB14LXhNeF14fYkC3YmtmLLdmp2bDbli3bnNufLduk26fbqNuqLdut27At27nckdywLd2K3qYt3rDfgC3fid+rLd+z4KCWLeCgmeCgmy3goKPgoKUt4KCn4KCpLeCgreChmS3goZvgo6Qt4KSD4KS6LeCkvOCkvi3gpY/gpZEt4KWX4KWi4KWj4KWmLeClr+CmgS3gpoPgprzgpr4t4KeE4KeH4KeI4KeLLeCnjeCnl+CnouCno+Cnpi3gp6/gqIEt4KiD4Ki84Ki+LeCpguCph+CpiOCpiy3gqY3gqZHgqaYt4Kmx4Km14KqBLeCqg+CqvOCqvi3gq4Xgq4ct4KuJ4KuLLeCrjeCrouCro+Crpi3gq6/grIEt4KyD4Ky84Ky+LeCthOCth+CtiOCtiy3grY3grZbgrZfgraLgraPgraYt4K2v4K6C4K6+LeCvguCvhi3gr4jgr4ot4K+N4K+X4K+mLeCvr+CwgC3gsIPgsL4t4LGE4LGGLeCxiOCxii3gsY3gsZXgsZbgsaLgsaPgsaYt4LGv4LKBLeCyg+CyvOCyvi3gs4Tgs4Yt4LOI4LOKLeCzjeCzleCzluCzouCzo+Czpi3gs6/gtIEt4LSD4LS+LeC1hOC1hi3gtYjgtYot4LWN4LWX4LWi4LWj4LWmLeC1r+C2guC2g+C3iuC3jy3gt5Tgt5bgt5gt4Lef4LemLeC3r+C3suC3s+C4seC4tC3guLrguYct4LmO4LmQLeC5meC6seC6tC3gurngurvgurzgu4gt4LuN4LuQLeC7meC8mOC8meC8oC3gvKngvLXgvLfgvLngvL7gvL/gvbEt4L6E4L6G4L6H4L6NLeC+l+C+mS3gvrzgv4bhgKst4YC+4YGALeGBieGBli3hgZnhgZ4t4YGg4YGiLeGBpOGBpy3hga3hgbEt4YG04YKCLeGCjeGCjy3hgp3hjZ0t4Y2f4Y2pLeGNseGcki3hnJThnLIt4Zy04Z2S4Z2T4Z2y4Z2z4Z60LeGfk+GfneGfoC3hn6nhoIst4aCN4aCQLeGgmeGiqeGkoC3hpKvhpLAt4aS74aWGLeGlj+GmsC3hp4Dhp4jhp4nhp5At4aea4aiXLeGom+GplS3hqZ7hqaAt4am84am/LeGqieGqkC3hqpnhqrAt4aq94ayALeGshOGstC3hrYThrZAt4a2Z4a2rLeGts+GugC3hroLhrqEt4a6t4a6wLeGuueGvpi3hr7PhsKQt4bC34bGALeGxieGxkC3hsZnhs5At4bOS4bOULeGzqOGzreGzsi3hs7Ths7jhs7nht4At4be14be8LeG3v+KAv+KBgOKBlOKDkC3ig5zig6Hig6Ut4oOw4rOvLeKzseK1v+K3oC3it7/jgKot44Cv44KZ44Ka6pigLeqYqeqZr+qZtC3qmb3qmp/qm7Dqm7HqoILqoIbqoIvqoKMt6qCn6qKA6qKB6qK0LeqjhOqjkC3qo5nqo6At6qOx6qSALeqkieqkpi3qpK3qpYct6qWT6qaALeqmg+qmsy3qp4Dqp5At6qeZ6qel6qewLeqnueqoqS3qqLbqqYPqqYzqqY3qqZAt6qmZ6qm7LeqpveqqsOqqsi3qqrTqqrfqqrjqqr7qqr/qq4Hqq6st6quv6qu16qu26q+jLeqvquqvrOqvreqvsC3qr7nvrJ7vuIAt77iP77igLe+4re+4s++4tO+5jS3vuY/vvJAt77yZ77y/XCI7XG5cbnZhciBub25BU0NJSWlkZW50aWZpZXJTdGFydCA9IG5ldyBSZWdFeHAoXCJbXCIgKyBub25BU0NJSWlkZW50aWZpZXJTdGFydENoYXJzICsgXCJdXCIpO1xudmFyIG5vbkFTQ0lJaWRlbnRpZmllciA9IG5ldyBSZWdFeHAoXCJbXCIgKyBub25BU0NJSWlkZW50aWZpZXJTdGFydENoYXJzICsgbm9uQVNDSUlpZGVudGlmaWVyQ2hhcnMgKyBcIl1cIik7XG5cbm5vbkFTQ0lJaWRlbnRpZmllclN0YXJ0Q2hhcnMgPSBub25BU0NJSWlkZW50aWZpZXJDaGFycyA9IG51bGw7XG5cbi8vIFRoZXNlIGFyZSBhIHJ1bi1sZW5ndGggYW5kIG9mZnNldCBlbmNvZGVkIHJlcHJlc2VudGF0aW9uIG9mIHRoZVxuLy8gPjB4ZmZmZiBjb2RlIHBvaW50cyB0aGF0IGFyZSBhIHZhbGlkIHBhcnQgb2YgaWRlbnRpZmllcnMuIFRoZVxuLy8gb2Zmc2V0IHN0YXJ0cyBhdCAweDEwMDAwLCBhbmQgZWFjaCBwYWlyIG9mIG51bWJlcnMgcmVwcmVzZW50cyBhblxuLy8gb2Zmc2V0IHRvIHRoZSBuZXh0IHJhbmdlLCBhbmQgdGhlbiBhIHNpemUgb2YgdGhlIHJhbmdlLiBUaGV5IHdlcmVcbi8vIGdlbmVyYXRlZCBieSB0b29scy9nZW5lcmF0ZS1pZGVudGlmaWVyLXJlZ2V4LmpzXG52YXIgYXN0cmFsSWRlbnRpZmllclN0YXJ0Q29kZXMgPSBbMCwgMTEsIDIsIDI1LCAyLCAxOCwgMiwgMSwgMiwgMTQsIDMsIDEzLCAzNSwgMTIyLCA3MCwgNTIsIDI2OCwgMjgsIDQsIDQ4LCA0OCwgMzEsIDE3LCAyNiwgNiwgMzcsIDExLCAyOSwgMywgMzUsIDUsIDcsIDIsIDQsIDQzLCAxNTcsIDk5LCAzOSwgOSwgNTEsIDE1NywgMzEwLCAxMCwgMjEsIDExLCA3LCAxNTMsIDUsIDMsIDAsIDIsIDQzLCAyLCAxLCA0LCAwLCAzLCAyMiwgMTEsIDIyLCAxMCwgMzAsIDk4LCAyMSwgMTEsIDI1LCA3MSwgNTUsIDcsIDEsIDY1LCAwLCAxNiwgMywgMiwgMiwgMiwgMjYsIDQ1LCAyOCwgNCwgMjgsIDM2LCA3LCAyLCAyNywgMjgsIDUzLCAxMSwgMjEsIDExLCAxOCwgMTQsIDE3LCAxMTEsIDcyLCA5NTUsIDUyLCA3NiwgNDQsIDMzLCAyNCwgMjcsIDM1LCA0MiwgMzQsIDQsIDAsIDEzLCA0NywgMTUsIDMsIDIyLCAwLCAzOCwgMTcsIDIsIDI0LCAxMzMsIDQ2LCAzOSwgNywgMywgMSwgMywgMjEsIDIsIDYsIDIsIDEsIDIsIDQsIDQsIDAsIDMyLCA0LCAyODcsIDQ3LCAyMSwgMSwgMiwgMCwgMTg1LCA0NiwgODIsIDQ3LCAyMSwgMCwgNjAsIDQyLCA1MDIsIDYzLCAzMiwgMCwgNDQ5LCA1NiwgMTI4OCwgOTIwLCAxMDQsIDExMCwgMjk2MiwgMTA3MCwgMTMyNjYsIDU2OCwgOCwgMzAsIDExNCwgMjksIDE5LCA0NywgMTcsIDMsIDMyLCAyMCwgNiwgMTgsIDg4MSwgNjgsIDEyLCAwLCA2NywgMTIsIDE2NDgxLCAxLCAzMDcxLCAxMDYsIDYsIDEyLCA0LCA4LCA4LCA5LCA1OTkxLCA4NCwgMiwgNzAsIDIsIDEsIDMsIDAsIDMsIDEsIDMsIDMsIDIsIDExLCAyLCAwLCAyLCA2LCAyLCA2NCwgMiwgMywgMywgNywgMiwgNiwgMiwgMjcsIDIsIDMsIDIsIDQsIDIsIDAsIDQsIDYsIDIsIDMzOSwgMywgMjQsIDIsIDI0LCAyLCAzMCwgMiwgMjQsIDIsIDMwLCAyLCAyNCwgMiwgMzAsIDIsIDI0LCAyLCAzMCwgMiwgMjQsIDIsIDcsIDQxNDksIDE5NiwgMTM0MCwgMywgMiwgMjYsIDIsIDEsIDIsIDAsIDMsIDAsIDIsIDksIDIsIDMsIDIsIDAsIDIsIDAsIDcsIDAsIDUsIDAsIDIsIDAsIDIsIDAsIDIsIDIsIDIsIDEsIDIsIDAsIDMsIDAsIDIsIDAsIDIsIDAsIDIsIDAsIDIsIDAsIDIsIDEsIDIsIDAsIDMsIDMsIDIsIDYsIDIsIDMsIDIsIDMsIDIsIDAsIDIsIDksIDIsIDE2LCA2LCAyLCAyLCA0LCAyLCAxNiwgNDQyMSwgNDI3MTAsIDQyLCA0MTQ4LCAxMiwgMjIxLCAxNjM1NSwgNTQxXTtcbnZhciBhc3RyYWxJZGVudGlmaWVyQ29kZXMgPSBbNTA5LCAwLCAyMjcsIDAsIDE1MCwgNCwgMjk0LCA5LCAxMzY4LCAyLCAyLCAxLCA2LCAzLCA0MSwgMiwgNSwgMCwgMTY2LCAxLCAxMzA2LCAyLCA1NCwgMTQsIDMyLCA5LCAxNiwgMywgNDYsIDEwLCA1NCwgOSwgNywgMiwgMzcsIDEzLCAyLCA5LCA1MiwgMCwgMTMsIDIsIDQ5LCAxMywgMTYsIDksIDgzLCAxMSwgMTY4LCAxMSwgNiwgOSwgOCwgMiwgNTcsIDAsIDIsIDYsIDMsIDEsIDMsIDIsIDEwLCAwLCAxMSwgMSwgMywgNiwgNCwgNCwgMzE2LCAxOSwgMTMsIDksIDIxNCwgNiwgMywgOCwgMTEyLCAxNiwgMTYsIDksIDgyLCAxMiwgOSwgOSwgNTM1LCA5LCAyMDg1NSwgOSwgMTM1LCA0LCA2MCwgNiwgMjYsIDksIDEwMTYsIDQ1LCAxNywgMywgMTk3MjMsIDEsIDUzMTksIDQsIDQsIDUsIDksIDcsIDMsIDYsIDMxLCAzLCAxNDksIDIsIDE0MTgsIDQ5LCA0MzA1LCA2LCA3OTI2MTgsIDIzOV07XG5cbi8vIFRoaXMgaGFzIGEgY29tcGxleGl0eSBsaW5lYXIgdG8gdGhlIHZhbHVlIG9mIHRoZSBjb2RlLiBUaGVcbi8vIGFzc3VtcHRpb24gaXMgdGhhdCBsb29raW5nIHVwIGFzdHJhbCBpZGVudGlmaWVyIGNoYXJhY3RlcnMgaXNcbi8vIHJhcmUuXG5mdW5jdGlvbiBpc0luQXN0cmFsU2V0KGNvZGUsIHNldCkge1xuICB2YXIgcG9zID0gNjU1MzY7XG4gIGZvciAodmFyIGkgPSAwOyBpIDwgc2V0Lmxlbmd0aDsgaSArPSAyKSB7XG4gICAgcG9zICs9IHNldFtpXTtcbiAgICBpZiAocG9zID4gY29kZSkge1xuICAgICAgcmV0dXJuIGZhbHNlO1xuICAgIH1wb3MgKz0gc2V0W2kgKyAxXTtcbiAgICBpZiAocG9zID49IGNvZGUpIHtcbiAgICAgIHJldHVybiB0cnVlO1xuICAgIH1cbiAgfVxufVxuZnVuY3Rpb24gaXNJZGVudGlmaWVyU3RhcnQoY29kZSwgYXN0cmFsKSB7XG4gIGlmIChjb2RlIDwgNjUpIHtcbiAgICByZXR1cm4gY29kZSA9PT0gMzY7XG4gIH1pZiAoY29kZSA8IDkxKSB7XG4gICAgcmV0dXJuIHRydWU7XG4gIH1pZiAoY29kZSA8IDk3KSB7XG4gICAgcmV0dXJuIGNvZGUgPT09IDk1O1xuICB9aWYgKGNvZGUgPCAxMjMpIHtcbiAgICByZXR1cm4gdHJ1ZTtcbiAgfWlmIChjb2RlIDw9IDY1NTM1KSB7XG4gICAgcmV0dXJuIGNvZGUgPj0gMTcwICYmIG5vbkFTQ0lJaWRlbnRpZmllclN0YXJ0LnRlc3QoU3RyaW5nLmZyb21DaGFyQ29kZShjb2RlKSk7XG4gIH1pZiAoYXN0cmFsID09PSBmYWxzZSkge1xuICAgIHJldHVybiBmYWxzZTtcbiAgfXJldHVybiBpc0luQXN0cmFsU2V0KGNvZGUsIGFzdHJhbElkZW50aWZpZXJTdGFydENvZGVzKTtcbn1cblxuZnVuY3Rpb24gaXNJZGVudGlmaWVyQ2hhcihjb2RlLCBhc3RyYWwpIHtcbiAgaWYgKGNvZGUgPCA0OCkge1xuICAgIHJldHVybiBjb2RlID09PSAzNjtcbiAgfWlmIChjb2RlIDwgNTgpIHtcbiAgICByZXR1cm4gdHJ1ZTtcbiAgfWlmIChjb2RlIDwgNjUpIHtcbiAgICByZXR1cm4gZmFsc2U7XG4gIH1pZiAoY29kZSA8IDkxKSB7XG4gICAgcmV0dXJuIHRydWU7XG4gIH1pZiAoY29kZSA8IDk3KSB7XG4gICAgcmV0dXJuIGNvZGUgPT09IDk1O1xuICB9aWYgKGNvZGUgPCAxMjMpIHtcbiAgICByZXR1cm4gdHJ1ZTtcbiAgfWlmIChjb2RlIDw9IDY1NTM1KSB7XG4gICAgcmV0dXJuIGNvZGUgPj0gMTcwICYmIG5vbkFTQ0lJaWRlbnRpZmllci50ZXN0KFN0cmluZy5mcm9tQ2hhckNvZGUoY29kZSkpO1xuICB9aWYgKGFzdHJhbCA9PT0gZmFsc2UpIHtcbiAgICByZXR1cm4gZmFsc2U7XG4gIH1yZXR1cm4gaXNJbkFzdHJhbFNldChjb2RlLCBhc3RyYWxJZGVudGlmaWVyU3RhcnRDb2RlcykgfHwgaXNJbkFzdHJhbFNldChjb2RlLCBhc3RyYWxJZGVudGlmaWVyQ29kZXMpO1xufVxuXG59LHt9XSw4OltmdW5jdGlvbihfZGVyZXFfLG1vZHVsZSxleHBvcnRzKXtcblwidXNlIHN0cmljdFwiO1xuXG52YXIgX2NsYXNzQ2FsbENoZWNrID0gZnVuY3Rpb24gKGluc3RhbmNlLCBDb25zdHJ1Y3RvcikgeyBpZiAoIShpbnN0YW5jZSBpbnN0YW5jZW9mIENvbnN0cnVjdG9yKSkgeyB0aHJvdyBuZXcgVHlwZUVycm9yKFwiQ2Fubm90IGNhbGwgYSBjbGFzcyBhcyBhIGZ1bmN0aW9uXCIpOyB9IH07XG5cbi8vIFRoZSBgZ2V0TGluZUluZm9gIGZ1bmN0aW9uIGlzIG1vc3RseSB1c2VmdWwgd2hlbiB0aGVcbi8vIGBsb2NhdGlvbnNgIG9wdGlvbiBpcyBvZmYgKGZvciBwZXJmb3JtYW5jZSByZWFzb25zKSBhbmQgeW91XG4vLyB3YW50IHRvIGZpbmQgdGhlIGxpbmUvY29sdW1uIHBvc2l0aW9uIGZvciBhIGdpdmVuIGNoYXJhY3RlclxuLy8gb2Zmc2V0LiBgaW5wdXRgIHNob3VsZCBiZSB0aGUgY29kZSBzdHJpbmcgdGhhdCB0aGUgb2Zmc2V0IHJlZmVyc1xuLy8gaW50by5cblxuZXhwb3J0cy5nZXRMaW5lSW5mbyA9IGdldExpbmVJbmZvO1xuZXhwb3J0cy5fX2VzTW9kdWxlID0gdHJ1ZTtcblxudmFyIFBhcnNlciA9IF9kZXJlcV8oXCIuL3N0YXRlXCIpLlBhcnNlcjtcblxudmFyIGxpbmVCcmVha0cgPSBfZGVyZXFfKFwiLi93aGl0ZXNwYWNlXCIpLmxpbmVCcmVha0c7XG5cbnZhciBkZXByZWNhdGUgPSBfZGVyZXFfKFwidXRpbFwiKS5kZXByZWNhdGU7XG5cbi8vIFRoZXNlIGFyZSB1c2VkIHdoZW4gYG9wdGlvbnMubG9jYXRpb25zYCBpcyBvbiwgZm9yIHRoZVxuLy8gYHN0YXJ0TG9jYCBhbmQgYGVuZExvY2AgcHJvcGVydGllcy5cblxudmFyIFBvc2l0aW9uID0gZXhwb3J0cy5Qb3NpdGlvbiA9IChmdW5jdGlvbiAoKSB7XG4gIGZ1bmN0aW9uIFBvc2l0aW9uKGxpbmUsIGNvbCkge1xuICAgIF9jbGFzc0NhbGxDaGVjayh0aGlzLCBQb3NpdGlvbik7XG5cbiAgICB0aGlzLmxpbmUgPSBsaW5lO1xuICAgIHRoaXMuY29sdW1uID0gY29sO1xuICB9XG5cbiAgUG9zaXRpb24ucHJvdG90eXBlLm9mZnNldCA9IGZ1bmN0aW9uIG9mZnNldChuKSB7XG4gICAgcmV0dXJuIG5ldyBQb3NpdGlvbih0aGlzLmxpbmUsIHRoaXMuY29sdW1uICsgbik7XG4gIH07XG5cbiAgcmV0dXJuIFBvc2l0aW9uO1xufSkoKTtcblxudmFyIFNvdXJjZUxvY2F0aW9uID0gZXhwb3J0cy5Tb3VyY2VMb2NhdGlvbiA9IGZ1bmN0aW9uIFNvdXJjZUxvY2F0aW9uKHAsIHN0YXJ0LCBlbmQpIHtcbiAgX2NsYXNzQ2FsbENoZWNrKHRoaXMsIFNvdXJjZUxvY2F0aW9uKTtcblxuICB0aGlzLnN0YXJ0ID0gc3RhcnQ7XG4gIHRoaXMuZW5kID0gZW5kO1xuICBpZiAocC5zb3VyY2VGaWxlICE9PSBudWxsKSB0aGlzLnNvdXJjZSA9IHAuc291cmNlRmlsZTtcbn07XG5cbmZ1bmN0aW9uIGdldExpbmVJbmZvKGlucHV0LCBvZmZzZXQpIHtcbiAgZm9yICh2YXIgbGluZSA9IDEsIGN1ciA9IDA7Oykge1xuICAgIGxpbmVCcmVha0cubGFzdEluZGV4ID0gY3VyO1xuICAgIHZhciBtYXRjaCA9IGxpbmVCcmVha0cuZXhlYyhpbnB1dCk7XG4gICAgaWYgKG1hdGNoICYmIG1hdGNoLmluZGV4IDwgb2Zmc2V0KSB7XG4gICAgICArK2xpbmU7XG4gICAgICBjdXIgPSBtYXRjaC5pbmRleCArIG1hdGNoWzBdLmxlbmd0aDtcbiAgICB9IGVsc2Uge1xuICAgICAgcmV0dXJuIG5ldyBQb3NpdGlvbihsaW5lLCBvZmZzZXQgLSBjdXIpO1xuICAgIH1cbiAgfVxufVxuXG52YXIgcHAgPSBQYXJzZXIucHJvdG90eXBlO1xuXG4vLyBUaGlzIGZ1bmN0aW9uIGlzIHVzZWQgdG8gcmFpc2UgZXhjZXB0aW9ucyBvbiBwYXJzZSBlcnJvcnMuIEl0XG4vLyB0YWtlcyBhbiBvZmZzZXQgaW50ZWdlciAoaW50byB0aGUgY3VycmVudCBgaW5wdXRgKSB0byBpbmRpY2F0ZVxuLy8gdGhlIGxvY2F0aW9uIG9mIHRoZSBlcnJvciwgYXR0YWNoZXMgdGhlIHBvc2l0aW9uIHRvIHRoZSBlbmRcbi8vIG9mIHRoZSBlcnJvciBtZXNzYWdlLCBhbmQgdGhlbiByYWlzZXMgYSBgU3ludGF4RXJyb3JgIHdpdGggdGhhdFxuLy8gbWVzc2FnZS5cblxucHAucmFpc2UgPSBmdW5jdGlvbiAocG9zLCBtZXNzYWdlKSB7XG4gIHZhciBsb2MgPSBnZXRMaW5lSW5mbyh0aGlzLmlucHV0LCBwb3MpO1xuICBtZXNzYWdlICs9IFwiIChcIiArIGxvYy5saW5lICsgXCI6XCIgKyBsb2MuY29sdW1uICsgXCIpXCI7XG4gIHZhciBlcnIgPSBuZXcgU3ludGF4RXJyb3IobWVzc2FnZSk7XG4gIGVyci5wb3MgPSBwb3M7ZXJyLmxvYyA9IGxvYztlcnIucmFpc2VkQXQgPSB0aGlzLnBvcztcbiAgdGhyb3cgZXJyO1xufTtcblxucHAuY3VyUG9zaXRpb24gPSBmdW5jdGlvbiAoKSB7XG4gIHJldHVybiBuZXcgUG9zaXRpb24odGhpcy5jdXJMaW5lLCB0aGlzLnBvcyAtIHRoaXMubGluZVN0YXJ0KTtcbn07XG5cbnBwLm1hcmtQb3NpdGlvbiA9IGZ1bmN0aW9uICgpIHtcbiAgcmV0dXJuIHRoaXMub3B0aW9ucy5sb2NhdGlvbnMgPyBbdGhpcy5zdGFydCwgdGhpcy5zdGFydExvY10gOiB0aGlzLnN0YXJ0O1xufTtcblxufSx7XCIuL3N0YXRlXCI6MTMsXCIuL3doaXRlc3BhY2VcIjoxOSxcInV0aWxcIjo1fV0sOTpbZnVuY3Rpb24oX2RlcmVxXyxtb2R1bGUsZXhwb3J0cyl7XG5cInVzZSBzdHJpY3RcIjtcblxudmFyIHR0ID0gX2RlcmVxXyhcIi4vdG9rZW50eXBlXCIpLnR5cGVzO1xuXG52YXIgUGFyc2VyID0gX2RlcmVxXyhcIi4vc3RhdGVcIikuUGFyc2VyO1xuXG52YXIgcmVzZXJ2ZWRXb3JkcyA9IF9kZXJlcV8oXCIuL2lkZW50aWZpZXJcIikucmVzZXJ2ZWRXb3JkcztcblxudmFyIGhhcyA9IF9kZXJlcV8oXCIuL3V0aWxcIikuaGFzO1xuXG52YXIgcHAgPSBQYXJzZXIucHJvdG90eXBlO1xuXG4vLyBDb252ZXJ0IGV4aXN0aW5nIGV4cHJlc3Npb24gYXRvbSB0byBhc3NpZ25hYmxlIHBhdHRlcm5cbi8vIGlmIHBvc3NpYmxlLlxuXG5wcC50b0Fzc2lnbmFibGUgPSBmdW5jdGlvbiAobm9kZSwgaXNCaW5kaW5nKSB7XG4gIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNiAmJiBub2RlKSB7XG4gICAgc3dpdGNoIChub2RlLnR5cGUpIHtcbiAgICAgIGNhc2UgXCJJZGVudGlmaWVyXCI6XG4gICAgICBjYXNlIFwiT2JqZWN0UGF0dGVyblwiOlxuICAgICAgY2FzZSBcIkFycmF5UGF0dGVyblwiOlxuICAgICAgY2FzZSBcIkFzc2lnbm1lbnRQYXR0ZXJuXCI6XG4gICAgICAgIGJyZWFrO1xuXG4gICAgICBjYXNlIFwiT2JqZWN0RXhwcmVzc2lvblwiOlxuICAgICAgICBub2RlLnR5cGUgPSBcIk9iamVjdFBhdHRlcm5cIjtcbiAgICAgICAgZm9yICh2YXIgaSA9IDA7IGkgPCBub2RlLnByb3BlcnRpZXMubGVuZ3RoOyBpKyspIHtcbiAgICAgICAgICB2YXIgcHJvcCA9IG5vZGUucHJvcGVydGllc1tpXTtcbiAgICAgICAgICBpZiAocHJvcC5raW5kICE9PSBcImluaXRcIikgdGhpcy5yYWlzZShwcm9wLmtleS5zdGFydCwgXCJPYmplY3QgcGF0dGVybiBjYW4ndCBjb250YWluIGdldHRlciBvciBzZXR0ZXJcIik7XG4gICAgICAgICAgdGhpcy50b0Fzc2lnbmFibGUocHJvcC52YWx1ZSwgaXNCaW5kaW5nKTtcbiAgICAgICAgfVxuICAgICAgICBicmVhaztcblxuICAgICAgY2FzZSBcIkFycmF5RXhwcmVzc2lvblwiOlxuICAgICAgICBub2RlLnR5cGUgPSBcIkFycmF5UGF0dGVyblwiO1xuICAgICAgICB0aGlzLnRvQXNzaWduYWJsZUxpc3Qobm9kZS5lbGVtZW50cywgaXNCaW5kaW5nKTtcbiAgICAgICAgYnJlYWs7XG5cbiAgICAgIGNhc2UgXCJBc3NpZ25tZW50RXhwcmVzc2lvblwiOlxuICAgICAgICBpZiAobm9kZS5vcGVyYXRvciA9PT0gXCI9XCIpIHtcbiAgICAgICAgICBub2RlLnR5cGUgPSBcIkFzc2lnbm1lbnRQYXR0ZXJuXCI7XG4gICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgdGhpcy5yYWlzZShub2RlLmxlZnQuZW5kLCBcIk9ubHkgJz0nIG9wZXJhdG9yIGNhbiBiZSB1c2VkIGZvciBzcGVjaWZ5aW5nIGRlZmF1bHQgdmFsdWUuXCIpO1xuICAgICAgICB9XG4gICAgICAgIGJyZWFrO1xuXG4gICAgICBjYXNlIFwiUGFyZW50aGVzaXplZEV4cHJlc3Npb25cIjpcbiAgICAgICAgbm9kZS5leHByZXNzaW9uID0gdGhpcy50b0Fzc2lnbmFibGUobm9kZS5leHByZXNzaW9uLCBpc0JpbmRpbmcpO1xuICAgICAgICBicmVhaztcblxuICAgICAgY2FzZSBcIk1lbWJlckV4cHJlc3Npb25cIjpcbiAgICAgICAgaWYgKCFpc0JpbmRpbmcpIGJyZWFrO1xuXG4gICAgICBkZWZhdWx0OlxuICAgICAgICB0aGlzLnJhaXNlKG5vZGUuc3RhcnQsIFwiQXNzaWduaW5nIHRvIHJ2YWx1ZVwiKTtcbiAgICB9XG4gIH1cbiAgcmV0dXJuIG5vZGU7XG59O1xuXG4vLyBDb252ZXJ0IGxpc3Qgb2YgZXhwcmVzc2lvbiBhdG9tcyB0byBiaW5kaW5nIGxpc3QuXG5cbnBwLnRvQXNzaWduYWJsZUxpc3QgPSBmdW5jdGlvbiAoZXhwckxpc3QsIGlzQmluZGluZykge1xuICB2YXIgZW5kID0gZXhwckxpc3QubGVuZ3RoO1xuICBpZiAoZW5kKSB7XG4gICAgdmFyIGxhc3QgPSBleHByTGlzdFtlbmQgLSAxXTtcbiAgICBpZiAobGFzdCAmJiBsYXN0LnR5cGUgPT0gXCJSZXN0RWxlbWVudFwiKSB7XG4gICAgICAtLWVuZDtcbiAgICB9IGVsc2UgaWYgKGxhc3QgJiYgbGFzdC50eXBlID09IFwiU3ByZWFkRWxlbWVudFwiKSB7XG4gICAgICBsYXN0LnR5cGUgPSBcIlJlc3RFbGVtZW50XCI7XG4gICAgICB2YXIgYXJnID0gbGFzdC5hcmd1bWVudDtcbiAgICAgIHRoaXMudG9Bc3NpZ25hYmxlKGFyZywgaXNCaW5kaW5nKTtcbiAgICAgIGlmIChhcmcudHlwZSAhPT0gXCJJZGVudGlmaWVyXCIgJiYgYXJnLnR5cGUgIT09IFwiTWVtYmVyRXhwcmVzc2lvblwiICYmIGFyZy50eXBlICE9PSBcIkFycmF5UGF0dGVyblwiKSB0aGlzLnVuZXhwZWN0ZWQoYXJnLnN0YXJ0KTtcbiAgICAgIC0tZW5kO1xuICAgIH1cbiAgfVxuICBmb3IgKHZhciBpID0gMDsgaSA8IGVuZDsgaSsrKSB7XG4gICAgdmFyIGVsdCA9IGV4cHJMaXN0W2ldO1xuICAgIGlmIChlbHQpIHRoaXMudG9Bc3NpZ25hYmxlKGVsdCwgaXNCaW5kaW5nKTtcbiAgfVxuICByZXR1cm4gZXhwckxpc3Q7XG59O1xuXG4vLyBQYXJzZXMgc3ByZWFkIGVsZW1lbnQuXG5cbnBwLnBhcnNlU3ByZWFkID0gZnVuY3Rpb24gKHJlZlNob3J0aGFuZERlZmF1bHRQb3MpIHtcbiAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICB0aGlzLm5leHQoKTtcbiAgbm9kZS5hcmd1bWVudCA9IHRoaXMucGFyc2VNYXliZUFzc2lnbihyZWZTaG9ydGhhbmREZWZhdWx0UG9zKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIlNwcmVhZEVsZW1lbnRcIik7XG59O1xuXG5wcC5wYXJzZVJlc3QgPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgdGhpcy5uZXh0KCk7XG4gIG5vZGUuYXJndW1lbnQgPSB0aGlzLnR5cGUgPT09IHR0Lm5hbWUgfHwgdGhpcy50eXBlID09PSB0dC5icmFja2V0TCA/IHRoaXMucGFyc2VCaW5kaW5nQXRvbSgpIDogdGhpcy51bmV4cGVjdGVkKCk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJSZXN0RWxlbWVudFwiKTtcbn07XG5cbi8vIFBhcnNlcyBsdmFsdWUgKGFzc2lnbmFibGUpIGF0b20uXG5cbnBwLnBhcnNlQmluZGluZ0F0b20gPSBmdW5jdGlvbiAoKSB7XG4gIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPCA2KSByZXR1cm4gdGhpcy5wYXJzZUlkZW50KCk7XG4gIHN3aXRjaCAodGhpcy50eXBlKSB7XG4gICAgY2FzZSB0dC5uYW1lOlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VJZGVudCgpO1xuXG4gICAgY2FzZSB0dC5icmFja2V0TDpcbiAgICAgIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgbm9kZS5lbGVtZW50cyA9IHRoaXMucGFyc2VCaW5kaW5nTGlzdCh0dC5icmFja2V0UiwgdHJ1ZSwgdHJ1ZSk7XG4gICAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiQXJyYXlQYXR0ZXJuXCIpO1xuXG4gICAgY2FzZSB0dC5icmFjZUw6XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZU9iaih0cnVlKTtcblxuICAgIGRlZmF1bHQ6XG4gICAgICB0aGlzLnVuZXhwZWN0ZWQoKTtcbiAgfVxufTtcblxucHAucGFyc2VCaW5kaW5nTGlzdCA9IGZ1bmN0aW9uIChjbG9zZSwgYWxsb3dFbXB0eSwgYWxsb3dUcmFpbGluZ0NvbW1hKSB7XG4gIHZhciBlbHRzID0gW10sXG4gICAgICBmaXJzdCA9IHRydWU7XG4gIHdoaWxlICghdGhpcy5lYXQoY2xvc2UpKSB7XG4gICAgaWYgKGZpcnN0KSBmaXJzdCA9IGZhbHNlO2Vsc2UgdGhpcy5leHBlY3QodHQuY29tbWEpO1xuICAgIGlmIChhbGxvd0VtcHR5ICYmIHRoaXMudHlwZSA9PT0gdHQuY29tbWEpIHtcbiAgICAgIGVsdHMucHVzaChudWxsKTtcbiAgICB9IGVsc2UgaWYgKGFsbG93VHJhaWxpbmdDb21tYSAmJiB0aGlzLmFmdGVyVHJhaWxpbmdDb21tYShjbG9zZSkpIHtcbiAgICAgIGJyZWFrO1xuICAgIH0gZWxzZSBpZiAodGhpcy50eXBlID09PSB0dC5lbGxpcHNpcykge1xuICAgICAgdmFyIHJlc3QgPSB0aGlzLnBhcnNlUmVzdCgpO1xuICAgICAgdGhpcy5wYXJzZUJpbmRpbmdMaXN0SXRlbShyZXN0KTtcbiAgICAgIGVsdHMucHVzaChyZXN0KTtcbiAgICAgIHRoaXMuZXhwZWN0KGNsb3NlKTtcbiAgICAgIGJyZWFrO1xuICAgIH0gZWxzZSB7XG4gICAgICB2YXIgZWxlbSA9IHRoaXMucGFyc2VNYXliZURlZmF1bHQodGhpcy5zdGFydCwgdGhpcy5zdGFydExvYyk7XG4gICAgICB0aGlzLnBhcnNlQmluZGluZ0xpc3RJdGVtKGVsZW0pO1xuICAgICAgZWx0cy5wdXNoKGVsZW0pO1xuICAgIH1cbiAgfVxuICByZXR1cm4gZWx0cztcbn07XG5cbnBwLnBhcnNlQmluZGluZ0xpc3RJdGVtID0gZnVuY3Rpb24gKHBhcmFtKSB7XG4gIHJldHVybiBwYXJhbTtcbn07XG5cbi8vIFBhcnNlcyBhc3NpZ25tZW50IHBhdHRlcm4gYXJvdW5kIGdpdmVuIGF0b20gaWYgcG9zc2libGUuXG5cbnBwLnBhcnNlTWF5YmVEZWZhdWx0ID0gZnVuY3Rpb24gKHN0YXJ0UG9zLCBzdGFydExvYywgbGVmdCkge1xuICBpZiAoQXJyYXkuaXNBcnJheShzdGFydFBvcykpIHtcbiAgICBpZiAodGhpcy5vcHRpb25zLmxvY2F0aW9ucyAmJiBub0NhbGxzID09PSB1bmRlZmluZWQpIHtcbiAgICAgIC8vIHNoaWZ0IGFyZ3VtZW50cyB0byBsZWZ0IGJ5IG9uZVxuICAgICAgbGVmdCA9IHN0YXJ0TG9jO1xuICAgICAgLy8gZmxhdHRlbiBzdGFydFBvc1xuICAgICAgc3RhcnRMb2MgPSBzdGFydFBvc1sxXTtcbiAgICAgIHN0YXJ0UG9zID0gc3RhcnRQb3NbMF07XG4gICAgfVxuICB9XG4gIGxlZnQgPSBsZWZ0IHx8IHRoaXMucGFyc2VCaW5kaW5nQXRvbSgpO1xuICBpZiAoIXRoaXMuZWF0KHR0LmVxKSkgcmV0dXJuIGxlZnQ7XG4gIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGVBdChzdGFydFBvcywgc3RhcnRMb2MpO1xuICBub2RlLm9wZXJhdG9yID0gXCI9XCI7XG4gIG5vZGUubGVmdCA9IGxlZnQ7XG4gIG5vZGUucmlnaHQgPSB0aGlzLnBhcnNlTWF5YmVBc3NpZ24oKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkFzc2lnbm1lbnRQYXR0ZXJuXCIpO1xufTtcblxuLy8gVmVyaWZ5IHRoYXQgYSBub2RlIGlzIGFuIGx2YWwg4oCUIHNvbWV0aGluZyB0aGF0IGNhbiBiZSBhc3NpZ25lZFxuLy8gdG8uXG5cbnBwLmNoZWNrTFZhbCA9IGZ1bmN0aW9uIChleHByLCBpc0JpbmRpbmcsIGNoZWNrQ2xhc2hlcykge1xuICBzd2l0Y2ggKGV4cHIudHlwZSkge1xuICAgIGNhc2UgXCJJZGVudGlmaWVyXCI6XG4gICAgICBpZiAodGhpcy5zdHJpY3QgJiYgKHJlc2VydmVkV29yZHMuc3RyaWN0QmluZChleHByLm5hbWUpIHx8IHJlc2VydmVkV29yZHMuc3RyaWN0KGV4cHIubmFtZSkpKSB0aGlzLnJhaXNlKGV4cHIuc3RhcnQsIChpc0JpbmRpbmcgPyBcIkJpbmRpbmcgXCIgOiBcIkFzc2lnbmluZyB0byBcIikgKyBleHByLm5hbWUgKyBcIiBpbiBzdHJpY3QgbW9kZVwiKTtcbiAgICAgIGlmIChjaGVja0NsYXNoZXMpIHtcbiAgICAgICAgaWYgKGhhcyhjaGVja0NsYXNoZXMsIGV4cHIubmFtZSkpIHRoaXMucmFpc2UoZXhwci5zdGFydCwgXCJBcmd1bWVudCBuYW1lIGNsYXNoIGluIHN0cmljdCBtb2RlXCIpO1xuICAgICAgICBjaGVja0NsYXNoZXNbZXhwci5uYW1lXSA9IHRydWU7XG4gICAgICB9XG4gICAgICBicmVhaztcblxuICAgIGNhc2UgXCJNZW1iZXJFeHByZXNzaW9uXCI6XG4gICAgICBpZiAoaXNCaW5kaW5nKSB0aGlzLnJhaXNlKGV4cHIuc3RhcnQsIChpc0JpbmRpbmcgPyBcIkJpbmRpbmdcIiA6IFwiQXNzaWduaW5nIHRvXCIpICsgXCIgbWVtYmVyIGV4cHJlc3Npb25cIik7XG4gICAgICBicmVhaztcblxuICAgIGNhc2UgXCJPYmplY3RQYXR0ZXJuXCI6XG4gICAgICBmb3IgKHZhciBpID0gMDsgaSA8IGV4cHIucHJvcGVydGllcy5sZW5ndGg7IGkrKykge1xuICAgICAgICB0aGlzLmNoZWNrTFZhbChleHByLnByb3BlcnRpZXNbaV0udmFsdWUsIGlzQmluZGluZywgY2hlY2tDbGFzaGVzKTtcbiAgICAgIH1icmVhaztcblxuICAgIGNhc2UgXCJBcnJheVBhdHRlcm5cIjpcbiAgICAgIGZvciAodmFyIGkgPSAwOyBpIDwgZXhwci5lbGVtZW50cy5sZW5ndGg7IGkrKykge1xuICAgICAgICB2YXIgZWxlbSA9IGV4cHIuZWxlbWVudHNbaV07XG4gICAgICAgIGlmIChlbGVtKSB0aGlzLmNoZWNrTFZhbChlbGVtLCBpc0JpbmRpbmcsIGNoZWNrQ2xhc2hlcyk7XG4gICAgICB9XG4gICAgICBicmVhaztcblxuICAgIGNhc2UgXCJBc3NpZ25tZW50UGF0dGVyblwiOlxuICAgICAgdGhpcy5jaGVja0xWYWwoZXhwci5sZWZ0LCBpc0JpbmRpbmcsIGNoZWNrQ2xhc2hlcyk7XG4gICAgICBicmVhaztcblxuICAgIGNhc2UgXCJSZXN0RWxlbWVudFwiOlxuICAgICAgdGhpcy5jaGVja0xWYWwoZXhwci5hcmd1bWVudCwgaXNCaW5kaW5nLCBjaGVja0NsYXNoZXMpO1xuICAgICAgYnJlYWs7XG5cbiAgICBjYXNlIFwiUGFyZW50aGVzaXplZEV4cHJlc3Npb25cIjpcbiAgICAgIHRoaXMuY2hlY2tMVmFsKGV4cHIuZXhwcmVzc2lvbiwgaXNCaW5kaW5nLCBjaGVja0NsYXNoZXMpO1xuICAgICAgYnJlYWs7XG5cbiAgICBkZWZhdWx0OlxuICAgICAgdGhpcy5yYWlzZShleHByLnN0YXJ0LCAoaXNCaW5kaW5nID8gXCJCaW5kaW5nXCIgOiBcIkFzc2lnbmluZyB0b1wiKSArIFwiIHJ2YWx1ZVwiKTtcbiAgfVxufTtcblxufSx7XCIuL2lkZW50aWZpZXJcIjo3LFwiLi9zdGF0ZVwiOjEzLFwiLi90b2tlbnR5cGVcIjoxNyxcIi4vdXRpbFwiOjE4fV0sMTA6W2Z1bmN0aW9uKF9kZXJlcV8sbW9kdWxlLGV4cG9ydHMpe1xuXCJ1c2Ugc3RyaWN0XCI7XG5cbnZhciBfY2xhc3NDYWxsQ2hlY2sgPSBmdW5jdGlvbiAoaW5zdGFuY2UsIENvbnN0cnVjdG9yKSB7IGlmICghKGluc3RhbmNlIGluc3RhbmNlb2YgQ29uc3RydWN0b3IpKSB7IHRocm93IG5ldyBUeXBlRXJyb3IoXCJDYW5ub3QgY2FsbCBhIGNsYXNzIGFzIGEgZnVuY3Rpb25cIik7IH0gfTtcblxuZXhwb3J0cy5fX2VzTW9kdWxlID0gdHJ1ZTtcblxudmFyIFBhcnNlciA9IF9kZXJlcV8oXCIuL3N0YXRlXCIpLlBhcnNlcjtcblxudmFyIFNvdXJjZUxvY2F0aW9uID0gX2RlcmVxXyhcIi4vbG9jYXRpb25cIikuU291cmNlTG9jYXRpb247XG5cbi8vIFN0YXJ0IGFuIEFTVCBub2RlLCBhdHRhY2hpbmcgYSBzdGFydCBvZmZzZXQuXG5cbnZhciBwcCA9IFBhcnNlci5wcm90b3R5cGU7XG5cbnZhciBOb2RlID0gZXhwb3J0cy5Ob2RlID0gZnVuY3Rpb24gTm9kZSgpIHtcbiAgX2NsYXNzQ2FsbENoZWNrKHRoaXMsIE5vZGUpO1xufTtcblxucHAuc3RhcnROb2RlID0gZnVuY3Rpb24gKCkge1xuICB2YXIgbm9kZSA9IG5ldyBOb2RlKCk7XG4gIG5vZGUuc3RhcnQgPSB0aGlzLnN0YXJ0O1xuICBpZiAodGhpcy5vcHRpb25zLmxvY2F0aW9ucykgbm9kZS5sb2MgPSBuZXcgU291cmNlTG9jYXRpb24odGhpcywgdGhpcy5zdGFydExvYyk7XG4gIGlmICh0aGlzLm9wdGlvbnMuZGlyZWN0U291cmNlRmlsZSkgbm9kZS5zb3VyY2VGaWxlID0gdGhpcy5vcHRpb25zLmRpcmVjdFNvdXJjZUZpbGU7XG4gIGlmICh0aGlzLm9wdGlvbnMucmFuZ2VzKSBub2RlLnJhbmdlID0gW3RoaXMuc3RhcnQsIDBdO1xuICByZXR1cm4gbm9kZTtcbn07XG5cbnBwLnN0YXJ0Tm9kZUF0ID0gZnVuY3Rpb24gKHBvcywgbG9jKSB7XG4gIHZhciBub2RlID0gbmV3IE5vZGUoKTtcbiAgaWYgKEFycmF5LmlzQXJyYXkocG9zKSkge1xuICAgIGlmICh0aGlzLm9wdGlvbnMubG9jYXRpb25zICYmIGxvYyA9PT0gdW5kZWZpbmVkKSB7XG4gICAgICAvLyBmbGF0dGVuIHBvc1xuICAgICAgbG9jID0gcG9zWzFdO1xuICAgICAgcG9zID0gcG9zWzBdO1xuICAgIH1cbiAgfVxuICBub2RlLnN0YXJ0ID0gcG9zO1xuICBpZiAodGhpcy5vcHRpb25zLmxvY2F0aW9ucykgbm9kZS5sb2MgPSBuZXcgU291cmNlTG9jYXRpb24odGhpcywgbG9jKTtcbiAgaWYgKHRoaXMub3B0aW9ucy5kaXJlY3RTb3VyY2VGaWxlKSBub2RlLnNvdXJjZUZpbGUgPSB0aGlzLm9wdGlvbnMuZGlyZWN0U291cmNlRmlsZTtcbiAgaWYgKHRoaXMub3B0aW9ucy5yYW5nZXMpIG5vZGUucmFuZ2UgPSBbcG9zLCAwXTtcbiAgcmV0dXJuIG5vZGU7XG59O1xuXG4vLyBGaW5pc2ggYW4gQVNUIG5vZGUsIGFkZGluZyBgdHlwZWAgYW5kIGBlbmRgIHByb3BlcnRpZXMuXG5cbnBwLmZpbmlzaE5vZGUgPSBmdW5jdGlvbiAobm9kZSwgdHlwZSkge1xuICBub2RlLnR5cGUgPSB0eXBlO1xuICBub2RlLmVuZCA9IHRoaXMubGFzdFRva0VuZDtcbiAgaWYgKHRoaXMub3B0aW9ucy5sb2NhdGlvbnMpIG5vZGUubG9jLmVuZCA9IHRoaXMubGFzdFRva0VuZExvYztcbiAgaWYgKHRoaXMub3B0aW9ucy5yYW5nZXMpIG5vZGUucmFuZ2VbMV0gPSB0aGlzLmxhc3RUb2tFbmQ7XG4gIHJldHVybiBub2RlO1xufTtcblxuLy8gRmluaXNoIG5vZGUgYXQgZ2l2ZW4gcG9zaXRpb25cblxucHAuZmluaXNoTm9kZUF0ID0gZnVuY3Rpb24gKG5vZGUsIHR5cGUsIHBvcywgbG9jKSB7XG4gIG5vZGUudHlwZSA9IHR5cGU7XG4gIGlmIChBcnJheS5pc0FycmF5KHBvcykpIHtcbiAgICBpZiAodGhpcy5vcHRpb25zLmxvY2F0aW9ucyAmJiBsb2MgPT09IHVuZGVmaW5lZCkge1xuICAgICAgLy8gZmxhdHRlbiBwb3NcbiAgICAgIGxvYyA9IHBvc1sxXTtcbiAgICAgIHBvcyA9IHBvc1swXTtcbiAgICB9XG4gIH1cbiAgbm9kZS5lbmQgPSBwb3M7XG4gIGlmICh0aGlzLm9wdGlvbnMubG9jYXRpb25zKSBub2RlLmxvYy5lbmQgPSBsb2M7XG4gIGlmICh0aGlzLm9wdGlvbnMucmFuZ2VzKSBub2RlLnJhbmdlWzFdID0gcG9zO1xuICByZXR1cm4gbm9kZTtcbn07XG5cbn0se1wiLi9sb2NhdGlvblwiOjgsXCIuL3N0YXRlXCI6MTN9XSwxMTpbZnVuY3Rpb24oX2RlcmVxXyxtb2R1bGUsZXhwb3J0cyl7XG5cblxuLy8gSW50ZXJwcmV0IGFuZCBkZWZhdWx0IGFuIG9wdGlvbnMgb2JqZWN0XG5cblwidXNlIHN0cmljdFwiO1xuXG5leHBvcnRzLmdldE9wdGlvbnMgPSBnZXRPcHRpb25zO1xuZXhwb3J0cy5fX2VzTW9kdWxlID0gdHJ1ZTtcblxudmFyIF91dGlsID0gX2RlcmVxXyhcIi4vdXRpbFwiKTtcblxudmFyIGhhcyA9IF91dGlsLmhhcztcbnZhciBpc0FycmF5ID0gX3V0aWwuaXNBcnJheTtcblxudmFyIFNvdXJjZUxvY2F0aW9uID0gX2RlcmVxXyhcIi4vbG9jYXRpb25cIikuU291cmNlTG9jYXRpb247XG5cbi8vIEEgc2Vjb25kIG9wdGlvbmFsIGFyZ3VtZW50IGNhbiBiZSBnaXZlbiB0byBmdXJ0aGVyIGNvbmZpZ3VyZVxuLy8gdGhlIHBhcnNlciBwcm9jZXNzLiBUaGVzZSBvcHRpb25zIGFyZSByZWNvZ25pemVkOlxuXG52YXIgZGVmYXVsdE9wdGlvbnMgPSB7XG4gIC8vIGBlY21hVmVyc2lvbmAgaW5kaWNhdGVzIHRoZSBFQ01BU2NyaXB0IHZlcnNpb24gdG8gcGFyc2UuIE11c3RcbiAgLy8gYmUgZWl0aGVyIDMsIG9yIDUsIG9yIDYuIFRoaXMgaW5mbHVlbmNlcyBzdXBwb3J0IGZvciBzdHJpY3RcbiAgLy8gbW9kZSwgdGhlIHNldCBvZiByZXNlcnZlZCB3b3Jkcywgc3VwcG9ydCBmb3IgZ2V0dGVycyBhbmRcbiAgLy8gc2V0dGVycyBhbmQgb3RoZXIgZmVhdHVyZXMuXG4gIGVjbWFWZXJzaW9uOiA1LFxuICAvLyBTb3VyY2UgdHlwZSAoXCJzY3JpcHRcIiBvciBcIm1vZHVsZVwiKSBmb3IgZGlmZmVyZW50IHNlbWFudGljc1xuICBzb3VyY2VUeXBlOiBcInNjcmlwdFwiLFxuICAvLyBgb25JbnNlcnRlZFNlbWljb2xvbmAgY2FuIGJlIGEgY2FsbGJhY2sgdGhhdCB3aWxsIGJlIGNhbGxlZFxuICAvLyB3aGVuIGEgc2VtaWNvbG9uIGlzIGF1dG9tYXRpY2FsbHkgaW5zZXJ0ZWQuIEl0IHdpbGwgYmUgcGFzc2VkXG4gIC8vIHRoIHBvc2l0aW9uIG9mIHRoZSBjb21tYSBhcyBhbiBvZmZzZXQsIGFuZCBpZiBgbG9jYXRpb25zYCBpc1xuICAvLyBlbmFibGVkLCBpdCBpcyBnaXZlbiB0aGUgbG9jYXRpb24gYXMgYSBge2xpbmUsIGNvbHVtbn1gIG9iamVjdFxuICAvLyBhcyBzZWNvbmQgYXJndW1lbnQuXG4gIG9uSW5zZXJ0ZWRTZW1pY29sb246IG51bGwsXG4gIC8vIGBvblRyYWlsaW5nQ29tbWFgIGlzIHNpbWlsYXIgdG8gYG9uSW5zZXJ0ZWRTZW1pY29sb25gLCBidXQgZm9yXG4gIC8vIHRyYWlsaW5nIGNvbW1hcy5cbiAgb25UcmFpbGluZ0NvbW1hOiBudWxsLFxuICAvLyBCeSBkZWZhdWx0LCByZXNlcnZlZCB3b3JkcyBhcmUgbm90IGVuZm9yY2VkLiBEaXNhYmxlXG4gIC8vIGBhbGxvd1Jlc2VydmVkYCB0byBlbmZvcmNlIHRoZW0uIFdoZW4gdGhpcyBvcHRpb24gaGFzIHRoZVxuICAvLyB2YWx1ZSBcIm5ldmVyXCIsIHJlc2VydmVkIHdvcmRzIGFuZCBrZXl3b3JkcyBjYW4gYWxzbyBub3QgYmVcbiAgLy8gdXNlZCBhcyBwcm9wZXJ0eSBuYW1lcy5cbiAgYWxsb3dSZXNlcnZlZDogdHJ1ZSxcbiAgLy8gV2hlbiBlbmFibGVkLCBhIHJldHVybiBhdCB0aGUgdG9wIGxldmVsIGlzIG5vdCBjb25zaWRlcmVkIGFuXG4gIC8vIGVycm9yLlxuICBhbGxvd1JldHVybk91dHNpZGVGdW5jdGlvbjogZmFsc2UsXG4gIC8vIFdoZW4gZW5hYmxlZCwgaW1wb3J0L2V4cG9ydCBzdGF0ZW1lbnRzIGFyZSBub3QgY29uc3RyYWluZWQgdG9cbiAgLy8gYXBwZWFyaW5nIGF0IHRoZSB0b3Agb2YgdGhlIHByb2dyYW0uXG4gIGFsbG93SW1wb3J0RXhwb3J0RXZlcnl3aGVyZTogZmFsc2UsXG4gIC8vIFdoZW4gZW5hYmxlZCwgaGFzaGJhbmcgZGlyZWN0aXZlIGluIHRoZSBiZWdpbm5pbmcgb2YgZmlsZVxuICAvLyBpcyBhbGxvd2VkIGFuZCB0cmVhdGVkIGFzIGEgbGluZSBjb21tZW50LlxuICBhbGxvd0hhc2hCYW5nOiBmYWxzZSxcbiAgLy8gV2hlbiBgbG9jYXRpb25zYCBpcyBvbiwgYGxvY2AgcHJvcGVydGllcyBob2xkaW5nIG9iamVjdHMgd2l0aFxuICAvLyBgc3RhcnRgIGFuZCBgZW5kYCBwcm9wZXJ0aWVzIGluIGB7bGluZSwgY29sdW1ufWAgZm9ybSAod2l0aFxuICAvLyBsaW5lIGJlaW5nIDEtYmFzZWQgYW5kIGNvbHVtbiAwLWJhc2VkKSB3aWxsIGJlIGF0dGFjaGVkIHRvIHRoZVxuICAvLyBub2Rlcy5cbiAgbG9jYXRpb25zOiBmYWxzZSxcbiAgLy8gQSBmdW5jdGlvbiBjYW4gYmUgcGFzc2VkIGFzIGBvblRva2VuYCBvcHRpb24sIHdoaWNoIHdpbGxcbiAgLy8gY2F1c2UgQWNvcm4gdG8gY2FsbCB0aGF0IGZ1bmN0aW9uIHdpdGggb2JqZWN0IGluIHRoZSBzYW1lXG4gIC8vIGZvcm1hdCBhcyB0b2tlbml6ZSgpIHJldHVybnMuIE5vdGUgdGhhdCB5b3UgYXJlIG5vdFxuICAvLyBhbGxvd2VkIHRvIGNhbGwgdGhlIHBhcnNlciBmcm9tIHRoZSBjYWxsYmFja+KAlHRoYXQgd2lsbFxuICAvLyBjb3JydXB0IGl0cyBpbnRlcm5hbCBzdGF0ZS5cbiAgb25Ub2tlbjogbnVsbCxcbiAgLy8gQSBmdW5jdGlvbiBjYW4gYmUgcGFzc2VkIGFzIGBvbkNvbW1lbnRgIG9wdGlvbiwgd2hpY2ggd2lsbFxuICAvLyBjYXVzZSBBY29ybiB0byBjYWxsIHRoYXQgZnVuY3Rpb24gd2l0aCBgKGJsb2NrLCB0ZXh0LCBzdGFydCxcbiAgLy8gZW5kKWAgcGFyYW1ldGVycyB3aGVuZXZlciBhIGNvbW1lbnQgaXMgc2tpcHBlZC4gYGJsb2NrYCBpcyBhXG4gIC8vIGJvb2xlYW4gaW5kaWNhdGluZyB3aGV0aGVyIHRoaXMgaXMgYSBibG9jayAoYC8qICovYCkgY29tbWVudCxcbiAgLy8gYHRleHRgIGlzIHRoZSBjb250ZW50IG9mIHRoZSBjb21tZW50LCBhbmQgYHN0YXJ0YCBhbmQgYGVuZGAgYXJlXG4gIC8vIGNoYXJhY3RlciBvZmZzZXRzIHRoYXQgZGVub3RlIHRoZSBzdGFydCBhbmQgZW5kIG9mIHRoZSBjb21tZW50LlxuICAvLyBXaGVuIHRoZSBgbG9jYXRpb25zYCBvcHRpb24gaXMgb24sIHR3byBtb3JlIHBhcmFtZXRlcnMgYXJlXG4gIC8vIHBhc3NlZCwgdGhlIGZ1bGwgYHtsaW5lLCBjb2x1bW59YCBsb2NhdGlvbnMgb2YgdGhlIHN0YXJ0IGFuZFxuICAvLyBlbmQgb2YgdGhlIGNvbW1lbnRzLiBOb3RlIHRoYXQgeW91IGFyZSBub3QgYWxsb3dlZCB0byBjYWxsIHRoZVxuICAvLyBwYXJzZXIgZnJvbSB0aGUgY2FsbGJhY2vigJR0aGF0IHdpbGwgY29ycnVwdCBpdHMgaW50ZXJuYWwgc3RhdGUuXG4gIG9uQ29tbWVudDogbnVsbCxcbiAgLy8gTm9kZXMgaGF2ZSB0aGVpciBzdGFydCBhbmQgZW5kIGNoYXJhY3RlcnMgb2Zmc2V0cyByZWNvcmRlZCBpblxuICAvLyBgc3RhcnRgIGFuZCBgZW5kYCBwcm9wZXJ0aWVzIChkaXJlY3RseSBvbiB0aGUgbm9kZSwgcmF0aGVyIHRoYW5cbiAgLy8gdGhlIGBsb2NgIG9iamVjdCwgd2hpY2ggaG9sZHMgbGluZS9jb2x1bW4gZGF0YS4gVG8gYWxzbyBhZGQgYVxuICAvLyBbc2VtaS1zdGFuZGFyZGl6ZWRdW3JhbmdlXSBgcmFuZ2VgIHByb3BlcnR5IGhvbGRpbmcgYSBgW3N0YXJ0LFxuICAvLyBlbmRdYCBhcnJheSB3aXRoIHRoZSBzYW1lIG51bWJlcnMsIHNldCB0aGUgYHJhbmdlc2Agb3B0aW9uIHRvXG4gIC8vIGB0cnVlYC5cbiAgLy9cbiAgLy8gW3JhbmdlXTogaHR0cHM6Ly9idWd6aWxsYS5tb3ppbGxhLm9yZy9zaG93X2J1Zy5jZ2k/aWQ9NzQ1Njc4XG4gIHJhbmdlczogZmFsc2UsXG4gIC8vIEl0IGlzIHBvc3NpYmxlIHRvIHBhcnNlIG11bHRpcGxlIGZpbGVzIGludG8gYSBzaW5nbGUgQVNUIGJ5XG4gIC8vIHBhc3NpbmcgdGhlIHRyZWUgcHJvZHVjZWQgYnkgcGFyc2luZyB0aGUgZmlyc3QgZmlsZSBhc1xuICAvLyBgcHJvZ3JhbWAgb3B0aW9uIGluIHN1YnNlcXVlbnQgcGFyc2VzLiBUaGlzIHdpbGwgYWRkIHRoZVxuICAvLyB0b3BsZXZlbCBmb3JtcyBvZiB0aGUgcGFyc2VkIGZpbGUgdG8gdGhlIGBQcm9ncmFtYCAodG9wKSBub2RlXG4gIC8vIG9mIGFuIGV4aXN0aW5nIHBhcnNlIHRyZWUuXG4gIHByb2dyYW06IG51bGwsXG4gIC8vIFdoZW4gYGxvY2F0aW9uc2AgaXMgb24sIHlvdSBjYW4gcGFzcyB0aGlzIHRvIHJlY29yZCB0aGUgc291cmNlXG4gIC8vIGZpbGUgaW4gZXZlcnkgbm9kZSdzIGBsb2NgIG9iamVjdC5cbiAgc291cmNlRmlsZTogbnVsbCxcbiAgLy8gVGhpcyB2YWx1ZSwgaWYgZ2l2ZW4sIGlzIHN0b3JlZCBpbiBldmVyeSBub2RlLCB3aGV0aGVyXG4gIC8vIGBsb2NhdGlvbnNgIGlzIG9uIG9yIG9mZi5cbiAgZGlyZWN0U291cmNlRmlsZTogbnVsbCxcbiAgLy8gV2hlbiBlbmFibGVkLCBwYXJlbnRoZXNpemVkIGV4cHJlc3Npb25zIGFyZSByZXByZXNlbnRlZCBieVxuICAvLyAobm9uLXN0YW5kYXJkKSBQYXJlbnRoZXNpemVkRXhwcmVzc2lvbiBub2Rlc1xuICBwcmVzZXJ2ZVBhcmVuczogZmFsc2UsXG4gIHBsdWdpbnM6IHt9XG59O2V4cG9ydHMuZGVmYXVsdE9wdGlvbnMgPSBkZWZhdWx0T3B0aW9ucztcblxuZnVuY3Rpb24gZ2V0T3B0aW9ucyhvcHRzKSB7XG4gIHZhciBvcHRpb25zID0ge307XG4gIGZvciAodmFyIG9wdCBpbiBkZWZhdWx0T3B0aW9ucykge1xuICAgIG9wdGlvbnNbb3B0XSA9IG9wdHMgJiYgaGFzKG9wdHMsIG9wdCkgPyBvcHRzW29wdF0gOiBkZWZhdWx0T3B0aW9uc1tvcHRdO1xuICB9aWYgKGlzQXJyYXkob3B0aW9ucy5vblRva2VuKSkge1xuICAgIChmdW5jdGlvbiAoKSB7XG4gICAgICB2YXIgdG9rZW5zID0gb3B0aW9ucy5vblRva2VuO1xuICAgICAgb3B0aW9ucy5vblRva2VuID0gZnVuY3Rpb24gKHRva2VuKSB7XG4gICAgICAgIHJldHVybiB0b2tlbnMucHVzaCh0b2tlbik7XG4gICAgICB9O1xuICAgIH0pKCk7XG4gIH1cbiAgaWYgKGlzQXJyYXkob3B0aW9ucy5vbkNvbW1lbnQpKSBvcHRpb25zLm9uQ29tbWVudCA9IHB1c2hDb21tZW50KG9wdGlvbnMsIG9wdGlvbnMub25Db21tZW50KTtcblxuICByZXR1cm4gb3B0aW9ucztcbn1cblxuZnVuY3Rpb24gcHVzaENvbW1lbnQob3B0aW9ucywgYXJyYXkpIHtcbiAgcmV0dXJuIGZ1bmN0aW9uIChibG9jaywgdGV4dCwgc3RhcnQsIGVuZCwgc3RhcnRMb2MsIGVuZExvYykge1xuICAgIHZhciBjb21tZW50ID0ge1xuICAgICAgdHlwZTogYmxvY2sgPyBcIkJsb2NrXCIgOiBcIkxpbmVcIixcbiAgICAgIHZhbHVlOiB0ZXh0LFxuICAgICAgc3RhcnQ6IHN0YXJ0LFxuICAgICAgZW5kOiBlbmRcbiAgICB9O1xuICAgIGlmIChvcHRpb25zLmxvY2F0aW9ucykgY29tbWVudC5sb2MgPSBuZXcgU291cmNlTG9jYXRpb24odGhpcywgc3RhcnRMb2MsIGVuZExvYyk7XG4gICAgaWYgKG9wdGlvbnMucmFuZ2VzKSBjb21tZW50LnJhbmdlID0gW3N0YXJ0LCBlbmRdO1xuICAgIGFycmF5LnB1c2goY29tbWVudCk7XG4gIH07XG59XG5cbn0se1wiLi9sb2NhdGlvblwiOjgsXCIuL3V0aWxcIjoxOH1dLDEyOltmdW5jdGlvbihfZGVyZXFfLG1vZHVsZSxleHBvcnRzKXtcblwidXNlIHN0cmljdFwiO1xuXG52YXIgdHQgPSBfZGVyZXFfKFwiLi90b2tlbnR5cGVcIikudHlwZXM7XG5cbnZhciBQYXJzZXIgPSBfZGVyZXFfKFwiLi9zdGF0ZVwiKS5QYXJzZXI7XG5cbnZhciBsaW5lQnJlYWsgPSBfZGVyZXFfKFwiLi93aGl0ZXNwYWNlXCIpLmxpbmVCcmVhaztcblxudmFyIHBwID0gUGFyc2VyLnByb3RvdHlwZTtcblxuLy8gIyMgUGFyc2VyIHV0aWxpdGllc1xuXG4vLyBUZXN0IHdoZXRoZXIgYSBzdGF0ZW1lbnQgbm9kZSBpcyB0aGUgc3RyaW5nIGxpdGVyYWwgYFwidXNlIHN0cmljdFwiYC5cblxucHAuaXNVc2VTdHJpY3QgPSBmdW5jdGlvbiAoc3RtdCkge1xuICByZXR1cm4gdGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDUgJiYgc3RtdC50eXBlID09PSBcIkV4cHJlc3Npb25TdGF0ZW1lbnRcIiAmJiBzdG10LmV4cHJlc3Npb24udHlwZSA9PT0gXCJMaXRlcmFsXCIgJiYgc3RtdC5leHByZXNzaW9uLnZhbHVlID09PSBcInVzZSBzdHJpY3RcIjtcbn07XG5cbi8vIFByZWRpY2F0ZSB0aGF0IHRlc3RzIHdoZXRoZXIgdGhlIG5leHQgdG9rZW4gaXMgb2YgdGhlIGdpdmVuXG4vLyB0eXBlLCBhbmQgaWYgeWVzLCBjb25zdW1lcyBpdCBhcyBhIHNpZGUgZWZmZWN0LlxuXG5wcC5lYXQgPSBmdW5jdGlvbiAodHlwZSkge1xuICBpZiAodGhpcy50eXBlID09PSB0eXBlKSB7XG4gICAgdGhpcy5uZXh0KCk7XG4gICAgcmV0dXJuIHRydWU7XG4gIH0gZWxzZSB7XG4gICAgcmV0dXJuIGZhbHNlO1xuICB9XG59O1xuXG4vLyBUZXN0cyB3aGV0aGVyIHBhcnNlZCB0b2tlbiBpcyBhIGNvbnRleHR1YWwga2V5d29yZC5cblxucHAuaXNDb250ZXh0dWFsID0gZnVuY3Rpb24gKG5hbWUpIHtcbiAgcmV0dXJuIHRoaXMudHlwZSA9PT0gdHQubmFtZSAmJiB0aGlzLnZhbHVlID09PSBuYW1lO1xufTtcblxuLy8gQ29uc3VtZXMgY29udGV4dHVhbCBrZXl3b3JkIGlmIHBvc3NpYmxlLlxuXG5wcC5lYXRDb250ZXh0dWFsID0gZnVuY3Rpb24gKG5hbWUpIHtcbiAgcmV0dXJuIHRoaXMudmFsdWUgPT09IG5hbWUgJiYgdGhpcy5lYXQodHQubmFtZSk7XG59O1xuXG4vLyBBc3NlcnRzIHRoYXQgZm9sbG93aW5nIHRva2VuIGlzIGdpdmVuIGNvbnRleHR1YWwga2V5d29yZC5cblxucHAuZXhwZWN0Q29udGV4dHVhbCA9IGZ1bmN0aW9uIChuYW1lKSB7XG4gIGlmICghdGhpcy5lYXRDb250ZXh0dWFsKG5hbWUpKSB0aGlzLnVuZXhwZWN0ZWQoKTtcbn07XG5cbi8vIFRlc3Qgd2hldGhlciBhIHNlbWljb2xvbiBjYW4gYmUgaW5zZXJ0ZWQgYXQgdGhlIGN1cnJlbnQgcG9zaXRpb24uXG5cbnBwLmNhbkluc2VydFNlbWljb2xvbiA9IGZ1bmN0aW9uICgpIHtcbiAgcmV0dXJuIHRoaXMudHlwZSA9PT0gdHQuZW9mIHx8IHRoaXMudHlwZSA9PT0gdHQuYnJhY2VSIHx8IGxpbmVCcmVhay50ZXN0KHRoaXMuaW5wdXQuc2xpY2UodGhpcy5sYXN0VG9rRW5kLCB0aGlzLnN0YXJ0KSk7XG59O1xuXG5wcC5pbnNlcnRTZW1pY29sb24gPSBmdW5jdGlvbiAoKSB7XG4gIGlmICh0aGlzLmNhbkluc2VydFNlbWljb2xvbigpKSB7XG4gICAgaWYgKHRoaXMub3B0aW9ucy5vbkluc2VydGVkU2VtaWNvbG9uKSB0aGlzLm9wdGlvbnMub25JbnNlcnRlZFNlbWljb2xvbih0aGlzLmxhc3RUb2tFbmQsIHRoaXMubGFzdFRva0VuZExvYyk7XG4gICAgcmV0dXJuIHRydWU7XG4gIH1cbn07XG5cbi8vIENvbnN1bWUgYSBzZW1pY29sb24sIG9yLCBmYWlsaW5nIHRoYXQsIHNlZSBpZiB3ZSBhcmUgYWxsb3dlZCB0b1xuLy8gcHJldGVuZCB0aGF0IHRoZXJlIGlzIGEgc2VtaWNvbG9uIGF0IHRoaXMgcG9zaXRpb24uXG5cbnBwLnNlbWljb2xvbiA9IGZ1bmN0aW9uICgpIHtcbiAgaWYgKCF0aGlzLmVhdCh0dC5zZW1pKSAmJiAhdGhpcy5pbnNlcnRTZW1pY29sb24oKSkgdGhpcy51bmV4cGVjdGVkKCk7XG59O1xuXG5wcC5hZnRlclRyYWlsaW5nQ29tbWEgPSBmdW5jdGlvbiAodG9rVHlwZSkge1xuICBpZiAodGhpcy50eXBlID09IHRva1R5cGUpIHtcbiAgICBpZiAodGhpcy5vcHRpb25zLm9uVHJhaWxpbmdDb21tYSkgdGhpcy5vcHRpb25zLm9uVHJhaWxpbmdDb21tYSh0aGlzLmxhc3RUb2tTdGFydCwgdGhpcy5sYXN0VG9rU3RhcnRMb2MpO1xuICAgIHRoaXMubmV4dCgpO1xuICAgIHJldHVybiB0cnVlO1xuICB9XG59O1xuXG4vLyBFeHBlY3QgYSB0b2tlbiBvZiBhIGdpdmVuIHR5cGUuIElmIGZvdW5kLCBjb25zdW1lIGl0LCBvdGhlcndpc2UsXG4vLyByYWlzZSBhbiB1bmV4cGVjdGVkIHRva2VuIGVycm9yLlxuXG5wcC5leHBlY3QgPSBmdW5jdGlvbiAodHlwZSkge1xuICB0aGlzLmVhdCh0eXBlKSB8fCB0aGlzLnVuZXhwZWN0ZWQoKTtcbn07XG5cbi8vIFJhaXNlIGFuIHVuZXhwZWN0ZWQgdG9rZW4gZXJyb3IuXG5cbnBwLnVuZXhwZWN0ZWQgPSBmdW5jdGlvbiAocG9zKSB7XG4gIHRoaXMucmFpc2UocG9zICE9IG51bGwgPyBwb3MgOiB0aGlzLnN0YXJ0LCBcIlVuZXhwZWN0ZWQgdG9rZW5cIik7XG59O1xuXG59LHtcIi4vc3RhdGVcIjoxMyxcIi4vdG9rZW50eXBlXCI6MTcsXCIuL3doaXRlc3BhY2VcIjoxOX1dLDEzOltmdW5jdGlvbihfZGVyZXFfLG1vZHVsZSxleHBvcnRzKXtcblwidXNlIHN0cmljdFwiO1xuXG5leHBvcnRzLlBhcnNlciA9IFBhcnNlcjtcbmV4cG9ydHMuX19lc01vZHVsZSA9IHRydWU7XG5cbnZhciBfaWRlbnRpZmllciA9IF9kZXJlcV8oXCIuL2lkZW50aWZpZXJcIik7XG5cbnZhciByZXNlcnZlZFdvcmRzID0gX2lkZW50aWZpZXIucmVzZXJ2ZWRXb3JkcztcbnZhciBrZXl3b3JkcyA9IF9pZGVudGlmaWVyLmtleXdvcmRzO1xuXG52YXIgdHQgPSBfZGVyZXFfKFwiLi90b2tlbnR5cGVcIikudHlwZXM7XG5cbnZhciBsaW5lQnJlYWsgPSBfZGVyZXFfKFwiLi93aGl0ZXNwYWNlXCIpLmxpbmVCcmVhaztcblxuZnVuY3Rpb24gUGFyc2VyKG9wdGlvbnMsIGlucHV0LCBzdGFydFBvcykge1xuICB0aGlzLm9wdGlvbnMgPSBvcHRpb25zO1xuICB0aGlzLnNvdXJjZUZpbGUgPSB0aGlzLm9wdGlvbnMuc291cmNlRmlsZSB8fCBudWxsO1xuICB0aGlzLmlzS2V5d29yZCA9IGtleXdvcmRzW3RoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2ID8gNiA6IDVdO1xuICB0aGlzLmlzUmVzZXJ2ZWRXb3JkID0gcmVzZXJ2ZWRXb3Jkc1t0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb25dO1xuICB0aGlzLmlucHV0ID0gaW5wdXQ7XG5cbiAgLy8gTG9hZCBwbHVnaW5zXG4gIHRoaXMubG9hZFBsdWdpbnModGhpcy5vcHRpb25zLnBsdWdpbnMpO1xuXG4gIC8vIFNldCB1cCB0b2tlbiBzdGF0ZVxuXG4gIC8vIFRoZSBjdXJyZW50IHBvc2l0aW9uIG9mIHRoZSB0b2tlbml6ZXIgaW4gdGhlIGlucHV0LlxuICBpZiAoc3RhcnRQb3MpIHtcbiAgICB0aGlzLnBvcyA9IHN0YXJ0UG9zO1xuICAgIHRoaXMubGluZVN0YXJ0ID0gTWF0aC5tYXgoMCwgdGhpcy5pbnB1dC5sYXN0SW5kZXhPZihcIlxcblwiLCBzdGFydFBvcykpO1xuICAgIHRoaXMuY3VyTGluZSA9IHRoaXMuaW5wdXQuc2xpY2UoMCwgdGhpcy5saW5lU3RhcnQpLnNwbGl0KGxpbmVCcmVhaykubGVuZ3RoO1xuICB9IGVsc2Uge1xuICAgIHRoaXMucG9zID0gdGhpcy5saW5lU3RhcnQgPSAwO1xuICAgIHRoaXMuY3VyTGluZSA9IDE7XG4gIH1cblxuICAvLyBQcm9wZXJ0aWVzIG9mIHRoZSBjdXJyZW50IHRva2VuOlxuICAvLyBJdHMgdHlwZVxuICB0aGlzLnR5cGUgPSB0dC5lb2Y7XG4gIC8vIEZvciB0b2tlbnMgdGhhdCBpbmNsdWRlIG1vcmUgaW5mb3JtYXRpb24gdGhhbiB0aGVpciB0eXBlLCB0aGUgdmFsdWVcbiAgdGhpcy52YWx1ZSA9IG51bGw7XG4gIC8vIEl0cyBzdGFydCBhbmQgZW5kIG9mZnNldFxuICB0aGlzLnN0YXJ0ID0gdGhpcy5lbmQgPSB0aGlzLnBvcztcbiAgLy8gQW5kLCBpZiBsb2NhdGlvbnMgYXJlIHVzZWQsIHRoZSB7bGluZSwgY29sdW1ufSBvYmplY3RcbiAgLy8gY29ycmVzcG9uZGluZyB0byB0aG9zZSBvZmZzZXRzXG4gIHRoaXMuc3RhcnRMb2MgPSB0aGlzLmVuZExvYyA9IG51bGw7XG5cbiAgLy8gUG9zaXRpb24gaW5mb3JtYXRpb24gZm9yIHRoZSBwcmV2aW91cyB0b2tlblxuICB0aGlzLmxhc3RUb2tFbmRMb2MgPSB0aGlzLmxhc3RUb2tTdGFydExvYyA9IG51bGw7XG4gIHRoaXMubGFzdFRva1N0YXJ0ID0gdGhpcy5sYXN0VG9rRW5kID0gdGhpcy5wb3M7XG5cbiAgLy8gVGhlIGNvbnRleHQgc3RhY2sgaXMgdXNlZCB0byBzdXBlcmZpY2lhbGx5IHRyYWNrIHN5bnRhY3RpY1xuICAvLyBjb250ZXh0IHRvIHByZWRpY3Qgd2hldGhlciBhIHJlZ3VsYXIgZXhwcmVzc2lvbiBpcyBhbGxvd2VkIGluIGFcbiAgLy8gZ2l2ZW4gcG9zaXRpb24uXG4gIHRoaXMuY29udGV4dCA9IHRoaXMuaW5pdGlhbENvbnRleHQoKTtcbiAgdGhpcy5leHByQWxsb3dlZCA9IHRydWU7XG5cbiAgLy8gRmlndXJlIG91dCBpZiBpdCdzIGEgbW9kdWxlIGNvZGUuXG4gIHRoaXMuc3RyaWN0ID0gdGhpcy5pbk1vZHVsZSA9IHRoaXMub3B0aW9ucy5zb3VyY2VUeXBlID09PSBcIm1vZHVsZVwiO1xuXG4gIC8vIFVzZWQgdG8gc2lnbmlmeSB0aGUgc3RhcnQgb2YgYSBwb3RlbnRpYWwgYXJyb3cgZnVuY3Rpb25cbiAgdGhpcy5wb3RlbnRpYWxBcnJvd0F0ID0gLTE7XG5cbiAgLy8gRmxhZ3MgdG8gdHJhY2sgd2hldGhlciB3ZSBhcmUgaW4gYSBmdW5jdGlvbiwgYSBnZW5lcmF0b3IuXG4gIHRoaXMuaW5GdW5jdGlvbiA9IHRoaXMuaW5HZW5lcmF0b3IgPSBmYWxzZTtcbiAgLy8gTGFiZWxzIGluIHNjb3BlLlxuICB0aGlzLmxhYmVscyA9IFtdO1xuXG4gIC8vIElmIGVuYWJsZWQsIHNraXAgbGVhZGluZyBoYXNoYmFuZyBsaW5lLlxuICBpZiAodGhpcy5wb3MgPT09IDAgJiYgdGhpcy5vcHRpb25zLmFsbG93SGFzaEJhbmcgJiYgdGhpcy5pbnB1dC5zbGljZSgwLCAyKSA9PT0gXCIjIVwiKSB0aGlzLnNraXBMaW5lQ29tbWVudCgyKTtcbn1cblxuUGFyc2VyLnByb3RvdHlwZS5leHRlbmQgPSBmdW5jdGlvbiAobmFtZSwgZikge1xuICB0aGlzW25hbWVdID0gZih0aGlzW25hbWVdKTtcbn07XG5cbi8vIFJlZ2lzdGVyZWQgcGx1Z2luc1xuXG52YXIgcGx1Z2lucyA9IHt9O1xuXG5leHBvcnRzLnBsdWdpbnMgPSBwbHVnaW5zO1xuUGFyc2VyLnByb3RvdHlwZS5sb2FkUGx1Z2lucyA9IGZ1bmN0aW9uIChwbHVnaW5zKSB7XG4gIGZvciAodmFyIF9uYW1lIGluIHBsdWdpbnMpIHtcbiAgICB2YXIgcGx1Z2luID0gZXhwb3J0cy5wbHVnaW5zW19uYW1lXTtcbiAgICBpZiAoIXBsdWdpbikgdGhyb3cgbmV3IEVycm9yKFwiUGx1Z2luICdcIiArIF9uYW1lICsgXCInIG5vdCBmb3VuZFwiKTtcbiAgICBwbHVnaW4odGhpcywgcGx1Z2luc1tfbmFtZV0pO1xuICB9XG59O1xuXG59LHtcIi4vaWRlbnRpZmllclwiOjcsXCIuL3Rva2VudHlwZVwiOjE3LFwiLi93aGl0ZXNwYWNlXCI6MTl9XSwxNDpbZnVuY3Rpb24oX2RlcmVxXyxtb2R1bGUsZXhwb3J0cyl7XG5cInVzZSBzdHJpY3RcIjtcblxudmFyIHR0ID0gX2RlcmVxXyhcIi4vdG9rZW50eXBlXCIpLnR5cGVzO1xuXG52YXIgUGFyc2VyID0gX2RlcmVxXyhcIi4vc3RhdGVcIikuUGFyc2VyO1xuXG52YXIgbGluZUJyZWFrID0gX2RlcmVxXyhcIi4vd2hpdGVzcGFjZVwiKS5saW5lQnJlYWs7XG5cbnZhciBwcCA9IFBhcnNlci5wcm90b3R5cGU7XG5cbi8vICMjIyBTdGF0ZW1lbnQgcGFyc2luZ1xuXG4vLyBQYXJzZSBhIHByb2dyYW0uIEluaXRpYWxpemVzIHRoZSBwYXJzZXIsIHJlYWRzIGFueSBudW1iZXIgb2Zcbi8vIHN0YXRlbWVudHMsIGFuZCB3cmFwcyB0aGVtIGluIGEgUHJvZ3JhbSBub2RlLiAgT3B0aW9uYWxseSB0YWtlcyBhXG4vLyBgcHJvZ3JhbWAgYXJndW1lbnQuICBJZiBwcmVzZW50LCB0aGUgc3RhdGVtZW50cyB3aWxsIGJlIGFwcGVuZGVkXG4vLyB0byBpdHMgYm9keSBpbnN0ZWFkIG9mIGNyZWF0aW5nIGEgbmV3IG5vZGUuXG5cbnBwLnBhcnNlVG9wTGV2ZWwgPSBmdW5jdGlvbiAobm9kZSkge1xuICB2YXIgZmlyc3QgPSB0cnVlO1xuICBpZiAoIW5vZGUuYm9keSkgbm9kZS5ib2R5ID0gW107XG4gIHdoaWxlICh0aGlzLnR5cGUgIT09IHR0LmVvZikge1xuICAgIHZhciBzdG10ID0gdGhpcy5wYXJzZVN0YXRlbWVudCh0cnVlLCB0cnVlKTtcbiAgICBub2RlLmJvZHkucHVzaChzdG10KTtcbiAgICBpZiAoZmlyc3QgJiYgdGhpcy5pc1VzZVN0cmljdChzdG10KSkgdGhpcy5zZXRTdHJpY3QodHJ1ZSk7XG4gICAgZmlyc3QgPSBmYWxzZTtcbiAgfVxuICB0aGlzLm5leHQoKTtcbiAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KSB7XG4gICAgbm9kZS5zb3VyY2VUeXBlID0gdGhpcy5vcHRpb25zLnNvdXJjZVR5cGU7XG4gIH1cbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIlByb2dyYW1cIik7XG59O1xuXG52YXIgbG9vcExhYmVsID0geyBraW5kOiBcImxvb3BcIiB9LFxuICAgIHN3aXRjaExhYmVsID0geyBraW5kOiBcInN3aXRjaFwiIH07XG5cbi8vIFBhcnNlIGEgc2luZ2xlIHN0YXRlbWVudC5cbi8vXG4vLyBJZiBleHBlY3RpbmcgYSBzdGF0ZW1lbnQgYW5kIGZpbmRpbmcgYSBzbGFzaCBvcGVyYXRvciwgcGFyc2UgYVxuLy8gcmVndWxhciBleHByZXNzaW9uIGxpdGVyYWwuIFRoaXMgaXMgdG8gaGFuZGxlIGNhc2VzIGxpa2Vcbi8vIGBpZiAoZm9vKSAvYmxhaC8uZXhlYyhmb28pYCwgd2hlcmUgbG9va2luZyBhdCB0aGUgcHJldmlvdXMgdG9rZW5cbi8vIGRvZXMgbm90IGhlbHAuXG5cbnBwLnBhcnNlU3RhdGVtZW50ID0gZnVuY3Rpb24gKGRlY2xhcmF0aW9uLCB0b3BMZXZlbCkge1xuICB2YXIgc3RhcnR0eXBlID0gdGhpcy50eXBlLFxuICAgICAgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG5cbiAgLy8gTW9zdCB0eXBlcyBvZiBzdGF0ZW1lbnRzIGFyZSByZWNvZ25pemVkIGJ5IHRoZSBrZXl3b3JkIHRoZXlcbiAgLy8gc3RhcnQgd2l0aC4gTWFueSBhcmUgdHJpdmlhbCB0byBwYXJzZSwgc29tZSByZXF1aXJlIGEgYml0IG9mXG4gIC8vIGNvbXBsZXhpdHkuXG5cbiAgc3dpdGNoIChzdGFydHR5cGUpIHtcbiAgICBjYXNlIHR0Ll9icmVhazpjYXNlIHR0Ll9jb250aW51ZTpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlQnJlYWtDb250aW51ZVN0YXRlbWVudChub2RlLCBzdGFydHR5cGUua2V5d29yZCk7XG4gICAgY2FzZSB0dC5fZGVidWdnZXI6XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZURlYnVnZ2VyU3RhdGVtZW50KG5vZGUpO1xuICAgIGNhc2UgdHQuX2RvOlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VEb1N0YXRlbWVudChub2RlKTtcbiAgICBjYXNlIHR0Ll9mb3I6XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZUZvclN0YXRlbWVudChub2RlKTtcbiAgICBjYXNlIHR0Ll9mdW5jdGlvbjpcbiAgICAgIGlmICghZGVjbGFyYXRpb24gJiYgdGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYpIHRoaXMudW5leHBlY3RlZCgpO1xuICAgICAgcmV0dXJuIHRoaXMucGFyc2VGdW5jdGlvblN0YXRlbWVudChub2RlKTtcbiAgICBjYXNlIHR0Ll9jbGFzczpcbiAgICAgIGlmICghZGVjbGFyYXRpb24pIHRoaXMudW5leHBlY3RlZCgpO1xuICAgICAgcmV0dXJuIHRoaXMucGFyc2VDbGFzcyhub2RlLCB0cnVlKTtcbiAgICBjYXNlIHR0Ll9pZjpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlSWZTdGF0ZW1lbnQobm9kZSk7XG4gICAgY2FzZSB0dC5fcmV0dXJuOlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VSZXR1cm5TdGF0ZW1lbnQobm9kZSk7XG4gICAgY2FzZSB0dC5fc3dpdGNoOlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VTd2l0Y2hTdGF0ZW1lbnQobm9kZSk7XG4gICAgY2FzZSB0dC5fdGhyb3c6XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZVRocm93U3RhdGVtZW50KG5vZGUpO1xuICAgIGNhc2UgdHQuX3RyeTpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlVHJ5U3RhdGVtZW50KG5vZGUpO1xuICAgIGNhc2UgdHQuX2xldDpjYXNlIHR0Ll9jb25zdDpcbiAgICAgIGlmICghZGVjbGFyYXRpb24pIHRoaXMudW5leHBlY3RlZCgpOyAvLyBOT1RFOiBmYWxscyB0aHJvdWdoIHRvIF92YXJcbiAgICBjYXNlIHR0Ll92YXI6XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZVZhclN0YXRlbWVudChub2RlLCBzdGFydHR5cGUpO1xuICAgIGNhc2UgdHQuX3doaWxlOlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VXaGlsZVN0YXRlbWVudChub2RlKTtcbiAgICBjYXNlIHR0Ll93aXRoOlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VXaXRoU3RhdGVtZW50KG5vZGUpO1xuICAgIGNhc2UgdHQuYnJhY2VMOlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VCbG9jaygpO1xuICAgIGNhc2UgdHQuc2VtaTpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlRW1wdHlTdGF0ZW1lbnQobm9kZSk7XG4gICAgY2FzZSB0dC5fZXhwb3J0OlxuICAgIGNhc2UgdHQuX2ltcG9ydDpcbiAgICAgIGlmICghdGhpcy5vcHRpb25zLmFsbG93SW1wb3J0RXhwb3J0RXZlcnl3aGVyZSkge1xuICAgICAgICBpZiAoIXRvcExldmVsKSB0aGlzLnJhaXNlKHRoaXMuc3RhcnQsIFwiJ2ltcG9ydCcgYW5kICdleHBvcnQnIG1heSBvbmx5IGFwcGVhciBhdCB0aGUgdG9wIGxldmVsXCIpO1xuICAgICAgICBpZiAoIXRoaXMuaW5Nb2R1bGUpIHRoaXMucmFpc2UodGhpcy5zdGFydCwgXCInaW1wb3J0JyBhbmQgJ2V4cG9ydCcgbWF5IGFwcGVhciBvbmx5IHdpdGggJ3NvdXJjZVR5cGU6IG1vZHVsZSdcIik7XG4gICAgICB9XG4gICAgICByZXR1cm4gc3RhcnR0eXBlID09PSB0dC5faW1wb3J0ID8gdGhpcy5wYXJzZUltcG9ydChub2RlKSA6IHRoaXMucGFyc2VFeHBvcnQobm9kZSk7XG5cbiAgICAvLyBJZiB0aGUgc3RhdGVtZW50IGRvZXMgbm90IHN0YXJ0IHdpdGggYSBzdGF0ZW1lbnQga2V5d29yZCBvciBhXG4gICAgLy8gYnJhY2UsIGl0J3MgYW4gRXhwcmVzc2lvblN0YXRlbWVudCBvciBMYWJlbGVkU3RhdGVtZW50LiBXZVxuICAgIC8vIHNpbXBseSBzdGFydCBwYXJzaW5nIGFuIGV4cHJlc3Npb24sIGFuZCBhZnRlcndhcmRzLCBpZiB0aGVcbiAgICAvLyBuZXh0IHRva2VuIGlzIGEgY29sb24gYW5kIHRoZSBleHByZXNzaW9uIHdhcyBhIHNpbXBsZVxuICAgIC8vIElkZW50aWZpZXIgbm9kZSwgd2Ugc3dpdGNoIHRvIGludGVycHJldGluZyBpdCBhcyBhIGxhYmVsLlxuICAgIGRlZmF1bHQ6XG4gICAgICB2YXIgbWF5YmVOYW1lID0gdGhpcy52YWx1ZSxcbiAgICAgICAgICBleHByID0gdGhpcy5wYXJzZUV4cHJlc3Npb24oKTtcbiAgICAgIGlmIChzdGFydHR5cGUgPT09IHR0Lm5hbWUgJiYgZXhwci50eXBlID09PSBcIklkZW50aWZpZXJcIiAmJiB0aGlzLmVhdCh0dC5jb2xvbikpIHJldHVybiB0aGlzLnBhcnNlTGFiZWxlZFN0YXRlbWVudChub2RlLCBtYXliZU5hbWUsIGV4cHIpO2Vsc2UgcmV0dXJuIHRoaXMucGFyc2VFeHByZXNzaW9uU3RhdGVtZW50KG5vZGUsIGV4cHIpO1xuICB9XG59O1xuXG5wcC5wYXJzZUJyZWFrQ29udGludWVTdGF0ZW1lbnQgPSBmdW5jdGlvbiAobm9kZSwga2V5d29yZCkge1xuICB2YXIgaXNCcmVhayA9IGtleXdvcmQgPT0gXCJicmVha1wiO1xuICB0aGlzLm5leHQoKTtcbiAgaWYgKHRoaXMuZWF0KHR0LnNlbWkpIHx8IHRoaXMuaW5zZXJ0U2VtaWNvbG9uKCkpIG5vZGUubGFiZWwgPSBudWxsO2Vsc2UgaWYgKHRoaXMudHlwZSAhPT0gdHQubmFtZSkgdGhpcy51bmV4cGVjdGVkKCk7ZWxzZSB7XG4gICAgbm9kZS5sYWJlbCA9IHRoaXMucGFyc2VJZGVudCgpO1xuICAgIHRoaXMuc2VtaWNvbG9uKCk7XG4gIH1cblxuICAvLyBWZXJpZnkgdGhhdCB0aGVyZSBpcyBhbiBhY3R1YWwgZGVzdGluYXRpb24gdG8gYnJlYWsgb3JcbiAgLy8gY29udGludWUgdG8uXG4gIGZvciAodmFyIGkgPSAwOyBpIDwgdGhpcy5sYWJlbHMubGVuZ3RoOyArK2kpIHtcbiAgICB2YXIgbGFiID0gdGhpcy5sYWJlbHNbaV07XG4gICAgaWYgKG5vZGUubGFiZWwgPT0gbnVsbCB8fCBsYWIubmFtZSA9PT0gbm9kZS5sYWJlbC5uYW1lKSB7XG4gICAgICBpZiAobGFiLmtpbmQgIT0gbnVsbCAmJiAoaXNCcmVhayB8fCBsYWIua2luZCA9PT0gXCJsb29wXCIpKSBicmVhaztcbiAgICAgIGlmIChub2RlLmxhYmVsICYmIGlzQnJlYWspIGJyZWFrO1xuICAgIH1cbiAgfVxuICBpZiAoaSA9PT0gdGhpcy5sYWJlbHMubGVuZ3RoKSB0aGlzLnJhaXNlKG5vZGUuc3RhcnQsIFwiVW5zeW50YWN0aWMgXCIgKyBrZXl3b3JkKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBpc0JyZWFrID8gXCJCcmVha1N0YXRlbWVudFwiIDogXCJDb250aW51ZVN0YXRlbWVudFwiKTtcbn07XG5cbnBwLnBhcnNlRGVidWdnZXJTdGF0ZW1lbnQgPSBmdW5jdGlvbiAobm9kZSkge1xuICB0aGlzLm5leHQoKTtcbiAgdGhpcy5zZW1pY29sb24oKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkRlYnVnZ2VyU3RhdGVtZW50XCIpO1xufTtcblxucHAucGFyc2VEb1N0YXRlbWVudCA9IGZ1bmN0aW9uIChub2RlKSB7XG4gIHRoaXMubmV4dCgpO1xuICB0aGlzLmxhYmVscy5wdXNoKGxvb3BMYWJlbCk7XG4gIG5vZGUuYm9keSA9IHRoaXMucGFyc2VTdGF0ZW1lbnQoZmFsc2UpO1xuICB0aGlzLmxhYmVscy5wb3AoKTtcbiAgdGhpcy5leHBlY3QodHQuX3doaWxlKTtcbiAgbm9kZS50ZXN0ID0gdGhpcy5wYXJzZVBhcmVuRXhwcmVzc2lvbigpO1xuICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYpIHRoaXMuZWF0KHR0LnNlbWkpO2Vsc2UgdGhpcy5zZW1pY29sb24oKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkRvV2hpbGVTdGF0ZW1lbnRcIik7XG59O1xuXG4vLyBEaXNhbWJpZ3VhdGluZyBiZXR3ZWVuIGEgYGZvcmAgYW5kIGEgYGZvcmAvYGluYCBvciBgZm9yYC9gb2ZgXG4vLyBsb29wIGlzIG5vbi10cml2aWFsLiBCYXNpY2FsbHksIHdlIGhhdmUgdG8gcGFyc2UgdGhlIGluaXQgYHZhcmBcbi8vIHN0YXRlbWVudCBvciBleHByZXNzaW9uLCBkaXNhbGxvd2luZyB0aGUgYGluYCBvcGVyYXRvciAoc2VlXG4vLyB0aGUgc2Vjb25kIHBhcmFtZXRlciB0byBgcGFyc2VFeHByZXNzaW9uYCksIGFuZCB0aGVuIGNoZWNrXG4vLyB3aGV0aGVyIHRoZSBuZXh0IHRva2VuIGlzIGBpbmAgb3IgYG9mYC4gV2hlbiB0aGVyZSBpcyBubyBpbml0XG4vLyBwYXJ0IChzZW1pY29sb24gaW1tZWRpYXRlbHkgYWZ0ZXIgdGhlIG9wZW5pbmcgcGFyZW50aGVzaXMpLCBpdFxuLy8gaXMgYSByZWd1bGFyIGBmb3JgIGxvb3AuXG5cbnBwLnBhcnNlRm9yU3RhdGVtZW50ID0gZnVuY3Rpb24gKG5vZGUpIHtcbiAgdGhpcy5uZXh0KCk7XG4gIHRoaXMubGFiZWxzLnB1c2gobG9vcExhYmVsKTtcbiAgdGhpcy5leHBlY3QodHQucGFyZW5MKTtcbiAgaWYgKHRoaXMudHlwZSA9PT0gdHQuc2VtaSkgcmV0dXJuIHRoaXMucGFyc2VGb3Iobm9kZSwgbnVsbCk7XG4gIGlmICh0aGlzLnR5cGUgPT09IHR0Ll92YXIgfHwgdGhpcy50eXBlID09PSB0dC5fbGV0IHx8IHRoaXMudHlwZSA9PT0gdHQuX2NvbnN0KSB7XG4gICAgdmFyIF9pbml0ID0gdGhpcy5zdGFydE5vZGUoKSxcbiAgICAgICAgdmFyS2luZCA9IHRoaXMudHlwZTtcbiAgICB0aGlzLm5leHQoKTtcbiAgICB0aGlzLnBhcnNlVmFyKF9pbml0LCB0cnVlLCB2YXJLaW5kKTtcbiAgICB0aGlzLmZpbmlzaE5vZGUoX2luaXQsIFwiVmFyaWFibGVEZWNsYXJhdGlvblwiKTtcbiAgICBpZiAoKHRoaXMudHlwZSA9PT0gdHQuX2luIHx8IHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2ICYmIHRoaXMuaXNDb250ZXh0dWFsKFwib2ZcIikpICYmIF9pbml0LmRlY2xhcmF0aW9ucy5sZW5ndGggPT09IDEgJiYgISh2YXJLaW5kICE9PSB0dC5fdmFyICYmIF9pbml0LmRlY2xhcmF0aW9uc1swXS5pbml0KSkgcmV0dXJuIHRoaXMucGFyc2VGb3JJbihub2RlLCBfaW5pdCk7XG4gICAgcmV0dXJuIHRoaXMucGFyc2VGb3Iobm9kZSwgX2luaXQpO1xuICB9XG4gIHZhciByZWZTaG9ydGhhbmREZWZhdWx0UG9zID0geyBzdGFydDogMCB9O1xuICB2YXIgaW5pdCA9IHRoaXMucGFyc2VFeHByZXNzaW9uKHRydWUsIHJlZlNob3J0aGFuZERlZmF1bHRQb3MpO1xuICBpZiAodGhpcy50eXBlID09PSB0dC5faW4gfHwgdGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYgJiYgdGhpcy5pc0NvbnRleHR1YWwoXCJvZlwiKSkge1xuICAgIHRoaXMudG9Bc3NpZ25hYmxlKGluaXQpO1xuICAgIHRoaXMuY2hlY2tMVmFsKGluaXQpO1xuICAgIHJldHVybiB0aGlzLnBhcnNlRm9ySW4obm9kZSwgaW5pdCk7XG4gIH0gZWxzZSBpZiAocmVmU2hvcnRoYW5kRGVmYXVsdFBvcy5zdGFydCkge1xuICAgIHRoaXMudW5leHBlY3RlZChyZWZTaG9ydGhhbmREZWZhdWx0UG9zLnN0YXJ0KTtcbiAgfVxuICByZXR1cm4gdGhpcy5wYXJzZUZvcihub2RlLCBpbml0KTtcbn07XG5cbnBwLnBhcnNlRnVuY3Rpb25TdGF0ZW1lbnQgPSBmdW5jdGlvbiAobm9kZSkge1xuICB0aGlzLm5leHQoKTtcbiAgcmV0dXJuIHRoaXMucGFyc2VGdW5jdGlvbihub2RlLCB0cnVlKTtcbn07XG5cbnBwLnBhcnNlSWZTdGF0ZW1lbnQgPSBmdW5jdGlvbiAobm9kZSkge1xuICB0aGlzLm5leHQoKTtcbiAgbm9kZS50ZXN0ID0gdGhpcy5wYXJzZVBhcmVuRXhwcmVzc2lvbigpO1xuICBub2RlLmNvbnNlcXVlbnQgPSB0aGlzLnBhcnNlU3RhdGVtZW50KGZhbHNlKTtcbiAgbm9kZS5hbHRlcm5hdGUgPSB0aGlzLmVhdCh0dC5fZWxzZSkgPyB0aGlzLnBhcnNlU3RhdGVtZW50KGZhbHNlKSA6IG51bGw7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJJZlN0YXRlbWVudFwiKTtcbn07XG5cbnBwLnBhcnNlUmV0dXJuU3RhdGVtZW50ID0gZnVuY3Rpb24gKG5vZGUpIHtcbiAgaWYgKCF0aGlzLmluRnVuY3Rpb24gJiYgIXRoaXMub3B0aW9ucy5hbGxvd1JldHVybk91dHNpZGVGdW5jdGlvbikgdGhpcy5yYWlzZSh0aGlzLnN0YXJ0LCBcIidyZXR1cm4nIG91dHNpZGUgb2YgZnVuY3Rpb25cIik7XG4gIHRoaXMubmV4dCgpO1xuXG4gIC8vIEluIGByZXR1cm5gIChhbmQgYGJyZWFrYC9gY29udGludWVgKSwgdGhlIGtleXdvcmRzIHdpdGhcbiAgLy8gb3B0aW9uYWwgYXJndW1lbnRzLCB3ZSBlYWdlcmx5IGxvb2sgZm9yIGEgc2VtaWNvbG9uIG9yIHRoZVxuICAvLyBwb3NzaWJpbGl0eSB0byBpbnNlcnQgb25lLlxuXG4gIGlmICh0aGlzLmVhdCh0dC5zZW1pKSB8fCB0aGlzLmluc2VydFNlbWljb2xvbigpKSBub2RlLmFyZ3VtZW50ID0gbnVsbDtlbHNlIHtcbiAgICBub2RlLmFyZ3VtZW50ID0gdGhpcy5wYXJzZUV4cHJlc3Npb24oKTt0aGlzLnNlbWljb2xvbigpO1xuICB9XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJSZXR1cm5TdGF0ZW1lbnRcIik7XG59O1xuXG5wcC5wYXJzZVN3aXRjaFN0YXRlbWVudCA9IGZ1bmN0aW9uIChub2RlKSB7XG4gIHRoaXMubmV4dCgpO1xuICBub2RlLmRpc2NyaW1pbmFudCA9IHRoaXMucGFyc2VQYXJlbkV4cHJlc3Npb24oKTtcbiAgbm9kZS5jYXNlcyA9IFtdO1xuICB0aGlzLmV4cGVjdCh0dC5icmFjZUwpO1xuICB0aGlzLmxhYmVscy5wdXNoKHN3aXRjaExhYmVsKTtcblxuICAvLyBTdGF0ZW1lbnRzIHVuZGVyIG11c3QgYmUgZ3JvdXBlZCAoYnkgbGFiZWwpIGluIFN3aXRjaENhc2VcbiAgLy8gbm9kZXMuIGBjdXJgIGlzIHVzZWQgdG8ga2VlcCB0aGUgbm9kZSB0aGF0IHdlIGFyZSBjdXJyZW50bHlcbiAgLy8gYWRkaW5nIHN0YXRlbWVudHMgdG8uXG5cbiAgZm9yICh2YXIgY3VyLCBzYXdEZWZhdWx0OyB0aGlzLnR5cGUgIT0gdHQuYnJhY2VSOykge1xuICAgIGlmICh0aGlzLnR5cGUgPT09IHR0Ll9jYXNlIHx8IHRoaXMudHlwZSA9PT0gdHQuX2RlZmF1bHQpIHtcbiAgICAgIHZhciBpc0Nhc2UgPSB0aGlzLnR5cGUgPT09IHR0Ll9jYXNlO1xuICAgICAgaWYgKGN1cikgdGhpcy5maW5pc2hOb2RlKGN1ciwgXCJTd2l0Y2hDYXNlXCIpO1xuICAgICAgbm9kZS5jYXNlcy5wdXNoKGN1ciA9IHRoaXMuc3RhcnROb2RlKCkpO1xuICAgICAgY3VyLmNvbnNlcXVlbnQgPSBbXTtcbiAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgaWYgKGlzQ2FzZSkge1xuICAgICAgICBjdXIudGVzdCA9IHRoaXMucGFyc2VFeHByZXNzaW9uKCk7XG4gICAgICB9IGVsc2Uge1xuICAgICAgICBpZiAoc2F3RGVmYXVsdCkgdGhpcy5yYWlzZSh0aGlzLmxhc3RUb2tTdGFydCwgXCJNdWx0aXBsZSBkZWZhdWx0IGNsYXVzZXNcIik7XG4gICAgICAgIHNhd0RlZmF1bHQgPSB0cnVlO1xuICAgICAgICBjdXIudGVzdCA9IG51bGw7XG4gICAgICB9XG4gICAgICB0aGlzLmV4cGVjdCh0dC5jb2xvbik7XG4gICAgfSBlbHNlIHtcbiAgICAgIGlmICghY3VyKSB0aGlzLnVuZXhwZWN0ZWQoKTtcbiAgICAgIGN1ci5jb25zZXF1ZW50LnB1c2godGhpcy5wYXJzZVN0YXRlbWVudCh0cnVlKSk7XG4gICAgfVxuICB9XG4gIGlmIChjdXIpIHRoaXMuZmluaXNoTm9kZShjdXIsIFwiU3dpdGNoQ2FzZVwiKTtcbiAgdGhpcy5uZXh0KCk7IC8vIENsb3NpbmcgYnJhY2VcbiAgdGhpcy5sYWJlbHMucG9wKCk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJTd2l0Y2hTdGF0ZW1lbnRcIik7XG59O1xuXG5wcC5wYXJzZVRocm93U3RhdGVtZW50ID0gZnVuY3Rpb24gKG5vZGUpIHtcbiAgdGhpcy5uZXh0KCk7XG4gIGlmIChsaW5lQnJlYWsudGVzdCh0aGlzLmlucHV0LnNsaWNlKHRoaXMubGFzdFRva0VuZCwgdGhpcy5zdGFydCkpKSB0aGlzLnJhaXNlKHRoaXMubGFzdFRva0VuZCwgXCJJbGxlZ2FsIG5ld2xpbmUgYWZ0ZXIgdGhyb3dcIik7XG4gIG5vZGUuYXJndW1lbnQgPSB0aGlzLnBhcnNlRXhwcmVzc2lvbigpO1xuICB0aGlzLnNlbWljb2xvbigpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiVGhyb3dTdGF0ZW1lbnRcIik7XG59O1xuXG4vLyBSZXVzZWQgZW1wdHkgYXJyYXkgYWRkZWQgZm9yIG5vZGUgZmllbGRzIHRoYXQgYXJlIGFsd2F5cyBlbXB0eS5cblxudmFyIGVtcHR5ID0gW107XG5cbnBwLnBhcnNlVHJ5U3RhdGVtZW50ID0gZnVuY3Rpb24gKG5vZGUpIHtcbiAgdGhpcy5uZXh0KCk7XG4gIG5vZGUuYmxvY2sgPSB0aGlzLnBhcnNlQmxvY2soKTtcbiAgbm9kZS5oYW5kbGVyID0gbnVsbDtcbiAgaWYgKHRoaXMudHlwZSA9PT0gdHQuX2NhdGNoKSB7XG4gICAgdmFyIGNsYXVzZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gICAgdGhpcy5uZXh0KCk7XG4gICAgdGhpcy5leHBlY3QodHQucGFyZW5MKTtcbiAgICBjbGF1c2UucGFyYW0gPSB0aGlzLnBhcnNlQmluZGluZ0F0b20oKTtcbiAgICB0aGlzLmNoZWNrTFZhbChjbGF1c2UucGFyYW0sIHRydWUpO1xuICAgIHRoaXMuZXhwZWN0KHR0LnBhcmVuUik7XG4gICAgY2xhdXNlLmd1YXJkID0gbnVsbDtcbiAgICBjbGF1c2UuYm9keSA9IHRoaXMucGFyc2VCbG9jaygpO1xuICAgIG5vZGUuaGFuZGxlciA9IHRoaXMuZmluaXNoTm9kZShjbGF1c2UsIFwiQ2F0Y2hDbGF1c2VcIik7XG4gIH1cbiAgbm9kZS5ndWFyZGVkSGFuZGxlcnMgPSBlbXB0eTtcbiAgbm9kZS5maW5hbGl6ZXIgPSB0aGlzLmVhdCh0dC5fZmluYWxseSkgPyB0aGlzLnBhcnNlQmxvY2soKSA6IG51bGw7XG4gIGlmICghbm9kZS5oYW5kbGVyICYmICFub2RlLmZpbmFsaXplcikgdGhpcy5yYWlzZShub2RlLnN0YXJ0LCBcIk1pc3NpbmcgY2F0Y2ggb3IgZmluYWxseSBjbGF1c2VcIik7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJUcnlTdGF0ZW1lbnRcIik7XG59O1xuXG5wcC5wYXJzZVZhclN0YXRlbWVudCA9IGZ1bmN0aW9uIChub2RlLCBraW5kKSB7XG4gIHRoaXMubmV4dCgpO1xuICB0aGlzLnBhcnNlVmFyKG5vZGUsIGZhbHNlLCBraW5kKTtcbiAgdGhpcy5zZW1pY29sb24oKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIlZhcmlhYmxlRGVjbGFyYXRpb25cIik7XG59O1xuXG5wcC5wYXJzZVdoaWxlU3RhdGVtZW50ID0gZnVuY3Rpb24gKG5vZGUpIHtcbiAgdGhpcy5uZXh0KCk7XG4gIG5vZGUudGVzdCA9IHRoaXMucGFyc2VQYXJlbkV4cHJlc3Npb24oKTtcbiAgdGhpcy5sYWJlbHMucHVzaChsb29wTGFiZWwpO1xuICBub2RlLmJvZHkgPSB0aGlzLnBhcnNlU3RhdGVtZW50KGZhbHNlKTtcbiAgdGhpcy5sYWJlbHMucG9wKCk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJXaGlsZVN0YXRlbWVudFwiKTtcbn07XG5cbnBwLnBhcnNlV2l0aFN0YXRlbWVudCA9IGZ1bmN0aW9uIChub2RlKSB7XG4gIGlmICh0aGlzLnN0cmljdCkgdGhpcy5yYWlzZSh0aGlzLnN0YXJ0LCBcIid3aXRoJyBpbiBzdHJpY3QgbW9kZVwiKTtcbiAgdGhpcy5uZXh0KCk7XG4gIG5vZGUub2JqZWN0ID0gdGhpcy5wYXJzZVBhcmVuRXhwcmVzc2lvbigpO1xuICBub2RlLmJvZHkgPSB0aGlzLnBhcnNlU3RhdGVtZW50KGZhbHNlKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIldpdGhTdGF0ZW1lbnRcIik7XG59O1xuXG5wcC5wYXJzZUVtcHR5U3RhdGVtZW50ID0gZnVuY3Rpb24gKG5vZGUpIHtcbiAgdGhpcy5uZXh0KCk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJFbXB0eVN0YXRlbWVudFwiKTtcbn07XG5cbnBwLnBhcnNlTGFiZWxlZFN0YXRlbWVudCA9IGZ1bmN0aW9uIChub2RlLCBtYXliZU5hbWUsIGV4cHIpIHtcbiAgZm9yICh2YXIgaSA9IDA7IGkgPCB0aGlzLmxhYmVscy5sZW5ndGg7ICsraSkge1xuICAgIGlmICh0aGlzLmxhYmVsc1tpXS5uYW1lID09PSBtYXliZU5hbWUpIHRoaXMucmFpc2UoZXhwci5zdGFydCwgXCJMYWJlbCAnXCIgKyBtYXliZU5hbWUgKyBcIicgaXMgYWxyZWFkeSBkZWNsYXJlZFwiKTtcbiAgfXZhciBraW5kID0gdGhpcy50eXBlLmlzTG9vcCA/IFwibG9vcFwiIDogdGhpcy50eXBlID09PSB0dC5fc3dpdGNoID8gXCJzd2l0Y2hcIiA6IG51bGw7XG4gIHRoaXMubGFiZWxzLnB1c2goeyBuYW1lOiBtYXliZU5hbWUsIGtpbmQ6IGtpbmQgfSk7XG4gIG5vZGUuYm9keSA9IHRoaXMucGFyc2VTdGF0ZW1lbnQodHJ1ZSk7XG4gIHRoaXMubGFiZWxzLnBvcCgpO1xuICBub2RlLmxhYmVsID0gZXhwcjtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkxhYmVsZWRTdGF0ZW1lbnRcIik7XG59O1xuXG5wcC5wYXJzZUV4cHJlc3Npb25TdGF0ZW1lbnQgPSBmdW5jdGlvbiAobm9kZSwgZXhwcikge1xuICBub2RlLmV4cHJlc3Npb24gPSBleHByO1xuICB0aGlzLnNlbWljb2xvbigpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiRXhwcmVzc2lvblN0YXRlbWVudFwiKTtcbn07XG5cbi8vIFBhcnNlIGEgc2VtaWNvbG9uLWVuY2xvc2VkIGJsb2NrIG9mIHN0YXRlbWVudHMsIGhhbmRsaW5nIGBcInVzZVxuLy8gc3RyaWN0XCJgIGRlY2xhcmF0aW9ucyB3aGVuIGBhbGxvd1N0cmljdGAgaXMgdHJ1ZSAodXNlZCBmb3Jcbi8vIGZ1bmN0aW9uIGJvZGllcykuXG5cbnBwLnBhcnNlQmxvY2sgPSBmdW5jdGlvbiAoYWxsb3dTdHJpY3QpIHtcbiAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpLFxuICAgICAgZmlyc3QgPSB0cnVlLFxuICAgICAgb2xkU3RyaWN0ID0gdW5kZWZpbmVkO1xuICBub2RlLmJvZHkgPSBbXTtcbiAgdGhpcy5leHBlY3QodHQuYnJhY2VMKTtcbiAgd2hpbGUgKCF0aGlzLmVhdCh0dC5icmFjZVIpKSB7XG4gICAgdmFyIHN0bXQgPSB0aGlzLnBhcnNlU3RhdGVtZW50KHRydWUpO1xuICAgIG5vZGUuYm9keS5wdXNoKHN0bXQpO1xuICAgIGlmIChmaXJzdCAmJiBhbGxvd1N0cmljdCAmJiB0aGlzLmlzVXNlU3RyaWN0KHN0bXQpKSB7XG4gICAgICBvbGRTdHJpY3QgPSB0aGlzLnN0cmljdDtcbiAgICAgIHRoaXMuc2V0U3RyaWN0KHRoaXMuc3RyaWN0ID0gdHJ1ZSk7XG4gICAgfVxuICAgIGZpcnN0ID0gZmFsc2U7XG4gIH1cbiAgaWYgKG9sZFN0cmljdCA9PT0gZmFsc2UpIHRoaXMuc2V0U3RyaWN0KGZhbHNlKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkJsb2NrU3RhdGVtZW50XCIpO1xufTtcblxuLy8gUGFyc2UgYSByZWd1bGFyIGBmb3JgIGxvb3AuIFRoZSBkaXNhbWJpZ3VhdGlvbiBjb2RlIGluXG4vLyBgcGFyc2VTdGF0ZW1lbnRgIHdpbGwgYWxyZWFkeSBoYXZlIHBhcnNlZCB0aGUgaW5pdCBzdGF0ZW1lbnQgb3Jcbi8vIGV4cHJlc3Npb24uXG5cbnBwLnBhcnNlRm9yID0gZnVuY3Rpb24gKG5vZGUsIGluaXQpIHtcbiAgbm9kZS5pbml0ID0gaW5pdDtcbiAgdGhpcy5leHBlY3QodHQuc2VtaSk7XG4gIG5vZGUudGVzdCA9IHRoaXMudHlwZSA9PT0gdHQuc2VtaSA/IG51bGwgOiB0aGlzLnBhcnNlRXhwcmVzc2lvbigpO1xuICB0aGlzLmV4cGVjdCh0dC5zZW1pKTtcbiAgbm9kZS51cGRhdGUgPSB0aGlzLnR5cGUgPT09IHR0LnBhcmVuUiA/IG51bGwgOiB0aGlzLnBhcnNlRXhwcmVzc2lvbigpO1xuICB0aGlzLmV4cGVjdCh0dC5wYXJlblIpO1xuICBub2RlLmJvZHkgPSB0aGlzLnBhcnNlU3RhdGVtZW50KGZhbHNlKTtcbiAgdGhpcy5sYWJlbHMucG9wKCk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJGb3JTdGF0ZW1lbnRcIik7XG59O1xuXG4vLyBQYXJzZSBhIGBmb3JgL2BpbmAgYW5kIGBmb3JgL2BvZmAgbG9vcCwgd2hpY2ggYXJlIGFsbW9zdFxuLy8gc2FtZSBmcm9tIHBhcnNlcidzIHBlcnNwZWN0aXZlLlxuXG5wcC5wYXJzZUZvckluID0gZnVuY3Rpb24gKG5vZGUsIGluaXQpIHtcbiAgdmFyIHR5cGUgPSB0aGlzLnR5cGUgPT09IHR0Ll9pbiA/IFwiRm9ySW5TdGF0ZW1lbnRcIiA6IFwiRm9yT2ZTdGF0ZW1lbnRcIjtcbiAgdGhpcy5uZXh0KCk7XG4gIG5vZGUubGVmdCA9IGluaXQ7XG4gIG5vZGUucmlnaHQgPSB0aGlzLnBhcnNlRXhwcmVzc2lvbigpO1xuICB0aGlzLmV4cGVjdCh0dC5wYXJlblIpO1xuICBub2RlLmJvZHkgPSB0aGlzLnBhcnNlU3RhdGVtZW50KGZhbHNlKTtcbiAgdGhpcy5sYWJlbHMucG9wKCk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgdHlwZSk7XG59O1xuXG4vLyBQYXJzZSBhIGxpc3Qgb2YgdmFyaWFibGUgZGVjbGFyYXRpb25zLlxuXG5wcC5wYXJzZVZhciA9IGZ1bmN0aW9uIChub2RlLCBpc0Zvciwga2luZCkge1xuICBub2RlLmRlY2xhcmF0aW9ucyA9IFtdO1xuICBub2RlLmtpbmQgPSBraW5kLmtleXdvcmQ7XG4gIGZvciAoOzspIHtcbiAgICB2YXIgZGVjbCA9IHRoaXMuc3RhcnROb2RlKCk7XG4gICAgdGhpcy5wYXJzZVZhcklkKGRlY2wpO1xuICAgIGlmICh0aGlzLmVhdCh0dC5lcSkpIHtcbiAgICAgIGRlY2wuaW5pdCA9IHRoaXMucGFyc2VNYXliZUFzc2lnbihpc0Zvcik7XG4gICAgfSBlbHNlIGlmIChraW5kID09PSB0dC5fY29uc3QgJiYgISh0aGlzLnR5cGUgPT09IHR0Ll9pbiB8fCB0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNiAmJiB0aGlzLmlzQ29udGV4dHVhbChcIm9mXCIpKSkge1xuICAgICAgdGhpcy51bmV4cGVjdGVkKCk7XG4gICAgfSBlbHNlIGlmIChkZWNsLmlkLnR5cGUgIT0gXCJJZGVudGlmaWVyXCIgJiYgIShpc0ZvciAmJiAodGhpcy50eXBlID09PSB0dC5faW4gfHwgdGhpcy5pc0NvbnRleHR1YWwoXCJvZlwiKSkpKSB7XG4gICAgICB0aGlzLnJhaXNlKHRoaXMubGFzdFRva0VuZCwgXCJDb21wbGV4IGJpbmRpbmcgcGF0dGVybnMgcmVxdWlyZSBhbiBpbml0aWFsaXphdGlvbiB2YWx1ZVwiKTtcbiAgICB9IGVsc2Uge1xuICAgICAgZGVjbC5pbml0ID0gbnVsbDtcbiAgICB9XG4gICAgbm9kZS5kZWNsYXJhdGlvbnMucHVzaCh0aGlzLmZpbmlzaE5vZGUoZGVjbCwgXCJWYXJpYWJsZURlY2xhcmF0b3JcIikpO1xuICAgIGlmICghdGhpcy5lYXQodHQuY29tbWEpKSBicmVhaztcbiAgfVxuICByZXR1cm4gbm9kZTtcbn07XG5cbnBwLnBhcnNlVmFySWQgPSBmdW5jdGlvbiAoZGVjbCkge1xuICBkZWNsLmlkID0gdGhpcy5wYXJzZUJpbmRpbmdBdG9tKCk7XG4gIHRoaXMuY2hlY2tMVmFsKGRlY2wuaWQsIHRydWUpO1xufTtcblxuLy8gUGFyc2UgYSBmdW5jdGlvbiBkZWNsYXJhdGlvbiBvciBsaXRlcmFsIChkZXBlbmRpbmcgb24gdGhlXG4vLyBgaXNTdGF0ZW1lbnRgIHBhcmFtZXRlcikuXG5cbnBwLnBhcnNlRnVuY3Rpb24gPSBmdW5jdGlvbiAobm9kZSwgaXNTdGF0ZW1lbnQsIGFsbG93RXhwcmVzc2lvbkJvZHkpIHtcbiAgdGhpcy5pbml0RnVuY3Rpb24obm9kZSk7XG4gIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNikgbm9kZS5nZW5lcmF0b3IgPSB0aGlzLmVhdCh0dC5zdGFyKTtcbiAgaWYgKGlzU3RhdGVtZW50IHx8IHRoaXMudHlwZSA9PT0gdHQubmFtZSkgbm9kZS5pZCA9IHRoaXMucGFyc2VJZGVudCgpO1xuICB0aGlzLnBhcnNlRnVuY3Rpb25QYXJhbXMobm9kZSk7XG4gIHRoaXMucGFyc2VGdW5jdGlvbkJvZHkobm9kZSwgYWxsb3dFeHByZXNzaW9uQm9keSk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgaXNTdGF0ZW1lbnQgPyBcIkZ1bmN0aW9uRGVjbGFyYXRpb25cIiA6IFwiRnVuY3Rpb25FeHByZXNzaW9uXCIpO1xufTtcblxucHAucGFyc2VGdW5jdGlvblBhcmFtcyA9IGZ1bmN0aW9uIChub2RlKSB7XG4gIHRoaXMuZXhwZWN0KHR0LnBhcmVuTCk7XG4gIG5vZGUucGFyYW1zID0gdGhpcy5wYXJzZUJpbmRpbmdMaXN0KHR0LnBhcmVuUiwgZmFsc2UsIGZhbHNlKTtcbn07XG5cbi8vIFBhcnNlIGEgY2xhc3MgZGVjbGFyYXRpb24gb3IgbGl0ZXJhbCAoZGVwZW5kaW5nIG9uIHRoZVxuLy8gYGlzU3RhdGVtZW50YCBwYXJhbWV0ZXIpLlxuXG5wcC5wYXJzZUNsYXNzID0gZnVuY3Rpb24gKG5vZGUsIGlzU3RhdGVtZW50KSB7XG4gIHRoaXMubmV4dCgpO1xuICB0aGlzLnBhcnNlQ2xhc3NJZChub2RlLCBpc1N0YXRlbWVudCk7XG4gIHRoaXMucGFyc2VDbGFzc1N1cGVyKG5vZGUpO1xuICB2YXIgY2xhc3NCb2R5ID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgdmFyIGhhZENvbnN0cnVjdG9yID0gZmFsc2U7XG4gIGNsYXNzQm9keS5ib2R5ID0gW107XG4gIHRoaXMuZXhwZWN0KHR0LmJyYWNlTCk7XG4gIHdoaWxlICghdGhpcy5lYXQodHQuYnJhY2VSKSkge1xuICAgIGlmICh0aGlzLmVhdCh0dC5zZW1pKSkgY29udGludWU7XG4gICAgdmFyIG1ldGhvZCA9IHRoaXMuc3RhcnROb2RlKCk7XG4gICAgdmFyIGlzR2VuZXJhdG9yID0gdGhpcy5lYXQodHQuc3Rhcik7XG4gICAgdmFyIGlzTWF5YmVTdGF0aWMgPSB0aGlzLnR5cGUgPT09IHR0Lm5hbWUgJiYgdGhpcy52YWx1ZSA9PT0gXCJzdGF0aWNcIjtcbiAgICB0aGlzLnBhcnNlUHJvcGVydHlOYW1lKG1ldGhvZCk7XG4gICAgbWV0aG9kW1wic3RhdGljXCJdID0gaXNNYXliZVN0YXRpYyAmJiB0aGlzLnR5cGUgIT09IHR0LnBhcmVuTDtcbiAgICBpZiAobWV0aG9kW1wic3RhdGljXCJdKSB7XG4gICAgICBpZiAoaXNHZW5lcmF0b3IpIHRoaXMudW5leHBlY3RlZCgpO1xuICAgICAgaXNHZW5lcmF0b3IgPSB0aGlzLmVhdCh0dC5zdGFyKTtcbiAgICAgIHRoaXMucGFyc2VQcm9wZXJ0eU5hbWUobWV0aG9kKTtcbiAgICB9XG4gICAgbWV0aG9kLmtpbmQgPSBcIm1ldGhvZFwiO1xuICAgIGlmICghbWV0aG9kLmNvbXB1dGVkKSB7XG4gICAgICB2YXIga2V5ID0gbWV0aG9kLmtleTtcblxuICAgICAgdmFyIGlzR2V0U2V0ID0gZmFsc2U7XG4gICAgICBpZiAoIWlzR2VuZXJhdG9yICYmIGtleS50eXBlID09PSBcIklkZW50aWZpZXJcIiAmJiB0aGlzLnR5cGUgIT09IHR0LnBhcmVuTCAmJiAoa2V5Lm5hbWUgPT09IFwiZ2V0XCIgfHwga2V5Lm5hbWUgPT09IFwic2V0XCIpKSB7XG4gICAgICAgIGlzR2V0U2V0ID0gdHJ1ZTtcbiAgICAgICAgbWV0aG9kLmtpbmQgPSBrZXkubmFtZTtcbiAgICAgICAga2V5ID0gdGhpcy5wYXJzZVByb3BlcnR5TmFtZShtZXRob2QpO1xuICAgICAgfVxuICAgICAgaWYgKCFtZXRob2RbXCJzdGF0aWNcIl0gJiYgKGtleS50eXBlID09PSBcIklkZW50aWZpZXJcIiAmJiBrZXkubmFtZSA9PT0gXCJjb25zdHJ1Y3RvclwiIHx8IGtleS50eXBlID09PSBcIkxpdGVyYWxcIiAmJiBrZXkudmFsdWUgPT09IFwiY29uc3RydWN0b3JcIikpIHtcbiAgICAgICAgaWYgKGhhZENvbnN0cnVjdG9yKSB0aGlzLnJhaXNlKGtleS5zdGFydCwgXCJEdXBsaWNhdGUgY29uc3RydWN0b3IgaW4gdGhlIHNhbWUgY2xhc3NcIik7XG4gICAgICAgIGlmIChpc0dldFNldCkgdGhpcy5yYWlzZShrZXkuc3RhcnQsIFwiQ29uc3RydWN0b3IgY2FuJ3QgaGF2ZSBnZXQvc2V0IG1vZGlmaWVyXCIpO1xuICAgICAgICBpZiAoaXNHZW5lcmF0b3IpIHRoaXMucmFpc2Uoa2V5LnN0YXJ0LCBcIkNvbnN0cnVjdG9yIGNhbid0IGJlIGEgZ2VuZXJhdG9yXCIpO1xuICAgICAgICBtZXRob2Qua2luZCA9IFwiY29uc3RydWN0b3JcIjtcbiAgICAgICAgaGFkQ29uc3RydWN0b3IgPSB0cnVlO1xuICAgICAgfVxuICAgIH1cbiAgICB0aGlzLnBhcnNlQ2xhc3NNZXRob2QoY2xhc3NCb2R5LCBtZXRob2QsIGlzR2VuZXJhdG9yKTtcbiAgfVxuICBub2RlLmJvZHkgPSB0aGlzLmZpbmlzaE5vZGUoY2xhc3NCb2R5LCBcIkNsYXNzQm9keVwiKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBpc1N0YXRlbWVudCA/IFwiQ2xhc3NEZWNsYXJhdGlvblwiIDogXCJDbGFzc0V4cHJlc3Npb25cIik7XG59O1xuXG5wcC5wYXJzZUNsYXNzTWV0aG9kID0gZnVuY3Rpb24gKGNsYXNzQm9keSwgbWV0aG9kLCBpc0dlbmVyYXRvcikge1xuICBtZXRob2QudmFsdWUgPSB0aGlzLnBhcnNlTWV0aG9kKGlzR2VuZXJhdG9yKTtcbiAgY2xhc3NCb2R5LmJvZHkucHVzaCh0aGlzLmZpbmlzaE5vZGUobWV0aG9kLCBcIk1ldGhvZERlZmluaXRpb25cIikpO1xufTtcblxucHAucGFyc2VDbGFzc0lkID0gZnVuY3Rpb24gKG5vZGUsIGlzU3RhdGVtZW50KSB7XG4gIG5vZGUuaWQgPSB0aGlzLnR5cGUgPT09IHR0Lm5hbWUgPyB0aGlzLnBhcnNlSWRlbnQoKSA6IGlzU3RhdGVtZW50ID8gdGhpcy51bmV4cGVjdGVkKCkgOiBudWxsO1xufTtcblxucHAucGFyc2VDbGFzc1N1cGVyID0gZnVuY3Rpb24gKG5vZGUpIHtcbiAgbm9kZS5zdXBlckNsYXNzID0gdGhpcy5lYXQodHQuX2V4dGVuZHMpID8gdGhpcy5wYXJzZUV4cHJTdWJzY3JpcHRzKCkgOiBudWxsO1xufTtcblxuLy8gUGFyc2VzIG1vZHVsZSBleHBvcnQgZGVjbGFyYXRpb24uXG5cbnBwLnBhcnNlRXhwb3J0ID0gZnVuY3Rpb24gKG5vZGUpIHtcbiAgdGhpcy5uZXh0KCk7XG4gIC8vIGV4cG9ydCAqIGZyb20gJy4uLidcbiAgaWYgKHRoaXMuZWF0KHR0LnN0YXIpKSB7XG4gICAgdGhpcy5leHBlY3RDb250ZXh0dWFsKFwiZnJvbVwiKTtcbiAgICBub2RlLnNvdXJjZSA9IHRoaXMudHlwZSA9PT0gdHQuc3RyaW5nID8gdGhpcy5wYXJzZUV4cHJBdG9tKCkgOiB0aGlzLnVuZXhwZWN0ZWQoKTtcbiAgICB0aGlzLnNlbWljb2xvbigpO1xuICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJFeHBvcnRBbGxEZWNsYXJhdGlvblwiKTtcbiAgfVxuICBpZiAodGhpcy5lYXQodHQuX2RlZmF1bHQpKSB7XG4gICAgLy8gZXhwb3J0IGRlZmF1bHQgLi4uXG4gICAgdmFyIGV4cHIgPSB0aGlzLnBhcnNlTWF5YmVBc3NpZ24oKTtcbiAgICB2YXIgbmVlZHNTZW1pID0gdHJ1ZTtcbiAgICBpZiAoZXhwci50eXBlID09IFwiRnVuY3Rpb25FeHByZXNzaW9uXCIgfHwgZXhwci50eXBlID09IFwiQ2xhc3NFeHByZXNzaW9uXCIpIHtcbiAgICAgIG5lZWRzU2VtaSA9IGZhbHNlO1xuICAgICAgaWYgKGV4cHIuaWQpIHtcbiAgICAgICAgZXhwci50eXBlID0gZXhwci50eXBlID09IFwiRnVuY3Rpb25FeHByZXNzaW9uXCIgPyBcIkZ1bmN0aW9uRGVjbGFyYXRpb25cIiA6IFwiQ2xhc3NEZWNsYXJhdGlvblwiO1xuICAgICAgfVxuICAgIH1cbiAgICBub2RlLmRlY2xhcmF0aW9uID0gZXhwcjtcbiAgICBpZiAobmVlZHNTZW1pKSB0aGlzLnNlbWljb2xvbigpO1xuICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJFeHBvcnREZWZhdWx0RGVjbGFyYXRpb25cIik7XG4gIH1cbiAgLy8gZXhwb3J0IHZhcnxjb25zdHxsZXR8ZnVuY3Rpb258Y2xhc3MgLi4uXG4gIGlmICh0aGlzLnNob3VsZFBhcnNlRXhwb3J0U3RhdGVtZW50KCkpIHtcbiAgICBub2RlLmRlY2xhcmF0aW9uID0gdGhpcy5wYXJzZVN0YXRlbWVudCh0cnVlKTtcbiAgICBub2RlLnNwZWNpZmllcnMgPSBbXTtcbiAgICBub2RlLnNvdXJjZSA9IG51bGw7XG4gIH0gZWxzZSB7XG4gICAgLy8gZXhwb3J0IHsgeCwgeSBhcyB6IH0gW2Zyb20gJy4uLiddXG4gICAgbm9kZS5kZWNsYXJhdGlvbiA9IG51bGw7XG4gICAgbm9kZS5zcGVjaWZpZXJzID0gdGhpcy5wYXJzZUV4cG9ydFNwZWNpZmllcnMoKTtcbiAgICBpZiAodGhpcy5lYXRDb250ZXh0dWFsKFwiZnJvbVwiKSkge1xuICAgICAgbm9kZS5zb3VyY2UgPSB0aGlzLnR5cGUgPT09IHR0LnN0cmluZyA/IHRoaXMucGFyc2VFeHByQXRvbSgpIDogdGhpcy51bmV4cGVjdGVkKCk7XG4gICAgfSBlbHNlIHtcbiAgICAgIG5vZGUuc291cmNlID0gbnVsbDtcbiAgICB9XG4gICAgdGhpcy5zZW1pY29sb24oKTtcbiAgfVxuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiRXhwb3J0TmFtZWREZWNsYXJhdGlvblwiKTtcbn07XG5cbnBwLnNob3VsZFBhcnNlRXhwb3J0U3RhdGVtZW50ID0gZnVuY3Rpb24gKCkge1xuICByZXR1cm4gdGhpcy50eXBlLmtleXdvcmQ7XG59O1xuXG4vLyBQYXJzZXMgYSBjb21tYS1zZXBhcmF0ZWQgbGlzdCBvZiBtb2R1bGUgZXhwb3J0cy5cblxucHAucGFyc2VFeHBvcnRTcGVjaWZpZXJzID0gZnVuY3Rpb24gKCkge1xuICB2YXIgbm9kZXMgPSBbXSxcbiAgICAgIGZpcnN0ID0gdHJ1ZTtcbiAgLy8gZXhwb3J0IHsgeCwgeSBhcyB6IH0gW2Zyb20gJy4uLiddXG4gIHRoaXMuZXhwZWN0KHR0LmJyYWNlTCk7XG4gIHdoaWxlICghdGhpcy5lYXQodHQuYnJhY2VSKSkge1xuICAgIGlmICghZmlyc3QpIHtcbiAgICAgIHRoaXMuZXhwZWN0KHR0LmNvbW1hKTtcbiAgICAgIGlmICh0aGlzLmFmdGVyVHJhaWxpbmdDb21tYSh0dC5icmFjZVIpKSBicmVhaztcbiAgICB9IGVsc2UgZmlyc3QgPSBmYWxzZTtcblxuICAgIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgICBub2RlLmxvY2FsID0gdGhpcy5wYXJzZUlkZW50KHRoaXMudHlwZSA9PT0gdHQuX2RlZmF1bHQpO1xuICAgIG5vZGUuZXhwb3J0ZWQgPSB0aGlzLmVhdENvbnRleHR1YWwoXCJhc1wiKSA/IHRoaXMucGFyc2VJZGVudCh0cnVlKSA6IG5vZGUubG9jYWw7XG4gICAgbm9kZXMucHVzaCh0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJFeHBvcnRTcGVjaWZpZXJcIikpO1xuICB9XG4gIHJldHVybiBub2Rlcztcbn07XG5cbi8vIFBhcnNlcyBpbXBvcnQgZGVjbGFyYXRpb24uXG5cbnBwLnBhcnNlSW1wb3J0ID0gZnVuY3Rpb24gKG5vZGUpIHtcbiAgdGhpcy5uZXh0KCk7XG4gIC8vIGltcG9ydCAnLi4uJ1xuICBpZiAodGhpcy50eXBlID09PSB0dC5zdHJpbmcpIHtcbiAgICBub2RlLnNwZWNpZmllcnMgPSBlbXB0eTtcbiAgICBub2RlLnNvdXJjZSA9IHRoaXMucGFyc2VFeHByQXRvbSgpO1xuICAgIG5vZGUua2luZCA9IFwiXCI7XG4gIH0gZWxzZSB7XG4gICAgbm9kZS5zcGVjaWZpZXJzID0gdGhpcy5wYXJzZUltcG9ydFNwZWNpZmllcnMoKTtcbiAgICB0aGlzLmV4cGVjdENvbnRleHR1YWwoXCJmcm9tXCIpO1xuICAgIG5vZGUuc291cmNlID0gdGhpcy50eXBlID09PSB0dC5zdHJpbmcgPyB0aGlzLnBhcnNlRXhwckF0b20oKSA6IHRoaXMudW5leHBlY3RlZCgpO1xuICB9XG4gIHRoaXMuc2VtaWNvbG9uKCk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJJbXBvcnREZWNsYXJhdGlvblwiKTtcbn07XG5cbi8vIFBhcnNlcyBhIGNvbW1hLXNlcGFyYXRlZCBsaXN0IG9mIG1vZHVsZSBpbXBvcnRzLlxuXG5wcC5wYXJzZUltcG9ydFNwZWNpZmllcnMgPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBub2RlcyA9IFtdLFxuICAgICAgZmlyc3QgPSB0cnVlO1xuICBpZiAodGhpcy50eXBlID09PSB0dC5uYW1lKSB7XG4gICAgLy8gaW1wb3J0IGRlZmF1bHRPYmosIHsgeCwgeSBhcyB6IH0gZnJvbSAnLi4uJ1xuICAgIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgICBub2RlLmxvY2FsID0gdGhpcy5wYXJzZUlkZW50KCk7XG4gICAgdGhpcy5jaGVja0xWYWwobm9kZS5sb2NhbCwgdHJ1ZSk7XG4gICAgbm9kZXMucHVzaCh0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJJbXBvcnREZWZhdWx0U3BlY2lmaWVyXCIpKTtcbiAgICBpZiAoIXRoaXMuZWF0KHR0LmNvbW1hKSkgcmV0dXJuIG5vZGVzO1xuICB9XG4gIGlmICh0aGlzLnR5cGUgPT09IHR0LnN0YXIpIHtcbiAgICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gICAgdGhpcy5uZXh0KCk7XG4gICAgdGhpcy5leHBlY3RDb250ZXh0dWFsKFwiYXNcIik7XG4gICAgbm9kZS5sb2NhbCA9IHRoaXMucGFyc2VJZGVudCgpO1xuICAgIHRoaXMuY2hlY2tMVmFsKG5vZGUubG9jYWwsIHRydWUpO1xuICAgIG5vZGVzLnB1c2godGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiSW1wb3J0TmFtZXNwYWNlU3BlY2lmaWVyXCIpKTtcbiAgICByZXR1cm4gbm9kZXM7XG4gIH1cbiAgdGhpcy5leHBlY3QodHQuYnJhY2VMKTtcbiAgd2hpbGUgKCF0aGlzLmVhdCh0dC5icmFjZVIpKSB7XG4gICAgaWYgKCFmaXJzdCkge1xuICAgICAgdGhpcy5leHBlY3QodHQuY29tbWEpO1xuICAgICAgaWYgKHRoaXMuYWZ0ZXJUcmFpbGluZ0NvbW1hKHR0LmJyYWNlUikpIGJyZWFrO1xuICAgIH0gZWxzZSBmaXJzdCA9IGZhbHNlO1xuXG4gICAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICAgIG5vZGUuaW1wb3J0ZWQgPSB0aGlzLnBhcnNlSWRlbnQodHJ1ZSk7XG4gICAgbm9kZS5sb2NhbCA9IHRoaXMuZWF0Q29udGV4dHVhbChcImFzXCIpID8gdGhpcy5wYXJzZUlkZW50KCkgOiBub2RlLmltcG9ydGVkO1xuICAgIHRoaXMuY2hlY2tMVmFsKG5vZGUubG9jYWwsIHRydWUpO1xuICAgIG5vZGVzLnB1c2godGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiSW1wb3J0U3BlY2lmaWVyXCIpKTtcbiAgfVxuICByZXR1cm4gbm9kZXM7XG59O1xuXG59LHtcIi4vc3RhdGVcIjoxMyxcIi4vdG9rZW50eXBlXCI6MTcsXCIuL3doaXRlc3BhY2VcIjoxOX1dLDE1OltmdW5jdGlvbihfZGVyZXFfLG1vZHVsZSxleHBvcnRzKXtcblwidXNlIHN0cmljdFwiO1xuXG52YXIgX2NsYXNzQ2FsbENoZWNrID0gZnVuY3Rpb24gKGluc3RhbmNlLCBDb25zdHJ1Y3RvcikgeyBpZiAoIShpbnN0YW5jZSBpbnN0YW5jZW9mIENvbnN0cnVjdG9yKSkgeyB0aHJvdyBuZXcgVHlwZUVycm9yKFwiQ2Fubm90IGNhbGwgYSBjbGFzcyBhcyBhIGZ1bmN0aW9uXCIpOyB9IH07XG5cbmV4cG9ydHMuX19lc01vZHVsZSA9IHRydWU7XG4vLyBUaGUgYWxnb3JpdGhtIHVzZWQgdG8gZGV0ZXJtaW5lIHdoZXRoZXIgYSByZWdleHAgY2FuIGFwcGVhciBhdCBhXG4vLyBnaXZlbiBwb2ludCBpbiB0aGUgcHJvZ3JhbSBpcyBsb29zZWx5IGJhc2VkIG9uIHN3ZWV0LmpzJyBhcHByb2FjaC5cbi8vIFNlZSBodHRwczovL2dpdGh1Yi5jb20vbW96aWxsYS9zd2VldC5qcy93aWtpL2Rlc2lnblxuXG52YXIgUGFyc2VyID0gX2RlcmVxXyhcIi4vc3RhdGVcIikuUGFyc2VyO1xuXG52YXIgdHQgPSBfZGVyZXFfKFwiLi90b2tlbnR5cGVcIikudHlwZXM7XG5cbnZhciBsaW5lQnJlYWsgPSBfZGVyZXFfKFwiLi93aGl0ZXNwYWNlXCIpLmxpbmVCcmVhaztcblxudmFyIFRva0NvbnRleHQgPSBleHBvcnRzLlRva0NvbnRleHQgPSBmdW5jdGlvbiBUb2tDb250ZXh0KHRva2VuLCBpc0V4cHIsIHByZXNlcnZlU3BhY2UsIG92ZXJyaWRlKSB7XG4gIF9jbGFzc0NhbGxDaGVjayh0aGlzLCBUb2tDb250ZXh0KTtcblxuICB0aGlzLnRva2VuID0gdG9rZW47XG4gIHRoaXMuaXNFeHByID0gaXNFeHByO1xuICB0aGlzLnByZXNlcnZlU3BhY2UgPSBwcmVzZXJ2ZVNwYWNlO1xuICB0aGlzLm92ZXJyaWRlID0gb3ZlcnJpZGU7XG59O1xuXG52YXIgdHlwZXMgPSB7XG4gIGJfc3RhdDogbmV3IFRva0NvbnRleHQoXCJ7XCIsIGZhbHNlKSxcbiAgYl9leHByOiBuZXcgVG9rQ29udGV4dChcIntcIiwgdHJ1ZSksXG4gIGJfdG1wbDogbmV3IFRva0NvbnRleHQoXCIke1wiLCB0cnVlKSxcbiAgcF9zdGF0OiBuZXcgVG9rQ29udGV4dChcIihcIiwgZmFsc2UpLFxuICBwX2V4cHI6IG5ldyBUb2tDb250ZXh0KFwiKFwiLCB0cnVlKSxcbiAgcV90bXBsOiBuZXcgVG9rQ29udGV4dChcImBcIiwgdHJ1ZSwgdHJ1ZSwgZnVuY3Rpb24gKHApIHtcbiAgICByZXR1cm4gcC5yZWFkVG1wbFRva2VuKCk7XG4gIH0pLFxuICBmX2V4cHI6IG5ldyBUb2tDb250ZXh0KFwiZnVuY3Rpb25cIiwgdHJ1ZSlcbn07XG5cbmV4cG9ydHMudHlwZXMgPSB0eXBlcztcbnZhciBwcCA9IFBhcnNlci5wcm90b3R5cGU7XG5cbnBwLmluaXRpYWxDb250ZXh0ID0gZnVuY3Rpb24gKCkge1xuICByZXR1cm4gW3R5cGVzLmJfc3RhdF07XG59O1xuXG5wcC5icmFjZUlzQmxvY2sgPSBmdW5jdGlvbiAocHJldlR5cGUpIHtcbiAgdmFyIHBhcmVudCA9IHVuZGVmaW5lZDtcbiAgaWYgKHByZXZUeXBlID09PSB0dC5jb2xvbiAmJiAocGFyZW50ID0gdGhpcy5jdXJDb250ZXh0KCkpLnRva2VuID09IFwie1wiKSByZXR1cm4gIXBhcmVudC5pc0V4cHI7XG4gIGlmIChwcmV2VHlwZSA9PT0gdHQuX3JldHVybikgcmV0dXJuIGxpbmVCcmVhay50ZXN0KHRoaXMuaW5wdXQuc2xpY2UodGhpcy5sYXN0VG9rRW5kLCB0aGlzLnN0YXJ0KSk7XG4gIGlmIChwcmV2VHlwZSA9PT0gdHQuX2Vsc2UgfHwgcHJldlR5cGUgPT09IHR0LnNlbWkgfHwgcHJldlR5cGUgPT09IHR0LmVvZikgcmV0dXJuIHRydWU7XG4gIGlmIChwcmV2VHlwZSA9PSB0dC5icmFjZUwpIHJldHVybiB0aGlzLmN1ckNvbnRleHQoKSA9PT0gdHlwZXMuYl9zdGF0O1xuICByZXR1cm4gIXRoaXMuZXhwckFsbG93ZWQ7XG59O1xuXG5wcC51cGRhdGVDb250ZXh0ID0gZnVuY3Rpb24gKHByZXZUeXBlKSB7XG4gIHZhciB1cGRhdGUgPSB1bmRlZmluZWQsXG4gICAgICB0eXBlID0gdGhpcy50eXBlO1xuICBpZiAodHlwZS5rZXl3b3JkICYmIHByZXZUeXBlID09IHR0LmRvdCkgdGhpcy5leHByQWxsb3dlZCA9IGZhbHNlO2Vsc2UgaWYgKHVwZGF0ZSA9IHR5cGUudXBkYXRlQ29udGV4dCkgdXBkYXRlLmNhbGwodGhpcywgcHJldlR5cGUpO2Vsc2UgdGhpcy5leHByQWxsb3dlZCA9IHR5cGUuYmVmb3JlRXhwcjtcbn07XG5cbi8vIFRva2VuLXNwZWNpZmljIGNvbnRleHQgdXBkYXRlIGNvZGVcblxudHQucGFyZW5SLnVwZGF0ZUNvbnRleHQgPSB0dC5icmFjZVIudXBkYXRlQ29udGV4dCA9IGZ1bmN0aW9uICgpIHtcbiAgaWYgKHRoaXMuY29udGV4dC5sZW5ndGggPT0gMSkge1xuICAgIHRoaXMuZXhwckFsbG93ZWQgPSB0cnVlO1xuICAgIHJldHVybjtcbiAgfVxuICB2YXIgb3V0ID0gdGhpcy5jb250ZXh0LnBvcCgpO1xuICBpZiAob3V0ID09PSB0eXBlcy5iX3N0YXQgJiYgdGhpcy5jdXJDb250ZXh0KCkgPT09IHR5cGVzLmZfZXhwcikge1xuICAgIHRoaXMuY29udGV4dC5wb3AoKTtcbiAgICB0aGlzLmV4cHJBbGxvd2VkID0gZmFsc2U7XG4gIH0gZWxzZSBpZiAob3V0ID09PSB0eXBlcy5iX3RtcGwpIHtcbiAgICB0aGlzLmV4cHJBbGxvd2VkID0gdHJ1ZTtcbiAgfSBlbHNlIHtcbiAgICB0aGlzLmV4cHJBbGxvd2VkID0gIW91dC5pc0V4cHI7XG4gIH1cbn07XG5cbnR0LmJyYWNlTC51cGRhdGVDb250ZXh0ID0gZnVuY3Rpb24gKHByZXZUeXBlKSB7XG4gIHRoaXMuY29udGV4dC5wdXNoKHRoaXMuYnJhY2VJc0Jsb2NrKHByZXZUeXBlKSA/IHR5cGVzLmJfc3RhdCA6IHR5cGVzLmJfZXhwcik7XG4gIHRoaXMuZXhwckFsbG93ZWQgPSB0cnVlO1xufTtcblxudHQuZG9sbGFyQnJhY2VMLnVwZGF0ZUNvbnRleHQgPSBmdW5jdGlvbiAoKSB7XG4gIHRoaXMuY29udGV4dC5wdXNoKHR5cGVzLmJfdG1wbCk7XG4gIHRoaXMuZXhwckFsbG93ZWQgPSB0cnVlO1xufTtcblxudHQucGFyZW5MLnVwZGF0ZUNvbnRleHQgPSBmdW5jdGlvbiAocHJldlR5cGUpIHtcbiAgdmFyIHN0YXRlbWVudFBhcmVucyA9IHByZXZUeXBlID09PSB0dC5faWYgfHwgcHJldlR5cGUgPT09IHR0Ll9mb3IgfHwgcHJldlR5cGUgPT09IHR0Ll93aXRoIHx8IHByZXZUeXBlID09PSB0dC5fd2hpbGU7XG4gIHRoaXMuY29udGV4dC5wdXNoKHN0YXRlbWVudFBhcmVucyA/IHR5cGVzLnBfc3RhdCA6IHR5cGVzLnBfZXhwcik7XG4gIHRoaXMuZXhwckFsbG93ZWQgPSB0cnVlO1xufTtcblxudHQuaW5jRGVjLnVwZGF0ZUNvbnRleHQgPSBmdW5jdGlvbiAoKSB7fTtcblxudHQuX2Z1bmN0aW9uLnVwZGF0ZUNvbnRleHQgPSBmdW5jdGlvbiAoKSB7XG4gIGlmICh0aGlzLmN1ckNvbnRleHQoKSAhPT0gdHlwZXMuYl9zdGF0KSB0aGlzLmNvbnRleHQucHVzaCh0eXBlcy5mX2V4cHIpO1xuICB0aGlzLmV4cHJBbGxvd2VkID0gZmFsc2U7XG59O1xuXG50dC5iYWNrUXVvdGUudXBkYXRlQ29udGV4dCA9IGZ1bmN0aW9uICgpIHtcbiAgaWYgKHRoaXMuY3VyQ29udGV4dCgpID09PSB0eXBlcy5xX3RtcGwpIHRoaXMuY29udGV4dC5wb3AoKTtlbHNlIHRoaXMuY29udGV4dC5wdXNoKHR5cGVzLnFfdG1wbCk7XG4gIHRoaXMuZXhwckFsbG93ZWQgPSBmYWxzZTtcbn07XG5cbi8vIHRva0V4cHJBbGxvd2VkIHN0YXlzIHVuY2hhbmdlZFxuXG59LHtcIi4vc3RhdGVcIjoxMyxcIi4vdG9rZW50eXBlXCI6MTcsXCIuL3doaXRlc3BhY2VcIjoxOX1dLDE2OltmdW5jdGlvbihfZGVyZXFfLG1vZHVsZSxleHBvcnRzKXtcblwidXNlIHN0cmljdFwiO1xuXG52YXIgX2NsYXNzQ2FsbENoZWNrID0gZnVuY3Rpb24gKGluc3RhbmNlLCBDb25zdHJ1Y3RvcikgeyBpZiAoIShpbnN0YW5jZSBpbnN0YW5jZW9mIENvbnN0cnVjdG9yKSkgeyB0aHJvdyBuZXcgVHlwZUVycm9yKFwiQ2Fubm90IGNhbGwgYSBjbGFzcyBhcyBhIGZ1bmN0aW9uXCIpOyB9IH07XG5cbmV4cG9ydHMuX19lc01vZHVsZSA9IHRydWU7XG5cbnZhciBfaWRlbnRpZmllciA9IF9kZXJlcV8oXCIuL2lkZW50aWZpZXJcIik7XG5cbnZhciBpc0lkZW50aWZpZXJTdGFydCA9IF9pZGVudGlmaWVyLmlzSWRlbnRpZmllclN0YXJ0O1xudmFyIGlzSWRlbnRpZmllckNoYXIgPSBfaWRlbnRpZmllci5pc0lkZW50aWZpZXJDaGFyO1xuXG52YXIgX3Rva2VudHlwZSA9IF9kZXJlcV8oXCIuL3Rva2VudHlwZVwiKTtcblxudmFyIHR0ID0gX3Rva2VudHlwZS50eXBlcztcbnZhciBrZXl3b3JkVHlwZXMgPSBfdG9rZW50eXBlLmtleXdvcmRzO1xuXG52YXIgUGFyc2VyID0gX2RlcmVxXyhcIi4vc3RhdGVcIikuUGFyc2VyO1xuXG52YXIgU291cmNlTG9jYXRpb24gPSBfZGVyZXFfKFwiLi9sb2NhdGlvblwiKS5Tb3VyY2VMb2NhdGlvbjtcblxudmFyIF93aGl0ZXNwYWNlID0gX2RlcmVxXyhcIi4vd2hpdGVzcGFjZVwiKTtcblxudmFyIGxpbmVCcmVhayA9IF93aGl0ZXNwYWNlLmxpbmVCcmVhaztcbnZhciBsaW5lQnJlYWtHID0gX3doaXRlc3BhY2UubGluZUJyZWFrRztcbnZhciBpc05ld0xpbmUgPSBfd2hpdGVzcGFjZS5pc05ld0xpbmU7XG52YXIgbm9uQVNDSUl3aGl0ZXNwYWNlID0gX3doaXRlc3BhY2Uubm9uQVNDSUl3aGl0ZXNwYWNlO1xuXG4vLyBPYmplY3QgdHlwZSB1c2VkIHRvIHJlcHJlc2VudCB0b2tlbnMuIE5vdGUgdGhhdCBub3JtYWxseSwgdG9rZW5zXG4vLyBzaW1wbHkgZXhpc3QgYXMgcHJvcGVydGllcyBvbiB0aGUgcGFyc2VyIG9iamVjdC4gVGhpcyBpcyBvbmx5XG4vLyB1c2VkIGZvciB0aGUgb25Ub2tlbiBjYWxsYmFjayBhbmQgdGhlIGV4dGVybmFsIHRva2VuaXplci5cblxudmFyIFRva2VuID0gZXhwb3J0cy5Ub2tlbiA9IGZ1bmN0aW9uIFRva2VuKHApIHtcbiAgX2NsYXNzQ2FsbENoZWNrKHRoaXMsIFRva2VuKTtcblxuICB0aGlzLnR5cGUgPSBwLnR5cGU7XG4gIHRoaXMudmFsdWUgPSBwLnZhbHVlO1xuICB0aGlzLnN0YXJ0ID0gcC5zdGFydDtcbiAgdGhpcy5lbmQgPSBwLmVuZDtcbiAgaWYgKHAub3B0aW9ucy5sb2NhdGlvbnMpIHRoaXMubG9jID0gbmV3IFNvdXJjZUxvY2F0aW9uKHAsIHAuc3RhcnRMb2MsIHAuZW5kTG9jKTtcbiAgaWYgKHAub3B0aW9ucy5yYW5nZXMpIHRoaXMucmFuZ2UgPSBbcC5zdGFydCwgcC5lbmRdO1xufTtcblxuLy8gIyMgVG9rZW5pemVyXG5cbnZhciBwcCA9IFBhcnNlci5wcm90b3R5cGU7XG5cbi8vIEFyZSB3ZSBydW5uaW5nIHVuZGVyIFJoaW5vP1xudmFyIGlzUmhpbm8gPSB0eXBlb2YgUGFja2FnZXMgIT09IFwidW5kZWZpbmVkXCI7XG5cbi8vIE1vdmUgdG8gdGhlIG5leHQgdG9rZW5cblxucHAubmV4dCA9IGZ1bmN0aW9uICgpIHtcbiAgaWYgKHRoaXMub3B0aW9ucy5vblRva2VuKSB0aGlzLm9wdGlvbnMub25Ub2tlbihuZXcgVG9rZW4odGhpcykpO1xuXG4gIHRoaXMubGFzdFRva0VuZCA9IHRoaXMuZW5kO1xuICB0aGlzLmxhc3RUb2tTdGFydCA9IHRoaXMuc3RhcnQ7XG4gIHRoaXMubGFzdFRva0VuZExvYyA9IHRoaXMuZW5kTG9jO1xuICB0aGlzLmxhc3RUb2tTdGFydExvYyA9IHRoaXMuc3RhcnRMb2M7XG4gIHRoaXMubmV4dFRva2VuKCk7XG59O1xuXG5wcC5nZXRUb2tlbiA9IGZ1bmN0aW9uICgpIHtcbiAgdGhpcy5uZXh0KCk7XG4gIHJldHVybiBuZXcgVG9rZW4odGhpcyk7XG59O1xuXG4vLyBJZiB3ZSdyZSBpbiBhbiBFUzYgZW52aXJvbm1lbnQsIG1ha2UgcGFyc2VycyBpdGVyYWJsZVxuaWYgKHR5cGVvZiBTeW1ib2wgIT09IFwidW5kZWZpbmVkXCIpIHBwW1N5bWJvbC5pdGVyYXRvcl0gPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBzZWxmID0gdGhpcztcbiAgcmV0dXJuIHsgbmV4dDogZnVuY3Rpb24gbmV4dCgpIHtcbiAgICAgIHZhciB0b2tlbiA9IHNlbGYuZ2V0VG9rZW4oKTtcbiAgICAgIHJldHVybiB7XG4gICAgICAgIGRvbmU6IHRva2VuLnR5cGUgPT09IHR0LmVvZixcbiAgICAgICAgdmFsdWU6IHRva2VuXG4gICAgICB9O1xuICAgIH0gfTtcbn07XG5cbi8vIFRvZ2dsZSBzdHJpY3QgbW9kZS4gUmUtcmVhZHMgdGhlIG5leHQgbnVtYmVyIG9yIHN0cmluZyB0byBwbGVhc2Vcbi8vIHBlZGFudGljIHRlc3RzIChgXCJ1c2Ugc3RyaWN0XCI7IDAxMDtgIHNob3VsZCBmYWlsKS5cblxucHAuc2V0U3RyaWN0ID0gZnVuY3Rpb24gKHN0cmljdCkge1xuICB0aGlzLnN0cmljdCA9IHN0cmljdDtcbiAgaWYgKHRoaXMudHlwZSAhPT0gdHQubnVtICYmIHRoaXMudHlwZSAhPT0gdHQuc3RyaW5nKSByZXR1cm47XG4gIHRoaXMucG9zID0gdGhpcy5zdGFydDtcbiAgaWYgKHRoaXMub3B0aW9ucy5sb2NhdGlvbnMpIHtcbiAgICB3aGlsZSAodGhpcy5wb3MgPCB0aGlzLmxpbmVTdGFydCkge1xuICAgICAgdGhpcy5saW5lU3RhcnQgPSB0aGlzLmlucHV0Lmxhc3RJbmRleE9mKFwiXFxuXCIsIHRoaXMubGluZVN0YXJ0IC0gMikgKyAxO1xuICAgICAgLS10aGlzLmN1ckxpbmU7XG4gICAgfVxuICB9XG4gIHRoaXMubmV4dFRva2VuKCk7XG59O1xuXG5wcC5jdXJDb250ZXh0ID0gZnVuY3Rpb24gKCkge1xuICByZXR1cm4gdGhpcy5jb250ZXh0W3RoaXMuY29udGV4dC5sZW5ndGggLSAxXTtcbn07XG5cbi8vIFJlYWQgYSBzaW5nbGUgdG9rZW4sIHVwZGF0aW5nIHRoZSBwYXJzZXIgb2JqZWN0J3MgdG9rZW4tcmVsYXRlZFxuLy8gcHJvcGVydGllcy5cblxucHAubmV4dFRva2VuID0gZnVuY3Rpb24gKCkge1xuICB2YXIgY3VyQ29udGV4dCA9IHRoaXMuY3VyQ29udGV4dCgpO1xuICBpZiAoIWN1ckNvbnRleHQgfHwgIWN1ckNvbnRleHQucHJlc2VydmVTcGFjZSkgdGhpcy5za2lwU3BhY2UoKTtcblxuICB0aGlzLnN0YXJ0ID0gdGhpcy5wb3M7XG4gIGlmICh0aGlzLm9wdGlvbnMubG9jYXRpb25zKSB0aGlzLnN0YXJ0TG9jID0gdGhpcy5jdXJQb3NpdGlvbigpO1xuICBpZiAodGhpcy5wb3MgPj0gdGhpcy5pbnB1dC5sZW5ndGgpIHJldHVybiB0aGlzLmZpbmlzaFRva2VuKHR0LmVvZik7XG5cbiAgaWYgKGN1ckNvbnRleHQub3ZlcnJpZGUpIHJldHVybiBjdXJDb250ZXh0Lm92ZXJyaWRlKHRoaXMpO2Vsc2UgdGhpcy5yZWFkVG9rZW4odGhpcy5mdWxsQ2hhckNvZGVBdFBvcygpKTtcbn07XG5cbnBwLnJlYWRUb2tlbiA9IGZ1bmN0aW9uIChjb2RlKSB7XG4gIC8vIElkZW50aWZpZXIgb3Iga2V5d29yZC4gJ1xcdVhYWFgnIHNlcXVlbmNlcyBhcmUgYWxsb3dlZCBpblxuICAvLyBpZGVudGlmaWVycywgc28gJ1xcJyBhbHNvIGRpc3BhdGNoZXMgdG8gdGhhdC5cbiAgaWYgKGlzSWRlbnRpZmllclN0YXJ0KGNvZGUsIHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KSB8fCBjb2RlID09PSA5MiAvKiAnXFwnICovKSByZXR1cm4gdGhpcy5yZWFkV29yZCgpO1xuXG4gIHJldHVybiB0aGlzLmdldFRva2VuRnJvbUNvZGUoY29kZSk7XG59O1xuXG5wcC5mdWxsQ2hhckNvZGVBdFBvcyA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIGNvZGUgPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MpO1xuICBpZiAoY29kZSA8PSA1NTI5NSB8fCBjb2RlID49IDU3MzQ0KSByZXR1cm4gY29kZTtcbiAgdmFyIG5leHQgPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAxKTtcbiAgcmV0dXJuIChjb2RlIDw8IDEwKSArIG5leHQgLSA1NjYxMzg4ODtcbn07XG5cbnBwLnNraXBCbG9ja0NvbW1lbnQgPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBzdGFydExvYyA9IHRoaXMub3B0aW9ucy5vbkNvbW1lbnQgJiYgdGhpcy5vcHRpb25zLmxvY2F0aW9ucyAmJiB0aGlzLmN1clBvc2l0aW9uKCk7XG4gIHZhciBzdGFydCA9IHRoaXMucG9zLFxuICAgICAgZW5kID0gdGhpcy5pbnB1dC5pbmRleE9mKFwiKi9cIiwgdGhpcy5wb3MgKz0gMik7XG4gIGlmIChlbmQgPT09IC0xKSB0aGlzLnJhaXNlKHRoaXMucG9zIC0gMiwgXCJVbnRlcm1pbmF0ZWQgY29tbWVudFwiKTtcbiAgdGhpcy5wb3MgPSBlbmQgKyAyO1xuICBpZiAodGhpcy5vcHRpb25zLmxvY2F0aW9ucykge1xuICAgIGxpbmVCcmVha0cubGFzdEluZGV4ID0gc3RhcnQ7XG4gICAgdmFyIG1hdGNoID0gdW5kZWZpbmVkO1xuICAgIHdoaWxlICgobWF0Y2ggPSBsaW5lQnJlYWtHLmV4ZWModGhpcy5pbnB1dCkpICYmIG1hdGNoLmluZGV4IDwgdGhpcy5wb3MpIHtcbiAgICAgICsrdGhpcy5jdXJMaW5lO1xuICAgICAgdGhpcy5saW5lU3RhcnQgPSBtYXRjaC5pbmRleCArIG1hdGNoWzBdLmxlbmd0aDtcbiAgICB9XG4gIH1cbiAgaWYgKHRoaXMub3B0aW9ucy5vbkNvbW1lbnQpIHRoaXMub3B0aW9ucy5vbkNvbW1lbnQodHJ1ZSwgdGhpcy5pbnB1dC5zbGljZShzdGFydCArIDIsIGVuZCksIHN0YXJ0LCB0aGlzLnBvcywgc3RhcnRMb2MsIHRoaXMub3B0aW9ucy5sb2NhdGlvbnMgJiYgdGhpcy5jdXJQb3NpdGlvbigpKTtcbn07XG5cbnBwLnNraXBMaW5lQ29tbWVudCA9IGZ1bmN0aW9uIChzdGFydFNraXApIHtcbiAgdmFyIHN0YXJ0ID0gdGhpcy5wb3M7XG4gIHZhciBzdGFydExvYyA9IHRoaXMub3B0aW9ucy5vbkNvbW1lbnQgJiYgdGhpcy5vcHRpb25zLmxvY2F0aW9ucyAmJiB0aGlzLmN1clBvc2l0aW9uKCk7XG4gIHZhciBjaCA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArPSBzdGFydFNraXApO1xuICB3aGlsZSAodGhpcy5wb3MgPCB0aGlzLmlucHV0Lmxlbmd0aCAmJiBjaCAhPT0gMTAgJiYgY2ggIT09IDEzICYmIGNoICE9PSA4MjMyICYmIGNoICE9PSA4MjMzKSB7XG4gICAgKyt0aGlzLnBvcztcbiAgICBjaCA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyk7XG4gIH1cbiAgaWYgKHRoaXMub3B0aW9ucy5vbkNvbW1lbnQpIHRoaXMub3B0aW9ucy5vbkNvbW1lbnQoZmFsc2UsIHRoaXMuaW5wdXQuc2xpY2Uoc3RhcnQgKyBzdGFydFNraXAsIHRoaXMucG9zKSwgc3RhcnQsIHRoaXMucG9zLCBzdGFydExvYywgdGhpcy5vcHRpb25zLmxvY2F0aW9ucyAmJiB0aGlzLmN1clBvc2l0aW9uKCkpO1xufTtcblxuLy8gQ2FsbGVkIGF0IHRoZSBzdGFydCBvZiB0aGUgcGFyc2UgYW5kIGFmdGVyIGV2ZXJ5IHRva2VuLiBTa2lwc1xuLy8gd2hpdGVzcGFjZSBhbmQgY29tbWVudHMsIGFuZC5cblxucHAuc2tpcFNwYWNlID0gZnVuY3Rpb24gKCkge1xuICB3aGlsZSAodGhpcy5wb3MgPCB0aGlzLmlucHV0Lmxlbmd0aCkge1xuICAgIHZhciBjaCA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyk7XG4gICAgaWYgKGNoID09PSAzMikge1xuICAgICAgLy8gJyAnXG4gICAgICArK3RoaXMucG9zO1xuICAgIH0gZWxzZSBpZiAoY2ggPT09IDEzKSB7XG4gICAgICArK3RoaXMucG9zO1xuICAgICAgdmFyIG5leHQgPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MpO1xuICAgICAgaWYgKG5leHQgPT09IDEwKSB7XG4gICAgICAgICsrdGhpcy5wb3M7XG4gICAgICB9XG4gICAgICBpZiAodGhpcy5vcHRpb25zLmxvY2F0aW9ucykge1xuICAgICAgICArK3RoaXMuY3VyTGluZTtcbiAgICAgICAgdGhpcy5saW5lU3RhcnQgPSB0aGlzLnBvcztcbiAgICAgIH1cbiAgICB9IGVsc2UgaWYgKGNoID09PSAxMCB8fCBjaCA9PT0gODIzMiB8fCBjaCA9PT0gODIzMykge1xuICAgICAgKyt0aGlzLnBvcztcbiAgICAgIGlmICh0aGlzLm9wdGlvbnMubG9jYXRpb25zKSB7XG4gICAgICAgICsrdGhpcy5jdXJMaW5lO1xuICAgICAgICB0aGlzLmxpbmVTdGFydCA9IHRoaXMucG9zO1xuICAgICAgfVxuICAgIH0gZWxzZSBpZiAoY2ggPiA4ICYmIGNoIDwgMTQpIHtcbiAgICAgICsrdGhpcy5wb3M7XG4gICAgfSBlbHNlIGlmIChjaCA9PT0gNDcpIHtcbiAgICAgIC8vICcvJ1xuICAgICAgdmFyIG5leHQgPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAxKTtcbiAgICAgIGlmIChuZXh0ID09PSA0Mikge1xuICAgICAgICAvLyAnKidcbiAgICAgICAgdGhpcy5za2lwQmxvY2tDb21tZW50KCk7XG4gICAgICB9IGVsc2UgaWYgKG5leHQgPT09IDQ3KSB7XG4gICAgICAgIC8vICcvJ1xuICAgICAgICB0aGlzLnNraXBMaW5lQ29tbWVudCgyKTtcbiAgICAgIH0gZWxzZSBicmVhaztcbiAgICB9IGVsc2UgaWYgKGNoID09PSAxNjApIHtcbiAgICAgIC8vICdcXHhhMCdcbiAgICAgICsrdGhpcy5wb3M7XG4gICAgfSBlbHNlIGlmIChjaCA+PSA1NzYwICYmIG5vbkFTQ0lJd2hpdGVzcGFjZS50ZXN0KFN0cmluZy5mcm9tQ2hhckNvZGUoY2gpKSkge1xuICAgICAgKyt0aGlzLnBvcztcbiAgICB9IGVsc2Uge1xuICAgICAgYnJlYWs7XG4gICAgfVxuICB9XG59O1xuXG4vLyBDYWxsZWQgYXQgdGhlIGVuZCBvZiBldmVyeSB0b2tlbi4gU2V0cyBgZW5kYCwgYHZhbGAsIGFuZFxuLy8gbWFpbnRhaW5zIGBjb250ZXh0YCBhbmQgYGV4cHJBbGxvd2VkYCwgYW5kIHNraXBzIHRoZSBzcGFjZSBhZnRlclxuLy8gdGhlIHRva2VuLCBzbyB0aGF0IHRoZSBuZXh0IG9uZSdzIGBzdGFydGAgd2lsbCBwb2ludCBhdCB0aGVcbi8vIHJpZ2h0IHBvc2l0aW9uLlxuXG5wcC5maW5pc2hUb2tlbiA9IGZ1bmN0aW9uICh0eXBlLCB2YWwpIHtcbiAgdGhpcy5lbmQgPSB0aGlzLnBvcztcbiAgaWYgKHRoaXMub3B0aW9ucy5sb2NhdGlvbnMpIHRoaXMuZW5kTG9jID0gdGhpcy5jdXJQb3NpdGlvbigpO1xuICB2YXIgcHJldlR5cGUgPSB0aGlzLnR5cGU7XG4gIHRoaXMudHlwZSA9IHR5cGU7XG4gIHRoaXMudmFsdWUgPSB2YWw7XG5cbiAgdGhpcy51cGRhdGVDb250ZXh0KHByZXZUeXBlKTtcbn07XG5cbi8vICMjIyBUb2tlbiByZWFkaW5nXG5cbi8vIFRoaXMgaXMgdGhlIGZ1bmN0aW9uIHRoYXQgaXMgY2FsbGVkIHRvIGZldGNoIHRoZSBuZXh0IHRva2VuLiBJdFxuLy8gaXMgc29tZXdoYXQgb2JzY3VyZSwgYmVjYXVzZSBpdCB3b3JrcyBpbiBjaGFyYWN0ZXIgY29kZXMgcmF0aGVyXG4vLyB0aGFuIGNoYXJhY3RlcnMsIGFuZCBiZWNhdXNlIG9wZXJhdG9yIHBhcnNpbmcgaGFzIGJlZW4gaW5saW5lZFxuLy8gaW50byBpdC5cbi8vXG4vLyBBbGwgaW4gdGhlIG5hbWUgb2Ygc3BlZWQuXG4vL1xucHAucmVhZFRva2VuX2RvdCA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIG5leHQgPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAxKTtcbiAgaWYgKG5leHQgPj0gNDggJiYgbmV4dCA8PSA1NykgcmV0dXJuIHRoaXMucmVhZE51bWJlcih0cnVlKTtcbiAgdmFyIG5leHQyID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMik7XG4gIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNiAmJiBuZXh0ID09PSA0NiAmJiBuZXh0MiA9PT0gNDYpIHtcbiAgICAvLyA0NiA9IGRvdCAnLidcbiAgICB0aGlzLnBvcyArPSAzO1xuICAgIHJldHVybiB0aGlzLmZpbmlzaFRva2VuKHR0LmVsbGlwc2lzKTtcbiAgfSBlbHNlIHtcbiAgICArK3RoaXMucG9zO1xuICAgIHJldHVybiB0aGlzLmZpbmlzaFRva2VuKHR0LmRvdCk7XG4gIH1cbn07XG5cbnBwLnJlYWRUb2tlbl9zbGFzaCA9IGZ1bmN0aW9uICgpIHtcbiAgLy8gJy8nXG4gIHZhciBuZXh0ID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMSk7XG4gIGlmICh0aGlzLmV4cHJBbGxvd2VkKSB7XG4gICAgKyt0aGlzLnBvcztyZXR1cm4gdGhpcy5yZWFkUmVnZXhwKCk7XG4gIH1cbiAgaWYgKG5leHQgPT09IDYxKSByZXR1cm4gdGhpcy5maW5pc2hPcCh0dC5hc3NpZ24sIDIpO1xuICByZXR1cm4gdGhpcy5maW5pc2hPcCh0dC5zbGFzaCwgMSk7XG59O1xuXG5wcC5yZWFkVG9rZW5fbXVsdF9tb2R1bG8gPSBmdW5jdGlvbiAoY29kZSkge1xuICAvLyAnJSonXG4gIHZhciBuZXh0ID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMSk7XG4gIGlmIChuZXh0ID09PSA2MSkgcmV0dXJuIHRoaXMuZmluaXNoT3AodHQuYXNzaWduLCAyKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoT3AoY29kZSA9PT0gNDIgPyB0dC5zdGFyIDogdHQubW9kdWxvLCAxKTtcbn07XG5cbnBwLnJlYWRUb2tlbl9waXBlX2FtcCA9IGZ1bmN0aW9uIChjb2RlKSB7XG4gIC8vICd8JidcbiAgdmFyIG5leHQgPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAxKTtcbiAgaWYgKG5leHQgPT09IGNvZGUpIHJldHVybiB0aGlzLmZpbmlzaE9wKGNvZGUgPT09IDEyNCA/IHR0LmxvZ2ljYWxPUiA6IHR0LmxvZ2ljYWxBTkQsIDIpO1xuICBpZiAobmV4dCA9PT0gNjEpIHJldHVybiB0aGlzLmZpbmlzaE9wKHR0LmFzc2lnbiwgMik7XG4gIHJldHVybiB0aGlzLmZpbmlzaE9wKGNvZGUgPT09IDEyNCA/IHR0LmJpdHdpc2VPUiA6IHR0LmJpdHdpc2VBTkQsIDEpO1xufTtcblxucHAucmVhZFRva2VuX2NhcmV0ID0gZnVuY3Rpb24gKCkge1xuICAvLyAnXidcbiAgdmFyIG5leHQgPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAxKTtcbiAgaWYgKG5leHQgPT09IDYxKSByZXR1cm4gdGhpcy5maW5pc2hPcCh0dC5hc3NpZ24sIDIpO1xuICByZXR1cm4gdGhpcy5maW5pc2hPcCh0dC5iaXR3aXNlWE9SLCAxKTtcbn07XG5cbnBwLnJlYWRUb2tlbl9wbHVzX21pbiA9IGZ1bmN0aW9uIChjb2RlKSB7XG4gIC8vICcrLSdcbiAgdmFyIG5leHQgPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAxKTtcbiAgaWYgKG5leHQgPT09IGNvZGUpIHtcbiAgICBpZiAobmV4dCA9PSA0NSAmJiB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAyKSA9PSA2MiAmJiBsaW5lQnJlYWsudGVzdCh0aGlzLmlucHV0LnNsaWNlKHRoaXMubGFzdFRva0VuZCwgdGhpcy5wb3MpKSkge1xuICAgICAgLy8gQSBgLS0+YCBsaW5lIGNvbW1lbnRcbiAgICAgIHRoaXMuc2tpcExpbmVDb21tZW50KDMpO1xuICAgICAgdGhpcy5za2lwU3BhY2UoKTtcbiAgICAgIHJldHVybiB0aGlzLm5leHRUb2tlbigpO1xuICAgIH1cbiAgICByZXR1cm4gdGhpcy5maW5pc2hPcCh0dC5pbmNEZWMsIDIpO1xuICB9XG4gIGlmIChuZXh0ID09PSA2MSkgcmV0dXJuIHRoaXMuZmluaXNoT3AodHQuYXNzaWduLCAyKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoT3AodHQucGx1c01pbiwgMSk7XG59O1xuXG5wcC5yZWFkVG9rZW5fbHRfZ3QgPSBmdW5jdGlvbiAoY29kZSkge1xuICAvLyAnPD4nXG4gIHZhciBuZXh0ID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMSk7XG4gIHZhciBzaXplID0gMTtcbiAgaWYgKG5leHQgPT09IGNvZGUpIHtcbiAgICBzaXplID0gY29kZSA9PT0gNjIgJiYgdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMikgPT09IDYyID8gMyA6IDI7XG4gICAgaWYgKHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIHNpemUpID09PSA2MSkgcmV0dXJuIHRoaXMuZmluaXNoT3AodHQuYXNzaWduLCBzaXplICsgMSk7XG4gICAgcmV0dXJuIHRoaXMuZmluaXNoT3AodHQuYml0U2hpZnQsIHNpemUpO1xuICB9XG4gIGlmIChuZXh0ID09IDMzICYmIGNvZGUgPT0gNjAgJiYgdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMikgPT0gNDUgJiYgdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMykgPT0gNDUpIHtcbiAgICBpZiAodGhpcy5pbk1vZHVsZSkgdGhpcy51bmV4cGVjdGVkKCk7XG4gICAgLy8gYDwhLS1gLCBhbiBYTUwtc3R5bGUgY29tbWVudCB0aGF0IHNob3VsZCBiZSBpbnRlcnByZXRlZCBhcyBhIGxpbmUgY29tbWVudFxuICAgIHRoaXMuc2tpcExpbmVDb21tZW50KDQpO1xuICAgIHRoaXMuc2tpcFNwYWNlKCk7XG4gICAgcmV0dXJuIHRoaXMubmV4dFRva2VuKCk7XG4gIH1cbiAgaWYgKG5leHQgPT09IDYxKSBzaXplID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMikgPT09IDYxID8gMyA6IDI7XG4gIHJldHVybiB0aGlzLmZpbmlzaE9wKHR0LnJlbGF0aW9uYWwsIHNpemUpO1xufTtcblxucHAucmVhZFRva2VuX2VxX2V4Y2wgPSBmdW5jdGlvbiAoY29kZSkge1xuICAvLyAnPSEnXG4gIHZhciBuZXh0ID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMSk7XG4gIGlmIChuZXh0ID09PSA2MSkgcmV0dXJuIHRoaXMuZmluaXNoT3AodHQuZXF1YWxpdHksIHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIDIpID09PSA2MSA/IDMgOiAyKTtcbiAgaWYgKGNvZGUgPT09IDYxICYmIG5leHQgPT09IDYyICYmIHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KSB7XG4gICAgLy8gJz0+J1xuICAgIHRoaXMucG9zICs9IDI7XG4gICAgcmV0dXJuIHRoaXMuZmluaXNoVG9rZW4odHQuYXJyb3cpO1xuICB9XG4gIHJldHVybiB0aGlzLmZpbmlzaE9wKGNvZGUgPT09IDYxID8gdHQuZXEgOiB0dC5wcmVmaXgsIDEpO1xufTtcblxucHAuZ2V0VG9rZW5Gcm9tQ29kZSA9IGZ1bmN0aW9uIChjb2RlKSB7XG4gIHN3aXRjaCAoY29kZSkge1xuICAgIC8vIFRoZSBpbnRlcnByZXRhdGlvbiBvZiBhIGRvdCBkZXBlbmRzIG9uIHdoZXRoZXIgaXQgaXMgZm9sbG93ZWRcbiAgICAvLyBieSBhIGRpZ2l0IG9yIGFub3RoZXIgdHdvIGRvdHMuXG4gICAgY2FzZSA0NjpcbiAgICAgIC8vICcuJ1xuICAgICAgcmV0dXJuIHRoaXMucmVhZFRva2VuX2RvdCgpO1xuXG4gICAgLy8gUHVuY3R1YXRpb24gdG9rZW5zLlxuICAgIGNhc2UgNDA6XG4gICAgICArK3RoaXMucG9zO3JldHVybiB0aGlzLmZpbmlzaFRva2VuKHR0LnBhcmVuTCk7XG4gICAgY2FzZSA0MTpcbiAgICAgICsrdGhpcy5wb3M7cmV0dXJuIHRoaXMuZmluaXNoVG9rZW4odHQucGFyZW5SKTtcbiAgICBjYXNlIDU5OlxuICAgICAgKyt0aGlzLnBvcztyZXR1cm4gdGhpcy5maW5pc2hUb2tlbih0dC5zZW1pKTtcbiAgICBjYXNlIDQ0OlxuICAgICAgKyt0aGlzLnBvcztyZXR1cm4gdGhpcy5maW5pc2hUb2tlbih0dC5jb21tYSk7XG4gICAgY2FzZSA5MTpcbiAgICAgICsrdGhpcy5wb3M7cmV0dXJuIHRoaXMuZmluaXNoVG9rZW4odHQuYnJhY2tldEwpO1xuICAgIGNhc2UgOTM6XG4gICAgICArK3RoaXMucG9zO3JldHVybiB0aGlzLmZpbmlzaFRva2VuKHR0LmJyYWNrZXRSKTtcbiAgICBjYXNlIDEyMzpcbiAgICAgICsrdGhpcy5wb3M7cmV0dXJuIHRoaXMuZmluaXNoVG9rZW4odHQuYnJhY2VMKTtcbiAgICBjYXNlIDEyNTpcbiAgICAgICsrdGhpcy5wb3M7cmV0dXJuIHRoaXMuZmluaXNoVG9rZW4odHQuYnJhY2VSKTtcbiAgICBjYXNlIDU4OlxuICAgICAgKyt0aGlzLnBvcztyZXR1cm4gdGhpcy5maW5pc2hUb2tlbih0dC5jb2xvbik7XG4gICAgY2FzZSA2MzpcbiAgICAgICsrdGhpcy5wb3M7cmV0dXJuIHRoaXMuZmluaXNoVG9rZW4odHQucXVlc3Rpb24pO1xuXG4gICAgY2FzZSA5NjpcbiAgICAgIC8vICdgJ1xuICAgICAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA8IDYpIGJyZWFrO1xuICAgICAgKyt0aGlzLnBvcztcbiAgICAgIHJldHVybiB0aGlzLmZpbmlzaFRva2VuKHR0LmJhY2tRdW90ZSk7XG5cbiAgICBjYXNlIDQ4OlxuICAgICAgLy8gJzAnXG4gICAgICB2YXIgbmV4dCA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIDEpO1xuICAgICAgaWYgKG5leHQgPT09IDEyMCB8fCBuZXh0ID09PSA4OCkgcmV0dXJuIHRoaXMucmVhZFJhZGl4TnVtYmVyKDE2KTsgLy8gJzB4JywgJzBYJyAtIGhleCBudW1iZXJcbiAgICAgIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNikge1xuICAgICAgICBpZiAobmV4dCA9PT0gMTExIHx8IG5leHQgPT09IDc5KSByZXR1cm4gdGhpcy5yZWFkUmFkaXhOdW1iZXIoOCk7IC8vICcwbycsICcwTycgLSBvY3RhbCBudW1iZXJcbiAgICAgICAgaWYgKG5leHQgPT09IDk4IHx8IG5leHQgPT09IDY2KSByZXR1cm4gdGhpcy5yZWFkUmFkaXhOdW1iZXIoMik7IC8vICcwYicsICcwQicgLSBiaW5hcnkgbnVtYmVyXG4gICAgICB9XG4gICAgLy8gQW55dGhpbmcgZWxzZSBiZWdpbm5pbmcgd2l0aCBhIGRpZ2l0IGlzIGFuIGludGVnZXIsIG9jdGFsXG4gICAgLy8gbnVtYmVyLCBvciBmbG9hdC5cbiAgICBjYXNlIDQ5OmNhc2UgNTA6Y2FzZSA1MTpjYXNlIDUyOmNhc2UgNTM6Y2FzZSA1NDpjYXNlIDU1OmNhc2UgNTY6Y2FzZSA1NzpcbiAgICAgIC8vIDEtOVxuICAgICAgcmV0dXJuIHRoaXMucmVhZE51bWJlcihmYWxzZSk7XG5cbiAgICAvLyBRdW90ZXMgcHJvZHVjZSBzdHJpbmdzLlxuICAgIGNhc2UgMzQ6Y2FzZSAzOTpcbiAgICAgIC8vICdcIicsIFwiJ1wiXG4gICAgICByZXR1cm4gdGhpcy5yZWFkU3RyaW5nKGNvZGUpO1xuXG4gICAgLy8gT3BlcmF0b3JzIGFyZSBwYXJzZWQgaW5saW5lIGluIHRpbnkgc3RhdGUgbWFjaGluZXMuICc9JyAoNjEpIGlzXG4gICAgLy8gb2Z0ZW4gcmVmZXJyZWQgdG8uIGBmaW5pc2hPcGAgc2ltcGx5IHNraXBzIHRoZSBhbW91bnQgb2ZcbiAgICAvLyBjaGFyYWN0ZXJzIGl0IGlzIGdpdmVuIGFzIHNlY29uZCBhcmd1bWVudCwgYW5kIHJldHVybnMgYSB0b2tlblxuICAgIC8vIG9mIHRoZSB0eXBlIGdpdmVuIGJ5IGl0cyBmaXJzdCBhcmd1bWVudC5cblxuICAgIGNhc2UgNDc6XG4gICAgICAvLyAnLydcbiAgICAgIHJldHVybiB0aGlzLnJlYWRUb2tlbl9zbGFzaCgpO1xuXG4gICAgY2FzZSAzNzpjYXNlIDQyOlxuICAgICAgLy8gJyUqJ1xuICAgICAgcmV0dXJuIHRoaXMucmVhZFRva2VuX211bHRfbW9kdWxvKGNvZGUpO1xuXG4gICAgY2FzZSAxMjQ6Y2FzZSAzODpcbiAgICAgIC8vICd8JidcbiAgICAgIHJldHVybiB0aGlzLnJlYWRUb2tlbl9waXBlX2FtcChjb2RlKTtcblxuICAgIGNhc2UgOTQ6XG4gICAgICAvLyAnXidcbiAgICAgIHJldHVybiB0aGlzLnJlYWRUb2tlbl9jYXJldCgpO1xuXG4gICAgY2FzZSA0MzpjYXNlIDQ1OlxuICAgICAgLy8gJystJ1xuICAgICAgcmV0dXJuIHRoaXMucmVhZFRva2VuX3BsdXNfbWluKGNvZGUpO1xuXG4gICAgY2FzZSA2MDpjYXNlIDYyOlxuICAgICAgLy8gJzw+J1xuICAgICAgcmV0dXJuIHRoaXMucmVhZFRva2VuX2x0X2d0KGNvZGUpO1xuXG4gICAgY2FzZSA2MTpjYXNlIDMzOlxuICAgICAgLy8gJz0hJ1xuICAgICAgcmV0dXJuIHRoaXMucmVhZFRva2VuX2VxX2V4Y2woY29kZSk7XG5cbiAgICBjYXNlIDEyNjpcbiAgICAgIC8vICd+J1xuICAgICAgcmV0dXJuIHRoaXMuZmluaXNoT3AodHQucHJlZml4LCAxKTtcbiAgfVxuXG4gIHRoaXMucmFpc2UodGhpcy5wb3MsIFwiVW5leHBlY3RlZCBjaGFyYWN0ZXIgJ1wiICsgY29kZVBvaW50VG9TdHJpbmcoY29kZSkgKyBcIidcIik7XG59O1xuXG5wcC5maW5pc2hPcCA9IGZ1bmN0aW9uICh0eXBlLCBzaXplKSB7XG4gIHZhciBzdHIgPSB0aGlzLmlucHV0LnNsaWNlKHRoaXMucG9zLCB0aGlzLnBvcyArIHNpemUpO1xuICB0aGlzLnBvcyArPSBzaXplO1xuICByZXR1cm4gdGhpcy5maW5pc2hUb2tlbih0eXBlLCBzdHIpO1xufTtcblxudmFyIHJlZ2V4cFVuaWNvZGVTdXBwb3J0ID0gZmFsc2U7XG50cnkge1xuICBuZXcgUmVnRXhwKFwi77+/XCIsIFwidVwiKTtyZWdleHBVbmljb2RlU3VwcG9ydCA9IHRydWU7XG59IGNhdGNoIChlKSB7fVxuXG4vLyBQYXJzZSBhIHJlZ3VsYXIgZXhwcmVzc2lvbi4gU29tZSBjb250ZXh0LWF3YXJlbmVzcyBpcyBuZWNlc3NhcnksXG4vLyBzaW5jZSBhICcvJyBpbnNpZGUgYSAnW10nIHNldCBkb2VzIG5vdCBlbmQgdGhlIGV4cHJlc3Npb24uXG5cbnBwLnJlYWRSZWdleHAgPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBlc2NhcGVkID0gdW5kZWZpbmVkLFxuICAgICAgaW5DbGFzcyA9IHVuZGVmaW5lZCxcbiAgICAgIHN0YXJ0ID0gdGhpcy5wb3M7XG4gIGZvciAoOzspIHtcbiAgICBpZiAodGhpcy5wb3MgPj0gdGhpcy5pbnB1dC5sZW5ndGgpIHRoaXMucmFpc2Uoc3RhcnQsIFwiVW50ZXJtaW5hdGVkIHJlZ3VsYXIgZXhwcmVzc2lvblwiKTtcbiAgICB2YXIgY2ggPSB0aGlzLmlucHV0LmNoYXJBdCh0aGlzLnBvcyk7XG4gICAgaWYgKGxpbmVCcmVhay50ZXN0KGNoKSkgdGhpcy5yYWlzZShzdGFydCwgXCJVbnRlcm1pbmF0ZWQgcmVndWxhciBleHByZXNzaW9uXCIpO1xuICAgIGlmICghZXNjYXBlZCkge1xuICAgICAgaWYgKGNoID09PSBcIltcIikgaW5DbGFzcyA9IHRydWU7ZWxzZSBpZiAoY2ggPT09IFwiXVwiICYmIGluQ2xhc3MpIGluQ2xhc3MgPSBmYWxzZTtlbHNlIGlmIChjaCA9PT0gXCIvXCIgJiYgIWluQ2xhc3MpIGJyZWFrO1xuICAgICAgZXNjYXBlZCA9IGNoID09PSBcIlxcXFxcIjtcbiAgICB9IGVsc2UgZXNjYXBlZCA9IGZhbHNlO1xuICAgICsrdGhpcy5wb3M7XG4gIH1cbiAgdmFyIGNvbnRlbnQgPSB0aGlzLmlucHV0LnNsaWNlKHN0YXJ0LCB0aGlzLnBvcyk7XG4gICsrdGhpcy5wb3M7XG4gIC8vIE5lZWQgdG8gdXNlIGByZWFkV29yZDFgIGJlY2F1c2UgJ1xcdVhYWFgnIHNlcXVlbmNlcyBhcmUgYWxsb3dlZFxuICAvLyBoZXJlIChkb24ndCBhc2spLlxuICB2YXIgbW9kcyA9IHRoaXMucmVhZFdvcmQxKCk7XG4gIHZhciB0bXAgPSBjb250ZW50O1xuICBpZiAobW9kcykge1xuICAgIHZhciB2YWxpZEZsYWdzID0gL15bZ21zaXldKiQvO1xuICAgIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNikgdmFsaWRGbGFncyA9IC9eW2dtc2l5dV0qJC87XG4gICAgaWYgKCF2YWxpZEZsYWdzLnRlc3QobW9kcykpIHRoaXMucmFpc2Uoc3RhcnQsIFwiSW52YWxpZCByZWd1bGFyIGV4cHJlc3Npb24gZmxhZ1wiKTtcbiAgICBpZiAobW9kcy5pbmRleE9mKFwidVwiKSA+PSAwICYmICFyZWdleHBVbmljb2RlU3VwcG9ydCkge1xuICAgICAgLy8gUmVwbGFjZSBlYWNoIGFzdHJhbCBzeW1ib2wgYW5kIGV2ZXJ5IFVuaWNvZGUgZXNjYXBlIHNlcXVlbmNlIHRoYXRcbiAgICAgIC8vIHBvc3NpYmx5IHJlcHJlc2VudHMgYW4gYXN0cmFsIHN5bWJvbCBvciBhIHBhaXJlZCBzdXJyb2dhdGUgd2l0aCBhXG4gICAgICAvLyBzaW5nbGUgQVNDSUkgc3ltYm9sIHRvIGF2b2lkIHRocm93aW5nIG9uIHJlZ3VsYXIgZXhwcmVzc2lvbnMgdGhhdFxuICAgICAgLy8gYXJlIG9ubHkgdmFsaWQgaW4gY29tYmluYXRpb24gd2l0aCB0aGUgYC91YCBmbGFnLlxuICAgICAgLy8gTm90ZTogcmVwbGFjaW5nIHdpdGggdGhlIEFTQ0lJIHN5bWJvbCBgeGAgbWlnaHQgY2F1c2UgZmFsc2VcbiAgICAgIC8vIG5lZ2F0aXZlcyBpbiB1bmxpa2VseSBzY2VuYXJpb3MuIEZvciBleGFtcGxlLCBgW1xcdXs2MX0tYl1gIGlzIGFcbiAgICAgIC8vIHBlcmZlY3RseSB2YWxpZCBwYXR0ZXJuIHRoYXQgaXMgZXF1aXZhbGVudCB0byBgW2EtYl1gLCBidXQgaXQgd291bGRcbiAgICAgIC8vIGJlIHJlcGxhY2VkIGJ5IGBbeC1iXWAgd2hpY2ggdGhyb3dzIGFuIGVycm9yLlxuICAgICAgdG1wID0gdG1wLnJlcGxhY2UoL1xcXFx1KFthLWZBLUYwLTldezR9KXxcXFxcdVxceyhbMC05YS1mQS1GXSspXFx9fFtcXHVEODAwLVxcdURCRkZdW1xcdURDMDAtXFx1REZGRl0vZywgXCJ4XCIpO1xuICAgIH1cbiAgfVxuICAvLyBEZXRlY3QgaW52YWxpZCByZWd1bGFyIGV4cHJlc3Npb25zLlxuICB2YXIgdmFsdWUgPSBudWxsO1xuICAvLyBSaGlubydzIHJlZ3VsYXIgZXhwcmVzc2lvbiBwYXJzZXIgaXMgZmxha3kgYW5kIHRocm93cyB1bmNhdGNoYWJsZSBleGNlcHRpb25zLFxuICAvLyBzbyBkb24ndCBkbyBkZXRlY3Rpb24gaWYgd2UgYXJlIHJ1bm5pbmcgdW5kZXIgUmhpbm9cbiAgaWYgKCFpc1JoaW5vKSB7XG4gICAgdHJ5IHtcbiAgICAgIG5ldyBSZWdFeHAodG1wKTtcbiAgICB9IGNhdGNoIChlKSB7XG4gICAgICBpZiAoZSBpbnN0YW5jZW9mIFN5bnRheEVycm9yKSB0aGlzLnJhaXNlKHN0YXJ0LCBcIkVycm9yIHBhcnNpbmcgcmVndWxhciBleHByZXNzaW9uOiBcIiArIGUubWVzc2FnZSk7XG4gICAgICB0aGlzLnJhaXNlKGUpO1xuICAgIH1cbiAgICAvLyBHZXQgYSByZWd1bGFyIGV4cHJlc3Npb24gb2JqZWN0IGZvciB0aGlzIHBhdHRlcm4tZmxhZyBwYWlyLCBvciBgbnVsbGAgaW5cbiAgICAvLyBjYXNlIHRoZSBjdXJyZW50IGVudmlyb25tZW50IGRvZXNuJ3Qgc3VwcG9ydCB0aGUgZmxhZ3MgaXQgdXNlcy5cbiAgICB0cnkge1xuICAgICAgdmFsdWUgPSBuZXcgUmVnRXhwKGNvbnRlbnQsIG1vZHMpO1xuICAgIH0gY2F0Y2ggKGVycikge31cbiAgfVxuICByZXR1cm4gdGhpcy5maW5pc2hUb2tlbih0dC5yZWdleHAsIHsgcGF0dGVybjogY29udGVudCwgZmxhZ3M6IG1vZHMsIHZhbHVlOiB2YWx1ZSB9KTtcbn07XG5cbi8vIFJlYWQgYW4gaW50ZWdlciBpbiB0aGUgZ2l2ZW4gcmFkaXguIFJldHVybiBudWxsIGlmIHplcm8gZGlnaXRzXG4vLyB3ZXJlIHJlYWQsIHRoZSBpbnRlZ2VyIHZhbHVlIG90aGVyd2lzZS4gV2hlbiBgbGVuYCBpcyBnaXZlbiwgdGhpc1xuLy8gd2lsbCByZXR1cm4gYG51bGxgIHVubGVzcyB0aGUgaW50ZWdlciBoYXMgZXhhY3RseSBgbGVuYCBkaWdpdHMuXG5cbnBwLnJlYWRJbnQgPSBmdW5jdGlvbiAocmFkaXgsIGxlbikge1xuICB2YXIgc3RhcnQgPSB0aGlzLnBvcyxcbiAgICAgIHRvdGFsID0gMDtcbiAgZm9yICh2YXIgaSA9IDAsIGUgPSBsZW4gPT0gbnVsbCA/IEluZmluaXR5IDogbGVuOyBpIDwgZTsgKytpKSB7XG4gICAgdmFyIGNvZGUgPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MpLFxuICAgICAgICB2YWwgPSB1bmRlZmluZWQ7XG4gICAgaWYgKGNvZGUgPj0gOTcpIHZhbCA9IGNvZGUgLSA5NyArIDEwOyAvLyBhXG4gICAgZWxzZSBpZiAoY29kZSA+PSA2NSkgdmFsID0gY29kZSAtIDY1ICsgMTA7IC8vIEFcbiAgICBlbHNlIGlmIChjb2RlID49IDQ4ICYmIGNvZGUgPD0gNTcpIHZhbCA9IGNvZGUgLSA0ODsgLy8gMC05XG4gICAgZWxzZSB2YWwgPSBJbmZpbml0eTtcbiAgICBpZiAodmFsID49IHJhZGl4KSBicmVhaztcbiAgICArK3RoaXMucG9zO1xuICAgIHRvdGFsID0gdG90YWwgKiByYWRpeCArIHZhbDtcbiAgfVxuICBpZiAodGhpcy5wb3MgPT09IHN0YXJ0IHx8IGxlbiAhPSBudWxsICYmIHRoaXMucG9zIC0gc3RhcnQgIT09IGxlbikgcmV0dXJuIG51bGw7XG5cbiAgcmV0dXJuIHRvdGFsO1xufTtcblxucHAucmVhZFJhZGl4TnVtYmVyID0gZnVuY3Rpb24gKHJhZGl4KSB7XG4gIHRoaXMucG9zICs9IDI7IC8vIDB4XG4gIHZhciB2YWwgPSB0aGlzLnJlYWRJbnQocmFkaXgpO1xuICBpZiAodmFsID09IG51bGwpIHRoaXMucmFpc2UodGhpcy5zdGFydCArIDIsIFwiRXhwZWN0ZWQgbnVtYmVyIGluIHJhZGl4IFwiICsgcmFkaXgpO1xuICBpZiAoaXNJZGVudGlmaWVyU3RhcnQodGhpcy5mdWxsQ2hhckNvZGVBdFBvcygpKSkgdGhpcy5yYWlzZSh0aGlzLnBvcywgXCJJZGVudGlmaWVyIGRpcmVjdGx5IGFmdGVyIG51bWJlclwiKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoVG9rZW4odHQubnVtLCB2YWwpO1xufTtcblxuLy8gUmVhZCBhbiBpbnRlZ2VyLCBvY3RhbCBpbnRlZ2VyLCBvciBmbG9hdGluZy1wb2ludCBudW1iZXIuXG5cbnBwLnJlYWROdW1iZXIgPSBmdW5jdGlvbiAoc3RhcnRzV2l0aERvdCkge1xuICB2YXIgc3RhcnQgPSB0aGlzLnBvcyxcbiAgICAgIGlzRmxvYXQgPSBmYWxzZSxcbiAgICAgIG9jdGFsID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zKSA9PT0gNDg7XG4gIGlmICghc3RhcnRzV2l0aERvdCAmJiB0aGlzLnJlYWRJbnQoMTApID09PSBudWxsKSB0aGlzLnJhaXNlKHN0YXJ0LCBcIkludmFsaWQgbnVtYmVyXCIpO1xuICBpZiAodGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zKSA9PT0gNDYpIHtcbiAgICArK3RoaXMucG9zO1xuICAgIHRoaXMucmVhZEludCgxMCk7XG4gICAgaXNGbG9hdCA9IHRydWU7XG4gIH1cbiAgdmFyIG5leHQgPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MpO1xuICBpZiAobmV4dCA9PT0gNjkgfHwgbmV4dCA9PT0gMTAxKSB7XG4gICAgLy8gJ2VFJ1xuICAgIG5leHQgPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQoKyt0aGlzLnBvcyk7XG4gICAgaWYgKG5leHQgPT09IDQzIHx8IG5leHQgPT09IDQ1KSArK3RoaXMucG9zOyAvLyAnKy0nXG4gICAgaWYgKHRoaXMucmVhZEludCgxMCkgPT09IG51bGwpIHRoaXMucmFpc2Uoc3RhcnQsIFwiSW52YWxpZCBudW1iZXJcIik7XG4gICAgaXNGbG9hdCA9IHRydWU7XG4gIH1cbiAgaWYgKGlzSWRlbnRpZmllclN0YXJ0KHRoaXMuZnVsbENoYXJDb2RlQXRQb3MoKSkpIHRoaXMucmFpc2UodGhpcy5wb3MsIFwiSWRlbnRpZmllciBkaXJlY3RseSBhZnRlciBudW1iZXJcIik7XG5cbiAgdmFyIHN0ciA9IHRoaXMuaW5wdXQuc2xpY2Uoc3RhcnQsIHRoaXMucG9zKSxcbiAgICAgIHZhbCA9IHVuZGVmaW5lZDtcbiAgaWYgKGlzRmxvYXQpIHZhbCA9IHBhcnNlRmxvYXQoc3RyKTtlbHNlIGlmICghb2N0YWwgfHwgc3RyLmxlbmd0aCA9PT0gMSkgdmFsID0gcGFyc2VJbnQoc3RyLCAxMCk7ZWxzZSBpZiAoL1s4OV0vLnRlc3Qoc3RyKSB8fCB0aGlzLnN0cmljdCkgdGhpcy5yYWlzZShzdGFydCwgXCJJbnZhbGlkIG51bWJlclwiKTtlbHNlIHZhbCA9IHBhcnNlSW50KHN0ciwgOCk7XG4gIHJldHVybiB0aGlzLmZpbmlzaFRva2VuKHR0Lm51bSwgdmFsKTtcbn07XG5cbi8vIFJlYWQgYSBzdHJpbmcgdmFsdWUsIGludGVycHJldGluZyBiYWNrc2xhc2gtZXNjYXBlcy5cblxucHAucmVhZENvZGVQb2ludCA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIGNoID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zKSxcbiAgICAgIGNvZGUgPSB1bmRlZmluZWQ7XG5cbiAgaWYgKGNoID09PSAxMjMpIHtcbiAgICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uIDwgNikgdGhpcy51bmV4cGVjdGVkKCk7XG4gICAgKyt0aGlzLnBvcztcbiAgICBjb2RlID0gdGhpcy5yZWFkSGV4Q2hhcih0aGlzLmlucHV0LmluZGV4T2YoXCJ9XCIsIHRoaXMucG9zKSAtIHRoaXMucG9zKTtcbiAgICArK3RoaXMucG9zO1xuICAgIGlmIChjb2RlID4gMTExNDExMSkgdGhpcy51bmV4cGVjdGVkKCk7XG4gIH0gZWxzZSB7XG4gICAgY29kZSA9IHRoaXMucmVhZEhleENoYXIoNCk7XG4gIH1cbiAgcmV0dXJuIGNvZGU7XG59O1xuXG5mdW5jdGlvbiBjb2RlUG9pbnRUb1N0cmluZyhjb2RlKSB7XG4gIC8vIFVURi0xNiBEZWNvZGluZ1xuICBpZiAoY29kZSA8PSA2NTUzNSkge1xuICAgIHJldHVybiBTdHJpbmcuZnJvbUNoYXJDb2RlKGNvZGUpO1xuICB9cmV0dXJuIFN0cmluZy5mcm9tQ2hhckNvZGUoKGNvZGUgLSA2NTUzNiA+PiAxMCkgKyA1NTI5NiwgKGNvZGUgLSA2NTUzNiAmIDEwMjMpICsgNTYzMjApO1xufVxuXG5wcC5yZWFkU3RyaW5nID0gZnVuY3Rpb24gKHF1b3RlKSB7XG4gIHZhciBvdXQgPSBcIlwiLFxuICAgICAgY2h1bmtTdGFydCA9ICsrdGhpcy5wb3M7XG4gIGZvciAoOzspIHtcbiAgICBpZiAodGhpcy5wb3MgPj0gdGhpcy5pbnB1dC5sZW5ndGgpIHRoaXMucmFpc2UodGhpcy5zdGFydCwgXCJVbnRlcm1pbmF0ZWQgc3RyaW5nIGNvbnN0YW50XCIpO1xuICAgIHZhciBjaCA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyk7XG4gICAgaWYgKGNoID09PSBxdW90ZSkgYnJlYWs7XG4gICAgaWYgKGNoID09PSA5Mikge1xuICAgICAgLy8gJ1xcJ1xuICAgICAgb3V0ICs9IHRoaXMuaW5wdXQuc2xpY2UoY2h1bmtTdGFydCwgdGhpcy5wb3MpO1xuICAgICAgb3V0ICs9IHRoaXMucmVhZEVzY2FwZWRDaGFyKCk7XG4gICAgICBjaHVua1N0YXJ0ID0gdGhpcy5wb3M7XG4gICAgfSBlbHNlIHtcbiAgICAgIGlmIChpc05ld0xpbmUoY2gpKSB0aGlzLnJhaXNlKHRoaXMuc3RhcnQsIFwiVW50ZXJtaW5hdGVkIHN0cmluZyBjb25zdGFudFwiKTtcbiAgICAgICsrdGhpcy5wb3M7XG4gICAgfVxuICB9XG4gIG91dCArPSB0aGlzLmlucHV0LnNsaWNlKGNodW5rU3RhcnQsIHRoaXMucG9zKyspO1xuICByZXR1cm4gdGhpcy5maW5pc2hUb2tlbih0dC5zdHJpbmcsIG91dCk7XG59O1xuXG4vLyBSZWFkcyB0ZW1wbGF0ZSBzdHJpbmcgdG9rZW5zLlxuXG5wcC5yZWFkVG1wbFRva2VuID0gZnVuY3Rpb24gKCkge1xuICB2YXIgb3V0ID0gXCJcIixcbiAgICAgIGNodW5rU3RhcnQgPSB0aGlzLnBvcztcbiAgZm9yICg7Oykge1xuICAgIGlmICh0aGlzLnBvcyA+PSB0aGlzLmlucHV0Lmxlbmd0aCkgdGhpcy5yYWlzZSh0aGlzLnN0YXJ0LCBcIlVudGVybWluYXRlZCB0ZW1wbGF0ZVwiKTtcbiAgICB2YXIgY2ggPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MpO1xuICAgIGlmIChjaCA9PT0gOTYgfHwgY2ggPT09IDM2ICYmIHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIDEpID09PSAxMjMpIHtcbiAgICAgIC8vICdgJywgJyR7J1xuICAgICAgaWYgKHRoaXMucG9zID09PSB0aGlzLnN0YXJ0ICYmIHRoaXMudHlwZSA9PT0gdHQudGVtcGxhdGUpIHtcbiAgICAgICAgaWYgKGNoID09PSAzNikge1xuICAgICAgICAgIHRoaXMucG9zICs9IDI7XG4gICAgICAgICAgcmV0dXJuIHRoaXMuZmluaXNoVG9rZW4odHQuZG9sbGFyQnJhY2VMKTtcbiAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICArK3RoaXMucG9zO1xuICAgICAgICAgIHJldHVybiB0aGlzLmZpbmlzaFRva2VuKHR0LmJhY2tRdW90ZSk7XG4gICAgICAgIH1cbiAgICAgIH1cbiAgICAgIG91dCArPSB0aGlzLmlucHV0LnNsaWNlKGNodW5rU3RhcnQsIHRoaXMucG9zKTtcbiAgICAgIHJldHVybiB0aGlzLmZpbmlzaFRva2VuKHR0LnRlbXBsYXRlLCBvdXQpO1xuICAgIH1cbiAgICBpZiAoY2ggPT09IDkyKSB7XG4gICAgICAvLyAnXFwnXG4gICAgICBvdXQgKz0gdGhpcy5pbnB1dC5zbGljZShjaHVua1N0YXJ0LCB0aGlzLnBvcyk7XG4gICAgICBvdXQgKz0gdGhpcy5yZWFkRXNjYXBlZENoYXIoKTtcbiAgICAgIGNodW5rU3RhcnQgPSB0aGlzLnBvcztcbiAgICB9IGVsc2UgaWYgKGlzTmV3TGluZShjaCkpIHtcbiAgICAgIG91dCArPSB0aGlzLmlucHV0LnNsaWNlKGNodW5rU3RhcnQsIHRoaXMucG9zKTtcbiAgICAgICsrdGhpcy5wb3M7XG4gICAgICBpZiAoY2ggPT09IDEzICYmIHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcykgPT09IDEwKSB7XG4gICAgICAgICsrdGhpcy5wb3M7XG4gICAgICAgIG91dCArPSBcIlxcblwiO1xuICAgICAgfSBlbHNlIHtcbiAgICAgICAgb3V0ICs9IFN0cmluZy5mcm9tQ2hhckNvZGUoY2gpO1xuICAgICAgfVxuICAgICAgaWYgKHRoaXMub3B0aW9ucy5sb2NhdGlvbnMpIHtcbiAgICAgICAgKyt0aGlzLmN1ckxpbmU7XG4gICAgICAgIHRoaXMubGluZVN0YXJ0ID0gdGhpcy5wb3M7XG4gICAgICB9XG4gICAgICBjaHVua1N0YXJ0ID0gdGhpcy5wb3M7XG4gICAgfSBlbHNlIHtcbiAgICAgICsrdGhpcy5wb3M7XG4gICAgfVxuICB9XG59O1xuXG4vLyBVc2VkIHRvIHJlYWQgZXNjYXBlZCBjaGFyYWN0ZXJzXG5cbnBwLnJlYWRFc2NhcGVkQ2hhciA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIGNoID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KCsrdGhpcy5wb3MpO1xuICB2YXIgb2N0YWwgPSAvXlswLTddKy8uZXhlYyh0aGlzLmlucHV0LnNsaWNlKHRoaXMucG9zLCB0aGlzLnBvcyArIDMpKTtcbiAgaWYgKG9jdGFsKSBvY3RhbCA9IG9jdGFsWzBdO1xuICB3aGlsZSAob2N0YWwgJiYgcGFyc2VJbnQob2N0YWwsIDgpID4gMjU1KSBvY3RhbCA9IG9jdGFsLnNsaWNlKDAsIC0xKTtcbiAgaWYgKG9jdGFsID09PSBcIjBcIikgb2N0YWwgPSBudWxsO1xuICArK3RoaXMucG9zO1xuICBpZiAob2N0YWwpIHtcbiAgICBpZiAodGhpcy5zdHJpY3QpIHRoaXMucmFpc2UodGhpcy5wb3MgLSAyLCBcIk9jdGFsIGxpdGVyYWwgaW4gc3RyaWN0IG1vZGVcIik7XG4gICAgdGhpcy5wb3MgKz0gb2N0YWwubGVuZ3RoIC0gMTtcbiAgICByZXR1cm4gU3RyaW5nLmZyb21DaGFyQ29kZShwYXJzZUludChvY3RhbCwgOCkpO1xuICB9IGVsc2Uge1xuICAgIHN3aXRjaCAoY2gpIHtcbiAgICAgIGNhc2UgMTEwOlxuICAgICAgICByZXR1cm4gXCJcXG5cIjsgLy8gJ24nIC0+ICdcXG4nXG4gICAgICBjYXNlIDExNDpcbiAgICAgICAgcmV0dXJuIFwiXFxyXCI7IC8vICdyJyAtPiAnXFxyJ1xuICAgICAgY2FzZSAxMjA6XG4gICAgICAgIHJldHVybiBTdHJpbmcuZnJvbUNoYXJDb2RlKHRoaXMucmVhZEhleENoYXIoMikpOyAvLyAneCdcbiAgICAgIGNhc2UgMTE3OlxuICAgICAgICByZXR1cm4gY29kZVBvaW50VG9TdHJpbmcodGhpcy5yZWFkQ29kZVBvaW50KCkpOyAvLyAndSdcbiAgICAgIGNhc2UgMTE2OlxuICAgICAgICByZXR1cm4gXCJcXHRcIjsgLy8gJ3QnIC0+ICdcXHQnXG4gICAgICBjYXNlIDk4OlxuICAgICAgICByZXR1cm4gXCJcXGJcIjsgLy8gJ2InIC0+ICdcXGInXG4gICAgICBjYXNlIDExODpcbiAgICAgICAgcmV0dXJuIFwiXFx1MDAwYlwiOyAvLyAndicgLT4gJ1xcdTAwMGInXG4gICAgICBjYXNlIDEwMjpcbiAgICAgICAgcmV0dXJuIFwiXFxmXCI7IC8vICdmJyAtPiAnXFxmJ1xuICAgICAgY2FzZSA0ODpcbiAgICAgICAgcmV0dXJuIFwiXFx1MDAwMFwiOyAvLyAwIC0+ICdcXDAnXG4gICAgICBjYXNlIDEzOlxuICAgICAgICBpZiAodGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zKSA9PT0gMTApICsrdGhpcy5wb3M7IC8vICdcXHJcXG4nXG4gICAgICBjYXNlIDEwOlxuICAgICAgICAvLyAnIFxcbidcbiAgICAgICAgaWYgKHRoaXMub3B0aW9ucy5sb2NhdGlvbnMpIHtcbiAgICAgICAgICB0aGlzLmxpbmVTdGFydCA9IHRoaXMucG9zOysrdGhpcy5jdXJMaW5lO1xuICAgICAgICB9XG4gICAgICAgIHJldHVybiBcIlwiO1xuICAgICAgZGVmYXVsdDpcbiAgICAgICAgcmV0dXJuIFN0cmluZy5mcm9tQ2hhckNvZGUoY2gpO1xuICAgIH1cbiAgfVxufTtcblxuLy8gVXNlZCB0byByZWFkIGNoYXJhY3RlciBlc2NhcGUgc2VxdWVuY2VzICgnXFx4JywgJ1xcdScsICdcXFUnKS5cblxucHAucmVhZEhleENoYXIgPSBmdW5jdGlvbiAobGVuKSB7XG4gIHZhciBuID0gdGhpcy5yZWFkSW50KDE2LCBsZW4pO1xuICBpZiAobiA9PT0gbnVsbCkgdGhpcy5yYWlzZSh0aGlzLnN0YXJ0LCBcIkJhZCBjaGFyYWN0ZXIgZXNjYXBlIHNlcXVlbmNlXCIpO1xuICByZXR1cm4gbjtcbn07XG5cbi8vIFVzZWQgdG8gc2lnbmFsIHRvIGNhbGxlcnMgb2YgYHJlYWRXb3JkMWAgd2hldGhlciB0aGUgd29yZFxuLy8gY29udGFpbmVkIGFueSBlc2NhcGUgc2VxdWVuY2VzLiBUaGlzIGlzIG5lZWRlZCBiZWNhdXNlIHdvcmRzIHdpdGhcbi8vIGVzY2FwZSBzZXF1ZW5jZXMgbXVzdCBub3QgYmUgaW50ZXJwcmV0ZWQgYXMga2V5d29yZHMuXG5cbnZhciBjb250YWluc0VzYztcblxuLy8gUmVhZCBhbiBpZGVudGlmaWVyLCBhbmQgcmV0dXJuIGl0IGFzIGEgc3RyaW5nLiBTZXRzIGBjb250YWluc0VzY2Bcbi8vIHRvIHdoZXRoZXIgdGhlIHdvcmQgY29udGFpbmVkIGEgJ1xcdScgZXNjYXBlLlxuLy9cbi8vIEluY3JlbWVudGFsbHkgYWRkcyBvbmx5IGVzY2FwZWQgY2hhcnMsIGFkZGluZyBvdGhlciBjaHVua3MgYXMtaXNcbi8vIGFzIGEgbWljcm8tb3B0aW1pemF0aW9uLlxuXG5wcC5yZWFkV29yZDEgPSBmdW5jdGlvbiAoKSB7XG4gIGNvbnRhaW5zRXNjID0gZmFsc2U7XG4gIHZhciB3b3JkID0gXCJcIixcbiAgICAgIGZpcnN0ID0gdHJ1ZSxcbiAgICAgIGNodW5rU3RhcnQgPSB0aGlzLnBvcztcbiAgdmFyIGFzdHJhbCA9IHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2O1xuICB3aGlsZSAodGhpcy5wb3MgPCB0aGlzLmlucHV0Lmxlbmd0aCkge1xuICAgIHZhciBjaCA9IHRoaXMuZnVsbENoYXJDb2RlQXRQb3MoKTtcbiAgICBpZiAoaXNJZGVudGlmaWVyQ2hhcihjaCwgYXN0cmFsKSkge1xuICAgICAgdGhpcy5wb3MgKz0gY2ggPD0gNjU1MzUgPyAxIDogMjtcbiAgICB9IGVsc2UgaWYgKGNoID09PSA5Mikge1xuICAgICAgLy8gXCJcXFwiXG4gICAgICBjb250YWluc0VzYyA9IHRydWU7XG4gICAgICB3b3JkICs9IHRoaXMuaW5wdXQuc2xpY2UoY2h1bmtTdGFydCwgdGhpcy5wb3MpO1xuICAgICAgdmFyIGVzY1N0YXJ0ID0gdGhpcy5wb3M7XG4gICAgICBpZiAodGhpcy5pbnB1dC5jaGFyQ29kZUF0KCsrdGhpcy5wb3MpICE9IDExNykgLy8gXCJ1XCJcbiAgICAgICAgdGhpcy5yYWlzZSh0aGlzLnBvcywgXCJFeHBlY3RpbmcgVW5pY29kZSBlc2NhcGUgc2VxdWVuY2UgXFxcXHVYWFhYXCIpO1xuICAgICAgKyt0aGlzLnBvcztcbiAgICAgIHZhciBlc2MgPSB0aGlzLnJlYWRDb2RlUG9pbnQoKTtcbiAgICAgIGlmICghKGZpcnN0ID8gaXNJZGVudGlmaWVyU3RhcnQgOiBpc0lkZW50aWZpZXJDaGFyKShlc2MsIGFzdHJhbCkpIHRoaXMucmFpc2UoZXNjU3RhcnQsIFwiSW52YWxpZCBVbmljb2RlIGVzY2FwZVwiKTtcbiAgICAgIHdvcmQgKz0gY29kZVBvaW50VG9TdHJpbmcoZXNjKTtcbiAgICAgIGNodW5rU3RhcnQgPSB0aGlzLnBvcztcbiAgICB9IGVsc2Uge1xuICAgICAgYnJlYWs7XG4gICAgfVxuICAgIGZpcnN0ID0gZmFsc2U7XG4gIH1cbiAgcmV0dXJuIHdvcmQgKyB0aGlzLmlucHV0LnNsaWNlKGNodW5rU3RhcnQsIHRoaXMucG9zKTtcbn07XG5cbi8vIFJlYWQgYW4gaWRlbnRpZmllciBvciBrZXl3b3JkIHRva2VuLiBXaWxsIGNoZWNrIGZvciByZXNlcnZlZFxuLy8gd29yZHMgd2hlbiBuZWNlc3NhcnkuXG5cbnBwLnJlYWRXb3JkID0gZnVuY3Rpb24gKCkge1xuICB2YXIgd29yZCA9IHRoaXMucmVhZFdvcmQxKCk7XG4gIHZhciB0eXBlID0gdHQubmFtZTtcbiAgaWYgKCh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNiB8fCAhY29udGFpbnNFc2MpICYmIHRoaXMuaXNLZXl3b3JkKHdvcmQpKSB0eXBlID0ga2V5d29yZFR5cGVzW3dvcmRdO1xuICByZXR1cm4gdGhpcy5maW5pc2hUb2tlbih0eXBlLCB3b3JkKTtcbn07XG5cbn0se1wiLi9pZGVudGlmaWVyXCI6NyxcIi4vbG9jYXRpb25cIjo4LFwiLi9zdGF0ZVwiOjEzLFwiLi90b2tlbnR5cGVcIjoxNyxcIi4vd2hpdGVzcGFjZVwiOjE5fV0sMTc6W2Z1bmN0aW9uKF9kZXJlcV8sbW9kdWxlLGV4cG9ydHMpe1xuXCJ1c2Ugc3RyaWN0XCI7XG5cbnZhciBfY2xhc3NDYWxsQ2hlY2sgPSBmdW5jdGlvbiAoaW5zdGFuY2UsIENvbnN0cnVjdG9yKSB7IGlmICghKGluc3RhbmNlIGluc3RhbmNlb2YgQ29uc3RydWN0b3IpKSB7IHRocm93IG5ldyBUeXBlRXJyb3IoXCJDYW5ub3QgY2FsbCBhIGNsYXNzIGFzIGEgZnVuY3Rpb25cIik7IH0gfTtcblxuZXhwb3J0cy5fX2VzTW9kdWxlID0gdHJ1ZTtcbi8vICMjIFRva2VuIHR5cGVzXG5cbi8vIFRoZSBhc3NpZ25tZW50IG9mIGZpbmUtZ3JhaW5lZCwgaW5mb3JtYXRpb24tY2FycnlpbmcgdHlwZSBvYmplY3RzXG4vLyBhbGxvd3MgdGhlIHRva2VuaXplciB0byBzdG9yZSB0aGUgaW5mb3JtYXRpb24gaXQgaGFzIGFib3V0IGFcbi8vIHRva2VuIGluIGEgd2F5IHRoYXQgaXMgdmVyeSBjaGVhcCBmb3IgdGhlIHBhcnNlciB0byBsb29rIHVwLlxuXG4vLyBBbGwgdG9rZW4gdHlwZSB2YXJpYWJsZXMgc3RhcnQgd2l0aCBhbiB1bmRlcnNjb3JlLCB0byBtYWtlIHRoZW1cbi8vIGVhc3kgdG8gcmVjb2duaXplLlxuXG4vLyBUaGUgYGJlZm9yZUV4cHJgIHByb3BlcnR5IGlzIHVzZWQgdG8gZGlzYW1iaWd1YXRlIGJldHdlZW4gcmVndWxhclxuLy8gZXhwcmVzc2lvbnMgYW5kIGRpdmlzaW9ucy4gSXQgaXMgc2V0IG9uIGFsbCB0b2tlbiB0eXBlcyB0aGF0IGNhblxuLy8gYmUgZm9sbG93ZWQgYnkgYW4gZXhwcmVzc2lvbiAodGh1cywgYSBzbGFzaCBhZnRlciB0aGVtIHdvdWxkIGJlIGFcbi8vIHJlZ3VsYXIgZXhwcmVzc2lvbikuXG4vL1xuLy8gYGlzTG9vcGAgbWFya3MgYSBrZXl3b3JkIGFzIHN0YXJ0aW5nIGEgbG9vcCwgd2hpY2ggaXMgaW1wb3J0YW50XG4vLyB0byBrbm93IHdoZW4gcGFyc2luZyBhIGxhYmVsLCBpbiBvcmRlciB0byBhbGxvdyBvciBkaXNhbGxvd1xuLy8gY29udGludWUganVtcHMgdG8gdGhhdCBsYWJlbC5cblxudmFyIFRva2VuVHlwZSA9IGV4cG9ydHMuVG9rZW5UeXBlID0gZnVuY3Rpb24gVG9rZW5UeXBlKGxhYmVsKSB7XG4gIHZhciBjb25mID0gYXJndW1lbnRzWzFdID09PSB1bmRlZmluZWQgPyB7fSA6IGFyZ3VtZW50c1sxXTtcblxuICBfY2xhc3NDYWxsQ2hlY2sodGhpcywgVG9rZW5UeXBlKTtcblxuICB0aGlzLmxhYmVsID0gbGFiZWw7XG4gIHRoaXMua2V5d29yZCA9IGNvbmYua2V5d29yZDtcbiAgdGhpcy5iZWZvcmVFeHByID0gISFjb25mLmJlZm9yZUV4cHI7XG4gIHRoaXMuc3RhcnRzRXhwciA9ICEhY29uZi5zdGFydHNFeHByO1xuICB0aGlzLmlzTG9vcCA9ICEhY29uZi5pc0xvb3A7XG4gIHRoaXMuaXNBc3NpZ24gPSAhIWNvbmYuaXNBc3NpZ247XG4gIHRoaXMucHJlZml4ID0gISFjb25mLnByZWZpeDtcbiAgdGhpcy5wb3N0Zml4ID0gISFjb25mLnBvc3RmaXg7XG4gIHRoaXMuYmlub3AgPSBjb25mLmJpbm9wIHx8IG51bGw7XG4gIHRoaXMudXBkYXRlQ29udGV4dCA9IG51bGw7XG59O1xuXG5mdW5jdGlvbiBiaW5vcChuYW1lLCBwcmVjKSB7XG4gIHJldHVybiBuZXcgVG9rZW5UeXBlKG5hbWUsIHsgYmVmb3JlRXhwcjogdHJ1ZSwgYmlub3A6IHByZWMgfSk7XG59XG52YXIgYmVmb3JlRXhwciA9IHsgYmVmb3JlRXhwcjogdHJ1ZSB9LFxuICAgIHN0YXJ0c0V4cHIgPSB7IHN0YXJ0c0V4cHI6IHRydWUgfTtcblxudmFyIHR5cGVzID0ge1xuICBudW06IG5ldyBUb2tlblR5cGUoXCJudW1cIiwgc3RhcnRzRXhwciksXG4gIHJlZ2V4cDogbmV3IFRva2VuVHlwZShcInJlZ2V4cFwiLCBzdGFydHNFeHByKSxcbiAgc3RyaW5nOiBuZXcgVG9rZW5UeXBlKFwic3RyaW5nXCIsIHN0YXJ0c0V4cHIpLFxuICBuYW1lOiBuZXcgVG9rZW5UeXBlKFwibmFtZVwiLCBzdGFydHNFeHByKSxcbiAgZW9mOiBuZXcgVG9rZW5UeXBlKFwiZW9mXCIpLFxuXG4gIC8vIFB1bmN0dWF0aW9uIHRva2VuIHR5cGVzLlxuICBicmFja2V0TDogbmV3IFRva2VuVHlwZShcIltcIiwgeyBiZWZvcmVFeHByOiB0cnVlLCBzdGFydHNFeHByOiB0cnVlIH0pLFxuICBicmFja2V0UjogbmV3IFRva2VuVHlwZShcIl1cIiksXG4gIGJyYWNlTDogbmV3IFRva2VuVHlwZShcIntcIiwgeyBiZWZvcmVFeHByOiB0cnVlLCBzdGFydHNFeHByOiB0cnVlIH0pLFxuICBicmFjZVI6IG5ldyBUb2tlblR5cGUoXCJ9XCIpLFxuICBwYXJlbkw6IG5ldyBUb2tlblR5cGUoXCIoXCIsIHsgYmVmb3JlRXhwcjogdHJ1ZSwgc3RhcnRzRXhwcjogdHJ1ZSB9KSxcbiAgcGFyZW5SOiBuZXcgVG9rZW5UeXBlKFwiKVwiKSxcbiAgY29tbWE6IG5ldyBUb2tlblR5cGUoXCIsXCIsIGJlZm9yZUV4cHIpLFxuICBzZW1pOiBuZXcgVG9rZW5UeXBlKFwiO1wiLCBiZWZvcmVFeHByKSxcbiAgY29sb246IG5ldyBUb2tlblR5cGUoXCI6XCIsIGJlZm9yZUV4cHIpLFxuICBkb3Q6IG5ldyBUb2tlblR5cGUoXCIuXCIpLFxuICBxdWVzdGlvbjogbmV3IFRva2VuVHlwZShcIj9cIiwgYmVmb3JlRXhwciksXG4gIGFycm93OiBuZXcgVG9rZW5UeXBlKFwiPT5cIiwgYmVmb3JlRXhwciksXG4gIHRlbXBsYXRlOiBuZXcgVG9rZW5UeXBlKFwidGVtcGxhdGVcIiksXG4gIGVsbGlwc2lzOiBuZXcgVG9rZW5UeXBlKFwiLi4uXCIsIGJlZm9yZUV4cHIpLFxuICBiYWNrUXVvdGU6IG5ldyBUb2tlblR5cGUoXCJgXCIsIHN0YXJ0c0V4cHIpLFxuICBkb2xsYXJCcmFjZUw6IG5ldyBUb2tlblR5cGUoXCIke1wiLCB7IGJlZm9yZUV4cHI6IHRydWUsIHN0YXJ0c0V4cHI6IHRydWUgfSksXG5cbiAgLy8gT3BlcmF0b3JzLiBUaGVzZSBjYXJyeSBzZXZlcmFsIGtpbmRzIG9mIHByb3BlcnRpZXMgdG8gaGVscCB0aGVcbiAgLy8gcGFyc2VyIHVzZSB0aGVtIHByb3Blcmx5ICh0aGUgcHJlc2VuY2Ugb2YgdGhlc2UgcHJvcGVydGllcyBpc1xuICAvLyB3aGF0IGNhdGVnb3JpemVzIHRoZW0gYXMgb3BlcmF0b3JzKS5cbiAgLy9cbiAgLy8gYGJpbm9wYCwgd2hlbiBwcmVzZW50LCBzcGVjaWZpZXMgdGhhdCB0aGlzIG9wZXJhdG9yIGlzIGEgYmluYXJ5XG4gIC8vIG9wZXJhdG9yLCBhbmQgd2lsbCByZWZlciB0byBpdHMgcHJlY2VkZW5jZS5cbiAgLy9cbiAgLy8gYHByZWZpeGAgYW5kIGBwb3N0Zml4YCBtYXJrIHRoZSBvcGVyYXRvciBhcyBhIHByZWZpeCBvciBwb3N0Zml4XG4gIC8vIHVuYXJ5IG9wZXJhdG9yLlxuICAvL1xuICAvLyBgaXNBc3NpZ25gIG1hcmtzIGFsbCBvZiBgPWAsIGArPWAsIGAtPWAgZXRjZXRlcmEsIHdoaWNoIGFjdCBhc1xuICAvLyBiaW5hcnkgb3BlcmF0b3JzIHdpdGggYSB2ZXJ5IGxvdyBwcmVjZWRlbmNlLCB0aGF0IHNob3VsZCByZXN1bHRcbiAgLy8gaW4gQXNzaWdubWVudEV4cHJlc3Npb24gbm9kZXMuXG5cbiAgZXE6IG5ldyBUb2tlblR5cGUoXCI9XCIsIHsgYmVmb3JlRXhwcjogdHJ1ZSwgaXNBc3NpZ246IHRydWUgfSksXG4gIGFzc2lnbjogbmV3IFRva2VuVHlwZShcIl89XCIsIHsgYmVmb3JlRXhwcjogdHJ1ZSwgaXNBc3NpZ246IHRydWUgfSksXG4gIGluY0RlYzogbmV3IFRva2VuVHlwZShcIisrLy0tXCIsIHsgcHJlZml4OiB0cnVlLCBwb3N0Zml4OiB0cnVlLCBzdGFydHNFeHByOiB0cnVlIH0pLFxuICBwcmVmaXg6IG5ldyBUb2tlblR5cGUoXCJwcmVmaXhcIiwgeyBiZWZvcmVFeHByOiB0cnVlLCBwcmVmaXg6IHRydWUsIHN0YXJ0c0V4cHI6IHRydWUgfSksXG4gIGxvZ2ljYWxPUjogYmlub3AoXCJ8fFwiLCAxKSxcbiAgbG9naWNhbEFORDogYmlub3AoXCImJlwiLCAyKSxcbiAgYml0d2lzZU9SOiBiaW5vcChcInxcIiwgMyksXG4gIGJpdHdpc2VYT1I6IGJpbm9wKFwiXlwiLCA0KSxcbiAgYml0d2lzZUFORDogYmlub3AoXCImXCIsIDUpLFxuICBlcXVhbGl0eTogYmlub3AoXCI9PS8hPVwiLCA2KSxcbiAgcmVsYXRpb25hbDogYmlub3AoXCI8Lz5cIiwgNyksXG4gIGJpdFNoaWZ0OiBiaW5vcChcIjw8Lz4+XCIsIDgpLFxuICBwbHVzTWluOiBuZXcgVG9rZW5UeXBlKFwiKy8tXCIsIHsgYmVmb3JlRXhwcjogdHJ1ZSwgYmlub3A6IDksIHByZWZpeDogdHJ1ZSwgc3RhcnRzRXhwcjogdHJ1ZSB9KSxcbiAgbW9kdWxvOiBiaW5vcChcIiVcIiwgMTApLFxuICBzdGFyOiBiaW5vcChcIipcIiwgMTApLFxuICBzbGFzaDogYmlub3AoXCIvXCIsIDEwKVxufTtcblxuZXhwb3J0cy50eXBlcyA9IHR5cGVzO1xuLy8gTWFwIGtleXdvcmQgbmFtZXMgdG8gdG9rZW4gdHlwZXMuXG5cbnZhciBrZXl3b3JkcyA9IHt9O1xuXG5leHBvcnRzLmtleXdvcmRzID0ga2V5d29yZHM7XG4vLyBTdWNjaW5jdCBkZWZpbml0aW9ucyBvZiBrZXl3b3JkIHRva2VuIHR5cGVzXG5mdW5jdGlvbiBrdyhuYW1lKSB7XG4gIHZhciBvcHRpb25zID0gYXJndW1lbnRzWzFdID09PSB1bmRlZmluZWQgPyB7fSA6IGFyZ3VtZW50c1sxXTtcblxuICBvcHRpb25zLmtleXdvcmQgPSBuYW1lO1xuICBrZXl3b3Jkc1tuYW1lXSA9IHR5cGVzW1wiX1wiICsgbmFtZV0gPSBuZXcgVG9rZW5UeXBlKG5hbWUsIG9wdGlvbnMpO1xufVxuXG5rdyhcImJyZWFrXCIpO1xua3coXCJjYXNlXCIsIGJlZm9yZUV4cHIpO1xua3coXCJjYXRjaFwiKTtcbmt3KFwiY29udGludWVcIik7XG5rdyhcImRlYnVnZ2VyXCIpO1xua3coXCJkZWZhdWx0XCIpO1xua3coXCJkb1wiLCB7IGlzTG9vcDogdHJ1ZSB9KTtcbmt3KFwiZWxzZVwiLCBiZWZvcmVFeHByKTtcbmt3KFwiZmluYWxseVwiKTtcbmt3KFwiZm9yXCIsIHsgaXNMb29wOiB0cnVlIH0pO1xua3coXCJmdW5jdGlvblwiLCBzdGFydHNFeHByKTtcbmt3KFwiaWZcIik7XG5rdyhcInJldHVyblwiLCBiZWZvcmVFeHByKTtcbmt3KFwic3dpdGNoXCIpO1xua3coXCJ0aHJvd1wiLCBiZWZvcmVFeHByKTtcbmt3KFwidHJ5XCIpO1xua3coXCJ2YXJcIik7XG5rdyhcImxldFwiKTtcbmt3KFwiY29uc3RcIik7XG5rdyhcIndoaWxlXCIsIHsgaXNMb29wOiB0cnVlIH0pO1xua3coXCJ3aXRoXCIpO1xua3coXCJuZXdcIiwgeyBiZWZvcmVFeHByOiB0cnVlLCBzdGFydHNFeHByOiB0cnVlIH0pO1xua3coXCJ0aGlzXCIsIHN0YXJ0c0V4cHIpO1xua3coXCJzdXBlclwiLCBzdGFydHNFeHByKTtcbmt3KFwiY2xhc3NcIik7XG5rdyhcImV4dGVuZHNcIiwgYmVmb3JlRXhwcik7XG5rdyhcImV4cG9ydFwiKTtcbmt3KFwiaW1wb3J0XCIpO1xua3coXCJ5aWVsZFwiLCB7IGJlZm9yZUV4cHI6IHRydWUsIHN0YXJ0c0V4cHI6IHRydWUgfSk7XG5rdyhcIm51bGxcIiwgc3RhcnRzRXhwcik7XG5rdyhcInRydWVcIiwgc3RhcnRzRXhwcik7XG5rdyhcImZhbHNlXCIsIHN0YXJ0c0V4cHIpO1xua3coXCJpblwiLCB7IGJlZm9yZUV4cHI6IHRydWUsIGJpbm9wOiA3IH0pO1xua3coXCJpbnN0YW5jZW9mXCIsIHsgYmVmb3JlRXhwcjogdHJ1ZSwgYmlub3A6IDcgfSk7XG5rdyhcInR5cGVvZlwiLCB7IGJlZm9yZUV4cHI6IHRydWUsIHByZWZpeDogdHJ1ZSwgc3RhcnRzRXhwcjogdHJ1ZSB9KTtcbmt3KFwidm9pZFwiLCB7IGJlZm9yZUV4cHI6IHRydWUsIHByZWZpeDogdHJ1ZSwgc3RhcnRzRXhwcjogdHJ1ZSB9KTtcbmt3KFwiZGVsZXRlXCIsIHsgYmVmb3JlRXhwcjogdHJ1ZSwgcHJlZml4OiB0cnVlLCBzdGFydHNFeHByOiB0cnVlIH0pO1xuXG59LHt9XSwxODpbZnVuY3Rpb24oX2RlcmVxXyxtb2R1bGUsZXhwb3J0cyl7XG5cInVzZSBzdHJpY3RcIjtcblxuZXhwb3J0cy5pc0FycmF5ID0gaXNBcnJheTtcblxuLy8gQ2hlY2tzIGlmIGFuIG9iamVjdCBoYXMgYSBwcm9wZXJ0eS5cblxuZXhwb3J0cy5oYXMgPSBoYXM7XG5leHBvcnRzLl9fZXNNb2R1bGUgPSB0cnVlO1xuXG5mdW5jdGlvbiBpc0FycmF5KG9iaikge1xuICByZXR1cm4gT2JqZWN0LnByb3RvdHlwZS50b1N0cmluZy5jYWxsKG9iaikgPT09IFwiW29iamVjdCBBcnJheV1cIjtcbn1cblxuZnVuY3Rpb24gaGFzKG9iaiwgcHJvcE5hbWUpIHtcbiAgcmV0dXJuIE9iamVjdC5wcm90b3R5cGUuaGFzT3duUHJvcGVydHkuY2FsbChvYmosIHByb3BOYW1lKTtcbn1cblxufSx7fV0sMTk6W2Z1bmN0aW9uKF9kZXJlcV8sbW9kdWxlLGV4cG9ydHMpe1xuXCJ1c2Ugc3RyaWN0XCI7XG5cbmV4cG9ydHMuaXNOZXdMaW5lID0gaXNOZXdMaW5lO1xuZXhwb3J0cy5fX2VzTW9kdWxlID0gdHJ1ZTtcbi8vIE1hdGNoZXMgYSB3aG9sZSBsaW5lIGJyZWFrICh3aGVyZSBDUkxGIGlzIGNvbnNpZGVyZWQgYSBzaW5nbGVcbi8vIGxpbmUgYnJlYWspLiBVc2VkIHRvIGNvdW50IGxpbmVzLlxuXG52YXIgbGluZUJyZWFrID0gL1xcclxcbj98XFxufFxcdTIwMjh8XFx1MjAyOS87XG5leHBvcnRzLmxpbmVCcmVhayA9IGxpbmVCcmVhaztcbnZhciBsaW5lQnJlYWtHID0gbmV3IFJlZ0V4cChsaW5lQnJlYWsuc291cmNlLCBcImdcIik7XG5cbmV4cG9ydHMubGluZUJyZWFrRyA9IGxpbmVCcmVha0c7XG5cbmZ1bmN0aW9uIGlzTmV3TGluZShjb2RlKSB7XG4gIHJldHVybiBjb2RlID09PSAxMCB8fCBjb2RlID09PSAxMyB8fCBjb2RlID09PSA4MjMyIHx8IGNvZGUgPT0gODIzMztcbn1cblxudmFyIG5vbkFTQ0lJd2hpdGVzcGFjZSA9IC9bXFx1MTY4MFxcdTE4MGVcXHUyMDAwLVxcdTIwMGFcXHUyMDJmXFx1MjA1ZlxcdTMwMDBcXHVmZWZmXS87XG5leHBvcnRzLm5vbkFTQ0lJd2hpdGVzcGFjZSA9IG5vbkFTQ0lJd2hpdGVzcGFjZTtcblxufSx7fV19LHt9LFsxXSkoMSlcbn0pOyIsIihmdW5jdGlvbihmKXtpZih0eXBlb2YgZXhwb3J0cz09PVwib2JqZWN0XCImJnR5cGVvZiBtb2R1bGUhPT1cInVuZGVmaW5lZFwiKXttb2R1bGUuZXhwb3J0cz1mKCl9ZWxzZSBpZih0eXBlb2YgZGVmaW5lPT09XCJmdW5jdGlvblwiJiZkZWZpbmUuYW1kKXtkZWZpbmUoW10sZil9ZWxzZXt2YXIgZztpZih0eXBlb2Ygd2luZG93IT09XCJ1bmRlZmluZWRcIil7Zz13aW5kb3d9ZWxzZSBpZih0eXBlb2YgZ2xvYmFsIT09XCJ1bmRlZmluZWRcIil7Zz1nbG9iYWx9ZWxzZSBpZih0eXBlb2Ygc2VsZiE9PVwidW5kZWZpbmVkXCIpe2c9c2VsZn1lbHNle2c9dGhpc30oZy5hY29ybiB8fCAoZy5hY29ybiA9IHt9KSkubG9vc2UgPSBmKCl9fSkoZnVuY3Rpb24oKXt2YXIgZGVmaW5lLG1vZHVsZSxleHBvcnRzO3JldHVybiAoZnVuY3Rpb24gZSh0LG4scil7ZnVuY3Rpb24gcyhvLHUpe2lmKCFuW29dKXtpZighdFtvXSl7dmFyIGE9dHlwZW9mIHJlcXVpcmU9PVwiZnVuY3Rpb25cIiYmcmVxdWlyZTtpZighdSYmYSlyZXR1cm4gYShvLCEwKTtpZihpKXJldHVybiBpKG8sITApO3ZhciBmPW5ldyBFcnJvcihcIkNhbm5vdCBmaW5kIG1vZHVsZSAnXCIrbytcIidcIik7dGhyb3cgZi5jb2RlPVwiTU9EVUxFX05PVF9GT1VORFwiLGZ9dmFyIGw9bltvXT17ZXhwb3J0czp7fX07dFtvXVswXS5jYWxsKGwuZXhwb3J0cyxmdW5jdGlvbihlKXt2YXIgbj10W29dWzFdW2VdO3JldHVybiBzKG4/bjplKX0sbCxsLmV4cG9ydHMsZSx0LG4scil9cmV0dXJuIG5bb10uZXhwb3J0c312YXIgaT10eXBlb2YgcmVxdWlyZT09XCJmdW5jdGlvblwiJiZyZXF1aXJlO2Zvcih2YXIgbz0wO288ci5sZW5ndGg7bysrKXMocltvXSk7cmV0dXJuIHN9KSh7MTpbZnVuY3Rpb24oX2RlcmVxXyxtb2R1bGUsZXhwb3J0cyl7XG5cInVzZSBzdHJpY3RcIjtcblxudmFyIF9pbnRlcm9wUmVxdWlyZVdpbGRjYXJkID0gZnVuY3Rpb24gKG9iaikgeyByZXR1cm4gb2JqICYmIG9iai5fX2VzTW9kdWxlID8gb2JqIDogeyBcImRlZmF1bHRcIjogb2JqIH07IH07XG5cbmV4cG9ydHMucGFyc2VfZGFtbWl0ID0gcGFyc2VfZGFtbWl0O1xuZXhwb3J0cy5fX2VzTW9kdWxlID0gdHJ1ZTtcbi8vIEFjb3JuOiBMb29zZSBwYXJzZXJcbi8vXG4vLyBUaGlzIG1vZHVsZSBwcm92aWRlcyBhbiBhbHRlcm5hdGl2ZSBwYXJzZXIgKGBwYXJzZV9kYW1taXRgKSB0aGF0XG4vLyBleHBvc2VzIHRoYXQgc2FtZSBpbnRlcmZhY2UgYXMgYHBhcnNlYCwgYnV0IHdpbGwgdHJ5IHRvIHBhcnNlXG4vLyBhbnl0aGluZyBhcyBKYXZhU2NyaXB0LCByZXBhaXJpbmcgc3ludGF4IGVycm9yIHRoZSBiZXN0IGl0IGNhbi5cbi8vIFRoZXJlIGFyZSBjaXJjdW1zdGFuY2VzIGluIHdoaWNoIGl0IHdpbGwgcmFpc2UgYW4gZXJyb3IgYW5kIGdpdmVcbi8vIHVwLCBidXQgdGhleSBhcmUgdmVyeSByYXJlLiBUaGUgcmVzdWx0aW5nIEFTVCB3aWxsIGJlIGEgbW9zdGx5XG4vLyB2YWxpZCBKYXZhU2NyaXB0IEFTVCAoYXMgcGVyIHRoZSBbTW96aWxsYSBwYXJzZXIgQVBJXVthcGldLCBleGNlcHRcbi8vIHRoYXQ6XG4vL1xuLy8gLSBSZXR1cm4gb3V0c2lkZSBmdW5jdGlvbnMgaXMgYWxsb3dlZFxuLy9cbi8vIC0gTGFiZWwgY29uc2lzdGVuY3kgKG5vIGNvbmZsaWN0cywgYnJlYWsgb25seSB0byBleGlzdGluZyBsYWJlbHMpXG4vLyAgIGlzIG5vdCBlbmZvcmNlZC5cbi8vXG4vLyAtIEJvZ3VzIElkZW50aWZpZXIgbm9kZXMgd2l0aCBhIG5hbWUgb2YgYFwi4pyWXCJgIGFyZSBpbnNlcnRlZCB3aGVuZXZlclxuLy8gICB0aGUgcGFyc2VyIGdvdCB0b28gY29uZnVzZWQgdG8gcmV0dXJuIGFueXRoaW5nIG1lYW5pbmdmdWwuXG4vL1xuLy8gW2FwaV06IGh0dHBzOi8vZGV2ZWxvcGVyLm1vemlsbGEub3JnL2VuLVVTL2RvY3MvU3BpZGVyTW9ua2V5L1BhcnNlcl9BUElcbi8vXG4vLyBUaGUgZXhwZWN0ZWQgdXNlIGZvciB0aGlzIGlzIHRvICpmaXJzdCogdHJ5IGBhY29ybi5wYXJzZWAsIGFuZCBvbmx5XG4vLyBpZiB0aGF0IGZhaWxzIHN3aXRjaCB0byBgcGFyc2VfZGFtbWl0YC4gVGhlIGxvb3NlIHBhcnNlciBtaWdodFxuLy8gcGFyc2UgYmFkbHkgaW5kZW50ZWQgY29kZSBpbmNvcnJlY3RseSwgc28gKipkb24ndCoqIHVzZSBpdCBhc1xuLy8geW91ciBkZWZhdWx0IHBhcnNlci5cbi8vXG4vLyBRdWl0ZSBhIGxvdCBvZiBhY29ybi5qcyBpcyBkdXBsaWNhdGVkIGhlcmUuIFRoZSBhbHRlcm5hdGl2ZSB3YXMgdG9cbi8vIGFkZCBhICpsb3QqIG9mIGV4dHJhIGNydWZ0IHRvIHRoYXQgZmlsZSwgbWFraW5nIGl0IGxlc3MgcmVhZGFibGVcbi8vIGFuZCBzbG93ZXIuIENvcHlpbmcgYW5kIGVkaXRpbmcgdGhlIGNvZGUgYWxsb3dlZCBtZSB0byBtYWtlXG4vLyBpbnZhc2l2ZSBjaGFuZ2VzIGFuZCBzaW1wbGlmaWNhdGlvbnMgd2l0aG91dCBjcmVhdGluZyBhIGNvbXBsaWNhdGVkXG4vLyB0YW5nbGUuXG5cbnZhciBhY29ybiA9IF9pbnRlcm9wUmVxdWlyZVdpbGRjYXJkKF9kZXJlcV8oXCIuLlwiKSk7XG5cbnZhciBfc3RhdGUgPSBfZGVyZXFfKFwiLi9zdGF0ZVwiKTtcblxudmFyIExvb3NlUGFyc2VyID0gX3N0YXRlLkxvb3NlUGFyc2VyO1xuXG5fZGVyZXFfKFwiLi90b2tlbml6ZVwiKTtcblxuX2RlcmVxXyhcIi4vcGFyc2V1dGlsXCIpO1xuXG5fZGVyZXFfKFwiLi9zdGF0ZW1lbnRcIik7XG5cbl9kZXJlcV8oXCIuL2V4cHJlc3Npb25cIik7XG5cbmV4cG9ydHMuTG9vc2VQYXJzZXIgPSBfc3RhdGUuTG9vc2VQYXJzZXI7XG5cbmFjb3JuLmRlZmF1bHRPcHRpb25zLnRhYlNpemUgPSA0O1xuXG5mdW5jdGlvbiBwYXJzZV9kYW1taXQoaW5wdXQsIG9wdGlvbnMpIHtcbiAgdmFyIHAgPSBuZXcgTG9vc2VQYXJzZXIoaW5wdXQsIG9wdGlvbnMpO1xuICBwLm5leHQoKTtcbiAgcmV0dXJuIHAucGFyc2VUb3BMZXZlbCgpO1xufVxuXG5hY29ybi5wYXJzZV9kYW1taXQgPSBwYXJzZV9kYW1taXQ7XG5hY29ybi5Mb29zZVBhcnNlciA9IExvb3NlUGFyc2VyO1xuXG59LHtcIi4uXCI6MyxcIi4vZXhwcmVzc2lvblwiOjQsXCIuL3BhcnNldXRpbFwiOjUsXCIuL3N0YXRlXCI6NixcIi4vc3RhdGVtZW50XCI6NyxcIi4vdG9rZW5pemVcIjo4fV0sMjpbZnVuY3Rpb24oX2RlcmVxXyxtb2R1bGUsZXhwb3J0cyl7XG4oZnVuY3Rpb24gKGdsb2JhbCl7XG5cInVzZSBzdHJpY3RcIjsoZnVuY3Rpb24oZil7aWYodHlwZW9mIGV4cG9ydHMgPT09IFwib2JqZWN0XCIgJiYgdHlwZW9mIG1vZHVsZSAhPT0gXCJ1bmRlZmluZWRcIil7bW9kdWxlLmV4cG9ydHMgPSBmKCk7fWVsc2UgaWYodHlwZW9mIGRlZmluZSA9PT0gXCJmdW5jdGlvblwiICYmIGRlZmluZS5hbWQpe2RlZmluZShbXSwgZik7fWVsc2Uge3ZhciBnO2lmKHR5cGVvZiB3aW5kb3cgIT09IFwidW5kZWZpbmVkXCIpe2cgPSB3aW5kb3c7fWVsc2UgaWYodHlwZW9mIGdsb2JhbCAhPT0gXCJ1bmRlZmluZWRcIil7ZyA9IGdsb2JhbDt9ZWxzZSBpZih0eXBlb2Ygc2VsZiAhPT0gXCJ1bmRlZmluZWRcIil7ZyA9IHNlbGY7fWVsc2Uge2cgPSB0aGlzO31nLmFjb3JuID0gZigpO319KShmdW5jdGlvbigpe3ZhciBkZWZpbmUsIG1vZHVsZSwgZXhwb3J0cztyZXR1cm4gKGZ1bmN0aW9uIGUodCwgbiwgcil7ZnVuY3Rpb24gcyhvLCB1KXtpZighbltvXSl7aWYoIXRbb10pe3ZhciBhPXR5cGVvZiBfZGVyZXFfID09IFwiZnVuY3Rpb25cIiAmJiBfZGVyZXFfO2lmKCF1ICYmIGEpe3JldHVybiBhKG8sICEwKTt9aWYoaSl7cmV0dXJuIGkobywgITApO312YXIgZj1uZXcgRXJyb3IoXCJDYW5ub3QgZmluZCBtb2R1bGUgJ1wiICsgbyArIFwiJ1wiKTt0aHJvdyAoZi5jb2RlID0gXCJNT0RVTEVfTk9UX0ZPVU5EXCIsIGYpO312YXIgbD1uW29dID0ge2V4cG9ydHM6e319O3Rbb11bMF0uY2FsbChsLmV4cG9ydHMsIGZ1bmN0aW9uKGUpe3ZhciBuPXRbb11bMV1bZV07cmV0dXJuIHMobj9uOmUpO30sIGwsIGwuZXhwb3J0cywgZSwgdCwgbiwgcik7fXJldHVybiBuW29dLmV4cG9ydHM7fXZhciBpPXR5cGVvZiBfZGVyZXFfID09IFwiZnVuY3Rpb25cIiAmJiBfZGVyZXFfO2Zvcih2YXIgbz0wOyBvIDwgci5sZW5ndGg7IG8rKykgcyhyW29dKTtyZXR1cm4gczt9KSh7MTpbZnVuY3Rpb24oX2RlcmVxXywgbW9kdWxlLCBleHBvcnRzKXtcInVzZSBzdHJpY3RcIjtleHBvcnRzLnBhcnNlID0gcGFyc2U7ZXhwb3J0cy5wYXJzZUV4cHJlc3Npb25BdCA9IHBhcnNlRXhwcmVzc2lvbkF0O2V4cG9ydHMudG9rZW5pemVyID0gdG9rZW5pemVyO2V4cG9ydHMuX19lc01vZHVsZSA9IHRydWU7dmFyIF9zdGF0ZT1fZGVyZXFfKFwiLi9zdGF0ZVwiKTt2YXIgUGFyc2VyPV9zdGF0ZS5QYXJzZXI7dmFyIF9vcHRpb25zPV9kZXJlcV8oXCIuL29wdGlvbnNcIik7dmFyIGdldE9wdGlvbnM9X29wdGlvbnMuZ2V0T3B0aW9ucztfZGVyZXFfKFwiLi9wYXJzZXV0aWxcIik7X2RlcmVxXyhcIi4vc3RhdGVtZW50XCIpO19kZXJlcV8oXCIuL2x2YWxcIik7X2RlcmVxXyhcIi4vZXhwcmVzc2lvblwiKTtleHBvcnRzLlBhcnNlciA9IF9zdGF0ZS5QYXJzZXI7ZXhwb3J0cy5wbHVnaW5zID0gX3N0YXRlLnBsdWdpbnM7ZXhwb3J0cy5kZWZhdWx0T3B0aW9ucyA9IF9vcHRpb25zLmRlZmF1bHRPcHRpb25zO3ZhciBfbG9jYXRpb249X2RlcmVxXyhcIi4vbG9jYXRpb25cIik7ZXhwb3J0cy5Tb3VyY2VMb2NhdGlvbiA9IF9sb2NhdGlvbi5Tb3VyY2VMb2NhdGlvbjtleHBvcnRzLmdldExpbmVJbmZvID0gX2xvY2F0aW9uLmdldExpbmVJbmZvO2V4cG9ydHMuTm9kZSA9IF9kZXJlcV8oXCIuL25vZGVcIikuTm9kZTt2YXIgX3Rva2VudHlwZT1fZGVyZXFfKFwiLi90b2tlbnR5cGVcIik7ZXhwb3J0cy5Ub2tlblR5cGUgPSBfdG9rZW50eXBlLlRva2VuVHlwZTtleHBvcnRzLnRva1R5cGVzID0gX3Rva2VudHlwZS50eXBlczt2YXIgX3Rva2VuY29udGV4dD1fZGVyZXFfKFwiLi90b2tlbmNvbnRleHRcIik7ZXhwb3J0cy5Ub2tDb250ZXh0ID0gX3Rva2VuY29udGV4dC5Ub2tDb250ZXh0O2V4cG9ydHMudG9rQ29udGV4dHMgPSBfdG9rZW5jb250ZXh0LnR5cGVzO3ZhciBfaWRlbnRpZmllcj1fZGVyZXFfKFwiLi9pZGVudGlmaWVyXCIpO2V4cG9ydHMuaXNJZGVudGlmaWVyQ2hhciA9IF9pZGVudGlmaWVyLmlzSWRlbnRpZmllckNoYXI7ZXhwb3J0cy5pc0lkZW50aWZpZXJTdGFydCA9IF9pZGVudGlmaWVyLmlzSWRlbnRpZmllclN0YXJ0O2V4cG9ydHMuVG9rZW4gPSBfZGVyZXFfKFwiLi90b2tlbml6ZVwiKS5Ub2tlbjt2YXIgX3doaXRlc3BhY2U9X2RlcmVxXyhcIi4vd2hpdGVzcGFjZVwiKTtleHBvcnRzLmlzTmV3TGluZSA9IF93aGl0ZXNwYWNlLmlzTmV3TGluZTtleHBvcnRzLmxpbmVCcmVhayA9IF93aGl0ZXNwYWNlLmxpbmVCcmVhaztleHBvcnRzLmxpbmVCcmVha0cgPSBfd2hpdGVzcGFjZS5saW5lQnJlYWtHO3ZhciB2ZXJzaW9uPVwiMS4yLjJcIjtleHBvcnRzLnZlcnNpb24gPSB2ZXJzaW9uO2Z1bmN0aW9uIHBhcnNlKGlucHV0LCBvcHRpb25zKXt2YXIgcD1wYXJzZXIob3B0aW9ucywgaW5wdXQpO3ZhciBzdGFydFBvcz1wLnBvcywgc3RhcnRMb2M9cC5vcHRpb25zLmxvY2F0aW9ucyAmJiBwLmN1clBvc2l0aW9uKCk7cC5uZXh0VG9rZW4oKTtyZXR1cm4gcC5wYXJzZVRvcExldmVsKHAub3B0aW9ucy5wcm9ncmFtIHx8IHAuc3RhcnROb2RlQXQoc3RhcnRQb3MsIHN0YXJ0TG9jKSk7fWZ1bmN0aW9uIHBhcnNlRXhwcmVzc2lvbkF0KGlucHV0LCBwb3MsIG9wdGlvbnMpe3ZhciBwPXBhcnNlcihvcHRpb25zLCBpbnB1dCwgcG9zKTtwLm5leHRUb2tlbigpO3JldHVybiBwLnBhcnNlRXhwcmVzc2lvbigpO31mdW5jdGlvbiB0b2tlbml6ZXIoaW5wdXQsIG9wdGlvbnMpe3JldHVybiBwYXJzZXIob3B0aW9ucywgaW5wdXQpO31mdW5jdGlvbiBwYXJzZXIob3B0aW9ucywgaW5wdXQpe3JldHVybiBuZXcgUGFyc2VyKGdldE9wdGlvbnMob3B0aW9ucyksIFN0cmluZyhpbnB1dCkpO319LCB7XCIuL2V4cHJlc3Npb25cIjo2LCBcIi4vaWRlbnRpZmllclwiOjcsIFwiLi9sb2NhdGlvblwiOjgsIFwiLi9sdmFsXCI6OSwgXCIuL25vZGVcIjoxMCwgXCIuL29wdGlvbnNcIjoxMSwgXCIuL3BhcnNldXRpbFwiOjEyLCBcIi4vc3RhdGVcIjoxMywgXCIuL3N0YXRlbWVudFwiOjE0LCBcIi4vdG9rZW5jb250ZXh0XCI6MTUsIFwiLi90b2tlbml6ZVwiOjE2LCBcIi4vdG9rZW50eXBlXCI6MTcsIFwiLi93aGl0ZXNwYWNlXCI6MTl9XSwgMjpbZnVuY3Rpb24oX2RlcmVxXywgbW9kdWxlLCBleHBvcnRzKXtpZih0eXBlb2YgT2JqZWN0LmNyZWF0ZSA9PT0gXCJmdW5jdGlvblwiKXttb2R1bGUuZXhwb3J0cyA9IGZ1bmN0aW9uIGluaGVyaXRzKGN0b3IsIHN1cGVyQ3Rvcil7Y3Rvci5zdXBlcl8gPSBzdXBlckN0b3I7Y3Rvci5wcm90b3R5cGUgPSBPYmplY3QuY3JlYXRlKHN1cGVyQ3Rvci5wcm90b3R5cGUsIHtjb25zdHJ1Y3Rvcjp7dmFsdWU6Y3RvciwgZW51bWVyYWJsZTpmYWxzZSwgd3JpdGFibGU6dHJ1ZSwgY29uZmlndXJhYmxlOnRydWV9fSk7fTt9ZWxzZSB7bW9kdWxlLmV4cG9ydHMgPSBmdW5jdGlvbiBpbmhlcml0cyhjdG9yLCBzdXBlckN0b3Ipe2N0b3Iuc3VwZXJfID0gc3VwZXJDdG9yO3ZhciBUZW1wQ3Rvcj1mdW5jdGlvbiBUZW1wQ3Rvcigpe307VGVtcEN0b3IucHJvdG90eXBlID0gc3VwZXJDdG9yLnByb3RvdHlwZTtjdG9yLnByb3RvdHlwZSA9IG5ldyBUZW1wQ3RvcigpO2N0b3IucHJvdG90eXBlLmNvbnN0cnVjdG9yID0gY3Rvcjt9O319LCB7fV0sIDM6W2Z1bmN0aW9uKF9kZXJlcV8sIG1vZHVsZSwgZXhwb3J0cyl7dmFyIHByb2Nlc3M9bW9kdWxlLmV4cG9ydHMgPSB7fTt2YXIgcXVldWU9W107dmFyIGRyYWluaW5nPWZhbHNlO2Z1bmN0aW9uIGRyYWluUXVldWUoKXtpZihkcmFpbmluZyl7cmV0dXJuO31kcmFpbmluZyA9IHRydWU7dmFyIGN1cnJlbnRRdWV1ZTt2YXIgbGVuPXF1ZXVlLmxlbmd0aDt3aGlsZShsZW4pIHtjdXJyZW50UXVldWUgPSBxdWV1ZTtxdWV1ZSA9IFtdO3ZhciBpPS0xO3doaWxlKCsraSA8IGxlbikge2N1cnJlbnRRdWV1ZVtpXSgpO31sZW4gPSBxdWV1ZS5sZW5ndGg7fWRyYWluaW5nID0gZmFsc2U7fXByb2Nlc3MubmV4dFRpY2sgPSBmdW5jdGlvbihmdW4pe3F1ZXVlLnB1c2goZnVuKTtpZighZHJhaW5pbmcpe3NldFRpbWVvdXQoZHJhaW5RdWV1ZSwgMCk7fX07cHJvY2Vzcy50aXRsZSA9IFwiYnJvd3NlclwiO3Byb2Nlc3MuYnJvd3NlciA9IHRydWU7cHJvY2Vzcy5lbnYgPSB7fTtwcm9jZXNzLmFyZ3YgPSBbXTtwcm9jZXNzLnZlcnNpb24gPSBcIlwiO3Byb2Nlc3MudmVyc2lvbnMgPSB7fTtmdW5jdGlvbiBub29wKCl7fXByb2Nlc3Mub24gPSBub29wO3Byb2Nlc3MuYWRkTGlzdGVuZXIgPSBub29wO3Byb2Nlc3Mub25jZSA9IG5vb3A7cHJvY2Vzcy5vZmYgPSBub29wO3Byb2Nlc3MucmVtb3ZlTGlzdGVuZXIgPSBub29wO3Byb2Nlc3MucmVtb3ZlQWxsTGlzdGVuZXJzID0gbm9vcDtwcm9jZXNzLmVtaXQgPSBub29wO3Byb2Nlc3MuYmluZGluZyA9IGZ1bmN0aW9uKG5hbWUpe3Rocm93IG5ldyBFcnJvcihcInByb2Nlc3MuYmluZGluZyBpcyBub3Qgc3VwcG9ydGVkXCIpO307cHJvY2Vzcy5jd2QgPSBmdW5jdGlvbigpe3JldHVybiBcIi9cIjt9O3Byb2Nlc3MuY2hkaXIgPSBmdW5jdGlvbihkaXIpe3Rocm93IG5ldyBFcnJvcihcInByb2Nlc3MuY2hkaXIgaXMgbm90IHN1cHBvcnRlZFwiKTt9O3Byb2Nlc3MudW1hc2sgPSBmdW5jdGlvbigpe3JldHVybiAwO307fSwge31dLCA0OltmdW5jdGlvbihfZGVyZXFfLCBtb2R1bGUsIGV4cG9ydHMpe21vZHVsZS5leHBvcnRzID0gZnVuY3Rpb24gaXNCdWZmZXIoYXJnKXtyZXR1cm4gYXJnICYmIHR5cGVvZiBhcmcgPT09IFwib2JqZWN0XCIgJiYgdHlwZW9mIGFyZy5jb3B5ID09PSBcImZ1bmN0aW9uXCIgJiYgdHlwZW9mIGFyZy5maWxsID09PSBcImZ1bmN0aW9uXCIgJiYgdHlwZW9mIGFyZy5yZWFkVUludDggPT09IFwiZnVuY3Rpb25cIjt9O30sIHt9XSwgNTpbZnVuY3Rpb24oX2RlcmVxXywgbW9kdWxlLCBleHBvcnRzKXsoZnVuY3Rpb24ocHJvY2VzcywgZ2xvYmFsKXt2YXIgZm9ybWF0UmVnRXhwPS8lW3NkaiVdL2c7ZXhwb3J0cy5mb3JtYXQgPSBmdW5jdGlvbihmKXtpZighaXNTdHJpbmcoZikpe3ZhciBvYmplY3RzPVtdO2Zvcih2YXIgaT0wOyBpIDwgYXJndW1lbnRzLmxlbmd0aDsgaSsrKSB7b2JqZWN0cy5wdXNoKGluc3BlY3QoYXJndW1lbnRzW2ldKSk7fXJldHVybiBvYmplY3RzLmpvaW4oXCIgXCIpO312YXIgaT0xO3ZhciBhcmdzPWFyZ3VtZW50czt2YXIgbGVuPWFyZ3MubGVuZ3RoO3ZhciBzdHI9U3RyaW5nKGYpLnJlcGxhY2UoZm9ybWF0UmVnRXhwLCBmdW5jdGlvbih4KXtpZih4ID09PSBcIiUlXCIpcmV0dXJuIFwiJVwiO2lmKGkgPj0gbGVuKXJldHVybiB4O3N3aXRjaCh4KXtjYXNlIFwiJXNcIjpyZXR1cm4gU3RyaW5nKGFyZ3NbaSsrXSk7Y2FzZSBcIiVkXCI6cmV0dXJuIE51bWJlcihhcmdzW2krK10pO2Nhc2UgXCIlalwiOnRyeXtyZXR1cm4gSlNPTi5zdHJpbmdpZnkoYXJnc1tpKytdKTt9Y2F0Y2goXykge3JldHVybiBcIltDaXJjdWxhcl1cIjt9ZGVmYXVsdDpyZXR1cm4geDt9fSk7Zm9yKHZhciB4PWFyZ3NbaV07IGkgPCBsZW47IHggPSBhcmdzWysraV0pIHtpZihpc051bGwoeCkgfHwgIWlzT2JqZWN0KHgpKXtzdHIgKz0gXCIgXCIgKyB4O31lbHNlIHtzdHIgKz0gXCIgXCIgKyBpbnNwZWN0KHgpO319cmV0dXJuIHN0cjt9O2V4cG9ydHMuZGVwcmVjYXRlID0gZnVuY3Rpb24oZm4sIG1zZyl7aWYoaXNVbmRlZmluZWQoZ2xvYmFsLnByb2Nlc3MpKXtyZXR1cm4gZnVuY3Rpb24oKXtyZXR1cm4gZXhwb3J0cy5kZXByZWNhdGUoZm4sIG1zZykuYXBwbHkodGhpcywgYXJndW1lbnRzKTt9O31pZihwcm9jZXNzLm5vRGVwcmVjYXRpb24gPT09IHRydWUpe3JldHVybiBmbjt9dmFyIHdhcm5lZD1mYWxzZTtmdW5jdGlvbiBkZXByZWNhdGVkKCl7aWYoIXdhcm5lZCl7aWYocHJvY2Vzcy50aHJvd0RlcHJlY2F0aW9uKXt0aHJvdyBuZXcgRXJyb3IobXNnKTt9ZWxzZSBpZihwcm9jZXNzLnRyYWNlRGVwcmVjYXRpb24pe2NvbnNvbGUudHJhY2UobXNnKTt9ZWxzZSB7Y29uc29sZS5lcnJvcihtc2cpO313YXJuZWQgPSB0cnVlO31yZXR1cm4gZm4uYXBwbHkodGhpcywgYXJndW1lbnRzKTt9cmV0dXJuIGRlcHJlY2F0ZWQ7fTt2YXIgZGVidWdzPXt9O3ZhciBkZWJ1Z0Vudmlyb247ZXhwb3J0cy5kZWJ1Z2xvZyA9IGZ1bmN0aW9uKHNldCl7aWYoaXNVbmRlZmluZWQoZGVidWdFbnZpcm9uKSlkZWJ1Z0Vudmlyb24gPSBwcm9jZXNzLmVudi5OT0RFX0RFQlVHIHx8IFwiXCI7c2V0ID0gc2V0LnRvVXBwZXJDYXNlKCk7aWYoIWRlYnVnc1tzZXRdKXtpZihuZXcgUmVnRXhwKFwiXFxcXGJcIiArIHNldCArIFwiXFxcXGJcIiwgXCJpXCIpLnRlc3QoZGVidWdFbnZpcm9uKSl7dmFyIHBpZD1wcm9jZXNzLnBpZDtkZWJ1Z3Nbc2V0XSA9IGZ1bmN0aW9uKCl7dmFyIG1zZz1leHBvcnRzLmZvcm1hdC5hcHBseShleHBvcnRzLCBhcmd1bWVudHMpO2NvbnNvbGUuZXJyb3IoXCIlcyAlZDogJXNcIiwgc2V0LCBwaWQsIG1zZyk7fTt9ZWxzZSB7ZGVidWdzW3NldF0gPSBmdW5jdGlvbigpe307fX1yZXR1cm4gZGVidWdzW3NldF07fTtmdW5jdGlvbiBpbnNwZWN0KG9iaiwgb3B0cyl7dmFyIGN0eD17c2VlbjpbXSwgc3R5bGl6ZTpzdHlsaXplTm9Db2xvcn07aWYoYXJndW1lbnRzLmxlbmd0aCA+PSAzKWN0eC5kZXB0aCA9IGFyZ3VtZW50c1syXTtpZihhcmd1bWVudHMubGVuZ3RoID49IDQpY3R4LmNvbG9ycyA9IGFyZ3VtZW50c1szXTtpZihpc0Jvb2xlYW4ob3B0cykpe2N0eC5zaG93SGlkZGVuID0gb3B0czt9ZWxzZSBpZihvcHRzKXtleHBvcnRzLl9leHRlbmQoY3R4LCBvcHRzKTt9aWYoaXNVbmRlZmluZWQoY3R4LnNob3dIaWRkZW4pKWN0eC5zaG93SGlkZGVuID0gZmFsc2U7aWYoaXNVbmRlZmluZWQoY3R4LmRlcHRoKSljdHguZGVwdGggPSAyO2lmKGlzVW5kZWZpbmVkKGN0eC5jb2xvcnMpKWN0eC5jb2xvcnMgPSBmYWxzZTtpZihpc1VuZGVmaW5lZChjdHguY3VzdG9tSW5zcGVjdCkpY3R4LmN1c3RvbUluc3BlY3QgPSB0cnVlO2lmKGN0eC5jb2xvcnMpY3R4LnN0eWxpemUgPSBzdHlsaXplV2l0aENvbG9yO3JldHVybiBmb3JtYXRWYWx1ZShjdHgsIG9iaiwgY3R4LmRlcHRoKTt9ZXhwb3J0cy5pbnNwZWN0ID0gaW5zcGVjdDtpbnNwZWN0LmNvbG9ycyA9IHtib2xkOlsxLCAyMl0sIGl0YWxpYzpbMywgMjNdLCB1bmRlcmxpbmU6WzQsIDI0XSwgaW52ZXJzZTpbNywgMjddLCB3aGl0ZTpbMzcsIDM5XSwgZ3JleTpbOTAsIDM5XSwgYmxhY2s6WzMwLCAzOV0sIGJsdWU6WzM0LCAzOV0sIGN5YW46WzM2LCAzOV0sIGdyZWVuOlszMiwgMzldLCBtYWdlbnRhOlszNSwgMzldLCByZWQ6WzMxLCAzOV0sIHllbGxvdzpbMzMsIDM5XX07aW5zcGVjdC5zdHlsZXMgPSB7c3BlY2lhbDpcImN5YW5cIiwgbnVtYmVyOlwieWVsbG93XCIsIGJvb2xlYW46XCJ5ZWxsb3dcIiwgdW5kZWZpbmVkOlwiZ3JleVwiLCBcIm51bGxcIjpcImJvbGRcIiwgc3RyaW5nOlwiZ3JlZW5cIiwgZGF0ZTpcIm1hZ2VudGFcIiwgcmVnZXhwOlwicmVkXCJ9O2Z1bmN0aW9uIHN0eWxpemVXaXRoQ29sb3Ioc3RyLCBzdHlsZVR5cGUpe3ZhciBzdHlsZT1pbnNwZWN0LnN0eWxlc1tzdHlsZVR5cGVdO2lmKHN0eWxlKXtyZXR1cm4gXCJcXHUwMDFiW1wiICsgaW5zcGVjdC5jb2xvcnNbc3R5bGVdWzBdICsgXCJtXCIgKyBzdHIgKyBcIlxcdTAwMWJbXCIgKyBpbnNwZWN0LmNvbG9yc1tzdHlsZV1bMV0gKyBcIm1cIjt9ZWxzZSB7cmV0dXJuIHN0cjt9fWZ1bmN0aW9uIHN0eWxpemVOb0NvbG9yKHN0ciwgc3R5bGVUeXBlKXtyZXR1cm4gc3RyO31mdW5jdGlvbiBhcnJheVRvSGFzaChhcnJheSl7dmFyIGhhc2g9e307YXJyYXkuZm9yRWFjaChmdW5jdGlvbih2YWwsIGlkeCl7aGFzaFt2YWxdID0gdHJ1ZTt9KTtyZXR1cm4gaGFzaDt9ZnVuY3Rpb24gZm9ybWF0VmFsdWUoY3R4LCB2YWx1ZSwgcmVjdXJzZVRpbWVzKXtpZihjdHguY3VzdG9tSW5zcGVjdCAmJiB2YWx1ZSAmJiBpc0Z1bmN0aW9uKHZhbHVlLmluc3BlY3QpICYmIHZhbHVlLmluc3BlY3QgIT09IGV4cG9ydHMuaW5zcGVjdCAmJiAhKHZhbHVlLmNvbnN0cnVjdG9yICYmIHZhbHVlLmNvbnN0cnVjdG9yLnByb3RvdHlwZSA9PT0gdmFsdWUpKXt2YXIgcmV0PXZhbHVlLmluc3BlY3QocmVjdXJzZVRpbWVzLCBjdHgpO2lmKCFpc1N0cmluZyhyZXQpKXtyZXQgPSBmb3JtYXRWYWx1ZShjdHgsIHJldCwgcmVjdXJzZVRpbWVzKTt9cmV0dXJuIHJldDt9dmFyIHByaW1pdGl2ZT1mb3JtYXRQcmltaXRpdmUoY3R4LCB2YWx1ZSk7aWYocHJpbWl0aXZlKXtyZXR1cm4gcHJpbWl0aXZlO312YXIga2V5cz1PYmplY3Qua2V5cyh2YWx1ZSk7dmFyIHZpc2libGVLZXlzPWFycmF5VG9IYXNoKGtleXMpO2lmKGN0eC5zaG93SGlkZGVuKXtrZXlzID0gT2JqZWN0LmdldE93blByb3BlcnR5TmFtZXModmFsdWUpO31pZihpc0Vycm9yKHZhbHVlKSAmJiAoa2V5cy5pbmRleE9mKFwibWVzc2FnZVwiKSA+PSAwIHx8IGtleXMuaW5kZXhPZihcImRlc2NyaXB0aW9uXCIpID49IDApKXtyZXR1cm4gZm9ybWF0RXJyb3IodmFsdWUpO31pZihrZXlzLmxlbmd0aCA9PT0gMCl7aWYoaXNGdW5jdGlvbih2YWx1ZSkpe3ZhciBuYW1lPXZhbHVlLm5hbWU/XCI6IFwiICsgdmFsdWUubmFtZTpcIlwiO3JldHVybiBjdHguc3R5bGl6ZShcIltGdW5jdGlvblwiICsgbmFtZSArIFwiXVwiLCBcInNwZWNpYWxcIik7fWlmKGlzUmVnRXhwKHZhbHVlKSl7cmV0dXJuIGN0eC5zdHlsaXplKFJlZ0V4cC5wcm90b3R5cGUudG9TdHJpbmcuY2FsbCh2YWx1ZSksIFwicmVnZXhwXCIpO31pZihpc0RhdGUodmFsdWUpKXtyZXR1cm4gY3R4LnN0eWxpemUoRGF0ZS5wcm90b3R5cGUudG9TdHJpbmcuY2FsbCh2YWx1ZSksIFwiZGF0ZVwiKTt9aWYoaXNFcnJvcih2YWx1ZSkpe3JldHVybiBmb3JtYXRFcnJvcih2YWx1ZSk7fX12YXIgYmFzZT1cIlwiLCBhcnJheT1mYWxzZSwgYnJhY2VzPVtcIntcIiwgXCJ9XCJdO2lmKGlzQXJyYXkodmFsdWUpKXthcnJheSA9IHRydWU7YnJhY2VzID0gW1wiW1wiLCBcIl1cIl07fWlmKGlzRnVuY3Rpb24odmFsdWUpKXt2YXIgbj12YWx1ZS5uYW1lP1wiOiBcIiArIHZhbHVlLm5hbWU6XCJcIjtiYXNlID0gXCIgW0Z1bmN0aW9uXCIgKyBuICsgXCJdXCI7fWlmKGlzUmVnRXhwKHZhbHVlKSl7YmFzZSA9IFwiIFwiICsgUmVnRXhwLnByb3RvdHlwZS50b1N0cmluZy5jYWxsKHZhbHVlKTt9aWYoaXNEYXRlKHZhbHVlKSl7YmFzZSA9IFwiIFwiICsgRGF0ZS5wcm90b3R5cGUudG9VVENTdHJpbmcuY2FsbCh2YWx1ZSk7fWlmKGlzRXJyb3IodmFsdWUpKXtiYXNlID0gXCIgXCIgKyBmb3JtYXRFcnJvcih2YWx1ZSk7fWlmKGtleXMubGVuZ3RoID09PSAwICYmICghYXJyYXkgfHwgdmFsdWUubGVuZ3RoID09IDApKXtyZXR1cm4gYnJhY2VzWzBdICsgYmFzZSArIGJyYWNlc1sxXTt9aWYocmVjdXJzZVRpbWVzIDwgMCl7aWYoaXNSZWdFeHAodmFsdWUpKXtyZXR1cm4gY3R4LnN0eWxpemUoUmVnRXhwLnByb3RvdHlwZS50b1N0cmluZy5jYWxsKHZhbHVlKSwgXCJyZWdleHBcIik7fWVsc2Uge3JldHVybiBjdHguc3R5bGl6ZShcIltPYmplY3RdXCIsIFwic3BlY2lhbFwiKTt9fWN0eC5zZWVuLnB1c2godmFsdWUpO3ZhciBvdXRwdXQ7aWYoYXJyYXkpe291dHB1dCA9IGZvcm1hdEFycmF5KGN0eCwgdmFsdWUsIHJlY3Vyc2VUaW1lcywgdmlzaWJsZUtleXMsIGtleXMpO31lbHNlIHtvdXRwdXQgPSBrZXlzLm1hcChmdW5jdGlvbihrZXkpe3JldHVybiBmb3JtYXRQcm9wZXJ0eShjdHgsIHZhbHVlLCByZWN1cnNlVGltZXMsIHZpc2libGVLZXlzLCBrZXksIGFycmF5KTt9KTt9Y3R4LnNlZW4ucG9wKCk7cmV0dXJuIHJlZHVjZVRvU2luZ2xlU3RyaW5nKG91dHB1dCwgYmFzZSwgYnJhY2VzKTt9ZnVuY3Rpb24gZm9ybWF0UHJpbWl0aXZlKGN0eCwgdmFsdWUpe2lmKGlzVW5kZWZpbmVkKHZhbHVlKSl7cmV0dXJuIGN0eC5zdHlsaXplKFwidW5kZWZpbmVkXCIsIFwidW5kZWZpbmVkXCIpO31pZihpc1N0cmluZyh2YWx1ZSkpe3ZhciBzaW1wbGU9XCInXCIgKyBKU09OLnN0cmluZ2lmeSh2YWx1ZSkucmVwbGFjZSgvXlwifFwiJC9nLCBcIlwiKS5yZXBsYWNlKC8nL2csIFwiXFxcXCdcIikucmVwbGFjZSgvXFxcXFwiL2csIFwiXFxcIlwiKSArIFwiJ1wiO3JldHVybiBjdHguc3R5bGl6ZShzaW1wbGUsIFwic3RyaW5nXCIpO31pZihpc051bWJlcih2YWx1ZSkpe3JldHVybiBjdHguc3R5bGl6ZShcIlwiICsgdmFsdWUsIFwibnVtYmVyXCIpO31pZihpc0Jvb2xlYW4odmFsdWUpKXtyZXR1cm4gY3R4LnN0eWxpemUoXCJcIiArIHZhbHVlLCBcImJvb2xlYW5cIik7fWlmKGlzTnVsbCh2YWx1ZSkpe3JldHVybiBjdHguc3R5bGl6ZShcIm51bGxcIiwgXCJudWxsXCIpO319ZnVuY3Rpb24gZm9ybWF0RXJyb3IodmFsdWUpe3JldHVybiBcIltcIiArIEVycm9yLnByb3RvdHlwZS50b1N0cmluZy5jYWxsKHZhbHVlKSArIFwiXVwiO31mdW5jdGlvbiBmb3JtYXRBcnJheShjdHgsIHZhbHVlLCByZWN1cnNlVGltZXMsIHZpc2libGVLZXlzLCBrZXlzKXt2YXIgb3V0cHV0PVtdO2Zvcih2YXIgaT0wLCBsPXZhbHVlLmxlbmd0aDsgaSA8IGw7ICsraSkge2lmKGhhc093blByb3BlcnR5KHZhbHVlLCBTdHJpbmcoaSkpKXtvdXRwdXQucHVzaChmb3JtYXRQcm9wZXJ0eShjdHgsIHZhbHVlLCByZWN1cnNlVGltZXMsIHZpc2libGVLZXlzLCBTdHJpbmcoaSksIHRydWUpKTt9ZWxzZSB7b3V0cHV0LnB1c2goXCJcIik7fX1rZXlzLmZvckVhY2goZnVuY3Rpb24oa2V5KXtpZigha2V5Lm1hdGNoKC9eXFxkKyQvKSl7b3V0cHV0LnB1c2goZm9ybWF0UHJvcGVydHkoY3R4LCB2YWx1ZSwgcmVjdXJzZVRpbWVzLCB2aXNpYmxlS2V5cywga2V5LCB0cnVlKSk7fX0pO3JldHVybiBvdXRwdXQ7fWZ1bmN0aW9uIGZvcm1hdFByb3BlcnR5KGN0eCwgdmFsdWUsIHJlY3Vyc2VUaW1lcywgdmlzaWJsZUtleXMsIGtleSwgYXJyYXkpe3ZhciBuYW1lLCBzdHIsIGRlc2M7ZGVzYyA9IE9iamVjdC5nZXRPd25Qcm9wZXJ0eURlc2NyaXB0b3IodmFsdWUsIGtleSkgfHwge3ZhbHVlOnZhbHVlW2tleV19O2lmKGRlc2MuZ2V0KXtpZihkZXNjLnNldCl7c3RyID0gY3R4LnN0eWxpemUoXCJbR2V0dGVyL1NldHRlcl1cIiwgXCJzcGVjaWFsXCIpO31lbHNlIHtzdHIgPSBjdHguc3R5bGl6ZShcIltHZXR0ZXJdXCIsIFwic3BlY2lhbFwiKTt9fWVsc2Uge2lmKGRlc2Muc2V0KXtzdHIgPSBjdHguc3R5bGl6ZShcIltTZXR0ZXJdXCIsIFwic3BlY2lhbFwiKTt9fWlmKCFoYXNPd25Qcm9wZXJ0eSh2aXNpYmxlS2V5cywga2V5KSl7bmFtZSA9IFwiW1wiICsga2V5ICsgXCJdXCI7fWlmKCFzdHIpe2lmKGN0eC5zZWVuLmluZGV4T2YoZGVzYy52YWx1ZSkgPCAwKXtpZihpc051bGwocmVjdXJzZVRpbWVzKSl7c3RyID0gZm9ybWF0VmFsdWUoY3R4LCBkZXNjLnZhbHVlLCBudWxsKTt9ZWxzZSB7c3RyID0gZm9ybWF0VmFsdWUoY3R4LCBkZXNjLnZhbHVlLCByZWN1cnNlVGltZXMgLSAxKTt9aWYoc3RyLmluZGV4T2YoXCJcXG5cIikgPiAtMSl7aWYoYXJyYXkpe3N0ciA9IHN0ci5zcGxpdChcIlxcblwiKS5tYXAoZnVuY3Rpb24obGluZSl7cmV0dXJuIFwiICBcIiArIGxpbmU7fSkuam9pbihcIlxcblwiKS5zdWJzdHIoMik7fWVsc2Uge3N0ciA9IFwiXFxuXCIgKyBzdHIuc3BsaXQoXCJcXG5cIikubWFwKGZ1bmN0aW9uKGxpbmUpe3JldHVybiBcIiAgIFwiICsgbGluZTt9KS5qb2luKFwiXFxuXCIpO319fWVsc2Uge3N0ciA9IGN0eC5zdHlsaXplKFwiW0NpcmN1bGFyXVwiLCBcInNwZWNpYWxcIik7fX1pZihpc1VuZGVmaW5lZChuYW1lKSl7aWYoYXJyYXkgJiYga2V5Lm1hdGNoKC9eXFxkKyQvKSl7cmV0dXJuIHN0cjt9bmFtZSA9IEpTT04uc3RyaW5naWZ5KFwiXCIgKyBrZXkpO2lmKG5hbWUubWF0Y2goL15cIihbYS16QS1aX11bYS16QS1aXzAtOV0qKVwiJC8pKXtuYW1lID0gbmFtZS5zdWJzdHIoMSwgbmFtZS5sZW5ndGggLSAyKTtuYW1lID0gY3R4LnN0eWxpemUobmFtZSwgXCJuYW1lXCIpO31lbHNlIHtuYW1lID0gbmFtZS5yZXBsYWNlKC8nL2csIFwiXFxcXCdcIikucmVwbGFjZSgvXFxcXFwiL2csIFwiXFxcIlwiKS5yZXBsYWNlKC8oXlwifFwiJCkvZywgXCInXCIpO25hbWUgPSBjdHguc3R5bGl6ZShuYW1lLCBcInN0cmluZ1wiKTt9fXJldHVybiBuYW1lICsgXCI6IFwiICsgc3RyO31mdW5jdGlvbiByZWR1Y2VUb1NpbmdsZVN0cmluZyhvdXRwdXQsIGJhc2UsIGJyYWNlcyl7dmFyIG51bUxpbmVzRXN0PTA7dmFyIGxlbmd0aD1vdXRwdXQucmVkdWNlKGZ1bmN0aW9uKHByZXYsIGN1cil7bnVtTGluZXNFc3QrKztpZihjdXIuaW5kZXhPZihcIlxcblwiKSA+PSAwKW51bUxpbmVzRXN0Kys7cmV0dXJuIHByZXYgKyBjdXIucmVwbGFjZSgvXFx1MDAxYlxcW1xcZFxcZD9tL2csIFwiXCIpLmxlbmd0aCArIDE7fSwgMCk7aWYobGVuZ3RoID4gNjApe3JldHVybiBicmFjZXNbMF0gKyAoYmFzZSA9PT0gXCJcIj9cIlwiOmJhc2UgKyBcIlxcbiBcIikgKyBcIiBcIiArIG91dHB1dC5qb2luKFwiLFxcbiAgXCIpICsgXCIgXCIgKyBicmFjZXNbMV07fXJldHVybiBicmFjZXNbMF0gKyBiYXNlICsgXCIgXCIgKyBvdXRwdXQuam9pbihcIiwgXCIpICsgXCIgXCIgKyBicmFjZXNbMV07fWZ1bmN0aW9uIGlzQXJyYXkoYXIpe3JldHVybiBBcnJheS5pc0FycmF5KGFyKTt9ZXhwb3J0cy5pc0FycmF5ID0gaXNBcnJheTtmdW5jdGlvbiBpc0Jvb2xlYW4oYXJnKXtyZXR1cm4gdHlwZW9mIGFyZyA9PT0gXCJib29sZWFuXCI7fWV4cG9ydHMuaXNCb29sZWFuID0gaXNCb29sZWFuO2Z1bmN0aW9uIGlzTnVsbChhcmcpe3JldHVybiBhcmcgPT09IG51bGw7fWV4cG9ydHMuaXNOdWxsID0gaXNOdWxsO2Z1bmN0aW9uIGlzTnVsbE9yVW5kZWZpbmVkKGFyZyl7cmV0dXJuIGFyZyA9PSBudWxsO31leHBvcnRzLmlzTnVsbE9yVW5kZWZpbmVkID0gaXNOdWxsT3JVbmRlZmluZWQ7ZnVuY3Rpb24gaXNOdW1iZXIoYXJnKXtyZXR1cm4gdHlwZW9mIGFyZyA9PT0gXCJudW1iZXJcIjt9ZXhwb3J0cy5pc051bWJlciA9IGlzTnVtYmVyO2Z1bmN0aW9uIGlzU3RyaW5nKGFyZyl7cmV0dXJuIHR5cGVvZiBhcmcgPT09IFwic3RyaW5nXCI7fWV4cG9ydHMuaXNTdHJpbmcgPSBpc1N0cmluZztmdW5jdGlvbiBpc1N5bWJvbChhcmcpe3JldHVybiB0eXBlb2YgYXJnID09PSBcInN5bWJvbFwiO31leHBvcnRzLmlzU3ltYm9sID0gaXNTeW1ib2w7ZnVuY3Rpb24gaXNVbmRlZmluZWQoYXJnKXtyZXR1cm4gYXJnID09PSB2b2lkIDA7fWV4cG9ydHMuaXNVbmRlZmluZWQgPSBpc1VuZGVmaW5lZDtmdW5jdGlvbiBpc1JlZ0V4cChyZSl7cmV0dXJuIGlzT2JqZWN0KHJlKSAmJiBvYmplY3RUb1N0cmluZyhyZSkgPT09IFwiW29iamVjdCBSZWdFeHBdXCI7fWV4cG9ydHMuaXNSZWdFeHAgPSBpc1JlZ0V4cDtmdW5jdGlvbiBpc09iamVjdChhcmcpe3JldHVybiB0eXBlb2YgYXJnID09PSBcIm9iamVjdFwiICYmIGFyZyAhPT0gbnVsbDt9ZXhwb3J0cy5pc09iamVjdCA9IGlzT2JqZWN0O2Z1bmN0aW9uIGlzRGF0ZShkKXtyZXR1cm4gaXNPYmplY3QoZCkgJiYgb2JqZWN0VG9TdHJpbmcoZCkgPT09IFwiW29iamVjdCBEYXRlXVwiO31leHBvcnRzLmlzRGF0ZSA9IGlzRGF0ZTtmdW5jdGlvbiBpc0Vycm9yKGUpe3JldHVybiBpc09iamVjdChlKSAmJiAob2JqZWN0VG9TdHJpbmcoZSkgPT09IFwiW29iamVjdCBFcnJvcl1cIiB8fCBlIGluc3RhbmNlb2YgRXJyb3IpO31leHBvcnRzLmlzRXJyb3IgPSBpc0Vycm9yO2Z1bmN0aW9uIGlzRnVuY3Rpb24oYXJnKXtyZXR1cm4gdHlwZW9mIGFyZyA9PT0gXCJmdW5jdGlvblwiO31leHBvcnRzLmlzRnVuY3Rpb24gPSBpc0Z1bmN0aW9uO2Z1bmN0aW9uIGlzUHJpbWl0aXZlKGFyZyl7cmV0dXJuIGFyZyA9PT0gbnVsbCB8fCB0eXBlb2YgYXJnID09PSBcImJvb2xlYW5cIiB8fCB0eXBlb2YgYXJnID09PSBcIm51bWJlclwiIHx8IHR5cGVvZiBhcmcgPT09IFwic3RyaW5nXCIgfHwgdHlwZW9mIGFyZyA9PT0gXCJzeW1ib2xcIiB8fCB0eXBlb2YgYXJnID09PSBcInVuZGVmaW5lZFwiO31leHBvcnRzLmlzUHJpbWl0aXZlID0gaXNQcmltaXRpdmU7ZXhwb3J0cy5pc0J1ZmZlciA9IF9kZXJlcV8oXCIuL3N1cHBvcnQvaXNCdWZmZXJcIik7ZnVuY3Rpb24gb2JqZWN0VG9TdHJpbmcobyl7cmV0dXJuIE9iamVjdC5wcm90b3R5cGUudG9TdHJpbmcuY2FsbChvKTt9ZnVuY3Rpb24gcGFkKG4pe3JldHVybiBuIDwgMTA/XCIwXCIgKyBuLnRvU3RyaW5nKDEwKTpuLnRvU3RyaW5nKDEwKTt9dmFyIG1vbnRocz1bXCJKYW5cIiwgXCJGZWJcIiwgXCJNYXJcIiwgXCJBcHJcIiwgXCJNYXlcIiwgXCJKdW5cIiwgXCJKdWxcIiwgXCJBdWdcIiwgXCJTZXBcIiwgXCJPY3RcIiwgXCJOb3ZcIiwgXCJEZWNcIl07ZnVuY3Rpb24gdGltZXN0YW1wKCl7dmFyIGQ9bmV3IERhdGUoKTt2YXIgdGltZT1bcGFkKGQuZ2V0SG91cnMoKSksIHBhZChkLmdldE1pbnV0ZXMoKSksIHBhZChkLmdldFNlY29uZHMoKSldLmpvaW4oXCI6XCIpO3JldHVybiBbZC5nZXREYXRlKCksIG1vbnRoc1tkLmdldE1vbnRoKCldLCB0aW1lXS5qb2luKFwiIFwiKTt9ZXhwb3J0cy5sb2cgPSBmdW5jdGlvbigpe2NvbnNvbGUubG9nKFwiJXMgLSAlc1wiLCB0aW1lc3RhbXAoKSwgZXhwb3J0cy5mb3JtYXQuYXBwbHkoZXhwb3J0cywgYXJndW1lbnRzKSk7fTtleHBvcnRzLmluaGVyaXRzID0gX2RlcmVxXyhcImluaGVyaXRzXCIpO2V4cG9ydHMuX2V4dGVuZCA9IGZ1bmN0aW9uKG9yaWdpbiwgYWRkKXtpZighYWRkIHx8ICFpc09iamVjdChhZGQpKXJldHVybiBvcmlnaW47dmFyIGtleXM9T2JqZWN0LmtleXMoYWRkKTt2YXIgaT1rZXlzLmxlbmd0aDt3aGlsZShpLS0pIHtvcmlnaW5ba2V5c1tpXV0gPSBhZGRba2V5c1tpXV07fXJldHVybiBvcmlnaW47fTtmdW5jdGlvbiBoYXNPd25Qcm9wZXJ0eShvYmosIHByb3Ape3JldHVybiBPYmplY3QucHJvdG90eXBlLmhhc093blByb3BlcnR5LmNhbGwob2JqLCBwcm9wKTt9fSkuY2FsbCh0aGlzLCBfZGVyZXFfKFwiX3Byb2Nlc3NcIiksIHR5cGVvZiBnbG9iYWwgIT09IFwidW5kZWZpbmVkXCI/Z2xvYmFsOnR5cGVvZiBzZWxmICE9PSBcInVuZGVmaW5lZFwiP3NlbGY6dHlwZW9mIHdpbmRvdyAhPT0gXCJ1bmRlZmluZWRcIj93aW5kb3c6e30pO30sIHtcIi4vc3VwcG9ydC9pc0J1ZmZlclwiOjQsIF9wcm9jZXNzOjMsIGluaGVyaXRzOjJ9XSwgNjpbZnVuY3Rpb24oX2RlcmVxXywgbW9kdWxlLCBleHBvcnRzKXtcInVzZSBzdHJpY3RcIjt2YXIgdHQ9X2RlcmVxXyhcIi4vdG9rZW50eXBlXCIpLnR5cGVzO3ZhciBQYXJzZXI9X2RlcmVxXyhcIi4vc3RhdGVcIikuUGFyc2VyO3ZhciByZXNlcnZlZFdvcmRzPV9kZXJlcV8oXCIuL2lkZW50aWZpZXJcIikucmVzZXJ2ZWRXb3Jkczt2YXIgaGFzPV9kZXJlcV8oXCIuL3V0aWxcIikuaGFzO3ZhciBwcD1QYXJzZXIucHJvdG90eXBlO3BwLmNoZWNrUHJvcENsYXNoID0gZnVuY3Rpb24ocHJvcCwgcHJvcEhhc2gpe2lmKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KXJldHVybjt2YXIga2V5PXByb3Aua2V5LCBuYW1lPXVuZGVmaW5lZDtzd2l0Y2goa2V5LnR5cGUpe2Nhc2UgXCJJZGVudGlmaWVyXCI6bmFtZSA9IGtleS5uYW1lO2JyZWFrO2Nhc2UgXCJMaXRlcmFsXCI6bmFtZSA9IFN0cmluZyhrZXkudmFsdWUpO2JyZWFrO2RlZmF1bHQ6cmV0dXJuO312YXIga2luZD1wcm9wLmtpbmQgfHwgXCJpbml0XCIsIG90aGVyPXVuZGVmaW5lZDtpZihoYXMocHJvcEhhc2gsIG5hbWUpKXtvdGhlciA9IHByb3BIYXNoW25hbWVdO3ZhciBpc0dldFNldD1raW5kICE9PSBcImluaXRcIjtpZigodGhpcy5zdHJpY3QgfHwgaXNHZXRTZXQpICYmIG90aGVyW2tpbmRdIHx8ICEoaXNHZXRTZXQgXiBvdGhlci5pbml0KSl0aGlzLnJhaXNlKGtleS5zdGFydCwgXCJSZWRlZmluaXRpb24gb2YgcHJvcGVydHlcIik7fWVsc2Uge290aGVyID0gcHJvcEhhc2hbbmFtZV0gPSB7aW5pdDpmYWxzZSwgZ2V0OmZhbHNlLCBzZXQ6ZmFsc2V9O31vdGhlcltraW5kXSA9IHRydWU7fTtwcC5wYXJzZUV4cHJlc3Npb24gPSBmdW5jdGlvbihub0luLCByZWZTaG9ydGhhbmREZWZhdWx0UG9zKXt2YXIgc3RhcnRQb3M9dGhpcy5zdGFydCwgc3RhcnRMb2M9dGhpcy5zdGFydExvYzt2YXIgZXhwcj10aGlzLnBhcnNlTWF5YmVBc3NpZ24obm9JbiwgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcyk7aWYodGhpcy50eXBlID09PSB0dC5jb21tYSl7dmFyIG5vZGU9dGhpcy5zdGFydE5vZGVBdChzdGFydFBvcywgc3RhcnRMb2MpO25vZGUuZXhwcmVzc2lvbnMgPSBbZXhwcl07d2hpbGUodGhpcy5lYXQodHQuY29tbWEpKSBub2RlLmV4cHJlc3Npb25zLnB1c2godGhpcy5wYXJzZU1heWJlQXNzaWduKG5vSW4sIHJlZlNob3J0aGFuZERlZmF1bHRQb3MpKTtyZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiU2VxdWVuY2VFeHByZXNzaW9uXCIpO31yZXR1cm4gZXhwcjt9O3BwLnBhcnNlTWF5YmVBc3NpZ24gPSBmdW5jdGlvbihub0luLCByZWZTaG9ydGhhbmREZWZhdWx0UG9zLCBhZnRlckxlZnRQYXJzZSl7aWYodGhpcy50eXBlID09IHR0Ll95aWVsZCAmJiB0aGlzLmluR2VuZXJhdG9yKXJldHVybiB0aGlzLnBhcnNlWWllbGQoKTt2YXIgZmFpbE9uU2hvcnRoYW5kQXNzaWduPXVuZGVmaW5lZDtpZighcmVmU2hvcnRoYW5kRGVmYXVsdFBvcyl7cmVmU2hvcnRoYW5kRGVmYXVsdFBvcyA9IHtzdGFydDowfTtmYWlsT25TaG9ydGhhbmRBc3NpZ24gPSB0cnVlO31lbHNlIHtmYWlsT25TaG9ydGhhbmRBc3NpZ24gPSBmYWxzZTt9dmFyIHN0YXJ0UG9zPXRoaXMuc3RhcnQsIHN0YXJ0TG9jPXRoaXMuc3RhcnRMb2M7aWYodGhpcy50eXBlID09IHR0LnBhcmVuTCB8fCB0aGlzLnR5cGUgPT0gdHQubmFtZSl0aGlzLnBvdGVudGlhbEFycm93QXQgPSB0aGlzLnN0YXJ0O3ZhciBsZWZ0PXRoaXMucGFyc2VNYXliZUNvbmRpdGlvbmFsKG5vSW4sIHJlZlNob3J0aGFuZERlZmF1bHRQb3MpO2lmKGFmdGVyTGVmdFBhcnNlKWxlZnQgPSBhZnRlckxlZnRQYXJzZS5jYWxsKHRoaXMsIGxlZnQsIHN0YXJ0UG9zLCBzdGFydExvYyk7aWYodGhpcy50eXBlLmlzQXNzaWduKXt2YXIgbm9kZT10aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0UG9zLCBzdGFydExvYyk7bm9kZS5vcGVyYXRvciA9IHRoaXMudmFsdWU7bm9kZS5sZWZ0ID0gdGhpcy50eXBlID09PSB0dC5lcT90aGlzLnRvQXNzaWduYWJsZShsZWZ0KTpsZWZ0O3JlZlNob3J0aGFuZERlZmF1bHRQb3Muc3RhcnQgPSAwO3RoaXMuY2hlY2tMVmFsKGxlZnQpO3RoaXMubmV4dCgpO25vZGUucmlnaHQgPSB0aGlzLnBhcnNlTWF5YmVBc3NpZ24obm9Jbik7cmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkFzc2lnbm1lbnRFeHByZXNzaW9uXCIpO31lbHNlIGlmKGZhaWxPblNob3J0aGFuZEFzc2lnbiAmJiByZWZTaG9ydGhhbmREZWZhdWx0UG9zLnN0YXJ0KXt0aGlzLnVuZXhwZWN0ZWQocmVmU2hvcnRoYW5kRGVmYXVsdFBvcy5zdGFydCk7fXJldHVybiBsZWZ0O307cHAucGFyc2VNYXliZUNvbmRpdGlvbmFsID0gZnVuY3Rpb24obm9JbiwgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcyl7dmFyIHN0YXJ0UG9zPXRoaXMuc3RhcnQsIHN0YXJ0TG9jPXRoaXMuc3RhcnRMb2M7dmFyIGV4cHI9dGhpcy5wYXJzZUV4cHJPcHMobm9JbiwgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcyk7aWYocmVmU2hvcnRoYW5kRGVmYXVsdFBvcyAmJiByZWZTaG9ydGhhbmREZWZhdWx0UG9zLnN0YXJ0KXJldHVybiBleHByO2lmKHRoaXMuZWF0KHR0LnF1ZXN0aW9uKSl7dmFyIG5vZGU9dGhpcy5zdGFydE5vZGVBdChzdGFydFBvcywgc3RhcnRMb2MpO25vZGUudGVzdCA9IGV4cHI7bm9kZS5jb25zZXF1ZW50ID0gdGhpcy5wYXJzZU1heWJlQXNzaWduKCk7dGhpcy5leHBlY3QodHQuY29sb24pO25vZGUuYWx0ZXJuYXRlID0gdGhpcy5wYXJzZU1heWJlQXNzaWduKG5vSW4pO3JldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJDb25kaXRpb25hbEV4cHJlc3Npb25cIik7fXJldHVybiBleHByO307cHAucGFyc2VFeHByT3BzID0gZnVuY3Rpb24obm9JbiwgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcyl7dmFyIHN0YXJ0UG9zPXRoaXMuc3RhcnQsIHN0YXJ0TG9jPXRoaXMuc3RhcnRMb2M7dmFyIGV4cHI9dGhpcy5wYXJzZU1heWJlVW5hcnkocmVmU2hvcnRoYW5kRGVmYXVsdFBvcyk7aWYocmVmU2hvcnRoYW5kRGVmYXVsdFBvcyAmJiByZWZTaG9ydGhhbmREZWZhdWx0UG9zLnN0YXJ0KXJldHVybiBleHByO3JldHVybiB0aGlzLnBhcnNlRXhwck9wKGV4cHIsIHN0YXJ0UG9zLCBzdGFydExvYywgLTEsIG5vSW4pO307cHAucGFyc2VFeHByT3AgPSBmdW5jdGlvbihsZWZ0LCBsZWZ0U3RhcnRQb3MsIGxlZnRTdGFydExvYywgbWluUHJlYywgbm9Jbil7dmFyIHByZWM9dGhpcy50eXBlLmJpbm9wO2lmKEFycmF5LmlzQXJyYXkobGVmdFN0YXJ0UG9zKSl7aWYodGhpcy5vcHRpb25zLmxvY2F0aW9ucyAmJiBub0luID09PSB1bmRlZmluZWQpe25vSW4gPSBtaW5QcmVjO21pblByZWMgPSBsZWZ0U3RhcnRMb2M7bGVmdFN0YXJ0TG9jID0gbGVmdFN0YXJ0UG9zWzFdO2xlZnRTdGFydFBvcyA9IGxlZnRTdGFydFBvc1swXTt9fWlmKHByZWMgIT0gbnVsbCAmJiAoIW5vSW4gfHwgdGhpcy50eXBlICE9PSB0dC5faW4pKXtpZihwcmVjID4gbWluUHJlYyl7dmFyIG5vZGU9dGhpcy5zdGFydE5vZGVBdChsZWZ0U3RhcnRQb3MsIGxlZnRTdGFydExvYyk7bm9kZS5sZWZ0ID0gbGVmdDtub2RlLm9wZXJhdG9yID0gdGhpcy52YWx1ZTt2YXIgb3A9dGhpcy50eXBlO3RoaXMubmV4dCgpO3ZhciBzdGFydFBvcz10aGlzLnN0YXJ0LCBzdGFydExvYz10aGlzLnN0YXJ0TG9jO25vZGUucmlnaHQgPSB0aGlzLnBhcnNlRXhwck9wKHRoaXMucGFyc2VNYXliZVVuYXJ5KCksIHN0YXJ0UG9zLCBzdGFydExvYywgcHJlYywgbm9Jbik7dGhpcy5maW5pc2hOb2RlKG5vZGUsIG9wID09PSB0dC5sb2dpY2FsT1IgfHwgb3AgPT09IHR0LmxvZ2ljYWxBTkQ/XCJMb2dpY2FsRXhwcmVzc2lvblwiOlwiQmluYXJ5RXhwcmVzc2lvblwiKTtyZXR1cm4gdGhpcy5wYXJzZUV4cHJPcChub2RlLCBsZWZ0U3RhcnRQb3MsIGxlZnRTdGFydExvYywgbWluUHJlYywgbm9Jbik7fX1yZXR1cm4gbGVmdDt9O3BwLnBhcnNlTWF5YmVVbmFyeSA9IGZ1bmN0aW9uKHJlZlNob3J0aGFuZERlZmF1bHRQb3Mpe2lmKHRoaXMudHlwZS5wcmVmaXgpe3ZhciBub2RlPXRoaXMuc3RhcnROb2RlKCksIHVwZGF0ZT10aGlzLnR5cGUgPT09IHR0LmluY0RlYztub2RlLm9wZXJhdG9yID0gdGhpcy52YWx1ZTtub2RlLnByZWZpeCA9IHRydWU7dGhpcy5uZXh0KCk7bm9kZS5hcmd1bWVudCA9IHRoaXMucGFyc2VNYXliZVVuYXJ5KCk7aWYocmVmU2hvcnRoYW5kRGVmYXVsdFBvcyAmJiByZWZTaG9ydGhhbmREZWZhdWx0UG9zLnN0YXJ0KXRoaXMudW5leHBlY3RlZChyZWZTaG9ydGhhbmREZWZhdWx0UG9zLnN0YXJ0KTtpZih1cGRhdGUpdGhpcy5jaGVja0xWYWwobm9kZS5hcmd1bWVudCk7ZWxzZSBpZih0aGlzLnN0cmljdCAmJiBub2RlLm9wZXJhdG9yID09PSBcImRlbGV0ZVwiICYmIG5vZGUuYXJndW1lbnQudHlwZSA9PT0gXCJJZGVudGlmaWVyXCIpdGhpcy5yYWlzZShub2RlLnN0YXJ0LCBcIkRlbGV0aW5nIGxvY2FsIHZhcmlhYmxlIGluIHN0cmljdCBtb2RlXCIpO3JldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgdXBkYXRlP1wiVXBkYXRlRXhwcmVzc2lvblwiOlwiVW5hcnlFeHByZXNzaW9uXCIpO312YXIgc3RhcnRQb3M9dGhpcy5zdGFydCwgc3RhcnRMb2M9dGhpcy5zdGFydExvYzt2YXIgZXhwcj10aGlzLnBhcnNlRXhwclN1YnNjcmlwdHMocmVmU2hvcnRoYW5kRGVmYXVsdFBvcyk7aWYocmVmU2hvcnRoYW5kRGVmYXVsdFBvcyAmJiByZWZTaG9ydGhhbmREZWZhdWx0UG9zLnN0YXJ0KXJldHVybiBleHByO3doaWxlKHRoaXMudHlwZS5wb3N0Zml4ICYmICF0aGlzLmNhbkluc2VydFNlbWljb2xvbigpKSB7dmFyIG5vZGU9dGhpcy5zdGFydE5vZGVBdChzdGFydFBvcywgc3RhcnRMb2MpO25vZGUub3BlcmF0b3IgPSB0aGlzLnZhbHVlO25vZGUucHJlZml4ID0gZmFsc2U7bm9kZS5hcmd1bWVudCA9IGV4cHI7dGhpcy5jaGVja0xWYWwoZXhwcik7dGhpcy5uZXh0KCk7ZXhwciA9IHRoaXMuZmluaXNoTm9kZShub2RlLCBcIlVwZGF0ZUV4cHJlc3Npb25cIik7fXJldHVybiBleHByO307cHAucGFyc2VFeHByU3Vic2NyaXB0cyA9IGZ1bmN0aW9uKHJlZlNob3J0aGFuZERlZmF1bHRQb3Mpe3ZhciBzdGFydFBvcz10aGlzLnN0YXJ0LCBzdGFydExvYz10aGlzLnN0YXJ0TG9jO3ZhciBleHByPXRoaXMucGFyc2VFeHByQXRvbShyZWZTaG9ydGhhbmREZWZhdWx0UG9zKTtpZihyZWZTaG9ydGhhbmREZWZhdWx0UG9zICYmIHJlZlNob3J0aGFuZERlZmF1bHRQb3Muc3RhcnQpcmV0dXJuIGV4cHI7cmV0dXJuIHRoaXMucGFyc2VTdWJzY3JpcHRzKGV4cHIsIHN0YXJ0UG9zLCBzdGFydExvYyk7fTtwcC5wYXJzZVN1YnNjcmlwdHMgPSBmdW5jdGlvbihiYXNlLCBzdGFydFBvcywgc3RhcnRMb2MsIG5vQ2FsbHMpe2lmKEFycmF5LmlzQXJyYXkoc3RhcnRQb3MpKXtpZih0aGlzLm9wdGlvbnMubG9jYXRpb25zICYmIG5vQ2FsbHMgPT09IHVuZGVmaW5lZCl7bm9DYWxscyA9IHN0YXJ0TG9jO3N0YXJ0TG9jID0gc3RhcnRQb3NbMV07c3RhcnRQb3MgPSBzdGFydFBvc1swXTt9fWZvcig7Oykge2lmKHRoaXMuZWF0KHR0LmRvdCkpe3ZhciBub2RlPXRoaXMuc3RhcnROb2RlQXQoc3RhcnRQb3MsIHN0YXJ0TG9jKTtub2RlLm9iamVjdCA9IGJhc2U7bm9kZS5wcm9wZXJ0eSA9IHRoaXMucGFyc2VJZGVudCh0cnVlKTtub2RlLmNvbXB1dGVkID0gZmFsc2U7YmFzZSA9IHRoaXMuZmluaXNoTm9kZShub2RlLCBcIk1lbWJlckV4cHJlc3Npb25cIik7fWVsc2UgaWYodGhpcy5lYXQodHQuYnJhY2tldEwpKXt2YXIgbm9kZT10aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0UG9zLCBzdGFydExvYyk7bm9kZS5vYmplY3QgPSBiYXNlO25vZGUucHJvcGVydHkgPSB0aGlzLnBhcnNlRXhwcmVzc2lvbigpO25vZGUuY29tcHV0ZWQgPSB0cnVlO3RoaXMuZXhwZWN0KHR0LmJyYWNrZXRSKTtiYXNlID0gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiTWVtYmVyRXhwcmVzc2lvblwiKTt9ZWxzZSBpZighbm9DYWxscyAmJiB0aGlzLmVhdCh0dC5wYXJlbkwpKXt2YXIgbm9kZT10aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0UG9zLCBzdGFydExvYyk7bm9kZS5jYWxsZWUgPSBiYXNlO25vZGUuYXJndW1lbnRzID0gdGhpcy5wYXJzZUV4cHJMaXN0KHR0LnBhcmVuUiwgZmFsc2UpO2Jhc2UgPSB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJDYWxsRXhwcmVzc2lvblwiKTt9ZWxzZSBpZih0aGlzLnR5cGUgPT09IHR0LmJhY2tRdW90ZSl7dmFyIG5vZGU9dGhpcy5zdGFydE5vZGVBdChzdGFydFBvcywgc3RhcnRMb2MpO25vZGUudGFnID0gYmFzZTtub2RlLnF1YXNpID0gdGhpcy5wYXJzZVRlbXBsYXRlKCk7YmFzZSA9IHRoaXMuZmluaXNoTm9kZShub2RlLCBcIlRhZ2dlZFRlbXBsYXRlRXhwcmVzc2lvblwiKTt9ZWxzZSB7cmV0dXJuIGJhc2U7fX19O3BwLnBhcnNlRXhwckF0b20gPSBmdW5jdGlvbihyZWZTaG9ydGhhbmREZWZhdWx0UG9zKXt2YXIgbm9kZT11bmRlZmluZWQsIGNhbkJlQXJyb3c9dGhpcy5wb3RlbnRpYWxBcnJvd0F0ID09IHRoaXMuc3RhcnQ7c3dpdGNoKHRoaXMudHlwZSl7Y2FzZSB0dC5fdGhpczpjYXNlIHR0Ll9zdXBlcjp2YXIgdHlwZT10aGlzLnR5cGUgPT09IHR0Ll90aGlzP1wiVGhpc0V4cHJlc3Npb25cIjpcIlN1cGVyXCI7bm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7dGhpcy5uZXh0KCk7cmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCB0eXBlKTtjYXNlIHR0Ll95aWVsZDppZih0aGlzLmluR2VuZXJhdG9yKXRoaXMudW5leHBlY3RlZCgpO2Nhc2UgdHQubmFtZTp2YXIgc3RhcnRQb3M9dGhpcy5zdGFydCwgc3RhcnRMb2M9dGhpcy5zdGFydExvYzt2YXIgaWQ9dGhpcy5wYXJzZUlkZW50KHRoaXMudHlwZSAhPT0gdHQubmFtZSk7aWYoY2FuQmVBcnJvdyAmJiAhdGhpcy5jYW5JbnNlcnRTZW1pY29sb24oKSAmJiB0aGlzLmVhdCh0dC5hcnJvdykpcmV0dXJuIHRoaXMucGFyc2VBcnJvd0V4cHJlc3Npb24odGhpcy5zdGFydE5vZGVBdChzdGFydFBvcywgc3RhcnRMb2MpLCBbaWRdKTtyZXR1cm4gaWQ7Y2FzZSB0dC5yZWdleHA6dmFyIHZhbHVlPXRoaXMudmFsdWU7bm9kZSA9IHRoaXMucGFyc2VMaXRlcmFsKHZhbHVlLnZhbHVlKTtub2RlLnJlZ2V4ID0ge3BhdHRlcm46dmFsdWUucGF0dGVybiwgZmxhZ3M6dmFsdWUuZmxhZ3N9O3JldHVybiBub2RlO2Nhc2UgdHQubnVtOmNhc2UgdHQuc3RyaW5nOnJldHVybiB0aGlzLnBhcnNlTGl0ZXJhbCh0aGlzLnZhbHVlKTtjYXNlIHR0Ll9udWxsOmNhc2UgdHQuX3RydWU6Y2FzZSB0dC5fZmFsc2U6bm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7bm9kZS52YWx1ZSA9IHRoaXMudHlwZSA9PT0gdHQuX251bGw/bnVsbDp0aGlzLnR5cGUgPT09IHR0Ll90cnVlO25vZGUucmF3ID0gdGhpcy50eXBlLmtleXdvcmQ7dGhpcy5uZXh0KCk7cmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkxpdGVyYWxcIik7Y2FzZSB0dC5wYXJlbkw6cmV0dXJuIHRoaXMucGFyc2VQYXJlbkFuZERpc3Rpbmd1aXNoRXhwcmVzc2lvbihjYW5CZUFycm93KTtjYXNlIHR0LmJyYWNrZXRMOm5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO3RoaXMubmV4dCgpO2lmKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA3ICYmIHRoaXMudHlwZSA9PT0gdHQuX2Zvcil7cmV0dXJuIHRoaXMucGFyc2VDb21wcmVoZW5zaW9uKG5vZGUsIGZhbHNlKTt9bm9kZS5lbGVtZW50cyA9IHRoaXMucGFyc2VFeHByTGlzdCh0dC5icmFja2V0UiwgdHJ1ZSwgdHJ1ZSwgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcyk7cmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkFycmF5RXhwcmVzc2lvblwiKTtjYXNlIHR0LmJyYWNlTDpyZXR1cm4gdGhpcy5wYXJzZU9iaihmYWxzZSwgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcyk7Y2FzZSB0dC5fZnVuY3Rpb246bm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7dGhpcy5uZXh0KCk7cmV0dXJuIHRoaXMucGFyc2VGdW5jdGlvbihub2RlLCBmYWxzZSk7Y2FzZSB0dC5fY2xhc3M6cmV0dXJuIHRoaXMucGFyc2VDbGFzcyh0aGlzLnN0YXJ0Tm9kZSgpLCBmYWxzZSk7Y2FzZSB0dC5fbmV3OnJldHVybiB0aGlzLnBhcnNlTmV3KCk7Y2FzZSB0dC5iYWNrUXVvdGU6cmV0dXJuIHRoaXMucGFyc2VUZW1wbGF0ZSgpO2RlZmF1bHQ6dGhpcy51bmV4cGVjdGVkKCk7fX07cHAucGFyc2VMaXRlcmFsID0gZnVuY3Rpb24odmFsdWUpe3ZhciBub2RlPXRoaXMuc3RhcnROb2RlKCk7bm9kZS52YWx1ZSA9IHZhbHVlO25vZGUucmF3ID0gdGhpcy5pbnB1dC5zbGljZSh0aGlzLnN0YXJ0LCB0aGlzLmVuZCk7dGhpcy5uZXh0KCk7cmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkxpdGVyYWxcIik7fTtwcC5wYXJzZVBhcmVuRXhwcmVzc2lvbiA9IGZ1bmN0aW9uKCl7dGhpcy5leHBlY3QodHQucGFyZW5MKTt2YXIgdmFsPXRoaXMucGFyc2VFeHByZXNzaW9uKCk7dGhpcy5leHBlY3QodHQucGFyZW5SKTtyZXR1cm4gdmFsO307cHAucGFyc2VQYXJlbkFuZERpc3Rpbmd1aXNoRXhwcmVzc2lvbiA9IGZ1bmN0aW9uKGNhbkJlQXJyb3cpe3ZhciBzdGFydFBvcz10aGlzLnN0YXJ0LCBzdGFydExvYz10aGlzLnN0YXJ0TG9jLCB2YWw9dW5kZWZpbmVkO2lmKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KXt0aGlzLm5leHQoKTtpZih0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNyAmJiB0aGlzLnR5cGUgPT09IHR0Ll9mb3Ipe3JldHVybiB0aGlzLnBhcnNlQ29tcHJlaGVuc2lvbih0aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0UG9zLCBzdGFydExvYyksIHRydWUpO312YXIgaW5uZXJTdGFydFBvcz10aGlzLnN0YXJ0LCBpbm5lclN0YXJ0TG9jPXRoaXMuc3RhcnRMb2M7dmFyIGV4cHJMaXN0PVtdLCBmaXJzdD10cnVlO3ZhciByZWZTaG9ydGhhbmREZWZhdWx0UG9zPXtzdGFydDowfSwgc3ByZWFkU3RhcnQ9dW5kZWZpbmVkLCBpbm5lclBhcmVuU3RhcnQ9dW5kZWZpbmVkO3doaWxlKHRoaXMudHlwZSAhPT0gdHQucGFyZW5SKSB7Zmlyc3Q/Zmlyc3QgPSBmYWxzZTp0aGlzLmV4cGVjdCh0dC5jb21tYSk7aWYodGhpcy50eXBlID09PSB0dC5lbGxpcHNpcyl7c3ByZWFkU3RhcnQgPSB0aGlzLnN0YXJ0O2V4cHJMaXN0LnB1c2godGhpcy5wYXJzZVBhcmVuSXRlbSh0aGlzLnBhcnNlUmVzdCgpKSk7YnJlYWs7fWVsc2Uge2lmKHRoaXMudHlwZSA9PT0gdHQucGFyZW5MICYmICFpbm5lclBhcmVuU3RhcnQpe2lubmVyUGFyZW5TdGFydCA9IHRoaXMuc3RhcnQ7fWV4cHJMaXN0LnB1c2godGhpcy5wYXJzZU1heWJlQXNzaWduKGZhbHNlLCByZWZTaG9ydGhhbmREZWZhdWx0UG9zLCB0aGlzLnBhcnNlUGFyZW5JdGVtKSk7fX12YXIgaW5uZXJFbmRQb3M9dGhpcy5zdGFydCwgaW5uZXJFbmRMb2M9dGhpcy5zdGFydExvYzt0aGlzLmV4cGVjdCh0dC5wYXJlblIpO2lmKGNhbkJlQXJyb3cgJiYgIXRoaXMuY2FuSW5zZXJ0U2VtaWNvbG9uKCkgJiYgdGhpcy5lYXQodHQuYXJyb3cpKXtpZihpbm5lclBhcmVuU3RhcnQpdGhpcy51bmV4cGVjdGVkKGlubmVyUGFyZW5TdGFydCk7cmV0dXJuIHRoaXMucGFyc2VQYXJlbkFycm93TGlzdChzdGFydFBvcywgc3RhcnRMb2MsIGV4cHJMaXN0KTt9aWYoIWV4cHJMaXN0Lmxlbmd0aCl0aGlzLnVuZXhwZWN0ZWQodGhpcy5sYXN0VG9rU3RhcnQpO2lmKHNwcmVhZFN0YXJ0KXRoaXMudW5leHBlY3RlZChzcHJlYWRTdGFydCk7aWYocmVmU2hvcnRoYW5kRGVmYXVsdFBvcy5zdGFydCl0aGlzLnVuZXhwZWN0ZWQocmVmU2hvcnRoYW5kRGVmYXVsdFBvcy5zdGFydCk7aWYoZXhwckxpc3QubGVuZ3RoID4gMSl7dmFsID0gdGhpcy5zdGFydE5vZGVBdChpbm5lclN0YXJ0UG9zLCBpbm5lclN0YXJ0TG9jKTt2YWwuZXhwcmVzc2lvbnMgPSBleHByTGlzdDt0aGlzLmZpbmlzaE5vZGVBdCh2YWwsIFwiU2VxdWVuY2VFeHByZXNzaW9uXCIsIGlubmVyRW5kUG9zLCBpbm5lckVuZExvYyk7fWVsc2Uge3ZhbCA9IGV4cHJMaXN0WzBdO319ZWxzZSB7dmFsID0gdGhpcy5wYXJzZVBhcmVuRXhwcmVzc2lvbigpO31pZih0aGlzLm9wdGlvbnMucHJlc2VydmVQYXJlbnMpe3ZhciBwYXI9dGhpcy5zdGFydE5vZGVBdChzdGFydFBvcywgc3RhcnRMb2MpO3Bhci5leHByZXNzaW9uID0gdmFsO3JldHVybiB0aGlzLmZpbmlzaE5vZGUocGFyLCBcIlBhcmVudGhlc2l6ZWRFeHByZXNzaW9uXCIpO31lbHNlIHtyZXR1cm4gdmFsO319O3BwLnBhcnNlUGFyZW5JdGVtID0gZnVuY3Rpb24oaXRlbSl7cmV0dXJuIGl0ZW07fTtwcC5wYXJzZVBhcmVuQXJyb3dMaXN0ID0gZnVuY3Rpb24oc3RhcnRQb3MsIHN0YXJ0TG9jLCBleHByTGlzdCl7cmV0dXJuIHRoaXMucGFyc2VBcnJvd0V4cHJlc3Npb24odGhpcy5zdGFydE5vZGVBdChzdGFydFBvcywgc3RhcnRMb2MpLCBleHByTGlzdCk7fTt2YXIgZW1wdHk9W107cHAucGFyc2VOZXcgPSBmdW5jdGlvbigpe3ZhciBub2RlPXRoaXMuc3RhcnROb2RlKCk7dmFyIG1ldGE9dGhpcy5wYXJzZUlkZW50KHRydWUpO2lmKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2ICYmIHRoaXMuZWF0KHR0LmRvdCkpe25vZGUubWV0YSA9IG1ldGE7bm9kZS5wcm9wZXJ0eSA9IHRoaXMucGFyc2VJZGVudCh0cnVlKTtpZihub2RlLnByb3BlcnR5Lm5hbWUgIT09IFwidGFyZ2V0XCIpdGhpcy5yYWlzZShub2RlLnByb3BlcnR5LnN0YXJ0LCBcIlRoZSBvbmx5IHZhbGlkIG1ldGEgcHJvcGVydHkgZm9yIG5ldyBpcyBuZXcudGFyZ2V0XCIpO3JldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJNZXRhUHJvcGVydHlcIik7fXZhciBzdGFydFBvcz10aGlzLnN0YXJ0LCBzdGFydExvYz10aGlzLnN0YXJ0TG9jO25vZGUuY2FsbGVlID0gdGhpcy5wYXJzZVN1YnNjcmlwdHModGhpcy5wYXJzZUV4cHJBdG9tKCksIHN0YXJ0UG9zLCBzdGFydExvYywgdHJ1ZSk7aWYodGhpcy5lYXQodHQucGFyZW5MKSlub2RlLmFyZ3VtZW50cyA9IHRoaXMucGFyc2VFeHByTGlzdCh0dC5wYXJlblIsIGZhbHNlKTtlbHNlIG5vZGUuYXJndW1lbnRzID0gZW1wdHk7cmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIk5ld0V4cHJlc3Npb25cIik7fTtwcC5wYXJzZVRlbXBsYXRlRWxlbWVudCA9IGZ1bmN0aW9uKCl7dmFyIGVsZW09dGhpcy5zdGFydE5vZGUoKTtlbGVtLnZhbHVlID0ge3Jhdzp0aGlzLmlucHV0LnNsaWNlKHRoaXMuc3RhcnQsIHRoaXMuZW5kKSwgY29va2VkOnRoaXMudmFsdWV9O3RoaXMubmV4dCgpO2VsZW0udGFpbCA9IHRoaXMudHlwZSA9PT0gdHQuYmFja1F1b3RlO3JldHVybiB0aGlzLmZpbmlzaE5vZGUoZWxlbSwgXCJUZW1wbGF0ZUVsZW1lbnRcIik7fTtwcC5wYXJzZVRlbXBsYXRlID0gZnVuY3Rpb24oKXt2YXIgbm9kZT10aGlzLnN0YXJ0Tm9kZSgpO3RoaXMubmV4dCgpO25vZGUuZXhwcmVzc2lvbnMgPSBbXTt2YXIgY3VyRWx0PXRoaXMucGFyc2VUZW1wbGF0ZUVsZW1lbnQoKTtub2RlLnF1YXNpcyA9IFtjdXJFbHRdO3doaWxlKCFjdXJFbHQudGFpbCkge3RoaXMuZXhwZWN0KHR0LmRvbGxhckJyYWNlTCk7bm9kZS5leHByZXNzaW9ucy5wdXNoKHRoaXMucGFyc2VFeHByZXNzaW9uKCkpO3RoaXMuZXhwZWN0KHR0LmJyYWNlUik7bm9kZS5xdWFzaXMucHVzaChjdXJFbHQgPSB0aGlzLnBhcnNlVGVtcGxhdGVFbGVtZW50KCkpO310aGlzLm5leHQoKTtyZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiVGVtcGxhdGVMaXRlcmFsXCIpO307cHAucGFyc2VPYmogPSBmdW5jdGlvbihpc1BhdHRlcm4sIHJlZlNob3J0aGFuZERlZmF1bHRQb3Mpe3ZhciBub2RlPXRoaXMuc3RhcnROb2RlKCksIGZpcnN0PXRydWUsIHByb3BIYXNoPXt9O25vZGUucHJvcGVydGllcyA9IFtdO3RoaXMubmV4dCgpO3doaWxlKCF0aGlzLmVhdCh0dC5icmFjZVIpKSB7aWYoIWZpcnN0KXt0aGlzLmV4cGVjdCh0dC5jb21tYSk7aWYodGhpcy5hZnRlclRyYWlsaW5nQ29tbWEodHQuYnJhY2VSKSlicmVhazt9ZWxzZSBmaXJzdCA9IGZhbHNlO3ZhciBwcm9wPXRoaXMuc3RhcnROb2RlKCksIGlzR2VuZXJhdG9yPXVuZGVmaW5lZCwgc3RhcnRQb3M9dW5kZWZpbmVkLCBzdGFydExvYz11bmRlZmluZWQ7aWYodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYpe3Byb3AubWV0aG9kID0gZmFsc2U7cHJvcC5zaG9ydGhhbmQgPSBmYWxzZTtpZihpc1BhdHRlcm4gfHwgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcyl7c3RhcnRQb3MgPSB0aGlzLnN0YXJ0O3N0YXJ0TG9jID0gdGhpcy5zdGFydExvYzt9aWYoIWlzUGF0dGVybilpc0dlbmVyYXRvciA9IHRoaXMuZWF0KHR0LnN0YXIpO310aGlzLnBhcnNlUHJvcGVydHlOYW1lKHByb3ApO3RoaXMucGFyc2VQcm9wZXJ0eVZhbHVlKHByb3AsIGlzUGF0dGVybiwgaXNHZW5lcmF0b3IsIHN0YXJ0UG9zLCBzdGFydExvYywgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcyk7dGhpcy5jaGVja1Byb3BDbGFzaChwcm9wLCBwcm9wSGFzaCk7bm9kZS5wcm9wZXJ0aWVzLnB1c2godGhpcy5maW5pc2hOb2RlKHByb3AsIFwiUHJvcGVydHlcIikpO31yZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIGlzUGF0dGVybj9cIk9iamVjdFBhdHRlcm5cIjpcIk9iamVjdEV4cHJlc3Npb25cIik7fTtwcC5wYXJzZVByb3BlcnR5VmFsdWUgPSBmdW5jdGlvbihwcm9wLCBpc1BhdHRlcm4sIGlzR2VuZXJhdG9yLCBzdGFydFBvcywgc3RhcnRMb2MsIHJlZlNob3J0aGFuZERlZmF1bHRQb3Mpe2lmKHRoaXMuZWF0KHR0LmNvbG9uKSl7cHJvcC52YWx1ZSA9IGlzUGF0dGVybj90aGlzLnBhcnNlTWF5YmVEZWZhdWx0KHRoaXMuc3RhcnQsIHRoaXMuc3RhcnRMb2MpOnRoaXMucGFyc2VNYXliZUFzc2lnbihmYWxzZSwgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcyk7cHJvcC5raW5kID0gXCJpbml0XCI7fWVsc2UgaWYodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYgJiYgdGhpcy50eXBlID09PSB0dC5wYXJlbkwpe2lmKGlzUGF0dGVybil0aGlzLnVuZXhwZWN0ZWQoKTtwcm9wLmtpbmQgPSBcImluaXRcIjtwcm9wLm1ldGhvZCA9IHRydWU7cHJvcC52YWx1ZSA9IHRoaXMucGFyc2VNZXRob2QoaXNHZW5lcmF0b3IpO31lbHNlIGlmKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA1ICYmICFwcm9wLmNvbXB1dGVkICYmIHByb3Aua2V5LnR5cGUgPT09IFwiSWRlbnRpZmllclwiICYmIChwcm9wLmtleS5uYW1lID09PSBcImdldFwiIHx8IHByb3Aua2V5Lm5hbWUgPT09IFwic2V0XCIpICYmICh0aGlzLnR5cGUgIT0gdHQuY29tbWEgJiYgdGhpcy50eXBlICE9IHR0LmJyYWNlUikpe2lmKGlzR2VuZXJhdG9yIHx8IGlzUGF0dGVybil0aGlzLnVuZXhwZWN0ZWQoKTtwcm9wLmtpbmQgPSBwcm9wLmtleS5uYW1lO3RoaXMucGFyc2VQcm9wZXJ0eU5hbWUocHJvcCk7cHJvcC52YWx1ZSA9IHRoaXMucGFyc2VNZXRob2QoZmFsc2UpO31lbHNlIGlmKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2ICYmICFwcm9wLmNvbXB1dGVkICYmIHByb3Aua2V5LnR5cGUgPT09IFwiSWRlbnRpZmllclwiKXtwcm9wLmtpbmQgPSBcImluaXRcIjtpZihpc1BhdHRlcm4pe2lmKHRoaXMuaXNLZXl3b3JkKHByb3Aua2V5Lm5hbWUpIHx8IHRoaXMuc3RyaWN0ICYmIChyZXNlcnZlZFdvcmRzLnN0cmljdEJpbmQocHJvcC5rZXkubmFtZSkgfHwgcmVzZXJ2ZWRXb3Jkcy5zdHJpY3QocHJvcC5rZXkubmFtZSkpIHx8ICF0aGlzLm9wdGlvbnMuYWxsb3dSZXNlcnZlZCAmJiB0aGlzLmlzUmVzZXJ2ZWRXb3JkKHByb3Aua2V5Lm5hbWUpKXRoaXMucmFpc2UocHJvcC5rZXkuc3RhcnQsIFwiQmluZGluZyBcIiArIHByb3Aua2V5Lm5hbWUpO3Byb3AudmFsdWUgPSB0aGlzLnBhcnNlTWF5YmVEZWZhdWx0KHN0YXJ0UG9zLCBzdGFydExvYywgcHJvcC5rZXkpO31lbHNlIGlmKHRoaXMudHlwZSA9PT0gdHQuZXEgJiYgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcyl7aWYoIXJlZlNob3J0aGFuZERlZmF1bHRQb3Muc3RhcnQpcmVmU2hvcnRoYW5kRGVmYXVsdFBvcy5zdGFydCA9IHRoaXMuc3RhcnQ7cHJvcC52YWx1ZSA9IHRoaXMucGFyc2VNYXliZURlZmF1bHQoc3RhcnRQb3MsIHN0YXJ0TG9jLCBwcm9wLmtleSk7fWVsc2Uge3Byb3AudmFsdWUgPSBwcm9wLmtleTt9cHJvcC5zaG9ydGhhbmQgPSB0cnVlO31lbHNlIHRoaXMudW5leHBlY3RlZCgpO307cHAucGFyc2VQcm9wZXJ0eU5hbWUgPSBmdW5jdGlvbihwcm9wKXtpZih0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNil7aWYodGhpcy5lYXQodHQuYnJhY2tldEwpKXtwcm9wLmNvbXB1dGVkID0gdHJ1ZTtwcm9wLmtleSA9IHRoaXMucGFyc2VNYXliZUFzc2lnbigpO3RoaXMuZXhwZWN0KHR0LmJyYWNrZXRSKTtyZXR1cm4gcHJvcC5rZXk7fWVsc2Uge3Byb3AuY29tcHV0ZWQgPSBmYWxzZTt9fXJldHVybiBwcm9wLmtleSA9IHRoaXMudHlwZSA9PT0gdHQubnVtIHx8IHRoaXMudHlwZSA9PT0gdHQuc3RyaW5nP3RoaXMucGFyc2VFeHByQXRvbSgpOnRoaXMucGFyc2VJZGVudCh0cnVlKTt9O3BwLmluaXRGdW5jdGlvbiA9IGZ1bmN0aW9uKG5vZGUpe25vZGUuaWQgPSBudWxsO2lmKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KXtub2RlLmdlbmVyYXRvciA9IGZhbHNlO25vZGUuZXhwcmVzc2lvbiA9IGZhbHNlO319O3BwLnBhcnNlTWV0aG9kID0gZnVuY3Rpb24oaXNHZW5lcmF0b3Ipe3ZhciBub2RlPXRoaXMuc3RhcnROb2RlKCk7dGhpcy5pbml0RnVuY3Rpb24obm9kZSk7dGhpcy5leHBlY3QodHQucGFyZW5MKTtub2RlLnBhcmFtcyA9IHRoaXMucGFyc2VCaW5kaW5nTGlzdCh0dC5wYXJlblIsIGZhbHNlLCBmYWxzZSk7dmFyIGFsbG93RXhwcmVzc2lvbkJvZHk9dW5kZWZpbmVkO2lmKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KXtub2RlLmdlbmVyYXRvciA9IGlzR2VuZXJhdG9yO2FsbG93RXhwcmVzc2lvbkJvZHkgPSB0cnVlO31lbHNlIHthbGxvd0V4cHJlc3Npb25Cb2R5ID0gZmFsc2U7fXRoaXMucGFyc2VGdW5jdGlvbkJvZHkobm9kZSwgYWxsb3dFeHByZXNzaW9uQm9keSk7cmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkZ1bmN0aW9uRXhwcmVzc2lvblwiKTt9O3BwLnBhcnNlQXJyb3dFeHByZXNzaW9uID0gZnVuY3Rpb24obm9kZSwgcGFyYW1zKXt0aGlzLmluaXRGdW5jdGlvbihub2RlKTtub2RlLnBhcmFtcyA9IHRoaXMudG9Bc3NpZ25hYmxlTGlzdChwYXJhbXMsIHRydWUpO3RoaXMucGFyc2VGdW5jdGlvbkJvZHkobm9kZSwgdHJ1ZSk7cmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkFycm93RnVuY3Rpb25FeHByZXNzaW9uXCIpO307cHAucGFyc2VGdW5jdGlvbkJvZHkgPSBmdW5jdGlvbihub2RlLCBhbGxvd0V4cHJlc3Npb24pe3ZhciBpc0V4cHJlc3Npb249YWxsb3dFeHByZXNzaW9uICYmIHRoaXMudHlwZSAhPT0gdHQuYnJhY2VMO2lmKGlzRXhwcmVzc2lvbil7bm9kZS5ib2R5ID0gdGhpcy5wYXJzZU1heWJlQXNzaWduKCk7bm9kZS5leHByZXNzaW9uID0gdHJ1ZTt9ZWxzZSB7dmFyIG9sZEluRnVuYz10aGlzLmluRnVuY3Rpb24sIG9sZEluR2VuPXRoaXMuaW5HZW5lcmF0b3IsIG9sZExhYmVscz10aGlzLmxhYmVsczt0aGlzLmluRnVuY3Rpb24gPSB0cnVlO3RoaXMuaW5HZW5lcmF0b3IgPSBub2RlLmdlbmVyYXRvcjt0aGlzLmxhYmVscyA9IFtdO25vZGUuYm9keSA9IHRoaXMucGFyc2VCbG9jayh0cnVlKTtub2RlLmV4cHJlc3Npb24gPSBmYWxzZTt0aGlzLmluRnVuY3Rpb24gPSBvbGRJbkZ1bmM7dGhpcy5pbkdlbmVyYXRvciA9IG9sZEluR2VuO3RoaXMubGFiZWxzID0gb2xkTGFiZWxzO31pZih0aGlzLnN0cmljdCB8fCAhaXNFeHByZXNzaW9uICYmIG5vZGUuYm9keS5ib2R5Lmxlbmd0aCAmJiB0aGlzLmlzVXNlU3RyaWN0KG5vZGUuYm9keS5ib2R5WzBdKSl7dmFyIG5hbWVIYXNoPXt9LCBvbGRTdHJpY3Q9dGhpcy5zdHJpY3Q7dGhpcy5zdHJpY3QgPSB0cnVlO2lmKG5vZGUuaWQpdGhpcy5jaGVja0xWYWwobm9kZS5pZCwgdHJ1ZSk7Zm9yKHZhciBpPTA7IGkgPCBub2RlLnBhcmFtcy5sZW5ndGg7IGkrKykge3RoaXMuY2hlY2tMVmFsKG5vZGUucGFyYW1zW2ldLCB0cnVlLCBuYW1lSGFzaCk7fXRoaXMuc3RyaWN0ID0gb2xkU3RyaWN0O319O3BwLnBhcnNlRXhwckxpc3QgPSBmdW5jdGlvbihjbG9zZSwgYWxsb3dUcmFpbGluZ0NvbW1hLCBhbGxvd0VtcHR5LCByZWZTaG9ydGhhbmREZWZhdWx0UG9zKXt2YXIgZWx0cz1bXSwgZmlyc3Q9dHJ1ZTt3aGlsZSghdGhpcy5lYXQoY2xvc2UpKSB7aWYoIWZpcnN0KXt0aGlzLmV4cGVjdCh0dC5jb21tYSk7aWYoYWxsb3dUcmFpbGluZ0NvbW1hICYmIHRoaXMuYWZ0ZXJUcmFpbGluZ0NvbW1hKGNsb3NlKSlicmVhazt9ZWxzZSBmaXJzdCA9IGZhbHNlO2lmKGFsbG93RW1wdHkgJiYgdGhpcy50eXBlID09PSB0dC5jb21tYSl7ZWx0cy5wdXNoKG51bGwpO31lbHNlIHtpZih0aGlzLnR5cGUgPT09IHR0LmVsbGlwc2lzKWVsdHMucHVzaCh0aGlzLnBhcnNlU3ByZWFkKHJlZlNob3J0aGFuZERlZmF1bHRQb3MpKTtlbHNlIGVsdHMucHVzaCh0aGlzLnBhcnNlTWF5YmVBc3NpZ24oZmFsc2UsIHJlZlNob3J0aGFuZERlZmF1bHRQb3MpKTt9fXJldHVybiBlbHRzO307cHAucGFyc2VJZGVudCA9IGZ1bmN0aW9uKGxpYmVyYWwpe3ZhciBub2RlPXRoaXMuc3RhcnROb2RlKCk7aWYobGliZXJhbCAmJiB0aGlzLm9wdGlvbnMuYWxsb3dSZXNlcnZlZCA9PSBcIm5ldmVyXCIpbGliZXJhbCA9IGZhbHNlO2lmKHRoaXMudHlwZSA9PT0gdHQubmFtZSl7aWYoIWxpYmVyYWwgJiYgKCF0aGlzLm9wdGlvbnMuYWxsb3dSZXNlcnZlZCAmJiB0aGlzLmlzUmVzZXJ2ZWRXb3JkKHRoaXMudmFsdWUpIHx8IHRoaXMuc3RyaWN0ICYmIHJlc2VydmVkV29yZHMuc3RyaWN0KHRoaXMudmFsdWUpICYmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNiB8fCB0aGlzLmlucHV0LnNsaWNlKHRoaXMuc3RhcnQsIHRoaXMuZW5kKS5pbmRleE9mKFwiXFxcXFwiKSA9PSAtMSkpKXRoaXMucmFpc2UodGhpcy5zdGFydCwgXCJUaGUga2V5d29yZCAnXCIgKyB0aGlzLnZhbHVlICsgXCInIGlzIHJlc2VydmVkXCIpO25vZGUubmFtZSA9IHRoaXMudmFsdWU7fWVsc2UgaWYobGliZXJhbCAmJiB0aGlzLnR5cGUua2V5d29yZCl7bm9kZS5uYW1lID0gdGhpcy50eXBlLmtleXdvcmQ7fWVsc2Uge3RoaXMudW5leHBlY3RlZCgpO310aGlzLm5leHQoKTtyZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiSWRlbnRpZmllclwiKTt9O3BwLnBhcnNlWWllbGQgPSBmdW5jdGlvbigpe3ZhciBub2RlPXRoaXMuc3RhcnROb2RlKCk7dGhpcy5uZXh0KCk7aWYodGhpcy50eXBlID09IHR0LnNlbWkgfHwgdGhpcy5jYW5JbnNlcnRTZW1pY29sb24oKSB8fCB0aGlzLnR5cGUgIT0gdHQuc3RhciAmJiAhdGhpcy50eXBlLnN0YXJ0c0V4cHIpe25vZGUuZGVsZWdhdGUgPSBmYWxzZTtub2RlLmFyZ3VtZW50ID0gbnVsbDt9ZWxzZSB7bm9kZS5kZWxlZ2F0ZSA9IHRoaXMuZWF0KHR0LnN0YXIpO25vZGUuYXJndW1lbnQgPSB0aGlzLnBhcnNlTWF5YmVBc3NpZ24oKTt9cmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIllpZWxkRXhwcmVzc2lvblwiKTt9O3BwLnBhcnNlQ29tcHJlaGVuc2lvbiA9IGZ1bmN0aW9uKG5vZGUsIGlzR2VuZXJhdG9yKXtub2RlLmJsb2NrcyA9IFtdO3doaWxlKHRoaXMudHlwZSA9PT0gdHQuX2Zvcikge3ZhciBibG9jaz10aGlzLnN0YXJ0Tm9kZSgpO3RoaXMubmV4dCgpO3RoaXMuZXhwZWN0KHR0LnBhcmVuTCk7YmxvY2subGVmdCA9IHRoaXMucGFyc2VCaW5kaW5nQXRvbSgpO3RoaXMuY2hlY2tMVmFsKGJsb2NrLmxlZnQsIHRydWUpO3RoaXMuZXhwZWN0Q29udGV4dHVhbChcIm9mXCIpO2Jsb2NrLnJpZ2h0ID0gdGhpcy5wYXJzZUV4cHJlc3Npb24oKTt0aGlzLmV4cGVjdCh0dC5wYXJlblIpO25vZGUuYmxvY2tzLnB1c2godGhpcy5maW5pc2hOb2RlKGJsb2NrLCBcIkNvbXByZWhlbnNpb25CbG9ja1wiKSk7fW5vZGUuZmlsdGVyID0gdGhpcy5lYXQodHQuX2lmKT90aGlzLnBhcnNlUGFyZW5FeHByZXNzaW9uKCk6bnVsbDtub2RlLmJvZHkgPSB0aGlzLnBhcnNlRXhwcmVzc2lvbigpO3RoaXMuZXhwZWN0KGlzR2VuZXJhdG9yP3R0LnBhcmVuUjp0dC5icmFja2V0Uik7bm9kZS5nZW5lcmF0b3IgPSBpc0dlbmVyYXRvcjtyZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiQ29tcHJlaGVuc2lvbkV4cHJlc3Npb25cIik7fTt9LCB7XCIuL2lkZW50aWZpZXJcIjo3LCBcIi4vc3RhdGVcIjoxMywgXCIuL3Rva2VudHlwZVwiOjE3LCBcIi4vdXRpbFwiOjE4fV0sIDc6W2Z1bmN0aW9uKF9kZXJlcV8sIG1vZHVsZSwgZXhwb3J0cyl7XCJ1c2Ugc3RyaWN0XCI7ZXhwb3J0cy5pc0lkZW50aWZpZXJTdGFydCA9IGlzSWRlbnRpZmllclN0YXJ0O2V4cG9ydHMuaXNJZGVudGlmaWVyQ2hhciA9IGlzSWRlbnRpZmllckNoYXI7ZXhwb3J0cy5fX2VzTW9kdWxlID0gdHJ1ZTtmdW5jdGlvbiBtYWtlUHJlZGljYXRlKHdvcmRzKXt3b3JkcyA9IHdvcmRzLnNwbGl0KFwiIFwiKTt2YXIgZj1cIlwiLCBjYXRzPVtdO291dDogZm9yKHZhciBpPTA7IGkgPCB3b3Jkcy5sZW5ndGg7ICsraSkge2Zvcih2YXIgaj0wOyBqIDwgY2F0cy5sZW5ndGg7ICsraikge2lmKGNhdHNbal1bMF0ubGVuZ3RoID09IHdvcmRzW2ldLmxlbmd0aCl7Y2F0c1tqXS5wdXNoKHdvcmRzW2ldKTtjb250aW51ZSBvdXQ7fX1jYXRzLnB1c2goW3dvcmRzW2ldXSk7fWZ1bmN0aW9uIGNvbXBhcmVUbyhhcnIpe2lmKGFyci5sZW5ndGggPT0gMSl7cmV0dXJuIGYgKz0gXCJyZXR1cm4gc3RyID09PSBcIiArIEpTT04uc3RyaW5naWZ5KGFyclswXSkgKyBcIjtcIjt9ZiArPSBcInN3aXRjaChzdHIpe1wiO2Zvcih2YXIgaT0wOyBpIDwgYXJyLmxlbmd0aDsgKytpKSB7ZiArPSBcImNhc2UgXCIgKyBKU09OLnN0cmluZ2lmeShhcnJbaV0pICsgXCI6XCI7fWYgKz0gXCJyZXR1cm4gdHJ1ZX1yZXR1cm4gZmFsc2U7XCI7fWlmKGNhdHMubGVuZ3RoID4gMyl7Y2F0cy5zb3J0KGZ1bmN0aW9uKGEsIGIpe3JldHVybiBiLmxlbmd0aCAtIGEubGVuZ3RoO30pO2YgKz0gXCJzd2l0Y2goc3RyLmxlbmd0aCl7XCI7Zm9yKHZhciBpPTA7IGkgPCBjYXRzLmxlbmd0aDsgKytpKSB7dmFyIGNhdD1jYXRzW2ldO2YgKz0gXCJjYXNlIFwiICsgY2F0WzBdLmxlbmd0aCArIFwiOlwiO2NvbXBhcmVUbyhjYXQpO31mICs9IFwifVwiO31lbHNlIHtjb21wYXJlVG8od29yZHMpO31yZXR1cm4gbmV3IEZ1bmN0aW9uKFwic3RyXCIsIGYpO312YXIgcmVzZXJ2ZWRXb3Jkcz17MzptYWtlUHJlZGljYXRlKFwiYWJzdHJhY3QgYm9vbGVhbiBieXRlIGNoYXIgY2xhc3MgZG91YmxlIGVudW0gZXhwb3J0IGV4dGVuZHMgZmluYWwgZmxvYXQgZ290byBpbXBsZW1lbnRzIGltcG9ydCBpbnQgaW50ZXJmYWNlIGxvbmcgbmF0aXZlIHBhY2thZ2UgcHJpdmF0ZSBwcm90ZWN0ZWQgcHVibGljIHNob3J0IHN0YXRpYyBzdXBlciBzeW5jaHJvbml6ZWQgdGhyb3dzIHRyYW5zaWVudCB2b2xhdGlsZVwiKSwgNTptYWtlUHJlZGljYXRlKFwiY2xhc3MgZW51bSBleHRlbmRzIHN1cGVyIGNvbnN0IGV4cG9ydCBpbXBvcnRcIiksIDY6bWFrZVByZWRpY2F0ZShcImVudW0gYXdhaXRcIiksIHN0cmljdDptYWtlUHJlZGljYXRlKFwiaW1wbGVtZW50cyBpbnRlcmZhY2UgbGV0IHBhY2thZ2UgcHJpdmF0ZSBwcm90ZWN0ZWQgcHVibGljIHN0YXRpYyB5aWVsZFwiKSwgc3RyaWN0QmluZDptYWtlUHJlZGljYXRlKFwiZXZhbCBhcmd1bWVudHNcIil9O2V4cG9ydHMucmVzZXJ2ZWRXb3JkcyA9IHJlc2VydmVkV29yZHM7dmFyIGVjbWE1QW5kTGVzc0tleXdvcmRzPVwiYnJlYWsgY2FzZSBjYXRjaCBjb250aW51ZSBkZWJ1Z2dlciBkZWZhdWx0IGRvIGVsc2UgZmluYWxseSBmb3IgZnVuY3Rpb24gaWYgcmV0dXJuIHN3aXRjaCB0aHJvdyB0cnkgdmFyIHdoaWxlIHdpdGggbnVsbCB0cnVlIGZhbHNlIGluc3RhbmNlb2YgdHlwZW9mIHZvaWQgZGVsZXRlIG5ldyBpbiB0aGlzXCI7dmFyIGtleXdvcmRzPXs1Om1ha2VQcmVkaWNhdGUoZWNtYTVBbmRMZXNzS2V5d29yZHMpLCA2Om1ha2VQcmVkaWNhdGUoZWNtYTVBbmRMZXNzS2V5d29yZHMgKyBcIiBsZXQgY29uc3QgY2xhc3MgZXh0ZW5kcyBleHBvcnQgaW1wb3J0IHlpZWxkIHN1cGVyXCIpfTtleHBvcnRzLmtleXdvcmRzID0ga2V5d29yZHM7dmFyIG5vbkFTQ0lJaWRlbnRpZmllclN0YXJ0Q2hhcnM9XCLCqsK1wrrDgC3DlsOYLcO2w7gty4HLhi3LkcugLcuky6zLrs2wLc20zbbNt826Lc29zb/Ohs6ILc6KzozOji3Ooc6jLc+1z7ct0oHSii3Ur9SxLdWW1ZnVoS3Wh9eQLdeq17At17LYoC3Zitmu2a/ZsS3bk9uV26Xbptuu26/bui3bvNu/3JDcki3cr92NLd6l3rHfii3fqt+037XfuuCggC3goJXgoJrgoKTgoKjgoYAt4KGY4KKgLeCisuCkhC3gpLngpL3gpZDgpZgt4KWh4KWxLeCmgOCmhS3gpozgpo/gppDgppMt4Kao4KaqLeCmsOCmsuCmti3gprngpr3gp47gp5zgp53gp58t4Keh4Kew4Kex4KiFLeCoiuCoj+CokOCoky3gqKjgqKot4Kiw4Kiy4Kiz4Ki14Ki24Ki44Ki54KmZLeCpnOCpnuCpsi3gqbTgqoUt4KqN4KqPLeCqkeCqky3gqqjgqqot4Kqw4Kqy4Kqz4Kq1LeCqueCqveCrkOCroOCroeCshS3grIzgrI/grJDgrJMt4Kyo4KyqLeCssOCssuCss+CstS3grLngrL3grZzgrZ3grZ8t4K2h4K2x4K6D4K6FLeCuiuCuji3grpDgrpIt4K6V4K6Z4K6a4K6c4K6e4K6f4K6j4K6k4K6oLeCuquCuri3grrngr5DgsIUt4LCM4LCOLeCwkOCwki3gsKjgsKot4LC54LC94LGY4LGZ4LGg4LGh4LKFLeCyjOCyji3gspDgspIt4LKo4LKqLeCys+CytS3gsrngsr3gs57gs6Dgs6Hgs7Hgs7LgtIUt4LSM4LSOLeC0kOC0ki3gtLrgtL3gtY7gtaDgtaHgtbot4LW/4LaFLeC2luC2mi3gtrHgtrMt4La74La94LeALeC3huC4gS3guLDguLLguLPguYAt4LmG4LqB4LqC4LqE4LqH4LqI4LqK4LqN4LqULeC6l+C6mS3gup/guqEt4Lqj4Lql4Lqn4Lqq4Lqr4LqtLeC6sOC6suC6s+C6veC7gC3gu4Tgu4bgu5wt4Luf4LyA4L2ALeC9h+C9iS3gvazgvogt4L6M4YCALeGAquGAv+GBkC3hgZXhgZot4YGd4YGh4YGl4YGm4YGuLeGBsOGBtS3hgoHhgo7hgqAt4YOF4YOH4YON4YOQLeGDuuGDvC3hiYjhiYot4YmN4YmQLeGJluGJmOGJmi3hiZ3hiaAt4YqI4YqKLeGKjeGKkC3hirDhirIt4Yq14Yq4LeGKvuGLgOGLgi3hi4Xhi4gt4YuW4YuYLeGMkOGMki3hjJXhjJgt4Y2a4Y6ALeGOj+GOoC3hj7ThkIEt4Zms4ZmvLeGZv+GagS3hmprhmqAt4Zuq4ZuuLeGbuOGcgC3hnIzhnI4t4ZyR4ZygLeGcseGdgC3hnZHhnaAt4Z2s4Z2uLeGdsOGegC3hnrPhn5fhn5zhoKAt4aG34aKALeGiqOGiquGisC3ho7XhpIAt4aSe4aWQLeGlreGlsC3hpbThpoAt4aar4aeBLeGnh+GogC3hqJbhqKAt4amU4aqn4ayFLeGss+GthS3hrYvhroMt4a6g4a6u4a6v4a66LeGvpeGwgC3hsKPhsY0t4bGP4bGaLeGxveGzqS3hs6zhs64t4bOx4bO14bO24bSALeG2v+G4gC3hvJXhvJgt4byd4bygLeG9heG9iC3hvY3hvZAt4b2X4b2Z4b2b4b2d4b2fLeG9veG+gC3hvrThvrYt4b684b6+4b+CLeG/hOG/hi3hv4zhv5At4b+T4b+WLeG/m+G/oC3hv6zhv7It4b+04b+2LeG/vOKBseKBv+KCkC3igpzihILihIfihIot4oST4oSV4oSYLeKEneKEpOKEpuKEqOKEqi3ihLnihLwt4oS/4oWFLeKFieKFjuKFoC3ihojisIAt4rCu4rCwLeKxnuKxoC3is6Tis6st4rOu4rOy4rOz4rSALeK0peK0p+K0reK0sC3itafita/itoAt4raW4ragLeK2puK2qC3itq7itrAt4ra24ra4LeK2vuK3gC3it4bit4gt4reO4reQLeK3luK3mC3it57jgIUt44CH44ChLeOAqeOAsS3jgLXjgLgt44C844GBLeOCluOCmy3jgp/jgqEt44O644O8LeODv+OEhS3jhK3jhLEt44aO44agLeOGuuOHsC3jh7/jkIAt5La15LiALem/jOqAgC3qkozqk5At6pO96pSALeqYjOqYkC3qmJ/qmKrqmKvqmYAt6pmu6pm/LeqaneqaoC3qm6/qnJct6pyf6pyiLeqeiOqeiy3qno7qnpAt6p6t6p6w6p6x6p+3Leqggeqggy3qoIXqoIct6qCK6qCMLeqgouqhgC3qobPqooIt6qKz6qOyLeqjt+qju+qkii3qpKXqpLAt6qWG6qWgLeqlvOqmhC3qprLqp4/qp6At6qek6qemLeqnr+qnui3qp77qqIAt6qio6qmALeqpguqphC3qqYvqqaAt6qm26qm66qm+Leqqr+qqseqqteqqtuqquS3qqr3qq4Dqq4Lqq5st6qud6qugLeqrquqrsi3qq7TqrIEt6qyG6qyJLeqsjuqskS3qrJbqrKAt6qym6qyoLeqsruqssC3qrZrqrZwt6q2f6q2k6q2l6q+ALeqvouqwgC3tnqPtnrAt7Z+G7Z+LLe2fu++kgC3vqa3vqbAt76uZ76yALe+shu+sky3vrJfvrJ3vrJ8t76yo76yqLe+stu+suC3vrLzvrL7vrYDvrYHvrYPvrYTvrYYt766x76+TLe+0ve+1kC3vto/vtpIt77eH77ewLe+3u++5sC3vubTvubYt77u877yhLe+8uu+9gS3vvZrvvaYt776+77+CLe+/h++/ii3vv4/vv5It77+X77+aLe+/nFwiO3ZhciBub25BU0NJSWlkZW50aWZpZXJDaGFycz1cIuKAjOKAjcK3zIAtza/Oh9KDLdKH1pEt1r3Wv9eB14LXhNeF14fYkC3YmtmLLdmp2bDbli3bnNufLduk26fbqNuqLdut27At27nckdywLd2K3qYt3rDfgC3fid+rLd+z4KCWLeCgmeCgmy3goKPgoKUt4KCn4KCpLeCgreChmS3goZvgo6Qt4KSD4KS6LeCkvOCkvi3gpY/gpZEt4KWX4KWi4KWj4KWmLeClr+CmgS3gpoPgprzgpr4t4KeE4KeH4KeI4KeLLeCnjeCnl+CnouCno+Cnpi3gp6/gqIEt4KiD4Ki84Ki+LeCpguCph+CpiOCpiy3gqY3gqZHgqaYt4Kmx4Km14KqBLeCqg+CqvOCqvi3gq4Xgq4ct4KuJ4KuLLeCrjeCrouCro+Crpi3gq6/grIEt4KyD4Ky84Ky+LeCthOCth+CtiOCtiy3grY3grZbgrZfgraLgraPgraYt4K2v4K6C4K6+LeCvguCvhi3gr4jgr4ot4K+N4K+X4K+mLeCvr+CwgC3gsIPgsL4t4LGE4LGGLeCxiOCxii3gsY3gsZXgsZbgsaLgsaPgsaYt4LGv4LKBLeCyg+CyvOCyvi3gs4Tgs4Yt4LOI4LOKLeCzjeCzleCzluCzouCzo+Czpi3gs6/gtIEt4LSD4LS+LeC1hOC1hi3gtYjgtYot4LWN4LWX4LWi4LWj4LWmLeC1r+C2guC2g+C3iuC3jy3gt5Tgt5bgt5gt4Lef4LemLeC3r+C3suC3s+C4seC4tC3guLrguYct4LmO4LmQLeC5meC6seC6tC3gurngurvgurzgu4gt4LuN4LuQLeC7meC8mOC8meC8oC3gvKngvLXgvLfgvLngvL7gvL/gvbEt4L6E4L6G4L6H4L6NLeC+l+C+mS3gvrzgv4bhgKst4YC+4YGALeGBieGBli3hgZnhgZ4t4YGg4YGiLeGBpOGBpy3hga3hgbEt4YG04YKCLeGCjeGCjy3hgp3hjZ0t4Y2f4Y2pLeGNseGcki3hnJThnLIt4Zy04Z2S4Z2T4Z2y4Z2z4Z60LeGfk+GfneGfoC3hn6nhoIst4aCN4aCQLeGgmeGiqeGkoC3hpKvhpLAt4aS74aWGLeGlj+GmsC3hp4Dhp4jhp4nhp5At4aea4aiXLeGom+GplS3hqZ7hqaAt4am84am/LeGqieGqkC3hqpnhqrAt4aq94ayALeGshOGstC3hrYThrZAt4a2Z4a2rLeGts+GugC3hroLhrqEt4a6t4a6wLeGuueGvpi3hr7PhsKQt4bC34bGALeGxieGxkC3hsZnhs5At4bOS4bOULeGzqOGzreGzsi3hs7Ths7jhs7nht4At4be14be8LeG3v+KAv+KBgOKBlOKDkC3ig5zig6Hig6Ut4oOw4rOvLeKzseK1v+K3oC3it7/jgKot44Cv44KZ44Ka6pigLeqYqeqZr+qZtC3qmb3qmp/qm7Dqm7HqoILqoIbqoIvqoKMt6qCn6qKA6qKB6qK0LeqjhOqjkC3qo5nqo6At6qOx6qSALeqkieqkpi3qpK3qpYct6qWT6qaALeqmg+qmsy3qp4Dqp5At6qeZ6qel6qewLeqnueqoqS3qqLbqqYPqqYzqqY3qqZAt6qmZ6qm7LeqpveqqsOqqsi3qqrTqqrfqqrjqqr7qqr/qq4Hqq6st6quv6qu16qu26q+jLeqvquqvrOqvreqvsC3qr7nvrJ7vuIAt77iP77igLe+4re+4s++4tO+5jS3vuY/vvJAt77yZ77y/XCI7dmFyIG5vbkFTQ0lJaWRlbnRpZmllclN0YXJ0PW5ldyBSZWdFeHAoXCJbXCIgKyBub25BU0NJSWlkZW50aWZpZXJTdGFydENoYXJzICsgXCJdXCIpO3ZhciBub25BU0NJSWlkZW50aWZpZXI9bmV3IFJlZ0V4cChcIltcIiArIG5vbkFTQ0lJaWRlbnRpZmllclN0YXJ0Q2hhcnMgKyBub25BU0NJSWlkZW50aWZpZXJDaGFycyArIFwiXVwiKTtub25BU0NJSWlkZW50aWZpZXJTdGFydENoYXJzID0gbm9uQVNDSUlpZGVudGlmaWVyQ2hhcnMgPSBudWxsO3ZhciBhc3RyYWxJZGVudGlmaWVyU3RhcnRDb2Rlcz1bMCwgMTEsIDIsIDI1LCAyLCAxOCwgMiwgMSwgMiwgMTQsIDMsIDEzLCAzNSwgMTIyLCA3MCwgNTIsIDI2OCwgMjgsIDQsIDQ4LCA0OCwgMzEsIDE3LCAyNiwgNiwgMzcsIDExLCAyOSwgMywgMzUsIDUsIDcsIDIsIDQsIDQzLCAxNTcsIDk5LCAzOSwgOSwgNTEsIDE1NywgMzEwLCAxMCwgMjEsIDExLCA3LCAxNTMsIDUsIDMsIDAsIDIsIDQzLCAyLCAxLCA0LCAwLCAzLCAyMiwgMTEsIDIyLCAxMCwgMzAsIDk4LCAyMSwgMTEsIDI1LCA3MSwgNTUsIDcsIDEsIDY1LCAwLCAxNiwgMywgMiwgMiwgMiwgMjYsIDQ1LCAyOCwgNCwgMjgsIDM2LCA3LCAyLCAyNywgMjgsIDUzLCAxMSwgMjEsIDExLCAxOCwgMTQsIDE3LCAxMTEsIDcyLCA5NTUsIDUyLCA3NiwgNDQsIDMzLCAyNCwgMjcsIDM1LCA0MiwgMzQsIDQsIDAsIDEzLCA0NywgMTUsIDMsIDIyLCAwLCAzOCwgMTcsIDIsIDI0LCAxMzMsIDQ2LCAzOSwgNywgMywgMSwgMywgMjEsIDIsIDYsIDIsIDEsIDIsIDQsIDQsIDAsIDMyLCA0LCAyODcsIDQ3LCAyMSwgMSwgMiwgMCwgMTg1LCA0NiwgODIsIDQ3LCAyMSwgMCwgNjAsIDQyLCA1MDIsIDYzLCAzMiwgMCwgNDQ5LCA1NiwgMTI4OCwgOTIwLCAxMDQsIDExMCwgMjk2MiwgMTA3MCwgMTMyNjYsIDU2OCwgOCwgMzAsIDExNCwgMjksIDE5LCA0NywgMTcsIDMsIDMyLCAyMCwgNiwgMTgsIDg4MSwgNjgsIDEyLCAwLCA2NywgMTIsIDE2NDgxLCAxLCAzMDcxLCAxMDYsIDYsIDEyLCA0LCA4LCA4LCA5LCA1OTkxLCA4NCwgMiwgNzAsIDIsIDEsIDMsIDAsIDMsIDEsIDMsIDMsIDIsIDExLCAyLCAwLCAyLCA2LCAyLCA2NCwgMiwgMywgMywgNywgMiwgNiwgMiwgMjcsIDIsIDMsIDIsIDQsIDIsIDAsIDQsIDYsIDIsIDMzOSwgMywgMjQsIDIsIDI0LCAyLCAzMCwgMiwgMjQsIDIsIDMwLCAyLCAyNCwgMiwgMzAsIDIsIDI0LCAyLCAzMCwgMiwgMjQsIDIsIDcsIDQxNDksIDE5NiwgMTM0MCwgMywgMiwgMjYsIDIsIDEsIDIsIDAsIDMsIDAsIDIsIDksIDIsIDMsIDIsIDAsIDIsIDAsIDcsIDAsIDUsIDAsIDIsIDAsIDIsIDAsIDIsIDIsIDIsIDEsIDIsIDAsIDMsIDAsIDIsIDAsIDIsIDAsIDIsIDAsIDIsIDAsIDIsIDEsIDIsIDAsIDMsIDMsIDIsIDYsIDIsIDMsIDIsIDMsIDIsIDAsIDIsIDksIDIsIDE2LCA2LCAyLCAyLCA0LCAyLCAxNiwgNDQyMSwgNDI3MTAsIDQyLCA0MTQ4LCAxMiwgMjIxLCAxNjM1NSwgNTQxXTt2YXIgYXN0cmFsSWRlbnRpZmllckNvZGVzPVs1MDksIDAsIDIyNywgMCwgMTUwLCA0LCAyOTQsIDksIDEzNjgsIDIsIDIsIDEsIDYsIDMsIDQxLCAyLCA1LCAwLCAxNjYsIDEsIDEzMDYsIDIsIDU0LCAxNCwgMzIsIDksIDE2LCAzLCA0NiwgMTAsIDU0LCA5LCA3LCAyLCAzNywgMTMsIDIsIDksIDUyLCAwLCAxMywgMiwgNDksIDEzLCAxNiwgOSwgODMsIDExLCAxNjgsIDExLCA2LCA5LCA4LCAyLCA1NywgMCwgMiwgNiwgMywgMSwgMywgMiwgMTAsIDAsIDExLCAxLCAzLCA2LCA0LCA0LCAzMTYsIDE5LCAxMywgOSwgMjE0LCA2LCAzLCA4LCAxMTIsIDE2LCAxNiwgOSwgODIsIDEyLCA5LCA5LCA1MzUsIDksIDIwODU1LCA5LCAxMzUsIDQsIDYwLCA2LCAyNiwgOSwgMTAxNiwgNDUsIDE3LCAzLCAxOTcyMywgMSwgNTMxOSwgNCwgNCwgNSwgOSwgNywgMywgNiwgMzEsIDMsIDE0OSwgMiwgMTQxOCwgNDksIDQzMDUsIDYsIDc5MjYxOCwgMjM5XTtmdW5jdGlvbiBpc0luQXN0cmFsU2V0KGNvZGUsIHNldCl7dmFyIHBvcz02NTUzNjtmb3IodmFyIGk9MDsgaSA8IHNldC5sZW5ndGg7IGkgKz0gMikge3BvcyArPSBzZXRbaV07aWYocG9zID4gY29kZSl7cmV0dXJuIGZhbHNlO31wb3MgKz0gc2V0W2kgKyAxXTtpZihwb3MgPj0gY29kZSl7cmV0dXJuIHRydWU7fX19ZnVuY3Rpb24gaXNJZGVudGlmaWVyU3RhcnQoY29kZSwgYXN0cmFsKXtpZihjb2RlIDwgNjUpe3JldHVybiBjb2RlID09PSAzNjt9aWYoY29kZSA8IDkxKXtyZXR1cm4gdHJ1ZTt9aWYoY29kZSA8IDk3KXtyZXR1cm4gY29kZSA9PT0gOTU7fWlmKGNvZGUgPCAxMjMpe3JldHVybiB0cnVlO31pZihjb2RlIDw9IDY1NTM1KXtyZXR1cm4gY29kZSA+PSAxNzAgJiYgbm9uQVNDSUlpZGVudGlmaWVyU3RhcnQudGVzdChTdHJpbmcuZnJvbUNoYXJDb2RlKGNvZGUpKTt9aWYoYXN0cmFsID09PSBmYWxzZSl7cmV0dXJuIGZhbHNlO31yZXR1cm4gaXNJbkFzdHJhbFNldChjb2RlLCBhc3RyYWxJZGVudGlmaWVyU3RhcnRDb2Rlcyk7fWZ1bmN0aW9uIGlzSWRlbnRpZmllckNoYXIoY29kZSwgYXN0cmFsKXtpZihjb2RlIDwgNDgpe3JldHVybiBjb2RlID09PSAzNjt9aWYoY29kZSA8IDU4KXtyZXR1cm4gdHJ1ZTt9aWYoY29kZSA8IDY1KXtyZXR1cm4gZmFsc2U7fWlmKGNvZGUgPCA5MSl7cmV0dXJuIHRydWU7fWlmKGNvZGUgPCA5Nyl7cmV0dXJuIGNvZGUgPT09IDk1O31pZihjb2RlIDwgMTIzKXtyZXR1cm4gdHJ1ZTt9aWYoY29kZSA8PSA2NTUzNSl7cmV0dXJuIGNvZGUgPj0gMTcwICYmIG5vbkFTQ0lJaWRlbnRpZmllci50ZXN0KFN0cmluZy5mcm9tQ2hhckNvZGUoY29kZSkpO31pZihhc3RyYWwgPT09IGZhbHNlKXtyZXR1cm4gZmFsc2U7fXJldHVybiBpc0luQXN0cmFsU2V0KGNvZGUsIGFzdHJhbElkZW50aWZpZXJTdGFydENvZGVzKSB8fCBpc0luQXN0cmFsU2V0KGNvZGUsIGFzdHJhbElkZW50aWZpZXJDb2Rlcyk7fX0sIHt9XSwgODpbZnVuY3Rpb24oX2RlcmVxXywgbW9kdWxlLCBleHBvcnRzKXtcInVzZSBzdHJpY3RcIjt2YXIgX2NsYXNzQ2FsbENoZWNrPWZ1bmN0aW9uIF9jbGFzc0NhbGxDaGVjayhpbnN0YW5jZSwgQ29uc3RydWN0b3Ipe2lmKCEoaW5zdGFuY2UgaW5zdGFuY2VvZiBDb25zdHJ1Y3Rvcikpe3Rocm93IG5ldyBUeXBlRXJyb3IoXCJDYW5ub3QgY2FsbCBhIGNsYXNzIGFzIGEgZnVuY3Rpb25cIik7fX07ZXhwb3J0cy5nZXRMaW5lSW5mbyA9IGdldExpbmVJbmZvO2V4cG9ydHMuX19lc01vZHVsZSA9IHRydWU7dmFyIFBhcnNlcj1fZGVyZXFfKFwiLi9zdGF0ZVwiKS5QYXJzZXI7dmFyIGxpbmVCcmVha0c9X2RlcmVxXyhcIi4vd2hpdGVzcGFjZVwiKS5saW5lQnJlYWtHO3ZhciBkZXByZWNhdGU9X2RlcmVxXyhcInV0aWxcIikuZGVwcmVjYXRlO3ZhciBQb3NpdGlvbj1leHBvcnRzLlBvc2l0aW9uID0gKGZ1bmN0aW9uKCl7ZnVuY3Rpb24gUG9zaXRpb24obGluZSwgY29sKXtfY2xhc3NDYWxsQ2hlY2sodGhpcywgUG9zaXRpb24pO3RoaXMubGluZSA9IGxpbmU7dGhpcy5jb2x1bW4gPSBjb2w7fVBvc2l0aW9uLnByb3RvdHlwZS5vZmZzZXQgPSBmdW5jdGlvbiBvZmZzZXQobil7cmV0dXJuIG5ldyBQb3NpdGlvbih0aGlzLmxpbmUsIHRoaXMuY29sdW1uICsgbik7fTtyZXR1cm4gUG9zaXRpb247fSkoKTt2YXIgU291cmNlTG9jYXRpb249ZXhwb3J0cy5Tb3VyY2VMb2NhdGlvbiA9IGZ1bmN0aW9uIFNvdXJjZUxvY2F0aW9uKHAsIHN0YXJ0LCBlbmQpe19jbGFzc0NhbGxDaGVjayh0aGlzLCBTb3VyY2VMb2NhdGlvbik7dGhpcy5zdGFydCA9IHN0YXJ0O3RoaXMuZW5kID0gZW5kO2lmKHAuc291cmNlRmlsZSAhPT0gbnVsbCl0aGlzLnNvdXJjZSA9IHAuc291cmNlRmlsZTt9O2Z1bmN0aW9uIGdldExpbmVJbmZvKGlucHV0LCBvZmZzZXQpe2Zvcih2YXIgbGluZT0xLCBjdXI9MDs7KSB7bGluZUJyZWFrRy5sYXN0SW5kZXggPSBjdXI7dmFyIG1hdGNoPWxpbmVCcmVha0cuZXhlYyhpbnB1dCk7aWYobWF0Y2ggJiYgbWF0Y2guaW5kZXggPCBvZmZzZXQpeysrbGluZTtjdXIgPSBtYXRjaC5pbmRleCArIG1hdGNoWzBdLmxlbmd0aDt9ZWxzZSB7cmV0dXJuIG5ldyBQb3NpdGlvbihsaW5lLCBvZmZzZXQgLSBjdXIpO319fXZhciBwcD1QYXJzZXIucHJvdG90eXBlO3BwLnJhaXNlID0gZnVuY3Rpb24ocG9zLCBtZXNzYWdlKXt2YXIgbG9jPWdldExpbmVJbmZvKHRoaXMuaW5wdXQsIHBvcyk7bWVzc2FnZSArPSBcIiAoXCIgKyBsb2MubGluZSArIFwiOlwiICsgbG9jLmNvbHVtbiArIFwiKVwiO3ZhciBlcnI9bmV3IFN5bnRheEVycm9yKG1lc3NhZ2UpO2Vyci5wb3MgPSBwb3M7ZXJyLmxvYyA9IGxvYztlcnIucmFpc2VkQXQgPSB0aGlzLnBvczt0aHJvdyBlcnI7fTtwcC5jdXJQb3NpdGlvbiA9IGZ1bmN0aW9uKCl7cmV0dXJuIG5ldyBQb3NpdGlvbih0aGlzLmN1ckxpbmUsIHRoaXMucG9zIC0gdGhpcy5saW5lU3RhcnQpO307cHAubWFya1Bvc2l0aW9uID0gZnVuY3Rpb24oKXtyZXR1cm4gdGhpcy5vcHRpb25zLmxvY2F0aW9ucz9bdGhpcy5zdGFydCwgdGhpcy5zdGFydExvY106dGhpcy5zdGFydDt9O30sIHtcIi4vc3RhdGVcIjoxMywgXCIuL3doaXRlc3BhY2VcIjoxOSwgdXRpbDo1fV0sIDk6W2Z1bmN0aW9uKF9kZXJlcV8sIG1vZHVsZSwgZXhwb3J0cyl7XCJ1c2Ugc3RyaWN0XCI7dmFyIHR0PV9kZXJlcV8oXCIuL3Rva2VudHlwZVwiKS50eXBlczt2YXIgUGFyc2VyPV9kZXJlcV8oXCIuL3N0YXRlXCIpLlBhcnNlcjt2YXIgcmVzZXJ2ZWRXb3Jkcz1fZGVyZXFfKFwiLi9pZGVudGlmaWVyXCIpLnJlc2VydmVkV29yZHM7dmFyIGhhcz1fZGVyZXFfKFwiLi91dGlsXCIpLmhhczt2YXIgcHA9UGFyc2VyLnByb3RvdHlwZTtwcC50b0Fzc2lnbmFibGUgPSBmdW5jdGlvbihub2RlLCBpc0JpbmRpbmcpe2lmKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2ICYmIG5vZGUpe3N3aXRjaChub2RlLnR5cGUpe2Nhc2UgXCJJZGVudGlmaWVyXCI6Y2FzZSBcIk9iamVjdFBhdHRlcm5cIjpjYXNlIFwiQXJyYXlQYXR0ZXJuXCI6Y2FzZSBcIkFzc2lnbm1lbnRQYXR0ZXJuXCI6YnJlYWs7Y2FzZSBcIk9iamVjdEV4cHJlc3Npb25cIjpub2RlLnR5cGUgPSBcIk9iamVjdFBhdHRlcm5cIjtmb3IodmFyIGk9MDsgaSA8IG5vZGUucHJvcGVydGllcy5sZW5ndGg7IGkrKykge3ZhciBwcm9wPW5vZGUucHJvcGVydGllc1tpXTtpZihwcm9wLmtpbmQgIT09IFwiaW5pdFwiKXRoaXMucmFpc2UocHJvcC5rZXkuc3RhcnQsIFwiT2JqZWN0IHBhdHRlcm4gY2FuJ3QgY29udGFpbiBnZXR0ZXIgb3Igc2V0dGVyXCIpO3RoaXMudG9Bc3NpZ25hYmxlKHByb3AudmFsdWUsIGlzQmluZGluZyk7fWJyZWFrO2Nhc2UgXCJBcnJheUV4cHJlc3Npb25cIjpub2RlLnR5cGUgPSBcIkFycmF5UGF0dGVyblwiO3RoaXMudG9Bc3NpZ25hYmxlTGlzdChub2RlLmVsZW1lbnRzLCBpc0JpbmRpbmcpO2JyZWFrO2Nhc2UgXCJBc3NpZ25tZW50RXhwcmVzc2lvblwiOmlmKG5vZGUub3BlcmF0b3IgPT09IFwiPVwiKXtub2RlLnR5cGUgPSBcIkFzc2lnbm1lbnRQYXR0ZXJuXCI7fWVsc2Uge3RoaXMucmFpc2Uobm9kZS5sZWZ0LmVuZCwgXCJPbmx5ICc9JyBvcGVyYXRvciBjYW4gYmUgdXNlZCBmb3Igc3BlY2lmeWluZyBkZWZhdWx0IHZhbHVlLlwiKTt9YnJlYWs7Y2FzZSBcIlBhcmVudGhlc2l6ZWRFeHByZXNzaW9uXCI6bm9kZS5leHByZXNzaW9uID0gdGhpcy50b0Fzc2lnbmFibGUobm9kZS5leHByZXNzaW9uLCBpc0JpbmRpbmcpO2JyZWFrO2Nhc2UgXCJNZW1iZXJFeHByZXNzaW9uXCI6aWYoIWlzQmluZGluZylicmVhaztkZWZhdWx0OnRoaXMucmFpc2Uobm9kZS5zdGFydCwgXCJBc3NpZ25pbmcgdG8gcnZhbHVlXCIpO319cmV0dXJuIG5vZGU7fTtwcC50b0Fzc2lnbmFibGVMaXN0ID0gZnVuY3Rpb24oZXhwckxpc3QsIGlzQmluZGluZyl7dmFyIGVuZD1leHByTGlzdC5sZW5ndGg7aWYoZW5kKXt2YXIgbGFzdD1leHByTGlzdFtlbmQgLSAxXTtpZihsYXN0ICYmIGxhc3QudHlwZSA9PSBcIlJlc3RFbGVtZW50XCIpey0tZW5kO31lbHNlIGlmKGxhc3QgJiYgbGFzdC50eXBlID09IFwiU3ByZWFkRWxlbWVudFwiKXtsYXN0LnR5cGUgPSBcIlJlc3RFbGVtZW50XCI7dmFyIGFyZz1sYXN0LmFyZ3VtZW50O3RoaXMudG9Bc3NpZ25hYmxlKGFyZywgaXNCaW5kaW5nKTtpZihhcmcudHlwZSAhPT0gXCJJZGVudGlmaWVyXCIgJiYgYXJnLnR5cGUgIT09IFwiTWVtYmVyRXhwcmVzc2lvblwiICYmIGFyZy50eXBlICE9PSBcIkFycmF5UGF0dGVyblwiKXRoaXMudW5leHBlY3RlZChhcmcuc3RhcnQpOy0tZW5kO319Zm9yKHZhciBpPTA7IGkgPCBlbmQ7IGkrKykge3ZhciBlbHQ9ZXhwckxpc3RbaV07aWYoZWx0KXRoaXMudG9Bc3NpZ25hYmxlKGVsdCwgaXNCaW5kaW5nKTt9cmV0dXJuIGV4cHJMaXN0O307cHAucGFyc2VTcHJlYWQgPSBmdW5jdGlvbihyZWZTaG9ydGhhbmREZWZhdWx0UG9zKXt2YXIgbm9kZT10aGlzLnN0YXJ0Tm9kZSgpO3RoaXMubmV4dCgpO25vZGUuYXJndW1lbnQgPSB0aGlzLnBhcnNlTWF5YmVBc3NpZ24ocmVmU2hvcnRoYW5kRGVmYXVsdFBvcyk7cmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIlNwcmVhZEVsZW1lbnRcIik7fTtwcC5wYXJzZVJlc3QgPSBmdW5jdGlvbigpe3ZhciBub2RlPXRoaXMuc3RhcnROb2RlKCk7dGhpcy5uZXh0KCk7bm9kZS5hcmd1bWVudCA9IHRoaXMudHlwZSA9PT0gdHQubmFtZSB8fCB0aGlzLnR5cGUgPT09IHR0LmJyYWNrZXRMP3RoaXMucGFyc2VCaW5kaW5nQXRvbSgpOnRoaXMudW5leHBlY3RlZCgpO3JldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJSZXN0RWxlbWVudFwiKTt9O3BwLnBhcnNlQmluZGluZ0F0b20gPSBmdW5jdGlvbigpe2lmKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA8IDYpcmV0dXJuIHRoaXMucGFyc2VJZGVudCgpO3N3aXRjaCh0aGlzLnR5cGUpe2Nhc2UgdHQubmFtZTpyZXR1cm4gdGhpcy5wYXJzZUlkZW50KCk7Y2FzZSB0dC5icmFja2V0TDp2YXIgbm9kZT10aGlzLnN0YXJ0Tm9kZSgpO3RoaXMubmV4dCgpO25vZGUuZWxlbWVudHMgPSB0aGlzLnBhcnNlQmluZGluZ0xpc3QodHQuYnJhY2tldFIsIHRydWUsIHRydWUpO3JldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJBcnJheVBhdHRlcm5cIik7Y2FzZSB0dC5icmFjZUw6cmV0dXJuIHRoaXMucGFyc2VPYmoodHJ1ZSk7ZGVmYXVsdDp0aGlzLnVuZXhwZWN0ZWQoKTt9fTtwcC5wYXJzZUJpbmRpbmdMaXN0ID0gZnVuY3Rpb24oY2xvc2UsIGFsbG93RW1wdHksIGFsbG93VHJhaWxpbmdDb21tYSl7dmFyIGVsdHM9W10sIGZpcnN0PXRydWU7d2hpbGUoIXRoaXMuZWF0KGNsb3NlKSkge2lmKGZpcnN0KWZpcnN0ID0gZmFsc2U7ZWxzZSB0aGlzLmV4cGVjdCh0dC5jb21tYSk7aWYoYWxsb3dFbXB0eSAmJiB0aGlzLnR5cGUgPT09IHR0LmNvbW1hKXtlbHRzLnB1c2gobnVsbCk7fWVsc2UgaWYoYWxsb3dUcmFpbGluZ0NvbW1hICYmIHRoaXMuYWZ0ZXJUcmFpbGluZ0NvbW1hKGNsb3NlKSl7YnJlYWs7fWVsc2UgaWYodGhpcy50eXBlID09PSB0dC5lbGxpcHNpcyl7dmFyIHJlc3Q9dGhpcy5wYXJzZVJlc3QoKTt0aGlzLnBhcnNlQmluZGluZ0xpc3RJdGVtKHJlc3QpO2VsdHMucHVzaChyZXN0KTt0aGlzLmV4cGVjdChjbG9zZSk7YnJlYWs7fWVsc2Uge3ZhciBlbGVtPXRoaXMucGFyc2VNYXliZURlZmF1bHQodGhpcy5zdGFydCwgdGhpcy5zdGFydExvYyk7dGhpcy5wYXJzZUJpbmRpbmdMaXN0SXRlbShlbGVtKTtlbHRzLnB1c2goZWxlbSk7fX1yZXR1cm4gZWx0czt9O3BwLnBhcnNlQmluZGluZ0xpc3RJdGVtID0gZnVuY3Rpb24ocGFyYW0pe3JldHVybiBwYXJhbTt9O3BwLnBhcnNlTWF5YmVEZWZhdWx0ID0gZnVuY3Rpb24oc3RhcnRQb3MsIHN0YXJ0TG9jLCBsZWZ0KXtpZihBcnJheS5pc0FycmF5KHN0YXJ0UG9zKSl7aWYodGhpcy5vcHRpb25zLmxvY2F0aW9ucyAmJiBub0NhbGxzID09PSB1bmRlZmluZWQpe2xlZnQgPSBzdGFydExvYztzdGFydExvYyA9IHN0YXJ0UG9zWzFdO3N0YXJ0UG9zID0gc3RhcnRQb3NbMF07fX1sZWZ0ID0gbGVmdCB8fCB0aGlzLnBhcnNlQmluZGluZ0F0b20oKTtpZighdGhpcy5lYXQodHQuZXEpKXJldHVybiBsZWZ0O3ZhciBub2RlPXRoaXMuc3RhcnROb2RlQXQoc3RhcnRQb3MsIHN0YXJ0TG9jKTtub2RlLm9wZXJhdG9yID0gXCI9XCI7bm9kZS5sZWZ0ID0gbGVmdDtub2RlLnJpZ2h0ID0gdGhpcy5wYXJzZU1heWJlQXNzaWduKCk7cmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkFzc2lnbm1lbnRQYXR0ZXJuXCIpO307cHAuY2hlY2tMVmFsID0gZnVuY3Rpb24oZXhwciwgaXNCaW5kaW5nLCBjaGVja0NsYXNoZXMpe3N3aXRjaChleHByLnR5cGUpe2Nhc2UgXCJJZGVudGlmaWVyXCI6aWYodGhpcy5zdHJpY3QgJiYgKHJlc2VydmVkV29yZHMuc3RyaWN0QmluZChleHByLm5hbWUpIHx8IHJlc2VydmVkV29yZHMuc3RyaWN0KGV4cHIubmFtZSkpKXRoaXMucmFpc2UoZXhwci5zdGFydCwgKGlzQmluZGluZz9cIkJpbmRpbmcgXCI6XCJBc3NpZ25pbmcgdG8gXCIpICsgZXhwci5uYW1lICsgXCIgaW4gc3RyaWN0IG1vZGVcIik7aWYoY2hlY2tDbGFzaGVzKXtpZihoYXMoY2hlY2tDbGFzaGVzLCBleHByLm5hbWUpKXRoaXMucmFpc2UoZXhwci5zdGFydCwgXCJBcmd1bWVudCBuYW1lIGNsYXNoIGluIHN0cmljdCBtb2RlXCIpO2NoZWNrQ2xhc2hlc1tleHByLm5hbWVdID0gdHJ1ZTt9YnJlYWs7Y2FzZSBcIk1lbWJlckV4cHJlc3Npb25cIjppZihpc0JpbmRpbmcpdGhpcy5yYWlzZShleHByLnN0YXJ0LCAoaXNCaW5kaW5nP1wiQmluZGluZ1wiOlwiQXNzaWduaW5nIHRvXCIpICsgXCIgbWVtYmVyIGV4cHJlc3Npb25cIik7YnJlYWs7Y2FzZSBcIk9iamVjdFBhdHRlcm5cIjpmb3IodmFyIGk9MDsgaSA8IGV4cHIucHJvcGVydGllcy5sZW5ndGg7IGkrKykge3RoaXMuY2hlY2tMVmFsKGV4cHIucHJvcGVydGllc1tpXS52YWx1ZSwgaXNCaW5kaW5nLCBjaGVja0NsYXNoZXMpO31icmVhaztjYXNlIFwiQXJyYXlQYXR0ZXJuXCI6Zm9yKHZhciBpPTA7IGkgPCBleHByLmVsZW1lbnRzLmxlbmd0aDsgaSsrKSB7dmFyIGVsZW09ZXhwci5lbGVtZW50c1tpXTtpZihlbGVtKXRoaXMuY2hlY2tMVmFsKGVsZW0sIGlzQmluZGluZywgY2hlY2tDbGFzaGVzKTt9YnJlYWs7Y2FzZSBcIkFzc2lnbm1lbnRQYXR0ZXJuXCI6dGhpcy5jaGVja0xWYWwoZXhwci5sZWZ0LCBpc0JpbmRpbmcsIGNoZWNrQ2xhc2hlcyk7YnJlYWs7Y2FzZSBcIlJlc3RFbGVtZW50XCI6dGhpcy5jaGVja0xWYWwoZXhwci5hcmd1bWVudCwgaXNCaW5kaW5nLCBjaGVja0NsYXNoZXMpO2JyZWFrO2Nhc2UgXCJQYXJlbnRoZXNpemVkRXhwcmVzc2lvblwiOnRoaXMuY2hlY2tMVmFsKGV4cHIuZXhwcmVzc2lvbiwgaXNCaW5kaW5nLCBjaGVja0NsYXNoZXMpO2JyZWFrO2RlZmF1bHQ6dGhpcy5yYWlzZShleHByLnN0YXJ0LCAoaXNCaW5kaW5nP1wiQmluZGluZ1wiOlwiQXNzaWduaW5nIHRvXCIpICsgXCIgcnZhbHVlXCIpO319O30sIHtcIi4vaWRlbnRpZmllclwiOjcsIFwiLi9zdGF0ZVwiOjEzLCBcIi4vdG9rZW50eXBlXCI6MTcsIFwiLi91dGlsXCI6MTh9XSwgMTA6W2Z1bmN0aW9uKF9kZXJlcV8sIG1vZHVsZSwgZXhwb3J0cyl7XCJ1c2Ugc3RyaWN0XCI7dmFyIF9jbGFzc0NhbGxDaGVjaz1mdW5jdGlvbiBfY2xhc3NDYWxsQ2hlY2soaW5zdGFuY2UsIENvbnN0cnVjdG9yKXtpZighKGluc3RhbmNlIGluc3RhbmNlb2YgQ29uc3RydWN0b3IpKXt0aHJvdyBuZXcgVHlwZUVycm9yKFwiQ2Fubm90IGNhbGwgYSBjbGFzcyBhcyBhIGZ1bmN0aW9uXCIpO319O2V4cG9ydHMuX19lc01vZHVsZSA9IHRydWU7dmFyIFBhcnNlcj1fZGVyZXFfKFwiLi9zdGF0ZVwiKS5QYXJzZXI7dmFyIFNvdXJjZUxvY2F0aW9uPV9kZXJlcV8oXCIuL2xvY2F0aW9uXCIpLlNvdXJjZUxvY2F0aW9uO3ZhciBwcD1QYXJzZXIucHJvdG90eXBlO3ZhciBOb2RlPWV4cG9ydHMuTm9kZSA9IGZ1bmN0aW9uIE5vZGUoKXtfY2xhc3NDYWxsQ2hlY2sodGhpcywgTm9kZSk7fTtwcC5zdGFydE5vZGUgPSBmdW5jdGlvbigpe3ZhciBub2RlPW5ldyBOb2RlKCk7bm9kZS5zdGFydCA9IHRoaXMuc3RhcnQ7aWYodGhpcy5vcHRpb25zLmxvY2F0aW9ucylub2RlLmxvYyA9IG5ldyBTb3VyY2VMb2NhdGlvbih0aGlzLCB0aGlzLnN0YXJ0TG9jKTtpZih0aGlzLm9wdGlvbnMuZGlyZWN0U291cmNlRmlsZSlub2RlLnNvdXJjZUZpbGUgPSB0aGlzLm9wdGlvbnMuZGlyZWN0U291cmNlRmlsZTtpZih0aGlzLm9wdGlvbnMucmFuZ2VzKW5vZGUucmFuZ2UgPSBbdGhpcy5zdGFydCwgMF07cmV0dXJuIG5vZGU7fTtwcC5zdGFydE5vZGVBdCA9IGZ1bmN0aW9uKHBvcywgbG9jKXt2YXIgbm9kZT1uZXcgTm9kZSgpO2lmKEFycmF5LmlzQXJyYXkocG9zKSl7aWYodGhpcy5vcHRpb25zLmxvY2F0aW9ucyAmJiBsb2MgPT09IHVuZGVmaW5lZCl7bG9jID0gcG9zWzFdO3BvcyA9IHBvc1swXTt9fW5vZGUuc3RhcnQgPSBwb3M7aWYodGhpcy5vcHRpb25zLmxvY2F0aW9ucylub2RlLmxvYyA9IG5ldyBTb3VyY2VMb2NhdGlvbih0aGlzLCBsb2MpO2lmKHRoaXMub3B0aW9ucy5kaXJlY3RTb3VyY2VGaWxlKW5vZGUuc291cmNlRmlsZSA9IHRoaXMub3B0aW9ucy5kaXJlY3RTb3VyY2VGaWxlO2lmKHRoaXMub3B0aW9ucy5yYW5nZXMpbm9kZS5yYW5nZSA9IFtwb3MsIDBdO3JldHVybiBub2RlO307cHAuZmluaXNoTm9kZSA9IGZ1bmN0aW9uKG5vZGUsIHR5cGUpe25vZGUudHlwZSA9IHR5cGU7bm9kZS5lbmQgPSB0aGlzLmxhc3RUb2tFbmQ7aWYodGhpcy5vcHRpb25zLmxvY2F0aW9ucylub2RlLmxvYy5lbmQgPSB0aGlzLmxhc3RUb2tFbmRMb2M7aWYodGhpcy5vcHRpb25zLnJhbmdlcylub2RlLnJhbmdlWzFdID0gdGhpcy5sYXN0VG9rRW5kO3JldHVybiBub2RlO307cHAuZmluaXNoTm9kZUF0ID0gZnVuY3Rpb24obm9kZSwgdHlwZSwgcG9zLCBsb2Mpe25vZGUudHlwZSA9IHR5cGU7aWYoQXJyYXkuaXNBcnJheShwb3MpKXtpZih0aGlzLm9wdGlvbnMubG9jYXRpb25zICYmIGxvYyA9PT0gdW5kZWZpbmVkKXtsb2MgPSBwb3NbMV07cG9zID0gcG9zWzBdO319bm9kZS5lbmQgPSBwb3M7aWYodGhpcy5vcHRpb25zLmxvY2F0aW9ucylub2RlLmxvYy5lbmQgPSBsb2M7aWYodGhpcy5vcHRpb25zLnJhbmdlcylub2RlLnJhbmdlWzFdID0gcG9zO3JldHVybiBub2RlO307fSwge1wiLi9sb2NhdGlvblwiOjgsIFwiLi9zdGF0ZVwiOjEzfV0sIDExOltmdW5jdGlvbihfZGVyZXFfLCBtb2R1bGUsIGV4cG9ydHMpe1widXNlIHN0cmljdFwiO2V4cG9ydHMuZ2V0T3B0aW9ucyA9IGdldE9wdGlvbnM7ZXhwb3J0cy5fX2VzTW9kdWxlID0gdHJ1ZTt2YXIgX3V0aWw9X2RlcmVxXyhcIi4vdXRpbFwiKTt2YXIgaGFzPV91dGlsLmhhczt2YXIgaXNBcnJheT1fdXRpbC5pc0FycmF5O3ZhciBTb3VyY2VMb2NhdGlvbj1fZGVyZXFfKFwiLi9sb2NhdGlvblwiKS5Tb3VyY2VMb2NhdGlvbjt2YXIgZGVmYXVsdE9wdGlvbnM9e2VjbWFWZXJzaW9uOjUsIHNvdXJjZVR5cGU6XCJzY3JpcHRcIiwgb25JbnNlcnRlZFNlbWljb2xvbjpudWxsLCBvblRyYWlsaW5nQ29tbWE6bnVsbCwgYWxsb3dSZXNlcnZlZDp0cnVlLCBhbGxvd1JldHVybk91dHNpZGVGdW5jdGlvbjpmYWxzZSwgYWxsb3dJbXBvcnRFeHBvcnRFdmVyeXdoZXJlOmZhbHNlLCBhbGxvd0hhc2hCYW5nOmZhbHNlLCBsb2NhdGlvbnM6ZmFsc2UsIG9uVG9rZW46bnVsbCwgb25Db21tZW50Om51bGwsIHJhbmdlczpmYWxzZSwgcHJvZ3JhbTpudWxsLCBzb3VyY2VGaWxlOm51bGwsIGRpcmVjdFNvdXJjZUZpbGU6bnVsbCwgcHJlc2VydmVQYXJlbnM6ZmFsc2UsIHBsdWdpbnM6e319O2V4cG9ydHMuZGVmYXVsdE9wdGlvbnMgPSBkZWZhdWx0T3B0aW9ucztmdW5jdGlvbiBnZXRPcHRpb25zKG9wdHMpe3ZhciBvcHRpb25zPXt9O2Zvcih2YXIgb3B0IGluIGRlZmF1bHRPcHRpb25zKSB7b3B0aW9uc1tvcHRdID0gb3B0cyAmJiBoYXMob3B0cywgb3B0KT9vcHRzW29wdF06ZGVmYXVsdE9wdGlvbnNbb3B0XTt9aWYoaXNBcnJheShvcHRpb25zLm9uVG9rZW4pKXsoZnVuY3Rpb24oKXt2YXIgdG9rZW5zPW9wdGlvbnMub25Ub2tlbjtvcHRpb25zLm9uVG9rZW4gPSBmdW5jdGlvbih0b2tlbil7cmV0dXJuIHRva2Vucy5wdXNoKHRva2VuKTt9O30pKCk7fWlmKGlzQXJyYXkob3B0aW9ucy5vbkNvbW1lbnQpKW9wdGlvbnMub25Db21tZW50ID0gcHVzaENvbW1lbnQob3B0aW9ucywgb3B0aW9ucy5vbkNvbW1lbnQpO3JldHVybiBvcHRpb25zO31mdW5jdGlvbiBwdXNoQ29tbWVudChvcHRpb25zLCBhcnJheSl7cmV0dXJuIGZ1bmN0aW9uKGJsb2NrLCB0ZXh0LCBzdGFydCwgZW5kLCBzdGFydExvYywgZW5kTG9jKXt2YXIgY29tbWVudD17dHlwZTpibG9jaz9cIkJsb2NrXCI6XCJMaW5lXCIsIHZhbHVlOnRleHQsIHN0YXJ0OnN0YXJ0LCBlbmQ6ZW5kfTtpZihvcHRpb25zLmxvY2F0aW9ucyljb21tZW50LmxvYyA9IG5ldyBTb3VyY2VMb2NhdGlvbih0aGlzLCBzdGFydExvYywgZW5kTG9jKTtpZihvcHRpb25zLnJhbmdlcyljb21tZW50LnJhbmdlID0gW3N0YXJ0LCBlbmRdO2FycmF5LnB1c2goY29tbWVudCk7fTt9fSwge1wiLi9sb2NhdGlvblwiOjgsIFwiLi91dGlsXCI6MTh9XSwgMTI6W2Z1bmN0aW9uKF9kZXJlcV8sIG1vZHVsZSwgZXhwb3J0cyl7XCJ1c2Ugc3RyaWN0XCI7dmFyIHR0PV9kZXJlcV8oXCIuL3Rva2VudHlwZVwiKS50eXBlczt2YXIgUGFyc2VyPV9kZXJlcV8oXCIuL3N0YXRlXCIpLlBhcnNlcjt2YXIgbGluZUJyZWFrPV9kZXJlcV8oXCIuL3doaXRlc3BhY2VcIikubGluZUJyZWFrO3ZhciBwcD1QYXJzZXIucHJvdG90eXBlO3BwLmlzVXNlU3RyaWN0ID0gZnVuY3Rpb24oc3RtdCl7cmV0dXJuIHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA1ICYmIHN0bXQudHlwZSA9PT0gXCJFeHByZXNzaW9uU3RhdGVtZW50XCIgJiYgc3RtdC5leHByZXNzaW9uLnR5cGUgPT09IFwiTGl0ZXJhbFwiICYmIHN0bXQuZXhwcmVzc2lvbi52YWx1ZSA9PT0gXCJ1c2Ugc3RyaWN0XCI7fTtwcC5lYXQgPSBmdW5jdGlvbih0eXBlKXtpZih0aGlzLnR5cGUgPT09IHR5cGUpe3RoaXMubmV4dCgpO3JldHVybiB0cnVlO31lbHNlIHtyZXR1cm4gZmFsc2U7fX07cHAuaXNDb250ZXh0dWFsID0gZnVuY3Rpb24obmFtZSl7cmV0dXJuIHRoaXMudHlwZSA9PT0gdHQubmFtZSAmJiB0aGlzLnZhbHVlID09PSBuYW1lO307cHAuZWF0Q29udGV4dHVhbCA9IGZ1bmN0aW9uKG5hbWUpe3JldHVybiB0aGlzLnZhbHVlID09PSBuYW1lICYmIHRoaXMuZWF0KHR0Lm5hbWUpO307cHAuZXhwZWN0Q29udGV4dHVhbCA9IGZ1bmN0aW9uKG5hbWUpe2lmKCF0aGlzLmVhdENvbnRleHR1YWwobmFtZSkpdGhpcy51bmV4cGVjdGVkKCk7fTtwcC5jYW5JbnNlcnRTZW1pY29sb24gPSBmdW5jdGlvbigpe3JldHVybiB0aGlzLnR5cGUgPT09IHR0LmVvZiB8fCB0aGlzLnR5cGUgPT09IHR0LmJyYWNlUiB8fCBsaW5lQnJlYWsudGVzdCh0aGlzLmlucHV0LnNsaWNlKHRoaXMubGFzdFRva0VuZCwgdGhpcy5zdGFydCkpO307cHAuaW5zZXJ0U2VtaWNvbG9uID0gZnVuY3Rpb24oKXtpZih0aGlzLmNhbkluc2VydFNlbWljb2xvbigpKXtpZih0aGlzLm9wdGlvbnMub25JbnNlcnRlZFNlbWljb2xvbil0aGlzLm9wdGlvbnMub25JbnNlcnRlZFNlbWljb2xvbih0aGlzLmxhc3RUb2tFbmQsIHRoaXMubGFzdFRva0VuZExvYyk7cmV0dXJuIHRydWU7fX07cHAuc2VtaWNvbG9uID0gZnVuY3Rpb24oKXtpZighdGhpcy5lYXQodHQuc2VtaSkgJiYgIXRoaXMuaW5zZXJ0U2VtaWNvbG9uKCkpdGhpcy51bmV4cGVjdGVkKCk7fTtwcC5hZnRlclRyYWlsaW5nQ29tbWEgPSBmdW5jdGlvbih0b2tUeXBlKXtpZih0aGlzLnR5cGUgPT0gdG9rVHlwZSl7aWYodGhpcy5vcHRpb25zLm9uVHJhaWxpbmdDb21tYSl0aGlzLm9wdGlvbnMub25UcmFpbGluZ0NvbW1hKHRoaXMubGFzdFRva1N0YXJ0LCB0aGlzLmxhc3RUb2tTdGFydExvYyk7dGhpcy5uZXh0KCk7cmV0dXJuIHRydWU7fX07cHAuZXhwZWN0ID0gZnVuY3Rpb24odHlwZSl7dGhpcy5lYXQodHlwZSkgfHwgdGhpcy51bmV4cGVjdGVkKCk7fTtwcC51bmV4cGVjdGVkID0gZnVuY3Rpb24ocG9zKXt0aGlzLnJhaXNlKHBvcyAhPSBudWxsP3Bvczp0aGlzLnN0YXJ0LCBcIlVuZXhwZWN0ZWQgdG9rZW5cIik7fTt9LCB7XCIuL3N0YXRlXCI6MTMsIFwiLi90b2tlbnR5cGVcIjoxNywgXCIuL3doaXRlc3BhY2VcIjoxOX1dLCAxMzpbZnVuY3Rpb24oX2RlcmVxXywgbW9kdWxlLCBleHBvcnRzKXtcInVzZSBzdHJpY3RcIjtleHBvcnRzLlBhcnNlciA9IFBhcnNlcjtleHBvcnRzLl9fZXNNb2R1bGUgPSB0cnVlO3ZhciBfaWRlbnRpZmllcj1fZGVyZXFfKFwiLi9pZGVudGlmaWVyXCIpO3ZhciByZXNlcnZlZFdvcmRzPV9pZGVudGlmaWVyLnJlc2VydmVkV29yZHM7dmFyIGtleXdvcmRzPV9pZGVudGlmaWVyLmtleXdvcmRzO3ZhciB0dD1fZGVyZXFfKFwiLi90b2tlbnR5cGVcIikudHlwZXM7dmFyIGxpbmVCcmVhaz1fZGVyZXFfKFwiLi93aGl0ZXNwYWNlXCIpLmxpbmVCcmVhaztmdW5jdGlvbiBQYXJzZXIob3B0aW9ucywgaW5wdXQsIHN0YXJ0UG9zKXt0aGlzLm9wdGlvbnMgPSBvcHRpb25zO3RoaXMuc291cmNlRmlsZSA9IHRoaXMub3B0aW9ucy5zb3VyY2VGaWxlIHx8IG51bGw7dGhpcy5pc0tleXdvcmQgPSBrZXl3b3Jkc1t0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNj82OjVdO3RoaXMuaXNSZXNlcnZlZFdvcmQgPSByZXNlcnZlZFdvcmRzW3RoaXMub3B0aW9ucy5lY21hVmVyc2lvbl07dGhpcy5pbnB1dCA9IGlucHV0O3RoaXMubG9hZFBsdWdpbnModGhpcy5vcHRpb25zLnBsdWdpbnMpO2lmKHN0YXJ0UG9zKXt0aGlzLnBvcyA9IHN0YXJ0UG9zO3RoaXMubGluZVN0YXJ0ID0gTWF0aC5tYXgoMCwgdGhpcy5pbnB1dC5sYXN0SW5kZXhPZihcIlxcblwiLCBzdGFydFBvcykpO3RoaXMuY3VyTGluZSA9IHRoaXMuaW5wdXQuc2xpY2UoMCwgdGhpcy5saW5lU3RhcnQpLnNwbGl0KGxpbmVCcmVhaykubGVuZ3RoO31lbHNlIHt0aGlzLnBvcyA9IHRoaXMubGluZVN0YXJ0ID0gMDt0aGlzLmN1ckxpbmUgPSAxO310aGlzLnR5cGUgPSB0dC5lb2Y7dGhpcy52YWx1ZSA9IG51bGw7dGhpcy5zdGFydCA9IHRoaXMuZW5kID0gdGhpcy5wb3M7dGhpcy5zdGFydExvYyA9IHRoaXMuZW5kTG9jID0gbnVsbDt0aGlzLmxhc3RUb2tFbmRMb2MgPSB0aGlzLmxhc3RUb2tTdGFydExvYyA9IG51bGw7dGhpcy5sYXN0VG9rU3RhcnQgPSB0aGlzLmxhc3RUb2tFbmQgPSB0aGlzLnBvczt0aGlzLmNvbnRleHQgPSB0aGlzLmluaXRpYWxDb250ZXh0KCk7dGhpcy5leHByQWxsb3dlZCA9IHRydWU7dGhpcy5zdHJpY3QgPSB0aGlzLmluTW9kdWxlID0gdGhpcy5vcHRpb25zLnNvdXJjZVR5cGUgPT09IFwibW9kdWxlXCI7dGhpcy5wb3RlbnRpYWxBcnJvd0F0ID0gLTE7dGhpcy5pbkZ1bmN0aW9uID0gdGhpcy5pbkdlbmVyYXRvciA9IGZhbHNlO3RoaXMubGFiZWxzID0gW107aWYodGhpcy5wb3MgPT09IDAgJiYgdGhpcy5vcHRpb25zLmFsbG93SGFzaEJhbmcgJiYgdGhpcy5pbnB1dC5zbGljZSgwLCAyKSA9PT0gXCIjIVwiKXRoaXMuc2tpcExpbmVDb21tZW50KDIpO31QYXJzZXIucHJvdG90eXBlLmV4dGVuZCA9IGZ1bmN0aW9uKG5hbWUsIGYpe3RoaXNbbmFtZV0gPSBmKHRoaXNbbmFtZV0pO307dmFyIHBsdWdpbnM9e307ZXhwb3J0cy5wbHVnaW5zID0gcGx1Z2lucztQYXJzZXIucHJvdG90eXBlLmxvYWRQbHVnaW5zID0gZnVuY3Rpb24ocGx1Z2lucyl7Zm9yKHZhciBfbmFtZSBpbiBwbHVnaW5zKSB7dmFyIHBsdWdpbj1leHBvcnRzLnBsdWdpbnNbX25hbWVdO2lmKCFwbHVnaW4pdGhyb3cgbmV3IEVycm9yKFwiUGx1Z2luICdcIiArIF9uYW1lICsgXCInIG5vdCBmb3VuZFwiKTtwbHVnaW4odGhpcywgcGx1Z2luc1tfbmFtZV0pO319O30sIHtcIi4vaWRlbnRpZmllclwiOjcsIFwiLi90b2tlbnR5cGVcIjoxNywgXCIuL3doaXRlc3BhY2VcIjoxOX1dLCAxNDpbZnVuY3Rpb24oX2RlcmVxXywgbW9kdWxlLCBleHBvcnRzKXtcInVzZSBzdHJpY3RcIjt2YXIgdHQ9X2RlcmVxXyhcIi4vdG9rZW50eXBlXCIpLnR5cGVzO3ZhciBQYXJzZXI9X2RlcmVxXyhcIi4vc3RhdGVcIikuUGFyc2VyO3ZhciBsaW5lQnJlYWs9X2RlcmVxXyhcIi4vd2hpdGVzcGFjZVwiKS5saW5lQnJlYWs7dmFyIHBwPVBhcnNlci5wcm90b3R5cGU7cHAucGFyc2VUb3BMZXZlbCA9IGZ1bmN0aW9uKG5vZGUpe3ZhciBmaXJzdD10cnVlO2lmKCFub2RlLmJvZHkpbm9kZS5ib2R5ID0gW107d2hpbGUodGhpcy50eXBlICE9PSB0dC5lb2YpIHt2YXIgc3RtdD10aGlzLnBhcnNlU3RhdGVtZW50KHRydWUsIHRydWUpO25vZGUuYm9keS5wdXNoKHN0bXQpO2lmKGZpcnN0ICYmIHRoaXMuaXNVc2VTdHJpY3Qoc3RtdCkpdGhpcy5zZXRTdHJpY3QodHJ1ZSk7Zmlyc3QgPSBmYWxzZTt9dGhpcy5uZXh0KCk7aWYodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYpe25vZGUuc291cmNlVHlwZSA9IHRoaXMub3B0aW9ucy5zb3VyY2VUeXBlO31yZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiUHJvZ3JhbVwiKTt9O3ZhciBsb29wTGFiZWw9e2tpbmQ6XCJsb29wXCJ9LCBzd2l0Y2hMYWJlbD17a2luZDpcInN3aXRjaFwifTtwcC5wYXJzZVN0YXRlbWVudCA9IGZ1bmN0aW9uKGRlY2xhcmF0aW9uLCB0b3BMZXZlbCl7dmFyIHN0YXJ0dHlwZT10aGlzLnR5cGUsIG5vZGU9dGhpcy5zdGFydE5vZGUoKTtzd2l0Y2goc3RhcnR0eXBlKXtjYXNlIHR0Ll9icmVhazpjYXNlIHR0Ll9jb250aW51ZTpyZXR1cm4gdGhpcy5wYXJzZUJyZWFrQ29udGludWVTdGF0ZW1lbnQobm9kZSwgc3RhcnR0eXBlLmtleXdvcmQpO2Nhc2UgdHQuX2RlYnVnZ2VyOnJldHVybiB0aGlzLnBhcnNlRGVidWdnZXJTdGF0ZW1lbnQobm9kZSk7Y2FzZSB0dC5fZG86cmV0dXJuIHRoaXMucGFyc2VEb1N0YXRlbWVudChub2RlKTtjYXNlIHR0Ll9mb3I6cmV0dXJuIHRoaXMucGFyc2VGb3JTdGF0ZW1lbnQobm9kZSk7Y2FzZSB0dC5fZnVuY3Rpb246aWYoIWRlY2xhcmF0aW9uICYmIHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KXRoaXMudW5leHBlY3RlZCgpO3JldHVybiB0aGlzLnBhcnNlRnVuY3Rpb25TdGF0ZW1lbnQobm9kZSk7Y2FzZSB0dC5fY2xhc3M6aWYoIWRlY2xhcmF0aW9uKXRoaXMudW5leHBlY3RlZCgpO3JldHVybiB0aGlzLnBhcnNlQ2xhc3Mobm9kZSwgdHJ1ZSk7Y2FzZSB0dC5faWY6cmV0dXJuIHRoaXMucGFyc2VJZlN0YXRlbWVudChub2RlKTtjYXNlIHR0Ll9yZXR1cm46cmV0dXJuIHRoaXMucGFyc2VSZXR1cm5TdGF0ZW1lbnQobm9kZSk7Y2FzZSB0dC5fc3dpdGNoOnJldHVybiB0aGlzLnBhcnNlU3dpdGNoU3RhdGVtZW50KG5vZGUpO2Nhc2UgdHQuX3Rocm93OnJldHVybiB0aGlzLnBhcnNlVGhyb3dTdGF0ZW1lbnQobm9kZSk7Y2FzZSB0dC5fdHJ5OnJldHVybiB0aGlzLnBhcnNlVHJ5U3RhdGVtZW50KG5vZGUpO2Nhc2UgdHQuX2xldDpjYXNlIHR0Ll9jb25zdDppZighZGVjbGFyYXRpb24pdGhpcy51bmV4cGVjdGVkKCk7Y2FzZSB0dC5fdmFyOnJldHVybiB0aGlzLnBhcnNlVmFyU3RhdGVtZW50KG5vZGUsIHN0YXJ0dHlwZSk7Y2FzZSB0dC5fd2hpbGU6cmV0dXJuIHRoaXMucGFyc2VXaGlsZVN0YXRlbWVudChub2RlKTtjYXNlIHR0Ll93aXRoOnJldHVybiB0aGlzLnBhcnNlV2l0aFN0YXRlbWVudChub2RlKTtjYXNlIHR0LmJyYWNlTDpyZXR1cm4gdGhpcy5wYXJzZUJsb2NrKCk7Y2FzZSB0dC5zZW1pOnJldHVybiB0aGlzLnBhcnNlRW1wdHlTdGF0ZW1lbnQobm9kZSk7Y2FzZSB0dC5fZXhwb3J0OmNhc2UgdHQuX2ltcG9ydDppZighdGhpcy5vcHRpb25zLmFsbG93SW1wb3J0RXhwb3J0RXZlcnl3aGVyZSl7aWYoIXRvcExldmVsKXRoaXMucmFpc2UodGhpcy5zdGFydCwgXCInaW1wb3J0JyBhbmQgJ2V4cG9ydCcgbWF5IG9ubHkgYXBwZWFyIGF0IHRoZSB0b3AgbGV2ZWxcIik7aWYoIXRoaXMuaW5Nb2R1bGUpdGhpcy5yYWlzZSh0aGlzLnN0YXJ0LCBcIidpbXBvcnQnIGFuZCAnZXhwb3J0JyBtYXkgYXBwZWFyIG9ubHkgd2l0aCAnc291cmNlVHlwZTogbW9kdWxlJ1wiKTt9cmV0dXJuIHN0YXJ0dHlwZSA9PT0gdHQuX2ltcG9ydD90aGlzLnBhcnNlSW1wb3J0KG5vZGUpOnRoaXMucGFyc2VFeHBvcnQobm9kZSk7ZGVmYXVsdDp2YXIgbWF5YmVOYW1lPXRoaXMudmFsdWUsIGV4cHI9dGhpcy5wYXJzZUV4cHJlc3Npb24oKTtpZihzdGFydHR5cGUgPT09IHR0Lm5hbWUgJiYgZXhwci50eXBlID09PSBcIklkZW50aWZpZXJcIiAmJiB0aGlzLmVhdCh0dC5jb2xvbikpcmV0dXJuIHRoaXMucGFyc2VMYWJlbGVkU3RhdGVtZW50KG5vZGUsIG1heWJlTmFtZSwgZXhwcik7ZWxzZSByZXR1cm4gdGhpcy5wYXJzZUV4cHJlc3Npb25TdGF0ZW1lbnQobm9kZSwgZXhwcik7fX07cHAucGFyc2VCcmVha0NvbnRpbnVlU3RhdGVtZW50ID0gZnVuY3Rpb24obm9kZSwga2V5d29yZCl7dmFyIGlzQnJlYWs9a2V5d29yZCA9PSBcImJyZWFrXCI7dGhpcy5uZXh0KCk7aWYodGhpcy5lYXQodHQuc2VtaSkgfHwgdGhpcy5pbnNlcnRTZW1pY29sb24oKSlub2RlLmxhYmVsID0gbnVsbDtlbHNlIGlmKHRoaXMudHlwZSAhPT0gdHQubmFtZSl0aGlzLnVuZXhwZWN0ZWQoKTtlbHNlIHtub2RlLmxhYmVsID0gdGhpcy5wYXJzZUlkZW50KCk7dGhpcy5zZW1pY29sb24oKTt9Zm9yKHZhciBpPTA7IGkgPCB0aGlzLmxhYmVscy5sZW5ndGg7ICsraSkge3ZhciBsYWI9dGhpcy5sYWJlbHNbaV07aWYobm9kZS5sYWJlbCA9PSBudWxsIHx8IGxhYi5uYW1lID09PSBub2RlLmxhYmVsLm5hbWUpe2lmKGxhYi5raW5kICE9IG51bGwgJiYgKGlzQnJlYWsgfHwgbGFiLmtpbmQgPT09IFwibG9vcFwiKSlicmVhaztpZihub2RlLmxhYmVsICYmIGlzQnJlYWspYnJlYWs7fX1pZihpID09PSB0aGlzLmxhYmVscy5sZW5ndGgpdGhpcy5yYWlzZShub2RlLnN0YXJ0LCBcIlVuc3ludGFjdGljIFwiICsga2V5d29yZCk7cmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBpc0JyZWFrP1wiQnJlYWtTdGF0ZW1lbnRcIjpcIkNvbnRpbnVlU3RhdGVtZW50XCIpO307cHAucGFyc2VEZWJ1Z2dlclN0YXRlbWVudCA9IGZ1bmN0aW9uKG5vZGUpe3RoaXMubmV4dCgpO3RoaXMuc2VtaWNvbG9uKCk7cmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkRlYnVnZ2VyU3RhdGVtZW50XCIpO307cHAucGFyc2VEb1N0YXRlbWVudCA9IGZ1bmN0aW9uKG5vZGUpe3RoaXMubmV4dCgpO3RoaXMubGFiZWxzLnB1c2gobG9vcExhYmVsKTtub2RlLmJvZHkgPSB0aGlzLnBhcnNlU3RhdGVtZW50KGZhbHNlKTt0aGlzLmxhYmVscy5wb3AoKTt0aGlzLmV4cGVjdCh0dC5fd2hpbGUpO25vZGUudGVzdCA9IHRoaXMucGFyc2VQYXJlbkV4cHJlc3Npb24oKTtpZih0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNil0aGlzLmVhdCh0dC5zZW1pKTtlbHNlIHRoaXMuc2VtaWNvbG9uKCk7cmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkRvV2hpbGVTdGF0ZW1lbnRcIik7fTtwcC5wYXJzZUZvclN0YXRlbWVudCA9IGZ1bmN0aW9uKG5vZGUpe3RoaXMubmV4dCgpO3RoaXMubGFiZWxzLnB1c2gobG9vcExhYmVsKTt0aGlzLmV4cGVjdCh0dC5wYXJlbkwpO2lmKHRoaXMudHlwZSA9PT0gdHQuc2VtaSlyZXR1cm4gdGhpcy5wYXJzZUZvcihub2RlLCBudWxsKTtpZih0aGlzLnR5cGUgPT09IHR0Ll92YXIgfHwgdGhpcy50eXBlID09PSB0dC5fbGV0IHx8IHRoaXMudHlwZSA9PT0gdHQuX2NvbnN0KXt2YXIgX2luaXQ9dGhpcy5zdGFydE5vZGUoKSwgdmFyS2luZD10aGlzLnR5cGU7dGhpcy5uZXh0KCk7dGhpcy5wYXJzZVZhcihfaW5pdCwgdHJ1ZSwgdmFyS2luZCk7dGhpcy5maW5pc2hOb2RlKF9pbml0LCBcIlZhcmlhYmxlRGVjbGFyYXRpb25cIik7aWYoKHRoaXMudHlwZSA9PT0gdHQuX2luIHx8IHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2ICYmIHRoaXMuaXNDb250ZXh0dWFsKFwib2ZcIikpICYmIF9pbml0LmRlY2xhcmF0aW9ucy5sZW5ndGggPT09IDEgJiYgISh2YXJLaW5kICE9PSB0dC5fdmFyICYmIF9pbml0LmRlY2xhcmF0aW9uc1swXS5pbml0KSlyZXR1cm4gdGhpcy5wYXJzZUZvckluKG5vZGUsIF9pbml0KTtyZXR1cm4gdGhpcy5wYXJzZUZvcihub2RlLCBfaW5pdCk7fXZhciByZWZTaG9ydGhhbmREZWZhdWx0UG9zPXtzdGFydDowfTt2YXIgaW5pdD10aGlzLnBhcnNlRXhwcmVzc2lvbih0cnVlLCByZWZTaG9ydGhhbmREZWZhdWx0UG9zKTtpZih0aGlzLnR5cGUgPT09IHR0Ll9pbiB8fCB0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNiAmJiB0aGlzLmlzQ29udGV4dHVhbChcIm9mXCIpKXt0aGlzLnRvQXNzaWduYWJsZShpbml0KTt0aGlzLmNoZWNrTFZhbChpbml0KTtyZXR1cm4gdGhpcy5wYXJzZUZvckluKG5vZGUsIGluaXQpO31lbHNlIGlmKHJlZlNob3J0aGFuZERlZmF1bHRQb3Muc3RhcnQpe3RoaXMudW5leHBlY3RlZChyZWZTaG9ydGhhbmREZWZhdWx0UG9zLnN0YXJ0KTt9cmV0dXJuIHRoaXMucGFyc2VGb3Iobm9kZSwgaW5pdCk7fTtwcC5wYXJzZUZ1bmN0aW9uU3RhdGVtZW50ID0gZnVuY3Rpb24obm9kZSl7dGhpcy5uZXh0KCk7cmV0dXJuIHRoaXMucGFyc2VGdW5jdGlvbihub2RlLCB0cnVlKTt9O3BwLnBhcnNlSWZTdGF0ZW1lbnQgPSBmdW5jdGlvbihub2RlKXt0aGlzLm5leHQoKTtub2RlLnRlc3QgPSB0aGlzLnBhcnNlUGFyZW5FeHByZXNzaW9uKCk7bm9kZS5jb25zZXF1ZW50ID0gdGhpcy5wYXJzZVN0YXRlbWVudChmYWxzZSk7bm9kZS5hbHRlcm5hdGUgPSB0aGlzLmVhdCh0dC5fZWxzZSk/dGhpcy5wYXJzZVN0YXRlbWVudChmYWxzZSk6bnVsbDtyZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiSWZTdGF0ZW1lbnRcIik7fTtwcC5wYXJzZVJldHVyblN0YXRlbWVudCA9IGZ1bmN0aW9uKG5vZGUpe2lmKCF0aGlzLmluRnVuY3Rpb24gJiYgIXRoaXMub3B0aW9ucy5hbGxvd1JldHVybk91dHNpZGVGdW5jdGlvbil0aGlzLnJhaXNlKHRoaXMuc3RhcnQsIFwiJ3JldHVybicgb3V0c2lkZSBvZiBmdW5jdGlvblwiKTt0aGlzLm5leHQoKTtpZih0aGlzLmVhdCh0dC5zZW1pKSB8fCB0aGlzLmluc2VydFNlbWljb2xvbigpKW5vZGUuYXJndW1lbnQgPSBudWxsO2Vsc2Uge25vZGUuYXJndW1lbnQgPSB0aGlzLnBhcnNlRXhwcmVzc2lvbigpO3RoaXMuc2VtaWNvbG9uKCk7fXJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJSZXR1cm5TdGF0ZW1lbnRcIik7fTtwcC5wYXJzZVN3aXRjaFN0YXRlbWVudCA9IGZ1bmN0aW9uKG5vZGUpe3RoaXMubmV4dCgpO25vZGUuZGlzY3JpbWluYW50ID0gdGhpcy5wYXJzZVBhcmVuRXhwcmVzc2lvbigpO25vZGUuY2FzZXMgPSBbXTt0aGlzLmV4cGVjdCh0dC5icmFjZUwpO3RoaXMubGFiZWxzLnB1c2goc3dpdGNoTGFiZWwpO2Zvcih2YXIgY3VyLCBzYXdEZWZhdWx0OyB0aGlzLnR5cGUgIT0gdHQuYnJhY2VSOykge2lmKHRoaXMudHlwZSA9PT0gdHQuX2Nhc2UgfHwgdGhpcy50eXBlID09PSB0dC5fZGVmYXVsdCl7dmFyIGlzQ2FzZT10aGlzLnR5cGUgPT09IHR0Ll9jYXNlO2lmKGN1cil0aGlzLmZpbmlzaE5vZGUoY3VyLCBcIlN3aXRjaENhc2VcIik7bm9kZS5jYXNlcy5wdXNoKGN1ciA9IHRoaXMuc3RhcnROb2RlKCkpO2N1ci5jb25zZXF1ZW50ID0gW107dGhpcy5uZXh0KCk7aWYoaXNDYXNlKXtjdXIudGVzdCA9IHRoaXMucGFyc2VFeHByZXNzaW9uKCk7fWVsc2Uge2lmKHNhd0RlZmF1bHQpdGhpcy5yYWlzZSh0aGlzLmxhc3RUb2tTdGFydCwgXCJNdWx0aXBsZSBkZWZhdWx0IGNsYXVzZXNcIik7c2F3RGVmYXVsdCA9IHRydWU7Y3VyLnRlc3QgPSBudWxsO310aGlzLmV4cGVjdCh0dC5jb2xvbik7fWVsc2Uge2lmKCFjdXIpdGhpcy51bmV4cGVjdGVkKCk7Y3VyLmNvbnNlcXVlbnQucHVzaCh0aGlzLnBhcnNlU3RhdGVtZW50KHRydWUpKTt9fWlmKGN1cil0aGlzLmZpbmlzaE5vZGUoY3VyLCBcIlN3aXRjaENhc2VcIik7dGhpcy5uZXh0KCk7dGhpcy5sYWJlbHMucG9wKCk7cmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIlN3aXRjaFN0YXRlbWVudFwiKTt9O3BwLnBhcnNlVGhyb3dTdGF0ZW1lbnQgPSBmdW5jdGlvbihub2RlKXt0aGlzLm5leHQoKTtpZihsaW5lQnJlYWsudGVzdCh0aGlzLmlucHV0LnNsaWNlKHRoaXMubGFzdFRva0VuZCwgdGhpcy5zdGFydCkpKXRoaXMucmFpc2UodGhpcy5sYXN0VG9rRW5kLCBcIklsbGVnYWwgbmV3bGluZSBhZnRlciB0aHJvd1wiKTtub2RlLmFyZ3VtZW50ID0gdGhpcy5wYXJzZUV4cHJlc3Npb24oKTt0aGlzLnNlbWljb2xvbigpO3JldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJUaHJvd1N0YXRlbWVudFwiKTt9O3ZhciBlbXB0eT1bXTtwcC5wYXJzZVRyeVN0YXRlbWVudCA9IGZ1bmN0aW9uKG5vZGUpe3RoaXMubmV4dCgpO25vZGUuYmxvY2sgPSB0aGlzLnBhcnNlQmxvY2soKTtub2RlLmhhbmRsZXIgPSBudWxsO2lmKHRoaXMudHlwZSA9PT0gdHQuX2NhdGNoKXt2YXIgY2xhdXNlPXRoaXMuc3RhcnROb2RlKCk7dGhpcy5uZXh0KCk7dGhpcy5leHBlY3QodHQucGFyZW5MKTtjbGF1c2UucGFyYW0gPSB0aGlzLnBhcnNlQmluZGluZ0F0b20oKTt0aGlzLmNoZWNrTFZhbChjbGF1c2UucGFyYW0sIHRydWUpO3RoaXMuZXhwZWN0KHR0LnBhcmVuUik7Y2xhdXNlLmd1YXJkID0gbnVsbDtjbGF1c2UuYm9keSA9IHRoaXMucGFyc2VCbG9jaygpO25vZGUuaGFuZGxlciA9IHRoaXMuZmluaXNoTm9kZShjbGF1c2UsIFwiQ2F0Y2hDbGF1c2VcIik7fW5vZGUuZ3VhcmRlZEhhbmRsZXJzID0gZW1wdHk7bm9kZS5maW5hbGl6ZXIgPSB0aGlzLmVhdCh0dC5fZmluYWxseSk/dGhpcy5wYXJzZUJsb2NrKCk6bnVsbDtpZighbm9kZS5oYW5kbGVyICYmICFub2RlLmZpbmFsaXplcil0aGlzLnJhaXNlKG5vZGUuc3RhcnQsIFwiTWlzc2luZyBjYXRjaCBvciBmaW5hbGx5IGNsYXVzZVwiKTtyZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiVHJ5U3RhdGVtZW50XCIpO307cHAucGFyc2VWYXJTdGF0ZW1lbnQgPSBmdW5jdGlvbihub2RlLCBraW5kKXt0aGlzLm5leHQoKTt0aGlzLnBhcnNlVmFyKG5vZGUsIGZhbHNlLCBraW5kKTt0aGlzLnNlbWljb2xvbigpO3JldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJWYXJpYWJsZURlY2xhcmF0aW9uXCIpO307cHAucGFyc2VXaGlsZVN0YXRlbWVudCA9IGZ1bmN0aW9uKG5vZGUpe3RoaXMubmV4dCgpO25vZGUudGVzdCA9IHRoaXMucGFyc2VQYXJlbkV4cHJlc3Npb24oKTt0aGlzLmxhYmVscy5wdXNoKGxvb3BMYWJlbCk7bm9kZS5ib2R5ID0gdGhpcy5wYXJzZVN0YXRlbWVudChmYWxzZSk7dGhpcy5sYWJlbHMucG9wKCk7cmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIldoaWxlU3RhdGVtZW50XCIpO307cHAucGFyc2VXaXRoU3RhdGVtZW50ID0gZnVuY3Rpb24obm9kZSl7aWYodGhpcy5zdHJpY3QpdGhpcy5yYWlzZSh0aGlzLnN0YXJ0LCBcIid3aXRoJyBpbiBzdHJpY3QgbW9kZVwiKTt0aGlzLm5leHQoKTtub2RlLm9iamVjdCA9IHRoaXMucGFyc2VQYXJlbkV4cHJlc3Npb24oKTtub2RlLmJvZHkgPSB0aGlzLnBhcnNlU3RhdGVtZW50KGZhbHNlKTtyZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiV2l0aFN0YXRlbWVudFwiKTt9O3BwLnBhcnNlRW1wdHlTdGF0ZW1lbnQgPSBmdW5jdGlvbihub2RlKXt0aGlzLm5leHQoKTtyZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiRW1wdHlTdGF0ZW1lbnRcIik7fTtwcC5wYXJzZUxhYmVsZWRTdGF0ZW1lbnQgPSBmdW5jdGlvbihub2RlLCBtYXliZU5hbWUsIGV4cHIpe2Zvcih2YXIgaT0wOyBpIDwgdGhpcy5sYWJlbHMubGVuZ3RoOyArK2kpIHtpZih0aGlzLmxhYmVsc1tpXS5uYW1lID09PSBtYXliZU5hbWUpdGhpcy5yYWlzZShleHByLnN0YXJ0LCBcIkxhYmVsICdcIiArIG1heWJlTmFtZSArIFwiJyBpcyBhbHJlYWR5IGRlY2xhcmVkXCIpO312YXIga2luZD10aGlzLnR5cGUuaXNMb29wP1wibG9vcFwiOnRoaXMudHlwZSA9PT0gdHQuX3N3aXRjaD9cInN3aXRjaFwiOm51bGw7dGhpcy5sYWJlbHMucHVzaCh7bmFtZTptYXliZU5hbWUsIGtpbmQ6a2luZH0pO25vZGUuYm9keSA9IHRoaXMucGFyc2VTdGF0ZW1lbnQodHJ1ZSk7dGhpcy5sYWJlbHMucG9wKCk7bm9kZS5sYWJlbCA9IGV4cHI7cmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkxhYmVsZWRTdGF0ZW1lbnRcIik7fTtwcC5wYXJzZUV4cHJlc3Npb25TdGF0ZW1lbnQgPSBmdW5jdGlvbihub2RlLCBleHByKXtub2RlLmV4cHJlc3Npb24gPSBleHByO3RoaXMuc2VtaWNvbG9uKCk7cmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkV4cHJlc3Npb25TdGF0ZW1lbnRcIik7fTtwcC5wYXJzZUJsb2NrID0gZnVuY3Rpb24oYWxsb3dTdHJpY3Qpe3ZhciBub2RlPXRoaXMuc3RhcnROb2RlKCksIGZpcnN0PXRydWUsIG9sZFN0cmljdD11bmRlZmluZWQ7bm9kZS5ib2R5ID0gW107dGhpcy5leHBlY3QodHQuYnJhY2VMKTt3aGlsZSghdGhpcy5lYXQodHQuYnJhY2VSKSkge3ZhciBzdG10PXRoaXMucGFyc2VTdGF0ZW1lbnQodHJ1ZSk7bm9kZS5ib2R5LnB1c2goc3RtdCk7aWYoZmlyc3QgJiYgYWxsb3dTdHJpY3QgJiYgdGhpcy5pc1VzZVN0cmljdChzdG10KSl7b2xkU3RyaWN0ID0gdGhpcy5zdHJpY3Q7dGhpcy5zZXRTdHJpY3QodGhpcy5zdHJpY3QgPSB0cnVlKTt9Zmlyc3QgPSBmYWxzZTt9aWYob2xkU3RyaWN0ID09PSBmYWxzZSl0aGlzLnNldFN0cmljdChmYWxzZSk7cmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkJsb2NrU3RhdGVtZW50XCIpO307cHAucGFyc2VGb3IgPSBmdW5jdGlvbihub2RlLCBpbml0KXtub2RlLmluaXQgPSBpbml0O3RoaXMuZXhwZWN0KHR0LnNlbWkpO25vZGUudGVzdCA9IHRoaXMudHlwZSA9PT0gdHQuc2VtaT9udWxsOnRoaXMucGFyc2VFeHByZXNzaW9uKCk7dGhpcy5leHBlY3QodHQuc2VtaSk7bm9kZS51cGRhdGUgPSB0aGlzLnR5cGUgPT09IHR0LnBhcmVuUj9udWxsOnRoaXMucGFyc2VFeHByZXNzaW9uKCk7dGhpcy5leHBlY3QodHQucGFyZW5SKTtub2RlLmJvZHkgPSB0aGlzLnBhcnNlU3RhdGVtZW50KGZhbHNlKTt0aGlzLmxhYmVscy5wb3AoKTtyZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiRm9yU3RhdGVtZW50XCIpO307cHAucGFyc2VGb3JJbiA9IGZ1bmN0aW9uKG5vZGUsIGluaXQpe3ZhciB0eXBlPXRoaXMudHlwZSA9PT0gdHQuX2luP1wiRm9ySW5TdGF0ZW1lbnRcIjpcIkZvck9mU3RhdGVtZW50XCI7dGhpcy5uZXh0KCk7bm9kZS5sZWZ0ID0gaW5pdDtub2RlLnJpZ2h0ID0gdGhpcy5wYXJzZUV4cHJlc3Npb24oKTt0aGlzLmV4cGVjdCh0dC5wYXJlblIpO25vZGUuYm9keSA9IHRoaXMucGFyc2VTdGF0ZW1lbnQoZmFsc2UpO3RoaXMubGFiZWxzLnBvcCgpO3JldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgdHlwZSk7fTtwcC5wYXJzZVZhciA9IGZ1bmN0aW9uKG5vZGUsIGlzRm9yLCBraW5kKXtub2RlLmRlY2xhcmF0aW9ucyA9IFtdO25vZGUua2luZCA9IGtpbmQua2V5d29yZDtmb3IoOzspIHt2YXIgZGVjbD10aGlzLnN0YXJ0Tm9kZSgpO3RoaXMucGFyc2VWYXJJZChkZWNsKTtpZih0aGlzLmVhdCh0dC5lcSkpe2RlY2wuaW5pdCA9IHRoaXMucGFyc2VNYXliZUFzc2lnbihpc0Zvcik7fWVsc2UgaWYoa2luZCA9PT0gdHQuX2NvbnN0ICYmICEodGhpcy50eXBlID09PSB0dC5faW4gfHwgdGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYgJiYgdGhpcy5pc0NvbnRleHR1YWwoXCJvZlwiKSkpe3RoaXMudW5leHBlY3RlZCgpO31lbHNlIGlmKGRlY2wuaWQudHlwZSAhPSBcIklkZW50aWZpZXJcIiAmJiAhKGlzRm9yICYmICh0aGlzLnR5cGUgPT09IHR0Ll9pbiB8fCB0aGlzLmlzQ29udGV4dHVhbChcIm9mXCIpKSkpe3RoaXMucmFpc2UodGhpcy5sYXN0VG9rRW5kLCBcIkNvbXBsZXggYmluZGluZyBwYXR0ZXJucyByZXF1aXJlIGFuIGluaXRpYWxpemF0aW9uIHZhbHVlXCIpO31lbHNlIHtkZWNsLmluaXQgPSBudWxsO31ub2RlLmRlY2xhcmF0aW9ucy5wdXNoKHRoaXMuZmluaXNoTm9kZShkZWNsLCBcIlZhcmlhYmxlRGVjbGFyYXRvclwiKSk7aWYoIXRoaXMuZWF0KHR0LmNvbW1hKSlicmVhazt9cmV0dXJuIG5vZGU7fTtwcC5wYXJzZVZhcklkID0gZnVuY3Rpb24oZGVjbCl7ZGVjbC5pZCA9IHRoaXMucGFyc2VCaW5kaW5nQXRvbSgpO3RoaXMuY2hlY2tMVmFsKGRlY2wuaWQsIHRydWUpO307cHAucGFyc2VGdW5jdGlvbiA9IGZ1bmN0aW9uKG5vZGUsIGlzU3RhdGVtZW50LCBhbGxvd0V4cHJlc3Npb25Cb2R5KXt0aGlzLmluaXRGdW5jdGlvbihub2RlKTtpZih0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNilub2RlLmdlbmVyYXRvciA9IHRoaXMuZWF0KHR0LnN0YXIpO2lmKGlzU3RhdGVtZW50IHx8IHRoaXMudHlwZSA9PT0gdHQubmFtZSlub2RlLmlkID0gdGhpcy5wYXJzZUlkZW50KCk7dGhpcy5wYXJzZUZ1bmN0aW9uUGFyYW1zKG5vZGUpO3RoaXMucGFyc2VGdW5jdGlvbkJvZHkobm9kZSwgYWxsb3dFeHByZXNzaW9uQm9keSk7cmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBpc1N0YXRlbWVudD9cIkZ1bmN0aW9uRGVjbGFyYXRpb25cIjpcIkZ1bmN0aW9uRXhwcmVzc2lvblwiKTt9O3BwLnBhcnNlRnVuY3Rpb25QYXJhbXMgPSBmdW5jdGlvbihub2RlKXt0aGlzLmV4cGVjdCh0dC5wYXJlbkwpO25vZGUucGFyYW1zID0gdGhpcy5wYXJzZUJpbmRpbmdMaXN0KHR0LnBhcmVuUiwgZmFsc2UsIGZhbHNlKTt9O3BwLnBhcnNlQ2xhc3MgPSBmdW5jdGlvbihub2RlLCBpc1N0YXRlbWVudCl7dGhpcy5uZXh0KCk7dGhpcy5wYXJzZUNsYXNzSWQobm9kZSwgaXNTdGF0ZW1lbnQpO3RoaXMucGFyc2VDbGFzc1N1cGVyKG5vZGUpO3ZhciBjbGFzc0JvZHk9dGhpcy5zdGFydE5vZGUoKTt2YXIgaGFkQ29uc3RydWN0b3I9ZmFsc2U7Y2xhc3NCb2R5LmJvZHkgPSBbXTt0aGlzLmV4cGVjdCh0dC5icmFjZUwpO3doaWxlKCF0aGlzLmVhdCh0dC5icmFjZVIpKSB7aWYodGhpcy5lYXQodHQuc2VtaSkpY29udGludWU7dmFyIG1ldGhvZD10aGlzLnN0YXJ0Tm9kZSgpO3ZhciBpc0dlbmVyYXRvcj10aGlzLmVhdCh0dC5zdGFyKTt2YXIgaXNNYXliZVN0YXRpYz10aGlzLnR5cGUgPT09IHR0Lm5hbWUgJiYgdGhpcy52YWx1ZSA9PT0gXCJzdGF0aWNcIjt0aGlzLnBhcnNlUHJvcGVydHlOYW1lKG1ldGhvZCk7bWV0aG9kW1wic3RhdGljXCJdID0gaXNNYXliZVN0YXRpYyAmJiB0aGlzLnR5cGUgIT09IHR0LnBhcmVuTDtpZihtZXRob2RbXCJzdGF0aWNcIl0pe2lmKGlzR2VuZXJhdG9yKXRoaXMudW5leHBlY3RlZCgpO2lzR2VuZXJhdG9yID0gdGhpcy5lYXQodHQuc3Rhcik7dGhpcy5wYXJzZVByb3BlcnR5TmFtZShtZXRob2QpO31tZXRob2Qua2luZCA9IFwibWV0aG9kXCI7aWYoIW1ldGhvZC5jb21wdXRlZCl7dmFyIGtleT1tZXRob2Qua2V5O3ZhciBpc0dldFNldD1mYWxzZTtpZighaXNHZW5lcmF0b3IgJiYga2V5LnR5cGUgPT09IFwiSWRlbnRpZmllclwiICYmIHRoaXMudHlwZSAhPT0gdHQucGFyZW5MICYmIChrZXkubmFtZSA9PT0gXCJnZXRcIiB8fCBrZXkubmFtZSA9PT0gXCJzZXRcIikpe2lzR2V0U2V0ID0gdHJ1ZTttZXRob2Qua2luZCA9IGtleS5uYW1lO2tleSA9IHRoaXMucGFyc2VQcm9wZXJ0eU5hbWUobWV0aG9kKTt9aWYoIW1ldGhvZFtcInN0YXRpY1wiXSAmJiAoa2V5LnR5cGUgPT09IFwiSWRlbnRpZmllclwiICYmIGtleS5uYW1lID09PSBcImNvbnN0cnVjdG9yXCIgfHwga2V5LnR5cGUgPT09IFwiTGl0ZXJhbFwiICYmIGtleS52YWx1ZSA9PT0gXCJjb25zdHJ1Y3RvclwiKSl7aWYoaGFkQ29uc3RydWN0b3IpdGhpcy5yYWlzZShrZXkuc3RhcnQsIFwiRHVwbGljYXRlIGNvbnN0cnVjdG9yIGluIHRoZSBzYW1lIGNsYXNzXCIpO2lmKGlzR2V0U2V0KXRoaXMucmFpc2Uoa2V5LnN0YXJ0LCBcIkNvbnN0cnVjdG9yIGNhbid0IGhhdmUgZ2V0L3NldCBtb2RpZmllclwiKTtpZihpc0dlbmVyYXRvcil0aGlzLnJhaXNlKGtleS5zdGFydCwgXCJDb25zdHJ1Y3RvciBjYW4ndCBiZSBhIGdlbmVyYXRvclwiKTttZXRob2Qua2luZCA9IFwiY29uc3RydWN0b3JcIjtoYWRDb25zdHJ1Y3RvciA9IHRydWU7fX10aGlzLnBhcnNlQ2xhc3NNZXRob2QoY2xhc3NCb2R5LCBtZXRob2QsIGlzR2VuZXJhdG9yKTt9bm9kZS5ib2R5ID0gdGhpcy5maW5pc2hOb2RlKGNsYXNzQm9keSwgXCJDbGFzc0JvZHlcIik7cmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBpc1N0YXRlbWVudD9cIkNsYXNzRGVjbGFyYXRpb25cIjpcIkNsYXNzRXhwcmVzc2lvblwiKTt9O3BwLnBhcnNlQ2xhc3NNZXRob2QgPSBmdW5jdGlvbihjbGFzc0JvZHksIG1ldGhvZCwgaXNHZW5lcmF0b3Ipe21ldGhvZC52YWx1ZSA9IHRoaXMucGFyc2VNZXRob2QoaXNHZW5lcmF0b3IpO2NsYXNzQm9keS5ib2R5LnB1c2godGhpcy5maW5pc2hOb2RlKG1ldGhvZCwgXCJNZXRob2REZWZpbml0aW9uXCIpKTt9O3BwLnBhcnNlQ2xhc3NJZCA9IGZ1bmN0aW9uKG5vZGUsIGlzU3RhdGVtZW50KXtub2RlLmlkID0gdGhpcy50eXBlID09PSB0dC5uYW1lP3RoaXMucGFyc2VJZGVudCgpOmlzU3RhdGVtZW50P3RoaXMudW5leHBlY3RlZCgpOm51bGw7fTtwcC5wYXJzZUNsYXNzU3VwZXIgPSBmdW5jdGlvbihub2RlKXtub2RlLnN1cGVyQ2xhc3MgPSB0aGlzLmVhdCh0dC5fZXh0ZW5kcyk/dGhpcy5wYXJzZUV4cHJTdWJzY3JpcHRzKCk6bnVsbDt9O3BwLnBhcnNlRXhwb3J0ID0gZnVuY3Rpb24obm9kZSl7dGhpcy5uZXh0KCk7aWYodGhpcy5lYXQodHQuc3Rhcikpe3RoaXMuZXhwZWN0Q29udGV4dHVhbChcImZyb21cIik7bm9kZS5zb3VyY2UgPSB0aGlzLnR5cGUgPT09IHR0LnN0cmluZz90aGlzLnBhcnNlRXhwckF0b20oKTp0aGlzLnVuZXhwZWN0ZWQoKTt0aGlzLnNlbWljb2xvbigpO3JldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJFeHBvcnRBbGxEZWNsYXJhdGlvblwiKTt9aWYodGhpcy5lYXQodHQuX2RlZmF1bHQpKXt2YXIgZXhwcj10aGlzLnBhcnNlTWF5YmVBc3NpZ24oKTt2YXIgbmVlZHNTZW1pPXRydWU7aWYoZXhwci50eXBlID09IFwiRnVuY3Rpb25FeHByZXNzaW9uXCIgfHwgZXhwci50eXBlID09IFwiQ2xhc3NFeHByZXNzaW9uXCIpe25lZWRzU2VtaSA9IGZhbHNlO2lmKGV4cHIuaWQpe2V4cHIudHlwZSA9IGV4cHIudHlwZSA9PSBcIkZ1bmN0aW9uRXhwcmVzc2lvblwiP1wiRnVuY3Rpb25EZWNsYXJhdGlvblwiOlwiQ2xhc3NEZWNsYXJhdGlvblwiO319bm9kZS5kZWNsYXJhdGlvbiA9IGV4cHI7aWYobmVlZHNTZW1pKXRoaXMuc2VtaWNvbG9uKCk7cmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkV4cG9ydERlZmF1bHREZWNsYXJhdGlvblwiKTt9aWYodGhpcy5zaG91bGRQYXJzZUV4cG9ydFN0YXRlbWVudCgpKXtub2RlLmRlY2xhcmF0aW9uID0gdGhpcy5wYXJzZVN0YXRlbWVudCh0cnVlKTtub2RlLnNwZWNpZmllcnMgPSBbXTtub2RlLnNvdXJjZSA9IG51bGw7fWVsc2Uge25vZGUuZGVjbGFyYXRpb24gPSBudWxsO25vZGUuc3BlY2lmaWVycyA9IHRoaXMucGFyc2VFeHBvcnRTcGVjaWZpZXJzKCk7aWYodGhpcy5lYXRDb250ZXh0dWFsKFwiZnJvbVwiKSl7bm9kZS5zb3VyY2UgPSB0aGlzLnR5cGUgPT09IHR0LnN0cmluZz90aGlzLnBhcnNlRXhwckF0b20oKTp0aGlzLnVuZXhwZWN0ZWQoKTt9ZWxzZSB7bm9kZS5zb3VyY2UgPSBudWxsO310aGlzLnNlbWljb2xvbigpO31yZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiRXhwb3J0TmFtZWREZWNsYXJhdGlvblwiKTt9O3BwLnNob3VsZFBhcnNlRXhwb3J0U3RhdGVtZW50ID0gZnVuY3Rpb24oKXtyZXR1cm4gdGhpcy50eXBlLmtleXdvcmQ7fTtwcC5wYXJzZUV4cG9ydFNwZWNpZmllcnMgPSBmdW5jdGlvbigpe3ZhciBub2Rlcz1bXSwgZmlyc3Q9dHJ1ZTt0aGlzLmV4cGVjdCh0dC5icmFjZUwpO3doaWxlKCF0aGlzLmVhdCh0dC5icmFjZVIpKSB7aWYoIWZpcnN0KXt0aGlzLmV4cGVjdCh0dC5jb21tYSk7aWYodGhpcy5hZnRlclRyYWlsaW5nQ29tbWEodHQuYnJhY2VSKSlicmVhazt9ZWxzZSBmaXJzdCA9IGZhbHNlO3ZhciBub2RlPXRoaXMuc3RhcnROb2RlKCk7bm9kZS5sb2NhbCA9IHRoaXMucGFyc2VJZGVudCh0aGlzLnR5cGUgPT09IHR0Ll9kZWZhdWx0KTtub2RlLmV4cG9ydGVkID0gdGhpcy5lYXRDb250ZXh0dWFsKFwiYXNcIik/dGhpcy5wYXJzZUlkZW50KHRydWUpOm5vZGUubG9jYWw7bm9kZXMucHVzaCh0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJFeHBvcnRTcGVjaWZpZXJcIikpO31yZXR1cm4gbm9kZXM7fTtwcC5wYXJzZUltcG9ydCA9IGZ1bmN0aW9uKG5vZGUpe3RoaXMubmV4dCgpO2lmKHRoaXMudHlwZSA9PT0gdHQuc3RyaW5nKXtub2RlLnNwZWNpZmllcnMgPSBlbXB0eTtub2RlLnNvdXJjZSA9IHRoaXMucGFyc2VFeHByQXRvbSgpO25vZGUua2luZCA9IFwiXCI7fWVsc2Uge25vZGUuc3BlY2lmaWVycyA9IHRoaXMucGFyc2VJbXBvcnRTcGVjaWZpZXJzKCk7dGhpcy5leHBlY3RDb250ZXh0dWFsKFwiZnJvbVwiKTtub2RlLnNvdXJjZSA9IHRoaXMudHlwZSA9PT0gdHQuc3RyaW5nP3RoaXMucGFyc2VFeHByQXRvbSgpOnRoaXMudW5leHBlY3RlZCgpO310aGlzLnNlbWljb2xvbigpO3JldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJJbXBvcnREZWNsYXJhdGlvblwiKTt9O3BwLnBhcnNlSW1wb3J0U3BlY2lmaWVycyA9IGZ1bmN0aW9uKCl7dmFyIG5vZGVzPVtdLCBmaXJzdD10cnVlO2lmKHRoaXMudHlwZSA9PT0gdHQubmFtZSl7dmFyIG5vZGU9dGhpcy5zdGFydE5vZGUoKTtub2RlLmxvY2FsID0gdGhpcy5wYXJzZUlkZW50KCk7dGhpcy5jaGVja0xWYWwobm9kZS5sb2NhbCwgdHJ1ZSk7bm9kZXMucHVzaCh0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJJbXBvcnREZWZhdWx0U3BlY2lmaWVyXCIpKTtpZighdGhpcy5lYXQodHQuY29tbWEpKXJldHVybiBub2Rlczt9aWYodGhpcy50eXBlID09PSB0dC5zdGFyKXt2YXIgbm9kZT10aGlzLnN0YXJ0Tm9kZSgpO3RoaXMubmV4dCgpO3RoaXMuZXhwZWN0Q29udGV4dHVhbChcImFzXCIpO25vZGUubG9jYWwgPSB0aGlzLnBhcnNlSWRlbnQoKTt0aGlzLmNoZWNrTFZhbChub2RlLmxvY2FsLCB0cnVlKTtub2Rlcy5wdXNoKHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkltcG9ydE5hbWVzcGFjZVNwZWNpZmllclwiKSk7cmV0dXJuIG5vZGVzO310aGlzLmV4cGVjdCh0dC5icmFjZUwpO3doaWxlKCF0aGlzLmVhdCh0dC5icmFjZVIpKSB7aWYoIWZpcnN0KXt0aGlzLmV4cGVjdCh0dC5jb21tYSk7aWYodGhpcy5hZnRlclRyYWlsaW5nQ29tbWEodHQuYnJhY2VSKSlicmVhazt9ZWxzZSBmaXJzdCA9IGZhbHNlO3ZhciBub2RlPXRoaXMuc3RhcnROb2RlKCk7bm9kZS5pbXBvcnRlZCA9IHRoaXMucGFyc2VJZGVudCh0cnVlKTtub2RlLmxvY2FsID0gdGhpcy5lYXRDb250ZXh0dWFsKFwiYXNcIik/dGhpcy5wYXJzZUlkZW50KCk6bm9kZS5pbXBvcnRlZDt0aGlzLmNoZWNrTFZhbChub2RlLmxvY2FsLCB0cnVlKTtub2Rlcy5wdXNoKHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkltcG9ydFNwZWNpZmllclwiKSk7fXJldHVybiBub2Rlczt9O30sIHtcIi4vc3RhdGVcIjoxMywgXCIuL3Rva2VudHlwZVwiOjE3LCBcIi4vd2hpdGVzcGFjZVwiOjE5fV0sIDE1OltmdW5jdGlvbihfZGVyZXFfLCBtb2R1bGUsIGV4cG9ydHMpe1widXNlIHN0cmljdFwiO3ZhciBfY2xhc3NDYWxsQ2hlY2s9ZnVuY3Rpb24gX2NsYXNzQ2FsbENoZWNrKGluc3RhbmNlLCBDb25zdHJ1Y3Rvcil7aWYoIShpbnN0YW5jZSBpbnN0YW5jZW9mIENvbnN0cnVjdG9yKSl7dGhyb3cgbmV3IFR5cGVFcnJvcihcIkNhbm5vdCBjYWxsIGEgY2xhc3MgYXMgYSBmdW5jdGlvblwiKTt9fTtleHBvcnRzLl9fZXNNb2R1bGUgPSB0cnVlO3ZhciBQYXJzZXI9X2RlcmVxXyhcIi4vc3RhdGVcIikuUGFyc2VyO3ZhciB0dD1fZGVyZXFfKFwiLi90b2tlbnR5cGVcIikudHlwZXM7dmFyIGxpbmVCcmVhaz1fZGVyZXFfKFwiLi93aGl0ZXNwYWNlXCIpLmxpbmVCcmVhazt2YXIgVG9rQ29udGV4dD1leHBvcnRzLlRva0NvbnRleHQgPSBmdW5jdGlvbiBUb2tDb250ZXh0KHRva2VuLCBpc0V4cHIsIHByZXNlcnZlU3BhY2UsIG92ZXJyaWRlKXtfY2xhc3NDYWxsQ2hlY2sodGhpcywgVG9rQ29udGV4dCk7dGhpcy50b2tlbiA9IHRva2VuO3RoaXMuaXNFeHByID0gaXNFeHByO3RoaXMucHJlc2VydmVTcGFjZSA9IHByZXNlcnZlU3BhY2U7dGhpcy5vdmVycmlkZSA9IG92ZXJyaWRlO307dmFyIHR5cGVzPXtiX3N0YXQ6bmV3IFRva0NvbnRleHQoXCJ7XCIsIGZhbHNlKSwgYl9leHByOm5ldyBUb2tDb250ZXh0KFwie1wiLCB0cnVlKSwgYl90bXBsOm5ldyBUb2tDb250ZXh0KFwiJHtcIiwgdHJ1ZSksIHBfc3RhdDpuZXcgVG9rQ29udGV4dChcIihcIiwgZmFsc2UpLCBwX2V4cHI6bmV3IFRva0NvbnRleHQoXCIoXCIsIHRydWUpLCBxX3RtcGw6bmV3IFRva0NvbnRleHQoXCJgXCIsIHRydWUsIHRydWUsIGZ1bmN0aW9uKHApe3JldHVybiBwLnJlYWRUbXBsVG9rZW4oKTt9KSwgZl9leHByOm5ldyBUb2tDb250ZXh0KFwiZnVuY3Rpb25cIiwgdHJ1ZSl9O2V4cG9ydHMudHlwZXMgPSB0eXBlczt2YXIgcHA9UGFyc2VyLnByb3RvdHlwZTtwcC5pbml0aWFsQ29udGV4dCA9IGZ1bmN0aW9uKCl7cmV0dXJuIFt0eXBlcy5iX3N0YXRdO307cHAuYnJhY2VJc0Jsb2NrID0gZnVuY3Rpb24ocHJldlR5cGUpe3ZhciBwYXJlbnQ9dW5kZWZpbmVkO2lmKHByZXZUeXBlID09PSB0dC5jb2xvbiAmJiAocGFyZW50ID0gdGhpcy5jdXJDb250ZXh0KCkpLnRva2VuID09IFwie1wiKXJldHVybiAhcGFyZW50LmlzRXhwcjtpZihwcmV2VHlwZSA9PT0gdHQuX3JldHVybilyZXR1cm4gbGluZUJyZWFrLnRlc3QodGhpcy5pbnB1dC5zbGljZSh0aGlzLmxhc3RUb2tFbmQsIHRoaXMuc3RhcnQpKTtpZihwcmV2VHlwZSA9PT0gdHQuX2Vsc2UgfHwgcHJldlR5cGUgPT09IHR0LnNlbWkgfHwgcHJldlR5cGUgPT09IHR0LmVvZilyZXR1cm4gdHJ1ZTtpZihwcmV2VHlwZSA9PSB0dC5icmFjZUwpcmV0dXJuIHRoaXMuY3VyQ29udGV4dCgpID09PSB0eXBlcy5iX3N0YXQ7cmV0dXJuICF0aGlzLmV4cHJBbGxvd2VkO307cHAudXBkYXRlQ29udGV4dCA9IGZ1bmN0aW9uKHByZXZUeXBlKXt2YXIgdXBkYXRlPXVuZGVmaW5lZCwgdHlwZT10aGlzLnR5cGU7aWYodHlwZS5rZXl3b3JkICYmIHByZXZUeXBlID09IHR0LmRvdCl0aGlzLmV4cHJBbGxvd2VkID0gZmFsc2U7ZWxzZSBpZih1cGRhdGUgPSB0eXBlLnVwZGF0ZUNvbnRleHQpdXBkYXRlLmNhbGwodGhpcywgcHJldlR5cGUpO2Vsc2UgdGhpcy5leHByQWxsb3dlZCA9IHR5cGUuYmVmb3JlRXhwcjt9O3R0LnBhcmVuUi51cGRhdGVDb250ZXh0ID0gdHQuYnJhY2VSLnVwZGF0ZUNvbnRleHQgPSBmdW5jdGlvbigpe2lmKHRoaXMuY29udGV4dC5sZW5ndGggPT0gMSl7dGhpcy5leHByQWxsb3dlZCA9IHRydWU7cmV0dXJuO312YXIgb3V0PXRoaXMuY29udGV4dC5wb3AoKTtpZihvdXQgPT09IHR5cGVzLmJfc3RhdCAmJiB0aGlzLmN1ckNvbnRleHQoKSA9PT0gdHlwZXMuZl9leHByKXt0aGlzLmNvbnRleHQucG9wKCk7dGhpcy5leHByQWxsb3dlZCA9IGZhbHNlO31lbHNlIGlmKG91dCA9PT0gdHlwZXMuYl90bXBsKXt0aGlzLmV4cHJBbGxvd2VkID0gdHJ1ZTt9ZWxzZSB7dGhpcy5leHByQWxsb3dlZCA9ICFvdXQuaXNFeHByO319O3R0LmJyYWNlTC51cGRhdGVDb250ZXh0ID0gZnVuY3Rpb24ocHJldlR5cGUpe3RoaXMuY29udGV4dC5wdXNoKHRoaXMuYnJhY2VJc0Jsb2NrKHByZXZUeXBlKT90eXBlcy5iX3N0YXQ6dHlwZXMuYl9leHByKTt0aGlzLmV4cHJBbGxvd2VkID0gdHJ1ZTt9O3R0LmRvbGxhckJyYWNlTC51cGRhdGVDb250ZXh0ID0gZnVuY3Rpb24oKXt0aGlzLmNvbnRleHQucHVzaCh0eXBlcy5iX3RtcGwpO3RoaXMuZXhwckFsbG93ZWQgPSB0cnVlO307dHQucGFyZW5MLnVwZGF0ZUNvbnRleHQgPSBmdW5jdGlvbihwcmV2VHlwZSl7dmFyIHN0YXRlbWVudFBhcmVucz1wcmV2VHlwZSA9PT0gdHQuX2lmIHx8IHByZXZUeXBlID09PSB0dC5fZm9yIHx8IHByZXZUeXBlID09PSB0dC5fd2l0aCB8fCBwcmV2VHlwZSA9PT0gdHQuX3doaWxlO3RoaXMuY29udGV4dC5wdXNoKHN0YXRlbWVudFBhcmVucz90eXBlcy5wX3N0YXQ6dHlwZXMucF9leHByKTt0aGlzLmV4cHJBbGxvd2VkID0gdHJ1ZTt9O3R0LmluY0RlYy51cGRhdGVDb250ZXh0ID0gZnVuY3Rpb24oKXt9O3R0Ll9mdW5jdGlvbi51cGRhdGVDb250ZXh0ID0gZnVuY3Rpb24oKXtpZih0aGlzLmN1ckNvbnRleHQoKSAhPT0gdHlwZXMuYl9zdGF0KXRoaXMuY29udGV4dC5wdXNoKHR5cGVzLmZfZXhwcik7dGhpcy5leHByQWxsb3dlZCA9IGZhbHNlO307dHQuYmFja1F1b3RlLnVwZGF0ZUNvbnRleHQgPSBmdW5jdGlvbigpe2lmKHRoaXMuY3VyQ29udGV4dCgpID09PSB0eXBlcy5xX3RtcGwpdGhpcy5jb250ZXh0LnBvcCgpO2Vsc2UgdGhpcy5jb250ZXh0LnB1c2godHlwZXMucV90bXBsKTt0aGlzLmV4cHJBbGxvd2VkID0gZmFsc2U7fTt9LCB7XCIuL3N0YXRlXCI6MTMsIFwiLi90b2tlbnR5cGVcIjoxNywgXCIuL3doaXRlc3BhY2VcIjoxOX1dLCAxNjpbZnVuY3Rpb24oX2RlcmVxXywgbW9kdWxlLCBleHBvcnRzKXtcInVzZSBzdHJpY3RcIjt2YXIgX2NsYXNzQ2FsbENoZWNrPWZ1bmN0aW9uIF9jbGFzc0NhbGxDaGVjayhpbnN0YW5jZSwgQ29uc3RydWN0b3Ipe2lmKCEoaW5zdGFuY2UgaW5zdGFuY2VvZiBDb25zdHJ1Y3Rvcikpe3Rocm93IG5ldyBUeXBlRXJyb3IoXCJDYW5ub3QgY2FsbCBhIGNsYXNzIGFzIGEgZnVuY3Rpb25cIik7fX07ZXhwb3J0cy5fX2VzTW9kdWxlID0gdHJ1ZTt2YXIgX2lkZW50aWZpZXI9X2RlcmVxXyhcIi4vaWRlbnRpZmllclwiKTt2YXIgaXNJZGVudGlmaWVyU3RhcnQ9X2lkZW50aWZpZXIuaXNJZGVudGlmaWVyU3RhcnQ7dmFyIGlzSWRlbnRpZmllckNoYXI9X2lkZW50aWZpZXIuaXNJZGVudGlmaWVyQ2hhcjt2YXIgX3Rva2VudHlwZT1fZGVyZXFfKFwiLi90b2tlbnR5cGVcIik7dmFyIHR0PV90b2tlbnR5cGUudHlwZXM7dmFyIGtleXdvcmRUeXBlcz1fdG9rZW50eXBlLmtleXdvcmRzO3ZhciBQYXJzZXI9X2RlcmVxXyhcIi4vc3RhdGVcIikuUGFyc2VyO3ZhciBTb3VyY2VMb2NhdGlvbj1fZGVyZXFfKFwiLi9sb2NhdGlvblwiKS5Tb3VyY2VMb2NhdGlvbjt2YXIgX3doaXRlc3BhY2U9X2RlcmVxXyhcIi4vd2hpdGVzcGFjZVwiKTt2YXIgbGluZUJyZWFrPV93aGl0ZXNwYWNlLmxpbmVCcmVhazt2YXIgbGluZUJyZWFrRz1fd2hpdGVzcGFjZS5saW5lQnJlYWtHO3ZhciBpc05ld0xpbmU9X3doaXRlc3BhY2UuaXNOZXdMaW5lO3ZhciBub25BU0NJSXdoaXRlc3BhY2U9X3doaXRlc3BhY2Uubm9uQVNDSUl3aGl0ZXNwYWNlO3ZhciBUb2tlbj1leHBvcnRzLlRva2VuID0gZnVuY3Rpb24gVG9rZW4ocCl7X2NsYXNzQ2FsbENoZWNrKHRoaXMsIFRva2VuKTt0aGlzLnR5cGUgPSBwLnR5cGU7dGhpcy52YWx1ZSA9IHAudmFsdWU7dGhpcy5zdGFydCA9IHAuc3RhcnQ7dGhpcy5lbmQgPSBwLmVuZDtpZihwLm9wdGlvbnMubG9jYXRpb25zKXRoaXMubG9jID0gbmV3IFNvdXJjZUxvY2F0aW9uKHAsIHAuc3RhcnRMb2MsIHAuZW5kTG9jKTtpZihwLm9wdGlvbnMucmFuZ2VzKXRoaXMucmFuZ2UgPSBbcC5zdGFydCwgcC5lbmRdO307dmFyIHBwPVBhcnNlci5wcm90b3R5cGU7dmFyIGlzUmhpbm89dHlwZW9mIFBhY2thZ2VzICE9PSBcInVuZGVmaW5lZFwiO3BwLm5leHQgPSBmdW5jdGlvbigpe2lmKHRoaXMub3B0aW9ucy5vblRva2VuKXRoaXMub3B0aW9ucy5vblRva2VuKG5ldyBUb2tlbih0aGlzKSk7dGhpcy5sYXN0VG9rRW5kID0gdGhpcy5lbmQ7dGhpcy5sYXN0VG9rU3RhcnQgPSB0aGlzLnN0YXJ0O3RoaXMubGFzdFRva0VuZExvYyA9IHRoaXMuZW5kTG9jO3RoaXMubGFzdFRva1N0YXJ0TG9jID0gdGhpcy5zdGFydExvYzt0aGlzLm5leHRUb2tlbigpO307cHAuZ2V0VG9rZW4gPSBmdW5jdGlvbigpe3RoaXMubmV4dCgpO3JldHVybiBuZXcgVG9rZW4odGhpcyk7fTtpZih0eXBlb2YgU3ltYm9sICE9PSBcInVuZGVmaW5lZFwiKXBwW1N5bWJvbC5pdGVyYXRvcl0gPSBmdW5jdGlvbigpe3ZhciBzZWxmPXRoaXM7cmV0dXJuIHtuZXh0OmZ1bmN0aW9uIG5leHQoKXt2YXIgdG9rZW49c2VsZi5nZXRUb2tlbigpO3JldHVybiB7ZG9uZTp0b2tlbi50eXBlID09PSB0dC5lb2YsIHZhbHVlOnRva2VufTt9fTt9O3BwLnNldFN0cmljdCA9IGZ1bmN0aW9uKHN0cmljdCl7dGhpcy5zdHJpY3QgPSBzdHJpY3Q7aWYodGhpcy50eXBlICE9PSB0dC5udW0gJiYgdGhpcy50eXBlICE9PSB0dC5zdHJpbmcpcmV0dXJuO3RoaXMucG9zID0gdGhpcy5zdGFydDtpZih0aGlzLm9wdGlvbnMubG9jYXRpb25zKXt3aGlsZSh0aGlzLnBvcyA8IHRoaXMubGluZVN0YXJ0KSB7dGhpcy5saW5lU3RhcnQgPSB0aGlzLmlucHV0Lmxhc3RJbmRleE9mKFwiXFxuXCIsIHRoaXMubGluZVN0YXJ0IC0gMikgKyAxOy0tdGhpcy5jdXJMaW5lO319dGhpcy5uZXh0VG9rZW4oKTt9O3BwLmN1ckNvbnRleHQgPSBmdW5jdGlvbigpe3JldHVybiB0aGlzLmNvbnRleHRbdGhpcy5jb250ZXh0Lmxlbmd0aCAtIDFdO307cHAubmV4dFRva2VuID0gZnVuY3Rpb24oKXt2YXIgY3VyQ29udGV4dD10aGlzLmN1ckNvbnRleHQoKTtpZighY3VyQ29udGV4dCB8fCAhY3VyQ29udGV4dC5wcmVzZXJ2ZVNwYWNlKXRoaXMuc2tpcFNwYWNlKCk7dGhpcy5zdGFydCA9IHRoaXMucG9zO2lmKHRoaXMub3B0aW9ucy5sb2NhdGlvbnMpdGhpcy5zdGFydExvYyA9IHRoaXMuY3VyUG9zaXRpb24oKTtpZih0aGlzLnBvcyA+PSB0aGlzLmlucHV0Lmxlbmd0aClyZXR1cm4gdGhpcy5maW5pc2hUb2tlbih0dC5lb2YpO2lmKGN1ckNvbnRleHQub3ZlcnJpZGUpcmV0dXJuIGN1ckNvbnRleHQub3ZlcnJpZGUodGhpcyk7ZWxzZSB0aGlzLnJlYWRUb2tlbih0aGlzLmZ1bGxDaGFyQ29kZUF0UG9zKCkpO307cHAucmVhZFRva2VuID0gZnVuY3Rpb24oY29kZSl7aWYoaXNJZGVudGlmaWVyU3RhcnQoY29kZSwgdGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYpIHx8IGNvZGUgPT09IDkyKXJldHVybiB0aGlzLnJlYWRXb3JkKCk7cmV0dXJuIHRoaXMuZ2V0VG9rZW5Gcm9tQ29kZShjb2RlKTt9O3BwLmZ1bGxDaGFyQ29kZUF0UG9zID0gZnVuY3Rpb24oKXt2YXIgY29kZT10aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MpO2lmKGNvZGUgPD0gNTUyOTUgfHwgY29kZSA+PSA1NzM0NClyZXR1cm4gY29kZTt2YXIgbmV4dD10aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAxKTtyZXR1cm4gKGNvZGUgPDwgMTApICsgbmV4dCAtIDU2NjEzODg4O307cHAuc2tpcEJsb2NrQ29tbWVudCA9IGZ1bmN0aW9uKCl7dmFyIHN0YXJ0TG9jPXRoaXMub3B0aW9ucy5vbkNvbW1lbnQgJiYgdGhpcy5vcHRpb25zLmxvY2F0aW9ucyAmJiB0aGlzLmN1clBvc2l0aW9uKCk7dmFyIHN0YXJ0PXRoaXMucG9zLCBlbmQ9dGhpcy5pbnB1dC5pbmRleE9mKFwiKi9cIiwgdGhpcy5wb3MgKz0gMik7aWYoZW5kID09PSAtMSl0aGlzLnJhaXNlKHRoaXMucG9zIC0gMiwgXCJVbnRlcm1pbmF0ZWQgY29tbWVudFwiKTt0aGlzLnBvcyA9IGVuZCArIDI7aWYodGhpcy5vcHRpb25zLmxvY2F0aW9ucyl7bGluZUJyZWFrRy5sYXN0SW5kZXggPSBzdGFydDt2YXIgbWF0Y2g9dW5kZWZpbmVkO3doaWxlKChtYXRjaCA9IGxpbmVCcmVha0cuZXhlYyh0aGlzLmlucHV0KSkgJiYgbWF0Y2guaW5kZXggPCB0aGlzLnBvcykgeysrdGhpcy5jdXJMaW5lO3RoaXMubGluZVN0YXJ0ID0gbWF0Y2guaW5kZXggKyBtYXRjaFswXS5sZW5ndGg7fX1pZih0aGlzLm9wdGlvbnMub25Db21tZW50KXRoaXMub3B0aW9ucy5vbkNvbW1lbnQodHJ1ZSwgdGhpcy5pbnB1dC5zbGljZShzdGFydCArIDIsIGVuZCksIHN0YXJ0LCB0aGlzLnBvcywgc3RhcnRMb2MsIHRoaXMub3B0aW9ucy5sb2NhdGlvbnMgJiYgdGhpcy5jdXJQb3NpdGlvbigpKTt9O3BwLnNraXBMaW5lQ29tbWVudCA9IGZ1bmN0aW9uKHN0YXJ0U2tpcCl7dmFyIHN0YXJ0PXRoaXMucG9zO3ZhciBzdGFydExvYz10aGlzLm9wdGlvbnMub25Db21tZW50ICYmIHRoaXMub3B0aW9ucy5sb2NhdGlvbnMgJiYgdGhpcy5jdXJQb3NpdGlvbigpO3ZhciBjaD10aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKz0gc3RhcnRTa2lwKTt3aGlsZSh0aGlzLnBvcyA8IHRoaXMuaW5wdXQubGVuZ3RoICYmIGNoICE9PSAxMCAmJiBjaCAhPT0gMTMgJiYgY2ggIT09IDgyMzIgJiYgY2ggIT09IDgyMzMpIHsrK3RoaXMucG9zO2NoID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zKTt9aWYodGhpcy5vcHRpb25zLm9uQ29tbWVudCl0aGlzLm9wdGlvbnMub25Db21tZW50KGZhbHNlLCB0aGlzLmlucHV0LnNsaWNlKHN0YXJ0ICsgc3RhcnRTa2lwLCB0aGlzLnBvcyksIHN0YXJ0LCB0aGlzLnBvcywgc3RhcnRMb2MsIHRoaXMub3B0aW9ucy5sb2NhdGlvbnMgJiYgdGhpcy5jdXJQb3NpdGlvbigpKTt9O3BwLnNraXBTcGFjZSA9IGZ1bmN0aW9uKCl7d2hpbGUodGhpcy5wb3MgPCB0aGlzLmlucHV0Lmxlbmd0aCkge3ZhciBjaD10aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MpO2lmKGNoID09PSAzMil7Kyt0aGlzLnBvczt9ZWxzZSBpZihjaCA9PT0gMTMpeysrdGhpcy5wb3M7dmFyIG5leHQ9dGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zKTtpZihuZXh0ID09PSAxMCl7Kyt0aGlzLnBvczt9aWYodGhpcy5vcHRpb25zLmxvY2F0aW9ucyl7Kyt0aGlzLmN1ckxpbmU7dGhpcy5saW5lU3RhcnQgPSB0aGlzLnBvczt9fWVsc2UgaWYoY2ggPT09IDEwIHx8IGNoID09PSA4MjMyIHx8IGNoID09PSA4MjMzKXsrK3RoaXMucG9zO2lmKHRoaXMub3B0aW9ucy5sb2NhdGlvbnMpeysrdGhpcy5jdXJMaW5lO3RoaXMubGluZVN0YXJ0ID0gdGhpcy5wb3M7fX1lbHNlIGlmKGNoID4gOCAmJiBjaCA8IDE0KXsrK3RoaXMucG9zO31lbHNlIGlmKGNoID09PSA0Nyl7dmFyIG5leHQ9dGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMSk7aWYobmV4dCA9PT0gNDIpe3RoaXMuc2tpcEJsb2NrQ29tbWVudCgpO31lbHNlIGlmKG5leHQgPT09IDQ3KXt0aGlzLnNraXBMaW5lQ29tbWVudCgyKTt9ZWxzZSBicmVhazt9ZWxzZSBpZihjaCA9PT0gMTYwKXsrK3RoaXMucG9zO31lbHNlIGlmKGNoID49IDU3NjAgJiYgbm9uQVNDSUl3aGl0ZXNwYWNlLnRlc3QoU3RyaW5nLmZyb21DaGFyQ29kZShjaCkpKXsrK3RoaXMucG9zO31lbHNlIHticmVhazt9fX07cHAuZmluaXNoVG9rZW4gPSBmdW5jdGlvbih0eXBlLCB2YWwpe3RoaXMuZW5kID0gdGhpcy5wb3M7aWYodGhpcy5vcHRpb25zLmxvY2F0aW9ucyl0aGlzLmVuZExvYyA9IHRoaXMuY3VyUG9zaXRpb24oKTt2YXIgcHJldlR5cGU9dGhpcy50eXBlO3RoaXMudHlwZSA9IHR5cGU7dGhpcy52YWx1ZSA9IHZhbDt0aGlzLnVwZGF0ZUNvbnRleHQocHJldlR5cGUpO307cHAucmVhZFRva2VuX2RvdCA9IGZ1bmN0aW9uKCl7dmFyIG5leHQ9dGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMSk7aWYobmV4dCA+PSA0OCAmJiBuZXh0IDw9IDU3KXJldHVybiB0aGlzLnJlYWROdW1iZXIodHJ1ZSk7dmFyIG5leHQyPXRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIDIpO2lmKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2ICYmIG5leHQgPT09IDQ2ICYmIG5leHQyID09PSA0Nil7dGhpcy5wb3MgKz0gMztyZXR1cm4gdGhpcy5maW5pc2hUb2tlbih0dC5lbGxpcHNpcyk7fWVsc2UgeysrdGhpcy5wb3M7cmV0dXJuIHRoaXMuZmluaXNoVG9rZW4odHQuZG90KTt9fTtwcC5yZWFkVG9rZW5fc2xhc2ggPSBmdW5jdGlvbigpe3ZhciBuZXh0PXRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIDEpO2lmKHRoaXMuZXhwckFsbG93ZWQpeysrdGhpcy5wb3M7cmV0dXJuIHRoaXMucmVhZFJlZ2V4cCgpO31pZihuZXh0ID09PSA2MSlyZXR1cm4gdGhpcy5maW5pc2hPcCh0dC5hc3NpZ24sIDIpO3JldHVybiB0aGlzLmZpbmlzaE9wKHR0LnNsYXNoLCAxKTt9O3BwLnJlYWRUb2tlbl9tdWx0X21vZHVsbyA9IGZ1bmN0aW9uKGNvZGUpe3ZhciBuZXh0PXRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIDEpO2lmKG5leHQgPT09IDYxKXJldHVybiB0aGlzLmZpbmlzaE9wKHR0LmFzc2lnbiwgMik7cmV0dXJuIHRoaXMuZmluaXNoT3AoY29kZSA9PT0gNDI/dHQuc3Rhcjp0dC5tb2R1bG8sIDEpO307cHAucmVhZFRva2VuX3BpcGVfYW1wID0gZnVuY3Rpb24oY29kZSl7dmFyIG5leHQ9dGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMSk7aWYobmV4dCA9PT0gY29kZSlyZXR1cm4gdGhpcy5maW5pc2hPcChjb2RlID09PSAxMjQ/dHQubG9naWNhbE9SOnR0LmxvZ2ljYWxBTkQsIDIpO2lmKG5leHQgPT09IDYxKXJldHVybiB0aGlzLmZpbmlzaE9wKHR0LmFzc2lnbiwgMik7cmV0dXJuIHRoaXMuZmluaXNoT3AoY29kZSA9PT0gMTI0P3R0LmJpdHdpc2VPUjp0dC5iaXR3aXNlQU5ELCAxKTt9O3BwLnJlYWRUb2tlbl9jYXJldCA9IGZ1bmN0aW9uKCl7dmFyIG5leHQ9dGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMSk7aWYobmV4dCA9PT0gNjEpcmV0dXJuIHRoaXMuZmluaXNoT3AodHQuYXNzaWduLCAyKTtyZXR1cm4gdGhpcy5maW5pc2hPcCh0dC5iaXR3aXNlWE9SLCAxKTt9O3BwLnJlYWRUb2tlbl9wbHVzX21pbiA9IGZ1bmN0aW9uKGNvZGUpe3ZhciBuZXh0PXRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIDEpO2lmKG5leHQgPT09IGNvZGUpe2lmKG5leHQgPT0gNDUgJiYgdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMikgPT0gNjIgJiYgbGluZUJyZWFrLnRlc3QodGhpcy5pbnB1dC5zbGljZSh0aGlzLmxhc3RUb2tFbmQsIHRoaXMucG9zKSkpe3RoaXMuc2tpcExpbmVDb21tZW50KDMpO3RoaXMuc2tpcFNwYWNlKCk7cmV0dXJuIHRoaXMubmV4dFRva2VuKCk7fXJldHVybiB0aGlzLmZpbmlzaE9wKHR0LmluY0RlYywgMik7fWlmKG5leHQgPT09IDYxKXJldHVybiB0aGlzLmZpbmlzaE9wKHR0LmFzc2lnbiwgMik7cmV0dXJuIHRoaXMuZmluaXNoT3AodHQucGx1c01pbiwgMSk7fTtwcC5yZWFkVG9rZW5fbHRfZ3QgPSBmdW5jdGlvbihjb2RlKXt2YXIgbmV4dD10aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAxKTt2YXIgc2l6ZT0xO2lmKG5leHQgPT09IGNvZGUpe3NpemUgPSBjb2RlID09PSA2MiAmJiB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAyKSA9PT0gNjI/MzoyO2lmKHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIHNpemUpID09PSA2MSlyZXR1cm4gdGhpcy5maW5pc2hPcCh0dC5hc3NpZ24sIHNpemUgKyAxKTtyZXR1cm4gdGhpcy5maW5pc2hPcCh0dC5iaXRTaGlmdCwgc2l6ZSk7fWlmKG5leHQgPT0gMzMgJiYgY29kZSA9PSA2MCAmJiB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAyKSA9PSA0NSAmJiB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAzKSA9PSA0NSl7aWYodGhpcy5pbk1vZHVsZSl0aGlzLnVuZXhwZWN0ZWQoKTt0aGlzLnNraXBMaW5lQ29tbWVudCg0KTt0aGlzLnNraXBTcGFjZSgpO3JldHVybiB0aGlzLm5leHRUb2tlbigpO31pZihuZXh0ID09PSA2MSlzaXplID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMikgPT09IDYxPzM6MjtyZXR1cm4gdGhpcy5maW5pc2hPcCh0dC5yZWxhdGlvbmFsLCBzaXplKTt9O3BwLnJlYWRUb2tlbl9lcV9leGNsID0gZnVuY3Rpb24oY29kZSl7dmFyIG5leHQ9dGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMSk7aWYobmV4dCA9PT0gNjEpcmV0dXJuIHRoaXMuZmluaXNoT3AodHQuZXF1YWxpdHksIHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIDIpID09PSA2MT8zOjIpO2lmKGNvZGUgPT09IDYxICYmIG5leHQgPT09IDYyICYmIHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KXt0aGlzLnBvcyArPSAyO3JldHVybiB0aGlzLmZpbmlzaFRva2VuKHR0LmFycm93KTt9cmV0dXJuIHRoaXMuZmluaXNoT3AoY29kZSA9PT0gNjE/dHQuZXE6dHQucHJlZml4LCAxKTt9O3BwLmdldFRva2VuRnJvbUNvZGUgPSBmdW5jdGlvbihjb2RlKXtzd2l0Y2goY29kZSl7Y2FzZSA0NjpyZXR1cm4gdGhpcy5yZWFkVG9rZW5fZG90KCk7Y2FzZSA0MDorK3RoaXMucG9zO3JldHVybiB0aGlzLmZpbmlzaFRva2VuKHR0LnBhcmVuTCk7Y2FzZSA0MTorK3RoaXMucG9zO3JldHVybiB0aGlzLmZpbmlzaFRva2VuKHR0LnBhcmVuUik7Y2FzZSA1OTorK3RoaXMucG9zO3JldHVybiB0aGlzLmZpbmlzaFRva2VuKHR0LnNlbWkpO2Nhc2UgNDQ6Kyt0aGlzLnBvcztyZXR1cm4gdGhpcy5maW5pc2hUb2tlbih0dC5jb21tYSk7Y2FzZSA5MTorK3RoaXMucG9zO3JldHVybiB0aGlzLmZpbmlzaFRva2VuKHR0LmJyYWNrZXRMKTtjYXNlIDkzOisrdGhpcy5wb3M7cmV0dXJuIHRoaXMuZmluaXNoVG9rZW4odHQuYnJhY2tldFIpO2Nhc2UgMTIzOisrdGhpcy5wb3M7cmV0dXJuIHRoaXMuZmluaXNoVG9rZW4odHQuYnJhY2VMKTtjYXNlIDEyNTorK3RoaXMucG9zO3JldHVybiB0aGlzLmZpbmlzaFRva2VuKHR0LmJyYWNlUik7Y2FzZSA1ODorK3RoaXMucG9zO3JldHVybiB0aGlzLmZpbmlzaFRva2VuKHR0LmNvbG9uKTtjYXNlIDYzOisrdGhpcy5wb3M7cmV0dXJuIHRoaXMuZmluaXNoVG9rZW4odHQucXVlc3Rpb24pO2Nhc2UgOTY6aWYodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uIDwgNilicmVhazsrK3RoaXMucG9zO3JldHVybiB0aGlzLmZpbmlzaFRva2VuKHR0LmJhY2tRdW90ZSk7Y2FzZSA0ODp2YXIgbmV4dD10aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAxKTtpZihuZXh0ID09PSAxMjAgfHwgbmV4dCA9PT0gODgpcmV0dXJuIHRoaXMucmVhZFJhZGl4TnVtYmVyKDE2KTtpZih0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNil7aWYobmV4dCA9PT0gMTExIHx8IG5leHQgPT09IDc5KXJldHVybiB0aGlzLnJlYWRSYWRpeE51bWJlcig4KTtpZihuZXh0ID09PSA5OCB8fCBuZXh0ID09PSA2NilyZXR1cm4gdGhpcy5yZWFkUmFkaXhOdW1iZXIoMik7fWNhc2UgNDk6Y2FzZSA1MDpjYXNlIDUxOmNhc2UgNTI6Y2FzZSA1MzpjYXNlIDU0OmNhc2UgNTU6Y2FzZSA1NjpjYXNlIDU3OnJldHVybiB0aGlzLnJlYWROdW1iZXIoZmFsc2UpO2Nhc2UgMzQ6Y2FzZSAzOTpyZXR1cm4gdGhpcy5yZWFkU3RyaW5nKGNvZGUpO2Nhc2UgNDc6cmV0dXJuIHRoaXMucmVhZFRva2VuX3NsYXNoKCk7Y2FzZSAzNzpjYXNlIDQyOnJldHVybiB0aGlzLnJlYWRUb2tlbl9tdWx0X21vZHVsbyhjb2RlKTtjYXNlIDEyNDpjYXNlIDM4OnJldHVybiB0aGlzLnJlYWRUb2tlbl9waXBlX2FtcChjb2RlKTtjYXNlIDk0OnJldHVybiB0aGlzLnJlYWRUb2tlbl9jYXJldCgpO2Nhc2UgNDM6Y2FzZSA0NTpyZXR1cm4gdGhpcy5yZWFkVG9rZW5fcGx1c19taW4oY29kZSk7Y2FzZSA2MDpjYXNlIDYyOnJldHVybiB0aGlzLnJlYWRUb2tlbl9sdF9ndChjb2RlKTtjYXNlIDYxOmNhc2UgMzM6cmV0dXJuIHRoaXMucmVhZFRva2VuX2VxX2V4Y2woY29kZSk7Y2FzZSAxMjY6cmV0dXJuIHRoaXMuZmluaXNoT3AodHQucHJlZml4LCAxKTt9dGhpcy5yYWlzZSh0aGlzLnBvcywgXCJVbmV4cGVjdGVkIGNoYXJhY3RlciAnXCIgKyBjb2RlUG9pbnRUb1N0cmluZyhjb2RlKSArIFwiJ1wiKTt9O3BwLmZpbmlzaE9wID0gZnVuY3Rpb24odHlwZSwgc2l6ZSl7dmFyIHN0cj10aGlzLmlucHV0LnNsaWNlKHRoaXMucG9zLCB0aGlzLnBvcyArIHNpemUpO3RoaXMucG9zICs9IHNpemU7cmV0dXJuIHRoaXMuZmluaXNoVG9rZW4odHlwZSwgc3RyKTt9O3ZhciByZWdleHBVbmljb2RlU3VwcG9ydD1mYWxzZTt0cnl7bmV3IFJlZ0V4cChcIu+/v1wiLCBcInVcIik7cmVnZXhwVW5pY29kZVN1cHBvcnQgPSB0cnVlO31jYXRjaChlKSB7fXBwLnJlYWRSZWdleHAgPSBmdW5jdGlvbigpe3ZhciBlc2NhcGVkPXVuZGVmaW5lZCwgaW5DbGFzcz11bmRlZmluZWQsIHN0YXJ0PXRoaXMucG9zO2Zvcig7Oykge2lmKHRoaXMucG9zID49IHRoaXMuaW5wdXQubGVuZ3RoKXRoaXMucmFpc2Uoc3RhcnQsIFwiVW50ZXJtaW5hdGVkIHJlZ3VsYXIgZXhwcmVzc2lvblwiKTt2YXIgY2g9dGhpcy5pbnB1dC5jaGFyQXQodGhpcy5wb3MpO2lmKGxpbmVCcmVhay50ZXN0KGNoKSl0aGlzLnJhaXNlKHN0YXJ0LCBcIlVudGVybWluYXRlZCByZWd1bGFyIGV4cHJlc3Npb25cIik7aWYoIWVzY2FwZWQpe2lmKGNoID09PSBcIltcIilpbkNsYXNzID0gdHJ1ZTtlbHNlIGlmKGNoID09PSBcIl1cIiAmJiBpbkNsYXNzKWluQ2xhc3MgPSBmYWxzZTtlbHNlIGlmKGNoID09PSBcIi9cIiAmJiAhaW5DbGFzcylicmVhaztlc2NhcGVkID0gY2ggPT09IFwiXFxcXFwiO31lbHNlIGVzY2FwZWQgPSBmYWxzZTsrK3RoaXMucG9zO312YXIgY29udGVudD10aGlzLmlucHV0LnNsaWNlKHN0YXJ0LCB0aGlzLnBvcyk7Kyt0aGlzLnBvczt2YXIgbW9kcz10aGlzLnJlYWRXb3JkMSgpO3ZhciB0bXA9Y29udGVudDtpZihtb2RzKXt2YXIgdmFsaWRGbGFncz0vXltnbXNpeV0qJC87aWYodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYpdmFsaWRGbGFncyA9IC9eW2dtc2l5dV0qJC87aWYoIXZhbGlkRmxhZ3MudGVzdChtb2RzKSl0aGlzLnJhaXNlKHN0YXJ0LCBcIkludmFsaWQgcmVndWxhciBleHByZXNzaW9uIGZsYWdcIik7aWYobW9kcy5pbmRleE9mKFwidVwiKSA+PSAwICYmICFyZWdleHBVbmljb2RlU3VwcG9ydCl7dG1wID0gdG1wLnJlcGxhY2UoL1xcXFx1KFthLWZBLUYwLTldezR9KXxcXFxcdVxceyhbMC05YS1mQS1GXSspXFx9fFtcXHVEODAwLVxcdURCRkZdW1xcdURDMDAtXFx1REZGRl0vZywgXCJ4XCIpO319dmFyIHZhbHVlPW51bGw7aWYoIWlzUmhpbm8pe3RyeXtuZXcgUmVnRXhwKHRtcCk7fWNhdGNoKGUpIHtpZihlIGluc3RhbmNlb2YgU3ludGF4RXJyb3IpdGhpcy5yYWlzZShzdGFydCwgXCJFcnJvciBwYXJzaW5nIHJlZ3VsYXIgZXhwcmVzc2lvbjogXCIgKyBlLm1lc3NhZ2UpO3RoaXMucmFpc2UoZSk7fXRyeXt2YWx1ZSA9IG5ldyBSZWdFeHAoY29udGVudCwgbW9kcyk7fWNhdGNoKGVycikge319cmV0dXJuIHRoaXMuZmluaXNoVG9rZW4odHQucmVnZXhwLCB7cGF0dGVybjpjb250ZW50LCBmbGFnczptb2RzLCB2YWx1ZTp2YWx1ZX0pO307cHAucmVhZEludCA9IGZ1bmN0aW9uKHJhZGl4LCBsZW4pe3ZhciBzdGFydD10aGlzLnBvcywgdG90YWw9MDtmb3IodmFyIGk9MCwgZT1sZW4gPT0gbnVsbD9JbmZpbml0eTpsZW47IGkgPCBlOyArK2kpIHt2YXIgY29kZT10aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MpLCB2YWw9dW5kZWZpbmVkO2lmKGNvZGUgPj0gOTcpdmFsID0gY29kZSAtIDk3ICsgMTA7ZWxzZSBpZihjb2RlID49IDY1KXZhbCA9IGNvZGUgLSA2NSArIDEwO2Vsc2UgaWYoY29kZSA+PSA0OCAmJiBjb2RlIDw9IDU3KXZhbCA9IGNvZGUgLSA0ODtlbHNlIHZhbCA9IEluZmluaXR5O2lmKHZhbCA+PSByYWRpeClicmVhazsrK3RoaXMucG9zO3RvdGFsID0gdG90YWwgKiByYWRpeCArIHZhbDt9aWYodGhpcy5wb3MgPT09IHN0YXJ0IHx8IGxlbiAhPSBudWxsICYmIHRoaXMucG9zIC0gc3RhcnQgIT09IGxlbilyZXR1cm4gbnVsbDtyZXR1cm4gdG90YWw7fTtwcC5yZWFkUmFkaXhOdW1iZXIgPSBmdW5jdGlvbihyYWRpeCl7dGhpcy5wb3MgKz0gMjt2YXIgdmFsPXRoaXMucmVhZEludChyYWRpeCk7aWYodmFsID09IG51bGwpdGhpcy5yYWlzZSh0aGlzLnN0YXJ0ICsgMiwgXCJFeHBlY3RlZCBudW1iZXIgaW4gcmFkaXggXCIgKyByYWRpeCk7aWYoaXNJZGVudGlmaWVyU3RhcnQodGhpcy5mdWxsQ2hhckNvZGVBdFBvcygpKSl0aGlzLnJhaXNlKHRoaXMucG9zLCBcIklkZW50aWZpZXIgZGlyZWN0bHkgYWZ0ZXIgbnVtYmVyXCIpO3JldHVybiB0aGlzLmZpbmlzaFRva2VuKHR0Lm51bSwgdmFsKTt9O3BwLnJlYWROdW1iZXIgPSBmdW5jdGlvbihzdGFydHNXaXRoRG90KXt2YXIgc3RhcnQ9dGhpcy5wb3MsIGlzRmxvYXQ9ZmFsc2UsIG9jdGFsPXRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcykgPT09IDQ4O2lmKCFzdGFydHNXaXRoRG90ICYmIHRoaXMucmVhZEludCgxMCkgPT09IG51bGwpdGhpcy5yYWlzZShzdGFydCwgXCJJbnZhbGlkIG51bWJlclwiKTtpZih0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MpID09PSA0Nil7Kyt0aGlzLnBvczt0aGlzLnJlYWRJbnQoMTApO2lzRmxvYXQgPSB0cnVlO312YXIgbmV4dD10aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MpO2lmKG5leHQgPT09IDY5IHx8IG5leHQgPT09IDEwMSl7bmV4dCA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCgrK3RoaXMucG9zKTtpZihuZXh0ID09PSA0MyB8fCBuZXh0ID09PSA0NSkrK3RoaXMucG9zO2lmKHRoaXMucmVhZEludCgxMCkgPT09IG51bGwpdGhpcy5yYWlzZShzdGFydCwgXCJJbnZhbGlkIG51bWJlclwiKTtpc0Zsb2F0ID0gdHJ1ZTt9aWYoaXNJZGVudGlmaWVyU3RhcnQodGhpcy5mdWxsQ2hhckNvZGVBdFBvcygpKSl0aGlzLnJhaXNlKHRoaXMucG9zLCBcIklkZW50aWZpZXIgZGlyZWN0bHkgYWZ0ZXIgbnVtYmVyXCIpO3ZhciBzdHI9dGhpcy5pbnB1dC5zbGljZShzdGFydCwgdGhpcy5wb3MpLCB2YWw9dW5kZWZpbmVkO2lmKGlzRmxvYXQpdmFsID0gcGFyc2VGbG9hdChzdHIpO2Vsc2UgaWYoIW9jdGFsIHx8IHN0ci5sZW5ndGggPT09IDEpdmFsID0gcGFyc2VJbnQoc3RyLCAxMCk7ZWxzZSBpZigvWzg5XS8udGVzdChzdHIpIHx8IHRoaXMuc3RyaWN0KXRoaXMucmFpc2Uoc3RhcnQsIFwiSW52YWxpZCBudW1iZXJcIik7ZWxzZSB2YWwgPSBwYXJzZUludChzdHIsIDgpO3JldHVybiB0aGlzLmZpbmlzaFRva2VuKHR0Lm51bSwgdmFsKTt9O3BwLnJlYWRDb2RlUG9pbnQgPSBmdW5jdGlvbigpe3ZhciBjaD10aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MpLCBjb2RlPXVuZGVmaW5lZDtpZihjaCA9PT0gMTIzKXtpZih0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPCA2KXRoaXMudW5leHBlY3RlZCgpOysrdGhpcy5wb3M7Y29kZSA9IHRoaXMucmVhZEhleENoYXIodGhpcy5pbnB1dC5pbmRleE9mKFwifVwiLCB0aGlzLnBvcykgLSB0aGlzLnBvcyk7Kyt0aGlzLnBvcztpZihjb2RlID4gMTExNDExMSl0aGlzLnVuZXhwZWN0ZWQoKTt9ZWxzZSB7Y29kZSA9IHRoaXMucmVhZEhleENoYXIoNCk7fXJldHVybiBjb2RlO307ZnVuY3Rpb24gY29kZVBvaW50VG9TdHJpbmcoY29kZSl7aWYoY29kZSA8PSA2NTUzNSl7cmV0dXJuIFN0cmluZy5mcm9tQ2hhckNvZGUoY29kZSk7fXJldHVybiBTdHJpbmcuZnJvbUNoYXJDb2RlKChjb2RlIC0gNjU1MzYgPj4gMTApICsgNTUyOTYsIChjb2RlIC0gNjU1MzYgJiAxMDIzKSArIDU2MzIwKTt9cHAucmVhZFN0cmluZyA9IGZ1bmN0aW9uKHF1b3RlKXt2YXIgb3V0PVwiXCIsIGNodW5rU3RhcnQ9Kyt0aGlzLnBvcztmb3IoOzspIHtpZih0aGlzLnBvcyA+PSB0aGlzLmlucHV0Lmxlbmd0aCl0aGlzLnJhaXNlKHRoaXMuc3RhcnQsIFwiVW50ZXJtaW5hdGVkIHN0cmluZyBjb25zdGFudFwiKTt2YXIgY2g9dGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zKTtpZihjaCA9PT0gcXVvdGUpYnJlYWs7aWYoY2ggPT09IDkyKXtvdXQgKz0gdGhpcy5pbnB1dC5zbGljZShjaHVua1N0YXJ0LCB0aGlzLnBvcyk7b3V0ICs9IHRoaXMucmVhZEVzY2FwZWRDaGFyKCk7Y2h1bmtTdGFydCA9IHRoaXMucG9zO31lbHNlIHtpZihpc05ld0xpbmUoY2gpKXRoaXMucmFpc2UodGhpcy5zdGFydCwgXCJVbnRlcm1pbmF0ZWQgc3RyaW5nIGNvbnN0YW50XCIpOysrdGhpcy5wb3M7fX1vdXQgKz0gdGhpcy5pbnB1dC5zbGljZShjaHVua1N0YXJ0LCB0aGlzLnBvcysrKTtyZXR1cm4gdGhpcy5maW5pc2hUb2tlbih0dC5zdHJpbmcsIG91dCk7fTtwcC5yZWFkVG1wbFRva2VuID0gZnVuY3Rpb24oKXt2YXIgb3V0PVwiXCIsIGNodW5rU3RhcnQ9dGhpcy5wb3M7Zm9yKDs7KSB7aWYodGhpcy5wb3MgPj0gdGhpcy5pbnB1dC5sZW5ndGgpdGhpcy5yYWlzZSh0aGlzLnN0YXJ0LCBcIlVudGVybWluYXRlZCB0ZW1wbGF0ZVwiKTt2YXIgY2g9dGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zKTtpZihjaCA9PT0gOTYgfHwgY2ggPT09IDM2ICYmIHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIDEpID09PSAxMjMpe2lmKHRoaXMucG9zID09PSB0aGlzLnN0YXJ0ICYmIHRoaXMudHlwZSA9PT0gdHQudGVtcGxhdGUpe2lmKGNoID09PSAzNil7dGhpcy5wb3MgKz0gMjtyZXR1cm4gdGhpcy5maW5pc2hUb2tlbih0dC5kb2xsYXJCcmFjZUwpO31lbHNlIHsrK3RoaXMucG9zO3JldHVybiB0aGlzLmZpbmlzaFRva2VuKHR0LmJhY2tRdW90ZSk7fX1vdXQgKz0gdGhpcy5pbnB1dC5zbGljZShjaHVua1N0YXJ0LCB0aGlzLnBvcyk7cmV0dXJuIHRoaXMuZmluaXNoVG9rZW4odHQudGVtcGxhdGUsIG91dCk7fWlmKGNoID09PSA5Mil7b3V0ICs9IHRoaXMuaW5wdXQuc2xpY2UoY2h1bmtTdGFydCwgdGhpcy5wb3MpO291dCArPSB0aGlzLnJlYWRFc2NhcGVkQ2hhcigpO2NodW5rU3RhcnQgPSB0aGlzLnBvczt9ZWxzZSBpZihpc05ld0xpbmUoY2gpKXtvdXQgKz0gdGhpcy5pbnB1dC5zbGljZShjaHVua1N0YXJ0LCB0aGlzLnBvcyk7Kyt0aGlzLnBvcztpZihjaCA9PT0gMTMgJiYgdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zKSA9PT0gMTApeysrdGhpcy5wb3M7b3V0ICs9IFwiXFxuXCI7fWVsc2Uge291dCArPSBTdHJpbmcuZnJvbUNoYXJDb2RlKGNoKTt9aWYodGhpcy5vcHRpb25zLmxvY2F0aW9ucyl7Kyt0aGlzLmN1ckxpbmU7dGhpcy5saW5lU3RhcnQgPSB0aGlzLnBvczt9Y2h1bmtTdGFydCA9IHRoaXMucG9zO31lbHNlIHsrK3RoaXMucG9zO319fTtwcC5yZWFkRXNjYXBlZENoYXIgPSBmdW5jdGlvbigpe3ZhciBjaD10aGlzLmlucHV0LmNoYXJDb2RlQXQoKyt0aGlzLnBvcyk7dmFyIG9jdGFsPS9eWzAtN10rLy5leGVjKHRoaXMuaW5wdXQuc2xpY2UodGhpcy5wb3MsIHRoaXMucG9zICsgMykpO2lmKG9jdGFsKW9jdGFsID0gb2N0YWxbMF07d2hpbGUob2N0YWwgJiYgcGFyc2VJbnQob2N0YWwsIDgpID4gMjU1KSBvY3RhbCA9IG9jdGFsLnNsaWNlKDAsIC0xKTtpZihvY3RhbCA9PT0gXCIwXCIpb2N0YWwgPSBudWxsOysrdGhpcy5wb3M7aWYob2N0YWwpe2lmKHRoaXMuc3RyaWN0KXRoaXMucmFpc2UodGhpcy5wb3MgLSAyLCBcIk9jdGFsIGxpdGVyYWwgaW4gc3RyaWN0IG1vZGVcIik7dGhpcy5wb3MgKz0gb2N0YWwubGVuZ3RoIC0gMTtyZXR1cm4gU3RyaW5nLmZyb21DaGFyQ29kZShwYXJzZUludChvY3RhbCwgOCkpO31lbHNlIHtzd2l0Y2goY2gpe2Nhc2UgMTEwOnJldHVybiBcIlxcblwiO2Nhc2UgMTE0OnJldHVybiBcIlxcclwiO2Nhc2UgMTIwOnJldHVybiBTdHJpbmcuZnJvbUNoYXJDb2RlKHRoaXMucmVhZEhleENoYXIoMikpO2Nhc2UgMTE3OnJldHVybiBjb2RlUG9pbnRUb1N0cmluZyh0aGlzLnJlYWRDb2RlUG9pbnQoKSk7Y2FzZSAxMTY6cmV0dXJuIFwiXFx0XCI7Y2FzZSA5ODpyZXR1cm4gXCJcXGJcIjtjYXNlIDExODpyZXR1cm4gXCJcXHUwMDBiXCI7Y2FzZSAxMDI6cmV0dXJuIFwiXFxmXCI7Y2FzZSA0ODpyZXR1cm4gXCJcXHUwMDAwXCI7Y2FzZSAxMzppZih0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MpID09PSAxMCkrK3RoaXMucG9zO2Nhc2UgMTA6aWYodGhpcy5vcHRpb25zLmxvY2F0aW9ucyl7dGhpcy5saW5lU3RhcnQgPSB0aGlzLnBvczsrK3RoaXMuY3VyTGluZTt9cmV0dXJuIFwiXCI7ZGVmYXVsdDpyZXR1cm4gU3RyaW5nLmZyb21DaGFyQ29kZShjaCk7fX19O3BwLnJlYWRIZXhDaGFyID0gZnVuY3Rpb24obGVuKXt2YXIgbj10aGlzLnJlYWRJbnQoMTYsIGxlbik7aWYobiA9PT0gbnVsbCl0aGlzLnJhaXNlKHRoaXMuc3RhcnQsIFwiQmFkIGNoYXJhY3RlciBlc2NhcGUgc2VxdWVuY2VcIik7cmV0dXJuIG47fTt2YXIgY29udGFpbnNFc2M7cHAucmVhZFdvcmQxID0gZnVuY3Rpb24oKXtjb250YWluc0VzYyA9IGZhbHNlO3ZhciB3b3JkPVwiXCIsIGZpcnN0PXRydWUsIGNodW5rU3RhcnQ9dGhpcy5wb3M7dmFyIGFzdHJhbD10aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNjt3aGlsZSh0aGlzLnBvcyA8IHRoaXMuaW5wdXQubGVuZ3RoKSB7dmFyIGNoPXRoaXMuZnVsbENoYXJDb2RlQXRQb3MoKTtpZihpc0lkZW50aWZpZXJDaGFyKGNoLCBhc3RyYWwpKXt0aGlzLnBvcyArPSBjaCA8PSA2NTUzNT8xOjI7fWVsc2UgaWYoY2ggPT09IDkyKXtjb250YWluc0VzYyA9IHRydWU7d29yZCArPSB0aGlzLmlucHV0LnNsaWNlKGNodW5rU3RhcnQsIHRoaXMucG9zKTt2YXIgZXNjU3RhcnQ9dGhpcy5wb3M7aWYodGhpcy5pbnB1dC5jaGFyQ29kZUF0KCsrdGhpcy5wb3MpICE9IDExNyl0aGlzLnJhaXNlKHRoaXMucG9zLCBcIkV4cGVjdGluZyBVbmljb2RlIGVzY2FwZSBzZXF1ZW5jZSBcXFxcdVhYWFhcIik7Kyt0aGlzLnBvczt2YXIgZXNjPXRoaXMucmVhZENvZGVQb2ludCgpO2lmKCEoZmlyc3Q/aXNJZGVudGlmaWVyU3RhcnQ6aXNJZGVudGlmaWVyQ2hhcikoZXNjLCBhc3RyYWwpKXRoaXMucmFpc2UoZXNjU3RhcnQsIFwiSW52YWxpZCBVbmljb2RlIGVzY2FwZVwiKTt3b3JkICs9IGNvZGVQb2ludFRvU3RyaW5nKGVzYyk7Y2h1bmtTdGFydCA9IHRoaXMucG9zO31lbHNlIHticmVhazt9Zmlyc3QgPSBmYWxzZTt9cmV0dXJuIHdvcmQgKyB0aGlzLmlucHV0LnNsaWNlKGNodW5rU3RhcnQsIHRoaXMucG9zKTt9O3BwLnJlYWRXb3JkID0gZnVuY3Rpb24oKXt2YXIgd29yZD10aGlzLnJlYWRXb3JkMSgpO3ZhciB0eXBlPXR0Lm5hbWU7aWYoKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2IHx8ICFjb250YWluc0VzYykgJiYgdGhpcy5pc0tleXdvcmQod29yZCkpdHlwZSA9IGtleXdvcmRUeXBlc1t3b3JkXTtyZXR1cm4gdGhpcy5maW5pc2hUb2tlbih0eXBlLCB3b3JkKTt9O30sIHtcIi4vaWRlbnRpZmllclwiOjcsIFwiLi9sb2NhdGlvblwiOjgsIFwiLi9zdGF0ZVwiOjEzLCBcIi4vdG9rZW50eXBlXCI6MTcsIFwiLi93aGl0ZXNwYWNlXCI6MTl9XSwgMTc6W2Z1bmN0aW9uKF9kZXJlcV8sIG1vZHVsZSwgZXhwb3J0cyl7XCJ1c2Ugc3RyaWN0XCI7dmFyIF9jbGFzc0NhbGxDaGVjaz1mdW5jdGlvbiBfY2xhc3NDYWxsQ2hlY2soaW5zdGFuY2UsIENvbnN0cnVjdG9yKXtpZighKGluc3RhbmNlIGluc3RhbmNlb2YgQ29uc3RydWN0b3IpKXt0aHJvdyBuZXcgVHlwZUVycm9yKFwiQ2Fubm90IGNhbGwgYSBjbGFzcyBhcyBhIGZ1bmN0aW9uXCIpO319O2V4cG9ydHMuX19lc01vZHVsZSA9IHRydWU7dmFyIFRva2VuVHlwZT1leHBvcnRzLlRva2VuVHlwZSA9IGZ1bmN0aW9uIFRva2VuVHlwZShsYWJlbCl7dmFyIGNvbmY9YXJndW1lbnRzWzFdID09PSB1bmRlZmluZWQ/e306YXJndW1lbnRzWzFdO19jbGFzc0NhbGxDaGVjayh0aGlzLCBUb2tlblR5cGUpO3RoaXMubGFiZWwgPSBsYWJlbDt0aGlzLmtleXdvcmQgPSBjb25mLmtleXdvcmQ7dGhpcy5iZWZvcmVFeHByID0gISFjb25mLmJlZm9yZUV4cHI7dGhpcy5zdGFydHNFeHByID0gISFjb25mLnN0YXJ0c0V4cHI7dGhpcy5pc0xvb3AgPSAhIWNvbmYuaXNMb29wO3RoaXMuaXNBc3NpZ24gPSAhIWNvbmYuaXNBc3NpZ247dGhpcy5wcmVmaXggPSAhIWNvbmYucHJlZml4O3RoaXMucG9zdGZpeCA9ICEhY29uZi5wb3N0Zml4O3RoaXMuYmlub3AgPSBjb25mLmJpbm9wIHx8IG51bGw7dGhpcy51cGRhdGVDb250ZXh0ID0gbnVsbDt9O2Z1bmN0aW9uIGJpbm9wKG5hbWUsIHByZWMpe3JldHVybiBuZXcgVG9rZW5UeXBlKG5hbWUsIHtiZWZvcmVFeHByOnRydWUsIGJpbm9wOnByZWN9KTt9dmFyIGJlZm9yZUV4cHI9e2JlZm9yZUV4cHI6dHJ1ZX0sIHN0YXJ0c0V4cHI9e3N0YXJ0c0V4cHI6dHJ1ZX07dmFyIHR5cGVzPXtudW06bmV3IFRva2VuVHlwZShcIm51bVwiLCBzdGFydHNFeHByKSwgcmVnZXhwOm5ldyBUb2tlblR5cGUoXCJyZWdleHBcIiwgc3RhcnRzRXhwciksIHN0cmluZzpuZXcgVG9rZW5UeXBlKFwic3RyaW5nXCIsIHN0YXJ0c0V4cHIpLCBuYW1lOm5ldyBUb2tlblR5cGUoXCJuYW1lXCIsIHN0YXJ0c0V4cHIpLCBlb2Y6bmV3IFRva2VuVHlwZShcImVvZlwiKSwgYnJhY2tldEw6bmV3IFRva2VuVHlwZShcIltcIiwge2JlZm9yZUV4cHI6dHJ1ZSwgc3RhcnRzRXhwcjp0cnVlfSksIGJyYWNrZXRSOm5ldyBUb2tlblR5cGUoXCJdXCIpLCBicmFjZUw6bmV3IFRva2VuVHlwZShcIntcIiwge2JlZm9yZUV4cHI6dHJ1ZSwgc3RhcnRzRXhwcjp0cnVlfSksIGJyYWNlUjpuZXcgVG9rZW5UeXBlKFwifVwiKSwgcGFyZW5MOm5ldyBUb2tlblR5cGUoXCIoXCIsIHtiZWZvcmVFeHByOnRydWUsIHN0YXJ0c0V4cHI6dHJ1ZX0pLCBwYXJlblI6bmV3IFRva2VuVHlwZShcIilcIiksIGNvbW1hOm5ldyBUb2tlblR5cGUoXCIsXCIsIGJlZm9yZUV4cHIpLCBzZW1pOm5ldyBUb2tlblR5cGUoXCI7XCIsIGJlZm9yZUV4cHIpLCBjb2xvbjpuZXcgVG9rZW5UeXBlKFwiOlwiLCBiZWZvcmVFeHByKSwgZG90Om5ldyBUb2tlblR5cGUoXCIuXCIpLCBxdWVzdGlvbjpuZXcgVG9rZW5UeXBlKFwiP1wiLCBiZWZvcmVFeHByKSwgYXJyb3c6bmV3IFRva2VuVHlwZShcIj0+XCIsIGJlZm9yZUV4cHIpLCB0ZW1wbGF0ZTpuZXcgVG9rZW5UeXBlKFwidGVtcGxhdGVcIiksIGVsbGlwc2lzOm5ldyBUb2tlblR5cGUoXCIuLi5cIiwgYmVmb3JlRXhwciksIGJhY2tRdW90ZTpuZXcgVG9rZW5UeXBlKFwiYFwiLCBzdGFydHNFeHByKSwgZG9sbGFyQnJhY2VMOm5ldyBUb2tlblR5cGUoXCIke1wiLCB7YmVmb3JlRXhwcjp0cnVlLCBzdGFydHNFeHByOnRydWV9KSwgZXE6bmV3IFRva2VuVHlwZShcIj1cIiwge2JlZm9yZUV4cHI6dHJ1ZSwgaXNBc3NpZ246dHJ1ZX0pLCBhc3NpZ246bmV3IFRva2VuVHlwZShcIl89XCIsIHtiZWZvcmVFeHByOnRydWUsIGlzQXNzaWduOnRydWV9KSwgaW5jRGVjOm5ldyBUb2tlblR5cGUoXCIrKy8tLVwiLCB7cHJlZml4OnRydWUsIHBvc3RmaXg6dHJ1ZSwgc3RhcnRzRXhwcjp0cnVlfSksIHByZWZpeDpuZXcgVG9rZW5UeXBlKFwicHJlZml4XCIsIHtiZWZvcmVFeHByOnRydWUsIHByZWZpeDp0cnVlLCBzdGFydHNFeHByOnRydWV9KSwgbG9naWNhbE9SOmJpbm9wKFwifHxcIiwgMSksIGxvZ2ljYWxBTkQ6Ymlub3AoXCImJlwiLCAyKSwgYml0d2lzZU9SOmJpbm9wKFwifFwiLCAzKSwgYml0d2lzZVhPUjpiaW5vcChcIl5cIiwgNCksIGJpdHdpc2VBTkQ6Ymlub3AoXCImXCIsIDUpLCBlcXVhbGl0eTpiaW5vcChcIj09LyE9XCIsIDYpLCByZWxhdGlvbmFsOmJpbm9wKFwiPC8+XCIsIDcpLCBiaXRTaGlmdDpiaW5vcChcIjw8Lz4+XCIsIDgpLCBwbHVzTWluOm5ldyBUb2tlblR5cGUoXCIrLy1cIiwge2JlZm9yZUV4cHI6dHJ1ZSwgYmlub3A6OSwgcHJlZml4OnRydWUsIHN0YXJ0c0V4cHI6dHJ1ZX0pLCBtb2R1bG86Ymlub3AoXCIlXCIsIDEwKSwgc3RhcjpiaW5vcChcIipcIiwgMTApLCBzbGFzaDpiaW5vcChcIi9cIiwgMTApfTtleHBvcnRzLnR5cGVzID0gdHlwZXM7dmFyIGtleXdvcmRzPXt9O2V4cG9ydHMua2V5d29yZHMgPSBrZXl3b3JkcztmdW5jdGlvbiBrdyhuYW1lKXt2YXIgb3B0aW9ucz1hcmd1bWVudHNbMV0gPT09IHVuZGVmaW5lZD97fTphcmd1bWVudHNbMV07b3B0aW9ucy5rZXl3b3JkID0gbmFtZTtrZXl3b3Jkc1tuYW1lXSA9IHR5cGVzW1wiX1wiICsgbmFtZV0gPSBuZXcgVG9rZW5UeXBlKG5hbWUsIG9wdGlvbnMpO31rdyhcImJyZWFrXCIpO2t3KFwiY2FzZVwiLCBiZWZvcmVFeHByKTtrdyhcImNhdGNoXCIpO2t3KFwiY29udGludWVcIik7a3coXCJkZWJ1Z2dlclwiKTtrdyhcImRlZmF1bHRcIik7a3coXCJkb1wiLCB7aXNMb29wOnRydWV9KTtrdyhcImVsc2VcIiwgYmVmb3JlRXhwcik7a3coXCJmaW5hbGx5XCIpO2t3KFwiZm9yXCIsIHtpc0xvb3A6dHJ1ZX0pO2t3KFwiZnVuY3Rpb25cIiwgc3RhcnRzRXhwcik7a3coXCJpZlwiKTtrdyhcInJldHVyblwiLCBiZWZvcmVFeHByKTtrdyhcInN3aXRjaFwiKTtrdyhcInRocm93XCIsIGJlZm9yZUV4cHIpO2t3KFwidHJ5XCIpO2t3KFwidmFyXCIpO2t3KFwibGV0XCIpO2t3KFwiY29uc3RcIik7a3coXCJ3aGlsZVwiLCB7aXNMb29wOnRydWV9KTtrdyhcIndpdGhcIik7a3coXCJuZXdcIiwge2JlZm9yZUV4cHI6dHJ1ZSwgc3RhcnRzRXhwcjp0cnVlfSk7a3coXCJ0aGlzXCIsIHN0YXJ0c0V4cHIpO2t3KFwic3VwZXJcIiwgc3RhcnRzRXhwcik7a3coXCJjbGFzc1wiKTtrdyhcImV4dGVuZHNcIiwgYmVmb3JlRXhwcik7a3coXCJleHBvcnRcIik7a3coXCJpbXBvcnRcIik7a3coXCJ5aWVsZFwiLCB7YmVmb3JlRXhwcjp0cnVlLCBzdGFydHNFeHByOnRydWV9KTtrdyhcIm51bGxcIiwgc3RhcnRzRXhwcik7a3coXCJ0cnVlXCIsIHN0YXJ0c0V4cHIpO2t3KFwiZmFsc2VcIiwgc3RhcnRzRXhwcik7a3coXCJpblwiLCB7YmVmb3JlRXhwcjp0cnVlLCBiaW5vcDo3fSk7a3coXCJpbnN0YW5jZW9mXCIsIHtiZWZvcmVFeHByOnRydWUsIGJpbm9wOjd9KTtrdyhcInR5cGVvZlwiLCB7YmVmb3JlRXhwcjp0cnVlLCBwcmVmaXg6dHJ1ZSwgc3RhcnRzRXhwcjp0cnVlfSk7a3coXCJ2b2lkXCIsIHtiZWZvcmVFeHByOnRydWUsIHByZWZpeDp0cnVlLCBzdGFydHNFeHByOnRydWV9KTtrdyhcImRlbGV0ZVwiLCB7YmVmb3JlRXhwcjp0cnVlLCBwcmVmaXg6dHJ1ZSwgc3RhcnRzRXhwcjp0cnVlfSk7fSwge31dLCAxODpbZnVuY3Rpb24oX2RlcmVxXywgbW9kdWxlLCBleHBvcnRzKXtcInVzZSBzdHJpY3RcIjtleHBvcnRzLmlzQXJyYXkgPSBpc0FycmF5O2V4cG9ydHMuaGFzID0gaGFzO2V4cG9ydHMuX19lc01vZHVsZSA9IHRydWU7ZnVuY3Rpb24gaXNBcnJheShvYmope3JldHVybiBPYmplY3QucHJvdG90eXBlLnRvU3RyaW5nLmNhbGwob2JqKSA9PT0gXCJbb2JqZWN0IEFycmF5XVwiO31mdW5jdGlvbiBoYXMob2JqLCBwcm9wTmFtZSl7cmV0dXJuIE9iamVjdC5wcm90b3R5cGUuaGFzT3duUHJvcGVydHkuY2FsbChvYmosIHByb3BOYW1lKTt9fSwge31dLCAxOTpbZnVuY3Rpb24oX2RlcmVxXywgbW9kdWxlLCBleHBvcnRzKXtcInVzZSBzdHJpY3RcIjtleHBvcnRzLmlzTmV3TGluZSA9IGlzTmV3TGluZTtleHBvcnRzLl9fZXNNb2R1bGUgPSB0cnVlO3ZhciBsaW5lQnJlYWs9L1xcclxcbj98XFxufFxcdTIwMjh8XFx1MjAyOS87ZXhwb3J0cy5saW5lQnJlYWsgPSBsaW5lQnJlYWs7dmFyIGxpbmVCcmVha0c9bmV3IFJlZ0V4cChsaW5lQnJlYWsuc291cmNlLCBcImdcIik7ZXhwb3J0cy5saW5lQnJlYWtHID0gbGluZUJyZWFrRztmdW5jdGlvbiBpc05ld0xpbmUoY29kZSl7cmV0dXJuIGNvZGUgPT09IDEwIHx8IGNvZGUgPT09IDEzIHx8IGNvZGUgPT09IDgyMzIgfHwgY29kZSA9PSA4MjMzO312YXIgbm9uQVNDSUl3aGl0ZXNwYWNlPS9bXFx1MTY4MFxcdTE4MGVcXHUyMDAwLVxcdTIwMGFcXHUyMDJmXFx1MjA1ZlxcdTMwMDBcXHVmZWZmXS87ZXhwb3J0cy5ub25BU0NJSXdoaXRlc3BhY2UgPSBub25BU0NJSXdoaXRlc3BhY2U7fSwge31dfSwge30sIFsxXSkoMSk7fSk7XG5cbn0pLmNhbGwodGhpcyx0eXBlb2YgZ2xvYmFsICE9PSBcInVuZGVmaW5lZFwiID8gZ2xvYmFsIDogdHlwZW9mIHNlbGYgIT09IFwidW5kZWZpbmVkXCIgPyBzZWxmIDogdHlwZW9mIHdpbmRvdyAhPT0gXCJ1bmRlZmluZWRcIiA/IHdpbmRvdyA6IHt9KVxufSx7fV0sMzpbZnVuY3Rpb24oX2RlcmVxXyxtb2R1bGUsZXhwb3J0cyl7XG5cInVzZSBzdHJpY3RcIjtcblxubW9kdWxlLmV4cG9ydHMgPSB0eXBlb2YgYWNvcm4gIT0gXCJ1bmRlZmluZWRcIiA/IGFjb3JuIDogX2RlcmVxXyhcImFjb3JuXCIpO1xuXG59LHtcImFjb3JuXCI6Mn1dLDQ6W2Z1bmN0aW9uKF9kZXJlcV8sbW9kdWxlLGV4cG9ydHMpe1xuXCJ1c2Ugc3RyaWN0XCI7XG5cbnZhciBMb29zZVBhcnNlciA9IF9kZXJlcV8oXCIuL3N0YXRlXCIpLkxvb3NlUGFyc2VyO1xuXG52YXIgaXNEdW1teSA9IF9kZXJlcV8oXCIuL3BhcnNldXRpbFwiKS5pc0R1bW15O1xuXG52YXIgdHQgPSBfZGVyZXFfKFwiLi5cIikudG9rVHlwZXM7XG5cbnZhciBscCA9IExvb3NlUGFyc2VyLnByb3RvdHlwZTtcblxubHAuY2hlY2tMVmFsID0gZnVuY3Rpb24gKGV4cHIsIGJpbmRpbmcpIHtcbiAgaWYgKCFleHByKSByZXR1cm4gZXhwcjtcbiAgc3dpdGNoIChleHByLnR5cGUpIHtcbiAgICBjYXNlIFwiSWRlbnRpZmllclwiOlxuICAgICAgcmV0dXJuIGV4cHI7XG5cbiAgICBjYXNlIFwiTWVtYmVyRXhwcmVzc2lvblwiOlxuICAgICAgcmV0dXJuIGJpbmRpbmcgPyB0aGlzLmR1bW15SWRlbnQoKSA6IGV4cHI7XG5cbiAgICBjYXNlIFwiUGFyZW50aGVzaXplZEV4cHJlc3Npb25cIjpcbiAgICAgIGV4cHIuZXhwcmVzc2lvbiA9IHRoaXMuY2hlY2tMVmFsKGV4cHIuZXhwcmVzc2lvbiwgYmluZGluZyk7XG4gICAgICByZXR1cm4gZXhwcjtcblxuICAgIC8vIEZJWE1FIHJlY3Vyc2l2ZWx5IGNoZWNrIGNvbnRlbnRzXG4gICAgY2FzZSBcIk9iamVjdFBhdHRlcm5cIjpcbiAgICBjYXNlIFwiQXJyYXlQYXR0ZXJuXCI6XG4gICAgY2FzZSBcIlJlc3RFbGVtZW50XCI6XG4gICAgY2FzZSBcIkFzc2lnbm1lbnRQYXR0ZXJuXCI6XG4gICAgICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYpIHJldHVybiBleHByO1xuXG4gICAgZGVmYXVsdDpcbiAgICAgIHJldHVybiB0aGlzLmR1bW15SWRlbnQoKTtcbiAgfVxufTtcblxubHAucGFyc2VFeHByZXNzaW9uID0gZnVuY3Rpb24gKG5vSW4pIHtcbiAgdmFyIHN0YXJ0ID0gdGhpcy5zdG9yZUN1cnJlbnRQb3MoKTtcbiAgdmFyIGV4cHIgPSB0aGlzLnBhcnNlTWF5YmVBc3NpZ24obm9Jbik7XG4gIGlmICh0aGlzLnRvay50eXBlID09PSB0dC5jb21tYSkge1xuICAgIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGVBdChzdGFydCk7XG4gICAgbm9kZS5leHByZXNzaW9ucyA9IFtleHByXTtcbiAgICB3aGlsZSAodGhpcy5lYXQodHQuY29tbWEpKSBub2RlLmV4cHJlc3Npb25zLnB1c2godGhpcy5wYXJzZU1heWJlQXNzaWduKG5vSW4pKTtcbiAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiU2VxdWVuY2VFeHByZXNzaW9uXCIpO1xuICB9XG4gIHJldHVybiBleHByO1xufTtcblxubHAucGFyc2VQYXJlbkV4cHJlc3Npb24gPSBmdW5jdGlvbiAoKSB7XG4gIHRoaXMucHVzaEN4KCk7XG4gIHRoaXMuZXhwZWN0KHR0LnBhcmVuTCk7XG4gIHZhciB2YWwgPSB0aGlzLnBhcnNlRXhwcmVzc2lvbigpO1xuICB0aGlzLnBvcEN4KCk7XG4gIHRoaXMuZXhwZWN0KHR0LnBhcmVuUik7XG4gIHJldHVybiB2YWw7XG59O1xuXG5scC5wYXJzZU1heWJlQXNzaWduID0gZnVuY3Rpb24gKG5vSW4pIHtcbiAgdmFyIHN0YXJ0ID0gdGhpcy5zdG9yZUN1cnJlbnRQb3MoKTtcbiAgdmFyIGxlZnQgPSB0aGlzLnBhcnNlTWF5YmVDb25kaXRpb25hbChub0luKTtcbiAgaWYgKHRoaXMudG9rLnR5cGUuaXNBc3NpZ24pIHtcbiAgICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlQXQoc3RhcnQpO1xuICAgIG5vZGUub3BlcmF0b3IgPSB0aGlzLnRvay52YWx1ZTtcbiAgICBub2RlLmxlZnQgPSB0aGlzLnRvay50eXBlID09PSB0dC5lcSA/IHRoaXMudG9Bc3NpZ25hYmxlKGxlZnQpIDogdGhpcy5jaGVja0xWYWwobGVmdCk7XG4gICAgdGhpcy5uZXh0KCk7XG4gICAgbm9kZS5yaWdodCA9IHRoaXMucGFyc2VNYXliZUFzc2lnbihub0luKTtcbiAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiQXNzaWdubWVudEV4cHJlc3Npb25cIik7XG4gIH1cbiAgcmV0dXJuIGxlZnQ7XG59O1xuXG5scC5wYXJzZU1heWJlQ29uZGl0aW9uYWwgPSBmdW5jdGlvbiAobm9Jbikge1xuICB2YXIgc3RhcnQgPSB0aGlzLnN0b3JlQ3VycmVudFBvcygpO1xuICB2YXIgZXhwciA9IHRoaXMucGFyc2VFeHByT3BzKG5vSW4pO1xuICBpZiAodGhpcy5lYXQodHQucXVlc3Rpb24pKSB7XG4gICAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0KTtcbiAgICBub2RlLnRlc3QgPSBleHByO1xuICAgIG5vZGUuY29uc2VxdWVudCA9IHRoaXMucGFyc2VNYXliZUFzc2lnbigpO1xuICAgIG5vZGUuYWx0ZXJuYXRlID0gdGhpcy5leHBlY3QodHQuY29sb24pID8gdGhpcy5wYXJzZU1heWJlQXNzaWduKG5vSW4pIDogdGhpcy5kdW1teUlkZW50KCk7XG4gICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkNvbmRpdGlvbmFsRXhwcmVzc2lvblwiKTtcbiAgfVxuICByZXR1cm4gZXhwcjtcbn07XG5cbmxwLnBhcnNlRXhwck9wcyA9IGZ1bmN0aW9uIChub0luKSB7XG4gIHZhciBzdGFydCA9IHRoaXMuc3RvcmVDdXJyZW50UG9zKCk7XG4gIHZhciBpbmRlbnQgPSB0aGlzLmN1ckluZGVudCxcbiAgICAgIGxpbmUgPSB0aGlzLmN1ckxpbmVTdGFydDtcbiAgcmV0dXJuIHRoaXMucGFyc2VFeHByT3AodGhpcy5wYXJzZU1heWJlVW5hcnkobm9JbiksIHN0YXJ0LCAtMSwgbm9JbiwgaW5kZW50LCBsaW5lKTtcbn07XG5cbmxwLnBhcnNlRXhwck9wID0gZnVuY3Rpb24gKGxlZnQsIHN0YXJ0LCBtaW5QcmVjLCBub0luLCBpbmRlbnQsIGxpbmUpIHtcbiAgaWYgKHRoaXMuY3VyTGluZVN0YXJ0ICE9IGxpbmUgJiYgdGhpcy5jdXJJbmRlbnQgPCBpbmRlbnQgJiYgdGhpcy50b2tlblN0YXJ0c0xpbmUoKSkgcmV0dXJuIGxlZnQ7XG4gIHZhciBwcmVjID0gdGhpcy50b2sudHlwZS5iaW5vcDtcbiAgaWYgKHByZWMgIT0gbnVsbCAmJiAoIW5vSW4gfHwgdGhpcy50b2sudHlwZSAhPT0gdHQuX2luKSkge1xuICAgIGlmIChwcmVjID4gbWluUHJlYykge1xuICAgICAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0KTtcbiAgICAgIG5vZGUubGVmdCA9IGxlZnQ7XG4gICAgICBub2RlLm9wZXJhdG9yID0gdGhpcy50b2sudmFsdWU7XG4gICAgICB0aGlzLm5leHQoKTtcbiAgICAgIGlmICh0aGlzLmN1ckxpbmVTdGFydCAhPSBsaW5lICYmIHRoaXMuY3VySW5kZW50IDwgaW5kZW50ICYmIHRoaXMudG9rZW5TdGFydHNMaW5lKCkpIHtcbiAgICAgICAgbm9kZS5yaWdodCA9IHRoaXMuZHVtbXlJZGVudCgpO1xuICAgICAgfSBlbHNlIHtcbiAgICAgICAgdmFyIHJpZ2h0U3RhcnQgPSB0aGlzLnN0b3JlQ3VycmVudFBvcygpO1xuICAgICAgICBub2RlLnJpZ2h0ID0gdGhpcy5wYXJzZUV4cHJPcCh0aGlzLnBhcnNlTWF5YmVVbmFyeShub0luKSwgcmlnaHRTdGFydCwgcHJlYywgbm9JbiwgaW5kZW50LCBsaW5lKTtcbiAgICAgIH1cbiAgICAgIHRoaXMuZmluaXNoTm9kZShub2RlLCAvJiZ8XFx8XFx8Ly50ZXN0KG5vZGUub3BlcmF0b3IpID8gXCJMb2dpY2FsRXhwcmVzc2lvblwiIDogXCJCaW5hcnlFeHByZXNzaW9uXCIpO1xuICAgICAgcmV0dXJuIHRoaXMucGFyc2VFeHByT3Aobm9kZSwgc3RhcnQsIG1pblByZWMsIG5vSW4sIGluZGVudCwgbGluZSk7XG4gICAgfVxuICB9XG4gIHJldHVybiBsZWZ0O1xufTtcblxubHAucGFyc2VNYXliZVVuYXJ5ID0gZnVuY3Rpb24gKG5vSW4pIHtcbiAgaWYgKHRoaXMudG9rLnR5cGUucHJlZml4KSB7XG4gICAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpLFxuICAgICAgICB1cGRhdGUgPSB0aGlzLnRvay50eXBlID09PSB0dC5pbmNEZWM7XG4gICAgbm9kZS5vcGVyYXRvciA9IHRoaXMudG9rLnZhbHVlO1xuICAgIG5vZGUucHJlZml4ID0gdHJ1ZTtcbiAgICB0aGlzLm5leHQoKTtcbiAgICBub2RlLmFyZ3VtZW50ID0gdGhpcy5wYXJzZU1heWJlVW5hcnkobm9Jbik7XG4gICAgaWYgKHVwZGF0ZSkgbm9kZS5hcmd1bWVudCA9IHRoaXMuY2hlY2tMVmFsKG5vZGUuYXJndW1lbnQpO1xuICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgdXBkYXRlID8gXCJVcGRhdGVFeHByZXNzaW9uXCIgOiBcIlVuYXJ5RXhwcmVzc2lvblwiKTtcbiAgfSBlbHNlIGlmICh0aGlzLnRvay50eXBlID09PSB0dC5lbGxpcHNpcykge1xuICAgIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgICB0aGlzLm5leHQoKTtcbiAgICBub2RlLmFyZ3VtZW50ID0gdGhpcy5wYXJzZU1heWJlVW5hcnkobm9Jbik7XG4gICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIlNwcmVhZEVsZW1lbnRcIik7XG4gIH1cbiAgdmFyIHN0YXJ0ID0gdGhpcy5zdG9yZUN1cnJlbnRQb3MoKTtcbiAgdmFyIGV4cHIgPSB0aGlzLnBhcnNlRXhwclN1YnNjcmlwdHMoKTtcbiAgd2hpbGUgKHRoaXMudG9rLnR5cGUucG9zdGZpeCAmJiAhdGhpcy5jYW5JbnNlcnRTZW1pY29sb24oKSkge1xuICAgIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGVBdChzdGFydCk7XG4gICAgbm9kZS5vcGVyYXRvciA9IHRoaXMudG9rLnZhbHVlO1xuICAgIG5vZGUucHJlZml4ID0gZmFsc2U7XG4gICAgbm9kZS5hcmd1bWVudCA9IHRoaXMuY2hlY2tMVmFsKGV4cHIpO1xuICAgIHRoaXMubmV4dCgpO1xuICAgIGV4cHIgPSB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJVcGRhdGVFeHByZXNzaW9uXCIpO1xuICB9XG4gIHJldHVybiBleHByO1xufTtcblxubHAucGFyc2VFeHByU3Vic2NyaXB0cyA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIHN0YXJ0ID0gdGhpcy5zdG9yZUN1cnJlbnRQb3MoKTtcbiAgcmV0dXJuIHRoaXMucGFyc2VTdWJzY3JpcHRzKHRoaXMucGFyc2VFeHByQXRvbSgpLCBzdGFydCwgZmFsc2UsIHRoaXMuY3VySW5kZW50LCB0aGlzLmN1ckxpbmVTdGFydCk7XG59O1xuXG5scC5wYXJzZVN1YnNjcmlwdHMgPSBmdW5jdGlvbiAoYmFzZSwgc3RhcnQsIG5vQ2FsbHMsIHN0YXJ0SW5kZW50LCBsaW5lKSB7XG4gIGZvciAoOzspIHtcbiAgICBpZiAodGhpcy5jdXJMaW5lU3RhcnQgIT0gbGluZSAmJiB0aGlzLmN1ckluZGVudCA8PSBzdGFydEluZGVudCAmJiB0aGlzLnRva2VuU3RhcnRzTGluZSgpKSB7XG4gICAgICBpZiAodGhpcy50b2sudHlwZSA9PSB0dC5kb3QgJiYgdGhpcy5jdXJJbmRlbnQgPT0gc3RhcnRJbmRlbnQpIC0tc3RhcnRJbmRlbnQ7ZWxzZSByZXR1cm4gYmFzZTtcbiAgICB9XG5cbiAgICBpZiAodGhpcy5lYXQodHQuZG90KSkge1xuICAgICAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0KTtcbiAgICAgIG5vZGUub2JqZWN0ID0gYmFzZTtcbiAgICAgIGlmICh0aGlzLmN1ckxpbmVTdGFydCAhPSBsaW5lICYmIHRoaXMuY3VySW5kZW50IDw9IHN0YXJ0SW5kZW50ICYmIHRoaXMudG9rZW5TdGFydHNMaW5lKCkpIG5vZGUucHJvcGVydHkgPSB0aGlzLmR1bW15SWRlbnQoKTtlbHNlIG5vZGUucHJvcGVydHkgPSB0aGlzLnBhcnNlUHJvcGVydHlBY2Nlc3NvcigpIHx8IHRoaXMuZHVtbXlJZGVudCgpO1xuICAgICAgbm9kZS5jb21wdXRlZCA9IGZhbHNlO1xuICAgICAgYmFzZSA9IHRoaXMuZmluaXNoTm9kZShub2RlLCBcIk1lbWJlckV4cHJlc3Npb25cIik7XG4gICAgfSBlbHNlIGlmICh0aGlzLnRvay50eXBlID09IHR0LmJyYWNrZXRMKSB7XG4gICAgICB0aGlzLnB1c2hDeCgpO1xuICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlQXQoc3RhcnQpO1xuICAgICAgbm9kZS5vYmplY3QgPSBiYXNlO1xuICAgICAgbm9kZS5wcm9wZXJ0eSA9IHRoaXMucGFyc2VFeHByZXNzaW9uKCk7XG4gICAgICBub2RlLmNvbXB1dGVkID0gdHJ1ZTtcbiAgICAgIHRoaXMucG9wQ3goKTtcbiAgICAgIHRoaXMuZXhwZWN0KHR0LmJyYWNrZXRSKTtcbiAgICAgIGJhc2UgPSB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJNZW1iZXJFeHByZXNzaW9uXCIpO1xuICAgIH0gZWxzZSBpZiAoIW5vQ2FsbHMgJiYgdGhpcy50b2sudHlwZSA9PSB0dC5wYXJlbkwpIHtcbiAgICAgIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGVBdChzdGFydCk7XG4gICAgICBub2RlLmNhbGxlZSA9IGJhc2U7XG4gICAgICBub2RlLmFyZ3VtZW50cyA9IHRoaXMucGFyc2VFeHByTGlzdCh0dC5wYXJlblIpO1xuICAgICAgYmFzZSA9IHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkNhbGxFeHByZXNzaW9uXCIpO1xuICAgIH0gZWxzZSBpZiAodGhpcy50b2sudHlwZSA9PSB0dC5iYWNrUXVvdGUpIHtcbiAgICAgIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGVBdChzdGFydCk7XG4gICAgICBub2RlLnRhZyA9IGJhc2U7XG4gICAgICBub2RlLnF1YXNpID0gdGhpcy5wYXJzZVRlbXBsYXRlKCk7XG4gICAgICBiYXNlID0gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiVGFnZ2VkVGVtcGxhdGVFeHByZXNzaW9uXCIpO1xuICAgIH0gZWxzZSB7XG4gICAgICByZXR1cm4gYmFzZTtcbiAgICB9XG4gIH1cbn07XG5cbmxwLnBhcnNlRXhwckF0b20gPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBub2RlID0gdW5kZWZpbmVkO1xuICBzd2l0Y2ggKHRoaXMudG9rLnR5cGUpIHtcbiAgICBjYXNlIHR0Ll90aGlzOlxuICAgIGNhc2UgdHQuX3N1cGVyOlxuICAgICAgdmFyIHR5cGUgPSB0aGlzLnRvay50eXBlID09PSB0dC5fdGhpcyA/IFwiVGhpc0V4cHJlc3Npb25cIiA6IFwiU3VwZXJcIjtcbiAgICAgIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIHR5cGUpO1xuXG4gICAgY2FzZSB0dC5uYW1lOlxuICAgICAgdmFyIHN0YXJ0ID0gdGhpcy5zdG9yZUN1cnJlbnRQb3MoKTtcbiAgICAgIHZhciBpZCA9IHRoaXMucGFyc2VJZGVudCgpO1xuICAgICAgcmV0dXJuIHRoaXMuZWF0KHR0LmFycm93KSA/IHRoaXMucGFyc2VBcnJvd0V4cHJlc3Npb24odGhpcy5zdGFydE5vZGVBdChzdGFydCksIFtpZF0pIDogaWQ7XG5cbiAgICBjYXNlIHR0LnJlZ2V4cDpcbiAgICAgIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICAgICAgdmFyIHZhbCA9IHRoaXMudG9rLnZhbHVlO1xuICAgICAgbm9kZS5yZWdleCA9IHsgcGF0dGVybjogdmFsLnBhdHRlcm4sIGZsYWdzOiB2YWwuZmxhZ3MgfTtcbiAgICAgIG5vZGUudmFsdWUgPSB2YWwudmFsdWU7XG4gICAgICBub2RlLnJhdyA9IHRoaXMuaW5wdXQuc2xpY2UodGhpcy50b2suc3RhcnQsIHRoaXMudG9rLmVuZCk7XG4gICAgICB0aGlzLm5leHQoKTtcbiAgICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJMaXRlcmFsXCIpO1xuXG4gICAgY2FzZSB0dC5udW06Y2FzZSB0dC5zdHJpbmc6XG4gICAgICBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgICAgIG5vZGUudmFsdWUgPSB0aGlzLnRvay52YWx1ZTtcbiAgICAgIG5vZGUucmF3ID0gdGhpcy5pbnB1dC5zbGljZSh0aGlzLnRvay5zdGFydCwgdGhpcy50b2suZW5kKTtcbiAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkxpdGVyYWxcIik7XG5cbiAgICBjYXNlIHR0Ll9udWxsOmNhc2UgdHQuX3RydWU6Y2FzZSB0dC5fZmFsc2U6XG4gICAgICBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgICAgIG5vZGUudmFsdWUgPSB0aGlzLnRvay50eXBlID09PSB0dC5fbnVsbCA/IG51bGwgOiB0aGlzLnRvay50eXBlID09PSB0dC5fdHJ1ZTtcbiAgICAgIG5vZGUucmF3ID0gdGhpcy50b2sudHlwZS5rZXl3b3JkO1xuICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiTGl0ZXJhbFwiKTtcblxuICAgIGNhc2UgdHQucGFyZW5MOlxuICAgICAgdmFyIHBhcmVuU3RhcnQgPSB0aGlzLnN0b3JlQ3VycmVudFBvcygpO1xuICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICB2YXIgaW5uZXIgPSB0aGlzLnBhcnNlRXhwcmVzc2lvbigpO1xuICAgICAgdGhpcy5leHBlY3QodHQucGFyZW5SKTtcbiAgICAgIGlmICh0aGlzLmVhdCh0dC5hcnJvdykpIHtcbiAgICAgICAgcmV0dXJuIHRoaXMucGFyc2VBcnJvd0V4cHJlc3Npb24odGhpcy5zdGFydE5vZGVBdChwYXJlblN0YXJ0KSwgaW5uZXIuZXhwcmVzc2lvbnMgfHwgKGlzRHVtbXkoaW5uZXIpID8gW10gOiBbaW5uZXJdKSk7XG4gICAgICB9XG4gICAgICBpZiAodGhpcy5vcHRpb25zLnByZXNlcnZlUGFyZW5zKSB7XG4gICAgICAgIHZhciBwYXIgPSB0aGlzLnN0YXJ0Tm9kZUF0KHBhcmVuU3RhcnQpO1xuICAgICAgICBwYXIuZXhwcmVzc2lvbiA9IGlubmVyO1xuICAgICAgICBpbm5lciA9IHRoaXMuZmluaXNoTm9kZShwYXIsIFwiUGFyZW50aGVzaXplZEV4cHJlc3Npb25cIik7XG4gICAgICB9XG4gICAgICByZXR1cm4gaW5uZXI7XG5cbiAgICBjYXNlIHR0LmJyYWNrZXRMOlxuICAgICAgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gICAgICBub2RlLmVsZW1lbnRzID0gdGhpcy5wYXJzZUV4cHJMaXN0KHR0LmJyYWNrZXRSLCB0cnVlKTtcbiAgICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJBcnJheUV4cHJlc3Npb25cIik7XG5cbiAgICBjYXNlIHR0LmJyYWNlTDpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlT2JqKCk7XG5cbiAgICBjYXNlIHR0Ll9jbGFzczpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlQ2xhc3MoKTtcblxuICAgIGNhc2UgdHQuX2Z1bmN0aW9uOlxuICAgICAgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gICAgICB0aGlzLm5leHQoKTtcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlRnVuY3Rpb24obm9kZSwgZmFsc2UpO1xuXG4gICAgY2FzZSB0dC5fbmV3OlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VOZXcoKTtcblxuICAgIGNhc2UgdHQuX3lpZWxkOlxuICAgICAgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gICAgICB0aGlzLm5leHQoKTtcbiAgICAgIGlmICh0aGlzLnNlbWljb2xvbigpIHx8IHRoaXMuY2FuSW5zZXJ0U2VtaWNvbG9uKCkgfHwgdGhpcy50b2sudHlwZSAhPSB0dC5zdGFyICYmICF0aGlzLnRvay50eXBlLnN0YXJ0c0V4cHIpIHtcbiAgICAgICAgbm9kZS5kZWxlZ2F0ZSA9IGZhbHNlO1xuICAgICAgICBub2RlLmFyZ3VtZW50ID0gbnVsbDtcbiAgICAgIH0gZWxzZSB7XG4gICAgICAgIG5vZGUuZGVsZWdhdGUgPSB0aGlzLmVhdCh0dC5zdGFyKTtcbiAgICAgICAgbm9kZS5hcmd1bWVudCA9IHRoaXMucGFyc2VNYXliZUFzc2lnbigpO1xuICAgICAgfVxuICAgICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIllpZWxkRXhwcmVzc2lvblwiKTtcblxuICAgIGNhc2UgdHQuYmFja1F1b3RlOlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VUZW1wbGF0ZSgpO1xuXG4gICAgZGVmYXVsdDpcbiAgICAgIHJldHVybiB0aGlzLmR1bW15SWRlbnQoKTtcbiAgfVxufTtcblxubHAucGFyc2VOZXcgPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGUoKSxcbiAgICAgIHN0YXJ0SW5kZW50ID0gdGhpcy5jdXJJbmRlbnQsXG4gICAgICBsaW5lID0gdGhpcy5jdXJMaW5lU3RhcnQ7XG4gIHZhciBtZXRhID0gdGhpcy5wYXJzZUlkZW50KHRydWUpO1xuICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYgJiYgdGhpcy5lYXQodHQuZG90KSkge1xuICAgIG5vZGUubWV0YSA9IG1ldGE7XG4gICAgbm9kZS5wcm9wZXJ0eSA9IHRoaXMucGFyc2VJZGVudCh0cnVlKTtcbiAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiTWV0YVByb3BlcnR5XCIpO1xuICB9XG4gIHZhciBzdGFydCA9IHRoaXMuc3RvcmVDdXJyZW50UG9zKCk7XG4gIG5vZGUuY2FsbGVlID0gdGhpcy5wYXJzZVN1YnNjcmlwdHModGhpcy5wYXJzZUV4cHJBdG9tKCksIHN0YXJ0LCB0cnVlLCBzdGFydEluZGVudCwgbGluZSk7XG4gIGlmICh0aGlzLnRvay50eXBlID09IHR0LnBhcmVuTCkge1xuICAgIG5vZGUuYXJndW1lbnRzID0gdGhpcy5wYXJzZUV4cHJMaXN0KHR0LnBhcmVuUik7XG4gIH0gZWxzZSB7XG4gICAgbm9kZS5hcmd1bWVudHMgPSBbXTtcbiAgfVxuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiTmV3RXhwcmVzc2lvblwiKTtcbn07XG5cbmxwLnBhcnNlVGVtcGxhdGVFbGVtZW50ID0gZnVuY3Rpb24gKCkge1xuICB2YXIgZWxlbSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gIGVsZW0udmFsdWUgPSB7XG4gICAgcmF3OiB0aGlzLmlucHV0LnNsaWNlKHRoaXMudG9rLnN0YXJ0LCB0aGlzLnRvay5lbmQpLFxuICAgIGNvb2tlZDogdGhpcy50b2sudmFsdWVcbiAgfTtcbiAgdGhpcy5uZXh0KCk7XG4gIGVsZW0udGFpbCA9IHRoaXMudG9rLnR5cGUgPT09IHR0LmJhY2tRdW90ZTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShlbGVtLCBcIlRlbXBsYXRlRWxlbWVudFwiKTtcbn07XG5cbmxwLnBhcnNlVGVtcGxhdGUgPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgdGhpcy5uZXh0KCk7XG4gIG5vZGUuZXhwcmVzc2lvbnMgPSBbXTtcbiAgdmFyIGN1ckVsdCA9IHRoaXMucGFyc2VUZW1wbGF0ZUVsZW1lbnQoKTtcbiAgbm9kZS5xdWFzaXMgPSBbY3VyRWx0XTtcbiAgd2hpbGUgKCFjdXJFbHQudGFpbCkge1xuICAgIHRoaXMubmV4dCgpO1xuICAgIG5vZGUuZXhwcmVzc2lvbnMucHVzaCh0aGlzLnBhcnNlRXhwcmVzc2lvbigpKTtcbiAgICBpZiAodGhpcy5leHBlY3QodHQuYnJhY2VSKSkge1xuICAgICAgY3VyRWx0ID0gdGhpcy5wYXJzZVRlbXBsYXRlRWxlbWVudCgpO1xuICAgIH0gZWxzZSB7XG4gICAgICBjdXJFbHQgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICAgICAgY3VyRWx0LnZhbHVlID0geyBjb29rZWQ6IFwiXCIsIHJhdzogXCJcIiB9O1xuICAgICAgY3VyRWx0LnRhaWwgPSB0cnVlO1xuICAgIH1cbiAgICBub2RlLnF1YXNpcy5wdXNoKGN1ckVsdCk7XG4gIH1cbiAgdGhpcy5leHBlY3QodHQuYmFja1F1b3RlKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIlRlbXBsYXRlTGl0ZXJhbFwiKTtcbn07XG5cbmxwLnBhcnNlT2JqID0gZnVuY3Rpb24gKCkge1xuICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gIG5vZGUucHJvcGVydGllcyA9IFtdO1xuICB0aGlzLnB1c2hDeCgpO1xuICB2YXIgaW5kZW50ID0gdGhpcy5jdXJJbmRlbnQgKyAxLFxuICAgICAgbGluZSA9IHRoaXMuY3VyTGluZVN0YXJ0O1xuICB0aGlzLmVhdCh0dC5icmFjZUwpO1xuICBpZiAodGhpcy5jdXJJbmRlbnQgKyAxIDwgaW5kZW50KSB7XG4gICAgaW5kZW50ID0gdGhpcy5jdXJJbmRlbnQ7bGluZSA9IHRoaXMuY3VyTGluZVN0YXJ0O1xuICB9XG4gIHdoaWxlICghdGhpcy5jbG9zZXModHQuYnJhY2VSLCBpbmRlbnQsIGxpbmUpKSB7XG4gICAgdmFyIHByb3AgPSB0aGlzLnN0YXJ0Tm9kZSgpLFxuICAgICAgICBpc0dlbmVyYXRvciA9IHVuZGVmaW5lZCxcbiAgICAgICAgc3RhcnQgPSB1bmRlZmluZWQ7XG4gICAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KSB7XG4gICAgICBzdGFydCA9IHRoaXMuc3RvcmVDdXJyZW50UG9zKCk7XG4gICAgICBwcm9wLm1ldGhvZCA9IGZhbHNlO1xuICAgICAgcHJvcC5zaG9ydGhhbmQgPSBmYWxzZTtcbiAgICAgIGlzR2VuZXJhdG9yID0gdGhpcy5lYXQodHQuc3Rhcik7XG4gICAgfVxuICAgIHRoaXMucGFyc2VQcm9wZXJ0eU5hbWUocHJvcCk7XG4gICAgaWYgKGlzRHVtbXkocHJvcC5rZXkpKSB7XG4gICAgICBpZiAoaXNEdW1teSh0aGlzLnBhcnNlTWF5YmVBc3NpZ24oKSkpIHRoaXMubmV4dCgpO3RoaXMuZWF0KHR0LmNvbW1hKTtjb250aW51ZTtcbiAgICB9XG4gICAgaWYgKHRoaXMuZWF0KHR0LmNvbG9uKSkge1xuICAgICAgcHJvcC5raW5kID0gXCJpbml0XCI7XG4gICAgICBwcm9wLnZhbHVlID0gdGhpcy5wYXJzZU1heWJlQXNzaWduKCk7XG4gICAgfSBlbHNlIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNiAmJiAodGhpcy50b2sudHlwZSA9PT0gdHQucGFyZW5MIHx8IHRoaXMudG9rLnR5cGUgPT09IHR0LmJyYWNlTCkpIHtcbiAgICAgIHByb3Aua2luZCA9IFwiaW5pdFwiO1xuICAgICAgcHJvcC5tZXRob2QgPSB0cnVlO1xuICAgICAgcHJvcC52YWx1ZSA9IHRoaXMucGFyc2VNZXRob2QoaXNHZW5lcmF0b3IpO1xuICAgIH0gZWxzZSBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDUgJiYgcHJvcC5rZXkudHlwZSA9PT0gXCJJZGVudGlmaWVyXCIgJiYgIXByb3AuY29tcHV0ZWQgJiYgKHByb3Aua2V5Lm5hbWUgPT09IFwiZ2V0XCIgfHwgcHJvcC5rZXkubmFtZSA9PT0gXCJzZXRcIikgJiYgKHRoaXMudG9rLnR5cGUgIT0gdHQuY29tbWEgJiYgdGhpcy50b2sudHlwZSAhPSB0dC5icmFjZVIpKSB7XG4gICAgICBwcm9wLmtpbmQgPSBwcm9wLmtleS5uYW1lO1xuICAgICAgdGhpcy5wYXJzZVByb3BlcnR5TmFtZShwcm9wKTtcbiAgICAgIHByb3AudmFsdWUgPSB0aGlzLnBhcnNlTWV0aG9kKGZhbHNlKTtcbiAgICB9IGVsc2Uge1xuICAgICAgcHJvcC5raW5kID0gXCJpbml0XCI7XG4gICAgICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYpIHtcbiAgICAgICAgaWYgKHRoaXMuZWF0KHR0LmVxKSkge1xuICAgICAgICAgIHZhciBhc3NpZ24gPSB0aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0KTtcbiAgICAgICAgICBhc3NpZ24ub3BlcmF0b3IgPSBcIj1cIjtcbiAgICAgICAgICBhc3NpZ24ubGVmdCA9IHByb3Aua2V5O1xuICAgICAgICAgIGFzc2lnbi5yaWdodCA9IHRoaXMucGFyc2VNYXliZUFzc2lnbigpO1xuICAgICAgICAgIHByb3AudmFsdWUgPSB0aGlzLmZpbmlzaE5vZGUoYXNzaWduLCBcIkFzc2lnbm1lbnRFeHByZXNzaW9uXCIpO1xuICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgIHByb3AudmFsdWUgPSBwcm9wLmtleTtcbiAgICAgICAgfVxuICAgICAgfSBlbHNlIHtcbiAgICAgICAgcHJvcC52YWx1ZSA9IHRoaXMuZHVtbXlJZGVudCgpO1xuICAgICAgfVxuICAgICAgcHJvcC5zaG9ydGhhbmQgPSB0cnVlO1xuICAgIH1cbiAgICBub2RlLnByb3BlcnRpZXMucHVzaCh0aGlzLmZpbmlzaE5vZGUocHJvcCwgXCJQcm9wZXJ0eVwiKSk7XG4gICAgdGhpcy5lYXQodHQuY29tbWEpO1xuICB9XG4gIHRoaXMucG9wQ3goKTtcbiAgaWYgKCF0aGlzLmVhdCh0dC5icmFjZVIpKSB7XG4gICAgLy8gSWYgdGhlcmUgaXMgbm8gY2xvc2luZyBicmFjZSwgbWFrZSB0aGUgbm9kZSBzcGFuIHRvIHRoZSBzdGFydFxuICAgIC8vIG9mIHRoZSBuZXh0IHRva2VuICh0aGlzIGlzIHVzZWZ1bCBmb3IgVGVybilcbiAgICB0aGlzLmxhc3QuZW5kID0gdGhpcy50b2suc3RhcnQ7XG4gICAgaWYgKHRoaXMub3B0aW9ucy5sb2NhdGlvbnMpIHRoaXMubGFzdC5sb2MuZW5kID0gdGhpcy50b2subG9jLnN0YXJ0O1xuICB9XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJPYmplY3RFeHByZXNzaW9uXCIpO1xufTtcblxubHAucGFyc2VQcm9wZXJ0eU5hbWUgPSBmdW5jdGlvbiAocHJvcCkge1xuICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYpIHtcbiAgICBpZiAodGhpcy5lYXQodHQuYnJhY2tldEwpKSB7XG4gICAgICBwcm9wLmNvbXB1dGVkID0gdHJ1ZTtcbiAgICAgIHByb3Aua2V5ID0gdGhpcy5wYXJzZUV4cHJlc3Npb24oKTtcbiAgICAgIHRoaXMuZXhwZWN0KHR0LmJyYWNrZXRSKTtcbiAgICAgIHJldHVybjtcbiAgICB9IGVsc2Uge1xuICAgICAgcHJvcC5jb21wdXRlZCA9IGZhbHNlO1xuICAgIH1cbiAgfVxuICB2YXIga2V5ID0gdGhpcy50b2sudHlwZSA9PT0gdHQubnVtIHx8IHRoaXMudG9rLnR5cGUgPT09IHR0LnN0cmluZyA/IHRoaXMucGFyc2VFeHByQXRvbSgpIDogdGhpcy5wYXJzZUlkZW50KCk7XG4gIHByb3Aua2V5ID0ga2V5IHx8IHRoaXMuZHVtbXlJZGVudCgpO1xufTtcblxubHAucGFyc2VQcm9wZXJ0eUFjY2Vzc29yID0gZnVuY3Rpb24gKCkge1xuICBpZiAodGhpcy50b2sudHlwZSA9PT0gdHQubmFtZSB8fCB0aGlzLnRvay50eXBlLmtleXdvcmQpIHJldHVybiB0aGlzLnBhcnNlSWRlbnQoKTtcbn07XG5cbmxwLnBhcnNlSWRlbnQgPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBuYW1lID0gdGhpcy50b2sudHlwZSA9PT0gdHQubmFtZSA/IHRoaXMudG9rLnZhbHVlIDogdGhpcy50b2sudHlwZS5rZXl3b3JkO1xuICBpZiAoIW5hbWUpIHJldHVybiB0aGlzLmR1bW15SWRlbnQoKTtcbiAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICB0aGlzLm5leHQoKTtcbiAgbm9kZS5uYW1lID0gbmFtZTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIklkZW50aWZpZXJcIik7XG59O1xuXG5scC5pbml0RnVuY3Rpb24gPSBmdW5jdGlvbiAobm9kZSkge1xuICBub2RlLmlkID0gbnVsbDtcbiAgbm9kZS5wYXJhbXMgPSBbXTtcbiAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KSB7XG4gICAgbm9kZS5nZW5lcmF0b3IgPSBmYWxzZTtcbiAgICBub2RlLmV4cHJlc3Npb24gPSBmYWxzZTtcbiAgfVxufTtcblxuLy8gQ29udmVydCBleGlzdGluZyBleHByZXNzaW9uIGF0b20gdG8gYXNzaWduYWJsZSBwYXR0ZXJuXG4vLyBpZiBwb3NzaWJsZS5cblxubHAudG9Bc3NpZ25hYmxlID0gZnVuY3Rpb24gKG5vZGUsIGJpbmRpbmcpIHtcbiAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2ICYmIG5vZGUpIHtcbiAgICBzd2l0Y2ggKG5vZGUudHlwZSkge1xuICAgICAgY2FzZSBcIk9iamVjdEV4cHJlc3Npb25cIjpcbiAgICAgICAgbm9kZS50eXBlID0gXCJPYmplY3RQYXR0ZXJuXCI7XG4gICAgICAgIHZhciBwcm9wcyA9IG5vZGUucHJvcGVydGllcztcbiAgICAgICAgZm9yICh2YXIgaSA9IDA7IGkgPCBwcm9wcy5sZW5ndGg7IGkrKykge1xuICAgICAgICAgIHRoaXMudG9Bc3NpZ25hYmxlKHByb3BzW2ldLnZhbHVlLCBiaW5kaW5nKTtcbiAgICAgICAgfWJyZWFrO1xuXG4gICAgICBjYXNlIFwiQXJyYXlFeHByZXNzaW9uXCI6XG4gICAgICAgIG5vZGUudHlwZSA9IFwiQXJyYXlQYXR0ZXJuXCI7XG4gICAgICAgIHRoaXMudG9Bc3NpZ25hYmxlTGlzdChub2RlLmVsZW1lbnRzLCBiaW5kaW5nKTtcbiAgICAgICAgYnJlYWs7XG5cbiAgICAgIGNhc2UgXCJTcHJlYWRFbGVtZW50XCI6XG4gICAgICAgIG5vZGUudHlwZSA9IFwiUmVzdEVsZW1lbnRcIjtcbiAgICAgICAgbm9kZS5hcmd1bWVudCA9IHRoaXMudG9Bc3NpZ25hYmxlKG5vZGUuYXJndW1lbnQsIGJpbmRpbmcpO1xuICAgICAgICBicmVhaztcblxuICAgICAgY2FzZSBcIkFzc2lnbm1lbnRFeHByZXNzaW9uXCI6XG4gICAgICAgIG5vZGUudHlwZSA9IFwiQXNzaWdubWVudFBhdHRlcm5cIjtcbiAgICAgICAgYnJlYWs7XG4gICAgfVxuICB9XG4gIHJldHVybiB0aGlzLmNoZWNrTFZhbChub2RlLCBiaW5kaW5nKTtcbn07XG5cbmxwLnRvQXNzaWduYWJsZUxpc3QgPSBmdW5jdGlvbiAoZXhwckxpc3QsIGJpbmRpbmcpIHtcbiAgZm9yICh2YXIgaSA9IDA7IGkgPCBleHByTGlzdC5sZW5ndGg7IGkrKykge1xuICAgIGV4cHJMaXN0W2ldID0gdGhpcy50b0Fzc2lnbmFibGUoZXhwckxpc3RbaV0sIGJpbmRpbmcpO1xuICB9cmV0dXJuIGV4cHJMaXN0O1xufTtcblxubHAucGFyc2VGdW5jdGlvblBhcmFtcyA9IGZ1bmN0aW9uIChwYXJhbXMpIHtcbiAgcGFyYW1zID0gdGhpcy5wYXJzZUV4cHJMaXN0KHR0LnBhcmVuUik7XG4gIHJldHVybiB0aGlzLnRvQXNzaWduYWJsZUxpc3QocGFyYW1zLCB0cnVlKTtcbn07XG5cbmxwLnBhcnNlTWV0aG9kID0gZnVuY3Rpb24gKGlzR2VuZXJhdG9yKSB7XG4gIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgdGhpcy5pbml0RnVuY3Rpb24obm9kZSk7XG4gIG5vZGUucGFyYW1zID0gdGhpcy5wYXJzZUZ1bmN0aW9uUGFyYW1zKCk7XG4gIG5vZGUuZ2VuZXJhdG9yID0gaXNHZW5lcmF0b3IgfHwgZmFsc2U7XG4gIG5vZGUuZXhwcmVzc2lvbiA9IHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2ICYmIHRoaXMudG9rLnR5cGUgIT09IHR0LmJyYWNlTDtcbiAgbm9kZS5ib2R5ID0gbm9kZS5leHByZXNzaW9uID8gdGhpcy5wYXJzZU1heWJlQXNzaWduKCkgOiB0aGlzLnBhcnNlQmxvY2soKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkZ1bmN0aW9uRXhwcmVzc2lvblwiKTtcbn07XG5cbmxwLnBhcnNlQXJyb3dFeHByZXNzaW9uID0gZnVuY3Rpb24gKG5vZGUsIHBhcmFtcykge1xuICB0aGlzLmluaXRGdW5jdGlvbihub2RlKTtcbiAgbm9kZS5wYXJhbXMgPSB0aGlzLnRvQXNzaWduYWJsZUxpc3QocGFyYW1zLCB0cnVlKTtcbiAgbm9kZS5leHByZXNzaW9uID0gdGhpcy50b2sudHlwZSAhPT0gdHQuYnJhY2VMO1xuICBub2RlLmJvZHkgPSBub2RlLmV4cHJlc3Npb24gPyB0aGlzLnBhcnNlTWF5YmVBc3NpZ24oKSA6IHRoaXMucGFyc2VCbG9jaygpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiQXJyb3dGdW5jdGlvbkV4cHJlc3Npb25cIik7XG59O1xuXG5scC5wYXJzZUV4cHJMaXN0ID0gZnVuY3Rpb24gKGNsb3NlLCBhbGxvd0VtcHR5KSB7XG4gIHRoaXMucHVzaEN4KCk7XG4gIHZhciBpbmRlbnQgPSB0aGlzLmN1ckluZGVudCxcbiAgICAgIGxpbmUgPSB0aGlzLmN1ckxpbmVTdGFydCxcbiAgICAgIGVsdHMgPSBbXTtcbiAgdGhpcy5uZXh0KCk7IC8vIE9wZW5pbmcgYnJhY2tldFxuICB3aGlsZSAoIXRoaXMuY2xvc2VzKGNsb3NlLCBpbmRlbnQgKyAxLCBsaW5lKSkge1xuICAgIGlmICh0aGlzLmVhdCh0dC5jb21tYSkpIHtcbiAgICAgIGVsdHMucHVzaChhbGxvd0VtcHR5ID8gbnVsbCA6IHRoaXMuZHVtbXlJZGVudCgpKTtcbiAgICAgIGNvbnRpbnVlO1xuICAgIH1cbiAgICB2YXIgZWx0ID0gdGhpcy5wYXJzZU1heWJlQXNzaWduKCk7XG4gICAgaWYgKGlzRHVtbXkoZWx0KSkge1xuICAgICAgaWYgKHRoaXMuY2xvc2VzKGNsb3NlLCBpbmRlbnQsIGxpbmUpKSBicmVhaztcbiAgICAgIHRoaXMubmV4dCgpO1xuICAgIH0gZWxzZSB7XG4gICAgICBlbHRzLnB1c2goZWx0KTtcbiAgICB9XG4gICAgdGhpcy5lYXQodHQuY29tbWEpO1xuICB9XG4gIHRoaXMucG9wQ3goKTtcbiAgaWYgKCF0aGlzLmVhdChjbG9zZSkpIHtcbiAgICAvLyBJZiB0aGVyZSBpcyBubyBjbG9zaW5nIGJyYWNlLCBtYWtlIHRoZSBub2RlIHNwYW4gdG8gdGhlIHN0YXJ0XG4gICAgLy8gb2YgdGhlIG5leHQgdG9rZW4gKHRoaXMgaXMgdXNlZnVsIGZvciBUZXJuKVxuICAgIHRoaXMubGFzdC5lbmQgPSB0aGlzLnRvay5zdGFydDtcbiAgICBpZiAodGhpcy5vcHRpb25zLmxvY2F0aW9ucykgdGhpcy5sYXN0LmxvYy5lbmQgPSB0aGlzLnRvay5sb2Muc3RhcnQ7XG4gIH1cbiAgcmV0dXJuIGVsdHM7XG59O1xuXG59LHtcIi4uXCI6MyxcIi4vcGFyc2V1dGlsXCI6NSxcIi4vc3RhdGVcIjo2fV0sNTpbZnVuY3Rpb24oX2RlcmVxXyxtb2R1bGUsZXhwb3J0cyl7XG5cInVzZSBzdHJpY3RcIjtcblxuZXhwb3J0cy5pc0R1bW15ID0gaXNEdW1teTtcbmV4cG9ydHMuX19lc01vZHVsZSA9IHRydWU7XG5cbnZhciBMb29zZVBhcnNlciA9IF9kZXJlcV8oXCIuL3N0YXRlXCIpLkxvb3NlUGFyc2VyO1xuXG52YXIgXyA9IF9kZXJlcV8oXCIuLlwiKTtcblxudmFyIE5vZGUgPSBfLk5vZGU7XG52YXIgU291cmNlTG9jYXRpb24gPSBfLlNvdXJjZUxvY2F0aW9uO1xudmFyIGxpbmVCcmVhayA9IF8ubGluZUJyZWFrO1xudmFyIGlzTmV3TGluZSA9IF8uaXNOZXdMaW5lO1xudmFyIHR0ID0gXy50b2tUeXBlcztcblxudmFyIGxwID0gTG9vc2VQYXJzZXIucHJvdG90eXBlO1xuXG5scC5zdGFydE5vZGUgPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBub2RlID0gbmV3IE5vZGUoKTtcbiAgbm9kZS5zdGFydCA9IHRoaXMudG9rLnN0YXJ0O1xuICBpZiAodGhpcy5vcHRpb25zLmxvY2F0aW9ucykgbm9kZS5sb2MgPSBuZXcgU291cmNlTG9jYXRpb24odGhpcy50b2tzLCB0aGlzLnRvay5sb2Muc3RhcnQpO1xuICBpZiAodGhpcy5vcHRpb25zLmRpcmVjdFNvdXJjZUZpbGUpIG5vZGUuc291cmNlRmlsZSA9IHRoaXMub3B0aW9ucy5kaXJlY3RTb3VyY2VGaWxlO1xuICBpZiAodGhpcy5vcHRpb25zLnJhbmdlcykgbm9kZS5yYW5nZSA9IFt0aGlzLnRvay5zdGFydCwgMF07XG4gIHJldHVybiBub2RlO1xufTtcblxubHAuc3RvcmVDdXJyZW50UG9zID0gZnVuY3Rpb24gKCkge1xuICByZXR1cm4gdGhpcy5vcHRpb25zLmxvY2F0aW9ucyA/IFt0aGlzLnRvay5zdGFydCwgdGhpcy50b2subG9jLnN0YXJ0XSA6IHRoaXMudG9rLnN0YXJ0O1xufTtcblxubHAuc3RhcnROb2RlQXQgPSBmdW5jdGlvbiAocG9zKSB7XG4gIHZhciBub2RlID0gbmV3IE5vZGUoKTtcbiAgaWYgKHRoaXMub3B0aW9ucy5sb2NhdGlvbnMpIHtcbiAgICBub2RlLnN0YXJ0ID0gcG9zWzBdO1xuICAgIG5vZGUubG9jID0gbmV3IFNvdXJjZUxvY2F0aW9uKHRoaXMudG9rcywgcG9zWzFdKTtcbiAgICBwb3MgPSBwb3NbMF07XG4gIH0gZWxzZSB7XG4gICAgbm9kZS5zdGFydCA9IHBvcztcbiAgfVxuICBpZiAodGhpcy5vcHRpb25zLmRpcmVjdFNvdXJjZUZpbGUpIG5vZGUuc291cmNlRmlsZSA9IHRoaXMub3B0aW9ucy5kaXJlY3RTb3VyY2VGaWxlO1xuICBpZiAodGhpcy5vcHRpb25zLnJhbmdlcykgbm9kZS5yYW5nZSA9IFtwb3MsIDBdO1xuICByZXR1cm4gbm9kZTtcbn07XG5cbmxwLmZpbmlzaE5vZGUgPSBmdW5jdGlvbiAobm9kZSwgdHlwZSkge1xuICBub2RlLnR5cGUgPSB0eXBlO1xuICBub2RlLmVuZCA9IHRoaXMubGFzdC5lbmQ7XG4gIGlmICh0aGlzLm9wdGlvbnMubG9jYXRpb25zKSBub2RlLmxvYy5lbmQgPSB0aGlzLmxhc3QubG9jLmVuZDtcbiAgaWYgKHRoaXMub3B0aW9ucy5yYW5nZXMpIG5vZGUucmFuZ2VbMV0gPSB0aGlzLmxhc3QuZW5kO1xuICByZXR1cm4gbm9kZTtcbn07XG5cbmxwLmR1bW15SWRlbnQgPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBkdW1teSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gIGR1bW15Lm5hbWUgPSBcIuKcllwiO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKGR1bW15LCBcIklkZW50aWZpZXJcIik7XG59O1xuXG5mdW5jdGlvbiBpc0R1bW15KG5vZGUpIHtcbiAgcmV0dXJuIG5vZGUubmFtZSA9PSBcIuKcllwiO1xufVxuXG5scC5lYXQgPSBmdW5jdGlvbiAodHlwZSkge1xuICBpZiAodGhpcy50b2sudHlwZSA9PT0gdHlwZSkge1xuICAgIHRoaXMubmV4dCgpO1xuICAgIHJldHVybiB0cnVlO1xuICB9IGVsc2Uge1xuICAgIHJldHVybiBmYWxzZTtcbiAgfVxufTtcblxubHAuaXNDb250ZXh0dWFsID0gZnVuY3Rpb24gKG5hbWUpIHtcbiAgcmV0dXJuIHRoaXMudG9rLnR5cGUgPT09IHR0Lm5hbWUgJiYgdGhpcy50b2sudmFsdWUgPT09IG5hbWU7XG59O1xuXG5scC5lYXRDb250ZXh0dWFsID0gZnVuY3Rpb24gKG5hbWUpIHtcbiAgcmV0dXJuIHRoaXMudG9rLnZhbHVlID09PSBuYW1lICYmIHRoaXMuZWF0KHR0Lm5hbWUpO1xufTtcblxubHAuY2FuSW5zZXJ0U2VtaWNvbG9uID0gZnVuY3Rpb24gKCkge1xuICByZXR1cm4gdGhpcy50b2sudHlwZSA9PT0gdHQuZW9mIHx8IHRoaXMudG9rLnR5cGUgPT09IHR0LmJyYWNlUiB8fCBsaW5lQnJlYWsudGVzdCh0aGlzLmlucHV0LnNsaWNlKHRoaXMubGFzdC5lbmQsIHRoaXMudG9rLnN0YXJ0KSk7XG59O1xuXG5scC5zZW1pY29sb24gPSBmdW5jdGlvbiAoKSB7XG4gIHJldHVybiB0aGlzLmVhdCh0dC5zZW1pKTtcbn07XG5cbmxwLmV4cGVjdCA9IGZ1bmN0aW9uICh0eXBlKSB7XG4gIGlmICh0aGlzLmVhdCh0eXBlKSkgcmV0dXJuIHRydWU7XG4gIGZvciAodmFyIGkgPSAxOyBpIDw9IDI7IGkrKykge1xuICAgIGlmICh0aGlzLmxvb2tBaGVhZChpKS50eXBlID09IHR5cGUpIHtcbiAgICAgIGZvciAodmFyIGogPSAwOyBqIDwgaTsgaisrKSB7XG4gICAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgfXJldHVybiB0cnVlO1xuICAgIH1cbiAgfVxufTtcblxubHAucHVzaEN4ID0gZnVuY3Rpb24gKCkge1xuICB0aGlzLmNvbnRleHQucHVzaCh0aGlzLmN1ckluZGVudCk7XG59O1xubHAucG9wQ3ggPSBmdW5jdGlvbiAoKSB7XG4gIHRoaXMuY3VySW5kZW50ID0gdGhpcy5jb250ZXh0LnBvcCgpO1xufTtcblxubHAubGluZUVuZCA9IGZ1bmN0aW9uIChwb3MpIHtcbiAgd2hpbGUgKHBvcyA8IHRoaXMuaW5wdXQubGVuZ3RoICYmICFpc05ld0xpbmUodGhpcy5pbnB1dC5jaGFyQ29kZUF0KHBvcykpKSArK3BvcztcbiAgcmV0dXJuIHBvcztcbn07XG5cbmxwLmluZGVudGF0aW9uQWZ0ZXIgPSBmdW5jdGlvbiAocG9zKSB7XG4gIGZvciAodmFyIGNvdW50ID0gMDs7ICsrcG9zKSB7XG4gICAgdmFyIGNoID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHBvcyk7XG4gICAgaWYgKGNoID09PSAzMikgKytjb3VudDtlbHNlIGlmIChjaCA9PT0gOSkgY291bnQgKz0gdGhpcy5vcHRpb25zLnRhYlNpemU7ZWxzZSByZXR1cm4gY291bnQ7XG4gIH1cbn07XG5cbmxwLmNsb3NlcyA9IGZ1bmN0aW9uIChjbG9zZVRvaywgaW5kZW50LCBsaW5lLCBibG9ja0hldXJpc3RpYykge1xuICBpZiAodGhpcy50b2sudHlwZSA9PT0gY2xvc2VUb2sgfHwgdGhpcy50b2sudHlwZSA9PT0gdHQuZW9mKSByZXR1cm4gdHJ1ZTtcbiAgcmV0dXJuIGxpbmUgIT0gdGhpcy5jdXJMaW5lU3RhcnQgJiYgdGhpcy5jdXJJbmRlbnQgPCBpbmRlbnQgJiYgdGhpcy50b2tlblN0YXJ0c0xpbmUoKSAmJiAoIWJsb2NrSGV1cmlzdGljIHx8IHRoaXMubmV4dExpbmVTdGFydCA+PSB0aGlzLmlucHV0Lmxlbmd0aCB8fCB0aGlzLmluZGVudGF0aW9uQWZ0ZXIodGhpcy5uZXh0TGluZVN0YXJ0KSA8IGluZGVudCk7XG59O1xuXG5scC50b2tlblN0YXJ0c0xpbmUgPSBmdW5jdGlvbiAoKSB7XG4gIGZvciAodmFyIHAgPSB0aGlzLnRvay5zdGFydCAtIDE7IHAgPj0gdGhpcy5jdXJMaW5lU3RhcnQ7IC0tcCkge1xuICAgIHZhciBjaCA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdChwKTtcbiAgICBpZiAoY2ggIT09IDkgJiYgY2ggIT09IDMyKSByZXR1cm4gZmFsc2U7XG4gIH1cbiAgcmV0dXJuIHRydWU7XG59O1xuXG59LHtcIi4uXCI6MyxcIi4vc3RhdGVcIjo2fV0sNjpbZnVuY3Rpb24oX2RlcmVxXyxtb2R1bGUsZXhwb3J0cyl7XG5cInVzZSBzdHJpY3RcIjtcblxuZXhwb3J0cy5Mb29zZVBhcnNlciA9IExvb3NlUGFyc2VyO1xuZXhwb3J0cy5fX2VzTW9kdWxlID0gdHJ1ZTtcblxudmFyIF8gPSBfZGVyZXFfKFwiLi5cIik7XG5cbnZhciB0b2tlbml6ZXIgPSBfLnRva2VuaXplcjtcbnZhciBTb3VyY2VMb2NhdGlvbiA9IF8uU291cmNlTG9jYXRpb247XG52YXIgdHQgPSBfLnRva1R5cGVzO1xuXG5mdW5jdGlvbiBMb29zZVBhcnNlcihpbnB1dCwgb3B0aW9ucykge1xuICB0aGlzLnRva3MgPSB0b2tlbml6ZXIoaW5wdXQsIG9wdGlvbnMpO1xuICB0aGlzLm9wdGlvbnMgPSB0aGlzLnRva3Mub3B0aW9ucztcbiAgdGhpcy5pbnB1dCA9IHRoaXMudG9rcy5pbnB1dDtcbiAgdGhpcy50b2sgPSB0aGlzLmxhc3QgPSB7IHR5cGU6IHR0LmVvZiwgc3RhcnQ6IDAsIGVuZDogMCB9O1xuICBpZiAodGhpcy5vcHRpb25zLmxvY2F0aW9ucykge1xuICAgIHZhciBoZXJlID0gdGhpcy50b2tzLmN1clBvc2l0aW9uKCk7XG4gICAgdGhpcy50b2subG9jID0gbmV3IFNvdXJjZUxvY2F0aW9uKHRoaXMudG9rcywgaGVyZSwgaGVyZSk7XG4gIH1cbiAgdGhpcy5haGVhZCA9IFtdOyAvLyBUb2tlbnMgYWhlYWRcbiAgdGhpcy5jb250ZXh0ID0gW107IC8vIEluZGVudGF0aW9uIGNvbnRleHRlZFxuICB0aGlzLmN1ckluZGVudCA9IDA7XG4gIHRoaXMuY3VyTGluZVN0YXJ0ID0gMDtcbiAgdGhpcy5uZXh0TGluZVN0YXJ0ID0gdGhpcy5saW5lRW5kKHRoaXMuY3VyTGluZVN0YXJ0KSArIDE7XG59XG5cbn0se1wiLi5cIjozfV0sNzpbZnVuY3Rpb24oX2RlcmVxXyxtb2R1bGUsZXhwb3J0cyl7XG5cInVzZSBzdHJpY3RcIjtcblxudmFyIExvb3NlUGFyc2VyID0gX2RlcmVxXyhcIi4vc3RhdGVcIikuTG9vc2VQYXJzZXI7XG5cbnZhciBpc0R1bW15ID0gX2RlcmVxXyhcIi4vcGFyc2V1dGlsXCIpLmlzRHVtbXk7XG5cbnZhciBfID0gX2RlcmVxXyhcIi4uXCIpO1xuXG52YXIgZ2V0TGluZUluZm8gPSBfLmdldExpbmVJbmZvO1xudmFyIHR0ID0gXy50b2tUeXBlcztcblxudmFyIGxwID0gTG9vc2VQYXJzZXIucHJvdG90eXBlO1xuXG5scC5wYXJzZVRvcExldmVsID0gZnVuY3Rpb24gKCkge1xuICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlQXQodGhpcy5vcHRpb25zLmxvY2F0aW9ucyA/IFswLCBnZXRMaW5lSW5mbyh0aGlzLmlucHV0LCAwKV0gOiAwKTtcbiAgbm9kZS5ib2R5ID0gW107XG4gIHdoaWxlICh0aGlzLnRvay50eXBlICE9PSB0dC5lb2YpIG5vZGUuYm9keS5wdXNoKHRoaXMucGFyc2VTdGF0ZW1lbnQoKSk7XG4gIHRoaXMubGFzdCA9IHRoaXMudG9rO1xuICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYpIHtcbiAgICBub2RlLnNvdXJjZVR5cGUgPSB0aGlzLm9wdGlvbnMuc291cmNlVHlwZTtcbiAgfVxuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiUHJvZ3JhbVwiKTtcbn07XG5cbmxwLnBhcnNlU3RhdGVtZW50ID0gZnVuY3Rpb24gKCkge1xuICB2YXIgc3RhcnR0eXBlID0gdGhpcy50b2sudHlwZSxcbiAgICAgIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuXG4gIHN3aXRjaCAoc3RhcnR0eXBlKSB7XG4gICAgY2FzZSB0dC5fYnJlYWs6Y2FzZSB0dC5fY29udGludWU6XG4gICAgICB0aGlzLm5leHQoKTtcbiAgICAgIHZhciBpc0JyZWFrID0gc3RhcnR0eXBlID09PSB0dC5fYnJlYWs7XG4gICAgICBpZiAodGhpcy5zZW1pY29sb24oKSB8fCB0aGlzLmNhbkluc2VydFNlbWljb2xvbigpKSB7XG4gICAgICAgIG5vZGUubGFiZWwgPSBudWxsO1xuICAgICAgfSBlbHNlIHtcbiAgICAgICAgbm9kZS5sYWJlbCA9IHRoaXMudG9rLnR5cGUgPT09IHR0Lm5hbWUgPyB0aGlzLnBhcnNlSWRlbnQoKSA6IG51bGw7XG4gICAgICAgIHRoaXMuc2VtaWNvbG9uKCk7XG4gICAgICB9XG4gICAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIGlzQnJlYWsgPyBcIkJyZWFrU3RhdGVtZW50XCIgOiBcIkNvbnRpbnVlU3RhdGVtZW50XCIpO1xuXG4gICAgY2FzZSB0dC5fZGVidWdnZXI6XG4gICAgICB0aGlzLm5leHQoKTtcbiAgICAgIHRoaXMuc2VtaWNvbG9uKCk7XG4gICAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiRGVidWdnZXJTdGF0ZW1lbnRcIik7XG5cbiAgICBjYXNlIHR0Ll9kbzpcbiAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgbm9kZS5ib2R5ID0gdGhpcy5wYXJzZVN0YXRlbWVudCgpO1xuICAgICAgbm9kZS50ZXN0ID0gdGhpcy5lYXQodHQuX3doaWxlKSA/IHRoaXMucGFyc2VQYXJlbkV4cHJlc3Npb24oKSA6IHRoaXMuZHVtbXlJZGVudCgpO1xuICAgICAgdGhpcy5zZW1pY29sb24oKTtcbiAgICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJEb1doaWxlU3RhdGVtZW50XCIpO1xuXG4gICAgY2FzZSB0dC5fZm9yOlxuICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICB0aGlzLnB1c2hDeCgpO1xuICAgICAgdGhpcy5leHBlY3QodHQucGFyZW5MKTtcbiAgICAgIGlmICh0aGlzLnRvay50eXBlID09PSB0dC5zZW1pKSByZXR1cm4gdGhpcy5wYXJzZUZvcihub2RlLCBudWxsKTtcbiAgICAgIGlmICh0aGlzLnRvay50eXBlID09PSB0dC5fdmFyIHx8IHRoaXMudG9rLnR5cGUgPT09IHR0Ll9sZXQgfHwgdGhpcy50b2sudHlwZSA9PT0gdHQuX2NvbnN0KSB7XG4gICAgICAgIHZhciBfaW5pdCA9IHRoaXMucGFyc2VWYXIodHJ1ZSk7XG4gICAgICAgIGlmIChfaW5pdC5kZWNsYXJhdGlvbnMubGVuZ3RoID09PSAxICYmICh0aGlzLnRvay50eXBlID09PSB0dC5faW4gfHwgdGhpcy5pc0NvbnRleHR1YWwoXCJvZlwiKSkpIHtcbiAgICAgICAgICByZXR1cm4gdGhpcy5wYXJzZUZvckluKG5vZGUsIF9pbml0KTtcbiAgICAgICAgfVxuICAgICAgICByZXR1cm4gdGhpcy5wYXJzZUZvcihub2RlLCBfaW5pdCk7XG4gICAgICB9XG4gICAgICB2YXIgaW5pdCA9IHRoaXMucGFyc2VFeHByZXNzaW9uKHRydWUpO1xuICAgICAgaWYgKHRoaXMudG9rLnR5cGUgPT09IHR0Ll9pbiB8fCB0aGlzLmlzQ29udGV4dHVhbChcIm9mXCIpKSByZXR1cm4gdGhpcy5wYXJzZUZvckluKG5vZGUsIHRoaXMudG9Bc3NpZ25hYmxlKGluaXQpKTtcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlRm9yKG5vZGUsIGluaXQpO1xuXG4gICAgY2FzZSB0dC5fZnVuY3Rpb246XG4gICAgICB0aGlzLm5leHQoKTtcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlRnVuY3Rpb24obm9kZSwgdHJ1ZSk7XG5cbiAgICBjYXNlIHR0Ll9pZjpcbiAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgbm9kZS50ZXN0ID0gdGhpcy5wYXJzZVBhcmVuRXhwcmVzc2lvbigpO1xuICAgICAgbm9kZS5jb25zZXF1ZW50ID0gdGhpcy5wYXJzZVN0YXRlbWVudCgpO1xuICAgICAgbm9kZS5hbHRlcm5hdGUgPSB0aGlzLmVhdCh0dC5fZWxzZSkgPyB0aGlzLnBhcnNlU3RhdGVtZW50KCkgOiBudWxsO1xuICAgICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIklmU3RhdGVtZW50XCIpO1xuXG4gICAgY2FzZSB0dC5fcmV0dXJuOlxuICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICBpZiAodGhpcy5lYXQodHQuc2VtaSkgfHwgdGhpcy5jYW5JbnNlcnRTZW1pY29sb24oKSkgbm9kZS5hcmd1bWVudCA9IG51bGw7ZWxzZSB7XG4gICAgICAgIG5vZGUuYXJndW1lbnQgPSB0aGlzLnBhcnNlRXhwcmVzc2lvbigpO3RoaXMuc2VtaWNvbG9uKCk7XG4gICAgICB9XG4gICAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiUmV0dXJuU3RhdGVtZW50XCIpO1xuXG4gICAgY2FzZSB0dC5fc3dpdGNoOlxuICAgICAgdmFyIGJsb2NrSW5kZW50ID0gdGhpcy5jdXJJbmRlbnQsXG4gICAgICAgICAgbGluZSA9IHRoaXMuY3VyTGluZVN0YXJ0O1xuICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICBub2RlLmRpc2NyaW1pbmFudCA9IHRoaXMucGFyc2VQYXJlbkV4cHJlc3Npb24oKTtcbiAgICAgIG5vZGUuY2FzZXMgPSBbXTtcbiAgICAgIHRoaXMucHVzaEN4KCk7XG4gICAgICB0aGlzLmV4cGVjdCh0dC5icmFjZUwpO1xuXG4gICAgICB2YXIgY3VyID0gdW5kZWZpbmVkO1xuICAgICAgd2hpbGUgKCF0aGlzLmNsb3Nlcyh0dC5icmFjZVIsIGJsb2NrSW5kZW50LCBsaW5lLCB0cnVlKSkge1xuICAgICAgICBpZiAodGhpcy50b2sudHlwZSA9PT0gdHQuX2Nhc2UgfHwgdGhpcy50b2sudHlwZSA9PT0gdHQuX2RlZmF1bHQpIHtcbiAgICAgICAgICB2YXIgaXNDYXNlID0gdGhpcy50b2sudHlwZSA9PT0gdHQuX2Nhc2U7XG4gICAgICAgICAgaWYgKGN1cikgdGhpcy5maW5pc2hOb2RlKGN1ciwgXCJTd2l0Y2hDYXNlXCIpO1xuICAgICAgICAgIG5vZGUuY2FzZXMucHVzaChjdXIgPSB0aGlzLnN0YXJ0Tm9kZSgpKTtcbiAgICAgICAgICBjdXIuY29uc2VxdWVudCA9IFtdO1xuICAgICAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgICAgIGlmIChpc0Nhc2UpIGN1ci50ZXN0ID0gdGhpcy5wYXJzZUV4cHJlc3Npb24oKTtlbHNlIGN1ci50ZXN0ID0gbnVsbDtcbiAgICAgICAgICB0aGlzLmV4cGVjdCh0dC5jb2xvbik7XG4gICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgaWYgKCFjdXIpIHtcbiAgICAgICAgICAgIG5vZGUuY2FzZXMucHVzaChjdXIgPSB0aGlzLnN0YXJ0Tm9kZSgpKTtcbiAgICAgICAgICAgIGN1ci5jb25zZXF1ZW50ID0gW107XG4gICAgICAgICAgICBjdXIudGVzdCA9IG51bGw7XG4gICAgICAgICAgfVxuICAgICAgICAgIGN1ci5jb25zZXF1ZW50LnB1c2godGhpcy5wYXJzZVN0YXRlbWVudCgpKTtcbiAgICAgICAgfVxuICAgICAgfVxuICAgICAgaWYgKGN1cikgdGhpcy5maW5pc2hOb2RlKGN1ciwgXCJTd2l0Y2hDYXNlXCIpO1xuICAgICAgdGhpcy5wb3BDeCgpO1xuICAgICAgdGhpcy5lYXQodHQuYnJhY2VSKTtcbiAgICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJTd2l0Y2hTdGF0ZW1lbnRcIik7XG5cbiAgICBjYXNlIHR0Ll90aHJvdzpcbiAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgbm9kZS5hcmd1bWVudCA9IHRoaXMucGFyc2VFeHByZXNzaW9uKCk7XG4gICAgICB0aGlzLnNlbWljb2xvbigpO1xuICAgICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIlRocm93U3RhdGVtZW50XCIpO1xuXG4gICAgY2FzZSB0dC5fdHJ5OlxuICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICBub2RlLmJsb2NrID0gdGhpcy5wYXJzZUJsb2NrKCk7XG4gICAgICBub2RlLmhhbmRsZXIgPSBudWxsO1xuICAgICAgaWYgKHRoaXMudG9rLnR5cGUgPT09IHR0Ll9jYXRjaCkge1xuICAgICAgICB2YXIgY2xhdXNlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICAgIHRoaXMuZXhwZWN0KHR0LnBhcmVuTCk7XG4gICAgICAgIGNsYXVzZS5wYXJhbSA9IHRoaXMudG9Bc3NpZ25hYmxlKHRoaXMucGFyc2VFeHByQXRvbSgpLCB0cnVlKTtcbiAgICAgICAgdGhpcy5leHBlY3QodHQucGFyZW5SKTtcbiAgICAgICAgY2xhdXNlLmd1YXJkID0gbnVsbDtcbiAgICAgICAgY2xhdXNlLmJvZHkgPSB0aGlzLnBhcnNlQmxvY2soKTtcbiAgICAgICAgbm9kZS5oYW5kbGVyID0gdGhpcy5maW5pc2hOb2RlKGNsYXVzZSwgXCJDYXRjaENsYXVzZVwiKTtcbiAgICAgIH1cbiAgICAgIG5vZGUuZmluYWxpemVyID0gdGhpcy5lYXQodHQuX2ZpbmFsbHkpID8gdGhpcy5wYXJzZUJsb2NrKCkgOiBudWxsO1xuICAgICAgaWYgKCFub2RlLmhhbmRsZXIgJiYgIW5vZGUuZmluYWxpemVyKSByZXR1cm4gbm9kZS5ibG9jaztcbiAgICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJUcnlTdGF0ZW1lbnRcIik7XG5cbiAgICBjYXNlIHR0Ll92YXI6XG4gICAgY2FzZSB0dC5fbGV0OlxuICAgIGNhc2UgdHQuX2NvbnN0OlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VWYXIoKTtcblxuICAgIGNhc2UgdHQuX3doaWxlOlxuICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICBub2RlLnRlc3QgPSB0aGlzLnBhcnNlUGFyZW5FeHByZXNzaW9uKCk7XG4gICAgICBub2RlLmJvZHkgPSB0aGlzLnBhcnNlU3RhdGVtZW50KCk7XG4gICAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiV2hpbGVTdGF0ZW1lbnRcIik7XG5cbiAgICBjYXNlIHR0Ll93aXRoOlxuICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICBub2RlLm9iamVjdCA9IHRoaXMucGFyc2VQYXJlbkV4cHJlc3Npb24oKTtcbiAgICAgIG5vZGUuYm9keSA9IHRoaXMucGFyc2VTdGF0ZW1lbnQoKTtcbiAgICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJXaXRoU3RhdGVtZW50XCIpO1xuXG4gICAgY2FzZSB0dC5icmFjZUw6XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZUJsb2NrKCk7XG5cbiAgICBjYXNlIHR0LnNlbWk6XG4gICAgICB0aGlzLm5leHQoKTtcbiAgICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJFbXB0eVN0YXRlbWVudFwiKTtcblxuICAgIGNhc2UgdHQuX2NsYXNzOlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VDbGFzcyh0cnVlKTtcblxuICAgIGNhc2UgdHQuX2ltcG9ydDpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlSW1wb3J0KCk7XG5cbiAgICBjYXNlIHR0Ll9leHBvcnQ6XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZUV4cG9ydCgpO1xuXG4gICAgZGVmYXVsdDpcbiAgICAgIHZhciBleHByID0gdGhpcy5wYXJzZUV4cHJlc3Npb24oKTtcbiAgICAgIGlmIChpc0R1bW15KGV4cHIpKSB7XG4gICAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgICBpZiAodGhpcy50b2sudHlwZSA9PT0gdHQuZW9mKSByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiRW1wdHlTdGF0ZW1lbnRcIik7XG4gICAgICAgIHJldHVybiB0aGlzLnBhcnNlU3RhdGVtZW50KCk7XG4gICAgICB9IGVsc2UgaWYgKHN0YXJ0dHlwZSA9PT0gdHQubmFtZSAmJiBleHByLnR5cGUgPT09IFwiSWRlbnRpZmllclwiICYmIHRoaXMuZWF0KHR0LmNvbG9uKSkge1xuICAgICAgICBub2RlLmJvZHkgPSB0aGlzLnBhcnNlU3RhdGVtZW50KCk7XG4gICAgICAgIG5vZGUubGFiZWwgPSBleHByO1xuICAgICAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiTGFiZWxlZFN0YXRlbWVudFwiKTtcbiAgICAgIH0gZWxzZSB7XG4gICAgICAgIG5vZGUuZXhwcmVzc2lvbiA9IGV4cHI7XG4gICAgICAgIHRoaXMuc2VtaWNvbG9uKCk7XG4gICAgICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJFeHByZXNzaW9uU3RhdGVtZW50XCIpO1xuICAgICAgfVxuICB9XG59O1xuXG5scC5wYXJzZUJsb2NrID0gZnVuY3Rpb24gKCkge1xuICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gIHRoaXMucHVzaEN4KCk7XG4gIHRoaXMuZXhwZWN0KHR0LmJyYWNlTCk7XG4gIHZhciBibG9ja0luZGVudCA9IHRoaXMuY3VySW5kZW50LFxuICAgICAgbGluZSA9IHRoaXMuY3VyTGluZVN0YXJ0O1xuICBub2RlLmJvZHkgPSBbXTtcbiAgd2hpbGUgKCF0aGlzLmNsb3Nlcyh0dC5icmFjZVIsIGJsb2NrSW5kZW50LCBsaW5lLCB0cnVlKSkgbm9kZS5ib2R5LnB1c2godGhpcy5wYXJzZVN0YXRlbWVudCgpKTtcbiAgdGhpcy5wb3BDeCgpO1xuICB0aGlzLmVhdCh0dC5icmFjZVIpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiQmxvY2tTdGF0ZW1lbnRcIik7XG59O1xuXG5scC5wYXJzZUZvciA9IGZ1bmN0aW9uIChub2RlLCBpbml0KSB7XG4gIG5vZGUuaW5pdCA9IGluaXQ7XG4gIG5vZGUudGVzdCA9IG5vZGUudXBkYXRlID0gbnVsbDtcbiAgaWYgKHRoaXMuZWF0KHR0LnNlbWkpICYmIHRoaXMudG9rLnR5cGUgIT09IHR0LnNlbWkpIG5vZGUudGVzdCA9IHRoaXMucGFyc2VFeHByZXNzaW9uKCk7XG4gIGlmICh0aGlzLmVhdCh0dC5zZW1pKSAmJiB0aGlzLnRvay50eXBlICE9PSB0dC5wYXJlblIpIG5vZGUudXBkYXRlID0gdGhpcy5wYXJzZUV4cHJlc3Npb24oKTtcbiAgdGhpcy5wb3BDeCgpO1xuICB0aGlzLmV4cGVjdCh0dC5wYXJlblIpO1xuICBub2RlLmJvZHkgPSB0aGlzLnBhcnNlU3RhdGVtZW50KCk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJGb3JTdGF0ZW1lbnRcIik7XG59O1xuXG5scC5wYXJzZUZvckluID0gZnVuY3Rpb24gKG5vZGUsIGluaXQpIHtcbiAgdmFyIHR5cGUgPSB0aGlzLnRvay50eXBlID09PSB0dC5faW4gPyBcIkZvckluU3RhdGVtZW50XCIgOiBcIkZvck9mU3RhdGVtZW50XCI7XG4gIHRoaXMubmV4dCgpO1xuICBub2RlLmxlZnQgPSBpbml0O1xuICBub2RlLnJpZ2h0ID0gdGhpcy5wYXJzZUV4cHJlc3Npb24oKTtcbiAgdGhpcy5wb3BDeCgpO1xuICB0aGlzLmV4cGVjdCh0dC5wYXJlblIpO1xuICBub2RlLmJvZHkgPSB0aGlzLnBhcnNlU3RhdGVtZW50KCk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgdHlwZSk7XG59O1xuXG5scC5wYXJzZVZhciA9IGZ1bmN0aW9uIChub0luKSB7XG4gIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgbm9kZS5raW5kID0gdGhpcy50b2sudHlwZS5rZXl3b3JkO1xuICB0aGlzLm5leHQoKTtcbiAgbm9kZS5kZWNsYXJhdGlvbnMgPSBbXTtcbiAgZG8ge1xuICAgIHZhciBkZWNsID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgICBkZWNsLmlkID0gdGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYgPyB0aGlzLnRvQXNzaWduYWJsZSh0aGlzLnBhcnNlRXhwckF0b20oKSwgdHJ1ZSkgOiB0aGlzLnBhcnNlSWRlbnQoKTtcbiAgICBkZWNsLmluaXQgPSB0aGlzLmVhdCh0dC5lcSkgPyB0aGlzLnBhcnNlTWF5YmVBc3NpZ24obm9JbikgOiBudWxsO1xuICAgIG5vZGUuZGVjbGFyYXRpb25zLnB1c2godGhpcy5maW5pc2hOb2RlKGRlY2wsIFwiVmFyaWFibGVEZWNsYXJhdG9yXCIpKTtcbiAgfSB3aGlsZSAodGhpcy5lYXQodHQuY29tbWEpKTtcbiAgaWYgKCFub2RlLmRlY2xhcmF0aW9ucy5sZW5ndGgpIHtcbiAgICB2YXIgZGVjbCA9IHRoaXMuc3RhcnROb2RlKCk7XG4gICAgZGVjbC5pZCA9IHRoaXMuZHVtbXlJZGVudCgpO1xuICAgIG5vZGUuZGVjbGFyYXRpb25zLnB1c2godGhpcy5maW5pc2hOb2RlKGRlY2wsIFwiVmFyaWFibGVEZWNsYXJhdG9yXCIpKTtcbiAgfVxuICBpZiAoIW5vSW4pIHRoaXMuc2VtaWNvbG9uKCk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJWYXJpYWJsZURlY2xhcmF0aW9uXCIpO1xufTtcblxubHAucGFyc2VDbGFzcyA9IGZ1bmN0aW9uIChpc1N0YXRlbWVudCkge1xuICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gIHRoaXMubmV4dCgpO1xuICBpZiAodGhpcy50b2sudHlwZSA9PT0gdHQubmFtZSkgbm9kZS5pZCA9IHRoaXMucGFyc2VJZGVudCgpO2Vsc2UgaWYgKGlzU3RhdGVtZW50KSBub2RlLmlkID0gdGhpcy5kdW1teUlkZW50KCk7ZWxzZSBub2RlLmlkID0gbnVsbDtcbiAgbm9kZS5zdXBlckNsYXNzID0gdGhpcy5lYXQodHQuX2V4dGVuZHMpID8gdGhpcy5wYXJzZUV4cHJlc3Npb24oKSA6IG51bGw7XG4gIG5vZGUuYm9keSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gIG5vZGUuYm9keS5ib2R5ID0gW107XG4gIHRoaXMucHVzaEN4KCk7XG4gIHZhciBpbmRlbnQgPSB0aGlzLmN1ckluZGVudCArIDEsXG4gICAgICBsaW5lID0gdGhpcy5jdXJMaW5lU3RhcnQ7XG4gIHRoaXMuZWF0KHR0LmJyYWNlTCk7XG4gIGlmICh0aGlzLmN1ckluZGVudCArIDEgPCBpbmRlbnQpIHtcbiAgICBpbmRlbnQgPSB0aGlzLmN1ckluZGVudDtsaW5lID0gdGhpcy5jdXJMaW5lU3RhcnQ7XG4gIH1cbiAgd2hpbGUgKCF0aGlzLmNsb3Nlcyh0dC5icmFjZVIsIGluZGVudCwgbGluZSkpIHtcbiAgICBpZiAodGhpcy5zZW1pY29sb24oKSkgY29udGludWU7XG4gICAgdmFyIG1ldGhvZCA9IHRoaXMuc3RhcnROb2RlKCksXG4gICAgICAgIGlzR2VuZXJhdG9yID0gdW5kZWZpbmVkO1xuICAgIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNikge1xuICAgICAgbWV0aG9kW1wic3RhdGljXCJdID0gZmFsc2U7XG4gICAgICBpc0dlbmVyYXRvciA9IHRoaXMuZWF0KHR0LnN0YXIpO1xuICAgIH1cbiAgICB0aGlzLnBhcnNlUHJvcGVydHlOYW1lKG1ldGhvZCk7XG4gICAgaWYgKGlzRHVtbXkobWV0aG9kLmtleSkpIHtcbiAgICAgIGlmIChpc0R1bW15KHRoaXMucGFyc2VNYXliZUFzc2lnbigpKSkgdGhpcy5uZXh0KCk7dGhpcy5lYXQodHQuY29tbWEpO2NvbnRpbnVlO1xuICAgIH1cbiAgICBpZiAobWV0aG9kLmtleS50eXBlID09PSBcIklkZW50aWZpZXJcIiAmJiAhbWV0aG9kLmNvbXB1dGVkICYmIG1ldGhvZC5rZXkubmFtZSA9PT0gXCJzdGF0aWNcIiAmJiAodGhpcy50b2sudHlwZSAhPSB0dC5wYXJlbkwgJiYgdGhpcy50b2sudHlwZSAhPSB0dC5icmFjZUwpKSB7XG4gICAgICBtZXRob2RbXCJzdGF0aWNcIl0gPSB0cnVlO1xuICAgICAgaXNHZW5lcmF0b3IgPSB0aGlzLmVhdCh0dC5zdGFyKTtcbiAgICAgIHRoaXMucGFyc2VQcm9wZXJ0eU5hbWUobWV0aG9kKTtcbiAgICB9IGVsc2Uge1xuICAgICAgbWV0aG9kW1wic3RhdGljXCJdID0gZmFsc2U7XG4gICAgfVxuICAgIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNSAmJiBtZXRob2Qua2V5LnR5cGUgPT09IFwiSWRlbnRpZmllclwiICYmICFtZXRob2QuY29tcHV0ZWQgJiYgKG1ldGhvZC5rZXkubmFtZSA9PT0gXCJnZXRcIiB8fCBtZXRob2Qua2V5Lm5hbWUgPT09IFwic2V0XCIpICYmIHRoaXMudG9rLnR5cGUgIT09IHR0LnBhcmVuTCAmJiB0aGlzLnRvay50eXBlICE9PSB0dC5icmFjZUwpIHtcbiAgICAgIG1ldGhvZC5raW5kID0gbWV0aG9kLmtleS5uYW1lO1xuICAgICAgdGhpcy5wYXJzZVByb3BlcnR5TmFtZShtZXRob2QpO1xuICAgICAgbWV0aG9kLnZhbHVlID0gdGhpcy5wYXJzZU1ldGhvZChmYWxzZSk7XG4gICAgfSBlbHNlIHtcbiAgICAgIGlmICghbWV0aG9kLmNvbXB1dGVkICYmICFtZXRob2RbXCJzdGF0aWNcIl0gJiYgIWlzR2VuZXJhdG9yICYmIChtZXRob2Qua2V5LnR5cGUgPT09IFwiSWRlbnRpZmllclwiICYmIG1ldGhvZC5rZXkubmFtZSA9PT0gXCJjb25zdHJ1Y3RvclwiIHx8IG1ldGhvZC5rZXkudHlwZSA9PT0gXCJMaXRlcmFsXCIgJiYgbWV0aG9kLmtleS52YWx1ZSA9PT0gXCJjb25zdHJ1Y3RvclwiKSkge1xuICAgICAgICBtZXRob2Qua2luZCA9IFwiY29uc3RydWN0b3JcIjtcbiAgICAgIH0gZWxzZSB7XG4gICAgICAgIG1ldGhvZC5raW5kID0gXCJtZXRob2RcIjtcbiAgICAgIH1cbiAgICAgIG1ldGhvZC52YWx1ZSA9IHRoaXMucGFyc2VNZXRob2QoaXNHZW5lcmF0b3IpO1xuICAgIH1cbiAgICBub2RlLmJvZHkuYm9keS5wdXNoKHRoaXMuZmluaXNoTm9kZShtZXRob2QsIFwiTWV0aG9kRGVmaW5pdGlvblwiKSk7XG4gIH1cbiAgdGhpcy5wb3BDeCgpO1xuICBpZiAoIXRoaXMuZWF0KHR0LmJyYWNlUikpIHtcbiAgICAvLyBJZiB0aGVyZSBpcyBubyBjbG9zaW5nIGJyYWNlLCBtYWtlIHRoZSBub2RlIHNwYW4gdG8gdGhlIHN0YXJ0XG4gICAgLy8gb2YgdGhlIG5leHQgdG9rZW4gKHRoaXMgaXMgdXNlZnVsIGZvciBUZXJuKVxuICAgIHRoaXMubGFzdC5lbmQgPSB0aGlzLnRvay5zdGFydDtcbiAgICBpZiAodGhpcy5vcHRpb25zLmxvY2F0aW9ucykgdGhpcy5sYXN0LmxvYy5lbmQgPSB0aGlzLnRvay5sb2Muc3RhcnQ7XG4gIH1cbiAgdGhpcy5zZW1pY29sb24oKTtcbiAgdGhpcy5maW5pc2hOb2RlKG5vZGUuYm9keSwgXCJDbGFzc0JvZHlcIik7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgaXNTdGF0ZW1lbnQgPyBcIkNsYXNzRGVjbGFyYXRpb25cIiA6IFwiQ2xhc3NFeHByZXNzaW9uXCIpO1xufTtcblxubHAucGFyc2VGdW5jdGlvbiA9IGZ1bmN0aW9uIChub2RlLCBpc1N0YXRlbWVudCkge1xuICB0aGlzLmluaXRGdW5jdGlvbihub2RlKTtcbiAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KSB7XG4gICAgbm9kZS5nZW5lcmF0b3IgPSB0aGlzLmVhdCh0dC5zdGFyKTtcbiAgfVxuICBpZiAodGhpcy50b2sudHlwZSA9PT0gdHQubmFtZSkgbm9kZS5pZCA9IHRoaXMucGFyc2VJZGVudCgpO2Vsc2UgaWYgKGlzU3RhdGVtZW50KSBub2RlLmlkID0gdGhpcy5kdW1teUlkZW50KCk7XG4gIG5vZGUucGFyYW1zID0gdGhpcy5wYXJzZUZ1bmN0aW9uUGFyYW1zKCk7XG4gIG5vZGUuYm9keSA9IHRoaXMucGFyc2VCbG9jaygpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIGlzU3RhdGVtZW50ID8gXCJGdW5jdGlvbkRlY2xhcmF0aW9uXCIgOiBcIkZ1bmN0aW9uRXhwcmVzc2lvblwiKTtcbn07XG5cbmxwLnBhcnNlRXhwb3J0ID0gZnVuY3Rpb24gKCkge1xuICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gIHRoaXMubmV4dCgpO1xuICBpZiAodGhpcy5lYXQodHQuc3RhcikpIHtcbiAgICBub2RlLnNvdXJjZSA9IHRoaXMuZWF0Q29udGV4dHVhbChcImZyb21cIikgPyB0aGlzLnBhcnNlRXhwckF0b20oKSA6IG51bGw7XG4gICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkV4cG9ydEFsbERlY2xhcmF0aW9uXCIpO1xuICB9XG4gIGlmICh0aGlzLmVhdCh0dC5fZGVmYXVsdCkpIHtcbiAgICB2YXIgZXhwciA9IHRoaXMucGFyc2VNYXliZUFzc2lnbigpO1xuICAgIGlmIChleHByLmlkKSB7XG4gICAgICBzd2l0Y2ggKGV4cHIudHlwZSkge1xuICAgICAgICBjYXNlIFwiRnVuY3Rpb25FeHByZXNzaW9uXCI6XG4gICAgICAgICAgZXhwci50eXBlID0gXCJGdW5jdGlvbkRlY2xhcmF0aW9uXCI7YnJlYWs7XG4gICAgICAgIGNhc2UgXCJDbGFzc0V4cHJlc3Npb25cIjpcbiAgICAgICAgICBleHByLnR5cGUgPSBcIkNsYXNzRGVjbGFyYXRpb25cIjticmVhaztcbiAgICAgIH1cbiAgICB9XG4gICAgbm9kZS5kZWNsYXJhdGlvbiA9IGV4cHI7XG4gICAgdGhpcy5zZW1pY29sb24oKTtcbiAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiRXhwb3J0RGVmYXVsdERlY2xhcmF0aW9uXCIpO1xuICB9XG4gIGlmICh0aGlzLnRvay50eXBlLmtleXdvcmQpIHtcbiAgICBub2RlLmRlY2xhcmF0aW9uID0gdGhpcy5wYXJzZVN0YXRlbWVudCgpO1xuICAgIG5vZGUuc3BlY2lmaWVycyA9IFtdO1xuICAgIG5vZGUuc291cmNlID0gbnVsbDtcbiAgfSBlbHNlIHtcbiAgICBub2RlLmRlY2xhcmF0aW9uID0gbnVsbDtcbiAgICBub2RlLnNwZWNpZmllcnMgPSB0aGlzLnBhcnNlRXhwb3J0U3BlY2lmaWVyTGlzdCgpO1xuICAgIG5vZGUuc291cmNlID0gdGhpcy5lYXRDb250ZXh0dWFsKFwiZnJvbVwiKSA/IHRoaXMucGFyc2VFeHByQXRvbSgpIDogbnVsbDtcbiAgICB0aGlzLnNlbWljb2xvbigpO1xuICB9XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJFeHBvcnROYW1lZERlY2xhcmF0aW9uXCIpO1xufTtcblxubHAucGFyc2VJbXBvcnQgPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgdGhpcy5uZXh0KCk7XG4gIGlmICh0aGlzLnRvay50eXBlID09PSB0dC5zdHJpbmcpIHtcbiAgICBub2RlLnNwZWNpZmllcnMgPSBbXTtcbiAgICBub2RlLnNvdXJjZSA9IHRoaXMucGFyc2VFeHByQXRvbSgpO1xuICAgIG5vZGUua2luZCA9IFwiXCI7XG4gIH0gZWxzZSB7XG4gICAgdmFyIGVsdCA9IHVuZGVmaW5lZDtcbiAgICBpZiAodGhpcy50b2sudHlwZSA9PT0gdHQubmFtZSAmJiB0aGlzLnRvay52YWx1ZSAhPT0gXCJmcm9tXCIpIHtcbiAgICAgIGVsdCA9IHRoaXMuc3RhcnROb2RlKCk7XG4gICAgICBlbHQubG9jYWwgPSB0aGlzLnBhcnNlSWRlbnQoKTtcbiAgICAgIHRoaXMuZmluaXNoTm9kZShlbHQsIFwiSW1wb3J0RGVmYXVsdFNwZWNpZmllclwiKTtcbiAgICAgIHRoaXMuZWF0KHR0LmNvbW1hKTtcbiAgICB9XG4gICAgbm9kZS5zcGVjaWZpZXJzID0gdGhpcy5wYXJzZUltcG9ydFNwZWNpZmllckxpc3QoKTtcbiAgICBub2RlLnNvdXJjZSA9IHRoaXMuZWF0Q29udGV4dHVhbChcImZyb21cIikgPyB0aGlzLnBhcnNlRXhwckF0b20oKSA6IG51bGw7XG4gICAgaWYgKGVsdCkgbm9kZS5zcGVjaWZpZXJzLnVuc2hpZnQoZWx0KTtcbiAgfVxuICB0aGlzLnNlbWljb2xvbigpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiSW1wb3J0RGVjbGFyYXRpb25cIik7XG59O1xuXG5scC5wYXJzZUltcG9ydFNwZWNpZmllckxpc3QgPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBlbHRzID0gW107XG4gIGlmICh0aGlzLnRvay50eXBlID09PSB0dC5zdGFyKSB7XG4gICAgdmFyIGVsdCA9IHRoaXMuc3RhcnROb2RlKCk7XG4gICAgdGhpcy5uZXh0KCk7XG4gICAgaWYgKHRoaXMuZWF0Q29udGV4dHVhbChcImFzXCIpKSBlbHQubG9jYWwgPSB0aGlzLnBhcnNlSWRlbnQoKTtcbiAgICBlbHRzLnB1c2godGhpcy5maW5pc2hOb2RlKGVsdCwgXCJJbXBvcnROYW1lc3BhY2VTcGVjaWZpZXJcIikpO1xuICB9IGVsc2Uge1xuICAgIHZhciBpbmRlbnQgPSB0aGlzLmN1ckluZGVudCxcbiAgICAgICAgbGluZSA9IHRoaXMuY3VyTGluZVN0YXJ0LFxuICAgICAgICBjb250aW51ZWRMaW5lID0gdGhpcy5uZXh0TGluZVN0YXJ0O1xuICAgIHRoaXMucHVzaEN4KCk7XG4gICAgdGhpcy5lYXQodHQuYnJhY2VMKTtcbiAgICBpZiAodGhpcy5jdXJMaW5lU3RhcnQgPiBjb250aW51ZWRMaW5lKSBjb250aW51ZWRMaW5lID0gdGhpcy5jdXJMaW5lU3RhcnQ7XG4gICAgd2hpbGUgKCF0aGlzLmNsb3Nlcyh0dC5icmFjZVIsIGluZGVudCArICh0aGlzLmN1ckxpbmVTdGFydCA8PSBjb250aW51ZWRMaW5lID8gMSA6IDApLCBsaW5lKSkge1xuICAgICAgdmFyIGVsdCA9IHRoaXMuc3RhcnROb2RlKCk7XG4gICAgICBpZiAodGhpcy5lYXQodHQuc3RhcikpIHtcbiAgICAgICAgaWYgKHRoaXMuZWF0Q29udGV4dHVhbChcImFzXCIpKSBlbHQubG9jYWwgPSB0aGlzLnBhcnNlSWRlbnQoKTtcbiAgICAgICAgdGhpcy5maW5pc2hOb2RlKGVsdCwgXCJJbXBvcnROYW1lc3BhY2VTcGVjaWZpZXJcIik7XG4gICAgICB9IGVsc2Uge1xuICAgICAgICBpZiAodGhpcy5pc0NvbnRleHR1YWwoXCJmcm9tXCIpKSBicmVhaztcbiAgICAgICAgZWx0LmltcG9ydGVkID0gdGhpcy5wYXJzZUlkZW50KCk7XG4gICAgICAgIGVsdC5sb2NhbCA9IHRoaXMuZWF0Q29udGV4dHVhbChcImFzXCIpID8gdGhpcy5wYXJzZUlkZW50KCkgOiBlbHQuaW1wb3J0ZWQ7XG4gICAgICAgIHRoaXMuZmluaXNoTm9kZShlbHQsIFwiSW1wb3J0U3BlY2lmaWVyXCIpO1xuICAgICAgfVxuICAgICAgZWx0cy5wdXNoKGVsdCk7XG4gICAgICB0aGlzLmVhdCh0dC5jb21tYSk7XG4gICAgfVxuICAgIHRoaXMuZWF0KHR0LmJyYWNlUik7XG4gICAgdGhpcy5wb3BDeCgpO1xuICB9XG4gIHJldHVybiBlbHRzO1xufTtcblxubHAucGFyc2VFeHBvcnRTcGVjaWZpZXJMaXN0ID0gZnVuY3Rpb24gKCkge1xuICB2YXIgZWx0cyA9IFtdO1xuICB2YXIgaW5kZW50ID0gdGhpcy5jdXJJbmRlbnQsXG4gICAgICBsaW5lID0gdGhpcy5jdXJMaW5lU3RhcnQsXG4gICAgICBjb250aW51ZWRMaW5lID0gdGhpcy5uZXh0TGluZVN0YXJ0O1xuICB0aGlzLnB1c2hDeCgpO1xuICB0aGlzLmVhdCh0dC5icmFjZUwpO1xuICBpZiAodGhpcy5jdXJMaW5lU3RhcnQgPiBjb250aW51ZWRMaW5lKSBjb250aW51ZWRMaW5lID0gdGhpcy5jdXJMaW5lU3RhcnQ7XG4gIHdoaWxlICghdGhpcy5jbG9zZXModHQuYnJhY2VSLCBpbmRlbnQgKyAodGhpcy5jdXJMaW5lU3RhcnQgPD0gY29udGludWVkTGluZSA/IDEgOiAwKSwgbGluZSkpIHtcbiAgICBpZiAodGhpcy5pc0NvbnRleHR1YWwoXCJmcm9tXCIpKSBicmVhaztcbiAgICB2YXIgZWx0ID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgICBlbHQubG9jYWwgPSB0aGlzLnBhcnNlSWRlbnQoKTtcbiAgICBlbHQuZXhwb3J0ZWQgPSB0aGlzLmVhdENvbnRleHR1YWwoXCJhc1wiKSA/IHRoaXMucGFyc2VJZGVudCgpIDogZWx0LmxvY2FsO1xuICAgIHRoaXMuZmluaXNoTm9kZShlbHQsIFwiRXhwb3J0U3BlY2lmaWVyXCIpO1xuICAgIGVsdHMucHVzaChlbHQpO1xuICAgIHRoaXMuZWF0KHR0LmNvbW1hKTtcbiAgfVxuICB0aGlzLmVhdCh0dC5icmFjZVIpO1xuICB0aGlzLnBvcEN4KCk7XG4gIHJldHVybiBlbHRzO1xufTtcblxufSx7XCIuLlwiOjMsXCIuL3BhcnNldXRpbFwiOjUsXCIuL3N0YXRlXCI6Nn1dLDg6W2Z1bmN0aW9uKF9kZXJlcV8sbW9kdWxlLGV4cG9ydHMpe1xuXCJ1c2Ugc3RyaWN0XCI7XG5cbnZhciBfID0gX2RlcmVxXyhcIi4uXCIpO1xuXG52YXIgdHQgPSBfLnRva1R5cGVzO1xudmFyIFRva2VuID0gXy5Ub2tlbjtcbnZhciBpc05ld0xpbmUgPSBfLmlzTmV3TGluZTtcbnZhciBTb3VyY2VMb2NhdGlvbiA9IF8uU291cmNlTG9jYXRpb247XG52YXIgZ2V0TGluZUluZm8gPSBfLmdldExpbmVJbmZvO1xudmFyIGxpbmVCcmVha0cgPSBfLmxpbmVCcmVha0c7XG5cbnZhciBMb29zZVBhcnNlciA9IF9kZXJlcV8oXCIuL3N0YXRlXCIpLkxvb3NlUGFyc2VyO1xuXG52YXIgbHAgPSBMb29zZVBhcnNlci5wcm90b3R5cGU7XG5cbmZ1bmN0aW9uIGlzU3BhY2UoY2gpIHtcbiAgcmV0dXJuIGNoIDwgMTQgJiYgY2ggPiA4IHx8IGNoID09PSAzMiB8fCBjaCA9PT0gMTYwIHx8IGlzTmV3TGluZShjaCk7XG59XG5cbmxwLm5leHQgPSBmdW5jdGlvbiAoKSB7XG4gIHRoaXMubGFzdCA9IHRoaXMudG9rO1xuICBpZiAodGhpcy5haGVhZC5sZW5ndGgpIHRoaXMudG9rID0gdGhpcy5haGVhZC5zaGlmdCgpO2Vsc2UgdGhpcy50b2sgPSB0aGlzLnJlYWRUb2tlbigpO1xuXG4gIGlmICh0aGlzLnRvay5zdGFydCA+PSB0aGlzLm5leHRMaW5lU3RhcnQpIHtcbiAgICB3aGlsZSAodGhpcy50b2suc3RhcnQgPj0gdGhpcy5uZXh0TGluZVN0YXJ0KSB7XG4gICAgICB0aGlzLmN1ckxpbmVTdGFydCA9IHRoaXMubmV4dExpbmVTdGFydDtcbiAgICAgIHRoaXMubmV4dExpbmVTdGFydCA9IHRoaXMubGluZUVuZCh0aGlzLmN1ckxpbmVTdGFydCkgKyAxO1xuICAgIH1cbiAgICB0aGlzLmN1ckluZGVudCA9IHRoaXMuaW5kZW50YXRpb25BZnRlcih0aGlzLmN1ckxpbmVTdGFydCk7XG4gIH1cbn07XG5cbmxwLnJlYWRUb2tlbiA9IGZ1bmN0aW9uICgpIHtcbiAgZm9yICg7Oykge1xuICAgIHRyeSB7XG4gICAgICB0aGlzLnRva3MubmV4dCgpO1xuICAgICAgaWYgKHRoaXMudG9rcy50eXBlID09PSB0dC5kb3QgJiYgdGhpcy5pbnB1dC5zdWJzdHIodGhpcy50b2tzLmVuZCwgMSkgPT09IFwiLlwiICYmIHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KSB7XG4gICAgICAgIHRoaXMudG9rcy5lbmQrKztcbiAgICAgICAgdGhpcy50b2tzLnR5cGUgPSB0dC5lbGxpcHNpcztcbiAgICAgIH1cbiAgICAgIHJldHVybiBuZXcgVG9rZW4odGhpcy50b2tzKTtcbiAgICB9IGNhdGNoIChlKSB7XG4gICAgICBpZiAoIShlIGluc3RhbmNlb2YgU3ludGF4RXJyb3IpKSB0aHJvdyBlO1xuXG4gICAgICAvLyBUcnkgdG8gc2tpcCBzb21lIHRleHQsIGJhc2VkIG9uIHRoZSBlcnJvciBtZXNzYWdlLCBhbmQgdGhlbiBjb250aW51ZVxuICAgICAgdmFyIG1zZyA9IGUubWVzc2FnZSxcbiAgICAgICAgICBwb3MgPSBlLnJhaXNlZEF0LFxuICAgICAgICAgIHJlcGxhY2UgPSB0cnVlO1xuICAgICAgaWYgKC91bnRlcm1pbmF0ZWQvaS50ZXN0KG1zZykpIHtcbiAgICAgICAgcG9zID0gdGhpcy5saW5lRW5kKGUucG9zICsgMSk7XG4gICAgICAgIGlmICgvc3RyaW5nLy50ZXN0KG1zZykpIHtcbiAgICAgICAgICByZXBsYWNlID0geyBzdGFydDogZS5wb3MsIGVuZDogcG9zLCB0eXBlOiB0dC5zdHJpbmcsIHZhbHVlOiB0aGlzLmlucHV0LnNsaWNlKGUucG9zICsgMSwgcG9zKSB9O1xuICAgICAgICB9IGVsc2UgaWYgKC9yZWd1bGFyIGV4cHIvaS50ZXN0KG1zZykpIHtcbiAgICAgICAgICB2YXIgcmUgPSB0aGlzLmlucHV0LnNsaWNlKGUucG9zLCBwb3MpO1xuICAgICAgICAgIHRyeSB7XG4gICAgICAgICAgICByZSA9IG5ldyBSZWdFeHAocmUpO1xuICAgICAgICAgIH0gY2F0Y2ggKGUpIHt9XG4gICAgICAgICAgcmVwbGFjZSA9IHsgc3RhcnQ6IGUucG9zLCBlbmQ6IHBvcywgdHlwZTogdHQucmVnZXhwLCB2YWx1ZTogcmUgfTtcbiAgICAgICAgfSBlbHNlIGlmICgvdGVtcGxhdGUvLnRlc3QobXNnKSkge1xuICAgICAgICAgIHJlcGxhY2UgPSB7IHN0YXJ0OiBlLnBvcywgZW5kOiBwb3MsXG4gICAgICAgICAgICB0eXBlOiB0dC50ZW1wbGF0ZSxcbiAgICAgICAgICAgIHZhbHVlOiB0aGlzLmlucHV0LnNsaWNlKGUucG9zLCBwb3MpIH07XG4gICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgcmVwbGFjZSA9IGZhbHNlO1xuICAgICAgICB9XG4gICAgICB9IGVsc2UgaWYgKC9pbnZhbGlkICh1bmljb2RlfHJlZ2V4cHxudW1iZXIpfGV4cGVjdGluZyB1bmljb2RlfG9jdGFsIGxpdGVyYWx8aXMgcmVzZXJ2ZWR8ZGlyZWN0bHkgYWZ0ZXIgbnVtYmVyfGV4cGVjdGVkIG51bWJlciBpbiByYWRpeC9pLnRlc3QobXNnKSkge1xuICAgICAgICB3aGlsZSAocG9zIDwgdGhpcy5pbnB1dC5sZW5ndGggJiYgIWlzU3BhY2UodGhpcy5pbnB1dC5jaGFyQ29kZUF0KHBvcykpKSArK3BvcztcbiAgICAgIH0gZWxzZSBpZiAoL2NoYXJhY3RlciBlc2NhcGV8ZXhwZWN0ZWQgaGV4YWRlY2ltYWwvaS50ZXN0KG1zZykpIHtcbiAgICAgICAgd2hpbGUgKHBvcyA8IHRoaXMuaW5wdXQubGVuZ3RoKSB7XG4gICAgICAgICAgdmFyIGNoID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHBvcysrKTtcbiAgICAgICAgICBpZiAoY2ggPT09IDM0IHx8IGNoID09PSAzOSB8fCBpc05ld0xpbmUoY2gpKSBicmVhaztcbiAgICAgICAgfVxuICAgICAgfSBlbHNlIGlmICgvdW5leHBlY3RlZCBjaGFyYWN0ZXIvaS50ZXN0KG1zZykpIHtcbiAgICAgICAgcG9zKys7XG4gICAgICAgIHJlcGxhY2UgPSBmYWxzZTtcbiAgICAgIH0gZWxzZSBpZiAoL3JlZ3VsYXIgZXhwcmVzc2lvbi9pLnRlc3QobXNnKSkge1xuICAgICAgICByZXBsYWNlID0gdHJ1ZTtcbiAgICAgIH0gZWxzZSB7XG4gICAgICAgIHRocm93IGU7XG4gICAgICB9XG4gICAgICB0aGlzLnJlc2V0VG8ocG9zKTtcbiAgICAgIGlmIChyZXBsYWNlID09PSB0cnVlKSByZXBsYWNlID0geyBzdGFydDogcG9zLCBlbmQ6IHBvcywgdHlwZTogdHQubmFtZSwgdmFsdWU6IFwi4pyWXCIgfTtcbiAgICAgIGlmIChyZXBsYWNlKSB7XG4gICAgICAgIGlmICh0aGlzLm9wdGlvbnMubG9jYXRpb25zKSByZXBsYWNlLmxvYyA9IG5ldyBTb3VyY2VMb2NhdGlvbih0aGlzLnRva3MsIGdldExpbmVJbmZvKHRoaXMuaW5wdXQsIHJlcGxhY2Uuc3RhcnQpLCBnZXRMaW5lSW5mbyh0aGlzLmlucHV0LCByZXBsYWNlLmVuZCkpO1xuICAgICAgICByZXR1cm4gcmVwbGFjZTtcbiAgICAgIH1cbiAgICB9XG4gIH1cbn07XG5cbmxwLnJlc2V0VG8gPSBmdW5jdGlvbiAocG9zKSB7XG4gIHRoaXMudG9rcy5wb3MgPSBwb3M7XG4gIHZhciBjaCA9IHRoaXMuaW5wdXQuY2hhckF0KHBvcyAtIDEpO1xuICB0aGlzLnRva3MuZXhwckFsbG93ZWQgPSAhY2ggfHwgL1tcXFtcXHtcXCgsOzo/XFwvKj0rXFwtfiF8JiVePD5dLy50ZXN0KGNoKSB8fCAvW2Vud2ZkXS8udGVzdChjaCkgJiYgL1xcYihrZXl3b3Jkc3xjYXNlfGVsc2V8cmV0dXJufHRocm93fG5ld3xpbnwoaW5zdGFuY2V8dHlwZSlvZnxkZWxldGV8dm9pZCkkLy50ZXN0KHRoaXMuaW5wdXQuc2xpY2UocG9zIC0gMTAsIHBvcykpO1xuXG4gIGlmICh0aGlzLm9wdGlvbnMubG9jYXRpb25zKSB7XG4gICAgdGhpcy50b2tzLmN1ckxpbmUgPSAxO1xuICAgIHRoaXMudG9rcy5saW5lU3RhcnQgPSBsaW5lQnJlYWtHLmxhc3RJbmRleCA9IDA7XG4gICAgdmFyIG1hdGNoID0gdW5kZWZpbmVkO1xuICAgIHdoaWxlICgobWF0Y2ggPSBsaW5lQnJlYWtHLmV4ZWModGhpcy5pbnB1dCkpICYmIG1hdGNoLmluZGV4IDwgcG9zKSB7XG4gICAgICArK3RoaXMudG9rcy5jdXJMaW5lO1xuICAgICAgdGhpcy50b2tzLmxpbmVTdGFydCA9IG1hdGNoLmluZGV4ICsgbWF0Y2hbMF0ubGVuZ3RoO1xuICAgIH1cbiAgfVxufTtcblxubHAubG9va0FoZWFkID0gZnVuY3Rpb24gKG4pIHtcbiAgd2hpbGUgKG4gPiB0aGlzLmFoZWFkLmxlbmd0aCkgdGhpcy5haGVhZC5wdXNoKHRoaXMucmVhZFRva2VuKCkpO1xuICByZXR1cm4gdGhpcy5haGVhZFtuIC0gMV07XG59O1xuXG59LHtcIi4uXCI6MyxcIi4vc3RhdGVcIjo2fV19LHt9LFsxXSkoMSlcbn0pOyIsIihmdW5jdGlvbihmKXtpZih0eXBlb2YgZXhwb3J0cz09PVwib2JqZWN0XCImJnR5cGVvZiBtb2R1bGUhPT1cInVuZGVmaW5lZFwiKXttb2R1bGUuZXhwb3J0cz1mKCl9ZWxzZSBpZih0eXBlb2YgZGVmaW5lPT09XCJmdW5jdGlvblwiJiZkZWZpbmUuYW1kKXtkZWZpbmUoW10sZil9ZWxzZXt2YXIgZztpZih0eXBlb2Ygd2luZG93IT09XCJ1bmRlZmluZWRcIil7Zz13aW5kb3d9ZWxzZSBpZih0eXBlb2YgZ2xvYmFsIT09XCJ1bmRlZmluZWRcIil7Zz1nbG9iYWx9ZWxzZSBpZih0eXBlb2Ygc2VsZiE9PVwidW5kZWZpbmVkXCIpe2c9c2VsZn1lbHNle2c9dGhpc30oZy5hY29ybiB8fCAoZy5hY29ybiA9IHt9KSkud2FsayA9IGYoKX19KShmdW5jdGlvbigpe3ZhciBkZWZpbmUsbW9kdWxlLGV4cG9ydHM7cmV0dXJuIChmdW5jdGlvbiBlKHQsbixyKXtmdW5jdGlvbiBzKG8sdSl7aWYoIW5bb10pe2lmKCF0W29dKXt2YXIgYT10eXBlb2YgcmVxdWlyZT09XCJmdW5jdGlvblwiJiZyZXF1aXJlO2lmKCF1JiZhKXJldHVybiBhKG8sITApO2lmKGkpcmV0dXJuIGkobywhMCk7dmFyIGY9bmV3IEVycm9yKFwiQ2Fubm90IGZpbmQgbW9kdWxlICdcIitvK1wiJ1wiKTt0aHJvdyBmLmNvZGU9XCJNT0RVTEVfTk9UX0ZPVU5EXCIsZn12YXIgbD1uW29dPXtleHBvcnRzOnt9fTt0W29dWzBdLmNhbGwobC5leHBvcnRzLGZ1bmN0aW9uKGUpe3ZhciBuPXRbb11bMV1bZV07cmV0dXJuIHMobj9uOmUpfSxsLGwuZXhwb3J0cyxlLHQsbixyKX1yZXR1cm4gbltvXS5leHBvcnRzfXZhciBpPXR5cGVvZiByZXF1aXJlPT1cImZ1bmN0aW9uXCImJnJlcXVpcmU7Zm9yKHZhciBvPTA7bzxyLmxlbmd0aDtvKyspcyhyW29dKTtyZXR1cm4gc30pKHsxOltmdW5jdGlvbihfZGVyZXFfLG1vZHVsZSxleHBvcnRzKXtcblwidXNlIHN0cmljdFwiO1xuXG52YXIgX2NsYXNzQ2FsbENoZWNrID0gZnVuY3Rpb24gKGluc3RhbmNlLCBDb25zdHJ1Y3RvcikgeyBpZiAoIShpbnN0YW5jZSBpbnN0YW5jZW9mIENvbnN0cnVjdG9yKSkgeyB0aHJvdyBuZXcgVHlwZUVycm9yKFwiQ2Fubm90IGNhbGwgYSBjbGFzcyBhcyBhIGZ1bmN0aW9uXCIpOyB9IH07XG5cbi8vIEFTVCB3YWxrZXIgbW9kdWxlIGZvciBNb3ppbGxhIFBhcnNlciBBUEkgY29tcGF0aWJsZSB0cmVlc1xuXG4vLyBBIHNpbXBsZSB3YWxrIGlzIG9uZSB3aGVyZSB5b3Ugc2ltcGx5IHNwZWNpZnkgY2FsbGJhY2tzIHRvIGJlXG4vLyBjYWxsZWQgb24gc3BlY2lmaWMgbm9kZXMuIFRoZSBsYXN0IHR3byBhcmd1bWVudHMgYXJlIG9wdGlvbmFsLiBBXG4vLyBzaW1wbGUgdXNlIHdvdWxkIGJlXG4vL1xuLy8gICAgIHdhbGsuc2ltcGxlKG15VHJlZSwge1xuLy8gICAgICAgICBFeHByZXNzaW9uOiBmdW5jdGlvbihub2RlKSB7IC4uLiB9XG4vLyAgICAgfSk7XG4vL1xuLy8gdG8gZG8gc29tZXRoaW5nIHdpdGggYWxsIGV4cHJlc3Npb25zLiBBbGwgUGFyc2VyIEFQSSBub2RlIHR5cGVzXG4vLyBjYW4gYmUgdXNlZCB0byBpZGVudGlmeSBub2RlIHR5cGVzLCBhcyB3ZWxsIGFzIEV4cHJlc3Npb24sXG4vLyBTdGF0ZW1lbnQsIGFuZCBTY29wZUJvZHksIHdoaWNoIGRlbm90ZSBjYXRlZ29yaWVzIG9mIG5vZGVzLlxuLy9cbi8vIFRoZSBiYXNlIGFyZ3VtZW50IGNhbiBiZSB1c2VkIHRvIHBhc3MgYSBjdXN0b20gKHJlY3Vyc2l2ZSlcbi8vIHdhbGtlciwgYW5kIHN0YXRlIGNhbiBiZSB1c2VkIHRvIGdpdmUgdGhpcyB3YWxrZWQgYW4gaW5pdGlhbFxuLy8gc3RhdGUuXG5cbmV4cG9ydHMuc2ltcGxlID0gc2ltcGxlO1xuXG4vLyBBbiBhbmNlc3RvciB3YWxrIGJ1aWxkcyB1cCBhbiBhcnJheSBvZiBhbmNlc3RvciBub2RlcyAoaW5jbHVkaW5nXG4vLyB0aGUgY3VycmVudCBub2RlKSBhbmQgcGFzc2VzIHRoZW0gdG8gdGhlIGNhbGxiYWNrIGFzIHRoZSBzdGF0ZSBwYXJhbWV0ZXIuXG5leHBvcnRzLmFuY2VzdG9yID0gYW5jZXN0b3I7XG5cbi8vIEEgcmVjdXJzaXZlIHdhbGsgaXMgb25lIHdoZXJlIHlvdXIgZnVuY3Rpb25zIG92ZXJyaWRlIHRoZSBkZWZhdWx0XG4vLyB3YWxrZXJzLiBUaGV5IGNhbiBtb2RpZnkgYW5kIHJlcGxhY2UgdGhlIHN0YXRlIHBhcmFtZXRlciB0aGF0J3Ncbi8vIHRocmVhZGVkIHRocm91Z2ggdGhlIHdhbGssIGFuZCBjYW4gb3B0IGhvdyBhbmQgd2hldGhlciB0byB3YWxrXG4vLyB0aGVpciBjaGlsZCBub2RlcyAoYnkgY2FsbGluZyB0aGVpciB0aGlyZCBhcmd1bWVudCBvbiB0aGVzZVxuLy8gbm9kZXMpLlxuZXhwb3J0cy5yZWN1cnNpdmUgPSByZWN1cnNpdmU7XG5cbi8vIEZpbmQgYSBub2RlIHdpdGggYSBnaXZlbiBzdGFydCwgZW5kLCBhbmQgdHlwZSAoYWxsIGFyZSBvcHRpb25hbCxcbi8vIG51bGwgY2FuIGJlIHVzZWQgYXMgd2lsZGNhcmQpLiBSZXR1cm5zIGEge25vZGUsIHN0YXRlfSBvYmplY3QsIG9yXG4vLyB1bmRlZmluZWQgd2hlbiBpdCBkb2Vzbid0IGZpbmQgYSBtYXRjaGluZyBub2RlLlxuZXhwb3J0cy5maW5kTm9kZUF0ID0gZmluZE5vZGVBdDtcblxuLy8gRmluZCB0aGUgaW5uZXJtb3N0IG5vZGUgb2YgYSBnaXZlbiB0eXBlIHRoYXQgY29udGFpbnMgdGhlIGdpdmVuXG4vLyBwb3NpdGlvbi4gSW50ZXJmYWNlIHNpbWlsYXIgdG8gZmluZE5vZGVBdC5cbmV4cG9ydHMuZmluZE5vZGVBcm91bmQgPSBmaW5kTm9kZUFyb3VuZDtcblxuLy8gRmluZCB0aGUgb3V0ZXJtb3N0IG1hdGNoaW5nIG5vZGUgYWZ0ZXIgYSBnaXZlbiBwb3NpdGlvbi5cbmV4cG9ydHMuZmluZE5vZGVBZnRlciA9IGZpbmROb2RlQWZ0ZXI7XG5cbi8vIEZpbmQgdGhlIG91dGVybW9zdCBtYXRjaGluZyBub2RlIGJlZm9yZSBhIGdpdmVuIHBvc2l0aW9uLlxuZXhwb3J0cy5maW5kTm9kZUJlZm9yZSA9IGZpbmROb2RlQmVmb3JlO1xuXG4vLyBVc2VkIHRvIGNyZWF0ZSBhIGN1c3RvbSB3YWxrZXIuIFdpbGwgZmlsbCBpbiBhbGwgbWlzc2luZyBub2RlXG4vLyB0eXBlIHByb3BlcnRpZXMgd2l0aCB0aGUgZGVmYXVsdHMuXG5leHBvcnRzLm1ha2UgPSBtYWtlO1xuZXhwb3J0cy5fX2VzTW9kdWxlID0gdHJ1ZTtcblxuZnVuY3Rpb24gc2ltcGxlKG5vZGUsIHZpc2l0b3JzLCBiYXNlLCBzdGF0ZSkge1xuICBpZiAoIWJhc2UpIGJhc2UgPSBleHBvcnRzLmJhc2U7KGZ1bmN0aW9uIGMobm9kZSwgc3QsIG92ZXJyaWRlKSB7XG4gICAgdmFyIHR5cGUgPSBvdmVycmlkZSB8fCBub2RlLnR5cGUsXG4gICAgICAgIGZvdW5kID0gdmlzaXRvcnNbdHlwZV07XG4gICAgYmFzZVt0eXBlXShub2RlLCBzdCwgYyk7XG4gICAgaWYgKGZvdW5kKSBmb3VuZChub2RlLCBzdCk7XG4gIH0pKG5vZGUsIHN0YXRlKTtcbn1cblxuZnVuY3Rpb24gYW5jZXN0b3Iobm9kZSwgdmlzaXRvcnMsIGJhc2UsIHN0YXRlKSB7XG4gIGlmICghYmFzZSkgYmFzZSA9IGV4cG9ydHMuYmFzZTtcbiAgaWYgKCFzdGF0ZSkgc3RhdGUgPSBbXTsoZnVuY3Rpb24gYyhub2RlLCBzdCwgb3ZlcnJpZGUpIHtcbiAgICB2YXIgdHlwZSA9IG92ZXJyaWRlIHx8IG5vZGUudHlwZSxcbiAgICAgICAgZm91bmQgPSB2aXNpdG9yc1t0eXBlXTtcbiAgICBpZiAobm9kZSAhPSBzdFtzdC5sZW5ndGggLSAxXSkge1xuICAgICAgc3QgPSBzdC5zbGljZSgpO1xuICAgICAgc3QucHVzaChub2RlKTtcbiAgICB9XG4gICAgYmFzZVt0eXBlXShub2RlLCBzdCwgYyk7XG4gICAgaWYgKGZvdW5kKSBmb3VuZChub2RlLCBzdCk7XG4gIH0pKG5vZGUsIHN0YXRlKTtcbn1cblxuZnVuY3Rpb24gcmVjdXJzaXZlKG5vZGUsIHN0YXRlLCBmdW5jcywgYmFzZSkge1xuICB2YXIgdmlzaXRvciA9IGZ1bmNzID8gZXhwb3J0cy5tYWtlKGZ1bmNzLCBiYXNlKSA6IGJhc2U7KGZ1bmN0aW9uIGMobm9kZSwgc3QsIG92ZXJyaWRlKSB7XG4gICAgdmlzaXRvcltvdmVycmlkZSB8fCBub2RlLnR5cGVdKG5vZGUsIHN0LCBjKTtcbiAgfSkobm9kZSwgc3RhdGUpO1xufVxuXG5mdW5jdGlvbiBtYWtlVGVzdCh0ZXN0KSB7XG4gIGlmICh0eXBlb2YgdGVzdCA9PSBcInN0cmluZ1wiKSB7XG4gICAgcmV0dXJuIGZ1bmN0aW9uICh0eXBlKSB7XG4gICAgICByZXR1cm4gdHlwZSA9PSB0ZXN0O1xuICAgIH07XG4gIH0gZWxzZSBpZiAoIXRlc3QpIHtcbiAgICByZXR1cm4gZnVuY3Rpb24gKCkge1xuICAgICAgcmV0dXJuIHRydWU7XG4gICAgfTtcbiAgfSBlbHNlIHtcbiAgICByZXR1cm4gdGVzdDtcbiAgfVxufVxuXG52YXIgRm91bmQgPSBmdW5jdGlvbiBGb3VuZChub2RlLCBzdGF0ZSkge1xuICBfY2xhc3NDYWxsQ2hlY2sodGhpcywgRm91bmQpO1xuXG4gIHRoaXMubm9kZSA9IG5vZGU7dGhpcy5zdGF0ZSA9IHN0YXRlO1xufTtcblxuZnVuY3Rpb24gZmluZE5vZGVBdChub2RlLCBzdGFydCwgZW5kLCB0ZXN0LCBiYXNlLCBzdGF0ZSkge1xuICB0ZXN0ID0gbWFrZVRlc3QodGVzdCk7XG4gIGlmICghYmFzZSkgYmFzZSA9IGV4cG9ydHMuYmFzZTtcbiAgdHJ5IHtcbiAgICA7KGZ1bmN0aW9uIGMobm9kZSwgc3QsIG92ZXJyaWRlKSB7XG4gICAgICB2YXIgdHlwZSA9IG92ZXJyaWRlIHx8IG5vZGUudHlwZTtcbiAgICAgIGlmICgoc3RhcnQgPT0gbnVsbCB8fCBub2RlLnN0YXJ0IDw9IHN0YXJ0KSAmJiAoZW5kID09IG51bGwgfHwgbm9kZS5lbmQgPj0gZW5kKSkgYmFzZVt0eXBlXShub2RlLCBzdCwgYyk7XG4gICAgICBpZiAodGVzdCh0eXBlLCBub2RlKSAmJiAoc3RhcnQgPT0gbnVsbCB8fCBub2RlLnN0YXJ0ID09IHN0YXJ0KSAmJiAoZW5kID09IG51bGwgfHwgbm9kZS5lbmQgPT0gZW5kKSkgdGhyb3cgbmV3IEZvdW5kKG5vZGUsIHN0KTtcbiAgICB9KShub2RlLCBzdGF0ZSk7XG4gIH0gY2F0Y2ggKGUpIHtcbiAgICBpZiAoZSBpbnN0YW5jZW9mIEZvdW5kKSB7XG4gICAgICByZXR1cm4gZTtcbiAgICB9dGhyb3cgZTtcbiAgfVxufVxuXG5mdW5jdGlvbiBmaW5kTm9kZUFyb3VuZChub2RlLCBwb3MsIHRlc3QsIGJhc2UsIHN0YXRlKSB7XG4gIHRlc3QgPSBtYWtlVGVzdCh0ZXN0KTtcbiAgaWYgKCFiYXNlKSBiYXNlID0gZXhwb3J0cy5iYXNlO1xuICB0cnkge1xuICAgIDsoZnVuY3Rpb24gYyhub2RlLCBzdCwgb3ZlcnJpZGUpIHtcbiAgICAgIHZhciB0eXBlID0gb3ZlcnJpZGUgfHwgbm9kZS50eXBlO1xuICAgICAgaWYgKG5vZGUuc3RhcnQgPiBwb3MgfHwgbm9kZS5lbmQgPCBwb3MpIHtcbiAgICAgICAgcmV0dXJuO1xuICAgICAgfWJhc2VbdHlwZV0obm9kZSwgc3QsIGMpO1xuICAgICAgaWYgKHRlc3QodHlwZSwgbm9kZSkpIHRocm93IG5ldyBGb3VuZChub2RlLCBzdCk7XG4gICAgfSkobm9kZSwgc3RhdGUpO1xuICB9IGNhdGNoIChlKSB7XG4gICAgaWYgKGUgaW5zdGFuY2VvZiBGb3VuZCkge1xuICAgICAgcmV0dXJuIGU7XG4gICAgfXRocm93IGU7XG4gIH1cbn1cblxuZnVuY3Rpb24gZmluZE5vZGVBZnRlcihub2RlLCBwb3MsIHRlc3QsIGJhc2UsIHN0YXRlKSB7XG4gIHRlc3QgPSBtYWtlVGVzdCh0ZXN0KTtcbiAgaWYgKCFiYXNlKSBiYXNlID0gZXhwb3J0cy5iYXNlO1xuICB0cnkge1xuICAgIDsoZnVuY3Rpb24gYyhub2RlLCBzdCwgb3ZlcnJpZGUpIHtcbiAgICAgIGlmIChub2RlLmVuZCA8IHBvcykge1xuICAgICAgICByZXR1cm47XG4gICAgICB9dmFyIHR5cGUgPSBvdmVycmlkZSB8fCBub2RlLnR5cGU7XG4gICAgICBpZiAobm9kZS5zdGFydCA+PSBwb3MgJiYgdGVzdCh0eXBlLCBub2RlKSkgdGhyb3cgbmV3IEZvdW5kKG5vZGUsIHN0KTtcbiAgICAgIGJhc2VbdHlwZV0obm9kZSwgc3QsIGMpO1xuICAgIH0pKG5vZGUsIHN0YXRlKTtcbiAgfSBjYXRjaCAoZSkge1xuICAgIGlmIChlIGluc3RhbmNlb2YgRm91bmQpIHtcbiAgICAgIHJldHVybiBlO1xuICAgIH10aHJvdyBlO1xuICB9XG59XG5cbmZ1bmN0aW9uIGZpbmROb2RlQmVmb3JlKG5vZGUsIHBvcywgdGVzdCwgYmFzZSwgc3RhdGUpIHtcbiAgdGVzdCA9IG1ha2VUZXN0KHRlc3QpO1xuICBpZiAoIWJhc2UpIGJhc2UgPSBleHBvcnRzLmJhc2U7XG4gIHZhciBtYXggPSB1bmRlZmluZWQ7KGZ1bmN0aW9uIGMobm9kZSwgc3QsIG92ZXJyaWRlKSB7XG4gICAgaWYgKG5vZGUuc3RhcnQgPiBwb3MpIHtcbiAgICAgIHJldHVybjtcbiAgICB9dmFyIHR5cGUgPSBvdmVycmlkZSB8fCBub2RlLnR5cGU7XG4gICAgaWYgKG5vZGUuZW5kIDw9IHBvcyAmJiAoIW1heCB8fCBtYXgubm9kZS5lbmQgPCBub2RlLmVuZCkgJiYgdGVzdCh0eXBlLCBub2RlKSkgbWF4ID0gbmV3IEZvdW5kKG5vZGUsIHN0KTtcbiAgICBiYXNlW3R5cGVdKG5vZGUsIHN0LCBjKTtcbiAgfSkobm9kZSwgc3RhdGUpO1xuICByZXR1cm4gbWF4O1xufVxuXG5mdW5jdGlvbiBtYWtlKGZ1bmNzLCBiYXNlKSB7XG4gIGlmICghYmFzZSkgYmFzZSA9IGV4cG9ydHMuYmFzZTtcbiAgdmFyIHZpc2l0b3IgPSB7fTtcbiAgZm9yICh2YXIgdHlwZSBpbiBiYXNlKSB2aXNpdG9yW3R5cGVdID0gYmFzZVt0eXBlXTtcbiAgZm9yICh2YXIgdHlwZSBpbiBmdW5jcykgdmlzaXRvclt0eXBlXSA9IGZ1bmNzW3R5cGVdO1xuICByZXR1cm4gdmlzaXRvcjtcbn1cblxuZnVuY3Rpb24gc2tpcFRocm91Z2gobm9kZSwgc3QsIGMpIHtcbiAgYyhub2RlLCBzdCk7XG59XG5mdW5jdGlvbiBpZ25vcmUoX25vZGUsIF9zdCwgX2MpIHt9XG5cbi8vIE5vZGUgd2Fsa2Vycy5cblxudmFyIGJhc2UgPSB7fTtcblxuZXhwb3J0cy5iYXNlID0gYmFzZTtcbmJhc2UuUHJvZ3JhbSA9IGJhc2UuQmxvY2tTdGF0ZW1lbnQgPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgZm9yICh2YXIgaSA9IDA7IGkgPCBub2RlLmJvZHkubGVuZ3RoOyArK2kpIHtcbiAgICBjKG5vZGUuYm9keVtpXSwgc3QsIFwiU3RhdGVtZW50XCIpO1xuICB9XG59O1xuYmFzZS5TdGF0ZW1lbnQgPSBza2lwVGhyb3VnaDtcbmJhc2UuRW1wdHlTdGF0ZW1lbnQgPSBpZ25vcmU7XG5iYXNlLkV4cHJlc3Npb25TdGF0ZW1lbnQgPSBiYXNlLlBhcmVudGhlc2l6ZWRFeHByZXNzaW9uID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIHJldHVybiBjKG5vZGUuZXhwcmVzc2lvbiwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbn07XG5iYXNlLklmU3RhdGVtZW50ID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIGMobm9kZS50ZXN0LCBzdCwgXCJFeHByZXNzaW9uXCIpO1xuICBjKG5vZGUuY29uc2VxdWVudCwgc3QsIFwiU3RhdGVtZW50XCIpO1xuICBpZiAobm9kZS5hbHRlcm5hdGUpIGMobm9kZS5hbHRlcm5hdGUsIHN0LCBcIlN0YXRlbWVudFwiKTtcbn07XG5iYXNlLkxhYmVsZWRTdGF0ZW1lbnQgPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgcmV0dXJuIGMobm9kZS5ib2R5LCBzdCwgXCJTdGF0ZW1lbnRcIik7XG59O1xuYmFzZS5CcmVha1N0YXRlbWVudCA9IGJhc2UuQ29udGludWVTdGF0ZW1lbnQgPSBpZ25vcmU7XG5iYXNlLldpdGhTdGF0ZW1lbnQgPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgYyhub2RlLm9iamVjdCwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbiAgYyhub2RlLmJvZHksIHN0LCBcIlN0YXRlbWVudFwiKTtcbn07XG5iYXNlLlN3aXRjaFN0YXRlbWVudCA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBjKG5vZGUuZGlzY3JpbWluYW50LCBzdCwgXCJFeHByZXNzaW9uXCIpO1xuICBmb3IgKHZhciBpID0gMDsgaSA8IG5vZGUuY2FzZXMubGVuZ3RoOyArK2kpIHtcbiAgICB2YXIgY3MgPSBub2RlLmNhc2VzW2ldO1xuICAgIGlmIChjcy50ZXN0KSBjKGNzLnRlc3QsIHN0LCBcIkV4cHJlc3Npb25cIik7XG4gICAgZm9yICh2YXIgaiA9IDA7IGogPCBjcy5jb25zZXF1ZW50Lmxlbmd0aDsgKytqKSB7XG4gICAgICBjKGNzLmNvbnNlcXVlbnRbal0sIHN0LCBcIlN0YXRlbWVudFwiKTtcbiAgICB9XG4gIH1cbn07XG5iYXNlLlJldHVyblN0YXRlbWVudCA9IGJhc2UuWWllbGRFeHByZXNzaW9uID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIGlmIChub2RlLmFyZ3VtZW50KSBjKG5vZGUuYXJndW1lbnQsIHN0LCBcIkV4cHJlc3Npb25cIik7XG59O1xuYmFzZS5UaHJvd1N0YXRlbWVudCA9IGJhc2UuU3ByZWFkRWxlbWVudCA9IGJhc2UuUmVzdEVsZW1lbnQgPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgcmV0dXJuIGMobm9kZS5hcmd1bWVudCwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbn07XG5iYXNlLlRyeVN0YXRlbWVudCA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBjKG5vZGUuYmxvY2ssIHN0LCBcIlN0YXRlbWVudFwiKTtcbiAgaWYgKG5vZGUuaGFuZGxlcikgYyhub2RlLmhhbmRsZXIuYm9keSwgc3QsIFwiU2NvcGVCb2R5XCIpO1xuICBpZiAobm9kZS5maW5hbGl6ZXIpIGMobm9kZS5maW5hbGl6ZXIsIHN0LCBcIlN0YXRlbWVudFwiKTtcbn07XG5iYXNlLldoaWxlU3RhdGVtZW50ID0gYmFzZS5Eb1doaWxlU3RhdGVtZW50ID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIGMobm9kZS50ZXN0LCBzdCwgXCJFeHByZXNzaW9uXCIpO1xuICBjKG5vZGUuYm9keSwgc3QsIFwiU3RhdGVtZW50XCIpO1xufTtcbmJhc2UuRm9yU3RhdGVtZW50ID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIGlmIChub2RlLmluaXQpIGMobm9kZS5pbml0LCBzdCwgXCJGb3JJbml0XCIpO1xuICBpZiAobm9kZS50ZXN0KSBjKG5vZGUudGVzdCwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbiAgaWYgKG5vZGUudXBkYXRlKSBjKG5vZGUudXBkYXRlLCBzdCwgXCJFeHByZXNzaW9uXCIpO1xuICBjKG5vZGUuYm9keSwgc3QsIFwiU3RhdGVtZW50XCIpO1xufTtcbmJhc2UuRm9ySW5TdGF0ZW1lbnQgPSBiYXNlLkZvck9mU3RhdGVtZW50ID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIGMobm9kZS5sZWZ0LCBzdCwgXCJGb3JJbml0XCIpO1xuICBjKG5vZGUucmlnaHQsIHN0LCBcIkV4cHJlc3Npb25cIik7XG4gIGMobm9kZS5ib2R5LCBzdCwgXCJTdGF0ZW1lbnRcIik7XG59O1xuYmFzZS5Gb3JJbml0ID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIGlmIChub2RlLnR5cGUgPT0gXCJWYXJpYWJsZURlY2xhcmF0aW9uXCIpIGMobm9kZSwgc3QpO2Vsc2UgYyhub2RlLCBzdCwgXCJFeHByZXNzaW9uXCIpO1xufTtcbmJhc2UuRGVidWdnZXJTdGF0ZW1lbnQgPSBpZ25vcmU7XG5cbmJhc2UuRnVuY3Rpb25EZWNsYXJhdGlvbiA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICByZXR1cm4gYyhub2RlLCBzdCwgXCJGdW5jdGlvblwiKTtcbn07XG5iYXNlLlZhcmlhYmxlRGVjbGFyYXRpb24gPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgZm9yICh2YXIgaSA9IDA7IGkgPCBub2RlLmRlY2xhcmF0aW9ucy5sZW5ndGg7ICsraSkge1xuICAgIHZhciBkZWNsID0gbm9kZS5kZWNsYXJhdGlvbnNbaV07XG4gICAgaWYgKGRlY2wuaW5pdCkgYyhkZWNsLmluaXQsIHN0LCBcIkV4cHJlc3Npb25cIik7XG4gIH1cbn07XG5cbmJhc2UuRnVuY3Rpb24gPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgcmV0dXJuIGMobm9kZS5ib2R5LCBzdCwgXCJTY29wZUJvZHlcIik7XG59O1xuYmFzZS5TY29wZUJvZHkgPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgcmV0dXJuIGMobm9kZSwgc3QsIFwiU3RhdGVtZW50XCIpO1xufTtcblxuYmFzZS5FeHByZXNzaW9uID0gc2tpcFRocm91Z2g7XG5iYXNlLlRoaXNFeHByZXNzaW9uID0gYmFzZS5TdXBlciA9IGJhc2UuTWV0YVByb3BlcnR5ID0gaWdub3JlO1xuYmFzZS5BcnJheUV4cHJlc3Npb24gPSBiYXNlLkFycmF5UGF0dGVybiA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBmb3IgKHZhciBpID0gMDsgaSA8IG5vZGUuZWxlbWVudHMubGVuZ3RoOyArK2kpIHtcbiAgICB2YXIgZWx0ID0gbm9kZS5lbGVtZW50c1tpXTtcbiAgICBpZiAoZWx0KSBjKGVsdCwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbiAgfVxufTtcbmJhc2UuT2JqZWN0RXhwcmVzc2lvbiA9IGJhc2UuT2JqZWN0UGF0dGVybiA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBmb3IgKHZhciBpID0gMDsgaSA8IG5vZGUucHJvcGVydGllcy5sZW5ndGg7ICsraSkge1xuICAgIGMobm9kZS5wcm9wZXJ0aWVzW2ldLCBzdCk7XG4gIH1cbn07XG5iYXNlLkZ1bmN0aW9uRXhwcmVzc2lvbiA9IGJhc2UuQXJyb3dGdW5jdGlvbkV4cHJlc3Npb24gPSBiYXNlLkZ1bmN0aW9uRGVjbGFyYXRpb247XG5iYXNlLlNlcXVlbmNlRXhwcmVzc2lvbiA9IGJhc2UuVGVtcGxhdGVMaXRlcmFsID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIGZvciAodmFyIGkgPSAwOyBpIDwgbm9kZS5leHByZXNzaW9ucy5sZW5ndGg7ICsraSkge1xuICAgIGMobm9kZS5leHByZXNzaW9uc1tpXSwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbiAgfVxufTtcbmJhc2UuVW5hcnlFeHByZXNzaW9uID0gYmFzZS5VcGRhdGVFeHByZXNzaW9uID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIGMobm9kZS5hcmd1bWVudCwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbn07XG5iYXNlLkJpbmFyeUV4cHJlc3Npb24gPSBiYXNlLkFzc2lnbm1lbnRFeHByZXNzaW9uID0gYmFzZS5Bc3NpZ25tZW50UGF0dGVybiA9IGJhc2UuTG9naWNhbEV4cHJlc3Npb24gPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgYyhub2RlLmxlZnQsIHN0LCBcIkV4cHJlc3Npb25cIik7XG4gIGMobm9kZS5yaWdodCwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbn07XG5iYXNlLkNvbmRpdGlvbmFsRXhwcmVzc2lvbiA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBjKG5vZGUudGVzdCwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbiAgYyhub2RlLmNvbnNlcXVlbnQsIHN0LCBcIkV4cHJlc3Npb25cIik7XG4gIGMobm9kZS5hbHRlcm5hdGUsIHN0LCBcIkV4cHJlc3Npb25cIik7XG59O1xuYmFzZS5OZXdFeHByZXNzaW9uID0gYmFzZS5DYWxsRXhwcmVzc2lvbiA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBjKG5vZGUuY2FsbGVlLCBzdCwgXCJFeHByZXNzaW9uXCIpO1xuICBpZiAobm9kZS5hcmd1bWVudHMpIGZvciAodmFyIGkgPSAwOyBpIDwgbm9kZS5hcmd1bWVudHMubGVuZ3RoOyArK2kpIHtcbiAgICBjKG5vZGUuYXJndW1lbnRzW2ldLCBzdCwgXCJFeHByZXNzaW9uXCIpO1xuICB9XG59O1xuYmFzZS5NZW1iZXJFeHByZXNzaW9uID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIGMobm9kZS5vYmplY3QsIHN0LCBcIkV4cHJlc3Npb25cIik7XG4gIGlmIChub2RlLmNvbXB1dGVkKSBjKG5vZGUucHJvcGVydHksIHN0LCBcIkV4cHJlc3Npb25cIik7XG59O1xuYmFzZS5FeHBvcnROYW1lZERlY2xhcmF0aW9uID0gYmFzZS5FeHBvcnREZWZhdWx0RGVjbGFyYXRpb24gPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgcmV0dXJuIGMobm9kZS5kZWNsYXJhdGlvbiwgc3QpO1xufTtcbmJhc2UuSW1wb3J0RGVjbGFyYXRpb24gPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgZm9yICh2YXIgaSA9IDA7IGkgPCBub2RlLnNwZWNpZmllcnMubGVuZ3RoOyBpKyspIHtcbiAgICBjKG5vZGUuc3BlY2lmaWVyc1tpXSwgc3QpO1xuICB9XG59O1xuYmFzZS5JbXBvcnRTcGVjaWZpZXIgPSBiYXNlLkltcG9ydERlZmF1bHRTcGVjaWZpZXIgPSBiYXNlLkltcG9ydE5hbWVzcGFjZVNwZWNpZmllciA9IGJhc2UuSWRlbnRpZmllciA9IGJhc2UuTGl0ZXJhbCA9IGlnbm9yZTtcblxuYmFzZS5UYWdnZWRUZW1wbGF0ZUV4cHJlc3Npb24gPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgYyhub2RlLnRhZywgc3QsIFwiRXhwcmVzc2lvblwiKTtcbiAgYyhub2RlLnF1YXNpLCBzdCk7XG59O1xuYmFzZS5DbGFzc0RlY2xhcmF0aW9uID0gYmFzZS5DbGFzc0V4cHJlc3Npb24gPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgaWYgKG5vZGUuc3VwZXJDbGFzcykgYyhub2RlLnN1cGVyQ2xhc3MsIHN0LCBcIkV4cHJlc3Npb25cIik7XG4gIGZvciAodmFyIGkgPSAwOyBpIDwgbm9kZS5ib2R5LmJvZHkubGVuZ3RoOyBpKyspIHtcbiAgICBjKG5vZGUuYm9keS5ib2R5W2ldLCBzdCk7XG4gIH1cbn07XG5iYXNlLk1ldGhvZERlZmluaXRpb24gPSBiYXNlLlByb3BlcnR5ID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIGlmIChub2RlLmNvbXB1dGVkKSBjKG5vZGUua2V5LCBzdCwgXCJFeHByZXNzaW9uXCIpO1xuICBjKG5vZGUudmFsdWUsIHN0LCBcIkV4cHJlc3Npb25cIik7XG59O1xuYmFzZS5Db21wcmVoZW5zaW9uRXhwcmVzc2lvbiA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBmb3IgKHZhciBpID0gMDsgaSA8IG5vZGUuYmxvY2tzLmxlbmd0aDsgaSsrKSB7XG4gICAgYyhub2RlLmJsb2Nrc1tpXS5yaWdodCwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbiAgfWMobm9kZS5ib2R5LCBzdCwgXCJFeHByZXNzaW9uXCIpO1xufTtcblxufSx7fV19LHt9LFsxXSkoMSlcbn0pOyIsbnVsbCwiaWYgKHR5cGVvZiBPYmplY3QuY3JlYXRlID09PSAnZnVuY3Rpb24nKSB7XG4gIC8vIGltcGxlbWVudGF0aW9uIGZyb20gc3RhbmRhcmQgbm9kZS5qcyAndXRpbCcgbW9kdWxlXG4gIG1vZHVsZS5leHBvcnRzID0gZnVuY3Rpb24gaW5oZXJpdHMoY3Rvciwgc3VwZXJDdG9yKSB7XG4gICAgY3Rvci5zdXBlcl8gPSBzdXBlckN0b3JcbiAgICBjdG9yLnByb3RvdHlwZSA9IE9iamVjdC5jcmVhdGUoc3VwZXJDdG9yLnByb3RvdHlwZSwge1xuICAgICAgY29uc3RydWN0b3I6IHtcbiAgICAgICAgdmFsdWU6IGN0b3IsXG4gICAgICAgIGVudW1lcmFibGU6IGZhbHNlLFxuICAgICAgICB3cml0YWJsZTogdHJ1ZSxcbiAgICAgICAgY29uZmlndXJhYmxlOiB0cnVlXG4gICAgICB9XG4gICAgfSk7XG4gIH07XG59IGVsc2Uge1xuICAvLyBvbGQgc2Nob29sIHNoaW0gZm9yIG9sZCBicm93c2Vyc1xuICBtb2R1bGUuZXhwb3J0cyA9IGZ1bmN0aW9uIGluaGVyaXRzKGN0b3IsIHN1cGVyQ3Rvcikge1xuICAgIGN0b3Iuc3VwZXJfID0gc3VwZXJDdG9yXG4gICAgdmFyIFRlbXBDdG9yID0gZnVuY3Rpb24gKCkge31cbiAgICBUZW1wQ3Rvci5wcm90b3R5cGUgPSBzdXBlckN0b3IucHJvdG90eXBlXG4gICAgY3Rvci5wcm90b3R5cGUgPSBuZXcgVGVtcEN0b3IoKVxuICAgIGN0b3IucHJvdG90eXBlLmNvbnN0cnVjdG9yID0gY3RvclxuICB9XG59XG4iLCIvLyBzaGltIGZvciB1c2luZyBwcm9jZXNzIGluIGJyb3dzZXJcblxudmFyIHByb2Nlc3MgPSBtb2R1bGUuZXhwb3J0cyA9IHt9O1xudmFyIHF1ZXVlID0gW107XG52YXIgZHJhaW5pbmcgPSBmYWxzZTtcbnZhciBjdXJyZW50UXVldWU7XG52YXIgcXVldWVJbmRleCA9IC0xO1xuXG5mdW5jdGlvbiBjbGVhblVwTmV4dFRpY2soKSB7XG4gICAgZHJhaW5pbmcgPSBmYWxzZTtcbiAgICBpZiAoY3VycmVudFF1ZXVlLmxlbmd0aCkge1xuICAgICAgICBxdWV1ZSA9IGN1cnJlbnRRdWV1ZS5jb25jYXQocXVldWUpO1xuICAgIH0gZWxzZSB7XG4gICAgICAgIHF1ZXVlSW5kZXggPSAtMTtcbiAgICB9XG4gICAgaWYgKHF1ZXVlLmxlbmd0aCkge1xuICAgICAgICBkcmFpblF1ZXVlKCk7XG4gICAgfVxufVxuXG5mdW5jdGlvbiBkcmFpblF1ZXVlKCkge1xuICAgIGlmIChkcmFpbmluZykge1xuICAgICAgICByZXR1cm47XG4gICAgfVxuICAgIHZhciB0aW1lb3V0ID0gc2V0VGltZW91dChjbGVhblVwTmV4dFRpY2spO1xuICAgIGRyYWluaW5nID0gdHJ1ZTtcblxuICAgIHZhciBsZW4gPSBxdWV1ZS5sZW5ndGg7XG4gICAgd2hpbGUobGVuKSB7XG4gICAgICAgIGN1cnJlbnRRdWV1ZSA9IHF1ZXVlO1xuICAgICAgICBxdWV1ZSA9IFtdO1xuICAgICAgICB3aGlsZSAoKytxdWV1ZUluZGV4IDwgbGVuKSB7XG4gICAgICAgICAgICBjdXJyZW50UXVldWVbcXVldWVJbmRleF0ucnVuKCk7XG4gICAgICAgIH1cbiAgICAgICAgcXVldWVJbmRleCA9IC0xO1xuICAgICAgICBsZW4gPSBxdWV1ZS5sZW5ndGg7XG4gICAgfVxuICAgIGN1cnJlbnRRdWV1ZSA9IG51bGw7XG4gICAgZHJhaW5pbmcgPSBmYWxzZTtcbiAgICBjbGVhclRpbWVvdXQodGltZW91dCk7XG59XG5cbnByb2Nlc3MubmV4dFRpY2sgPSBmdW5jdGlvbiAoZnVuKSB7XG4gICAgdmFyIGFyZ3MgPSBuZXcgQXJyYXkoYXJndW1lbnRzLmxlbmd0aCAtIDEpO1xuICAgIGlmIChhcmd1bWVudHMubGVuZ3RoID4gMSkge1xuICAgICAgICBmb3IgKHZhciBpID0gMTsgaSA8IGFyZ3VtZW50cy5sZW5ndGg7IGkrKykge1xuICAgICAgICAgICAgYXJnc1tpIC0gMV0gPSBhcmd1bWVudHNbaV07XG4gICAgICAgIH1cbiAgICB9XG4gICAgcXVldWUucHVzaChuZXcgSXRlbShmdW4sIGFyZ3MpKTtcbiAgICBpZiAocXVldWUubGVuZ3RoID09PSAxICYmICFkcmFpbmluZykge1xuICAgICAgICBzZXRUaW1lb3V0KGRyYWluUXVldWUsIDApO1xuICAgIH1cbn07XG5cbi8vIHY4IGxpa2VzIHByZWRpY3RpYmxlIG9iamVjdHNcbmZ1bmN0aW9uIEl0ZW0oZnVuLCBhcnJheSkge1xuICAgIHRoaXMuZnVuID0gZnVuO1xuICAgIHRoaXMuYXJyYXkgPSBhcnJheTtcbn1cbkl0ZW0ucHJvdG90eXBlLnJ1biA9IGZ1bmN0aW9uICgpIHtcbiAgICB0aGlzLmZ1bi5hcHBseShudWxsLCB0aGlzLmFycmF5KTtcbn07XG5wcm9jZXNzLnRpdGxlID0gJ2Jyb3dzZXInO1xucHJvY2Vzcy5icm93c2VyID0gdHJ1ZTtcbnByb2Nlc3MuZW52ID0ge307XG5wcm9jZXNzLmFyZ3YgPSBbXTtcbnByb2Nlc3MudmVyc2lvbiA9ICcnOyAvLyBlbXB0eSBzdHJpbmcgdG8gYXZvaWQgcmVnZXhwIGlzc3Vlc1xucHJvY2Vzcy52ZXJzaW9ucyA9IHt9O1xuXG5mdW5jdGlvbiBub29wKCkge31cblxucHJvY2Vzcy5vbiA9IG5vb3A7XG5wcm9jZXNzLmFkZExpc3RlbmVyID0gbm9vcDtcbnByb2Nlc3Mub25jZSA9IG5vb3A7XG5wcm9jZXNzLm9mZiA9IG5vb3A7XG5wcm9jZXNzLnJlbW92ZUxpc3RlbmVyID0gbm9vcDtcbnByb2Nlc3MucmVtb3ZlQWxsTGlzdGVuZXJzID0gbm9vcDtcbnByb2Nlc3MuZW1pdCA9IG5vb3A7XG5cbnByb2Nlc3MuYmluZGluZyA9IGZ1bmN0aW9uIChuYW1lKSB7XG4gICAgdGhyb3cgbmV3IEVycm9yKCdwcm9jZXNzLmJpbmRpbmcgaXMgbm90IHN1cHBvcnRlZCcpO1xufTtcblxuLy8gVE9ETyhzaHR5bG1hbilcbnByb2Nlc3MuY3dkID0gZnVuY3Rpb24gKCkgeyByZXR1cm4gJy8nIH07XG5wcm9jZXNzLmNoZGlyID0gZnVuY3Rpb24gKGRpcikge1xuICAgIHRocm93IG5ldyBFcnJvcigncHJvY2Vzcy5jaGRpciBpcyBub3Qgc3VwcG9ydGVkJyk7XG59O1xucHJvY2Vzcy51bWFzayA9IGZ1bmN0aW9uKCkgeyByZXR1cm4gMDsgfTtcbiIsIm1vZHVsZS5leHBvcnRzID0gZnVuY3Rpb24gaXNCdWZmZXIoYXJnKSB7XG4gIHJldHVybiBhcmcgJiYgdHlwZW9mIGFyZyA9PT0gJ29iamVjdCdcbiAgICAmJiB0eXBlb2YgYXJnLmNvcHkgPT09ICdmdW5jdGlvbidcbiAgICAmJiB0eXBlb2YgYXJnLmZpbGwgPT09ICdmdW5jdGlvbidcbiAgICAmJiB0eXBlb2YgYXJnLnJlYWRVSW50OCA9PT0gJ2Z1bmN0aW9uJztcbn0iLCIvLyBDb3B5cmlnaHQgSm95ZW50LCBJbmMuIGFuZCBvdGhlciBOb2RlIGNvbnRyaWJ1dG9ycy5cbi8vXG4vLyBQZXJtaXNzaW9uIGlzIGhlcmVieSBncmFudGVkLCBmcmVlIG9mIGNoYXJnZSwgdG8gYW55IHBlcnNvbiBvYnRhaW5pbmcgYVxuLy8gY29weSBvZiB0aGlzIHNvZnR3YXJlIGFuZCBhc3NvY2lhdGVkIGRvY3VtZW50YXRpb24gZmlsZXMgKHRoZVxuLy8gXCJTb2Z0d2FyZVwiKSwgdG8gZGVhbCBpbiB0aGUgU29mdHdhcmUgd2l0aG91dCByZXN0cmljdGlvbiwgaW5jbHVkaW5nXG4vLyB3aXRob3V0IGxpbWl0YXRpb24gdGhlIHJpZ2h0cyB0byB1c2UsIGNvcHksIG1vZGlmeSwgbWVyZ2UsIHB1Ymxpc2gsXG4vLyBkaXN0cmlidXRlLCBzdWJsaWNlbnNlLCBhbmQvb3Igc2VsbCBjb3BpZXMgb2YgdGhlIFNvZnR3YXJlLCBhbmQgdG8gcGVybWl0XG4vLyBwZXJzb25zIHRvIHdob20gdGhlIFNvZnR3YXJlIGlzIGZ1cm5pc2hlZCB0byBkbyBzbywgc3ViamVjdCB0byB0aGVcbi8vIGZvbGxvd2luZyBjb25kaXRpb25zOlxuLy9cbi8vIFRoZSBhYm92ZSBjb3B5cmlnaHQgbm90aWNlIGFuZCB0aGlzIHBlcm1pc3Npb24gbm90aWNlIHNoYWxsIGJlIGluY2x1ZGVkXG4vLyBpbiBhbGwgY29waWVzIG9yIHN1YnN0YW50aWFsIHBvcnRpb25zIG9mIHRoZSBTb2Z0d2FyZS5cbi8vXG4vLyBUSEUgU09GVFdBUkUgSVMgUFJPVklERUQgXCJBUyBJU1wiLCBXSVRIT1VUIFdBUlJBTlRZIE9GIEFOWSBLSU5ELCBFWFBSRVNTXG4vLyBPUiBJTVBMSUVELCBJTkNMVURJTkcgQlVUIE5PVCBMSU1JVEVEIFRPIFRIRSBXQVJSQU5USUVTIE9GXG4vLyBNRVJDSEFOVEFCSUxJVFksIEZJVE5FU1MgRk9SIEEgUEFSVElDVUxBUiBQVVJQT1NFIEFORCBOT05JTkZSSU5HRU1FTlQuIElOXG4vLyBOTyBFVkVOVCBTSEFMTCBUSEUgQVVUSE9SUyBPUiBDT1BZUklHSFQgSE9MREVSUyBCRSBMSUFCTEUgRk9SIEFOWSBDTEFJTSxcbi8vIERBTUFHRVMgT1IgT1RIRVIgTElBQklMSVRZLCBXSEVUSEVSIElOIEFOIEFDVElPTiBPRiBDT05UUkFDVCwgVE9SVCBPUlxuLy8gT1RIRVJXSVNFLCBBUklTSU5HIEZST00sIE9VVCBPRiBPUiBJTiBDT05ORUNUSU9OIFdJVEggVEhFIFNPRlRXQVJFIE9SIFRIRVxuLy8gVVNFIE9SIE9USEVSIERFQUxJTkdTIElOIFRIRSBTT0ZUV0FSRS5cblxudmFyIGZvcm1hdFJlZ0V4cCA9IC8lW3NkaiVdL2c7XG5leHBvcnRzLmZvcm1hdCA9IGZ1bmN0aW9uKGYpIHtcbiAgaWYgKCFpc1N0cmluZyhmKSkge1xuICAgIHZhciBvYmplY3RzID0gW107XG4gICAgZm9yICh2YXIgaSA9IDA7IGkgPCBhcmd1bWVudHMubGVuZ3RoOyBpKyspIHtcbiAgICAgIG9iamVjdHMucHVzaChpbnNwZWN0KGFyZ3VtZW50c1tpXSkpO1xuICAgIH1cbiAgICByZXR1cm4gb2JqZWN0cy5qb2luKCcgJyk7XG4gIH1cblxuICB2YXIgaSA9IDE7XG4gIHZhciBhcmdzID0gYXJndW1lbnRzO1xuICB2YXIgbGVuID0gYXJncy5sZW5ndGg7XG4gIHZhciBzdHIgPSBTdHJpbmcoZikucmVwbGFjZShmb3JtYXRSZWdFeHAsIGZ1bmN0aW9uKHgpIHtcbiAgICBpZiAoeCA9PT0gJyUlJykgcmV0dXJuICclJztcbiAgICBpZiAoaSA+PSBsZW4pIHJldHVybiB4O1xuICAgIHN3aXRjaCAoeCkge1xuICAgICAgY2FzZSAnJXMnOiByZXR1cm4gU3RyaW5nKGFyZ3NbaSsrXSk7XG4gICAgICBjYXNlICclZCc6IHJldHVybiBOdW1iZXIoYXJnc1tpKytdKTtcbiAgICAgIGNhc2UgJyVqJzpcbiAgICAgICAgdHJ5IHtcbiAgICAgICAgICByZXR1cm4gSlNPTi5zdHJpbmdpZnkoYXJnc1tpKytdKTtcbiAgICAgICAgfSBjYXRjaCAoXykge1xuICAgICAgICAgIHJldHVybiAnW0NpcmN1bGFyXSc7XG4gICAgICAgIH1cbiAgICAgIGRlZmF1bHQ6XG4gICAgICAgIHJldHVybiB4O1xuICAgIH1cbiAgfSk7XG4gIGZvciAodmFyIHggPSBhcmdzW2ldOyBpIDwgbGVuOyB4ID0gYXJnc1srK2ldKSB7XG4gICAgaWYgKGlzTnVsbCh4KSB8fCAhaXNPYmplY3QoeCkpIHtcbiAgICAgIHN0ciArPSAnICcgKyB4O1xuICAgIH0gZWxzZSB7XG4gICAgICBzdHIgKz0gJyAnICsgaW5zcGVjdCh4KTtcbiAgICB9XG4gIH1cbiAgcmV0dXJuIHN0cjtcbn07XG5cblxuLy8gTWFyayB0aGF0IGEgbWV0aG9kIHNob3VsZCBub3QgYmUgdXNlZC5cbi8vIFJldHVybnMgYSBtb2RpZmllZCBmdW5jdGlvbiB3aGljaCB3YXJucyBvbmNlIGJ5IGRlZmF1bHQuXG4vLyBJZiAtLW5vLWRlcHJlY2F0aW9uIGlzIHNldCwgdGhlbiBpdCBpcyBhIG5vLW9wLlxuZXhwb3J0cy5kZXByZWNhdGUgPSBmdW5jdGlvbihmbiwgbXNnKSB7XG4gIC8vIEFsbG93IGZvciBkZXByZWNhdGluZyB0aGluZ3MgaW4gdGhlIHByb2Nlc3Mgb2Ygc3RhcnRpbmcgdXAuXG4gIGlmIChpc1VuZGVmaW5lZChnbG9iYWwucHJvY2VzcykpIHtcbiAgICByZXR1cm4gZnVuY3Rpb24oKSB7XG4gICAgICByZXR1cm4gZXhwb3J0cy5kZXByZWNhdGUoZm4sIG1zZykuYXBwbHkodGhpcywgYXJndW1lbnRzKTtcbiAgICB9O1xuICB9XG5cbiAgaWYgKHByb2Nlc3Mubm9EZXByZWNhdGlvbiA9PT0gdHJ1ZSkge1xuICAgIHJldHVybiBmbjtcbiAgfVxuXG4gIHZhciB3YXJuZWQgPSBmYWxzZTtcbiAgZnVuY3Rpb24gZGVwcmVjYXRlZCgpIHtcbiAgICBpZiAoIXdhcm5lZCkge1xuICAgICAgaWYgKHByb2Nlc3MudGhyb3dEZXByZWNhdGlvbikge1xuICAgICAgICB0aHJvdyBuZXcgRXJyb3IobXNnKTtcbiAgICAgIH0gZWxzZSBpZiAocHJvY2Vzcy50cmFjZURlcHJlY2F0aW9uKSB7XG4gICAgICAgIGNvbnNvbGUudHJhY2UobXNnKTtcbiAgICAgIH0gZWxzZSB7XG4gICAgICAgIGNvbnNvbGUuZXJyb3IobXNnKTtcbiAgICAgIH1cbiAgICAgIHdhcm5lZCA9IHRydWU7XG4gICAgfVxuICAgIHJldHVybiBmbi5hcHBseSh0aGlzLCBhcmd1bWVudHMpO1xuICB9XG5cbiAgcmV0dXJuIGRlcHJlY2F0ZWQ7XG59O1xuXG5cbnZhciBkZWJ1Z3MgPSB7fTtcbnZhciBkZWJ1Z0Vudmlyb247XG5leHBvcnRzLmRlYnVnbG9nID0gZnVuY3Rpb24oc2V0KSB7XG4gIGlmIChpc1VuZGVmaW5lZChkZWJ1Z0Vudmlyb24pKVxuICAgIGRlYnVnRW52aXJvbiA9IHByb2Nlc3MuZW52Lk5PREVfREVCVUcgfHwgJyc7XG4gIHNldCA9IHNldC50b1VwcGVyQ2FzZSgpO1xuICBpZiAoIWRlYnVnc1tzZXRdKSB7XG4gICAgaWYgKG5ldyBSZWdFeHAoJ1xcXFxiJyArIHNldCArICdcXFxcYicsICdpJykudGVzdChkZWJ1Z0Vudmlyb24pKSB7XG4gICAgICB2YXIgcGlkID0gcHJvY2Vzcy5waWQ7XG4gICAgICBkZWJ1Z3Nbc2V0XSA9IGZ1bmN0aW9uKCkge1xuICAgICAgICB2YXIgbXNnID0gZXhwb3J0cy5mb3JtYXQuYXBwbHkoZXhwb3J0cywgYXJndW1lbnRzKTtcbiAgICAgICAgY29uc29sZS5lcnJvcignJXMgJWQ6ICVzJywgc2V0LCBwaWQsIG1zZyk7XG4gICAgICB9O1xuICAgIH0gZWxzZSB7XG4gICAgICBkZWJ1Z3Nbc2V0XSA9IGZ1bmN0aW9uKCkge307XG4gICAgfVxuICB9XG4gIHJldHVybiBkZWJ1Z3Nbc2V0XTtcbn07XG5cblxuLyoqXG4gKiBFY2hvcyB0aGUgdmFsdWUgb2YgYSB2YWx1ZS4gVHJ5cyB0byBwcmludCB0aGUgdmFsdWUgb3V0XG4gKiBpbiB0aGUgYmVzdCB3YXkgcG9zc2libGUgZ2l2ZW4gdGhlIGRpZmZlcmVudCB0eXBlcy5cbiAqXG4gKiBAcGFyYW0ge09iamVjdH0gb2JqIFRoZSBvYmplY3QgdG8gcHJpbnQgb3V0LlxuICogQHBhcmFtIHtPYmplY3R9IG9wdHMgT3B0aW9uYWwgb3B0aW9ucyBvYmplY3QgdGhhdCBhbHRlcnMgdGhlIG91dHB1dC5cbiAqL1xuLyogbGVnYWN5OiBvYmosIHNob3dIaWRkZW4sIGRlcHRoLCBjb2xvcnMqL1xuZnVuY3Rpb24gaW5zcGVjdChvYmosIG9wdHMpIHtcbiAgLy8gZGVmYXVsdCBvcHRpb25zXG4gIHZhciBjdHggPSB7XG4gICAgc2VlbjogW10sXG4gICAgc3R5bGl6ZTogc3R5bGl6ZU5vQ29sb3JcbiAgfTtcbiAgLy8gbGVnYWN5Li4uXG4gIGlmIChhcmd1bWVudHMubGVuZ3RoID49IDMpIGN0eC5kZXB0aCA9IGFyZ3VtZW50c1syXTtcbiAgaWYgKGFyZ3VtZW50cy5sZW5ndGggPj0gNCkgY3R4LmNvbG9ycyA9IGFyZ3VtZW50c1szXTtcbiAgaWYgKGlzQm9vbGVhbihvcHRzKSkge1xuICAgIC8vIGxlZ2FjeS4uLlxuICAgIGN0eC5zaG93SGlkZGVuID0gb3B0cztcbiAgfSBlbHNlIGlmIChvcHRzKSB7XG4gICAgLy8gZ290IGFuIFwib3B0aW9uc1wiIG9iamVjdFxuICAgIGV4cG9ydHMuX2V4dGVuZChjdHgsIG9wdHMpO1xuICB9XG4gIC8vIHNldCBkZWZhdWx0IG9wdGlvbnNcbiAgaWYgKGlzVW5kZWZpbmVkKGN0eC5zaG93SGlkZGVuKSkgY3R4LnNob3dIaWRkZW4gPSBmYWxzZTtcbiAgaWYgKGlzVW5kZWZpbmVkKGN0eC5kZXB0aCkpIGN0eC5kZXB0aCA9IDI7XG4gIGlmIChpc1VuZGVmaW5lZChjdHguY29sb3JzKSkgY3R4LmNvbG9ycyA9IGZhbHNlO1xuICBpZiAoaXNVbmRlZmluZWQoY3R4LmN1c3RvbUluc3BlY3QpKSBjdHguY3VzdG9tSW5zcGVjdCA9IHRydWU7XG4gIGlmIChjdHguY29sb3JzKSBjdHguc3R5bGl6ZSA9IHN0eWxpemVXaXRoQ29sb3I7XG4gIHJldHVybiBmb3JtYXRWYWx1ZShjdHgsIG9iaiwgY3R4LmRlcHRoKTtcbn1cbmV4cG9ydHMuaW5zcGVjdCA9IGluc3BlY3Q7XG5cblxuLy8gaHR0cDovL2VuLndpa2lwZWRpYS5vcmcvd2lraS9BTlNJX2VzY2FwZV9jb2RlI2dyYXBoaWNzXG5pbnNwZWN0LmNvbG9ycyA9IHtcbiAgJ2JvbGQnIDogWzEsIDIyXSxcbiAgJ2l0YWxpYycgOiBbMywgMjNdLFxuICAndW5kZXJsaW5lJyA6IFs0LCAyNF0sXG4gICdpbnZlcnNlJyA6IFs3LCAyN10sXG4gICd3aGl0ZScgOiBbMzcsIDM5XSxcbiAgJ2dyZXknIDogWzkwLCAzOV0sXG4gICdibGFjaycgOiBbMzAsIDM5XSxcbiAgJ2JsdWUnIDogWzM0LCAzOV0sXG4gICdjeWFuJyA6IFszNiwgMzldLFxuICAnZ3JlZW4nIDogWzMyLCAzOV0sXG4gICdtYWdlbnRhJyA6IFszNSwgMzldLFxuICAncmVkJyA6IFszMSwgMzldLFxuICAneWVsbG93JyA6IFszMywgMzldXG59O1xuXG4vLyBEb24ndCB1c2UgJ2JsdWUnIG5vdCB2aXNpYmxlIG9uIGNtZC5leGVcbmluc3BlY3Quc3R5bGVzID0ge1xuICAnc3BlY2lhbCc6ICdjeWFuJyxcbiAgJ251bWJlcic6ICd5ZWxsb3cnLFxuICAnYm9vbGVhbic6ICd5ZWxsb3cnLFxuICAndW5kZWZpbmVkJzogJ2dyZXknLFxuICAnbnVsbCc6ICdib2xkJyxcbiAgJ3N0cmluZyc6ICdncmVlbicsXG4gICdkYXRlJzogJ21hZ2VudGEnLFxuICAvLyBcIm5hbWVcIjogaW50ZW50aW9uYWxseSBub3Qgc3R5bGluZ1xuICAncmVnZXhwJzogJ3JlZCdcbn07XG5cblxuZnVuY3Rpb24gc3R5bGl6ZVdpdGhDb2xvcihzdHIsIHN0eWxlVHlwZSkge1xuICB2YXIgc3R5bGUgPSBpbnNwZWN0LnN0eWxlc1tzdHlsZVR5cGVdO1xuXG4gIGlmIChzdHlsZSkge1xuICAgIHJldHVybiAnXFx1MDAxYlsnICsgaW5zcGVjdC5jb2xvcnNbc3R5bGVdWzBdICsgJ20nICsgc3RyICtcbiAgICAgICAgICAgJ1xcdTAwMWJbJyArIGluc3BlY3QuY29sb3JzW3N0eWxlXVsxXSArICdtJztcbiAgfSBlbHNlIHtcbiAgICByZXR1cm4gc3RyO1xuICB9XG59XG5cblxuZnVuY3Rpb24gc3R5bGl6ZU5vQ29sb3Ioc3RyLCBzdHlsZVR5cGUpIHtcbiAgcmV0dXJuIHN0cjtcbn1cblxuXG5mdW5jdGlvbiBhcnJheVRvSGFzaChhcnJheSkge1xuICB2YXIgaGFzaCA9IHt9O1xuXG4gIGFycmF5LmZvckVhY2goZnVuY3Rpb24odmFsLCBpZHgpIHtcbiAgICBoYXNoW3ZhbF0gPSB0cnVlO1xuICB9KTtcblxuICByZXR1cm4gaGFzaDtcbn1cblxuXG5mdW5jdGlvbiBmb3JtYXRWYWx1ZShjdHgsIHZhbHVlLCByZWN1cnNlVGltZXMpIHtcbiAgLy8gUHJvdmlkZSBhIGhvb2sgZm9yIHVzZXItc3BlY2lmaWVkIGluc3BlY3QgZnVuY3Rpb25zLlxuICAvLyBDaGVjayB0aGF0IHZhbHVlIGlzIGFuIG9iamVjdCB3aXRoIGFuIGluc3BlY3QgZnVuY3Rpb24gb24gaXRcbiAgaWYgKGN0eC5jdXN0b21JbnNwZWN0ICYmXG4gICAgICB2YWx1ZSAmJlxuICAgICAgaXNGdW5jdGlvbih2YWx1ZS5pbnNwZWN0KSAmJlxuICAgICAgLy8gRmlsdGVyIG91dCB0aGUgdXRpbCBtb2R1bGUsIGl0J3MgaW5zcGVjdCBmdW5jdGlvbiBpcyBzcGVjaWFsXG4gICAgICB2YWx1ZS5pbnNwZWN0ICE9PSBleHBvcnRzLmluc3BlY3QgJiZcbiAgICAgIC8vIEFsc28gZmlsdGVyIG91dCBhbnkgcHJvdG90eXBlIG9iamVjdHMgdXNpbmcgdGhlIGNpcmN1bGFyIGNoZWNrLlxuICAgICAgISh2YWx1ZS5jb25zdHJ1Y3RvciAmJiB2YWx1ZS5jb25zdHJ1Y3Rvci5wcm90b3R5cGUgPT09IHZhbHVlKSkge1xuICAgIHZhciByZXQgPSB2YWx1ZS5pbnNwZWN0KHJlY3Vyc2VUaW1lcywgY3R4KTtcbiAgICBpZiAoIWlzU3RyaW5nKHJldCkpIHtcbiAgICAgIHJldCA9IGZvcm1hdFZhbHVlKGN0eCwgcmV0LCByZWN1cnNlVGltZXMpO1xuICAgIH1cbiAgICByZXR1cm4gcmV0O1xuICB9XG5cbiAgLy8gUHJpbWl0aXZlIHR5cGVzIGNhbm5vdCBoYXZlIHByb3BlcnRpZXNcbiAgdmFyIHByaW1pdGl2ZSA9IGZvcm1hdFByaW1pdGl2ZShjdHgsIHZhbHVlKTtcbiAgaWYgKHByaW1pdGl2ZSkge1xuICAgIHJldHVybiBwcmltaXRpdmU7XG4gIH1cblxuICAvLyBMb29rIHVwIHRoZSBrZXlzIG9mIHRoZSBvYmplY3QuXG4gIHZhciBrZXlzID0gT2JqZWN0LmtleXModmFsdWUpO1xuICB2YXIgdmlzaWJsZUtleXMgPSBhcnJheVRvSGFzaChrZXlzKTtcblxuICBpZiAoY3R4LnNob3dIaWRkZW4pIHtcbiAgICBrZXlzID0gT2JqZWN0LmdldE93blByb3BlcnR5TmFtZXModmFsdWUpO1xuICB9XG5cbiAgLy8gSUUgZG9lc24ndCBtYWtlIGVycm9yIGZpZWxkcyBub24tZW51bWVyYWJsZVxuICAvLyBodHRwOi8vbXNkbi5taWNyb3NvZnQuY29tL2VuLXVzL2xpYnJhcnkvaWUvZHd3NTJzYnQodj12cy45NCkuYXNweFxuICBpZiAoaXNFcnJvcih2YWx1ZSlcbiAgICAgICYmIChrZXlzLmluZGV4T2YoJ21lc3NhZ2UnKSA+PSAwIHx8IGtleXMuaW5kZXhPZignZGVzY3JpcHRpb24nKSA+PSAwKSkge1xuICAgIHJldHVybiBmb3JtYXRFcnJvcih2YWx1ZSk7XG4gIH1cblxuICAvLyBTb21lIHR5cGUgb2Ygb2JqZWN0IHdpdGhvdXQgcHJvcGVydGllcyBjYW4gYmUgc2hvcnRjdXR0ZWQuXG4gIGlmIChrZXlzLmxlbmd0aCA9PT0gMCkge1xuICAgIGlmIChpc0Z1bmN0aW9uKHZhbHVlKSkge1xuICAgICAgdmFyIG5hbWUgPSB2YWx1ZS5uYW1lID8gJzogJyArIHZhbHVlLm5hbWUgOiAnJztcbiAgICAgIHJldHVybiBjdHguc3R5bGl6ZSgnW0Z1bmN0aW9uJyArIG5hbWUgKyAnXScsICdzcGVjaWFsJyk7XG4gICAgfVxuICAgIGlmIChpc1JlZ0V4cCh2YWx1ZSkpIHtcbiAgICAgIHJldHVybiBjdHguc3R5bGl6ZShSZWdFeHAucHJvdG90eXBlLnRvU3RyaW5nLmNhbGwodmFsdWUpLCAncmVnZXhwJyk7XG4gICAgfVxuICAgIGlmIChpc0RhdGUodmFsdWUpKSB7XG4gICAgICByZXR1cm4gY3R4LnN0eWxpemUoRGF0ZS5wcm90b3R5cGUudG9TdHJpbmcuY2FsbCh2YWx1ZSksICdkYXRlJyk7XG4gICAgfVxuICAgIGlmIChpc0Vycm9yKHZhbHVlKSkge1xuICAgICAgcmV0dXJuIGZvcm1hdEVycm9yKHZhbHVlKTtcbiAgICB9XG4gIH1cblxuICB2YXIgYmFzZSA9ICcnLCBhcnJheSA9IGZhbHNlLCBicmFjZXMgPSBbJ3snLCAnfSddO1xuXG4gIC8vIE1ha2UgQXJyYXkgc2F5IHRoYXQgdGhleSBhcmUgQXJyYXlcbiAgaWYgKGlzQXJyYXkodmFsdWUpKSB7XG4gICAgYXJyYXkgPSB0cnVlO1xuICAgIGJyYWNlcyA9IFsnWycsICddJ107XG4gIH1cblxuICAvLyBNYWtlIGZ1bmN0aW9ucyBzYXkgdGhhdCB0aGV5IGFyZSBmdW5jdGlvbnNcbiAgaWYgKGlzRnVuY3Rpb24odmFsdWUpKSB7XG4gICAgdmFyIG4gPSB2YWx1ZS5uYW1lID8gJzogJyArIHZhbHVlLm5hbWUgOiAnJztcbiAgICBiYXNlID0gJyBbRnVuY3Rpb24nICsgbiArICddJztcbiAgfVxuXG4gIC8vIE1ha2UgUmVnRXhwcyBzYXkgdGhhdCB0aGV5IGFyZSBSZWdFeHBzXG4gIGlmIChpc1JlZ0V4cCh2YWx1ZSkpIHtcbiAgICBiYXNlID0gJyAnICsgUmVnRXhwLnByb3RvdHlwZS50b1N0cmluZy5jYWxsKHZhbHVlKTtcbiAgfVxuXG4gIC8vIE1ha2UgZGF0ZXMgd2l0aCBwcm9wZXJ0aWVzIGZpcnN0IHNheSB0aGUgZGF0ZVxuICBpZiAoaXNEYXRlKHZhbHVlKSkge1xuICAgIGJhc2UgPSAnICcgKyBEYXRlLnByb3RvdHlwZS50b1VUQ1N0cmluZy5jYWxsKHZhbHVlKTtcbiAgfVxuXG4gIC8vIE1ha2UgZXJyb3Igd2l0aCBtZXNzYWdlIGZpcnN0IHNheSB0aGUgZXJyb3JcbiAgaWYgKGlzRXJyb3IodmFsdWUpKSB7XG4gICAgYmFzZSA9ICcgJyArIGZvcm1hdEVycm9yKHZhbHVlKTtcbiAgfVxuXG4gIGlmIChrZXlzLmxlbmd0aCA9PT0gMCAmJiAoIWFycmF5IHx8IHZhbHVlLmxlbmd0aCA9PSAwKSkge1xuICAgIHJldHVybiBicmFjZXNbMF0gKyBiYXNlICsgYnJhY2VzWzFdO1xuICB9XG5cbiAgaWYgKHJlY3Vyc2VUaW1lcyA8IDApIHtcbiAgICBpZiAoaXNSZWdFeHAodmFsdWUpKSB7XG4gICAgICByZXR1cm4gY3R4LnN0eWxpemUoUmVnRXhwLnByb3RvdHlwZS50b1N0cmluZy5jYWxsKHZhbHVlKSwgJ3JlZ2V4cCcpO1xuICAgIH0gZWxzZSB7XG4gICAgICByZXR1cm4gY3R4LnN0eWxpemUoJ1tPYmplY3RdJywgJ3NwZWNpYWwnKTtcbiAgICB9XG4gIH1cblxuICBjdHguc2Vlbi5wdXNoKHZhbHVlKTtcblxuICB2YXIgb3V0cHV0O1xuICBpZiAoYXJyYXkpIHtcbiAgICBvdXRwdXQgPSBmb3JtYXRBcnJheShjdHgsIHZhbHVlLCByZWN1cnNlVGltZXMsIHZpc2libGVLZXlzLCBrZXlzKTtcbiAgfSBlbHNlIHtcbiAgICBvdXRwdXQgPSBrZXlzLm1hcChmdW5jdGlvbihrZXkpIHtcbiAgICAgIHJldHVybiBmb3JtYXRQcm9wZXJ0eShjdHgsIHZhbHVlLCByZWN1cnNlVGltZXMsIHZpc2libGVLZXlzLCBrZXksIGFycmF5KTtcbiAgICB9KTtcbiAgfVxuXG4gIGN0eC5zZWVuLnBvcCgpO1xuXG4gIHJldHVybiByZWR1Y2VUb1NpbmdsZVN0cmluZyhvdXRwdXQsIGJhc2UsIGJyYWNlcyk7XG59XG5cblxuZnVuY3Rpb24gZm9ybWF0UHJpbWl0aXZlKGN0eCwgdmFsdWUpIHtcbiAgaWYgKGlzVW5kZWZpbmVkKHZhbHVlKSlcbiAgICByZXR1cm4gY3R4LnN0eWxpemUoJ3VuZGVmaW5lZCcsICd1bmRlZmluZWQnKTtcbiAgaWYgKGlzU3RyaW5nKHZhbHVlKSkge1xuICAgIHZhciBzaW1wbGUgPSAnXFwnJyArIEpTT04uc3RyaW5naWZ5KHZhbHVlKS5yZXBsYWNlKC9eXCJ8XCIkL2csICcnKVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgLnJlcGxhY2UoLycvZywgXCJcXFxcJ1wiKVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgLnJlcGxhY2UoL1xcXFxcIi9nLCAnXCInKSArICdcXCcnO1xuICAgIHJldHVybiBjdHguc3R5bGl6ZShzaW1wbGUsICdzdHJpbmcnKTtcbiAgfVxuICBpZiAoaXNOdW1iZXIodmFsdWUpKVxuICAgIHJldHVybiBjdHguc3R5bGl6ZSgnJyArIHZhbHVlLCAnbnVtYmVyJyk7XG4gIGlmIChpc0Jvb2xlYW4odmFsdWUpKVxuICAgIHJldHVybiBjdHguc3R5bGl6ZSgnJyArIHZhbHVlLCAnYm9vbGVhbicpO1xuICAvLyBGb3Igc29tZSByZWFzb24gdHlwZW9mIG51bGwgaXMgXCJvYmplY3RcIiwgc28gc3BlY2lhbCBjYXNlIGhlcmUuXG4gIGlmIChpc051bGwodmFsdWUpKVxuICAgIHJldHVybiBjdHguc3R5bGl6ZSgnbnVsbCcsICdudWxsJyk7XG59XG5cblxuZnVuY3Rpb24gZm9ybWF0RXJyb3IodmFsdWUpIHtcbiAgcmV0dXJuICdbJyArIEVycm9yLnByb3RvdHlwZS50b1N0cmluZy5jYWxsKHZhbHVlKSArICddJztcbn1cblxuXG5mdW5jdGlvbiBmb3JtYXRBcnJheShjdHgsIHZhbHVlLCByZWN1cnNlVGltZXMsIHZpc2libGVLZXlzLCBrZXlzKSB7XG4gIHZhciBvdXRwdXQgPSBbXTtcbiAgZm9yICh2YXIgaSA9IDAsIGwgPSB2YWx1ZS5sZW5ndGg7IGkgPCBsOyArK2kpIHtcbiAgICBpZiAoaGFzT3duUHJvcGVydHkodmFsdWUsIFN0cmluZyhpKSkpIHtcbiAgICAgIG91dHB1dC5wdXNoKGZvcm1hdFByb3BlcnR5KGN0eCwgdmFsdWUsIHJlY3Vyc2VUaW1lcywgdmlzaWJsZUtleXMsXG4gICAgICAgICAgU3RyaW5nKGkpLCB0cnVlKSk7XG4gICAgfSBlbHNlIHtcbiAgICAgIG91dHB1dC5wdXNoKCcnKTtcbiAgICB9XG4gIH1cbiAga2V5cy5mb3JFYWNoKGZ1bmN0aW9uKGtleSkge1xuICAgIGlmICgha2V5Lm1hdGNoKC9eXFxkKyQvKSkge1xuICAgICAgb3V0cHV0LnB1c2goZm9ybWF0UHJvcGVydHkoY3R4LCB2YWx1ZSwgcmVjdXJzZVRpbWVzLCB2aXNpYmxlS2V5cyxcbiAgICAgICAgICBrZXksIHRydWUpKTtcbiAgICB9XG4gIH0pO1xuICByZXR1cm4gb3V0cHV0O1xufVxuXG5cbmZ1bmN0aW9uIGZvcm1hdFByb3BlcnR5KGN0eCwgdmFsdWUsIHJlY3Vyc2VUaW1lcywgdmlzaWJsZUtleXMsIGtleSwgYXJyYXkpIHtcbiAgdmFyIG5hbWUsIHN0ciwgZGVzYztcbiAgZGVzYyA9IE9iamVjdC5nZXRPd25Qcm9wZXJ0eURlc2NyaXB0b3IodmFsdWUsIGtleSkgfHwgeyB2YWx1ZTogdmFsdWVba2V5XSB9O1xuICBpZiAoZGVzYy5nZXQpIHtcbiAgICBpZiAoZGVzYy5zZXQpIHtcbiAgICAgIHN0ciA9IGN0eC5zdHlsaXplKCdbR2V0dGVyL1NldHRlcl0nLCAnc3BlY2lhbCcpO1xuICAgIH0gZWxzZSB7XG4gICAgICBzdHIgPSBjdHguc3R5bGl6ZSgnW0dldHRlcl0nLCAnc3BlY2lhbCcpO1xuICAgIH1cbiAgfSBlbHNlIHtcbiAgICBpZiAoZGVzYy5zZXQpIHtcbiAgICAgIHN0ciA9IGN0eC5zdHlsaXplKCdbU2V0dGVyXScsICdzcGVjaWFsJyk7XG4gICAgfVxuICB9XG4gIGlmICghaGFzT3duUHJvcGVydHkodmlzaWJsZUtleXMsIGtleSkpIHtcbiAgICBuYW1lID0gJ1snICsga2V5ICsgJ10nO1xuICB9XG4gIGlmICghc3RyKSB7XG4gICAgaWYgKGN0eC5zZWVuLmluZGV4T2YoZGVzYy52YWx1ZSkgPCAwKSB7XG4gICAgICBpZiAoaXNOdWxsKHJlY3Vyc2VUaW1lcykpIHtcbiAgICAgICAgc3RyID0gZm9ybWF0VmFsdWUoY3R4LCBkZXNjLnZhbHVlLCBudWxsKTtcbiAgICAgIH0gZWxzZSB7XG4gICAgICAgIHN0ciA9IGZvcm1hdFZhbHVlKGN0eCwgZGVzYy52YWx1ZSwgcmVjdXJzZVRpbWVzIC0gMSk7XG4gICAgICB9XG4gICAgICBpZiAoc3RyLmluZGV4T2YoJ1xcbicpID4gLTEpIHtcbiAgICAgICAgaWYgKGFycmF5KSB7XG4gICAgICAgICAgc3RyID0gc3RyLnNwbGl0KCdcXG4nKS5tYXAoZnVuY3Rpb24obGluZSkge1xuICAgICAgICAgICAgcmV0dXJuICcgICcgKyBsaW5lO1xuICAgICAgICAgIH0pLmpvaW4oJ1xcbicpLnN1YnN0cigyKTtcbiAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICBzdHIgPSAnXFxuJyArIHN0ci5zcGxpdCgnXFxuJykubWFwKGZ1bmN0aW9uKGxpbmUpIHtcbiAgICAgICAgICAgIHJldHVybiAnICAgJyArIGxpbmU7XG4gICAgICAgICAgfSkuam9pbignXFxuJyk7XG4gICAgICAgIH1cbiAgICAgIH1cbiAgICB9IGVsc2Uge1xuICAgICAgc3RyID0gY3R4LnN0eWxpemUoJ1tDaXJjdWxhcl0nLCAnc3BlY2lhbCcpO1xuICAgIH1cbiAgfVxuICBpZiAoaXNVbmRlZmluZWQobmFtZSkpIHtcbiAgICBpZiAoYXJyYXkgJiYga2V5Lm1hdGNoKC9eXFxkKyQvKSkge1xuICAgICAgcmV0dXJuIHN0cjtcbiAgICB9XG4gICAgbmFtZSA9IEpTT04uc3RyaW5naWZ5KCcnICsga2V5KTtcbiAgICBpZiAobmFtZS5tYXRjaCgvXlwiKFthLXpBLVpfXVthLXpBLVpfMC05XSopXCIkLykpIHtcbiAgICAgIG5hbWUgPSBuYW1lLnN1YnN0cigxLCBuYW1lLmxlbmd0aCAtIDIpO1xuICAgICAgbmFtZSA9IGN0eC5zdHlsaXplKG5hbWUsICduYW1lJyk7XG4gICAgfSBlbHNlIHtcbiAgICAgIG5hbWUgPSBuYW1lLnJlcGxhY2UoLycvZywgXCJcXFxcJ1wiKVxuICAgICAgICAgICAgICAgICAucmVwbGFjZSgvXFxcXFwiL2csICdcIicpXG4gICAgICAgICAgICAgICAgIC5yZXBsYWNlKC8oXlwifFwiJCkvZywgXCInXCIpO1xuICAgICAgbmFtZSA9IGN0eC5zdHlsaXplKG5hbWUsICdzdHJpbmcnKTtcbiAgICB9XG4gIH1cblxuICByZXR1cm4gbmFtZSArICc6ICcgKyBzdHI7XG59XG5cblxuZnVuY3Rpb24gcmVkdWNlVG9TaW5nbGVTdHJpbmcob3V0cHV0LCBiYXNlLCBicmFjZXMpIHtcbiAgdmFyIG51bUxpbmVzRXN0ID0gMDtcbiAgdmFyIGxlbmd0aCA9IG91dHB1dC5yZWR1Y2UoZnVuY3Rpb24ocHJldiwgY3VyKSB7XG4gICAgbnVtTGluZXNFc3QrKztcbiAgICBpZiAoY3VyLmluZGV4T2YoJ1xcbicpID49IDApIG51bUxpbmVzRXN0Kys7XG4gICAgcmV0dXJuIHByZXYgKyBjdXIucmVwbGFjZSgvXFx1MDAxYlxcW1xcZFxcZD9tL2csICcnKS5sZW5ndGggKyAxO1xuICB9LCAwKTtcblxuICBpZiAobGVuZ3RoID4gNjApIHtcbiAgICByZXR1cm4gYnJhY2VzWzBdICtcbiAgICAgICAgICAgKGJhc2UgPT09ICcnID8gJycgOiBiYXNlICsgJ1xcbiAnKSArXG4gICAgICAgICAgICcgJyArXG4gICAgICAgICAgIG91dHB1dC5qb2luKCcsXFxuICAnKSArXG4gICAgICAgICAgICcgJyArXG4gICAgICAgICAgIGJyYWNlc1sxXTtcbiAgfVxuXG4gIHJldHVybiBicmFjZXNbMF0gKyBiYXNlICsgJyAnICsgb3V0cHV0LmpvaW4oJywgJykgKyAnICcgKyBicmFjZXNbMV07XG59XG5cblxuLy8gTk9URTogVGhlc2UgdHlwZSBjaGVja2luZyBmdW5jdGlvbnMgaW50ZW50aW9uYWxseSBkb24ndCB1c2UgYGluc3RhbmNlb2ZgXG4vLyBiZWNhdXNlIGl0IGlzIGZyYWdpbGUgYW5kIGNhbiBiZSBlYXNpbHkgZmFrZWQgd2l0aCBgT2JqZWN0LmNyZWF0ZSgpYC5cbmZ1bmN0aW9uIGlzQXJyYXkoYXIpIHtcbiAgcmV0dXJuIEFycmF5LmlzQXJyYXkoYXIpO1xufVxuZXhwb3J0cy5pc0FycmF5ID0gaXNBcnJheTtcblxuZnVuY3Rpb24gaXNCb29sZWFuKGFyZykge1xuICByZXR1cm4gdHlwZW9mIGFyZyA9PT0gJ2Jvb2xlYW4nO1xufVxuZXhwb3J0cy5pc0Jvb2xlYW4gPSBpc0Jvb2xlYW47XG5cbmZ1bmN0aW9uIGlzTnVsbChhcmcpIHtcbiAgcmV0dXJuIGFyZyA9PT0gbnVsbDtcbn1cbmV4cG9ydHMuaXNOdWxsID0gaXNOdWxsO1xuXG5mdW5jdGlvbiBpc051bGxPclVuZGVmaW5lZChhcmcpIHtcbiAgcmV0dXJuIGFyZyA9PSBudWxsO1xufVxuZXhwb3J0cy5pc051bGxPclVuZGVmaW5lZCA9IGlzTnVsbE9yVW5kZWZpbmVkO1xuXG5mdW5jdGlvbiBpc051bWJlcihhcmcpIHtcbiAgcmV0dXJuIHR5cGVvZiBhcmcgPT09ICdudW1iZXInO1xufVxuZXhwb3J0cy5pc051bWJlciA9IGlzTnVtYmVyO1xuXG5mdW5jdGlvbiBpc1N0cmluZyhhcmcpIHtcbiAgcmV0dXJuIHR5cGVvZiBhcmcgPT09ICdzdHJpbmcnO1xufVxuZXhwb3J0cy5pc1N0cmluZyA9IGlzU3RyaW5nO1xuXG5mdW5jdGlvbiBpc1N5bWJvbChhcmcpIHtcbiAgcmV0dXJuIHR5cGVvZiBhcmcgPT09ICdzeW1ib2wnO1xufVxuZXhwb3J0cy5pc1N5bWJvbCA9IGlzU3ltYm9sO1xuXG5mdW5jdGlvbiBpc1VuZGVmaW5lZChhcmcpIHtcbiAgcmV0dXJuIGFyZyA9PT0gdm9pZCAwO1xufVxuZXhwb3J0cy5pc1VuZGVmaW5lZCA9IGlzVW5kZWZpbmVkO1xuXG5mdW5jdGlvbiBpc1JlZ0V4cChyZSkge1xuICByZXR1cm4gaXNPYmplY3QocmUpICYmIG9iamVjdFRvU3RyaW5nKHJlKSA9PT0gJ1tvYmplY3QgUmVnRXhwXSc7XG59XG5leHBvcnRzLmlzUmVnRXhwID0gaXNSZWdFeHA7XG5cbmZ1bmN0aW9uIGlzT2JqZWN0KGFyZykge1xuICByZXR1cm4gdHlwZW9mIGFyZyA9PT0gJ29iamVjdCcgJiYgYXJnICE9PSBudWxsO1xufVxuZXhwb3J0cy5pc09iamVjdCA9IGlzT2JqZWN0O1xuXG5mdW5jdGlvbiBpc0RhdGUoZCkge1xuICByZXR1cm4gaXNPYmplY3QoZCkgJiYgb2JqZWN0VG9TdHJpbmcoZCkgPT09ICdbb2JqZWN0IERhdGVdJztcbn1cbmV4cG9ydHMuaXNEYXRlID0gaXNEYXRlO1xuXG5mdW5jdGlvbiBpc0Vycm9yKGUpIHtcbiAgcmV0dXJuIGlzT2JqZWN0KGUpICYmXG4gICAgICAob2JqZWN0VG9TdHJpbmcoZSkgPT09ICdbb2JqZWN0IEVycm9yXScgfHwgZSBpbnN0YW5jZW9mIEVycm9yKTtcbn1cbmV4cG9ydHMuaXNFcnJvciA9IGlzRXJyb3I7XG5cbmZ1bmN0aW9uIGlzRnVuY3Rpb24oYXJnKSB7XG4gIHJldHVybiB0eXBlb2YgYXJnID09PSAnZnVuY3Rpb24nO1xufVxuZXhwb3J0cy5pc0Z1bmN0aW9uID0gaXNGdW5jdGlvbjtcblxuZnVuY3Rpb24gaXNQcmltaXRpdmUoYXJnKSB7XG4gIHJldHVybiBhcmcgPT09IG51bGwgfHxcbiAgICAgICAgIHR5cGVvZiBhcmcgPT09ICdib29sZWFuJyB8fFxuICAgICAgICAgdHlwZW9mIGFyZyA9PT0gJ251bWJlcicgfHxcbiAgICAgICAgIHR5cGVvZiBhcmcgPT09ICdzdHJpbmcnIHx8XG4gICAgICAgICB0eXBlb2YgYXJnID09PSAnc3ltYm9sJyB8fCAgLy8gRVM2IHN5bWJvbFxuICAgICAgICAgdHlwZW9mIGFyZyA9PT0gJ3VuZGVmaW5lZCc7XG59XG5leHBvcnRzLmlzUHJpbWl0aXZlID0gaXNQcmltaXRpdmU7XG5cbmV4cG9ydHMuaXNCdWZmZXIgPSByZXF1aXJlKCcuL3N1cHBvcnQvaXNCdWZmZXInKTtcblxuZnVuY3Rpb24gb2JqZWN0VG9TdHJpbmcobykge1xuICByZXR1cm4gT2JqZWN0LnByb3RvdHlwZS50b1N0cmluZy5jYWxsKG8pO1xufVxuXG5cbmZ1bmN0aW9uIHBhZChuKSB7XG4gIHJldHVybiBuIDwgMTAgPyAnMCcgKyBuLnRvU3RyaW5nKDEwKSA6IG4udG9TdHJpbmcoMTApO1xufVxuXG5cbnZhciBtb250aHMgPSBbJ0phbicsICdGZWInLCAnTWFyJywgJ0FwcicsICdNYXknLCAnSnVuJywgJ0p1bCcsICdBdWcnLCAnU2VwJyxcbiAgICAgICAgICAgICAgJ09jdCcsICdOb3YnLCAnRGVjJ107XG5cbi8vIDI2IEZlYiAxNjoxOTozNFxuZnVuY3Rpb24gdGltZXN0YW1wKCkge1xuICB2YXIgZCA9IG5ldyBEYXRlKCk7XG4gIHZhciB0aW1lID0gW3BhZChkLmdldEhvdXJzKCkpLFxuICAgICAgICAgICAgICBwYWQoZC5nZXRNaW51dGVzKCkpLFxuICAgICAgICAgICAgICBwYWQoZC5nZXRTZWNvbmRzKCkpXS5qb2luKCc6Jyk7XG4gIHJldHVybiBbZC5nZXREYXRlKCksIG1vbnRoc1tkLmdldE1vbnRoKCldLCB0aW1lXS5qb2luKCcgJyk7XG59XG5cblxuLy8gbG9nIGlzIGp1c3QgYSB0aGluIHdyYXBwZXIgdG8gY29uc29sZS5sb2cgdGhhdCBwcmVwZW5kcyBhIHRpbWVzdGFtcFxuZXhwb3J0cy5sb2cgPSBmdW5jdGlvbigpIHtcbiAgY29uc29sZS5sb2coJyVzIC0gJXMnLCB0aW1lc3RhbXAoKSwgZXhwb3J0cy5mb3JtYXQuYXBwbHkoZXhwb3J0cywgYXJndW1lbnRzKSk7XG59O1xuXG5cbi8qKlxuICogSW5oZXJpdCB0aGUgcHJvdG90eXBlIG1ldGhvZHMgZnJvbSBvbmUgY29uc3RydWN0b3IgaW50byBhbm90aGVyLlxuICpcbiAqIFRoZSBGdW5jdGlvbi5wcm90b3R5cGUuaW5oZXJpdHMgZnJvbSBsYW5nLmpzIHJld3JpdHRlbiBhcyBhIHN0YW5kYWxvbmVcbiAqIGZ1bmN0aW9uIChub3Qgb24gRnVuY3Rpb24ucHJvdG90eXBlKS4gTk9URTogSWYgdGhpcyBmaWxlIGlzIHRvIGJlIGxvYWRlZFxuICogZHVyaW5nIGJvb3RzdHJhcHBpbmcgdGhpcyBmdW5jdGlvbiBuZWVkcyB0byBiZSByZXdyaXR0ZW4gdXNpbmcgc29tZSBuYXRpdmVcbiAqIGZ1bmN0aW9ucyBhcyBwcm90b3R5cGUgc2V0dXAgdXNpbmcgbm9ybWFsIEphdmFTY3JpcHQgZG9lcyBub3Qgd29yayBhc1xuICogZXhwZWN0ZWQgZHVyaW5nIGJvb3RzdHJhcHBpbmcgKHNlZSBtaXJyb3IuanMgaW4gcjExNDkwMykuXG4gKlxuICogQHBhcmFtIHtmdW5jdGlvbn0gY3RvciBDb25zdHJ1Y3RvciBmdW5jdGlvbiB3aGljaCBuZWVkcyB0byBpbmhlcml0IHRoZVxuICogICAgIHByb3RvdHlwZS5cbiAqIEBwYXJhbSB7ZnVuY3Rpb259IHN1cGVyQ3RvciBDb25zdHJ1Y3RvciBmdW5jdGlvbiB0byBpbmhlcml0IHByb3RvdHlwZSBmcm9tLlxuICovXG5leHBvcnRzLmluaGVyaXRzID0gcmVxdWlyZSgnaW5oZXJpdHMnKTtcblxuZXhwb3J0cy5fZXh0ZW5kID0gZnVuY3Rpb24ob3JpZ2luLCBhZGQpIHtcbiAgLy8gRG9uJ3QgZG8gYW55dGhpbmcgaWYgYWRkIGlzbid0IGFuIG9iamVjdFxuICBpZiAoIWFkZCB8fCAhaXNPYmplY3QoYWRkKSkgcmV0dXJuIG9yaWdpbjtcblxuICB2YXIga2V5cyA9IE9iamVjdC5rZXlzKGFkZCk7XG4gIHZhciBpID0ga2V5cy5sZW5ndGg7XG4gIHdoaWxlIChpLS0pIHtcbiAgICBvcmlnaW5ba2V5c1tpXV0gPSBhZGRba2V5c1tpXV07XG4gIH1cbiAgcmV0dXJuIG9yaWdpbjtcbn07XG5cbmZ1bmN0aW9uIGhhc093blByb3BlcnR5KG9iaiwgcHJvcCkge1xuICByZXR1cm4gT2JqZWN0LnByb3RvdHlwZS5oYXNPd25Qcm9wZXJ0eS5jYWxsKG9iaiwgcHJvcCk7XG59XG4iXX0=
