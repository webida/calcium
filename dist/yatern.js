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

},{"util":19}],2:[function(require,module,exports){
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
    return ["computed", null];
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
var constraints = [];
function clearConstraints() {
    visitedStatus.length = 0;
    constraints.length = 0;
}

var rtCX = undefined;
function addConstraints(ast, initStatus, newRtCX) {

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
        var propAcc = propAccess(node);

        constraints.push({ OBJ: objAVal,
            PROP: propAcc[1],
            READ_TO: ret });
        objAVal.propagate(new cstr.ReadProp(propAcc[1], ret));

        // returns AVal for receiver and read member
        return [objAVal, ret];
    }

    // constraint generating walker for expressions
    var constraintGenerator = walk.make({

        Identifier: function Identifier(node, curStatus, c) {
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
            if (node.left.type === 'Identifier') {
                // LHS is a simple variable.
                var varName = node.left.name;
                var lhsAVal = curStatus.sc.getAValOf(varName);
                // lhs is not visited. Need to handle here.
                // Use aval found in the scope for lhs
                Ĉ.set(node.left, curStatus.delta, lhsAVal);

                if (node.operator === '=') {
                    // simple assignment
                    constraints.push({
                        FROM: rhsAVal,
                        TO: lhsAVal
                    });
                    rhsAVal.propagate(lhsAVal);
                    // node's AVal from RHS
                    Ĉ.set(node, curStatus.delta, rhsAVal);
                    return rhsAVal;
                }
                // updating assignment
                var resAVal = Ĉ.get(node, curStatus.delta);
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
            } else if (node.left.type === 'MemberExpression') {
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
                    // node's AVal from RHS
                    Ĉ.set(node, curStatus.delta, rhsAVal);
                    return rhsAVal;
                }
                // updating assignment
                var resAVal = Ĉ.get(node, curStatus.delta);
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
                    constraints.push({ FROM: rhsAVal,
                        TO: lhsAVal });
                    rhsAVal.propagate(lhsAVal);
                }
            }
        },

        LogicalExpression: function LogicalExpression(node, curStatus, c) {
            var res = Ĉ.get(node, curStatus.delta);
            var left = c(node.left, curStatus, undefined);
            var right = c(node.right, curStatus, undefined);
            constraints.push({ FROM: left, TO: res }, { FROM: right, TO: res });
            left.propagate(res);
            right.propagate(res);
            return res;
        },

        ConditionalExpression: function ConditionalExpression(node, curStatus, c) {
            var res = Ĉ.get(node, curStatus.delta);
            c(node.test, curStatus, undefined);
            var cons = c(node.consequent, curStatus, undefined);
            var alt = c(node.alternate, curStatus, undefined);
            constraints.push({ FROM: cons, TO: res }, { FROM: alt, TO: res });
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
            constraints.push({ CONSTRUCTOR: callee,
                ARGS: args,
                RET: ret,
                EXC: curStatus.exc,
                DELTA: newDelta });
            callee.propagate(new cstr.IsCtor(args, ret, curStatus.exc, newDelta));
            return ret;
        },

        ArrayExpression: function ArrayExpression(node, curStatus, c) {
            var ret = Ĉ.get(node, curStatus.delta);
            // NOTE prototype object is not recorded in Ĉ
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
            var ret = Ĉ.get(node, curStatus.delta);
            // NOTE prototype object is not recorded in Ĉ
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
                // NOTE prototype object is not recorded in Ĉ
                fnInstance = new types.FnType(new types.AVal(rtCX.protos.Function), '[anonymous function]', node.body['@block'].getParamVarNames(), curStatus.sc, node, rtCX.protos.Object);
                node.fnInstances.push(fnInstance);
                // NOTE prototype object is not recorded in Ĉ
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
            var ret = Ĉ.get(node, curStatus.delta);
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
                // NOTE prototype object is not recorded in Ĉ
                fnInstance = new types.FnType(new types.AVal(rtCX.protos.Function), node.id.name, node.body['@block'].getParamVarNames(), sc0, node, rtCX.protos.Object);
                node.fnInstances.push(fnInstance);
                // for each fnInstance, assign one prototype object
                // NOTE prototype object is not recorded in Ĉ
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
            // use aval in the scope for function declaration
            Ĉ.set(node, curStatus.delta, lhsAVal);

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
            var lastAVal = c(node.expressions[lastIndex], curStatus, undefined);
            Ĉ.set(node, curStatus.delta, lastAVal);
            return lastAVal;
        },

        UnaryExpression: function UnaryExpression(node, curStatus, c) {
            c(node.argument, curStatus, undefined);
            var res = Ĉ.get(node, curStatus.delta);
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
            var res = Ĉ.get(node, curStatus.delta);
            constraints.push({ TYPE: types.PrimNumber,
                INCL_SET: res });
            res.addType(types.PrimNumber);
            // We ignore the effect of updating to number type
            return res;
        },

        BinaryExpression: function BinaryExpression(node, curStatus, c) {
            var lOprd = c(node.left, curStatus, undefined);
            var rOprd = c(node.right, curStatus, undefined);
            var res = Ĉ.get(node, curStatus.delta);

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

},{"../domains/status":5,"../domains/types":6,"./constraints":3,"acorn/dist/walk":15}],3:[function(require,module,exports){
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

function _classCallCheck(instance, Constructor) { if (!(instance instanceof Constructor)) { throw new TypeError('Cannot call a class as a function'); } }

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
function Type(name) {
    this.name = name;
}
Type.prototype = Object.create(null);
Type.prototype.getName = function () {
    return this.name;
};

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

var AbsCache = (function () {
    function AbsCache() {
        _classCallCheck(this, AbsCache);

        this.map = new Map();
    }

    // export

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
     * Get all the types of the loc
     * @param loc
     * @returns [Type]
     */

    AbsCache.prototype.getTypeOfLoc = function getTypeOfLoc(loc) {
        if (!this.map.has(loc)) {
            // no type is available
            return null;
        }
        var tps = [];
        for (var _iterator2 = this.map.get(loc).values(), _isArray2 = Array.isArray(_iterator2), _i2 = 0, _iterator2 = _isArray2 ? _iterator2 : _iterator2[Symbol.iterator]();;) {
            var _ref2;

            if (_isArray2) {
                if (_i2 >= _iterator2.length) break;
                _ref2 = _iterator2[_i2++];
            } else {
                _i2 = _iterator2.next();
                if (_i2.done) break;
                _ref2 = _i2.value;
            }

            var av = _ref2;

            for (var _iterator3 = av.getTypes(), _isArray3 = Array.isArray(_iterator3), _i3 = 0, _iterator3 = _isArray3 ? _iterator3 : _iterator3[Symbol.iterator]();;) {
                var _ref3;

                if (_isArray3) {
                    if (_i3 >= _iterator3.length) break;
                    _ref3 = _iterator3[_i3++];
                } else {
                    _i3 = _iterator3.next();
                    if (_i3.done) break;
                    _ref3 = _i3.value;
                }

                var tp = _ref3;

                if (tps.indexOf(tp) === -1) {
                    tps.push(tp);
                }
            }
        }
        return tps;
    };

    return AbsCache;
})();

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

exports.AbsCache = AbsCache;

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
var thisOccur = require('./thisOccur');
var myWalker = require('./util/myWalker');

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
        },
        Ĉ: new types.AbsCache()
    };
    cGen.addConstraints(ast, initStatus, rtCX);
    var constraints = cGen.constraints;
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
exports.findIdentifierAt = varRefs.findIdentifierAt;
exports.findVarRefsAt = varRefs.findVarRefsAt;
exports.onFunctionOrReturnKeyword = retOccur.onFunctionOrReturnKeyword;
exports.findReturnStatements = retOccur.findReturnStatements;
exports.onThisKeyword = thisOccur.onThisKeyword;
exports.findThisExpressions = thisOccur.findThisExpressions;
exports.findSurroundingNode = myWalker.findSurroundingNode;

},{"./aux":1,"./constraint/cGen":2,"./domains/context":4,"./domains/status":5,"./domains/types":6,"./retOccur":8,"./thisOccur":9,"./util/myWalker":10,"./varBlock":11,"./varrefs":12,"acorn/dist/acorn":13,"acorn/dist/acorn_loose":14}],8:[function(require,module,exports){
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
    "use strict";

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
    "use strict";
    var rets = [];
    if (fNode.type !== 'FunctionExpression' && fNode.type !== 'FunctionDeclaration') {
        throw Error('fNode should be a function node');
    }

    var walker = walk.make({
        ReturnStatement: function ReturnStatement(node) {
            return rets.push(node);
        },
        Function: function Function() {
            // not visit inner functions
        }
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
    "use strict";

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

},{"./util/myWalker":10,"acorn/dist/walk":15}],9:[function(require,module,exports){
'use strict';

var walk = require('acorn/dist/walk');
var myWalker = require('./util/myWalker');

/**
 * Check whether given pos is on a this keyword
 * @param ast - AST of a program
 * @param pos - index position
 * @returns {*} - function node or null
 */
function onThisKeyword(ast, pos) {
    "use strict";

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
    "use strict";
    var rets = [];
    if (fNode.type !== 'FunctionExpression' && fNode.type !== 'FunctionDeclaration') {
        throw Error('fNode should be a function node');
    }

    var walker = walk.make({
        ThisExpression: function ThisExpression(node) {
            return rets.push(node);
        },
        Function: function Function() {
            // not visit inner functions
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
    "use strict";

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

},{"./util/myWalker":10,"acorn/dist/walk":15}],10:[function(require,module,exports){
'use strict';

var walk = require('acorn/dist/walk');

/**
 * a walker that visits each id even though it is var declaration
 * the parameter vb denote varBlock
 */
var varWalker = walk.make({
    Function: function Function(node, vb, c) {
        'use strict';
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
        'use strict';
        for (var i = 0; i < node.declarations.length; ++i) {
            var decl = node.declarations[i];
            c(decl.id, vb);
            if (decl.init) c(decl.init, vb);
        }
    }
});

/**
 * Wrap a walker with pre- and post- actions
 *
 * @param preNode - Apply before visiting the current node.
 * If returns false, do not visit the node.
 * @param postNode - Apply after visiting the current node.
 * If given, return values are overridden.
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

    for (var nodeType in walker) {
        var _ret = _loop(nodeType);

        if (_ret === 'continue') continue;
    }
    return retWalker;
}

function findSurroundingNode(ast, start, end) {
    "use strict";
    function Found(node) {
        this.node = node;
    }

    var walker = wrapWalker(varWalker, function (node) {
        return !(node.start > start || node.end < end);
    }, function (node) {
        throw new Found(node);
    });

    try {
        walk.recursive(ast, undefined, walker);
    } catch (e) {
        if (e instanceof Found) {
            return e.node;
        } else {
            throw e;
        }
    }
    // node not found
    return null;
}

exports.wrapWalker = wrapWalker;
exports.varWalker = varWalker;
exports.findSurroundingNode = findSurroundingNode;

},{"acorn/dist/walk":15}],11:[function(require,module,exports){
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
    VariablePattern: function VariablePattern(node, currBlock, c) {
        c(node, currBlock, 'Identifier');
    },

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

},{"./aux":1,"./domains/types":6,"acorn/dist/walk":15}],12:[function(require,module,exports){
'use strict';

var walk = require('acorn/dist/walk');
var myWalker = require('./util/myWalker');

function findIdentifierAt(ast, pos) {
    "use strict";

    function Found(node, state) {
        this.node = node;
        this.state = state;
    }

    // find the node
    var walker = myWalker.wrapWalker(myWalker.varWalker, function (node, vb) {
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
    "use strict";
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
    "use strict";
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
    }, myWalker.varWalker);

    walk.recursive(vb1.originNode, vb1, walker);
    return refs;
}

exports.findIdentifierAt = findIdentifierAt;
exports.findVarRefsAt = findVarRefsAt;

},{"./util/myWalker":10,"acorn/dist/walk":15}],13:[function(require,module,exports){
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
    raw: this.input.slice(this.start, this.end).replace(/\r\n?/g, '\n'),
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
    f += "}";

    // Otherwise, simply generate a flat `switch` statement.
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
var version = "2.2.0";

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
}

// The `getLineInfo` function is mostly useful when the
// `locations` option is off (for performance reasons) and you
// want to find the line/column position for a given character
// offset. `input` should be the code string that the offset refers
// into.

;

exports.SourceLocation = SourceLocation;

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
  if (!this.eat(_tokentype.types.eq)) return left;
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
}

// Start an AST node, attaching a start offset.

;

exports.Node = Node;
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
      type: block ? 'Block' : 'Line',
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
    if (this.pos === 0 && this.options.allowHashBang && this.input.slice(0, 2) === '#!') this.skipLineComment(2);
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

_tokentype.types.incDec.updateContext = function () {
  // tokExprAllowed stays unchanged
};

_tokentype.types._function.updateContext = function () {
  if (this.curContext() !== types.b_stat) this.context.push(types.f_expr);
  this.exprAllowed = false;
};

_tokentype.types.backQuote.updateContext = function () {
  if (this.curContext() === types.q_tmpl) this.context.pop();else this.context.push(types.q_tmpl);
  this.exprAllowed = false;
};

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
}

// ## Tokenizer

;

exports.Token = Token;
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
    if (mods.indexOf('u') >= 0 && !regexpUnicodeSupport) {
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
    code = this.readHexChar(this.input.indexOf('}', this.pos) - this.pos);
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

},{}],14:[function(require,module,exports){
(function (global){
(function(f){if(typeof exports==="object"&&typeof module!=="undefined"){module.exports=f()}else if(typeof define==="function"&&define.amd){define([],f)}else{var g;if(typeof window!=="undefined"){g=window}else if(typeof global!=="undefined"){g=global}else if(typeof self!=="undefined"){g=self}else{g=this}(g.acorn || (g.acorn = {})).loose = f()}})(function(){var define,module,exports;return (function e(t,n,r){function s(o,u){if(!n[o]){if(!t[o]){var a=typeof require=="function"&&require;if(!u&&a)return a(o,!0);if(i)return i(o,!0);var f=new Error("Cannot find module '"+o+"'");throw f.code="MODULE_NOT_FOUND",f}var l=n[o]={exports:{}};t[o][0].call(l.exports,function(e){var n=t[o][1][e];return s(n?n:e)},l,l.exports,e,t,n,r)}return n[o].exports}var i=typeof require=="function"&&require;for(var o=0;o<r.length;o++)s(r[o]);return s})({1:[function(_dereq_,module,exports){
(function (global){
"use strict";(function(f){if(typeof exports === "object" && typeof module !== "undefined"){module.exports = f();}else if(typeof define === "function" && define.amd){define([],f);}else {var g;if(typeof window !== "undefined"){g = window;}else if(typeof global !== "undefined"){g = global;}else if(typeof self !== "undefined"){g = self;}else {g = this;}g.acorn = f();}})(function(){var define,module,exports;return (function e(t,n,r){function s(o,u){if(!n[o]){if(!t[o]){var a=typeof _dereq_ == "function" && _dereq_;if(!u && a)return a(o,!0);if(i)return i(o,!0);var f=new Error("Cannot find module '" + o + "'");throw (f.code = "MODULE_NOT_FOUND",f);}var l=n[o] = {exports:{}};t[o][0].call(l.exports,function(e){var n=t[o][1][e];return s(n?n:e);},l,l.exports,e,t,n,r);}return n[o].exports;}var i=typeof _dereq_ == "function" && _dereq_;for(var o=0;o < r.length;o++) s(r[o]);return s;})({1:[function(_dereq_,module,exports){ // A recursive descent parser operates by defining functions for all
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
"use strict";var _tokentype=_dereq_("./tokentype");var _state=_dereq_("./state");var _identifier=_dereq_("./identifier");var _util=_dereq_("./util");var pp=_state.Parser.prototype; // Check if property name clashes with already added.
// Object/class getters and setters are not allowed to clash —
// either with each other or with an init property — and in
// strict mode, init properties are also not allowed to be repeated.
pp.checkPropClash = function(prop,propHash){if(this.options.ecmaVersion >= 6 && (prop.computed || prop.method || prop.shorthand))return;var key=prop.key,name=undefined;switch(key.type){case "Identifier":name = key.name;break;case "Literal":name = String(key.value);break;default:return;}var kind=prop.kind;if(this.options.ecmaVersion >= 6){if(name === "__proto__" && kind === "init"){if(propHash.proto)this.raise(key.start,"Redefinition of __proto__ property");propHash.proto = true;}return;}var other=undefined;if(_util.has(propHash,name)){other = propHash[name];var isGetSet=kind !== "init";if((this.strict || isGetSet) && other[kind] || !(isGetSet ^ other.init))this.raise(key.start,"Redefinition of property");}else {other = propHash[name] = {init:false,get:false,set:false};}other[kind] = true;}; // ### Expression parsing
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
pp.parseExpression = function(noIn,refShorthandDefaultPos){var startPos=this.start,startLoc=this.startLoc;var expr=this.parseMaybeAssign(noIn,refShorthandDefaultPos);if(this.type === _tokentype.types.comma){var node=this.startNodeAt(startPos,startLoc);node.expressions = [expr];while(this.eat(_tokentype.types.comma)) node.expressions.push(this.parseMaybeAssign(noIn,refShorthandDefaultPos));return this.finishNode(node,"SequenceExpression");}return expr;}; // Parse an assignment expression. This includes applications of
// operators like `+=`.
pp.parseMaybeAssign = function(noIn,refShorthandDefaultPos,afterLeftParse){if(this.type == _tokentype.types._yield && this.inGenerator)return this.parseYield();var failOnShorthandAssign=undefined;if(!refShorthandDefaultPos){refShorthandDefaultPos = {start:0};failOnShorthandAssign = true;}else {failOnShorthandAssign = false;}var startPos=this.start,startLoc=this.startLoc;if(this.type == _tokentype.types.parenL || this.type == _tokentype.types.name)this.potentialArrowAt = this.start;var left=this.parseMaybeConditional(noIn,refShorthandDefaultPos);if(afterLeftParse)left = afterLeftParse.call(this,left,startPos,startLoc);if(this.type.isAssign){var node=this.startNodeAt(startPos,startLoc);node.operator = this.value;node.left = this.type === _tokentype.types.eq?this.toAssignable(left):left;refShorthandDefaultPos.start = 0; // reset because shorthand default was used correctly
this.checkLVal(left);this.next();node.right = this.parseMaybeAssign(noIn);return this.finishNode(node,"AssignmentExpression");}else if(failOnShorthandAssign && refShorthandDefaultPos.start){this.unexpected(refShorthandDefaultPos.start);}return left;}; // Parse a ternary conditional (`?:`) operator.
pp.parseMaybeConditional = function(noIn,refShorthandDefaultPos){var startPos=this.start,startLoc=this.startLoc;var expr=this.parseExprOps(noIn,refShorthandDefaultPos);if(refShorthandDefaultPos && refShorthandDefaultPos.start)return expr;if(this.eat(_tokentype.types.question)){var node=this.startNodeAt(startPos,startLoc);node.test = expr;node.consequent = this.parseMaybeAssign();this.expect(_tokentype.types.colon);node.alternate = this.parseMaybeAssign(noIn);return this.finishNode(node,"ConditionalExpression");}return expr;}; // Start the precedence parser.
pp.parseExprOps = function(noIn,refShorthandDefaultPos){var startPos=this.start,startLoc=this.startLoc;var expr=this.parseMaybeUnary(refShorthandDefaultPos);if(refShorthandDefaultPos && refShorthandDefaultPos.start)return expr;return this.parseExprOp(expr,startPos,startLoc,-1,noIn);}; // Parse binary operators with the operator precedence parsing
// algorithm. `left` is the left-hand side of the operator.
// `minPrec` provides context that allows the function to stop and
// defer further parser to one of its callers when it encounters an
// operator that has a lower precedence than the set it is parsing.
pp.parseExprOp = function(left,leftStartPos,leftStartLoc,minPrec,noIn){var prec=this.type.binop;if(prec != null && (!noIn || this.type !== _tokentype.types._in)){if(prec > minPrec){var node=this.startNodeAt(leftStartPos,leftStartLoc);node.left = left;node.operator = this.value;var op=this.type;this.next();var startPos=this.start,startLoc=this.startLoc;node.right = this.parseExprOp(this.parseMaybeUnary(),startPos,startLoc,prec,noIn);this.finishNode(node,op === _tokentype.types.logicalOR || op === _tokentype.types.logicalAND?"LogicalExpression":"BinaryExpression");return this.parseExprOp(node,leftStartPos,leftStartLoc,minPrec,noIn);}}return left;}; // Parse unary operators, both prefix and postfix.
pp.parseMaybeUnary = function(refShorthandDefaultPos){if(this.type.prefix){var node=this.startNode(),update=this.type === _tokentype.types.incDec;node.operator = this.value;node.prefix = true;this.next();node.argument = this.parseMaybeUnary();if(refShorthandDefaultPos && refShorthandDefaultPos.start)this.unexpected(refShorthandDefaultPos.start);if(update)this.checkLVal(node.argument);else if(this.strict && node.operator === "delete" && node.argument.type === "Identifier")this.raise(node.start,"Deleting local variable in strict mode");return this.finishNode(node,update?"UpdateExpression":"UnaryExpression");}var startPos=this.start,startLoc=this.startLoc;var expr=this.parseExprSubscripts(refShorthandDefaultPos);if(refShorthandDefaultPos && refShorthandDefaultPos.start)return expr;while(this.type.postfix && !this.canInsertSemicolon()) {var node=this.startNodeAt(startPos,startLoc);node.operator = this.value;node.prefix = false;node.argument = expr;this.checkLVal(expr);this.next();expr = this.finishNode(node,"UpdateExpression");}return expr;}; // Parse call, dot, and `[]`-subscript expressions.
pp.parseExprSubscripts = function(refShorthandDefaultPos){var startPos=this.start,startLoc=this.startLoc;var expr=this.parseExprAtom(refShorthandDefaultPos);if(refShorthandDefaultPos && refShorthandDefaultPos.start)return expr;return this.parseSubscripts(expr,startPos,startLoc);};pp.parseSubscripts = function(base,startPos,startLoc,noCalls){for(;;) {if(this.eat(_tokentype.types.dot)){var node=this.startNodeAt(startPos,startLoc);node.object = base;node.property = this.parseIdent(true);node.computed = false;base = this.finishNode(node,"MemberExpression");}else if(this.eat(_tokentype.types.bracketL)){var node=this.startNodeAt(startPos,startLoc);node.object = base;node.property = this.parseExpression();node.computed = true;this.expect(_tokentype.types.bracketR);base = this.finishNode(node,"MemberExpression");}else if(!noCalls && this.eat(_tokentype.types.parenL)){var node=this.startNodeAt(startPos,startLoc);node.callee = base;node.arguments = this.parseExprList(_tokentype.types.parenR,false);base = this.finishNode(node,"CallExpression");}else if(this.type === _tokentype.types.backQuote){var node=this.startNodeAt(startPos,startLoc);node.tag = base;node.quasi = this.parseTemplate();base = this.finishNode(node,"TaggedTemplateExpression");}else {return base;}}}; // Parse an atomic expression — either a single token that is an
// expression, an expression started by a keyword like `function` or
// `new`, or an expression wrapped in punctuation like `()`, `[]`,
// or `{}`.
pp.parseExprAtom = function(refShorthandDefaultPos){var node=undefined,canBeArrow=this.potentialArrowAt == this.start;switch(this.type){case _tokentype.types._super:if(!this.inFunction)this.raise(this.start,"'super' outside of function or class");case _tokentype.types._this:var type=this.type === _tokentype.types._this?"ThisExpression":"Super";node = this.startNode();this.next();return this.finishNode(node,type);case _tokentype.types._yield:if(this.inGenerator)this.unexpected();case _tokentype.types.name:var startPos=this.start,startLoc=this.startLoc;var id=this.parseIdent(this.type !== _tokentype.types.name);if(canBeArrow && !this.canInsertSemicolon() && this.eat(_tokentype.types.arrow))return this.parseArrowExpression(this.startNodeAt(startPos,startLoc),[id]);return id;case _tokentype.types.regexp:var value=this.value;node = this.parseLiteral(value.value);node.regex = {pattern:value.pattern,flags:value.flags};return node;case _tokentype.types.num:case _tokentype.types.string:return this.parseLiteral(this.value);case _tokentype.types._null:case _tokentype.types._true:case _tokentype.types._false:node = this.startNode();node.value = this.type === _tokentype.types._null?null:this.type === _tokentype.types._true;node.raw = this.type.keyword;this.next();return this.finishNode(node,"Literal");case _tokentype.types.parenL:return this.parseParenAndDistinguishExpression(canBeArrow);case _tokentype.types.bracketL:node = this.startNode();this.next(); // check whether this is array comprehension or regular array
if(this.options.ecmaVersion >= 7 && this.type === _tokentype.types._for){return this.parseComprehension(node,false);}node.elements = this.parseExprList(_tokentype.types.bracketR,true,true,refShorthandDefaultPos);return this.finishNode(node,"ArrayExpression");case _tokentype.types.braceL:return this.parseObj(false,refShorthandDefaultPos);case _tokentype.types._function:node = this.startNode();this.next();return this.parseFunction(node,false);case _tokentype.types._class:return this.parseClass(this.startNode(),false);case _tokentype.types._new:return this.parseNew();case _tokentype.types.backQuote:return this.parseTemplate();default:this.unexpected();}};pp.parseLiteral = function(value){var node=this.startNode();node.value = value;node.raw = this.input.slice(this.start,this.end);this.next();return this.finishNode(node,"Literal");};pp.parseParenExpression = function(){this.expect(_tokentype.types.parenL);var val=this.parseExpression();this.expect(_tokentype.types.parenR);return val;};pp.parseParenAndDistinguishExpression = function(canBeArrow){var startPos=this.start,startLoc=this.startLoc,val=undefined;if(this.options.ecmaVersion >= 6){this.next();if(this.options.ecmaVersion >= 7 && this.type === _tokentype.types._for){return this.parseComprehension(this.startNodeAt(startPos,startLoc),true);}var innerStartPos=this.start,innerStartLoc=this.startLoc;var exprList=[],first=true;var refShorthandDefaultPos={start:0},spreadStart=undefined,innerParenStart=undefined;while(this.type !== _tokentype.types.parenR) {first?first = false:this.expect(_tokentype.types.comma);if(this.type === _tokentype.types.ellipsis){spreadStart = this.start;exprList.push(this.parseParenItem(this.parseRest()));break;}else {if(this.type === _tokentype.types.parenL && !innerParenStart){innerParenStart = this.start;}exprList.push(this.parseMaybeAssign(false,refShorthandDefaultPos,this.parseParenItem));}}var innerEndPos=this.start,innerEndLoc=this.startLoc;this.expect(_tokentype.types.parenR);if(canBeArrow && !this.canInsertSemicolon() && this.eat(_tokentype.types.arrow)){if(innerParenStart)this.unexpected(innerParenStart);return this.parseParenArrowList(startPos,startLoc,exprList);}if(!exprList.length)this.unexpected(this.lastTokStart);if(spreadStart)this.unexpected(spreadStart);if(refShorthandDefaultPos.start)this.unexpected(refShorthandDefaultPos.start);if(exprList.length > 1){val = this.startNodeAt(innerStartPos,innerStartLoc);val.expressions = exprList;this.finishNodeAt(val,"SequenceExpression",innerEndPos,innerEndLoc);}else {val = exprList[0];}}else {val = this.parseParenExpression();}if(this.options.preserveParens){var par=this.startNodeAt(startPos,startLoc);par.expression = val;return this.finishNode(par,"ParenthesizedExpression");}else {return val;}};pp.parseParenItem = function(item){return item;};pp.parseParenArrowList = function(startPos,startLoc,exprList){return this.parseArrowExpression(this.startNodeAt(startPos,startLoc),exprList);}; // New's precedence is slightly tricky. It must allow its argument
// to be a `[]` or dot subscript expression, but not a call — at
// least, not without wrapping it in parentheses. Thus, it uses the
var empty=[];pp.parseNew = function(){var node=this.startNode();var meta=this.parseIdent(true);if(this.options.ecmaVersion >= 6 && this.eat(_tokentype.types.dot)){node.meta = meta;node.property = this.parseIdent(true);if(node.property.name !== "target")this.raise(node.property.start,"The only valid meta property for new is new.target");return this.finishNode(node,"MetaProperty");}var startPos=this.start,startLoc=this.startLoc;node.callee = this.parseSubscripts(this.parseExprAtom(),startPos,startLoc,true);if(this.eat(_tokentype.types.parenL))node.arguments = this.parseExprList(_tokentype.types.parenR,false);else node.arguments = empty;return this.finishNode(node,"NewExpression");}; // Parse template expression.
pp.parseTemplateElement = function(){var elem=this.startNode();elem.value = {raw:this.input.slice(this.start,this.end).replace(/\r\n?/g,'\n'),cooked:this.value};this.next();elem.tail = this.type === _tokentype.types.backQuote;return this.finishNode(elem,"TemplateElement");};pp.parseTemplate = function(){var node=this.startNode();this.next();node.expressions = [];var curElt=this.parseTemplateElement();node.quasis = [curElt];while(!curElt.tail) {this.expect(_tokentype.types.dollarBraceL);node.expressions.push(this.parseExpression());this.expect(_tokentype.types.braceR);node.quasis.push(curElt = this.parseTemplateElement());}this.next();return this.finishNode(node,"TemplateLiteral");}; // Parse an object literal or binding pattern.
pp.parseObj = function(isPattern,refShorthandDefaultPos){var node=this.startNode(),first=true,propHash={};node.properties = [];this.next();while(!this.eat(_tokentype.types.braceR)) {if(!first){this.expect(_tokentype.types.comma);if(this.afterTrailingComma(_tokentype.types.braceR))break;}else first = false;var prop=this.startNode(),isGenerator=undefined,startPos=undefined,startLoc=undefined;if(this.options.ecmaVersion >= 6){prop.method = false;prop.shorthand = false;if(isPattern || refShorthandDefaultPos){startPos = this.start;startLoc = this.startLoc;}if(!isPattern)isGenerator = this.eat(_tokentype.types.star);}this.parsePropertyName(prop);this.parsePropertyValue(prop,isPattern,isGenerator,startPos,startLoc,refShorthandDefaultPos);this.checkPropClash(prop,propHash);node.properties.push(this.finishNode(prop,"Property"));}return this.finishNode(node,isPattern?"ObjectPattern":"ObjectExpression");};pp.parsePropertyValue = function(prop,isPattern,isGenerator,startPos,startLoc,refShorthandDefaultPos){if(this.eat(_tokentype.types.colon)){prop.value = isPattern?this.parseMaybeDefault(this.start,this.startLoc):this.parseMaybeAssign(false,refShorthandDefaultPos);prop.kind = "init";}else if(this.options.ecmaVersion >= 6 && this.type === _tokentype.types.parenL){if(isPattern)this.unexpected();prop.kind = "init";prop.method = true;prop.value = this.parseMethod(isGenerator);}else if(this.options.ecmaVersion >= 5 && !prop.computed && prop.key.type === "Identifier" && (prop.key.name === "get" || prop.key.name === "set") && (this.type != _tokentype.types.comma && this.type != _tokentype.types.braceR)){if(isGenerator || isPattern)this.unexpected();prop.kind = prop.key.name;this.parsePropertyName(prop);prop.value = this.parseMethod(false);var paramCount=prop.kind === "get"?0:1;if(prop.value.params.length !== paramCount){var start=prop.value.start;if(prop.kind === "get")this.raise(start,"getter should have no params");else this.raise(start,"setter should have exactly one param");}}else if(this.options.ecmaVersion >= 6 && !prop.computed && prop.key.type === "Identifier"){prop.kind = "init";if(isPattern){if(this.isKeyword(prop.key.name) || this.strict && (_identifier.reservedWords.strictBind(prop.key.name) || _identifier.reservedWords.strict(prop.key.name)) || !this.options.allowReserved && this.isReservedWord(prop.key.name))this.raise(prop.key.start,"Binding " + prop.key.name);prop.value = this.parseMaybeDefault(startPos,startLoc,prop.key);}else if(this.type === _tokentype.types.eq && refShorthandDefaultPos){if(!refShorthandDefaultPos.start)refShorthandDefaultPos.start = this.start;prop.value = this.parseMaybeDefault(startPos,startLoc,prop.key);}else {prop.value = prop.key;}prop.shorthand = true;}else this.unexpected();};pp.parsePropertyName = function(prop){if(this.options.ecmaVersion >= 6){if(this.eat(_tokentype.types.bracketL)){prop.computed = true;prop.key = this.parseMaybeAssign();this.expect(_tokentype.types.bracketR);return prop.key;}else {prop.computed = false;}}return prop.key = this.type === _tokentype.types.num || this.type === _tokentype.types.string?this.parseExprAtom():this.parseIdent(true);}; // Initialize empty function node.
pp.initFunction = function(node){node.id = null;if(this.options.ecmaVersion >= 6){node.generator = false;node.expression = false;}}; // Parse object or class method.
pp.parseMethod = function(isGenerator){var node=this.startNode();this.initFunction(node);this.expect(_tokentype.types.parenL);node.params = this.parseBindingList(_tokentype.types.parenR,false,false);var allowExpressionBody=undefined;if(this.options.ecmaVersion >= 6){node.generator = isGenerator;}this.parseFunctionBody(node,false);return this.finishNode(node,"FunctionExpression");}; // Parse arrow function expression with given parameters.
pp.parseArrowExpression = function(node,params){this.initFunction(node);node.params = this.toAssignableList(params,true);this.parseFunctionBody(node,true);return this.finishNode(node,"ArrowFunctionExpression");}; // Parse function body and check parameters.
pp.parseFunctionBody = function(node,allowExpression){var isExpression=allowExpression && this.type !== _tokentype.types.braceL;if(isExpression){node.body = this.parseMaybeAssign();node.expression = true;}else { // Start a new scope with regard to labels and the `inFunction`
// flag (restore them to their old value afterwards).
var oldInFunc=this.inFunction,oldInGen=this.inGenerator,oldLabels=this.labels;this.inFunction = true;this.inGenerator = node.generator;this.labels = [];node.body = this.parseBlock(true);node.expression = false;this.inFunction = oldInFunc;this.inGenerator = oldInGen;this.labels = oldLabels;} // If this is a strict mode function, verify that argument names
// are not repeated, and it does not try to bind the words `eval`
// or `arguments`.
if(this.strict || !isExpression && node.body.body.length && this.isUseStrict(node.body.body[0])){var nameHash={},oldStrict=this.strict;this.strict = true;if(node.id)this.checkLVal(node.id,true);for(var i=0;i < node.params.length;i++) {this.checkLVal(node.params[i],true,nameHash);}this.strict = oldStrict;}}; // Parses a comma-separated list of expressions, and returns them as
// an array. `close` is the token type that ends the list, and
// `allowEmpty` can be turned on to allow subsequent commas with
// nothing in between them to be parsed as `null` (which is needed
// for array literals).
pp.parseExprList = function(close,allowTrailingComma,allowEmpty,refShorthandDefaultPos){var elts=[],first=true;while(!this.eat(close)) {if(!first){this.expect(_tokentype.types.comma);if(allowTrailingComma && this.afterTrailingComma(close))break;}else first = false;var elt=undefined;if(allowEmpty && this.type === _tokentype.types.comma)elt = null;else if(this.type === _tokentype.types.ellipsis)elt = this.parseSpread(refShorthandDefaultPos);else elt = this.parseMaybeAssign(false,refShorthandDefaultPos);elts.push(elt);}return elts;}; // Parse the next token as an identifier. If `liberal` is true (used
// when parsing properties), it will also convert keywords into
// identifiers.
pp.parseIdent = function(liberal){var node=this.startNode();if(liberal && this.options.allowReserved == "never")liberal = false;if(this.type === _tokentype.types.name){if(!liberal && (!this.options.allowReserved && this.isReservedWord(this.value) || this.strict && _identifier.reservedWords.strict(this.value) && (this.options.ecmaVersion >= 6 || this.input.slice(this.start,this.end).indexOf("\\") == -1)))this.raise(this.start,"The keyword '" + this.value + "' is reserved");node.name = this.value;}else if(liberal && this.type.keyword){node.name = this.type.keyword;}else {this.unexpected();}this.next();return this.finishNode(node,"Identifier");}; // Parses yield expression inside generator.
pp.parseYield = function(){var node=this.startNode();this.next();if(this.type == _tokentype.types.semi || this.canInsertSemicolon() || this.type != _tokentype.types.star && !this.type.startsExpr){node.delegate = false;node.argument = null;}else {node.delegate = this.eat(_tokentype.types.star);node.argument = this.parseMaybeAssign();}return this.finishNode(node,"YieldExpression");}; // Parses array and generator comprehensions.
pp.parseComprehension = function(node,isGenerator){node.blocks = [];while(this.type === _tokentype.types._for) {var block=this.startNode();this.next();this.expect(_tokentype.types.parenL);block.left = this.parseBindingAtom();this.checkLVal(block.left,true);this.expectContextual("of");block.right = this.parseExpression();this.expect(_tokentype.types.parenR);node.blocks.push(this.finishNode(block,"ComprehensionBlock"));}node.filter = this.eat(_tokentype.types._if)?this.parseParenExpression():null;node.body = this.parseExpression();this.expect(isGenerator?_tokentype.types.parenR:_tokentype.types.bracketR);node.generator = isGenerator;return this.finishNode(node,"ComprehensionExpression");};},{"./identifier":2,"./state":10,"./tokentype":14,"./util":15}],2:[function(_dereq_,module,exports){ // This is a trick taken from Esprima. It turns out that, on
// non-Chrome browsers, to check whether a string is in a set, a
// predicate containing a big ugly `switch` statement is faster than
// a regular expression, and on Chrome the two are about on par.
// This function uses `eval` (non-lexical) to produce such a
// predicate from a space-separated string of words.
//
// It starts by sorting the words by length.
"use strict";exports.__esModule = true;exports.isIdentifierStart = isIdentifierStart;exports.isIdentifierChar = isIdentifierChar;function makePredicate(words){words = words.split(" ");var f="",cats=[];out: for(var i=0;i < words.length;++i) {for(var j=0;j < cats.length;++j) {if(cats[j][0].length == words[i].length){cats[j].push(words[i]);continue out;}}cats.push([words[i]]);}function compareTo(arr){if(arr.length == 1)return f += "return str === " + JSON.stringify(arr[0]) + ";";f += "switch(str){";for(var i=0;i < arr.length;++i) {f += "case " + JSON.stringify(arr[i]) + ":";}f += "return true}return false;";} // When there are more than three length categories, an outer
// switch first dispatches on the lengths, to save on comparisons.
if(cats.length > 3){cats.sort(function(a,b){return b.length - a.length;});f += "switch(str.length){";for(var i=0;i < cats.length;++i) {var cat=cats[i];f += "case " + cat[0].length + ":";compareTo(cat);}f += "}"; // Otherwise, simply generate a flat `switch` statement.
}else {compareTo(words);}return new Function("str",f);} // Reserved word lists for various dialects of the language
var reservedWords={3:makePredicate("abstract boolean byte char class double enum export extends final float goto implements import int interface long native package private protected public short static super synchronized throws transient volatile"),5:makePredicate("class enum extends super const export import"),6:makePredicate("enum await"),strict:makePredicate("implements interface let package private protected public static yield"),strictBind:makePredicate("eval arguments")};exports.reservedWords = reservedWords; // And the keywords
var ecma5AndLessKeywords="break case catch continue debugger default do else finally for function if return switch throw try var while with null true false instanceof typeof void delete new in this";var keywords={5:makePredicate(ecma5AndLessKeywords),6:makePredicate(ecma5AndLessKeywords + " let const class extends export import yield super")};exports.keywords = keywords; // ## Character categories
// Big ugly regular expressions that match characters in the
// whitespace, identifier, and identifier-start categories. These
// are only applied when a character is found to actually have a
// code point above 128.
// Generated by `tools/generate-identifier-regex.js`.
var nonASCIIidentifierStartChars="ªµºÀ-ÖØ-öø-ˁˆ-ˑˠ-ˤˬˮͰ-ʹͶͷͺ-ͽͿΆΈ-ΊΌΎ-ΡΣ-ϵϷ-ҁҊ-ԯԱ-Ֆՙա-ևא-תװ-ײؠ-يٮٯٱ-ۓەۥۦۮۯۺ-ۼۿܐܒ-ܯݍ-ޥޱߊ-ߪߴߵߺࠀ-ࠕࠚࠤࠨࡀ-ࡘࢠ-ࢲऄ-हऽॐक़-ॡॱ-ঀঅ-ঌএঐও-নপ-রলশ-হঽৎড়ঢ়য়-ৡৰৱਅ-ਊਏਐਓ-ਨਪ-ਰਲਲ਼ਵਸ਼ਸਹਖ਼-ੜਫ਼ੲ-ੴઅ-ઍએ-ઑઓ-નપ-રલળવ-હઽૐૠૡଅ-ଌଏଐଓ-ନପ-ରଲଳଵ-ହଽଡ଼ଢ଼ୟ-ୡୱஃஅ-ஊஎ-ஐஒ-கஙசஜஞடணதந-பம-ஹௐఅ-ఌఎ-ఐఒ-నప-హఽౘౙౠౡಅ-ಌಎ-ಐಒ-ನಪ-ಳವ-ಹಽೞೠೡೱೲഅ-ഌഎ-ഐഒ-ഺഽൎൠൡൺ-ൿඅ-ඖක-නඳ-රලව-ෆก-ะาำเ-ๆກຂຄງຈຊຍດ-ທນ-ຟມ-ຣລວສຫອ-ະາຳຽເ-ໄໆໜ-ໟༀཀ-ཇཉ-ཬྈ-ྌက-ဪဿၐ-ၕၚ-ၝၡၥၦၮ-ၰၵ-ႁႎႠ-ჅჇჍა-ჺჼ-ቈቊ-ቍቐ-ቖቘቚ-ቝበ-ኈኊ-ኍነ-ኰኲ-ኵኸ-ኾዀዂ-ዅወ-ዖዘ-ጐጒ-ጕጘ-ፚᎀ-ᎏᎠ-Ᏼᐁ-ᙬᙯ-ᙿᚁ-ᚚᚠ-ᛪᛮ-ᛸᜀ-ᜌᜎ-ᜑᜠ-ᜱᝀ-ᝑᝠ-ᝬᝮ-ᝰក-ឳៗៜᠠ-ᡷᢀ-ᢨᢪᢰ-ᣵᤀ-ᤞᥐ-ᥭᥰ-ᥴᦀ-ᦫᧁ-ᧇᨀ-ᨖᨠ-ᩔᪧᬅ-ᬳᭅ-ᭋᮃ-ᮠᮮᮯᮺ-ᯥᰀ-ᰣᱍ-ᱏᱚ-ᱽᳩ-ᳬᳮ-ᳱᳵᳶᴀ-ᶿḀ-ἕἘ-Ἕἠ-ὅὈ-Ὅὐ-ὗὙὛὝὟ-ώᾀ-ᾴᾶ-ᾼιῂ-ῄῆ-ῌῐ-ΐῖ-Ίῠ-Ῥῲ-ῴῶ-ῼⁱⁿₐ-ₜℂℇℊ-ℓℕ℘-ℝℤΩℨK-ℹℼ-ℿⅅ-ⅉⅎⅠ-ↈⰀ-Ⱞⰰ-ⱞⱠ-ⳤⳫ-ⳮⳲⳳⴀ-ⴥⴧⴭⴰ-ⵧⵯⶀ-ⶖⶠ-ⶦⶨ-ⶮⶰ-ⶶⶸ-ⶾⷀ-ⷆⷈ-ⷎⷐ-ⷖⷘ-ⷞ々-〇〡-〩〱-〵〸-〼ぁ-ゖ゛-ゟァ-ヺー-ヿㄅ-ㄭㄱ-ㆎㆠ-ㆺㇰ-ㇿ㐀-䶵一-鿌ꀀ-ꒌꓐ-ꓽꔀ-ꘌꘐ-ꘟꘪꘫꙀ-ꙮꙿ-ꚝꚠ-ꛯꜗ-ꜟꜢ-ꞈꞋ-ꞎꞐ-ꞭꞰꞱꟷ-ꠁꠃ-ꠅꠇ-ꠊꠌ-ꠢꡀ-ꡳꢂ-ꢳꣲ-ꣷꣻꤊ-ꤥꤰ-ꥆꥠ-ꥼꦄ-ꦲꧏꧠ-ꧤꧦ-ꧯꧺ-ꧾꨀ-ꨨꩀ-ꩂꩄ-ꩋꩠ-ꩶꩺꩾ-ꪯꪱꪵꪶꪹ-ꪽꫀꫂꫛ-ꫝꫠ-ꫪꫲ-ꫴꬁ-ꬆꬉ-ꬎꬑ-ꬖꬠ-ꬦꬨ-ꬮꬰ-ꭚꭜ-ꭟꭤꭥꯀ-ꯢ가-힣ힰ-ퟆퟋ-ퟻ豈-舘並-龎ﬀ-ﬆﬓ-ﬗיִײַ-ﬨשׁ-זּטּ-לּמּנּסּףּפּצּ-ﮱﯓ-ﴽﵐ-ﶏﶒ-ﷇﷰ-ﷻﹰ-ﹴﹶ-ﻼＡ-Ｚａ-ｚｦ-ﾾￂ-ￇￊ-ￏￒ-ￗￚ-ￜ";var nonASCIIidentifierChars="‌‍·̀-ͯ·҃-֑҇-ׇֽֿׁׂׅׄؐ-ًؚ-٩ٰۖ-ۜ۟-۪ۤۧۨ-ۭ۰-۹ܑܰ-݊ަ-ް߀-߉߫-߳ࠖ-࠙ࠛ-ࠣࠥ-ࠧࠩ-࡙࠭-࡛ࣤ-ःऺ-़ा-ॏ॑-ॗॢॣ०-९ঁ-ঃ়া-ৄেৈো-্ৗৢৣ০-৯ਁ-ਃ਼ਾ-ੂੇੈੋ-੍ੑ੦-ੱੵઁ-ઃ઼ા-ૅે-ૉો-્ૢૣ૦-૯ଁ-ଃ଼ା-ୄେୈୋ-୍ୖୗୢୣ୦-୯ஂா-ூெ-ைொ-்ௗ௦-௯ఀ-ఃా-ౄె-ైొ-్ౕౖౢౣ౦-౯ಁ-ಃ಼ಾ-ೄೆ-ೈೊ-್ೕೖೢೣ೦-೯ഁ-ഃാ-ൄെ-ൈൊ-്ൗൢൣ൦-൯ංඃ්ා-ුූෘ-ෟ෦-෯ෲෳัิ-ฺ็-๎๐-๙ັິ-ູົຼ່-ໍ໐-໙༘༙༠-༩༹༵༷༾༿ཱ-྄྆྇ྍ-ྗྙ-ྼ࿆ါ-ှ၀-၉ၖ-ၙၞ-ၠၢ-ၤၧ-ၭၱ-ၴႂ-ႍႏ-ႝ፝-፟፩-፱ᜒ-᜔ᜲ-᜴ᝒᝓᝲᝳ឴-៓៝០-៩᠋-᠍᠐-᠙ᢩᤠ-ᤫᤰ-᤻᥆-᥏ᦰ-ᧀᧈᧉ᧐-᧚ᨗ-ᨛᩕ-ᩞ᩠-᩿᩼-᪉᪐-᪙᪰-᪽ᬀ-ᬄ᬴-᭄᭐-᭙᭫-᭳ᮀ-ᮂᮡ-ᮭ᮰-᮹᯦-᯳ᰤ-᰷᱀-᱉᱐-᱙᳐-᳔᳒-᳨᳭ᳲ-᳴᳸᳹᷀-᷵᷼-᷿‿⁀⁔⃐-⃥⃜⃡-⃰⳯-⵿⳱ⷠ-〪ⷿ-゙゚〯꘠-꘩꙯ꙴ-꙽ꚟ꛰꛱ꠂ꠆ꠋꠣ-ꠧꢀꢁꢴ-꣄꣐-꣙꣠-꣱꤀-꤉ꤦ-꤭ꥇ-꥓ꦀ-ꦃ꦳-꧀꧐-꧙ꧥ꧰-꧹ꨩ-ꨶꩃꩌꩍ꩐-꩙ꩻ-ꩽꪰꪲ-ꪴꪷꪸꪾ꪿꫁ꫫ-ꫯꫵ꫶ꯣ-ꯪ꯬꯭꯰-꯹ﬞ︀-️︠-︭︳︴﹍-﹏０-９＿";var nonASCIIidentifierStart=new RegExp("[" + nonASCIIidentifierStartChars + "]");var nonASCIIidentifier=new RegExp("[" + nonASCIIidentifierStartChars + nonASCIIidentifierChars + "]");nonASCIIidentifierStartChars = nonASCIIidentifierChars = null; // These are a run-length and offset encoded representation of the
// >0xffff code points that are a valid part of identifiers. The
// offset starts at 0x10000, and each pair of numbers represents an
// offset to the next range, and then a size of the range. They were
// generated by tools/generate-identifier-regex.js
var astralIdentifierStartCodes=[0,11,2,25,2,18,2,1,2,14,3,13,35,122,70,52,268,28,4,48,48,31,17,26,6,37,11,29,3,35,5,7,2,4,43,157,99,39,9,51,157,310,10,21,11,7,153,5,3,0,2,43,2,1,4,0,3,22,11,22,10,30,98,21,11,25,71,55,7,1,65,0,16,3,2,2,2,26,45,28,4,28,36,7,2,27,28,53,11,21,11,18,14,17,111,72,955,52,76,44,33,24,27,35,42,34,4,0,13,47,15,3,22,0,38,17,2,24,133,46,39,7,3,1,3,21,2,6,2,1,2,4,4,0,32,4,287,47,21,1,2,0,185,46,82,47,21,0,60,42,502,63,32,0,449,56,1288,920,104,110,2962,1070,13266,568,8,30,114,29,19,47,17,3,32,20,6,18,881,68,12,0,67,12,16481,1,3071,106,6,12,4,8,8,9,5991,84,2,70,2,1,3,0,3,1,3,3,2,11,2,0,2,6,2,64,2,3,3,7,2,6,2,27,2,3,2,4,2,0,4,6,2,339,3,24,2,24,2,30,2,24,2,30,2,24,2,30,2,24,2,30,2,24,2,7,4149,196,1340,3,2,26,2,1,2,0,3,0,2,9,2,3,2,0,2,0,7,0,5,0,2,0,2,0,2,2,2,1,2,0,3,0,2,0,2,0,2,0,2,0,2,1,2,0,3,3,2,6,2,3,2,3,2,0,2,9,2,16,6,2,2,4,2,16,4421,42710,42,4148,12,221,16355,541];var astralIdentifierCodes=[509,0,227,0,150,4,294,9,1368,2,2,1,6,3,41,2,5,0,166,1,1306,2,54,14,32,9,16,3,46,10,54,9,7,2,37,13,2,9,52,0,13,2,49,13,16,9,83,11,168,11,6,9,8,2,57,0,2,6,3,1,3,2,10,0,11,1,3,6,4,4,316,19,13,9,214,6,3,8,112,16,16,9,82,12,9,9,535,9,20855,9,135,4,60,6,26,9,1016,45,17,3,19723,1,5319,4,4,5,9,7,3,6,31,3,149,2,1418,49,4305,6,792618,239]; // This has a complexity linear to the value of the code. The
// assumption is that looking up astral identifier characters is
// rare.
function isInAstralSet(code,set){var pos=0x10000;for(var i=0;i < set.length;i += 2) {pos += set[i];if(pos > code)return false;pos += set[i + 1];if(pos >= code)return true;}} // Test whether a given character code starts an identifier.
function isIdentifierStart(code,astral){if(code < 65)return code === 36;if(code < 91)return true;if(code < 97)return code === 95;if(code < 123)return true;if(code <= 0xffff)return code >= 0xaa && nonASCIIidentifierStart.test(String.fromCharCode(code));if(astral === false)return false;return isInAstralSet(code,astralIdentifierStartCodes);} // Test whether a given character is part of an identifier.
function isIdentifierChar(code,astral){if(code < 48)return code === 36;if(code < 58)return true;if(code < 65)return false;if(code < 91)return true;if(code < 97)return code === 95;if(code < 123)return true;if(code <= 0xffff)return code >= 0xaa && nonASCIIidentifier.test(String.fromCharCode(code));if(astral === false)return false;return isInAstralSet(code,astralIdentifierStartCodes) || isInAstralSet(code,astralIdentifierCodes);}},{}],3:[function(_dereq_,module,exports){ // Acorn is a tiny, fast JavaScript parser written in JavaScript.
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
"use strict";exports.__esModule = true;exports.parse = parse;exports.parseExpressionAt = parseExpressionAt;exports.tokenizer = tokenizer;var _state=_dereq_("./state");var _options=_dereq_("./options");_dereq_("./parseutil");_dereq_("./statement");_dereq_("./lval");_dereq_("./expression");_dereq_("./location");exports.Parser = _state.Parser;exports.plugins = _state.plugins;exports.defaultOptions = _options.defaultOptions;var _locutil=_dereq_("./locutil");exports.Position = _locutil.Position;exports.SourceLocation = _locutil.SourceLocation;exports.getLineInfo = _locutil.getLineInfo;var _node=_dereq_("./node");exports.Node = _node.Node;var _tokentype=_dereq_("./tokentype");exports.TokenType = _tokentype.TokenType;exports.tokTypes = _tokentype.types;var _tokencontext=_dereq_("./tokencontext");exports.TokContext = _tokencontext.TokContext;exports.tokContexts = _tokencontext.types;var _identifier=_dereq_("./identifier");exports.isIdentifierChar = _identifier.isIdentifierChar;exports.isIdentifierStart = _identifier.isIdentifierStart;var _tokenize=_dereq_("./tokenize");exports.Token = _tokenize.Token;var _whitespace=_dereq_("./whitespace");exports.isNewLine = _whitespace.isNewLine;exports.lineBreak = _whitespace.lineBreak;exports.lineBreakG = _whitespace.lineBreakG;var version="2.2.0";exports.version = version; // The main exported interface (under `self.acorn` when in the
// browser) is a `parse` function that takes a code string and
// returns an abstract syntax tree as specified by [Mozilla parser
// API][api].
//
// [api]: https://developer.mozilla.org/en-US/docs/SpiderMonkey/Parser_API
function parse(input,options){return new _state.Parser(options,input).parse();} // This function tries to parse a single expression at a given
// offset in a string. Useful for parsing mixed-language formats
// that embed JavaScript expressions.
function parseExpressionAt(input,pos,options){var p=new _state.Parser(options,input,pos);p.nextToken();return p.parseExpression();} // Acorn is organized as a tokenizer and a recursive-descent parser.
// The `tokenize` export provides an interface to the tokenizer.
function tokenizer(input,options){return new _state.Parser(options,input);}},{"./expression":1,"./identifier":2,"./location":4,"./locutil":5,"./lval":6,"./node":7,"./options":8,"./parseutil":9,"./state":10,"./statement":11,"./tokencontext":12,"./tokenize":13,"./tokentype":14,"./whitespace":16}],4:[function(_dereq_,module,exports){"use strict";var _state=_dereq_("./state");var _locutil=_dereq_("./locutil");var pp=_state.Parser.prototype; // This function is used to raise exceptions on parse errors. It
// takes an offset integer (into the current `input`) to indicate
// the location of the error, attaches the position to the end
// of the error message, and then raises a `SyntaxError` with that
// message.
pp.raise = function(pos,message){var loc=_locutil.getLineInfo(this.input,pos);message += " (" + loc.line + ":" + loc.column + ")";var err=new SyntaxError(message);err.pos = pos;err.loc = loc;err.raisedAt = this.pos;throw err;};pp.curPosition = function(){if(this.options.locations){return new _locutil.Position(this.curLine,this.pos - this.lineStart);}};},{"./locutil":5,"./state":10}],5:[function(_dereq_,module,exports){"use strict";exports.__esModule = true;exports.getLineInfo = getLineInfo;function _classCallCheck(instance,Constructor){if(!(instance instanceof Constructor)){throw new TypeError("Cannot call a class as a function");}}var _whitespace=_dereq_("./whitespace"); // These are used when `options.locations` is on, for the
// `startLoc` and `endLoc` properties.
var Position=(function(){function Position(line,col){_classCallCheck(this,Position);this.line = line;this.column = col;}Position.prototype.offset = function offset(n){return new Position(this.line,this.column + n);};return Position;})();exports.Position = Position;var SourceLocation=function SourceLocation(p,start,end){_classCallCheck(this,SourceLocation);this.start = start;this.end = end;if(p.sourceFile !== null)this.source = p.sourceFile;} // The `getLineInfo` function is mostly useful when the
// `locations` option is off (for performance reasons) and you
// want to find the line/column position for a given character
// offset. `input` should be the code string that the offset refers
// into.
;exports.SourceLocation = SourceLocation;function getLineInfo(input,offset){for(var line=1,cur=0;;) {_whitespace.lineBreakG.lastIndex = cur;var match=_whitespace.lineBreakG.exec(input);if(match && match.index < offset){++line;cur = match.index + match[0].length;}else {return new Position(line,offset - cur);}}}},{"./whitespace":16}],6:[function(_dereq_,module,exports){"use strict";var _tokentype=_dereq_("./tokentype");var _state=_dereq_("./state");var _identifier=_dereq_("./identifier");var _util=_dereq_("./util");var pp=_state.Parser.prototype; // Convert existing expression atom to assignable pattern
// if possible.
pp.toAssignable = function(node,isBinding){if(this.options.ecmaVersion >= 6 && node){switch(node.type){case "Identifier":case "ObjectPattern":case "ArrayPattern":case "AssignmentPattern":break;case "ObjectExpression":node.type = "ObjectPattern";for(var i=0;i < node.properties.length;i++) {var prop=node.properties[i];if(prop.kind !== "init")this.raise(prop.key.start,"Object pattern can't contain getter or setter");this.toAssignable(prop.value,isBinding);}break;case "ArrayExpression":node.type = "ArrayPattern";this.toAssignableList(node.elements,isBinding);break;case "AssignmentExpression":if(node.operator === "="){node.type = "AssignmentPattern";delete node.operator;}else {this.raise(node.left.end,"Only '=' operator can be used for specifying default value.");}break;case "ParenthesizedExpression":node.expression = this.toAssignable(node.expression,isBinding);break;case "MemberExpression":if(!isBinding)break;default:this.raise(node.start,"Assigning to rvalue");}}return node;}; // Convert list of expression atoms to binding list.
pp.toAssignableList = function(exprList,isBinding){var end=exprList.length;if(end){var last=exprList[end - 1];if(last && last.type == "RestElement"){--end;}else if(last && last.type == "SpreadElement"){last.type = "RestElement";var arg=last.argument;this.toAssignable(arg,isBinding);if(arg.type !== "Identifier" && arg.type !== "MemberExpression" && arg.type !== "ArrayPattern")this.unexpected(arg.start);--end;}}for(var i=0;i < end;i++) {var elt=exprList[i];if(elt)this.toAssignable(elt,isBinding);}return exprList;}; // Parses spread element.
pp.parseSpread = function(refShorthandDefaultPos){var node=this.startNode();this.next();node.argument = this.parseMaybeAssign(refShorthandDefaultPos);return this.finishNode(node,"SpreadElement");};pp.parseRest = function(){var node=this.startNode();this.next();node.argument = this.type === _tokentype.types.name || this.type === _tokentype.types.bracketL?this.parseBindingAtom():this.unexpected();return this.finishNode(node,"RestElement");}; // Parses lvalue (assignable) atom.
pp.parseBindingAtom = function(){if(this.options.ecmaVersion < 6)return this.parseIdent();switch(this.type){case _tokentype.types.name:return this.parseIdent();case _tokentype.types.bracketL:var node=this.startNode();this.next();node.elements = this.parseBindingList(_tokentype.types.bracketR,true,true);return this.finishNode(node,"ArrayPattern");case _tokentype.types.braceL:return this.parseObj(true);default:this.unexpected();}};pp.parseBindingList = function(close,allowEmpty,allowTrailingComma){var elts=[],first=true;while(!this.eat(close)) {if(first)first = false;else this.expect(_tokentype.types.comma);if(allowEmpty && this.type === _tokentype.types.comma){elts.push(null);}else if(allowTrailingComma && this.afterTrailingComma(close)){break;}else if(this.type === _tokentype.types.ellipsis){var rest=this.parseRest();this.parseBindingListItem(rest);elts.push(rest);this.expect(close);break;}else {var elem=this.parseMaybeDefault(this.start,this.startLoc);this.parseBindingListItem(elem);elts.push(elem);}}return elts;};pp.parseBindingListItem = function(param){return param;}; // Parses assignment pattern around given atom if possible.
pp.parseMaybeDefault = function(startPos,startLoc,left){left = left || this.parseBindingAtom();if(!this.eat(_tokentype.types.eq))return left;var node=this.startNodeAt(startPos,startLoc);node.left = left;node.right = this.parseMaybeAssign();return this.finishNode(node,"AssignmentPattern");}; // Verify that a node is an lval — something that can be assigned
// to.
pp.checkLVal = function(expr,isBinding,checkClashes){switch(expr.type){case "Identifier":if(this.strict && (_identifier.reservedWords.strictBind(expr.name) || _identifier.reservedWords.strict(expr.name)))this.raise(expr.start,(isBinding?"Binding ":"Assigning to ") + expr.name + " in strict mode");if(checkClashes){if(_util.has(checkClashes,expr.name))this.raise(expr.start,"Argument name clash in strict mode");checkClashes[expr.name] = true;}break;case "MemberExpression":if(isBinding)this.raise(expr.start,(isBinding?"Binding":"Assigning to") + " member expression");break;case "ObjectPattern":for(var i=0;i < expr.properties.length;i++) {this.checkLVal(expr.properties[i].value,isBinding,checkClashes);}break;case "ArrayPattern":for(var i=0;i < expr.elements.length;i++) {var elem=expr.elements[i];if(elem)this.checkLVal(elem,isBinding,checkClashes);}break;case "AssignmentPattern":this.checkLVal(expr.left,isBinding,checkClashes);break;case "RestElement":this.checkLVal(expr.argument,isBinding,checkClashes);break;case "ParenthesizedExpression":this.checkLVal(expr.expression,isBinding,checkClashes);break;default:this.raise(expr.start,(isBinding?"Binding":"Assigning to") + " rvalue");}};},{"./identifier":2,"./state":10,"./tokentype":14,"./util":15}],7:[function(_dereq_,module,exports){"use strict";exports.__esModule = true;function _classCallCheck(instance,Constructor){if(!(instance instanceof Constructor)){throw new TypeError("Cannot call a class as a function");}}var _state=_dereq_("./state");var _locutil=_dereq_("./locutil");var Node=function Node(parser,pos,loc){_classCallCheck(this,Node);this.type = "";this.start = pos;this.end = 0;if(parser.options.locations)this.loc = new _locutil.SourceLocation(parser,loc);if(parser.options.directSourceFile)this.sourceFile = parser.options.directSourceFile;if(parser.options.ranges)this.range = [pos,0];} // Start an AST node, attaching a start offset.
;exports.Node = Node;var pp=_state.Parser.prototype;pp.startNode = function(){return new Node(this,this.start,this.startLoc);};pp.startNodeAt = function(pos,loc){return new Node(this,pos,loc);}; // Finish an AST node, adding `type` and `end` properties.
function finishNodeAt(node,type,pos,loc){node.type = type;node.end = pos;if(this.options.locations)node.loc.end = loc;if(this.options.ranges)node.range[1] = pos;return node;}pp.finishNode = function(node,type){return finishNodeAt.call(this,node,type,this.lastTokEnd,this.lastTokEndLoc);}; // Finish node at given position
pp.finishNodeAt = function(node,type,pos,loc){return finishNodeAt.call(this,node,type,pos,loc);};},{"./locutil":5,"./state":10}],8:[function(_dereq_,module,exports){"use strict";exports.__esModule = true;exports.getOptions = getOptions;var _util=_dereq_("./util");var _locutil=_dereq_("./locutil"); // A second optional argument can be given to further configure
// the parser process. These options are recognized:
var defaultOptions={ // `ecmaVersion` indicates the ECMAScript version to parse. Must
// be either 3, or 5, or 6. This influences support for strict
// mode, the set of reserved words, support for getters and
// setters and other features.
ecmaVersion:5, // Source type ("script" or "module") for different semantics
sourceType:"script", // `onInsertedSemicolon` can be a callback that will be called
// when a semicolon is automatically inserted. It will be passed
// th position of the comma as an offset, and if `locations` is
// enabled, it is given the location as a `{line, column}` object
// as second argument.
onInsertedSemicolon:null, // `onTrailingComma` is similar to `onInsertedSemicolon`, but for
// trailing commas.
onTrailingComma:null, // By default, reserved words are not enforced. Disable
// `allowReserved` to enforce them. When this option has the
// value "never", reserved words and keywords can also not be
// used as property names.
allowReserved:true, // When enabled, a return at the top level is not considered an
// error.
allowReturnOutsideFunction:false, // When enabled, import/export statements are not constrained to
// appearing at the top of the program.
allowImportExportEverywhere:false, // When enabled, hashbang directive in the beginning of file
// is allowed and treated as a line comment.
allowHashBang:false, // When `locations` is on, `loc` properties holding objects with
// `start` and `end` properties in `{line, column}` form (with
// line being 1-based and column 0-based) will be attached to the
// nodes.
locations:false, // A function can be passed as `onToken` option, which will
// cause Acorn to call that function with object in the same
// format as tokenize() returns. Note that you are not
// allowed to call the parser from the callback—that will
// corrupt its internal state.
onToken:null, // A function can be passed as `onComment` option, which will
// cause Acorn to call that function with `(block, text, start,
// end)` parameters whenever a comment is skipped. `block` is a
// boolean indicating whether this is a block (`/* */`) comment,
// `text` is the content of the comment, and `start` and `end` are
// character offsets that denote the start and end of the comment.
// When the `locations` option is on, two more parameters are
// passed, the full `{line, column}` locations of the start and
// end of the comments. Note that you are not allowed to call the
// parser from the callback—that will corrupt its internal state.
onComment:null, // Nodes have their start and end characters offsets recorded in
// `start` and `end` properties (directly on the node, rather than
// the `loc` object, which holds line/column data. To also add a
// [semi-standardized][range] `range` property holding a `[start,
// end]` array with the same numbers, set the `ranges` option to
// `true`.
//
// [range]: https://bugzilla.mozilla.org/show_bug.cgi?id=745678
ranges:false, // It is possible to parse multiple files into a single AST by
// passing the tree produced by parsing the first file as
// `program` option in subsequent parses. This will add the
// toplevel forms of the parsed file to the `Program` (top) node
// of an existing parse tree.
program:null, // When `locations` is on, you can pass this to record the source
// file in every node's `loc` object.
sourceFile:null, // This value, if given, is stored in every node, whether
// `locations` is on or off.
directSourceFile:null, // When enabled, parenthesized expressions are represented by
// (non-standard) ParenthesizedExpression nodes
preserveParens:false,plugins:{}};exports.defaultOptions = defaultOptions; // Interpret and default an options object
function getOptions(opts){var options={};for(var opt in defaultOptions) {options[opt] = opts && _util.has(opts,opt)?opts[opt]:defaultOptions[opt];}if(_util.isArray(options.onToken)){(function(){var tokens=options.onToken;options.onToken = function(token){return tokens.push(token);};})();}if(_util.isArray(options.onComment))options.onComment = pushComment(options,options.onComment);return options;}function pushComment(options,array){return function(block,text,start,end,startLoc,endLoc){var comment={type:block?'Block':'Line',value:text,start:start,end:end};if(options.locations)comment.loc = new _locutil.SourceLocation(this,startLoc,endLoc);if(options.ranges)comment.range = [start,end];array.push(comment);};}},{"./locutil":5,"./util":15}],9:[function(_dereq_,module,exports){"use strict";var _tokentype=_dereq_("./tokentype");var _state=_dereq_("./state");var _whitespace=_dereq_("./whitespace");var pp=_state.Parser.prototype; // ## Parser utilities
// Test whether a statement node is the string literal `"use strict"`.
pp.isUseStrict = function(stmt){return this.options.ecmaVersion >= 5 && stmt.type === "ExpressionStatement" && stmt.expression.type === "Literal" && stmt.expression.raw.slice(1,-1) === "use strict";}; // Predicate that tests whether the next token is of the given
// type, and if yes, consumes it as a side effect.
pp.eat = function(type){if(this.type === type){this.next();return true;}else {return false;}}; // Tests whether parsed token is a contextual keyword.
pp.isContextual = function(name){return this.type === _tokentype.types.name && this.value === name;}; // Consumes contextual keyword if possible.
pp.eatContextual = function(name){return this.value === name && this.eat(_tokentype.types.name);}; // Asserts that following token is given contextual keyword.
pp.expectContextual = function(name){if(!this.eatContextual(name))this.unexpected();}; // Test whether a semicolon can be inserted at the current position.
pp.canInsertSemicolon = function(){return this.type === _tokentype.types.eof || this.type === _tokentype.types.braceR || _whitespace.lineBreak.test(this.input.slice(this.lastTokEnd,this.start));};pp.insertSemicolon = function(){if(this.canInsertSemicolon()){if(this.options.onInsertedSemicolon)this.options.onInsertedSemicolon(this.lastTokEnd,this.lastTokEndLoc);return true;}}; // Consume a semicolon, or, failing that, see if we are allowed to
// pretend that there is a semicolon at this position.
pp.semicolon = function(){if(!this.eat(_tokentype.types.semi) && !this.insertSemicolon())this.unexpected();};pp.afterTrailingComma = function(tokType){if(this.type == tokType){if(this.options.onTrailingComma)this.options.onTrailingComma(this.lastTokStart,this.lastTokStartLoc);this.next();return true;}}; // Expect a token of a given type. If found, consume it, otherwise,
// raise an unexpected token error.
pp.expect = function(type){this.eat(type) || this.unexpected();}; // Raise an unexpected token error.
pp.unexpected = function(pos){this.raise(pos != null?pos:this.start,"Unexpected token");};},{"./state":10,"./tokentype":14,"./whitespace":16}],10:[function(_dereq_,module,exports){"use strict";exports.__esModule = true;function _classCallCheck(instance,Constructor){if(!(instance instanceof Constructor)){throw new TypeError("Cannot call a class as a function");}}var _identifier=_dereq_("./identifier");var _tokentype=_dereq_("./tokentype");var _whitespace=_dereq_("./whitespace");var _options=_dereq_("./options"); // Registered plugins
var plugins={};exports.plugins = plugins;var Parser=(function(){function Parser(options,input,startPos){_classCallCheck(this,Parser);this.options = _options.getOptions(options);this.sourceFile = this.options.sourceFile;this.isKeyword = _identifier.keywords[this.options.ecmaVersion >= 6?6:5];this.isReservedWord = _identifier.reservedWords[this.options.ecmaVersion];this.input = String(input); // Used to signal to callers of `readWord1` whether the word
// contained any escape sequences. This is needed because words with
// escape sequences must not be interpreted as keywords.
this.containsEsc = false; // Load plugins
this.loadPlugins(this.options.plugins); // Set up token state
// The current position of the tokenizer in the input.
if(startPos){this.pos = startPos;this.lineStart = Math.max(0,this.input.lastIndexOf("\n",startPos));this.curLine = this.input.slice(0,this.lineStart).split(_whitespace.lineBreak).length;}else {this.pos = this.lineStart = 0;this.curLine = 1;} // Properties of the current token:
// Its type
this.type = _tokentype.types.eof; // For tokens that include more information than their type, the value
this.value = null; // Its start and end offset
this.start = this.end = this.pos; // And, if locations are used, the {line, column} object
// corresponding to those offsets
this.startLoc = this.endLoc = this.curPosition(); // Position information for the previous token
this.lastTokEndLoc = this.lastTokStartLoc = null;this.lastTokStart = this.lastTokEnd = this.pos; // The context stack is used to superficially track syntactic
// context to predict whether a regular expression is allowed in a
// given position.
this.context = this.initialContext();this.exprAllowed = true; // Figure out if it's a module code.
this.strict = this.inModule = this.options.sourceType === "module"; // Used to signify the start of a potential arrow function
this.potentialArrowAt = -1; // Flags to track whether we are in a function, a generator.
this.inFunction = this.inGenerator = false; // Labels in scope.
this.labels = []; // If enabled, skip leading hashbang line.
if(this.pos === 0 && this.options.allowHashBang && this.input.slice(0,2) === '#!')this.skipLineComment(2);}Parser.prototype.extend = function extend(name,f){this[name] = f(this[name]);};Parser.prototype.loadPlugins = function loadPlugins(pluginConfigs){for(var _name in pluginConfigs) {var plugin=plugins[_name];if(!plugin)throw new Error("Plugin '" + _name + "' not found");plugin(this,pluginConfigs[_name]);}};Parser.prototype.parse = function parse(){var node=this.options.program || this.startNode();this.nextToken();return this.parseTopLevel(node);};return Parser;})();exports.Parser = Parser;},{"./identifier":2,"./options":8,"./tokentype":14,"./whitespace":16}],11:[function(_dereq_,module,exports){"use strict";var _tokentype=_dereq_("./tokentype");var _state=_dereq_("./state");var _whitespace=_dereq_("./whitespace");var pp=_state.Parser.prototype; // ### Statement parsing
// Parse a program. Initializes the parser, reads any number of
// statements, and wraps them in a Program node.  Optionally takes a
// `program` argument.  If present, the statements will be appended
// to its body instead of creating a new node.
pp.parseTopLevel = function(node){var first=true;if(!node.body)node.body = [];while(this.type !== _tokentype.types.eof) {var stmt=this.parseStatement(true,true);node.body.push(stmt);if(first){if(this.isUseStrict(stmt))this.setStrict(true);first = false;}}this.next();if(this.options.ecmaVersion >= 6){node.sourceType = this.options.sourceType;}return this.finishNode(node,"Program");};var loopLabel={kind:"loop"},switchLabel={kind:"switch"}; // Parse a single statement.
//
// If expecting a statement and finding a slash operator, parse a
// regular expression literal. This is to handle cases like
// `if (foo) /blah/.exec(foo)`, where looking at the previous token
// does not help.
pp.parseStatement = function(declaration,topLevel){var starttype=this.type,node=this.startNode(); // Most types of statements are recognized by the keyword they
// start with. Many are trivial to parse, some require a bit of
// complexity.
switch(starttype){case _tokentype.types._break:case _tokentype.types._continue:return this.parseBreakContinueStatement(node,starttype.keyword);case _tokentype.types._debugger:return this.parseDebuggerStatement(node);case _tokentype.types._do:return this.parseDoStatement(node);case _tokentype.types._for:return this.parseForStatement(node);case _tokentype.types._function:if(!declaration && this.options.ecmaVersion >= 6)this.unexpected();return this.parseFunctionStatement(node);case _tokentype.types._class:if(!declaration)this.unexpected();return this.parseClass(node,true);case _tokentype.types._if:return this.parseIfStatement(node);case _tokentype.types._return:return this.parseReturnStatement(node);case _tokentype.types._switch:return this.parseSwitchStatement(node);case _tokentype.types._throw:return this.parseThrowStatement(node);case _tokentype.types._try:return this.parseTryStatement(node);case _tokentype.types._let:case _tokentype.types._const:if(!declaration)this.unexpected(); // NOTE: falls through to _var
case _tokentype.types._var:return this.parseVarStatement(node,starttype);case _tokentype.types._while:return this.parseWhileStatement(node);case _tokentype.types._with:return this.parseWithStatement(node);case _tokentype.types.braceL:return this.parseBlock();case _tokentype.types.semi:return this.parseEmptyStatement(node);case _tokentype.types._export:case _tokentype.types._import:if(!this.options.allowImportExportEverywhere){if(!topLevel)this.raise(this.start,"'import' and 'export' may only appear at the top level");if(!this.inModule)this.raise(this.start,"'import' and 'export' may appear only with 'sourceType: module'");}return starttype === _tokentype.types._import?this.parseImport(node):this.parseExport(node); // If the statement does not start with a statement keyword or a
// brace, it's an ExpressionStatement or LabeledStatement. We
// simply start parsing an expression, and afterwards, if the
// next token is a colon and the expression was a simple
// Identifier node, we switch to interpreting it as a label.
default:var maybeName=this.value,expr=this.parseExpression();if(starttype === _tokentype.types.name && expr.type === "Identifier" && this.eat(_tokentype.types.colon))return this.parseLabeledStatement(node,maybeName,expr);else return this.parseExpressionStatement(node,expr);}};pp.parseBreakContinueStatement = function(node,keyword){var isBreak=keyword == "break";this.next();if(this.eat(_tokentype.types.semi) || this.insertSemicolon())node.label = null;else if(this.type !== _tokentype.types.name)this.unexpected();else {node.label = this.parseIdent();this.semicolon();} // Verify that there is an actual destination to break or
// continue to.
for(var i=0;i < this.labels.length;++i) {var lab=this.labels[i];if(node.label == null || lab.name === node.label.name){if(lab.kind != null && (isBreak || lab.kind === "loop"))break;if(node.label && isBreak)break;}}if(i === this.labels.length)this.raise(node.start,"Unsyntactic " + keyword);return this.finishNode(node,isBreak?"BreakStatement":"ContinueStatement");};pp.parseDebuggerStatement = function(node){this.next();this.semicolon();return this.finishNode(node,"DebuggerStatement");};pp.parseDoStatement = function(node){this.next();this.labels.push(loopLabel);node.body = this.parseStatement(false);this.labels.pop();this.expect(_tokentype.types._while);node.test = this.parseParenExpression();if(this.options.ecmaVersion >= 6)this.eat(_tokentype.types.semi);else this.semicolon();return this.finishNode(node,"DoWhileStatement");}; // Disambiguating between a `for` and a `for`/`in` or `for`/`of`
// loop is non-trivial. Basically, we have to parse the init `var`
// statement or expression, disallowing the `in` operator (see
// the second parameter to `parseExpression`), and then check
// whether the next token is `in` or `of`. When there is no init
// part (semicolon immediately after the opening parenthesis), it
// is a regular `for` loop.
pp.parseForStatement = function(node){this.next();this.labels.push(loopLabel);this.expect(_tokentype.types.parenL);if(this.type === _tokentype.types.semi)return this.parseFor(node,null);if(this.type === _tokentype.types._var || this.type === _tokentype.types._let || this.type === _tokentype.types._const){var _init=this.startNode(),varKind=this.type;this.next();this.parseVar(_init,true,varKind);this.finishNode(_init,"VariableDeclaration");if((this.type === _tokentype.types._in || this.options.ecmaVersion >= 6 && this.isContextual("of")) && _init.declarations.length === 1 && !(varKind !== _tokentype.types._var && _init.declarations[0].init))return this.parseForIn(node,_init);return this.parseFor(node,_init);}var refShorthandDefaultPos={start:0};var init=this.parseExpression(true,refShorthandDefaultPos);if(this.type === _tokentype.types._in || this.options.ecmaVersion >= 6 && this.isContextual("of")){this.toAssignable(init);this.checkLVal(init);return this.parseForIn(node,init);}else if(refShorthandDefaultPos.start){this.unexpected(refShorthandDefaultPos.start);}return this.parseFor(node,init);};pp.parseFunctionStatement = function(node){this.next();return this.parseFunction(node,true);};pp.parseIfStatement = function(node){this.next();node.test = this.parseParenExpression();node.consequent = this.parseStatement(false);node.alternate = this.eat(_tokentype.types._else)?this.parseStatement(false):null;return this.finishNode(node,"IfStatement");};pp.parseReturnStatement = function(node){if(!this.inFunction && !this.options.allowReturnOutsideFunction)this.raise(this.start,"'return' outside of function");this.next(); // In `return` (and `break`/`continue`), the keywords with
// optional arguments, we eagerly look for a semicolon or the
// possibility to insert one.
if(this.eat(_tokentype.types.semi) || this.insertSemicolon())node.argument = null;else {node.argument = this.parseExpression();this.semicolon();}return this.finishNode(node,"ReturnStatement");};pp.parseSwitchStatement = function(node){this.next();node.discriminant = this.parseParenExpression();node.cases = [];this.expect(_tokentype.types.braceL);this.labels.push(switchLabel); // Statements under must be grouped (by label) in SwitchCase
// nodes. `cur` is used to keep the node that we are currently
// adding statements to.
for(var cur,sawDefault=false;this.type != _tokentype.types.braceR;) {if(this.type === _tokentype.types._case || this.type === _tokentype.types._default){var isCase=this.type === _tokentype.types._case;if(cur)this.finishNode(cur,"SwitchCase");node.cases.push(cur = this.startNode());cur.consequent = [];this.next();if(isCase){cur.test = this.parseExpression();}else {if(sawDefault)this.raise(this.lastTokStart,"Multiple default clauses");sawDefault = true;cur.test = null;}this.expect(_tokentype.types.colon);}else {if(!cur)this.unexpected();cur.consequent.push(this.parseStatement(true));}}if(cur)this.finishNode(cur,"SwitchCase");this.next(); // Closing brace
this.labels.pop();return this.finishNode(node,"SwitchStatement");};pp.parseThrowStatement = function(node){this.next();if(_whitespace.lineBreak.test(this.input.slice(this.lastTokEnd,this.start)))this.raise(this.lastTokEnd,"Illegal newline after throw");node.argument = this.parseExpression();this.semicolon();return this.finishNode(node,"ThrowStatement");}; // Reused empty array added for node fields that are always empty.
var empty=[];pp.parseTryStatement = function(node){this.next();node.block = this.parseBlock();node.handler = null;if(this.type === _tokentype.types._catch){var clause=this.startNode();this.next();this.expect(_tokentype.types.parenL);clause.param = this.parseBindingAtom();this.checkLVal(clause.param,true);this.expect(_tokentype.types.parenR);clause.guard = null;clause.body = this.parseBlock();node.handler = this.finishNode(clause,"CatchClause");}node.guardedHandlers = empty;node.finalizer = this.eat(_tokentype.types._finally)?this.parseBlock():null;if(!node.handler && !node.finalizer)this.raise(node.start,"Missing catch or finally clause");return this.finishNode(node,"TryStatement");};pp.parseVarStatement = function(node,kind){this.next();this.parseVar(node,false,kind);this.semicolon();return this.finishNode(node,"VariableDeclaration");};pp.parseWhileStatement = function(node){this.next();node.test = this.parseParenExpression();this.labels.push(loopLabel);node.body = this.parseStatement(false);this.labels.pop();return this.finishNode(node,"WhileStatement");};pp.parseWithStatement = function(node){if(this.strict)this.raise(this.start,"'with' in strict mode");this.next();node.object = this.parseParenExpression();node.body = this.parseStatement(false);return this.finishNode(node,"WithStatement");};pp.parseEmptyStatement = function(node){this.next();return this.finishNode(node,"EmptyStatement");};pp.parseLabeledStatement = function(node,maybeName,expr){for(var i=0;i < this.labels.length;++i) {if(this.labels[i].name === maybeName)this.raise(expr.start,"Label '" + maybeName + "' is already declared");}var kind=this.type.isLoop?"loop":this.type === _tokentype.types._switch?"switch":null;for(var i=this.labels.length - 1;i >= 0;i--) {var label=this.labels[i];if(label.statementStart == node.start){label.statementStart = this.start;label.kind = kind;}else break;}this.labels.push({name:maybeName,kind:kind,statementStart:this.start});node.body = this.parseStatement(true);this.labels.pop();node.label = expr;return this.finishNode(node,"LabeledStatement");};pp.parseExpressionStatement = function(node,expr){node.expression = expr;this.semicolon();return this.finishNode(node,"ExpressionStatement");}; // Parse a semicolon-enclosed block of statements, handling `"use
// strict"` declarations when `allowStrict` is true (used for
// function bodies).
pp.parseBlock = function(allowStrict){var node=this.startNode(),first=true,oldStrict=undefined;node.body = [];this.expect(_tokentype.types.braceL);while(!this.eat(_tokentype.types.braceR)) {var stmt=this.parseStatement(true);node.body.push(stmt);if(first && allowStrict && this.isUseStrict(stmt)){oldStrict = this.strict;this.setStrict(this.strict = true);}first = false;}if(oldStrict === false)this.setStrict(false);return this.finishNode(node,"BlockStatement");}; // Parse a regular `for` loop. The disambiguation code in
// `parseStatement` will already have parsed the init statement or
// expression.
pp.parseFor = function(node,init){node.init = init;this.expect(_tokentype.types.semi);node.test = this.type === _tokentype.types.semi?null:this.parseExpression();this.expect(_tokentype.types.semi);node.update = this.type === _tokentype.types.parenR?null:this.parseExpression();this.expect(_tokentype.types.parenR);node.body = this.parseStatement(false);this.labels.pop();return this.finishNode(node,"ForStatement");}; // Parse a `for`/`in` and `for`/`of` loop, which are almost
// same from parser's perspective.
pp.parseForIn = function(node,init){var type=this.type === _tokentype.types._in?"ForInStatement":"ForOfStatement";this.next();node.left = init;node.right = this.parseExpression();this.expect(_tokentype.types.parenR);node.body = this.parseStatement(false);this.labels.pop();return this.finishNode(node,type);}; // Parse a list of variable declarations.
pp.parseVar = function(node,isFor,kind){node.declarations = [];node.kind = kind.keyword;for(;;) {var decl=this.startNode();this.parseVarId(decl);if(this.eat(_tokentype.types.eq)){decl.init = this.parseMaybeAssign(isFor);}else if(kind === _tokentype.types._const && !(this.type === _tokentype.types._in || this.options.ecmaVersion >= 6 && this.isContextual("of"))){this.unexpected();}else if(decl.id.type != "Identifier" && !(isFor && (this.type === _tokentype.types._in || this.isContextual("of")))){this.raise(this.lastTokEnd,"Complex binding patterns require an initialization value");}else {decl.init = null;}node.declarations.push(this.finishNode(decl,"VariableDeclarator"));if(!this.eat(_tokentype.types.comma))break;}return node;};pp.parseVarId = function(decl){decl.id = this.parseBindingAtom();this.checkLVal(decl.id,true);}; // Parse a function declaration or literal (depending on the
// `isStatement` parameter).
pp.parseFunction = function(node,isStatement,allowExpressionBody){this.initFunction(node);if(this.options.ecmaVersion >= 6)node.generator = this.eat(_tokentype.types.star);if(isStatement || this.type === _tokentype.types.name)node.id = this.parseIdent();this.parseFunctionParams(node);this.parseFunctionBody(node,allowExpressionBody);return this.finishNode(node,isStatement?"FunctionDeclaration":"FunctionExpression");};pp.parseFunctionParams = function(node){this.expect(_tokentype.types.parenL);node.params = this.parseBindingList(_tokentype.types.parenR,false,false);}; // Parse a class declaration or literal (depending on the
// `isStatement` parameter).
pp.parseClass = function(node,isStatement){this.next();this.parseClassId(node,isStatement);this.parseClassSuper(node);var classBody=this.startNode();var hadConstructor=false;classBody.body = [];this.expect(_tokentype.types.braceL);while(!this.eat(_tokentype.types.braceR)) {if(this.eat(_tokentype.types.semi))continue;var method=this.startNode();var isGenerator=this.eat(_tokentype.types.star);var isMaybeStatic=this.type === _tokentype.types.name && this.value === "static";this.parsePropertyName(method);method["static"] = isMaybeStatic && this.type !== _tokentype.types.parenL;if(method["static"]){if(isGenerator)this.unexpected();isGenerator = this.eat(_tokentype.types.star);this.parsePropertyName(method);}method.kind = "method";var isGetSet=false;if(!method.computed){var key=method.key;if(!isGenerator && key.type === "Identifier" && this.type !== _tokentype.types.parenL && (key.name === "get" || key.name === "set")){isGetSet = true;method.kind = key.name;key = this.parsePropertyName(method);}if(!method["static"] && (key.type === "Identifier" && key.name === "constructor" || key.type === "Literal" && key.value === "constructor")){if(hadConstructor)this.raise(key.start,"Duplicate constructor in the same class");if(isGetSet)this.raise(key.start,"Constructor can't have get/set modifier");if(isGenerator)this.raise(key.start,"Constructor can't be a generator");method.kind = "constructor";hadConstructor = true;}}this.parseClassMethod(classBody,method,isGenerator);if(isGetSet){var paramCount=method.kind === "get"?0:1;if(method.value.params.length !== paramCount){var start=method.value.start;if(method.kind === "get")this.raise(start,"getter should have no params");else this.raise(start,"setter should have exactly one param");}}}node.body = this.finishNode(classBody,"ClassBody");return this.finishNode(node,isStatement?"ClassDeclaration":"ClassExpression");};pp.parseClassMethod = function(classBody,method,isGenerator){method.value = this.parseMethod(isGenerator);classBody.body.push(this.finishNode(method,"MethodDefinition"));};pp.parseClassId = function(node,isStatement){node.id = this.type === _tokentype.types.name?this.parseIdent():isStatement?this.unexpected():null;};pp.parseClassSuper = function(node){node.superClass = this.eat(_tokentype.types._extends)?this.parseExprSubscripts():null;}; // Parses module export declaration.
pp.parseExport = function(node){this.next(); // export * from '...'
if(this.eat(_tokentype.types.star)){this.expectContextual("from");node.source = this.type === _tokentype.types.string?this.parseExprAtom():this.unexpected();this.semicolon();return this.finishNode(node,"ExportAllDeclaration");}if(this.eat(_tokentype.types._default)){ // export default ...
var expr=this.parseMaybeAssign();var needsSemi=true;if(expr.type == "FunctionExpression" || expr.type == "ClassExpression"){needsSemi = false;if(expr.id){expr.type = expr.type == "FunctionExpression"?"FunctionDeclaration":"ClassDeclaration";}}node.declaration = expr;if(needsSemi)this.semicolon();return this.finishNode(node,"ExportDefaultDeclaration");} // export var|const|let|function|class ...
if(this.shouldParseExportStatement()){node.declaration = this.parseStatement(true);node.specifiers = [];node.source = null;}else { // export { x, y as z } [from '...']
node.declaration = null;node.specifiers = this.parseExportSpecifiers();if(this.eatContextual("from")){node.source = this.type === _tokentype.types.string?this.parseExprAtom():this.unexpected();}else {node.source = null;}this.semicolon();}return this.finishNode(node,"ExportNamedDeclaration");};pp.shouldParseExportStatement = function(){return this.type.keyword;}; // Parses a comma-separated list of module exports.
pp.parseExportSpecifiers = function(){var nodes=[],first=true; // export { x, y as z } [from '...']
this.expect(_tokentype.types.braceL);while(!this.eat(_tokentype.types.braceR)) {if(!first){this.expect(_tokentype.types.comma);if(this.afterTrailingComma(_tokentype.types.braceR))break;}else first = false;var node=this.startNode();node.local = this.parseIdent(this.type === _tokentype.types._default);node.exported = this.eatContextual("as")?this.parseIdent(true):node.local;nodes.push(this.finishNode(node,"ExportSpecifier"));}return nodes;}; // Parses import declaration.
pp.parseImport = function(node){this.next(); // import '...'
if(this.type === _tokentype.types.string){node.specifiers = empty;node.source = this.parseExprAtom();}else {node.specifiers = this.parseImportSpecifiers();this.expectContextual("from");node.source = this.type === _tokentype.types.string?this.parseExprAtom():this.unexpected();}this.semicolon();return this.finishNode(node,"ImportDeclaration");}; // Parses a comma-separated list of module imports.
pp.parseImportSpecifiers = function(){var nodes=[],first=true;if(this.type === _tokentype.types.name){ // import defaultObj, { x, y as z } from '...'
var node=this.startNode();node.local = this.parseIdent();this.checkLVal(node.local,true);nodes.push(this.finishNode(node,"ImportDefaultSpecifier"));if(!this.eat(_tokentype.types.comma))return nodes;}if(this.type === _tokentype.types.star){var node=this.startNode();this.next();this.expectContextual("as");node.local = this.parseIdent();this.checkLVal(node.local,true);nodes.push(this.finishNode(node,"ImportNamespaceSpecifier"));return nodes;}this.expect(_tokentype.types.braceL);while(!this.eat(_tokentype.types.braceR)) {if(!first){this.expect(_tokentype.types.comma);if(this.afterTrailingComma(_tokentype.types.braceR))break;}else first = false;var node=this.startNode();node.imported = this.parseIdent(true);node.local = this.eatContextual("as")?this.parseIdent():node.imported;this.checkLVal(node.local,true);nodes.push(this.finishNode(node,"ImportSpecifier"));}return nodes;};},{"./state":10,"./tokentype":14,"./whitespace":16}],12:[function(_dereq_,module,exports){ // The algorithm used to determine whether a regexp can appear at a
// given point in the program is loosely based on sweet.js' approach.
// See https://github.com/mozilla/sweet.js/wiki/design
"use strict";exports.__esModule = true;function _classCallCheck(instance,Constructor){if(!(instance instanceof Constructor)){throw new TypeError("Cannot call a class as a function");}}var _state=_dereq_("./state");var _tokentype=_dereq_("./tokentype");var _whitespace=_dereq_("./whitespace");var TokContext=function TokContext(token,isExpr,preserveSpace,override){_classCallCheck(this,TokContext);this.token = token;this.isExpr = !!isExpr;this.preserveSpace = !!preserveSpace;this.override = override;};exports.TokContext = TokContext;var types={b_stat:new TokContext("{",false),b_expr:new TokContext("{",true),b_tmpl:new TokContext("${",true),p_stat:new TokContext("(",false),p_expr:new TokContext("(",true),q_tmpl:new TokContext("`",true,true,function(p){return p.readTmplToken();}),f_expr:new TokContext("function",true)};exports.types = types;var pp=_state.Parser.prototype;pp.initialContext = function(){return [types.b_stat];};pp.braceIsBlock = function(prevType){if(prevType === _tokentype.types.colon){var _parent=this.curContext();if(_parent === types.b_stat || _parent === types.b_expr)return !_parent.isExpr;}if(prevType === _tokentype.types._return)return _whitespace.lineBreak.test(this.input.slice(this.lastTokEnd,this.start));if(prevType === _tokentype.types._else || prevType === _tokentype.types.semi || prevType === _tokentype.types.eof || prevType === _tokentype.types.parenR)return true;if(prevType == _tokentype.types.braceL)return this.curContext() === types.b_stat;return !this.exprAllowed;};pp.updateContext = function(prevType){var update=undefined,type=this.type;if(type.keyword && prevType == _tokentype.types.dot)this.exprAllowed = false;else if(update = type.updateContext)update.call(this,prevType);else this.exprAllowed = type.beforeExpr;}; // Token-specific context update code
_tokentype.types.parenR.updateContext = _tokentype.types.braceR.updateContext = function(){if(this.context.length == 1){this.exprAllowed = true;return;}var out=this.context.pop();if(out === types.b_stat && this.curContext() === types.f_expr){this.context.pop();this.exprAllowed = false;}else if(out === types.b_tmpl){this.exprAllowed = true;}else {this.exprAllowed = !out.isExpr;}};_tokentype.types.braceL.updateContext = function(prevType){this.context.push(this.braceIsBlock(prevType)?types.b_stat:types.b_expr);this.exprAllowed = true;};_tokentype.types.dollarBraceL.updateContext = function(){this.context.push(types.b_tmpl);this.exprAllowed = true;};_tokentype.types.parenL.updateContext = function(prevType){var statementParens=prevType === _tokentype.types._if || prevType === _tokentype.types._for || prevType === _tokentype.types._with || prevType === _tokentype.types._while;this.context.push(statementParens?types.p_stat:types.p_expr);this.exprAllowed = true;};_tokentype.types.incDec.updateContext = function(){ // tokExprAllowed stays unchanged
};_tokentype.types._function.updateContext = function(){if(this.curContext() !== types.b_stat)this.context.push(types.f_expr);this.exprAllowed = false;};_tokentype.types.backQuote.updateContext = function(){if(this.curContext() === types.q_tmpl)this.context.pop();else this.context.push(types.q_tmpl);this.exprAllowed = false;};},{"./state":10,"./tokentype":14,"./whitespace":16}],13:[function(_dereq_,module,exports){"use strict";exports.__esModule = true;function _classCallCheck(instance,Constructor){if(!(instance instanceof Constructor)){throw new TypeError("Cannot call a class as a function");}}var _identifier=_dereq_("./identifier");var _tokentype=_dereq_("./tokentype");var _state=_dereq_("./state");var _locutil=_dereq_("./locutil");var _whitespace=_dereq_("./whitespace"); // Object type used to represent tokens. Note that normally, tokens
// simply exist as properties on the parser object. This is only
// used for the onToken callback and the external tokenizer.
var Token=function Token(p){_classCallCheck(this,Token);this.type = p.type;this.value = p.value;this.start = p.start;this.end = p.end;if(p.options.locations)this.loc = new _locutil.SourceLocation(p,p.startLoc,p.endLoc);if(p.options.ranges)this.range = [p.start,p.end];} // ## Tokenizer
;exports.Token = Token;var pp=_state.Parser.prototype; // Are we running under Rhino?
var isRhino=typeof Packages == "object" && Object.prototype.toString.call(Packages) == "[object JavaPackage]"; // Move to the next token
pp.next = function(){if(this.options.onToken)this.options.onToken(new Token(this));this.lastTokEnd = this.end;this.lastTokStart = this.start;this.lastTokEndLoc = this.endLoc;this.lastTokStartLoc = this.startLoc;this.nextToken();};pp.getToken = function(){this.next();return new Token(this);}; // If we're in an ES6 environment, make parsers iterable
if(typeof Symbol !== "undefined")pp[Symbol.iterator] = function(){var self=this;return {next:function next(){var token=self.getToken();return {done:token.type === _tokentype.types.eof,value:token};}};}; // Toggle strict mode. Re-reads the next number or string to please
// pedantic tests (`"use strict"; 010;` should fail).
pp.setStrict = function(strict){this.strict = strict;if(this.type !== _tokentype.types.num && this.type !== _tokentype.types.string)return;this.pos = this.start;if(this.options.locations){while(this.pos < this.lineStart) {this.lineStart = this.input.lastIndexOf("\n",this.lineStart - 2) + 1;--this.curLine;}}this.nextToken();};pp.curContext = function(){return this.context[this.context.length - 1];}; // Read a single token, updating the parser object's token-related
// properties.
pp.nextToken = function(){var curContext=this.curContext();if(!curContext || !curContext.preserveSpace)this.skipSpace();this.start = this.pos;if(this.options.locations)this.startLoc = this.curPosition();if(this.pos >= this.input.length)return this.finishToken(_tokentype.types.eof);if(curContext.override)return curContext.override(this);else this.readToken(this.fullCharCodeAtPos());};pp.readToken = function(code){ // Identifier or keyword. '\uXXXX' sequences are allowed in
// identifiers, so '\' also dispatches to that.
if(_identifier.isIdentifierStart(code,this.options.ecmaVersion >= 6) || code === 92 /* '\' */)return this.readWord();return this.getTokenFromCode(code);};pp.fullCharCodeAtPos = function(){var code=this.input.charCodeAt(this.pos);if(code <= 0xd7ff || code >= 0xe000)return code;var next=this.input.charCodeAt(this.pos + 1);return (code << 10) + next - 0x35fdc00;};pp.skipBlockComment = function(){var startLoc=this.options.onComment && this.curPosition();var start=this.pos,end=this.input.indexOf("*/",this.pos += 2);if(end === -1)this.raise(this.pos - 2,"Unterminated comment");this.pos = end + 2;if(this.options.locations){_whitespace.lineBreakG.lastIndex = start;var match=undefined;while((match = _whitespace.lineBreakG.exec(this.input)) && match.index < this.pos) {++this.curLine;this.lineStart = match.index + match[0].length;}}if(this.options.onComment)this.options.onComment(true,this.input.slice(start + 2,end),start,this.pos,startLoc,this.curPosition());};pp.skipLineComment = function(startSkip){var start=this.pos;var startLoc=this.options.onComment && this.curPosition();var ch=this.input.charCodeAt(this.pos += startSkip);while(this.pos < this.input.length && ch !== 10 && ch !== 13 && ch !== 8232 && ch !== 8233) {++this.pos;ch = this.input.charCodeAt(this.pos);}if(this.options.onComment)this.options.onComment(false,this.input.slice(start + startSkip,this.pos),start,this.pos,startLoc,this.curPosition());}; // Called at the start of the parse and after every token. Skips
// whitespace and comments, and.
pp.skipSpace = function(){loop: while(this.pos < this.input.length) {var ch=this.input.charCodeAt(this.pos);switch(ch){case 32:case 160: // ' '
++this.pos;break;case 13:if(this.input.charCodeAt(this.pos + 1) === 10){++this.pos;}case 10:case 8232:case 8233:++this.pos;if(this.options.locations){++this.curLine;this.lineStart = this.pos;}break;case 47: // '/'
switch(this.input.charCodeAt(this.pos + 1)){case 42: // '*'
this.skipBlockComment();break;case 47:this.skipLineComment(2);break;default:break loop;}break;default:if(ch > 8 && ch < 14 || ch >= 5760 && _whitespace.nonASCIIwhitespace.test(String.fromCharCode(ch))){++this.pos;}else {break loop;}}}}; // Called at the end of every token. Sets `end`, `val`, and
// maintains `context` and `exprAllowed`, and skips the space after
// the token, so that the next one's `start` will point at the
// right position.
pp.finishToken = function(type,val){this.end = this.pos;if(this.options.locations)this.endLoc = this.curPosition();var prevType=this.type;this.type = type;this.value = val;this.updateContext(prevType);}; // ### Token reading
// This is the function that is called to fetch the next token. It
// is somewhat obscure, because it works in character codes rather
// than characters, and because operator parsing has been inlined
// into it.
//
// All in the name of speed.
//
pp.readToken_dot = function(){var next=this.input.charCodeAt(this.pos + 1);if(next >= 48 && next <= 57)return this.readNumber(true);var next2=this.input.charCodeAt(this.pos + 2);if(this.options.ecmaVersion >= 6 && next === 46 && next2 === 46){ // 46 = dot '.'
this.pos += 3;return this.finishToken(_tokentype.types.ellipsis);}else {++this.pos;return this.finishToken(_tokentype.types.dot);}};pp.readToken_slash = function(){ // '/'
var next=this.input.charCodeAt(this.pos + 1);if(this.exprAllowed){++this.pos;return this.readRegexp();}if(next === 61)return this.finishOp(_tokentype.types.assign,2);return this.finishOp(_tokentype.types.slash,1);};pp.readToken_mult_modulo = function(code){ // '%*'
var next=this.input.charCodeAt(this.pos + 1);if(next === 61)return this.finishOp(_tokentype.types.assign,2);return this.finishOp(code === 42?_tokentype.types.star:_tokentype.types.modulo,1);};pp.readToken_pipe_amp = function(code){ // '|&'
var next=this.input.charCodeAt(this.pos + 1);if(next === code)return this.finishOp(code === 124?_tokentype.types.logicalOR:_tokentype.types.logicalAND,2);if(next === 61)return this.finishOp(_tokentype.types.assign,2);return this.finishOp(code === 124?_tokentype.types.bitwiseOR:_tokentype.types.bitwiseAND,1);};pp.readToken_caret = function(){ // '^'
var next=this.input.charCodeAt(this.pos + 1);if(next === 61)return this.finishOp(_tokentype.types.assign,2);return this.finishOp(_tokentype.types.bitwiseXOR,1);};pp.readToken_plus_min = function(code){ // '+-'
var next=this.input.charCodeAt(this.pos + 1);if(next === code){if(next == 45 && this.input.charCodeAt(this.pos + 2) == 62 && _whitespace.lineBreak.test(this.input.slice(this.lastTokEnd,this.pos))){ // A `-->` line comment
this.skipLineComment(3);this.skipSpace();return this.nextToken();}return this.finishOp(_tokentype.types.incDec,2);}if(next === 61)return this.finishOp(_tokentype.types.assign,2);return this.finishOp(_tokentype.types.plusMin,1);};pp.readToken_lt_gt = function(code){ // '<>'
var next=this.input.charCodeAt(this.pos + 1);var size=1;if(next === code){size = code === 62 && this.input.charCodeAt(this.pos + 2) === 62?3:2;if(this.input.charCodeAt(this.pos + size) === 61)return this.finishOp(_tokentype.types.assign,size + 1);return this.finishOp(_tokentype.types.bitShift,size);}if(next == 33 && code == 60 && this.input.charCodeAt(this.pos + 2) == 45 && this.input.charCodeAt(this.pos + 3) == 45){if(this.inModule)this.unexpected(); // `<!--`, an XML-style comment that should be interpreted as a line comment
this.skipLineComment(4);this.skipSpace();return this.nextToken();}if(next === 61)size = this.input.charCodeAt(this.pos + 2) === 61?3:2;return this.finishOp(_tokentype.types.relational,size);};pp.readToken_eq_excl = function(code){ // '=!'
var next=this.input.charCodeAt(this.pos + 1);if(next === 61)return this.finishOp(_tokentype.types.equality,this.input.charCodeAt(this.pos + 2) === 61?3:2);if(code === 61 && next === 62 && this.options.ecmaVersion >= 6){ // '=>'
this.pos += 2;return this.finishToken(_tokentype.types.arrow);}return this.finishOp(code === 61?_tokentype.types.eq:_tokentype.types.prefix,1);};pp.getTokenFromCode = function(code){switch(code){ // The interpretation of a dot depends on whether it is followed
// by a digit or another two dots.
case 46: // '.'
return this.readToken_dot(); // Punctuation tokens.
case 40:++this.pos;return this.finishToken(_tokentype.types.parenL);case 41:++this.pos;return this.finishToken(_tokentype.types.parenR);case 59:++this.pos;return this.finishToken(_tokentype.types.semi);case 44:++this.pos;return this.finishToken(_tokentype.types.comma);case 91:++this.pos;return this.finishToken(_tokentype.types.bracketL);case 93:++this.pos;return this.finishToken(_tokentype.types.bracketR);case 123:++this.pos;return this.finishToken(_tokentype.types.braceL);case 125:++this.pos;return this.finishToken(_tokentype.types.braceR);case 58:++this.pos;return this.finishToken(_tokentype.types.colon);case 63:++this.pos;return this.finishToken(_tokentype.types.question);case 96: // '`'
if(this.options.ecmaVersion < 6)break;++this.pos;return this.finishToken(_tokentype.types.backQuote);case 48: // '0'
var next=this.input.charCodeAt(this.pos + 1);if(next === 120 || next === 88)return this.readRadixNumber(16); // '0x', '0X' - hex number
if(this.options.ecmaVersion >= 6){if(next === 111 || next === 79)return this.readRadixNumber(8); // '0o', '0O' - octal number
if(next === 98 || next === 66)return this.readRadixNumber(2); // '0b', '0B' - binary number
} // Anything else beginning with a digit is an integer, octal
// number, or float.
case 49:case 50:case 51:case 52:case 53:case 54:case 55:case 56:case 57: // 1-9
return this.readNumber(false); // Quotes produce strings.
case 34:case 39: // '"', "'"
return this.readString(code); // Operators are parsed inline in tiny state machines. '=' (61) is
// often referred to. `finishOp` simply skips the amount of
// characters it is given as second argument, and returns a token
// of the type given by its first argument.
case 47: // '/'
return this.readToken_slash();case 37:case 42: // '%*'
return this.readToken_mult_modulo(code);case 124:case 38: // '|&'
return this.readToken_pipe_amp(code);case 94: // '^'
return this.readToken_caret();case 43:case 45: // '+-'
return this.readToken_plus_min(code);case 60:case 62: // '<>'
return this.readToken_lt_gt(code);case 61:case 33: // '=!'
return this.readToken_eq_excl(code);case 126: // '~'
return this.finishOp(_tokentype.types.prefix,1);}this.raise(this.pos,"Unexpected character '" + codePointToString(code) + "'");};pp.finishOp = function(type,size){var str=this.input.slice(this.pos,this.pos + size);this.pos += size;return this.finishToken(type,str);}; // Parse a regular expression. Some context-awareness is necessary,
// since a '/' inside a '[]' set does not end the expression.
function tryCreateRegexp(src,flags,throwErrorAt){try{return new RegExp(src,flags);}catch(e) {if(throwErrorAt !== undefined){if(e instanceof SyntaxError)this.raise(throwErrorAt,"Error parsing regular expression: " + e.message);this.raise(e);}}}var regexpUnicodeSupport=!!tryCreateRegexp("￿","u");pp.readRegexp = function(){var _this=this;var escaped=undefined,inClass=undefined,start=this.pos;for(;;) {if(this.pos >= this.input.length)this.raise(start,"Unterminated regular expression");var ch=this.input.charAt(this.pos);if(_whitespace.lineBreak.test(ch))this.raise(start,"Unterminated regular expression");if(!escaped){if(ch === "[")inClass = true;else if(ch === "]" && inClass)inClass = false;else if(ch === "/" && !inClass)break;escaped = ch === "\\";}else escaped = false;++this.pos;}var content=this.input.slice(start,this.pos);++this.pos; // Need to use `readWord1` because '\uXXXX' sequences are allowed
// here (don't ask).
var mods=this.readWord1();var tmp=content;if(mods){var validFlags=/^[gmsiy]*$/;if(this.options.ecmaVersion >= 6)validFlags = /^[gmsiyu]*$/;if(!validFlags.test(mods))this.raise(start,"Invalid regular expression flag");if(mods.indexOf('u') >= 0 && !regexpUnicodeSupport){ // Replace each astral symbol and every Unicode escape sequence that
// possibly represents an astral symbol or a paired surrogate with a
// single ASCII symbol to avoid throwing on regular expressions that
// are only valid in combination with the `/u` flag.
// Note: replacing with the ASCII symbol `x` might cause false
// negatives in unlikely scenarios. For example, `[\u{61}-b]` is a
// perfectly valid pattern that is equivalent to `[a-b]`, but it would
// be replaced by `[x-b]` which throws an error.
tmp = tmp.replace(/\\u\{([0-9a-fA-F]+)\}/g,function(match,code,offset){code = Number("0x" + code);if(code > 0x10FFFF)_this.raise(start + offset + 3,"Code point out of bounds");return "x";});tmp = tmp.replace(/\\u([a-fA-F0-9]{4})|[\uD800-\uDBFF][\uDC00-\uDFFF]/g,"x");}} // Detect invalid regular expressions.
var value=null; // Rhino's regular expression parser is flaky and throws uncatchable exceptions,
// so don't do detection if we are running under Rhino
if(!isRhino){tryCreateRegexp(tmp,undefined,start); // Get a regular expression object for this pattern-flag pair, or `null` in
// case the current environment doesn't support the flags it uses.
value = tryCreateRegexp(content,mods);}return this.finishToken(_tokentype.types.regexp,{pattern:content,flags:mods,value:value});}; // Read an integer in the given radix. Return null if zero digits
// were read, the integer value otherwise. When `len` is given, this
// will return `null` unless the integer has exactly `len` digits.
pp.readInt = function(radix,len){var start=this.pos,total=0;for(var i=0,e=len == null?Infinity:len;i < e;++i) {var code=this.input.charCodeAt(this.pos),val=undefined;if(code >= 97)val = code - 97 + 10; // a
else if(code >= 65)val = code - 65 + 10; // A
else if(code >= 48 && code <= 57)val = code - 48; // 0-9
else val = Infinity;if(val >= radix)break;++this.pos;total = total * radix + val;}if(this.pos === start || len != null && this.pos - start !== len)return null;return total;};pp.readRadixNumber = function(radix){this.pos += 2; // 0x
var val=this.readInt(radix);if(val == null)this.raise(this.start + 2,"Expected number in radix " + radix);if(_identifier.isIdentifierStart(this.fullCharCodeAtPos()))this.raise(this.pos,"Identifier directly after number");return this.finishToken(_tokentype.types.num,val);}; // Read an integer, octal integer, or floating-point number.
pp.readNumber = function(startsWithDot){var start=this.pos,isFloat=false,octal=this.input.charCodeAt(this.pos) === 48;if(!startsWithDot && this.readInt(10) === null)this.raise(start,"Invalid number");var next=this.input.charCodeAt(this.pos);if(next === 46){ // '.'
++this.pos;this.readInt(10);isFloat = true;next = this.input.charCodeAt(this.pos);}if(next === 69 || next === 101){ // 'eE'
next = this.input.charCodeAt(++this.pos);if(next === 43 || next === 45)++this.pos; // '+-'
if(this.readInt(10) === null)this.raise(start,"Invalid number");isFloat = true;}if(_identifier.isIdentifierStart(this.fullCharCodeAtPos()))this.raise(this.pos,"Identifier directly after number");var str=this.input.slice(start,this.pos),val=undefined;if(isFloat)val = parseFloat(str);else if(!octal || str.length === 1)val = parseInt(str,10);else if(/[89]/.test(str) || this.strict)this.raise(start,"Invalid number");else val = parseInt(str,8);return this.finishToken(_tokentype.types.num,val);}; // Read a string value, interpreting backslash-escapes.
pp.readCodePoint = function(){var ch=this.input.charCodeAt(this.pos),code=undefined;if(ch === 123){if(this.options.ecmaVersion < 6)this.unexpected();var codePos=++this.pos;code = this.readHexChar(this.input.indexOf('}',this.pos) - this.pos);++this.pos;if(code > 0x10FFFF)this.raise(codePos,"Code point out of bounds");}else {code = this.readHexChar(4);}return code;};function codePointToString(code){ // UTF-16 Decoding
if(code <= 0xFFFF)return String.fromCharCode(code);code -= 0x10000;return String.fromCharCode((code >> 10) + 0xD800,(code & 1023) + 0xDC00);}pp.readString = function(quote){var out="",chunkStart=++this.pos;for(;;) {if(this.pos >= this.input.length)this.raise(this.start,"Unterminated string constant");var ch=this.input.charCodeAt(this.pos);if(ch === quote)break;if(ch === 92){ // '\'
out += this.input.slice(chunkStart,this.pos);out += this.readEscapedChar(false);chunkStart = this.pos;}else {if(_whitespace.isNewLine(ch))this.raise(this.start,"Unterminated string constant");++this.pos;}}out += this.input.slice(chunkStart,this.pos++);return this.finishToken(_tokentype.types.string,out);}; // Reads template string tokens.
pp.readTmplToken = function(){var out="",chunkStart=this.pos;for(;;) {if(this.pos >= this.input.length)this.raise(this.start,"Unterminated template");var ch=this.input.charCodeAt(this.pos);if(ch === 96 || ch === 36 && this.input.charCodeAt(this.pos + 1) === 123){ // '`', '${'
if(this.pos === this.start && this.type === _tokentype.types.template){if(ch === 36){this.pos += 2;return this.finishToken(_tokentype.types.dollarBraceL);}else {++this.pos;return this.finishToken(_tokentype.types.backQuote);}}out += this.input.slice(chunkStart,this.pos);return this.finishToken(_tokentype.types.template,out);}if(ch === 92){ // '\'
out += this.input.slice(chunkStart,this.pos);out += this.readEscapedChar(true);chunkStart = this.pos;}else if(_whitespace.isNewLine(ch)){out += this.input.slice(chunkStart,this.pos);++this.pos;switch(ch){case 13:if(this.input.charCodeAt(this.pos) === 10)++this.pos;case 10:out += "\n";break;default:out += String.fromCharCode(ch);break;}if(this.options.locations){++this.curLine;this.lineStart = this.pos;}chunkStart = this.pos;}else {++this.pos;}}}; // Used to read escaped characters
pp.readEscapedChar = function(inTemplate){var ch=this.input.charCodeAt(++this.pos);++this.pos;switch(ch){case 110:return "\n"; // 'n' -> '\n'
case 114:return "\r"; // 'r' -> '\r'
case 120:return String.fromCharCode(this.readHexChar(2)); // 'x'
case 117:return codePointToString(this.readCodePoint()); // 'u'
case 116:return "\t"; // 't' -> '\t'
case 98:return "\b"; // 'b' -> '\b'
case 118:return "\u000b"; // 'v' -> '\u000b'
case 102:return "\f"; // 'f' -> '\f'
case 13:if(this.input.charCodeAt(this.pos) === 10)++this.pos; // '\r\n'
case 10: // ' \n'
if(this.options.locations){this.lineStart = this.pos;++this.curLine;}return "";default:if(ch >= 48 && ch <= 55){var octalStr=this.input.substr(this.pos - 1,3).match(/^[0-7]+/)[0];var octal=parseInt(octalStr,8);if(octal > 255){octalStr = octalStr.slice(0,-1);octal = parseInt(octalStr,8);}if(octal > 0 && (this.strict || inTemplate)){this.raise(this.pos - 2,"Octal literal in strict mode");}this.pos += octalStr.length - 1;return String.fromCharCode(octal);}return String.fromCharCode(ch);}}; // Used to read character escape sequences ('\x', '\u', '\U').
pp.readHexChar = function(len){var codePos=this.pos;var n=this.readInt(16,len);if(n === null)this.raise(codePos,"Bad character escape sequence");return n;}; // Read an identifier, and return it as a string. Sets `this.containsEsc`
// to whether the word contained a '\u' escape.
//
// Incrementally adds only escaped chars, adding other chunks as-is
// as a micro-optimization.
pp.readWord1 = function(){this.containsEsc = false;var word="",first=true,chunkStart=this.pos;var astral=this.options.ecmaVersion >= 6;while(this.pos < this.input.length) {var ch=this.fullCharCodeAtPos();if(_identifier.isIdentifierChar(ch,astral)){this.pos += ch <= 0xffff?1:2;}else if(ch === 92){ // "\"
this.containsEsc = true;word += this.input.slice(chunkStart,this.pos);var escStart=this.pos;if(this.input.charCodeAt(++this.pos) != 117) // "u"
this.raise(this.pos,"Expecting Unicode escape sequence \\uXXXX");++this.pos;var esc=this.readCodePoint();if(!(first?_identifier.isIdentifierStart:_identifier.isIdentifierChar)(esc,astral))this.raise(escStart,"Invalid Unicode escape");word += codePointToString(esc);chunkStart = this.pos;}else {break;}first = false;}return word + this.input.slice(chunkStart,this.pos);}; // Read an identifier or keyword token. Will check for reserved
// words when necessary.
pp.readWord = function(){var word=this.readWord1();var type=_tokentype.types.name;if((this.options.ecmaVersion >= 6 || !this.containsEsc) && this.isKeyword(word))type = _tokentype.keywords[word];return this.finishToken(type,word);};},{"./identifier":2,"./locutil":5,"./state":10,"./tokentype":14,"./whitespace":16}],14:[function(_dereq_,module,exports){ // ## Token types
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
"use strict";exports.__esModule = true;function _classCallCheck(instance,Constructor){if(!(instance instanceof Constructor)){throw new TypeError("Cannot call a class as a function");}}var TokenType=function TokenType(label){var conf=arguments.length <= 1 || arguments[1] === undefined?{}:arguments[1];_classCallCheck(this,TokenType);this.label = label;this.keyword = conf.keyword;this.beforeExpr = !!conf.beforeExpr;this.startsExpr = !!conf.startsExpr;this.isLoop = !!conf.isLoop;this.isAssign = !!conf.isAssign;this.prefix = !!conf.prefix;this.postfix = !!conf.postfix;this.binop = conf.binop || null;this.updateContext = null;};exports.TokenType = TokenType;function binop(name,prec){return new TokenType(name,{beforeExpr:true,binop:prec});}var beforeExpr={beforeExpr:true},startsExpr={startsExpr:true};var types={num:new TokenType("num",startsExpr),regexp:new TokenType("regexp",startsExpr),string:new TokenType("string",startsExpr),name:new TokenType("name",startsExpr),eof:new TokenType("eof"), // Punctuation token types.
bracketL:new TokenType("[",{beforeExpr:true,startsExpr:true}),bracketR:new TokenType("]"),braceL:new TokenType("{",{beforeExpr:true,startsExpr:true}),braceR:new TokenType("}"),parenL:new TokenType("(",{beforeExpr:true,startsExpr:true}),parenR:new TokenType(")"),comma:new TokenType(",",beforeExpr),semi:new TokenType(";",beforeExpr),colon:new TokenType(":",beforeExpr),dot:new TokenType("."),question:new TokenType("?",beforeExpr),arrow:new TokenType("=>",beforeExpr),template:new TokenType("template"),ellipsis:new TokenType("...",beforeExpr),backQuote:new TokenType("`",startsExpr),dollarBraceL:new TokenType("${",{beforeExpr:true,startsExpr:true}), // Operators. These carry several kinds of properties to help the
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
eq:new TokenType("=",{beforeExpr:true,isAssign:true}),assign:new TokenType("_=",{beforeExpr:true,isAssign:true}),incDec:new TokenType("++/--",{prefix:true,postfix:true,startsExpr:true}),prefix:new TokenType("prefix",{beforeExpr:true,prefix:true,startsExpr:true}),logicalOR:binop("||",1),logicalAND:binop("&&",2),bitwiseOR:binop("|",3),bitwiseXOR:binop("^",4),bitwiseAND:binop("&",5),equality:binop("==/!=",6),relational:binop("</>",7),bitShift:binop("<</>>",8),plusMin:new TokenType("+/-",{beforeExpr:true,binop:9,prefix:true,startsExpr:true}),modulo:binop("%",10),star:binop("*",10),slash:binop("/",10)};exports.types = types; // Map keyword names to token types.
var keywords={};exports.keywords = keywords; // Succinct definitions of keyword token types
function kw(name){var options=arguments.length <= 1 || arguments[1] === undefined?{}:arguments[1];options.keyword = name;keywords[name] = types["_" + name] = new TokenType(name,options);}kw("break");kw("case",beforeExpr);kw("catch");kw("continue");kw("debugger");kw("default",beforeExpr);kw("do",{isLoop:true});kw("else",beforeExpr);kw("finally");kw("for",{isLoop:true});kw("function",startsExpr);kw("if");kw("return",beforeExpr);kw("switch");kw("throw",beforeExpr);kw("try");kw("var");kw("let");kw("const");kw("while",{isLoop:true});kw("with");kw("new",{beforeExpr:true,startsExpr:true});kw("this",startsExpr);kw("super",startsExpr);kw("class");kw("extends",beforeExpr);kw("export");kw("import");kw("yield",{beforeExpr:true,startsExpr:true});kw("null",startsExpr);kw("true",startsExpr);kw("false",startsExpr);kw("in",{beforeExpr:true,binop:7});kw("instanceof",{beforeExpr:true,binop:7});kw("typeof",{beforeExpr:true,prefix:true,startsExpr:true});kw("void",{beforeExpr:true,prefix:true,startsExpr:true});kw("delete",{beforeExpr:true,prefix:true,startsExpr:true});},{}],15:[function(_dereq_,module,exports){"use strict";exports.__esModule = true;exports.isArray = isArray;exports.has = has;function isArray(obj){return Object.prototype.toString.call(obj) === "[object Array]";} // Checks if an object has a property.
function has(obj,propName){return Object.prototype.hasOwnProperty.call(obj,propName);}},{}],16:[function(_dereq_,module,exports){ // Matches a whole line break (where CRLF is considered a single
// line break). Used to count lines.
"use strict";exports.__esModule = true;exports.isNewLine = isNewLine;var lineBreak=/\r\n?|\n|\u2028|\u2029/;exports.lineBreak = lineBreak;var lineBreakG=new RegExp(lineBreak.source,"g");exports.lineBreakG = lineBreakG;function isNewLine(code){return code === 10 || code === 13 || code === 0x2028 || code == 0x2029;}var nonASCIIwhitespace=/[\u1680\u180e\u2000-\u200a\u202f\u205f\u3000\ufeff]/;exports.nonASCIIwhitespace = nonASCIIwhitespace;},{}]},{},[3])(3);});

}).call(this,typeof global !== "undefined" ? global : typeof self !== "undefined" ? self : typeof window !== "undefined" ? window : {})
},{}],2:[function(_dereq_,module,exports){
"use strict";

module.exports = typeof acorn != 'undefined' ? acorn : _dereq_("acorn");

},{"acorn":1}],3:[function(_dereq_,module,exports){
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
    raw: this.input.slice(this.tok.start, this.tok.end).replace(/\r\n?/g, '\n'),
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
      curElt.value = { cooked: '', raw: '' };
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

},{"..":2,"./parseutil":5,"./state":6}],4:[function(_dereq_,module,exports){
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

},{"..":2,"./expression":3,"./state":6,"./statement":7,"./tokenize":8}],5:[function(_dereq_,module,exports){
"use strict";

exports.__esModule = true;
exports.isDummy = isDummy;

function isDummy(node) {
  return node.name == "✖";
}

},{}],6:[function(_dereq_,module,exports){
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

},{"..":2}],7:[function(_dereq_,module,exports){
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
    node.kind = '';
  } else {
    var elt = undefined;
    if (this.tok.type === _.tokTypes.name && this.tok.value !== "from") {
      elt = this.startNode();
      elt.local = this.parseIdent();
      this.finishNode(elt, "ImportDefaultSpecifier");
      this.eat(_.tokTypes.comma);
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

},{"..":2,"./parseutil":5,"./state":6}],8:[function(_dereq_,module,exports){
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

},{"..":2,"./state":6}]},{},[4])(4)
});
}).call(this,typeof global !== "undefined" ? global : typeof self !== "undefined" ? self : typeof window !== "undefined" ? window : {})

},{}],15:[function(require,module,exports){
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
}

// Find a node with a given start, end, and type (all are optional,
// null can be used as wildcard). Returns a {node, state} object, or
// undefined when it doesn't find a matching node.
;

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
    var decl = node.declarations[i];
    c(decl.id, st, "Pattern");
    if (decl.init) c(decl.init, st, "Expression");
  }
};

base.Function = function (node, st, c) {
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

},{}],16:[function(require,module,exports){
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

},{}],17:[function(require,module,exports){
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

},{}],18:[function(require,module,exports){
module.exports = function isBuffer(arg) {
  return arg && typeof arg === 'object'
    && typeof arg.copy === 'function'
    && typeof arg.fill === 'function'
    && typeof arg.readUInt8 === 'function';
}
},{}],19:[function(require,module,exports){
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

},{"./support/isBuffer":18,"_process":17,"inherits":16}]},{},[7])(7)
});
//# sourceMappingURL=data:application/json;charset:utf-8;base64,eyJ2ZXJzaW9uIjozLCJzb3VyY2VzIjpbIm5vZGVfbW9kdWxlcy9icm93c2VyaWZ5L25vZGVfbW9kdWxlcy9icm93c2VyLXBhY2svX3ByZWx1ZGUuanMiLCIvaG9tZS9zd2tpbS9XZWJzdG9ybVByb2plY3RzL3lhdGVybi9saWIvYXV4LmpzIiwiL2hvbWUvc3draW0vV2Vic3Rvcm1Qcm9qZWN0cy95YXRlcm4vbGliL2NvbnN0cmFpbnQvY0dlbi5qcyIsIi9ob21lL3N3a2ltL1dlYnN0b3JtUHJvamVjdHMveWF0ZXJuL2xpYi9jb25zdHJhaW50L2NvbnN0cmFpbnRzLmpzIiwiL2hvbWUvc3draW0vV2Vic3Rvcm1Qcm9qZWN0cy95YXRlcm4vbGliL2RvbWFpbnMvY29udGV4dC5qcyIsIi9ob21lL3N3a2ltL1dlYnN0b3JtUHJvamVjdHMveWF0ZXJuL2xpYi9kb21haW5zL3N0YXR1cy5qcyIsIi9ob21lL3N3a2ltL1dlYnN0b3JtUHJvamVjdHMveWF0ZXJuL2xpYi9kb21haW5zL3R5cGVzLmpzIiwiL2hvbWUvc3draW0vV2Vic3Rvcm1Qcm9qZWN0cy95YXRlcm4vbGliL2luZmVyLmpzIiwiL2hvbWUvc3draW0vV2Vic3Rvcm1Qcm9qZWN0cy95YXRlcm4vbGliL3JldE9jY3VyLmpzIiwiL2hvbWUvc3draW0vV2Vic3Rvcm1Qcm9qZWN0cy95YXRlcm4vbGliL3RoaXNPY2N1ci5qcyIsIi9ob21lL3N3a2ltL1dlYnN0b3JtUHJvamVjdHMveWF0ZXJuL2xpYi91dGlsL215V2Fsa2VyLmpzIiwiL2hvbWUvc3draW0vV2Vic3Rvcm1Qcm9qZWN0cy95YXRlcm4vbGliL3ZhckJsb2NrLmpzIiwiL2hvbWUvc3draW0vV2Vic3Rvcm1Qcm9qZWN0cy95YXRlcm4vbGliL3ZhcnJlZnMuanMiLCJub2RlX21vZHVsZXMvYWNvcm4vZGlzdC9hY29ybi5qcyIsIm5vZGVfbW9kdWxlcy9hY29ybi9kaXN0L2Fjb3JuX2xvb3NlLmpzIiwibm9kZV9tb2R1bGVzL2Fjb3JuL2Rpc3Qvd2Fsay5qcyIsIm5vZGVfbW9kdWxlcy9icm93c2VyaWZ5L25vZGVfbW9kdWxlcy9pbmhlcml0cy9pbmhlcml0c19icm93c2VyLmpzIiwibm9kZV9tb2R1bGVzL2Jyb3dzZXJpZnkvbm9kZV9tb2R1bGVzL3Byb2Nlc3MvYnJvd3Nlci5qcyIsIm5vZGVfbW9kdWxlcy9icm93c2VyaWZ5L25vZGVfbW9kdWxlcy91dGlsL3N1cHBvcnQvaXNCdWZmZXJCcm93c2VyLmpzIiwibm9kZV9tb2R1bGVzL2Jyb3dzZXJpZnkvbm9kZV9tb2R1bGVzL3V0aWwvdXRpbC5qcyJdLCJuYW1lcyI6W10sIm1hcHBpbmdzIjoiQUFBQTs7O0FDQUEsSUFBSSxJQUFJLEdBQUcsT0FBTyxDQUFDLE1BQU0sQ0FBQyxDQUFDOztBQUUzQixTQUFTLFdBQVcsQ0FBQyxHQUFHLEVBQUUsUUFBUSxFQUFFO0FBQ2hDLFFBQUksUUFBUSxHQUFHLEVBQUUsQ0FBQzs7QUFFbEIsUUFBSSxHQUFHLEdBQUcsUUFBUSxLQUFLLFNBQVMsR0FBRyxDQUFDLEdBQUcsUUFBUSxDQUFDOztBQUVoRCxhQUFTLFFBQVEsQ0FBQyxJQUFJLEVBQUU7QUFDcEIsWUFBSSxDQUFDLFFBQVEsQ0FBQyxHQUFHLEdBQUcsQ0FBQztBQUNyQixnQkFBUSxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsQ0FBQztBQUNwQixXQUFHLEVBQUUsQ0FBQztLQUNUOzs7QUFHRCxhQUFTLGlCQUFpQixDQUFDLElBQUksRUFBRTtBQUM3QixZQUFJLElBQUksSUFBSSxJQUFJLENBQUMsY0FBYyxDQUFDLE1BQU0sQ0FBQyxFQUFFO0FBQ3JDLG9CQUFRLENBQUMsSUFBSSxDQUFDLENBQUM7U0FDbEI7QUFDRCxZQUFJLElBQUksSUFBSSxPQUFPLElBQUksS0FBSyxRQUFRLEVBQUU7QUFDbEMsaUJBQUssSUFBSSxDQUFDLElBQUksSUFBSSxFQUFFO0FBQ2hCLGlDQUFpQixDQUFDLElBQUksQ0FBQyxDQUFDLENBQUMsQ0FBQyxDQUFDO2FBQzlCO1NBQ0o7S0FDSjs7QUFFRCxxQkFBaUIsQ0FBQyxHQUFHLENBQUMsQ0FBQzs7QUFFdkIsV0FB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O0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7Ozs7O0FDanZHQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBOzs7OztBQ3p0REE7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7Ozs7QUNqWEE7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBOztBQ3ZCQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTs7QUMxRkE7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBOzs7QUNMQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBIiwiZmlsZSI6ImdlbmVyYXRlZC5qcyIsInNvdXJjZVJvb3QiOiIiLCJzb3VyY2VzQ29udGVudCI6WyIoZnVuY3Rpb24gZSh0LG4scil7ZnVuY3Rpb24gcyhvLHUpe2lmKCFuW29dKXtpZighdFtvXSl7dmFyIGE9dHlwZW9mIHJlcXVpcmU9PVwiZnVuY3Rpb25cIiYmcmVxdWlyZTtpZighdSYmYSlyZXR1cm4gYShvLCEwKTtpZihpKXJldHVybiBpKG8sITApO3ZhciBmPW5ldyBFcnJvcihcIkNhbm5vdCBmaW5kIG1vZHVsZSAnXCIrbytcIidcIik7dGhyb3cgZi5jb2RlPVwiTU9EVUxFX05PVF9GT1VORFwiLGZ9dmFyIGw9bltvXT17ZXhwb3J0czp7fX07dFtvXVswXS5jYWxsKGwuZXhwb3J0cyxmdW5jdGlvbihlKXt2YXIgbj10W29dWzFdW2VdO3JldHVybiBzKG4/bjplKX0sbCxsLmV4cG9ydHMsZSx0LG4scil9cmV0dXJuIG5bb10uZXhwb3J0c312YXIgaT10eXBlb2YgcmVxdWlyZT09XCJmdW5jdGlvblwiJiZyZXF1aXJlO2Zvcih2YXIgbz0wO288ci5sZW5ndGg7bysrKXMocltvXSk7cmV0dXJuIHN9KSIsInZhciB1dGlsID0gcmVxdWlyZSgndXRpbCcpO1xuXG5mdW5jdGlvbiBnZXROb2RlTGlzdChhc3QsIHN0YXJ0TnVtKSB7XG4gICAgdmFyIG5vZGVMaXN0ID0gW107XG5cbiAgICB2YXIgbnVtID0gc3RhcnROdW0gPT09IHVuZGVmaW5lZCA/IDAgOiBzdGFydE51bTtcblxuICAgIGZ1bmN0aW9uIGFzc2lnbklkKG5vZGUpIHtcbiAgICAgICAgbm9kZVsnQGxhYmVsJ10gPSBudW07XG4gICAgICAgIG5vZGVMaXN0LnB1c2gobm9kZSk7XG4gICAgICAgIG51bSsrO1xuICAgIH1cblxuICAgIC8vIExhYmVsIGV2ZXJ5IEFTVCBub2RlIHdpdGggcHJvcGVydHkgJ3R5cGUnXG4gICAgZnVuY3Rpb24gbGFiZWxOb2RlV2l0aFR5cGUobm9kZSkge1xuICAgICAgICBpZiAobm9kZSAmJiBub2RlLmhhc093blByb3BlcnR5KCd0eXBlJykpIHtcbiAgICAgICAgICAgIGFzc2lnbklkKG5vZGUpO1xuICAgICAgICB9XG4gICAgICAgIGlmIChub2RlICYmIHR5cGVvZiBub2RlID09PSAnb2JqZWN0Jykge1xuICAgICAgICAgICAgZm9yICh2YXIgcCBpbiBub2RlKSB7XG4gICAgICAgICAgICAgICAgbGFiZWxOb2RlV2l0aFR5cGUobm9kZVtwXSk7XG4gICAgICAgICAgICB9XG4gICAgICAgIH1cbiAgICB9XG5cbiAgICBsYWJlbE5vZGVXaXRoVHlwZShhc3QpO1xuXG4gICAgcmV0dXJuIG5vZGVMaXN0O1xufVxuXG5mdW5jdGlvbiBzaG93VW5mb2xkZWQob2JqKSB7XG4gICAgY29uc29sZS5sb2codXRpbC5pbnNwZWN0KG9iaiwge2RlcHRoOiBudWxsfSkpO1xufVxuXG5leHBvcnRzLmdldE5vZGVMaXN0ID0gZ2V0Tm9kZUxpc3Q7XG5leHBvcnRzLnNob3dVbmZvbGRlZCA9IHNob3dVbmZvbGRlZDtcbiIsIid1c2Ugc3RyaWN0JztcblxuY29uc3QgdHlwZXMgPSByZXF1aXJlKCcuLi9kb21haW5zL3R5cGVzJyk7XG5jb25zdCB3YWxrID0gcmVxdWlyZSgnYWNvcm4vZGlzdC93YWxrJyk7XG5jb25zdCBzdGF0dXMgPSByZXF1aXJlKCcuLi9kb21haW5zL3N0YXR1cycpO1xuY29uc3QgY3N0ciA9IHJlcXVpcmUoJy4vY29uc3RyYWludHMnKTtcblxuLy8gYXJndW1lbnRzIGFyZSBcIiBvbGRTdGF0dXMgKCwgbmFtZSwgdmFsKSogXCJcbmZ1bmN0aW9uIGNoYW5nZWRTdGF0dXMob2xkU3RhdHVzKSB7XG4gICAgY29uc3QgbmV3U3RhdHVzID0gbmV3IHN0YXR1cy5TdGF0dXM7XG4gICAgZm9yIChsZXQgaSA9IDE7IGkgPCBhcmd1bWVudHMubGVuZ3RoOyBpID0gaSArIDIpXG4gICAgICAgIG5ld1N0YXR1c1thcmd1bWVudHNbaV1dID0gYXJndW1lbnRzW2krMV07XG5cbiAgICBmb3IgKGxldCBwIGluIG9sZFN0YXR1cykge1xuICAgICAgICBpZiAobmV3U3RhdHVzW3BdID09PSB1bmRlZmluZWQpXG4gICAgICAgICAgICBuZXdTdGF0dXNbcF0gPSBvbGRTdGF0dXNbcF07XG4gICAgfVxuICAgIHJldHVybiBuZXdTdGF0dXM7XG59XG5cbi8vIHJldHVybnMgW2FjY2VzcyB0eXBlLCBwcm9wIHZhbHVlXVxuZnVuY3Rpb24gcHJvcEFjY2Vzcyhub2RlKSB7XG4gICAgY29uc3QgcHJvcCA9IG5vZGUucHJvcGVydHk7XG4gICAgaWYgKCFub2RlLmNvbXB1dGVkKSB7XG4gICAgICAgIHJldHVybiBbJ2RvdEFjY2VzcycsIHByb3AubmFtZV07XG4gICAgfVxuICAgIGlmIChwcm9wLnR5cGUgPT09ICdMaXRlcmFsJykge1xuICAgICAgICBpZiAodHlwZW9mIHByb3AudmFsdWUgPT09ICdzdHJpbmcnKVxuICAgICAgICAgICAgcmV0dXJuIFsnc3RyaW5nTGl0ZXJhbCcsIHByb3AudmFsdWVdO1xuICAgICAgICBpZiAodHlwZW9mIHByb3AudmFsdWUgPT09ICdudW1iZXInKVxuICAgICAgICAgICAgLy8gY29udmVydCBudW1iZXIgdG8gc3RyaW5nXG4gICAgICAgICAgICByZXR1cm4gWydudW1iZXJMaXRlcmFsJywgcHJvcC52YWx1ZSArICcnXTtcbiAgICB9XG4gICAgcmV0dXJuIFtcImNvbXB1dGVkXCIsIG51bGxdO1xufVxuXG5mdW5jdGlvbiB1bm9wUmVzdWx0VHlwZShvcCkge1xuICAgIHN3aXRjaCAob3ApIHtcbiAgICAgICAgY2FzZSAnKyc6IGNhc2UgJy0nOiBjYXNlICd+JzpcbiAgICAgICAgICAgIHJldHVybiB0eXBlcy5QcmltTnVtYmVyO1xuICAgICAgICBjYXNlICchJzpcbiAgICAgICAgICAgIHJldHVybiB0eXBlcy5QcmltQm9vbGVhbjtcbiAgICAgICAgY2FzZSAndHlwZW9mJzpcbiAgICAgICAgICAgIHJldHVybiB0eXBlcy5QcmltU3RyaW5nO1xuICAgICAgICBjYXNlICd2b2lkJzogY2FzZSAnZGVsZXRlJzpcbiAgICAgICAgICAgIHJldHVybiBudWxsO1xuICAgIH1cbn1cblxuZnVuY3Rpb24gYmlub3BJc0Jvb2xlYW4ob3ApIHtcbiAgICBzd2l0Y2ggKG9wKSB7XG4gICAgICAgIGNhc2UgJz09JzogY2FzZSAnIT0nOiBjYXNlICc9PT0nOiBjYXNlICchPT0nOlxuICAgICAgICBjYXNlICc8JzogY2FzZSAnPic6IGNhc2UgJz49JzogY2FzZSAnPD0nOlxuICAgICAgICBjYXNlICdpbic6IGNhc2UgJ2luc3RhbmNlb2YnOlxuICAgICAgICAgICAgcmV0dXJuIHRydWU7XG4gICAgfVxuICAgIHJldHVybiBmYWxzZTtcbn1cblxuLy8gVG8gcHJldmVudCByZWN1cnNpb24sXG4vLyB3ZSByZW1lbWJlciB0aGUgc3RhdHVzIHVzZWQgaW4gYWRkQ29uc3RyYWludHNcbmNvbnN0IHZpc2l0ZWRTdGF0dXMgPSBbXTtcbmNvbnN0IGNvbnN0cmFpbnRzID0gW107XG5mdW5jdGlvbiBjbGVhckNvbnN0cmFpbnRzKCkge1xuICAgIHZpc2l0ZWRTdGF0dXMubGVuZ3RoID0gMDtcbiAgICBjb25zdHJhaW50cy5sZW5ndGggPSAwO1xufVxuXG5sZXQgcnRDWDtcbmZ1bmN0aW9uIGFkZENvbnN0cmFpbnRzKGFzdCwgaW5pdFN0YXR1cywgbmV3UnRDWCkge1xuXG4gICAgLy8gc2V0IHJ0Q1hcbiAgICBydENYID0gbmV3UnRDWCB8fCBydENYO1xuICAgIGNvbnN0IMSIID0gcnRDWC7EiDtcblxuICAgIC8vIENoZWNrIHdoZXRoZXIgd2UgaGF2ZSBwcm9jZXNzZWQgJ2luaXRTdGF0dXMnIGJlZm9yZVxuICAgIGZvciAobGV0IGk9MDsgaSA8IHZpc2l0ZWRTdGF0dXMubGVuZ3RoOyBpKyspIHtcbiAgICAgICAgaWYgKGluaXRTdGF0dXMuZXF1YWxzKHZpc2l0ZWRTdGF0dXNbaV0pKSB7XG4gICAgICAgICAgICAgLy8gSWYgc28sIGRvIG5vdGhpbmdcbiAgICAgICAgICAgICAvLyBzaWduaWZ5aW5nIHdlIGRpZG4ndCBhZGQgY29uc3RyYWludHNcbiAgICAgICAgICAgICByZXR1cm4gZmFsc2U7XG4gICAgICAgICB9XG4gICAgfVxuICAgIC8vIElmIHRoZSBpbml0U3RhdHVzIGlzIG5ldywgcHVzaCBpdC5cbiAgICAvLyBXZSBkbyBub3QgcmVjb3JkIGFzdCBzaW5jZSBhc3Qgbm9kZSBkZXBlbmRzIG9uIHRoZSBzdGF0dXNcbiAgICB2aXNpdGVkU3RhdHVzLnB1c2goaW5pdFN0YXR1cyk7XG5cbiAgICBmdW5jdGlvbiByZWFkTWVtYmVyKG5vZGUsIGN1clN0YXR1cywgYykge1xuICAgICAgICBjb25zdCByZXQgPSDEiC5nZXQobm9kZSwgY3VyU3RhdHVzLmRlbHRhKTtcbiAgICAgICAgY29uc3Qgb2JqQVZhbCA9IGMobm9kZS5vYmplY3QsIGN1clN0YXR1cywgdW5kZWZpbmVkKTtcbiAgICAgICAgaWYgKG5vZGUucHJvcGVydHkudHlwZSAhPT0gJ0lkZW50aWZpZXInKSB7XG4gICAgICAgICAgICAvLyByZXR1cm4gZnJvbSBwcm9wZXJ0eSBpcyBpZ25vcmVkXG4gICAgICAgICAgICBjKG5vZGUucHJvcGVydHksIGN1clN0YXR1cywgdW5kZWZpbmVkKTtcbiAgICAgICAgfVxuICAgICAgICBjb25zdCBwcm9wQWNjID0gcHJvcEFjY2Vzcyhub2RlKTtcblxuICAgICAgICBjb25zdHJhaW50cy5wdXNoKHtPQko6IG9iakFWYWwsXG4gICAgICAgICAgICBQUk9QOiBwcm9wQWNjWzFdLFxuICAgICAgICAgICAgUkVBRF9UTzogcmV0fSk7XG4gICAgICAgIG9iakFWYWwucHJvcGFnYXRlKG5ldyBjc3RyLlJlYWRQcm9wKHByb3BBY2NbMV0sIHJldCkpO1xuXG4gICAgICAgIC8vIHJldHVybnMgQVZhbCBmb3IgcmVjZWl2ZXIgYW5kIHJlYWQgbWVtYmVyXG4gICAgICAgIHJldHVybiBbb2JqQVZhbCwgcmV0XTtcbiAgICB9XG5cbiAgICAvLyBjb25zdHJhaW50IGdlbmVyYXRpbmcgd2Fsa2VyIGZvciBleHByZXNzaW9uc1xuICAgIGNvbnN0IGNvbnN0cmFpbnRHZW5lcmF0b3IgPSB3YWxrLm1ha2Uoe1xuXG4gICAgICAgIElkZW50aWZpZXI6IGZ1bmN0aW9uIChub2RlLCBjdXJTdGF0dXMsIGMpIHtcbiAgICAgICAgICAgIGNvbnN0IGF2ID0gY3VyU3RhdHVzLnNjLmdldEFWYWxPZihub2RlLm5hbWUpO1xuICAgICAgICAgICAgLy8gdXNlIGF2YWwgaW4gdGhlIHNjb3BlXG4gICAgICAgICAgICDEiC5zZXQobm9kZSwgY3VyU3RhdHVzLmRlbHRhLCBhdik7XG4gICAgICAgICAgICByZXR1cm4gYXY7XG4gICAgICAgIH0sXG5cbiAgICAgICAgVGhpc0V4cHJlc3Npb246IGZ1bmN0aW9uIChub2RlLCBjdXJTdGF0dXMsIGMpIHtcbiAgICAgICAgICAgIGNvbnN0IGF2ID0gY3VyU3RhdHVzLnNlbGY7XG4gICAgICAgICAgICAvLyB1c2UgYXZhbCBmb3IgJ3RoaXMnXG4gICAgICAgICAgICDEiC5zZXQobm9kZSwgY3VyU3RhdHVzLmRlbHRhLCBhdik7XG4gICAgICAgICAgICByZXR1cm4gYXY7XG4gICAgICAgIH0sXG5cbiAgICAgICAgTGl0ZXJhbDogZnVuY3Rpb24gKG5vZGUsIGN1clN0YXR1cywgYykge1xuICAgICAgICAgICAgY29uc3QgcmVzID0gxIguZ2V0KG5vZGUsIGN1clN0YXR1cy5kZWx0YSk7XG4gICAgICAgICAgICBpZiAobm9kZS5yZWdleCkge1xuICAgICAgICAgICAgICAgIC8vIG5vdCBpbXBsZW1lbnRlZCB5ZXRcbiAgICAgICAgICAgICAgICAvLyB0aHJvdyBuZXcgRXJyb3IoJ3JlZ2V4IGxpdGVyYWwgaXMgbm90IGltcGxlbWVudGVkIHlldCcpO1xuICAgICAgICAgICAgICAgIHJldHVybiByZXM7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBzd2l0Y2ggKHR5cGVvZiBub2RlLnZhbHVlKSB7XG4gICAgICAgICAgICBjYXNlICdudW1iZXInOlxuICAgICAgICAgICAgICAgIGNvbnN0cmFpbnRzLnB1c2goe1RZUEU6IHR5cGVzLlByaW1OdW1iZXIsXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgSU5DTF9TRVQ6IHJlc30pO1xuICAgICAgICAgICAgICAgIHJlcy5hZGRUeXBlKHR5cGVzLlByaW1OdW1iZXIpO1xuICAgICAgICAgICAgICAgIGJyZWFrO1xuICAgICAgICAgICAgY2FzZSAnc3RyaW5nJzpcbiAgICAgICAgICAgICAgICBjb25zdHJhaW50cy5wdXNoKHtUWVBFOiB0eXBlcy5QcmltU3RyaW5nLFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIElOQ0xfU0VUOiByZXN9KTtcbiAgICAgICAgICAgICAgICByZXMuYWRkVHlwZSh0eXBlcy5QcmltU3RyaW5nKTtcbiAgICAgICAgICAgICAgICBicmVhaztcbiAgICAgICAgICAgIGNhc2UgJ2Jvb2xlYW4nOlxuICAgICAgICAgICAgICAgIGNvbnN0cmFpbnRzLnB1c2goe1RZUEU6IHR5cGVzLlByaW1Cb29sZWFuLFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIElOQ0xfU0VUOiByZXN9KTtcbiAgICAgICAgICAgICAgICByZXMuYWRkVHlwZSh0eXBlcy5QcmltQm9vbGVhbik7XG4gICAgICAgICAgICAgICAgYnJlYWs7XG4gICAgICAgICAgICBjYXNlICdvYmplY3QnOlxuICAgICAgICAgICAgICAgIC8vIEkgZ3Vlc3M6IExpdGVyYWwgJiYgb2JqZWN0ID09PiBub2RlLnZhbHVlID09IG51bGxcbiAgICAgICAgICAgICAgICAvLyBudWxsIGlzIGlnbm9yZWQsIHNvIG5vdGhpbmcgdG8gYWRkXG4gICAgICAgICAgICAgICAgYnJlYWs7XG4gICAgICAgICAgICBjYXNlICdmdW5jdGlvbic6XG4gICAgICAgICAgICAgICAgdGhyb3cgbmV3IEVycm9yKCdJIGd1ZXNzIGZ1bmN0aW9uIGlzIGltcG9zc2libGUgaGVyZS4nKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIHJldHVybiByZXM7XG4gICAgICAgIH0sXG5cbiAgICAgICAgQXNzaWdubWVudEV4cHJlc3Npb246IGZ1bmN0aW9uIChub2RlLCBjdXJTdGF0dXMsIGMpIHtcbiAgICAgICAgICAgIGNvbnN0IHJoc0FWYWwgPSBjKG5vZGUucmlnaHQsIGN1clN0YXR1cywgdW5kZWZpbmVkKTtcbiAgICAgICAgICAgIGlmIChub2RlLmxlZnQudHlwZSA9PT0gJ0lkZW50aWZpZXInKSB7XG4gICAgICAgICAgICAgICAgLy8gTEhTIGlzIGEgc2ltcGxlIHZhcmlhYmxlLlxuICAgICAgICAgICAgICAgIGNvbnN0IHZhck5hbWUgPSBub2RlLmxlZnQubmFtZTtcbiAgICAgICAgICAgICAgICBjb25zdCBsaHNBVmFsID0gY3VyU3RhdHVzLnNjLmdldEFWYWxPZih2YXJOYW1lKTtcbiAgICAgICAgICAgICAgICAvLyBsaHMgaXMgbm90IHZpc2l0ZWQuIE5lZWQgdG8gaGFuZGxlIGhlcmUuXG4gICAgICAgICAgICAgICAgLy8gVXNlIGF2YWwgZm91bmQgaW4gdGhlIHNjb3BlIGZvciBsaHNcbiAgICAgICAgICAgICAgICDEiC5zZXQobm9kZS5sZWZ0LCBjdXJTdGF0dXMuZGVsdGEsIGxoc0FWYWwpO1xuXG4gICAgICAgICAgICAgICAgaWYgKG5vZGUub3BlcmF0b3IgPT09ICc9Jykge1xuICAgICAgICAgICAgICAgICAgICAvLyBzaW1wbGUgYXNzaWdubWVudFxuICAgICAgICAgICAgICAgICAgICBjb25zdHJhaW50cy5wdXNoKHtcbiAgICAgICAgICAgICAgICAgICAgICAgIEZST006IHJoc0FWYWwsXG4gICAgICAgICAgICAgICAgICAgICAgICBUTzogbGhzQVZhbFxuICAgICAgICAgICAgICAgICAgICB9KTtcbiAgICAgICAgICAgICAgICAgICAgcmhzQVZhbC5wcm9wYWdhdGUobGhzQVZhbCk7XG4gICAgICAgICAgICAgICAgICAgIC8vIG5vZGUncyBBVmFsIGZyb20gUkhTXG4gICAgICAgICAgICAgICAgICAgIMSILnNldChub2RlLCBjdXJTdGF0dXMuZGVsdGEsIHJoc0FWYWwpO1xuICAgICAgICAgICAgICAgICAgICByZXR1cm4gcmhzQVZhbDtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgLy8gdXBkYXRpbmcgYXNzaWdubWVudFxuICAgICAgICAgICAgICAgIGNvbnN0IHJlc0FWYWwgPSDEiC5nZXQobm9kZSwgY3VyU3RhdHVzLmRlbHRhKTtcbiAgICAgICAgICAgICAgICBpZiAobm9kZS5vcGVyYXRvciA9PT0gJys9Jykge1xuICAgICAgICAgICAgICAgICAgICAvLyBjb25jYXRlbmF0aW5nIHVwZGF0ZVxuICAgICAgICAgICAgICAgICAgICBjb25zdHJhaW50cy5wdXNoKHtcbiAgICAgICAgICAgICAgICAgICAgICAgIEFERF9PUFJEMTogbGhzQVZhbCxcbiAgICAgICAgICAgICAgICAgICAgICAgIEFERF9PUFJEMjogcmhzQVZhbCxcbiAgICAgICAgICAgICAgICAgICAgICAgIFJFU1VMVDogcmVzQVZhbFxuICAgICAgICAgICAgICAgICAgICB9KTtcbiAgICAgICAgICAgICAgICAgICAgbGhzQVZhbC5wcm9wYWdhdGUobmV3IGNzdHIuSXNBZGRlZChyaHNBVmFsLCByZXNBVmFsKSk7XG4gICAgICAgICAgICAgICAgICAgIHJoc0FWYWwucHJvcGFnYXRlKG5ldyBjc3RyLklzQWRkZWQobGhzQVZhbCwgcmVzQVZhbCkpO1xuICAgICAgICAgICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgICAgICAgICAgIC8vIGFyaXRobWV0aWMgdXBkYXRlXG4gICAgICAgICAgICAgICAgICAgIGNvbnN0cmFpbnRzLnB1c2goe1xuICAgICAgICAgICAgICAgICAgICAgICAgVFlQRTp0eXBlcy5QcmltTnVtYmVyLFxuICAgICAgICAgICAgICAgICAgICAgICAgSU5DTF9TRVQ6IHJlc0FWYWxcbiAgICAgICAgICAgICAgICAgICAgfSk7XG4gICAgICAgICAgICAgICAgICAgIHJlc0FWYWwuYWRkVHlwZSh0eXBlcy5QcmltTnVtYmVyKTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgcmV0dXJuIHJlc0FWYWw7XG4gICAgICAgICAgICB9IGVsc2UgaWYgKG5vZGUubGVmdC50eXBlID09PSAnTWVtYmVyRXhwcmVzc2lvbicpIHtcbiAgICAgICAgICAgICAgICBjb25zdCBvYmpBVmFsID0gYyhub2RlLmxlZnQub2JqZWN0LCBjdXJTdGF0dXMsIHVuZGVmaW5lZCk7XG4gICAgICAgICAgICAgICAgY29uc3QgcHJvcEFjYyA9IHByb3BBY2Nlc3Mobm9kZS5sZWZ0KTtcbiAgICAgICAgICAgICAgICBpZiAobm9kZS5vcGVyYXRvciA9PT0gJz0nKSB7XG4gICAgICAgICAgICAgICAgICAgIC8vIGFzc2lnbm1lbnQgdG8gbWVtYmVyXG4gICAgICAgICAgICAgICAgICAgIGNvbnN0cmFpbnRzLnB1c2goe1xuICAgICAgICAgICAgICAgICAgICAgICAgT0JKOiBvYmpBVmFsLFxuICAgICAgICAgICAgICAgICAgICAgICAgUFJPUDogcHJvcEFjY1sxXSxcbiAgICAgICAgICAgICAgICAgICAgICAgIFdSSVRFX1dJVEg6IHJoc0FWYWxcbiAgICAgICAgICAgICAgICAgICAgfSk7XG4gICAgICAgICAgICAgICAgICAgIG9iakFWYWwucHJvcGFnYXRlKG5ldyBjc3RyLldyaXRlUHJvcChwcm9wQWNjWzFdLCByaHNBVmFsKSk7XG4gICAgICAgICAgICAgICAgICAgIC8vIGlmIHByb3BlcnR5IGlzIG51bWJlciBsaXRlcmFsLCBhbHNvIHdyaXRlIHRvICd1bmtub3duJ1xuICAgICAgICAgICAgICAgICAgICBpZiAocHJvcEFjY1swXSA9PT0gJ251bWJlckxpdGVyYWwnKSB7XG4gICAgICAgICAgICAgICAgICAgICAgICBvYmpBVmFsLnByb3BhZ2F0ZShuZXcgY3N0ci5Xcml0ZVByb3AobnVsbCwgcmhzQVZhbCkpO1xuICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgIC8vIG5vZGUncyBBVmFsIGZyb20gUkhTXG4gICAgICAgICAgICAgICAgICAgIMSILnNldChub2RlLCBjdXJTdGF0dXMuZGVsdGEsIHJoc0FWYWwpO1xuICAgICAgICAgICAgICAgICAgICByZXR1cm4gcmhzQVZhbDtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgLy8gdXBkYXRpbmcgYXNzaWdubWVudFxuICAgICAgICAgICAgICAgIGNvbnN0IHJlc0FWYWwgPSDEiC5nZXQobm9kZSwgY3VyU3RhdHVzLmRlbHRhKTtcbiAgICAgICAgICAgICAgICBjb25zdCByZWN2QW5kUmV0ID0gcmVhZE1lbWJlcihub2RlLmxlZnQsIGN1clN0YXR1cywgYyk7XG4gICAgICAgICAgICAgICAgaWYgKG5vZGUub3BlcmF0b3IgPT09ICcrPScpIHtcbiAgICAgICAgICAgICAgICAgICAgLy8gY29uY2F0ZW5hdGluZyB1cGRhdGVcbiAgICAgICAgICAgICAgICAgICAgY29uc3RyYWludHMucHVzaCh7XG4gICAgICAgICAgICAgICAgICAgICAgICBBRERfT1BSRDE6IHJlY3ZBbmRSZXRbMV0sXG4gICAgICAgICAgICAgICAgICAgICAgICBBRERfT1BSRDI6IHJoc0FWYWwsXG4gICAgICAgICAgICAgICAgICAgICAgICBSRVNVTFQ6IHJlc0FWYWxcbiAgICAgICAgICAgICAgICAgICAgfSk7XG4gICAgICAgICAgICAgICAgICAgIHJlY3ZBbmRSZXRbMV0ucHJvcGFnYXRlKG5ldyBjc3RyLklzQWRkZWQocmhzQVZhbCwgcmVzQVZhbCkpO1xuICAgICAgICAgICAgICAgICAgICByaHNBVmFsLnByb3BhZ2F0ZShuZXcgY3N0ci5Jc0FkZGVkKHJlY3ZBbmRSZXRbMV0sIHJlc0FWYWwpKTtcbiAgICAgICAgICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgICAgICAgICAgICAvLyBhcml0aG1ldGljIHVwZGF0ZVxuICAgICAgICAgICAgICAgICAgICBjb25zdHJhaW50cy5wdXNoKHtcbiAgICAgICAgICAgICAgICAgICAgICAgIFRZUEU6IHR5cGVzLlByaW1OdW1iZXIsXG4gICAgICAgICAgICAgICAgICAgICAgICBJTkNMX1NFVDogcmVzQVZhbFxuICAgICAgICAgICAgICAgICAgICB9KTtcbiAgICAgICAgICAgICAgICAgICAgcmVzQVZhbC5hZGRUeXBlKHR5cGVzLlByaW1OdW1iZXIpO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICByZXR1cm4gcmVzQVZhbDtcbiAgICAgICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgICAgICAgY29uc29sZS5pbmZvKCdBc3NpZ25tZW50IHVzaW5nIHBhdHRlcm4gaXMgbm90IGltcGxlbWVudGVkJyk7XG4gICAgICAgICAgICB9XG4gICAgICAgIH0sXG5cbiAgICAgICAgVmFyaWFibGVEZWNsYXJhdGlvbjogZnVuY3Rpb24gKG5vZGUsIGN1clN0YXR1cywgYykge1xuICAgICAgICAgICAgZm9yIChsZXQgaSA9IDA7IGkgPCBub2RlLmRlY2xhcmF0aW9ucy5sZW5ndGg7IGkrKykge1xuICAgICAgICAgICAgICAgIGNvbnN0IGRlY2wgPSBub2RlLmRlY2xhcmF0aW9uc1tpXTtcbiAgICAgICAgICAgICAgICBjb25zdCBsaHNBVmFsID0gY3VyU3RhdHVzLnNjLmdldEFWYWxPZihkZWNsLmlkLm5hbWUpO1xuICAgICAgICAgICAgICAgIC8vIGRlY2xhcmVkIHZhciBub2RlIGlzICdpZCdcbiAgICAgICAgICAgICAgICDEiC5zZXQoZGVjbC5pZCwgY3VyU3RhdHVzLmRlbHRhLCBsaHNBVmFsKTtcbiAgICAgICAgICAgICAgICBpZiAoZGVjbC5pbml0KSB7XG4gICAgICAgICAgICAgICAgICAgIGNvbnN0IHJoc0FWYWwgPSBjKGRlY2wuaW5pdCwgY3VyU3RhdHVzLCB1bmRlZmluZWQpO1xuICAgICAgICAgICAgICAgICAgICDEiC5zZXQoZGVjbC5pbml0LCBjdXJTdGF0dXMuZGVsdGEsIHJoc0FWYWwpO1xuICAgICAgICAgICAgICAgICAgICBjb25zdHJhaW50cy5wdXNoKHtGUk9NOiByaHNBVmFsLFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBUTzogbGhzQVZhbH0pO1xuICAgICAgICAgICAgICAgICAgICByaHNBVmFsLnByb3BhZ2F0ZShsaHNBVmFsKTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICB9XG4gICAgICAgIH0sXG5cbiAgICAgICAgTG9naWNhbEV4cHJlc3Npb246IGZ1bmN0aW9uIChub2RlLCBjdXJTdGF0dXMsIGMpIHtcbiAgICAgICAgICAgIGNvbnN0IHJlcyA9IMSILmdldChub2RlLCBjdXJTdGF0dXMuZGVsdGEpO1xuICAgICAgICAgICAgY29uc3QgbGVmdCA9IGMobm9kZS5sZWZ0LCBjdXJTdGF0dXMsIHVuZGVmaW5lZCk7XG4gICAgICAgICAgICBjb25zdCByaWdodCA9IGMobm9kZS5yaWdodCwgY3VyU3RhdHVzLCB1bmRlZmluZWQpO1xuICAgICAgICAgICAgY29uc3RyYWludHMucHVzaCh7RlJPTTogbGVmdCwgVE86IHJlc30sXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgIHtGUk9NOiByaWdodCwgVE86IHJlc30pO1xuICAgICAgICAgICAgbGVmdC5wcm9wYWdhdGUocmVzKTtcbiAgICAgICAgICAgIHJpZ2h0LnByb3BhZ2F0ZShyZXMpO1xuICAgICAgICAgICAgcmV0dXJuIHJlcztcbiAgICAgICAgfSxcblxuICAgICAgICBDb25kaXRpb25hbEV4cHJlc3Npb246IGZ1bmN0aW9uIChub2RlLCBjdXJTdGF0dXMsIGMpIHtcbiAgICAgICAgICAgIGNvbnN0IHJlcyA9IMSILmdldChub2RlLCBjdXJTdGF0dXMuZGVsdGEpO1xuICAgICAgICAgICAgYyhub2RlLnRlc3QsIGN1clN0YXR1cywgdW5kZWZpbmVkKTtcbiAgICAgICAgICAgIGNvbnN0IGNvbnMgPSBjKG5vZGUuY29uc2VxdWVudCwgY3VyU3RhdHVzLCB1bmRlZmluZWQpO1xuICAgICAgICAgICAgY29uc3QgYWx0ID0gYyhub2RlLmFsdGVybmF0ZSwgY3VyU3RhdHVzLCB1bmRlZmluZWQpO1xuICAgICAgICAgICAgY29uc3RyYWludHMucHVzaCh7RlJPTTogY29ucywgVE86IHJlc30sXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgIHtGUk9NOiBhbHQsIFRPOiByZXN9KTtcbiAgICAgICAgICAgIGNvbnMucHJvcGFnYXRlKHJlcyk7XG4gICAgICAgICAgICBhbHQucHJvcGFnYXRlKHJlcyk7XG4gICAgICAgICAgICByZXR1cm4gcmVzO1xuICAgICAgICB9LFxuXG4gICAgICAgIE5ld0V4cHJlc3Npb246IGZ1bmN0aW9uIChub2RlLCBjdXJTdGF0dXMsIGMpIHtcbiAgICAgICAgICAgIGNvbnN0IHJldCA9IMSILmdldChub2RlLCBjdXJTdGF0dXMuZGVsdGEpO1xuICAgICAgICAgICAgY29uc3QgY2FsbGVlID0gYyhub2RlLmNhbGxlZSwgY3VyU3RhdHVzLCB1bmRlZmluZWQpO1xuICAgICAgICAgICAgY29uc3QgYXJncyA9IFtdO1xuICAgICAgICAgICAgZm9yIChsZXQgaSA9IDA7IGkgPCBub2RlLmFyZ3VtZW50cy5sZW5ndGg7IGkrKykge1xuICAgICAgICAgICAgICAgIGFyZ3MucHVzaChjKG5vZGUuYXJndW1lbnRzW2ldLCBjdXJTdGF0dXMsIHVuZGVmaW5lZCkpO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgY29uc3QgbmV3RGVsdGEgPSBjdXJTdGF0dXMuZGVsdGEuYXBwZW5kT25lKG5vZGVbJ0BsYWJlbCddKTtcbiAgICAgICAgICAgIGNvbnN0cmFpbnRzLnB1c2goe0NPTlNUUlVDVE9SOiBjYWxsZWUsXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICBBUkdTOiBhcmdzLFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgUkVUOiByZXQsXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICBFWEM6IGN1clN0YXR1cy5leGMsXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICBERUxUQTogbmV3RGVsdGF9KTtcbiAgICAgICAgICAgIGNhbGxlZS5wcm9wYWdhdGUoXG4gICAgICAgICAgICAgICAgbmV3IGNzdHIuSXNDdG9yKFxuICAgICAgICAgICAgICAgICAgICBhcmdzLFxuICAgICAgICAgICAgICAgICAgICByZXQsXG4gICAgICAgICAgICAgICAgICAgIGN1clN0YXR1cy5leGMsXG4gICAgICAgICAgICAgICAgICAgIG5ld0RlbHRhKSk7XG4gICAgICAgICAgICByZXR1cm4gcmV0O1xuICAgICAgICB9LFxuXG4gICAgICAgIEFycmF5RXhwcmVzc2lvbjogZnVuY3Rpb24gKG5vZGUsIGN1clN0YXR1cywgYykge1xuICAgICAgICAgICAgY29uc3QgcmV0ID0gxIguZ2V0KG5vZGUsIGN1clN0YXR1cy5kZWx0YSk7XG4gICAgICAgICAgICAvLyBOT1RFIHByb3RvdHlwZSBvYmplY3QgaXMgbm90IHJlY29yZGVkIGluIMSIXG4gICAgICAgICAgICBjb25zdCBhcnJUeXBlID0gbmV3IHR5cGVzLkFyclR5cGUobmV3IHR5cGVzLkFWYWwocnRDWC5wcm90b3MuQXJyYXkpKTtcbiAgICAgICAgICAgIC8vIGFkZCBsZW5ndGggcHJvcGVydHlcbiAgICAgICAgICAgIGFyclR5cGUuZ2V0UHJvcCgnbGVuZ3RoJykuYWRkVHlwZSh0eXBlcy5QcmltTnVtYmVyKTtcblxuICAgICAgICAgICAgY29uc3RyYWludHMucHVzaCh7VFlQRTogYXJyVHlwZSwgSU5DTF9TRVQ6IHJldH0pO1xuICAgICAgICAgICAgcmV0LmFkZFR5cGUoYXJyVHlwZSk7XG5cbiAgICAgICAgICAgIC8vIGFkZCBhcnJheSBlbGVtZW50c1xuICAgICAgICAgICAgZm9yIChsZXQgaSA9IDA7IGkgPCBub2RlLmVsZW1lbnRzLmxlbmd0aDsgaSsrKSB7XG4gICAgICAgICAgICAgICAgY29uc3QgZWx0QVZhbCA9IGMobm9kZS5lbGVtZW50c1tpXSwgY3VyU3RhdHVzLCB1bmRlZmluZWQpO1xuXG4gICAgICAgICAgICAgICAgY29uc3QgcHJvcCA9IGkgKyAnJztcbiAgICAgICAgICAgICAgICBjb25zdHJhaW50cy5wdXNoKHtPQko6IHJldCwgUFJPUDogcHJvcCwgQVZBTDogZWx0QVZhbH0pO1xuICAgICAgICAgICAgICAgIGNvbnN0cmFpbnRzLnB1c2goe09CSjogcmV0LCBQUk9QOiBudWxsLCBBVkFMOiBlbHRBVmFsfSk7XG4gICAgICAgICAgICAgICAgcmV0LnByb3BhZ2F0ZShuZXcgY3N0ci5Xcml0ZVByb3AocHJvcCwgZWx0QVZhbCkpO1xuICAgICAgICAgICAgICAgIHJldC5wcm9wYWdhdGUobmV3IGNzdHIuV3JpdGVQcm9wKG51bGwsIGVsdEFWYWwpKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIHJldHVybiByZXQ7XG4gICAgICAgIH0sXG5cbiAgICAgICAgT2JqZWN0RXhwcmVzc2lvbjogZnVuY3Rpb24gKG5vZGUsIGN1clN0YXR1cywgYykge1xuICAgICAgICAgICAgY29uc3QgcmV0ID0gxIguZ2V0KG5vZGUsIGN1clN0YXR1cy5kZWx0YSk7XG4gICAgICAgICAgICAvLyBOT1RFIHByb3RvdHlwZSBvYmplY3QgaXMgbm90IHJlY29yZGVkIGluIMSIXG4gICAgICAgICAgICBjb25zdCBvYmpUeXBlID0gbmV3IHR5cGVzLk9ialR5cGUobmV3IHR5cGVzLkFWYWwocnRDWC5wcm90b3MuT2JqZWN0KSk7XG4gICAgICAgICAgICBjb25zdHJhaW50cy5wdXNoKHtUWVBFOiBvYmpUeXBlLCBJTkNMX1NFVDogcmV0fSk7XG4gICAgICAgICAgICByZXQuYWRkVHlwZShvYmpUeXBlKTtcblxuICAgICAgICAgICAgZm9yIChsZXQgaSA9IDA7IGkgPCBub2RlLnByb3BlcnRpZXMubGVuZ3RoOyBpKyspIHtcbiAgICAgICAgICAgICAgICBjb25zdCBwcm9wUGFpciA9IG5vZGUucHJvcGVydGllc1tpXTtcbiAgICAgICAgICAgICAgICBjb25zdCBwcm9wS2V5ID0gcHJvcFBhaXIua2V5O1xuICAgICAgICAgICAgICAgIGxldCBuYW1lO1xuICAgICAgICAgICAgICAgIGNvbnN0IHByb3BFeHByID0gcHJvcFBhaXIudmFsdWU7XG5cbiAgICAgICAgICAgICAgICBjb25zdCBmbGRBVmFsID0gYyhwcm9wRXhwciwgY3VyU3RhdHVzLCB1bmRlZmluZWQpO1xuXG4gICAgICAgICAgICAgICAgaWYgKHByb3BLZXkudHlwZSA9PT0gJ0lkZW50aWZpZXInKSB7XG4gICAgICAgICAgICAgICAgICAgIG5hbWUgPSBwcm9wS2V5Lm5hbWU7XG4gICAgICAgICAgICAgICAgfSBlbHNlIGlmICh0eXBlb2YgcHJvcEtleS52YWx1ZSA9PT0gJ3N0cmluZycpIHtcbiAgICAgICAgICAgICAgICAgICAgbmFtZSA9IHByb3BLZXkudmFsdWU7XG4gICAgICAgICAgICAgICAgfSBlbHNlIGlmICh0eXBlb2YgcHJvcEtleS52YWx1ZSA9PT0gJ251bWJlcicpIHtcbiAgICAgICAgICAgICAgICAgICAgLy8gY29udmVydCBudW1iZXIgdG8gc3RyaW5nXG4gICAgICAgICAgICAgICAgICAgIG5hbWUgPSBwcm9wS2V5LnZhbHVlICsgJyc7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIGNvbnN0cmFpbnRzLnB1c2goe09CSjogcmV0LCBQUk9QOiBuYW1lLCBBVkFMOiBmbGRBVmFsfSk7XG4gICAgICAgICAgICAgICAgcmV0LnByb3BhZ2F0ZShuZXcgY3N0ci5Xcml0ZVByb3AobmFtZSwgZmxkQVZhbCkpO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgcmV0dXJuIHJldDtcbiAgICAgICAgfSxcblxuICAgICAgICBGdW5jdGlvbkV4cHJlc3Npb246IGZ1bmN0aW9uIChub2RlLCBjdXJTdGF0dXMsIGMpIHtcbiAgICAgICAgICAgIGlmICghbm9kZS5mbkluc3RhbmNlcykge1xuICAgICAgICAgICAgICAgIG5vZGUuZm5JbnN0YW5jZXMgPSBbXTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGxldCBmbkluc3RhbmNlID0gbnVsbDtcbiAgICAgICAgICAgIG5vZGUuZm5JbnN0YW5jZXMuZm9yRWFjaChmdW5jdGlvbiAoZm5UeXBlKSB7XG4gICAgICAgICAgICAgICAgaWYgKGZuVHlwZS5zYyA9PT0gY3VyU3RhdHVzLnNjKSB7XG4gICAgICAgICAgICAgICAgICAgIGZuSW5zdGFuY2UgPSBmblR5cGU7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgfSk7XG4gICAgICAgICAgICBpZiAoIWZuSW5zdGFuY2UpIHtcbiAgICAgICAgICAgICAgICAvLyBOT1RFIHByb3RvdHlwZSBvYmplY3QgaXMgbm90IHJlY29yZGVkIGluIMSIXG4gICAgICAgICAgICAgICAgZm5JbnN0YW5jZVxuICAgICAgICAgICAgICAgICAgICA9IG5ldyB0eXBlcy5GblR5cGUobmV3IHR5cGVzLkFWYWwocnRDWC5wcm90b3MuRnVuY3Rpb24pLFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgJ1thbm9ueW1vdXMgZnVuY3Rpb25dJyxcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIG5vZGUuYm9keVsnQGJsb2NrJ10uZ2V0UGFyYW1WYXJOYW1lcygpLFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgY3VyU3RhdHVzLnNjLFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgbm9kZSxcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIHJ0Q1gucHJvdG9zLk9iamVjdCk7XG4gICAgICAgICAgICAgICAgbm9kZS5mbkluc3RhbmNlcy5wdXNoKGZuSW5zdGFuY2UpO1xuICAgICAgICAgICAgICAgIC8vIE5PVEUgcHJvdG90eXBlIG9iamVjdCBpcyBub3QgcmVjb3JkZWQgaW4gxIhcbiAgICAgICAgICAgICAgICBjb25zdCBwcm90b3R5cGVPYmplY3QgPVxuICAgICAgICAgICAgICAgICAgICBuZXcgdHlwZXMuT2JqVHlwZShuZXcgdHlwZXMuQVZhbChydENYLnByb3Rvcy5PYmplY3QpLFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAnPy5wcm90b3R5cGUnKTtcbiAgICAgICAgICAgICAgICAvLyBGb3IgLnByb3RvdHlwZVxuICAgICAgICAgICAgICAgIGNvbnN0IHByb3RvdHlwZVByb3AgPSBmbkluc3RhbmNlLmdldFByb3AoJ3Byb3RvdHlwZScpO1xuICAgICAgICAgICAgICAgIGNvbnN0cmFpbnRzLnB1c2goe1RZUEU6IHByb3RvdHlwZU9iamVjdCxcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBJTkNMX1NFVDogcHJvdG90eXBlUHJvcH0pO1xuICAgICAgICAgICAgICAgIHByb3RvdHlwZVByb3AuYWRkVHlwZShwcm90b3R5cGVPYmplY3QpO1xuICAgICAgICAgICAgICAgIC8vIEZvciAucHJvdG90eXBlLmNvbnN0cnVjdG9yXG4gICAgICAgICAgICAgICAgY29uc3QgY29uc3RydWN0b3JQcm9wID0gcHJvdG90eXBlT2JqZWN0LmdldFByb3AoJ2NvbnN0cnVjdG9yJyk7XG4gICAgICAgICAgICAgICAgY29uc3RyYWludHMucHVzaCh7VFlQRTogZm5JbnN0YW5jZSxcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBJTkNMX1NFVDogY29uc3RydWN0b3JQcm9wfSk7XG4gICAgICAgICAgICAgICAgY29uc3RydWN0b3JQcm9wLmFkZFR5cGUoZm5JbnN0YW5jZSk7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBjb25zdCByZXQgPSDEiC5nZXQobm9kZSwgY3VyU3RhdHVzLmRlbHRhKTtcbiAgICAgICAgICAgIGNvbnN0cmFpbnRzLnB1c2goe1RZUEU6IGZuSW5zdGFuY2UsXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICBJTkNMX1NFVDogcmV0fSk7XG4gICAgICAgICAgICByZXQuYWRkVHlwZShmbkluc3RhbmNlKTtcbiAgICAgICAgICAgIHJldHVybiByZXQ7XG4gICAgICAgIH0sXG5cbiAgICAgICAgRnVuY3Rpb25EZWNsYXJhdGlvbjogZnVuY3Rpb24gKG5vZGUsIGN1clN0YXR1cywgYykge1xuICAgICAgICAgICAgLy8gRHJvcCBpbml0aWFsIGNhdGNoIHNjb3Blc1xuICAgICAgICAgICAgY29uc3Qgc2MwID0gY3VyU3RhdHVzLnNjLnJlbW92ZUluaXRpYWxDYXRjaEJsb2NrcygpO1xuICAgICAgICAgICAgaWYgKCFub2RlLmZuSW5zdGFuY2VzKSB7XG4gICAgICAgICAgICAgICAgbm9kZS5mbkluc3RhbmNlcyA9IFtdO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgbGV0IGZuSW5zdGFuY2UgPSBudWxsO1xuICAgICAgICAgICAgbm9kZS5mbkluc3RhbmNlcy5mb3JFYWNoKGZ1bmN0aW9uIChmblR5cGUpIHtcbiAgICAgICAgICAgICAgICBpZiAoZm5UeXBlLnNjID09PSBzYzApIHtcbiAgICAgICAgICAgICAgICAgICAgZm5JbnN0YW5jZSA9IGZuVHlwZTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICB9KTtcbiAgICAgICAgICAgIGlmICghZm5JbnN0YW5jZSkge1xuICAgICAgICAgICAgICAgIC8vIE5PVEUgcHJvdG90eXBlIG9iamVjdCBpcyBub3QgcmVjb3JkZWQgaW4gxIhcbiAgICAgICAgICAgICAgICBmbkluc3RhbmNlXG4gICAgICAgICAgICAgICAgICAgID0gbmV3IHR5cGVzLkZuVHlwZShuZXcgdHlwZXMuQVZhbChydENYLnByb3Rvcy5GdW5jdGlvbiksXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBub2RlLmlkLm5hbWUsXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBub2RlLmJvZHlbJ0BibG9jayddLmdldFBhcmFtVmFyTmFtZXMoKSxcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIHNjMCxcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIG5vZGUsXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBydENYLnByb3Rvcy5PYmplY3QpO1xuICAgICAgICAgICAgICAgIG5vZGUuZm5JbnN0YW5jZXMucHVzaChmbkluc3RhbmNlKTtcbiAgICAgICAgICAgICAgICAvLyBmb3IgZWFjaCBmbkluc3RhbmNlLCBhc3NpZ24gb25lIHByb3RvdHlwZSBvYmplY3RcbiAgICAgICAgICAgICAgICAvLyBOT1RFIHByb3RvdHlwZSBvYmplY3QgaXMgbm90IHJlY29yZGVkIGluIMSIXG4gICAgICAgICAgICAgICAgY29uc3QgcHJvdG90eXBlT2JqZWN0ID1cbiAgICAgICAgICAgICAgICAgICAgbmV3IHR5cGVzLk9ialR5cGUobmV3IHR5cGVzLkFWYWwocnRDWC5wcm90b3MuT2JqZWN0KSxcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgbm9kZS5pZC5uYW1lICsgJy5wcm90b3R5cGUnKTtcbiAgICAgICAgICAgICAgICAvLyBGb3IgLnByb3RvdHlwZVxuICAgICAgICAgICAgICAgIGNvbnN0IHByb3RvdHlwZVByb3AgPSBmbkluc3RhbmNlLmdldFByb3AoJ3Byb3RvdHlwZScpO1xuICAgICAgICAgICAgICAgIGNvbnN0cmFpbnRzLnB1c2goe1RZUEU6IHByb3RvdHlwZU9iamVjdCxcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBJTkNMX1NFVDogcHJvdG90eXBlUHJvcH0pO1xuICAgICAgICAgICAgICAgIHByb3RvdHlwZVByb3AuYWRkVHlwZShwcm90b3R5cGVPYmplY3QpO1xuICAgICAgICAgICAgICAgIC8vIEZvciAucHJvdG90eXBlLmNvbnN0cnVjdG9yXG4gICAgICAgICAgICAgICAgY29uc3QgY29uc3RydWN0b3JQcm9wID0gcHJvdG90eXBlT2JqZWN0LmdldFByb3AoJ2NvbnN0cnVjdG9yJyk7XG4gICAgICAgICAgICAgICAgY29uc3RyYWludHMucHVzaCh7VFlQRTogZm5JbnN0YW5jZSxcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBJTkNMX1NFVDogY29uc3RydWN0b3JQcm9wfSk7XG4gICAgICAgICAgICAgICAgY29uc3RydWN0b3JQcm9wLmFkZFR5cGUoZm5JbnN0YW5jZSk7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBjb25zdCBsaHNBVmFsID0gc2MwLmdldEFWYWxPZihub2RlLmlkLm5hbWUpO1xuICAgICAgICAgICAgLy8gdXNlIGF2YWwgaW4gdGhlIHNjb3BlIGZvciBmdW5jdGlvbiBkZWNsYXJhdGlvblxuICAgICAgICAgICAgxIguc2V0KG5vZGUsIGN1clN0YXR1cy5kZWx0YSwgbGhzQVZhbCk7XG5cbiAgICAgICAgICAgIGNvbnN0cmFpbnRzLnB1c2goe1RZUEU6IGZuSW5zdGFuY2UsXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICBJTkNMX1NFVDogbGhzQVZhbH0pO1xuICAgICAgICAgICAgbGhzQVZhbC5hZGRUeXBlKGZuSW5zdGFuY2UpO1xuICAgICAgICAgICAgLy8gbm90aGluZyB0byByZXR1cm5cbiAgICAgICAgICAgIHJldHVybiB0eXBlcy5BVmFsTnVsbDtcbiAgICAgICAgfSxcblxuICAgICAgICBTZXF1ZW5jZUV4cHJlc3Npb246IGZ1bmN0aW9uIChub2RlLCBjdXJTdGF0dXMsIGMpIHtcbiAgICAgICAgICAgIGNvbnN0IGxhc3RJbmRleCA9IG5vZGUuZXhwcmVzc2lvbnMubGVuZ3RoIC0gMTtcbiAgICAgICAgICAgIGZvciAobGV0IGkgPSAwOyBpIDwgbGFzdEluZGV4OyBpKyspIHtcbiAgICAgICAgICAgICAgICBjKG5vZGUuZXhwcmVzc2lvbnNbaV0sIGN1clN0YXR1cywgdW5kZWZpbmVkKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGNvbnN0IGxhc3RBVmFsID0gYyhub2RlLmV4cHJlc3Npb25zW2xhc3RJbmRleF0sIGN1clN0YXR1cywgdW5kZWZpbmVkKTtcbiAgICAgICAgICAgIMSILnNldChub2RlLCBjdXJTdGF0dXMuZGVsdGEsIGxhc3RBVmFsKTtcbiAgICAgICAgICAgIHJldHVybiBsYXN0QVZhbDtcbiAgICAgICAgfSxcblxuICAgICAgICBVbmFyeUV4cHJlc3Npb246IGZ1bmN0aW9uIChub2RlLCBjdXJTdGF0dXMsIGMpIHtcbiAgICAgICAgICAgIGMobm9kZS5hcmd1bWVudCwgY3VyU3RhdHVzLCB1bmRlZmluZWQpO1xuICAgICAgICAgICAgY29uc3QgcmVzID0gxIguZ2V0KG5vZGUsIGN1clN0YXR1cy5kZWx0YSk7XG4gICAgICAgICAgICBjb25zdCB0eXBlID0gdW5vcFJlc3VsdFR5cGUobm9kZS5vcGVyYXRvcik7XG4gICAgICAgICAgICBpZiAodHlwZSkge1xuICAgICAgICAgICAgICAgIGNvbnN0cmFpbnRzLnB1c2goe1RZUEU6IHR5cGUsXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgSU5DTF9TRVQ6IHJlc30pO1xuICAgICAgICAgICAgICAgIHJlcy5hZGRUeXBlKHR5cGUpO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgcmV0dXJuIHJlcztcbiAgICAgICAgfSxcblxuICAgICAgICBVcGRhdGVFeHByZXNzaW9uOiBmdW5jdGlvbiAobm9kZSwgY3VyU3RhdHVzLCBjKSB7XG4gICAgICAgICAgICBjKG5vZGUuYXJndW1lbnQsIGN1clN0YXR1cywgdW5kZWZpbmVkKTtcbiAgICAgICAgICAgIGNvbnN0IHJlcyA9IMSILmdldChub2RlLCBjdXJTdGF0dXMuZGVsdGEpO1xuICAgICAgICAgICAgY29uc3RyYWludHMucHVzaCh7VFlQRTogdHlwZXMuUHJpbU51bWJlcixcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIElOQ0xfU0VUOiByZXN9KTtcbiAgICAgICAgICAgIHJlcy5hZGRUeXBlKHR5cGVzLlByaW1OdW1iZXIpO1xuICAgICAgICAgICAgLy8gV2UgaWdub3JlIHRoZSBlZmZlY3Qgb2YgdXBkYXRpbmcgdG8gbnVtYmVyIHR5cGVcbiAgICAgICAgICAgIHJldHVybiByZXM7XG4gICAgICAgIH0sXG5cbiAgICAgICAgQmluYXJ5RXhwcmVzc2lvbjogZnVuY3Rpb24gKG5vZGUsIGN1clN0YXR1cywgYykge1xuICAgICAgICAgICAgY29uc3QgbE9wcmQgPSBjKG5vZGUubGVmdCwgY3VyU3RhdHVzLCB1bmRlZmluZWQpO1xuICAgICAgICAgICAgY29uc3Qgck9wcmQgPSBjKG5vZGUucmlnaHQsIGN1clN0YXR1cywgdW5kZWZpbmVkKTtcbiAgICAgICAgICAgIGNvbnN0IHJlcyA9IMSILmdldChub2RlLCBjdXJTdGF0dXMuZGVsdGEpO1xuXG4gICAgICAgICAgICBpZiAobm9kZS5vcGVyYXRvciA9PSAnKycpIHtcbiAgICAgICAgICAgICAgICBjb25zdHJhaW50cy5wdXNoKHtBRERfT1BSRDE6IGxPcHJkLFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIEFERF9PUFJEMjogck9wcmQsXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgUkVTVUxUOiByZXMgfSk7XG4gICAgICAgICAgICAgICAgbE9wcmQucHJvcGFnYXRlKG5ldyBjc3RyLklzQWRkZWQock9wcmQsIHJlcykpO1xuICAgICAgICAgICAgICAgIHJPcHJkLnByb3BhZ2F0ZShuZXcgY3N0ci5Jc0FkZGVkKGxPcHJkLCByZXMpKTtcbiAgICAgICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgICAgICAgaWYgKGJpbm9wSXNCb29sZWFuKG5vZGUub3BlcmF0b3IpKSB7XG4gICAgICAgICAgICAgICAgICAgIGNvbnN0cmFpbnRzLnB1c2goe1RZUEU6IHR5cGVzLlByaW1Cb29sZWFuLFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBJTkNMX1NFVDogcmVzfSk7XG4gICAgICAgICAgICAgICAgICAgIHJlcy5hZGRUeXBlKHR5cGVzLlByaW1Cb29sZWFuKTtcbiAgICAgICAgICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgICAgICAgICAgICBjb25zdHJhaW50cy5wdXNoKHtUWVBFOiB0eXBlcy5QcmltTnVtYmVyLFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBJTkNMX1NFVDogcmVzfSk7XG4gICAgICAgICAgICAgICAgICAgIHJlcy5hZGRUeXBlKHR5cGVzLlByaW1OdW1iZXIpO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIHJldHVybiByZXM7XG4gICAgICAgIH0sXG5cbiAgICAgICAgVHJ5U3RhdGVtZW50OiBmdW5jdGlvbiAobm9kZSwgY3VyU3RhdHVzLCBjKSB7XG4gICAgICAgICAgICAvLyBjb25zdHJ1Y3Qgc2NvcGUgY2hhaW4gZm9yIGNhdGNoIGJsb2NrXG4gICAgICAgICAgICBjb25zdCBjYXRjaEJsb2NrU0MgPVxuICAgICAgICAgICAgICAgIG5vZGUuaGFuZGxlci5ib2R5WydAYmxvY2snXVxuICAgICAgICAgICAgICAgIC5nZXRTY29wZUluc3RhbmNlKGN1clN0YXR1cy5zYywgY3VyU3RhdHVzLmRlbHRhKTtcbiAgICAgICAgICAgIC8vIGdldCB0aGUgQVZhbCBmb3IgZXhjZXB0aW9uIHBhcmFtZXRlclxuICAgICAgICAgICAgY29uc3QgZXhjQVZhbCA9IGNhdGNoQmxvY2tTQy5nZXRBVmFsT2Yobm9kZS5oYW5kbGVyLnBhcmFtLm5hbWUpO1xuXG4gICAgICAgICAgICAvLyBmb3IgdHJ5IGJsb2NrXG4gICAgICAgICAgICBjb25zdCB0cnlTdGF0dXMgPSBjaGFuZ2VkU3RhdHVzKGN1clN0YXR1cywgJ2V4YycsIGV4Y0FWYWwpO1xuICAgICAgICAgICAgYyhub2RlLmJsb2NrLCB0cnlTdGF0dXMsIHVuZGVmaW5lZCk7XG5cbiAgICAgICAgICAgIC8vIGZvciBjYXRjaCBibG9ja1xuICAgICAgICAgICAgY29uc3QgY2F0Y2hTdGF0dXMgPSBjaGFuZ2VkU3RhdHVzKGN1clN0YXR1cywgJ3NjJywgY2F0Y2hCbG9ja1NDKTtcbiAgICAgICAgICAgIGMobm9kZS5oYW5kbGVyLmJvZHksIGNhdGNoU3RhdHVzLCB1bmRlZmluZWQpO1xuXG4gICAgICAgICAgICAvLyBmb3IgZmluYWxseSBibG9ja1xuICAgICAgICAgICAgaWYgKG5vZGUuZmluYWxpemVyICE9PSBudWxsKVxuICAgICAgICAgICAgICAgIGMobm9kZS5maW5hbGl6ZXIsIGN1clN0YXR1cywgdW5kZWZpbmVkKTtcbiAgICAgICAgfSxcblxuICAgICAgICBUaHJvd1N0YXRlbWVudDogZnVuY3Rpb24gKG5vZGUsIGN1clN0YXR1cywgYykge1xuICAgICAgICAgICAgY29uc3QgdGhyID0gYyhub2RlLmFyZ3VtZW50LCBjdXJTdGF0dXMsIHVuZGVmaW5lZCk7XG4gICAgICAgICAgICBjb25zdHJhaW50cy5wdXNoKHtGUk9NOiB0aHIsXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICBUTzogY3VyU3RhdHVzLmV4Y30pO1xuICAgICAgICAgICAgdGhyLnByb3BhZ2F0ZShjdXJTdGF0dXMuZXhjKTtcbiAgICAgICAgfSxcblxuICAgICAgICBDYWxsRXhwcmVzc2lvbjogZnVuY3Rpb24gKG5vZGUsIGN1clN0YXR1cywgYykge1xuICAgICAgICAgICAgY29uc3QgcmVzQVZhbCA9IMSILmdldChub2RlLCBjdXJTdGF0dXMuZGVsdGEpO1xuICAgICAgICAgICAgY29uc3QgYXJnQVZhbHMgPSBbXTtcblxuICAgICAgICAgICAgLy8gZ2V0IEFWYWxzIGZvciBlYWNoIGFyZ3VtZW50c1xuICAgICAgICAgICAgZm9yIChsZXQgaSA9IDA7IGkgPCBub2RlLmFyZ3VtZW50cy5sZW5ndGg7IGkrKykge1xuICAgICAgICAgICAgICAgIGFyZ0FWYWxzLnB1c2goXG4gICAgICAgICAgICAgICAgICAgIGMobm9kZS5hcmd1bWVudHNbaV0sIGN1clN0YXR1cywgdW5kZWZpbmVkKSk7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICAvLyBhcHBlbmQgY3VycmVudCBjYWxsIHNpdGUgdG8gdGhlIGNvbnRleHRcbiAgICAgICAgICAgIGNvbnN0IG5ld0RlbHRhID0gY3VyU3RhdHVzLmRlbHRhLmFwcGVuZE9uZShub2RlWydAbGFiZWwnXSk7XG5cbiAgICAgICAgICAgIGlmIChub2RlLmNhbGxlZS50eXBlID09PSAnTWVtYmVyRXhwcmVzc2lvbicpIHtcbiAgICAgICAgICAgICAgICAvLyBtZXRob2QgY2FsbFxuICAgICAgICAgICAgICAgIC8vIHZhciByZWN2ID0gYyhub2RlLmNhbGxlZS5vYmplY3QsIGN1clN0YXR1cywgdW5kZWZpbmVkKTtcbiAgICAgICAgICAgICAgICAvLyB2YXIgbWV0aG9kTmFtZSA9IGltbWVkUHJvcChub2RlLmNhbGxlZSk7XG4gICAgICAgICAgICAgICAgLy8gY29uc3RyYWludHMucHVzaCh7XG4gICAgICAgICAgICAgICAgLy8gICBSRUNWOiByZWN2LFxuICAgICAgICAgICAgICAgIC8vICAgUFJPUE5BTUU6IG1ldGhvZE5hbWUsXG4gICAgICAgICAgICAgICAgLy8gICBQQVJBTVM6IGFyZ0FWYWxzLFxuICAgICAgICAgICAgICAgIC8vICAgUkVUOiByZXNBVmFsLFxuICAgICAgICAgICAgICAgIC8vICAgRVhDOiBjdXJTdGF0dXMuZXhjLFxuICAgICAgICAgICAgICAgIC8vICAgREVMVEE6IG5ld0RlbHRhXG4gICAgICAgICAgICAgICAgLy8gfSk7XG4gICAgICAgICAgICAgICAgY29uc3QgcmVjdkFuZFJldCA9IHJlYWRNZW1iZXIobm9kZS5jYWxsZWUsIGN1clN0YXR1cywgYyk7XG4gICAgICAgICAgICAgICAgcmVjdkFuZFJldFsxXS5wcm9wYWdhdGUoXG4gICAgICAgICAgICAgICAgICAgIG5ldyBjc3RyLklzQ2FsbGVlKFxuICAgICAgICAgICAgICAgICAgICAgICAgcmVjdkFuZFJldFswXSxcbiAgICAgICAgICAgICAgICAgICAgICAgIGFyZ0FWYWxzLFxuICAgICAgICAgICAgICAgICAgICAgICAgcmVzQVZhbCxcbiAgICAgICAgICAgICAgICAgICAgICAgIGN1clN0YXR1cy5leGMsXG4gICAgICAgICAgICAgICAgICAgICAgICBuZXdEZWx0YSkpO1xuICAgICAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICAgICAgICAvLyBub3JtYWwgZnVuY3Rpb24gY2FsbFxuICAgICAgICAgICAgICAgIGNvbnN0IGNhbGxlZUFWYWwgPSBjKG5vZGUuY2FsbGVlLCBjdXJTdGF0dXMsIHVuZGVmaW5lZCk7XG4gICAgICAgICAgICAgICAgLy8gY2FsbGVl7J2YIHJldHVybuydhCBjYWxsIGV4cHJlc3Npb27snLzroZxcbiAgICAgICAgICAgICAgICAvLyBjYWxsZWXsnZggZXhjZXB0aW9u7J2EIO2YuOy2nCDsuKHsnZggZXhjZXB0aW9u7JeQIOyghOuLrO2VtOyVvFxuICAgICAgICAgICAgICAgIGNvbnN0cmFpbnRzLnB1c2goe1xuICAgICAgICAgICAgICAgICAgICBDQUxMRUU6IGNhbGxlZUFWYWwsXG4gICAgICAgICAgICAgICAgICAgIFNFTEY6IHJ0Q1guZ2xvYmFsT2JqZWN0LFxuICAgICAgICAgICAgICAgICAgICBQQVJBTVM6IGFyZ0FWYWxzLFxuICAgICAgICAgICAgICAgICAgICBSRVQ6IHJlc0FWYWwsXG4gICAgICAgICAgICAgICAgICAgIEVYQzogY3VyU3RhdHVzLmV4YyxcbiAgICAgICAgICAgICAgICAgICAgREVMVEE6IG5ld0RlbHRhXG4gICAgICAgICAgICAgICAgfSk7XG4gICAgICAgICAgICAgICAgY2FsbGVlQVZhbC5wcm9wYWdhdGUoXG4gICAgICAgICAgICAgICAgICAgIG5ldyBjc3RyLklzQ2FsbGVlKFxuICAgICAgICAgICAgICAgICAgICAgICAgbmV3IHR5cGVzLkFWYWwocnRDWC5nbG9iYWxPYmplY3QpLFxuICAgICAgICAgICAgICAgICAgICAgICAgYXJnQVZhbHMsXG4gICAgICAgICAgICAgICAgICAgICAgICByZXNBVmFsLFxuICAgICAgICAgICAgICAgICAgICAgICAgY3VyU3RhdHVzLmV4YyxcbiAgICAgICAgICAgICAgICAgICAgICAgIG5ld0RlbHRhKSk7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICByZXR1cm4gcmVzQVZhbDtcbiAgICAgICAgfSxcblxuICAgICAgICBNZW1iZXJFeHByZXNzaW9uOiBmdW5jdGlvbiAobm9kZSwgY3VyU3RhdHVzLCBjKSB7XG4gICAgICAgICAgICBjb25zdCByZWN2QW5kUmV0ID0gcmVhZE1lbWJlcihub2RlLCBjdXJTdGF0dXMsIGMpO1xuICAgICAgICAgICAgcmV0dXJuIHJlY3ZBbmRSZXRbMV07XG4gICAgICAgIH0sXG5cbiAgICAgICAgUmV0dXJuU3RhdGVtZW50OiBmdW5jdGlvbiAobm9kZSwgY3VyU3RhdHVzLCBjKSB7XG4gICAgICAgICAgICBpZiAoIW5vZGUuYXJndW1lbnQpIHJldHVybjtcbiAgICAgICAgICAgIGNvbnN0IHJldCA9IGMobm9kZS5hcmd1bWVudCwgY3VyU3RhdHVzLCB1bmRlZmluZWQpO1xuICAgICAgICAgICAgY29uc3RyYWludHMucHVzaCh7RlJPTTogcmV0LFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgVE86IGN1clN0YXR1cy5yZXR9KTtcbiAgICAgICAgICAgIHJldC5wcm9wYWdhdGUoY3VyU3RhdHVzLnJldCk7XG4gICAgICAgIH1cbiAgICB9KTtcblxuICAgIHJlY3Vyc2l2ZVdpdGhSZXR1cm4oYXN0LCBpbml0U3RhdHVzLCBjb25zdHJhaW50R2VuZXJhdG9yKTtcblxuICAgIC8vIFdlIGFjdHVhbGx5IGFkZGVkIGNvbnN0cmFpbnRzXG4gICAgcmV0dXJuIHRydWU7XG59XG5cbmZ1bmN0aW9uIHJlY3Vyc2l2ZVdpdGhSZXR1cm4obm9kZSwgc3RhdGUsIHZpc2l0b3IpIHtcbiAgICBmdW5jdGlvbiBjKG5vZGUsIHN0LCBvdmVycmlkZSkge1xuICAgICAgICByZXR1cm4gdmlzaXRvcltvdmVycmlkZSB8fCBub2RlLnR5cGVdKG5vZGUsIHN0LCBjKTtcbiAgICB9XG4gICAgcmV0dXJuIGMobm9kZSwgc3RhdGUpO1xufVxuXG5leHBvcnRzLmNvbnN0cmFpbnRzID0gY29uc3RyYWludHM7XG5leHBvcnRzLmFkZENvbnN0cmFpbnRzID0gYWRkQ29uc3RyYWludHM7XG5leHBvcnRzLmNsZWFyQ29uc3RyYWludHMgPSBjbGVhckNvbnN0cmFpbnRzO1xuIiwiJ3VzZSBzdHJpY3QnO1xuXG5jb25zdCB0eXBlcyA9IHJlcXVpcmUoJy4uL2RvbWFpbnMvdHlwZXMnKTtcbmNvbnN0IHN0YXR1cyA9IHJlcXVpcmUoJy4uL2RvbWFpbnMvc3RhdHVzJyk7XG5jb25zdCBjR2VuID0gcmVxdWlyZSgnLi9jR2VuJyk7XG5cbmZ1bmN0aW9uIENTVFIoKSB7fVxuQ1NUUi5wcm90b3R5cGUgPSBPYmplY3QuY3JlYXRlKG51bGwpO1xuQ1NUUi5wcm90b3R5cGUuZXF1YWxzID0gZnVuY3Rpb24gKG90aGVyKSB7XG4gICAgcmV0dXJuIHRoaXMgPT09IG90aGVyO1xufTtcblxuZnVuY3Rpb24gUmVhZFByb3AocHJvcCwgdG8pIHtcbiAgICB0aGlzLnByb3AgPSBwcm9wO1xuICAgIHRoaXMudG8gPSB0bztcbn1cblJlYWRQcm9wLnByb3RvdHlwZSA9IE9iamVjdC5jcmVhdGUoQ1NUUi5wcm90b3R5cGUpO1xuUmVhZFByb3AucHJvdG90eXBlLmFkZFR5cGUgPSBmdW5jdGlvbiAob2JqKSB7XG4gICAgaWYgKCEob2JqIGluc3RhbmNlb2YgKHR5cGVzLk9ialR5cGUpKSkgcmV0dXJuO1xuICAgIC8vIHdoZW4gb2JqIGlzIE9ialR5cGUsXG4gICAgY29uc3Qgb3duUHJvcCA9IG9iai5nZXRQcm9wKHRoaXMucHJvcCwgdHJ1ZSk7XG4gICAgaWYgKG93blByb3ApIHtcbiAgICAgICAgLy8gd2hlbiB0aGUgb2JqZWN0IGhhcyB0aGUgcHJvcCxcbiAgICAgICAgb3duUHJvcC5wcm9wYWdhdGUodGhpcy50byk7XG4gICAgfSBlbHNlIGlmIChvYmouZ2V0UHJvcCgnX19wcm90b19fJywgdHJ1ZSkpIHtcbiAgICAgICAgLy8gdXNlIHByb3RvdHlwZSBjaGFpblxuICAgICAgICBvYmouZ2V0UHJvcCgnX19wcm90b19fJylcbiAgICAgICAgICAucHJvcGFnYXRlKG5ldyBSZWFkUHJvcCh0aGlzLnByb3AsIHRoaXMudG8pKTtcbiAgICB9XG59O1xuUmVhZFByb3AucHJvdG90eXBlLmVxdWFscyA9IGZ1bmN0aW9uIChvdGhlcikge1xuICAgIGlmICghKG90aGVyIGluc3RhbmNlb2YgUmVhZFByb3ApKSByZXR1cm4gZmFsc2U7XG4gICAgcmV0dXJuIHRoaXMucHJvcCA9PT0gb3RoZXIucHJvcFxuICAgICAgICAmJiB0aGlzLnRvLmVxdWFscyhvdGhlci50byk7XG59O1xuXG5mdW5jdGlvbiBXcml0ZVByb3AocHJvcCwgZnJvbSkge1xuICAgIHRoaXMucHJvcCA9IHByb3A7XG4gICAgdGhpcy5mcm9tID0gZnJvbTtcbn1cbldyaXRlUHJvcC5wcm90b3R5cGUgPSBPYmplY3QuY3JlYXRlKENTVFIucHJvdG90eXBlKTtcbldyaXRlUHJvcC5wcm90b3R5cGUuYWRkVHlwZSA9IGZ1bmN0aW9uIChvYmopIHtcbiAgICBpZiAoIShvYmogaW5zdGFuY2VvZiAodHlwZXMuT2JqVHlwZSkpKSByZXR1cm47XG4gICAgY29uc3Qgb3duUHJvcCA9IG9iai5nZXRQcm9wKHRoaXMucHJvcCk7XG4gICAgdGhpcy5mcm9tLnByb3BhZ2F0ZShvd25Qcm9wKTtcbn07XG5cbmZ1bmN0aW9uIElzQWRkZWQob3RoZXIsIHRhcmdldCkge1xuICAgIHRoaXMub3RoZXIgPSBvdGhlcjtcbiAgICB0aGlzLnRhcmdldCA9IHRhcmdldDtcbn1cbklzQWRkZWQucHJvdG90eXBlID0gT2JqZWN0LmNyZWF0ZShDU1RSLnByb3RvdHlwZSk7XG5Jc0FkZGVkLnByb3RvdHlwZS5hZGRUeXBlID0gZnVuY3Rpb24gKHR5cGUpIHtcbiAgICBpZiAoKHR5cGUgPT09IHR5cGVzLlByaW1OdW1iZXIgXG4gICAgICAgICB8fCB0eXBlID09PSB0eXBlcy5QcmltQm9vbGVhbilcbiAgICAgJiYgKHRoaXMub3RoZXIuaGFzVHlwZSh0eXBlcy5QcmltTnVtYmVyKSBcbiAgICAgICAgIHx8IHRoaXMub3RoZXIuaGFzVHlwZSh0eXBlcy5QcmltQm9vbGVhbikpKSB7XG4gICAgICAgIHRoaXMudGFyZ2V0LmFkZFR5cGUodHlwZXMuUHJpbU51bWJlcik7XG4gICAgfVxuICAgIGlmICh0eXBlID09PSB0eXBlcy5QcmltU3RyaW5nXG4gICAgICYmICF0aGlzLm90aGVyLmlzRW1wdHkoKSkge1xuICAgICAgICAgdGhpcy50YXJnZXQuYWRkVHlwZSh0eXBlcy5QcmltU3RyaW5nKTtcbiAgICB9XG59O1xuXG5mdW5jdGlvbiBJc0NhbGxlZShzZWxmLCBhcmdzLCByZXQsIGV4YywgZGVsdGEpIHtcbiAgICB0aGlzLnNlbGYgPSBzZWxmO1xuICAgIHRoaXMuYXJncyA9IGFyZ3M7XG4gICAgdGhpcy5yZXQgPSByZXQ7XG4gICAgdGhpcy5leGMgPSBleGM7XG4gICAgdGhpcy5kZWx0YSA9IGRlbHRhO1xufVxuSXNDYWxsZWUucHJvdG90eXBlID0gT2JqZWN0LmNyZWF0ZShDU1RSLnByb3RvdHlwZSk7XG5Jc0NhbGxlZS5wcm90b3R5cGUuYWRkVHlwZSA9IGZ1bmN0aW9uIChmKSB7XG4gICAgaWYgKCEoZiBpbnN0YW5jZW9mICh0eXBlcy5GblR5cGUpKSkgcmV0dXJuO1xuICAgIGNvbnN0IGZ1bkVudiA9IGYuZ2V0RnVuRW52KHRoaXMuZGVsdGEpO1xuICAgIGNvbnN0IG5ld1NDID0gZi5vcmlnaW5Ob2RlLmJvZHlbJ0BibG9jayddLmdldFNjb3BlSW5zdGFuY2UoZi5zYywgdGhpcy5kZWx0YSk7XG4gICAgY29uc3QgZnVuU3RhdHVzXG4gICAgICAgID0gbmV3IHN0YXR1cy5TdGF0dXMoZnVuRW52WzBdLCBmdW5FbnZbMV0sIGZ1bkVudlsyXSwgXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgdGhpcy5kZWx0YSwgbmV3U0MpO1xuICAgIC8vIHBhc3MgdGhpcyBvYmplY3RcbiAgICB0aGlzLnNlbGYucHJvcGFnYXRlKGZ1bkVudlswXSk7XG5cbiAgICBjb25zdCBtaW5MZW4gPSBNYXRoLm1pbih0aGlzLmFyZ3MubGVuZ3RoLCBmLnBhcmFtTmFtZXMubGVuZ3RoKTtcbiAgICBmb3IgKGxldCBpID0gMDsgaSA8IG1pbkxlbjsgaSsrKSB7XG4gICAgICAgIHRoaXMuYXJnc1tpXS5wcm9wYWdhdGUobmV3U0MuZ2V0QVZhbE9mKGYucGFyYW1OYW1lc1tpXSkpO1xuICAgIH1cblxuICAgIC8vIGZvciBhcmd1bWVudHMgb2JqZWN0XG4gICAgaWYgKGYub3JpZ2luTm9kZS5ib2R5WydAYmxvY2snXS51c2VBcmd1bWVudHNPYmplY3QpIHtcbiAgICAgICAgY29uc3QgYXJnT2JqID0gZi5nZXRBcmd1bWVudHNPYmplY3QodGhpcy5kZWx0YSk7XG4gICAgICAgIG5ld1NDLmdldEFWYWxPZignYXJndW1lbnRzJykuYWRkVHlwZShhcmdPYmopO1xuICAgICAgICBmb3IgKGxldCBpID0gMDsgaSA8IHRoaXMuYXJncy5sZW5ndGg7IGkrKykge1xuICAgICAgICAgICAgdGhpcy5hcmdzW2ldLnByb3BhZ2F0ZShhcmdPYmouZ2V0UHJvcChpICsgJycpKTtcbiAgICAgICAgICAgIHRoaXMuYXJnc1tpXS5wcm9wYWdhdGUoYXJnT2JqLmdldFByb3AobnVsbCkpO1xuICAgICAgICB9XG4gICAgICAgIGFyZ09iai5nZXRQcm9wKCdjYWxsZWUnKS5hZGRUeXBlKGYpO1xuICAgICAgICBhcmdPYmouZ2V0UHJvcCgnbGVuZ3RoJykuYWRkVHlwZSh0eXBlcy5QcmltTnVtYmVyKTtcbiAgICB9XG5cbiAgICAvLyBjb25zdHJhaW50IGdlbmVyYXRpb24gZm9yIHRoZSBmdW5jdGlvbiBib2R5XG4gICAgY0dlbi5hZGRDb25zdHJhaW50cyhmLm9yaWdpbk5vZGUuYm9keSwgZnVuU3RhdHVzKTtcblxuICAgIC8vIGdldCByZXR1cm4gXG4gICAgZnVuRW52WzFdLnByb3BhZ2F0ZSh0aGlzLnJldCk7XG4gICAgLy8gZ2V0IGV4Y2VwdGlvblxuICAgIGZ1bkVudlsyXS5wcm9wYWdhdGUodGhpcy5leGMpO1xufTtcblxuZnVuY3Rpb24gSXNDdG9yKGFyZ3MsIHJldCwgZXhjLCBkZWx0YSkge1xuICAgIHRoaXMuYXJncyA9IGFyZ3M7XG4gICAgdGhpcy5yZXQgPSByZXQ7XG4gICAgdGhpcy5leGMgPSBleGM7XG4gICAgdGhpcy5kZWx0YSA9IGRlbHRhO1xufVxuSXNDdG9yLnByb3RvdHlwZSA9IE9iamVjdC5jcmVhdGUoQ1NUUi5wcm90b3R5cGUpO1xuSXNDdG9yLnByb3RvdHlwZS5hZGRUeXBlID0gZnVuY3Rpb24gKGYpIHtcbiAgICBpZiAoIShmIGluc3RhbmNlb2YgKHR5cGVzLkZuVHlwZSkpKSByZXR1cm47XG4gICAgY29uc3QgZnVuRW52ID0gZi5nZXRGdW5FbnYodGhpcy5kZWx0YSk7XG4gICAgY29uc3QgbmV3U0MgPSBmLm9yaWdpbk5vZGUuYm9keVsnQGJsb2NrJ10uZ2V0U2NvcGVJbnN0YW5jZShmLnNjLCB0aGlzLmRlbHRhKTtcbiAgICBjb25zdCBmdW5TdGF0dXNcbiAgICAgICAgPSBuZXcgc3RhdHVzLlN0YXR1cyhmdW5FbnZbMF0sIG5ldyBJZk9ialR5cGUoZnVuRW52WzFdKSwgZnVuRW52WzJdLFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIHRoaXMuZGVsdGEsIG5ld1NDKTtcbiAgICAvLyBwYXNzIHRoaXMgb2JqZWN0XG4gICAgY29uc3QgbmV3T2JqID0gZi5nZXRJbnN0YW5jZSgpO1xuICAgIGZ1bkVudlswXS5hZGRUeXBlKG5ld09iaik7XG5cbiAgICBjb25zdCBtaW5MZW4gPSBNYXRoLm1pbih0aGlzLmFyZ3MubGVuZ3RoLCBmLnBhcmFtTmFtZXMubGVuZ3RoKTtcbiAgICBmb3IgKGxldCBpID0gMDsgaSA8IG1pbkxlbjsgaSsrKSB7XG4gICAgICAgIHRoaXMuYXJnc1tpXS5wcm9wYWdhdGUobmV3U0MuZ2V0QVZhbE9mKGYucGFyYW1OYW1lc1tpXSkpO1xuICAgIH1cblxuICAgIC8vIGZvciBhcmd1bWVudHMgb2JqZWN0XG4gICAgaWYgKGYub3JpZ2luTm9kZS5ib2R5WydAYmxvY2snXS51c2VBcmd1bWVudHNPYmplY3QpIHtcbiAgICAgICAgY29uc3QgYXJnT2JqID0gZi5nZXRBcmd1bWVudHNPYmplY3QodGhpcy5kZWx0YSk7XG4gICAgICAgIG5ld1NDLmdldEFWYWxPZignYXJndW1lbnRzJykuYWRkVHlwZShhcmdPYmopO1xuICAgICAgICBmb3IgKGxldCBpID0gMDsgaSA8IHRoaXMuYXJncy5sZW5ndGg7IGkrKykge1xuICAgICAgICAgICAgdGhpcy5hcmdzW2ldLnByb3BhZ2F0ZShhcmdPYmouZ2V0UHJvcChpICsgJycpKTtcbiAgICAgICAgICAgIHRoaXMuYXJnc1tpXS5wcm9wYWdhdGUoYXJnT2JqLmdldFByb3AobnVsbCkpO1xuICAgICAgICB9XG4gICAgICAgIGFyZ09iai5nZXRQcm9wKCdjYWxsZWUnKS5hZGRUeXBlKGYpO1xuICAgICAgICBhcmdPYmouZ2V0UHJvcCgnbGVuZ3RoJykuYWRkVHlwZSh0eXBlcy5QcmltTnVtYmVyKTtcbiAgICB9XG5cbiAgICAvLyBjb25zdHJhaW50IGdlbmVyYXRpb24gZm9yIHRoZSBmdW5jdGlvbiBib2R5XG4gICAgY0dlbi5hZGRDb25zdHJhaW50cyhmLm9yaWdpbk5vZGUuYm9keSwgZnVuU3RhdHVzKTtcblxuICAgIC8vIGJ5IGV4cGxpY2l0IHJldHVybiwgb25seSBPYmpUeXBlIGFyZSBwcm9wYWdhdGVkXG4gICAgZnVuRW52WzFdLnByb3BhZ2F0ZSh0aGlzLnJldCk7XG4gICAgLy8gcmV0dXJuIG5ldyBvYmplY3RcbiAgICB0aGlzLnJldC5hZGRUeXBlKG5ld09iaik7XG4gICAgLy8gZ2V0IGV4Y2VwdGlvblxuICAgIGZ1bkVudlsyXS5wcm9wYWdhdGUodGhpcy5leGMpO1xufTtcblxuLy8gaWdub3JlIG5vbiBvYmplY3QgdHlwZXNcbmZ1bmN0aW9uIElmT2JqVHlwZShhdmFsKSB7XG4gICAgdGhpcy5hdmFsID0gYXZhbDtcbn1cbklmT2JqVHlwZS5wcm90b3R5cGUgPSBPYmplY3QuY3JlYXRlKENTVFIucHJvdG90eXBlKTtcbklmT2JqVHlwZS5wcm90b3R5cGUuYWRkVHlwZSA9IGZ1bmN0aW9uICh0eXBlKSB7XG4gICAgaWYgKCEodHlwZSBpbnN0YW5jZW9mIHR5cGVzLk9ialR5cGUpKSByZXR1cm47XG4gICAgdGhpcy5hdmFsLmFkZFR5cGUodHlwZSk7XG59O1xuXG5leHBvcnRzLlJlYWRQcm9wID0gUmVhZFByb3A7XG5leHBvcnRzLldyaXRlUHJvcCA9IFdyaXRlUHJvcDtcbmV4cG9ydHMuSXNBZGRlZCA9IElzQWRkZWQ7XG5leHBvcnRzLklzQ2FsbGVlID0gSXNDYWxsZWU7XG5leHBvcnRzLklzQ3RvciA9IElzQ3RvcjtcbiIsIi8vIENvbnRleHQgZm9yIGstQ0ZBIGFuYWx5c2lzXG4vL1xuLy8gQXNzdW1lIGEgY29udGV4dCBpcyBhbiBhcnJheSBvZiBudW1iZXJzLlxuLy8gQSBudW1iZXIgaW4gc3VjaCBsaXN0IGRlbm90ZXMgYSBjYWxsIHNpdGUsIHRoYXQgaXMgQGxhYmVsIG9mIGEgQ2FsbEV4cHJlc3Npb24uXG4vLyBXZSBrZWVwIHRoZSBtb3N0IHJlY2VudCAnaycgY2FsbHNpdGVzLlxuLy8gRXF1YWxpdHkgb24gY29udGV4dHMgc2hvdWxkIGxvb2sgaW50byB0aGUgbnVtYmVycy5cblxudmFyIGNhbGxTaXRlQ29udGV4dFBhcmFtZXRlciA9IHtcbiAgICAvLyBtYXhpbXVtIGxlbmd0aCBvZiBjb250ZXh0XG4gICAgbWF4RGVwdGhLOiAwLFxuICAgIC8vIGZ1bmN0aW9uIGxpc3QgZm9yIHNlbnNpdGl2ZSBhbmFseXNpc1xuICAgIHNlbnNGdW5jczoge31cbn07XG5cbmZ1bmN0aW9uIENhbGxTaXRlQ29udGV4dChjc0xpc3QpIHtcbiAgICBpZiAoY3NMaXN0KSB0aGlzLmNzTGlzdCA9IGNzTGlzdDtcbiAgICBlbHNlIHRoaXMuY3NMaXN0ID0gW107XG59XG5cbkNhbGxTaXRlQ29udGV4dC5wcm90b3R5cGUuZXF1YWxzID0gZnVuY3Rpb24gKG90aGVyKSB7XG4gICAgaWYgKHRoaXMuY3NMaXN0Lmxlbmd0aCAhPSBvdGhlci5jc0xpc3QubGVuZ3RoKSByZXR1cm4gZmFsc2U7XG4gICAgZm9yICh2YXIgaSA9IDA7IGkgPCB0aGlzLmNzTGlzdC5sZW5ndGg7IGkrKykge1xuICAgICAgICBpZiAodGhpcy5jc0xpc3RbaV0gIT09IG90aGVyLmNzTGlzdFtpXSkgcmV0dXJuIGZhbHNlO1xuICAgIH1cbiAgICByZXR1cm4gdHJ1ZTtcbn07XG5cbkNhbGxTaXRlQ29udGV4dC5wcm90b3R5cGUuYXBwZW5kT25lID0gZnVuY3Rpb24gKGNhbGxTaXRlKSB7XG4gICAgLy8gdXNlIGNvbmNhdCB0byBjcmVhdGUgYSBuZXcgYXJyYXlcbiAgICAvLyBvbGRlc3Qgb25lIGNvbWVzIGZpcnN0XG4gICAgdmFyIGFwcGVuZGVkID0gdGhpcy5jc0xpc3QuY29uY2F0KGNhbGxTaXRlKTtcbiAgICBpZiAoYXBwZW5kZWQubGVuZ3RoID4gY2FsbFNpdGVDb250ZXh0UGFyYW1ldGVyLm1heERlcHRoSykge1xuICAgICAgICBhcHBlbmRlZC5zaGlmdCgpO1xuICAgIH1cbiAgICByZXR1cm4gbmV3IENhbGxTaXRlQ29udGV4dChhcHBlbmRlZCk7XG59O1xuXG5DYWxsU2l0ZUNvbnRleHQucHJvdG90eXBlLnRvU3RyaW5nID0gZnVuY3Rpb24gKCkge1xuICAgIHJldHVybiB0aGlzLmNzTGlzdC50b1N0cmluZygpO1xufTtcblxuZXhwb3J0cy5jYWxsU2l0ZUNvbnRleHRQYXJhbWV0ZXIgPSBjYWxsU2l0ZUNvbnRleHRQYXJhbWV0ZXI7XG5leHBvcnRzLkNhbGxTaXRlQ29udGV4dCA9IENhbGxTaXRlQ29udGV4dDsiLCIvLyBTdGF0dXM6XG4vLyB7IHNlbGYgIDogQVZhbCxcbi8vICAgcmV0ICAgOiBBVmFsLFxuLy8gICBleGMgICA6IEFWYWwsXG4vLyAgIGRlbHRhIDogQ29udGV4dCxcbi8vICAgc2MgICAgOiBTY29wZUNoYWluIH1cblxuZnVuY3Rpb24gU3RhdHVzKHNlbGYsIHJldCwgZXhjLCBkZWx0YSwgc2MpIHtcbiAgICB0aGlzLnNlbGYgPSBzZWxmO1xuICAgIHRoaXMucmV0ID0gcmV0O1xuICAgIHRoaXMuZXhjID0gZXhjO1xuICAgIHRoaXMuZGVsdGEgPSBkZWx0YTtcbiAgICB0aGlzLnNjID0gc2M7XG59XG5cblN0YXR1cy5wcm90b3R5cGUuZXF1YWxzID0gZnVuY3Rpb24gKG90aGVyKSB7XG4gICAgcmV0dXJuIHRoaXMuc2VsZiA9PT0gb3RoZXIuc2VsZiAmJlxuICAgICAgICB0aGlzLnJldCA9PT0gb3RoZXIucmV0ICYmXG4gICAgICAgIHRoaXMuZXhjID09PSBvdGhlci5leGMgJiZcbiAgICAgICAgdGhpcy5kZWx0YS5lcXVhbHMob3RoZXIuZGVsdGEpICYmXG4gICAgICAgIHRoaXMuc2MgPT09IG90aGVyLnNjO1xufTtcblxuZXhwb3J0cy5TdGF0dXMgPSBTdGF0dXM7IiwiJ3VzZSBzdHJpY3QnO1xuXG4vLyBmb3IgREVCVUdcbnZhciBjb3VudCA9IDA7XG4vKipcbiAqIHRoZSBhYnN0cmFjdCB2YWx1ZSBmb3IgYSBjb25jcmV0ZSB2YWx1ZVxuICogd2hpY2ggaXMgYSBzZXQgb2YgdHlwZXMuXG4gKiBAY29uc3RydWN0b3JcbiAqIEBwYXJhbSB7VHlwZX0gdHlwZSAtIGdpdmUgYSB0eXBlIHRvIG1ha2UgQVZhbCB3aXRoIGEgc2luZ2xlIHR5cGVcbiAqL1xuZnVuY3Rpb24gQVZhbCh0eXBlKSB7XG4gICAgLy8gdHlwZTogY29udGFpbmVkIHR5cGVzXG4gICAgLy8gV2UgYXNzdW1lIHR5cGVzIGFyZSBkaXN0aW5ndWlzaGFibGUgYnkgJz09PSdcbiAgICBpZiAodHlwZSkgdGhpcy50eXBlcyA9IG5ldyBTZXQoW3R5cGVdKTtcbiAgICBlbHNlIHRoaXMudHlwZXMgPSBuZXcgU2V0KCk7XG4gICAgLy8gZm9yd2FyZHM6IHByb3BhZ2F0aW9uIHRhcmdldHNcbiAgICAvLyBXZSBhc3N1bWUgdGFyZ2V0cyBhcmUgZGlzdGluZ3Vpc2hhYmxlIGJ5ICdlcXVhbHMnIG1ldGhvZFxuICAgIHRoaXMuZm9yd2FyZHMgPSBuZXcgU2V0KCk7XG4gICAgLy8gZm9yIERFQlVHXG4gICAgdGhpcy5faWQgPSBjb3VudCsrO1xufVxuLyoqIENoZWNrIHdoZXRoZXIgaXQgaGFzIGFueSB0eXBlXG4gKiBAcmV0dXJucyB7Ym9vbGVhbn1cbiAqL1xuQVZhbC5wcm90b3R5cGUuaXNFbXB0eSA9IGZ1bmN0aW9uICgpIHtcbiAgICByZXR1cm4gdGhpcy50eXBlcy5zaXplID09PSAwO1xufTtcblxuLyoqXG4gKiBAcmV0dXJucyB7W1R5cGVdfVxuICovXG5BVmFsLnByb3RvdHlwZS5nZXRUeXBlcyA9IGZ1bmN0aW9uICgpIHtcbiAgICByZXR1cm4gdGhpcy50eXBlcztcbn07XG5cbi8qKlxuICogQHJldHVybnMge2Jvb2xlYW59XG4gKi9cbkFWYWwucHJvdG90eXBlLmhhc1R5cGUgPSBmdW5jdGlvbiAodHlwZSkge1xuICAgIHJldHVybiB0aGlzLnR5cGVzLmhhcyh0eXBlKTtcbn07XG5cbi8qKlxuICogQWRkIGEgdHlwZS5cbiAqIEBwYXJhbSB7VHlwZX0gdHlwZVxuICovXG5BVmFsLnByb3RvdHlwZS5hZGRUeXBlID0gZnVuY3Rpb24gKHR5cGUpIHtcbiAgICBpZiAodGhpcy50eXBlcy5oYXModHlwZSkpIHJldHVybjtcbiAgICAvLyBnaXZlbiB0eXBlIGlzIG5ld1xuICAgIHRoaXMudHlwZXMuYWRkKHR5cGUpO1xuICAgIC8vIHNlbmQgdG8gcHJvcGFnYXRpb24gdGFyZ2F0c1xuICAgIHRoaXMuZm9yd2FyZHMuZm9yRWFjaChmdW5jdGlvbiAoZndkKSB7XG4gICAgICAgIGZ3ZC5hZGRUeXBlKHR5cGUpO1xuICAgIH0pO1xufTtcbi8qKlxuICogQHBhcmFtIHtBVmFsfSB0YXJnZXRcbiAqL1xuQVZhbC5wcm90b3R5cGUucHJvcGFnYXRlID0gZnVuY3Rpb24gKHRhcmdldCkge1xuICAgIGlmICghdGhpcy5hZGRGb3J3YXJkKHRhcmdldCkpIHJldHVybjtcbiAgICAvLyB0YXJnZXQgaXMgbmV3bHkgYWRkZWRcbiAgICAvLyBzZW5kIHR5cGVzIHRvIHRoZSBuZXcgdGFyZ2V0XG4gICAgdGhpcy50eXBlcy5mb3JFYWNoKGZ1bmN0aW9uICh0eXBlKSB7XG4gICAgICAgIHRhcmdldC5hZGRUeXBlKHR5cGUpO1xuICAgIH0pO1xufTtcblxuQVZhbC5wcm90b3R5cGUuYWRkRm9yd2FyZCA9IGZ1bmN0aW9uIChmd2QpIHtcbiAgICBmb3IgKGxldCBvbGRGd2Qgb2YgdGhpcy5mb3J3YXJkcykge1xuICAgICAgICBpZiAoZndkLmVxdWFscyhvbGRGd2QpKSByZXR1cm4gZmFsc2U7XG4gICAgfVxuICAgIHRoaXMuZm9yd2FyZHMuYWRkKGZ3ZCk7XG4gICAgcmV0dXJuIHRydWU7XG59O1xuXG5BVmFsLnByb3RvdHlwZS5lcXVhbHMgPSBmdW5jdGlvbiAob3RoZXIpIHtcbiAgICAvLyBzaW1wbGUgcmVmZXJlbmNlIGNvbXBhcmlzb25cbiAgICByZXR1cm4gdGhpcyA9PT0gb3RoZXI7XG59O1xuXG4vKipcbiAqIFRPRE86IGNoZWNrIHdoZXRoZXIgd2UgcmVhbGx5IG5lZWQgdGhpcyBtZXRob2QuXG4gKiBAcGFyYW0ge3N0cmluZ30gcHJvcFxuICogQHJldHVybnMge0FWYWx9XG4gKi9cbkFWYWwucHJvdG90eXBlLmdldFByb3AgPSBmdW5jdGlvbiAocHJvcCkge1xuICAgIGlmIChwcm9wID09PSAn4pyWJykge1xuICAgICAgICAvLyDinJYgaXMgdGhlIGJvZ3VzIHByb3BlcnR5IG5hbWUgYWRkZWQgZm9yIGVycm9yIHJlY292ZXJ5LlxuICAgICAgICByZXR1cm4gQVZhbE51bGw7XG4gICAgfVxuICAgIGlmICh0aGlzLnByb3BzLmhhcyhwcm9wKSkge1xuICAgICAgICByZXR1cm4gdGhpcy5wcm9wcy5nZXQocHJvcCk7XG4gICAgfSBlbHNlIHtcbiAgICAgICAgcmV0dXJuIEFWYWxOdWxsO1xuICAgIH1cbn07XG5cbi8qKlxuICogdGhlIHN1cGVyIGNsYXNzIG9mIGFsbCB0eXBlc1xuICogZWFjaCB0eXBlIHNob3VsZCBiZSBkaXN0aW5ndWlzaGFibGUgYnkgJz09PScgb3BlcmF0aW9uLlxuICogQGNvbnN0cnVjdG9yXG4gKi9cbmZ1bmN0aW9uIFR5cGUobmFtZSkge1xuICAgIHRoaXMubmFtZSA9IG5hbWU7XG59XG5UeXBlLnByb3RvdHlwZSA9IE9iamVjdC5jcmVhdGUobnVsbCk7XG5UeXBlLnByb3RvdHlwZS5nZXROYW1lID0gZnVuY3Rpb24gKCkge1xuICAgIHJldHVybiB0aGlzLm5hbWU7XG59O1xuXG4vKipcbiAqIDEuIG9iamVjdCB0eXBlc1xuICogQHBhcmFtIHtBVmFsfSBwcm90byAtIEFWYWwgb2YgY29uc3RydWN0b3IncyBwcm90b3R5cGVcbiAqIEBwYXJhbSB7c3RyaW5nfSBuYW1lIC0gZ3Vlc3NlZCBuYW1lXG4gKi9cbmZ1bmN0aW9uIE9ialR5cGUocHJvdG8sIG5hbWUpIHtcbiAgICB0aGlzLm5hbWUgPSBuYW1lO1xuICAgIHRoaXMucHJvcHMgPSBuZXcgTWFwKCk7XG5cbiAgICAvLyBzaGFyZSBwcm90byB3aXRoIF9fcHJvdG9fX1xuICAgIHRoaXMuc2V0UHJvcCgnX19wcm90b19fJywgcHJvdG8pO1xufVxuT2JqVHlwZS5wcm90b3R5cGUgPSBPYmplY3QuY3JlYXRlKFR5cGUucHJvdG90eXBlKTtcbi8qKlxuICogQHBhcmFtIHtzdHJpbmd8bnVsbH0gcHJvcCAtIG51bGwgZm9yIGNvbXB1dGVkIHByb3BzXG4gKiBAcGFyYW0ge2Jvb2xlYW59IHJlYWRPbmx5IC0gaWYgZmFsc2UsIGNyZWF0ZSBBVmFsIGZvciBwcm9wIGlmIG5lY2Vzc2FyeVxuICogQHJldHVybnMge0FWYWx9IEFWYWwgb2YgdGhlIHByb3BlcnR5XG4gKi9cbk9ialR5cGUucHJvdG90eXBlLmdldFByb3AgPSBmdW5jdGlvbiAocHJvcCwgcmVhZE9ubHkpIHtcbiAgICBpZiAocHJvcCA9PT0gJ+KclicpIHtcbiAgICAgICAgLy8g4pyWIGlzIHRoZSBib2d1cyBwcm9wZXJ0eSBuYW1lIGFkZGVkIGR1cmluZyBwYXJzaW5nIGVycm9yIHJlY292ZXJ5LlxuICAgICAgICByZXR1cm4gQVZhbE51bGw7XG4gICAgfVxuICAgIGlmICh0aGlzLnByb3BzLmhhcyhwcm9wKSkge1xuICAgICAgICByZXR1cm4gdGhpcy5wcm9wcy5nZXQocHJvcCk7XG4gICAgfSBlbHNlIGlmIChyZWFkT25seSkge1xuICAgICAgICByZXR1cm4gbnVsbDtcbiAgICB9IGVsc2Uge1xuICAgICAgICB2YXIgbmV3UHJvcEFWYWwgPSBuZXcgQVZhbDtcbiAgICAgICAgdGhpcy5wcm9wcy5zZXQocHJvcCwgbmV3UHJvcEFWYWwpO1xuICAgICAgICByZXR1cm4gbmV3UHJvcEFWYWw7XG4gICAgfVxufTtcbi8qKlxuICogV2UgdXNlIHRoaXMgZnVuY3Rpb24gdG8gc2hhcmUgLnByb3RvdHlwZSB3aXRoIGluc3RhbmNlcyBfX3Byb3RvX19cbiAqIEl0IGlzIHBvc3NpYmxlIHRvIHVzZSB0aGlzIGZ1bmN0aW9uIHRvIG1lcmdlIEFWYWxzIHRvIG9wdGltaXplIHRoZSBhbmFseXplci5cbiAqIEBwYXJhbSB7c3RyaW5nfG51bGx9IHByb3AgLSBudWxsIGZvciBjb21wdXRlZCBwcm9wc1xuICogQHBhcmFtIHtBVmFsfSBhdmFsXG4gKi9cbk9ialR5cGUucHJvdG90eXBlLnNldFByb3AgPSBmdW5jdGlvbiAocHJvcCwgYXZhbCkge1xuICAgIGlmIChwcm9wID09PSAn4pyWJykge1xuICAgICAgICAvLyDinJYgaXMgdGhlIGJvZ3VzIHByb3BlcnR5IG5hbWUgYWRkZWQgZHVyaW5nIHBhcnNpbmcgZXJyb3IgcmVjb3ZlcnkuXG4gICAgICAgIHJldHVybjtcbiAgICB9XG4gICAgdGhpcy5wcm9wcy5zZXQocHJvcCwgYXZhbCk7XG59O1xuLyoqXG4gKiBUT0RPOiBDaGVjayB0aGlzIGZ1bmN0aW9uJ3MgbmVjZXNzaXR5XG4gKiBAcGFyYW0ge3N0cmluZ30gcHJvcFxuICogQHJldHVybnMge2Jvb2xlYW59XG4gKi9cbk9ialR5cGUucHJvdG90eXBlLmhhc1Byb3AgPSBmdW5jdGlvbiAocHJvcCkge1xuICAgIGlmIChwcm9wID09PSAn4pyWJykgcmV0dXJuIGZhbHNlO1xuICAgIHJldHVybiB0aGlzLnByb3BzLmhhcyhwcm9wKTtcbn07XG4vKipcbiAqIFRPRE86IENoZWNrIHRoaXMgZnVuY3Rpb24ncyBuZWNlc3NpdHlcbiAqIEBwYXJhbSB7VHlwZX0gdHlwZVxuICogQHBhcmFtIHtzdHJpbmd9IHByb3BcbiAqL1xuT2JqVHlwZS5wcm90b3R5cGUuYWRkVHlwZVRvUHJvcCA9IGZ1bmN0aW9uICh0eXBlLCBwcm9wKSB7XG4gICAgaWYgKHByb3AgPT09ICfinJYnKSByZXR1cm47XG4gICAgaWYgKCF0aGlzLnByb3BzLmhhcyhwcm9wKSkge1xuICAgICAgICB0aGlzLnByb3BzLnNldChwcm9wLCBuZXcgQVZhbCk7XG4gICAgfVxuICAgIGlmICh0aGlzLnByb3BzLmdldChwcm9wKS5oYXNUeXBlKHR5cGUpKSByZXR1cm47XG4gICAgdGhpcy5wcm9wcy5nZXQocHJvcCkuYWRkVHlwZSh0eXBlKTtcbn07XG4vKipcbiAqIFRPRE86IENoZWNrIHRoaXMgZnVuY3Rpb24ncyBuZWNlc3NpdHlcbiAqIEBwYXJhbSB7QVZhbH0gYXZhbFxuICogQHBhcmFtIHtzdHJpbmd9IHByb3BcbiAqL1xuT2JqVHlwZS5wcm90b3R5cGUuam9pbkFWYWxUb1Byb3AgPSBmdW5jdGlvbiAoYXZhbCwgcHJvcCkge1xuICAgIHZhciBzZWxmID0gdGhpcztcbiAgICBhdmFsLmdldFR5cGVzKCkuZm9yRWFjaChmdW5jdGlvbiAodHlwZSkge1xuICAgICAgICBzZWxmLmFkZFR5cGVUb1Byb3AodHlwZSwgcHJvcCk7XG4gICAgfSk7XG59O1xuXG4vLyBtYWtlIGFuIE9iaiBmcm9tIHRoZSBnbG9iYWwgc2NvcGVcbmZ1bmN0aW9uIG1rT2JqRnJvbUdsb2JhbFNjb3BlKGdTY29wZSkge1xuICAgIHZhciBnT2JqID0gbmV3IE9ialR5cGUoQVZhbE51bGwsICcqZ2xvYmFsIHNjb3BlKicpO1xuICAgIGdPYmoucHJvcHMgPSBnU2NvcGUudmFyTWFwO1xuICAgIC8vIE92ZXJyaWRlIGdldFByb3AgbWV0aG9kIGZvciBnbG9iYWwgb2JqZWN0XG4gICAgLy8gV2UgaWdub3JlICdyZWFkT25seScgcGFyYW1ldGVyIHRvIGFsd2F5cyByZXR1cm4gaXRzIG93biBwcm9wIEFWYWwgXG4gICAgZ09iai5nZXRQcm9wID0gZnVuY3Rpb24gKHByb3ApIHtcbiAgICAgICAgcmV0dXJuIE9ialR5cGUucHJvdG90eXBlLmdldFByb3AuY2FsbCh0aGlzLCBwcm9wKTtcbiAgICB9O1xuICAgIHJldHVybiBnT2JqO1xufVxuXG4vKipcbiAqIDIuIHByaW1pdGl2ZSB0eXBlc1xuICogQGNvbnN0cnVjdG9yXG4gKiBAcGFyYW0ge3N0cmluZ30gbmFtZVxuICovXG5mdW5jdGlvbiBQcmltVHlwZShuYW1lKSB7XG4gICAgdGhpcy5uYW1lID0gbmFtZTtcbn1cblByaW1UeXBlLnByb3RvdHlwZSA9IE9iamVjdC5jcmVhdGUoVHlwZS5wcm90b3R5cGUpO1xuXG4vKipcbiAqIDMuIGZ1bmN0aW9uIHR5cGVzXG4gKiB0aGUgbmFtZSBpcyB1c2VkIGZvciB0aGUgdHlwZSBvZiB0aGUgaW5zdGFuY2VzIGZyb20gdGhlIGZ1bmN0aW9uXG4gKiBAY29uc3RydWN0b3JcbiAqIEBwYXJhbSB7QVZhbH0gZm5fcHJvdG8gLSBBVmFsIGZvciBjb25zdHJ1Y3RvcidzIC5wcm90b3R5cGVcbiAqIEBwYXJhbSB7c3RyaW5nfSBuYW1lIC0gZ3Vlc3NlZCBuYW1lXG4gKiBAcGFyYW0ge1tzdHJpbmddfSBhcmdOYW1lcyAtIGxpc3Qgb2YgcGFyYW1ldGVyIG5hbWVzXG4gKiBAcGFyYW0ge1Njb3BlfSBzYyAtIGZ1bmN0aW9ucyBzY29wZSBjaGFpbiwgb3IgY2xvc3VyZVxuICogQHBhcmFtIHtub2RlfSBvcmlnaW5Ob2RlIC0gQVNUIG5vZGUgZm9yIHRoZSBmdW5jdGlvblxuICogQHBhcmFtIHtUeXBlfSBhcmdQcm90byAtIHByb3RvdHlwZSBmb3IgYXJndW1lbnRzIG9iamVjdFxuICovXG5mdW5jdGlvbiBGblR5cGUoZm5fcHJvdG8sIG5hbWUsIGFyZ05hbWVzLCBzYywgb3JpZ2luTm9kZSwgYXJnUHJvdG8pIHtcbiAgICBPYmpUeXBlLmNhbGwodGhpcywgZm5fcHJvdG8sIG5hbWUpO1xuICAgIHRoaXMucGFyYW1OYW1lcyA9IGFyZ05hbWVzO1xuICAgIHRoaXMuc2MgPSBzYztcbiAgICB0aGlzLm9yaWdpbk5vZGUgPSBvcmlnaW5Ob2RlO1xuICAgIHRoaXMuYXJnUHJvdG8gPSBhcmdQcm90bztcbiAgICAvLyBmdW5FbnYgOiBDYWxsQ29udGV4dCAtPiBbc2VsZiwgcmV0LCBleGNdXG4gICAgdGhpcy5mdW5FbnYgPSBuZXcgTWFwO1xufVxuRm5UeXBlLnByb3RvdHlwZSA9IE9iamVjdC5jcmVhdGUoT2JqVHlwZS5wcm90b3R5cGUpO1xuXG4vKipcbiAqIGNvbnN0cnVjdCBTdGF0dXMgZm9yIGZ1bmN0aW9uXG4gKiBAcGFyYW0ge0NhbGxDb250ZXh0fSBkZWx0YSAtIGNhbGwgY29udGV4dFxuICogQHJldHVybnMge1tBVmFsLCBBVmFsLCBBVmFsXX0gLSBmb3Igc2VsZiwgcmV0dXJuIGFuZCBleGNlcHRpb24gQVZhbHNcbiAqL1xuRm5UeXBlLnByb3RvdHlwZS5nZXRGdW5FbnYgPSBmdW5jdGlvbiAoZGVsdGEpIHtcbiAgICBpZiAodGhpcy5mdW5FbnYuaGFzKGRlbHRhKSkge1xuICAgICAgICByZXR1cm4gdGhpcy5mdW5FbnYuZ2V0KGRlbHRhKTtcbiAgICB9IGVsc2Uge1xuICAgICAgICB2YXIgdHJpcGxlID0gW25ldyBBVmFsLCBuZXcgQVZhbCwgbmV3IEFWYWxdO1xuICAgICAgICB0aGlzLmZ1bkVudi5zZXQoZGVsdGEsIHRyaXBsZSk7XG4gICAgICAgIHJldHVybiB0cmlwbGU7XG4gICAgfVxufTtcblxuRm5UeXBlLnByb3RvdHlwZS5nZXRBcmd1bWVudHNPYmplY3QgPSBmdW5jdGlvbiAoZGVsdGEpIHtcbiAgICB0aGlzLmFyZ09iak1hcCA9IHRoaXMuYXJnT2JqTWFwIHx8IG5ldyBNYXA7XG4gICAgaWYgKHRoaXMuYXJnT2JqTWFwLmhhcyhkZWx0YSkpIHtcbiAgICAgICAgcmV0dXJuIHRoaXMuYXJnT2JqTWFwLmdldChkZWx0YSk7XG4gICAgfSBlbHNlIHtcbiAgICAgICAgdmFyIGFyZ09iaiA9IG5ldyBPYmpUeXBlKG5ldyBBVmFsKHRoaXMuYXJnUHJvdG8pLCAnKmFyZ3VtZW50cyBvYmplY3QqJyk7XG4gICAgICAgIHRoaXMuYXJnT2JqTWFwLnNldChkZWx0YSwgYXJnT2JqKTtcbiAgICAgICAgcmV0dXJuIGFyZ09iajtcbiAgICB9XG59O1xuXG4vKipcbiAqIGdldCBPYmplY3QgbWFkZSBieSB0aGUgZnVuY3Rpb25cbiAqIFRPRE86IHVzZSBhZGRpdGlvbmFsIGluZm9ybWF0aW9uIHRvIGNyZWF0ZSBtdWx0aXBsZSBpbnN0YW5jZXNcbiAqIEByZXR1cm5zIHtPYmpUeXBlfVxuICovXG5GblR5cGUucHJvdG90eXBlLmdldEluc3RhbmNlID0gZnVuY3Rpb24gKCkge1xuICAgIC8vIG9iakluc3RhbmNlIGlzIHRoZSBvYmplY3QgbWFkZSBieSB0aGUgZnVuY3Rpb2FublxuICAgIGlmICh0aGlzLm9iakluc3RhbmNlKSByZXR1cm4gdGhpcy5vYmpJbnN0YW5jZTtcbiAgICAvLyB3ZSB1bmlmeSBjb25zdHJ1Y3RvcidzIC5wcm90b3R5cGUgYW5kIGluc3RhbmNlJ3MgX19wcm90b19fXG4gICAgdGhpcy5vYmpJbnN0YW5jZSA9IG5ldyBPYmpUeXBlKHRoaXMuZ2V0UHJvcCgncHJvdG90eXBlJykpO1xuICAgIHJldHVybiB0aGlzLm9iakluc3RhbmNlO1xufTtcblxuLyoqIFxuICogNC4gYXJyYXkgdHlwZXNcbiAqIEBjb25zdHJ1Y3RvclxuICovXG5mdW5jdGlvbiBBcnJUeXBlKGFycl9wcm90bykge1xuICAgIE9ialR5cGUuY2FsbCh0aGlzLCBhcnJfcHJvdG8sICdBcnJheScpO1xufVxuQXJyVHlwZS5wcm90b3R5cGUgPSBPYmplY3QuY3JlYXRlKE9ialR5cGUucHJvdG90eXBlKTtcblxuLy8gTWFrZSBwcmltaXRpdmUgdHlwZXNcbnZhciBQcmltTnVtYmVyID0gbmV3IFByaW1UeXBlKCdudW1iZXInKTtcbnZhciBQcmltU3RyaW5nID0gbmV3IFByaW1UeXBlKCdzdHJpbmcnKTtcbnZhciBQcmltQm9vbGVhbiA9IG5ldyBQcmltVHlwZSgnYm9vbGVhbicpO1xuXG4vLyBBYnNOdWxsIHJlcHJlc2VudHMgYWxsIGVtcHR5IGFic3RyYWN0IHZhbHVlcy5cbnZhciBBVmFsTnVsbCA9IG5ldyBBVmFsKCk7XG4vLyBZb3Ugc2hvdWxkIG5vdCBhZGQgYW55IHByb3BlcnRpZXMgdG8gaXQuXG5BVmFsTnVsbC5wcm9wcyA9IG51bGw7XG4vLyBBZGRpbmcgdHlwZXMgYXJlIGlnbm9yZWQuXG5BVmFsTnVsbC5hZGRUeXBlID0gZnVuY3Rpb24gKCkge307XG5cbmNsYXNzIEFic0NhY2hlIHtcbiAgICBjb25zdHJ1Y3RvcigpIHtcbiAgICAgICAgdGhpcy5tYXAgPSBuZXcgTWFwKCk7XG4gICAgfVxuXG4gICAgLyoqXG4gICAgICogR2V0IGlmIG9uZSBleGlzdHMsIGlmIG5vdCBjcmVhdGUgb25lXG4gICAgICogQHBhcmFtIGxvY1xuICAgICAqIEBwYXJhbSBjdHhcbiAgICAgKiBAcmV0dXJucyB7Kn1cbiAgICAgKi9cbiAgICBnZXQobG9jLCBjdHgpIHtcbiAgICAgICAgaWYgKCF0aGlzLm1hcC5oYXMobG9jKSkge1xuICAgICAgICAgICAgLy8gY3JlYXRlIGlubmVyIG1hcFxuICAgICAgICAgICAgdGhpcy5tYXAuc2V0KGxvYywgbmV3IE1hcCgpKTtcbiAgICAgICAgfVxuICAgICAgICBjb25zdCBtYXBMb2MgPSB0aGlzLm1hcC5nZXQobG9jKTtcbiAgICAgICAgaWYgKCFtYXBMb2MuaGFzKGN0eCkpIHtcbiAgICAgICAgICAgIGNvbnN0IGF2ID0gbmV3IEFWYWwoKTtcbiAgICAgICAgICAgIG1hcExvYy5zZXQoY3R4LCBhdik7XG4gICAgICAgICAgICByZXR1cm4gYXY7XG4gICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgICByZXR1cm4gbWFwTG9jLmdldChjdHgpO1xuICAgICAgICB9XG4gICAgfVxuXG4gICAgLyoqXG4gICAgICogVG8gdXNlIGF2IG1hZGUgYnkgb3RoZXJzIChlLmcuIHNjb3BlKVxuICAgICAqIEBwYXJhbSBsb2NcbiAgICAgKiBAcGFyYW0gY3R4XG4gICAgICogQHBhcmFtIGF2XG4gICAgICovXG4gICAgc2V0KGxvYywgY3R4LCBhdikge1xuICAgICAgICBpZiAoIXRoaXMubWFwLmhhcyhsb2MpKSB7XG4gICAgICAgICAgICAvLyBjcmVhdGUgaW5uZXIgbWFwXG4gICAgICAgICAgICB0aGlzLm1hcC5zZXQobG9jLCBuZXcgTWFwKCkpO1xuICAgICAgICB9XG4gICAgICAgIHRoaXMubWFwLmdldChsb2MpLnNldChjdHgsIGF2KTtcbiAgICB9XG5cbiAgICAvKipcbiAgICAgKiBDaGVjayB3aGV0aGVyIGl0IGhhcyBvbmUgZm9yIGxvYyBhbmQgY3R4XG4gICAgICogQHBhcmFtIGxvY1xuICAgICAqIEBwYXJhbSBjdHhcbiAgICAgKiBAcmV0dXJucyB7Ym9vbGVhbn1cbiAgICAgKi9cbiAgICBoYXMobG9jLCBjdHgpIHtcbiAgICAgICAgcmV0dXJuIHRoaXMubWFwLmhhcyhsb2MpICYmIHRoaXMubWFwLmdldChsb2MpLmhhcyhjdHgpO1xuICAgIH1cblxuICAgIC8qKlxuICAgICAqIEdldCBhbGwgdGhlIHR5cGVzIG9mIHRoZSBsb2NcbiAgICAgKiBAcGFyYW0gbG9jXG4gICAgICogQHJldHVybnMgW1R5cGVdXG4gICAgICovXG4gICAgZ2V0VHlwZU9mTG9jKGxvYykge1xuICAgICAgICBpZiAoIXRoaXMubWFwLmhhcyhsb2MpKSB7XG4gICAgICAgICAgICAvLyBubyB0eXBlIGlzIGF2YWlsYWJsZVxuICAgICAgICAgICAgcmV0dXJuIG51bGw7XG4gICAgICAgIH1cbiAgICAgICAgY29uc3QgdHBzID0gW107XG4gICAgICAgIGZvciAodmFyIGF2IG9mIHRoaXMubWFwLmdldChsb2MpLnZhbHVlcygpKSB7XG4gICAgICAgICAgICBmb3IgKHZhciB0cCBvZiBhdi5nZXRUeXBlcygpKSB7XG4gICAgICAgICAgICAgICAgaWYgKHRwcy5pbmRleE9mKHRwKSA9PT0gLTEpIHtcbiAgICAgICAgICAgICAgICAgICAgdHBzLnB1c2godHApO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgIH1cbiAgICAgICAgfVxuICAgICAgICByZXR1cm4gdHBzO1xuICAgIH1cbn1cblxuLy8gZXhwb3J0XG5leHBvcnRzLlR5cGUgPSBUeXBlO1xuZXhwb3J0cy5PYmpUeXBlID0gT2JqVHlwZTtcbmV4cG9ydHMuRm5UeXBlID0gRm5UeXBlO1xuZXhwb3J0cy5BcnJUeXBlID0gQXJyVHlwZTtcbmV4cG9ydHMuUHJpbU51bWJlciA9IFByaW1OdW1iZXI7XG5leHBvcnRzLlByaW1TdHJpbmcgPSBQcmltU3RyaW5nO1xuZXhwb3J0cy5QcmltQm9vbGVhbiA9IFByaW1Cb29sZWFuO1xuZXhwb3J0cy5ta09iakZyb21HbG9iYWxTY29wZSA9IG1rT2JqRnJvbUdsb2JhbFNjb3BlO1xuXG5leHBvcnRzLkFWYWwgPSBBVmFsO1xuZXhwb3J0cy5BVmFsTnVsbCA9IEFWYWxOdWxsO1xuXG5leHBvcnRzLkFic0NhY2hlID0gQWJzQ2FjaGU7XG4iLCIvLyBpbXBvcnQgbmVjZXNzYXJ5IGxpYnJhcmllc1xuY29uc3QgYWNvcm4gPSByZXF1aXJlKCdhY29ybi9kaXN0L2Fjb3JuJyk7XG5jb25zdCBhY29ybl9sb29zZSA9IHJlcXVpcmUoJ2Fjb3JuL2Rpc3QvYWNvcm5fbG9vc2UnKTtcbmNvbnN0IGF1eCA9IHJlcXVpcmUoJy4vYXV4Jyk7XG5jb25zdCB0eXBlcyA9IHJlcXVpcmUoJy4vZG9tYWlucy90eXBlcycpO1xuY29uc3QgY29udGV4dCA9IHJlcXVpcmUoJy4vZG9tYWlucy9jb250ZXh0Jyk7XG5jb25zdCBzdGF0dXMgPSByZXF1aXJlKCcuL2RvbWFpbnMvc3RhdHVzJyk7XG5jb25zdCB2YXJCbG9jayA9IHJlcXVpcmUoJy4vdmFyQmxvY2snKTtcbmNvbnN0IGNHZW4gPSByZXF1aXJlKCcuL2NvbnN0cmFpbnQvY0dlbicpO1xuY29uc3QgdmFyUmVmcyA9IHJlcXVpcmUoJy4vdmFycmVmcycpO1xuY29uc3QgcmV0T2NjdXIgPSByZXF1aXJlKCcuL3JldE9jY3VyJyk7XG5jb25zdCB0aGlzT2NjdXIgPSByZXF1aXJlKCcuL3RoaXNPY2N1cicpO1xuY29uc3QgbXlXYWxrZXIgPSByZXF1aXJlKCcuL3V0aWwvbXlXYWxrZXInKTtcblxuZnVuY3Rpb24gYW5hbHl6ZShpbnB1dCwgcmV0QWxsKSB7XG4gICAgLy8gdGhlIFNjb3BlIG9iamVjdCBmb3IgZ2xvYmFsIHNjb3BlXG4gICAgLy8gc2NvcGUuU2NvcGUuZ2xvYmFsU2NvcGUgPSBuZXcgc2NvcGUuU2NvcGUobnVsbCk7XG5cbiAgICAvLyBwYXJzaW5nIGlucHV0IHByb2dyYW1cbiAgICB2YXIgYXN0O1xuICAgIHRyeSB7XG4gICAgICAgIGFzdCA9IGFjb3JuLnBhcnNlKGlucHV0KTtcbiAgICB9IGNhdGNoIChlKSB7XG4gICAgICAgIGFzdCA9IGFjb3JuX2xvb3NlLnBhcnNlX2RhbW1pdChpbnB1dCk7XG4gICAgfVxuXG4gICAgdmFyIG5vZGVBcnJheUluZGV4ZWRCeUxpc3QgPSBhdXguZ2V0Tm9kZUxpc3QoYXN0KTtcblxuICAgIC8vIFNob3cgQVNUIGJlZm9yZSBzY29wZSByZXNvbHV0aW9uXG4gICAgLy8gYXV4LnNob3dVbmZvbGRlZChhc3QpO1xuXG4gICAgdmFyQmxvY2suYW5ub3RhdGVCbG9ja0luZm8oYXN0KTtcbiAgICB2YXIgZ0Jsb2NrID0gYXN0WydAYmxvY2snXTtcbiAgICB2YXIgaW5pdGlhbENvbnRleHQgPSBuZXcgY29udGV4dC5DYWxsU2l0ZUNvbnRleHQ7XG4gICAgdmFyIGdTY29wZSA9IGdCbG9jay5nZXRTY29wZUluc3RhbmNlKG51bGwsIGluaXRpYWxDb250ZXh0KTtcbiAgICB2YXIgZ09iamVjdCA9IHR5cGVzLm1rT2JqRnJvbUdsb2JhbFNjb3BlKGdTY29wZSk7XG4gICAgdmFyIGluaXRTdGF0dXMgPSBuZXcgc3RhdHVzLlN0YXR1cyhcbiAgICAgICAgZ09iamVjdCxcbiAgICAgICAgdHlwZXMuQVZhbE51bGwsXG4gICAgICAgIHR5cGVzLkFWYWxOdWxsLFxuICAgICAgICBpbml0aWFsQ29udGV4dCxcbiAgICAgICAgZ1Njb3BlKTtcbiAgICAvLyB0aGUgcHJvdG90eXBlIG9iamVjdCBvZiBPYmplY3RcbiAgICB2YXIgT2JqUHJvdG8gPSBuZXcgdHlwZXMuT2JqVHlwZShudWxsLCAnT2JqZWN0LnByb3RvdHlwZScpO1xuICAgIHZhciBydENYID0ge1xuICAgICAgICBnbG9iYWxPYmplY3Q6IGdPYmplY3QsXG4gICAgICAgIC8vIHRlbXBvcmFsXG4gICAgICAgIHByb3Rvczoge1xuICAgICAgICAgICAgT2JqZWN0OiBPYmpQcm90byxcbiAgICAgICAgICAgIEZ1bmN0aW9uOiBuZXcgdHlwZXMuT2JqVHlwZShuZXcgdHlwZXMuQVZhbChPYmpQcm90byksICdGdW5jdGlvbi5wcm90b3R5cGUnKSxcbiAgICAgICAgICAgIEFycmF5OiBuZXcgdHlwZXMuT2JqVHlwZShuZXcgdHlwZXMuQVZhbChPYmpQcm90byksICdBcnJheS5wcm90b3R5cGUnKSxcbiAgICAgICAgICAgIFJlZ0V4cDogbmV3IHR5cGVzLk9ialR5cGUobmV3IHR5cGVzLkFWYWwoT2JqUHJvdG8pLCAnUmVnRXhwLnByb3RvdHlwZScpLFxuICAgICAgICAgICAgU3RyaW5nOiBuZXcgdHlwZXMuT2JqVHlwZShuZXcgdHlwZXMuQVZhbChPYmpQcm90byksICdTdHJpbmcucHJvdG90eXBlJyksXG4gICAgICAgICAgICBOdW1iZXI6IG5ldyB0eXBlcy5PYmpUeXBlKG5ldyB0eXBlcy5BVmFsKE9ialByb3RvKSwgJ051bWJlci5wcm90b3R5cGUnKSxcbiAgICAgICAgICAgIEJvb2xlYW46IG5ldyB0eXBlcy5PYmpUeXBlKG5ldyB0eXBlcy5BVmFsKE9ialByb3RvKSwgJ0Jvb2xlYW4ucHJvdG90eXBlJylcbiAgICAgICAgfSxcbiAgICAgICAgxIg6IG5ldyB0eXBlcy5BYnNDYWNoZSgpXG4gICAgfTtcbiAgICBjR2VuLmFkZENvbnN0cmFpbnRzKGFzdCwgaW5pdFN0YXR1cywgcnRDWCk7XG4gICAgdmFyIGNvbnN0cmFpbnRzID0gY0dlbi5jb25zdHJhaW50cztcbiAgICAvL2F1eC5zaG93VW5mb2xkZWQoZ0Jsb2NrQW5kQW5ub3RhdGVkQVNULmFzdCk7XG4gICAgLy8gYXV4LnNob3dVbmZvbGRlZChjb25zdHJhaW50cyk7XG4gICAgLy8gYXV4LnNob3dVbmZvbGRlZChnQmxvY2spO1xuICAgIC8vIGNvbnNvbGUubG9nKHV0aWwuaW5zcGVjdChnQmxvY2ssIHtkZXB0aDogMTB9KSk7XG4gICAgaWYgKHJldEFsbCkge1xuICAgICAgICByZXR1cm4ge1xuICAgICAgICAgICAgZ09iamVjdDogZ09iamVjdCxcbiAgICAgICAgICAgIEFTVDogYXN0LFxuICAgICAgICAgICAgZ0Jsb2NrOiBnQmxvY2ssXG4gICAgICAgICAgICBnU2NvcGU6IGdTY29wZSxcbiAgICAgICAgICAgIMSIOiBydENYLsSIXG4gICAgICAgIH07XG4gICAgfSBlbHNlIHtcbiAgICAgICAgcmV0dXJuIGdPYmplY3Q7XG4gICAgfVxufVxuXG5leHBvcnRzLmFuYWx5emUgPSBhbmFseXplO1xuZXhwb3J0cy5maW5kSWRlbnRpZmllckF0ID0gdmFyUmVmcy5maW5kSWRlbnRpZmllckF0O1xuZXhwb3J0cy5maW5kVmFyUmVmc0F0ID0gdmFyUmVmcy5maW5kVmFyUmVmc0F0O1xuZXhwb3J0cy5vbkZ1bmN0aW9uT3JSZXR1cm5LZXl3b3JkID0gcmV0T2NjdXIub25GdW5jdGlvbk9yUmV0dXJuS2V5d29yZDtcbmV4cG9ydHMuZmluZFJldHVyblN0YXRlbWVudHMgPSByZXRPY2N1ci5maW5kUmV0dXJuU3RhdGVtZW50cztcbmV4cG9ydHMub25UaGlzS2V5d29yZCA9IHRoaXNPY2N1ci5vblRoaXNLZXl3b3JkO1xuZXhwb3J0cy5maW5kVGhpc0V4cHJlc3Npb25zID0gdGhpc09jY3VyLmZpbmRUaGlzRXhwcmVzc2lvbnM7XG5leHBvcnRzLmZpbmRTdXJyb3VuZGluZ05vZGUgPSBteVdhbGtlci5maW5kU3Vycm91bmRpbmdOb2RlOyIsImNvbnN0IHdhbGsgPSByZXF1aXJlKCdhY29ybi9kaXN0L3dhbGsnKTtcbmNvbnN0IG15V2Fsa2VyID0gcmVxdWlyZSgnLi91dGlsL215V2Fsa2VyJyk7XG5cbi8qKlxuICogQ2hlY2sgd2hldGhlciBnaXZlbiBwb3MgaXMgb24gYSBmdW5jdGlvbiBrZXl3b3JkXG4gKiBAcGFyYW0gYXN0IC0gQVNUIG9mIGEgcHJvZ3JhbVxuICogQHBhcmFtIHBvcyAtIGluZGV4IHBvc2l0aW9uXG4gKiBAcmV0dXJucyB7Kn0gLSBmdW5jdGlvbiBub2RlIG9yIG51bGxcbiAqL1xuZnVuY3Rpb24gb25GdW5jdGlvbk9yUmV0dXJuS2V5d29yZChhc3QsIHBvcykge1xuICAgIFwidXNlIHN0cmljdFwiO1xuXG4gICAgLy8gZmluZCBmdW5jdGlvbiBub2RlXG4gICAgLy8gc3QgaXMgdGhlIGVuY2xvc2luZyBmdW5jdGlvblxuICAgIGNvbnN0IHdhbGtlciA9IG15V2Fsa2VyLndyYXBXYWxrZXIod2Fsay5iYXNlLFxuICAgICAgICAvLyBwcmVcbiAgICAgICAgKG5vZGUsIHN0KSA9PiB7XG4gICAgICAgICAgICBpZiAobm9kZS5zdGFydCA+IHBvcyB8fCBub2RlLmVuZCA8IHBvcykge1xuICAgICAgICAgICAgICAgIHJldHVybiBmYWxzZTtcbiAgICAgICAgICAgIH1cblxuICAgICAgICAgICAgLy8gb24gYSBmdW5jdGlvbiBrZXl3b3JkLCA4IGlzIHRoZSBsZW5ndGggb2YgJ2Z1bmN0aW9uJ1xuICAgICAgICAgICAgLy8gb3Igb24gcmV0dXJuIGtleXdvcmQsIDYgaXMgdGhlIGxlbmd0aCBvZiAncmV0dXJuJ1xuICAgICAgICAgICAgaWYgKCgobm9kZS50eXBlID09PSAnRnVuY3Rpb25EZWNsYXJhdGlvbicgfHwgbm9kZS50eXBlID09PSAnRnVuY3Rpb25FeHByZXNzaW9uJylcbiAgICAgICAgICAgICAgICAmJiAobm9kZS5zdGFydCA8PSBwb3MgJiYgcG9zIDw9IG5vZGUuc3RhcnQgKyA4KSlcbiAgICAgICAgICAgICAgICB8fFxuICAgICAgICAgICAgICAgIChub2RlLnR5cGUgPT09ICdSZXR1cm5TdGF0ZW1lbnQnXG4gICAgICAgICAgICAgICAgJiYgKG5vZGUuc3RhcnQgPD0gcG9zICYmIHBvcyA8PSBub2RlLnN0YXJ0ICsgNikpKSB7XG4gICAgICAgICAgICAgICAgdGhyb3cgc3Q7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICByZXR1cm4gdHJ1ZTtcbiAgICAgICAgfSxcbiAgICAgICAgLy8gcG9zdFxuICAgICAgICB1bmRlZmluZWQsXG4gICAgICAgIC8vIHN0Q2hhbmdlXG4gICAgICAgIChub2RlLCBzdCkgPT4ge1xuICAgICAgICAgICAgaWYgKG5vZGUudHlwZSA9PT0gJ0Z1bmN0aW9uRGVjbGFyYXRpb24nXG4gICAgICAgICAgICAgICAgfHwgbm9kZS50eXBlID09PSAnRnVuY3Rpb25FeHByZXNzaW9uJykge1xuICAgICAgICAgICAgICAgIHJldHVybiBub2RlO1xuICAgICAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICAgICAgICByZXR1cm4gc3Q7XG4gICAgICAgICAgICB9XG4gICAgICAgIH0pO1xuXG4gICAgdHJ5IHtcbiAgICAgICAgd2Fsay5yZWN1cnNpdmUoYXN0LCB1bmRlZmluZWQsIHdhbGtlcik7XG4gICAgfSBjYXRjaCAoZSkge1xuICAgICAgICBpZiAoZSAmJiBlLnR5cGUgJiZcbiAgICAgICAgICAgIChlLnR5cGUgPT09ICdGdW5jdGlvbkV4cHJlc3Npb24nXG4gICAgICAgICAgICB8fCBlLnR5cGUgPT09ICdGdW5jdGlvbkRlY2xhcmF0aW9uJykpIHtcbiAgICAgICAgICAgIHJldHVybiBlO1xuICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgICAgdGhyb3cgZTtcbiAgICAgICAgfVxuICAgIH1cbiAgICAvLyBpZGVudGlmaWVyIG5vdCBmb3VuZFxuICAgIHJldHVybiBudWxsO1xufVxuXG4vKipcbiAqIEdpdmVuIGEgZnVuY3Rpb24gbm9kZSwgZmluZCBpdHMgcmV0dXJuIG5vZGVzXG4gKlxuICogQHBhcmFtIGZOb2RlIC0gQVNUIG5vZGUgb2YgYSBmdW5jdGlvbiwgcG9zc2libHkgd2l0aCBubyBhbm5vdGF0aW9uXG4gKiBAcmV0dXJucyB7Kn0gLSBhcnJheSBvZiBBU1Qgbm9kZXNcbiAqL1xuZnVuY3Rpb24gZ2V0UmV0dXJuTm9kZXMoZk5vZGUpIHtcbiAgICBcInVzZSBzdHJpY3RcIjtcbiAgICBjb25zdCByZXRzID0gW107XG4gICAgaWYgKGZOb2RlLnR5cGUgIT09ICdGdW5jdGlvbkV4cHJlc3Npb24nXG4gICAgICAgICYmIGZOb2RlLnR5cGUgIT09ICdGdW5jdGlvbkRlY2xhcmF0aW9uJykge1xuICAgICAgICB0aHJvdyBFcnJvcignZk5vZGUgc2hvdWxkIGJlIGEgZnVuY3Rpb24gbm9kZScpO1xuICAgIH1cblxuICAgIGNvbnN0IHdhbGtlciA9IHdhbGsubWFrZSh7XG4gICAgICAgIFJldHVyblN0YXRlbWVudDogKG5vZGUpID0+IHtcbiAgICAgICAgICAgIHJldHVybiByZXRzLnB1c2gobm9kZSk7XG4gICAgICAgIH0sXG4gICAgICAgIEZ1bmN0aW9uOiAoKSA9PiB7XG4gICAgICAgICAgICAvLyBub3QgdmlzaXQgaW5uZXIgZnVuY3Rpb25zXG4gICAgICAgIH1cbiAgICB9LCB3YWxrLmJhc2UpO1xuXG4gICAgd2Fsay5yZWN1cnNpdmUoZk5vZGUuYm9keSwgdW5kZWZpbmVkLCB3YWxrZXIpO1xuXG4gICAgcmV0dXJuIHJldHM7XG59XG5cbi8qKlxuICogRmluZCByZXR1cm4gbm9kZXMgY29ycmVzcG9uZGluZyB0byB0aGUgcG9zaXRpb25cbiAqIGlmIHRoZSBwb3MgaXMgb24gYSBmdW5jdGlvbiBrZXl3b3JkXG4gKlxuICogQHBhcmFtIGFzdCAtIEFTVCBub2RlIG9mIGEgcHJvZ3JhbSwgcG9zc2libHkgd2l0aCBubyBhbm5vdGF0aW9uXG4gKiBAcGFyYW0gcG9zIC0gY3Vyc29yIHBvc2l0aW9uXG4gKiBAcGFyYW0gaW5jbHVkZUZ1bmN0aW9uS2V5d29yZCAtIHdoZXRoZXIgdG8gaW5jbHVkZSBmdW5jdGlvbiBrZXl3b3JkIHJhbmdlXG4gKiBAcmV0dXJucyB7QXJyYXl9IC0gYXJyYXkgb2YgQVNUIG5vZGVzIG9mIHJldHVybiBzdGF0ZW1lbnRzXG4gKi9cbmZ1bmN0aW9uIGZpbmRSZXR1cm5TdGF0ZW1lbnRzKGFzdCwgcG9zLCBpbmNsdWRlRnVuY3Rpb25LZXl3b3JkKSB7XG4gICAgXCJ1c2Ugc3RyaWN0XCI7XG5cbiAgICBjb25zdCBmTm9kZSA9IG9uRnVuY3Rpb25PclJldHVybktleXdvcmQoYXN0LCBwb3MpO1xuICAgIGlmICghZk5vZGUpIHtcbiAgICAgICAgLy8gcG9zIGlzIG5vdCBvbiBmdW5jdGlvbiBrZXl3b3JkXG4gICAgICAgIHJldHVybiBudWxsO1xuICAgIH1cblxuICAgIGNvbnN0IHJldHMgPSBnZXRSZXR1cm5Ob2RlcyhmTm9kZSk7XG4gICAgLy8gd2hlbiBmdW5jdGlvbiBkb2VzIG5vdCBoYXZlIHJldHVybiBzdGF0ZW1lbnRzLFxuICAgIC8vIGluZGljYXRlIGl0IGJ5IHRoZSBjbG9zaW5nIGJyYWNlIG9mIHRoZSBmdW5jdGlvbiBib2R5XG4gICAgaWYgKHJldHMubGVuZ3RoID09PSAwKSB7XG4gICAgICAgIHJldHMucHVzaCh7c3RhcnQ6IGZOb2RlLmVuZCAtIDEsIGVuZDogZk5vZGUuZW5kfSk7XG4gICAgfVxuICAgIGlmIChpbmNsdWRlRnVuY3Rpb25LZXl3b3JkKSB7XG4gICAgICAgIHJldHMucHVzaCh7c3RhcnQ6IGZOb2RlLnN0YXJ0LCBlbmQ6IGZOb2RlLnN0YXJ0ICsgOH0pO1xuICAgIH1cbiAgICByZXR1cm4gcmV0cztcbn1cblxuZXhwb3J0cy5vbkZ1bmN0aW9uT3JSZXR1cm5LZXl3b3JkID0gb25GdW5jdGlvbk9yUmV0dXJuS2V5d29yZDtcbmV4cG9ydHMuZmluZFJldHVyblN0YXRlbWVudHMgPSBmaW5kUmV0dXJuU3RhdGVtZW50czsiLCJjb25zdCB3YWxrID0gcmVxdWlyZSgnYWNvcm4vZGlzdC93YWxrJyk7XG5jb25zdCBteVdhbGtlciA9IHJlcXVpcmUoJy4vdXRpbC9teVdhbGtlcicpO1xuXG4vKipcbiAqIENoZWNrIHdoZXRoZXIgZ2l2ZW4gcG9zIGlzIG9uIGEgdGhpcyBrZXl3b3JkXG4gKiBAcGFyYW0gYXN0IC0gQVNUIG9mIGEgcHJvZ3JhbVxuICogQHBhcmFtIHBvcyAtIGluZGV4IHBvc2l0aW9uXG4gKiBAcmV0dXJucyB7Kn0gLSBmdW5jdGlvbiBub2RlIG9yIG51bGxcbiAqL1xuZnVuY3Rpb24gb25UaGlzS2V5d29yZChhc3QsIHBvcykge1xuICAgIFwidXNlIHN0cmljdFwiO1xuXG4gICAgLy8gZmluZCBmdW5jdGlvbiBub2RlXG4gICAgLy8gc3QgaXMgdGhlIGVuY2xvc2luZyBmdW5jdGlvblxuICAgIGNvbnN0IHdhbGtlciA9IG15V2Fsa2VyLndyYXBXYWxrZXIod2Fsay5iYXNlLFxuICAgICAgICAvLyBwcmVcbiAgICAgICAgKG5vZGUsIHN0KSA9PiB7XG4gICAgICAgICAgICBpZiAobm9kZS5zdGFydCA+IHBvcyB8fCBub2RlLmVuZCA8IHBvcykge1xuICAgICAgICAgICAgICAgIHJldHVybiBmYWxzZTtcbiAgICAgICAgICAgIH1cblxuICAgICAgICAgICAgaWYgKG5vZGUudHlwZSA9PT0gJ1RoaXNFeHByZXNzaW9uJykge1xuICAgICAgICAgICAgICAgIHRocm93IHN0O1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgcmV0dXJuIHRydWU7XG4gICAgICAgIH0sXG4gICAgICAgIC8vIHBvc3RcbiAgICAgICAgdW5kZWZpbmVkLFxuICAgICAgICAvLyBzdENoYW5nZVxuICAgICAgICAobm9kZSwgc3QpID0+IHtcbiAgICAgICAgICAgIGlmIChub2RlLnR5cGUgPT09ICdGdW5jdGlvbkRlY2xhcmF0aW9uJ1xuICAgICAgICAgICAgICAgIHx8IG5vZGUudHlwZSA9PT0gJ0Z1bmN0aW9uRXhwcmVzc2lvbicpIHtcbiAgICAgICAgICAgICAgICByZXR1cm4gbm9kZTtcbiAgICAgICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgICAgICAgcmV0dXJuIHN0O1xuICAgICAgICAgICAgfVxuICAgICAgICB9KTtcblxuICAgIHRyeSB7XG4gICAgICAgIHdhbGsucmVjdXJzaXZlKGFzdCwgdW5kZWZpbmVkLCB3YWxrZXIpO1xuICAgIH0gY2F0Y2ggKGUpIHtcbiAgICAgICAgaWYgKGUgJiYgZS50eXBlICYmXG4gICAgICAgICAgICAoZS50eXBlID09PSAnRnVuY3Rpb25FeHByZXNzaW9uJ1xuICAgICAgICAgICAgfHwgZS50eXBlID09PSAnRnVuY3Rpb25EZWNsYXJhdGlvbicpKSB7XG4gICAgICAgICAgICByZXR1cm4gZTtcbiAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICAgIHRocm93IGU7XG4gICAgICAgIH1cbiAgICB9XG4gICAgLy8gaWRlbnRpZmllciBub3QgZm91bmRcbiAgICByZXR1cm4gbnVsbDtcbn1cblxuLyoqXG4gKiBHaXZlbiBhIGZ1bmN0aW9uIG5vZGUsIGZpbmQgaXRzIHRoaXMgbm9kZXNcbiAqXG4gKiBAcGFyYW0gZk5vZGUgLSBBU1Qgbm9kZSBvZiBhIGZ1bmN0aW9uLCBwb3NzaWJseSB3aXRoIG5vIGFubm90YXRpb25cbiAqIEByZXR1cm5zIHsqfSAtIGFycmF5IG9mIEFTVCBub2Rlc1xuICovXG5mdW5jdGlvbiBnZXRUaGlzTm9kZXMoZk5vZGUpIHtcbiAgICBcInVzZSBzdHJpY3RcIjtcbiAgICBjb25zdCByZXRzID0gW107XG4gICAgaWYgKGZOb2RlLnR5cGUgIT09ICdGdW5jdGlvbkV4cHJlc3Npb24nXG4gICAgICAgICYmIGZOb2RlLnR5cGUgIT09ICdGdW5jdGlvbkRlY2xhcmF0aW9uJykge1xuICAgICAgICB0aHJvdyBFcnJvcignZk5vZGUgc2hvdWxkIGJlIGEgZnVuY3Rpb24gbm9kZScpO1xuICAgIH1cblxuICAgIGNvbnN0IHdhbGtlciA9IHdhbGsubWFrZSh7XG4gICAgICAgIFRoaXNFeHByZXNzaW9uOiAobm9kZSkgPT4ge1xuICAgICAgICAgICAgcmV0dXJuIHJldHMucHVzaChub2RlKTtcbiAgICAgICAgfSxcbiAgICAgICAgRnVuY3Rpb246ICgpID0+IHtcbiAgICAgICAgICAgIC8vIG5vdCB2aXNpdCBpbm5lciBmdW5jdGlvbnNcbiAgICAgICAgfVxuICAgIH0sIHdhbGsuYmFzZSk7XG5cbiAgICB3YWxrLnJlY3Vyc2l2ZShmTm9kZS5ib2R5LCB1bmRlZmluZWQsIHdhbGtlcik7XG5cbiAgICByZXR1cm4gcmV0cztcbn1cblxuLyoqXG4gKiBGaW5kIHRoaXMgbm9kZXMgaWYgdGhlIHBvcyBpcyBvbiBhIHRoaXMga2V5d29yZFxuICpcbiAqIEBwYXJhbSBhc3QgLSBBU1Qgbm9kZSBvZiBhIHByb2dyYW0sIHBvc3NpYmx5IHdpdGggbm8gYW5ub3RhdGlvblxuICogQHBhcmFtIHBvcyAtIGN1cnNvciBwb3NpdGlvblxuICogQHBhcmFtIGluY2x1ZGVGdW5jdGlvbktleXdvcmQgLSB3aGV0aGVyIHRvIGluY2x1ZGUgZnVuY3Rpb24ga2V5d29yZCByYW5nZVxuICogQHJldHVybnMge0FycmF5fSAtIGFycmF5IG9mIEFTVCBub2RlcyBvZiByZXR1cm4gc3RhdGVtZW50c1xuICovXG5mdW5jdGlvbiBmaW5kVGhpc0V4cHJlc3Npb25zKGFzdCwgcG9zLCBpbmNsdWRlRnVuY3Rpb25LZXl3b3JkKSB7XG4gICAgXCJ1c2Ugc3RyaWN0XCI7XG5cbiAgICBjb25zdCBmTm9kZSA9IG9uVGhpc0tleXdvcmQoYXN0LCBwb3MpO1xuICAgIGlmICghZk5vZGUpIHtcbiAgICAgICAgLy8gcG9zIGlzIG5vdCBvbiB0aGlzIGtleXdvcmRcbiAgICAgICAgcmV0dXJuIG51bGw7XG4gICAgfVxuXG4gICAgY29uc3QgcmV0cyA9IGdldFRoaXNOb2RlcyhmTm9kZSk7XG4gICAgaWYgKGluY2x1ZGVGdW5jdGlvbktleXdvcmQpIHtcbiAgICAgICAgcmV0cy5wdXNoKHtzdGFydDogZk5vZGUuc3RhcnQsIGVuZDogZk5vZGUuc3RhcnQgKyA4fSk7XG4gICAgfVxuICAgIHJldHVybiByZXRzO1xufVxuXG5leHBvcnRzLm9uVGhpc0tleXdvcmQgPSBvblRoaXNLZXl3b3JkO1xuZXhwb3J0cy5maW5kVGhpc0V4cHJlc3Npb25zID0gZmluZFRoaXNFeHByZXNzaW9uczsiLCJjb25zdCB3YWxrID0gcmVxdWlyZSgnYWNvcm4vZGlzdC93YWxrJyk7XG5cbi8qKlxuICogYSB3YWxrZXIgdGhhdCB2aXNpdHMgZWFjaCBpZCBldmVuIHRob3VnaCBpdCBpcyB2YXIgZGVjbGFyYXRpb25cbiAqIHRoZSBwYXJhbWV0ZXIgdmIgZGVub3RlIHZhckJsb2NrXG4gKi9cbmNvbnN0IHZhcldhbGtlcj0gd2Fsay5tYWtlKHtcbiAgICBGdW5jdGlvbjogZnVuY3Rpb24gKG5vZGUsIHZiLCBjKSB7XG4gICAgICAgICd1c2Ugc3RyaWN0JztcbiAgICAgICAgY29uc3QgaW5uZXJWYiA9IG5vZGUuYm9keVsnQGJsb2NrJ107XG4gICAgICAgIGlmIChub2RlLmlkKSBjKG5vZGUuaWQsIGlubmVyVmIpO1xuICAgICAgICBmb3IgKGxldCBpID0gMDsgaSA8IG5vZGUucGFyYW1zLmxlbmd0aDsgaSsrKVxuICAgICAgICAgICAgYyhub2RlLnBhcmFtc1tpXSwgaW5uZXJWYik7XG4gICAgICAgIGMobm9kZS5ib2R5LCBpbm5lclZiKTtcbiAgICB9LFxuICAgIFRyeVN0YXRlbWVudDogZnVuY3Rpb24gKG5vZGUsIHZiLCBjKSB7XG4gICAgICAgIGMobm9kZS5ibG9jaywgdmIpO1xuICAgICAgICBpZiAobm9kZS5oYW5kbGVyKSB7XG4gICAgICAgICAgICBjKG5vZGUuaGFuZGxlciwgdmIpO1xuICAgICAgICB9XG4gICAgICAgIGlmIChub2RlLmZpbmFsaXplcikge1xuICAgICAgICAgICAgYyhub2RlLmZpbmFsaXplciwgdmIpO1xuICAgICAgICB9XG4gICAgfSxcbiAgICBDYXRjaENsYXVzZTogZnVuY3Rpb24gKG5vZGUsIHZiLCBjKSB7XG4gICAgICAgIGNvbnN0IGNhdGNoVmIgPSBub2RlLmJvZHlbJ0BibG9jayddO1xuICAgICAgICBjKG5vZGUucGFyYW0sIGNhdGNoVmIpO1xuICAgICAgICBjKG5vZGUuYm9keSwgY2F0Y2hWYik7XG4gICAgfSxcbiAgICBWYXJpYWJsZURlY2xhcmF0aW9uOiBmdW5jdGlvbiAobm9kZSwgdmIsIGMpIHtcbiAgICAgICAgJ3VzZSBzdHJpY3QnO1xuICAgICAgICBmb3IgKGxldCBpID0gMDsgaSA8IG5vZGUuZGVjbGFyYXRpb25zLmxlbmd0aDsgKytpKSB7XG4gICAgICAgICAgICBjb25zdCBkZWNsID0gbm9kZS5kZWNsYXJhdGlvbnNbaV07XG4gICAgICAgICAgICBjKGRlY2wuaWQsIHZiKTtcbiAgICAgICAgICAgIGlmIChkZWNsLmluaXQpIGMoZGVjbC5pbml0LCB2Yik7XG4gICAgICAgIH1cbiAgICB9XG59KTtcblxuLyoqXG4gKiBXcmFwIGEgd2Fsa2VyIHdpdGggcHJlLSBhbmQgcG9zdC0gYWN0aW9uc1xuICpcbiAqIEBwYXJhbSBwcmVOb2RlIC0gQXBwbHkgYmVmb3JlIHZpc2l0aW5nIHRoZSBjdXJyZW50IG5vZGUuXG4gKiBJZiByZXR1cm5zIGZhbHNlLCBkbyBub3QgdmlzaXQgdGhlIG5vZGUuXG4gKiBAcGFyYW0gcG9zdE5vZGUgLSBBcHBseSBhZnRlciB2aXNpdGluZyB0aGUgY3VycmVudCBub2RlLlxuICogSWYgZ2l2ZW4sIHJldHVybiB2YWx1ZXMgYXJlIG92ZXJyaWRkZW4uXG4gKiBAcmV0dXJucyB7Kn0gLSBhIG5ldyB3YWxrZXJcbiAqL1xuZnVuY3Rpb24gd3JhcFdhbGtlcih3YWxrZXIsIHByZU5vZGUsIHBvc3ROb2RlLCBzdENoYW5nZSkge1xuICAgICd1c2Ugc3RyaWN0JztcbiAgICBjb25zdCByZXRXYWxrZXIgPSB7fTtcbiAgICAvLyB3cmFwcGluZyBlYWNoIGZ1bmN0aW9uIHByZU5vZGUgYW5kIHBvc3ROb2RlXG4gICAgZm9yIChsZXQgbm9kZVR5cGUgaW4gd2Fsa2VyKSB7XG4gICAgICAgIGlmICghd2Fsa2VyLmhhc093blByb3BlcnR5KG5vZGVUeXBlKSkge1xuICAgICAgICAgICAgY29udGludWU7XG4gICAgICAgIH1cbiAgICAgICAgcmV0V2Fsa2VyW25vZGVUeXBlXSA9IChub2RlLCBzdCwgYykgPT4ge1xuICAgICAgICAgICAgbGV0IHJldDtcbiAgICAgICAgICAgIGxldCBuZXdTdCA9IHN0O1xuICAgICAgICAgICAgaWYgKHN0Q2hhbmdlKSB7XG4gICAgICAgICAgICAgICAgbmV3U3QgPSBzdENoYW5nZShub2RlLCBzdCk7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBpZiAoIXByZU5vZGUgfHwgcHJlTm9kZShub2RlLCBuZXdTdCwgYykpIHtcbiAgICAgICAgICAgICAgICByZXQgPSB3YWxrZXJbbm9kZVR5cGVdKG5vZGUsIG5ld1N0LCBjKTtcbiAgICAgICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgICAgICAgcmV0dXJuO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgaWYgKHBvc3ROb2RlKSB7XG4gICAgICAgICAgICAgICAgcmV0ID0gcG9zdE5vZGUobm9kZSwgbmV3U3QsIGMpO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgcmV0dXJuIHJldDtcbiAgICAgICAgfVxuICAgIH1cbiAgICByZXR1cm4gcmV0V2Fsa2VyO1xufVxuXG5cbmZ1bmN0aW9uIGZpbmRTdXJyb3VuZGluZ05vZGUoYXN0LCBzdGFydCwgZW5kKSB7XG4gICAgXCJ1c2Ugc3RyaWN0XCI7XG4gICAgZnVuY3Rpb24gRm91bmQobm9kZSkge1xuICAgICAgICB0aGlzLm5vZGUgPSBub2RlO1xuICAgIH1cblxuICAgIGNvbnN0IHdhbGtlciA9IHdyYXBXYWxrZXIodmFyV2Fsa2VyLFxuICAgICAgICBub2RlID0+ICEobm9kZS5zdGFydCA+IHN0YXJ0IHx8IG5vZGUuZW5kIDwgZW5kKSxcbiAgICAgICAgbm9kZSA9PiB7IHRocm93IG5ldyBGb3VuZChub2RlKTsgfVxuICAgICk7XG5cbiAgICB0cnkge1xuICAgICAgICB3YWxrLnJlY3Vyc2l2ZShhc3QsIHVuZGVmaW5lZCwgd2Fsa2VyKTtcbiAgICB9IGNhdGNoIChlKSB7XG4gICAgICAgIGlmIChlIGluc3RhbmNlb2YgRm91bmQpIHtcbiAgICAgICAgICAgIHJldHVybiBlLm5vZGU7XG4gICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgICB0aHJvdyBlO1xuICAgICAgICB9XG4gICAgfVxuICAgIC8vIG5vZGUgbm90IGZvdW5kXG4gICAgcmV0dXJuIG51bGw7XG59XG5cbmV4cG9ydHMud3JhcFdhbGtlciA9IHdyYXBXYWxrZXI7XG5leHBvcnRzLnZhcldhbGtlciA9IHZhcldhbGtlcjtcbmV4cG9ydHMuZmluZFN1cnJvdW5kaW5nTm9kZSA9IGZpbmRTdXJyb3VuZGluZ05vZGU7IiwiLypcbiBKYXZhU2NyaXB064qUIGdsb2JhbCwgZnVuY3Rpb24gYmxvY2ssIGNhdGNoIGJsb2Nr7JeQIOuzgOyImOqwgCDri6zrprDri6QuXG4gRVM264qUIOydvOuwmCBibG9ja+yXkOuPhCDri6zrprDri6QuXG5cbiBWYXJCbG9ja+uKlCDqsIEgYmxvY2vsl5Ag64us66awIOuzgOyImOuTpOydhCDrgpjtg4Drgrjri6QuXG4gLSBwYXJlbiAgICAgIDogQmxvY2tWYXJzLCDrsJTquaUgYmxvY2vsnYQg64KY7YOA64K064qUIOqwneyytFxuIC0gb3JpZ2luTGFiZWw6IG51bWJlciwg7ZW064u5IEJsb2NrVmFyc+qwgCDshKDslrjrkJwgQVNUIG5vZGXsnZggQGxhYmVsXG4gICAgb3JpZ2lu7J20IOuQoCDsiJgg7J6I64qUIG5vZGXripRcbiAgICBGdW5jdGlvbi5ib2R5LCBDYXRjaENsYXVzZS5ibG9jayDrkZDqsIDsp4Dri6QuXG4gICAg65GQ6rCA7KeAIOuqqOuRkCBCbG9ja1N0YXRlbWVudOydtOuLpC5cbiAtIGlzQ2F0Y2ggICAgOiBib29sZWFuLFxuICAgKiB0cnVlICAtPiBjYXRjaCBibG9ja1xuICAgKiBmYWxzZSAtPiBmdW5jdGlvbiBibG9jaywgb3IgZ2xvYmFsXG5cbiAtIHBhcmFtVmFyTmFtZXMgOiDrp6TqsJzrs4DsiJgg7J2066aEIOuqqeuhnSwg66ek6rCcIOuzgOyImCDsiJzshJzrjIDroZxcbiAtIGxvY2FsVmFyTmFtZXMgOiDsp4Dsl60g67OA7IiYIOydtOumhCDrqqnroZ0sIOyInOyEnCDrrLTsnZjrr7hcbiAgICBhcmd1bWVudHPrpbwg7IKs7Jqp7ZWY64qUIOqyveyasCBsb2NhbFZhck5hbWVz7JeQIOuTseyepe2VmOqzoCxcbiAgICBhcmd1bWVudHMgb2JqZWN066W8IOyCrOyaqe2VmOuptCB1c2VBcmd1bWVudHNPYmplY3QgPT0gdHJ1ZVxuXG4gLSAob3B0aW9uYWwpIHVzZUFyZ3VtZW50c09iamVjdDogYm9vbGVhblxuICAgIO2VqOyImCBib2R5IGJsb2Nr7J24IOqyveyasOyXkOunjCDsgqzsmqkg6rCA64qlXG4gICAgKiB0cnVlICA6IGFyZ3VtZW50cyBvYmplY3TqsIAg7IKs7Jqp65CY7JeI64ukLlxuICAgICAg7KaJIO2VqOyImCBib2R57JeQ7IScIOuzgOyImCBhcmd1bWVudHPrpbwg7ISg7Ja4IOyXhuydtCDsgqzsmqntlojri6QuXG4gICAgICDsnbQg6rK97JqwLCBhcmd1bWVudHPripQg7ZWo7IiY7J2YIOyngOyXrSDrs4DsiJjroZwg65Ox66Gd65Cc64ukLlxuICAgICogZmFsc2Ug7J24IOqyveyasOuKlCDsl4bri6QuIOq3uOuftOqxsOuptCDslYTsmIgg67OA7IiYIOyekOyytOqwgCDsl4bri6QuXG5cbiAtIHVzZWRWYXJpYWJsZXMgOiDqsIEgYmxvY2vsnZgg66ek6rCc67OA7IiYLCDsp4Dsl63rs4DsiJgg7KSRXG4gICDsgqzsmqnrkJjripQg7JyE7LmY6rCAIOyeiOuKlCDqsoPrk6TsnZgg66qp66GdXG5cbiAtIGluc3RhbmNlcyA6IERlbHRhIC0+IFZhckJsb2Nr7J2YIOuzgOyImOuTpCAtPiBBVmFsXG4gICBnZXRJbnN0YW5jZShkZWx0YSkg66W8IO2Gte2VtCDqsJnsnYAgZGVsdGHripQg6rCZ7J2AIG1hcHBpbmcg7KO86rKMIOunjOuTrFxuXG4gLSBzY29wZUluc3RhbmNlcyA6IFtTY29wZV1cbiAgIO2YhOyerCBWYXJCbG9ja+ydhCDrp4jsp4Drp4nsnLzroZwg7ZWY64qUIFNjb3Bl66W8IOuqqOuRkCDrqqjsnYDri6QuXG4gICBnZXRTY29wZUluc3RhbmNlKGRlbHRhLCBwYXJlbikg7J2EIO2Gte2VtCDqsJnsnYAgc2NvcGUgY2hhaW7snYBcbiAgIOqwmeydgCDqsJ3ssrTqsIAg65CY64+E66GdIOunjOuToOuLpC5cbiovXG4ndXNlIHN0cmljdCc7XG5cbnZhciB0eXBlcyA9IHJlcXVpcmUoJy4vZG9tYWlucy90eXBlcycpO1xudmFyIHdhbGsgPSByZXF1aXJlKCdhY29ybi9kaXN0L3dhbGsnKTtcbnZhciBhdXggPSByZXF1aXJlKCcuL2F1eCcpO1xuXG5mdW5jdGlvbiBWYXJCbG9jayhwYXJlbiwgb3JpZ2luTm9kZSwgaXNDYXRjaCkge1xuICAgIHRoaXMucGFyZW4gPSBwYXJlbjtcbiAgICB0aGlzLm9yaWdpbk5vZGUgPSBvcmlnaW5Ob2RlO1xuICAgIHRoaXMub3JpZ2luTGFiZWwgPSBvcmlnaW5Ob2RlWydAbGFiZWwnXTtcbiAgICB0aGlzLmlzQ2F0Y2ggPSBpc0NhdGNoO1xuICAgIHRoaXMucGFyYW1WYXJOYW1lcyA9IFtdO1xuICAgIHRoaXMubG9jYWxWYXJOYW1lcyA9IFtdO1xuXG4gICAgdGhpcy51c2VkVmFyaWFibGVzID0gW107XG4gICAgLy8gdGhpcy51c2VBcmd1bWVudHNPYmplY3RcbiAgICB0aGlzLmluc3RhbmNlcyA9IE9iamVjdC5jcmVhdGUobnVsbCk7XG4gICAgdGhpcy5zY29wZUluc3RhbmNlcyA9IFtdO1xufVxuXG5WYXJCbG9jay5wcm90b3R5cGUgPSBPYmplY3QuY3JlYXRlKG51bGwpO1xuXG5WYXJCbG9jay5wcm90b3R5cGUuaXNHbG9iYWwgPSBmdW5jdGlvbiAoKSB7XG4gICAgcmV0dXJuIHRoaXMucGFyZW4gPT0gbnVsbDtcbn07XG5WYXJCbG9jay5wcm90b3R5cGUuaXNGdW5jdGlvbiA9IGZ1bmN0aW9uICgpIHtcbiAgICByZXR1cm4gdGhpcy5wYXJlbiAhPSBudWxsICYmIHRoaXMubG9jYWxWYXJOYW1lcyAhPSBudWxsO1xufTtcblZhckJsb2NrLnByb3RvdHlwZS5pc0NhdGNoQmxvY2sgPSBmdW5jdGlvbiAoKSB7XG4gICAgcmV0dXJuIHRoaXMuaXNDYXRjaDtcbn07XG5cblZhckJsb2NrLnByb3RvdHlwZS5nZXRMb2NhbFZhck5hbWVzID0gZnVuY3Rpb24gKCkge1xuICAgIHJldHVybiB0aGlzLmxvY2FsVmFyTmFtZXM7XG59O1xuVmFyQmxvY2sucHJvdG90eXBlLmdldFBhcmFtVmFyTmFtZXMgPSBmdW5jdGlvbiAoKSB7XG4gICAgcmV0dXJuIHRoaXMucGFyYW1WYXJOYW1lcztcbn07XG5WYXJCbG9jay5wcm90b3R5cGUuaGFzTG9jYWxWYXIgPSBmdW5jdGlvbiAodmFyTmFtZSkge1xuICAgIHJldHVybiB0aGlzLmxvY2FsVmFyTmFtZXMgJiYgdGhpcy5sb2NhbFZhck5hbWVzLmluZGV4T2YodmFyTmFtZSkgPiAtMTtcbn07XG5WYXJCbG9jay5wcm90b3R5cGUuaGFzUGFyYW1WYXIgPSBmdW5jdGlvbiAodmFyTmFtZSkge1xuICAgIHJldHVybiB0aGlzLnBhcmFtVmFyTmFtZXMuaW5kZXhPZih2YXJOYW1lKSA+IC0xO1xufTtcblZhckJsb2NrLnByb3RvdHlwZS5oYXNWYXIgPSBmdW5jdGlvbiAodmFyTmFtZSkge1xuICAgIHJldHVybiB0aGlzLmhhc1BhcmFtVmFyKHZhck5hbWUpIHx8IHRoaXMuaGFzTG9jYWxWYXIodmFyTmFtZSk7XG59O1xuXG5WYXJCbG9jay5wcm90b3R5cGUuYWRkRGVjbGFyZWRMb2NhbFZhciA9IGZ1bmN0aW9uICh2YXJOYW1lLCBpc0Z1bkRlY2wpIHtcbiAgICB2YXIgY3VyckJsb2NrID0gdGhpcztcbiAgICAvLyBwZWVsIG9mZiBpbml0aWFsIGNhdGNoIGJsb2Nrc1xuICAgIC8vIGZvciBmdW5jdGlvbiBkZWNsLCBza2lwIGFueSBjYXRjaCBibG9ja3MsXG4gICAgLy8gZm9yIHZhcmlhYmxlIGRlY2wsIHNraXAgY2F0Y2ggYmxvY2sgd2l0aCBkaWZmZXJlbnQgdmFyTmFtZS5cbiAgICB3aGlsZSAoY3VyckJsb2NrLmlzQ2F0Y2hCbG9jaygpICYmXG4gICAgICAgICAgIChpc0Z1bkRlY2wgfHwgIWN1cnJCbG9jay5oYXNQYXJhbVZhcih2YXJOYW1lKSkpIHtcbiAgICAgICAgY3VyckJsb2NrID0gY3VyckJsb2NrLnBhcmVuO1xuICAgIH1cbiAgICAvLyBpZiBhbHJlYWR5IGFkZGVkLCBkbyBub3QgYWRkXG4gICAgaWYgKCFjdXJyQmxvY2suaGFzVmFyKHZhck5hbWUpKSB7XG4gICAgICAgIGN1cnJCbG9jay5sb2NhbFZhck5hbWVzLnB1c2godmFyTmFtZSk7XG4gICAgfVxuICAgIC8vIHJldHVybnMgdGhlIGJsb2NrIG9iamVjdCB0aGF0IGNvbnRhaW5zIHRoZSB2YXJpYWJsZVxuICAgIHJldHVybiBjdXJyQmxvY2s7XG59O1xuVmFyQmxvY2sucHJvdG90eXBlLmFkZFBhcmFtVmFyID0gZnVuY3Rpb24gKHZhck5hbWUpIHtcbiAgICB0aGlzLnBhcmFtVmFyTmFtZXMucHVzaCh2YXJOYW1lKTtcbn07XG5WYXJCbG9jay5wcm90b3R5cGUuZmluZFZhckluQ2hhaW4gPSBmdW5jdGlvbiAodmFyTmFtZSkge1xuICAgIHZhciBjdXJyQmxvY2sgPSB0aGlzO1xuICAgIHdoaWxlIChjdXJyQmxvY2sgJiYgY3VyckJsb2NrLnBhcmVuICYmICFjdXJyQmxvY2suaGFzVmFyKHZhck5hbWUpKSB7XG4gICAgICAgIGN1cnJCbG9jayA9IGN1cnJCbG9jay5wYXJlbjtcbiAgICB9XG4gICAgLy8gaWYgbm90IGZvdW5kLCBpdCB3aWxsIHJldHVybiB0aGUgZ2xvYmFsXG4gICAgcmV0dXJuIGN1cnJCbG9jaztcbn07XG5cblZhckJsb2NrLnByb3RvdHlwZS5hZGRVc2VkVmFyID0gZnVuY3Rpb24gKHZhck5hbWUpIHtcbiAgICBpZiAodGhpcy51c2VkVmFyaWFibGVzLmluZGV4T2YodmFyTmFtZSkgPT09IC0xKSB7XG4gICAgICAgIHRoaXMudXNlZFZhcmlhYmxlcy5wdXNoKHZhck5hbWUpO1xuICAgIH1cbn07XG5WYXJCbG9jay5wcm90b3R5cGUuZ2V0VXNlZFZhck5hbWVzID0gZnVuY3Rpb24gKCkge1xuICAgIHJldHVybiB0aGlzLnVzZWRWYXJpYWJsZXM7XG59O1xuVmFyQmxvY2sucHJvdG90eXBlLmlzVXNlZFZhciA9IGZ1bmN0aW9uICh2YXJOYW1lKSB7XG4gICAgcmV0dXJuIHRoaXMudXNlZFZhcmlhYmxlcy5pbmRleE9mKHZhck5hbWUpID4gLTE7XG59O1xuXG4vLyByZXR1cm5zIGEgbWFwcGluZ1xuVmFyQmxvY2sucHJvdG90eXBlLmdldEluc3RhbmNlID0gZnVuY3Rpb24gKGRlbHRhKSB7XG4gICAgaWYgKHRoaXMuaW5zdGFuY2VzW2RlbHRhXSkge1xuICAgICAgICByZXR1cm4gdGhpcy5pbnN0YW5jZXNbZGVsdGFdO1xuICAgIH1cbiAgICAvLyBjb25zdHJ1Y3QgVmFyTWFwXG4gICAgdmFyIHZhck1hcCA9IG5ldyBNYXAoKTtcbiAgICB2YXIgdmFyTmFtZXMgPSB0aGlzLmdldFBhcmFtVmFyTmFtZXMoKS5jb25jYXQodGhpcy5nZXRMb2NhbFZhck5hbWVzKCkpO1xuXG4gICAgZm9yICh2YXIgaSA9IDA7IGkgPCB2YXJOYW1lcy5sZW5ndGg7IGkrKykge1xuICAgICAgICB2YXJNYXAuc2V0KHZhck5hbWVzW2ldLCBuZXcgdHlwZXMuQVZhbCgpKTtcbiAgICB9XG4gICAgLy8gcmVtZW1iZXIgdGhlIGluc3RhbmNlXG4gICAgdGhpcy5pbnN0YW5jZXNbZGVsdGFdID0gdmFyTWFwO1xuICAgIHJldHVybiB2YXJNYXA7XG59O1xuLy8gcmV0dXJucyBhbiBhcnJheVxuVmFyQmxvY2sucHJvdG90eXBlLmdldFBhcmFtQVZhbHMgPSBmdW5jdGlvbiAoZGVsdGEpIHtcbiAgICB2YXIgaW5zdGFuY2UgPSB0aGlzLmdldEluc3RhbmNlKGRlbHRhKTtcbiAgICB2YXIgcGFyYW1zID0gW107XG4gICAgdGhpcy5nZXRQYXJhbVZhck5hbWVzKCkuZm9yRWFjaChmdW5jdGlvbiAobmFtZSkge1xuICAgICAgICBwYXJhbXMucHVzaChpbnN0YW5jZVthdXguaW50ZXJuYWxOYW1lKG5hbWUpXSk7XG4gICAgfSk7XG4gICAgcmV0dXJuIHBhcmFtcztcbn07XG4vLyByZXR1cm5zIGFuIEFWYWxcblZhckJsb2NrLnByb3RvdHlwZS5nZXRBcmd1bWVudHNBVmFsID0gZnVuY3Rpb24gKGRlbHRhKSB7XG4gICAgaWYgKCF0aGlzLnVzZUFyZ3VtZW50c09iamVjdCkge1xuICAgICAgICB0aHJvdyBuZXcgRXJyb3IoJ05vdCBmb3IgdGhpcyBWYXJCbG9jaycpO1xuICAgIH1cbiAgICByZXR1cm4gdGhpcy5nZXRJbnN0YW5jZShkZWx0YSlbYXV4LmludGVybmFsTmFtZSgnYXJndW1lbnRzJyldO1xufTtcblxuLy8gZ2V0IGEgU2NvcGUgaW5zdGFuY2VcblZhckJsb2NrLnByb3RvdHlwZS5nZXRTY29wZUluc3RhbmNlID0gZnVuY3Rpb24gKHBhcmVuLCBkZWx0YSkge1xuICAgIHZhciB2YXJNYXAgPSB0aGlzLmdldEluc3RhbmNlKGRlbHRhKTtcbiAgICB2YXIgZm91bmQgPSBudWxsO1xuXG4gICAgdGhpcy5zY29wZUluc3RhbmNlcy5mb3JFYWNoKGZ1bmN0aW9uIChzYykge1xuICAgICAgICBpZiAoc2MucGFyZW4gPT09IHBhcmVuICYmIHNjLnZhck1hcCA9PT0gdmFyTWFwKSBmb3VuZCA9IHNjO1xuICAgIH0pO1xuXG4gICAgaWYgKGZvdW5kKSB7XG4gICAgICAgIHJldHVybiBmb3VuZDtcbiAgICB9IGVsc2Uge1xuICAgICAgICB2YXIgbmV3U2NvcGVJbnN0YW5jZSA9IG5ldyBTY29wZShwYXJlbiwgdmFyTWFwLCB0aGlzKTtcbiAgICAgICAgdGhpcy5zY29wZUluc3RhbmNlcy5wdXNoKG5ld1Njb3BlSW5zdGFuY2UpO1xuICAgICAgICByZXR1cm4gbmV3U2NvcGVJbnN0YW5jZTtcbiAgICB9XG59O1xuXG52YXIgZGVjbGFyZWRWYXJpYWJsZUZpbmRlciA9IHdhbGsubWFrZSh7XG4gICBGdW5jdGlvbjogZnVuY3Rpb24gKG5vZGUsIGN1cnJCbG9jaywgYykge1xuICAgICAgICB2YXIgcGFyZW5CbG9jayA9IGN1cnJCbG9jaztcbiAgICAgICAgaWYgKG5vZGUuaWQpIHtcbiAgICAgICAgICAgIHZhciBmdW5jTmFtZSA9IG5vZGUuaWQubmFtZTtcbiAgICAgICAgICAgIHBhcmVuQmxvY2sgPSBjdXJyQmxvY2suYWRkRGVjbGFyZWRMb2NhbFZhcihmdW5jTmFtZSwgdHJ1ZSk7XG4gICAgICAgIH1cbiAgICAgICAgLy8gY3JlYXRlIGEgVmFyQmxvY2sgZm9yIGZ1bmN0aW9uXG4gICAgICAgIHZhciBmdW5jQmxvY2sgPSBuZXcgVmFyQmxvY2socGFyZW5CbG9jaywgbm9kZSk7XG4gICAgICAgIG5vZGUuYm9keVsnQGJsb2NrJ10gPSBmdW5jQmxvY2s7XG4gICAgICAgIC8vIGFkZCBmdW5jdGlvbiBwYXJhbWV0ZXJzIHRvIHRoZSBzY29wZVxuICAgICAgICBmb3IgKHZhciBpID0gMDsgaSA8IG5vZGUucGFyYW1zLmxlbmd0aDsgaSsrKSB7XG4gICAgICAgICAgICB2YXIgcGFyYW1OYW1lID0gbm9kZS5wYXJhbXNbaV0ubmFtZTtcbiAgICAgICAgICAgIGZ1bmNCbG9jay5hZGRQYXJhbVZhcihwYXJhbU5hbWUpO1xuICAgICAgICB9XG4gICAgICAgIGMobm9kZS5ib2R5LCBmdW5jQmxvY2ssIHVuZGVmaW5lZCk7XG4gICAgfSxcbiAgICBWYXJpYWJsZURlY2xhcmF0aW9uOiBmdW5jdGlvbiAobm9kZSwgY3VyckJsb2NrLCBjKSB7XG4gICAgICAgIGZvciAodmFyIGkgPSAwOyBpIDwgbm9kZS5kZWNsYXJhdGlvbnMubGVuZ3RoOyBpKyspIHtcbiAgICAgICAgICAgIHZhciBkZWNsID0gbm9kZS5kZWNsYXJhdGlvbnNbaV07XG4gICAgICAgICAgICB2YXIgbmFtZSA9IGRlY2wuaWQubmFtZTtcbiAgICAgICAgICAgIGN1cnJCbG9jay5hZGREZWNsYXJlZExvY2FsVmFyKG5hbWUpO1xuICAgICAgICB9XG4gICAgICAgIGlmIChkZWNsLmluaXQpIGMoZGVjbC5pbml0LCBjdXJyQmxvY2ssIHVuZGVmaW5lZCk7XG4gICAgfSxcbiAgICBUcnlTdGF0ZW1lbnQ6IGZ1bmN0aW9uIChub2RlLCBjdXJyU2NvcGUsIGMpIHtcbiAgICAgICAgYyhub2RlLmJsb2NrLCBjdXJyU2NvcGUsIHVuZGVmaW5lZCk7XG4gICAgICAgIGlmIChub2RlLmhhbmRsZXIpIHtcbiAgICAgICAgICAgIGMobm9kZS5oYW5kbGVyLCBjdXJyU2NvcGUsIHVuZGVmaW5lZCk7XG4gICAgICAgIH1cbiAgICAgICAgaWYgKG5vZGUuZmluYWxpemVyKSB7XG4gICAgICAgICAgICBjKG5vZGUuZmluYWxpemVyLCBjdXJyU2NvcGUsIHVuZGVmaW5lZCk7XG4gICAgICAgIH1cbiAgICB9LFxuICAgIENhdGNoQ2xhdXNlOiBmdW5jdGlvbiAobm9kZSwgY3VyckJsb2NrLCBjKSB7XG4gICAgICAgIHZhciBjYXRjaEJsb2NrID0gbmV3IFZhckJsb2NrKGN1cnJCbG9jaywgbm9kZSwgdHJ1ZSk7XG4gICAgICAgIGNhdGNoQmxvY2suYWRkUGFyYW1WYXIobm9kZS5wYXJhbS5uYW1lKTtcbiAgICAgICAgbm9kZS5ib2R5WydAYmxvY2snXSA9IGNhdGNoQmxvY2s7XG4gICAgICAgIGMobm9kZS5ib2R5LCBjYXRjaEJsb2NrLCB1bmRlZmluZWQpO1xuICAgIH1cbn0pO1xuXG4vLyBGb3IgdmFyaWFibGVzIGluIGdsb2JhbCBhbmQgYXJndW1lbnRzIGluIGZ1bmN0aW9uc1xudmFyIHZhcmlhYmxlVXNhZ2VDb2xsZWN0b3IgPSB3YWxrLm1ha2Uoe1xuICAgIFZhcmlhYmxlUGF0dGVybjogZnVuY3Rpb24gKG5vZGUsIGN1cnJCbG9jaywgYykge1xuICAgICAgICBjKG5vZGUsIGN1cnJCbG9jaywgJ0lkZW50aWZpZXInKTtcbiAgICB9LFxuXG4gICAgSWRlbnRpZmllcjogZnVuY3Rpb24gKG5vZGUsIGN1cnJCbG9jaywgYykge1xuICAgICAgICB2YXIgY29udGFpbmluZ0Jsb2NrLCB2YXJOYW1lID0gbm9kZS5uYW1lO1xuICAgICAgICBpZiAodmFyTmFtZSAhPT0gJ2FyZ3VtZW50cycpIHtcbiAgICAgICAgICAgIGNvbnRhaW5pbmdCbG9jayA9IGN1cnJCbG9jay5maW5kVmFySW5DaGFpbih2YXJOYW1lKTtcbiAgICAgICAgICAgIGlmIChjb250YWluaW5nQmxvY2suaXNHbG9iYWwoKSkge1xuICAgICAgICAgICAgICAgIGNvbnRhaW5pbmdCbG9jay5hZGREZWNsYXJlZExvY2FsVmFyKHZhck5hbWUpO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgY29udGFpbmluZ0Jsb2NrLmFkZFVzZWRWYXIodmFyTmFtZSk7XG4gICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgICAvLyB2YXJOYW1lID09ICdhcmd1bWVudHMnXG4gICAgICAgICAgICBjb250YWluaW5nQmxvY2sgPSBjdXJyQmxvY2s7XG4gICAgICAgICAgICB3aGlsZSAoY29udGFpbmluZ0Jsb2NrLmlzQ2F0Y2hCbG9jaygpICYmXG4gICAgICAgICAgICAgICAgICAgICFjb250YWluaW5nQmxvY2suaGFzUGFyYW1WYXIodmFyTmFtZSkpIHtcbiAgICAgICAgICAgICAgICBjb250YWluaW5nQmxvY2sgPSBjb250YWluaW5nQmxvY2sucGFyZW47XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBpZiAoY29udGFpbmluZ0Jsb2NrLmhhc1Zhcih2YXJOYW1lKSkge1xuICAgICAgICAgICAgICAgIC8vIGFyZ3VtZW50cyBpcyBleHBsaWNpdGx5IGRlY2xhcmVkXG4gICAgICAgICAgICAgICAgY29udGFpbmluZ0Jsb2NrLmFkZFVzZWRWYXIodmFyTmFtZSk7XG4gICAgICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgICAgICAgIC8vIGFyZ3VtZW50cyBpcyBub3QgZXhwbGljaXRseSBkZWNsYXJlZFxuICAgICAgICAgICAgICAgIC8vIGFkZCBpdCBhcyBsb2NhbCB2YXJpYWJsZVxuICAgICAgICAgICAgICAgIGNvbnRhaW5pbmdCbG9jay5hZGREZWNsYXJlZExvY2FsVmFyKHZhck5hbWUpO1xuICAgICAgICAgICAgICAgIC8vIGFsc28gaXQgaXMgdXNlZFxuICAgICAgICAgICAgICAgIGNvbnRhaW5pbmdCbG9jay5hZGRVc2VkVmFyKHZhck5hbWUpO1xuICAgICAgICAgICAgICAgIGlmIChjb250YWluaW5nQmxvY2suaXNGdW5jdGlvbigpKSB7XG4gICAgICAgICAgICAgICAgICAgIGNvbnRhaW5pbmdCbG9jay51c2VBcmd1bWVudHNPYmplY3QgPSB0cnVlO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgIH1cbiAgICAgICAgfVxuICAgIH0sXG5cbiAgICBSZXR1cm5TdGF0ZW1lbnQ6IGZ1bmN0aW9uIChub2RlLCBjdXJyQmxvY2ssIGMpIHtcbiAgICAgICAgdmFyIGZ1bmN0aW9uQmxvY2sgPSBjdXJyQmxvY2s7XG4gICAgICAgIHdoaWxlIChmdW5jdGlvbkJsb2NrLmlzQ2F0Y2hCbG9jaygpKSB7XG4gICAgICAgICAgICBmdW5jdGlvbkJsb2NrID0gZnVuY3Rpb25CbG9jay5wYXJlbjtcbiAgICAgICAgfVxuICAgICAgICBpZiAoIWZ1bmN0aW9uQmxvY2suaXNHbG9iYWwoKSAmJiBub2RlLmFyZ3VtZW50ICE9PSBudWxsKSB7XG4gICAgICAgICAgICBmdW5jdGlvbkJsb2NrLnVzZVJldHVybldpdGhBcmd1bWVudCA9IHRydWU7XG4gICAgICAgIH1cbiAgICAgICAgaWYgKG5vZGUuYXJndW1lbnQpIHtcbiAgICAgICAgICAgIGMobm9kZS5hcmd1bWVudCwgY3VyckJsb2NrLCB1bmRlZmluZWQpO1xuICAgICAgICB9XG4gICAgfSxcblxuICAgIFNjb3BlQm9keTogZnVuY3Rpb24gKG5vZGUsIGN1cnJCbG9jaywgYykge1xuICAgICAgICBjKG5vZGUsIG5vZGVbJ0BibG9jayddIHx8IGN1cnJCbG9jayk7XG4gICAgfVxufSk7XG5cblxuZnVuY3Rpb24gYW5ub3RhdGVCbG9ja0luZm8oYXN0LCBnQmxvY2spIHtcbiAgICBpZiAoIWdCbG9jaykge1xuICAgICAgICAvLyB3aGVuIGdsb2JhbCBibG9jayBpcyBub3QgZ2l2ZW4sIGNyZWF0ZVxuICAgICAgICBnQmxvY2sgPSBuZXcgVmFyQmxvY2sobnVsbCwgYXN0KTtcbiAgICB9XG4gICAgYXN0WydAYmxvY2snXSA9IGdCbG9jaztcbiAgICB3YWxrLnJlY3Vyc2l2ZShhc3QsIGdCbG9jaywgbnVsbCwgZGVjbGFyZWRWYXJpYWJsZUZpbmRlcik7XG4gICAgd2Fsay5yZWN1cnNpdmUoYXN0LCBnQmxvY2ssIG51bGwsIHZhcmlhYmxlVXNhZ2VDb2xsZWN0b3IpO1xuICAgIHJldHVybiBhc3Q7XG59XG5cbi8vIGRlZmluZSBzY29wZSBvYmplY3RcbmZ1bmN0aW9uIFNjb3BlKHBhcmVuLCB2YXJNYXAsIHZiKSB7XG4gICAgdGhpcy5wYXJlbiA9IHBhcmVuO1xuICAgIHRoaXMudmFyTWFwID0gdmFyTWFwO1xuICAgIHRoaXMudmIgPSB2Yjtcbn1cblNjb3BlLnByb3RvdHlwZSA9IE9iamVjdC5jcmVhdGUobnVsbCk7XG4vLyBmaW5kIEFWYWwgb2YgYSB2YXJpYWJsZSBpbiB0aGUgY2hhaW5cblNjb3BlLnByb3RvdHlwZS5nZXRBVmFsT2YgPSBmdW5jdGlvbiAodmFyTmFtZSkge1xuICAgIHZhciBjdXJyID0gdGhpcztcbiAgICB3aGlsZSAoY3VyciAhPSBudWxsKSB7XG4gICAgICAgIGlmIChjdXJyLnZhck1hcC5oYXModmFyTmFtZSkpIHtcbiAgICAgICAgICAgIHJldHVybiBjdXJyLnZhck1hcC5nZXQodmFyTmFtZSk7XG4gICAgICAgIH1cbiAgICAgICAgY3VyciA9IGN1cnIucGFyZW47XG4gICAgfVxuICAgIHRocm93IG5ldyBFcnJvcignU2hvdWxkIGhhdmUgZm91bmQgdGhlIHZhcmlhYmxlJyk7XG59O1xuLy8gcmVtb3ZlIGluaXRpYWwgY2F0Y2ggc2NvcGVzIGZyb20gdGhlIGNoYWluXG5TY29wZS5wcm90b3R5cGUucmVtb3ZlSW5pdGlhbENhdGNoQmxvY2tzID0gZnVuY3Rpb24gKCkge1xuICAgIHZhciBjdXJyID0gdGhpcztcbiAgICB3aGlsZSAoY3Vyci52Yi5pc0NhdGNoQmxvY2soKSkge1xuICAgICAgICBjdXJyID0gY3Vyci5wYXJlbjtcbiAgICB9XG4gICAgcmV0dXJuIGN1cnI7XG59O1xuXG5cbmV4cG9ydHMuVmFyQmxvY2sgPSBWYXJCbG9jaztcbmV4cG9ydHMuYW5ub3RhdGVCbG9ja0luZm8gPSBhbm5vdGF0ZUJsb2NrSW5mbztcbmV4cG9ydHMuU2NvcGUgPSBTY29wZTtcbiIsImNvbnN0IHdhbGsgPSByZXF1aXJlKCdhY29ybi9kaXN0L3dhbGsnKTtcbmNvbnN0IG15V2Fsa2VyID0gcmVxdWlyZSgnLi91dGlsL215V2Fsa2VyJyk7XG5cbmZ1bmN0aW9uIGZpbmRJZGVudGlmaWVyQXQoYXN0LCBwb3MpIHtcbiAgICBcInVzZSBzdHJpY3RcIjtcblxuICAgIGZ1bmN0aW9uIEZvdW5kKG5vZGUsIHN0YXRlKSB7XG4gICAgICAgIHRoaXMubm9kZSA9IG5vZGU7XG4gICAgICAgIHRoaXMuc3RhdGUgPSBzdGF0ZTtcbiAgICB9XG5cbiAgICAvLyBmaW5kIHRoZSBub2RlXG4gICAgY29uc3Qgd2Fsa2VyID0gbXlXYWxrZXIud3JhcFdhbGtlcihteVdhbGtlci52YXJXYWxrZXIsXG4gICAgICAgIChub2RlLCB2YikgPT4ge1xuICAgICAgICAgICAgaWYgKG5vZGUuc3RhcnQgPiBwb3MgfHwgbm9kZS5lbmQgPCBwb3MpIHtcbiAgICAgICAgICAgICAgICByZXR1cm4gZmFsc2U7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBpZiAobm9kZS50eXBlID09PSAnSWRlbnRpZmllcicgJiYgbm9kZS5uYW1lICE9PSAn4pyWJykge1xuICAgICAgICAgICAgICAgIHRocm93IG5ldyBGb3VuZChub2RlLCB2Yik7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICByZXR1cm4gdHJ1ZTtcbiAgICAgICAgfSk7XG5cbiAgICB0cnkge1xuICAgICAgICB3YWxrLnJlY3Vyc2l2ZShhc3QsIGFzdFsnQGJsb2NrJ10sIHdhbGtlcik7XG4gICAgfSBjYXRjaCAoZSkge1xuICAgICAgICBpZiAoZSBpbnN0YW5jZW9mIEZvdW5kKSB7XG4gICAgICAgICAgICByZXR1cm4gZTtcbiAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICAgIHRocm93IGU7XG4gICAgICAgIH1cbiAgICB9XG4gICAgLy8gaWRlbnRpZmllciBub3QgZm91bmRcbiAgICByZXR1cm4gbnVsbDtcbn1cblxuLyoqXG4gKlxuICogQHBhcmFtIGFzdCAtIHNjb3BlIGFubm90YXRlZCBBU1RcbiAqIEBwYXJhbSB7bnVtYmVyfSBwb3MgLSBjaGFyYWN0ZXIgcG9zaXRpb25cbiAqIEByZXR1cm5zIHsqfSAtIGFycmF5IG9mIEFTVCBub2Rlc1xuICovXG5mdW5jdGlvbiBmaW5kVmFyUmVmc0F0KGFzdCwgcG9zKSB7XG4gICAgXCJ1c2Ugc3RyaWN0XCI7XG4gICAgY29uc3QgZm91bmQgPSBmaW5kSWRlbnRpZmllckF0KGFzdCwgcG9zKTtcbiAgICBpZiAoIWZvdW5kKSB7XG4gICAgICAgIC8vIHBvcyBpcyBub3QgYXQgYSB2YXJpYWJsZVxuICAgICAgICByZXR1cm4gbnVsbDtcbiAgICB9XG4gICAgLy8gZmluZCByZWZzIGZvciB0aGUgaWQgbm9kZVxuICAgIGNvbnN0IHJlZnMgPSBmaW5kUmVmc1RvVmFyaWFibGUoYXN0LCBmb3VuZCk7XG5cbiAgICByZXR1cm4gcmVmcztcbn1cblxuLyoqXG4gKlxuICogQHBhcmFtIGFzdCAtIHNjb3BlIGFubm90YXRlZCBBU1RcbiAqIEBwYXJhbSBmb3VuZCAtIG5vZGUgYW5kIHZhckJsb2NrIG9mIHRoZSB2YXJpYWJsZVxuICogQHJldHVybnMge0FycmF5fSAtIGFycmF5IG9mIEFTVCBub2Rlc1xuICovXG5mdW5jdGlvbiBmaW5kUmVmc1RvVmFyaWFibGUoYXN0LCBmb3VuZCkge1xuICAgIFwidXNlIHN0cmljdFwiO1xuICAgIGNvbnN0IHZhck5hbWUgPSBmb3VuZC5ub2RlLm5hbWU7XG4gICAgY29uc3QgdmIxID0gZm91bmQuc3RhdGUuZmluZFZhckluQ2hhaW4odmFyTmFtZSk7XG4gICAgY29uc3QgcmVmcyA9IFtdO1xuXG4gICAgY29uc3Qgd2Fsa2VyID0gd2Fsay5tYWtlKHtcbiAgICAgICAgSWRlbnRpZmllcjogKG5vZGUsIHZiKSA9PiB7XG4gICAgICAgICAgICBpZiAobm9kZS5uYW1lICE9PSB2YXJOYW1lKSByZXR1cm47XG4gICAgICAgICAgICBpZiAodmIxID09PSB2Yi5maW5kVmFySW5DaGFpbih2YXJOYW1lKSkge1xuICAgICAgICAgICAgICAgIHJlZnMucHVzaChub2RlKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgfVxuICAgIH0sIG15V2Fsa2VyLnZhcldhbGtlcik7XG5cbiAgICB3YWxrLnJlY3Vyc2l2ZSh2YjEub3JpZ2luTm9kZSwgdmIxLCB3YWxrZXIpO1xuICAgIHJldHVybiByZWZzO1xufVxuXG5leHBvcnRzLmZpbmRJZGVudGlmaWVyQXQgPSBmaW5kSWRlbnRpZmllckF0O1xuZXhwb3J0cy5maW5kVmFyUmVmc0F0ID0gZmluZFZhclJlZnNBdDsiLCIoZnVuY3Rpb24oZil7aWYodHlwZW9mIGV4cG9ydHM9PT1cIm9iamVjdFwiJiZ0eXBlb2YgbW9kdWxlIT09XCJ1bmRlZmluZWRcIil7bW9kdWxlLmV4cG9ydHM9ZigpfWVsc2UgaWYodHlwZW9mIGRlZmluZT09PVwiZnVuY3Rpb25cIiYmZGVmaW5lLmFtZCl7ZGVmaW5lKFtdLGYpfWVsc2V7dmFyIGc7aWYodHlwZW9mIHdpbmRvdyE9PVwidW5kZWZpbmVkXCIpe2c9d2luZG93fWVsc2UgaWYodHlwZW9mIGdsb2JhbCE9PVwidW5kZWZpbmVkXCIpe2c9Z2xvYmFsfWVsc2UgaWYodHlwZW9mIHNlbGYhPT1cInVuZGVmaW5lZFwiKXtnPXNlbGZ9ZWxzZXtnPXRoaXN9Zy5hY29ybiA9IGYoKX19KShmdW5jdGlvbigpe3ZhciBkZWZpbmUsbW9kdWxlLGV4cG9ydHM7cmV0dXJuIChmdW5jdGlvbiBlKHQsbixyKXtmdW5jdGlvbiBzKG8sdSl7aWYoIW5bb10pe2lmKCF0W29dKXt2YXIgYT10eXBlb2YgcmVxdWlyZT09XCJmdW5jdGlvblwiJiZyZXF1aXJlO2lmKCF1JiZhKXJldHVybiBhKG8sITApO2lmKGkpcmV0dXJuIGkobywhMCk7dmFyIGY9bmV3IEVycm9yKFwiQ2Fubm90IGZpbmQgbW9kdWxlICdcIitvK1wiJ1wiKTt0aHJvdyBmLmNvZGU9XCJNT0RVTEVfTk9UX0ZPVU5EXCIsZn12YXIgbD1uW29dPXtleHBvcnRzOnt9fTt0W29dWzBdLmNhbGwobC5leHBvcnRzLGZ1bmN0aW9uKGUpe3ZhciBuPXRbb11bMV1bZV07cmV0dXJuIHMobj9uOmUpfSxsLGwuZXhwb3J0cyxlLHQsbixyKX1yZXR1cm4gbltvXS5leHBvcnRzfXZhciBpPXR5cGVvZiByZXF1aXJlPT1cImZ1bmN0aW9uXCImJnJlcXVpcmU7Zm9yKHZhciBvPTA7bzxyLmxlbmd0aDtvKyspcyhyW29dKTtyZXR1cm4gc30pKHsxOltmdW5jdGlvbihfZGVyZXFfLG1vZHVsZSxleHBvcnRzKXtcbi8vIEEgcmVjdXJzaXZlIGRlc2NlbnQgcGFyc2VyIG9wZXJhdGVzIGJ5IGRlZmluaW5nIGZ1bmN0aW9ucyBmb3IgYWxsXG4vLyBzeW50YWN0aWMgZWxlbWVudHMsIGFuZCByZWN1cnNpdmVseSBjYWxsaW5nIHRob3NlLCBlYWNoIGZ1bmN0aW9uXG4vLyBhZHZhbmNpbmcgdGhlIGlucHV0IHN0cmVhbSBhbmQgcmV0dXJuaW5nIGFuIEFTVCBub2RlLiBQcmVjZWRlbmNlXG4vLyBvZiBjb25zdHJ1Y3RzIChmb3IgZXhhbXBsZSwgdGhlIGZhY3QgdGhhdCBgIXhbMV1gIG1lYW5zIGAhKHhbMV0pYFxuLy8gaW5zdGVhZCBvZiBgKCF4KVsxXWAgaXMgaGFuZGxlZCBieSB0aGUgZmFjdCB0aGF0IHRoZSBwYXJzZXJcbi8vIGZ1bmN0aW9uIHRoYXQgcGFyc2VzIHVuYXJ5IHByZWZpeCBvcGVyYXRvcnMgaXMgY2FsbGVkIGZpcnN0LCBhbmRcbi8vIGluIHR1cm4gY2FsbHMgdGhlIGZ1bmN0aW9uIHRoYXQgcGFyc2VzIGBbXWAgc3Vic2NyaXB0cyDigJQgdGhhdFxuLy8gd2F5LCBpdCdsbCByZWNlaXZlIHRoZSBub2RlIGZvciBgeFsxXWAgYWxyZWFkeSBwYXJzZWQsIGFuZCB3cmFwc1xuLy8gKnRoYXQqIGluIHRoZSB1bmFyeSBvcGVyYXRvciBub2RlLlxuLy9cbi8vIEFjb3JuIHVzZXMgYW4gW29wZXJhdG9yIHByZWNlZGVuY2UgcGFyc2VyXVtvcHBdIHRvIGhhbmRsZSBiaW5hcnlcbi8vIG9wZXJhdG9yIHByZWNlZGVuY2UsIGJlY2F1c2UgaXQgaXMgbXVjaCBtb3JlIGNvbXBhY3QgdGhhbiB1c2luZ1xuLy8gdGhlIHRlY2huaXF1ZSBvdXRsaW5lZCBhYm92ZSwgd2hpY2ggdXNlcyBkaWZmZXJlbnQsIG5lc3Rpbmdcbi8vIGZ1bmN0aW9ucyB0byBzcGVjaWZ5IHByZWNlZGVuY2UsIGZvciBhbGwgb2YgdGhlIHRlbiBiaW5hcnlcbi8vIHByZWNlZGVuY2UgbGV2ZWxzIHRoYXQgSmF2YVNjcmlwdCBkZWZpbmVzLlxuLy9cbi8vIFtvcHBdOiBodHRwOi8vZW4ud2lraXBlZGlhLm9yZy93aWtpL09wZXJhdG9yLXByZWNlZGVuY2VfcGFyc2VyXG5cblwidXNlIHN0cmljdFwiO1xuXG52YXIgX3Rva2VudHlwZSA9IF9kZXJlcV8oXCIuL3Rva2VudHlwZVwiKTtcblxudmFyIF9zdGF0ZSA9IF9kZXJlcV8oXCIuL3N0YXRlXCIpO1xuXG52YXIgX2lkZW50aWZpZXIgPSBfZGVyZXFfKFwiLi9pZGVudGlmaWVyXCIpO1xuXG52YXIgX3V0aWwgPSBfZGVyZXFfKFwiLi91dGlsXCIpO1xuXG52YXIgcHAgPSBfc3RhdGUuUGFyc2VyLnByb3RvdHlwZTtcblxuLy8gQ2hlY2sgaWYgcHJvcGVydHkgbmFtZSBjbGFzaGVzIHdpdGggYWxyZWFkeSBhZGRlZC5cbi8vIE9iamVjdC9jbGFzcyBnZXR0ZXJzIGFuZCBzZXR0ZXJzIGFyZSBub3QgYWxsb3dlZCB0byBjbGFzaCDigJRcbi8vIGVpdGhlciB3aXRoIGVhY2ggb3RoZXIgb3Igd2l0aCBhbiBpbml0IHByb3BlcnR5IOKAlCBhbmQgaW5cbi8vIHN0cmljdCBtb2RlLCBpbml0IHByb3BlcnRpZXMgYXJlIGFsc28gbm90IGFsbG93ZWQgdG8gYmUgcmVwZWF0ZWQuXG5cbnBwLmNoZWNrUHJvcENsYXNoID0gZnVuY3Rpb24gKHByb3AsIHByb3BIYXNoKSB7XG4gIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNiAmJiAocHJvcC5jb21wdXRlZCB8fCBwcm9wLm1ldGhvZCB8fCBwcm9wLnNob3J0aGFuZCkpIHJldHVybjtcbiAgdmFyIGtleSA9IHByb3Aua2V5LFxuICAgICAgbmFtZSA9IHVuZGVmaW5lZDtcbiAgc3dpdGNoIChrZXkudHlwZSkge1xuICAgIGNhc2UgXCJJZGVudGlmaWVyXCI6XG4gICAgICBuYW1lID0ga2V5Lm5hbWU7YnJlYWs7XG4gICAgY2FzZSBcIkxpdGVyYWxcIjpcbiAgICAgIG5hbWUgPSBTdHJpbmcoa2V5LnZhbHVlKTticmVhaztcbiAgICBkZWZhdWx0OlxuICAgICAgcmV0dXJuO1xuICB9XG4gIHZhciBraW5kID0gcHJvcC5raW5kO1xuICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYpIHtcbiAgICBpZiAobmFtZSA9PT0gXCJfX3Byb3RvX19cIiAmJiBraW5kID09PSBcImluaXRcIikge1xuICAgICAgaWYgKHByb3BIYXNoLnByb3RvKSB0aGlzLnJhaXNlKGtleS5zdGFydCwgXCJSZWRlZmluaXRpb24gb2YgX19wcm90b19fIHByb3BlcnR5XCIpO1xuICAgICAgcHJvcEhhc2gucHJvdG8gPSB0cnVlO1xuICAgIH1cbiAgICByZXR1cm47XG4gIH1cbiAgdmFyIG90aGVyID0gdW5kZWZpbmVkO1xuICBpZiAoX3V0aWwuaGFzKHByb3BIYXNoLCBuYW1lKSkge1xuICAgIG90aGVyID0gcHJvcEhhc2hbbmFtZV07XG4gICAgdmFyIGlzR2V0U2V0ID0ga2luZCAhPT0gXCJpbml0XCI7XG4gICAgaWYgKCh0aGlzLnN0cmljdCB8fCBpc0dldFNldCkgJiYgb3RoZXJba2luZF0gfHwgIShpc0dldFNldCBeIG90aGVyLmluaXQpKSB0aGlzLnJhaXNlKGtleS5zdGFydCwgXCJSZWRlZmluaXRpb24gb2YgcHJvcGVydHlcIik7XG4gIH0gZWxzZSB7XG4gICAgb3RoZXIgPSBwcm9wSGFzaFtuYW1lXSA9IHtcbiAgICAgIGluaXQ6IGZhbHNlLFxuICAgICAgZ2V0OiBmYWxzZSxcbiAgICAgIHNldDogZmFsc2VcbiAgICB9O1xuICB9XG4gIG90aGVyW2tpbmRdID0gdHJ1ZTtcbn07XG5cbi8vICMjIyBFeHByZXNzaW9uIHBhcnNpbmdcblxuLy8gVGhlc2UgbmVzdCwgZnJvbSB0aGUgbW9zdCBnZW5lcmFsIGV4cHJlc3Npb24gdHlwZSBhdCB0aGUgdG9wIHRvXG4vLyAnYXRvbWljJywgbm9uZGl2aXNpYmxlIGV4cHJlc3Npb24gdHlwZXMgYXQgdGhlIGJvdHRvbS4gTW9zdCBvZlxuLy8gdGhlIGZ1bmN0aW9ucyB3aWxsIHNpbXBseSBsZXQgdGhlIGZ1bmN0aW9uKHMpIGJlbG93IHRoZW0gcGFyc2UsXG4vLyBhbmQsICppZiogdGhlIHN5bnRhY3RpYyBjb25zdHJ1Y3QgdGhleSBoYW5kbGUgaXMgcHJlc2VudCwgd3JhcFxuLy8gdGhlIEFTVCBub2RlIHRoYXQgdGhlIGlubmVyIHBhcnNlciBnYXZlIHRoZW0gaW4gYW5vdGhlciBub2RlLlxuXG4vLyBQYXJzZSBhIGZ1bGwgZXhwcmVzc2lvbi4gVGhlIG9wdGlvbmFsIGFyZ3VtZW50cyBhcmUgdXNlZCB0b1xuLy8gZm9yYmlkIHRoZSBgaW5gIG9wZXJhdG9yIChpbiBmb3IgbG9vcHMgaW5pdGFsaXphdGlvbiBleHByZXNzaW9ucylcbi8vIGFuZCBwcm92aWRlIHJlZmVyZW5jZSBmb3Igc3RvcmluZyAnPScgb3BlcmF0b3IgaW5zaWRlIHNob3J0aGFuZFxuLy8gcHJvcGVydHkgYXNzaWdubWVudCBpbiBjb250ZXh0cyB3aGVyZSBib3RoIG9iamVjdCBleHByZXNzaW9uXG4vLyBhbmQgb2JqZWN0IHBhdHRlcm4gbWlnaHQgYXBwZWFyIChzbyBpdCdzIHBvc3NpYmxlIHRvIHJhaXNlXG4vLyBkZWxheWVkIHN5bnRheCBlcnJvciBhdCBjb3JyZWN0IHBvc2l0aW9uKS5cblxucHAucGFyc2VFeHByZXNzaW9uID0gZnVuY3Rpb24gKG5vSW4sIHJlZlNob3J0aGFuZERlZmF1bHRQb3MpIHtcbiAgdmFyIHN0YXJ0UG9zID0gdGhpcy5zdGFydCxcbiAgICAgIHN0YXJ0TG9jID0gdGhpcy5zdGFydExvYztcbiAgdmFyIGV4cHIgPSB0aGlzLnBhcnNlTWF5YmVBc3NpZ24obm9JbiwgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcyk7XG4gIGlmICh0aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuY29tbWEpIHtcbiAgICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlQXQoc3RhcnRQb3MsIHN0YXJ0TG9jKTtcbiAgICBub2RlLmV4cHJlc3Npb25zID0gW2V4cHJdO1xuICAgIHdoaWxlICh0aGlzLmVhdChfdG9rZW50eXBlLnR5cGVzLmNvbW1hKSkgbm9kZS5leHByZXNzaW9ucy5wdXNoKHRoaXMucGFyc2VNYXliZUFzc2lnbihub0luLCByZWZTaG9ydGhhbmREZWZhdWx0UG9zKSk7XG4gICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIlNlcXVlbmNlRXhwcmVzc2lvblwiKTtcbiAgfVxuICByZXR1cm4gZXhwcjtcbn07XG5cbi8vIFBhcnNlIGFuIGFzc2lnbm1lbnQgZXhwcmVzc2lvbi4gVGhpcyBpbmNsdWRlcyBhcHBsaWNhdGlvbnMgb2Zcbi8vIG9wZXJhdG9ycyBsaWtlIGArPWAuXG5cbnBwLnBhcnNlTWF5YmVBc3NpZ24gPSBmdW5jdGlvbiAobm9JbiwgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcywgYWZ0ZXJMZWZ0UGFyc2UpIHtcbiAgaWYgKHRoaXMudHlwZSA9PSBfdG9rZW50eXBlLnR5cGVzLl95aWVsZCAmJiB0aGlzLmluR2VuZXJhdG9yKSByZXR1cm4gdGhpcy5wYXJzZVlpZWxkKCk7XG5cbiAgdmFyIGZhaWxPblNob3J0aGFuZEFzc2lnbiA9IHVuZGVmaW5lZDtcbiAgaWYgKCFyZWZTaG9ydGhhbmREZWZhdWx0UG9zKSB7XG4gICAgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcyA9IHsgc3RhcnQ6IDAgfTtcbiAgICBmYWlsT25TaG9ydGhhbmRBc3NpZ24gPSB0cnVlO1xuICB9IGVsc2Uge1xuICAgIGZhaWxPblNob3J0aGFuZEFzc2lnbiA9IGZhbHNlO1xuICB9XG4gIHZhciBzdGFydFBvcyA9IHRoaXMuc3RhcnQsXG4gICAgICBzdGFydExvYyA9IHRoaXMuc3RhcnRMb2M7XG4gIGlmICh0aGlzLnR5cGUgPT0gX3Rva2VudHlwZS50eXBlcy5wYXJlbkwgfHwgdGhpcy50eXBlID09IF90b2tlbnR5cGUudHlwZXMubmFtZSkgdGhpcy5wb3RlbnRpYWxBcnJvd0F0ID0gdGhpcy5zdGFydDtcbiAgdmFyIGxlZnQgPSB0aGlzLnBhcnNlTWF5YmVDb25kaXRpb25hbChub0luLCByZWZTaG9ydGhhbmREZWZhdWx0UG9zKTtcbiAgaWYgKGFmdGVyTGVmdFBhcnNlKSBsZWZ0ID0gYWZ0ZXJMZWZ0UGFyc2UuY2FsbCh0aGlzLCBsZWZ0LCBzdGFydFBvcywgc3RhcnRMb2MpO1xuICBpZiAodGhpcy50eXBlLmlzQXNzaWduKSB7XG4gICAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0UG9zLCBzdGFydExvYyk7XG4gICAgbm9kZS5vcGVyYXRvciA9IHRoaXMudmFsdWU7XG4gICAgbm9kZS5sZWZ0ID0gdGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLmVxID8gdGhpcy50b0Fzc2lnbmFibGUobGVmdCkgOiBsZWZ0O1xuICAgIHJlZlNob3J0aGFuZERlZmF1bHRQb3Muc3RhcnQgPSAwOyAvLyByZXNldCBiZWNhdXNlIHNob3J0aGFuZCBkZWZhdWx0IHdhcyB1c2VkIGNvcnJlY3RseVxuICAgIHRoaXMuY2hlY2tMVmFsKGxlZnQpO1xuICAgIHRoaXMubmV4dCgpO1xuICAgIG5vZGUucmlnaHQgPSB0aGlzLnBhcnNlTWF5YmVBc3NpZ24obm9Jbik7XG4gICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkFzc2lnbm1lbnRFeHByZXNzaW9uXCIpO1xuICB9IGVsc2UgaWYgKGZhaWxPblNob3J0aGFuZEFzc2lnbiAmJiByZWZTaG9ydGhhbmREZWZhdWx0UG9zLnN0YXJ0KSB7XG4gICAgdGhpcy51bmV4cGVjdGVkKHJlZlNob3J0aGFuZERlZmF1bHRQb3Muc3RhcnQpO1xuICB9XG4gIHJldHVybiBsZWZ0O1xufTtcblxuLy8gUGFyc2UgYSB0ZXJuYXJ5IGNvbmRpdGlvbmFsIChgPzpgKSBvcGVyYXRvci5cblxucHAucGFyc2VNYXliZUNvbmRpdGlvbmFsID0gZnVuY3Rpb24gKG5vSW4sIHJlZlNob3J0aGFuZERlZmF1bHRQb3MpIHtcbiAgdmFyIHN0YXJ0UG9zID0gdGhpcy5zdGFydCxcbiAgICAgIHN0YXJ0TG9jID0gdGhpcy5zdGFydExvYztcbiAgdmFyIGV4cHIgPSB0aGlzLnBhcnNlRXhwck9wcyhub0luLCByZWZTaG9ydGhhbmREZWZhdWx0UG9zKTtcbiAgaWYgKHJlZlNob3J0aGFuZERlZmF1bHRQb3MgJiYgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcy5zdGFydCkgcmV0dXJuIGV4cHI7XG4gIGlmICh0aGlzLmVhdChfdG9rZW50eXBlLnR5cGVzLnF1ZXN0aW9uKSkge1xuICAgIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGVBdChzdGFydFBvcywgc3RhcnRMb2MpO1xuICAgIG5vZGUudGVzdCA9IGV4cHI7XG4gICAgbm9kZS5jb25zZXF1ZW50ID0gdGhpcy5wYXJzZU1heWJlQXNzaWduKCk7XG4gICAgdGhpcy5leHBlY3QoX3Rva2VudHlwZS50eXBlcy5jb2xvbik7XG4gICAgbm9kZS5hbHRlcm5hdGUgPSB0aGlzLnBhcnNlTWF5YmVBc3NpZ24obm9Jbik7XG4gICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkNvbmRpdGlvbmFsRXhwcmVzc2lvblwiKTtcbiAgfVxuICByZXR1cm4gZXhwcjtcbn07XG5cbi8vIFN0YXJ0IHRoZSBwcmVjZWRlbmNlIHBhcnNlci5cblxucHAucGFyc2VFeHByT3BzID0gZnVuY3Rpb24gKG5vSW4sIHJlZlNob3J0aGFuZERlZmF1bHRQb3MpIHtcbiAgdmFyIHN0YXJ0UG9zID0gdGhpcy5zdGFydCxcbiAgICAgIHN0YXJ0TG9jID0gdGhpcy5zdGFydExvYztcbiAgdmFyIGV4cHIgPSB0aGlzLnBhcnNlTWF5YmVVbmFyeShyZWZTaG9ydGhhbmREZWZhdWx0UG9zKTtcbiAgaWYgKHJlZlNob3J0aGFuZERlZmF1bHRQb3MgJiYgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcy5zdGFydCkgcmV0dXJuIGV4cHI7XG4gIHJldHVybiB0aGlzLnBhcnNlRXhwck9wKGV4cHIsIHN0YXJ0UG9zLCBzdGFydExvYywgLTEsIG5vSW4pO1xufTtcblxuLy8gUGFyc2UgYmluYXJ5IG9wZXJhdG9ycyB3aXRoIHRoZSBvcGVyYXRvciBwcmVjZWRlbmNlIHBhcnNpbmdcbi8vIGFsZ29yaXRobS4gYGxlZnRgIGlzIHRoZSBsZWZ0LWhhbmQgc2lkZSBvZiB0aGUgb3BlcmF0b3IuXG4vLyBgbWluUHJlY2AgcHJvdmlkZXMgY29udGV4dCB0aGF0IGFsbG93cyB0aGUgZnVuY3Rpb24gdG8gc3RvcCBhbmRcbi8vIGRlZmVyIGZ1cnRoZXIgcGFyc2VyIHRvIG9uZSBvZiBpdHMgY2FsbGVycyB3aGVuIGl0IGVuY291bnRlcnMgYW5cbi8vIG9wZXJhdG9yIHRoYXQgaGFzIGEgbG93ZXIgcHJlY2VkZW5jZSB0aGFuIHRoZSBzZXQgaXQgaXMgcGFyc2luZy5cblxucHAucGFyc2VFeHByT3AgPSBmdW5jdGlvbiAobGVmdCwgbGVmdFN0YXJ0UG9zLCBsZWZ0U3RhcnRMb2MsIG1pblByZWMsIG5vSW4pIHtcbiAgdmFyIHByZWMgPSB0aGlzLnR5cGUuYmlub3A7XG4gIGlmIChwcmVjICE9IG51bGwgJiYgKCFub0luIHx8IHRoaXMudHlwZSAhPT0gX3Rva2VudHlwZS50eXBlcy5faW4pKSB7XG4gICAgaWYgKHByZWMgPiBtaW5QcmVjKSB7XG4gICAgICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlQXQobGVmdFN0YXJ0UG9zLCBsZWZ0U3RhcnRMb2MpO1xuICAgICAgbm9kZS5sZWZ0ID0gbGVmdDtcbiAgICAgIG5vZGUub3BlcmF0b3IgPSB0aGlzLnZhbHVlO1xuICAgICAgdmFyIG9wID0gdGhpcy50eXBlO1xuICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICB2YXIgc3RhcnRQb3MgPSB0aGlzLnN0YXJ0LFxuICAgICAgICAgIHN0YXJ0TG9jID0gdGhpcy5zdGFydExvYztcbiAgICAgIG5vZGUucmlnaHQgPSB0aGlzLnBhcnNlRXhwck9wKHRoaXMucGFyc2VNYXliZVVuYXJ5KCksIHN0YXJ0UG9zLCBzdGFydExvYywgcHJlYywgbm9Jbik7XG4gICAgICB0aGlzLmZpbmlzaE5vZGUobm9kZSwgb3AgPT09IF90b2tlbnR5cGUudHlwZXMubG9naWNhbE9SIHx8IG9wID09PSBfdG9rZW50eXBlLnR5cGVzLmxvZ2ljYWxBTkQgPyBcIkxvZ2ljYWxFeHByZXNzaW9uXCIgOiBcIkJpbmFyeUV4cHJlc3Npb25cIik7XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZUV4cHJPcChub2RlLCBsZWZ0U3RhcnRQb3MsIGxlZnRTdGFydExvYywgbWluUHJlYywgbm9Jbik7XG4gICAgfVxuICB9XG4gIHJldHVybiBsZWZ0O1xufTtcblxuLy8gUGFyc2UgdW5hcnkgb3BlcmF0b3JzLCBib3RoIHByZWZpeCBhbmQgcG9zdGZpeC5cblxucHAucGFyc2VNYXliZVVuYXJ5ID0gZnVuY3Rpb24gKHJlZlNob3J0aGFuZERlZmF1bHRQb3MpIHtcbiAgaWYgKHRoaXMudHlwZS5wcmVmaXgpIHtcbiAgICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCksXG4gICAgICAgIHVwZGF0ZSA9IHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5pbmNEZWM7XG4gICAgbm9kZS5vcGVyYXRvciA9IHRoaXMudmFsdWU7XG4gICAgbm9kZS5wcmVmaXggPSB0cnVlO1xuICAgIHRoaXMubmV4dCgpO1xuICAgIG5vZGUuYXJndW1lbnQgPSB0aGlzLnBhcnNlTWF5YmVVbmFyeSgpO1xuICAgIGlmIChyZWZTaG9ydGhhbmREZWZhdWx0UG9zICYmIHJlZlNob3J0aGFuZERlZmF1bHRQb3Muc3RhcnQpIHRoaXMudW5leHBlY3RlZChyZWZTaG9ydGhhbmREZWZhdWx0UG9zLnN0YXJ0KTtcbiAgICBpZiAodXBkYXRlKSB0aGlzLmNoZWNrTFZhbChub2RlLmFyZ3VtZW50KTtlbHNlIGlmICh0aGlzLnN0cmljdCAmJiBub2RlLm9wZXJhdG9yID09PSBcImRlbGV0ZVwiICYmIG5vZGUuYXJndW1lbnQudHlwZSA9PT0gXCJJZGVudGlmaWVyXCIpIHRoaXMucmFpc2Uobm9kZS5zdGFydCwgXCJEZWxldGluZyBsb2NhbCB2YXJpYWJsZSBpbiBzdHJpY3QgbW9kZVwiKTtcbiAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIHVwZGF0ZSA/IFwiVXBkYXRlRXhwcmVzc2lvblwiIDogXCJVbmFyeUV4cHJlc3Npb25cIik7XG4gIH1cbiAgdmFyIHN0YXJ0UG9zID0gdGhpcy5zdGFydCxcbiAgICAgIHN0YXJ0TG9jID0gdGhpcy5zdGFydExvYztcbiAgdmFyIGV4cHIgPSB0aGlzLnBhcnNlRXhwclN1YnNjcmlwdHMocmVmU2hvcnRoYW5kRGVmYXVsdFBvcyk7XG4gIGlmIChyZWZTaG9ydGhhbmREZWZhdWx0UG9zICYmIHJlZlNob3J0aGFuZERlZmF1bHRQb3Muc3RhcnQpIHJldHVybiBleHByO1xuICB3aGlsZSAodGhpcy50eXBlLnBvc3RmaXggJiYgIXRoaXMuY2FuSW5zZXJ0U2VtaWNvbG9uKCkpIHtcbiAgICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlQXQoc3RhcnRQb3MsIHN0YXJ0TG9jKTtcbiAgICBub2RlLm9wZXJhdG9yID0gdGhpcy52YWx1ZTtcbiAgICBub2RlLnByZWZpeCA9IGZhbHNlO1xuICAgIG5vZGUuYXJndW1lbnQgPSBleHByO1xuICAgIHRoaXMuY2hlY2tMVmFsKGV4cHIpO1xuICAgIHRoaXMubmV4dCgpO1xuICAgIGV4cHIgPSB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJVcGRhdGVFeHByZXNzaW9uXCIpO1xuICB9XG4gIHJldHVybiBleHByO1xufTtcblxuLy8gUGFyc2UgY2FsbCwgZG90LCBhbmQgYFtdYC1zdWJzY3JpcHQgZXhwcmVzc2lvbnMuXG5cbnBwLnBhcnNlRXhwclN1YnNjcmlwdHMgPSBmdW5jdGlvbiAocmVmU2hvcnRoYW5kRGVmYXVsdFBvcykge1xuICB2YXIgc3RhcnRQb3MgPSB0aGlzLnN0YXJ0LFxuICAgICAgc3RhcnRMb2MgPSB0aGlzLnN0YXJ0TG9jO1xuICB2YXIgZXhwciA9IHRoaXMucGFyc2VFeHByQXRvbShyZWZTaG9ydGhhbmREZWZhdWx0UG9zKTtcbiAgaWYgKHJlZlNob3J0aGFuZERlZmF1bHRQb3MgJiYgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcy5zdGFydCkgcmV0dXJuIGV4cHI7XG4gIHJldHVybiB0aGlzLnBhcnNlU3Vic2NyaXB0cyhleHByLCBzdGFydFBvcywgc3RhcnRMb2MpO1xufTtcblxucHAucGFyc2VTdWJzY3JpcHRzID0gZnVuY3Rpb24gKGJhc2UsIHN0YXJ0UG9zLCBzdGFydExvYywgbm9DYWxscykge1xuICBmb3IgKDs7KSB7XG4gICAgaWYgKHRoaXMuZWF0KF90b2tlbnR5cGUudHlwZXMuZG90KSkge1xuICAgICAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0UG9zLCBzdGFydExvYyk7XG4gICAgICBub2RlLm9iamVjdCA9IGJhc2U7XG4gICAgICBub2RlLnByb3BlcnR5ID0gdGhpcy5wYXJzZUlkZW50KHRydWUpO1xuICAgICAgbm9kZS5jb21wdXRlZCA9IGZhbHNlO1xuICAgICAgYmFzZSA9IHRoaXMuZmluaXNoTm9kZShub2RlLCBcIk1lbWJlckV4cHJlc3Npb25cIik7XG4gICAgfSBlbHNlIGlmICh0aGlzLmVhdChfdG9rZW50eXBlLnR5cGVzLmJyYWNrZXRMKSkge1xuICAgICAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0UG9zLCBzdGFydExvYyk7XG4gICAgICBub2RlLm9iamVjdCA9IGJhc2U7XG4gICAgICBub2RlLnByb3BlcnR5ID0gdGhpcy5wYXJzZUV4cHJlc3Npb24oKTtcbiAgICAgIG5vZGUuY29tcHV0ZWQgPSB0cnVlO1xuICAgICAgdGhpcy5leHBlY3QoX3Rva2VudHlwZS50eXBlcy5icmFja2V0Uik7XG4gICAgICBiYXNlID0gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiTWVtYmVyRXhwcmVzc2lvblwiKTtcbiAgICB9IGVsc2UgaWYgKCFub0NhbGxzICYmIHRoaXMuZWF0KF90b2tlbnR5cGUudHlwZXMucGFyZW5MKSkge1xuICAgICAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0UG9zLCBzdGFydExvYyk7XG4gICAgICBub2RlLmNhbGxlZSA9IGJhc2U7XG4gICAgICBub2RlLmFyZ3VtZW50cyA9IHRoaXMucGFyc2VFeHByTGlzdChfdG9rZW50eXBlLnR5cGVzLnBhcmVuUiwgZmFsc2UpO1xuICAgICAgYmFzZSA9IHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkNhbGxFeHByZXNzaW9uXCIpO1xuICAgIH0gZWxzZSBpZiAodGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLmJhY2tRdW90ZSkge1xuICAgICAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0UG9zLCBzdGFydExvYyk7XG4gICAgICBub2RlLnRhZyA9IGJhc2U7XG4gICAgICBub2RlLnF1YXNpID0gdGhpcy5wYXJzZVRlbXBsYXRlKCk7XG4gICAgICBiYXNlID0gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiVGFnZ2VkVGVtcGxhdGVFeHByZXNzaW9uXCIpO1xuICAgIH0gZWxzZSB7XG4gICAgICByZXR1cm4gYmFzZTtcbiAgICB9XG4gIH1cbn07XG5cbi8vIFBhcnNlIGFuIGF0b21pYyBleHByZXNzaW9uIOKAlCBlaXRoZXIgYSBzaW5nbGUgdG9rZW4gdGhhdCBpcyBhblxuLy8gZXhwcmVzc2lvbiwgYW4gZXhwcmVzc2lvbiBzdGFydGVkIGJ5IGEga2V5d29yZCBsaWtlIGBmdW5jdGlvbmAgb3Jcbi8vIGBuZXdgLCBvciBhbiBleHByZXNzaW9uIHdyYXBwZWQgaW4gcHVuY3R1YXRpb24gbGlrZSBgKClgLCBgW11gLFxuLy8gb3IgYHt9YC5cblxucHAucGFyc2VFeHByQXRvbSA9IGZ1bmN0aW9uIChyZWZTaG9ydGhhbmREZWZhdWx0UG9zKSB7XG4gIHZhciBub2RlID0gdW5kZWZpbmVkLFxuICAgICAgY2FuQmVBcnJvdyA9IHRoaXMucG90ZW50aWFsQXJyb3dBdCA9PSB0aGlzLnN0YXJ0O1xuICBzd2l0Y2ggKHRoaXMudHlwZSkge1xuICAgIGNhc2UgX3Rva2VudHlwZS50eXBlcy5fc3VwZXI6XG4gICAgICBpZiAoIXRoaXMuaW5GdW5jdGlvbikgdGhpcy5yYWlzZSh0aGlzLnN0YXJ0LCBcIidzdXBlcicgb3V0c2lkZSBvZiBmdW5jdGlvbiBvciBjbGFzc1wiKTtcbiAgICBjYXNlIF90b2tlbnR5cGUudHlwZXMuX3RoaXM6XG4gICAgICB2YXIgdHlwZSA9IHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5fdGhpcyA/IFwiVGhpc0V4cHJlc3Npb25cIiA6IFwiU3VwZXJcIjtcbiAgICAgIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIHR5cGUpO1xuXG4gICAgY2FzZSBfdG9rZW50eXBlLnR5cGVzLl95aWVsZDpcbiAgICAgIGlmICh0aGlzLmluR2VuZXJhdG9yKSB0aGlzLnVuZXhwZWN0ZWQoKTtcblxuICAgIGNhc2UgX3Rva2VudHlwZS50eXBlcy5uYW1lOlxuICAgICAgdmFyIHN0YXJ0UG9zID0gdGhpcy5zdGFydCxcbiAgICAgICAgICBzdGFydExvYyA9IHRoaXMuc3RhcnRMb2M7XG4gICAgICB2YXIgaWQgPSB0aGlzLnBhcnNlSWRlbnQodGhpcy50eXBlICE9PSBfdG9rZW50eXBlLnR5cGVzLm5hbWUpO1xuICAgICAgaWYgKGNhbkJlQXJyb3cgJiYgIXRoaXMuY2FuSW5zZXJ0U2VtaWNvbG9uKCkgJiYgdGhpcy5lYXQoX3Rva2VudHlwZS50eXBlcy5hcnJvdykpIHJldHVybiB0aGlzLnBhcnNlQXJyb3dFeHByZXNzaW9uKHRoaXMuc3RhcnROb2RlQXQoc3RhcnRQb3MsIHN0YXJ0TG9jKSwgW2lkXSk7XG4gICAgICByZXR1cm4gaWQ7XG5cbiAgICBjYXNlIF90b2tlbnR5cGUudHlwZXMucmVnZXhwOlxuICAgICAgdmFyIHZhbHVlID0gdGhpcy52YWx1ZTtcbiAgICAgIG5vZGUgPSB0aGlzLnBhcnNlTGl0ZXJhbCh2YWx1ZS52YWx1ZSk7XG4gICAgICBub2RlLnJlZ2V4ID0geyBwYXR0ZXJuOiB2YWx1ZS5wYXR0ZXJuLCBmbGFnczogdmFsdWUuZmxhZ3MgfTtcbiAgICAgIHJldHVybiBub2RlO1xuXG4gICAgY2FzZSBfdG9rZW50eXBlLnR5cGVzLm51bTpjYXNlIF90b2tlbnR5cGUudHlwZXMuc3RyaW5nOlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VMaXRlcmFsKHRoaXMudmFsdWUpO1xuXG4gICAgY2FzZSBfdG9rZW50eXBlLnR5cGVzLl9udWxsOmNhc2UgX3Rva2VudHlwZS50eXBlcy5fdHJ1ZTpjYXNlIF90b2tlbnR5cGUudHlwZXMuX2ZhbHNlOlxuICAgICAgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gICAgICBub2RlLnZhbHVlID0gdGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLl9udWxsID8gbnVsbCA6IHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5fdHJ1ZTtcbiAgICAgIG5vZGUucmF3ID0gdGhpcy50eXBlLmtleXdvcmQ7XG4gICAgICB0aGlzLm5leHQoKTtcbiAgICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJMaXRlcmFsXCIpO1xuXG4gICAgY2FzZSBfdG9rZW50eXBlLnR5cGVzLnBhcmVuTDpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlUGFyZW5BbmREaXN0aW5ndWlzaEV4cHJlc3Npb24oY2FuQmVBcnJvdyk7XG5cbiAgICBjYXNlIF90b2tlbnR5cGUudHlwZXMuYnJhY2tldEw6XG4gICAgICBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgLy8gY2hlY2sgd2hldGhlciB0aGlzIGlzIGFycmF5IGNvbXByZWhlbnNpb24gb3IgcmVndWxhciBhcnJheVxuICAgICAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA3ICYmIHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5fZm9yKSB7XG4gICAgICAgIHJldHVybiB0aGlzLnBhcnNlQ29tcHJlaGVuc2lvbihub2RlLCBmYWxzZSk7XG4gICAgICB9XG4gICAgICBub2RlLmVsZW1lbnRzID0gdGhpcy5wYXJzZUV4cHJMaXN0KF90b2tlbnR5cGUudHlwZXMuYnJhY2tldFIsIHRydWUsIHRydWUsIHJlZlNob3J0aGFuZERlZmF1bHRQb3MpO1xuICAgICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkFycmF5RXhwcmVzc2lvblwiKTtcblxuICAgIGNhc2UgX3Rva2VudHlwZS50eXBlcy5icmFjZUw6XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZU9iaihmYWxzZSwgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcyk7XG5cbiAgICBjYXNlIF90b2tlbnR5cGUudHlwZXMuX2Z1bmN0aW9uOlxuICAgICAgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gICAgICB0aGlzLm5leHQoKTtcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlRnVuY3Rpb24obm9kZSwgZmFsc2UpO1xuXG4gICAgY2FzZSBfdG9rZW50eXBlLnR5cGVzLl9jbGFzczpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlQ2xhc3ModGhpcy5zdGFydE5vZGUoKSwgZmFsc2UpO1xuXG4gICAgY2FzZSBfdG9rZW50eXBlLnR5cGVzLl9uZXc6XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZU5ldygpO1xuXG4gICAgY2FzZSBfdG9rZW50eXBlLnR5cGVzLmJhY2tRdW90ZTpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlVGVtcGxhdGUoKTtcblxuICAgIGRlZmF1bHQ6XG4gICAgICB0aGlzLnVuZXhwZWN0ZWQoKTtcbiAgfVxufTtcblxucHAucGFyc2VMaXRlcmFsID0gZnVuY3Rpb24gKHZhbHVlKSB7XG4gIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgbm9kZS52YWx1ZSA9IHZhbHVlO1xuICBub2RlLnJhdyA9IHRoaXMuaW5wdXQuc2xpY2UodGhpcy5zdGFydCwgdGhpcy5lbmQpO1xuICB0aGlzLm5leHQoKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkxpdGVyYWxcIik7XG59O1xuXG5wcC5wYXJzZVBhcmVuRXhwcmVzc2lvbiA9IGZ1bmN0aW9uICgpIHtcbiAgdGhpcy5leHBlY3QoX3Rva2VudHlwZS50eXBlcy5wYXJlbkwpO1xuICB2YXIgdmFsID0gdGhpcy5wYXJzZUV4cHJlc3Npb24oKTtcbiAgdGhpcy5leHBlY3QoX3Rva2VudHlwZS50eXBlcy5wYXJlblIpO1xuICByZXR1cm4gdmFsO1xufTtcblxucHAucGFyc2VQYXJlbkFuZERpc3Rpbmd1aXNoRXhwcmVzc2lvbiA9IGZ1bmN0aW9uIChjYW5CZUFycm93KSB7XG4gIHZhciBzdGFydFBvcyA9IHRoaXMuc3RhcnQsXG4gICAgICBzdGFydExvYyA9IHRoaXMuc3RhcnRMb2MsXG4gICAgICB2YWwgPSB1bmRlZmluZWQ7XG4gIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNikge1xuICAgIHRoaXMubmV4dCgpO1xuXG4gICAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA3ICYmIHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5fZm9yKSB7XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZUNvbXByZWhlbnNpb24odGhpcy5zdGFydE5vZGVBdChzdGFydFBvcywgc3RhcnRMb2MpLCB0cnVlKTtcbiAgICB9XG5cbiAgICB2YXIgaW5uZXJTdGFydFBvcyA9IHRoaXMuc3RhcnQsXG4gICAgICAgIGlubmVyU3RhcnRMb2MgPSB0aGlzLnN0YXJ0TG9jO1xuICAgIHZhciBleHByTGlzdCA9IFtdLFxuICAgICAgICBmaXJzdCA9IHRydWU7XG4gICAgdmFyIHJlZlNob3J0aGFuZERlZmF1bHRQb3MgPSB7IHN0YXJ0OiAwIH0sXG4gICAgICAgIHNwcmVhZFN0YXJ0ID0gdW5kZWZpbmVkLFxuICAgICAgICBpbm5lclBhcmVuU3RhcnQgPSB1bmRlZmluZWQ7XG4gICAgd2hpbGUgKHRoaXMudHlwZSAhPT0gX3Rva2VudHlwZS50eXBlcy5wYXJlblIpIHtcbiAgICAgIGZpcnN0ID8gZmlyc3QgPSBmYWxzZSA6IHRoaXMuZXhwZWN0KF90b2tlbnR5cGUudHlwZXMuY29tbWEpO1xuICAgICAgaWYgKHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5lbGxpcHNpcykge1xuICAgICAgICBzcHJlYWRTdGFydCA9IHRoaXMuc3RhcnQ7XG4gICAgICAgIGV4cHJMaXN0LnB1c2godGhpcy5wYXJzZVBhcmVuSXRlbSh0aGlzLnBhcnNlUmVzdCgpKSk7XG4gICAgICAgIGJyZWFrO1xuICAgICAgfSBlbHNlIHtcbiAgICAgICAgaWYgKHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5wYXJlbkwgJiYgIWlubmVyUGFyZW5TdGFydCkge1xuICAgICAgICAgIGlubmVyUGFyZW5TdGFydCA9IHRoaXMuc3RhcnQ7XG4gICAgICAgIH1cbiAgICAgICAgZXhwckxpc3QucHVzaCh0aGlzLnBhcnNlTWF5YmVBc3NpZ24oZmFsc2UsIHJlZlNob3J0aGFuZERlZmF1bHRQb3MsIHRoaXMucGFyc2VQYXJlbkl0ZW0pKTtcbiAgICAgIH1cbiAgICB9XG4gICAgdmFyIGlubmVyRW5kUG9zID0gdGhpcy5zdGFydCxcbiAgICAgICAgaW5uZXJFbmRMb2MgPSB0aGlzLnN0YXJ0TG9jO1xuICAgIHRoaXMuZXhwZWN0KF90b2tlbnR5cGUudHlwZXMucGFyZW5SKTtcblxuICAgIGlmIChjYW5CZUFycm93ICYmICF0aGlzLmNhbkluc2VydFNlbWljb2xvbigpICYmIHRoaXMuZWF0KF90b2tlbnR5cGUudHlwZXMuYXJyb3cpKSB7XG4gICAgICBpZiAoaW5uZXJQYXJlblN0YXJ0KSB0aGlzLnVuZXhwZWN0ZWQoaW5uZXJQYXJlblN0YXJ0KTtcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlUGFyZW5BcnJvd0xpc3Qoc3RhcnRQb3MsIHN0YXJ0TG9jLCBleHByTGlzdCk7XG4gICAgfVxuXG4gICAgaWYgKCFleHByTGlzdC5sZW5ndGgpIHRoaXMudW5leHBlY3RlZCh0aGlzLmxhc3RUb2tTdGFydCk7XG4gICAgaWYgKHNwcmVhZFN0YXJ0KSB0aGlzLnVuZXhwZWN0ZWQoc3ByZWFkU3RhcnQpO1xuICAgIGlmIChyZWZTaG9ydGhhbmREZWZhdWx0UG9zLnN0YXJ0KSB0aGlzLnVuZXhwZWN0ZWQocmVmU2hvcnRoYW5kRGVmYXVsdFBvcy5zdGFydCk7XG5cbiAgICBpZiAoZXhwckxpc3QubGVuZ3RoID4gMSkge1xuICAgICAgdmFsID0gdGhpcy5zdGFydE5vZGVBdChpbm5lclN0YXJ0UG9zLCBpbm5lclN0YXJ0TG9jKTtcbiAgICAgIHZhbC5leHByZXNzaW9ucyA9IGV4cHJMaXN0O1xuICAgICAgdGhpcy5maW5pc2hOb2RlQXQodmFsLCBcIlNlcXVlbmNlRXhwcmVzc2lvblwiLCBpbm5lckVuZFBvcywgaW5uZXJFbmRMb2MpO1xuICAgIH0gZWxzZSB7XG4gICAgICB2YWwgPSBleHByTGlzdFswXTtcbiAgICB9XG4gIH0gZWxzZSB7XG4gICAgdmFsID0gdGhpcy5wYXJzZVBhcmVuRXhwcmVzc2lvbigpO1xuICB9XG5cbiAgaWYgKHRoaXMub3B0aW9ucy5wcmVzZXJ2ZVBhcmVucykge1xuICAgIHZhciBwYXIgPSB0aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0UG9zLCBzdGFydExvYyk7XG4gICAgcGFyLmV4cHJlc3Npb24gPSB2YWw7XG4gICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShwYXIsIFwiUGFyZW50aGVzaXplZEV4cHJlc3Npb25cIik7XG4gIH0gZWxzZSB7XG4gICAgcmV0dXJuIHZhbDtcbiAgfVxufTtcblxucHAucGFyc2VQYXJlbkl0ZW0gPSBmdW5jdGlvbiAoaXRlbSkge1xuICByZXR1cm4gaXRlbTtcbn07XG5cbnBwLnBhcnNlUGFyZW5BcnJvd0xpc3QgPSBmdW5jdGlvbiAoc3RhcnRQb3MsIHN0YXJ0TG9jLCBleHByTGlzdCkge1xuICByZXR1cm4gdGhpcy5wYXJzZUFycm93RXhwcmVzc2lvbih0aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0UG9zLCBzdGFydExvYyksIGV4cHJMaXN0KTtcbn07XG5cbi8vIE5ldydzIHByZWNlZGVuY2UgaXMgc2xpZ2h0bHkgdHJpY2t5LiBJdCBtdXN0IGFsbG93IGl0cyBhcmd1bWVudFxuLy8gdG8gYmUgYSBgW11gIG9yIGRvdCBzdWJzY3JpcHQgZXhwcmVzc2lvbiwgYnV0IG5vdCBhIGNhbGwg4oCUIGF0XG4vLyBsZWFzdCwgbm90IHdpdGhvdXQgd3JhcHBpbmcgaXQgaW4gcGFyZW50aGVzZXMuIFRodXMsIGl0IHVzZXMgdGhlXG5cbnZhciBlbXB0eSA9IFtdO1xuXG5wcC5wYXJzZU5ldyA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICB2YXIgbWV0YSA9IHRoaXMucGFyc2VJZGVudCh0cnVlKTtcbiAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2ICYmIHRoaXMuZWF0KF90b2tlbnR5cGUudHlwZXMuZG90KSkge1xuICAgIG5vZGUubWV0YSA9IG1ldGE7XG4gICAgbm9kZS5wcm9wZXJ0eSA9IHRoaXMucGFyc2VJZGVudCh0cnVlKTtcbiAgICBpZiAobm9kZS5wcm9wZXJ0eS5uYW1lICE9PSBcInRhcmdldFwiKSB0aGlzLnJhaXNlKG5vZGUucHJvcGVydHkuc3RhcnQsIFwiVGhlIG9ubHkgdmFsaWQgbWV0YSBwcm9wZXJ0eSBmb3IgbmV3IGlzIG5ldy50YXJnZXRcIik7XG4gICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIk1ldGFQcm9wZXJ0eVwiKTtcbiAgfVxuICB2YXIgc3RhcnRQb3MgPSB0aGlzLnN0YXJ0LFxuICAgICAgc3RhcnRMb2MgPSB0aGlzLnN0YXJ0TG9jO1xuICBub2RlLmNhbGxlZSA9IHRoaXMucGFyc2VTdWJzY3JpcHRzKHRoaXMucGFyc2VFeHByQXRvbSgpLCBzdGFydFBvcywgc3RhcnRMb2MsIHRydWUpO1xuICBpZiAodGhpcy5lYXQoX3Rva2VudHlwZS50eXBlcy5wYXJlbkwpKSBub2RlLmFyZ3VtZW50cyA9IHRoaXMucGFyc2VFeHByTGlzdChfdG9rZW50eXBlLnR5cGVzLnBhcmVuUiwgZmFsc2UpO2Vsc2Ugbm9kZS5hcmd1bWVudHMgPSBlbXB0eTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIk5ld0V4cHJlc3Npb25cIik7XG59O1xuXG4vLyBQYXJzZSB0ZW1wbGF0ZSBleHByZXNzaW9uLlxuXG5wcC5wYXJzZVRlbXBsYXRlRWxlbWVudCA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIGVsZW0gPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICBlbGVtLnZhbHVlID0ge1xuICAgIHJhdzogdGhpcy5pbnB1dC5zbGljZSh0aGlzLnN0YXJ0LCB0aGlzLmVuZCkucmVwbGFjZSgvXFxyXFxuPy9nLCAnXFxuJyksXG4gICAgY29va2VkOiB0aGlzLnZhbHVlXG4gIH07XG4gIHRoaXMubmV4dCgpO1xuICBlbGVtLnRhaWwgPSB0aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuYmFja1F1b3RlO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKGVsZW0sIFwiVGVtcGxhdGVFbGVtZW50XCIpO1xufTtcblxucHAucGFyc2VUZW1wbGF0ZSA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICB0aGlzLm5leHQoKTtcbiAgbm9kZS5leHByZXNzaW9ucyA9IFtdO1xuICB2YXIgY3VyRWx0ID0gdGhpcy5wYXJzZVRlbXBsYXRlRWxlbWVudCgpO1xuICBub2RlLnF1YXNpcyA9IFtjdXJFbHRdO1xuICB3aGlsZSAoIWN1ckVsdC50YWlsKSB7XG4gICAgdGhpcy5leHBlY3QoX3Rva2VudHlwZS50eXBlcy5kb2xsYXJCcmFjZUwpO1xuICAgIG5vZGUuZXhwcmVzc2lvbnMucHVzaCh0aGlzLnBhcnNlRXhwcmVzc2lvbigpKTtcbiAgICB0aGlzLmV4cGVjdChfdG9rZW50eXBlLnR5cGVzLmJyYWNlUik7XG4gICAgbm9kZS5xdWFzaXMucHVzaChjdXJFbHQgPSB0aGlzLnBhcnNlVGVtcGxhdGVFbGVtZW50KCkpO1xuICB9XG4gIHRoaXMubmV4dCgpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiVGVtcGxhdGVMaXRlcmFsXCIpO1xufTtcblxuLy8gUGFyc2UgYW4gb2JqZWN0IGxpdGVyYWwgb3IgYmluZGluZyBwYXR0ZXJuLlxuXG5wcC5wYXJzZU9iaiA9IGZ1bmN0aW9uIChpc1BhdHRlcm4sIHJlZlNob3J0aGFuZERlZmF1bHRQb3MpIHtcbiAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpLFxuICAgICAgZmlyc3QgPSB0cnVlLFxuICAgICAgcHJvcEhhc2ggPSB7fTtcbiAgbm9kZS5wcm9wZXJ0aWVzID0gW107XG4gIHRoaXMubmV4dCgpO1xuICB3aGlsZSAoIXRoaXMuZWF0KF90b2tlbnR5cGUudHlwZXMuYnJhY2VSKSkge1xuICAgIGlmICghZmlyc3QpIHtcbiAgICAgIHRoaXMuZXhwZWN0KF90b2tlbnR5cGUudHlwZXMuY29tbWEpO1xuICAgICAgaWYgKHRoaXMuYWZ0ZXJUcmFpbGluZ0NvbW1hKF90b2tlbnR5cGUudHlwZXMuYnJhY2VSKSkgYnJlYWs7XG4gICAgfSBlbHNlIGZpcnN0ID0gZmFsc2U7XG5cbiAgICB2YXIgcHJvcCA9IHRoaXMuc3RhcnROb2RlKCksXG4gICAgICAgIGlzR2VuZXJhdG9yID0gdW5kZWZpbmVkLFxuICAgICAgICBzdGFydFBvcyA9IHVuZGVmaW5lZCxcbiAgICAgICAgc3RhcnRMb2MgPSB1bmRlZmluZWQ7XG4gICAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KSB7XG4gICAgICBwcm9wLm1ldGhvZCA9IGZhbHNlO1xuICAgICAgcHJvcC5zaG9ydGhhbmQgPSBmYWxzZTtcbiAgICAgIGlmIChpc1BhdHRlcm4gfHwgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcykge1xuICAgICAgICBzdGFydFBvcyA9IHRoaXMuc3RhcnQ7XG4gICAgICAgIHN0YXJ0TG9jID0gdGhpcy5zdGFydExvYztcbiAgICAgIH1cbiAgICAgIGlmICghaXNQYXR0ZXJuKSBpc0dlbmVyYXRvciA9IHRoaXMuZWF0KF90b2tlbnR5cGUudHlwZXMuc3Rhcik7XG4gICAgfVxuICAgIHRoaXMucGFyc2VQcm9wZXJ0eU5hbWUocHJvcCk7XG4gICAgdGhpcy5wYXJzZVByb3BlcnR5VmFsdWUocHJvcCwgaXNQYXR0ZXJuLCBpc0dlbmVyYXRvciwgc3RhcnRQb3MsIHN0YXJ0TG9jLCByZWZTaG9ydGhhbmREZWZhdWx0UG9zKTtcbiAgICB0aGlzLmNoZWNrUHJvcENsYXNoKHByb3AsIHByb3BIYXNoKTtcbiAgICBub2RlLnByb3BlcnRpZXMucHVzaCh0aGlzLmZpbmlzaE5vZGUocHJvcCwgXCJQcm9wZXJ0eVwiKSk7XG4gIH1cbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBpc1BhdHRlcm4gPyBcIk9iamVjdFBhdHRlcm5cIiA6IFwiT2JqZWN0RXhwcmVzc2lvblwiKTtcbn07XG5cbnBwLnBhcnNlUHJvcGVydHlWYWx1ZSA9IGZ1bmN0aW9uIChwcm9wLCBpc1BhdHRlcm4sIGlzR2VuZXJhdG9yLCBzdGFydFBvcywgc3RhcnRMb2MsIHJlZlNob3J0aGFuZERlZmF1bHRQb3MpIHtcbiAgaWYgKHRoaXMuZWF0KF90b2tlbnR5cGUudHlwZXMuY29sb24pKSB7XG4gICAgcHJvcC52YWx1ZSA9IGlzUGF0dGVybiA/IHRoaXMucGFyc2VNYXliZURlZmF1bHQodGhpcy5zdGFydCwgdGhpcy5zdGFydExvYykgOiB0aGlzLnBhcnNlTWF5YmVBc3NpZ24oZmFsc2UsIHJlZlNob3J0aGFuZERlZmF1bHRQb3MpO1xuICAgIHByb3Aua2luZCA9IFwiaW5pdFwiO1xuICB9IGVsc2UgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2ICYmIHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5wYXJlbkwpIHtcbiAgICBpZiAoaXNQYXR0ZXJuKSB0aGlzLnVuZXhwZWN0ZWQoKTtcbiAgICBwcm9wLmtpbmQgPSBcImluaXRcIjtcbiAgICBwcm9wLm1ldGhvZCA9IHRydWU7XG4gICAgcHJvcC52YWx1ZSA9IHRoaXMucGFyc2VNZXRob2QoaXNHZW5lcmF0b3IpO1xuICB9IGVsc2UgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA1ICYmICFwcm9wLmNvbXB1dGVkICYmIHByb3Aua2V5LnR5cGUgPT09IFwiSWRlbnRpZmllclwiICYmIChwcm9wLmtleS5uYW1lID09PSBcImdldFwiIHx8IHByb3Aua2V5Lm5hbWUgPT09IFwic2V0XCIpICYmICh0aGlzLnR5cGUgIT0gX3Rva2VudHlwZS50eXBlcy5jb21tYSAmJiB0aGlzLnR5cGUgIT0gX3Rva2VudHlwZS50eXBlcy5icmFjZVIpKSB7XG4gICAgaWYgKGlzR2VuZXJhdG9yIHx8IGlzUGF0dGVybikgdGhpcy51bmV4cGVjdGVkKCk7XG4gICAgcHJvcC5raW5kID0gcHJvcC5rZXkubmFtZTtcbiAgICB0aGlzLnBhcnNlUHJvcGVydHlOYW1lKHByb3ApO1xuICAgIHByb3AudmFsdWUgPSB0aGlzLnBhcnNlTWV0aG9kKGZhbHNlKTtcbiAgICB2YXIgcGFyYW1Db3VudCA9IHByb3Aua2luZCA9PT0gXCJnZXRcIiA/IDAgOiAxO1xuICAgIGlmIChwcm9wLnZhbHVlLnBhcmFtcy5sZW5ndGggIT09IHBhcmFtQ291bnQpIHtcbiAgICAgIHZhciBzdGFydCA9IHByb3AudmFsdWUuc3RhcnQ7XG4gICAgICBpZiAocHJvcC5raW5kID09PSBcImdldFwiKSB0aGlzLnJhaXNlKHN0YXJ0LCBcImdldHRlciBzaG91bGQgaGF2ZSBubyBwYXJhbXNcIik7ZWxzZSB0aGlzLnJhaXNlKHN0YXJ0LCBcInNldHRlciBzaG91bGQgaGF2ZSBleGFjdGx5IG9uZSBwYXJhbVwiKTtcbiAgICB9XG4gIH0gZWxzZSBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYgJiYgIXByb3AuY29tcHV0ZWQgJiYgcHJvcC5rZXkudHlwZSA9PT0gXCJJZGVudGlmaWVyXCIpIHtcbiAgICBwcm9wLmtpbmQgPSBcImluaXRcIjtcbiAgICBpZiAoaXNQYXR0ZXJuKSB7XG4gICAgICBpZiAodGhpcy5pc0tleXdvcmQocHJvcC5rZXkubmFtZSkgfHwgdGhpcy5zdHJpY3QgJiYgKF9pZGVudGlmaWVyLnJlc2VydmVkV29yZHMuc3RyaWN0QmluZChwcm9wLmtleS5uYW1lKSB8fCBfaWRlbnRpZmllci5yZXNlcnZlZFdvcmRzLnN0cmljdChwcm9wLmtleS5uYW1lKSkgfHwgIXRoaXMub3B0aW9ucy5hbGxvd1Jlc2VydmVkICYmIHRoaXMuaXNSZXNlcnZlZFdvcmQocHJvcC5rZXkubmFtZSkpIHRoaXMucmFpc2UocHJvcC5rZXkuc3RhcnQsIFwiQmluZGluZyBcIiArIHByb3Aua2V5Lm5hbWUpO1xuICAgICAgcHJvcC52YWx1ZSA9IHRoaXMucGFyc2VNYXliZURlZmF1bHQoc3RhcnRQb3MsIHN0YXJ0TG9jLCBwcm9wLmtleSk7XG4gICAgfSBlbHNlIGlmICh0aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuZXEgJiYgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcykge1xuICAgICAgaWYgKCFyZWZTaG9ydGhhbmREZWZhdWx0UG9zLnN0YXJ0KSByZWZTaG9ydGhhbmREZWZhdWx0UG9zLnN0YXJ0ID0gdGhpcy5zdGFydDtcbiAgICAgIHByb3AudmFsdWUgPSB0aGlzLnBhcnNlTWF5YmVEZWZhdWx0KHN0YXJ0UG9zLCBzdGFydExvYywgcHJvcC5rZXkpO1xuICAgIH0gZWxzZSB7XG4gICAgICBwcm9wLnZhbHVlID0gcHJvcC5rZXk7XG4gICAgfVxuICAgIHByb3Auc2hvcnRoYW5kID0gdHJ1ZTtcbiAgfSBlbHNlIHRoaXMudW5leHBlY3RlZCgpO1xufTtcblxucHAucGFyc2VQcm9wZXJ0eU5hbWUgPSBmdW5jdGlvbiAocHJvcCkge1xuICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYpIHtcbiAgICBpZiAodGhpcy5lYXQoX3Rva2VudHlwZS50eXBlcy5icmFja2V0TCkpIHtcbiAgICAgIHByb3AuY29tcHV0ZWQgPSB0cnVlO1xuICAgICAgcHJvcC5rZXkgPSB0aGlzLnBhcnNlTWF5YmVBc3NpZ24oKTtcbiAgICAgIHRoaXMuZXhwZWN0KF90b2tlbnR5cGUudHlwZXMuYnJhY2tldFIpO1xuICAgICAgcmV0dXJuIHByb3Aua2V5O1xuICAgIH0gZWxzZSB7XG4gICAgICBwcm9wLmNvbXB1dGVkID0gZmFsc2U7XG4gICAgfVxuICB9XG4gIHJldHVybiBwcm9wLmtleSA9IHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5udW0gfHwgdGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLnN0cmluZyA/IHRoaXMucGFyc2VFeHByQXRvbSgpIDogdGhpcy5wYXJzZUlkZW50KHRydWUpO1xufTtcblxuLy8gSW5pdGlhbGl6ZSBlbXB0eSBmdW5jdGlvbiBub2RlLlxuXG5wcC5pbml0RnVuY3Rpb24gPSBmdW5jdGlvbiAobm9kZSkge1xuICBub2RlLmlkID0gbnVsbDtcbiAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KSB7XG4gICAgbm9kZS5nZW5lcmF0b3IgPSBmYWxzZTtcbiAgICBub2RlLmV4cHJlc3Npb24gPSBmYWxzZTtcbiAgfVxufTtcblxuLy8gUGFyc2Ugb2JqZWN0IG9yIGNsYXNzIG1ldGhvZC5cblxucHAucGFyc2VNZXRob2QgPSBmdW5jdGlvbiAoaXNHZW5lcmF0b3IpIHtcbiAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICB0aGlzLmluaXRGdW5jdGlvbihub2RlKTtcbiAgdGhpcy5leHBlY3QoX3Rva2VudHlwZS50eXBlcy5wYXJlbkwpO1xuICBub2RlLnBhcmFtcyA9IHRoaXMucGFyc2VCaW5kaW5nTGlzdChfdG9rZW50eXBlLnR5cGVzLnBhcmVuUiwgZmFsc2UsIGZhbHNlKTtcbiAgdmFyIGFsbG93RXhwcmVzc2lvbkJvZHkgPSB1bmRlZmluZWQ7XG4gIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNikge1xuICAgIG5vZGUuZ2VuZXJhdG9yID0gaXNHZW5lcmF0b3I7XG4gIH1cbiAgdGhpcy5wYXJzZUZ1bmN0aW9uQm9keShub2RlLCBmYWxzZSk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJGdW5jdGlvbkV4cHJlc3Npb25cIik7XG59O1xuXG4vLyBQYXJzZSBhcnJvdyBmdW5jdGlvbiBleHByZXNzaW9uIHdpdGggZ2l2ZW4gcGFyYW1ldGVycy5cblxucHAucGFyc2VBcnJvd0V4cHJlc3Npb24gPSBmdW5jdGlvbiAobm9kZSwgcGFyYW1zKSB7XG4gIHRoaXMuaW5pdEZ1bmN0aW9uKG5vZGUpO1xuICBub2RlLnBhcmFtcyA9IHRoaXMudG9Bc3NpZ25hYmxlTGlzdChwYXJhbXMsIHRydWUpO1xuICB0aGlzLnBhcnNlRnVuY3Rpb25Cb2R5KG5vZGUsIHRydWUpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiQXJyb3dGdW5jdGlvbkV4cHJlc3Npb25cIik7XG59O1xuXG4vLyBQYXJzZSBmdW5jdGlvbiBib2R5IGFuZCBjaGVjayBwYXJhbWV0ZXJzLlxuXG5wcC5wYXJzZUZ1bmN0aW9uQm9keSA9IGZ1bmN0aW9uIChub2RlLCBhbGxvd0V4cHJlc3Npb24pIHtcbiAgdmFyIGlzRXhwcmVzc2lvbiA9IGFsbG93RXhwcmVzc2lvbiAmJiB0aGlzLnR5cGUgIT09IF90b2tlbnR5cGUudHlwZXMuYnJhY2VMO1xuXG4gIGlmIChpc0V4cHJlc3Npb24pIHtcbiAgICBub2RlLmJvZHkgPSB0aGlzLnBhcnNlTWF5YmVBc3NpZ24oKTtcbiAgICBub2RlLmV4cHJlc3Npb24gPSB0cnVlO1xuICB9IGVsc2Uge1xuICAgIC8vIFN0YXJ0IGEgbmV3IHNjb3BlIHdpdGggcmVnYXJkIHRvIGxhYmVscyBhbmQgdGhlIGBpbkZ1bmN0aW9uYFxuICAgIC8vIGZsYWcgKHJlc3RvcmUgdGhlbSB0byB0aGVpciBvbGQgdmFsdWUgYWZ0ZXJ3YXJkcykuXG4gICAgdmFyIG9sZEluRnVuYyA9IHRoaXMuaW5GdW5jdGlvbixcbiAgICAgICAgb2xkSW5HZW4gPSB0aGlzLmluR2VuZXJhdG9yLFxuICAgICAgICBvbGRMYWJlbHMgPSB0aGlzLmxhYmVscztcbiAgICB0aGlzLmluRnVuY3Rpb24gPSB0cnVlO3RoaXMuaW5HZW5lcmF0b3IgPSBub2RlLmdlbmVyYXRvcjt0aGlzLmxhYmVscyA9IFtdO1xuICAgIG5vZGUuYm9keSA9IHRoaXMucGFyc2VCbG9jayh0cnVlKTtcbiAgICBub2RlLmV4cHJlc3Npb24gPSBmYWxzZTtcbiAgICB0aGlzLmluRnVuY3Rpb24gPSBvbGRJbkZ1bmM7dGhpcy5pbkdlbmVyYXRvciA9IG9sZEluR2VuO3RoaXMubGFiZWxzID0gb2xkTGFiZWxzO1xuICB9XG5cbiAgLy8gSWYgdGhpcyBpcyBhIHN0cmljdCBtb2RlIGZ1bmN0aW9uLCB2ZXJpZnkgdGhhdCBhcmd1bWVudCBuYW1lc1xuICAvLyBhcmUgbm90IHJlcGVhdGVkLCBhbmQgaXQgZG9lcyBub3QgdHJ5IHRvIGJpbmQgdGhlIHdvcmRzIGBldmFsYFxuICAvLyBvciBgYXJndW1lbnRzYC5cbiAgaWYgKHRoaXMuc3RyaWN0IHx8ICFpc0V4cHJlc3Npb24gJiYgbm9kZS5ib2R5LmJvZHkubGVuZ3RoICYmIHRoaXMuaXNVc2VTdHJpY3Qobm9kZS5ib2R5LmJvZHlbMF0pKSB7XG4gICAgdmFyIG5hbWVIYXNoID0ge30sXG4gICAgICAgIG9sZFN0cmljdCA9IHRoaXMuc3RyaWN0O1xuICAgIHRoaXMuc3RyaWN0ID0gdHJ1ZTtcbiAgICBpZiAobm9kZS5pZCkgdGhpcy5jaGVja0xWYWwobm9kZS5pZCwgdHJ1ZSk7XG4gICAgZm9yICh2YXIgaSA9IDA7IGkgPCBub2RlLnBhcmFtcy5sZW5ndGg7IGkrKykge1xuICAgICAgdGhpcy5jaGVja0xWYWwobm9kZS5wYXJhbXNbaV0sIHRydWUsIG5hbWVIYXNoKTtcbiAgICB9dGhpcy5zdHJpY3QgPSBvbGRTdHJpY3Q7XG4gIH1cbn07XG5cbi8vIFBhcnNlcyBhIGNvbW1hLXNlcGFyYXRlZCBsaXN0IG9mIGV4cHJlc3Npb25zLCBhbmQgcmV0dXJucyB0aGVtIGFzXG4vLyBhbiBhcnJheS4gYGNsb3NlYCBpcyB0aGUgdG9rZW4gdHlwZSB0aGF0IGVuZHMgdGhlIGxpc3QsIGFuZFxuLy8gYGFsbG93RW1wdHlgIGNhbiBiZSB0dXJuZWQgb24gdG8gYWxsb3cgc3Vic2VxdWVudCBjb21tYXMgd2l0aFxuLy8gbm90aGluZyBpbiBiZXR3ZWVuIHRoZW0gdG8gYmUgcGFyc2VkIGFzIGBudWxsYCAod2hpY2ggaXMgbmVlZGVkXG4vLyBmb3IgYXJyYXkgbGl0ZXJhbHMpLlxuXG5wcC5wYXJzZUV4cHJMaXN0ID0gZnVuY3Rpb24gKGNsb3NlLCBhbGxvd1RyYWlsaW5nQ29tbWEsIGFsbG93RW1wdHksIHJlZlNob3J0aGFuZERlZmF1bHRQb3MpIHtcbiAgdmFyIGVsdHMgPSBbXSxcbiAgICAgIGZpcnN0ID0gdHJ1ZTtcbiAgd2hpbGUgKCF0aGlzLmVhdChjbG9zZSkpIHtcbiAgICBpZiAoIWZpcnN0KSB7XG4gICAgICB0aGlzLmV4cGVjdChfdG9rZW50eXBlLnR5cGVzLmNvbW1hKTtcbiAgICAgIGlmIChhbGxvd1RyYWlsaW5nQ29tbWEgJiYgdGhpcy5hZnRlclRyYWlsaW5nQ29tbWEoY2xvc2UpKSBicmVhaztcbiAgICB9IGVsc2UgZmlyc3QgPSBmYWxzZTtcblxuICAgIHZhciBlbHQgPSB1bmRlZmluZWQ7XG4gICAgaWYgKGFsbG93RW1wdHkgJiYgdGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLmNvbW1hKSBlbHQgPSBudWxsO2Vsc2UgaWYgKHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5lbGxpcHNpcykgZWx0ID0gdGhpcy5wYXJzZVNwcmVhZChyZWZTaG9ydGhhbmREZWZhdWx0UG9zKTtlbHNlIGVsdCA9IHRoaXMucGFyc2VNYXliZUFzc2lnbihmYWxzZSwgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcyk7XG4gICAgZWx0cy5wdXNoKGVsdCk7XG4gIH1cbiAgcmV0dXJuIGVsdHM7XG59O1xuXG4vLyBQYXJzZSB0aGUgbmV4dCB0b2tlbiBhcyBhbiBpZGVudGlmaWVyLiBJZiBgbGliZXJhbGAgaXMgdHJ1ZSAodXNlZFxuLy8gd2hlbiBwYXJzaW5nIHByb3BlcnRpZXMpLCBpdCB3aWxsIGFsc28gY29udmVydCBrZXl3b3JkcyBpbnRvXG4vLyBpZGVudGlmaWVycy5cblxucHAucGFyc2VJZGVudCA9IGZ1bmN0aW9uIChsaWJlcmFsKSB7XG4gIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgaWYgKGxpYmVyYWwgJiYgdGhpcy5vcHRpb25zLmFsbG93UmVzZXJ2ZWQgPT0gXCJuZXZlclwiKSBsaWJlcmFsID0gZmFsc2U7XG4gIGlmICh0aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMubmFtZSkge1xuICAgIGlmICghbGliZXJhbCAmJiAoIXRoaXMub3B0aW9ucy5hbGxvd1Jlc2VydmVkICYmIHRoaXMuaXNSZXNlcnZlZFdvcmQodGhpcy52YWx1ZSkgfHwgdGhpcy5zdHJpY3QgJiYgX2lkZW50aWZpZXIucmVzZXJ2ZWRXb3Jkcy5zdHJpY3QodGhpcy52YWx1ZSkgJiYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2IHx8IHRoaXMuaW5wdXQuc2xpY2UodGhpcy5zdGFydCwgdGhpcy5lbmQpLmluZGV4T2YoXCJcXFxcXCIpID09IC0xKSkpIHRoaXMucmFpc2UodGhpcy5zdGFydCwgXCJUaGUga2V5d29yZCAnXCIgKyB0aGlzLnZhbHVlICsgXCInIGlzIHJlc2VydmVkXCIpO1xuICAgIG5vZGUubmFtZSA9IHRoaXMudmFsdWU7XG4gIH0gZWxzZSBpZiAobGliZXJhbCAmJiB0aGlzLnR5cGUua2V5d29yZCkge1xuICAgIG5vZGUubmFtZSA9IHRoaXMudHlwZS5rZXl3b3JkO1xuICB9IGVsc2Uge1xuICAgIHRoaXMudW5leHBlY3RlZCgpO1xuICB9XG4gIHRoaXMubmV4dCgpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiSWRlbnRpZmllclwiKTtcbn07XG5cbi8vIFBhcnNlcyB5aWVsZCBleHByZXNzaW9uIGluc2lkZSBnZW5lcmF0b3IuXG5cbnBwLnBhcnNlWWllbGQgPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgdGhpcy5uZXh0KCk7XG4gIGlmICh0aGlzLnR5cGUgPT0gX3Rva2VudHlwZS50eXBlcy5zZW1pIHx8IHRoaXMuY2FuSW5zZXJ0U2VtaWNvbG9uKCkgfHwgdGhpcy50eXBlICE9IF90b2tlbnR5cGUudHlwZXMuc3RhciAmJiAhdGhpcy50eXBlLnN0YXJ0c0V4cHIpIHtcbiAgICBub2RlLmRlbGVnYXRlID0gZmFsc2U7XG4gICAgbm9kZS5hcmd1bWVudCA9IG51bGw7XG4gIH0gZWxzZSB7XG4gICAgbm9kZS5kZWxlZ2F0ZSA9IHRoaXMuZWF0KF90b2tlbnR5cGUudHlwZXMuc3Rhcik7XG4gICAgbm9kZS5hcmd1bWVudCA9IHRoaXMucGFyc2VNYXliZUFzc2lnbigpO1xuICB9XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJZaWVsZEV4cHJlc3Npb25cIik7XG59O1xuXG4vLyBQYXJzZXMgYXJyYXkgYW5kIGdlbmVyYXRvciBjb21wcmVoZW5zaW9ucy5cblxucHAucGFyc2VDb21wcmVoZW5zaW9uID0gZnVuY3Rpb24gKG5vZGUsIGlzR2VuZXJhdG9yKSB7XG4gIG5vZGUuYmxvY2tzID0gW107XG4gIHdoaWxlICh0aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuX2Zvcikge1xuICAgIHZhciBibG9jayA9IHRoaXMuc3RhcnROb2RlKCk7XG4gICAgdGhpcy5uZXh0KCk7XG4gICAgdGhpcy5leHBlY3QoX3Rva2VudHlwZS50eXBlcy5wYXJlbkwpO1xuICAgIGJsb2NrLmxlZnQgPSB0aGlzLnBhcnNlQmluZGluZ0F0b20oKTtcbiAgICB0aGlzLmNoZWNrTFZhbChibG9jay5sZWZ0LCB0cnVlKTtcbiAgICB0aGlzLmV4cGVjdENvbnRleHR1YWwoXCJvZlwiKTtcbiAgICBibG9jay5yaWdodCA9IHRoaXMucGFyc2VFeHByZXNzaW9uKCk7XG4gICAgdGhpcy5leHBlY3QoX3Rva2VudHlwZS50eXBlcy5wYXJlblIpO1xuICAgIG5vZGUuYmxvY2tzLnB1c2godGhpcy5maW5pc2hOb2RlKGJsb2NrLCBcIkNvbXByZWhlbnNpb25CbG9ja1wiKSk7XG4gIH1cbiAgbm9kZS5maWx0ZXIgPSB0aGlzLmVhdChfdG9rZW50eXBlLnR5cGVzLl9pZikgPyB0aGlzLnBhcnNlUGFyZW5FeHByZXNzaW9uKCkgOiBudWxsO1xuICBub2RlLmJvZHkgPSB0aGlzLnBhcnNlRXhwcmVzc2lvbigpO1xuICB0aGlzLmV4cGVjdChpc0dlbmVyYXRvciA/IF90b2tlbnR5cGUudHlwZXMucGFyZW5SIDogX3Rva2VudHlwZS50eXBlcy5icmFja2V0Uik7XG4gIG5vZGUuZ2VuZXJhdG9yID0gaXNHZW5lcmF0b3I7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJDb21wcmVoZW5zaW9uRXhwcmVzc2lvblwiKTtcbn07XG5cbn0se1wiLi9pZGVudGlmaWVyXCI6MixcIi4vc3RhdGVcIjoxMCxcIi4vdG9rZW50eXBlXCI6MTQsXCIuL3V0aWxcIjoxNX1dLDI6W2Z1bmN0aW9uKF9kZXJlcV8sbW9kdWxlLGV4cG9ydHMpe1xuLy8gVGhpcyBpcyBhIHRyaWNrIHRha2VuIGZyb20gRXNwcmltYS4gSXQgdHVybnMgb3V0IHRoYXQsIG9uXG4vLyBub24tQ2hyb21lIGJyb3dzZXJzLCB0byBjaGVjayB3aGV0aGVyIGEgc3RyaW5nIGlzIGluIGEgc2V0LCBhXG4vLyBwcmVkaWNhdGUgY29udGFpbmluZyBhIGJpZyB1Z2x5IGBzd2l0Y2hgIHN0YXRlbWVudCBpcyBmYXN0ZXIgdGhhblxuLy8gYSByZWd1bGFyIGV4cHJlc3Npb24sIGFuZCBvbiBDaHJvbWUgdGhlIHR3byBhcmUgYWJvdXQgb24gcGFyLlxuLy8gVGhpcyBmdW5jdGlvbiB1c2VzIGBldmFsYCAobm9uLWxleGljYWwpIHRvIHByb2R1Y2Ugc3VjaCBhXG4vLyBwcmVkaWNhdGUgZnJvbSBhIHNwYWNlLXNlcGFyYXRlZCBzdHJpbmcgb2Ygd29yZHMuXG4vL1xuLy8gSXQgc3RhcnRzIGJ5IHNvcnRpbmcgdGhlIHdvcmRzIGJ5IGxlbmd0aC5cblxuXCJ1c2Ugc3RyaWN0XCI7XG5cbmV4cG9ydHMuX19lc01vZHVsZSA9IHRydWU7XG5leHBvcnRzLmlzSWRlbnRpZmllclN0YXJ0ID0gaXNJZGVudGlmaWVyU3RhcnQ7XG5leHBvcnRzLmlzSWRlbnRpZmllckNoYXIgPSBpc0lkZW50aWZpZXJDaGFyO1xuZnVuY3Rpb24gbWFrZVByZWRpY2F0ZSh3b3Jkcykge1xuICB3b3JkcyA9IHdvcmRzLnNwbGl0KFwiIFwiKTtcbiAgdmFyIGYgPSBcIlwiLFxuICAgICAgY2F0cyA9IFtdO1xuICBvdXQ6IGZvciAodmFyIGkgPSAwOyBpIDwgd29yZHMubGVuZ3RoOyArK2kpIHtcbiAgICBmb3IgKHZhciBqID0gMDsgaiA8IGNhdHMubGVuZ3RoOyArK2opIHtcbiAgICAgIGlmIChjYXRzW2pdWzBdLmxlbmd0aCA9PSB3b3Jkc1tpXS5sZW5ndGgpIHtcbiAgICAgICAgY2F0c1tqXS5wdXNoKHdvcmRzW2ldKTtcbiAgICAgICAgY29udGludWUgb3V0O1xuICAgICAgfVxuICAgIH1jYXRzLnB1c2goW3dvcmRzW2ldXSk7XG4gIH1cbiAgZnVuY3Rpb24gY29tcGFyZVRvKGFycikge1xuICAgIGlmIChhcnIubGVuZ3RoID09IDEpIHJldHVybiBmICs9IFwicmV0dXJuIHN0ciA9PT0gXCIgKyBKU09OLnN0cmluZ2lmeShhcnJbMF0pICsgXCI7XCI7XG4gICAgZiArPSBcInN3aXRjaChzdHIpe1wiO1xuICAgIGZvciAodmFyIGkgPSAwOyBpIDwgYXJyLmxlbmd0aDsgKytpKSB7XG4gICAgICBmICs9IFwiY2FzZSBcIiArIEpTT04uc3RyaW5naWZ5KGFycltpXSkgKyBcIjpcIjtcbiAgICB9ZiArPSBcInJldHVybiB0cnVlfXJldHVybiBmYWxzZTtcIjtcbiAgfVxuXG4gIC8vIFdoZW4gdGhlcmUgYXJlIG1vcmUgdGhhbiB0aHJlZSBsZW5ndGggY2F0ZWdvcmllcywgYW4gb3V0ZXJcbiAgLy8gc3dpdGNoIGZpcnN0IGRpc3BhdGNoZXMgb24gdGhlIGxlbmd0aHMsIHRvIHNhdmUgb24gY29tcGFyaXNvbnMuXG5cbiAgaWYgKGNhdHMubGVuZ3RoID4gMykge1xuICAgIGNhdHMuc29ydChmdW5jdGlvbiAoYSwgYikge1xuICAgICAgcmV0dXJuIGIubGVuZ3RoIC0gYS5sZW5ndGg7XG4gICAgfSk7XG4gICAgZiArPSBcInN3aXRjaChzdHIubGVuZ3RoKXtcIjtcbiAgICBmb3IgKHZhciBpID0gMDsgaSA8IGNhdHMubGVuZ3RoOyArK2kpIHtcbiAgICAgIHZhciBjYXQgPSBjYXRzW2ldO1xuICAgICAgZiArPSBcImNhc2UgXCIgKyBjYXRbMF0ubGVuZ3RoICsgXCI6XCI7XG4gICAgICBjb21wYXJlVG8oY2F0KTtcbiAgICB9XG4gICAgZiArPSBcIn1cIjtcblxuICAgIC8vIE90aGVyd2lzZSwgc2ltcGx5IGdlbmVyYXRlIGEgZmxhdCBgc3dpdGNoYCBzdGF0ZW1lbnQuXG4gIH0gZWxzZSB7XG4gICAgICBjb21wYXJlVG8od29yZHMpO1xuICAgIH1cbiAgcmV0dXJuIG5ldyBGdW5jdGlvbihcInN0clwiLCBmKTtcbn1cblxuLy8gUmVzZXJ2ZWQgd29yZCBsaXN0cyBmb3IgdmFyaW91cyBkaWFsZWN0cyBvZiB0aGUgbGFuZ3VhZ2VcblxudmFyIHJlc2VydmVkV29yZHMgPSB7XG4gIDM6IG1ha2VQcmVkaWNhdGUoXCJhYnN0cmFjdCBib29sZWFuIGJ5dGUgY2hhciBjbGFzcyBkb3VibGUgZW51bSBleHBvcnQgZXh0ZW5kcyBmaW5hbCBmbG9hdCBnb3RvIGltcGxlbWVudHMgaW1wb3J0IGludCBpbnRlcmZhY2UgbG9uZyBuYXRpdmUgcGFja2FnZSBwcml2YXRlIHByb3RlY3RlZCBwdWJsaWMgc2hvcnQgc3RhdGljIHN1cGVyIHN5bmNocm9uaXplZCB0aHJvd3MgdHJhbnNpZW50IHZvbGF0aWxlXCIpLFxuICA1OiBtYWtlUHJlZGljYXRlKFwiY2xhc3MgZW51bSBleHRlbmRzIHN1cGVyIGNvbnN0IGV4cG9ydCBpbXBvcnRcIiksXG4gIDY6IG1ha2VQcmVkaWNhdGUoXCJlbnVtIGF3YWl0XCIpLFxuICBzdHJpY3Q6IG1ha2VQcmVkaWNhdGUoXCJpbXBsZW1lbnRzIGludGVyZmFjZSBsZXQgcGFja2FnZSBwcml2YXRlIHByb3RlY3RlZCBwdWJsaWMgc3RhdGljIHlpZWxkXCIpLFxuICBzdHJpY3RCaW5kOiBtYWtlUHJlZGljYXRlKFwiZXZhbCBhcmd1bWVudHNcIilcbn07XG5cbmV4cG9ydHMucmVzZXJ2ZWRXb3JkcyA9IHJlc2VydmVkV29yZHM7XG4vLyBBbmQgdGhlIGtleXdvcmRzXG5cbnZhciBlY21hNUFuZExlc3NLZXl3b3JkcyA9IFwiYnJlYWsgY2FzZSBjYXRjaCBjb250aW51ZSBkZWJ1Z2dlciBkZWZhdWx0IGRvIGVsc2UgZmluYWxseSBmb3IgZnVuY3Rpb24gaWYgcmV0dXJuIHN3aXRjaCB0aHJvdyB0cnkgdmFyIHdoaWxlIHdpdGggbnVsbCB0cnVlIGZhbHNlIGluc3RhbmNlb2YgdHlwZW9mIHZvaWQgZGVsZXRlIG5ldyBpbiB0aGlzXCI7XG5cbnZhciBrZXl3b3JkcyA9IHtcbiAgNTogbWFrZVByZWRpY2F0ZShlY21hNUFuZExlc3NLZXl3b3JkcyksXG4gIDY6IG1ha2VQcmVkaWNhdGUoZWNtYTVBbmRMZXNzS2V5d29yZHMgKyBcIiBsZXQgY29uc3QgY2xhc3MgZXh0ZW5kcyBleHBvcnQgaW1wb3J0IHlpZWxkIHN1cGVyXCIpXG59O1xuXG5leHBvcnRzLmtleXdvcmRzID0ga2V5d29yZHM7XG4vLyAjIyBDaGFyYWN0ZXIgY2F0ZWdvcmllc1xuXG4vLyBCaWcgdWdseSByZWd1bGFyIGV4cHJlc3Npb25zIHRoYXQgbWF0Y2ggY2hhcmFjdGVycyBpbiB0aGVcbi8vIHdoaXRlc3BhY2UsIGlkZW50aWZpZXIsIGFuZCBpZGVudGlmaWVyLXN0YXJ0IGNhdGVnb3JpZXMuIFRoZXNlXG4vLyBhcmUgb25seSBhcHBsaWVkIHdoZW4gYSBjaGFyYWN0ZXIgaXMgZm91bmQgdG8gYWN0dWFsbHkgaGF2ZSBhXG4vLyBjb2RlIHBvaW50IGFib3ZlIDEyOC5cbi8vIEdlbmVyYXRlZCBieSBgdG9vbHMvZ2VuZXJhdGUtaWRlbnRpZmllci1yZWdleC5qc2AuXG5cbnZhciBub25BU0NJSWlkZW50aWZpZXJTdGFydENoYXJzID0gXCLCqsK1wrrDgC3DlsOYLcO2w7gty4HLhi3LkcugLcuky6zLrs2wLc20zbbNt826Lc29zb/Ohs6ILc6KzozOji3Ooc6jLc+1z7ct0oHSii3Ur9SxLdWW1ZnVoS3Wh9eQLdeq17At17LYoC3Zitmu2a/ZsS3bk9uV26Xbptuu26/bui3bvNu/3JDcki3cr92NLd6l3rHfii3fqt+037XfuuCggC3goJXgoJrgoKTgoKjgoYAt4KGY4KKgLeCisuCkhC3gpLngpL3gpZDgpZgt4KWh4KWxLeCmgOCmhS3gpozgpo/gppDgppMt4Kao4KaqLeCmsOCmsuCmti3gprngpr3gp47gp5zgp53gp58t4Keh4Kew4Kex4KiFLeCoiuCoj+CokOCoky3gqKjgqKot4Kiw4Kiy4Kiz4Ki14Ki24Ki44Ki54KmZLeCpnOCpnuCpsi3gqbTgqoUt4KqN4KqPLeCqkeCqky3gqqjgqqot4Kqw4Kqy4Kqz4Kq1LeCqueCqveCrkOCroOCroeCshS3grIzgrI/grJDgrJMt4Kyo4KyqLeCssOCssuCss+CstS3grLngrL3grZzgrZ3grZ8t4K2h4K2x4K6D4K6FLeCuiuCuji3grpDgrpIt4K6V4K6Z4K6a4K6c4K6e4K6f4K6j4K6k4K6oLeCuquCuri3grrngr5DgsIUt4LCM4LCOLeCwkOCwki3gsKjgsKot4LC54LC94LGY4LGZ4LGg4LGh4LKFLeCyjOCyji3gspDgspIt4LKo4LKqLeCys+CytS3gsrngsr3gs57gs6Dgs6Hgs7Hgs7LgtIUt4LSM4LSOLeC0kOC0ki3gtLrgtL3gtY7gtaDgtaHgtbot4LW/4LaFLeC2luC2mi3gtrHgtrMt4La74La94LeALeC3huC4gS3guLDguLLguLPguYAt4LmG4LqB4LqC4LqE4LqH4LqI4LqK4LqN4LqULeC6l+C6mS3gup/guqEt4Lqj4Lql4Lqn4Lqq4Lqr4LqtLeC6sOC6suC6s+C6veC7gC3gu4Tgu4bgu5wt4Luf4LyA4L2ALeC9h+C9iS3gvazgvogt4L6M4YCALeGAquGAv+GBkC3hgZXhgZot4YGd4YGh4YGl4YGm4YGuLeGBsOGBtS3hgoHhgo7hgqAt4YOF4YOH4YON4YOQLeGDuuGDvC3hiYjhiYot4YmN4YmQLeGJluGJmOGJmi3hiZ3hiaAt4YqI4YqKLeGKjeGKkC3hirDhirIt4Yq14Yq4LeGKvuGLgOGLgi3hi4Xhi4gt4YuW4YuYLeGMkOGMki3hjJXhjJgt4Y2a4Y6ALeGOj+GOoC3hj7ThkIEt4Zms4ZmvLeGZv+GagS3hmprhmqAt4Zuq4ZuuLeGbuOGcgC3hnIzhnI4t4ZyR4ZygLeGcseGdgC3hnZHhnaAt4Z2s4Z2uLeGdsOGegC3hnrPhn5fhn5zhoKAt4aG34aKALeGiqOGiquGisC3ho7XhpIAt4aSe4aWQLeGlreGlsC3hpbThpoAt4aar4aeBLeGnh+GogC3hqJbhqKAt4amU4aqn4ayFLeGss+GthS3hrYvhroMt4a6g4a6u4a6v4a66LeGvpeGwgC3hsKPhsY0t4bGP4bGaLeGxveGzqS3hs6zhs64t4bOx4bO14bO24bSALeG2v+G4gC3hvJXhvJgt4byd4bygLeG9heG9iC3hvY3hvZAt4b2X4b2Z4b2b4b2d4b2fLeG9veG+gC3hvrThvrYt4b684b6+4b+CLeG/hOG/hi3hv4zhv5At4b+T4b+WLeG/m+G/oC3hv6zhv7It4b+04b+2LeG/vOKBseKBv+KCkC3igpzihILihIfihIot4oST4oSV4oSYLeKEneKEpOKEpuKEqOKEqi3ihLnihLwt4oS/4oWFLeKFieKFjuKFoC3ihojisIAt4rCu4rCwLeKxnuKxoC3is6Tis6st4rOu4rOy4rOz4rSALeK0peK0p+K0reK0sC3itafita/itoAt4raW4ragLeK2puK2qC3itq7itrAt4ra24ra4LeK2vuK3gC3it4bit4gt4reO4reQLeK3luK3mC3it57jgIUt44CH44ChLeOAqeOAsS3jgLXjgLgt44C844GBLeOCluOCmy3jgp/jgqEt44O644O8LeODv+OEhS3jhK3jhLEt44aO44agLeOGuuOHsC3jh7/jkIAt5La15LiALem/jOqAgC3qkozqk5At6pO96pSALeqYjOqYkC3qmJ/qmKrqmKvqmYAt6pmu6pm/LeqaneqaoC3qm6/qnJct6pyf6pyiLeqeiOqeiy3qno7qnpAt6p6t6p6w6p6x6p+3Leqggeqggy3qoIXqoIct6qCK6qCMLeqgouqhgC3qobPqooIt6qKz6qOyLeqjt+qju+qkii3qpKXqpLAt6qWG6qWgLeqlvOqmhC3qprLqp4/qp6At6qek6qemLeqnr+qnui3qp77qqIAt6qio6qmALeqpguqphC3qqYvqqaAt6qm26qm66qm+Leqqr+qqseqqteqqtuqquS3qqr3qq4Dqq4Lqq5st6qud6qugLeqrquqrsi3qq7TqrIEt6qyG6qyJLeqsjuqskS3qrJbqrKAt6qym6qyoLeqsruqssC3qrZrqrZwt6q2f6q2k6q2l6q+ALeqvouqwgC3tnqPtnrAt7Z+G7Z+LLe2fu++kgC3vqa3vqbAt76uZ76yALe+shu+sky3vrJfvrJ3vrJ8t76yo76yqLe+stu+suC3vrLzvrL7vrYDvrYHvrYPvrYTvrYYt766x76+TLe+0ve+1kC3vto/vtpIt77eH77ewLe+3u++5sC3vubTvubYt77u877yhLe+8uu+9gS3vvZrvvaYt776+77+CLe+/h++/ii3vv4/vv5It77+X77+aLe+/nFwiO1xudmFyIG5vbkFTQ0lJaWRlbnRpZmllckNoYXJzID0gXCLigIzigI3Ct8yALc2vzofSgy3Sh9aRLda91r/XgdeC14TXhdeH2JAt2JrZiy3Zqdmw25Yt25zbny3bpNun26jbqi3brduwLdu53JHcsC3dit6mLd6w34At34nfqy3fs+Cgli3goJngoJst4KCj4KClLeCgp+CgqS3goK3goZkt4KGb4KOkLeCkg+Ckui3gpLzgpL4t4KWP4KWRLeCll+ClouClo+Clpi3gpa/gpoEt4KaD4Ka84Ka+LeCnhOCnh+CniOCniy3gp43gp5fgp6Lgp6Pgp6Yt4Kev4KiBLeCog+CovOCovi3gqYLgqYfgqYjgqYst4KmN4KmR4KmmLeCpseCpteCqgS3gqoPgqrzgqr4t4KuF4KuHLeCrieCriy3gq43gq6Lgq6Pgq6Yt4Kuv4KyBLeCsg+CsvOCsvi3grYTgrYfgrYjgrYst4K2N4K2W4K2X4K2i4K2j4K2mLeCtr+CuguCuvi3gr4Lgr4Yt4K+I4K+KLeCvjeCvl+Cvpi3gr6/gsIAt4LCD4LC+LeCxhOCxhi3gsYjgsYot4LGN4LGV4LGW4LGi4LGj4LGmLeCxr+CygS3gsoPgsrzgsr4t4LOE4LOGLeCziOCzii3gs43gs5Xgs5bgs6Lgs6Pgs6Yt4LOv4LSBLeC0g+C0vi3gtYTgtYYt4LWI4LWKLeC1jeC1l+C1ouC1o+C1pi3gta/gtoLgtoPgt4rgt48t4LeU4LeW4LeYLeC3n+C3pi3gt6/gt7Lgt7PguLHguLQt4Li64LmHLeC5juC5kC3guZngurHgurQt4Lq54Lq74Lq84LuILeC7jeC7kC3gu5ngvJjgvJngvKAt4Lyp4Ly14Ly34Ly54Ly+4Ly/4L2xLeC+hOC+huC+h+C+jS3gvpfgvpkt4L684L+G4YCrLeGAvuGBgC3hgYnhgZYt4YGZ4YGeLeGBoOGBoi3hgaThgact4YGt4YGxLeGBtOGCgi3hgo3hgo8t4YKd4Y2dLeGNn+GNqS3hjbHhnJIt4ZyU4ZyyLeGctOGdkuGdk+GdsuGds+GetC3hn5Phn53hn6At4Z+p4aCLLeGgjeGgkC3hoJnhoqnhpKAt4aSr4aSwLeGku+Glhi3hpY/hprAt4aeA4aeI4aeJ4aeQLeGnmuGoly3hqJvhqZUt4ame4amgLeGpvOGpvy3hqonhqpAt4aqZ4aqwLeGqveGsgC3hrIThrLQt4a2E4a2QLeGtmeGtqy3hrbPhroAt4a6C4a6hLeGureGusC3hrrnhr6Yt4a+z4bCkLeGwt+GxgC3hsYnhsZAt4bGZ4bOQLeGzkuGzlC3hs6jhs63hs7It4bO04bO44bO54beALeG3teG3vC3ht7/igL/igYDigZTig5At4oOc4oOh4oOlLeKDsOKzry3is7Hitb/it6At4re/44CqLeOAr+OCmeOCmuqYoC3qmKnqma/qmbQt6pm96pqf6puw6pux6qCC6qCG6qCL6qCjLeqgp+qigOqigeqitC3qo4Tqo5At6qOZ6qOgLeqjseqkgC3qpInqpKYt6qSt6qWHLeqlk+qmgC3qpoPqprMt6qeA6qeQLeqnmeqnpeqnsC3qp7nqqKkt6qi26qmD6qmM6qmN6qmQLeqpmeqpuy3qqb3qqrDqqrIt6qq06qq36qq46qq+6qq/6quB6qurLeqrr+qrteqrtuqvoy3qr6rqr6zqr63qr7At6q+576ye77iALe+4j++4oC3vuK3vuLPvuLTvuY0t77mP77yQLe+8me+8v1wiO1xuXG52YXIgbm9uQVNDSUlpZGVudGlmaWVyU3RhcnQgPSBuZXcgUmVnRXhwKFwiW1wiICsgbm9uQVNDSUlpZGVudGlmaWVyU3RhcnRDaGFycyArIFwiXVwiKTtcbnZhciBub25BU0NJSWlkZW50aWZpZXIgPSBuZXcgUmVnRXhwKFwiW1wiICsgbm9uQVNDSUlpZGVudGlmaWVyU3RhcnRDaGFycyArIG5vbkFTQ0lJaWRlbnRpZmllckNoYXJzICsgXCJdXCIpO1xuXG5ub25BU0NJSWlkZW50aWZpZXJTdGFydENoYXJzID0gbm9uQVNDSUlpZGVudGlmaWVyQ2hhcnMgPSBudWxsO1xuXG4vLyBUaGVzZSBhcmUgYSBydW4tbGVuZ3RoIGFuZCBvZmZzZXQgZW5jb2RlZCByZXByZXNlbnRhdGlvbiBvZiB0aGVcbi8vID4weGZmZmYgY29kZSBwb2ludHMgdGhhdCBhcmUgYSB2YWxpZCBwYXJ0IG9mIGlkZW50aWZpZXJzLiBUaGVcbi8vIG9mZnNldCBzdGFydHMgYXQgMHgxMDAwMCwgYW5kIGVhY2ggcGFpciBvZiBudW1iZXJzIHJlcHJlc2VudHMgYW5cbi8vIG9mZnNldCB0byB0aGUgbmV4dCByYW5nZSwgYW5kIHRoZW4gYSBzaXplIG9mIHRoZSByYW5nZS4gVGhleSB3ZXJlXG4vLyBnZW5lcmF0ZWQgYnkgdG9vbHMvZ2VuZXJhdGUtaWRlbnRpZmllci1yZWdleC5qc1xudmFyIGFzdHJhbElkZW50aWZpZXJTdGFydENvZGVzID0gWzAsIDExLCAyLCAyNSwgMiwgMTgsIDIsIDEsIDIsIDE0LCAzLCAxMywgMzUsIDEyMiwgNzAsIDUyLCAyNjgsIDI4LCA0LCA0OCwgNDgsIDMxLCAxNywgMjYsIDYsIDM3LCAxMSwgMjksIDMsIDM1LCA1LCA3LCAyLCA0LCA0MywgMTU3LCA5OSwgMzksIDksIDUxLCAxNTcsIDMxMCwgMTAsIDIxLCAxMSwgNywgMTUzLCA1LCAzLCAwLCAyLCA0MywgMiwgMSwgNCwgMCwgMywgMjIsIDExLCAyMiwgMTAsIDMwLCA5OCwgMjEsIDExLCAyNSwgNzEsIDU1LCA3LCAxLCA2NSwgMCwgMTYsIDMsIDIsIDIsIDIsIDI2LCA0NSwgMjgsIDQsIDI4LCAzNiwgNywgMiwgMjcsIDI4LCA1MywgMTEsIDIxLCAxMSwgMTgsIDE0LCAxNywgMTExLCA3MiwgOTU1LCA1MiwgNzYsIDQ0LCAzMywgMjQsIDI3LCAzNSwgNDIsIDM0LCA0LCAwLCAxMywgNDcsIDE1LCAzLCAyMiwgMCwgMzgsIDE3LCAyLCAyNCwgMTMzLCA0NiwgMzksIDcsIDMsIDEsIDMsIDIxLCAyLCA2LCAyLCAxLCAyLCA0LCA0LCAwLCAzMiwgNCwgMjg3LCA0NywgMjEsIDEsIDIsIDAsIDE4NSwgNDYsIDgyLCA0NywgMjEsIDAsIDYwLCA0MiwgNTAyLCA2MywgMzIsIDAsIDQ0OSwgNTYsIDEyODgsIDkyMCwgMTA0LCAxMTAsIDI5NjIsIDEwNzAsIDEzMjY2LCA1NjgsIDgsIDMwLCAxMTQsIDI5LCAxOSwgNDcsIDE3LCAzLCAzMiwgMjAsIDYsIDE4LCA4ODEsIDY4LCAxMiwgMCwgNjcsIDEyLCAxNjQ4MSwgMSwgMzA3MSwgMTA2LCA2LCAxMiwgNCwgOCwgOCwgOSwgNTk5MSwgODQsIDIsIDcwLCAyLCAxLCAzLCAwLCAzLCAxLCAzLCAzLCAyLCAxMSwgMiwgMCwgMiwgNiwgMiwgNjQsIDIsIDMsIDMsIDcsIDIsIDYsIDIsIDI3LCAyLCAzLCAyLCA0LCAyLCAwLCA0LCA2LCAyLCAzMzksIDMsIDI0LCAyLCAyNCwgMiwgMzAsIDIsIDI0LCAyLCAzMCwgMiwgMjQsIDIsIDMwLCAyLCAyNCwgMiwgMzAsIDIsIDI0LCAyLCA3LCA0MTQ5LCAxOTYsIDEzNDAsIDMsIDIsIDI2LCAyLCAxLCAyLCAwLCAzLCAwLCAyLCA5LCAyLCAzLCAyLCAwLCAyLCAwLCA3LCAwLCA1LCAwLCAyLCAwLCAyLCAwLCAyLCAyLCAyLCAxLCAyLCAwLCAzLCAwLCAyLCAwLCAyLCAwLCAyLCAwLCAyLCAwLCAyLCAxLCAyLCAwLCAzLCAzLCAyLCA2LCAyLCAzLCAyLCAzLCAyLCAwLCAyLCA5LCAyLCAxNiwgNiwgMiwgMiwgNCwgMiwgMTYsIDQ0MjEsIDQyNzEwLCA0MiwgNDE0OCwgMTIsIDIyMSwgMTYzNTUsIDU0MV07XG52YXIgYXN0cmFsSWRlbnRpZmllckNvZGVzID0gWzUwOSwgMCwgMjI3LCAwLCAxNTAsIDQsIDI5NCwgOSwgMTM2OCwgMiwgMiwgMSwgNiwgMywgNDEsIDIsIDUsIDAsIDE2NiwgMSwgMTMwNiwgMiwgNTQsIDE0LCAzMiwgOSwgMTYsIDMsIDQ2LCAxMCwgNTQsIDksIDcsIDIsIDM3LCAxMywgMiwgOSwgNTIsIDAsIDEzLCAyLCA0OSwgMTMsIDE2LCA5LCA4MywgMTEsIDE2OCwgMTEsIDYsIDksIDgsIDIsIDU3LCAwLCAyLCA2LCAzLCAxLCAzLCAyLCAxMCwgMCwgMTEsIDEsIDMsIDYsIDQsIDQsIDMxNiwgMTksIDEzLCA5LCAyMTQsIDYsIDMsIDgsIDExMiwgMTYsIDE2LCA5LCA4MiwgMTIsIDksIDksIDUzNSwgOSwgMjA4NTUsIDksIDEzNSwgNCwgNjAsIDYsIDI2LCA5LCAxMDE2LCA0NSwgMTcsIDMsIDE5NzIzLCAxLCA1MzE5LCA0LCA0LCA1LCA5LCA3LCAzLCA2LCAzMSwgMywgMTQ5LCAyLCAxNDE4LCA0OSwgNDMwNSwgNiwgNzkyNjE4LCAyMzldO1xuXG4vLyBUaGlzIGhhcyBhIGNvbXBsZXhpdHkgbGluZWFyIHRvIHRoZSB2YWx1ZSBvZiB0aGUgY29kZS4gVGhlXG4vLyBhc3N1bXB0aW9uIGlzIHRoYXQgbG9va2luZyB1cCBhc3RyYWwgaWRlbnRpZmllciBjaGFyYWN0ZXJzIGlzXG4vLyByYXJlLlxuZnVuY3Rpb24gaXNJbkFzdHJhbFNldChjb2RlLCBzZXQpIHtcbiAgdmFyIHBvcyA9IDB4MTAwMDA7XG4gIGZvciAodmFyIGkgPSAwOyBpIDwgc2V0Lmxlbmd0aDsgaSArPSAyKSB7XG4gICAgcG9zICs9IHNldFtpXTtcbiAgICBpZiAocG9zID4gY29kZSkgcmV0dXJuIGZhbHNlO1xuICAgIHBvcyArPSBzZXRbaSArIDFdO1xuICAgIGlmIChwb3MgPj0gY29kZSkgcmV0dXJuIHRydWU7XG4gIH1cbn1cblxuLy8gVGVzdCB3aGV0aGVyIGEgZ2l2ZW4gY2hhcmFjdGVyIGNvZGUgc3RhcnRzIGFuIGlkZW50aWZpZXIuXG5cbmZ1bmN0aW9uIGlzSWRlbnRpZmllclN0YXJ0KGNvZGUsIGFzdHJhbCkge1xuICBpZiAoY29kZSA8IDY1KSByZXR1cm4gY29kZSA9PT0gMzY7XG4gIGlmIChjb2RlIDwgOTEpIHJldHVybiB0cnVlO1xuICBpZiAoY29kZSA8IDk3KSByZXR1cm4gY29kZSA9PT0gOTU7XG4gIGlmIChjb2RlIDwgMTIzKSByZXR1cm4gdHJ1ZTtcbiAgaWYgKGNvZGUgPD0gMHhmZmZmKSByZXR1cm4gY29kZSA+PSAweGFhICYmIG5vbkFTQ0lJaWRlbnRpZmllclN0YXJ0LnRlc3QoU3RyaW5nLmZyb21DaGFyQ29kZShjb2RlKSk7XG4gIGlmIChhc3RyYWwgPT09IGZhbHNlKSByZXR1cm4gZmFsc2U7XG4gIHJldHVybiBpc0luQXN0cmFsU2V0KGNvZGUsIGFzdHJhbElkZW50aWZpZXJTdGFydENvZGVzKTtcbn1cblxuLy8gVGVzdCB3aGV0aGVyIGEgZ2l2ZW4gY2hhcmFjdGVyIGlzIHBhcnQgb2YgYW4gaWRlbnRpZmllci5cblxuZnVuY3Rpb24gaXNJZGVudGlmaWVyQ2hhcihjb2RlLCBhc3RyYWwpIHtcbiAgaWYgKGNvZGUgPCA0OCkgcmV0dXJuIGNvZGUgPT09IDM2O1xuICBpZiAoY29kZSA8IDU4KSByZXR1cm4gdHJ1ZTtcbiAgaWYgKGNvZGUgPCA2NSkgcmV0dXJuIGZhbHNlO1xuICBpZiAoY29kZSA8IDkxKSByZXR1cm4gdHJ1ZTtcbiAgaWYgKGNvZGUgPCA5NykgcmV0dXJuIGNvZGUgPT09IDk1O1xuICBpZiAoY29kZSA8IDEyMykgcmV0dXJuIHRydWU7XG4gIGlmIChjb2RlIDw9IDB4ZmZmZikgcmV0dXJuIGNvZGUgPj0gMHhhYSAmJiBub25BU0NJSWlkZW50aWZpZXIudGVzdChTdHJpbmcuZnJvbUNoYXJDb2RlKGNvZGUpKTtcbiAgaWYgKGFzdHJhbCA9PT0gZmFsc2UpIHJldHVybiBmYWxzZTtcbiAgcmV0dXJuIGlzSW5Bc3RyYWxTZXQoY29kZSwgYXN0cmFsSWRlbnRpZmllclN0YXJ0Q29kZXMpIHx8IGlzSW5Bc3RyYWxTZXQoY29kZSwgYXN0cmFsSWRlbnRpZmllckNvZGVzKTtcbn1cblxufSx7fV0sMzpbZnVuY3Rpb24oX2RlcmVxXyxtb2R1bGUsZXhwb3J0cyl7XG4vLyBBY29ybiBpcyBhIHRpbnksIGZhc3QgSmF2YVNjcmlwdCBwYXJzZXIgd3JpdHRlbiBpbiBKYXZhU2NyaXB0LlxuLy9cbi8vIEFjb3JuIHdhcyB3cml0dGVuIGJ5IE1hcmlqbiBIYXZlcmJla2UsIEluZ3ZhciBTdGVwYW55YW4sIGFuZFxuLy8gdmFyaW91cyBjb250cmlidXRvcnMgYW5kIHJlbGVhc2VkIHVuZGVyIGFuIE1JVCBsaWNlbnNlLlxuLy9cbi8vIEdpdCByZXBvc2l0b3JpZXMgZm9yIEFjb3JuIGFyZSBhdmFpbGFibGUgYXRcbi8vXG4vLyAgICAgaHR0cDovL21hcmlqbmhhdmVyYmVrZS5ubC9naXQvYWNvcm5cbi8vICAgICBodHRwczovL2dpdGh1Yi5jb20vbWFyaWpuaC9hY29ybi5naXRcbi8vXG4vLyBQbGVhc2UgdXNlIHRoZSBbZ2l0aHViIGJ1ZyB0cmFja2VyXVtnaGJ0XSB0byByZXBvcnQgaXNzdWVzLlxuLy9cbi8vIFtnaGJ0XTogaHR0cHM6Ly9naXRodWIuY29tL21hcmlqbmgvYWNvcm4vaXNzdWVzXG4vL1xuLy8gVGhpcyBmaWxlIGRlZmluZXMgdGhlIG1haW4gcGFyc2VyIGludGVyZmFjZS4gVGhlIGxpYnJhcnkgYWxzbyBjb21lc1xuLy8gd2l0aCBhIFtlcnJvci10b2xlcmFudCBwYXJzZXJdW2RhbW1pdF0gYW5kIGFuXG4vLyBbYWJzdHJhY3Qgc3ludGF4IHRyZWUgd2Fsa2VyXVt3YWxrXSwgZGVmaW5lZCBpbiBvdGhlciBmaWxlcy5cbi8vXG4vLyBbZGFtbWl0XTogYWNvcm5fbG9vc2UuanNcbi8vIFt3YWxrXTogdXRpbC93YWxrLmpzXG5cblwidXNlIHN0cmljdFwiO1xuXG5leHBvcnRzLl9fZXNNb2R1bGUgPSB0cnVlO1xuZXhwb3J0cy5wYXJzZSA9IHBhcnNlO1xuZXhwb3J0cy5wYXJzZUV4cHJlc3Npb25BdCA9IHBhcnNlRXhwcmVzc2lvbkF0O1xuZXhwb3J0cy50b2tlbml6ZXIgPSB0b2tlbml6ZXI7XG5cbnZhciBfc3RhdGUgPSBfZGVyZXFfKFwiLi9zdGF0ZVwiKTtcblxudmFyIF9vcHRpb25zID0gX2RlcmVxXyhcIi4vb3B0aW9uc1wiKTtcblxuX2RlcmVxXyhcIi4vcGFyc2V1dGlsXCIpO1xuXG5fZGVyZXFfKFwiLi9zdGF0ZW1lbnRcIik7XG5cbl9kZXJlcV8oXCIuL2x2YWxcIik7XG5cbl9kZXJlcV8oXCIuL2V4cHJlc3Npb25cIik7XG5cbl9kZXJlcV8oXCIuL2xvY2F0aW9uXCIpO1xuXG5leHBvcnRzLlBhcnNlciA9IF9zdGF0ZS5QYXJzZXI7XG5leHBvcnRzLnBsdWdpbnMgPSBfc3RhdGUucGx1Z2lucztcbmV4cG9ydHMuZGVmYXVsdE9wdGlvbnMgPSBfb3B0aW9ucy5kZWZhdWx0T3B0aW9ucztcblxudmFyIF9sb2N1dGlsID0gX2RlcmVxXyhcIi4vbG9jdXRpbFwiKTtcblxuZXhwb3J0cy5Qb3NpdGlvbiA9IF9sb2N1dGlsLlBvc2l0aW9uO1xuZXhwb3J0cy5Tb3VyY2VMb2NhdGlvbiA9IF9sb2N1dGlsLlNvdXJjZUxvY2F0aW9uO1xuZXhwb3J0cy5nZXRMaW5lSW5mbyA9IF9sb2N1dGlsLmdldExpbmVJbmZvO1xuXG52YXIgX25vZGUgPSBfZGVyZXFfKFwiLi9ub2RlXCIpO1xuXG5leHBvcnRzLk5vZGUgPSBfbm9kZS5Ob2RlO1xuXG52YXIgX3Rva2VudHlwZSA9IF9kZXJlcV8oXCIuL3Rva2VudHlwZVwiKTtcblxuZXhwb3J0cy5Ub2tlblR5cGUgPSBfdG9rZW50eXBlLlRva2VuVHlwZTtcbmV4cG9ydHMudG9rVHlwZXMgPSBfdG9rZW50eXBlLnR5cGVzO1xuXG52YXIgX3Rva2VuY29udGV4dCA9IF9kZXJlcV8oXCIuL3Rva2VuY29udGV4dFwiKTtcblxuZXhwb3J0cy5Ub2tDb250ZXh0ID0gX3Rva2VuY29udGV4dC5Ub2tDb250ZXh0O1xuZXhwb3J0cy50b2tDb250ZXh0cyA9IF90b2tlbmNvbnRleHQudHlwZXM7XG5cbnZhciBfaWRlbnRpZmllciA9IF9kZXJlcV8oXCIuL2lkZW50aWZpZXJcIik7XG5cbmV4cG9ydHMuaXNJZGVudGlmaWVyQ2hhciA9IF9pZGVudGlmaWVyLmlzSWRlbnRpZmllckNoYXI7XG5leHBvcnRzLmlzSWRlbnRpZmllclN0YXJ0ID0gX2lkZW50aWZpZXIuaXNJZGVudGlmaWVyU3RhcnQ7XG5cbnZhciBfdG9rZW5pemUgPSBfZGVyZXFfKFwiLi90b2tlbml6ZVwiKTtcblxuZXhwb3J0cy5Ub2tlbiA9IF90b2tlbml6ZS5Ub2tlbjtcblxudmFyIF93aGl0ZXNwYWNlID0gX2RlcmVxXyhcIi4vd2hpdGVzcGFjZVwiKTtcblxuZXhwb3J0cy5pc05ld0xpbmUgPSBfd2hpdGVzcGFjZS5pc05ld0xpbmU7XG5leHBvcnRzLmxpbmVCcmVhayA9IF93aGl0ZXNwYWNlLmxpbmVCcmVhaztcbmV4cG9ydHMubGluZUJyZWFrRyA9IF93aGl0ZXNwYWNlLmxpbmVCcmVha0c7XG52YXIgdmVyc2lvbiA9IFwiMi4yLjBcIjtcblxuZXhwb3J0cy52ZXJzaW9uID0gdmVyc2lvbjtcbi8vIFRoZSBtYWluIGV4cG9ydGVkIGludGVyZmFjZSAodW5kZXIgYHNlbGYuYWNvcm5gIHdoZW4gaW4gdGhlXG4vLyBicm93c2VyKSBpcyBhIGBwYXJzZWAgZnVuY3Rpb24gdGhhdCB0YWtlcyBhIGNvZGUgc3RyaW5nIGFuZFxuLy8gcmV0dXJucyBhbiBhYnN0cmFjdCBzeW50YXggdHJlZSBhcyBzcGVjaWZpZWQgYnkgW01vemlsbGEgcGFyc2VyXG4vLyBBUEldW2FwaV0uXG4vL1xuLy8gW2FwaV06IGh0dHBzOi8vZGV2ZWxvcGVyLm1vemlsbGEub3JnL2VuLVVTL2RvY3MvU3BpZGVyTW9ua2V5L1BhcnNlcl9BUElcblxuZnVuY3Rpb24gcGFyc2UoaW5wdXQsIG9wdGlvbnMpIHtcbiAgcmV0dXJuIG5ldyBfc3RhdGUuUGFyc2VyKG9wdGlvbnMsIGlucHV0KS5wYXJzZSgpO1xufVxuXG4vLyBUaGlzIGZ1bmN0aW9uIHRyaWVzIHRvIHBhcnNlIGEgc2luZ2xlIGV4cHJlc3Npb24gYXQgYSBnaXZlblxuLy8gb2Zmc2V0IGluIGEgc3RyaW5nLiBVc2VmdWwgZm9yIHBhcnNpbmcgbWl4ZWQtbGFuZ3VhZ2UgZm9ybWF0c1xuLy8gdGhhdCBlbWJlZCBKYXZhU2NyaXB0IGV4cHJlc3Npb25zLlxuXG5mdW5jdGlvbiBwYXJzZUV4cHJlc3Npb25BdChpbnB1dCwgcG9zLCBvcHRpb25zKSB7XG4gIHZhciBwID0gbmV3IF9zdGF0ZS5QYXJzZXIob3B0aW9ucywgaW5wdXQsIHBvcyk7XG4gIHAubmV4dFRva2VuKCk7XG4gIHJldHVybiBwLnBhcnNlRXhwcmVzc2lvbigpO1xufVxuXG4vLyBBY29ybiBpcyBvcmdhbml6ZWQgYXMgYSB0b2tlbml6ZXIgYW5kIGEgcmVjdXJzaXZlLWRlc2NlbnQgcGFyc2VyLlxuLy8gVGhlIGB0b2tlbml6ZWAgZXhwb3J0IHByb3ZpZGVzIGFuIGludGVyZmFjZSB0byB0aGUgdG9rZW5pemVyLlxuXG5mdW5jdGlvbiB0b2tlbml6ZXIoaW5wdXQsIG9wdGlvbnMpIHtcbiAgcmV0dXJuIG5ldyBfc3RhdGUuUGFyc2VyKG9wdGlvbnMsIGlucHV0KTtcbn1cblxufSx7XCIuL2V4cHJlc3Npb25cIjoxLFwiLi9pZGVudGlmaWVyXCI6MixcIi4vbG9jYXRpb25cIjo0LFwiLi9sb2N1dGlsXCI6NSxcIi4vbHZhbFwiOjYsXCIuL25vZGVcIjo3LFwiLi9vcHRpb25zXCI6OCxcIi4vcGFyc2V1dGlsXCI6OSxcIi4vc3RhdGVcIjoxMCxcIi4vc3RhdGVtZW50XCI6MTEsXCIuL3Rva2VuY29udGV4dFwiOjEyLFwiLi90b2tlbml6ZVwiOjEzLFwiLi90b2tlbnR5cGVcIjoxNCxcIi4vd2hpdGVzcGFjZVwiOjE2fV0sNDpbZnVuY3Rpb24oX2RlcmVxXyxtb2R1bGUsZXhwb3J0cyl7XG5cInVzZSBzdHJpY3RcIjtcblxudmFyIF9zdGF0ZSA9IF9kZXJlcV8oXCIuL3N0YXRlXCIpO1xuXG52YXIgX2xvY3V0aWwgPSBfZGVyZXFfKFwiLi9sb2N1dGlsXCIpO1xuXG52YXIgcHAgPSBfc3RhdGUuUGFyc2VyLnByb3RvdHlwZTtcblxuLy8gVGhpcyBmdW5jdGlvbiBpcyB1c2VkIHRvIHJhaXNlIGV4Y2VwdGlvbnMgb24gcGFyc2UgZXJyb3JzLiBJdFxuLy8gdGFrZXMgYW4gb2Zmc2V0IGludGVnZXIgKGludG8gdGhlIGN1cnJlbnQgYGlucHV0YCkgdG8gaW5kaWNhdGVcbi8vIHRoZSBsb2NhdGlvbiBvZiB0aGUgZXJyb3IsIGF0dGFjaGVzIHRoZSBwb3NpdGlvbiB0byB0aGUgZW5kXG4vLyBvZiB0aGUgZXJyb3IgbWVzc2FnZSwgYW5kIHRoZW4gcmFpc2VzIGEgYFN5bnRheEVycm9yYCB3aXRoIHRoYXRcbi8vIG1lc3NhZ2UuXG5cbnBwLnJhaXNlID0gZnVuY3Rpb24gKHBvcywgbWVzc2FnZSkge1xuICB2YXIgbG9jID0gX2xvY3V0aWwuZ2V0TGluZUluZm8odGhpcy5pbnB1dCwgcG9zKTtcbiAgbWVzc2FnZSArPSBcIiAoXCIgKyBsb2MubGluZSArIFwiOlwiICsgbG9jLmNvbHVtbiArIFwiKVwiO1xuICB2YXIgZXJyID0gbmV3IFN5bnRheEVycm9yKG1lc3NhZ2UpO1xuICBlcnIucG9zID0gcG9zO2Vyci5sb2MgPSBsb2M7ZXJyLnJhaXNlZEF0ID0gdGhpcy5wb3M7XG4gIHRocm93IGVycjtcbn07XG5cbnBwLmN1clBvc2l0aW9uID0gZnVuY3Rpb24gKCkge1xuICBpZiAodGhpcy5vcHRpb25zLmxvY2F0aW9ucykge1xuICAgIHJldHVybiBuZXcgX2xvY3V0aWwuUG9zaXRpb24odGhpcy5jdXJMaW5lLCB0aGlzLnBvcyAtIHRoaXMubGluZVN0YXJ0KTtcbiAgfVxufTtcblxufSx7XCIuL2xvY3V0aWxcIjo1LFwiLi9zdGF0ZVwiOjEwfV0sNTpbZnVuY3Rpb24oX2RlcmVxXyxtb2R1bGUsZXhwb3J0cyl7XG5cInVzZSBzdHJpY3RcIjtcblxuZXhwb3J0cy5fX2VzTW9kdWxlID0gdHJ1ZTtcbmV4cG9ydHMuZ2V0TGluZUluZm8gPSBnZXRMaW5lSW5mbztcblxuZnVuY3Rpb24gX2NsYXNzQ2FsbENoZWNrKGluc3RhbmNlLCBDb25zdHJ1Y3RvcikgeyBpZiAoIShpbnN0YW5jZSBpbnN0YW5jZW9mIENvbnN0cnVjdG9yKSkgeyB0aHJvdyBuZXcgVHlwZUVycm9yKFwiQ2Fubm90IGNhbGwgYSBjbGFzcyBhcyBhIGZ1bmN0aW9uXCIpOyB9IH1cblxudmFyIF93aGl0ZXNwYWNlID0gX2RlcmVxXyhcIi4vd2hpdGVzcGFjZVwiKTtcblxuLy8gVGhlc2UgYXJlIHVzZWQgd2hlbiBgb3B0aW9ucy5sb2NhdGlvbnNgIGlzIG9uLCBmb3IgdGhlXG4vLyBgc3RhcnRMb2NgIGFuZCBgZW5kTG9jYCBwcm9wZXJ0aWVzLlxuXG52YXIgUG9zaXRpb24gPSAoZnVuY3Rpb24gKCkge1xuICBmdW5jdGlvbiBQb3NpdGlvbihsaW5lLCBjb2wpIHtcbiAgICBfY2xhc3NDYWxsQ2hlY2sodGhpcywgUG9zaXRpb24pO1xuXG4gICAgdGhpcy5saW5lID0gbGluZTtcbiAgICB0aGlzLmNvbHVtbiA9IGNvbDtcbiAgfVxuXG4gIFBvc2l0aW9uLnByb3RvdHlwZS5vZmZzZXQgPSBmdW5jdGlvbiBvZmZzZXQobikge1xuICAgIHJldHVybiBuZXcgUG9zaXRpb24odGhpcy5saW5lLCB0aGlzLmNvbHVtbiArIG4pO1xuICB9O1xuXG4gIHJldHVybiBQb3NpdGlvbjtcbn0pKCk7XG5cbmV4cG9ydHMuUG9zaXRpb24gPSBQb3NpdGlvbjtcblxudmFyIFNvdXJjZUxvY2F0aW9uID0gZnVuY3Rpb24gU291cmNlTG9jYXRpb24ocCwgc3RhcnQsIGVuZCkge1xuICBfY2xhc3NDYWxsQ2hlY2sodGhpcywgU291cmNlTG9jYXRpb24pO1xuXG4gIHRoaXMuc3RhcnQgPSBzdGFydDtcbiAgdGhpcy5lbmQgPSBlbmQ7XG4gIGlmIChwLnNvdXJjZUZpbGUgIT09IG51bGwpIHRoaXMuc291cmNlID0gcC5zb3VyY2VGaWxlO1xufVxuXG4vLyBUaGUgYGdldExpbmVJbmZvYCBmdW5jdGlvbiBpcyBtb3N0bHkgdXNlZnVsIHdoZW4gdGhlXG4vLyBgbG9jYXRpb25zYCBvcHRpb24gaXMgb2ZmIChmb3IgcGVyZm9ybWFuY2UgcmVhc29ucykgYW5kIHlvdVxuLy8gd2FudCB0byBmaW5kIHRoZSBsaW5lL2NvbHVtbiBwb3NpdGlvbiBmb3IgYSBnaXZlbiBjaGFyYWN0ZXJcbi8vIG9mZnNldC4gYGlucHV0YCBzaG91bGQgYmUgdGhlIGNvZGUgc3RyaW5nIHRoYXQgdGhlIG9mZnNldCByZWZlcnNcbi8vIGludG8uXG5cbjtcblxuZXhwb3J0cy5Tb3VyY2VMb2NhdGlvbiA9IFNvdXJjZUxvY2F0aW9uO1xuXG5mdW5jdGlvbiBnZXRMaW5lSW5mbyhpbnB1dCwgb2Zmc2V0KSB7XG4gIGZvciAodmFyIGxpbmUgPSAxLCBjdXIgPSAwOzspIHtcbiAgICBfd2hpdGVzcGFjZS5saW5lQnJlYWtHLmxhc3RJbmRleCA9IGN1cjtcbiAgICB2YXIgbWF0Y2ggPSBfd2hpdGVzcGFjZS5saW5lQnJlYWtHLmV4ZWMoaW5wdXQpO1xuICAgIGlmIChtYXRjaCAmJiBtYXRjaC5pbmRleCA8IG9mZnNldCkge1xuICAgICAgKytsaW5lO1xuICAgICAgY3VyID0gbWF0Y2guaW5kZXggKyBtYXRjaFswXS5sZW5ndGg7XG4gICAgfSBlbHNlIHtcbiAgICAgIHJldHVybiBuZXcgUG9zaXRpb24obGluZSwgb2Zmc2V0IC0gY3VyKTtcbiAgICB9XG4gIH1cbn1cblxufSx7XCIuL3doaXRlc3BhY2VcIjoxNn1dLDY6W2Z1bmN0aW9uKF9kZXJlcV8sbW9kdWxlLGV4cG9ydHMpe1xuXCJ1c2Ugc3RyaWN0XCI7XG5cbnZhciBfdG9rZW50eXBlID0gX2RlcmVxXyhcIi4vdG9rZW50eXBlXCIpO1xuXG52YXIgX3N0YXRlID0gX2RlcmVxXyhcIi4vc3RhdGVcIik7XG5cbnZhciBfaWRlbnRpZmllciA9IF9kZXJlcV8oXCIuL2lkZW50aWZpZXJcIik7XG5cbnZhciBfdXRpbCA9IF9kZXJlcV8oXCIuL3V0aWxcIik7XG5cbnZhciBwcCA9IF9zdGF0ZS5QYXJzZXIucHJvdG90eXBlO1xuXG4vLyBDb252ZXJ0IGV4aXN0aW5nIGV4cHJlc3Npb24gYXRvbSB0byBhc3NpZ25hYmxlIHBhdHRlcm5cbi8vIGlmIHBvc3NpYmxlLlxuXG5wcC50b0Fzc2lnbmFibGUgPSBmdW5jdGlvbiAobm9kZSwgaXNCaW5kaW5nKSB7XG4gIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNiAmJiBub2RlKSB7XG4gICAgc3dpdGNoIChub2RlLnR5cGUpIHtcbiAgICAgIGNhc2UgXCJJZGVudGlmaWVyXCI6XG4gICAgICBjYXNlIFwiT2JqZWN0UGF0dGVyblwiOlxuICAgICAgY2FzZSBcIkFycmF5UGF0dGVyblwiOlxuICAgICAgY2FzZSBcIkFzc2lnbm1lbnRQYXR0ZXJuXCI6XG4gICAgICAgIGJyZWFrO1xuXG4gICAgICBjYXNlIFwiT2JqZWN0RXhwcmVzc2lvblwiOlxuICAgICAgICBub2RlLnR5cGUgPSBcIk9iamVjdFBhdHRlcm5cIjtcbiAgICAgICAgZm9yICh2YXIgaSA9IDA7IGkgPCBub2RlLnByb3BlcnRpZXMubGVuZ3RoOyBpKyspIHtcbiAgICAgICAgICB2YXIgcHJvcCA9IG5vZGUucHJvcGVydGllc1tpXTtcbiAgICAgICAgICBpZiAocHJvcC5raW5kICE9PSBcImluaXRcIikgdGhpcy5yYWlzZShwcm9wLmtleS5zdGFydCwgXCJPYmplY3QgcGF0dGVybiBjYW4ndCBjb250YWluIGdldHRlciBvciBzZXR0ZXJcIik7XG4gICAgICAgICAgdGhpcy50b0Fzc2lnbmFibGUocHJvcC52YWx1ZSwgaXNCaW5kaW5nKTtcbiAgICAgICAgfVxuICAgICAgICBicmVhaztcblxuICAgICAgY2FzZSBcIkFycmF5RXhwcmVzc2lvblwiOlxuICAgICAgICBub2RlLnR5cGUgPSBcIkFycmF5UGF0dGVyblwiO1xuICAgICAgICB0aGlzLnRvQXNzaWduYWJsZUxpc3Qobm9kZS5lbGVtZW50cywgaXNCaW5kaW5nKTtcbiAgICAgICAgYnJlYWs7XG5cbiAgICAgIGNhc2UgXCJBc3NpZ25tZW50RXhwcmVzc2lvblwiOlxuICAgICAgICBpZiAobm9kZS5vcGVyYXRvciA9PT0gXCI9XCIpIHtcbiAgICAgICAgICBub2RlLnR5cGUgPSBcIkFzc2lnbm1lbnRQYXR0ZXJuXCI7XG4gICAgICAgICAgZGVsZXRlIG5vZGUub3BlcmF0b3I7XG4gICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgdGhpcy5yYWlzZShub2RlLmxlZnQuZW5kLCBcIk9ubHkgJz0nIG9wZXJhdG9yIGNhbiBiZSB1c2VkIGZvciBzcGVjaWZ5aW5nIGRlZmF1bHQgdmFsdWUuXCIpO1xuICAgICAgICB9XG4gICAgICAgIGJyZWFrO1xuXG4gICAgICBjYXNlIFwiUGFyZW50aGVzaXplZEV4cHJlc3Npb25cIjpcbiAgICAgICAgbm9kZS5leHByZXNzaW9uID0gdGhpcy50b0Fzc2lnbmFibGUobm9kZS5leHByZXNzaW9uLCBpc0JpbmRpbmcpO1xuICAgICAgICBicmVhaztcblxuICAgICAgY2FzZSBcIk1lbWJlckV4cHJlc3Npb25cIjpcbiAgICAgICAgaWYgKCFpc0JpbmRpbmcpIGJyZWFrO1xuXG4gICAgICBkZWZhdWx0OlxuICAgICAgICB0aGlzLnJhaXNlKG5vZGUuc3RhcnQsIFwiQXNzaWduaW5nIHRvIHJ2YWx1ZVwiKTtcbiAgICB9XG4gIH1cbiAgcmV0dXJuIG5vZGU7XG59O1xuXG4vLyBDb252ZXJ0IGxpc3Qgb2YgZXhwcmVzc2lvbiBhdG9tcyB0byBiaW5kaW5nIGxpc3QuXG5cbnBwLnRvQXNzaWduYWJsZUxpc3QgPSBmdW5jdGlvbiAoZXhwckxpc3QsIGlzQmluZGluZykge1xuICB2YXIgZW5kID0gZXhwckxpc3QubGVuZ3RoO1xuICBpZiAoZW5kKSB7XG4gICAgdmFyIGxhc3QgPSBleHByTGlzdFtlbmQgLSAxXTtcbiAgICBpZiAobGFzdCAmJiBsYXN0LnR5cGUgPT0gXCJSZXN0RWxlbWVudFwiKSB7XG4gICAgICAtLWVuZDtcbiAgICB9IGVsc2UgaWYgKGxhc3QgJiYgbGFzdC50eXBlID09IFwiU3ByZWFkRWxlbWVudFwiKSB7XG4gICAgICBsYXN0LnR5cGUgPSBcIlJlc3RFbGVtZW50XCI7XG4gICAgICB2YXIgYXJnID0gbGFzdC5hcmd1bWVudDtcbiAgICAgIHRoaXMudG9Bc3NpZ25hYmxlKGFyZywgaXNCaW5kaW5nKTtcbiAgICAgIGlmIChhcmcudHlwZSAhPT0gXCJJZGVudGlmaWVyXCIgJiYgYXJnLnR5cGUgIT09IFwiTWVtYmVyRXhwcmVzc2lvblwiICYmIGFyZy50eXBlICE9PSBcIkFycmF5UGF0dGVyblwiKSB0aGlzLnVuZXhwZWN0ZWQoYXJnLnN0YXJ0KTtcbiAgICAgIC0tZW5kO1xuICAgIH1cbiAgfVxuICBmb3IgKHZhciBpID0gMDsgaSA8IGVuZDsgaSsrKSB7XG4gICAgdmFyIGVsdCA9IGV4cHJMaXN0W2ldO1xuICAgIGlmIChlbHQpIHRoaXMudG9Bc3NpZ25hYmxlKGVsdCwgaXNCaW5kaW5nKTtcbiAgfVxuICByZXR1cm4gZXhwckxpc3Q7XG59O1xuXG4vLyBQYXJzZXMgc3ByZWFkIGVsZW1lbnQuXG5cbnBwLnBhcnNlU3ByZWFkID0gZnVuY3Rpb24gKHJlZlNob3J0aGFuZERlZmF1bHRQb3MpIHtcbiAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICB0aGlzLm5leHQoKTtcbiAgbm9kZS5hcmd1bWVudCA9IHRoaXMucGFyc2VNYXliZUFzc2lnbihyZWZTaG9ydGhhbmREZWZhdWx0UG9zKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIlNwcmVhZEVsZW1lbnRcIik7XG59O1xuXG5wcC5wYXJzZVJlc3QgPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgdGhpcy5uZXh0KCk7XG4gIG5vZGUuYXJndW1lbnQgPSB0aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMubmFtZSB8fCB0aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuYnJhY2tldEwgPyB0aGlzLnBhcnNlQmluZGluZ0F0b20oKSA6IHRoaXMudW5leHBlY3RlZCgpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiUmVzdEVsZW1lbnRcIik7XG59O1xuXG4vLyBQYXJzZXMgbHZhbHVlIChhc3NpZ25hYmxlKSBhdG9tLlxuXG5wcC5wYXJzZUJpbmRpbmdBdG9tID0gZnVuY3Rpb24gKCkge1xuICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uIDwgNikgcmV0dXJuIHRoaXMucGFyc2VJZGVudCgpO1xuICBzd2l0Y2ggKHRoaXMudHlwZSkge1xuICAgIGNhc2UgX3Rva2VudHlwZS50eXBlcy5uYW1lOlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VJZGVudCgpO1xuXG4gICAgY2FzZSBfdG9rZW50eXBlLnR5cGVzLmJyYWNrZXRMOlxuICAgICAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICBub2RlLmVsZW1lbnRzID0gdGhpcy5wYXJzZUJpbmRpbmdMaXN0KF90b2tlbnR5cGUudHlwZXMuYnJhY2tldFIsIHRydWUsIHRydWUpO1xuICAgICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkFycmF5UGF0dGVyblwiKTtcblxuICAgIGNhc2UgX3Rva2VudHlwZS50eXBlcy5icmFjZUw6XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZU9iaih0cnVlKTtcblxuICAgIGRlZmF1bHQ6XG4gICAgICB0aGlzLnVuZXhwZWN0ZWQoKTtcbiAgfVxufTtcblxucHAucGFyc2VCaW5kaW5nTGlzdCA9IGZ1bmN0aW9uIChjbG9zZSwgYWxsb3dFbXB0eSwgYWxsb3dUcmFpbGluZ0NvbW1hKSB7XG4gIHZhciBlbHRzID0gW10sXG4gICAgICBmaXJzdCA9IHRydWU7XG4gIHdoaWxlICghdGhpcy5lYXQoY2xvc2UpKSB7XG4gICAgaWYgKGZpcnN0KSBmaXJzdCA9IGZhbHNlO2Vsc2UgdGhpcy5leHBlY3QoX3Rva2VudHlwZS50eXBlcy5jb21tYSk7XG4gICAgaWYgKGFsbG93RW1wdHkgJiYgdGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLmNvbW1hKSB7XG4gICAgICBlbHRzLnB1c2gobnVsbCk7XG4gICAgfSBlbHNlIGlmIChhbGxvd1RyYWlsaW5nQ29tbWEgJiYgdGhpcy5hZnRlclRyYWlsaW5nQ29tbWEoY2xvc2UpKSB7XG4gICAgICBicmVhaztcbiAgICB9IGVsc2UgaWYgKHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5lbGxpcHNpcykge1xuICAgICAgdmFyIHJlc3QgPSB0aGlzLnBhcnNlUmVzdCgpO1xuICAgICAgdGhpcy5wYXJzZUJpbmRpbmdMaXN0SXRlbShyZXN0KTtcbiAgICAgIGVsdHMucHVzaChyZXN0KTtcbiAgICAgIHRoaXMuZXhwZWN0KGNsb3NlKTtcbiAgICAgIGJyZWFrO1xuICAgIH0gZWxzZSB7XG4gICAgICB2YXIgZWxlbSA9IHRoaXMucGFyc2VNYXliZURlZmF1bHQodGhpcy5zdGFydCwgdGhpcy5zdGFydExvYyk7XG4gICAgICB0aGlzLnBhcnNlQmluZGluZ0xpc3RJdGVtKGVsZW0pO1xuICAgICAgZWx0cy5wdXNoKGVsZW0pO1xuICAgIH1cbiAgfVxuICByZXR1cm4gZWx0cztcbn07XG5cbnBwLnBhcnNlQmluZGluZ0xpc3RJdGVtID0gZnVuY3Rpb24gKHBhcmFtKSB7XG4gIHJldHVybiBwYXJhbTtcbn07XG5cbi8vIFBhcnNlcyBhc3NpZ25tZW50IHBhdHRlcm4gYXJvdW5kIGdpdmVuIGF0b20gaWYgcG9zc2libGUuXG5cbnBwLnBhcnNlTWF5YmVEZWZhdWx0ID0gZnVuY3Rpb24gKHN0YXJ0UG9zLCBzdGFydExvYywgbGVmdCkge1xuICBsZWZ0ID0gbGVmdCB8fCB0aGlzLnBhcnNlQmluZGluZ0F0b20oKTtcbiAgaWYgKCF0aGlzLmVhdChfdG9rZW50eXBlLnR5cGVzLmVxKSkgcmV0dXJuIGxlZnQ7XG4gIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGVBdChzdGFydFBvcywgc3RhcnRMb2MpO1xuICBub2RlLmxlZnQgPSBsZWZ0O1xuICBub2RlLnJpZ2h0ID0gdGhpcy5wYXJzZU1heWJlQXNzaWduKCk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJBc3NpZ25tZW50UGF0dGVyblwiKTtcbn07XG5cbi8vIFZlcmlmeSB0aGF0IGEgbm9kZSBpcyBhbiBsdmFsIOKAlCBzb21ldGhpbmcgdGhhdCBjYW4gYmUgYXNzaWduZWRcbi8vIHRvLlxuXG5wcC5jaGVja0xWYWwgPSBmdW5jdGlvbiAoZXhwciwgaXNCaW5kaW5nLCBjaGVja0NsYXNoZXMpIHtcbiAgc3dpdGNoIChleHByLnR5cGUpIHtcbiAgICBjYXNlIFwiSWRlbnRpZmllclwiOlxuICAgICAgaWYgKHRoaXMuc3RyaWN0ICYmIChfaWRlbnRpZmllci5yZXNlcnZlZFdvcmRzLnN0cmljdEJpbmQoZXhwci5uYW1lKSB8fCBfaWRlbnRpZmllci5yZXNlcnZlZFdvcmRzLnN0cmljdChleHByLm5hbWUpKSkgdGhpcy5yYWlzZShleHByLnN0YXJ0LCAoaXNCaW5kaW5nID8gXCJCaW5kaW5nIFwiIDogXCJBc3NpZ25pbmcgdG8gXCIpICsgZXhwci5uYW1lICsgXCIgaW4gc3RyaWN0IG1vZGVcIik7XG4gICAgICBpZiAoY2hlY2tDbGFzaGVzKSB7XG4gICAgICAgIGlmIChfdXRpbC5oYXMoY2hlY2tDbGFzaGVzLCBleHByLm5hbWUpKSB0aGlzLnJhaXNlKGV4cHIuc3RhcnQsIFwiQXJndW1lbnQgbmFtZSBjbGFzaCBpbiBzdHJpY3QgbW9kZVwiKTtcbiAgICAgICAgY2hlY2tDbGFzaGVzW2V4cHIubmFtZV0gPSB0cnVlO1xuICAgICAgfVxuICAgICAgYnJlYWs7XG5cbiAgICBjYXNlIFwiTWVtYmVyRXhwcmVzc2lvblwiOlxuICAgICAgaWYgKGlzQmluZGluZykgdGhpcy5yYWlzZShleHByLnN0YXJ0LCAoaXNCaW5kaW5nID8gXCJCaW5kaW5nXCIgOiBcIkFzc2lnbmluZyB0b1wiKSArIFwiIG1lbWJlciBleHByZXNzaW9uXCIpO1xuICAgICAgYnJlYWs7XG5cbiAgICBjYXNlIFwiT2JqZWN0UGF0dGVyblwiOlxuICAgICAgZm9yICh2YXIgaSA9IDA7IGkgPCBleHByLnByb3BlcnRpZXMubGVuZ3RoOyBpKyspIHtcbiAgICAgICAgdGhpcy5jaGVja0xWYWwoZXhwci5wcm9wZXJ0aWVzW2ldLnZhbHVlLCBpc0JpbmRpbmcsIGNoZWNrQ2xhc2hlcyk7XG4gICAgICB9YnJlYWs7XG5cbiAgICBjYXNlIFwiQXJyYXlQYXR0ZXJuXCI6XG4gICAgICBmb3IgKHZhciBpID0gMDsgaSA8IGV4cHIuZWxlbWVudHMubGVuZ3RoOyBpKyspIHtcbiAgICAgICAgdmFyIGVsZW0gPSBleHByLmVsZW1lbnRzW2ldO1xuICAgICAgICBpZiAoZWxlbSkgdGhpcy5jaGVja0xWYWwoZWxlbSwgaXNCaW5kaW5nLCBjaGVja0NsYXNoZXMpO1xuICAgICAgfVxuICAgICAgYnJlYWs7XG5cbiAgICBjYXNlIFwiQXNzaWdubWVudFBhdHRlcm5cIjpcbiAgICAgIHRoaXMuY2hlY2tMVmFsKGV4cHIubGVmdCwgaXNCaW5kaW5nLCBjaGVja0NsYXNoZXMpO1xuICAgICAgYnJlYWs7XG5cbiAgICBjYXNlIFwiUmVzdEVsZW1lbnRcIjpcbiAgICAgIHRoaXMuY2hlY2tMVmFsKGV4cHIuYXJndW1lbnQsIGlzQmluZGluZywgY2hlY2tDbGFzaGVzKTtcbiAgICAgIGJyZWFrO1xuXG4gICAgY2FzZSBcIlBhcmVudGhlc2l6ZWRFeHByZXNzaW9uXCI6XG4gICAgICB0aGlzLmNoZWNrTFZhbChleHByLmV4cHJlc3Npb24sIGlzQmluZGluZywgY2hlY2tDbGFzaGVzKTtcbiAgICAgIGJyZWFrO1xuXG4gICAgZGVmYXVsdDpcbiAgICAgIHRoaXMucmFpc2UoZXhwci5zdGFydCwgKGlzQmluZGluZyA/IFwiQmluZGluZ1wiIDogXCJBc3NpZ25pbmcgdG9cIikgKyBcIiBydmFsdWVcIik7XG4gIH1cbn07XG5cbn0se1wiLi9pZGVudGlmaWVyXCI6MixcIi4vc3RhdGVcIjoxMCxcIi4vdG9rZW50eXBlXCI6MTQsXCIuL3V0aWxcIjoxNX1dLDc6W2Z1bmN0aW9uKF9kZXJlcV8sbW9kdWxlLGV4cG9ydHMpe1xuXCJ1c2Ugc3RyaWN0XCI7XG5cbmV4cG9ydHMuX19lc01vZHVsZSA9IHRydWU7XG5cbmZ1bmN0aW9uIF9jbGFzc0NhbGxDaGVjayhpbnN0YW5jZSwgQ29uc3RydWN0b3IpIHsgaWYgKCEoaW5zdGFuY2UgaW5zdGFuY2VvZiBDb25zdHJ1Y3RvcikpIHsgdGhyb3cgbmV3IFR5cGVFcnJvcihcIkNhbm5vdCBjYWxsIGEgY2xhc3MgYXMgYSBmdW5jdGlvblwiKTsgfSB9XG5cbnZhciBfc3RhdGUgPSBfZGVyZXFfKFwiLi9zdGF0ZVwiKTtcblxudmFyIF9sb2N1dGlsID0gX2RlcmVxXyhcIi4vbG9jdXRpbFwiKTtcblxudmFyIE5vZGUgPSBmdW5jdGlvbiBOb2RlKHBhcnNlciwgcG9zLCBsb2MpIHtcbiAgX2NsYXNzQ2FsbENoZWNrKHRoaXMsIE5vZGUpO1xuXG4gIHRoaXMudHlwZSA9IFwiXCI7XG4gIHRoaXMuc3RhcnQgPSBwb3M7XG4gIHRoaXMuZW5kID0gMDtcbiAgaWYgKHBhcnNlci5vcHRpb25zLmxvY2F0aW9ucykgdGhpcy5sb2MgPSBuZXcgX2xvY3V0aWwuU291cmNlTG9jYXRpb24ocGFyc2VyLCBsb2MpO1xuICBpZiAocGFyc2VyLm9wdGlvbnMuZGlyZWN0U291cmNlRmlsZSkgdGhpcy5zb3VyY2VGaWxlID0gcGFyc2VyLm9wdGlvbnMuZGlyZWN0U291cmNlRmlsZTtcbiAgaWYgKHBhcnNlci5vcHRpb25zLnJhbmdlcykgdGhpcy5yYW5nZSA9IFtwb3MsIDBdO1xufVxuXG4vLyBTdGFydCBhbiBBU1Qgbm9kZSwgYXR0YWNoaW5nIGEgc3RhcnQgb2Zmc2V0LlxuXG47XG5cbmV4cG9ydHMuTm9kZSA9IE5vZGU7XG52YXIgcHAgPSBfc3RhdGUuUGFyc2VyLnByb3RvdHlwZTtcblxucHAuc3RhcnROb2RlID0gZnVuY3Rpb24gKCkge1xuICByZXR1cm4gbmV3IE5vZGUodGhpcywgdGhpcy5zdGFydCwgdGhpcy5zdGFydExvYyk7XG59O1xuXG5wcC5zdGFydE5vZGVBdCA9IGZ1bmN0aW9uIChwb3MsIGxvYykge1xuICByZXR1cm4gbmV3IE5vZGUodGhpcywgcG9zLCBsb2MpO1xufTtcblxuLy8gRmluaXNoIGFuIEFTVCBub2RlLCBhZGRpbmcgYHR5cGVgIGFuZCBgZW5kYCBwcm9wZXJ0aWVzLlxuXG5mdW5jdGlvbiBmaW5pc2hOb2RlQXQobm9kZSwgdHlwZSwgcG9zLCBsb2MpIHtcbiAgbm9kZS50eXBlID0gdHlwZTtcbiAgbm9kZS5lbmQgPSBwb3M7XG4gIGlmICh0aGlzLm9wdGlvbnMubG9jYXRpb25zKSBub2RlLmxvYy5lbmQgPSBsb2M7XG4gIGlmICh0aGlzLm9wdGlvbnMucmFuZ2VzKSBub2RlLnJhbmdlWzFdID0gcG9zO1xuICByZXR1cm4gbm9kZTtcbn1cblxucHAuZmluaXNoTm9kZSA9IGZ1bmN0aW9uIChub2RlLCB0eXBlKSB7XG4gIHJldHVybiBmaW5pc2hOb2RlQXQuY2FsbCh0aGlzLCBub2RlLCB0eXBlLCB0aGlzLmxhc3RUb2tFbmQsIHRoaXMubGFzdFRva0VuZExvYyk7XG59O1xuXG4vLyBGaW5pc2ggbm9kZSBhdCBnaXZlbiBwb3NpdGlvblxuXG5wcC5maW5pc2hOb2RlQXQgPSBmdW5jdGlvbiAobm9kZSwgdHlwZSwgcG9zLCBsb2MpIHtcbiAgcmV0dXJuIGZpbmlzaE5vZGVBdC5jYWxsKHRoaXMsIG5vZGUsIHR5cGUsIHBvcywgbG9jKTtcbn07XG5cbn0se1wiLi9sb2N1dGlsXCI6NSxcIi4vc3RhdGVcIjoxMH1dLDg6W2Z1bmN0aW9uKF9kZXJlcV8sbW9kdWxlLGV4cG9ydHMpe1xuXCJ1c2Ugc3RyaWN0XCI7XG5cbmV4cG9ydHMuX19lc01vZHVsZSA9IHRydWU7XG5leHBvcnRzLmdldE9wdGlvbnMgPSBnZXRPcHRpb25zO1xuXG52YXIgX3V0aWwgPSBfZGVyZXFfKFwiLi91dGlsXCIpO1xuXG52YXIgX2xvY3V0aWwgPSBfZGVyZXFfKFwiLi9sb2N1dGlsXCIpO1xuXG4vLyBBIHNlY29uZCBvcHRpb25hbCBhcmd1bWVudCBjYW4gYmUgZ2l2ZW4gdG8gZnVydGhlciBjb25maWd1cmVcbi8vIHRoZSBwYXJzZXIgcHJvY2Vzcy4gVGhlc2Ugb3B0aW9ucyBhcmUgcmVjb2duaXplZDpcblxudmFyIGRlZmF1bHRPcHRpb25zID0ge1xuICAvLyBgZWNtYVZlcnNpb25gIGluZGljYXRlcyB0aGUgRUNNQVNjcmlwdCB2ZXJzaW9uIHRvIHBhcnNlLiBNdXN0XG4gIC8vIGJlIGVpdGhlciAzLCBvciA1LCBvciA2LiBUaGlzIGluZmx1ZW5jZXMgc3VwcG9ydCBmb3Igc3RyaWN0XG4gIC8vIG1vZGUsIHRoZSBzZXQgb2YgcmVzZXJ2ZWQgd29yZHMsIHN1cHBvcnQgZm9yIGdldHRlcnMgYW5kXG4gIC8vIHNldHRlcnMgYW5kIG90aGVyIGZlYXR1cmVzLlxuICBlY21hVmVyc2lvbjogNSxcbiAgLy8gU291cmNlIHR5cGUgKFwic2NyaXB0XCIgb3IgXCJtb2R1bGVcIikgZm9yIGRpZmZlcmVudCBzZW1hbnRpY3NcbiAgc291cmNlVHlwZTogXCJzY3JpcHRcIixcbiAgLy8gYG9uSW5zZXJ0ZWRTZW1pY29sb25gIGNhbiBiZSBhIGNhbGxiYWNrIHRoYXQgd2lsbCBiZSBjYWxsZWRcbiAgLy8gd2hlbiBhIHNlbWljb2xvbiBpcyBhdXRvbWF0aWNhbGx5IGluc2VydGVkLiBJdCB3aWxsIGJlIHBhc3NlZFxuICAvLyB0aCBwb3NpdGlvbiBvZiB0aGUgY29tbWEgYXMgYW4gb2Zmc2V0LCBhbmQgaWYgYGxvY2F0aW9uc2AgaXNcbiAgLy8gZW5hYmxlZCwgaXQgaXMgZ2l2ZW4gdGhlIGxvY2F0aW9uIGFzIGEgYHtsaW5lLCBjb2x1bW59YCBvYmplY3RcbiAgLy8gYXMgc2Vjb25kIGFyZ3VtZW50LlxuICBvbkluc2VydGVkU2VtaWNvbG9uOiBudWxsLFxuICAvLyBgb25UcmFpbGluZ0NvbW1hYCBpcyBzaW1pbGFyIHRvIGBvbkluc2VydGVkU2VtaWNvbG9uYCwgYnV0IGZvclxuICAvLyB0cmFpbGluZyBjb21tYXMuXG4gIG9uVHJhaWxpbmdDb21tYTogbnVsbCxcbiAgLy8gQnkgZGVmYXVsdCwgcmVzZXJ2ZWQgd29yZHMgYXJlIG5vdCBlbmZvcmNlZC4gRGlzYWJsZVxuICAvLyBgYWxsb3dSZXNlcnZlZGAgdG8gZW5mb3JjZSB0aGVtLiBXaGVuIHRoaXMgb3B0aW9uIGhhcyB0aGVcbiAgLy8gdmFsdWUgXCJuZXZlclwiLCByZXNlcnZlZCB3b3JkcyBhbmQga2V5d29yZHMgY2FuIGFsc28gbm90IGJlXG4gIC8vIHVzZWQgYXMgcHJvcGVydHkgbmFtZXMuXG4gIGFsbG93UmVzZXJ2ZWQ6IHRydWUsXG4gIC8vIFdoZW4gZW5hYmxlZCwgYSByZXR1cm4gYXQgdGhlIHRvcCBsZXZlbCBpcyBub3QgY29uc2lkZXJlZCBhblxuICAvLyBlcnJvci5cbiAgYWxsb3dSZXR1cm5PdXRzaWRlRnVuY3Rpb246IGZhbHNlLFxuICAvLyBXaGVuIGVuYWJsZWQsIGltcG9ydC9leHBvcnQgc3RhdGVtZW50cyBhcmUgbm90IGNvbnN0cmFpbmVkIHRvXG4gIC8vIGFwcGVhcmluZyBhdCB0aGUgdG9wIG9mIHRoZSBwcm9ncmFtLlxuICBhbGxvd0ltcG9ydEV4cG9ydEV2ZXJ5d2hlcmU6IGZhbHNlLFxuICAvLyBXaGVuIGVuYWJsZWQsIGhhc2hiYW5nIGRpcmVjdGl2ZSBpbiB0aGUgYmVnaW5uaW5nIG9mIGZpbGVcbiAgLy8gaXMgYWxsb3dlZCBhbmQgdHJlYXRlZCBhcyBhIGxpbmUgY29tbWVudC5cbiAgYWxsb3dIYXNoQmFuZzogZmFsc2UsXG4gIC8vIFdoZW4gYGxvY2F0aW9uc2AgaXMgb24sIGBsb2NgIHByb3BlcnRpZXMgaG9sZGluZyBvYmplY3RzIHdpdGhcbiAgLy8gYHN0YXJ0YCBhbmQgYGVuZGAgcHJvcGVydGllcyBpbiBge2xpbmUsIGNvbHVtbn1gIGZvcm0gKHdpdGhcbiAgLy8gbGluZSBiZWluZyAxLWJhc2VkIGFuZCBjb2x1bW4gMC1iYXNlZCkgd2lsbCBiZSBhdHRhY2hlZCB0byB0aGVcbiAgLy8gbm9kZXMuXG4gIGxvY2F0aW9uczogZmFsc2UsXG4gIC8vIEEgZnVuY3Rpb24gY2FuIGJlIHBhc3NlZCBhcyBgb25Ub2tlbmAgb3B0aW9uLCB3aGljaCB3aWxsXG4gIC8vIGNhdXNlIEFjb3JuIHRvIGNhbGwgdGhhdCBmdW5jdGlvbiB3aXRoIG9iamVjdCBpbiB0aGUgc2FtZVxuICAvLyBmb3JtYXQgYXMgdG9rZW5pemUoKSByZXR1cm5zLiBOb3RlIHRoYXQgeW91IGFyZSBub3RcbiAgLy8gYWxsb3dlZCB0byBjYWxsIHRoZSBwYXJzZXIgZnJvbSB0aGUgY2FsbGJhY2vigJR0aGF0IHdpbGxcbiAgLy8gY29ycnVwdCBpdHMgaW50ZXJuYWwgc3RhdGUuXG4gIG9uVG9rZW46IG51bGwsXG4gIC8vIEEgZnVuY3Rpb24gY2FuIGJlIHBhc3NlZCBhcyBgb25Db21tZW50YCBvcHRpb24sIHdoaWNoIHdpbGxcbiAgLy8gY2F1c2UgQWNvcm4gdG8gY2FsbCB0aGF0IGZ1bmN0aW9uIHdpdGggYChibG9jaywgdGV4dCwgc3RhcnQsXG4gIC8vIGVuZClgIHBhcmFtZXRlcnMgd2hlbmV2ZXIgYSBjb21tZW50IGlzIHNraXBwZWQuIGBibG9ja2AgaXMgYVxuICAvLyBib29sZWFuIGluZGljYXRpbmcgd2hldGhlciB0aGlzIGlzIGEgYmxvY2sgKGAvKiAqL2ApIGNvbW1lbnQsXG4gIC8vIGB0ZXh0YCBpcyB0aGUgY29udGVudCBvZiB0aGUgY29tbWVudCwgYW5kIGBzdGFydGAgYW5kIGBlbmRgIGFyZVxuICAvLyBjaGFyYWN0ZXIgb2Zmc2V0cyB0aGF0IGRlbm90ZSB0aGUgc3RhcnQgYW5kIGVuZCBvZiB0aGUgY29tbWVudC5cbiAgLy8gV2hlbiB0aGUgYGxvY2F0aW9uc2Agb3B0aW9uIGlzIG9uLCB0d28gbW9yZSBwYXJhbWV0ZXJzIGFyZVxuICAvLyBwYXNzZWQsIHRoZSBmdWxsIGB7bGluZSwgY29sdW1ufWAgbG9jYXRpb25zIG9mIHRoZSBzdGFydCBhbmRcbiAgLy8gZW5kIG9mIHRoZSBjb21tZW50cy4gTm90ZSB0aGF0IHlvdSBhcmUgbm90IGFsbG93ZWQgdG8gY2FsbCB0aGVcbiAgLy8gcGFyc2VyIGZyb20gdGhlIGNhbGxiYWNr4oCUdGhhdCB3aWxsIGNvcnJ1cHQgaXRzIGludGVybmFsIHN0YXRlLlxuICBvbkNvbW1lbnQ6IG51bGwsXG4gIC8vIE5vZGVzIGhhdmUgdGhlaXIgc3RhcnQgYW5kIGVuZCBjaGFyYWN0ZXJzIG9mZnNldHMgcmVjb3JkZWQgaW5cbiAgLy8gYHN0YXJ0YCBhbmQgYGVuZGAgcHJvcGVydGllcyAoZGlyZWN0bHkgb24gdGhlIG5vZGUsIHJhdGhlciB0aGFuXG4gIC8vIHRoZSBgbG9jYCBvYmplY3QsIHdoaWNoIGhvbGRzIGxpbmUvY29sdW1uIGRhdGEuIFRvIGFsc28gYWRkIGFcbiAgLy8gW3NlbWktc3RhbmRhcmRpemVkXVtyYW5nZV0gYHJhbmdlYCBwcm9wZXJ0eSBob2xkaW5nIGEgYFtzdGFydCxcbiAgLy8gZW5kXWAgYXJyYXkgd2l0aCB0aGUgc2FtZSBudW1iZXJzLCBzZXQgdGhlIGByYW5nZXNgIG9wdGlvbiB0b1xuICAvLyBgdHJ1ZWAuXG4gIC8vXG4gIC8vIFtyYW5nZV06IGh0dHBzOi8vYnVnemlsbGEubW96aWxsYS5vcmcvc2hvd19idWcuY2dpP2lkPTc0NTY3OFxuICByYW5nZXM6IGZhbHNlLFxuICAvLyBJdCBpcyBwb3NzaWJsZSB0byBwYXJzZSBtdWx0aXBsZSBmaWxlcyBpbnRvIGEgc2luZ2xlIEFTVCBieVxuICAvLyBwYXNzaW5nIHRoZSB0cmVlIHByb2R1Y2VkIGJ5IHBhcnNpbmcgdGhlIGZpcnN0IGZpbGUgYXNcbiAgLy8gYHByb2dyYW1gIG9wdGlvbiBpbiBzdWJzZXF1ZW50IHBhcnNlcy4gVGhpcyB3aWxsIGFkZCB0aGVcbiAgLy8gdG9wbGV2ZWwgZm9ybXMgb2YgdGhlIHBhcnNlZCBmaWxlIHRvIHRoZSBgUHJvZ3JhbWAgKHRvcCkgbm9kZVxuICAvLyBvZiBhbiBleGlzdGluZyBwYXJzZSB0cmVlLlxuICBwcm9ncmFtOiBudWxsLFxuICAvLyBXaGVuIGBsb2NhdGlvbnNgIGlzIG9uLCB5b3UgY2FuIHBhc3MgdGhpcyB0byByZWNvcmQgdGhlIHNvdXJjZVxuICAvLyBmaWxlIGluIGV2ZXJ5IG5vZGUncyBgbG9jYCBvYmplY3QuXG4gIHNvdXJjZUZpbGU6IG51bGwsXG4gIC8vIFRoaXMgdmFsdWUsIGlmIGdpdmVuLCBpcyBzdG9yZWQgaW4gZXZlcnkgbm9kZSwgd2hldGhlclxuICAvLyBgbG9jYXRpb25zYCBpcyBvbiBvciBvZmYuXG4gIGRpcmVjdFNvdXJjZUZpbGU6IG51bGwsXG4gIC8vIFdoZW4gZW5hYmxlZCwgcGFyZW50aGVzaXplZCBleHByZXNzaW9ucyBhcmUgcmVwcmVzZW50ZWQgYnlcbiAgLy8gKG5vbi1zdGFuZGFyZCkgUGFyZW50aGVzaXplZEV4cHJlc3Npb24gbm9kZXNcbiAgcHJlc2VydmVQYXJlbnM6IGZhbHNlLFxuICBwbHVnaW5zOiB7fVxufTtcblxuZXhwb3J0cy5kZWZhdWx0T3B0aW9ucyA9IGRlZmF1bHRPcHRpb25zO1xuLy8gSW50ZXJwcmV0IGFuZCBkZWZhdWx0IGFuIG9wdGlvbnMgb2JqZWN0XG5cbmZ1bmN0aW9uIGdldE9wdGlvbnMob3B0cykge1xuICB2YXIgb3B0aW9ucyA9IHt9O1xuICBmb3IgKHZhciBvcHQgaW4gZGVmYXVsdE9wdGlvbnMpIHtcbiAgICBvcHRpb25zW29wdF0gPSBvcHRzICYmIF91dGlsLmhhcyhvcHRzLCBvcHQpID8gb3B0c1tvcHRdIDogZGVmYXVsdE9wdGlvbnNbb3B0XTtcbiAgfWlmIChfdXRpbC5pc0FycmF5KG9wdGlvbnMub25Ub2tlbikpIHtcbiAgICAoZnVuY3Rpb24gKCkge1xuICAgICAgdmFyIHRva2VucyA9IG9wdGlvbnMub25Ub2tlbjtcbiAgICAgIG9wdGlvbnMub25Ub2tlbiA9IGZ1bmN0aW9uICh0b2tlbikge1xuICAgICAgICByZXR1cm4gdG9rZW5zLnB1c2godG9rZW4pO1xuICAgICAgfTtcbiAgICB9KSgpO1xuICB9XG4gIGlmIChfdXRpbC5pc0FycmF5KG9wdGlvbnMub25Db21tZW50KSkgb3B0aW9ucy5vbkNvbW1lbnQgPSBwdXNoQ29tbWVudChvcHRpb25zLCBvcHRpb25zLm9uQ29tbWVudCk7XG5cbiAgcmV0dXJuIG9wdGlvbnM7XG59XG5cbmZ1bmN0aW9uIHB1c2hDb21tZW50KG9wdGlvbnMsIGFycmF5KSB7XG4gIHJldHVybiBmdW5jdGlvbiAoYmxvY2ssIHRleHQsIHN0YXJ0LCBlbmQsIHN0YXJ0TG9jLCBlbmRMb2MpIHtcbiAgICB2YXIgY29tbWVudCA9IHtcbiAgICAgIHR5cGU6IGJsb2NrID8gJ0Jsb2NrJyA6ICdMaW5lJyxcbiAgICAgIHZhbHVlOiB0ZXh0LFxuICAgICAgc3RhcnQ6IHN0YXJ0LFxuICAgICAgZW5kOiBlbmRcbiAgICB9O1xuICAgIGlmIChvcHRpb25zLmxvY2F0aW9ucykgY29tbWVudC5sb2MgPSBuZXcgX2xvY3V0aWwuU291cmNlTG9jYXRpb24odGhpcywgc3RhcnRMb2MsIGVuZExvYyk7XG4gICAgaWYgKG9wdGlvbnMucmFuZ2VzKSBjb21tZW50LnJhbmdlID0gW3N0YXJ0LCBlbmRdO1xuICAgIGFycmF5LnB1c2goY29tbWVudCk7XG4gIH07XG59XG5cbn0se1wiLi9sb2N1dGlsXCI6NSxcIi4vdXRpbFwiOjE1fV0sOTpbZnVuY3Rpb24oX2RlcmVxXyxtb2R1bGUsZXhwb3J0cyl7XG5cInVzZSBzdHJpY3RcIjtcblxudmFyIF90b2tlbnR5cGUgPSBfZGVyZXFfKFwiLi90b2tlbnR5cGVcIik7XG5cbnZhciBfc3RhdGUgPSBfZGVyZXFfKFwiLi9zdGF0ZVwiKTtcblxudmFyIF93aGl0ZXNwYWNlID0gX2RlcmVxXyhcIi4vd2hpdGVzcGFjZVwiKTtcblxudmFyIHBwID0gX3N0YXRlLlBhcnNlci5wcm90b3R5cGU7XG5cbi8vICMjIFBhcnNlciB1dGlsaXRpZXNcblxuLy8gVGVzdCB3aGV0aGVyIGEgc3RhdGVtZW50IG5vZGUgaXMgdGhlIHN0cmluZyBsaXRlcmFsIGBcInVzZSBzdHJpY3RcImAuXG5cbnBwLmlzVXNlU3RyaWN0ID0gZnVuY3Rpb24gKHN0bXQpIHtcbiAgcmV0dXJuIHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA1ICYmIHN0bXQudHlwZSA9PT0gXCJFeHByZXNzaW9uU3RhdGVtZW50XCIgJiYgc3RtdC5leHByZXNzaW9uLnR5cGUgPT09IFwiTGl0ZXJhbFwiICYmIHN0bXQuZXhwcmVzc2lvbi5yYXcuc2xpY2UoMSwgLTEpID09PSBcInVzZSBzdHJpY3RcIjtcbn07XG5cbi8vIFByZWRpY2F0ZSB0aGF0IHRlc3RzIHdoZXRoZXIgdGhlIG5leHQgdG9rZW4gaXMgb2YgdGhlIGdpdmVuXG4vLyB0eXBlLCBhbmQgaWYgeWVzLCBjb25zdW1lcyBpdCBhcyBhIHNpZGUgZWZmZWN0LlxuXG5wcC5lYXQgPSBmdW5jdGlvbiAodHlwZSkge1xuICBpZiAodGhpcy50eXBlID09PSB0eXBlKSB7XG4gICAgdGhpcy5uZXh0KCk7XG4gICAgcmV0dXJuIHRydWU7XG4gIH0gZWxzZSB7XG4gICAgcmV0dXJuIGZhbHNlO1xuICB9XG59O1xuXG4vLyBUZXN0cyB3aGV0aGVyIHBhcnNlZCB0b2tlbiBpcyBhIGNvbnRleHR1YWwga2V5d29yZC5cblxucHAuaXNDb250ZXh0dWFsID0gZnVuY3Rpb24gKG5hbWUpIHtcbiAgcmV0dXJuIHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5uYW1lICYmIHRoaXMudmFsdWUgPT09IG5hbWU7XG59O1xuXG4vLyBDb25zdW1lcyBjb250ZXh0dWFsIGtleXdvcmQgaWYgcG9zc2libGUuXG5cbnBwLmVhdENvbnRleHR1YWwgPSBmdW5jdGlvbiAobmFtZSkge1xuICByZXR1cm4gdGhpcy52YWx1ZSA9PT0gbmFtZSAmJiB0aGlzLmVhdChfdG9rZW50eXBlLnR5cGVzLm5hbWUpO1xufTtcblxuLy8gQXNzZXJ0cyB0aGF0IGZvbGxvd2luZyB0b2tlbiBpcyBnaXZlbiBjb250ZXh0dWFsIGtleXdvcmQuXG5cbnBwLmV4cGVjdENvbnRleHR1YWwgPSBmdW5jdGlvbiAobmFtZSkge1xuICBpZiAoIXRoaXMuZWF0Q29udGV4dHVhbChuYW1lKSkgdGhpcy51bmV4cGVjdGVkKCk7XG59O1xuXG4vLyBUZXN0IHdoZXRoZXIgYSBzZW1pY29sb24gY2FuIGJlIGluc2VydGVkIGF0IHRoZSBjdXJyZW50IHBvc2l0aW9uLlxuXG5wcC5jYW5JbnNlcnRTZW1pY29sb24gPSBmdW5jdGlvbiAoKSB7XG4gIHJldHVybiB0aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuZW9mIHx8IHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5icmFjZVIgfHwgX3doaXRlc3BhY2UubGluZUJyZWFrLnRlc3QodGhpcy5pbnB1dC5zbGljZSh0aGlzLmxhc3RUb2tFbmQsIHRoaXMuc3RhcnQpKTtcbn07XG5cbnBwLmluc2VydFNlbWljb2xvbiA9IGZ1bmN0aW9uICgpIHtcbiAgaWYgKHRoaXMuY2FuSW5zZXJ0U2VtaWNvbG9uKCkpIHtcbiAgICBpZiAodGhpcy5vcHRpb25zLm9uSW5zZXJ0ZWRTZW1pY29sb24pIHRoaXMub3B0aW9ucy5vbkluc2VydGVkU2VtaWNvbG9uKHRoaXMubGFzdFRva0VuZCwgdGhpcy5sYXN0VG9rRW5kTG9jKTtcbiAgICByZXR1cm4gdHJ1ZTtcbiAgfVxufTtcblxuLy8gQ29uc3VtZSBhIHNlbWljb2xvbiwgb3IsIGZhaWxpbmcgdGhhdCwgc2VlIGlmIHdlIGFyZSBhbGxvd2VkIHRvXG4vLyBwcmV0ZW5kIHRoYXQgdGhlcmUgaXMgYSBzZW1pY29sb24gYXQgdGhpcyBwb3NpdGlvbi5cblxucHAuc2VtaWNvbG9uID0gZnVuY3Rpb24gKCkge1xuICBpZiAoIXRoaXMuZWF0KF90b2tlbnR5cGUudHlwZXMuc2VtaSkgJiYgIXRoaXMuaW5zZXJ0U2VtaWNvbG9uKCkpIHRoaXMudW5leHBlY3RlZCgpO1xufTtcblxucHAuYWZ0ZXJUcmFpbGluZ0NvbW1hID0gZnVuY3Rpb24gKHRva1R5cGUpIHtcbiAgaWYgKHRoaXMudHlwZSA9PSB0b2tUeXBlKSB7XG4gICAgaWYgKHRoaXMub3B0aW9ucy5vblRyYWlsaW5nQ29tbWEpIHRoaXMub3B0aW9ucy5vblRyYWlsaW5nQ29tbWEodGhpcy5sYXN0VG9rU3RhcnQsIHRoaXMubGFzdFRva1N0YXJ0TG9jKTtcbiAgICB0aGlzLm5leHQoKTtcbiAgICByZXR1cm4gdHJ1ZTtcbiAgfVxufTtcblxuLy8gRXhwZWN0IGEgdG9rZW4gb2YgYSBnaXZlbiB0eXBlLiBJZiBmb3VuZCwgY29uc3VtZSBpdCwgb3RoZXJ3aXNlLFxuLy8gcmFpc2UgYW4gdW5leHBlY3RlZCB0b2tlbiBlcnJvci5cblxucHAuZXhwZWN0ID0gZnVuY3Rpb24gKHR5cGUpIHtcbiAgdGhpcy5lYXQodHlwZSkgfHwgdGhpcy51bmV4cGVjdGVkKCk7XG59O1xuXG4vLyBSYWlzZSBhbiB1bmV4cGVjdGVkIHRva2VuIGVycm9yLlxuXG5wcC51bmV4cGVjdGVkID0gZnVuY3Rpb24gKHBvcykge1xuICB0aGlzLnJhaXNlKHBvcyAhPSBudWxsID8gcG9zIDogdGhpcy5zdGFydCwgXCJVbmV4cGVjdGVkIHRva2VuXCIpO1xufTtcblxufSx7XCIuL3N0YXRlXCI6MTAsXCIuL3Rva2VudHlwZVwiOjE0LFwiLi93aGl0ZXNwYWNlXCI6MTZ9XSwxMDpbZnVuY3Rpb24oX2RlcmVxXyxtb2R1bGUsZXhwb3J0cyl7XG5cInVzZSBzdHJpY3RcIjtcblxuZXhwb3J0cy5fX2VzTW9kdWxlID0gdHJ1ZTtcblxuZnVuY3Rpb24gX2NsYXNzQ2FsbENoZWNrKGluc3RhbmNlLCBDb25zdHJ1Y3RvcikgeyBpZiAoIShpbnN0YW5jZSBpbnN0YW5jZW9mIENvbnN0cnVjdG9yKSkgeyB0aHJvdyBuZXcgVHlwZUVycm9yKFwiQ2Fubm90IGNhbGwgYSBjbGFzcyBhcyBhIGZ1bmN0aW9uXCIpOyB9IH1cblxudmFyIF9pZGVudGlmaWVyID0gX2RlcmVxXyhcIi4vaWRlbnRpZmllclwiKTtcblxudmFyIF90b2tlbnR5cGUgPSBfZGVyZXFfKFwiLi90b2tlbnR5cGVcIik7XG5cbnZhciBfd2hpdGVzcGFjZSA9IF9kZXJlcV8oXCIuL3doaXRlc3BhY2VcIik7XG5cbnZhciBfb3B0aW9ucyA9IF9kZXJlcV8oXCIuL29wdGlvbnNcIik7XG5cbi8vIFJlZ2lzdGVyZWQgcGx1Z2luc1xudmFyIHBsdWdpbnMgPSB7fTtcblxuZXhwb3J0cy5wbHVnaW5zID0gcGx1Z2lucztcblxudmFyIFBhcnNlciA9IChmdW5jdGlvbiAoKSB7XG4gIGZ1bmN0aW9uIFBhcnNlcihvcHRpb25zLCBpbnB1dCwgc3RhcnRQb3MpIHtcbiAgICBfY2xhc3NDYWxsQ2hlY2sodGhpcywgUGFyc2VyKTtcblxuICAgIHRoaXMub3B0aW9ucyA9IF9vcHRpb25zLmdldE9wdGlvbnMob3B0aW9ucyk7XG4gICAgdGhpcy5zb3VyY2VGaWxlID0gdGhpcy5vcHRpb25zLnNvdXJjZUZpbGU7XG4gICAgdGhpcy5pc0tleXdvcmQgPSBfaWRlbnRpZmllci5rZXl3b3Jkc1t0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNiA/IDYgOiA1XTtcbiAgICB0aGlzLmlzUmVzZXJ2ZWRXb3JkID0gX2lkZW50aWZpZXIucmVzZXJ2ZWRXb3Jkc1t0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb25dO1xuICAgIHRoaXMuaW5wdXQgPSBTdHJpbmcoaW5wdXQpO1xuXG4gICAgLy8gVXNlZCB0byBzaWduYWwgdG8gY2FsbGVycyBvZiBgcmVhZFdvcmQxYCB3aGV0aGVyIHRoZSB3b3JkXG4gICAgLy8gY29udGFpbmVkIGFueSBlc2NhcGUgc2VxdWVuY2VzLiBUaGlzIGlzIG5lZWRlZCBiZWNhdXNlIHdvcmRzIHdpdGhcbiAgICAvLyBlc2NhcGUgc2VxdWVuY2VzIG11c3Qgbm90IGJlIGludGVycHJldGVkIGFzIGtleXdvcmRzLlxuICAgIHRoaXMuY29udGFpbnNFc2MgPSBmYWxzZTtcblxuICAgIC8vIExvYWQgcGx1Z2luc1xuICAgIHRoaXMubG9hZFBsdWdpbnModGhpcy5vcHRpb25zLnBsdWdpbnMpO1xuXG4gICAgLy8gU2V0IHVwIHRva2VuIHN0YXRlXG5cbiAgICAvLyBUaGUgY3VycmVudCBwb3NpdGlvbiBvZiB0aGUgdG9rZW5pemVyIGluIHRoZSBpbnB1dC5cbiAgICBpZiAoc3RhcnRQb3MpIHtcbiAgICAgIHRoaXMucG9zID0gc3RhcnRQb3M7XG4gICAgICB0aGlzLmxpbmVTdGFydCA9IE1hdGgubWF4KDAsIHRoaXMuaW5wdXQubGFzdEluZGV4T2YoXCJcXG5cIiwgc3RhcnRQb3MpKTtcbiAgICAgIHRoaXMuY3VyTGluZSA9IHRoaXMuaW5wdXQuc2xpY2UoMCwgdGhpcy5saW5lU3RhcnQpLnNwbGl0KF93aGl0ZXNwYWNlLmxpbmVCcmVhaykubGVuZ3RoO1xuICAgIH0gZWxzZSB7XG4gICAgICB0aGlzLnBvcyA9IHRoaXMubGluZVN0YXJ0ID0gMDtcbiAgICAgIHRoaXMuY3VyTGluZSA9IDE7XG4gICAgfVxuXG4gICAgLy8gUHJvcGVydGllcyBvZiB0aGUgY3VycmVudCB0b2tlbjpcbiAgICAvLyBJdHMgdHlwZVxuICAgIHRoaXMudHlwZSA9IF90b2tlbnR5cGUudHlwZXMuZW9mO1xuICAgIC8vIEZvciB0b2tlbnMgdGhhdCBpbmNsdWRlIG1vcmUgaW5mb3JtYXRpb24gdGhhbiB0aGVpciB0eXBlLCB0aGUgdmFsdWVcbiAgICB0aGlzLnZhbHVlID0gbnVsbDtcbiAgICAvLyBJdHMgc3RhcnQgYW5kIGVuZCBvZmZzZXRcbiAgICB0aGlzLnN0YXJ0ID0gdGhpcy5lbmQgPSB0aGlzLnBvcztcbiAgICAvLyBBbmQsIGlmIGxvY2F0aW9ucyBhcmUgdXNlZCwgdGhlIHtsaW5lLCBjb2x1bW59IG9iamVjdFxuICAgIC8vIGNvcnJlc3BvbmRpbmcgdG8gdGhvc2Ugb2Zmc2V0c1xuICAgIHRoaXMuc3RhcnRMb2MgPSB0aGlzLmVuZExvYyA9IHRoaXMuY3VyUG9zaXRpb24oKTtcblxuICAgIC8vIFBvc2l0aW9uIGluZm9ybWF0aW9uIGZvciB0aGUgcHJldmlvdXMgdG9rZW5cbiAgICB0aGlzLmxhc3RUb2tFbmRMb2MgPSB0aGlzLmxhc3RUb2tTdGFydExvYyA9IG51bGw7XG4gICAgdGhpcy5sYXN0VG9rU3RhcnQgPSB0aGlzLmxhc3RUb2tFbmQgPSB0aGlzLnBvcztcblxuICAgIC8vIFRoZSBjb250ZXh0IHN0YWNrIGlzIHVzZWQgdG8gc3VwZXJmaWNpYWxseSB0cmFjayBzeW50YWN0aWNcbiAgICAvLyBjb250ZXh0IHRvIHByZWRpY3Qgd2hldGhlciBhIHJlZ3VsYXIgZXhwcmVzc2lvbiBpcyBhbGxvd2VkIGluIGFcbiAgICAvLyBnaXZlbiBwb3NpdGlvbi5cbiAgICB0aGlzLmNvbnRleHQgPSB0aGlzLmluaXRpYWxDb250ZXh0KCk7XG4gICAgdGhpcy5leHByQWxsb3dlZCA9IHRydWU7XG5cbiAgICAvLyBGaWd1cmUgb3V0IGlmIGl0J3MgYSBtb2R1bGUgY29kZS5cbiAgICB0aGlzLnN0cmljdCA9IHRoaXMuaW5Nb2R1bGUgPSB0aGlzLm9wdGlvbnMuc291cmNlVHlwZSA9PT0gXCJtb2R1bGVcIjtcblxuICAgIC8vIFVzZWQgdG8gc2lnbmlmeSB0aGUgc3RhcnQgb2YgYSBwb3RlbnRpYWwgYXJyb3cgZnVuY3Rpb25cbiAgICB0aGlzLnBvdGVudGlhbEFycm93QXQgPSAtMTtcblxuICAgIC8vIEZsYWdzIHRvIHRyYWNrIHdoZXRoZXIgd2UgYXJlIGluIGEgZnVuY3Rpb24sIGEgZ2VuZXJhdG9yLlxuICAgIHRoaXMuaW5GdW5jdGlvbiA9IHRoaXMuaW5HZW5lcmF0b3IgPSBmYWxzZTtcbiAgICAvLyBMYWJlbHMgaW4gc2NvcGUuXG4gICAgdGhpcy5sYWJlbHMgPSBbXTtcblxuICAgIC8vIElmIGVuYWJsZWQsIHNraXAgbGVhZGluZyBoYXNoYmFuZyBsaW5lLlxuICAgIGlmICh0aGlzLnBvcyA9PT0gMCAmJiB0aGlzLm9wdGlvbnMuYWxsb3dIYXNoQmFuZyAmJiB0aGlzLmlucHV0LnNsaWNlKDAsIDIpID09PSAnIyEnKSB0aGlzLnNraXBMaW5lQ29tbWVudCgyKTtcbiAgfVxuXG4gIFBhcnNlci5wcm90b3R5cGUuZXh0ZW5kID0gZnVuY3Rpb24gZXh0ZW5kKG5hbWUsIGYpIHtcbiAgICB0aGlzW25hbWVdID0gZih0aGlzW25hbWVdKTtcbiAgfTtcblxuICBQYXJzZXIucHJvdG90eXBlLmxvYWRQbHVnaW5zID0gZnVuY3Rpb24gbG9hZFBsdWdpbnMocGx1Z2luQ29uZmlncykge1xuICAgIGZvciAodmFyIF9uYW1lIGluIHBsdWdpbkNvbmZpZ3MpIHtcbiAgICAgIHZhciBwbHVnaW4gPSBwbHVnaW5zW19uYW1lXTtcbiAgICAgIGlmICghcGx1Z2luKSB0aHJvdyBuZXcgRXJyb3IoXCJQbHVnaW4gJ1wiICsgX25hbWUgKyBcIicgbm90IGZvdW5kXCIpO1xuICAgICAgcGx1Z2luKHRoaXMsIHBsdWdpbkNvbmZpZ3NbX25hbWVdKTtcbiAgICB9XG4gIH07XG5cbiAgUGFyc2VyLnByb3RvdHlwZS5wYXJzZSA9IGZ1bmN0aW9uIHBhcnNlKCkge1xuICAgIHZhciBub2RlID0gdGhpcy5vcHRpb25zLnByb2dyYW0gfHwgdGhpcy5zdGFydE5vZGUoKTtcbiAgICB0aGlzLm5leHRUb2tlbigpO1xuICAgIHJldHVybiB0aGlzLnBhcnNlVG9wTGV2ZWwobm9kZSk7XG4gIH07XG5cbiAgcmV0dXJuIFBhcnNlcjtcbn0pKCk7XG5cbmV4cG9ydHMuUGFyc2VyID0gUGFyc2VyO1xuXG59LHtcIi4vaWRlbnRpZmllclwiOjIsXCIuL29wdGlvbnNcIjo4LFwiLi90b2tlbnR5cGVcIjoxNCxcIi4vd2hpdGVzcGFjZVwiOjE2fV0sMTE6W2Z1bmN0aW9uKF9kZXJlcV8sbW9kdWxlLGV4cG9ydHMpe1xuXCJ1c2Ugc3RyaWN0XCI7XG5cbnZhciBfdG9rZW50eXBlID0gX2RlcmVxXyhcIi4vdG9rZW50eXBlXCIpO1xuXG52YXIgX3N0YXRlID0gX2RlcmVxXyhcIi4vc3RhdGVcIik7XG5cbnZhciBfd2hpdGVzcGFjZSA9IF9kZXJlcV8oXCIuL3doaXRlc3BhY2VcIik7XG5cbnZhciBwcCA9IF9zdGF0ZS5QYXJzZXIucHJvdG90eXBlO1xuXG4vLyAjIyMgU3RhdGVtZW50IHBhcnNpbmdcblxuLy8gUGFyc2UgYSBwcm9ncmFtLiBJbml0aWFsaXplcyB0aGUgcGFyc2VyLCByZWFkcyBhbnkgbnVtYmVyIG9mXG4vLyBzdGF0ZW1lbnRzLCBhbmQgd3JhcHMgdGhlbSBpbiBhIFByb2dyYW0gbm9kZS4gIE9wdGlvbmFsbHkgdGFrZXMgYVxuLy8gYHByb2dyYW1gIGFyZ3VtZW50LiAgSWYgcHJlc2VudCwgdGhlIHN0YXRlbWVudHMgd2lsbCBiZSBhcHBlbmRlZFxuLy8gdG8gaXRzIGJvZHkgaW5zdGVhZCBvZiBjcmVhdGluZyBhIG5ldyBub2RlLlxuXG5wcC5wYXJzZVRvcExldmVsID0gZnVuY3Rpb24gKG5vZGUpIHtcbiAgdmFyIGZpcnN0ID0gdHJ1ZTtcbiAgaWYgKCFub2RlLmJvZHkpIG5vZGUuYm9keSA9IFtdO1xuICB3aGlsZSAodGhpcy50eXBlICE9PSBfdG9rZW50eXBlLnR5cGVzLmVvZikge1xuICAgIHZhciBzdG10ID0gdGhpcy5wYXJzZVN0YXRlbWVudCh0cnVlLCB0cnVlKTtcbiAgICBub2RlLmJvZHkucHVzaChzdG10KTtcbiAgICBpZiAoZmlyc3QpIHtcbiAgICAgIGlmICh0aGlzLmlzVXNlU3RyaWN0KHN0bXQpKSB0aGlzLnNldFN0cmljdCh0cnVlKTtcbiAgICAgIGZpcnN0ID0gZmFsc2U7XG4gICAgfVxuICB9XG4gIHRoaXMubmV4dCgpO1xuICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYpIHtcbiAgICBub2RlLnNvdXJjZVR5cGUgPSB0aGlzLm9wdGlvbnMuc291cmNlVHlwZTtcbiAgfVxuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiUHJvZ3JhbVwiKTtcbn07XG5cbnZhciBsb29wTGFiZWwgPSB7IGtpbmQ6IFwibG9vcFwiIH0sXG4gICAgc3dpdGNoTGFiZWwgPSB7IGtpbmQ6IFwic3dpdGNoXCIgfTtcblxuLy8gUGFyc2UgYSBzaW5nbGUgc3RhdGVtZW50LlxuLy9cbi8vIElmIGV4cGVjdGluZyBhIHN0YXRlbWVudCBhbmQgZmluZGluZyBhIHNsYXNoIG9wZXJhdG9yLCBwYXJzZSBhXG4vLyByZWd1bGFyIGV4cHJlc3Npb24gbGl0ZXJhbC4gVGhpcyBpcyB0byBoYW5kbGUgY2FzZXMgbGlrZVxuLy8gYGlmIChmb28pIC9ibGFoLy5leGVjKGZvbylgLCB3aGVyZSBsb29raW5nIGF0IHRoZSBwcmV2aW91cyB0b2tlblxuLy8gZG9lcyBub3QgaGVscC5cblxucHAucGFyc2VTdGF0ZW1lbnQgPSBmdW5jdGlvbiAoZGVjbGFyYXRpb24sIHRvcExldmVsKSB7XG4gIHZhciBzdGFydHR5cGUgPSB0aGlzLnR5cGUsXG4gICAgICBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcblxuICAvLyBNb3N0IHR5cGVzIG9mIHN0YXRlbWVudHMgYXJlIHJlY29nbml6ZWQgYnkgdGhlIGtleXdvcmQgdGhleVxuICAvLyBzdGFydCB3aXRoLiBNYW55IGFyZSB0cml2aWFsIHRvIHBhcnNlLCBzb21lIHJlcXVpcmUgYSBiaXQgb2ZcbiAgLy8gY29tcGxleGl0eS5cblxuICBzd2l0Y2ggKHN0YXJ0dHlwZSkge1xuICAgIGNhc2UgX3Rva2VudHlwZS50eXBlcy5fYnJlYWs6Y2FzZSBfdG9rZW50eXBlLnR5cGVzLl9jb250aW51ZTpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlQnJlYWtDb250aW51ZVN0YXRlbWVudChub2RlLCBzdGFydHR5cGUua2V5d29yZCk7XG4gICAgY2FzZSBfdG9rZW50eXBlLnR5cGVzLl9kZWJ1Z2dlcjpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlRGVidWdnZXJTdGF0ZW1lbnQobm9kZSk7XG4gICAgY2FzZSBfdG9rZW50eXBlLnR5cGVzLl9kbzpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlRG9TdGF0ZW1lbnQobm9kZSk7XG4gICAgY2FzZSBfdG9rZW50eXBlLnR5cGVzLl9mb3I6XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZUZvclN0YXRlbWVudChub2RlKTtcbiAgICBjYXNlIF90b2tlbnR5cGUudHlwZXMuX2Z1bmN0aW9uOlxuICAgICAgaWYgKCFkZWNsYXJhdGlvbiAmJiB0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNikgdGhpcy51bmV4cGVjdGVkKCk7XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZUZ1bmN0aW9uU3RhdGVtZW50KG5vZGUpO1xuICAgIGNhc2UgX3Rva2VudHlwZS50eXBlcy5fY2xhc3M6XG4gICAgICBpZiAoIWRlY2xhcmF0aW9uKSB0aGlzLnVuZXhwZWN0ZWQoKTtcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlQ2xhc3Mobm9kZSwgdHJ1ZSk7XG4gICAgY2FzZSBfdG9rZW50eXBlLnR5cGVzLl9pZjpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlSWZTdGF0ZW1lbnQobm9kZSk7XG4gICAgY2FzZSBfdG9rZW50eXBlLnR5cGVzLl9yZXR1cm46XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZVJldHVyblN0YXRlbWVudChub2RlKTtcbiAgICBjYXNlIF90b2tlbnR5cGUudHlwZXMuX3N3aXRjaDpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlU3dpdGNoU3RhdGVtZW50KG5vZGUpO1xuICAgIGNhc2UgX3Rva2VudHlwZS50eXBlcy5fdGhyb3c6XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZVRocm93U3RhdGVtZW50KG5vZGUpO1xuICAgIGNhc2UgX3Rva2VudHlwZS50eXBlcy5fdHJ5OlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VUcnlTdGF0ZW1lbnQobm9kZSk7XG4gICAgY2FzZSBfdG9rZW50eXBlLnR5cGVzLl9sZXQ6Y2FzZSBfdG9rZW50eXBlLnR5cGVzLl9jb25zdDpcbiAgICAgIGlmICghZGVjbGFyYXRpb24pIHRoaXMudW5leHBlY3RlZCgpOyAvLyBOT1RFOiBmYWxscyB0aHJvdWdoIHRvIF92YXJcbiAgICBjYXNlIF90b2tlbnR5cGUudHlwZXMuX3ZhcjpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlVmFyU3RhdGVtZW50KG5vZGUsIHN0YXJ0dHlwZSk7XG4gICAgY2FzZSBfdG9rZW50eXBlLnR5cGVzLl93aGlsZTpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlV2hpbGVTdGF0ZW1lbnQobm9kZSk7XG4gICAgY2FzZSBfdG9rZW50eXBlLnR5cGVzLl93aXRoOlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VXaXRoU3RhdGVtZW50KG5vZGUpO1xuICAgIGNhc2UgX3Rva2VudHlwZS50eXBlcy5icmFjZUw6XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZUJsb2NrKCk7XG4gICAgY2FzZSBfdG9rZW50eXBlLnR5cGVzLnNlbWk6XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZUVtcHR5U3RhdGVtZW50KG5vZGUpO1xuICAgIGNhc2UgX3Rva2VudHlwZS50eXBlcy5fZXhwb3J0OlxuICAgIGNhc2UgX3Rva2VudHlwZS50eXBlcy5faW1wb3J0OlxuICAgICAgaWYgKCF0aGlzLm9wdGlvbnMuYWxsb3dJbXBvcnRFeHBvcnRFdmVyeXdoZXJlKSB7XG4gICAgICAgIGlmICghdG9wTGV2ZWwpIHRoaXMucmFpc2UodGhpcy5zdGFydCwgXCInaW1wb3J0JyBhbmQgJ2V4cG9ydCcgbWF5IG9ubHkgYXBwZWFyIGF0IHRoZSB0b3AgbGV2ZWxcIik7XG4gICAgICAgIGlmICghdGhpcy5pbk1vZHVsZSkgdGhpcy5yYWlzZSh0aGlzLnN0YXJ0LCBcIidpbXBvcnQnIGFuZCAnZXhwb3J0JyBtYXkgYXBwZWFyIG9ubHkgd2l0aCAnc291cmNlVHlwZTogbW9kdWxlJ1wiKTtcbiAgICAgIH1cbiAgICAgIHJldHVybiBzdGFydHR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuX2ltcG9ydCA/IHRoaXMucGFyc2VJbXBvcnQobm9kZSkgOiB0aGlzLnBhcnNlRXhwb3J0KG5vZGUpO1xuXG4gICAgLy8gSWYgdGhlIHN0YXRlbWVudCBkb2VzIG5vdCBzdGFydCB3aXRoIGEgc3RhdGVtZW50IGtleXdvcmQgb3IgYVxuICAgIC8vIGJyYWNlLCBpdCdzIGFuIEV4cHJlc3Npb25TdGF0ZW1lbnQgb3IgTGFiZWxlZFN0YXRlbWVudC4gV2VcbiAgICAvLyBzaW1wbHkgc3RhcnQgcGFyc2luZyBhbiBleHByZXNzaW9uLCBhbmQgYWZ0ZXJ3YXJkcywgaWYgdGhlXG4gICAgLy8gbmV4dCB0b2tlbiBpcyBhIGNvbG9uIGFuZCB0aGUgZXhwcmVzc2lvbiB3YXMgYSBzaW1wbGVcbiAgICAvLyBJZGVudGlmaWVyIG5vZGUsIHdlIHN3aXRjaCB0byBpbnRlcnByZXRpbmcgaXQgYXMgYSBsYWJlbC5cbiAgICBkZWZhdWx0OlxuICAgICAgdmFyIG1heWJlTmFtZSA9IHRoaXMudmFsdWUsXG4gICAgICAgICAgZXhwciA9IHRoaXMucGFyc2VFeHByZXNzaW9uKCk7XG4gICAgICBpZiAoc3RhcnR0eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLm5hbWUgJiYgZXhwci50eXBlID09PSBcIklkZW50aWZpZXJcIiAmJiB0aGlzLmVhdChfdG9rZW50eXBlLnR5cGVzLmNvbG9uKSkgcmV0dXJuIHRoaXMucGFyc2VMYWJlbGVkU3RhdGVtZW50KG5vZGUsIG1heWJlTmFtZSwgZXhwcik7ZWxzZSByZXR1cm4gdGhpcy5wYXJzZUV4cHJlc3Npb25TdGF0ZW1lbnQobm9kZSwgZXhwcik7XG4gIH1cbn07XG5cbnBwLnBhcnNlQnJlYWtDb250aW51ZVN0YXRlbWVudCA9IGZ1bmN0aW9uIChub2RlLCBrZXl3b3JkKSB7XG4gIHZhciBpc0JyZWFrID0ga2V5d29yZCA9PSBcImJyZWFrXCI7XG4gIHRoaXMubmV4dCgpO1xuICBpZiAodGhpcy5lYXQoX3Rva2VudHlwZS50eXBlcy5zZW1pKSB8fCB0aGlzLmluc2VydFNlbWljb2xvbigpKSBub2RlLmxhYmVsID0gbnVsbDtlbHNlIGlmICh0aGlzLnR5cGUgIT09IF90b2tlbnR5cGUudHlwZXMubmFtZSkgdGhpcy51bmV4cGVjdGVkKCk7ZWxzZSB7XG4gICAgbm9kZS5sYWJlbCA9IHRoaXMucGFyc2VJZGVudCgpO1xuICAgIHRoaXMuc2VtaWNvbG9uKCk7XG4gIH1cblxuICAvLyBWZXJpZnkgdGhhdCB0aGVyZSBpcyBhbiBhY3R1YWwgZGVzdGluYXRpb24gdG8gYnJlYWsgb3JcbiAgLy8gY29udGludWUgdG8uXG4gIGZvciAodmFyIGkgPSAwOyBpIDwgdGhpcy5sYWJlbHMubGVuZ3RoOyArK2kpIHtcbiAgICB2YXIgbGFiID0gdGhpcy5sYWJlbHNbaV07XG4gICAgaWYgKG5vZGUubGFiZWwgPT0gbnVsbCB8fCBsYWIubmFtZSA9PT0gbm9kZS5sYWJlbC5uYW1lKSB7XG4gICAgICBpZiAobGFiLmtpbmQgIT0gbnVsbCAmJiAoaXNCcmVhayB8fCBsYWIua2luZCA9PT0gXCJsb29wXCIpKSBicmVhaztcbiAgICAgIGlmIChub2RlLmxhYmVsICYmIGlzQnJlYWspIGJyZWFrO1xuICAgIH1cbiAgfVxuICBpZiAoaSA9PT0gdGhpcy5sYWJlbHMubGVuZ3RoKSB0aGlzLnJhaXNlKG5vZGUuc3RhcnQsIFwiVW5zeW50YWN0aWMgXCIgKyBrZXl3b3JkKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBpc0JyZWFrID8gXCJCcmVha1N0YXRlbWVudFwiIDogXCJDb250aW51ZVN0YXRlbWVudFwiKTtcbn07XG5cbnBwLnBhcnNlRGVidWdnZXJTdGF0ZW1lbnQgPSBmdW5jdGlvbiAobm9kZSkge1xuICB0aGlzLm5leHQoKTtcbiAgdGhpcy5zZW1pY29sb24oKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkRlYnVnZ2VyU3RhdGVtZW50XCIpO1xufTtcblxucHAucGFyc2VEb1N0YXRlbWVudCA9IGZ1bmN0aW9uIChub2RlKSB7XG4gIHRoaXMubmV4dCgpO1xuICB0aGlzLmxhYmVscy5wdXNoKGxvb3BMYWJlbCk7XG4gIG5vZGUuYm9keSA9IHRoaXMucGFyc2VTdGF0ZW1lbnQoZmFsc2UpO1xuICB0aGlzLmxhYmVscy5wb3AoKTtcbiAgdGhpcy5leHBlY3QoX3Rva2VudHlwZS50eXBlcy5fd2hpbGUpO1xuICBub2RlLnRlc3QgPSB0aGlzLnBhcnNlUGFyZW5FeHByZXNzaW9uKCk7XG4gIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNikgdGhpcy5lYXQoX3Rva2VudHlwZS50eXBlcy5zZW1pKTtlbHNlIHRoaXMuc2VtaWNvbG9uKCk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJEb1doaWxlU3RhdGVtZW50XCIpO1xufTtcblxuLy8gRGlzYW1iaWd1YXRpbmcgYmV0d2VlbiBhIGBmb3JgIGFuZCBhIGBmb3JgL2BpbmAgb3IgYGZvcmAvYG9mYFxuLy8gbG9vcCBpcyBub24tdHJpdmlhbC4gQmFzaWNhbGx5LCB3ZSBoYXZlIHRvIHBhcnNlIHRoZSBpbml0IGB2YXJgXG4vLyBzdGF0ZW1lbnQgb3IgZXhwcmVzc2lvbiwgZGlzYWxsb3dpbmcgdGhlIGBpbmAgb3BlcmF0b3IgKHNlZVxuLy8gdGhlIHNlY29uZCBwYXJhbWV0ZXIgdG8gYHBhcnNlRXhwcmVzc2lvbmApLCBhbmQgdGhlbiBjaGVja1xuLy8gd2hldGhlciB0aGUgbmV4dCB0b2tlbiBpcyBgaW5gIG9yIGBvZmAuIFdoZW4gdGhlcmUgaXMgbm8gaW5pdFxuLy8gcGFydCAoc2VtaWNvbG9uIGltbWVkaWF0ZWx5IGFmdGVyIHRoZSBvcGVuaW5nIHBhcmVudGhlc2lzKSwgaXRcbi8vIGlzIGEgcmVndWxhciBgZm9yYCBsb29wLlxuXG5wcC5wYXJzZUZvclN0YXRlbWVudCA9IGZ1bmN0aW9uIChub2RlKSB7XG4gIHRoaXMubmV4dCgpO1xuICB0aGlzLmxhYmVscy5wdXNoKGxvb3BMYWJlbCk7XG4gIHRoaXMuZXhwZWN0KF90b2tlbnR5cGUudHlwZXMucGFyZW5MKTtcbiAgaWYgKHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5zZW1pKSByZXR1cm4gdGhpcy5wYXJzZUZvcihub2RlLCBudWxsKTtcbiAgaWYgKHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5fdmFyIHx8IHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5fbGV0IHx8IHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5fY29uc3QpIHtcbiAgICB2YXIgX2luaXQgPSB0aGlzLnN0YXJ0Tm9kZSgpLFxuICAgICAgICB2YXJLaW5kID0gdGhpcy50eXBlO1xuICAgIHRoaXMubmV4dCgpO1xuICAgIHRoaXMucGFyc2VWYXIoX2luaXQsIHRydWUsIHZhcktpbmQpO1xuICAgIHRoaXMuZmluaXNoTm9kZShfaW5pdCwgXCJWYXJpYWJsZURlY2xhcmF0aW9uXCIpO1xuICAgIGlmICgodGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLl9pbiB8fCB0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNiAmJiB0aGlzLmlzQ29udGV4dHVhbChcIm9mXCIpKSAmJiBfaW5pdC5kZWNsYXJhdGlvbnMubGVuZ3RoID09PSAxICYmICEodmFyS2luZCAhPT0gX3Rva2VudHlwZS50eXBlcy5fdmFyICYmIF9pbml0LmRlY2xhcmF0aW9uc1swXS5pbml0KSkgcmV0dXJuIHRoaXMucGFyc2VGb3JJbihub2RlLCBfaW5pdCk7XG4gICAgcmV0dXJuIHRoaXMucGFyc2VGb3Iobm9kZSwgX2luaXQpO1xuICB9XG4gIHZhciByZWZTaG9ydGhhbmREZWZhdWx0UG9zID0geyBzdGFydDogMCB9O1xuICB2YXIgaW5pdCA9IHRoaXMucGFyc2VFeHByZXNzaW9uKHRydWUsIHJlZlNob3J0aGFuZERlZmF1bHRQb3MpO1xuICBpZiAodGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLl9pbiB8fCB0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNiAmJiB0aGlzLmlzQ29udGV4dHVhbChcIm9mXCIpKSB7XG4gICAgdGhpcy50b0Fzc2lnbmFibGUoaW5pdCk7XG4gICAgdGhpcy5jaGVja0xWYWwoaW5pdCk7XG4gICAgcmV0dXJuIHRoaXMucGFyc2VGb3JJbihub2RlLCBpbml0KTtcbiAgfSBlbHNlIGlmIChyZWZTaG9ydGhhbmREZWZhdWx0UG9zLnN0YXJ0KSB7XG4gICAgdGhpcy51bmV4cGVjdGVkKHJlZlNob3J0aGFuZERlZmF1bHRQb3Muc3RhcnQpO1xuICB9XG4gIHJldHVybiB0aGlzLnBhcnNlRm9yKG5vZGUsIGluaXQpO1xufTtcblxucHAucGFyc2VGdW5jdGlvblN0YXRlbWVudCA9IGZ1bmN0aW9uIChub2RlKSB7XG4gIHRoaXMubmV4dCgpO1xuICByZXR1cm4gdGhpcy5wYXJzZUZ1bmN0aW9uKG5vZGUsIHRydWUpO1xufTtcblxucHAucGFyc2VJZlN0YXRlbWVudCA9IGZ1bmN0aW9uIChub2RlKSB7XG4gIHRoaXMubmV4dCgpO1xuICBub2RlLnRlc3QgPSB0aGlzLnBhcnNlUGFyZW5FeHByZXNzaW9uKCk7XG4gIG5vZGUuY29uc2VxdWVudCA9IHRoaXMucGFyc2VTdGF0ZW1lbnQoZmFsc2UpO1xuICBub2RlLmFsdGVybmF0ZSA9IHRoaXMuZWF0KF90b2tlbnR5cGUudHlwZXMuX2Vsc2UpID8gdGhpcy5wYXJzZVN0YXRlbWVudChmYWxzZSkgOiBudWxsO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiSWZTdGF0ZW1lbnRcIik7XG59O1xuXG5wcC5wYXJzZVJldHVyblN0YXRlbWVudCA9IGZ1bmN0aW9uIChub2RlKSB7XG4gIGlmICghdGhpcy5pbkZ1bmN0aW9uICYmICF0aGlzLm9wdGlvbnMuYWxsb3dSZXR1cm5PdXRzaWRlRnVuY3Rpb24pIHRoaXMucmFpc2UodGhpcy5zdGFydCwgXCIncmV0dXJuJyBvdXRzaWRlIG9mIGZ1bmN0aW9uXCIpO1xuICB0aGlzLm5leHQoKTtcblxuICAvLyBJbiBgcmV0dXJuYCAoYW5kIGBicmVha2AvYGNvbnRpbnVlYCksIHRoZSBrZXl3b3JkcyB3aXRoXG4gIC8vIG9wdGlvbmFsIGFyZ3VtZW50cywgd2UgZWFnZXJseSBsb29rIGZvciBhIHNlbWljb2xvbiBvciB0aGVcbiAgLy8gcG9zc2liaWxpdHkgdG8gaW5zZXJ0IG9uZS5cblxuICBpZiAodGhpcy5lYXQoX3Rva2VudHlwZS50eXBlcy5zZW1pKSB8fCB0aGlzLmluc2VydFNlbWljb2xvbigpKSBub2RlLmFyZ3VtZW50ID0gbnVsbDtlbHNlIHtcbiAgICBub2RlLmFyZ3VtZW50ID0gdGhpcy5wYXJzZUV4cHJlc3Npb24oKTt0aGlzLnNlbWljb2xvbigpO1xuICB9XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJSZXR1cm5TdGF0ZW1lbnRcIik7XG59O1xuXG5wcC5wYXJzZVN3aXRjaFN0YXRlbWVudCA9IGZ1bmN0aW9uIChub2RlKSB7XG4gIHRoaXMubmV4dCgpO1xuICBub2RlLmRpc2NyaW1pbmFudCA9IHRoaXMucGFyc2VQYXJlbkV4cHJlc3Npb24oKTtcbiAgbm9kZS5jYXNlcyA9IFtdO1xuICB0aGlzLmV4cGVjdChfdG9rZW50eXBlLnR5cGVzLmJyYWNlTCk7XG4gIHRoaXMubGFiZWxzLnB1c2goc3dpdGNoTGFiZWwpO1xuXG4gIC8vIFN0YXRlbWVudHMgdW5kZXIgbXVzdCBiZSBncm91cGVkIChieSBsYWJlbCkgaW4gU3dpdGNoQ2FzZVxuICAvLyBub2Rlcy4gYGN1cmAgaXMgdXNlZCB0byBrZWVwIHRoZSBub2RlIHRoYXQgd2UgYXJlIGN1cnJlbnRseVxuICAvLyBhZGRpbmcgc3RhdGVtZW50cyB0by5cblxuICBmb3IgKHZhciBjdXIsIHNhd0RlZmF1bHQgPSBmYWxzZTsgdGhpcy50eXBlICE9IF90b2tlbnR5cGUudHlwZXMuYnJhY2VSOykge1xuICAgIGlmICh0aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuX2Nhc2UgfHwgdGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLl9kZWZhdWx0KSB7XG4gICAgICB2YXIgaXNDYXNlID0gdGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLl9jYXNlO1xuICAgICAgaWYgKGN1cikgdGhpcy5maW5pc2hOb2RlKGN1ciwgXCJTd2l0Y2hDYXNlXCIpO1xuICAgICAgbm9kZS5jYXNlcy5wdXNoKGN1ciA9IHRoaXMuc3RhcnROb2RlKCkpO1xuICAgICAgY3VyLmNvbnNlcXVlbnQgPSBbXTtcbiAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgaWYgKGlzQ2FzZSkge1xuICAgICAgICBjdXIudGVzdCA9IHRoaXMucGFyc2VFeHByZXNzaW9uKCk7XG4gICAgICB9IGVsc2Uge1xuICAgICAgICBpZiAoc2F3RGVmYXVsdCkgdGhpcy5yYWlzZSh0aGlzLmxhc3RUb2tTdGFydCwgXCJNdWx0aXBsZSBkZWZhdWx0IGNsYXVzZXNcIik7XG4gICAgICAgIHNhd0RlZmF1bHQgPSB0cnVlO1xuICAgICAgICBjdXIudGVzdCA9IG51bGw7XG4gICAgICB9XG4gICAgICB0aGlzLmV4cGVjdChfdG9rZW50eXBlLnR5cGVzLmNvbG9uKTtcbiAgICB9IGVsc2Uge1xuICAgICAgaWYgKCFjdXIpIHRoaXMudW5leHBlY3RlZCgpO1xuICAgICAgY3VyLmNvbnNlcXVlbnQucHVzaCh0aGlzLnBhcnNlU3RhdGVtZW50KHRydWUpKTtcbiAgICB9XG4gIH1cbiAgaWYgKGN1cikgdGhpcy5maW5pc2hOb2RlKGN1ciwgXCJTd2l0Y2hDYXNlXCIpO1xuICB0aGlzLm5leHQoKTsgLy8gQ2xvc2luZyBicmFjZVxuICB0aGlzLmxhYmVscy5wb3AoKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIlN3aXRjaFN0YXRlbWVudFwiKTtcbn07XG5cbnBwLnBhcnNlVGhyb3dTdGF0ZW1lbnQgPSBmdW5jdGlvbiAobm9kZSkge1xuICB0aGlzLm5leHQoKTtcbiAgaWYgKF93aGl0ZXNwYWNlLmxpbmVCcmVhay50ZXN0KHRoaXMuaW5wdXQuc2xpY2UodGhpcy5sYXN0VG9rRW5kLCB0aGlzLnN0YXJ0KSkpIHRoaXMucmFpc2UodGhpcy5sYXN0VG9rRW5kLCBcIklsbGVnYWwgbmV3bGluZSBhZnRlciB0aHJvd1wiKTtcbiAgbm9kZS5hcmd1bWVudCA9IHRoaXMucGFyc2VFeHByZXNzaW9uKCk7XG4gIHRoaXMuc2VtaWNvbG9uKCk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJUaHJvd1N0YXRlbWVudFwiKTtcbn07XG5cbi8vIFJldXNlZCBlbXB0eSBhcnJheSBhZGRlZCBmb3Igbm9kZSBmaWVsZHMgdGhhdCBhcmUgYWx3YXlzIGVtcHR5LlxuXG52YXIgZW1wdHkgPSBbXTtcblxucHAucGFyc2VUcnlTdGF0ZW1lbnQgPSBmdW5jdGlvbiAobm9kZSkge1xuICB0aGlzLm5leHQoKTtcbiAgbm9kZS5ibG9jayA9IHRoaXMucGFyc2VCbG9jaygpO1xuICBub2RlLmhhbmRsZXIgPSBudWxsO1xuICBpZiAodGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLl9jYXRjaCkge1xuICAgIHZhciBjbGF1c2UgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICAgIHRoaXMubmV4dCgpO1xuICAgIHRoaXMuZXhwZWN0KF90b2tlbnR5cGUudHlwZXMucGFyZW5MKTtcbiAgICBjbGF1c2UucGFyYW0gPSB0aGlzLnBhcnNlQmluZGluZ0F0b20oKTtcbiAgICB0aGlzLmNoZWNrTFZhbChjbGF1c2UucGFyYW0sIHRydWUpO1xuICAgIHRoaXMuZXhwZWN0KF90b2tlbnR5cGUudHlwZXMucGFyZW5SKTtcbiAgICBjbGF1c2UuZ3VhcmQgPSBudWxsO1xuICAgIGNsYXVzZS5ib2R5ID0gdGhpcy5wYXJzZUJsb2NrKCk7XG4gICAgbm9kZS5oYW5kbGVyID0gdGhpcy5maW5pc2hOb2RlKGNsYXVzZSwgXCJDYXRjaENsYXVzZVwiKTtcbiAgfVxuICBub2RlLmd1YXJkZWRIYW5kbGVycyA9IGVtcHR5O1xuICBub2RlLmZpbmFsaXplciA9IHRoaXMuZWF0KF90b2tlbnR5cGUudHlwZXMuX2ZpbmFsbHkpID8gdGhpcy5wYXJzZUJsb2NrKCkgOiBudWxsO1xuICBpZiAoIW5vZGUuaGFuZGxlciAmJiAhbm9kZS5maW5hbGl6ZXIpIHRoaXMucmFpc2Uobm9kZS5zdGFydCwgXCJNaXNzaW5nIGNhdGNoIG9yIGZpbmFsbHkgY2xhdXNlXCIpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiVHJ5U3RhdGVtZW50XCIpO1xufTtcblxucHAucGFyc2VWYXJTdGF0ZW1lbnQgPSBmdW5jdGlvbiAobm9kZSwga2luZCkge1xuICB0aGlzLm5leHQoKTtcbiAgdGhpcy5wYXJzZVZhcihub2RlLCBmYWxzZSwga2luZCk7XG4gIHRoaXMuc2VtaWNvbG9uKCk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJWYXJpYWJsZURlY2xhcmF0aW9uXCIpO1xufTtcblxucHAucGFyc2VXaGlsZVN0YXRlbWVudCA9IGZ1bmN0aW9uIChub2RlKSB7XG4gIHRoaXMubmV4dCgpO1xuICBub2RlLnRlc3QgPSB0aGlzLnBhcnNlUGFyZW5FeHByZXNzaW9uKCk7XG4gIHRoaXMubGFiZWxzLnB1c2gobG9vcExhYmVsKTtcbiAgbm9kZS5ib2R5ID0gdGhpcy5wYXJzZVN0YXRlbWVudChmYWxzZSk7XG4gIHRoaXMubGFiZWxzLnBvcCgpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiV2hpbGVTdGF0ZW1lbnRcIik7XG59O1xuXG5wcC5wYXJzZVdpdGhTdGF0ZW1lbnQgPSBmdW5jdGlvbiAobm9kZSkge1xuICBpZiAodGhpcy5zdHJpY3QpIHRoaXMucmFpc2UodGhpcy5zdGFydCwgXCInd2l0aCcgaW4gc3RyaWN0IG1vZGVcIik7XG4gIHRoaXMubmV4dCgpO1xuICBub2RlLm9iamVjdCA9IHRoaXMucGFyc2VQYXJlbkV4cHJlc3Npb24oKTtcbiAgbm9kZS5ib2R5ID0gdGhpcy5wYXJzZVN0YXRlbWVudChmYWxzZSk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJXaXRoU3RhdGVtZW50XCIpO1xufTtcblxucHAucGFyc2VFbXB0eVN0YXRlbWVudCA9IGZ1bmN0aW9uIChub2RlKSB7XG4gIHRoaXMubmV4dCgpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiRW1wdHlTdGF0ZW1lbnRcIik7XG59O1xuXG5wcC5wYXJzZUxhYmVsZWRTdGF0ZW1lbnQgPSBmdW5jdGlvbiAobm9kZSwgbWF5YmVOYW1lLCBleHByKSB7XG4gIGZvciAodmFyIGkgPSAwOyBpIDwgdGhpcy5sYWJlbHMubGVuZ3RoOyArK2kpIHtcbiAgICBpZiAodGhpcy5sYWJlbHNbaV0ubmFtZSA9PT0gbWF5YmVOYW1lKSB0aGlzLnJhaXNlKGV4cHIuc3RhcnQsIFwiTGFiZWwgJ1wiICsgbWF5YmVOYW1lICsgXCInIGlzIGFscmVhZHkgZGVjbGFyZWRcIik7XG4gIH12YXIga2luZCA9IHRoaXMudHlwZS5pc0xvb3AgPyBcImxvb3BcIiA6IHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5fc3dpdGNoID8gXCJzd2l0Y2hcIiA6IG51bGw7XG4gIGZvciAodmFyIGkgPSB0aGlzLmxhYmVscy5sZW5ndGggLSAxOyBpID49IDA7IGktLSkge1xuICAgIHZhciBsYWJlbCA9IHRoaXMubGFiZWxzW2ldO1xuICAgIGlmIChsYWJlbC5zdGF0ZW1lbnRTdGFydCA9PSBub2RlLnN0YXJ0KSB7XG4gICAgICBsYWJlbC5zdGF0ZW1lbnRTdGFydCA9IHRoaXMuc3RhcnQ7XG4gICAgICBsYWJlbC5raW5kID0ga2luZDtcbiAgICB9IGVsc2UgYnJlYWs7XG4gIH1cbiAgdGhpcy5sYWJlbHMucHVzaCh7IG5hbWU6IG1heWJlTmFtZSwga2luZDoga2luZCwgc3RhdGVtZW50U3RhcnQ6IHRoaXMuc3RhcnQgfSk7XG4gIG5vZGUuYm9keSA9IHRoaXMucGFyc2VTdGF0ZW1lbnQodHJ1ZSk7XG4gIHRoaXMubGFiZWxzLnBvcCgpO1xuICBub2RlLmxhYmVsID0gZXhwcjtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkxhYmVsZWRTdGF0ZW1lbnRcIik7XG59O1xuXG5wcC5wYXJzZUV4cHJlc3Npb25TdGF0ZW1lbnQgPSBmdW5jdGlvbiAobm9kZSwgZXhwcikge1xuICBub2RlLmV4cHJlc3Npb24gPSBleHByO1xuICB0aGlzLnNlbWljb2xvbigpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiRXhwcmVzc2lvblN0YXRlbWVudFwiKTtcbn07XG5cbi8vIFBhcnNlIGEgc2VtaWNvbG9uLWVuY2xvc2VkIGJsb2NrIG9mIHN0YXRlbWVudHMsIGhhbmRsaW5nIGBcInVzZVxuLy8gc3RyaWN0XCJgIGRlY2xhcmF0aW9ucyB3aGVuIGBhbGxvd1N0cmljdGAgaXMgdHJ1ZSAodXNlZCBmb3Jcbi8vIGZ1bmN0aW9uIGJvZGllcykuXG5cbnBwLnBhcnNlQmxvY2sgPSBmdW5jdGlvbiAoYWxsb3dTdHJpY3QpIHtcbiAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpLFxuICAgICAgZmlyc3QgPSB0cnVlLFxuICAgICAgb2xkU3RyaWN0ID0gdW5kZWZpbmVkO1xuICBub2RlLmJvZHkgPSBbXTtcbiAgdGhpcy5leHBlY3QoX3Rva2VudHlwZS50eXBlcy5icmFjZUwpO1xuICB3aGlsZSAoIXRoaXMuZWF0KF90b2tlbnR5cGUudHlwZXMuYnJhY2VSKSkge1xuICAgIHZhciBzdG10ID0gdGhpcy5wYXJzZVN0YXRlbWVudCh0cnVlKTtcbiAgICBub2RlLmJvZHkucHVzaChzdG10KTtcbiAgICBpZiAoZmlyc3QgJiYgYWxsb3dTdHJpY3QgJiYgdGhpcy5pc1VzZVN0cmljdChzdG10KSkge1xuICAgICAgb2xkU3RyaWN0ID0gdGhpcy5zdHJpY3Q7XG4gICAgICB0aGlzLnNldFN0cmljdCh0aGlzLnN0cmljdCA9IHRydWUpO1xuICAgIH1cbiAgICBmaXJzdCA9IGZhbHNlO1xuICB9XG4gIGlmIChvbGRTdHJpY3QgPT09IGZhbHNlKSB0aGlzLnNldFN0cmljdChmYWxzZSk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJCbG9ja1N0YXRlbWVudFwiKTtcbn07XG5cbi8vIFBhcnNlIGEgcmVndWxhciBgZm9yYCBsb29wLiBUaGUgZGlzYW1iaWd1YXRpb24gY29kZSBpblxuLy8gYHBhcnNlU3RhdGVtZW50YCB3aWxsIGFscmVhZHkgaGF2ZSBwYXJzZWQgdGhlIGluaXQgc3RhdGVtZW50IG9yXG4vLyBleHByZXNzaW9uLlxuXG5wcC5wYXJzZUZvciA9IGZ1bmN0aW9uIChub2RlLCBpbml0KSB7XG4gIG5vZGUuaW5pdCA9IGluaXQ7XG4gIHRoaXMuZXhwZWN0KF90b2tlbnR5cGUudHlwZXMuc2VtaSk7XG4gIG5vZGUudGVzdCA9IHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5zZW1pID8gbnVsbCA6IHRoaXMucGFyc2VFeHByZXNzaW9uKCk7XG4gIHRoaXMuZXhwZWN0KF90b2tlbnR5cGUudHlwZXMuc2VtaSk7XG4gIG5vZGUudXBkYXRlID0gdGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLnBhcmVuUiA/IG51bGwgOiB0aGlzLnBhcnNlRXhwcmVzc2lvbigpO1xuICB0aGlzLmV4cGVjdChfdG9rZW50eXBlLnR5cGVzLnBhcmVuUik7XG4gIG5vZGUuYm9keSA9IHRoaXMucGFyc2VTdGF0ZW1lbnQoZmFsc2UpO1xuICB0aGlzLmxhYmVscy5wb3AoKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkZvclN0YXRlbWVudFwiKTtcbn07XG5cbi8vIFBhcnNlIGEgYGZvcmAvYGluYCBhbmQgYGZvcmAvYG9mYCBsb29wLCB3aGljaCBhcmUgYWxtb3N0XG4vLyBzYW1lIGZyb20gcGFyc2VyJ3MgcGVyc3BlY3RpdmUuXG5cbnBwLnBhcnNlRm9ySW4gPSBmdW5jdGlvbiAobm9kZSwgaW5pdCkge1xuICB2YXIgdHlwZSA9IHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5faW4gPyBcIkZvckluU3RhdGVtZW50XCIgOiBcIkZvck9mU3RhdGVtZW50XCI7XG4gIHRoaXMubmV4dCgpO1xuICBub2RlLmxlZnQgPSBpbml0O1xuICBub2RlLnJpZ2h0ID0gdGhpcy5wYXJzZUV4cHJlc3Npb24oKTtcbiAgdGhpcy5leHBlY3QoX3Rva2VudHlwZS50eXBlcy5wYXJlblIpO1xuICBub2RlLmJvZHkgPSB0aGlzLnBhcnNlU3RhdGVtZW50KGZhbHNlKTtcbiAgdGhpcy5sYWJlbHMucG9wKCk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgdHlwZSk7XG59O1xuXG4vLyBQYXJzZSBhIGxpc3Qgb2YgdmFyaWFibGUgZGVjbGFyYXRpb25zLlxuXG5wcC5wYXJzZVZhciA9IGZ1bmN0aW9uIChub2RlLCBpc0Zvciwga2luZCkge1xuICBub2RlLmRlY2xhcmF0aW9ucyA9IFtdO1xuICBub2RlLmtpbmQgPSBraW5kLmtleXdvcmQ7XG4gIGZvciAoOzspIHtcbiAgICB2YXIgZGVjbCA9IHRoaXMuc3RhcnROb2RlKCk7XG4gICAgdGhpcy5wYXJzZVZhcklkKGRlY2wpO1xuICAgIGlmICh0aGlzLmVhdChfdG9rZW50eXBlLnR5cGVzLmVxKSkge1xuICAgICAgZGVjbC5pbml0ID0gdGhpcy5wYXJzZU1heWJlQXNzaWduKGlzRm9yKTtcbiAgICB9IGVsc2UgaWYgKGtpbmQgPT09IF90b2tlbnR5cGUudHlwZXMuX2NvbnN0ICYmICEodGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLl9pbiB8fCB0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNiAmJiB0aGlzLmlzQ29udGV4dHVhbChcIm9mXCIpKSkge1xuICAgICAgdGhpcy51bmV4cGVjdGVkKCk7XG4gICAgfSBlbHNlIGlmIChkZWNsLmlkLnR5cGUgIT0gXCJJZGVudGlmaWVyXCIgJiYgIShpc0ZvciAmJiAodGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLl9pbiB8fCB0aGlzLmlzQ29udGV4dHVhbChcIm9mXCIpKSkpIHtcbiAgICAgIHRoaXMucmFpc2UodGhpcy5sYXN0VG9rRW5kLCBcIkNvbXBsZXggYmluZGluZyBwYXR0ZXJucyByZXF1aXJlIGFuIGluaXRpYWxpemF0aW9uIHZhbHVlXCIpO1xuICAgIH0gZWxzZSB7XG4gICAgICBkZWNsLmluaXQgPSBudWxsO1xuICAgIH1cbiAgICBub2RlLmRlY2xhcmF0aW9ucy5wdXNoKHRoaXMuZmluaXNoTm9kZShkZWNsLCBcIlZhcmlhYmxlRGVjbGFyYXRvclwiKSk7XG4gICAgaWYgKCF0aGlzLmVhdChfdG9rZW50eXBlLnR5cGVzLmNvbW1hKSkgYnJlYWs7XG4gIH1cbiAgcmV0dXJuIG5vZGU7XG59O1xuXG5wcC5wYXJzZVZhcklkID0gZnVuY3Rpb24gKGRlY2wpIHtcbiAgZGVjbC5pZCA9IHRoaXMucGFyc2VCaW5kaW5nQXRvbSgpO1xuICB0aGlzLmNoZWNrTFZhbChkZWNsLmlkLCB0cnVlKTtcbn07XG5cbi8vIFBhcnNlIGEgZnVuY3Rpb24gZGVjbGFyYXRpb24gb3IgbGl0ZXJhbCAoZGVwZW5kaW5nIG9uIHRoZVxuLy8gYGlzU3RhdGVtZW50YCBwYXJhbWV0ZXIpLlxuXG5wcC5wYXJzZUZ1bmN0aW9uID0gZnVuY3Rpb24gKG5vZGUsIGlzU3RhdGVtZW50LCBhbGxvd0V4cHJlc3Npb25Cb2R5KSB7XG4gIHRoaXMuaW5pdEZ1bmN0aW9uKG5vZGUpO1xuICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYpIG5vZGUuZ2VuZXJhdG9yID0gdGhpcy5lYXQoX3Rva2VudHlwZS50eXBlcy5zdGFyKTtcbiAgaWYgKGlzU3RhdGVtZW50IHx8IHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5uYW1lKSBub2RlLmlkID0gdGhpcy5wYXJzZUlkZW50KCk7XG4gIHRoaXMucGFyc2VGdW5jdGlvblBhcmFtcyhub2RlKTtcbiAgdGhpcy5wYXJzZUZ1bmN0aW9uQm9keShub2RlLCBhbGxvd0V4cHJlc3Npb25Cb2R5KTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBpc1N0YXRlbWVudCA/IFwiRnVuY3Rpb25EZWNsYXJhdGlvblwiIDogXCJGdW5jdGlvbkV4cHJlc3Npb25cIik7XG59O1xuXG5wcC5wYXJzZUZ1bmN0aW9uUGFyYW1zID0gZnVuY3Rpb24gKG5vZGUpIHtcbiAgdGhpcy5leHBlY3QoX3Rva2VudHlwZS50eXBlcy5wYXJlbkwpO1xuICBub2RlLnBhcmFtcyA9IHRoaXMucGFyc2VCaW5kaW5nTGlzdChfdG9rZW50eXBlLnR5cGVzLnBhcmVuUiwgZmFsc2UsIGZhbHNlKTtcbn07XG5cbi8vIFBhcnNlIGEgY2xhc3MgZGVjbGFyYXRpb24gb3IgbGl0ZXJhbCAoZGVwZW5kaW5nIG9uIHRoZVxuLy8gYGlzU3RhdGVtZW50YCBwYXJhbWV0ZXIpLlxuXG5wcC5wYXJzZUNsYXNzID0gZnVuY3Rpb24gKG5vZGUsIGlzU3RhdGVtZW50KSB7XG4gIHRoaXMubmV4dCgpO1xuICB0aGlzLnBhcnNlQ2xhc3NJZChub2RlLCBpc1N0YXRlbWVudCk7XG4gIHRoaXMucGFyc2VDbGFzc1N1cGVyKG5vZGUpO1xuICB2YXIgY2xhc3NCb2R5ID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgdmFyIGhhZENvbnN0cnVjdG9yID0gZmFsc2U7XG4gIGNsYXNzQm9keS5ib2R5ID0gW107XG4gIHRoaXMuZXhwZWN0KF90b2tlbnR5cGUudHlwZXMuYnJhY2VMKTtcbiAgd2hpbGUgKCF0aGlzLmVhdChfdG9rZW50eXBlLnR5cGVzLmJyYWNlUikpIHtcbiAgICBpZiAodGhpcy5lYXQoX3Rva2VudHlwZS50eXBlcy5zZW1pKSkgY29udGludWU7XG4gICAgdmFyIG1ldGhvZCA9IHRoaXMuc3RhcnROb2RlKCk7XG4gICAgdmFyIGlzR2VuZXJhdG9yID0gdGhpcy5lYXQoX3Rva2VudHlwZS50eXBlcy5zdGFyKTtcbiAgICB2YXIgaXNNYXliZVN0YXRpYyA9IHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5uYW1lICYmIHRoaXMudmFsdWUgPT09IFwic3RhdGljXCI7XG4gICAgdGhpcy5wYXJzZVByb3BlcnR5TmFtZShtZXRob2QpO1xuICAgIG1ldGhvZFtcInN0YXRpY1wiXSA9IGlzTWF5YmVTdGF0aWMgJiYgdGhpcy50eXBlICE9PSBfdG9rZW50eXBlLnR5cGVzLnBhcmVuTDtcbiAgICBpZiAobWV0aG9kW1wic3RhdGljXCJdKSB7XG4gICAgICBpZiAoaXNHZW5lcmF0b3IpIHRoaXMudW5leHBlY3RlZCgpO1xuICAgICAgaXNHZW5lcmF0b3IgPSB0aGlzLmVhdChfdG9rZW50eXBlLnR5cGVzLnN0YXIpO1xuICAgICAgdGhpcy5wYXJzZVByb3BlcnR5TmFtZShtZXRob2QpO1xuICAgIH1cbiAgICBtZXRob2Qua2luZCA9IFwibWV0aG9kXCI7XG4gICAgdmFyIGlzR2V0U2V0ID0gZmFsc2U7XG4gICAgaWYgKCFtZXRob2QuY29tcHV0ZWQpIHtcbiAgICAgIHZhciBrZXkgPSBtZXRob2Qua2V5O1xuXG4gICAgICBpZiAoIWlzR2VuZXJhdG9yICYmIGtleS50eXBlID09PSBcIklkZW50aWZpZXJcIiAmJiB0aGlzLnR5cGUgIT09IF90b2tlbnR5cGUudHlwZXMucGFyZW5MICYmIChrZXkubmFtZSA9PT0gXCJnZXRcIiB8fCBrZXkubmFtZSA9PT0gXCJzZXRcIikpIHtcbiAgICAgICAgaXNHZXRTZXQgPSB0cnVlO1xuICAgICAgICBtZXRob2Qua2luZCA9IGtleS5uYW1lO1xuICAgICAgICBrZXkgPSB0aGlzLnBhcnNlUHJvcGVydHlOYW1lKG1ldGhvZCk7XG4gICAgICB9XG4gICAgICBpZiAoIW1ldGhvZFtcInN0YXRpY1wiXSAmJiAoa2V5LnR5cGUgPT09IFwiSWRlbnRpZmllclwiICYmIGtleS5uYW1lID09PSBcImNvbnN0cnVjdG9yXCIgfHwga2V5LnR5cGUgPT09IFwiTGl0ZXJhbFwiICYmIGtleS52YWx1ZSA9PT0gXCJjb25zdHJ1Y3RvclwiKSkge1xuICAgICAgICBpZiAoaGFkQ29uc3RydWN0b3IpIHRoaXMucmFpc2Uoa2V5LnN0YXJ0LCBcIkR1cGxpY2F0ZSBjb25zdHJ1Y3RvciBpbiB0aGUgc2FtZSBjbGFzc1wiKTtcbiAgICAgICAgaWYgKGlzR2V0U2V0KSB0aGlzLnJhaXNlKGtleS5zdGFydCwgXCJDb25zdHJ1Y3RvciBjYW4ndCBoYXZlIGdldC9zZXQgbW9kaWZpZXJcIik7XG4gICAgICAgIGlmIChpc0dlbmVyYXRvcikgdGhpcy5yYWlzZShrZXkuc3RhcnQsIFwiQ29uc3RydWN0b3IgY2FuJ3QgYmUgYSBnZW5lcmF0b3JcIik7XG4gICAgICAgIG1ldGhvZC5raW5kID0gXCJjb25zdHJ1Y3RvclwiO1xuICAgICAgICBoYWRDb25zdHJ1Y3RvciA9IHRydWU7XG4gICAgICB9XG4gICAgfVxuICAgIHRoaXMucGFyc2VDbGFzc01ldGhvZChjbGFzc0JvZHksIG1ldGhvZCwgaXNHZW5lcmF0b3IpO1xuICAgIGlmIChpc0dldFNldCkge1xuICAgICAgdmFyIHBhcmFtQ291bnQgPSBtZXRob2Qua2luZCA9PT0gXCJnZXRcIiA/IDAgOiAxO1xuICAgICAgaWYgKG1ldGhvZC52YWx1ZS5wYXJhbXMubGVuZ3RoICE9PSBwYXJhbUNvdW50KSB7XG4gICAgICAgIHZhciBzdGFydCA9IG1ldGhvZC52YWx1ZS5zdGFydDtcbiAgICAgICAgaWYgKG1ldGhvZC5raW5kID09PSBcImdldFwiKSB0aGlzLnJhaXNlKHN0YXJ0LCBcImdldHRlciBzaG91bGQgaGF2ZSBubyBwYXJhbXNcIik7ZWxzZSB0aGlzLnJhaXNlKHN0YXJ0LCBcInNldHRlciBzaG91bGQgaGF2ZSBleGFjdGx5IG9uZSBwYXJhbVwiKTtcbiAgICAgIH1cbiAgICB9XG4gIH1cbiAgbm9kZS5ib2R5ID0gdGhpcy5maW5pc2hOb2RlKGNsYXNzQm9keSwgXCJDbGFzc0JvZHlcIik7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgaXNTdGF0ZW1lbnQgPyBcIkNsYXNzRGVjbGFyYXRpb25cIiA6IFwiQ2xhc3NFeHByZXNzaW9uXCIpO1xufTtcblxucHAucGFyc2VDbGFzc01ldGhvZCA9IGZ1bmN0aW9uIChjbGFzc0JvZHksIG1ldGhvZCwgaXNHZW5lcmF0b3IpIHtcbiAgbWV0aG9kLnZhbHVlID0gdGhpcy5wYXJzZU1ldGhvZChpc0dlbmVyYXRvcik7XG4gIGNsYXNzQm9keS5ib2R5LnB1c2godGhpcy5maW5pc2hOb2RlKG1ldGhvZCwgXCJNZXRob2REZWZpbml0aW9uXCIpKTtcbn07XG5cbnBwLnBhcnNlQ2xhc3NJZCA9IGZ1bmN0aW9uIChub2RlLCBpc1N0YXRlbWVudCkge1xuICBub2RlLmlkID0gdGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLm5hbWUgPyB0aGlzLnBhcnNlSWRlbnQoKSA6IGlzU3RhdGVtZW50ID8gdGhpcy51bmV4cGVjdGVkKCkgOiBudWxsO1xufTtcblxucHAucGFyc2VDbGFzc1N1cGVyID0gZnVuY3Rpb24gKG5vZGUpIHtcbiAgbm9kZS5zdXBlckNsYXNzID0gdGhpcy5lYXQoX3Rva2VudHlwZS50eXBlcy5fZXh0ZW5kcykgPyB0aGlzLnBhcnNlRXhwclN1YnNjcmlwdHMoKSA6IG51bGw7XG59O1xuXG4vLyBQYXJzZXMgbW9kdWxlIGV4cG9ydCBkZWNsYXJhdGlvbi5cblxucHAucGFyc2VFeHBvcnQgPSBmdW5jdGlvbiAobm9kZSkge1xuICB0aGlzLm5leHQoKTtcbiAgLy8gZXhwb3J0ICogZnJvbSAnLi4uJ1xuICBpZiAodGhpcy5lYXQoX3Rva2VudHlwZS50eXBlcy5zdGFyKSkge1xuICAgIHRoaXMuZXhwZWN0Q29udGV4dHVhbChcImZyb21cIik7XG4gICAgbm9kZS5zb3VyY2UgPSB0aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuc3RyaW5nID8gdGhpcy5wYXJzZUV4cHJBdG9tKCkgOiB0aGlzLnVuZXhwZWN0ZWQoKTtcbiAgICB0aGlzLnNlbWljb2xvbigpO1xuICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJFeHBvcnRBbGxEZWNsYXJhdGlvblwiKTtcbiAgfVxuICBpZiAodGhpcy5lYXQoX3Rva2VudHlwZS50eXBlcy5fZGVmYXVsdCkpIHtcbiAgICAvLyBleHBvcnQgZGVmYXVsdCAuLi5cbiAgICB2YXIgZXhwciA9IHRoaXMucGFyc2VNYXliZUFzc2lnbigpO1xuICAgIHZhciBuZWVkc1NlbWkgPSB0cnVlO1xuICAgIGlmIChleHByLnR5cGUgPT0gXCJGdW5jdGlvbkV4cHJlc3Npb25cIiB8fCBleHByLnR5cGUgPT0gXCJDbGFzc0V4cHJlc3Npb25cIikge1xuICAgICAgbmVlZHNTZW1pID0gZmFsc2U7XG4gICAgICBpZiAoZXhwci5pZCkge1xuICAgICAgICBleHByLnR5cGUgPSBleHByLnR5cGUgPT0gXCJGdW5jdGlvbkV4cHJlc3Npb25cIiA/IFwiRnVuY3Rpb25EZWNsYXJhdGlvblwiIDogXCJDbGFzc0RlY2xhcmF0aW9uXCI7XG4gICAgICB9XG4gICAgfVxuICAgIG5vZGUuZGVjbGFyYXRpb24gPSBleHByO1xuICAgIGlmIChuZWVkc1NlbWkpIHRoaXMuc2VtaWNvbG9uKCk7XG4gICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkV4cG9ydERlZmF1bHREZWNsYXJhdGlvblwiKTtcbiAgfVxuICAvLyBleHBvcnQgdmFyfGNvbnN0fGxldHxmdW5jdGlvbnxjbGFzcyAuLi5cbiAgaWYgKHRoaXMuc2hvdWxkUGFyc2VFeHBvcnRTdGF0ZW1lbnQoKSkge1xuICAgIG5vZGUuZGVjbGFyYXRpb24gPSB0aGlzLnBhcnNlU3RhdGVtZW50KHRydWUpO1xuICAgIG5vZGUuc3BlY2lmaWVycyA9IFtdO1xuICAgIG5vZGUuc291cmNlID0gbnVsbDtcbiAgfSBlbHNlIHtcbiAgICAvLyBleHBvcnQgeyB4LCB5IGFzIHogfSBbZnJvbSAnLi4uJ11cbiAgICBub2RlLmRlY2xhcmF0aW9uID0gbnVsbDtcbiAgICBub2RlLnNwZWNpZmllcnMgPSB0aGlzLnBhcnNlRXhwb3J0U3BlY2lmaWVycygpO1xuICAgIGlmICh0aGlzLmVhdENvbnRleHR1YWwoXCJmcm9tXCIpKSB7XG4gICAgICBub2RlLnNvdXJjZSA9IHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5zdHJpbmcgPyB0aGlzLnBhcnNlRXhwckF0b20oKSA6IHRoaXMudW5leHBlY3RlZCgpO1xuICAgIH0gZWxzZSB7XG4gICAgICBub2RlLnNvdXJjZSA9IG51bGw7XG4gICAgfVxuICAgIHRoaXMuc2VtaWNvbG9uKCk7XG4gIH1cbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkV4cG9ydE5hbWVkRGVjbGFyYXRpb25cIik7XG59O1xuXG5wcC5zaG91bGRQYXJzZUV4cG9ydFN0YXRlbWVudCA9IGZ1bmN0aW9uICgpIHtcbiAgcmV0dXJuIHRoaXMudHlwZS5rZXl3b3JkO1xufTtcblxuLy8gUGFyc2VzIGEgY29tbWEtc2VwYXJhdGVkIGxpc3Qgb2YgbW9kdWxlIGV4cG9ydHMuXG5cbnBwLnBhcnNlRXhwb3J0U3BlY2lmaWVycyA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIG5vZGVzID0gW10sXG4gICAgICBmaXJzdCA9IHRydWU7XG4gIC8vIGV4cG9ydCB7IHgsIHkgYXMgeiB9IFtmcm9tICcuLi4nXVxuICB0aGlzLmV4cGVjdChfdG9rZW50eXBlLnR5cGVzLmJyYWNlTCk7XG4gIHdoaWxlICghdGhpcy5lYXQoX3Rva2VudHlwZS50eXBlcy5icmFjZVIpKSB7XG4gICAgaWYgKCFmaXJzdCkge1xuICAgICAgdGhpcy5leHBlY3QoX3Rva2VudHlwZS50eXBlcy5jb21tYSk7XG4gICAgICBpZiAodGhpcy5hZnRlclRyYWlsaW5nQ29tbWEoX3Rva2VudHlwZS50eXBlcy5icmFjZVIpKSBicmVhaztcbiAgICB9IGVsc2UgZmlyc3QgPSBmYWxzZTtcblxuICAgIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgICBub2RlLmxvY2FsID0gdGhpcy5wYXJzZUlkZW50KHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5fZGVmYXVsdCk7XG4gICAgbm9kZS5leHBvcnRlZCA9IHRoaXMuZWF0Q29udGV4dHVhbChcImFzXCIpID8gdGhpcy5wYXJzZUlkZW50KHRydWUpIDogbm9kZS5sb2NhbDtcbiAgICBub2Rlcy5wdXNoKHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkV4cG9ydFNwZWNpZmllclwiKSk7XG4gIH1cbiAgcmV0dXJuIG5vZGVzO1xufTtcblxuLy8gUGFyc2VzIGltcG9ydCBkZWNsYXJhdGlvbi5cblxucHAucGFyc2VJbXBvcnQgPSBmdW5jdGlvbiAobm9kZSkge1xuICB0aGlzLm5leHQoKTtcbiAgLy8gaW1wb3J0ICcuLi4nXG4gIGlmICh0aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuc3RyaW5nKSB7XG4gICAgbm9kZS5zcGVjaWZpZXJzID0gZW1wdHk7XG4gICAgbm9kZS5zb3VyY2UgPSB0aGlzLnBhcnNlRXhwckF0b20oKTtcbiAgfSBlbHNlIHtcbiAgICBub2RlLnNwZWNpZmllcnMgPSB0aGlzLnBhcnNlSW1wb3J0U3BlY2lmaWVycygpO1xuICAgIHRoaXMuZXhwZWN0Q29udGV4dHVhbChcImZyb21cIik7XG4gICAgbm9kZS5zb3VyY2UgPSB0aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuc3RyaW5nID8gdGhpcy5wYXJzZUV4cHJBdG9tKCkgOiB0aGlzLnVuZXhwZWN0ZWQoKTtcbiAgfVxuICB0aGlzLnNlbWljb2xvbigpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiSW1wb3J0RGVjbGFyYXRpb25cIik7XG59O1xuXG4vLyBQYXJzZXMgYSBjb21tYS1zZXBhcmF0ZWQgbGlzdCBvZiBtb2R1bGUgaW1wb3J0cy5cblxucHAucGFyc2VJbXBvcnRTcGVjaWZpZXJzID0gZnVuY3Rpb24gKCkge1xuICB2YXIgbm9kZXMgPSBbXSxcbiAgICAgIGZpcnN0ID0gdHJ1ZTtcbiAgaWYgKHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5uYW1lKSB7XG4gICAgLy8gaW1wb3J0IGRlZmF1bHRPYmosIHsgeCwgeSBhcyB6IH0gZnJvbSAnLi4uJ1xuICAgIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgICBub2RlLmxvY2FsID0gdGhpcy5wYXJzZUlkZW50KCk7XG4gICAgdGhpcy5jaGVja0xWYWwobm9kZS5sb2NhbCwgdHJ1ZSk7XG4gICAgbm9kZXMucHVzaCh0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJJbXBvcnREZWZhdWx0U3BlY2lmaWVyXCIpKTtcbiAgICBpZiAoIXRoaXMuZWF0KF90b2tlbnR5cGUudHlwZXMuY29tbWEpKSByZXR1cm4gbm9kZXM7XG4gIH1cbiAgaWYgKHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5zdGFyKSB7XG4gICAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICAgIHRoaXMubmV4dCgpO1xuICAgIHRoaXMuZXhwZWN0Q29udGV4dHVhbChcImFzXCIpO1xuICAgIG5vZGUubG9jYWwgPSB0aGlzLnBhcnNlSWRlbnQoKTtcbiAgICB0aGlzLmNoZWNrTFZhbChub2RlLmxvY2FsLCB0cnVlKTtcbiAgICBub2Rlcy5wdXNoKHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkltcG9ydE5hbWVzcGFjZVNwZWNpZmllclwiKSk7XG4gICAgcmV0dXJuIG5vZGVzO1xuICB9XG4gIHRoaXMuZXhwZWN0KF90b2tlbnR5cGUudHlwZXMuYnJhY2VMKTtcbiAgd2hpbGUgKCF0aGlzLmVhdChfdG9rZW50eXBlLnR5cGVzLmJyYWNlUikpIHtcbiAgICBpZiAoIWZpcnN0KSB7XG4gICAgICB0aGlzLmV4cGVjdChfdG9rZW50eXBlLnR5cGVzLmNvbW1hKTtcbiAgICAgIGlmICh0aGlzLmFmdGVyVHJhaWxpbmdDb21tYShfdG9rZW50eXBlLnR5cGVzLmJyYWNlUikpIGJyZWFrO1xuICAgIH0gZWxzZSBmaXJzdCA9IGZhbHNlO1xuXG4gICAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICAgIG5vZGUuaW1wb3J0ZWQgPSB0aGlzLnBhcnNlSWRlbnQodHJ1ZSk7XG4gICAgbm9kZS5sb2NhbCA9IHRoaXMuZWF0Q29udGV4dHVhbChcImFzXCIpID8gdGhpcy5wYXJzZUlkZW50KCkgOiBub2RlLmltcG9ydGVkO1xuICAgIHRoaXMuY2hlY2tMVmFsKG5vZGUubG9jYWwsIHRydWUpO1xuICAgIG5vZGVzLnB1c2godGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiSW1wb3J0U3BlY2lmaWVyXCIpKTtcbiAgfVxuICByZXR1cm4gbm9kZXM7XG59O1xuXG59LHtcIi4vc3RhdGVcIjoxMCxcIi4vdG9rZW50eXBlXCI6MTQsXCIuL3doaXRlc3BhY2VcIjoxNn1dLDEyOltmdW5jdGlvbihfZGVyZXFfLG1vZHVsZSxleHBvcnRzKXtcbi8vIFRoZSBhbGdvcml0aG0gdXNlZCB0byBkZXRlcm1pbmUgd2hldGhlciBhIHJlZ2V4cCBjYW4gYXBwZWFyIGF0IGFcbi8vIGdpdmVuIHBvaW50IGluIHRoZSBwcm9ncmFtIGlzIGxvb3NlbHkgYmFzZWQgb24gc3dlZXQuanMnIGFwcHJvYWNoLlxuLy8gU2VlIGh0dHBzOi8vZ2l0aHViLmNvbS9tb3ppbGxhL3N3ZWV0LmpzL3dpa2kvZGVzaWduXG5cblwidXNlIHN0cmljdFwiO1xuXG5leHBvcnRzLl9fZXNNb2R1bGUgPSB0cnVlO1xuXG5mdW5jdGlvbiBfY2xhc3NDYWxsQ2hlY2soaW5zdGFuY2UsIENvbnN0cnVjdG9yKSB7IGlmICghKGluc3RhbmNlIGluc3RhbmNlb2YgQ29uc3RydWN0b3IpKSB7IHRocm93IG5ldyBUeXBlRXJyb3IoXCJDYW5ub3QgY2FsbCBhIGNsYXNzIGFzIGEgZnVuY3Rpb25cIik7IH0gfVxuXG52YXIgX3N0YXRlID0gX2RlcmVxXyhcIi4vc3RhdGVcIik7XG5cbnZhciBfdG9rZW50eXBlID0gX2RlcmVxXyhcIi4vdG9rZW50eXBlXCIpO1xuXG52YXIgX3doaXRlc3BhY2UgPSBfZGVyZXFfKFwiLi93aGl0ZXNwYWNlXCIpO1xuXG52YXIgVG9rQ29udGV4dCA9IGZ1bmN0aW9uIFRva0NvbnRleHQodG9rZW4sIGlzRXhwciwgcHJlc2VydmVTcGFjZSwgb3ZlcnJpZGUpIHtcbiAgX2NsYXNzQ2FsbENoZWNrKHRoaXMsIFRva0NvbnRleHQpO1xuXG4gIHRoaXMudG9rZW4gPSB0b2tlbjtcbiAgdGhpcy5pc0V4cHIgPSAhIWlzRXhwcjtcbiAgdGhpcy5wcmVzZXJ2ZVNwYWNlID0gISFwcmVzZXJ2ZVNwYWNlO1xuICB0aGlzLm92ZXJyaWRlID0gb3ZlcnJpZGU7XG59O1xuXG5leHBvcnRzLlRva0NvbnRleHQgPSBUb2tDb250ZXh0O1xudmFyIHR5cGVzID0ge1xuICBiX3N0YXQ6IG5ldyBUb2tDb250ZXh0KFwie1wiLCBmYWxzZSksXG4gIGJfZXhwcjogbmV3IFRva0NvbnRleHQoXCJ7XCIsIHRydWUpLFxuICBiX3RtcGw6IG5ldyBUb2tDb250ZXh0KFwiJHtcIiwgdHJ1ZSksXG4gIHBfc3RhdDogbmV3IFRva0NvbnRleHQoXCIoXCIsIGZhbHNlKSxcbiAgcF9leHByOiBuZXcgVG9rQ29udGV4dChcIihcIiwgdHJ1ZSksXG4gIHFfdG1wbDogbmV3IFRva0NvbnRleHQoXCJgXCIsIHRydWUsIHRydWUsIGZ1bmN0aW9uIChwKSB7XG4gICAgcmV0dXJuIHAucmVhZFRtcGxUb2tlbigpO1xuICB9KSxcbiAgZl9leHByOiBuZXcgVG9rQ29udGV4dChcImZ1bmN0aW9uXCIsIHRydWUpXG59O1xuXG5leHBvcnRzLnR5cGVzID0gdHlwZXM7XG52YXIgcHAgPSBfc3RhdGUuUGFyc2VyLnByb3RvdHlwZTtcblxucHAuaW5pdGlhbENvbnRleHQgPSBmdW5jdGlvbiAoKSB7XG4gIHJldHVybiBbdHlwZXMuYl9zdGF0XTtcbn07XG5cbnBwLmJyYWNlSXNCbG9jayA9IGZ1bmN0aW9uIChwcmV2VHlwZSkge1xuICBpZiAocHJldlR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuY29sb24pIHtcbiAgICB2YXIgX3BhcmVudCA9IHRoaXMuY3VyQ29udGV4dCgpO1xuICAgIGlmIChfcGFyZW50ID09PSB0eXBlcy5iX3N0YXQgfHwgX3BhcmVudCA9PT0gdHlwZXMuYl9leHByKSByZXR1cm4gIV9wYXJlbnQuaXNFeHByO1xuICB9XG4gIGlmIChwcmV2VHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5fcmV0dXJuKSByZXR1cm4gX3doaXRlc3BhY2UubGluZUJyZWFrLnRlc3QodGhpcy5pbnB1dC5zbGljZSh0aGlzLmxhc3RUb2tFbmQsIHRoaXMuc3RhcnQpKTtcbiAgaWYgKHByZXZUeXBlID09PSBfdG9rZW50eXBlLnR5cGVzLl9lbHNlIHx8IHByZXZUeXBlID09PSBfdG9rZW50eXBlLnR5cGVzLnNlbWkgfHwgcHJldlR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuZW9mIHx8IHByZXZUeXBlID09PSBfdG9rZW50eXBlLnR5cGVzLnBhcmVuUikgcmV0dXJuIHRydWU7XG4gIGlmIChwcmV2VHlwZSA9PSBfdG9rZW50eXBlLnR5cGVzLmJyYWNlTCkgcmV0dXJuIHRoaXMuY3VyQ29udGV4dCgpID09PSB0eXBlcy5iX3N0YXQ7XG4gIHJldHVybiAhdGhpcy5leHByQWxsb3dlZDtcbn07XG5cbnBwLnVwZGF0ZUNvbnRleHQgPSBmdW5jdGlvbiAocHJldlR5cGUpIHtcbiAgdmFyIHVwZGF0ZSA9IHVuZGVmaW5lZCxcbiAgICAgIHR5cGUgPSB0aGlzLnR5cGU7XG4gIGlmICh0eXBlLmtleXdvcmQgJiYgcHJldlR5cGUgPT0gX3Rva2VudHlwZS50eXBlcy5kb3QpIHRoaXMuZXhwckFsbG93ZWQgPSBmYWxzZTtlbHNlIGlmICh1cGRhdGUgPSB0eXBlLnVwZGF0ZUNvbnRleHQpIHVwZGF0ZS5jYWxsKHRoaXMsIHByZXZUeXBlKTtlbHNlIHRoaXMuZXhwckFsbG93ZWQgPSB0eXBlLmJlZm9yZUV4cHI7XG59O1xuXG4vLyBUb2tlbi1zcGVjaWZpYyBjb250ZXh0IHVwZGF0ZSBjb2RlXG5cbl90b2tlbnR5cGUudHlwZXMucGFyZW5SLnVwZGF0ZUNvbnRleHQgPSBfdG9rZW50eXBlLnR5cGVzLmJyYWNlUi51cGRhdGVDb250ZXh0ID0gZnVuY3Rpb24gKCkge1xuICBpZiAodGhpcy5jb250ZXh0Lmxlbmd0aCA9PSAxKSB7XG4gICAgdGhpcy5leHByQWxsb3dlZCA9IHRydWU7XG4gICAgcmV0dXJuO1xuICB9XG4gIHZhciBvdXQgPSB0aGlzLmNvbnRleHQucG9wKCk7XG4gIGlmIChvdXQgPT09IHR5cGVzLmJfc3RhdCAmJiB0aGlzLmN1ckNvbnRleHQoKSA9PT0gdHlwZXMuZl9leHByKSB7XG4gICAgdGhpcy5jb250ZXh0LnBvcCgpO1xuICAgIHRoaXMuZXhwckFsbG93ZWQgPSBmYWxzZTtcbiAgfSBlbHNlIGlmIChvdXQgPT09IHR5cGVzLmJfdG1wbCkge1xuICAgIHRoaXMuZXhwckFsbG93ZWQgPSB0cnVlO1xuICB9IGVsc2Uge1xuICAgIHRoaXMuZXhwckFsbG93ZWQgPSAhb3V0LmlzRXhwcjtcbiAgfVxufTtcblxuX3Rva2VudHlwZS50eXBlcy5icmFjZUwudXBkYXRlQ29udGV4dCA9IGZ1bmN0aW9uIChwcmV2VHlwZSkge1xuICB0aGlzLmNvbnRleHQucHVzaCh0aGlzLmJyYWNlSXNCbG9jayhwcmV2VHlwZSkgPyB0eXBlcy5iX3N0YXQgOiB0eXBlcy5iX2V4cHIpO1xuICB0aGlzLmV4cHJBbGxvd2VkID0gdHJ1ZTtcbn07XG5cbl90b2tlbnR5cGUudHlwZXMuZG9sbGFyQnJhY2VMLnVwZGF0ZUNvbnRleHQgPSBmdW5jdGlvbiAoKSB7XG4gIHRoaXMuY29udGV4dC5wdXNoKHR5cGVzLmJfdG1wbCk7XG4gIHRoaXMuZXhwckFsbG93ZWQgPSB0cnVlO1xufTtcblxuX3Rva2VudHlwZS50eXBlcy5wYXJlbkwudXBkYXRlQ29udGV4dCA9IGZ1bmN0aW9uIChwcmV2VHlwZSkge1xuICB2YXIgc3RhdGVtZW50UGFyZW5zID0gcHJldlR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuX2lmIHx8IHByZXZUeXBlID09PSBfdG9rZW50eXBlLnR5cGVzLl9mb3IgfHwgcHJldlR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuX3dpdGggfHwgcHJldlR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuX3doaWxlO1xuICB0aGlzLmNvbnRleHQucHVzaChzdGF0ZW1lbnRQYXJlbnMgPyB0eXBlcy5wX3N0YXQgOiB0eXBlcy5wX2V4cHIpO1xuICB0aGlzLmV4cHJBbGxvd2VkID0gdHJ1ZTtcbn07XG5cbl90b2tlbnR5cGUudHlwZXMuaW5jRGVjLnVwZGF0ZUNvbnRleHQgPSBmdW5jdGlvbiAoKSB7XG4gIC8vIHRva0V4cHJBbGxvd2VkIHN0YXlzIHVuY2hhbmdlZFxufTtcblxuX3Rva2VudHlwZS50eXBlcy5fZnVuY3Rpb24udXBkYXRlQ29udGV4dCA9IGZ1bmN0aW9uICgpIHtcbiAgaWYgKHRoaXMuY3VyQ29udGV4dCgpICE9PSB0eXBlcy5iX3N0YXQpIHRoaXMuY29udGV4dC5wdXNoKHR5cGVzLmZfZXhwcik7XG4gIHRoaXMuZXhwckFsbG93ZWQgPSBmYWxzZTtcbn07XG5cbl90b2tlbnR5cGUudHlwZXMuYmFja1F1b3RlLnVwZGF0ZUNvbnRleHQgPSBmdW5jdGlvbiAoKSB7XG4gIGlmICh0aGlzLmN1ckNvbnRleHQoKSA9PT0gdHlwZXMucV90bXBsKSB0aGlzLmNvbnRleHQucG9wKCk7ZWxzZSB0aGlzLmNvbnRleHQucHVzaCh0eXBlcy5xX3RtcGwpO1xuICB0aGlzLmV4cHJBbGxvd2VkID0gZmFsc2U7XG59O1xuXG59LHtcIi4vc3RhdGVcIjoxMCxcIi4vdG9rZW50eXBlXCI6MTQsXCIuL3doaXRlc3BhY2VcIjoxNn1dLDEzOltmdW5jdGlvbihfZGVyZXFfLG1vZHVsZSxleHBvcnRzKXtcblwidXNlIHN0cmljdFwiO1xuXG5leHBvcnRzLl9fZXNNb2R1bGUgPSB0cnVlO1xuXG5mdW5jdGlvbiBfY2xhc3NDYWxsQ2hlY2soaW5zdGFuY2UsIENvbnN0cnVjdG9yKSB7IGlmICghKGluc3RhbmNlIGluc3RhbmNlb2YgQ29uc3RydWN0b3IpKSB7IHRocm93IG5ldyBUeXBlRXJyb3IoXCJDYW5ub3QgY2FsbCBhIGNsYXNzIGFzIGEgZnVuY3Rpb25cIik7IH0gfVxuXG52YXIgX2lkZW50aWZpZXIgPSBfZGVyZXFfKFwiLi9pZGVudGlmaWVyXCIpO1xuXG52YXIgX3Rva2VudHlwZSA9IF9kZXJlcV8oXCIuL3Rva2VudHlwZVwiKTtcblxudmFyIF9zdGF0ZSA9IF9kZXJlcV8oXCIuL3N0YXRlXCIpO1xuXG52YXIgX2xvY3V0aWwgPSBfZGVyZXFfKFwiLi9sb2N1dGlsXCIpO1xuXG52YXIgX3doaXRlc3BhY2UgPSBfZGVyZXFfKFwiLi93aGl0ZXNwYWNlXCIpO1xuXG4vLyBPYmplY3QgdHlwZSB1c2VkIHRvIHJlcHJlc2VudCB0b2tlbnMuIE5vdGUgdGhhdCBub3JtYWxseSwgdG9rZW5zXG4vLyBzaW1wbHkgZXhpc3QgYXMgcHJvcGVydGllcyBvbiB0aGUgcGFyc2VyIG9iamVjdC4gVGhpcyBpcyBvbmx5XG4vLyB1c2VkIGZvciB0aGUgb25Ub2tlbiBjYWxsYmFjayBhbmQgdGhlIGV4dGVybmFsIHRva2VuaXplci5cblxudmFyIFRva2VuID0gZnVuY3Rpb24gVG9rZW4ocCkge1xuICBfY2xhc3NDYWxsQ2hlY2sodGhpcywgVG9rZW4pO1xuXG4gIHRoaXMudHlwZSA9IHAudHlwZTtcbiAgdGhpcy52YWx1ZSA9IHAudmFsdWU7XG4gIHRoaXMuc3RhcnQgPSBwLnN0YXJ0O1xuICB0aGlzLmVuZCA9IHAuZW5kO1xuICBpZiAocC5vcHRpb25zLmxvY2F0aW9ucykgdGhpcy5sb2MgPSBuZXcgX2xvY3V0aWwuU291cmNlTG9jYXRpb24ocCwgcC5zdGFydExvYywgcC5lbmRMb2MpO1xuICBpZiAocC5vcHRpb25zLnJhbmdlcykgdGhpcy5yYW5nZSA9IFtwLnN0YXJ0LCBwLmVuZF07XG59XG5cbi8vICMjIFRva2VuaXplclxuXG47XG5cbmV4cG9ydHMuVG9rZW4gPSBUb2tlbjtcbnZhciBwcCA9IF9zdGF0ZS5QYXJzZXIucHJvdG90eXBlO1xuXG4vLyBBcmUgd2UgcnVubmluZyB1bmRlciBSaGlubz9cbnZhciBpc1JoaW5vID0gdHlwZW9mIFBhY2thZ2VzID09IFwib2JqZWN0XCIgJiYgT2JqZWN0LnByb3RvdHlwZS50b1N0cmluZy5jYWxsKFBhY2thZ2VzKSA9PSBcIltvYmplY3QgSmF2YVBhY2thZ2VdXCI7XG5cbi8vIE1vdmUgdG8gdGhlIG5leHQgdG9rZW5cblxucHAubmV4dCA9IGZ1bmN0aW9uICgpIHtcbiAgaWYgKHRoaXMub3B0aW9ucy5vblRva2VuKSB0aGlzLm9wdGlvbnMub25Ub2tlbihuZXcgVG9rZW4odGhpcykpO1xuXG4gIHRoaXMubGFzdFRva0VuZCA9IHRoaXMuZW5kO1xuICB0aGlzLmxhc3RUb2tTdGFydCA9IHRoaXMuc3RhcnQ7XG4gIHRoaXMubGFzdFRva0VuZExvYyA9IHRoaXMuZW5kTG9jO1xuICB0aGlzLmxhc3RUb2tTdGFydExvYyA9IHRoaXMuc3RhcnRMb2M7XG4gIHRoaXMubmV4dFRva2VuKCk7XG59O1xuXG5wcC5nZXRUb2tlbiA9IGZ1bmN0aW9uICgpIHtcbiAgdGhpcy5uZXh0KCk7XG4gIHJldHVybiBuZXcgVG9rZW4odGhpcyk7XG59O1xuXG4vLyBJZiB3ZSdyZSBpbiBhbiBFUzYgZW52aXJvbm1lbnQsIG1ha2UgcGFyc2VycyBpdGVyYWJsZVxuaWYgKHR5cGVvZiBTeW1ib2wgIT09IFwidW5kZWZpbmVkXCIpIHBwW1N5bWJvbC5pdGVyYXRvcl0gPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBzZWxmID0gdGhpcztcbiAgcmV0dXJuIHsgbmV4dDogZnVuY3Rpb24gbmV4dCgpIHtcbiAgICAgIHZhciB0b2tlbiA9IHNlbGYuZ2V0VG9rZW4oKTtcbiAgICAgIHJldHVybiB7XG4gICAgICAgIGRvbmU6IHRva2VuLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuZW9mLFxuICAgICAgICB2YWx1ZTogdG9rZW5cbiAgICAgIH07XG4gICAgfSB9O1xufTtcblxuLy8gVG9nZ2xlIHN0cmljdCBtb2RlLiBSZS1yZWFkcyB0aGUgbmV4dCBudW1iZXIgb3Igc3RyaW5nIHRvIHBsZWFzZVxuLy8gcGVkYW50aWMgdGVzdHMgKGBcInVzZSBzdHJpY3RcIjsgMDEwO2Agc2hvdWxkIGZhaWwpLlxuXG5wcC5zZXRTdHJpY3QgPSBmdW5jdGlvbiAoc3RyaWN0KSB7XG4gIHRoaXMuc3RyaWN0ID0gc3RyaWN0O1xuICBpZiAodGhpcy50eXBlICE9PSBfdG9rZW50eXBlLnR5cGVzLm51bSAmJiB0aGlzLnR5cGUgIT09IF90b2tlbnR5cGUudHlwZXMuc3RyaW5nKSByZXR1cm47XG4gIHRoaXMucG9zID0gdGhpcy5zdGFydDtcbiAgaWYgKHRoaXMub3B0aW9ucy5sb2NhdGlvbnMpIHtcbiAgICB3aGlsZSAodGhpcy5wb3MgPCB0aGlzLmxpbmVTdGFydCkge1xuICAgICAgdGhpcy5saW5lU3RhcnQgPSB0aGlzLmlucHV0Lmxhc3RJbmRleE9mKFwiXFxuXCIsIHRoaXMubGluZVN0YXJ0IC0gMikgKyAxO1xuICAgICAgLS10aGlzLmN1ckxpbmU7XG4gICAgfVxuICB9XG4gIHRoaXMubmV4dFRva2VuKCk7XG59O1xuXG5wcC5jdXJDb250ZXh0ID0gZnVuY3Rpb24gKCkge1xuICByZXR1cm4gdGhpcy5jb250ZXh0W3RoaXMuY29udGV4dC5sZW5ndGggLSAxXTtcbn07XG5cbi8vIFJlYWQgYSBzaW5nbGUgdG9rZW4sIHVwZGF0aW5nIHRoZSBwYXJzZXIgb2JqZWN0J3MgdG9rZW4tcmVsYXRlZFxuLy8gcHJvcGVydGllcy5cblxucHAubmV4dFRva2VuID0gZnVuY3Rpb24gKCkge1xuICB2YXIgY3VyQ29udGV4dCA9IHRoaXMuY3VyQ29udGV4dCgpO1xuICBpZiAoIWN1ckNvbnRleHQgfHwgIWN1ckNvbnRleHQucHJlc2VydmVTcGFjZSkgdGhpcy5za2lwU3BhY2UoKTtcblxuICB0aGlzLnN0YXJ0ID0gdGhpcy5wb3M7XG4gIGlmICh0aGlzLm9wdGlvbnMubG9jYXRpb25zKSB0aGlzLnN0YXJ0TG9jID0gdGhpcy5jdXJQb3NpdGlvbigpO1xuICBpZiAodGhpcy5wb3MgPj0gdGhpcy5pbnB1dC5sZW5ndGgpIHJldHVybiB0aGlzLmZpbmlzaFRva2VuKF90b2tlbnR5cGUudHlwZXMuZW9mKTtcblxuICBpZiAoY3VyQ29udGV4dC5vdmVycmlkZSkgcmV0dXJuIGN1ckNvbnRleHQub3ZlcnJpZGUodGhpcyk7ZWxzZSB0aGlzLnJlYWRUb2tlbih0aGlzLmZ1bGxDaGFyQ29kZUF0UG9zKCkpO1xufTtcblxucHAucmVhZFRva2VuID0gZnVuY3Rpb24gKGNvZGUpIHtcbiAgLy8gSWRlbnRpZmllciBvciBrZXl3b3JkLiAnXFx1WFhYWCcgc2VxdWVuY2VzIGFyZSBhbGxvd2VkIGluXG4gIC8vIGlkZW50aWZpZXJzLCBzbyAnXFwnIGFsc28gZGlzcGF0Y2hlcyB0byB0aGF0LlxuICBpZiAoX2lkZW50aWZpZXIuaXNJZGVudGlmaWVyU3RhcnQoY29kZSwgdGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYpIHx8IGNvZGUgPT09IDkyIC8qICdcXCcgKi8pIHJldHVybiB0aGlzLnJlYWRXb3JkKCk7XG5cbiAgcmV0dXJuIHRoaXMuZ2V0VG9rZW5Gcm9tQ29kZShjb2RlKTtcbn07XG5cbnBwLmZ1bGxDaGFyQ29kZUF0UG9zID0gZnVuY3Rpb24gKCkge1xuICB2YXIgY29kZSA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyk7XG4gIGlmIChjb2RlIDw9IDB4ZDdmZiB8fCBjb2RlID49IDB4ZTAwMCkgcmV0dXJuIGNvZGU7XG4gIHZhciBuZXh0ID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMSk7XG4gIHJldHVybiAoY29kZSA8PCAxMCkgKyBuZXh0IC0gMHgzNWZkYzAwO1xufTtcblxucHAuc2tpcEJsb2NrQ29tbWVudCA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIHN0YXJ0TG9jID0gdGhpcy5vcHRpb25zLm9uQ29tbWVudCAmJiB0aGlzLmN1clBvc2l0aW9uKCk7XG4gIHZhciBzdGFydCA9IHRoaXMucG9zLFxuICAgICAgZW5kID0gdGhpcy5pbnB1dC5pbmRleE9mKFwiKi9cIiwgdGhpcy5wb3MgKz0gMik7XG4gIGlmIChlbmQgPT09IC0xKSB0aGlzLnJhaXNlKHRoaXMucG9zIC0gMiwgXCJVbnRlcm1pbmF0ZWQgY29tbWVudFwiKTtcbiAgdGhpcy5wb3MgPSBlbmQgKyAyO1xuICBpZiAodGhpcy5vcHRpb25zLmxvY2F0aW9ucykge1xuICAgIF93aGl0ZXNwYWNlLmxpbmVCcmVha0cubGFzdEluZGV4ID0gc3RhcnQ7XG4gICAgdmFyIG1hdGNoID0gdW5kZWZpbmVkO1xuICAgIHdoaWxlICgobWF0Y2ggPSBfd2hpdGVzcGFjZS5saW5lQnJlYWtHLmV4ZWModGhpcy5pbnB1dCkpICYmIG1hdGNoLmluZGV4IDwgdGhpcy5wb3MpIHtcbiAgICAgICsrdGhpcy5jdXJMaW5lO1xuICAgICAgdGhpcy5saW5lU3RhcnQgPSBtYXRjaC5pbmRleCArIG1hdGNoWzBdLmxlbmd0aDtcbiAgICB9XG4gIH1cbiAgaWYgKHRoaXMub3B0aW9ucy5vbkNvbW1lbnQpIHRoaXMub3B0aW9ucy5vbkNvbW1lbnQodHJ1ZSwgdGhpcy5pbnB1dC5zbGljZShzdGFydCArIDIsIGVuZCksIHN0YXJ0LCB0aGlzLnBvcywgc3RhcnRMb2MsIHRoaXMuY3VyUG9zaXRpb24oKSk7XG59O1xuXG5wcC5za2lwTGluZUNvbW1lbnQgPSBmdW5jdGlvbiAoc3RhcnRTa2lwKSB7XG4gIHZhciBzdGFydCA9IHRoaXMucG9zO1xuICB2YXIgc3RhcnRMb2MgPSB0aGlzLm9wdGlvbnMub25Db21tZW50ICYmIHRoaXMuY3VyUG9zaXRpb24oKTtcbiAgdmFyIGNoID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICs9IHN0YXJ0U2tpcCk7XG4gIHdoaWxlICh0aGlzLnBvcyA8IHRoaXMuaW5wdXQubGVuZ3RoICYmIGNoICE9PSAxMCAmJiBjaCAhPT0gMTMgJiYgY2ggIT09IDgyMzIgJiYgY2ggIT09IDgyMzMpIHtcbiAgICArK3RoaXMucG9zO1xuICAgIGNoID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zKTtcbiAgfVxuICBpZiAodGhpcy5vcHRpb25zLm9uQ29tbWVudCkgdGhpcy5vcHRpb25zLm9uQ29tbWVudChmYWxzZSwgdGhpcy5pbnB1dC5zbGljZShzdGFydCArIHN0YXJ0U2tpcCwgdGhpcy5wb3MpLCBzdGFydCwgdGhpcy5wb3MsIHN0YXJ0TG9jLCB0aGlzLmN1clBvc2l0aW9uKCkpO1xufTtcblxuLy8gQ2FsbGVkIGF0IHRoZSBzdGFydCBvZiB0aGUgcGFyc2UgYW5kIGFmdGVyIGV2ZXJ5IHRva2VuLiBTa2lwc1xuLy8gd2hpdGVzcGFjZSBhbmQgY29tbWVudHMsIGFuZC5cblxucHAuc2tpcFNwYWNlID0gZnVuY3Rpb24gKCkge1xuICBsb29wOiB3aGlsZSAodGhpcy5wb3MgPCB0aGlzLmlucHV0Lmxlbmd0aCkge1xuICAgIHZhciBjaCA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyk7XG4gICAgc3dpdGNoIChjaCkge1xuICAgICAgY2FzZSAzMjpjYXNlIDE2MDpcbiAgICAgICAgLy8gJyAnXG4gICAgICAgICsrdGhpcy5wb3M7XG4gICAgICAgIGJyZWFrO1xuICAgICAgY2FzZSAxMzpcbiAgICAgICAgaWYgKHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIDEpID09PSAxMCkge1xuICAgICAgICAgICsrdGhpcy5wb3M7XG4gICAgICAgIH1cbiAgICAgIGNhc2UgMTA6Y2FzZSA4MjMyOmNhc2UgODIzMzpcbiAgICAgICAgKyt0aGlzLnBvcztcbiAgICAgICAgaWYgKHRoaXMub3B0aW9ucy5sb2NhdGlvbnMpIHtcbiAgICAgICAgICArK3RoaXMuY3VyTGluZTtcbiAgICAgICAgICB0aGlzLmxpbmVTdGFydCA9IHRoaXMucG9zO1xuICAgICAgICB9XG4gICAgICAgIGJyZWFrO1xuICAgICAgY2FzZSA0NzpcbiAgICAgICAgLy8gJy8nXG4gICAgICAgIHN3aXRjaCAodGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMSkpIHtcbiAgICAgICAgICBjYXNlIDQyOlxuICAgICAgICAgICAgLy8gJyonXG4gICAgICAgICAgICB0aGlzLnNraXBCbG9ja0NvbW1lbnQoKTtcbiAgICAgICAgICAgIGJyZWFrO1xuICAgICAgICAgIGNhc2UgNDc6XG4gICAgICAgICAgICB0aGlzLnNraXBMaW5lQ29tbWVudCgyKTtcbiAgICAgICAgICAgIGJyZWFrO1xuICAgICAgICAgIGRlZmF1bHQ6XG4gICAgICAgICAgICBicmVhayBsb29wO1xuICAgICAgICB9XG4gICAgICAgIGJyZWFrO1xuICAgICAgZGVmYXVsdDpcbiAgICAgICAgaWYgKGNoID4gOCAmJiBjaCA8IDE0IHx8IGNoID49IDU3NjAgJiYgX3doaXRlc3BhY2Uubm9uQVNDSUl3aGl0ZXNwYWNlLnRlc3QoU3RyaW5nLmZyb21DaGFyQ29kZShjaCkpKSB7XG4gICAgICAgICAgKyt0aGlzLnBvcztcbiAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICBicmVhayBsb29wO1xuICAgICAgICB9XG4gICAgfVxuICB9XG59O1xuXG4vLyBDYWxsZWQgYXQgdGhlIGVuZCBvZiBldmVyeSB0b2tlbi4gU2V0cyBgZW5kYCwgYHZhbGAsIGFuZFxuLy8gbWFpbnRhaW5zIGBjb250ZXh0YCBhbmQgYGV4cHJBbGxvd2VkYCwgYW5kIHNraXBzIHRoZSBzcGFjZSBhZnRlclxuLy8gdGhlIHRva2VuLCBzbyB0aGF0IHRoZSBuZXh0IG9uZSdzIGBzdGFydGAgd2lsbCBwb2ludCBhdCB0aGVcbi8vIHJpZ2h0IHBvc2l0aW9uLlxuXG5wcC5maW5pc2hUb2tlbiA9IGZ1bmN0aW9uICh0eXBlLCB2YWwpIHtcbiAgdGhpcy5lbmQgPSB0aGlzLnBvcztcbiAgaWYgKHRoaXMub3B0aW9ucy5sb2NhdGlvbnMpIHRoaXMuZW5kTG9jID0gdGhpcy5jdXJQb3NpdGlvbigpO1xuICB2YXIgcHJldlR5cGUgPSB0aGlzLnR5cGU7XG4gIHRoaXMudHlwZSA9IHR5cGU7XG4gIHRoaXMudmFsdWUgPSB2YWw7XG5cbiAgdGhpcy51cGRhdGVDb250ZXh0KHByZXZUeXBlKTtcbn07XG5cbi8vICMjIyBUb2tlbiByZWFkaW5nXG5cbi8vIFRoaXMgaXMgdGhlIGZ1bmN0aW9uIHRoYXQgaXMgY2FsbGVkIHRvIGZldGNoIHRoZSBuZXh0IHRva2VuLiBJdFxuLy8gaXMgc29tZXdoYXQgb2JzY3VyZSwgYmVjYXVzZSBpdCB3b3JrcyBpbiBjaGFyYWN0ZXIgY29kZXMgcmF0aGVyXG4vLyB0aGFuIGNoYXJhY3RlcnMsIGFuZCBiZWNhdXNlIG9wZXJhdG9yIHBhcnNpbmcgaGFzIGJlZW4gaW5saW5lZFxuLy8gaW50byBpdC5cbi8vXG4vLyBBbGwgaW4gdGhlIG5hbWUgb2Ygc3BlZWQuXG4vL1xucHAucmVhZFRva2VuX2RvdCA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIG5leHQgPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAxKTtcbiAgaWYgKG5leHQgPj0gNDggJiYgbmV4dCA8PSA1NykgcmV0dXJuIHRoaXMucmVhZE51bWJlcih0cnVlKTtcbiAgdmFyIG5leHQyID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMik7XG4gIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNiAmJiBuZXh0ID09PSA0NiAmJiBuZXh0MiA9PT0gNDYpIHtcbiAgICAvLyA0NiA9IGRvdCAnLidcbiAgICB0aGlzLnBvcyArPSAzO1xuICAgIHJldHVybiB0aGlzLmZpbmlzaFRva2VuKF90b2tlbnR5cGUudHlwZXMuZWxsaXBzaXMpO1xuICB9IGVsc2Uge1xuICAgICsrdGhpcy5wb3M7XG4gICAgcmV0dXJuIHRoaXMuZmluaXNoVG9rZW4oX3Rva2VudHlwZS50eXBlcy5kb3QpO1xuICB9XG59O1xuXG5wcC5yZWFkVG9rZW5fc2xhc2ggPSBmdW5jdGlvbiAoKSB7XG4gIC8vICcvJ1xuICB2YXIgbmV4dCA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIDEpO1xuICBpZiAodGhpcy5leHByQWxsb3dlZCkge1xuICAgICsrdGhpcy5wb3M7cmV0dXJuIHRoaXMucmVhZFJlZ2V4cCgpO1xuICB9XG4gIGlmIChuZXh0ID09PSA2MSkgcmV0dXJuIHRoaXMuZmluaXNoT3AoX3Rva2VudHlwZS50eXBlcy5hc3NpZ24sIDIpO1xuICByZXR1cm4gdGhpcy5maW5pc2hPcChfdG9rZW50eXBlLnR5cGVzLnNsYXNoLCAxKTtcbn07XG5cbnBwLnJlYWRUb2tlbl9tdWx0X21vZHVsbyA9IGZ1bmN0aW9uIChjb2RlKSB7XG4gIC8vICclKidcbiAgdmFyIG5leHQgPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAxKTtcbiAgaWYgKG5leHQgPT09IDYxKSByZXR1cm4gdGhpcy5maW5pc2hPcChfdG9rZW50eXBlLnR5cGVzLmFzc2lnbiwgMik7XG4gIHJldHVybiB0aGlzLmZpbmlzaE9wKGNvZGUgPT09IDQyID8gX3Rva2VudHlwZS50eXBlcy5zdGFyIDogX3Rva2VudHlwZS50eXBlcy5tb2R1bG8sIDEpO1xufTtcblxucHAucmVhZFRva2VuX3BpcGVfYW1wID0gZnVuY3Rpb24gKGNvZGUpIHtcbiAgLy8gJ3wmJ1xuICB2YXIgbmV4dCA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIDEpO1xuICBpZiAobmV4dCA9PT0gY29kZSkgcmV0dXJuIHRoaXMuZmluaXNoT3AoY29kZSA9PT0gMTI0ID8gX3Rva2VudHlwZS50eXBlcy5sb2dpY2FsT1IgOiBfdG9rZW50eXBlLnR5cGVzLmxvZ2ljYWxBTkQsIDIpO1xuICBpZiAobmV4dCA9PT0gNjEpIHJldHVybiB0aGlzLmZpbmlzaE9wKF90b2tlbnR5cGUudHlwZXMuYXNzaWduLCAyKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoT3AoY29kZSA9PT0gMTI0ID8gX3Rva2VudHlwZS50eXBlcy5iaXR3aXNlT1IgOiBfdG9rZW50eXBlLnR5cGVzLmJpdHdpc2VBTkQsIDEpO1xufTtcblxucHAucmVhZFRva2VuX2NhcmV0ID0gZnVuY3Rpb24gKCkge1xuICAvLyAnXidcbiAgdmFyIG5leHQgPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAxKTtcbiAgaWYgKG5leHQgPT09IDYxKSByZXR1cm4gdGhpcy5maW5pc2hPcChfdG9rZW50eXBlLnR5cGVzLmFzc2lnbiwgMik7XG4gIHJldHVybiB0aGlzLmZpbmlzaE9wKF90b2tlbnR5cGUudHlwZXMuYml0d2lzZVhPUiwgMSk7XG59O1xuXG5wcC5yZWFkVG9rZW5fcGx1c19taW4gPSBmdW5jdGlvbiAoY29kZSkge1xuICAvLyAnKy0nXG4gIHZhciBuZXh0ID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMSk7XG4gIGlmIChuZXh0ID09PSBjb2RlKSB7XG4gICAgaWYgKG5leHQgPT0gNDUgJiYgdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMikgPT0gNjIgJiYgX3doaXRlc3BhY2UubGluZUJyZWFrLnRlc3QodGhpcy5pbnB1dC5zbGljZSh0aGlzLmxhc3RUb2tFbmQsIHRoaXMucG9zKSkpIHtcbiAgICAgIC8vIEEgYC0tPmAgbGluZSBjb21tZW50XG4gICAgICB0aGlzLnNraXBMaW5lQ29tbWVudCgzKTtcbiAgICAgIHRoaXMuc2tpcFNwYWNlKCk7XG4gICAgICByZXR1cm4gdGhpcy5uZXh0VG9rZW4oKTtcbiAgICB9XG4gICAgcmV0dXJuIHRoaXMuZmluaXNoT3AoX3Rva2VudHlwZS50eXBlcy5pbmNEZWMsIDIpO1xuICB9XG4gIGlmIChuZXh0ID09PSA2MSkgcmV0dXJuIHRoaXMuZmluaXNoT3AoX3Rva2VudHlwZS50eXBlcy5hc3NpZ24sIDIpO1xuICByZXR1cm4gdGhpcy5maW5pc2hPcChfdG9rZW50eXBlLnR5cGVzLnBsdXNNaW4sIDEpO1xufTtcblxucHAucmVhZFRva2VuX2x0X2d0ID0gZnVuY3Rpb24gKGNvZGUpIHtcbiAgLy8gJzw+J1xuICB2YXIgbmV4dCA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIDEpO1xuICB2YXIgc2l6ZSA9IDE7XG4gIGlmIChuZXh0ID09PSBjb2RlKSB7XG4gICAgc2l6ZSA9IGNvZGUgPT09IDYyICYmIHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIDIpID09PSA2MiA/IDMgOiAyO1xuICAgIGlmICh0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyBzaXplKSA9PT0gNjEpIHJldHVybiB0aGlzLmZpbmlzaE9wKF90b2tlbnR5cGUudHlwZXMuYXNzaWduLCBzaXplICsgMSk7XG4gICAgcmV0dXJuIHRoaXMuZmluaXNoT3AoX3Rva2VudHlwZS50eXBlcy5iaXRTaGlmdCwgc2l6ZSk7XG4gIH1cbiAgaWYgKG5leHQgPT0gMzMgJiYgY29kZSA9PSA2MCAmJiB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAyKSA9PSA0NSAmJiB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAzKSA9PSA0NSkge1xuICAgIGlmICh0aGlzLmluTW9kdWxlKSB0aGlzLnVuZXhwZWN0ZWQoKTtcbiAgICAvLyBgPCEtLWAsIGFuIFhNTC1zdHlsZSBjb21tZW50IHRoYXQgc2hvdWxkIGJlIGludGVycHJldGVkIGFzIGEgbGluZSBjb21tZW50XG4gICAgdGhpcy5za2lwTGluZUNvbW1lbnQoNCk7XG4gICAgdGhpcy5za2lwU3BhY2UoKTtcbiAgICByZXR1cm4gdGhpcy5uZXh0VG9rZW4oKTtcbiAgfVxuICBpZiAobmV4dCA9PT0gNjEpIHNpemUgPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAyKSA9PT0gNjEgPyAzIDogMjtcbiAgcmV0dXJuIHRoaXMuZmluaXNoT3AoX3Rva2VudHlwZS50eXBlcy5yZWxhdGlvbmFsLCBzaXplKTtcbn07XG5cbnBwLnJlYWRUb2tlbl9lcV9leGNsID0gZnVuY3Rpb24gKGNvZGUpIHtcbiAgLy8gJz0hJ1xuICB2YXIgbmV4dCA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIDEpO1xuICBpZiAobmV4dCA9PT0gNjEpIHJldHVybiB0aGlzLmZpbmlzaE9wKF90b2tlbnR5cGUudHlwZXMuZXF1YWxpdHksIHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIDIpID09PSA2MSA/IDMgOiAyKTtcbiAgaWYgKGNvZGUgPT09IDYxICYmIG5leHQgPT09IDYyICYmIHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KSB7XG4gICAgLy8gJz0+J1xuICAgIHRoaXMucG9zICs9IDI7XG4gICAgcmV0dXJuIHRoaXMuZmluaXNoVG9rZW4oX3Rva2VudHlwZS50eXBlcy5hcnJvdyk7XG4gIH1cbiAgcmV0dXJuIHRoaXMuZmluaXNoT3AoY29kZSA9PT0gNjEgPyBfdG9rZW50eXBlLnR5cGVzLmVxIDogX3Rva2VudHlwZS50eXBlcy5wcmVmaXgsIDEpO1xufTtcblxucHAuZ2V0VG9rZW5Gcm9tQ29kZSA9IGZ1bmN0aW9uIChjb2RlKSB7XG4gIHN3aXRjaCAoY29kZSkge1xuICAgIC8vIFRoZSBpbnRlcnByZXRhdGlvbiBvZiBhIGRvdCBkZXBlbmRzIG9uIHdoZXRoZXIgaXQgaXMgZm9sbG93ZWRcbiAgICAvLyBieSBhIGRpZ2l0IG9yIGFub3RoZXIgdHdvIGRvdHMuXG4gICAgY2FzZSA0NjpcbiAgICAgIC8vICcuJ1xuICAgICAgcmV0dXJuIHRoaXMucmVhZFRva2VuX2RvdCgpO1xuXG4gICAgLy8gUHVuY3R1YXRpb24gdG9rZW5zLlxuICAgIGNhc2UgNDA6XG4gICAgICArK3RoaXMucG9zO3JldHVybiB0aGlzLmZpbmlzaFRva2VuKF90b2tlbnR5cGUudHlwZXMucGFyZW5MKTtcbiAgICBjYXNlIDQxOlxuICAgICAgKyt0aGlzLnBvcztyZXR1cm4gdGhpcy5maW5pc2hUb2tlbihfdG9rZW50eXBlLnR5cGVzLnBhcmVuUik7XG4gICAgY2FzZSA1OTpcbiAgICAgICsrdGhpcy5wb3M7cmV0dXJuIHRoaXMuZmluaXNoVG9rZW4oX3Rva2VudHlwZS50eXBlcy5zZW1pKTtcbiAgICBjYXNlIDQ0OlxuICAgICAgKyt0aGlzLnBvcztyZXR1cm4gdGhpcy5maW5pc2hUb2tlbihfdG9rZW50eXBlLnR5cGVzLmNvbW1hKTtcbiAgICBjYXNlIDkxOlxuICAgICAgKyt0aGlzLnBvcztyZXR1cm4gdGhpcy5maW5pc2hUb2tlbihfdG9rZW50eXBlLnR5cGVzLmJyYWNrZXRMKTtcbiAgICBjYXNlIDkzOlxuICAgICAgKyt0aGlzLnBvcztyZXR1cm4gdGhpcy5maW5pc2hUb2tlbihfdG9rZW50eXBlLnR5cGVzLmJyYWNrZXRSKTtcbiAgICBjYXNlIDEyMzpcbiAgICAgICsrdGhpcy5wb3M7cmV0dXJuIHRoaXMuZmluaXNoVG9rZW4oX3Rva2VudHlwZS50eXBlcy5icmFjZUwpO1xuICAgIGNhc2UgMTI1OlxuICAgICAgKyt0aGlzLnBvcztyZXR1cm4gdGhpcy5maW5pc2hUb2tlbihfdG9rZW50eXBlLnR5cGVzLmJyYWNlUik7XG4gICAgY2FzZSA1ODpcbiAgICAgICsrdGhpcy5wb3M7cmV0dXJuIHRoaXMuZmluaXNoVG9rZW4oX3Rva2VudHlwZS50eXBlcy5jb2xvbik7XG4gICAgY2FzZSA2MzpcbiAgICAgICsrdGhpcy5wb3M7cmV0dXJuIHRoaXMuZmluaXNoVG9rZW4oX3Rva2VudHlwZS50eXBlcy5xdWVzdGlvbik7XG5cbiAgICBjYXNlIDk2OlxuICAgICAgLy8gJ2AnXG4gICAgICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uIDwgNikgYnJlYWs7XG4gICAgICArK3RoaXMucG9zO1xuICAgICAgcmV0dXJuIHRoaXMuZmluaXNoVG9rZW4oX3Rva2VudHlwZS50eXBlcy5iYWNrUXVvdGUpO1xuXG4gICAgY2FzZSA0ODpcbiAgICAgIC8vICcwJ1xuICAgICAgdmFyIG5leHQgPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAxKTtcbiAgICAgIGlmIChuZXh0ID09PSAxMjAgfHwgbmV4dCA9PT0gODgpIHJldHVybiB0aGlzLnJlYWRSYWRpeE51bWJlcigxNik7IC8vICcweCcsICcwWCcgLSBoZXggbnVtYmVyXG4gICAgICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYpIHtcbiAgICAgICAgaWYgKG5leHQgPT09IDExMSB8fCBuZXh0ID09PSA3OSkgcmV0dXJuIHRoaXMucmVhZFJhZGl4TnVtYmVyKDgpOyAvLyAnMG8nLCAnME8nIC0gb2N0YWwgbnVtYmVyXG4gICAgICAgIGlmIChuZXh0ID09PSA5OCB8fCBuZXh0ID09PSA2NikgcmV0dXJuIHRoaXMucmVhZFJhZGl4TnVtYmVyKDIpOyAvLyAnMGInLCAnMEInIC0gYmluYXJ5IG51bWJlclxuICAgICAgfVxuICAgIC8vIEFueXRoaW5nIGVsc2UgYmVnaW5uaW5nIHdpdGggYSBkaWdpdCBpcyBhbiBpbnRlZ2VyLCBvY3RhbFxuICAgIC8vIG51bWJlciwgb3IgZmxvYXQuXG4gICAgY2FzZSA0OTpjYXNlIDUwOmNhc2UgNTE6Y2FzZSA1MjpjYXNlIDUzOmNhc2UgNTQ6Y2FzZSA1NTpjYXNlIDU2OmNhc2UgNTc6XG4gICAgICAvLyAxLTlcbiAgICAgIHJldHVybiB0aGlzLnJlYWROdW1iZXIoZmFsc2UpO1xuXG4gICAgLy8gUXVvdGVzIHByb2R1Y2Ugc3RyaW5ncy5cbiAgICBjYXNlIDM0OmNhc2UgMzk6XG4gICAgICAvLyAnXCInLCBcIidcIlxuICAgICAgcmV0dXJuIHRoaXMucmVhZFN0cmluZyhjb2RlKTtcblxuICAgIC8vIE9wZXJhdG9ycyBhcmUgcGFyc2VkIGlubGluZSBpbiB0aW55IHN0YXRlIG1hY2hpbmVzLiAnPScgKDYxKSBpc1xuICAgIC8vIG9mdGVuIHJlZmVycmVkIHRvLiBgZmluaXNoT3BgIHNpbXBseSBza2lwcyB0aGUgYW1vdW50IG9mXG4gICAgLy8gY2hhcmFjdGVycyBpdCBpcyBnaXZlbiBhcyBzZWNvbmQgYXJndW1lbnQsIGFuZCByZXR1cm5zIGEgdG9rZW5cbiAgICAvLyBvZiB0aGUgdHlwZSBnaXZlbiBieSBpdHMgZmlyc3QgYXJndW1lbnQuXG5cbiAgICBjYXNlIDQ3OlxuICAgICAgLy8gJy8nXG4gICAgICByZXR1cm4gdGhpcy5yZWFkVG9rZW5fc2xhc2goKTtcblxuICAgIGNhc2UgMzc6Y2FzZSA0MjpcbiAgICAgIC8vICclKidcbiAgICAgIHJldHVybiB0aGlzLnJlYWRUb2tlbl9tdWx0X21vZHVsbyhjb2RlKTtcblxuICAgIGNhc2UgMTI0OmNhc2UgMzg6XG4gICAgICAvLyAnfCYnXG4gICAgICByZXR1cm4gdGhpcy5yZWFkVG9rZW5fcGlwZV9hbXAoY29kZSk7XG5cbiAgICBjYXNlIDk0OlxuICAgICAgLy8gJ14nXG4gICAgICByZXR1cm4gdGhpcy5yZWFkVG9rZW5fY2FyZXQoKTtcblxuICAgIGNhc2UgNDM6Y2FzZSA0NTpcbiAgICAgIC8vICcrLSdcbiAgICAgIHJldHVybiB0aGlzLnJlYWRUb2tlbl9wbHVzX21pbihjb2RlKTtcblxuICAgIGNhc2UgNjA6Y2FzZSA2MjpcbiAgICAgIC8vICc8PidcbiAgICAgIHJldHVybiB0aGlzLnJlYWRUb2tlbl9sdF9ndChjb2RlKTtcblxuICAgIGNhc2UgNjE6Y2FzZSAzMzpcbiAgICAgIC8vICc9ISdcbiAgICAgIHJldHVybiB0aGlzLnJlYWRUb2tlbl9lcV9leGNsKGNvZGUpO1xuXG4gICAgY2FzZSAxMjY6XG4gICAgICAvLyAnfidcbiAgICAgIHJldHVybiB0aGlzLmZpbmlzaE9wKF90b2tlbnR5cGUudHlwZXMucHJlZml4LCAxKTtcbiAgfVxuXG4gIHRoaXMucmFpc2UodGhpcy5wb3MsIFwiVW5leHBlY3RlZCBjaGFyYWN0ZXIgJ1wiICsgY29kZVBvaW50VG9TdHJpbmcoY29kZSkgKyBcIidcIik7XG59O1xuXG5wcC5maW5pc2hPcCA9IGZ1bmN0aW9uICh0eXBlLCBzaXplKSB7XG4gIHZhciBzdHIgPSB0aGlzLmlucHV0LnNsaWNlKHRoaXMucG9zLCB0aGlzLnBvcyArIHNpemUpO1xuICB0aGlzLnBvcyArPSBzaXplO1xuICByZXR1cm4gdGhpcy5maW5pc2hUb2tlbih0eXBlLCBzdHIpO1xufTtcblxuLy8gUGFyc2UgYSByZWd1bGFyIGV4cHJlc3Npb24uIFNvbWUgY29udGV4dC1hd2FyZW5lc3MgaXMgbmVjZXNzYXJ5LFxuLy8gc2luY2UgYSAnLycgaW5zaWRlIGEgJ1tdJyBzZXQgZG9lcyBub3QgZW5kIHRoZSBleHByZXNzaW9uLlxuXG5mdW5jdGlvbiB0cnlDcmVhdGVSZWdleHAoc3JjLCBmbGFncywgdGhyb3dFcnJvckF0KSB7XG4gIHRyeSB7XG4gICAgcmV0dXJuIG5ldyBSZWdFeHAoc3JjLCBmbGFncyk7XG4gIH0gY2F0Y2ggKGUpIHtcbiAgICBpZiAodGhyb3dFcnJvckF0ICE9PSB1bmRlZmluZWQpIHtcbiAgICAgIGlmIChlIGluc3RhbmNlb2YgU3ludGF4RXJyb3IpIHRoaXMucmFpc2UodGhyb3dFcnJvckF0LCBcIkVycm9yIHBhcnNpbmcgcmVndWxhciBleHByZXNzaW9uOiBcIiArIGUubWVzc2FnZSk7XG4gICAgICB0aGlzLnJhaXNlKGUpO1xuICAgIH1cbiAgfVxufVxuXG52YXIgcmVnZXhwVW5pY29kZVN1cHBvcnQgPSAhIXRyeUNyZWF0ZVJlZ2V4cChcIu+/v1wiLCBcInVcIik7XG5cbnBwLnJlYWRSZWdleHAgPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBfdGhpcyA9IHRoaXM7XG5cbiAgdmFyIGVzY2FwZWQgPSB1bmRlZmluZWQsXG4gICAgICBpbkNsYXNzID0gdW5kZWZpbmVkLFxuICAgICAgc3RhcnQgPSB0aGlzLnBvcztcbiAgZm9yICg7Oykge1xuICAgIGlmICh0aGlzLnBvcyA+PSB0aGlzLmlucHV0Lmxlbmd0aCkgdGhpcy5yYWlzZShzdGFydCwgXCJVbnRlcm1pbmF0ZWQgcmVndWxhciBleHByZXNzaW9uXCIpO1xuICAgIHZhciBjaCA9IHRoaXMuaW5wdXQuY2hhckF0KHRoaXMucG9zKTtcbiAgICBpZiAoX3doaXRlc3BhY2UubGluZUJyZWFrLnRlc3QoY2gpKSB0aGlzLnJhaXNlKHN0YXJ0LCBcIlVudGVybWluYXRlZCByZWd1bGFyIGV4cHJlc3Npb25cIik7XG4gICAgaWYgKCFlc2NhcGVkKSB7XG4gICAgICBpZiAoY2ggPT09IFwiW1wiKSBpbkNsYXNzID0gdHJ1ZTtlbHNlIGlmIChjaCA9PT0gXCJdXCIgJiYgaW5DbGFzcykgaW5DbGFzcyA9IGZhbHNlO2Vsc2UgaWYgKGNoID09PSBcIi9cIiAmJiAhaW5DbGFzcykgYnJlYWs7XG4gICAgICBlc2NhcGVkID0gY2ggPT09IFwiXFxcXFwiO1xuICAgIH0gZWxzZSBlc2NhcGVkID0gZmFsc2U7XG4gICAgKyt0aGlzLnBvcztcbiAgfVxuICB2YXIgY29udGVudCA9IHRoaXMuaW5wdXQuc2xpY2Uoc3RhcnQsIHRoaXMucG9zKTtcbiAgKyt0aGlzLnBvcztcbiAgLy8gTmVlZCB0byB1c2UgYHJlYWRXb3JkMWAgYmVjYXVzZSAnXFx1WFhYWCcgc2VxdWVuY2VzIGFyZSBhbGxvd2VkXG4gIC8vIGhlcmUgKGRvbid0IGFzaykuXG4gIHZhciBtb2RzID0gdGhpcy5yZWFkV29yZDEoKTtcbiAgdmFyIHRtcCA9IGNvbnRlbnQ7XG4gIGlmIChtb2RzKSB7XG4gICAgdmFyIHZhbGlkRmxhZ3MgPSAvXltnbXNpeV0qJC87XG4gICAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KSB2YWxpZEZsYWdzID0gL15bZ21zaXl1XSokLztcbiAgICBpZiAoIXZhbGlkRmxhZ3MudGVzdChtb2RzKSkgdGhpcy5yYWlzZShzdGFydCwgXCJJbnZhbGlkIHJlZ3VsYXIgZXhwcmVzc2lvbiBmbGFnXCIpO1xuICAgIGlmIChtb2RzLmluZGV4T2YoJ3UnKSA+PSAwICYmICFyZWdleHBVbmljb2RlU3VwcG9ydCkge1xuICAgICAgLy8gUmVwbGFjZSBlYWNoIGFzdHJhbCBzeW1ib2wgYW5kIGV2ZXJ5IFVuaWNvZGUgZXNjYXBlIHNlcXVlbmNlIHRoYXRcbiAgICAgIC8vIHBvc3NpYmx5IHJlcHJlc2VudHMgYW4gYXN0cmFsIHN5bWJvbCBvciBhIHBhaXJlZCBzdXJyb2dhdGUgd2l0aCBhXG4gICAgICAvLyBzaW5nbGUgQVNDSUkgc3ltYm9sIHRvIGF2b2lkIHRocm93aW5nIG9uIHJlZ3VsYXIgZXhwcmVzc2lvbnMgdGhhdFxuICAgICAgLy8gYXJlIG9ubHkgdmFsaWQgaW4gY29tYmluYXRpb24gd2l0aCB0aGUgYC91YCBmbGFnLlxuICAgICAgLy8gTm90ZTogcmVwbGFjaW5nIHdpdGggdGhlIEFTQ0lJIHN5bWJvbCBgeGAgbWlnaHQgY2F1c2UgZmFsc2VcbiAgICAgIC8vIG5lZ2F0aXZlcyBpbiB1bmxpa2VseSBzY2VuYXJpb3MuIEZvciBleGFtcGxlLCBgW1xcdXs2MX0tYl1gIGlzIGFcbiAgICAgIC8vIHBlcmZlY3RseSB2YWxpZCBwYXR0ZXJuIHRoYXQgaXMgZXF1aXZhbGVudCB0byBgW2EtYl1gLCBidXQgaXQgd291bGRcbiAgICAgIC8vIGJlIHJlcGxhY2VkIGJ5IGBbeC1iXWAgd2hpY2ggdGhyb3dzIGFuIGVycm9yLlxuICAgICAgdG1wID0gdG1wLnJlcGxhY2UoL1xcXFx1XFx7KFswLTlhLWZBLUZdKylcXH0vZywgZnVuY3Rpb24gKG1hdGNoLCBjb2RlLCBvZmZzZXQpIHtcbiAgICAgICAgY29kZSA9IE51bWJlcihcIjB4XCIgKyBjb2RlKTtcbiAgICAgICAgaWYgKGNvZGUgPiAweDEwRkZGRikgX3RoaXMucmFpc2Uoc3RhcnQgKyBvZmZzZXQgKyAzLCBcIkNvZGUgcG9pbnQgb3V0IG9mIGJvdW5kc1wiKTtcbiAgICAgICAgcmV0dXJuIFwieFwiO1xuICAgICAgfSk7XG4gICAgICB0bXAgPSB0bXAucmVwbGFjZSgvXFxcXHUoW2EtZkEtRjAtOV17NH0pfFtcXHVEODAwLVxcdURCRkZdW1xcdURDMDAtXFx1REZGRl0vZywgXCJ4XCIpO1xuICAgIH1cbiAgfVxuICAvLyBEZXRlY3QgaW52YWxpZCByZWd1bGFyIGV4cHJlc3Npb25zLlxuICB2YXIgdmFsdWUgPSBudWxsO1xuICAvLyBSaGlubydzIHJlZ3VsYXIgZXhwcmVzc2lvbiBwYXJzZXIgaXMgZmxha3kgYW5kIHRocm93cyB1bmNhdGNoYWJsZSBleGNlcHRpb25zLFxuICAvLyBzbyBkb24ndCBkbyBkZXRlY3Rpb24gaWYgd2UgYXJlIHJ1bm5pbmcgdW5kZXIgUmhpbm9cbiAgaWYgKCFpc1JoaW5vKSB7XG4gICAgdHJ5Q3JlYXRlUmVnZXhwKHRtcCwgdW5kZWZpbmVkLCBzdGFydCk7XG4gICAgLy8gR2V0IGEgcmVndWxhciBleHByZXNzaW9uIG9iamVjdCBmb3IgdGhpcyBwYXR0ZXJuLWZsYWcgcGFpciwgb3IgYG51bGxgIGluXG4gICAgLy8gY2FzZSB0aGUgY3VycmVudCBlbnZpcm9ubWVudCBkb2Vzbid0IHN1cHBvcnQgdGhlIGZsYWdzIGl0IHVzZXMuXG4gICAgdmFsdWUgPSB0cnlDcmVhdGVSZWdleHAoY29udGVudCwgbW9kcyk7XG4gIH1cbiAgcmV0dXJuIHRoaXMuZmluaXNoVG9rZW4oX3Rva2VudHlwZS50eXBlcy5yZWdleHAsIHsgcGF0dGVybjogY29udGVudCwgZmxhZ3M6IG1vZHMsIHZhbHVlOiB2YWx1ZSB9KTtcbn07XG5cbi8vIFJlYWQgYW4gaW50ZWdlciBpbiB0aGUgZ2l2ZW4gcmFkaXguIFJldHVybiBudWxsIGlmIHplcm8gZGlnaXRzXG4vLyB3ZXJlIHJlYWQsIHRoZSBpbnRlZ2VyIHZhbHVlIG90aGVyd2lzZS4gV2hlbiBgbGVuYCBpcyBnaXZlbiwgdGhpc1xuLy8gd2lsbCByZXR1cm4gYG51bGxgIHVubGVzcyB0aGUgaW50ZWdlciBoYXMgZXhhY3RseSBgbGVuYCBkaWdpdHMuXG5cbnBwLnJlYWRJbnQgPSBmdW5jdGlvbiAocmFkaXgsIGxlbikge1xuICB2YXIgc3RhcnQgPSB0aGlzLnBvcyxcbiAgICAgIHRvdGFsID0gMDtcbiAgZm9yICh2YXIgaSA9IDAsIGUgPSBsZW4gPT0gbnVsbCA/IEluZmluaXR5IDogbGVuOyBpIDwgZTsgKytpKSB7XG4gICAgdmFyIGNvZGUgPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MpLFxuICAgICAgICB2YWwgPSB1bmRlZmluZWQ7XG4gICAgaWYgKGNvZGUgPj0gOTcpIHZhbCA9IGNvZGUgLSA5NyArIDEwOyAvLyBhXG4gICAgZWxzZSBpZiAoY29kZSA+PSA2NSkgdmFsID0gY29kZSAtIDY1ICsgMTA7IC8vIEFcbiAgICAgIGVsc2UgaWYgKGNvZGUgPj0gNDggJiYgY29kZSA8PSA1NykgdmFsID0gY29kZSAtIDQ4OyAvLyAwLTlcbiAgICAgICAgZWxzZSB2YWwgPSBJbmZpbml0eTtcbiAgICBpZiAodmFsID49IHJhZGl4KSBicmVhaztcbiAgICArK3RoaXMucG9zO1xuICAgIHRvdGFsID0gdG90YWwgKiByYWRpeCArIHZhbDtcbiAgfVxuICBpZiAodGhpcy5wb3MgPT09IHN0YXJ0IHx8IGxlbiAhPSBudWxsICYmIHRoaXMucG9zIC0gc3RhcnQgIT09IGxlbikgcmV0dXJuIG51bGw7XG5cbiAgcmV0dXJuIHRvdGFsO1xufTtcblxucHAucmVhZFJhZGl4TnVtYmVyID0gZnVuY3Rpb24gKHJhZGl4KSB7XG4gIHRoaXMucG9zICs9IDI7IC8vIDB4XG4gIHZhciB2YWwgPSB0aGlzLnJlYWRJbnQocmFkaXgpO1xuICBpZiAodmFsID09IG51bGwpIHRoaXMucmFpc2UodGhpcy5zdGFydCArIDIsIFwiRXhwZWN0ZWQgbnVtYmVyIGluIHJhZGl4IFwiICsgcmFkaXgpO1xuICBpZiAoX2lkZW50aWZpZXIuaXNJZGVudGlmaWVyU3RhcnQodGhpcy5mdWxsQ2hhckNvZGVBdFBvcygpKSkgdGhpcy5yYWlzZSh0aGlzLnBvcywgXCJJZGVudGlmaWVyIGRpcmVjdGx5IGFmdGVyIG51bWJlclwiKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoVG9rZW4oX3Rva2VudHlwZS50eXBlcy5udW0sIHZhbCk7XG59O1xuXG4vLyBSZWFkIGFuIGludGVnZXIsIG9jdGFsIGludGVnZXIsIG9yIGZsb2F0aW5nLXBvaW50IG51bWJlci5cblxucHAucmVhZE51bWJlciA9IGZ1bmN0aW9uIChzdGFydHNXaXRoRG90KSB7XG4gIHZhciBzdGFydCA9IHRoaXMucG9zLFxuICAgICAgaXNGbG9hdCA9IGZhbHNlLFxuICAgICAgb2N0YWwgPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MpID09PSA0ODtcbiAgaWYgKCFzdGFydHNXaXRoRG90ICYmIHRoaXMucmVhZEludCgxMCkgPT09IG51bGwpIHRoaXMucmFpc2Uoc3RhcnQsIFwiSW52YWxpZCBudW1iZXJcIik7XG4gIHZhciBuZXh0ID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zKTtcbiAgaWYgKG5leHQgPT09IDQ2KSB7XG4gICAgLy8gJy4nXG4gICAgKyt0aGlzLnBvcztcbiAgICB0aGlzLnJlYWRJbnQoMTApO1xuICAgIGlzRmxvYXQgPSB0cnVlO1xuICAgIG5leHQgPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MpO1xuICB9XG4gIGlmIChuZXh0ID09PSA2OSB8fCBuZXh0ID09PSAxMDEpIHtcbiAgICAvLyAnZUUnXG4gICAgbmV4dCA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCgrK3RoaXMucG9zKTtcbiAgICBpZiAobmV4dCA9PT0gNDMgfHwgbmV4dCA9PT0gNDUpICsrdGhpcy5wb3M7IC8vICcrLSdcbiAgICBpZiAodGhpcy5yZWFkSW50KDEwKSA9PT0gbnVsbCkgdGhpcy5yYWlzZShzdGFydCwgXCJJbnZhbGlkIG51bWJlclwiKTtcbiAgICBpc0Zsb2F0ID0gdHJ1ZTtcbiAgfVxuICBpZiAoX2lkZW50aWZpZXIuaXNJZGVudGlmaWVyU3RhcnQodGhpcy5mdWxsQ2hhckNvZGVBdFBvcygpKSkgdGhpcy5yYWlzZSh0aGlzLnBvcywgXCJJZGVudGlmaWVyIGRpcmVjdGx5IGFmdGVyIG51bWJlclwiKTtcblxuICB2YXIgc3RyID0gdGhpcy5pbnB1dC5zbGljZShzdGFydCwgdGhpcy5wb3MpLFxuICAgICAgdmFsID0gdW5kZWZpbmVkO1xuICBpZiAoaXNGbG9hdCkgdmFsID0gcGFyc2VGbG9hdChzdHIpO2Vsc2UgaWYgKCFvY3RhbCB8fCBzdHIubGVuZ3RoID09PSAxKSB2YWwgPSBwYXJzZUludChzdHIsIDEwKTtlbHNlIGlmICgvWzg5XS8udGVzdChzdHIpIHx8IHRoaXMuc3RyaWN0KSB0aGlzLnJhaXNlKHN0YXJ0LCBcIkludmFsaWQgbnVtYmVyXCIpO2Vsc2UgdmFsID0gcGFyc2VJbnQoc3RyLCA4KTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoVG9rZW4oX3Rva2VudHlwZS50eXBlcy5udW0sIHZhbCk7XG59O1xuXG4vLyBSZWFkIGEgc3RyaW5nIHZhbHVlLCBpbnRlcnByZXRpbmcgYmFja3NsYXNoLWVzY2FwZXMuXG5cbnBwLnJlYWRDb2RlUG9pbnQgPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBjaCA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyksXG4gICAgICBjb2RlID0gdW5kZWZpbmVkO1xuXG4gIGlmIChjaCA9PT0gMTIzKSB7XG4gICAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA8IDYpIHRoaXMudW5leHBlY3RlZCgpO1xuICAgIHZhciBjb2RlUG9zID0gKyt0aGlzLnBvcztcbiAgICBjb2RlID0gdGhpcy5yZWFkSGV4Q2hhcih0aGlzLmlucHV0LmluZGV4T2YoJ30nLCB0aGlzLnBvcykgLSB0aGlzLnBvcyk7XG4gICAgKyt0aGlzLnBvcztcbiAgICBpZiAoY29kZSA+IDB4MTBGRkZGKSB0aGlzLnJhaXNlKGNvZGVQb3MsIFwiQ29kZSBwb2ludCBvdXQgb2YgYm91bmRzXCIpO1xuICB9IGVsc2Uge1xuICAgIGNvZGUgPSB0aGlzLnJlYWRIZXhDaGFyKDQpO1xuICB9XG4gIHJldHVybiBjb2RlO1xufTtcblxuZnVuY3Rpb24gY29kZVBvaW50VG9TdHJpbmcoY29kZSkge1xuICAvLyBVVEYtMTYgRGVjb2RpbmdcbiAgaWYgKGNvZGUgPD0gMHhGRkZGKSByZXR1cm4gU3RyaW5nLmZyb21DaGFyQ29kZShjb2RlKTtcbiAgY29kZSAtPSAweDEwMDAwO1xuICByZXR1cm4gU3RyaW5nLmZyb21DaGFyQ29kZSgoY29kZSA+PiAxMCkgKyAweEQ4MDAsIChjb2RlICYgMTAyMykgKyAweERDMDApO1xufVxuXG5wcC5yZWFkU3RyaW5nID0gZnVuY3Rpb24gKHF1b3RlKSB7XG4gIHZhciBvdXQgPSBcIlwiLFxuICAgICAgY2h1bmtTdGFydCA9ICsrdGhpcy5wb3M7XG4gIGZvciAoOzspIHtcbiAgICBpZiAodGhpcy5wb3MgPj0gdGhpcy5pbnB1dC5sZW5ndGgpIHRoaXMucmFpc2UodGhpcy5zdGFydCwgXCJVbnRlcm1pbmF0ZWQgc3RyaW5nIGNvbnN0YW50XCIpO1xuICAgIHZhciBjaCA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyk7XG4gICAgaWYgKGNoID09PSBxdW90ZSkgYnJlYWs7XG4gICAgaWYgKGNoID09PSA5Mikge1xuICAgICAgLy8gJ1xcJ1xuICAgICAgb3V0ICs9IHRoaXMuaW5wdXQuc2xpY2UoY2h1bmtTdGFydCwgdGhpcy5wb3MpO1xuICAgICAgb3V0ICs9IHRoaXMucmVhZEVzY2FwZWRDaGFyKGZhbHNlKTtcbiAgICAgIGNodW5rU3RhcnQgPSB0aGlzLnBvcztcbiAgICB9IGVsc2Uge1xuICAgICAgaWYgKF93aGl0ZXNwYWNlLmlzTmV3TGluZShjaCkpIHRoaXMucmFpc2UodGhpcy5zdGFydCwgXCJVbnRlcm1pbmF0ZWQgc3RyaW5nIGNvbnN0YW50XCIpO1xuICAgICAgKyt0aGlzLnBvcztcbiAgICB9XG4gIH1cbiAgb3V0ICs9IHRoaXMuaW5wdXQuc2xpY2UoY2h1bmtTdGFydCwgdGhpcy5wb3MrKyk7XG4gIHJldHVybiB0aGlzLmZpbmlzaFRva2VuKF90b2tlbnR5cGUudHlwZXMuc3RyaW5nLCBvdXQpO1xufTtcblxuLy8gUmVhZHMgdGVtcGxhdGUgc3RyaW5nIHRva2Vucy5cblxucHAucmVhZFRtcGxUb2tlbiA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIG91dCA9IFwiXCIsXG4gICAgICBjaHVua1N0YXJ0ID0gdGhpcy5wb3M7XG4gIGZvciAoOzspIHtcbiAgICBpZiAodGhpcy5wb3MgPj0gdGhpcy5pbnB1dC5sZW5ndGgpIHRoaXMucmFpc2UodGhpcy5zdGFydCwgXCJVbnRlcm1pbmF0ZWQgdGVtcGxhdGVcIik7XG4gICAgdmFyIGNoID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zKTtcbiAgICBpZiAoY2ggPT09IDk2IHx8IGNoID09PSAzNiAmJiB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAxKSA9PT0gMTIzKSB7XG4gICAgICAvLyAnYCcsICckeydcbiAgICAgIGlmICh0aGlzLnBvcyA9PT0gdGhpcy5zdGFydCAmJiB0aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMudGVtcGxhdGUpIHtcbiAgICAgICAgaWYgKGNoID09PSAzNikge1xuICAgICAgICAgIHRoaXMucG9zICs9IDI7XG4gICAgICAgICAgcmV0dXJuIHRoaXMuZmluaXNoVG9rZW4oX3Rva2VudHlwZS50eXBlcy5kb2xsYXJCcmFjZUwpO1xuICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgICsrdGhpcy5wb3M7XG4gICAgICAgICAgcmV0dXJuIHRoaXMuZmluaXNoVG9rZW4oX3Rva2VudHlwZS50eXBlcy5iYWNrUXVvdGUpO1xuICAgICAgICB9XG4gICAgICB9XG4gICAgICBvdXQgKz0gdGhpcy5pbnB1dC5zbGljZShjaHVua1N0YXJ0LCB0aGlzLnBvcyk7XG4gICAgICByZXR1cm4gdGhpcy5maW5pc2hUb2tlbihfdG9rZW50eXBlLnR5cGVzLnRlbXBsYXRlLCBvdXQpO1xuICAgIH1cbiAgICBpZiAoY2ggPT09IDkyKSB7XG4gICAgICAvLyAnXFwnXG4gICAgICBvdXQgKz0gdGhpcy5pbnB1dC5zbGljZShjaHVua1N0YXJ0LCB0aGlzLnBvcyk7XG4gICAgICBvdXQgKz0gdGhpcy5yZWFkRXNjYXBlZENoYXIodHJ1ZSk7XG4gICAgICBjaHVua1N0YXJ0ID0gdGhpcy5wb3M7XG4gICAgfSBlbHNlIGlmIChfd2hpdGVzcGFjZS5pc05ld0xpbmUoY2gpKSB7XG4gICAgICBvdXQgKz0gdGhpcy5pbnB1dC5zbGljZShjaHVua1N0YXJ0LCB0aGlzLnBvcyk7XG4gICAgICArK3RoaXMucG9zO1xuICAgICAgc3dpdGNoIChjaCkge1xuICAgICAgICBjYXNlIDEzOlxuICAgICAgICAgIGlmICh0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MpID09PSAxMCkgKyt0aGlzLnBvcztcbiAgICAgICAgY2FzZSAxMDpcbiAgICAgICAgICBvdXQgKz0gXCJcXG5cIjtcbiAgICAgICAgICBicmVhaztcbiAgICAgICAgZGVmYXVsdDpcbiAgICAgICAgICBvdXQgKz0gU3RyaW5nLmZyb21DaGFyQ29kZShjaCk7XG4gICAgICAgICAgYnJlYWs7XG4gICAgICB9XG4gICAgICBpZiAodGhpcy5vcHRpb25zLmxvY2F0aW9ucykge1xuICAgICAgICArK3RoaXMuY3VyTGluZTtcbiAgICAgICAgdGhpcy5saW5lU3RhcnQgPSB0aGlzLnBvcztcbiAgICAgIH1cbiAgICAgIGNodW5rU3RhcnQgPSB0aGlzLnBvcztcbiAgICB9IGVsc2Uge1xuICAgICAgKyt0aGlzLnBvcztcbiAgICB9XG4gIH1cbn07XG5cbi8vIFVzZWQgdG8gcmVhZCBlc2NhcGVkIGNoYXJhY3RlcnNcblxucHAucmVhZEVzY2FwZWRDaGFyID0gZnVuY3Rpb24gKGluVGVtcGxhdGUpIHtcbiAgdmFyIGNoID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KCsrdGhpcy5wb3MpO1xuICArK3RoaXMucG9zO1xuICBzd2l0Y2ggKGNoKSB7XG4gICAgY2FzZSAxMTA6XG4gICAgICByZXR1cm4gXCJcXG5cIjsgLy8gJ24nIC0+ICdcXG4nXG4gICAgY2FzZSAxMTQ6XG4gICAgICByZXR1cm4gXCJcXHJcIjsgLy8gJ3InIC0+ICdcXHInXG4gICAgY2FzZSAxMjA6XG4gICAgICByZXR1cm4gU3RyaW5nLmZyb21DaGFyQ29kZSh0aGlzLnJlYWRIZXhDaGFyKDIpKTsgLy8gJ3gnXG4gICAgY2FzZSAxMTc6XG4gICAgICByZXR1cm4gY29kZVBvaW50VG9TdHJpbmcodGhpcy5yZWFkQ29kZVBvaW50KCkpOyAvLyAndSdcbiAgICBjYXNlIDExNjpcbiAgICAgIHJldHVybiBcIlxcdFwiOyAvLyAndCcgLT4gJ1xcdCdcbiAgICBjYXNlIDk4OlxuICAgICAgcmV0dXJuIFwiXFxiXCI7IC8vICdiJyAtPiAnXFxiJ1xuICAgIGNhc2UgMTE4OlxuICAgICAgcmV0dXJuIFwiXFx1MDAwYlwiOyAvLyAndicgLT4gJ1xcdTAwMGInXG4gICAgY2FzZSAxMDI6XG4gICAgICByZXR1cm4gXCJcXGZcIjsgLy8gJ2YnIC0+ICdcXGYnXG4gICAgY2FzZSAxMzpcbiAgICAgIGlmICh0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MpID09PSAxMCkgKyt0aGlzLnBvczsgLy8gJ1xcclxcbidcbiAgICBjYXNlIDEwOlxuICAgICAgLy8gJyBcXG4nXG4gICAgICBpZiAodGhpcy5vcHRpb25zLmxvY2F0aW9ucykge1xuICAgICAgICB0aGlzLmxpbmVTdGFydCA9IHRoaXMucG9zOysrdGhpcy5jdXJMaW5lO1xuICAgICAgfVxuICAgICAgcmV0dXJuIFwiXCI7XG4gICAgZGVmYXVsdDpcbiAgICAgIGlmIChjaCA+PSA0OCAmJiBjaCA8PSA1NSkge1xuICAgICAgICB2YXIgb2N0YWxTdHIgPSB0aGlzLmlucHV0LnN1YnN0cih0aGlzLnBvcyAtIDEsIDMpLm1hdGNoKC9eWzAtN10rLylbMF07XG4gICAgICAgIHZhciBvY3RhbCA9IHBhcnNlSW50KG9jdGFsU3RyLCA4KTtcbiAgICAgICAgaWYgKG9jdGFsID4gMjU1KSB7XG4gICAgICAgICAgb2N0YWxTdHIgPSBvY3RhbFN0ci5zbGljZSgwLCAtMSk7XG4gICAgICAgICAgb2N0YWwgPSBwYXJzZUludChvY3RhbFN0ciwgOCk7XG4gICAgICAgIH1cbiAgICAgICAgaWYgKG9jdGFsID4gMCAmJiAodGhpcy5zdHJpY3QgfHwgaW5UZW1wbGF0ZSkpIHtcbiAgICAgICAgICB0aGlzLnJhaXNlKHRoaXMucG9zIC0gMiwgXCJPY3RhbCBsaXRlcmFsIGluIHN0cmljdCBtb2RlXCIpO1xuICAgICAgICB9XG4gICAgICAgIHRoaXMucG9zICs9IG9jdGFsU3RyLmxlbmd0aCAtIDE7XG4gICAgICAgIHJldHVybiBTdHJpbmcuZnJvbUNoYXJDb2RlKG9jdGFsKTtcbiAgICAgIH1cbiAgICAgIHJldHVybiBTdHJpbmcuZnJvbUNoYXJDb2RlKGNoKTtcbiAgfVxufTtcblxuLy8gVXNlZCB0byByZWFkIGNoYXJhY3RlciBlc2NhcGUgc2VxdWVuY2VzICgnXFx4JywgJ1xcdScsICdcXFUnKS5cblxucHAucmVhZEhleENoYXIgPSBmdW5jdGlvbiAobGVuKSB7XG4gIHZhciBjb2RlUG9zID0gdGhpcy5wb3M7XG4gIHZhciBuID0gdGhpcy5yZWFkSW50KDE2LCBsZW4pO1xuICBpZiAobiA9PT0gbnVsbCkgdGhpcy5yYWlzZShjb2RlUG9zLCBcIkJhZCBjaGFyYWN0ZXIgZXNjYXBlIHNlcXVlbmNlXCIpO1xuICByZXR1cm4gbjtcbn07XG5cbi8vIFJlYWQgYW4gaWRlbnRpZmllciwgYW5kIHJldHVybiBpdCBhcyBhIHN0cmluZy4gU2V0cyBgdGhpcy5jb250YWluc0VzY2Bcbi8vIHRvIHdoZXRoZXIgdGhlIHdvcmQgY29udGFpbmVkIGEgJ1xcdScgZXNjYXBlLlxuLy9cbi8vIEluY3JlbWVudGFsbHkgYWRkcyBvbmx5IGVzY2FwZWQgY2hhcnMsIGFkZGluZyBvdGhlciBjaHVua3MgYXMtaXNcbi8vIGFzIGEgbWljcm8tb3B0aW1pemF0aW9uLlxuXG5wcC5yZWFkV29yZDEgPSBmdW5jdGlvbiAoKSB7XG4gIHRoaXMuY29udGFpbnNFc2MgPSBmYWxzZTtcbiAgdmFyIHdvcmQgPSBcIlwiLFxuICAgICAgZmlyc3QgPSB0cnVlLFxuICAgICAgY2h1bmtTdGFydCA9IHRoaXMucG9zO1xuICB2YXIgYXN0cmFsID0gdGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDY7XG4gIHdoaWxlICh0aGlzLnBvcyA8IHRoaXMuaW5wdXQubGVuZ3RoKSB7XG4gICAgdmFyIGNoID0gdGhpcy5mdWxsQ2hhckNvZGVBdFBvcygpO1xuICAgIGlmIChfaWRlbnRpZmllci5pc0lkZW50aWZpZXJDaGFyKGNoLCBhc3RyYWwpKSB7XG4gICAgICB0aGlzLnBvcyArPSBjaCA8PSAweGZmZmYgPyAxIDogMjtcbiAgICB9IGVsc2UgaWYgKGNoID09PSA5Mikge1xuICAgICAgLy8gXCJcXFwiXG4gICAgICB0aGlzLmNvbnRhaW5zRXNjID0gdHJ1ZTtcbiAgICAgIHdvcmQgKz0gdGhpcy5pbnB1dC5zbGljZShjaHVua1N0YXJ0LCB0aGlzLnBvcyk7XG4gICAgICB2YXIgZXNjU3RhcnQgPSB0aGlzLnBvcztcbiAgICAgIGlmICh0aGlzLmlucHV0LmNoYXJDb2RlQXQoKyt0aGlzLnBvcykgIT0gMTE3KSAvLyBcInVcIlxuICAgICAgICB0aGlzLnJhaXNlKHRoaXMucG9zLCBcIkV4cGVjdGluZyBVbmljb2RlIGVzY2FwZSBzZXF1ZW5jZSBcXFxcdVhYWFhcIik7XG4gICAgICArK3RoaXMucG9zO1xuICAgICAgdmFyIGVzYyA9IHRoaXMucmVhZENvZGVQb2ludCgpO1xuICAgICAgaWYgKCEoZmlyc3QgPyBfaWRlbnRpZmllci5pc0lkZW50aWZpZXJTdGFydCA6IF9pZGVudGlmaWVyLmlzSWRlbnRpZmllckNoYXIpKGVzYywgYXN0cmFsKSkgdGhpcy5yYWlzZShlc2NTdGFydCwgXCJJbnZhbGlkIFVuaWNvZGUgZXNjYXBlXCIpO1xuICAgICAgd29yZCArPSBjb2RlUG9pbnRUb1N0cmluZyhlc2MpO1xuICAgICAgY2h1bmtTdGFydCA9IHRoaXMucG9zO1xuICAgIH0gZWxzZSB7XG4gICAgICBicmVhaztcbiAgICB9XG4gICAgZmlyc3QgPSBmYWxzZTtcbiAgfVxuICByZXR1cm4gd29yZCArIHRoaXMuaW5wdXQuc2xpY2UoY2h1bmtTdGFydCwgdGhpcy5wb3MpO1xufTtcblxuLy8gUmVhZCBhbiBpZGVudGlmaWVyIG9yIGtleXdvcmQgdG9rZW4uIFdpbGwgY2hlY2sgZm9yIHJlc2VydmVkXG4vLyB3b3JkcyB3aGVuIG5lY2Vzc2FyeS5cblxucHAucmVhZFdvcmQgPSBmdW5jdGlvbiAoKSB7XG4gIHZhciB3b3JkID0gdGhpcy5yZWFkV29yZDEoKTtcbiAgdmFyIHR5cGUgPSBfdG9rZW50eXBlLnR5cGVzLm5hbWU7XG4gIGlmICgodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYgfHwgIXRoaXMuY29udGFpbnNFc2MpICYmIHRoaXMuaXNLZXl3b3JkKHdvcmQpKSB0eXBlID0gX3Rva2VudHlwZS5rZXl3b3Jkc1t3b3JkXTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoVG9rZW4odHlwZSwgd29yZCk7XG59O1xuXG59LHtcIi4vaWRlbnRpZmllclwiOjIsXCIuL2xvY3V0aWxcIjo1LFwiLi9zdGF0ZVwiOjEwLFwiLi90b2tlbnR5cGVcIjoxNCxcIi4vd2hpdGVzcGFjZVwiOjE2fV0sMTQ6W2Z1bmN0aW9uKF9kZXJlcV8sbW9kdWxlLGV4cG9ydHMpe1xuLy8gIyMgVG9rZW4gdHlwZXNcblxuLy8gVGhlIGFzc2lnbm1lbnQgb2YgZmluZS1ncmFpbmVkLCBpbmZvcm1hdGlvbi1jYXJyeWluZyB0eXBlIG9iamVjdHNcbi8vIGFsbG93cyB0aGUgdG9rZW5pemVyIHRvIHN0b3JlIHRoZSBpbmZvcm1hdGlvbiBpdCBoYXMgYWJvdXQgYVxuLy8gdG9rZW4gaW4gYSB3YXkgdGhhdCBpcyB2ZXJ5IGNoZWFwIGZvciB0aGUgcGFyc2VyIHRvIGxvb2sgdXAuXG5cbi8vIEFsbCB0b2tlbiB0eXBlIHZhcmlhYmxlcyBzdGFydCB3aXRoIGFuIHVuZGVyc2NvcmUsIHRvIG1ha2UgdGhlbVxuLy8gZWFzeSB0byByZWNvZ25pemUuXG5cbi8vIFRoZSBgYmVmb3JlRXhwcmAgcHJvcGVydHkgaXMgdXNlZCB0byBkaXNhbWJpZ3VhdGUgYmV0d2VlbiByZWd1bGFyXG4vLyBleHByZXNzaW9ucyBhbmQgZGl2aXNpb25zLiBJdCBpcyBzZXQgb24gYWxsIHRva2VuIHR5cGVzIHRoYXQgY2FuXG4vLyBiZSBmb2xsb3dlZCBieSBhbiBleHByZXNzaW9uICh0aHVzLCBhIHNsYXNoIGFmdGVyIHRoZW0gd291bGQgYmUgYVxuLy8gcmVndWxhciBleHByZXNzaW9uKS5cbi8vXG4vLyBgaXNMb29wYCBtYXJrcyBhIGtleXdvcmQgYXMgc3RhcnRpbmcgYSBsb29wLCB3aGljaCBpcyBpbXBvcnRhbnRcbi8vIHRvIGtub3cgd2hlbiBwYXJzaW5nIGEgbGFiZWwsIGluIG9yZGVyIHRvIGFsbG93IG9yIGRpc2FsbG93XG4vLyBjb250aW51ZSBqdW1wcyB0byB0aGF0IGxhYmVsLlxuXG5cInVzZSBzdHJpY3RcIjtcblxuZXhwb3J0cy5fX2VzTW9kdWxlID0gdHJ1ZTtcblxuZnVuY3Rpb24gX2NsYXNzQ2FsbENoZWNrKGluc3RhbmNlLCBDb25zdHJ1Y3RvcikgeyBpZiAoIShpbnN0YW5jZSBpbnN0YW5jZW9mIENvbnN0cnVjdG9yKSkgeyB0aHJvdyBuZXcgVHlwZUVycm9yKFwiQ2Fubm90IGNhbGwgYSBjbGFzcyBhcyBhIGZ1bmN0aW9uXCIpOyB9IH1cblxudmFyIFRva2VuVHlwZSA9IGZ1bmN0aW9uIFRva2VuVHlwZShsYWJlbCkge1xuICB2YXIgY29uZiA9IGFyZ3VtZW50cy5sZW5ndGggPD0gMSB8fCBhcmd1bWVudHNbMV0gPT09IHVuZGVmaW5lZCA/IHt9IDogYXJndW1lbnRzWzFdO1xuXG4gIF9jbGFzc0NhbGxDaGVjayh0aGlzLCBUb2tlblR5cGUpO1xuXG4gIHRoaXMubGFiZWwgPSBsYWJlbDtcbiAgdGhpcy5rZXl3b3JkID0gY29uZi5rZXl3b3JkO1xuICB0aGlzLmJlZm9yZUV4cHIgPSAhIWNvbmYuYmVmb3JlRXhwcjtcbiAgdGhpcy5zdGFydHNFeHByID0gISFjb25mLnN0YXJ0c0V4cHI7XG4gIHRoaXMuaXNMb29wID0gISFjb25mLmlzTG9vcDtcbiAgdGhpcy5pc0Fzc2lnbiA9ICEhY29uZi5pc0Fzc2lnbjtcbiAgdGhpcy5wcmVmaXggPSAhIWNvbmYucHJlZml4O1xuICB0aGlzLnBvc3RmaXggPSAhIWNvbmYucG9zdGZpeDtcbiAgdGhpcy5iaW5vcCA9IGNvbmYuYmlub3AgfHwgbnVsbDtcbiAgdGhpcy51cGRhdGVDb250ZXh0ID0gbnVsbDtcbn07XG5cbmV4cG9ydHMuVG9rZW5UeXBlID0gVG9rZW5UeXBlO1xuXG5mdW5jdGlvbiBiaW5vcChuYW1lLCBwcmVjKSB7XG4gIHJldHVybiBuZXcgVG9rZW5UeXBlKG5hbWUsIHsgYmVmb3JlRXhwcjogdHJ1ZSwgYmlub3A6IHByZWMgfSk7XG59XG52YXIgYmVmb3JlRXhwciA9IHsgYmVmb3JlRXhwcjogdHJ1ZSB9LFxuICAgIHN0YXJ0c0V4cHIgPSB7IHN0YXJ0c0V4cHI6IHRydWUgfTtcblxudmFyIHR5cGVzID0ge1xuICBudW06IG5ldyBUb2tlblR5cGUoXCJudW1cIiwgc3RhcnRzRXhwciksXG4gIHJlZ2V4cDogbmV3IFRva2VuVHlwZShcInJlZ2V4cFwiLCBzdGFydHNFeHByKSxcbiAgc3RyaW5nOiBuZXcgVG9rZW5UeXBlKFwic3RyaW5nXCIsIHN0YXJ0c0V4cHIpLFxuICBuYW1lOiBuZXcgVG9rZW5UeXBlKFwibmFtZVwiLCBzdGFydHNFeHByKSxcbiAgZW9mOiBuZXcgVG9rZW5UeXBlKFwiZW9mXCIpLFxuXG4gIC8vIFB1bmN0dWF0aW9uIHRva2VuIHR5cGVzLlxuICBicmFja2V0TDogbmV3IFRva2VuVHlwZShcIltcIiwgeyBiZWZvcmVFeHByOiB0cnVlLCBzdGFydHNFeHByOiB0cnVlIH0pLFxuICBicmFja2V0UjogbmV3IFRva2VuVHlwZShcIl1cIiksXG4gIGJyYWNlTDogbmV3IFRva2VuVHlwZShcIntcIiwgeyBiZWZvcmVFeHByOiB0cnVlLCBzdGFydHNFeHByOiB0cnVlIH0pLFxuICBicmFjZVI6IG5ldyBUb2tlblR5cGUoXCJ9XCIpLFxuICBwYXJlbkw6IG5ldyBUb2tlblR5cGUoXCIoXCIsIHsgYmVmb3JlRXhwcjogdHJ1ZSwgc3RhcnRzRXhwcjogdHJ1ZSB9KSxcbiAgcGFyZW5SOiBuZXcgVG9rZW5UeXBlKFwiKVwiKSxcbiAgY29tbWE6IG5ldyBUb2tlblR5cGUoXCIsXCIsIGJlZm9yZUV4cHIpLFxuICBzZW1pOiBuZXcgVG9rZW5UeXBlKFwiO1wiLCBiZWZvcmVFeHByKSxcbiAgY29sb246IG5ldyBUb2tlblR5cGUoXCI6XCIsIGJlZm9yZUV4cHIpLFxuICBkb3Q6IG5ldyBUb2tlblR5cGUoXCIuXCIpLFxuICBxdWVzdGlvbjogbmV3IFRva2VuVHlwZShcIj9cIiwgYmVmb3JlRXhwciksXG4gIGFycm93OiBuZXcgVG9rZW5UeXBlKFwiPT5cIiwgYmVmb3JlRXhwciksXG4gIHRlbXBsYXRlOiBuZXcgVG9rZW5UeXBlKFwidGVtcGxhdGVcIiksXG4gIGVsbGlwc2lzOiBuZXcgVG9rZW5UeXBlKFwiLi4uXCIsIGJlZm9yZUV4cHIpLFxuICBiYWNrUXVvdGU6IG5ldyBUb2tlblR5cGUoXCJgXCIsIHN0YXJ0c0V4cHIpLFxuICBkb2xsYXJCcmFjZUw6IG5ldyBUb2tlblR5cGUoXCIke1wiLCB7IGJlZm9yZUV4cHI6IHRydWUsIHN0YXJ0c0V4cHI6IHRydWUgfSksXG5cbiAgLy8gT3BlcmF0b3JzLiBUaGVzZSBjYXJyeSBzZXZlcmFsIGtpbmRzIG9mIHByb3BlcnRpZXMgdG8gaGVscCB0aGVcbiAgLy8gcGFyc2VyIHVzZSB0aGVtIHByb3Blcmx5ICh0aGUgcHJlc2VuY2Ugb2YgdGhlc2UgcHJvcGVydGllcyBpc1xuICAvLyB3aGF0IGNhdGVnb3JpemVzIHRoZW0gYXMgb3BlcmF0b3JzKS5cbiAgLy9cbiAgLy8gYGJpbm9wYCwgd2hlbiBwcmVzZW50LCBzcGVjaWZpZXMgdGhhdCB0aGlzIG9wZXJhdG9yIGlzIGEgYmluYXJ5XG4gIC8vIG9wZXJhdG9yLCBhbmQgd2lsbCByZWZlciB0byBpdHMgcHJlY2VkZW5jZS5cbiAgLy9cbiAgLy8gYHByZWZpeGAgYW5kIGBwb3N0Zml4YCBtYXJrIHRoZSBvcGVyYXRvciBhcyBhIHByZWZpeCBvciBwb3N0Zml4XG4gIC8vIHVuYXJ5IG9wZXJhdG9yLlxuICAvL1xuICAvLyBgaXNBc3NpZ25gIG1hcmtzIGFsbCBvZiBgPWAsIGArPWAsIGAtPWAgZXRjZXRlcmEsIHdoaWNoIGFjdCBhc1xuICAvLyBiaW5hcnkgb3BlcmF0b3JzIHdpdGggYSB2ZXJ5IGxvdyBwcmVjZWRlbmNlLCB0aGF0IHNob3VsZCByZXN1bHRcbiAgLy8gaW4gQXNzaWdubWVudEV4cHJlc3Npb24gbm9kZXMuXG5cbiAgZXE6IG5ldyBUb2tlblR5cGUoXCI9XCIsIHsgYmVmb3JlRXhwcjogdHJ1ZSwgaXNBc3NpZ246IHRydWUgfSksXG4gIGFzc2lnbjogbmV3IFRva2VuVHlwZShcIl89XCIsIHsgYmVmb3JlRXhwcjogdHJ1ZSwgaXNBc3NpZ246IHRydWUgfSksXG4gIGluY0RlYzogbmV3IFRva2VuVHlwZShcIisrLy0tXCIsIHsgcHJlZml4OiB0cnVlLCBwb3N0Zml4OiB0cnVlLCBzdGFydHNFeHByOiB0cnVlIH0pLFxuICBwcmVmaXg6IG5ldyBUb2tlblR5cGUoXCJwcmVmaXhcIiwgeyBiZWZvcmVFeHByOiB0cnVlLCBwcmVmaXg6IHRydWUsIHN0YXJ0c0V4cHI6IHRydWUgfSksXG4gIGxvZ2ljYWxPUjogYmlub3AoXCJ8fFwiLCAxKSxcbiAgbG9naWNhbEFORDogYmlub3AoXCImJlwiLCAyKSxcbiAgYml0d2lzZU9SOiBiaW5vcChcInxcIiwgMyksXG4gIGJpdHdpc2VYT1I6IGJpbm9wKFwiXlwiLCA0KSxcbiAgYml0d2lzZUFORDogYmlub3AoXCImXCIsIDUpLFxuICBlcXVhbGl0eTogYmlub3AoXCI9PS8hPVwiLCA2KSxcbiAgcmVsYXRpb25hbDogYmlub3AoXCI8Lz5cIiwgNyksXG4gIGJpdFNoaWZ0OiBiaW5vcChcIjw8Lz4+XCIsIDgpLFxuICBwbHVzTWluOiBuZXcgVG9rZW5UeXBlKFwiKy8tXCIsIHsgYmVmb3JlRXhwcjogdHJ1ZSwgYmlub3A6IDksIHByZWZpeDogdHJ1ZSwgc3RhcnRzRXhwcjogdHJ1ZSB9KSxcbiAgbW9kdWxvOiBiaW5vcChcIiVcIiwgMTApLFxuICBzdGFyOiBiaW5vcChcIipcIiwgMTApLFxuICBzbGFzaDogYmlub3AoXCIvXCIsIDEwKVxufTtcblxuZXhwb3J0cy50eXBlcyA9IHR5cGVzO1xuLy8gTWFwIGtleXdvcmQgbmFtZXMgdG8gdG9rZW4gdHlwZXMuXG5cbnZhciBrZXl3b3JkcyA9IHt9O1xuXG5leHBvcnRzLmtleXdvcmRzID0ga2V5d29yZHM7XG4vLyBTdWNjaW5jdCBkZWZpbml0aW9ucyBvZiBrZXl3b3JkIHRva2VuIHR5cGVzXG5mdW5jdGlvbiBrdyhuYW1lKSB7XG4gIHZhciBvcHRpb25zID0gYXJndW1lbnRzLmxlbmd0aCA8PSAxIHx8IGFyZ3VtZW50c1sxXSA9PT0gdW5kZWZpbmVkID8ge30gOiBhcmd1bWVudHNbMV07XG5cbiAgb3B0aW9ucy5rZXl3b3JkID0gbmFtZTtcbiAga2V5d29yZHNbbmFtZV0gPSB0eXBlc1tcIl9cIiArIG5hbWVdID0gbmV3IFRva2VuVHlwZShuYW1lLCBvcHRpb25zKTtcbn1cblxua3coXCJicmVha1wiKTtcbmt3KFwiY2FzZVwiLCBiZWZvcmVFeHByKTtcbmt3KFwiY2F0Y2hcIik7XG5rdyhcImNvbnRpbnVlXCIpO1xua3coXCJkZWJ1Z2dlclwiKTtcbmt3KFwiZGVmYXVsdFwiLCBiZWZvcmVFeHByKTtcbmt3KFwiZG9cIiwgeyBpc0xvb3A6IHRydWUgfSk7XG5rdyhcImVsc2VcIiwgYmVmb3JlRXhwcik7XG5rdyhcImZpbmFsbHlcIik7XG5rdyhcImZvclwiLCB7IGlzTG9vcDogdHJ1ZSB9KTtcbmt3KFwiZnVuY3Rpb25cIiwgc3RhcnRzRXhwcik7XG5rdyhcImlmXCIpO1xua3coXCJyZXR1cm5cIiwgYmVmb3JlRXhwcik7XG5rdyhcInN3aXRjaFwiKTtcbmt3KFwidGhyb3dcIiwgYmVmb3JlRXhwcik7XG5rdyhcInRyeVwiKTtcbmt3KFwidmFyXCIpO1xua3coXCJsZXRcIik7XG5rdyhcImNvbnN0XCIpO1xua3coXCJ3aGlsZVwiLCB7IGlzTG9vcDogdHJ1ZSB9KTtcbmt3KFwid2l0aFwiKTtcbmt3KFwibmV3XCIsIHsgYmVmb3JlRXhwcjogdHJ1ZSwgc3RhcnRzRXhwcjogdHJ1ZSB9KTtcbmt3KFwidGhpc1wiLCBzdGFydHNFeHByKTtcbmt3KFwic3VwZXJcIiwgc3RhcnRzRXhwcik7XG5rdyhcImNsYXNzXCIpO1xua3coXCJleHRlbmRzXCIsIGJlZm9yZUV4cHIpO1xua3coXCJleHBvcnRcIik7XG5rdyhcImltcG9ydFwiKTtcbmt3KFwieWllbGRcIiwgeyBiZWZvcmVFeHByOiB0cnVlLCBzdGFydHNFeHByOiB0cnVlIH0pO1xua3coXCJudWxsXCIsIHN0YXJ0c0V4cHIpO1xua3coXCJ0cnVlXCIsIHN0YXJ0c0V4cHIpO1xua3coXCJmYWxzZVwiLCBzdGFydHNFeHByKTtcbmt3KFwiaW5cIiwgeyBiZWZvcmVFeHByOiB0cnVlLCBiaW5vcDogNyB9KTtcbmt3KFwiaW5zdGFuY2VvZlwiLCB7IGJlZm9yZUV4cHI6IHRydWUsIGJpbm9wOiA3IH0pO1xua3coXCJ0eXBlb2ZcIiwgeyBiZWZvcmVFeHByOiB0cnVlLCBwcmVmaXg6IHRydWUsIHN0YXJ0c0V4cHI6IHRydWUgfSk7XG5rdyhcInZvaWRcIiwgeyBiZWZvcmVFeHByOiB0cnVlLCBwcmVmaXg6IHRydWUsIHN0YXJ0c0V4cHI6IHRydWUgfSk7XG5rdyhcImRlbGV0ZVwiLCB7IGJlZm9yZUV4cHI6IHRydWUsIHByZWZpeDogdHJ1ZSwgc3RhcnRzRXhwcjogdHJ1ZSB9KTtcblxufSx7fV0sMTU6W2Z1bmN0aW9uKF9kZXJlcV8sbW9kdWxlLGV4cG9ydHMpe1xuXCJ1c2Ugc3RyaWN0XCI7XG5cbmV4cG9ydHMuX19lc01vZHVsZSA9IHRydWU7XG5leHBvcnRzLmlzQXJyYXkgPSBpc0FycmF5O1xuZXhwb3J0cy5oYXMgPSBoYXM7XG5cbmZ1bmN0aW9uIGlzQXJyYXkob2JqKSB7XG4gIHJldHVybiBPYmplY3QucHJvdG90eXBlLnRvU3RyaW5nLmNhbGwob2JqKSA9PT0gXCJbb2JqZWN0IEFycmF5XVwiO1xufVxuXG4vLyBDaGVja3MgaWYgYW4gb2JqZWN0IGhhcyBhIHByb3BlcnR5LlxuXG5mdW5jdGlvbiBoYXMob2JqLCBwcm9wTmFtZSkge1xuICByZXR1cm4gT2JqZWN0LnByb3RvdHlwZS5oYXNPd25Qcm9wZXJ0eS5jYWxsKG9iaiwgcHJvcE5hbWUpO1xufVxuXG59LHt9XSwxNjpbZnVuY3Rpb24oX2RlcmVxXyxtb2R1bGUsZXhwb3J0cyl7XG4vLyBNYXRjaGVzIGEgd2hvbGUgbGluZSBicmVhayAod2hlcmUgQ1JMRiBpcyBjb25zaWRlcmVkIGEgc2luZ2xlXG4vLyBsaW5lIGJyZWFrKS4gVXNlZCB0byBjb3VudCBsaW5lcy5cblxuXCJ1c2Ugc3RyaWN0XCI7XG5cbmV4cG9ydHMuX19lc01vZHVsZSA9IHRydWU7XG5leHBvcnRzLmlzTmV3TGluZSA9IGlzTmV3TGluZTtcbnZhciBsaW5lQnJlYWsgPSAvXFxyXFxuP3xcXG58XFx1MjAyOHxcXHUyMDI5LztcbmV4cG9ydHMubGluZUJyZWFrID0gbGluZUJyZWFrO1xudmFyIGxpbmVCcmVha0cgPSBuZXcgUmVnRXhwKGxpbmVCcmVhay5zb3VyY2UsIFwiZ1wiKTtcblxuZXhwb3J0cy5saW5lQnJlYWtHID0gbGluZUJyZWFrRztcblxuZnVuY3Rpb24gaXNOZXdMaW5lKGNvZGUpIHtcbiAgcmV0dXJuIGNvZGUgPT09IDEwIHx8IGNvZGUgPT09IDEzIHx8IGNvZGUgPT09IDB4MjAyOCB8fCBjb2RlID09IDB4MjAyOTtcbn1cblxudmFyIG5vbkFTQ0lJd2hpdGVzcGFjZSA9IC9bXFx1MTY4MFxcdTE4MGVcXHUyMDAwLVxcdTIwMGFcXHUyMDJmXFx1MjA1ZlxcdTMwMDBcXHVmZWZmXS87XG5leHBvcnRzLm5vbkFTQ0lJd2hpdGVzcGFjZSA9IG5vbkFTQ0lJd2hpdGVzcGFjZTtcblxufSx7fV19LHt9LFszXSkoMylcbn0pOyIsIihmdW5jdGlvbihmKXtpZih0eXBlb2YgZXhwb3J0cz09PVwib2JqZWN0XCImJnR5cGVvZiBtb2R1bGUhPT1cInVuZGVmaW5lZFwiKXttb2R1bGUuZXhwb3J0cz1mKCl9ZWxzZSBpZih0eXBlb2YgZGVmaW5lPT09XCJmdW5jdGlvblwiJiZkZWZpbmUuYW1kKXtkZWZpbmUoW10sZil9ZWxzZXt2YXIgZztpZih0eXBlb2Ygd2luZG93IT09XCJ1bmRlZmluZWRcIil7Zz13aW5kb3d9ZWxzZSBpZih0eXBlb2YgZ2xvYmFsIT09XCJ1bmRlZmluZWRcIil7Zz1nbG9iYWx9ZWxzZSBpZih0eXBlb2Ygc2VsZiE9PVwidW5kZWZpbmVkXCIpe2c9c2VsZn1lbHNle2c9dGhpc30oZy5hY29ybiB8fCAoZy5hY29ybiA9IHt9KSkubG9vc2UgPSBmKCl9fSkoZnVuY3Rpb24oKXt2YXIgZGVmaW5lLG1vZHVsZSxleHBvcnRzO3JldHVybiAoZnVuY3Rpb24gZSh0LG4scil7ZnVuY3Rpb24gcyhvLHUpe2lmKCFuW29dKXtpZighdFtvXSl7dmFyIGE9dHlwZW9mIHJlcXVpcmU9PVwiZnVuY3Rpb25cIiYmcmVxdWlyZTtpZighdSYmYSlyZXR1cm4gYShvLCEwKTtpZihpKXJldHVybiBpKG8sITApO3ZhciBmPW5ldyBFcnJvcihcIkNhbm5vdCBmaW5kIG1vZHVsZSAnXCIrbytcIidcIik7dGhyb3cgZi5jb2RlPVwiTU9EVUxFX05PVF9GT1VORFwiLGZ9dmFyIGw9bltvXT17ZXhwb3J0czp7fX07dFtvXVswXS5jYWxsKGwuZXhwb3J0cyxmdW5jdGlvbihlKXt2YXIgbj10W29dWzFdW2VdO3JldHVybiBzKG4/bjplKX0sbCxsLmV4cG9ydHMsZSx0LG4scil9cmV0dXJuIG5bb10uZXhwb3J0c312YXIgaT10eXBlb2YgcmVxdWlyZT09XCJmdW5jdGlvblwiJiZyZXF1aXJlO2Zvcih2YXIgbz0wO288ci5sZW5ndGg7bysrKXMocltvXSk7cmV0dXJuIHN9KSh7MTpbZnVuY3Rpb24oX2RlcmVxXyxtb2R1bGUsZXhwb3J0cyl7XG4oZnVuY3Rpb24gKGdsb2JhbCl7XG5cInVzZSBzdHJpY3RcIjsoZnVuY3Rpb24oZil7aWYodHlwZW9mIGV4cG9ydHMgPT09IFwib2JqZWN0XCIgJiYgdHlwZW9mIG1vZHVsZSAhPT0gXCJ1bmRlZmluZWRcIil7bW9kdWxlLmV4cG9ydHMgPSBmKCk7fWVsc2UgaWYodHlwZW9mIGRlZmluZSA9PT0gXCJmdW5jdGlvblwiICYmIGRlZmluZS5hbWQpe2RlZmluZShbXSxmKTt9ZWxzZSB7dmFyIGc7aWYodHlwZW9mIHdpbmRvdyAhPT0gXCJ1bmRlZmluZWRcIil7ZyA9IHdpbmRvdzt9ZWxzZSBpZih0eXBlb2YgZ2xvYmFsICE9PSBcInVuZGVmaW5lZFwiKXtnID0gZ2xvYmFsO31lbHNlIGlmKHR5cGVvZiBzZWxmICE9PSBcInVuZGVmaW5lZFwiKXtnID0gc2VsZjt9ZWxzZSB7ZyA9IHRoaXM7fWcuYWNvcm4gPSBmKCk7fX0pKGZ1bmN0aW9uKCl7dmFyIGRlZmluZSxtb2R1bGUsZXhwb3J0cztyZXR1cm4gKGZ1bmN0aW9uIGUodCxuLHIpe2Z1bmN0aW9uIHMobyx1KXtpZighbltvXSl7aWYoIXRbb10pe3ZhciBhPXR5cGVvZiBfZGVyZXFfID09IFwiZnVuY3Rpb25cIiAmJiBfZGVyZXFfO2lmKCF1ICYmIGEpcmV0dXJuIGEobywhMCk7aWYoaSlyZXR1cm4gaShvLCEwKTt2YXIgZj1uZXcgRXJyb3IoXCJDYW5ub3QgZmluZCBtb2R1bGUgJ1wiICsgbyArIFwiJ1wiKTt0aHJvdyAoZi5jb2RlID0gXCJNT0RVTEVfTk9UX0ZPVU5EXCIsZik7fXZhciBsPW5bb10gPSB7ZXhwb3J0czp7fX07dFtvXVswXS5jYWxsKGwuZXhwb3J0cyxmdW5jdGlvbihlKXt2YXIgbj10W29dWzFdW2VdO3JldHVybiBzKG4/bjplKTt9LGwsbC5leHBvcnRzLGUsdCxuLHIpO31yZXR1cm4gbltvXS5leHBvcnRzO312YXIgaT10eXBlb2YgX2RlcmVxXyA9PSBcImZ1bmN0aW9uXCIgJiYgX2RlcmVxXztmb3IodmFyIG89MDtvIDwgci5sZW5ndGg7bysrKSBzKHJbb10pO3JldHVybiBzO30pKHsxOltmdW5jdGlvbihfZGVyZXFfLG1vZHVsZSxleHBvcnRzKXsgLy8gQSByZWN1cnNpdmUgZGVzY2VudCBwYXJzZXIgb3BlcmF0ZXMgYnkgZGVmaW5pbmcgZnVuY3Rpb25zIGZvciBhbGxcbi8vIHN5bnRhY3RpYyBlbGVtZW50cywgYW5kIHJlY3Vyc2l2ZWx5IGNhbGxpbmcgdGhvc2UsIGVhY2ggZnVuY3Rpb25cbi8vIGFkdmFuY2luZyB0aGUgaW5wdXQgc3RyZWFtIGFuZCByZXR1cm5pbmcgYW4gQVNUIG5vZGUuIFByZWNlZGVuY2Vcbi8vIG9mIGNvbnN0cnVjdHMgKGZvciBleGFtcGxlLCB0aGUgZmFjdCB0aGF0IGAheFsxXWAgbWVhbnMgYCEoeFsxXSlgXG4vLyBpbnN0ZWFkIG9mIGAoIXgpWzFdYCBpcyBoYW5kbGVkIGJ5IHRoZSBmYWN0IHRoYXQgdGhlIHBhcnNlclxuLy8gZnVuY3Rpb24gdGhhdCBwYXJzZXMgdW5hcnkgcHJlZml4IG9wZXJhdG9ycyBpcyBjYWxsZWQgZmlyc3QsIGFuZFxuLy8gaW4gdHVybiBjYWxscyB0aGUgZnVuY3Rpb24gdGhhdCBwYXJzZXMgYFtdYCBzdWJzY3JpcHRzIOKAlCB0aGF0XG4vLyB3YXksIGl0J2xsIHJlY2VpdmUgdGhlIG5vZGUgZm9yIGB4WzFdYCBhbHJlYWR5IHBhcnNlZCwgYW5kIHdyYXBzXG4vLyAqdGhhdCogaW4gdGhlIHVuYXJ5IG9wZXJhdG9yIG5vZGUuXG4vL1xuLy8gQWNvcm4gdXNlcyBhbiBbb3BlcmF0b3IgcHJlY2VkZW5jZSBwYXJzZXJdW29wcF0gdG8gaGFuZGxlIGJpbmFyeVxuLy8gb3BlcmF0b3IgcHJlY2VkZW5jZSwgYmVjYXVzZSBpdCBpcyBtdWNoIG1vcmUgY29tcGFjdCB0aGFuIHVzaW5nXG4vLyB0aGUgdGVjaG5pcXVlIG91dGxpbmVkIGFib3ZlLCB3aGljaCB1c2VzIGRpZmZlcmVudCwgbmVzdGluZ1xuLy8gZnVuY3Rpb25zIHRvIHNwZWNpZnkgcHJlY2VkZW5jZSwgZm9yIGFsbCBvZiB0aGUgdGVuIGJpbmFyeVxuLy8gcHJlY2VkZW5jZSBsZXZlbHMgdGhhdCBKYXZhU2NyaXB0IGRlZmluZXMuXG4vL1xuLy8gW29wcF06IGh0dHA6Ly9lbi53aWtpcGVkaWEub3JnL3dpa2kvT3BlcmF0b3ItcHJlY2VkZW5jZV9wYXJzZXJcblwidXNlIHN0cmljdFwiO3ZhciBfdG9rZW50eXBlPV9kZXJlcV8oXCIuL3Rva2VudHlwZVwiKTt2YXIgX3N0YXRlPV9kZXJlcV8oXCIuL3N0YXRlXCIpO3ZhciBfaWRlbnRpZmllcj1fZGVyZXFfKFwiLi9pZGVudGlmaWVyXCIpO3ZhciBfdXRpbD1fZGVyZXFfKFwiLi91dGlsXCIpO3ZhciBwcD1fc3RhdGUuUGFyc2VyLnByb3RvdHlwZTsgLy8gQ2hlY2sgaWYgcHJvcGVydHkgbmFtZSBjbGFzaGVzIHdpdGggYWxyZWFkeSBhZGRlZC5cbi8vIE9iamVjdC9jbGFzcyBnZXR0ZXJzIGFuZCBzZXR0ZXJzIGFyZSBub3QgYWxsb3dlZCB0byBjbGFzaCDigJRcbi8vIGVpdGhlciB3aXRoIGVhY2ggb3RoZXIgb3Igd2l0aCBhbiBpbml0IHByb3BlcnR5IOKAlCBhbmQgaW5cbi8vIHN0cmljdCBtb2RlLCBpbml0IHByb3BlcnRpZXMgYXJlIGFsc28gbm90IGFsbG93ZWQgdG8gYmUgcmVwZWF0ZWQuXG5wcC5jaGVja1Byb3BDbGFzaCA9IGZ1bmN0aW9uKHByb3AscHJvcEhhc2gpe2lmKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2ICYmIChwcm9wLmNvbXB1dGVkIHx8IHByb3AubWV0aG9kIHx8IHByb3Auc2hvcnRoYW5kKSlyZXR1cm47dmFyIGtleT1wcm9wLmtleSxuYW1lPXVuZGVmaW5lZDtzd2l0Y2goa2V5LnR5cGUpe2Nhc2UgXCJJZGVudGlmaWVyXCI6bmFtZSA9IGtleS5uYW1lO2JyZWFrO2Nhc2UgXCJMaXRlcmFsXCI6bmFtZSA9IFN0cmluZyhrZXkudmFsdWUpO2JyZWFrO2RlZmF1bHQ6cmV0dXJuO312YXIga2luZD1wcm9wLmtpbmQ7aWYodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYpe2lmKG5hbWUgPT09IFwiX19wcm90b19fXCIgJiYga2luZCA9PT0gXCJpbml0XCIpe2lmKHByb3BIYXNoLnByb3RvKXRoaXMucmFpc2Uoa2V5LnN0YXJ0LFwiUmVkZWZpbml0aW9uIG9mIF9fcHJvdG9fXyBwcm9wZXJ0eVwiKTtwcm9wSGFzaC5wcm90byA9IHRydWU7fXJldHVybjt9dmFyIG90aGVyPXVuZGVmaW5lZDtpZihfdXRpbC5oYXMocHJvcEhhc2gsbmFtZSkpe290aGVyID0gcHJvcEhhc2hbbmFtZV07dmFyIGlzR2V0U2V0PWtpbmQgIT09IFwiaW5pdFwiO2lmKCh0aGlzLnN0cmljdCB8fCBpc0dldFNldCkgJiYgb3RoZXJba2luZF0gfHwgIShpc0dldFNldCBeIG90aGVyLmluaXQpKXRoaXMucmFpc2Uoa2V5LnN0YXJ0LFwiUmVkZWZpbml0aW9uIG9mIHByb3BlcnR5XCIpO31lbHNlIHtvdGhlciA9IHByb3BIYXNoW25hbWVdID0ge2luaXQ6ZmFsc2UsZ2V0OmZhbHNlLHNldDpmYWxzZX07fW90aGVyW2tpbmRdID0gdHJ1ZTt9OyAvLyAjIyMgRXhwcmVzc2lvbiBwYXJzaW5nXG4vLyBUaGVzZSBuZXN0LCBmcm9tIHRoZSBtb3N0IGdlbmVyYWwgZXhwcmVzc2lvbiB0eXBlIGF0IHRoZSB0b3AgdG9cbi8vICdhdG9taWMnLCBub25kaXZpc2libGUgZXhwcmVzc2lvbiB0eXBlcyBhdCB0aGUgYm90dG9tLiBNb3N0IG9mXG4vLyB0aGUgZnVuY3Rpb25zIHdpbGwgc2ltcGx5IGxldCB0aGUgZnVuY3Rpb24ocykgYmVsb3cgdGhlbSBwYXJzZSxcbi8vIGFuZCwgKmlmKiB0aGUgc3ludGFjdGljIGNvbnN0cnVjdCB0aGV5IGhhbmRsZSBpcyBwcmVzZW50LCB3cmFwXG4vLyB0aGUgQVNUIG5vZGUgdGhhdCB0aGUgaW5uZXIgcGFyc2VyIGdhdmUgdGhlbSBpbiBhbm90aGVyIG5vZGUuXG4vLyBQYXJzZSBhIGZ1bGwgZXhwcmVzc2lvbi4gVGhlIG9wdGlvbmFsIGFyZ3VtZW50cyBhcmUgdXNlZCB0b1xuLy8gZm9yYmlkIHRoZSBgaW5gIG9wZXJhdG9yIChpbiBmb3IgbG9vcHMgaW5pdGFsaXphdGlvbiBleHByZXNzaW9ucylcbi8vIGFuZCBwcm92aWRlIHJlZmVyZW5jZSBmb3Igc3RvcmluZyAnPScgb3BlcmF0b3IgaW5zaWRlIHNob3J0aGFuZFxuLy8gcHJvcGVydHkgYXNzaWdubWVudCBpbiBjb250ZXh0cyB3aGVyZSBib3RoIG9iamVjdCBleHByZXNzaW9uXG4vLyBhbmQgb2JqZWN0IHBhdHRlcm4gbWlnaHQgYXBwZWFyIChzbyBpdCdzIHBvc3NpYmxlIHRvIHJhaXNlXG4vLyBkZWxheWVkIHN5bnRheCBlcnJvciBhdCBjb3JyZWN0IHBvc2l0aW9uKS5cbnBwLnBhcnNlRXhwcmVzc2lvbiA9IGZ1bmN0aW9uKG5vSW4scmVmU2hvcnRoYW5kRGVmYXVsdFBvcyl7dmFyIHN0YXJ0UG9zPXRoaXMuc3RhcnQsc3RhcnRMb2M9dGhpcy5zdGFydExvYzt2YXIgZXhwcj10aGlzLnBhcnNlTWF5YmVBc3NpZ24obm9JbixyZWZTaG9ydGhhbmREZWZhdWx0UG9zKTtpZih0aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuY29tbWEpe3ZhciBub2RlPXRoaXMuc3RhcnROb2RlQXQoc3RhcnRQb3Msc3RhcnRMb2MpO25vZGUuZXhwcmVzc2lvbnMgPSBbZXhwcl07d2hpbGUodGhpcy5lYXQoX3Rva2VudHlwZS50eXBlcy5jb21tYSkpIG5vZGUuZXhwcmVzc2lvbnMucHVzaCh0aGlzLnBhcnNlTWF5YmVBc3NpZ24obm9JbixyZWZTaG9ydGhhbmREZWZhdWx0UG9zKSk7cmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLFwiU2VxdWVuY2VFeHByZXNzaW9uXCIpO31yZXR1cm4gZXhwcjt9OyAvLyBQYXJzZSBhbiBhc3NpZ25tZW50IGV4cHJlc3Npb24uIFRoaXMgaW5jbHVkZXMgYXBwbGljYXRpb25zIG9mXG4vLyBvcGVyYXRvcnMgbGlrZSBgKz1gLlxucHAucGFyc2VNYXliZUFzc2lnbiA9IGZ1bmN0aW9uKG5vSW4scmVmU2hvcnRoYW5kRGVmYXVsdFBvcyxhZnRlckxlZnRQYXJzZSl7aWYodGhpcy50eXBlID09IF90b2tlbnR5cGUudHlwZXMuX3lpZWxkICYmIHRoaXMuaW5HZW5lcmF0b3IpcmV0dXJuIHRoaXMucGFyc2VZaWVsZCgpO3ZhciBmYWlsT25TaG9ydGhhbmRBc3NpZ249dW5kZWZpbmVkO2lmKCFyZWZTaG9ydGhhbmREZWZhdWx0UG9zKXtyZWZTaG9ydGhhbmREZWZhdWx0UG9zID0ge3N0YXJ0OjB9O2ZhaWxPblNob3J0aGFuZEFzc2lnbiA9IHRydWU7fWVsc2Uge2ZhaWxPblNob3J0aGFuZEFzc2lnbiA9IGZhbHNlO312YXIgc3RhcnRQb3M9dGhpcy5zdGFydCxzdGFydExvYz10aGlzLnN0YXJ0TG9jO2lmKHRoaXMudHlwZSA9PSBfdG9rZW50eXBlLnR5cGVzLnBhcmVuTCB8fCB0aGlzLnR5cGUgPT0gX3Rva2VudHlwZS50eXBlcy5uYW1lKXRoaXMucG90ZW50aWFsQXJyb3dBdCA9IHRoaXMuc3RhcnQ7dmFyIGxlZnQ9dGhpcy5wYXJzZU1heWJlQ29uZGl0aW9uYWwobm9JbixyZWZTaG9ydGhhbmREZWZhdWx0UG9zKTtpZihhZnRlckxlZnRQYXJzZSlsZWZ0ID0gYWZ0ZXJMZWZ0UGFyc2UuY2FsbCh0aGlzLGxlZnQsc3RhcnRQb3Msc3RhcnRMb2MpO2lmKHRoaXMudHlwZS5pc0Fzc2lnbil7dmFyIG5vZGU9dGhpcy5zdGFydE5vZGVBdChzdGFydFBvcyxzdGFydExvYyk7bm9kZS5vcGVyYXRvciA9IHRoaXMudmFsdWU7bm9kZS5sZWZ0ID0gdGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLmVxP3RoaXMudG9Bc3NpZ25hYmxlKGxlZnQpOmxlZnQ7cmVmU2hvcnRoYW5kRGVmYXVsdFBvcy5zdGFydCA9IDA7IC8vIHJlc2V0IGJlY2F1c2Ugc2hvcnRoYW5kIGRlZmF1bHQgd2FzIHVzZWQgY29ycmVjdGx5XG50aGlzLmNoZWNrTFZhbChsZWZ0KTt0aGlzLm5leHQoKTtub2RlLnJpZ2h0ID0gdGhpcy5wYXJzZU1heWJlQXNzaWduKG5vSW4pO3JldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSxcIkFzc2lnbm1lbnRFeHByZXNzaW9uXCIpO31lbHNlIGlmKGZhaWxPblNob3J0aGFuZEFzc2lnbiAmJiByZWZTaG9ydGhhbmREZWZhdWx0UG9zLnN0YXJ0KXt0aGlzLnVuZXhwZWN0ZWQocmVmU2hvcnRoYW5kRGVmYXVsdFBvcy5zdGFydCk7fXJldHVybiBsZWZ0O307IC8vIFBhcnNlIGEgdGVybmFyeSBjb25kaXRpb25hbCAoYD86YCkgb3BlcmF0b3IuXG5wcC5wYXJzZU1heWJlQ29uZGl0aW9uYWwgPSBmdW5jdGlvbihub0luLHJlZlNob3J0aGFuZERlZmF1bHRQb3Mpe3ZhciBzdGFydFBvcz10aGlzLnN0YXJ0LHN0YXJ0TG9jPXRoaXMuc3RhcnRMb2M7dmFyIGV4cHI9dGhpcy5wYXJzZUV4cHJPcHMobm9JbixyZWZTaG9ydGhhbmREZWZhdWx0UG9zKTtpZihyZWZTaG9ydGhhbmREZWZhdWx0UG9zICYmIHJlZlNob3J0aGFuZERlZmF1bHRQb3Muc3RhcnQpcmV0dXJuIGV4cHI7aWYodGhpcy5lYXQoX3Rva2VudHlwZS50eXBlcy5xdWVzdGlvbikpe3ZhciBub2RlPXRoaXMuc3RhcnROb2RlQXQoc3RhcnRQb3Msc3RhcnRMb2MpO25vZGUudGVzdCA9IGV4cHI7bm9kZS5jb25zZXF1ZW50ID0gdGhpcy5wYXJzZU1heWJlQXNzaWduKCk7dGhpcy5leHBlY3QoX3Rva2VudHlwZS50eXBlcy5jb2xvbik7bm9kZS5hbHRlcm5hdGUgPSB0aGlzLnBhcnNlTWF5YmVBc3NpZ24obm9Jbik7cmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLFwiQ29uZGl0aW9uYWxFeHByZXNzaW9uXCIpO31yZXR1cm4gZXhwcjt9OyAvLyBTdGFydCB0aGUgcHJlY2VkZW5jZSBwYXJzZXIuXG5wcC5wYXJzZUV4cHJPcHMgPSBmdW5jdGlvbihub0luLHJlZlNob3J0aGFuZERlZmF1bHRQb3Mpe3ZhciBzdGFydFBvcz10aGlzLnN0YXJ0LHN0YXJ0TG9jPXRoaXMuc3RhcnRMb2M7dmFyIGV4cHI9dGhpcy5wYXJzZU1heWJlVW5hcnkocmVmU2hvcnRoYW5kRGVmYXVsdFBvcyk7aWYocmVmU2hvcnRoYW5kRGVmYXVsdFBvcyAmJiByZWZTaG9ydGhhbmREZWZhdWx0UG9zLnN0YXJ0KXJldHVybiBleHByO3JldHVybiB0aGlzLnBhcnNlRXhwck9wKGV4cHIsc3RhcnRQb3Msc3RhcnRMb2MsLTEsbm9Jbik7fTsgLy8gUGFyc2UgYmluYXJ5IG9wZXJhdG9ycyB3aXRoIHRoZSBvcGVyYXRvciBwcmVjZWRlbmNlIHBhcnNpbmdcbi8vIGFsZ29yaXRobS4gYGxlZnRgIGlzIHRoZSBsZWZ0LWhhbmQgc2lkZSBvZiB0aGUgb3BlcmF0b3IuXG4vLyBgbWluUHJlY2AgcHJvdmlkZXMgY29udGV4dCB0aGF0IGFsbG93cyB0aGUgZnVuY3Rpb24gdG8gc3RvcCBhbmRcbi8vIGRlZmVyIGZ1cnRoZXIgcGFyc2VyIHRvIG9uZSBvZiBpdHMgY2FsbGVycyB3aGVuIGl0IGVuY291bnRlcnMgYW5cbi8vIG9wZXJhdG9yIHRoYXQgaGFzIGEgbG93ZXIgcHJlY2VkZW5jZSB0aGFuIHRoZSBzZXQgaXQgaXMgcGFyc2luZy5cbnBwLnBhcnNlRXhwck9wID0gZnVuY3Rpb24obGVmdCxsZWZ0U3RhcnRQb3MsbGVmdFN0YXJ0TG9jLG1pblByZWMsbm9Jbil7dmFyIHByZWM9dGhpcy50eXBlLmJpbm9wO2lmKHByZWMgIT0gbnVsbCAmJiAoIW5vSW4gfHwgdGhpcy50eXBlICE9PSBfdG9rZW50eXBlLnR5cGVzLl9pbikpe2lmKHByZWMgPiBtaW5QcmVjKXt2YXIgbm9kZT10aGlzLnN0YXJ0Tm9kZUF0KGxlZnRTdGFydFBvcyxsZWZ0U3RhcnRMb2MpO25vZGUubGVmdCA9IGxlZnQ7bm9kZS5vcGVyYXRvciA9IHRoaXMudmFsdWU7dmFyIG9wPXRoaXMudHlwZTt0aGlzLm5leHQoKTt2YXIgc3RhcnRQb3M9dGhpcy5zdGFydCxzdGFydExvYz10aGlzLnN0YXJ0TG9jO25vZGUucmlnaHQgPSB0aGlzLnBhcnNlRXhwck9wKHRoaXMucGFyc2VNYXliZVVuYXJ5KCksc3RhcnRQb3Msc3RhcnRMb2MscHJlYyxub0luKTt0aGlzLmZpbmlzaE5vZGUobm9kZSxvcCA9PT0gX3Rva2VudHlwZS50eXBlcy5sb2dpY2FsT1IgfHwgb3AgPT09IF90b2tlbnR5cGUudHlwZXMubG9naWNhbEFORD9cIkxvZ2ljYWxFeHByZXNzaW9uXCI6XCJCaW5hcnlFeHByZXNzaW9uXCIpO3JldHVybiB0aGlzLnBhcnNlRXhwck9wKG5vZGUsbGVmdFN0YXJ0UG9zLGxlZnRTdGFydExvYyxtaW5QcmVjLG5vSW4pO319cmV0dXJuIGxlZnQ7fTsgLy8gUGFyc2UgdW5hcnkgb3BlcmF0b3JzLCBib3RoIHByZWZpeCBhbmQgcG9zdGZpeC5cbnBwLnBhcnNlTWF5YmVVbmFyeSA9IGZ1bmN0aW9uKHJlZlNob3J0aGFuZERlZmF1bHRQb3Mpe2lmKHRoaXMudHlwZS5wcmVmaXgpe3ZhciBub2RlPXRoaXMuc3RhcnROb2RlKCksdXBkYXRlPXRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5pbmNEZWM7bm9kZS5vcGVyYXRvciA9IHRoaXMudmFsdWU7bm9kZS5wcmVmaXggPSB0cnVlO3RoaXMubmV4dCgpO25vZGUuYXJndW1lbnQgPSB0aGlzLnBhcnNlTWF5YmVVbmFyeSgpO2lmKHJlZlNob3J0aGFuZERlZmF1bHRQb3MgJiYgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcy5zdGFydCl0aGlzLnVuZXhwZWN0ZWQocmVmU2hvcnRoYW5kRGVmYXVsdFBvcy5zdGFydCk7aWYodXBkYXRlKXRoaXMuY2hlY2tMVmFsKG5vZGUuYXJndW1lbnQpO2Vsc2UgaWYodGhpcy5zdHJpY3QgJiYgbm9kZS5vcGVyYXRvciA9PT0gXCJkZWxldGVcIiAmJiBub2RlLmFyZ3VtZW50LnR5cGUgPT09IFwiSWRlbnRpZmllclwiKXRoaXMucmFpc2Uobm9kZS5zdGFydCxcIkRlbGV0aW5nIGxvY2FsIHZhcmlhYmxlIGluIHN0cmljdCBtb2RlXCIpO3JldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSx1cGRhdGU/XCJVcGRhdGVFeHByZXNzaW9uXCI6XCJVbmFyeUV4cHJlc3Npb25cIik7fXZhciBzdGFydFBvcz10aGlzLnN0YXJ0LHN0YXJ0TG9jPXRoaXMuc3RhcnRMb2M7dmFyIGV4cHI9dGhpcy5wYXJzZUV4cHJTdWJzY3JpcHRzKHJlZlNob3J0aGFuZERlZmF1bHRQb3MpO2lmKHJlZlNob3J0aGFuZERlZmF1bHRQb3MgJiYgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcy5zdGFydClyZXR1cm4gZXhwcjt3aGlsZSh0aGlzLnR5cGUucG9zdGZpeCAmJiAhdGhpcy5jYW5JbnNlcnRTZW1pY29sb24oKSkge3ZhciBub2RlPXRoaXMuc3RhcnROb2RlQXQoc3RhcnRQb3Msc3RhcnRMb2MpO25vZGUub3BlcmF0b3IgPSB0aGlzLnZhbHVlO25vZGUucHJlZml4ID0gZmFsc2U7bm9kZS5hcmd1bWVudCA9IGV4cHI7dGhpcy5jaGVja0xWYWwoZXhwcik7dGhpcy5uZXh0KCk7ZXhwciA9IHRoaXMuZmluaXNoTm9kZShub2RlLFwiVXBkYXRlRXhwcmVzc2lvblwiKTt9cmV0dXJuIGV4cHI7fTsgLy8gUGFyc2UgY2FsbCwgZG90LCBhbmQgYFtdYC1zdWJzY3JpcHQgZXhwcmVzc2lvbnMuXG5wcC5wYXJzZUV4cHJTdWJzY3JpcHRzID0gZnVuY3Rpb24ocmVmU2hvcnRoYW5kRGVmYXVsdFBvcyl7dmFyIHN0YXJ0UG9zPXRoaXMuc3RhcnQsc3RhcnRMb2M9dGhpcy5zdGFydExvYzt2YXIgZXhwcj10aGlzLnBhcnNlRXhwckF0b20ocmVmU2hvcnRoYW5kRGVmYXVsdFBvcyk7aWYocmVmU2hvcnRoYW5kRGVmYXVsdFBvcyAmJiByZWZTaG9ydGhhbmREZWZhdWx0UG9zLnN0YXJ0KXJldHVybiBleHByO3JldHVybiB0aGlzLnBhcnNlU3Vic2NyaXB0cyhleHByLHN0YXJ0UG9zLHN0YXJ0TG9jKTt9O3BwLnBhcnNlU3Vic2NyaXB0cyA9IGZ1bmN0aW9uKGJhc2Usc3RhcnRQb3Msc3RhcnRMb2Msbm9DYWxscyl7Zm9yKDs7KSB7aWYodGhpcy5lYXQoX3Rva2VudHlwZS50eXBlcy5kb3QpKXt2YXIgbm9kZT10aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0UG9zLHN0YXJ0TG9jKTtub2RlLm9iamVjdCA9IGJhc2U7bm9kZS5wcm9wZXJ0eSA9IHRoaXMucGFyc2VJZGVudCh0cnVlKTtub2RlLmNvbXB1dGVkID0gZmFsc2U7YmFzZSA9IHRoaXMuZmluaXNoTm9kZShub2RlLFwiTWVtYmVyRXhwcmVzc2lvblwiKTt9ZWxzZSBpZih0aGlzLmVhdChfdG9rZW50eXBlLnR5cGVzLmJyYWNrZXRMKSl7dmFyIG5vZGU9dGhpcy5zdGFydE5vZGVBdChzdGFydFBvcyxzdGFydExvYyk7bm9kZS5vYmplY3QgPSBiYXNlO25vZGUucHJvcGVydHkgPSB0aGlzLnBhcnNlRXhwcmVzc2lvbigpO25vZGUuY29tcHV0ZWQgPSB0cnVlO3RoaXMuZXhwZWN0KF90b2tlbnR5cGUudHlwZXMuYnJhY2tldFIpO2Jhc2UgPSB0aGlzLmZpbmlzaE5vZGUobm9kZSxcIk1lbWJlckV4cHJlc3Npb25cIik7fWVsc2UgaWYoIW5vQ2FsbHMgJiYgdGhpcy5lYXQoX3Rva2VudHlwZS50eXBlcy5wYXJlbkwpKXt2YXIgbm9kZT10aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0UG9zLHN0YXJ0TG9jKTtub2RlLmNhbGxlZSA9IGJhc2U7bm9kZS5hcmd1bWVudHMgPSB0aGlzLnBhcnNlRXhwckxpc3QoX3Rva2VudHlwZS50eXBlcy5wYXJlblIsZmFsc2UpO2Jhc2UgPSB0aGlzLmZpbmlzaE5vZGUobm9kZSxcIkNhbGxFeHByZXNzaW9uXCIpO31lbHNlIGlmKHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5iYWNrUXVvdGUpe3ZhciBub2RlPXRoaXMuc3RhcnROb2RlQXQoc3RhcnRQb3Msc3RhcnRMb2MpO25vZGUudGFnID0gYmFzZTtub2RlLnF1YXNpID0gdGhpcy5wYXJzZVRlbXBsYXRlKCk7YmFzZSA9IHRoaXMuZmluaXNoTm9kZShub2RlLFwiVGFnZ2VkVGVtcGxhdGVFeHByZXNzaW9uXCIpO31lbHNlIHtyZXR1cm4gYmFzZTt9fX07IC8vIFBhcnNlIGFuIGF0b21pYyBleHByZXNzaW9uIOKAlCBlaXRoZXIgYSBzaW5nbGUgdG9rZW4gdGhhdCBpcyBhblxuLy8gZXhwcmVzc2lvbiwgYW4gZXhwcmVzc2lvbiBzdGFydGVkIGJ5IGEga2V5d29yZCBsaWtlIGBmdW5jdGlvbmAgb3Jcbi8vIGBuZXdgLCBvciBhbiBleHByZXNzaW9uIHdyYXBwZWQgaW4gcHVuY3R1YXRpb24gbGlrZSBgKClgLCBgW11gLFxuLy8gb3IgYHt9YC5cbnBwLnBhcnNlRXhwckF0b20gPSBmdW5jdGlvbihyZWZTaG9ydGhhbmREZWZhdWx0UG9zKXt2YXIgbm9kZT11bmRlZmluZWQsY2FuQmVBcnJvdz10aGlzLnBvdGVudGlhbEFycm93QXQgPT0gdGhpcy5zdGFydDtzd2l0Y2godGhpcy50eXBlKXtjYXNlIF90b2tlbnR5cGUudHlwZXMuX3N1cGVyOmlmKCF0aGlzLmluRnVuY3Rpb24pdGhpcy5yYWlzZSh0aGlzLnN0YXJ0LFwiJ3N1cGVyJyBvdXRzaWRlIG9mIGZ1bmN0aW9uIG9yIGNsYXNzXCIpO2Nhc2UgX3Rva2VudHlwZS50eXBlcy5fdGhpczp2YXIgdHlwZT10aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuX3RoaXM/XCJUaGlzRXhwcmVzc2lvblwiOlwiU3VwZXJcIjtub2RlID0gdGhpcy5zdGFydE5vZGUoKTt0aGlzLm5leHQoKTtyZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsdHlwZSk7Y2FzZSBfdG9rZW50eXBlLnR5cGVzLl95aWVsZDppZih0aGlzLmluR2VuZXJhdG9yKXRoaXMudW5leHBlY3RlZCgpO2Nhc2UgX3Rva2VudHlwZS50eXBlcy5uYW1lOnZhciBzdGFydFBvcz10aGlzLnN0YXJ0LHN0YXJ0TG9jPXRoaXMuc3RhcnRMb2M7dmFyIGlkPXRoaXMucGFyc2VJZGVudCh0aGlzLnR5cGUgIT09IF90b2tlbnR5cGUudHlwZXMubmFtZSk7aWYoY2FuQmVBcnJvdyAmJiAhdGhpcy5jYW5JbnNlcnRTZW1pY29sb24oKSAmJiB0aGlzLmVhdChfdG9rZW50eXBlLnR5cGVzLmFycm93KSlyZXR1cm4gdGhpcy5wYXJzZUFycm93RXhwcmVzc2lvbih0aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0UG9zLHN0YXJ0TG9jKSxbaWRdKTtyZXR1cm4gaWQ7Y2FzZSBfdG9rZW50eXBlLnR5cGVzLnJlZ2V4cDp2YXIgdmFsdWU9dGhpcy52YWx1ZTtub2RlID0gdGhpcy5wYXJzZUxpdGVyYWwodmFsdWUudmFsdWUpO25vZGUucmVnZXggPSB7cGF0dGVybjp2YWx1ZS5wYXR0ZXJuLGZsYWdzOnZhbHVlLmZsYWdzfTtyZXR1cm4gbm9kZTtjYXNlIF90b2tlbnR5cGUudHlwZXMubnVtOmNhc2UgX3Rva2VudHlwZS50eXBlcy5zdHJpbmc6cmV0dXJuIHRoaXMucGFyc2VMaXRlcmFsKHRoaXMudmFsdWUpO2Nhc2UgX3Rva2VudHlwZS50eXBlcy5fbnVsbDpjYXNlIF90b2tlbnR5cGUudHlwZXMuX3RydWU6Y2FzZSBfdG9rZW50eXBlLnR5cGVzLl9mYWxzZTpub2RlID0gdGhpcy5zdGFydE5vZGUoKTtub2RlLnZhbHVlID0gdGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLl9udWxsP251bGw6dGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLl90cnVlO25vZGUucmF3ID0gdGhpcy50eXBlLmtleXdvcmQ7dGhpcy5uZXh0KCk7cmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLFwiTGl0ZXJhbFwiKTtjYXNlIF90b2tlbnR5cGUudHlwZXMucGFyZW5MOnJldHVybiB0aGlzLnBhcnNlUGFyZW5BbmREaXN0aW5ndWlzaEV4cHJlc3Npb24oY2FuQmVBcnJvdyk7Y2FzZSBfdG9rZW50eXBlLnR5cGVzLmJyYWNrZXRMOm5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO3RoaXMubmV4dCgpOyAvLyBjaGVjayB3aGV0aGVyIHRoaXMgaXMgYXJyYXkgY29tcHJlaGVuc2lvbiBvciByZWd1bGFyIGFycmF5XG5pZih0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNyAmJiB0aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuX2Zvcil7cmV0dXJuIHRoaXMucGFyc2VDb21wcmVoZW5zaW9uKG5vZGUsZmFsc2UpO31ub2RlLmVsZW1lbnRzID0gdGhpcy5wYXJzZUV4cHJMaXN0KF90b2tlbnR5cGUudHlwZXMuYnJhY2tldFIsdHJ1ZSx0cnVlLHJlZlNob3J0aGFuZERlZmF1bHRQb3MpO3JldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSxcIkFycmF5RXhwcmVzc2lvblwiKTtjYXNlIF90b2tlbnR5cGUudHlwZXMuYnJhY2VMOnJldHVybiB0aGlzLnBhcnNlT2JqKGZhbHNlLHJlZlNob3J0aGFuZERlZmF1bHRQb3MpO2Nhc2UgX3Rva2VudHlwZS50eXBlcy5fZnVuY3Rpb246bm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7dGhpcy5uZXh0KCk7cmV0dXJuIHRoaXMucGFyc2VGdW5jdGlvbihub2RlLGZhbHNlKTtjYXNlIF90b2tlbnR5cGUudHlwZXMuX2NsYXNzOnJldHVybiB0aGlzLnBhcnNlQ2xhc3ModGhpcy5zdGFydE5vZGUoKSxmYWxzZSk7Y2FzZSBfdG9rZW50eXBlLnR5cGVzLl9uZXc6cmV0dXJuIHRoaXMucGFyc2VOZXcoKTtjYXNlIF90b2tlbnR5cGUudHlwZXMuYmFja1F1b3RlOnJldHVybiB0aGlzLnBhcnNlVGVtcGxhdGUoKTtkZWZhdWx0OnRoaXMudW5leHBlY3RlZCgpO319O3BwLnBhcnNlTGl0ZXJhbCA9IGZ1bmN0aW9uKHZhbHVlKXt2YXIgbm9kZT10aGlzLnN0YXJ0Tm9kZSgpO25vZGUudmFsdWUgPSB2YWx1ZTtub2RlLnJhdyA9IHRoaXMuaW5wdXQuc2xpY2UodGhpcy5zdGFydCx0aGlzLmVuZCk7dGhpcy5uZXh0KCk7cmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLFwiTGl0ZXJhbFwiKTt9O3BwLnBhcnNlUGFyZW5FeHByZXNzaW9uID0gZnVuY3Rpb24oKXt0aGlzLmV4cGVjdChfdG9rZW50eXBlLnR5cGVzLnBhcmVuTCk7dmFyIHZhbD10aGlzLnBhcnNlRXhwcmVzc2lvbigpO3RoaXMuZXhwZWN0KF90b2tlbnR5cGUudHlwZXMucGFyZW5SKTtyZXR1cm4gdmFsO307cHAucGFyc2VQYXJlbkFuZERpc3Rpbmd1aXNoRXhwcmVzc2lvbiA9IGZ1bmN0aW9uKGNhbkJlQXJyb3cpe3ZhciBzdGFydFBvcz10aGlzLnN0YXJ0LHN0YXJ0TG9jPXRoaXMuc3RhcnRMb2MsdmFsPXVuZGVmaW5lZDtpZih0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNil7dGhpcy5uZXh0KCk7aWYodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDcgJiYgdGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLl9mb3Ipe3JldHVybiB0aGlzLnBhcnNlQ29tcHJlaGVuc2lvbih0aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0UG9zLHN0YXJ0TG9jKSx0cnVlKTt9dmFyIGlubmVyU3RhcnRQb3M9dGhpcy5zdGFydCxpbm5lclN0YXJ0TG9jPXRoaXMuc3RhcnRMb2M7dmFyIGV4cHJMaXN0PVtdLGZpcnN0PXRydWU7dmFyIHJlZlNob3J0aGFuZERlZmF1bHRQb3M9e3N0YXJ0OjB9LHNwcmVhZFN0YXJ0PXVuZGVmaW5lZCxpbm5lclBhcmVuU3RhcnQ9dW5kZWZpbmVkO3doaWxlKHRoaXMudHlwZSAhPT0gX3Rva2VudHlwZS50eXBlcy5wYXJlblIpIHtmaXJzdD9maXJzdCA9IGZhbHNlOnRoaXMuZXhwZWN0KF90b2tlbnR5cGUudHlwZXMuY29tbWEpO2lmKHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5lbGxpcHNpcyl7c3ByZWFkU3RhcnQgPSB0aGlzLnN0YXJ0O2V4cHJMaXN0LnB1c2godGhpcy5wYXJzZVBhcmVuSXRlbSh0aGlzLnBhcnNlUmVzdCgpKSk7YnJlYWs7fWVsc2Uge2lmKHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5wYXJlbkwgJiYgIWlubmVyUGFyZW5TdGFydCl7aW5uZXJQYXJlblN0YXJ0ID0gdGhpcy5zdGFydDt9ZXhwckxpc3QucHVzaCh0aGlzLnBhcnNlTWF5YmVBc3NpZ24oZmFsc2UscmVmU2hvcnRoYW5kRGVmYXVsdFBvcyx0aGlzLnBhcnNlUGFyZW5JdGVtKSk7fX12YXIgaW5uZXJFbmRQb3M9dGhpcy5zdGFydCxpbm5lckVuZExvYz10aGlzLnN0YXJ0TG9jO3RoaXMuZXhwZWN0KF90b2tlbnR5cGUudHlwZXMucGFyZW5SKTtpZihjYW5CZUFycm93ICYmICF0aGlzLmNhbkluc2VydFNlbWljb2xvbigpICYmIHRoaXMuZWF0KF90b2tlbnR5cGUudHlwZXMuYXJyb3cpKXtpZihpbm5lclBhcmVuU3RhcnQpdGhpcy51bmV4cGVjdGVkKGlubmVyUGFyZW5TdGFydCk7cmV0dXJuIHRoaXMucGFyc2VQYXJlbkFycm93TGlzdChzdGFydFBvcyxzdGFydExvYyxleHByTGlzdCk7fWlmKCFleHByTGlzdC5sZW5ndGgpdGhpcy51bmV4cGVjdGVkKHRoaXMubGFzdFRva1N0YXJ0KTtpZihzcHJlYWRTdGFydCl0aGlzLnVuZXhwZWN0ZWQoc3ByZWFkU3RhcnQpO2lmKHJlZlNob3J0aGFuZERlZmF1bHRQb3Muc3RhcnQpdGhpcy51bmV4cGVjdGVkKHJlZlNob3J0aGFuZERlZmF1bHRQb3Muc3RhcnQpO2lmKGV4cHJMaXN0Lmxlbmd0aCA+IDEpe3ZhbCA9IHRoaXMuc3RhcnROb2RlQXQoaW5uZXJTdGFydFBvcyxpbm5lclN0YXJ0TG9jKTt2YWwuZXhwcmVzc2lvbnMgPSBleHByTGlzdDt0aGlzLmZpbmlzaE5vZGVBdCh2YWwsXCJTZXF1ZW5jZUV4cHJlc3Npb25cIixpbm5lckVuZFBvcyxpbm5lckVuZExvYyk7fWVsc2Uge3ZhbCA9IGV4cHJMaXN0WzBdO319ZWxzZSB7dmFsID0gdGhpcy5wYXJzZVBhcmVuRXhwcmVzc2lvbigpO31pZih0aGlzLm9wdGlvbnMucHJlc2VydmVQYXJlbnMpe3ZhciBwYXI9dGhpcy5zdGFydE5vZGVBdChzdGFydFBvcyxzdGFydExvYyk7cGFyLmV4cHJlc3Npb24gPSB2YWw7cmV0dXJuIHRoaXMuZmluaXNoTm9kZShwYXIsXCJQYXJlbnRoZXNpemVkRXhwcmVzc2lvblwiKTt9ZWxzZSB7cmV0dXJuIHZhbDt9fTtwcC5wYXJzZVBhcmVuSXRlbSA9IGZ1bmN0aW9uKGl0ZW0pe3JldHVybiBpdGVtO307cHAucGFyc2VQYXJlbkFycm93TGlzdCA9IGZ1bmN0aW9uKHN0YXJ0UG9zLHN0YXJ0TG9jLGV4cHJMaXN0KXtyZXR1cm4gdGhpcy5wYXJzZUFycm93RXhwcmVzc2lvbih0aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0UG9zLHN0YXJ0TG9jKSxleHByTGlzdCk7fTsgLy8gTmV3J3MgcHJlY2VkZW5jZSBpcyBzbGlnaHRseSB0cmlja3kuIEl0IG11c3QgYWxsb3cgaXRzIGFyZ3VtZW50XG4vLyB0byBiZSBhIGBbXWAgb3IgZG90IHN1YnNjcmlwdCBleHByZXNzaW9uLCBidXQgbm90IGEgY2FsbCDigJQgYXRcbi8vIGxlYXN0LCBub3Qgd2l0aG91dCB3cmFwcGluZyBpdCBpbiBwYXJlbnRoZXNlcy4gVGh1cywgaXQgdXNlcyB0aGVcbnZhciBlbXB0eT1bXTtwcC5wYXJzZU5ldyA9IGZ1bmN0aW9uKCl7dmFyIG5vZGU9dGhpcy5zdGFydE5vZGUoKTt2YXIgbWV0YT10aGlzLnBhcnNlSWRlbnQodHJ1ZSk7aWYodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYgJiYgdGhpcy5lYXQoX3Rva2VudHlwZS50eXBlcy5kb3QpKXtub2RlLm1ldGEgPSBtZXRhO25vZGUucHJvcGVydHkgPSB0aGlzLnBhcnNlSWRlbnQodHJ1ZSk7aWYobm9kZS5wcm9wZXJ0eS5uYW1lICE9PSBcInRhcmdldFwiKXRoaXMucmFpc2Uobm9kZS5wcm9wZXJ0eS5zdGFydCxcIlRoZSBvbmx5IHZhbGlkIG1ldGEgcHJvcGVydHkgZm9yIG5ldyBpcyBuZXcudGFyZ2V0XCIpO3JldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSxcIk1ldGFQcm9wZXJ0eVwiKTt9dmFyIHN0YXJ0UG9zPXRoaXMuc3RhcnQsc3RhcnRMb2M9dGhpcy5zdGFydExvYztub2RlLmNhbGxlZSA9IHRoaXMucGFyc2VTdWJzY3JpcHRzKHRoaXMucGFyc2VFeHByQXRvbSgpLHN0YXJ0UG9zLHN0YXJ0TG9jLHRydWUpO2lmKHRoaXMuZWF0KF90b2tlbnR5cGUudHlwZXMucGFyZW5MKSlub2RlLmFyZ3VtZW50cyA9IHRoaXMucGFyc2VFeHByTGlzdChfdG9rZW50eXBlLnR5cGVzLnBhcmVuUixmYWxzZSk7ZWxzZSBub2RlLmFyZ3VtZW50cyA9IGVtcHR5O3JldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSxcIk5ld0V4cHJlc3Npb25cIik7fTsgLy8gUGFyc2UgdGVtcGxhdGUgZXhwcmVzc2lvbi5cbnBwLnBhcnNlVGVtcGxhdGVFbGVtZW50ID0gZnVuY3Rpb24oKXt2YXIgZWxlbT10aGlzLnN0YXJ0Tm9kZSgpO2VsZW0udmFsdWUgPSB7cmF3OnRoaXMuaW5wdXQuc2xpY2UodGhpcy5zdGFydCx0aGlzLmVuZCkucmVwbGFjZSgvXFxyXFxuPy9nLCdcXG4nKSxjb29rZWQ6dGhpcy52YWx1ZX07dGhpcy5uZXh0KCk7ZWxlbS50YWlsID0gdGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLmJhY2tRdW90ZTtyZXR1cm4gdGhpcy5maW5pc2hOb2RlKGVsZW0sXCJUZW1wbGF0ZUVsZW1lbnRcIik7fTtwcC5wYXJzZVRlbXBsYXRlID0gZnVuY3Rpb24oKXt2YXIgbm9kZT10aGlzLnN0YXJ0Tm9kZSgpO3RoaXMubmV4dCgpO25vZGUuZXhwcmVzc2lvbnMgPSBbXTt2YXIgY3VyRWx0PXRoaXMucGFyc2VUZW1wbGF0ZUVsZW1lbnQoKTtub2RlLnF1YXNpcyA9IFtjdXJFbHRdO3doaWxlKCFjdXJFbHQudGFpbCkge3RoaXMuZXhwZWN0KF90b2tlbnR5cGUudHlwZXMuZG9sbGFyQnJhY2VMKTtub2RlLmV4cHJlc3Npb25zLnB1c2godGhpcy5wYXJzZUV4cHJlc3Npb24oKSk7dGhpcy5leHBlY3QoX3Rva2VudHlwZS50eXBlcy5icmFjZVIpO25vZGUucXVhc2lzLnB1c2goY3VyRWx0ID0gdGhpcy5wYXJzZVRlbXBsYXRlRWxlbWVudCgpKTt9dGhpcy5uZXh0KCk7cmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLFwiVGVtcGxhdGVMaXRlcmFsXCIpO307IC8vIFBhcnNlIGFuIG9iamVjdCBsaXRlcmFsIG9yIGJpbmRpbmcgcGF0dGVybi5cbnBwLnBhcnNlT2JqID0gZnVuY3Rpb24oaXNQYXR0ZXJuLHJlZlNob3J0aGFuZERlZmF1bHRQb3Mpe3ZhciBub2RlPXRoaXMuc3RhcnROb2RlKCksZmlyc3Q9dHJ1ZSxwcm9wSGFzaD17fTtub2RlLnByb3BlcnRpZXMgPSBbXTt0aGlzLm5leHQoKTt3aGlsZSghdGhpcy5lYXQoX3Rva2VudHlwZS50eXBlcy5icmFjZVIpKSB7aWYoIWZpcnN0KXt0aGlzLmV4cGVjdChfdG9rZW50eXBlLnR5cGVzLmNvbW1hKTtpZih0aGlzLmFmdGVyVHJhaWxpbmdDb21tYShfdG9rZW50eXBlLnR5cGVzLmJyYWNlUikpYnJlYWs7fWVsc2UgZmlyc3QgPSBmYWxzZTt2YXIgcHJvcD10aGlzLnN0YXJ0Tm9kZSgpLGlzR2VuZXJhdG9yPXVuZGVmaW5lZCxzdGFydFBvcz11bmRlZmluZWQsc3RhcnRMb2M9dW5kZWZpbmVkO2lmKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KXtwcm9wLm1ldGhvZCA9IGZhbHNlO3Byb3Auc2hvcnRoYW5kID0gZmFsc2U7aWYoaXNQYXR0ZXJuIHx8IHJlZlNob3J0aGFuZERlZmF1bHRQb3Mpe3N0YXJ0UG9zID0gdGhpcy5zdGFydDtzdGFydExvYyA9IHRoaXMuc3RhcnRMb2M7fWlmKCFpc1BhdHRlcm4paXNHZW5lcmF0b3IgPSB0aGlzLmVhdChfdG9rZW50eXBlLnR5cGVzLnN0YXIpO310aGlzLnBhcnNlUHJvcGVydHlOYW1lKHByb3ApO3RoaXMucGFyc2VQcm9wZXJ0eVZhbHVlKHByb3AsaXNQYXR0ZXJuLGlzR2VuZXJhdG9yLHN0YXJ0UG9zLHN0YXJ0TG9jLHJlZlNob3J0aGFuZERlZmF1bHRQb3MpO3RoaXMuY2hlY2tQcm9wQ2xhc2gocHJvcCxwcm9wSGFzaCk7bm9kZS5wcm9wZXJ0aWVzLnB1c2godGhpcy5maW5pc2hOb2RlKHByb3AsXCJQcm9wZXJ0eVwiKSk7fXJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSxpc1BhdHRlcm4/XCJPYmplY3RQYXR0ZXJuXCI6XCJPYmplY3RFeHByZXNzaW9uXCIpO307cHAucGFyc2VQcm9wZXJ0eVZhbHVlID0gZnVuY3Rpb24ocHJvcCxpc1BhdHRlcm4saXNHZW5lcmF0b3Isc3RhcnRQb3Msc3RhcnRMb2MscmVmU2hvcnRoYW5kRGVmYXVsdFBvcyl7aWYodGhpcy5lYXQoX3Rva2VudHlwZS50eXBlcy5jb2xvbikpe3Byb3AudmFsdWUgPSBpc1BhdHRlcm4/dGhpcy5wYXJzZU1heWJlRGVmYXVsdCh0aGlzLnN0YXJ0LHRoaXMuc3RhcnRMb2MpOnRoaXMucGFyc2VNYXliZUFzc2lnbihmYWxzZSxyZWZTaG9ydGhhbmREZWZhdWx0UG9zKTtwcm9wLmtpbmQgPSBcImluaXRcIjt9ZWxzZSBpZih0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNiAmJiB0aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMucGFyZW5MKXtpZihpc1BhdHRlcm4pdGhpcy51bmV4cGVjdGVkKCk7cHJvcC5raW5kID0gXCJpbml0XCI7cHJvcC5tZXRob2QgPSB0cnVlO3Byb3AudmFsdWUgPSB0aGlzLnBhcnNlTWV0aG9kKGlzR2VuZXJhdG9yKTt9ZWxzZSBpZih0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNSAmJiAhcHJvcC5jb21wdXRlZCAmJiBwcm9wLmtleS50eXBlID09PSBcIklkZW50aWZpZXJcIiAmJiAocHJvcC5rZXkubmFtZSA9PT0gXCJnZXRcIiB8fCBwcm9wLmtleS5uYW1lID09PSBcInNldFwiKSAmJiAodGhpcy50eXBlICE9IF90b2tlbnR5cGUudHlwZXMuY29tbWEgJiYgdGhpcy50eXBlICE9IF90b2tlbnR5cGUudHlwZXMuYnJhY2VSKSl7aWYoaXNHZW5lcmF0b3IgfHwgaXNQYXR0ZXJuKXRoaXMudW5leHBlY3RlZCgpO3Byb3Aua2luZCA9IHByb3Aua2V5Lm5hbWU7dGhpcy5wYXJzZVByb3BlcnR5TmFtZShwcm9wKTtwcm9wLnZhbHVlID0gdGhpcy5wYXJzZU1ldGhvZChmYWxzZSk7dmFyIHBhcmFtQ291bnQ9cHJvcC5raW5kID09PSBcImdldFwiPzA6MTtpZihwcm9wLnZhbHVlLnBhcmFtcy5sZW5ndGggIT09IHBhcmFtQ291bnQpe3ZhciBzdGFydD1wcm9wLnZhbHVlLnN0YXJ0O2lmKHByb3Aua2luZCA9PT0gXCJnZXRcIil0aGlzLnJhaXNlKHN0YXJ0LFwiZ2V0dGVyIHNob3VsZCBoYXZlIG5vIHBhcmFtc1wiKTtlbHNlIHRoaXMucmFpc2Uoc3RhcnQsXCJzZXR0ZXIgc2hvdWxkIGhhdmUgZXhhY3RseSBvbmUgcGFyYW1cIik7fX1lbHNlIGlmKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2ICYmICFwcm9wLmNvbXB1dGVkICYmIHByb3Aua2V5LnR5cGUgPT09IFwiSWRlbnRpZmllclwiKXtwcm9wLmtpbmQgPSBcImluaXRcIjtpZihpc1BhdHRlcm4pe2lmKHRoaXMuaXNLZXl3b3JkKHByb3Aua2V5Lm5hbWUpIHx8IHRoaXMuc3RyaWN0ICYmIChfaWRlbnRpZmllci5yZXNlcnZlZFdvcmRzLnN0cmljdEJpbmQocHJvcC5rZXkubmFtZSkgfHwgX2lkZW50aWZpZXIucmVzZXJ2ZWRXb3Jkcy5zdHJpY3QocHJvcC5rZXkubmFtZSkpIHx8ICF0aGlzLm9wdGlvbnMuYWxsb3dSZXNlcnZlZCAmJiB0aGlzLmlzUmVzZXJ2ZWRXb3JkKHByb3Aua2V5Lm5hbWUpKXRoaXMucmFpc2UocHJvcC5rZXkuc3RhcnQsXCJCaW5kaW5nIFwiICsgcHJvcC5rZXkubmFtZSk7cHJvcC52YWx1ZSA9IHRoaXMucGFyc2VNYXliZURlZmF1bHQoc3RhcnRQb3Msc3RhcnRMb2MscHJvcC5rZXkpO31lbHNlIGlmKHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5lcSAmJiByZWZTaG9ydGhhbmREZWZhdWx0UG9zKXtpZighcmVmU2hvcnRoYW5kRGVmYXVsdFBvcy5zdGFydClyZWZTaG9ydGhhbmREZWZhdWx0UG9zLnN0YXJ0ID0gdGhpcy5zdGFydDtwcm9wLnZhbHVlID0gdGhpcy5wYXJzZU1heWJlRGVmYXVsdChzdGFydFBvcyxzdGFydExvYyxwcm9wLmtleSk7fWVsc2Uge3Byb3AudmFsdWUgPSBwcm9wLmtleTt9cHJvcC5zaG9ydGhhbmQgPSB0cnVlO31lbHNlIHRoaXMudW5leHBlY3RlZCgpO307cHAucGFyc2VQcm9wZXJ0eU5hbWUgPSBmdW5jdGlvbihwcm9wKXtpZih0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNil7aWYodGhpcy5lYXQoX3Rva2VudHlwZS50eXBlcy5icmFja2V0TCkpe3Byb3AuY29tcHV0ZWQgPSB0cnVlO3Byb3Aua2V5ID0gdGhpcy5wYXJzZU1heWJlQXNzaWduKCk7dGhpcy5leHBlY3QoX3Rva2VudHlwZS50eXBlcy5icmFja2V0Uik7cmV0dXJuIHByb3Aua2V5O31lbHNlIHtwcm9wLmNvbXB1dGVkID0gZmFsc2U7fX1yZXR1cm4gcHJvcC5rZXkgPSB0aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMubnVtIHx8IHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5zdHJpbmc/dGhpcy5wYXJzZUV4cHJBdG9tKCk6dGhpcy5wYXJzZUlkZW50KHRydWUpO307IC8vIEluaXRpYWxpemUgZW1wdHkgZnVuY3Rpb24gbm9kZS5cbnBwLmluaXRGdW5jdGlvbiA9IGZ1bmN0aW9uKG5vZGUpe25vZGUuaWQgPSBudWxsO2lmKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KXtub2RlLmdlbmVyYXRvciA9IGZhbHNlO25vZGUuZXhwcmVzc2lvbiA9IGZhbHNlO319OyAvLyBQYXJzZSBvYmplY3Qgb3IgY2xhc3MgbWV0aG9kLlxucHAucGFyc2VNZXRob2QgPSBmdW5jdGlvbihpc0dlbmVyYXRvcil7dmFyIG5vZGU9dGhpcy5zdGFydE5vZGUoKTt0aGlzLmluaXRGdW5jdGlvbihub2RlKTt0aGlzLmV4cGVjdChfdG9rZW50eXBlLnR5cGVzLnBhcmVuTCk7bm9kZS5wYXJhbXMgPSB0aGlzLnBhcnNlQmluZGluZ0xpc3QoX3Rva2VudHlwZS50eXBlcy5wYXJlblIsZmFsc2UsZmFsc2UpO3ZhciBhbGxvd0V4cHJlc3Npb25Cb2R5PXVuZGVmaW5lZDtpZih0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNil7bm9kZS5nZW5lcmF0b3IgPSBpc0dlbmVyYXRvcjt9dGhpcy5wYXJzZUZ1bmN0aW9uQm9keShub2RlLGZhbHNlKTtyZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsXCJGdW5jdGlvbkV4cHJlc3Npb25cIik7fTsgLy8gUGFyc2UgYXJyb3cgZnVuY3Rpb24gZXhwcmVzc2lvbiB3aXRoIGdpdmVuIHBhcmFtZXRlcnMuXG5wcC5wYXJzZUFycm93RXhwcmVzc2lvbiA9IGZ1bmN0aW9uKG5vZGUscGFyYW1zKXt0aGlzLmluaXRGdW5jdGlvbihub2RlKTtub2RlLnBhcmFtcyA9IHRoaXMudG9Bc3NpZ25hYmxlTGlzdChwYXJhbXMsdHJ1ZSk7dGhpcy5wYXJzZUZ1bmN0aW9uQm9keShub2RlLHRydWUpO3JldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSxcIkFycm93RnVuY3Rpb25FeHByZXNzaW9uXCIpO307IC8vIFBhcnNlIGZ1bmN0aW9uIGJvZHkgYW5kIGNoZWNrIHBhcmFtZXRlcnMuXG5wcC5wYXJzZUZ1bmN0aW9uQm9keSA9IGZ1bmN0aW9uKG5vZGUsYWxsb3dFeHByZXNzaW9uKXt2YXIgaXNFeHByZXNzaW9uPWFsbG93RXhwcmVzc2lvbiAmJiB0aGlzLnR5cGUgIT09IF90b2tlbnR5cGUudHlwZXMuYnJhY2VMO2lmKGlzRXhwcmVzc2lvbil7bm9kZS5ib2R5ID0gdGhpcy5wYXJzZU1heWJlQXNzaWduKCk7bm9kZS5leHByZXNzaW9uID0gdHJ1ZTt9ZWxzZSB7IC8vIFN0YXJ0IGEgbmV3IHNjb3BlIHdpdGggcmVnYXJkIHRvIGxhYmVscyBhbmQgdGhlIGBpbkZ1bmN0aW9uYFxuLy8gZmxhZyAocmVzdG9yZSB0aGVtIHRvIHRoZWlyIG9sZCB2YWx1ZSBhZnRlcndhcmRzKS5cbnZhciBvbGRJbkZ1bmM9dGhpcy5pbkZ1bmN0aW9uLG9sZEluR2VuPXRoaXMuaW5HZW5lcmF0b3Isb2xkTGFiZWxzPXRoaXMubGFiZWxzO3RoaXMuaW5GdW5jdGlvbiA9IHRydWU7dGhpcy5pbkdlbmVyYXRvciA9IG5vZGUuZ2VuZXJhdG9yO3RoaXMubGFiZWxzID0gW107bm9kZS5ib2R5ID0gdGhpcy5wYXJzZUJsb2NrKHRydWUpO25vZGUuZXhwcmVzc2lvbiA9IGZhbHNlO3RoaXMuaW5GdW5jdGlvbiA9IG9sZEluRnVuYzt0aGlzLmluR2VuZXJhdG9yID0gb2xkSW5HZW47dGhpcy5sYWJlbHMgPSBvbGRMYWJlbHM7fSAvLyBJZiB0aGlzIGlzIGEgc3RyaWN0IG1vZGUgZnVuY3Rpb24sIHZlcmlmeSB0aGF0IGFyZ3VtZW50IG5hbWVzXG4vLyBhcmUgbm90IHJlcGVhdGVkLCBhbmQgaXQgZG9lcyBub3QgdHJ5IHRvIGJpbmQgdGhlIHdvcmRzIGBldmFsYFxuLy8gb3IgYGFyZ3VtZW50c2AuXG5pZih0aGlzLnN0cmljdCB8fCAhaXNFeHByZXNzaW9uICYmIG5vZGUuYm9keS5ib2R5Lmxlbmd0aCAmJiB0aGlzLmlzVXNlU3RyaWN0KG5vZGUuYm9keS5ib2R5WzBdKSl7dmFyIG5hbWVIYXNoPXt9LG9sZFN0cmljdD10aGlzLnN0cmljdDt0aGlzLnN0cmljdCA9IHRydWU7aWYobm9kZS5pZCl0aGlzLmNoZWNrTFZhbChub2RlLmlkLHRydWUpO2Zvcih2YXIgaT0wO2kgPCBub2RlLnBhcmFtcy5sZW5ndGg7aSsrKSB7dGhpcy5jaGVja0xWYWwobm9kZS5wYXJhbXNbaV0sdHJ1ZSxuYW1lSGFzaCk7fXRoaXMuc3RyaWN0ID0gb2xkU3RyaWN0O319OyAvLyBQYXJzZXMgYSBjb21tYS1zZXBhcmF0ZWQgbGlzdCBvZiBleHByZXNzaW9ucywgYW5kIHJldHVybnMgdGhlbSBhc1xuLy8gYW4gYXJyYXkuIGBjbG9zZWAgaXMgdGhlIHRva2VuIHR5cGUgdGhhdCBlbmRzIHRoZSBsaXN0LCBhbmRcbi8vIGBhbGxvd0VtcHR5YCBjYW4gYmUgdHVybmVkIG9uIHRvIGFsbG93IHN1YnNlcXVlbnQgY29tbWFzIHdpdGhcbi8vIG5vdGhpbmcgaW4gYmV0d2VlbiB0aGVtIHRvIGJlIHBhcnNlZCBhcyBgbnVsbGAgKHdoaWNoIGlzIG5lZWRlZFxuLy8gZm9yIGFycmF5IGxpdGVyYWxzKS5cbnBwLnBhcnNlRXhwckxpc3QgPSBmdW5jdGlvbihjbG9zZSxhbGxvd1RyYWlsaW5nQ29tbWEsYWxsb3dFbXB0eSxyZWZTaG9ydGhhbmREZWZhdWx0UG9zKXt2YXIgZWx0cz1bXSxmaXJzdD10cnVlO3doaWxlKCF0aGlzLmVhdChjbG9zZSkpIHtpZighZmlyc3Qpe3RoaXMuZXhwZWN0KF90b2tlbnR5cGUudHlwZXMuY29tbWEpO2lmKGFsbG93VHJhaWxpbmdDb21tYSAmJiB0aGlzLmFmdGVyVHJhaWxpbmdDb21tYShjbG9zZSkpYnJlYWs7fWVsc2UgZmlyc3QgPSBmYWxzZTt2YXIgZWx0PXVuZGVmaW5lZDtpZihhbGxvd0VtcHR5ICYmIHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5jb21tYSllbHQgPSBudWxsO2Vsc2UgaWYodGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLmVsbGlwc2lzKWVsdCA9IHRoaXMucGFyc2VTcHJlYWQocmVmU2hvcnRoYW5kRGVmYXVsdFBvcyk7ZWxzZSBlbHQgPSB0aGlzLnBhcnNlTWF5YmVBc3NpZ24oZmFsc2UscmVmU2hvcnRoYW5kRGVmYXVsdFBvcyk7ZWx0cy5wdXNoKGVsdCk7fXJldHVybiBlbHRzO307IC8vIFBhcnNlIHRoZSBuZXh0IHRva2VuIGFzIGFuIGlkZW50aWZpZXIuIElmIGBsaWJlcmFsYCBpcyB0cnVlICh1c2VkXG4vLyB3aGVuIHBhcnNpbmcgcHJvcGVydGllcyksIGl0IHdpbGwgYWxzbyBjb252ZXJ0IGtleXdvcmRzIGludG9cbi8vIGlkZW50aWZpZXJzLlxucHAucGFyc2VJZGVudCA9IGZ1bmN0aW9uKGxpYmVyYWwpe3ZhciBub2RlPXRoaXMuc3RhcnROb2RlKCk7aWYobGliZXJhbCAmJiB0aGlzLm9wdGlvbnMuYWxsb3dSZXNlcnZlZCA9PSBcIm5ldmVyXCIpbGliZXJhbCA9IGZhbHNlO2lmKHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5uYW1lKXtpZighbGliZXJhbCAmJiAoIXRoaXMub3B0aW9ucy5hbGxvd1Jlc2VydmVkICYmIHRoaXMuaXNSZXNlcnZlZFdvcmQodGhpcy52YWx1ZSkgfHwgdGhpcy5zdHJpY3QgJiYgX2lkZW50aWZpZXIucmVzZXJ2ZWRXb3Jkcy5zdHJpY3QodGhpcy52YWx1ZSkgJiYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2IHx8IHRoaXMuaW5wdXQuc2xpY2UodGhpcy5zdGFydCx0aGlzLmVuZCkuaW5kZXhPZihcIlxcXFxcIikgPT0gLTEpKSl0aGlzLnJhaXNlKHRoaXMuc3RhcnQsXCJUaGUga2V5d29yZCAnXCIgKyB0aGlzLnZhbHVlICsgXCInIGlzIHJlc2VydmVkXCIpO25vZGUubmFtZSA9IHRoaXMudmFsdWU7fWVsc2UgaWYobGliZXJhbCAmJiB0aGlzLnR5cGUua2V5d29yZCl7bm9kZS5uYW1lID0gdGhpcy50eXBlLmtleXdvcmQ7fWVsc2Uge3RoaXMudW5leHBlY3RlZCgpO310aGlzLm5leHQoKTtyZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsXCJJZGVudGlmaWVyXCIpO307IC8vIFBhcnNlcyB5aWVsZCBleHByZXNzaW9uIGluc2lkZSBnZW5lcmF0b3IuXG5wcC5wYXJzZVlpZWxkID0gZnVuY3Rpb24oKXt2YXIgbm9kZT10aGlzLnN0YXJ0Tm9kZSgpO3RoaXMubmV4dCgpO2lmKHRoaXMudHlwZSA9PSBfdG9rZW50eXBlLnR5cGVzLnNlbWkgfHwgdGhpcy5jYW5JbnNlcnRTZW1pY29sb24oKSB8fCB0aGlzLnR5cGUgIT0gX3Rva2VudHlwZS50eXBlcy5zdGFyICYmICF0aGlzLnR5cGUuc3RhcnRzRXhwcil7bm9kZS5kZWxlZ2F0ZSA9IGZhbHNlO25vZGUuYXJndW1lbnQgPSBudWxsO31lbHNlIHtub2RlLmRlbGVnYXRlID0gdGhpcy5lYXQoX3Rva2VudHlwZS50eXBlcy5zdGFyKTtub2RlLmFyZ3VtZW50ID0gdGhpcy5wYXJzZU1heWJlQXNzaWduKCk7fXJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSxcIllpZWxkRXhwcmVzc2lvblwiKTt9OyAvLyBQYXJzZXMgYXJyYXkgYW5kIGdlbmVyYXRvciBjb21wcmVoZW5zaW9ucy5cbnBwLnBhcnNlQ29tcHJlaGVuc2lvbiA9IGZ1bmN0aW9uKG5vZGUsaXNHZW5lcmF0b3Ipe25vZGUuYmxvY2tzID0gW107d2hpbGUodGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLl9mb3IpIHt2YXIgYmxvY2s9dGhpcy5zdGFydE5vZGUoKTt0aGlzLm5leHQoKTt0aGlzLmV4cGVjdChfdG9rZW50eXBlLnR5cGVzLnBhcmVuTCk7YmxvY2subGVmdCA9IHRoaXMucGFyc2VCaW5kaW5nQXRvbSgpO3RoaXMuY2hlY2tMVmFsKGJsb2NrLmxlZnQsdHJ1ZSk7dGhpcy5leHBlY3RDb250ZXh0dWFsKFwib2ZcIik7YmxvY2sucmlnaHQgPSB0aGlzLnBhcnNlRXhwcmVzc2lvbigpO3RoaXMuZXhwZWN0KF90b2tlbnR5cGUudHlwZXMucGFyZW5SKTtub2RlLmJsb2Nrcy5wdXNoKHRoaXMuZmluaXNoTm9kZShibG9jayxcIkNvbXByZWhlbnNpb25CbG9ja1wiKSk7fW5vZGUuZmlsdGVyID0gdGhpcy5lYXQoX3Rva2VudHlwZS50eXBlcy5faWYpP3RoaXMucGFyc2VQYXJlbkV4cHJlc3Npb24oKTpudWxsO25vZGUuYm9keSA9IHRoaXMucGFyc2VFeHByZXNzaW9uKCk7dGhpcy5leHBlY3QoaXNHZW5lcmF0b3I/X3Rva2VudHlwZS50eXBlcy5wYXJlblI6X3Rva2VudHlwZS50eXBlcy5icmFja2V0Uik7bm9kZS5nZW5lcmF0b3IgPSBpc0dlbmVyYXRvcjtyZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsXCJDb21wcmVoZW5zaW9uRXhwcmVzc2lvblwiKTt9O30se1wiLi9pZGVudGlmaWVyXCI6MixcIi4vc3RhdGVcIjoxMCxcIi4vdG9rZW50eXBlXCI6MTQsXCIuL3V0aWxcIjoxNX1dLDI6W2Z1bmN0aW9uKF9kZXJlcV8sbW9kdWxlLGV4cG9ydHMpeyAvLyBUaGlzIGlzIGEgdHJpY2sgdGFrZW4gZnJvbSBFc3ByaW1hLiBJdCB0dXJucyBvdXQgdGhhdCwgb25cbi8vIG5vbi1DaHJvbWUgYnJvd3NlcnMsIHRvIGNoZWNrIHdoZXRoZXIgYSBzdHJpbmcgaXMgaW4gYSBzZXQsIGFcbi8vIHByZWRpY2F0ZSBjb250YWluaW5nIGEgYmlnIHVnbHkgYHN3aXRjaGAgc3RhdGVtZW50IGlzIGZhc3RlciB0aGFuXG4vLyBhIHJlZ3VsYXIgZXhwcmVzc2lvbiwgYW5kIG9uIENocm9tZSB0aGUgdHdvIGFyZSBhYm91dCBvbiBwYXIuXG4vLyBUaGlzIGZ1bmN0aW9uIHVzZXMgYGV2YWxgIChub24tbGV4aWNhbCkgdG8gcHJvZHVjZSBzdWNoIGFcbi8vIHByZWRpY2F0ZSBmcm9tIGEgc3BhY2Utc2VwYXJhdGVkIHN0cmluZyBvZiB3b3Jkcy5cbi8vXG4vLyBJdCBzdGFydHMgYnkgc29ydGluZyB0aGUgd29yZHMgYnkgbGVuZ3RoLlxuXCJ1c2Ugc3RyaWN0XCI7ZXhwb3J0cy5fX2VzTW9kdWxlID0gdHJ1ZTtleHBvcnRzLmlzSWRlbnRpZmllclN0YXJ0ID0gaXNJZGVudGlmaWVyU3RhcnQ7ZXhwb3J0cy5pc0lkZW50aWZpZXJDaGFyID0gaXNJZGVudGlmaWVyQ2hhcjtmdW5jdGlvbiBtYWtlUHJlZGljYXRlKHdvcmRzKXt3b3JkcyA9IHdvcmRzLnNwbGl0KFwiIFwiKTt2YXIgZj1cIlwiLGNhdHM9W107b3V0OiBmb3IodmFyIGk9MDtpIDwgd29yZHMubGVuZ3RoOysraSkge2Zvcih2YXIgaj0wO2ogPCBjYXRzLmxlbmd0aDsrK2opIHtpZihjYXRzW2pdWzBdLmxlbmd0aCA9PSB3b3Jkc1tpXS5sZW5ndGgpe2NhdHNbal0ucHVzaCh3b3Jkc1tpXSk7Y29udGludWUgb3V0O319Y2F0cy5wdXNoKFt3b3Jkc1tpXV0pO31mdW5jdGlvbiBjb21wYXJlVG8oYXJyKXtpZihhcnIubGVuZ3RoID09IDEpcmV0dXJuIGYgKz0gXCJyZXR1cm4gc3RyID09PSBcIiArIEpTT04uc3RyaW5naWZ5KGFyclswXSkgKyBcIjtcIjtmICs9IFwic3dpdGNoKHN0cil7XCI7Zm9yKHZhciBpPTA7aSA8IGFyci5sZW5ndGg7KytpKSB7ZiArPSBcImNhc2UgXCIgKyBKU09OLnN0cmluZ2lmeShhcnJbaV0pICsgXCI6XCI7fWYgKz0gXCJyZXR1cm4gdHJ1ZX1yZXR1cm4gZmFsc2U7XCI7fSAvLyBXaGVuIHRoZXJlIGFyZSBtb3JlIHRoYW4gdGhyZWUgbGVuZ3RoIGNhdGVnb3JpZXMsIGFuIG91dGVyXG4vLyBzd2l0Y2ggZmlyc3QgZGlzcGF0Y2hlcyBvbiB0aGUgbGVuZ3RocywgdG8gc2F2ZSBvbiBjb21wYXJpc29ucy5cbmlmKGNhdHMubGVuZ3RoID4gMyl7Y2F0cy5zb3J0KGZ1bmN0aW9uKGEsYil7cmV0dXJuIGIubGVuZ3RoIC0gYS5sZW5ndGg7fSk7ZiArPSBcInN3aXRjaChzdHIubGVuZ3RoKXtcIjtmb3IodmFyIGk9MDtpIDwgY2F0cy5sZW5ndGg7KytpKSB7dmFyIGNhdD1jYXRzW2ldO2YgKz0gXCJjYXNlIFwiICsgY2F0WzBdLmxlbmd0aCArIFwiOlwiO2NvbXBhcmVUbyhjYXQpO31mICs9IFwifVwiOyAvLyBPdGhlcndpc2UsIHNpbXBseSBnZW5lcmF0ZSBhIGZsYXQgYHN3aXRjaGAgc3RhdGVtZW50LlxufWVsc2Uge2NvbXBhcmVUbyh3b3Jkcyk7fXJldHVybiBuZXcgRnVuY3Rpb24oXCJzdHJcIixmKTt9IC8vIFJlc2VydmVkIHdvcmQgbGlzdHMgZm9yIHZhcmlvdXMgZGlhbGVjdHMgb2YgdGhlIGxhbmd1YWdlXG52YXIgcmVzZXJ2ZWRXb3Jkcz17MzptYWtlUHJlZGljYXRlKFwiYWJzdHJhY3QgYm9vbGVhbiBieXRlIGNoYXIgY2xhc3MgZG91YmxlIGVudW0gZXhwb3J0IGV4dGVuZHMgZmluYWwgZmxvYXQgZ290byBpbXBsZW1lbnRzIGltcG9ydCBpbnQgaW50ZXJmYWNlIGxvbmcgbmF0aXZlIHBhY2thZ2UgcHJpdmF0ZSBwcm90ZWN0ZWQgcHVibGljIHNob3J0IHN0YXRpYyBzdXBlciBzeW5jaHJvbml6ZWQgdGhyb3dzIHRyYW5zaWVudCB2b2xhdGlsZVwiKSw1Om1ha2VQcmVkaWNhdGUoXCJjbGFzcyBlbnVtIGV4dGVuZHMgc3VwZXIgY29uc3QgZXhwb3J0IGltcG9ydFwiKSw2Om1ha2VQcmVkaWNhdGUoXCJlbnVtIGF3YWl0XCIpLHN0cmljdDptYWtlUHJlZGljYXRlKFwiaW1wbGVtZW50cyBpbnRlcmZhY2UgbGV0IHBhY2thZ2UgcHJpdmF0ZSBwcm90ZWN0ZWQgcHVibGljIHN0YXRpYyB5aWVsZFwiKSxzdHJpY3RCaW5kOm1ha2VQcmVkaWNhdGUoXCJldmFsIGFyZ3VtZW50c1wiKX07ZXhwb3J0cy5yZXNlcnZlZFdvcmRzID0gcmVzZXJ2ZWRXb3JkczsgLy8gQW5kIHRoZSBrZXl3b3Jkc1xudmFyIGVjbWE1QW5kTGVzc0tleXdvcmRzPVwiYnJlYWsgY2FzZSBjYXRjaCBjb250aW51ZSBkZWJ1Z2dlciBkZWZhdWx0IGRvIGVsc2UgZmluYWxseSBmb3IgZnVuY3Rpb24gaWYgcmV0dXJuIHN3aXRjaCB0aHJvdyB0cnkgdmFyIHdoaWxlIHdpdGggbnVsbCB0cnVlIGZhbHNlIGluc3RhbmNlb2YgdHlwZW9mIHZvaWQgZGVsZXRlIG5ldyBpbiB0aGlzXCI7dmFyIGtleXdvcmRzPXs1Om1ha2VQcmVkaWNhdGUoZWNtYTVBbmRMZXNzS2V5d29yZHMpLDY6bWFrZVByZWRpY2F0ZShlY21hNUFuZExlc3NLZXl3b3JkcyArIFwiIGxldCBjb25zdCBjbGFzcyBleHRlbmRzIGV4cG9ydCBpbXBvcnQgeWllbGQgc3VwZXJcIil9O2V4cG9ydHMua2V5d29yZHMgPSBrZXl3b3JkczsgLy8gIyMgQ2hhcmFjdGVyIGNhdGVnb3JpZXNcbi8vIEJpZyB1Z2x5IHJlZ3VsYXIgZXhwcmVzc2lvbnMgdGhhdCBtYXRjaCBjaGFyYWN0ZXJzIGluIHRoZVxuLy8gd2hpdGVzcGFjZSwgaWRlbnRpZmllciwgYW5kIGlkZW50aWZpZXItc3RhcnQgY2F0ZWdvcmllcy4gVGhlc2Vcbi8vIGFyZSBvbmx5IGFwcGxpZWQgd2hlbiBhIGNoYXJhY3RlciBpcyBmb3VuZCB0byBhY3R1YWxseSBoYXZlIGFcbi8vIGNvZGUgcG9pbnQgYWJvdmUgMTI4LlxuLy8gR2VuZXJhdGVkIGJ5IGB0b29scy9nZW5lcmF0ZS1pZGVudGlmaWVyLXJlZ2V4LmpzYC5cbnZhciBub25BU0NJSWlkZW50aWZpZXJTdGFydENoYXJzPVwiwqrCtcK6w4Atw5bDmC3DtsO4LcuBy4Yty5HLoC3LpMusy67NsC3NtM22zbfNui3Nvc2/zobOiC3Ois6Mzo4tzqHOoy3Ptc+3LdKB0oot1K/UsS3VltWZ1aEt1ofXkC3XqtewLdey2KAt2YrZrtmv2bEt25Pbldul26bbrtuv27ot27zbv9yQ3JIt3K/djS3epd6x34ot36rftN+137rgoIAt4KCV4KCa4KCk4KCo4KGALeChmOCioC3gorLgpIQt4KS54KS94KWQ4KWYLeCloeClsS3gpoDgpoUt4KaM4KaP4KaQ4KaTLeCmqOCmqi3gprDgprLgprYt4Ka54Ka94KeO4Kec4Ked4KefLeCnoeCnsOCnseCohS3gqIrgqI/gqJDgqJMt4Kio4KiqLeCosOCosuCos+CoteCotuCouOCoueCpmS3gqZzgqZ7gqbIt4Km04KqFLeCqjeCqjy3gqpHgqpMt4Kqo4KqqLeCqsOCqsuCqs+CqtS3gqrngqr3gq5Dgq6Dgq6HgrIUt4KyM4KyP4KyQ4KyTLeCsqOCsqi3grLDgrLLgrLPgrLUt4Ky54Ky94K2c4K2d4K2fLeCtoeCtseCug+CuhS3grorgro4t4K6Q4K6SLeCuleCumeCumuCunOCunuCun+Cuo+CupOCuqC3grqrgrq4t4K654K+Q4LCFLeCwjOCwji3gsJDgsJIt4LCo4LCqLeCwueCwveCxmOCxmeCxoOCxoeCyhS3gsozgso4t4LKQ4LKSLeCyqOCyqi3gsrPgsrUt4LK54LK94LOe4LOg4LOh4LOx4LOy4LSFLeC0jOC0ji3gtJDgtJIt4LS64LS94LWO4LWg4LWh4LW6LeC1v+C2hS3gtpbgtpot4Lax4LazLeC2u+C2veC3gC3gt4bguIEt4Liw4Liy4Liz4LmALeC5huC6geC6guC6hOC6h+C6iOC6iuC6jeC6lC3gupfgupkt4Lqf4LqhLeC6o+C6peC6p+C6quC6q+C6rS3gurDgurLgurPgur3gu4At4LuE4LuG4LucLeC7n+C8gOC9gC3gvYfgvYkt4L2s4L6ILeC+jOGAgC3hgKrhgL/hgZAt4YGV4YGaLeGBneGBoeGBpeGBpuGBri3hgbDhgbUt4YKB4YKO4YKgLeGDheGDh+GDjeGDkC3hg7rhg7wt4YmI4YmKLeGJjeGJkC3hiZbhiZjhiZot4Ymd4YmgLeGKiOGKii3hio3hipAt4Yqw4YqyLeGKteGKuC3hir7hi4Dhi4It4YuF4YuILeGLluGLmC3hjJDhjJIt4YyV4YyYLeGNmuGOgC3hjo/hjqAt4Y+04ZCBLeGZrOGZry3hmb/hmoEt4Zqa4ZqgLeGbquGbri3hm7jhnIAt4ZyM4ZyOLeGckeGcoC3hnLHhnYAt4Z2R4Z2gLeGdrOGdri3hnbDhnoAt4Z6z4Z+X4Z+c4aCgLeGht+GigC3hoqjhoqrhorAt4aO14aSALeGknuGlkC3hpa3hpbAt4aW04aaALeGmq+GngS3hp4fhqIAt4aiW4aigLeGplOGqp+GshS3hrLPhrYUt4a2L4a6DLeGuoOGuruGur+Guui3hr6XhsIAt4bCj4bGNLeGxj+Gxmi3hsb3hs6kt4bOs4bOuLeGzseGzteGztuG0gC3htr/huIAt4byV4byYLeG8neG8oC3hvYXhvYgt4b2N4b2QLeG9l+G9meG9m+G9neG9ny3hvb3hvoAt4b604b62LeG+vOG+vuG/gi3hv4Thv4Yt4b+M4b+QLeG/k+G/li3hv5vhv6At4b+s4b+yLeG/tOG/ti3hv7zigbHigb/igpAt4oKc4oSC4oSH4oSKLeKEk+KEleKEmC3ihJ3ihKTihKbihKjihKot4oS54oS8LeKEv+KFhS3ihYnihY7ihaAt4oaI4rCALeKwruKwsC3isZ7isaAt4rOk4rOrLeKzruKzsuKzs+K0gC3itKXitKfitK3itLAt4rWn4rWv4raALeK2luK2oC3itqbitqgt4rau4rawLeK2tuK2uC3itr7it4At4reG4reILeK3juK3kC3it5bit5gt4ree44CFLeOAh+OAoS3jgKnjgLEt44C144C4LeOAvOOBgS3jgpbjgpst44Kf44KhLeODuuODvC3jg7/jhIUt44St44SxLeOGjuOGoC3jhrrjh7At44e/45CALeS2teS4gC3pv4zqgIAt6pKM6pOQLeqTveqUgC3qmIzqmJAt6pif6piq6pir6pmALeqZruqZvy3qmp3qmqAt6puv6pyXLeqcn+qcoi3qnojqnost6p6O6p6QLeqereqesOqeseqfty3qoIHqoIMt6qCF6qCHLeqgiuqgjC3qoKLqoYAt6qGz6qKCLeqis+qjsi3qo7fqo7vqpIot6qSl6qSwLeqlhuqloC3qpbzqpoQt6qay6qeP6qegLeqnpOqnpi3qp6/qp7ot6qe+6qiALeqoqOqpgC3qqYLqqYQt6qmL6qmgLeqptuqpuuqpvi3qqq/qqrHqqrXqqrbqqrkt6qq96quA6quC6qubLeqrneqroC3qq6rqq7It6qu06qyBLeqshuqsiS3qrI7qrJEt6qyW6qygLeqspuqsqC3qrK7qrLAt6q2a6q2cLeqtn+qtpOqtpeqvgC3qr6LqsIAt7Z6j7Z6wLe2fhu2fiy3tn7vvpIAt76mt76mwLe+rme+sgC3vrIbvrJMt76yX76yd76yfLe+sqO+sqi3vrLbvrLgt76y876y+762A762B762D762E762GLe+use+vky3vtL3vtZAt77aP77aSLe+3h++3sC3vt7vvubAt77m077m2Le+7vO+8oS3vvLrvvYEt772a772mLe++vu+/gi3vv4fvv4ot77+P77+SLe+/l++/mi3vv5xcIjt2YXIgbm9uQVNDSUlpZGVudGlmaWVyQ2hhcnM9XCLigIzigI3Ct8yALc2vzofSgy3Sh9aRLda91r/XgdeC14TXhdeH2JAt2JrZiy3Zqdmw25Yt25zbny3bpNun26jbqi3brduwLdu53JHcsC3dit6mLd6w34At34nfqy3fs+Cgli3goJngoJst4KCj4KClLeCgp+CgqS3goK3goZkt4KGb4KOkLeCkg+Ckui3gpLzgpL4t4KWP4KWRLeCll+ClouClo+Clpi3gpa/gpoEt4KaD4Ka84Ka+LeCnhOCnh+CniOCniy3gp43gp5fgp6Lgp6Pgp6Yt4Kev4KiBLeCog+CovOCovi3gqYLgqYfgqYjgqYst4KmN4KmR4KmmLeCpseCpteCqgS3gqoPgqrzgqr4t4KuF4KuHLeCrieCriy3gq43gq6Lgq6Pgq6Yt4Kuv4KyBLeCsg+CsvOCsvi3grYTgrYfgrYjgrYst4K2N4K2W4K2X4K2i4K2j4K2mLeCtr+CuguCuvi3gr4Lgr4Yt4K+I4K+KLeCvjeCvl+Cvpi3gr6/gsIAt4LCD4LC+LeCxhOCxhi3gsYjgsYot4LGN4LGV4LGW4LGi4LGj4LGmLeCxr+CygS3gsoPgsrzgsr4t4LOE4LOGLeCziOCzii3gs43gs5Xgs5bgs6Lgs6Pgs6Yt4LOv4LSBLeC0g+C0vi3gtYTgtYYt4LWI4LWKLeC1jeC1l+C1ouC1o+C1pi3gta/gtoLgtoPgt4rgt48t4LeU4LeW4LeYLeC3n+C3pi3gt6/gt7Lgt7PguLHguLQt4Li64LmHLeC5juC5kC3guZngurHgurQt4Lq54Lq74Lq84LuILeC7jeC7kC3gu5ngvJjgvJngvKAt4Lyp4Ly14Ly34Ly54Ly+4Ly/4L2xLeC+hOC+huC+h+C+jS3gvpfgvpkt4L684L+G4YCrLeGAvuGBgC3hgYnhgZYt4YGZ4YGeLeGBoOGBoi3hgaThgact4YGt4YGxLeGBtOGCgi3hgo3hgo8t4YKd4Y2dLeGNn+GNqS3hjbHhnJIt4ZyU4ZyyLeGctOGdkuGdk+GdsuGds+GetC3hn5Phn53hn6At4Z+p4aCLLeGgjeGgkC3hoJnhoqnhpKAt4aSr4aSwLeGku+Glhi3hpY/hprAt4aeA4aeI4aeJ4aeQLeGnmuGoly3hqJvhqZUt4ame4amgLeGpvOGpvy3hqonhqpAt4aqZ4aqwLeGqveGsgC3hrIThrLQt4a2E4a2QLeGtmeGtqy3hrbPhroAt4a6C4a6hLeGureGusC3hrrnhr6Yt4a+z4bCkLeGwt+GxgC3hsYnhsZAt4bGZ4bOQLeGzkuGzlC3hs6jhs63hs7It4bO04bO44bO54beALeG3teG3vC3ht7/igL/igYDigZTig5At4oOc4oOh4oOlLeKDsOKzry3is7Hitb/it6At4re/44CqLeOAr+OCmeOCmuqYoC3qmKnqma/qmbQt6pm96pqf6puw6pux6qCC6qCG6qCL6qCjLeqgp+qigOqigeqitC3qo4Tqo5At6qOZ6qOgLeqjseqkgC3qpInqpKYt6qSt6qWHLeqlk+qmgC3qpoPqprMt6qeA6qeQLeqnmeqnpeqnsC3qp7nqqKkt6qi26qmD6qmM6qmN6qmQLeqpmeqpuy3qqb3qqrDqqrIt6qq06qq36qq46qq+6qq/6quB6qurLeqrr+qrteqrtuqvoy3qr6rqr6zqr63qr7At6q+576ye77iALe+4j++4oC3vuK3vuLPvuLTvuY0t77mP77yQLe+8me+8v1wiO3ZhciBub25BU0NJSWlkZW50aWZpZXJTdGFydD1uZXcgUmVnRXhwKFwiW1wiICsgbm9uQVNDSUlpZGVudGlmaWVyU3RhcnRDaGFycyArIFwiXVwiKTt2YXIgbm9uQVNDSUlpZGVudGlmaWVyPW5ldyBSZWdFeHAoXCJbXCIgKyBub25BU0NJSWlkZW50aWZpZXJTdGFydENoYXJzICsgbm9uQVNDSUlpZGVudGlmaWVyQ2hhcnMgKyBcIl1cIik7bm9uQVNDSUlpZGVudGlmaWVyU3RhcnRDaGFycyA9IG5vbkFTQ0lJaWRlbnRpZmllckNoYXJzID0gbnVsbDsgLy8gVGhlc2UgYXJlIGEgcnVuLWxlbmd0aCBhbmQgb2Zmc2V0IGVuY29kZWQgcmVwcmVzZW50YXRpb24gb2YgdGhlXG4vLyA+MHhmZmZmIGNvZGUgcG9pbnRzIHRoYXQgYXJlIGEgdmFsaWQgcGFydCBvZiBpZGVudGlmaWVycy4gVGhlXG4vLyBvZmZzZXQgc3RhcnRzIGF0IDB4MTAwMDAsIGFuZCBlYWNoIHBhaXIgb2YgbnVtYmVycyByZXByZXNlbnRzIGFuXG4vLyBvZmZzZXQgdG8gdGhlIG5leHQgcmFuZ2UsIGFuZCB0aGVuIGEgc2l6ZSBvZiB0aGUgcmFuZ2UuIFRoZXkgd2VyZVxuLy8gZ2VuZXJhdGVkIGJ5IHRvb2xzL2dlbmVyYXRlLWlkZW50aWZpZXItcmVnZXguanNcbnZhciBhc3RyYWxJZGVudGlmaWVyU3RhcnRDb2Rlcz1bMCwxMSwyLDI1LDIsMTgsMiwxLDIsMTQsMywxMywzNSwxMjIsNzAsNTIsMjY4LDI4LDQsNDgsNDgsMzEsMTcsMjYsNiwzNywxMSwyOSwzLDM1LDUsNywyLDQsNDMsMTU3LDk5LDM5LDksNTEsMTU3LDMxMCwxMCwyMSwxMSw3LDE1Myw1LDMsMCwyLDQzLDIsMSw0LDAsMywyMiwxMSwyMiwxMCwzMCw5OCwyMSwxMSwyNSw3MSw1NSw3LDEsNjUsMCwxNiwzLDIsMiwyLDI2LDQ1LDI4LDQsMjgsMzYsNywyLDI3LDI4LDUzLDExLDIxLDExLDE4LDE0LDE3LDExMSw3Miw5NTUsNTIsNzYsNDQsMzMsMjQsMjcsMzUsNDIsMzQsNCwwLDEzLDQ3LDE1LDMsMjIsMCwzOCwxNywyLDI0LDEzMyw0NiwzOSw3LDMsMSwzLDIxLDIsNiwyLDEsMiw0LDQsMCwzMiw0LDI4Nyw0NywyMSwxLDIsMCwxODUsNDYsODIsNDcsMjEsMCw2MCw0Miw1MDIsNjMsMzIsMCw0NDksNTYsMTI4OCw5MjAsMTA0LDExMCwyOTYyLDEwNzAsMTMyNjYsNTY4LDgsMzAsMTE0LDI5LDE5LDQ3LDE3LDMsMzIsMjAsNiwxOCw4ODEsNjgsMTIsMCw2NywxMiwxNjQ4MSwxLDMwNzEsMTA2LDYsMTIsNCw4LDgsOSw1OTkxLDg0LDIsNzAsMiwxLDMsMCwzLDEsMywzLDIsMTEsMiwwLDIsNiwyLDY0LDIsMywzLDcsMiw2LDIsMjcsMiwzLDIsNCwyLDAsNCw2LDIsMzM5LDMsMjQsMiwyNCwyLDMwLDIsMjQsMiwzMCwyLDI0LDIsMzAsMiwyNCwyLDMwLDIsMjQsMiw3LDQxNDksMTk2LDEzNDAsMywyLDI2LDIsMSwyLDAsMywwLDIsOSwyLDMsMiwwLDIsMCw3LDAsNSwwLDIsMCwyLDAsMiwyLDIsMSwyLDAsMywwLDIsMCwyLDAsMiwwLDIsMCwyLDEsMiwwLDMsMywyLDYsMiwzLDIsMywyLDAsMiw5LDIsMTYsNiwyLDIsNCwyLDE2LDQ0MjEsNDI3MTAsNDIsNDE0OCwxMiwyMjEsMTYzNTUsNTQxXTt2YXIgYXN0cmFsSWRlbnRpZmllckNvZGVzPVs1MDksMCwyMjcsMCwxNTAsNCwyOTQsOSwxMzY4LDIsMiwxLDYsMyw0MSwyLDUsMCwxNjYsMSwxMzA2LDIsNTQsMTQsMzIsOSwxNiwzLDQ2LDEwLDU0LDksNywyLDM3LDEzLDIsOSw1MiwwLDEzLDIsNDksMTMsMTYsOSw4MywxMSwxNjgsMTEsNiw5LDgsMiw1NywwLDIsNiwzLDEsMywyLDEwLDAsMTEsMSwzLDYsNCw0LDMxNiwxOSwxMyw5LDIxNCw2LDMsOCwxMTIsMTYsMTYsOSw4MiwxMiw5LDksNTM1LDksMjA4NTUsOSwxMzUsNCw2MCw2LDI2LDksMTAxNiw0NSwxNywzLDE5NzIzLDEsNTMxOSw0LDQsNSw5LDcsMyw2LDMxLDMsMTQ5LDIsMTQxOCw0OSw0MzA1LDYsNzkyNjE4LDIzOV07IC8vIFRoaXMgaGFzIGEgY29tcGxleGl0eSBsaW5lYXIgdG8gdGhlIHZhbHVlIG9mIHRoZSBjb2RlLiBUaGVcbi8vIGFzc3VtcHRpb24gaXMgdGhhdCBsb29raW5nIHVwIGFzdHJhbCBpZGVudGlmaWVyIGNoYXJhY3RlcnMgaXNcbi8vIHJhcmUuXG5mdW5jdGlvbiBpc0luQXN0cmFsU2V0KGNvZGUsc2V0KXt2YXIgcG9zPTB4MTAwMDA7Zm9yKHZhciBpPTA7aSA8IHNldC5sZW5ndGg7aSArPSAyKSB7cG9zICs9IHNldFtpXTtpZihwb3MgPiBjb2RlKXJldHVybiBmYWxzZTtwb3MgKz0gc2V0W2kgKyAxXTtpZihwb3MgPj0gY29kZSlyZXR1cm4gdHJ1ZTt9fSAvLyBUZXN0IHdoZXRoZXIgYSBnaXZlbiBjaGFyYWN0ZXIgY29kZSBzdGFydHMgYW4gaWRlbnRpZmllci5cbmZ1bmN0aW9uIGlzSWRlbnRpZmllclN0YXJ0KGNvZGUsYXN0cmFsKXtpZihjb2RlIDwgNjUpcmV0dXJuIGNvZGUgPT09IDM2O2lmKGNvZGUgPCA5MSlyZXR1cm4gdHJ1ZTtpZihjb2RlIDwgOTcpcmV0dXJuIGNvZGUgPT09IDk1O2lmKGNvZGUgPCAxMjMpcmV0dXJuIHRydWU7aWYoY29kZSA8PSAweGZmZmYpcmV0dXJuIGNvZGUgPj0gMHhhYSAmJiBub25BU0NJSWlkZW50aWZpZXJTdGFydC50ZXN0KFN0cmluZy5mcm9tQ2hhckNvZGUoY29kZSkpO2lmKGFzdHJhbCA9PT0gZmFsc2UpcmV0dXJuIGZhbHNlO3JldHVybiBpc0luQXN0cmFsU2V0KGNvZGUsYXN0cmFsSWRlbnRpZmllclN0YXJ0Q29kZXMpO30gLy8gVGVzdCB3aGV0aGVyIGEgZ2l2ZW4gY2hhcmFjdGVyIGlzIHBhcnQgb2YgYW4gaWRlbnRpZmllci5cbmZ1bmN0aW9uIGlzSWRlbnRpZmllckNoYXIoY29kZSxhc3RyYWwpe2lmKGNvZGUgPCA0OClyZXR1cm4gY29kZSA9PT0gMzY7aWYoY29kZSA8IDU4KXJldHVybiB0cnVlO2lmKGNvZGUgPCA2NSlyZXR1cm4gZmFsc2U7aWYoY29kZSA8IDkxKXJldHVybiB0cnVlO2lmKGNvZGUgPCA5NylyZXR1cm4gY29kZSA9PT0gOTU7aWYoY29kZSA8IDEyMylyZXR1cm4gdHJ1ZTtpZihjb2RlIDw9IDB4ZmZmZilyZXR1cm4gY29kZSA+PSAweGFhICYmIG5vbkFTQ0lJaWRlbnRpZmllci50ZXN0KFN0cmluZy5mcm9tQ2hhckNvZGUoY29kZSkpO2lmKGFzdHJhbCA9PT0gZmFsc2UpcmV0dXJuIGZhbHNlO3JldHVybiBpc0luQXN0cmFsU2V0KGNvZGUsYXN0cmFsSWRlbnRpZmllclN0YXJ0Q29kZXMpIHx8IGlzSW5Bc3RyYWxTZXQoY29kZSxhc3RyYWxJZGVudGlmaWVyQ29kZXMpO319LHt9XSwzOltmdW5jdGlvbihfZGVyZXFfLG1vZHVsZSxleHBvcnRzKXsgLy8gQWNvcm4gaXMgYSB0aW55LCBmYXN0IEphdmFTY3JpcHQgcGFyc2VyIHdyaXR0ZW4gaW4gSmF2YVNjcmlwdC5cbi8vXG4vLyBBY29ybiB3YXMgd3JpdHRlbiBieSBNYXJpam4gSGF2ZXJiZWtlLCBJbmd2YXIgU3RlcGFueWFuLCBhbmRcbi8vIHZhcmlvdXMgY29udHJpYnV0b3JzIGFuZCByZWxlYXNlZCB1bmRlciBhbiBNSVQgbGljZW5zZS5cbi8vXG4vLyBHaXQgcmVwb3NpdG9yaWVzIGZvciBBY29ybiBhcmUgYXZhaWxhYmxlIGF0XG4vL1xuLy8gICAgIGh0dHA6Ly9tYXJpam5oYXZlcmJla2UubmwvZ2l0L2Fjb3JuXG4vLyAgICAgaHR0cHM6Ly9naXRodWIuY29tL21hcmlqbmgvYWNvcm4uZ2l0XG4vL1xuLy8gUGxlYXNlIHVzZSB0aGUgW2dpdGh1YiBidWcgdHJhY2tlcl1bZ2hidF0gdG8gcmVwb3J0IGlzc3Vlcy5cbi8vXG4vLyBbZ2hidF06IGh0dHBzOi8vZ2l0aHViLmNvbS9tYXJpam5oL2Fjb3JuL2lzc3Vlc1xuLy9cbi8vIFRoaXMgZmlsZSBkZWZpbmVzIHRoZSBtYWluIHBhcnNlciBpbnRlcmZhY2UuIFRoZSBsaWJyYXJ5IGFsc28gY29tZXNcbi8vIHdpdGggYSBbZXJyb3ItdG9sZXJhbnQgcGFyc2VyXVtkYW1taXRdIGFuZCBhblxuLy8gW2Fic3RyYWN0IHN5bnRheCB0cmVlIHdhbGtlcl1bd2Fsa10sIGRlZmluZWQgaW4gb3RoZXIgZmlsZXMuXG4vL1xuLy8gW2RhbW1pdF06IGFjb3JuX2xvb3NlLmpzXG4vLyBbd2Fsa106IHV0aWwvd2Fsay5qc1xuXCJ1c2Ugc3RyaWN0XCI7ZXhwb3J0cy5fX2VzTW9kdWxlID0gdHJ1ZTtleHBvcnRzLnBhcnNlID0gcGFyc2U7ZXhwb3J0cy5wYXJzZUV4cHJlc3Npb25BdCA9IHBhcnNlRXhwcmVzc2lvbkF0O2V4cG9ydHMudG9rZW5pemVyID0gdG9rZW5pemVyO3ZhciBfc3RhdGU9X2RlcmVxXyhcIi4vc3RhdGVcIik7dmFyIF9vcHRpb25zPV9kZXJlcV8oXCIuL29wdGlvbnNcIik7X2RlcmVxXyhcIi4vcGFyc2V1dGlsXCIpO19kZXJlcV8oXCIuL3N0YXRlbWVudFwiKTtfZGVyZXFfKFwiLi9sdmFsXCIpO19kZXJlcV8oXCIuL2V4cHJlc3Npb25cIik7X2RlcmVxXyhcIi4vbG9jYXRpb25cIik7ZXhwb3J0cy5QYXJzZXIgPSBfc3RhdGUuUGFyc2VyO2V4cG9ydHMucGx1Z2lucyA9IF9zdGF0ZS5wbHVnaW5zO2V4cG9ydHMuZGVmYXVsdE9wdGlvbnMgPSBfb3B0aW9ucy5kZWZhdWx0T3B0aW9uczt2YXIgX2xvY3V0aWw9X2RlcmVxXyhcIi4vbG9jdXRpbFwiKTtleHBvcnRzLlBvc2l0aW9uID0gX2xvY3V0aWwuUG9zaXRpb247ZXhwb3J0cy5Tb3VyY2VMb2NhdGlvbiA9IF9sb2N1dGlsLlNvdXJjZUxvY2F0aW9uO2V4cG9ydHMuZ2V0TGluZUluZm8gPSBfbG9jdXRpbC5nZXRMaW5lSW5mbzt2YXIgX25vZGU9X2RlcmVxXyhcIi4vbm9kZVwiKTtleHBvcnRzLk5vZGUgPSBfbm9kZS5Ob2RlO3ZhciBfdG9rZW50eXBlPV9kZXJlcV8oXCIuL3Rva2VudHlwZVwiKTtleHBvcnRzLlRva2VuVHlwZSA9IF90b2tlbnR5cGUuVG9rZW5UeXBlO2V4cG9ydHMudG9rVHlwZXMgPSBfdG9rZW50eXBlLnR5cGVzO3ZhciBfdG9rZW5jb250ZXh0PV9kZXJlcV8oXCIuL3Rva2VuY29udGV4dFwiKTtleHBvcnRzLlRva0NvbnRleHQgPSBfdG9rZW5jb250ZXh0LlRva0NvbnRleHQ7ZXhwb3J0cy50b2tDb250ZXh0cyA9IF90b2tlbmNvbnRleHQudHlwZXM7dmFyIF9pZGVudGlmaWVyPV9kZXJlcV8oXCIuL2lkZW50aWZpZXJcIik7ZXhwb3J0cy5pc0lkZW50aWZpZXJDaGFyID0gX2lkZW50aWZpZXIuaXNJZGVudGlmaWVyQ2hhcjtleHBvcnRzLmlzSWRlbnRpZmllclN0YXJ0ID0gX2lkZW50aWZpZXIuaXNJZGVudGlmaWVyU3RhcnQ7dmFyIF90b2tlbml6ZT1fZGVyZXFfKFwiLi90b2tlbml6ZVwiKTtleHBvcnRzLlRva2VuID0gX3Rva2VuaXplLlRva2VuO3ZhciBfd2hpdGVzcGFjZT1fZGVyZXFfKFwiLi93aGl0ZXNwYWNlXCIpO2V4cG9ydHMuaXNOZXdMaW5lID0gX3doaXRlc3BhY2UuaXNOZXdMaW5lO2V4cG9ydHMubGluZUJyZWFrID0gX3doaXRlc3BhY2UubGluZUJyZWFrO2V4cG9ydHMubGluZUJyZWFrRyA9IF93aGl0ZXNwYWNlLmxpbmVCcmVha0c7dmFyIHZlcnNpb249XCIyLjIuMFwiO2V4cG9ydHMudmVyc2lvbiA9IHZlcnNpb247IC8vIFRoZSBtYWluIGV4cG9ydGVkIGludGVyZmFjZSAodW5kZXIgYHNlbGYuYWNvcm5gIHdoZW4gaW4gdGhlXG4vLyBicm93c2VyKSBpcyBhIGBwYXJzZWAgZnVuY3Rpb24gdGhhdCB0YWtlcyBhIGNvZGUgc3RyaW5nIGFuZFxuLy8gcmV0dXJucyBhbiBhYnN0cmFjdCBzeW50YXggdHJlZSBhcyBzcGVjaWZpZWQgYnkgW01vemlsbGEgcGFyc2VyXG4vLyBBUEldW2FwaV0uXG4vL1xuLy8gW2FwaV06IGh0dHBzOi8vZGV2ZWxvcGVyLm1vemlsbGEub3JnL2VuLVVTL2RvY3MvU3BpZGVyTW9ua2V5L1BhcnNlcl9BUElcbmZ1bmN0aW9uIHBhcnNlKGlucHV0LG9wdGlvbnMpe3JldHVybiBuZXcgX3N0YXRlLlBhcnNlcihvcHRpb25zLGlucHV0KS5wYXJzZSgpO30gLy8gVGhpcyBmdW5jdGlvbiB0cmllcyB0byBwYXJzZSBhIHNpbmdsZSBleHByZXNzaW9uIGF0IGEgZ2l2ZW5cbi8vIG9mZnNldCBpbiBhIHN0cmluZy4gVXNlZnVsIGZvciBwYXJzaW5nIG1peGVkLWxhbmd1YWdlIGZvcm1hdHNcbi8vIHRoYXQgZW1iZWQgSmF2YVNjcmlwdCBleHByZXNzaW9ucy5cbmZ1bmN0aW9uIHBhcnNlRXhwcmVzc2lvbkF0KGlucHV0LHBvcyxvcHRpb25zKXt2YXIgcD1uZXcgX3N0YXRlLlBhcnNlcihvcHRpb25zLGlucHV0LHBvcyk7cC5uZXh0VG9rZW4oKTtyZXR1cm4gcC5wYXJzZUV4cHJlc3Npb24oKTt9IC8vIEFjb3JuIGlzIG9yZ2FuaXplZCBhcyBhIHRva2VuaXplciBhbmQgYSByZWN1cnNpdmUtZGVzY2VudCBwYXJzZXIuXG4vLyBUaGUgYHRva2VuaXplYCBleHBvcnQgcHJvdmlkZXMgYW4gaW50ZXJmYWNlIHRvIHRoZSB0b2tlbml6ZXIuXG5mdW5jdGlvbiB0b2tlbml6ZXIoaW5wdXQsb3B0aW9ucyl7cmV0dXJuIG5ldyBfc3RhdGUuUGFyc2VyKG9wdGlvbnMsaW5wdXQpO319LHtcIi4vZXhwcmVzc2lvblwiOjEsXCIuL2lkZW50aWZpZXJcIjoyLFwiLi9sb2NhdGlvblwiOjQsXCIuL2xvY3V0aWxcIjo1LFwiLi9sdmFsXCI6NixcIi4vbm9kZVwiOjcsXCIuL29wdGlvbnNcIjo4LFwiLi9wYXJzZXV0aWxcIjo5LFwiLi9zdGF0ZVwiOjEwLFwiLi9zdGF0ZW1lbnRcIjoxMSxcIi4vdG9rZW5jb250ZXh0XCI6MTIsXCIuL3Rva2VuaXplXCI6MTMsXCIuL3Rva2VudHlwZVwiOjE0LFwiLi93aGl0ZXNwYWNlXCI6MTZ9XSw0OltmdW5jdGlvbihfZGVyZXFfLG1vZHVsZSxleHBvcnRzKXtcInVzZSBzdHJpY3RcIjt2YXIgX3N0YXRlPV9kZXJlcV8oXCIuL3N0YXRlXCIpO3ZhciBfbG9jdXRpbD1fZGVyZXFfKFwiLi9sb2N1dGlsXCIpO3ZhciBwcD1fc3RhdGUuUGFyc2VyLnByb3RvdHlwZTsgLy8gVGhpcyBmdW5jdGlvbiBpcyB1c2VkIHRvIHJhaXNlIGV4Y2VwdGlvbnMgb24gcGFyc2UgZXJyb3JzLiBJdFxuLy8gdGFrZXMgYW4gb2Zmc2V0IGludGVnZXIgKGludG8gdGhlIGN1cnJlbnQgYGlucHV0YCkgdG8gaW5kaWNhdGVcbi8vIHRoZSBsb2NhdGlvbiBvZiB0aGUgZXJyb3IsIGF0dGFjaGVzIHRoZSBwb3NpdGlvbiB0byB0aGUgZW5kXG4vLyBvZiB0aGUgZXJyb3IgbWVzc2FnZSwgYW5kIHRoZW4gcmFpc2VzIGEgYFN5bnRheEVycm9yYCB3aXRoIHRoYXRcbi8vIG1lc3NhZ2UuXG5wcC5yYWlzZSA9IGZ1bmN0aW9uKHBvcyxtZXNzYWdlKXt2YXIgbG9jPV9sb2N1dGlsLmdldExpbmVJbmZvKHRoaXMuaW5wdXQscG9zKTttZXNzYWdlICs9IFwiIChcIiArIGxvYy5saW5lICsgXCI6XCIgKyBsb2MuY29sdW1uICsgXCIpXCI7dmFyIGVycj1uZXcgU3ludGF4RXJyb3IobWVzc2FnZSk7ZXJyLnBvcyA9IHBvcztlcnIubG9jID0gbG9jO2Vyci5yYWlzZWRBdCA9IHRoaXMucG9zO3Rocm93IGVycjt9O3BwLmN1clBvc2l0aW9uID0gZnVuY3Rpb24oKXtpZih0aGlzLm9wdGlvbnMubG9jYXRpb25zKXtyZXR1cm4gbmV3IF9sb2N1dGlsLlBvc2l0aW9uKHRoaXMuY3VyTGluZSx0aGlzLnBvcyAtIHRoaXMubGluZVN0YXJ0KTt9fTt9LHtcIi4vbG9jdXRpbFwiOjUsXCIuL3N0YXRlXCI6MTB9XSw1OltmdW5jdGlvbihfZGVyZXFfLG1vZHVsZSxleHBvcnRzKXtcInVzZSBzdHJpY3RcIjtleHBvcnRzLl9fZXNNb2R1bGUgPSB0cnVlO2V4cG9ydHMuZ2V0TGluZUluZm8gPSBnZXRMaW5lSW5mbztmdW5jdGlvbiBfY2xhc3NDYWxsQ2hlY2soaW5zdGFuY2UsQ29uc3RydWN0b3Ipe2lmKCEoaW5zdGFuY2UgaW5zdGFuY2VvZiBDb25zdHJ1Y3Rvcikpe3Rocm93IG5ldyBUeXBlRXJyb3IoXCJDYW5ub3QgY2FsbCBhIGNsYXNzIGFzIGEgZnVuY3Rpb25cIik7fX12YXIgX3doaXRlc3BhY2U9X2RlcmVxXyhcIi4vd2hpdGVzcGFjZVwiKTsgLy8gVGhlc2UgYXJlIHVzZWQgd2hlbiBgb3B0aW9ucy5sb2NhdGlvbnNgIGlzIG9uLCBmb3IgdGhlXG4vLyBgc3RhcnRMb2NgIGFuZCBgZW5kTG9jYCBwcm9wZXJ0aWVzLlxudmFyIFBvc2l0aW9uPShmdW5jdGlvbigpe2Z1bmN0aW9uIFBvc2l0aW9uKGxpbmUsY29sKXtfY2xhc3NDYWxsQ2hlY2sodGhpcyxQb3NpdGlvbik7dGhpcy5saW5lID0gbGluZTt0aGlzLmNvbHVtbiA9IGNvbDt9UG9zaXRpb24ucHJvdG90eXBlLm9mZnNldCA9IGZ1bmN0aW9uIG9mZnNldChuKXtyZXR1cm4gbmV3IFBvc2l0aW9uKHRoaXMubGluZSx0aGlzLmNvbHVtbiArIG4pO307cmV0dXJuIFBvc2l0aW9uO30pKCk7ZXhwb3J0cy5Qb3NpdGlvbiA9IFBvc2l0aW9uO3ZhciBTb3VyY2VMb2NhdGlvbj1mdW5jdGlvbiBTb3VyY2VMb2NhdGlvbihwLHN0YXJ0LGVuZCl7X2NsYXNzQ2FsbENoZWNrKHRoaXMsU291cmNlTG9jYXRpb24pO3RoaXMuc3RhcnQgPSBzdGFydDt0aGlzLmVuZCA9IGVuZDtpZihwLnNvdXJjZUZpbGUgIT09IG51bGwpdGhpcy5zb3VyY2UgPSBwLnNvdXJjZUZpbGU7fSAvLyBUaGUgYGdldExpbmVJbmZvYCBmdW5jdGlvbiBpcyBtb3N0bHkgdXNlZnVsIHdoZW4gdGhlXG4vLyBgbG9jYXRpb25zYCBvcHRpb24gaXMgb2ZmIChmb3IgcGVyZm9ybWFuY2UgcmVhc29ucykgYW5kIHlvdVxuLy8gd2FudCB0byBmaW5kIHRoZSBsaW5lL2NvbHVtbiBwb3NpdGlvbiBmb3IgYSBnaXZlbiBjaGFyYWN0ZXJcbi8vIG9mZnNldC4gYGlucHV0YCBzaG91bGQgYmUgdGhlIGNvZGUgc3RyaW5nIHRoYXQgdGhlIG9mZnNldCByZWZlcnNcbi8vIGludG8uXG47ZXhwb3J0cy5Tb3VyY2VMb2NhdGlvbiA9IFNvdXJjZUxvY2F0aW9uO2Z1bmN0aW9uIGdldExpbmVJbmZvKGlucHV0LG9mZnNldCl7Zm9yKHZhciBsaW5lPTEsY3VyPTA7Oykge193aGl0ZXNwYWNlLmxpbmVCcmVha0cubGFzdEluZGV4ID0gY3VyO3ZhciBtYXRjaD1fd2hpdGVzcGFjZS5saW5lQnJlYWtHLmV4ZWMoaW5wdXQpO2lmKG1hdGNoICYmIG1hdGNoLmluZGV4IDwgb2Zmc2V0KXsrK2xpbmU7Y3VyID0gbWF0Y2guaW5kZXggKyBtYXRjaFswXS5sZW5ndGg7fWVsc2Uge3JldHVybiBuZXcgUG9zaXRpb24obGluZSxvZmZzZXQgLSBjdXIpO319fX0se1wiLi93aGl0ZXNwYWNlXCI6MTZ9XSw2OltmdW5jdGlvbihfZGVyZXFfLG1vZHVsZSxleHBvcnRzKXtcInVzZSBzdHJpY3RcIjt2YXIgX3Rva2VudHlwZT1fZGVyZXFfKFwiLi90b2tlbnR5cGVcIik7dmFyIF9zdGF0ZT1fZGVyZXFfKFwiLi9zdGF0ZVwiKTt2YXIgX2lkZW50aWZpZXI9X2RlcmVxXyhcIi4vaWRlbnRpZmllclwiKTt2YXIgX3V0aWw9X2RlcmVxXyhcIi4vdXRpbFwiKTt2YXIgcHA9X3N0YXRlLlBhcnNlci5wcm90b3R5cGU7IC8vIENvbnZlcnQgZXhpc3RpbmcgZXhwcmVzc2lvbiBhdG9tIHRvIGFzc2lnbmFibGUgcGF0dGVyblxuLy8gaWYgcG9zc2libGUuXG5wcC50b0Fzc2lnbmFibGUgPSBmdW5jdGlvbihub2RlLGlzQmluZGluZyl7aWYodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYgJiYgbm9kZSl7c3dpdGNoKG5vZGUudHlwZSl7Y2FzZSBcIklkZW50aWZpZXJcIjpjYXNlIFwiT2JqZWN0UGF0dGVyblwiOmNhc2UgXCJBcnJheVBhdHRlcm5cIjpjYXNlIFwiQXNzaWdubWVudFBhdHRlcm5cIjpicmVhaztjYXNlIFwiT2JqZWN0RXhwcmVzc2lvblwiOm5vZGUudHlwZSA9IFwiT2JqZWN0UGF0dGVyblwiO2Zvcih2YXIgaT0wO2kgPCBub2RlLnByb3BlcnRpZXMubGVuZ3RoO2krKykge3ZhciBwcm9wPW5vZGUucHJvcGVydGllc1tpXTtpZihwcm9wLmtpbmQgIT09IFwiaW5pdFwiKXRoaXMucmFpc2UocHJvcC5rZXkuc3RhcnQsXCJPYmplY3QgcGF0dGVybiBjYW4ndCBjb250YWluIGdldHRlciBvciBzZXR0ZXJcIik7dGhpcy50b0Fzc2lnbmFibGUocHJvcC52YWx1ZSxpc0JpbmRpbmcpO31icmVhaztjYXNlIFwiQXJyYXlFeHByZXNzaW9uXCI6bm9kZS50eXBlID0gXCJBcnJheVBhdHRlcm5cIjt0aGlzLnRvQXNzaWduYWJsZUxpc3Qobm9kZS5lbGVtZW50cyxpc0JpbmRpbmcpO2JyZWFrO2Nhc2UgXCJBc3NpZ25tZW50RXhwcmVzc2lvblwiOmlmKG5vZGUub3BlcmF0b3IgPT09IFwiPVwiKXtub2RlLnR5cGUgPSBcIkFzc2lnbm1lbnRQYXR0ZXJuXCI7ZGVsZXRlIG5vZGUub3BlcmF0b3I7fWVsc2Uge3RoaXMucmFpc2Uobm9kZS5sZWZ0LmVuZCxcIk9ubHkgJz0nIG9wZXJhdG9yIGNhbiBiZSB1c2VkIGZvciBzcGVjaWZ5aW5nIGRlZmF1bHQgdmFsdWUuXCIpO31icmVhaztjYXNlIFwiUGFyZW50aGVzaXplZEV4cHJlc3Npb25cIjpub2RlLmV4cHJlc3Npb24gPSB0aGlzLnRvQXNzaWduYWJsZShub2RlLmV4cHJlc3Npb24saXNCaW5kaW5nKTticmVhaztjYXNlIFwiTWVtYmVyRXhwcmVzc2lvblwiOmlmKCFpc0JpbmRpbmcpYnJlYWs7ZGVmYXVsdDp0aGlzLnJhaXNlKG5vZGUuc3RhcnQsXCJBc3NpZ25pbmcgdG8gcnZhbHVlXCIpO319cmV0dXJuIG5vZGU7fTsgLy8gQ29udmVydCBsaXN0IG9mIGV4cHJlc3Npb24gYXRvbXMgdG8gYmluZGluZyBsaXN0LlxucHAudG9Bc3NpZ25hYmxlTGlzdCA9IGZ1bmN0aW9uKGV4cHJMaXN0LGlzQmluZGluZyl7dmFyIGVuZD1leHByTGlzdC5sZW5ndGg7aWYoZW5kKXt2YXIgbGFzdD1leHByTGlzdFtlbmQgLSAxXTtpZihsYXN0ICYmIGxhc3QudHlwZSA9PSBcIlJlc3RFbGVtZW50XCIpey0tZW5kO31lbHNlIGlmKGxhc3QgJiYgbGFzdC50eXBlID09IFwiU3ByZWFkRWxlbWVudFwiKXtsYXN0LnR5cGUgPSBcIlJlc3RFbGVtZW50XCI7dmFyIGFyZz1sYXN0LmFyZ3VtZW50O3RoaXMudG9Bc3NpZ25hYmxlKGFyZyxpc0JpbmRpbmcpO2lmKGFyZy50eXBlICE9PSBcIklkZW50aWZpZXJcIiAmJiBhcmcudHlwZSAhPT0gXCJNZW1iZXJFeHByZXNzaW9uXCIgJiYgYXJnLnR5cGUgIT09IFwiQXJyYXlQYXR0ZXJuXCIpdGhpcy51bmV4cGVjdGVkKGFyZy5zdGFydCk7LS1lbmQ7fX1mb3IodmFyIGk9MDtpIDwgZW5kO2krKykge3ZhciBlbHQ9ZXhwckxpc3RbaV07aWYoZWx0KXRoaXMudG9Bc3NpZ25hYmxlKGVsdCxpc0JpbmRpbmcpO31yZXR1cm4gZXhwckxpc3Q7fTsgLy8gUGFyc2VzIHNwcmVhZCBlbGVtZW50LlxucHAucGFyc2VTcHJlYWQgPSBmdW5jdGlvbihyZWZTaG9ydGhhbmREZWZhdWx0UG9zKXt2YXIgbm9kZT10aGlzLnN0YXJ0Tm9kZSgpO3RoaXMubmV4dCgpO25vZGUuYXJndW1lbnQgPSB0aGlzLnBhcnNlTWF5YmVBc3NpZ24ocmVmU2hvcnRoYW5kRGVmYXVsdFBvcyk7cmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLFwiU3ByZWFkRWxlbWVudFwiKTt9O3BwLnBhcnNlUmVzdCA9IGZ1bmN0aW9uKCl7dmFyIG5vZGU9dGhpcy5zdGFydE5vZGUoKTt0aGlzLm5leHQoKTtub2RlLmFyZ3VtZW50ID0gdGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLm5hbWUgfHwgdGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLmJyYWNrZXRMP3RoaXMucGFyc2VCaW5kaW5nQXRvbSgpOnRoaXMudW5leHBlY3RlZCgpO3JldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSxcIlJlc3RFbGVtZW50XCIpO307IC8vIFBhcnNlcyBsdmFsdWUgKGFzc2lnbmFibGUpIGF0b20uXG5wcC5wYXJzZUJpbmRpbmdBdG9tID0gZnVuY3Rpb24oKXtpZih0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPCA2KXJldHVybiB0aGlzLnBhcnNlSWRlbnQoKTtzd2l0Y2godGhpcy50eXBlKXtjYXNlIF90b2tlbnR5cGUudHlwZXMubmFtZTpyZXR1cm4gdGhpcy5wYXJzZUlkZW50KCk7Y2FzZSBfdG9rZW50eXBlLnR5cGVzLmJyYWNrZXRMOnZhciBub2RlPXRoaXMuc3RhcnROb2RlKCk7dGhpcy5uZXh0KCk7bm9kZS5lbGVtZW50cyA9IHRoaXMucGFyc2VCaW5kaW5nTGlzdChfdG9rZW50eXBlLnR5cGVzLmJyYWNrZXRSLHRydWUsdHJ1ZSk7cmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLFwiQXJyYXlQYXR0ZXJuXCIpO2Nhc2UgX3Rva2VudHlwZS50eXBlcy5icmFjZUw6cmV0dXJuIHRoaXMucGFyc2VPYmoodHJ1ZSk7ZGVmYXVsdDp0aGlzLnVuZXhwZWN0ZWQoKTt9fTtwcC5wYXJzZUJpbmRpbmdMaXN0ID0gZnVuY3Rpb24oY2xvc2UsYWxsb3dFbXB0eSxhbGxvd1RyYWlsaW5nQ29tbWEpe3ZhciBlbHRzPVtdLGZpcnN0PXRydWU7d2hpbGUoIXRoaXMuZWF0KGNsb3NlKSkge2lmKGZpcnN0KWZpcnN0ID0gZmFsc2U7ZWxzZSB0aGlzLmV4cGVjdChfdG9rZW50eXBlLnR5cGVzLmNvbW1hKTtpZihhbGxvd0VtcHR5ICYmIHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5jb21tYSl7ZWx0cy5wdXNoKG51bGwpO31lbHNlIGlmKGFsbG93VHJhaWxpbmdDb21tYSAmJiB0aGlzLmFmdGVyVHJhaWxpbmdDb21tYShjbG9zZSkpe2JyZWFrO31lbHNlIGlmKHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5lbGxpcHNpcyl7dmFyIHJlc3Q9dGhpcy5wYXJzZVJlc3QoKTt0aGlzLnBhcnNlQmluZGluZ0xpc3RJdGVtKHJlc3QpO2VsdHMucHVzaChyZXN0KTt0aGlzLmV4cGVjdChjbG9zZSk7YnJlYWs7fWVsc2Uge3ZhciBlbGVtPXRoaXMucGFyc2VNYXliZURlZmF1bHQodGhpcy5zdGFydCx0aGlzLnN0YXJ0TG9jKTt0aGlzLnBhcnNlQmluZGluZ0xpc3RJdGVtKGVsZW0pO2VsdHMucHVzaChlbGVtKTt9fXJldHVybiBlbHRzO307cHAucGFyc2VCaW5kaW5nTGlzdEl0ZW0gPSBmdW5jdGlvbihwYXJhbSl7cmV0dXJuIHBhcmFtO307IC8vIFBhcnNlcyBhc3NpZ25tZW50IHBhdHRlcm4gYXJvdW5kIGdpdmVuIGF0b20gaWYgcG9zc2libGUuXG5wcC5wYXJzZU1heWJlRGVmYXVsdCA9IGZ1bmN0aW9uKHN0YXJ0UG9zLHN0YXJ0TG9jLGxlZnQpe2xlZnQgPSBsZWZ0IHx8IHRoaXMucGFyc2VCaW5kaW5nQXRvbSgpO2lmKCF0aGlzLmVhdChfdG9rZW50eXBlLnR5cGVzLmVxKSlyZXR1cm4gbGVmdDt2YXIgbm9kZT10aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0UG9zLHN0YXJ0TG9jKTtub2RlLmxlZnQgPSBsZWZ0O25vZGUucmlnaHQgPSB0aGlzLnBhcnNlTWF5YmVBc3NpZ24oKTtyZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsXCJBc3NpZ25tZW50UGF0dGVyblwiKTt9OyAvLyBWZXJpZnkgdGhhdCBhIG5vZGUgaXMgYW4gbHZhbCDigJQgc29tZXRoaW5nIHRoYXQgY2FuIGJlIGFzc2lnbmVkXG4vLyB0by5cbnBwLmNoZWNrTFZhbCA9IGZ1bmN0aW9uKGV4cHIsaXNCaW5kaW5nLGNoZWNrQ2xhc2hlcyl7c3dpdGNoKGV4cHIudHlwZSl7Y2FzZSBcIklkZW50aWZpZXJcIjppZih0aGlzLnN0cmljdCAmJiAoX2lkZW50aWZpZXIucmVzZXJ2ZWRXb3Jkcy5zdHJpY3RCaW5kKGV4cHIubmFtZSkgfHwgX2lkZW50aWZpZXIucmVzZXJ2ZWRXb3Jkcy5zdHJpY3QoZXhwci5uYW1lKSkpdGhpcy5yYWlzZShleHByLnN0YXJ0LChpc0JpbmRpbmc/XCJCaW5kaW5nIFwiOlwiQXNzaWduaW5nIHRvIFwiKSArIGV4cHIubmFtZSArIFwiIGluIHN0cmljdCBtb2RlXCIpO2lmKGNoZWNrQ2xhc2hlcyl7aWYoX3V0aWwuaGFzKGNoZWNrQ2xhc2hlcyxleHByLm5hbWUpKXRoaXMucmFpc2UoZXhwci5zdGFydCxcIkFyZ3VtZW50IG5hbWUgY2xhc2ggaW4gc3RyaWN0IG1vZGVcIik7Y2hlY2tDbGFzaGVzW2V4cHIubmFtZV0gPSB0cnVlO31icmVhaztjYXNlIFwiTWVtYmVyRXhwcmVzc2lvblwiOmlmKGlzQmluZGluZyl0aGlzLnJhaXNlKGV4cHIuc3RhcnQsKGlzQmluZGluZz9cIkJpbmRpbmdcIjpcIkFzc2lnbmluZyB0b1wiKSArIFwiIG1lbWJlciBleHByZXNzaW9uXCIpO2JyZWFrO2Nhc2UgXCJPYmplY3RQYXR0ZXJuXCI6Zm9yKHZhciBpPTA7aSA8IGV4cHIucHJvcGVydGllcy5sZW5ndGg7aSsrKSB7dGhpcy5jaGVja0xWYWwoZXhwci5wcm9wZXJ0aWVzW2ldLnZhbHVlLGlzQmluZGluZyxjaGVja0NsYXNoZXMpO31icmVhaztjYXNlIFwiQXJyYXlQYXR0ZXJuXCI6Zm9yKHZhciBpPTA7aSA8IGV4cHIuZWxlbWVudHMubGVuZ3RoO2krKykge3ZhciBlbGVtPWV4cHIuZWxlbWVudHNbaV07aWYoZWxlbSl0aGlzLmNoZWNrTFZhbChlbGVtLGlzQmluZGluZyxjaGVja0NsYXNoZXMpO31icmVhaztjYXNlIFwiQXNzaWdubWVudFBhdHRlcm5cIjp0aGlzLmNoZWNrTFZhbChleHByLmxlZnQsaXNCaW5kaW5nLGNoZWNrQ2xhc2hlcyk7YnJlYWs7Y2FzZSBcIlJlc3RFbGVtZW50XCI6dGhpcy5jaGVja0xWYWwoZXhwci5hcmd1bWVudCxpc0JpbmRpbmcsY2hlY2tDbGFzaGVzKTticmVhaztjYXNlIFwiUGFyZW50aGVzaXplZEV4cHJlc3Npb25cIjp0aGlzLmNoZWNrTFZhbChleHByLmV4cHJlc3Npb24saXNCaW5kaW5nLGNoZWNrQ2xhc2hlcyk7YnJlYWs7ZGVmYXVsdDp0aGlzLnJhaXNlKGV4cHIuc3RhcnQsKGlzQmluZGluZz9cIkJpbmRpbmdcIjpcIkFzc2lnbmluZyB0b1wiKSArIFwiIHJ2YWx1ZVwiKTt9fTt9LHtcIi4vaWRlbnRpZmllclwiOjIsXCIuL3N0YXRlXCI6MTAsXCIuL3Rva2VudHlwZVwiOjE0LFwiLi91dGlsXCI6MTV9XSw3OltmdW5jdGlvbihfZGVyZXFfLG1vZHVsZSxleHBvcnRzKXtcInVzZSBzdHJpY3RcIjtleHBvcnRzLl9fZXNNb2R1bGUgPSB0cnVlO2Z1bmN0aW9uIF9jbGFzc0NhbGxDaGVjayhpbnN0YW5jZSxDb25zdHJ1Y3Rvcil7aWYoIShpbnN0YW5jZSBpbnN0YW5jZW9mIENvbnN0cnVjdG9yKSl7dGhyb3cgbmV3IFR5cGVFcnJvcihcIkNhbm5vdCBjYWxsIGEgY2xhc3MgYXMgYSBmdW5jdGlvblwiKTt9fXZhciBfc3RhdGU9X2RlcmVxXyhcIi4vc3RhdGVcIik7dmFyIF9sb2N1dGlsPV9kZXJlcV8oXCIuL2xvY3V0aWxcIik7dmFyIE5vZGU9ZnVuY3Rpb24gTm9kZShwYXJzZXIscG9zLGxvYyl7X2NsYXNzQ2FsbENoZWNrKHRoaXMsTm9kZSk7dGhpcy50eXBlID0gXCJcIjt0aGlzLnN0YXJ0ID0gcG9zO3RoaXMuZW5kID0gMDtpZihwYXJzZXIub3B0aW9ucy5sb2NhdGlvbnMpdGhpcy5sb2MgPSBuZXcgX2xvY3V0aWwuU291cmNlTG9jYXRpb24ocGFyc2VyLGxvYyk7aWYocGFyc2VyLm9wdGlvbnMuZGlyZWN0U291cmNlRmlsZSl0aGlzLnNvdXJjZUZpbGUgPSBwYXJzZXIub3B0aW9ucy5kaXJlY3RTb3VyY2VGaWxlO2lmKHBhcnNlci5vcHRpb25zLnJhbmdlcyl0aGlzLnJhbmdlID0gW3BvcywwXTt9IC8vIFN0YXJ0IGFuIEFTVCBub2RlLCBhdHRhY2hpbmcgYSBzdGFydCBvZmZzZXQuXG47ZXhwb3J0cy5Ob2RlID0gTm9kZTt2YXIgcHA9X3N0YXRlLlBhcnNlci5wcm90b3R5cGU7cHAuc3RhcnROb2RlID0gZnVuY3Rpb24oKXtyZXR1cm4gbmV3IE5vZGUodGhpcyx0aGlzLnN0YXJ0LHRoaXMuc3RhcnRMb2MpO307cHAuc3RhcnROb2RlQXQgPSBmdW5jdGlvbihwb3MsbG9jKXtyZXR1cm4gbmV3IE5vZGUodGhpcyxwb3MsbG9jKTt9OyAvLyBGaW5pc2ggYW4gQVNUIG5vZGUsIGFkZGluZyBgdHlwZWAgYW5kIGBlbmRgIHByb3BlcnRpZXMuXG5mdW5jdGlvbiBmaW5pc2hOb2RlQXQobm9kZSx0eXBlLHBvcyxsb2Mpe25vZGUudHlwZSA9IHR5cGU7bm9kZS5lbmQgPSBwb3M7aWYodGhpcy5vcHRpb25zLmxvY2F0aW9ucylub2RlLmxvYy5lbmQgPSBsb2M7aWYodGhpcy5vcHRpb25zLnJhbmdlcylub2RlLnJhbmdlWzFdID0gcG9zO3JldHVybiBub2RlO31wcC5maW5pc2hOb2RlID0gZnVuY3Rpb24obm9kZSx0eXBlKXtyZXR1cm4gZmluaXNoTm9kZUF0LmNhbGwodGhpcyxub2RlLHR5cGUsdGhpcy5sYXN0VG9rRW5kLHRoaXMubGFzdFRva0VuZExvYyk7fTsgLy8gRmluaXNoIG5vZGUgYXQgZ2l2ZW4gcG9zaXRpb25cbnBwLmZpbmlzaE5vZGVBdCA9IGZ1bmN0aW9uKG5vZGUsdHlwZSxwb3MsbG9jKXtyZXR1cm4gZmluaXNoTm9kZUF0LmNhbGwodGhpcyxub2RlLHR5cGUscG9zLGxvYyk7fTt9LHtcIi4vbG9jdXRpbFwiOjUsXCIuL3N0YXRlXCI6MTB9XSw4OltmdW5jdGlvbihfZGVyZXFfLG1vZHVsZSxleHBvcnRzKXtcInVzZSBzdHJpY3RcIjtleHBvcnRzLl9fZXNNb2R1bGUgPSB0cnVlO2V4cG9ydHMuZ2V0T3B0aW9ucyA9IGdldE9wdGlvbnM7dmFyIF91dGlsPV9kZXJlcV8oXCIuL3V0aWxcIik7dmFyIF9sb2N1dGlsPV9kZXJlcV8oXCIuL2xvY3V0aWxcIik7IC8vIEEgc2Vjb25kIG9wdGlvbmFsIGFyZ3VtZW50IGNhbiBiZSBnaXZlbiB0byBmdXJ0aGVyIGNvbmZpZ3VyZVxuLy8gdGhlIHBhcnNlciBwcm9jZXNzLiBUaGVzZSBvcHRpb25zIGFyZSByZWNvZ25pemVkOlxudmFyIGRlZmF1bHRPcHRpb25zPXsgLy8gYGVjbWFWZXJzaW9uYCBpbmRpY2F0ZXMgdGhlIEVDTUFTY3JpcHQgdmVyc2lvbiB0byBwYXJzZS4gTXVzdFxuLy8gYmUgZWl0aGVyIDMsIG9yIDUsIG9yIDYuIFRoaXMgaW5mbHVlbmNlcyBzdXBwb3J0IGZvciBzdHJpY3Rcbi8vIG1vZGUsIHRoZSBzZXQgb2YgcmVzZXJ2ZWQgd29yZHMsIHN1cHBvcnQgZm9yIGdldHRlcnMgYW5kXG4vLyBzZXR0ZXJzIGFuZCBvdGhlciBmZWF0dXJlcy5cbmVjbWFWZXJzaW9uOjUsIC8vIFNvdXJjZSB0eXBlIChcInNjcmlwdFwiIG9yIFwibW9kdWxlXCIpIGZvciBkaWZmZXJlbnQgc2VtYW50aWNzXG5zb3VyY2VUeXBlOlwic2NyaXB0XCIsIC8vIGBvbkluc2VydGVkU2VtaWNvbG9uYCBjYW4gYmUgYSBjYWxsYmFjayB0aGF0IHdpbGwgYmUgY2FsbGVkXG4vLyB3aGVuIGEgc2VtaWNvbG9uIGlzIGF1dG9tYXRpY2FsbHkgaW5zZXJ0ZWQuIEl0IHdpbGwgYmUgcGFzc2VkXG4vLyB0aCBwb3NpdGlvbiBvZiB0aGUgY29tbWEgYXMgYW4gb2Zmc2V0LCBhbmQgaWYgYGxvY2F0aW9uc2AgaXNcbi8vIGVuYWJsZWQsIGl0IGlzIGdpdmVuIHRoZSBsb2NhdGlvbiBhcyBhIGB7bGluZSwgY29sdW1ufWAgb2JqZWN0XG4vLyBhcyBzZWNvbmQgYXJndW1lbnQuXG5vbkluc2VydGVkU2VtaWNvbG9uOm51bGwsIC8vIGBvblRyYWlsaW5nQ29tbWFgIGlzIHNpbWlsYXIgdG8gYG9uSW5zZXJ0ZWRTZW1pY29sb25gLCBidXQgZm9yXG4vLyB0cmFpbGluZyBjb21tYXMuXG5vblRyYWlsaW5nQ29tbWE6bnVsbCwgLy8gQnkgZGVmYXVsdCwgcmVzZXJ2ZWQgd29yZHMgYXJlIG5vdCBlbmZvcmNlZC4gRGlzYWJsZVxuLy8gYGFsbG93UmVzZXJ2ZWRgIHRvIGVuZm9yY2UgdGhlbS4gV2hlbiB0aGlzIG9wdGlvbiBoYXMgdGhlXG4vLyB2YWx1ZSBcIm5ldmVyXCIsIHJlc2VydmVkIHdvcmRzIGFuZCBrZXl3b3JkcyBjYW4gYWxzbyBub3QgYmVcbi8vIHVzZWQgYXMgcHJvcGVydHkgbmFtZXMuXG5hbGxvd1Jlc2VydmVkOnRydWUsIC8vIFdoZW4gZW5hYmxlZCwgYSByZXR1cm4gYXQgdGhlIHRvcCBsZXZlbCBpcyBub3QgY29uc2lkZXJlZCBhblxuLy8gZXJyb3IuXG5hbGxvd1JldHVybk91dHNpZGVGdW5jdGlvbjpmYWxzZSwgLy8gV2hlbiBlbmFibGVkLCBpbXBvcnQvZXhwb3J0IHN0YXRlbWVudHMgYXJlIG5vdCBjb25zdHJhaW5lZCB0b1xuLy8gYXBwZWFyaW5nIGF0IHRoZSB0b3Agb2YgdGhlIHByb2dyYW0uXG5hbGxvd0ltcG9ydEV4cG9ydEV2ZXJ5d2hlcmU6ZmFsc2UsIC8vIFdoZW4gZW5hYmxlZCwgaGFzaGJhbmcgZGlyZWN0aXZlIGluIHRoZSBiZWdpbm5pbmcgb2YgZmlsZVxuLy8gaXMgYWxsb3dlZCBhbmQgdHJlYXRlZCBhcyBhIGxpbmUgY29tbWVudC5cbmFsbG93SGFzaEJhbmc6ZmFsc2UsIC8vIFdoZW4gYGxvY2F0aW9uc2AgaXMgb24sIGBsb2NgIHByb3BlcnRpZXMgaG9sZGluZyBvYmplY3RzIHdpdGhcbi8vIGBzdGFydGAgYW5kIGBlbmRgIHByb3BlcnRpZXMgaW4gYHtsaW5lLCBjb2x1bW59YCBmb3JtICh3aXRoXG4vLyBsaW5lIGJlaW5nIDEtYmFzZWQgYW5kIGNvbHVtbiAwLWJhc2VkKSB3aWxsIGJlIGF0dGFjaGVkIHRvIHRoZVxuLy8gbm9kZXMuXG5sb2NhdGlvbnM6ZmFsc2UsIC8vIEEgZnVuY3Rpb24gY2FuIGJlIHBhc3NlZCBhcyBgb25Ub2tlbmAgb3B0aW9uLCB3aGljaCB3aWxsXG4vLyBjYXVzZSBBY29ybiB0byBjYWxsIHRoYXQgZnVuY3Rpb24gd2l0aCBvYmplY3QgaW4gdGhlIHNhbWVcbi8vIGZvcm1hdCBhcyB0b2tlbml6ZSgpIHJldHVybnMuIE5vdGUgdGhhdCB5b3UgYXJlIG5vdFxuLy8gYWxsb3dlZCB0byBjYWxsIHRoZSBwYXJzZXIgZnJvbSB0aGUgY2FsbGJhY2vigJR0aGF0IHdpbGxcbi8vIGNvcnJ1cHQgaXRzIGludGVybmFsIHN0YXRlLlxub25Ub2tlbjpudWxsLCAvLyBBIGZ1bmN0aW9uIGNhbiBiZSBwYXNzZWQgYXMgYG9uQ29tbWVudGAgb3B0aW9uLCB3aGljaCB3aWxsXG4vLyBjYXVzZSBBY29ybiB0byBjYWxsIHRoYXQgZnVuY3Rpb24gd2l0aCBgKGJsb2NrLCB0ZXh0LCBzdGFydCxcbi8vIGVuZClgIHBhcmFtZXRlcnMgd2hlbmV2ZXIgYSBjb21tZW50IGlzIHNraXBwZWQuIGBibG9ja2AgaXMgYVxuLy8gYm9vbGVhbiBpbmRpY2F0aW5nIHdoZXRoZXIgdGhpcyBpcyBhIGJsb2NrIChgLyogKi9gKSBjb21tZW50LFxuLy8gYHRleHRgIGlzIHRoZSBjb250ZW50IG9mIHRoZSBjb21tZW50LCBhbmQgYHN0YXJ0YCBhbmQgYGVuZGAgYXJlXG4vLyBjaGFyYWN0ZXIgb2Zmc2V0cyB0aGF0IGRlbm90ZSB0aGUgc3RhcnQgYW5kIGVuZCBvZiB0aGUgY29tbWVudC5cbi8vIFdoZW4gdGhlIGBsb2NhdGlvbnNgIG9wdGlvbiBpcyBvbiwgdHdvIG1vcmUgcGFyYW1ldGVycyBhcmVcbi8vIHBhc3NlZCwgdGhlIGZ1bGwgYHtsaW5lLCBjb2x1bW59YCBsb2NhdGlvbnMgb2YgdGhlIHN0YXJ0IGFuZFxuLy8gZW5kIG9mIHRoZSBjb21tZW50cy4gTm90ZSB0aGF0IHlvdSBhcmUgbm90IGFsbG93ZWQgdG8gY2FsbCB0aGVcbi8vIHBhcnNlciBmcm9tIHRoZSBjYWxsYmFja+KAlHRoYXQgd2lsbCBjb3JydXB0IGl0cyBpbnRlcm5hbCBzdGF0ZS5cbm9uQ29tbWVudDpudWxsLCAvLyBOb2RlcyBoYXZlIHRoZWlyIHN0YXJ0IGFuZCBlbmQgY2hhcmFjdGVycyBvZmZzZXRzIHJlY29yZGVkIGluXG4vLyBgc3RhcnRgIGFuZCBgZW5kYCBwcm9wZXJ0aWVzIChkaXJlY3RseSBvbiB0aGUgbm9kZSwgcmF0aGVyIHRoYW5cbi8vIHRoZSBgbG9jYCBvYmplY3QsIHdoaWNoIGhvbGRzIGxpbmUvY29sdW1uIGRhdGEuIFRvIGFsc28gYWRkIGFcbi8vIFtzZW1pLXN0YW5kYXJkaXplZF1bcmFuZ2VdIGByYW5nZWAgcHJvcGVydHkgaG9sZGluZyBhIGBbc3RhcnQsXG4vLyBlbmRdYCBhcnJheSB3aXRoIHRoZSBzYW1lIG51bWJlcnMsIHNldCB0aGUgYHJhbmdlc2Agb3B0aW9uIHRvXG4vLyBgdHJ1ZWAuXG4vL1xuLy8gW3JhbmdlXTogaHR0cHM6Ly9idWd6aWxsYS5tb3ppbGxhLm9yZy9zaG93X2J1Zy5jZ2k/aWQ9NzQ1Njc4XG5yYW5nZXM6ZmFsc2UsIC8vIEl0IGlzIHBvc3NpYmxlIHRvIHBhcnNlIG11bHRpcGxlIGZpbGVzIGludG8gYSBzaW5nbGUgQVNUIGJ5XG4vLyBwYXNzaW5nIHRoZSB0cmVlIHByb2R1Y2VkIGJ5IHBhcnNpbmcgdGhlIGZpcnN0IGZpbGUgYXNcbi8vIGBwcm9ncmFtYCBvcHRpb24gaW4gc3Vic2VxdWVudCBwYXJzZXMuIFRoaXMgd2lsbCBhZGQgdGhlXG4vLyB0b3BsZXZlbCBmb3JtcyBvZiB0aGUgcGFyc2VkIGZpbGUgdG8gdGhlIGBQcm9ncmFtYCAodG9wKSBub2RlXG4vLyBvZiBhbiBleGlzdGluZyBwYXJzZSB0cmVlLlxucHJvZ3JhbTpudWxsLCAvLyBXaGVuIGBsb2NhdGlvbnNgIGlzIG9uLCB5b3UgY2FuIHBhc3MgdGhpcyB0byByZWNvcmQgdGhlIHNvdXJjZVxuLy8gZmlsZSBpbiBldmVyeSBub2RlJ3MgYGxvY2Agb2JqZWN0Llxuc291cmNlRmlsZTpudWxsLCAvLyBUaGlzIHZhbHVlLCBpZiBnaXZlbiwgaXMgc3RvcmVkIGluIGV2ZXJ5IG5vZGUsIHdoZXRoZXJcbi8vIGBsb2NhdGlvbnNgIGlzIG9uIG9yIG9mZi5cbmRpcmVjdFNvdXJjZUZpbGU6bnVsbCwgLy8gV2hlbiBlbmFibGVkLCBwYXJlbnRoZXNpemVkIGV4cHJlc3Npb25zIGFyZSByZXByZXNlbnRlZCBieVxuLy8gKG5vbi1zdGFuZGFyZCkgUGFyZW50aGVzaXplZEV4cHJlc3Npb24gbm9kZXNcbnByZXNlcnZlUGFyZW5zOmZhbHNlLHBsdWdpbnM6e319O2V4cG9ydHMuZGVmYXVsdE9wdGlvbnMgPSBkZWZhdWx0T3B0aW9uczsgLy8gSW50ZXJwcmV0IGFuZCBkZWZhdWx0IGFuIG9wdGlvbnMgb2JqZWN0XG5mdW5jdGlvbiBnZXRPcHRpb25zKG9wdHMpe3ZhciBvcHRpb25zPXt9O2Zvcih2YXIgb3B0IGluIGRlZmF1bHRPcHRpb25zKSB7b3B0aW9uc1tvcHRdID0gb3B0cyAmJiBfdXRpbC5oYXMob3B0cyxvcHQpP29wdHNbb3B0XTpkZWZhdWx0T3B0aW9uc1tvcHRdO31pZihfdXRpbC5pc0FycmF5KG9wdGlvbnMub25Ub2tlbikpeyhmdW5jdGlvbigpe3ZhciB0b2tlbnM9b3B0aW9ucy5vblRva2VuO29wdGlvbnMub25Ub2tlbiA9IGZ1bmN0aW9uKHRva2VuKXtyZXR1cm4gdG9rZW5zLnB1c2godG9rZW4pO307fSkoKTt9aWYoX3V0aWwuaXNBcnJheShvcHRpb25zLm9uQ29tbWVudCkpb3B0aW9ucy5vbkNvbW1lbnQgPSBwdXNoQ29tbWVudChvcHRpb25zLG9wdGlvbnMub25Db21tZW50KTtyZXR1cm4gb3B0aW9uczt9ZnVuY3Rpb24gcHVzaENvbW1lbnQob3B0aW9ucyxhcnJheSl7cmV0dXJuIGZ1bmN0aW9uKGJsb2NrLHRleHQsc3RhcnQsZW5kLHN0YXJ0TG9jLGVuZExvYyl7dmFyIGNvbW1lbnQ9e3R5cGU6YmxvY2s/J0Jsb2NrJzonTGluZScsdmFsdWU6dGV4dCxzdGFydDpzdGFydCxlbmQ6ZW5kfTtpZihvcHRpb25zLmxvY2F0aW9ucyljb21tZW50LmxvYyA9IG5ldyBfbG9jdXRpbC5Tb3VyY2VMb2NhdGlvbih0aGlzLHN0YXJ0TG9jLGVuZExvYyk7aWYob3B0aW9ucy5yYW5nZXMpY29tbWVudC5yYW5nZSA9IFtzdGFydCxlbmRdO2FycmF5LnB1c2goY29tbWVudCk7fTt9fSx7XCIuL2xvY3V0aWxcIjo1LFwiLi91dGlsXCI6MTV9XSw5OltmdW5jdGlvbihfZGVyZXFfLG1vZHVsZSxleHBvcnRzKXtcInVzZSBzdHJpY3RcIjt2YXIgX3Rva2VudHlwZT1fZGVyZXFfKFwiLi90b2tlbnR5cGVcIik7dmFyIF9zdGF0ZT1fZGVyZXFfKFwiLi9zdGF0ZVwiKTt2YXIgX3doaXRlc3BhY2U9X2RlcmVxXyhcIi4vd2hpdGVzcGFjZVwiKTt2YXIgcHA9X3N0YXRlLlBhcnNlci5wcm90b3R5cGU7IC8vICMjIFBhcnNlciB1dGlsaXRpZXNcbi8vIFRlc3Qgd2hldGhlciBhIHN0YXRlbWVudCBub2RlIGlzIHRoZSBzdHJpbmcgbGl0ZXJhbCBgXCJ1c2Ugc3RyaWN0XCJgLlxucHAuaXNVc2VTdHJpY3QgPSBmdW5jdGlvbihzdG10KXtyZXR1cm4gdGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDUgJiYgc3RtdC50eXBlID09PSBcIkV4cHJlc3Npb25TdGF0ZW1lbnRcIiAmJiBzdG10LmV4cHJlc3Npb24udHlwZSA9PT0gXCJMaXRlcmFsXCIgJiYgc3RtdC5leHByZXNzaW9uLnJhdy5zbGljZSgxLC0xKSA9PT0gXCJ1c2Ugc3RyaWN0XCI7fTsgLy8gUHJlZGljYXRlIHRoYXQgdGVzdHMgd2hldGhlciB0aGUgbmV4dCB0b2tlbiBpcyBvZiB0aGUgZ2l2ZW5cbi8vIHR5cGUsIGFuZCBpZiB5ZXMsIGNvbnN1bWVzIGl0IGFzIGEgc2lkZSBlZmZlY3QuXG5wcC5lYXQgPSBmdW5jdGlvbih0eXBlKXtpZih0aGlzLnR5cGUgPT09IHR5cGUpe3RoaXMubmV4dCgpO3JldHVybiB0cnVlO31lbHNlIHtyZXR1cm4gZmFsc2U7fX07IC8vIFRlc3RzIHdoZXRoZXIgcGFyc2VkIHRva2VuIGlzIGEgY29udGV4dHVhbCBrZXl3b3JkLlxucHAuaXNDb250ZXh0dWFsID0gZnVuY3Rpb24obmFtZSl7cmV0dXJuIHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5uYW1lICYmIHRoaXMudmFsdWUgPT09IG5hbWU7fTsgLy8gQ29uc3VtZXMgY29udGV4dHVhbCBrZXl3b3JkIGlmIHBvc3NpYmxlLlxucHAuZWF0Q29udGV4dHVhbCA9IGZ1bmN0aW9uKG5hbWUpe3JldHVybiB0aGlzLnZhbHVlID09PSBuYW1lICYmIHRoaXMuZWF0KF90b2tlbnR5cGUudHlwZXMubmFtZSk7fTsgLy8gQXNzZXJ0cyB0aGF0IGZvbGxvd2luZyB0b2tlbiBpcyBnaXZlbiBjb250ZXh0dWFsIGtleXdvcmQuXG5wcC5leHBlY3RDb250ZXh0dWFsID0gZnVuY3Rpb24obmFtZSl7aWYoIXRoaXMuZWF0Q29udGV4dHVhbChuYW1lKSl0aGlzLnVuZXhwZWN0ZWQoKTt9OyAvLyBUZXN0IHdoZXRoZXIgYSBzZW1pY29sb24gY2FuIGJlIGluc2VydGVkIGF0IHRoZSBjdXJyZW50IHBvc2l0aW9uLlxucHAuY2FuSW5zZXJ0U2VtaWNvbG9uID0gZnVuY3Rpb24oKXtyZXR1cm4gdGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLmVvZiB8fCB0aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuYnJhY2VSIHx8IF93aGl0ZXNwYWNlLmxpbmVCcmVhay50ZXN0KHRoaXMuaW5wdXQuc2xpY2UodGhpcy5sYXN0VG9rRW5kLHRoaXMuc3RhcnQpKTt9O3BwLmluc2VydFNlbWljb2xvbiA9IGZ1bmN0aW9uKCl7aWYodGhpcy5jYW5JbnNlcnRTZW1pY29sb24oKSl7aWYodGhpcy5vcHRpb25zLm9uSW5zZXJ0ZWRTZW1pY29sb24pdGhpcy5vcHRpb25zLm9uSW5zZXJ0ZWRTZW1pY29sb24odGhpcy5sYXN0VG9rRW5kLHRoaXMubGFzdFRva0VuZExvYyk7cmV0dXJuIHRydWU7fX07IC8vIENvbnN1bWUgYSBzZW1pY29sb24sIG9yLCBmYWlsaW5nIHRoYXQsIHNlZSBpZiB3ZSBhcmUgYWxsb3dlZCB0b1xuLy8gcHJldGVuZCB0aGF0IHRoZXJlIGlzIGEgc2VtaWNvbG9uIGF0IHRoaXMgcG9zaXRpb24uXG5wcC5zZW1pY29sb24gPSBmdW5jdGlvbigpe2lmKCF0aGlzLmVhdChfdG9rZW50eXBlLnR5cGVzLnNlbWkpICYmICF0aGlzLmluc2VydFNlbWljb2xvbigpKXRoaXMudW5leHBlY3RlZCgpO307cHAuYWZ0ZXJUcmFpbGluZ0NvbW1hID0gZnVuY3Rpb24odG9rVHlwZSl7aWYodGhpcy50eXBlID09IHRva1R5cGUpe2lmKHRoaXMub3B0aW9ucy5vblRyYWlsaW5nQ29tbWEpdGhpcy5vcHRpb25zLm9uVHJhaWxpbmdDb21tYSh0aGlzLmxhc3RUb2tTdGFydCx0aGlzLmxhc3RUb2tTdGFydExvYyk7dGhpcy5uZXh0KCk7cmV0dXJuIHRydWU7fX07IC8vIEV4cGVjdCBhIHRva2VuIG9mIGEgZ2l2ZW4gdHlwZS4gSWYgZm91bmQsIGNvbnN1bWUgaXQsIG90aGVyd2lzZSxcbi8vIHJhaXNlIGFuIHVuZXhwZWN0ZWQgdG9rZW4gZXJyb3IuXG5wcC5leHBlY3QgPSBmdW5jdGlvbih0eXBlKXt0aGlzLmVhdCh0eXBlKSB8fCB0aGlzLnVuZXhwZWN0ZWQoKTt9OyAvLyBSYWlzZSBhbiB1bmV4cGVjdGVkIHRva2VuIGVycm9yLlxucHAudW5leHBlY3RlZCA9IGZ1bmN0aW9uKHBvcyl7dGhpcy5yYWlzZShwb3MgIT0gbnVsbD9wb3M6dGhpcy5zdGFydCxcIlVuZXhwZWN0ZWQgdG9rZW5cIik7fTt9LHtcIi4vc3RhdGVcIjoxMCxcIi4vdG9rZW50eXBlXCI6MTQsXCIuL3doaXRlc3BhY2VcIjoxNn1dLDEwOltmdW5jdGlvbihfZGVyZXFfLG1vZHVsZSxleHBvcnRzKXtcInVzZSBzdHJpY3RcIjtleHBvcnRzLl9fZXNNb2R1bGUgPSB0cnVlO2Z1bmN0aW9uIF9jbGFzc0NhbGxDaGVjayhpbnN0YW5jZSxDb25zdHJ1Y3Rvcil7aWYoIShpbnN0YW5jZSBpbnN0YW5jZW9mIENvbnN0cnVjdG9yKSl7dGhyb3cgbmV3IFR5cGVFcnJvcihcIkNhbm5vdCBjYWxsIGEgY2xhc3MgYXMgYSBmdW5jdGlvblwiKTt9fXZhciBfaWRlbnRpZmllcj1fZGVyZXFfKFwiLi9pZGVudGlmaWVyXCIpO3ZhciBfdG9rZW50eXBlPV9kZXJlcV8oXCIuL3Rva2VudHlwZVwiKTt2YXIgX3doaXRlc3BhY2U9X2RlcmVxXyhcIi4vd2hpdGVzcGFjZVwiKTt2YXIgX29wdGlvbnM9X2RlcmVxXyhcIi4vb3B0aW9uc1wiKTsgLy8gUmVnaXN0ZXJlZCBwbHVnaW5zXG52YXIgcGx1Z2lucz17fTtleHBvcnRzLnBsdWdpbnMgPSBwbHVnaW5zO3ZhciBQYXJzZXI9KGZ1bmN0aW9uKCl7ZnVuY3Rpb24gUGFyc2VyKG9wdGlvbnMsaW5wdXQsc3RhcnRQb3Mpe19jbGFzc0NhbGxDaGVjayh0aGlzLFBhcnNlcik7dGhpcy5vcHRpb25zID0gX29wdGlvbnMuZ2V0T3B0aW9ucyhvcHRpb25zKTt0aGlzLnNvdXJjZUZpbGUgPSB0aGlzLm9wdGlvbnMuc291cmNlRmlsZTt0aGlzLmlzS2V5d29yZCA9IF9pZGVudGlmaWVyLmtleXdvcmRzW3RoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2PzY6NV07dGhpcy5pc1Jlc2VydmVkV29yZCA9IF9pZGVudGlmaWVyLnJlc2VydmVkV29yZHNbdGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uXTt0aGlzLmlucHV0ID0gU3RyaW5nKGlucHV0KTsgLy8gVXNlZCB0byBzaWduYWwgdG8gY2FsbGVycyBvZiBgcmVhZFdvcmQxYCB3aGV0aGVyIHRoZSB3b3JkXG4vLyBjb250YWluZWQgYW55IGVzY2FwZSBzZXF1ZW5jZXMuIFRoaXMgaXMgbmVlZGVkIGJlY2F1c2Ugd29yZHMgd2l0aFxuLy8gZXNjYXBlIHNlcXVlbmNlcyBtdXN0IG5vdCBiZSBpbnRlcnByZXRlZCBhcyBrZXl3b3Jkcy5cbnRoaXMuY29udGFpbnNFc2MgPSBmYWxzZTsgLy8gTG9hZCBwbHVnaW5zXG50aGlzLmxvYWRQbHVnaW5zKHRoaXMub3B0aW9ucy5wbHVnaW5zKTsgLy8gU2V0IHVwIHRva2VuIHN0YXRlXG4vLyBUaGUgY3VycmVudCBwb3NpdGlvbiBvZiB0aGUgdG9rZW5pemVyIGluIHRoZSBpbnB1dC5cbmlmKHN0YXJ0UG9zKXt0aGlzLnBvcyA9IHN0YXJ0UG9zO3RoaXMubGluZVN0YXJ0ID0gTWF0aC5tYXgoMCx0aGlzLmlucHV0Lmxhc3RJbmRleE9mKFwiXFxuXCIsc3RhcnRQb3MpKTt0aGlzLmN1ckxpbmUgPSB0aGlzLmlucHV0LnNsaWNlKDAsdGhpcy5saW5lU3RhcnQpLnNwbGl0KF93aGl0ZXNwYWNlLmxpbmVCcmVhaykubGVuZ3RoO31lbHNlIHt0aGlzLnBvcyA9IHRoaXMubGluZVN0YXJ0ID0gMDt0aGlzLmN1ckxpbmUgPSAxO30gLy8gUHJvcGVydGllcyBvZiB0aGUgY3VycmVudCB0b2tlbjpcbi8vIEl0cyB0eXBlXG50aGlzLnR5cGUgPSBfdG9rZW50eXBlLnR5cGVzLmVvZjsgLy8gRm9yIHRva2VucyB0aGF0IGluY2x1ZGUgbW9yZSBpbmZvcm1hdGlvbiB0aGFuIHRoZWlyIHR5cGUsIHRoZSB2YWx1ZVxudGhpcy52YWx1ZSA9IG51bGw7IC8vIEl0cyBzdGFydCBhbmQgZW5kIG9mZnNldFxudGhpcy5zdGFydCA9IHRoaXMuZW5kID0gdGhpcy5wb3M7IC8vIEFuZCwgaWYgbG9jYXRpb25zIGFyZSB1c2VkLCB0aGUge2xpbmUsIGNvbHVtbn0gb2JqZWN0XG4vLyBjb3JyZXNwb25kaW5nIHRvIHRob3NlIG9mZnNldHNcbnRoaXMuc3RhcnRMb2MgPSB0aGlzLmVuZExvYyA9IHRoaXMuY3VyUG9zaXRpb24oKTsgLy8gUG9zaXRpb24gaW5mb3JtYXRpb24gZm9yIHRoZSBwcmV2aW91cyB0b2tlblxudGhpcy5sYXN0VG9rRW5kTG9jID0gdGhpcy5sYXN0VG9rU3RhcnRMb2MgPSBudWxsO3RoaXMubGFzdFRva1N0YXJ0ID0gdGhpcy5sYXN0VG9rRW5kID0gdGhpcy5wb3M7IC8vIFRoZSBjb250ZXh0IHN0YWNrIGlzIHVzZWQgdG8gc3VwZXJmaWNpYWxseSB0cmFjayBzeW50YWN0aWNcbi8vIGNvbnRleHQgdG8gcHJlZGljdCB3aGV0aGVyIGEgcmVndWxhciBleHByZXNzaW9uIGlzIGFsbG93ZWQgaW4gYVxuLy8gZ2l2ZW4gcG9zaXRpb24uXG50aGlzLmNvbnRleHQgPSB0aGlzLmluaXRpYWxDb250ZXh0KCk7dGhpcy5leHByQWxsb3dlZCA9IHRydWU7IC8vIEZpZ3VyZSBvdXQgaWYgaXQncyBhIG1vZHVsZSBjb2RlLlxudGhpcy5zdHJpY3QgPSB0aGlzLmluTW9kdWxlID0gdGhpcy5vcHRpb25zLnNvdXJjZVR5cGUgPT09IFwibW9kdWxlXCI7IC8vIFVzZWQgdG8gc2lnbmlmeSB0aGUgc3RhcnQgb2YgYSBwb3RlbnRpYWwgYXJyb3cgZnVuY3Rpb25cbnRoaXMucG90ZW50aWFsQXJyb3dBdCA9IC0xOyAvLyBGbGFncyB0byB0cmFjayB3aGV0aGVyIHdlIGFyZSBpbiBhIGZ1bmN0aW9uLCBhIGdlbmVyYXRvci5cbnRoaXMuaW5GdW5jdGlvbiA9IHRoaXMuaW5HZW5lcmF0b3IgPSBmYWxzZTsgLy8gTGFiZWxzIGluIHNjb3BlLlxudGhpcy5sYWJlbHMgPSBbXTsgLy8gSWYgZW5hYmxlZCwgc2tpcCBsZWFkaW5nIGhhc2hiYW5nIGxpbmUuXG5pZih0aGlzLnBvcyA9PT0gMCAmJiB0aGlzLm9wdGlvbnMuYWxsb3dIYXNoQmFuZyAmJiB0aGlzLmlucHV0LnNsaWNlKDAsMikgPT09ICcjIScpdGhpcy5za2lwTGluZUNvbW1lbnQoMik7fVBhcnNlci5wcm90b3R5cGUuZXh0ZW5kID0gZnVuY3Rpb24gZXh0ZW5kKG5hbWUsZil7dGhpc1tuYW1lXSA9IGYodGhpc1tuYW1lXSk7fTtQYXJzZXIucHJvdG90eXBlLmxvYWRQbHVnaW5zID0gZnVuY3Rpb24gbG9hZFBsdWdpbnMocGx1Z2luQ29uZmlncyl7Zm9yKHZhciBfbmFtZSBpbiBwbHVnaW5Db25maWdzKSB7dmFyIHBsdWdpbj1wbHVnaW5zW19uYW1lXTtpZighcGx1Z2luKXRocm93IG5ldyBFcnJvcihcIlBsdWdpbiAnXCIgKyBfbmFtZSArIFwiJyBub3QgZm91bmRcIik7cGx1Z2luKHRoaXMscGx1Z2luQ29uZmlnc1tfbmFtZV0pO319O1BhcnNlci5wcm90b3R5cGUucGFyc2UgPSBmdW5jdGlvbiBwYXJzZSgpe3ZhciBub2RlPXRoaXMub3B0aW9ucy5wcm9ncmFtIHx8IHRoaXMuc3RhcnROb2RlKCk7dGhpcy5uZXh0VG9rZW4oKTtyZXR1cm4gdGhpcy5wYXJzZVRvcExldmVsKG5vZGUpO307cmV0dXJuIFBhcnNlcjt9KSgpO2V4cG9ydHMuUGFyc2VyID0gUGFyc2VyO30se1wiLi9pZGVudGlmaWVyXCI6MixcIi4vb3B0aW9uc1wiOjgsXCIuL3Rva2VudHlwZVwiOjE0LFwiLi93aGl0ZXNwYWNlXCI6MTZ9XSwxMTpbZnVuY3Rpb24oX2RlcmVxXyxtb2R1bGUsZXhwb3J0cyl7XCJ1c2Ugc3RyaWN0XCI7dmFyIF90b2tlbnR5cGU9X2RlcmVxXyhcIi4vdG9rZW50eXBlXCIpO3ZhciBfc3RhdGU9X2RlcmVxXyhcIi4vc3RhdGVcIik7dmFyIF93aGl0ZXNwYWNlPV9kZXJlcV8oXCIuL3doaXRlc3BhY2VcIik7dmFyIHBwPV9zdGF0ZS5QYXJzZXIucHJvdG90eXBlOyAvLyAjIyMgU3RhdGVtZW50IHBhcnNpbmdcbi8vIFBhcnNlIGEgcHJvZ3JhbS4gSW5pdGlhbGl6ZXMgdGhlIHBhcnNlciwgcmVhZHMgYW55IG51bWJlciBvZlxuLy8gc3RhdGVtZW50cywgYW5kIHdyYXBzIHRoZW0gaW4gYSBQcm9ncmFtIG5vZGUuICBPcHRpb25hbGx5IHRha2VzIGFcbi8vIGBwcm9ncmFtYCBhcmd1bWVudC4gIElmIHByZXNlbnQsIHRoZSBzdGF0ZW1lbnRzIHdpbGwgYmUgYXBwZW5kZWRcbi8vIHRvIGl0cyBib2R5IGluc3RlYWQgb2YgY3JlYXRpbmcgYSBuZXcgbm9kZS5cbnBwLnBhcnNlVG9wTGV2ZWwgPSBmdW5jdGlvbihub2RlKXt2YXIgZmlyc3Q9dHJ1ZTtpZighbm9kZS5ib2R5KW5vZGUuYm9keSA9IFtdO3doaWxlKHRoaXMudHlwZSAhPT0gX3Rva2VudHlwZS50eXBlcy5lb2YpIHt2YXIgc3RtdD10aGlzLnBhcnNlU3RhdGVtZW50KHRydWUsdHJ1ZSk7bm9kZS5ib2R5LnB1c2goc3RtdCk7aWYoZmlyc3Qpe2lmKHRoaXMuaXNVc2VTdHJpY3Qoc3RtdCkpdGhpcy5zZXRTdHJpY3QodHJ1ZSk7Zmlyc3QgPSBmYWxzZTt9fXRoaXMubmV4dCgpO2lmKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KXtub2RlLnNvdXJjZVR5cGUgPSB0aGlzLm9wdGlvbnMuc291cmNlVHlwZTt9cmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLFwiUHJvZ3JhbVwiKTt9O3ZhciBsb29wTGFiZWw9e2tpbmQ6XCJsb29wXCJ9LHN3aXRjaExhYmVsPXtraW5kOlwic3dpdGNoXCJ9OyAvLyBQYXJzZSBhIHNpbmdsZSBzdGF0ZW1lbnQuXG4vL1xuLy8gSWYgZXhwZWN0aW5nIGEgc3RhdGVtZW50IGFuZCBmaW5kaW5nIGEgc2xhc2ggb3BlcmF0b3IsIHBhcnNlIGFcbi8vIHJlZ3VsYXIgZXhwcmVzc2lvbiBsaXRlcmFsLiBUaGlzIGlzIHRvIGhhbmRsZSBjYXNlcyBsaWtlXG4vLyBgaWYgKGZvbykgL2JsYWgvLmV4ZWMoZm9vKWAsIHdoZXJlIGxvb2tpbmcgYXQgdGhlIHByZXZpb3VzIHRva2VuXG4vLyBkb2VzIG5vdCBoZWxwLlxucHAucGFyc2VTdGF0ZW1lbnQgPSBmdW5jdGlvbihkZWNsYXJhdGlvbix0b3BMZXZlbCl7dmFyIHN0YXJ0dHlwZT10aGlzLnR5cGUsbm9kZT10aGlzLnN0YXJ0Tm9kZSgpOyAvLyBNb3N0IHR5cGVzIG9mIHN0YXRlbWVudHMgYXJlIHJlY29nbml6ZWQgYnkgdGhlIGtleXdvcmQgdGhleVxuLy8gc3RhcnQgd2l0aC4gTWFueSBhcmUgdHJpdmlhbCB0byBwYXJzZSwgc29tZSByZXF1aXJlIGEgYml0IG9mXG4vLyBjb21wbGV4aXR5Llxuc3dpdGNoKHN0YXJ0dHlwZSl7Y2FzZSBfdG9rZW50eXBlLnR5cGVzLl9icmVhazpjYXNlIF90b2tlbnR5cGUudHlwZXMuX2NvbnRpbnVlOnJldHVybiB0aGlzLnBhcnNlQnJlYWtDb250aW51ZVN0YXRlbWVudChub2RlLHN0YXJ0dHlwZS5rZXl3b3JkKTtjYXNlIF90b2tlbnR5cGUudHlwZXMuX2RlYnVnZ2VyOnJldHVybiB0aGlzLnBhcnNlRGVidWdnZXJTdGF0ZW1lbnQobm9kZSk7Y2FzZSBfdG9rZW50eXBlLnR5cGVzLl9kbzpyZXR1cm4gdGhpcy5wYXJzZURvU3RhdGVtZW50KG5vZGUpO2Nhc2UgX3Rva2VudHlwZS50eXBlcy5fZm9yOnJldHVybiB0aGlzLnBhcnNlRm9yU3RhdGVtZW50KG5vZGUpO2Nhc2UgX3Rva2VudHlwZS50eXBlcy5fZnVuY3Rpb246aWYoIWRlY2xhcmF0aW9uICYmIHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KXRoaXMudW5leHBlY3RlZCgpO3JldHVybiB0aGlzLnBhcnNlRnVuY3Rpb25TdGF0ZW1lbnQobm9kZSk7Y2FzZSBfdG9rZW50eXBlLnR5cGVzLl9jbGFzczppZighZGVjbGFyYXRpb24pdGhpcy51bmV4cGVjdGVkKCk7cmV0dXJuIHRoaXMucGFyc2VDbGFzcyhub2RlLHRydWUpO2Nhc2UgX3Rva2VudHlwZS50eXBlcy5faWY6cmV0dXJuIHRoaXMucGFyc2VJZlN0YXRlbWVudChub2RlKTtjYXNlIF90b2tlbnR5cGUudHlwZXMuX3JldHVybjpyZXR1cm4gdGhpcy5wYXJzZVJldHVyblN0YXRlbWVudChub2RlKTtjYXNlIF90b2tlbnR5cGUudHlwZXMuX3N3aXRjaDpyZXR1cm4gdGhpcy5wYXJzZVN3aXRjaFN0YXRlbWVudChub2RlKTtjYXNlIF90b2tlbnR5cGUudHlwZXMuX3Rocm93OnJldHVybiB0aGlzLnBhcnNlVGhyb3dTdGF0ZW1lbnQobm9kZSk7Y2FzZSBfdG9rZW50eXBlLnR5cGVzLl90cnk6cmV0dXJuIHRoaXMucGFyc2VUcnlTdGF0ZW1lbnQobm9kZSk7Y2FzZSBfdG9rZW50eXBlLnR5cGVzLl9sZXQ6Y2FzZSBfdG9rZW50eXBlLnR5cGVzLl9jb25zdDppZighZGVjbGFyYXRpb24pdGhpcy51bmV4cGVjdGVkKCk7IC8vIE5PVEU6IGZhbGxzIHRocm91Z2ggdG8gX3ZhclxuY2FzZSBfdG9rZW50eXBlLnR5cGVzLl92YXI6cmV0dXJuIHRoaXMucGFyc2VWYXJTdGF0ZW1lbnQobm9kZSxzdGFydHR5cGUpO2Nhc2UgX3Rva2VudHlwZS50eXBlcy5fd2hpbGU6cmV0dXJuIHRoaXMucGFyc2VXaGlsZVN0YXRlbWVudChub2RlKTtjYXNlIF90b2tlbnR5cGUudHlwZXMuX3dpdGg6cmV0dXJuIHRoaXMucGFyc2VXaXRoU3RhdGVtZW50KG5vZGUpO2Nhc2UgX3Rva2VudHlwZS50eXBlcy5icmFjZUw6cmV0dXJuIHRoaXMucGFyc2VCbG9jaygpO2Nhc2UgX3Rva2VudHlwZS50eXBlcy5zZW1pOnJldHVybiB0aGlzLnBhcnNlRW1wdHlTdGF0ZW1lbnQobm9kZSk7Y2FzZSBfdG9rZW50eXBlLnR5cGVzLl9leHBvcnQ6Y2FzZSBfdG9rZW50eXBlLnR5cGVzLl9pbXBvcnQ6aWYoIXRoaXMub3B0aW9ucy5hbGxvd0ltcG9ydEV4cG9ydEV2ZXJ5d2hlcmUpe2lmKCF0b3BMZXZlbCl0aGlzLnJhaXNlKHRoaXMuc3RhcnQsXCInaW1wb3J0JyBhbmQgJ2V4cG9ydCcgbWF5IG9ubHkgYXBwZWFyIGF0IHRoZSB0b3AgbGV2ZWxcIik7aWYoIXRoaXMuaW5Nb2R1bGUpdGhpcy5yYWlzZSh0aGlzLnN0YXJ0LFwiJ2ltcG9ydCcgYW5kICdleHBvcnQnIG1heSBhcHBlYXIgb25seSB3aXRoICdzb3VyY2VUeXBlOiBtb2R1bGUnXCIpO31yZXR1cm4gc3RhcnR0eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLl9pbXBvcnQ/dGhpcy5wYXJzZUltcG9ydChub2RlKTp0aGlzLnBhcnNlRXhwb3J0KG5vZGUpOyAvLyBJZiB0aGUgc3RhdGVtZW50IGRvZXMgbm90IHN0YXJ0IHdpdGggYSBzdGF0ZW1lbnQga2V5d29yZCBvciBhXG4vLyBicmFjZSwgaXQncyBhbiBFeHByZXNzaW9uU3RhdGVtZW50IG9yIExhYmVsZWRTdGF0ZW1lbnQuIFdlXG4vLyBzaW1wbHkgc3RhcnQgcGFyc2luZyBhbiBleHByZXNzaW9uLCBhbmQgYWZ0ZXJ3YXJkcywgaWYgdGhlXG4vLyBuZXh0IHRva2VuIGlzIGEgY29sb24gYW5kIHRoZSBleHByZXNzaW9uIHdhcyBhIHNpbXBsZVxuLy8gSWRlbnRpZmllciBub2RlLCB3ZSBzd2l0Y2ggdG8gaW50ZXJwcmV0aW5nIGl0IGFzIGEgbGFiZWwuXG5kZWZhdWx0OnZhciBtYXliZU5hbWU9dGhpcy52YWx1ZSxleHByPXRoaXMucGFyc2VFeHByZXNzaW9uKCk7aWYoc3RhcnR0eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLm5hbWUgJiYgZXhwci50eXBlID09PSBcIklkZW50aWZpZXJcIiAmJiB0aGlzLmVhdChfdG9rZW50eXBlLnR5cGVzLmNvbG9uKSlyZXR1cm4gdGhpcy5wYXJzZUxhYmVsZWRTdGF0ZW1lbnQobm9kZSxtYXliZU5hbWUsZXhwcik7ZWxzZSByZXR1cm4gdGhpcy5wYXJzZUV4cHJlc3Npb25TdGF0ZW1lbnQobm9kZSxleHByKTt9fTtwcC5wYXJzZUJyZWFrQ29udGludWVTdGF0ZW1lbnQgPSBmdW5jdGlvbihub2RlLGtleXdvcmQpe3ZhciBpc0JyZWFrPWtleXdvcmQgPT0gXCJicmVha1wiO3RoaXMubmV4dCgpO2lmKHRoaXMuZWF0KF90b2tlbnR5cGUudHlwZXMuc2VtaSkgfHwgdGhpcy5pbnNlcnRTZW1pY29sb24oKSlub2RlLmxhYmVsID0gbnVsbDtlbHNlIGlmKHRoaXMudHlwZSAhPT0gX3Rva2VudHlwZS50eXBlcy5uYW1lKXRoaXMudW5leHBlY3RlZCgpO2Vsc2Uge25vZGUubGFiZWwgPSB0aGlzLnBhcnNlSWRlbnQoKTt0aGlzLnNlbWljb2xvbigpO30gLy8gVmVyaWZ5IHRoYXQgdGhlcmUgaXMgYW4gYWN0dWFsIGRlc3RpbmF0aW9uIHRvIGJyZWFrIG9yXG4vLyBjb250aW51ZSB0by5cbmZvcih2YXIgaT0wO2kgPCB0aGlzLmxhYmVscy5sZW5ndGg7KytpKSB7dmFyIGxhYj10aGlzLmxhYmVsc1tpXTtpZihub2RlLmxhYmVsID09IG51bGwgfHwgbGFiLm5hbWUgPT09IG5vZGUubGFiZWwubmFtZSl7aWYobGFiLmtpbmQgIT0gbnVsbCAmJiAoaXNCcmVhayB8fCBsYWIua2luZCA9PT0gXCJsb29wXCIpKWJyZWFrO2lmKG5vZGUubGFiZWwgJiYgaXNCcmVhaylicmVhazt9fWlmKGkgPT09IHRoaXMubGFiZWxzLmxlbmd0aCl0aGlzLnJhaXNlKG5vZGUuc3RhcnQsXCJVbnN5bnRhY3RpYyBcIiArIGtleXdvcmQpO3JldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSxpc0JyZWFrP1wiQnJlYWtTdGF0ZW1lbnRcIjpcIkNvbnRpbnVlU3RhdGVtZW50XCIpO307cHAucGFyc2VEZWJ1Z2dlclN0YXRlbWVudCA9IGZ1bmN0aW9uKG5vZGUpe3RoaXMubmV4dCgpO3RoaXMuc2VtaWNvbG9uKCk7cmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLFwiRGVidWdnZXJTdGF0ZW1lbnRcIik7fTtwcC5wYXJzZURvU3RhdGVtZW50ID0gZnVuY3Rpb24obm9kZSl7dGhpcy5uZXh0KCk7dGhpcy5sYWJlbHMucHVzaChsb29wTGFiZWwpO25vZGUuYm9keSA9IHRoaXMucGFyc2VTdGF0ZW1lbnQoZmFsc2UpO3RoaXMubGFiZWxzLnBvcCgpO3RoaXMuZXhwZWN0KF90b2tlbnR5cGUudHlwZXMuX3doaWxlKTtub2RlLnRlc3QgPSB0aGlzLnBhcnNlUGFyZW5FeHByZXNzaW9uKCk7aWYodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYpdGhpcy5lYXQoX3Rva2VudHlwZS50eXBlcy5zZW1pKTtlbHNlIHRoaXMuc2VtaWNvbG9uKCk7cmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLFwiRG9XaGlsZVN0YXRlbWVudFwiKTt9OyAvLyBEaXNhbWJpZ3VhdGluZyBiZXR3ZWVuIGEgYGZvcmAgYW5kIGEgYGZvcmAvYGluYCBvciBgZm9yYC9gb2ZgXG4vLyBsb29wIGlzIG5vbi10cml2aWFsLiBCYXNpY2FsbHksIHdlIGhhdmUgdG8gcGFyc2UgdGhlIGluaXQgYHZhcmBcbi8vIHN0YXRlbWVudCBvciBleHByZXNzaW9uLCBkaXNhbGxvd2luZyB0aGUgYGluYCBvcGVyYXRvciAoc2VlXG4vLyB0aGUgc2Vjb25kIHBhcmFtZXRlciB0byBgcGFyc2VFeHByZXNzaW9uYCksIGFuZCB0aGVuIGNoZWNrXG4vLyB3aGV0aGVyIHRoZSBuZXh0IHRva2VuIGlzIGBpbmAgb3IgYG9mYC4gV2hlbiB0aGVyZSBpcyBubyBpbml0XG4vLyBwYXJ0IChzZW1pY29sb24gaW1tZWRpYXRlbHkgYWZ0ZXIgdGhlIG9wZW5pbmcgcGFyZW50aGVzaXMpLCBpdFxuLy8gaXMgYSByZWd1bGFyIGBmb3JgIGxvb3AuXG5wcC5wYXJzZUZvclN0YXRlbWVudCA9IGZ1bmN0aW9uKG5vZGUpe3RoaXMubmV4dCgpO3RoaXMubGFiZWxzLnB1c2gobG9vcExhYmVsKTt0aGlzLmV4cGVjdChfdG9rZW50eXBlLnR5cGVzLnBhcmVuTCk7aWYodGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLnNlbWkpcmV0dXJuIHRoaXMucGFyc2VGb3Iobm9kZSxudWxsKTtpZih0aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuX3ZhciB8fCB0aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuX2xldCB8fCB0aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuX2NvbnN0KXt2YXIgX2luaXQ9dGhpcy5zdGFydE5vZGUoKSx2YXJLaW5kPXRoaXMudHlwZTt0aGlzLm5leHQoKTt0aGlzLnBhcnNlVmFyKF9pbml0LHRydWUsdmFyS2luZCk7dGhpcy5maW5pc2hOb2RlKF9pbml0LFwiVmFyaWFibGVEZWNsYXJhdGlvblwiKTtpZigodGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLl9pbiB8fCB0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNiAmJiB0aGlzLmlzQ29udGV4dHVhbChcIm9mXCIpKSAmJiBfaW5pdC5kZWNsYXJhdGlvbnMubGVuZ3RoID09PSAxICYmICEodmFyS2luZCAhPT0gX3Rva2VudHlwZS50eXBlcy5fdmFyICYmIF9pbml0LmRlY2xhcmF0aW9uc1swXS5pbml0KSlyZXR1cm4gdGhpcy5wYXJzZUZvckluKG5vZGUsX2luaXQpO3JldHVybiB0aGlzLnBhcnNlRm9yKG5vZGUsX2luaXQpO312YXIgcmVmU2hvcnRoYW5kRGVmYXVsdFBvcz17c3RhcnQ6MH07dmFyIGluaXQ9dGhpcy5wYXJzZUV4cHJlc3Npb24odHJ1ZSxyZWZTaG9ydGhhbmREZWZhdWx0UG9zKTtpZih0aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuX2luIHx8IHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2ICYmIHRoaXMuaXNDb250ZXh0dWFsKFwib2ZcIikpe3RoaXMudG9Bc3NpZ25hYmxlKGluaXQpO3RoaXMuY2hlY2tMVmFsKGluaXQpO3JldHVybiB0aGlzLnBhcnNlRm9ySW4obm9kZSxpbml0KTt9ZWxzZSBpZihyZWZTaG9ydGhhbmREZWZhdWx0UG9zLnN0YXJ0KXt0aGlzLnVuZXhwZWN0ZWQocmVmU2hvcnRoYW5kRGVmYXVsdFBvcy5zdGFydCk7fXJldHVybiB0aGlzLnBhcnNlRm9yKG5vZGUsaW5pdCk7fTtwcC5wYXJzZUZ1bmN0aW9uU3RhdGVtZW50ID0gZnVuY3Rpb24obm9kZSl7dGhpcy5uZXh0KCk7cmV0dXJuIHRoaXMucGFyc2VGdW5jdGlvbihub2RlLHRydWUpO307cHAucGFyc2VJZlN0YXRlbWVudCA9IGZ1bmN0aW9uKG5vZGUpe3RoaXMubmV4dCgpO25vZGUudGVzdCA9IHRoaXMucGFyc2VQYXJlbkV4cHJlc3Npb24oKTtub2RlLmNvbnNlcXVlbnQgPSB0aGlzLnBhcnNlU3RhdGVtZW50KGZhbHNlKTtub2RlLmFsdGVybmF0ZSA9IHRoaXMuZWF0KF90b2tlbnR5cGUudHlwZXMuX2Vsc2UpP3RoaXMucGFyc2VTdGF0ZW1lbnQoZmFsc2UpOm51bGw7cmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLFwiSWZTdGF0ZW1lbnRcIik7fTtwcC5wYXJzZVJldHVyblN0YXRlbWVudCA9IGZ1bmN0aW9uKG5vZGUpe2lmKCF0aGlzLmluRnVuY3Rpb24gJiYgIXRoaXMub3B0aW9ucy5hbGxvd1JldHVybk91dHNpZGVGdW5jdGlvbil0aGlzLnJhaXNlKHRoaXMuc3RhcnQsXCIncmV0dXJuJyBvdXRzaWRlIG9mIGZ1bmN0aW9uXCIpO3RoaXMubmV4dCgpOyAvLyBJbiBgcmV0dXJuYCAoYW5kIGBicmVha2AvYGNvbnRpbnVlYCksIHRoZSBrZXl3b3JkcyB3aXRoXG4vLyBvcHRpb25hbCBhcmd1bWVudHMsIHdlIGVhZ2VybHkgbG9vayBmb3IgYSBzZW1pY29sb24gb3IgdGhlXG4vLyBwb3NzaWJpbGl0eSB0byBpbnNlcnQgb25lLlxuaWYodGhpcy5lYXQoX3Rva2VudHlwZS50eXBlcy5zZW1pKSB8fCB0aGlzLmluc2VydFNlbWljb2xvbigpKW5vZGUuYXJndW1lbnQgPSBudWxsO2Vsc2Uge25vZGUuYXJndW1lbnQgPSB0aGlzLnBhcnNlRXhwcmVzc2lvbigpO3RoaXMuc2VtaWNvbG9uKCk7fXJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSxcIlJldHVyblN0YXRlbWVudFwiKTt9O3BwLnBhcnNlU3dpdGNoU3RhdGVtZW50ID0gZnVuY3Rpb24obm9kZSl7dGhpcy5uZXh0KCk7bm9kZS5kaXNjcmltaW5hbnQgPSB0aGlzLnBhcnNlUGFyZW5FeHByZXNzaW9uKCk7bm9kZS5jYXNlcyA9IFtdO3RoaXMuZXhwZWN0KF90b2tlbnR5cGUudHlwZXMuYnJhY2VMKTt0aGlzLmxhYmVscy5wdXNoKHN3aXRjaExhYmVsKTsgLy8gU3RhdGVtZW50cyB1bmRlciBtdXN0IGJlIGdyb3VwZWQgKGJ5IGxhYmVsKSBpbiBTd2l0Y2hDYXNlXG4vLyBub2Rlcy4gYGN1cmAgaXMgdXNlZCB0byBrZWVwIHRoZSBub2RlIHRoYXQgd2UgYXJlIGN1cnJlbnRseVxuLy8gYWRkaW5nIHN0YXRlbWVudHMgdG8uXG5mb3IodmFyIGN1cixzYXdEZWZhdWx0PWZhbHNlO3RoaXMudHlwZSAhPSBfdG9rZW50eXBlLnR5cGVzLmJyYWNlUjspIHtpZih0aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuX2Nhc2UgfHwgdGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLl9kZWZhdWx0KXt2YXIgaXNDYXNlPXRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5fY2FzZTtpZihjdXIpdGhpcy5maW5pc2hOb2RlKGN1cixcIlN3aXRjaENhc2VcIik7bm9kZS5jYXNlcy5wdXNoKGN1ciA9IHRoaXMuc3RhcnROb2RlKCkpO2N1ci5jb25zZXF1ZW50ID0gW107dGhpcy5uZXh0KCk7aWYoaXNDYXNlKXtjdXIudGVzdCA9IHRoaXMucGFyc2VFeHByZXNzaW9uKCk7fWVsc2Uge2lmKHNhd0RlZmF1bHQpdGhpcy5yYWlzZSh0aGlzLmxhc3RUb2tTdGFydCxcIk11bHRpcGxlIGRlZmF1bHQgY2xhdXNlc1wiKTtzYXdEZWZhdWx0ID0gdHJ1ZTtjdXIudGVzdCA9IG51bGw7fXRoaXMuZXhwZWN0KF90b2tlbnR5cGUudHlwZXMuY29sb24pO31lbHNlIHtpZighY3VyKXRoaXMudW5leHBlY3RlZCgpO2N1ci5jb25zZXF1ZW50LnB1c2godGhpcy5wYXJzZVN0YXRlbWVudCh0cnVlKSk7fX1pZihjdXIpdGhpcy5maW5pc2hOb2RlKGN1cixcIlN3aXRjaENhc2VcIik7dGhpcy5uZXh0KCk7IC8vIENsb3NpbmcgYnJhY2VcbnRoaXMubGFiZWxzLnBvcCgpO3JldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSxcIlN3aXRjaFN0YXRlbWVudFwiKTt9O3BwLnBhcnNlVGhyb3dTdGF0ZW1lbnQgPSBmdW5jdGlvbihub2RlKXt0aGlzLm5leHQoKTtpZihfd2hpdGVzcGFjZS5saW5lQnJlYWsudGVzdCh0aGlzLmlucHV0LnNsaWNlKHRoaXMubGFzdFRva0VuZCx0aGlzLnN0YXJ0KSkpdGhpcy5yYWlzZSh0aGlzLmxhc3RUb2tFbmQsXCJJbGxlZ2FsIG5ld2xpbmUgYWZ0ZXIgdGhyb3dcIik7bm9kZS5hcmd1bWVudCA9IHRoaXMucGFyc2VFeHByZXNzaW9uKCk7dGhpcy5zZW1pY29sb24oKTtyZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsXCJUaHJvd1N0YXRlbWVudFwiKTt9OyAvLyBSZXVzZWQgZW1wdHkgYXJyYXkgYWRkZWQgZm9yIG5vZGUgZmllbGRzIHRoYXQgYXJlIGFsd2F5cyBlbXB0eS5cbnZhciBlbXB0eT1bXTtwcC5wYXJzZVRyeVN0YXRlbWVudCA9IGZ1bmN0aW9uKG5vZGUpe3RoaXMubmV4dCgpO25vZGUuYmxvY2sgPSB0aGlzLnBhcnNlQmxvY2soKTtub2RlLmhhbmRsZXIgPSBudWxsO2lmKHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5fY2F0Y2gpe3ZhciBjbGF1c2U9dGhpcy5zdGFydE5vZGUoKTt0aGlzLm5leHQoKTt0aGlzLmV4cGVjdChfdG9rZW50eXBlLnR5cGVzLnBhcmVuTCk7Y2xhdXNlLnBhcmFtID0gdGhpcy5wYXJzZUJpbmRpbmdBdG9tKCk7dGhpcy5jaGVja0xWYWwoY2xhdXNlLnBhcmFtLHRydWUpO3RoaXMuZXhwZWN0KF90b2tlbnR5cGUudHlwZXMucGFyZW5SKTtjbGF1c2UuZ3VhcmQgPSBudWxsO2NsYXVzZS5ib2R5ID0gdGhpcy5wYXJzZUJsb2NrKCk7bm9kZS5oYW5kbGVyID0gdGhpcy5maW5pc2hOb2RlKGNsYXVzZSxcIkNhdGNoQ2xhdXNlXCIpO31ub2RlLmd1YXJkZWRIYW5kbGVycyA9IGVtcHR5O25vZGUuZmluYWxpemVyID0gdGhpcy5lYXQoX3Rva2VudHlwZS50eXBlcy5fZmluYWxseSk/dGhpcy5wYXJzZUJsb2NrKCk6bnVsbDtpZighbm9kZS5oYW5kbGVyICYmICFub2RlLmZpbmFsaXplcil0aGlzLnJhaXNlKG5vZGUuc3RhcnQsXCJNaXNzaW5nIGNhdGNoIG9yIGZpbmFsbHkgY2xhdXNlXCIpO3JldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSxcIlRyeVN0YXRlbWVudFwiKTt9O3BwLnBhcnNlVmFyU3RhdGVtZW50ID0gZnVuY3Rpb24obm9kZSxraW5kKXt0aGlzLm5leHQoKTt0aGlzLnBhcnNlVmFyKG5vZGUsZmFsc2Usa2luZCk7dGhpcy5zZW1pY29sb24oKTtyZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsXCJWYXJpYWJsZURlY2xhcmF0aW9uXCIpO307cHAucGFyc2VXaGlsZVN0YXRlbWVudCA9IGZ1bmN0aW9uKG5vZGUpe3RoaXMubmV4dCgpO25vZGUudGVzdCA9IHRoaXMucGFyc2VQYXJlbkV4cHJlc3Npb24oKTt0aGlzLmxhYmVscy5wdXNoKGxvb3BMYWJlbCk7bm9kZS5ib2R5ID0gdGhpcy5wYXJzZVN0YXRlbWVudChmYWxzZSk7dGhpcy5sYWJlbHMucG9wKCk7cmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLFwiV2hpbGVTdGF0ZW1lbnRcIik7fTtwcC5wYXJzZVdpdGhTdGF0ZW1lbnQgPSBmdW5jdGlvbihub2RlKXtpZih0aGlzLnN0cmljdCl0aGlzLnJhaXNlKHRoaXMuc3RhcnQsXCInd2l0aCcgaW4gc3RyaWN0IG1vZGVcIik7dGhpcy5uZXh0KCk7bm9kZS5vYmplY3QgPSB0aGlzLnBhcnNlUGFyZW5FeHByZXNzaW9uKCk7bm9kZS5ib2R5ID0gdGhpcy5wYXJzZVN0YXRlbWVudChmYWxzZSk7cmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLFwiV2l0aFN0YXRlbWVudFwiKTt9O3BwLnBhcnNlRW1wdHlTdGF0ZW1lbnQgPSBmdW5jdGlvbihub2RlKXt0aGlzLm5leHQoKTtyZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsXCJFbXB0eVN0YXRlbWVudFwiKTt9O3BwLnBhcnNlTGFiZWxlZFN0YXRlbWVudCA9IGZ1bmN0aW9uKG5vZGUsbWF5YmVOYW1lLGV4cHIpe2Zvcih2YXIgaT0wO2kgPCB0aGlzLmxhYmVscy5sZW5ndGg7KytpKSB7aWYodGhpcy5sYWJlbHNbaV0ubmFtZSA9PT0gbWF5YmVOYW1lKXRoaXMucmFpc2UoZXhwci5zdGFydCxcIkxhYmVsICdcIiArIG1heWJlTmFtZSArIFwiJyBpcyBhbHJlYWR5IGRlY2xhcmVkXCIpO312YXIga2luZD10aGlzLnR5cGUuaXNMb29wP1wibG9vcFwiOnRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5fc3dpdGNoP1wic3dpdGNoXCI6bnVsbDtmb3IodmFyIGk9dGhpcy5sYWJlbHMubGVuZ3RoIC0gMTtpID49IDA7aS0tKSB7dmFyIGxhYmVsPXRoaXMubGFiZWxzW2ldO2lmKGxhYmVsLnN0YXRlbWVudFN0YXJ0ID09IG5vZGUuc3RhcnQpe2xhYmVsLnN0YXRlbWVudFN0YXJ0ID0gdGhpcy5zdGFydDtsYWJlbC5raW5kID0ga2luZDt9ZWxzZSBicmVhazt9dGhpcy5sYWJlbHMucHVzaCh7bmFtZTptYXliZU5hbWUsa2luZDpraW5kLHN0YXRlbWVudFN0YXJ0OnRoaXMuc3RhcnR9KTtub2RlLmJvZHkgPSB0aGlzLnBhcnNlU3RhdGVtZW50KHRydWUpO3RoaXMubGFiZWxzLnBvcCgpO25vZGUubGFiZWwgPSBleHByO3JldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSxcIkxhYmVsZWRTdGF0ZW1lbnRcIik7fTtwcC5wYXJzZUV4cHJlc3Npb25TdGF0ZW1lbnQgPSBmdW5jdGlvbihub2RlLGV4cHIpe25vZGUuZXhwcmVzc2lvbiA9IGV4cHI7dGhpcy5zZW1pY29sb24oKTtyZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsXCJFeHByZXNzaW9uU3RhdGVtZW50XCIpO307IC8vIFBhcnNlIGEgc2VtaWNvbG9uLWVuY2xvc2VkIGJsb2NrIG9mIHN0YXRlbWVudHMsIGhhbmRsaW5nIGBcInVzZVxuLy8gc3RyaWN0XCJgIGRlY2xhcmF0aW9ucyB3aGVuIGBhbGxvd1N0cmljdGAgaXMgdHJ1ZSAodXNlZCBmb3Jcbi8vIGZ1bmN0aW9uIGJvZGllcykuXG5wcC5wYXJzZUJsb2NrID0gZnVuY3Rpb24oYWxsb3dTdHJpY3Qpe3ZhciBub2RlPXRoaXMuc3RhcnROb2RlKCksZmlyc3Q9dHJ1ZSxvbGRTdHJpY3Q9dW5kZWZpbmVkO25vZGUuYm9keSA9IFtdO3RoaXMuZXhwZWN0KF90b2tlbnR5cGUudHlwZXMuYnJhY2VMKTt3aGlsZSghdGhpcy5lYXQoX3Rva2VudHlwZS50eXBlcy5icmFjZVIpKSB7dmFyIHN0bXQ9dGhpcy5wYXJzZVN0YXRlbWVudCh0cnVlKTtub2RlLmJvZHkucHVzaChzdG10KTtpZihmaXJzdCAmJiBhbGxvd1N0cmljdCAmJiB0aGlzLmlzVXNlU3RyaWN0KHN0bXQpKXtvbGRTdHJpY3QgPSB0aGlzLnN0cmljdDt0aGlzLnNldFN0cmljdCh0aGlzLnN0cmljdCA9IHRydWUpO31maXJzdCA9IGZhbHNlO31pZihvbGRTdHJpY3QgPT09IGZhbHNlKXRoaXMuc2V0U3RyaWN0KGZhbHNlKTtyZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsXCJCbG9ja1N0YXRlbWVudFwiKTt9OyAvLyBQYXJzZSBhIHJlZ3VsYXIgYGZvcmAgbG9vcC4gVGhlIGRpc2FtYmlndWF0aW9uIGNvZGUgaW5cbi8vIGBwYXJzZVN0YXRlbWVudGAgd2lsbCBhbHJlYWR5IGhhdmUgcGFyc2VkIHRoZSBpbml0IHN0YXRlbWVudCBvclxuLy8gZXhwcmVzc2lvbi5cbnBwLnBhcnNlRm9yID0gZnVuY3Rpb24obm9kZSxpbml0KXtub2RlLmluaXQgPSBpbml0O3RoaXMuZXhwZWN0KF90b2tlbnR5cGUudHlwZXMuc2VtaSk7bm9kZS50ZXN0ID0gdGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLnNlbWk/bnVsbDp0aGlzLnBhcnNlRXhwcmVzc2lvbigpO3RoaXMuZXhwZWN0KF90b2tlbnR5cGUudHlwZXMuc2VtaSk7bm9kZS51cGRhdGUgPSB0aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMucGFyZW5SP251bGw6dGhpcy5wYXJzZUV4cHJlc3Npb24oKTt0aGlzLmV4cGVjdChfdG9rZW50eXBlLnR5cGVzLnBhcmVuUik7bm9kZS5ib2R5ID0gdGhpcy5wYXJzZVN0YXRlbWVudChmYWxzZSk7dGhpcy5sYWJlbHMucG9wKCk7cmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLFwiRm9yU3RhdGVtZW50XCIpO307IC8vIFBhcnNlIGEgYGZvcmAvYGluYCBhbmQgYGZvcmAvYG9mYCBsb29wLCB3aGljaCBhcmUgYWxtb3N0XG4vLyBzYW1lIGZyb20gcGFyc2VyJ3MgcGVyc3BlY3RpdmUuXG5wcC5wYXJzZUZvckluID0gZnVuY3Rpb24obm9kZSxpbml0KXt2YXIgdHlwZT10aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuX2luP1wiRm9ySW5TdGF0ZW1lbnRcIjpcIkZvck9mU3RhdGVtZW50XCI7dGhpcy5uZXh0KCk7bm9kZS5sZWZ0ID0gaW5pdDtub2RlLnJpZ2h0ID0gdGhpcy5wYXJzZUV4cHJlc3Npb24oKTt0aGlzLmV4cGVjdChfdG9rZW50eXBlLnR5cGVzLnBhcmVuUik7bm9kZS5ib2R5ID0gdGhpcy5wYXJzZVN0YXRlbWVudChmYWxzZSk7dGhpcy5sYWJlbHMucG9wKCk7cmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLHR5cGUpO307IC8vIFBhcnNlIGEgbGlzdCBvZiB2YXJpYWJsZSBkZWNsYXJhdGlvbnMuXG5wcC5wYXJzZVZhciA9IGZ1bmN0aW9uKG5vZGUsaXNGb3Isa2luZCl7bm9kZS5kZWNsYXJhdGlvbnMgPSBbXTtub2RlLmtpbmQgPSBraW5kLmtleXdvcmQ7Zm9yKDs7KSB7dmFyIGRlY2w9dGhpcy5zdGFydE5vZGUoKTt0aGlzLnBhcnNlVmFySWQoZGVjbCk7aWYodGhpcy5lYXQoX3Rva2VudHlwZS50eXBlcy5lcSkpe2RlY2wuaW5pdCA9IHRoaXMucGFyc2VNYXliZUFzc2lnbihpc0Zvcik7fWVsc2UgaWYoa2luZCA9PT0gX3Rva2VudHlwZS50eXBlcy5fY29uc3QgJiYgISh0aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuX2luIHx8IHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2ICYmIHRoaXMuaXNDb250ZXh0dWFsKFwib2ZcIikpKXt0aGlzLnVuZXhwZWN0ZWQoKTt9ZWxzZSBpZihkZWNsLmlkLnR5cGUgIT0gXCJJZGVudGlmaWVyXCIgJiYgIShpc0ZvciAmJiAodGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLl9pbiB8fCB0aGlzLmlzQ29udGV4dHVhbChcIm9mXCIpKSkpe3RoaXMucmFpc2UodGhpcy5sYXN0VG9rRW5kLFwiQ29tcGxleCBiaW5kaW5nIHBhdHRlcm5zIHJlcXVpcmUgYW4gaW5pdGlhbGl6YXRpb24gdmFsdWVcIik7fWVsc2Uge2RlY2wuaW5pdCA9IG51bGw7fW5vZGUuZGVjbGFyYXRpb25zLnB1c2godGhpcy5maW5pc2hOb2RlKGRlY2wsXCJWYXJpYWJsZURlY2xhcmF0b3JcIikpO2lmKCF0aGlzLmVhdChfdG9rZW50eXBlLnR5cGVzLmNvbW1hKSlicmVhazt9cmV0dXJuIG5vZGU7fTtwcC5wYXJzZVZhcklkID0gZnVuY3Rpb24oZGVjbCl7ZGVjbC5pZCA9IHRoaXMucGFyc2VCaW5kaW5nQXRvbSgpO3RoaXMuY2hlY2tMVmFsKGRlY2wuaWQsdHJ1ZSk7fTsgLy8gUGFyc2UgYSBmdW5jdGlvbiBkZWNsYXJhdGlvbiBvciBsaXRlcmFsIChkZXBlbmRpbmcgb24gdGhlXG4vLyBgaXNTdGF0ZW1lbnRgIHBhcmFtZXRlcikuXG5wcC5wYXJzZUZ1bmN0aW9uID0gZnVuY3Rpb24obm9kZSxpc1N0YXRlbWVudCxhbGxvd0V4cHJlc3Npb25Cb2R5KXt0aGlzLmluaXRGdW5jdGlvbihub2RlKTtpZih0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNilub2RlLmdlbmVyYXRvciA9IHRoaXMuZWF0KF90b2tlbnR5cGUudHlwZXMuc3Rhcik7aWYoaXNTdGF0ZW1lbnQgfHwgdGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLm5hbWUpbm9kZS5pZCA9IHRoaXMucGFyc2VJZGVudCgpO3RoaXMucGFyc2VGdW5jdGlvblBhcmFtcyhub2RlKTt0aGlzLnBhcnNlRnVuY3Rpb25Cb2R5KG5vZGUsYWxsb3dFeHByZXNzaW9uQm9keSk7cmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLGlzU3RhdGVtZW50P1wiRnVuY3Rpb25EZWNsYXJhdGlvblwiOlwiRnVuY3Rpb25FeHByZXNzaW9uXCIpO307cHAucGFyc2VGdW5jdGlvblBhcmFtcyA9IGZ1bmN0aW9uKG5vZGUpe3RoaXMuZXhwZWN0KF90b2tlbnR5cGUudHlwZXMucGFyZW5MKTtub2RlLnBhcmFtcyA9IHRoaXMucGFyc2VCaW5kaW5nTGlzdChfdG9rZW50eXBlLnR5cGVzLnBhcmVuUixmYWxzZSxmYWxzZSk7fTsgLy8gUGFyc2UgYSBjbGFzcyBkZWNsYXJhdGlvbiBvciBsaXRlcmFsIChkZXBlbmRpbmcgb24gdGhlXG4vLyBgaXNTdGF0ZW1lbnRgIHBhcmFtZXRlcikuXG5wcC5wYXJzZUNsYXNzID0gZnVuY3Rpb24obm9kZSxpc1N0YXRlbWVudCl7dGhpcy5uZXh0KCk7dGhpcy5wYXJzZUNsYXNzSWQobm9kZSxpc1N0YXRlbWVudCk7dGhpcy5wYXJzZUNsYXNzU3VwZXIobm9kZSk7dmFyIGNsYXNzQm9keT10aGlzLnN0YXJ0Tm9kZSgpO3ZhciBoYWRDb25zdHJ1Y3Rvcj1mYWxzZTtjbGFzc0JvZHkuYm9keSA9IFtdO3RoaXMuZXhwZWN0KF90b2tlbnR5cGUudHlwZXMuYnJhY2VMKTt3aGlsZSghdGhpcy5lYXQoX3Rva2VudHlwZS50eXBlcy5icmFjZVIpKSB7aWYodGhpcy5lYXQoX3Rva2VudHlwZS50eXBlcy5zZW1pKSljb250aW51ZTt2YXIgbWV0aG9kPXRoaXMuc3RhcnROb2RlKCk7dmFyIGlzR2VuZXJhdG9yPXRoaXMuZWF0KF90b2tlbnR5cGUudHlwZXMuc3Rhcik7dmFyIGlzTWF5YmVTdGF0aWM9dGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLm5hbWUgJiYgdGhpcy52YWx1ZSA9PT0gXCJzdGF0aWNcIjt0aGlzLnBhcnNlUHJvcGVydHlOYW1lKG1ldGhvZCk7bWV0aG9kW1wic3RhdGljXCJdID0gaXNNYXliZVN0YXRpYyAmJiB0aGlzLnR5cGUgIT09IF90b2tlbnR5cGUudHlwZXMucGFyZW5MO2lmKG1ldGhvZFtcInN0YXRpY1wiXSl7aWYoaXNHZW5lcmF0b3IpdGhpcy51bmV4cGVjdGVkKCk7aXNHZW5lcmF0b3IgPSB0aGlzLmVhdChfdG9rZW50eXBlLnR5cGVzLnN0YXIpO3RoaXMucGFyc2VQcm9wZXJ0eU5hbWUobWV0aG9kKTt9bWV0aG9kLmtpbmQgPSBcIm1ldGhvZFwiO3ZhciBpc0dldFNldD1mYWxzZTtpZighbWV0aG9kLmNvbXB1dGVkKXt2YXIga2V5PW1ldGhvZC5rZXk7aWYoIWlzR2VuZXJhdG9yICYmIGtleS50eXBlID09PSBcIklkZW50aWZpZXJcIiAmJiB0aGlzLnR5cGUgIT09IF90b2tlbnR5cGUudHlwZXMucGFyZW5MICYmIChrZXkubmFtZSA9PT0gXCJnZXRcIiB8fCBrZXkubmFtZSA9PT0gXCJzZXRcIikpe2lzR2V0U2V0ID0gdHJ1ZTttZXRob2Qua2luZCA9IGtleS5uYW1lO2tleSA9IHRoaXMucGFyc2VQcm9wZXJ0eU5hbWUobWV0aG9kKTt9aWYoIW1ldGhvZFtcInN0YXRpY1wiXSAmJiAoa2V5LnR5cGUgPT09IFwiSWRlbnRpZmllclwiICYmIGtleS5uYW1lID09PSBcImNvbnN0cnVjdG9yXCIgfHwga2V5LnR5cGUgPT09IFwiTGl0ZXJhbFwiICYmIGtleS52YWx1ZSA9PT0gXCJjb25zdHJ1Y3RvclwiKSl7aWYoaGFkQ29uc3RydWN0b3IpdGhpcy5yYWlzZShrZXkuc3RhcnQsXCJEdXBsaWNhdGUgY29uc3RydWN0b3IgaW4gdGhlIHNhbWUgY2xhc3NcIik7aWYoaXNHZXRTZXQpdGhpcy5yYWlzZShrZXkuc3RhcnQsXCJDb25zdHJ1Y3RvciBjYW4ndCBoYXZlIGdldC9zZXQgbW9kaWZpZXJcIik7aWYoaXNHZW5lcmF0b3IpdGhpcy5yYWlzZShrZXkuc3RhcnQsXCJDb25zdHJ1Y3RvciBjYW4ndCBiZSBhIGdlbmVyYXRvclwiKTttZXRob2Qua2luZCA9IFwiY29uc3RydWN0b3JcIjtoYWRDb25zdHJ1Y3RvciA9IHRydWU7fX10aGlzLnBhcnNlQ2xhc3NNZXRob2QoY2xhc3NCb2R5LG1ldGhvZCxpc0dlbmVyYXRvcik7aWYoaXNHZXRTZXQpe3ZhciBwYXJhbUNvdW50PW1ldGhvZC5raW5kID09PSBcImdldFwiPzA6MTtpZihtZXRob2QudmFsdWUucGFyYW1zLmxlbmd0aCAhPT0gcGFyYW1Db3VudCl7dmFyIHN0YXJ0PW1ldGhvZC52YWx1ZS5zdGFydDtpZihtZXRob2Qua2luZCA9PT0gXCJnZXRcIil0aGlzLnJhaXNlKHN0YXJ0LFwiZ2V0dGVyIHNob3VsZCBoYXZlIG5vIHBhcmFtc1wiKTtlbHNlIHRoaXMucmFpc2Uoc3RhcnQsXCJzZXR0ZXIgc2hvdWxkIGhhdmUgZXhhY3RseSBvbmUgcGFyYW1cIik7fX19bm9kZS5ib2R5ID0gdGhpcy5maW5pc2hOb2RlKGNsYXNzQm9keSxcIkNsYXNzQm9keVwiKTtyZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsaXNTdGF0ZW1lbnQ/XCJDbGFzc0RlY2xhcmF0aW9uXCI6XCJDbGFzc0V4cHJlc3Npb25cIik7fTtwcC5wYXJzZUNsYXNzTWV0aG9kID0gZnVuY3Rpb24oY2xhc3NCb2R5LG1ldGhvZCxpc0dlbmVyYXRvcil7bWV0aG9kLnZhbHVlID0gdGhpcy5wYXJzZU1ldGhvZChpc0dlbmVyYXRvcik7Y2xhc3NCb2R5LmJvZHkucHVzaCh0aGlzLmZpbmlzaE5vZGUobWV0aG9kLFwiTWV0aG9kRGVmaW5pdGlvblwiKSk7fTtwcC5wYXJzZUNsYXNzSWQgPSBmdW5jdGlvbihub2RlLGlzU3RhdGVtZW50KXtub2RlLmlkID0gdGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLm5hbWU/dGhpcy5wYXJzZUlkZW50KCk6aXNTdGF0ZW1lbnQ/dGhpcy51bmV4cGVjdGVkKCk6bnVsbDt9O3BwLnBhcnNlQ2xhc3NTdXBlciA9IGZ1bmN0aW9uKG5vZGUpe25vZGUuc3VwZXJDbGFzcyA9IHRoaXMuZWF0KF90b2tlbnR5cGUudHlwZXMuX2V4dGVuZHMpP3RoaXMucGFyc2VFeHByU3Vic2NyaXB0cygpOm51bGw7fTsgLy8gUGFyc2VzIG1vZHVsZSBleHBvcnQgZGVjbGFyYXRpb24uXG5wcC5wYXJzZUV4cG9ydCA9IGZ1bmN0aW9uKG5vZGUpe3RoaXMubmV4dCgpOyAvLyBleHBvcnQgKiBmcm9tICcuLi4nXG5pZih0aGlzLmVhdChfdG9rZW50eXBlLnR5cGVzLnN0YXIpKXt0aGlzLmV4cGVjdENvbnRleHR1YWwoXCJmcm9tXCIpO25vZGUuc291cmNlID0gdGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLnN0cmluZz90aGlzLnBhcnNlRXhwckF0b20oKTp0aGlzLnVuZXhwZWN0ZWQoKTt0aGlzLnNlbWljb2xvbigpO3JldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSxcIkV4cG9ydEFsbERlY2xhcmF0aW9uXCIpO31pZih0aGlzLmVhdChfdG9rZW50eXBlLnR5cGVzLl9kZWZhdWx0KSl7IC8vIGV4cG9ydCBkZWZhdWx0IC4uLlxudmFyIGV4cHI9dGhpcy5wYXJzZU1heWJlQXNzaWduKCk7dmFyIG5lZWRzU2VtaT10cnVlO2lmKGV4cHIudHlwZSA9PSBcIkZ1bmN0aW9uRXhwcmVzc2lvblwiIHx8IGV4cHIudHlwZSA9PSBcIkNsYXNzRXhwcmVzc2lvblwiKXtuZWVkc1NlbWkgPSBmYWxzZTtpZihleHByLmlkKXtleHByLnR5cGUgPSBleHByLnR5cGUgPT0gXCJGdW5jdGlvbkV4cHJlc3Npb25cIj9cIkZ1bmN0aW9uRGVjbGFyYXRpb25cIjpcIkNsYXNzRGVjbGFyYXRpb25cIjt9fW5vZGUuZGVjbGFyYXRpb24gPSBleHByO2lmKG5lZWRzU2VtaSl0aGlzLnNlbWljb2xvbigpO3JldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSxcIkV4cG9ydERlZmF1bHREZWNsYXJhdGlvblwiKTt9IC8vIGV4cG9ydCB2YXJ8Y29uc3R8bGV0fGZ1bmN0aW9ufGNsYXNzIC4uLlxuaWYodGhpcy5zaG91bGRQYXJzZUV4cG9ydFN0YXRlbWVudCgpKXtub2RlLmRlY2xhcmF0aW9uID0gdGhpcy5wYXJzZVN0YXRlbWVudCh0cnVlKTtub2RlLnNwZWNpZmllcnMgPSBbXTtub2RlLnNvdXJjZSA9IG51bGw7fWVsc2UgeyAvLyBleHBvcnQgeyB4LCB5IGFzIHogfSBbZnJvbSAnLi4uJ11cbm5vZGUuZGVjbGFyYXRpb24gPSBudWxsO25vZGUuc3BlY2lmaWVycyA9IHRoaXMucGFyc2VFeHBvcnRTcGVjaWZpZXJzKCk7aWYodGhpcy5lYXRDb250ZXh0dWFsKFwiZnJvbVwiKSl7bm9kZS5zb3VyY2UgPSB0aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuc3RyaW5nP3RoaXMucGFyc2VFeHByQXRvbSgpOnRoaXMudW5leHBlY3RlZCgpO31lbHNlIHtub2RlLnNvdXJjZSA9IG51bGw7fXRoaXMuc2VtaWNvbG9uKCk7fXJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSxcIkV4cG9ydE5hbWVkRGVjbGFyYXRpb25cIik7fTtwcC5zaG91bGRQYXJzZUV4cG9ydFN0YXRlbWVudCA9IGZ1bmN0aW9uKCl7cmV0dXJuIHRoaXMudHlwZS5rZXl3b3JkO307IC8vIFBhcnNlcyBhIGNvbW1hLXNlcGFyYXRlZCBsaXN0IG9mIG1vZHVsZSBleHBvcnRzLlxucHAucGFyc2VFeHBvcnRTcGVjaWZpZXJzID0gZnVuY3Rpb24oKXt2YXIgbm9kZXM9W10sZmlyc3Q9dHJ1ZTsgLy8gZXhwb3J0IHsgeCwgeSBhcyB6IH0gW2Zyb20gJy4uLiddXG50aGlzLmV4cGVjdChfdG9rZW50eXBlLnR5cGVzLmJyYWNlTCk7d2hpbGUoIXRoaXMuZWF0KF90b2tlbnR5cGUudHlwZXMuYnJhY2VSKSkge2lmKCFmaXJzdCl7dGhpcy5leHBlY3QoX3Rva2VudHlwZS50eXBlcy5jb21tYSk7aWYodGhpcy5hZnRlclRyYWlsaW5nQ29tbWEoX3Rva2VudHlwZS50eXBlcy5icmFjZVIpKWJyZWFrO31lbHNlIGZpcnN0ID0gZmFsc2U7dmFyIG5vZGU9dGhpcy5zdGFydE5vZGUoKTtub2RlLmxvY2FsID0gdGhpcy5wYXJzZUlkZW50KHRoaXMudHlwZSA9PT0gX3Rva2VudHlwZS50eXBlcy5fZGVmYXVsdCk7bm9kZS5leHBvcnRlZCA9IHRoaXMuZWF0Q29udGV4dHVhbChcImFzXCIpP3RoaXMucGFyc2VJZGVudCh0cnVlKTpub2RlLmxvY2FsO25vZGVzLnB1c2godGhpcy5maW5pc2hOb2RlKG5vZGUsXCJFeHBvcnRTcGVjaWZpZXJcIikpO31yZXR1cm4gbm9kZXM7fTsgLy8gUGFyc2VzIGltcG9ydCBkZWNsYXJhdGlvbi5cbnBwLnBhcnNlSW1wb3J0ID0gZnVuY3Rpb24obm9kZSl7dGhpcy5uZXh0KCk7IC8vIGltcG9ydCAnLi4uJ1xuaWYodGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLnN0cmluZyl7bm9kZS5zcGVjaWZpZXJzID0gZW1wdHk7bm9kZS5zb3VyY2UgPSB0aGlzLnBhcnNlRXhwckF0b20oKTt9ZWxzZSB7bm9kZS5zcGVjaWZpZXJzID0gdGhpcy5wYXJzZUltcG9ydFNwZWNpZmllcnMoKTt0aGlzLmV4cGVjdENvbnRleHR1YWwoXCJmcm9tXCIpO25vZGUuc291cmNlID0gdGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLnN0cmluZz90aGlzLnBhcnNlRXhwckF0b20oKTp0aGlzLnVuZXhwZWN0ZWQoKTt9dGhpcy5zZW1pY29sb24oKTtyZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsXCJJbXBvcnREZWNsYXJhdGlvblwiKTt9OyAvLyBQYXJzZXMgYSBjb21tYS1zZXBhcmF0ZWQgbGlzdCBvZiBtb2R1bGUgaW1wb3J0cy5cbnBwLnBhcnNlSW1wb3J0U3BlY2lmaWVycyA9IGZ1bmN0aW9uKCl7dmFyIG5vZGVzPVtdLGZpcnN0PXRydWU7aWYodGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLm5hbWUpeyAvLyBpbXBvcnQgZGVmYXVsdE9iaiwgeyB4LCB5IGFzIHogfSBmcm9tICcuLi4nXG52YXIgbm9kZT10aGlzLnN0YXJ0Tm9kZSgpO25vZGUubG9jYWwgPSB0aGlzLnBhcnNlSWRlbnQoKTt0aGlzLmNoZWNrTFZhbChub2RlLmxvY2FsLHRydWUpO25vZGVzLnB1c2godGhpcy5maW5pc2hOb2RlKG5vZGUsXCJJbXBvcnREZWZhdWx0U3BlY2lmaWVyXCIpKTtpZighdGhpcy5lYXQoX3Rva2VudHlwZS50eXBlcy5jb21tYSkpcmV0dXJuIG5vZGVzO31pZih0aGlzLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuc3Rhcil7dmFyIG5vZGU9dGhpcy5zdGFydE5vZGUoKTt0aGlzLm5leHQoKTt0aGlzLmV4cGVjdENvbnRleHR1YWwoXCJhc1wiKTtub2RlLmxvY2FsID0gdGhpcy5wYXJzZUlkZW50KCk7dGhpcy5jaGVja0xWYWwobm9kZS5sb2NhbCx0cnVlKTtub2Rlcy5wdXNoKHRoaXMuZmluaXNoTm9kZShub2RlLFwiSW1wb3J0TmFtZXNwYWNlU3BlY2lmaWVyXCIpKTtyZXR1cm4gbm9kZXM7fXRoaXMuZXhwZWN0KF90b2tlbnR5cGUudHlwZXMuYnJhY2VMKTt3aGlsZSghdGhpcy5lYXQoX3Rva2VudHlwZS50eXBlcy5icmFjZVIpKSB7aWYoIWZpcnN0KXt0aGlzLmV4cGVjdChfdG9rZW50eXBlLnR5cGVzLmNvbW1hKTtpZih0aGlzLmFmdGVyVHJhaWxpbmdDb21tYShfdG9rZW50eXBlLnR5cGVzLmJyYWNlUikpYnJlYWs7fWVsc2UgZmlyc3QgPSBmYWxzZTt2YXIgbm9kZT10aGlzLnN0YXJ0Tm9kZSgpO25vZGUuaW1wb3J0ZWQgPSB0aGlzLnBhcnNlSWRlbnQodHJ1ZSk7bm9kZS5sb2NhbCA9IHRoaXMuZWF0Q29udGV4dHVhbChcImFzXCIpP3RoaXMucGFyc2VJZGVudCgpOm5vZGUuaW1wb3J0ZWQ7dGhpcy5jaGVja0xWYWwobm9kZS5sb2NhbCx0cnVlKTtub2Rlcy5wdXNoKHRoaXMuZmluaXNoTm9kZShub2RlLFwiSW1wb3J0U3BlY2lmaWVyXCIpKTt9cmV0dXJuIG5vZGVzO307fSx7XCIuL3N0YXRlXCI6MTAsXCIuL3Rva2VudHlwZVwiOjE0LFwiLi93aGl0ZXNwYWNlXCI6MTZ9XSwxMjpbZnVuY3Rpb24oX2RlcmVxXyxtb2R1bGUsZXhwb3J0cyl7IC8vIFRoZSBhbGdvcml0aG0gdXNlZCB0byBkZXRlcm1pbmUgd2hldGhlciBhIHJlZ2V4cCBjYW4gYXBwZWFyIGF0IGFcbi8vIGdpdmVuIHBvaW50IGluIHRoZSBwcm9ncmFtIGlzIGxvb3NlbHkgYmFzZWQgb24gc3dlZXQuanMnIGFwcHJvYWNoLlxuLy8gU2VlIGh0dHBzOi8vZ2l0aHViLmNvbS9tb3ppbGxhL3N3ZWV0LmpzL3dpa2kvZGVzaWduXG5cInVzZSBzdHJpY3RcIjtleHBvcnRzLl9fZXNNb2R1bGUgPSB0cnVlO2Z1bmN0aW9uIF9jbGFzc0NhbGxDaGVjayhpbnN0YW5jZSxDb25zdHJ1Y3Rvcil7aWYoIShpbnN0YW5jZSBpbnN0YW5jZW9mIENvbnN0cnVjdG9yKSl7dGhyb3cgbmV3IFR5cGVFcnJvcihcIkNhbm5vdCBjYWxsIGEgY2xhc3MgYXMgYSBmdW5jdGlvblwiKTt9fXZhciBfc3RhdGU9X2RlcmVxXyhcIi4vc3RhdGVcIik7dmFyIF90b2tlbnR5cGU9X2RlcmVxXyhcIi4vdG9rZW50eXBlXCIpO3ZhciBfd2hpdGVzcGFjZT1fZGVyZXFfKFwiLi93aGl0ZXNwYWNlXCIpO3ZhciBUb2tDb250ZXh0PWZ1bmN0aW9uIFRva0NvbnRleHQodG9rZW4saXNFeHByLHByZXNlcnZlU3BhY2Usb3ZlcnJpZGUpe19jbGFzc0NhbGxDaGVjayh0aGlzLFRva0NvbnRleHQpO3RoaXMudG9rZW4gPSB0b2tlbjt0aGlzLmlzRXhwciA9ICEhaXNFeHByO3RoaXMucHJlc2VydmVTcGFjZSA9ICEhcHJlc2VydmVTcGFjZTt0aGlzLm92ZXJyaWRlID0gb3ZlcnJpZGU7fTtleHBvcnRzLlRva0NvbnRleHQgPSBUb2tDb250ZXh0O3ZhciB0eXBlcz17Yl9zdGF0Om5ldyBUb2tDb250ZXh0KFwie1wiLGZhbHNlKSxiX2V4cHI6bmV3IFRva0NvbnRleHQoXCJ7XCIsdHJ1ZSksYl90bXBsOm5ldyBUb2tDb250ZXh0KFwiJHtcIix0cnVlKSxwX3N0YXQ6bmV3IFRva0NvbnRleHQoXCIoXCIsZmFsc2UpLHBfZXhwcjpuZXcgVG9rQ29udGV4dChcIihcIix0cnVlKSxxX3RtcGw6bmV3IFRva0NvbnRleHQoXCJgXCIsdHJ1ZSx0cnVlLGZ1bmN0aW9uKHApe3JldHVybiBwLnJlYWRUbXBsVG9rZW4oKTt9KSxmX2V4cHI6bmV3IFRva0NvbnRleHQoXCJmdW5jdGlvblwiLHRydWUpfTtleHBvcnRzLnR5cGVzID0gdHlwZXM7dmFyIHBwPV9zdGF0ZS5QYXJzZXIucHJvdG90eXBlO3BwLmluaXRpYWxDb250ZXh0ID0gZnVuY3Rpb24oKXtyZXR1cm4gW3R5cGVzLmJfc3RhdF07fTtwcC5icmFjZUlzQmxvY2sgPSBmdW5jdGlvbihwcmV2VHlwZSl7aWYocHJldlR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuY29sb24pe3ZhciBfcGFyZW50PXRoaXMuY3VyQ29udGV4dCgpO2lmKF9wYXJlbnQgPT09IHR5cGVzLmJfc3RhdCB8fCBfcGFyZW50ID09PSB0eXBlcy5iX2V4cHIpcmV0dXJuICFfcGFyZW50LmlzRXhwcjt9aWYocHJldlR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuX3JldHVybilyZXR1cm4gX3doaXRlc3BhY2UubGluZUJyZWFrLnRlc3QodGhpcy5pbnB1dC5zbGljZSh0aGlzLmxhc3RUb2tFbmQsdGhpcy5zdGFydCkpO2lmKHByZXZUeXBlID09PSBfdG9rZW50eXBlLnR5cGVzLl9lbHNlIHx8IHByZXZUeXBlID09PSBfdG9rZW50eXBlLnR5cGVzLnNlbWkgfHwgcHJldlR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuZW9mIHx8IHByZXZUeXBlID09PSBfdG9rZW50eXBlLnR5cGVzLnBhcmVuUilyZXR1cm4gdHJ1ZTtpZihwcmV2VHlwZSA9PSBfdG9rZW50eXBlLnR5cGVzLmJyYWNlTClyZXR1cm4gdGhpcy5jdXJDb250ZXh0KCkgPT09IHR5cGVzLmJfc3RhdDtyZXR1cm4gIXRoaXMuZXhwckFsbG93ZWQ7fTtwcC51cGRhdGVDb250ZXh0ID0gZnVuY3Rpb24ocHJldlR5cGUpe3ZhciB1cGRhdGU9dW5kZWZpbmVkLHR5cGU9dGhpcy50eXBlO2lmKHR5cGUua2V5d29yZCAmJiBwcmV2VHlwZSA9PSBfdG9rZW50eXBlLnR5cGVzLmRvdCl0aGlzLmV4cHJBbGxvd2VkID0gZmFsc2U7ZWxzZSBpZih1cGRhdGUgPSB0eXBlLnVwZGF0ZUNvbnRleHQpdXBkYXRlLmNhbGwodGhpcyxwcmV2VHlwZSk7ZWxzZSB0aGlzLmV4cHJBbGxvd2VkID0gdHlwZS5iZWZvcmVFeHByO307IC8vIFRva2VuLXNwZWNpZmljIGNvbnRleHQgdXBkYXRlIGNvZGVcbl90b2tlbnR5cGUudHlwZXMucGFyZW5SLnVwZGF0ZUNvbnRleHQgPSBfdG9rZW50eXBlLnR5cGVzLmJyYWNlUi51cGRhdGVDb250ZXh0ID0gZnVuY3Rpb24oKXtpZih0aGlzLmNvbnRleHQubGVuZ3RoID09IDEpe3RoaXMuZXhwckFsbG93ZWQgPSB0cnVlO3JldHVybjt9dmFyIG91dD10aGlzLmNvbnRleHQucG9wKCk7aWYob3V0ID09PSB0eXBlcy5iX3N0YXQgJiYgdGhpcy5jdXJDb250ZXh0KCkgPT09IHR5cGVzLmZfZXhwcil7dGhpcy5jb250ZXh0LnBvcCgpO3RoaXMuZXhwckFsbG93ZWQgPSBmYWxzZTt9ZWxzZSBpZihvdXQgPT09IHR5cGVzLmJfdG1wbCl7dGhpcy5leHByQWxsb3dlZCA9IHRydWU7fWVsc2Uge3RoaXMuZXhwckFsbG93ZWQgPSAhb3V0LmlzRXhwcjt9fTtfdG9rZW50eXBlLnR5cGVzLmJyYWNlTC51cGRhdGVDb250ZXh0ID0gZnVuY3Rpb24ocHJldlR5cGUpe3RoaXMuY29udGV4dC5wdXNoKHRoaXMuYnJhY2VJc0Jsb2NrKHByZXZUeXBlKT90eXBlcy5iX3N0YXQ6dHlwZXMuYl9leHByKTt0aGlzLmV4cHJBbGxvd2VkID0gdHJ1ZTt9O190b2tlbnR5cGUudHlwZXMuZG9sbGFyQnJhY2VMLnVwZGF0ZUNvbnRleHQgPSBmdW5jdGlvbigpe3RoaXMuY29udGV4dC5wdXNoKHR5cGVzLmJfdG1wbCk7dGhpcy5leHByQWxsb3dlZCA9IHRydWU7fTtfdG9rZW50eXBlLnR5cGVzLnBhcmVuTC51cGRhdGVDb250ZXh0ID0gZnVuY3Rpb24ocHJldlR5cGUpe3ZhciBzdGF0ZW1lbnRQYXJlbnM9cHJldlR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuX2lmIHx8IHByZXZUeXBlID09PSBfdG9rZW50eXBlLnR5cGVzLl9mb3IgfHwgcHJldlR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuX3dpdGggfHwgcHJldlR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuX3doaWxlO3RoaXMuY29udGV4dC5wdXNoKHN0YXRlbWVudFBhcmVucz90eXBlcy5wX3N0YXQ6dHlwZXMucF9leHByKTt0aGlzLmV4cHJBbGxvd2VkID0gdHJ1ZTt9O190b2tlbnR5cGUudHlwZXMuaW5jRGVjLnVwZGF0ZUNvbnRleHQgPSBmdW5jdGlvbigpeyAvLyB0b2tFeHByQWxsb3dlZCBzdGF5cyB1bmNoYW5nZWRcbn07X3Rva2VudHlwZS50eXBlcy5fZnVuY3Rpb24udXBkYXRlQ29udGV4dCA9IGZ1bmN0aW9uKCl7aWYodGhpcy5jdXJDb250ZXh0KCkgIT09IHR5cGVzLmJfc3RhdCl0aGlzLmNvbnRleHQucHVzaCh0eXBlcy5mX2V4cHIpO3RoaXMuZXhwckFsbG93ZWQgPSBmYWxzZTt9O190b2tlbnR5cGUudHlwZXMuYmFja1F1b3RlLnVwZGF0ZUNvbnRleHQgPSBmdW5jdGlvbigpe2lmKHRoaXMuY3VyQ29udGV4dCgpID09PSB0eXBlcy5xX3RtcGwpdGhpcy5jb250ZXh0LnBvcCgpO2Vsc2UgdGhpcy5jb250ZXh0LnB1c2godHlwZXMucV90bXBsKTt0aGlzLmV4cHJBbGxvd2VkID0gZmFsc2U7fTt9LHtcIi4vc3RhdGVcIjoxMCxcIi4vdG9rZW50eXBlXCI6MTQsXCIuL3doaXRlc3BhY2VcIjoxNn1dLDEzOltmdW5jdGlvbihfZGVyZXFfLG1vZHVsZSxleHBvcnRzKXtcInVzZSBzdHJpY3RcIjtleHBvcnRzLl9fZXNNb2R1bGUgPSB0cnVlO2Z1bmN0aW9uIF9jbGFzc0NhbGxDaGVjayhpbnN0YW5jZSxDb25zdHJ1Y3Rvcil7aWYoIShpbnN0YW5jZSBpbnN0YW5jZW9mIENvbnN0cnVjdG9yKSl7dGhyb3cgbmV3IFR5cGVFcnJvcihcIkNhbm5vdCBjYWxsIGEgY2xhc3MgYXMgYSBmdW5jdGlvblwiKTt9fXZhciBfaWRlbnRpZmllcj1fZGVyZXFfKFwiLi9pZGVudGlmaWVyXCIpO3ZhciBfdG9rZW50eXBlPV9kZXJlcV8oXCIuL3Rva2VudHlwZVwiKTt2YXIgX3N0YXRlPV9kZXJlcV8oXCIuL3N0YXRlXCIpO3ZhciBfbG9jdXRpbD1fZGVyZXFfKFwiLi9sb2N1dGlsXCIpO3ZhciBfd2hpdGVzcGFjZT1fZGVyZXFfKFwiLi93aGl0ZXNwYWNlXCIpOyAvLyBPYmplY3QgdHlwZSB1c2VkIHRvIHJlcHJlc2VudCB0b2tlbnMuIE5vdGUgdGhhdCBub3JtYWxseSwgdG9rZW5zXG4vLyBzaW1wbHkgZXhpc3QgYXMgcHJvcGVydGllcyBvbiB0aGUgcGFyc2VyIG9iamVjdC4gVGhpcyBpcyBvbmx5XG4vLyB1c2VkIGZvciB0aGUgb25Ub2tlbiBjYWxsYmFjayBhbmQgdGhlIGV4dGVybmFsIHRva2VuaXplci5cbnZhciBUb2tlbj1mdW5jdGlvbiBUb2tlbihwKXtfY2xhc3NDYWxsQ2hlY2sodGhpcyxUb2tlbik7dGhpcy50eXBlID0gcC50eXBlO3RoaXMudmFsdWUgPSBwLnZhbHVlO3RoaXMuc3RhcnQgPSBwLnN0YXJ0O3RoaXMuZW5kID0gcC5lbmQ7aWYocC5vcHRpb25zLmxvY2F0aW9ucyl0aGlzLmxvYyA9IG5ldyBfbG9jdXRpbC5Tb3VyY2VMb2NhdGlvbihwLHAuc3RhcnRMb2MscC5lbmRMb2MpO2lmKHAub3B0aW9ucy5yYW5nZXMpdGhpcy5yYW5nZSA9IFtwLnN0YXJ0LHAuZW5kXTt9IC8vICMjIFRva2VuaXplclxuO2V4cG9ydHMuVG9rZW4gPSBUb2tlbjt2YXIgcHA9X3N0YXRlLlBhcnNlci5wcm90b3R5cGU7IC8vIEFyZSB3ZSBydW5uaW5nIHVuZGVyIFJoaW5vP1xudmFyIGlzUmhpbm89dHlwZW9mIFBhY2thZ2VzID09IFwib2JqZWN0XCIgJiYgT2JqZWN0LnByb3RvdHlwZS50b1N0cmluZy5jYWxsKFBhY2thZ2VzKSA9PSBcIltvYmplY3QgSmF2YVBhY2thZ2VdXCI7IC8vIE1vdmUgdG8gdGhlIG5leHQgdG9rZW5cbnBwLm5leHQgPSBmdW5jdGlvbigpe2lmKHRoaXMub3B0aW9ucy5vblRva2VuKXRoaXMub3B0aW9ucy5vblRva2VuKG5ldyBUb2tlbih0aGlzKSk7dGhpcy5sYXN0VG9rRW5kID0gdGhpcy5lbmQ7dGhpcy5sYXN0VG9rU3RhcnQgPSB0aGlzLnN0YXJ0O3RoaXMubGFzdFRva0VuZExvYyA9IHRoaXMuZW5kTG9jO3RoaXMubGFzdFRva1N0YXJ0TG9jID0gdGhpcy5zdGFydExvYzt0aGlzLm5leHRUb2tlbigpO307cHAuZ2V0VG9rZW4gPSBmdW5jdGlvbigpe3RoaXMubmV4dCgpO3JldHVybiBuZXcgVG9rZW4odGhpcyk7fTsgLy8gSWYgd2UncmUgaW4gYW4gRVM2IGVudmlyb25tZW50LCBtYWtlIHBhcnNlcnMgaXRlcmFibGVcbmlmKHR5cGVvZiBTeW1ib2wgIT09IFwidW5kZWZpbmVkXCIpcHBbU3ltYm9sLml0ZXJhdG9yXSA9IGZ1bmN0aW9uKCl7dmFyIHNlbGY9dGhpcztyZXR1cm4ge25leHQ6ZnVuY3Rpb24gbmV4dCgpe3ZhciB0b2tlbj1zZWxmLmdldFRva2VuKCk7cmV0dXJuIHtkb25lOnRva2VuLnR5cGUgPT09IF90b2tlbnR5cGUudHlwZXMuZW9mLHZhbHVlOnRva2VufTt9fTt9OyAvLyBUb2dnbGUgc3RyaWN0IG1vZGUuIFJlLXJlYWRzIHRoZSBuZXh0IG51bWJlciBvciBzdHJpbmcgdG8gcGxlYXNlXG4vLyBwZWRhbnRpYyB0ZXN0cyAoYFwidXNlIHN0cmljdFwiOyAwMTA7YCBzaG91bGQgZmFpbCkuXG5wcC5zZXRTdHJpY3QgPSBmdW5jdGlvbihzdHJpY3Qpe3RoaXMuc3RyaWN0ID0gc3RyaWN0O2lmKHRoaXMudHlwZSAhPT0gX3Rva2VudHlwZS50eXBlcy5udW0gJiYgdGhpcy50eXBlICE9PSBfdG9rZW50eXBlLnR5cGVzLnN0cmluZylyZXR1cm47dGhpcy5wb3MgPSB0aGlzLnN0YXJ0O2lmKHRoaXMub3B0aW9ucy5sb2NhdGlvbnMpe3doaWxlKHRoaXMucG9zIDwgdGhpcy5saW5lU3RhcnQpIHt0aGlzLmxpbmVTdGFydCA9IHRoaXMuaW5wdXQubGFzdEluZGV4T2YoXCJcXG5cIix0aGlzLmxpbmVTdGFydCAtIDIpICsgMTstLXRoaXMuY3VyTGluZTt9fXRoaXMubmV4dFRva2VuKCk7fTtwcC5jdXJDb250ZXh0ID0gZnVuY3Rpb24oKXtyZXR1cm4gdGhpcy5jb250ZXh0W3RoaXMuY29udGV4dC5sZW5ndGggLSAxXTt9OyAvLyBSZWFkIGEgc2luZ2xlIHRva2VuLCB1cGRhdGluZyB0aGUgcGFyc2VyIG9iamVjdCdzIHRva2VuLXJlbGF0ZWRcbi8vIHByb3BlcnRpZXMuXG5wcC5uZXh0VG9rZW4gPSBmdW5jdGlvbigpe3ZhciBjdXJDb250ZXh0PXRoaXMuY3VyQ29udGV4dCgpO2lmKCFjdXJDb250ZXh0IHx8ICFjdXJDb250ZXh0LnByZXNlcnZlU3BhY2UpdGhpcy5za2lwU3BhY2UoKTt0aGlzLnN0YXJ0ID0gdGhpcy5wb3M7aWYodGhpcy5vcHRpb25zLmxvY2F0aW9ucyl0aGlzLnN0YXJ0TG9jID0gdGhpcy5jdXJQb3NpdGlvbigpO2lmKHRoaXMucG9zID49IHRoaXMuaW5wdXQubGVuZ3RoKXJldHVybiB0aGlzLmZpbmlzaFRva2VuKF90b2tlbnR5cGUudHlwZXMuZW9mKTtpZihjdXJDb250ZXh0Lm92ZXJyaWRlKXJldHVybiBjdXJDb250ZXh0Lm92ZXJyaWRlKHRoaXMpO2Vsc2UgdGhpcy5yZWFkVG9rZW4odGhpcy5mdWxsQ2hhckNvZGVBdFBvcygpKTt9O3BwLnJlYWRUb2tlbiA9IGZ1bmN0aW9uKGNvZGUpeyAvLyBJZGVudGlmaWVyIG9yIGtleXdvcmQuICdcXHVYWFhYJyBzZXF1ZW5jZXMgYXJlIGFsbG93ZWQgaW5cbi8vIGlkZW50aWZpZXJzLCBzbyAnXFwnIGFsc28gZGlzcGF0Y2hlcyB0byB0aGF0LlxuaWYoX2lkZW50aWZpZXIuaXNJZGVudGlmaWVyU3RhcnQoY29kZSx0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNikgfHwgY29kZSA9PT0gOTIgLyogJ1xcJyAqLylyZXR1cm4gdGhpcy5yZWFkV29yZCgpO3JldHVybiB0aGlzLmdldFRva2VuRnJvbUNvZGUoY29kZSk7fTtwcC5mdWxsQ2hhckNvZGVBdFBvcyA9IGZ1bmN0aW9uKCl7dmFyIGNvZGU9dGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zKTtpZihjb2RlIDw9IDB4ZDdmZiB8fCBjb2RlID49IDB4ZTAwMClyZXR1cm4gY29kZTt2YXIgbmV4dD10aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAxKTtyZXR1cm4gKGNvZGUgPDwgMTApICsgbmV4dCAtIDB4MzVmZGMwMDt9O3BwLnNraXBCbG9ja0NvbW1lbnQgPSBmdW5jdGlvbigpe3ZhciBzdGFydExvYz10aGlzLm9wdGlvbnMub25Db21tZW50ICYmIHRoaXMuY3VyUG9zaXRpb24oKTt2YXIgc3RhcnQ9dGhpcy5wb3MsZW5kPXRoaXMuaW5wdXQuaW5kZXhPZihcIiovXCIsdGhpcy5wb3MgKz0gMik7aWYoZW5kID09PSAtMSl0aGlzLnJhaXNlKHRoaXMucG9zIC0gMixcIlVudGVybWluYXRlZCBjb21tZW50XCIpO3RoaXMucG9zID0gZW5kICsgMjtpZih0aGlzLm9wdGlvbnMubG9jYXRpb25zKXtfd2hpdGVzcGFjZS5saW5lQnJlYWtHLmxhc3RJbmRleCA9IHN0YXJ0O3ZhciBtYXRjaD11bmRlZmluZWQ7d2hpbGUoKG1hdGNoID0gX3doaXRlc3BhY2UubGluZUJyZWFrRy5leGVjKHRoaXMuaW5wdXQpKSAmJiBtYXRjaC5pbmRleCA8IHRoaXMucG9zKSB7Kyt0aGlzLmN1ckxpbmU7dGhpcy5saW5lU3RhcnQgPSBtYXRjaC5pbmRleCArIG1hdGNoWzBdLmxlbmd0aDt9fWlmKHRoaXMub3B0aW9ucy5vbkNvbW1lbnQpdGhpcy5vcHRpb25zLm9uQ29tbWVudCh0cnVlLHRoaXMuaW5wdXQuc2xpY2Uoc3RhcnQgKyAyLGVuZCksc3RhcnQsdGhpcy5wb3Msc3RhcnRMb2MsdGhpcy5jdXJQb3NpdGlvbigpKTt9O3BwLnNraXBMaW5lQ29tbWVudCA9IGZ1bmN0aW9uKHN0YXJ0U2tpcCl7dmFyIHN0YXJ0PXRoaXMucG9zO3ZhciBzdGFydExvYz10aGlzLm9wdGlvbnMub25Db21tZW50ICYmIHRoaXMuY3VyUG9zaXRpb24oKTt2YXIgY2g9dGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICs9IHN0YXJ0U2tpcCk7d2hpbGUodGhpcy5wb3MgPCB0aGlzLmlucHV0Lmxlbmd0aCAmJiBjaCAhPT0gMTAgJiYgY2ggIT09IDEzICYmIGNoICE9PSA4MjMyICYmIGNoICE9PSA4MjMzKSB7Kyt0aGlzLnBvcztjaCA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyk7fWlmKHRoaXMub3B0aW9ucy5vbkNvbW1lbnQpdGhpcy5vcHRpb25zLm9uQ29tbWVudChmYWxzZSx0aGlzLmlucHV0LnNsaWNlKHN0YXJ0ICsgc3RhcnRTa2lwLHRoaXMucG9zKSxzdGFydCx0aGlzLnBvcyxzdGFydExvYyx0aGlzLmN1clBvc2l0aW9uKCkpO307IC8vIENhbGxlZCBhdCB0aGUgc3RhcnQgb2YgdGhlIHBhcnNlIGFuZCBhZnRlciBldmVyeSB0b2tlbi4gU2tpcHNcbi8vIHdoaXRlc3BhY2UgYW5kIGNvbW1lbnRzLCBhbmQuXG5wcC5za2lwU3BhY2UgPSBmdW5jdGlvbigpe2xvb3A6IHdoaWxlKHRoaXMucG9zIDwgdGhpcy5pbnB1dC5sZW5ndGgpIHt2YXIgY2g9dGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zKTtzd2l0Y2goY2gpe2Nhc2UgMzI6Y2FzZSAxNjA6IC8vICcgJ1xuKyt0aGlzLnBvczticmVhaztjYXNlIDEzOmlmKHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIDEpID09PSAxMCl7Kyt0aGlzLnBvczt9Y2FzZSAxMDpjYXNlIDgyMzI6Y2FzZSA4MjMzOisrdGhpcy5wb3M7aWYodGhpcy5vcHRpb25zLmxvY2F0aW9ucyl7Kyt0aGlzLmN1ckxpbmU7dGhpcy5saW5lU3RhcnQgPSB0aGlzLnBvczt9YnJlYWs7Y2FzZSA0NzogLy8gJy8nXG5zd2l0Y2godGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMSkpe2Nhc2UgNDI6IC8vICcqJ1xudGhpcy5za2lwQmxvY2tDb21tZW50KCk7YnJlYWs7Y2FzZSA0Nzp0aGlzLnNraXBMaW5lQ29tbWVudCgyKTticmVhaztkZWZhdWx0OmJyZWFrIGxvb3A7fWJyZWFrO2RlZmF1bHQ6aWYoY2ggPiA4ICYmIGNoIDwgMTQgfHwgY2ggPj0gNTc2MCAmJiBfd2hpdGVzcGFjZS5ub25BU0NJSXdoaXRlc3BhY2UudGVzdChTdHJpbmcuZnJvbUNoYXJDb2RlKGNoKSkpeysrdGhpcy5wb3M7fWVsc2Uge2JyZWFrIGxvb3A7fX19fTsgLy8gQ2FsbGVkIGF0IHRoZSBlbmQgb2YgZXZlcnkgdG9rZW4uIFNldHMgYGVuZGAsIGB2YWxgLCBhbmRcbi8vIG1haW50YWlucyBgY29udGV4dGAgYW5kIGBleHByQWxsb3dlZGAsIGFuZCBza2lwcyB0aGUgc3BhY2UgYWZ0ZXJcbi8vIHRoZSB0b2tlbiwgc28gdGhhdCB0aGUgbmV4dCBvbmUncyBgc3RhcnRgIHdpbGwgcG9pbnQgYXQgdGhlXG4vLyByaWdodCBwb3NpdGlvbi5cbnBwLmZpbmlzaFRva2VuID0gZnVuY3Rpb24odHlwZSx2YWwpe3RoaXMuZW5kID0gdGhpcy5wb3M7aWYodGhpcy5vcHRpb25zLmxvY2F0aW9ucyl0aGlzLmVuZExvYyA9IHRoaXMuY3VyUG9zaXRpb24oKTt2YXIgcHJldlR5cGU9dGhpcy50eXBlO3RoaXMudHlwZSA9IHR5cGU7dGhpcy52YWx1ZSA9IHZhbDt0aGlzLnVwZGF0ZUNvbnRleHQocHJldlR5cGUpO307IC8vICMjIyBUb2tlbiByZWFkaW5nXG4vLyBUaGlzIGlzIHRoZSBmdW5jdGlvbiB0aGF0IGlzIGNhbGxlZCB0byBmZXRjaCB0aGUgbmV4dCB0b2tlbi4gSXRcbi8vIGlzIHNvbWV3aGF0IG9ic2N1cmUsIGJlY2F1c2UgaXQgd29ya3MgaW4gY2hhcmFjdGVyIGNvZGVzIHJhdGhlclxuLy8gdGhhbiBjaGFyYWN0ZXJzLCBhbmQgYmVjYXVzZSBvcGVyYXRvciBwYXJzaW5nIGhhcyBiZWVuIGlubGluZWRcbi8vIGludG8gaXQuXG4vL1xuLy8gQWxsIGluIHRoZSBuYW1lIG9mIHNwZWVkLlxuLy9cbnBwLnJlYWRUb2tlbl9kb3QgPSBmdW5jdGlvbigpe3ZhciBuZXh0PXRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIDEpO2lmKG5leHQgPj0gNDggJiYgbmV4dCA8PSA1NylyZXR1cm4gdGhpcy5yZWFkTnVtYmVyKHRydWUpO3ZhciBuZXh0Mj10aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAyKTtpZih0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNiAmJiBuZXh0ID09PSA0NiAmJiBuZXh0MiA9PT0gNDYpeyAvLyA0NiA9IGRvdCAnLidcbnRoaXMucG9zICs9IDM7cmV0dXJuIHRoaXMuZmluaXNoVG9rZW4oX3Rva2VudHlwZS50eXBlcy5lbGxpcHNpcyk7fWVsc2UgeysrdGhpcy5wb3M7cmV0dXJuIHRoaXMuZmluaXNoVG9rZW4oX3Rva2VudHlwZS50eXBlcy5kb3QpO319O3BwLnJlYWRUb2tlbl9zbGFzaCA9IGZ1bmN0aW9uKCl7IC8vICcvJ1xudmFyIG5leHQ9dGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMSk7aWYodGhpcy5leHByQWxsb3dlZCl7Kyt0aGlzLnBvcztyZXR1cm4gdGhpcy5yZWFkUmVnZXhwKCk7fWlmKG5leHQgPT09IDYxKXJldHVybiB0aGlzLmZpbmlzaE9wKF90b2tlbnR5cGUudHlwZXMuYXNzaWduLDIpO3JldHVybiB0aGlzLmZpbmlzaE9wKF90b2tlbnR5cGUudHlwZXMuc2xhc2gsMSk7fTtwcC5yZWFkVG9rZW5fbXVsdF9tb2R1bG8gPSBmdW5jdGlvbihjb2RlKXsgLy8gJyUqJ1xudmFyIG5leHQ9dGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMSk7aWYobmV4dCA9PT0gNjEpcmV0dXJuIHRoaXMuZmluaXNoT3AoX3Rva2VudHlwZS50eXBlcy5hc3NpZ24sMik7cmV0dXJuIHRoaXMuZmluaXNoT3AoY29kZSA9PT0gNDI/X3Rva2VudHlwZS50eXBlcy5zdGFyOl90b2tlbnR5cGUudHlwZXMubW9kdWxvLDEpO307cHAucmVhZFRva2VuX3BpcGVfYW1wID0gZnVuY3Rpb24oY29kZSl7IC8vICd8JidcbnZhciBuZXh0PXRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIDEpO2lmKG5leHQgPT09IGNvZGUpcmV0dXJuIHRoaXMuZmluaXNoT3AoY29kZSA9PT0gMTI0P190b2tlbnR5cGUudHlwZXMubG9naWNhbE9SOl90b2tlbnR5cGUudHlwZXMubG9naWNhbEFORCwyKTtpZihuZXh0ID09PSA2MSlyZXR1cm4gdGhpcy5maW5pc2hPcChfdG9rZW50eXBlLnR5cGVzLmFzc2lnbiwyKTtyZXR1cm4gdGhpcy5maW5pc2hPcChjb2RlID09PSAxMjQ/X3Rva2VudHlwZS50eXBlcy5iaXR3aXNlT1I6X3Rva2VudHlwZS50eXBlcy5iaXR3aXNlQU5ELDEpO307cHAucmVhZFRva2VuX2NhcmV0ID0gZnVuY3Rpb24oKXsgLy8gJ14nXG52YXIgbmV4dD10aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAxKTtpZihuZXh0ID09PSA2MSlyZXR1cm4gdGhpcy5maW5pc2hPcChfdG9rZW50eXBlLnR5cGVzLmFzc2lnbiwyKTtyZXR1cm4gdGhpcy5maW5pc2hPcChfdG9rZW50eXBlLnR5cGVzLmJpdHdpc2VYT1IsMSk7fTtwcC5yZWFkVG9rZW5fcGx1c19taW4gPSBmdW5jdGlvbihjb2RlKXsgLy8gJystJ1xudmFyIG5leHQ9dGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMSk7aWYobmV4dCA9PT0gY29kZSl7aWYobmV4dCA9PSA0NSAmJiB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAyKSA9PSA2MiAmJiBfd2hpdGVzcGFjZS5saW5lQnJlYWsudGVzdCh0aGlzLmlucHV0LnNsaWNlKHRoaXMubGFzdFRva0VuZCx0aGlzLnBvcykpKXsgLy8gQSBgLS0+YCBsaW5lIGNvbW1lbnRcbnRoaXMuc2tpcExpbmVDb21tZW50KDMpO3RoaXMuc2tpcFNwYWNlKCk7cmV0dXJuIHRoaXMubmV4dFRva2VuKCk7fXJldHVybiB0aGlzLmZpbmlzaE9wKF90b2tlbnR5cGUudHlwZXMuaW5jRGVjLDIpO31pZihuZXh0ID09PSA2MSlyZXR1cm4gdGhpcy5maW5pc2hPcChfdG9rZW50eXBlLnR5cGVzLmFzc2lnbiwyKTtyZXR1cm4gdGhpcy5maW5pc2hPcChfdG9rZW50eXBlLnR5cGVzLnBsdXNNaW4sMSk7fTtwcC5yZWFkVG9rZW5fbHRfZ3QgPSBmdW5jdGlvbihjb2RlKXsgLy8gJzw+J1xudmFyIG5leHQ9dGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMSk7dmFyIHNpemU9MTtpZihuZXh0ID09PSBjb2RlKXtzaXplID0gY29kZSA9PT0gNjIgJiYgdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMikgPT09IDYyPzM6MjtpZih0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyBzaXplKSA9PT0gNjEpcmV0dXJuIHRoaXMuZmluaXNoT3AoX3Rva2VudHlwZS50eXBlcy5hc3NpZ24sc2l6ZSArIDEpO3JldHVybiB0aGlzLmZpbmlzaE9wKF90b2tlbnR5cGUudHlwZXMuYml0U2hpZnQsc2l6ZSk7fWlmKG5leHQgPT0gMzMgJiYgY29kZSA9PSA2MCAmJiB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAyKSA9PSA0NSAmJiB0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAzKSA9PSA0NSl7aWYodGhpcy5pbk1vZHVsZSl0aGlzLnVuZXhwZWN0ZWQoKTsgLy8gYDwhLS1gLCBhbiBYTUwtc3R5bGUgY29tbWVudCB0aGF0IHNob3VsZCBiZSBpbnRlcnByZXRlZCBhcyBhIGxpbmUgY29tbWVudFxudGhpcy5za2lwTGluZUNvbW1lbnQoNCk7dGhpcy5za2lwU3BhY2UoKTtyZXR1cm4gdGhpcy5uZXh0VG9rZW4oKTt9aWYobmV4dCA9PT0gNjEpc2l6ZSA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyArIDIpID09PSA2MT8zOjI7cmV0dXJuIHRoaXMuZmluaXNoT3AoX3Rva2VudHlwZS50eXBlcy5yZWxhdGlvbmFsLHNpemUpO307cHAucmVhZFRva2VuX2VxX2V4Y2wgPSBmdW5jdGlvbihjb2RlKXsgLy8gJz0hJ1xudmFyIG5leHQ9dGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMSk7aWYobmV4dCA9PT0gNjEpcmV0dXJuIHRoaXMuZmluaXNoT3AoX3Rva2VudHlwZS50eXBlcy5lcXVhbGl0eSx0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MgKyAyKSA9PT0gNjE/MzoyKTtpZihjb2RlID09PSA2MSAmJiBuZXh0ID09PSA2MiAmJiB0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNil7IC8vICc9PidcbnRoaXMucG9zICs9IDI7cmV0dXJuIHRoaXMuZmluaXNoVG9rZW4oX3Rva2VudHlwZS50eXBlcy5hcnJvdyk7fXJldHVybiB0aGlzLmZpbmlzaE9wKGNvZGUgPT09IDYxP190b2tlbnR5cGUudHlwZXMuZXE6X3Rva2VudHlwZS50eXBlcy5wcmVmaXgsMSk7fTtwcC5nZXRUb2tlbkZyb21Db2RlID0gZnVuY3Rpb24oY29kZSl7c3dpdGNoKGNvZGUpeyAvLyBUaGUgaW50ZXJwcmV0YXRpb24gb2YgYSBkb3QgZGVwZW5kcyBvbiB3aGV0aGVyIGl0IGlzIGZvbGxvd2VkXG4vLyBieSBhIGRpZ2l0IG9yIGFub3RoZXIgdHdvIGRvdHMuXG5jYXNlIDQ2OiAvLyAnLidcbnJldHVybiB0aGlzLnJlYWRUb2tlbl9kb3QoKTsgLy8gUHVuY3R1YXRpb24gdG9rZW5zLlxuY2FzZSA0MDorK3RoaXMucG9zO3JldHVybiB0aGlzLmZpbmlzaFRva2VuKF90b2tlbnR5cGUudHlwZXMucGFyZW5MKTtjYXNlIDQxOisrdGhpcy5wb3M7cmV0dXJuIHRoaXMuZmluaXNoVG9rZW4oX3Rva2VudHlwZS50eXBlcy5wYXJlblIpO2Nhc2UgNTk6Kyt0aGlzLnBvcztyZXR1cm4gdGhpcy5maW5pc2hUb2tlbihfdG9rZW50eXBlLnR5cGVzLnNlbWkpO2Nhc2UgNDQ6Kyt0aGlzLnBvcztyZXR1cm4gdGhpcy5maW5pc2hUb2tlbihfdG9rZW50eXBlLnR5cGVzLmNvbW1hKTtjYXNlIDkxOisrdGhpcy5wb3M7cmV0dXJuIHRoaXMuZmluaXNoVG9rZW4oX3Rva2VudHlwZS50eXBlcy5icmFja2V0TCk7Y2FzZSA5MzorK3RoaXMucG9zO3JldHVybiB0aGlzLmZpbmlzaFRva2VuKF90b2tlbnR5cGUudHlwZXMuYnJhY2tldFIpO2Nhc2UgMTIzOisrdGhpcy5wb3M7cmV0dXJuIHRoaXMuZmluaXNoVG9rZW4oX3Rva2VudHlwZS50eXBlcy5icmFjZUwpO2Nhc2UgMTI1OisrdGhpcy5wb3M7cmV0dXJuIHRoaXMuZmluaXNoVG9rZW4oX3Rva2VudHlwZS50eXBlcy5icmFjZVIpO2Nhc2UgNTg6Kyt0aGlzLnBvcztyZXR1cm4gdGhpcy5maW5pc2hUb2tlbihfdG9rZW50eXBlLnR5cGVzLmNvbG9uKTtjYXNlIDYzOisrdGhpcy5wb3M7cmV0dXJuIHRoaXMuZmluaXNoVG9rZW4oX3Rva2VudHlwZS50eXBlcy5xdWVzdGlvbik7Y2FzZSA5NjogLy8gJ2AnXG5pZih0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPCA2KWJyZWFrOysrdGhpcy5wb3M7cmV0dXJuIHRoaXMuZmluaXNoVG9rZW4oX3Rva2VudHlwZS50eXBlcy5iYWNrUXVvdGUpO2Nhc2UgNDg6IC8vICcwJ1xudmFyIG5leHQ9dGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMSk7aWYobmV4dCA9PT0gMTIwIHx8IG5leHQgPT09IDg4KXJldHVybiB0aGlzLnJlYWRSYWRpeE51bWJlcigxNik7IC8vICcweCcsICcwWCcgLSBoZXggbnVtYmVyXG5pZih0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNil7aWYobmV4dCA9PT0gMTExIHx8IG5leHQgPT09IDc5KXJldHVybiB0aGlzLnJlYWRSYWRpeE51bWJlcig4KTsgLy8gJzBvJywgJzBPJyAtIG9jdGFsIG51bWJlclxuaWYobmV4dCA9PT0gOTggfHwgbmV4dCA9PT0gNjYpcmV0dXJuIHRoaXMucmVhZFJhZGl4TnVtYmVyKDIpOyAvLyAnMGInLCAnMEInIC0gYmluYXJ5IG51bWJlclxufSAvLyBBbnl0aGluZyBlbHNlIGJlZ2lubmluZyB3aXRoIGEgZGlnaXQgaXMgYW4gaW50ZWdlciwgb2N0YWxcbi8vIG51bWJlciwgb3IgZmxvYXQuXG5jYXNlIDQ5OmNhc2UgNTA6Y2FzZSA1MTpjYXNlIDUyOmNhc2UgNTM6Y2FzZSA1NDpjYXNlIDU1OmNhc2UgNTY6Y2FzZSA1NzogLy8gMS05XG5yZXR1cm4gdGhpcy5yZWFkTnVtYmVyKGZhbHNlKTsgLy8gUXVvdGVzIHByb2R1Y2Ugc3RyaW5ncy5cbmNhc2UgMzQ6Y2FzZSAzOTogLy8gJ1wiJywgXCInXCJcbnJldHVybiB0aGlzLnJlYWRTdHJpbmcoY29kZSk7IC8vIE9wZXJhdG9ycyBhcmUgcGFyc2VkIGlubGluZSBpbiB0aW55IHN0YXRlIG1hY2hpbmVzLiAnPScgKDYxKSBpc1xuLy8gb2Z0ZW4gcmVmZXJyZWQgdG8uIGBmaW5pc2hPcGAgc2ltcGx5IHNraXBzIHRoZSBhbW91bnQgb2Zcbi8vIGNoYXJhY3RlcnMgaXQgaXMgZ2l2ZW4gYXMgc2Vjb25kIGFyZ3VtZW50LCBhbmQgcmV0dXJucyBhIHRva2VuXG4vLyBvZiB0aGUgdHlwZSBnaXZlbiBieSBpdHMgZmlyc3QgYXJndW1lbnQuXG5jYXNlIDQ3OiAvLyAnLydcbnJldHVybiB0aGlzLnJlYWRUb2tlbl9zbGFzaCgpO2Nhc2UgMzc6Y2FzZSA0MjogLy8gJyUqJ1xucmV0dXJuIHRoaXMucmVhZFRva2VuX211bHRfbW9kdWxvKGNvZGUpO2Nhc2UgMTI0OmNhc2UgMzg6IC8vICd8JidcbnJldHVybiB0aGlzLnJlYWRUb2tlbl9waXBlX2FtcChjb2RlKTtjYXNlIDk0OiAvLyAnXidcbnJldHVybiB0aGlzLnJlYWRUb2tlbl9jYXJldCgpO2Nhc2UgNDM6Y2FzZSA0NTogLy8gJystJ1xucmV0dXJuIHRoaXMucmVhZFRva2VuX3BsdXNfbWluKGNvZGUpO2Nhc2UgNjA6Y2FzZSA2MjogLy8gJzw+J1xucmV0dXJuIHRoaXMucmVhZFRva2VuX2x0X2d0KGNvZGUpO2Nhc2UgNjE6Y2FzZSAzMzogLy8gJz0hJ1xucmV0dXJuIHRoaXMucmVhZFRva2VuX2VxX2V4Y2woY29kZSk7Y2FzZSAxMjY6IC8vICd+J1xucmV0dXJuIHRoaXMuZmluaXNoT3AoX3Rva2VudHlwZS50eXBlcy5wcmVmaXgsMSk7fXRoaXMucmFpc2UodGhpcy5wb3MsXCJVbmV4cGVjdGVkIGNoYXJhY3RlciAnXCIgKyBjb2RlUG9pbnRUb1N0cmluZyhjb2RlKSArIFwiJ1wiKTt9O3BwLmZpbmlzaE9wID0gZnVuY3Rpb24odHlwZSxzaXplKXt2YXIgc3RyPXRoaXMuaW5wdXQuc2xpY2UodGhpcy5wb3MsdGhpcy5wb3MgKyBzaXplKTt0aGlzLnBvcyArPSBzaXplO3JldHVybiB0aGlzLmZpbmlzaFRva2VuKHR5cGUsc3RyKTt9OyAvLyBQYXJzZSBhIHJlZ3VsYXIgZXhwcmVzc2lvbi4gU29tZSBjb250ZXh0LWF3YXJlbmVzcyBpcyBuZWNlc3NhcnksXG4vLyBzaW5jZSBhICcvJyBpbnNpZGUgYSAnW10nIHNldCBkb2VzIG5vdCBlbmQgdGhlIGV4cHJlc3Npb24uXG5mdW5jdGlvbiB0cnlDcmVhdGVSZWdleHAoc3JjLGZsYWdzLHRocm93RXJyb3JBdCl7dHJ5e3JldHVybiBuZXcgUmVnRXhwKHNyYyxmbGFncyk7fWNhdGNoKGUpIHtpZih0aHJvd0Vycm9yQXQgIT09IHVuZGVmaW5lZCl7aWYoZSBpbnN0YW5jZW9mIFN5bnRheEVycm9yKXRoaXMucmFpc2UodGhyb3dFcnJvckF0LFwiRXJyb3IgcGFyc2luZyByZWd1bGFyIGV4cHJlc3Npb246IFwiICsgZS5tZXNzYWdlKTt0aGlzLnJhaXNlKGUpO319fXZhciByZWdleHBVbmljb2RlU3VwcG9ydD0hIXRyeUNyZWF0ZVJlZ2V4cChcIu+/v1wiLFwidVwiKTtwcC5yZWFkUmVnZXhwID0gZnVuY3Rpb24oKXt2YXIgX3RoaXM9dGhpczt2YXIgZXNjYXBlZD11bmRlZmluZWQsaW5DbGFzcz11bmRlZmluZWQsc3RhcnQ9dGhpcy5wb3M7Zm9yKDs7KSB7aWYodGhpcy5wb3MgPj0gdGhpcy5pbnB1dC5sZW5ndGgpdGhpcy5yYWlzZShzdGFydCxcIlVudGVybWluYXRlZCByZWd1bGFyIGV4cHJlc3Npb25cIik7dmFyIGNoPXRoaXMuaW5wdXQuY2hhckF0KHRoaXMucG9zKTtpZihfd2hpdGVzcGFjZS5saW5lQnJlYWsudGVzdChjaCkpdGhpcy5yYWlzZShzdGFydCxcIlVudGVybWluYXRlZCByZWd1bGFyIGV4cHJlc3Npb25cIik7aWYoIWVzY2FwZWQpe2lmKGNoID09PSBcIltcIilpbkNsYXNzID0gdHJ1ZTtlbHNlIGlmKGNoID09PSBcIl1cIiAmJiBpbkNsYXNzKWluQ2xhc3MgPSBmYWxzZTtlbHNlIGlmKGNoID09PSBcIi9cIiAmJiAhaW5DbGFzcylicmVhaztlc2NhcGVkID0gY2ggPT09IFwiXFxcXFwiO31lbHNlIGVzY2FwZWQgPSBmYWxzZTsrK3RoaXMucG9zO312YXIgY29udGVudD10aGlzLmlucHV0LnNsaWNlKHN0YXJ0LHRoaXMucG9zKTsrK3RoaXMucG9zOyAvLyBOZWVkIHRvIHVzZSBgcmVhZFdvcmQxYCBiZWNhdXNlICdcXHVYWFhYJyBzZXF1ZW5jZXMgYXJlIGFsbG93ZWRcbi8vIGhlcmUgKGRvbid0IGFzaykuXG52YXIgbW9kcz10aGlzLnJlYWRXb3JkMSgpO3ZhciB0bXA9Y29udGVudDtpZihtb2RzKXt2YXIgdmFsaWRGbGFncz0vXltnbXNpeV0qJC87aWYodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYpdmFsaWRGbGFncyA9IC9eW2dtc2l5dV0qJC87aWYoIXZhbGlkRmxhZ3MudGVzdChtb2RzKSl0aGlzLnJhaXNlKHN0YXJ0LFwiSW52YWxpZCByZWd1bGFyIGV4cHJlc3Npb24gZmxhZ1wiKTtpZihtb2RzLmluZGV4T2YoJ3UnKSA+PSAwICYmICFyZWdleHBVbmljb2RlU3VwcG9ydCl7IC8vIFJlcGxhY2UgZWFjaCBhc3RyYWwgc3ltYm9sIGFuZCBldmVyeSBVbmljb2RlIGVzY2FwZSBzZXF1ZW5jZSB0aGF0XG4vLyBwb3NzaWJseSByZXByZXNlbnRzIGFuIGFzdHJhbCBzeW1ib2wgb3IgYSBwYWlyZWQgc3Vycm9nYXRlIHdpdGggYVxuLy8gc2luZ2xlIEFTQ0lJIHN5bWJvbCB0byBhdm9pZCB0aHJvd2luZyBvbiByZWd1bGFyIGV4cHJlc3Npb25zIHRoYXRcbi8vIGFyZSBvbmx5IHZhbGlkIGluIGNvbWJpbmF0aW9uIHdpdGggdGhlIGAvdWAgZmxhZy5cbi8vIE5vdGU6IHJlcGxhY2luZyB3aXRoIHRoZSBBU0NJSSBzeW1ib2wgYHhgIG1pZ2h0IGNhdXNlIGZhbHNlXG4vLyBuZWdhdGl2ZXMgaW4gdW5saWtlbHkgc2NlbmFyaW9zLiBGb3IgZXhhbXBsZSwgYFtcXHV7NjF9LWJdYCBpcyBhXG4vLyBwZXJmZWN0bHkgdmFsaWQgcGF0dGVybiB0aGF0IGlzIGVxdWl2YWxlbnQgdG8gYFthLWJdYCwgYnV0IGl0IHdvdWxkXG4vLyBiZSByZXBsYWNlZCBieSBgW3gtYl1gIHdoaWNoIHRocm93cyBhbiBlcnJvci5cbnRtcCA9IHRtcC5yZXBsYWNlKC9cXFxcdVxceyhbMC05YS1mQS1GXSspXFx9L2csZnVuY3Rpb24obWF0Y2gsY29kZSxvZmZzZXQpe2NvZGUgPSBOdW1iZXIoXCIweFwiICsgY29kZSk7aWYoY29kZSA+IDB4MTBGRkZGKV90aGlzLnJhaXNlKHN0YXJ0ICsgb2Zmc2V0ICsgMyxcIkNvZGUgcG9pbnQgb3V0IG9mIGJvdW5kc1wiKTtyZXR1cm4gXCJ4XCI7fSk7dG1wID0gdG1wLnJlcGxhY2UoL1xcXFx1KFthLWZBLUYwLTldezR9KXxbXFx1RDgwMC1cXHVEQkZGXVtcXHVEQzAwLVxcdURGRkZdL2csXCJ4XCIpO319IC8vIERldGVjdCBpbnZhbGlkIHJlZ3VsYXIgZXhwcmVzc2lvbnMuXG52YXIgdmFsdWU9bnVsbDsgLy8gUmhpbm8ncyByZWd1bGFyIGV4cHJlc3Npb24gcGFyc2VyIGlzIGZsYWt5IGFuZCB0aHJvd3MgdW5jYXRjaGFibGUgZXhjZXB0aW9ucyxcbi8vIHNvIGRvbid0IGRvIGRldGVjdGlvbiBpZiB3ZSBhcmUgcnVubmluZyB1bmRlciBSaGlub1xuaWYoIWlzUmhpbm8pe3RyeUNyZWF0ZVJlZ2V4cCh0bXAsdW5kZWZpbmVkLHN0YXJ0KTsgLy8gR2V0IGEgcmVndWxhciBleHByZXNzaW9uIG9iamVjdCBmb3IgdGhpcyBwYXR0ZXJuLWZsYWcgcGFpciwgb3IgYG51bGxgIGluXG4vLyBjYXNlIHRoZSBjdXJyZW50IGVudmlyb25tZW50IGRvZXNuJ3Qgc3VwcG9ydCB0aGUgZmxhZ3MgaXQgdXNlcy5cbnZhbHVlID0gdHJ5Q3JlYXRlUmVnZXhwKGNvbnRlbnQsbW9kcyk7fXJldHVybiB0aGlzLmZpbmlzaFRva2VuKF90b2tlbnR5cGUudHlwZXMucmVnZXhwLHtwYXR0ZXJuOmNvbnRlbnQsZmxhZ3M6bW9kcyx2YWx1ZTp2YWx1ZX0pO307IC8vIFJlYWQgYW4gaW50ZWdlciBpbiB0aGUgZ2l2ZW4gcmFkaXguIFJldHVybiBudWxsIGlmIHplcm8gZGlnaXRzXG4vLyB3ZXJlIHJlYWQsIHRoZSBpbnRlZ2VyIHZhbHVlIG90aGVyd2lzZS4gV2hlbiBgbGVuYCBpcyBnaXZlbiwgdGhpc1xuLy8gd2lsbCByZXR1cm4gYG51bGxgIHVubGVzcyB0aGUgaW50ZWdlciBoYXMgZXhhY3RseSBgbGVuYCBkaWdpdHMuXG5wcC5yZWFkSW50ID0gZnVuY3Rpb24ocmFkaXgsbGVuKXt2YXIgc3RhcnQ9dGhpcy5wb3MsdG90YWw9MDtmb3IodmFyIGk9MCxlPWxlbiA9PSBudWxsP0luZmluaXR5OmxlbjtpIDwgZTsrK2kpIHt2YXIgY29kZT10aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MpLHZhbD11bmRlZmluZWQ7aWYoY29kZSA+PSA5Nyl2YWwgPSBjb2RlIC0gOTcgKyAxMDsgLy8gYVxuZWxzZSBpZihjb2RlID49IDY1KXZhbCA9IGNvZGUgLSA2NSArIDEwOyAvLyBBXG5lbHNlIGlmKGNvZGUgPj0gNDggJiYgY29kZSA8PSA1Nyl2YWwgPSBjb2RlIC0gNDg7IC8vIDAtOVxuZWxzZSB2YWwgPSBJbmZpbml0eTtpZih2YWwgPj0gcmFkaXgpYnJlYWs7Kyt0aGlzLnBvczt0b3RhbCA9IHRvdGFsICogcmFkaXggKyB2YWw7fWlmKHRoaXMucG9zID09PSBzdGFydCB8fCBsZW4gIT0gbnVsbCAmJiB0aGlzLnBvcyAtIHN0YXJ0ICE9PSBsZW4pcmV0dXJuIG51bGw7cmV0dXJuIHRvdGFsO307cHAucmVhZFJhZGl4TnVtYmVyID0gZnVuY3Rpb24ocmFkaXgpe3RoaXMucG9zICs9IDI7IC8vIDB4XG52YXIgdmFsPXRoaXMucmVhZEludChyYWRpeCk7aWYodmFsID09IG51bGwpdGhpcy5yYWlzZSh0aGlzLnN0YXJ0ICsgMixcIkV4cGVjdGVkIG51bWJlciBpbiByYWRpeCBcIiArIHJhZGl4KTtpZihfaWRlbnRpZmllci5pc0lkZW50aWZpZXJTdGFydCh0aGlzLmZ1bGxDaGFyQ29kZUF0UG9zKCkpKXRoaXMucmFpc2UodGhpcy5wb3MsXCJJZGVudGlmaWVyIGRpcmVjdGx5IGFmdGVyIG51bWJlclwiKTtyZXR1cm4gdGhpcy5maW5pc2hUb2tlbihfdG9rZW50eXBlLnR5cGVzLm51bSx2YWwpO307IC8vIFJlYWQgYW4gaW50ZWdlciwgb2N0YWwgaW50ZWdlciwgb3IgZmxvYXRpbmctcG9pbnQgbnVtYmVyLlxucHAucmVhZE51bWJlciA9IGZ1bmN0aW9uKHN0YXJ0c1dpdGhEb3Qpe3ZhciBzdGFydD10aGlzLnBvcyxpc0Zsb2F0PWZhbHNlLG9jdGFsPXRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcykgPT09IDQ4O2lmKCFzdGFydHNXaXRoRG90ICYmIHRoaXMucmVhZEludCgxMCkgPT09IG51bGwpdGhpcy5yYWlzZShzdGFydCxcIkludmFsaWQgbnVtYmVyXCIpO3ZhciBuZXh0PXRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyk7aWYobmV4dCA9PT0gNDYpeyAvLyAnLidcbisrdGhpcy5wb3M7dGhpcy5yZWFkSW50KDEwKTtpc0Zsb2F0ID0gdHJ1ZTtuZXh0ID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zKTt9aWYobmV4dCA9PT0gNjkgfHwgbmV4dCA9PT0gMTAxKXsgLy8gJ2VFJ1xubmV4dCA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdCgrK3RoaXMucG9zKTtpZihuZXh0ID09PSA0MyB8fCBuZXh0ID09PSA0NSkrK3RoaXMucG9zOyAvLyAnKy0nXG5pZih0aGlzLnJlYWRJbnQoMTApID09PSBudWxsKXRoaXMucmFpc2Uoc3RhcnQsXCJJbnZhbGlkIG51bWJlclwiKTtpc0Zsb2F0ID0gdHJ1ZTt9aWYoX2lkZW50aWZpZXIuaXNJZGVudGlmaWVyU3RhcnQodGhpcy5mdWxsQ2hhckNvZGVBdFBvcygpKSl0aGlzLnJhaXNlKHRoaXMucG9zLFwiSWRlbnRpZmllciBkaXJlY3RseSBhZnRlciBudW1iZXJcIik7dmFyIHN0cj10aGlzLmlucHV0LnNsaWNlKHN0YXJ0LHRoaXMucG9zKSx2YWw9dW5kZWZpbmVkO2lmKGlzRmxvYXQpdmFsID0gcGFyc2VGbG9hdChzdHIpO2Vsc2UgaWYoIW9jdGFsIHx8IHN0ci5sZW5ndGggPT09IDEpdmFsID0gcGFyc2VJbnQoc3RyLDEwKTtlbHNlIGlmKC9bODldLy50ZXN0KHN0cikgfHwgdGhpcy5zdHJpY3QpdGhpcy5yYWlzZShzdGFydCxcIkludmFsaWQgbnVtYmVyXCIpO2Vsc2UgdmFsID0gcGFyc2VJbnQoc3RyLDgpO3JldHVybiB0aGlzLmZpbmlzaFRva2VuKF90b2tlbnR5cGUudHlwZXMubnVtLHZhbCk7fTsgLy8gUmVhZCBhIHN0cmluZyB2YWx1ZSwgaW50ZXJwcmV0aW5nIGJhY2tzbGFzaC1lc2NhcGVzLlxucHAucmVhZENvZGVQb2ludCA9IGZ1bmN0aW9uKCl7dmFyIGNoPXRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyksY29kZT11bmRlZmluZWQ7aWYoY2ggPT09IDEyMyl7aWYodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uIDwgNil0aGlzLnVuZXhwZWN0ZWQoKTt2YXIgY29kZVBvcz0rK3RoaXMucG9zO2NvZGUgPSB0aGlzLnJlYWRIZXhDaGFyKHRoaXMuaW5wdXQuaW5kZXhPZignfScsdGhpcy5wb3MpIC0gdGhpcy5wb3MpOysrdGhpcy5wb3M7aWYoY29kZSA+IDB4MTBGRkZGKXRoaXMucmFpc2UoY29kZVBvcyxcIkNvZGUgcG9pbnQgb3V0IG9mIGJvdW5kc1wiKTt9ZWxzZSB7Y29kZSA9IHRoaXMucmVhZEhleENoYXIoNCk7fXJldHVybiBjb2RlO307ZnVuY3Rpb24gY29kZVBvaW50VG9TdHJpbmcoY29kZSl7IC8vIFVURi0xNiBEZWNvZGluZ1xuaWYoY29kZSA8PSAweEZGRkYpcmV0dXJuIFN0cmluZy5mcm9tQ2hhckNvZGUoY29kZSk7Y29kZSAtPSAweDEwMDAwO3JldHVybiBTdHJpbmcuZnJvbUNoYXJDb2RlKChjb2RlID4+IDEwKSArIDB4RDgwMCwoY29kZSAmIDEwMjMpICsgMHhEQzAwKTt9cHAucmVhZFN0cmluZyA9IGZ1bmN0aW9uKHF1b3RlKXt2YXIgb3V0PVwiXCIsY2h1bmtTdGFydD0rK3RoaXMucG9zO2Zvcig7Oykge2lmKHRoaXMucG9zID49IHRoaXMuaW5wdXQubGVuZ3RoKXRoaXMucmFpc2UodGhpcy5zdGFydCxcIlVudGVybWluYXRlZCBzdHJpbmcgY29uc3RhbnRcIik7dmFyIGNoPXRoaXMuaW5wdXQuY2hhckNvZGVBdCh0aGlzLnBvcyk7aWYoY2ggPT09IHF1b3RlKWJyZWFrO2lmKGNoID09PSA5Mil7IC8vICdcXCdcbm91dCArPSB0aGlzLmlucHV0LnNsaWNlKGNodW5rU3RhcnQsdGhpcy5wb3MpO291dCArPSB0aGlzLnJlYWRFc2NhcGVkQ2hhcihmYWxzZSk7Y2h1bmtTdGFydCA9IHRoaXMucG9zO31lbHNlIHtpZihfd2hpdGVzcGFjZS5pc05ld0xpbmUoY2gpKXRoaXMucmFpc2UodGhpcy5zdGFydCxcIlVudGVybWluYXRlZCBzdHJpbmcgY29uc3RhbnRcIik7Kyt0aGlzLnBvczt9fW91dCArPSB0aGlzLmlucHV0LnNsaWNlKGNodW5rU3RhcnQsdGhpcy5wb3MrKyk7cmV0dXJuIHRoaXMuZmluaXNoVG9rZW4oX3Rva2VudHlwZS50eXBlcy5zdHJpbmcsb3V0KTt9OyAvLyBSZWFkcyB0ZW1wbGF0ZSBzdHJpbmcgdG9rZW5zLlxucHAucmVhZFRtcGxUb2tlbiA9IGZ1bmN0aW9uKCl7dmFyIG91dD1cIlwiLGNodW5rU3RhcnQ9dGhpcy5wb3M7Zm9yKDs7KSB7aWYodGhpcy5wb3MgPj0gdGhpcy5pbnB1dC5sZW5ndGgpdGhpcy5yYWlzZSh0aGlzLnN0YXJ0LFwiVW50ZXJtaW5hdGVkIHRlbXBsYXRlXCIpO3ZhciBjaD10aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MpO2lmKGNoID09PSA5NiB8fCBjaCA9PT0gMzYgJiYgdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zICsgMSkgPT09IDEyMyl7IC8vICdgJywgJyR7J1xuaWYodGhpcy5wb3MgPT09IHRoaXMuc3RhcnQgJiYgdGhpcy50eXBlID09PSBfdG9rZW50eXBlLnR5cGVzLnRlbXBsYXRlKXtpZihjaCA9PT0gMzYpe3RoaXMucG9zICs9IDI7cmV0dXJuIHRoaXMuZmluaXNoVG9rZW4oX3Rva2VudHlwZS50eXBlcy5kb2xsYXJCcmFjZUwpO31lbHNlIHsrK3RoaXMucG9zO3JldHVybiB0aGlzLmZpbmlzaFRva2VuKF90b2tlbnR5cGUudHlwZXMuYmFja1F1b3RlKTt9fW91dCArPSB0aGlzLmlucHV0LnNsaWNlKGNodW5rU3RhcnQsdGhpcy5wb3MpO3JldHVybiB0aGlzLmZpbmlzaFRva2VuKF90b2tlbnR5cGUudHlwZXMudGVtcGxhdGUsb3V0KTt9aWYoY2ggPT09IDkyKXsgLy8gJ1xcJ1xub3V0ICs9IHRoaXMuaW5wdXQuc2xpY2UoY2h1bmtTdGFydCx0aGlzLnBvcyk7b3V0ICs9IHRoaXMucmVhZEVzY2FwZWRDaGFyKHRydWUpO2NodW5rU3RhcnQgPSB0aGlzLnBvczt9ZWxzZSBpZihfd2hpdGVzcGFjZS5pc05ld0xpbmUoY2gpKXtvdXQgKz0gdGhpcy5pbnB1dC5zbGljZShjaHVua1N0YXJ0LHRoaXMucG9zKTsrK3RoaXMucG9zO3N3aXRjaChjaCl7Y2FzZSAxMzppZih0aGlzLmlucHV0LmNoYXJDb2RlQXQodGhpcy5wb3MpID09PSAxMCkrK3RoaXMucG9zO2Nhc2UgMTA6b3V0ICs9IFwiXFxuXCI7YnJlYWs7ZGVmYXVsdDpvdXQgKz0gU3RyaW5nLmZyb21DaGFyQ29kZShjaCk7YnJlYWs7fWlmKHRoaXMub3B0aW9ucy5sb2NhdGlvbnMpeysrdGhpcy5jdXJMaW5lO3RoaXMubGluZVN0YXJ0ID0gdGhpcy5wb3M7fWNodW5rU3RhcnQgPSB0aGlzLnBvczt9ZWxzZSB7Kyt0aGlzLnBvczt9fX07IC8vIFVzZWQgdG8gcmVhZCBlc2NhcGVkIGNoYXJhY3RlcnNcbnBwLnJlYWRFc2NhcGVkQ2hhciA9IGZ1bmN0aW9uKGluVGVtcGxhdGUpe3ZhciBjaD10aGlzLmlucHV0LmNoYXJDb2RlQXQoKyt0aGlzLnBvcyk7Kyt0aGlzLnBvcztzd2l0Y2goY2gpe2Nhc2UgMTEwOnJldHVybiBcIlxcblwiOyAvLyAnbicgLT4gJ1xcbidcbmNhc2UgMTE0OnJldHVybiBcIlxcclwiOyAvLyAncicgLT4gJ1xccidcbmNhc2UgMTIwOnJldHVybiBTdHJpbmcuZnJvbUNoYXJDb2RlKHRoaXMucmVhZEhleENoYXIoMikpOyAvLyAneCdcbmNhc2UgMTE3OnJldHVybiBjb2RlUG9pbnRUb1N0cmluZyh0aGlzLnJlYWRDb2RlUG9pbnQoKSk7IC8vICd1J1xuY2FzZSAxMTY6cmV0dXJuIFwiXFx0XCI7IC8vICd0JyAtPiAnXFx0J1xuY2FzZSA5ODpyZXR1cm4gXCJcXGJcIjsgLy8gJ2InIC0+ICdcXGInXG5jYXNlIDExODpyZXR1cm4gXCJcXHUwMDBiXCI7IC8vICd2JyAtPiAnXFx1MDAwYidcbmNhc2UgMTAyOnJldHVybiBcIlxcZlwiOyAvLyAnZicgLT4gJ1xcZidcbmNhc2UgMTM6aWYodGhpcy5pbnB1dC5jaGFyQ29kZUF0KHRoaXMucG9zKSA9PT0gMTApKyt0aGlzLnBvczsgLy8gJ1xcclxcbidcbmNhc2UgMTA6IC8vICcgXFxuJ1xuaWYodGhpcy5vcHRpb25zLmxvY2F0aW9ucyl7dGhpcy5saW5lU3RhcnQgPSB0aGlzLnBvczsrK3RoaXMuY3VyTGluZTt9cmV0dXJuIFwiXCI7ZGVmYXVsdDppZihjaCA+PSA0OCAmJiBjaCA8PSA1NSl7dmFyIG9jdGFsU3RyPXRoaXMuaW5wdXQuc3Vic3RyKHRoaXMucG9zIC0gMSwzKS5tYXRjaCgvXlswLTddKy8pWzBdO3ZhciBvY3RhbD1wYXJzZUludChvY3RhbFN0ciw4KTtpZihvY3RhbCA+IDI1NSl7b2N0YWxTdHIgPSBvY3RhbFN0ci5zbGljZSgwLC0xKTtvY3RhbCA9IHBhcnNlSW50KG9jdGFsU3RyLDgpO31pZihvY3RhbCA+IDAgJiYgKHRoaXMuc3RyaWN0IHx8IGluVGVtcGxhdGUpKXt0aGlzLnJhaXNlKHRoaXMucG9zIC0gMixcIk9jdGFsIGxpdGVyYWwgaW4gc3RyaWN0IG1vZGVcIik7fXRoaXMucG9zICs9IG9jdGFsU3RyLmxlbmd0aCAtIDE7cmV0dXJuIFN0cmluZy5mcm9tQ2hhckNvZGUob2N0YWwpO31yZXR1cm4gU3RyaW5nLmZyb21DaGFyQ29kZShjaCk7fX07IC8vIFVzZWQgdG8gcmVhZCBjaGFyYWN0ZXIgZXNjYXBlIHNlcXVlbmNlcyAoJ1xceCcsICdcXHUnLCAnXFxVJykuXG5wcC5yZWFkSGV4Q2hhciA9IGZ1bmN0aW9uKGxlbil7dmFyIGNvZGVQb3M9dGhpcy5wb3M7dmFyIG49dGhpcy5yZWFkSW50KDE2LGxlbik7aWYobiA9PT0gbnVsbCl0aGlzLnJhaXNlKGNvZGVQb3MsXCJCYWQgY2hhcmFjdGVyIGVzY2FwZSBzZXF1ZW5jZVwiKTtyZXR1cm4gbjt9OyAvLyBSZWFkIGFuIGlkZW50aWZpZXIsIGFuZCByZXR1cm4gaXQgYXMgYSBzdHJpbmcuIFNldHMgYHRoaXMuY29udGFpbnNFc2NgXG4vLyB0byB3aGV0aGVyIHRoZSB3b3JkIGNvbnRhaW5lZCBhICdcXHUnIGVzY2FwZS5cbi8vXG4vLyBJbmNyZW1lbnRhbGx5IGFkZHMgb25seSBlc2NhcGVkIGNoYXJzLCBhZGRpbmcgb3RoZXIgY2h1bmtzIGFzLWlzXG4vLyBhcyBhIG1pY3JvLW9wdGltaXphdGlvbi5cbnBwLnJlYWRXb3JkMSA9IGZ1bmN0aW9uKCl7dGhpcy5jb250YWluc0VzYyA9IGZhbHNlO3ZhciB3b3JkPVwiXCIsZmlyc3Q9dHJ1ZSxjaHVua1N0YXJ0PXRoaXMucG9zO3ZhciBhc3RyYWw9dGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDY7d2hpbGUodGhpcy5wb3MgPCB0aGlzLmlucHV0Lmxlbmd0aCkge3ZhciBjaD10aGlzLmZ1bGxDaGFyQ29kZUF0UG9zKCk7aWYoX2lkZW50aWZpZXIuaXNJZGVudGlmaWVyQ2hhcihjaCxhc3RyYWwpKXt0aGlzLnBvcyArPSBjaCA8PSAweGZmZmY/MToyO31lbHNlIGlmKGNoID09PSA5Mil7IC8vIFwiXFxcIlxudGhpcy5jb250YWluc0VzYyA9IHRydWU7d29yZCArPSB0aGlzLmlucHV0LnNsaWNlKGNodW5rU3RhcnQsdGhpcy5wb3MpO3ZhciBlc2NTdGFydD10aGlzLnBvcztpZih0aGlzLmlucHV0LmNoYXJDb2RlQXQoKyt0aGlzLnBvcykgIT0gMTE3KSAvLyBcInVcIlxudGhpcy5yYWlzZSh0aGlzLnBvcyxcIkV4cGVjdGluZyBVbmljb2RlIGVzY2FwZSBzZXF1ZW5jZSBcXFxcdVhYWFhcIik7Kyt0aGlzLnBvczt2YXIgZXNjPXRoaXMucmVhZENvZGVQb2ludCgpO2lmKCEoZmlyc3Q/X2lkZW50aWZpZXIuaXNJZGVudGlmaWVyU3RhcnQ6X2lkZW50aWZpZXIuaXNJZGVudGlmaWVyQ2hhcikoZXNjLGFzdHJhbCkpdGhpcy5yYWlzZShlc2NTdGFydCxcIkludmFsaWQgVW5pY29kZSBlc2NhcGVcIik7d29yZCArPSBjb2RlUG9pbnRUb1N0cmluZyhlc2MpO2NodW5rU3RhcnQgPSB0aGlzLnBvczt9ZWxzZSB7YnJlYWs7fWZpcnN0ID0gZmFsc2U7fXJldHVybiB3b3JkICsgdGhpcy5pbnB1dC5zbGljZShjaHVua1N0YXJ0LHRoaXMucG9zKTt9OyAvLyBSZWFkIGFuIGlkZW50aWZpZXIgb3Iga2V5d29yZCB0b2tlbi4gV2lsbCBjaGVjayBmb3IgcmVzZXJ2ZWRcbi8vIHdvcmRzIHdoZW4gbmVjZXNzYXJ5LlxucHAucmVhZFdvcmQgPSBmdW5jdGlvbigpe3ZhciB3b3JkPXRoaXMucmVhZFdvcmQxKCk7dmFyIHR5cGU9X3Rva2VudHlwZS50eXBlcy5uYW1lO2lmKCh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNiB8fCAhdGhpcy5jb250YWluc0VzYykgJiYgdGhpcy5pc0tleXdvcmQod29yZCkpdHlwZSA9IF90b2tlbnR5cGUua2V5d29yZHNbd29yZF07cmV0dXJuIHRoaXMuZmluaXNoVG9rZW4odHlwZSx3b3JkKTt9O30se1wiLi9pZGVudGlmaWVyXCI6MixcIi4vbG9jdXRpbFwiOjUsXCIuL3N0YXRlXCI6MTAsXCIuL3Rva2VudHlwZVwiOjE0LFwiLi93aGl0ZXNwYWNlXCI6MTZ9XSwxNDpbZnVuY3Rpb24oX2RlcmVxXyxtb2R1bGUsZXhwb3J0cyl7IC8vICMjIFRva2VuIHR5cGVzXG4vLyBUaGUgYXNzaWdubWVudCBvZiBmaW5lLWdyYWluZWQsIGluZm9ybWF0aW9uLWNhcnJ5aW5nIHR5cGUgb2JqZWN0c1xuLy8gYWxsb3dzIHRoZSB0b2tlbml6ZXIgdG8gc3RvcmUgdGhlIGluZm9ybWF0aW9uIGl0IGhhcyBhYm91dCBhXG4vLyB0b2tlbiBpbiBhIHdheSB0aGF0IGlzIHZlcnkgY2hlYXAgZm9yIHRoZSBwYXJzZXIgdG8gbG9vayB1cC5cbi8vIEFsbCB0b2tlbiB0eXBlIHZhcmlhYmxlcyBzdGFydCB3aXRoIGFuIHVuZGVyc2NvcmUsIHRvIG1ha2UgdGhlbVxuLy8gZWFzeSB0byByZWNvZ25pemUuXG4vLyBUaGUgYGJlZm9yZUV4cHJgIHByb3BlcnR5IGlzIHVzZWQgdG8gZGlzYW1iaWd1YXRlIGJldHdlZW4gcmVndWxhclxuLy8gZXhwcmVzc2lvbnMgYW5kIGRpdmlzaW9ucy4gSXQgaXMgc2V0IG9uIGFsbCB0b2tlbiB0eXBlcyB0aGF0IGNhblxuLy8gYmUgZm9sbG93ZWQgYnkgYW4gZXhwcmVzc2lvbiAodGh1cywgYSBzbGFzaCBhZnRlciB0aGVtIHdvdWxkIGJlIGFcbi8vIHJlZ3VsYXIgZXhwcmVzc2lvbikuXG4vL1xuLy8gYGlzTG9vcGAgbWFya3MgYSBrZXl3b3JkIGFzIHN0YXJ0aW5nIGEgbG9vcCwgd2hpY2ggaXMgaW1wb3J0YW50XG4vLyB0byBrbm93IHdoZW4gcGFyc2luZyBhIGxhYmVsLCBpbiBvcmRlciB0byBhbGxvdyBvciBkaXNhbGxvd1xuLy8gY29udGludWUganVtcHMgdG8gdGhhdCBsYWJlbC5cblwidXNlIHN0cmljdFwiO2V4cG9ydHMuX19lc01vZHVsZSA9IHRydWU7ZnVuY3Rpb24gX2NsYXNzQ2FsbENoZWNrKGluc3RhbmNlLENvbnN0cnVjdG9yKXtpZighKGluc3RhbmNlIGluc3RhbmNlb2YgQ29uc3RydWN0b3IpKXt0aHJvdyBuZXcgVHlwZUVycm9yKFwiQ2Fubm90IGNhbGwgYSBjbGFzcyBhcyBhIGZ1bmN0aW9uXCIpO319dmFyIFRva2VuVHlwZT1mdW5jdGlvbiBUb2tlblR5cGUobGFiZWwpe3ZhciBjb25mPWFyZ3VtZW50cy5sZW5ndGggPD0gMSB8fCBhcmd1bWVudHNbMV0gPT09IHVuZGVmaW5lZD97fTphcmd1bWVudHNbMV07X2NsYXNzQ2FsbENoZWNrKHRoaXMsVG9rZW5UeXBlKTt0aGlzLmxhYmVsID0gbGFiZWw7dGhpcy5rZXl3b3JkID0gY29uZi5rZXl3b3JkO3RoaXMuYmVmb3JlRXhwciA9ICEhY29uZi5iZWZvcmVFeHByO3RoaXMuc3RhcnRzRXhwciA9ICEhY29uZi5zdGFydHNFeHByO3RoaXMuaXNMb29wID0gISFjb25mLmlzTG9vcDt0aGlzLmlzQXNzaWduID0gISFjb25mLmlzQXNzaWduO3RoaXMucHJlZml4ID0gISFjb25mLnByZWZpeDt0aGlzLnBvc3RmaXggPSAhIWNvbmYucG9zdGZpeDt0aGlzLmJpbm9wID0gY29uZi5iaW5vcCB8fCBudWxsO3RoaXMudXBkYXRlQ29udGV4dCA9IG51bGw7fTtleHBvcnRzLlRva2VuVHlwZSA9IFRva2VuVHlwZTtmdW5jdGlvbiBiaW5vcChuYW1lLHByZWMpe3JldHVybiBuZXcgVG9rZW5UeXBlKG5hbWUse2JlZm9yZUV4cHI6dHJ1ZSxiaW5vcDpwcmVjfSk7fXZhciBiZWZvcmVFeHByPXtiZWZvcmVFeHByOnRydWV9LHN0YXJ0c0V4cHI9e3N0YXJ0c0V4cHI6dHJ1ZX07dmFyIHR5cGVzPXtudW06bmV3IFRva2VuVHlwZShcIm51bVwiLHN0YXJ0c0V4cHIpLHJlZ2V4cDpuZXcgVG9rZW5UeXBlKFwicmVnZXhwXCIsc3RhcnRzRXhwciksc3RyaW5nOm5ldyBUb2tlblR5cGUoXCJzdHJpbmdcIixzdGFydHNFeHByKSxuYW1lOm5ldyBUb2tlblR5cGUoXCJuYW1lXCIsc3RhcnRzRXhwciksZW9mOm5ldyBUb2tlblR5cGUoXCJlb2ZcIiksIC8vIFB1bmN0dWF0aW9uIHRva2VuIHR5cGVzLlxuYnJhY2tldEw6bmV3IFRva2VuVHlwZShcIltcIix7YmVmb3JlRXhwcjp0cnVlLHN0YXJ0c0V4cHI6dHJ1ZX0pLGJyYWNrZXRSOm5ldyBUb2tlblR5cGUoXCJdXCIpLGJyYWNlTDpuZXcgVG9rZW5UeXBlKFwie1wiLHtiZWZvcmVFeHByOnRydWUsc3RhcnRzRXhwcjp0cnVlfSksYnJhY2VSOm5ldyBUb2tlblR5cGUoXCJ9XCIpLHBhcmVuTDpuZXcgVG9rZW5UeXBlKFwiKFwiLHtiZWZvcmVFeHByOnRydWUsc3RhcnRzRXhwcjp0cnVlfSkscGFyZW5SOm5ldyBUb2tlblR5cGUoXCIpXCIpLGNvbW1hOm5ldyBUb2tlblR5cGUoXCIsXCIsYmVmb3JlRXhwciksc2VtaTpuZXcgVG9rZW5UeXBlKFwiO1wiLGJlZm9yZUV4cHIpLGNvbG9uOm5ldyBUb2tlblR5cGUoXCI6XCIsYmVmb3JlRXhwciksZG90Om5ldyBUb2tlblR5cGUoXCIuXCIpLHF1ZXN0aW9uOm5ldyBUb2tlblR5cGUoXCI/XCIsYmVmb3JlRXhwciksYXJyb3c6bmV3IFRva2VuVHlwZShcIj0+XCIsYmVmb3JlRXhwciksdGVtcGxhdGU6bmV3IFRva2VuVHlwZShcInRlbXBsYXRlXCIpLGVsbGlwc2lzOm5ldyBUb2tlblR5cGUoXCIuLi5cIixiZWZvcmVFeHByKSxiYWNrUXVvdGU6bmV3IFRva2VuVHlwZShcImBcIixzdGFydHNFeHByKSxkb2xsYXJCcmFjZUw6bmV3IFRva2VuVHlwZShcIiR7XCIse2JlZm9yZUV4cHI6dHJ1ZSxzdGFydHNFeHByOnRydWV9KSwgLy8gT3BlcmF0b3JzLiBUaGVzZSBjYXJyeSBzZXZlcmFsIGtpbmRzIG9mIHByb3BlcnRpZXMgdG8gaGVscCB0aGVcbi8vIHBhcnNlciB1c2UgdGhlbSBwcm9wZXJseSAodGhlIHByZXNlbmNlIG9mIHRoZXNlIHByb3BlcnRpZXMgaXNcbi8vIHdoYXQgY2F0ZWdvcml6ZXMgdGhlbSBhcyBvcGVyYXRvcnMpLlxuLy9cbi8vIGBiaW5vcGAsIHdoZW4gcHJlc2VudCwgc3BlY2lmaWVzIHRoYXQgdGhpcyBvcGVyYXRvciBpcyBhIGJpbmFyeVxuLy8gb3BlcmF0b3IsIGFuZCB3aWxsIHJlZmVyIHRvIGl0cyBwcmVjZWRlbmNlLlxuLy9cbi8vIGBwcmVmaXhgIGFuZCBgcG9zdGZpeGAgbWFyayB0aGUgb3BlcmF0b3IgYXMgYSBwcmVmaXggb3IgcG9zdGZpeFxuLy8gdW5hcnkgb3BlcmF0b3IuXG4vL1xuLy8gYGlzQXNzaWduYCBtYXJrcyBhbGwgb2YgYD1gLCBgKz1gLCBgLT1gIGV0Y2V0ZXJhLCB3aGljaCBhY3QgYXNcbi8vIGJpbmFyeSBvcGVyYXRvcnMgd2l0aCBhIHZlcnkgbG93IHByZWNlZGVuY2UsIHRoYXQgc2hvdWxkIHJlc3VsdFxuLy8gaW4gQXNzaWdubWVudEV4cHJlc3Npb24gbm9kZXMuXG5lcTpuZXcgVG9rZW5UeXBlKFwiPVwiLHtiZWZvcmVFeHByOnRydWUsaXNBc3NpZ246dHJ1ZX0pLGFzc2lnbjpuZXcgVG9rZW5UeXBlKFwiXz1cIix7YmVmb3JlRXhwcjp0cnVlLGlzQXNzaWduOnRydWV9KSxpbmNEZWM6bmV3IFRva2VuVHlwZShcIisrLy0tXCIse3ByZWZpeDp0cnVlLHBvc3RmaXg6dHJ1ZSxzdGFydHNFeHByOnRydWV9KSxwcmVmaXg6bmV3IFRva2VuVHlwZShcInByZWZpeFwiLHtiZWZvcmVFeHByOnRydWUscHJlZml4OnRydWUsc3RhcnRzRXhwcjp0cnVlfSksbG9naWNhbE9SOmJpbm9wKFwifHxcIiwxKSxsb2dpY2FsQU5EOmJpbm9wKFwiJiZcIiwyKSxiaXR3aXNlT1I6Ymlub3AoXCJ8XCIsMyksYml0d2lzZVhPUjpiaW5vcChcIl5cIiw0KSxiaXR3aXNlQU5EOmJpbm9wKFwiJlwiLDUpLGVxdWFsaXR5OmJpbm9wKFwiPT0vIT1cIiw2KSxyZWxhdGlvbmFsOmJpbm9wKFwiPC8+XCIsNyksYml0U2hpZnQ6Ymlub3AoXCI8PC8+PlwiLDgpLHBsdXNNaW46bmV3IFRva2VuVHlwZShcIisvLVwiLHtiZWZvcmVFeHByOnRydWUsYmlub3A6OSxwcmVmaXg6dHJ1ZSxzdGFydHNFeHByOnRydWV9KSxtb2R1bG86Ymlub3AoXCIlXCIsMTApLHN0YXI6Ymlub3AoXCIqXCIsMTApLHNsYXNoOmJpbm9wKFwiL1wiLDEwKX07ZXhwb3J0cy50eXBlcyA9IHR5cGVzOyAvLyBNYXAga2V5d29yZCBuYW1lcyB0byB0b2tlbiB0eXBlcy5cbnZhciBrZXl3b3Jkcz17fTtleHBvcnRzLmtleXdvcmRzID0ga2V5d29yZHM7IC8vIFN1Y2NpbmN0IGRlZmluaXRpb25zIG9mIGtleXdvcmQgdG9rZW4gdHlwZXNcbmZ1bmN0aW9uIGt3KG5hbWUpe3ZhciBvcHRpb25zPWFyZ3VtZW50cy5sZW5ndGggPD0gMSB8fCBhcmd1bWVudHNbMV0gPT09IHVuZGVmaW5lZD97fTphcmd1bWVudHNbMV07b3B0aW9ucy5rZXl3b3JkID0gbmFtZTtrZXl3b3Jkc1tuYW1lXSA9IHR5cGVzW1wiX1wiICsgbmFtZV0gPSBuZXcgVG9rZW5UeXBlKG5hbWUsb3B0aW9ucyk7fWt3KFwiYnJlYWtcIik7a3coXCJjYXNlXCIsYmVmb3JlRXhwcik7a3coXCJjYXRjaFwiKTtrdyhcImNvbnRpbnVlXCIpO2t3KFwiZGVidWdnZXJcIik7a3coXCJkZWZhdWx0XCIsYmVmb3JlRXhwcik7a3coXCJkb1wiLHtpc0xvb3A6dHJ1ZX0pO2t3KFwiZWxzZVwiLGJlZm9yZUV4cHIpO2t3KFwiZmluYWxseVwiKTtrdyhcImZvclwiLHtpc0xvb3A6dHJ1ZX0pO2t3KFwiZnVuY3Rpb25cIixzdGFydHNFeHByKTtrdyhcImlmXCIpO2t3KFwicmV0dXJuXCIsYmVmb3JlRXhwcik7a3coXCJzd2l0Y2hcIik7a3coXCJ0aHJvd1wiLGJlZm9yZUV4cHIpO2t3KFwidHJ5XCIpO2t3KFwidmFyXCIpO2t3KFwibGV0XCIpO2t3KFwiY29uc3RcIik7a3coXCJ3aGlsZVwiLHtpc0xvb3A6dHJ1ZX0pO2t3KFwid2l0aFwiKTtrdyhcIm5ld1wiLHtiZWZvcmVFeHByOnRydWUsc3RhcnRzRXhwcjp0cnVlfSk7a3coXCJ0aGlzXCIsc3RhcnRzRXhwcik7a3coXCJzdXBlclwiLHN0YXJ0c0V4cHIpO2t3KFwiY2xhc3NcIik7a3coXCJleHRlbmRzXCIsYmVmb3JlRXhwcik7a3coXCJleHBvcnRcIik7a3coXCJpbXBvcnRcIik7a3coXCJ5aWVsZFwiLHtiZWZvcmVFeHByOnRydWUsc3RhcnRzRXhwcjp0cnVlfSk7a3coXCJudWxsXCIsc3RhcnRzRXhwcik7a3coXCJ0cnVlXCIsc3RhcnRzRXhwcik7a3coXCJmYWxzZVwiLHN0YXJ0c0V4cHIpO2t3KFwiaW5cIix7YmVmb3JlRXhwcjp0cnVlLGJpbm9wOjd9KTtrdyhcImluc3RhbmNlb2ZcIix7YmVmb3JlRXhwcjp0cnVlLGJpbm9wOjd9KTtrdyhcInR5cGVvZlwiLHtiZWZvcmVFeHByOnRydWUscHJlZml4OnRydWUsc3RhcnRzRXhwcjp0cnVlfSk7a3coXCJ2b2lkXCIse2JlZm9yZUV4cHI6dHJ1ZSxwcmVmaXg6dHJ1ZSxzdGFydHNFeHByOnRydWV9KTtrdyhcImRlbGV0ZVwiLHtiZWZvcmVFeHByOnRydWUscHJlZml4OnRydWUsc3RhcnRzRXhwcjp0cnVlfSk7fSx7fV0sMTU6W2Z1bmN0aW9uKF9kZXJlcV8sbW9kdWxlLGV4cG9ydHMpe1widXNlIHN0cmljdFwiO2V4cG9ydHMuX19lc01vZHVsZSA9IHRydWU7ZXhwb3J0cy5pc0FycmF5ID0gaXNBcnJheTtleHBvcnRzLmhhcyA9IGhhcztmdW5jdGlvbiBpc0FycmF5KG9iail7cmV0dXJuIE9iamVjdC5wcm90b3R5cGUudG9TdHJpbmcuY2FsbChvYmopID09PSBcIltvYmplY3QgQXJyYXldXCI7fSAvLyBDaGVja3MgaWYgYW4gb2JqZWN0IGhhcyBhIHByb3BlcnR5LlxuZnVuY3Rpb24gaGFzKG9iaixwcm9wTmFtZSl7cmV0dXJuIE9iamVjdC5wcm90b3R5cGUuaGFzT3duUHJvcGVydHkuY2FsbChvYmoscHJvcE5hbWUpO319LHt9XSwxNjpbZnVuY3Rpb24oX2RlcmVxXyxtb2R1bGUsZXhwb3J0cyl7IC8vIE1hdGNoZXMgYSB3aG9sZSBsaW5lIGJyZWFrICh3aGVyZSBDUkxGIGlzIGNvbnNpZGVyZWQgYSBzaW5nbGVcbi8vIGxpbmUgYnJlYWspLiBVc2VkIHRvIGNvdW50IGxpbmVzLlxuXCJ1c2Ugc3RyaWN0XCI7ZXhwb3J0cy5fX2VzTW9kdWxlID0gdHJ1ZTtleHBvcnRzLmlzTmV3TGluZSA9IGlzTmV3TGluZTt2YXIgbGluZUJyZWFrPS9cXHJcXG4/fFxcbnxcXHUyMDI4fFxcdTIwMjkvO2V4cG9ydHMubGluZUJyZWFrID0gbGluZUJyZWFrO3ZhciBsaW5lQnJlYWtHPW5ldyBSZWdFeHAobGluZUJyZWFrLnNvdXJjZSxcImdcIik7ZXhwb3J0cy5saW5lQnJlYWtHID0gbGluZUJyZWFrRztmdW5jdGlvbiBpc05ld0xpbmUoY29kZSl7cmV0dXJuIGNvZGUgPT09IDEwIHx8IGNvZGUgPT09IDEzIHx8IGNvZGUgPT09IDB4MjAyOCB8fCBjb2RlID09IDB4MjAyOTt9dmFyIG5vbkFTQ0lJd2hpdGVzcGFjZT0vW1xcdTE2ODBcXHUxODBlXFx1MjAwMC1cXHUyMDBhXFx1MjAyZlxcdTIwNWZcXHUzMDAwXFx1ZmVmZl0vO2V4cG9ydHMubm9uQVNDSUl3aGl0ZXNwYWNlID0gbm9uQVNDSUl3aGl0ZXNwYWNlO30se31dfSx7fSxbM10pKDMpO30pO1xuXG59KS5jYWxsKHRoaXMsdHlwZW9mIGdsb2JhbCAhPT0gXCJ1bmRlZmluZWRcIiA/IGdsb2JhbCA6IHR5cGVvZiBzZWxmICE9PSBcInVuZGVmaW5lZFwiID8gc2VsZiA6IHR5cGVvZiB3aW5kb3cgIT09IFwidW5kZWZpbmVkXCIgPyB3aW5kb3cgOiB7fSlcbn0se31dLDI6W2Z1bmN0aW9uKF9kZXJlcV8sbW9kdWxlLGV4cG9ydHMpe1xuXCJ1c2Ugc3RyaWN0XCI7XG5cbm1vZHVsZS5leHBvcnRzID0gdHlwZW9mIGFjb3JuICE9ICd1bmRlZmluZWQnID8gYWNvcm4gOiBfZGVyZXFfKFwiYWNvcm5cIik7XG5cbn0se1wiYWNvcm5cIjoxfV0sMzpbZnVuY3Rpb24oX2RlcmVxXyxtb2R1bGUsZXhwb3J0cyl7XG5cInVzZSBzdHJpY3RcIjtcblxudmFyIF9zdGF0ZSA9IF9kZXJlcV8oXCIuL3N0YXRlXCIpO1xuXG52YXIgX3BhcnNldXRpbCA9IF9kZXJlcV8oXCIuL3BhcnNldXRpbFwiKTtcblxudmFyIF8gPSBfZGVyZXFfKFwiLi5cIik7XG5cbnZhciBscCA9IF9zdGF0ZS5Mb29zZVBhcnNlci5wcm90b3R5cGU7XG5cbmxwLmNoZWNrTFZhbCA9IGZ1bmN0aW9uIChleHByLCBiaW5kaW5nKSB7XG4gIGlmICghZXhwcikgcmV0dXJuIGV4cHI7XG4gIHN3aXRjaCAoZXhwci50eXBlKSB7XG4gICAgY2FzZSBcIklkZW50aWZpZXJcIjpcbiAgICAgIHJldHVybiBleHByO1xuXG4gICAgY2FzZSBcIk1lbWJlckV4cHJlc3Npb25cIjpcbiAgICAgIHJldHVybiBiaW5kaW5nID8gdGhpcy5kdW1teUlkZW50KCkgOiBleHByO1xuXG4gICAgY2FzZSBcIlBhcmVudGhlc2l6ZWRFeHByZXNzaW9uXCI6XG4gICAgICBleHByLmV4cHJlc3Npb24gPSB0aGlzLmNoZWNrTFZhbChleHByLmV4cHJlc3Npb24sIGJpbmRpbmcpO1xuICAgICAgcmV0dXJuIGV4cHI7XG5cbiAgICAvLyBGSVhNRSByZWN1cnNpdmVseSBjaGVjayBjb250ZW50c1xuICAgIGNhc2UgXCJPYmplY3RQYXR0ZXJuXCI6XG4gICAgY2FzZSBcIkFycmF5UGF0dGVyblwiOlxuICAgIGNhc2UgXCJSZXN0RWxlbWVudFwiOlxuICAgIGNhc2UgXCJBc3NpZ25tZW50UGF0dGVyblwiOlxuICAgICAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KSByZXR1cm4gZXhwcjtcblxuICAgIGRlZmF1bHQ6XG4gICAgICByZXR1cm4gdGhpcy5kdW1teUlkZW50KCk7XG4gIH1cbn07XG5cbmxwLnBhcnNlRXhwcmVzc2lvbiA9IGZ1bmN0aW9uIChub0luKSB7XG4gIHZhciBzdGFydCA9IHRoaXMuc3RvcmVDdXJyZW50UG9zKCk7XG4gIHZhciBleHByID0gdGhpcy5wYXJzZU1heWJlQXNzaWduKG5vSW4pO1xuICBpZiAodGhpcy50b2sudHlwZSA9PT0gXy50b2tUeXBlcy5jb21tYSkge1xuICAgIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGVBdChzdGFydCk7XG4gICAgbm9kZS5leHByZXNzaW9ucyA9IFtleHByXTtcbiAgICB3aGlsZSAodGhpcy5lYXQoXy50b2tUeXBlcy5jb21tYSkpIG5vZGUuZXhwcmVzc2lvbnMucHVzaCh0aGlzLnBhcnNlTWF5YmVBc3NpZ24obm9JbikpO1xuICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJTZXF1ZW5jZUV4cHJlc3Npb25cIik7XG4gIH1cbiAgcmV0dXJuIGV4cHI7XG59O1xuXG5scC5wYXJzZVBhcmVuRXhwcmVzc2lvbiA9IGZ1bmN0aW9uICgpIHtcbiAgdGhpcy5wdXNoQ3goKTtcbiAgdGhpcy5leHBlY3QoXy50b2tUeXBlcy5wYXJlbkwpO1xuICB2YXIgdmFsID0gdGhpcy5wYXJzZUV4cHJlc3Npb24oKTtcbiAgdGhpcy5wb3BDeCgpO1xuICB0aGlzLmV4cGVjdChfLnRva1R5cGVzLnBhcmVuUik7XG4gIHJldHVybiB2YWw7XG59O1xuXG5scC5wYXJzZU1heWJlQXNzaWduID0gZnVuY3Rpb24gKG5vSW4pIHtcbiAgdmFyIHN0YXJ0ID0gdGhpcy5zdG9yZUN1cnJlbnRQb3MoKTtcbiAgdmFyIGxlZnQgPSB0aGlzLnBhcnNlTWF5YmVDb25kaXRpb25hbChub0luKTtcbiAgaWYgKHRoaXMudG9rLnR5cGUuaXNBc3NpZ24pIHtcbiAgICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlQXQoc3RhcnQpO1xuICAgIG5vZGUub3BlcmF0b3IgPSB0aGlzLnRvay52YWx1ZTtcbiAgICBub2RlLmxlZnQgPSB0aGlzLnRvay50eXBlID09PSBfLnRva1R5cGVzLmVxID8gdGhpcy50b0Fzc2lnbmFibGUobGVmdCkgOiB0aGlzLmNoZWNrTFZhbChsZWZ0KTtcbiAgICB0aGlzLm5leHQoKTtcbiAgICBub2RlLnJpZ2h0ID0gdGhpcy5wYXJzZU1heWJlQXNzaWduKG5vSW4pO1xuICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJBc3NpZ25tZW50RXhwcmVzc2lvblwiKTtcbiAgfVxuICByZXR1cm4gbGVmdDtcbn07XG5cbmxwLnBhcnNlTWF5YmVDb25kaXRpb25hbCA9IGZ1bmN0aW9uIChub0luKSB7XG4gIHZhciBzdGFydCA9IHRoaXMuc3RvcmVDdXJyZW50UG9zKCk7XG4gIHZhciBleHByID0gdGhpcy5wYXJzZUV4cHJPcHMobm9Jbik7XG4gIGlmICh0aGlzLmVhdChfLnRva1R5cGVzLnF1ZXN0aW9uKSkge1xuICAgIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGVBdChzdGFydCk7XG4gICAgbm9kZS50ZXN0ID0gZXhwcjtcbiAgICBub2RlLmNvbnNlcXVlbnQgPSB0aGlzLnBhcnNlTWF5YmVBc3NpZ24oKTtcbiAgICBub2RlLmFsdGVybmF0ZSA9IHRoaXMuZXhwZWN0KF8udG9rVHlwZXMuY29sb24pID8gdGhpcy5wYXJzZU1heWJlQXNzaWduKG5vSW4pIDogdGhpcy5kdW1teUlkZW50KCk7XG4gICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkNvbmRpdGlvbmFsRXhwcmVzc2lvblwiKTtcbiAgfVxuICByZXR1cm4gZXhwcjtcbn07XG5cbmxwLnBhcnNlRXhwck9wcyA9IGZ1bmN0aW9uIChub0luKSB7XG4gIHZhciBzdGFydCA9IHRoaXMuc3RvcmVDdXJyZW50UG9zKCk7XG4gIHZhciBpbmRlbnQgPSB0aGlzLmN1ckluZGVudCxcbiAgICAgIGxpbmUgPSB0aGlzLmN1ckxpbmVTdGFydDtcbiAgcmV0dXJuIHRoaXMucGFyc2VFeHByT3AodGhpcy5wYXJzZU1heWJlVW5hcnkobm9JbiksIHN0YXJ0LCAtMSwgbm9JbiwgaW5kZW50LCBsaW5lKTtcbn07XG5cbmxwLnBhcnNlRXhwck9wID0gZnVuY3Rpb24gKGxlZnQsIHN0YXJ0LCBtaW5QcmVjLCBub0luLCBpbmRlbnQsIGxpbmUpIHtcbiAgaWYgKHRoaXMuY3VyTGluZVN0YXJ0ICE9IGxpbmUgJiYgdGhpcy5jdXJJbmRlbnQgPCBpbmRlbnQgJiYgdGhpcy50b2tlblN0YXJ0c0xpbmUoKSkgcmV0dXJuIGxlZnQ7XG4gIHZhciBwcmVjID0gdGhpcy50b2sudHlwZS5iaW5vcDtcbiAgaWYgKHByZWMgIT0gbnVsbCAmJiAoIW5vSW4gfHwgdGhpcy50b2sudHlwZSAhPT0gXy50b2tUeXBlcy5faW4pKSB7XG4gICAgaWYgKHByZWMgPiBtaW5QcmVjKSB7XG4gICAgICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlQXQoc3RhcnQpO1xuICAgICAgbm9kZS5sZWZ0ID0gbGVmdDtcbiAgICAgIG5vZGUub3BlcmF0b3IgPSB0aGlzLnRvay52YWx1ZTtcbiAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgaWYgKHRoaXMuY3VyTGluZVN0YXJ0ICE9IGxpbmUgJiYgdGhpcy5jdXJJbmRlbnQgPCBpbmRlbnQgJiYgdGhpcy50b2tlblN0YXJ0c0xpbmUoKSkge1xuICAgICAgICBub2RlLnJpZ2h0ID0gdGhpcy5kdW1teUlkZW50KCk7XG4gICAgICB9IGVsc2Uge1xuICAgICAgICB2YXIgcmlnaHRTdGFydCA9IHRoaXMuc3RvcmVDdXJyZW50UG9zKCk7XG4gICAgICAgIG5vZGUucmlnaHQgPSB0aGlzLnBhcnNlRXhwck9wKHRoaXMucGFyc2VNYXliZVVuYXJ5KG5vSW4pLCByaWdodFN0YXJ0LCBwcmVjLCBub0luLCBpbmRlbnQsIGxpbmUpO1xuICAgICAgfVxuICAgICAgdGhpcy5maW5pc2hOb2RlKG5vZGUsIC8mJnxcXHxcXHwvLnRlc3Qobm9kZS5vcGVyYXRvcikgPyBcIkxvZ2ljYWxFeHByZXNzaW9uXCIgOiBcIkJpbmFyeUV4cHJlc3Npb25cIik7XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZUV4cHJPcChub2RlLCBzdGFydCwgbWluUHJlYywgbm9JbiwgaW5kZW50LCBsaW5lKTtcbiAgICB9XG4gIH1cbiAgcmV0dXJuIGxlZnQ7XG59O1xuXG5scC5wYXJzZU1heWJlVW5hcnkgPSBmdW5jdGlvbiAobm9Jbikge1xuICBpZiAodGhpcy50b2sudHlwZS5wcmVmaXgpIHtcbiAgICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCksXG4gICAgICAgIHVwZGF0ZSA9IHRoaXMudG9rLnR5cGUgPT09IF8udG9rVHlwZXMuaW5jRGVjO1xuICAgIG5vZGUub3BlcmF0b3IgPSB0aGlzLnRvay52YWx1ZTtcbiAgICBub2RlLnByZWZpeCA9IHRydWU7XG4gICAgdGhpcy5uZXh0KCk7XG4gICAgbm9kZS5hcmd1bWVudCA9IHRoaXMucGFyc2VNYXliZVVuYXJ5KG5vSW4pO1xuICAgIGlmICh1cGRhdGUpIG5vZGUuYXJndW1lbnQgPSB0aGlzLmNoZWNrTFZhbChub2RlLmFyZ3VtZW50KTtcbiAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIHVwZGF0ZSA/IFwiVXBkYXRlRXhwcmVzc2lvblwiIDogXCJVbmFyeUV4cHJlc3Npb25cIik7XG4gIH0gZWxzZSBpZiAodGhpcy50b2sudHlwZSA9PT0gXy50b2tUeXBlcy5lbGxpcHNpcykge1xuICAgIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgICB0aGlzLm5leHQoKTtcbiAgICBub2RlLmFyZ3VtZW50ID0gdGhpcy5wYXJzZU1heWJlVW5hcnkobm9Jbik7XG4gICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIlNwcmVhZEVsZW1lbnRcIik7XG4gIH1cbiAgdmFyIHN0YXJ0ID0gdGhpcy5zdG9yZUN1cnJlbnRQb3MoKTtcbiAgdmFyIGV4cHIgPSB0aGlzLnBhcnNlRXhwclN1YnNjcmlwdHMoKTtcbiAgd2hpbGUgKHRoaXMudG9rLnR5cGUucG9zdGZpeCAmJiAhdGhpcy5jYW5JbnNlcnRTZW1pY29sb24oKSkge1xuICAgIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGVBdChzdGFydCk7XG4gICAgbm9kZS5vcGVyYXRvciA9IHRoaXMudG9rLnZhbHVlO1xuICAgIG5vZGUucHJlZml4ID0gZmFsc2U7XG4gICAgbm9kZS5hcmd1bWVudCA9IHRoaXMuY2hlY2tMVmFsKGV4cHIpO1xuICAgIHRoaXMubmV4dCgpO1xuICAgIGV4cHIgPSB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJVcGRhdGVFeHByZXNzaW9uXCIpO1xuICB9XG4gIHJldHVybiBleHByO1xufTtcblxubHAucGFyc2VFeHByU3Vic2NyaXB0cyA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIHN0YXJ0ID0gdGhpcy5zdG9yZUN1cnJlbnRQb3MoKTtcbiAgcmV0dXJuIHRoaXMucGFyc2VTdWJzY3JpcHRzKHRoaXMucGFyc2VFeHByQXRvbSgpLCBzdGFydCwgZmFsc2UsIHRoaXMuY3VySW5kZW50LCB0aGlzLmN1ckxpbmVTdGFydCk7XG59O1xuXG5scC5wYXJzZVN1YnNjcmlwdHMgPSBmdW5jdGlvbiAoYmFzZSwgc3RhcnQsIG5vQ2FsbHMsIHN0YXJ0SW5kZW50LCBsaW5lKSB7XG4gIGZvciAoOzspIHtcbiAgICBpZiAodGhpcy5jdXJMaW5lU3RhcnQgIT0gbGluZSAmJiB0aGlzLmN1ckluZGVudCA8PSBzdGFydEluZGVudCAmJiB0aGlzLnRva2VuU3RhcnRzTGluZSgpKSB7XG4gICAgICBpZiAodGhpcy50b2sudHlwZSA9PSBfLnRva1R5cGVzLmRvdCAmJiB0aGlzLmN1ckluZGVudCA9PSBzdGFydEluZGVudCkgLS1zdGFydEluZGVudDtlbHNlIHJldHVybiBiYXNlO1xuICAgIH1cblxuICAgIGlmICh0aGlzLmVhdChfLnRva1R5cGVzLmRvdCkpIHtcbiAgICAgIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGVBdChzdGFydCk7XG4gICAgICBub2RlLm9iamVjdCA9IGJhc2U7XG4gICAgICBpZiAodGhpcy5jdXJMaW5lU3RhcnQgIT0gbGluZSAmJiB0aGlzLmN1ckluZGVudCA8PSBzdGFydEluZGVudCAmJiB0aGlzLnRva2VuU3RhcnRzTGluZSgpKSBub2RlLnByb3BlcnR5ID0gdGhpcy5kdW1teUlkZW50KCk7ZWxzZSBub2RlLnByb3BlcnR5ID0gdGhpcy5wYXJzZVByb3BlcnR5QWNjZXNzb3IoKSB8fCB0aGlzLmR1bW15SWRlbnQoKTtcbiAgICAgIG5vZGUuY29tcHV0ZWQgPSBmYWxzZTtcbiAgICAgIGJhc2UgPSB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJNZW1iZXJFeHByZXNzaW9uXCIpO1xuICAgIH0gZWxzZSBpZiAodGhpcy50b2sudHlwZSA9PSBfLnRva1R5cGVzLmJyYWNrZXRMKSB7XG4gICAgICB0aGlzLnB1c2hDeCgpO1xuICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlQXQoc3RhcnQpO1xuICAgICAgbm9kZS5vYmplY3QgPSBiYXNlO1xuICAgICAgbm9kZS5wcm9wZXJ0eSA9IHRoaXMucGFyc2VFeHByZXNzaW9uKCk7XG4gICAgICBub2RlLmNvbXB1dGVkID0gdHJ1ZTtcbiAgICAgIHRoaXMucG9wQ3goKTtcbiAgICAgIHRoaXMuZXhwZWN0KF8udG9rVHlwZXMuYnJhY2tldFIpO1xuICAgICAgYmFzZSA9IHRoaXMuZmluaXNoTm9kZShub2RlLCBcIk1lbWJlckV4cHJlc3Npb25cIik7XG4gICAgfSBlbHNlIGlmICghbm9DYWxscyAmJiB0aGlzLnRvay50eXBlID09IF8udG9rVHlwZXMucGFyZW5MKSB7XG4gICAgICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlQXQoc3RhcnQpO1xuICAgICAgbm9kZS5jYWxsZWUgPSBiYXNlO1xuICAgICAgbm9kZS5hcmd1bWVudHMgPSB0aGlzLnBhcnNlRXhwckxpc3QoXy50b2tUeXBlcy5wYXJlblIpO1xuICAgICAgYmFzZSA9IHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkNhbGxFeHByZXNzaW9uXCIpO1xuICAgIH0gZWxzZSBpZiAodGhpcy50b2sudHlwZSA9PSBfLnRva1R5cGVzLmJhY2tRdW90ZSkge1xuICAgICAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZUF0KHN0YXJ0KTtcbiAgICAgIG5vZGUudGFnID0gYmFzZTtcbiAgICAgIG5vZGUucXVhc2kgPSB0aGlzLnBhcnNlVGVtcGxhdGUoKTtcbiAgICAgIGJhc2UgPSB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJUYWdnZWRUZW1wbGF0ZUV4cHJlc3Npb25cIik7XG4gICAgfSBlbHNlIHtcbiAgICAgIHJldHVybiBiYXNlO1xuICAgIH1cbiAgfVxufTtcblxubHAucGFyc2VFeHByQXRvbSA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIG5vZGUgPSB1bmRlZmluZWQ7XG4gIHN3aXRjaCAodGhpcy50b2sudHlwZSkge1xuICAgIGNhc2UgXy50b2tUeXBlcy5fdGhpczpcbiAgICBjYXNlIF8udG9rVHlwZXMuX3N1cGVyOlxuICAgICAgdmFyIHR5cGUgPSB0aGlzLnRvay50eXBlID09PSBfLnRva1R5cGVzLl90aGlzID8gXCJUaGlzRXhwcmVzc2lvblwiIDogXCJTdXBlclwiO1xuICAgICAgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gICAgICB0aGlzLm5leHQoKTtcbiAgICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgdHlwZSk7XG5cbiAgICBjYXNlIF8udG9rVHlwZXMubmFtZTpcbiAgICAgIHZhciBzdGFydCA9IHRoaXMuc3RvcmVDdXJyZW50UG9zKCk7XG4gICAgICB2YXIgaWQgPSB0aGlzLnBhcnNlSWRlbnQoKTtcbiAgICAgIHJldHVybiB0aGlzLmVhdChfLnRva1R5cGVzLmFycm93KSA/IHRoaXMucGFyc2VBcnJvd0V4cHJlc3Npb24odGhpcy5zdGFydE5vZGVBdChzdGFydCksIFtpZF0pIDogaWQ7XG5cbiAgICBjYXNlIF8udG9rVHlwZXMucmVnZXhwOlxuICAgICAgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gICAgICB2YXIgdmFsID0gdGhpcy50b2sudmFsdWU7XG4gICAgICBub2RlLnJlZ2V4ID0geyBwYXR0ZXJuOiB2YWwucGF0dGVybiwgZmxhZ3M6IHZhbC5mbGFncyB9O1xuICAgICAgbm9kZS52YWx1ZSA9IHZhbC52YWx1ZTtcbiAgICAgIG5vZGUucmF3ID0gdGhpcy5pbnB1dC5zbGljZSh0aGlzLnRvay5zdGFydCwgdGhpcy50b2suZW5kKTtcbiAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkxpdGVyYWxcIik7XG5cbiAgICBjYXNlIF8udG9rVHlwZXMubnVtOmNhc2UgXy50b2tUeXBlcy5zdHJpbmc6XG4gICAgICBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgICAgIG5vZGUudmFsdWUgPSB0aGlzLnRvay52YWx1ZTtcbiAgICAgIG5vZGUucmF3ID0gdGhpcy5pbnB1dC5zbGljZSh0aGlzLnRvay5zdGFydCwgdGhpcy50b2suZW5kKTtcbiAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkxpdGVyYWxcIik7XG5cbiAgICBjYXNlIF8udG9rVHlwZXMuX251bGw6Y2FzZSBfLnRva1R5cGVzLl90cnVlOmNhc2UgXy50b2tUeXBlcy5fZmFsc2U6XG4gICAgICBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgICAgIG5vZGUudmFsdWUgPSB0aGlzLnRvay50eXBlID09PSBfLnRva1R5cGVzLl9udWxsID8gbnVsbCA6IHRoaXMudG9rLnR5cGUgPT09IF8udG9rVHlwZXMuX3RydWU7XG4gICAgICBub2RlLnJhdyA9IHRoaXMudG9rLnR5cGUua2V5d29yZDtcbiAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkxpdGVyYWxcIik7XG5cbiAgICBjYXNlIF8udG9rVHlwZXMucGFyZW5MOlxuICAgICAgdmFyIHBhcmVuU3RhcnQgPSB0aGlzLnN0b3JlQ3VycmVudFBvcygpO1xuICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICB2YXIgaW5uZXIgPSB0aGlzLnBhcnNlRXhwcmVzc2lvbigpO1xuICAgICAgdGhpcy5leHBlY3QoXy50b2tUeXBlcy5wYXJlblIpO1xuICAgICAgaWYgKHRoaXMuZWF0KF8udG9rVHlwZXMuYXJyb3cpKSB7XG4gICAgICAgIHJldHVybiB0aGlzLnBhcnNlQXJyb3dFeHByZXNzaW9uKHRoaXMuc3RhcnROb2RlQXQocGFyZW5TdGFydCksIGlubmVyLmV4cHJlc3Npb25zIHx8IChfcGFyc2V1dGlsLmlzRHVtbXkoaW5uZXIpID8gW10gOiBbaW5uZXJdKSk7XG4gICAgICB9XG4gICAgICBpZiAodGhpcy5vcHRpb25zLnByZXNlcnZlUGFyZW5zKSB7XG4gICAgICAgIHZhciBwYXIgPSB0aGlzLnN0YXJ0Tm9kZUF0KHBhcmVuU3RhcnQpO1xuICAgICAgICBwYXIuZXhwcmVzc2lvbiA9IGlubmVyO1xuICAgICAgICBpbm5lciA9IHRoaXMuZmluaXNoTm9kZShwYXIsIFwiUGFyZW50aGVzaXplZEV4cHJlc3Npb25cIik7XG4gICAgICB9XG4gICAgICByZXR1cm4gaW5uZXI7XG5cbiAgICBjYXNlIF8udG9rVHlwZXMuYnJhY2tldEw6XG4gICAgICBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgICAgIG5vZGUuZWxlbWVudHMgPSB0aGlzLnBhcnNlRXhwckxpc3QoXy50b2tUeXBlcy5icmFja2V0UiwgdHJ1ZSk7XG4gICAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiQXJyYXlFeHByZXNzaW9uXCIpO1xuXG4gICAgY2FzZSBfLnRva1R5cGVzLmJyYWNlTDpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlT2JqKCk7XG5cbiAgICBjYXNlIF8udG9rVHlwZXMuX2NsYXNzOlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VDbGFzcygpO1xuXG4gICAgY2FzZSBfLnRva1R5cGVzLl9mdW5jdGlvbjpcbiAgICAgIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZUZ1bmN0aW9uKG5vZGUsIGZhbHNlKTtcblxuICAgIGNhc2UgXy50b2tUeXBlcy5fbmV3OlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VOZXcoKTtcblxuICAgIGNhc2UgXy50b2tUeXBlcy5feWllbGQ6XG4gICAgICBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgaWYgKHRoaXMuc2VtaWNvbG9uKCkgfHwgdGhpcy5jYW5JbnNlcnRTZW1pY29sb24oKSB8fCB0aGlzLnRvay50eXBlICE9IF8udG9rVHlwZXMuc3RhciAmJiAhdGhpcy50b2sudHlwZS5zdGFydHNFeHByKSB7XG4gICAgICAgIG5vZGUuZGVsZWdhdGUgPSBmYWxzZTtcbiAgICAgICAgbm9kZS5hcmd1bWVudCA9IG51bGw7XG4gICAgICB9IGVsc2Uge1xuICAgICAgICBub2RlLmRlbGVnYXRlID0gdGhpcy5lYXQoXy50b2tUeXBlcy5zdGFyKTtcbiAgICAgICAgbm9kZS5hcmd1bWVudCA9IHRoaXMucGFyc2VNYXliZUFzc2lnbigpO1xuICAgICAgfVxuICAgICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIllpZWxkRXhwcmVzc2lvblwiKTtcblxuICAgIGNhc2UgXy50b2tUeXBlcy5iYWNrUXVvdGU6XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZVRlbXBsYXRlKCk7XG5cbiAgICBkZWZhdWx0OlxuICAgICAgcmV0dXJuIHRoaXMuZHVtbXlJZGVudCgpO1xuICB9XG59O1xuXG5scC5wYXJzZU5ldyA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpLFxuICAgICAgc3RhcnRJbmRlbnQgPSB0aGlzLmN1ckluZGVudCxcbiAgICAgIGxpbmUgPSB0aGlzLmN1ckxpbmVTdGFydDtcbiAgdmFyIG1ldGEgPSB0aGlzLnBhcnNlSWRlbnQodHJ1ZSk7XG4gIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNiAmJiB0aGlzLmVhdChfLnRva1R5cGVzLmRvdCkpIHtcbiAgICBub2RlLm1ldGEgPSBtZXRhO1xuICAgIG5vZGUucHJvcGVydHkgPSB0aGlzLnBhcnNlSWRlbnQodHJ1ZSk7XG4gICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIk1ldGFQcm9wZXJ0eVwiKTtcbiAgfVxuICB2YXIgc3RhcnQgPSB0aGlzLnN0b3JlQ3VycmVudFBvcygpO1xuICBub2RlLmNhbGxlZSA9IHRoaXMucGFyc2VTdWJzY3JpcHRzKHRoaXMucGFyc2VFeHByQXRvbSgpLCBzdGFydCwgdHJ1ZSwgc3RhcnRJbmRlbnQsIGxpbmUpO1xuICBpZiAodGhpcy50b2sudHlwZSA9PSBfLnRva1R5cGVzLnBhcmVuTCkge1xuICAgIG5vZGUuYXJndW1lbnRzID0gdGhpcy5wYXJzZUV4cHJMaXN0KF8udG9rVHlwZXMucGFyZW5SKTtcbiAgfSBlbHNlIHtcbiAgICBub2RlLmFyZ3VtZW50cyA9IFtdO1xuICB9XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJOZXdFeHByZXNzaW9uXCIpO1xufTtcblxubHAucGFyc2VUZW1wbGF0ZUVsZW1lbnQgPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBlbGVtID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgZWxlbS52YWx1ZSA9IHtcbiAgICByYXc6IHRoaXMuaW5wdXQuc2xpY2UodGhpcy50b2suc3RhcnQsIHRoaXMudG9rLmVuZCkucmVwbGFjZSgvXFxyXFxuPy9nLCAnXFxuJyksXG4gICAgY29va2VkOiB0aGlzLnRvay52YWx1ZVxuICB9O1xuICB0aGlzLm5leHQoKTtcbiAgZWxlbS50YWlsID0gdGhpcy50b2sudHlwZSA9PT0gXy50b2tUeXBlcy5iYWNrUXVvdGU7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUoZWxlbSwgXCJUZW1wbGF0ZUVsZW1lbnRcIik7XG59O1xuXG5scC5wYXJzZVRlbXBsYXRlID0gZnVuY3Rpb24gKCkge1xuICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gIHRoaXMubmV4dCgpO1xuICBub2RlLmV4cHJlc3Npb25zID0gW107XG4gIHZhciBjdXJFbHQgPSB0aGlzLnBhcnNlVGVtcGxhdGVFbGVtZW50KCk7XG4gIG5vZGUucXVhc2lzID0gW2N1ckVsdF07XG4gIHdoaWxlICghY3VyRWx0LnRhaWwpIHtcbiAgICB0aGlzLm5leHQoKTtcbiAgICBub2RlLmV4cHJlc3Npb25zLnB1c2godGhpcy5wYXJzZUV4cHJlc3Npb24oKSk7XG4gICAgaWYgKHRoaXMuZXhwZWN0KF8udG9rVHlwZXMuYnJhY2VSKSkge1xuICAgICAgY3VyRWx0ID0gdGhpcy5wYXJzZVRlbXBsYXRlRWxlbWVudCgpO1xuICAgIH0gZWxzZSB7XG4gICAgICBjdXJFbHQgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICAgICAgY3VyRWx0LnZhbHVlID0geyBjb29rZWQ6ICcnLCByYXc6ICcnIH07XG4gICAgICBjdXJFbHQudGFpbCA9IHRydWU7XG4gICAgfVxuICAgIG5vZGUucXVhc2lzLnB1c2goY3VyRWx0KTtcbiAgfVxuICB0aGlzLmV4cGVjdChfLnRva1R5cGVzLmJhY2tRdW90ZSk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJUZW1wbGF0ZUxpdGVyYWxcIik7XG59O1xuXG5scC5wYXJzZU9iaiA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICBub2RlLnByb3BlcnRpZXMgPSBbXTtcbiAgdGhpcy5wdXNoQ3goKTtcbiAgdmFyIGluZGVudCA9IHRoaXMuY3VySW5kZW50ICsgMSxcbiAgICAgIGxpbmUgPSB0aGlzLmN1ckxpbmVTdGFydDtcbiAgdGhpcy5lYXQoXy50b2tUeXBlcy5icmFjZUwpO1xuICBpZiAodGhpcy5jdXJJbmRlbnQgKyAxIDwgaW5kZW50KSB7XG4gICAgaW5kZW50ID0gdGhpcy5jdXJJbmRlbnQ7bGluZSA9IHRoaXMuY3VyTGluZVN0YXJ0O1xuICB9XG4gIHdoaWxlICghdGhpcy5jbG9zZXMoXy50b2tUeXBlcy5icmFjZVIsIGluZGVudCwgbGluZSkpIHtcbiAgICB2YXIgcHJvcCA9IHRoaXMuc3RhcnROb2RlKCksXG4gICAgICAgIGlzR2VuZXJhdG9yID0gdW5kZWZpbmVkLFxuICAgICAgICBzdGFydCA9IHVuZGVmaW5lZDtcbiAgICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYpIHtcbiAgICAgIHN0YXJ0ID0gdGhpcy5zdG9yZUN1cnJlbnRQb3MoKTtcbiAgICAgIHByb3AubWV0aG9kID0gZmFsc2U7XG4gICAgICBwcm9wLnNob3J0aGFuZCA9IGZhbHNlO1xuICAgICAgaXNHZW5lcmF0b3IgPSB0aGlzLmVhdChfLnRva1R5cGVzLnN0YXIpO1xuICAgIH1cbiAgICB0aGlzLnBhcnNlUHJvcGVydHlOYW1lKHByb3ApO1xuICAgIGlmIChfcGFyc2V1dGlsLmlzRHVtbXkocHJvcC5rZXkpKSB7XG4gICAgICBpZiAoX3BhcnNldXRpbC5pc0R1bW15KHRoaXMucGFyc2VNYXliZUFzc2lnbigpKSkgdGhpcy5uZXh0KCk7dGhpcy5lYXQoXy50b2tUeXBlcy5jb21tYSk7Y29udGludWU7XG4gICAgfVxuICAgIGlmICh0aGlzLmVhdChfLnRva1R5cGVzLmNvbG9uKSkge1xuICAgICAgcHJvcC5raW5kID0gXCJpbml0XCI7XG4gICAgICBwcm9wLnZhbHVlID0gdGhpcy5wYXJzZU1heWJlQXNzaWduKCk7XG4gICAgfSBlbHNlIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNiAmJiAodGhpcy50b2sudHlwZSA9PT0gXy50b2tUeXBlcy5wYXJlbkwgfHwgdGhpcy50b2sudHlwZSA9PT0gXy50b2tUeXBlcy5icmFjZUwpKSB7XG4gICAgICBwcm9wLmtpbmQgPSBcImluaXRcIjtcbiAgICAgIHByb3AubWV0aG9kID0gdHJ1ZTtcbiAgICAgIHByb3AudmFsdWUgPSB0aGlzLnBhcnNlTWV0aG9kKGlzR2VuZXJhdG9yKTtcbiAgICB9IGVsc2UgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA1ICYmIHByb3Aua2V5LnR5cGUgPT09IFwiSWRlbnRpZmllclwiICYmICFwcm9wLmNvbXB1dGVkICYmIChwcm9wLmtleS5uYW1lID09PSBcImdldFwiIHx8IHByb3Aua2V5Lm5hbWUgPT09IFwic2V0XCIpICYmICh0aGlzLnRvay50eXBlICE9IF8udG9rVHlwZXMuY29tbWEgJiYgdGhpcy50b2sudHlwZSAhPSBfLnRva1R5cGVzLmJyYWNlUikpIHtcbiAgICAgIHByb3Aua2luZCA9IHByb3Aua2V5Lm5hbWU7XG4gICAgICB0aGlzLnBhcnNlUHJvcGVydHlOYW1lKHByb3ApO1xuICAgICAgcHJvcC52YWx1ZSA9IHRoaXMucGFyc2VNZXRob2QoZmFsc2UpO1xuICAgIH0gZWxzZSB7XG4gICAgICBwcm9wLmtpbmQgPSBcImluaXRcIjtcbiAgICAgIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNikge1xuICAgICAgICBpZiAodGhpcy5lYXQoXy50b2tUeXBlcy5lcSkpIHtcbiAgICAgICAgICB2YXIgYXNzaWduID0gdGhpcy5zdGFydE5vZGVBdChzdGFydCk7XG4gICAgICAgICAgYXNzaWduLm9wZXJhdG9yID0gXCI9XCI7XG4gICAgICAgICAgYXNzaWduLmxlZnQgPSBwcm9wLmtleTtcbiAgICAgICAgICBhc3NpZ24ucmlnaHQgPSB0aGlzLnBhcnNlTWF5YmVBc3NpZ24oKTtcbiAgICAgICAgICBwcm9wLnZhbHVlID0gdGhpcy5maW5pc2hOb2RlKGFzc2lnbiwgXCJBc3NpZ25tZW50RXhwcmVzc2lvblwiKTtcbiAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICBwcm9wLnZhbHVlID0gcHJvcC5rZXk7XG4gICAgICAgIH1cbiAgICAgIH0gZWxzZSB7XG4gICAgICAgIHByb3AudmFsdWUgPSB0aGlzLmR1bW15SWRlbnQoKTtcbiAgICAgIH1cbiAgICAgIHByb3Auc2hvcnRoYW5kID0gdHJ1ZTtcbiAgICB9XG4gICAgbm9kZS5wcm9wZXJ0aWVzLnB1c2godGhpcy5maW5pc2hOb2RlKHByb3AsIFwiUHJvcGVydHlcIikpO1xuICAgIHRoaXMuZWF0KF8udG9rVHlwZXMuY29tbWEpO1xuICB9XG4gIHRoaXMucG9wQ3goKTtcbiAgaWYgKCF0aGlzLmVhdChfLnRva1R5cGVzLmJyYWNlUikpIHtcbiAgICAvLyBJZiB0aGVyZSBpcyBubyBjbG9zaW5nIGJyYWNlLCBtYWtlIHRoZSBub2RlIHNwYW4gdG8gdGhlIHN0YXJ0XG4gICAgLy8gb2YgdGhlIG5leHQgdG9rZW4gKHRoaXMgaXMgdXNlZnVsIGZvciBUZXJuKVxuICAgIHRoaXMubGFzdC5lbmQgPSB0aGlzLnRvay5zdGFydDtcbiAgICBpZiAodGhpcy5vcHRpb25zLmxvY2F0aW9ucykgdGhpcy5sYXN0LmxvYy5lbmQgPSB0aGlzLnRvay5sb2Muc3RhcnQ7XG4gIH1cbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIk9iamVjdEV4cHJlc3Npb25cIik7XG59O1xuXG5scC5wYXJzZVByb3BlcnR5TmFtZSA9IGZ1bmN0aW9uIChwcm9wKSB7XG4gIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNikge1xuICAgIGlmICh0aGlzLmVhdChfLnRva1R5cGVzLmJyYWNrZXRMKSkge1xuICAgICAgcHJvcC5jb21wdXRlZCA9IHRydWU7XG4gICAgICBwcm9wLmtleSA9IHRoaXMucGFyc2VFeHByZXNzaW9uKCk7XG4gICAgICB0aGlzLmV4cGVjdChfLnRva1R5cGVzLmJyYWNrZXRSKTtcbiAgICAgIHJldHVybjtcbiAgICB9IGVsc2Uge1xuICAgICAgcHJvcC5jb21wdXRlZCA9IGZhbHNlO1xuICAgIH1cbiAgfVxuICB2YXIga2V5ID0gdGhpcy50b2sudHlwZSA9PT0gXy50b2tUeXBlcy5udW0gfHwgdGhpcy50b2sudHlwZSA9PT0gXy50b2tUeXBlcy5zdHJpbmcgPyB0aGlzLnBhcnNlRXhwckF0b20oKSA6IHRoaXMucGFyc2VJZGVudCgpO1xuICBwcm9wLmtleSA9IGtleSB8fCB0aGlzLmR1bW15SWRlbnQoKTtcbn07XG5cbmxwLnBhcnNlUHJvcGVydHlBY2Nlc3NvciA9IGZ1bmN0aW9uICgpIHtcbiAgaWYgKHRoaXMudG9rLnR5cGUgPT09IF8udG9rVHlwZXMubmFtZSB8fCB0aGlzLnRvay50eXBlLmtleXdvcmQpIHJldHVybiB0aGlzLnBhcnNlSWRlbnQoKTtcbn07XG5cbmxwLnBhcnNlSWRlbnQgPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBuYW1lID0gdGhpcy50b2sudHlwZSA9PT0gXy50b2tUeXBlcy5uYW1lID8gdGhpcy50b2sudmFsdWUgOiB0aGlzLnRvay50eXBlLmtleXdvcmQ7XG4gIGlmICghbmFtZSkgcmV0dXJuIHRoaXMuZHVtbXlJZGVudCgpO1xuICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gIHRoaXMubmV4dCgpO1xuICBub2RlLm5hbWUgPSBuYW1lO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiSWRlbnRpZmllclwiKTtcbn07XG5cbmxwLmluaXRGdW5jdGlvbiA9IGZ1bmN0aW9uIChub2RlKSB7XG4gIG5vZGUuaWQgPSBudWxsO1xuICBub2RlLnBhcmFtcyA9IFtdO1xuICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYpIHtcbiAgICBub2RlLmdlbmVyYXRvciA9IGZhbHNlO1xuICAgIG5vZGUuZXhwcmVzc2lvbiA9IGZhbHNlO1xuICB9XG59O1xuXG4vLyBDb252ZXJ0IGV4aXN0aW5nIGV4cHJlc3Npb24gYXRvbSB0byBhc3NpZ25hYmxlIHBhdHRlcm5cbi8vIGlmIHBvc3NpYmxlLlxuXG5scC50b0Fzc2lnbmFibGUgPSBmdW5jdGlvbiAobm9kZSwgYmluZGluZykge1xuICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYgJiYgbm9kZSkge1xuICAgIHN3aXRjaCAobm9kZS50eXBlKSB7XG4gICAgICBjYXNlIFwiT2JqZWN0RXhwcmVzc2lvblwiOlxuICAgICAgICBub2RlLnR5cGUgPSBcIk9iamVjdFBhdHRlcm5cIjtcbiAgICAgICAgdmFyIHByb3BzID0gbm9kZS5wcm9wZXJ0aWVzO1xuICAgICAgICBmb3IgKHZhciBpID0gMDsgaSA8IHByb3BzLmxlbmd0aDsgaSsrKSB7XG4gICAgICAgICAgdGhpcy50b0Fzc2lnbmFibGUocHJvcHNbaV0udmFsdWUsIGJpbmRpbmcpO1xuICAgICAgICB9YnJlYWs7XG5cbiAgICAgIGNhc2UgXCJBcnJheUV4cHJlc3Npb25cIjpcbiAgICAgICAgbm9kZS50eXBlID0gXCJBcnJheVBhdHRlcm5cIjtcbiAgICAgICAgdGhpcy50b0Fzc2lnbmFibGVMaXN0KG5vZGUuZWxlbWVudHMsIGJpbmRpbmcpO1xuICAgICAgICBicmVhaztcblxuICAgICAgY2FzZSBcIlNwcmVhZEVsZW1lbnRcIjpcbiAgICAgICAgbm9kZS50eXBlID0gXCJSZXN0RWxlbWVudFwiO1xuICAgICAgICBub2RlLmFyZ3VtZW50ID0gdGhpcy50b0Fzc2lnbmFibGUobm9kZS5hcmd1bWVudCwgYmluZGluZyk7XG4gICAgICAgIGJyZWFrO1xuXG4gICAgICBjYXNlIFwiQXNzaWdubWVudEV4cHJlc3Npb25cIjpcbiAgICAgICAgbm9kZS50eXBlID0gXCJBc3NpZ25tZW50UGF0dGVyblwiO1xuICAgICAgICBkZWxldGUgbm9kZS5vcGVyYXRvcjtcbiAgICAgICAgYnJlYWs7XG4gICAgfVxuICB9XG4gIHJldHVybiB0aGlzLmNoZWNrTFZhbChub2RlLCBiaW5kaW5nKTtcbn07XG5cbmxwLnRvQXNzaWduYWJsZUxpc3QgPSBmdW5jdGlvbiAoZXhwckxpc3QsIGJpbmRpbmcpIHtcbiAgZm9yICh2YXIgaSA9IDA7IGkgPCBleHByTGlzdC5sZW5ndGg7IGkrKykge1xuICAgIGV4cHJMaXN0W2ldID0gdGhpcy50b0Fzc2lnbmFibGUoZXhwckxpc3RbaV0sIGJpbmRpbmcpO1xuICB9cmV0dXJuIGV4cHJMaXN0O1xufTtcblxubHAucGFyc2VGdW5jdGlvblBhcmFtcyA9IGZ1bmN0aW9uIChwYXJhbXMpIHtcbiAgcGFyYW1zID0gdGhpcy5wYXJzZUV4cHJMaXN0KF8udG9rVHlwZXMucGFyZW5SKTtcbiAgcmV0dXJuIHRoaXMudG9Bc3NpZ25hYmxlTGlzdChwYXJhbXMsIHRydWUpO1xufTtcblxubHAucGFyc2VNZXRob2QgPSBmdW5jdGlvbiAoaXNHZW5lcmF0b3IpIHtcbiAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICB0aGlzLmluaXRGdW5jdGlvbihub2RlKTtcbiAgbm9kZS5wYXJhbXMgPSB0aGlzLnBhcnNlRnVuY3Rpb25QYXJhbXMoKTtcbiAgbm9kZS5nZW5lcmF0b3IgPSBpc0dlbmVyYXRvciB8fCBmYWxzZTtcbiAgbm9kZS5leHByZXNzaW9uID0gdGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYgJiYgdGhpcy50b2sudHlwZSAhPT0gXy50b2tUeXBlcy5icmFjZUw7XG4gIG5vZGUuYm9keSA9IG5vZGUuZXhwcmVzc2lvbiA/IHRoaXMucGFyc2VNYXliZUFzc2lnbigpIDogdGhpcy5wYXJzZUJsb2NrKCk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJGdW5jdGlvbkV4cHJlc3Npb25cIik7XG59O1xuXG5scC5wYXJzZUFycm93RXhwcmVzc2lvbiA9IGZ1bmN0aW9uIChub2RlLCBwYXJhbXMpIHtcbiAgdGhpcy5pbml0RnVuY3Rpb24obm9kZSk7XG4gIG5vZGUucGFyYW1zID0gdGhpcy50b0Fzc2lnbmFibGVMaXN0KHBhcmFtcywgdHJ1ZSk7XG4gIG5vZGUuZXhwcmVzc2lvbiA9IHRoaXMudG9rLnR5cGUgIT09IF8udG9rVHlwZXMuYnJhY2VMO1xuICBub2RlLmJvZHkgPSBub2RlLmV4cHJlc3Npb24gPyB0aGlzLnBhcnNlTWF5YmVBc3NpZ24oKSA6IHRoaXMucGFyc2VCbG9jaygpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiQXJyb3dGdW5jdGlvbkV4cHJlc3Npb25cIik7XG59O1xuXG5scC5wYXJzZUV4cHJMaXN0ID0gZnVuY3Rpb24gKGNsb3NlLCBhbGxvd0VtcHR5KSB7XG4gIHRoaXMucHVzaEN4KCk7XG4gIHZhciBpbmRlbnQgPSB0aGlzLmN1ckluZGVudCxcbiAgICAgIGxpbmUgPSB0aGlzLmN1ckxpbmVTdGFydCxcbiAgICAgIGVsdHMgPSBbXTtcbiAgdGhpcy5uZXh0KCk7IC8vIE9wZW5pbmcgYnJhY2tldFxuICB3aGlsZSAoIXRoaXMuY2xvc2VzKGNsb3NlLCBpbmRlbnQgKyAxLCBsaW5lKSkge1xuICAgIGlmICh0aGlzLmVhdChfLnRva1R5cGVzLmNvbW1hKSkge1xuICAgICAgZWx0cy5wdXNoKGFsbG93RW1wdHkgPyBudWxsIDogdGhpcy5kdW1teUlkZW50KCkpO1xuICAgICAgY29udGludWU7XG4gICAgfVxuICAgIHZhciBlbHQgPSB0aGlzLnBhcnNlTWF5YmVBc3NpZ24oKTtcbiAgICBpZiAoX3BhcnNldXRpbC5pc0R1bW15KGVsdCkpIHtcbiAgICAgIGlmICh0aGlzLmNsb3NlcyhjbG9zZSwgaW5kZW50LCBsaW5lKSkgYnJlYWs7XG4gICAgICB0aGlzLm5leHQoKTtcbiAgICB9IGVsc2Uge1xuICAgICAgZWx0cy5wdXNoKGVsdCk7XG4gICAgfVxuICAgIHRoaXMuZWF0KF8udG9rVHlwZXMuY29tbWEpO1xuICB9XG4gIHRoaXMucG9wQ3goKTtcbiAgaWYgKCF0aGlzLmVhdChjbG9zZSkpIHtcbiAgICAvLyBJZiB0aGVyZSBpcyBubyBjbG9zaW5nIGJyYWNlLCBtYWtlIHRoZSBub2RlIHNwYW4gdG8gdGhlIHN0YXJ0XG4gICAgLy8gb2YgdGhlIG5leHQgdG9rZW4gKHRoaXMgaXMgdXNlZnVsIGZvciBUZXJuKVxuICAgIHRoaXMubGFzdC5lbmQgPSB0aGlzLnRvay5zdGFydDtcbiAgICBpZiAodGhpcy5vcHRpb25zLmxvY2F0aW9ucykgdGhpcy5sYXN0LmxvYy5lbmQgPSB0aGlzLnRvay5sb2Muc3RhcnQ7XG4gIH1cbiAgcmV0dXJuIGVsdHM7XG59O1xuXG59LHtcIi4uXCI6MixcIi4vcGFyc2V1dGlsXCI6NSxcIi4vc3RhdGVcIjo2fV0sNDpbZnVuY3Rpb24oX2RlcmVxXyxtb2R1bGUsZXhwb3J0cyl7XG4vLyBBY29ybjogTG9vc2UgcGFyc2VyXG4vL1xuLy8gVGhpcyBtb2R1bGUgcHJvdmlkZXMgYW4gYWx0ZXJuYXRpdmUgcGFyc2VyIChgcGFyc2VfZGFtbWl0YCkgdGhhdFxuLy8gZXhwb3NlcyB0aGF0IHNhbWUgaW50ZXJmYWNlIGFzIGBwYXJzZWAsIGJ1dCB3aWxsIHRyeSB0byBwYXJzZVxuLy8gYW55dGhpbmcgYXMgSmF2YVNjcmlwdCwgcmVwYWlyaW5nIHN5bnRheCBlcnJvciB0aGUgYmVzdCBpdCBjYW4uXG4vLyBUaGVyZSBhcmUgY2lyY3Vtc3RhbmNlcyBpbiB3aGljaCBpdCB3aWxsIHJhaXNlIGFuIGVycm9yIGFuZCBnaXZlXG4vLyB1cCwgYnV0IHRoZXkgYXJlIHZlcnkgcmFyZS4gVGhlIHJlc3VsdGluZyBBU1Qgd2lsbCBiZSBhIG1vc3RseVxuLy8gdmFsaWQgSmF2YVNjcmlwdCBBU1QgKGFzIHBlciB0aGUgW01vemlsbGEgcGFyc2VyIEFQSV1bYXBpXSwgZXhjZXB0XG4vLyB0aGF0OlxuLy9cbi8vIC0gUmV0dXJuIG91dHNpZGUgZnVuY3Rpb25zIGlzIGFsbG93ZWRcbi8vXG4vLyAtIExhYmVsIGNvbnNpc3RlbmN5IChubyBjb25mbGljdHMsIGJyZWFrIG9ubHkgdG8gZXhpc3RpbmcgbGFiZWxzKVxuLy8gICBpcyBub3QgZW5mb3JjZWQuXG4vL1xuLy8gLSBCb2d1cyBJZGVudGlmaWVyIG5vZGVzIHdpdGggYSBuYW1lIG9mIGBcIuKcllwiYCBhcmUgaW5zZXJ0ZWQgd2hlbmV2ZXJcbi8vICAgdGhlIHBhcnNlciBnb3QgdG9vIGNvbmZ1c2VkIHRvIHJldHVybiBhbnl0aGluZyBtZWFuaW5nZnVsLlxuLy9cbi8vIFthcGldOiBodHRwczovL2RldmVsb3Blci5tb3ppbGxhLm9yZy9lbi1VUy9kb2NzL1NwaWRlck1vbmtleS9QYXJzZXJfQVBJXG4vL1xuLy8gVGhlIGV4cGVjdGVkIHVzZSBmb3IgdGhpcyBpcyB0byAqZmlyc3QqIHRyeSBgYWNvcm4ucGFyc2VgLCBhbmQgb25seVxuLy8gaWYgdGhhdCBmYWlscyBzd2l0Y2ggdG8gYHBhcnNlX2RhbW1pdGAuIFRoZSBsb29zZSBwYXJzZXIgbWlnaHRcbi8vIHBhcnNlIGJhZGx5IGluZGVudGVkIGNvZGUgaW5jb3JyZWN0bHksIHNvICoqZG9uJ3QqKiB1c2UgaXQgYXNcbi8vIHlvdXIgZGVmYXVsdCBwYXJzZXIuXG4vL1xuLy8gUXVpdGUgYSBsb3Qgb2YgYWNvcm4uanMgaXMgZHVwbGljYXRlZCBoZXJlLiBUaGUgYWx0ZXJuYXRpdmUgd2FzIHRvXG4vLyBhZGQgYSAqbG90KiBvZiBleHRyYSBjcnVmdCB0byB0aGF0IGZpbGUsIG1ha2luZyBpdCBsZXNzIHJlYWRhYmxlXG4vLyBhbmQgc2xvd2VyLiBDb3B5aW5nIGFuZCBlZGl0aW5nIHRoZSBjb2RlIGFsbG93ZWQgbWUgdG8gbWFrZVxuLy8gaW52YXNpdmUgY2hhbmdlcyBhbmQgc2ltcGxpZmljYXRpb25zIHdpdGhvdXQgY3JlYXRpbmcgYSBjb21wbGljYXRlZFxuLy8gdGFuZ2xlLlxuXG5cInVzZSBzdHJpY3RcIjtcblxuZXhwb3J0cy5fX2VzTW9kdWxlID0gdHJ1ZTtcbmV4cG9ydHMucGFyc2VfZGFtbWl0ID0gcGFyc2VfZGFtbWl0O1xuXG5mdW5jdGlvbiBfaW50ZXJvcFJlcXVpcmVXaWxkY2FyZChvYmopIHsgaWYgKG9iaiAmJiBvYmouX19lc01vZHVsZSkgeyByZXR1cm4gb2JqOyB9IGVsc2UgeyB2YXIgbmV3T2JqID0ge307IGlmIChvYmogIT0gbnVsbCkgeyBmb3IgKHZhciBrZXkgaW4gb2JqKSB7IGlmIChPYmplY3QucHJvdG90eXBlLmhhc093blByb3BlcnR5LmNhbGwob2JqLCBrZXkpKSBuZXdPYmpba2V5XSA9IG9ialtrZXldOyB9IH0gbmV3T2JqW1wiZGVmYXVsdFwiXSA9IG9iajsgcmV0dXJuIG5ld09iajsgfSB9XG5cbnZhciBfID0gX2RlcmVxXyhcIi4uXCIpO1xuXG52YXIgYWNvcm4gPSBfaW50ZXJvcFJlcXVpcmVXaWxkY2FyZChfKTtcblxudmFyIF9zdGF0ZSA9IF9kZXJlcV8oXCIuL3N0YXRlXCIpO1xuXG5fZGVyZXFfKFwiLi90b2tlbml6ZVwiKTtcblxuX2RlcmVxXyhcIi4vc3RhdGVtZW50XCIpO1xuXG5fZGVyZXFfKFwiLi9leHByZXNzaW9uXCIpO1xuXG5leHBvcnRzLkxvb3NlUGFyc2VyID0gX3N0YXRlLkxvb3NlUGFyc2VyO1xuXG5hY29ybi5kZWZhdWx0T3B0aW9ucy50YWJTaXplID0gNDtcblxuZnVuY3Rpb24gcGFyc2VfZGFtbWl0KGlucHV0LCBvcHRpb25zKSB7XG4gIHZhciBwID0gbmV3IF9zdGF0ZS5Mb29zZVBhcnNlcihpbnB1dCwgb3B0aW9ucyk7XG4gIHAubmV4dCgpO1xuICByZXR1cm4gcC5wYXJzZVRvcExldmVsKCk7XG59XG5cbmFjb3JuLnBhcnNlX2RhbW1pdCA9IHBhcnNlX2RhbW1pdDtcbmFjb3JuLkxvb3NlUGFyc2VyID0gX3N0YXRlLkxvb3NlUGFyc2VyO1xuXG59LHtcIi4uXCI6MixcIi4vZXhwcmVzc2lvblwiOjMsXCIuL3N0YXRlXCI6NixcIi4vc3RhdGVtZW50XCI6NyxcIi4vdG9rZW5pemVcIjo4fV0sNTpbZnVuY3Rpb24oX2RlcmVxXyxtb2R1bGUsZXhwb3J0cyl7XG5cInVzZSBzdHJpY3RcIjtcblxuZXhwb3J0cy5fX2VzTW9kdWxlID0gdHJ1ZTtcbmV4cG9ydHMuaXNEdW1teSA9IGlzRHVtbXk7XG5cbmZ1bmN0aW9uIGlzRHVtbXkobm9kZSkge1xuICByZXR1cm4gbm9kZS5uYW1lID09IFwi4pyWXCI7XG59XG5cbn0se31dLDY6W2Z1bmN0aW9uKF9kZXJlcV8sbW9kdWxlLGV4cG9ydHMpe1xuXCJ1c2Ugc3RyaWN0XCI7XG5cbmV4cG9ydHMuX19lc01vZHVsZSA9IHRydWU7XG5cbmZ1bmN0aW9uIF9jbGFzc0NhbGxDaGVjayhpbnN0YW5jZSwgQ29uc3RydWN0b3IpIHsgaWYgKCEoaW5zdGFuY2UgaW5zdGFuY2VvZiBDb25zdHJ1Y3RvcikpIHsgdGhyb3cgbmV3IFR5cGVFcnJvcihcIkNhbm5vdCBjYWxsIGEgY2xhc3MgYXMgYSBmdW5jdGlvblwiKTsgfSB9XG5cbnZhciBfID0gX2RlcmVxXyhcIi4uXCIpO1xuXG52YXIgTG9vc2VQYXJzZXIgPSAoZnVuY3Rpb24gKCkge1xuICBmdW5jdGlvbiBMb29zZVBhcnNlcihpbnB1dCwgb3B0aW9ucykge1xuICAgIF9jbGFzc0NhbGxDaGVjayh0aGlzLCBMb29zZVBhcnNlcik7XG5cbiAgICB0aGlzLnRva3MgPSBfLnRva2VuaXplcihpbnB1dCwgb3B0aW9ucyk7XG4gICAgdGhpcy5vcHRpb25zID0gdGhpcy50b2tzLm9wdGlvbnM7XG4gICAgdGhpcy5pbnB1dCA9IHRoaXMudG9rcy5pbnB1dDtcbiAgICB0aGlzLnRvayA9IHRoaXMubGFzdCA9IHsgdHlwZTogXy50b2tUeXBlcy5lb2YsIHN0YXJ0OiAwLCBlbmQ6IDAgfTtcbiAgICBpZiAodGhpcy5vcHRpb25zLmxvY2F0aW9ucykge1xuICAgICAgdmFyIGhlcmUgPSB0aGlzLnRva3MuY3VyUG9zaXRpb24oKTtcbiAgICAgIHRoaXMudG9rLmxvYyA9IG5ldyBfLlNvdXJjZUxvY2F0aW9uKHRoaXMudG9rcywgaGVyZSwgaGVyZSk7XG4gICAgfVxuICAgIHRoaXMuYWhlYWQgPSBbXTsgLy8gVG9rZW5zIGFoZWFkXG4gICAgdGhpcy5jb250ZXh0ID0gW107IC8vIEluZGVudGF0aW9uIGNvbnRleHRlZFxuICAgIHRoaXMuY3VySW5kZW50ID0gMDtcbiAgICB0aGlzLmN1ckxpbmVTdGFydCA9IDA7XG4gICAgdGhpcy5uZXh0TGluZVN0YXJ0ID0gdGhpcy5saW5lRW5kKHRoaXMuY3VyTGluZVN0YXJ0KSArIDE7XG4gIH1cblxuICBMb29zZVBhcnNlci5wcm90b3R5cGUuc3RhcnROb2RlID0gZnVuY3Rpb24gc3RhcnROb2RlKCkge1xuICAgIHJldHVybiBuZXcgXy5Ob2RlKHRoaXMudG9rcywgdGhpcy50b2suc3RhcnQsIHRoaXMub3B0aW9ucy5sb2NhdGlvbnMgPyB0aGlzLnRvay5sb2Muc3RhcnQgOiBudWxsKTtcbiAgfTtcblxuICBMb29zZVBhcnNlci5wcm90b3R5cGUuc3RvcmVDdXJyZW50UG9zID0gZnVuY3Rpb24gc3RvcmVDdXJyZW50UG9zKCkge1xuICAgIHJldHVybiB0aGlzLm9wdGlvbnMubG9jYXRpb25zID8gW3RoaXMudG9rLnN0YXJ0LCB0aGlzLnRvay5sb2Muc3RhcnRdIDogdGhpcy50b2suc3RhcnQ7XG4gIH07XG5cbiAgTG9vc2VQYXJzZXIucHJvdG90eXBlLnN0YXJ0Tm9kZUF0ID0gZnVuY3Rpb24gc3RhcnROb2RlQXQocG9zKSB7XG4gICAgaWYgKHRoaXMub3B0aW9ucy5sb2NhdGlvbnMpIHtcbiAgICAgIHJldHVybiBuZXcgXy5Ob2RlKHRoaXMudG9rcywgcG9zWzBdLCBwb3NbMV0pO1xuICAgIH0gZWxzZSB7XG4gICAgICByZXR1cm4gbmV3IF8uTm9kZSh0aGlzLnRva3MsIHBvcyk7XG4gICAgfVxuICB9O1xuXG4gIExvb3NlUGFyc2VyLnByb3RvdHlwZS5maW5pc2hOb2RlID0gZnVuY3Rpb24gZmluaXNoTm9kZShub2RlLCB0eXBlKSB7XG4gICAgbm9kZS50eXBlID0gdHlwZTtcbiAgICBub2RlLmVuZCA9IHRoaXMubGFzdC5lbmQ7XG4gICAgaWYgKHRoaXMub3B0aW9ucy5sb2NhdGlvbnMpIG5vZGUubG9jLmVuZCA9IHRoaXMubGFzdC5sb2MuZW5kO1xuICAgIGlmICh0aGlzLm9wdGlvbnMucmFuZ2VzKSBub2RlLnJhbmdlWzFdID0gdGhpcy5sYXN0LmVuZDtcbiAgICByZXR1cm4gbm9kZTtcbiAgfTtcblxuICBMb29zZVBhcnNlci5wcm90b3R5cGUuZHVtbXlJZGVudCA9IGZ1bmN0aW9uIGR1bW15SWRlbnQoKSB7XG4gICAgdmFyIGR1bW15ID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgICBkdW1teS5uYW1lID0gXCLinJZcIjtcbiAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKGR1bW15LCBcIklkZW50aWZpZXJcIik7XG4gIH07XG5cbiAgTG9vc2VQYXJzZXIucHJvdG90eXBlLmVhdCA9IGZ1bmN0aW9uIGVhdCh0eXBlKSB7XG4gICAgaWYgKHRoaXMudG9rLnR5cGUgPT09IHR5cGUpIHtcbiAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgcmV0dXJuIHRydWU7XG4gICAgfSBlbHNlIHtcbiAgICAgIHJldHVybiBmYWxzZTtcbiAgICB9XG4gIH07XG5cbiAgTG9vc2VQYXJzZXIucHJvdG90eXBlLmlzQ29udGV4dHVhbCA9IGZ1bmN0aW9uIGlzQ29udGV4dHVhbChuYW1lKSB7XG4gICAgcmV0dXJuIHRoaXMudG9rLnR5cGUgPT09IF8udG9rVHlwZXMubmFtZSAmJiB0aGlzLnRvay52YWx1ZSA9PT0gbmFtZTtcbiAgfTtcblxuICBMb29zZVBhcnNlci5wcm90b3R5cGUuZWF0Q29udGV4dHVhbCA9IGZ1bmN0aW9uIGVhdENvbnRleHR1YWwobmFtZSkge1xuICAgIHJldHVybiB0aGlzLnRvay52YWx1ZSA9PT0gbmFtZSAmJiB0aGlzLmVhdChfLnRva1R5cGVzLm5hbWUpO1xuICB9O1xuXG4gIExvb3NlUGFyc2VyLnByb3RvdHlwZS5jYW5JbnNlcnRTZW1pY29sb24gPSBmdW5jdGlvbiBjYW5JbnNlcnRTZW1pY29sb24oKSB7XG4gICAgcmV0dXJuIHRoaXMudG9rLnR5cGUgPT09IF8udG9rVHlwZXMuZW9mIHx8IHRoaXMudG9rLnR5cGUgPT09IF8udG9rVHlwZXMuYnJhY2VSIHx8IF8ubGluZUJyZWFrLnRlc3QodGhpcy5pbnB1dC5zbGljZSh0aGlzLmxhc3QuZW5kLCB0aGlzLnRvay5zdGFydCkpO1xuICB9O1xuXG4gIExvb3NlUGFyc2VyLnByb3RvdHlwZS5zZW1pY29sb24gPSBmdW5jdGlvbiBzZW1pY29sb24oKSB7XG4gICAgcmV0dXJuIHRoaXMuZWF0KF8udG9rVHlwZXMuc2VtaSk7XG4gIH07XG5cbiAgTG9vc2VQYXJzZXIucHJvdG90eXBlLmV4cGVjdCA9IGZ1bmN0aW9uIGV4cGVjdCh0eXBlKSB7XG4gICAgaWYgKHRoaXMuZWF0KHR5cGUpKSByZXR1cm4gdHJ1ZTtcbiAgICBmb3IgKHZhciBpID0gMTsgaSA8PSAyOyBpKyspIHtcbiAgICAgIGlmICh0aGlzLmxvb2tBaGVhZChpKS50eXBlID09IHR5cGUpIHtcbiAgICAgICAgZm9yICh2YXIgaiA9IDA7IGogPCBpOyBqKyspIHtcbiAgICAgICAgICB0aGlzLm5leHQoKTtcbiAgICAgICAgfXJldHVybiB0cnVlO1xuICAgICAgfVxuICAgIH1cbiAgfTtcblxuICBMb29zZVBhcnNlci5wcm90b3R5cGUucHVzaEN4ID0gZnVuY3Rpb24gcHVzaEN4KCkge1xuICAgIHRoaXMuY29udGV4dC5wdXNoKHRoaXMuY3VySW5kZW50KTtcbiAgfTtcblxuICBMb29zZVBhcnNlci5wcm90b3R5cGUucG9wQ3ggPSBmdW5jdGlvbiBwb3BDeCgpIHtcbiAgICB0aGlzLmN1ckluZGVudCA9IHRoaXMuY29udGV4dC5wb3AoKTtcbiAgfTtcblxuICBMb29zZVBhcnNlci5wcm90b3R5cGUubGluZUVuZCA9IGZ1bmN0aW9uIGxpbmVFbmQocG9zKSB7XG4gICAgd2hpbGUgKHBvcyA8IHRoaXMuaW5wdXQubGVuZ3RoICYmICFfLmlzTmV3TGluZSh0aGlzLmlucHV0LmNoYXJDb2RlQXQocG9zKSkpICsrcG9zO1xuICAgIHJldHVybiBwb3M7XG4gIH07XG5cbiAgTG9vc2VQYXJzZXIucHJvdG90eXBlLmluZGVudGF0aW9uQWZ0ZXIgPSBmdW5jdGlvbiBpbmRlbnRhdGlvbkFmdGVyKHBvcykge1xuICAgIGZvciAodmFyIGNvdW50ID0gMDs7ICsrcG9zKSB7XG4gICAgICB2YXIgY2ggPSB0aGlzLmlucHV0LmNoYXJDb2RlQXQocG9zKTtcbiAgICAgIGlmIChjaCA9PT0gMzIpICsrY291bnQ7ZWxzZSBpZiAoY2ggPT09IDkpIGNvdW50ICs9IHRoaXMub3B0aW9ucy50YWJTaXplO2Vsc2UgcmV0dXJuIGNvdW50O1xuICAgIH1cbiAgfTtcblxuICBMb29zZVBhcnNlci5wcm90b3R5cGUuY2xvc2VzID0gZnVuY3Rpb24gY2xvc2VzKGNsb3NlVG9rLCBpbmRlbnQsIGxpbmUsIGJsb2NrSGV1cmlzdGljKSB7XG4gICAgaWYgKHRoaXMudG9rLnR5cGUgPT09IGNsb3NlVG9rIHx8IHRoaXMudG9rLnR5cGUgPT09IF8udG9rVHlwZXMuZW9mKSByZXR1cm4gdHJ1ZTtcbiAgICByZXR1cm4gbGluZSAhPSB0aGlzLmN1ckxpbmVTdGFydCAmJiB0aGlzLmN1ckluZGVudCA8IGluZGVudCAmJiB0aGlzLnRva2VuU3RhcnRzTGluZSgpICYmICghYmxvY2tIZXVyaXN0aWMgfHwgdGhpcy5uZXh0TGluZVN0YXJ0ID49IHRoaXMuaW5wdXQubGVuZ3RoIHx8IHRoaXMuaW5kZW50YXRpb25BZnRlcih0aGlzLm5leHRMaW5lU3RhcnQpIDwgaW5kZW50KTtcbiAgfTtcblxuICBMb29zZVBhcnNlci5wcm90b3R5cGUudG9rZW5TdGFydHNMaW5lID0gZnVuY3Rpb24gdG9rZW5TdGFydHNMaW5lKCkge1xuICAgIGZvciAodmFyIHAgPSB0aGlzLnRvay5zdGFydCAtIDE7IHAgPj0gdGhpcy5jdXJMaW5lU3RhcnQ7IC0tcCkge1xuICAgICAgdmFyIGNoID0gdGhpcy5pbnB1dC5jaGFyQ29kZUF0KHApO1xuICAgICAgaWYgKGNoICE9PSA5ICYmIGNoICE9PSAzMikgcmV0dXJuIGZhbHNlO1xuICAgIH1cbiAgICByZXR1cm4gdHJ1ZTtcbiAgfTtcblxuICByZXR1cm4gTG9vc2VQYXJzZXI7XG59KSgpO1xuXG5leHBvcnRzLkxvb3NlUGFyc2VyID0gTG9vc2VQYXJzZXI7XG5cbn0se1wiLi5cIjoyfV0sNzpbZnVuY3Rpb24oX2RlcmVxXyxtb2R1bGUsZXhwb3J0cyl7XG5cInVzZSBzdHJpY3RcIjtcblxudmFyIF9zdGF0ZSA9IF9kZXJlcV8oXCIuL3N0YXRlXCIpO1xuXG52YXIgX3BhcnNldXRpbCA9IF9kZXJlcV8oXCIuL3BhcnNldXRpbFwiKTtcblxudmFyIF8gPSBfZGVyZXFfKFwiLi5cIik7XG5cbnZhciBscCA9IF9zdGF0ZS5Mb29zZVBhcnNlci5wcm90b3R5cGU7XG5cbmxwLnBhcnNlVG9wTGV2ZWwgPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGVBdCh0aGlzLm9wdGlvbnMubG9jYXRpb25zID8gWzAsIF8uZ2V0TGluZUluZm8odGhpcy5pbnB1dCwgMCldIDogMCk7XG4gIG5vZGUuYm9keSA9IFtdO1xuICB3aGlsZSAodGhpcy50b2sudHlwZSAhPT0gXy50b2tUeXBlcy5lb2YpIG5vZGUuYm9keS5wdXNoKHRoaXMucGFyc2VTdGF0ZW1lbnQoKSk7XG4gIHRoaXMubGFzdCA9IHRoaXMudG9rO1xuICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDYpIHtcbiAgICBub2RlLnNvdXJjZVR5cGUgPSB0aGlzLm9wdGlvbnMuc291cmNlVHlwZTtcbiAgfVxuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiUHJvZ3JhbVwiKTtcbn07XG5cbmxwLnBhcnNlU3RhdGVtZW50ID0gZnVuY3Rpb24gKCkge1xuICB2YXIgc3RhcnR0eXBlID0gdGhpcy50b2sudHlwZSxcbiAgICAgIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuXG4gIHN3aXRjaCAoc3RhcnR0eXBlKSB7XG4gICAgY2FzZSBfLnRva1R5cGVzLl9icmVhazpjYXNlIF8udG9rVHlwZXMuX2NvbnRpbnVlOlxuICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICB2YXIgaXNCcmVhayA9IHN0YXJ0dHlwZSA9PT0gXy50b2tUeXBlcy5fYnJlYWs7XG4gICAgICBpZiAodGhpcy5zZW1pY29sb24oKSB8fCB0aGlzLmNhbkluc2VydFNlbWljb2xvbigpKSB7XG4gICAgICAgIG5vZGUubGFiZWwgPSBudWxsO1xuICAgICAgfSBlbHNlIHtcbiAgICAgICAgbm9kZS5sYWJlbCA9IHRoaXMudG9rLnR5cGUgPT09IF8udG9rVHlwZXMubmFtZSA/IHRoaXMucGFyc2VJZGVudCgpIDogbnVsbDtcbiAgICAgICAgdGhpcy5zZW1pY29sb24oKTtcbiAgICAgIH1cbiAgICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgaXNCcmVhayA/IFwiQnJlYWtTdGF0ZW1lbnRcIiA6IFwiQ29udGludWVTdGF0ZW1lbnRcIik7XG5cbiAgICBjYXNlIF8udG9rVHlwZXMuX2RlYnVnZ2VyOlxuICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICB0aGlzLnNlbWljb2xvbigpO1xuICAgICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkRlYnVnZ2VyU3RhdGVtZW50XCIpO1xuXG4gICAgY2FzZSBfLnRva1R5cGVzLl9kbzpcbiAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgbm9kZS5ib2R5ID0gdGhpcy5wYXJzZVN0YXRlbWVudCgpO1xuICAgICAgbm9kZS50ZXN0ID0gdGhpcy5lYXQoXy50b2tUeXBlcy5fd2hpbGUpID8gdGhpcy5wYXJzZVBhcmVuRXhwcmVzc2lvbigpIDogdGhpcy5kdW1teUlkZW50KCk7XG4gICAgICB0aGlzLnNlbWljb2xvbigpO1xuICAgICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkRvV2hpbGVTdGF0ZW1lbnRcIik7XG5cbiAgICBjYXNlIF8udG9rVHlwZXMuX2ZvcjpcbiAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgdGhpcy5wdXNoQ3goKTtcbiAgICAgIHRoaXMuZXhwZWN0KF8udG9rVHlwZXMucGFyZW5MKTtcbiAgICAgIGlmICh0aGlzLnRvay50eXBlID09PSBfLnRva1R5cGVzLnNlbWkpIHJldHVybiB0aGlzLnBhcnNlRm9yKG5vZGUsIG51bGwpO1xuICAgICAgaWYgKHRoaXMudG9rLnR5cGUgPT09IF8udG9rVHlwZXMuX3ZhciB8fCB0aGlzLnRvay50eXBlID09PSBfLnRva1R5cGVzLl9sZXQgfHwgdGhpcy50b2sudHlwZSA9PT0gXy50b2tUeXBlcy5fY29uc3QpIHtcbiAgICAgICAgdmFyIF9pbml0ID0gdGhpcy5wYXJzZVZhcih0cnVlKTtcbiAgICAgICAgaWYgKF9pbml0LmRlY2xhcmF0aW9ucy5sZW5ndGggPT09IDEgJiYgKHRoaXMudG9rLnR5cGUgPT09IF8udG9rVHlwZXMuX2luIHx8IHRoaXMuaXNDb250ZXh0dWFsKFwib2ZcIikpKSB7XG4gICAgICAgICAgcmV0dXJuIHRoaXMucGFyc2VGb3JJbihub2RlLCBfaW5pdCk7XG4gICAgICAgIH1cbiAgICAgICAgcmV0dXJuIHRoaXMucGFyc2VGb3Iobm9kZSwgX2luaXQpO1xuICAgICAgfVxuICAgICAgdmFyIGluaXQgPSB0aGlzLnBhcnNlRXhwcmVzc2lvbih0cnVlKTtcbiAgICAgIGlmICh0aGlzLnRvay50eXBlID09PSBfLnRva1R5cGVzLl9pbiB8fCB0aGlzLmlzQ29udGV4dHVhbChcIm9mXCIpKSByZXR1cm4gdGhpcy5wYXJzZUZvckluKG5vZGUsIHRoaXMudG9Bc3NpZ25hYmxlKGluaXQpKTtcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlRm9yKG5vZGUsIGluaXQpO1xuXG4gICAgY2FzZSBfLnRva1R5cGVzLl9mdW5jdGlvbjpcbiAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgcmV0dXJuIHRoaXMucGFyc2VGdW5jdGlvbihub2RlLCB0cnVlKTtcblxuICAgIGNhc2UgXy50b2tUeXBlcy5faWY6XG4gICAgICB0aGlzLm5leHQoKTtcbiAgICAgIG5vZGUudGVzdCA9IHRoaXMucGFyc2VQYXJlbkV4cHJlc3Npb24oKTtcbiAgICAgIG5vZGUuY29uc2VxdWVudCA9IHRoaXMucGFyc2VTdGF0ZW1lbnQoKTtcbiAgICAgIG5vZGUuYWx0ZXJuYXRlID0gdGhpcy5lYXQoXy50b2tUeXBlcy5fZWxzZSkgPyB0aGlzLnBhcnNlU3RhdGVtZW50KCkgOiBudWxsO1xuICAgICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIklmU3RhdGVtZW50XCIpO1xuXG4gICAgY2FzZSBfLnRva1R5cGVzLl9yZXR1cm46XG4gICAgICB0aGlzLm5leHQoKTtcbiAgICAgIGlmICh0aGlzLmVhdChfLnRva1R5cGVzLnNlbWkpIHx8IHRoaXMuY2FuSW5zZXJ0U2VtaWNvbG9uKCkpIG5vZGUuYXJndW1lbnQgPSBudWxsO2Vsc2Uge1xuICAgICAgICBub2RlLmFyZ3VtZW50ID0gdGhpcy5wYXJzZUV4cHJlc3Npb24oKTt0aGlzLnNlbWljb2xvbigpO1xuICAgICAgfVxuICAgICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIlJldHVyblN0YXRlbWVudFwiKTtcblxuICAgIGNhc2UgXy50b2tUeXBlcy5fc3dpdGNoOlxuICAgICAgdmFyIGJsb2NrSW5kZW50ID0gdGhpcy5jdXJJbmRlbnQsXG4gICAgICAgICAgbGluZSA9IHRoaXMuY3VyTGluZVN0YXJ0O1xuICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICBub2RlLmRpc2NyaW1pbmFudCA9IHRoaXMucGFyc2VQYXJlbkV4cHJlc3Npb24oKTtcbiAgICAgIG5vZGUuY2FzZXMgPSBbXTtcbiAgICAgIHRoaXMucHVzaEN4KCk7XG4gICAgICB0aGlzLmV4cGVjdChfLnRva1R5cGVzLmJyYWNlTCk7XG5cbiAgICAgIHZhciBjdXIgPSB1bmRlZmluZWQ7XG4gICAgICB3aGlsZSAoIXRoaXMuY2xvc2VzKF8udG9rVHlwZXMuYnJhY2VSLCBibG9ja0luZGVudCwgbGluZSwgdHJ1ZSkpIHtcbiAgICAgICAgaWYgKHRoaXMudG9rLnR5cGUgPT09IF8udG9rVHlwZXMuX2Nhc2UgfHwgdGhpcy50b2sudHlwZSA9PT0gXy50b2tUeXBlcy5fZGVmYXVsdCkge1xuICAgICAgICAgIHZhciBpc0Nhc2UgPSB0aGlzLnRvay50eXBlID09PSBfLnRva1R5cGVzLl9jYXNlO1xuICAgICAgICAgIGlmIChjdXIpIHRoaXMuZmluaXNoTm9kZShjdXIsIFwiU3dpdGNoQ2FzZVwiKTtcbiAgICAgICAgICBub2RlLmNhc2VzLnB1c2goY3VyID0gdGhpcy5zdGFydE5vZGUoKSk7XG4gICAgICAgICAgY3VyLmNvbnNlcXVlbnQgPSBbXTtcbiAgICAgICAgICB0aGlzLm5leHQoKTtcbiAgICAgICAgICBpZiAoaXNDYXNlKSBjdXIudGVzdCA9IHRoaXMucGFyc2VFeHByZXNzaW9uKCk7ZWxzZSBjdXIudGVzdCA9IG51bGw7XG4gICAgICAgICAgdGhpcy5leHBlY3QoXy50b2tUeXBlcy5jb2xvbik7XG4gICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgaWYgKCFjdXIpIHtcbiAgICAgICAgICAgIG5vZGUuY2FzZXMucHVzaChjdXIgPSB0aGlzLnN0YXJ0Tm9kZSgpKTtcbiAgICAgICAgICAgIGN1ci5jb25zZXF1ZW50ID0gW107XG4gICAgICAgICAgICBjdXIudGVzdCA9IG51bGw7XG4gICAgICAgICAgfVxuICAgICAgICAgIGN1ci5jb25zZXF1ZW50LnB1c2godGhpcy5wYXJzZVN0YXRlbWVudCgpKTtcbiAgICAgICAgfVxuICAgICAgfVxuICAgICAgaWYgKGN1cikgdGhpcy5maW5pc2hOb2RlKGN1ciwgXCJTd2l0Y2hDYXNlXCIpO1xuICAgICAgdGhpcy5wb3BDeCgpO1xuICAgICAgdGhpcy5lYXQoXy50b2tUeXBlcy5icmFjZVIpO1xuICAgICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIlN3aXRjaFN0YXRlbWVudFwiKTtcblxuICAgIGNhc2UgXy50b2tUeXBlcy5fdGhyb3c6XG4gICAgICB0aGlzLm5leHQoKTtcbiAgICAgIG5vZGUuYXJndW1lbnQgPSB0aGlzLnBhcnNlRXhwcmVzc2lvbigpO1xuICAgICAgdGhpcy5zZW1pY29sb24oKTtcbiAgICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJUaHJvd1N0YXRlbWVudFwiKTtcblxuICAgIGNhc2UgXy50b2tUeXBlcy5fdHJ5OlxuICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICBub2RlLmJsb2NrID0gdGhpcy5wYXJzZUJsb2NrKCk7XG4gICAgICBub2RlLmhhbmRsZXIgPSBudWxsO1xuICAgICAgaWYgKHRoaXMudG9rLnR5cGUgPT09IF8udG9rVHlwZXMuX2NhdGNoKSB7XG4gICAgICAgIHZhciBjbGF1c2UgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICAgICAgICB0aGlzLm5leHQoKTtcbiAgICAgICAgdGhpcy5leHBlY3QoXy50b2tUeXBlcy5wYXJlbkwpO1xuICAgICAgICBjbGF1c2UucGFyYW0gPSB0aGlzLnRvQXNzaWduYWJsZSh0aGlzLnBhcnNlRXhwckF0b20oKSwgdHJ1ZSk7XG4gICAgICAgIHRoaXMuZXhwZWN0KF8udG9rVHlwZXMucGFyZW5SKTtcbiAgICAgICAgY2xhdXNlLmd1YXJkID0gbnVsbDtcbiAgICAgICAgY2xhdXNlLmJvZHkgPSB0aGlzLnBhcnNlQmxvY2soKTtcbiAgICAgICAgbm9kZS5oYW5kbGVyID0gdGhpcy5maW5pc2hOb2RlKGNsYXVzZSwgXCJDYXRjaENsYXVzZVwiKTtcbiAgICAgIH1cbiAgICAgIG5vZGUuZmluYWxpemVyID0gdGhpcy5lYXQoXy50b2tUeXBlcy5fZmluYWxseSkgPyB0aGlzLnBhcnNlQmxvY2soKSA6IG51bGw7XG4gICAgICBpZiAoIW5vZGUuaGFuZGxlciAmJiAhbm9kZS5maW5hbGl6ZXIpIHJldHVybiBub2RlLmJsb2NrO1xuICAgICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIlRyeVN0YXRlbWVudFwiKTtcblxuICAgIGNhc2UgXy50b2tUeXBlcy5fdmFyOlxuICAgIGNhc2UgXy50b2tUeXBlcy5fbGV0OlxuICAgIGNhc2UgXy50b2tUeXBlcy5fY29uc3Q6XG4gICAgICByZXR1cm4gdGhpcy5wYXJzZVZhcigpO1xuXG4gICAgY2FzZSBfLnRva1R5cGVzLl93aGlsZTpcbiAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgbm9kZS50ZXN0ID0gdGhpcy5wYXJzZVBhcmVuRXhwcmVzc2lvbigpO1xuICAgICAgbm9kZS5ib2R5ID0gdGhpcy5wYXJzZVN0YXRlbWVudCgpO1xuICAgICAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIldoaWxlU3RhdGVtZW50XCIpO1xuXG4gICAgY2FzZSBfLnRva1R5cGVzLl93aXRoOlxuICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICBub2RlLm9iamVjdCA9IHRoaXMucGFyc2VQYXJlbkV4cHJlc3Npb24oKTtcbiAgICAgIG5vZGUuYm9keSA9IHRoaXMucGFyc2VTdGF0ZW1lbnQoKTtcbiAgICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJXaXRoU3RhdGVtZW50XCIpO1xuXG4gICAgY2FzZSBfLnRva1R5cGVzLmJyYWNlTDpcbiAgICAgIHJldHVybiB0aGlzLnBhcnNlQmxvY2soKTtcblxuICAgIGNhc2UgXy50b2tUeXBlcy5zZW1pOlxuICAgICAgdGhpcy5uZXh0KCk7XG4gICAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiRW1wdHlTdGF0ZW1lbnRcIik7XG5cbiAgICBjYXNlIF8udG9rVHlwZXMuX2NsYXNzOlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VDbGFzcyh0cnVlKTtcblxuICAgIGNhc2UgXy50b2tUeXBlcy5faW1wb3J0OlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VJbXBvcnQoKTtcblxuICAgIGNhc2UgXy50b2tUeXBlcy5fZXhwb3J0OlxuICAgICAgcmV0dXJuIHRoaXMucGFyc2VFeHBvcnQoKTtcblxuICAgIGRlZmF1bHQ6XG4gICAgICB2YXIgZXhwciA9IHRoaXMucGFyc2VFeHByZXNzaW9uKCk7XG4gICAgICBpZiAoX3BhcnNldXRpbC5pc0R1bW15KGV4cHIpKSB7XG4gICAgICAgIHRoaXMubmV4dCgpO1xuICAgICAgICBpZiAodGhpcy50b2sudHlwZSA9PT0gXy50b2tUeXBlcy5lb2YpIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJFbXB0eVN0YXRlbWVudFwiKTtcbiAgICAgICAgcmV0dXJuIHRoaXMucGFyc2VTdGF0ZW1lbnQoKTtcbiAgICAgIH0gZWxzZSBpZiAoc3RhcnR0eXBlID09PSBfLnRva1R5cGVzLm5hbWUgJiYgZXhwci50eXBlID09PSBcIklkZW50aWZpZXJcIiAmJiB0aGlzLmVhdChfLnRva1R5cGVzLmNvbG9uKSkge1xuICAgICAgICBub2RlLmJvZHkgPSB0aGlzLnBhcnNlU3RhdGVtZW50KCk7XG4gICAgICAgIG5vZGUubGFiZWwgPSBleHByO1xuICAgICAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiTGFiZWxlZFN0YXRlbWVudFwiKTtcbiAgICAgIH0gZWxzZSB7XG4gICAgICAgIG5vZGUuZXhwcmVzc2lvbiA9IGV4cHI7XG4gICAgICAgIHRoaXMuc2VtaWNvbG9uKCk7XG4gICAgICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJFeHByZXNzaW9uU3RhdGVtZW50XCIpO1xuICAgICAgfVxuICB9XG59O1xuXG5scC5wYXJzZUJsb2NrID0gZnVuY3Rpb24gKCkge1xuICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gIHRoaXMucHVzaEN4KCk7XG4gIHRoaXMuZXhwZWN0KF8udG9rVHlwZXMuYnJhY2VMKTtcbiAgdmFyIGJsb2NrSW5kZW50ID0gdGhpcy5jdXJJbmRlbnQsXG4gICAgICBsaW5lID0gdGhpcy5jdXJMaW5lU3RhcnQ7XG4gIG5vZGUuYm9keSA9IFtdO1xuICB3aGlsZSAoIXRoaXMuY2xvc2VzKF8udG9rVHlwZXMuYnJhY2VSLCBibG9ja0luZGVudCwgbGluZSwgdHJ1ZSkpIG5vZGUuYm9keS5wdXNoKHRoaXMucGFyc2VTdGF0ZW1lbnQoKSk7XG4gIHRoaXMucG9wQ3goKTtcbiAgdGhpcy5lYXQoXy50b2tUeXBlcy5icmFjZVIpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiQmxvY2tTdGF0ZW1lbnRcIik7XG59O1xuXG5scC5wYXJzZUZvciA9IGZ1bmN0aW9uIChub2RlLCBpbml0KSB7XG4gIG5vZGUuaW5pdCA9IGluaXQ7XG4gIG5vZGUudGVzdCA9IG5vZGUudXBkYXRlID0gbnVsbDtcbiAgaWYgKHRoaXMuZWF0KF8udG9rVHlwZXMuc2VtaSkgJiYgdGhpcy50b2sudHlwZSAhPT0gXy50b2tUeXBlcy5zZW1pKSBub2RlLnRlc3QgPSB0aGlzLnBhcnNlRXhwcmVzc2lvbigpO1xuICBpZiAodGhpcy5lYXQoXy50b2tUeXBlcy5zZW1pKSAmJiB0aGlzLnRvay50eXBlICE9PSBfLnRva1R5cGVzLnBhcmVuUikgbm9kZS51cGRhdGUgPSB0aGlzLnBhcnNlRXhwcmVzc2lvbigpO1xuICB0aGlzLnBvcEN4KCk7XG4gIHRoaXMuZXhwZWN0KF8udG9rVHlwZXMucGFyZW5SKTtcbiAgbm9kZS5ib2R5ID0gdGhpcy5wYXJzZVN0YXRlbWVudCgpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiRm9yU3RhdGVtZW50XCIpO1xufTtcblxubHAucGFyc2VGb3JJbiA9IGZ1bmN0aW9uIChub2RlLCBpbml0KSB7XG4gIHZhciB0eXBlID0gdGhpcy50b2sudHlwZSA9PT0gXy50b2tUeXBlcy5faW4gPyBcIkZvckluU3RhdGVtZW50XCIgOiBcIkZvck9mU3RhdGVtZW50XCI7XG4gIHRoaXMubmV4dCgpO1xuICBub2RlLmxlZnQgPSBpbml0O1xuICBub2RlLnJpZ2h0ID0gdGhpcy5wYXJzZUV4cHJlc3Npb24oKTtcbiAgdGhpcy5wb3BDeCgpO1xuICB0aGlzLmV4cGVjdChfLnRva1R5cGVzLnBhcmVuUik7XG4gIG5vZGUuYm9keSA9IHRoaXMucGFyc2VTdGF0ZW1lbnQoKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCB0eXBlKTtcbn07XG5cbmxwLnBhcnNlVmFyID0gZnVuY3Rpb24gKG5vSW4pIHtcbiAgdmFyIG5vZGUgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICBub2RlLmtpbmQgPSB0aGlzLnRvay50eXBlLmtleXdvcmQ7XG4gIHRoaXMubmV4dCgpO1xuICBub2RlLmRlY2xhcmF0aW9ucyA9IFtdO1xuICBkbyB7XG4gICAgdmFyIGRlY2wgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICAgIGRlY2wuaWQgPSB0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNiA/IHRoaXMudG9Bc3NpZ25hYmxlKHRoaXMucGFyc2VFeHByQXRvbSgpLCB0cnVlKSA6IHRoaXMucGFyc2VJZGVudCgpO1xuICAgIGRlY2wuaW5pdCA9IHRoaXMuZWF0KF8udG9rVHlwZXMuZXEpID8gdGhpcy5wYXJzZU1heWJlQXNzaWduKG5vSW4pIDogbnVsbDtcbiAgICBub2RlLmRlY2xhcmF0aW9ucy5wdXNoKHRoaXMuZmluaXNoTm9kZShkZWNsLCBcIlZhcmlhYmxlRGVjbGFyYXRvclwiKSk7XG4gIH0gd2hpbGUgKHRoaXMuZWF0KF8udG9rVHlwZXMuY29tbWEpKTtcbiAgaWYgKCFub2RlLmRlY2xhcmF0aW9ucy5sZW5ndGgpIHtcbiAgICB2YXIgZGVjbCA9IHRoaXMuc3RhcnROb2RlKCk7XG4gICAgZGVjbC5pZCA9IHRoaXMuZHVtbXlJZGVudCgpO1xuICAgIG5vZGUuZGVjbGFyYXRpb25zLnB1c2godGhpcy5maW5pc2hOb2RlKGRlY2wsIFwiVmFyaWFibGVEZWNsYXJhdG9yXCIpKTtcbiAgfVxuICBpZiAoIW5vSW4pIHRoaXMuc2VtaWNvbG9uKCk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJWYXJpYWJsZURlY2xhcmF0aW9uXCIpO1xufTtcblxubHAucGFyc2VDbGFzcyA9IGZ1bmN0aW9uIChpc1N0YXRlbWVudCkge1xuICB2YXIgbm9kZSA9IHRoaXMuc3RhcnROb2RlKCk7XG4gIHRoaXMubmV4dCgpO1xuICBpZiAodGhpcy50b2sudHlwZSA9PT0gXy50b2tUeXBlcy5uYW1lKSBub2RlLmlkID0gdGhpcy5wYXJzZUlkZW50KCk7ZWxzZSBpZiAoaXNTdGF0ZW1lbnQpIG5vZGUuaWQgPSB0aGlzLmR1bW15SWRlbnQoKTtlbHNlIG5vZGUuaWQgPSBudWxsO1xuICBub2RlLnN1cGVyQ2xhc3MgPSB0aGlzLmVhdChfLnRva1R5cGVzLl9leHRlbmRzKSA/IHRoaXMucGFyc2VFeHByZXNzaW9uKCkgOiBudWxsO1xuICBub2RlLmJvZHkgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICBub2RlLmJvZHkuYm9keSA9IFtdO1xuICB0aGlzLnB1c2hDeCgpO1xuICB2YXIgaW5kZW50ID0gdGhpcy5jdXJJbmRlbnQgKyAxLFxuICAgICAgbGluZSA9IHRoaXMuY3VyTGluZVN0YXJ0O1xuICB0aGlzLmVhdChfLnRva1R5cGVzLmJyYWNlTCk7XG4gIGlmICh0aGlzLmN1ckluZGVudCArIDEgPCBpbmRlbnQpIHtcbiAgICBpbmRlbnQgPSB0aGlzLmN1ckluZGVudDtsaW5lID0gdGhpcy5jdXJMaW5lU3RhcnQ7XG4gIH1cbiAgd2hpbGUgKCF0aGlzLmNsb3NlcyhfLnRva1R5cGVzLmJyYWNlUiwgaW5kZW50LCBsaW5lKSkge1xuICAgIGlmICh0aGlzLnNlbWljb2xvbigpKSBjb250aW51ZTtcbiAgICB2YXIgbWV0aG9kID0gdGhpcy5zdGFydE5vZGUoKSxcbiAgICAgICAgaXNHZW5lcmF0b3IgPSB1bmRlZmluZWQ7XG4gICAgaWYgKHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KSB7XG4gICAgICBtZXRob2RbXCJzdGF0aWNcIl0gPSBmYWxzZTtcbiAgICAgIGlzR2VuZXJhdG9yID0gdGhpcy5lYXQoXy50b2tUeXBlcy5zdGFyKTtcbiAgICB9XG4gICAgdGhpcy5wYXJzZVByb3BlcnR5TmFtZShtZXRob2QpO1xuICAgIGlmIChfcGFyc2V1dGlsLmlzRHVtbXkobWV0aG9kLmtleSkpIHtcbiAgICAgIGlmIChfcGFyc2V1dGlsLmlzRHVtbXkodGhpcy5wYXJzZU1heWJlQXNzaWduKCkpKSB0aGlzLm5leHQoKTt0aGlzLmVhdChfLnRva1R5cGVzLmNvbW1hKTtjb250aW51ZTtcbiAgICB9XG4gICAgaWYgKG1ldGhvZC5rZXkudHlwZSA9PT0gXCJJZGVudGlmaWVyXCIgJiYgIW1ldGhvZC5jb21wdXRlZCAmJiBtZXRob2Qua2V5Lm5hbWUgPT09IFwic3RhdGljXCIgJiYgKHRoaXMudG9rLnR5cGUgIT0gXy50b2tUeXBlcy5wYXJlbkwgJiYgdGhpcy50b2sudHlwZSAhPSBfLnRva1R5cGVzLmJyYWNlTCkpIHtcbiAgICAgIG1ldGhvZFtcInN0YXRpY1wiXSA9IHRydWU7XG4gICAgICBpc0dlbmVyYXRvciA9IHRoaXMuZWF0KF8udG9rVHlwZXMuc3Rhcik7XG4gICAgICB0aGlzLnBhcnNlUHJvcGVydHlOYW1lKG1ldGhvZCk7XG4gICAgfSBlbHNlIHtcbiAgICAgIG1ldGhvZFtcInN0YXRpY1wiXSA9IGZhbHNlO1xuICAgIH1cbiAgICBpZiAodGhpcy5vcHRpb25zLmVjbWFWZXJzaW9uID49IDUgJiYgbWV0aG9kLmtleS50eXBlID09PSBcIklkZW50aWZpZXJcIiAmJiAhbWV0aG9kLmNvbXB1dGVkICYmIChtZXRob2Qua2V5Lm5hbWUgPT09IFwiZ2V0XCIgfHwgbWV0aG9kLmtleS5uYW1lID09PSBcInNldFwiKSAmJiB0aGlzLnRvay50eXBlICE9PSBfLnRva1R5cGVzLnBhcmVuTCAmJiB0aGlzLnRvay50eXBlICE9PSBfLnRva1R5cGVzLmJyYWNlTCkge1xuICAgICAgbWV0aG9kLmtpbmQgPSBtZXRob2Qua2V5Lm5hbWU7XG4gICAgICB0aGlzLnBhcnNlUHJvcGVydHlOYW1lKG1ldGhvZCk7XG4gICAgICBtZXRob2QudmFsdWUgPSB0aGlzLnBhcnNlTWV0aG9kKGZhbHNlKTtcbiAgICB9IGVsc2Uge1xuICAgICAgaWYgKCFtZXRob2QuY29tcHV0ZWQgJiYgIW1ldGhvZFtcInN0YXRpY1wiXSAmJiAhaXNHZW5lcmF0b3IgJiYgKG1ldGhvZC5rZXkudHlwZSA9PT0gXCJJZGVudGlmaWVyXCIgJiYgbWV0aG9kLmtleS5uYW1lID09PSBcImNvbnN0cnVjdG9yXCIgfHwgbWV0aG9kLmtleS50eXBlID09PSBcIkxpdGVyYWxcIiAmJiBtZXRob2Qua2V5LnZhbHVlID09PSBcImNvbnN0cnVjdG9yXCIpKSB7XG4gICAgICAgIG1ldGhvZC5raW5kID0gXCJjb25zdHJ1Y3RvclwiO1xuICAgICAgfSBlbHNlIHtcbiAgICAgICAgbWV0aG9kLmtpbmQgPSBcIm1ldGhvZFwiO1xuICAgICAgfVxuICAgICAgbWV0aG9kLnZhbHVlID0gdGhpcy5wYXJzZU1ldGhvZChpc0dlbmVyYXRvcik7XG4gICAgfVxuICAgIG5vZGUuYm9keS5ib2R5LnB1c2godGhpcy5maW5pc2hOb2RlKG1ldGhvZCwgXCJNZXRob2REZWZpbml0aW9uXCIpKTtcbiAgfVxuICB0aGlzLnBvcEN4KCk7XG4gIGlmICghdGhpcy5lYXQoXy50b2tUeXBlcy5icmFjZVIpKSB7XG4gICAgLy8gSWYgdGhlcmUgaXMgbm8gY2xvc2luZyBicmFjZSwgbWFrZSB0aGUgbm9kZSBzcGFuIHRvIHRoZSBzdGFydFxuICAgIC8vIG9mIHRoZSBuZXh0IHRva2VuICh0aGlzIGlzIHVzZWZ1bCBmb3IgVGVybilcbiAgICB0aGlzLmxhc3QuZW5kID0gdGhpcy50b2suc3RhcnQ7XG4gICAgaWYgKHRoaXMub3B0aW9ucy5sb2NhdGlvbnMpIHRoaXMubGFzdC5sb2MuZW5kID0gdGhpcy50b2subG9jLnN0YXJ0O1xuICB9XG4gIHRoaXMuc2VtaWNvbG9uKCk7XG4gIHRoaXMuZmluaXNoTm9kZShub2RlLmJvZHksIFwiQ2xhc3NCb2R5XCIpO1xuICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIGlzU3RhdGVtZW50ID8gXCJDbGFzc0RlY2xhcmF0aW9uXCIgOiBcIkNsYXNzRXhwcmVzc2lvblwiKTtcbn07XG5cbmxwLnBhcnNlRnVuY3Rpb24gPSBmdW5jdGlvbiAobm9kZSwgaXNTdGF0ZW1lbnQpIHtcbiAgdGhpcy5pbml0RnVuY3Rpb24obm9kZSk7XG4gIGlmICh0aGlzLm9wdGlvbnMuZWNtYVZlcnNpb24gPj0gNikge1xuICAgIG5vZGUuZ2VuZXJhdG9yID0gdGhpcy5lYXQoXy50b2tUeXBlcy5zdGFyKTtcbiAgfVxuICBpZiAodGhpcy50b2sudHlwZSA9PT0gXy50b2tUeXBlcy5uYW1lKSBub2RlLmlkID0gdGhpcy5wYXJzZUlkZW50KCk7ZWxzZSBpZiAoaXNTdGF0ZW1lbnQpIG5vZGUuaWQgPSB0aGlzLmR1bW15SWRlbnQoKTtcbiAgbm9kZS5wYXJhbXMgPSB0aGlzLnBhcnNlRnVuY3Rpb25QYXJhbXMoKTtcbiAgbm9kZS5ib2R5ID0gdGhpcy5wYXJzZUJsb2NrKCk7XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgaXNTdGF0ZW1lbnQgPyBcIkZ1bmN0aW9uRGVjbGFyYXRpb25cIiA6IFwiRnVuY3Rpb25FeHByZXNzaW9uXCIpO1xufTtcblxubHAucGFyc2VFeHBvcnQgPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgdGhpcy5uZXh0KCk7XG4gIGlmICh0aGlzLmVhdChfLnRva1R5cGVzLnN0YXIpKSB7XG4gICAgbm9kZS5zb3VyY2UgPSB0aGlzLmVhdENvbnRleHR1YWwoXCJmcm9tXCIpID8gdGhpcy5wYXJzZUV4cHJBdG9tKCkgOiBudWxsO1xuICAgIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJFeHBvcnRBbGxEZWNsYXJhdGlvblwiKTtcbiAgfVxuICBpZiAodGhpcy5lYXQoXy50b2tUeXBlcy5fZGVmYXVsdCkpIHtcbiAgICB2YXIgZXhwciA9IHRoaXMucGFyc2VNYXliZUFzc2lnbigpO1xuICAgIGlmIChleHByLmlkKSB7XG4gICAgICBzd2l0Y2ggKGV4cHIudHlwZSkge1xuICAgICAgICBjYXNlIFwiRnVuY3Rpb25FeHByZXNzaW9uXCI6XG4gICAgICAgICAgZXhwci50eXBlID0gXCJGdW5jdGlvbkRlY2xhcmF0aW9uXCI7YnJlYWs7XG4gICAgICAgIGNhc2UgXCJDbGFzc0V4cHJlc3Npb25cIjpcbiAgICAgICAgICBleHByLnR5cGUgPSBcIkNsYXNzRGVjbGFyYXRpb25cIjticmVhaztcbiAgICAgIH1cbiAgICB9XG4gICAgbm9kZS5kZWNsYXJhdGlvbiA9IGV4cHI7XG4gICAgdGhpcy5zZW1pY29sb24oKTtcbiAgICByZXR1cm4gdGhpcy5maW5pc2hOb2RlKG5vZGUsIFwiRXhwb3J0RGVmYXVsdERlY2xhcmF0aW9uXCIpO1xuICB9XG4gIGlmICh0aGlzLnRvay50eXBlLmtleXdvcmQpIHtcbiAgICBub2RlLmRlY2xhcmF0aW9uID0gdGhpcy5wYXJzZVN0YXRlbWVudCgpO1xuICAgIG5vZGUuc3BlY2lmaWVycyA9IFtdO1xuICAgIG5vZGUuc291cmNlID0gbnVsbDtcbiAgfSBlbHNlIHtcbiAgICBub2RlLmRlY2xhcmF0aW9uID0gbnVsbDtcbiAgICBub2RlLnNwZWNpZmllcnMgPSB0aGlzLnBhcnNlRXhwb3J0U3BlY2lmaWVyTGlzdCgpO1xuICAgIG5vZGUuc291cmNlID0gdGhpcy5lYXRDb250ZXh0dWFsKFwiZnJvbVwiKSA/IHRoaXMucGFyc2VFeHByQXRvbSgpIDogbnVsbDtcbiAgICB0aGlzLnNlbWljb2xvbigpO1xuICB9XG4gIHJldHVybiB0aGlzLmZpbmlzaE5vZGUobm9kZSwgXCJFeHBvcnROYW1lZERlY2xhcmF0aW9uXCIpO1xufTtcblxubHAucGFyc2VJbXBvcnQgPSBmdW5jdGlvbiAoKSB7XG4gIHZhciBub2RlID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgdGhpcy5uZXh0KCk7XG4gIGlmICh0aGlzLnRvay50eXBlID09PSBfLnRva1R5cGVzLnN0cmluZykge1xuICAgIG5vZGUuc3BlY2lmaWVycyA9IFtdO1xuICAgIG5vZGUuc291cmNlID0gdGhpcy5wYXJzZUV4cHJBdG9tKCk7XG4gICAgbm9kZS5raW5kID0gJyc7XG4gIH0gZWxzZSB7XG4gICAgdmFyIGVsdCA9IHVuZGVmaW5lZDtcbiAgICBpZiAodGhpcy50b2sudHlwZSA9PT0gXy50b2tUeXBlcy5uYW1lICYmIHRoaXMudG9rLnZhbHVlICE9PSBcImZyb21cIikge1xuICAgICAgZWx0ID0gdGhpcy5zdGFydE5vZGUoKTtcbiAgICAgIGVsdC5sb2NhbCA9IHRoaXMucGFyc2VJZGVudCgpO1xuICAgICAgdGhpcy5maW5pc2hOb2RlKGVsdCwgXCJJbXBvcnREZWZhdWx0U3BlY2lmaWVyXCIpO1xuICAgICAgdGhpcy5lYXQoXy50b2tUeXBlcy5jb21tYSk7XG4gICAgfVxuICAgIG5vZGUuc3BlY2lmaWVycyA9IHRoaXMucGFyc2VJbXBvcnRTcGVjaWZpZXJMaXN0KCk7XG4gICAgbm9kZS5zb3VyY2UgPSB0aGlzLmVhdENvbnRleHR1YWwoXCJmcm9tXCIpID8gdGhpcy5wYXJzZUV4cHJBdG9tKCkgOiBudWxsO1xuICAgIGlmIChlbHQpIG5vZGUuc3BlY2lmaWVycy51bnNoaWZ0KGVsdCk7XG4gIH1cbiAgdGhpcy5zZW1pY29sb24oKTtcbiAgcmV0dXJuIHRoaXMuZmluaXNoTm9kZShub2RlLCBcIkltcG9ydERlY2xhcmF0aW9uXCIpO1xufTtcblxubHAucGFyc2VJbXBvcnRTcGVjaWZpZXJMaXN0ID0gZnVuY3Rpb24gKCkge1xuICB2YXIgZWx0cyA9IFtdO1xuICBpZiAodGhpcy50b2sudHlwZSA9PT0gXy50b2tUeXBlcy5zdGFyKSB7XG4gICAgdmFyIGVsdCA9IHRoaXMuc3RhcnROb2RlKCk7XG4gICAgdGhpcy5uZXh0KCk7XG4gICAgaWYgKHRoaXMuZWF0Q29udGV4dHVhbChcImFzXCIpKSBlbHQubG9jYWwgPSB0aGlzLnBhcnNlSWRlbnQoKTtcbiAgICBlbHRzLnB1c2godGhpcy5maW5pc2hOb2RlKGVsdCwgXCJJbXBvcnROYW1lc3BhY2VTcGVjaWZpZXJcIikpO1xuICB9IGVsc2Uge1xuICAgIHZhciBpbmRlbnQgPSB0aGlzLmN1ckluZGVudCxcbiAgICAgICAgbGluZSA9IHRoaXMuY3VyTGluZVN0YXJ0LFxuICAgICAgICBjb250aW51ZWRMaW5lID0gdGhpcy5uZXh0TGluZVN0YXJ0O1xuICAgIHRoaXMucHVzaEN4KCk7XG4gICAgdGhpcy5lYXQoXy50b2tUeXBlcy5icmFjZUwpO1xuICAgIGlmICh0aGlzLmN1ckxpbmVTdGFydCA+IGNvbnRpbnVlZExpbmUpIGNvbnRpbnVlZExpbmUgPSB0aGlzLmN1ckxpbmVTdGFydDtcbiAgICB3aGlsZSAoIXRoaXMuY2xvc2VzKF8udG9rVHlwZXMuYnJhY2VSLCBpbmRlbnQgKyAodGhpcy5jdXJMaW5lU3RhcnQgPD0gY29udGludWVkTGluZSA/IDEgOiAwKSwgbGluZSkpIHtcbiAgICAgIHZhciBlbHQgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICAgICAgaWYgKHRoaXMuZWF0KF8udG9rVHlwZXMuc3RhcikpIHtcbiAgICAgICAgaWYgKHRoaXMuZWF0Q29udGV4dHVhbChcImFzXCIpKSBlbHQubG9jYWwgPSB0aGlzLnBhcnNlSWRlbnQoKTtcbiAgICAgICAgdGhpcy5maW5pc2hOb2RlKGVsdCwgXCJJbXBvcnROYW1lc3BhY2VTcGVjaWZpZXJcIik7XG4gICAgICB9IGVsc2Uge1xuICAgICAgICBpZiAodGhpcy5pc0NvbnRleHR1YWwoXCJmcm9tXCIpKSBicmVhaztcbiAgICAgICAgZWx0LmltcG9ydGVkID0gdGhpcy5wYXJzZUlkZW50KCk7XG4gICAgICAgIGlmIChfcGFyc2V1dGlsLmlzRHVtbXkoZWx0LmltcG9ydGVkKSkgYnJlYWs7XG4gICAgICAgIGVsdC5sb2NhbCA9IHRoaXMuZWF0Q29udGV4dHVhbChcImFzXCIpID8gdGhpcy5wYXJzZUlkZW50KCkgOiBlbHQuaW1wb3J0ZWQ7XG4gICAgICAgIHRoaXMuZmluaXNoTm9kZShlbHQsIFwiSW1wb3J0U3BlY2lmaWVyXCIpO1xuICAgICAgfVxuICAgICAgZWx0cy5wdXNoKGVsdCk7XG4gICAgICB0aGlzLmVhdChfLnRva1R5cGVzLmNvbW1hKTtcbiAgICB9XG4gICAgdGhpcy5lYXQoXy50b2tUeXBlcy5icmFjZVIpO1xuICAgIHRoaXMucG9wQ3goKTtcbiAgfVxuICByZXR1cm4gZWx0cztcbn07XG5cbmxwLnBhcnNlRXhwb3J0U3BlY2lmaWVyTGlzdCA9IGZ1bmN0aW9uICgpIHtcbiAgdmFyIGVsdHMgPSBbXTtcbiAgdmFyIGluZGVudCA9IHRoaXMuY3VySW5kZW50LFxuICAgICAgbGluZSA9IHRoaXMuY3VyTGluZVN0YXJ0LFxuICAgICAgY29udGludWVkTGluZSA9IHRoaXMubmV4dExpbmVTdGFydDtcbiAgdGhpcy5wdXNoQ3goKTtcbiAgdGhpcy5lYXQoXy50b2tUeXBlcy5icmFjZUwpO1xuICBpZiAodGhpcy5jdXJMaW5lU3RhcnQgPiBjb250aW51ZWRMaW5lKSBjb250aW51ZWRMaW5lID0gdGhpcy5jdXJMaW5lU3RhcnQ7XG4gIHdoaWxlICghdGhpcy5jbG9zZXMoXy50b2tUeXBlcy5icmFjZVIsIGluZGVudCArICh0aGlzLmN1ckxpbmVTdGFydCA8PSBjb250aW51ZWRMaW5lID8gMSA6IDApLCBsaW5lKSkge1xuICAgIGlmICh0aGlzLmlzQ29udGV4dHVhbChcImZyb21cIikpIGJyZWFrO1xuICAgIHZhciBlbHQgPSB0aGlzLnN0YXJ0Tm9kZSgpO1xuICAgIGVsdC5sb2NhbCA9IHRoaXMucGFyc2VJZGVudCgpO1xuICAgIGlmIChfcGFyc2V1dGlsLmlzRHVtbXkoZWx0LmxvY2FsKSkgYnJlYWs7XG4gICAgZWx0LmV4cG9ydGVkID0gdGhpcy5lYXRDb250ZXh0dWFsKFwiYXNcIikgPyB0aGlzLnBhcnNlSWRlbnQoKSA6IGVsdC5sb2NhbDtcbiAgICB0aGlzLmZpbmlzaE5vZGUoZWx0LCBcIkV4cG9ydFNwZWNpZmllclwiKTtcbiAgICBlbHRzLnB1c2goZWx0KTtcbiAgICB0aGlzLmVhdChfLnRva1R5cGVzLmNvbW1hKTtcbiAgfVxuICB0aGlzLmVhdChfLnRva1R5cGVzLmJyYWNlUik7XG4gIHRoaXMucG9wQ3goKTtcbiAgcmV0dXJuIGVsdHM7XG59O1xuXG59LHtcIi4uXCI6MixcIi4vcGFyc2V1dGlsXCI6NSxcIi4vc3RhdGVcIjo2fV0sODpbZnVuY3Rpb24oX2RlcmVxXyxtb2R1bGUsZXhwb3J0cyl7XG5cInVzZSBzdHJpY3RcIjtcblxudmFyIF8gPSBfZGVyZXFfKFwiLi5cIik7XG5cbnZhciBfc3RhdGUgPSBfZGVyZXFfKFwiLi9zdGF0ZVwiKTtcblxudmFyIGxwID0gX3N0YXRlLkxvb3NlUGFyc2VyLnByb3RvdHlwZTtcblxuZnVuY3Rpb24gaXNTcGFjZShjaCkge1xuICByZXR1cm4gY2ggPCAxNCAmJiBjaCA+IDggfHwgY2ggPT09IDMyIHx8IGNoID09PSAxNjAgfHwgXy5pc05ld0xpbmUoY2gpO1xufVxuXG5scC5uZXh0ID0gZnVuY3Rpb24gKCkge1xuICB0aGlzLmxhc3QgPSB0aGlzLnRvaztcbiAgaWYgKHRoaXMuYWhlYWQubGVuZ3RoKSB0aGlzLnRvayA9IHRoaXMuYWhlYWQuc2hpZnQoKTtlbHNlIHRoaXMudG9rID0gdGhpcy5yZWFkVG9rZW4oKTtcblxuICBpZiAodGhpcy50b2suc3RhcnQgPj0gdGhpcy5uZXh0TGluZVN0YXJ0KSB7XG4gICAgd2hpbGUgKHRoaXMudG9rLnN0YXJ0ID49IHRoaXMubmV4dExpbmVTdGFydCkge1xuICAgICAgdGhpcy5jdXJMaW5lU3RhcnQgPSB0aGlzLm5leHRMaW5lU3RhcnQ7XG4gICAgICB0aGlzLm5leHRMaW5lU3RhcnQgPSB0aGlzLmxpbmVFbmQodGhpcy5jdXJMaW5lU3RhcnQpICsgMTtcbiAgICB9XG4gICAgdGhpcy5jdXJJbmRlbnQgPSB0aGlzLmluZGVudGF0aW9uQWZ0ZXIodGhpcy5jdXJMaW5lU3RhcnQpO1xuICB9XG59O1xuXG5scC5yZWFkVG9rZW4gPSBmdW5jdGlvbiAoKSB7XG4gIGZvciAoOzspIHtcbiAgICB0cnkge1xuICAgICAgdGhpcy50b2tzLm5leHQoKTtcbiAgICAgIGlmICh0aGlzLnRva3MudHlwZSA9PT0gXy50b2tUeXBlcy5kb3QgJiYgdGhpcy5pbnB1dC5zdWJzdHIodGhpcy50b2tzLmVuZCwgMSkgPT09IFwiLlwiICYmIHRoaXMub3B0aW9ucy5lY21hVmVyc2lvbiA+PSA2KSB7XG4gICAgICAgIHRoaXMudG9rcy5lbmQrKztcbiAgICAgICAgdGhpcy50b2tzLnR5cGUgPSBfLnRva1R5cGVzLmVsbGlwc2lzO1xuICAgICAgfVxuICAgICAgcmV0dXJuIG5ldyBfLlRva2VuKHRoaXMudG9rcyk7XG4gICAgfSBjYXRjaCAoZSkge1xuICAgICAgaWYgKCEoZSBpbnN0YW5jZW9mIFN5bnRheEVycm9yKSkgdGhyb3cgZTtcblxuICAgICAgLy8gVHJ5IHRvIHNraXAgc29tZSB0ZXh0LCBiYXNlZCBvbiB0aGUgZXJyb3IgbWVzc2FnZSwgYW5kIHRoZW4gY29udGludWVcbiAgICAgIHZhciBtc2cgPSBlLm1lc3NhZ2UsXG4gICAgICAgICAgcG9zID0gZS5yYWlzZWRBdCxcbiAgICAgICAgICByZXBsYWNlID0gdHJ1ZTtcbiAgICAgIGlmICgvdW50ZXJtaW5hdGVkL2kudGVzdChtc2cpKSB7XG4gICAgICAgIHBvcyA9IHRoaXMubGluZUVuZChlLnBvcyArIDEpO1xuICAgICAgICBpZiAoL3N0cmluZy8udGVzdChtc2cpKSB7XG4gICAgICAgICAgcmVwbGFjZSA9IHsgc3RhcnQ6IGUucG9zLCBlbmQ6IHBvcywgdHlwZTogXy50b2tUeXBlcy5zdHJpbmcsIHZhbHVlOiB0aGlzLmlucHV0LnNsaWNlKGUucG9zICsgMSwgcG9zKSB9O1xuICAgICAgICB9IGVsc2UgaWYgKC9yZWd1bGFyIGV4cHIvaS50ZXN0KG1zZykpIHtcbiAgICAgICAgICB2YXIgcmUgPSB0aGlzLmlucHV0LnNsaWNlKGUucG9zLCBwb3MpO1xuICAgICAgICAgIHRyeSB7XG4gICAgICAgICAgICByZSA9IG5ldyBSZWdFeHAocmUpO1xuICAgICAgICAgIH0gY2F0Y2ggKGUpIHt9XG4gICAgICAgICAgcmVwbGFjZSA9IHsgc3RhcnQ6IGUucG9zLCBlbmQ6IHBvcywgdHlwZTogXy50b2tUeXBlcy5yZWdleHAsIHZhbHVlOiByZSB9O1xuICAgICAgICB9IGVsc2UgaWYgKC90ZW1wbGF0ZS8udGVzdChtc2cpKSB7XG4gICAgICAgICAgcmVwbGFjZSA9IHsgc3RhcnQ6IGUucG9zLCBlbmQ6IHBvcyxcbiAgICAgICAgICAgIHR5cGU6IF8udG9rVHlwZXMudGVtcGxhdGUsXG4gICAgICAgICAgICB2YWx1ZTogdGhpcy5pbnB1dC5zbGljZShlLnBvcywgcG9zKSB9O1xuICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgIHJlcGxhY2UgPSBmYWxzZTtcbiAgICAgICAgfVxuICAgICAgfSBlbHNlIGlmICgvaW52YWxpZCAodW5pY29kZXxyZWdleHB8bnVtYmVyKXxleHBlY3RpbmcgdW5pY29kZXxvY3RhbCBsaXRlcmFsfGlzIHJlc2VydmVkfGRpcmVjdGx5IGFmdGVyIG51bWJlcnxleHBlY3RlZCBudW1iZXIgaW4gcmFkaXgvaS50ZXN0KG1zZykpIHtcbiAgICAgICAgd2hpbGUgKHBvcyA8IHRoaXMuaW5wdXQubGVuZ3RoICYmICFpc1NwYWNlKHRoaXMuaW5wdXQuY2hhckNvZGVBdChwb3MpKSkgKytwb3M7XG4gICAgICB9IGVsc2UgaWYgKC9jaGFyYWN0ZXIgZXNjYXBlfGV4cGVjdGVkIGhleGFkZWNpbWFsL2kudGVzdChtc2cpKSB7XG4gICAgICAgIHdoaWxlIChwb3MgPCB0aGlzLmlucHV0Lmxlbmd0aCkge1xuICAgICAgICAgIHZhciBjaCA9IHRoaXMuaW5wdXQuY2hhckNvZGVBdChwb3MrKyk7XG4gICAgICAgICAgaWYgKGNoID09PSAzNCB8fCBjaCA9PT0gMzkgfHwgXy5pc05ld0xpbmUoY2gpKSBicmVhaztcbiAgICAgICAgfVxuICAgICAgfSBlbHNlIGlmICgvdW5leHBlY3RlZCBjaGFyYWN0ZXIvaS50ZXN0KG1zZykpIHtcbiAgICAgICAgcG9zKys7XG4gICAgICAgIHJlcGxhY2UgPSBmYWxzZTtcbiAgICAgIH0gZWxzZSBpZiAoL3JlZ3VsYXIgZXhwcmVzc2lvbi9pLnRlc3QobXNnKSkge1xuICAgICAgICByZXBsYWNlID0gdHJ1ZTtcbiAgICAgIH0gZWxzZSB7XG4gICAgICAgIHRocm93IGU7XG4gICAgICB9XG4gICAgICB0aGlzLnJlc2V0VG8ocG9zKTtcbiAgICAgIGlmIChyZXBsYWNlID09PSB0cnVlKSByZXBsYWNlID0geyBzdGFydDogcG9zLCBlbmQ6IHBvcywgdHlwZTogXy50b2tUeXBlcy5uYW1lLCB2YWx1ZTogXCLinJZcIiB9O1xuICAgICAgaWYgKHJlcGxhY2UpIHtcbiAgICAgICAgaWYgKHRoaXMub3B0aW9ucy5sb2NhdGlvbnMpIHJlcGxhY2UubG9jID0gbmV3IF8uU291cmNlTG9jYXRpb24odGhpcy50b2tzLCBfLmdldExpbmVJbmZvKHRoaXMuaW5wdXQsIHJlcGxhY2Uuc3RhcnQpLCBfLmdldExpbmVJbmZvKHRoaXMuaW5wdXQsIHJlcGxhY2UuZW5kKSk7XG4gICAgICAgIHJldHVybiByZXBsYWNlO1xuICAgICAgfVxuICAgIH1cbiAgfVxufTtcblxubHAucmVzZXRUbyA9IGZ1bmN0aW9uIChwb3MpIHtcbiAgdGhpcy50b2tzLnBvcyA9IHBvcztcbiAgdmFyIGNoID0gdGhpcy5pbnB1dC5jaGFyQXQocG9zIC0gMSk7XG4gIHRoaXMudG9rcy5leHByQWxsb3dlZCA9ICFjaCB8fCAvW1xcW1xce1xcKCw7Oj9cXC8qPStcXC1+IXwmJV48Pl0vLnRlc3QoY2gpIHx8IC9bZW53ZmRdLy50ZXN0KGNoKSAmJiAvXFxiKGtleXdvcmRzfGNhc2V8ZWxzZXxyZXR1cm58dGhyb3d8bmV3fGlufChpbnN0YW5jZXx0eXBlKW9mfGRlbGV0ZXx2b2lkKSQvLnRlc3QodGhpcy5pbnB1dC5zbGljZShwb3MgLSAxMCwgcG9zKSk7XG5cbiAgaWYgKHRoaXMub3B0aW9ucy5sb2NhdGlvbnMpIHtcbiAgICB0aGlzLnRva3MuY3VyTGluZSA9IDE7XG4gICAgdGhpcy50b2tzLmxpbmVTdGFydCA9IF8ubGluZUJyZWFrRy5sYXN0SW5kZXggPSAwO1xuICAgIHZhciBtYXRjaCA9IHVuZGVmaW5lZDtcbiAgICB3aGlsZSAoKG1hdGNoID0gXy5saW5lQnJlYWtHLmV4ZWModGhpcy5pbnB1dCkpICYmIG1hdGNoLmluZGV4IDwgcG9zKSB7XG4gICAgICArK3RoaXMudG9rcy5jdXJMaW5lO1xuICAgICAgdGhpcy50b2tzLmxpbmVTdGFydCA9IG1hdGNoLmluZGV4ICsgbWF0Y2hbMF0ubGVuZ3RoO1xuICAgIH1cbiAgfVxufTtcblxubHAubG9va0FoZWFkID0gZnVuY3Rpb24gKG4pIHtcbiAgd2hpbGUgKG4gPiB0aGlzLmFoZWFkLmxlbmd0aCkgdGhpcy5haGVhZC5wdXNoKHRoaXMucmVhZFRva2VuKCkpO1xuICByZXR1cm4gdGhpcy5haGVhZFtuIC0gMV07XG59O1xuXG59LHtcIi4uXCI6MixcIi4vc3RhdGVcIjo2fV19LHt9LFs0XSkoNClcbn0pOyIsIihmdW5jdGlvbihmKXtpZih0eXBlb2YgZXhwb3J0cz09PVwib2JqZWN0XCImJnR5cGVvZiBtb2R1bGUhPT1cInVuZGVmaW5lZFwiKXttb2R1bGUuZXhwb3J0cz1mKCl9ZWxzZSBpZih0eXBlb2YgZGVmaW5lPT09XCJmdW5jdGlvblwiJiZkZWZpbmUuYW1kKXtkZWZpbmUoW10sZil9ZWxzZXt2YXIgZztpZih0eXBlb2Ygd2luZG93IT09XCJ1bmRlZmluZWRcIil7Zz13aW5kb3d9ZWxzZSBpZih0eXBlb2YgZ2xvYmFsIT09XCJ1bmRlZmluZWRcIil7Zz1nbG9iYWx9ZWxzZSBpZih0eXBlb2Ygc2VsZiE9PVwidW5kZWZpbmVkXCIpe2c9c2VsZn1lbHNle2c9dGhpc30oZy5hY29ybiB8fCAoZy5hY29ybiA9IHt9KSkud2FsayA9IGYoKX19KShmdW5jdGlvbigpe3ZhciBkZWZpbmUsbW9kdWxlLGV4cG9ydHM7cmV0dXJuIChmdW5jdGlvbiBlKHQsbixyKXtmdW5jdGlvbiBzKG8sdSl7aWYoIW5bb10pe2lmKCF0W29dKXt2YXIgYT10eXBlb2YgcmVxdWlyZT09XCJmdW5jdGlvblwiJiZyZXF1aXJlO2lmKCF1JiZhKXJldHVybiBhKG8sITApO2lmKGkpcmV0dXJuIGkobywhMCk7dmFyIGY9bmV3IEVycm9yKFwiQ2Fubm90IGZpbmQgbW9kdWxlICdcIitvK1wiJ1wiKTt0aHJvdyBmLmNvZGU9XCJNT0RVTEVfTk9UX0ZPVU5EXCIsZn12YXIgbD1uW29dPXtleHBvcnRzOnt9fTt0W29dWzBdLmNhbGwobC5leHBvcnRzLGZ1bmN0aW9uKGUpe3ZhciBuPXRbb11bMV1bZV07cmV0dXJuIHMobj9uOmUpfSxsLGwuZXhwb3J0cyxlLHQsbixyKX1yZXR1cm4gbltvXS5leHBvcnRzfXZhciBpPXR5cGVvZiByZXF1aXJlPT1cImZ1bmN0aW9uXCImJnJlcXVpcmU7Zm9yKHZhciBvPTA7bzxyLmxlbmd0aDtvKyspcyhyW29dKTtyZXR1cm4gc30pKHsxOltmdW5jdGlvbihfZGVyZXFfLG1vZHVsZSxleHBvcnRzKXtcbi8vIEFTVCB3YWxrZXIgbW9kdWxlIGZvciBNb3ppbGxhIFBhcnNlciBBUEkgY29tcGF0aWJsZSB0cmVlc1xuXG4vLyBBIHNpbXBsZSB3YWxrIGlzIG9uZSB3aGVyZSB5b3Ugc2ltcGx5IHNwZWNpZnkgY2FsbGJhY2tzIHRvIGJlXG4vLyBjYWxsZWQgb24gc3BlY2lmaWMgbm9kZXMuIFRoZSBsYXN0IHR3byBhcmd1bWVudHMgYXJlIG9wdGlvbmFsLiBBXG4vLyBzaW1wbGUgdXNlIHdvdWxkIGJlXG4vL1xuLy8gICAgIHdhbGsuc2ltcGxlKG15VHJlZSwge1xuLy8gICAgICAgICBFeHByZXNzaW9uOiBmdW5jdGlvbihub2RlKSB7IC4uLiB9XG4vLyAgICAgfSk7XG4vL1xuLy8gdG8gZG8gc29tZXRoaW5nIHdpdGggYWxsIGV4cHJlc3Npb25zLiBBbGwgUGFyc2VyIEFQSSBub2RlIHR5cGVzXG4vLyBjYW4gYmUgdXNlZCB0byBpZGVudGlmeSBub2RlIHR5cGVzLCBhcyB3ZWxsIGFzIEV4cHJlc3Npb24sXG4vLyBTdGF0ZW1lbnQsIGFuZCBTY29wZUJvZHksIHdoaWNoIGRlbm90ZSBjYXRlZ29yaWVzIG9mIG5vZGVzLlxuLy9cbi8vIFRoZSBiYXNlIGFyZ3VtZW50IGNhbiBiZSB1c2VkIHRvIHBhc3MgYSBjdXN0b20gKHJlY3Vyc2l2ZSlcbi8vIHdhbGtlciwgYW5kIHN0YXRlIGNhbiBiZSB1c2VkIHRvIGdpdmUgdGhpcyB3YWxrZWQgYW4gaW5pdGlhbFxuLy8gc3RhdGUuXG5cblwidXNlIHN0cmljdFwiO1xuXG5leHBvcnRzLl9fZXNNb2R1bGUgPSB0cnVlO1xuZXhwb3J0cy5zaW1wbGUgPSBzaW1wbGU7XG5leHBvcnRzLmFuY2VzdG9yID0gYW5jZXN0b3I7XG5leHBvcnRzLnJlY3Vyc2l2ZSA9IHJlY3Vyc2l2ZTtcbmV4cG9ydHMuZmluZE5vZGVBdCA9IGZpbmROb2RlQXQ7XG5leHBvcnRzLmZpbmROb2RlQXJvdW5kID0gZmluZE5vZGVBcm91bmQ7XG5leHBvcnRzLmZpbmROb2RlQWZ0ZXIgPSBmaW5kTm9kZUFmdGVyO1xuZXhwb3J0cy5maW5kTm9kZUJlZm9yZSA9IGZpbmROb2RlQmVmb3JlO1xuZXhwb3J0cy5tYWtlID0gbWFrZTtcblxuZnVuY3Rpb24gX2NsYXNzQ2FsbENoZWNrKGluc3RhbmNlLCBDb25zdHJ1Y3RvcikgeyBpZiAoIShpbnN0YW5jZSBpbnN0YW5jZW9mIENvbnN0cnVjdG9yKSkgeyB0aHJvdyBuZXcgVHlwZUVycm9yKFwiQ2Fubm90IGNhbGwgYSBjbGFzcyBhcyBhIGZ1bmN0aW9uXCIpOyB9IH1cblxuZnVuY3Rpb24gc2ltcGxlKG5vZGUsIHZpc2l0b3JzLCBiYXNlLCBzdGF0ZSwgb3ZlcnJpZGUpIHtcbiAgaWYgKCFiYXNlKSBiYXNlID0gZXhwb3J0cy5iYXNlOyhmdW5jdGlvbiBjKG5vZGUsIHN0LCBvdmVycmlkZSkge1xuICAgIHZhciB0eXBlID0gb3ZlcnJpZGUgfHwgbm9kZS50eXBlLFxuICAgICAgICBmb3VuZCA9IHZpc2l0b3JzW3R5cGVdO1xuICAgIGJhc2VbdHlwZV0obm9kZSwgc3QsIGMpO1xuICAgIGlmIChmb3VuZCkgZm91bmQobm9kZSwgc3QpO1xuICB9KShub2RlLCBzdGF0ZSwgb3ZlcnJpZGUpO1xufVxuXG4vLyBBbiBhbmNlc3RvciB3YWxrIGJ1aWxkcyB1cCBhbiBhcnJheSBvZiBhbmNlc3RvciBub2RlcyAoaW5jbHVkaW5nXG4vLyB0aGUgY3VycmVudCBub2RlKSBhbmQgcGFzc2VzIHRoZW0gdG8gdGhlIGNhbGxiYWNrIGFzIHRoZSBzdGF0ZSBwYXJhbWV0ZXIuXG5cbmZ1bmN0aW9uIGFuY2VzdG9yKG5vZGUsIHZpc2l0b3JzLCBiYXNlLCBzdGF0ZSkge1xuICBpZiAoIWJhc2UpIGJhc2UgPSBleHBvcnRzLmJhc2U7XG4gIGlmICghc3RhdGUpIHN0YXRlID0gW107KGZ1bmN0aW9uIGMobm9kZSwgc3QsIG92ZXJyaWRlKSB7XG4gICAgdmFyIHR5cGUgPSBvdmVycmlkZSB8fCBub2RlLnR5cGUsXG4gICAgICAgIGZvdW5kID0gdmlzaXRvcnNbdHlwZV07XG4gICAgaWYgKG5vZGUgIT0gc3Rbc3QubGVuZ3RoIC0gMV0pIHtcbiAgICAgIHN0ID0gc3Quc2xpY2UoKTtcbiAgICAgIHN0LnB1c2gobm9kZSk7XG4gICAgfVxuICAgIGJhc2VbdHlwZV0obm9kZSwgc3QsIGMpO1xuICAgIGlmIChmb3VuZCkgZm91bmQobm9kZSwgc3QpO1xuICB9KShub2RlLCBzdGF0ZSk7XG59XG5cbi8vIEEgcmVjdXJzaXZlIHdhbGsgaXMgb25lIHdoZXJlIHlvdXIgZnVuY3Rpb25zIG92ZXJyaWRlIHRoZSBkZWZhdWx0XG4vLyB3YWxrZXJzLiBUaGV5IGNhbiBtb2RpZnkgYW5kIHJlcGxhY2UgdGhlIHN0YXRlIHBhcmFtZXRlciB0aGF0J3Ncbi8vIHRocmVhZGVkIHRocm91Z2ggdGhlIHdhbGssIGFuZCBjYW4gb3B0IGhvdyBhbmQgd2hldGhlciB0byB3YWxrXG4vLyB0aGVpciBjaGlsZCBub2RlcyAoYnkgY2FsbGluZyB0aGVpciB0aGlyZCBhcmd1bWVudCBvbiB0aGVzZVxuLy8gbm9kZXMpLlxuXG5mdW5jdGlvbiByZWN1cnNpdmUobm9kZSwgc3RhdGUsIGZ1bmNzLCBiYXNlLCBvdmVycmlkZSkge1xuICB2YXIgdmlzaXRvciA9IGZ1bmNzID8gZXhwb3J0cy5tYWtlKGZ1bmNzLCBiYXNlKSA6IGJhc2U7KGZ1bmN0aW9uIGMobm9kZSwgc3QsIG92ZXJyaWRlKSB7XG4gICAgdmlzaXRvcltvdmVycmlkZSB8fCBub2RlLnR5cGVdKG5vZGUsIHN0LCBjKTtcbiAgfSkobm9kZSwgc3RhdGUsIG92ZXJyaWRlKTtcbn1cblxuZnVuY3Rpb24gbWFrZVRlc3QodGVzdCkge1xuICBpZiAodHlwZW9mIHRlc3QgPT0gXCJzdHJpbmdcIikgcmV0dXJuIGZ1bmN0aW9uICh0eXBlKSB7XG4gICAgcmV0dXJuIHR5cGUgPT0gdGVzdDtcbiAgfTtlbHNlIGlmICghdGVzdCkgcmV0dXJuIGZ1bmN0aW9uICgpIHtcbiAgICByZXR1cm4gdHJ1ZTtcbiAgfTtlbHNlIHJldHVybiB0ZXN0O1xufVxuXG52YXIgRm91bmQgPSBmdW5jdGlvbiBGb3VuZChub2RlLCBzdGF0ZSkge1xuICBfY2xhc3NDYWxsQ2hlY2sodGhpcywgRm91bmQpO1xuXG4gIHRoaXMubm9kZSA9IG5vZGU7dGhpcy5zdGF0ZSA9IHN0YXRlO1xufVxuXG4vLyBGaW5kIGEgbm9kZSB3aXRoIGEgZ2l2ZW4gc3RhcnQsIGVuZCwgYW5kIHR5cGUgKGFsbCBhcmUgb3B0aW9uYWwsXG4vLyBudWxsIGNhbiBiZSB1c2VkIGFzIHdpbGRjYXJkKS4gUmV0dXJucyBhIHtub2RlLCBzdGF0ZX0gb2JqZWN0LCBvclxuLy8gdW5kZWZpbmVkIHdoZW4gaXQgZG9lc24ndCBmaW5kIGEgbWF0Y2hpbmcgbm9kZS5cbjtcblxuZnVuY3Rpb24gZmluZE5vZGVBdChub2RlLCBzdGFydCwgZW5kLCB0ZXN0LCBiYXNlLCBzdGF0ZSkge1xuICB0ZXN0ID0gbWFrZVRlc3QodGVzdCk7XG4gIGlmICghYmFzZSkgYmFzZSA9IGV4cG9ydHMuYmFzZTtcbiAgdHJ5IHtcbiAgICA7KGZ1bmN0aW9uIGMobm9kZSwgc3QsIG92ZXJyaWRlKSB7XG4gICAgICB2YXIgdHlwZSA9IG92ZXJyaWRlIHx8IG5vZGUudHlwZTtcbiAgICAgIGlmICgoc3RhcnQgPT0gbnVsbCB8fCBub2RlLnN0YXJ0IDw9IHN0YXJ0KSAmJiAoZW5kID09IG51bGwgfHwgbm9kZS5lbmQgPj0gZW5kKSkgYmFzZVt0eXBlXShub2RlLCBzdCwgYyk7XG4gICAgICBpZiAodGVzdCh0eXBlLCBub2RlKSAmJiAoc3RhcnQgPT0gbnVsbCB8fCBub2RlLnN0YXJ0ID09IHN0YXJ0KSAmJiAoZW5kID09IG51bGwgfHwgbm9kZS5lbmQgPT0gZW5kKSkgdGhyb3cgbmV3IEZvdW5kKG5vZGUsIHN0KTtcbiAgICB9KShub2RlLCBzdGF0ZSk7XG4gIH0gY2F0Y2ggKGUpIHtcbiAgICBpZiAoZSBpbnN0YW5jZW9mIEZvdW5kKSByZXR1cm4gZTtcbiAgICB0aHJvdyBlO1xuICB9XG59XG5cbi8vIEZpbmQgdGhlIGlubmVybW9zdCBub2RlIG9mIGEgZ2l2ZW4gdHlwZSB0aGF0IGNvbnRhaW5zIHRoZSBnaXZlblxuLy8gcG9zaXRpb24uIEludGVyZmFjZSBzaW1pbGFyIHRvIGZpbmROb2RlQXQuXG5cbmZ1bmN0aW9uIGZpbmROb2RlQXJvdW5kKG5vZGUsIHBvcywgdGVzdCwgYmFzZSwgc3RhdGUpIHtcbiAgdGVzdCA9IG1ha2VUZXN0KHRlc3QpO1xuICBpZiAoIWJhc2UpIGJhc2UgPSBleHBvcnRzLmJhc2U7XG4gIHRyeSB7XG4gICAgOyhmdW5jdGlvbiBjKG5vZGUsIHN0LCBvdmVycmlkZSkge1xuICAgICAgdmFyIHR5cGUgPSBvdmVycmlkZSB8fCBub2RlLnR5cGU7XG4gICAgICBpZiAobm9kZS5zdGFydCA+IHBvcyB8fCBub2RlLmVuZCA8IHBvcykgcmV0dXJuO1xuICAgICAgYmFzZVt0eXBlXShub2RlLCBzdCwgYyk7XG4gICAgICBpZiAodGVzdCh0eXBlLCBub2RlKSkgdGhyb3cgbmV3IEZvdW5kKG5vZGUsIHN0KTtcbiAgICB9KShub2RlLCBzdGF0ZSk7XG4gIH0gY2F0Y2ggKGUpIHtcbiAgICBpZiAoZSBpbnN0YW5jZW9mIEZvdW5kKSByZXR1cm4gZTtcbiAgICB0aHJvdyBlO1xuICB9XG59XG5cbi8vIEZpbmQgdGhlIG91dGVybW9zdCBtYXRjaGluZyBub2RlIGFmdGVyIGEgZ2l2ZW4gcG9zaXRpb24uXG5cbmZ1bmN0aW9uIGZpbmROb2RlQWZ0ZXIobm9kZSwgcG9zLCB0ZXN0LCBiYXNlLCBzdGF0ZSkge1xuICB0ZXN0ID0gbWFrZVRlc3QodGVzdCk7XG4gIGlmICghYmFzZSkgYmFzZSA9IGV4cG9ydHMuYmFzZTtcbiAgdHJ5IHtcbiAgICA7KGZ1bmN0aW9uIGMobm9kZSwgc3QsIG92ZXJyaWRlKSB7XG4gICAgICBpZiAobm9kZS5lbmQgPCBwb3MpIHJldHVybjtcbiAgICAgIHZhciB0eXBlID0gb3ZlcnJpZGUgfHwgbm9kZS50eXBlO1xuICAgICAgaWYgKG5vZGUuc3RhcnQgPj0gcG9zICYmIHRlc3QodHlwZSwgbm9kZSkpIHRocm93IG5ldyBGb3VuZChub2RlLCBzdCk7XG4gICAgICBiYXNlW3R5cGVdKG5vZGUsIHN0LCBjKTtcbiAgICB9KShub2RlLCBzdGF0ZSk7XG4gIH0gY2F0Y2ggKGUpIHtcbiAgICBpZiAoZSBpbnN0YW5jZW9mIEZvdW5kKSByZXR1cm4gZTtcbiAgICB0aHJvdyBlO1xuICB9XG59XG5cbi8vIEZpbmQgdGhlIG91dGVybW9zdCBtYXRjaGluZyBub2RlIGJlZm9yZSBhIGdpdmVuIHBvc2l0aW9uLlxuXG5mdW5jdGlvbiBmaW5kTm9kZUJlZm9yZShub2RlLCBwb3MsIHRlc3QsIGJhc2UsIHN0YXRlKSB7XG4gIHRlc3QgPSBtYWtlVGVzdCh0ZXN0KTtcbiAgaWYgKCFiYXNlKSBiYXNlID0gZXhwb3J0cy5iYXNlO1xuICB2YXIgbWF4ID0gdW5kZWZpbmVkOyhmdW5jdGlvbiBjKG5vZGUsIHN0LCBvdmVycmlkZSkge1xuICAgIGlmIChub2RlLnN0YXJ0ID4gcG9zKSByZXR1cm47XG4gICAgdmFyIHR5cGUgPSBvdmVycmlkZSB8fCBub2RlLnR5cGU7XG4gICAgaWYgKG5vZGUuZW5kIDw9IHBvcyAmJiAoIW1heCB8fCBtYXgubm9kZS5lbmQgPCBub2RlLmVuZCkgJiYgdGVzdCh0eXBlLCBub2RlKSkgbWF4ID0gbmV3IEZvdW5kKG5vZGUsIHN0KTtcbiAgICBiYXNlW3R5cGVdKG5vZGUsIHN0LCBjKTtcbiAgfSkobm9kZSwgc3RhdGUpO1xuICByZXR1cm4gbWF4O1xufVxuXG4vLyBVc2VkIHRvIGNyZWF0ZSBhIGN1c3RvbSB3YWxrZXIuIFdpbGwgZmlsbCBpbiBhbGwgbWlzc2luZyBub2RlXG4vLyB0eXBlIHByb3BlcnRpZXMgd2l0aCB0aGUgZGVmYXVsdHMuXG5cbmZ1bmN0aW9uIG1ha2UoZnVuY3MsIGJhc2UpIHtcbiAgaWYgKCFiYXNlKSBiYXNlID0gZXhwb3J0cy5iYXNlO1xuICB2YXIgdmlzaXRvciA9IHt9O1xuICBmb3IgKHZhciB0eXBlIGluIGJhc2UpIHZpc2l0b3JbdHlwZV0gPSBiYXNlW3R5cGVdO1xuICBmb3IgKHZhciB0eXBlIGluIGZ1bmNzKSB2aXNpdG9yW3R5cGVdID0gZnVuY3NbdHlwZV07XG4gIHJldHVybiB2aXNpdG9yO1xufVxuXG5mdW5jdGlvbiBza2lwVGhyb3VnaChub2RlLCBzdCwgYykge1xuICBjKG5vZGUsIHN0KTtcbn1cbmZ1bmN0aW9uIGlnbm9yZShfbm9kZSwgX3N0LCBfYykge31cblxuLy8gTm9kZSB3YWxrZXJzLlxuXG52YXIgYmFzZSA9IHt9O1xuXG5leHBvcnRzLmJhc2UgPSBiYXNlO1xuYmFzZS5Qcm9ncmFtID0gYmFzZS5CbG9ja1N0YXRlbWVudCA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBmb3IgKHZhciBpID0gMDsgaSA8IG5vZGUuYm9keS5sZW5ndGg7ICsraSkge1xuICAgIGMobm9kZS5ib2R5W2ldLCBzdCwgXCJTdGF0ZW1lbnRcIik7XG4gIH1cbn07XG5iYXNlLlN0YXRlbWVudCA9IHNraXBUaHJvdWdoO1xuYmFzZS5FbXB0eVN0YXRlbWVudCA9IGlnbm9yZTtcbmJhc2UuRXhwcmVzc2lvblN0YXRlbWVudCA9IGJhc2UuUGFyZW50aGVzaXplZEV4cHJlc3Npb24gPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgcmV0dXJuIGMobm9kZS5leHByZXNzaW9uLCBzdCwgXCJFeHByZXNzaW9uXCIpO1xufTtcbmJhc2UuSWZTdGF0ZW1lbnQgPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgYyhub2RlLnRlc3QsIHN0LCBcIkV4cHJlc3Npb25cIik7XG4gIGMobm9kZS5jb25zZXF1ZW50LCBzdCwgXCJTdGF0ZW1lbnRcIik7XG4gIGlmIChub2RlLmFsdGVybmF0ZSkgYyhub2RlLmFsdGVybmF0ZSwgc3QsIFwiU3RhdGVtZW50XCIpO1xufTtcbmJhc2UuTGFiZWxlZFN0YXRlbWVudCA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICByZXR1cm4gYyhub2RlLmJvZHksIHN0LCBcIlN0YXRlbWVudFwiKTtcbn07XG5iYXNlLkJyZWFrU3RhdGVtZW50ID0gYmFzZS5Db250aW51ZVN0YXRlbWVudCA9IGlnbm9yZTtcbmJhc2UuV2l0aFN0YXRlbWVudCA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBjKG5vZGUub2JqZWN0LCBzdCwgXCJFeHByZXNzaW9uXCIpO1xuICBjKG5vZGUuYm9keSwgc3QsIFwiU3RhdGVtZW50XCIpO1xufTtcbmJhc2UuU3dpdGNoU3RhdGVtZW50ID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIGMobm9kZS5kaXNjcmltaW5hbnQsIHN0LCBcIkV4cHJlc3Npb25cIik7XG4gIGZvciAodmFyIGkgPSAwOyBpIDwgbm9kZS5jYXNlcy5sZW5ndGg7ICsraSkge1xuICAgIHZhciBjcyA9IG5vZGUuY2FzZXNbaV07XG4gICAgaWYgKGNzLnRlc3QpIGMoY3MudGVzdCwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbiAgICBmb3IgKHZhciBqID0gMDsgaiA8IGNzLmNvbnNlcXVlbnQubGVuZ3RoOyArK2opIHtcbiAgICAgIGMoY3MuY29uc2VxdWVudFtqXSwgc3QsIFwiU3RhdGVtZW50XCIpO1xuICAgIH1cbiAgfVxufTtcbmJhc2UuUmV0dXJuU3RhdGVtZW50ID0gYmFzZS5ZaWVsZEV4cHJlc3Npb24gPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgaWYgKG5vZGUuYXJndW1lbnQpIGMobm9kZS5hcmd1bWVudCwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbn07XG5iYXNlLlRocm93U3RhdGVtZW50ID0gYmFzZS5TcHJlYWRFbGVtZW50ID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIHJldHVybiBjKG5vZGUuYXJndW1lbnQsIHN0LCBcIkV4cHJlc3Npb25cIik7XG59O1xuYmFzZS5UcnlTdGF0ZW1lbnQgPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgYyhub2RlLmJsb2NrLCBzdCwgXCJTdGF0ZW1lbnRcIik7XG4gIGlmIChub2RlLmhhbmRsZXIpIHtcbiAgICBjKG5vZGUuaGFuZGxlci5wYXJhbSwgc3QsIFwiUGF0dGVyblwiKTtcbiAgICBjKG5vZGUuaGFuZGxlci5ib2R5LCBzdCwgXCJTY29wZUJvZHlcIik7XG4gIH1cbiAgaWYgKG5vZGUuZmluYWxpemVyKSBjKG5vZGUuZmluYWxpemVyLCBzdCwgXCJTdGF0ZW1lbnRcIik7XG59O1xuYmFzZS5XaGlsZVN0YXRlbWVudCA9IGJhc2UuRG9XaGlsZVN0YXRlbWVudCA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBjKG5vZGUudGVzdCwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbiAgYyhub2RlLmJvZHksIHN0LCBcIlN0YXRlbWVudFwiKTtcbn07XG5iYXNlLkZvclN0YXRlbWVudCA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBpZiAobm9kZS5pbml0KSBjKG5vZGUuaW5pdCwgc3QsIFwiRm9ySW5pdFwiKTtcbiAgaWYgKG5vZGUudGVzdCkgYyhub2RlLnRlc3QsIHN0LCBcIkV4cHJlc3Npb25cIik7XG4gIGlmIChub2RlLnVwZGF0ZSkgYyhub2RlLnVwZGF0ZSwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbiAgYyhub2RlLmJvZHksIHN0LCBcIlN0YXRlbWVudFwiKTtcbn07XG5iYXNlLkZvckluU3RhdGVtZW50ID0gYmFzZS5Gb3JPZlN0YXRlbWVudCA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBjKG5vZGUubGVmdCwgc3QsIFwiRm9ySW5pdFwiKTtcbiAgYyhub2RlLnJpZ2h0LCBzdCwgXCJFeHByZXNzaW9uXCIpO1xuICBjKG5vZGUuYm9keSwgc3QsIFwiU3RhdGVtZW50XCIpO1xufTtcbmJhc2UuRm9ySW5pdCA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBpZiAobm9kZS50eXBlID09IFwiVmFyaWFibGVEZWNsYXJhdGlvblwiKSBjKG5vZGUsIHN0KTtlbHNlIGMobm9kZSwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbn07XG5iYXNlLkRlYnVnZ2VyU3RhdGVtZW50ID0gaWdub3JlO1xuXG5iYXNlLkZ1bmN0aW9uRGVjbGFyYXRpb24gPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgcmV0dXJuIGMobm9kZSwgc3QsIFwiRnVuY3Rpb25cIik7XG59O1xuYmFzZS5WYXJpYWJsZURlY2xhcmF0aW9uID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIGZvciAodmFyIGkgPSAwOyBpIDwgbm9kZS5kZWNsYXJhdGlvbnMubGVuZ3RoOyArK2kpIHtcbiAgICB2YXIgZGVjbCA9IG5vZGUuZGVjbGFyYXRpb25zW2ldO1xuICAgIGMoZGVjbC5pZCwgc3QsIFwiUGF0dGVyblwiKTtcbiAgICBpZiAoZGVjbC5pbml0KSBjKGRlY2wuaW5pdCwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbiAgfVxufTtcblxuYmFzZS5GdW5jdGlvbiA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBmb3IgKHZhciBpID0gMDsgaSA8IG5vZGUucGFyYW1zLmxlbmd0aDsgaSsrKSB7XG4gICAgYyhub2RlLnBhcmFtc1tpXSwgc3QsIFwiUGF0dGVyblwiKTtcbiAgfWMobm9kZS5ib2R5LCBzdCwgbm9kZS5leHByZXNzaW9uID8gXCJTY29wZUV4cHJlc3Npb25cIiA6IFwiU2NvcGVCb2R5XCIpO1xufTtcbi8vIEZJWE1FIGRyb3AgdGhlc2Ugbm9kZSB0eXBlcyBpbiBuZXh0IG1ham9yIHZlcnNpb25cbi8vIChUaGV5IGFyZSBhd2t3YXJkLCBhbmQgaW4gRVM2IGV2ZXJ5IGJsb2NrIGNhbiBiZSBhIHNjb3BlLilcbmJhc2UuU2NvcGVCb2R5ID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIHJldHVybiBjKG5vZGUsIHN0LCBcIlN0YXRlbWVudFwiKTtcbn07XG5iYXNlLlNjb3BlRXhwcmVzc2lvbiA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICByZXR1cm4gYyhub2RlLCBzdCwgXCJFeHByZXNzaW9uXCIpO1xufTtcblxuYmFzZS5QYXR0ZXJuID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIGlmIChub2RlLnR5cGUgPT0gXCJJZGVudGlmaWVyXCIpIGMobm9kZSwgc3QsIFwiVmFyaWFibGVQYXR0ZXJuXCIpO2Vsc2UgaWYgKG5vZGUudHlwZSA9PSBcIk1lbWJlckV4cHJlc3Npb25cIikgYyhub2RlLCBzdCwgXCJNZW1iZXJQYXR0ZXJuXCIpO2Vsc2UgYyhub2RlLCBzdCk7XG59O1xuYmFzZS5WYXJpYWJsZVBhdHRlcm4gPSBpZ25vcmU7XG5iYXNlLk1lbWJlclBhdHRlcm4gPSBza2lwVGhyb3VnaDtcbmJhc2UuUmVzdEVsZW1lbnQgPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgcmV0dXJuIGMobm9kZS5hcmd1bWVudCwgc3QsIFwiUGF0dGVyblwiKTtcbn07XG5iYXNlLkFycmF5UGF0dGVybiA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBmb3IgKHZhciBpID0gMDsgaSA8IG5vZGUuZWxlbWVudHMubGVuZ3RoOyArK2kpIHtcbiAgICB2YXIgZWx0ID0gbm9kZS5lbGVtZW50c1tpXTtcbiAgICBpZiAoZWx0KSBjKGVsdCwgc3QsIFwiUGF0dGVyblwiKTtcbiAgfVxufTtcbmJhc2UuT2JqZWN0UGF0dGVybiA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBmb3IgKHZhciBpID0gMDsgaSA8IG5vZGUucHJvcGVydGllcy5sZW5ndGg7ICsraSkge1xuICAgIGMobm9kZS5wcm9wZXJ0aWVzW2ldLnZhbHVlLCBzdCwgXCJQYXR0ZXJuXCIpO1xuICB9XG59O1xuXG5iYXNlLkV4cHJlc3Npb24gPSBza2lwVGhyb3VnaDtcbmJhc2UuVGhpc0V4cHJlc3Npb24gPSBiYXNlLlN1cGVyID0gYmFzZS5NZXRhUHJvcGVydHkgPSBpZ25vcmU7XG5iYXNlLkFycmF5RXhwcmVzc2lvbiA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBmb3IgKHZhciBpID0gMDsgaSA8IG5vZGUuZWxlbWVudHMubGVuZ3RoOyArK2kpIHtcbiAgICB2YXIgZWx0ID0gbm9kZS5lbGVtZW50c1tpXTtcbiAgICBpZiAoZWx0KSBjKGVsdCwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbiAgfVxufTtcbmJhc2UuT2JqZWN0RXhwcmVzc2lvbiA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBmb3IgKHZhciBpID0gMDsgaSA8IG5vZGUucHJvcGVydGllcy5sZW5ndGg7ICsraSkge1xuICAgIGMobm9kZS5wcm9wZXJ0aWVzW2ldLCBzdCk7XG4gIH1cbn07XG5iYXNlLkZ1bmN0aW9uRXhwcmVzc2lvbiA9IGJhc2UuQXJyb3dGdW5jdGlvbkV4cHJlc3Npb24gPSBiYXNlLkZ1bmN0aW9uRGVjbGFyYXRpb247XG5iYXNlLlNlcXVlbmNlRXhwcmVzc2lvbiA9IGJhc2UuVGVtcGxhdGVMaXRlcmFsID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIGZvciAodmFyIGkgPSAwOyBpIDwgbm9kZS5leHByZXNzaW9ucy5sZW5ndGg7ICsraSkge1xuICAgIGMobm9kZS5leHByZXNzaW9uc1tpXSwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbiAgfVxufTtcbmJhc2UuVW5hcnlFeHByZXNzaW9uID0gYmFzZS5VcGRhdGVFeHByZXNzaW9uID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIGMobm9kZS5hcmd1bWVudCwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbn07XG5iYXNlLkJpbmFyeUV4cHJlc3Npb24gPSBiYXNlLkxvZ2ljYWxFeHByZXNzaW9uID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIGMobm9kZS5sZWZ0LCBzdCwgXCJFeHByZXNzaW9uXCIpO1xuICBjKG5vZGUucmlnaHQsIHN0LCBcIkV4cHJlc3Npb25cIik7XG59O1xuYmFzZS5Bc3NpZ25tZW50RXhwcmVzc2lvbiA9IGJhc2UuQXNzaWdubWVudFBhdHRlcm4gPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgYyhub2RlLmxlZnQsIHN0LCBcIlBhdHRlcm5cIik7XG4gIGMobm9kZS5yaWdodCwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbn07XG5iYXNlLkNvbmRpdGlvbmFsRXhwcmVzc2lvbiA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBjKG5vZGUudGVzdCwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbiAgYyhub2RlLmNvbnNlcXVlbnQsIHN0LCBcIkV4cHJlc3Npb25cIik7XG4gIGMobm9kZS5hbHRlcm5hdGUsIHN0LCBcIkV4cHJlc3Npb25cIik7XG59O1xuYmFzZS5OZXdFeHByZXNzaW9uID0gYmFzZS5DYWxsRXhwcmVzc2lvbiA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBjKG5vZGUuY2FsbGVlLCBzdCwgXCJFeHByZXNzaW9uXCIpO1xuICBpZiAobm9kZS5hcmd1bWVudHMpIGZvciAodmFyIGkgPSAwOyBpIDwgbm9kZS5hcmd1bWVudHMubGVuZ3RoOyArK2kpIHtcbiAgICBjKG5vZGUuYXJndW1lbnRzW2ldLCBzdCwgXCJFeHByZXNzaW9uXCIpO1xuICB9XG59O1xuYmFzZS5NZW1iZXJFeHByZXNzaW9uID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIGMobm9kZS5vYmplY3QsIHN0LCBcIkV4cHJlc3Npb25cIik7XG4gIGlmIChub2RlLmNvbXB1dGVkKSBjKG5vZGUucHJvcGVydHksIHN0LCBcIkV4cHJlc3Npb25cIik7XG59O1xuYmFzZS5FeHBvcnROYW1lZERlY2xhcmF0aW9uID0gYmFzZS5FeHBvcnREZWZhdWx0RGVjbGFyYXRpb24gPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgaWYgKG5vZGUuZGVjbGFyYXRpb24pIGMobm9kZS5kZWNsYXJhdGlvbiwgc3QpO1xufTtcbmJhc2UuSW1wb3J0RGVjbGFyYXRpb24gPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgZm9yICh2YXIgaSA9IDA7IGkgPCBub2RlLnNwZWNpZmllcnMubGVuZ3RoOyBpKyspIHtcbiAgICBjKG5vZGUuc3BlY2lmaWVyc1tpXSwgc3QpO1xuICB9XG59O1xuYmFzZS5JbXBvcnRTcGVjaWZpZXIgPSBiYXNlLkltcG9ydERlZmF1bHRTcGVjaWZpZXIgPSBiYXNlLkltcG9ydE5hbWVzcGFjZVNwZWNpZmllciA9IGJhc2UuSWRlbnRpZmllciA9IGJhc2UuTGl0ZXJhbCA9IGlnbm9yZTtcblxuYmFzZS5UYWdnZWRUZW1wbGF0ZUV4cHJlc3Npb24gPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgYyhub2RlLnRhZywgc3QsIFwiRXhwcmVzc2lvblwiKTtcbiAgYyhub2RlLnF1YXNpLCBzdCk7XG59O1xuYmFzZS5DbGFzc0RlY2xhcmF0aW9uID0gYmFzZS5DbGFzc0V4cHJlc3Npb24gPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgcmV0dXJuIGMobm9kZSwgc3QsIFwiQ2xhc3NcIik7XG59O1xuYmFzZS5DbGFzcyA9IGZ1bmN0aW9uIChub2RlLCBzdCwgYykge1xuICBpZiAobm9kZS5pZCkgYyhub2RlLmlkLCBzdCwgXCJQYXR0ZXJuXCIpO1xuICBpZiAobm9kZS5zdXBlckNsYXNzKSBjKG5vZGUuc3VwZXJDbGFzcywgc3QsIFwiRXhwcmVzc2lvblwiKTtcbiAgZm9yICh2YXIgaSA9IDA7IGkgPCBub2RlLmJvZHkuYm9keS5sZW5ndGg7IGkrKykge1xuICAgIGMobm9kZS5ib2R5LmJvZHlbaV0sIHN0KTtcbiAgfVxufTtcbmJhc2UuTWV0aG9kRGVmaW5pdGlvbiA9IGJhc2UuUHJvcGVydHkgPSBmdW5jdGlvbiAobm9kZSwgc3QsIGMpIHtcbiAgaWYgKG5vZGUuY29tcHV0ZWQpIGMobm9kZS5rZXksIHN0LCBcIkV4cHJlc3Npb25cIik7XG4gIGMobm9kZS52YWx1ZSwgc3QsIFwiRXhwcmVzc2lvblwiKTtcbn07XG5iYXNlLkNvbXByZWhlbnNpb25FeHByZXNzaW9uID0gZnVuY3Rpb24gKG5vZGUsIHN0LCBjKSB7XG4gIGZvciAodmFyIGkgPSAwOyBpIDwgbm9kZS5ibG9ja3MubGVuZ3RoOyBpKyspIHtcbiAgICBjKG5vZGUuYmxvY2tzW2ldLnJpZ2h0LCBzdCwgXCJFeHByZXNzaW9uXCIpO1xuICB9Yyhub2RlLmJvZHksIHN0LCBcIkV4cHJlc3Npb25cIik7XG59O1xuXG59LHt9XX0se30sWzFdKSgxKVxufSk7IiwiaWYgKHR5cGVvZiBPYmplY3QuY3JlYXRlID09PSAnZnVuY3Rpb24nKSB7XG4gIC8vIGltcGxlbWVudGF0aW9uIGZyb20gc3RhbmRhcmQgbm9kZS5qcyAndXRpbCcgbW9kdWxlXG4gIG1vZHVsZS5leHBvcnRzID0gZnVuY3Rpb24gaW5oZXJpdHMoY3Rvciwgc3VwZXJDdG9yKSB7XG4gICAgY3Rvci5zdXBlcl8gPSBzdXBlckN0b3JcbiAgICBjdG9yLnByb3RvdHlwZSA9IE9iamVjdC5jcmVhdGUoc3VwZXJDdG9yLnByb3RvdHlwZSwge1xuICAgICAgY29uc3RydWN0b3I6IHtcbiAgICAgICAgdmFsdWU6IGN0b3IsXG4gICAgICAgIGVudW1lcmFibGU6IGZhbHNlLFxuICAgICAgICB3cml0YWJsZTogdHJ1ZSxcbiAgICAgICAgY29uZmlndXJhYmxlOiB0cnVlXG4gICAgICB9XG4gICAgfSk7XG4gIH07XG59IGVsc2Uge1xuICAvLyBvbGQgc2Nob29sIHNoaW0gZm9yIG9sZCBicm93c2Vyc1xuICBtb2R1bGUuZXhwb3J0cyA9IGZ1bmN0aW9uIGluaGVyaXRzKGN0b3IsIHN1cGVyQ3Rvcikge1xuICAgIGN0b3Iuc3VwZXJfID0gc3VwZXJDdG9yXG4gICAgdmFyIFRlbXBDdG9yID0gZnVuY3Rpb24gKCkge31cbiAgICBUZW1wQ3Rvci5wcm90b3R5cGUgPSBzdXBlckN0b3IucHJvdG90eXBlXG4gICAgY3Rvci5wcm90b3R5cGUgPSBuZXcgVGVtcEN0b3IoKVxuICAgIGN0b3IucHJvdG90eXBlLmNvbnN0cnVjdG9yID0gY3RvclxuICB9XG59XG4iLCIvLyBzaGltIGZvciB1c2luZyBwcm9jZXNzIGluIGJyb3dzZXJcblxudmFyIHByb2Nlc3MgPSBtb2R1bGUuZXhwb3J0cyA9IHt9O1xudmFyIHF1ZXVlID0gW107XG52YXIgZHJhaW5pbmcgPSBmYWxzZTtcbnZhciBjdXJyZW50UXVldWU7XG52YXIgcXVldWVJbmRleCA9IC0xO1xuXG5mdW5jdGlvbiBjbGVhblVwTmV4dFRpY2soKSB7XG4gICAgZHJhaW5pbmcgPSBmYWxzZTtcbiAgICBpZiAoY3VycmVudFF1ZXVlLmxlbmd0aCkge1xuICAgICAgICBxdWV1ZSA9IGN1cnJlbnRRdWV1ZS5jb25jYXQocXVldWUpO1xuICAgIH0gZWxzZSB7XG4gICAgICAgIHF1ZXVlSW5kZXggPSAtMTtcbiAgICB9XG4gICAgaWYgKHF1ZXVlLmxlbmd0aCkge1xuICAgICAgICBkcmFpblF1ZXVlKCk7XG4gICAgfVxufVxuXG5mdW5jdGlvbiBkcmFpblF1ZXVlKCkge1xuICAgIGlmIChkcmFpbmluZykge1xuICAgICAgICByZXR1cm47XG4gICAgfVxuICAgIHZhciB0aW1lb3V0ID0gc2V0VGltZW91dChjbGVhblVwTmV4dFRpY2spO1xuICAgIGRyYWluaW5nID0gdHJ1ZTtcblxuICAgIHZhciBsZW4gPSBxdWV1ZS5sZW5ndGg7XG4gICAgd2hpbGUobGVuKSB7XG4gICAgICAgIGN1cnJlbnRRdWV1ZSA9IHF1ZXVlO1xuICAgICAgICBxdWV1ZSA9IFtdO1xuICAgICAgICB3aGlsZSAoKytxdWV1ZUluZGV4IDwgbGVuKSB7XG4gICAgICAgICAgICBjdXJyZW50UXVldWVbcXVldWVJbmRleF0ucnVuKCk7XG4gICAgICAgIH1cbiAgICAgICAgcXVldWVJbmRleCA9IC0xO1xuICAgICAgICBsZW4gPSBxdWV1ZS5sZW5ndGg7XG4gICAgfVxuICAgIGN1cnJlbnRRdWV1ZSA9IG51bGw7XG4gICAgZHJhaW5pbmcgPSBmYWxzZTtcbiAgICBjbGVhclRpbWVvdXQodGltZW91dCk7XG59XG5cbnByb2Nlc3MubmV4dFRpY2sgPSBmdW5jdGlvbiAoZnVuKSB7XG4gICAgdmFyIGFyZ3MgPSBuZXcgQXJyYXkoYXJndW1lbnRzLmxlbmd0aCAtIDEpO1xuICAgIGlmIChhcmd1bWVudHMubGVuZ3RoID4gMSkge1xuICAgICAgICBmb3IgKHZhciBpID0gMTsgaSA8IGFyZ3VtZW50cy5sZW5ndGg7IGkrKykge1xuICAgICAgICAgICAgYXJnc1tpIC0gMV0gPSBhcmd1bWVudHNbaV07XG4gICAgICAgIH1cbiAgICB9XG4gICAgcXVldWUucHVzaChuZXcgSXRlbShmdW4sIGFyZ3MpKTtcbiAgICBpZiAocXVldWUubGVuZ3RoID09PSAxICYmICFkcmFpbmluZykge1xuICAgICAgICBzZXRUaW1lb3V0KGRyYWluUXVldWUsIDApO1xuICAgIH1cbn07XG5cbi8vIHY4IGxpa2VzIHByZWRpY3RpYmxlIG9iamVjdHNcbmZ1bmN0aW9uIEl0ZW0oZnVuLCBhcnJheSkge1xuICAgIHRoaXMuZnVuID0gZnVuO1xuICAgIHRoaXMuYXJyYXkgPSBhcnJheTtcbn1cbkl0ZW0ucHJvdG90eXBlLnJ1biA9IGZ1bmN0aW9uICgpIHtcbiAgICB0aGlzLmZ1bi5hcHBseShudWxsLCB0aGlzLmFycmF5KTtcbn07XG5wcm9jZXNzLnRpdGxlID0gJ2Jyb3dzZXInO1xucHJvY2Vzcy5icm93c2VyID0gdHJ1ZTtcbnByb2Nlc3MuZW52ID0ge307XG5wcm9jZXNzLmFyZ3YgPSBbXTtcbnByb2Nlc3MudmVyc2lvbiA9ICcnOyAvLyBlbXB0eSBzdHJpbmcgdG8gYXZvaWQgcmVnZXhwIGlzc3Vlc1xucHJvY2Vzcy52ZXJzaW9ucyA9IHt9O1xuXG5mdW5jdGlvbiBub29wKCkge31cblxucHJvY2Vzcy5vbiA9IG5vb3A7XG5wcm9jZXNzLmFkZExpc3RlbmVyID0gbm9vcDtcbnByb2Nlc3Mub25jZSA9IG5vb3A7XG5wcm9jZXNzLm9mZiA9IG5vb3A7XG5wcm9jZXNzLnJlbW92ZUxpc3RlbmVyID0gbm9vcDtcbnByb2Nlc3MucmVtb3ZlQWxsTGlzdGVuZXJzID0gbm9vcDtcbnByb2Nlc3MuZW1pdCA9IG5vb3A7XG5cbnByb2Nlc3MuYmluZGluZyA9IGZ1bmN0aW9uIChuYW1lKSB7XG4gICAgdGhyb3cgbmV3IEVycm9yKCdwcm9jZXNzLmJpbmRpbmcgaXMgbm90IHN1cHBvcnRlZCcpO1xufTtcblxuLy8gVE9ETyhzaHR5bG1hbilcbnByb2Nlc3MuY3dkID0gZnVuY3Rpb24gKCkgeyByZXR1cm4gJy8nIH07XG5wcm9jZXNzLmNoZGlyID0gZnVuY3Rpb24gKGRpcikge1xuICAgIHRocm93IG5ldyBFcnJvcigncHJvY2Vzcy5jaGRpciBpcyBub3Qgc3VwcG9ydGVkJyk7XG59O1xucHJvY2Vzcy51bWFzayA9IGZ1bmN0aW9uKCkgeyByZXR1cm4gMDsgfTtcbiIsIm1vZHVsZS5leHBvcnRzID0gZnVuY3Rpb24gaXNCdWZmZXIoYXJnKSB7XG4gIHJldHVybiBhcmcgJiYgdHlwZW9mIGFyZyA9PT0gJ29iamVjdCdcbiAgICAmJiB0eXBlb2YgYXJnLmNvcHkgPT09ICdmdW5jdGlvbidcbiAgICAmJiB0eXBlb2YgYXJnLmZpbGwgPT09ICdmdW5jdGlvbidcbiAgICAmJiB0eXBlb2YgYXJnLnJlYWRVSW50OCA9PT0gJ2Z1bmN0aW9uJztcbn0iLCIvLyBDb3B5cmlnaHQgSm95ZW50LCBJbmMuIGFuZCBvdGhlciBOb2RlIGNvbnRyaWJ1dG9ycy5cbi8vXG4vLyBQZXJtaXNzaW9uIGlzIGhlcmVieSBncmFudGVkLCBmcmVlIG9mIGNoYXJnZSwgdG8gYW55IHBlcnNvbiBvYnRhaW5pbmcgYVxuLy8gY29weSBvZiB0aGlzIHNvZnR3YXJlIGFuZCBhc3NvY2lhdGVkIGRvY3VtZW50YXRpb24gZmlsZXMgKHRoZVxuLy8gXCJTb2Z0d2FyZVwiKSwgdG8gZGVhbCBpbiB0aGUgU29mdHdhcmUgd2l0aG91dCByZXN0cmljdGlvbiwgaW5jbHVkaW5nXG4vLyB3aXRob3V0IGxpbWl0YXRpb24gdGhlIHJpZ2h0cyB0byB1c2UsIGNvcHksIG1vZGlmeSwgbWVyZ2UsIHB1Ymxpc2gsXG4vLyBkaXN0cmlidXRlLCBzdWJsaWNlbnNlLCBhbmQvb3Igc2VsbCBjb3BpZXMgb2YgdGhlIFNvZnR3YXJlLCBhbmQgdG8gcGVybWl0XG4vLyBwZXJzb25zIHRvIHdob20gdGhlIFNvZnR3YXJlIGlzIGZ1cm5pc2hlZCB0byBkbyBzbywgc3ViamVjdCB0byB0aGVcbi8vIGZvbGxvd2luZyBjb25kaXRpb25zOlxuLy9cbi8vIFRoZSBhYm92ZSBjb3B5cmlnaHQgbm90aWNlIGFuZCB0aGlzIHBlcm1pc3Npb24gbm90aWNlIHNoYWxsIGJlIGluY2x1ZGVkXG4vLyBpbiBhbGwgY29waWVzIG9yIHN1YnN0YW50aWFsIHBvcnRpb25zIG9mIHRoZSBTb2Z0d2FyZS5cbi8vXG4vLyBUSEUgU09GVFdBUkUgSVMgUFJPVklERUQgXCJBUyBJU1wiLCBXSVRIT1VUIFdBUlJBTlRZIE9GIEFOWSBLSU5ELCBFWFBSRVNTXG4vLyBPUiBJTVBMSUVELCBJTkNMVURJTkcgQlVUIE5PVCBMSU1JVEVEIFRPIFRIRSBXQVJSQU5USUVTIE9GXG4vLyBNRVJDSEFOVEFCSUxJVFksIEZJVE5FU1MgRk9SIEEgUEFSVElDVUxBUiBQVVJQT1NFIEFORCBOT05JTkZSSU5HRU1FTlQuIElOXG4vLyBOTyBFVkVOVCBTSEFMTCBUSEUgQVVUSE9SUyBPUiBDT1BZUklHSFQgSE9MREVSUyBCRSBMSUFCTEUgRk9SIEFOWSBDTEFJTSxcbi8vIERBTUFHRVMgT1IgT1RIRVIgTElBQklMSVRZLCBXSEVUSEVSIElOIEFOIEFDVElPTiBPRiBDT05UUkFDVCwgVE9SVCBPUlxuLy8gT1RIRVJXSVNFLCBBUklTSU5HIEZST00sIE9VVCBPRiBPUiBJTiBDT05ORUNUSU9OIFdJVEggVEhFIFNPRlRXQVJFIE9SIFRIRVxuLy8gVVNFIE9SIE9USEVSIERFQUxJTkdTIElOIFRIRSBTT0ZUV0FSRS5cblxudmFyIGZvcm1hdFJlZ0V4cCA9IC8lW3NkaiVdL2c7XG5leHBvcnRzLmZvcm1hdCA9IGZ1bmN0aW9uKGYpIHtcbiAgaWYgKCFpc1N0cmluZyhmKSkge1xuICAgIHZhciBvYmplY3RzID0gW107XG4gICAgZm9yICh2YXIgaSA9IDA7IGkgPCBhcmd1bWVudHMubGVuZ3RoOyBpKyspIHtcbiAgICAgIG9iamVjdHMucHVzaChpbnNwZWN0KGFyZ3VtZW50c1tpXSkpO1xuICAgIH1cbiAgICByZXR1cm4gb2JqZWN0cy5qb2luKCcgJyk7XG4gIH1cblxuICB2YXIgaSA9IDE7XG4gIHZhciBhcmdzID0gYXJndW1lbnRzO1xuICB2YXIgbGVuID0gYXJncy5sZW5ndGg7XG4gIHZhciBzdHIgPSBTdHJpbmcoZikucmVwbGFjZShmb3JtYXRSZWdFeHAsIGZ1bmN0aW9uKHgpIHtcbiAgICBpZiAoeCA9PT0gJyUlJykgcmV0dXJuICclJztcbiAgICBpZiAoaSA+PSBsZW4pIHJldHVybiB4O1xuICAgIHN3aXRjaCAoeCkge1xuICAgICAgY2FzZSAnJXMnOiByZXR1cm4gU3RyaW5nKGFyZ3NbaSsrXSk7XG4gICAgICBjYXNlICclZCc6IHJldHVybiBOdW1iZXIoYXJnc1tpKytdKTtcbiAgICAgIGNhc2UgJyVqJzpcbiAgICAgICAgdHJ5IHtcbiAgICAgICAgICByZXR1cm4gSlNPTi5zdHJpbmdpZnkoYXJnc1tpKytdKTtcbiAgICAgICAgfSBjYXRjaCAoXykge1xuICAgICAgICAgIHJldHVybiAnW0NpcmN1bGFyXSc7XG4gICAgICAgIH1cbiAgICAgIGRlZmF1bHQ6XG4gICAgICAgIHJldHVybiB4O1xuICAgIH1cbiAgfSk7XG4gIGZvciAodmFyIHggPSBhcmdzW2ldOyBpIDwgbGVuOyB4ID0gYXJnc1srK2ldKSB7XG4gICAgaWYgKGlzTnVsbCh4KSB8fCAhaXNPYmplY3QoeCkpIHtcbiAgICAgIHN0ciArPSAnICcgKyB4O1xuICAgIH0gZWxzZSB7XG4gICAgICBzdHIgKz0gJyAnICsgaW5zcGVjdCh4KTtcbiAgICB9XG4gIH1cbiAgcmV0dXJuIHN0cjtcbn07XG5cblxuLy8gTWFyayB0aGF0IGEgbWV0aG9kIHNob3VsZCBub3QgYmUgdXNlZC5cbi8vIFJldHVybnMgYSBtb2RpZmllZCBmdW5jdGlvbiB3aGljaCB3YXJucyBvbmNlIGJ5IGRlZmF1bHQuXG4vLyBJZiAtLW5vLWRlcHJlY2F0aW9uIGlzIHNldCwgdGhlbiBpdCBpcyBhIG5vLW9wLlxuZXhwb3J0cy5kZXByZWNhdGUgPSBmdW5jdGlvbihmbiwgbXNnKSB7XG4gIC8vIEFsbG93IGZvciBkZXByZWNhdGluZyB0aGluZ3MgaW4gdGhlIHByb2Nlc3Mgb2Ygc3RhcnRpbmcgdXAuXG4gIGlmIChpc1VuZGVmaW5lZChnbG9iYWwucHJvY2VzcykpIHtcbiAgICByZXR1cm4gZnVuY3Rpb24oKSB7XG4gICAgICByZXR1cm4gZXhwb3J0cy5kZXByZWNhdGUoZm4sIG1zZykuYXBwbHkodGhpcywgYXJndW1lbnRzKTtcbiAgICB9O1xuICB9XG5cbiAgaWYgKHByb2Nlc3Mubm9EZXByZWNhdGlvbiA9PT0gdHJ1ZSkge1xuICAgIHJldHVybiBmbjtcbiAgfVxuXG4gIHZhciB3YXJuZWQgPSBmYWxzZTtcbiAgZnVuY3Rpb24gZGVwcmVjYXRlZCgpIHtcbiAgICBpZiAoIXdhcm5lZCkge1xuICAgICAgaWYgKHByb2Nlc3MudGhyb3dEZXByZWNhdGlvbikge1xuICAgICAgICB0aHJvdyBuZXcgRXJyb3IobXNnKTtcbiAgICAgIH0gZWxzZSBpZiAocHJvY2Vzcy50cmFjZURlcHJlY2F0aW9uKSB7XG4gICAgICAgIGNvbnNvbGUudHJhY2UobXNnKTtcbiAgICAgIH0gZWxzZSB7XG4gICAgICAgIGNvbnNvbGUuZXJyb3IobXNnKTtcbiAgICAgIH1cbiAgICAgIHdhcm5lZCA9IHRydWU7XG4gICAgfVxuICAgIHJldHVybiBmbi5hcHBseSh0aGlzLCBhcmd1bWVudHMpO1xuICB9XG5cbiAgcmV0dXJuIGRlcHJlY2F0ZWQ7XG59O1xuXG5cbnZhciBkZWJ1Z3MgPSB7fTtcbnZhciBkZWJ1Z0Vudmlyb247XG5leHBvcnRzLmRlYnVnbG9nID0gZnVuY3Rpb24oc2V0KSB7XG4gIGlmIChpc1VuZGVmaW5lZChkZWJ1Z0Vudmlyb24pKVxuICAgIGRlYnVnRW52aXJvbiA9IHByb2Nlc3MuZW52Lk5PREVfREVCVUcgfHwgJyc7XG4gIHNldCA9IHNldC50b1VwcGVyQ2FzZSgpO1xuICBpZiAoIWRlYnVnc1tzZXRdKSB7XG4gICAgaWYgKG5ldyBSZWdFeHAoJ1xcXFxiJyArIHNldCArICdcXFxcYicsICdpJykudGVzdChkZWJ1Z0Vudmlyb24pKSB7XG4gICAgICB2YXIgcGlkID0gcHJvY2Vzcy5waWQ7XG4gICAgICBkZWJ1Z3Nbc2V0XSA9IGZ1bmN0aW9uKCkge1xuICAgICAgICB2YXIgbXNnID0gZXhwb3J0cy5mb3JtYXQuYXBwbHkoZXhwb3J0cywgYXJndW1lbnRzKTtcbiAgICAgICAgY29uc29sZS5lcnJvcignJXMgJWQ6ICVzJywgc2V0LCBwaWQsIG1zZyk7XG4gICAgICB9O1xuICAgIH0gZWxzZSB7XG4gICAgICBkZWJ1Z3Nbc2V0XSA9IGZ1bmN0aW9uKCkge307XG4gICAgfVxuICB9XG4gIHJldHVybiBkZWJ1Z3Nbc2V0XTtcbn07XG5cblxuLyoqXG4gKiBFY2hvcyB0aGUgdmFsdWUgb2YgYSB2YWx1ZS4gVHJ5cyB0byBwcmludCB0aGUgdmFsdWUgb3V0XG4gKiBpbiB0aGUgYmVzdCB3YXkgcG9zc2libGUgZ2l2ZW4gdGhlIGRpZmZlcmVudCB0eXBlcy5cbiAqXG4gKiBAcGFyYW0ge09iamVjdH0gb2JqIFRoZSBvYmplY3QgdG8gcHJpbnQgb3V0LlxuICogQHBhcmFtIHtPYmplY3R9IG9wdHMgT3B0aW9uYWwgb3B0aW9ucyBvYmplY3QgdGhhdCBhbHRlcnMgdGhlIG91dHB1dC5cbiAqL1xuLyogbGVnYWN5OiBvYmosIHNob3dIaWRkZW4sIGRlcHRoLCBjb2xvcnMqL1xuZnVuY3Rpb24gaW5zcGVjdChvYmosIG9wdHMpIHtcbiAgLy8gZGVmYXVsdCBvcHRpb25zXG4gIHZhciBjdHggPSB7XG4gICAgc2VlbjogW10sXG4gICAgc3R5bGl6ZTogc3R5bGl6ZU5vQ29sb3JcbiAgfTtcbiAgLy8gbGVnYWN5Li4uXG4gIGlmIChhcmd1bWVudHMubGVuZ3RoID49IDMpIGN0eC5kZXB0aCA9IGFyZ3VtZW50c1syXTtcbiAgaWYgKGFyZ3VtZW50cy5sZW5ndGggPj0gNCkgY3R4LmNvbG9ycyA9IGFyZ3VtZW50c1szXTtcbiAgaWYgKGlzQm9vbGVhbihvcHRzKSkge1xuICAgIC8vIGxlZ2FjeS4uLlxuICAgIGN0eC5zaG93SGlkZGVuID0gb3B0cztcbiAgfSBlbHNlIGlmIChvcHRzKSB7XG4gICAgLy8gZ290IGFuIFwib3B0aW9uc1wiIG9iamVjdFxuICAgIGV4cG9ydHMuX2V4dGVuZChjdHgsIG9wdHMpO1xuICB9XG4gIC8vIHNldCBkZWZhdWx0IG9wdGlvbnNcbiAgaWYgKGlzVW5kZWZpbmVkKGN0eC5zaG93SGlkZGVuKSkgY3R4LnNob3dIaWRkZW4gPSBmYWxzZTtcbiAgaWYgKGlzVW5kZWZpbmVkKGN0eC5kZXB0aCkpIGN0eC5kZXB0aCA9IDI7XG4gIGlmIChpc1VuZGVmaW5lZChjdHguY29sb3JzKSkgY3R4LmNvbG9ycyA9IGZhbHNlO1xuICBpZiAoaXNVbmRlZmluZWQoY3R4LmN1c3RvbUluc3BlY3QpKSBjdHguY3VzdG9tSW5zcGVjdCA9IHRydWU7XG4gIGlmIChjdHguY29sb3JzKSBjdHguc3R5bGl6ZSA9IHN0eWxpemVXaXRoQ29sb3I7XG4gIHJldHVybiBmb3JtYXRWYWx1ZShjdHgsIG9iaiwgY3R4LmRlcHRoKTtcbn1cbmV4cG9ydHMuaW5zcGVjdCA9IGluc3BlY3Q7XG5cblxuLy8gaHR0cDovL2VuLndpa2lwZWRpYS5vcmcvd2lraS9BTlNJX2VzY2FwZV9jb2RlI2dyYXBoaWNzXG5pbnNwZWN0LmNvbG9ycyA9IHtcbiAgJ2JvbGQnIDogWzEsIDIyXSxcbiAgJ2l0YWxpYycgOiBbMywgMjNdLFxuICAndW5kZXJsaW5lJyA6IFs0LCAyNF0sXG4gICdpbnZlcnNlJyA6IFs3LCAyN10sXG4gICd3aGl0ZScgOiBbMzcsIDM5XSxcbiAgJ2dyZXknIDogWzkwLCAzOV0sXG4gICdibGFjaycgOiBbMzAsIDM5XSxcbiAgJ2JsdWUnIDogWzM0LCAzOV0sXG4gICdjeWFuJyA6IFszNiwgMzldLFxuICAnZ3JlZW4nIDogWzMyLCAzOV0sXG4gICdtYWdlbnRhJyA6IFszNSwgMzldLFxuICAncmVkJyA6IFszMSwgMzldLFxuICAneWVsbG93JyA6IFszMywgMzldXG59O1xuXG4vLyBEb24ndCB1c2UgJ2JsdWUnIG5vdCB2aXNpYmxlIG9uIGNtZC5leGVcbmluc3BlY3Quc3R5bGVzID0ge1xuICAnc3BlY2lhbCc6ICdjeWFuJyxcbiAgJ251bWJlcic6ICd5ZWxsb3cnLFxuICAnYm9vbGVhbic6ICd5ZWxsb3cnLFxuICAndW5kZWZpbmVkJzogJ2dyZXknLFxuICAnbnVsbCc6ICdib2xkJyxcbiAgJ3N0cmluZyc6ICdncmVlbicsXG4gICdkYXRlJzogJ21hZ2VudGEnLFxuICAvLyBcIm5hbWVcIjogaW50ZW50aW9uYWxseSBub3Qgc3R5bGluZ1xuICAncmVnZXhwJzogJ3JlZCdcbn07XG5cblxuZnVuY3Rpb24gc3R5bGl6ZVdpdGhDb2xvcihzdHIsIHN0eWxlVHlwZSkge1xuICB2YXIgc3R5bGUgPSBpbnNwZWN0LnN0eWxlc1tzdHlsZVR5cGVdO1xuXG4gIGlmIChzdHlsZSkge1xuICAgIHJldHVybiAnXFx1MDAxYlsnICsgaW5zcGVjdC5jb2xvcnNbc3R5bGVdWzBdICsgJ20nICsgc3RyICtcbiAgICAgICAgICAgJ1xcdTAwMWJbJyArIGluc3BlY3QuY29sb3JzW3N0eWxlXVsxXSArICdtJztcbiAgfSBlbHNlIHtcbiAgICByZXR1cm4gc3RyO1xuICB9XG59XG5cblxuZnVuY3Rpb24gc3R5bGl6ZU5vQ29sb3Ioc3RyLCBzdHlsZVR5cGUpIHtcbiAgcmV0dXJuIHN0cjtcbn1cblxuXG5mdW5jdGlvbiBhcnJheVRvSGFzaChhcnJheSkge1xuICB2YXIgaGFzaCA9IHt9O1xuXG4gIGFycmF5LmZvckVhY2goZnVuY3Rpb24odmFsLCBpZHgpIHtcbiAgICBoYXNoW3ZhbF0gPSB0cnVlO1xuICB9KTtcblxuICByZXR1cm4gaGFzaDtcbn1cblxuXG5mdW5jdGlvbiBmb3JtYXRWYWx1ZShjdHgsIHZhbHVlLCByZWN1cnNlVGltZXMpIHtcbiAgLy8gUHJvdmlkZSBhIGhvb2sgZm9yIHVzZXItc3BlY2lmaWVkIGluc3BlY3QgZnVuY3Rpb25zLlxuICAvLyBDaGVjayB0aGF0IHZhbHVlIGlzIGFuIG9iamVjdCB3aXRoIGFuIGluc3BlY3QgZnVuY3Rpb24gb24gaXRcbiAgaWYgKGN0eC5jdXN0b21JbnNwZWN0ICYmXG4gICAgICB2YWx1ZSAmJlxuICAgICAgaXNGdW5jdGlvbih2YWx1ZS5pbnNwZWN0KSAmJlxuICAgICAgLy8gRmlsdGVyIG91dCB0aGUgdXRpbCBtb2R1bGUsIGl0J3MgaW5zcGVjdCBmdW5jdGlvbiBpcyBzcGVjaWFsXG4gICAgICB2YWx1ZS5pbnNwZWN0ICE9PSBleHBvcnRzLmluc3BlY3QgJiZcbiAgICAgIC8vIEFsc28gZmlsdGVyIG91dCBhbnkgcHJvdG90eXBlIG9iamVjdHMgdXNpbmcgdGhlIGNpcmN1bGFyIGNoZWNrLlxuICAgICAgISh2YWx1ZS5jb25zdHJ1Y3RvciAmJiB2YWx1ZS5jb25zdHJ1Y3Rvci5wcm90b3R5cGUgPT09IHZhbHVlKSkge1xuICAgIHZhciByZXQgPSB2YWx1ZS5pbnNwZWN0KHJlY3Vyc2VUaW1lcywgY3R4KTtcbiAgICBpZiAoIWlzU3RyaW5nKHJldCkpIHtcbiAgICAgIHJldCA9IGZvcm1hdFZhbHVlKGN0eCwgcmV0LCByZWN1cnNlVGltZXMpO1xuICAgIH1cbiAgICByZXR1cm4gcmV0O1xuICB9XG5cbiAgLy8gUHJpbWl0aXZlIHR5cGVzIGNhbm5vdCBoYXZlIHByb3BlcnRpZXNcbiAgdmFyIHByaW1pdGl2ZSA9IGZvcm1hdFByaW1pdGl2ZShjdHgsIHZhbHVlKTtcbiAgaWYgKHByaW1pdGl2ZSkge1xuICAgIHJldHVybiBwcmltaXRpdmU7XG4gIH1cblxuICAvLyBMb29rIHVwIHRoZSBrZXlzIG9mIHRoZSBvYmplY3QuXG4gIHZhciBrZXlzID0gT2JqZWN0LmtleXModmFsdWUpO1xuICB2YXIgdmlzaWJsZUtleXMgPSBhcnJheVRvSGFzaChrZXlzKTtcblxuICBpZiAoY3R4LnNob3dIaWRkZW4pIHtcbiAgICBrZXlzID0gT2JqZWN0LmdldE93blByb3BlcnR5TmFtZXModmFsdWUpO1xuICB9XG5cbiAgLy8gSUUgZG9lc24ndCBtYWtlIGVycm9yIGZpZWxkcyBub24tZW51bWVyYWJsZVxuICAvLyBodHRwOi8vbXNkbi5taWNyb3NvZnQuY29tL2VuLXVzL2xpYnJhcnkvaWUvZHd3NTJzYnQodj12cy45NCkuYXNweFxuICBpZiAoaXNFcnJvcih2YWx1ZSlcbiAgICAgICYmIChrZXlzLmluZGV4T2YoJ21lc3NhZ2UnKSA+PSAwIHx8IGtleXMuaW5kZXhPZignZGVzY3JpcHRpb24nKSA+PSAwKSkge1xuICAgIHJldHVybiBmb3JtYXRFcnJvcih2YWx1ZSk7XG4gIH1cblxuICAvLyBTb21lIHR5cGUgb2Ygb2JqZWN0IHdpdGhvdXQgcHJvcGVydGllcyBjYW4gYmUgc2hvcnRjdXR0ZWQuXG4gIGlmIChrZXlzLmxlbmd0aCA9PT0gMCkge1xuICAgIGlmIChpc0Z1bmN0aW9uKHZhbHVlKSkge1xuICAgICAgdmFyIG5hbWUgPSB2YWx1ZS5uYW1lID8gJzogJyArIHZhbHVlLm5hbWUgOiAnJztcbiAgICAgIHJldHVybiBjdHguc3R5bGl6ZSgnW0Z1bmN0aW9uJyArIG5hbWUgKyAnXScsICdzcGVjaWFsJyk7XG4gICAgfVxuICAgIGlmIChpc1JlZ0V4cCh2YWx1ZSkpIHtcbiAgICAgIHJldHVybiBjdHguc3R5bGl6ZShSZWdFeHAucHJvdG90eXBlLnRvU3RyaW5nLmNhbGwodmFsdWUpLCAncmVnZXhwJyk7XG4gICAgfVxuICAgIGlmIChpc0RhdGUodmFsdWUpKSB7XG4gICAgICByZXR1cm4gY3R4LnN0eWxpemUoRGF0ZS5wcm90b3R5cGUudG9TdHJpbmcuY2FsbCh2YWx1ZSksICdkYXRlJyk7XG4gICAgfVxuICAgIGlmIChpc0Vycm9yKHZhbHVlKSkge1xuICAgICAgcmV0dXJuIGZvcm1hdEVycm9yKHZhbHVlKTtcbiAgICB9XG4gIH1cblxuICB2YXIgYmFzZSA9ICcnLCBhcnJheSA9IGZhbHNlLCBicmFjZXMgPSBbJ3snLCAnfSddO1xuXG4gIC8vIE1ha2UgQXJyYXkgc2F5IHRoYXQgdGhleSBhcmUgQXJyYXlcbiAgaWYgKGlzQXJyYXkodmFsdWUpKSB7XG4gICAgYXJyYXkgPSB0cnVlO1xuICAgIGJyYWNlcyA9IFsnWycsICddJ107XG4gIH1cblxuICAvLyBNYWtlIGZ1bmN0aW9ucyBzYXkgdGhhdCB0aGV5IGFyZSBmdW5jdGlvbnNcbiAgaWYgKGlzRnVuY3Rpb24odmFsdWUpKSB7XG4gICAgdmFyIG4gPSB2YWx1ZS5uYW1lID8gJzogJyArIHZhbHVlLm5hbWUgOiAnJztcbiAgICBiYXNlID0gJyBbRnVuY3Rpb24nICsgbiArICddJztcbiAgfVxuXG4gIC8vIE1ha2UgUmVnRXhwcyBzYXkgdGhhdCB0aGV5IGFyZSBSZWdFeHBzXG4gIGlmIChpc1JlZ0V4cCh2YWx1ZSkpIHtcbiAgICBiYXNlID0gJyAnICsgUmVnRXhwLnByb3RvdHlwZS50b1N0cmluZy5jYWxsKHZhbHVlKTtcbiAgfVxuXG4gIC8vIE1ha2UgZGF0ZXMgd2l0aCBwcm9wZXJ0aWVzIGZpcnN0IHNheSB0aGUgZGF0ZVxuICBpZiAoaXNEYXRlKHZhbHVlKSkge1xuICAgIGJhc2UgPSAnICcgKyBEYXRlLnByb3RvdHlwZS50b1VUQ1N0cmluZy5jYWxsKHZhbHVlKTtcbiAgfVxuXG4gIC8vIE1ha2UgZXJyb3Igd2l0aCBtZXNzYWdlIGZpcnN0IHNheSB0aGUgZXJyb3JcbiAgaWYgKGlzRXJyb3IodmFsdWUpKSB7XG4gICAgYmFzZSA9ICcgJyArIGZvcm1hdEVycm9yKHZhbHVlKTtcbiAgfVxuXG4gIGlmIChrZXlzLmxlbmd0aCA9PT0gMCAmJiAoIWFycmF5IHx8IHZhbHVlLmxlbmd0aCA9PSAwKSkge1xuICAgIHJldHVybiBicmFjZXNbMF0gKyBiYXNlICsgYnJhY2VzWzFdO1xuICB9XG5cbiAgaWYgKHJlY3Vyc2VUaW1lcyA8IDApIHtcbiAgICBpZiAoaXNSZWdFeHAodmFsdWUpKSB7XG4gICAgICByZXR1cm4gY3R4LnN0eWxpemUoUmVnRXhwLnByb3RvdHlwZS50b1N0cmluZy5jYWxsKHZhbHVlKSwgJ3JlZ2V4cCcpO1xuICAgIH0gZWxzZSB7XG4gICAgICByZXR1cm4gY3R4LnN0eWxpemUoJ1tPYmplY3RdJywgJ3NwZWNpYWwnKTtcbiAgICB9XG4gIH1cblxuICBjdHguc2Vlbi5wdXNoKHZhbHVlKTtcblxuICB2YXIgb3V0cHV0O1xuICBpZiAoYXJyYXkpIHtcbiAgICBvdXRwdXQgPSBmb3JtYXRBcnJheShjdHgsIHZhbHVlLCByZWN1cnNlVGltZXMsIHZpc2libGVLZXlzLCBrZXlzKTtcbiAgfSBlbHNlIHtcbiAgICBvdXRwdXQgPSBrZXlzLm1hcChmdW5jdGlvbihrZXkpIHtcbiAgICAgIHJldHVybiBmb3JtYXRQcm9wZXJ0eShjdHgsIHZhbHVlLCByZWN1cnNlVGltZXMsIHZpc2libGVLZXlzLCBrZXksIGFycmF5KTtcbiAgICB9KTtcbiAgfVxuXG4gIGN0eC5zZWVuLnBvcCgpO1xuXG4gIHJldHVybiByZWR1Y2VUb1NpbmdsZVN0cmluZyhvdXRwdXQsIGJhc2UsIGJyYWNlcyk7XG59XG5cblxuZnVuY3Rpb24gZm9ybWF0UHJpbWl0aXZlKGN0eCwgdmFsdWUpIHtcbiAgaWYgKGlzVW5kZWZpbmVkKHZhbHVlKSlcbiAgICByZXR1cm4gY3R4LnN0eWxpemUoJ3VuZGVmaW5lZCcsICd1bmRlZmluZWQnKTtcbiAgaWYgKGlzU3RyaW5nKHZhbHVlKSkge1xuICAgIHZhciBzaW1wbGUgPSAnXFwnJyArIEpTT04uc3RyaW5naWZ5KHZhbHVlKS5yZXBsYWNlKC9eXCJ8XCIkL2csICcnKVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgLnJlcGxhY2UoLycvZywgXCJcXFxcJ1wiKVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgLnJlcGxhY2UoL1xcXFxcIi9nLCAnXCInKSArICdcXCcnO1xuICAgIHJldHVybiBjdHguc3R5bGl6ZShzaW1wbGUsICdzdHJpbmcnKTtcbiAgfVxuICBpZiAoaXNOdW1iZXIodmFsdWUpKVxuICAgIHJldHVybiBjdHguc3R5bGl6ZSgnJyArIHZhbHVlLCAnbnVtYmVyJyk7XG4gIGlmIChpc0Jvb2xlYW4odmFsdWUpKVxuICAgIHJldHVybiBjdHguc3R5bGl6ZSgnJyArIHZhbHVlLCAnYm9vbGVhbicpO1xuICAvLyBGb3Igc29tZSByZWFzb24gdHlwZW9mIG51bGwgaXMgXCJvYmplY3RcIiwgc28gc3BlY2lhbCBjYXNlIGhlcmUuXG4gIGlmIChpc051bGwodmFsdWUpKVxuICAgIHJldHVybiBjdHguc3R5bGl6ZSgnbnVsbCcsICdudWxsJyk7XG59XG5cblxuZnVuY3Rpb24gZm9ybWF0RXJyb3IodmFsdWUpIHtcbiAgcmV0dXJuICdbJyArIEVycm9yLnByb3RvdHlwZS50b1N0cmluZy5jYWxsKHZhbHVlKSArICddJztcbn1cblxuXG5mdW5jdGlvbiBmb3JtYXRBcnJheShjdHgsIHZhbHVlLCByZWN1cnNlVGltZXMsIHZpc2libGVLZXlzLCBrZXlzKSB7XG4gIHZhciBvdXRwdXQgPSBbXTtcbiAgZm9yICh2YXIgaSA9IDAsIGwgPSB2YWx1ZS5sZW5ndGg7IGkgPCBsOyArK2kpIHtcbiAgICBpZiAoaGFzT3duUHJvcGVydHkodmFsdWUsIFN0cmluZyhpKSkpIHtcbiAgICAgIG91dHB1dC5wdXNoKGZvcm1hdFByb3BlcnR5KGN0eCwgdmFsdWUsIHJlY3Vyc2VUaW1lcywgdmlzaWJsZUtleXMsXG4gICAgICAgICAgU3RyaW5nKGkpLCB0cnVlKSk7XG4gICAgfSBlbHNlIHtcbiAgICAgIG91dHB1dC5wdXNoKCcnKTtcbiAgICB9XG4gIH1cbiAga2V5cy5mb3JFYWNoKGZ1bmN0aW9uKGtleSkge1xuICAgIGlmICgha2V5Lm1hdGNoKC9eXFxkKyQvKSkge1xuICAgICAgb3V0cHV0LnB1c2goZm9ybWF0UHJvcGVydHkoY3R4LCB2YWx1ZSwgcmVjdXJzZVRpbWVzLCB2aXNpYmxlS2V5cyxcbiAgICAgICAgICBrZXksIHRydWUpKTtcbiAgICB9XG4gIH0pO1xuICByZXR1cm4gb3V0cHV0O1xufVxuXG5cbmZ1bmN0aW9uIGZvcm1hdFByb3BlcnR5KGN0eCwgdmFsdWUsIHJlY3Vyc2VUaW1lcywgdmlzaWJsZUtleXMsIGtleSwgYXJyYXkpIHtcbiAgdmFyIG5hbWUsIHN0ciwgZGVzYztcbiAgZGVzYyA9IE9iamVjdC5nZXRPd25Qcm9wZXJ0eURlc2NyaXB0b3IodmFsdWUsIGtleSkgfHwgeyB2YWx1ZTogdmFsdWVba2V5XSB9O1xuICBpZiAoZGVzYy5nZXQpIHtcbiAgICBpZiAoZGVzYy5zZXQpIHtcbiAgICAgIHN0ciA9IGN0eC5zdHlsaXplKCdbR2V0dGVyL1NldHRlcl0nLCAnc3BlY2lhbCcpO1xuICAgIH0gZWxzZSB7XG4gICAgICBzdHIgPSBjdHguc3R5bGl6ZSgnW0dldHRlcl0nLCAnc3BlY2lhbCcpO1xuICAgIH1cbiAgfSBlbHNlIHtcbiAgICBpZiAoZGVzYy5zZXQpIHtcbiAgICAgIHN0ciA9IGN0eC5zdHlsaXplKCdbU2V0dGVyXScsICdzcGVjaWFsJyk7XG4gICAgfVxuICB9XG4gIGlmICghaGFzT3duUHJvcGVydHkodmlzaWJsZUtleXMsIGtleSkpIHtcbiAgICBuYW1lID0gJ1snICsga2V5ICsgJ10nO1xuICB9XG4gIGlmICghc3RyKSB7XG4gICAgaWYgKGN0eC5zZWVuLmluZGV4T2YoZGVzYy52YWx1ZSkgPCAwKSB7XG4gICAgICBpZiAoaXNOdWxsKHJlY3Vyc2VUaW1lcykpIHtcbiAgICAgICAgc3RyID0gZm9ybWF0VmFsdWUoY3R4LCBkZXNjLnZhbHVlLCBudWxsKTtcbiAgICAgIH0gZWxzZSB7XG4gICAgICAgIHN0ciA9IGZvcm1hdFZhbHVlKGN0eCwgZGVzYy52YWx1ZSwgcmVjdXJzZVRpbWVzIC0gMSk7XG4gICAgICB9XG4gICAgICBpZiAoc3RyLmluZGV4T2YoJ1xcbicpID4gLTEpIHtcbiAgICAgICAgaWYgKGFycmF5KSB7XG4gICAgICAgICAgc3RyID0gc3RyLnNwbGl0KCdcXG4nKS5tYXAoZnVuY3Rpb24obGluZSkge1xuICAgICAgICAgICAgcmV0dXJuICcgICcgKyBsaW5lO1xuICAgICAgICAgIH0pLmpvaW4oJ1xcbicpLnN1YnN0cigyKTtcbiAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICBzdHIgPSAnXFxuJyArIHN0ci5zcGxpdCgnXFxuJykubWFwKGZ1bmN0aW9uKGxpbmUpIHtcbiAgICAgICAgICAgIHJldHVybiAnICAgJyArIGxpbmU7XG4gICAgICAgICAgfSkuam9pbignXFxuJyk7XG4gICAgICAgIH1cbiAgICAgIH1cbiAgICB9IGVsc2Uge1xuICAgICAgc3RyID0gY3R4LnN0eWxpemUoJ1tDaXJjdWxhcl0nLCAnc3BlY2lhbCcpO1xuICAgIH1cbiAgfVxuICBpZiAoaXNVbmRlZmluZWQobmFtZSkpIHtcbiAgICBpZiAoYXJyYXkgJiYga2V5Lm1hdGNoKC9eXFxkKyQvKSkge1xuICAgICAgcmV0dXJuIHN0cjtcbiAgICB9XG4gICAgbmFtZSA9IEpTT04uc3RyaW5naWZ5KCcnICsga2V5KTtcbiAgICBpZiAobmFtZS5tYXRjaCgvXlwiKFthLXpBLVpfXVthLXpBLVpfMC05XSopXCIkLykpIHtcbiAgICAgIG5hbWUgPSBuYW1lLnN1YnN0cigxLCBuYW1lLmxlbmd0aCAtIDIpO1xuICAgICAgbmFtZSA9IGN0eC5zdHlsaXplKG5hbWUsICduYW1lJyk7XG4gICAgfSBlbHNlIHtcbiAgICAgIG5hbWUgPSBuYW1lLnJlcGxhY2UoLycvZywgXCJcXFxcJ1wiKVxuICAgICAgICAgICAgICAgICAucmVwbGFjZSgvXFxcXFwiL2csICdcIicpXG4gICAgICAgICAgICAgICAgIC5yZXBsYWNlKC8oXlwifFwiJCkvZywgXCInXCIpO1xuICAgICAgbmFtZSA9IGN0eC5zdHlsaXplKG5hbWUsICdzdHJpbmcnKTtcbiAgICB9XG4gIH1cblxuICByZXR1cm4gbmFtZSArICc6ICcgKyBzdHI7XG59XG5cblxuZnVuY3Rpb24gcmVkdWNlVG9TaW5nbGVTdHJpbmcob3V0cHV0LCBiYXNlLCBicmFjZXMpIHtcbiAgdmFyIG51bUxpbmVzRXN0ID0gMDtcbiAgdmFyIGxlbmd0aCA9IG91dHB1dC5yZWR1Y2UoZnVuY3Rpb24ocHJldiwgY3VyKSB7XG4gICAgbnVtTGluZXNFc3QrKztcbiAgICBpZiAoY3VyLmluZGV4T2YoJ1xcbicpID49IDApIG51bUxpbmVzRXN0Kys7XG4gICAgcmV0dXJuIHByZXYgKyBjdXIucmVwbGFjZSgvXFx1MDAxYlxcW1xcZFxcZD9tL2csICcnKS5sZW5ndGggKyAxO1xuICB9LCAwKTtcblxuICBpZiAobGVuZ3RoID4gNjApIHtcbiAgICByZXR1cm4gYnJhY2VzWzBdICtcbiAgICAgICAgICAgKGJhc2UgPT09ICcnID8gJycgOiBiYXNlICsgJ1xcbiAnKSArXG4gICAgICAgICAgICcgJyArXG4gICAgICAgICAgIG91dHB1dC5qb2luKCcsXFxuICAnKSArXG4gICAgICAgICAgICcgJyArXG4gICAgICAgICAgIGJyYWNlc1sxXTtcbiAgfVxuXG4gIHJldHVybiBicmFjZXNbMF0gKyBiYXNlICsgJyAnICsgb3V0cHV0LmpvaW4oJywgJykgKyAnICcgKyBicmFjZXNbMV07XG59XG5cblxuLy8gTk9URTogVGhlc2UgdHlwZSBjaGVja2luZyBmdW5jdGlvbnMgaW50ZW50aW9uYWxseSBkb24ndCB1c2UgYGluc3RhbmNlb2ZgXG4vLyBiZWNhdXNlIGl0IGlzIGZyYWdpbGUgYW5kIGNhbiBiZSBlYXNpbHkgZmFrZWQgd2l0aCBgT2JqZWN0LmNyZWF0ZSgpYC5cbmZ1bmN0aW9uIGlzQXJyYXkoYXIpIHtcbiAgcmV0dXJuIEFycmF5LmlzQXJyYXkoYXIpO1xufVxuZXhwb3J0cy5pc0FycmF5ID0gaXNBcnJheTtcblxuZnVuY3Rpb24gaXNCb29sZWFuKGFyZykge1xuICByZXR1cm4gdHlwZW9mIGFyZyA9PT0gJ2Jvb2xlYW4nO1xufVxuZXhwb3J0cy5pc0Jvb2xlYW4gPSBpc0Jvb2xlYW47XG5cbmZ1bmN0aW9uIGlzTnVsbChhcmcpIHtcbiAgcmV0dXJuIGFyZyA9PT0gbnVsbDtcbn1cbmV4cG9ydHMuaXNOdWxsID0gaXNOdWxsO1xuXG5mdW5jdGlvbiBpc051bGxPclVuZGVmaW5lZChhcmcpIHtcbiAgcmV0dXJuIGFyZyA9PSBudWxsO1xufVxuZXhwb3J0cy5pc051bGxPclVuZGVmaW5lZCA9IGlzTnVsbE9yVW5kZWZpbmVkO1xuXG5mdW5jdGlvbiBpc051bWJlcihhcmcpIHtcbiAgcmV0dXJuIHR5cGVvZiBhcmcgPT09ICdudW1iZXInO1xufVxuZXhwb3J0cy5pc051bWJlciA9IGlzTnVtYmVyO1xuXG5mdW5jdGlvbiBpc1N0cmluZyhhcmcpIHtcbiAgcmV0dXJuIHR5cGVvZiBhcmcgPT09ICdzdHJpbmcnO1xufVxuZXhwb3J0cy5pc1N0cmluZyA9IGlzU3RyaW5nO1xuXG5mdW5jdGlvbiBpc1N5bWJvbChhcmcpIHtcbiAgcmV0dXJuIHR5cGVvZiBhcmcgPT09ICdzeW1ib2wnO1xufVxuZXhwb3J0cy5pc1N5bWJvbCA9IGlzU3ltYm9sO1xuXG5mdW5jdGlvbiBpc1VuZGVmaW5lZChhcmcpIHtcbiAgcmV0dXJuIGFyZyA9PT0gdm9pZCAwO1xufVxuZXhwb3J0cy5pc1VuZGVmaW5lZCA9IGlzVW5kZWZpbmVkO1xuXG5mdW5jdGlvbiBpc1JlZ0V4cChyZSkge1xuICByZXR1cm4gaXNPYmplY3QocmUpICYmIG9iamVjdFRvU3RyaW5nKHJlKSA9PT0gJ1tvYmplY3QgUmVnRXhwXSc7XG59XG5leHBvcnRzLmlzUmVnRXhwID0gaXNSZWdFeHA7XG5cbmZ1bmN0aW9uIGlzT2JqZWN0KGFyZykge1xuICByZXR1cm4gdHlwZW9mIGFyZyA9PT0gJ29iamVjdCcgJiYgYXJnICE9PSBudWxsO1xufVxuZXhwb3J0cy5pc09iamVjdCA9IGlzT2JqZWN0O1xuXG5mdW5jdGlvbiBpc0RhdGUoZCkge1xuICByZXR1cm4gaXNPYmplY3QoZCkgJiYgb2JqZWN0VG9TdHJpbmcoZCkgPT09ICdbb2JqZWN0IERhdGVdJztcbn1cbmV4cG9ydHMuaXNEYXRlID0gaXNEYXRlO1xuXG5mdW5jdGlvbiBpc0Vycm9yKGUpIHtcbiAgcmV0dXJuIGlzT2JqZWN0KGUpICYmXG4gICAgICAob2JqZWN0VG9TdHJpbmcoZSkgPT09ICdbb2JqZWN0IEVycm9yXScgfHwgZSBpbnN0YW5jZW9mIEVycm9yKTtcbn1cbmV4cG9ydHMuaXNFcnJvciA9IGlzRXJyb3I7XG5cbmZ1bmN0aW9uIGlzRnVuY3Rpb24oYXJnKSB7XG4gIHJldHVybiB0eXBlb2YgYXJnID09PSAnZnVuY3Rpb24nO1xufVxuZXhwb3J0cy5pc0Z1bmN0aW9uID0gaXNGdW5jdGlvbjtcblxuZnVuY3Rpb24gaXNQcmltaXRpdmUoYXJnKSB7XG4gIHJldHVybiBhcmcgPT09IG51bGwgfHxcbiAgICAgICAgIHR5cGVvZiBhcmcgPT09ICdib29sZWFuJyB8fFxuICAgICAgICAgdHlwZW9mIGFyZyA9PT0gJ251bWJlcicgfHxcbiAgICAgICAgIHR5cGVvZiBhcmcgPT09ICdzdHJpbmcnIHx8XG4gICAgICAgICB0eXBlb2YgYXJnID09PSAnc3ltYm9sJyB8fCAgLy8gRVM2IHN5bWJvbFxuICAgICAgICAgdHlwZW9mIGFyZyA9PT0gJ3VuZGVmaW5lZCc7XG59XG5leHBvcnRzLmlzUHJpbWl0aXZlID0gaXNQcmltaXRpdmU7XG5cbmV4cG9ydHMuaXNCdWZmZXIgPSByZXF1aXJlKCcuL3N1cHBvcnQvaXNCdWZmZXInKTtcblxuZnVuY3Rpb24gb2JqZWN0VG9TdHJpbmcobykge1xuICByZXR1cm4gT2JqZWN0LnByb3RvdHlwZS50b1N0cmluZy5jYWxsKG8pO1xufVxuXG5cbmZ1bmN0aW9uIHBhZChuKSB7XG4gIHJldHVybiBuIDwgMTAgPyAnMCcgKyBuLnRvU3RyaW5nKDEwKSA6IG4udG9TdHJpbmcoMTApO1xufVxuXG5cbnZhciBtb250aHMgPSBbJ0phbicsICdGZWInLCAnTWFyJywgJ0FwcicsICdNYXknLCAnSnVuJywgJ0p1bCcsICdBdWcnLCAnU2VwJyxcbiAgICAgICAgICAgICAgJ09jdCcsICdOb3YnLCAnRGVjJ107XG5cbi8vIDI2IEZlYiAxNjoxOTozNFxuZnVuY3Rpb24gdGltZXN0YW1wKCkge1xuICB2YXIgZCA9IG5ldyBEYXRlKCk7XG4gIHZhciB0aW1lID0gW3BhZChkLmdldEhvdXJzKCkpLFxuICAgICAgICAgICAgICBwYWQoZC5nZXRNaW51dGVzKCkpLFxuICAgICAgICAgICAgICBwYWQoZC5nZXRTZWNvbmRzKCkpXS5qb2luKCc6Jyk7XG4gIHJldHVybiBbZC5nZXREYXRlKCksIG1vbnRoc1tkLmdldE1vbnRoKCldLCB0aW1lXS5qb2luKCcgJyk7XG59XG5cblxuLy8gbG9nIGlzIGp1c3QgYSB0aGluIHdyYXBwZXIgdG8gY29uc29sZS5sb2cgdGhhdCBwcmVwZW5kcyBhIHRpbWVzdGFtcFxuZXhwb3J0cy5sb2cgPSBmdW5jdGlvbigpIHtcbiAgY29uc29sZS5sb2coJyVzIC0gJXMnLCB0aW1lc3RhbXAoKSwgZXhwb3J0cy5mb3JtYXQuYXBwbHkoZXhwb3J0cywgYXJndW1lbnRzKSk7XG59O1xuXG5cbi8qKlxuICogSW5oZXJpdCB0aGUgcHJvdG90eXBlIG1ldGhvZHMgZnJvbSBvbmUgY29uc3RydWN0b3IgaW50byBhbm90aGVyLlxuICpcbiAqIFRoZSBGdW5jdGlvbi5wcm90b3R5cGUuaW5oZXJpdHMgZnJvbSBsYW5nLmpzIHJld3JpdHRlbiBhcyBhIHN0YW5kYWxvbmVcbiAqIGZ1bmN0aW9uIChub3Qgb24gRnVuY3Rpb24ucHJvdG90eXBlKS4gTk9URTogSWYgdGhpcyBmaWxlIGlzIHRvIGJlIGxvYWRlZFxuICogZHVyaW5nIGJvb3RzdHJhcHBpbmcgdGhpcyBmdW5jdGlvbiBuZWVkcyB0byBiZSByZXdyaXR0ZW4gdXNpbmcgc29tZSBuYXRpdmVcbiAqIGZ1bmN0aW9ucyBhcyBwcm90b3R5cGUgc2V0dXAgdXNpbmcgbm9ybWFsIEphdmFTY3JpcHQgZG9lcyBub3Qgd29yayBhc1xuICogZXhwZWN0ZWQgZHVyaW5nIGJvb3RzdHJhcHBpbmcgKHNlZSBtaXJyb3IuanMgaW4gcjExNDkwMykuXG4gKlxuICogQHBhcmFtIHtmdW5jdGlvbn0gY3RvciBDb25zdHJ1Y3RvciBmdW5jdGlvbiB3aGljaCBuZWVkcyB0byBpbmhlcml0IHRoZVxuICogICAgIHByb3RvdHlwZS5cbiAqIEBwYXJhbSB7ZnVuY3Rpb259IHN1cGVyQ3RvciBDb25zdHJ1Y3RvciBmdW5jdGlvbiB0byBpbmhlcml0IHByb3RvdHlwZSBmcm9tLlxuICovXG5leHBvcnRzLmluaGVyaXRzID0gcmVxdWlyZSgnaW5oZXJpdHMnKTtcblxuZXhwb3J0cy5fZXh0ZW5kID0gZnVuY3Rpb24ob3JpZ2luLCBhZGQpIHtcbiAgLy8gRG9uJ3QgZG8gYW55dGhpbmcgaWYgYWRkIGlzbid0IGFuIG9iamVjdFxuICBpZiAoIWFkZCB8fCAhaXNPYmplY3QoYWRkKSkgcmV0dXJuIG9yaWdpbjtcblxuICB2YXIga2V5cyA9IE9iamVjdC5rZXlzKGFkZCk7XG4gIHZhciBpID0ga2V5cy5sZW5ndGg7XG4gIHdoaWxlIChpLS0pIHtcbiAgICBvcmlnaW5ba2V5c1tpXV0gPSBhZGRba2V5c1tpXV07XG4gIH1cbiAgcmV0dXJuIG9yaWdpbjtcbn07XG5cbmZ1bmN0aW9uIGhhc093blByb3BlcnR5KG9iaiwgcHJvcCkge1xuICByZXR1cm4gT2JqZWN0LnByb3RvdHlwZS5oYXNPd25Qcm9wZXJ0eS5jYWxsKG9iaiwgcHJvcCk7XG59XG4iXX0=
