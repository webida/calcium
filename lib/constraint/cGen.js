'use strict';

import * as types from '../domains/types'
import * as myWalker from '../util/myWalker'
const walk = require('acorn/dist/walk');
const status = require('../domains/status');
const cstr = require('./constraints');

// returns [access type, prop value]
function propAccess(node) {
    const prop = node.property;
    if (!node.computed) {
        return ['dotAccess', prop.name];
    }
    if (prop.type === 'Literal') {
        if (typeof prop.value === 'string')
            return ['stringLiteral', prop.value];
        if (typeof prop.value === 'number')
            // convert number to string
            return ['numberLiteral', prop.value + ''];
    }
    return ['computed', null];
}

function unopResultType(op) {
    switch (op) {
        case '+': case '-': case '~':
            return types.PrimNumber;
        case '!':
            return types.PrimBoolean;
        case 'typeof':
            return types.PrimString;
        case 'void': case 'delete':
            return null;
    }
}

function binopIsBoolean(op) {
    switch (op) {
        case '==': case '!=': case '===': case '!==':
        case '<': case '>': case '>=': case '<=':
        case 'in': case 'instanceof':
            return true;
    }
    return false;
}

// To prevent recursion,
// we remember the status used in addConstraints
const visitedStatus = [];
function clearConstraints() {
    visitedStatus.length = 0;
}

let rtCX;
function addConstraints(ast, initStatus, newRtCX) {

    // set rtCX
    rtCX = newRtCX || rtCX;
    const Ĉ = rtCX.Ĉ;

    // Check whether we have processed 'initStatus' before
    for (let i=0; i < visitedStatus.length; i++) {
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
        const ret = Ĉ.get(node, curStatus.delta);
        const objAVal = c(node.object, curStatus, undefined);
        if (node.property.type !== 'Identifier') {
            // return from property is ignored
            c(node.property, curStatus, undefined);
        }
        const [, propName] = propAccess(node);

        objAVal.propagate(new cstr.ReadProp(propName, ret));

        // returns AVal for receiver and read member
        return [objAVal, ret];
    }

    // constraint generating walker for expressions
    const constraintGenerator = walk.make({

        Identifier: function (node, curStatus, c) {
            const av = curStatus.sc.getAValOf(node.name);
            // use aval in the scope
            Ĉ.set(node, curStatus.delta, av);
            return av;
        },

        ThisExpression: function (node, curStatus, c) {
            const av = curStatus.self;
            // use aval for 'this'
            Ĉ.set(node, curStatus.delta, av);
            return av;
        },

        Literal: function (node, curStatus, c) {
            const res = Ĉ.get(node, curStatus.delta);
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

        AssignmentExpression: function (node, curStatus, c) {
            const rhsAVal = c(node.right, curStatus, undefined);
            if (node.left.type === 'Identifier') {
                // LHS is a simple variable.
                const varName = node.left.name;
                const lhsAVal = curStatus.sc.getAValOf(varName);
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
                const resAVal = Ĉ.get(node, curStatus.delta);
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
                const objAVal = c(node.left.object, curStatus, undefined);
                const [accType, propName] = propAccess(node.left);
                if (node.operator === '=') {
                    // assignment to member
                    objAVal.propagate(new cstr.WriteProp(propName, rhsAVal));
                    // if property is number literal, also write to 'unknown'
                    if (accType === 'numberLiteral') {
                        objAVal.propagate(new cstr.WriteProp(null, rhsAVal));
                    }
                    // node's AVal from RHS
                    Ĉ.set(node, curStatus.delta, rhsAVal);
                    return rhsAVal;
                }
                // updating assignment
                const resAVal = Ĉ.get(node, curStatus.delta);
                const [, retAVal] = readMember(node.left, curStatus, c);
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

        VariableDeclaration: function (node, curStatus, c) {
            for (let i = 0; i < node.declarations.length; i++) {
                const decl = node.declarations[i];
                const lhsAVal = curStatus.sc.getAValOf(decl.id.name);
                // declared var node is 'id'
                Ĉ.set(decl.id, curStatus.delta, lhsAVal);
                if (decl.init) {
                    const rhsAVal = c(decl.init, curStatus, undefined);
                    Ĉ.set(decl.init, curStatus.delta, rhsAVal);
                    rhsAVal.propagate(lhsAVal);
                }
            }
        },

        LogicalExpression: function (node, curStatus, c) {
            const res = Ĉ.get(node, curStatus.delta);
            const left = c(node.left, curStatus, undefined);
            const right = c(node.right, curStatus, undefined);
            left.propagate(res);
            right.propagate(res);
            return res;
        },

        ConditionalExpression: function (node, curStatus, c) {
            const res = Ĉ.get(node, curStatus.delta);
            c(node.test, curStatus, undefined);
            const cons = c(node.consequent, curStatus, undefined);
            const alt = c(node.alternate, curStatus, undefined);
            cons.propagate(res);
            alt.propagate(res);
            return res;
        },

        NewExpression: function (node, curStatus, c) {
            const ret = Ĉ.get(node, curStatus.delta);
            const callee = c(node.callee, curStatus, undefined);
            const args = [];
            for (let i = 0; i < node.arguments.length; i++) {
                args.push(c(node.arguments[i], curStatus, undefined));
            }
            const newDelta = curStatus.delta.appendOne(node['@label']);
            callee.propagate(
                new cstr.IsCtor(
                    args,
                    ret,
                    curStatus.exc,
                    newDelta));
            return ret;
        },

        ArrayExpression: function (node, curStatus, c) {
            const ret = Ĉ.get(node, curStatus.delta);
            // NOTE prototype object is not recorded in Ĉ
            const arrType = new types.ArrType(new types.AVal(rtCX.protos.Array));
            // add length property
            arrType.getProp('length').addType(types.PrimNumber);

            ret.addType(arrType);

            // add array elements
            for (let i = 0; i < node.elements.length; i++) {
                if (node.elements[i] == null) {
                    continue;
                }
                const eltAVal = c(node.elements[i], curStatus, undefined);

                const prop = i + '';
                ret.propagate(new cstr.WriteProp(prop, eltAVal));
                ret.propagate(new cstr.WriteProp(null, eltAVal));
            }
            return ret;
        },

        ObjectExpression: function (node, curStatus, c) {
            const ret = Ĉ.get(node, curStatus.delta);
            // NOTE prototype object is not recorded in Ĉ
            const objType = new types.ObjType(new types.AVal(rtCX.protos.Object));
            ret.addType(objType);

            for (let i = 0; i < node.properties.length; i++) {
                const propPair = node.properties[i];
                const propKey = propPair.key;
                let name;
                const propExpr = propPair.value;

                const fldAVal = c(propExpr, curStatus, undefined);

                if (propKey.type === 'Identifier') {
                    name = propKey.name;
                } else if (typeof propKey.value === 'string') {
                    name = propKey.value;
                } else if (typeof propKey.value === 'number') {
                    // convert number to string
                    name = propKey.value + '';
                }
                ret.propagate(new cstr.WriteProp(name, fldAVal));
            }
            return ret;
        },

        FunctionExpression: function (node, curStatus, c) {
            if (!node.fnInstances) {
                node.fnInstances = [];
            }
            let fnInstance = null;
            node.fnInstances.forEach(function (fnType) {
                if (fnType.sc === curStatus.sc) {
                    fnInstance = fnType;
                }
            });
            if (!fnInstance) {
                // NOTE prototype object is not recorded in Ĉ
                fnInstance
                    = new types.FnType(new types.AVal(rtCX.protos.Function),
                                       '[anonymous function]',
                                       node.body['@block'].getParamVarNames(),
                                       curStatus.sc,
                                       node,
                                       rtCX.protos.Object);
                node.fnInstances.push(fnInstance);
                // NOTE prototype object is not recorded in Ĉ
                const prototypeObject =
                    new types.ObjType(new types.AVal(rtCX.protos.Object),
                                      '?.prototype');
                // For .prototype
                const prototypeProp = fnInstance.getProp('prototype');
                prototypeProp.addType(prototypeObject);
                // For .prototype.constructor
                const constructorProp = prototypeObject.getProp('constructor');
                constructorProp.addType(fnInstance);
            }
            const ret = Ĉ.get(node, curStatus.delta);
            ret.addType(fnInstance);
            return ret;
        },

        FunctionDeclaration: function (node, curStatus, c) {
            // Drop initial catch or normal scopes
            const sc0 = curStatus.sc.removeInitialCatchOrNormalBlocks();
            if (!node.fnInstances) {
                node.fnInstances = [];
            }
            let fnInstance = null;
            node.fnInstances.forEach(function (fnType) {
                if (fnType.sc === sc0) {
                    fnInstance = fnType;
                }
            });
            if (!fnInstance) {
                // NOTE prototype object is not recorded in Ĉ
                fnInstance
                    = new types.FnType(new types.AVal(rtCX.protos.Function),
                                       node.id.name,
                                       node.body['@block'].getParamVarNames(),
                                       sc0,
                                       node,
                                       rtCX.protos.Object);
                node.fnInstances.push(fnInstance);
                // for each fnInstance, assign one prototype object
                // NOTE prototype object is not recorded in Ĉ
                const prototypeObject =
                    new types.ObjType(new types.AVal(rtCX.protos.Object),
                                      node.id.name + '.prototype');
                // For .prototype
                const prototypeProp = fnInstance.getProp('prototype');
                prototypeProp.addType(prototypeObject);
                // For .prototype.constructor
                const constructorProp = prototypeObject.getProp('constructor');
                constructorProp.addType(fnInstance);
            }
            const lhsAVal = sc0.getAValOf(node.id.name);
            lhsAVal.addType(fnInstance);
            // nothing to return
            return types.AValNull;
        },

        SequenceExpression: function (node, curStatus, c) {
            const lastIndex = node.expressions.length - 1;
            for (let i = 0; i < lastIndex; i++) {
                c(node.expressions[i], curStatus, undefined);
            }
            const lastAVal = c(node.expressions[lastIndex], curStatus, undefined);
            Ĉ.set(node, curStatus.delta, lastAVal);
            return lastAVal;
        },

        UnaryExpression: function (node, curStatus, c) {
            c(node.argument, curStatus, undefined);
            const res = Ĉ.get(node, curStatus.delta);
            const type = unopResultType(node.operator);
            if (type) {
                res.addType(type);
            }
            return res;
        },

        UpdateExpression: function (node, curStatus, c) {
            c(node.argument, curStatus, undefined);
            const res = Ĉ.get(node, curStatus.delta);
            res.addType(types.PrimNumber);
            // We ignore the effect of updating to number type
            return res;
        },

        BinaryExpression: function (node, curStatus, c) {
            const lOprd = c(node.left, curStatus, undefined);
            const rOprd = c(node.right, curStatus, undefined);
            const res = Ĉ.get(node, curStatus.delta);

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

        ForStatement: function (node, curStatus, c) {
            if (node['@block']) {
                // if it has @block property
                const forBlockSC =
                    node['@block'].getScopeInstance(curStatus.sc, curStatus.delta);
                curStatus = curStatus.getNewStatus({sc: forBlockSC});
            }
            walk.base.ForStatement(node, curStatus, c);
        },

        BlockStatement: function (node, curStatus, c) {
            if (node['@block']) {
                // if it has @block property
                const normalBlockSC =
                    node['@block'].getScopeInstance(curStatus.sc, curStatus.delta);
                curStatus = curStatus.getNewStatus({sc: normalBlockSC});
            }
            walk.base.BlockStatement(node, curStatus, c);
        },

        TryStatement: function (node, curStatus, c) {
            // construct scope chain for catch block
            const catchBlockSC =
                node.handler.body['@block']
                .getScopeInstance(curStatus.sc, curStatus.delta);
            // get the AVal for exception parameter
            const excAVal = catchBlockSC.getAValOf(node.handler.param.name);

            // for try block
            const tryStatus = curStatus.getNewStatus({exc: excAVal});
            c(node.block, tryStatus, undefined);

            // for catch block
            const catchStatus = curStatus.getNewStatus({sc: catchBlockSC});
            c(node.handler.body, catchStatus, undefined);

            // for finally block
            if (node.finalizer !== null)
                c(node.finalizer, curStatus, undefined);
        },

        ThrowStatement: function (node, curStatus, c) {
            const thr = c(node.argument, curStatus, undefined);
            thr.propagate(curStatus.exc);
        },

        CallExpression: function (node, curStatus, c) {
            const resAVal = Ĉ.get(node, curStatus.delta);
            const argAVals = [];

            // get AVals for each arguments
            for (let i = 0; i < node.arguments.length; i++) {
                argAVals.push(
                    c(node.arguments[i], curStatus, undefined));
            }
            // append current call site to the context
            const newDelta = curStatus.delta.appendOne(node['@label']);

            if (node.callee.type === 'MemberExpression') {
                // method call
                const [recvAVal, retAVal] = readMember(node.callee, curStatus, c);
                retAVal.propagate(
                    new cstr.IsCallee(
                        recvAVal,
                        argAVals,
                        resAVal,
                        curStatus.exc,
                        newDelta));
            } else {
                // normal function call
                const calleeAVal = c(node.callee, curStatus, undefined);
                // callee의 return을 call expression으로
                // callee의 exception을 호출 측의 exception에 전달해야
                calleeAVal.propagate(
                    new cstr.IsCallee(
                        new types.AVal(rtCX.globalObject),
                        argAVals,
                        resAVal,
                        curStatus.exc,
                        newDelta));
            }
            return resAVal;
        },

        MemberExpression: function (node, curStatus, c) {
            const [, retAVal] = readMember(node, curStatus, c);
            return retAVal;
        },

        ReturnStatement: function (node, curStatus, c) {
            if (!node.argument) return;
            const ret = c(node.argument, curStatus, undefined);
            ret.propagate(curStatus.ret);
        }
    });

    myWalker.recursiveWithReturn(ast, initStatus, constraintGenerator);

    // We actually added constraints
    return true;
}

exports.addConstraints = addConstraints;
exports.clearConstraints = clearConstraints;
