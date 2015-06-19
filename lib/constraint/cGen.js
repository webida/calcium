var types = require('../domains/types')
var walk = require('acorn/dist/walk');
var status = require('../domains/status');
var cstr = require('./constraints');

// arguments are " oldStatus (, name, val)* "
function changedStatus(oldStatus) {
    var newStatus = new status.Status;
    for (var i = 1; i < arguments.length; i = i + 2)
        newStatus[arguments[i]] = arguments[i+1];

    for (var p in oldStatus) {
        if (newStatus[p] === undefined)
            newStatus[p] = oldStatus[p];
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
        if (typeof prop.value === 'string')
            return ['stringLiteral', prop.value];
        if (typeof prop.value === 'number')
            // convert number to string
            return ['numberLiteral', prop.value + ''];
    }
    return ["computed", null];
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

function readMember(node, curStatus, c) {
    var ret = new types.AVal;
    var objAVal = c(node.object, curStatus, undefined);
    if (node.property.type !== 'Identifier') {
        // return from property is ignored
        c(node.property, curStatus, undefined);
    }
    var propAcc = propAccess(node);

    constraints.push({OBJ: objAVal,
                      PROP: propAcc[1],
                      READ_TO: ret});
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

var rtCX;
function addConstraints(ast, initStatus, newRtCX) {

    // set rtCX
    rtCX = newRtCX || rtCX;

    // Check whether we have processed 'initStatus' before
    for (var i=0; i < visitedStatus.length; i++) {
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

        Identifier: function (node, curStatus, c) {
            return curStatus.sc.getAValOf(node.name);
        },

        ThisExpression: function (node, curStatus, c) {
            return curStatus.self;
        },

        Literal: function (node, curStatus, c) {
            var res = new types.AVal;
            if (node.regex) {
                // not implemented yet
                // throw new Error('regex literal is not implemented yet');
                return res;
            }
            switch (typeof node.value) {
            case 'number':
                constraints.push({TYPE: types.PrimNumber,
                                  INCL_SET: res});
                res.addType(types.PrimNumber);
                break;
            case 'string':
                constraints.push({TYPE: types.PrimString,
                                  INCL_SET: res});
                res.addType(types.PrimString);
                break;
            case 'boolean':
                constraints.push({TYPE: types.PrimBoolean,
                                  INCL_SET: res});
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
            var rhsAVal = c(node.right, curStatus, undefined);
            if (node.left.type !== 'MemberExpression') {
                // LHS is a simple variable.
                var varName = node.left.name;
                var lhsAVal = curStatus.sc.getAValOf(varName);
                constraints.push({FROM: rhsAVal,
                                  TO: lhsAVal});
                rhsAVal.propagate(lhsAVal);
                // corresponding AVal is the RHS
                return rhsAVal;
            }
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
                // if property is number literal, also write to <i>
                if (propAcc[0] === 'numberLiteral') {
                    objAVal.propagate(new cstr.WriteProp(null, rhsAVal));
                }
                return rhsAVal;
            }
            var resAVal = new types.AVal;
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
            constraints.push({
                OBJ: recvAndRet[0],
                PROP: propAcc,
                WRITE_WITH: resAVal
            });
            recvAndRet[0].propagate(new cstr.WriteProp(propAcc, resAVal));
            return resAVal;
        },

        VariableDeclaration: function (node, curStatus, c) {
            for (var i = 0; i < node.declarations.length; i++) {
                var decl = node.declarations[i];
                if (decl.init) {
                    var lhsAVal = curStatus.sc.getAValOf(decl.id.name);
                    var rhsAVal = c(decl.init, curStatus, undefined);
                    constraints.push({FROM: rhsAVal,
                                      TO: lhsAVal});
                    rhsAVal.propagate(lhsAVal);
                }
            }
        },

        LogicalExpression: function (node, curStatus, c) {
            var res = new types.AVal;
            var left = c(node.left, curStatus, undefined);
            var right = c(node.right, curStatus, undefined);
            constraints.push({FROM: left, TO: res},
                             {FROM: right, TO: res});
            left.propagate(res);
            right.propagate(res);
            return res;
        },

        ConditionalExpression: function (node, curStatus, c) {
            var res = new types.AVal;
            c(node.test, curStatus, undefined);
            var cons = c(node.consequent, curStatus, undefined);
            var alt = c(node.alternate, curStatus, undefined);
            constraints.push({FROM: cons, TO: res},
                             {FROM: alt, TO: res});
            cons.propagate(res);
            alt.propagate(res);
            return res;
        },

        NewExpression: function (node, curStatus, c) {
            var ret = new types.AVal;
            var callee = c(node.callee, curStatus, undefined);
            var args = [];
            for (var i = 0; i < node.arguments.length; i++) {
                args.push(c(node.arguments[i], curStatus, undefined));
            }
            var newDelta = curStatus.delta.appendOne(node['@label']);
            constraints.push({CONSTRUCTOR: callee,
                              ARGS: args,
                              RET: ret,
                              EXC: curStatus.exc,
                              DELTA: newDelta});
            callee.propagate(
                new cstr.IsCtor(
                    args,
                    ret,
                    curStatus.exc,
                    newDelta));
            return ret;
        },

        ArrayExpression: function (node, curStatus, c) {
            var ret = new types.AVal;
            var arrType = new types.ArrType(new types.AVal(rtCX.protos.Array));
            // add length property
            arrType.getProp('length').addType(types.PrimNumber);

            constraints.push({TYPE: arrType, INCL_SET: ret});
            ret.addType(arrType);

            // add array elements
            for (var i = 0; i < node.elements.length; i++) {
                var eltAVal = c(node.elements[i], curStatus, undefined);

                var prop = i + '';
                constraints.push({OBJ: ret, PROP: prop, AVAL: eltAVal});
                constraints.push({OBJ: ret, PROP: null, AVAL: eltAVal});
                ret.propagate(new cstr.WriteProp(prop, eltAVal));
                ret.propagate(new cstr.WriteProp(null, eltAVal));
            }
            return ret;
        },

        ObjectExpression: function (node, curStatus, c) {
            var ret = new types.AVal;
            var objType = new types.ObjType(new types.AVal(rtCX.protos.Object));
            constraints.push({TYPE: objType, INCL_SET: ret});
            ret.addType(objType);

            for (var i = 0; i < node.properties.length; i++) {
                var propPair = node.properties[i];
                var propKey = propPair.key;
                var name;
                var propExpr = propPair.value;

                var fldAVal = c(propExpr, curStatus, undefined);

                if (propKey.type === 'Identifier') {
                    name = propKey.name;
                } else if (typeof propKey.value === 'string') {
                    name = propKey.value;
                } else if (typeof propKey.value === 'number') {
                    // convert number to string
                    name = propKey.value + '';
                }
                constraints.push({OBJ: ret, PROP: name, AVAL: fldAVal});
                ret.propagate(new cstr.WriteProp(name, fldAVal));
            }
            return ret;
        },

        FunctionExpression: function (node, curStatus, c) {
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
                fnInstance
                    = new types.FnType(new types.AVal(rtCX.protos.Function),
                                       '[anonymous function]',
                                       node.body['@block'].getParamVarNames(),
                                       curStatus.sc,
                                       node,
                                       rtCX.protos.Object);
                node.fnInstances.push(fnInstance);
                var prototypeObject =
                    new types.ObjType(new types.AVal(rtCX.protos.Object),
                                      '?.prototype');
                // For .prototype
                var prototypeProp = fnInstance.getProp('prototype');
                constraints.push({TYPE: prototypeObject,
                                  INCL_SET: prototypeProp});
                prototypeProp.addType(prototypeObject);
                // For .prototype.constructor
                var constructorProp = prototypeObject.getProp('constructor');
                constraints.push({TYPE: fnInstance,
                                  INCL_SET: constructorProp});
                constructorProp.addType(fnInstance);
            }
            var ret = new types.AVal;
            constraints.push({TYPE: fnInstance,
                              INCL_SET: ret});
            ret.addType(fnInstance);
            return ret;
        },

        FunctionDeclaration: function (node, curStatus, c) {
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
                fnInstance
                    = new types.FnType(new types.AVal(rtCX.protos.Function),
                                       node.id.name,
                                       node.body['@block'].getParamVarNames(),
                                       sc0,
                                       node,
                                       rtCX.protos.Object);
                node.fnInstances.push(fnInstance);
                // for each fnInstance, assign one prototype object
                var prototypeObject =
                    new types.ObjType(new types.AVal(rtCX.protos.Object),
                                      node.id.name + '.prototype');
                // For .prototype
                var prototypeProp = fnInstance.getProp('prototype');
                constraints.push({TYPE: prototypeObject,
                                  INCL_SET: prototypeProp});
                prototypeProp.addType(prototypeObject);
                // For .prototype.constructor
                var constructorProp = prototypeObject.getProp('constructor');
                constraints.push({TYPE: fnInstance,
                                  INCL_SET: constructorProp});
                constructorProp.addType(fnInstance);
            }
            var lhsAVal = sc0.getAValOf(node.id.name);

            constraints.push({TYPE: fnInstance,
                              INCL_SET: lhsAVal});
            lhsAVal.addType(fnInstance);
            // nothing to return
            return types.AValNull;
        },

        SequenceExpression: function (node, curStatus, c) {
            var lastIndex = node.expressions.length - 1;
            for (var i = 0; i < lastIndex; i++) {
                c(node.expressions[i], curStatus, undefined);
            }
            return c(node.expressions[lastIndex], curStatus, undefined);
        },

        UnaryExpression: function (node, curStatus, c) {
            c(node.argument, curStatus, undefined);
            var res = new types.AVal;
            var type = unopResultType(node.operator);
            if (type) {
                constraints.push({TYPE: type,
                                  INCL_SET: res});
                res.addType(type);
            }
            return res;
        },

        UpdateExpression: function (node, curStatus, c) {
            c(node.argument, curStatus, undefined);
            var res = new types.AVal;
            constraints.push({TYPE: types.PrimNumber,
                              INCL_SET: res});
            res.addType(types.PrimNumber);
            // We ignore the effect of updating to number type
            return res;
        },

        BinaryExpression: function (node, curStatus, c) {
            var lOprd = c(node.left, curStatus, undefined);
            var rOprd = c(node.right, curStatus, undefined);
            var res = new types.AVal;

            if (node.operator == '+') {
                constraints.push({ADD_OPRD1: lOprd,
                                  ADD_OPRD2: rOprd,
                                  RESULT: res });
                lOprd.propagate(new cstr.IsAdded(rOprd, res));
                rOprd.propagate(new cstr.IsAdded(lOprd, res));
            } else {
                if (binopIsBoolean(node.operator)) {
                    constraints.push({TYPE: types.PrimBoolean,
                                      INCL_SET: res});
                    res.addType(types.PrimBoolean);
                } else {
                    constraints.push({TYPE: types.PrimNumber,
                                      INCL_SET: res});
                    res.addType(types.PrimNumber);
                }
            }
            return res;
        },

        TryStatement: function (node, curStatus, c) {
            // construct scope chain for catch block
            var catchBlockSC =
                node.handler.body['@block']
                .getScopeInstance(curStatus.sc, curStatus.delta);
            // get the AVal for exception parameter
            var excAVal = catchBlockSC.getAValOf(node.handler.param.name);

            // for try block
            var tryStatus = changedStatus(curStatus, 'exc', excAVal);
            c(node.block, tryStatus, undefined);

            // for catch block
            var catchStatus = changedStatus(curStatus, 'sc', catchBlockSC);
            c(node.handler.body, catchStatus, undefined);

            // for finally block
            if (node.finalizer !== null)
                c(node.finalizer.body, curStatus, undefined);
        },

        ThrowStatement: function (node, curStatus, c) {
            var thr = c(node.argument, curStatus, undefined);
            constraints.push({FROM: thr,
                              TO: curStatus.exc});
            thr.propagate(curStatus.exc);
        },

        CallExpression: function (node, curStatus, c) {
            var resAVal = new types.AVal;
            var argAVals = [];

            // get AVals for each arguments
            for (var i = 0; i < node.arguments.length; i++) {
                argAVals.push(
                    c(node.arguments[i], curStatus, undefined));
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
                recvAndRet[1].propagate(
                    new cstr.IsCallee(
                        recvAndRet[0],
                        argAVals,
                        resAVal,
                        curStatus.exc,
                        newDelta));
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
            var recvAndRet = readMember(node, curStatus, c);
            return recvAndRet[1];
        },

        ReturnStatement: function (node, curStatus, c) {
            if (!node.argument) return;
            var ret = c(node.argument, curStatus, undefined);
            constraints.push({FROM: ret,
                              TO: curStatus.ret});
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
