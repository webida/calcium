var types = require('../domains/types')
var walk = require('acorn/util/walk');
var status = require('../domains/status');

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

function immedProp(node) {
    var prop = node.property;
    if (!node.computed) return prop.name;
    if (prop.type === 'Literal') return prop.value;
    return '<i>';
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
            return types.AValNull;
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
var visitedStatus = [];
var constraints = [];
function clearConstraints() {
    visitedStatus.length = 0;
    constraints.length = 0;
}

function addConstraints(ast, initStatus, rtCX) {

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
                break;
            case 'string':
                constraints.push({TYPE: types.PrimString,
                                  INCL_SET: res});
                break;
            case 'boolean':
                constraints.push({TYPE: types.PrimBoolean,
                                  INCL_SET: res});
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
            if (node.left.type === 'MemberExpression') {
                // TODO
                // LHS is not a simple variable.
            } else {
                // LHS is a simple variable.
                var varName = node.left.name;
                var lhsAVal = curStatus.sc.getAValOf(varName);
                var rhsAVal = c(node.right, curStatus, undefined);
                constraints.push({FROM: rhsAVal,
                                  TO: lhsAVal});
                // corresponding AVal is the RHS
                return rhsAVal;
            }
        },

        VariableDeclaration: function (node, curStatus, c) {
            for (var i = 0; i < node.declarations.length; i++) {
                var decl = node.declarations[i];
                if (decl.init) {
                    var lhsAVal = curStatus.sc.getAValOf(decl.id.name);
                    var rhsAVal = c(decl.init, curStatus, undefined);
                    constraints.push({FROM: rhsAVal,
                                      TO: lhsAVal});
                }
            }
        },
    
        LogicalExpression: function (node, curStatus, c) {
            var res = new types.AVal;
            var left = c(node.left, curStatus, undefined);
            var right = c(node.right, curStatus, undefined);
            constraints.push({FROM: left, TO: res},
                             {FROM: right, TO: res});
            return res;
        },
    
        ConditionalExpression: function (node, curStatus, c) {
            var res = new types.AVal;
            c(node.test, curStatus, undefined);
            var cons = c(node.consequent, curStatus, undefined);
            var alt = c(node.alternate, curStatus, undefined);
            constraints.push({FROM: cons, TO: res},
                             {FROM: alt, TO: res});
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
            constraints.push({CALLEE: callee,
                              ARGS: args,
                              RET: ret,
                              EXC: curStatus.exc,
                              DELTA: newDelta});
            return ret;
        },

        ArrayExpression: function (node, curStatus, c) {
            var ret = new types.AVal;
            var arrType = new types.ArrType(rtCX.protos.Array);
            constraints.push({TYPE: arrType, INCL_SET: ret});

            for (var i = 0; i < node.elements.length; i++) {
                var eltAVal = c(node.elements[i], undefined);

                constraints.push({OBJ: ret, PROP: i, AVAL: eltAVal});
                constraints.push({OBJ: ret, PROP: '<i>', AVAL: eltAVal});
            }
            return ret;
        },

        ObjectExpression: function (node, curStatus, c) {
            var ret = new types.AVal;
            var objType = new types.ObjType(rtCX.protos.Object);
            constraints.push({TYPE: objType, INCL_SET: ret});

            for (var i = 0; i < node.properties.length; i++) {
                var propPair = node.properties[i];
                var propKey = propPair.key;
                var name;
                var propExpr = propPair.value;

                var fldAVal = c(propExpr, curStatus, undefined);

                if (propKey.type === 'Identifier') {
                    name = propKey.name;
                } else if (typeof propKey.value === 'string'
                        || typeof propKey.value === 'number') {
                    name = propKey.value;
                }
                constraints.push({OBJ: ret, PROP: name, AVAL: fldAVal});
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
                    = new types.FnType(rtCX.protos.Function,
                                       '[anonymous function]',
                                       node.body['@block'].getParamVarNames(),
                                       curStatus.sc);
                node.fnInstances.push(fnInstance);
                var prototypeObject =
                    new types.ObjType(rtCX.protos.Object,
                                      '?.prototype');
                var prototypeProp = fnInstance.getProp('prototype');
                constraints.push({TYPE: prototypeObject,
                                  INCL_SET: prototypeProp});
            }
            var ret = new types.AVal;
            constraints.push({TYPE: fnInstance,
                              INCL_SET: ret});
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
                    = new types.FnType(rtCX.protos.Function,
                                       node.id.name,
                                       node.body['@block'].getParamVarNames(), 
                                       sc0);
                node.fnInstances.push(fnInstance);
                // for each fnInstance, assign one prototype object
                var prototypeObject =
                    new types.ObjType(rtCX.protos.Object,
                                      node.id.name + '.prototype');
                var prototypeProp = fnInstance.getProp('prototype');
                constraints.push({TYPE: prototypeObject,
                                  INCL_SET: prototypeProp});
            }
            var lhsAVal = sc0.getAValOf(node.id.name);

            constraints.push({TYPE: fnInstance,
                              INCL_SET: lhsAVal});
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
            constraints.push({TYPE: unopResultType(node.operator),
                              INCL_SET: res});
            return res;
        },

        UpdateExpression: function (node, curStatus, c) {
            c(node.argument, curStatus, undefined);
            var res = new types.AVal;
            constraints.push({TYPE: types.PrimNumber,
                              INCL_SET: res});
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
            } else {
                if (binopIsBoolean(node.operator)) {
                    constraints.push({TYPE: types.PrimBoolean,
                                      INCL_SET: res});
                } else {
                    constraints.push({TYPE: types.PrimNumber,
                                      INCL_SET: res});
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
        },

        CallExpression: function (node, curStatus, c) {
            var resAVal = new types.AVal;
            var argAVals = [];
            
            // get AVals for each arguments
            for (var i = 0; i < node.arguments.length; i++) {
                argAVals.push(
                    c(node.arguments[i], curStatus, undefined));
            }
    
            if (node.callee.type === 'MemberExpression') {
    
                // TODO: method call
            } else {
                // normal function call
                var calleeAVal = c(node.callee, curStatus, undefined);
                // append current call site to the context
                var newDelta = curStatus.delta.appendOne(node['@label']);
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
            }
            return resAVal;
        },

        MemberExpression: function (node, curStatus, c) {
            var ret = new types.AVal;
            var objAVal = c(node.object, curStatus, undefined);
            if (node.property.type !== 'Identifier') {
                // return from property is ignored
                c(node.property, curStatus, undefined);
            }
            var name = immedProp(node);

            constraints.push({OBJ: objAVal,
                              PROP: name,
                              READ_TO: ret});
            return ret;
        },

        ReturnStatement: function (node, curStatus, c) {
            if (!node.argument) return;
            var ret = c(node.argument, curStatus, undefined);
            constraints.push({FROM: ret,
                              TO: curStatus.ret});
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