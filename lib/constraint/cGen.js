var types = require('../domains/types')
var walk = require('acorn/util/walk');

// status:
// { self  : AVal, 
//   ret   : AVal, 
//   exc   : AVal, 
//   delta : Context,
//   sc    : ScopeChain }

// arguments are " oldStatus (, name, val)* "
function changedStatus(oldStatus) {
    var newStatus = Object.create(null);
    for (var i = 1; i < arguments.length; i = i + 2)
        newStatus[arguments[i]] = arguments[i+1];

    for (var p in oldStatus) {
        if (newStatus[p] === undefined) 
            newStatus[p] = oldStatus[p];
    }
    return newStatus;
}

function unopResultType(op) {
    switch (op) {
        case '+': case '-': case '~': return types.PrimNumber;
        case '!': return types.PrimBoolean;
        case 'typeof': return types.PrimString;
        case 'void': case 'delete': return types.AValNull;
    }
}

function getConstraints(ast, gScope, cx) {
    // temporal set for generated constraints.
    var constraints = [];

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
        
        FunctionDeclaration: function (node, curStatus, c) {
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
                    = new types.FnType(node.id.name, 
                                       node.body['@block'].getParamVarNames(), 
                                       sc0);
                node.fnInstances.push(fnInstance);
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
            res.addType(unopResultType(node.operator));
            return res;
        },

        UpdateExpression: function (node, curStatus, c) {
            c(node.argument, curStatus, undefined);
            var res = new types.AVal;
            res.addType(types.PrimNumber);
            // We ignore the effect of updating to number type
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
                    SELF: cx.globalObject,
                    PARAMS: argAVals,
                    RET: resAVal,
                    EXC: curStatus.exc,
                    DELTA: newDelta
                });
            }
            return resAVal;
        },

        ReturnStatement: function (node, curStatus, c) {
            if (!node.argument) return;
            var ret = c(node.argument, curStatus, undefined);
            constraints.push({FROM: ret,
                              TO: curStatus.ret});
        }
    });

    recursiveWithReturn(ast, gScope, constraintGenerator);

    return constraints;
}

function recursiveWithReturn(node, state, visitor) {
    function c(node, st, override) {
        return visitor[override || node.type](node, st, c);
    }
    return c(node, state);
}

exports.getConstraints = getConstraints;
