// import necessary libraries
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
    var initialContext = new context.CallSiteContext;
    var gScope = gBlock.getScopeInstance(null, initialContext);
    var gObject = types.mkObjFromGlobalScope(gScope);
    var initStatus = new status.Status(
        gObject,
        types.AValNull,
        types.AValNull,
        initialContext,
        gScope);
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
        return {gObject: gObject, AST: ast};
    } else {
        return gObject;
    }
}

exports.analyze = analyze;
exports.findIdentifierNodeAt = varRefs.findIdentifierNodeAt;