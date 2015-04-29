// import necessary libraries
// var acorn = require('acorn/acorn');
var acorn_loose = require('acorn/acorn_loose');
var aux = require('./aux');
var types = require('./domains/types');
var context = require('./domains/context');

function analyze(input) {
    // the Scope object for global scope
    // scope.Scope.globalScope = new scope.Scope(null);

    // parsing input program
    var ast = acorn_loose.parse_dammit(input);

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
    var varBlock = require('./varBlock');
    var gBlockAndAnnotatedAST = varBlock.annotateBlockInfo(ast);
    var gBlock = gBlockAndAnnotatedAST.globalBlock;
    var gScope = gBlock.getScopeInstance(null, []);
    var gObject = types.mkObjFromGlobalScope(gScope);
    var cGen = require('./constraint/cGen');
    var initialContext = new context.CallSiteContext;
    var initStatus = {
        self: gObject,
        ret: types.AValNull,
        exc: types.AValNull,
        delta: initialContext,
        sc: gScope
    };
    var cx = {
        globalObject: gObject
        // bindings for Object, Function, and so on
    };
    var constraints = cGen.getConstraints(ast, initStatus, cx);
    aux.showUnfolded(gBlockAndAnnotatedAST.ast);
    aux.showUnfolded(constraints);
    aux.showUnfolded(gBlock);

}

exports.analyze = analyze;