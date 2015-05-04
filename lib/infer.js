// import necessary libraries
// var acorn = require('acorn/acorn');
var acorn_loose = require('acorn/acorn_loose');
var aux = require('./aux');
var types = require('./domains/types');
var context = require('./domains/context');
var status = require('./domains/status')

function analyze(input) {
    // the Scope object for global scope
    // scope.Scope.globalScope = new scope.Scope(null);

    // parsing input program
    var ast = acorn_loose.parse_dammit(input);

    var nodeArrayIndexedByList = aux.getNodeList(ast);
//    console.log(nodeArrayIndexedByList);

    // Show AST before scope resolution
    aux.showUnfolded(ast);

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
    var initialContext = new context.CallSiteContext;
    var gScope = gBlock.getScopeInstance(null, initialContext);
    var gObject = types.mkObjFromGlobalScope(gScope);
    var cGen = require('./constraint/cGen');
    var initStatus = new status.Status(
        gObject,
        types.AValNull,
        types.AValNull,
        initialContext,
        gScope);
    var rtCX = {
        globalObject: gObject
        // bindings for Object, Function, and so on
    };
    cGen.addConstraints(ast, initStatus, rtCX);
    var constraints = cGen.constraints;
    aux.showUnfolded(gBlockAndAnnotatedAST.ast);
    aux.showUnfolded(constraints);
    aux.showUnfolded(gBlock);

}

exports.analyze = analyze;