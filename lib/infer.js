// import necessary libraries
// var acorn = require('acorn/acorn');
var acorn_loose = require('acorn/acorn_loose');
var walk = require('acorn/util/walk');
var cGen = require('./cGen');
var aux = require('./aux');
var scope = require('./scope');
var scopeResolver = require('./scopeResolver');


function analyze(input) {
    // the Scope object for global scope
    scope.Scope.globalScope = new scope.Scope(null);

    // parsing input program
    var ast = acorn_loose.parse_dammit(input);

    var nodeArrayIndexedByList = aux.getNodeList(ast);
    // console.log(nodeArrayIndexedByList);

    // Show AST before scope resolution
    aux.showUnfolded(ast);

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

}

exports.analyze = analyze;