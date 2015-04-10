function f() {
    var ret, h = 1;
    try {
        throw new Error;
    } catch (g) {
        // function g() {
        //  return 'called';
        // }
        var g = function () { return 'called'; };
        ret = g;
    }
    console.log(ret);
    // g callable. So, g is in f's scope.
    // function 
    console.log(g());
}

try {
    f();
} catch (e) {
    console.log('!!!');
}

// function declarations are not bound to catch scopes.
// but anonymous functions assigned to variables can be bound to catch scopes.
