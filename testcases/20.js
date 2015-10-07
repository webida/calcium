// context-sensitively analyze all functions
function id(x) { return x; }
var x = id(1);
var y = id(true);

function foo(y) { return y; }
var a = foo(1);
var b = foo(true);
