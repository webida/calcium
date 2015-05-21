var x = undefined;
var y = NaN;
var z = Infinity;

var o = {};

var regex = /abc/;

function f() {
    var Infinity = 0;
    var NaN = 0;
    var undefined = 0;
    var null = 0;
    console.log(Infinity);
    console.log(NaN);
    console.log(undefined);
    console.log(null);
    
}


f();
