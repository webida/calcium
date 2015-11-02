'use strict';

function add(x,y) {     // 1
    return x + y;
}

add(1,'');  // 2

function Foo(data) {    // 3
    this.data = data;
}
Foo.prototype.getData = function () {   // 4
    return this.data;
};

var foo = new Foo('Hello');     // 5
console.log(foo.getData());     // 6
