'use strict';

var x = 3;
var y = false;

function ggg() {
    this.GGG = 3;
}
ggg();  // 1

function id(x) {
    return x;
}
id(x);  // 2

function add(x,y) {
    return x + y;
}

add(1,'');  // 3
