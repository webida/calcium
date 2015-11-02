'use strict';

var t1, t2, t3;
function f() {
    let x = 3;
    {
        let x = '';
        t2 = x;
        let y = true;
        t3 = y;
    }
    t1 = x;
}

f();
