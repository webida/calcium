var a, b;

function f1(a, b) {
    var a, b;
}

function f2(a, b = a) {
    var a;
    b;
}

function f3(a = () => b) { }

function f4({a, b : b}, x = a, y = b) { }

function f5(a = arguments) {
    arguments;
}

function f6(arguments) {
    function f7(a = arguments) {
        arguments;
    }
}
