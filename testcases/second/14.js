function f(y) {
    try {
        throw 0;        // 0
        try {
            throw 2;    // 1
            return 4;   // 2
        } catch (e) {   // 3
            throw 3;    // 4
        }

    } catch (y) {       // 5
        throw y;        // 6
    } finally {
        throw function () { // 7
            return;         // 8
        };
    }
    return y;           // 9
}
