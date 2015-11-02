var res;
try {
    var x = 1;
} catch (x) {
    res = x;
    try {
        var y;
    } catch (x) {
        res = x + y;
    }
} finally {
    res = x + y;
}
