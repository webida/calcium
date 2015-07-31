var x = 3, y = x;
function id(x) {
    var y,z;
    return x;
}

try {
    throw new Error;
} catch (e) {
    console.log(e);
} finally {
    console.log('END');
}
