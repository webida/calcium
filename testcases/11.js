try {
    throw 3; 
} catch (e) {
    var a = e; 
}

function pitcher() {
    throw ''; 
}  

try {
    pitcher(); 
} catch (e) { 	
    var b = e; 
}
