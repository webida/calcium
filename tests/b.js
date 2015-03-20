var g = 3;
try {
  throw 100;
} catch (e) {
  var f = 1;
	try {
	  throw 'a';
  } catch (g) {
	  var e, g = 10;
		e++;
	}
  console.log(e);
}

console.log('f: ' + f);
console.log('g: ' + g);

