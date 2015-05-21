var i = 0, j, pairs ='';

while (i < 5) {
  i++;
  if (i === 3) {
    continue;
  }
  j = 0;
  do {
	j += 1;
	console.log(j);
	pairs += '(' + i + ',' + j + ')\n';
  } while (j < 5);
}
