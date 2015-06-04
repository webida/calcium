var chai = require('chai');
var assert = chai.assert, expect = chai.expect, should = chai.should();
var fs = require('fs');
var infer = require('../lib/infer.js');

describe('YAtern', function () {
	it('should analyze 01.js successfuly', function () {
	  var data = fs.readFileSync('./testcases/01.js').toString();
		infer.analyze(data);
		assert.equal(0,0);
  })
	it('should analyze 02.js successfuly', function () {
	  var data = fs.readFileSync('./testcases/02.js').toString();
		infer.analyze(data);
		assert.equal(0,0);
  })
	it('should analyze 03.js successfuly', function () {
	  var data = fs.readFileSync('./testcases/03.js').toString();
		infer.analyze(data);
		assert.equal(0,0);
  })
	it('should analyze 04.js successfuly', function () {
	  var data = fs.readFileSync('./testcases/04.js').toString();
		infer.analyze(data);
		assert.equal(0,0);
  })
	it('should analyze 05.js successfuly', function () {
	  var data = fs.readFileSync('./testcases/05.js').toString();
		infer.analyze(data);
		assert.equal(0,0);
  })
	it('should analyze 06.js successfuly', function () {
	  var data = fs.readFileSync('./testcases/06.js').toString();
		infer.analyze(data);
		assert.equal(0,0);
  })
	it('should analyze 07.js successfuly', function () {
	  var data = fs.readFileSync('./testcases/07.js').toString();
		infer.analyze(data);
		assert.equal(0,0);
  })
	it('should analyze 08.js successfuly', function () {
	  var data = fs.readFileSync('./testcases/08.js').toString();
		infer.analyze(data);
		assert.equal(0,0);
  })
	it('should analyze 09.js successfuly', function () {
	  var data = fs.readFileSync('./testcases/09.js').toString();
		infer.analyze(data);
		assert.equal(0,0);
  })
	it('should analyze 10.js successfuly', function () {
	  var data = fs.readFileSync('./testcases/10.js').toString();
		infer.analyze(data);
		assert.equal(0,0);
  })
	it('should analyze 11.js successfuly', function () {
	  var data = fs.readFileSync('./testcases/11.js').toString();
		infer.analyze(data);
		assert.equal(0,0);
  })
})

