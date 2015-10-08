var chai = require('chai');
var assert = chai.assert,
    expect = chai.expect,
    should = chai.should();
var fs = require('fs');
var infer = require('../lib/infer');
import * as types from '../lib/domains/types'

function hasTypes(aval, types) {
    expect(aval.types.size).to.be.equal(types.length);
    aval.types.forEach(function (type) {
        expect(types).to.include(type);
    });
}

function getIfSingleton(set) {
    expect(set.size).to.be.equal(1);
    var elt = null;
    set.forEach(function (e) {
       elt = e;
    });
    return elt;
}

describe('YAtern', function () {

    it('should analyze 01.js successfully', function () {
        var data = fs.readFileSync('./testcases/01.js').toString();
        var gObject = infer.analyze(data);

        hasTypes(gObject.getProp('x', true), [types.PrimNumber]);
    });

    it('should analyze 02.js successfully', function () {
        var data = fs.readFileSync('./testcases/02.js').toString();
        var gObject = infer.analyze(data);

        hasTypes(gObject.getProp('x', true), [types.PrimNumber]);
        hasTypes(gObject.getProp('y', true), [types.PrimBoolean]);
    });

    it('should analyze 03.js successfully', function () {
        var data = fs.readFileSync('./testcases/03.js').toString();
        var gObject = infer.analyze(data);

        hasTypes(gObject.getProp('i', true), [types.PrimNumber]);
        hasTypes(gObject.getProp('j', true), [types.PrimNumber]);
    });

    it('should analyze 04.js successfully', function () {
        var data = fs.readFileSync('./testcases/04.js').toString();
        var gObject = infer.analyze(data);

        hasTypes(gObject.getProp('i', true), [types.PrimNumber]);
        hasTypes(gObject.getProp('j', true), [types.PrimNumber]);
        hasTypes(gObject.getProp('pairs', true), [types.PrimString]);
    });

    it('should analyze 05.js successfully', function () {
        var data = fs.readFileSync('./testcases/05.js').toString();
        var gObject = infer.analyze(data);

        hasTypes(gObject.getProp('isEven', true), [types.PrimBoolean]);
    });

    it('should analyze 06.js successfully', function () {
        var data = fs.readFileSync('./testcases/06.js').toString();
        var gObject = infer.analyze(data);

        hasTypes(gObject.getProp('x', true), [types.PrimNumber]);
        hasTypes(gObject.getProp('x1', true), [types.PrimNumber]);
        hasTypes(gObject.getProp('x2', true), [types.PrimNumber]);
        hasTypes(gObject.getProp('x3', true), [types.PrimNumber]);
        hasTypes(gObject.getProp('x4', true), [types.PrimBoolean]);
        hasTypes(gObject.getProp('x5', true), [types.PrimString]);
        hasTypes(gObject.getProp('x6', true), []);
        hasTypes(gObject.getProp('y1', true), [types.PrimNumber]);
        hasTypes(gObject.getProp('y2', true), [types.PrimNumber]);
        hasTypes(gObject.getProp('y3', true), [types.PrimNumber]);
        hasTypes(gObject.getProp('y4', true), [types.PrimNumber]);
        hasTypes(gObject.getProp('y5', true), [types.PrimNumber]);
        hasTypes(gObject.getProp('y6', true), [types.PrimBoolean]);
        hasTypes(gObject.getProp('y7', true), [types.PrimBoolean]);
    });

    it('should analyze 07.js successfully', function () {
        var data = fs.readFileSync('./testcases/07.js').toString();
        var gObject = infer.analyze(data);

        hasTypes(gObject.getProp('x1', true),
                 [types.PrimNumber, types.PrimBoolean]);
        hasTypes(gObject.getProp('x2', true),
                 [types.PrimNumber, types.PrimString]);
        hasTypes(gObject.getProp('x3', true), [types.PrimBoolean]);
    });

    it('should analyze 08.js successfully', function () {
        var data = fs.readFileSync('./testcases/08.js').toString();
        var gObject = infer.analyze(data);

        hasTypes(gObject.getProp('one', true), [types.PrimNumber]);
        hasTypes(gObject.getProp('ab', true), [types.PrimString]);
    });

    it('should analyze 09.js successfully', function () {
        var data = fs.readFileSync('./testcases/09.js').toString();
        var gObject = infer.analyze(data);

        var type = getIfSingleton(gObject.getProp('foo', true).types);
        hasTypes(type.getProp('data', true), [types.PrimString]);
        hasTypes(gObject.getProp('y', true), [types.PrimString]);
    });

    it('should analyze 10.js successfully', function () {
        var data = fs.readFileSync('./testcases/10.js').toString();
        var gObject = infer.analyze(data);

        hasTypes(gObject.getProp('v', true), [types.PrimNumber]);

        var obj_type = getIfSingleton(gObject.getProp('obj', true).types);
        var aval_obj_x = obj_type.getProp('x', true),
            aval_obj_z = obj_type.getProp('z', true),
            aval_obj_1 = obj_type.getProp('1', true);
        hasTypes(aval_obj_x, [types.PrimNumber]);
        hasTypes(aval_obj_z, [types.PrimString]);
        hasTypes(aval_obj_1, [types.PrimNumber]);

        var arr_type = getIfSingleton(gObject.getProp('arr', true).types);
        hasTypes(arr_type.getProp('3', true), [types.PrimString]);

        hasTypes(gObject.getProp('n', true), [types.PrimNumber]);
        hasTypes(gObject.getProp('b', true), [types.PrimBoolean]);
        hasTypes(gObject.getProp('s', true), [types.PrimString]);
        hasTypes(gObject.getProp('l', true), [types.PrimNumber]);
    });

    it('should analyze 11.js successfully', function () {
        var data = fs.readFileSync('./testcases/11.js').toString();
        var gObject = infer.analyze(data);

        hasTypes(gObject.getProp('a', true), [types.PrimNumber]);
        hasTypes(gObject.getProp('b', true), [types.PrimString]);
    });

    it('should analyze 12.js successfully', function () {
        var data = fs.readFileSync('./testcases/12.js').toString();
        var gObject = infer.analyze(data);

        hasTypes(gObject.getProp('x1', true), [types.PrimBoolean]);
        hasTypes(gObject.getProp('x2', true), [types.PrimBoolean]);
        hasTypes(gObject.getProp('x3', true), [types.PrimString]);
        hasTypes(gObject.getProp('x4', true), [types.PrimString]);
        hasTypes(gObject.getProp('x5', true), [types.PrimBoolean]);
        hasTypes(gObject.getProp('x6', true), [types.PrimBoolean]);
    });

    it('should analyze 13.js successfully', function () {
        var data = fs.readFileSync('./testcases/13.js').toString();
        var gObject = infer.analyze(data);

        hasTypes(gObject.getProp('x', true), [types.PrimBoolean]);
        hasTypes(gObject.getProp('y', true), [types.PrimNumber]);
        hasTypes(gObject.getProp('z', true), [types.PrimNumber]);
    });

    it('should analyze 14.js successfully', function () {
        var data = fs.readFileSync('./testcases/14.js').toString();
        var gObject = infer.analyze(data);

        hasTypes(gObject.getProp('x', true), [types.PrimString]);
    });

    it('should analyze 15.js successfully', function () {
        var data = fs.readFileSync('./testcases/15.js').toString();
        var gObject = infer.analyze(data);

        hasTypes(gObject.getProp('t1', true), [types.PrimNumber]);
        hasTypes(gObject.getProp('t2', true), [types.PrimString]);
        hasTypes(gObject.getProp('t3', true), [types.PrimBoolean]);
    });

    it('should analyze 16.js successfully', function () {
        var data = fs.readFileSync('./testcases/16.js').toString();
        var gObject = infer.analyze(data);

        hasTypes(gObject.getProp('a0', true), [types.PrimNumber, types.PrimBoolean]);
        hasTypes(gObject.getProp('a1', true), [types.PrimNumber]);
        hasTypes(gObject.getProp('a3', true), [types.PrimBoolean]);
    });

    it('should analyze 17.js successfully', function () {
        var data = fs.readFileSync('./testcases/17.js').toString();
        var gObject = infer.analyze(data);

        hasTypes(gObject.getProp('x', true), []);
        hasTypes(gObject.getProp('y', true), [types.PrimString]);
    });

    it('should analyze 18.js successfully', function () {
        var data = fs.readFileSync('./testcases/18.js').toString();
        var gObject = infer.analyze(data);

        hasTypes(gObject.getProp('x', true), [types.PrimNumber]);
        hasTypes(gObject.getProp('y', true), []);
    });

    it('should analyze 19.js successfully', function () {
        var data = fs.readFileSync('./testcases/19.js').toString();
        var gObject = infer.analyze(data);

        hasTypes(gObject.getProp('x', true), [types.PrimNumber]);
        hasTypes(gObject.getProp('y', true), [types.PrimBoolean]);
        hasTypes(gObject.getProp('z', true), [types.PrimString]);
    });

    it('should analyze 20.js successfully', function () {
        var data = fs.readFileSync('./testcases/20.js').toString();
        var options = require('../testcases/options/oneSensitiveOption').options;
        var gObject = infer.analyze(data, false, options);

        hasTypes(gObject.getProp('x', true), [types.PrimNumber]);
        hasTypes(gObject.getProp('y', true), [types.PrimBoolean]);
        hasTypes(gObject.getProp('a', true), [types.PrimNumber]);
        hasTypes(gObject.getProp('b', true), [types.PrimBoolean]);
    });

    it('should analyze 21.js successfully', function () {
        var data = fs.readFileSync('./testcases/21.js').toString();
        var options = require('../testcases/options/nameBasedSensitiveOption').options;
        var gObject = infer.analyze(data, false, options);

        hasTypes(gObject.getProp('x', true), [types.PrimNumber]);
        hasTypes(gObject.getProp('y', true), [types.PrimBoolean]);
        hasTypes(gObject.getProp('a', true), [types.PrimNumber, types.PrimBoolean]);
        hasTypes(gObject.getProp('b', true), [types.PrimNumber, types.PrimBoolean]);
    });

    it('should analyze 22.js successfully', function () {
        var data = fs.readFileSync('./testcases/22.js').toString();
        var result = infer.analyze(data, true);

        var getTypeAtRange = require('../lib/getTypeData').getTypeAtRange;

        var typeOfArr = getTypeAtRange(result.AST, result.Ĉ, 5, 5).typeString;
        expect(typeOfArr).to.be.equal('[?]');
    });
});
