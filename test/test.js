var chai = require('chai');
var assert = chai.assert,
    expect = chai.expect,
    should = chai.should();
var fs = require('fs');
var infer = require('../lib/infer');
var types = require('../lib/domains/types');

function hasTypes(aval, types) {
    expect(aval).to.have.property('types').with.length(types.length);
    types.forEach(function (type) {
        expect(aval.types).to.include(type);
    });
}


describe('YAtern', function () {

    it('should analyze 01.js successfuly', function () {
        var data = fs.readFileSync('./testcases/01.js').toString();
        var gObject = infer.analyze(data);

        hasTypes(gObject.getProp('x', true), [types.PrimNumber]);
    })

    it('should analyze 02.js successfuly', function () {
        var data = fs.readFileSync('./testcases/02.js').toString();
        var gObject = infer.analyze(data);

        hasTypes(gObject.getProp('x', true), [types.PrimNumber]);
        hasTypes(gObject.getProp('y', true), [types.PrimBoolean]);
    })

    it('should analyze 03.js successfuly', function () {
        var data = fs.readFileSync('./testcases/03.js').toString();
        var gObject = infer.analyze(data);

        hasTypes(gObject.getProp('i', true), [types.PrimNumber]);
        hasTypes(gObject.getProp('j', true), [types.PrimNumber]);
    })

    it('should analyze 04.js successfuly', function () {
        var data = fs.readFileSync('./testcases/04.js').toString();
        var gObject = infer.analyze(data);

        hasTypes(gObject.getProp('i', true), [types.PrimNumber]);
        hasTypes(gObject.getProp('j', true), [types.PrimNumber]);
        hasTypes(gObject.getProp('pairs', true), [types.PrimString]);
    })

    it('should analyze 05.js successfuly', function () {
        var data = fs.readFileSync('./testcases/05.js').toString();
        var gObject = infer.analyze(data);

        hasTypes(gObject.getProp('isEven', true), [types.PrimBoolean]);
    })

    it('should analyze 06.js successfuly', function () {
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
    })

    it('should analyze 07.js successfuly', function () {
        var data = fs.readFileSync('./testcases/07.js').toString();
        var gObject = infer.analyze(data);

        hasTypes(gObject.getProp('x1', true),
                 [types.PrimNumber, types.PrimBoolean]);
        hasTypes(gObject.getProp('x2', true),
                 [types.PrimNumber, types.PrimString]);
        hasTypes(gObject.getProp('x3', true), [types.PrimBoolean]);
    })

    it('should analyze 08.js successfuly', function () {
        var data = fs.readFileSync('./testcases/08.js').toString();
        var gObject = infer.analyze(data);

        hasTypes(gObject.getProp('one', true), [types.PrimNumber]);
        hasTypes(gObject.getProp('ab', true), [types.PrimString]);
    })

    it('should analyze 09.js successfuly', function () {
        var data = fs.readFileSync('./testcases/09.js').toString();
        var gObject = infer.analyze(data);

        var aval_foo = gObject.getProp('foo', true);
        expect(aval_foo).to.have.property('types').with.length(1);
        hasTypes(aval_foo.types[0].getProp('data', true), [types.PrimString]);
        hasTypes(gObject.getProp('y', true), [types.PrimString]);
    })

    it('should analyze 10.js successfuly', function () {
        var data = fs.readFileSync('./testcases/10.js').toString();
        var gObject = infer.analyze(data);

        hasTypes(gObject.getProp('v', true), [types.PrimNumber]);

        var aval_obj = gObject.getProp('obj', true);
        expect(aval_obj).to.have.property('types').with.length(1);
        var obj_type = aval_obj.types[0];
        var aval_obj_x = obj_type.getProp('x', true),
            aval_obj_z = obj_type.getProp('z', true),
            aval_obj_1 = obj_type.getProp('1', true);
        hasTypes(aval_obj_x, [types.PrimNumber]);
        hasTypes(aval_obj_z, [types.PrimString]);
        hasTypes(aval_obj_1, [types.PrimNumber]);

        var aval_arr = gObject.getProp('arr', true);
        expect(aval_arr).to.have.property('types').with.length(1);
        var arr_type = aval_arr.types[0];
        hasTypes(arr_type.getProp('3', true), [types.PrimString]);

        hasTypes(gObject.getProp('n', true), [types.PrimNumber]);
        hasTypes(gObject.getProp('b', true), [types.PrimBoolean]);
        hasTypes(gObject.getProp('s', true), [types.PrimString]);
        hasTypes(gObject.getProp('l', true), [types.PrimNumber]);
    })

    it('should analyze 11.js successfuly', function () {
        var data = fs.readFileSync('./testcases/11.js').toString();
        var gObject = infer.analyze(data);

        hasTypes(gObject.getProp('a', true), [types.PrimNumber]);
        hasTypes(gObject.getProp('b', true), [types.PrimString]);
    })
})
