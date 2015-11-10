var chai = require('chai');
var expect = chai.expect,
    should = chai.should();
var fs = require('fs');
var infer = require('../lib/infer');
import * as types from '../lib/domains/types'
import * as myWalker from '../lib/util/myWalker'
import * as varRef from '../lib/varrefs'

function hasTypes(obj, name, types) {
    it('types of ' + name + ' should be ' + types.map((tp) => tp._toString([])),
        () => {
            const aval = obj.getProp(name, true);
            expect(aval.types.size).to.equal(types.length);
            aval.types.forEach(function (type) {
                expect(types).to.include(type);
            });
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

describe('calcium', function () {

    describe('Analyze 01.js', () => {
        var data = fs.readFileSync('./testcases/01.js').toString();
        var gObject = infer.analyze(data);

        hasTypes(gObject, 'x', [types.PrimNumber]);
    });

    describe('Analyze 02.js', () => {
        var data = fs.readFileSync('./testcases/02.js').toString();
        var gObject = infer.analyze(data);

        hasTypes(gObject, 'x', [types.PrimNumber]);
        hasTypes(gObject, 'y', [types.PrimBoolean]);
    });

    describe('Analyze 03.js', () => {
        var data = fs.readFileSync('./testcases/03.js').toString();
        var gObject = infer.analyze(data);

        hasTypes(gObject, 'i', [types.PrimNumber]);
        hasTypes(gObject, 'j', [types.PrimNumber]);
    });

    describe('Analyze 04.js', () => {
        var data = fs.readFileSync('./testcases/04.js').toString();
        var gObject = infer.analyze(data);

        hasTypes(gObject, 'i', [types.PrimNumber]);
        hasTypes(gObject, 'j', [types.PrimNumber]);
        hasTypes(gObject, 'pairs', [types.PrimString]);
    });

     describe('Analyze 06.js', () => {
        var data = fs.readFileSync('./testcases/06.js').toString();
        var gObject = infer.analyze(data);

        hasTypes(gObject, 'x', [types.PrimNumber]);
        hasTypes(gObject, 'x1', [types.PrimNumber]);
        hasTypes(gObject, 'x2', [types.PrimNumber]);
        hasTypes(gObject, 'x3', [types.PrimNumber]);
        hasTypes(gObject, 'x4', [types.PrimBoolean]);
        hasTypes(gObject, 'x5', [types.PrimString]);
        hasTypes(gObject, 'x6', []);
        hasTypes(gObject, 'y1', [types.PrimNumber]);
        hasTypes(gObject, 'y2', [types.PrimNumber]);
        hasTypes(gObject, 'y3', [types.PrimNumber]);
        hasTypes(gObject, 'y4', [types.PrimNumber]);
        hasTypes(gObject, 'y5', [types.PrimNumber]);
        hasTypes(gObject, 'y6', [types.PrimBoolean]);
        hasTypes(gObject, 'y7', [types.PrimBoolean]);
    });

    describe('Analyze 07.js', function () {
        var data = fs.readFileSync('./testcases/07.js').toString();
        var gObject = infer.analyze(data);

        hasTypes(gObject, 'x1', [types.PrimNumber, types.PrimBoolean]);
        hasTypes(gObject, 'x2', [types.PrimNumber, types.PrimString]);
        hasTypes(gObject, 'x3', [types.PrimBoolean]);
    });

    describe('Analyze 08.js', function () {
        var data = fs.readFileSync('./testcases/08.js').toString();
        var gObject = infer.analyze(data);

        hasTypes(gObject, 'one', [types.PrimNumber]);
        hasTypes(gObject, 'ab', [types.PrimString]);
    });

    describe('Analyze 09.js', function () {
        var data = fs.readFileSync('./testcases/09.js').toString();
        var gObject = infer.analyze(data);

        describe('Object foo', () => {
            var type = getIfSingleton(gObject.getProp('foo', true).types);
            hasTypes(type, 'data', [types.PrimString]);
        });
        hasTypes(gObject, 'y', [types.PrimString]);
    });

    describe('Analyze 10.js', function () {
        var data = fs.readFileSync('./testcases/10.js').toString();
        var gObject = infer.analyze(data);

        hasTypes(gObject, 'v', [types.PrimNumber]);

        describe('Object obj', () => {
            var obj_type = getIfSingleton(gObject.getProp('obj', true).types);
            hasTypes(obj_type, 'x', [types.PrimNumber]);
            hasTypes(obj_type, 'z', [types.PrimString]);
            hasTypes(obj_type, '1', [types.PrimNumber]);
        });

        describe('Array arr', () => {
            var arr_type = getIfSingleton(gObject.getProp('arr', true).types);
            hasTypes(arr_type, '3', [types.PrimString]);
        });

        hasTypes(gObject, 'n', [types.PrimNumber]);
        hasTypes(gObject, 'b', [types.PrimBoolean]);
        hasTypes(gObject, 's', [types.PrimString]);
        hasTypes(gObject, 'l', [types.PrimNumber]);
    });

    describe('Analyze 11.js', function () {
        var data = fs.readFileSync('./testcases/11.js').toString();
        var gObject = infer.analyze(data);

        hasTypes(gObject, 'a', [types.PrimNumber]);
        hasTypes(gObject, 'b', [types.PrimString]);
    });

    describe('Analyze 12.js', function () {
        var data = fs.readFileSync('./testcases/12.js').toString();
        var gObject = infer.analyze(data);

        hasTypes(gObject, 'x1', [types.PrimBoolean]);
        hasTypes(gObject, 'x2', [types.PrimBoolean]);
        hasTypes(gObject, 'x3', [types.PrimString]);
        hasTypes(gObject, 'x4', [types.PrimString]);
        hasTypes(gObject, 'x5', [types.PrimBoolean]);
        hasTypes(gObject, 'x6', [types.PrimBoolean]);
    });

    describe('Analyze 13.js', function () {
        var data = fs.readFileSync('./testcases/13.js').toString();
        var gObject = infer.analyze(data);

        hasTypes(gObject, 'x', [types.PrimBoolean]);
        hasTypes(gObject, 'y', [types.PrimNumber]);
        hasTypes(gObject, 'z', [types.PrimNumber]);
    });

    describe('Analyze 14.js', function () {
        var data = fs.readFileSync('./testcases/14.js').toString();
        var gObject = infer.analyze(data);

        hasTypes(gObject, 'x', [types.PrimString]);
    });

    describe('Analyze 15.js', function () {
        var data = fs.readFileSync('./testcases/15.js').toString();
        var gObject = infer.analyze(data);

        hasTypes(gObject, 't1', [types.PrimNumber]);
        hasTypes(gObject, 't2', [types.PrimString]);
        hasTypes(gObject, 't3', [types.PrimBoolean]);
    });

    describe('Analyze 16.js', function () {
        var data = fs.readFileSync('./testcases/16.js').toString();
        var gObject = infer.analyze(data);

        hasTypes(gObject, 'a0', [types.PrimNumber, types.PrimBoolean]);
        hasTypes(gObject, 'a1', [types.PrimNumber]);
        hasTypes(gObject, 'a3', [types.PrimBoolean]);
    });

    describe('Analyze 17.js', function () {
        var data = fs.readFileSync('./testcases/17.js').toString();
        var gObject = infer.analyze(data);

        hasTypes(gObject, 'x', []);
        hasTypes(gObject, 'y', [types.PrimString]);
    });

    describe('Analyze 18.js', function () {
        var data = fs.readFileSync('./testcases/18.js').toString();
        var gObject = infer.analyze(data);

        hasTypes(gObject, 'x', [types.PrimNumber]);
        hasTypes(gObject, 'y', []);
    });

    describe('Analyze 19.js', function () {
        var data = fs.readFileSync('./testcases/19.js').toString();
        var gObject = infer.analyze(data);

        hasTypes(gObject, 'x', [types.PrimNumber]);
        hasTypes(gObject, 'y', [types.PrimBoolean]);
        hasTypes(gObject, 'z', [types.PrimString]);
    });

    describe('Analyze 20.js', function () {
        var data = fs.readFileSync('./testcases/20.js').toString();
        var options = require('../testcases/options/oneSensitiveOption').options;
        var gObject = infer.analyze(data, false, options);

        hasTypes(gObject, 'x', [types.PrimNumber]);
        hasTypes(gObject, 'y', [types.PrimBoolean]);
        hasTypes(gObject, 'a', [types.PrimNumber]);
        hasTypes(gObject, 'b', [types.PrimBoolean]);
    });

    describe('Analyze 21.js', function () {
        var data = fs.readFileSync('./testcases/21.js').toString();
        var options = require('../testcases/options/nameBasedSensitiveOption').options;
        var gObject = infer.analyze(data, false, options);

        hasTypes(gObject, 'x', [types.PrimNumber]);
        hasTypes(gObject, 'y', [types.PrimBoolean]);
        hasTypes(gObject, 'a', [types.PrimNumber, types.PrimBoolean]);
        hasTypes(gObject, 'b', [types.PrimNumber, types.PrimBoolean]);
    });

    describe('Analyze 22.js', function () {
        var data = fs.readFileSync('./testcases/22.js').toString();
        var result = infer.analyze(data, true);

        var getTypeAtRange = require('../lib/getTypeData').getTypeAtRange;

        it('type of arr should be [?]', () => {
            var typeOfArr = getTypeAtRange(result.AST, result.Ĉ, 5, 5).typeString;
            expect(typeOfArr).to.equal('[?]');
        });
        it('type of id should be fn(x:number|boolean) -> number|boolean', () => {
            var typeOfFn = getTypeAtRange(result.AST, result.Ĉ, 88, 88).typeString;
            expect(typeOfFn).to.equal('fn(x:number|boolean) -> number|boolean');
        });
    });

    describe('Analyzing 23.js: checking defaults in patterns', function () {
        const data = fs.readFileSync('./testcases/23.js').toString();
        const ast = infer.analyze(data, true).AST;
        const params = ast.body[0].params;
        it('x', () => {
            expect(myWalker.patternHasDefaults(params[0])).to.equal(false);
        });
        it('y = 1', () => {
            expect(myWalker.patternHasDefaults(params[1])).to.equal(true);
        });
        it('{a, b}', () => {
            expect(myWalker.patternHasDefaults(params[2])).to.equal(false);
        });
        it('[c, {d, [e, f = 1]}]', () => {
            expect(myWalker.patternHasDefaults(params[3])).to.equal(true);
        });
        it('[u, {v: v, w: w = 1}]', () => {
            expect(myWalker.patternHasDefaults(params[4])).to.equal(true);
        });
        it('...rest = []', () => {
            expect(myWalker.patternHasDefaults(params[5])).to.equal(true);
        });
    });
    describe('Analyzing 24.js: Checking variable occurrences', () => {
        const data = fs.readFileSync('./testcases/24.js').toString();
        const ast = infer.analyze(data, true).AST;

        function cmpOccur(pos, target) {
            // slice is needed to remove irrelevant property
            const refs = varRef.findVarRefsAt(ast, pos).slice();
            expect(refs).to.deep.equal(target);

        }

        it('At f1\'s parameter a', () => {
           cmpOccur(23, [{start: 23, end: 24}, {start: 39, end: 40}]);
        });
        it('At f2\'s first parameter a', () => {
            cmpOccur(60, [{start: 60, end: 61}, {start: 67, end: 68}]);
        });
        it('At f2\'s first parameter a', () => {
            cmpOccur(63, [{start: 63, end: 64}, {start: 87, end: 88}]);
        });
        it('At b in f3\'s default value', () => {
            cmpOccur(115, [{start: 7, end: 8}, {start: 115, end: 116}]);
        });
        it('At f4\'s parameter a', () => {
            cmpOccur(136, [{start: 136, end: 137}, {start: 151, end: 152}]);
        });
        it('At f4\'s parameter b', () => {
            cmpOccur(143, [{start: 143, end: 144}, {start: 158, end: 159}]);
        });
        it('At f5\'s arguments', () => {
            cmpOccur(182, [{start: 182, end: 191}, {start: 199, end: 208}]);
        });
        it('At f7\'s default, arguments', () => {
            cmpOccur(258, [{start: 258, end: 267}, {start: 279, end: 288}]);
        });
    });

    describe('Analyzing 25.js: Checking destructuring', () => {
        var data = fs.readFileSync('./testcases/25.js').toString();
        var options = require('../testcases/options/nameBasedSensitiveOption').options;
        var gObject = infer.analyze(data, false, options);

        hasTypes(gObject, 'e0', [types.PrimNumber]);
        hasTypes(gObject, 'e1', [types.PrimString]);
        hasTypes(gObject, 'f1', [types.PrimNumber]);
        hasTypes(gObject, 'v2', [types.PrimString]);
        hasTypes(gObject, 'x1', [types.PrimNumber]);
        hasTypes(gObject, 'x2', [types.PrimNumber, types.PrimString]);
        hasTypes(gObject, 'x3', [types.PrimNumber]);
        hasTypes(gObject, 'x4', [types.PrimString]);
        hasTypes(gObject, 'x5', [types.PrimNumber, types.PrimBoolean]);
        hasTypes(gObject, 'x6', [types.PrimString]);
        hasTypes(gObject, 'x7', [types.PrimBoolean]);
        hasTypes(gObject, 'x8', [types.PrimString]);
        hasTypes(gObject, 'x9', [types.PrimNumber]);
        hasTypes(gObject, 'x10', [types.PrimString]);
        hasTypes(gObject, 'x11', [types.PrimBoolean]);
    });
});
