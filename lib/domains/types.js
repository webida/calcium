// for DEBUG
var count = 0;
// the abstract values for concrete values
// which are the sets of types
// We maintain 'props' for performance.
function AVal(type) {
    if (type) this.types = [type];
    else this.types = [];
    // OPTIONAL
    // for abstract values,
    // a prop is the merged AVals each types.
    this.props = Object.create(null);
    // for DEBUG
    this._id = count++;
}

/**
 * @returns {[Type]}
 */
AVal.prototype.getTypes = function () {
    return this.types;
};

/**
 * @returns {boolean}
 */
AVal.prototype.hasType = function (type) {
    return this.types.indexOf(type) > -1;
};

/**
 * @param {Type} type
 */
AVal.prototype.addType = function (type) {
    if (this.types.indexOf(type) === -1) {
        this.types.push(type);
    }
    // TODO: 추가된 type을 AVal의 prop에 반영 전략 필요
    // 바로 전달할 것인가?
};

function mkInternalProp(prop) {
    if (prop === '✖') 
        console.log("[Error]");
    return '*' + prop;
}
/**
 * @param {string} prop
 * @returns {AVal}
 */
AVal.prototype.getProp = function (prop) {
    if (prop === '✖') {
        // ✖ is the bogus property name added for error recovery.
        return AValNull;
    }
    var inProp = mkInternalProp(prop);
    if (inProp in this.props) {
        // Assume AVal has the merged AVal for the prop.
        return this.props[inProp];
    } else {
        return AValNull;
    }
};

// super class of all types
// I assume that each type is distinguishable by '===' operation.
function Type() {}
Type.prototype = Object.create(null);
var AllType = new Type;

// 1. object types
/**
 * @param {AVal} proto - AVal of prototype object
 * @param {string} name
 */
function ObjType(proto, name) {
    this.name = name;
    this.props = Object.create(null);
    // make __proto__ property
    this.joinAValToProp(proto, '__proto__');
}
ObjType.prototype = Object.create(AllType);
/**
 * @param {string} prop
 * @returns {AVal} AVal of the property
 */
ObjType.prototype.getProp = function (prop) {
    if (prop === '✖') {
        // ✖ is the bogus property name added during parsing error recovery.
        return AValNull;
    }
    var inProp = mkInternalProp(prop);
    if (inProp in this.props) {
        return this.props[inProp];
    } else {
        return AValNull;
    }
};
/**
 * @param {string} prop
 * @returns {boolean}
 */
ObjType.prototype.hasProp = function (prop) {
    if (prop === '✖') 
        return AValNull;
    var inProp = mkInternalProp(prop);
    return (inProp in this.props);
};
/**
 * @param {Type} type
 * @param {string} prop
 */
ObjType.prototype.addTypeToProp = function (type, prop) {
    if (prop === '✖') return;
    var inProp = mkInternalProp(prop);
    if (!this.props[inProp]) {
        this.props[inProp] = new AVal;
    }
    if (this.props[inProp].hasType(type)) return;
    this.props[inProp].addType(type);
};
/**
 * @param {AVal} aval
 * @param {string} prop
 */
ObjType.prototype.joinAValToProp = function (aval, prop) {
    var self = this;
    aval.getTypes().forEach(function (type) {
        self.addTypeToProp(type, prop);
    });
};

var AllObjType = new ObjType(new AVal, '[AllObjType]');


// 2. primitive types
function PrimType(name) {
    this.name = name;
}
PrimType.prototype = Object.create(AllType);

// 3. function types
// the name is used for the type of the instances from the function
function FnType(name, argNames, sc) {
    // its __proto__ should be Function.prototype
    // for now it is AVal representing null - TODO use the correct proto
    ObjType.call(this, new AVal(PrimNumber), name);
    //ObjType.call(this, new AVal, name);
    // this.thisAVal = new AVal;
    this.paramNames = argNames;
    // this.retAVal = new AVal;
    this.sc = sc;
    // AVals for function usage
    this.usage = Object.create(null);
}
FnType.prototype = Object.create(AllObjType);

// returns AVals for given function usage
FnType.prototype.getUsageAVals = function (delta) {
    if (this.usage[delta] === undefined) {
        var params = [];
        // for 'this'
        params.push(new AVal);
        // for regular parameters
        for (var i = 1; i < this.paramNames.length; i++) {
            params.push(new AVal);
        }
        return this.usage[delta] = {params: params, ret: new AVal, exc: new AVal};
    } else return this.usage[delta];
};

// Make primitive types
var PrimNumber = new PrimType('number');
var PrimString = new PrimType('string');
var PrimBoolean = new PrimType('boolean');

// AbsNull represents all empty abstract values.
var AValNull = new AVal();
// You should not add any properties to it.
AValNull.props = null;



// export
exports.Type = Type;
exports.ObjType = ObjType;
exports.FnType = FnType;
exports.PrimNumber = PrimNumber;
exports.PrimString = PrimString;
exports.PrimBoolean = PrimBoolean;

exports.AVal = AVal;
exports.AValNull = AValNull;