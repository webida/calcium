// for DEBUG
var count = 0;
// the abstract values for concrete values
// which are the sets of types
// We maintain 'props' for performance.
function AbsVal(type) {
    if (type) this.types = [type];
    else this.types = [];
    // OPTIONAL
    // for abstract values,
    // a prop is the merged AbsVals each types.
    this.props = Object.create(null);
    // for DEBUG
    this._id = count++;
}

/**
 * @returns {[Type]}
 */
AbsVal.prototype.getTypes = function () {
    return this.types;
};

/**
 * @returns {boolean}
 */
AbsVal.prototype.hasType = function (type) {
    return this.types.indexOf(type) > -1;
};

/**
 * @param {Type} type
 */
AbsVal.prototype.addType = function (type) {
    if (this.types.indexOf(type) === -1) {
        this.types.push(type);
    }
};

/**
 * @param {string} prop
 * @returns {AbsVal}
 */
AbsVal.prototype.getProp = function (prop) {
    if (prop === '✖') {
        // ✖ is the bogus property name added for error recovery.
        return AbsNull;
    }
    if (prop in this.props) {
        // Assume AbsVal has the merged AbsVal for the prop.
        return this.props[prop];
    } else {
        return AbsNull;
    }
};


// super class of all types
// I assume that each type is distinguishable by '===' operation.
function Type() {}
Type.prototype = Object.create(null);
var AllType = new Type;

// 1. object types
/**
 * @param {AbsVal} proto - AbsVal of prototype object
 * @param {string} name
 */
function ObjType(proto, name) {
    this.name = name;
    this.props = Object.create(null);
    // make __proto__ property
    this.joinAbsValToProp(proto, '___proto___');
}
ObjType.prototype = Object.create(AllType);

/**
 * @param {string} prop
 * @returns {AbsVal} AbsVal of the property
 */
ObjType.prototype.getProp = function (prop) {
    if (prop === '✖') {
        // ✖ is the bogus property name added during parsing error recovery.
        return AbsNull;
    }
    if (prop in this.props) {
        return this.props[prop];
    } else {
        return AbsNull;
    }
};

/**
 * @param {string} prop
 * @returns {boolean}
 */
ObjType.prototype.hasProp = function (prop) {
    return (prop in this.props);
};

/**
 * @param {Type} type
 * @param {string} prop
 */
ObjType.prototype.addTypeToProp = function (type, prop) {
    if (prop === '✖') return;
    if (!this.props[prop]) {
        this.props[prop] = new AbsVal;
    }
    if (this.props[prop].hasType(type)) return;
    this.props[prop].addType(type);
};

/**
 * @param {AbsVal} absval
 * @param {string} prop
 */
ObjType.prototype.joinAbsValToProp = function (absval, prop) {
    var self = this;
    absval.getTypes().forEach(function (type) {
        self.addTypeToProp(type, prop);
    });
};

var AllObjType = new ObjType(new AbsVal, '[AllObjType]');


// 2. primitive types
function PrimType(name) {
    this.name = name;
}
PrimType.prototype = Object.create(AllType);

// 3. function types
// the name is used for the type of the instances from the function
function FnType(name, argNames, argAbsVals) {
    // its __proto__ should be Function.prototype
    // for now it is AbsVal representing null - TODO use the correct proto
    ObjType.call(this, new AbsVal(PrimNumber), name);
    //ObjType.call(this, new AbsVal, name);
    this.thisAbsVal = new AbsVal;
    this.paramNames = argNames;
    this.paramAbsVals = argAbsVals;
    this.retAbsVal = new AbsVal;
}
FnType.prototype = Object.create(AllObjType);


// Make primitive types
var PrimNumber = new PrimType('number');
var PrimString = new PrimType('string');
var PrimBoolean = new PrimType('boolean');

// AbsNull represents all empty abstract values.
var AbsNull = new AbsVal();
// You should not add any properties to it.
AbsNull.props = null;


// export
exports.Type = Type;
exports.ObjType = ObjType;
exports.FnType = FnType;
exports.AbsVal = AbsVal;
exports.PrimNumber = PrimNumber;
exports.PrimString = PrimString;
exports.PrimBoolean = PrimBoolean;
