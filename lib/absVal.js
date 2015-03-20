// super class of all types
// I assume that each type is distinguishable by '===' operation.
function Type() {}
Type.prototype = Object.create(null);

var AllType = new Type;

// 1. object types
/**
 * @param {string} name
 * @param {AbsVal} proto - AbsVal of prototype object
 */
function ObjType(proto, name) {
    this.name = name;
    this.props = Object.create(null);
    // make __proto__ property
    this.joinAbsValToProp(proto, '__proto__');
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
    if (type in this.props[prop]) return;
    this.props[prop].push(type);
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

// 2. primitive types
function PrimType(name) {
    this.name = name;
}
PrimType.prototype = Object.create(AllType);

var PrimNumber = new PrimType('number');
var PrimString = new PrimType('string');
var PrimBoolean = new PrimType('boolean');

function FnType(proto, name) {
    ObjType.call(this, proto, name);
}

// for DEBUG
var count = 0;
// the abstract values for concrete values
// which are the sets of types
// We maintain 'props' for performance.
function AbsVal() {
    this.types = [];
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
AbsVal.getProp = function (prop) {
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


// AbsNull represents all empty abstract values.
var AbsNull = new AbsVal();
// You should not add any properties to it.
AbsNull.props = null;


exports.Type = Type;
exports.ObjType = ObjType;
exports.AbsVal = AbsVal;
// Not export PrimType
// exports.PrimType = PrimType;
exports.PrimNumber = PrimNumber;
exports.PrimString = PrimString;
exports.PrimBoolean = PrimBoolean;
