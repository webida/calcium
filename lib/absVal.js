// super class of all types
// I assume that each type is distinguishable by '===' operation.
function Type() {}
Type.prototype = Object.create(null);

var AllType = new Type;

// 1. object types
function ObjType(proto, name) {
		this.proto = proto;
		this.name = name;
		this.props = Object.create(null);
}
ObjType.prototype = Object.create(AllType);
ObjType.prototype.getProp = function (prop) {
		if (prop === '✖') {
				// ✖ is the bogus property name added for error recovery.
				return AbsNull;
		}
		if (prop in props) {
				return props[prop];
		} else {
				return AbsNull;
		}
};

// var ObjectPrototype = new ObjType(null, '');
// var ObjectType = 


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
function AbsVal() {
		this.types = [];
		// for abstract values,
		// a prop is the merged AbsVals from each types.
		this.props = Object.create(null);
		// for DEBUG
		this._id = count++;
}
AbsVal.prototype.hasType = function (type) {
		return this.types.indexOf(type) > -1;
};
AbsVal.prototype.addType = function (type) {
		if (this.types.indexOf(type) === -1) {
				this.types.push(type);
		}
};
AbsVal.getProp = function (prop) {
		if (prop === '✖') {
				// ✖ is the bogus property name added for error recovery.
				return AbsNull;
		}
		if (prop in props) {
				// Assume AbsVal has the merged AbsVal for the prop.
				return props[prop];
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
exports.PrimType = PrimType;
exports.AbsVal = AbsVal;
exports.PrimNumber = PrimNumber;
exports.PrimString = PrimString;
exports.PrimBoolean = PrimBoolean;
