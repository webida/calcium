// Status:
// { self  : AVal, 
//   ret   : AVal, 
//   exc   : AVal, 
//   delta : Context,
//   sc    : ScopeChain }

function Status(self, ret, exc, delta, sc) {
    this.self = self;
    this.ret = ret;
    this.exc = exc;
    this.delta = delta;
    this.sc = sc;
}

Status.prototype.equals = function (other) {
    if (this.self === other.self
     && this.ret === other.ret
     && this.exc === other.exc
     && this.delta.equals(other.delta)
     && this.sc === other.sc) {
         return true;
     } else {
         return false;
     }
};

exports.Status = Status;