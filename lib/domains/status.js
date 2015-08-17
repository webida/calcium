// Status:
// { self  : AVal,
//   ret   : AVal,
//   exc   : AVal,
//   delta : Context,
//   sc    : ScopeChain }

export class Status {
    constructor(self, ret, exc, delta, sc) {
        "use strict";
        this.self = self;
        this.ret = ret;
        this.exc = exc;
        this.delta = delta;
        this.sc = sc;
    }

    equals(other) {
        return this.self === other.self &&
            this.ret === other.ret &&
            this.exc === other.exc &&
            this.delta.equals(other.delta) &&
            this.sc === other.sc;
    }
}
