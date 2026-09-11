export const V1 = {
  add: (a, b) => ({ tag: "add", _1: a, _2: b }),
  mul: (a, b) => ({ tag: "mul", _1: a, _2: b }),
  succ: a => ({ tag: "succ", _1: a }),
  zero: { tag: "zero" },
  render: function r(v) {
    if (v.tag === "add") return "Add(" + r(v._1) + " " + r(v._2) + ")";
    if (v.tag === "mul") return "Mul(" + r(v._1) + " " + r(v._2) + ")";
    if (v.tag === "succ") return "Succ(" + r(v._1) + ")";
    return "Zero";
  },
  count: function c(v) {
    if (v.tag === "add") return 1 + c(v._1) + c(v._2);
    if (v.tag === "mul") return 1 + c(v._1) + c(v._2);
    if (v.tag === "succ") return 1 + c(v._1);
    return 1;
  }
};

export const V2 = {
  add: (a, b) => ({ tag: 0, _1: a, _2: b }),
  mul: (a, b) => ({ tag: 1, _1: a, _2: b }),
  succ: a => ({ tag: 2, _1: a, _2: null }),
  zero: { tag: 3, _1: null, _2: null },
  render: function r(v) {
    switch (v.tag) {
      case 0: return "Add(" + r(v._1) + " " + r(v._2) + ")";
      case 1: return "Mul(" + r(v._1) + " " + r(v._2) + ")";
      case 2: return "Succ(" + r(v._1) + ")";
      default: return "Zero";
    }
  },
  count: function c(v) {
    switch (v.tag) {
      case 0: return 1 + c(v._1) + c(v._2);
      case 1: return 1 + c(v._1) + c(v._2);
      case 2: return 1 + c(v._1);
      default: return 1;
    }
  }
};

export const V2_without_empty_fields = {
  add: (a, b) => ({ tag: 0, _1: a, _2: b }),
  mul: (a, b) => ({ tag: 1, _1: a, _2: b }),
  succ: a => ({ tag: 2, _1: a }),
  zero: { tag: 3 },
  render: function r(v) {
    switch (v.tag) {
      case 0: return "Add(" + r(v._1) + " " + r(v._2) + ")";
      case 1: return "Mul(" + r(v._1) + " " + r(v._2) + ")";
      case 2: return "Succ(" + r(v._1) + ")";
      default: return "Zero";
    }
  },
  count: function c(v) {
    switch (v.tag) {
      case 0: return 1 + c(v._1) + c(v._2);
      case 1: return 1 + c(v._1) + c(v._2);
      case 2: return 1 + c(v._1);
      default: return 1;
    }
  }
};

export const V3 = {
  add: (a, b) => ["add", a, b],
  mul: (a, b) => ["mul", a, b],
  succ: a => ["succ", a],
  zero: ["zero"],
  render: function r(v) {
    const t = v[0];
    if (t === "add") return "Add(" + r(v[1]) + " " + r(v[2]) + ")";
    if (t === "mul") return "Mul(" + r(v[1]) + " " + r(v[2]) + ")";
    if (t === "succ") return "Succ(" + r(v[1]) + ")";
    return "Zero";
  },
  count: function c(v) {
    const t = v[0];
    if (t === "add") return 1 + c(v[1]) + c(v[2]);
    if (t === "mul") return 1 + c(v[1]) + c(v[2]);
    if (t === "succ") return 1 + c(v[1]);
    return 1;
  }
};

export const V4 = {
  add: (a, b) => [0, a, b],
  mul: (a, b) => [1, a, b],
  succ: a => [2, a],
  zero: 3,
  render: function r(v) {
    if (typeof v === "number") return "Zero";
    switch (v[0]) {
      case 0: return "Add(" + r(v[1]) + " " + r(v[2]) + ")";
      case 1: return "Mul(" + r(v[1]) + " " + r(v[2]) + ")";
      default: return "Succ(" + r(v[1]) + ")";
    }
  },
  count: function c(v) {
    if (typeof v === "number") return 1;
    switch (v[0]) {
      case 0: return 1 + c(v[1]) + c(v[2]);
      case 1: return 1 + c(v[1]) + c(v[2]);
      default: return 1 + c(v[1]);
    }
  }
};

const MAX_NODES = 2_000_000;
const arena_tags = new Uint8Array(MAX_NODES);
const arena_1 = new Int32Array(MAX_NODES);
const arena_2 = new Int32Array(MAX_NODES);
let arena_ptr = 0;

export const V5 = {
  reset: () => { arena_ptr = 0; },
  add: (a, b) => {
    const id = ++arena_ptr;
    arena_tags[id] = 0; arena_1[id] = a; arena_2[id] = b;
    return id;
  },
  mul: (a, b) => {
    const id = ++arena_ptr;
    arena_tags[id] = 1; arena_1[id] = a; arena_2[id] = b;
    return id;
  },
  succ: a => {
    const id = ++arena_ptr;
    arena_tags[id] = 2; arena_1[id] = a;
    return id;
  },
  zero: 0,
  render: function r(id) {
    if (id === 0) return "Zero";
    switch (arena_tags[id]) {
      case 0: return "Add(" + r(arena_1[id]) + " " + r(arena_2[id]) + ")";
      case 1: return "Mul(" + r(arena_1[id]) + " " + r(arena_2[id]) + ")";
      case 2: return "Succ(" + r(arena_1[id]) + ")";
      default: return "Zero";
    }
  },
  count: function c(id) {
    if (id === 0) return 1;
    switch (arena_tags[id]) {
      case 0: return 1 + c(arena_1[id]) + c(arena_2[id]);
      case 1: return 1 + c(arena_1[id]) + c(arena_2[id]);
      case 2: return 1 + c(arena_1[id]);
      default: return 1;
    }
  }
};

class NodeClass {
  constructor(tag, a, b) {
    this.tag = tag;
    this._1 = a;
    this._2 = b;
  }
}
const zeroNode = new NodeClass(3, null, null);

export const V6 = {
  add: (a, b) => new NodeClass(0, a, b),
  mul: (a, b) => new NodeClass(1, a, b),
  succ: a => new NodeClass(2, a, null),
  zero: zeroNode,
  render: function r(v) {
    switch (v.tag) {
      case 0: return "Add(" + r(v._1) + " " + r(v._2) + ")";
      case 1: return "Mul(" + r(v._1) + " " + r(v._2) + ")";
      case 2: return "Succ(" + r(v._1) + ")";
      default: return "Zero";
    }
  },
  count: function c(v) {
    switch (v.tag) {
      case 0: return 1 + c(v._1) + c(v._2);
      case 1: return 1 + c(v._1) + c(v._2);
      case 2: return 1 + c(v._1);
      default: return 1;
    }
  }
};

// =============================================================================
// 7. PureScript (Default `purs` compiler code generation)
// =============================================================================

// Constructor definitions generated by `purs`
const PS_Add = /* #__PURE__ */ (function () {
  function Add(value0, value1) {
    this.value0 = value0;
    this.value1 = value1;
  }
  Add.create = function (value0) {
    return function (value1) {
      return new Add(value0, value1);
    };
  };
  return Add;
})();

const PS_Mul = /* #__PURE__ */ (function () {
  function Mul(value0, value1) {
    this.value0 = value0;
    this.value1 = value1;
  }
  Mul.create = function (value0) {
    return function (value1) {
      return new Mul(value0, value1);
    };
  };
  return Mul;
})();

const PS_Succ = /* #__PURE__ */ (function () {
  function Succ(value0) {
    this.value0 = value0;
  }
  Succ.create = function (value0) {
    return new Succ(value0);
  };
  return Succ;
})();

const PS_Zero = /* #__PURE__ */ (function () {
  function Zero() { }
  Zero.value = new Zero();
  return Zero;
})();

// PureScript representation export
export const V7 = {
  // Direct constructors (PureScript inlines saturated calls like `Add a b`)
  add: (a, b) => new PS_Add(a, b),
  mul: (a, b) => new PS_Mul(a, b),
  succ: a => new PS_Succ(a),
  zero: PS_Zero.value,

  // Pattern matching as emitted by PureScript (linear instanceof checks)
  render: function r(v) {
    if (v instanceof PS_Add) {
      return "Add(" + r(v.value0) + " " + r(v.value1) + ")";
    }
    if (v instanceof PS_Mul) {
      return "Mul(" + r(v.value0) + " " + r(v.value1) + ")";
    }
    if (v instanceof PS_Succ) {
      return "Succ(" + r(v.value0) + ")";
    }
    if (v instanceof PS_Zero) {
      return "Zero";
    }
    throw new Error("Failed pattern match");
  },

  count: function c(v) {
    if (v instanceof PS_Add) {
      return 1 + c(v.value0) + c(v.value1);
    }
    if (v instanceof PS_Mul) {
      return 1 + c(v.value0) + c(v.value1);
    }
    if (v instanceof PS_Succ) {
      return 1 + c(v.value0);
    }
    if (v instanceof PS_Zero) {
      return 1;
    }
    throw new Error("Failed pattern match");
  }
};

// =============================================================================
// 8. PureScript Modernized (ES6 Class Declarations + instanceof)
// =============================================================================

class PS_AddClass {
  constructor(value0, value1) {
    this.value0 = value0;
    this.value1 = value1;
  }
  static create(value0) {
    return (value1) => new PS_AddClass(value0, value1);
  }
}

class PS_MulClass {
  constructor(value0, value1) {
    this.value0 = value0;
    this.value1 = value1;
  }
  static create(value0) {
    return (value1) => new PS_MulClass(value0, value1);
  }
}

class PS_SuccClass {
  constructor(value0) {
    this.value0 = value0;
  }
  static create(value0) {
    return new PS_SuccClass(value0);
  }
}

class PS_ZeroClass {
  static value = new PS_ZeroClass();
}

export const V8 = {
  add: (a, b) => new PS_AddClass(a, b),
  mul: (a, b) => new PS_MulClass(a, b),
  succ: a => new PS_SuccClass(a),
  zero: PS_ZeroClass.value,

  render: function r(v) {
    if (v instanceof PS_AddClass) {
      return "Add(" + r(v.value0) + " " + r(v.value1) + ")";
    }
    if (v instanceof PS_MulClass) {
      return "Mul(" + r(v.value0) + " " + r(v.value1) + ")";
    }
    if (v instanceof PS_SuccClass) {
      return "Succ(" + r(v.value0) + ")";
    }
    if (v instanceof PS_ZeroClass) {
      return "Zero";
    }
    throw new Error("Failed pattern match");
  },

  count: function c(v) {
    if (v instanceof PS_AddClass) {
      return 1 + c(v.value0) + c(v.value1);
    }
    if (v instanceof PS_MulClass) {
      return 1 + c(v.value0) + c(v.value1);
    }
    if (v instanceof PS_SuccClass) {
      return 1 + c(v.value0);
    }
    if (v instanceof PS_ZeroClass) {
      return 1;
    }
    throw new Error("Failed pattern match");
  }
};
