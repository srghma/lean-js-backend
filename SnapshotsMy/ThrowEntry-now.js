const _c$IO$Error$unexpectedEof = { tag: "IO$Error$unexpectedEof" };
const _c$List$nil = { tag: "List$nil" };

// The failure of a Lean `IO` action, as a JavaScript exception. The wrapper is what
// tells a Lean failure from any other exception the program may see.
class _LeanIoError extends Error {
  constructor(e) { super("lean io error"); this.leanError = e; }
}

// `Option.none`, where the analysis found that an `Option` need not be an object: a
// symbol, so that no Lean value — `undefined` and `null` included — is equal to it.
const _none = Symbol("none");

const main$__closed__3 = ({ tag: "IO$Error$userError", _1: "boom 2" });

const errors = ({
  tag: "List$cons",
  _1: ({ tag: "IO$Error$userError", _1: "something went wrong" }),
  _2: ({
    tag: "List$cons",
    _1: ({ tag: "IO$Error$otherError", _1: "Bad thing", _s1_0: 7 }),
    _2: ({
      tag: "List$cons",
      _1: ({ tag: "IO$Error$noFileOrDirectory", _1: "data.txt", _2: "open failed", _s2_0: 2 }),
      _2: ({
        tag: "List$cons",
        _1: ({
          tag: "IO$Error$invalidArgument",
          _1: ({ tag: "Option$some", _1: "read" }),
          _2: "Not a number",
          _s2_0: 22
        }),
        _2: ({ tag: "List$cons", _1: _c$IO$Error$unexpectedEof, _2: _c$List$nil })
      })
    })
  })
});

function IO$Error$downCaseFirst(x) {
  const x_3 = x.length === 0 ? 65 : x.codePointAt(0);
  if (x_3 >= 65 && x_3 <= 90) {
    return x.length === 0 ? x : String.fromCodePoint(x_3 + 32 >>> 0) + x.slice(x.codePointAt(0) > 65535 ? 2 : 1);
  }
  return x.length === 0 ? x : String.fromCodePoint(x_3) + x.slice(x.codePointAt(0) > 65535 ? 2 : 1);
}

function IO$Error$otherErrorToString(x, y, z) {
  const s = IO$Error$downCaseFirst(x) + " (error code: " + String(y >>> 0);
  if (z === _none) {
    return s + ")";
  }
  return s + ", " + IO$Error$downCaseFirst(z) + ")";
}

function List$forIn_u39_$loop(x) {
  while (x.tag !== "List$nil") {
    console.log(IO$Error$toString(x._1));
    x = x._2;
  }
  return null;
}

function IO$Error$toString(x) {
  if (x.tag === "IO$Error$alreadyExists") {
    const x_7 = x._1;
    if (x_7.tag === "Option$none") {
      return IO$Error$otherErrorToString("already exists", x._s2_0, x._2);
    }
    return "already exists (error code: " + String(x._s2_0 >>> 0) + ", " + IO$Error$downCaseFirst(x._2) + ")\n  file: " + x_7._1;
  }
  if (x.tag === "IO$Error$otherError") {
    return IO$Error$downCaseFirst(x._1) + " (error code: " + String(x._s1_0 >>> 0) + ")";
  }
  if (x.tag === "IO$Error$resourceBusy") {
    return IO$Error$otherErrorToString("resource busy", x._s1_0, x._1);
  }
  if (x.tag === "IO$Error$resourceVanished") {
    return IO$Error$otherErrorToString("resource vanished", x._s1_0, x._1);
  }
  if (x.tag === "IO$Error$unsupportedOperation") {
    return IO$Error$otherErrorToString("unsupported operation", x._s1_0, x._1);
  }
  if (x.tag === "IO$Error$hardwareFault") {
    return "hardware fault (error code: " + String(x._s1_0 >>> 0) + ")";
  }
  if (x.tag === "IO$Error$unsatisfiedConstraints") {
    return "directory not empty (error code: " + String(x._s1_0 >>> 0) + ")";
  }
  if (x.tag === "IO$Error$illegalOperation") {
    return IO$Error$otherErrorToString("illegal operation", x._s1_0, x._1);
  }
  if (x.tag === "IO$Error$protocolError") {
    return IO$Error$otherErrorToString("protocol error", x._s1_0, x._1);
  }
  if (x.tag === "IO$Error$timeExpired") {
    return IO$Error$otherErrorToString("time expired", x._s1_0, x._1);
  }
  if (x.tag === "IO$Error$interrupted") {
    return "interrupted system call (error code: " + String(x._s2_0 >>> 0) + ", " + IO$Error$downCaseFirst(x._2) + ")\n  file: " + x._1;
  }
  if (x.tag === "IO$Error$noFileOrDirectory") {
    return "no such file or directory (error code: " + String(x._s2_0 >>> 0) + ")\n  file: " + x._1;
  }
  if (x.tag === "IO$Error$invalidArgument") {
    const x_74 = x._1;
    if (x_74.tag === "Option$none") {
      return IO$Error$otherErrorToString("invalid argument", x._s2_0, x._2);
    }
    return "invalid argument (error code: " + String(x._s2_0 >>> 0) + ", " + IO$Error$downCaseFirst(x._2) + ")\n  file: " + x_74._1;
  }
  if (x.tag === "IO$Error$permissionDenied") {
    const x_90 = x._1;
    const s = IO$Error$downCaseFirst(x._2) + " (error code: " + String(x._s2_0 >>> 0);
    if (x_90.tag === "Option$none") {
      return s + ")";
    }
    return s + ")\n  file: " + x_90._1;
  }
  if (x.tag === "IO$Error$resourceExhausted") {
    const x_98 = x._1;
    if (x_98.tag === "Option$none") {
      return IO$Error$otherErrorToString("resource exhausted", x._s2_0, x._2);
    }
    return "resource exhausted (error code: " + String(x._s2_0 >>> 0) + ", " + IO$Error$downCaseFirst(x._2) + ")\n  file: " + x_98._1;
  }
  if (x.tag === "IO$Error$inappropriateType") {
    const x_114 = x._1;
    if (x_114.tag === "Option$none") {
      return IO$Error$otherErrorToString("inappropriate type", x._s2_0, x._2);
    }
    return "inappropriate type (error code: " + String(x._s2_0 >>> 0) + ", " + IO$Error$downCaseFirst(x._2) + ")\n  file: " + x_114._1;
  }
  if (x.tag === "IO$Error$noSuchThing") {
    const x_130 = x._1;
    if (x_130.tag === "Option$none") {
      return IO$Error$otherErrorToString("no such thing", x._s2_0, x._2);
    }
    return "no such thing (error code: " + String(x._s2_0 >>> 0) + ", " + IO$Error$downCaseFirst(x._2) + ")\n  file: " + x_130._1;
  }
  if (x.tag === "IO$Error$unexpectedEof") {
    return "end of file";
  }
  return x._1;
}

function main() {
  List$forIn_u39_$loop(errors);
  throw new _LeanIoError(main$__closed__3);
}

try {
  main();
} catch (_e) {
  if (typeof process !== "undefined" && _e instanceof _LeanIoError) {
    process.stderr.write("uncaught exception: " + IO$Error$toString(_e.leanError) + "\n");
    process.exitCode = 1;
  } else {
    throw _e;
  }
}
