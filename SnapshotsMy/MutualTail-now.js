const test5 = (x, y) => _mut$test3(2, x, y);
const test4 = (x, y, z) => _mut$test3(1, x, y, z);
const test3 = (x, y) => _mut$test3(0, x, y);

function _mut$test3(_f, _a0, _a1, _a2) {
  while (true) {
    if (_f === 0) {
      if (_a0 === 0) {
        return _a1;
      }
      _f = 1;
      _a0 = _a0 > 1 ? _a0 - 1 : 0;
      _a1 = _a1 + 1;
      _a2 = 2;
      continue;
    }
    if (_f === 1) {
      if (_a0 === 0) {
        return _a1;
      }
      _f = 2;
      _a0 = _a0 > 1 ? _a0 - 1 : 0;
      _a1 = _a1 + _a2;
      continue;
    }
    if (_a0 === 0) {
      return _a1;
    }
    _f = 0;
    _a0 = _a0 > 1 ? _a0 - 1 : 0;
    _a1 = _a1 + 3;
  }
}

const test2 = x => _mut$test1(1, x);
const test1 = x => _mut$test1(0, x);

function _mut$test1(_f, _a0) {
  while (true) {
    if (_f === 0) {
      const x_3 = _a0 === 0;
      if (x_3) {
        return x_3;
      }
      _f = 1;
      _a0 = _a0 > 1 ? _a0 - 1 : 0;
      continue;
    }
    if (_a0 === 0) {
      return false;
    }
    _f = 0;
    _a0 = _a0 > 1 ? _a0 - 1 : 0;
  }
}

export {test1, test2, test3, test4, test5};
