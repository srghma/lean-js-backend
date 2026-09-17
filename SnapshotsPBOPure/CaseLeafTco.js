import {
  Array_append,
  Array_back_,
  Int_instDecidableEq,
} from "../runtime/lean_runtime_non_configurable.mjs";
export const test1Fuel = (v0, v1, v2) => {
  let v3 = v0, v4 = v1, v5 = v2;
  while (true) {
    if (v3 === 0) {
      return v5;
    } else {
      const v6 = v3 - 1;
      const v7 = v5.length;
      const v8 = 0 < v7;
      if (v8) {
        const v9 = v5[0];
        const v10 = Int_instDecidableEq(v9, 1);
        if (v10) {
          const v11 = Array_back_(v5);
          if (v11.tag === 0) {
            const v12 = [...v5, 1];
            return v12;
          } else {
            const v12 = v11._1;
            const v13 = Int_instDecidableEq(v12, 2);
            if (v13) {
              return v5;
            } else {
              if (v4) {
                const v14 = [];
                return v14;
              } else {
                const v14 = [];
                const v15 = [...v14, v12];
                const v16 = [...v15, 1];
                const v17 = [...v16, 3];
                const v18 = [...v17, v12];
                const v19 = [...v18, 5];
                const v20 = [...v19, 6];
                const v21 = [...v20, 7];
                const v22 = [...v21, 8];
                const v23 = [...v22, 9];
                const v24 = [...v23, 10];
                const v25 = [...v24, 1];
                const v26 = [...v25, 12];
                const v27 = [...v26, 13];
                const v28 = [...v27, 14];
                const v29 = [...v28, 15];
                const v30 = [...v29, 16];
                const v31 = [...v30, 17];
                const v32 = Array_append(v31, v5);
                v3 = v6;
                v5 = v32;
                continue;
              }
            }
          }
        } else {
          const v11 = Array_back_(v5);
          if (v11.tag === 0) {
            const v12 = [...v5, v9];
            return v12;
          } else {
            const v12 = v11._1;
            if (v4) {
              const v13 = [];
              return v13;
            } else {
              const v13 = [];
              const v14 = [...v13, v12];
              const v15 = [...v14, v9];
              const v16 = [...v15, 3];
              const v17 = [...v16, v12];
              const v18 = [...v17, 5];
              const v19 = [...v18, 6];
              const v20 = [...v19, 7];
              const v21 = [...v20, 8];
              const v22 = [...v21, 9];
              const v23 = [...v22, 10];
              const v24 = [...v23, v9];
              const v25 = [...v24, 12];
              const v26 = [...v25, 13];
              const v27 = [...v26, 14];
              const v28 = [...v27, 15];
              const v29 = [...v28, 16];
              const v30 = [...v29, 17];
              const v31 = Array_append(v30, v5);
              v3 = v6;
              v5 = v31;
              continue;
            }
          }
        }
      } else {
        const v9 = Array_back_(v5);
        if (v9.tag === 0) {
          return v5;
        } else {
          const v10 = v9._1;
          const v11 = [...v5, v10];
          return v11;
        }
      }
    }
  }
};
export const test1FuelCalled = (v0, v1) => test1Fuel(1000000, v0, v1);
