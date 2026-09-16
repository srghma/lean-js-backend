const test1FuelCalled = (v0, v1) => {
  const v2 = 1000000;
  return test1Fuel(v2, v0, v1);
};
const test1Fuel = (v0, v1, v2) => {
  let v3 = v0, v4 = v1, v5 = v2, c$3 = true, r$3;
  while (c$3) {
    if (v3 === 0) {
      c$3 = false;
      r$3 = v5;
      continue;
    } else {
      const v6 = Math.max(0, v3 - 1);
      const v7 = 0;
      const v8 = v5.length;
      const v9 = v7 < v8;
      if (v9) {
        const v10 = v5[v7];
        const v11 = 1;
        const v12 = v11;
        const v13 = Int_instDecidableEq(v10, v12);
        if (v13) {
          const v14 = Array_back_(v5);
          if (v14.tag === 0) {
            const v15 = [...v5, v12];
            c$3 = false;
            r$3 = v15;
            continue;
          } else {
            const v15 = v14._1;
            const v16 = 2;
            const v17 = v16;
            const v18 = Int_instDecidableEq(v15, v17);
            if (v18) {
              c$3 = false;
              r$3 = v5;
              continue;
            } else {
              const v19 = v12;
              const v20 = v15;
              if (v4) {
                const v21 = 0;
                const v22 = Array_mkEmpty(v21);
                c$3 = false;
                r$3 = v22;
                continue;
              } else {
                const v21 = 3;
                const v22 = v21;
                const v23 = 5;
                const v24 = v23;
                const v25 = 6;
                const v26 = v25;
                const v27 = 7;
                const v28 = v27;
                const v29 = 8;
                const v30 = v29;
                const v31 = 9;
                const v32 = v31;
                const v33 = 10;
                const v34 = v33;
                const v35 = 12;
                const v36 = v35;
                const v37 = 13;
                const v38 = v37;
                const v39 = 14;
                const v40 = v39;
                const v41 = 15;
                const v42 = v41;
                const v43 = 16;
                const v44 = v43;
                const v45 = 17;
                const v46 = v45;
                const v47 = Array_mkEmpty(v45);
                const v48 = [...v47, v20];
                const v49 = [...v48, v19];
                const v50 = [...v49, v22];
                const v51 = [...v50, v20];
                const v52 = [...v51, v24];
                const v53 = [...v52, v26];
                const v54 = [...v53, v28];
                const v55 = [...v54, v30];
                const v56 = [...v55, v32];
                const v57 = [...v56, v34];
                const v58 = [...v57, v19];
                const v59 = [...v58, v36];
                const v60 = [...v59, v38];
                const v61 = [...v60, v40];
                const v62 = [...v61, v42];
                const v63 = [...v62, v44];
                const v64 = [...v63, v46];
                const v65 = Array_append(v64, v5);
                const t$3$0 = v6;
                const t$3$1 = v4;
                const t$3$2 = v65;
                v3 = t$3$0;
                v4 = t$3$1;
                v5 = t$3$2;
                continue;
              }
            }
          }
        } else {
          const v14 = Array_back_(v5);
          if (v14.tag === 0) {
            const v15 = [...v5, v10];
            c$3 = false;
            r$3 = v15;
            continue;
          } else {
            const v15 = v14._1;
            const v16 = v10;
            const v17 = v15;
            if (v4) {
              const v18 = 0;
              const v19 = Array_mkEmpty(v18);
              c$3 = false;
              r$3 = v19;
              continue;
            } else {
              const v18 = 3;
              const v19 = v18;
              const v20 = 5;
              const v21 = v20;
              const v22 = 6;
              const v23 = v22;
              const v24 = 7;
              const v25 = v24;
              const v26 = 8;
              const v27 = v26;
              const v28 = 9;
              const v29 = v28;
              const v30 = 10;
              const v31 = v30;
              const v32 = 12;
              const v33 = v32;
              const v34 = 13;
              const v35 = v34;
              const v36 = 14;
              const v37 = v36;
              const v38 = 15;
              const v39 = v38;
              const v40 = 16;
              const v41 = v40;
              const v42 = 17;
              const v43 = v42;
              const v44 = Array_mkEmpty(v42);
              const v45 = [...v44, v17];
              const v46 = [...v45, v16];
              const v47 = [...v46, v19];
              const v48 = [...v47, v17];
              const v49 = [...v48, v21];
              const v50 = [...v49, v23];
              const v51 = [...v50, v25];
              const v52 = [...v51, v27];
              const v53 = [...v52, v29];
              const v54 = [...v53, v31];
              const v55 = [...v54, v16];
              const v56 = [...v55, v33];
              const v57 = [...v56, v35];
              const v58 = [...v57, v37];
              const v59 = [...v58, v39];
              const v60 = [...v59, v41];
              const v61 = [...v60, v43];
              const v62 = Array_append(v61, v5);
              const t$3$0 = v6;
              const t$3$1 = v4;
              const t$3$2 = v62;
              v3 = t$3$0;
              v4 = t$3$1;
              v5 = t$3$2;
              continue;
            }
          }
        }
      } else {
        const v10 = Array_back_(v5);
        if (v10.tag === 0) {
          c$3 = false;
          r$3 = v5;
          continue;
        } else {
          const v11 = v10._1;
          const v12 = [...v5, v11];
          c$3 = false;
          r$3 = v12;
          continue;
        }
      }
    }
  }
  return r$3;
};
export { test1FuelCalled, test1Fuel };
