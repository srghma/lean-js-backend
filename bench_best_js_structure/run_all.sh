#!/usr/bin/env bash
set -e

# Verify prerequisites
for cmd in bun node google-chrome-stable; do
  if ! command -v "$cmd" &> /dev/null; then
    echo "Error: $cmd is not found in PATH."
    exit 1
  fi
done

echo ""
echo "========================================================================================="
echo " 🚀 1. RUNNING ON BUN"
echo "========================================================================================="
bun --expose-gc bench_recursive.mjs

echo ""
echo "========================================================================================="
echo " 🚀 2. RUNNING ON NODE (V8)"
echo "========================================================================================="
/nix/store/ppybqca4ijv2x6ncwipz6ys3lzknnrbl-nodejs-slim-26.8.1/bin/node --expose-gc bench_recursive.mjs

# echo ""
# echo "========================================================================================="
# echo " 🚀 3. RUNNING ON GOOGLE CHROME STABLE (HEADLESS)"
# echo "========================================================================================="
# CHROME_BIN=/nix/store/wp7bdhas8jkw2jcv8cdx2izla1an6qc0-google-chrome-152.0.7977.75/bin/google-chrome-stable node run_chrome.mjs

echo ""
echo "✅ Done with all 3 engines!"
