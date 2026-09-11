import { chromium } from 'playwright';
import http from 'http';
import fs from 'fs';
import path from 'path';

const PORT = 8089;
const server = http.createServer((req, res) => {
  const file = req.url === '/' ? '/index.html' : req.url;
  const filePath = path.resolve('.' + file);

  if (fs.existsSync(filePath)) {
    const ext = path.extname(filePath);
    const contentType = ext === '.mjs' || ext === '.js'
      ? 'application/javascript'
      : 'text/html';
    res.writeHead(200, { 'Content-Type': contentType });
    res.end(fs.readFileSync(filePath));
  } else {
    res.writeHead(404);
    res.end();
  }
}).listen(PORT);

const indexHtml = `<!DOCTYPE html>
<html>
<head><meta charset="utf-8"></head>
<body>
  <script type="module" src="/bench_recursive.mjs"></script>
</body>
</html>`;
fs.writeFileSync('./index.html', indexHtml);

try {
  const browser = await chromium.launch({
    executablePath: process.env.CHROME_BIN,
    headless: true,
    args: ['--js-flags=--expose-gc', '--no-sandbox']
  });

  const page = await browser.newPage();

  // Forward console messages directly to the terminal
  page.on('console', msg => console.log(msg.text()));
  page.on('pageerror', err => console.error(err));

  await page.goto(`http://localhost:${PORT}/index.html`);

  // Wait until Mitata prints results and finishes execution
  await page.waitForTimeout(25000);

  await browser.close();
} finally {
  server.close();
  if (fs.existsSync('./index.html')) fs.unlinkSync('./index.html');
}
