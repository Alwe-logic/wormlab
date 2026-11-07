// claude.ai の公開ページ（Artifact）に載せる版を dist/ から作る。
//
//   npm run build && node scripts/artifact.mjs [出力先]     （出力先の既定は dist-artifact/）
//
// claude.ai のページは <html><head><body> の骨組みを向こうが付けるので、こちらは中身だけを渡す。
// そのために次のように書き換える。
//   - <title> と本文（<body> の中身）と <script> だけを残す
//   - CSS は <style> に埋め込む
//   - "/_astro/…" という絶対パスを相対パス "assets/…" に直す（ページの置き場所に依らず読めるように。
//     claude.ai は "_" で始まる名前を自分用に取っておくので、フォルダの名前も変える）
//
// 【メモ】Node.js の標準ライブラリだけで書いているので、npm install は要らない。

import { copyFileSync, mkdirSync, readdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const DIST = 'dist';
const OUT = process.argv[2] ?? 'dist-artifact';

const html = readFileSync(join(DIST, 'index.html'), 'utf8');

const title = html.match(/<title>([\s\S]*?)<\/title>/)?.[1] ?? 'wormlab';

// <head> の CSS を集めて埋め込む
const css = [...html.matchAll(/<link rel="stylesheet" href="\/_astro\/([^"]+)">/g)]
  .map((m) => readFileSync(join(DIST, '_astro', m[1]), 'utf8'))
  .join('\n');

// <body> の中身。Astro は最後の <script> を </html> の後ろに出すことがあるので、それも拾う
const body = html.match(/<body>([\s\S]*)<\/body>/)?.[1] ?? '';
const trailing = html.split('</html>')[1] ?? '';

const fixPaths = (s) => s.replaceAll('"/_astro/', '"assets/');

const page = [
  `<title>${title}</title>`,
  // 左右の余白を safe area に合わせて広げている（global.css の .wrap）ことを claude.ai に伝える
  '<meta name="claude:viewport-fit-sides" content="cover">',
  `<style>\n${css}\n</style>`,
  fixPaths(body).trim(),
  fixPaths(trailing).trim(),
].join('\n');

rmSync(OUT, { recursive: true, force: true });
mkdirSync(join(OUT, 'assets'), { recursive: true });
writeFileSync(join(OUT, 'index.html'), page + '\n');

// JavaScript の中の "/_astro/…"（WebAssembly の場所）は、同じフォルダからの相対パスにする
for (const name of readdirSync(join(DIST, '_astro'))) {
  const src = join(DIST, '_astro', name);
  const dst = join(OUT, 'assets', name);
  if (name.endsWith('.js')) {
    writeFileSync(dst, readFileSync(src, 'utf8').replaceAll('"/_astro/', '"./'));
  } else if (!name.endsWith('.css')) {
    copyFileSync(src, dst);
  }
}

const left = readFileSync(join(OUT, 'index.html'), 'utf8').match(/"\/_astro\//g);
if (left) throw new Error(`絶対パスが残っています（${left.length} 個）`);
console.log(`${OUT}/ に書き出しました`);
