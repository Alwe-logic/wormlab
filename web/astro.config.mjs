import { defineConfig } from 'astro/config';

// GitHub Pages などサブディレクトリに置くときは、環境変数 BASE_PATH（例：/wormlab）で
// サイトの置き場所を指定する。手元で開くときは何も指定しなくてよい。
export default defineConfig({
  site: process.env.SITE_URL,
  base: process.env.BASE_PATH ?? '/',
});
