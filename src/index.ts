import { serve } from "bun";
import index from "./index.html";

const server = serve({
  routes: {
    // Serve static files from public directory
    "/pkg/*": async (req) => {
      const url = new URL(req.url);
      const filePath = `./public${url.pathname}`;
      const file = Bun.file(filePath);

      if (await file.exists()) {
        return new Response(file);
      }
      return new Response("AAAAAAAAAA Not Found", { status: 404 });
    },

    // Serve index.html for all unmatched routes.
    "/*": index,
  },

  development: process.env.NODE_ENV !== "production" && {
    // Enable browser hot reloading in development
    hmr: true,

    // Echo console logs from the browser to the server
    console: true,
  },
});

console.log(`🚀 Server running at ${server.url}`);
