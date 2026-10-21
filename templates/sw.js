
const CACHE_AUDIO = "mesa-audio-v1";
const TIMEOUT_RED = 2500;          // ms que le damos a la red antes de usar el caché
const CLAVE_ESTADO = "/__estado_red";   // marca persistente de "la red no está"

const RE_AUDIO = /^\/audio\/[^/]+\/[^/.]+\.mp3$/;
const RE_MESA = /^\/mesa\/[^/]+$/;
const RE_SETLIST = /^\/setlist\/[^/]+$/;
const RE_ACORDES = /^\/acordes\/[^/]+$/;
const RE_MEZCLA = /^\/mezcla\/[^/]+$/;
const RE_RASGUEO = /^\/rasgueo\/[^/]+$/;

function esEstatico(pathname){
  return pathname === "/manifest.webmanifest" || pathname === "/icono-192.png" || pathname === "/icono-512.png";
}
function esCascaronDePagina(pathname){
  return pathname === "/" || RE_MESA.test(pathname) || RE_SETLIST.test(pathname)
    || RE_ACORDES.test(pathname) || RE_MEZCLA.test(pathname) || RE_RASGUEO.test(pathname) || esEstatico(pathname);
}

// Clave con la que se guarda una página. "/mesa/<song>" y
// "/mesa/<song>?setlist=<id>" son páginas DISTINTAS (la segunda trae los
// botones Anterior/Siguiente), así que el setlist forma parte de la clave.
// Cualquier otro parámetro ("&autoplay=1" al encadenar temas) se descarta:
// no cambia el HTML y duplicaría entradas. Tiene que dar exactamente la
// misma cadena que arma el servidor en urls_offline_cancion.
function claveDePagina(url){
  const sl = url.searchParams.get("setlist");
  return url.pathname + (sl ? "?setlist=" + encodeURIComponent(sl) : "");
}

// Sin esto, "sin conexión" no significa que el fetch falle: con wifi pero sin
// ruta hasta la PC (Tailscale caído, otra red), el pedido queda colgado hasta
// el timeout de TCP del sistema -- 30 a 90 segundos. Como la página espera esas
// respuestas para arrancar, se ve congelada en vez de abrir del caché.
// No abortamos el fetch (que siga si quiere): simplemente dejamos de esperarlo.
function conTope(promesa, ms){
  return new Promise((resolve, reject) => {
    const t = setTimeout(() => reject(new Error("timeout")), ms);
    promesa.then(
      (r) => { clearTimeout(t); resolve(r); },
      (e) => { clearTimeout(t); reject(e); }
    );
  });
}

// --- estado de la red -------------------------------------------------------
// Pagar TIMEOUT_RED una vez está bien; pagarlo en cada pedido del arranque
// (página + acordes + mezcla) son 5 segundos por canción. Así que en cuanto un
// pedido se cae, queda anotado y los siguientes van derecho al caché.
// El navegador mata al service worker por inactividad y se lleva las variables,
// así que la marca también va al caché: leerla de ahí es ~1 ms, muchísimo menos
// que un timeout.
let redCaida = false;      // espejo en memoria, para no ir al caché cada vez
let estadoLeido = false;
let ultimoAvisado = null;  // para no spamear a las páginas con el mismo estado

async function redEstaCaida(cache){
  if(estadoLeido) return redCaida;
  try{ redCaida = !!(await cache.match(CLAVE_ESTADO)); }catch(e){ redCaida = false; }
  estadoLeido = true;
  return redCaida;
}
async function anotarRedCaida(cache){
  redCaida = true; estadoLeido = true;
  try{ await cache.put(CLAVE_ESTADO, new Response("1")); }catch(e){}
  avisar("offline");
}
async function anotarRedOk(cache){
  // sin este chequeo, cada arranque normal avisaría "conexión recuperada"
  // aunque nunca se hubiera caído nada
  const veniaCaida = await redEstaCaida(cache);
  redCaida = false; estadoLeido = true;
  if(!veniaCaida) return;
  try{ await cache.delete(CLAVE_ESTADO); }catch(e){}
  avisar("online");
}

function avisar(estado){
  if(estado === ultimoAvisado) return;
  ultimoAvisado = estado;
  self.clients.matchAll({ type: "window" })
    .then((cs) => cs.forEach((c) => c.postMessage({ tipo: "mesa-red", estado })))
    .catch(() => {});
}

// Mientras la red está caída contestamos del caché al instante, pero probamos
// por atrás: si volvió, se limpia la marca Y se actualiza la copia guardada,
// así la próxima carga ya sale fresca. Sin este sondeo la app se quedaría
// pegada al caché para siempre.
async function sondear(cache, req){
  try{
    const resp = await conTope(fetch(req), TIMEOUT_RED);
    if(!resp) return;
    await anotarRedOk(cache);   // llegamos al servidor; hasta un 500 cuenta
    if(!resp.ok) return;
    await refrescarCopia(cache, req, resp);
  }catch(e){ /* sigue sin red: la marca queda como estaba */ }
}

// Actualiza la copia offline con lo que acaba de contestar el servidor. Solo
// pisa entradas que YA existen: el caché no crece solo, lo llena el botón de
// descarga. Única excepción: la variante "?setlist=<id>" de una mesa que YA
// está descargada -- si abrís desde un setlist nuevo un tema que ya bajaste,
// esa página (unos KB) se guarda para que offline conserve Anterior/Siguiente.
// Corre en CADA respuesta buena, no solo al recuperarse de un corte: si no,
// la página guardada se queda con el HTML de la versión de la app que estaba
// el día que se descargó, y offline abrís una app vieja.
async function refrescarCopia(cache, req, resp){
  if(!resp || !resp.ok) return;
  try{
    const url = new URL(req.url);
    const clave = claveDePagina(url);
    if(await cache.match(clave)){ await cache.put(clave, resp.clone()); return; }
    if(RE_MESA.test(url.pathname) && url.searchParams.get("setlist") && await cache.match(url.pathname)){
      await cache.put(clave, resp.clone());
    }
  }catch(e){}
}

self.addEventListener("install", (event) => {
  self.skipWaiting();
  event.waitUntil(
    caches.open(CACHE_AUDIO)
      .then((cache) => cache.addAll(["/manifest.webmanifest", "/icono-192.png", "/icono-512.png"]))
      .catch(() => {})
  );
});
self.addEventListener("activate", (e) => { e.waitUntil(self.clients.claim()); });

self.addEventListener("fetch", (event) => {
  const req = event.request;
  if(req.method !== "GET") return;   // POST (mute, tempo, borrar...) pasa sin tocarse
  const url = new URL(req.url);

  // El latido no se cachea nunca: su única razón de ser es fallar cuando no
  // hay red. Pasa por acá y no derecho a la red para que el resultado alimente
  // el mismo estado que usa todo lo demás -- así, cuando pasás a la canción
  // siguiente, el cortacircuito ya está decidido y la carga es instantánea.
  if(url.pathname === "/ping"){
    event.respondWith((async () => {
      const cache = await caches.open(CACHE_AUDIO);
      try{
        const resp = await conTope(fetch(req), TIMEOUT_RED);
        await anotarRedOk(cache);
        return resp;
      }catch(e){
        await anotarRedCaida(cache);
        return new Response("sin red", { status: 503 });
      }
    })());
    return;
  }

  // audio a velocidad normal (nunca el "?t=" de otras velocidades, que se
  // generan al vuelo y no se guardan offline): cache primero
  if(RE_AUDIO.test(url.pathname) && !url.search){
    event.respondWith(
      caches.open(CACHE_AUDIO).then(async (cache) => {
        const cacheado = await cache.match(req);
        return cacheado || fetch(req);
      })
    );
    return;
  }

  // portada, mesa de una canción, y los datos que esa página pide al cargar.
  // ignoreSearch porque "/mesa/<song>" puede llegar con "?setlist=..." y lo
  // que se guardó al descargar fue la versión sin parámetros.
  if(esCascaronDePagina(url.pathname)){
    event.respondWith((async () => {
      const cache = await caches.open(CACHE_AUDIO);
      // primero la variante exacta (con su setlist); si no está, cualquier
      // copia de la misma ruta sirve para no quedarse sin página
      const cacheado = (await cache.match(claveDePagina(url))) || (await cache.match(req, { ignoreSearch: true }));

      // ya sabemos que no hay red y tenemos copia: cero espera
      if(cacheado && await redEstaCaida(cache)){
        avisar("offline");
        event.waitUntil(sondear(cache, req));
        return cacheado;
      }

      try{
        // con copia guardada le damos a la red TIMEOUT_RED y listo; sin copia
        // no hay nada mejor que esperarla (primera visita, conexión lenta)
        const resp = await (cacheado ? conTope(fetch(req), TIMEOUT_RED) : fetch(req));
        await anotarRedOk(cache);
        if(cacheado) await refrescarCopia(cache, req, resp);
        return resp;
      }catch(e){
        await anotarRedCaida(cache);
        return cacheado || Response.error();
      }
    })());
  }
});
