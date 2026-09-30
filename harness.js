// Headless harness: stubs just enough DOM to run go.html's engine, then tests
// the rules. Run: node test.js
const fs = require("fs");
const vm = require("vm");

/* ---- minimal DOM stubs ---- */
const noop = () => {};
function El(id) {
  const kids = [];
  return {
    id, innerHTML: "", textContent: "", value: "", hidden: false,
    style: {}, dataset: {}, scrollTop: 0, scrollHeight: 0,
    clientWidth: 800, clientHeight: 600, width: 800, height: 600,
    classList: { add: noop, remove: noop, toggle: noop, contains: () => false },
    appendChild(c) { kids.push(c); return c; },
    get childElementCount() { return kids.length; },
    get children() { return kids; },
    addEventListener: noop, click: noop, focus: noop,
    getBoundingClientRect: () => ({ left: 0, top: 0, width: 800, height: 600 }),
    getContext: () => ctx2d,
  };
}
const elCache = new Map();
const gradient = { addColorStop: noop };
const ctx2d = new Proxy({}, {
  get(_, p) {
    if (p === "createLinearGradient" || p === "createRadialGradient") return () => gradient;
    if (p === "measureText") return () => ({ width: 20 });
    if (p === "setTransform" || p === "save" || p === "restore") return noop;
    return typeof p === "string" ? noop : undefined;
  },
  set: () => true,
});
const document = {
  getElementById: id => (elCache.has(id) ? elCache.get(id) : (elCache.set(id, El(id)), elCache.get(id))),
  createElement: () => El("tmp"),
  addEventListener: noop,
};
const sandbox = {
  document,
  window: { addEventListener: noop, innerWidth: 1200, innerHeight: 900, devicePixelRatio: 1 },
  // Real time: botTick() loops until performance.now() passes its budget,
  // and a constant clock would spin there forever.
  performance: { now: () => Date.now() },
  console, confirm: () => true, setTimeout,
  Blob: function () {}, URL: { createObjectURL: () => "", revokeObjectURL: noop },
  Math, Date, JSON, Set, Map, Array, Object, Number, String, parseFloat, parseInt, isNaN,
};
sandbox.globalThis = sandbox;
vm.createContext(sandbox);

const html = fs.readFileSync("go.html", "utf8");
const script = html.match(/<script>([\s\S]*?)<\/script>/)[1];
const exportHook = `
;globalThis.__T = {
  illegal, group, placeOn, idx, key, xy,
  get N(){return N}, get board(){return board}, get koPoint(){return koPoint},
  get seen(){return seen}, get moveNo(){return moveNo}, get phase(){return phase},
  get toPlay(){return toPlay}, get dead(){return dead}, get history(){return history},
  get passStreak(){return passStreak}, get hcpStones(){return hcpStones}, get komi(){return komi},
  setBoard(n, stones, opts={}) {
    N = n;
    board = new Array(n*n).fill(0);
    for (const [x,y,c] of stones) board[idx(x,y)] = c;
    toPlay = opts.toPlay || 1;
    koPoint = opts.ko === undefined ? -1 : opts.ko;
    posKey = key(board);
    initState = {board:board.slice(), toPlay, caps:{...caps}, koPoint:-1, passStreak:0,
                 posKey, moveNo:0, phase:"play", outcome:null};
    seen = new Set(opts.seen || [posKey]);
    history = []; passStreak = 0; moveNo = 0; phase = "play"; dead = new Set();
    hcpStones = [];
  },
  doPlay: play, doPass: pass, undo, countScore, toggleDead, setDead: s => { dead = s; },
  scoreGame, newGame, sgfText, get doc(){return document},
  bot, runPlayout, botScratch, scoreOn, playFast, policyMove, prepareBot, playBotMove, playout, policyMove, moveScore, areaDiff, isBotTurn,
  botMoveOnce(plays){
    prepareBot();
    while(bot.plays<plays) runPlayout();
    const mv=playBotMove();
    if(bot.tree) bot.treeBoard=board.slice();
    return mv;
  },
  searchSync(n){
    botScratch(N);
    bot.tree=newNode(); bot.treeBoard=board.slice(); bot.rootBoard=bot.treeBoard;
    bot.ko=koPoint; bot.colour=toPlay; bot.plays=0; bot.seed=123456789;
    const t0=Date.now();
    while(bot.plays<n) runPlayout();
    let best=null,bv=-1;
    for(const ch of bot.tree.children.values()) if(ch.visits>bv){bv=ch.visits;best=ch;}
    return {plays:bot.plays, ms:Date.now()-t0, branches:bot.tree.children.size,
            bestMove:best?best.move:-2, bestVisits:best?best.visits:0,
            bestRate:best?best.wins/best.visits:0, played:bot.plays};
  },
  setBot(s,l){ bot.side=s; bot.level=l; },
  playedIndexes: () => history.map((_,k)=>playedIndex(k)),
  lastMoveName: () => (viewLastMove()<0 ? '—' : dispName(viewLastMove())), get el(){return sandbox.document.getElementById}, setHcp: a => { hcpStones = a; }, setN: n => { N = n; }, setKomi: k => { komi = k; }, setPhase: p => { phase = p; },
};
`;
vm.runInContext(script + exportHook, sandbox, { filename: "go-engine.js" });
const T = sandbox.__T;
module.exports = { T, sandbox };

const B = 1, W = 2, E = 0;
let pass = 0, fail = 0;
function ok(name, cond, extra = "") {
  if (cond) { pass++; console.log("  ok   " + name); }
  else { fail++; console.log("  FAIL " + name + (extra ? "  → " + extra : "")); }
}

