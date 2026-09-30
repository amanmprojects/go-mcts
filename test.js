// Rules tests for go.html — run: node test.js
"use strict";
const {T} = require("./harness.js");

const B=1, W=2, E=0;
let pass=0, fail=0;
function ok(name, cond, extra=""){
  if(cond){ pass++; console.log("  ok   "+name); }
  else    { fail++; console.log("  FAIL "+name+(extra?"  → "+extra:"")); }
}

/* ---- 1. captures ---- */
console.log("\ncaptures");
{
  // W(1,1) is walled in by black; black fills its last liberty at (1,0).
  T.setBoard(9, [[0,1,B],[2,1,B],[1,2,B],[1,1,W]]);
  T.doPlay(T.idx(1,0));
  ok("single stone captured", T.board[T.idx(1,1)]===E);
  ok("capturing stone stands",  T.board[T.idx(1,0)]===B);
}
{
  // Chain of three, one shared liberty.
  T.setBoard(9, [[0,2,B],[2,1,B],[1,2,B],[0,0,W],[0,1,W],[1,1,W]]);
  T.doPlay(T.idx(1,0));
  ok("chain of 3 captured",
     T.board[T.idx(0,0)]===E && T.board[T.idx(0,1)]===E && T.board[T.idx(1,1)]===E);
  ok("chain captured in one move", T.moveNo===1);
}

/* ---- 2. suicide ---- */
console.log("\nsuicide");
{
  T.setBoard(9, [[1,0,W],[0,1,W],[1,2,W]]);
  const why = T.illegal(T.board, T.idx(0,0), B, -1, new Set());
  ok("suicide rejected by rule check", why==="suicide", "reason="+why);
  T.doPlay(T.idx(0,0));
  ok("suicide move not placed", T.board[T.idx(0,0)]===E && T.moveNo===0);
}
{
  // Same corner, but the move captures first — legal, and both whites die.
  T.setBoard(9, [[1,0,W],[0,1,W],[1,1,B],[2,0,B],[0,2,B]]);
  T.doPlay(T.idx(0,0));
  ok("capture beats the suicide rule", T.board[T.idx(0,0)]===B);
  ok("both white stones lifted",
     T.board[T.idx(1,0)]===E && T.board[T.idx(0,1)]===E);
}

/* ---- 3. board edges ---- */
console.log("\nboard edges");
{
  // Corner stone dies when the one point it touches is filled.
  T.setBoard(9, [[0,0,W],[0,1,B],[1,1,B],[2,0,B]]);
  T.doPlay(T.idx(1,0));
  ok("corner stone captured", T.board[T.idx(0,0)]===E);
}
{
  // A stone on the edge has three neighbours, not four.
  T.setBoard(9, [[0,1,W],[0,0,W],[1,0,W],[1,1,W]]);
  const g = T.group(T.board, T.idx(0,0));
  ok("edge chain found across the corner", g.stones.length===4,
     "stones="+g.stones.length);
  ok("edge chain liberties: 4, not 6", g.liberties.size===4, "libs="+g.liberties.size);
}

/* ---- 4. ko ---- */
console.log("\nko");
{
  // Black (1,1) has one liberty, at (2,1). White plays there to capture.
  const stones = [[0,1,W],[1,0,W],[1,2,W],[1,1,B],[2,0,B],[2,2,B],[3,1,B]];
  T.setBoard(9, stones, {toPlay:W});
  T.doPlay(T.idx(2,1));
  ok("ko: capture happened", T.board[T.idx(1,1)]===E && T.board[T.idx(2,1)]===W);
  ok("ko: ko point recorded", T.koPoint===T.idx(1,1));
  ok("ko: immediate recapture refused",
     T.illegal(T.board, T.idx(1,1), B, T.koPoint, T.seen)==="ko");
  T.doPlay(T.idx(1,1));
  ok("ko: board unchanged by refused recapture", T.board[T.idx(1,1)]===E);
}
{
  // Mirrored: white (1,1) has one liberty, black takes it, white answers
  // elsewhere, and black is then free to retake the ko.
  const stones = [[0,1,B],[1,0,B],[1,2,B],[1,1,W],[2,0,W],[2,2,W],[3,1,W]];
  T.setBoard(9, stones, {toPlay:B});
  T.doPlay(T.idx(2,1));        // B captures
  ok("ko: black captured the ko", T.board[T.idx(1,1)]===E && T.koPoint===T.idx(1,1));
  T.doPlay(T.idx(6,6));        // W ko threat
  T.doPlay(T.idx(1,1));        // B takes it back
  ok("ko retaken after a threat", T.board[T.idx(1,1)]===B);
}

/* ---- 5. positional superko ---- */
console.log("\nsuperko");
{
  // Capture on a 3x3 board, remember the resulting position, then re-create it.
  T.setBoard(3, [[0,0,B],[1,0,W]]);
  T.doPlay(T.idx(2,0));
  const repeat = T.key(T.board);

  T.setBoard(3, [[0,0,B],[1,0,W]], {seen:[repeat]});
  ok("rule check: repeat refused",
     T.illegal(T.board, T.idx(2,0), B, -1, T.seen)==="superko");
  T.doPlay(T.idx(2,0));
  ok("board position not recreated", T.board[T.idx(2,0)]===E);

  T.setBoard(3, [[0,0,B],[1,0,W]], {seen:[]});
  T.doPlay(T.idx(2,0));
  ok("same move allowed when unseen", T.board[T.idx(2,0)]===B);
}

/* ---- 6. pass, undo, review ---- */
console.log("\npass and undo");
{
  T.setBoard(9, []);
  T.doPlay(T.idx(4,4));
  T.doPlay(T.idx(4,5));
  const before=T.key(T.board), n=T.moveNo;
  T.undo();
  ok("undo restores the board", T.key(T.board)!==before);
  ok("undo decrements the move number", T.moveNo===n-1);
  T.undo(); T.undo();
  ok("undo back to an empty board", T.moveNo===0 && T.key(T.board)===T.key(new Array(81).fill(0)));
  ok("undo past the start is a no-op", (T.undo(), T.moveNo===0));
}
{
  T.setBoard(9, []);
  T.doPass(); T.doPass();
  ok("two passes enter scoring", T.phase==="score");
  T.undo();
  ok("undo leaves scoring", T.phase==="play" && T.moveNo===1);
}
{
  // The regression that broke first: undoing both passes of a game with no
  // stones on the board must not run off the start of the move list.
  T.setBoard(9, []);
  T.doPass(); T.doPass();
  let threw=null;
  try { T.undo(); } catch(e){ threw=e; }
  ok("undo after two opening passes is safe", threw===null, threw && threw.message);
  // Undo takes back only the second pass; the first one is still on the record.
  ok("one pass left, still playing", T.moveNo===1 && T.phase==="play" && T.history.length===1,
     `moveNo=${T.moveNo} phase=${T.phase} hist=${T.history.length}`);
  T.undo();
  ok("second undo reaches move 0", T.moveNo===0 && T.history.length===0,
     `moveNo=${T.moveNo} hist=${T.history.length}`);
}
{
  // Undo must also drop the undone position from the superko history.
  T.setBoard(3, [[0,0,B],[1,0,W]]);
  T.doPlay(T.idx(2,0));
  T.undo();
  T.doPlay(T.idx(2,0));
  ok("undone position is playable again", T.board[T.idx(2,0)]===B);
}

/* ---- 7. area scoring (Chinese) ---- */
console.log("\narea scoring");

// Every position must satisfy: stones + territory + neutral === N*N.
function checkTotals(r, n, label){
  const sum = r.stones[0]+r.stones[1]+r.terr[0]+r.terr[1]+r.terr[2];
  ok(label+": stones+territory+neutral = "+(n*n), sum===n*n, "got "+sum);
}
{
  // 5x5. Column 2 is a black wall; columns 0-1 are its territory, columns
  // 3-4 white with column 4 theirs. 15 - 10 with no komi.
  const s=[];
  for(let y=0;y<5;y++) s.push([2,y,B],[3,y,W]);
  T.setBoard(5, s); T.setKomi(0);
  const r=T.scoreGame();
  ok("black 15 (5 stones + 10 territory)", r.black===15, "got "+r.black);
  ok("white 10 (5 stones + 5 territory)",  r.white===10, "got "+r.white);
  ok("territory split 10 / 5 / 0",
     r.terr[0]===10 && r.terr[1]===5 && r.terr[2]===0, JSON.stringify(r.terr));
  checkTotals(r,5,"split board");
}
{
  // 3x3 dame: one empty point touching both colours stays neutral.
  T.setBoard(3, [[0,0,B],[0,1,B],[0,2,B],[1,0,B],
                 [2,0,W],[2,1,W],[2,2,W],[1,2,W]]);
  T.setKomi(0);
  const r=T.scoreGame();
  ok("dame point is neutral", r.terr[2]===1, JSON.stringify(r.terr));
  ok("dame board scores 4 - 4", r.black===4 && r.white===4,
     `B=${r.black} W=${r.white}`);
  checkTotals(r,3,"dame board");
}
{
  // Take the split board and mark the black wall dead. The wall leaves the
  // board, so all 25 points end up white's: 10 stones + 15 territory.
  const s=[];
  for(let y=0;y<5;y++) s.push([2,y,B],[3,y,W]);
  T.setBoard(5, s);
  T.setPhase("score"); T.setKomi(0);
  const chain=T.group(T.board, T.idx(2,2));
  ok("black wall is one chain of 5", chain.stones.length===5, "stones="+chain.stones.length);
  T.setDead(new Set(chain.stones));
  const r=T.scoreGame();
  ok("dead wall: 0 black", r.black===0, "got "+r.black);
  ok("dead wall hands 15 points to white (25)", r.white===25, "got "+r.white);
  checkTotals(r,5,"dead-wall board");
}
{
  // Marking only part of a chain is impossible — toggleDead works on chains.
  T.setBoard(5, [[0,0,B],[0,1,B],[1,0,B]]);
  T.setPhase("score");
  T.toggleDead(T.idx(0,0));
  ok("whole chain marked dead", T.dead.size===3, "size="+T.dead.size);
  T.toggleDead(T.idx(1,0));
  ok("clicking again revives the chain", T.dead.size===0);
  T.toggleDead(T.idx(0,0));
  ok("and it can be re-marked", T.dead.size===3);
}
{
  // Seki: both groups alive, sharing two liberties, nothing dead.
  const s=[[0,0,B],[0,1,B],[0,2,B],[1,0,B],[1,1,B],
           [1,2,W],[1,3,W],[1,4,W],[0,3,W],[0,4,W]];
  T.setBoard(5, s); T.setPhase("score"); T.setKomi(0);
  const r=T.scoreGame();
  ok("seki counts for both sides", r.black===5 && r.white===5,
     `B=${r.black} W=${r.white} ${JSON.stringify(r.terr)}`);
  checkTotals(r,5,"seki board");
}
{
  // A lone wall owns every empty point around it: 5 stones + 20 territory.
  T.setBoard(5, [[2,0,B],[2,1,B],[2,2,B],[2,3,B],[2,4,B]]); T.setKomi(7.5);
  const r=T.scoreGame();
  ok("lone wall owns 20 points", r.terr[0]===20, "terr="+r.terr[0]);
  ok("komi 7.5 goes to black (32.5)", Math.abs(r.black-32.5)<1e-9 && r.winner==="Black",
     `B=${r.black} W=${r.white}`);
  checkTotals(r,5,"komi board");
}

/* ---- 7b. move list / last-move marker ---- */
console.log("\nmove list");
{
  T.setBoard(9, []);
  const points=[[2,2],[6,2],[6,6],[2,6],[4,4],[3,2],[2,3]];
  points.forEach(([x,y])=>T.doPlay(T.idx(x,y)));
  ok("one snapshot per move", T.history.length===points.length,
     `${T.history.length} vs ${points.length}`);
  const names=points.map(([x,y])=>String.fromCharCode(65+x)+(9-y));
  const listed=T.playedIndexes().map(i=>i<0?"pass":String.fromCharCode(65+(i%9))+(9-((i/9)|0)));
  ok("move list matches the moves played", JSON.stringify(listed)===JSON.stringify(names),
     JSON.stringify(listed)+" vs "+JSON.stringify(names));
  ok("last move points at the final stone",
     T.playedIndexes()[points.length-1]===T.idx(2,3),
     "got "+T.playedIndexes()[points.length-1]);
  T.doPass();
  ok("a pass is listed as a pass", T.playedIndexes()[points.length]==-1);
  ok("last move is '-' after a pass", T.lastMoveName()==="—", T.lastMoveName());
}
{
  // After undoing, the list shrinks and the last entry still matches.
  T.undo();
  const l=T.playedIndexes();
  ok("undo drops the pass from the list", l.length===7, "len="+l.length);
  ok("last move still correct after undo", l[l.length-1]===T.idx(2,3));
}

/* ---- 8. handicap setup ---- */
console.log("\nhandicap");
{
  // Drive the real setup path: set the controls, then start a game.
  const el=id=>T.doc.getElementById(id);
  el("selSize").value="19"; el("selHc").value="4"; el("inKomi").value="7.5";
  T.newGame();
  ok("4 handicap stones placed", T.hcpStones.length===4, JSON.stringify(T.hcpStones));
  ok("white to move after handicap", T.toPlay===W, "toPlay="+T.toPlay);
  const sp=new Set([[3,3],[15,3],[9,3],[3,9],[15,9],[9,9],[3,15],[15,15],[9,15]]
                     .map(([x,y])=>T.idx(x,y)));
  ok("handicap stones sit on star points",
     T.hcpStones.every(i=>sp.has(i)), JSON.stringify(T.hcpStones));
  ok("all handicap stones are black",
     T.hcpStones.every(i=>T.board[i]===B));
  ok("no move recorded for the handicap", T.moveNo===0 && T.history.length===0);
  ok("komi read from the control", T.komi===7.5);
  ok("turn indicator shows White",
     el("turn").innerHTML.includes("White"), el("turn").innerHTML);

  el("selHc").value="0"; T.newGame();
  ok("even game starts with black, empty board",
     T.toPlay===B && T.hcpStones.length===0 && T.key(T.board)===T.key(new Array(361).fill(0)));

  // 2 stones: the two lower corners, D4 and Q16.
  el("selHc").value="2"; T.newGame();
  ok("2 stones at the lower corners",
     T.hcpStones.length===2 && T.hcpStones.includes(T.idx(3,15)) && T.hcpStones.includes(T.idx(15,15)),
     JSON.stringify(T.hcpStones));

  // 5 stones: corners plus tengen.
  el("selHc").value="5"; T.newGame();
  ok("5 stones include tengen K10", T.hcpStones.includes(T.idx(9,9)),
     JSON.stringify(T.hcpStones));
  ok("5 stones are the 4 corners + centre", T.hcpStones.length===5);

  // 13x13 has nine hoshi.
  el("selSize").value="13"; el("selHc").value="9"; T.newGame();
  ok("13x13 nine handicap stones", T.hcpStones.length===9, JSON.stringify(T.hcpStones));
  ok("13x13 board really is 13 wide", T.N===13 && T.board.length===169);

  // A 9x9 has only five handicap points; asking for nine must clamp, not crash.
  el("selSize").value="9"; el("selHc").value="9";
  let threw=null;
  try { T.newGame(); } catch(e){ threw=e; }
  ok("9x9 with handicap 9 does not crash", threw===null, threw && threw.message);
  ok("9x9 clamps to 5 stones", T.hcpStones.length===5, JSON.stringify(T.hcpStones));
  ok("9x9 dropdown reflects the clamp", el("selHc").value==="5", el("selHc").value);
  ok("all 9x9 handicap stones on hoshi",
     T.hcpStones.every(i=>[[2,2],[6,2],[2,6],[6,6],[4,4]].some(([x,y])=>T.idx(x,y)===i)));

  el("selSize").value="19"; el("selHc").value="0"; T.newGame();
}

/* ---- 8b. SGF export ---- */
console.log("\nSGF");
{
  T.doc.getElementById("selSize").value="19"; T.doc.getElementById("selHc").value="0"; T.doc.getElementById("inKomi").value="7.5";
  T.newGame();
  [[3,3],[15,3],[3,15],[15,15],[9,9]].forEach(([x,y])=>T.doPlay(T.idx(x,y)));
  T.doPass();
  const sgf=T.sgfText();
  ok("size and komi in the header", sgf.startsWith("[GM[1]FF[4]") && sgf.includes("SZ[19]") && sgf.includes("KM[7.5]"),
     sgf.slice(0,80));
  ok("Chinese rules recorded", sgf.includes("RU[Chinese]"));
  const moves=sgf.slice(sgf.indexOf("DT[")+14).match(/;[BW](\[[A-T]\d+\]|\[\])/g)||[];
  ok("one SGF node per move (6)", moves.length===6, JSON.stringify(moves));
  ok("alternating colours, first is black",
     moves[0]===";B[D16]" && moves[1]===";W[Q16]" && moves[2]===";B[D4]",
     JSON.stringify(moves));
  ok("pass recorded as an empty value", moves[5]===";W[]", moves[5]);
  ok("root node closed before the moves",
     sgf.slice(sgf.indexOf("DT[")+13, sgf.indexOf("DT[")+15)==="]]", sgf.slice(0,140));
  ok("brackets balanced",
     (sgf.match(/\[/g)||[]).length===(sgf.match(/\]/g)||[]).length);
}
{
  T.doc.getElementById("selHc").value="4"; T.newGame();
  const sgf=T.sgfText();
  ok("handicap recorded in the header", sgf.includes("HA[4]"), sgf.slice(0,120));
  ok("four setup stones as AB properties",
     (sgf.match(/AB[A-T]\d+/g)||[]).length===4, JSON.stringify(sgf.match(/AB[A-T]\d+/g)));
  ok("handicap game has no moves yet", !/[;][BW]/.test(sgf.slice(sgf.indexOf("DT["))));
}

/* ---- 9. random self-play smoke test ---- */
console.log("\nself-play smoke test");
{
  let played=0, passes=0, crashed=null;
  T.setBoard(19, []); T.setKomi(7.5);
  let seed=12345;
  const rnd=()=>((seed=(seed*1103515245+12345)&0x7fffffff)/0x7fffffff);
  try{
    for(let m=0;m<500;m++){
      // pick a random legal move; if none, pass
      let done=false;
      for(let tries=0;tries<40;tries++){
        const i=Math.floor(rnd()*361);
        if(!T.illegal(T.board,i,T.toPlay,T.koPoint,T.seen)){ T.doPlay(i); played++; done=true; break; }
      }
      if(!done){ T.doPass(); passes++; }
      if(T.passStreak>=2) break;
    }
    ok("500 random moves without crashing", crashed===null, crashed&&crashed.message);
    T.doPass(); T.doPass();
    ok("two passes end the game", T.phase==="score", "phase="+T.phase);
    T.countScore();
    ok("score counted", T.phase==="over");
    const r=T.scoreGame();
    ok("an area score is never a tie", r.black!==r.white,
       `B=${r.black} W=${r.white}`);
    ok("area totals add up",
       Math.abs((r.terr[0]+r.terr[1]+r.terr[2])+r.stones[0]+r.stones[1]-361)<1e-9,
       JSON.stringify(r));
    console.log(`       (${played} stones, ${passes} passes, final ${r.black.toFixed(1)}–${r.white.toFixed(1)})`);
  }catch(e){ crashed=e; ok("500 random moves without crashing", false, e.message+e.stack); }
}

/* ---- 10. the bot ---- */
console.log("\nbot");
{
  const el=id=>T.doc.getElementById(id);
  el("selSize").value="9"; el("selHc").value="0"; el("inKomi").value="7.5";
  T.newGame(); T.botScratch(9);

  // A playout must reach a real ending, not run out of moves.
  let byCap=0, byPass=0;
  for(let k=0;k<20;k++){
    const b=new Array(81).fill(0); let col=B, ko=-1, passes=0, moves=0;
    while(passes<2 && moves<202){
      const i=T.policyMove(b,col,ko);
      if(i<0){ passes++; ko=-1; } else { ko=T.playFast(b,i,col); passes=0; moves++; }
      col=(col===B?W:B);
    }
    moves>=202 ? byCap++ : byPass++;
  }
  ok("playouts end by passing, not by running out of moves", byCap===0,
     `${byCap} hit the cap, ${byPass} passed`);

  // Light playouts should look like a game, not a scribble: both colours get
  // stones, and most of the board is accounted for.
  let bs=0, ws=0, n=40, brk=false;
  for(let k=0;k<n;k++){
    const b=new Array(81).fill(0);
    T.playout(b, B, -1);
    const s=T.scoreOn(b);
    bs+=s.stones[0]; ws+=s.stones[1];
  }
  ok("playouts give both colours stones",
     bs/n>8 && ws/n>8 && Math.abs(bs-ws)<n*3, `B ${(bs/n).toFixed(1)} W ${(ws/n).toFixed(1)}`);

  // The search must return a legal move, and it must be a real choice.
  const r=T.searchSync(300);
  // The root set is bounded on purpose: spreading the playouts over every
  // empty point leaves each one too few to tell them apart.
  ok("root move set is bounded", r.branches>5 && r.branches<=41,
     "branches="+r.branches);
  ok("opening move is a real point, not a pass", r.bestMove>=0, "move="+r.bestMove);
  ok("search commits visits to a child", r.bestVisits>0, "bestVisits="+r.bestVisits);
  ok("best move is legal",
     T.illegal(T.board, r.bestMove, T.toPlay, T.koPoint, T.seen)===null,
     "reason="+T.illegal(T.board, r.bestMove, T.toPlay, T.koPoint, T.seen));
  ok("best move beats the average child",
     r.bestRate>0.4, "rate="+r.bestRate);
}
{
  // Bot against bot, to the end. Uses few playouts per move to stay quick;
  // this is about the game running clean, not about strength.
  const el=id=>T.doc.getElementById(id);
  el("selSize").value="9"; T.newGame();
  let n=0, err=null;
  try{
    while(T.phase==="play" && n<200){ T.botMoveOnce(40); n++; }
  }catch(e){ err=e.message; }
  ok("bot plays a whole game without throwing", err===null, err||"");
  ok("game ends in scoring", T.phase==="score", "phase="+T.phase+" after "+n+" moves");
  ok("both colours moved", T.playedIndexes().filter(i=>i>=0).length>10);
  ok("no illegal move stalled the game", T.moveNo>=n-2, `moveNo=${T.moveNo} n=${n}`);
  const s=T.scoreGame();
  const sum=s.stones[0]+s.stones[1]+s.terr[0]+s.terr[1]+s.terr[2];
  ok("score accounts for the whole board", sum===81, "sum="+sum);
}
{
  // The bot's search state must not be left corrupting the real game.
  const el=id=>T.doc.getElementById(id);
  el("selSize").value="9"; T.newGame();
  const before=T.key(T.board);
  T.searchSync(200);
  ok("searching leaves the real board untouched", T.key(T.board)===before);
  ok("searching records no move", T.moveNo===0 && T.history.length===0);
}
{
  // Regression: 7.5 komi on a 9x9 is 9% of the board, and the search took the
  // pass branch and ended the game on move three (D5 D6 pass pass).
  const el=id=>T.doc.getElementById(id);
  for(const [sz,k] of [["9","5.5"],["13","7.5"],["19","7.5"]]){
    el("selSize").value=sz; el("selSize").onchange();
    ok(sz+"x"+sz+" default komi is "+k, +el("inKomi").value===+k, el("inKomi").value);
  }
  el("selSize").value="9"; el("selSize").onchange(); T.newGame();
  ok("engine reads the 9x9 komi", T.komi===5.5, "komi="+T.komi);
}
{
  // The same defect, seen as behaviour: the bot must not pass out a nearly
  // empty board at any komi.
  const el=id=>T.doc.getElementById(id);
  for(const k of ["0","5.5","7.5"]){
    el("selSize").value="9"; el("inKomi").value=k; T.newGame();
    let n=0;
    while(T.phase==="play" && n<20){ T.botMoveOnce(150); n++; }
    const early=T.playedIndexes().slice(0,8).filter(i=>i<0).length;
    ok("9x9 komi "+k+": no pass in the first 8 moves", early===0, early+" passes");
    ok("9x9 komi "+k+": game still running at 20 plies", T.phase==="play",
       "phase="+T.phase+" after "+T.moveNo+" moves");
  }
}

console.log(`\n${pass} passed, ${fail} failed\n`);
process.exit(fail?1:0);
