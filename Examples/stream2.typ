typed; inductive;

type Stream[A] = /\X (!K (A -> (K -> X) -> X) -> X);

let cons =  /\A fun a:A s:Stream[A] => /\X (fun t:!K (A -> (K -> X) -> X) => t a s):Stream[A];
