open LMLCv2

let _ = let x = Lang.fresh_ml () in
        let y = Lang.fresh_ml () in
        (Lang.pp_lambda (Executor.evaluate (Transpiler.lmlc (Appl (Fun (x, Var x), Var y)))))