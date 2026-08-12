module Sql = struct
  let begin_tx order = ()
  let insert order = ()
  let commit order = ()
end

module Postgres = struct
  let save order =
    Sql.begin_tx order;
    Sql.insert order;
    Sql.commit order
end

let validate order = ()
let finalize order = ()

let run order =
  validate order;
  Postgres.save order;
  finalize order
