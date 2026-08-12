module Sql = struct
  let insert order = ()
end

module Postgres = struct
  let save order = Sql.insert order
end

let validate order = ()
let finalize order = ()

let run order =
  validate order;
  Postgres.save order;
  finalize order
