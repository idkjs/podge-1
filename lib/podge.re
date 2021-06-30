/** A Hodgepodge of functionality in OCaml */;

/** Module handles to the original libraries themselves */
module Originals = {
  module U = Unix;
  module P = Printf;
  module L = List;
  module Y = Yojson.Basic;
  module T = ANSITerminal;
  module S = String;
};

/** Simple Module Alias of Astring */
module String = Astring;

/** Math and Probability functions */
module Math = {
  type nums('a) =
    | Int: nums(int)
    | Float: nums(float);

  /** Produce an array of random Floats or Ints */

  let random_array = (type t, n, num_t: nums(t)) => {
    Random.self_init();
    switch (num_t) {
    | Int => (
        Array.init(
          n,
          _ => {
            let made = Random.int(1 lsl 30 - 1);
            if (Random.bool()) {
              made;
            } else {
              (-1) * made;
            };
          },
        ):
          array(t)
      )
    | Float => (Array.init(n, _ => Random.float(max_float)): array(t))
    };
  };

  /** Calculate first deriviative of f */

  let derivative = (~f, argument) => {
    let eps = sqrt(epsilon_float);
    (f(argument +. eps) -. f(argument -. eps)) /. (2. *. eps);
  };

  /** Simple Linear regression */

  let linear_regression = (~xs, ~ys) => {
    let sum = xs =>
      Array.fold_right((value, running) => value +. running, xs, 0.0);
    let mean = xs => sum(xs) /. float_of_int(Array.length(xs));
    let mean_x = mean(xs);
    let mean_y = mean(ys);
    let std = (xs, m) => {
      let normalizer = Array.length(xs) - 1;
      sqrt(
        Array.fold_right(
          (value, running) => (value -. m) ** 2.0 +. running,
          xs,
          0.0,
        )
        /. float_of_int(normalizer),
      );
    };
    let pearson_r = (xs, ys) => {
      let sum_xy = ref(0.0);
      let sum_sq_v_x = ref(0.0);
      let sum_sq_v_y = ref(0.0);
      let zipped =
        Originals.L.combine(Array.to_list(xs), Array.to_list(ys));
      List.iter(
        ((i_x, i_y)) => {
          let var_x = i_x -. mean_x;
          let var_y = i_y -. mean_y;
          sum_xy := sum_xy^ +. var_x *. var_y;
          sum_sq_v_x := sum_sq_v_x^ +. var_x ** 2.0;
          sum_sq_v_y := sum_sq_v_y^ +. var_y ** 2.0;
        },
        zipped,
      );
      sum_xy^ /. sqrt(sum_sq_v_x^ *. sum_sq_v_y^);
    };
    let r = pearson_r(xs, ys);
    let b = r *. std(ys, mean_y) /. std(xs, mean_x);
    let a = mean_y -. b *. mean_x;
    let line = x => b *. x +. a;
    line;
  };

  let rec pow = (~base) =>
    fun
    | 0 => 1
    | 1 => base
    | n => {
        let b = pow(~base, n / 2);
        b
        * b
        * (
          if (n mod 2 == 0) {
            1;
          } else {
            base;
          }
        );
      };

  let log2 = x => log(x) /. log(2.);

  let bit_string_of_int = num => {
    let rec helper = (a_num, accum) =>
      switch (a_num) {
      | 0 => accum
      | _x => [string_of_int(a_num mod 2), ...helper(a_num / 2, accum)]
      };

    helper(num, []) |> List.rev |> Originals.S.concat("");
  };

  let bit_string_of_string = str => {
    let all_ints = ref([]);
    Originals.S.iter(
      a_char => all_ints := [int_of_char(a_char), ...all_ints^],
      str,
    );
    List.rev(all_ints^)
    |> List.map(bit_string_of_int)
    |> Originals.S.concat("");
  };

  let sum_ints = l => List.fold_left((+), 0, l);

  let sum_floats = l => List.fold_left((+.), 0.0, l);

  let average_ints = l =>
    float_of_int(sum_ints(l)) /. float_of_int(List.length(l));

  let average_floats = l => sum_floats(l) /. float_of_int(List.length(l));

  let pi = 4.0 *. atan(1.0);

  /** Range takes:
      an optional chunk int [defaulting to 1],
      an optional inclusivity bool [defaulting to false],
      a labeled ~from int [where the list starts from]
      and finally, the "upto" int [where the list ends].

      By default, your upto is not inclusive. So for example:
      1 <--> 5 gives back [1; 2; 3; 4]
      but
      1 <---> 5 gives back [1; 2; 3; 4; 5]

      It can also handle descending amounts:
      1 <---> -10 gives you
      [1; 0; -1; -2; -3; -4; -5; -6; -7; -8; -9; -10]
      and 1 <--> 1 gives you []

      Note: <--> <---> are located in Podge.Infix
      See also: it is tail recursive. */

  let range = (~chunk=1, ~inclusive=false, ~from, upto) =>
    if (upto < from) {
      let rec dec_aux = (count, upto, accum) =>
        if (inclusive) {
          if (count - chunk < upto) {
            List.rev([count, ...accum]);
          } else {
            dec_aux(count - chunk, upto, [count, ...accum]);
          };
        } else if (count - chunk <= upto) {
          List.rev([count, ...accum]);
        } else {
          dec_aux(count - chunk, upto, [count, ...accum]);
        };

      dec_aux(from, upto, []);
    } else if (upto == from) {
      [];
    } else {
      let rec asc_aux = (count, upto, accum) =>
        if (inclusive) {
          if (count + chunk > upto) {
            List.rev([count, ...accum]);
          } else {
            asc_aux(count + chunk, upto, [count, ...accum]);
          };
        } else if (count + chunk >= upto) {
          List.rev([count, ...accum]);
        } else {
          asc_aux(count + chunk, upto, [count, ...accum]);
        };

      asc_aux(from, upto, []);
    };

  let validate_prob = p =>
    if (p < 0.0 || p > 1.0) {
      raise(
        Invalid_argument(
          "Not a valid Probability, needs to be between 0 and 1",
        ),
      );
    };

  /** Computes the entropy from a list of probabilities */

  let entropy = probs =>
    List.fold_left(
      (accum, p) => {
        validate_prob(p);
        accum +. p *. log2(1.0 /. p);
      },
      0.0,
      probs,
    );

  /** Represents the number of bits of information contained in this
      message, roughly how many number of bits we should encode this
      message with. The less likely an event is to occur, the more
      information we can say actually is contained in the event */

  let self_information = p => {
    validate_prob(p);
    log2(1.0 /. p);
  };

  let rec distance = (l, r) =>
    switch (l, r) {
    | ([a_val_l, ...rest_l], [a_val_r, ...rest_r]) =>
      (a_val_l -. a_val_r) ** 2.0 +. distance(rest_l, rest_r)
    | _ => 0.0
    };

  let init_with_f = (~f, n) => {
    let rec init_aux = (n, accum) =>
      if (n <= 0) {
        accum;
      } else {
        init_aux(n - 1, [f(n - 1), ...accum]);
      };

    init_aux(n, []);
  };

  let combination = (n, m) => {
    let g = ((k, r)) =>
      init_with_f(~f=i => (k + pow(~base=2, n - i - 1), i), r);
    let rec aux = (m, xs) =>
      if (m == 1) {
        List.map(fst, xs);
      } else {
        aux(m - 1, List.map(g, xs) |> List.concat);
      };

    aux(m, init_with_f(~f=i => (pow(~base=2, i), n - i - 1), n));
  };
};

module Infix = {
  /** See Podge.Math.range for documentation. */

  let (<-->) = (i, j) => Math.range(~from=i, j);

  /** See Podge.Math.range for documentation. */

  let (<--->) = (i, j) => Math.range(~inclusive=true, ~from=i, j);
};

/** Pretty printing of json and updating */
module Yojson = {
  type did_update = [ | `Updated | `No_update];

  let show_pretty_of_string = s =>
    Yojson.Basic.from_string(s)
    |> Yojson.Basic.pretty_to_string
    |> print_endline;

  let show_pretty_of_in_mem = j =>
    Yojson.Basic.pretty_to_string(j) |> print_endline;

  let show_pretty_of_file = f =>
    Yojson.Basic.from_file(f)
    |> Yojson.Basic.pretty_to_string
    |> print_endline;

  /** Update a value for a given key */

  let update = (~key, ~new_value, j): (did_update, Yojson.Basic.t) => {
    let updated = ref(false);
    let as_obj = Yojson.Basic.Util.to_assoc(j);
    let g =
      List.map(
        fun
        | (this_key, _inner) when this_key == key => {
            updated := true;
            (this_key, new_value);
          }
        | otherwise => otherwise,
        as_obj,
      );

    if (updated^) {
      (`Updated, `Assoc(g));
    } else {
      (`No_update, `Assoc(g));
    };
  };

  /** Remove a key-value pair */

  let remove = (~key, j): (did_update, Yojson.Basic.t) => {
    let updated = ref(false);
    let as_obj = Yojson.Basic.Util.to_assoc(j);
    let g =
      List.fold_left(
        (accum, (this_key, _) as key_value) =>
          if (this_key == key) {
            updated := true;
            accum;
          } else {
            [key_value, ...accum];
          },
        [],
        as_obj,
      );

    if (updated^) {
      (`Updated, `Assoc(List.rev(g)));
    } else {
      (`No_update, `Assoc(List.rev(g)));
    };
  };
};

/** Helper functions for using Tyxml */
module Html5 = {
  /** Print to stdout a tag */

  let show_tag = e => {
    let format = Format.formatter_of_out_channel(Stdlib.stdout);

    Tyxml.Xml.pp((), format, e);
  };

  /** Convert a Tyxml into a string */

  let to_string = e => {
    let cont = Buffer.create(1024);
    let format = Format.formatter_of_buffer(cont);

    Tyxml.Xml.pp((), format, e);
    Buffer.contents(cont);
  };
};

module Unix: {
  /** Read all the output of a process */

  let read_process_output: string => list(string);

  /** Read all the contents of a file, get back a string */

  let read_lines: string => list(string);

  /** Read all the contents of a file as a single string */

  let read_all: string => string;

  /** Read one char from the terminal without waiting for the return
      key */

  let get_one_char: unit => char;

  /** Simple time stamp of the current time */

  let time_now: unit => string;

  /** Daemonize the current process */

  let daemonize: unit => unit;

  /** Simple timeout  */

  let timeout:
    (
      ~on_timeout: unit => unit=?,
      ~arg: 'a,
      ~timeout: int,
      ~default_value: 'b,
      'a => 'b
    ) =>
    'b;
} = {
  let exhaust = ic => {
    let all_input = ref([]);
    try(
      while (true) {
        all_input := [input_line(ic), ...all_input^];
      }
    ) {
    | End_of_file => ()
    };
    close_in(ic);
    List.rev(all_input^);
  };

  let read_process_output = p => Unix.open_process_in(p) |> exhaust;

  let read_lines = path => open_in(path) |> exhaust;

  let read_all = path => open_in(path) |> exhaust |> Originals.S.concat("");

  let get_one_char = () => {
    let termio = Unix.(tcgetattr(stdin));
    Unix.(tcsetattr(stdin, TCSADRAIN, {...termio, c_icanon: false}));
    let res = input_char(stdin);
    Unix.(tcsetattr(stdin, TCSADRAIN, termio));
    res;
  };

  let time_now = () => {
    open Unix;
    let localtime = localtime(time());
    Printf.sprintf(
      "[%02u:%02u:%02u]",
      localtime.tm_hour,
      localtime.tm_min,
      localtime.tm_sec,
    );
  };

  let daemonize = () =>
    switch (Unix.fork()) {
    | pid =>
      if (pid < 0) {
        raise(Failure("Couldn't fork correctly"));
      } else if (pid > 0) {
        exit(-1);
      } else {
        switch (Unix.setsid()) {
        | sid =>
          if (sid < 0) {
            raise(Failure("Issue with setsid"));
          } else if (sid > 0) {
            exit(-1);
          } else {
            Unix.umask(0)
            |> (
              _ => {
                Unix.chdir("/");
                List.iter(Unix.close, [Unix.stdin, Unix.stdout]);
              }
            );
          }
        };
      }
    };

  let timeout = (~on_timeout=() => (), ~arg, ~timeout, ~default_value, f) => {
    exception Timeout;
    let sigalrm_handler = Sys.Signal_handle(_ => raise(Timeout));
    let old_behavior = Sys.signal(Sys.sigalrm, sigalrm_handler);
    let reset_sigalrm = () => Sys.set_signal(Sys.sigalrm, old_behavior);
    ignore(Unix.alarm(timeout));
    try({
      let res = f(arg);
      reset_sigalrm();
      res;
    }) {
    | exc =>
      reset_sigalrm();
      if (exc == Timeout) {
        on_timeout();
        default_value;
      } else {
        raise(exc);
      };
    };
  };
};

module Analyze = {
  let time_it = (~f, x) => {
    let t = Sys.time();
    let fx = f(x);
    (Printf.sprintf("Execution time: %fs\n", Sys.time() -. t), fx);
  };

  /* TODO Add a doc string explaing meaning */
  let ratio_pair = (time_double, time) => {
    let r = time_double /. time;
    (`Time_ratio(r), `Time_log2_ratio(Math.log2(r)));
  };
};

module Cohttp = {
  let did_request_succeed = resp =>
    Cohttp.Response.status(resp)
    |> Cohttp.Code.code_of_status
    |> Cohttp.Code.is_success;

  let show_headers = hdrs =>
    hdrs
    |> Cohttp.Header.iter((key, values) =>
         Printf.sprintf(
           "%s",
           Printf.sprintf("%s %s", key, Originals.S.concat("", values)),
         )
         |> print_endline
       );
};

module Printf = {
  let printfn = str => Printf.kprintf(print_endline, str);
  let printfn_e = str => Printf.kprintf(prerr_endline, str);
};

module Debugging = {
  let show_callstack = n =>
    Printexc.get_callstack(n)
    |> Printexc.raw_backtrace_to_string
    |> print_endline;
};

module List = {
  /** Evaluate f on each item of the given list and check if all
      evaluated to true */

  let all = (~f, on) => List.map(f, on) |> List.fold_left((&&), true);

  /** Evaluate f on each item of the given list and check if any
      evaluated to false */

  let any = (~f, on) => List.map(f, on) |> List.fold_left((||), false);

  let unique = l =>
    List.fold_left(
      (a, e) =>
        if (List.mem(e, a)) {
          a;
        } else {
          [e, ...a];
        },
      [],
      l,
    );

  let group_by = ls => {
    let ls' =
      List.fold_left(
        (accum, (this_key, x1)) =>
          switch (accum) {
          | [] => [(this_key, [x1])]
          | [(that_key, ls2), ...acctl] =>
            if (this_key == that_key) {
              [(this_key, [x1, ...ls2]), ...acctl];
            } else {
              [(this_key, [x1]), ...accum];
            }
          },
        [],
        ls,
      );

    List.rev(ls');
  };

  let take = (~n, xs) => {
    let rec aux = (n, xs, accum) =>
      if (n <= 0 || xs == []) {
        List.rev(accum);
      } else {
        aux(n - 1, List.tl(xs), [List.hd(xs), ...accum]);
      };

    aux(n, xs, []);
  };

  let rec drop = (~n, xs) =>
    if (n <= 0 || xs == []) {
      xs;
    } else {
      drop(~n=n - 1, List.tl(xs));
    };

  let equal_parts = (~segs, l) => {
    let this_much = List.length(l) / segs;
    let rec helper = (accum, rest) =>
      switch (rest) {
      | [] => accum
      | rest =>
        let pull = take(~n=this_much, rest);
        let remaining = drop(~n=this_much, rest);
        if (List.length(remaining) < this_much) {
          [remaining @ pull, ...helper(accum, [])];
        } else {
          [pull, ...helper(accum, remaining)];
        };
      };

    helper([], l);
  };

  let filter_map = (~f, ~g, l) =>
    List.fold_left(
      (accum, value) =>
        if (f(value)) {
          [g(value), ...accum];
        } else {
          accum;
        },
      [],
      l,
    );

  let cut = (l, start) => {
    let result =
      List.fold_right(
        (value, (counter, (pre, after))) =>
          if (counter != start) {
            (counter + 1, ([value, ...pre], after));
          } else {
            (counter, (pre, [value, ...after]));
          },
        List.rev(l),
        (0, ([], [])),
      );

    let (pre, after) = snd(result);
    (List.rev(pre), List.rev(after));
  };
};

module Web: {
  /** Various reason why a HTTP request might fail */

  type error_t =
    | Can_only_handle_http
    | Host_lookup_failed
    | No_ip_from_hostname
    | Post_failed;

  /** Goes: HTTP status line, HTTP Headers, response body */

  type reply = result((string, list(string), string), error_t);

  /** Takes a HTTP url and gives back an optional pair of a list of
      headers and the body. HTTPS is accepted but warning it is not
      implemented so HTTPS servers may reject your request */

  let get: (~trim_body: bool=?, string) => reply;

  /** Takes a route and a bytes for body and does a PUT, no checking
      of HTTP errors, like get HTTPS requests will be accepted by
      post but it may be rejected by an HTTPS server since HTTPS is
      not currently implemented.*/

  let post: (~trim_reply: bool=?, ~post_body: string=?, string) => reply;
} = {
  type error_t =
    | Can_only_handle_http
    | Host_lookup_failed
    | No_ip_from_hostname
    | Post_failed;

  type reply = result((string, list(string), string), error_t);

  let (>>=) = (x, f: 'a => option('b)) =>
    switch (x) {
    | None => None
    | Some(d) => f(d)
    };

  let address = host =>
    Originals.U.(
      ADDR_INET(gethostbyname(host).h_addr_list[0], 80)
    );

  let really_output = (out_chan, message) => {
    output_bytes(out_chan, message);
    flush(out_chan);
  };

  let read_all = in_chan => {
    let buff = Buffer.create(4096);
    try(
      while (true) {
        input_char(in_chan) |> Buffer.add_char(buff);
      }
    ) {
    | End_of_file => ()
    };
    buff |> Buffer.to_bytes;
  };

  let headers_and_body = (~trim_body=true, http_resp) => {
    let starting_point = ref(2);
    let end_len = Bytes.length(http_resp);
    let last_two = Bytes.create(2);
    Bytes.set(last_two, 0, '\000');
    Bytes.set(last_two, 1, '\000');
    let current = Bytes.create(2);
    try(
      while (starting_point^ < end_len - 2) {
        open Bytes;
        set(last_two, 0, get(http_resp, starting_point^ - 2));
        set(last_two, 1, get(http_resp, starting_point^ - 1));
        set(current, 0, get(http_resp, starting_point^));
        set(current, 1, get(http_resp, starting_point^ + 1));
        let cr = Bytes.of_string("\r\n");
        if (last_two == cr && current == cr) {
          raise(Exit);
        };
        incr(starting_point);
      }
    ) {
    | Exit => ()
    };
    let leftover = end_len - starting_point^;
    let (status_line, headers) =
      switch (
        Originals.(
          Bytes.sub_string(http_resp, 0, starting_point^)
          |> S.split_on_char('\n')
          |> L.map(S.trim)
          |> L.filter((!=)(""))
        )
      ) {
      | [] => failwith("headers_and_body")
      | [s, ...h] => (s, h)
      };

    (
      status_line,
      headers,
      Bytes.sub(http_resp, starting_point^, leftover)
      |> (
        body =>
          if (trim_body) {
            Bytes.trim(body);
          } else {
            body;
          }
      ),
    );
  };

  let get = (~trim_body=true, route) => {
    let error_reason = ref(Can_only_handle_http);
    let uri = Uri.of_string(route);
    let request =
      Uri.scheme(uri)
      >>= (
        s =>
          switch (s) {
          | x when x != "http" && x != "https" => None
          | _ =>
            Uri.host(uri)
            >>= (
              host =>
                (
                  try(Some(Originals.U.open_connection(address(host)))) {
                  | Not_found =>
                    error_reason := Host_lookup_failed;
                    None;
                  | Invalid_argument(_) =>
                    error_reason := No_ip_from_hostname;
                    None;
                  }
                )
                >>= (
                  ((in_chan, out_chan)) => {
                    Originals.U.(
                      setsockopt(
                        descr_of_out_channel(out_chan),
                        TCP_NODELAY,
                        true,
                      )
                    );
                    let msg = host =>
                      Originals.P.sprintf(
                        "GET / HTTP/1.1\r\nHost:%s\r\nUser-Agent: OCaml - Podge\r\nConnection: close\r\n\r\n",
                        host,
                      );

                    really_output(out_chan, Bytes.of_string(msg(host)));
                    let all = read_all(in_chan);
                    try(
                      {
                        close_in(in_chan);
                        close_out(out_chan);
                      }
                    ) {
                    | _ => ()
                    };
                    Some(headers_and_body(~trim_body, all));
                  }
                )
            )
          }
      );

    switch (request) {
    | None => Error(error_reason^)
    | Some((a, b, c)) => Ok((a, b, Bytes.to_string(c)))
    };
  };

  let post = (~trim_reply=true, ~post_body=?, route) => {
    let uri = Uri.of_string(route);
    let error_reason = ref(Post_failed);
    let request =
      Uri.scheme(uri)
      >>= (
        s =>
          switch (s) {
          | x when x != "http" && x != "https" => None
          | _ =>
            Uri.host(uri)
            >>= (
              host => {
                let (in_chan, out_chan) =
                  Originals.U.open_connection(address(host));
                let fd_ = Originals.U.descr_of_out_channel(out_chan);
                Originals.(U.setsockopt(fd_, U.TCP_NODELAY, true));
                let post_request =
                  switch (post_body) {
                  | Some(b) =>
                    let b' = Bytes.of_string(b);
                    Originals.P.sprintf(
                      "POST %s HTTP/1.1\r\nHost:%s\r\nContent-length: %d\r\nUser-Agent: OCaml - Podge\r\nConnection: close\r\n\r\n%s",
                      Uri.path_and_query(uri),
                      host,
                      Bytes.length(b'),
                      b,
                    );
                  | None =>
                    Originals.P.sprintf(
                      "POST %s HTTP/1.1\r\nHost:%s\r\nUser-Agent: OCaml - Podge\r\nConnection: close\r\n\r\n",
                      Uri.path_and_query(uri),
                      host,
                    )
                  };

                really_output(out_chan, Bytes.of_string(post_request));
                let reply = read_all(in_chan);
                try(
                  {
                    close_in(in_chan);
                    close_out(out_chan);
                  }
                ) {
                | _ => ()
                };
                Some(headers_and_body(~trim_body=trim_reply, reply));
              }
            )
          }
      );

    switch (request) {
    | None => Error(error_reason^)
    | Some((a, b, c)) => Ok((a, b, Bytes.to_string(c)))
    };
  };
};

/** Simple querying for Xml nodes, keys order matters */
module Xml: {
  let query_node_of_file: (~keys: list(string), ~path: string) => string;
  let query_node_of_string: (~keys: list(string), ~str: string) => string;
} = {
  open Ezxmlm;

  let rec dig = (keys, xml_doc, final_result) =>
    switch (keys) {
    | [] => final_result
    | [outer_most, ...rest] =>
      let new_xml =
        try(member(Originals.S.lowercase_ascii(outer_most), xml_doc)) {
        | _ => member(Originals.S.lowercase_ascii(outer_most), xml_doc)
        };

      dig(rest, new_xml, data_to_string(new_xml));
    };

  let query_node_of_file = (~keys, ~path) => {
    let (_, xml) = from_channel(open_in(path));
    dig(keys, xml, "");
  };

  let query_node_of_string = (~keys, ~str) => {
    let (_, xml) = from_string(str);
    dig(keys, xml, "");
  };
};

module ANSITerminal = {
  open Originals;

  /** Create a colorized message, presumably for a log message */

  let colored_message =
      (~t_color=T.Yellow, ~m_color=T.Blue, ~with_time=true, str) => {
    let just_time =
      T.sprintf([T.Foreground(t_color)], "%s ", Unix.time_now());
    let just_message = T.sprintf([T.Foreground(m_color)], "%s", str);
    if (with_time) {
      just_time ++ just_message;
    } else {
      just_message;
    };
  };
};
