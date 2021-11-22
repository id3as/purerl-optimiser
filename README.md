# purerl-optimiser

A parse-transform for optimising the output from purescript / purerl. There are a number of

# Configuration

At present, configuration is simple and purely around the optimisations around math operators. For example, in your rebar.config,

```
{deps, [
        ...
        {purerl_optimiser, {git,"https://github.com/id3as/purerl-optimiser.git", {branch, main}}}
        ...
       ]}.

{erl_opts,
 [ ...
 , {parse_transform, purerl_optimiser}
 , {d, 'PURERL_MEMOIZE', 1}
 , {purerl_optimiser, #{ math => #{ booleanLike => [ "Data.HeytingAlgebra.heytingAlgebraBoolean "
                                                   ]
                                  , intLike => [ "Data.Eq.eqInt"
                                               , "Data.Ord.ordInt"
                                               , "Data.Semiring.semiringInt"
                                               , "Data.Semiring.ringInt"
                                               , "Data.EuclideanRing.euclideanRingInt"
                                               , "Avp.Types.ordFfiInt90"
                                               , "Avp.Types.semiringFfiInt90"
                                               , "Avp.Types.ringFfiInt90"
                                               ]
                                  , numberLike => [ "Data.Ord.ordNumber"
                                                  , "Data.Time.Duration.ordMilliseconds"
                                                  , "Data.Semiring.semiringNumber"
                                                  , "Data.Semiring.ringNumber"
                                                  , "Data.EuclideanRing.euclideanRingNumber"
                                                  , "Data.Eq.eqNumber"
                                                  ]
                                  }
                       }
   }
   ...
 ]}.

```

So within deps, include this repository. And then within your erl_opts:

`{parse_transform, purerl_optimiser}` - add the parse transform to the compile step

`{d, 'PURERL_MEMOIZE', 1}` - define PURERL_MEMOIZE to enable the memoization feature

`{purerl_optimiser, ...` - configuration for the parse transform itself. Currently, this provides information for the math optimisations to indicate which types (or more specifically typeclasses) are just Newtype wrappers around boolean / integer / float values.

# Diagnostics

If you define the `PURS_OPTIMISER_DEBUG` environment variable, then the parse transform will dump the converted erlang files into /tmp/purs_optimiser, e.g.:

```
PURS_OPTIMISER_DEBUG=1 rebar3 compile
```

## Build

    $ rebar3 compile
