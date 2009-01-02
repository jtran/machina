// Interpreter Core
// by Jonathan Tran
// http://jonnytran.com/

if (!console) {
  // Define dummy console if Firebug isn't loaded.
  var console = {
    debug: function(s) {},
    error: function(s) {},
    info:  function(s) {},
    log:   function(s) {},
    warn:  function(s) {},
  }
}

// Generic equality
function equals(a, b) {
  for (var j, o = arguments, i = o.length, c = a instanceof Object; --i;)
    if (a === (b = o[i]))
      continue;
    else if (!c || !(b instanceof Object))
      return false;
    else for (j in b)
      if (!equals(a[j], b[j]))
        return false;
  return true;
}

// Generic object cloning
function clone(obj) {
  if (obj == null || typeof(obj) != 'object') return obj;

  var temp = new obj.constructor();

  for (var k in obj) {
    // TODO: make transients generic, not just this one field.
    if (k == 'evaled') continue;  // Don't copy transients
    temp[k] = clone(obj[k]);
  }

  return temp;
}

// e.g. (For example)
// Asserts an example has an expected value
function eg(expected, v) {
  if (expected.neq(v)) {
    console.error("Test failed: expected: ", expected, '  found: ', v);
  }
  return v;
}


// Global work queue
var q = [];
var newQ = [];
var pushedToQ = [];

function addToWorkQueue(f) {
  pushedToQ.push(f);
}


// Asserts that an expression has a specified type
function ofType(t, v) {
  if (t !== v.type) {
    console.error("Type assertion failed: expected: ", t, '  found: ', v.type);
  }
  return v;
}

// The constructor for all expressions in the language.
function Exp() {
  this.type = arguments[0];

  this.eq = function() {
    var a = [this];
    $.each(arguments, function(i, x) {a.push(x)} );
    return equals.apply(this, a);
  }

  this.neq = function() {
    return !this.eq.apply(this, arguments);
  }
  
  this.getChildren = function() { return [] }
  
  this.toHtmlString = function() { return this.toString() }
  
  this.toElmt = function() {
    var elmt = document.createElement('div');
    $(elmt).html(this.toHtmlString());
    $.each(this.getChildren(), function(i, child) {
      if (child.length) {
        $.each(child, function(j, subchild) {
          $(elmt).append(subchild.toElmt());
        });
      }
      else {
        $(elmt).append(child.toElmt());
      }
    });
    elmt.className = this.className;
    return elmt;
  }
  
  this.toLayout = function() {
    var elmt = document.createElement('div');
    $.each(this.getChildren(), function(i, child) {
      if (child.length) {
        $.each(child, function(j, subchild) {
          $(elmt).append(subchild.toLayout());
        });
      }
      else {
        $(elmt).append(child.toLayout());
      }
    });
    var div = document.createElement('div');
    $(div).append(this.toHtmlString());
    if (this.evaled) {
      $(div).append('<span class="evaled">' + this.evaled + '</span>');
    }
    $(elmt).append(div);
    elmt.className = this.className;
    return elmt;
  };
  
  switch (arguments[0]) {
  case 'NIL':
    this.className = "exp list nil";
    this.toString = function() {
      return 'nil';
    }
    break;
  
  case 'PAIR':
    this.first = arguments[1];
    this.second = arguments[2];
    this.className = "exp list pair";
    this.getChildren = function() { return [this.first, this.second] }
    this.toString = function() {
      return '(' + this.first + ', ' + this.second + ')';
    }
    this.toHtmlString = function() {
      return 'pair';
    }
    break;
  
  case 'FST':
    this.pair = arguments[1];
    this.className = 'exp fst';
    this.getChildren = function() { return [this.pair] }
    this.toString = function() {
      return this.pair + '.1';
    }
    this.toHtmlString = function() {
      return 'first';
    }
    break;
  
  case 'SND':
    this.pair = arguments[1];
    this.className = 'exp snd';
    this.getChildren = function() { return [this.pair] }
    this.toString = function() {
      return this.pair + '.2';
    }
    this.toHtmlString = function() {
      return 'second';
    }
    break;
  
  case 'INT':
    this.intVal = arguments[1];
    this.className = 'exp int';
    this.toString = function() {
      return this.intVal.toString(); // + ' : ' + this.type.toLowerCase();
    }
    this.toHtmlString = function() {
      return this.intVal.toString(); // + '&nbsp;:&nbsp;' + this.type.toLowerCase();
    }
    break;
  
  case 'SYM':
    this.symVal = arguments[1];
    this.className = 'exp sym';
    this.toString = function() {
      return this.symVal;
    }
    this.toHtmlString = function() {
      return "<i>" + this.symVal + "</i>";
    }
    break;
  
  case 'CHAN':
    this.ctx = arguments[1];
    this.sender = arguments[2];
    this.value = null;
    this.send = function(v) {
      if (isValue(v)) {
        console.debug('chan was sent value', this, v);
        this.value = v;
      }
      else {
        this.sender = v;
      }
      // TODO: wake up the thread waiting?
      
      // Return true to remove this from the queue.
      return isValue(v);
    }
    this.className = 'exp chan';
    this.getChildren = function() { return [this.sender] }
    this.toString = function() {
      return "(ch " + this.sender + ")";
    }
    this.toHtmlString = function() {
      return "chan";
    }
    break;
  
  case 'PRIM':
    this.primOp = arguments[1];
    this.className = 'exp prim';
    this.toString = function() {
      return this.primOp;
    }
    break;
  
  case 'FUN':
    $.each(arguments[1], function(i, s) {
      ofType('SYM', s);
    });
    this.params = arguments[1];
    this.body = arguments[2];
    if (arguments.length > 3) {
      this.fixPoint = arguments[3];
    }
    this.className = 'exp fun';
    this.getChildren = function() { return [this.body] }
    this.toString = function() {
      return 'fn(' + this.params.join(',') + ')';
    }
    this.toHtmlString = function() {
      var s = '';
      if (this.fixPoint) {
        s += 'let <i>' + this.fixPoint + '</i> = ';
      }
      s += '&lambda; ' + $.map(this.params, function(s) {return "<i>" + s + "</i>"}).join(', ') + '.';
      return s;
    }
    break;
  
  case 'CLOSURE':
    this.ctx = arguments[1];
    this.params = arguments[2];
    this.body = arguments[3];
    this.fixPoint = arguments[4];
    this.className = 'exp closure';
    this.getChildren = function() { return [this.body] }
    this.toString = function() {
      return '<G, fn(' + this.params.join(',') + ')>';
    }
    this.toHtmlString = function() {
      return '&lt;&Gamma;, &lambda; ' +
        $.map(this.params, function(s) {return "<i>" + s.toHtmlString() + "</i>"}).join(', ') +
        '&gt;';
    }
    break;
  
  case 'APP':
    this.fun = arguments[1];
    this.args = arguments[2];
    this.getChildren = function() { return [this.fun, this.args] }
    this.className = 'exp app';
    this.toString = function() {
      return 'apply';
    }
    break;
  
  case 'CASE':
    this.cond = arguments[1];
    this.branches = arguments[2];
    this.className = 'exp case';
    this.getChildren = function() { return [this.cond, this.branches] }
    this.toString = function() {
      return 'case';
    }
    this.toLayout = function() {
      var elmt = document.createElement('div');
      $(elmt).append(this.cond.toLayout());
      for (var i = 0; i < this.branches.length; i += 2) {
        // Make a div of each branch
        var div = document.createElement('div');
        $(div).append(this.branches[i].toLayout());
        if (i != this.branches.length - 1) {
          $(div).append(this.branches[i+1].toLayout());
        }
        // Set the class
        div.className = 'case_branch';
        
        $(elmt).append(div);
      }
      
      var div = document.createElement('div');
      $(div).append(this.toHtmlString());
      if (this.evaled) {
        $(div).append('<span class="evaled">' + this.evaled + '</span>');
      }
      div.className = 'label';
      $(elmt).append(div);
      elmt.className = this.className;
      return elmt;
    };
    break;
  
  default:
    // clone calls this with 0 args all the time.
    //console.warn('Unknown expression type', this.type);
  };
  
}

// Returns true iff e is a value.
function isValue(e) {
  switch(e.type) {
  case 'INT':
  case 'NIL':
  case 'PAIR':
  case 'PRIM':
  case 'CLOSURE':
    return true;
  default:
    return false;
  }
}

// TODO: implement
function isNormalForm(e) {
  return isValue(e);
}

// Returns true iff e is in weak head normal form (WHNF).
// Basically, this is a fancy way of saying that the caller needs to force
// evaluation of e enough so that it can see its top-level form or shape.  In
// this language an exp is in WHNF if it is not immediately reducable.
function isWhnf(e) {
  switch(e.type) {
  case 'INT':
  case 'NIL':
  case 'PAIR':
  case 'PRIM':
  case 'CLOSURE':
    return true;
  default:
    return false;
  }
}

// Returns true iff eCond matches the pattern.
function matches(ctx, ePattern, eCond) {
  switch (ePattern.type) {
  case 'PAIR':
    return ePattern.type == eCond.type &&
           matches(ePattern.first,  eCond.first) &&
           matches(ePattern.second, eCond.second);
  case 'NIL':
    return ePattern.type == eCond.type;
  case 'INT':
    return ePattern.type == eCond.type &&
           ePattern.intVal == eCond.intVal;
  case 'SYM':
    // Symbols match anything.  ???
    return true;
  case 'PRIM':
    return ePattern.type == eCond.type &&
           ePattern.primOp == eCond.primOp;
  default:
    console.error('Invalid pattern of type: ' + ePattern.type);
    throw ePattern;
  }
}

// Evaluates e in the given context.
// This always returns immediately, possibly spawning a new thread/channel.
function eval(ctx, e) {
  // If e is a value, don't spawn.
  if (isValue(e)) return e;
  
  // If e is already a channel, don't spawn.
  if (e.type == 'CHAN') {
    // If the channel has already been sent a value, remove the channel.
    if (e.value)  console.debug('popping chan %o with value %s', e, e.value);
    if (!e.value) console.debug('evaling chan %s', e);
    return (e.value) ? e.value
                     : e
  }
  
  var ch = new Exp('CHAN', ctx, e);
  
  // Wrap call to evalStep so that we can return immediately and
  // send the eventual return value to the channel.
  var g = function() {
    var v = evalStep(ch.ctx, ch.sender);
    
    // Cache results
    if (v !== ch.sender) {
      ch.sender.evaled = v;
    }
    
    // Channel determines whether we should be removed from the queue.
    return ch.send(v);
  }
  
  // Add g to the global thread queue.
  console.debug('pushing ', e, ch);
  addToWorkQueue({thunk: g, chan: ch});
  
  return ch;
}

// Evaluate e in the given context.
// This only takes one step of evaluation, so the returned exp may not be a
// value.
function evalStep(ctx, e) {
  switch (e.type) {
  case 'NIL':
    return e;
  case 'PAIR':
    return e;
  case 'FST':
    var p = eval(ctx, e.pair);
    return (p.type == 'PAIR') ? p.first
                              : eval(ctx, new Exp('FST', p));
  case 'SND':
    var p = eval(ctx, e.pair);
    return (p.type == 'PAIR') ? p.second
                              : eval(ctx, new Exp('SND', p));
  case 'INT':
    return e;
  case 'SYM':
    return clone(ctx[e.symVal]);
  case 'PRIM':
    return e;
  case 'FUN':
    return new Exp('CLOSURE', ctx, e.params, e.body, e.fixPoint);
  case 'CLOSURE':
    return e;
  case 'CHAN':
    return (e.value) ? e.value
                     : e;
  case 'APP':
    var f = eval(ctx, e.fun);
    var args = $.map(e.args, function(e) {
            return eval(ctx, e);
          });
    
    if (f.type == 'PRIM') {
      var notAllInt = function() {
        for (var i = 0; i < args.length; i++) {
          if (args[i].type != 'INT') return true;
        }
        return false;
      }
      
      switch (f.primOp) {
      case 'ADD':
        if (notAllInt()) return new Exp('APP', f, args);
        s = 0;
        $.each(args, function() {
          s += this.intVal;
        });
        return new Exp('INT', s);
      case 'MUL':
        if (notAllInt()) return new Exp('APP', f, args);
        s = 1;
        $.each(args, function() {
          s *= this.intVal;
        });
        return new Exp('INT', s);
      case 'SUB':
        if (notAllInt()) return new Exp('APP', f, args);
        return new Exp('INT', args[0].intVal - args[1].intVal);
      case 'NEG':
        if (notAllInt()) return new Exp('APP', f, args);
        return new Exp('INT', -args[0].intVal);
      case '=':
        // TODO: Fix this
        if (args[0].eq(args[1])) {
          return new Exp('INT', 1);
        }
        else {
          return new Exp('NIL');
        }
      default:
        console.error('Unknown primitive op: ', f);
        throw e;
      }
    }
    else if (f.type == 'CLOSURE') {
      if (args.length > f.params.length) {
        console.error('Function expects %d parameter(s); applied to %d args', f.params.length, args.length);
        throw e;
      }

      // Clone the context so we leave the original in tact.
      appCtx = clone(f.ctx);
      // Bind fix point
      if (f.fixPoint) {
        appCtx[f.fixPoint] = f;
      }
      // Bind arguments to params
      $.each(args, function(i, arg) {
        appCtx[f.params[i].symVal] = arg;
      });
      // Eval in the new context
      var v = eval(appCtx, f.body);

      return v;
    }
    return new Exp('APP', f, args);
    
  case 'CASE':
    var vCond = eval(ctx, e.cond);
    // eval patterns?
    // eval patterns, but not branch bodies.
    // var vBranches = $.map(e.branches, function(i, e) {
    //       return (i % 2 == 0) ? eval(ctx, e)
    //                           : e
    //     });
    
    if (!isWhnf(vCond)) return new Exp('CASE', vCond, e.branches);
    
    for (var i = 0; i < e.branches.length; i += 2) {
      // If we've reached the end, the last pattern is actually the else
      // branch.
      if (i == e.branches.length - 1) {
        return eval(ctx, e.branches[i]);
      }

      // If pattern matches, evaluate the branch
      if (matches(ctx, e.branches[i], vCond)) {
        return eval(ctx, e.branches[i+1]);
      }
    }
    console.error('Malformed case expression; missing else branch', e);
    throw e;
    
  default:
    console.error('Can not evalate expression of unknown type: ', e);
  }
}

// Force evaluation of e in the given context.
// This calls evalStep repeatedly until e is in normal form.
// A callback can optionally be given to watch evaluation step by step.
function force(ctx, e) {
  var t = 0;
  var callback = (arguments.length > 2) ? arguments[2] : null;
  
  while (!isNormalForm(e)) {
    // step each thing in the queue
    newQ = $.grep(q, function(work) {
      var keep = ! work.thunk();  // do work
      if (callback) callback(e, t);
      return keep;
    });
    q = newQ.concat(pushedToQ);
    pushedToQ = [];
    
    e = evalStep(ctx, e);
    
    // Show the caller where we are so far.
    if (callback) callback(e, t);
    
    // Track how many steps we've taken.
    t++;
    
    // Exit early if we've been running a long time.
    if (window.debug && t >= 100) {
      console.debug('q', q);
      console.error('force took too many iterations (%d). Turn off window.debug to continue unbounded.', t);
      return e;
    }
  }
  
  console.info('force iterations:', t);
  return e;
}

// The empty context used for evaluation.
function emptyCtx() {
  return {};
}
