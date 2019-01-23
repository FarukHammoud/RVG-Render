local facade = require"facade"
local image = require"image"
local chronos = require"chronos"
local blue = require"blue"
local filter = require"filter"

local unpack = table.unpack
local floor = math.floor

local _M = facade.driver()

local background = _M.solid_color(_M.color.white)

local function stderr(...)
    io.stderr:write(string.format(...))
end
local function apply_linear(xf,x,y)
	return  xf[1]*x+xf[2]*y,xf[3]*x+xf[4]*y
end

local function apply(x_f,x,y)
	return x_f[1]*x+x_f[2]*y+x_f[3],x_f[4]*x+x_f[5]*y+x_f[6]
end
local function sign(x)
	if x > 0 then
		return 1
	elseif x == 0 then
		return 0
	else 
		return -1
	end
end
local function signn(x)
	if x == 0 then
		return 1
	else
		return sign(x)
	end
end
local function crossing_point(y,x1,y1,x2,y2)
	if y >= y1 and y <= y2 or y >= y2 and y <= y1 then
		f = (y-y1)/(y2-y1)
		x = x1 + f*(x2-x1)
		return x
	else
		return nil
	end
end
local function crossing_number(x,y,x1,y1,x2,y2)
	if y >= y1 and y < y2 or y >= y2 and y < y1 then
		if x < x1 and x < x2 then
			return signn(y2-y1)
		elseif x >= x1 and x < x2 or x >= x2 and x < x1 then
			a = y2 - y1
			b = x1 - x2
			c = - (a*x1 + b*y1)
			if a*(a*x+b*y+c) <= 0 then
				return signn(a)
			end
		end
	end
	return 0 
end
local function rule(w_r,counter)
	if w_r == "" then
		if counter ~= 0 then return true
		else return false
		end
	elseif w_r == "z" then
		if counter == 0 then return true
		else return false
		end
	elseif w_r == "e" then
		if counter%2 == 0 then return true
		else return false
		end
	else -- w_r == "eo"
		if counter%2 == 1 then return true
		else return false
		end
	end
end
local function pointin_triangle(x,y,pts)
	x1,y1,x2,y2,x3,y3 = unpack(pts)

	counter = crossing_number(x,y,x1,y1,x2,y2)
	counter = counter + crossing_number(x,y,x2,y2,x3,y3)
	counter = counter + crossing_number(x,y,x3,y3,x1,y1)
	
	return rule("",counter)
end
local function pointin_polygon(x,y,pts,w_r)
	counter = 0
	for i=0, #pts/2 - 2 do
		x1,y1 = pts[2*i+1],pts[2*i+2]
		x2,y2 = pts[2*i+3],pts[2*i+4]
		counter = counter + crossing_number(x,y,x1,y1,x2,y2)
	end
 	x1,y1 = pts[#pts-1],pts[#pts]
	x2,y2 = pts[1],pts[2]
	counter = counter + crossing_number(x,y,x1,y1,x2,y2)
	return rule(w_r,counter)
end
local function pointin_circle( x, y, data,T_inv)
	old_x, old_y = apply(T_inv,x,y)
	cx,cy,r = unpack(data)
	if (old_x-cx)*(old_x-cx)+(old_y-cy)*(old_y-cy) < r*r then
		return true
	else
		return false
	end
end
local function b2(i,t) -- t aplicado ao i-ezimo polinomio de bernstein ( 2 grau )
	if i == 0 then
		return (1-t)*(1-t)
	elseif i == 1 then
		return 2*t*(1-t)
	else
		return t*t
	end
end
local function b3(i,t) -- mesma coisa pra grau 3
	if i == 0 then
		return (1-t)*(1-t)*(1-t)
	elseif i == 1 then
		return 3*(1-t)*(1-t)*t
	elseif i == 2 then
		return 3*t*t*(1-t)
	else 
		return t*t*t
	end
end
local function qua_(x0,x1,x2,t)
	return 2*((-(1-t))*x0 + ((1-t)-t)*x1 + (t)*x2)
end
local function b_qua(x0,y0,x1,y1,x2,y2,t)
	x = b2(0,t)*x0 + b2(1,t)*x1 + b2(2,t)*x2
	y = b2(0,t)*y0 + b2(1,t)*y1 + b2(2,t)*y2
	return x,y
end
local function b_cub(cub,t)
	x0,y0,x1,y1,x2,y2,x3,y3 = unpack(cub)
	x = x0*(1-t)^3 + 3*x1*t*(1-t)^2+3*x2*(1-t)*t^2+x3*t^3
	y = y0*(1-t)^3 + 3*y1*t*(1-t)^2+3*y2*(1-t)*t^2+y3*t^3
	return x,y
end
local function b_rat(rat,t)
	u0,v0,w0,u1,v1,w1,u2,v2,w2 = unpack(rat)	
	u = b2(0,t)*u0 + b2(1,t)*u1 + b2(2,t)*u2
	v = b2(0,t)*v0 + b2(1,t)*v1 + b2(2,t)*v2
	w = b2(0,t)*w0 + b2(1,t)*w1 + b2(2,t)*w2
	return u,v,w
end
local function real_b_rat_(rat,t) -- only works for t = 0 or 1
	u0,v0,w0,u1,v1,w1,u2,v2,w2 = unpack(rat)	
	if t == 0 then
		x_ = (2*w1/w0)*((u1/w1)-(u0/w0))
		y_ = (2*w1/w0)*((v1/w1)-(v0/w0))
	elseif t == 1 then
		x_ = (2*w1/w2)*((u2/w2)-(u1/w1))
		y_ = (2*w1/w2)*((v2/w2)-(u1/w1))
	end
	return x_,y_
end
local function b_rat_(rat,t) -- fake derivative ( derivative in R3 )
	u0,v0,w0,u1,v1,w1,u2,v2,w2 = unpack(rat)	
	ut_ = qua_(u0,u1,u2,t)
	vt_ = qua_(v0,v1,v2,t)
	wt_ = qua_(w0,w1,w2,t)
	return ut_,vt_,wt_
end
local function b_qua_(x0,y0,x1,y1,x2,y2,t) -- derivada
	x_ = qua_(x0,x1,x2,t)
	y_ = qua_(y0,y1,y2,t)
	return x_,y_
end
local function b_cub_(cub,t) -- derivada
	x0,y0,x1,y1,x2,y2,x3,y3 = unpack(cub)
	x_ = 3*(-b2(0,t)*x0+(b2(0,t)-b2(1,t))*x1+(b2(1,t)-b2(2,t))*x2+b2(2,t)*x3)
	y_ = 3*(-b2(0,t)*y0+(b2(0,t)-b2(1,t))*y1+(b2(1,t)-b2(2,t))*y2+b2(2,t)*y3)
	return x_,y_
end
local function bhaskara(a,b,c) 
	b = b/2
	delta = b*b - a*c
	if delta < 0 then
		return 0/0,0/0
	elseif delta == 0 then
		return -b/a,0/0
	else -- delta > 0
		if a == 0 then
			if b > 0 then
				return 0/0,c/(-b-math.sqrt(delta))
			else 
				return 0/0,c/(-b+math.sqrt(delta))
			end
		else
			if b > 0 then
				return (-b-math.sqrt(delta))/a,c/(-b-math.sqrt(delta))
			else
				return (-b+math.sqrt(delta))/a,c/(-b+math.sqrt(delta))
			end
		end
	end
end
local function t_crit_rat(rat)
	-- Une catastrophe
end
local function t_crit_qua(x0,x1,x2) -- critic t
	return (x0-x1)/(x0-2*x1+x2)
end
local function t_crit_cub(x0,x1,x2,x3)
	return bhaskara(x3-3*x2+3*x1-x0,x0*2-4*x1+2*x2,-x0+x1)
end
local function divide_qua(qua,t)
	x0,y0,x1,y1,x2,y2 = unpack(qua)
	print('dividindo em t = ',t)
	xt, yt = b_qua(x0,y0,x1,y1,x2,y2,t) -- new interpolated
	x0_, y0_ = b_qua_(x0,y0,x1,y1,x2,y2,0) -- initial point derivative
	x2_, y2_ = b_qua_(x0,y0,x1,y1,x2,y2,1) -- final point derivative
	c1_x, c1_y = x0 + t*x0_/2, y0 + t*y0_/2 -- control point
	c2_x, c2_y = x2 - (1-t)*x2_/2, y2 - (1-t)*y2_/2 -- control point
	return {x0,y0,c1_x,c1_y,xt,yt},{xt,yt,c2_x,c2_y,x2,y2}
end
local function divide_cub(cub,t)
	x0,y0,x1,y1,x2,y2,x3,y3 = unpack(cub)
	xt, yt = b_cub(cub,t) -- new interpolated
	x0_, y0_ = b_cub_(cub,0) -- initial point derivative
	xt_, yt_ = b_cub_(cub,t) -- interpolated point derivative
	x3_, y3_ = b_cub_(cub,1) -- final point derivative
	c11_x, c11_y = x0 + t*x0_/3, y0 + t*y0_/3 -- control point
	c12_x, c12_y = xt - t*xt_/3, yt - t*yt_/3 -- control point
	c21_x, c21_y = xt + (1-t)*xt_/3, yt + (1-t)*yt_/3 -- control point
	c22_x, c22_y = x3 - (1-t)*x3_/3, y3 - (1-t)*y3_/3 -- control point
	return {x0,y0,c11_x,c11_y,c12_x,c12_y,xt,yt},{xt,yt,c21_x,c21_y,c22_x,c22_y,x3,y3}
end
local function divide_rat(rat,t)
	u0,v0,w0,u1,v1,w1,u2,v2,w2 = unpack(rat)
	ut,vt,wt = b_rat(rat,t) -- new interpolated
	u0_,v0_,w0_ = b_rat_(rat,0) -- initial point derivative
	u2_,v2_,w2_ = b_rat_(rat,1) -- final point derivative
	c1_u,c1_v,c1_w = u0 + t*u0_/2, v0 + t*v0_/2, w0 + t*w0_/2 -- control point 
	c2_u,c2_v,c2_w = u2 - (1-t)*u2_/2, v2 - (1-t)*v2_/2, w2 - (1-t)*w2_/2 -- the same
	return {u0,v0,w0,c1_u,c1_v,c1_w,ut,vt,wt},{ut,vt,wt,c2_u,c2_v,c2_w,u2,v2,w2}
end 
local function bisection(y0,y1,y2,y_)
	t_min = 0
	t_max = 1
	while t_max - t_min > 0.001 do
		t = (t_max + t_min)/2
		x,y = b_qua(0,y0,0,y1,0,y2,t)
		if y >= y_ and y0<=y2 or y <= y_ and y0>y2 then
			t_max = (t_max+t_min)/2
		else
			t_min = (t_max+t_min)/2
		end
	end
	return (t_max+t_min)/2
end	
local function c_bisection(y0,y1,y2,y3,y_)
	t_min = 0
	t_max = 1
	while t_max - t_min > 0.001 do
		t = (t_max + t_min)/2
		x,y = b_cub({0,y0,0,y1,0,y2,0,y3},t)
		if y >= y_ and y0<= y3 or y <= y_ and y0>y3 then
			t_max = (t_max+t_min)/2
		else
			t_min = (t_max+t_min)/2
		end
	end
	return (t_max+t_min)/2
end
local function r_bisection(rat,y_)
	u0,v0,w0,u1,v1,w1,u2,v2,w2 = unpack(rat)
	y0,y2 = v0/w0,v2/w2
	t_min = 0
	t_max = 1
	while t_max - t_min > 0.001 do
		t = (t_max + t_min)/2
		u,v,w = b_rat(rat,t)
		y = v/w
		if y >= y_ and y0<= y2 or y <= y_ and y0>y2 then
			t_max = (t_max+t_min)/2
		else
			t_min = (t_max+t_min)/2
		end
	end
	return (t_max+t_min)/2
end
local function pointin_path(x,y,data,w_r)
	counter = 0
	for i = 1,#data do
		local contour = data[i] -- 1 - type, 2 - points, 3 - roots
		if contour[1] == 'line' then
			x0,y0,x1,y1 = unpack(contour[2])
			counter = counter + crossing_number(x,y,x0,y0,x1,y1)
		elseif contour[1] == 'quad' then
			x0,y0,x1,y1,x2,y2 = unpack(contour[2])
			if y >= math.min(y0,y1,y2) and y < math.max(y0,y1,y2) then
				flag = false
				if x <= math.min(x0,x1,x2) then
					flag = true
				elseif x < math.max(x0,x1,x2) then
					if contour[3][y] == nil then
						t = bisection(y0,y1,y2,y)
					 	x_,y_ = b_qua(x0,y0,x1,y1,x2,y2,t)
						contour[3][y] = x_
					else
						x_ = contour[3][y]
					end
					if x < x_ then
						flag = true
					end
				end
				if flag then
					counter = counter + sign(y2-y0)
				end
			end
		elseif contour[1] == 'cubi' then
			x0,y0,x1,y1,x2,y2,x3,y3 = unpack(contour[2])
			if y >= math.min(y0,y3) and y < math.max(y0,y3) then
				flag = false
				if x <= math.min(x0,x3) then
					flag = true
				elseif x < math.max(x0,x3) then
					if contour[3][y] == nil then
						t = c_bisection(y0,y1,y2,y3,y)
						x_,y_ = b_cub(contour[2],t)
						contour[3][y] = x_
					else
						x_ = contour[3][y]
					end
					if x < x_ then
						flag = true
					end
				end
				if flag then
					counter = counter + sign(y3-y0)
				end
			
			elseif y == math.min(y0,y3) then
				if x > math.min(x0,x3) and x < math.max(x0,x3) then
					counter = counter + sign(x3-x0)
				end
			end
		elseif contour[1] == 'rati' then
			u0,v0,w0,u1,v1,w1,u2,v2,w2 = unpack(contour[2])
			x0,y0 = u0/w0,v0/w0
			x2,y2 = u2/w2,v2/w2
			if y >= math.min(y0,y2) and y < math.max(y0,y2) then
				flag = false
				if x <= math.min(x0,x2) then
					flag = true
				elseif x < math.max(x0,x2) then
					if contour[3][y] == nil then
						t = r_bisection(contour[2],y)
						u_,v_,w_ = b_rat(contour[2],t)
						x_ = u_/w_
						contour[3][y] =  x_
					else
						x_ = contour[3][y]
					end
					if x < x_ then
						flag = true
					end
				end
				if flag then
					counter = counter + sign(y2-y0)
				end
			end
		end
	end
	return rule(w_r,counter)
end
local function sample(content_table, x, y)	
	color = {1,1,1,1}
	for i=1, #content_table  do
	    shape = content_table[i]
	    if shape[1] == "triangle" then
		    if pointin_triangle(x,y,shape[3]) then
			    color =  shape[2]
		    end
	    elseif shape[1] == "polygon" then
		    if pointin_polygon(x,y,shape[3],shape[4]) then
			    color = shape[2]
		    end
            elseif shape[1] == "circle" then
		    if pointin_circle(x,y,shape[3],shape[4]) then
			    color = shape[2]
		    end
	    elseif shape[1] == "path" then
		    if pointin_path(x,y,shape[3],shape[4]) then
			    color = shape[2]
		    end
	    else
		    print("shape not recognized by 'sample'")
	    end
     	end
    	return unpack(color)
end

local function parse(args)
	local parsed = {
		pattern = nil,
		tx = nil,
		ty = nil,
        linewidth = nil,
		maxdepth = nil,
		p = nil,
		dumptreename = nil,
		dumpcellsprefix = nil,
	}
    local options = {
        { "^(%-maxdepth:(%d+)(.*))$", function(all, n, e)
            if not n then return false end
            assert(e == "", "invalid option " .. all)
            parsed.maxdepth = assert(tonumber(n), "invalid option " .. all)
            assert(parsed.maxdepth >= 1, "invalid option " .. all)
            return true
        end },
        { "^(%-tx:(%-?%d+)(.*))$", function(all, n, e)
            if not n then return false end
            assert(e == "", "trail invalid option " .. all)
            parsed.tx = assert(tonumber(n), "number invalid option " .. all)
            return true
        end },
        { "^(%-ty:(%-?%d+)(.*))$", function(all, n, e)
            if not n then return false end
            assert(e == "", "trail invalid option " .. all)
            parsed.ty = assert(tonumber(n), "number invalid option " .. all)
            return true
        end },
        { "^%-dumptree:(.*)$", function(n)
            if not n then return false end
            parsed.dumptreename = n
            return true
        end },
        { "^%-dumpcells:(.*)$", function(n)
            if not n then return false end
            parsed.dumpcellsprefix = n
            return true
        end },
        { "^(%-p:(%d+)(.*))$", function(all, n, e)
            if not n then return false end
            assert(e == "", "trail invalid option " .. all)
            parsed.p = assert(tonumber(n), "number invalid option " .. all)
            return true
        end },
        { "^(%-linewidth:(%d+)(.*))$", function(all, n, e)
            if not n then return false end
            assert(e == "", "trail invalid option " .. all)
			-- global variable
            parsed.linewidth = assert(tonumber(n),
                "number invalid option " .. all)
            return true
        end },
        { "^(%-pattern:(%d+)(.*))$", function(all, n, e)
            if not n then return false end
            assert(e == "", "trail invalid option " .. all)
            n = assert(tonumber(n), "number invalid option " .. all)
            assert(blue[n], "pattern does not exist" .. all)
            parsed.pattern = n
            return true
        end },
        { ".*", function(all)
            error("unrecognized option " .. all)
        end }
    }
    -- process options
    for i, arg in ipairs(args) do
        for j, option in ipairs(options) do
            if option[2](arg:match(option[1])) then
                break
            end
        end
    end
    return parsed
end

local winding_rule_prefix = {
    [_M.winding_rule.non_zero] = "",
    [_M.winding_rule.zero] = "z",
    [_M.winding_rule.even] = "e",
    [_M.winding_rule.odd] = "eo"
}
local function x_times(a,b)
	return {a[1]*b[1]+a[2]*b[4],a[1]*b[2]+a[2]*b[5],
	a[1]*b[3]+a[2]*b[6]+a[3],a[4]*b[1]+a[5]*b[4],a[4]*b[2]+a[5]*b[5],
	a[4]*b[3]+a[5]*b[6]+a[6]}
end
local function inverse(a_m) -- Affine Matrix
	local f = a_m[1]*a_m[5]-a_m[4]*a_m[2]
	return {a_m[5]/f,-a_m[2]/f,(-a_m[3]*a_m[5]+a_m[2]*a_m[6])/f,-a_m[4]/f,a_m[1]/f,(a_m[3]*a_m[4]-a_m[1]*a_m[6])/f}
end
bx,by = 0,0
local function path_accelerate(copy)
	t = {} -- objeto generico que nao sei pra que serve

	local function append(x)
		table.insert(copy[#copy][3],x)
	end
	local function open(x0,y0)
		bx, by = x0, y0
	end
	local function close(x0,y0)
		append({"line",{x0,y0,bx,by},{}})
	end
    	t.begin_contour = function(self, x0, y0)
		print('begin',x0,y0)
		open(x0,y0)
	end
        t.end_open_contour = function(self, x0, y0)
		print('end_open',x0,y0)
		close(x0,y0)
	end
        t.end_closed_contour = function(self, x0, y0)
		print('end close',x0,y0)
	end
	t.linear_segment = function(self, x0, y0, x1, y1)
		print('line',x0,y0,x1,y1)
		append({"line",{x0,y0,x1,y1},{}})
	end 
	t.quadratic_segment = function(self, x0, y0, x1, y1, x2, y2) 
		print('quad',x0,y0,x1,y1,x2,y2)
		append({"quad",{x0,y0,x1,y1,x2,y2},{}})
	end
	t.rational_quadratic_segment = function(self, u0, v0, w0, u1, v1, w1, u2, v2, w2) 
		print('rati',u0,v0,w0,u1,v1,w1,u2,v2,w2)
		append({"rati",{u0,v0,w0,u1,v1,w1,u2,v2,w2},{}})
	end
	t.cubic_segment = function(self, x0, y0, x1, y1, x2, y2, x3, y3) 
		print('cubi',x0,y0,x1,y1,x2,y2,x3,y3)
		append({"cubi",{x0,y0,x1,y1,x2,y2,x3,y3},{}})
	end
	return t
end

local function monotonize(forward)
	t = {} -- objeto generico que nao sei pra que serve
	crit = {}
	local function add(...)
		arr_t = table.pack(...)
		print('unpack',unpack(arr_t))
		for i,t in ipairs(arr_t) do
			print(t)
			if t ~= nil and t > 0 and t < 1 then
				flag = true
				for j,t_ in ipairs(crit) do
					if t_ == t then
						flag = false
					end
				end
				if flag then
					table.insert(crit,t)
				end
			end
		end
		table.sort(crit)
	end
    	t.begin_contour = function(self, x0, y0)
		forward:begin_contour(x0,y0)
	end
        t.end_open_contour = function(self, x0, y0)
		forward:end_open_contour(x0,y0)
	end
        t.end_closed_contour = function(self, x0, y0)
		forward:end_closed_contour(x0,y0)
	end
	t.linear_segment = function(self, x0, y0, x1, y1)
		forward:linear_segment(x0,y0,x1,y1)
	end 
	t.quadratic_segment = function(self, x0, y0, x1, y1, x2, y2)
		crit = {}
		print('[PRE] Monotonizing quadratic ...')
		-- t critico em x
		tx = t_crit_qua(x0,x1,x2)
		ty = t_crit_qua(y0,y1,y2)
		add(tx,ty)
		qua = {x0,y0,x1,y1,x2,y2}
		print('criticos',unpack(crit))
		for i,critic in ipairs(crit) do	
			n_qua, qua = divide_qua(qua,critic)
			forward:quadratic_segment(unpack(n_qua))
		end
		forward:quadratic_segment(unpack(qua))
	end
	t.rational_quadratic_segment = function(self, x0, y0, x1, y1, w1, x2, y2) 
		crit = {}
		print('[PRE] Monotonizing rational quadratic ...')
		-- ts criticos
		a = x0-2*x1+x2
		b = -2*x0+2*x1
		c = x0

		d = 2 - 2*w1

		e = y0-2*y1+y2
		f = -2*y0+2*y1
		g = y0


		a_ = -2*a*d +b*d - 2*d*b +d*a
		b_ = 2*a - b*d - 2*d*c +d*b
		c_ = b +d*c
		
		e_ = -2*e*d +f*d - 2*d*f +d*e
		f_ = 2*e - f*d - 2*d*g +d*f
		g_ = f +d*g
		print('indices',a_,b_,c_,d,e_,f_,g_)	
		tx1,tx2 = bhaskara(a_,b_,c_)
		ty1,ty2 = bhaskara(e_,f_,g_)

		add(tx1,tx2,ty1,ty2)
		rat = {x0,y0,1,x1,y1,w1,x2,y2,1}
		print('criticos',unpack(crit))
		for i, critic in ipairs(crit) do 
			n_rat, rat = divide_rat(rat,critic)
			forward:rational_quadratic_segment(unpack(n_rat))
		end
		forward:rational_quadratic_segment(unpack(rat))
	end
	t.cubic_segment = function(self, x0, y0, x1, y1, x2, y2, x3, y3)
		crit = {}
		print('[PRE] Monotonizing cubic ...')
		-- ts criticos
		tx1,tx2 = t_crit_cub(x0,x1,x2,x3)
		ty1,ty2 = t_crit_cub(y0,y1,y2,y3)
		add(tx1,tx2,ty1,ty2)
		cub = {x0,y0,x1,y1,x2,y2,x3,y3}
		print('criticos',unpack(crit))
		
		for i,critic in ipairs(crit) do
			n_cub, cub = divide_cub(cub,critic)
			forward:cubic_segment(unpack(n_cub))
		end
		forward:cubic_segment(unpack(cub))
	end
	return t
end
function _M.accelerate(content, viewport, args)
     
    -- por enquanto essa funcao retorna uma tabela (lista de shapes)
    -- , onde cada item eh uma tabela (shape) contendo nome e uma lista
    -- de numeros que significam algo, sempre se referindo a cena.
    --
    -- Eventuais mudancas de sistema de coordenada e camera sao feitas aqui
    -- e portanto begin_transform e end_transform nao sao repassados ao
    -- render. Documentacao do formato abaixo.
    --
    -- Primitiva {"tipo",{cor},{pts ou parametros},{winding_rule ou T inversa}}
    
    -- nxf = xf:transformed(a_xf)
    -- x,y = xf:apply(x,y)
    -- matrix:inverse()
    content_table = {}
    scene = content:get_scene_data()
    act_xf = {content:get_xf()}
    local function cur()
	    return act_xf[#act_xf]
    end
    local function add(xf)
	    act_xf[#act_xf+1] = xf:transformed(act_xf[#act_xf])
    end
    local function del()
	    act_xf[#act_xf] = nil
    end
	
    scene:iterate{
	    count = 1,
	    begin_transform = function(self,depth,xf)
		    print(self.count,"begin",xf,depth)
		    print("act_xf",unpack(cur()))
		    print("xf",xf)
		    add(xf)
		    self.count = self.count + 1
	    end,
	    painted_element = function(self,winding_rule, shape, paint)
		    print(self.count, winding_rule, shape, paint)
		    local xf = shape:get_xf()
		    print("xf",unpack(xf))
		    w_r = winding_rule_prefix[winding_rule]
		    add(xf)
		    a = {}
		    print("actual xf:",unpack(cur()))
		    local pt = paint:get_type()
		    if pt == _M.paint_type.solid_color then
			    local v_color = paint:get_solid_color()
			    print("rgb",v_color[1],v_color[2],v_color[3])
			    color = {v_color[1],v_color[2],v_color[3],1}
		    else
			    print("paint not supported",pt)
			    color = {1,1,1,1}
		    end
		    --local st = shape:get_type()
		    st = _M.shape_type.path
		    if st == _M.shape_type.triangle then
			    local tri = shape:get_triangle_data()
			    local x1,y1 = apply(act_xf[#act_xf],tri:get_x1(),tri:get_y1())
			    local x2,y2 = apply(act_xf[#act_xf],tri:get_x2(),tri:get_y2())
			    local x3,y3 = apply(act_xf[#act_xf],tri:get_x3(),tri:get_y3())
			    print("triangle",x1,y1,x2,y2,x3,y3)
			    print("color",color[1],color[2],color[3],color[4])
			    table.insert(content_table,{"triangle",
			    color,{x1,y1,x2,y2,x3,y3}})	
		    elseif st == _M.shape_type.polygon then
			    local poly = shape:get_polygon_data()
			    local u_coords = poly:get_coordinates()
			    print("polygon")
			    coords = {}
			    for i = 1, #u_coords,2 do
				    x, y = apply(act_xf[#act_xf],u_coords[i],u_coords[i+1])
				    table.insert(coords,x)
				    table.insert(coords,y)
			    end
		 	    table.insert(content_table,{"polygon",color,coords,w_r})
			    for i = 1, #coords,2 do
				    print("",coords[i],coords[i+1])	
			    end
		    elseif st == _M.shape_type.circle then
			    local circ = shape:get_circle_data()
			    local cx,cy = circ:get_cx(), circ:get_cy()
			    local r = circ:get_r()
			    local T_inv = inverse(act_xf[#act_xf])
			    print("circle",cx,cy,r)
			    table.insert(content_table,{"circle",color
			    ,{cx,cy,r},T_inv})
		    elseif st == _M.shape_type.path then
			    print('iniciando o iterate')
			    local path_data = shape:as_path_data()
			    table.insert(content_table,{"path",color,{},w_r})
			    path_data:iterate(filter.xform(cur(),monotonize(path_accelerate(content_table))))
		    
			    print("content",unpack(content_table[1][2]))
		    else 
			    print(st)
			    print("shape not supported",st)
		    end 
		    self.count = self.count +1
	    end,
    	    end_transform = function(self,depth,xf)
		    del()
	  	    print(self.count,"end", xf, depth)
		    self.count = self.count + 1
    	    end
    }
    
    parsed = parse(args)	
    stderr("parsed arguments\n")
    for i,v in pairs(parsed) do
        stderr("  -%s:%s\n", tostring(i), tostring(v))
    end
	-- This function should inspect the content and pre-process
    -- it into a better representation, an accelerated
    -- representation, to simplify the job of sample(accelerated, x, y).
    -- Here, we simply return the unmodified content.
    -- It is up to you to do better!
    return content_table
end

function _M.render(accelerated, viewport, file, args)
    local parsed = parse(args)
    stderr("parsed arguments\n")
    for i,v in pairs(parsed) do
        stderr("  -%s:%s\n", tostring(i), tostring(v))
    end
local time = chronos.chronos()
    -- Get viewport to compute pixel centers
    local vxmin, vymin, vxmax, vymax = unpack(viewport, 1, 4)
    local width, height = vxmax-vxmin, vymax-vymin
    -- Allocate output image
    local img = image.image(width, height, 4)
    -- Render
    for i = 1, height do
stderr("\r%5g%%", floor(1000*i/height)/10)
        local y = vymin+i-1.+.5
        for j = 1, width do
            local x = vxmin+j-1+.5
            img:set_pixel(j, i, sample(accelerated, x, y))
        end
    end
stderr("\n")
stderr("rendering in %.3fs\n", time:elapsed())
time:reset()
    -- Store output image
    image.png.store8(file, img)
stderr("saved in %.3fs\n", time:elapsed())
end

return _M
