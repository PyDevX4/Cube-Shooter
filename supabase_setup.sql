-- Cube Shooter online accounts. Paste all of this into Supabase: SQL Editor -> New query -> Run.

-- One row per player: their username and saved progress (coins, upgrades, skins, best wave...)
create table if not exists public.players (
  id uuid primary key references auth.users (id) on delete cascade,
  username text not null,
  progress jsonb not null default '{}'::jsonb,
  updated_at timestamptz not null default now()
);

-- Usernames are unique no matter the upper/lower case
create unique index if not exists players_username_key on public.players (lower(username));

-- Row Level Security: a player can only ever read and change their own row
alter table public.players enable row level security;

drop policy if exists "read own row" on public.players;
create policy "read own row" on public.players
  for select using (auth.uid() = id);

drop policy if exists "create own row" on public.players;
create policy "create own row" on public.players
  for insert with check (auth.uid() = id);

drop policy if exists "update own row" on public.players;
create policy "update own row" on public.players
  for update using (auth.uid() = id) with check (auth.uid() = id);

drop policy if exists "delete own row" on public.players;
create policy "delete own row" on public.players
  for delete using (auth.uid() = id);

-- Lets the game tell "that username is taken" before signing up, without exposing anyone's data
create or replace function public.username_taken(name text)
returns boolean
language sql
security definer
set search_path = public
as $$
  select exists (select 1 from public.players where lower(username) = lower(name));
$$;
grant execute on function public.username_taken(text) to anon, authenticated;

-- Lets a logged-in player delete their own account (login and progress) from the Settings menu
create or replace function public.delete_my_account()
returns void
language sql
security definer
set search_path = public, auth
as $$
  delete from auth.users where id = auth.uid();
$$;
revoke execute on function public.delete_my_account() from anon;
grant execute on function public.delete_my_account() to authenticated;

-- Admin accounts: set is_admin to true on your own row in Table Editor -> players.
-- Players can only change their username and progress, never is_admin (so nobody can make themselves an admin).
alter table public.players add column if not exists is_admin boolean not null default false;
-- The owner account (you): the ` console bar and its commands. Set is_owner to true on your own row.
alter table public.players add column if not exists is_owner boolean not null default false;
revoke insert, update on public.players from authenticated, anon;
grant insert (id, username, progress) on public.players to authenticated;
grant update (username, progress, updated_at) on public.players to authenticated;

-- The theme everyone's game shows (Halloween, Christmas...). Only owner accounts can change it.
create table if not exists public.game_settings (
  id int primary key default 1,
  theme text not null default 'None',
  updated_at timestamptz not null default now(),
  constraint game_settings_one_row check (id = 1)
);
insert into public.game_settings (id, theme) values (1, 'None') on conflict (id) do nothing;
alter table public.game_settings enable row level security;

drop policy if exists "everyone reads the theme" on public.game_settings;
create policy "everyone reads the theme" on public.game_settings
  for select using (true);

drop policy if exists "owners set the theme" on public.game_settings;
create policy "owners set the theme" on public.game_settings
  for update using (exists (select 1 from public.players p where p.id = auth.uid() and p.is_owner))
  with check (exists (select 1 from public.players p where p.id = auth.uid() and p.is_owner));

grant select on public.game_settings to anon, authenticated;
grant update (theme, updated_at) on public.game_settings to authenticated;
